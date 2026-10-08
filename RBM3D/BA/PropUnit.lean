/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KHeatDiff
import RBM3D.BA.Prop5

/-!
# The unit first and second differences of `Θ_BA`, mixed charges `σ₁ ≠ σ₂` (BA-P6)

Ticket T2341.  Targets `baPropUnit1mixed_holds` and `baPropUnit2mixed_holds`: the pins
`BAPropUnit1mixed`, `BAPropUnit2mixed` (the texts of `PropUnit1`, `PropUnit2` of
`Propagator/PropUnit.lean:39,52` with `Θ ↦ BATheta`, the bulk hypothesis `‖m‖ = 1, κ ≤ Im m ↦
BAReal d L g κ E m`, and `σ₁ ≠ σ₂`), by porting `Propagator/PropUnit.lean`
(`propUnit1_holds :747`, `propUnit2_holds :826`) with the substitutions
`Theta_eq_laplace_prod ↦ BATheta_eq_laplace_kBA` (through `baP5_theta_eq`),
`lgGam/lgEps ↦ baP5Gam/baP5Eps` (`γ = t g²`), `kProd_diff1_le/diff2_le ↦ kBA_diff1_le/diff2_le`,
`kProd_gap ↦ kBA_gap`, `lg_convA ↦ baP5_convA`, and the polynomial head below in place of
`lg_bulk`/`lg_zero`.

Notation: `n ∈ {1, 2}` (first/second difference), `N = d + n`, `p = N - 2` (the decay
`(|a|+1)^{-p}`), `M = ⌊d/2⌋ + 1`, `A = |a|`, `e = 1 - t`, `γ = t g²`, `ε = e / γ`.

* **Representation**: for `0 < t < 1`, `Θ_t(0, a) = γ⁻¹ ∫₀^∞ e^{-ετ} kBA(τ, a) dτ`
  (`baP5_theta_eq`), so the unit differences are `γ⁻¹ ∫ e^{-ετ} (Δ kBA_τ)(a) dτ`.
* **Head** `τ ≤ L²`: `kBA_diff1_le`/`kBA_diff2_le`, `|Δ kBA_τ(a)| ≤ C min(1, τ^{-N/2})
  (1 + A²/max(τ,1))^{-M}`, polynomial in `A`.  The new Laplace lemma `baPropUnit_laplace_head`
  (the polynomial twin of `lg_bulk`): `γ⁻¹ ∫₀^∞ e^{-ετ} min(1, τ^{-N/2}) (1 + A²/max(τ,1))^{-M} dτ
  ≤ C (g² + 1 - t)⁻¹ (A + 1)^{-(N-2)}` (split at `τ = 1` and `τ = max(A,1)²`; `ε < 1`: the integral
  of the integrand; `ε ≥ 1`: its supremum times `1/ε`).
* **Tail** `τ ≥ L²`: `kBA_gap` (second and third conjuncts) and the band's `pu_tail` / `lg_tail`.
* **`t = 0`**: `Θ_0 = 1` (`baP5_Theta_zero`), the band's `pu_t0_bound`.

Ports of private lemmas of `Propagator/PropUnit.lean` (nothing from `../RBM1D`, `../RBM2D`):
`pu_zdist_two_le :68`, `pu_zdistD_two_le :73`, `pu_zdist_one_le :81`, `pu_zdistD_single_le :88`,
`pu_shift :98`, `pu_tail :239`, `pu_int_bound :325`, `pu_Theta_eq :454`, `pu_diff1_eq :477`,
`pu_diff2_eq :497`, `pu_master :537`, `pu_one_norm_le :683`, `pu_one_eq_zero :689`, `pu_t0_bound
:695`, `pu_ne_zero :731`, `pu_norm4 :739`, with the head hypotheses replaced.  Private helpers here
carry the prefix `baPU_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Set

namespace RBM.BA

open RBM RBM.Gauss RBM.Heat

/-! ## 1. The pins (mixed charges) -/

/-- **Unit pin 1, mixed charges**: `|Θ_t(0, a + e_j) − Θ_t(0, a)| ≤ C (g² + |1−t|)⁻¹ (|a| + 1)^{-(d−1)}`,
`σ₁ ≠ σ₂` (`PropUnit1` with `Θ ↦ BATheta`, `BAReal`). -/
def BAPropUnit1mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ (a : Zd d L) (j : Fin d),
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single j 1) - BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Unit pin 2, mixed charges**: unit second differences (`i ≠ j` and `i = j`), `(|a| + 1)^{-d}`,
`σ₁ ≠ σ₂` (`PropUnit2` with `Θ ↦ BATheta`, `BAReal`). -/
def BAPropUnit2mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ (a : Zd d L) (i j : Fin d),
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single i 1 + Pi.single j 1)
              - BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single i 1)
              - BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single j 1) + BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-! ## 2. Lattice facts (ports of `Propagator/PropUnit.lean:68-102`) -/

/-- `2 |u|_L ≤ L` on the cycle `ℤ_L`. -/
private lemma baPU_zdist_two_le (L : ℕ) (u : ZMod L) : 2 * zdist L u ≤ L := by
  unfold zdist
  omega

/-- `2 |x| ≤ d L` on the torus (`|x|` the periodic `ℓ¹` distance). -/
private lemma baPU_zdistD_two_le (d L : ℕ) (x : Zd d L) : 2 * zdistD d L x ≤ d * L := by
  unfold zdistD
  rw [Finset.mul_sum]
  calc ∑ i, 2 * zdist L (x i) ≤ ∑ _i : Fin d, L :=
        Finset.sum_le_sum (fun i _ => baPU_zdist_two_le L (x i))
    _ = d * L := by simp

/-- The unit step has length `≤ 1` on the cycle. -/
private lemma baPU_zdist_one_le (L : ℕ) : zdist L (1 : ZMod L) ≤ 1 := by
  unfold zdist
  refine (min_le_left _ _).trans ?_
  rw [ZMod.val_one_eq_one_mod]
  exact Nat.mod_le _ _

/-- The unit vector `e_j` has length `≤ 1`. -/
private lemma baPU_zdistD_single_le (d L : ℕ) (j : Fin d) :
    zdistD d L (Pi.single j (1 : ZMod L)) ≤ 1 := by
  unfold zdistD
  rw [Finset.sum_eq_single j]
  · simpa using baPU_zdist_one_le L
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `|a| ≤ |a + u| + |u|`. -/
private lemma baPU_shift {d L : ℕ} [NeZero L] (a u : Zd d L) :
    zdistD d L a ≤ zdistD d L (a + u) + zdistD d L u := by
  have h := zdistD_add_le d L (a + u) (-u)
  rw [add_neg_cancel_right, zdistD_neg] at h
  exact h

/-! ## 3. The polynomial head integral (the new Laplace lemma) -/

/-- The polynomial head integrand `min(1, τ^{-N/2}) (1 + A²/max(τ,1))^{-M}` (`N = d + n`,
`M = ⌊d/2⌋ + 1`), the bound of `kBA_diff1_le`/`kBA_diff2_le` without the constant. -/
private noncomputable def baPU_h (N M : ℕ) (A τ : ℝ) : ℝ :=
  min 1 (τ ^ (-(N : ℝ) / 2)) * (1 + A ^ 2 / max τ 1) ^ (-((M : ℝ)))

private lemma baPU_min_nonneg (N : ℕ) {τ : ℝ} (hτ : 0 < τ) : 0 ≤ min 1 (τ ^ (-(N : ℝ) / 2)) :=
  le_min zero_le_one (Real.rpow_nonneg hτ.le _)

private lemma baPU_one_le_W (A τ : ℝ) : 1 ≤ 1 + A ^ 2 / max τ 1 := by
  have : 0 ≤ A ^ 2 / max τ 1 := by positivity
  linarith

private lemma baPU_h_nonneg (N M : ℕ) (A : ℝ) {τ : ℝ} (hτ : 0 < τ) : 0 ≤ baPU_h N M A τ :=
  mul_nonneg (baPU_min_nonneg N hτ) (Real.rpow_nonneg (by linarith [baPU_one_le_W A τ]) _)

private lemma baPU_h_eq (N M : ℕ) (A τ : ℝ) :
    baPU_h N M A τ = min 1 (τ ^ (-(N : ℝ) / 2)) * ((1 + A ^ 2 / max τ 1) ^ M)⁻¹ := by
  unfold baPU_h
  rw [Real.rpow_neg (by linarith [baPU_one_le_W A τ]), Real.rpow_natCast]

private lemma baPU_h_le_min (N M : ℕ) (A : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    baPU_h N M A τ ≤ min 1 (τ ^ (-(N : ℝ) / 2)) := by
  unfold baPU_h
  have h2 : (1 + A ^ 2 / max τ 1) ^ (-((M : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (baPU_one_le_W A τ) (neg_nonpos.mpr (Nat.cast_nonneg M))
  calc min 1 (τ ^ (-(N : ℝ) / 2)) * (1 + A ^ 2 / max τ 1) ^ (-((M : ℝ)))
      ≤ min 1 (τ ^ (-(N : ℝ) / 2)) * 1 := mul_le_mul_of_nonneg_left h2 (baPU_min_nonneg N hτ)
    _ = _ := mul_one _

private lemma baPU_h_meas (N M : ℕ) (A : ℝ) : Measurable (baPU_h N M A) := by
  unfold baPU_h
  fun_prop

/-- `max(A, 1)² ≤ 1 + A²`. -/
private lemma baPU_B_sq_le {A : ℝ} : (max A 1) ^ 2 ≤ 1 + A ^ 2 := by
  rcases le_total A 1 with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg A]
  · rw [max_eq_left h]; linarith

/-- `(B²)^{-p/2} = (B^p)⁻¹`. -/
private lemma baPU_R_pow {B : ℝ} (hB : 0 < B) (p : ℕ) : (B ^ 2) ^ (-(p : ℝ) / 2) = (B ^ p)⁻¹ := by
  rw [← Real.rpow_natCast B 2, ← Real.rpow_mul hB.le]
  have : ((2 : ℕ) : ℝ) * (-(p : ℝ) / 2) = -(p : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg hB.le, Real.rpow_natCast]

/-- `τ ≤ 1`: `h ≤ (B^{2M})⁻¹`, `B = max(A, 1)`. -/
private lemma baPU_h_low (N M : ℕ) {A τ : ℝ} (hA : 0 ≤ A) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    baPU_h N M A τ ≤ (((max A 1) ^ 2) ^ M)⁻¹ := by
  rw [baPU_h_eq, max_eq_right hτ1, div_one]
  have h1 : min 1 (τ ^ (-(N : ℝ) / 2)) ≤ 1 := min_le_left _ _
  have hB : (max A 1) ^ 2 ≤ 1 + A ^ 2 := baPU_B_sq_le
  have hB0 : 0 < (max A 1) ^ 2 := by positivity
  have h2 : ((1 + A ^ 2) ^ M)⁻¹ ≤ (((max A 1) ^ 2) ^ M)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hB0.le hB M)
  calc min 1 (τ ^ (-(N : ℝ) / 2)) * ((1 + A ^ 2) ^ M)⁻¹ ≤ 1 * ((1 + A ^ 2) ^ M)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((1 + A ^ 2) ^ M)⁻¹ := one_mul _
    _ ≤ _ := h2

/-- `τ ≥ 1`: `h ≤ τ^{M - N/2} (B^{2M})⁻¹`. -/
private lemma baPU_h_mid (N M : ℕ) {A τ : ℝ} (hA : 0 ≤ A) (hτ : 1 ≤ τ) :
    baPU_h N M A τ ≤ τ ^ ((M : ℝ) - (N : ℝ) / 2) * (((max A 1) ^ 2) ^ M)⁻¹ := by
  have hτ0 : 0 < τ := by linarith
  rw [baPU_h_eq, max_eq_left hτ]
  have hB : (max A 1) ^ 2 ≤ τ + A ^ 2 := by
    have := baPU_B_sq_le (A := A); linarith
  have hB0 : 0 < (max A 1) ^ 2 := by positivity
  have h1 : min 1 (τ ^ (-(N : ℝ) / 2)) ≤ τ ^ (-(N : ℝ) / 2) := min_le_right _ _
  have h3 : (max A 1) ^ 2 / τ ≤ 1 + A ^ 2 / τ := by
    have : 1 + A ^ 2 / τ = (τ + A ^ 2) / τ := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right hB hτ0.le
  have h4 : (((max A 1) ^ 2 / τ) ^ M)⁻¹ = τ ^ M * (((max A 1) ^ 2) ^ M)⁻¹ := by
    rw [div_pow, inv_div]; field_simp
  have h2 : ((1 + A ^ 2 / τ) ^ M)⁻¹ ≤ τ ^ M * (((max A 1) ^ 2) ^ M)⁻¹ := by
    rw [← h4]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 M)
  have h5 : τ ^ ((M : ℝ) - (N : ℝ) / 2) = τ ^ (-(N : ℝ) / 2) * τ ^ M := by
    rw [← Real.rpow_natCast τ M, ← Real.rpow_add hτ0]
    congr 1; ring
  rw [h5, mul_assoc]
  exact mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg hτ0.le _)

/-- `τ ≥ 1`: `h ≤ τ^{-N/2}`. -/
private lemma baPU_h_tail (N M : ℕ) {A τ : ℝ} (hτ : 0 < τ) :
    baPU_h N M A τ ≤ τ ^ (-(N : ℝ) / 2) :=
  (baPU_h_le_min N M A hτ).trans (min_le_right _ _)

/-- The supremum: `h ≤ (B^p)⁻¹` (`N = p + 2`, `p ≤ 2M`).  For `τ ≥ 1`, with `v = min(N/2, M)`,
`h ≤ τ^{-v} (1 + A²/τ)^{-v} = (τ + A²)^{-v} ≤ (B²)^{-v} ≤ (B²)^{-p/2}`. -/
private lemma baPU_h_sup {N M p : ℕ} (hN : N = p + 2) (hpM : p ≤ 2 * M) {A τ : ℝ} (hA : 0 ≤ A)
    (hτ : 0 < τ) : baPU_h N M A τ ≤ ((max A 1) ^ p)⁻¹ := by
  have hB1 : 1 ≤ max A 1 := le_max_right _ _
  have hB0 : 0 < max A 1 := by linarith
  have hR1 : 1 ≤ (max A 1) ^ 2 := one_le_pow₀ hB1
  have hR0 : 0 < (max A 1) ^ 2 := by linarith
  rcases le_total τ 1 with h1 | h1
  · refine (baPU_h_low N M hA hτ h1).trans ?_
    rw [← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hB1 (by omega))
  · set v : ℝ := min ((N : ℝ) / 2) (M : ℝ) with hv
    have hpv : (p : ℝ) / 2 ≤ v := by
      rw [hv]
      refine le_min ?_ ?_
      · have : (N : ℝ) = p + 2 := by rw [hN]; push_cast; ring
        rw [this]; linarith
      · have : (p : ℝ) ≤ 2 * M := by exact_mod_cast hpM
        linarith
    have hv1 : v ≤ (N : ℝ) / 2 := min_le_left _ _
    have hv2 : v ≤ (M : ℝ) := min_le_right _ _
    have hW := baPU_one_le_W A τ
    rw [max_eq_left h1] at hW
    unfold baPU_h
    rw [max_eq_left h1]
    have e1 : τ ^ (-(N : ℝ) / 2) ≤ τ ^ (-v) := by
      apply Real.rpow_le_rpow_of_exponent_le h1
      have : -(N : ℝ) / 2 = -((N : ℝ) / 2) := by ring
      rw [this]; linarith
    have e2 : (1 + A ^ 2 / τ) ^ (-((M : ℝ))) ≤ (1 + A ^ 2 / τ) ^ (-v) :=
      Real.rpow_le_rpow_of_exponent_le hW (by linarith)
    have e3 : τ ^ (-v) * (1 + A ^ 2 / τ) ^ (-v) = (τ + A ^ 2) ^ (-v) := by
      rw [← Real.mul_rpow hτ.le (by linarith)]
      congr 1; field_simp
    have hτA : (max A 1) ^ 2 ≤ τ + A ^ 2 := by
      have := baPU_B_sq_le (A := A); linarith
    have hv0 : 0 ≤ v := by
      rw [hv]; exact le_min (by positivity) (by positivity)
    have e4 : (τ + A ^ 2) ^ (-v) ≤ ((max A 1) ^ 2) ^ (-v) :=
      Real.rpow_le_rpow_of_nonpos hR0 hτA (by linarith)
    have e5 : ((max A 1) ^ 2) ^ (-v) ≤ ((max A 1) ^ 2) ^ (-(p : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by
        have : -(p : ℝ) / 2 = -((p : ℝ) / 2) := by ring
        rw [this]; linarith)
    calc min 1 (τ ^ (-(N : ℝ) / 2)) * (1 + A ^ 2 / τ) ^ (-((M : ℝ)))
        ≤ τ ^ (-v) * (1 + A ^ 2 / τ) ^ (-v) :=
          mul_le_mul ((min_le_right _ _).trans e1) e2 (Real.rpow_nonneg (by linarith) _)
            (Real.rpow_nonneg hτ.le _)
      _ = (τ + A ^ 2) ^ (-v) := e3
      _ ≤ ((max A 1) ^ 2) ^ (-v) := e4
      _ ≤ ((max A 1) ^ 2) ^ (-(p : ℝ) / 2) := e5
      _ = ((max A 1) ^ p)⁻¹ := baPU_R_pow hB0 p

/-- A measurable function bounded by an integrable one on a measurable set is integrable there. -/
private lemma baPU_integrableOn_of_le {S : Set ℝ} (hS : MeasurableSet S) {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : IntegrableOn g S) (h0 : ∀ τ ∈ S, 0 ≤ f τ) (hle : ∀ τ ∈ S, f τ ≤ g τ) :
    IntegrableOn f S := by
  refine Integrable.mono' hg hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
  rw [Real.norm_of_nonneg (h0 τ hτ)]
  exact hle τ hτ

/-- The integral: `h` is integrable on `(0, ∞)` and `∫₀^∞ h ≤ 4 (B^p)⁻¹` (`N = p + 2`, `2 ≤ p`,
`p + 1 ≤ 2M`; `B = max(A, 1)`).  Pieces `(0, 1]`, `(1, B²]`, `(B², ∞)` with the bounds `c₁`,
`τ^{M - N/2} c₁`, `τ^{-N/2}` (`c₁ = (B^{2M})⁻¹`); `∫₁^{R} τ^s ≤ R^{s+1}/(s+1)` with `s + 1 ≥ 1/2`,
`∫_R^∞ τ^{-N/2} = R^{1-N/2}/(N/2 - 1)` with `N/2 - 1 ≥ 1`. -/
private lemma baPU_h_int {N M p : ℕ} (hN : N = p + 2) (hp : 2 ≤ p) (hpM : p + 1 ≤ 2 * M) {A : ℝ}
    (hA : 0 ≤ A) :
    IntegrableOn (baPU_h N M A) (Ioi 0) ∧
      ∫ τ in Ioi (0 : ℝ), baPU_h N M A τ ≤ 4 * ((max A 1) ^ p)⁻¹ := by
  have hB1 : 1 ≤ max A 1 := le_max_right _ _
  have hB0 : 0 < max A 1 := by linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (max A 1) ^ 2 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hRdef]; exact one_le_pow₀ hB1
  have hR0 : 0 < R := by linarith
  have hNr : (N : ℝ) = p + 2 := by rw [hN]; push_cast; ring
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpMr : (p : ℝ) + 1 ≤ 2 * M := by exact_mod_cast hpM
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (M : ℝ) - (N : ℝ) / 2 := ⟨_, rfl⟩
  have hs1 : 1 / 2 ≤ s + 1 := by rw [hs, hNr]; linarith
  have hsm : -1 < s := by linarith
  have hq : -(N : ℝ) / 2 < -1 := by rw [hNr]; linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ((max A 1) ^ p)⁻¹ := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  have hER : R ^ (-(p : ℝ) / 2) = E := by rw [hRdef, hE]; exact baPU_R_pow hB0 p
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = (R ^ M)⁻¹ := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  have hc1E : c1 ≤ E := by
    rw [hc1, ← hER, ← Real.rpow_natCast, ← Real.rpow_neg hR0.le]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hRs : R ^ (s + 1) = R ^ M * E := by
    rw [← hER, ← Real.rpow_natCast, ← Real.rpow_add hR0]
    congr 1
    rw [hs, hNr]; ring
  have hc1s : c1 * R ^ (s + 1) = E := by
    rw [hRs, hc1]; field_simp
  have hR3 : R ^ (-(N : ℝ) / 2 + 1) = E := by
    rw [← hER]; congr 1; rw [hNr]; ring
  -- the three pieces
  have hmeas := baPU_h_meas N M A
  have hnn : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ baPU_h N M A τ := fun τ hτ => baPU_h_nonneg N M A hτ
  have hI1 : IntegrableOn (baPU_h N M A) (Ioc 0 1) := by
    refine baPU_integrableOn_of_le measurableSet_Ioc hmeas (integrableOn_const (C := c1) (by simp)
      (by simp)) (fun τ hτ => hnn τ hτ.1) (fun τ hτ => ?_)
    rw [hc1, hRdef]; exact baPU_h_low N M hA hτ.1 hτ.2
  have hI2 : IntegrableOn (baPU_h N M A) (Ioc 1 R) := by
    have hg : IntegrableOn (fun τ : ℝ => τ ^ s * c1) (Ioc 1 R) :=
      ((intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := R) hsm).1).mul_const c1
    refine baPU_integrableOn_of_le measurableSet_Ioc hmeas hg
      (fun τ hτ => baPU_h_nonneg N M A (by linarith [hτ.1])) (fun τ hτ => ?_)
    rw [hc1, hRdef, hs]; exact baPU_h_mid N M hA hτ.1.le
  have hI3 : IntegrableOn (baPU_h N M A) (Ioi R) := by
    have hg : IntegrableOn (fun τ : ℝ => τ ^ (-(N : ℝ) / 2)) (Ioi R) :=
      integrableOn_Ioi_rpow_of_lt hq hR0
    refine baPU_integrableOn_of_le measurableSet_Ioi hmeas hg
      (fun τ hτ => baPU_h_nonneg N M A (by linarith [mem_Ioi.1 hτ])) (fun τ hτ => ?_)
    exact baPU_h_tail N M (by linarith [mem_Ioi.1 hτ])
  have hU12 : Ioc (0 : ℝ) 1 ∪ Ioc 1 R = Ioc 0 R := Ioc_union_Ioc_eq_Ioc zero_le_one hR1
  have hU : Ioc (0 : ℝ) R ∪ Ioi R = Ioi 0 := Ioc_union_Ioi_eq_Ioi hR0.le
  have hI12 : IntegrableOn (baPU_h N M A) (Ioc 0 R) := by
    rw [← hU12]; exact hI1.union hI2
  have hint : IntegrableOn (baPU_h N M A) (Ioi 0) := by
    rw [← hU]; exact hI12.union hI3
  refine ⟨hint, ?_⟩
  have hsplit : ∫ τ in Ioi (0 : ℝ), baPU_h N M A τ
      = (∫ τ in Ioc 0 1, baPU_h N M A τ) + (∫ τ in Ioc 1 R, baPU_h N M A τ)
        + ∫ τ in Ioi R, baPU_h N M A τ := by
    rw [← hU, setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi hI12 hI3, ← hU12,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hI1 hI2]
  -- the three integrals
  have J1 : ∫ τ in Ioc 0 1, baPU_h N M A τ ≤ c1 := by
    calc ∫ τ in Ioc 0 1, baPU_h N M A τ ≤ ∫ τ in Ioc (0 : ℝ) 1, c1 :=
          setIntegral_mono_on hI1 (integrableOn_const (C := c1) (by simp) (by simp))
            measurableSet_Ioc (fun τ hτ => by rw [hc1, hRdef]; exact baPU_h_low N M hA hτ.1 hτ.2)
      _ = c1 := by simp [setIntegral_const, Real.volume_real_Ioc]
  have J2 : ∫ τ in Ioc 1 R, baPU_h N M A τ ≤ E / (s + 1) := by
    have hg : IntegrableOn (fun τ : ℝ => τ ^ s * c1) (Ioc 1 R) :=
      ((intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := R) hsm).1).mul_const c1
    have hval : ∫ τ in Ioc 1 R, τ ^ s = (R ^ (s + 1) - 1 ^ (s + 1)) / (s + 1) := by
      rw [← intervalIntegral.integral_of_le hR1]
      exact integral_rpow (Or.inl hsm)
    calc ∫ τ in Ioc 1 R, baPU_h N M A τ ≤ ∫ τ in Ioc 1 R, τ ^ s * c1 :=
          setIntegral_mono_on hI2 hg measurableSet_Ioc (fun τ hτ => by
            rw [hc1, hRdef, hs]; exact baPU_h_mid N M hA hτ.1.le)
      _ = (R ^ (s + 1) - 1 ^ (s + 1)) / (s + 1) * c1 := by rw [integral_mul_const, hval]
      _ ≤ R ^ (s + 1) / (s + 1) * c1 := by
          rw [Real.one_rpow]
          have : 0 < s + 1 := by linarith
          gcongr
          linarith
      _ = E / (s + 1) := by rw [div_mul_eq_mul_div, mul_comm (R ^ (s + 1)) c1, hc1s]
  have J3 : ∫ τ in Ioi R, baPU_h N M A τ ≤ E / ((N : ℝ) / 2 - 1) := by
    have hg : IntegrableOn (fun τ : ℝ => τ ^ (-(N : ℝ) / 2)) (Ioi R) :=
      integrableOn_Ioi_rpow_of_lt hq hR0
    calc ∫ τ in Ioi R, baPU_h N M A τ ≤ ∫ τ in Ioi R, τ ^ (-(N : ℝ) / 2) :=
          setIntegral_mono_on hI3 hg measurableSet_Ioi (fun τ hτ =>
            baPU_h_tail N M (by linarith [mem_Ioi.1 hτ]))
      _ = -R ^ (-(N : ℝ) / 2 + 1) / (-(N : ℝ) / 2 + 1) := integral_Ioi_rpow_of_lt hq hR0
      _ = E / ((N : ℝ) / 2 - 1) := by
          rw [hR3]
          have : (-(N : ℝ) / 2 + 1) = -((N : ℝ) / 2 - 1) := by ring
          rw [this, div_neg, neg_div, neg_neg]
  rw [hsplit]
  have hd2 : E / (s + 1) ≤ 2 * E := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hd3 : E / ((N : ℝ) / 2 - 1) ≤ E := by
    rw [div_le_iff₀ (by rw [hNr]; linarith)]; rw [hNr]; nlinarith
  linarith

/-- `∫₀^∞ e^{-ετ} dτ = 1/ε` and integrability, `ε > 0`. -/
private lemma baPU_exp_int {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) = 1 / ε := by
  have ha : -ε < 0 := by linarith
  refine ⟨integrableOn_exp_mul_Ioi ha 0, ?_⟩
  rw [integral_exp_mul_Ioi ha 0]
  simp [neg_div]

/-- `((max A 1)^p)⁻¹ ≤ 2^p ((A + 1)^p)⁻¹` (`A + 1 ≤ 2 max(A, 1)`). -/
private lemma baPU_B_inv_le (p : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((max A 1) ^ p)⁻¹ ≤ 2 ^ p * (((A + 1) ^ p)⁻¹) := by
  have hB1 : 1 ≤ max A 1 := le_max_right _ _
  have hAB : A ≤ max A 1 := le_max_left _ _
  have h1 : (A + 1) ^ p ≤ 2 ^ p * (max A 1) ^ p := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) p
  have hB0 : 0 < (max A 1) ^ p := by positivity
  have hA0 : 0 < (A + 1) ^ p := by positivity
  simp only [inv_eq_one_div, mul_one_div]
  rw [div_le_div_iff₀ hB0 hA0]
  linarith

/-- **The head** (private core): `γ⁻¹ ∫₀^∞ e^{-ετ} h ≤ C_H (g² + e)⁻¹ ((A + 1)^p)⁻¹`, `ε = e/γ`,
under the two conversions of `baP5_convA`.  `ε < 1`: `∫ h ≤ 4 (B^p)⁻¹`; `ε ≥ 1`: `sup h ≤ (B^p)⁻¹`
and `∫ e^{-ετ} = 1/ε`. -/
private lemma baPU_head {N M p : ℕ} (hN : N = p + 2) (hp : 2 ≤ p) (hpM : p + 1 ≤ 2 * M) {CA : ℝ}
    (hCA : 0 < CA) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ (γ e g2 A : ℝ), 0 < γ → 0 < e → 0 < g2 → 0 ≤ A →
      (1 ≤ e / γ → 1 / e ≤ CA / (g2 + e)) → (e / γ < 1 → 1 / γ ≤ CA / (g2 + e)) →
      IntegrableOn (fun τ : ℝ => Real.exp (-(e / γ) * τ) * baPU_h N M A τ) (Ioi 0) ∧
      γ⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) * baPU_h N M A τ
        ≤ CH * ((g2 + e)⁻¹ * (((A + 1) ^ p)⁻¹)) := by
  refine ⟨CA * (4 * 2 ^ p), by positivity, ?_⟩
  intro γ e g2 A hγ he hg2 hA hA1 hA2
  have hε : 0 < e / γ := div_pos he hγ
  have hg2e : 0 < g2 + e := by positivity
  have hCAe : CA / (g2 + e) = CA * (g2 + e)⁻¹ := div_eq_mul_inv _ _
  have hB1 : 1 ≤ max A 1 := le_max_right _ _
  have hBp : 0 < ((max A 1) ^ p)⁻¹ := by positivity
  have hAp : 0 < (((A + 1) ^ p)⁻¹) := by positivity
  have hmeas := baPU_h_meas N M A
  obtain ⟨hhI, hhJ⟩ := baPU_h_int hN hp hpM hA
  have hBA := baPU_B_inv_le p hA
  have hexp1 : ∀ τ ∈ Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) ≤ 1 := fun τ hτ => by
    rw [Real.exp_le_one_iff]
    have := mem_Ioi.1 hτ
    nlinarith
  have hint : IntegrableOn (fun τ : ℝ => Real.exp (-(e / γ) * τ) * baPU_h N M A τ) (Ioi 0) := by
    refine baPU_integrableOn_of_le measurableSet_Ioi
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).mul hmeas) hhI
      (fun τ hτ => mul_nonneg (Real.exp_pos _).le (baPU_h_nonneg N M A hτ)) (fun τ hτ => ?_)
    calc Real.exp (-(e / γ) * τ) * baPU_h N M A τ ≤ 1 * baPU_h N M A τ :=
          mul_le_mul_of_nonneg_right (hexp1 τ hτ) (baPU_h_nonneg N M A hτ)
      _ = _ := one_mul _
  refine ⟨hint, ?_⟩
  have hK : 0 ≤ (g2 + e)⁻¹ * (((A + 1) ^ p)⁻¹) := by positivity
  rcases lt_or_ge (e / γ) 1 with hlt | hge1
  · -- `ε < 1`
    have hJ : ∫ τ in Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) * baPU_h N M A τ
        ≤ 4 * ((max A 1) ^ p)⁻¹ := by
      refine le_trans (setIntegral_mono_on hint hhI measurableSet_Ioi (fun τ hτ => ?_)) hhJ
      calc Real.exp (-(e / γ) * τ) * baPU_h N M A τ ≤ 1 * baPU_h N M A τ :=
            mul_le_mul_of_nonneg_right (hexp1 τ hτ) (baPU_h_nonneg N M A hτ)
        _ = _ := one_mul _
    have hJ' : ∫ τ in Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) * baPU_h N M A τ
        ≤ 4 * 2 ^ p * (((A + 1) ^ p)⁻¹) := by
      refine hJ.trans ?_
      calc 4 * ((max A 1) ^ p)⁻¹ ≤ 4 * (2 ^ p * (((A + 1) ^ p)⁻¹)) :=
            mul_le_mul_of_nonneg_left hBA (by norm_num)
        _ = _ := by ring
    calc γ⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) * baPU_h N M A τ
        ≤ γ⁻¹ * (4 * 2 ^ p * (((A + 1) ^ p)⁻¹)) :=
          mul_le_mul_of_nonneg_left hJ' (by positivity)
      _ = (1 / γ) * (4 * 2 ^ p * (((A + 1) ^ p)⁻¹)) := by ring
      _ ≤ (CA / (g2 + e)) * (4 * 2 ^ p * (((A + 1) ^ p)⁻¹)) :=
          mul_le_mul_of_nonneg_right (hA2 hlt) (by positivity)
      _ = CA * (4 * 2 ^ p) * ((g2 + e)⁻¹ * (((A + 1) ^ p)⁻¹)) := by rw [hCAe]; ring
  · -- `ε ≥ 1`
    obtain ⟨hEI, hEv⟩ := baPU_exp_int hε
    have hJ : ∫ τ in Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) * baPU_h N M A τ
        ≤ ((max A 1) ^ p)⁻¹ * (1 / (e / γ)) := by
      have hg : IntegrableOn (fun τ : ℝ => Real.exp (-(e / γ) * τ) * ((max A 1) ^ p)⁻¹) (Ioi 0) :=
        hEI.mul_const _
      calc ∫ τ in Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) * baPU_h N M A τ
          ≤ ∫ τ in Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) * ((max A 1) ^ p)⁻¹ :=
            setIntegral_mono_on hint hg measurableSet_Ioi (fun τ hτ =>
              mul_le_mul_of_nonneg_left (baPU_h_sup hN (by omega) hA (mem_Ioi.1 hτ))
                (Real.exp_pos _).le)
        _ = ((max A 1) ^ p)⁻¹ * (1 / (e / γ)) := by rw [integral_mul_const, hEv, mul_comm]
    calc γ⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(e / γ) * τ) * baPU_h N M A τ
        ≤ γ⁻¹ * (((max A 1) ^ p)⁻¹ * (1 / (e / γ))) :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = ((max A 1) ^ p)⁻¹ * (1 / e) := by field_simp
      _ ≤ (2 ^ p * (((A + 1) ^ p)⁻¹)) * (CA / (g2 + e)) :=
          mul_le_mul hBA (hA1 hge1) (by positivity) (by positivity)
      _ = CA * (2 ^ p) * ((g2 + e)⁻¹ * (((A + 1) ^ p)⁻¹)) := by rw [hCAe]; ring
      _ ≤ CA * (4 * 2 ^ p) * ((g2 + e)⁻¹ * (((A + 1) ^ p)⁻¹)) := by
          have h1 : 0 ≤ CA * 2 ^ p * ((g2 + e)⁻¹ * (((A + 1) ^ p)⁻¹)) := by positivity
          nlinarith [h1]

/-- **The new Laplace lemma** (public; the polynomial twin of `lg_bulk`).  For `0 < t < 1`, `A ≥ 0`,
`n ∈ {1, 2}`, `d ≥ 3`, `γ = baP5Gam g t = t g²`, `ε = baP5Eps g t = (1 - t)/γ`:
`e^{-ετ} min(1, τ^{-(d+n)/2}) (1 + A²/max(τ,1))^{-M}`, `M = ⌊d/2⌋ + 1`, is integrable on `(0, ∞)` and
`γ⁻¹ ∫₀^∞ e^{-ετ} min(1, τ^{-(d+n)/2}) (1 + A²/max(τ,1))^{-M} dτ ≤ C (g² + 1 - t)⁻¹ (A + 1)^{-(d+n-2)}`.
The integral over `(0, ∞)` dominates the one over `(0, L²]` (the integrand is nonnegative). -/
theorem baPropUnit_laplace_head (d n : ℕ) (hd : 3 ≤ d) (hn1 : 1 ≤ n) (hn2 : n ≤ 2) {Λ : ℝ}
    (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g t A : ℝ), 0 < g → g ≤ Λ → 0 < t → t < 1 → 0 ≤ A →
      IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ) *
          (min 1 (τ ^ (-((d : ℝ) + n) / 2)) * (1 + A ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ)))))
        (Ioi 0) ∧
      (baP5Gam g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) *
          (min 1 (τ ^ (-((d : ℝ) + n) / 2)) * (1 + A ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ))))
        ≤ C * ((g ^ 2 + (1 - t))⁻¹ * (((A + 1) ^ (d + n - 2))⁻¹)) := by
  obtain ⟨CA, hCA, hconv⟩ := baP5_convA Λ hΛ
  obtain ⟨CH, hCH, hhead⟩ := baPU_head (N := d + n) (M := d / 2 + 1) (p := d + n - 2)
    (by omega) (by omega) (by omega) hCA
  refine ⟨CH, hCH, ?_⟩
  intro g t A hg hgΛ ht0 ht1 hA
  have hγ := baP5_gam_pos hg ht0
  have he : 0 < 1 - t := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  obtain ⟨hA1, hA2⟩ := hconv g t hg hgΛ ht0 ht1
  have hεeq : baP5Eps g t = (1 - t) / baP5Gam g t := rfl
  rw [hεeq] at hA1 hA2
  have hh := hhead (baP5Gam g t) (1 - t) (g ^ 2) A hγ he hg2 hA hA1 hA2
  have hcast : ∀ τ : ℝ, baPU_h (d + n) (d / 2 + 1) A τ
      = min 1 (τ ^ (-((d : ℝ) + n) / 2)) * (1 + A ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ))) := by
    intro τ; unfold baPU_h; push_cast; rfl
  simp only [← hcast]
  exact hh

/-! ## 4. The tail and the abstract integral bound (ports of `pu_tail`, `pu_int_bound`) -/

/-- The tail: `γ⁻¹ L^{-m} min(1/ε, L²/c_G) ≤ C_T (g² + e)⁻¹ (N + 1)^{-p}` for `N ≤ dL/2`. -/
private lemma baPU_tail {m p : ℕ} (hm : m = p + 2) {cG CA : ℝ} (hcG : 0 < cG) (hCA : 0 < CA)
    (d : ℕ) :
    ∃ CT : ℝ, 0 < CT ∧ ∀ (γ e g2 : ℝ) (L N : ℕ), 0 < γ → 0 < e → 0 < g2 → 1 ≤ L →
      2 * N ≤ d * L →
      (1 ≤ e / γ → 1 / e ≤ CA / (g2 + e)) → (e / γ < 1 → 1 / γ ≤ CA / (g2 + e)) →
      γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * min (1 / (e / γ)) ((L : ℝ) ^ 2 / cG))
        ≤ CT * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
  set Pp : ℝ := ((d : ℝ) / 2 + 1) ^ p with hPp
  have hPp0 : 0 < Pp := by positivity
  refine ⟨CA * Pp * (1 + 1 / cG), by positivity, ?_⟩
  intro γ e g2 L N hγ he hg2 hL hNL hA1 hA2
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  have hg2e : 0 < g2 + e := by positivity
  have hLp : 0 < (L : ℝ) ^ p := by positivity
  have hN1p : 0 < ((N : ℝ) + 1) ^ p := by positivity
  have hNL' : 2 * (N : ℝ) ≤ (d : ℝ) * L := by exact_mod_cast hNL
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hCAe : CA / (g2 + e) = CA * (g2 + e)⁻¹ := div_eq_mul_inv _ _
  have hLN : ((L : ℝ) ^ p)⁻¹ ≤ Pp * (((N : ℝ) + 1) ^ p)⁻¹ := by
    have h1 : (N : ℝ) + 1 ≤ ((d : ℝ) / 2 + 1) * (L : ℝ) := by nlinarith
    have h2 : ((N : ℝ) + 1) ^ p ≤ Pp * (L : ℝ) ^ p := by
      calc ((N : ℝ) + 1) ^ p ≤ (((d : ℝ) / 2 + 1) * (L : ℝ)) ^ p :=
            pow_le_pow_left₀ (by positivity) h1 p
        _ = Pp * (L : ℝ) ^ p := mul_pow _ _ _
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hLp hN1p, one_mul]
    exact h2
  have hLm : ((L : ℝ) ^ m)⁻¹ ≤ ((L : ℝ) ^ p)⁻¹ := by
    apply inv_anti₀ hLp
    exact pow_le_pow_right₀ hLr (by omega)
  have hLm2 : ((L : ℝ) ^ m)⁻¹ * (L : ℝ) ^ 2 = ((L : ℝ) ^ p)⁻¹ := by
    rw [hm, pow_add]; field_simp
  have hTg : 0 ≤ (g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹ := by positivity
  have hmin0 : ∀ x y : ℝ, min x y ≤ x := fun x y => min_le_left x y
  have hmin1 : ∀ x y : ℝ, min x y ≤ y := fun x y => min_le_right x y
  rcases lt_or_ge (e / γ) 1 with hlt | hge1
  · calc γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * min (1 / (e / γ)) ((L : ℝ) ^ 2 / cG))
        ≤ γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * ((L : ℝ) ^ 2 / cG)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmin1 _ _) (by positivity)
      _ = (1 / γ) * (1 / cG) * ((((L : ℝ) ^ m)⁻¹ * (L : ℝ) ^ 2)) := by
          field_simp
      _ = (1 / γ) * (1 / cG) * ((L : ℝ) ^ p)⁻¹ := by rw [hLm2]
      _ ≤ (CA / (g2 + e)) * (1 / cG) * (Pp * (((N : ℝ) + 1) ^ p)⁻¹) := by
          have h1 : 0 ≤ (1 / cG) * ((L : ℝ) ^ p)⁻¹ := by positivity
          have h2 : 0 ≤ (CA / (g2 + e)) * (1 / cG) := by positivity
          calc (1 / γ) * (1 / cG) * ((L : ℝ) ^ p)⁻¹
              = (1 / γ) * ((1 / cG) * ((L : ℝ) ^ p)⁻¹) := by ring
            _ ≤ (CA / (g2 + e)) * ((1 / cG) * ((L : ℝ) ^ p)⁻¹) :=
                mul_le_mul_of_nonneg_right (hA2 hlt) h1
            _ = (CA / (g2 + e)) * (1 / cG) * ((L : ℝ) ^ p)⁻¹ := by ring
            _ ≤ (CA / (g2 + e)) * (1 / cG) * (Pp * (((N : ℝ) + 1) ^ p)⁻¹) :=
                mul_le_mul_of_nonneg_left hLN h2
      _ = CA * Pp * (1 / cG) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by rw [hCAe]; ring
      _ ≤ CA * Pp * (1 + 1 / cG) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
          have h1 : 0 ≤ CA * Pp := by positivity
          nlinarith [mul_nonneg h1 hTg]
  · calc γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * min (1 / (e / γ)) ((L : ℝ) ^ 2 / cG))
        ≤ γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * (1 / (e / γ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmin0 _ _) (by positivity)
      _ = ((L : ℝ) ^ m)⁻¹ * (1 / e) := by field_simp
      _ ≤ ((L : ℝ) ^ p)⁻¹ * (CA / (g2 + e)) := by
          have h1 : 0 ≤ 1 / e := by positivity
          have h2 : 0 ≤ ((L : ℝ) ^ p)⁻¹ := by positivity
          calc ((L : ℝ) ^ m)⁻¹ * (1 / e) ≤ ((L : ℝ) ^ p)⁻¹ * (1 / e) :=
                mul_le_mul_of_nonneg_right hLm h1
            _ ≤ ((L : ℝ) ^ p)⁻¹ * (CA / (g2 + e)) :=
                mul_le_mul_of_nonneg_left (hA1 hge1) h2
      _ ≤ (Pp * (((N : ℝ) + 1) ^ p)⁻¹) * (CA / (g2 + e)) :=
          mul_le_mul_of_nonneg_right hLN (by positivity)
      _ = CA * Pp * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by rw [hCAe]; ring
      _ ≤ CA * Pp * (1 + 1 / cG) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
          have h1 : 0 ≤ CA * Pp := by positivity
          have h2 : 0 ≤ CA * Pp * (1 / cG) := by positivity
          nlinarith [mul_nonneg h2 hTg]
/-- The abstract integral bound (`pu_int_bound :325`, with the polynomial head `H`): a continuous `f`
with the head bound `|f| ≤ C_K H` on `(0, L²]` and the tail bound on `[L², ∞)` has
`∫ e^{-ετ} f ≤ C_K ∫ e^{-ετ} H + C_G L^{-m} min(1/ε, L²/c_G)`. -/
private lemma baPU_int_bound {m : ℕ} {Lr : ℝ} (hLr : 0 < Lr) {f H : ℝ → ℝ}
    (hf : Continuous f) {CK CG cG ε : ℝ} (hCK : 0 ≤ CK) (hCG : 0 ≤ CG) (hcG : 0 < cG)
    (hε : 0 < ε) (hH0 : ∀ τ : ℝ, 0 < τ → 0 ≤ H τ)
    (hJ : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * H τ) (Ioi 0))
    (hhead : ∀ τ : ℝ, 0 < τ → τ ≤ Lr ^ 2 → |f τ| ≤ CK * H τ)
    (htail : ∀ τ : ℝ, Lr ^ 2 ≤ τ → |f τ| ≤ CG * (Lr ^ m)⁻¹ * Real.exp (-cG * τ / Lr ^ 2)) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * f τ) (Ioi 0) ∧
    |∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) * f τ|
      ≤ CK * (∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) * H τ)
        + CG * (Lr ^ m)⁻¹ * min (1 / ε) (Lr ^ 2 / cG) := by
  set T : ℝ := Lr ^ 2 with hT
  have hT0 : 0 < T := by positivity
  set fe : ℝ → ℝ := fun τ => Real.exp (-ε * τ) * f τ with hfe
  have hfe_cont : Continuous fe :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf
  have hheadb : ∀ τ ∈ Ioc 0 T, |fe τ| ≤ CK * (Real.exp (-ε * τ) * H τ) := by
    intro τ hτ
    have h := hhead τ hτ.1 hτ.2
    have he0 := Real.exp_pos (-ε * τ)
    simp only [hfe, abs_mul, abs_of_pos he0]
    calc Real.exp (-ε * τ) * |f τ| ≤ Real.exp (-ε * τ) * (CK * H τ) :=
          mul_le_mul_of_nonneg_left h he0.le
      _ = _ := by ring
  have htailb : ∀ τ ∈ Ioi T, |fe τ| ≤ CG * (Lr ^ m)⁻¹ * Real.exp (-ε * τ - cG * τ / T) := by
    intro τ hτ
    have h := htail τ (le_of_lt hτ)
    have he0 := Real.exp_pos (-ε * τ)
    simp only [hfe, abs_mul, abs_of_pos he0]
    have e1 : Real.exp (-ε * τ - cG * τ / T) = Real.exp (-ε * τ) * Real.exp (-cG * τ / T) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1]
    calc Real.exp (-ε * τ) * |f τ|
        ≤ Real.exp (-ε * τ) * (CG * (Lr ^ m)⁻¹ * Real.exp (-cG * τ / T)) :=
          mul_le_mul_of_nonneg_left h he0.le
      _ = _ := by ring
  have ht := lg_tail T hT0
  obtain ⟨hI1, hV1⟩ := ht.1 ε cG hε.le hcG
  obtain ⟨-, hV2⟩ := ht.2.1 ε cG hε hcG.le
  have hHi : IntegrableOn fe (Ioc 0 T) := by
    refine Integrable.mono' ((hJ.mono_set Ioc_subset_Ioi_self).const_mul CK)
      hfe_cont.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [Real.norm_eq_abs]
    exact hheadb τ hτ
  have hTi : IntegrableOn fe (Ioi T) := by
    refine Integrable.mono' (hI1.const_mul (CG * (Lr ^ m)⁻¹)) hfe_cont.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [Real.norm_eq_abs]
    exact htailb τ hτ
  have hint : IntegrableOn fe (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hT0.le]
    exact hHi.union hTi
  refine ⟨hint, ?_⟩
  have hsplit : ∫ τ in Ioi (0 : ℝ), fe τ = (∫ τ in Ioc 0 T, fe τ) + ∫ τ in Ioi T, fe τ := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hHi hTi,
      Ioc_union_Ioi_eq_Ioi hT0.le]
  have hH : |∫ τ in Ioc 0 T, fe τ|
      ≤ CK * ∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) * H τ := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ τ in Ioc 0 T, fe τ‖ ≤ ∫ τ in Ioc 0 T, CK * (Real.exp (-ε * τ) * H τ) := by
          refine norm_integral_le_of_norm_le ((hJ.mono_set Ioc_subset_Ioi_self).const_mul CK) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).2
            (Filter.Eventually.of_forall fun τ hτ => ?_)
          rw [Real.norm_eq_abs]
          exact hheadb τ hτ
      _ = CK * ∫ τ in Ioc 0 T, Real.exp (-ε * τ) * H τ := integral_const_mul _ _
      _ ≤ CK * ∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) * H τ := by
          apply mul_le_mul_of_nonneg_left _ hCK
          refine setIntegral_mono_set hJ ?_ (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
          exact mul_nonneg (Real.exp_pos _).le (hH0 τ hτ)
  have hεT : Real.exp (-ε * T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hTl : |∫ τ in Ioi T, fe τ| ≤ CG * (Lr ^ m)⁻¹ * min (1 / ε) (T / cG) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ τ in Ioi T, fe τ‖
        ≤ ∫ τ in Ioi T, CG * (Lr ^ m)⁻¹ * Real.exp (-ε * τ - cG * τ / T) := by
          refine norm_integral_le_of_norm_le (hI1.const_mul _) ?_
          refine (ae_restrict_iff' measurableSet_Ioi).2
            (Filter.Eventually.of_forall fun τ hτ => ?_)
          rw [Real.norm_eq_abs]
          exact htailb τ hτ
      _ = CG * (Lr ^ m)⁻¹ * ∫ τ in Ioi T, Real.exp (-ε * τ - cG * τ / T) :=
          integral_const_mul _ _
      _ ≤ CG * (Lr ^ m)⁻¹ * min (1 / ε) (T / cG) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine le_min ?_ ?_
          · calc _ ≤ Real.exp (-ε * T) / ε := hV2
              _ ≤ 1 / ε := by
                  rw [div_le_div_iff_of_pos_right hε]; exact hεT
          · calc _ ≤ Real.exp (-ε * T) * (T / cG) := hV1
              _ ≤ 1 * (T / cG) := mul_le_mul_of_nonneg_right hεT (by positivity)
              _ = _ := one_mul _
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hH hTl)

/-! ## 5. The Laplace representation of the unit differences (twins of `pu_diff1_eq`, `pu_diff2_eq`) -/

/-- `τ ↦ kBA(τ, a)` is continuous (component of `kBA_basic`). -/
private lemma baPU_kBA_cont {d L : ℕ} [NeZero L] {g E : ℝ} {m : ℂ} (hg : 0 < g)
    (hS : BASelf d L g (E : ℂ) m) (a : Zd d L) :
    Continuous (fun τ : ℝ => kBA d L g E m τ a) :=
  (kBA_basic d L g E m hg hS).2.2.2.2.2 a

/-- `e^{-ετ} kBA(τ, a)` is integrable on `(0, ∞)` for `ε > 0` (port of `baP5_F_integrable`,
`BA/Prop5.lean:113`, which is private). -/
private lemma baPU_F_integrable {d L : ℕ} [NeZero L] {g E : ℝ} {m : ℂ} (hg : 0 < g)
    (hS : BASelf d L g (E : ℂ) m) {ε : ℝ} (hε : 0 < ε) (a : Zd d L) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a) (Ioi 0) := by
  have hg' : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hc := baPU_kBA_cont hg hS a
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a)
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a).aestronglyMeasurable
  refine Integrable.mono' hg' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hτ' : 0 ≤ τ := le_of_lt hτ
  obtain ⟨h0, -, h1, -⟩ := kBA_basic d L g E m hg hS
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (h0 τ hτ' a))]
  calc Real.exp (-ε * τ) * kBA d L g E m τ a ≤ Real.exp (-ε * τ) * 1 :=
        mul_le_mul_of_nonneg_left (h1 τ hτ' a) (Real.exp_pos _).le
    _ = _ := mul_one _

/-- The unit first difference as `γ⁻¹ |∫ e^{-ετ} (kBA_τ(a + e_j) - kBA_τ(a))|`. -/
private lemma baPU_diff1_eq {d L : ℕ} [NeZero L] (hL : 3 ≤ L) {g E : ℝ} {m : ℂ} {t : ℝ}
    (hg : 0 < g) (hS : BASelf d L g (E : ℂ) m) (ht0 : 0 < t) (ht1 : t < 1) (a : Zd d L)
    (j : Fin d) :
    ‖BATheta d L g E m t true false 0 (a + Pi.single j 1) - BATheta d L g E m t true false 0 a‖
      = (baP5Gam g t)⁻¹ * |∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) *
          (kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a)| := by
  have hγ : 0 < baP5Gam g t := baP5_gam_pos hg ht0
  have hε : 0 < baP5Eps g t := baP5_eps_pos hg ht0 ht1
  rw [baP5_theta_eq d L hL g E m t hg hS ht0 ht1, baP5_theta_eq d L hL g E m t hg hS ht0 ht1,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hI : ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) *
        (kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a)
      = (∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ (a + Pi.single j 1))
        - ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a := by
    simp_rw [mul_sub]
    exact integral_sub (baPU_F_integrable hg hS hε _) (baPU_F_integrable hg hS hε _)
  rw [hI, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hγ)]

/-- The unit second difference as `γ⁻¹ |∫ e^{-ετ} (Δ_i Δ_j kBA_τ)(a)|`. -/
private lemma baPU_diff2_eq {d L : ℕ} [NeZero L] (hL : 3 ≤ L) {g E : ℝ} {m : ℂ} {t : ℝ}
    (hg : 0 < g) (hS : BASelf d L g (E : ℂ) m) (ht0 : 0 < t) (ht1 : t < 1) (a : Zd d L)
    (i j : Fin d) :
    ‖BATheta d L g E m t true false 0 (a + Pi.single i 1 + Pi.single j 1)
        - BATheta d L g E m t true false 0 (a + Pi.single i 1)
        - BATheta d L g E m t true false 0 (a + Pi.single j 1)
        + BATheta d L g E m t true false 0 a‖
      = (baP5Gam g t)⁻¹ * |∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) *
          (kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a)| := by
  have hγ : 0 < baP5Gam g t := baP5_gam_pos hg ht0
  have hε : 0 < baP5Eps g t := baP5_eps_pos hg ht0 ht1
  rw [baP5_theta_eq d L hL g E m t hg hS ht0 ht1 (a + Pi.single i 1 + Pi.single j 1),
    baP5_theta_eq d L hL g E m t hg hS ht0 ht1 (a + Pi.single i 1),
    baP5_theta_eq d L hL g E m t hg hS ht0 ht1 (a + Pi.single j 1),
    baP5_theta_eq d L hL g E m t hg hS ht0 ht1 a, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
    ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  have i1 := baPU_F_integrable hg hS hε (a + Pi.single i 1 + Pi.single j 1)
  have i2 := baPU_F_integrable hg hS hε (a + Pi.single i 1)
  have i3 := baPU_F_integrable hg hS hε (a + Pi.single j 1)
  have i4 := baPU_F_integrable hg hS hε a
  have e : ∀ τ : ℝ, Real.exp (-(baP5Eps g t) * τ) *
        (kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
          - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a)
      = Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1)
        - Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ (a + Pi.single i 1)
        - Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ (a + Pi.single j 1)
        + Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a := fun τ => by ring
  simp_rw [e]
  have i12 : IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ)
      * kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1)
      - Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ (a + Pi.single i 1)) (Ioi 0) := i1.sub i2
  have i123 : IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ)
      * kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1)
      - Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ (a + Pi.single i 1)
      - Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ (a + Pi.single j 1)) (Ioi 0) := i12.sub i3
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2,
    ← mul_sub, ← mul_sub, ← mul_add, abs_mul, abs_of_pos (inv_pos.mpr hγ)]

/-! ## 6. The glue (twin of `pu_master :537`) -/

/-- The glue: for a continuous `f` with the polynomial head bound and the tail bound, `γ⁻¹ |∫ e^{-ετ} f|`
is bounded by `C (g² + e)⁻¹ (|a| + 1)^{-(d+n-2)}` (`m = d + n`, `p = d + n - 2`). -/
private lemma baPU_master (d : ℕ) (hd : 3 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ) {n : ℕ} (hn1 : 1 ≤ n)
    (hn2 : n ≤ 2) {CK CG cG : ℝ} (hCK : 0 < CK) (hCG : 0 < CG) (hcG : 0 < cG) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ), 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (a : Zd d L) (f : ℝ → ℝ), Continuous f →
      (∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
          |f τ| ≤ CK * baPU_h (d + n) (d / 2 + 1) (zdistD d L a : ℝ) τ) →
      (∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →
          |f τ| ≤ CG * ((L : ℝ) ^ (d + n))⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) →
      IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ) * f τ) (Ioi 0) ∧
      (baP5Gam g t)⁻¹ * |∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) * f τ|
        ≤ C * ((g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d + n - 2))⁻¹) := by
  obtain ⟨CA, hCA, hconv⟩ := baP5_convA Λ hΛ
  obtain ⟨CH, hCH, hhead⟩ := baPU_head (N := d + n) (M := d / 2 + 1) (p := d + n - 2)
    (by omega) (by omega) (by omega) hCA
  obtain ⟨CT, hCT, htail⟩ := baPU_tail (m := d + n) (p := d + n - 2) (by omega) hcG hCA d
  refine ⟨CK * CH + CG * CT, by positivity, ?_⟩
  intro L hL g hg hgΛ t ht0 ht1 a f hf hh ht
  have hγ : 0 < baP5Gam g t := baP5_gam_pos hg ht0
  have he : 0 < 1 - t := by linarith
  have hε : 0 < baP5Eps g t := baP5_eps_pos hg ht0 ht1
  have hg2 : 0 < g ^ 2 := by positivity
  have hLr : (0 : ℝ) < (L : ℝ) := by
    have : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  obtain ⟨hA1, hA2⟩ := hconv g t hg hgΛ ht0 ht1
  have hεeq : baP5Eps g t = (1 - t) / baP5Gam g t := rfl
  rw [hεeq] at hA1 hA2
  obtain ⟨hJ, hJv⟩ := hhead (baP5Gam g t) (1 - t) (g ^ 2) (zdistD d L a : ℝ) hγ he hg2
    (Nat.cast_nonneg _) hA1 hA2
  have hN2 : 2 * zdistD d L a ≤ d * L := baPU_zdistD_two_le d L a
  have h2 := htail (baP5Gam g t) (1 - t) (g ^ 2) L (zdistD d L a) hγ he hg2 (by omega) hN2
    hA1 hA2
  rw [← hεeq] at h2
  rw [← hεeq] at hJ hJv
  obtain ⟨hint, hbd⟩ := baPU_int_bound (m := d + n) hLr hf hCK.le hCG.le hcG hε
    (fun τ hτ => baPU_h_nonneg (d + n) (d / 2 + 1) _ hτ) hJ hh ht
  refine ⟨hint, ?_⟩
  calc (baP5Gam g t)⁻¹ * |∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) * f τ|
      ≤ (baP5Gam g t)⁻¹ * (CK * (∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ)
            * baPU_h (d + n) (d / 2 + 1) (zdistD d L a : ℝ) τ)
          + CG * ((L : ℝ) ^ (d + n))⁻¹ * min (1 / baP5Eps g t) ((L : ℝ) ^ 2 / cG)) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = CK * ((baP5Gam g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ)
            * baPU_h (d + n) (d / 2 + 1) (zdistD d L a : ℝ) τ)
          + CG * ((baP5Gam g t)⁻¹ * (((L : ℝ) ^ (d + n))⁻¹ * min (1 / baP5Eps g t)
            ((L : ℝ) ^ 2 / cG))) := by ring
    _ ≤ CK * (CH * ((g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d + n - 2))⁻¹))
          + CG * (CT * ((g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d + n - 2))⁻¹)) := by
        gcongr
    _ = (CK * CH + CG * CT) * ((g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d + n - 2))⁻¹) := by
        ring

/-! ## 7. The case `t = 0`, `Θ_0 = 1` (ports of `pu_one_norm_le`, `pu_one_eq_zero`, `pu_t0_bound`, `pu_ne_zero`, `pu_norm4`) -/

/-- The entries of the identity matrix have norm `≤ 1`. -/
private lemma baPU_one_norm_le {d L : ℕ} (x : Zd d L) :
    ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 x‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-- The off-diagonal entries of the identity matrix vanish. -/
private lemma baPU_one_eq_zero {d L : ℕ} {x : Zd d L} (hx : x ≠ 0) :
    (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 x = 0 := by
  simp [Ne.symm hx]

/-- `t = 0`: a quantity `D ≤ 4`, vanishing for `n > 2`, is
`≤ 4 (Λ² + 1) 3^d (g² + 1)⁻¹ (n + 1)^{-q}`. -/
private lemma baPU_t0_bound {Λ g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {d q : ℕ} (hq : q ≤ d) (n : ℕ)
    (D : ℝ) (hD4 : D ≤ 4) (hDn : 2 < n → D = 0) :
    D ≤ 4 * (Λ ^ 2 + 1) * 3 ^ d * ((g ^ 2 + 1)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹) := by
  have hg2 : 0 < g ^ 2 + 1 := by positivity
  have hn1q : 0 < ((n : ℝ) + 1) ^ q := by positivity
  have hΛ0 : 0 < Λ := lt_of_lt_of_le hg hgΛ
  have hTg : 0 ≤ (g ^ 2 + 1)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹ := by positivity
  by_cases hn : n ≤ 2
  · have hn2' : (n : ℝ) + 1 ≤ 3 := by exact_mod_cast (by omega : n + 1 ≤ 3)
    have h1 : ((n : ℝ) + 1) ^ q ≤ 3 ^ d := by
      calc ((n : ℝ) + 1) ^ q ≤ 3 ^ q := pow_le_pow_left₀ (by positivity) hn2' q
        _ ≤ 3 ^ d := pow_le_pow_right₀ (by norm_num) hq
    have h2 : (Λ ^ 2 + 1)⁻¹ ≤ (g ^ 2 + 1)⁻¹ := inv_anti₀ hg2 (by nlinarith)
    have h3 : ((3 : ℝ) ^ d)⁻¹ ≤ (((n : ℝ) + 1) ^ q)⁻¹ := inv_anti₀ hn1q h1
    calc D ≤ 4 := hD4
      _ = 4 * (Λ ^ 2 + 1) * 3 ^ d * ((Λ ^ 2 + 1)⁻¹ * ((3 : ℝ) ^ d)⁻¹) := by
          have : (Λ ^ 2 + 1) ≠ 0 := by positivity
          field_simp
      _ ≤ 4 * (Λ ^ 2 + 1) * 3 ^ d * ((g ^ 2 + 1)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹) := by gcongr
  · rw [hDn (by omega)]
    positivity

/-- A point `x = a + u` with `|u| ≤ 2` is nonzero when `|a| > 2`. -/
private lemma baPU_ne_zero {d L : ℕ} [NeZero L] (a u x : Zd d L) (hx : x = a + u)
    (hu : zdistD d L u ≤ 2) (hn : 2 < zdistD d L a) : x ≠ 0 := by
  intro h0
  have := baPU_shift a u
  rw [← hx, h0, zdistD_zero] at this
  omega

/-- The four-term triangle inequality for the second difference. -/
private lemma baPU_norm4 (A B C D : ℂ) : ‖A - B - C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  calc ‖A - B - C + D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_add_le _ _
    _ ≤ (‖A - B‖ + ‖C‖) + ‖D‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by gcongr; exact norm_sub_le _ _
/-! ## 8. The targets -/

/-- **`BAPropUnit1mixed` holds** for every `d`, `Λ`, `κ` (unit first difference of `Θ_BA`,
`σ₁ ≠ σ₂`, no loss).  Special case `σ₁ ≠ σ₂` of the band statement, not the general `σ`. -/
theorem baPropUnit1mixed_holds (d : ℕ) (Λ κ : ℝ) : BAPropUnit1mixed d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨CK, hCK, hK⟩ := kBA_diff1_le d (by omega) Λ κ hΛ hκ
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := kBA_gap d (by omega) Λ κ hΛ hκ
  obtain ⟨CM, hCM, hM⟩ := baPU_master d hd hΛ (n := 1) le_rfl (by norm_num) hCK hCG hcG
  refine ⟨max CM (4 * (Λ ^ 2 + 1) * 3 ^ d), lt_max_of_lt_left hCM, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ hσ a j
  have : NeZero L := ⟨by omega⟩
  have he : 0 < 1 - t := by linarith
  have hTg0 : 0 ≤ (g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by positivity
  rw [abs_of_pos he, mul_assoc, baP5_Theta_mixed d L g E m t hσ]
  have hu1 : zdistD d L (Pi.single j (1 : ZMod L)) ≤ 2 :=
    (baPU_zdistD_single_le d L j).trans (by omega)
  rcases ht0.eq_or_lt with h0 | h0
  · -- `t = 0`
    subst h0
    simp only [baP5_Theta_zero]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right
      ((le_max_right _ _) : 4 * (Λ ^ 2 + 1) * 3 ^ d ≤ _) hTg0)
    have hT := baPU_t0_bound (d := d) (q := d - 1) hg hgΛ (by omega) (zdistD d L a)
      ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 (a + Pi.single j 1)
        - (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 a‖ ?_ ?_
    · simpa using hT
    · have n1 := baPU_one_norm_le (a + Pi.single j 1)
      have n0 := baPU_one_norm_le a
      exact (norm_sub_le _ _).trans (by linarith)
    · intro hn
      have hx1 := baPU_ne_zero a (Pi.single j 1) _ rfl hu1 hn
      have hx0 := baPU_ne_zero a 0 a (add_zero a).symm (by simp) hn
      rw [baPU_one_eq_zero hx1, baPU_one_eq_zero hx0]
      simp
  · -- `0 < t`
    have hS := hr.1
    have hf : Continuous (fun τ : ℝ => kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a) :=
      (baPU_kBA_cont hg hS _).sub (baPU_kBA_cont hg hS _)
    have hhead : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
        |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
          ≤ CK * baPU_h (d + 1) (d / 2 + 1) (zdistD d L a : ℝ) τ := by
      intro τ hτ hτL
      have h := hK L hL g E m hg hgΛ hr τ hτ hτL a j
      have hc : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
      unfold baPU_h
      rw [hc, ← mul_assoc]
      exact h
    have htail : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →
        |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
          ≤ CG * (((L : ℝ) ^ (d + 1))⁻¹) * Real.exp (-cG * τ / (L : ℝ) ^ 2) :=
      fun τ hτ => (hG L hL g E m hg hgΛ hr τ hτ a j j).2.1
    obtain ⟨-, hbd⟩ := hM L hL g hg hgΛ t h0 ht1 a _ hf hhead htail
    rw [baPU_diff1_eq hL hg hS h0 ht1 a j]
    have hp : d + 1 - 2 = d - 1 := by omega
    rw [hp] at hbd
    exact hbd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hTg0)

/-- **`BAPropUnit2mixed` holds** for every `d`, `Λ`, `κ` (unit second differences, mixed and
same-direction, `σ₁ ≠ σ₂`, no loss).  Special case `σ₁ ≠ σ₂` of the band statement. -/
theorem baPropUnit2mixed_holds (d : ℕ) (Λ κ : ℝ) : BAPropUnit2mixed d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨CK, hCK, hK⟩ := kBA_diff2_le d (by omega) Λ κ hΛ hκ
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := kBA_gap d (by omega) Λ κ hΛ hκ
  obtain ⟨CM, hCM, hM⟩ := baPU_master d hd hΛ (n := 2) (by norm_num) le_rfl hCK hCG hcG
  refine ⟨max CM (4 * (Λ ^ 2 + 1) * 3 ^ d), lt_max_of_lt_left hCM, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ hσ a i j
  have : NeZero L := ⟨by omega⟩
  have he : 0 < 1 - t := by linarith
  have hTg0 : 0 ≤ (g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by positivity
  rw [abs_of_pos he, mul_assoc, baP5_Theta_mixed d L g E m t hσ]
  have hui : zdistD d L (Pi.single i (1 : ZMod L)) ≤ 1 := baPU_zdistD_single_le d L i
  have huj : zdistD d L (Pi.single j (1 : ZMod L)) ≤ 1 := baPU_zdistD_single_le d L j
  have huij : zdistD d L (Pi.single i (1 : ZMod L) + Pi.single j 1) ≤ 2 := by
    have := zdistD_add_le d L (Pi.single i (1 : ZMod L)) (Pi.single j 1)
    omega
  rcases ht0.eq_or_lt with h0 | h0
  · -- `t = 0`
    subst h0
    simp only [baP5_Theta_zero]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right
      ((le_max_right _ _) : 4 * (Λ ^ 2 + 1) * 3 ^ d ≤ _) hTg0)
    have hT := baPU_t0_bound (d := d) (q := d) hg hgΛ le_rfl (zdistD d L a)
      ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 (a + Pi.single i 1 + Pi.single j 1)
        - (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 (a + Pi.single i 1)
        - (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 (a + Pi.single j 1)
        + (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 a‖ ?_ ?_
    · simpa using hT
    · have n1 := baPU_one_norm_le (a + Pi.single i 1 + Pi.single j 1)
      have n2 := baPU_one_norm_le (a + Pi.single i 1)
      have n3 := baPU_one_norm_le (a + Pi.single j 1)
      have n4 := baPU_one_norm_le a
      exact (baPU_norm4 _ _ _ _).trans (by linarith)
    · intro hn
      have hx1 := baPU_ne_zero a (Pi.single i 1 + Pi.single j 1) _ (add_assoc _ _ _) huij hn
      have hx2 := baPU_ne_zero a (Pi.single i 1) _ rfl (by omega) hn
      have hx3 := baPU_ne_zero a (Pi.single j 1) _ rfl (by omega) hn
      have hx4 := baPU_ne_zero a 0 a (add_zero a).symm (by simp) hn
      rw [baPU_one_eq_zero hx1, baPU_one_eq_zero hx2, baPU_one_eq_zero hx3, baPU_one_eq_zero hx4]
      simp
  · -- `0 < t`
    have hS := hr.1
    have hf : Continuous (fun τ : ℝ => kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1)
        - kBA d L g E m τ (a + Pi.single i 1) - kBA d L g E m τ (a + Pi.single j 1)
        + kBA d L g E m τ a) :=
      (((baPU_kBA_cont hg hS _).sub (baPU_kBA_cont hg hS _)).sub (baPU_kBA_cont hg hS _)).add
        (baPU_kBA_cont hg hS _)
    have hhead : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
        |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
          ≤ CK * baPU_h (d + 2) (d / 2 + 1) (zdistD d L a : ℝ) τ := by
      intro τ hτ hτL
      have h := hK L hL g E m hg hgΛ hr τ hτ hτL a i j
      have hc : ((d + 2 : ℕ) : ℝ) = (d : ℝ) + 2 := by push_cast; ring
      unfold baPU_h
      rw [hc, ← mul_assoc]
      exact h
    have htail : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →
        |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
          ≤ CG * (((L : ℝ) ^ (d + 2))⁻¹) * Real.exp (-cG * τ / (L : ℝ) ^ 2) :=
      fun τ hτ => (hG L hL g E m hg hgΛ hr τ hτ a i j).2.2
    obtain ⟨-, hbd⟩ := hM L hL g hg hgΛ t h0 ht1 a _ hf hhead htail
    rw [baPU_diff2_eq hL hg hS h0 ht1 a i j]
    have hp : d + 2 - 2 = d := by omega
    rw [hp] at hbd
    exact hbd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hTg0)

example (d : ℕ) (Λ κ : ℝ) : BAPropUnit1mixed d Λ κ := baPropUnit1mixed_holds d Λ κ
example (d : ℕ) (Λ κ : ℝ) : BAPropUnit2mixed d Λ κ := baPropUnit2mixed_holds d Λ κ

/-! ## 9. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, flow point `P`)

Both targets at the `KKernel` instance data (`BAReal 3 4 g₀ (Im m₀) E m₀`, `g₀ ≈ 4.67 ≤ 10`), with every
deterministic hypothesis discharged (`3 ≤ d`, `0 < Λ`, `0 < κ`, `3 ≤ L`, `0 < g ≤ Λ`, `BAReal`,
`0 ≤ t < 1`, `σ₁ ≠ σ₂`); the constants `C` stay existential, as in the statements.  Pattern of
`BA/Prop5.lean:1428`. -/

namespace PropUnitInst

open RBM.BA.MFixedPointInst

/-- `baPropUnit1mixed_holds` at `t = 1/2` (`ε ≈ 0.046 < 1`), `σ = (+,-)`, `a = (1, 0, 0) ≠ 0`
(`|a| = 1`), `j = 0`. -/
theorem inst_unit1 : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
    zdistD 3 4 (![1, 0, 0] : Zd 3 4) = 1 ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ((![1, 0, 0] : Zd 3 4) + Pi.single 0 1)
        - BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 (![1, 0, 0] : Zd 3 4)‖
      ≤ C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹
        * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baPropUnit1mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, by decide, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      true false (by decide) ![1, 0, 0] 0⟩

/-- `baPropUnit1mixed_holds` at the other mixed charge `σ = (-,+)`, `t = 1/100` (`ε ≈ 4.5 ≥ 1`),
`a = (2, 1, 0)` (`|a| = 3`), `j = 1`. -/
theorem inst_unit1_large_eps : ∃ C : ℝ, 0 < C ∧ zdistD 3 4 (![2, 1, 0] : Zd 3 4) = 3 ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 100) false true 0 ((![2, 1, 0] : Zd 3 4) + Pi.single 1 1)
        - BATheta 3 4 P.g0 P.E P.m0 (1 / 100) false true 0 (![2, 1, 0] : Zd 3 4)‖
      ≤ C * (P.g0 ^ 2 + |1 - (1 / 100 : ℝ)|)⁻¹
        * (((zdistD 3 4 (![2, 1, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baPropUnit1mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 100) (by norm_num) (by norm_num)
      false true (by decide) ![2, 1, 0] 1⟩

/-- `baPropUnit1mixed_holds` at `t = 0` (`Θ_0 = 1`), `a = (1, 0, 0)`, `j = 0`. -/
theorem inst_unit1_zero : ∃ C : ℝ, 0 < C ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 0 true false 0 ((![1, 0, 0] : Zd 3 4) + Pi.single 0 1)
        - BATheta 3 4 P.g0 P.E P.m0 0 true false 0 (![1, 0, 0] : Zd 3 4)‖
      ≤ C * (P.g0 ^ 2 + |1 - (0 : ℝ)|)⁻¹
        * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baPropUnit1mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real 0 le_rfl (by norm_num)
    true false (by decide) ![1, 0, 0] 0⟩

/-- `baPropUnit2mixed_holds` at `t = 1/2`, `σ = (+,-)`, `a = (1, 0, 0) ≠ 0`, `i = j = 0`. -/
theorem inst_unit2 : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
    zdistD 3 4 (![1, 0, 0] : Zd 3 4) = 1 ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0
          ((![1, 0, 0] : Zd 3 4) + Pi.single 0 1 + Pi.single 0 1)
        - BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ((![1, 0, 0] : Zd 3 4) + Pi.single 0 1)
        - BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ((![1, 0, 0] : Zd 3 4) + Pi.single 0 1)
        + BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 (![1, 0, 0] : Zd 3 4)‖
      ≤ C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹
        * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := baPropUnit2mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, by decide, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      true false (by decide) ![1, 0, 0] 0 0⟩

/-- `baPropUnit2mixed_holds` at `σ = (-,+)`, `t = 1/100` (`ε ≥ 1`), `a = (2, 1, 0)` (`|a| = 3`),
mixed directions `(i, j) = (0, 2)`. -/
theorem inst_unit2_large_eps : ∃ C : ℝ, 0 < C ∧ zdistD 3 4 (![2, 1, 0] : Zd 3 4) = 3 ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 100) false true 0
          ((![2, 1, 0] : Zd 3 4) + Pi.single 0 1 + Pi.single 2 1)
        - BATheta 3 4 P.g0 P.E P.m0 (1 / 100) false true 0 ((![2, 1, 0] : Zd 3 4) + Pi.single 0 1)
        - BATheta 3 4 P.g0 P.E P.m0 (1 / 100) false true 0 ((![2, 1, 0] : Zd 3 4) + Pi.single 2 1)
        + BATheta 3 4 P.g0 P.E P.m0 (1 / 100) false true 0 (![2, 1, 0] : Zd 3 4)‖
      ≤ C * (P.g0 ^ 2 + |1 - (1 / 100 : ℝ)|)⁻¹
        * (((zdistD 3 4 (![2, 1, 0] : Zd 3 4) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := baPropUnit2mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 100) (by norm_num) (by norm_num)
      false true (by decide) ![2, 1, 0] 0 2⟩

/-- `baPropUnit2mixed_holds` at `t = 0` (`Θ_0 = 1`), `a = (1, 0, 0)`, mixed directions
`(i, j) = (0, 2)`. -/
theorem inst_unit2_zero : ∃ C : ℝ, 0 < C ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 0 true false 0
          ((![1, 0, 0] : Zd 3 4) + Pi.single 0 1 + Pi.single 2 1)
        - BATheta 3 4 P.g0 P.E P.m0 0 true false 0 ((![1, 0, 0] : Zd 3 4) + Pi.single 0 1)
        - BATheta 3 4 P.g0 P.E P.m0 0 true false 0 ((![1, 0, 0] : Zd 3 4) + Pi.single 2 1)
        + BATheta 3 4 P.g0 P.E P.m0 0 true false 0 (![1, 0, 0] : Zd 3 4)‖
      ≤ C * (P.g0 ^ 2 + |1 - (0 : ℝ)|)⁻¹
        * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := baPropUnit2mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real 0 le_rfl (by norm_num)
    true false (by decide) ![1, 0, 0] 0 2⟩

/-- The new Laplace lemma `baPropUnit_laplace_head` at `d = 3`, `n = 2`, `Λ = 10`, `g = 1`, `t = 1/2`,
`A = 1` (every deterministic hypothesis discharged; `ε = baP5Eps 1 (1/2) = 1`). -/
theorem inst_laplace_head : ∃ C : ℝ, 0 < C ∧
    IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps 1 (1 / 2)) * τ) *
        (min 1 (τ ^ (-(((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) / 2))
          * (1 + (1 : ℝ) ^ 2 / max τ 1) ^ (-(((3 / 2 + 1 : ℕ) : ℝ))))) (Ioi 0) ∧
    (baP5Gam 1 (1 / 2))⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps 1 (1 / 2)) * τ) *
        (min 1 (τ ^ (-(((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) / 2))
          * (1 + (1 : ℝ) ^ 2 / max τ 1) ^ (-(((3 / 2 + 1 : ℕ) : ℝ))))
      ≤ C * (((1 : ℝ) ^ 2 + (1 - 1 / 2))⁻¹ * ((((1 : ℝ) + 1) ^ (3 + 2 - 2))⁻¹)) := by
  obtain ⟨C, hC, H⟩ := baPropUnit_laplace_head 3 2 le_rfl (by norm_num) le_rfl (Λ := 10)
    (by norm_num)
  exact ⟨C, hC, H 1 (1 / 2) 1 one_pos (by norm_num) (by norm_num) (by norm_num) zero_le_one⟩

end PropUnitInst

end RBM.BA
