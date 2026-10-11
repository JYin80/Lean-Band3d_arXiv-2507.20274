/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.EKNonzero
import RBM3D.BA.EMn2BA
import RBM3D.BA.CombesThomas
import RBM3D.BA.GreenSchur
import RBM3D.BA.Prop6Path

/-!
# BA stage TL, row TL2b (T2429), part 1: the one-index kernel bounds and the decay of `K̃`

The deterministic kernel facts of the twisted tree (`docs/tickets/T2398-TL-proofs.md`): Lemma T.10 (a), (b), (d) for the
one-index kernel `Ũ_{v,u} = BAuKer v u` (the pins `BATwKerA`, `BATwKerFar`, `BATwKerZero` of `BA/TwistPins.lean:193-213`;
(c) is the merged `baEKSameRow_holds`), and Lemma T.1 (iii), the decay of `K̃` in `|a - c₁|` (new pin `BATwKDecay`).

* T.10 (a), (b) are proved from the public `EKPins_norm_uKer_le`, `EKPins_norm_Q_le`, `EKPins_norm_Theta_le` (their `private`
  is removed in `BA/EKPins.lean`, DECISIONS §153 (1), §161 (1)) and `baEKXiBall_holds`; (d) is the `A`-form of the merged
  private lemma `EKNonzero_norm_projMat_mul_uKer_le` (the merged one is at `A = 1`), written here with the helpers of
  `BA/EKNonzero.lean` made public.
* T.1 (iii) is the case split of `baComp_holds` (`BA/EMn2BA.lean:472`) for `Σ_{a'} Θ(a,a') M(c₂,a') M(a',c₁)` and the
  eventual absorption of `baEMn2ExpHK` (`BA/EMn2BA.lean:637`).

Private helpers carry the stem `TwistKer_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. T.10 (a), (b) -/

section Ker

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- `‖Ξ‖_{∞→∞} ≤ (u - v)/(1 - u)` (`Ξ = (u - v) M^{(σ₁σ₂)} Θ_u`; the twin of the private `EKSum_norm_Xi_le`, `BA/EKSum.lean:90`). -/
private theorem TwistKer_norm_Xi_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {v u : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u < 1)
    (σ₁ σ₂ : Bool) : ‖BAXi d L g E m v u σ₁ σ₂‖ ≤ (u - v) / (1 - u) := by
  have hu0 : 0 ≤ u := hv.trans hvu
  have hQ := EKPins_norm_Q_le hr σ₁ σ₂
  have hΘ := EKPins_norm_Theta_le hr hu0 hu σ₁ σ₂
  have hc : ‖(u : ℂ) - v‖ = u - v := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  unfold BAXi
  calc ‖((u : ℂ) - v) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m u σ₁ σ₂)‖
      ≤ ‖(u : ℂ) - v‖ * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m u σ₁ σ₂‖ := norm_smul_le _ _
    _ ≤ (u - v) * (‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖ * ‖BATheta d L g E m u σ₁ σ₂‖) := by
        rw [hc]; exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by linarith)
    _ ≤ (u - v) * (1 * (1 - u)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hQ hΘ (norm_nonneg _) zero_le_one) (by linarith)
    _ = (u - v) / (1 - u) := by rw [one_mul, div_eq_mul_inv]

/-- **T.10 (a)** from `EKPins_norm_uKer_le`: `‖Ũ_{v,u} ∘ A‖_∞ ≤ ((1-v)/(1-u)) ‖A‖_∞`. -/
theorem baTwKerA_holds (d : ℕ) (Λ κ : ℝ) : BATwKerA d Λ κ := by
  intro hd hΛ hκ L hL g hg hgΛ E m hr σ₁ σ₂ v u hv hvu hu A
  have : NeZero L := ⟨by omega⟩
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (EKPins_norm_uKer_le hr hv hvu hu σ₁ σ₂) (norm_nonneg _))

/-- **T.10 (b)** (`(D.6)`): near the anchor `c₁` the ball sums of `Ξ` (`baEKXiBall_holds` at `Λ' = W^ε`, `R = W^ε ℓ_v`), far from it
`‖A b‖ ≤ W^{-D}` and `‖Ξ‖_{∞→∞} ≤ (u-v)/(1-u) ≤ (1-v)/(1-u) ≤ W`.  The constant is that of `baEKXiBall_holds`. -/
theorem baTwKerFar_holds (d : ℕ) (Λ κ : ℝ) : BATwKerFar d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨CX, hCX, hX⟩ := baEKXiBall_holds d Λ κ hd hΛ hκ
  refine ⟨CX, hCX, ?_⟩
  intro L hL g hg hgΛ W ε D hW1 hε0 hε1 hD v u hv hvu hu hWu E m hr σ₁ σ₂ c₁ A hA
  have : NeZero L := ⟨by omega⟩
  have hW0 : 0 < W := by linarith
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hgL : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
  have hu1 : u < 1 := by linarith
  have hu0 : 0 ≤ u := hv.trans hvu
  have hv1 : v < 1 := lt_of_le_of_lt hvu hu1
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hρ : 1 ≤ W ^ ε := Real.one_le_rpow hW1.le hε0.le
  have hℓ : 1 ≤ ellT L g v := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ L))
  set ρ : ℝ := W ^ ε with hρdef
  set ℓ : ℝ := ellT L g v with hℓdef
  set r : ℝ := (g ^ 2 + |1 - v|) / (g ^ 2 + |1 - u|) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hR1 : 1 ≤ ρ * ℓ := by nlinarith
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hXi := TwistKer_norm_Xi_le hr hv hvu hu1 σ₁ σ₂
  have hXiW : (u - v) / (1 - u) ≤ W := by
    have h1 : (u - v) / (1 - u) ≤ (1 - v) / (1 - u) :=
      div_le_div_of_nonneg_right (by linarith) h1u.le
    have h2 : ((1 - u) / (1 - v))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWu
    rw [inv_div] at h2
    exact h1.trans h2
  have hrow : ∀ a, ∑ b, ‖BAXi d L g E m v u σ₁ σ₂ a b‖ ≤ W :=
    fun a => ((sum_norm_row_le _ a).trans hXi).trans hXiW
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro a
  have hcomp : (BAuKer d L g E m v u σ₁ σ₂ *ᵥ A) a =
      A a + ∑ b, BAXi d L g E m v u σ₁ σ₂ a b * A b := by
    rw [BAuKer_eq_one_add_Xi hr hu0 hu1 σ₁ σ₂]
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    simp
  rw [hcomp]
  set nr : Finset (Zd d L) := Finset.univ.filter fun b => (zdistD d L (b - c₁) : ℝ) < ρ * ℓ with hnr
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Zd d L))
    (fun b => (zdistD d L (b - c₁) : ℝ) < ρ * ℓ) (fun b => ‖BAXi d L g E m v u σ₁ σ₂ a b‖ * ‖A b‖)
  have hnear : ∑ b ∈ nr, ‖BAXi d L g E m v u σ₁ σ₂ a b‖ * ‖A b‖ ≤ ‖A‖ * (CX * ρ ^ 2 * r) := by
    have hb := hX L hL g hg hgΛ E m hr v u hv hvu hu1 (by linarith) σ₁ σ₂ ρ hρ (ρ * ℓ) hR1 le_rfl a c₁ nr (by
      intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      rw [← neg_sub b c₁, zdistD_neg]
      exact hb'.le)
    calc ∑ b ∈ nr, ‖BAXi d L g E m v u σ₁ σ₂ a b‖ * ‖A b‖
        ≤ ∑ b ∈ nr, ‖BAXi d L g E m v u σ₁ σ₂ a b‖ * ‖A‖ :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm A b) (norm_nonneg _)
      _ = (∑ b ∈ nr, ‖BAXi d L g E m v u σ₁ σ₂ a b‖) * ‖A‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ (CX * ρ ^ 2 * r) * ‖A‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = ‖A‖ * (CX * ρ ^ 2 * r) := mul_comm _ _
  have hfar : ∑ b ∈ Finset.univ.filter (fun b => ¬ (zdistD d L (b - c₁) : ℝ) < ρ * ℓ), ‖BAXi d L g E m v u σ₁ σ₂ a b‖ * ‖A b‖ ≤
      W ^ (-D + 1) := by
    calc _ ≤ ∑ b ∈ Finset.univ.filter (fun b => ¬ (zdistD d L (b - c₁) : ℝ) < ρ * ℓ), ‖BAXi d L g E m v u σ₁ σ₂ a b‖ * W ^ (-D) := by
          refine Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hA b ?_) (norm_nonneg _)
          exact not_lt.mp (Finset.mem_filter.mp hb).2
      _ = (∑ b ∈ Finset.univ.filter (fun b => ¬ (zdistD d L (b - c₁) : ℝ) < ρ * ℓ), ‖BAXi d L g E m v u σ₁ σ₂ a b‖) * W ^ (-D) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ W * W ^ (-D) := by
          refine mul_le_mul_of_nonneg_right ?_ hWD
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)).trans (hrow a)
      _ = W ^ (-D + 1) := by
          rw [Real.rpow_add hW0, Real.rpow_one, mul_comm]
  have hsum : ‖∑ b, BAXi d L g E m v u σ₁ σ₂ a b * A b‖ ≤ ‖A‖ * (CX * ρ ^ 2 * r) + W ^ (-D + 1) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul]
    rw [← hsplit]
    exact add_le_add hnear hfar
  have hW2 : W ^ (2 * ε) = ρ ^ 2 := by
    rw [mul_comm, Real.rpow_mul hW0.le, hρdef]; norm_cast
  calc ‖A a + ∑ b, BAXi d L g E m v u σ₁ σ₂ a b * A b‖ ≤ ‖A a‖ + ‖∑ b, BAXi d L g E m v u σ₁ σ₂ a b * A b‖ := norm_add_le _ _
    _ ≤ ‖A‖ + (‖A‖ * (CX * ρ ^ 2 * r) + W ^ (-D + 1)) := add_le_add (norm_le_pi_norm A a) hsum
    _ = (1 + CX * W ^ (2 * ε) * r) * ‖A‖ + W ^ (-D + 1) := by rw [hW2]; ring

end Ker

/-! ## 2. T.10 (d), the `A`-form: `‖Proj · Ũ_{v,u}‖ ≤ 2 + A C₀ E_k` for `(1 - v) L² ≤ A g²` -/

section Zero

open scoped Matrix.Norms.Operator

variable {k L : ℕ} [NeZero L]

omit [NeZero L] in
/-- `(u - v) (g² + |1-u|)⁻¹ L² ≤ A` for `(1 - v) L² ≤ A g²`, `v ≤ u < 1` (`EKNonzero_coef` is the case `A = 1`, `hsg`). -/
private theorem TwistKer_coef {g v u A : ℝ} (hg : 0 < g) (hL : 3 ≤ L) (hvA : (1 - v) * (L : ℝ) ^ 2 ≤ A * g ^ 2)
    (hvu : v ≤ u) (hu : u < 1) : (u - v) * ((g ^ 2 + |1 - u|)⁻¹ * (L : ℝ) ^ 2) ≤ A := by
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  have h1 : (g ^ 2 + |1 - u|)⁻¹ ≤ (g ^ 2)⁻¹ :=
    inv_anti₀ hg2 (by have := abs_nonneg (1 - u); linarith)
  have h2 : u - v ≤ 1 - v := by linarith
  have h3 : (g ^ 2 + |1 - u|)⁻¹ * (L : ℝ) ^ 2 ≤ (g ^ 2)⁻¹ * (L : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  calc (u - v) * ((g ^ 2 + |1 - u|)⁻¹ * (L : ℝ) ^ 2)
      ≤ (1 - v) * ((g ^ 2)⁻¹ * (L : ℝ) ^ 2) := mul_le_mul h2 h3 (by positivity) (by linarith)
    _ = ((1 - v) * (L : ℝ) ^ 2) / g ^ 2 := by field_simp
    _ ≤ A := by rw [div_le_iff₀ hg2]; exact hvA

/-- The `A`-form of the private `EKNonzero_norm_projMat_mul_uKer_le` (`BA/EKNonzero.lean:191`; same proof, `hsg : 1 - g²/L² ≤ s` replaced by
`(1 - s) L² ≤ A g²` and `EKNonzero_coef` by `TwistKer_coef`): `‖Proj Ũ_{v,u}‖ ≤ 2 + A C₀ E_k`. -/
private theorem TwistKer_norm_projMat_mul_uKer_le {κ C₀ g E A : ℝ} {m : ℂ} (hC₀ : 0 < C₀) (hA : 0 < A) (hL : 3 ≤ L)
    (hg : 0 < g) (hr : BAReal (k + 2) L g κ E m) {v u : ℝ} (hv : 0 ≤ v)
    (hvA : (1 - v) * (L : ℝ) ^ 2 ≤ A * g ^ 2) (hvu : v ≤ u) (hu : u < 1) (σ₁ σ₂ : Bool)
    (hbd : ∀ a : Zd (k + 2) L, ‖BATheta0 (k + 2) L g E m u σ₁ σ₂ 0 a‖
      ≤ C₀ * (g ^ 2 + |1 - u|)⁻¹ * (((zdistD (k + 2) L a : ℝ) + 1) ^ (k + 2 - 2))⁻¹) :
    ‖projMat (k + 2) L * BAuKer (k + 2) L g E m v u σ₁ σ₂‖ ≤ 2 + A * (C₀ * EKNonzero_E k) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  have hu0 : 0 ≤ u := hv.trans hvu
  have hE0 := EKNonzero_E_pos k
  have hTheta0 : ‖BATheta0 (k + 2) L g E m u σ₁ σ₂‖
      ≤ C₀ * (g ^ 2 + |1 - u|)⁻¹ * (EKNonzero_E k * (L : ℝ) ^ 2) := by
    refine (norm_le_sum_row_zero _ (fun a b c => EKNonzero_Theta0_shift g E m u σ₁ σ₂ a b c)).trans ?_
    calc ∑ b : Zd (k + 2) L, ‖BATheta0 (k + 2) L g E m u σ₁ σ₂ 0 b‖
        ≤ ∑ b : Zd (k + 2) L, C₀ * (g ^ 2 + |1 - u|)⁻¹
            * (((zdistD (k + 2) L b : ℝ) + 1) ^ (k + 2 - 2))⁻¹ :=
          Finset.sum_le_sum fun b _ => hbd b
      _ = C₀ * (g ^ 2 + |1 - u|)⁻¹
            * ∑ b : Zd (k + 2) L, (((zdistD (k + 2) L b : ℝ) + 1) ^ k)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by norm_num
      _ ≤ C₀ * (g ^ 2 + |1 - u|)⁻¹ * (EKNonzero_E k * (L : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := sum_radial_pow_le (L := L) k hL1
          unfold EKNonzero_E
          rw [mul_assoc]
          exact this
  have hcoef := TwistKer_coef hg hL hvA hvu hu
  have hsplit : projMat (k + 2) L * BAuKer (k + 2) L g E m v u σ₁ σ₂
      = projMat (k + 2) L + ((u : ℂ) - v) •
        (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ * BATheta0 (k + 2) L g E m u σ₁ σ₂) := by
    rw [BAuKer_eq_one_add hr hu0 hu, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, EKNonzero_projMat_comm (fun a b r => EKNonzero_Mss_shift g E m σ₁ σ₂ a b r),
      Matrix.mul_assoc, EKNonzero_projMat_mul_Theta]
  rw [hsplit]
  have hQ := EKPins_norm_Q_le hr σ₁ σ₂
  have hsmul := norm_smul_le ((u : ℂ) - v)
    (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ * BATheta0 (k + 2) L g E m u σ₁ σ₂)
  have hmul := norm_mul_le (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂)
    (BATheta0 (k + 2) L g E m u σ₁ σ₂)
  have hmul' : ‖BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ * BATheta0 (k + 2) L g E m u σ₁ σ₂‖
      ≤ ‖BATheta0 (k + 2) L g E m u σ₁ σ₂‖ := by
    refine hmul.trans ?_
    calc _ ≤ 1 * ‖BATheta0 (k + 2) L g E m u σ₁ σ₂‖ := mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
      _ = _ := one_mul _
  have hc : ‖(u : ℂ) - v‖ = u - v := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hterm : ‖((u : ℂ) - v) • (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ *
      BATheta0 (k + 2) L g E m u σ₁ σ₂)‖ ≤ A * (C₀ * EKNonzero_E k) := by
    calc _ ≤ (u - v) * ‖BATheta0 (k + 2) L g E m u σ₁ σ₂‖ := by
          rw [← hc]
          exact hsmul.trans (mul_le_mul_of_nonneg_left hmul' (norm_nonneg _))
      _ ≤ (u - v) * (C₀ * (g ^ 2 + |1 - u|)⁻¹ * (EKNonzero_E k * (L : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hTheta0 (by linarith)
      _ = (C₀ * EKNonzero_E k) * ((u - v) * ((g ^ 2 + |1 - u|)⁻¹ * (L : ℝ) ^ 2)) := by ring
      _ ≤ (C₀ * EKNonzero_E k) * A := mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = A * (C₀ * EKNonzero_E k) := mul_comm _ _
  calc _ ≤ ‖projMat (k + 2) L‖ + ‖((u : ℂ) - v) • (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ *
        BATheta0 (k + 2) L g E m u σ₁ σ₂)‖ := norm_add_le _ _
    _ ≤ 2 + A * (C₀ * EKNonzero_E k) := add_le_add norm_projMat_le hterm

/-- **T.10 (d)** for every `A > 0` (the zero mode; `C(A) = 2 + A C₀ E_k` with `C₀` of `baProp8_holds`, `E_k` the radial-sum constant): the merged lemma
is the case `A = 1` (`hsg`).  `(1 - v) L² ≤ A g²` is the regime, `Q^{(1)} = projMat`. -/
theorem baTwKerZero_holds (d : ℕ) (Λ κ : ℝ) : BATwKerZero d Λ κ := by
  intro hd hΛ hκ A hA
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨C₀, hC₀, hbd⟩ := baProp8_holds (k + 2) Λ κ hd hΛ hκ
  have hE0 := EKNonzero_E_pos k
  refine ⟨2 + A * (C₀ * EKNonzero_E k), by positivity, ?_⟩
  intro L hL g hg hgΛ E m hr σ₁ σ₂ v u hv hvA hvu hu
  have : NeZero L := ⟨by omega⟩
  exact TwistKer_norm_projMat_mul_uKer_le hC₀ hA hL hg hr hv hvA hvu hu σ₁ σ₂
    (fun a => hbd L hL g hg hgΛ E m hr u (hv.trans hvu) hu σ₁ σ₂ a)

end Zero

/-! ## 3. T.1 (iii): the decay of `K̃` in `|a - c₁|` -/

section Decay

variable {d L : ℕ} [NeZero L]

/-- `|M(σ)_{ab}| = |M^{(B)}_{ab}|` (`M(-) = (M^{(B)})^*`, `M^{(B)}` symmetric; a copy of the private `TwistPins_norm_sigma`, `BA/TwistPins.lean:517`). -/
private theorem TwistKer_norm_sigma (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b‖ = ‖BAMB d L g (E : ℂ) m a b‖ := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.norm_conj]
    rw [BAMB_symm d L g (E : ℂ) m b a]
  · simp only [BAMsigma, ite_true]

omit [NeZero L] in
/-- The case split of `baComp_holds` (`BA/EMn2BA.lean:472`) for the twisted sum `Σ_{a'} Θ(a,a') M(c₂,a') M(a',c₁)`: if `|a - c₁| ≥ 2y` then either
`|a - a'| ≥ y` (`Θ` carries `e^{-c₅ y/ℓ}`, Property 5) or `|a' - c₁| ≥ y` (`M` carries `e^{-c₀ y}`, `BAMB_decay_large`, and `ℓ ≥ 1`); the other factors are
bounded by `B_{t,K} ≤ 2(1-t)⁻¹` (`EMn2BA_bparam_le`) and `|M| ≤ c₀⁻¹`, and `Σ_{a'} |M(c₂,a')| ≤ C_M` (`BAMB_row_l1`). -/
private theorem TwistKer_tree_core {k : ℕ} (hd : 3 ≤ k + 2) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      BAReal (k + 2) L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₁ σ₂ : Bool) (a c₁ c₂ : Zd (k + 2) L) (y : ℝ), 0 ≤ y →
        2 * y ≤ (zdistD (k + 2) L (a - c₁) : ℝ) →
        ‖∑ a', BATheta (k + 2) L g E m t σ₁ σ₂ a a' * BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a' *
            BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₂ a' c₁‖ ≤ C * (1 - t)⁻¹ * Real.exp (-(c * y / ellT L g t)) := by
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := baProp5_holds (k + 2) Λ κ hd hΛ hκ
  have hc₀ := BAct_rate_pos (k + 2) Λ κ (by omega) hΛ hκ
  set c₀ := BAct_rate (k + 2) Λ κ with hc₀def
  have hCM : 0 < c₀⁻¹ * expC k c₀ := by unfold expC; positivity
  set CM : ℝ := c₀⁻¹ * expC k c₀ with hCMdef
  refine ⟨2 * C₅ * c₀⁻¹ * CM, min c₅ c₀, by positivity, lt_min hc₅ hc₀, ?_⟩
  intro L _ hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ a c₁ c₂ y hy hay
  set ℓ : ℝ := ellT L g t with hℓdef
  have hℓ1 : 1 ≤ ℓ := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ L))
  have hℓ0 : 0 < ℓ := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hinv0 : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr h1t.le
  set c := min c₅ c₀ with hcdef
  have hc1 : c ≤ c₅ := min_le_left _ _
  have hc2 : c ≤ c₀ := min_le_right _ _
  have hcpos : 0 < c := lt_min hc₅ hc₀
  set Ev : ℝ := Real.exp (-(c * y / ℓ)) with hEv
  have hEv0 : 0 < Ev := Real.exp_pos _
  have hEv1 : Ev ≤ 1 := by
    rw [hEv]; refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ c * y / ℓ := by positivity
    linarith
  set K : ℝ := 2 * C₅ * c₀⁻¹ * (1 - t)⁻¹ * Ev with hK
  have hpt : ∀ a' : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a' * BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a' *
      BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₂ a' c₁‖ ≤ K * ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ := by
    intro a'
    rw [norm_mul, norm_mul, TwistKer_norm_sigma, TwistKer_norm_sigma]
    set r : ℕ := zdistD (k + 2) L (a - a') with hr_def
    set s : ℕ := zdistD (k + 2) L (a' - c₁) with hs_def
    have hadd : zdistD (k + 2) L (a - c₁) ≤ r + s := by
      have := zdistD_add_le (k + 2) L (a - a') (a' - c₁)
      rwa [show a - a' + (a' - c₁) = a - c₁ by ring] at this
    have hrs : 2 * y ≤ (r : ℝ) + (s : ℝ) := by
      have : (zdistD (k + 2) L (a - c₁) : ℝ) ≤ ((r + s : ℕ) : ℝ) := by exact_mod_cast hadd
      push_cast at this
      linarith
    have hΘ0 : 0 ≤ ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a'‖ := norm_nonneg _
    -- the bounds of the two factors
    have hΘ := H5 L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ (a' - a)
    have hdist : zdistD (k + 2) L (a' - a) = r := by rw [hr_def, ← neg_sub a a', zdistD_neg]
    rw [hdist, ← EMn2BA_theta_shift] at hΘ
    have hB := EMn2BA_bparam_le (k + 2) L (by omega) g ht1 r
    have hΘsup : ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a'‖ ≤ 2 * C₅ * (1 - t)⁻¹ := by
      refine hΘ.trans ?_
      have hexp : Real.exp (-c₅ * (r : ℝ) / ℓ) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have : 0 ≤ c₅ * (r : ℝ) / ℓ := by positivity
        rw [neg_mul, neg_div]; linarith
      calc C₅ * Bparam (k + 2) L g t r * Real.exp (-c₅ * (r : ℝ) / ℓ)
          ≤ C₅ * (2 * (1 - t)⁻¹) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hB hC₅.le) hexp (Real.exp_pos _).le (by positivity)
        _ = 2 * C₅ * (1 - t)⁻¹ := by ring
    have hM := BAMB_decay_large (k + 2) L hL (by omega) Λ g κ E m hΛ hg hgΛ hκ hr a' c₁
    have hMsup : ‖BAMB (k + 2) L g (E : ℂ) m a' c₁‖ ≤ c₀⁻¹ := by
      refine hM.trans ?_
      have : Real.exp (-c₀ * (s : ℝ)) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have : 0 ≤ c₀ * (s : ℝ) := by positivity
        linarith
      calc c₀⁻¹ * Real.exp (-c₀ * (s : ℝ)) ≤ c₀⁻¹ * 1 := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hc₀.le)
        _ = c₀⁻¹ := mul_one _
    have hM0 : 0 ≤ ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ := norm_nonneg _
    have hM20 : 0 ≤ ‖BAMB (k + 2) L g (E : ℂ) m a' c₁‖ := norm_nonneg _
    have hy2 : y ≤ (r : ℝ) ∨ y ≤ (s : ℝ) := by
      by_contra hcon
      push Not at hcon
      linarith [hcon.1, hcon.2]
    have hcy : c * y / ℓ ≤ c * y := by
      rw [div_le_iff₀ hℓ0]; nlinarith [mul_nonneg hcpos.le hy]
    calc ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a'‖ * ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ * ‖BAMB (k + 2) L g (E : ℂ) m a' c₁‖
        ≤ (2 * C₅ * (1 - t)⁻¹ * Ev) * ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ * c₀⁻¹ := by
          rcases hy2 with hyr | hys
          · -- `Θ` carries the decay
            have hΘd : ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a'‖ ≤ 2 * C₅ * (1 - t)⁻¹ * Ev := by
              refine hΘ.trans ?_
              have hexp : Real.exp (-c₅ * (r : ℝ) / ℓ) ≤ Ev := by
                rw [hEv]; refine Real.exp_le_exp.mpr ?_
                rw [neg_mul, neg_div, neg_le_neg_iff]
                have : c * y / ℓ ≤ c₅ * (r : ℝ) / ℓ := by
                  refine div_le_div_of_nonneg_right ?_ hℓ0.le
                  nlinarith [mul_le_mul hc1 hyr hy hc₅.le]
                exact this
              calc C₅ * Bparam (k + 2) L g t r * Real.exp (-c₅ * (r : ℝ) / ℓ)
                  ≤ C₅ * (2 * (1 - t)⁻¹) * Ev :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hB hC₅.le) hexp (Real.exp_pos _).le (by positivity)
                _ = 2 * C₅ * (1 - t)⁻¹ * Ev := by ring
            calc _ ≤ (2 * C₅ * (1 - t)⁻¹ * Ev) * ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ * ‖BAMB (k + 2) L g (E : ℂ) m a' c₁‖ :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΘd hM0) hM20
              _ ≤ _ := mul_le_mul_of_nonneg_left hMsup (by positivity)
          · -- `M(a', c₁)` carries the decay
            have hMd : ‖BAMB (k + 2) L g (E : ℂ) m a' c₁‖ ≤ c₀⁻¹ * Ev := by
              refine hM.trans ?_
              refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hc₀.le)
              rw [hEv]; refine Real.exp_le_exp.mpr ?_
              rw [neg_mul, neg_le_neg_iff]
              nlinarith [mul_le_mul hc2 hys hy hc₀.le]
            calc _ ≤ (2 * C₅ * (1 - t)⁻¹) * ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ * (c₀⁻¹ * Ev) :=
                  mul_le_mul (mul_le_mul_of_nonneg_right hΘsup hM0) hMd hM20 (by positivity)
              _ = _ := by ring
      _ = K * ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ := by rw [hK]; ring
  have hrow := BAMB_row_l1 k L hL Λ g κ E m hΛ hg hgΛ hκ hr c₂
  have hK0 : 0 ≤ K := by positivity
  calc _ ≤ ∑ a', ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a' * BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a' *
            BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₂ a' c₁‖ := norm_sum_le _ _
    _ ≤ ∑ a', K * ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ := Finset.sum_le_sum fun a' _ => hpt a'
    _ = K * ∑ a', ‖BAMB (k + 2) L g (E : ℂ) m c₂ a'‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ K * CM := mul_le_mul_of_nonneg_left hrow hK0
    _ = 2 * C₅ * c₀⁻¹ * CM * (1 - t)⁻¹ * Real.exp (-(c * y / ℓ)) := by rw [hK, hEv]; ring

/-- `K x^A ≤ e^{c x^{ε₁}}` for large `x` (`x^s = o(e^{b x})` at `x^{ε₁}`; the pattern of `EMn2BAInst_far_ev`, `BA/EMn2BA.lean:918`). -/
private theorem TwistKer_absorb {A c ε₁ K : ℝ} (hc : 0 < c) (hε₁ : 0 < ε₁) :
    ∀ᶠ x : ℝ in atTop, K * x ^ A ≤ Real.exp (c * x ^ ε₁) := by
  have hlo := (isLittleO_rpow_exp_pos_mul_atTop (A / ε₁) hc).def (c := 1 / (|K| + 1)) (by positivity)
  have hy : Tendsto (fun x : ℝ => x ^ ε₁) atTop atTop := tendsto_rpow_atTop hε₁
  filter_upwards [hy.eventually hlo, eventually_gt_atTop 0] with x hx hx0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hx0.le _) _),
    Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.rpow_mul hx0.le, mul_div_cancel₀ _ hε₁.ne'] at hx
  have hK : 0 < |K| + 1 := by positivity
  have hxA : 0 ≤ x ^ A := Real.rpow_nonneg hx0.le _
  calc K * x ^ A ≤ |K| * x ^ A := mul_le_mul_of_nonneg_right (le_abs_self K) hxA
    _ ≤ (|K| + 1) * x ^ A := by nlinarith
    _ ≤ (|K| + 1) * (1 / (|K| + 1) * Real.exp (c * x ^ ε₁)) := mul_le_mul_of_nonneg_left hx hK.le
    _ = Real.exp (c * x ^ ε₁) := by field_simp

/-- `(1 - v)⁻¹ ≤ 2 W^{1/𝔠}` for `v ≤ t₀_n` once `N^𝔠 ≤ W` (`1 - t₀ ≥ Im z/2 ≥ N^{-1}/2`; the block `hamp` of `baEMn2ExpHK`, `BA/EMn2BA.lean:661`). -/
private theorem TwistKer_amp {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔠 : 0 < 𝔠) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (hBn : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) {v : ℝ}
    (hv : v ≤ BAflowT0 sz z n) : (1 - v)⁻¹ ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
  have hNpos : 0 < sz.size n := by
    unfold Sizes.size
    exact pow_pos (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega)) d
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have hNim' : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hT := EMn2BA_one_sub_T0 hκ sz hflow n
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2 ≤ 1 - v := by linarith
  have h3 : (1 - v)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2)⁻¹ := inv_anti₀ (by positivity) h2
  have h4 : (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2)⁻¹ = 2 * ((sz.size n : ℕ) : ℝ) := by
    rw [Real.rpow_neg_one]; field_simp
  have h5 : ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
    have := sz.size_rpow_le_W_rpow h𝔠 n hBn (τ := 1) zero_le_one
    rwa [Real.rpow_one] at this
  rw [h4] at h3
  linarith

/-- **T.1 (iii)** (`TP:37-38`; paper `Def_decay`, `3_5:1115-1120`): the twisted tree `K̃_{σ,(a;c₁,c₂)}` (`twK` at the carrier `baFMz sz z`; its kernels are at the flow
coupling `g₀ = BAflowLam0 sz z n = √t₀ · sz.lam n`) is `≤ W^{-D}` when `|a - c₁| ≥ W^{ε₁} ℓ_v`, for every `ε₁, D > 0` and every large `n`, uniformly in
`v ∈ [0, t₀]`, `σ`, `a`, `c₁`, `c₂`.  The cut is at the model scale `ellT (sz.L n) (sz.lam n) v` and in `zdistInf`, exactly as `twDec` (T.11 (v)); the step to the
kernel's own scale is `ℓ_v(g₀) ≤ ℓ_v(lam)` (`EMn2BA_ellT_mono_g`).  The constants of the proof (Property 5, `BAMB_decay_large`) and the polynomial size of `B_{v,0}`
are absorbed by `e^{-c W^{ε₁}}` for `n` large (`W_n → ∞`); no `∃ C` stays in the statement. -/
def BATwKDecay (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ ε₁ D : ℝ, 0 < ε₁ → 0 < D →
      ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ BAflowT0 sz z n → ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
        ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ) →
        ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **T.1 (iii) is proved** (`TwistKer_tree_core` at `Λ = 𝔡⁻¹`, `y = W^{ε₁} ℓ_v(g₀)/2`; `ℓ_v(g₀) ≤ ℓ_v(lam)`; `(1-v)⁻¹ ≤ 2 W^{1/𝔠}`; `W^{D + 1/𝔠} ≲ e^{c W^{ε₁}/2}`). -/
theorem baTwKDecay_holds (d : ℕ) : BATwKDecay d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow ε₁ D hε₁ hD
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨C, c, hC, hc, H⟩ := TwistKer_tree_core hd hΛ hκ
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hNc : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop := (tendsto_rpow_atTop h𝔠).comp hsz
  have hWtop : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := tendsto_atTop_mono' _ hband hNc
  have habs := hWtop.eventually (TwistKer_absorb (A := D + 1 / 𝔠) (K := 2 * C) (half_pos hc) hε₁)
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, hband, habs] with n hlam hBn hab
  intro v hv0 hvT σ a c₁ c₂ hcut
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  obtain ⟨hg0, hgΛ⟩ := hlam
  have hv1 : v < 1 := lt_of_le_of_lt hvT (EMn2BA_T0_lt_one hκ sz hflow n)
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hL3 := sz.three_le_L n
  have hlam_le : BAflowLam0 sz z n ≤ sz.lam n := by
    have h1 : Real.sqrt (BAflowT0 sz z n) ≤ 1 :=
      Real.sqrt_le_one.mpr (EMn2BA_T0_lt_one hκ sz hflow n).le
    have e : BAflowLam0 sz z n = Real.sqrt (BAflowT0 sz z n) * sz.lam n := rfl
    have hlam : 0 < sz.lam n := by
      by_contra hneg
      push Not at hneg
      have := mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg (BAflowT0 sz z n)) hneg
      linarith
    rw [e]
    nlinarith
  -- the cut at the kernel's scale
  set ℓ₀ : ℝ := ellT (sz.L n) (BAflowLam0 sz z n) v with hℓ₀
  have hℓ₀1 : 1 ≤ ℓ₀ := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  have hℓ₀0 : 0 < ℓ₀ := by linarith
  have hmono : ℓ₀ ≤ ellT (sz.L n) (sz.lam n) v := EMn2BA_ellT_mono_g (sz.L n) hlam_le v
  have hWε : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hWpos.le _
  have hcut' : 2 * (((sz.W n : ℕ) : ℝ) ^ ε₁ * ℓ₀ / 2) ≤ (zdistD (k + 2) (sz.L n) (a - c₁) : ℝ) := by
    have h1 : ((sz.W n : ℕ) : ℝ) ^ ε₁ * ℓ₀ ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) v :=
      mul_le_mul_of_nonneg_left hmono hWε
    have h2 : (zdistInf (k + 2) (sz.L n) (a - c₁) : ℝ) ≤ (zdistD (k + 2) (sz.L n) (a - c₁) : ℝ) := by
      exact_mod_cast zdistInf_le_zdistD (k + 2) (sz.L n) (a - c₁)
    linarith
  have hy0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁ * ℓ₀ / 2 := by positivity
  have hmain := H (sz.L n) hL3 (BAflowLam0 sz z n) hg0 hgΛ (BAflowEs sz z n) _ hr v hv0 hv1 (σ 0) (σ 1) a c₁ c₂
    (((sz.W n : ℕ) : ℝ) ^ ε₁ * ℓ₀ / 2) hy0 hcut'
  set X : ℝ := c / 2 * ((sz.W n : ℕ) : ℝ) ^ ε₁ with hX
  have hexp : c * (((sz.W n : ℕ) : ℝ) ^ ε₁ * ℓ₀ / 2) / ℓ₀ = X := by
    rw [hX]; field_simp
  rw [hexp] at hmain
  have hnorm : ‖twK (baFMz sz z) n v σ a c₁ c₂‖ = (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ *
      ‖∑ a', BATheta (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (σ 0) (σ 1) a a' *
        BAMsigma (k + 2) (sz.L n) (BAMB (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' *
        BAMsigma (k + 2) (sz.L n) (BAMB (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁‖ := by
    rw [twK_ba z n hr.1.1 v σ a c₁ c₂, norm_mul]
    simp
  have hamp := TwistKer_amp hκ hε h𝔠 sz hflow n hBn hvT
  have hWinv : (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have hW1c : 2 * C * ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) ≤ Real.exp X * ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have e1 : ((sz.W n : ℕ) : ℝ) ^ (D + 1 / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-D) = ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
      rw [← Real.rpow_add hWpos]; ring_nf
    have e : 2 * C * ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) = (2 * C * ((sz.W n : ℕ) : ℝ) ^ (D + 1 / 𝔠)) * ((sz.W n : ℕ) : ℝ) ^ (-D) := by
      rw [mul_assoc (2 * C), e1]
    rw [e]
    exact mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hWpos.le _)
  calc ‖twK (baFMz sz z) n v σ a c₁ c₂‖ = _ := hnorm
    _ ≤ 1 * (C * (1 - v)⁻¹ * Real.exp (-X)) := mul_le_mul hWinv hmain (norm_nonneg _) zero_le_one
    _ ≤ (2 * C * ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠)) * Real.exp (-X) := by
        rw [one_mul]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        calc C * (1 - v)⁻¹ ≤ C * (2 * ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠)) := mul_le_mul_of_nonneg_left hamp hC.le
          _ = _ := by ring
    _ ≤ (Real.exp X * ((sz.W n : ℕ) : ℝ) ^ (-D)) * Real.exp (-X) := mul_le_mul_of_nonneg_right hW1c (Real.exp_pos _).le
    _ = ((sz.W n : ℕ) : ℝ) ^ (-D) := by
        rw [Real.exp_neg]; field_simp

end Decay

/-! ## 4. The instances (`d = 3`; targets 1 at the flow point `Pf` of `(L, g) = (4, 1/2)`, target 2 at `sz0`, `zSeq`, `flow_sz0`) -/

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.MFixedPointInst
open scoped Matrix.Norms.Operator

/-- The flow point of `(L, g) = (4, 1/2)` (`BA/MFixedPoint.lean:877-885`: `0 < Pf.g0 ≤ 1/2`, `BAReal`, `κ = Im Pf.m0`, `Λ = 1`). -/
private def TwistKer_Pf : FlowPt 4 (1 / 2) := (exists_flowPt 4 (g := 1 / 2) (by norm_num)).some

/-- T.10 (a) at `Pf`, `v = 0 < u = 1/2`, `A = δ₀ ≠ 0`, charges `(-,+)`. -/
example : ∃ A : Zd 3 4 → ℂ, A ≠ 0 ∧ ‖BAuKer 3 4 TwistKer_Pf.g0 TwistKer_Pf.E TwistKer_Pf.m0 0 (1 / 2) false true *ᵥ A‖ ≤ (1 - 0) / (1 - 1 / 2) * ‖A‖ :=
  ⟨fun x => if x = 0 then 1 else 0, fun hA => by simpa using congrFun hA 0,
    baTwKerA_holds 3 1 TwistKer_Pf.m0.im le_rfl one_pos TwistKer_Pf.real.1.1 4 (by norm_num) TwistKer_Pf.g0 TwistKer_Pf.g0_pos
      (TwistKer_Pf.g0_le.trans (by norm_num)) TwistKer_Pf.E TwistKer_Pf.m0 TwistKer_Pf.real false true 0 (1 / 2) le_rfl (by norm_num) (by norm_num) _⟩

/-- T.10 (b) at `Pf`: `W = 16`, `ε = 1/2`, `D = 2`, `v = 0`, `u = 1/2`, anchor `c₁ = 0`, `A = δ₀` (`‖A b‖ ≤ W^{-D}` off the near set `{|b| < W^ε ℓ_v}`, which contains `0`). -/
example : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ A : Zd 3 4 → ℂ, A ≠ 0 ∧ ‖BAuKer 3 4 TwistKer_Pf.g0 TwistKer_Pf.E TwistKer_Pf.m0 0 (1 / 2) false true *ᵥ A‖ ≤
    (1 + C₁ * (16 : ℝ) ^ (2 * (1 / 2 : ℝ)) * ((TwistKer_Pf.g0 ^ 2 + |1 - 0|) / (TwistKer_Pf.g0 ^ 2 + |1 - 1 / 2|))) * ‖A‖ + (16 : ℝ) ^ (-2 + 1 : ℝ) := by
  obtain ⟨C₁, hC₁, H⟩ := baTwKerFar_holds 3 1 TwistKer_Pf.m0.im le_rfl one_pos TwistKer_Pf.real.1.1
  have hg := TwistKer_Pf.g0_pos; have hg2 := TwistKer_Pf.g0_le
  refine ⟨C₁, hC₁, fun x => if x = 0 then 1 else 0, fun hA => by simpa using congrFun hA 0, H 4 (by norm_num) TwistKer_Pf.g0 hg (hg2.trans (by norm_num)) 16 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 (1 / 2) le_rfl (by norm_num) (by norm_num; nlinarith) (by norm_num) TwistKer_Pf.E TwistKer_Pf.m0 TwistKer_Pf.real false true 0 _ ?_⟩
  intro b hb
  by_cases h0 : b = 0
  · subst h0
    have h1 := one_le_ellT (L := 4) (g := TwistKer_Pf.g0) (t := 0) (by norm_num)
    have h2 : (1 : ℝ) ≤ 16 ^ (1 / 2 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    simp [zdistD] at hb; nlinarith
  · simp [h0]

/-- T.10 (d) with `A = 2 > 1` at `Pf`, `v = 1 - g₀²/8 < u = 1 - g₀²/16`: `(1 - v) L² = 2 g₀²`, so the regime of the merged `A = 1` lemma (`(1-v)L² ≤ g₀²`) fails and only the
`A`-form applies. -/
example : ∃ C : ℝ, 0 < C ∧ ‖projMat 3 4 * BAuKer 3 4 TwistKer_Pf.g0 TwistKer_Pf.E TwistKer_Pf.m0 (1 - TwistKer_Pf.g0 ^ 2 / 8) (1 - TwistKer_Pf.g0 ^ 2 / 16) false true‖ ≤ C ∧
    1 - TwistKer_Pf.g0 ^ 2 / 8 < 1 - TwistKer_Pf.g0 ^ 2 / 16 ∧ ¬ (1 - (1 - TwistKer_Pf.g0 ^ 2 / 8)) * ((4 : ℕ) : ℝ) ^ 2 ≤ 1 * TwistKer_Pf.g0 ^ 2 := by
  obtain ⟨C, hC, H⟩ := baTwKerZero_holds 3 1 TwistKer_Pf.m0.im le_rfl one_pos TwistKer_Pf.real.1.1 2 two_pos
  have hg := TwistKer_Pf.g0_pos; have hg2 := TwistKer_Pf.g0_le
  have hp : 0 < TwistKer_Pf.g0 ^ 2 := by positivity
  have hq : TwistKer_Pf.g0 ^ 2 ≤ 1 / 4 := by nlinarith
  refine ⟨C, hC, H 4 (by norm_num) TwistKer_Pf.g0 hg (hg2.trans (by norm_num)) TwistKer_Pf.E TwistKer_Pf.m0 TwistKer_Pf.real false true _ _ (by nlinarith)
    (by push_cast; nlinarith) (by linarith) (by linarith), by linarith, ?_⟩
  push_cast
  nlinarith

/-- T.10 (d) with `A = (κ+1)/κ`, `κ = Im Pf.m0` (the use of TL2d), `v = 1 - g₀²/16 < u = 1 - g₀²/32`. -/
example : ∃ C : ℝ, 0 < C ∧ ‖projMat 3 4 * BAuKer 3 4 TwistKer_Pf.g0 TwistKer_Pf.E TwistKer_Pf.m0 (1 - TwistKer_Pf.g0 ^ 2 / 16) (1 - TwistKer_Pf.g0 ^ 2 / 32) false true‖ ≤ C ∧
    1 - TwistKer_Pf.g0 ^ 2 / 16 < 1 - TwistKer_Pf.g0 ^ 2 / 32 := by
  have hκ := TwistKer_Pf.real.1.1
  obtain ⟨C, hC, H⟩ := baTwKerZero_holds 3 1 TwistKer_Pf.m0.im le_rfl one_pos hκ ((TwistKer_Pf.m0.im + 1) / TwistKer_Pf.m0.im) (by positivity)
  have hg := TwistKer_Pf.g0_pos; have hg2 := TwistKer_Pf.g0_le
  have hp : 0 < TwistKer_Pf.g0 ^ 2 := by positivity
  have hA : 1 ≤ (TwistKer_Pf.m0.im + 1) / TwistKer_Pf.m0.im := by rw [le_div_iff₀ hκ]; linarith
  refine ⟨C, hC, H 4 (by norm_num) TwistKer_Pf.g0 hg (hg2.trans (by norm_num)) TwistKer_Pf.E TwistKer_Pf.m0 TwistKer_Pf.real false true _ _ (by nlinarith)
    (by push_cast; nlinarith) (by linarith) (by linarith), by linarith⟩

/-- T.1 (iii) at `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`), `zSeq`, `flow_sz0` (`(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`), `ε₁ = 1/10`,
`D = 2`.  For every `n` and `v ∈ [0, 1/2]` (`1/2 < t₀`, `half_lt_t0`) the pair `a = (2(n+1), 0, 0)`, `c₁ = 0` lies in the cut-off region (`|a - c₁|_∞ ≥ 2(n+1) ≥ W_n^{1/10}`,
`ℓ_v(lam_n) ≤ 1`), so the theorem is applied to a nonempty set for large `n`, every charge `σ` and every `c₂`. -/
example : ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 2 → ∃ a c₁ : Zd 3 (sz0.L n),
    ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ellT (sz0.L n) (sz0.lam n) v ≤ (zdistInf 3 (sz0.L n) (a - c₁) : ℝ) ∧
    ∀ (σ : Fin 2 → Bool) (c₂ : Zd 3 (sz0.L n)),
      ‖twK (baFMz sz0 zSeq) n v σ a c₁ c₂‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (-2 : ℝ) := by
  filter_upwards [baTwKDecay_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (1 / 10) 2 (by norm_num) (by norm_num)] with n hn
  intro v hv0 hv1
  have hy1 : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- `zdistInf (a - 0) ≥ 2(n+1)` for `a = (2(n+1), 0, 0)` in `Z_{4(n+1)}^3`
  have h1 : 2 * (n + 1) ≤ zdistInf 3 (sz0.L n) (![((2 * (n + 1) : ℕ) : ZMod (sz0.L n)), 0, 0] - 0) := by
    have h := Finset.le_sup (f := fun j => zdist (sz0.L n)
      ((![((2 * (n + 1) : ℕ) : ZMod (sz0.L n)), 0, 0] - 0 : Zd 3 (sz0.L n)) j)) (Finset.mem_univ (0 : Fin 3))
    refine le_trans ?_ h
    have hL : sz0.L n = 4 * (n + 1) := rfl
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, Matrix.cons_val_zero, zdist, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (by rw [hL]; omega)]
    rw [hL]; omega
  have h1' : (2 * ((n : ℝ) + 1)) ≤ (zdistInf 3 (sz0.L n) (![((2 * (n + 1) : ℕ) : ZMod (sz0.L n)), 0, 0] - 0) : ℝ) := by
    exact_mod_cast h1
  -- `ℓ_v(lam_n) ≤ 1` for `v ≤ 1/2`: `lam_n ≤ 1/64`, `√|1 - v| ≥ 1/2`
  have hell : ellT (sz0.L n) (sz0.lam n) v ≤ 1 := by
    refine (min_le_left _ _).trans (max_le ?_ le_rfl)
    have hs : (1 / 2 : ℝ) ≤ Real.sqrt |1 - v| := by
      rw [Real.le_sqrt (by norm_num) (abs_nonneg _), abs_of_nonneg (by linarith)]
      linarith
    have hlam : sz0.lam n ≤ 1 / 2 := by
      have e : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
      rw [e]
      have h6 : (2 : ℝ) ^ 6 ≤ (2 * ((n : ℝ) + 1)) ^ 6 := pow_le_pow_left₀ (by norm_num) hy1 6
      calc ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ ((2 : ℝ) ^ 6)⁻¹ := inv_anti₀ (by norm_num) h6
        _ ≤ 1 / 2 := by norm_num
    rw [div_le_one (by linarith)]
    linarith
  -- `W_n^{1/10} = ((2(n+1))^5)^{1/10} ≤ 2(n+1)`
  have hW : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have hWn : ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [sz0]
    rw [hWn]
    calc ((2 * ((n : ℝ) + 1)) ^ 5) ^ (1 / 10 : ℝ) = (2 * ((n : ℝ) + 1)) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ (2 * ((n : ℝ) + 1)) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = _ := Real.rpow_one _
  have hWpos : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcut : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ellT (sz0.L n) (sz0.lam n) v ≤
      (zdistInf 3 (sz0.L n) (![((2 * (n + 1) : ℕ) : ZMod (sz0.L n)), 0, 0] - 0) : ℝ) :=
    calc _ ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * 1 := mul_le_mul_of_nonneg_left hell hWpos
      _ ≤ _ := by rw [mul_one]; exact hW.trans h1'
  exact ⟨_, 0, hcut, fun σ c₂ => hn v hv0 (hv1.trans (half_lt_t0 n).le) σ _ 0 c₂ hcut⟩

end Inst

end RBM.BA

end
