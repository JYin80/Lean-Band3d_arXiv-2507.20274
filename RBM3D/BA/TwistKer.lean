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
# BA stage TL, row TL2b (T2429), part 1: the kernel bounds, the decay of `K̃`, the fine-lattice core

Deterministic facts of the twisted tree (`docs/tickets/T2398-TL-proofs.md`).

* Lemma T.10 (a), (b), (d) for the one-index kernel `Ũ_{v,u} = BAuKer v u`: the pins `BATwKerA`,
  `BATwKerFar`, `BATwKerZero` of `BA/TwistPins.lean:193-213` (T.10 (c) is the merged
  `baEKSameRow_holds`).  (a), (b) come from the public `EKPins_norm_uKer_le`, `EKPins_norm_Q_le`,
  `EKPins_norm_Theta_le` (their `private` is removed in `BA/EKPins.lean`, DECISIONS §153 (1),
  §161 (1)) and `baEKXiBall_holds`; (d) is the `A`-form of the merged private lemma
  `EKNonzero_norm_projMat_mul_uKer_le` (the merged one is the case `A = 1`), written here with the
  helpers of `BA/EKNonzero.lean` made public.
* Lemma T.1 (iii), the decay of `K̃` in `|a - c₁|` (new pin `BATwKDecay`, `baTwKDecay_holds`): the
  case split of `baComp_holds` (`BA/EMn2BA.lean:472`) for `Σ_{a'} Θ(a,a') M(c₂,a') M(a',c₁)` and the
  eventual absorption of `baEMn2ExpHK` (`BA/EMn2BA.lean:637`).
* Section 5, the fine lattice `Idx d (sz.L n) (sz.W n)`: `E_a = W^{-d} 1_{[a]}`, the trace sandwich,
  the loops `𝓛 = Tr ∏ G(σ_i) E_{a_i}` as traces of fine matrices, the Ward identity, and from them
  the deterministic cores of Lemmas T.2 (fold), T.4 at `n = 3` (contraction of `L̃^{(3)}`), T.5
  (entries of `G` from the 2-loop) and of the source bounds `Ẽ^{G̊}`, `L̃`, `(Ẽ⊗Ẽ)` used by
  `BA/TwistKer2.lean`.

Private helpers carry the stem `TwistKer_`; the helpers `TwistKer_*` used by `BA/TwistKer2.lean`
are public.
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

/-! ## 5. The fine lattice: `E_a`, the trace sandwich, loops and the Ward identity (the deterministic core of T.2, T.4 at `n = 3`, T.5)

`loopFine H z σ a` is the trace of `∏ G(σ_i) E_{a_i}` over the block-product index; here it is read on the fine lattice with `E_a = W^{-d} 1_{[a]}`
(`TwistKer_fE`).  The identities are the entrywise computations that the private `trace_pm_formula`, `loopFine_pm_formula` (`Green/Pins.lean:377-437`) and
`Gres_ward_left` (`Induction/Contract.lean:277`) make for the band model, here copied (stem `TwistKer_`) for `Idx d (sz.L n) (sz.W n)`. -/

section Fine

variable {d : ℕ} {sz : Sizes d} (n : ℕ)

/-- `E_a = W^{-d} 1_{[a]}` on the fine lattice (`Eblk` read through `splitEquiv`). -/
private def TwistKer_fE (a : Zd d (sz.L n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Matrix.diagonal fun x => if (split d (sz.L n) (sz.W n) x).1 = a then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ else 0

private theorem TwistKer_fE_apply (a : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)) :
    TwistKer_fE n a x y = if x = y then (if (split d (sz.L n) (sz.W n) x).1 = a then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ else 0) else 0 := by
  simp [TwistKer_fE, Matrix.diagonal_apply]

/-- `Tr(A E_a B E_b) = W^{-2d} Σ_{i∈[b]} Σ_{j∈[a]} A_{ij} B_{ji}`. -/
private theorem TwistKer_trace_sandwich (A B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a b : Zd d (sz.L n)) :
    Matrix.trace (A * TwistKer_fE n a * B * TwistKer_fE n b) =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ i ∈ twBlk n b, ∑ j ∈ twBlk n a, A i j * B j i := by
  set w : ℂ := (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ with hw
  have h1 : ∀ (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (c : Zd d (sz.L n)) (i j : Idx d (sz.L n) (sz.W n)),
      (M * TwistKer_fE n c) i j = M i j * (if (split d (sz.L n) (sz.W n) j).1 = c then w else 0) := by
    intro M c i j
    simp [TwistKer_fE, Matrix.mul_diagonal, hw]
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  have h2 : ∀ i, (A * TwistKer_fE n a * B * TwistKer_fE n b) i i =
      (if (split d (sz.L n) (sz.W n) i).1 = b then w else 0) * ∑ j, A i j * (if (split d (sz.L n) (sz.W n) j).1 = a then w else 0) * B j i := by
    intro i
    rw [h1, Matrix.mul_apply, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1]
  simp only [h2]
  have h3 : ∀ i : Idx d (sz.L n) (sz.W n), (if (split d (sz.L n) (sz.W n) i).1 = b then w else 0) *
      ∑ j, A i j * (if (split d (sz.L n) (sz.W n) j).1 = a then w else 0) * B j i =
      if (split d (sz.L n) (sz.W n) i).1 = b then w ^ 2 * ∑ j ∈ twBlk n a, A i j * B j i else 0 := by
    intro i
    by_cases hi : (split d (sz.L n) (sz.W n) i).1 = b
    · simp only [hi, ite_true]
      rw [twBlk, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : (split d (sz.L n) (sz.W n) j).1 = a
      · simp [hj]; ring
      · simp [hj]
    · simp [hi]
  simp only [h3]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rfl

/-- `Tr(E_b M) = W^{-d} Σ_{y∈[b]} M_{yy}`. -/
private theorem TwistKer_trace_fE_mul (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (b : Zd d (sz.L n)) :
    Matrix.trace (TwistKer_fE n b * M) = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ y ∈ twBlk n b, M y y := by
  unfold Matrix.trace TwistKer_fE
  simp only [Matrix.diag_apply, Matrix.diagonal_mul]
  rw [twBlk, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (split d (sz.L n) (sz.W n) i).1 = b <;> simp [hi]

/-- `Σ_a Σ_{x∈[a]} F x = Σ_x F x` (a copy of the private `TwistPins_sum_blk`). -/
private theorem TwistKer_sum_blk {β : Type*} [AddCommMonoid β] (F : Idx d (sz.L n) (sz.W n) → β) :
    ∑ a : Zd d (sz.L n), ∑ x ∈ twBlk n a, F x = ∑ x, F x :=
  Finset.sum_fiberwise Finset.univ (fun x => (split d (sz.L n) (sz.W n) x).1) F

/-- `G(σ)^* = G(-σ)` for Hermitian `H` (a copy of the private `Gres_conjTranspose`, `Induction/Contract.lean:225`). -/
private theorem TwistKer_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse,
      Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hH', Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false, ← Matrix.nonsing_inv_eq_ringInverse,
      Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hH', Complex.star_def, Complex.conj_conj]

/-- **Ward's identity** `G(+) - G(-) = (z - z̄) G(+) G(-) = (z - z̄) G(-) G(+)` (a copy of the private `Gres_sub`, `Induction/Contract.lean:240`). -/
private theorem TwistKer_Gres_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Gres H z true - Gres H z false = (z - (starRingEnd ℂ) z) • (Gres H z true * Gres H z false) ∧
    Gres H z true - Gres H z false = (z - (starRingEnd ℂ) z) • (Gres H z false * Gres H z true) := by
  have hA : IsUnit (H - z • (1 : Matrix ι ι ℂ)) := isUnit_sub_smul_of_isHermitian hH hz
  have hB : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix ι ι ℂ)) :=
    isUnit_sub_smul_of_isHermitian hH (by simpa using hz)
  have hAd : IsUnit (H - z • (1 : Matrix ι ι ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hBd : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix ι ι ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hB
  simp only [Gres, ↓reduceIte, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse]
  set A : Matrix ι ι ℂ := H - z • (1 : Matrix ι ι ℂ) with hAdef
  set B : Matrix ι ι ℂ := H - (starRingEnd ℂ) z • (1 : Matrix ι ι ℂ) with hBdef
  have hBA : B - A = (z - (starRingEnd ℂ) z) • (1 : Matrix ι ι ℂ) := by
    rw [hAdef, hBdef, sub_sub_sub_cancel_left, ← sub_smul]
  have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAd
  have hAinv' : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAd
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBd
  have hBinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBd
  constructor
  · have : A⁻¹ * (B - A) * B⁻¹ = A⁻¹ - B⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hBinv', Matrix.mul_one,
        hAinv, Matrix.one_mul]
    rw [← this, hBA]
    simp
  · have : B⁻¹ * (B - A) * A⁻¹ = A⁻¹ - B⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hBinv, Matrix.one_mul, Matrix.mul_assoc, hAinv',
        Matrix.mul_one]
    rw [← this, hBA]
    simp

/-- `G(-σ) G(σ) = (2 i η)⁻¹ (G(+) - G(-))` (a copy of the private `Gres_ward_left`, `Induction/Contract.lean:277`). -/
private theorem TwistKer_Gres_ward_left {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Gres H z (!σ) * Gres H z σ = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
  have hk : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz
    simp [this]
  obtain ⟨h1, h2⟩ := TwistKer_Gres_sub hH hz
  have hsub : z - (starRingEnd ℂ) z = 2 * Complex.I * (z.im : ℂ) := by rw [Complex.sub_conj]; push_cast; ring
  rw [hsub] at h1 h2
  cases σ with
  | true =>
    simp only [Bool.not_true]
    rw [h2, smul_smul, inv_mul_cancel₀ hk, one_smul]
  | false =>
    simp only [Bool.not_false]
    rw [h1, smul_smul, inv_mul_cancel₀ hk, one_smul]

/-- `G(σ) G(-σ) = (2 i η)⁻¹ (G(+) - G(-))`. -/
private theorem TwistKer_Gres_ward_right {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Gres H z σ * Gres H z (!σ) = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
  have := TwistKer_Gres_ward_left hH hz (!σ)
  simpa using this

/-- `blockMat` commutes with `Gres` (a copy of the private `gres_blockMat_true`, `Green/Pins.lean:346`, for both signs). -/
private theorem TwistKer_Gres_blockMat (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (σ : Bool) :
    Gres (blockMat d (sz.L n) (sz.W n) H) z σ = blockMat d (sz.L n) (sz.W n) (Gres H z σ) := by
  unfold Gres blockMat
  set w : ℂ := if σ then z else (starRingEnd ℂ) z with hw
  have e1 : H.submatrix (splitEquiv d (sz.L n) (sz.W n)).symm (splitEquiv d (sz.L n) (sz.W n)).symm -
        w • (1 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) =
      (H - w • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)).submatrix (splitEquiv d (sz.L n) (sz.W n)).symm
        (splitEquiv d (sz.L n) (sz.W n)).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_submatrix_equiv]

/-- `E_a` through `blockMat` is `Eblk a`. -/
private theorem TwistKer_blockMat_fE (c : Zd d (sz.L n)) :
    blockMat d (sz.L n) (sz.W n) (TwistKer_fE n c) = Eblk d (sz.L n) (sz.W n) c := by
  ext x y
  unfold blockMat Eblk TwistKer_fE
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    have : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm x) = x :=
      (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply x
    simp [this]
  · have : (splitEquiv d (sz.L n) (sz.W n)).symm x ≠ (splitEquiv d (sz.L n) (sz.W n)).symm y :=
      fun h => hxy ((splitEquiv d (sz.L n) (sz.W n)).symm.injective h)
    simp [hxy, this]

/-- **The loops of the fine lattice as traces of fine matrices**: `𝓛_{σ,a} = Tr ∏_i G(σ_i) E_{a_i}` with `E_a = W^{-d} 1_{[a]}` on `Idx`. -/
private theorem TwistKer_loopFine_eq (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n) H z σ a =
      Matrix.trace (List.ofFn fun i => Gres H z (σ i) * TwistKer_fE n (a i)).prod := by
  unfold loopFine loopM
  set Φ := Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d (sz.L n) (sz.W n)) with hΦdef
  have hΦ : ∀ M, Φ M = blockMat d (sz.L n) (sz.W n) M := fun M => rfl
  have hprod : (List.ofFn fun i => Gres (blockMat d (sz.L n) (sz.W n) H) z (σ i) * Eblk d (sz.L n) (sz.W n) (a i)).prod =
      Φ (List.ofFn fun i => Gres H z (σ i) * TwistKer_fE n (a i)).prod := by
    rw [map_list_prod, List.map_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun i => ?_)
    simp only [Function.comp_apply]
    rw [map_mul, hΦ, hΦ, TwistKer_Gres_blockMat, TwistKer_blockMat_fE]
  rw [hprod]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, hΦ, blockMat, Matrix.submatrix_apply]
  exact Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm
    (fun i => (List.ofFn fun i => Gres H z (σ i) * TwistKer_fE n (a i)).prod i i)

/-- The 1-loop. -/
private theorem TwistKer_loop1 (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (σ : Bool) (c : Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n) H z ![σ] ![c] = Matrix.trace (Gres H z σ * TwistKer_fE n c) := by
  rw [TwistKer_loopFine_eq]
  simp [List.ofFn_succ]

/-- The 3-loop. -/
private theorem TwistKer_loop3 (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (σ₀ σ₁ σ₂ : Bool)
    (a₀ a₁ a₂ : Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n) H z ![σ₀, σ₁, σ₂] ![a₀, a₁, a₂] =
      Matrix.trace (Gres H z σ₀ * TwistKer_fE n a₀ * Gres H z σ₁ * TwistKer_fE n a₁ * Gres H z σ₂ * TwistKer_fE n a₂) := by
  rw [TwistKer_loopFine_eq]
  simp [List.ofFn_succ, mul_assoc]

/-- The 2-loop. -/
private theorem TwistKer_loop2 (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (σ₀ σ₁ : Bool)
    (a₀ a₁ : Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n) H z ![σ₀, σ₁] ![a₀, a₁] =
      Matrix.trace (Gres H z σ₀ * TwistKer_fE n a₀ * Gres H z σ₁ * TwistKer_fE n a₁) := by
  rw [TwistKer_loopFine_eq]
  simp [List.ofFn_succ, mul_assoc]

/-- **The 2-loop in entries**: `𝓛_{(+,-),(a,b)} = W^{-2d} Σ_{i∈[b], j∈[a]} |G_{ij}|²` (Hermitian `H`; the twin of the private `loopFine_pm_formula`, `Green/Pins.lean:407`). -/
private theorem TwistKer_loop2_pm {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) (z : ℂ)
    (a b : Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n) H z ![true, false] ![a, b] =
      ((((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ∑ i ∈ twBlk n b, ∑ j ∈ twBlk n a, ‖Gres H z true i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [TwistKer_loop2, TwistKer_trace_sandwich]
  have hG : Gres H z false = (Gres H z true)ᴴ := by
    have := TwistKer_Gres_conjTranspose hH z true
    simpa using this.symm
  rw [hG]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']

/-- The entry of `G` is dominated by the 2-loop: `|G_{ij}|² ≤ W^{2d} 𝓛_{(+,-),([j],[i])}`. -/
private theorem TwistKer_entry_le_loop2 {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) (z : ℂ)
    (i j : Idx d (sz.L n) (sz.W n)) :
    ‖Gres H z true i j‖ ^ 2 ≤ (((sz.W n : ℕ) : ℝ) ^ d) ^ 2 *
      ‖loopFine d (sz.L n) (sz.W n) H z ![true, false] ![(split d (sz.L n) (sz.W n) j).1, (split d (sz.L n) (sz.W n) i).1]‖ := by
  rw [TwistKer_loop2_pm n hH z, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hi : i ∈ twBlk n (split d (sz.L n) (sz.W n) i).1 := by simp [twBlk]
  have hj : j ∈ twBlk n (split d (sz.L n) (sz.W n) j).1 := by simp [twBlk]
  have h1 : ‖Gres H z true i j‖ ^ 2 ≤ ∑ i' ∈ twBlk n (split d (sz.L n) (sz.W n) i).1, ∑ j' ∈ twBlk n (split d (sz.L n) (sz.W n) j).1,
      ‖Gres H z true i' j'‖ ^ 2 := by
    refine (Finset.single_le_sum (f := fun j' => ‖Gres H z true i j'‖ ^ 2) (fun _ _ => by positivity) hj).trans ?_
    exact Finset.single_le_sum (f := fun i' => ∑ j' ∈ twBlk n (split d (sz.L n) (sz.W n) j).1, ‖Gres H z true i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hi
  calc ‖Gres H z true i j‖ ^ 2 ≤ _ := h1
    _ = (((sz.W n : ℕ) : ℝ) ^ d) ^ 2 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 * ∑ i' ∈ twBlk n (split d (sz.L n) (sz.W n) i).1,
        ∑ j' ∈ twBlk n (split d (sz.L n) (sz.W n) j).1, ‖Gres H z true i' j'‖ ^ 2) := by
        field_simp

/-- `Σ_a twSq(X; c, a) = W^{-2d} Σ_{y∈[c]} (X X^*)_{yy}` (sum over the column block). -/
private theorem TwistKer_sum_twSq_row (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (c : Zd d (sz.L n)) :
    (((∑ a, twSq n X c a : ℝ)) : ℂ) = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ y ∈ twBlk n c, (X * Xᴴ) y y := by
  unfold twSq
  push_cast
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [TwistKer_sum_blk n (fun x : Idx d (sz.L n) (sz.W n) => ((‖X y x‖ : ℝ) : ℂ) ^ 2)]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.mul_conj']

/-- `Σ_b twSq(X; b, c) = W^{-2d} Σ_{x∈[c]} (X^* X)_{xx}` (sum over the row block). -/
private theorem TwistKer_sum_twSq_col (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (c : Zd d (sz.L n)) :
    (((∑ b, twSq n X b c : ℝ)) : ℂ) = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n c, (Xᴴ * X) x x := by
  unfold twSq
  push_cast
  rw [← Finset.mul_sum]
  congr 1
  have : ∀ b : Zd d (sz.L n), ∑ y ∈ twBlk n b, ∑ x ∈ twBlk n c, ((‖X y x‖ : ℝ) : ℂ) ^ 2 =
      ∑ x ∈ twBlk n c, ∑ y ∈ twBlk n b, ((‖X y x‖ : ℝ) : ℂ) ^ 2 := fun b => Finset.sum_comm
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [TwistKer_sum_blk n (fun y : Idx d (sz.L n) (sz.W n) => ((‖X y x‖ : ℝ) : ℂ) ^ 2)]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_comm, Complex.mul_conj']

/-- `Σ_{y∈[c]} M_{yy} = W^d Tr(E_c M)`. -/
private theorem TwistKer_blk_diag_sum (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (c : Zd d (sz.L n)) :
    ∑ y ∈ twBlk n c, M y y = (((sz.W n : ℕ) : ℂ) ^ d) * Matrix.trace (TwistKer_fE n c * M) := by
  rw [TwistKer_trace_fE_mul]
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  field_simp

/-- The arithmetic of the Ward sums: `T = ‖(T : ℂ)‖`, `(T : ℂ) = W^{-2d} (2iη)⁻¹ W^d (t₁ - t₂)`, `‖t_i‖ ≤ M` give `T ≤ (W^d η)⁻¹ M`. -/
private theorem TwistKer_ward_arith {T η M : ℝ} (hη : 0 < η) (hT : 0 ≤ T) (t₁ t₂ : ℂ) (h₁ : ‖t₁‖ ≤ M) (h₂ : ‖t₂‖ ≤ M) (W : ℝ)
    (hW : 0 < W) (hTc : (T : ℂ) = ((W : ℂ)⁻¹) ^ 2 * ((2 * Complex.I * (η : ℂ))⁻¹ * ((W : ℂ) * (t₁ - t₂)))) :
    T ≤ (W * η)⁻¹ * M := by
  have h1 : T = ‖(T : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hT]
  rw [h1, hTc]
  have hk : ‖(2 * Complex.I * (η : ℂ))⁻¹‖ = (2 * η)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
    simp
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, hk, Complex.norm_real, Real.norm_of_nonneg hW.le]
  have h3 : ‖t₁ - t₂‖ ≤ 2 * M := by
    have := norm_sub_le t₁ t₂
    linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans h₁
  calc W⁻¹ ^ 2 * ((2 * η)⁻¹ * (W * ‖t₁ - t₂‖)) ≤ W⁻¹ ^ 2 * ((2 * η)⁻¹ * (W * (2 * M))) := by
        gcongr
    _ = (W * η)⁻¹ * M := by field_simp

/-- **Ward at the right end of a 1-loop**: `Σ_a 𝓛^{(2)}`-type sum `Σ_a twSq(G(σ); c, a) ≤ (W^d η)⁻¹ max |𝓛^{(1)}_{c}|`. -/
private theorem TwistKer_ward_row1 {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (σ : Bool) (c : Zd d (sz.L n)) {M : ℝ} (hM : ∀ τ : Bool, ‖loopFine d (sz.L n) (sz.W n) H z ![τ] ![c]‖ ≤ M) :
    ∑ a, twSq n (Gres H z σ) c a ≤ ((((sz.W n : ℕ) : ℝ) ^ d) * z.im)⁻¹ * M := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  refine TwistKer_ward_arith hz (Finset.sum_nonneg fun a _ => ?_) (Matrix.trace (Gres H z true * TwistKer_fE n c))
    (Matrix.trace (Gres H z false * TwistKer_fE n c)) (by simpa [TwistKer_loop1] using hM true)
    (by simpa [TwistKer_loop1] using hM false) _ hW ?_
  · unfold twSq; positivity
  · rw [TwistKer_sum_twSq_row]
    have hX : Gres H z σ * (Gres H z σ)ᴴ = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
      rw [TwistKer_Gres_conjTranspose hH z σ]; exact TwistKer_Gres_ward_right hH hz.ne' σ
    rw [hX]
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [TwistKer_blk_diag_sum, TwistKer_blk_diag_sum, Matrix.trace_mul_comm (TwistKer_fE n c), Matrix.trace_mul_comm (TwistKer_fE n c)]
    push_cast
    ring

/-- `E_a` is Hermitian. -/
private theorem TwistKer_fE_herm (a : Zd d (sz.L n)) : (TwistKer_fE n a)ᴴ = TwistKer_fE n a := by
  have h : (TwistKer_fE n a).IsHermitian := Matrix.isHermitian_diagonal_iff.mpr fun x => by
    by_cases hx : (split d (sz.L n) (sz.W n) x).1 = a <;> simp [hx, IsSelfAdjoint]
  exact h

/-- **Ward at the left end of a 1-loop**: `Σ_b twSq(G(σ); b, c) ≤ (W^d η)⁻¹ max |𝓛^{(1)}_c|`. -/
private theorem TwistKer_ward_col1 {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (σ : Bool) (c : Zd d (sz.L n)) {M : ℝ} (hM : ∀ τ : Bool, ‖loopFine d (sz.L n) (sz.W n) H z ![τ] ![c]‖ ≤ M) :
    ∑ b, twSq n (Gres H z σ) b c ≤ ((((sz.W n : ℕ) : ℝ) ^ d) * z.im)⁻¹ * M := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  refine TwistKer_ward_arith hz (Finset.sum_nonneg fun a _ => ?_) (Matrix.trace (Gres H z true * TwistKer_fE n c))
    (Matrix.trace (Gres H z false * TwistKer_fE n c)) (by simpa [TwistKer_loop1] using hM true)
    (by simpa [TwistKer_loop1] using hM false) _ hW ?_
  · unfold twSq; positivity
  · rw [TwistKer_sum_twSq_col]
    have hX : (Gres H z σ)ᴴ * Gres H z σ = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
      rw [TwistKer_Gres_conjTranspose hH z σ]; exact TwistKer_Gres_ward_left hH hz.ne' σ
    rw [hX]
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [TwistKer_blk_diag_sum, TwistKer_blk_diag_sum, Matrix.trace_mul_comm (TwistKer_fE n c), Matrix.trace_mul_comm (TwistKer_fE n c)]
    push_cast
    ring

/-- `Σ_{y∈[c]} (P (k (D₁ - D₂)) Q)_{yy}` in terms of traces. -/
private theorem TwistKer_ward_sum_form (P Q D₁ D₂ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℂ) (c : Zd d (sz.L n)) :
    ∑ y ∈ twBlk n c, (P * (k • (D₁ - D₂)) * Q) y y = (((sz.W n : ℕ) : ℂ) ^ d) *
      (k * (Matrix.trace (TwistKer_fE n c * (P * D₁ * Q)) - Matrix.trace (TwistKer_fE n c * (P * D₂ * Q)))) := by
  rw [TwistKer_blk_diag_sum]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_smul,
    Matrix.trace_sub]
  simp [smul_eq_mul]

/-- **Ward at the vertex `a₁` of a 4-loop** (the fold at the twist of `L̃^{(3)}`, `TP` Lemma T.4, B.5): for `X = G(σ₁) E_{a₂} G(σ₂)`,
`Σ_a twSq(X; a, c₁) = W^{-d} (2iη)⁻¹ (𝓛^{(3)}_{(σ₂,-σ₂,+),(c₁,a₂,a₂)} - 𝓛^{(3)}_{(σ₂,-σ₂,-),(c₁,a₂,a₂)}) ≤ (W^d η)⁻¹ max |𝓛^{(3)}|`. -/
private theorem TwistKer_ward_col3 {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (σ₁ σ₂ : Bool) (a₂ c₁ : Zd d (sz.L n)) {M : ℝ}
    (hM : ∀ τ : Bool, ‖loopFine d (sz.L n) (sz.W n) H z ![σ₂, !σ₂, τ] ![c₁, a₂, a₂]‖ ≤ M) :
    ∑ a, twSq n (Gres H z σ₁ * TwistKer_fE n a₂ * Gres H z σ₂) a c₁ ≤ ((((sz.W n : ℕ) : ℝ) ^ d) * z.im)⁻¹ * M := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have ht : ∀ τ : Bool, Matrix.trace (TwistKer_fE n c₁ * (Gres H z (!σ₂) * TwistKer_fE n a₂ * Gres H z τ * (TwistKer_fE n a₂ * Gres H z σ₂))) =
      loopFine d (sz.L n) (sz.W n) H z ![σ₂, !σ₂, τ] ![c₁, a₂, a₂] := by
    intro τ
    rw [TwistKer_loop3]
    have : TwistKer_fE n c₁ * (Gres H z (!σ₂) * TwistKer_fE n a₂ * Gres H z τ * (TwistKer_fE n a₂ * Gres H z σ₂)) =
        (TwistKer_fE n c₁ * Gres H z (!σ₂) * TwistKer_fE n a₂ * Gres H z τ * TwistKer_fE n a₂) * Gres H z σ₂ := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  refine TwistKer_ward_arith hz (Finset.sum_nonneg fun a _ => ?_)
    (Matrix.trace (TwistKer_fE n c₁ * (Gres H z (!σ₂) * TwistKer_fE n a₂ * Gres H z true * (TwistKer_fE n a₂ * Gres H z σ₂))))
    (Matrix.trace (TwistKer_fE n c₁ * (Gres H z (!σ₂) * TwistKer_fE n a₂ * Gres H z false * (TwistKer_fE n a₂ * Gres H z σ₂))))
    (by rw [ht]; exact hM true) (by rw [ht]; exact hM false) _ hW ?_
  · unfold twSq; positivity
  · rw [TwistKer_sum_twSq_col]
    have hX : (Gres H z σ₁ * TwistKer_fE n a₂ * Gres H z σ₂)ᴴ * (Gres H z σ₁ * TwistKer_fE n a₂ * Gres H z σ₂) =
        (Gres H z (!σ₂) * TwistKer_fE n a₂) * ((2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false)) *
          (TwistKer_fE n a₂ * Gres H z σ₂) := by
      rw [← TwistKer_Gres_ward_left hH hz.ne' σ₁]
      simp only [Matrix.conjTranspose_mul, TwistKer_Gres_conjTranspose hH z, TwistKer_fE_herm, Matrix.mul_assoc]
    rw [hX, TwistKer_ward_sum_form]
    push_cast
    ring

/-- **Ward at the vertex `a'` of a 4-loop, second form** (the fold at the twist of `L̃^{(3)}` with the summed vertex in the middle): for `X = G(σ₁) E_a G(σ₂)`,
`Σ_{a'} twSq(X; c₂, a') ≤ (W^d η)⁻¹ max |𝓛^{(3)}_{(-σ₁,σ₁,±),(c₂,a,a)}|`. -/
private theorem TwistKer_ward_row3 {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (σ₁ σ₂ : Bool) (a c₂ : Zd d (sz.L n)) {M : ℝ}
    (hM : ∀ τ : Bool, ‖loopFine d (sz.L n) (sz.W n) H z ![!σ₁, σ₁, τ] ![c₂, a, a]‖ ≤ M) :
    ∑ a', twSq n (Gres H z σ₁ * TwistKer_fE n a * Gres H z σ₂) c₂ a' ≤ ((((sz.W n : ℕ) : ℝ) ^ d) * z.im)⁻¹ * M := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have ht : ∀ τ : Bool, Matrix.trace (TwistKer_fE n c₂ * (Gres H z σ₁ * TwistKer_fE n a * Gres H z τ * (TwistKer_fE n a * Gres H z (!σ₁)))) =
      loopFine d (sz.L n) (sz.W n) H z ![!σ₁, σ₁, τ] ![c₂, a, a] := by
    intro τ
    rw [TwistKer_loop3]
    have : TwistKer_fE n c₂ * (Gres H z σ₁ * TwistKer_fE n a * Gres H z τ * (TwistKer_fE n a * Gres H z (!σ₁))) =
        (TwistKer_fE n c₂ * Gres H z σ₁ * TwistKer_fE n a * Gres H z τ * TwistKer_fE n a) * Gres H z (!σ₁) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  refine TwistKer_ward_arith hz (Finset.sum_nonneg fun a _ => ?_)
    (Matrix.trace (TwistKer_fE n c₂ * (Gres H z σ₁ * TwistKer_fE n a * Gres H z true * (TwistKer_fE n a * Gres H z (!σ₁)))))
    (Matrix.trace (TwistKer_fE n c₂ * (Gres H z σ₁ * TwistKer_fE n a * Gres H z false * (TwistKer_fE n a * Gres H z (!σ₁)))))
    (by rw [ht]; exact hM true) (by rw [ht]; exact hM false) _ hW ?_
  · unfold twSq; positivity
  · rw [TwistKer_sum_twSq_row]
    have hX : (Gres H z σ₁ * TwistKer_fE n a * Gres H z σ₂) * (Gres H z σ₁ * TwistKer_fE n a * Gres H z σ₂)ᴴ =
        (Gres H z σ₁ * TwistKer_fE n a) * ((2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false)) *
          (TwistKer_fE n a * Gres H z (!σ₁)) := by
      rw [← TwistKer_Gres_ward_right hH hz.ne' σ₂]
      simp only [Matrix.conjTranspose_mul, TwistKer_Gres_conjTranspose hH z, TwistKer_fE_herm, Matrix.mul_assoc]
    rw [hX, TwistKer_ward_sum_form]
    push_cast
    ring

/-- `(M E_a)_{ij} = W^{-d} 1_{[j]=a} M_{ij}`. -/
private theorem TwistKer_mul_fE_apply (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (c : Zd d (sz.L n))
    (i j : Idx d (sz.L n) (sz.W n)) :
    (M * TwistKer_fE n c) i j = M i j * (if (split d (sz.L n) (sz.W n) j).1 = c then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ else 0) := by
  simp [TwistKer_fE, Matrix.mul_diagonal]

/-- `(A E_a B)_{ij} = W^{-d} Σ_{y∈[a]} A_{iy} B_{yj}`. -/
private theorem TwistKer_mul3_apply (A B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (c : Zd d (sz.L n))
    (i j : Idx d (sz.L n) (sz.W n)) :
    (A * TwistKer_fE n c * B) i j = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ y ∈ twBlk n c, A i y * B y j := by
  rw [Matrix.mul_apply, twBlk, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [TwistKer_mul_fE_apply]
  by_cases hy : (split d (sz.L n) (sz.W n) y).1 = c
  · simp [hy]; ring
  · simp [hy]

/-- `twChg` of the carrier's `G` is `Gres` (Hermitian `H`). -/
private theorem TwistKer_twChg_eq {G : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {z : ℂ} (hG : G = Gres H z true) (σ : Bool) :
    twChg G σ = Gres H z σ := by
  subst hG
  funext x y
  cases σ
  · have h := TwistKer_Gres_conjTranspose hH z true
    simp only [Bool.not_true] at h
    rw [← h]
    simp [twChg, Matrix.conjTranspose_apply]
  · simp [twChg]

/-- **The fold of `L̃^{(3)}` at the twist and the first vertex** (`TP` T.4, (B.4) with `k = 1`): `|L̃^{(3)}_{(a₁,a₂)}|² ≤ twSq(G₁; c₂, a₁) twSq(G₂ E_{a₂} G₃; a₁, c₁)`. -/
private theorem TwistKer_twL3_fold1 (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 3 → Bool) (a₁ a₂ c₁ c₂ : Zd d (sz.L n)) :
    ‖twL3 C n v ω σ a₁ a₂ c₁ c₂‖ ^ 2 ≤ twSq n (Gres H z (σ 0)) c₂ a₁ * twSq n (Gres H z (σ 1) * TwistKer_fE n a₂ * Gres H z (σ 2)) a₁ c₁ := by
  have e : twL3 C n v ω σ a₁ a₂ c₁ c₂ = twLoopX n (Gres H z (σ 0)) (Gres H z (σ 1) * TwistKer_fE n a₂ * Gres H z (σ 2)) a₁ c₁ c₂ := by
    unfold twL3 twLoopX
    simp only [TwistKer_twChg_eq n hH hG, TwistKer_mul3_apply]
    have hs : ∀ x : Idx d (sz.L n) (sz.W n), ∑ y ∈ twBlk n a₂, ∑ w ∈ twBlk n c₁, Gres H z (σ 0) (twShift n c₂ w) x * Gres H z (σ 1) x y * Gres H z (σ 2) y w =
        ∑ w ∈ twBlk n c₁, ∑ y ∈ twBlk n a₂, Gres H z (σ 0) (twShift n c₂ w) x * Gres H z (σ 1) x y * Gres H z (σ 2) y w := fun x => Finset.sum_comm
    simp only [hs]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [e]
  have := twFold_holds sz n (Gres H z (σ 0)) (fun x w => (Gres H z (σ 1) * TwistKer_fE n a₂ * Gres H z (σ 2)) x w) a₁ c₁ c₂
  exact this

/-- **The fold of `L̃^{(3)}` at the twist and the middle vertex** (`TP` T.4, (B.4) with `k = 2`): `|L̃^{(3)}_{(a,a')}|² ≤ twSq(G₁ E_a G₂; c₂, a') twSq(G₃; a', c₁)`. -/
private theorem TwistKer_twL3_fold2 (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 3 → Bool) (a a' c₁ c₂ : Zd d (sz.L n)) :
    ‖twL3 C n v ω σ a a' c₁ c₂‖ ^ 2 ≤ twSq n (Gres H z (σ 0) * TwistKer_fE n a * Gres H z (σ 1)) c₂ a' * twSq n (Gres H z (σ 2)) a' c₁ := by
  have e : twL3 C n v ω σ a a' c₁ c₂ = twLoopX n (Gres H z (σ 0) * TwistKer_fE n a * Gres H z (σ 1)) (Gres H z (σ 2)) a' c₁ c₂ := by
    unfold twL3 twLoopX
    simp only [TwistKer_twChg_eq n hH hG, TwistKer_mul3_apply]
    have hs : ∀ y : Idx d (sz.L n) (sz.W n), ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, Gres H z (σ 0) (twShift n c₂ w) x * Gres H z (σ 1) x y * Gres H z (σ 2) y w =
        ∑ w ∈ twBlk n c₁, ∑ x ∈ twBlk n a, Gres H z (σ 0) (twShift n c₂ w) x * Gres H z (σ 1) x y * Gres H z (σ 2) y w := fun y => Finset.sum_comm
    rw [Finset.sum_comm]
    simp only [hs]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [e]
  exact twFold_holds sz n _ _ a' c₁ c₂

/-- **T.4 at `n = 3` (the deterministic core of T.11 (ii))**: `Σ_{a'} |L̃^{(3)}_{(a',a)}| ≤ (W^d η)⁻¹ (M₁ M₃)^{1/2}` for the first term of `(D.3)`
(fold at the twist and at `a'`, Ward at `a'` in both folded loops: `TwistKer_ward_row1`, `TwistKer_ward_col3`, Cauchy-Schwarz). -/
private theorem TwistKer_sum_twL3_first (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (hz : 0 < z.im) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 3 → Bool) (a c₁ c₂ : Zd d (sz.L n))
    {M₁ M₃ : ℝ} (hM₁ : ∀ τ : Bool, ∀ c : Zd d (sz.L n), ‖loopFine d (sz.L n) (sz.W n) H z ![τ] ![c]‖ ≤ M₁)
    (hM₃ : ∀ (τ : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)), ‖loopFine d (sz.L n) (sz.W n) H z τ b‖ ≤ M₃) :
    ∑ a', ‖twL3 C n v ω σ a' a c₁ c₂‖ ≤ ((((sz.W n : ℕ) : ℝ) ^ d) * z.im)⁻¹ * Real.sqrt (M₁ * M₃) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set P : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * z.im)⁻¹ with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ true 0)
  have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ (fun _ => true) (fun _ => 0))
  have hS₁ : ∑ a', twSq n (Gres H z (σ 0)) c₂ a' ≤ P * M₁ :=
    TwistKer_ward_row1 n hH hz (σ 0) c₂ (fun τ => hM₁ τ c₂)
  have hS₂ : ∑ a', twSq n (Gres H z (σ 1) * TwistKer_fE n a * Gres H z (σ 2)) a' c₁ ≤ P * M₃ :=
    TwistKer_ward_col3 n hH hz (σ 1) (σ 2) a c₁ (fun τ => hM₃ ![σ 2, !σ 2, τ] ![c₁, a, a])
  have hs0 : ∀ (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (b c : Zd d (sz.L n)), 0 ≤ twSq n X b c := fun X b c => by
    unfold twSq; positivity
  calc ∑ a', ‖twL3 C n v ω σ a' a c₁ c₂‖
      ≤ ∑ a', Real.sqrt (twSq n (Gres H z (σ 0)) c₂ a') * Real.sqrt (twSq n (Gres H z (σ 1) * TwistKer_fE n a * Gres H z (σ 2)) a' c₁) := by
        refine Finset.sum_le_sum fun a' _ => ?_
        rw [← Real.sqrt_mul (hs0 _ _ _)]
        exact Real.le_sqrt_of_sq_le (TwistKer_twL3_fold1 n C hH v ω hG σ a' a c₁ c₂)
    _ ≤ Real.sqrt (∑ a', twSq n (Gres H z (σ 0)) c₂ a') * Real.sqrt (∑ a', twSq n (Gres H z (σ 1) * TwistKer_fE n a * Gres H z (σ 2)) a' c₁) :=
        Real.sum_sqrt_mul_sqrt_le _ (fun a' => hs0 _ _ _) (fun a' => hs0 _ _ _)
    _ ≤ Real.sqrt (P * M₁) * Real.sqrt (P * M₃) :=
        mul_le_mul (Real.sqrt_le_sqrt hS₁) (Real.sqrt_le_sqrt hS₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = P * Real.sqrt (M₁ * M₃) := by
        rw [← Real.sqrt_mul (by positivity), show P * M₁ * (P * M₃) = P ^ 2 * (M₁ * M₃) by ring,
          Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq hP0]

/-- The second term of `(D.3)`: `Σ_{a'} |L̃^{(3)}_{(a,a')}| ≤ (W^d η)⁻¹ (M₁ M₃)^{1/2}` (fold at the twist and at `a'` = the middle vertex). -/
private theorem TwistKer_sum_twL3_second (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (hz : 0 < z.im) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 3 → Bool) (a c₁ c₂ : Zd d (sz.L n))
    {M₁ M₃ : ℝ} (hM₁ : ∀ τ : Bool, ∀ c : Zd d (sz.L n), ‖loopFine d (sz.L n) (sz.W n) H z ![τ] ![c]‖ ≤ M₁)
    (hM₃ : ∀ (τ : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)), ‖loopFine d (sz.L n) (sz.W n) H z τ b‖ ≤ M₃) :
    ∑ a', ‖twL3 C n v ω σ a a' c₁ c₂‖ ≤ ((((sz.W n : ℕ) : ℝ) ^ d) * z.im)⁻¹ * Real.sqrt (M₁ * M₃) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set P : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * z.im)⁻¹ with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ true 0)
  have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ (fun _ => true) (fun _ => 0))
  have hS₁ : ∑ a', twSq n (Gres H z (σ 0) * TwistKer_fE n a * Gres H z (σ 1)) c₂ a' ≤ P * M₃ :=
    TwistKer_ward_row3 n hH hz (σ 0) (σ 1) a c₂ (fun τ => hM₃ ![!σ 0, σ 0, τ] ![c₂, a, a])
  have hS₂ : ∑ a', twSq n (Gres H z (σ 2)) a' c₁ ≤ P * M₁ :=
    TwistKer_ward_col1 n hH hz (σ 2) c₁ (fun τ => hM₁ τ c₁)
  have hs0 : ∀ (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (b c : Zd d (sz.L n)), 0 ≤ twSq n X b c := fun X b c => by
    unfold twSq; positivity
  calc ∑ a', ‖twL3 C n v ω σ a a' c₁ c₂‖
      ≤ ∑ a', Real.sqrt (twSq n (Gres H z (σ 0) * TwistKer_fE n a * Gres H z (σ 1)) c₂ a') * Real.sqrt (twSq n (Gres H z (σ 2)) a' c₁) := by
        refine Finset.sum_le_sum fun a' _ => ?_
        rw [← Real.sqrt_mul (hs0 _ _ _)]
        exact Real.le_sqrt_of_sq_le (TwistKer_twL3_fold2 n C hH v ω hG σ a a' c₁ c₂)
    _ ≤ Real.sqrt (∑ a', twSq n (Gres H z (σ 0) * TwistKer_fE n a * Gres H z (σ 1)) c₂ a') * Real.sqrt (∑ a', twSq n (Gres H z (σ 2)) a' c₁) :=
        Real.sum_sqrt_mul_sqrt_le _ (fun a' => hs0 _ _ _) (fun a' => hs0 _ _ _)
    _ ≤ Real.sqrt (P * M₃) * Real.sqrt (P * M₁) :=
        mul_le_mul (Real.sqrt_le_sqrt hS₁) (Real.sqrt_le_sqrt hS₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = P * Real.sqrt (M₁ * M₃) := by
        rw [← Real.sqrt_mul (by positivity), show P * M₃ * (P * M₁) = P ^ 2 * (M₁ * M₃) by ring,
          Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq hP0]

/-- **The deterministic bound of the source `Ẽ^{G̊}` (T.11 (ii))**: `|Ẽ^{G̊}_v(a)| ≤ 2 m η⁻¹ (M₁ M₃)^{1/2}` from `|Tr(G̊(σ)E_{a'})| ≤ m` (`m ≺ W^{-d}B`), `max|𝓛^{(1)}| ≤ M₁`,
`max|𝓛^{(3)}| ≤ M₃` (`TwistKer_sum_twL3_first`, `TwistKer_sum_twL3_second`). -/
theorem TwistKer_twEG_le (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (hz : 0 < z.im) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true)
    (hL : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), C.L n v σ a ω = loopFine d (sz.L n) (sz.W n) H z σ a)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) {m M₁ M₃ : ℝ}
    (htr : ∀ (τ : Bool) (a' : Zd d (sz.L n)), ‖C.L n v ![τ] ![a'] ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))‖ ≤ m)
    (hM₁ : ∀ (τ : Bool) (c : Zd d (sz.L n)), ‖C.L n v ![τ] ![c] ω‖ ≤ M₁)
    (hM₃ : ∀ (τ : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)), ‖C.L n v τ b ω‖ ≤ M₃) :
    ‖twEG C n v ω σ a c₁ c₂‖ ≤ 2 * m * (z.im⁻¹ * Real.sqrt (M₁ * M₃)) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hM₁' : ∀ (τ : Bool) (c : Zd d (sz.L n)), ‖loopFine d (sz.L n) (sz.W n) H z ![τ] ![c]‖ ≤ M₁ := fun τ c => by
    rw [← hL 1]; exact hM₁ τ c
  have hM₃' : ∀ (τ : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)), ‖loopFine d (sz.L n) (sz.W n) H z τ b‖ ≤ M₃ := fun τ b => by
    rw [← hL 3]; exact hM₃ τ b
  have hm : 0 ≤ m := (norm_nonneg _).trans (htr true 0)
  have h1 := TwistKer_sum_twL3_first n C hH hz v ω hG ![σ 0, σ 0, σ 1] a c₁ c₂ hM₁' hM₃'
  have h2 := TwistKer_sum_twL3_second n C hH hz v ω hG ![σ 0, σ 1, σ 1] a c₁ c₂ hM₁' hM₃'
  unfold twEG
  dsimp only
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hsum : ‖∑ a', ((C.L n v ![σ 0] ![a'] ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
        twL3 C n v ω ![σ 0, σ 0, σ 1] a' a c₁ c₂ +
      (C.L n v ![σ 1] ![a'] ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * twL3 C n v ω ![σ 0, σ 1, σ 1] a a' c₁ c₂)‖ ≤
      2 * m * ((((sz.W n : ℕ) : ℝ) ^ d * z.im)⁻¹ * Real.sqrt (M₁ * M₃)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a', ‖(C.L n v ![σ 0] ![a'] ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
            twL3 C n v ω ![σ 0, σ 0, σ 1] a' a c₁ c₂ +
          (C.L n v ![σ 1] ![a'] ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * twL3 C n v ω ![σ 0, σ 1, σ 1] a a' c₁ c₂‖
        ≤ ∑ a', (m * ‖twL3 C n v ω ![σ 0, σ 0, σ 1] a' a c₁ c₂‖ + m * ‖twL3 C n v ω ![σ 0, σ 1, σ 1] a a' c₁ c₂‖) := by
          refine Finset.sum_le_sum fun a' _ => ?_
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (htr (σ 0) a') (norm_nonneg _)
          · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (htr (σ 1) a') (norm_nonneg _)
      _ = m * ∑ a', ‖twL3 C n v ω ![σ 0, σ 0, σ 1] a' a c₁ c₂‖ + m * ∑ a', ‖twL3 C n v ω ![σ 0, σ 1, σ 1] a a' c₁ c₂‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ m * ((((sz.W n : ℕ) : ℝ) ^ d * z.im)⁻¹ * Real.sqrt (M₁ * M₃)) + m * ((((sz.W n : ℕ) : ℝ) ^ d * z.im)⁻¹ * Real.sqrt (M₁ * M₃)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hm) (mul_le_mul_of_nonneg_left h2 hm)
      _ = 2 * m * ((((sz.W n : ℕ) : ℝ) ^ d * z.im)⁻¹ * Real.sqrt (M₁ * M₃)) := by ring
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ a', _‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (2 * m * ((((sz.W n : ℕ) : ℝ) ^ d * z.im)⁻¹ * Real.sqrt (M₁ * M₃))) :=
        mul_le_mul_of_nonneg_left hsum hW.le
    _ = 2 * m * (z.im⁻¹ * Real.sqrt (M₁ * M₃)) := by
        have hz0 : z.im ≠ 0 := hz.ne'
        field_simp

/-- `|[a]| = W^d`. -/
private theorem TwistKer_card_blk (a : Zd d (sz.L n)) : ((twBlk n a).card : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d := by
  have : (twBlk n a).card = (sz.W n) ^ d := card_Iblk d (sz.L n) (sz.W n) a
  rw [this]; push_cast; rfl

/-- A sum over a set is at most its cardinality times the bound of the summands. -/
private theorem TwistKer_norm_sum_le {β : Type*} (s : Finset β) (f : β → ℂ) {m : ℝ} (h : ∀ i ∈ s, ‖f i‖ ≤ m) :
    ‖∑ i ∈ s, f i‖ ≤ (s.card : ℝ) * m :=
  (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul s _ m h).trans (by rw [nsmul_eq_mul]))

/-- `‖W^{-d}‖ = (W^d)⁻¹`. -/
private theorem TwistKer_norm_winv : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  simp

private theorem TwistKer_W_pos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
  have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  positivity

/-- A double sum over two blocks of summands of norm `≤ m`: `‖Σ_{x∈[a]} Σ_{w∈[c]} f x w‖ ≤ W^{2d} m`. -/
private theorem TwistKer_norm_sum2_le (a c : Zd d (sz.L n)) (f : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) {m : ℝ}
    (h : ∀ x ∈ twBlk n a, ∀ w ∈ twBlk n c, ‖f x w‖ ≤ m) :
    ‖∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c, f x w‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * m) := by
  have := TwistKer_norm_sum_le (twBlk n a) (fun x => ∑ w ∈ twBlk n c, f x w) (m := ((sz.W n : ℕ) : ℝ) ^ d * m) (fun x hx => by
    have := TwistKer_norm_sum_le (twBlk n c) (fun w => f x w) (m := m) (fun w hw => h x hx w hw)
    rwa [TwistKer_card_blk] at this)
  rwa [TwistKer_card_blk] at this

/-- The average of the entries: `|L̃_{σ,(a;c₁,c₂)}| ≤ m` if every summand `|X₂(x,w) X₁(w', x)| ≤ m` (`x ∈ [a]`, `w ∈ [c₁]`). -/
private theorem TwistKer_twLoopX_le (X₁ X₂ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a c₁ c₂ : Zd d (sz.L n)) {m : ℝ}
    (h : ∀ x ∈ twBlk n a, ∀ w ∈ twBlk n c₁, ‖X₂ x w * X₁ (twShift n c₂ w) x‖ ≤ m) : ‖twLoopX n X₁ X₂ a c₁ c₂‖ ≤ m := by
  have hW := TwistKer_W_pos n (sz := sz)
  unfold twLoopX
  rw [norm_mul, norm_pow, TwistKer_norm_winv]
  have h2 := TwistKer_norm_sum2_le n a c₁ (fun x w => X₂ x w * X₁ (twShift n c₂ w) x) h
  calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ‖∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, X₂ x w * X₁ (twShift n c₂ w) x‖
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * m)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = m := by field_simp

/-- The average of the entries of `L̃^{(3)}`: `|L̃^{(3)}| ≤ m` if every summand is `≤ m`. -/
private theorem TwistKer_twL3_le (C : FlowFM sz) (v : ℝ) (ω : sz.SeqΩ) (σ : Fin 3 → Bool) (a₁ a₂ c₁ c₂ : Zd d (sz.L n)) {m : ℝ}
    (h : ∀ x ∈ twBlk n a₁, ∀ y ∈ twBlk n a₂, ∀ w ∈ twBlk n c₁,
      ‖twChg (C.G n v ω) (σ 0) (twShift n c₂ w) x * twChg (C.G n v ω) (σ 1) x y * twChg (C.G n v ω) (σ 2) y w‖ ≤ m) :
    ‖twL3 C n v ω σ a₁ a₂ c₁ c₂‖ ≤ m := by
  have hW := TwistKer_W_pos n (sz := sz)
  unfold twL3
  rw [norm_mul, norm_pow, TwistKer_norm_winv]
  have h3 := TwistKer_norm_sum_le (twBlk n a₁) (fun x => ∑ y ∈ twBlk n a₂, ∑ w ∈ twBlk n c₁,
      twChg (C.G n v ω) (σ 0) (twShift n c₂ w) x * twChg (C.G n v ω) (σ 1) x y * twChg (C.G n v ω) (σ 2) y w)
    (m := ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * m)) (fun x hx => TwistKer_norm_sum2_le n a₂ c₁ _ (fun y hy w hw => h x hx y hy w hw))
  rw [TwistKer_card_blk] at h3
  calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 * ‖∑ x ∈ twBlk n a₁, ∑ y ∈ twBlk n a₂, ∑ w ∈ twBlk n c₁,
        twChg (C.G n v ω) (σ 0) (twShift n c₂ w) x * twChg (C.G n v ω) (σ 1) x y * twChg (C.G n v ω) (σ 2) y w‖
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * m))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = m := by field_simp

/-- The average of the entries of `∂_{xy} L̃`: `|∂_{xy} L̃_v(b)| ≤ m₁ + m₂`. -/
private theorem TwistKer_twDer_le (C : FlowFM sz) (v : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n))
    (x y : Idx d (sz.L n) (sz.W n)) {m₁ m₂ : ℝ}
    (h₁ : ∀ z ∈ twBlk n b, ∀ w ∈ twBlk n c₁,
      ‖twChg (C.G n v ω) (σ 0) y z * twChg (C.G n v ω) (σ 1) z w * twChg (C.G n v ω) (σ 0) (twShift n c₂ w) x‖ ≤ m₁)
    (h₂ : ∀ w ∈ twBlk n c₁, ∀ z ∈ twBlk n b,
      ‖twChg (C.G n v ω) (σ 1) y w * twChg (C.G n v ω) (σ 0) (twShift n c₂ w) z * twChg (C.G n v ω) (σ 1) z x‖ ≤ m₂) :
    ‖twDer C n v ω σ b c₁ c₂ x y‖ ≤ m₁ + m₂ := by
  have hW := TwistKer_W_pos n (sz := sz)
  unfold twDer
  dsimp only
  rw [norm_mul, norm_neg, norm_pow, TwistKer_norm_winv]
  have h1 := TwistKer_norm_sum2_le n b c₁ (fun z w => twChg (C.G n v ω) (σ 0) y z * twChg (C.G n v ω) (σ 1) z w *
    twChg (C.G n v ω) (σ 0) (twShift n c₂ w) x) h₁
  have h2 := TwistKer_norm_sum2_le n c₁ b (fun w z => twChg (C.G n v ω) (σ 1) y w * twChg (C.G n v ω) (σ 0) (twShift n c₂ w) z *
    twChg (C.G n v ω) (σ 1) z x) h₂
  calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ‖(∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, twChg (C.G n v ω) (σ 0) y z * twChg (C.G n v ω) (σ 1) z w *
          twChg (C.G n v ω) (σ 0) (twShift n c₂ w) x) +
        ∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, twChg (C.G n v ω) (σ 1) y w * twChg (C.G n v ω) (σ 0) (twShift n c₂ w) z * twChg (C.G n v ω) (σ 1) z x‖
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * m₁) +
          ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * m₂)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) (by positivity)
    _ = m₁ + m₂ := by field_simp

/-- Membership in a block. -/
private theorem TwistKer_mem_blk {c : Zd d (sz.L n)} {x : Idx d (sz.L n) (sz.W n)} :
    x ∈ twBlk n c ↔ (split d (sz.L n) (sz.W n) x).1 = c := by
  simp [twBlk]

/-- **Entries of `G`**: `|G(σ)_{yx}| ≤ η⁻¹` (a copy of the private `EMCTE2_norm_Gres_entry_le`, `Universality/EMCTE2.lean:144`). -/
theorem TwistKer_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (σ : Bool) (x y : ι) : ‖Gres H z σ x y‖ ≤ (z.im)⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (RBM.Gauss.norm_Gsig_le_inv_eta hH hz (le_of_eq (abs_of_pos hz).symm) σ)

/-- **`L̃` (T.11 helper)**: `|L̃_{σ,(a;c₁,c₂)}| ≤ Λ²`, and `≤ ν Λ` if `|a - c₁|_∞ ≥ X` (entries of `G` between blocks at distance `≥ X` are `≤ ν`, all entries `≤ Λ`). -/
theorem TwistKer_twL2_bounds (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) {Λ ν X : ℝ}
    (hν : 0 ≤ ν) (hbd : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)), ‖Gres H z τ y x‖ ≤ Λ)
    (hDec : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)),
      X ≤ (zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - (split d (sz.L n) (sz.W n) x).1) : ℝ) → ‖Gres H z τ y x‖ ≤ ν) :
    ‖twL2' C n v ω σ a c₁ c₂‖ ≤ Λ * Λ ∧
      (X ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ) → ‖twL2' C n v ω σ a c₁ c₂‖ ≤ ν * Λ) := by
  have e : twL2' C n v ω σ a c₁ c₂ = twLoopX n (Gres H z (σ 0)) (Gres H z (σ 1)) a c₁ c₂ := by
    unfold twL2'; rw [TwistKer_twChg_eq n hH hG, TwistKer_twChg_eq n hH hG]
  rw [e]
  refine ⟨TwistKer_twLoopX_le n _ _ a c₁ c₂ fun x _ w _ => ?_, fun hX => TwistKer_twLoopX_le n _ _ a c₁ c₂ fun x hx w hw => ?_⟩
  · rw [norm_mul]
    exact mul_le_mul (hbd _ _ _) (hbd _ _ _) (norm_nonneg _) ((norm_nonneg _).trans (hbd true x w))
  · have hx' := (TwistKer_mem_blk n).1 hx
    have hw' := (TwistKer_mem_blk n).1 hw
    rw [norm_mul]
    exact mul_le_mul (hDec _ _ _ (by rw [hx', hw']; exact hX)) (hbd _ _ _) (norm_nonneg _) hν

/-- `L̃^{(3)}` decays when one of the entries between `(a₁, a₂)` or `(a₂, c₁)` does: `|L̃^{(3)}| ≤ Λ² ν`. -/
private theorem TwistKer_twL3_decay (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 3 → Bool) (a₁ a₂ c₁ c₂ : Zd d (sz.L n)) {Λ ν X : ℝ}
    (hν : 0 ≤ ν) (hbd : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)), ‖Gres H z τ y x‖ ≤ Λ)
    (hDec : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)),
      X ≤ (zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - (split d (sz.L n) (sz.W n) x).1) : ℝ) → ‖Gres H z τ y x‖ ≤ ν)
    (hX : X ≤ (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ∨ X ≤ (zdistInf d (sz.L n) (a₂ - c₁) : ℝ)) :
    ‖twL3 C n v ω σ a₁ a₂ c₁ c₂‖ ≤ Λ * (Λ * ν) := by
  refine TwistKer_twL3_le n C v ω σ a₁ a₂ c₁ c₂ fun x hx y hy w hw => ?_
  have hx' := (TwistKer_mem_blk n).1 hx
  have hy' := (TwistKer_mem_blk n).1 hy
  have hw' := (TwistKer_mem_blk n).1 hw
  simp only [TwistKer_twChg_eq n hH hG, norm_mul]
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hbd true x w)
  rcases hX with hX | hX
  · have h2 := hDec (σ 1) x y (by rw [hx', hy']; exact hX)
    calc ‖Gres H z (σ 0) (twShift n c₂ w) x‖ * ‖Gres H z (σ 1) x y‖ * ‖Gres H z (σ 2) y w‖ ≤ Λ * ν * Λ :=
          mul_le_mul (mul_le_mul (hbd _ _ _) h2 (norm_nonneg _) hΛ0) (hbd _ _ _) (norm_nonneg _) (mul_nonneg hΛ0 hν)
      _ = Λ * (Λ * ν) := by ring
  · have h3 := hDec (σ 2) y w (by rw [hy', hw']; exact hX)
    calc ‖Gres H z (σ 0) (twShift n c₂ w) x‖ * ‖Gres H z (σ 1) x y‖ * ‖Gres H z (σ 2) y w‖ ≤ Λ * Λ * ν :=
          mul_le_mul (mul_le_mul (hbd _ _ _) (hbd _ _ _) (norm_nonneg _) hΛ0) h3 (norm_nonneg _) (mul_nonneg hΛ0 hΛ0)
      _ = Λ * (Λ * ν) := by ring

/-- Triangle inequality of the `L^∞` distance. -/
private theorem TwistKer_zdistInf_add_le (L : ℕ) [NeZero L] (x y : Zd d L) : zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  refine Finset.sup_le fun i _ => (zdist_add_le L (x i) (y i)).trans (add_le_add ?_ ?_)
  · exact Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)
  · exact Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)

/-- `|p - r| ≥ 2X` forces `|p - q| ≥ X` or `|q - r| ≥ X`. -/
theorem TwistKer_far_split (L : ℕ) [NeZero L] {X : ℝ} (p q r : Zd d L) (h : 2 * X ≤ (zdistInf d L (p - r) : ℝ)) :
    X ≤ (zdistInf d L (p - q) : ℝ) ∨ X ≤ (zdistInf d L (q - r) : ℝ) := by
  by_contra hcon
  push Not at hcon
  have h1 := TwistKer_zdistInf_add_le (d := d) L (p - q) (q - r)
  rw [show p - q + (q - r) = p - r by ring] at h1
  have h2 : (zdistInf d L (p - r) : ℝ) ≤ (zdistInf d L (p - q) : ℝ) + (zdistInf d L (q - r) : ℝ) := by exact_mod_cast h1
  linarith [hcon.1, hcon.2]

/-- **The source `Ẽ^{G̊}` decays** when `|a - c₁|_∞ ≥ 2X`: `|Ẽ^{G̊}_v(a)| ≤ N · 2 M (Λ² ν)` (`M` bounds `|Tr(G̊(σ)E_{a'})|`). -/
theorem TwistKer_twEG_decay (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) {Λ ν X Mt : ℝ}
    (hν : 0 ≤ ν) (hX0 : 0 ≤ X) (hbd : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)), ‖Gres H z τ y x‖ ≤ Λ)
    (hDec : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)),
      X ≤ (zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - (split d (sz.L n) (sz.W n) x).1) : ℝ) → ‖Gres H z τ y x‖ ≤ ν)
    (htr : ∀ (τ : Bool) (a' : Zd d (sz.L n)), ‖C.L n v ![τ] ![a'] ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))‖ ≤ Mt)
    (hX : 2 * X ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ)) :
    ‖twEG C n v ω σ a c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (2 * (Mt * (Λ * (Λ * ν)))) := by
  have hW := TwistKer_W_pos n (sz := sz)
  have hMt : 0 ≤ Mt := (norm_nonneg _).trans (htr true 0)
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  unfold twEG
  dsimp only
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hterm : ∀ a' : Zd d (sz.L n), ‖(C.L n v ![σ 0] ![a'] ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
        twL3 C n v ω ![σ 0, σ 0, σ 1] a' a c₁ c₂ +
      (C.L n v ![σ 1] ![a'] ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * twL3 C n v ω ![σ 0, σ 1, σ 1] a a' c₁ c₂‖ ≤
      2 * (Mt * (Λ * (Λ * ν))) := by
    intro a'
    refine (norm_add_le _ _).trans ?_
    have h1 := TwistKer_twL3_decay n C hH v ω hG ![σ 0, σ 0, σ 1] a' a c₁ c₂ hν hbd hDec (Or.inr (by linarith))
    have h2 := TwistKer_twL3_decay n C hH v ω hG ![σ 0, σ 1, σ 1] a a' c₁ c₂ hν hbd hDec (TwistKer_far_split (sz.L n) a a' c₁ hX)
    rw [norm_mul, norm_mul]
    have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hbd true 0 0)
    have e1 := mul_le_mul (htr (σ 0) a') h1 (norm_nonneg _) hMt
    have e2 := mul_le_mul (htr (σ 1) a') h2 (norm_nonneg _) hMt
    linarith
  have hsum : ‖∑ a', ((C.L n v ![σ 0] ![a'] ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
        twL3 C n v ω ![σ 0, σ 0, σ 1] a' a c₁ c₂ +
      (C.L n v ![σ 1] ![a'] ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * twL3 C n v ω ![σ 0, σ 1, σ 1] a a' c₁ c₂)‖ ≤
      ((sz.L n : ℕ) : ℝ) ^ d * (2 * (Mt * (Λ * (Λ * ν)))) := by
    refine (TwistKer_norm_sum_le Finset.univ _ (fun a' _ => hterm a')).trans ?_
    rw [Finset.card_univ, card_Zd]
    push_cast
    exact le_rfl
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ a', _‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (2 * (Mt * (Λ * (Λ * ν))))) :=
        mul_le_mul_of_nonneg_left hsum hW.le
    _ = ((sz.size n : ℕ) : ℝ) * (2 * (Mt * (Λ * (Λ * ν)))) := by rw [hsize]; ring

/-- `|∂_{xy} L̃_v(b)| ≤ 2 Λ³` for all `x, y`. -/
private theorem TwistKer_twDer_gen (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n))
    (x y : Idx d (sz.L n) (sz.W n)) {Λ : ℝ} (hbd : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)), ‖Gres H z τ y x‖ ≤ Λ) :
    ‖twDer C n v ω σ b c₁ c₂ x y‖ ≤ 2 * (Λ * (Λ * Λ)) := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hbd true 0 0)
  have h : ∀ (τ₁ τ₂ τ₃ : Bool) (p q r : Idx d (sz.L n) (sz.W n)), ‖Gres H z τ₁ p q * Gres H z τ₂ q r‖ ≤ Λ * Λ := fun _ _ _ p q r => by
    rw [norm_mul]; exact mul_le_mul (hbd _ _ _) (hbd _ _ _) (norm_nonneg _) hΛ0
  have h3 : ∀ (τ₁ τ₂ τ₃ : Bool) (p q r s' t u : Idx d (sz.L n) (sz.W n)), ‖Gres H z τ₁ p q * Gres H z τ₂ r s' * Gres H z τ₃ t u‖ ≤ Λ * (Λ * Λ) :=
    fun τ₁ τ₂ τ₃ p q r s' t u => by
      rw [norm_mul, norm_mul]
      calc ‖Gres H z τ₁ p q‖ * ‖Gres H z τ₂ r s'‖ * ‖Gres H z τ₃ t u‖ ≤ Λ * Λ * Λ :=
          mul_le_mul (mul_le_mul (hbd _ _ _) (hbd _ _ _) (norm_nonneg _) hΛ0) (hbd _ _ _) (norm_nonneg _) (mul_nonneg hΛ0 hΛ0)
        _ = Λ * (Λ * Λ) := by ring
  have := TwistKer_twDer_le n C v ω σ b c₁ c₂ x y (m₁ := Λ * (Λ * Λ)) (m₂ := Λ * (Λ * Λ))
    (fun z' _ w _ => by simp only [TwistKer_twChg_eq n hH hG]; exact h3 _ _ _ _ _ _ _ _ _)
    (fun w _ z' _ => by simp only [TwistKer_twChg_eq n hH hG]; exact h3 _ _ _ _ _ _ _ _ _)
  linarith

/-- `∂_{xy} L̃_v(b)` decays when `|b - c₁|_∞ ≥ 2X` and `[x] = [y]`: `|∂_{xy} L̃_v(b)| ≤ 2 Λ² ν`. -/
private theorem TwistKer_twDer_decay (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n))
    (x y : Idx d (sz.L n) (sz.W n)) (hxy : (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1) {Λ ν X : ℝ}
    (hν : 0 ≤ ν) (hX0 : 0 ≤ X) (hbd : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)), ‖Gres H z τ y x‖ ≤ Λ)
    (hDec : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)),
      X ≤ (zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - (split d (sz.L n) (sz.W n) x).1) : ℝ) → ‖Gres H z τ y x‖ ≤ ν)
    (hX : 2 * X ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ)) :
    ‖twDer C n v ω σ b c₁ c₂ x y‖ ≤ 2 * (Λ * (Λ * ν)) := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hbd true 0 0)
  have := TwistKer_twDer_le n C v ω σ b c₁ c₂ x y (m₁ := Λ * (Λ * ν)) (m₂ := Λ * (Λ * ν))
    (fun z' hz' w hw => by
      have hz'' := (TwistKer_mem_blk n).1 hz'
      have hw'' := (TwistKer_mem_blk n).1 hw
      simp only [TwistKer_twChg_eq n hH hG, norm_mul]
      have h2 := hDec (σ 1) z' w (by rw [hz'', hw'']; linarith)
      calc ‖Gres H z (σ 0) y z'‖ * ‖Gres H z (σ 1) z' w‖ * ‖Gres H z (σ 0) (twShift n c₂ w) x‖ ≤ Λ * ν * Λ :=
          mul_le_mul (mul_le_mul (hbd _ _ _) h2 (norm_nonneg _) hΛ0) (hbd _ _ _) (norm_nonneg _) (mul_nonneg hΛ0 hν)
        _ = Λ * (Λ * ν) := by ring)
    (fun w hw z' hz' => by
      have hz'' := (TwistKer_mem_blk n).1 hz'
      have hw'' := (TwistKer_mem_blk n).1 hw
      simp only [TwistKer_twChg_eq n hH hG, norm_mul]
      have hsp := TwistKer_far_split (sz.L n) b (split d (sz.L n) (sz.W n) y).1 c₁ hX
      rcases hsp with h | h
      · have h2 := hDec (σ 1) z' x (by rw [hz'', hxy]; exact h)
        calc ‖Gres H z (σ 1) y w‖ * ‖Gres H z (σ 0) (twShift n c₂ w) z'‖ * ‖Gres H z (σ 1) z' x‖ ≤ Λ * Λ * ν :=
            mul_le_mul (mul_le_mul (hbd _ _ _) (hbd _ _ _) (norm_nonneg _) hΛ0) h2 (norm_nonneg _) (mul_nonneg hΛ0 hΛ0)
          _ = Λ * (Λ * ν) := by ring
      · have h2 := hDec (σ 1) y w (by rw [hw'']; exact h)
        calc ‖Gres H z (σ 1) y w‖ * ‖Gres H z (σ 0) (twShift n c₂ w) z'‖ * ‖Gres H z (σ 1) z' x‖ ≤ ν * Λ * Λ :=
            mul_le_mul (mul_le_mul h2 (hbd _ _ _) (norm_nonneg _) hν) (hbd _ _ _) (norm_nonneg _) (mul_nonneg hν hΛ0)
          _ = Λ * (Λ * ν) := by ring)
  linarith

/-- **The quadratic-variation source `(Ẽ⊗Ẽ)_v(a, b')` decays** in `a` when `|a - c₁|_∞ ≥ 2X` (`S = I` at BA: `C.S` is supported on the diagonal and `≤ 1`):
`|(Ẽ⊗Ẽ)(a,b')| ≤ N² · 2Λ²ν · 2Λ³` for every `b'`. -/
theorem TwistKer_twEE_decay (C : FlowFM sz) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (v : ℝ) (ω : sz.SeqΩ) (hG : C.G n v ω = Gres H z true) (σ : Fin 2 → Bool) (a b' c₁ c₂ : Zd d (sz.L n)) {Λ ν X : ℝ}
    (hν : 0 ≤ ν) (hX0 : 0 ≤ X) (hbd : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)), ‖Gres H z τ y x‖ ≤ Λ)
    (hDec : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)),
      X ≤ (zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - (split d (sz.L n) (sz.W n) x).1) : ℝ) → ‖Gres H z τ y x‖ ≤ ν)
    (hS0 : ∀ p q : Zd d (sz.L n), p ≠ q → C.S n p q = 0) (hS1 : ∀ p q : Zd d (sz.L n), ‖C.S n p q‖ ≤ 1)
    (hX : 2 * X ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ)) :
    ‖twEE C n v ω σ a b' c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 * (2 * (Λ * (Λ * ν)) * (2 * (Λ * (Λ * Λ)))) := by
  have hW := TwistKer_W_pos n (sz := sz)
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hbd true 0 0)
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  have hW1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
  set Bd : ℝ := 2 * (Λ * (Λ * ν)) * (2 * (Λ * (Λ * Λ))) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hterm : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
      (twDer C n v ω σ a c₁ c₂ x y * (starRingEnd ℂ) (twDer C n v ω σ b' c₁ c₂ x y))‖ ≤ Bd := by
    intro x y
    by_cases hxy : (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1
    · rw [norm_mul, norm_mul, norm_mul, TwistKer_norm_winv, Complex.norm_conj]
      have h1 := TwistKer_twDer_decay n C hH v ω hG σ a c₁ c₂ x y hxy hν hX0 hbd hDec hX
      have h2 := TwistKer_twDer_gen n C hH v ω hG σ b' c₁ c₂ x y hbd
      have hS := hS1 (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖C.S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1‖ *
            (‖twDer C n v ω σ a c₁ c₂ x y‖ * ‖twDer C n v ω σ b' c₁ c₂ x y‖) ≤ 1 * 1 * Bd := by
            refine mul_le_mul (mul_le_mul hW1 hS (norm_nonneg _) zero_le_one) (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
        _ = Bd := by ring
    · rw [hS0 _ _ hxy]
      simpa using hBd0
  unfold twEE
  have hinner : ∀ x : Idx d (sz.L n) (sz.W n), ‖∑ y : Idx d (sz.L n) (sz.W n),
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (twDer C n v ω σ a c₁ c₂ x y * (starRingEnd ℂ) (twDer C n v ω σ b' c₁ c₂ x y))‖ ≤ ((sz.size n : ℕ) : ℝ) * Bd := by
    intro x
    have := TwistKer_norm_sum_le (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))) (fun y =>
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (twDer C n v ω σ a c₁ c₂ x y * (starRingEnd ℂ) (twDer C n v ω σ b' c₁ c₂ x y))) (m := Bd) (fun y _ => hterm x y)
    rw [Finset.card_univ, Sizes.card_Idx] at this
    exact this
  have hout := TwistKer_norm_sum_le (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))) (fun x => ∑ y : Idx d (sz.L n) (sz.W n),
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (twDer C n v ω σ a c₁ c₂ x y * (starRingEnd ℂ) (twDer C n v ω σ b' c₁ c₂ x y))) (m := ((sz.size n : ℕ) : ℝ) * Bd) (fun x _ => hinner x)
  rw [Finset.card_univ, Sizes.card_Idx] at hout
  calc _ ≤ _ := hout
    _ = ((sz.size n : ℕ) : ℝ) ^ 2 * Bd := by ring

/-- Symmetry of the `L^∞` distance. -/
theorem TwistKer_zdistInf_neg (L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  simp only [Pi.neg_apply, zdist_neg]

/-- **`|𝓛^{(2)}| ≤ η⁻²`** (every charge pair): the sandwich of `E_a`, `E_b` against entries `≤ η⁻¹`. -/
theorem TwistKer_loop2_le {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (σ₀ σ₁ : Bool) (a b : Zd d (sz.L n)) :
    ‖loopFine d (sz.L n) (sz.W n) H z ![σ₀, σ₁] ![a, b]‖ ≤ (z.im)⁻¹ * (z.im)⁻¹ := by
  have hW := TwistKer_W_pos n (sz := sz)
  have hΛ0 : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  rw [TwistKer_loop2, TwistKer_trace_sandwich, norm_mul, norm_pow, TwistKer_norm_winv]
  have h2 := TwistKer_norm_sum2_le n b a (fun i j => Gres H z σ₀ i j * Gres H z σ₁ j i) (m := (z.im)⁻¹ * (z.im)⁻¹) (fun i _ j _ => by
    rw [norm_mul]; exact mul_le_mul (TwistKer_entry_le hH hz _ _ _) (TwistKer_entry_le hH hz _ _ _) (norm_nonneg _) hΛ0)
  calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ‖∑ i ∈ twBlk n b, ∑ j ∈ twBlk n a, Gres H z σ₀ i j * Gres H z σ₁ j i‖
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * ((z.im)⁻¹ * (z.im)⁻¹))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (z.im)⁻¹ * (z.im)⁻¹ := by field_simp

/-- **Entries of `G` between far blocks from the 2-loop** (`TP` Lemma T.5, `n = 2`): if `‖𝓛^{(2)}_{(+,-),(p,q)}‖ ≤ ρ` for all blocks with `|p - q|_∞ ≥ X`, then every entry
`|G(σ)_{yx}| ≤ W^d ρ^{1/2}` with `|[y] - [x]|_∞ ≥ X`. -/
theorem TwistKer_entry_decay {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {z : ℂ} {X ρ : ℝ}
    (hloop : ∀ p q : Zd d (sz.L n), X ≤ (zdistInf d (sz.L n) (p - q) : ℝ) →
      ‖loopFine d (sz.L n) (sz.W n) H z ![true, false] ![p, q]‖ ≤ ρ) :
    ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)),
      X ≤ (zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - (split d (sz.L n) (sz.W n) x).1) : ℝ) →
        ‖Gres H z τ y x‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * Real.sqrt ρ := by
  have hW := TwistKer_W_pos n (sz := sz)
  have hneg : ∀ p q : Zd d (sz.L n), zdistInf d (sz.L n) (q - p) = zdistInf d (sz.L n) (p - q) := fun p q => by
    rw [← neg_sub p q, TwistKer_zdistInf_neg]
  have key : ∀ y x : Idx d (sz.L n) (sz.W n),
      X ≤ (zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - (split d (sz.L n) (sz.W n) x).1) : ℝ) →
        ‖Gres H z true y x‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * Real.sqrt ρ := by
    intro y x hyx
    have h1 := TwistKer_entry_le_loop2 n hH z y x
    have h2 := hloop (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 (by rw [hneg]; exact hyx)
    have h3 : ‖Gres H z true y x‖ ^ 2 ≤ (((sz.W n : ℕ) : ℝ) ^ d) ^ 2 * ρ :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    have h4 : ‖Gres H z true y x‖ ≤ Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2 * ρ) := Real.le_sqrt_of_sq_le h3
    have hρ : 0 ≤ ρ := (norm_nonneg _).trans h2
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW.le] at h4
    exact h4
  intro τ y x hyx
  cases τ
  · have h := TwistKer_Gres_conjTranspose hH z true
    simp only [Bool.not_true] at h
    rw [← h, Matrix.conjTranspose_apply, Complex.star_def, Complex.norm_conj]
    exact key x y (by rw [hneg]; exact hyx)
  · exact key y x hyx

/-- **`|𝓛^{(1)}| ≤ η⁻¹`**: `𝓛^{(1)}_{σ,c} = W^{-d} Σ_{y∈[c]} G(σ)_{yy}`. -/
theorem TwistKer_loop1_le {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (σ : Bool) (c : Zd d (sz.L n)) : ‖loopFine d (sz.L n) (sz.W n) H z ![σ] ![c]‖ ≤ (z.im)⁻¹ := by
  have hW := TwistKer_W_pos n (sz := sz)
  rw [TwistKer_loop1, Matrix.trace_mul_comm, TwistKer_trace_fE_mul, norm_mul, TwistKer_norm_winv]
  have h := TwistKer_norm_sum_le (twBlk n c) (fun y => Gres H z σ y y) (m := (z.im)⁻¹) (fun y _ => TwistKer_entry_le hH hz _ _ _)
  rw [TwistKer_card_blk] at h
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ y ∈ twBlk n c, Gres H z σ y y‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * (z.im)⁻¹) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (z.im)⁻¹ := by field_simp

end Fine

end RBM.BA

end
