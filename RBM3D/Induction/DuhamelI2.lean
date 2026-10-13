/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.DuhamelI
import RBM3D.Induction.PfStep5Grid
import RBM3D.Chain.GridRepTailGen2

/-!
# S5-15 (T2333; T2496, U4s3b): the integrated hierarchy at `n = 2`, case (i), over the flow carrier

`stDuhamelI_holds : ∀ d, STDuhamelI d` (`3_5:1941-2069`: `(int_K-LcalE_n=2)`,
`(jymwons)`..`(iois-mtx2)`) and the engine `stDuhamelConclgL_engine` (zero-mode set `∅`, every
sign class `P`), over a carrier `(Cm : Step2Mat sz, μ)`; the generic pin `stDuhamelIgL_of`
(`STDuhamelIgL`, `Chain/Step5Gen.lean`), and the band theorems `stDuhamelConcl_engine`,
`stDuhamelI_holds` (names and types unchanged) as its corollaries through `STDuhamelI_iff_gL`.
The kernel and numerics part is in `Induction/DuhamelI`.

Section 1: the grid Duhamel form `duhamelIG_duhamel` (target 6; the port of
`BA/Step5IIIWalk.lean:304-671`, `Step5IIIWalk_duhamel`, with the names `duhamelIG_*`, `BA/*` not
being importable here).  Section 2: the model-free scalar helpers of the pathwise bound (moved
from `DuhamelI` section 5).  Section 3: the pathwise bound at one size index (`duhamelIG_path_rem`:
the drift term and the martingale term through `Φ`).  Section 4: the per-section statement
`duhamelIG_section` (the grid events E1-E6 through F9 `Step2EventsGen_Grid`). Section 5: the
engine, the pin, the band discharges and the compiled instances.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open private duhamelI_zdistInf_sub_comm duhamelI_tailW_eq duhamelI_cardK duhamelI_measure_le from RBM3D.Induction.DuhamelI
open private Step5KerGen_cmp_pos from RBM3D.Chain.Step5KerGen
open private pfStep5Grid_abs pfStep5Grid_slot pfStep5Grid_slot_apply pfStep5Grid_slot_add pfStep5Grid_slot_sub
  pfStep5Grid_slot_smul pfStep5Grid_slot_one pfStep5Grid_norm_slot pfStep5Grid_sum2 pfStep5Grid_update2
  pfStep5Grid_update2' pfStep5Grid_alg pfStep5Grid_inv_le from RBM3D.Induction.PfStep5Grid

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.BA

section KernelG

variable {d : ℕ}

/-! ## 1. Target 6: the grid Duhamel form at the carrier kernel -/

section Duhamel

open scoped Matrix.Norms.Operator

variable {sz : Sizes d} {C : FlowFM sz} {n : ℕ}

/-- The `ℓ^∞` operator norm of a matrix is at most `ρ` when every row sum is. -/
private theorem duhamelIG_norm_le_rows {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ a, ∑ b, ‖A a b‖ ≤ ρ) : ‖A‖ ≤ ρ := by
  rw [Matrix.linfty_opNorm_def]
  have hs : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ ρ.toNNReal := Finset.sup_le fun a _ => by
    rw [← NNReal.coe_le_coe]
    simpa [NNReal.coe_sum, Real.coe_toNNReal _ hρ] using h a
  have := NNReal.coe_le_coe.mpr hs
  simpa [Real.coe_toNNReal _ hρ] using this

/-- **K1 gives the one-slot identity** `u_{s,t} = 1 + (t - s) θ_t` (`0 ≤ t < 1`, every `s`): `u_{t,t} = 1` and `u_{s,t} = (1 - sX) Θ_t`,
`θ_t = X Θ_t` (`Chain/Step2Gen.lean:188-193`). -/
private theorem duhamelIG_uKer_eq (hker : GridRepTailGen_Ker C n) (σ σ' : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    Step2Gen_uKer C n σ σ' s t = 1 + ((t - s : ℝ) : ℂ) • Step2Gen_thetaKer C n σ σ' t := by
  have h1 : Step2Gen_uKer C n σ σ' t t = 1 := (hker.1 σ σ' 0 t t ht0 ht1 ht0 ht1).1
  unfold Step2Gen_uKer at h1 ⊢
  unfold Step2Gen_thetaKer
  set X := Step2Kern_Mss C n σ σ' * C.S n with hX
  have hsplit : (1 - (s : ℂ) • X) = (1 - (t : ℂ) • X) + ((t - s : ℝ) : ℂ) • X := by
    push_cast; rw [sub_smul]; abel
  rw [hsplit, add_mul, h1, smul_mul_assoc]


/-- Row sums of `θ_t`: K3 at `s = -1` (`u_{-1,t} - 1 = (t + 1) θ_t`). -/
private theorem duhamelIG_theta_rows (hker : GridRepTailGen_Ker C n) (σ σ' : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Zd d (sz.L n)) : ∑ b, ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ (1 - t)⁻¹ := by
  have h3 := hker.2.2.1 σ σ' (-1) t ht0 ht1 a
  have e : ∀ b, ‖Step2Gen_uKer C n σ σ' (-1) t a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ =
      (t + 1) * ‖Step2Gen_thetaKer C n σ σ' t a b‖ := by
    intro b
    rw [duhamelIG_uKer_eq hker σ σ' ht0 ht1 (-1)]
    simp only [Matrix.add_apply, Matrix.smul_apply, add_sub_cancel_left, smul_eq_mul, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg (by linarith)]
    ring
  simp only [e, ← Finset.mul_sum] at h3
  have habs : |t - -1| = t + 1 := by rw [abs_of_nonneg (by linarith)]; ring
  rw [habs] at h3
  have hpos : 0 < t + 1 := by linarith
  have : (t + 1) * ∑ b, ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ (t + 1) * (1 - t)⁻¹ := h3
  exact le_of_mul_le_mul_left this hpos

private theorem duhamelIG_theta_norm (hker : GridRepTailGen_Ker C n) (σ σ' : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖Step2Gen_thetaKer C n σ σ' t‖ ≤ (1 - t)⁻¹ :=
  duhamelIG_norm_le_rows _ (inv_nonneg.2 (by linarith)) (duhamelIG_theta_rows hker σ σ' ht0 ht1)

/-- The resolvent identity `θ_w - θ_v = (w - v) θ_w θ_v` from K1 (the semigroup law with `u = -1`) and the one-slot identity. -/
private theorem duhamelIG_theta_resolvent (hker : GridRepTailGen_Ker C n) (σ σ' : Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Step2Gen_thetaKer C n σ σ' w - Step2Gen_thetaKer C n σ σ' v =
      ((w - v : ℝ) : ℂ) • (Step2Gen_thetaKer C n σ σ' w * Step2Gen_thetaKer C n σ σ' v) := by
  have hs := (hker.1 σ σ' (-1) v w hv0 hv1 hw0 hw1).2
  rw [duhamelIG_uKer_eq hker σ σ' hw0 hw1 v, duhamelIG_uKer_eq hker σ σ' hv0 hv1 (-1),
    duhamelIG_uKer_eq hker σ σ' hw0 hw1 (-1)] at hs
  set θw := Step2Gen_thetaKer C n σ σ' w
  set θv := Step2Gen_thetaKer C n σ σ' v
  have hc : ((v + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : v + 1 ≠ 0)
  refine smul_right_injective _ hc ?_
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at hs
  push_cast at hs ⊢
  simp only [smul_sub, smul_smul]
  linear_combination (norm := module) (-1 : ℂ) • hs

/-! ### The operators `𝒰_{v,w}`, `Θ^{(2)}_t` on the sup-normed 2-index tensors -/

section Ops

variable (C) (n) (σ : Fin 2 → Bool)

/-- `𝒰_{v,w}` as a bounded operator: slot `0` and slot `1` of the one-index kernel `uKer` at the charges `(σ_i, σ_{i+1})`. -/
private def duhamelIG_Uc (v w : ℝ) :
    ((Fin 2 → Zd d (sz.L n)) → ℂ) →L[ℂ] ((Fin 2 → Zd d (sz.L n)) → ℂ) :=
  pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_uKer C n (σ 0) (σ (finRotate 2 0)) v w) *
    pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_uKer C n (σ 1) (σ (finRotate 2 1)) v w)

/-- `Θ^{(2)}_t` as a bounded operator. -/
private def duhamelIG_Tc (t : ℝ) :
    ((Fin 2 → Zd d (sz.L n)) → ℂ) →L[ℂ] ((Fin 2 → Zd d (sz.L n)) → ℂ) :=
  pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) t) +
    pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) t)

variable {C} {n} {σ}

private theorem duhamelIG_Uc_apply (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (v w : ℝ) :
    duhamelIG_Uc C n σ v w A = Step2Gen_UN C n σ v w A := by
  funext a
  rw [duhamelIG_Uc, mul_apply_eq_comp]
  simp only [Step2Gen_UN, pfStep5Grid_slot_apply, Fin.prod_univ_two]
  rw [pfStep5Grid_sum2]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [pfStep5Grid_update2', pfStep5Grid_update2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem duhamelIG_Tc_apply (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (t : ℝ) :
    duhamelIG_Tc C n σ t A = Step2Gen_ThetaN C n σ t A := by
  funext a
  simp only [duhamelIG_Tc, Step2Gen_ThetaN, Fin.sum_univ_two, Pi.add_apply, _root_.add_apply, pfStep5Grid_slot_apply]

end Ops

/-! ### Norm bounds from K1-K3 -/

section Norms

variable {σ : Fin 2 → Bool} (hker : GridRepTailGen_Ker C n)
include hker

/-- the slot operator of `θ_x`, `0 ≤ x ≤ ut < 1`, has norm `≤ (1 - ut)⁻¹`. -/
private theorem duhamelIG_norm_slotTheta (i : Fin 2) {x ut : ℝ} (hx0 : 0 ≤ x) (hxu : x ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_slot d (sz.L n) i (Step2Gen_thetaKer C n (σ i) (σ (finRotate 2 i)) x)‖ ≤ (1 - ut)⁻¹ :=
  (pfStep5Grid_norm_slot d (sz.L n) i _).trans
    ((duhamelIG_theta_norm hker _ _ hx0 (lt_of_le_of_lt hxu hu1)).trans (pfStep5Grid_inv_le hxu hu1))

private theorem duhamelIG_norm_Tc {x ut : ℝ} (hx0 : 0 ≤ x) (hxu : x ≤ ut) (hu1 : ut < 1) :
    ‖duhamelIG_Tc C n σ x‖ ≤ 2 * (1 - ut)⁻¹ := by
  unfold duhamelIG_Tc
  have h0 := duhamelIG_norm_slotTheta hker (σ := σ) 0 hx0 hxu hu1
  have h1 := duhamelIG_norm_slotTheta hker (σ := σ) 1 hx0 hxu hu1
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (1 - ut)⁻¹ + (1 - ut)⁻¹ := add_le_add h0 h1
    _ = 2 * (1 - ut)⁻¹ := by ring

/-- `‖θ_w - θ_v‖ ≤ (w - v) (1 - ut)⁻²` (the resolvent identity). -/
private theorem duhamelIG_theta_sub_norm (σ' σ'' : Bool) {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut)
    (hu1 : ut < 1) :
    ‖Step2Gen_thetaKer C n σ' σ'' w - Step2Gen_thetaKer C n σ' σ'' v‖ ≤ (w - v) * ((1 - ut)⁻¹) ^ 2 := by
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hv1 : v < 1 := lt_of_le_of_lt hvw hw1
  rw [duhamelIG_theta_resolvent hker σ' σ'' hv0 hv1 (hv0.trans hvw) hw1, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]
  refine mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans ?_) (by linarith)
  have h1 := (duhamelIG_theta_norm hker σ' σ'' (hv0.trans hvw) hw1).trans (pfStep5Grid_inv_le hwu hu1)
  have h2 := (duhamelIG_theta_norm hker σ' σ'' hv0 hv1).trans (pfStep5Grid_inv_le (hvw.trans hwu) hu1)
  calc _ ≤ (1 - ut)⁻¹ * (1 - ut)⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) (inv_nonneg.2 (by linarith))
    _ = ((1 - ut)⁻¹) ^ 2 := by ring

private theorem duhamelIG_norm_Tc_sub {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖duhamelIG_Tc C n σ w - duhamelIG_Tc C n σ v‖ ≤ 2 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by
  have hB : ∀ i : Fin 2, ‖pfStep5Grid_slot d (sz.L n) i (Step2Gen_thetaKer C n (σ i) (σ (finRotate 2 i)) w -
      Step2Gen_thetaKer C n (σ i) (σ (finRotate 2 i)) v)‖ ≤ (w - v) * ((1 - ut)⁻¹) ^ 2 := fun i =>
    (pfStep5Grid_norm_slot d (sz.L n) i _).trans (duhamelIG_theta_sub_norm hker _ _ hv0 hvw hwu hu1)
  have e : duhamelIG_Tc C n σ w - duhamelIG_Tc C n σ v =
      pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w -
        Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) v) +
      pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w -
        Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) v) := by
    unfold duhamelIG_Tc
    rw [pfStep5Grid_slot_sub, pfStep5Grid_slot_sub]
    abel
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (w - v) * ((1 - ut)⁻¹) ^ 2 + (w - v) * ((1 - ut)⁻¹) ^ 2 := add_le_add (hB 0) (hB 1)
    _ = 2 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by ring

private theorem duhamelIG_norm_uKer (σ' σ'' : Bool) {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut)
    (hu1 : ut < 1) : ‖Step2Gen_uKer C n σ' σ'' v w‖ ≤ (1 - ut)⁻¹ := by
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have h1 : (1 - v) / (1 - w) ≤ (1 - w)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (by linarith)) (by linarith)
  have h2 : 0 ≤ (1 - v) / (1 - w) := div_nonneg (by linarith) (by linarith)
  exact (duhamelIG_norm_le_rows _ h2 (hker.2.1 σ' σ'' v w hv0 hvw hw1)).trans (h1.trans (pfStep5Grid_inv_le hwu hu1))

private theorem duhamelIG_norm_Uc {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖duhamelIG_Uc C n σ v w‖ ≤ ((1 - ut)⁻¹) ^ 2 := by
  have hB : ∀ i : Fin 2, ‖pfStep5Grid_slot d (sz.L n) i (Step2Gen_uKer C n (σ i) (σ (finRotate 2 i)) v w)‖ ≤
      (1 - ut)⁻¹ := fun i =>
    (pfStep5Grid_norm_slot d (sz.L n) i _).trans (duhamelIG_norm_uKer hker _ _ hv0 hvw hwu hu1)
  unfold duhamelIG_Uc
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ (1 - ut)⁻¹ * (1 - ut)⁻¹ :=
        mul_le_mul (hB 0) (hB 1) (norm_nonneg _) (inv_nonneg.mpr (by linarith))
    _ = ((1 - ut)⁻¹) ^ 2 := by ring

private theorem duhamelIG_Uc_expand {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    duhamelIG_Uc C n σ v w - 1 - ((w - v : ℝ) : ℂ) • duhamelIG_Tc C n σ w =
      (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w) *
          pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w)) := by
  unfold duhamelIG_Uc duhamelIG_Tc
  rw [duhamelIG_uKer_eq hker _ _ hw0 hw1 v, duhamelIG_uKer_eq hker _ _ hw0 hw1 v,
    pfStep5Grid_slot_add, pfStep5Grid_slot_add, pfStep5Grid_slot_smul, pfStep5Grid_slot_smul,
    pfStep5Grid_slot_one, pfStep5Grid_slot_one]
  exact pfStep5Grid_alg _ _ _

private theorem duhamelIG_norm_quad {w ut : ℝ} (hw0 : 0 ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w) *
          pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w)‖ ≤
      ((1 - ut)⁻¹) ^ 2 := by
  have h0 := duhamelIG_norm_slotTheta hker (σ := σ) 0 hw0 hwu hu1
  have h1 := duhamelIG_norm_slotTheta hker (σ := σ) 1 hw0 hwu hu1
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ (1 - ut)⁻¹ * (1 - ut)⁻¹ :=
        mul_le_mul h0 h1 (norm_nonneg _) (inv_nonneg.mpr (by linarith))
    _ = ((1 - ut)⁻¹) ^ 2 := by ring

private theorem duhamelIG_norm_Uc_sub_one {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖duhamelIG_Uc C n σ v w - 1‖ ≤ 3 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hB1 : 1 ≤ (1 - ut)⁻¹ := by
    rw [one_le_inv₀ (by linarith)]; linarith
  have hδ0 : 0 ≤ w - v := by linarith
  have hδ1 : w - v ≤ 1 := by
    have : 0 ≤ v := hv0
    nlinarith
  have hδn : ‖((w - v : ℝ) : ℂ)‖ = w - v := by
    rw [Complex.norm_real, Real.norm_of_nonneg hδ0]
  have e := duhamelIG_Uc_expand hker (σ := σ) (v := v) hw0 hw1
  have e' : duhamelIG_Uc C n σ v w - 1 =
      ((w - v : ℝ) : ℂ) • duhamelIG_Tc C n σ w + (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w) *
          pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w)) := by
    rw [← e]; abel
  rw [e']
  have hT := duhamelIG_norm_Tc hker (σ := σ) hw0 hwu hu1
  have hQ := duhamelIG_norm_quad hker (σ := σ) hw0 hwu hu1
  set B := (1 - ut)⁻¹ with hBdef
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (w - v) * (2 * B) + (w - v) * (w - v) * B ^ 2 := by
        rw [norm_smul, norm_smul, hδn, norm_mul, hδn]
        exact add_le_add (mul_le_mul_of_nonneg_left hT hδ0)
          (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ ≤ 3 * (w - v) * B ^ 2 := by
        have h1 : B ≤ B ^ 2 := by nlinarith
        have h2 : (w - v) * (w - v) * B ^ 2 ≤ 1 * (w - v) * B ^ 2 := by
          have := mul_le_mul_of_nonneg_right hδ1 hδ0
          have := mul_le_mul_of_nonneg_right this (sq_nonneg B)
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hδ0]

private theorem duhamelIG_norm_Uc_sub_one_Tc {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖duhamelIG_Uc C n σ v w - 1 - ((w - v : ℝ) : ℂ) • duhamelIG_Tc C n σ v‖ ≤
      3 * (w - v) ^ 2 * ((1 - ut)⁻¹) ^ 2 := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hδ0 : 0 ≤ w - v := by linarith
  have hδn : ‖((w - v : ℝ) : ℂ)‖ = w - v := by
    rw [Complex.norm_real, Real.norm_of_nonneg hδ0]
  have e := duhamelIG_Uc_expand hker (σ := σ) (v := v) hw0 hw1
  have e' : duhamelIG_Uc C n σ v w - 1 - ((w - v : ℝ) : ℂ) • duhamelIG_Tc C n σ v =
      ((w - v : ℝ) : ℂ) • (duhamelIG_Tc C n σ w - duhamelIG_Tc C n σ v) +
        (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w) *
          pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w)) := by
    rw [← e, smul_sub]; abel
  rw [e']
  have hT := duhamelIG_norm_Tc_sub hker (σ := σ) hv0 hvw hwu hu1
  have hQ := duhamelIG_norm_quad hker (σ := σ) hw0 hwu hu1
  set B := (1 - ut)⁻¹ with hBdef
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (w - v) * (2 * (w - v) * B ^ 2) + (w - v) * (w - v) * B ^ 2 := by
        rw [norm_smul, norm_smul, hδn, norm_mul, hδn]
        exact add_le_add (mul_le_mul_of_nonneg_left hT hδ0)
          (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = 3 * (w - v) ^ 2 * B ^ 2 := by ring

end Norms

/-! ### The Duhamel form -/

/-- **The Duhamel form `(int_K-L_ST)` at the kernel `Step2Gen_UN` of a carrier with K1-K3** (deterministic, any 2-index tensors; band
`pfStep5Grid_duhamel`, `Induction/PfStep5Grid.lean:892`, with the energy bound and the unit modulus of `m` replaced by the kernel class): on a grid
`u_{j+1} = u_j + Δ`, `0 ≤ u_0`, `u_k < 1`, if `A_j = A_0 + Δ Σ_{i<j} (Θ^{(2)}_{u_i,σ} A_i + F_i) + Rem_j + Mart_j` for `j ≤ k` with
`|A_j| ≤ M`, `|Rem_j| ≤ R`, then
`|A_k - 𝒰_{u_0,u_k} A_0 - Δ Σ_{j<k} 𝒰_{u_j,u_k} F_j - Σ_{j<k} 𝒰_{u_j,u_k}(Mart_{j+1} - Mart_j)| ≤ 64 (1-u_k)^{-7} (R + Δ M)`. -/
theorem _root_.RBM.BA.duhamelIG_duhamel (hker : GridRepTailGen_Ker C n) (Δ M R : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ)
    (A F Rem Mart : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0)
    (hu : ∀ j, u (j + 1) = u j + Δ) (hk : u k < 1)
    (hA : ∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) (hRem : ∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R)
    (hrec : ∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (Step2Gen_ThetaN C n σ (u i) (A i) b + F i b) + Rem j b + Mart j b)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖A k a - Step2Gen_UN C n σ (u 0) (u k) (A 0) a -
        ∑ j ∈ Finset.range k, (Δ : ℂ) * Step2Gen_UN C n σ (u j) (u k) (F j) a -
        ∑ j ∈ Finset.range k, Step2Gen_UN C n σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
      64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) := by
  have hmono : Monotone u := monotone_nat_of_le_succ fun j => by rw [hu j]; linarith
  have hform : ∀ j, u j = u 0 + j * Δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hu j, ih]; push_cast; ring
  have hunn : ∀ j, 0 ≤ u j := fun j => hu0.trans (hmono (Nat.zero_le j))
  have hlt : ∀ j, j ≤ k → u j < 1 := fun j hj => lt_of_le_of_lt (hmono hj) hk
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    have := hform k
    have := hunn 0
    linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have hR : 0 ≤ R := (norm_nonneg _).trans (hRem 0 (Nat.zero_le _) 0)
  have hB : 1 ≤ ((1 - u k)⁻¹) := by
    rw [one_le_inv₀ (by linarith [hunn k])]
    linarith [hunn k]
  have hB0 : 0 ≤ ((1 - u k)⁻¹) := by linarith
  have hrhs : 0 ≤ 64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) := by positivity
  cases k with
  | zero =>
    have h0 : Step2Gen_UN C n σ (u 0) (u 0) (A 0) = A 0 := Step2Gen_UN_self C n hker.1 σ (hunn 0) hk (A 0)
    simpa [h0] using hrhs
  | succ m =>
    have hu1 : u (m + 1) < 1 := hk
    have hmΔ : ((m : ℝ) + 1) * Δ ≤ 1 := by exact_mod_cast hkΔ
    have hd : ∀ j, u (j + 1) - u j = Δ := fun j => by rw [hu j]; ring
    have hPk : duhamelIG_Uc C n σ (u (m + 1)) (u (m + 1)) = 1 :=
      ContinuousLinearMap.ext fun B => by
        rw [duhamelIG_Uc_apply, one_apply_eq_self]
        exact Step2Gen_UN_self C n hker.1 σ (hunn _) hu1 B
    have hPX : ∀ j, j < m + 1 → duhamelIG_Uc C n σ (u j) (u (m + 1)) =
        duhamelIG_Uc C n σ (u (j + 1)) (u (m + 1)) * duhamelIG_Uc C n σ (u j) (u (j + 1)) := by
      intro j hj
      refine ContinuousLinearMap.ext fun B => ?_
      rw [mul_apply_eq_comp, duhamelIG_Uc_apply, duhamelIG_Uc_apply, duhamelIG_Uc_apply]
      exact (Step2Gen_UN_comp C n hker.1 σ (u := u j) (v := u (j + 1)) (w := u (m + 1))
        (hunn _) (hlt _ hj) (hunn _) hu1 B).symm
    have hP : ∀ j, j ≤ m + 1 → ‖duhamelIG_Uc C n σ (u j) (u (m + 1))‖ ≤ ((1 - u (m + 1))⁻¹) ^ 2 :=
      fun j hj => duhamelIG_norm_Uc hker (hunn j) (hmono hj) le_rfl hu1
    have hXn : ∀ j, j < m + 1 → ‖duhamelIG_Uc C n σ (u j) (u (j + 1))‖ ≤ ((1 - u (m + 1))⁻¹) ^ 2 :=
      fun j hj => duhamelIG_norm_Uc hker (hunn j) (hmono (Nat.le_succ j)) (hmono hj) hu1
    have hX1 : ∀ j, j < m + 1 → ‖duhamelIG_Uc C n σ (u j) (u (j + 1)) - 1‖ ≤
        3 * Δ * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      have := duhamelIG_norm_Uc_sub_one hker (σ := σ) (hunn j) (hmono (Nat.le_succ j)) (hmono hj) hu1
      rwa [hd] at this
    have hX2 : ∀ j, j < m + 1 → ‖duhamelIG_Uc C n σ (u j) (u (j + 1)) - 1 -
        (Δ : ℂ) • duhamelIG_Tc C n σ (u j)‖ ≤ 3 * Δ ^ 2 * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      have := duhamelIG_norm_Uc_sub_one_Tc hker (σ := σ) (hunn j) (hmono (Nat.le_succ j)) (hmono hj) hu1
      rwa [hd] at this
    have hΘ : ∀ j, j < m + 1 → ‖duhamelIG_Tc C n σ (u j)‖ ≤ 2 * ((1 - u (m + 1))⁻¹) :=
      fun j hj => duhamelIG_norm_Tc hker (hunn j) (hmono (Nat.le_of_lt hj)) hu1
    have hΘΘ : ∀ j, j + 1 < m + 1 → ‖duhamelIG_Tc C n σ (u j) -
        duhamelIG_Tc C n σ (u (j + 1))‖ ≤ 2 * Δ * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      rw [norm_sub_rev]
      have := duhamelIG_norm_Tc_sub hker (σ := σ) (hunn j) (hmono (Nat.le_succ j)) (hmono hj.le) hu1
      rwa [hd] at this
    have hA' : ∀ j, j ≤ m + 1 → ‖A j‖ ≤ M := fun j hj => (pi_norm_le_iff_of_nonneg hM).mpr (hA j hj)
    have hRem' : ∀ j, j ≤ m + 1 → ‖Rem j‖ ≤ R := fun j hj => (pi_norm_le_iff_of_nonneg hR).mpr (hRem j hj)
    have hrec' : ∀ j, j < m + 1 → A (j + 1) - A j =
        (Δ : ℂ) • (duhamelIG_Tc C n σ (u j) (A j) + F j) + (Rem (j + 1) - Rem j) +
          (Mart (j + 1) - Mart j) := by
      intro j hj
      funext b
      have h1 := hrec (j + 1) (by omega) b
      have h0 := hrec j (by omega) b
      rw [Finset.sum_range_succ] at h1
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, duhamelIG_Tc_apply]
      linear_combination h1 - h0
    have habs := pfStep5Grid_abs (E := (Fin 2 → Zd d (sz.L n)) → ℂ) m Δ ((1 - u (m + 1))⁻¹) M R hB hΔ hmΔ
      (fun j => duhamelIG_Uc C n σ (u j) (u (m + 1)))
      (fun j => duhamelIG_Uc C n σ (u j) (u (j + 1)))
      (fun j => duhamelIG_Tc C n σ (u j)) A F Rem Mart hPk hPX hP hXn hX1 hX2 hΘ hΘΘ hA' hRem' hrec'
    refine le_trans ?_ habs
    refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ a)
    congr 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, duhamelIG_Uc_apply]
    rw [Finset.mul_sum]
    rfl


end Duhamel

/-! ## 2. Model-free scalar helpers of the pathwise bound (moved from `DuhamelI` section 5) -/

section Scalar

variable {d : ℕ}

private theorem duhamelI_grid (s tt : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ tt n) (hK : K n ≠ 0) :
    0 ≤ gridStep s tt K n ∧ (∀ j, gridTime s tt K n (j + 1) = gridTime s tt K n j + gridStep s tt K n) ∧
      gridTime s tt K n 0 = s n ∧ gridTime s tt K n (K n) = tt n ∧
      (K n : ℝ) * gridStep s tt K n = tt n - s n ∧
      (∀ j ≤ K n, s n ≤ gridTime s tt K n j ∧ gridTime s tt K n j ≤ tt n) ∧
      (∀ j < K n, gridTime s tt K n j ≤ gridTime s tt K n (j + 1)) := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ : 0 ≤ gridStep s tt K n := div_nonneg (by linarith) hKpos.le
  refine ⟨hΔ, fun j => ?_, ST_gridTime_zero s tt K n, gridTime_last s tt K n hK, ?_,
    fun j hj => ST_gridTime_mem s tt K n j hst hK hj, fun j _ => ?_⟩
  · unfold gridTime; push_cast; ring
  · unfold gridStep; field_simp
  · unfold gridTime; push_cast; nlinarith [hΔ]

/-- `W^{-d} 𝒯̃^L_{u,D}` is nondecreasing in the time. -/
private theorem duhamelI_prof_mono (sz : Sizes d) (n : ℕ) {u v D : ℝ} (hg : 0 ≤ sz.lam n) (huv : u ≤ v)
    (hv : v < 1) (x y : Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) x y ≤ STprof sz n v D ((sz.L n : ℕ) : ℝ) x y := by
  unfold STprof
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold tailW
  exact max_le_max (ST_tailT_mono_time (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    hg huv hv (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))) le_rfl

private theorem duhamelI_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

private theorem duhamelI_sqrt_aux {Λ ρ c₀ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 1 ≤ ρ) (hc₀ : 0 < c₀) :
    Real.sqrt (2 * Λ * ρ / c₀) ≤ Λ * ρ * (2 / c₀ + 1) := by
  have h1 : 2 * Λ * ρ / c₀ = (Λ * ρ) * (2 / c₀) := by ring
  rw [h1, Real.sqrt_mul (by positivity)]
  have hΛρ : 1 ≤ Λ * ρ := by nlinarith
  have hx : Real.sqrt (Λ * ρ) ≤ Λ * ρ := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hy : Real.sqrt (2 / c₀) ≤ 2 / c₀ + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg (2 / c₀)]
  exact mul_le_mul hx hy (Real.sqrt_nonneg _) (by positivity)

private theorem duhamelI_rpow_quarter {A : ℝ} (hA : 1 ≤ A) :
    0 < A ^ (-(1 / 4) : ℝ) ∧ A ^ (-(1 / 4) : ℝ) ≤ 1 ∧ A ^ (-(1 / 2) : ℝ) = (A ^ (-(1 / 4) : ℝ)) ^ 2 ∧
      A ^ (-(1 / 3) : ℝ) ≤ A ^ (-(1 / 4) : ℝ) := by
  have hA0 : 0 < A := by linarith
  refine ⟨Real.rpow_pos_of_pos hA0 _, Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num), ?_,
    Real.rpow_le_rpow_of_exponent_le hA (by norm_num)⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num

private theorem duhamelI_absorb {Λ κ F P Wm A ρ Nτ : ℝ} (hΛ : 1 ≤ Λ) (hκ : 0 ≤ κ) (hF : 0 ≤ F) (hP : 0 ≤ P)
    (hWm : 0 ≤ Wm) (hA : 1 ≤ A) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ (2 * A) ^ (1 / 100 : ℝ))
    (hN : (2 * κ + 1) * Λ ^ 2 ≤ Nτ) :
    Λ * F + Λ ^ 2 * κ * (ρ ^ 3 * A ^ (-(1 / 4) : ℝ)) * P + Wm ≤ Nτ * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) := by
  have hA0 : 0 < A := by linarith
  have h2A : (0 : ℝ) < 2 * A := by linarith
  have hρ3 : ρ ^ 3 ≤ 2 * A ^ (3 / 100 : ℝ) := by
    have h1 : ρ ^ 3 ≤ ((2 * A) ^ (1 / 100 : ℝ)) ^ 3 := pow_le_pow_left₀ (by linarith) hρ 3
    have h2 : ((2 * A) ^ (1 / 100 : ℝ)) ^ 3 = (2 * A) ^ (3 / 100 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2A.le]; norm_num
    have h3 : (2 * A) ^ (3 / 100 : ℝ) = 2 ^ (3 / 100 : ℝ) * A ^ (3 / 100 : ℝ) := Real.mul_rpow (by norm_num) hA0.le
    have h4 : (2 : ℝ) ^ (3 / 100 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (3 / 100 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    rw [h2, h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hA0.le _))
  have hexp : A ^ (3 / 100 : ℝ) * A ^ (-(1 / 4) : ℝ) ≤ A ^ (-(1 / 5) : ℝ) := by
    rw [← Real.rpow_add hA0]
    exact Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have h5 : ρ ^ 3 * A ^ (-(1 / 4) : ℝ) ≤ 2 * A ^ (-(1 / 5) : ℝ) := by
    have := mul_le_mul_of_nonneg_right hρ3 (Real.rpow_nonneg hA0.le (-(1 / 4) : ℝ))
    nlinarith
  have hA5 : 0 ≤ A ^ (-(1 / 5) : ℝ) := Real.rpow_nonneg hA0.le _
  have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
  have hΛ0 : 0 ≤ Λ ^ 2 := sq_nonneg Λ
  have s1 : Λ ^ 2 * κ * (ρ ^ 3 * A ^ (-(1 / 4) : ℝ)) * P ≤ Λ ^ 2 * κ * (2 * A ^ (-(1 / 5) : ℝ)) * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (mul_nonneg hΛ0 hκ)) hP
  have s2 : Λ * F ≤ Λ ^ 2 * F := mul_le_mul_of_nonneg_right hΛ2 hF
  have hX : 0 ≤ A ^ (-(1 / 5) : ℝ) * P := mul_nonneg hA5 hP
  have hN0 : 0 ≤ Nτ := le_trans (by positivity) hN
  have hΛ1 : 1 ≤ Λ ^ 2 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hκ hΛ0) hX, mul_nonneg hΛ0 hF, mul_nonneg hΛ0 hWm, mul_nonneg (mul_nonneg hκ hΛ0) hF,
    mul_nonneg (mul_nonneg hκ hΛ0) hWm, mul_le_mul_of_nonneg_right hN (add_nonneg (add_nonneg hF hX) hWm)]

end Scalar

/-! ## 3. The pathwise bound at one size index -/

section DriftG

variable {sz : Sizes d}

/-- The crude Riemann sum `Σ_{j<K} Δ η_{u_j}⁻¹ ≤ ρ / Im m` (`η_u = (1-u) Im m`, `u_j ≤ w`, `KΔ = w - s ≤ 1 - s`). -/
private theorem duhamelIG_riemann (Ck : FlowFM sz) (n : ℕ) (hη : ∀ v : ℝ, Ck.eta n v = (1 - v) * (Ck.m n).im) (u : ℕ → ℝ) (Δ s w : ℝ) (K : ℕ) (hΔ : 0 ≤ Δ)
    (hKΔ : (K : ℝ) * Δ = w - s) (hw : w < 1) (hu : ∀ j < K, u j ≤ w) (hc : 0 < (Ck.m n).im) :
    ∑ j ∈ Finset.range K, Δ * (Ck.eta n (u j))⁻¹ ≤ ((1 - s) / (1 - w)) / (Ck.m n).im := by
  have h1w : 0 < 1 - w := by linarith
  have hterm : ∀ j ∈ Finset.range K, Δ * (Ck.eta n (u j))⁻¹ ≤ Δ * ((1 - w) * (Ck.m n).im)⁻¹ := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ hΔ
    rw [hη]
    exact inv_anti₀ (mul_pos h1w hc)
      (mul_le_mul_of_nonneg_right (by linarith [hu j (Finset.mem_range.1 hj)]) hc.le)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (K : ℝ) * (Δ * ((1 - w) * (Ck.m n).im)⁻¹) = ((K : ℝ) * Δ) * ((1 - w) * (Ck.m n).im)⁻¹ := by ring
    _ = (w - s) * ((1 - w) * (Ck.m n).im)⁻¹ := by rw [hKΔ]
    _ ≤ (1 - s) * ((1 - w) * (Ck.m n).im)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith [hKΔ, mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) hΔ])
          (by positivity)
    _ = ((1 - s) / (1 - w)) / (Ck.m n).im := by field_simp


/-- The crude Riemann bound in the form used below: `Σ_{j<K} Δ η_{u_j}⁻¹ ≤ ρ / c₀` for `c₀ ≤ Im m`. -/
private theorem duhamelIG_riemann' (Ck : FlowFM sz) (n : ℕ) (hη : ∀ v : ℝ, Ck.eta n v = (1 - v) * (Ck.m n).im) (u : ℕ → ℝ) (Δ s w c₀ : ℝ) (K : ℕ) (hΔ : 0 ≤ Δ)
    (hKΔ : (K : ℝ) * Δ = w - s) (hsw : s ≤ w) (hw : w < 1) (hu : ∀ j < K, u j ≤ w) (hc₀ : 0 < c₀)
    (hc : c₀ ≤ (Ck.m n).im) :
    ∑ j ∈ Finset.range K, Δ * (Ck.eta n (u j))⁻¹ ≤ ((1 - s) / (1 - w)) / c₀ :=
  (duhamelIG_riemann Ck n hη u Δ s w K hΔ hKΔ hw hu (lt_of_lt_of_le hc₀ hc)).trans
    (div_le_div_of_nonneg_left (div_nonneg (by linarith) (by linarith)) hc₀ hc)

/-- **The drift term** (`(jymwons-L-K)`, `(jymwons-Gc)`): if `|F_j(b)| ≤ Λ e₀ η_{u_j}⁻¹ W^{-d}𝒯̃^L_{u_j,D}`, then
`|Δ Σ_{j<K} (𝒰_{u_j,w} ∘ F_j)_a| ≤ Λ e₀ (ρ/c₀) C ρ W^{-d}(𝒯_w + ρ W^{-D})`, `ρ = (1-s)/(1-w)`. -/
private theorem duhamelIG_drift (Ck : FlowFM sz) (n : ℕ) {s w Λ DE C c₀ e₀ Δ : ℝ} {K : ℕ} (u : ℕ → ℝ)
    (Fj : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hU : Step2Gen_USemigroup Ck n)
    (hpair : ∀ w : ℝ, 0 < w → w < 1 → Step2Gen_thetaKer Ck n (σ 1) (σ 0) w = Step2Gen_thetaKer Ck n (σ 0) (σ 1) w)
    (hη : ∀ v : ℝ, Ck.eta n v = (1 - v) * (Ck.m n).im) 
    (hs0 : 0 ≤ s) (hsw : s < w) (hw1 : w < 1) (hΛ : 0 ≤ Λ)
    (hC : 0 ≤ C) (he₀ : 0 ≤ e₀) (hc₀ : 0 < c₀) (hc : c₀ ≤ (Ck.m n).im) (hΔ : 0 ≤ Δ)
    (hKΔ : (K : ℝ) * Δ = w - s) (hu_s : ∀ j ≤ K, s ≤ u j) (hu_w : ∀ j ≤ K, u j ≤ w)
    (hΦ : ∀ (D' v w' : ℝ), s ≤ v → v ≤ w' → w' ≤ w → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w' x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w')) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w' ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w') * ((sz.W n : ℕ) : ℝ) ^ (-D'))))
    (hF : ∀ j ≤ K, ∀ b : Fin 2 → Zd d (sz.L n), ‖Fj j b‖ ≤ (Λ * e₀ * (Ck.eta n (u j))⁻¹) *
      STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) :
    ‖∑ j ∈ Finset.range K, (Δ : ℂ) * Step2Gen_UN Ck n σ (u j) w (Fj j) a‖ ≤
      Λ * e₀ * (((1 - s) / (1 - w)) / c₀) * (C * ((1 - s) / (1 - w)) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (tailT d (sz.L n) (sz.lam n) w
          ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + (1 - s) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-DE)))) := by
  have hw0 : 0 < w := lt_of_le_of_lt hs0 hsw
  have h1w : 0 < 1 - w := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hc0 : 0 < (Ck.m n).im := lt_of_lt_of_le hc₀ hc
  set ρ : ℝ := (1 - s) / (1 - w) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1w]; linarith
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 < Wd := by positivity
  set T : ℝ := tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hT
  set WmE : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-DE) with hWmE
  have hT0 : 0 ≤ T := tailT_nonneg (Nat.cast_nonneg _)
  have hWmE0 : 0 ≤ WmE := Real.rpow_nonneg hW.le _
  have hu_lt : ∀ j ≤ K, u j < 1 := fun j hj => (hu_w j hj).trans_lt hw1
  have hηp : ∀ j ≤ K, 0 < Ck.eta n (u j) := fun j hj => by
    rw [hη]; exact mul_pos (by linarith [hu_lt j hj]) hc0
  have hriem' := duhamelIG_riemann' Ck n hη u Δ s w c₀ K hΔ hKΔ hsw.le hw1 (fun j hj => hu_w j hj.le) hc₀ hc
  have hR0 : 0 ≤ C * ρ * (Wd * (T + ρ * WmE)) := by positivity
  have hterm : ∀ j ∈ Finset.range K, ‖(Δ : ℂ) * Step2Gen_UN Ck n σ (u j) w (Fj j) a‖ ≤
      Δ * ((Λ * e₀ * (Ck.eta n (u j))⁻¹) * (C * ρ * (Wd * (T + ρ * WmE)))) := by
    intro j hj
    have hjK : j ≤ K := (Finset.mem_range.1 hj).le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ]
    refine mul_le_mul_of_nonneg_left ?_ hΔ
    have hej : 0 ≤ Λ * e₀ * (Ck.eta n (u j))⁻¹ := by
      have := (hηp j hjK).le; positivity
    have h1 := duhamelIG_Ugen_le hU σ hpair (hs0.trans (hu_s j hjK)) (hu_w j hjK) hw0 hw1 (Fj j) a
    have h2 := duhamelI_Phi_mono (T := fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖)
      (h := 2 * (1 - u j)) (q := fun x y => ‖Fj j ![x, y]‖)
      (q' := fun x y => (Λ * e₀ * (Ck.eta n (u j))⁻¹) * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) x y)
      (fun x y => norm_nonneg _) (by linarith [hu_lt j hjK]) (fun x y => hF j hjK ![x, y]) a
    rw [duhamelI_Phi_smul] at h2
    have h4 := hΦ DE (u j) w (hu_s j hjK) (hu_w j hjK) le_rfl a
    have hρj : (1 - u j) / (1 - w) ≤ ρ := div_le_div_of_nonneg_right (by linarith [hu_s j hjK]) h1w.le
    have hρj0 : 0 ≤ (1 - u j) / (1 - w) := div_nonneg (by linarith [hu_lt j hjK]) h1w.le
    have h5 : C * ((1 - u j) / (1 - w)) * (Wd * (T + (1 - u j) / (1 - w) * WmE)) ≤
        C * ρ * (Wd * (T + ρ * WmE)) := by gcongr
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left (h4.trans h5) hej))
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  calc ∑ j ∈ Finset.range K, Δ * ((Λ * e₀ * (Ck.eta n (u j))⁻¹) * (C * ρ * (Wd * (T + ρ * WmE))))
      = (Λ * e₀ * (C * ρ * (Wd * (T + ρ * WmE)))) * ∑ j ∈ Finset.range K, Δ * (Ck.eta n (u j))⁻¹ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ (Λ * e₀ * (C * ρ * (Wd * (T + ρ * WmE)))) * (ρ / c₀) :=
        mul_le_mul_of_nonneg_left hriem' (by positivity)
    _ = _ := by ring

/-- **The martingale term** (`(uuwmskiow)`): if `|M_j(b)| ≤ Λ (Σ_{i<j} Δ Q_i(b) + N^{-D_m})^{1/2}` and
`Q_i(b) ≤ 2Λ A^{-1/2} η_{u_i}⁻¹ (W^{-d}𝒯̃^L_{u_i,D})²`, then `|Σ_{j<K} (𝒰_{u_j,w} ∘ ΔM_j)_a|` is at most
`4 (Λ² ρ (2/c₀+1) A^{-1/4} ρ² C W^{-d}(𝒯_w + W^{-D}) + Λ N^{-D_m/2} 9 ρ²)`, `ρ = (1-s)/(1-w)`. -/
private theorem duhamelIG_mart (Ck : FlowFM sz) (n : ℕ) {s w Λ DE Dm C c₀ Δ : ℝ} {K : ℕ} (u : ℕ → ℝ)
    (Mt : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) (Q : ℕ → (Fin 2 → Zd d (sz.L n)) → ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (hU : Step2Gen_USemigroup Ck n)
    (hpair : ∀ w : ℝ, 0 < w → w < 1 → Step2Gen_thetaKer Ck n (σ 1) (σ 0) w = Step2Gen_thetaKer Ck n (σ 0) (σ 1) w)
    (hη : ∀ v : ℝ, Ck.eta n v = (1 - v) * (Ck.m n).im) (hrow : ∀ w' : ℝ, 0 ≤ w' → w' < 1 → ∀ x : Zd d (sz.L n), ∑ y, ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w' x y‖ ≤ (1 - w')⁻¹)
    (hK1 : 1 ≤ K) (hs0 : 0 ≤ s) (hsw : s < w) (hw1 : w < 1)
    (hlam : 0 < sz.lam n) (hΛ : 1 ≤ Λ) (hA : 1 ≤ STAI sz n) (hc₀ : 0 < c₀) (hc : c₀ ≤ (Ck.m n).im)
    (hΔ : 0 ≤ Δ) (hKΔ : (K : ℝ) * Δ = w - s) (hu0 : u 0 = s) (hu_s : ∀ j ≤ K, s ≤ u j)
    (hu_w : ∀ j ≤ K, u j ≤ w) (hmono : ∀ j < K, u j ≤ u (j + 1))
    (hΦ : ∀ (D' v w' : ℝ), s ≤ v → v ≤ w' → w' ≤ w → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w' x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w')) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w' ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w') * ((sz.W n : ℕ) : ℝ) ^ (-D'))))
    (hQ0 : ∀ j b, 0 ≤ Q j b)
    (hQ : ∀ j ≤ K, ∀ b : Fin 2 → Zd d (sz.L n), Q j b ≤ 2 * (Λ * (STAI sz n ^ (-(1 / 2) : ℝ) *
      (Ck.eta n (u j))⁻¹ * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) ^ 2)))
    (hMart : ∀ (b : Fin 2 → Zd d (sz.L n)) (j : ℕ), j ≤ K → ‖Mt j b‖ ≤ Λ * Real.sqrt (∑ i ∈ Finset.range j,
      Δ * Q i b + ((sz.size n : ℕ) : ℝ) ^ (-Dm))) :
    ‖∑ j ∈ Finset.range K, Step2Gen_UN Ck n σ (u j) w
        (fun b => Mt (j + 1) b - Mt j b) a‖ ≤
      4 * ((Λ * (Λ * ((1 - s) / (1 - w)) * (2 / c₀ + 1) * STAI sz n ^ (-(1 / 4) : ℝ))) *
          (((1 - s) / (1 - w)) ^ 2 * (C * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
              ((sz.W n : ℕ) : ℝ) ^ (-DE))))) +
        (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * (9 * ((1 - s) / (1 - w)) ^ 2)) := by
  have hw0 : 0 < w := lt_of_le_of_lt hs0 hsw
  have h1w : 0 < 1 - w := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hc0 : 0 < (Ck.m n).im := lt_of_lt_of_le hc₀ hc
  set ρ : ℝ := (1 - s) / (1 - w) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1w]; linarith
  have hρe : 1 - s = ρ * (1 - w) := by rw [hρdef]; field_simp
  set A := STAI sz n with hAdef
  obtain ⟨ha₄0, ha₄1, ha₂, -⟩ := duhamelI_rpow_quarter hA
  set a₄ := A ^ (-(1 / 4) : ℝ) with ha₄def
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 < Wd := by positivity
  set T : ℝ := tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hT
  set WmE : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-DE) with hWmE
  have hT0 : 0 ≤ T := tailT_nonneg (Nat.cast_nonneg _)
  have hWmE0 : 0 ≤ WmE := Real.rpow_nonneg hW.le _
  have hu_lt : ∀ j ≤ K, u j < 1 := fun j hj => (hu_w j hj).trans_lt hw1
  have hu_nn : ∀ j ≤ K, 0 ≤ u j := fun j hj => hs0.trans (hu_s j hj)
  have hηp : ∀ j ≤ K, 0 < Ck.eta n (u j) := fun j hj => by
    rw [hη]; exact mul_pos (by linarith [hu_lt j hj]) hc0
  have hriem' := duhamelIG_riemann' Ck n hη u Δ s w c₀ K hΔ hKΔ hsw.le hw1 (fun j hj => hu_w j hj.le) hc₀ hc
  have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-Dm) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set Bf : (Fin 2 → Zd d (sz.L n)) → ℝ := fun b => Λ * Real.sqrt (∑ j ∈ Finset.range K, Δ * Q j b +
    ((sz.size n : ℕ) : ℝ) ^ (-Dm)) with hBf
  have hB : ∀ b j, j ≤ K → ‖Mt j b‖ ≤ Bf b := by
    intro b j hj
    refine (hMart b j hj).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add_left ?_ _)) (by linarith)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      (fun i _ _ => mul_nonneg hΔ (hQ0 _ _))
  have hMr_le := duhamelIG_mart_Ugen hU σ hpair u K hK1 hw0 hw1 hu_nn hu_w hmono Mt Bf hB a
  have hBb : ∀ b : Fin 2 → Zd d (sz.L n), Bf b ≤
      (Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * STprof sz n w DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) +
        Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm)) := by
    intro b
    set Pb := STprof sz n w DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) with hPb
    have hPb0 : 0 ≤ Pb := (ST_STprof_pos sz n _ _ _ _ _).le
    have hterm' : ∀ j ∈ Finset.range K, Δ * Q j b ≤ Δ * ((2 * Λ * a₄ ^ 2 * Pb ^ 2) * (Ck.eta n (u j))⁻¹) := by
      intro j hj
      have hjK := (Finset.mem_range.1 hj).le
      refine mul_le_mul_of_nonneg_left ?_ hΔ
      have hη0 : 0 ≤ (Ck.eta n (u j))⁻¹ := inv_nonneg.2 (hηp j hjK).le
      have hpj : STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) ≤ Pb :=
        duhamelI_prof_mono sz n hlam.le (hu_w j hjK) hw1 _ _
      have hpj0 := (ST_STprof_pos sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)).le
      refine (hQ j hjK b).trans ?_
      rw [ha₂]
      calc 2 * (Λ * (a₄ ^ 2 * (Ck.eta n (u j))⁻¹ * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) ^ 2))
          ≤ 2 * (Λ * (a₄ ^ 2 * (Ck.eta n (u j))⁻¹ * Pb ^ 2)) := by gcongr
        _ = _ := by ring
    have hQV : ∑ j ∈ Finset.range K, Δ * Q j b ≤ (2 * Λ * ρ / c₀) * (a₄ * Pb) ^ 2 := by
      refine (Finset.sum_le_sum hterm').trans ?_
      calc ∑ j ∈ Finset.range K, Δ * ((2 * Λ * a₄ ^ 2 * Pb ^ 2) * (Ck.eta n (u j))⁻¹)
          = (2 * Λ * a₄ ^ 2 * Pb ^ 2) * ∑ j ∈ Finset.range K, Δ * (Ck.eta n (u j))⁻¹ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ (2 * Λ * a₄ ^ 2 * Pb ^ 2) * (ρ / c₀) := mul_le_mul_of_nonneg_left hriem' (by positivity)
        _ = (2 * Λ * ρ / c₀) * (a₄ * Pb) ^ 2 := by ring
    have hS0 : 0 ≤ ∑ j ∈ Finset.range K, Δ * Q j b := Finset.sum_nonneg fun j _ => mul_nonneg hΔ (hQ0 _ _)
    have hsq := duhamelI_sqrt_aux hΛ hρ1 hc₀
    calc Bf b = Λ * Real.sqrt (∑ j ∈ Finset.range K, Δ * Q j b + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) := rfl
      _ ≤ Λ * (Real.sqrt (∑ j ∈ Finset.range K, Δ * Q j b) + Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) :=
          mul_le_mul_of_nonneg_left (duhamelI_sqrt_add hS0 hN0) (by linarith)
      _ ≤ Λ * (Real.sqrt ((2 * Λ * ρ / c₀) * (a₄ * Pb) ^ 2) + Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) := by
          gcongr
      _ = Λ * (Real.sqrt (2 * Λ * ρ / c₀) * (a₄ * Pb) + Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ ≤ Λ * ((Λ * ρ * (2 / c₀ + 1)) * (a₄ * Pb) + Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) := by
          gcongr
      _ = _ := by ring
  -- `Φ` of the bound
  set Tk : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖ with hTk
  have hTk0 : ∀ x y, 0 ≤ Tk x y := fun x y => norm_nonneg _
  have hh0 : 2 * (1 - u 0) = ρ * (2 * (1 - w)) := by rw [hu0, hρe]; ring
  have hΦ1 := duhamelI_Phi_mono (T := Tk) (h := 2 * (1 - u 0))
    (q := fun x y => Bf ![x, y])
    (q' := fun x y => (Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * STprof sz n w DE ((sz.L n : ℕ) : ℝ) x y +
      (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * 1) hTk0
    (by rw [hu0]; linarith) (fun x y => by simpa using hBb ![x, y]) a
  rw [duhamelI_Phi_lin] at hΦ1
  have hΦp : duhamelI_Phi Tk (2 * (1 - u 0)) (fun x y => STprof sz n w DE ((sz.L n : ℕ) : ℝ) x y) a ≤
      ρ ^ 2 * (C * (Wd * (T + WmE))) := by
    rw [hh0]
    refine (duhamelI_Phi_scale hTk0 (fun x y => (ST_STprof_pos sz n _ _ _ _ _).le) (by linarith) hρ1 a).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ρ)
    have := hΦ DE w w hsw.le le_rfl le_rfl a
    rw [div_self h1w.ne'] at this
    simpa using this
  have hΦo : duhamelI_Phi Tk (2 * (1 - u 0)) (fun _ _ => 1) a ≤ ρ ^ 2 * 9 := by
    rw [hh0]
    refine (duhamelI_Phi_scale hTk0 (fun _ _ => zero_le_one) (by linarith) hρ1 a).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ρ)
    have hrow' : ∀ x : Zd d (sz.L n), ∑ y, Tk x y ≤ (1 - w)⁻¹ := fun x => hrow w hw0.le hw1 x
    refine (duhamelI_Phi_one hTk0 (by linarith) hrow' a).trans (le_of_eq ?_)
    field_simp
    ring
  have hc1 : 0 ≤ Λ * (Λ * ρ * (2 / c₀ + 1) * a₄) := by positivity
  have hc2 : 0 ≤ Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm)) := by positivity
  refine hMr_le.trans ?_
  refine mul_le_mul_of_nonneg_left (hΦ1.trans ?_) (by norm_num)
  calc _ ≤ (Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * (ρ ^ 2 * (C * (Wd * (T + WmE)))) +
        (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * (ρ ^ 2 * 9) :=
        add_le_add (mul_le_mul_of_nonneg_left hΦp hc1) (mul_le_mul_of_nonneg_left hΦo hc2)
    _ = _ := by ring

end DriftG

section PathG

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
-- the remainder combines the drift, martingale and floor estimates: 200000 is not enough
/-- **The pathwise remainder at one size index** (`duhamelI_path` without the initial term): on a sample `ω` of the grid walk of
`[s, tt]` at which the decomposition of `STGridMartAt`, the three error terms at every grid time and the martingale tail hold,
`‖(𝓛-𝒦)^{(2)}_{tt,σ,a} - [𝒰_{s,tt} (𝓛-𝒦)_s]_a‖ ≤ κ Λ² ρ³ A^{-1/4} W^{-d}𝒯̃^L_{tt,D}(|a₁-a₂|) + W^{-D}`,
`ρ = (1-s)/(1-tt)`, `κ = 4C/c₀ + 8C(2/c₀+1)`.  The hypotheses are uniform in the label `(σ, a)`, so the bound holds at every label
of the same sample (`duhamelII_section` applies it at `(σ, (c, a₂))` for every `c`). -/
theorem duhamelIG_path_rem {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (s tt : ℕ → ℝ) (K : ℕ → ℕ) (ω : PathΩ sz)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) {Λ D DE Dm M R C c₀ : ℝ} (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n))
    (hs0 : 0 ≤ s n) (hstt : s n < tt n) (htt1 : tt n < 1) (hK : K n ≠ 0)
    (hlam : 0 < sz.lam n) (hΛ : 1 ≤ Λ) (hA : 1 ≤ STAI sz n) (hc₀ : 0 < c₀) (hc : c₀ ≤ (Cm.m n).im)
    (hC : 0 ≤ C) (hker : GridRepTailGen_Ker Cm.toFlowFM n)
    (hpair : ∀ w : ℝ, 0 < w → w < 1 → Step2Gen_thetaKer Cm.toFlowFM n (σ 1) (σ 0) w = Step2Gen_thetaKer Cm.toFlowFM n (σ 0) (σ 1) w)
    (hη : ∀ v : ℝ, Cm.eta n v = (1 - v) * (Cm.m n).im)
    (hΦ : ∀ (D' v w : ℝ), s n ≤ v → v ≤ w → w ≤ tt n → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Cm.toFlowFM n (σ 0) (σ 1) w x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D'))))
    (hDE : (1 - s n) / (1 - tt n) * ((sz.W n : ℕ) : ℝ) ^ (-DE) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hid : ∀ i : STLab sz n, ∀ k, k ≤ K n → STgAg Cm s tt K n i.1 i.2 k ω =
      STgAg Cm s tt K n i.1 i.2 0 ω + ((gridStep s tt K n : ℝ) : ℂ) *
        ∑ j ∈ Finset.range k, STgDriftg Cm s tt K n i.1 i.2 j ω + Rem i k ω + Mart i k ω)
    (hRem : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ R)
    (hM : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖STgAg Cm s tt K n i.1 i.2 k ω‖ ≤ M)
    (hMart : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Mart i k ω‖ ≤ Λ * Real.sqrt (∑ j ∈ Finset.range k,
      gridStep s tt K n * ‖STEEMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) i.1 i.2‖ +
        ((sz.size n : ℕ) : ℝ) ^ (-Dm)))
    (hELK : ∀ j, j ≤ K n → ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STELKLKMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) σ b‖ ≤
        Λ * ((STAI sz n) ^ (-(1 / 3) : ℝ) * (Cm.eta n (gridTime s tt K n j))⁻¹ *
          STprof sz n (gridTime s tt K n j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)))
    (hEGt : ∀ j, j ≤ K n → ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STEGtMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) σ b‖ ≤
        Λ * ((STAI sz n) ^ (-(1 / 2) : ℝ) * (Cm.eta n (gridTime s tt K n j))⁻¹ *
          STprof sz n (gridTime s tt K n j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)))
    (hEEk : ∀ j, j ≤ K n → ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (k : Fin 2),
      ‖STEEkMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) k σ b‖ ≤
        Λ * ((STAI sz n) ^ (-(1 / 2) : ℝ) * (Cm.eta n (gridTime s tt K n j))⁻¹ *
          STprof sz n (gridTime s tt K n j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) ^ 2))
    (hfloor : 36 * ((1 - s n) / (1 - tt n)) ^ 2 * (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) +
        64 * ((1 - tt n)⁻¹) ^ 7 * (R + gridStep s tt K n * M) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) :
    ‖STgAg Cm s tt K n σ a (K n) ω - Step2Gen_UN Cm.toFlowFM n σ (s n) (tt n)
        (fun b => STgAg Cm s tt K n σ b 0 ω) a‖ ≤
      (4 * C / c₀ + 8 * C * (2 / c₀ + 1)) * (Λ ^ 2 * (((1 - s n) / (1 - tt n)) ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
          STprof sz n (tt n) D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  obtain ⟨hΔ, hu1, hu0, huK, hKΔ, hmem, hmono⟩ := duhamelI_grid s tt K n hstt.le hK
  have hw0 : 0 < tt n := lt_of_le_of_lt hs0 hstt
  have h1w : 0 < 1 - tt n := by linarith
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hK
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set ρ : ℝ := (1 - s n) / (1 - tt n) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1w]; linarith
  set A := STAI sz n with hAdef
  obtain ⟨ha₄0, ha₄1, ha₂, ha₃⟩ := duhamelI_rpow_quarter hA
  set a₄ := A ^ (-(1 / 4) : ℝ) with ha₄def
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 < Wd := by positivity
  set T : ℝ := tailT d (sz.L n) (sz.lam n) (tt n) ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hT
  set P : ℝ := STprof sz n (tt n) D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) with hP
  set WmE : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-DE) with hWmE
  set WmD : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-D) with hWmD
  have hT0 : 0 ≤ T := tailT_nonneg (Nat.cast_nonneg _)
  have hWmE0 : 0 ≤ WmE := Real.rpow_nonneg hW.le _
  have hWmD0 : 0 ≤ WmD := Real.rpow_nonneg hW.le _
  have hZP : Wd * (T + ρ * WmE) ≤ 2 * P := by
    have hP' : P = Wd * max T WmD := by
      rw [hP]; unfold STprof; rw [duhamelI_tailW_eq]
    rw [hP']
    calc Wd * (T + ρ * WmE) ≤ Wd * (T + WmD) := mul_le_mul_of_nonneg_left (by linarith [hDE]) hWd0.le
      _ ≤ Wd * (2 * max T WmD) :=
          mul_le_mul_of_nonneg_left (by linarith [le_max_left T WmD, le_max_right T WmD]) hWd0.le
      _ = 2 * (Wd * max T WmD) := by ring
  have hZP' : Wd * (T + WmE) ≤ 2 * P := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hWd0.le) hZP
  -- the grid
  set u : ℕ → ℝ := gridTime s tt K n with hu
  set Δ : ℝ := gridStep s tt K n with hΔdef
  have hu_s : ∀ j ≤ K n, s n ≤ u j := fun j hj => (hmem j hj).1
  have hu_w : ∀ j ≤ K n, u j ≤ tt n := fun j hj => (hmem j hj).2
  have hmono' : ∀ j < K n, u j ≤ u (j + 1) := hmono
  -- the Duhamel formula on the grid
  have hdu := duhamelIG_duhamel hker Δ M R σ (K n) u
    (fun j b => STgAg Cm s tt K n σ b j ω)
    (fun j b => STELKLKMg Cm n (u j) (Cm.Hpath s tt K n j ω) σ b +
      STEGtMg Cm n (u j) (Cm.Hpath s tt K n j ω) σ b)
    (fun j b => Rem (σ, b) j ω) (fun j b => Mart (σ, b) j ω) hΔ (by rw [hu0]; exact hs0) hu1
    (by rw [huK]; exact htt1) (fun j hj b => hM (σ, b) j hj) (fun j hj b => hRem (σ, b) j hj)
    (fun j hj b => by
      have h := hid (σ, b) j hj
      have e : ∀ i, STgDriftg Cm s tt K n σ b i ω =
          Step2Gen_ThetaN Cm.toFlowFM n σ (u i)
            (fun b' => STgAg Cm s tt K n σ b' i ω) b +
          (STELKLKMg Cm n (u i) (Cm.Hpath s tt K n i ω) σ b +
            STEGtMg Cm n (u i) (Cm.Hpath s tt K n i ω) σ b) := by
        intro i
        unfold STgDriftg
        rw [add_assoc]
        rfl
      simp only [e] at h
      exact h) a
  rw [hu0, huK] at hdu
  set Fj : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ := fun j b =>
    STELKLKMg Cm n (u j) (Cm.Hpath s tt K n j ω) σ b +
      STEGtMg Cm n (u j) (Cm.Hpath s tt K n j ω) σ b with hFj
  set Iv : ℂ := Step2Gen_UN Cm.toFlowFM n σ (s n) (tt n)
    (fun b => STgAg Cm s tt K n σ b 0 ω) a with hIv
  set Dr : ℂ := ∑ j ∈ Finset.range (K n), (Δ : ℂ) *
    Step2Gen_UN Cm.toFlowFM n σ (u j) (tt n) (Fj j) a with hDr
  set Mr : ℂ := ∑ j ∈ Finset.range (K n), Step2Gen_UN Cm.toFlowFM n σ (u j) (tt n)
    (fun b => Mart (σ, b) (j + 1) ω - Mart (σ, b) j ω) a with hMr
  have hsplit : ‖STgAg Cm s tt K n σ a (K n) ω - Iv‖ ≤
      ‖Dr‖ + ‖Mr‖ + 64 * ((1 - tt n)⁻¹) ^ 7 * (R + Δ * M) := by
    set X := STgAg Cm s tt K n σ a (K n) ω with hX
    have e : X - Iv = (X - Iv - Dr - Mr) + Dr + Mr := by ring
    have h1 := norm_add_le (X - Iv - Dr - Mr + Dr) Mr
    have h2 := norm_add_le (X - Iv - Dr - Mr) Dr
    have hdu' : ‖X - Iv - Dr - Mr‖ ≤ 64 * ((1 - tt n)⁻¹) ^ 7 * (R + Δ * M) := hdu
    rw [e]
    linarith
  -- the drift
  have hF : ∀ j ≤ K n, ∀ b : Fin 2 → Zd d (sz.L n), ‖Fj j b‖ ≤
      (Λ * (2 * a₄) * (Cm.eta n (u j))⁻¹) * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) := by
    intro j hj b
    have hu_lt : u j < 1 := (hu_w j hj).trans_lt htt1
    have hη0 : 0 ≤ (Cm.eta n (u j))⁻¹ := inv_nonneg.2 (by
      rw [hη]; exact (mul_pos (by linarith) (lt_of_lt_of_le hc₀ hc)).le)
    have hp0 := (ST_STprof_pos sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)).le
    have h1 := hELK j hj σ b
    have h2 := hEGt j hj σ b
    have h3 : A ^ (-(1 / 2) : ℝ) ≤ a₄ := by rw [ha₂]; nlinarith
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Λ * (A ^ (-(1 / 3) : ℝ) * (Cm.eta n (u j))⁻¹ *
          STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) +
        Λ * (A ^ (-(1 / 2) : ℝ) * (Cm.eta n (u j))⁻¹ *
          STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) := add_le_add h1 h2
      _ ≤ Λ * (a₄ * (Cm.eta n (u j))⁻¹ * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) +
        Λ * (a₄ * (Cm.eta n (u j))⁻¹ * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) := by
          gcongr
      _ = _ := by ring
  have hDr_le := duhamelIG_drift Cm.toFlowFM n (s := s n) (w := tt n) (Λ := Λ) (DE := DE) (C := C) (c₀ := c₀)
    (e₀ := 2 * a₄) (Δ := Δ) (K := K n) u Fj σ a hker.1 hpair hη hs0 hstt htt1 (by linarith) hC (by linarith) hc₀ hc hΔ hKΔ
    hu_s hu_w hΦ hF
  have hMart' : ∀ (b : Fin 2 → Zd d (sz.L n)) (j : ℕ), j ≤ K n →
      ‖Mart (σ, b) j ω‖ ≤ Λ * Real.sqrt (∑ i ∈ Finset.range j, Δ * ‖STEEMg Cm n (u i)
        (Cm.Hpath s tt K n i ω) σ b‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) := fun b j hj => hMart (σ, b) j hj
  have hMr_le := duhamelIG_mart Cm.toFlowFM n (s := s n) (w := tt n) (Λ := Λ) (DE := DE) (Dm := Dm) (C := C)
    (c₀ := c₀) (Δ := Δ) (K := K n) u (fun j b => Mart (σ, b) j ω)
    (fun j b => ‖STEEMg Cm n (u j) (Cm.Hpath s tt K n j ω) σ b‖) σ a hker.1 hpair hη (fun w' hw0 hw1 x => duhamelIG_theta_rows hker (σ 0) (σ 1) hw0 hw1 x) hK1 hs0 hstt htt1 hlam hΛ hA hc₀ hc
    hΔ hKΔ hu0 hu_s hu_w hmono' hΦ (fun j b => norm_nonneg _)
    (fun j hj b => by
      have h3 : STEEMg Cm n (u j) (Cm.Hpath s tt K n j ω) σ b =
          STEEkMg Cm n (u j) (Cm.Hpath s tt K n j ω) 0 σ b +
            STEEkMg Cm n (u j) (Cm.Hpath s tt K n j ω) 1 σ b := rfl
      rw [h3]
      have := add_le_add (hEEk j hj σ b 0) (hEEk j hj σ b 1)
      refine (norm_add_le _ _).trans (this.trans (le_of_eq ?_))
      ring) hMart'
  have hP0 : 0 ≤ P := (ST_STprof_pos sz n _ _ _ _ _).le
  clear hELK hEGt hEEk hMart hMart' hid hRem hM hF hdu
  have hDr2 : ‖Dr‖ ≤ (4 * C / c₀) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P := by
    refine hDr_le.trans ?_
    have h1 : Λ * (2 * a₄) * (ρ / c₀) * (C * ρ * (Wd * (T + ρ * WmE))) ≤
        Λ * (2 * a₄) * (ρ / c₀) * (C * ρ * (2 * P)) := by gcongr
    refine h1.trans ?_
    have e : Λ * (2 * a₄) * (ρ / c₀) * (C * ρ * (2 * P)) = (4 * C / c₀) * (Λ * ρ ^ 2 * a₄) * P := by ring
    rw [e]
    have h2 : Λ * ρ ^ 2 * a₄ ≤ Λ ^ 2 * (ρ ^ 3 * a₄) := by
      have : Λ * ρ ^ 2 ≤ Λ ^ 2 * ρ ^ 3 := mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
      nlinarith
    gcongr
  have hMr2 : ‖Mr‖ ≤ (8 * C * (2 / c₀ + 1)) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P +
      36 * ρ ^ 2 * (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) := by
    refine hMr_le.trans ?_
    have h1 : 4 * ((Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * (ρ ^ 2 * (C * (Wd * (T + WmE)))) +
        (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * (9 * ρ ^ 2)) ≤
        4 * ((Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * (ρ ^ 2 * (C * (2 * P))) +
        (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * (9 * ρ ^ 2)) := by gcongr
    refine h1.trans (le_of_eq ?_)
    ring
  have e : (4 * C / c₀ + 8 * C * (2 / c₀ + 1)) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P =
      (4 * C / c₀) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P + (8 * C * (2 / c₀ + 1)) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P := by ring
  rw [e]
  linarith

end PathG

/-! ## 4. The per-section statement -/

section SectionG

variable {d : ℕ}

/-- `PrecL` is invariant under pointwise equality of the two families. -/
private theorem duhamelIG_prec_congr {sz : Sizes d} {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω, ξ n u ω = ξ' n u ω) (hζ : ∀ n u ω, ζ n u ω = ζ' n u ω) (h : PrecL sz μ ξ ζ) : PrecL sz μ ξ' ζ' := by
  have e1 : ξ = ξ' := funext fun n => funext fun u => funext fun ω => hξ n u ω
  have e2 : ζ = ζ' := funext fun n => funext fun u => funext fun ω => hζ n u ω
  subst e1; subst e2; exact h

/-- measurability of `STELKLKMg` in the matrix (F9, clause 3). -/
private theorem duhamelIG_ELKLK_meas {sz : Sizes d} {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ)
    (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STELKLKMg Cm n u H σ a := by
  unfold STELKLKMg
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
  exact ((Step2EventsGen_STLKMg_measurable hG n u _ _).mul measurable_const).mul (Step2EventsGen_STLKMg_measurable hG n u _ _)

/-- measurability of `‖𝒰_{v,w} ∘ (𝓛-𝒦)_u‖` in the matrix (F9, clause 3). -/
private theorem duhamelIG_Ugen_meas {sz : Sizes d} {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ)
    (u v w : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖Step2Gen_UN Cm.toFlowFM n σ v w (fun b => STLKMg Cm n u H σ b) a‖ := by
  unfold Step2Gen_UN
  exact (Finset.measurable_sum _ fun b _ => measurable_const.mul (Step2EventsGen_STLKMg_measurable hG n u σ b)).norm

/-- `STELKLKMg` at the model matrix is `STELKLKg` (F9, clause 2). -/
private theorem duhamelIG_ELKLK_eq {sz : Sizes d} (Cm : Step2Mat sz)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hLM : ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω)
    (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STELKLKMg Cm n u (Hm n u ω) σ a = STELKLKg Cm.toFlowFM n u σ a ω := by
  unfold STELKLKMg STELKLKg
  simp only [Step2EventsGen_STLKMg_eq Cm hLM]

/-- The grid events at the sections of `[s, tt]` from a per-section `≺` on `[s, t]` (band `duhamelI_whp_sec`, through F9). -/
private theorem duhamelIG_whp_sec {sz : Sizes d} {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ}
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hlaw : Step2EventsGen_Law Cm μ Hm) {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)] {s t : ℕ → ℝ}
    (tt : ∀ n, TimeIcc s t n) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hKne : ∀ n, K n ≠ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop, (((K n + 1) * Fintype.card (V n) : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F Z : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u)) (hZ : ∀ n v u, Measurable (Z n v u)) {τ : ℝ} (hτ : 0 < τ)
    (h : PrecL sz μ (U := fun n => TimeIcc s t n × V n) (fun n p ω => F n p.2 (p.1 : ℝ) (Hm n (p.1 : ℝ) ω))
      (fun n p ω => Z n p.2 (p.1 : ℝ) (Hm n (p.1 : ℝ) ω))) :
    HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ∈ Finset.range (K n + 1), ∀ v : V n,
      F n v (gridTime s (fun m => (tt m : ℝ)) K n j) (Cm.Hpath s (fun m => (tt m : ℝ)) K n j ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n v (gridTime s (fun m => (tt m : ℝ)) K n j)
          (Cm.Hpath s (fun m => (tt m : ℝ)) K n j ω)}) := by
  refine Step2EventsGen_grid_whp_of_sections Cm μ hlaw s (fun m => (tt m : ℝ)) K hs (fun n => (tt n).2.1) hKne hC0 hcard F Z hF hZ τ hτ
    fun tt' => ?_
  exact StochDomAt.precomp_param h (fun n v => (⟨(tt' n : ℝ), (tt' n).2.1, (tt' n).2.2.trans (tt n).2.2⟩, v))

end SectionG

section SectionMain

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
-- the six grid events and the pathwise case analysis elaborate a long `have` list: 200000 is not enough
/-- **The per-section statement over a carrier** (band `duhamelI_section`): at a section `tt n ∈ [s_n, t_n]` the family `‖(𝓛-𝒦)^{(2)}_{tt,σ,a}‖` is dominated by
`F + A^{-1/5} W^{-d}𝒯̃^L_{tt,D} + W^{-D}` at the law `law sz`, given the initial term `≺ F`, `STEtermsMidConclgL` and `(con_st_ind)`.
The grid has `K_n = N^m` steps; the six events (initial term, three error terms, martingale tails, identities) are at the grid times, the
section being the last grid time of `[s, tt]` (the law identity `(5.1)` of F9, `hGrid`).  The inputs besides the carrier are the decay `hΦC` of
`Φ` of a profile at the kernel (`duhamelIG_Phi_STprof`), the decomposition and the martingale tail `hGMA` (`STGridMartAtgL`), the Hermitian grid
walk `hHerm`, the kernel facts `hker`, `hpair`, the size `‖𝒦^{(2)}‖ ≤ N` `hKn` and the loop form `hL` (a priori bound). -/
private theorem duhamelIG_section (hd : 3 ≤ d) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hGMA : STGridMartAtgL d C₀ Flow mkM T0)
    {κ ε 𝔡 𝔠 c₀ : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) {z : ℕ → ℂ} (hflow : Flow sz κ ε 𝔠 𝔡 z)
    (hAd : sz.Admissible 𝔠 𝔡) (hc₀ : 0 < c₀) (hIm : ∀ n, c₀ ≤ ((mkM sz z).m n).im)
    (hη : ∀ n u, (mkM sz z).eta n u = (1 - u) * ((mkM sz z).m n).im)
    {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm (mkM sz z) E) (hGrid : Step2EventsGen_Grid (mkM sz z) (law sz))
    (hHerm : ∀ s t K n k ω, ((mkM sz z).Hpath s t K n k ω).IsHermitian)
    (hker : ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hpair : ∀ (n : ℕ) (σ : Fin 2 → Bool) (w : ℝ), 0 < w → w < 1 →
      Step2Gen_thetaKer (mkM sz z).toFlowFM n (σ 1) (σ 0) w = Step2Gen_thetaKer (mkM sz z).toFlowFM n (σ 0) (σ 1) w)
    {C : ℝ} (hC : 0 < C)
    (hΦC : ∀ (n : ℕ) (σ σ' : Bool) (D v w : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → 0 ≤ v → v ≤ w → w < 1 →
      (∀ x, ∑ y, ‖Step2Gen_thetaKer (mkM sz z).toFlowFM n σ σ' w x y‖ ≤ (1 - w)⁻¹) →
      (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - w ∨ 1 - v ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
      ∀ a : Fin 2 → Zd d (sz.L n),
        duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer (mkM sz z).toFlowFM n σ σ' w x y‖) (2 * (1 - v))
            (fun x y => STprof sz n v D ((sz.L n : ℕ) : ℝ) x y) a ≤
          C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
              (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D))))
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htz : ∀ n, t n ≤ T0 sz z n) (ht1 : ∀ n, t n < 1)
    (hKn : ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ t n → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖(mkM sz z).K n v σ a‖ ≤ ((sz.size n : ℕ) : ℝ))
    (hReg : STReg5Mid sz s t)
    (hTTT : ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∨ 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hCon : STConStInd sz (1 / 100) s t) (hE : STEtermsMidConclgL (mkM sz z).toFlowFM (law sz) s t)
    {D : ℝ} (hD : 0 < D) (P : (Fin 2 → Bool) → Prop) (F : ∀ n, STIdx2P sz P s t n → ℝ)
    (hF0 : ∀ n p, 0 ≤ F n p)
    (hini : PrecL sz (law sz) (U := STIdx2P sz P s t) (fun n p ω => ‖Step2Gen_UN (mkM sz z).toFlowFM n p.2.1.1 (s n) (p.1 : ℝ)
      (fun b => (mkM sz z).L n (s n) p.2.1.1 b ω - (mkM sz z).K n (s n) p.2.1.1 b) p.2.2‖) (fun n p _ => F n p))
    (tt : ∀ n, TimeIcc s t n) :
    PrecL sz (law sz) (U := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖(mkM sz z).L n (tt n : ℝ) v.1.1 v.2 ω - (mkM sz z).K n (tt n : ℝ) v.1.1 v.2‖)
      (fun n v _ => F n (tt n, v) + STAI sz n ^ (-(1 / 5) : ℝ) *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  classical
  set Cm : Step2Mat sz := mkM sz z with hCm
  by_cases hP : ∃ σ, P σ
  swap
  · exact Step2EventsGen_prec_of_le_ev (law sz) (fun n v ω => by
      exact absurd ⟨v.1.1, v.1.2⟩ hP) (Eventually.of_forall fun n v ω => absurd ⟨v.1.1, v.1.2⟩ hP)
  have : ∀ n, Nonempty ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) :=
    fun n => ⟨(⟨hP.choose, hP.choose_spec⟩, fun _ => 0)⟩
  have hsN := tendsto_size sz hAd.2.2.1
  obtain ⟨Hm', hGMM', hLM', hMeasLM, hMeasGMM, hlaw⟩ := hGrid
  have hGrid' : Step2EventsGen_Grid Cm (law sz) := ⟨Hm', hGMM', hLM', hMeasLM, hMeasGMM, hlaw⟩
  intro τ hτ D' hD'
  set κs : ℝ := 4 * C / c₀ + 8 * C * (2 / c₀ + 1) with hκs
  set DE : ℝ := D + d + 2 with hDE
  set Dm : ℝ := 2 * (D + D' + 6 + τ) with hDm
  obtain ⟨CK, hCK0, hK⟩ := hGMA κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s (fun n => (tt n : ℝ)) hs (fun n => (tt n).2.1)
    (fun n => (tt n).2.2.trans (htz n)) Dm (by positivity)
  set x₀ : ℝ := max CK (2 * (C₀ + D + 12)) with hx₀
  set m : ℕ := ⌈x₀⌉₊ with hm
  set K : ℕ → ℕ := fun n => (sz.size n) ^ m with hKdef
  have hKne : ∀ n, K n ≠ 0 := fun n => pow_ne_zero _ (by have := sz.one_le_size n; omega)
  have hKbig : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    have h1 : CK ≤ (m : ℝ) := (le_max_left _ _).trans (Nat.le_ceil x₀)
    calc ((sz.size n : ℕ) : ℝ) ^ CK ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 h1
      _ = K n := by rw [Real.rpow_natCast]; simp [hKdef]
  obtain ⟨Mart, Rem, hid, hrem, hmart⟩ := hK K hKne hKbig
  set τ₁ : ℝ := τ / 4 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨hE1, hE2, hE3⟩ := hE DE (by positivity)
  -- card bounds
  have hcardV : ∀ᶠ n in atTop, (Fintype.card ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    exact duhamelI_card_le sz P n hn
  have hcardK : ∀ (c : ℕ → ℕ), (∀ᶠ n in atTop, (c n : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ)) →
      ∀ᶠ n in atTop, (((K n + 1) * c n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (((m + 5 : ℕ) : ℝ)) := fun c hc => by
    filter_upwards [hc, hsN.eventually (eventually_ge_atTop 4)] with n h1 h2
    exact duhamelI_cardK (sz.size n) m (c n) h2 h1
  -- E1: the initial term at the grid index `0`
  have hΞ1 := Step2EventsGen_grid_whp_zero Cm (law sz) hlaw (V := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) s
    (fun n => (tt n : ℝ)) K hs (fun n => (tt n).2.1) hKne (C := 3) (by norm_num) hcardV
    (fun n v u H => ‖Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ) (fun b => STLKMg Cm n u H v.1.1 b) v.2‖)
    (fun n v u H => F n (tt n, v))
    (fun n v u => duhamelIG_Ugen_meas hGrid' n u _ _ _ v.2) (fun n v u => measurable_const) τ₁ hτ₁0
    (duhamelIG_prec_congr (fun n v ω => by
        simp only [Step2EventsGen_STLKMg_eq Cm hLM']) (fun n v ω => rfl)
      (StochDomAt.precomp_param hini (fun n v => (tt n, v))))
  -- E2, E3, E4: the three error terms at every grid index
  have hcardL : ∀ᶠ n in atTop, (Fintype.card (sz.STLab n) : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    have := ST_card_lab_le sz n hn
    have h0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hcardL2 : ∀ᶠ n in atTop, (Fintype.card (sz.STLab n × Fin 2) : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    have := ST_card_lab_le sz n hn
    rw [Fintype.card_prod, Fintype.card_fin]; push_cast
    linarith
  have hΞ2 := duhamelIG_whp_sec (V := fun n => sz.STLab n) hlaw tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL)
    (fun n v u H => ‖STELKLKMg Cm n u H v.1 v.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 3) : ℝ) * (Cm.eta n u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1))
    (fun n v u => (duhamelIG_ELKLK_meas hGrid' n u v.1 v.2).norm) (fun n v u => measurable_const) hτ₁0
    (duhamelIG_prec_congr (fun n p ω => by
        simp only [duhamelIG_ELKLK_eq Cm hLM']) (fun n p ω => rfl) hE1)
  have hΞ3 := duhamelIG_whp_sec (V := fun n => sz.STLab n) hlaw tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL)
    (fun n v u H => ‖STEGtMg Cm n u H v.1 v.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1))
    (fun n v u => (Step2EventsGen_STEGtMg_measurable hGrid' n u v.1 v.2).norm) (fun n v u => measurable_const) hτ₁0
    (duhamelIG_prec_congr (fun n p ω => by
        simp only [Step2EventsGen_STEGtMg_eq Cm hLM']) (fun n p ω => rfl) hE2)
  have hΞ4 := duhamelIG_whp_sec (V := fun n => sz.STLab n × Fin 2) hlaw tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL2)
    (fun n v u H => ‖STEEkMg Cm n u H v.2 v.1.1 v.1.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.1.2 0) (v.1.2 1) ^ 2)
    (fun n v u => (Step2EventsGen_STEEkMg_measurable hGrid' n u v.2 v.1.1 v.1.2).norm) (fun n v u => measurable_const) hτ₁0
    (duhamelIG_prec_congr (fun n p ω => by
        simp only [Step2EventsGen_STEEkMg_eq Cm hLM']) (fun n p ω => rfl)
      (StochDomAt.precomp_param hE3 (fun n (p : TimeIcc s t n × (sz.STLab n × Fin 2)) =>
        (((p.1, p.2.1), p.2.2) : STIdx2 sz s t n × Fin 2))))
  have hΞ := hΞ1.inter hsN (hΞ2.inter hsN (hΞ3.inter hsN hΞ4))
  -- E5: the martingale tails of all labels
  have hmartE : ∀ᶠ n in atTop, Cm.Pp (⋃ i : sz.STLab n, {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ τ₁ * (∑ j ∈ Finset.range k, gridStep s (fun m => (tt m : ℝ)) K n *
        ‖STEEMg Cm n (gridTime s (fun m => (tt m : ℝ)) K n j)
          (Cm.Hpath s (fun m => (tt m : ℝ)) K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) <
        ‖Mart n i k ω‖}) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) := by
    filter_upwards [hmart τ₁ hτ₁0, hsN.eventually (eventually_ge_atTop 4)] with n hn h4
    exact ST_union_prob Cm.Pp _ (by exact_mod_cast (by omega : 1 ≤ sz.size n)) (ST_card_lab_le sz n h4)
      (by rw [hDm]; nlinarith) hn
  -- E6: the almost sure identities
  have hae : ∀ᶠ n in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ i : sz.STLab n,
      (∀ k, k ≤ K n → STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 k ω =
        STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 0 ω +
          ((gridStep s (fun m => (tt m : ℝ)) K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDriftg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 j ω + Rem n i k ω + Mart n i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n)) := by
    filter_upwards [hrem] with n hn
    exact ae_all_iff.2 fun i => (hid n i).and (hn i)
  -- numerical facts
  have hWO := hAd.2.2.2.2
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hWbig : ∀ᶠ n in atTop, 2 * 𝔡⁻¹ ^ 2 ≤ ((sz.W n : ℕ) : ℝ) := by
    filter_upwards [hAd.2.2.2.1, hsN.eventually (eventually_le_rpow (2 * 𝔡⁻¹ ^ 2) hAd.1)] with n h1 h2
    exact h2.trans h1
  have hNc : ∀ᶠ n in atTop, c₀⁻¹ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := hAd.2.2.1.eventually (eventually_ge_atTop _)
  have hNτ : ∀ᶠ n in atTop, 2 * κs + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    hsN.eventually (eventually_le_rpow _ (half_pos hτ))
  have hiniE := StochDomAt.precomp_param hini (fun n v => (tt n, v))
  filter_upwards [hiniE τ hτ D' hD', hev, hWO, hWbig, hNc, hNτ, hCon, hmartE, hae, hΞ (D' + 1) (by linarith),
    hsN.eventually (eventually_ge_atTop 256), hKn] with n hini1 hAn hWOn hWb hNcn hNτn hCon1 hmartn haen hΞn h256 hKnn
  obtain ⟨hlam, hA1⟩ := hAn
  have hlamle : sz.lam n ≤ 𝔡⁻¹ := hWOn.2
  have htt1 : (tt n : ℝ) < 1 := (tt n).2.2.trans_lt (ht1 n)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN256 : (256 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast h256
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hΛ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1 hτ₁0.le
  by_cases hsn : s n < (tt n : ℝ)
  swap
  · -- the section is the initial time: `𝒰_{s,s} = 1`
    have hts : (tt n : ℝ) = s n := le_antisymm (not_lt.1 hsn) (tt n).2.1
    refine le_trans (measure_mono ?_) hini1
    rintro ω ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have hs1 : s n < 1 := (hst n).trans (ht1 n)
    have hU := Step2Gen_UN_self Cm.toFlowFM n (hker n).1 v.1.1 (hs n) hs1
      (fun b => Cm.L n (s n) v.1.1 b ω - Cm.K n (s n) v.1.1 b)
    have hF1 : 0 ≤ STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) := add_nonneg (mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) _)
          (ST_STprof_pos sz n _ _ _ _ _).le) (Real.rpow_nonneg hW0.le _)
    simp only [hts] at hv hF1 ⊢
    change _ < ‖Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (s n) (fun b => Cm.L n (s n) v.1.1 b ω - Cm.K n (s n) v.1.1 b) v.2‖
    rw [hU]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)) hv
    linarith [hF0 n (tt n, v)]
  -- the main case: `s n < tt n`
  have hs1 : s n < 1 := (hst n).trans (ht1 n)
  have h1tt : 0 < 1 - (tt n : ℝ) := by linarith
  have htN : (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := duhamelI_htN sz n hlam hA1 (hReg n).1
  have hTi : (1 - (tt n : ℝ))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) :=
    (inv_anti₀ (by linarith [ht1 n]) (by linarith [(tt n).2.2])).trans htN
  have hρA := duhamelI_rho sz n hlam (tt n).2.1 (tt n).2.2 (ht1 n) (by linarith [(hReg n).2, (hst n)]) hCon1.1
  set ρ : ℝ := (1 - s n) / (1 - (tt n : ℝ)) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1tt]; linarith
  have hρN : ρ ≤ ((sz.size n : ℕ) : ℝ) :=
    ((div_le_div_of_nonneg_right (by linarith [hs n]) h1tt.le).trans_eq (one_div _)).trans hTi
  have hx₀m : x₀ ≤ (m : ℝ) := Nat.le_ceil x₀
  have hKx : ((sz.size n : ℕ) : ℝ) ^ x₀ ≤ K n := by
    calc ((sz.size n : ℕ) : ℝ) ^ x₀ ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hx₀m
      _ = K n := by rw [Real.rpow_natCast]; simp [hKdef]
  have hΔ : gridStep s (fun m => (tt m : ℝ)) K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-x₀) := by
    have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero (hKne n)
    have hNx : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ x₀ := Real.rpow_pos_of_pos (by linarith) _
    unfold gridStep
    calc ((tt n : ℝ) - s n) / K n ≤ 1 / K n := div_le_div_of_nonneg_right (by linarith [(tt n).2.2, ht1 n, hs n]) hKpos.le
      _ ≤ 1 / ((sz.size n : ℕ) : ℝ) ^ x₀ := one_div_le_one_div_of_le hNx hKx
      _ = _ := by rw [Real.rpow_neg (by linarith), one_div]
  have hWN := duhamelI_W_le_size sz (by omega : d ≠ 0) n
  have hWm : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_nonpos hW0 hWN (neg_nonpos.2 hD.le)
  have hfloor := duhamelI_floor (Δ := gridStep s (fun m => (tt m : ℝ)) K n) (Wm := ((sz.W n : ℕ) : ℝ) ^ (-D))
    (C₀ := C₀) (c₀ := c₀) (D := D) (τ := τ) (Dm := Dm) (x := x₀) (ρ := ρ) (Ti := (1 - (tt n : ℝ))⁻¹) hN256 hNcn hτ hD hC₀
    (by linarith) hρN (inv_nonneg.2 h1tt.le) hTi (div_nonneg (by linarith [(tt n).2.1]) (by exact_mod_cast Nat.zero_le _)) hΔ hWm
    (by rw [hDm]; linarith) (le_max_right _ _)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hDEn : ρ * ((sz.W n : ℕ) : ℝ) ^ (-DE) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have h2A : (1 : ℝ) ≤ 2 * STAI sz n := by linarith
    have hρ2 : ρ ≤ 2 * STAI sz n := hρA.trans (by
      calc (2 * STAI sz n) ^ (1 / 100 : ℝ) ≤ (2 * STAI sz n) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h2A (by norm_num)
        _ = 2 * STAI sz n := Real.rpow_one _)
    have hA2 : 2 * STAI sz n ≤ ((sz.W n : ℕ) : ℝ) ^ (d + 1) := by
      unfold STAI
      calc 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ≤ 2 * (𝔡⁻¹ ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by
            gcongr
        _ = (2 * 𝔡⁻¹ ^ 2) * ((sz.W n : ℕ) : ℝ) ^ d := by ring
        _ ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_right hWb (by positivity)
        _ = _ := by ring
    calc ρ * ((sz.W n : ℕ) : ℝ) ^ (-DE) ≤ ((sz.W n : ℕ) : ℝ) ^ (d + 1) * ((sz.W n : ℕ) : ℝ) ^ (-DE) :=
          mul_le_mul_of_nonneg_right (hρ2.trans hA2) (Real.rpow_nonneg hW0.le _)
      _ = ((sz.W n : ℕ) : ℝ) ^ (-D - 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hW0]; congr 1; push_cast; rw [hDE]; ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hNτ' : (2 * κs + 1) * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    have e1 : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; rw [hτ₁]; push_cast; ring
    have e2 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    rw [e1, ← e2]
    exact mul_le_mul_of_nonneg_right hNτn (Real.rpow_nonneg (by linarith) _)
  have hΦn : ∀ (σ : Fin 2 → Bool) (D'' v w : ℝ), s n ≤ v → v ≤ w → w ≤ (tt n : ℝ) → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Cm.toFlowFM n (σ 0) (σ 1) w x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D'' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
    intro σ D'' v w hv hvw hw a
    have hw1 : w < 1 := hw.trans_lt htt1
    refine hΦC n (σ 0) (σ 1) D'' v w hlam hlamle ((hs n).trans hv) hvw hw1
      (fun x => duhamelIG_theta_rows (hker n) (σ 0) (σ 1) ((hs n).trans (hv.trans hvw)) hw1 x) ?_ a
    exact (hTTT n).imp (fun h => h.trans (by linarith [(tt n).2.2])) (fun h => by linarith)
  -- the bad event at the section, as a measurable set of matrices
  set ζ : ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) → ℝ := fun v => F n (tt n, v) +
    STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
      ((sz.W n : ℕ) : ℝ) ^ (-D) with hζ
  set Sset : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    ⋃ v, {H | ((sz.size n : ℕ) : ℝ) ^ τ * ζ v < ‖STLKMg Cm n (tt n : ℝ) H v.1.1 v.2‖} with hSset
  have hSm : MeasurableSet Sset := MeasurableSet.iUnion fun v =>
    measurableSet_lt measurable_const (Step2EventsGen_STLKMg_measurable hGrid' n _ _ _).norm
  have heq := hlaw s (fun m => (tt m : ℝ)) K n (K n) (hs n) (tt n).2.1 (hKne n) Sset hSm
  rw [gridTime_last s (fun m => (tt m : ℝ)) K n (hKne n)] at heq
  have hbad : badSetAt sz.size (fun n v ω => ‖Cm.L n (tt n : ℝ) v.1.1 v.2 ω - Cm.K n (tt n : ℝ) v.1.1 v.2‖)
      (fun n v _ => F n (tt n, v) + STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) τ n = {ω | Hm' n (tt n : ℝ) ω ∈ Sset} := by
    ext ω; simp [badSetAt, hSset, hζ, STLKMg, STLMg, hLM']
  rw [hbad, ← heq]
  set Gset : Set (PathΩ sz) := {ω | ∀ i : sz.STLab n,
      (∀ k, k ≤ K n → STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 k ω =
        STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 0 ω +
          ((gridStep s (fun m => (tt m : ℝ)) K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDriftg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 j ω + Rem n i k ω + Mart n i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n))}
    with hGset
  have hG : Cm.Pp Gsetᶜ = 0 := ae_iff.1 haen
  refine duhamelI_measure_le Cm.Pp (G := Gset) (by linarith) ?_ hΞn hmartn hG
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
  obtain ⟨⟨hA, hB⟩, hGω⟩ := hcon
  obtain ⟨h1, h2, h3, h4⟩ := hA
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hω
  have hv' : ((sz.size n : ℕ) : ℝ) ^ τ * ζ v < ‖STLKMg Cm n (tt n : ℝ)
      (Cm.Hpath s (fun m => (tt m : ℝ)) K n (K n) ω) v.1.1 v.2‖ := hv
  have hc : c₀ ≤ (Cm.m n).im := hIm n
  have hMa : ∀ i : sz.STLab n, ∀ k, k ≤ K n → ‖STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 k ω‖ ≤
      (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ) := by
    intro i k hk
    have hmem := ST_gridTime_mem s (fun m => (tt m : ℝ)) K n k (tt n).2.1 (hKne n) hk
    exact duhamelIG_apriori hL n (hη n) hmem.2 htt1 hTi hc₀ hc (hHerm s (fun m => (tt m : ℝ)) K n k ω) i.1 i.2
      (hKnn _ ((hs n).trans hmem.1) (hmem.2.trans (tt n).2.2) i.1 i.2)
  have hMart' : ∀ i : sz.STLab n, ∀ k, k ≤ K n → ‖Mart n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ *
      Real.sqrt (∑ j ∈ Finset.range k, gridStep s (fun m => (tt m : ℝ)) K n *
        ‖STEEMg Cm n (gridTime s (fun m => (tt m : ℝ)) K n j)
          (Cm.Hpath s (fun m => (tt m : ℝ)) K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) := by
    intro i k hk
    by_contra hlt
    rw [not_le, Real.sqrt_eq_rpow] at hlt
    exact hB (Set.mem_iUnion.2 ⟨i, k, hk, hlt⟩)
  have hrem := duhamelIG_path_rem Cm n s (fun m => (tt m : ℝ)) K ω (Mart n) (Rem n)
    (Λ := ((sz.size n : ℕ) : ℝ) ^ τ₁) (D := D) (DE := DE) (Dm := Dm)
    (M := (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ))
    (R := ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n)) (C := C) (c₀ := c₀)
    v.1.1 v.2 (hs n) hsn htt1 (hKne n) hlam hΛ hA1 hc₀ hc hC.le (hker n) (hpair n v.1.1) (hη n) (hΦn v.1.1) hDEn
    (fun i k hk => (hGω i).1 k hk) (fun i k hk => (hGω i).2 k hk) hMa hMart'
    (fun j hj σ b => h2 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, b))
    (fun j hj σ b => h3 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, b))
    (fun j hj σ b k => h4 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) ((σ, b), k)) hfloor
  have hIv : ‖Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ)
      (fun b => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b 0 ω) v.2‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * F n (tt n, v) := h1 v
  have hP0 : 0 ≤ STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) := (ST_STprof_pos sz n _ _ _ _ _).le
  have hWmD0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hκs0 : 0 ≤ κs := by rw [hκs]; positivity
  have hSTgA : STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 v.2 (K n) ω =
      STLKMg Cm n (tt n : ℝ) (Cm.Hpath s (fun m => (tt m : ℝ)) K n (K n) ω) v.1.1 v.2 := by
    unfold STgAg; rw [gridTime_last s (fun m => (tt m : ℝ)) K n (hKne n)]
  have hAK : ‖STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 v.2 (K n) ω‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ₁ * F n (tt n, v) +
        (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * κs * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ)) *
          STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have hrem2 : ‖STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 v.2 (K n) ω -
        Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ) (fun b => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b 0 ω) v.2‖ ≤
        κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
          STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) := hrem
    calc _ ≤ _ := norm_le_insert' _ (Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ)
            (fun b => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b 0 ω) v.2)
      _ ≤ _ := add_le_add hIv hrem2
      _ = _ := by ring
  have hfin := duhamelI_absorb hΛ hκs0 (hF0 n (tt n, v)) hP0 hWmD0 hA1 hρ1 hρA hNτ'
  rw [hSTgA] at hAK
  exact absurd (hAK.trans hfin) (not_le.2 hv')

end SectionMain

/-! ## 5. The engine and the pin -/

section Main

variable {d : ℕ}

/-- E1: the slots `(σ₁,σ₀)` and `(σ₀,σ₁)` of `𝒰^{(2)}_σ` carry the same kernel `θ_w`, from the swap `Θ^{(σ,!σ)} = Θ^{(!σ,σ)}` of `IniTermGen_KerFacts`
and `Θ = 1 + w θ` (`IniTermIIGen_Theta_eq`). -/
private theorem duhamelIG_pair {sz : Sizes d} {C : FlowFM sz} (n : ℕ) (hU : Step2Gen_USemigroup C n)
    (hswap : ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Bool, STThg C n σ (!σ) t = STThg C n (!σ) σ t)
    (σ : Fin 2 → Bool) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    Step2Gen_thetaKer C n (σ 1) (σ 0) w = Step2Gen_thetaKer C n (σ 0) (σ 1) w := by
  by_cases h : σ 0 = σ 1
  · rw [h]
  · have h1 : σ 1 = !(σ 0) := by
      cases h0 : σ 0 <;> cases h1' : σ 1 <;> simp_all
    have e := hswap w hw0.le hw1 (σ 0)
    rw [IniTermIIGen_Theta_eq C n hU _ _ hw0.le hw1, IniTermIIGen_Theta_eq C n hU _ _ hw0.le hw1] at e
    have hw : (w : ℂ) ≠ 0 := by exact_mod_cast hw0.ne'
    have e' : (w : ℂ) • Step2Gen_thetaKer C n (σ 0) (!σ 0) w = (w : ℂ) • Step2Gen_thetaKer C n (!σ 0) (σ 0) w := add_left_cancel e
    rw [h1]
    exact (smul_right_injective _ hw e').symm

/-- **The engine of `STDuhamelIgL` over a carrier family** (`(int_K-LcalE_n=2)`, `3_5:1941-2069`; band `stDuhamelConcl_engine`), zero-mode set `Q = ∅`, any sign class `P`:
if the initial term at `s` obeys `F`, then `‖(𝓛-𝒦)^{(2)}_{u,σ,a}‖ ≺ F + A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}` uniformly in `u ∈ [s,t]`, `σ ∈ P`.
Family premises (rows of the ticket table): `hF` flow facts (row 1), `hKer` the kernel facts at the coupling `gK` (row 2; R1 inside), `hGR` `GridRepTailGen_Ker` (row 3,
guarded), `hGM` the grid decomposition and martingale tail (row 4), `hBd, hK2` the size data and the decay of `𝒦^{(2)}` (rows 6, 7), `hFM` the flow modulus D2
(row 8, `∃ c` before `(sz, 𝔠, z)`), `hmn` the inline `‖m‖ ≤ 1`, `hKs` the time modulus D3 of `𝒦^{(2)}` (the text of `NQEndFlowGen_KLipFam` at `k = 2`, inline), `hLF` the
loop form (row 10), `hGrid` F9 (A10) and `hHerm` the Hermitian grid walk (A11), both unguarded; `hE` is the body of `STEtermsMidConclgL` written out (the
registry scan of `RBM3D/Test/Axioms.lean` then sees only `PrecL`). -/
theorem _root_.RBM.BA.stDuhamelConclgL_engine (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hF : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hKer : IniTermGen_KerFacts d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hGR : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hGM : STGridMartgL d Flow mkM T0) (hBd : STBdatagL d Flow T0) (hK2 : Step2IterGen_K2 d Flow mkM)
    (hFM : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c)
    (hmn : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hKs : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, t n ≤ T0 sz z n) →
        ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
          ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
            ‖(mkM sz z).K n u σ a - (mkM sz z).K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'|)
    (hLF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mkM sz z) (law sz))
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mkM sz z).Hpath s t K n k ω).IsHermitian)
    (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ T0 sz z n) (hReg : STReg5Mid sz s t)
    (hTTT : ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∨ 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hCon : STConStInd sz (1 / 100) s t) (hE : ∀ D : ℝ, 0 < D →
      PrecL sz (law sz) (U := STIdx2 sz s t) (fun n p ω => ‖STELKLKg (mkM sz z).toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * ((mkM sz z).eta n (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      PrecL sz (law sz) (U := STIdx2 sz s t) (fun n p ω => ‖STEGtg (mkM sz z).toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * ((mkM sz z).eta n (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      PrecL sz (law sz) (U := fun n => STIdx2 sz s t n × Fin 2)
        (fun n p ω => ‖STEEg (mkM sz z).toFlowFM n (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * ((mkM sz z).eta n (p.1.1 : ℝ))⁻¹ *
          STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2))
    (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConclgL (mkM sz z).toFlowFM (law sz) ∅ P s t := by
  classical
  intro D hD F hF0 hini
  simp only [st5_zeroModeSet_empty] at hini ⊢
  obtain ⟨κm, hκm, hFm⟩ := hF κ hκ
  obtain ⟨hAd, hT1, hIm, hηeq⟩ := hFm sz ε 𝔠 𝔡 z hflow
  have hsize : sz.SizeTendsto := hAd.2.2.1
  have hsN := tendsto_size sz hsize
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htz n) (hT1 n)
  have ht0 : ∀ n, 0 ≤ t n := fun n => (hs n).trans (hst n).le
  have hm := hmn sz κ ε 𝔠 𝔡 z hκ hflow
  have hL := hLF sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨C₀, hC₀, hGMA⟩ := hGM
  -- the kernel facts, `Φ` of a profile and the swap
  obtain ⟨C₆, C₈, Cs, c₀k, A, hC₆, hC₈, hCs, hc₀k, hA, Hk⟩ := hKer hd κ 𝔡 hκ h𝔡
  obtain ⟨hUsg, hdec, hcmp, hswap, -⟩ := Hk sz ε 𝔠 z hflow
  obtain ⟨C, hC, hΦ⟩ := duhamelIG_Phi_lam hd (Λ := 𝔡⁻¹) (inv_pos.2 h𝔡) hC₆ hA
  have hΦC := hΦ sz (mkM sz z).toFlowFM (gK sz z) hdec hcmp
  -- the size of `𝒦^{(2)}` (A8 (a)) and D3
  obtain ⟨CK, hCK, hdec2⟩ := hK2 hd κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow (fun _ => 0) t (fun _ => le_rfl) ht1
  obtain ⟨cB, hcB, hBdata⟩ := hBd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hBdz⟩ := hBdata 𝔠
  have hKn := lemDecCalELipG_Kn hCK.le hcB hc hsize
    (hdec2.mono fun n h u D σ a hu hut hD => h u D σ a hu hut hD) (hBdz sz z hflow t ht0 htz)
  have hKsz := hKs sz κ ε 𝔠 𝔡 z hκ hε hflow t htz
  -- D2
  obtain ⟨c₁, hc₁, hFMz⟩ := hFM κ ε 𝔡 hκ hε h𝔡
  obtain ⟨Hm, G, hLM, hGMM, hG, hmod⟩ := hFMz sz 𝔠 z hflow
  by_cases hP : ∃ σ, P σ
  swap
  · exact Step2EventsGen_prec_of_le_ev (law sz) (fun n p ω => absurd ⟨p.2.1.1, p.2.1.2⟩ hP)
      (Eventually.of_forall fun n p ω => absurd ⟨p.2.1.1, p.2.1.2⟩ hP)
  have hne : ∀ n, Nonempty ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) :=
    fun n => ⟨(⟨hP.choose, hP.choose_spec⟩, fun _ => 0)⟩
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [ht1 n, hs n]
  have hev := st5_eventually_A_ge_one sz h𝔡 hAd.2.2.2.2
  have htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [hev] with n hn
    exact duhamelI_htN sz n hn.1 hn.2 (hReg n).1
  have hQ := (LemDecCalELip_envg hκm hIm hηeq hsize htN 0).mono fun n h => h.2.2.1
  obtain ⟨CH, hCH0, hCH⟩ := LemDecCalELip_LK2gL hL hLM hc₁ hmod hm hs ht1 hsize hQ hKsz
  refine duhamelIG_lift sz (law sz) G hG hsize (fun n => (hst n).le) hlen
    (V := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) (Cv := 3) (CR := D) (by norm_num) hD.le ?_
    (fun n p ω => ‖(mkM sz z).L n (p.1 : ℝ) p.2.1.1 p.2.2 ω - (mkM sz z).K n (p.1 : ℝ) p.2.1.1 p.2.2‖)
    (fun n p => F n p + STAI sz n ^ (-(1 / 5) : ℝ) *
      STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ?_ ?_ ?_ ⟨CH, hCH0, ?_⟩
  · filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    exact duhamelI_card_le sz P n hn
  · intro n p
    exact add_nonneg (add_nonneg (hF0 n p) (mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) _)
      (ST_STprof_pos sz n _ _ _ _ _).le)) (Real.rpow_nonneg (by positivity) _)
  · exact Step2EventsGen_PT_of_sections (law sz) (fun n => (hst n).le) _ _ fun tt =>
      duhamelIG_section hd law Flow mkM T0 hC₀ hGMA hκ hε h𝔡 sz hflow hAd hκm hIm hηeq hL (hGrid sz z) (hHerm sz z)
        (hGR sz κ ε 𝔠 𝔡 z hκ hflow) (fun n σ w hw0 hw1 => duhamelIG_pair n (hUsg n) (hswap n) σ hw0 hw1) hC hΦC hs hst htz ht1 hKn hReg
        hTTT hCon hE hD P F hF0 hini tt
  · filter_upwards with n p
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWm : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hW0 (duhamelI_W_le_size sz (by omega) n) (neg_nonpos.2 hD.le)
    have := mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) (-(1 / 5) : ℝ) : (0 : ℝ) ≤ STAI sz n ^ (-(1 / 5) : ℝ))
      (ST_STprof_pos sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)).le
    linarith [hF0 n p]
  · filter_upwards [hCH] with n hn ω hω u u' v
    exact hn ω hω u u' v.1.1 v.2

end Main

section Pin

variable {d : ℕ}

/-- **`STDuhamelIgL`** (case (i), the integrated hierarchy without zero-mode removal, all signs; `(iois-mtx2)`, `3_5:2067`) over a carrier family `(law, Flow, mkM, T0)`:
the engine `stDuhamelConclgL_engine` at the regime `STReg5I` (`st5_reg5I_mid`, `(TTT2)` through `Or.inl`) and `𝔠_d = 1/100`.  The premises are those of the engine
(rows 1-4, 6-8, `hmn`, `hKs`, 10, A10, A11 of the ticket table); band `stDuhamelI_holds` is its corollary through `STDuhamelI_iff_gL`. -/
theorem _root_.RBM.BA.stDuhamelIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hF : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hKer : IniTermGen_KerFacts d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hGR : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hGM : STGridMartgL d Flow mkM T0) (hBd : STBdatagL d Flow T0) (hK2 : Step2IterGen_K2 d Flow mkM)
    (hFM : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c)
    (hmn : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hKs : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, t n ≤ T0 sz z n) →
        ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
          ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
            ‖(mkM sz z).K n u σ a - (mkM sz z).K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'|)
    (hLF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mkM sz z) (law sz))
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mkM sz z).Hpath s t K n k ω).IsHermitian) :
    STDuhamelIgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg _ _ _ _ _ hCon _ _ _ _ hE
  exact RBM.BA.stDuhamelConclgL_engine d law Flow mkM T0 E gK hF hKer hGR hGM hBd hK2 hFM hmn hKs hLF hGrid hHerm hd hκ hε h𝔡 sz
    hflow hs hst htz (st5_reg5I_mid (by omega) hReg) (fun n => Or.inl (hReg n).1) hCon hE STSigAll

/-- D3 at the band (the family form, the text of `NQEndFlowGen_KLipFam` at `k = 2`, inline because `NQEndFlowGen` is downstream of `LemDecCalELip`):
`LemDecCalELip_STKloop_two_lip` with `(1 - t)⁻¹ ≤ N` from `Green.v3_premises_of_stFlow` and `|E_n| ≤ 2 - κ`. -/
theorem duhamelI_Ks_band (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    (t : ℕ → ℝ) (ht : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖(bandStep2Mat sz (STflowE z)).K n u σ a - (bandStep2Mat sz (STflowE z)).K n u' σ a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'| := by
  obtain ⟨hA, hE, ht1, hR⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  filter_upwards [hR, (sz.tendsto_size hA.2.2.1).eventually_ge_atTop 1] with n hn hN1 u u' hu0 hut hu'0 hu't σ a
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) := Real.rpow_pos_of_pos (by linarith) _
  have htN : (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) :=
    calc (1 - t n)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2))⁻¹ := inv_anti₀ hp hn
      _ = ((sz.size n : ℕ) : ℝ) ^ (-(-1 + ε / 2)) := (Real.rpow_neg (by linarith) _).symm
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = _ := Real.rpow_one _
  have hE2 : |STflowE z n| ≤ 2 := ((hE n).le).trans (by linarith)
  have h := LemDecCalELip_STKloop_two_lip sz n hE2 (ht1 n) hu0 hut hu'0 hu't htN σ a
  refine h.trans ?_
  have h26 : ((sz.size n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) :=
    pow_le_pow_right₀ hN (by norm_num)
  exact mul_le_mul_of_nonneg_right h26 (abs_nonneg _)

/-- **The band tuple of the pin `STDuhamelIgL`**: `stDuhamelIgL_of` at `(seqP, STFlow, bandStep2Mat ∘ STflowE, lemT)` with the energy `STflowE z` and the coupling `gK = lam`;
every premise is discharged by a merged band result (`step5CasesGen_flowFacts_band`, `iniTermGen_kerFacts_band`, `gridRepTailGen_ker_band`, `ST_gridMart_of_repN`,
`ST_Bdata_holds`, `step2IterGen_K2_band`, D2 `lemDecCalELipG_flowMod_band`, `norm_mE`, D3 `duhamelI_Ks_band`, `stepDecompGen_loopForm_band`, F9 `Step2EventsGen_bandGrid`,
`pathH_isHermitian`). -/
theorem duhamelI_band_gL (d : ℕ) (hd : 3 ≤ d) :
    STDuhamelIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  RBM.BA.stDuhamelIgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) (fun _ z => STflowE z) (fun sz _ => sz.lam)
    (step5CasesGen_flowFacts_band d) (iniTermGen_kerFacts_band d)
    (fun sz κ ε 𝔠 𝔡 z _ h n => gridRepTailGen_ker_band sz (STflowE z) n (abs_lemE_lt_two (ST_flow_im_pos sz h n)).le)
    (bandStep2_STGridMart.1 (ST_gridMart_of_repN (RBM.Ind.stGridRepN_holds d hd)))
    ((bandFM_STBdata d).1 (ST_Bdata_holds (by omega))) (step2IterGen_K2_band d)
    (fun _ _ _ _ _ _ => ⟨1, zero_le_one, fun sz _ z h => lemDecCalELipG_flowMod_band sz (tendsto_size sz h.1.2.2.1) _⟩)
    (fun sz κ ε 𝔠 𝔡 z _ h n => (norm_mE (abs_lemE_lt_two (ST_flow_im_pos sz h n)).le).le)
    (fun sz κ ε 𝔠 𝔡 z hκ hε h t ht => duhamelI_Ks_band d sz κ ε 𝔠 𝔡 z hκ hε h t ht)
    (fun sz κ ε 𝔠 𝔡 z _ h => stepDecompGen_loopForm_band sz (STflowE z) fun n => abs_lemE_lt_two (ST_flow_im_pos sz h n))
    (fun sz z => Step2EventsGen_bandGrid sz (STflowE z)) (fun sz z s t K n k ω => pathH_isHermitian sz s t K n k ω)

/-- **The engine of `STDuhamelI`** (`(int_K-LcalE_n=2)`, `3_5:1941-2069`), zero-mode set `Q = ∅`, any sign class `P`: if the initial term at `s` obeys `F`, then
`‖(𝓛-𝒦)^{(2)}_{u,σ,a}‖ ≺ F + A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}` uniformly in `u ∈ [s,t]`, `σ ∈ P`.  Hypotheses: the flow; the window `STReg5Mid`; `(TTT2)` in the form
"`1-t ≥ ilambda²/L²` or `1-s ≤ ilambda²/L²`" (case (i) or case (ii)); `(con_st_ind)` at `𝔠_d = 1/100`; `hE`, the body of `STEtermsMidConcl` written out
(`STEtermsMidConcl sz (STflowE z) s t` is accepted as `hE`; written out so that the registry scan of `RBM3D/Test/Axioms.lean`, which flags a Prop-valued definition that nothing proves, sees only `Prec`).  The band corollary, name and type unchanged (G1), of `stDuhamelConclgL_engine` at the band tuple through `bandFM_STDuhamelConcl`. -/
theorem stDuhamelConcl_engine (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5Mid sz s t)
    (hTTT : ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∨ 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hCon : STConStInd sz (1 / 100) s t)
    (hE : ∀ D : ℝ, 0 < D →
      sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STELKLK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (etaT (STflowE z n) (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STEGt sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      sz.Prec (U := fun n => STIdx2 sz s t n × Fin 2)
        (fun n p ω => ‖STEEk sz n (STflowE z n) (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (p.1.1 : ℝ))⁻¹ *
          STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2))
    (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConcl sz ∅ P (STflowE z) s t :=
  (RBM.BA.bandFM_STDuhamelConcl sz (STflowE z) s t ∅ P).2
    (RBM.BA.stDuhamelConclgL_engine d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) (fun _ z => STflowE z) (fun sz _ => sz.lam)
      (step5CasesGen_flowFacts_band d) (iniTermGen_kerFacts_band d)
      (fun sz κ ε 𝔠 𝔡 z _ h n => gridRepTailGen_ker_band sz (STflowE z) n (abs_lemE_lt_two (ST_flow_im_pos sz h n)).le)
      (bandStep2_STGridMart.1 (ST_gridMart_of_repN (RBM.Ind.stGridRepN_holds d hd)))
      ((bandFM_STBdata d).1 (ST_Bdata_holds (by omega))) (step2IterGen_K2_band d)
      (fun _ _ _ _ _ _ => ⟨1, zero_le_one, fun sz _ z h => lemDecCalELipG_flowMod_band sz (tendsto_size sz h.1.2.2.1) _⟩)
      (fun sz κ ε 𝔠 𝔡 z _ h n => (norm_mE (abs_lemE_lt_two (ST_flow_im_pos sz h n)).le).le)
      (fun sz κ ε 𝔠 𝔡 z hκ hε h t ht => duhamelI_Ks_band d sz κ ε 𝔠 𝔡 z hκ hε h t ht)
      (fun sz κ ε 𝔠 𝔡 z _ h => stepDecompGen_loopForm_band sz (STflowE z) fun n => abs_lemE_lt_two (ST_flow_im_pos sz h n))
      (fun sz z => Step2EventsGen_bandGrid sz (STflowE z)) (fun sz z s t K n k ω => pathH_isHermitian sz s t K n k ω) hd hκ hε h𝔡 sz
      hflow hs hst htz hReg hTTT hCon hE P)

/-- **`STDuhamelI`** (case (i), the integrated hierarchy without zero-mode removal, all signs): the band corollary, name and type unchanged (G1), of
`stDuhamelIgL_of` through `STDuhamelI_iff_gL`. -/
theorem stDuhamelI_holds (d : ℕ) : STDuhamelI d :=
  (RBM.BA.STDuhamelI_iff_gL d).2 fun hd => duhamelI_band_gL d hd hd

end Pin

end KernelG

end RBM.Gauss.Sizes

/-! ## Compiled nonempty instances at `d = 3` -/

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter RBM.BA

/-- `stDuhamelI_holds` at `(szB, zB, 7/8, 15/16)` (the data of `inst_duhamelI`). -/
theorem inst_duhamelI_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_duhamelI (stDuhamelI_holds 3) Cd hCd

/-- `stDuhamelConcl_engine` at the same data, for all signs; `STEtermsMidConcl` is the proved pin of another gate. -/
example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STDuhamelConcl szB ∅ STSigAll (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  stDuhamelConcl_engine (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (st5_reg5I_mid (by norm_num) szB_reg5I) (fun n => Or.inl (szB_reg5I n).1)
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hE STSigAll

/-- The same at the data of case (ii), `(szB, zB, 15/16, 31/32)`, equal signs (`(TTT2)` through `1-s ≤ ilambda²/L²`). -/
example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) :
    STDuhamelConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  stDuhamelConcl_engine (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (fun n => ⟨(szB_reg5II n).1, by simp [szB]; norm_num⟩)
    (fun n => Or.inr (szB_reg5II n).2) (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num))
    hE STSigSame

/-- The exponent closure (5) at concrete numbers (`duhamelI_absorb`): `A = 2^99`, so that `(2A)^{1/100} = 2 = ρ`; `Λ = 2`,
`κ = 3`, `F = P = W^{-D} = 1`, `N^τ = (2κ+1)Λ² = 28`. -/
example : (2 : ℝ) * 1 + 2 ^ 2 * 3 * (2 ^ 3 * ((2 : ℝ) ^ 99) ^ (-(1 / 4) : ℝ)) * 1 + 1 ≤
    28 * (1 + ((2 : ℝ) ^ 99) ^ (-(1 / 5) : ℝ) * 1 + 1) :=
  duhamelI_absorb (Λ := 2) (κ := 3) (F := 1) (P := 1) (Wm := 1) (A := 2 ^ 99) (ρ := 2) (Nτ := 28) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h1 : (2 * (2 : ℝ) ^ 99) = 2 ^ 100 := by norm_num
      have h2 : ((1 : ℝ) / 100) = ((100 : ℕ) : ℝ)⁻¹ := by norm_num
      rw [h1, h2, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)])
    (by norm_num)


/-- **Target 6 at a concrete instance** (`duhamelIG_duhamel`): at the band kernel `Step2Gen_UN (bandStep2Mat sz0 (fun _ => 1/2))`, `d = 3`, `n = 0` (`L = 4`, `W = 32`), the charge
class `σ = (+,-)`, `k = 3` steps of size `Δ = 1/16` from `u_0 = 0` (`u_3 = 3/16 < 1`): `A_j ≡ 1 + j/10` (every entry), `Mart_j ≡ j/10`, `Rem = 0` and the forcing
`F_i = -Θ^{(2)}_{u_i} A_i`, which cancels the drift, so that `A_j = A_0 + Δ Σ_{i<j} (Θ^{(2)} A_i + F_i) + Rem_j + Mart_j` holds.  `K1`-`K4` are the band results
(`gridRepTailGen_ker_band`); every hypothesis is discharged. -/
example (a : Fin 2 → Zd 3 (sz0.L 0)) :=
  RBM.BA.duhamelIG_duhamel (C := (bandStep2Mat sz0 (fun _ => 1 / 2)).toFlowFM) (n := 0)
    (RBM.BA.gridRepTailGen_ker_band sz0 (fun _ => 1 / 2) 0 (by norm_num)) (1 / 16) 2 0 ![true, false] 3 (fun j => (j : ℝ) / 16)
    (fun j _ => (((1 + (j : ℝ) / 10 : ℝ)) : ℂ))
    (fun i b => -Step2Gen_ThetaN (bandStep2Mat sz0 (fun _ => 1 / 2)).toFlowFM 0 ![true, false] ((i : ℝ) / 16)
      (fun _ => (((1 + (i : ℝ) / 10 : ℝ)) : ℂ)) b)
    (fun _ _ => 0) (fun j _ => (((j : ℝ) / 10 : ℝ) : ℂ)) (by norm_num) (by norm_num) (fun j => by push_cast; ring) (by norm_num)
    (fun j hj b => by
      have hj' : (j : ℝ) ≤ 3 := by exact_mod_cast hj
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith)
    (fun j _ b => le_of_eq norm_zero)
    (fun j _ b => by
      simp only [add_neg_cancel, Finset.sum_const_zero, mul_zero, add_zero]
      push_cast; ring) a

/-- **Target 8 at a concrete instance** (`stDuhamelIgL_of` at the band tuple through `duhamelI_band_gL`, every premise discharged by a band result) at
`(szB, zB, 7/8, 15/16)` and every `C_d > 0`: the conclusion of the generic pin, read through `STDuhamelI_iff_gL`, gives the instance `InstIng5Concl`. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_duhamelI ((RBM.BA.STDuhamelI_iff_gL 3).2 (duhamelI_band_gL 3 (by norm_num))) Cd hCd

/-- **`duhamelIG_Phi_lam` at a concrete instance** (target 7, the kernel part): at the band kernel `bandFM sz0 (STflowE z0)` of the flow `(sz0, z0)` (`κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`; the decay `Step5KerGen_ThDecay` and the comparison R1 are `iniTermGen_kerFacts_band`), `n = 0` (`L = 4`, `λ = 1/64`), `σ σ' = (+,-)`, `D = 1`, `v = 0`, `w = 1/2`:
the constant `C` exists and bounds `Φ` of the profile at every `a`; the row sums of `θ_w` are K3 of `gridRepTailGen_ker_band`, the window `(TTT2)` is `λ²/L² ≤ 1 - w`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 (sz0.L 0),
    duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer (bandFM sz0 (STflowE z0)) 0 true false (1 / 2) x y‖) (2 * (1 - 0))
        (fun x y => STprof sz0 0 0 1 ((sz0.L 0 : ℕ) : ℝ) x y) a ≤
      C * ((1 - 0) / (1 - 1 / 2)) * ((((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ *
        (tailT 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ((zdistInf 3 (sz0.L 0) (a 0 - a 1) : ℕ) : ℝ) +
          (1 - 0) / (1 - 1 / 2) * ((sz0.W 0 : ℕ) : ℝ) ^ (-1 : ℝ))) := by
  obtain ⟨C₆, C₈, Cs, c₀, A, hC₆, -, -, -, hA, H⟩ := iniTermGen_kerFacts_band 3 (le_refl 3) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨-, hdec, hcmp, -, -⟩ := H sz0 (1 / 10) (1 / 6) z0 flow_z0
  obtain ⟨C, hC, hΦ⟩ := duhamelIG_Phi_lam (le_refl 3) (Λ := (1 / 10 : ℝ)⁻¹) (by norm_num) hC₆ hA
  refine ⟨C, hC, fun a => hΦ sz0 (bandFM sz0 (STflowE z0)) sz0.lam hdec hcmp 0 true false 1 0 (1 / 2)
    (by rw [sz0_values.2.2.2]; norm_num) (by rw [sz0_values.2.2.2]; norm_num) le_rfl (by norm_num) (by norm_num) ?_ ?_ a⟩
  · intro x
    exact duhamelIG_theta_rows (gridRepTailGen_ker_band sz0 (STflowE z0) 0 (abs_lemE_lt_two (ST_flow_im_pos sz0 flow_z0 0)).le) true false
      (by norm_num) (by norm_num) x
  · left
    rw [sz0_values.2.2.2, sz0_values.1]; norm_num

/-- **`duhamelIG_Ugen_le` at a concrete instance** (target 7, section 4): `‖𝒰^{(2)}_{0,1/2} Y‖_a ≤ Φ_{2}(‖θ_{1/2}‖, |Y|)` at the band kernel `bandFM sz0 (STflowE z0)`, `n = 0`,
`σ = (+,+)` (the swap E1 is then trivial), `Y ≡ 1`, with the semigroup law K1 of `gridRepTailGen_ker_band`. -/
example (a : Fin 2 → Zd 3 (sz0.L 0)) :
    ‖Step2Gen_UN (bandFM sz0 (STflowE z0)) 0 ![true, true] 0 (1 / 2) (fun _ => (1 : ℂ)) a‖ ≤
      duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer (bandFM sz0 (STflowE z0)) 0 (![true, true] 0) (![true, true] 1) (1 / 2) x y‖)
        (2 * (1 - 0)) (fun x y => ‖(fun _ => (1 : ℂ)) ![x, y]‖) a :=
  duhamelIG_Ugen_le (gridRepTailGen_ker_band sz0 (STflowE z0) 0 (abs_lemE_lt_two (ST_flow_im_pos sz0 flow_z0 0)).le).1 ![true, true]
    (fun _ _ _ => rfl) le_rfl (by norm_num) (by norm_num) (by norm_num) _ a

end RBM.Gauss.Step5Inst
