/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.DecayGen
import RBM3D.Induction.GridEnvelopeN

/-!
# The envelope of the grid drift over a flow carrier

Generic forms of `Induction/GridEnvelopeN` over a carrier `Cm : Step2Mat sz` (namespace `RBM.BA`);
`GridDriftNg`, `stepErrNg` (`Chain/HierDriftGen`) and `exists_norm_KI_le_wing` are used by name.

* `sum_gridStep_div_etaNg_le` (band `sum_gridStep_div_etaT_le`): `Σ_j Δ/η_{u_j} ≤ (Im m)⁻¹ log N`
  under `RangeCond`, with `η_t = (1 - t) Im m` from `DecayGen_Spec`;
* `SumWeightedStepErrNg_Stmt`, `sum_weighted_stepErrNg_le` (band `SumWeightedStepErrN_Stmt`,
  `sum_weighted_stepErrN_le`): the weighted step errors sum to at most `N^{-D_t}`.  The hypothesis
  `∀ n, (Cm.m n).im ≤ 1` replaces `|E n| ≤ 2 - κ`.  The proof is the band theorem at the energy
  `E'_n = 2 √(1 - (Im m_n)²)`, for which `(mE E'_n).im = Im m_n`, `|E'_n| ≤ 2 - κ_m²`, and
  `stepErrNg` (which reads the carrier only through `Cm.eta`) is `stepErrN … E'_n`.

Private band helpers are reused by `open private … from RBM3D.Induction.GridEnvelopeN`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private gridEnv_gridStep_nonneg gridEnv_gridTime_le gridEnv_gridTime_nonneg gridEnv_one_le_size
  from RBM3D.Induction.GridEnvelopeN

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal
open RBM.Ind (kStepC uStepC)

/-! ## 1. `Σ_j Δ/η_{u_j} ≤ (Im m)⁻¹ log N` -/

section SumEta

variable {d : ℕ} {sz : Sizes d}

/-- `sum_gridStep_div_etaNg_le` (band `sum_gridStep_div_etaT_le`): `Σ_j Δ/η_{u_j} ≤ (Im m)⁻¹ log N`
on the grid `u_j = s + jΔ` under `RangeCond` (`1 - t ≥ N^{-(1-τ')}`, `τ' > 0`), `η_t = (1 - t) Im m` being the `DecayGen_Spec`
reading of `Cm.eta`: each term is `≤ (Im m)^{-1}(log(1-u_j) - log(1-u_{j+1}))`, the sum telescopes to `-log(1-t) ≤ (1-τ') log N`. -/
theorem sum_gridStep_div_etaNg_le (Cm : Step2Mat sz) {κm τ' : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm) (hτ' : 0 < τ')
    {s t : ℕ → ℝ} {K : ℕ → ℕ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hrange : sz.RangeCond τ' t) :
    ∀ᶠ n : ℕ in atTop, ∑ j ∈ Finset.range (K n), gridStep s t K n / Cm.eta n (gridTime s t K n j) ≤
      (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hrange] with n hn
  have hu1 : ∀ j ≤ K n, gridTime s t K n j < 1 := fun j hj =>
    (gridEnv_gridTime_le (hst n) (hK0 n) hj).trans_lt (ht1 n)
  have hpos : ∀ j ≤ K n, 0 < 1 - gridTime s t K n j := fun j hj => by linarith [hu1 j hj]
  have him : 0 < (Cm.m n).im := hspec.1.trans_le (hspec.2.1 n)
  have hstep : ∀ j < K n, gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log (1 - gridTime s t K n j) - Real.log (1 - gridTime s t K n (j + 1)) := by
    intro j hj
    have h1 := hpos j hj.le
    have h2 := hpos (j + 1) hj
    have hx : 0 < (1 - gridTime s t K n j) / (1 - gridTime s t K n (j + 1)) := div_pos h1 h2
    have h3 := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div h1.ne' h2.ne', inv_div] at h3
    have hΔj : gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
      unfold gridTime; push_cast; ring
    have e : 1 - (1 - gridTime s t K n (j + 1)) / (1 - gridTime s t K n j) =
        gridStep s t K n / (1 - gridTime s t K n j) := by
      rw [hΔj]; field_simp; ring
    rwa [e] at h3
  have hsum : ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log (1 - gridTime s t K n 0) - Real.log (1 - gridTime s t K n (K n)) := by
    rw [← Finset.sum_range_sub' (fun j => Real.log (1 - gridTime s t K n j)) (K n)]
    exact Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.1 hj)
  have hs' : gridTime s t K n 0 = s n := by unfold gridTime; simp
  have hlast : gridTime s t K n (K n) = t n := gridTime_last s t K n (hK0 n)
  rw [hs', hlast] at hsum
  have hlog0 : Real.log (1 - s n) ≤ 0 :=
    Real.log_nonpos (by linarith [hst n, ht1 n]) (by linarith [hs0 n])
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := gridEnv_one_le_size sz n
  have hlogN : 0 ≤ Real.log ((sz.size n : ℕ) : ℝ) := Real.log_nonneg hN1
  have ht0 : 0 < 1 - t n := by linarith [ht1 n]
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hlogt : -Real.log (1 - t n) ≤ Real.log ((sz.size n : ℕ) : ℝ) := by
    have h4 := Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hn
    rw [Real.log_rpow hNpos] at h4
    nlinarith
  have hfin : ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log ((sz.size n : ℕ) : ℝ) := by linarith
  calc ∑ j ∈ Finset.range (K n), gridStep s t K n / Cm.eta n (gridTime s t K n j)
      = (Cm.m n).im⁻¹ *
          ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hspec.2.2 n]
        field_simp
    _ ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hfin (inv_nonneg.2 him.le)

end SumEta

/-! ## 2. The weighted step errors -/

section Weighted

variable {d : ℕ} {sz : Sizes d}

/-- `stepErrNg` reads the carrier only through `C.eta n`. -/
theorem GridEnvelopeGen_stepErrNg_eta {C C' : FlowFM sz} (n k : ℕ) (u v Δ Bk : ℝ) (h : ∀ t, C.eta n t = C'.eta n t) :
    stepErrNg C n k u v Δ Bk = stepErrNg C' n k u v Δ Bk := by
  unfold stepErrNg
  rw [h, h]

/-- The energy `E' = 2 √(1 - y²)` with `y = Im m ∈ [0, 1]` has `Im m(E') = y` (`mE_im`). -/
theorem GridEnvelopeGen_mE_im_Ep {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (mE (2 * Real.sqrt (1 - y ^ 2))).im = y := by
  have h1 : (2 * Real.sqrt (1 - y ^ 2)) ^ 2 = 4 * (1 - y ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by nlinarith)]
    norm_num
  rw [mE_im, h1]
  have h2 : 4 - 4 * (1 - y ^ 2) = (2 * y) ^ 2 := by ring
  rw [h2, Real.sqrt_sq (by linarith)]
  ring

/-- `|E'| ≤ 2 - κ²` for `0 < κ ≤ y ≤ 1`. -/
theorem GridEnvelopeGen_abs_Ep_le {y κ : ℝ} (hκ : 0 < κ) (hκy : κ ≤ y) (hy1 : y ≤ 1) :
    |2 * Real.sqrt (1 - y ^ 2)| ≤ 2 - κ ^ 2 := by
  have hy0 : 0 ≤ y := hκ.le.trans hκy
  have hr0 : 0 ≤ Real.sqrt (1 - y ^ 2) := Real.sqrt_nonneg _
  rw [abs_of_nonneg (by positivity)]
  have hr2 : Real.sqrt (1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt (by nlinarith)
  have hκ1 : κ ^ 2 ≤ 1 := by nlinarith
  have hκ2 : κ ^ 2 ≤ y ^ 2 := by nlinarith
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [hcon, hr0, hr2, hκ1, hκ2, sq_nonneg (κ ^ 2)]

/-- `SumWeightedStepErrNg_Stmt` (band `SumWeightedStepErrN_Stmt`): on the grid `u_j = gridTime s t K n j` with
`K n ≥ N^{C_K}`, the step errors `stepErrNg` at the envelope `B_k = N^{τ_K} η_{u_{j+1}}^{-k}`, weighted by the coarse row bound
`(1 + (1 − u_m)^{-1})^k` of the kernel, sum to at most `N^{-D_t}` for every `m ≤ K n`, eventually, as soon as
`C_K` exceeds the four lower bounds in the hypotheses (`θ = 1 − τ'`, `RangeCond τ' t`).  The spectral data are `DecayGen_Spec`
(`κ_m ≤ Im m`, `η_t = (1 - t) Im m`) and the hypothesis `∀ n, (Cm.m n).im ≤ 1`. -/
def SumWeightedStepErrNg_Stmt : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) {κm τ' τK C_K D_t : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ),
    DecayGen_Spec Cm.toFlowFM κm → (∀ n, (Cm.m n).im ≤ 1) → 0 < τ' → τ' ≤ 1 → 0 < τK → 0 ≤ D_t → 2 ≤ k →
    sz.SizeTendsto → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) → sz.RangeCond τ' t →
    8 + (4 * (k : ℝ) + 8) * (1 - τ') + 2 * D_t < C_K → 3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + D_t < C_K →
    2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + D_t < C_K → 1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ m ≤ K n, ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        stepErrNg Cm.toFlowFM n k (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t)

/-- `sum_weighted_stepErrNg_le`: the statement `SumWeightedStepErrNg_Stmt`, from the band
`sum_weighted_stepErrN_le` at the energy `E'_n = 2 √(1 - (Im m_n)²)` (`κ = κ_m²`). -/
theorem sum_weighted_stepErrNg_le : SumWeightedStepErrNg_Stmt := by
  intro d sz Cm κm τ' τK C_K D_t s t K k hspec him1 hτ' hτ'1 hτK hDt hk hsize hs0 hst ht1 hK0 hrange h1 h2 h3 h4 hKN
  set E' : ℕ → ℝ := fun n => 2 * Real.sqrt (1 - ((Cm.m n).im) ^ 2) with hE'
  have hκm : 0 < κm := hspec.1
  have hE'2 : ∀ n, |E' n| ≤ 2 - κm ^ 2 := fun n =>
    GridEnvelopeGen_abs_Ep_le hκm (hspec.2.1 n) (him1 n)
  have hmE : ∀ n, (mE (E' n)).im = (Cm.m n).im := fun n =>
    GridEnvelopeGen_mE_im_Ep (hκm.le.trans (hspec.2.1 n)) (him1 n)
  have hetaE : ∀ n t, etaT (E' n) t = Cm.eta n t := fun n t => by
    rw [hspec.2.2 n t]; unfold etaT; rw [hmE n]
  have hstep : ∀ n u v Δ B, RBM.Ind.stepErrN d (sz.L n) (sz.W n) (E' n) k u v Δ B =
      stepErrNg Cm.toFlowFM n k u v Δ B := fun n u v Δ B => by
    rw [bandFM_stepErrN sz E' n k u v Δ B]
    exact GridEnvelopeGen_stepErrNg_eta n k u v Δ B (fun t => hetaE n t)
  have hband := RBM.Ind.sum_weighted_stepErrN_le d sz (κ := κm ^ 2) (E := E') k (by positivity) hτ' hτ'1 hτK hDt hk hsize
    hE'2 hs0 hst ht1 hK0 hrange h1 h2 h3 h4 hKN
  refine hband.mono fun n hn m hm => ?_
  have := hn m hm
  simp only [hstep, hetaE] at this
  exact this

end Weighted

end RBM.BA

end
