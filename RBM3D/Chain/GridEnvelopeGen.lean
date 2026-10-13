/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.DecayGen
import RBM3D.Induction.GridEnvelopeN

/-!
# The envelope of the grid drift over the carrier (BA-T row T4s2a, file 2, ticket T2473)

Generic forms of `Induction/GridEnvelopeN.lean` (not edited) over a carrier `Cm : Step2Mat sz`,
namespace `RBM.BA`, no `BA/*` import.  T2474's `GridDriftNg`, `stepErrNg`, `predIncNg` and
`exists_norm_KI_le_wing` are read by name (dispatcher answer (1)).

* `gridDriftNg_envelope` (band `gridDriftN_envelope`, `GridEnvelopeN:111`): `GridDriftNg` holds
  a.e. with the step errors `stepErrNg … (N^{τ_K} η_{u_{j+1}}^{-k})` for every grid step `j < K n`
  at once, eventually in `n`; the `𝒦`-window is `exists_norm_KI_le_wing` (`STKboundgL`, the link
  `KI ∘ KLloopOf = K`, and `0 < η ≤ 1 - v`);
* `sum_gridStep_div_etaNg_le` (band `sum_gridStep_div_etaT_le`, `GridEnvelopeN:180`):
  `Σ_j Δ/η_{u_j} ≤ (Im m)⁻¹ log N` under `RangeCond`, with `η_t = (1 - t) Im m` from
  `DecayGen_Spec`;
* `SumWeightedStepErrNg_Stmt`, `sum_weighted_stepErrNg_le` (band `GridEnvelopeN:595, 613`): the
  weighted step errors sum to at most `N^{-D_t}`.  The premise `∀ n, (Cm.m n).im ≤ 1` is allowed
  (Amend 1, S2).  The proof is the band theorem at the energy `E'_n = 2 √(1 - (Im m_n)²)`, for
  which `(mE E'_n).im = Im m_n`, `|E'_n| ≤ 2 - κ_m²`, and `stepErrNg` (which reads the carrier
  only through `Cm.eta`) is `stepErrN … E'_n`.

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

/-! ## 1. The envelope of the grid drift -/

section Drift

variable {d : ℕ} {sz : Sizes d}

/-- **Target 5, `gridDriftNg_envelope`** (band `gridDriftN_envelope`, `GridEnvelopeN:111`): `exists_norm_KI_le_wing` supplies
`B_k = N^{τ_K} η_{u_{j+1}}^{-k}` in `GridDriftNg` for every grid step `j < K n` at once, so `GridDriftNg` holds with
`stepErrNg Cm.toFlowFM … (N^{τ_K} η_{u_{j+1}}^{-k})`, a.e. in `ω` simultaneously for all `j < K n` and all labels.  The
one-step drift `GridDriftNg Cm s t K` (T2474's `gridDriftNg`) is a hypothesis. -/
theorem gridDriftNg_envelope (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 2 ≤ k) (τK : ℝ) (hτK : 0 < τK) {s t : ℕ → ℝ} {K : ℕ → ℕ} (hsize : sz.SizeTendsto)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hη : ∀ (n : ℕ) (v : ℝ), 0 ≤ v → v < 1 → 0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hGD : GridDriftNg Cm s t K) (σ : Fin k → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ j, j < K n → ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        stepErrNg Cm.toFlowFM n k (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k) := by
  classical
  have hv1 : ∀ n j, j < K n → gridTime s t K n (j + 1) < 1 := fun n j hj =>
    (gridEnv_gridTime_le (hst n) (hK0 n) (show j + 1 ≤ K n by omega)).trans_lt (ht1 n)
  -- the deterministic envelope statement at the grid step `j`
  let P : ℕ → ℕ → Prop := fun n j => ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)),
    ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖Cm.KI n w J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k
  have hP : ∀ᶠ n in atTop, ∀ j, j < K n → P n j := by
    by_contra hcon
    have hfreq := Filter.not_eventually.1 hcon
    let bad : ℕ → Prop := fun n => ∃ j, j < K n ∧ ¬ P n j
    have hbad : ∀ n, ¬ (∀ j, j < K n → P n j) → bad n := by
      intro n hn
      by_contra hb
      exact hn fun j hj => by
        by_contra hc
        exact hb ⟨j, hj, hc⟩
    let v : ℕ → ℝ := fun n =>
      if h : bad n then gridTime s t K n (Classical.choose h + 1) else 0
    have hvmem : ∀ n, 0 ≤ v n ∧ v n < 1 := by
      intro n
      by_cases h : bad n
      · have e : v n = gridTime s t K n (Classical.choose h + 1) := by simp [v, h]
        rw [e]
        exact ⟨gridEnv_gridTime_nonneg (hs0 n) (hst n) _, hv1 n _ (Classical.choose_spec h).1⟩
      · have e : v n = 0 := by simp [v, h]
        rw [e]
        exact ⟨le_rfl, one_pos⟩
    have hwin := exists_norm_KI_le_wing Cm μ hsize hKb hKK hη v (fun n => (hvmem n).1)
      (fun n => (hvmem n).2) k τK hτK
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hwin).exists
    have hbn : bad n := hbad n hn1
    obtain ⟨hjlt, hnP⟩ := Classical.choose_spec hbn
    have e : v n = gridTime s t K n (Classical.choose hbn + 1) := by simp [v, hbn]
    apply hnP
    intro w hw J hJ h2 hJk
    have hb := hn2 w (by rw [e]; exact hw) J hJ h2 hJk
    rw [e] at hb
    exact hb
  filter_upwards [hP] with n hn
  refine ae_all_iff.2 fun j => ?_
  by_cases hj : j < K n
  · have hη' : 0 < Cm.eta n (gridTime s t K n (j + 1)) :=
      (hη n _ (gridEnv_gridTime_nonneg (hs0 n) (hst n) _) (hv1 n j hj)).1
    have hBk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη'.le) _)
    have h := hGD hs0 hst ht1 hK0 n j hj k hk σ _ hBk (hn j hj)
    exact h.mono fun ω hω _ => hω
  · exact Eventually.of_forall fun ω h => absurd h hj

end Drift

/-! ## 2. `Σ_j Δ/η_{u_j} ≤ (Im m)⁻¹ log N` -/

section SumEta

variable {d : ℕ} {sz : Sizes d}

/-- **Target 5, `sum_gridStep_div_etaNg_le`** (band `sum_gridStep_div_etaT_le`, `GridEnvelopeN:180`): `Σ_j Δ/η_{u_j} ≤ (Im m)⁻¹ log N`
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

/-! ## 3. The weighted step errors -/

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

/-- **Pin `SumWeightedStepErrNg_Stmt`** (band `SumWeightedStepErrN_Stmt`, `GridEnvelopeN:595`): on the grid `u_j = gridTime s t K n j` with
`K n ≥ N^{C_K}`, the step errors of `gridDriftNg_envelope` (`B_k = N^{τ_K} η_{u_{j+1}}^{-k}`), weighted by the coarse row bound
`(1 + (1 − u_m)^{-1})^k` of the kernel, sum to at most `N^{-D_t}` for every `m ≤ K n`, eventually, as soon as `C_K` exceeds the three
rows A, B, C and the expansion row D (`θ = 1 − τ'`, `RangeCond τ' t`).  The spectral data are `DecayGen_Spec` (`κ_m ≤ Im m`,
`η_t = (1 - t) Im m`) and the inline premise `∀ n, (Cm.m n).im ≤ 1` (Amend 1, S2; band discharge `hierDriftGen_band_eta` at `v = 0`,
BA discharge owed by T4-BA, `BAm_norm_le_one`). -/
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

/-- **Target 5, `sum_weighted_stepErrNg_le`**: the pinned statement `SumWeightedStepErrNg_Stmt`, from the band
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

/-! ## 4. Compiled nonempty instances at the band carrier (`d = 3`)

The size sequence is the merged `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `N_0 = 2097152`), the carrier is `bandStep2Mat sz0 E0` with
`E0 ≡ 0` (`Im m = 1`, `κ_m = 1/2` by `DecayGen_bandSpec` at `κ = 1`), and the data are those of the band instances of
`Induction/GridEnvelopeN.lean:707-780` (`GridEnvelopeNCheck`).  Every deterministic hypothesis is discharged; the registered
pin `STKboundgL` (KL7) stays a hypothesis of the first example. -/

section Instances

namespace GridEnvelopeGenCheck

open RBM.Gauss.SizesInst RBM.Ind.GridEnvelopeNCheck

private abbrev Cm0 : Step2Mat sz0 := bandStep2Mat sz0 (fun _ => 0)

private theorem hE0 : ∀ n, |(fun _ : ℕ => (0 : ℝ)) n| < 2 := fun _ => by norm_num
private theorem hL0 : StepDecompGen_LoopForm Cm0 (fun _ => 0) := stepDecompGen_loopForm_band sz0 _ hE0
private theorem hW0 : StepDecompGen_WalkForm Cm0 sz0.lam (fun _ => 0) := stepDecompGen_walkForm_band sz0 _
private theorem hspec0 : DecayGen_Spec Cm0.toFlowFM (Real.sqrt 1 / 2) :=
  DecayGen_bandSpec sz0 (κ := 1) (by norm_num) (fun n => by norm_num)

private theorem him1 (n : ℕ) : (Cm0.m n).im ≤ 1 := by
  change (mE 0).im ≤ 1
  rw [mE_im]
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 - (0 : ℝ) ^ 2) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4]
  norm_num

private theorem hη0 (n : ℕ) (v : ℝ) (_ : 0 ≤ v) (hv1 : v < 1) : 0 < Cm0.eta n v ∧ Cm0.eta n v ≤ 1 - v :=
  hierDriftGen_band_eta 0 (by norm_num) hv1

/-- **Target 5, `gridDriftNg_envelope`** at `κ`-free data: `k = 3`, `τ_K = 1/2`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, every sign vector.
`GridDriftNg` is `gridDriftNg` of T2474 with every class discharged at the band; `SizeTendsto` is `sz0_tendsto`; the link is `rfl`.
The registered pin `STKboundgL` (KL7) is the one hypothesis left open. -/
example (hKb : STKboundgL Cm0.toFlowFM (Sizes.seqP sz0)) (σ : Fin 3 → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂Cm0.Pp, ∀ j, j < (fun _ => 4 : ℕ → ℕ) n → ∀ a : Fin 3 → Zd 3 (sz0.L n),
      ‖predIncNg Cm0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j σ ω a -
          (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n : ℂ) *
          (∑ l ∈ Finset.Icc 3 3, STksimLKMg Cm0 n (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j)
              (Cm0.Hpath (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j ω) l (KLloopOf 3 (sz0.L n) σ a) +
            STelklkMg Cm0 n (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j)
              (Cm0.Hpath (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j ω) (KLloopOf 3 (sz0.L n) σ a) +
            STegtMg Cm0 n (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j)
              (Cm0.Hpath (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j ω) (KLloopOf 3 (sz0.L n) σ a))‖ ≤
        stepErrNg Cm0.toFlowFM n 3 (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j)
          (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n (j + 1))
          (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n)
          (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
            (Cm0.eta n (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n (j + 1)))⁻¹ ^ 3) :=
  gridDriftNg_envelope Cm0 (Sizes.seqP sz0) 3 (by norm_num) (1 / 2) (by norm_num) sz0_tendsto hKb
    (fun n w k σ a => rfl) hη0 (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num)
    (gridDriftNg hL0 hW0 _ _ _ (fun n => hierDriftGen_expand_band sz0 _ hE0 _ _ _ n)
      (hierDriftGen_kLoop_band sz0 _ hE0) (hierDriftGen_kTwo_band sz0 _ hE0) (hierDriftGen_uStep_band sz0 _ hE0)
      (fun n a => hierDriftGen_SB_row sz0 n a) (hierDriftGen_kLink_band sz0 _)) σ

/-- **Target 5, `sum_gridStep_div_etaNg_le`** at `τ' = 2/3`, `s ≡ 0`, `K ≡ 4`, `t_n = 1 - N_n^{-1/3}` (the boundary of
`RangeCond`, `t_n → 1`): every hypothesis proved. -/
example : ∀ᶠ n : ℕ in atTop, ∑ j ∈ Finset.range ((fun _ => 4 : ℕ → ℕ) n),
      gridStep (fun _ => (0 : ℝ)) tBd (fun _ => 4) n / Cm0.eta n (gridTime (fun _ => (0 : ℝ)) tBd (fun _ => 4) n j) ≤
    (Cm0.m n).im⁻¹ * Real.log ((sz0.size n : ℕ) : ℝ) :=
  sum_gridStep_div_etaNg_le Cm0 hspec0 (τ' := 2 / 3) (by norm_num) (s := fun _ => 0) (t := tBd) (K := fun _ => 4)
    (fun _ => le_rfl) (fun n => zero_le_tBd n) tBd_lt_one
    (fun _ => by norm_num) rangeCond_tBd

/-- **Target 5, `sum_weighted_stepErrNg_le`** at `k = 3`, `τ' = τ_K = 1/2`, `C_K = 21`, `D_t = 1`, `s ≡ 0`, `t ≡ 1/2`,
`K n = N_n^{21}`: the four inequalities read `20 < 21`, `13.5 < 21`, `5.5 < 21`, `0.5 < 21`; nothing is left as a hypothesis. -/
example : ∀ᶠ n : ℕ in atTop, ∀ m ≤ Kc n,
      ∑ j ∈ Finset.range m, (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n m)⁻¹) ^ 3 *
          stepErrNg Cm0.toFlowFM n 3 (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j)
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1))
            (gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (Cm0.eta n (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1)))⁻¹ ^ 3) ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  sum_weighted_stepErrNg_le 3 sz0 Cm0 (κm := Real.sqrt 1 / 2) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 21) (D_t := 1)
    (s := fun _ => 0) (t := fun _ => 1 / 2) (K := Kc) 3 hspec0 him1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sz0_tendsto (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    Kc_ne_zero rangeCond_half (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Eventually.of_forall rpow_21_le_Kc)

end GridEnvelopeGenCheck

end Instances

end RBM.BA

end
