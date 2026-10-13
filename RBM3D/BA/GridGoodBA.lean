/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GridDriftBA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.KDecayBA
import RBM3D.Chain.AzumaProxyGen
import RBM3D.Chain.GridEnvelopeGen
import RBM3D.Chain.DecayGenTw
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.GreenLDE
import RBM3D.BA.CombesThomas
import RBM3D.BA.Ward
import RBM3D.BA.KBase

/-!
# The block Anderson readings of T4s2's outputs (BA-T row T5-BA (b), ticket T2492)

The BA instances of the pin `GridGoodNgL`, of the envelope of the grid drift, of the Azuma proxies and of the initial membership of
`GoodSetNg` (supervisor 2351 T4S2-C1).  No merged file is edited.

* §1 target 8: `baGridGood_of` (the four T2486 (a) facts as hypotheses of exact type) and the closure `baGridGood_holds`.
* §2 target 9: the envelope `baGridDrift_envelope` (a private copy of `gridDriftNg_envelope` taking the drift eventually, F1).
* §3 target 10: the Azuma and `Y` readings.
* §4 target 7: the initial membership `baGoodSetNg_init`.
* §5 compiled nonempty instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`.

Every helper is `private` or prefixed `GridGoodBA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private gridEnv_gridTime_le gridEnv_gridTime_nonneg from RBM3D.Induction.GridEnvelopeN

open private gdn_loopOf_eq from RBM3D.Induction.GridDriftN

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 8: `GridGoodNgL` at BA -/

section GridGood

/-- **Target 8, `baGridGood_of`** (the conditional form): T4s2a's pin `GridGoodNgL` at the BA family `(seqP ∘ withLam 0, BAFlow,
baStep2Mat, BAflowT0)`, through `gridGoodNgL_of`, with the four T2486 (a) facts as hypotheses of exact type
(`T2486_BAKcalDecay`, `T2486_BACarrierFacts` in its Amend 1 form, `T2486_BASEforLn`, `T2486_BAEtermDecay`).  `hFlow`, `hLaw`,
`hWard` are merged (`Step2EventsGenTw_baFlow`, `_baLaw`, `DecayGenTw_baWardPair`), `hW` is `baStep2Mat_walkForm`, `hSpec` is
inline (`κm = κ`, `EMn2BA_mF_data`). -/
theorem baGridGood_of (d : ℕ)
    (hKcal : 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (baFMz sz z))
    (hCarrier : (∀ (sz : Sizes d) (lam0 E : ℕ → ℝ),
        Step34Gen_LCompat (baStep2Mat sz lam0 E) (sz.seqHflowBA lam0) ∧ Step34Gen_KCompat (baStep2Mat sz lam0 E)) ∧
      (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
        StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z)))
    (hSE : ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
      STSEforLngL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
        (fun sz z => BAflowT0 sz z))
    (hEK : 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
      STDecayLoopUgL (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM (Sizes.seqP (sz.withLam 0)) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
            STegtg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω
              ⟨List.ofFn σ, List.ofFn a⟩) ∧
          (∀ l : ℕ, STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
            STksimLKg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω l
              ⟨List.ofFn σ, List.ofFn a⟩)) ∧
          STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
            STelklkg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω
              ⟨List.ofFn σ, List.ofFn a⟩) ∧
          STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
            STeeg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω σ
              (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i)))) :
    GridGoodNgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z) := by
  by_cases hd : 3 ≤ d
  · exact gridGoodNgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z)
      (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun _ _ => 0)
      (fun sz z n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))
      (hSE STAny) (Step2EventsGenTw_baFlow d)
      (fun sz κ ε 𝔠 𝔡 z hκ h => ⟨κ, hκ, fun n => (EMn2BA_mF_data sz h n).1, fun n t => rfl⟩)
      (fun sz κ ε 𝔠 𝔡 z hκ h => hCarrier.2 sz κ ε 𝔠 𝔡 z hκ h)
      (fun sz κ ε 𝔠 𝔡 z hκ h => baStep2Mat_walkForm sz _ _)
      (fun sz z => Step2EventsGenTw_baLaw sz _ _)
      (fun sz z => (hCarrier.1 sz _ _).1)
      (fun sz z => DecayGenTw_baWardPair sz _ _)
      (hKcal hd) (hEK hd)
  · intro hd'
    exact absurd hd' hd

/-- **Target 8, `baGridGood_holds`** (`T2492_BAGridGood`, every `d`): the closure.  The four facts of `baGridGood_of` are the merged
T2486 (a) results `baKcalDecay_holds`, `baStep2Mat_carrierFacts`, `baSEforLn_holds`, `baEtermDecaygL` (the `3 ≤ d` guard of the
pin is introduced first, T2486 1a row 13). -/
theorem baGridGood_holds (d : ℕ) :
    GridGoodNgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z) :=
  baGridGood_of d (baKcalDecay_holds d) (baStep2Mat_carrierFacts d) (baSEforLn_holds d) (baEtermDecaygL d)

end GridGood

/-! ## 2. Target 9: the envelope with the eventual drift (finding F1) -/

section Envelope

/-- **A private copy of `gridDriftNg_envelope`** (`Chain/GridEnvelopeGen.lean:67`) taking the one-step drift **eventually** in `n` (finding F1:
the BA drift classes hold past the window of `BAflow_lam0_window` only).  The drift is the per-index statement of `gridDriftNg_at`,
quantified over the loop length, the signs and the window bound `Bk`; the proof is the original one (the deterministic envelope
`exists_norm_KI_le_wing` at the first bad grid step) with the drift hypothesis entering through `filter_upwards`. -/
private theorem GridGoodBA_envelope_ev {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 2 ≤ k) (τK : ℝ) (hτK : 0 < τK) {s t : ℕ → ℝ} {K : ℕ → ℕ} (hsize : sz.SizeTendsto)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hη : ∀ (n : ℕ) (v : ℝ), 0 ≤ v → v < 1 → 0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hGD : ∀ᶠ n in atTop, ∀ j : ℕ, j < K n → ∀ k : ℕ, 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
      (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
        2 ≤ J.length → J.length ≤ k → ‖Cm.KI n w J‖ ≤ Bk) →
      ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin k → Zd d (sz.L n),
        ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
            (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
              STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
              STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
          stepErrNg Cm.toFlowFM n k (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n) Bk)
    (σ : Fin k → Bool) :
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
  filter_upwards [hP, hGD] with n hn hGDn
  refine ae_all_iff.2 fun j => ?_
  by_cases hj : j < K n
  · have hη' : 0 < Cm.eta n (gridTime s t K n (j + 1)) :=
      (hη n _ (gridEnv_gridTime_nonneg (hs0 n) (hst n) _) (hv1 n j hj)).1
    have hBk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη'.le) _)
    have h := hGDn j hj k hk σ _ hBk (hn j hj)
    exact h.mono fun ω hω _ => hω
  · exact Eventually.of_forall fun ω h => absurd h hj

/-- **Target 9, `baGridDrift_envelope`**: the conclusion of `gridDriftNg_envelope` at the BA family along the flow, through the private
eventual copy (finding F1).  Inputs: `hη` from target 1 (b) (`κ ≤ Im m ≤ 1`, so `0 < η ≤ 1 - v`), `hKK` from target 2 (definitional),
`hGD` from target 6 (`baGridDrift_ev`), `STKboundgL` (registered; input (c)); the window `t n ≤ BAflowT0 sz z n < 1`. -/
theorem baGridDrift_envelope {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (hL : StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z))
    (hKb : STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)))
    (k : ℕ) (hk : 2 ≤ k) (τK : ℝ) (hτK : 0 < τK) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hK0 : ∀ n, K n ≠ 0) (σ : Fin k → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp, ∀ j, j < K n → ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n j)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n j)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n j)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        stepErrNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n k (gridTime s t K n j)
          (gridTime s t K n (j + 1)) (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).eta n (gridTime s t K n (j + 1)))⁻¹ ^ k) := by
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  refine GridGoodBA_envelope_ev (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) k hk τK hτK
    hflow.1.2.2.1 hKb (fun n w k σ a => rfl) ?_ hs0 hst ht1 hK0 (baGridDrift_ev sz κ ε 𝔠 𝔡 z hκ hflow hL s t K hs0 hst ht1 hK0) σ
  intro n v hv0 hv1
  have hm := EMn2BA_mF_data sz hflow n
  have hη : (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).eta n v = (1 - v) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl
  rw [hη]
  refine ⟨mul_pos (by linarith) (by linarith [hm.1]), ?_⟩
  nlinarith [hm.2]

end Envelope

/-! ## 3. Target 10: the Azuma and `Y` readings at BA -/

section Azuma

variable {d : ℕ}

/-- **Target 10, `baAzumaSubG`**: the Azuma sub-Gaussian pin at the BA carrier (`azumaSubGNg` with `baStep2Mat_walkForm`; the
instance argument is `baStep2Mat_isProb`), every `lam0, E, s, t, K`; the walk coupling is `0`. -/
theorem baAzumaSubG (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    AzumaSubGNg (baStep2Mat sz lam0 E) 0 s t K :=
  azumaSubGNg (baStep2Mat sz lam0 E) (baStep2Mat_walkForm sz lam0 E) s t K

/-- **Target 10, `baYMoments`**: the `Y` moments at the BA carrier along the flow (`yMomentsNg`; `GridRepTailGen_Ker` at every index
is `gridRepTailGen_ker_BA` under `BAflow_real`). -/
theorem baYMoments (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (hL : StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z))
    (κm τ' : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    YMomentsNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) κm τ' s t K :=
  yMomentsNg hL (baStep2Mat_walkForm sz _ _)
    (fun n => gridRepTailGen_ker_BA sz _ _ n hκ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)) κm τ' s t K

/-- **Target 10, `baAzumaProxy_subG_goodExit`**: `azumaProxy_subG_goodExitg` at the BA carrier along the flow.  The pin `AzumaSubGNg` is
`baAzumaSubG`, the quadratic variation is `baQVPropagated` (target 6), the walk is `baStep2Mat_walkForm`, the kernel class is
`gridRepTailGen_ker_BA`; what remains is the majorant `hQ` of `Δ · k · qvFormNg` on the good set (input (d), `U3s2-U3s3`). -/
theorem baAzumaProxy_subG_goodExit (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (hL : StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z))
    {s v : ℕ → ℝ} {K : ℕ → ℕ} (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (Q : NNReal)
    (hQ : ∀ M, GoodSetNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' M →
      M.IsHermitian →
      gridStep s v K n * ((k : ℝ) * qvFormNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n
        (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) σ (gridTime s v K n)
      (goodExitTauNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s v K k Γ Λ Φ τ' D' n)
      (fun j ω => ZvecNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s v K n j σ ω) m a j Q :=
  azumaProxy_subG_goodExitg (baAzumaSubG sz _ _ s v K) hL (baStep2Mat_walkForm sz _ _) (baQVPropagated sz _ _ hL) hs0 hsv hv1 n k
    (gridRepTailGen_ker_BA sz _ _ n hκ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)) hk σ Γ Λ Φ τ' D' m hm a j hj Q hQ

end Azuma

/-! ## 4. Target 7: the initial membership `baGoodSetNg_init`

At `s n = 0` the grid state is `H_0 = g₀ Ψ` (`azumaProxy_Hpath_zerog`) and `u_0 = 0`, `z_0 = E + m`, so `G_0 = M = M^{(B)} ⊗ I` and the
loops are the initial loops: `𝓛_0 = BAMLoop = 𝒦_0` on every well-formed loop (`BAMLoop_trace`, the initial clause of `BAKsol_isKLoopS`,
`M_aa = m`).  Every clause of `GoodSetNg` that carries `𝓛 - 𝒦` has the value `0`.  The clauses that carry `𝓛` alone are bounded
entrywise: `‖M^{(σ)}_{xy}‖ ≤ 1` (Ward) and `‖M^{(σ)}_{xy}‖ ≤ c⁻¹ e^{-c|x-y|}` (Combes-Thomas), the `ee` clause once through
`Σ_b ‖M_{xb}‖ ‖M_{yb}‖ ≤ 1` (Cauchy-Schwarz and Ward). -/

section Init

variable {d : ℕ}

/-! ### 4.1 Lists and products -/

/-- `‖∏ f‖ ≤ ‖f p‖ ‖f q‖` for `‖f i‖ ≤ 1`, two distinct indices. -/
private theorem GridGoodBA_norm_prod_two (f : ℕ → ℂ) (n : ℕ) (h : ∀ i < n, ‖f i‖ ≤ 1) {p q : ℕ} (hp : p < n)
    (hq : q < n) (hpq : p ≠ q) : ‖∏ i ∈ Finset.range n, f i‖ ≤ ‖f p‖ * ‖f q‖ := by
  rw [norm_prod]
  have hsub : ({p, q} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  rw [← Finset.prod_sdiff hsub, Finset.prod_pair hpq]
  have h1 : ∏ i ∈ Finset.range n \ {p, q}, ‖f i‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
      (fun i hi => h i (by simpa using (Finset.mem_sdiff.1 hi).1))
  calc _ ≤ 1 * (‖f p‖ * ‖f q‖) := by gcongr
    _ = _ := one_mul _

/-- `‖∏ f‖ ≤ ‖f p‖` for `‖f i‖ ≤ 1`. -/
private theorem GridGoodBA_norm_prod_one (f : ℕ → ℂ) (n : ℕ) (h : ∀ i < n, ‖f i‖ ≤ 1) {p : ℕ} (hp : p < n) :
    ‖∏ i ∈ Finset.range n, f i‖ ≤ ‖f p‖ := by
  rw [norm_prod]
  have hsub : ({p} : Finset ℕ) ⊆ Finset.range n := by simpa using hp
  rw [← Finset.prod_sdiff hsub, Finset.prod_singleton]
  have h1 : ∏ i ∈ Finset.range n \ {p}, ‖f i‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
      (fun i hi => h i (by simpa using (Finset.mem_sdiff.1 hi).1))
  calc _ ≤ 1 * ‖f p‖ := by gcongr
    _ = _ := one_mul _

/-- **The edge product of `BAMLoop`**: `BAMLoop M I = (W^d)^{-(n-1)} ∏_{i<n} M(σ_i)(a_{i-1}, a_i)` (cyclic, `a_{-1} = a_{n-1}`). -/
private theorem GridGoodBA_BAMLoop_eq {L W : ℕ} [NeZero L] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L))
    (hI : I.WF) :
    BAMLoop d L W M I = (((W : ℂ) ^ d)⁻¹) ^ (I.length - 1) *
      ∏ i ∈ Finset.range I.length,
        M (I.σ.getD i false) (I.a.getD ((i + (I.length - 1)) % I.length) 0) (I.a.getD i 0) := by
  unfold BAMLoop
  congr 1
  have hσ : I.σ.length = I.length := hI
  have hlen : I.a.length = I.length := rfl
  change ((I.σ.zip ((I.a.rotate (I.length - 1)).zip I.a)).map fun p => M p.1 p.2.1 p.2.2).prod = _
  have : (I.σ.zip ((I.a.rotate (I.length - 1)).zip I.a)).map (fun p => M p.1 p.2.1 p.2.2) =
      (List.range I.length).map (fun i =>
        M (I.σ.getD i false) (I.a.getD ((i + (I.length - 1)) % I.length) 0) (I.a.getD i 0)) := by
    refine List.ext_getElem (by simp [hσ, hlen]) fun i h1 h2 => ?_
    have hi : i < I.length := by simpa [hσ, hlen] using h2
    have hn : 0 < I.length := by omega
    simp only [List.getElem_map, List.getElem_zip, List.getElem_rotate, List.getElem_range]
    rw [List.getD_eq_getElem I.σ false (show i < I.σ.length by omega),
      List.getD_eq_getElem I.a 0 (show i < I.a.length by omega),
      List.getD_eq_getElem I.a 0 (show (i + (I.length - 1)) % I.length < I.a.length from Nat.mod_lt _ hn)]
    simp [hlen]
  rw [this]
  rfl

/-- A chain of labels moves at most the sum of its steps (`zdistD` is a norm). -/
private theorem GridGoodBA_chain {L : ℕ} [NeZero L] (f : ℕ → Zd d L) (n : ℕ) (B : ℝ)
    (hB : ∀ i, 1 ≤ i → i < n → (zdistD d L (f (i - 1) - f i) : ℝ) ≤ B) :
    ∀ q p : ℕ, p ≤ q → q < n → (zdistD d L (f p - f q) : ℝ) ≤ ((q : ℝ) - p) * B := by
  intro q
  induction q with
  | zero =>
    intro p hp _
    have : p = 0 := by omega
    subst this
    simp
  | succ q ih =>
    intro p hp hq
    rcases Nat.lt_or_ge q p with h | h
    · have : p = q + 1 := by omega
      subst this
      simp
    · have h1 := ih p h (by omega)
      have h2 := hB (q + 1) (by omega) hq
      simp only [Nat.add_sub_cancel] at h2
      have h3 : zdistD d L (f p - f (q + 1)) ≤ zdistD d L (f p - f q) + zdistD d L (f q - f (q + 1)) := by
        have := zdistD_add_le d L (f p - f q) (f q - f (q + 1))
        rwa [sub_add_sub_cancel] at this
      have h3' : (zdistD d L (f p - f (q + 1)) : ℝ) ≤ (zdistD d L (f p - f q) : ℝ) + (zdistD d L (f q - f (q + 1)) : ℝ) := by
        exact_mod_cast h3
      push_cast
      linarith

/-- **A far pair on a cyclic list forces a far edge**: if two labels of `al` (length `n`) are `R` apart then some cyclic edge is at
least `R / n` long. -/
private theorem GridGoodBA_far_edge {L : ℕ} [NeZero L] (al : List (Zd d L)) (hn : 0 < al.length) {u v : Zd d L}
    (hu : u ∈ al) (hv : v ∈ al) (R : ℝ) (hR : R ≤ (zdistD d L (u - v) : ℝ)) :
    ∃ i < al.length, R ≤ (al.length : ℝ) * (zdistD d L (al.getD ((i + (al.length - 1)) % al.length) 0 - al.getD i 0) : ℝ) := by
  by_cases hR0 : R ≤ 0
  · refine ⟨0, hn, hR0.trans ?_⟩
    positivity
  push Not at hR0
  by_contra hcon
  push Not at hcon
  set n := al.length with hnn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℕ → Zd d L := fun i => al.getD i 0 with hf
  have hB : ∀ i, 1 ≤ i → i < n → (zdistD d L (f (i - 1) - f i) : ℝ) ≤ R / n := by
    intro i hi1 hin
    have h := hcon i hin
    have hmod : (i + (n - 1)) % n = i - 1 := by
      have : i + (n - 1) = (i - 1) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at h
    rw [le_div_iff₀ hnR]
    nlinarith
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hu
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.1 hv
  have hfp : al[p] = f p := (List.getD_eq_getElem al 0 hp).symm
  have hfq : al[q] = f q := (List.getD_eq_getElem al 0 hq).symm
  rw [hfp, hfq] at hR
  have hcalc : ∀ p q : ℕ, p < n → q < n → (zdistD d L (f p - f q) : ℝ) < R := by
    intro p q hp hq
    rcases le_total p q with h | h
    · have := GridGoodBA_chain f n (R / n) hB q p h hq
      have h2 : ((q : ℝ) - p) * (R / n) < R := by
        have h3 : ((q : ℝ) - p) < n := by
          have : (q : ℝ) < n := by exact_mod_cast hq
          have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
          linarith
        calc ((q : ℝ) - p) * (R / n) < n * (R / n) := by gcongr
          _ = R := by field_simp
      linarith
    · have := GridGoodBA_chain f n (R / n) hB p q h hp
      have h2 : ((p : ℝ) - q) * (R / n) < R := by
        have h3 : ((p : ℝ) - q) < n := by
          have : (p : ℝ) < n := by exact_mod_cast hp
          have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
          linarith
        calc ((p : ℝ) - q) * (R / n) < n * (R / n) := by gcongr
          _ = R := by field_simp
      have h4 : zdistD d L (f p - f q) = zdistD d L (f q - f p) := by
        rw [← zdistD_neg d L (f p - f q), neg_sub]
      rw [h4]
      linarith
  have := hcalc p q hp hq
  linarith

/-! ### 4.2 The entries of `M^{(σ)}` and the bounds on `BAMLoop` -/

section Entries

variable {L W : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}

/-- `‖M^{(B)}_{xy}‖ ≤ 1` (Ward: `Σ_b ‖M_{xb}‖² = 1`). -/
private theorem GridGoodBA_norm_BAMB_le_one (hr : BAReal d L g κ E m) (x y : Zd d L) :
    ‖BAMB d L g (E : ℂ) m x y‖ ≤ 1 := by
  have hrow := BAMB_row_sq_real d L g E m hr.1 x
  have hle : ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (f := fun b => ‖BAMB d L g (E : ℂ) m x b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ y)
  nlinarith [norm_nonneg (BAMB d L g (E : ℂ) m x y)]

/-- The charges `σ = ±` change no modulus: `M(-) = (M^{(B)})^*` and `M^{(B)}` is symmetric. -/
private theorem GridGoodBA_norm_Ms (σ : Bool) (x y : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y‖ = ‖BAMB d L g (E : ℂ) m x y‖ := by
  cases σ
  · simp [BAMsigma, Matrix.conjTranspose_apply, BAMB_symm d L g (E : ℂ) m x y]
  · simp [BAMsigma]

/-- `Σ_b ‖M_{xb}‖ ‖M_{yb}‖ ≤ 1` (Cauchy-Schwarz and Ward). -/
private theorem GridGoodBA_cs (hr : BAReal d L g κ E m) (x y : Zd d L) :
    ∑ b : Zd d L, ‖BAMB d L g (E : ℂ) m x b‖ * ‖BAMB d L g (E : ℂ) m y b‖ ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖BAMB d L g (E : ℂ) m x b‖)
    (fun b => ‖BAMB d L g (E : ℂ) m y b‖)
  rw [BAMB_row_sq_real d L g E m hr.1 x, BAMB_row_sq_real d L g E m hr.1 y] at h
  nlinarith [h, Finset.sum_nonneg (fun b (_ : b ∈ (Finset.univ : Finset (Zd d L))) =>
    mul_nonneg (norm_nonneg (BAMB d L g (E : ℂ) m x b)) (norm_nonneg (BAMB d L g (E : ℂ) m y b)))]

/-- The Combes-Thomas decay of the entries of `M^{(σ)}` (`BAMB_decay_large`, `Λ` with `0 < g ≤ Λ`). -/
private theorem GridGoodBA_decay (hL : 3 ≤ L) (hd : 0 < d) (Λ : ℝ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (σ : Bool) (x y : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y‖ ≤
      (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (x - y) : ℝ)) := by
  rw [GridGoodBA_norm_Ms]
  exact BAMB_decay_large d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr x y

/-- The edge of `BAMLoop` at the position `i`. -/
private def GridGoodBA_edge (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) (i : ℕ) : ℂ :=
  M (I.σ.getD i false) (I.a.getD ((i + (I.length - 1)) % I.length) 0) (I.a.getD i 0)

/-- Every edge of `BAMLoop` at `M^{(σ)}` has modulus at most `1`. -/
private theorem GridGoodBA_edge_le_one (hr : BAReal d L g κ E m) (I : LoopIdx (Zd d L)) (i : ℕ) :
    ‖GridGoodBA_edge (BAMsigma d L (BAMB d L g (E : ℂ) m)) I i‖ ≤ 1 := by
  unfold GridGoodBA_edge
  rw [GridGoodBA_norm_Ms]
  exact GridGoodBA_norm_BAMB_le_one hr _ _

/-- The real prefactor of `BAMLoop`. -/
private theorem GridGoodBA_norm_pref (hW : 0 < W) (n : ℕ) : ‖(((W : ℂ) ^ d)⁻¹) ^ n‖ = (((W : ℝ) ^ d)⁻¹) ^ n := by
  simp

/-- **One edge of a loop**: `‖BAMLoop‖ ≤ W^{-(n-1)d} ‖edge_p‖` (all edges have modulus at most `1`). -/
private theorem GridGoodBA_BAMLoop_one (hr : BAReal d L g κ E m) (hW : 0 < W) (I : LoopIdx (Zd d L)) (hI : I.WF)
    {p : ℕ} (hp : p < I.length) :
    ‖BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) I‖ ≤
      (((W : ℝ) ^ d)⁻¹) ^ (I.length - 1) *
        ‖GridGoodBA_edge (BAMsigma d L (BAMB d L g (E : ℂ) m)) I p‖ := by
  rw [GridGoodBA_BAMLoop_eq _ I hI, norm_mul, GridGoodBA_norm_pref hW]
  exact mul_le_mul_of_nonneg_left (GridGoodBA_norm_prod_one (GridGoodBA_edge (BAMsigma d L (BAMB d L g (E : ℂ) m)) I)
    I.length (fun i _ => GridGoodBA_edge_le_one hr I i) hp) (by positivity)

/-- **Two edges of a loop**: `‖BAMLoop‖ ≤ W^{-(n-1)d} ‖edge_p‖ ‖edge_q‖`, `p ≠ q`. -/
private theorem GridGoodBA_BAMLoop_two (hr : BAReal d L g κ E m) (hW : 0 < W) (I : LoopIdx (Zd d L)) (hI : I.WF)
    {p q : ℕ} (hp : p < I.length) (hq : q < I.length) (hpq : p ≠ q) :
    ‖BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) I‖ ≤
      (((W : ℝ) ^ d)⁻¹) ^ (I.length - 1) *
        (‖GridGoodBA_edge (BAMsigma d L (BAMB d L g (E : ℂ) m)) I p‖ *
          ‖GridGoodBA_edge (BAMsigma d L (BAMB d L g (E : ℂ) m)) I q‖) := by
  rw [GridGoodBA_BAMLoop_eq _ I hI, norm_mul, GridGoodBA_norm_pref hW]
  exact mul_le_mul_of_nonneg_left (GridGoodBA_norm_prod_two (GridGoodBA_edge (BAMsigma d L (BAMB d L g (E : ℂ) m)) I)
    I.length (fun i _ => GridGoodBA_edge_le_one hr I i) hp hq hpq) (by positivity)

/-- **A far pair of labels makes a loop small**: if two labels of `I` are `R` apart (`ℓ¹`), then
`‖BAMLoop‖ ≤ W^{-(n-1)d} c⁻¹ e^{-c R / n}`. -/
private theorem GridGoodBA_BAMLoop_far (hL : 3 ≤ L) (hd : 0 < d) (Λ : ℝ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hr : BAReal d L g κ E m) (hW : 0 < W) (I : LoopIdx (Zd d L)) (hI : I.WF) (hn : 0 < I.length)
    {u v : Zd d L} (hu : u ∈ I.a) (hv : v ∈ I.a) (R : ℝ) (hR : R ≤ (zdistD d L (u - v) : ℝ)) :
    ‖BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) I‖ ≤
      (((W : ℝ) ^ d)⁻¹) ^ (I.length - 1) *
        ((BAct_rate d Λ κ)⁻¹ * Real.exp (-(BAct_rate d Λ κ * R / (I.length : ℝ)))) := by
  obtain ⟨i, hi, hRi⟩ := GridGoodBA_far_edge I.a hn hu hv R hR
  refine (GridGoodBA_BAMLoop_one hr hW I hI hi).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hc := BAct_rate_pos d Λ κ hd hΛ hκ
  unfold GridGoodBA_edge
  refine (GridGoodBA_decay hL hd Λ hΛ hg hgΛ hκ hr _ _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc.le)
  apply Real.exp_le_exp.2
  have hnR : (0 : ℝ) < (I.length : ℝ) := by exact_mod_cast hn
  have hRi' : R ≤ (I.length : ℝ) * (zdistD d L (I.a.getD ((i + (I.length - 1)) % I.length) 0 - I.a.getD i 0) : ℝ) := hRi
  have h1 : R / (I.length : ℝ) ≤ (zdistD d L (I.a.getD ((i + (I.length - 1)) % I.length) 0 - I.a.getD i 0) : ℝ) := by
    rw [div_le_iff₀ hnR]
    linarith [mul_comm (I.length : ℝ) (zdistD d L (I.a.getD ((i + (I.length - 1)) % I.length) 0 - I.a.getD i 0) : ℝ)]
  rw [neg_mul, neg_le_neg_iff, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h1 hc.le

end Entries

/-! ### 4.3 The initial loops: `𝓛_0 = BAMLoop = 𝒦_0` -/

section InitLoops

open scoped Kronecker

variable (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- **`G_0 = M`**: at `H = g₀ Ψ`, `z_0 = E + m`, the signed Green factors are `M(σ) ⊗ I_{W^d}` (`BAMres_fine_kron`, `ST_Gres_false`). -/
private theorem GridGoodBA_Gres_init (hm : 0 < (BAmF sz lam0 E n).im) (σ : Bool) :
    Gres (blockMat d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)))
        (ztOf (BAmF sz lam0 E n) (E n) 0) σ =
      (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ) ⊗ₖ
        (1 : Matrix (Fin (sz.W n ^ d)) (Fin (sz.W n ^ d)) ℂ) := by
  have hw : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by simpa using hm.ne'
  have hk := BAMres_fine_kron d (sz.L n) (sz.W n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) hw
  have hz0 : ztOf (BAmF sz lam0 E n) (E n) 0 = (E n : ℂ) + BAmF sz lam0 E n := by
    simp [ztOf]
  have htrue : Gres (blockMat d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)))
      (ztOf (BAmF sz lam0 E n) (E n) 0) true =
      BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) ⊗ₖ
        (1 : Matrix (Fin (sz.W n ^ d)) (Fin (sz.W n ^ d)) ℂ) := by
    unfold Gres
    simp only [↓reduceIte]
    rw [hz0, ← Matrix.nonsing_inv_eq_ringInverse]
    have e1 : blockMat d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) -
        ((E n : ℂ) + BAmF sz lam0 E n) • (1 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) =
        (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) -
          ((E n : ℂ) + BAmF sz lam0 E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)).submatrix
          (splitEquiv d (sz.L n) (sz.W n)).symm (splitEquiv d (sz.L n) (sz.W n)).symm := by
      unfold blockMat
      simp only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply, Matrix.submatrix_one_equiv]
    rw [e1, Matrix.inv_submatrix_equiv, Matrix.nonsing_inv_eq_ringInverse]
    change (Mres (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (BAmF sz lam0 E n)).submatrix _ _ = _
    rw [hk, Matrix.submatrix_submatrix]
    simp
  cases σ
  · have hH : (blockMat d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))).IsHermitian := by
      unfold blockMat
      refine Matrix.IsHermitian.submatrix ?_ _
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
        show star ((lam0 n : ℝ) : ℂ) = ((lam0 n : ℝ) : ℂ) from Complex.conj_ofReal _]
    rw [ST_Gres_false hH, htrue, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    simp [BAMsigma]
  · rw [htrue]
    simp [BAMsigma]

/-- **`𝓛_0 = BAMLoop`** on the loops `(σ, a)` of length `j ≥ 1` (`loopFine`, `BAMLoop_trace`). -/
private theorem GridGoodBA_loopFine_init (hm : 0 < (BAmF sz lam0 E n).im) {j : ℕ} (hj : 1 ≤ j) (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))
        (ztOf (BAmF sz lam0 E n) (E n) 0) σ a =
      BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
        (loopOf σ a) := by
  rw [BAMLoop_trace d (sz.L n) (sz.W n) _ hj σ a]
  unfold loopFine loopM
  simp only [GridGoodBA_Gres_init sz lam0 E n hm]

/-- The list-based loop values of the carrier at `u = 0`, `H = g₀ Ψ`: `𝓛_{0,I} = BAMLoop` for a well-formed `I` of length `≥ 1`. -/
private theorem GridGoodBA_LIM_init (hm : 0 < (BAmF sz lam0 E n).im) (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF)
    (h1 : 1 ≤ I.length) :
    (baStep2Mat sz lam0 E).LIM n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) I =
      BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n))) I := by
  have hI' := gdn_loopOf_eq I hI
  rw [← hI']
  have := GridGoodBA_loopFine_init sz lam0 E n hm h1 (fun i : Fin I.length => I.σ.getD i false)
    (fun i : Fin I.length => I.a.getD i (0 : Zd d (sz.L n)))
  rw [← this]
  unfold loopFine
  rw [loopM_eq_loopL]
  rfl

/-- `BAMLoop` of a one-loop is `m(σ)`: `M(σ)_{aa} = m` or `m̄` (`BAMB_diag_eq`). -/
private theorem GridGoodBA_BAMLoop_one_loop {L : ℕ} [NeZero L] {W : ℕ} {g : ℝ} {z m : ℂ} (h : BASelf d L g z m) (s : Bool)
    (a : Zd d L) :
    BAMLoop d L W (BAMsigma d L (BAMB d L g z m)) ⟨[s], [a]⟩ = PropSpin m s := by
  unfold BAMLoop
  simp only [LoopIdx.length, List.length_singleton, Nat.sub_self, pow_zero, one_mul, List.rotate_zero, List.zip_cons_cons,
    List.zip_nil_right, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  cases s
  · simp [BAMsigma, PropSpin, Matrix.conjTranspose_apply, BAMB_diag_eq d L g z m h a]
  · simp [BAMsigma, PropSpin, BAMB_diag_eq d L g z m h a]

/-- **`𝒦_0 = BAMLoop`** at `u = 0` for the loops of length `≥ 1` (`BAKsol_isKLoopS`: the initial clause for length `≥ 2`, the one-loop
clause for length `1`), at an index with `0 < g₀`. -/
private theorem GridGoodBA_KI_init {κ : ℝ} (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF)
    (h1 : 1 ≤ I.length) :
    (baStep2Mat sz lam0 E).KI n 0 I =
      BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n))) I := by
  have hK := BAKsol_isKLoopS (baKsolve d) hg hκ (sz.three_le_L n) hg le_rfl hr (W := sz.W n)
  change BAKsol d (sz.L n) (sz.W n) _ _ 0 I = _
  rcases Nat.lt_or_ge 1 I.length with h2 | h2
  · exact hK.2.1 I hI h2
  · obtain ⟨σ', a'⟩ := I
    have hl : σ'.length = 1 := hI.trans (le_antisymm h2 h1)
    have hl' : a'.length = 1 := le_antisymm h2 h1
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hl
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl'
    rw [hK.2.2 0 ⟨le_rfl, one_pos⟩ s a, GridGoodBA_BAMLoop_one_loop hr.1 s a]

/-- **`𝓛_0 - 𝒦_0 = 0`** on every well-formed loop of length `≥ 1`. -/
private theorem GridGoodBA_LIM_sub_KI {κ : ℝ} (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF)
    (h1 : 1 ≤ I.length) :
    (baStep2Mat sz lam0 E).LIM n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) I -
      (baStep2Mat sz lam0 E).KI n 0 I = 0 := by
  rw [GridGoodBA_LIM_init sz lam0 E n (lt_of_lt_of_le hκ hr.2) I hI h1, GridGoodBA_KI_init sz lam0 E n hκ hg hr I hI h1, sub_self]

end InitLoops

/-! ### 4.4 The pair form `𝓔⊗𝓔` at the initial state -/

section InitEE

variable {L W : ℕ} [NeZero L]

/-- The label list of the `ee`-loop (`STeeLoop`, `Induction/Step34Pins.lean:152`) is `L₁ ++ b' :: (L₂ ++ [b])`. -/
private theorem GridGoodBA_ee_a_list (σ : List Bool) (a a' : List (Zd d L)) (c : ℕ) (b b' : Zd d L) :
    (STeeLoop σ a a' c b b').a = ((a.drop (c - 1) ++ a.take (c - 1)) ++
      b' :: (((a'.take (c - 1)).reverse ++ (a'.drop (c - 1)).reverse) ++ [b])) := by
  simp [STeeLoop, List.append_assoc]

/-- The label before the cut `b'` of the `ee`-loop, independent of `b, b'`. -/
private def GridGoodBA_eeX {k : ℕ} (a : Fin k → Zd d L) (c : ℕ) : Zd d L :=
  ((List.ofFn a).drop (c - 1) ++ (List.ofFn a).take (c - 1)).getD (k - 1) 0

/-- The label after the cut `b'` of the `ee`-loop, independent of `b, b'`. -/
private def GridGoodBA_eeY {k : ℕ} (a' : Fin k → Zd d L) (c : ℕ) : Zd d L :=
  (((List.ofFn a').take (c - 1)).reverse ++ ((List.ofFn a').drop (c - 1)).reverse).getD 0 0

/-- **Two edges of the `ee`-loop at `b = b'`**: the edges at the cut `b'` are `M_{xb}` and `M_{by}`; the rest is bounded by `1`. -/
private theorem GridGoodBA_ee_loop_two {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (hW : 0 < W) {k : ℕ} (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a a' : Fin k → Zd d L) {c : ℕ} (hc1 : 1 ≤ c) (hck : c ≤ k) (β : Zd d L) :
    ‖BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β)‖ ≤
      (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 1) *
        (‖BAMB d L g (E : ℂ) m (GridGoodBA_eeX a c) β‖ * ‖BAMB d L g (E : ℂ) m (GridGoodBA_eeY a' c) β‖) := by
  set I := STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β with hIdef
  have hwf : I.WF := RBM.Ind.eeLoop_WF (List.ofFn σ) (List.ofFn a) (List.ofFn a') hc1 (by simpa using hck) (by simp) (by simp) β β
  have hlen : I.length = 2 * k + 2 := by
    have := RBM.Ind.length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := c) (by simp; omega) (by simp) β β
    simpa using this
  have hlist := GridGoodBA_ee_a_list (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β
  have hL1 : ((List.ofFn a).drop (c - 1) ++ (List.ofFn a).take (c - 1)).length = k := by
    simp only [List.length_append, List.length_drop, List.length_take, List.length_ofFn]
    omega
  have hL2 : 0 < (((List.ofFn a').take (c - 1)).reverse ++ ((List.ofFn a').drop (c - 1)).reverse).length := by
    simp only [List.length_append, List.length_reverse, List.length_drop, List.length_take, List.length_ofFn]
    omega
  have h2 := GridGoodBA_BAMLoop_two hr hW I hwf (p := k) (q := k + 1) (by omega) (by omega) (by omega)
  refine h2.trans ?_
  rw [hlen, show 2 * k + 2 - 1 = 2 * k + 1 by omega]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold GridGoodBA_edge
  rw [GridGoodBA_norm_Ms, GridGoodBA_norm_Ms, hlen]
  have hmod1 : (k + (2 * k + 2 - 1)) % (2 * k + 2) = k - 1 := by
    rw [show k + (2 * k + 2 - 1) = (k - 1) + (2 * k + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hmod2 : (k + 1 + (2 * k + 2 - 1)) % (2 * k + 2) = k := by
    rw [show k + 1 + (2 * k + 2 - 1) = k + (2 * k + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hmod1, hmod2, hlist]
  have h3 : ∀ z : Zd d L, ((((List.ofFn a).drop (c - 1) ++ (List.ofFn a).take (c - 1)) ++
      β :: (((List.ofFn a').take (c - 1)).reverse ++ ((List.ofFn a').drop (c - 1)).reverse ++ [β]))).getD (k - 1) z =
      ((List.ofFn a).drop (c - 1) ++ (List.ofFn a).take (c - 1)).getD (k - 1) z := fun z =>
    List.getD_append _ _ _ _ (by omega)
  have h4 : (((List.ofFn a).drop (c - 1) ++ (List.ofFn a).take (c - 1)) ++
      β :: (((List.ofFn a').take (c - 1)).reverse ++ ((List.ofFn a').drop (c - 1)).reverse ++ [β])).getD k 0 = β := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hL1]
  have h5 : (((List.ofFn a).drop (c - 1) ++ (List.ofFn a).take (c - 1)) ++
      β :: (((List.ofFn a').take (c - 1)).reverse ++ ((List.ofFn a').drop (c - 1)).reverse ++ [β])).getD (k + 1) 0 =
      GridGoodBA_eeY a' c := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hL1, show k + 1 - k = 1 by omega, List.getD_cons_succ]
    unfold GridGoodBA_eeY
    rw [List.getD_append _ _ _ _ (by omega)]
  rw [show (List.ofFn a).drop (c - 1) ++ (List.ofFn a).take (c - 1) ++
      β :: (((List.ofFn a').take (c - 1)).reverse ++ ((List.ofFn a').drop (c - 1)).reverse ++ [β]) =
      ((List.ofFn a).drop (c - 1) ++ (List.ofFn a).take (c - 1)) ++
      β :: (((List.ofFn a').take (c - 1)).reverse ++ ((List.ofFn a').drop (c - 1)).reverse ++ [β]) from rfl]
  rw [h3, h4, h5]
  rw [BAMB_symm d L g (E : ℂ) m β (GridGoodBA_eeY a' c)]
  exact le_rfl

end InitEE

section InitEESum

variable (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- **`𝓔⊗𝓔` at the initial state is a sum of initial loops** (`S = 1`: only `b = b'` survives; `𝓛_0 = BAMLoop`). -/
private theorem GridGoodBA_STeeMg_init_le (hm : 0 < (BAmF sz lam0 E n).im) {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool)
    (a a' : Fin k → Zd d (sz.L n)) :
    ‖STeeMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) σ a a'‖ ≤
      ((sz.W n : ℝ) ^ d) * ∑ c ∈ Finset.Icc 1 k, ∑ β : Zd d (sz.L n),
        ‖BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
          (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β)‖ := by
  unfold STeeMg
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
  rw [Finset.mem_Icc] at hc
  have hS : (baStep2Mat sz lam0 E).S n = 1 := rfl
  rw [hS]
  have hsum : ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) b b' *
      STLIMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))
        (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c b b') =
      ∑ β : Zd d (sz.L n), STLIMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))
        (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  have hwf : (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β).WF :=
    RBM.Ind.eeLoop_WF (List.ofFn σ) (List.ofFn a) (List.ofFn a') hc.1 (by simpa using hc.2) (by simp) (by simp) β β
  have hlen : (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β).length = 2 * k + 2 := by
    have := RBM.Ind.length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := c) (by simp; omega) (by simp) β β
    simpa using this
  have := GridGoodBA_LIM_init sz lam0 E n hm _ hwf (by omega)
  change ‖(baStep2Mat sz lam0 E).LIM n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) _‖ ≤ _
  rw [this]

end InitEESum

section InitBounds

variable (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- Two labels of a vector at distance `≥ R` (`ℓ¹`) from the diameter `diam_∞ a ≥ R`. -/
private theorem GridGoodBA_diam_pair {L j : ℕ} [NeZero L] (hj : 1 ≤ j) (a : Fin j → Zd d L) (R : ℝ)
    (hR : R ≤ (STdiamInf a : ℝ)) : ∃ p q : Fin j, R ≤ (zdistD d L (a p - a q) : ℝ) := by
  have hne : (Finset.univ : Finset (Fin j × Fin j)).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_univ _⟩
  obtain ⟨pq, -, hpq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin j × Fin j)) hne
    (fun p : Fin j × Fin j => zdistInf d L (a p.1 - a p.2))
  refine ⟨pq.1, pq.2, ?_⟩
  have h1 : STdiamInf a = zdistInf d L (a pq.1 - a pq.2) := hpq
  rw [h1] at hR
  exact hR.trans (by exact_mod_cast zdistInf_le_zdistD d L _)

/-- `exp(-c R / j) ≤ exp(-c R / Q)` for `1 ≤ j ≤ Q`, `c R ≥ 0`. -/
private theorem GridGoodBA_exp_mono {c R : ℝ} (hcR : 0 ≤ c * R) {j Q : ℕ} (hj : 1 ≤ j) (hjQ : j ≤ Q) :
    Real.exp (-(c * R / (j : ℝ))) ≤ Real.exp (-(c * R / (Q : ℝ))) := by
  apply Real.exp_le_exp.2
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have : c * R / (Q : ℝ) ≤ c * R / (j : ℝ) :=
    div_le_div_of_nonneg_left hcR hj0 (by exact_mod_cast hjQ)
  linarith

/-- **The `ee` level (D4)**: `‖𝓔⊗𝓔‖ ≤ k W^{-2kd}` at the initial state (Ward and Cauchy-Schwarz; no decay is used). -/
private theorem GridGoodBA_ee_level {κ : ℝ} (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n))
    {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)) :
    ‖STeeMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) σ a a'‖ ≤
      (k : ℝ) * (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k) := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hW : 0 < sz.W n := sz.W_pos n
  refine (GridGoodBA_STeeMg_init_le sz lam0 E n hm hk σ a a').trans ?_
  have hW0 : (0 : ℝ) < ((sz.W n : ℝ) ^ d) := by positivity
  have hterm : ∀ c ∈ Finset.Icc 1 k, ∑ β : Zd d (sz.L n),
      ‖BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
        (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β)‖ ≤ (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    calc _ ≤ ∑ β : Zd d (sz.L n), (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) *
          (‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) (GridGoodBA_eeX a c) β‖ *
            ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) (GridGoodBA_eeY a' c) β‖) :=
          Finset.sum_le_sum fun β _ => GridGoodBA_ee_loop_two hr hW hk σ a a' hc.1 hc.2 β
      _ = (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) * ∑ β : Zd d (sz.L n),
          ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) (GridGoodBA_eeX a c) β‖ *
            ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) (GridGoodBA_eeY a' c) β‖ := by
          rw [Finset.mul_sum]
      _ ≤ (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) * 1 :=
          mul_le_mul_of_nonneg_left (GridGoodBA_cs hr _ _) (by positivity)
      _ = _ := mul_one _
  calc (sz.W n : ℝ) ^ d * ∑ c ∈ Finset.Icc 1 k, ∑ β : Zd d (sz.L n), _ ≤
      (sz.W n : ℝ) ^ d * ∑ _c ∈ Finset.Icc 1 k, (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hW0.le
    _ = (k : ℝ) * (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, pow_succ]
        field_simp

/-- `(W^d)⁻¹ ^ r ≤ 1`. -/
private theorem GridGoodBA_pref_le_one {W : ℕ} (hW : 0 < W) (r : ℕ) : (((W : ℝ) ^ d)⁻¹) ^ r ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (W : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW)
  exact pow_le_one₀ (inv_nonneg.2 (by positivity)) (inv_le_one_of_one_le₀ h1)

/-- **A far pair of labels makes the loop small (decay clause)**: for a loop `(σ, a)` of length `1 ≤ j ≤ Q` with `diam_∞ a ≥ R ≥ 0`,
`‖𝓛_0‖ ≤ c⁻¹ e^{-c R / Q}`. -/
private theorem GridGoodBA_dec {κ : ℝ} (hκ : 0 < κ) (hd : 0 < d) (Λ : ℝ) (hΛ : 0 < Λ) (hg : 0 < lam0 n) (hgΛ : lam0 n ≤ Λ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {j Q : ℕ} (hj : 1 ≤ j) (hjQ : j ≤ Q)
    (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)) (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ (STdiamInf a : ℝ)) :
    ‖loopFine d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))
        (ztOf (BAmF sz lam0 E n) (E n) 0) σ a‖ ≤
      (BAct_rate d Λ κ)⁻¹ * Real.exp (-(BAct_rate d Λ κ * R / (Q : ℝ))) := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hW : 0 < sz.W n := sz.W_pos n
  rw [GridGoodBA_loopFine_init sz lam0 E n hm hj σ a]
  obtain ⟨p, q, hpq⟩ := GridGoodBA_diam_pair hj a R hR
  have hwf : (loopOf σ a).WF := by simp [loopOf, LoopIdx.WF]
  have hlen : (loopOf σ a).length = j := by simp [loopOf, LoopIdx.length]
  have hup : a p ∈ (loopOf σ a).a := List.mem_ofFn.2 ⟨p, rfl⟩
  have hvq : a q ∈ (loopOf σ a).a := List.mem_ofFn.2 ⟨q, rfl⟩
  have h := GridGoodBA_BAMLoop_far (sz.three_le_L n) hd Λ hΛ hg hgΛ hκ hr hW (loopOf σ a) hwf (by omega) hup hvq R hpq
  refine h.trans ?_
  rw [hlen]
  have hc := BAct_rate_pos d Λ κ hd hΛ hκ
  have hcR : 0 ≤ BAct_rate d Λ κ * R := mul_nonneg hc.le hR0
  calc _ ≤ 1 * ((BAct_rate d Λ κ)⁻¹ * Real.exp (-(BAct_rate d Λ κ * R / (j : ℝ)))) :=
        mul_le_mul_of_nonneg_right (GridGoodBA_pref_le_one hW _) (by positivity)
    _ = (BAct_rate d Λ κ)⁻¹ * Real.exp (-(BAct_rate d Λ κ * R / (j : ℝ))) := one_mul _
    _ ≤ _ := mul_le_mul_of_nonneg_left (GridGoodBA_exp_mono hcR hj hjQ) (inv_nonneg.2 hc.le)

/-- **The `ee` far clause (Vb)**: `diam_∞ (a, a') ≥ R ≥ 0` gives `‖𝓔⊗𝓔‖ ≤ k L^d c⁻¹ e^{-c R/(2k+2)}`. -/
private theorem GridGoodBA_ee_far {κ : ℝ} (hκ : 0 < κ) (hd : 0 < d) (Λ : ℝ) (hΛ : 0 < Λ) (hg : 0 < lam0 n) (hgΛ : lam0 n ≤ Λ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool)
    (a a' : Fin k → Zd d (sz.L n)) (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ (STdiamInf (Fin.append a a') : ℝ)) :
    ‖STeeMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) σ a a'‖ ≤
      (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d) *
        ((BAct_rate d Λ κ)⁻¹ * Real.exp (-(BAct_rate d Λ κ * R / ((2 * k + 2 : ℕ) : ℝ)))) := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hW : 0 < sz.W n := sz.W_pos n
  refine (GridGoodBA_STeeMg_init_le sz lam0 E n hm hk σ a a').trans ?_
  obtain ⟨p, q, hpq⟩ := GridGoodBA_diam_pair (by omega : 1 ≤ k + k) (Fin.append a a') R hR
  have hc := BAct_rate_pos d Λ κ hd hΛ hκ
  have hW0 : (0 : ℝ) < ((sz.W n : ℝ) ^ d) := by positivity
  set T : ℝ := (BAct_rate d Λ κ)⁻¹ * Real.exp (-(BAct_rate d Λ κ * R / ((2 * k + 2 : ℕ) : ℝ))) with hT
  have hT0 : 0 ≤ T := by positivity
  have hmem : ∀ (c : ℕ) (β : Zd d (sz.L n)) (i : Fin (k + k)),
      Fin.append a a' i ∈ (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β).a := by
    intro c β i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      exact RBM.Ind.mem_eeLoop_left _ _ _ _ _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)
    · rw [Fin.append_right]
      exact RBM.Ind.mem_eeLoop_right _ _ _ _ _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  have hterm : ∀ c ∈ Finset.Icc 1 k, ∑ β : Zd d (sz.L n),
      ‖BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
        (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β)‖ ≤
      (((sz.L n : ℕ) : ℝ) ^ d) * ((((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) * T) := by
    intro c hc'
    rw [Finset.mem_Icc] at hc'
    have : ∀ β : Zd d (sz.L n), ‖BAMLoop d (sz.L n) (sz.W n)
        (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
        (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β)‖ ≤ (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) * T := by
      intro β
      have hwf : (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β).WF :=
        RBM.Ind.eeLoop_WF (List.ofFn σ) (List.ofFn a) (List.ofFn a') hc'.1 (by simpa using hc'.2) (by simp) (by simp) β β
      have hlen : (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') c β β).length = 2 * k + 2 := by
        have := RBM.Ind.length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := c) (by simp; omega) (by simp) β β
        simpa using this
      have h := GridGoodBA_BAMLoop_far (sz.three_le_L n) hd Λ hΛ hg hgΛ hκ hr hW _ hwf (by omega) (hmem c β p) (hmem c β q) R hpq
      refine h.trans ?_
      rw [hlen, show 2 * k + 2 - 1 = 2 * k + 1 by omega]
    calc _ ≤ ∑ _β : Zd d (sz.L n), (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) * T := Finset.sum_le_sum fun β _ => this β
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast
        ring
  calc (sz.W n : ℝ) ^ d * ∑ c ∈ Finset.Icc 1 k, ∑ β : Zd d (sz.L n), _ ≤
      (sz.W n : ℝ) ^ d * ∑ _c ∈ Finset.Icc 1 k, (((sz.L n : ℕ) : ℝ) ^ d) * ((((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1) * T) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hW0.le
    _ = (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d) * ((((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k) * T) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, pow_succ]
        field_simp
    _ ≤ (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d) * (1 * T) := by
        gcongr
        exact GridGoodBA_pref_le_one hW _
    _ = _ := by rw [one_mul]

end InitBounds

/-! ### 4.5 The clauses with `𝓛 - 𝒦`: value `0` -/

section InitZero

variable (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) {κ : ℝ}

/-- `(𝓛 - 𝒦)_{0,I}(g₀ Ψ) = 0` on every well-formed loop of length `≥ 1` (`STLKIMg`). -/
private theorem GridGoodBA_STLKIMg_zero (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF)
    (h1 : 1 ≤ I.length) :
    STLKIMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) I = 0 :=
  GridGoodBA_LIM_sub_KI sz lam0 E n hκ hg hr I hI h1

/-- The same for the two chains of a two-edge cut. -/
private theorem GridGoodBA_STLKIMg_zero_cut (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) (x : Zd d (sz.L n)) :
    STLKIMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (I.cutGlueL k l x) = 0 ∧
      STLKIMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (I.cutGlueR k l x) = 0 := by
  refine ⟨GridGoodBA_STLKIMg_zero sz lam0 E n hκ hg hr _ (LoopIdx.wf_cutGlueL I x hI hk hkl hl) ?_,
    GridGoodBA_STLKIMg_zero sz lam0 E n hκ hg hr _ (LoopIdx.wf_cutGlueR I x hI hk hkl hl) ?_⟩
  · rw [LoopIdx.length_cutGlueL I x hk hkl hl]; omega
  · rw [LoopIdx.length_cutGlueR I x hk hkl hl]; omega

/-- `STksimLKMg = 0` at the initial state (D1). -/
private theorem GridGoodBA_STksimLKMg_zero (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF) :
    STksimLKMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) l I = 0 := by
  unfold STksimLKMg
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l' hl' =>
    Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl'
  have hz1 := GridGoodBA_STLKIMg_zero_cut sz lam0 E n hκ hg hr I hI hk.1 hl'.1 hl'.2 x
  have hz2 := GridGoodBA_STLKIMg_zero_cut sz lam0 E n hκ hg hr I hI hk.1 hl'.1 hl'.2 y
  rw [hz1.1, hz2.2]
  simp

/-- `STelklkMg = 0` at the initial state (D2). -/
private theorem GridGoodBA_STelklkMg_zero (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF) :
    STelklkMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) I = 0 := by
  unfold STelklkMg
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l' hl' =>
    Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl'
  have hz1 := GridGoodBA_STLKIMg_zero_cut sz lam0 E n hκ hg hr I hI hk.1 hl'.1 hl'.2 x
  have hz2 := GridGoodBA_STLKIMg_zero_cut sz lam0 E n hκ hg hr I hI hk.1 hl'.1 hl'.2 y
  rw [hz1.1]
  simp

/-- `STavgErrMg = 0` at the initial state: `𝓛_{⟨σ,a⟩} = M(σ)_{aa} = m(σ)`. -/
private theorem GridGoodBA_STavgErrMg_zero (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n))
    (s : Bool) (a : Zd d (sz.L n)) :
    STavgErrMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) s a = 0 := by
  unfold STavgErrMg
  have h1 : STLIMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) ⟨[s], [a]⟩ =
      PropSpin (BAmF sz lam0 E n) s := by
    have := GridGoodBA_LIM_init sz lam0 E n (lt_of_lt_of_le hκ hr.2) ⟨[s], [a]⟩ (by simp [LoopIdx.WF])
      (by simp [LoopIdx.length])
    change (baStep2Mat sz lam0 E).LIM n 0 _ _ = _
    rw [this]
    exact GridGoodBA_BAMLoop_one_loop hr.1 s a
  rw [h1]
  unfold STmsigg PropSpin
  cases s <;> exact sub_self _

/-- `STegtMg = 0` at the initial state (D3). -/
private theorem GridGoodBA_STegtMg_zero (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n))
    (I : LoopIdx (Zd d (sz.L n))) :
    STegtMg (baStep2Mat sz lam0 E) n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) I = 0 := by
  unfold STegtMg
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun x _ =>
    Finset.sum_eq_zero fun y _ => ?_)
  rw [GridGoodBA_STavgErrMg_zero sz lam0 E n hκ hr]
  simp

/-- `𝓛_0 - 𝒦_0 = 0` for the vector loops `(σ, a)` of length `j ≥ 1`. -/
private theorem GridGoodBA_LM_sub_K_zero (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {j : ℕ} (hj : 1 ≤ j) (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) σ a -
      (baStep2Mat sz lam0 E).K n 0 σ a = 0 := by
  have h1 := GridGoodBA_LIM_sub_KI sz lam0 E n hκ hg hr (loopOf σ a) (by simp [loopOf, LoopIdx.WF])
    (by simpa [loopOf, LoopIdx.length] using hj)
  have h2 : (baStep2Mat sz lam0 E).LM n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) σ a =
      (baStep2Mat sz lam0 E).LIM n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (loopOf σ a) := by
    change loopFine d (sz.L n) (sz.W n) _ _ σ a = loopL d (sz.L n) (sz.W n) _ _ _
    rw [loopFine, loopM_eq_loopL]
  have h3 : (baStep2Mat sz lam0 E).K n 0 σ a = (baStep2Mat sz lam0 E).KI n 0 (loopOf σ a) := rfl
  rw [h2, h3]
  exact h1

end InitZero

/-! ### 4.6 `H_0 = g₀ Ψ` is good at one index -/

section InitAssemble

variable (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- A far pair forces `0 < d` (for `d = 0` the lattice is a point and `diam_∞ = 0`). -/
private theorem GridGoodBA_pos_d {L j : ℕ} [NeZero L] (a : Fin j → Zd d L) {R : ℝ} (hR0 : 0 < R)
    (hR : R ≤ (STdiamInf a : ℝ)) : 0 < d := by
  by_contra hd
  have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
  subst hd0
  have : STdiamInf a = 0 := by
    unfold STdiamInf zdistInf
    simp
  rw [this] at hR
  simp at hR
  linarith

/-- The `ee` level estimate in the form of the clause (D4): `Bctl_0 ≥ W^{-d} (1 + 𝔡⁻²)⁻¹` once `g_n ≤ 𝔡⁻¹`. -/
private theorem GridGoodBA_Bctl_lower {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hlam : sz.lam n ≤ 𝔡⁻¹) (hlam0 : 0 ≤ sz.lam n) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 + (𝔡⁻¹) ^ 2)⁻¹ ≤ sz.Bctl n 0 := by
  unfold Sizes.Bctl Bparam
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hg2 : sz.lam n ^ 2 ≤ (𝔡⁻¹) ^ 2 := pow_le_pow_left₀ hlam0 hlam 2
  have hq : 0 < 1 + (𝔡⁻¹) ^ 2 := by positivity
  have h1 : (1 + (𝔡⁻¹) ^ 2)⁻¹ ≤ (sz.lam n ^ 2 + |1 - (0 : ℝ)|)⁻¹ := by
    apply inv_anti₀ (by positivity)
    simp only [sub_zero, abs_one]
    linarith
  have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - (0 : ℝ)|)⁻¹ := by positivity
  calc (1 + (𝔡⁻¹) ^ 2)⁻¹ ≤ (sz.lam n ^ 2 + |1 - (0 : ℝ)|)⁻¹ := h1
    _ = (sz.lam n ^ 2 + |1 - (0 : ℝ)|)⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by simp
    _ ≤ _ := le_add_of_nonneg_right h2

/-- **`H_0 = g₀ Ψ` is in the good set** at one index (the sum of §§4.1-4.5): `0 < g₀ ≤ 𝔡⁻¹`, `g ≤ 𝔡⁻¹`, the `ee` level
`C₀ = k (1 + 𝔡⁻²)^{2k} ≤ Γ² Λ`, and the far threshold `hfar` (`k L^d c⁻¹ e^{-c W^{τ'}/(2k+2)} ≤ W^{-D'}`). -/
private theorem GridGoodBA_goodSet_n {κ 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hg : 0 < lam0 n) (hgΛ : lam0 n ≤ 𝔡⁻¹)
    (hlam : sz.lam n ≤ 𝔡⁻¹) (hlam0 : 0 ≤ sz.lam n) {k : ℕ} (hk : 1 ≤ k) {Γ Λ Φ τ' D' : ℝ} (hΓ : 0 ≤ Γ)
    (hΓΦ : 1 ≤ Γ * Φ) (hΓΛ : (k : ℝ) * (1 + (𝔡⁻¹) ^ 2) ^ (2 * k) ≤ Γ * (Γ * Λ))
    (hfar : (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d) *
      ((BAct_rate d 𝔡⁻¹ κ)⁻¹ * Real.exp (-(BAct_rate d 𝔡⁻¹ κ * (((sz.W n : ℕ) : ℝ) ^ τ') / ((2 * k + 2 : ℕ) : ℝ)))) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-D')) :
    GoodSetNg (baStep2Mat sz lam0 E) n 0 k Γ Λ Φ τ' D' (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hm1 : (BAmF sz lam0 E n).im ≤ 1 := by
    refine (Complex.im_le_norm _).trans ?_
    exact BAm_norm_le_one d (sz.L n) _ ((E n : ℝ) : ℂ) _ (by simp) hr.1
  have hW : 0 < sz.W n := sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast hW
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hB : 0 < sz.Bctl n 0 := st_Bctl_pos sz (by norm_num)
  have hη : (baStep2Mat sz lam0 E).eta n 0 = (BAmF sz lam0 E n).im := by
    change etaOf (BAmF sz lam0 E n) 0 = _
    simp [etaOf]
  have hη0 : 0 < (baStep2Mat sz lam0 E).eta n 0 := by rw [hη]; exact hm
  have hη1 : (baStep2Mat sz lam0 E).eta n 0 ≤ 1 := by rw [hη]; exact hm1
  have hΓΦ0 : 0 ≤ Γ * Φ := by linarith
  have hD0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hRHS : ∀ c : ℝ, 0 ≤ c → ∀ r : ℕ, 0 ≤ c * (sz.Bctl n 0 ^ r / (baStep2Mat sz lam0 E).eta n 0) := fun c hc r =>
    mul_nonneg hc (div_nonneg (pow_nonneg hB.le _) hη0.le)
  have hwfo : ∀ {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)), (loopOf σ a).WF :=
    fun σ a => by simp [loopOf, LoopIdx.WF]
  have hfarpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ τ' := Real.rpow_pos_of_pos hW0 _
  -- the far bound `T ≤ k L^d T ≤ W^{-D'}`
  have hTT : 0 < d → (BAct_rate d 𝔡⁻¹ κ)⁻¹ * Real.exp (-(BAct_rate d 𝔡⁻¹ κ * (((sz.W n : ℕ) : ℝ) ^ τ') / ((2 * k + 2 : ℕ) : ℝ))) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-D') := by
    intro hd
    refine le_trans ?_ hfar
    have hc := BAct_rate_pos d 𝔡⁻¹ κ hd (inv_pos.2 h𝔡) hκ
    have hT0 : 0 ≤ (BAct_rate d 𝔡⁻¹ κ)⁻¹ * Real.exp (-(BAct_rate d 𝔡⁻¹ κ * (((sz.W n : ℕ) : ℝ) ^ τ') / ((2 * k + 2 : ℕ) : ℝ))) := by
      positivity
    have hkL : (1 : ℝ) ≤ (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d) := by
      have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have h2 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
      nlinarith
    calc _ = 1 * ((BAct_rate d 𝔡⁻¹ κ)⁻¹ * Real.exp (-(BAct_rate d 𝔡⁻¹ κ * (((sz.W n : ℕ) : ℝ) ^ τ') / ((2 * k + 2 : ℕ) : ℝ)))) :=
          (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hkL hT0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Hermitian
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star ((lam0 n : ℝ) : ℂ) = ((lam0 n : ℝ) : ℂ) from Complex.conj_ofReal _]
  · -- (G2)
    intro m hm1' hmk
    have hsup : Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
        (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
          ‖(baStep2Mat sz lam0 E).LM n 0 (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) p.1 p.2 -
            (baStep2Mat sz lam0 E).K n 0 p.1 p.2‖) ≤ 0 := by
      refine Finset.sup'_le _ _ fun p _ => ?_
      rw [GridGoodBA_LM_sub_K_zero sz lam0 E n hκ hg hr hm1' p.1 p.2, norm_zero]
    have := div_nonpos_of_nonpos_of_nonneg hsup (pow_nonneg hB.le m)
    linarith
  · -- (Dec)
    intro j hj1 hj2 σ a hfar'
    rw [GridGoodBA_LM_sub_K_zero sz lam0 E n hκ hg hr hj1 σ a, norm_zero, add_zero]
    have hell : 1 ≤ ellT (sz.L n) (sz.lam n) 0 := one_le_ellT hL1
    have hR : ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) :=
      le_trans (le_mul_of_one_le_left hfarpos.le hell) hfar'
    have hd := GridGoodBA_pos_d a hfarpos hR
    have := GridGoodBA_dec sz lam0 E n hκ hd 𝔡⁻¹ (inv_pos.2 h𝔡) hg hgΛ hr hj1 hj2 σ a _ hfarpos.le hR
    exact this.trans (hTT hd)
  · -- (D1)
    intro l hl3 hlk σ a
    rw [GridGoodBA_STksimLKMg_zero sz lam0 E n hκ hg hr l _ (hwfo σ a), norm_zero]
    exact hRHS _ (mul_nonneg hΓ hΓΦ0) k
  · -- (D2)
    intro σ a
    rw [GridGoodBA_STelklkMg_zero sz lam0 E n hκ hg hr _ (hwfo σ a), norm_zero]
    exact hRHS _ (mul_nonneg hΓ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))) k
  · -- (D3)
    intro σ a
    rw [GridGoodBA_STegtMg_zero sz lam0 E n hκ hr, norm_zero]
    exact hRHS _ (mul_nonneg hΓ hΓΦ0) k
  · -- (D4)
    intro σ a a'
    refine (GridGoodBA_ee_level sz lam0 E n hκ hr hk σ a a').trans ?_
    set q : ℝ := 1 + (𝔡⁻¹) ^ 2 with hq
    have hq0 : 0 < q := by positivity
    set X : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (2 * k) with hX
    have hX0 : 0 ≤ X := by positivity
    have hlow := GridGoodBA_Bctl_lower sz n h𝔡 hlam hlam0
    have hBl : X * (q⁻¹) ^ (2 * k) ≤ sz.Bctl n 0 ^ (2 * k) := by
      rw [hX, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hlow _
    have hG : (k : ℝ) * q ^ (2 * k) ≤ Γ * (Γ * Λ) := hΓΛ
    have hG0 : 0 ≤ Γ * (Γ * Λ) := le_trans (by positivity) hG
    have hBp : 0 ≤ sz.Bctl n 0 ^ (2 * k) := pow_nonneg hB.le _
    have hdiv : sz.Bctl n 0 ^ (2 * k) ≤ sz.Bctl n 0 ^ (2 * k) / (baStep2Mat sz lam0 E).eta n 0 := by
      rw [le_div_iff₀ hη0]
      nlinarith
    have hQq : q ^ (2 * k) * (q⁻¹) ^ (2 * k) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hq0.ne', one_pow]
    calc (k : ℝ) * X = (k : ℝ) * q ^ (2 * k) * (X * (q⁻¹) ^ (2 * k)) := by
          rw [mul_assoc, ← mul_assoc (q ^ (2 * k)), mul_comm (q ^ (2 * k)) X, mul_assoc, hQq, mul_one]
      _ ≤ Γ * (Γ * Λ) * sz.Bctl n 0 ^ (2 * k) := mul_le_mul hG hBl (by positivity) hG0
      _ ≤ Γ * (Γ * Λ) * (sz.Bctl n 0 ^ (2 * k) / (baStep2Mat sz lam0 E).eta n 0) :=
          mul_le_mul_of_nonneg_left hdiv hG0
  · -- (Va)
    intro σ a hfar'
    rw [GridGoodBA_STelklkMg_zero sz lam0 E n hκ hg hr _ (hwfo σ a), GridGoodBA_STegtMg_zero sz lam0 E n hκ hr,
      Finset.sum_eq_zero (fun l _ => GridGoodBA_STksimLKMg_zero sz lam0 E n hκ hg hr l _ (hwfo σ a))]
    simpa using hD0
  · -- (Vb)
    intro σ a a' hfar'
    have hell : 1 ≤ ellT (sz.L n) (sz.lam n) 0 := one_le_ellT hL1
    have hR : ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append a a') : ℝ) :=
      le_trans (le_mul_of_one_le_left hfarpos.le hell) hfar'
    have hd := GridGoodBA_pos_d (Fin.append a a') hfarpos hR
    exact (GridGoodBA_ee_far sz lam0 E n hκ hd 𝔡⁻¹ (inv_pos.2 h𝔡) hg hgΛ hr hk σ a a' _ hfarpos.le hR).trans hfar

end InitAssemble

/-! ### 4.7 The eventual threshold and the theorem -/

section InitEventual

/-- `A W^P e^{-c W^{τ'}} ≤ W^{-D}` for large `W` (an exponential of a power beats every power). -/
private theorem GridGoodBA_exp_ev (P D c τ' A : ℝ) (hc : 0 < c) (hτ' : 0 < τ') :
    ∀ᶠ W : ℝ in atTop, A * (W ^ P * Real.exp (-(c * W ^ τ'))) ≤ W ^ (-D) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((P + D) / τ') c hc
  have h2 := h1.comp (tendsto_rpow_atTop hτ')
  have h3 : Tendsto (fun W : ℝ => A * (W ^ (P + D) * Real.exp (-c * W ^ τ'))) atTop (𝓝 (A * 0)) := by
    refine (Tendsto.const_mul A ?_)
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with W hW
    simp only [Function.comp]
    rw [← Real.rpow_mul hW.le]
    congr 2
    field_simp
  rw [mul_zero] at h3
  filter_upwards [h3.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)), eventually_gt_atTop 0] with W hW hW0
  have hWD : 0 < W ^ D := Real.rpow_pos_of_pos hW0 D
  have e2 : W ^ (P + D) = W ^ P * W ^ D := Real.rpow_add hW0 P D
  rw [Real.rpow_neg hW0.le, ← one_div, le_div_iff₀ hWD]
  have : A * (W ^ P * Real.exp (-(c * W ^ τ'))) * W ^ D = A * (W ^ (P + D) * Real.exp (-c * W ^ τ')) := by
    rw [e2, neg_mul]; ring
  rw [this]
  exact hW.le

/-- `W_n → ∞` along an admissible sequence (`W ≥ N^𝔠`, `N → ∞`). -/
private theorem GridGoodBA_W_tendsto {𝔠 𝔡 : ℝ} (sz : Sizes d) (h : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hsize, hband, -⟩ := h
  have h1 : Tendsto (fun n => (((sz.size n : ℕ) : ℝ)) ^ 𝔠) atTop atTop := (tendsto_rpow_atTop h𝔠).comp hsize
  exact tendsto_atTop_mono' atTop hband h1

/-- **The far threshold** (`k L^d c⁻¹ e^{-c W^{τ'}/(2k+2)} ≤ W^{-D'}` eventually): `L^d ≤ N ≤ W^{1/𝔠}` and an exponential of a power
beats a power. -/
private theorem GridGoodBA_far_ev {𝔠 𝔡 κ : ℝ} (hκ : 0 < κ) (sz : Sizes d) (h : sz.Admissible 𝔠 𝔡) (k : ℕ) {τ' D' : ℝ}
    (hτ' : 0 < τ') :
    ∀ᶠ n in atTop, (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d) *
      ((BAct_rate d 𝔡⁻¹ κ)⁻¹ * Real.exp (-(BAct_rate d 𝔡⁻¹ κ * (((sz.W n : ℕ) : ℝ) ^ τ') / ((2 * k + 2 : ℕ) : ℝ)))) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  have h𝔠 : 0 < 𝔠 := h.1
  have h𝔡 : 0 < 𝔡 := h.2.1
  by_cases hd : 0 < d
  · have hc := BAct_rate_pos d 𝔡⁻¹ κ hd (inv_pos.2 h𝔡) hκ
    set c := BAct_rate d 𝔡⁻¹ κ with hcdef
    have hQ : (0 : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by positivity
    have hc' : 0 < c / ((2 * k + 2 : ℕ) : ℝ) := div_pos hc hQ
    have hWt := GridGoodBA_W_tendsto sz h
    have hev := hWt.eventually (GridGoodBA_exp_ev (1 / 𝔠) D' (c / ((2 * k + 2 : ℕ) : ℝ)) τ' ((k : ℝ) * c⁻¹) hc' hτ')
    filter_upwards [hev, h.2.2.2.1, hWt.eventually_gt_atTop 0] with n hn hband hW0
    have hLN : (((sz.L n : ℕ) : ℝ) ^ d) ≤ ((sz.size n : ℕ) : ℝ) := by
      have : (sz.L n) ^ d ≤ sz.size n := by
        unfold Sizes.size
        exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
      exact_mod_cast this
    have hsz0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hNW : ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
      calc ((sz.size n : ℕ) : ℝ) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (1 / 𝔠) := by
            rw [← Real.rpow_mul hsz0]
            field_simp
            simp
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hsz0 _) hband (by positivity)
    have hexp : Real.exp (-(c * (((sz.W n : ℕ) : ℝ) ^ τ') / ((2 * k + 2 : ℕ) : ℝ))) =
        Real.exp (-(c / ((2 * k + 2 : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ')) := by
      congr 2
      ring
    rw [hexp]
    have hT0 : 0 ≤ Real.exp (-(c / ((2 * k + 2 : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ')) := (Real.exp_pos _).le
    calc (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d) * (c⁻¹ * Real.exp (-(c / ((2 * k + 2 : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ')))
        ≤ (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) * (c⁻¹ * Real.exp (-(c / ((2 * k + 2 : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ'))) := by
          gcongr
          exact hLN.trans hNW
      _ = ((k : ℝ) * c⁻¹) * (((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) *
            Real.exp (-(c / ((2 * k + 2 : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ'))) := by ring
      _ ≤ _ := hn
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst hd0
    refine Eventually.of_forall fun n => ?_
    have hc0 : BAct_rate 0 𝔡⁻¹ κ = 0 := by
      unfold BAct_rate
      rw [show 4 * (((0 : ℕ) : ℝ)) * 𝔡⁻¹ = 0 by simp, div_zero, add_zero, Real.log_one]
      exact min_eq_left (by positivity)
    rw [hc0]
    simp only [inv_zero, zero_mul, mul_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **Target 7, `baGoodSetNg_init`** (supervisor 2351 T4S2-C2, F5; `T2492_InitMem`): the initial membership at BA, the hypothesis `h0` of
`azumaProxy_pos_goodExitTauNg`, in the eventual form.  The (D4) level `C₀ = k (1 + 𝔡⁻²)^{2k}` depends on `(𝔡, k)` only and is fixed
before `(𝔠, sz, z)`.  At `s n = 0` the grid state is `H_0 = g₀ Ψ` (`azumaProxy_Hpath_zerog`, `baStep2Mat_walkForm`) and `u_0 = 0`, so
`G_0 = M`, `𝓛_0 = BAMLoop = 𝒦_0` and every clause with `𝓛 - 𝒦` vanishes; the far clauses hold from the Combes-Thomas decay of `M`
(`BAMB_decay_large`) past a threshold in `n` (`GridGoodBA_far_ev`); the level (D4) uses only Ward and Cauchy-Schwarz. -/
theorem baGoodSetNg_init {d : ℕ} (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
        ∀ Γ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Γ n) → (∀ n, 1 ≤ Γ n * Φ n) → (∀ n, C₀ ≤ Γ n * (Γ n * Λ n)) →
          ∀ τ' D' : ℝ, 0 < τ' → 0 < D' →
            ∀ᶠ n in atTop, ∀ (s v : ℕ → ℝ) (K : ℕ → ℕ) (ω : PathΩ sz), s n = 0 →
              GoodSetNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s v K n 0) k (Γ n) (Λ n) (Φ n) τ' D'
                ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s v K n 0 ω) := by
  refine ⟨(k : ℝ) * (1 + (𝔡⁻¹) ^ 2) ^ (2 * k), by positivity, ?_⟩
  intro 𝔠 sz z hflow Γ Λ Φ hΓ hΓΦ hΓΛ τ' D' hτ' hD'
  have hwin := BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow
  have hWO := hflow.1.2.2.2.2
  have hfar := GridGoodBA_far_ev (D' := D') hκ sz hflow.1 k hτ'
  filter_upwards [hwin, hWO, hfar] with n hn1 hn2 hn3
  intro s v K ω hs
  have hu : gridTime s v K n 0 = 0 := by simp [gridTime, hs]
  rw [hu, azumaProxy_Hpath_zerog (baStep2Mat_walkForm sz _ _) s v K n hs ω]
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlam0 : 0 ≤ sz.lam n := le_trans (Real.rpow_nonneg hW.le _) hn2.1
  exact GridGoodBA_goodSet_n sz (BAflowLam0 sz z) (BAflowEs sz z) n hκ h𝔡 (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) hn1.1 hn1.2
    hn2.2 hlam0 hk (hΓ n) (hΓΦ n) (hΓΛ n) hn3

end InitEventual

end Init

/-! ## 5. Compiled nonempty instances (targets 7-10)

`d = 3`, the preflight sequence `sz0`, the spectral parameters `zSeq` with `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`, the grid
`(s, t, K) = (0, 1/32, 4)`.  Every deterministic premise is discharged; `STKboundgL` and `STKwardgL` by the merged `inst_BAKbound` and `baKward_holds`.  What
stays a hypothesis of an example is another gate's pin: `STLKgL`, `STStep2ConclgL` (T1-BA) and `hQ` of target 10 (U3s2-U3s3). -/

namespace GridGoodBAInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst RBM.BA.GridDriftBAInst

/-- **Target 8** at the data (conditional form): the four T2486 (a) facts by name. -/
example : GridGoodNgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z) :=
  baGridGood_of 3 (baKcalDecay_holds 3) (baStep2Mat_carrierFacts 3) (baSEforLn_holds 3) (baEtermDecaygL 3)

/-- **Target 8** at the data: the closure applied at `(κ, ε, 𝔡, C_d) = (1/2, 1/10, 1/10, 1)`, the flow `flow_sz0`, the windows
`s ≡ 1/10 < t ≡ 1/2 ≤ t₀`; `(con_st_ind)` from `s1Setup_conStInd_const`; the other gates' pins stay hypotheses. -/
example (hLK : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10))
    (hStep2 : STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2) 1) :
    GridGoodNConclg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (Sizes.seqP (sz0.withLam 0))
      (fun _ => 1 / 10) (fun _ => 1 / 2) := by
  obtain ⟨𝔠d, h𝔠d, -, H⟩ := baGridGood_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 one_pos
  exact H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun n => (t0_sz0 n).trans' (by norm_num)) trivial inst_BAKbound
    (baKward_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0) hLK
    (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠d) hStep2

/-- **Target 7** at the data: `k = 3`, `(κ, ε, 𝔡) = (1/2, 1/10, 1/10)`, the levels `Γ ≡ Φ ≡ 1`, `Λ ≡ C₀`; the conclusion holds
at some index `n`, for every `ω`, on the grid `(s, v, K) = (0, 1/32, 4)`. -/
example : ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ n : ℕ, ∀ ω : PathΩ sz0,
    GoodSetNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) n (gridTime (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) n 0)
      3 1 C₀ 1 1 1 ((baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).Hpath (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) n 0 ω) := by
  obtain ⟨C₀, hC₀, H⟩ := baGoodSetNg_init (d := 3) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 3 (by norm_num)
  have h := H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1) (fun _ => C₀) (fun _ => 1) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by simp) 1 1 one_pos one_pos
  obtain ⟨n, hn⟩ := h.exists
  exact ⟨C₀, hC₀, n, fun ω => hn (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) ω rfl⟩

/-- **Target 9** at the data: the envelope (`k = 2`, `τ_K = 1`, `σ = (+, -)`), eventually in `n`; `STKboundgL` by `inst_BAKbound`. -/
example :=
  baGridDrift_envelope sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 inst_loopForm inst_BAKbound 2 le_rfl 1 one_pos
    (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) (fun _ => le_rfl) (fun _ => by norm_num)
    (fun n => (t0_sz0 n).trans' (by norm_num)) (fun _ => by norm_num) ![true, false]

/-- **Target 10** at the data: the Azuma pin, the `Y` moments, and `azumaProxy_subG_goodExitg` at `n = 1`, `k = 2`, `σ = (+, -)`,
`m = 1`, `j = 0` (`hQ` stays a hypothesis). -/
example : AzumaSubGNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) 0 (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) :=
  baAzumaSubG sz0 _ _ _ _ _

example (κm τ' : ℝ) :
    YMomentsNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) κm τ' (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) :=
  baYMoments sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 inst_loopForm κm τ' _ _ _

example (Q : NNReal)
    (hQ : ∀ M, GoodSetNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) 1 (gridTime (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) 1 0)
        2 1 1 1 1 1 M → M.IsHermitian →
      gridStep (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) 1 * ((2 : ℕ) * qvFormNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) 1
        (gridTime (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) 1 1) (gridTime (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) 1 1) ![true, false] M
        (fun _ => 0)) ≤ (Q : ℝ)) :
    SubGaussStopNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) ![true, false] (gridTime (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) 1)
      (goodExitTauNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) 2
        (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 1 1)
      (fun j ω => ZvecNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) 1 j ![true, false] ω)
      1 (fun _ => 0) 0 Q :=
  baAzumaProxy_subG_goodExit sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 inst_loopForm (fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) 1 2 le_rfl ![true, false] (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 1 1
    (by norm_num [gridStep]) (fun _ => 0) 0 (by norm_num) Q hQ

end GridGoodBAInst

end RBM.BA

end
