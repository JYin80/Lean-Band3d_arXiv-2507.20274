/-
Release check for T2495 (dispatcher V3, 2026-10-13 06:58 UTC; DECISIONS §296).  BA-T T7-BA: the BA readings of T7 (T7a = T2454 `Chain/DecayGen`,
T7b = T2467 `Chain/Step2EventsGen`) at the BA setting `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, in the new leaf
`BA/DecayLoopBA.lean` (targets 1-6; reserve `BA/DecayLoopBA2.lean` only under the split).  No merged file is edited.
Part 1: merged names.  Part 2: pins (prefix `T2495_`, content binding): the uniform, per-time and single-time loop decay at
BA with the far decay of `𝒦` closed (`baKcalDecay_holds`, U2-BA), the eventual range `N⁻¹ ≤ 1 - t`, the Step 2 closure of
`STDecayLoopUgL` (`twSteps` conjuncts 1 and 4) under the two stage-L pins of exact type, the two L-bridges at BA.  Then shapes
(not binding): the `toFlowFM` spelling (finding G3), the per-time reading of `STGdecayWgL` (finding G4), `twSteps` at BA, R1 at
BA (for the record: no pin contains it), the instance data.
Coupling (UBA-C1; R1 = DECISIONS §273 (1)): not triggered; the cutoff reads `sz.lam`, the kernels sit inside `baFMz`, the
crossing lives inside the merged `baKcalDecay_holds`.  No pin reads `withLam` except the law `seqP (sz.withLam 0)`.
TN-C4: no grid statement.  Step 1: none read.
Merged names only.  Statements only; no proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2495-check.lean
-/
import RBM3D.Chain.DecayGenTw
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.GridGoodGen
import RBM3D.BA.KDecayBA
import RBM3D.BA.Step2CloseBA
import RBM3D.BA.NetLiftBA
import RBM3D.BA.B45BA

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the BA setting (row 0, T8-BA)
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.baStep2Mat
#check @RBM.Gauss.Sizes.seqP
#check @RBM.BA.PrecL
#check @RBM.BA.PrecPTL

-- T7a (T2454): the pins and the three results read at BA
#check @RBM.BA.STDecayLoopUgL
#check @RBM.BA.STDecayLoopPTgL
#check @RBM.BA.STDecayLoopAtgL
#check @RBM.BA.STKcalDecaygL
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.DecayGen_WardPair
#check @RBM.BA.stDecayLoopAtgL_of
#check @RBM.BA.stDecayLoopPTgL_of_step2
#check @RBM.BA.stDecayLoopUgL_of_step2
#check @RBM.BA.DecayGenTw_baWardPair

-- T7b (T2467): the Step 2 events layer and its BA leaf
#check @RBM.BA.Step2EventsGen_Flow
#check @RBM.BA.Step2EventsGen_Rot3
#check @RBM.BA.Step2EventsGen_Grid
#check @RBM.BA.STScaleInvgL
#check @RBM.BA.STBdatagL
#check @RBM.BA.ST_event_lwg
#check @RBM.BA.ST_good_probg
#check @RBM.BA.stLWBgL_of_LWtermG
#check @RBM.BA.stLWTgL_of_LWtermExpG
#check @RBM.BA.Step2EventsGenTw_baFlow
#check @RBM.BA.Step2EventsGenTw_baRot3
#check @RBM.BA.Step2EventsGenTw_baGrid
#check @RBM.BA.Step2EventsGenTw_toFlowFM

-- U2-BA (T2486): the far decay of `𝒦`, the flow facts, the ℰ-term decays, the readings with `hNt` open
#check @RBM.BA.BAKcalDecay
#check @RBM.BA.baKcalDecay_holds
#check @RBM.BA.KDecayBAInst.inst_baKcalDecay
#check @RBM.BA.KDecayBAInst.inst_baKcalDecay_far
#check @RBM.BA.baStep5CasesGen_flowFacts
#check @RBM.BA.baEtermDecaygL
#check @RBM.BA.baWardTypePgL_of
#check @RBM.BA.baB45gL_of

-- T1-BA (T2487): Step 2 at BA and its frame
#check @RBM.BA.baStep2_holds
#check @RBM.BA.baStep2_oneLoop
#check @RBM.BA.baSTGijDecgL_holds
#check @RBM.BA.BAStep2
#check @RBM.BA.BAStep2_iff_STStep2G
#check @RBM.BA.STStep2G
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STStep2DecayPTgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep1WeakgL

-- stage L (inputs of exact type; owner BA-L6 = T2494)
#check @RBM.BA.baPin
#check @RBM.BA.BALWterm
#check @RBM.BA.BALWtermExp
#check @RBM.BA.BASTLWB
#check @RBM.BA.BASTLWT
#check @RBM.BA.STLWBgL
#check @RBM.BA.STLWTgL

-- flow data, the range, uniform to per time
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_one_sub_T0
#check @RBM.BA.baFlow_premises
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Path.perTimeOfStochDomAt

-- consumers and the coupling record
#check @RBM.BA.twSteps
#check @RBM.BA.STLmaxUgL
#check @RBM.BA.STLKUgL
#check @RBM.BA.gridGoodNgL_of
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.baStep5III_lam0_le_lam

-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: pins (content binding) -/

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1, `baDecayLoopU_of`** (`lem_decayLoop` uniformly in `u ∈ [s,t]`, `3_5:1126`; BA `7_8:1994`): `stDecayLoopUgL_of_step2`
at `baFMz sz z`, law `seqP (sz.withLam 0)`; F3 inline (`κm = κ`, `EMn2BA_mF_data`), `Admissible` from the flow, `t < 1` from
`EMn2BA_T0_lt_one`, the Ward pair `DecayGenTw_baWardPair`, the far decay of `𝒦` from `baKcalDecay_holds`.  Only the Step 2 decay
`STGdecayWgL` stays an input.  It is the `hU` of `baEtermDecaygL` (finding G3) and conjunct 4 of `twSteps` at BA. -/
def T2495_DecayLoopU (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (s t : ℕ → ℝ) (Cd : ℝ), (∀ n, 0 ≤ s n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
        STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- **Target 2 (a), `baFlow_sizeInv_le`**: the eventual range `N⁻¹ ≤ 1 - t_n` below the BA horizon, from `baFlow_premises`
(`RangeCond (ε/2) t`) and `N^{-1} ≤ N^{-1+ε/2}`.  It is `hrange` of `stDecayLoopPTgL_of_step2` and the open `hNt` of
`baWardTypePgL_of`, `baB45gL_of`. -/
def T2495_SizeInv (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n

/-- **Target 2 (b), `baDecayLoopPT_of`** (the BA twin of T7a target 5): `stDecayLoopPTgL_of_step2` at the BA setting, `hrange` from
target 2 (a), the other facts as in target 1; the per-time Step 2 decay `STStep2DecayPTgL` stays an input. -/
def T2495_DecayLoopPT (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (s t : ℕ → ℝ) (Cd : ℝ), (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STStep2DecayPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) Cd s t →
        STDecayLoopPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- **Target 3, `baDecayLoopAt_holds`** (the BA twin of T7a target 4, single time): the merged pin `STDecayLoopAtgL` at `baFMz sz z`
along every BA flow, with `κm = κ`; its own premises (`DecayGen_Spec`, `Admissible`, the time window, the prefactor, the decay
input) stay inside the merged body. -/
def T2495_DecayLoopAt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (C₀ : ℝ) (u P : ℕ → ℝ), STDecayLoopAtgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) κ 𝔠 𝔡 C₀ u P

/-- **Target 4, `baStep2Decay_holds`**: `twSteps` conjuncts 1 and 4 at BA in the frame of `STStep2G` (`Chain/Step2Gen.lean:591`),
from `baStep2_holds` and target 1.  The constants `Cd, 𝔠d` come before `(𝔠, sz, z)` (supervisor 0349 U5S-C3).  Inputs: the two
stage-L pins (exact type, owner BA-L6).  The Step 1 and induction binders are binders of the frame, not premises. -/
def T2495_Step2Decay (d : ℕ) : Prop :=
  BALWterm d → BALWtermExp d → 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
          (∀ n, t n ≤ BAflowT0 sz z n) →
          STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s → STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s →
          STConStInd sz 𝔠d s t →
          STStep1LoopgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
          STStep1WeakgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
            STStep2ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd ∧
              STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- **Target 5, `baSTLWB_of`**: the generic L-bridge `stLWBgL_of_LWtermG` at BA (F1 `BAFlow`, F7 `Step2EventsGenTw_baRot3`), every `d`. -/
def T2495_STLWB (d : ℕ) : Prop := 3 ≤ d → BALWterm d → BASTLWB d

/-- **Target 5, `baSTLWT_of`**: the generic L-bridge `stLWTgL_of_LWtermExpG` at BA, every `d`. -/
def T2495_STLWT (d : ℕ) : Prop := 3 ≤ d → BALWtermExp d → BASTLWT d

/-! ## Shapes (not binding) -/

/-- Finding G3: the `toFlowFM` spelling of the BA family (`Step2EventsGenTw_toFlowFM`, definitional) gives the same `Prop`, so the
`hU` of `baEtermDecaygL` (`BA/SEforLnBA.lean:274`) is target 1 at the same data; no second statement. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
  STDecayLoopUgL (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM (Sizes.seqP (sz.withLam 0)) s t ↔
    STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- Finding G4 (private helper `DecayLoopBA_PT_of_U`): the uniform Step 2 decay gives the per-time one through
`RBM.Path.perTimeOfStochDomAt`, at every carrier and law.  This is the per-time reading T2487 answer (5) did not export; it feeds
target 2 (b) in the instances. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ),
  STGdecayWgL C μ s t Cd → STStep2DecayPTgL C μ Cd s t

/-- `twSteps` at BA (V2a, TLF-C5): target 4 gives conjuncts 1 and 4; conjuncts 2-3 are U3-BA's. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ),
  (STStep2ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd ∧
      STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) →
    STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd

/-- R1 at BA (`gK = BAflowLam0 sz z`, `A = (κ+1)/κ`, from `TwistStep2_lam0_sq`), recorded only: no `T2495_*` pin contains it. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
    sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2

section Inst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- Target 6, instance of target 1 at `sz0`, `zSeq`, `s ≡ 1/10`, `t ≡ 1/2 < t₀` (`half_lt_t0`); only the Step 2 decay stays open. -/
example : Prop := ∀ Cd : ℝ,
  STGdecayWgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2) Cd →
    STDecayLoopUgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2)

/-- Target 6, instance of target 4 at `sz0`, `zSeq`: constants first, then the conclusion under the binders of the frame; the
stage-L pins stay hypotheses. -/
example : Prop := BALWterm 3 → BALWtermExp 3 → ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
  (STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) →
    STDecaygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) →
    STConStInd sz0 𝔠d (fun _ => 1 / 10) (fun _ => 1 / 2) →
    STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2) →
    STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2) Cd ∧
        STDecayLoopUgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2))

end Inst

end RBM.BA

end
