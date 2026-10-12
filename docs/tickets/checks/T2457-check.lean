/-
Release check for T2457 (dispatcher V3, Mon Oct 12 13:50 UTC 2026; DECISIONS §266).  Sub-stage U row U3s1 (ST side, vocabulary, additive):
the generic Step 3-4 vocabulary of `Induction/Step34Pins.lean` and `Induction/Step34PinsP.lean` over the carrier, in the
new files `Chain/Step34Gen.lean` and the leaf `Chain/Step34GenTw.lean`; the two band files are not edited (supervisor
1152 U-C2, F5).
Part 1: merged names.  Part 2: content-binding pins: `T2457_LmaxUgL`, `T2457_LKUgL` (conjuncts 2-3 of `twSteps`,
`BA/TwistPins.lean:135-138`, verbatim; supervisor 1049 TLF-C5), `T2457_Step3RgL`, `T2457_Step4RgL`; `T2457_EKDecaygL`,
`T2457_EKLowgL` (binding unless the 1a's D3 (b) adds a coupling argument; then their band reading must be these pins by
definitional unfoldings).  Part 3: shapes, not binding: `T2457_IngRgL` (D2), `T2457_EKSumRes2gL` (D3) and every `example`.
The TLF-C5 examples (definitional unfoldings, projections) are 1b targets in `Chain/Step34GenTw.lean`; this file pins only their
`Prop` shape.  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2457-check.lean
-/
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.Step2Kern
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step34PinsP
import RBM3D.Induction.DecayLoopA
import RBM3D.Induction.Contract
import RBM3D.Induction.NewPQ
import RBM3D.Evolution.Prec
import RBM3D.BA.TwistPins
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.EKPins
import RBM3D.BA.EKSum
import RBM3D.BA.EKNonzero
import RBM3D.Gauss.BlockAnderson

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- band originals in `Step34Pins` / `Step34PinsP` that get a generic form (targets 1-7)
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STLmax_of_STLmaxU
#check @RBM.Gauss.Sizes.STLK_of_STLKU
#check @RBM.Gauss.Sizes.STmaxL
#check @RBM.Gauss.Sizes.STmaxLK
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STsupXiLK
#check @RBM.Gauss.Sizes.STLKtensor
#check @RBM.Gauss.Sizes.STLI
#check @RBM.Gauss.Sizes.STKI
#check @RBM.Gauss.Sizes.STLKI
#check @RBM.Gauss.Sizes.STksimLK
#check @RBM.Gauss.Sizes.STelklk
#check @RBM.Gauss.Sizes.STavgErr
#check @RBM.Gauss.Sizes.STegt
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STSEforLnConcl
#check @RBM.Gauss.Sizes.STXiBoot
#check @RBM.Gauss.Sizes.STNQConcl
#check @RBM.Gauss.Sizes.STNQConcl'
#check @RBM.Gauss.Sizes.STIterHyp
#check @RBM.Gauss.Sizes.STWardTypeP
#check @RBM.Gauss.Sizes.STB45
#check @RBM.Gauss.Sizes.STStep3R
#check @RBM.Gauss.Sizes.STStep4R
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STIterR
#check @RBM.Gauss.Sizes.STSEforLn
#check @RBM.Gauss.Sizes.STOeqNQ
#check @RBM.Gauss.Sizes.STWardTypePPin
#check @RBM.Gauss.Sizes.STB45Pin
#check @RBM.Gauss.Sizes.STNewPQ
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.Gauss.Sizes.STEKLow
#check @RBM.Gauss.Sizes.STEKSumNdecay
#check @RBM.Gauss.Sizes.STEKSumRes1
#check @RBM.Gauss.Sizes.STEKSumRes2NAL
#check @RBM.Gauss.Sizes.STEKSumRes2
#check @RBM.Gauss.Sizes.STEKNonzero
-- model-free: reused, no generic form
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STPsi
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STAII
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STIdiff
#check @RBM.Gauss.Sizes.STeeLoop
#check @RBM.Gauss.Sizes.STn12E
#check @RBM.Gauss.Sizes.STn12
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STRegIterI
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.Gauss.Sizes.STAlternating
#check @RBM.Gauss.Sizes.STEKWin
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.STContract
#check @RBM.Gauss.Sizes.STContractM
#check @RBM.Gauss.Sizes.stContractM_holds
-- superseded (`Test/Axioms.lean` `supersededProps`): no generic form
#check @RBM.Gauss.Sizes.STStep3
#check @RBM.Gauss.Sizes.STStep4
#check @RBM.Gauss.Sizes.STStep3I
#check @RBM.Gauss.Sizes.STOeqQt
#check @RBM.Gauss.Sizes.STOeqQtNZ
#check @RBM.Gauss.Sizes.STIterations
#check @RBM.Gauss.Sizes.STIterationsII
#check @RBM.Gauss.Sizes.STOeqNQ'
#check @RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ
-- the band theorems of the band instances (targets 6-7) and the band data
#check @RBM.Gauss.Sizes.stek_sumNdecay_holds
#check @RBM.Gauss.Sizes.stek_sumRes1_holds
#check @RBM.Gauss.Sizes.stek_sumRes2NAL_holds
#check @RBM.Gauss.Sizes.stek_sumRes2_holds
#check @RBM.Gauss.Sizes.stek_nonzero_holds
#check @RBM.Gauss.Sizes.stNewPQ_holds
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.mSigma
#check @RBM.PropSpin
#check @RBM.EKsgn
#check @RBM.UN
#check @RBM.ThetaN
#check @RBM.zeroModeSet
#check @RBM.EKFastDecay
#check @RBM.EKSumZero
#check @RBM.Gauss.loopL
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.LoopIdx
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.lemT
#check @RBM.Gauss.Step34Inst.inst_step3R
#check @RBM.Gauss.Step34Inst.inst_step4R
#check @RBM.Gauss.Step34Inst.InstStep3Concl
#check @RBM.Gauss.Step34Inst.InstStep4Concl
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34PInst.inst_OeqNQ'
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.flow_z0
-- the carrier, the T8 / T8b vocabulary and kernels, the generic pins that already exist
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.STLKgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.Carrier_ofFn_ext
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STLocalEntryUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.bandFM_STStep2Concl
#check @RBM.BA.bandFM_STKward
#check @RBM.BA.STStep2G
#check @RBM.BA.STStep2_iff
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Kern_UN_band
#check @RBM.BA.Step2Kern_ThetaN_band
#check @RBM.BA.STmsigg
#check @RBM.BA.STLIMg
#check @RBM.BA.STLKIMg
#check @RBM.BA.STksimLKMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STavgErrMg
#check @RBM.BA.STegtMg
#check @RBM.BA.STeeMg
#check @RBM.BA.bandStep2_STLIM
#check @RBM.BA.bandStep2_STegtM
#check @RBM.BA.bandStep2_STeeM
-- band bridges in `BA/FlowPins` that `Chain/Step34Gen` cannot import (re-derived by unfolding there)
#check @RBM.BA.bandFM_STLK
#check @RBM.BA.bandFM_STLmax
#check @RBM.BA.bandFM_STKbound
#check @RBM.BA.bandFM_STStep1Loop
-- the TL consumer (TLF-C5) and the BA readings (statement level here; proofs: U3-BA)
#check @RBM.BA.twSteps
#check @RBM.BA.BATwFrame
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baStep2Mat
#check @RBM.BA.BAStep2
#check @RBM.BA.STMainIndG
#check @RBM.BA.BAUN
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.BAEKSumNdecay
#check @RBM.BA.BAEKSumDecay1
#check @RBM.BA.baEKSumNdecay_holds
#check @RBM.BA.baEKSumDecay1_holds
#check @RBM.BA.baEKSumDecayNAL_holds
#check @RBM.BA.baEKSumDecay2_holds
#check @RBM.BA.baEKSumDecayNonzero_holds
#check @RBM.Gauss.Sizes.seqHflowBA
-- measure-level vocabulary
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.Sizes.Whp
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.STdiamInf
#check @RBM.ellT

/-! ## Part 2: the content-binding pins -/

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1, `STLmaxUgL`** (content binding; supervisor 1049 TLF-C5): the carrier form of `STLmaxU`
(`Induction/Step34Pins.lean:176`) is conjunct 2 of `twSteps` (`BA/TwistPins.lean:135-136`) verbatim. -/
def T2457_LmaxUgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))

/-- **Target 1, `STLKUgL`** (content binding; TLF-C5): the carrier form of `STLKU` (`Step34Pins.lean:184`) is conjunct 3
of `twSteps` (`BA/TwistPins.lean:137-138`) verbatim. -/
def T2457_LKUgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)

/-- **Target 5, Step 3 per regime over a carrier** (content binding): `STStep3R` (`Step34Pins.lean:250`) in the shape of
`STStep2G` (`Chain/Step2Gen.lean:591`, `(law, Flow, mk, T0)`); the band order of binders and premises is kept. -/
def T2457_Step3RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STKwardgL (mk sz z) (law sz) →
          STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t → STStep1LoopgL (mk sz z) (law sz) s t →
          STStep2ConclgL (mk sz z) (law sz) s t Cd → T2457_LmaxUgL (mk sz z) (law sz) s t

/-- **Target 5, Step 4 per regime over a carrier** (content binding): `STStep4R` (`Step34Pins.lean:261`). -/
def T2457_Step4RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STKwardgL (mk sz z) (law sz) →
          STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t → STStep1LoopgL (mk sz z) (law sz) s t →
          STStep2ConclgL (mk sz z) (law sz) s t Cd → T2457_LmaxUgL (mk sz z) (law sz) s t →
          T2457_LKUgL (mk sz z) (law sz) s t

/-- **Target 6, `STEKDecaygL`** (binding, see the header): `STEKDecay` (`Step34Pins.lean:595`) at a law `μ`
(`Whp sz = HighProbAt (seqP sz) sz.size`).  T7 (T2454 target 7, `stEtermDecaygL`) reads it. -/
def T2457_EKDecaygL {d : ℕ} {sz : Sizes d} (μ : Measure sz.SeqΩ) {m : ℕ} (s t : ℕ → ℝ)
    (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D →
    HighProbAt μ sz.size (fun n => {ω | ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D (𝒜 n v ω)})

/-- **Target 6, `STEKLowgL`** (binding, see the header): `STEKLow` (`Step34Pins.lean:602`) at a law `μ`. -/
def T2457_EKLowgL {d : ℕ} {sz : Sizes d} (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ)
    (X : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) : Prop :=
  ∃ b : ℝ, HighProbAt μ sz.size (fun n => {ω | ∀ v : TimeIcc s t n, ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v ω})

/-! ## Part 3: shapes (not binding) -/

/-- TLF-C5 (target 8, the example itself is a 1b target in `Chain/Step34GenTw.lean`): `twSteps` is Step 2's conclusion,
target 1 (conjuncts 2-3) and conjunct 4 (verbatim here; T7's `STDecayLoopUgL`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ),
  twSteps C μ s t Cd ↔
    (STStep2ConclgL C μ s t Cd ∧ T2457_LmaxUgL C μ s t ∧ T2457_LKUgL C μ s t ∧
      (∀ k : ℕ, 1 ≤ k → ∀ τ' D' : ℝ, 0 < τ' → 0 < D' →
        PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
          (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
            (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
          (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))))

/-- TLF-C5, the two projections (target 8). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ),
  (twSteps C μ s t Cd → T2457_LmaxUgL C μ s t) ∧ (twSteps C μ s t Cd → T2457_LKUgL C μ s t)

/-- Target 1, band bridges (definitional equality expected: `Prec sz = PrecL sz (seqP sz)`, `(bandFM sz E).L = Lloop sz · (E ·)`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E s t : ℕ → ℝ),
  (STLmaxU sz E s t ↔ T2457_LmaxUgL (bandFM sz E) (Sizes.seqP sz) s t) ∧
    (STLKU sz E s t ↔ T2457_LKUgL (bandFM sz E) (Sizes.seqP sz) s t)

/-- Target 1, the endpoints `u = t` (band `STLmax_of_STLmaxU`, `STLK_of_STLKU`, `Step34Pins.lean:284, 291`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ), (∀ n, s n ≤ t n) →
  (T2457_LmaxUgL C μ s t → STLmaxgL C μ t) ∧ (T2457_LKUgL C μ s t → STLKgL C μ t)

/-- Target 3 (D1, default): the list-indexed loops and ℰ-terms at a sample are T8's matrix forms at the flow matrix;
band bridges by `rfl` at `Hf = seqHflow sz`. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))),
  STLI sz n (E n) τ ω I = STLIMg (bandStep2Mat sz E) n τ (seqHflow sz n τ ω) I ∧
    STegt sz n (E n) τ ω I = STegtMg (bandStep2Mat sz E) n τ (seqHflow sz n τ ω) I

/-- Target 3 (D1), the quadratic-variation loop. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (m : ℕ) (σ : Fin m → Bool)
    (a a' : Fin m → Zd d (sz.L n)),
  STee sz n (E n) τ ω σ a a' = STeeMg (bandStep2Mat sz E) n τ (seqHflow sz n τ ω) σ a a'

/-- Target 3, the compatibility facts `Step34Gen_LCompat`, `Step34Gen_KCompat` at the band (proved here:
`loopM_eq_loopL`, `Lloop`; `STKloop` is `KLK ∘ KLloopOf`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (t : ℝ) (k : ℕ) (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ),
  (bandStep2Mat sz E).L n t σ a ω = (bandStep2Mat sz E).LIM n t (seqHflow sz n t ω) (KLloopOf d (sz.L n) σ a) ∧
    (bandStep2Mat sz E).K n t σ a = (bandStep2Mat sz E).KI n t (KLloopOf d (sz.L n) σ a)

/-- Target 3, the same at the BA carrier (statement level; owed by U3-BA). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (k : ℕ) (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ),
  (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).L n t σ a ω =
    (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).LIM n t (sz.seqHflowBA (BAflowLam0 sz z) n t ω)
      (KLloopOf d (sz.L n) σ a)

/-- Targets 4, 6 (U-C4, E-C1): the band readings of the two carrier kernels that `STB45gL` and the five `STEK*gL` read
(proved bridges: `Step2Kern_ThetaN_band`, `Step2Kern_UN_band`, `mSigma E = PropSpin (mE E)`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ)
    (A : (Fin k → Zd d (sz.L n)) → ℂ),
  Step2Gen_ThetaN (bandFM sz E) n σ t A = ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (E n)) σ) t A ∧
    Step2Gen_UN (bandFM sz E) n σ s t A = UN d (sz.L n) (sz.lam n) (EKsgn (mE (E n)) σ) s t A

/-- Target 5, band bridge of Step 3 (proved: `bandFM_STKward` is not definitional); Step 4 likewise. -/
example : Prop := ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
  (STStep3R d R ↔ T2457_Step3RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) ∧
  (STStep4R d R ↔ T2457_Step4RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))

/-- Target 5 at the BA reading of `BAStep2` (`BA/FlowPins.lean:432`; statement level; proofs: U3s4, U3-BA). -/
example : Prop := ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
  T2457_Step3RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
    T2457_Step4RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- **Target 5 (D2, default; shape, not binding)**: the setting `STIngR` (`Step34Pins.lean:445`) over a carrier family;
the conclusion reads `(sz, z)`, so an instance can read `mk sz z`, its `Step2Mat` extension and the flow matrix. -/
def T2457_IngRgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Concl : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STKwardgL (mk sz z) (law sz) →
          STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t →
          STStep2ConclgL (mk sz z) (law sz) s t Cd → Concl sz z s t

/-- Target 5 (D2), band bridge of the setting (proved, through `bandFM_STKward`). -/
example : Prop := ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
  STIngR d R Concl ↔ T2457_IngRgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z s t => Concl sz (STflowE z) s t)

/-- Target 6, band bridges (definitional equality expected: `Whp sz = HighProbAt (seqP sz) sz.size`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (m : ℕ) (s t : ℕ → ℝ)
    (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) (X : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ),
  (STEKDecay sz s t 𝒜 ↔ T2457_EKDecaygL (Sizes.seqP sz) s t 𝒜) ∧ (STEKLow sz s t X ↔ T2457_EKLowgL (Sizes.seqP sz) s t X)

/-- **Target 6 (D3, default; shape, not binding)**: `(sum_res_2)` (`STEKSumRes2`, `Step34Pins.lean:651`) over the carrier
kernel `Step2Gen_UN C` (E-C1) for the carriers of a class `Ker sz C κ`, in place of `∀ m, ‖m n‖ = 1 → κ ≤ Im m n`.  The other
four forms follow the same pattern.  D3 (b): the coupling read by `STEKWin`, the decay hypothesis and the ratio is `sz.lam`
here; stage E's BA theorems read the kernel coupling `lam0` (see the ticket). -/
def T2457_EKSumRes2gL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Ker : ∀ sz : Sizes d, FlowFM sz → ℝ → Prop) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ s t : ℕ → ℝ, STEKWin sz s t → ∀ C : FlowFM sz, Ker sz C κ → ∀ σ : Fin n_ → Bool,
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), T2457_EKDecaygL (law sz) s t 𝒜 →
    (∀ n v ω, EKSumZero (𝒜 n v ω)) →
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), T2457_EKLowgL (law sz) s t X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n)
        (fun n v ω => ‖Step2Gen_UN C n σ (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ n_ * X n v ω)

/-- Target 6 (D3), the band instance: the merged band pin gives the generic form at the band class (proved in the 1b from
`stek_sumRes2_holds`; the band hypotheses `|E n| ≤ 2`, `mE` are allowed in the band class only). -/
example : Prop := ∀ d : ℕ, STEKSumRes2 d →
  T2457_EKSumRes2gL d (fun sz => Sizes.seqP sz)
    (fun sz C κ => ∃ E : ℕ → ℝ, C = bandFM sz E ∧ ∀ n, |E n| ≤ 2 ∧ κ ≤ (mE (E n)).im)

end RBM.BA

end
