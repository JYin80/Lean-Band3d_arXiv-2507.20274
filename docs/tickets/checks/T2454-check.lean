/-
Release check for T2454 (dispatcher V3, Mon Oct 12 12:24 UTC 2026; DECISIONS §264).  BA-T T7 (sub-stage T, ST side): `lem_decayLoop` and the Step 2 events
over the carrier.  Layout (A): new `Chain/DecayGen`, `Chain/Step2EventsGen` and the leaf `Chain/DecayGenTw`; the band files
`Induction/DecayLoopA`, `DecayLoopB`, `Step2Events` are not edited.
Part 1: merged names.  Part 2: `T2454_DecayLoopUgL` is content binding (conjunct 4 of `twSteps`, `BA/TwistPins.lean:139-142`,
verbatim; supervisor 1049 TLF-C5).  `T2454_KcalDecaygL` and every `example` are shapes (not binding).  The TLF-C5 examples (definitional
equality with `twSteps`) are 1b targets in `Chain/DecayGenTw.lean`; this file pins only their `Prop` shape.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2454-check.lean
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.LWPinsBA
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.LWGen
import RBM3D.Induction.DecayLoopA
import RBM3D.Induction.DecayLoopB
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Core
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.KDecay
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.B45
import RBM3D.Induction.SEforLn2
import RBM3D.Graph.LWPins
import RBM3D.Evolution.Pins
import RBM3D.Defs.StochDomAt

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the band pins and results of `DecayLoopA`, `DecayLoopB` (targets 1-7)
#check @RBM.Gauss.Sizes.STdiamInf
#check @RBM.Gauss.Sizes.STDecayLoopAt
#check @RBM.Gauss.Sizes.STDecayLoopPT
#check @RBM.Gauss.Sizes.STDecayLoopU
#check @RBM.Gauss.Sizes.stDecayLoopAt_holds
#check @RBM.Gauss.Sizes.stDecayLoopPT_of_step2
#check @RBM.Gauss.Sizes.stDecayLoopU_of_step2
#check @RBM.Gauss.Sizes.stEtermDecay
#check @RBM.Gauss.Sizes.DecayLoopA_diam_le_KLmaxDist
#check @RBM.Ind.LoopDecay
#check @RBM.Ind.DecayLoopB_card_ball
-- the band inputs: the Step 2 decay, the far decay of `𝒦`, `STEKDecay` and the ℰ-terms
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep2DecayPT
#check @RBM.Gauss.Sizes.STKcalDecay
#check @RBM.Gauss.Sizes.stKcalDecay_holds
#check @RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible
#check @RBM.Gauss.Sizes.stKbound_timeIcc
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Loop.KLK
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLmaxDist
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.EKFastDecay
#check @RBM.Gauss.Sizes.STegt
#check @RBM.Gauss.Sizes.STksimLK
#check @RBM.Gauss.Sizes.STelklk
#check @RBM.Gauss.Sizes.STee
-- the band events of `Step2Events`, the good event of `Step2Core`, the L bridges (targets 8-11)
#check @RBM.Gauss.Sizes.STScaleInv
#check @RBM.Gauss.Sizes.ST_LW_sections
#check @RBM.Gauss.Sizes.ST_event_weak
#check @RBM.Gauss.Sizes.ST_event_init
#check @RBM.Gauss.Sizes.ST_event_lw
#check @RBM.Gauss.Sizes.ST_event_mg
#check @RBM.Gauss.Sizes.ST_good_prob
#check @RBM.Gauss.Sizes.STGoodAt
#check @RBM.Gauss.Sizes.STBdata
#check @RBM.Gauss.Sizes.ST_Bdata_holds
#check @RBM.Gauss.Sizes.STLWB_of_LWterm
#check @RBM.Gauss.Sizes.STLWT_of_LWtermExp
#check @RBM.Gauss.Sizes.LWterm
#check @RBM.Gauss.Sizes.LWtermExp
#check @RBM.Gauss.Sizes.LWAssm
#check @RBM.Gauss.Sizes.ST_flow_im_pos
#check @RBM.Gauss.Sizes.STprof
-- the carrier and the generic vocabulary (row 0, T8, T8b, T2, stage L)
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.PrecPTL
#check @RBM.BA.bandFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.Step2Data
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.bandStep2Data
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STStep2DecayPTgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.bandFM_STGdecayW
#check @RBM.BA.bandFM_STStep2DecayPT
#check @RBM.BA.STDecaygL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.STLWassmExpgL
#check @RBM.BA.STLWBgL
#check @RBM.BA.STLWTgL
#check @RBM.BA.STEMn2ExpgL
#check @RBM.BA.STgAg
#check @RBM.BA.STgDriftg
#check @RBM.BA.STGMMg
#check @RBM.BA.STLKMg
#check @RBM.BA.STEGtMg
#check @RBM.BA.STEEMg
#check @RBM.BA.STJhatMg
#check @RBM.BA.STegtMg
#check @RBM.BA.STksimLKMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STeeMg
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.LWtermG
#check @RBM.BA.LWtermExpG
#check @RBM.BA.bandPin
#check @RBM.BA.STLWB_bandPin
#check @RBM.BA.STLWT_bandPin
-- the TL consumer (TLF-C5) and the BA carrier (T7-BA)
#check @RBM.BA.twSteps
#check @RBM.BA.BATwFrame
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_LM
#check @RBM.BA.BASTLWB
#check @RBM.BA.BASTLWT
-- the U2 consumers (1152 F4)
#check @RBM.Gauss.Sizes.stB45Pin_holds
#check @RBM.Gauss.Sizes.stSEforLn_holds
-- measure-level vocabulary
#check @RBM.ellT
#check @RBM.Path.TimeIcc
#check @RBM.Path.gridTime
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT

/-! ## Part 2: the pinned statement (content binding) and shapes (not binding) -/

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1** (content binding; supervisor 1049 TLF-C5): the carrier form of `STDecayLoopU` (`Induction/DecayLoopB.lean:792`) is
conjunct 4 of `twSteps` (`BA/TwistPins.lean:139-142`) verbatim, the binder order `∀ τ' D' : ℝ, 0 < τ' → 0 < D' →` included.
`STDecayLoopUgL C μ s t` of `Chain/DecayGen.lean` must be definitionally equal to it. -/
def T2454_DecayLoopUgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ' D' : ℝ, 0 < τ' → 0 < D' → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

/-- TLF-C5 (shape only; the example itself is target 12, in `Chain/DecayGenTw.lean`): `twSteps` is Step 2's conclusion,
conjuncts 2-3 (the carrier forms of `STLmaxU`, `STLKU`, which U3s1 names later; here verbatim) and target 1. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ),
  twSteps C μ s t Cd ↔
    (STStep2ConclgL C μ s t Cd ∧
      (∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))) ∧
      (∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)) ∧
      T2454_DecayLoopUgL C μ s t)

/-- TLF-C5, the projection (shape only; target 12's second example). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ),
  twSteps C μ s t Cd → T2454_DecayLoopUgL C μ s t

/-- Target 1, band bridge (shape; proved in the 1b, not definitional: the band binder order is `∀ τ', 0 < τ' → ∀ D', 0 < D'`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E s t : ℕ → ℝ),
  STDecayLoopU sz E s t ↔ T2454_DecayLoopUgL (bandFM sz E) (Sizes.seqP sz) s t

/-- Target 1 at the BA carrier and law (shape; T7-BA proves it from target 6 after U2-BA's `BAKcalDecay`, supervisor 1155 C8). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
  T2454_DecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- Target 2 (shape): the window form per time over `PrecPTL`, in the binder order of `STDecayLoopPT` (`DecayLoopA.lean:106`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ),
  ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

/-- **Target 3** (shape, not binding): the far decay of `𝒦` over a carrier, the consumer form of `inst_stKcalDecay_admissible`
(`Induction/KDecay.lean:976`) at the carrier's energy (no `∀ E, |E| ≤ 2 - κ`).  The 1a may change the far metric (`ℓ¹` `KLmaxDist`
here) or the window, and says why. -/
def T2454_KcalDecaygL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D →
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ ≤ (RBM.Loop.KLmaxDist d (sz.L n) a : ℝ) →
        ‖C.K n u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- Target 3, band reading (shape; proved in the 1b from `inst_stKcalDecay_admissible`; band hypotheses are allowed here only). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (κ 𝔠 𝔡 : ℝ), 3 ≤ d → 0 < κ → sz.Admissible 𝔠 𝔡 →
  (∀ n, |E n| ≤ 2 - κ) → T2454_KcalDecaygL (bandFM sz E)

/-- Target 6, route (shape, not binding): the uniform Step-2 decay, the far decay of `𝒦` and the carrier facts `F` (the 1a's
table) give target 1 on `[s,t]`. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ) (F : Prop),
  F → STGdecayWgL C μ s t Cd → T2454_KcalDecaygL C → T2454_DecayLoopUgL C μ s t

/-- Target 8 (shape; a definitional bridge to `STScaleInv` at `bandFM` is expected): `(eq:LW_assm_exp)` at the scale family at every
time section. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ),
  ∀ (tt : ∀ n, TimeIcc s t n) (D : ℝ), 0 < D → STLWassmExpgL C μ (fun n => (tt n : ℝ)) D (fun n => Kf n (tt n : ℝ))

/-- Target 9, (E1) (shape, not binding): the weak law on the grid over a `Step2Mat` carrier (band `ST_event_weak`,
`Step2Events.lean:609`, at `bandStep2Mat`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (δ₀ : ℝ),
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ x y,
    ‖STGMMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) x y‖ ≤ δ₀})

/-- Target 9, (E3) (shape, not binding): the factor `(mE (E n)).im * (1 - u)` of `ST_event_lw` (`Step2Events.lean:637`) becomes the
carrier's `eta`, as `STLWTgL` reads it. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (Kf : ℕ → ℝ → ℝ) (Λ : ℕ → ℝ),
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
    ‖STEGtMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ ≤
      Λ n / Cm.eta n (gridTime s T K n j) * (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)})

end RBM.BA

end
