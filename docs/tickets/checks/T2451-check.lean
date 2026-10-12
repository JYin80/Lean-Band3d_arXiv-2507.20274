/-
Release check for T2451 (dispatcher V3, Mon Oct 12 11:56 UTC 2026; DECISIONS §263).  BA-TL TL2e, the last row of stage TL: the net (S2) and the `Ξ` bootstrap close
`BATwistLoopStep` from TL2d's `BATwistStepFixed` (supervisor 1049 TLF-C2), for every regime, hence at `STCaseI` and `STCaseII`; T.13 (ii) with S3.
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2451_`; content binding): `T2451_TL2e` is `T2441_TL2e`
(`t/T2441:RBM3D/Probe/T2441Pins.lean:53-54`) verbatim; `T2451_TwKcircBound` is T.13 (ii) in the frame and `Bctl` form of `twK_bound`.
Then shapes (not binding) of the regimes, the route, the consumer and the instances.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2451-check.lean
-/
import RBM3D.BA.TwistStep
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistPins
import RBM3D.BA.TwistChain
import RBM3D.BA.TwistAvgB
import RBM3D.BA.TwistKer2
import RBM3D.BA.TwistFold2
import RBM3D.BA.Step1Setup
import RBM3D.BA.GreenSchur
import RBM3D.BA.MFixedPoint
import RBM3D.BA.EMn2BA
import RBM3D.BA.FlowPins
import RBM3D.Graph.BAExp14b
import RBM3D.Chain.Carrier
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Sizes
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step1Setup
import RBM3D.Induction.MainIndRegimes

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- target 1: TL2d's pin, its two instances, the step and the frame
#check @RBM.BA.BATwistStepFixed
#check @RBM.BA.baTwistStepFixed_caseI
#check @RBM.BA.baTwistStepFixed_caseII
#check @RBM.BA.BATwistLoopStep
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.BATwFrame
#check @RBM.BA.twSteps
#check @RBM.BA.twL2'
#check @RBM.BA.twK
#check @RBM.BA.PrecL
-- round 0 and the passage per time sequence -> per time
#check @RBM.BA.TwistStep_zcrude
#check @RBM.Gauss.Sizes.ST_prec_of_le_ev
#check @RBM.StochDomAt
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.perTimeDomAt_iff_forall_section
#check @RBM.Path.stochDomAt_of_perTimeDomAt
-- the net (S2): the abstract lift, the good event, the time modulus of `G` at the BA carrier, the Step-1 use of the same lift
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Gauss.HighProbAt
#check @RBM.BA.baGopbound
#check @RBM.BA.baG_continuousOn
#check @RBM.BA.baNetLift
#check @RBM.Gauss.Sizes.st6_precU_of_forall_seq
-- the contraction of the bootstrap
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.BA.twB0_ge
#check @RBM.BA.twB0_ge_holds
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baFMz
-- target 2: the regimes; the consumers (BA-V V2a/V2b, TL-V, L4b2)
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.st_caseI_of_reg5I
#check @RBM.Gauss.Sizes.st_caseI_of_reg5III
#check @RBM.Gauss.Sizes.st_caseII_of_reg5II
#check @RBM.Gauss.Sizes.st_caseII_of_reg5IV
#check @RBM.BA.BAMainIndTL
#check @RBM.BA.BAMLOutTL
#check @RBM.BA.BAChainTL
#check @RBM.BA.baChainTL_holds
#check @RBM.BA.BATwistLoopBase
#check @RBM.BA.baTwistLoopBase_holds
#check @RBM.BA.BATwistAvgProd
#check @RBM.BA.baTwistAvgProd_holds
#check @RBM.BA.BAExp14bS2
-- target 3: T.13 (ii) and S3
#check @RBM.BA.twK_bound
#check @RBM.BA.twK_bound_holds
#check @RBM.BA.twMB
#check @RBM.BA.twMB_ba
#check @RBM.BA.BAMsigma
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAflow_real
#check @RBM.BA.twCirc_holds
-- the instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
#check @RBM.BA.TwistStep2_szII
#check @RBM.BA.TwistStep2_zII
#check @RBM.BA.TwistStep2_flowII
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const
#check @RBM.Gauss.Step34Inst.conStInd_const

/-! ## Part 2: the target statements (content binding) and shapes (not binding) -/

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- **Target 1** (content binding): `T2441_TL2e` (`t/T2441:RBM3D/Probe/T2441Pins.lean:53-54`) verbatim.  The net (S2) and the
bootstrap use no regime: `BATwistStepFixed d R` gives `BATwistLoopStep d R`, every `d` and `R` (TP:171; supervisor 1049 TLF-C2). -/
def T2451_TL2e : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistStepFixed d R → BATwistLoopStep d R

/-- **Target 3** (content binding; T.13 (ii) with S3, TP:189, supervisor 0652 `:129`): the circled twisted tree
`K̃^∘ = K̃ − W^{-d} M^{(B)}(σ₂)_{a c₁} M^{(B)}(σ₁)_{c₂ a}` (the identity part of `Θ` in `twK`) satisfies
`‖K̃^∘‖ ≤ C Bctl` and `Σ_a ‖K̃^∘‖ ≤ C (W^d η)⁻¹`.  Frame, window and `Bctl` form of `twK_bound` (`TwistPins:122`; design D3: no decay
in `|a − c₁|` is needed); `C` depends on `(d, κ, ε, 𝔡)` only. -/
def T2451_TwKcircBound (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
        (∀ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
            BAMsigma d (sz.L n) (twMB (baFMz sz z) n) (σ 1) a c₁ * BAMsigma d (sz.L n) (twMB (baFMz sz z) n) (σ 0) c₂ a‖ ≤
          C * sz.Bctl n (t n)) ∧
        ∑ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
            BAMsigma d (sz.L n) (twMB (baFMz sz z) n) (σ 1) a c₁ * BAMsigma d (sz.L n) (twMB (baFMz sz z) n) (σ 0) c₂ a‖ ≤
          C * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹

/-- Target 1 as a Prop value. -/
example : Prop := T2451_TL2e

/-- Target 2 as a Prop value (the two regimes of TL2d's target 3). -/
example : Prop := ∀ d : ℕ, BATwistLoopStep d STCaseI ∧ BATwistLoopStep d STCaseII

/-- Route of target 2 (not binding): target 1 at the two merged instances of `BATwistStepFixed`. -/
example : Prop := T2451_TL2e → (∀ d : ℕ, BATwistStepFixed d STCaseI) → (∀ d : ℕ, BATwistStepFixed d STCaseII) →
  ∀ d : ℕ, BATwistLoopStep d STCaseI ∧ BATwistLoopStep d STCaseII

/-- Target 3 as a Prop value, and its route from `twK_bound` (not binding). -/
example : Prop := ∀ d : ℕ, T2451_TwKcircBound d
example : Prop := ∀ d : ℕ, twK_bound d → T2451_TwKcircBound d

/-- Consumer (not this row): V2a's target `BAMainIndTL d R` at the four band regimes (supervisor 1049 `:93`), the premise
`BAMainIndTL d STAny` of `BAChainTL` after V2b's glue (`:94`). -/
example : Prop := ∀ d : ℕ, BAMainIndTL d STReg5I ∧ BAMainIndTL d STReg5II ∧ BAMainIndTL d STReg5III ∧ BAMainIndTL d STReg5IV
example : Prop := ∀ d : ℕ, BAMainIndTL d STAny

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst in
/-- Target 4 shape, `STCaseI` at `sz0`, `s ≡ 1/2`, `t ≡ 2/3` (`t0_sz0`): `twSteps` and TL2 at `s` stay hypotheses; TL2 at every
`τ ∈ [s,t]`. -/
example : Prop := ∀ Cd : ℝ, 0 < Cd →
  twSteps (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) Cd →
  BATwistLoopLaw (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) →
  ∀ τ : ℕ → ℝ, (∀ n, 1 / 2 ≤ τ n) → (∀ n, τ n ≤ 2 / 3) → BATwistLoopLaw (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) τ

/-- Target 4 shape, `STCaseII` at `TwistStep2_szII`, `s ≡ 0`, `t ≡ 1/2000` (`TwistStep2_flowII`). -/
example : Prop := ∀ Cd : ℝ, 0 < Cd →
  twSteps (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) Cd →
  BATwistLoopLaw (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) →
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n ≤ 1 / 2000) →
    BATwistLoopLaw (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) τ

end RBM.BA

end
