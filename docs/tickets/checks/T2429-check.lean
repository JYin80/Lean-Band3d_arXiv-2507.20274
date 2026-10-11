/-
Release check for T2429 (dispatcher V3, Sun Oct 11 22:07 UTC 2026; DECISIONS §241).  BA-TL TL2b: T.10 (a), (b), (d), T.1 (iii), T.11 (i), (ii), (iv), (v)
(supervisor 1049 TLF-C1 and Suggestion; design T2413 F1, F2, F6, §2 D2).  Section 1: merged names (`main` e6fc599).  Section 2: the
shapes of the `_holds` targets over the merged TL0 pins and the consumer's instantiation at `STCaseI`/`STCaseII` (Prop values; the
new T.1 (iii) pin `BATwKDecay` is fixed by the probe step, not here).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2429-check.lean
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.EKPins
import RBM3D.BA.EKNonzero
import RBM3D.BA.Prop6Path
import RBM3D.BA.FlowPins
import RBM3D.BA.CombesThomas
import RBM3D.BA.GreenSchur
import RBM3D.BA.KInduct
import RBM3D.BA.MFixedPoint
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step2Gen
import RBM3D.Induction.KDecay
import RBM3D.Induction.Contract
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step1Setup
import RBM3D.Kernel.Evolution
import RBM3D.Defs.Params
import RBM3D.Defs.Sizes

-- Section 1a: the TL0 pins proved here, the frame and the objects of T.11 (`BA/TwistPins.lean`)
#check @RBM.BA.BATwKerA
#check @RBM.BA.BATwKerFar
#check @RBM.BA.BATwKerZero
#check @RBM.BA.BATwistSrc1
#check @RBM.BA.BATwistSrc2
#check @RBM.BA.BATwistSrc4
#check @RBM.BA.BATwistSrc5
#check @RBM.BA.BATwFrame
#check @RBM.BA.twSteps
#check @RBM.BA.twSrc
#check @RBM.BA.twDec
#check @RBM.BA.twB1
#check @RBM.BA.twB2
#check @RBM.BA.twEG
#check @RBM.BA.twEE
#check @RBM.BA.twL3
#check @RBM.BA.twL2'
#check @RBM.BA.twK
#check @RBM.BA.twK_ba
#check @RBM.BA.twK_bound
#check @RBM.BA.twK_bound_holds
#check @RBM.BA.twFold_holds
#check @RBM.BA.twWard_holds
-- downstream (TL2d/TL2e): the step the sources feed
#check @RBM.BA.BATwistLoopStep

-- Section 1b: kernel inputs (stage E, Prop 5/8, `M^{(B)}` decay)
#check @RBM.BA.BAuKer
#check @RBM.BA.BAuKer_eq_one_add
#check @RBM.BA.baEKSumNdecay_holds
#check @RBM.BA.BAEKXiBall
#check @RBM.BA.baEKXiBall_holds
#check @RBM.BA.baEKSameRow_holds
#check @RBM.BA.BAEKSumDecayNonzero
#check @RBM.BA.baEKSumDecayNonzero_holds
#check @RBM.BA.BAProp5
#check @RBM.BA.baProp5_holds
#check @RBM.BA.BAProp8
#check @RBM.BA.baProp8_holds
#check @RBM.BA.BAMB_decay_large
#check @RBM.BA.BAReal
#check @RBM.projMat
#check @RBM.ellT
#check @RBM.zdistD
#check @RBM.Gauss.zdistInf

-- Section 1c: the carrier, the flow, the stochastic inputs of T.11
#check @RBM.BA.PrecL
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BALloop
#check @RBM.BA.baKsol_one
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.stSumTwoLoop_exists
#check @RBM.Gauss.Sizes.STContractM
#check @RBM.Gauss.Sizes.stContractM_holds
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII

-- Section 1d: instance data
#check @RBM.BA.MFixedPointInst.FlowPt
#check @RBM.BA.MFixedPointInst.exists_flowPt
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const

-- Section 2: target shapes (Prop values, no proofs)
namespace RBM.BA.T2429Check

/-- Targets 1 (T.10 (a), (b), (d)): the quantifier shape of `baEKSameRow_holds`; the pins carry `3 ≤ d → 0 < Λ → 0 < κ → …`. -/
def T2429_KerA : Prop := ∀ (d : ℕ) (Λ κ : ℝ), RBM.BA.BATwKerA d Λ κ
def T2429_KerFar : Prop := ∀ (d : ℕ) (Λ κ : ℝ), RBM.BA.BATwKerFar d Λ κ
def T2429_KerZero : Prop := ∀ (d : ℕ) (Λ κ : ℝ), RBM.BA.BATwKerZero d Λ κ

/-- Targets 3 (T.11 (i), (ii), (iv), (v)): for every regime `R`. -/
def T2429_Src1 : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), RBM.BA.BATwistSrc1 d R
def T2429_Src2 : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), RBM.BA.BATwistSrc2 d R
def T2429_Src4 : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), RBM.BA.BATwistSrc4 d R
def T2429_Src5 : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), RBM.BA.BATwistSrc5 d R

/-- The consumer's instantiation (TL2d: the two cases of `3_5:1105`). -/
example : Prop := RBM.BA.BATwistSrc1 3 RBM.Gauss.Sizes.STCaseI
example : Prop := RBM.BA.BATwistSrc5 3 RBM.Gauss.Sizes.STCaseII

end RBM.BA.T2429Check
