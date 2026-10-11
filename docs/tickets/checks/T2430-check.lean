/-
Release check for T2430 (dispatcher V3, Sun Oct 11 22:07 UTC 2026; DECISIONS §241).  BA-TL TL2c: T.11 (iii), the quadratic variation of the
twisted 2-loop, `BATwistSrc3` at BA by the Schatten trick (supervisor 1049 TLF-C1; design T2413 §2, §7, §8).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2430-check.lean
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.FlowPins
import RBM3D.BA.EMn2BA
import RBM3D.Chain.Carrier
import RBM3D.Induction.Contract
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.ContractPt
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step1Setup
import RBM3D.Loop.GLoopFlow
import RBM3D.Defs.Sizes
import RBM3D.Defs.StochDomAt

#check @RBM.BA.BATwistSrc3
#check @RBM.BA.BATwFrame
#check @RBM.BA.twSteps
#check @RBM.BA.twEE
#check @RBM.BA.twDer
#check @RBM.BA.twSrc
#check @RBM.BA.twBlk
#check @RBM.BA.twShift
#check @RBM.BA.twChg
#check @RBM.BA.twFold_holds
#check @RBM.BA.twWard_holds
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAGt
#check @RBM.BA.BALloop
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.Gauss.Sizes.STContractM
#check @RBM.Gauss.Sizes.stContractM_holds
#check @RBM.Gauss.Sizes.Contract_maxLoopM
#check @RBM.Gauss.Sizes.STContractPt
#check @RBM.Gauss.Sizes.stContractPt_holds
#check @RBM.BA.BAContractAt
#check @RBM.BA.baSTContractM
#check @RBM.BA.baSTContractM_flow
#check @RBM.BA.baEMn2PolyFacts
#check @RBM.BA.baEMn2ExpFacts
#check @RBM.BA.EMn2BA_mim_pos
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.Gauss.ztOf_im
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STAny
#check @RBM.StochDomAt.of_subset_union
#check @RBM.StochDomAt.mul
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const

/-- The target of T2430: the pin `BATwistSrc3` for every regime `R` (T.11 (iii) uses no regime). -/
def T2430_Target (d : ℕ) : Prop :=
  ∀ R : (∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), RBM.BA.BATwistSrc3 d R

/-- The regimes of TL2d fit the parameter `R` (statement level). -/
example : Prop := RBM.BA.BATwistSrc3 3 RBM.Gauss.Sizes.STCaseI
example : Prop := RBM.BA.BATwistSrc3 3 RBM.Gauss.Sizes.STCaseII
example : Prop := T2430_Target 3

/-- The CS conjunct reads the carrier's block kernel; at BA it is `1` (`BA/FlowPins.lean:327`; statement only). -/
example : Prop := ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ) (n : ℕ), (RBM.BA.baFMz sz z).S n = 1
