/-
Release check for T2441 (dispatcher V3, Mon Oct 12 05:25 UTC 2026; DECISIONS §249).  BA-TL TL2d: T.12′ at one fixed time (all charges; regimes `STCaseI`,
`STCaseII`) with the `Ξ̃` bound as a hypothesis (new pin, fixed by the probe), T.12″ `BATwistZeroMode`, the corollary `baTwistGridMart_holds`.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2441-check.lean
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.TwistKer
import RBM3D.BA.TwistKer2
import RBM3D.BA.TwistQV
import RBM3D.BA.TwistAvgB
import RBM3D.BA.TwistGrid
import RBM3D.BA.TwistGrid2
import RBM3D.BA.TwistGridRem2
import RBM3D.BA.TwistGridTail2
import RBM3D.BA.TwistGridWTail2
import RBM3D.BA.EKPins
import RBM3D.BA.KBase
import RBM3D.BA.Ward
import RBM3D.BA.MFixedPoint
import RBM3D.BA.KInduct
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.LWGen
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Sizes
import RBM3D.Gauss.FineModel
import RBM3D.Induction.Defs
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step5Kit
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Core

-- target 1: the corollary (DECISIONS §242 (2))
#check @RBM.BA.BATwistGridMart
#check @RBM.BA.BATwistGridMartAt
#check @RBM.BA.BATwistGridAssemble
#check @RBM.BA.baTwistGridAssemble_holds
#check @RBM.BA.baTwistGridRem_holds
#check @RBM.BA.baTwistGridTail_holds
#check @RBM.BA.BATwistGridWTail
#check @RBM.BA.baTwistGridWTail_holds
-- target 2: T.12″ and its inputs
#check @RBM.BA.BATwistZeroMode
#check @RBM.BA.twK_ba
#check @RBM.BA.twMB_ba
#check @RBM.BA.BATheta_row_sum_pm
#check @RBM.BA.BATheta_conj
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAMsigma
-- target 3: the frame, the laws, TL2e's pin, the regimes
#check @RBM.BA.BATwFrame
#check @RBM.BA.twSteps
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.BATwistLoopStep
#check @RBM.BA.twL2'
#check @RBM.BA.twK
#check @RBM.BA.twSrc
#check @RBM.BA.PrecL
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.st5_conStInd_mono
-- T.10 and T.1 (iii)
#check @RBM.BA.baEKSameRow_holds
#check @RBM.BA.baTwKerFar_holds
#check @RBM.BA.baTwKerZero_holds
#check @RBM.BA.baTwKDecay_holds
#check @RBM.BA.twK_bound_holds
-- T.11
#check @RBM.BA.BATwistSrc4
#check @RBM.BA.baTwistSrc1_holds
#check @RBM.BA.baTwistSrc2_holds
#check @RBM.BA.baTwistSrc3_holds
#check @RBM.BA.baTwistSrc4_holds
#check @RBM.BA.baTwistSrc5_holds
-- case (C): Lemma T.3 and TL1 at `τ`
#check @RBM.BA.twWard_holds
#check @RBM.BA.BATwistAvgLaw
#check @RBM.BA.baTwistAvgProd_holds
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.baKsol_one
#check @RBM.StochDomAt.precomp_param
-- the grid walk: Duhamel 4 (a), T.9, the weights, back to the law
#check @RBM.BA.BATwistDuhamel_holds
#check @RBM.BA.BATwistHier_holds
#check @RBM.BA.twMart
#check @RBM.BA.twU
#check @RBM.BA.BAuKer_comp
#check @RBM.BA.BAuKer_eq_one_add
#check @RBM.BA.baStep2Mat_Pp
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.ST_grid_whp_of_sections
#check @RBM.Gauss.Sizes.ST_model_le_path
#check @RBM.Gauss.Sizes.ST_pathP_eq_seqP
-- the instance datum
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0

namespace RBM.BA.T2441Check
/-- Target 1 as a Prop value (every `d`). -/
example : Prop := ∀ d : ℕ, RBM.BA.BATwistGridMart d
/-- Target 2 as a Prop value. -/
example : Prop := ∀ d : ℕ, RBM.BA.BATwistZeroMode d
/-- TL2e's target at the two regimes of target 3 (not proved here). -/
example : Prop := ∀ d : ℕ, RBM.BA.BATwistLoopStep d RBM.Gauss.Sizes.STCaseI ∧ RBM.BA.BATwistLoopStep d RBM.Gauss.Sizes.STCaseII
end RBM.BA.T2441Check
