/-
Release check for T2428 (dispatcher V3, Sun Oct 11 22:07 UTC 2026; DECISIONS §241).  BA-TL TL2a: T.8 and T.9 in grid form, the twisted loop
hierarchy and its Duhamel form over the BA carrier `baStep2Mat` with T8b's kernels and `BAuKer` (supervisor 1049 TLF-C1,
TLF-C3; 0853 BAT-F1).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2428-check.lean
-/
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenSchur
import RBM3D.BA.MFixedPoint
import RBM3D.BA.KBase
import RBM3D.BA.KInduct
import RBM3D.BA.EKPins
import RBM3D.BA.EMn2BA
import RBM3D.BA.TwistPins
import RBM3D.Gauss.BlockAnderson
import RBM3D.Path.Walk
import RBM3D.Hierarchy.ContractionSecondLoop
import RBM3D.Induction.LoopGenN
import RBM3D.Induction.HierarchyN
import RBM3D.Induction.HierAlgebra
import RBM3D.Induction.GridDuhamelN
import RBM3D.Path.DifREP1
import RBM3D.Path.DifREP2
import RBM3D.Path.DifREP3

-- the BA carrier and the flow
#check @RBM.BA.Step2Mat
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Data
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflow_real
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Path.pathP
#check @RBM.Path.pathH
#check @RBM.Path.gridTime
-- T8b's block kernels (in place in Chain/Step2Gen) and their BA identities (TLF-C3, item (iii))
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.BA.Step2Kern_uKer_BA
-- the BA kernels the statements read
#check @RBM.BA.BATheta
#check @RBM.BA.BAMss
#check @RBM.BA.BAuKer
#check @RBM.BA.BAuKer_eq_one_add
#check @RBM.BA.BATheta_resolvent
#check @RBM.BA.BATheta_hasDerivAt
#check @RBM.BA.baKsol_two
#check @RBM.BA.EMn2BA_SB_zero
-- the generic grid statements TL2a twins (target 4)
#check @RBM.BA.STGridMartAtgL
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.STgAg
#check @RBM.BA.STEEMg
#check @RBM.BA.STeeUMg
-- TL0 (T2421): the twisted objects and the consumer statement
#check @RBM.BA.twL2'
#check @RBM.BA.twK
#check @RBM.BA.twK_ba
#check @RBM.BA.twL3
#check @RBM.BA.twB1
#check @RBM.BA.twB2
#check @RBM.BA.twEG
#check @RBM.BA.twDer
#check @RBM.BA.twEE
#check @RBM.BA.BATwKerA
#check @RBM.BA.BATwistLoopStep
-- band basis (item (ii))
#check @RBM.Ind.genMatOf
#check @RBM.Ind.loopGenNOf
#check @RBM.Ind.hierarchyN_of_loopGenN
#check @RBM.Ind.loopDrift_sub_K_deriv_n
#check @RBM.Gauss.sum_coordinateSecondWordDeriv_allCuts
#check @RBM.Ind.StoppedDuhamelN
#check @RBM.Ind.stoppedDuhamelN
#check @RBM.Ind.StoppedAzumaN
#check @RBM.Ind.martIncN
#check @RBM.Ind.predIncN
#check @RBM.Ind.difRep_identity
#check @RBM.Ind.gridRepRemN_holds
#check @RBM.Ind.gridRepTailN_holds
#check @RBM.Ind.gridRepWTailN_holds
