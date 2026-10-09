/-
Release check for T2356 (dispatcher V1, Fri Oct 9 00:58 UTC 2026; DECISIONS §160 (2)).  UN-47 Eq729B: port of RBM2D `GUEPhase` with a `d ≥ 3`
statement design (stage 1a).  Merged names (`main` 93b8ec8).  Run: `lake env lean docs/tickets/checks/T2356-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Eq729A
import RBM3D.Universality.GUEPhase.OneLoop
import RBM3D.Universality.GUEPhase.DuhamelC
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Universality.GUEPhase.BootstrapAt
import RBM3D.Universality.ZeroModeProfile
import RBM3D.Loop.KLTree
-- stage 1b (Fri Oct 9 03:51 UTC 2026, DECISIONS §164, supervisor 0344 E2): HypA, ZTransfer, QUEFromQDiff, KLFinal added; DuhamelC is not imported by Eq729B.lean
import RBM3D.Universality.GUEPhase.HypA
import RBM3D.Main.ZTransfer
import RBM3D.Main.QUEFromQDiff
import RBM3D.Loop.KLFinal

-- the GUE-phase layers
#check @RBM.Univ.GUEPhase.eq729F
#check @RBM.Univ.GUEPhase.eq729e
#check @RBM.Univ.GUEPhase.eq729c
#check @RBM.Univ.GUEPhase.eq729_one_step
#check @RBM.Univ.GUEPhase.eq729_primRhs_one
#check @RBM.Univ.GUEPhase.eq729_time_mem
#check @RBM.Univ.GUEPhase.eq729_step_nonneg
#check @RBM.Univ.GUEPhase.gueGrid_expect_oneLoop
#check @RBM.Univ.GUEPhase.gueGrid_loop_duhamel
#check @RBM.Univ.GUEPhase.kTwoGUE
#check @RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pm
#check @RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pp
#check @RBM.Univ.GUEPhase.eq736_detDomAt
#check @RBM.Univ.GUEPhase.UnifDetDomAt
#check @RBM.Univ.GUEPhase.GUEPhaseGrid_gloop_two_smul_lemT_eq
#check @RBM.Univ.GUEPhase.GUEPathBounds
#check @RBM.Univ.GUEPhase.gueGridK
#check @RBM.Univ.GUEPhase.map_gueH_zero
#check @RBM.Univ.GUEPhase.map_gueH_last
#check @RBM.Univ.GUEPhase.primRhsGUE
#check @RBM.Univ.GUEPhase.ellT_eq_L
-- the OU layer and the target pin
#check @RBM.Univ.UNOUEq747
#check @RBM.Univ.profPMTilde
#check @RBM.Univ.profPPTilde
#check @RBM.Univ.ouEtaQ
#check @RBM.Univ.ouTauMax
#check @RBM.Univ.ouTStar
#check @RBM.Univ.ouZeta
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouP
#check @RBM.Univ.Nsz
#check @RBM.Univ.UNMLOut
#check @RBM.Endpoints.qdBoundExp
#check @RBM.Endpoints.calB
#check @RBM.Endpoints.avg2
-- the ST vocabulary (initial term) and Lemma 2.8
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Loop.KLK
#check @RBM.mSigma
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.lemma28_quant
#check @RBM.eq_inv_sqrt_mul_zt
#check @RBM.Univ.GUEPhase.Hyp_Kt_detDom
#check @RBM.Univ.GUEPhase.Hyp_Kt_one
#check @RBM.Endpoints.queChain
