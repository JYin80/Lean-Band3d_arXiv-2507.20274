/-
Release check for T2354 (dispatcher V1, Fri Oct 9 00:58 UTC 2026; DECISIONS §160).  UN-49 HypB + UN-50a LLTransfer: ports of RBM2D `GUEPhase`.
Merged names (`main` 93b8ec8).  Run: `lake env lean docs/tickets/checks/T2354-check.lean`.
-/
import RBM3D.Universality.GUEPhase.HypA
import RBM3D.Green.EntryDom
import RBM3D.Induction.PerTimeCalc
import RBM3D.Path.Stop
import RBM3D.Universality.GUEPhase.Grid
import RBM3D.Universality.ZeroModeProfile

-- (A) HypB: HypA and the process layer
#check @RBM.Univ.GUEPhase.Hyp_step_nonneg
#check @RBM.Univ.GUEPhase.Hyp_time_mem
#check @RBM.Univ.GUEPhase.Hyp_interp_bound
#check @RBM.Univ.GUEPhase.Hyp_exists_loopOf
#check @RBM.Univ.GUEPhase.Hyp_eps_le_dev
#check @RBM.Univ.GUEPhase.Hyp_trace_eq_gloop_one
#check @RBM.Univ.GUEPhase.Hyp_cutGlue_le
#check @RBM.Univ.GUEPhase.Hyp_Kt_detDom
#check @RBM.Univ.GUEPhase.Hyp_Kt_one
#check @RBM.Univ.GUEPhase.Hyp_Kt_disc
#check @RBM.Univ.GUEPhase.Hyp_grid
#check @RBM.Univ.GUEPhase.gueStop
#check @RBM.Univ.GUEPhase.gueLmax
#check @RBM.Univ.GUEPhase.gueDmax
#check @RBM.Univ.GUEPhase.gueDev
#check @RBM.Univ.GUEPhase.gueDelta
#check @RBM.Univ.GUEPhase.gueLproc
#check @RBM.Univ.GUEPhase.gueDproc
#check @RBM.Univ.GUEPhase.gueDproc_continuousOn
#check @RBM.Univ.GUEPhase.norm_egtNGUE_le
#check @RBM.Univ.GUEPhase.primBilGUE
#check @RBM.Univ.GUEPhase.primRhsGUE
#check @RBM.Univ.GUEPhase.supOn
#check @RBM.Univ.GUEPhase.LoopSet
#check @RBM.Green.entryDom_goodEvent_of_llErr
#check @RBM.Green.llErrMat
#check @RBM.Green.avgErr
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
#check @RBM.Path.firstHit
#check @RBM.Path.lt_firstHit_imp
#check @RBM.Ind.loopMax
#check @RBM.Path.gridTime
-- (B) LLTransfer: the grid, the OU layer, Lemma 2.8
#check @RBM.Univ.GUEPhase.GUEPathBounds
#check @RBM.Univ.GUEPhase.Pgue
#check @RBM.Univ.GUEPhase.gueH_measurable
#check @RBM.Univ.GUEPhase.map_gueH_last
#check @RBM.Univ.GUEPhase.gueGridK
#check @RBM.Univ.ouEtaLL
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouP
#check @RBM.Univ.ouZeta
#check @RBM.Univ.UNOULL
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.eq_inv_sqrt_mul_zt
#check @RBM.lemma28_quant
