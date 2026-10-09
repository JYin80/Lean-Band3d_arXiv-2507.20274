/-
Release check for T2358 (dispatcher V1, Fri Oct 9 01:53 UTC 2026; DECISIONS §162; supervisor 2026-10-09-0143 PASS, C1–C3).  LW-13b R1 = P:
the provenance engine.  The statements of the row are the T2348 probe's (`t/T2348:RBM3D/Probe/T2348Pins.lean:29-185, 291-310`,
with C3), checked by script diff in the audit; this file checks the merged names they use (`main` 83847ef).
Run: `lake env lean docs/tickets/checks/T2358-check.lean`.
-/
import RBM3D.Graph.LWEngine
import RBM3D.Graph.LWMoment

#check @RBM.Graph.LocStepX
#check @RBM.Graph.LWLocRegConcl
#check @RBM.Graph.lwEvX
#check @RBM.Graph.lwEngine_shift
#check @RBM.Graph.lwEngine_combine
#check @RBM.Graph.lwEngine_exists
#check @RBM.Graph.lw_localregularX
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.fxyPowGraph_val_eq
#check @RBM.Graph.localReg_fxyBeta
#check @RBM.Graph.lwSampleData
#check @RBM.Graph.lwS
#check @RBM.Graph.PGraph
#check @RBM.Graph.lvl1_sum_flatMap
#check @RBM.Green.GaussIBP
#check @RBM.Gauss.Sizes.lwMoment_fxyPow_val
#check @RBM.Gauss.Sizes.LWf
#check @RBM.Gauss.Sizes.LWS
#check @RBM.Gauss.Sizes.STGM
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.Sizes.Gt
