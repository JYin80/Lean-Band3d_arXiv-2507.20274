/-
Release check for T2360 (dispatcher V1, Fri Oct 9 02:52 UTC 2026; DECISIONS §163 (2); supervisor 2026-10-09-0243 K1–K6).  BA-DK: stage-K design.
Merged names (`main` 8d76de9).  Run: `lake env lean docs/tickets/checks/T2360-check.lean`.
-/
import RBM3D.Loop.KLFinal
import RBM3D.BA.FlowPins
import RBM3D.BA.Prop6Path
import RBM3D.BA.KHeatDiff

#check @RBM.Loop.IsKLoopS
#check @RBM.BA.STKboundgL
#check @RBM.BA.baFMz
#check @RBM.BA.BAProp5to8
#check @RBM.BA.baProp5to8_holds
#check @RBM.BA.BATheta
#check @RBM.BA.BAReal
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Loop.KLK
