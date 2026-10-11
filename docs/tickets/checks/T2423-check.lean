/-
Release check for T2423 (dispatcher V2, Sun Oct 11 11:00 UTC 2026; DECISIONS §237).  BA-L R1 `BASim`: the graph-level
matching of a BA step with a band `LocStep` (supervisor 0951 L4-C1).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2423-check.lean
-/
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAGGExp

#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.PGraph.lvl1Comp
#check @RBM.Graph.LGraph.LocStd
#check @RBM.Graph.ba_W_sub_one
#check @RBM.Graph.BAexpFrameE
#check @RBM.Graph.baExpFrameE_holds
