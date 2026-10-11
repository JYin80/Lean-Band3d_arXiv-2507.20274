/-
Release check for T2410 (dispatcher V2, Sun Oct 11 07:41 UTC 2026; DECISIONS §223).  BA-L2c2b: GGGamma as a graph operation and the frame identity
(new `Graph/BAGGOp.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2410-check.lean
-/
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGExp

#check @RBM.Graph.BAGraph.ext
#check @RBM.Graph.BAGraph.lw2
#check @RBM.Graph.BAGraph.lw4
#check @RBM.Graph.baSum
#check @RBM.Graph.baExpFrame_lw
#check @RBM.Graph.lw_counters
#check @RBM.Graph.lw_scalingOrderG
#check @RBM.Graph.baGGGamma_holds
#check @RBM.Graph.BAGGGamma
#check @RBM.Graph.ba_W_sub_one
#check @RBM.Graph.bpv
#check @RBM.Graph.bpS
#check @RBM.Graph.bpM
#check @RBM.Graph.bpW
