/-
Release check for T2419 (dispatcher V2, Sun Oct 11 10:00 UTC 2026; DECISIONS §232).  BA-L L4d `BAExpandId`: the BA identity
half (supervisor 0951 Q2, Q4).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2419-check.lean
-/
import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpandW
import RBM3D.BA.MFixedPoint

#check @RBM.Gauss.Sizes.expandG
#check @RBM.Gauss.Sizes.ExpandGSum
#check @RBM.Gauss.Sizes.expandG_sum
#check @RBM.Gauss.Sizes.RCand
#check @RBM.Gauss.Sizes.lwExpandIdentity_holds
#check @RBM.Gauss.Sizes.LWG5Graph
#check @RBM.Graph.BAGGGamma
#check @RBM.Graph.baGGGamma_holds
#check @RBM.Graph.ba_W_sub_one
#check @RBM.Graph.BAexpFrameE
#check @RBM.Graph.baExpFrameE_holds
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAlwData
#check @RBM.BA.BASelf
