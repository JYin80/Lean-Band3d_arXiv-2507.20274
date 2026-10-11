/-
Release check for T2407 (dispatcher V2, Sun Oct 11 04:19 UTC 2026; DECISIONS §221).  BA-L2c1: the BA weight expansion (B.19) as a graph operation
(new `Graph/BAWeightOp.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2407-check.lean
-/
import RBM3D.Graph.BAExpandWOrd
import RBM3D.Graph.LWWeightExp

#check @RBM.Graph.BAlweight
#check @RBM.Graph.baLweight_holds
#check @RBM.Graph.BAlwData
#check @RBM.Graph.baW_mul
#check @RBM.Graph.BAGraph.lanlwTerms
#check @RBM.Graph.lanlw_val
#check @RBM.Graph.lanlwT1_counters
#check @RBM.Graph.lanlw_ord
#check @RBM.Graph.lanlw_scalingOrderG
#check @RBM.Graph.owxT1
#check @RBM.Graph.owxT1_ord
#check @RBM.Graph.owx_graph_E
