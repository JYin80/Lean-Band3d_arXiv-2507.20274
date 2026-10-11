/-
Release check for T2426 (dispatcher V2, Sun Oct 11 11:16 UTC 2026; DECISIONS §239).  BA-L L3b3′ `BAScostS′`: the cost
vocabulary at atoms and the five BA-only ScostLL lemmas (T2397 G2).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2426-check.lean
-/
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp

#check @RBM.Graph.atomSetoid
#check @RBM.Graph.promoteC
#check @RBM.Graph.LGraph.scost
#check @RBM.Graph.LGraph.ScostLL
#check @RBM.Graph.scostLL_moveLoop
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.fxyPowGraph_locCostGe
#check @RBM.Graph.locCostGe_locStep
