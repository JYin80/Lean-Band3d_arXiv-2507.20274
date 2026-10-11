/-
Release check for T2425 (dispatcher V2, Sun Oct 11 11:16 UTC 2026; DECISIONS §239).  BA-L L3a1 `BASymm1`: the twists of a BA
graph (twin of LWSymm §1-§3).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2425-check.lean
-/
import RBM3D.Graph.LWSymm
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAExpandW

#check @RBM.Graph.lwSymmTwistG
#check @RBM.Graph.lwSymm_twist_integral
#check @RBM.Graph.BAGraph.nLoops
#check @RBM.Graph.BAGraph.nExt
#check @RBM.Graph.BAGraph.nPairs
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.baM_symm
#check @RBM.Graph.BAlwData
