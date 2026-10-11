/-
Release check for T2417 (dispatcher V2, Sun Oct 11 09:58 UTC 2026; DECISIONS §232).  BA-L R0 `BAAtomic`: the atomic image
(supervisor 0951 L4-C2).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2417-check.lean
-/
import RBM3D.Graph.BAVocab
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LocalRegular2
import RBM3D.Graph.LocalRegular6a

#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAGraph.atom
#check @RBM.Graph.BAGraph.atomAdj
#check @RBM.Graph.BAGraph.counters
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.LGraph.mergeP
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.LocStd
#check @RBM.Graph.LGraph.lvl1NLoops
#check @RBM.Graph.LGraph.lvl1NPairs
#check @RBM.Graph.PGraph.lvl1Comp
#check @RBM.Graph.LGraph.CircIffLoop
#check @RBM.Graph.LGraph.molNV
#check @RBM.Graph.LGraph.molNW
#check @RBM.Graph.PGraph.PathInv2
