/-
Release check for T2142 (dispatcher V1, Sun Oct  4 16:32 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
LW-10a: `lem:localregular` first half (starting graph, predicates, paths); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2142-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LGraph
#check @RBM.Graph.PGraph
#check @RBM.Graph.LGraph.molGraph
#check @RBM.Graph.LGraph.Mol
#check @RBM.Graph.LGraph.molOf
#check @RBM.Graph.LGraph.molSolid
#check @RBM.Graph.LGraph.IsExtMol
#check @RBM.Graph.LGraph.nM
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.p2Graph
#check @RBM.Graph.p2Graph_val_eq
#check @RBM.Graph.fxyVal
#check @RBM.Graph.ord
#check @RBM.Graph.LGraph.counters
#check @RBM.Graph.LocStep
#check @RBM.Graph.Lvl1Reach
#check @RBM.Graph.lvl1_lemma_size
#check @RBM.Graph.lvl1_lemma_induction
#check @RBM.Graph.lvl1_induction
#check @RBM.Graph.PGraph.LocStd
#check @RBM.Graph.lvl1Pack
#check @RBM.Graph.lvl1WeightOuts0
#check @RBM.Graph.lvl1EdgeOuts0
#check @RBM.Graph.lvl1GGOuts0
