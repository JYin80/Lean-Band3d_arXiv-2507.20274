/-
Release check for T2128 (dispatcher V1, Sun Oct  4 10:34 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
LW-08: locally standard graphs, `strat_local`, the `lvl1 lemma`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2128-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.PGraph
#check @RBM.Graph.PGraph.val
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.LGraph.val_eq_partition
#check @RBM.Graph.LGraph.partition_normal
#check @RBM.Graph.LGraph.scalingSize
#check @RBM.Graph.LGraph.scalingOrder
#check @RBM.Graph.Counters.scalingSize_eq
#check @RBM.Graph.ord
#check @RBM.Graph.owx_graph_E
#check @RBM.Graph.oe1x_graph_E
#check @RBM.Graph.oe1x_graph_E_loop
#check @RBM.Graph.oe2x_graph_E
#check @RBM.Graph.owxT1
#check @RBM.Graph.oe1xT1
#check @RBM.Graph.oe2xR1
#check @RBM.Graph.owxT1_ord
#check @RBM.Graph.oe1xT1_ord
#check @RBM.Graph.oe2xR1_ord
#check @RBM.Graph.lwSplit
#check @RBM.Graph.lwSampleData
#check @RBM.Graph.lwClaimSize
#check @RBM.Graph.p2Graph
#check @RBM.Graph.figGraph
