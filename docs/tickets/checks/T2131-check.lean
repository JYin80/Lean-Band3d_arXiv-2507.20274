/-
Release check for T2131 (dispatcher V1, Sun Oct  4 11:18 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
LW-08a: conjugation and transposition of graphs, `(Owx)` at an external vertex; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2131-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.val
#check @RBM.Graph.LData
#check @RBM.Graph.SEdge
#check @RBM.Graph.PGraph
#check @RBM.Graph.owx_graph_E
#check @RBM.Graph.oe1x_graph_E
#check @RBM.Graph.oe1x_graph_E_loop
#check @RBM.Graph.oe2x_graph_E
#check @RBM.Graph.owxT1
#check @RBM.Graph.owxT1_ord
#check @RBM.Graph.lwSampleData
#check @RBM.Graph.lwSplit
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Sizes.seqP
