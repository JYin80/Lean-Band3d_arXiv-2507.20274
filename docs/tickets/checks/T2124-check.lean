/-
Release check for T2124 (dispatcher V1, Sun Oct  4 08:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
LW-09: `claim:size` (`7_8:264`), `(eq:estSpm-W)`, `scalemole`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2124-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LGraph.scalingSize
#check @RBM.Graph.LGraph.scalingSizeG
#check @RBM.Graph.LGraph.val
#check @RBM.Graph.LGraph.counters
#check @RBM.Graph.LGraph.nM
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.lwSplus
#check @RBM.Graph.LWPins_lwSp
#check @RBM.Gauss.Sizes.STGbEXPii
#check @RBM.Gauss.Sizes.STGbEXPij
#check @RBM.Loop.KLShort_holds
