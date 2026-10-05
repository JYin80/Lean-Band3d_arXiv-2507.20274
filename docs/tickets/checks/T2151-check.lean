/-
Release check for T2151 (dispatcher V1, Sun Oct  4 18:20 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
LW-10b: `lem:localregular` second half: (4), (6), assembly; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2151-check.lean`.
-/
import RBM3D

#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.PGraph.LocReg1
#check @RBM.Graph.PGraph.LocReg2
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.PGraph.LocReg6
#check @RBM.Graph.PGraph.PathInv
#check @RBM.Graph.pathInv_locStep
#check @RBM.Graph.lw_localregular_expansion
#check @RBM.Graph.fxyPowGraph_ord
#check @RBM.Graph.LocStep
#check @RBM.Graph.lvl1_lemma_size
#check @RBM.Graph.lvl1_lemma_induction
#check @RBM.Graph.lvl1_step_good
#check @RBM.Graph.ord
