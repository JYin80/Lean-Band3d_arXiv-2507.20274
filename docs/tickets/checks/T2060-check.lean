/-
Release check for T2060 (dispatcher V1, Sat Oct  3 14:09 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §24).
LW-04 builds the Stein bridge of the expansions on the merged graph vocabulary (`Graph/LWVocab`, T2050), the merged
derivative of the inverse (`Graph/Expansions`), the merged model (`Gauss/FineModel`) and `GaussIBP` (hypothesis);
this file checks that the names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2060-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.val
#check @RBM.Graph.LGraph.term
#check @RBM.Graph.LData
#check @RBM.Graph.hasDerivAt_inverse_apply
#check @RBM.Graph.hasDerivAt_inverse_sub_apply
#check @RBM.Green.GaussIBP
#check @RBM.Green.Tame
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Xentry
#check @RBM.Gauss.coordinateMatrix
#check @RBM.Gauss.Xmat_update
#check @RBM.Gauss.svarF
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqGvar
