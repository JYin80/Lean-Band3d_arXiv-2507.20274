/-
Release check for T2014 (dispatcher V1, Sat Oct  3 01:02 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
KL2 ports `RBM2D/Loop/TreeRep.lean:545–1674` at `c9a24cf` (the cut of a tree at an internal edge and
the cut bijection); this file checks that the merged declarations the port builds on (KL1 = T2008,
merged 710acd2; `Loop/Partition.lean`) exist on `main`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2014-check.lean`.
-/
import RBM3D

#check @RBM.Zd
#check @RBM.Loop.IsDiag
#check @RBM.Loop.diagonals
#check @RBM.Loop.Crossing
#check @RBM.Loop.TSP
#check @RBM.Loop.KLwholeP
#check @RBM.Loop.KLInArc
#check @RBM.Loop.KLArcLe
#check @RBM.Loop.KLarcWidth
#check @RBM.Loop.KLnodes
#check @RBM.Loop.KLmem_nodes_of_mem
#check @RBM.Loop.KLleafPar
#check @RBM.Loop.KLnodePar
#check @RBM.Loop.KLleafPar_spec
#check @RBM.Loop.KLnodePar_spec
#check @RBM.Loop.KLIsTSP
#check @RBM.Loop.KLisTSP_of_mem_TSP
#check @RBM.Loop.KLtreeValW
#check @RBM.Loop.KLtreeValG
#check @RBM.Loop.KLtreeValW_empty
