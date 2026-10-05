/-
Release check for T2140 (dispatcher V1, Sun Oct  4 16:07 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-17: port of CltSwap onto `Gauss/FineModel`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2140-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Ω
#check @RBM.Gauss.PF
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.slice
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.Sizes.measurable_slice
#check @RBM.Gauss.Sizes.SeqΩ
