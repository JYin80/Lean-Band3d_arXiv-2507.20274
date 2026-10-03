/-
Release check for T2080 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-03: moves probe §9, §11 (events) and adds the ST-2 ↔ LW bridges; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2080-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STLWB
#check @RBM.Gauss.Sizes.STLWT
#check @RBM.Gauss.Sizes.STEGtM
#check @RBM.Gauss.Sizes.LWE
#check @RBM.Gauss.Sizes.LWterm
#check @RBM.Gauss.Sizes.LWtermExp
#check @RBM.Gauss.Sizes.LWAssmExp
#check @RBM.Gauss.Sizes.STGoodAt
#check @RBM.Gauss.Sizes.ST_good_engine
#check @RBM.Gauss.Sizes.STBctl_pos
