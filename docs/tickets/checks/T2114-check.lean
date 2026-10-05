/-
Release check for T2114 (dispatcher V1, Sun Oct  4 05:03 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-29: ports RBM2D `Green/IBPRem` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2114-check.lean`.
-/
import RBM3D

#check @RBM.Green.ibpRem
#check @RBM.Green.ibpRem_eq_add
#check @RBM.Green.norm_greenDiagCentered_sub_minor_le
#check @RBM.Green.perTimeDomAt_of_moment
#check @RBM.Green.LocalLawDetSeq
#check @RBM.Green.IBPDetThm
#check @RBM.Green.FixedTimeFAThm
#check @RBM.Green.greenDiagCentered
#check @RBM.Green.condRow
