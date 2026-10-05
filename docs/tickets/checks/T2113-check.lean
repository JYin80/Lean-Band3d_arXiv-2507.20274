/-
Release check for T2113 (dispatcher V1, Sun Oct  4 05:03 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-25: ports RBM2D `Green/MinorDiff` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2113-check.lean`.
-/
import RBM3D

#check @RBM.Green.MinorDiffGainUpTo'
#check @RBM.Green.MinorGoodLe
#check @RBM.Green.flucGainUpTo'_of_minorDiffGainUpTo'
#check @RBM.Green.minorGoodLe_of_goodEvent_flow
#check @RBM.Green.minorDiff
#check @RBM.Green.flucDiagSet
#check @RBM.Green.norm_minorDiff_le
#check @RBM.Green.applyOps
