/-
Release check for T2123 (dispatcher V1, Sun Oct  4 07:49 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-28: ports RBM2D `Green/Eq45Small`, `Green/FlucThreshold` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2123-check.lean`.
-/
import RBM3D

#check @RBM.Green.flucGainUpTo'_goodEvent
#check @RBM.Green.minorDiffGainUpTo'_of_le_on
#check @RBM.Green.badBase
#check @RBM.Green.condEnv
#check @RBM.Green.MinorDiffGainUpTo'
#check @RBM.Green.localLawDetThm
#check @RBM.Green.FixedTimeFAThm
#check @RBM.Green.LocalLawDetSeq
#check @RBM.Green.MinorGoodLe
