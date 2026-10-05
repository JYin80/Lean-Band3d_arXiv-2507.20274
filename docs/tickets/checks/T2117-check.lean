/-
Release check for T2117 (dispatcher V1, Sun Oct  4 06:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-26: ports RBM2D `Green/MinorDiffCond` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2117-check.lean`.
-/
import RBM3D

#check @RBM.Green.MinorDiffGainUpTo'
#check @RBM.Green.flucGainUpTo'_of_minorDiffGainUpTo'
#check @RBM.Green.bddMeas_applyOps_minorDiff_flucDiagSet
#check @RBM.Green.DiffBd
#check @RBM.Green.minorDiff
#check @RBM.Green.flucDiagSet
#check @RBM.Green.applyOps
#check @RBM.Green.perTimeDomAt_of_moment
#check @RBM.Green.MinorGoodLe
