/-
Release check for T2108 (dispatcher V1, Sun Oct  4 03:29 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-27: ports RBM2D `Green/AvgPins`, `Green/LocalLaw` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2108-check.lean`.
-/
import RBM3D

#check @RBM.Green.LoopDetSeq
#check @RBM.Green.GbEXPHypV3
#check @RBM.Green.GbEXPV3Theorem
#check @RBM.Green.giiOmegaSeq_of_stGiiGEX
#check @RBM.Green.giiSeq_of_asGMc
#check @RBM.Green.gijOmegaSeq
#check @RBM.Green.giiOmegaSeq
#check @RBM.Green.perTimeDomAt_of_moment
#check @RBM.Green.condRow
