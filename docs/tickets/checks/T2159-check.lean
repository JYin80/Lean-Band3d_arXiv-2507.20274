/-
Release check for T2159 (dispatcher V1, Sun Oct  4 20:06 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-34: the pin `AzumaSubGN` and `0 ∈ GoodSetN` at `u = 0`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2159-check.lean`.
-/
import RBM3D

#check @RBM.Ind.AzumaSubGN
#check @RBM.Ind.AssembledN
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Path.goodExitTauN
#check @RBM.Path.goodExitMeasN
#check @RBM.Path.pathH
#check @RBM.Path.filt
