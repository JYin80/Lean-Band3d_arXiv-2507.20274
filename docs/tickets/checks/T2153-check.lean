/-
Release check for T2153 (dispatcher V1, Sun Oct  4 18:35 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-31: envelope bookkeeping of the grid drift (port of RBM2D GridEnvelopeN); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2153-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.gridGoodN_holds
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Gauss.etaT
