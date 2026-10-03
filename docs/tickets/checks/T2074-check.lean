/-
Release check for T2074 (dispatcher V1, Sat Oct  3 19:38 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §28).
ST2-18: this file checks that the merged names the ticket builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2074-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STNetLift2
#check @RBM.Gauss.Sizes.STNetLift
#check @RBM.Ind.GopboundPin
#check @RBM.Ind.ContinuityNet.cont_core
