/-
Release check for T2150 (dispatcher V1, Sun Oct  4 18:03 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-12: `lem:newKLK` sharp at `ℓ = L`, the pin `STNewKLKL`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2150-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STNewKLKL
#check @RBM.Gauss.Sizes.STNewKLKLAt
#check @RBM.Gauss.Sizes.STNewKLK
#check @RBM.Gauss.Sizes.stNewKLK_holds
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STJhatM
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.STGMM
#check @RBM.Loop.KLK_ward
