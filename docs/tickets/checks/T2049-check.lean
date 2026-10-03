/-
Release check for T2049 (dispatcher V1, Sat Oct  3 10:32 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §25).
S3-01 moves the T2041 probe's Steps 3–4 pins into the library; this file checks that the merged names they bind to exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2049-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.etaT
#check @RBM.Loop.KLK
#check @RBM.UN
#check @RBM.zeroModeSet
#check (RBM.EKSumDecay2 : ℕ → ℕ → ℝ → ℝ → Prop)
#check (RBM.EKSumDecayNonzero : ℕ → ℕ → ℝ → ℝ → Prop)
