/-
Release check for T2055 (dispatcher V1, Sat Oct  3 11:01 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §25).
S3-04 proves the merged pin `STMollifierEx` and the operator algebra; this file checks the names it builds on.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2055-check.lean`.
-/
import RBM3D

#check (RBM.Gauss.Sizes.STMollifierEx : ℕ → Prop)
#print RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.zeroModeSet
#check @RBM.projMat
#check @RBM.UN
#check @RBM.ellT

example : Prop := ∀ d : ℕ, RBM.Gauss.Sizes.STMollifierEx d
