/-
Release check for T2054 (dispatcher V1, Sat Oct  3 11:01 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §25).
S3-02 proves the merged pin `STContract`; this file checks that it and the merged loop vocabulary exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2054-check.lean`.
-/
import RBM3D

#check (RBM.Gauss.Sizes.STContract : ℕ → Prop)
#print RBM.Gauss.Sizes.STContract
#check @RBM.Gauss.Sizes.STmaxL
#check @RBM.Gauss.Sizes.STLI
#check @RBM.Gauss.Gres
#check @RBM.Gauss.etaT

example : Prop := ∀ d : ℕ, RBM.Gauss.Sizes.STContract d
