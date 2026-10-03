/-
Release check for T2040 (dispatcher V1, Sat Oct  3 06:15 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §12, §19).
Design ticket (report only): `#check` of the merged vocabulary its pins must bind to.  No proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2040-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.Whp
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.etaT
#check @RBM.Loop.KLK
#check @RBM.Loop.LoopIdx
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.lemT
#check @RBM.tailT
#check @RBM.mE
-- `claim:TTk` (merged) and the quantities of `lem:LW_moment_exp`
#check (RBM.EKTTk : ℕ → ℕ → Prop)
#check @RBM.ekTTk_holds
#check @RBM.PsiT
#check @RBM.sfT
