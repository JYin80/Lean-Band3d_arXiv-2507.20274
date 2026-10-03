/-
Release check for T2076 (dispatcher V1, Sat Oct  3 19:53 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-32 ports RBM2D `Induction/ConArg` at `c9a24cf` onto the merged MD layer and the merged ST-1 files; this file checks that the names it builds on exist.
Run from the main worktree: `lake env lean docs/tickets/checks/T2076-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STConArg
#check @RBM.Gauss.Sizes.STomegaC
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.gloop_eq_loopM
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.sum_gloop_ward_last_div
#check @RBM.Ind.trace_gram_rpow_le
#check @RBM.Ind.loopMax_two_mul_le_tilde
#check @RBM.Ind.ztTilde_arith
