/-
Release check for T2053 (dispatcher V1, Sat Oct  3 11:01 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §18, §25).
EK-6 proves the merged consumer pins `STEK*` from the merged `EK*` pins; this file checks that both sides exist
(`ekSumDecayNonzero_holds` is EK-5's: T2053 starts only after T2035 merges, so it is not checked here).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2053-check.lean`.
-/
import RBM3D

#check (RBM.Gauss.Sizes.STEKSumNdecay : ℕ → Prop)
#check (RBM.Gauss.Sizes.STEKSumRes1 : ℕ → Prop)
#check (RBM.Gauss.Sizes.STEKSumRes2NAL : ℕ → Prop)
#check (RBM.Gauss.Sizes.STEKSumRes2 : ℕ → Prop)
#check (RBM.Gauss.Sizes.STEKNonzero : ℕ → Prop)
#check @RBM.ekSumNdecay_holds
#check @RBM.ekSumDecay1_holds
#check @RBM.ekSumDecayNAL_holds
#check @RBM.ekSumDecay2_holds
#check @RBM.prop5Decay_holds
#check @RBM.prop6Diff1_holds
#check @RBM.prop8ZeroMode_holds
#check @RBM.Gauss.Sizes.Bandwidth
