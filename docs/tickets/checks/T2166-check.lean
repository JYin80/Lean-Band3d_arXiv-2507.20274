/-
Release check for T2166 (dispatcher V1, Sun Oct  4 23:12 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-10a: non-alternating good-set inputs part 1: the merged grid good set, assembly and drift vocabulary it builds on; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2166-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Ind.qvFormN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Gauss.Sizes.STksimLKM
#check @RBM.Gauss.Sizes.STelklkM
#check @RBM.Gauss.Sizes.STegtM
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.ellT_mono
#check @RBM.ekSumDecayNAL_holds
#check @RBM.Gauss.Sizes.STNQConcl
