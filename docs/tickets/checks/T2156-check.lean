/-
Release check for T2156 (dispatcher V1, Sun Oct  4 19:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-13b: summed envelope of the `𝒬`-process remainder (port of RBM2D AltGridQ §10); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2156-check.lean`.
-/
import RBM3D

#check @RBM.Ind.qErrQN
#check @RBM.Ind.qStepErrN
#check @RBM.Ind.SumWeightedStepErrN_Stmt
#check @RBM.Ind.sum_weighted_stepErrN_le
#check @RBM.Ind.gridDriftN_envelope
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Gauss.etaT
