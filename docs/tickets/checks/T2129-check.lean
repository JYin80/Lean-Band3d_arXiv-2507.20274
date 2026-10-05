/-
Release check for T2129 (dispatcher V1, Sun Oct  4 10:49 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-06: K-loop fast decay `STKcalDecay`, uniform-in-time `STKbound`/`STKward`, lattice sum of the tail; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2129-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLK
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLmaxDist
#check @RBM.Loop.KLPT
#check @RBM.Loop.KLPT_holds
#check @RBM.Loop.KLbound_holds
#check @RBM.Gauss.Sizes.stKbound_holds
#check @RBM.Gauss.Sizes.stKward_holds
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Green.perTime_timeIcc_of_forall_seq
#check @RBM.tailT
#check @RBM.BparamR
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.zdistD
#check @RBM.sum_radial_exp_decay_le
#check @RBM.Gauss.etaT
