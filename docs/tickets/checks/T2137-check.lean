/-
Release check for T2137 (dispatcher V1, Sun Oct  4 15:12 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-08: `lem:SEforLn` parts (1), (2); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2137-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STSEforLn
#check @RBM.Gauss.Sizes.STSEforLnConcl
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STegt
#check @RBM.Gauss.Sizes.STksimLK
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STn12E
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STContract
#check @RBM.Gauss.Sizes.stContract_holds
#check @RBM.Gauss.Sizes.stKbound_timeIcc
#check @RBM.Gauss.Sizes.stKward_timeIcc
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKward
