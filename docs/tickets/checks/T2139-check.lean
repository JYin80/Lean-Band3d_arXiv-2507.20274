/-
Release check for T2139 (dispatcher V1, Sun Oct  4 16:07 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-09: `lem:SEforLn` parts (3), (4) and the pin `STSEforLn`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2139-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STSEforLn
#check @RBM.Gauss.Sizes.STSEforLnConcl
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STelklk
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STeeLoop
#check @RBM.Gauss.Sizes.STn12
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STContract
#check @RBM.Gauss.Sizes.stContract_holds
#check @RBM.Gauss.Sizes.stKward_timeIcc
#check @RBM.Gauss.Sizes.stSumTwoLoop
#check @RBM.Gauss.Sizes.stSumTwoLoop_exists
#check @RBM.Gauss.Sizes.stSEforLn_part1
#check @RBM.Gauss.Sizes.stSEforLn_part2
#check @RBM.Gauss.Step34Inst.inst_SEforLn
#check @RBM.tailT
#check @RBM.SB
