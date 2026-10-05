/-
Release check for T2146 (dispatcher V1, Sun Oct  4 17:19 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-32: good set of the general-`n` grid walk, exit time, measurability, `GridGoodN`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2146-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STSEforLn
#check @RBM.Gauss.Sizes.stSEforLn_holds
#check @RBM.Gauss.Sizes.STSEforLnConcl
#check @RBM.Gauss.Sizes.STDecayLoopU
#check @RBM.Gauss.Sizes.stDecayLoopU_of_step2
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STXiBoot
#check @RBM.Gauss.Sizes.STksimLKM
#check @RBM.Gauss.Sizes.STelklkM
#check @RBM.Gauss.Sizes.STegtM
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Path.pathH
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.gridTime
#check @RBM.Path.map_pathH_eq
#check @RBM.Path.gridTransferPT
#check @RBM.Path.firstHit
#check @RBM.Gauss.HighProbAt
