/-
Release check for T2066 (dispatcher V1, Sat Oct  3 18:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §28).
ST2-01 moves the Step 2 vocabulary and pins of the T2039 probe into the library, bound to the merged ST-1 and Steps 3–4
declarations; this file checks that those merged names exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2066-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.zdistInf
#check @RBM.ellT
