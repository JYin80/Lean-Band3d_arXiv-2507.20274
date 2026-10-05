/-
Release check for T2163 (dispatcher V1, Sun Oct  4 21:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-27: initial term of Step 5 case (ii): the merged pin, kit, kernel and propagator facts it builds on; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2163-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STIniTermII
#check @RBM.Gauss.Sizes.STIniTermConcl
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.ST_step5_caseII_of_pins
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_zeroModeSet_empty
#check @RBM.step5Kernel_UN_decompU
#check @RBM.prop8ZeroMode_holds
#check @RBM.prop5Short_holds
#check @RBM.Ind.Ugen
