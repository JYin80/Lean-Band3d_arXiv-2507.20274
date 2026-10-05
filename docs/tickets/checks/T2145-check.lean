/-
Release check for T2145 (dispatcher V1, Sun Oct  4 17:17 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-03: Step 5 cases (ii), (iii) from pins and the skeleton instances; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2145-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STStep5II
#check @RBM.Gauss.Sizes.STStep5III
#check @RBM.Gauss.Sizes.STPfStep5
#check @RBM.Gauss.Sizes.STDuhamelII
#check @RBM.Gauss.Sizes.STIniTermII
#check @RBM.Gauss.Sizes.STWardII
#check @RBM.Gauss.Sizes.STEtermsMid
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_prec_cover
#check @RBM.Gauss.Sizes.ST_step5_assembly
#check @RBM.Gauss.Step5Inst.inst_step5II
#check @RBM.Gauss.Step5Inst.inst_step5III
#check @RBM.Gauss.Step5Inst.inst_skeletonI
