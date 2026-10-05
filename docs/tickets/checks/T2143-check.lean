/-
Release check for T2143 (dispatcher V1, Sun Oct  4 16:46 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-02: Step 5 kit, assembly, case (i) from pins, case (iv) proved; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2143-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STStep5Concl
#check @RBM.Gauss.Sizes.STStep5I
#check @RBM.Gauss.Sizes.STStep5IV
#check @RBM.Gauss.Sizes.STStep5
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STEtermsMid
#check @RBM.Gauss.Sizes.STDuhamelI
#check @RBM.Gauss.Sizes.STIniTermI
#check @RBM.Gauss.Sizes.st5_reg5I_mid
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STDecayStrongU
#check @RBM.Gauss.Step5Inst.szCL
