/-
Release check for T2152 (dispatcher V1, Sun Oct  4 18:20 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-21: `(eq:bound_isolated)`: the pin `STCltIso` (CLT step and decorrelation); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2152-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STCltIso
#check @RBM.Gauss.Sizes.STCltIsoConcl
#check @RBM.Gauss.Sizes.STcltB
#check @RBM.Gauss.Sizes.STcltX
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Evol.cltTelescope
#check @RBM.Evol.integral_eq_zero_of_cltSwap_neg
#check @RBM.Evol.cltTransfer
#check @RBM.Evol.cltEvalAt
#check @RBM.Evol.CltPathBoundMulti
#check @RBM.Evol.cltPathMulti_bound
#check @RBM.Evol.HClt
#check @RBM.Evol.cltGood_whp
#check @RBM.Evol.cltCoord_tail
#check @RBM.Gauss.Sizes.stFarEntryAtLog
#check @RBM.Gauss.Step5Inst.szCL
