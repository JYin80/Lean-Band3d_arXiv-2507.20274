/-
Release check for T2149 (dispatcher V1, Sun Oct  4 17:47 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-20: the good event of the CLT replacement step (port of RBM2D CltGood); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2149-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STFarEntryAtLog
#check @RBM.Gauss.Sizes.stFarEntryAtLog
#check @RBM.Gauss.Sizes.prec_timeIcc_section
#check @RBM.Evol.cltGoodAt
#check @RBM.Evol.CltPathBound
#check @RBM.Evol.cltTransfer
#check @RBM.Gauss.PF
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Step5Inst.szCL
#check @RBM.Gauss.Step5Inst.zCL
#check @RBM.Gauss.Step5Inst.sCL
#check @RBM.Gauss.Step5Inst.tCL
