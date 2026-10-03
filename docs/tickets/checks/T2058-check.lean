/-
Release check for T2058 (dispatcher V1, Sat Oct  3 13:22 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §25).
S3-23 proves the deterministic scale facts of Steps 3–4 on the merged `Step34Pins` / `ScaleFacts` vocabulary;
this file checks that the names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2058-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STPsi
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STAII
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STRegIterI
#check @RBM.Gauss.Sizes.STEKWin
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.Ind.scaleFacts_R1
#check @RBM.Ind.scaleFacts_R2
#check @RBM.Ind.scaleFacts_etaT_div_etaT
#check @RBM.Gauss.etaT
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
