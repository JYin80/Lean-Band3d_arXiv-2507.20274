/-
Release check for T2126 (dispatcher V1, Sun Oct  4 10:02 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-30: ports RBM2D `Green/FlucAvgDet`, `Green/IBPDet`, `Green/GbEXP` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2126-check.lean`.
-/
import RBM3D

#check @RBM.Green.FixedTimeFAThm
#check @RBM.Green.IBPDetThm
#check @RBM.Green.GbEXPV3Theorem
#check @RBM.Green.LocalLaw_gbEXPV3Theorem_of_fa_ibp
#check @RBM.Green.localLawDetThm
#check @RBM.Green.stGbEXP_of_v3
#check @RBM.Green.stGbEXPii_of_v3
#check @RBM.Green.stGbEXPij_of_v3
#check @RBM.Gauss.Sizes.STGbEXP
#check @RBM.Gauss.Sizes.STStep1
#check @RBM.Ind.step1TargetV3_holds
#check @RBM.Green.flucGain_of_localLaw
#check @RBM.Green.hsmall_of_highProb
#check @RBM.Green.highProbAt_detFlucDelta_of_localLaw
#check @RBM.Green.integral_norm_flucAvg_pow_le_iter_budget
#check @RBM.Green.perTimeDomAt_ibpRem
#check @RBM.Green.IBPRem_hΨlow_of_floor
#check @RBM.Green.eta_lower_of_rangeCond
#check @RBM.Green.FixedTimeFASeq
#check @RBM.Green.IBPDetSeq
#check @RBM.Green.condDiagBlk
#check @RBM.Green.blkCoef2
#check @RBM.Gauss.splitEquiv
