/-
Release check for T2191 (dispatcher V1, Mon Oct  5 07:37 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST-D5: Step 6 design (and the one-step `STMainInd` assembly skeleton); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2191-check.lean`.
-/
import RBM3D

-- the Step-6 conclusion and `lem:main_ind`
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STMainInd
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STLocalMax
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.Prec
-- the Step 1-5 pins and their uniform conclusions
#check @RBM.Gauss.Sizes.STStep1
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STStep1Weak
#check @RBM.Green.stStep1_holds
#check @RBM.Gauss.Sizes.STStep2
#check @RBM.Gauss.Sizes.ST_step2_of_pinsLW'
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STStep3R
#check @RBM.Gauss.Sizes.STStep4R
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STStep5Concl
#check @RBM.Gauss.Sizes.STStep5R
#check @RBM.Gauss.Sizes.STStep5
#check @RBM.Gauss.Sizes.STDecayStrongU
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKward_of_flow
-- endpoints and constants
#check @RBM.Gauss.Sizes.STLK_of_STLKU
#check @RBM.Gauss.Sizes.STLmax_of_STLmaxU
#check @RBM.Gauss.Sizes.ST_step5_assembly
#check @RBM.Gauss.Sizes.st5_conStInd_mono
#check @RBM.StochDomAt.precomp_param
#check @RBM.lemT_lt_one
-- evolution kernel, sum-zero and zero-mode operators
#check @RBM.Gauss.Sizes.STEKSumNdecay
#check @RBM.Gauss.Sizes.STEKSumRes2NAL
#check @RBM.Gauss.Sizes.STEKSumRes2
#check @RBM.Gauss.Sizes.STEKNonzero
#check @RBM.Gauss.Sizes.stek_sumNdecay_holds
#check @RBM.Gauss.Sizes.stek_sumRes2NAL_holds
#check @RBM.Gauss.Sizes.stek_sumRes2_holds
#check @RBM.Gauss.Sizes.stek_nonzero_holds
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.Gauss.Sizes.stQopNorm_holds
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Ind.Ugen
#check @RBM.UN
#check @RBM.zeroModeSet
#check @RBM.zeroModeSetLin
#check @RBM.EKSameRow
#check @RBM.ekSameRow_holds
#check @RBM.Gauss.Sizes.STExpInv
#check @RBM.Gauss.Sizes.stExpInv_holds
-- expected loops, drift objects, light-weight pins
#check @RBM.Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts
#check @RBM.Gauss.initialLoopValue_two_edges
#check @RBM.Gauss.momentDomAt_of_stochDomAt
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STEEk
#check @RBM.Gauss.Sizes.LWE
#check @RBM.Gauss.Sizes.LWAvgLaw
#check @RBM.Gauss.Sizes.LWtermEXP
-- instances at d = 3
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step5Inst.szG
#check @RBM.Gauss.Step5Inst.flow_zG
#check @RBM.Gauss.Step5Inst.szB_reg5I
#check @RBM.Gauss.Step5Inst.szB_reg5II
#check @RBM.Gauss.Step5Inst.sz0_reg5III
#check @RBM.Gauss.Step5Inst.szG_reg4
