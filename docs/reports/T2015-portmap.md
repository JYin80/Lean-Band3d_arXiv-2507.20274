# T2015 port map of sub-gate ST-1: RBM2D `c9a24cf` -> RBM3D (design report ST-D1)

Generated Sat Oct  3 04:48:08 UTC 2026 (`date -u`) by the scripts of P.10 (python3; read-only `git -C ../RBM2D --no-optional-locks show`; the class, the sub-gate and the paper labels of each file are those of `docs/reports/T2002-portmap.md` part C, re-derived and checked below).  RBM2D line numbers are those of commit `c9a24cf`; "kept" is the line count of the same file at `0c1330a` (`-1`: deleted as dead code by RBM2D T2274), i.e. the part the final d = 2 proof uses.  Dependencies between files are the imports of the **kept** text (`0c1330a`); an import is an upper bound of a real dependency.

## P.1 Inventory (ticket item 1): the 86 files of ST-1

Selection rule (T2002 portmap, `mkportmap.py`): groups `Gauss/.*`, `Green/.*`, `Hierarchy/.*`, `Induction/(Continuity|ConArg|ConArgDet|Step1)` minus the MD vocabulary files (`Gauss/{Model,Domination,MomentBridge,LinearForm,Envelope,SteinMatrix}`, `Hierarchy/{Loops,Operations,OperationsPairWord}`) minus class d.  Columns: lines at `c9a24cf` / kept at `0c1330a` (recomputed from git: equal to the T2002 numbers for all 86 rows), class (a: renaming only, b: exponents, c: re-written), exponent tokens by kind counted in the file text (`W2` = `W ^ 2`, `L2`, `N2` = `(W * L) ^ 2` or `size ^ 2`, `inv2` = `W⁻²`-type, `d=2`, `Z2` = `Z2`/`zdist2`, `1/5`, `scal` = uses of `scaleM/ellT/tailT/ellStar/Meta/ellz`), paper labels (this paper) cited by the file (T2002; `(dir)` = inferred from the directory), number of public declarations (defs/theorems), number referenced by files of ST-2..ST-6, and the ticket of P.7.

| # | RBM2D file | lines | kept | cl | exponent tokens | paper labels (T2002) | pub | used | ticket |
|---|---|---|---|---|---|---|---|---|---|
| 1 | Gauss/FlowTimeCont | 61 | 28 | a | - | - | 5 | 0 | S1-01 |
| 2 | Gauss/GreenCoordinateSecondDerivative | 90 | 58 | a | - | - | 2 | 0 | S1-02 |
| 3 | Gauss/GreenDerivative | 143 | 99 | a | - | - | 3 | 1 | S1-01 |
| 4 | Gauss/GreenTimeCont | 94 | 81 | a | - | - | 5 | 1 | S1-01 |
| 5 | Gauss/LoopCoordinateDerivative | 234 | 163 | a | Z2/zdist2:6 | - | 9 | 5 | S1-02 |
| 6 | Gauss/LoopCoordinateDerivativeBounds | 252 | 252 | b | W^2:2 W⁻²/L⁻²:8 Z2/zdist2:3 | - | 3 | 0 | S1-02 |
| 7 | Gauss/LoopCoordinateIntegrability | 158 | 113 | b | W^2:2 Z2/zdist2:7 | - | 9 | 0 | S1-02 |
| 8 | Gauss/LoopCoordinateSecondDerivative | 176 | 134 | a | Z2/zdist2:5 | - | 6 | 2 | S1-02 |
| 9 | Gauss/LoopDerivative | 203 | 128 | a | Z2/zdist2:6 | - | 6 | 1 | S1-01 |
| 10 | Gauss/LoopEnvelope | 131 | 119 | b | W^2:4 W⁻²/L⁻²:12 Z2/zdist2:5 | - | 8 | 6 | S1-01 |
| 11 | Gauss/LoopExpectationDerivative | 102 | 102 | b | W^2:1 W⁻²/L⁻²:1 Z2/zdist2:2 | - | 2 | 1 | S1-05 |
| 12 | Gauss/LoopFlowCoordinateChain | 216 | 181 | a | Z2/zdist2:10 | - | 15 | 3 | S1-05 |
| 13 | Gauss/LoopFlowDerivativeEnvelope | 200 | 195 | b | W^2:12 W⁻²/L⁻²:3 Z2/zdist2:3 | - | 8 | 0 | S1-05 |
| 14 | Gauss/LoopFlowSteinExpectation | 351 | 341 | b | W^2:4 W⁻²/L⁻²:5 Z2/zdist2:7 | - | 8 | 0 | S1-05 |
| 15 | Gauss/LoopGeneratorExpectation | 106 | 106 | a | Z2/zdist2:2 | - | 2 | 2 | S1-06 |
| 16 | Gauss/LoopGeneratorSamplewise | 58 | 58 | b | W^2:2 Z2/zdist2:3 | - | 2 | 2 | S1-06 |
| 17 | Gauss/LoopInitialValue | 54 | 35 | b | W⁻²/L⁻²:1 Z2/zdist2:4 | - | 5 | 2 | S1-06 |
| 18 | Gauss/LoopInitialValueProjectionWords | 113 | 105 | b | W⁻²/L⁻²:5 Z2/zdist2:11 | - | 6 | 2 | S1-06 |
| 19 | Gauss/LoopInitialValueScalar | 119 | 98 | b | W⁻²/L⁻²:3 Z2/zdist2:5 | - | 7 | 4 | S1-06 |
| 20 | Gauss/LoopInitialValueSupport | 88 | 60 | b | W⁻²/L⁻²:4 Z2/zdist2:11 | - | 4 | 2 | S1-06 |
| 21 | Gauss/LoopSampleCont | 85 | 76 | a | Z2/zdist2:5 | - | 8 | 4 | S1-01 |
| 22 | Gauss/LoopSpectralDriftCuts | 210 | 203 | b | W^2:3 Z2/zdist2:23 | - | 9 | 0 | S1-06 |
| 23 | Gauss/LoopTimeCont | 106 | 87 | a | Z2/zdist2:4 | - | 10 | 3 | S1-01 |
| 24 | Gauss/SpectralAlgebra | 62 | 53 | a | - | - | 4 | 4 | S1-01 |
| 25 | Gauss/SpectralDerivative | 49 | 32 | a | - | - | 2 | 1 | S1-01 |
| 26 | Gauss/SpectralWindow | 81 | 50 | a | Z2/zdist2:1 | - | 9 | 7 | S1-01 |
| 27 | Green/AvgPins | 736 | 567 | b | L^2:1 W⁻²/L⁻²:7 d=2:2 Z2/zdist2:8 | GavLGEX@3_5:33; lem_GbEXP@3_5:14 | 39 | 0 | S1-27 |
| 28 | Green/CondDom | 647 | 359 | b | d=2:3 Z2/zdist2:1 | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 13 | 0 | S1-24 |
| 29 | Green/CondRow | 492 | 373 | a | - | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 31 | 0 | S1-17 |
| 30 | Green/CondStable | 645 | 433 | b | d=2:1 Z2/zdist2:2 | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 7 | 0 | S1-24 |
| 31 | Green/EntryBlock | 836 | 557 | b | W^2:4 L^2:1 W⁻²/L⁻²:18 d=2:3 Z2/zdist2:82 1/5:11 | lem_GbEXP@3_5:14; example@A:548 | 36 | 2 | S1-16 |
| 32 | Green/EntryCore | 1014 | 856 | a | - | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 33 | 2 | S1-10 |
| 33 | Green/EntryDom | 1042 | 641 | b | W^2:2 L^2:1 W⁻²/L⁻²:2 d=2:1 Z2/zdist2:13 | lem_GbEXP@3_5:14; GavLGEX@3_5:33; GiiGEX@3_5:21; GijGEX@3_5:24; def_asGMc@3_5:16 | 13 | 1 | S1-16 |
| 34 | Green/EntryGauss | 151 | 108 | a | - | GiiGEX@3_5:21; GijGEX@3_5:24 | 4 | 0 | S1-24 |
| 35 | Green/Eq45Small | 505 | 415 | b | d=2:1 | def_asGMc@3_5:16 | 16 | 0 | S1-28 |
| 36 | Green/FlucAvg | 546 | 411 | b | W⁻²/L⁻²:1 d=2:3 Z2/zdist2:13 | GavLGEX@3_5:33; Main_DEL_COND@1_2:359 | 26 | 1 | S1-18 |
| 37 | Green/FlucAvgDet | 623 | 524 | b | W⁻²/L⁻²:23 d=2:3 Z2/zdist2:4 | GavLGEX@3_5:33; lem_GbEXP@3_5:14 | 18 | 0 | S1-30 |
| 38 | Green/FlucIter | 1877 | 1540 | b | W⁻²/L⁻²:5 d=2:2 Z2/zdist2:3 | GavLGEX@3_5:33 | 87 | 1 | S1-20,S1-21 |
| 39 | Green/FlucIterHigh | 970 | 764 | b | d=2:1 Z2/zdist2:1 | GavLGEX@3_5:33 | 50 | 0 | S1-22 |
| 40 | Green/FlucThreshold | 718 | 477 | b | W⁻²/L⁻²:8 d=2:4 Z2/zdist2:1 | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 21 | 0 | S1-28 |
| 41 | Green/FlucVanish | 556 | 477 | b | W^2:7 W⁻²/L⁻²:17 d=2:2 Z2/zdist2:14 | GavLGEX@3_5:33 | 35 | 0 | S1-17 |
| 42 | Green/GbEXP | 111 | 59 | b | W⁻²/L⁻²:1 | GavLGEX@3_5:33; GiiGEX@3_5:21; GijGEX@3_5:24; lem_GbEXP@3_5:14 | 6 | 1 | S1-30 |
| 43 | Green/GreenDeriv | 418 | 356 | a | Z2/zdist2:2 | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 26 | 0 | S1-17 |
| 44 | Green/IBP | 1653 | 1268 | b | d=2:2 Z2/zdist2:1 1/5:2 | GavLGEX@3_5:33 | 27 | 0 | S1-23 |
| 45 | Green/IBPDet | 335 | 287 | b | W⁻²/L⁻²:11 d=2:2 | GavLGEX@3_5:33 | 9 | 0 | S1-30 |
| 46 | Green/IBPPoly | 482 | 392 | a | - | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 10 | 0 | S1-19 |
| 47 | Green/IBPRem | 886 | 542 | b | d=2:1 Z2/zdist2:1 | GavLGEX@3_5:33; Main_DEL_COND@1_2:359 | 12 | 0 | S1-29 |
| 48 | Green/LDE | 818 | 712 | b | W^2:1 Z2/zdist2:3 | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 18 | 0 | S1-18 |
| 49 | Green/LDEQuad | 1105 | 924 | b | Z2/zdist2:1 | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 75 | 0 | S1-12 |
| 50 | Green/LDEQuadInst | 794 | 701 | a | Z2/zdist2:1 | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 33 | 0 | S1-19 |
| 51 | Green/LDEQuadMom | 970 | 796 | a | - | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 37 | 1 | S1-13 |
| 52 | Green/LDEQuadT | 1209 | 1019 | a | - | lem_GbEXP@3_5:14 | 61 | 0 | S1-14 |
| 53 | Green/LocalLaw | 378 | 352 | b | W^2:4 W⁻²/L⁻²:7 Z2/zdist2:43 | GavLGEX@3_5:33; GijGEX@3_5:24 | 2 | 0 | S1-27 |
| 54 | Green/Minor | 317 | 225 | a | - | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 22 | 0 | S1-10 |
| 55 | Green/MinorDiff | 1388 | 917 | b | d=2:1 | GavLGEX@3_5:33; def_asGMc@3_5:16 | 56 | 0 | S1-25 |
| 56 | Green/MinorDiffCond | 1464 | 912 | b | d=2:1 | def_asGMc@3_5:16; lem_GbEXP@3_5:14 | 37 | 0 | S1-26 |
| 57 | Green/MinorGoodLe | 474 | 336 | b | d=2:1 | def_asGMc@3_5:16 | 8 | 0 | S1-22 |
| 58 | Green/Pins | 593 | 342 | b | W^2:1 W⁻²/L⁻²:4 Z2/zdist2:32 | GavLGEX@3_5:33; GiiGEX@3_5:21; GijGEX@3_5:24; def_asGMc@3_5:16; lem_GbEXP@3_5:14; Eq:Gdecay_w@1_2:1349; Gtm... | 52 | 28 | S1-07 |
| 59 | Green/RowIndep | 1759 | 1313 | b | Z2/zdist2:2 1/5:1 | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) | 68 | 0 | S1-11 |
| 60 | Green/Stability | 415 | 363 | c | W^2:1 L^2:2 W⁻²/L⁻²:9 d=2:8 Z2/zdist2:16 | lem_propTH(4)@1_2:1140, eq:THETAinftinf@1_2:1141, eq:latticesum_d3 (merged Kernel/SumDecay.lean) | 4 | 0 | S1-15 |
| 61 | Hierarchy/ContractionBasic | 72 | 72 | b | W^2:1 W⁻²/L⁻²:4 Z2/zdist2:4 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 3 | 0 | S1-03 |
| 62 | Hierarchy/ContractionCutWords | 117 | 117 | b | W^2:1 Z2/zdist2:16 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 6 | 1 | S1-03 |
| 63 | Hierarchy/ContractionDirections | 198 | 181 | b | W⁻²/L⁻²:2 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 9 | 0 | S1-03 |
| 64 | Hierarchy/ContractionDrift | 81 | 81 | b | W^2:2 W⁻²/L⁻²:2 Z2/zdist2:12 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 3 | 1 | S1-03 |
| 65 | Hierarchy/ContractionEdgeSplits | 66 | 51 | a | - | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 4 | 3 | S1-04 |
| 66 | Hierarchy/ContractionFirstDerivativePositionSum | 77 | 77 | a | Z2/zdist2:4 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 3 | 0 | S1-04 |
| 67 | Hierarchy/ContractionPairPositionCut | 80 | 53 | b | W^2:2 Z2/zdist2:11 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 2 | 0 | S1-04 |
| 68 | Hierarchy/ContractionPairSplits | 107 | 49 | a | - | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 5 | 3 | S1-04 |
| 69 | Hierarchy/ContractionPositionLoopBridge | 80 | 46 | a | Z2/zdist2:7 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 5 | 1 | S1-04 |
| 70 | Hierarchy/ContractionSameEdgePositionCut | 69 | 47 | b | W^2:2 Z2/zdist2:7 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 2 | 0 | S1-04 |
| 71 | Hierarchy/ContractionSecondDerivativePositionSum | 151 | 151 | a | Z2/zdist2:12 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 5 | 0 | S1-04 |
| 72 | Hierarchy/ContractionSecondDerivativeTraceSum | 52 | 52 | a | Z2/zdist2:1 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 1 | 0 | S1-04 |
| 73 | Hierarchy/ContractionSecondLoop | 201 | 201 | b | W^2:3 Z2/zdist2:21 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 4 | 0 | S1-04 |
| 74 | Hierarchy/ContractionSecondLoopAllCuts | 111 | 81 | b | W^2:6 Z2/zdist2:12 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 5 | 3 | S1-04 |
| 75 | Hierarchy/ContractionSecondLoopSameEdge | 129 | 65 | b | W^2:2 Z2/zdist2:6 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 3 | 1 | S1-04 |
| 76 | Hierarchy/ContractionSecondLoopSameEdgeCut | 72 | 72 | b | W^2:1 Z2/zdist2:7 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 3 | 0 | S1-04 |
| 77 | Hierarchy/ContractionSecondLoopSameEdgeWord | 86 | 86 | b | W^2:1 Z2/zdist2:4 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 2 | 0 | S1-04 |
| 78 | Hierarchy/ContractionSum | 214 | 214 | b | W^2:1 Z2/zdist2:2 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 6 | 1 | S1-03 |
| 79 | Hierarchy/ContractionUnused | 120 | 120 | b | W^2:1 Z2/zdist2:2 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 5 | 1 | S1-03 |
| 80 | Hierarchy/LoopHierarchyCutBlockSumBound | 118 | 31 | b | W⁻²/L⁻²:1 Z2/zdist2:25 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 4 | 1 | S1-06 |
| 81 | Hierarchy/LoopHierarchyCutContinuity | 321 | 69 | b | W^2:2 W⁻²/L⁻²:3 Z2/zdist2:22 | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) | 13 | 2 | S1-06 |
| 82 | Hierarchy/WardResolvent | 193 | 162 | b | W^2:5 W⁻²/L⁻²:6 Z2/zdist2:12 | WI_calL@1_2:1036 | 6 | 2 | S1-31 |
| 83 | Induction/ConArg | 807 | 767 | b | W⁻²/L⁻²:2 d=2:2 Z2/zdist2:9 scales:22 | lem_ConArg@3_5:42; res_lo_bo_eta@3_5:52 | 2 | 0 | S1-32 |
| 84 | Induction/ConArgDet | 1348 | 966 | b | W^2:9 W⁻²/L⁻²:40 d=2:1 Z2/zdist2:55 | lem_ConArg@3_5:42 | 53 | 1 | S1-31 |
| 85 | Induction/Continuity | 1644 | 1462 | b | W^2:8 L^2:34 (WL)^2:33 d=2:2 Z2/zdist2:17 scales:84 | Gtmwc@1_2:1327; lRB1@1_2:1321 | 4 | 0 | S1-33,S1-34 |
| 86 | Induction/Step1 | 1515 | 1384 | b | W^2:10 L^2:3 (WL)^2:3 W⁻²/L⁻²:6 d=2:4 Z2/zdist2:58 scales:79 | Gtmwc@1_2:1327; con_st_ind@1_2:1296; lRB1@1_2:1321; lem:main_ind@1_2:1256; lem_GbEXP@3_5:14; GijGEX@3_5:24;... | 2 | 0 | S1-35,S1-36 |

## P.2 Totals (checked against T2002 portmap part E)

| dir | files | lines c9a24cf | kept 0c1330a | a/b/c | public decls | referenced by ST-2..6 |
|---|---|---|---|---|---|---|
| Gauss | 26 | 3542 | 2957 | 14/12/0 | 157 | 53 |
| Green | 34 | 26927 | 20318 | 9/24/1 | 992 | 37 |
| Hierarchy | 22 | 2715 | 2078 | 6/16/0 | 99 | 20 |
| Induction | 4 | 5314 | 4579 | 0/4/0 | 61 | 1 |
| **ST-1** | **86** | **38498** | **29932** | **29/56/1** | **1309** | **111** |

T2002 part E, row ST-1: 86 files / 38498 lines / 29932 kept / 29/56/1/0.  Recomputed: 86 / 38498 / 29932 / 29/56/1: equal.

## P.3 The interface of ST-1: declarations referenced by files of ST-2..ST-6 (ticket item 1)

A public declaration (def/theorem of an ST-1 file, name at `c9a24cf`) is "referenced" if its qualified name, a dotted suffix, or (when the short name is unique among the ST-1 declarations and has at least 6 characters) the short name occurs as an identifier in a file of ST-2, ST-3, ST-4, ST-5 or ST-6 (119 files, class != d, text at `c9a24cf`, comments stripped).  Short names of fewer than 6 characters (`h`, `U`, `w`, `congr`, `cons`) are excluded: with them the count was inflated by tactics and bound variables.

| ST-1 file:line | kind | declaration | referenced by (groups; files) | ticket |
|---|---|---|---|---|
| Gauss/GreenDerivative:25 | theorem | Gauss.hasDerivAt_green_moving | ST-2:5, ST-5:1 | S1-01 |
| Gauss/GreenTimeCont:28 | theorem | Gauss.continuous_green_of_isHermitian | ST-2:2, ST-4:2, ST-6:1 | S1-01 |
| Gauss/LoopCoordinateDerivative:25 | def | Gauss.coordinateBlock | ST-5:2 | S1-02 |
| Gauss/LoopCoordinateDerivative:30 | theorem | Gauss.HflowBlock_update | ST-2:1, ST-5:1 | S1-02 |
| Gauss/LoopCoordinateDerivative:57 | theorem | Gauss.hasDerivAt_green_HflowBlock_update | ST-5:1 | S1-02 |
| Gauss/LoopCoordinateDerivative:91 | def | Gauss.coordinateWordDeriv | ST-5:1 | S1-02 |
| Gauss/LoopCoordinateDerivative:150 | theorem | Gauss.hasDerivAt_gloop_update | ST-5:1 | S1-02 |
| Gauss/LoopCoordinateSecondDerivative:45 | def | Gauss.coordinateSecondWordDeriv | ST-2:1, ST-5:1 | S1-02 |
| Gauss/LoopCoordinateSecondDerivative:138 | theorem | Gauss.hasDerivAt_deriv_gloop_update | ST-2:1, ST-5:1 | S1-02 |
| Gauss/LoopDerivative:25 | def | Gauss.spectralMSign | ST-2:2, ST-5:1 | S1-01 |
| Gauss/LoopEnvelope:24 | theorem | Gauss.norm_matrix_entry_le_opNorm | ST-2:1, ST-4:2, ST-6:1 | S1-01 |
| Gauss/LoopEnvelope:32 | theorem | Gauss.norm_matrix_trace_le_card_mul | ST-2:6, ST-5:1, ST-6:1 | S1-01 |
| Gauss/LoopEnvelope:45 | theorem | Gauss.norm_Eblk_le_inv_W_sq | ST-2:6 | S1-01 |
| Gauss/LoopEnvelope:55 | theorem | Gauss.norm_Gsig_le_inv_eta | ST-2:5 | S1-01 |
| Gauss/LoopEnvelope:92 | theorem | Gauss.card_BlockIndex | ST-2:6, ST-5:1 | S1-01 |
| Gauss/LoopEnvelope:97 | theorem | Gauss.norm_gloop_le_crude | ST-2:5, ST-3:2, ST-5:2 | S1-01 |
| Gauss/LoopExpectationDerivative:25 | theorem | Gauss.hasDerivAt_integral_gloop_HflowBlock_spectralZ | ST-5:1 | S1-05 |
| Gauss/LoopFlowCoordinateChain:72 | theorem | Gauss.Xblock_eq_sum_coordinates | ST-5:1 | S1-05 |
| Gauss/LoopFlowCoordinateChain:125 | def | Gauss.gsigSpectralFlowDeriv | ST-5:1 | S1-05 |
| Gauss/LoopFlowCoordinateChain:141 | def | Gauss.spectralWordDeriv | ST-5:1 | S1-05 |
| Gauss/LoopGeneratorExpectation:23 | theorem | Gauss.integrable_samplewiseLoopGeneratorCuts | ST-5:1 | S1-06 |
| Gauss/LoopGeneratorExpectation:57 | theorem | Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts | ST-5:1 | S1-06 |
| Gauss/LoopGeneratorSamplewise:24 | def | Gauss.samplewiseLoopGeneratorCuts | ST-5:1 | S1-06 |
| Gauss/LoopGeneratorSamplewise:40 | theorem | Gauss.samplewise_loop_generator_eq_cuts | ST-5:1 | S1-06 |
| Gauss/LoopInitialValue:27 | def | Gauss.initialLoopValue | ST-3:2, ST-5:1 | S1-06 |
| Gauss/LoopInitialValue:47 | theorem | Gauss.integral_gloop_HflowBlock_zero | ST-5:1 | S1-06 |
| Gauss/LoopInitialValueProjectionWords:28 | def | Gauss.adjacentBlockWeight | ST-3:2 | S1-06 |
| Gauss/LoopInitialValueProjectionWords:91 | theorem | Gauss.initialLoopValue_nonempty | ST-3:2 | S1-06 |
| Gauss/LoopInitialValueScalar:50 | theorem | Gauss.trace_Eblk_eq_one | ST-2:2, ST-3:6, ST-5:3 | S1-06 |
| Gauss/LoopInitialValueScalar:63 | def | Gauss.initialGreenScalar | ST-3:2, ST-5:2 | S1-06 |
| Gauss/LoopInitialValueScalar:76 | theorem | Gauss.initialLoopValue_one_edge | ST-5:1 | S1-06 |
| Gauss/LoopInitialValueScalar:95 | theorem | Gauss.initialLoopValue_two_edges | ST-3:1, ST-5:1 | S1-06 |
| Gauss/LoopInitialValueSupport:21 | def | Gauss.AdjacentMismatch | ST-3:2 | S1-06 |
| Gauss/LoopInitialValueSupport:43 | theorem | Gauss.adjacentBlockWeight_all_same | ST-3:2 | S1-06 |
| Gauss/LoopSampleCont:30 | theorem | Gauss.continuous_green_HflowBlock_sample | ST-5:1 | S1-01 |
| Gauss/LoopSampleCont:58 | theorem | Gauss.continuous_gloopProd_HflowBlock_sample | ST-5:1 | S1-01 |
| Gauss/LoopSampleCont:64 | theorem | Gauss.continuous_gloop_HflowBlock_sample | ST-5:2 | S1-01 |
| Gauss/LoopSampleCont:71 | theorem | Gauss.measurable_gloop_HflowBlock_sample | ST-5:3 | S1-01 |
| Gauss/LoopTimeCont:27 | def | Gauss.HflowBlock | ST-2:1, ST-5:2 | S1-01 |
| Gauss/LoopTimeCont:35 | theorem | Gauss.HflowBlock_isHermitian | ST-2:1, ST-5:2 | S1-01 |
| Gauss/LoopTimeCont:83 | theorem | Gauss.continuous_matrixTrace | ST-2:2, ST-5:2 | S1-01 |
| Gauss/SpectralAlgebra:20 | theorem | Gauss.spectralM_sqrt_sq | ST-3:1, ST-4:1 | S1-01 |
| Gauss/SpectralAlgebra:27 | theorem | Gauss.spectralM_mul | ST-2:1, ST-3:2, ST-5:2 | S1-01 |
| Gauss/SpectralAlgebra:37 | theorem | Gauss.spectralM_quadratic | ST-5:1 | S1-01 |
| Gauss/SpectralAlgebra:43 | theorem | Gauss.norm_spectralM | ST-2:13, ST-3:17, ST-4:5, ST-5:4, ST-6:2 | S1-01 |
| Gauss/SpectralDerivative:18 | theorem | Gauss.hasDerivAt_spectralZ | ST-2:3, ST-5:1 | S1-01 |
| Gauss/SpectralWindow:21 | def | Gauss.spectralM | ST-2:28, ST-3:28, ST-4:8, ST-5:5, ST-6:3 | S1-01 |
| Gauss/SpectralWindow:24 | theorem | Gauss.spectralM_im | ST-2:18, ST-3:19, ST-4:6, ST-5:3, ST-6:2 | S1-01 |
| Gauss/SpectralWindow:27 | theorem | Gauss.spectralM_im_pos | ST-2:22, ST-3:17, ST-4:3, ST-5:5 | S1-01 |
| Gauss/SpectralWindow:34 | def | Gauss.spectralZ | ST-2:25, ST-3:17, ST-4:8, ST-5:6, ST-6:4 | S1-01 |
| Gauss/SpectralWindow:36 | theorem | Gauss.spectralZ_im | ST-2:13, ST-3:8, ST-4:2, ST-5:4, ST-6:2 | S1-01 |
| Gauss/SpectralWindow:39 | theorem | Gauss.continuous_spectralZ | ST-5:1 | S1-01 |
| Gauss/SpectralWindow:44 | theorem | Gauss.spectralZ_im_gap | ST-2:1, ST-5:1 | S1-01 |
| Green/EntryBlock:509 | def | Green.blkCoef2 | ST-3:1 | S1-16 |
| Green/EntryBlock:532 | theorem | Green.sum_blkCoef2 | ST-3:1 | S1-16 |
| Green/EntryCore:175 | def | Green.GoodEvent | ST-2:4 | S1-10 |
| Green/EntryCore:793 | theorem | Green.norm_condExp_le | ST-2:2 | S1-10 |
| Green/EntryDom:154 | def | Green.goodSet | ST-2:9 | S1-16 |
| Green/FlucAvg:96 | theorem | Green.measurable_green_apply | ST-3:1, ST-4:1 | S1-18 |
| Green/FlucIter:1369 | theorem | Green.FlucGainUpTo'.rho_nonneg | ST-2:1 | S1-20,S1-21 |
| Green/GbEXP:45 | theorem | Green.gbEXPV3 | ST-3:2, ST-6:1 | S1-30 |
| Green/LDEQuadMom:509 | theorem | Green.RowChaos.integrable_norm_pow | ST-2:1 | S1-13 |
| Green/Pins:85 | def | Green.AsGMcSeq | ST-2:1, ST-3:3 | S1-07 |
| Green/Pins:111 | def | Green.LoopDetSeq | ST-2:1, ST-3:3 | S1-07 |
| Green/Pins:119 | def | Green.GavLDetSeq | ST-3:3 | S1-07 |
| Green/Pins:152 | def | Green.GbEXPHypV3 | ST-2:7, ST-3:8, ST-4:4 | S1-07 |
| Green/Pins:166 | def | Green.GbEXPV3Theorem | ST-2:1 | S1-07 |
| Green/Pins:187 | theorem | Green.perTime_timeIcc_of_forall_seq | ST-2:1, ST-3:4, ST-6:1 | S1-07 |
| Green/Pins:205 | theorem | Green.perSeq_of_perTime_timeIcc | ST-2:1, ST-3:4, ST-4:1 | S1-07 |
| Green/Pins:227 | def | Green.GijGEXPTSwap | ST-2:1 | S1-07 |
| Green/Pins:236 | def | Green.GiiGEXPT | ST-2:1 | S1-07 |
| Green/Pins:246 | def | Green.AsGMcPT | ST-2:1, ST-4:1 | S1-07 |
| Green/Pins:253 | theorem | Green.rangeCond_mono | ST-2:1, ST-3:2, ST-4:1, ST-6:1 | S1-07 |
| Green/Pins:260 | theorem | Green.gijGEXPTSwap_giiGEXPT_of_V3 | ST-2:1, ST-4:1 | S1-07 |
| Green/Pins:293 | theorem | Green.v3_premises_of_mainIndHyp | ST-3:3 | S1-07 |
| Green/Pins:308 | theorem | Green.perTimeDomAt_of_nonpos | ST-3:1, ST-4:1 | S1-07 |
| Green/Pins:325 | theorem | Green.greenBlk_time_zero | ST-2:1, ST-3:1, ST-4:1 | S1-07 |
| Green/Pins:338 | theorem | Green.gexRHS_nonneg | ST-2:1 | S1-07 |
| Green/Pins:345 | theorem | Green.maxLoopPM_nonneg | ST-2:1 | S1-07 |
| Green/Pins:391 | theorem | Green.avgErr_time_zero | ST-2:1 | S1-07 |
| Green/Pins:488 | def | Green.Instance.sizes | ST-3:2, ST-4:1 | S1-07 |
| Green/Pins:495 | def | Green.Instance.energy | ST-2:8, ST-3:24, ST-4:1, ST-6:2 | S1-07 |
| Green/Pins:498 | def | Green.Instance.time | ST-4:1 | S1-07 |
| Green/Pins:501 | def | Green.Instance.sTime | ST-4:1 | S1-07 |
| Green/Pins:506 | theorem | Green.Instance.size_eq | ST-2:13, ST-3:23, ST-5:4, ST-6:1 | S1-07 |
| Green/Pins:511 | theorem | Green.Instance.sizeTendsto | ST-2:5, ST-3:15, ST-5:3, ST-6:1 | S1-07 |
| Green/Pins:518 | theorem | Green.Instance.bandwidth | ST-2:1, ST-3:12, ST-5:3, ST-6:1 | S1-07 |
| Green/Pins:524 | theorem | Green.Instance.rangeCond | ST-2:4, ST-3:11, ST-5:1, ST-6:1 | S1-07 |
| Green/Pins:537 | theorem | Green.Instance.energy_bulk | ST-2:4, ST-3:9, ST-6:1 | S1-07 |
| Green/Pins:575 | theorem | Green.Instance.premises | ST-4:1 | S1-07 |
| Hierarchy/ContractionCutWords:75 | theorem | blockRelabel_submatrix_split | ST-2:1 | S1-03 |
| Hierarchy/ContractionDrift:66 | theorem | neg_trace_scalarDrift_cutGlue_split | ST-2:1 | S1-03 |
| Hierarchy/ContractionEdgeSplits:15 | structure | Gauss.EdgeSplit | ST-2:1 | S1-04 |
| Hierarchy/ContractionEdgeSplits:21 | def | Gauss.edgeSplits | ST-2:1 | S1-04 |
| Hierarchy/ContractionEdgeSplits:40 | theorem | Gauss.edgeSplits_prefix_lengths | ST-2:1 | S1-04 |
| Hierarchy/ContractionPairSplits:15 | structure | Gauss.PairSplit | ST-2:1 | S1-04 |
| Hierarchy/ContractionPairSplits:23 | def | Gauss.pairSplits | ST-2:1 | S1-04 |
| Hierarchy/ContractionPairSplits:40 | theorem | Gauss.pairSplits_reconstruct | ST-2:1 | S1-04 |
| Hierarchy/ContractionPositionLoopBridge:19 | def | Gauss.segmentLoopIdx | ST-2:1 | S1-04 |
| Hierarchy/ContractionSecondLoopAllCuts:20 | def | Gauss.sameEdgeCutValue | ST-2:1 | S1-04 |
| Hierarchy/ContractionSecondLoopAllCuts:33 | def | Gauss.pairCutValue | ST-2:1 | S1-04 |
| Hierarchy/ContractionSecondLoopAllCuts:61 | theorem | Gauss.sum_coordinateSecondWordDeriv_allCuts | ST-2:1 | S1-04 |
| Hierarchy/ContractionSecondLoopSameEdge:52 | theorem | sum_coordinateBlock_trace_pair | ST-5:1 | S1-04 |
| Hierarchy/ContractionSum:156 | def | Gauss.blockRelabel | ST-2:1 | S1-03 |
| Hierarchy/ContractionUnused:110 | theorem | Gauss.sum_allCoords_trace_blocks | ST-2:1 | S1-03 |
| Hierarchy/LoopHierarchyCutBlockSumBound:30 | theorem | Gauss.sum_norm_SB_row | ST-2:4, ST-3:2, ST-4:1 | S1-06 |
| Hierarchy/LoopHierarchyCutContinuity:26 | theorem | Gauss.continuousOn_gloop_any_window | ST-5:1 | S1-06 |
| Hierarchy/LoopHierarchyCutContinuity:53 | theorem | Gauss.norm_gloop_any_window_le | ST-5:1 | S1-06 |
| Hierarchy/WardResolvent:25 | theorem | green_sub_green | ST-2:1, ST-3:1 | S1-31 |
| Hierarchy/WardResolvent:159 | theorem | sum_gloop_ward_last_div | ST-3:1, ST-5:1 | S1-31 |
| Induction/ConArgDet:71 | theorem | Ind.isUnit_sub_smul_one_of_im_ne_zero | ST-2:5, ST-3:2, ST-4:1, ST-5:2, ST-6:1 | S1-31 |

Total: 111 declarations of 1309, in 40 of the 86 files.

## P.4 Prerequisites outside ST-1: the import closures (kept graph) of the two chains

**Step 1 chain (`Induction/Step1.lean`)**: ST-1: 13 files / 5577 kept, MD: 10 files / 2620 kept, ST-2: 3 files / 643 kept, ST-3: 3 files / 1745 kept, ST-6: 1 files / 326 kept, none: 5 files / 585 kept, other: 7 files / 0 kept.

* MD: Path/PerTime (168 kept, cl a); Path/Walk (578 kept, cl a); Path/Step2Props (238 kept, cl b); Gauss/Domination (276 kept, cl a); Gauss/Envelope (175 kept, cl a); Hierarchy/Loops (267 kept, cl b); Gauss/Model (456 kept, cl b); Defs/StochDom (131 kept, cl a); Defs/Model (250 kept, cl b); Hierarchy/Operations (81 kept, cl a)
* ST-2: Path/Scales (263 kept, cl c); Path/Kernel (264 kept, cl b); Path/Step2Vocab (116 kept, cl c)
* ST-3: Induction/ScaleFacts (312 kept, cl c); Induction/PerTimeCalc (615 kept, cl a); Induction/Split (818 kept, cl b)
* ST-6: Induction/Defs (326 kept, cl b)

**`lem_GbEXP` chain (`Green/GbEXP.lean`)**: ST-1: 44 files / 21279 kept, MD: 13 files / 3164 kept, ST-2: 7 files / 2930 kept, ST-3: 2 files / 1433 kept, ST-6: 1 files / 326 kept, none: 5 files / 772 kept, other: 35 files / 0 kept.

* MD: Path/Step2Props (238 kept, cl b); Gauss/Model (456 kept, cl b); Path/PerTime (168 kept, cl a); Gauss/Domination (276 kept, cl a); Hierarchy/Loops (267 kept, cl b); Path/Walk (578 kept, cl a); Defs/Model (250 kept, cl b); Defs/StochDom (131 kept, cl a); Gauss/Envelope (175 kept, cl a); Gauss/LinearForm (204 kept, cl a); Hierarchy/Operations (81 kept, cl a); Gauss/SteinMatrix (198 kept, cl a); Hierarchy/OperationsPairWord (142 kept, cl a)
* ST-2: Path/Step2Local (428 kept, cl c); Path/GoodSet (847 kept, cl c); Path/KellStar (355 kept, cl b); Path/Step2Vocab (116 kept, cl c); Path/UBounds (657 kept, cl b); Path/Scales (263 kept, cl c); Path/Kernel (264 kept, cl b)
* ST-3: Induction/PerTimeCalc (615 kept, cl a); Induction/Split (818 kept, cl b)
* ST-6: Induction/Defs (326 kept, cl b)

**After cutting the imports of ST-2 and ST-6 files** (the RBM3D tickets replace them by the merged `Bctl/ellT/etaT` and by the probe vocabulary, P.7), the closures are:

* `Induction/Step1`: ST-1: 13, ST-3: 3, none: 5, MD: 9, other: 7; ST-3 files reached: Induction/ScaleFacts, Induction/PerTimeCalc, Induction/Split; MD files: Path/Step2Props, Gauss/Domination, Gauss/Envelope, Path/PerTime, Hierarchy/Loops, Gauss/Model, Defs/StochDom, Defs/Model, Hierarchy/Operations.  Cut edges (importer -> ST-2/ST-6 file): Induction/Step1 -> Induction/Defs; Induction/ConArg -> Induction/Defs; Induction/Continuity -> Induction/Defs; Induction/ScaleFacts -> Induction/Defs; Green/Pins -> Path/Step2Vocab; Green/Pins -> Induction/Defs; Path/ScalesBridge -> Path/Scales; Induction/ConArgDet -> Path/Scales; Path/Step2Props -> Path/Scales.  Links from non-`other` files to the Propagator/Loop layer (PT, KL): Path/ScalesBridge -> Loop/Kcal; Path/Step2Props -> Propagator/Basic.
* `Green/GbEXP`: ST-1: 44, MD: 12, other: 35, ST-3: 2, none: 5; ST-3 files reached: Induction/PerTimeCalc, Induction/Split; MD files: Path/Step2Props, Gauss/Model, Path/PerTime, Gauss/Domination, Hierarchy/Loops, Defs/Model, Defs/StochDom, Gauss/Envelope, Gauss/LinearForm, Hierarchy/Operations, Gauss/SteinMatrix, Hierarchy/OperationsPairWord.  Cut edges (importer -> ST-2/ST-6 file): Green/LocalLaw -> Path/Step2Local; Green/Stability -> Induction/Defs; Green/Pins -> Path/Step2Vocab; Green/Pins -> Induction/Defs; Green/CondDom -> Path/Scales; Path/Step2Props -> Path/Scales; Green/FlucAvg -> Induction/Defs.  Links from non-`other` files to the Propagator/Loop layer (PT, KL): Green/Stability -> Loop/Kcal; Green/Stability -> Loop/LatticeCount; Green/Stability -> Propagator/Prop5; Path/Step2Props -> Propagator/Basic.

Reading: the Step 1 chain is 13 ST-1 files (5577 kept) plus `Induction/{ScaleFacts, PerTimeCalc, Split}` (ST-3 by T2002, 1745 kept: re-assigned to S1-08, S1-09) and the vocabulary `Induction/Defs` (ST-6, replaced by the probe: S1-07); the `lem_GbEXP` chain is 44 ST-1 files (21279 kept) plus `Induction/{PerTimeCalc, Split}`.  After the cuts the two chains touch the propagator and K-loop layers only through the links listed (`Green/Stability` for `lem_GbEXP`; the merged definition of Theta through `Path/Step2Props` and the `Loop/Kcal` link of class-d `Path/ScalesBridge` for Step 1), so ST-1 takes `ML:Kbound` (`STKbound`) and the PT pins as hypotheses and needs no ST-2 file.  The 41 ST-1 files outside the `lem_GbEXP` chain are the Gaussian-calculus and loop-contraction files (consumed by ST-2/ST-5: P.3) and the Step 1 stream.

## P.5 Dependency layers of the ST-1 files (imports of the kept text; layer = longest import path inside ST-1)

| layer | files (kept lines) |
|---|---|
| 0 | FlowTimeCont (28), LDEQuad (924), Minor (225), Pins (342), ContractionBasic (72), ContractionDrift (81), WardResolvent (162) |
| 1 | GreenTimeCont (81), EntryCore (856), ContractionDirections (181) |
| 2 | LoopTimeCont (87), LDEQuadMom (796), RowIndep (1313), ContractionSum (214) |
| 3 | LoopSampleCont (76), CondRow (373), GreenDeriv (356), LDEQuadT (1019), ContractionUnused (120) |
| 4 | LoopEnvelope (119), ContractionCutWords (117) |
| 5 | SpectralWindow (50) |
| 6 | SpectralAlgebra (53) |
| 7 | SpectralDerivative (32), Stability (363), ConArgDet (966), Continuity (1462) |
| 8 | GreenDerivative (99), EntryBlock (557), ConArg (767) |
| 9 | LoopDerivative (128), EntryDom (641), FlucVanish (477), Step1 (1384) |
| 10 | LoopCoordinateDerivative (163), FlucAvg (411), LDE (712) |
| 11 | GreenCoordinateSecondDerivative (58), LoopFlowCoordinateChain (181), FlucIter (1540), IBPPoly (392) |
| 12 | LoopCoordinateSecondDerivative (134), LoopSpectralDriftCuts (203), FlucIterHigh (764), IBP (1268), LDEQuadInst (701) |
| 13 | LoopCoordinateDerivativeBounds (252), CondDom (359), EntryGauss (108), MinorGoodLe (336), ContractionSecondLoop (201) |
| 14 | LoopCoordinateIntegrability (113), AvgPins (567), CondStable (433), MinorDiff (917), ContractionSecondLoopSameEdge (65) |
| 15 | LoopFlowSteinExpectation (341), IBPRem (542), LocalLaw (352), MinorDiffCond (912), ContractionSecondLoopSameEdgeWord (86) |
| 16 | LoopFlowDerivativeEnvelope (195), Eq45Small (415), ContractionSecondLoopSameEdgeCut (72) |
| 17 | LoopExpectationDerivative (102), FlucThreshold (477), ContractionEdgeSplits (51) |
| 18 | LoopInitialValue (35), FlucAvgDet (524), ContractionPairSplits (49) |
| 19 | LoopInitialValueScalar (98), IBPDet (287), ContractionFirstDerivativePositionSum (77) |
| 20 | LoopInitialValueProjectionWords (105), GbEXP (59), ContractionSecondDerivativePositionSum (151) |
| 21 | LoopInitialValueSupport (60), ContractionSecondDerivativeTraceSum (52) |
| 22 | ContractionPositionLoopBridge (46) |
| 23 | ContractionSameEdgePositionCut (47) |
| 24 | ContractionPairPositionCut (53) |
| 25 | ContractionSecondLoopAllCuts (81) |
| 26 | LoopGeneratorSamplewise (58) |
| 27 | LoopGeneratorExpectation (106) |
| 28 | LoopHierarchyCutContinuity (69) |
| 29 | LoopHierarchyCutBlockSumBound (31) |

## P.6 Exponent tokens of d = 2 in the Step 1 chain: file:line at `c9a24cf` (code lines only)

Kinds: `W2` = `W ^ 2`, `L2`, `N2` = `(W * L) ^ 2` / `size ^ 2`, `inv2` = `W⁻²`-type, `d2` = `d = 2`, `e30` = the exponent `30` / `29/30` of `con_st_ind`.  Script `tokens.py`.

| file:line | kinds | line |
|---|---|---|
| Induction/Step1:146 | W2 | `scaleM L W E u ≤ (W : ℝ) ^ 2 := by` |
| Induction/Step1:150 | W2,L2,N2 | `have h1 : min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) ≤ (W : ℝ) ^ 2 := min_le_left _ _` |
| Induction/Step1:151 | W2,L2,N2 | `have h0 : 0 ≤ min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) :=` |
| Induction/Step1:153 | W2,L2,N2 | `calc (spectralM E).im * min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u))` |
| Induction/Step1:154 | W2 | `≤ 1 * (W : ℝ) ^ 2 := mul_le_mul hm h1 h0 zero_le_one` |
| Induction/Step1:161 | e30 | `(hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :` |
| Induction/Step1:173 | e30 | `have hρ30 : ρ ^ 30 ≤ Ms := by` |
| Induction/Step1:174 | e30 | `have h1 : ((1 - t) / (1 - s)) ^ 30 = (ρ ^ 30)⁻¹ := by` |
| Induction/Step1:177 | e30 | `have h2 : 0 < ρ ^ 30 := pow_pos hρ0 30` |
| Induction/Step1:181 | e30 | `have h1 : ρ = (ρ ^ 30) ^ ((1 : ℝ) / 30) := by` |
| Induction/Step1:183 | e30 | `calc ρ = (ρ ^ 30) ^ ((1 : ℝ) / 30) := h1` |
| Induction/Step1:198 | e30 | `have hinv : (scaleM L W E u)⁻¹ ≤ Ms ^ (-((29 : ℝ) / 30)) := by` |
| Induction/Step1:202 | e30 | `≤ Ms ^ ((1 : ℝ) / 30) * Ms ^ (-((29 : ℝ) / 30)) :=` |
| Induction/Step1:541 | inv2 | `have h2 : ((W : ℝ)⁻¹ ^ 2) ≤ (scaleM L W E u)⁻¹ := by` |
| Induction/Step1:825 | W2 | `gexRHS L W E u M a b ≤ 25 * B + ((W : ℝ) ^ 2)⁻¹ := by` |
| Induction/Step1:851 | W2 | `have h2 : (if zdist2 L (a - b) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0) ≤ ((W : ℝ) ^ 2)⁻¹ := by` |
| Induction/Step1:921 | W2 | `(hWg : ((W : ℝ) ^ 2)⁻¹ ≤ g)` |
| Induction/Step1:1461 | e30 | `have h4 : ((1 - 3 / 4 : ℝ) / (1 - 1 / 2)) ^ 30 = (1 / 2 : ℝ) ^ 30 := by norm_num` |
| Induction/Step1:1469 | e30 | `_ = (1 / 2 : ℝ) ^ 30 := by norm_num` |
| Induction/ConArgDet:712 | inv2 | `(W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k : BlockIndex L W,` |
| Induction/ConArgDet:716 | inv2 | `set S : ℝ := (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k : BlockIndex L W,` |
| Induction/ConArgDet:771 | W2 | `blockSel (W := W) b * (blockSel b)ᵀ = ((W : ℂ) ^ 2) • Eblk L W b := by` |
| Induction/ConArgDet:813 | W2 | `= ((W : ℂ) ^ 2) ^ (p + 1) * trace ((Yᴴ * Y * Eblk L W b) ^ (p + 1)) := by` |
| Induction/ConArgDet:820 | inv2 | `∑ i, bw b i * f i = (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, f (b, α) := by` |
| Induction/ConArgDet:837 | W2 | `≤ (W : ℝ) ^ 2 * (w.im)⁻¹ * loopMax L W H w (p * (2 * τ.length - 1)) ^ (1 / (p : ℝ)) := by` |
| Induction/ConArgDet:855 | W2 | `≤ ((W : ℝ) ^ 2 * (w.im)⁻¹) ^ (p' + 1) * LM := by` |
| Induction/ConArgDet:857 | W2 | `mul_assoc (((W : ℝ) ^ 2) ^ (p' + 1))]` |
| Induction/ConArgDet:863 | W2 | `_ ≤ (((W : ℝ) ^ 2 * (w.im)⁻¹) ^ (p' + 1) * LM) ^ (1 / ((p' + 1 : ℕ) : ℝ)) :=` |
| Induction/ConArgDet:866 | W2 | `_ = (W : ℝ) ^ 2 * (w.im)⁻¹ * LM ^ (1 / ((p' + 1 : ℕ) : ℝ)) := by` |
| Induction/ConArgDet:907 | inv2 | `have hS0 : 0 ≤ (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2 := by positivity` |
| Induction/ConArgDet:915 | inv2 | `_ = ∑ i, bw a0 i * ((W : ℝ)⁻¹ ^ 2 * ∑ β : Fin W × Fin W, ‖M i (am, β)‖ ^ 2) :=` |
| Induction/ConArgDet:917 | inv2 | `_ = (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W,` |
| Induction/ConArgDet:918 | inv2 | `((W : ℝ)⁻¹ ^ 2 * ∑ β : Fin W × Fin W, ‖M (a0, α) (am, β)‖ ^ 2) :=` |
| Induction/ConArgDet:919 | inv2 | `sum_bw_mul a0 (fun i => (W : ℝ)⁻¹ ^ 2 * ∑ β : Fin W × Fin W, ‖M i (am, β)‖ ^ 2)` |
| Induction/ConArgDet:920 | inv2 | `_ ≤ (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ((W : ℝ)⁻¹ ^ 2 * ((∑ k, ‖X (a0, α) k‖ ^ 2) * T)) := by` |
| Induction/ConArgDet:923 | inv2 | `_ = (W : ℝ)⁻¹ ^ 2 * ((W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2) * T := by` |
| Induction/ConArgDet:924 | inv2 | `have e : ∀ α : Fin W × Fin W, (W : ℝ)⁻¹ ^ 2 * ((∑ k, ‖X (a0, α) k‖ ^ 2) * T)` |
| Induction/ConArgDet:925 | inv2 | `= (∑ k, ‖X (a0, α) k‖ ^ 2) * ((W : ℝ)⁻¹ ^ 2 * T) := fun α => by ring` |
| Induction/ConArgDet:928 | inv2 | `_ ≤ (W : ℝ)⁻¹ ^ 2 * ((W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2)` |
| Induction/ConArgDet:929 | W2 | `* ((W : ℝ) ^ 2 * (w.im)⁻¹ * LMw ^ (1 / (p : ℝ))) :=` |
| Induction/ConArgDet:931 | W2,inv2 | `_ ≤ (W : ℝ)⁻¹ ^ 2 * ((z.im)⁻¹ * LMz) * ((W : ℝ) ^ 2 * (w.im)⁻¹ * LMw ^ (1 / (p : ℝ))) := by` |
| Induction/Continuity:621 | L2,N2 | `(spectralM E).im * ((((W * L) ^ 2 : ℕ) : ℝ) * /u - u'/) := by` |
| Induction/Continuity:626 | L2,N2 | `have h : (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u) - (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u') =` |
| Induction/Continuity:627 | L2,N2 | `(((W * L) ^ 2 : ℕ) : ℝ) * (u' - u) := by ring` |
| Induction/Continuity:632 | L2,N2 | `(hN : 1 ≤ (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) : (spectralM E).im ≤ scaleM L W E u := by` |
| Induction/Continuity:634 | W2 | `have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW)` |
| Induction/Continuity:635 | W2,L2,N2 | `have : (1 : ℝ) ≤ min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) := le_min hW2 hN` |
| Induction/Continuity:641 | L2,N2 | `scaleM L W E u ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by` |
| Induction/Continuity:645 | W2,L2,N2 | `have h1 : min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) ≤ (W : ℝ) ^ 2 := min_le_left _ _` |
| Induction/Continuity:646 | W2,L2,N2 | `have h2 : (W : ℝ) ^ 2 ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by` |
| Induction/Continuity:650 | L2 | `have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ this` |
| Induction/Continuity:652 | W2,L2,N2 | `have h0 : 0 ≤ min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) := by` |
| Induction/Continuity:654 | W2,L2,N2 | `calc (spectralM E).im * min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u))` |
| Induction/Continuity:655 | W2 | `≤ 1 * (W : ℝ) ^ 2 := mul_le_mul hm h1 h0 zero_le_one` |
| Induction/Continuity:935 | L2,N2 | `(hN1 : (1 - t)⁻¹ ≤ (((W * L) ^ 2 : ℕ) : ℝ))` |
| Induction/Continuity:936 | L2,N2 | `(hx : (((W * L) ^ 2 : ℕ) : ℝ) * /u - u'/ ≤ x) :` |
| Induction/Continuity:939 | L2,N2 | `have hN0 : 0 ≤ (((W * L) ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _` |
| Induction/Continuity:941 | L2,N2 | `have hNu' : 1 ≤ (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u') := by` |
| Induction/Continuity:942 | L2,N2 | `have h1 : 1 ≤ (((W * L) ^ 2 : ℕ) : ℝ) * (1 - t) := by` |
| Induction/Continuity:950 | L2,N2 | `have h2 : (spectralM E).im * ((((W * L) ^ 2 : ℕ) : ℝ) * /u - u'/) ≤ (spectralM E).im * x :=` |
| Induction/Continuity:976 | L2,N2 | `(hN1 : (1 - t)⁻¹ ≤ (((W * L) ^ 2 : ℕ) : ℝ)) (hx0 : 0 ≤ x)` |
| Induction/Continuity:977 | L2,N2 | `(hx1 : (((W * L) ^ 2 : ℕ) : ℝ) * /u - u'/ ≤ x)` |
| Induction/Continuity:1059 | L2,N2 | `((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4) ≤ (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) := by` |
| Induction/Continuity:1066 | L2,N2 | `(ω : Ω L W) {N E t u u' A c₁ : ℝ} (hN : N = (((W * L) ^ 2 : ℕ) : ℝ))` |
| Induction/Continuity:1078 | L2,N2 | `have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW hL1)` |
| Induction/Continuity:1109 | L2,N2 | `have hx : (((W * L) ^ 2 : ℕ) : ℝ) * /u - u'/ ≤ 1 / 10 :=` |
| Induction/Continuity:1132 | L2,N2 | `((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ k ≤` |
| Induction/Continuity:1134 | L2,N2 | `have hN1 : (1 : ℝ) ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by` |
| Induction/Continuity:1135 | L2,N2 | `have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW (by omega))` |
| Induction/Continuity:1137 | L2,N2 | `have hN0 : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by linarith` |
| Induction/Continuity:1143 | L2,N2 | `have h2 : ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ (k - 1) ≤ (scaleM L W E u)⁻¹ ^ (k - 1) :=` |
| Induction/Continuity:1145 | L2,N2 | `have h3 : ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ k ≤ ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ (k - 1) :=` |
| Induction/Continuity:1147 | L2,N2 | `calc ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ k ≤ ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ (k - 1) := h3` |
| Induction/Continuity:1189 | L2,N2 | `(ω : Ω L W) {N E s t u u' c₁ : ℝ} {k : ℕ} (hN : N = (((W * L) ^ 2 : ℕ) : ℝ))` |
| Induction/Continuity:1583 | e30 | `have hr : ((1 - contT n) / ((n : ℝ) + 3) ^ (-(4 : ℝ) / 41)) ^ 30 =` |
| Induction/ScaleFacts:89 | e30 | `(hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :` |
| Induction/ScaleFacts:90 | e30 | `scaleM L W E s ^ ((29 : ℝ) / 30) ≤ scaleM L W E u := by` |
| Induction/ScaleFacts:101 | e30 | `have ha30 : a ^ 30 = M := by` |
| Induction/ScaleFacts:103 | e30 | `have h29 : M ^ ((29 : ℝ) / 30) = a ^ 29 := by` |
| Induction/ScaleFacts:106 | e30 | `have h1 : (a⁻¹) ^ 30 ≤ q ^ 30 := by rw [inv_pow, ha30]; exact hstep` |
| Induction/ScaleFacts:111 | e30 | `calc M ^ ((29 : ℝ) / 30) = M * a⁻¹ := by` |
| Induction/ScaleFacts:124 | e30 | `scaleM (d.L n) (d.W n) (E n) (s n) ^ ((29 : ℝ) / 30) ≤` |
| Induction/ScaleFacts:205 | e30 | `((1 - chainTime t n₀ (k + 1) n) / (1 - chainTime t n₀ k n)) ^ 30 := by` |
| Induction/ScaleFacts:251 | e30 | `have hratio : ((1 - chainTime t n₀ (k + 1) n) / (1 - chainTime t n₀ k n)) ^ 30 =` |
| Induction/ScaleFacts:393 | e30 | `(chainTime (fun _ => 1 / 2) 1000 0 n) ^ ((29 : ℝ) / 30) ≤` |
| Induction/Split:176 | inv2 | `if p.1 = b then (W : ℝ)⁻¹ ^ 2 else 0` |
| Induction/Split:184 | inv2 | `have hcast : (((W : ℝ)⁻¹ ^ 2 : ℝ) : ℂ) = (W : ℂ)⁻¹ ^ 2 := by` |
| Induction/Split:615 | inv2 | `theorem norm_Eblk_le (b : Z2 L) : ‖Eblk L W b‖ ≤ (W : ℝ)⁻¹ ^ 2 := by` |
| Induction/Split:652 | inv2 | `‖gchain L W H z σ a‖ ≤ /z.im/⁻¹ ^ σ.length * ((W : ℝ)⁻¹ ^ 2) ^ a.length := by` |
| Induction/Split:664 | inv2 | `pow_succ' ((W : ℝ)⁻¹ ^ 2)]` |
| Induction/Split:671 | inv2 | `≤ /z.im/⁻¹ * ((W : ℝ)⁻¹ ^ 2) *` |
| Induction/Split:672 | inv2 | `(/z.im/⁻¹ ^ σ.length * ((W : ℝ)⁻¹ ^ 2) ^ a.length) := by` |
| Induction/Split:680 | inv2 | `‖gloop L W H z I‖ ≤ /z.im/⁻¹ ^ I.a.length * ((W : ℝ)⁻¹ ^ 2) ^ (I.a.length - 1) := by` |
| Induction/Split:695 | inv2 | `‖gloop L W H z I‖ ≤ η⁻¹ ^ I.a.length * ((W : ℝ)⁻¹ ^ 2) ^ (I.a.length - 1) := by` |
| Path/Scales:44 | W2 | `def scaleM (L W : ℕ) (E u : ℝ) : ℝ := (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u` |
| Path/Scales:100 | L2 | `ellT L u ^ 2 = min (1 / (1 - u)) ((L : ℝ) ^ 2) := by` |
| Path/Scales:115 | W2,L2 | `scaleM L W E u = (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - u)) := by` |
| Path/Scales:118 | W2,L2 | `= (W : ℝ) ^ 2 * (spectralM E).im * (min (1 / (1 - u)) ((L : ℝ) ^ 2) * (1 - u)) := by` |
| Path/Scales:120 | W2,L2 | `_ = (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - u)) := by` |
| Path/Scales:126 | W2,L2,N2 | `(spectralM E).im * min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) := by` |
| Path/Scales:127 | W2,L2,N2 | `have h : (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u) = (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (1 - u)) := by` |
| Path/Scales:129 | W2 | `rw [scaleM_eq hL hu, h, mul_comm ((W : ℝ) ^ 2) _, mul_assoc,` |
| Path/Scales:168 | W2 | `have hC : 0 ≤ (W : ℝ) ^ 2 * (spectralM E).im :=` |
| Path/Scales:175 | L2 | `have hmin : min 1 ((L : ℝ) ^ 2 * (1 - s)) * ((1 - v) / (1 - s)) ≤` |
| Path/Scales:176 | L2 | `min 1 ((L : ℝ) ^ 2 * (1 - v)) := by` |
| Path/Scales:178 | L2 | `· calc min 1 ((L : ℝ) ^ 2 * (1 - s)) * ((1 - v) / (1 - s)) ≤ 1 * 1 :=` |
| Path/Scales:181 | L2 | `· calc min 1 ((L : ℝ) ^ 2 * (1 - s)) * ((1 - v) / (1 - s))` |
| Path/Scales:182 | L2 | `≤ (L : ℝ) ^ 2 * (1 - s) * ((1 - v) / (1 - s)) :=` |
| Path/Scales:184 | L2 | `_ = (L : ℝ) ^ 2 * (1 - v) := by field_simp` |
| Path/Scales:185 | W2,L2 | `calc (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - s)) * (1 - v) / (1 - s)` |
| Path/Scales:186 | W2 | `= (W : ℝ) ^ 2 * (spectralM E).im *` |
| Path/Scales:187 | L2 | `(min 1 ((L : ℝ) ^ 2 * (1 - s)) * ((1 - v) / (1 - s))) := by ring` |
| Path/Scales:188 | W2,L2 | `_ ≤ (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - v)) :=` |
| Path/Scales:197 | e30 | `(hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :` |
| Path/Scales:203 | e30 | `have hq : 0 < ((1 - t) / (1 - s)) ^ 30 := pow_pos (div_pos hxt hxs) 30` |
| Path/Scales:205 | e30 | `have hr : ((1 - s) / (1 - t)) ^ 30 ≤ scaleM L W E s := by` |
| Path/Scales:212 | e30 | `have h30 : ((1 - s) / (1 - v)) ^ 30 ≤ scaleM L W E s :=` |
| Path/Scales:215 | e30 | `calc ((1 - s) / (1 - v)) ^ 29 = ((1 - s) / (1 - v)) ^ 30 * ((1 - v) / (1 - s)) := by` |
| Path/Scales:228 | L2,N2 | `(hcW : (((W * L) ^ 2 : ℕ) : ℝ) ^ c ≤ W)` |
| Path/Scales:229 | L2,N2 | `(hrange : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t) :` |
| Path/Scales:230 | L2,N2 | `(spectralM E).im * (((W * L) ^ 2 : ℕ) : ℝ) ^ (min (2 * c) τ) ≤ scaleM L W E t ∧` |
| Path/Scales:231 | L2,N2 | `(etaT E t)⁻¹ ≤ (((W * L) ^ 2 : ℕ) : ℝ) ^ (1 - τ) / (spectralM E).im := by` |
| Path/Scales:232 | L2,N2 | `set N : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hNdef` |
| Path/Scales:235 | L2,N2 | `have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW hL)` |
| Path/Scales:244 | W2 | `_ ≤ (W : ℝ) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hcW 2` |
| Path/Scales:310 | e30 | `example : ¬ ((scaleM 8 4 0 (1 / 2))⁻¹ ≤ ((1 - 3 / 4) / (1 - 1 / 2) : ℝ) ^ 30) := by` |
| Path/Step2Props:117 | e30 | `∀ᶠ n : ℕ in atTop, (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ≤ ((1 - t n) / (1 - s n)) ^ 30` |
| Green/Pins:370 | W2 | `if zdist2 L (a - b) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0 := by` |
| Green/Pins:408 | inv2 | `‖loopPM L W E u M a b‖ = ((W : ℝ)⁻¹ ^ 2) ^ 2 *` |
| Green/Pins:415 | inv2 | `((((W : ℝ)⁻¹ ^ 2) ^ 2 * ∑ β : Fin W × Fin W, ∑ α : Fin W × Fin W,` |
| Gauss/LoopEnvelope:46 | inv2 | `‖Eblk L W a‖ ≤ (W : ℝ)⁻¹ ^ 2 := by` |
| Gauss/LoopEnvelope:70 | inv2 | `≤ (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ l.length := by` |
| Gauss/LoopEnvelope:82 | inv2 | `_ ≤ η⁻¹ * ((W : ℝ)⁻¹ ^ 2) *` |
| Gauss/LoopEnvelope:83 | inv2 | `(η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ l.length := by` |
| Gauss/LoopEnvelope:87 | inv2 | `_ = (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ l.length *` |
| Gauss/LoopEnvelope:88 | inv2 | `(η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) := by ring` |
| Gauss/LoopEnvelope:92 | W2 | `theorem card_BlockIndex : Fintype.card (BlockIndex L W) = (L * W) ^ 2 := by` |
| Gauss/LoopEnvelope:101 | W2 | `(((L * W) ^ 2 : ℕ) : ℝ) *` |
| Gauss/LoopEnvelope:102 | inv2 | `(η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length := by` |
| Gauss/LoopEnvelope:111 | inv2 | `(η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (I.σ.zip I.a).length := by` |
| Gauss/LoopEnvelope:113 | W2 | `_ = (((L * W) ^ 2 : ℕ) : ℝ) *` |
| Gauss/LoopEnvelope:114 | inv2 | `(η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length := by` |
| Gauss/LoopEnvelope:125 | W2 | `(((L * W) ^ 2 : ℕ) : ℝ) *` |
| Gauss/LoopEnvelope:126 | inv2 | `(η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length := by` |

Total 144 lines in 9 files.

## P.7 Split table (ticket item 7): 36 proof tickets for ST-1

Rules.  Tickets follow a topological order of the kept import graph (the script checks that every dependency of a ticket is an earlier ticket).  Size: `est` = kept lines of the RBM2D sources x 1.0 (class a) / 1.1 (class b) / 1.5 (class c) + the new lines named in the notes + 60 (the compiled nonempty instance of every endpoint theorem, CLAUDE.md section 4 step 2) - the discount named in the notes; a file cut between two tickets is divided in proportion to its line ranges (the cut is a heading of the file).  Roles: `prover` = class a or class b with few exponent tokens; `prover-hard` = class b with many exponent tokens or deep proofs; `prover-max` = class c, interface-heavy, or endpoint.  "MD-k" = vocabulary tickets of T2002 E.2 (MD-1 T2006, MD-2 T2012, MD-3 T2013, MD-4 T2018, MD-5 T2021: all merged on `main`; tickets of this table that depend on MD-4 or MD-5: none).  "cut" = an import of an ST-2/ST-3/ST-6 file that the RBM3D ticket replaces by a merged declaration or cuts.

| id | RBM3D target (under `RBM3D/`) | RBM2D sources (kept) | kept | est | depends on (ST-1) | MD / external | role |
|---|---|---|---|---|---|---|---|
| S1-01 | Gauss/FlowCalculus.lean | Gauss/SpectralWindow (50); Gauss/SpectralAlgebra (53); Gauss/SpectralDerivative (32); Gauss/FlowTimeCont (28); Gauss/GreenTimeCont (81); Gauss/LoopTimeCont (87); Gauss/LoopSampleCont (76); Gauss/GreenDerivative (99); Gauss/LoopDerivative (128); Gauss/LoopEnvelope (119) | 753 | 603 | - | MD-1 ok; MD-2 ok; MD-3 ok | prover |
| S1-02 | Gauss/LoopCoordinate.lean | Gauss/LoopCoordinateDerivative (163); Gauss/LoopCoordinateSecondDerivative (134); Gauss/GreenCoordinateSecondDerivative (58); Gauss/LoopCoordinateDerivativeBounds (252); Gauss/LoopCoordinateIntegrability (113) | 720 | 816 | S1-01 | - | prover |
| S1-03 | Hierarchy/ContractionBasic.lean | Hierarchy/ContractionBasic (72); Hierarchy/ContractionDirections (181); Hierarchy/ContractionSum (214); Hierarchy/ContractionUnused (120); Hierarchy/ContractionCutWords (117); Hierarchy/ContractionDrift (81) | 785 | 924 | - | MD-1 ok; MD-2 ok; MD-3 ok | prover |
| S1-04 | Hierarchy/ContractionSecondLoop.lean | Hierarchy/ContractionSecondLoop (201); Hierarchy/ContractionSecondLoopSameEdge (65); Hierarchy/ContractionSecondLoopSameEdgeWord (86); Hierarchy/ContractionSecondLoopSameEdgeCut (72); Hierarchy/ContractionEdgeSplits (51); Hierarchy/ContractionPairSplits (49); Hierarchy/ContractionFirstDerivativePositionSum (77); Hierarchy/ContractionSecondDerivativePositionSum (151); Hierarchy/ContractionSecondDerivativeTraceSum (52); Hierarchy/ContractionPositionLoopBridge (46); Hierarchy/ContractionSameEdgePositionCut (47); Hierarchy/ContractionPairPositionCut (53); Hierarchy/ContractionSecondLoopAllCuts (81) | 1031 | 1152 | S1-02,S1-03 | - | prover |
| S1-05 | Gauss/LoopFlowStein.lean | Gauss/LoopFlowCoordinateChain (181); Gauss/LoopFlowDerivativeEnvelope (195); Gauss/LoopFlowSteinExpectation (341); Gauss/LoopExpectationDerivative (102) | 819 | 943 | S1-02 | MD-2 ok | prover-hard |
| S1-06 | Gauss/LoopGenerator.lean | Gauss/LoopSpectralDriftCuts (203); Gauss/LoopGeneratorSamplewise (58); Gauss/LoopGeneratorExpectation (106); Gauss/LoopInitialValue (35); Gauss/LoopInitialValueSupport (60); Gauss/LoopInitialValueScalar (98); Gauss/LoopInitialValueProjectionWords (105); Hierarchy/LoopHierarchyCutBlockSumBound (31); Hierarchy/LoopHierarchyCutContinuity (69) | 765 | 891 | S1-05,S1-04,S1-03 | PT pins hyp. | prover |
| S1-07 | Induction/Defs, Green/Pins, Test/Axioms.lean | Green/Pins (342); [Induction/Defs (326; from ST-6)] | 668 | 886 | - | cut: Path/Step2Vocab | prover-max |
| S1-08 | Induction/ScaleFacts, Induction/PerTimeCalc.lean | [Induction/ScaleFacts (312; from ST-3)]; [Induction/PerTimeCalc (615; from ST-3)] | 927 | 1343 | S1-07 | MD-2 ok | prover-hard |
| S1-09 | Induction/Split.lean | [Induction/Split (818; from ST-3)] | 818 | 960 | - | MD-1 ok; MD-2 ok; MD-3 ok | prover-hard |
| S1-10 | Green/EntryCore.lean | Green/Minor (225); Green/EntryCore (856) | 1081 | 1141 | - | - | prover |
| S1-11 | Green/RowIndep.lean | Green/RowIndep (1313) | 1313 | 1504 | S1-10 | MD-1 ok; MD-2 ok | prover-hard |
| S1-12 | Green/LDEQuad.lean | Green/LDEQuad (924) | 924 | 1076 | - | MD-1 ok; MD-2 ok | prover |
| S1-13 | Green/LDEQuadMom.lean | Green/LDEQuadMom (796) | 796 | 856 | S1-10,S1-12 | - | prover |
| S1-14 | Green/LDEQuadT.lean | Green/LDEQuadT (1019) | 1019 | 1079 | S1-13 | - | prover |
| S1-15 | Green/Stability.lean | Green/Stability (363) | 363 | 604 | S1-10,S1-07,S1-01 | MD-1 ok; MD-2 ok; KL: STKbound hyp.; PT pins hyp. | prover-max |
| S1-16 | Green/EntryDom.lean | Green/EntryBlock (557); Green/EntryDom (641) | 1198 | 1378 | S1-10,S1-15,S1-07,S1-08 | - | prover-hard |
| S1-17 | Green/FlucVanish.lean | Green/CondRow (373); Green/GreenDeriv (356); Green/FlucVanish (477) | 1206 | 1314 | S1-10,S1-11,S1-16,S1-03,S1-12,S1-01 | MD-1 ok; MD-2 ok | prover-hard |
| S1-18 | Green/LDE.lean | Green/FlucAvg (411); Green/LDE (712) | 1123 | 1295 | S1-17,S1-01,S1-07,S1-09,S1-11,S1-16 | MD-2 ok | prover-hard |
| S1-19 | Green/IBPPoly.lean | Green/IBPPoly (392); Green/LDEQuadInst (701) | 1093 | 1153 | S1-12,S1-18,S1-14,S1-11 | MD-2 ok | prover |
| S1-20 | Green/FlucIter.lean | Green/FlucIter (779 of 1540) | 779 | 917 | S1-18,S1-17 | - | prover-hard |
| S1-21 | Green/FlucIterGain.lean | Green/FlucIter (761 of 1540) | 761 | 897 | S1-18,S1-17,S1-20 | - | prover-hard |
| S1-22 | Green/MinorGoodLe.lean | Green/FlucIterHigh (764); Green/MinorGoodLe (336) | 1100 | 1270 | S1-20,S1-21 | - | prover-hard |
| S1-23 | Green/IBP.lean | Green/IBP (1268) | 1268 | 1455 | S1-18,S1-17,S1-19 | - | prover-hard |
| S1-24 | Green/CondDom.lean | Green/CondDom (359); Green/CondStable (433); Green/EntryGauss (108) | 900 | 1039 | S1-23,S1-16,S1-18,S1-19,S1-07,S1-08 | MD-2 ok; cut: Path/Scales | prover-hard |
| S1-25 | Green/MinorDiff.lean | Green/MinorDiff (917) | 917 | 1069 | S1-22 | - | prover-hard |
| S1-26 | Green/MinorDiffCond.lean | Green/MinorDiffCond (912) | 912 | 1063 | S1-25,S1-24,S1-01 | MD-1 ok; MD-2 ok; MD-3 ok; PT pins hyp. | prover-hard |
| S1-27 | Green/LocalLaw.lean | Green/AvgPins (567); Green/LocalLaw (352) | 919 | 1071 | S1-24,S1-17 | cut: Path/Step2Local | prover-hard |
| S1-28 | Green/FlucThreshold.lean | Green/Eq45Small (415); Green/FlucThreshold (477) | 892 | 1041 | S1-27,S1-26 | - | prover-hard |
| S1-29 | Green/IBPRem.lean | Green/IBPRem (542) | 542 | 656 | S1-24,S1-27 | - | prover-hard |
| S1-30 | Green/GbEXP.lean | Green/FlucAvgDet (524); Green/IBPDet (287); Green/GbEXP (59) | 870 | 1017 | S1-27,S1-29,S1-28,S1-16 | - | prover-max |
| S1-31 | Induction/ConArgDet.lean | Hierarchy/WardResolvent (162); Induction/ConArgDet (966) | 1128 | 1301 | S1-09,S1-01 | MD-1 ok; MD-3 ok; cut: Path/Scales | prover-hard |
| S1-32 | Induction/ConArg.lean | Induction/ConArg (767) | 767 | 904 | S1-07,S1-31,S1-08 | - | prover-hard |
| S1-33 | Induction/ContinuityNet.lean | Induction/Continuity (679 of 1462) | 679 | 807 | S1-07,S1-01 | MD-1 ok; MD-2 ok; MD-3 ok; PT pins hyp. | prover-hard |
| S1-34 | Induction/Continuity.lean | Induction/Continuity (783 of 1462) | 783 | 921 | S1-07,S1-01,S1-33 | MD-1 ok; MD-2 ok; MD-3 ok; PT pins hyp. | prover-hard |
| S1-35 | Induction/Step1Setup.lean | Induction/Step1 (882 of 1384) | 882 | 1031 | S1-07,S1-32,S1-33,S1-34,S1-08,S1-09,S1-01 | - | prover-hard |
| S1-36 | Induction/Step1.lean | Induction/Step1 (502 of 1384) | 502 | 862 | S1-07,S1-32,S1-33,S1-34,S1-08,S1-09,S1-01,S1-35 | - | prover-max |

Totals: 36 tickets, kept 32003 (86 files = 29932, plus `Induction/{ScaleFacts,PerTimeCalc,Split,Defs}` = 2071), estimated 37239 lines.
Target modules: 39 names (39 distinct), checked for an existing file `RBM3D/<name>.lean` in the main worktree and 48 ticket worktrees: existing: Test/Axioms (`Test/Axioms` is the registry: S1-07 adds the pins to it); every other name is new.
Roles: prover 10, prover-hard 22, prover-max 4.  Estimates per ticket: min 603, max 1504.

Critical path: 12 tickets (S1-10 -> S1-15 -> S1-16 -> S1-17 -> S1-18 -> S1-20 -> S1-21 -> S1-22 -> S1-25 -> S1-26 -> S1-28 -> S1-30), 13006 estimated lines.  First wave (no ST-1 dependency): S1-01, S1-03, S1-07, S1-09, S1-10, S1-12.  Tickets per dependency depth: 1: 6, 2: 7, 3: 6, 4: 3, 5: 2, 6: 2, 7: 2, 8: 2, 9: 2, 10: 2, 11: 1, 12: 1.

Notes per ticket (new content, merged overlap, cuts):
* S1-01: merged mE/zt/lemE (Defs/Semicircle) and the GLoopFlow envelopes cover SpectralWindow (50), SpectralAlgebra (53), LoopEnvelope (119): estimate lowered by their 222 kept lines
* S1-07: Induction/Defs (ST-6 by T2002) is replaced by the probe vocabulary; Test/Axioms registers the pins (DECISIONS section 16)
* S1-08: ScaleFacts, PerTimeCalc are ST-3 files by T2002; Step 1 and Green import them; new = probe 4.1 (closure, monotonicity)
* S1-09: Split is an ST-3 file by T2002; ConArgDet and Green/FlucAvg import it
* S1-15: Kstab2 = O(1 + log L) is a d = 2 lattice sum; the d >= 3 constants come from the merged Kernel/SumDecay and the PT pins (hypotheses)
* S1-27: Green/LocalLaw imports Path/Step2Local only for two private helper lemmas: copy them, do not import ST-2

Key statements per ticket (RBM2D `file:line name` at `c9a24cf`; names listed in the ticket definition are looked up in the inventory and the script fails if one is missing; tickets without a list show the last public theorem of each source file):

* S1-01: SpectralWindow:64 continuousOn_integral_norm_gloop_pow_spectralZ; SpectralAlgebra:43 norm_spectralM; SpectralDerivative:33 hasDerivAt_spectralZ_im; FlowTimeCont:53 continuous_seqHflow_entry_time; GreenTimeCont:88 continuous_green_Hflow_nonzero_index_example; LoopTimeCont:96 continuous_gloop_Hflow_one_edge_example; LoopSampleCont:77 measurable_gloop_HflowBlock_one_edge_example; GreenDerivative:82 hasDerivAt_green_HflowBlock_spectralZ; LoopDerivative:114 hasDerivAt_gloop_HflowBlock_spectralZ; LoopEnvelope:120 norm_gloop_HflowBlock_le_crude_on_Icc
* S1-02: LoopCoordinateDerivative:150 hasDerivAt_gloop_update; LoopCoordinateSecondDerivative:138 hasDerivAt_deriv_gloop_update; GreenCoordinateSecondDerivative:59 hasDerivAt_deriv_green_HflowBlock_update; LoopCoordinateDerivativeBounds:218 norm_gloop_coordinate_derivatives_le; LoopCoordinateIntegrability:131 measurable_integrable_actual_gloop_coordinate_derivatives
* S1-03: ContractionBasic:47 sum_Svar_diag_mul; ContractionDirections:189 weighted_trace_coordinate_diag; ContractionSum:201 sum_usedCoords_trace_blocks; ContractionUnused:110 sum_allCoords_trace_blocks; ContractionCutWords:87 sum_coordinate_cutChains; ContractionDrift:66 neg_trace_scalarDrift_cutGlue_split
* S1-04: ContractionSecondLoop:172 sum_twoEdge_mixed_deriv; ContractionSecondLoopSameEdge:101 sum_gsigCoordinateSecondDeriv_Eblk; ContractionSecondLoopSameEdgeWord:56 sum_gsigCoordinateSecondDeriv_word; ContractionSecondLoopSameEdgeCut:47 sum_sameEdge_cutLoops; ContractionEdgeSplits:52 edgeSplits_unique_position; ContractionPairSplits:83 pairSplits_unique_positions; ContractionFirstDerivativePositionSum:43 coordinateWordDeriv_eq_edgeSplits_sum; ContractionSecondDerivativePositionSum:130 coordinateSecondWordDeriv_eq_position_sums; ContractionSecondDerivativeTraceSum:33 sum_coordinateSecondWordDeriv_trace_positions; ContractionPositionLoopBridge:62 pairSplit_segment_products; ContractionSameEdgePositionCut:49 sum_coordinateSameEdgeTerm_cutLoops_of_mem; ContractionPairPositionCut:55 sum_coordinatePairTerm_cutLoops_of_mem; ContractionSecondLoopAllCuts:96 sum_gloopSecondWordDeriv_allCuts
* S1-05: LoopFlowCoordinateChain:193 loop_flow_derivative_actual_coordinate_chain; LoopFlowDerivativeEnvelope:105 norm_samplewise_loop_flow_derivative_le_envelope; LoopFlowSteinExpectation:295 expected_samplewise_loop_flow_derivative; LoopExpectationDerivative:87 deriv_integral_gloop_HflowBlock_spectralZ
* S1-06: LoopSpectralDriftCuts:196 trace_spectralWordDeriv_eq_sum_original_cuts; LoopGeneratorSamplewise:40 samplewise_loop_generator_eq_cuts; LoopGeneratorExpectation:57 deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts; LoopInitialValue:47 integral_gloop_HflowBlock_zero; LoopInitialValueSupport:70 initialLoopValue_all_same; LoopInitialValueScalar:95 initialLoopValue_two_edges; LoopInitialValueProjectionWords:107 adjacentBlockWeight_three; LoopHierarchyCutBlockSumBound:78 sum_norm_integral_pairCutIntegrand_le; LoopHierarchyCutContinuity:307 expected_gloop_hierarchy_integral_unconditional
* S1-07: Pins:152 GbEXPHypV3; Pins:166 GbEXPV3Theorem; Pins:227 GijGEXPTSwap; Pins:236 GiiGEXPT; Pins:246 AsGMcPT; Pins:260 gijGEXPTSwap_giiGEXPT_of_V3
* S1-08: ScaleFacts:72 scaleFacts_R1; ScaleFacts:87 scaleFacts_R2_pt; ScaleFacts:136 scaleFacts_ellT_ratio; ScaleFacts:148 scaleFacts_ellT_pow_four; PerTimeCalc:698 forbidden_region; PerTimeCalc:826 stepOneBootstrap
* S1-09: Split:529 loopMax_odd_sq_le; Split:635 split_norm_trace_mul_Eblk_le; Split:692 norm_gloop_le_of_le_abs_im; Split:385 norm_gloop_symIdx_split_le
* S1-10: Minor:255 green_diag_paper; EntryCore:818 norm_sum_coef_green_sub_le
* S1-11: RowIndep:1330 highProb_norm_rowSum_sq_le
* S1-12: LDEQuad:889 sum_coord_mul_deriv
* S1-13: LDEQuadMom:765 Vq_eq_ldeQuadRHS
* S1-14: LDEQuadT:995 mom_le_momVpow
* S1-15: Stability:304 eventually_Kstab2_mul_rpow_le
* S1-16: EntryBlock:594 norm_avgErr_le; EntryDom:696 avg_bound_stochDom
* S1-17: CondRow:358 greenMinorMat_eq_minorGreen; GreenDeriv:354 continuous_green_comp; FlucVanish:472 flucVanish_blockAvg2_eq_blkCoef2
* S1-18: FlucAvg:396 eventually_le_W; LDE:659 stochDom_normSq_Hflow_diag
* S1-19: IBPPoly:299 gaussIBP; LDEQuadInst:641 stochDom_ldeQuad
* S1-20: FlucIter:1453 integral_norm_flucAvg_pow_le_iter_budget
* S1-21: FlucIter:1453 integral_norm_flucAvg_pow_le_iter_budget
* S1-22: FlucIterHigh:751 flucGainUpTo'_of_minorDiffGainUpTo'; MinorGoodLe:319 minorGoodLe_of_goodEvent_flow
* S1-23: IBP:1311 ibpRem_eq_add
* S1-24: CondDom:316 perTimeDomAt_of_moment; CondStable:410 norm_greenDiagCentered_sub_minor_le; EntryGauss:93 giiSeq_of_asGMc
* S1-25: MinorDiff:907 bddMeas_applyOps_minorDiff_flucDiagSet
* S1-26: MinorDiffCond:890 flucGainUpTo'_goodEvent
* S1-27: AvgPins:70 LocalLawDetSeq; AvgPins:110 FixedTimeFASeq; AvgPins:115 IBPDetSeq; AvgPins:134 LocalLawDetThm
* S1-28: Eq45Small:248 hsmall_of_highProb; FlucThreshold:436 flucGain_of_localLaw
* S1-29: IBPRem:503 perTimeDomAt_ibpRem
* S1-30: FlucAvgDet:453 fixedTimeFAThm; IBPDet:241 ibpDetThm; GbEXP:45 gbEXPV3
* S1-31: WardResolvent:25 green_sub_green; WardResolvent:159 sum_gloop_ward_last_div; ConArgDet:537 ztTilde_arith; ConArgDet:1019 loopMax_two_mul_le_tilde; ConArgDet:834 trace_gram_rpow_le
* S1-32: ConArg:61 ConArgPin; ConArg:613 conArg
* S1-33: Continuity:65 GopboundPin
* S1-34: Continuity:1269 gopbound; Continuity:1261 Step1NetLift; Continuity:1331 step1NetLift
* S1-35: Step1:84 Step1TargetV3
* S1-36: Step1:1378 step1

Stream totals (kept lines / estimated lines / tickets):

* Gaussian calculus and loop algebra (S1-01..S1-06): 4873 / 5329 / 6
* pins, Step 1 scale facts and calculus, loop splitting (S1-07..S1-09): 2413 / 3189 / 3
* Green: `lem_GbEXP` (S1-10..S1-30): 19976 / 22895 / 21
* Step 1 proper: `lem_ConArg`, continuity, Step 1 (S1-31..S1-36): 4741 / 5826 / 6

## P.8 Probe extracts (script `extract.py`; docstrings omitted; full text: `RBM3D/Probe/T2015Pins.lean` on branch `t/T2015`)

### P.8.1 Estimate-level definitions (probe sections 1, 1b) and the Step 1 conclusions
```lean
-- probe line 177
def STKloop (n : ℕ) (E τ : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  KLK d (sz.L n) (sz.lam n) (sz.W n) E τ (KLloopOf d (sz.L n) σ a)
-- probe line 182
def STWB (n : ℕ) (τ : ℝ) (K : ℕ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) τ K
-- probe line 186
def STblk (n : ℕ) (x : Idx d (sz.L n) (sz.W n)) : Zd d (sz.L n) :=
  (split d (sz.L n) (sz.W n) x).1
-- probe line 190
def STGM (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  Gt sz n E τ true ω x y - (if x = y then mE E else 0)
-- probe line 195
def STmaxLoop2 (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩
    (fun p : Zd d (sz.L n) × Zd d (sz.L n) => ‖Lloop sz n E τ ![false, true] ![p.1, p.2] ω‖)
-- probe line 200
def STomegaC (n : ℕ) (E τ C₀ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖Gt sz n E τ true ω x y‖ ≤ C₀ then 1 else 0
-- probe line 205
def STgexRHS (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) : ℝ :=
  (∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
    ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
        ‖Lloop sz n E τ σ ![a', b'] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0)
-- probe line 217
def STLK (E τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1 p.2 ω - STKloop sz n (E n) (τ n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ k)
-- probe line 225
def STLmax (E τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1 p.2 ω‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))
-- probe line 234
def STDecay (E τ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1 p.2 ω - STKloop sz n (E n) (τ n) p.1 p.2‖)
      (fun n p _ => (sz.Bctl n (τ n)) ^ (1 / 5 : ℝ) *
          STWB sz n (τ n) (zdistInf d (sz.L n) (p.2 0 - p.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (τ n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
-- probe line 247
def STDecayStrong (E τ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz
      (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - τ n})
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1.1 p.1.2 ω - STKloop sz n (E n) (τ n) p.1.1 p.1.2‖)
      (fun n p _ => (sz.Bctl n (τ n)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
-- probe line 257
def STLocalMax (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (τ n) ω p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ (1 / 2 : ℝ))
-- probe line 264
def STLocalEntry (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (τ n) ω p.1 p.2‖ ^ 2)
    (fun n p _ => STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)))
-- probe line 272
def STExp2 (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (τ n) p.1 p.2 ω ∂(sz.seqP)) -
        STKloop sz n (E n) (τ n) p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (τ n)))
-- probe line 281
def STConStInd (𝔠d : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, (sz.Bctl n (t n)) ^ 𝔠d ≤ (1 - t n) / (1 - s n) ∧ (1 - t n) / (1 - s n) < 1
-- probe line 287
def STKbound (E : ℕ → ℝ) : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) →
    ∀ k : ℕ, 1 ≤ k →
      Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p _ => ‖STKloop sz n (E n) (τ n) p.1 p.2‖)
        (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))
-- probe line 310
def STindMax (n : ℕ) (E τ A : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n E τ ω x y‖ ≤ A then 1 else 0
-- probe line 315
def STGiiGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => STindMax sz n (E n) (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖STGM sz n (E n) (t n) ω p.1 p.2‖ ^ 2)
    (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)
-- probe line 323
def STGijGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  Prec sz
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => STindMax sz n (E n) (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖Gt sz n (E n) (t n) true ω p.1.1 p.1.2‖ ^ 2)
    (fun n p ω => STgexRHS sz n (E n) (t n) ω (STblk sz n p.1.1) (STblk sz n p.1.2))
-- probe line 333
def STGavLGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    Prec sz (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)
      (fun n _ _ => Ψ n ^ 2) →
    Prec sz (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖Lloop sz n (E n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (E n)‖)
      (fun n _ _ => Ψ n ^ 2)
-- probe line 347
def STStep1Loop (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
-- probe line 354
def STStep1Weak (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))
-- probe line 361
def STStep1LoopPT (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecPT sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
-- probe line 368
def STStep1WeakPT (E s t : ℕ → ℝ) : Prop :=
  PrecPT sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))
-- probe line 376
def STForbidden (E s u : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => STindMax sz n (E n) (u n) (2 * (sz.Bctl n (s n)) ^ (1 / 4 : ℝ)) ω *
      ‖STGM sz n (E n) (u n) ω p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (s n)) ^ (3 / 8 : ℝ))
```

### P.8.2 The pins (probe section 2) and the deterministic pins of the skeleton
```lean
-- probe line 396
def STflowE (z : ℕ → ℂ) : ℕ → ℝ := fun n => lemE (z n)
-- probe line 399
def STFlow {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
  sz.Admissible 𝔠 𝔡 ∧ ∀ n, sz.locDomain κ ε n (z n)
-- probe line 407
def STMainInd (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          (STLK sz (STflowE z) s ∧ STDecay sz (STflowE z) s ∧ STDecayStrong sz (STflowE z) s ∧
            STLocalMax sz (STflowE z) s ∧ STExp2 sz (STflowE z) s) →
          STConStInd sz 𝔠d s t →
          STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
            STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t ∧
            STDecayStrong sz (STflowE z) t
-- probe line 421
def STGbEXPii (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGiiGEX sz (STflowE z) t ε₀
-- probe line 428
def STGbEXPij (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGijGEX sz (STflowE z) t ε₀
-- probe line 435
def STGbEXPav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGavLGEX sz (STflowE z) t ε₀
-- probe line 442
def STGbEXP (d : ℕ) : Prop := STGbEXPii d ∧ STGbEXPij d ∧ STGbEXPav d
-- probe line 447
def STConArg (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 ε₁ C₀ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ → 0 < C₀ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
        STLmax sz (STflowE z) s →
        ∀ k : ℕ, 2 ≤ k →
          Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
            (fun n p ω => STomegaC sz n (STflowE z n) (t n) C₀ ω *
              ‖Lloop sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n _ _ => (sz.Bctl n (s n) *
              (etaT (STflowE z n) (s n) / etaT (STflowE z n) (t n))) ^ (k - 1))
-- probe line 462
def STStep1 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STKbound sz (STflowE z) → STLK sz (STflowE z) s → STLocalMax sz (STflowE z) s →
          STConStInd sz 𝔠d s t →
            STStep1Loop sz (STflowE z) s t ∧ STStep1Weak sz (STflowE z) s t
-- probe line 476
def STBootstrap (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalMax sz (STflowE z) s →
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → STForbidden sz (STflowE z) s u) →
        Whp sz (fun n => {ω | ∀ u ∈ Set.Icc (s n) (t n), ∀ x y : Idx d (sz.L n) (sz.W n),
          ‖STGM sz n (STflowE z n) u ω x y‖ ≤ (sz.Bctl n (s n)) ^ (1 / 4 : ℝ)})
-- probe line 490
def STNetLift (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
          ∀ k : ℕ, 1 ≤ k →
            Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
              (fun n p ω => ‖Lloop sz n (STflowE z n) (u n) p.1 p.2 ω‖)
              (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
          STStep1Loop sz (STflowE z) s t
-- probe line 1273
def STLoopBase : Prop :=
  ∀ (n : ℕ) (E u : ℝ) (σ : Fin 1 → Bool) (a : Fin 1 → Zd d (sz.L n)) (ω : sz.SeqΩ),
    (∀ x y : Idx d (sz.L n) (sz.W n), ‖Gt sz n E u true ω x y‖ ≤ 2) →
      ‖Lloop sz n E u σ a ω‖ ≤ 2
-- probe line 1540
def STEnvelope : Prop :=
  ∀ (n : ℕ) (E u : ℝ), |E| < 2 → u < 1 → ∀ (k : ℕ) (σ : Fin (k + 1) → Bool)
    (a : Fin (k + 1) → Zd d (sz.L n)) (ω : sz.SeqΩ),
    ‖Lloop sz n E u σ a ω‖ ≤ (etaT E u)⁻¹ ^ (k + 1) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ k
```

### P.8.3 The skeleton and the compiled instances (statements only, `--head`)
```lean
-- probe line 1775
theorem ST_step1_skeleton
    (hGii : STGbEXPii d) (hCA : STConArg d) (hBoot : STBootstrap d) (hNet : STNetLift d)
    {κ ε 𝔡 𝔠 𝔠d ε₀ : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (hε₀ : 0 < ε₀) (h𝔠d0 : 0 < 𝔠d) (h𝔠d : 𝔠d ≤ 1 / 100) (z : ℕ → ℂ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) (hEnv : STEnvelope sz)
    (hsmall : ∀ᶠ n in atTop, 2 * (sz.Bctl n (s n)) ^ (1 / 4 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ∧
      sz.Bctl n (s n) ≤ 1)
    (hKb : STKbound sz (STflowE z)) (ha : STLK sz (STflowE z) s)
    (hc : STLocalMax sz (STflowE z) s) (hcon : STConStInd sz 𝔠d s t) :
    STStep1Loop sz (STflowE z) s t ∧ STStep1Weak sz (STflowE z) s t
-- probe line 1636
theorem ST_apriori (hsize : Tendsto sz.size atTop atTop) (hEnv : STEnvelope sz) (hCA : STConArg d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s u : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsu : ∀ n, s n ≤ u n)
    (hu1 : ∀ n, u n < 1) (hL : STLmax sz (STflowE z) s) (k : ℕ) (hk : 2 ≤ k) :
    Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => STomegaC sz n (STflowE z n) (u n) 2 ω *
        ‖Lloop sz n (STflowE z n) (u n) p.1 p.2 ω‖)
      (fun n _ _ => (sz.Bctl n (s n) *
        (etaT (STflowE z n) (s n) / etaT (STflowE z n) (u n))) ^ (k - 1))
-- probe line 634
theorem inst_mainInd (h : STMainInd 3) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ((STLK sz0 (STflowE z0) sInst ∧ STDecay sz0 (STflowE z0) sInst ∧
          STDecayStrong sz0 (STflowE z0) sInst ∧ STLocalMax sz0 (STflowE z0) sInst ∧
          STExp2 sz0 (STflowE z0) sInst) →
        (STLK sz0 (STflowE z0) tInst ∧ STLmax sz0 (STflowE z0) tInst ∧
          STDecay sz0 (STflowE z0) tInst ∧ STExp2 sz0 (STflowE z0) tInst ∧
          STLocalEntry sz0 (STflowE z0) tInst ∧ STDecayStrong sz0 (STflowE z0) tInst))
-- probe line 650
theorem inst_gbEXP (h : STGbEXP 3) :
    STGiiGEX sz0 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tInst (1 / 20) ∧
      STGavLGEX sz0 (STflowE z0) tInst (1 / 20)
-- probe line 665
theorem inst_conArg (h : STConArg 3) (hL : STLmax sz0 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1))
-- probe line 679
theorem inst_step1 (h : STStep1 3) {𝔠d : ℝ} (h0 : 0 < 𝔠d) (h1 : 𝔠d ≤ 1 / 100)
    (hK : STKbound sz0 (STflowE z0)) (ha : STLK sz0 (STflowE z0) sInst)
    (hc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst
-- probe line 690
theorem inst_bootstrap (h : STBootstrap 3) (hc : STLocalMax sz0 (STflowE z0) sInst)
    (hF : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
      STForbidden sz0 (STflowE z0) sInst u) :
    Whp sz0 (fun n => {ω | ∀ u ∈ Set.Icc (sInst n) (tInst n),
      ∀ x y : Idx 3 (sz0.L n) (sz0.W n),
        ‖STGM sz0 n (STflowE z0 n) u ω x y‖ ≤ (sz0.Bctl n (sInst n)) ^ (1 / 4 : ℝ)})
-- probe line 701
theorem inst_netLift (h : STNetLift 3)
    (hu : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
      ∀ k : ℕ, 1 ≤ k →
        Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (u n) p.1 p.2 ω‖)
          (fun n _ _ => ((1 - sInst n) / (1 - u n)) ^ (k - 1) * (sz0.Bctl n (sInst n)) ^ (k - 1))) :
    STStep1Loop sz0 (STflowE z0) sInst tInst
-- probe line 1889
theorem inst_skeleton (hGii : STGbEXPii 3) (hCA : STConArg 3) (hBoot : STBootstrap 3) (hNet : STNetLift 3)
    (hEnv : STEnvelope sz0) {𝔠d : ℝ} (h0 : 0 < 𝔠d) (h1 : 𝔠d ≤ 1 / 100)
    (hKb : STKbound sz0 (STflowE z0)) (ha : STLK sz0 (STflowE z0) sInst)
    (hc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst
-- probe line 1901
theorem inst_precPT (h : STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst) :
    STStep1WeakPT sz0 (STflowE z0) sInst tInst
-- probe line 725
theorem inst_gbEXP_endT (h : STGbEXP 3) :
    STGiiGEX sz0 (STflowE z0) tEnd (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tEnd (1 / 20) ∧
      STGavLGEX sz0 (STflowE z0) tEnd (1 / 20)
-- probe line 737
theorem inst_conArg_endT (h : STConArg 3) (hL : STLmax sz0 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) (tEnd n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) (tEnd n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            etaT (STflowE z0 n) (tEnd n))) ^ (k - 1))
-- probe line 759
theorem sz1_admissible : sz1.Admissible (1 / 6) (1 / 10)
-- probe line 777
theorem inst_mainInd_lowg (h : STMainInd 3) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ((STLK sz1 (STflowE z0) sInst ∧ STDecay sz1 (STflowE z0) sInst ∧
          STDecayStrong sz1 (STflowE z0) sInst ∧ STLocalMax sz1 (STflowE z0) sInst ∧
          STExp2 sz1 (STflowE z0) sInst) →
        (STLK sz1 (STflowE z0) tInst ∧ STLmax sz1 (STflowE z0) tInst ∧
          STDecay sz1 (STflowE z0) tInst ∧ STExp2 sz1 (STflowE z0) tInst ∧
          STLocalEntry sz1 (STflowE z0) tInst ∧ STDecayStrong sz1 (STflowE z0) tInst))
-- probe line 793
theorem inst_gbEXP_lowg (h : STGbEXP 3) :
    STGiiGEX sz1 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz1 (STflowE z0) tInst (1 / 20) ∧
      STGavLGEX sz1 (STflowE z0) tInst (1 / 20)
-- probe line 807
theorem inst_conArg_lowg (h : STConArg 3) (hL : STLmax sz1 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz1 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz1.L n)))
        (fun n p ω => STomegaC sz1 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz1 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz1.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1))
-- probe line 820
theorem inst_step1_lowg (h : STStep1 3) {𝔠d : ℝ} (h0 : 0 < 𝔠d) (h1 : 𝔠d ≤ 1 / 100)
    (hK : STKbound sz1 (STflowE z0)) (ha : STLK sz1 (STflowE z0) sInst)
    (hc : STLocalMax sz1 (STflowE z0) sInst) :
    STStep1Loop sz1 (STflowE z0) sInst tInst ∧ STStep1Weak sz1 (STflowE z0) sInst tInst
```

### P.8.4 `bind2_extra.lean`: the text appended to `bind1.lean` to show that `STEnvelope` is the merged sharp envelope (report b.2)
```lean
namespace RBM.Gauss.Sizes
open RBM RBM.Probe.T2015 RBM.Path RBM.Gauss Filter
variable {d : ℕ} (sz : Sizes d)
/-- `STEnvelope` is the merged sharp envelope `norm_loopM_le_sharp` at `blockMat (seqHflow ..)`. -/
theorem STEnvelope_of_merged : STEnvelope sz := by
  intro n E u hE hu k σ a ω
  have hpos : 0 < etaT E u := etaT_pos hE hu
  have hH : (blockMat d (sz.L n) (sz.W n) (seqHflow sz n u ω)).IsHermitian :=
    (seqHflow_isHermitian sz n u ω).submatrix _
  exact norm_loopM_le_sharp d (sz.L n) (sz.W n) hH hpos (by rw [← etaT_eq_zt_im, abs_of_pos hpos]) σ a
end RBM.Gauss.Sizes
#print axioms RBM.Gauss.Sizes.STEnvelope_of_merged
```

### P.8.5 Merged declarations used by each pin (script `pinuses.py`: the identifiers of the pin statement and of the probe `ST...` definitions it reaches; `Eblk` is inside `Lloop` (merged `loopM`), `Bparam` inside `Bctl`)
```
$ python3 pinuses.py T2015Pins.lean STMainInd STGbEXP STConArg STStep1 STBootstrap STNetLift STKbound STFlow
STMainInd: Sizes Admissible locDomain Idx Zd zdistInf Prec Gt Lloop KLK Bctl Bparam ellT mE lemE lemT   [via 15 probe definitions]
STGbEXP: Sizes Admissible locDomain Idx Zd zdistInf Prec Gt Lloop mE lemE lemT   [via 14 probe definitions]
STConArg: Sizes Admissible locDomain Idx Zd Prec Gt Lloop Bctl etaT lemE   [via 5 probe definitions]
STStep1: Sizes Admissible locDomain Idx Zd Prec TimeIcc Gt Lloop KLK Bctl mE lemE lemT   [via 11 probe definitions]
STBootstrap: Sizes Admissible locDomain Idx Prec Whp Gt Bctl mE lemE lemT   [via 7 probe definitions]
STNetLift: Sizes Admissible locDomain Zd Prec TimeIcc Lloop Bctl lemE lemT   [via 4 probe definitions]
STKbound: Zd Prec KLK Bctl   [via 2 probe definitions]
STFlow: Sizes Admissible locDomain   [via 1 probe definitions]
```

## P.9 Mathlib names used by the probe (script `names.py`: every candidate identifier of the probe text is `#check`ed in a file that imports the probe's modules and opens only `MeasureTheory ProbabilityTheory Filter Matrix`)

Candidates 167; elaborate (present in Lean core, Std or Mathlib): 144; do not elaborate under these opens: 23 (names of RBM3D declarations, which live in namespace `RBM`, local hypotheses, field projections).  No name was invented: a name absent from Mathlib would be in the second list and would fail the build.

Present, one line each (`#check @name`, the type cut at 150 characters; script `names.py`):

```
Bool.false_eq_true : (false = true) = False
Complex.norm_natCast : ∀ (n : ℕ), ‖↑n‖ = ↑n
ENNReal.ofReal : ℝ → ℝ≥0∞
@ENNReal.ofReal_add : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
@ENNReal.ofReal_le_ofReal : ∀ {p q : ℝ}, p ≤ q → ENNReal.ofReal p ≤ ENNReal.ofReal q
@Eventually.of_forall : ∀ {α : Type u_1} {p : α → Prop} {f : Filter α}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
@Finset.mem_univ : ∀ {α : Type u_1} [inst : Fintype α] (x : α), x ∈ Finset.univ
@Finset.mul_sum : ∀ {ι : Type u_1} {R : Type u_2} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R), a * ∑ i ∈ s, f i = ∑ i ∈ s,
@Finset.sum_ite_eq' : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M), (∑ x ∈ s, 
@Finset.sum_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι} [AddLeftMono N], (∀ i
@Finset.sup'_le : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α}, (∀ b ∈ s, f b ≤ a) → 
fun p inst => Finset.filter p Finset.univ : (p : ?m.3 → Prop) → DecidablePred p → Finset ?m.3
fun α inst => Finset.univ.sup' : (α : Type u_1) → SemilatticeSup α → Finset.univ.Nonempty → (?m.4 → α) → α
@Fintype.sum_prod_type : ∀ {γ : Type u_1} {α₁ : Type u_2} {α₂ : Type u_3} [inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid γ] (f : α₁
@List.ofFn : {α : Type u_1} → {n : ℕ} → (Fin n → α) → List α
@List.ofFn_succ : ∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofFn f = f 0 :: List.ofFn fun i => f i.succ
@List.ofFn_zero : ∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
@List.prod_cons : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] {a : α} {l : List α}, (a :: l).prod = a * l.prod
@List.prod_nil : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α], [].prod = 1
@conjTranspose_apply : ∀ {m : Type u_2} {n : Type u_3} {α : Type u_1} [inst : Star α] (M : Matrix m n α) (i : m) (j : n), Mᴴ j i = star (M i j)
@conjTranspose_nonsing_inv : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : Matrix n n α) [ins
@conjTranspose_one : ∀ {n : Type u_2} {α : Type u_1} [inst : DecidableEq n] [inst_1 : NonAssocSemiring α] [inst_2 : StarRing α], 1ᴴ = 1
@conjTranspose_smul : ∀ {m : Type u_2} {n : Type u_3} {R : Type u_4} {α : Type u_1} [inst : Star R] [inst_1 : Star α] [inst_2 : SMul R α] [StarModule 
@conjTranspose_sub : ∀ {m : Type u_2} {n : Type u_3} {α : Type u_1} [inst : AddGroup α] [inst_1 : StarAddMonoid α] (M N : Matrix m n α), (M - N)ᴴ = Mᴴ
@diag : {n : Type u_2} → {α : Type u_1} → Matrix n n α → n → α
@diagonal : {n : Type u_2} → {α : Type u_1} → [DecidableEq n] → [Zero α] → (n → α) → Matrix n n α
@inv_submatrix_equiv : ∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] [inst_3 : Fint
@mul_diagonal : ∀ {m : Type u_2} {n : Type u_3} {α : Type u_1} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n] (d :
@nonsing_inv_eq_ringInverse : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : Matrix n n α), A⁻
@Matrix.one_apply : ∀ {n : Type u_2} {α : Type u_1} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α] {i j : n}, 1 i j = if i = j then 1 else 
@submatrix_apply : ∀ {l : Type u_2} {m : Type u_3} {n : Type u_4} {o : Type u_5} {α : Type u_1} (A : Matrix m n α) (r : l → m) (c : o → n) (i : l) (j 
@trace : {n : Type u_1} → {R : Type u_2} → [Fintype n] → [AddCommMonoid R] → Matrix n n R → R
Nat.add_sub_cancel : ∀ (n m : ℕ), n + m - m = n
@Nat.cast_nonneg : ∀ {α : Type u_1} [inst : Semiring α] [inst_1 : PartialOrder α] [IsOrderedRing α] (n : ℕ), 0 ≤ ↑n
@Nat.le_self_pow : ∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
@Nat.mul_pos : ∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
Nat.one_le_pow : ∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
@Nat.pos_of_ne_zero : ∀ {n : ℕ}, n ≠ 0 → 0 < n
@Nat.pow_le_pow_left : ∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
Nat.sub_le : ∀ (n m : ℕ), n - m ≤ n
Nat.sub_self : ∀ (n : ℕ), n - n = 0
Real.exp : ℝ → ℝ
@Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
@Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
@Real.rpow_le_one : ∀ {x z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ z → x ^ z ≤ 1
@Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
@Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
@Real.rpow_le_rpow_of_exponent_ge : ∀ {x y z : ℝ}, 0 < x → x ≤ 1 → z ≤ y → x ^ y ≤ x ^ z
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.rpow_le_rpow_of_nonpos : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
@Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
@Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_neg_one : ∀ (x : ℝ), x ^ (-1) = x⁻¹
@Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
Real.rpow_one : ∀ (x : ℝ), x ^ 1 = x
@Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
Real.sqrt : ℝ → ℝ
@Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
Real.sqrt_pos.mpr : 0 < ?m.1 → 0 < √?m.1
@Real.zero_rpow : ∀ {x : ℝ}, x ≠ 0 → 0 ^ x = 0
@Set.Icc : {α : Type u_1} → [Preorder α] → α → α → Set α
@Set.mem_union : ∀ {α : Type u_1} (x : α) (a b : Set α), x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b
@abs_nonneg : ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
@abs_of_pos : ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a : α} [AddLeftMono α], 0 < a → |a| = a
@add_le_add : ∀ {α : Type u_1} {a b c d : α} [inst : Add α] [inst_1 : Preorder α] [AddLeftMono α] [AddRightMono α], a ≤ b → c ≤ d → a + c ≤ b + d
@by_cases : ∀ {p q : Prop}, (p → q) → (¬p → q) → q
@by_contra : ∀ {p : Prop}, (¬p → False) → p
@div_eq_mul_inv : ∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b = a * b⁻¹
@div_le_div_iff₀ : ∀ {G₀ : Type u_1} [inst : CommGroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}, 0 < b → 0 < d → (a 
@div_le_div_of_nonneg_left : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c :
@div_le_div_of_nonneg_right : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}, a ≤ b → 0 ≤ c 
@div_nonneg : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a b : G₀}, 0 ≤ a → 0 ≤ b → 0 ≤ a / b
@eventually_ge_atTop : ∀ {α : Type u_1} [inst : Preorder α] (a : α), ∀ᶠ (x : α) in atTop, a ≤ x
@gt_mem_nhds : ∀ {α : Type u_1} [ts : TopologicalSpace α] [inst : Preorder α] [OrderTopology α] {a b : α}, b < a → ∀ᶠ (x : α) in nhds b, x < a
@inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b : G₀}, 0 < b → b ≤ 
@inv_div : ∀ {α : Type u_1} [inst : DivisionMonoid α] (a b : α), (a / b)⁻¹ = b / a
@inv_le_comm₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b : G₀}, 0 < a → 0
inv_nonneg.mpr : 0 ≤ ?m.5 → 0 ≤ ?m.5⁻¹
@inv_one : ∀ {G : Type u_1} [inst : InvOneClass G], 1⁻¹ = 1
@ite_false : ∀ {α : Sort u_1} {x : Decidable False} (a b : α), (if False then a else b) = b
@ite_true : ∀ {α : Sort u_1} {x : Decidable True} (a b : α), (if True then a else b) = a
@le_max_left : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max a b
@le_max_right : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max a b
@le_mul_of_one_le_left : ∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Zero α] {a b : α} [inst_2 : Preorder α] [MulPosMono α], 0 ≤ b → 1 ≤ a → b ≤
@le_mul_of_one_le_right : ∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Zero α] {a b : α} [inst_2 : Preorder α] [PosMulMono α], 0 ≤ a → 1 ≤ b → a 
@le_of_pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀} {n : ℕ} [MulPosMono 
@le_rfl : ∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ≤ a
@le_trans : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c
@lt_of_le_of_lt : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b < c → a < c
@lt_of_lt_of_le : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b ≤ c → a < c
@max_eq_left : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → max a b = a
@max_eq_right : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → max a b = b
@max_lt : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c < a → max b c < a
@measure_mono : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F} {s t : Set α}, s ⊆ t → μ s ≤ μ t
@measure_union_le : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F} (s t : Set α), μ (s ∪ t) ≤ μ s + μ
@mul_add : ∀ {R : Type u_1} [inst : Mul R] [inst_1 : Add R] [LeftDistribClass R] (a b c : R), a * (b + c) = a * b + a * c
@mul_assoc : ∀ {G : Type u_1} [inst : Semigroup G] (a b c : G), a * b * c = a * (b * c)
@mul_comm : ∀ {G : Type u_1} [inst : CommMagma G] (a b : G), a * b = b * a
@mul_div_mul_right : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {c : G₀} (a b : G₀), c ≠ 0 → a * c / (b * c) = a / b
@mul_inv_cancel₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → a * a⁻¹ = 1
@mul_le_mul_of_nonneg_left : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α], b ≤ c → 0 ≤ a → a * b
@mul_le_mul_of_nonneg_right : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [MulPosMono α], b ≤ c → 0 ≤ a → b * 
@mul_nonneg : ∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
@mul_one : ∀ {M : Type u_1} [inst : MulOneClass M] (a : M), a * 1 = a
@mul_pow : ∀ {M : Type u_1} [inst : CommMonoid M] (a b : M) (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
@norm_add_le : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a b : E), ‖a + b‖ ≤ ‖a‖ + ‖b‖
@norm_inv : ∀ {α : Type u_1} [inst : NormedDivisionRing α] (a : α), ‖a⁻¹‖ = ‖a‖⁻¹
@norm_mul : ∀ {α : Type u_1} [inst : Norm α] [inst_1 : Mul α] [NormMulClass α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
@norm_nonneg : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a : E), 0 ≤ ‖a‖
norm_num : Lean.ParserDescr
@norm_pow : ∀ {α : Type u_1} [inst : SeminormedRing α] [NormOneClass α] [NormMulClass α] (a : α) (n : ℕ), ‖a ^ n‖ = ‖a‖ ^ n
@norm_star : ∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E] (x : E), ‖star x‖ = ‖x‖
@norm_sum_le : ∀ {ι : Type u_1} {E : Type u_2} [inst : SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E), ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖
not_le.mp : ¬?m.3 ≤ ?m.4 → ?m.4 < ?m.3
not_lt.mp : ¬?m.3 < ?m.4 → ?m.4 ≤ ?m.3
@not_or : ∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
@one_div : ∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), 1 / a = a⁻¹
@one_le_div : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α}, 0 < b → (1 ≤ a / b ↔ b ≤ a)
@one_le_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀], 1 ≤ a → ∀ {n : ℕ}, 1 
@one_mul : ∀ {M : Type u_1} [inst : MulOneClass M] (a : M), 1 * a = a
@one_pos : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
@one_pow : ∀ {M : Type u_1} [inst : Monoid M] (n : ℕ), 1 ^ n = 1
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ 
@pow_le_pow_of_le_one : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [PosMulMono M₀], 0 ≤ a → a ≤ 1 → ∀ {m n : ℕ}, m ≤
@pow_lt_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : PartialOrder M₀] {a b : M₀} [PosMulStrictMono M₀] [MulPosMono M₀], a < b → 
@pow_nonneg : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀], 0 ≤ a → ∀ (n : ℕ), 0 ≤
@pow_one : ∀ {M : Type u_1} [inst : Monoid M] (a : M), a ^ 1 = a
@pow_pos : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : PartialOrder M₀] {a : M₀} [PosMulStrictMono M₀] [ZeroLEOneClass M₀], 0 < a → ∀ (n : 
@pow_zero : ∀ {M : Type u_1} [inst : Monoid M] (a : M), a ^ 0 = 1
@sq_abs : ∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α), |a| ^ 2 = a ^ 2
@sq_nonneg : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a : R), 0 ≤ a ^ 2
@sub_add_cancel : ∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + b = a
@sub_eq_add_neg : ∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - b = a + -b
@tendsto_atTop_mono : ∀ {α : Type u_1} {β : Type u_2} [inst : Preorder β] {l : Filter α} {f g : α → β}, (∀ (n : α), f n ≤ g n) → Tendsto f l atTop → T
@tendsto_const_nhds : ∀ {X : Type u_1} [inst : TopologicalSpace X] {α : Type u_2} {x : X} {f : Filter α}, Tendsto (fun x_1 => x) f (nhds x)
fun α f x => Tendsto.comp tendsto_inv_atTop_zero : ∀ (α : Type u_1) (f : α → ?m.13) (x : Filter α), Tendsto f x atTop → Tendsto ((fun r => r⁻¹) ∘ f) x
@tendsto_natCast_atTop_atTop : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [Archimedean R], Tendsto Nat.cast atTo
tendsto_natCast_atTop_iff.mp : Tendsto (fun n => ↑(?m.7 n)) ?m.8 atTop → Tendsto ?m.7 ?m.8 atTop
tendsto_natCast_atTop_iff.mpr : Tendsto ?m.7 ?m.8 atTop → Tendsto (fun n => ↑(?m.7 n)) ?m.8 atTop
@tendsto_of_tendsto_of_tendsto_of_le_of_le : ∀ {α : Type u_1} {β : Type u_2} [ts : TopologicalSpace α] [inst : Preorder α] [OrderTopology α] {f g h : 
@tendsto_pow_atTop : ∀ {α : Type u_1} [inst : Semiring α] [inst_1 : PartialOrder α] [IsOrderedRing α] {n : ℕ}, n ≠ 0 → Tendsto (fun x => x ^ n) atTop 
@tendsto_rpow_atTop : ∀ {y : ℝ}, 0 < y → Tendsto (fun x => x ^ y) atTop atTop
@zero_mul : ∀ {M₀ : Type u_1} [self : MulZeroClass M₀] (a : M₀), 0 * a = 0
```

Not elaborated (RBM3D, local): abs_lemE_le eventually_two_mul_rpow_le exact_mod_cast field_simp filter_upwards lemT_lt_one lemT_pos lemma28_quant mE_im mE_im_pos norm_mE push_cast ring_nf seqHflow_isHermitian set_option split_ifs sz.W_pos sz.three_le_L sz0.W_pos sz0.three_le_L sz0_admissible sz0_bandwidth sz0_tendsto

## P.10 Scripts (verbatim; run from one directory in this order: `st1_list.py`, `st1_meta.py`, `st1_decls.py`, `names.py`, `mkportmap.py OUT`; `inv.py`, `closure1.py`, `tokens.py`, `split_def.py`, `splitcalc.py`, `extract.py` are libraries; `clash.py`, `cite_check.py`, `mkbind.py`, `names.py`, `samebody.py`, `vocabdiff.py`, `usedby.py`, `pinuses.py` are the checks of the prove report; `bind2_extra.lean` is printed in P.8.4)

### P.10 `inv.py`

```python
#!/usr/bin/env python3
"""Public declarations of Lean files at a git ref (adapted from the T2002 portmap script J.inv.py).
usage: inv.py REPO REF FILE [FILE...] [--sig N] [--all]
Prints per file: FILE<TAB>LINES<TAB>NDEF<TAB>NTHM and `  L<line> <kind> <fullname> <signature>` per public decl."""
import subprocess, sys, re
KINDS = ('def', 'abbrev', 'structure', 'class', 'inductive', 'instance', 'opaque', 'irreducible_def')
THM = ('theorem', 'lemma')
MODS = ('noncomputable', 'protected', 'private', 'partial', 'unsafe', 'nonrec')
def show(repo, ref, path):
    return subprocess.run(['git', '-C', repo, '--no-optional-locks', 'show', f'{ref}:{path}'],
                          capture_output=True, text=True, check=True).stdout
def strip_comments(text):
    out = []; i = 0; depth = 0; n = len(text)
    while i < n:
        if text.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth > 0:
            if text[i] == '\n': out.append('\n')
            i += 1; continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: break
            i = j; continue
        out.append(text[i]); i += 1
    return ''.join(out)
def parse(text, sig_n):
    lines = strip_comments(text).split('\n')
    stack = []; decls = []; i = 0
    while i < len(lines):
        ln = lines[i]; s = ln.strip()
        m = re.match(r'^namespace\s+(\S+)', s)
        if m: stack.append(('ns', m.group(1))); i += 1; continue
        m = re.match(r'^section\b\s*(\S*)', s)
        if m and not s.startswith('section_'): stack.append(('sec', m.group(1))); i += 1; continue
        m = re.match(r'^end\b\s*(\S*)', s)
        if m and (s == 'end' or re.match(r'^end(\s+\S+)?$', s)):
            if stack: stack.pop()
            i += 1; continue
        t = re.sub(r'^(@\[[^\]]*\]\s*)+', '', s)
        toks = t.split(); mods = []
        while toks and toks[0] in MODS: mods.append(toks.pop(0))
        if toks and (toks[0] in KINDS or toks[0] in THM):
            kind = toks[0]; rest = ' '.join(toks[1:]); buf = rest; j = i
            def done(b):
                d = 0
                for k, ch in enumerate(b):
                    if ch in '([{⟨': d += 1
                    elif ch in ')]}⟩': d -= 1
                    elif d == 0 and b.startswith(':=', k): return k
                    elif d == 0 and b.startswith(' where', k): return k
                    elif d == 0 and b.startswith(' with', k) and kind == 'instance': return k
                return -1
            while done(buf) < 0 and j + 1 < len(lines) and j - i < 40:
                j += 1; buf += ' ' + lines[j].strip()
            k = done(buf); sigtxt = buf[:k] if k >= 0 else buf
            sigtxt = re.sub(r'\s+', ' ', sigtxt).strip()
            if kind == 'instance':
                nm = sigtxt.split(' ')[0] if sigtxt and not sigtxt.startswith(':') else '<anon>'; sg = sigtxt
            else:
                mm = re.match(r'^([^\s:({\[⟨]+)\s*(.*)$', sigtxt)
                nm = mm.group(1) if mm else '<?>'; sg = mm.group(2) if mm else sigtxt
            nss = [x[1] for x in stack if x[0] == 'ns']
            full = nm if nm.startswith('_root_.') else '.'.join(nss + [nm])
            full = full.replace('_root_.', '')
            decls.append((i + 1, kind, full, 'private' in mods, sg[:sig_n]))
            i = j + 1; continue
        i += 1
    return decls
if __name__ == '__main__':
    args = sys.argv[1:]; sig_n = 100; show_all = False
    if '--sig' in args:
        k = args.index('--sig'); sig_n = int(args[k + 1]); del args[k:k + 2]
    if '--all' in args: args.remove('--all'); show_all = True
    repo, ref, files = args[0], args[1], args[2:]
    for f in files:
        text = show(repo, ref, f)
        nl = len(text.split('\n')) - (1 if text.endswith('\n') else 0)
        ds = parse(text, sig_n)
        pub = [d for d in ds if d[1] in KINDS and not d[3]]
        pthm = [d for d in ds if d[1] in THM and not d[3]]
        print(f'{f}\t{nl}\t{len(pub)}\t{len(pthm)}')
        for (ln, kind, full, priv, sg) in sorted(pub + (pthm if show_all else [])):
            print(f'  L{ln} {kind} {full} {sg}')
```

### P.10 `st1_list.py`

```python
#!/usr/bin/env python3
"""ST-1 file list of RBM2D (c9a24cf): portmap part C rows of T2002 (read from the main worktree) filtered by the T2002 sub-gate predicate.
Output TSV: path, lines(c9a24cf), kept(0c1330a), class, labels"""
import re, subprocess, sys
PORTMAP = '/Users/junyin/Lean_proof/RBM3D/docs/reports/T2002-portmap.md'
rows = {}
sec = False
dirname = None
for l in open(PORTMAP, encoding='utf-8'):
    if l.startswith('## C. One row per RBM2D file'): sec = True; continue
    if sec and l.startswith('## D.'): break
    if not sec: continue
    m = re.match(r'^### (\w+) ->', l)
    if m: dirname = m.group(1); continue
    if not l.startswith('| ') or l.startswith('| RBM2D file') or l.startswith('|---'): continue
    cells = [c.strip() for c in l.strip().strip('|').split(' | ')]
    if len(cells) < 7: continue
    f, lines, kept, cl, tgt, basis, labs = cells[:7]
    rows['RBM2D/%s/%s' % (dirname, f)] = (int(lines), int(kept), cl, tgt, basis, labs)
def _p(*alts): return re.compile('^RBM2D/(' + '|'.join(alts) + ')\\.lean$')
MD = _p('Defs/(Model|StochDom)', 'Gauss/(Model|Domination|MomentBridge|LinearForm|Envelope|SteinMatrix)',
        'Path/(PerTime|Walk|Transfer|Markov|Stop|Azuma|Step2Props)', 'Hierarchy/(Loops|Operations|OperationsPairWord)')
ST1 = _p('Gauss/.*', 'Green/.*', 'Hierarchy/.*', 'Induction/(Continuity|ConArg|ConArgDet|Step1)')
sel = []
for p, (n, k, cl, tgt, basis, labs) in sorted(rows.items()):
    if cl == 'd': continue
    if MD.match(p): continue
    if ST1.match(p): sel.append((p, n, k, cl, labs))
if __name__ == '__main__':
    print('files', len(sel), 'lines', sum(x[1] for x in sel), 'kept', sum(max(x[2], 0) for x in sel), file=sys.stderr)
    from collections import Counter
    print('classes', dict(Counter(x[3] for x in sel)), file=sys.stderr)
    for p, n, k, cl, labs in sel: print('\t'.join([p, str(n), str(k), cl, labs]))
```

### P.10 `st1_meta.py`

```python
#!/usr/bin/env python3
"""Per-file facts of the 86 ST-1 files: lines at c9a24cf and kept at 0c1330a (recomputed from git, compared with the portmap),
title (first `# ` line of the module docstring), RBM2D imports, exponent tokens by kind."""
import re, subprocess, sys, json
sys.path.insert(0, '.')
from st1_list import sel
R = '/Users/junyin/Lean_proof/RBM2D'
def git(*a):
    return subprocess.run(['git', '-C', R, '--no-optional-locks', *a], capture_output=True, text=True)
def nlines(ref, f):
    r = git('show', f'{ref}:{f}')
    if r.returncode != 0: return -1
    t = r.stdout
    return len(t.split('\n')) - (1 if t.endswith('\n') else 0)
TOK = [('W^2', r'(?<![A-Za-z0-9_])\(?\(?W(?: : ℝ\)| : ℂ\)| : ℕ\))?\)?\s*\^\s*2\b'),
       ('L^2', r'(?<![A-Za-z0-9_])\(?\(?L(?: : ℝ\)| : ℂ\)| : ℕ\))?\)?\s*\^\s*2\b'),
       ('(WL)^2', r'\(\(?W \* L\)\)? \^ 2|\(\(W : ℝ\) \* \(L : ℝ\)\) \^ 2|size\s*\^\s*2'),
       ('W⁻²/L⁻²', r'[WLN]⁻²|W\^\{-2\}|⁻¹ \^ 2'),
       ('d=2', r'\bd = 2\b|\bd=2\b|Z_L\^2|Z_\{WL\}\^2'),
       ('Z2/zdist2', r'\bZ2\b|\bzdist2\b'),
       ('1/5', r'5⁻¹|\(1 / 5\)|\b1/5\b'),
       ('scales', r'\bscaleM\b|\bellT\b|\btailT\b|\bellStar\b|\bMeta\b|\bellz\b')]
out = []
for p, n, k, cl, labs in sel:
    t = git('show', f'c9a24cf:{p}').stdout
    n2 = nlines('c9a24cf', p); k2 = nlines('0c1330a', p)
    assert n2 == n, (p, n2, n)
    assert k2 == k, (p, k2, k)
    m = re.search(r'/-!(.*?)-/', t, re.S)
    head = m.group(1) if m else ''
    title = ''
    for l in head.split('\n'):
        if l.strip().startswith('#'): title = l.strip().lstrip('#').strip(); break
    imps = re.findall(r'^import\s+(RBM2D\.[A-Za-z0-9_.]+)', t, re.M)
    cnt = {name: len(re.findall(pat, t)) for name, pat in TOK}
    out.append(dict(path=p, lines=n, kept=k, cls=cl, title=title, imps=imps, tok=cnt, labels=labs))
json.dump(out, open('st1_meta.json', 'w'), ensure_ascii=False, indent=1)
print('ok', len(out), 'files; lines/kept recomputed from git equal the portmap for all rows')
```

### P.10 `st1_decls.py`

```python
#!/usr/bin/env python3
"""Public declarations (def/abbrev/structure/class/instance + theorem/lemma) of the 86 ST-1 files at c9a24cf, with line numbers; and
the cross-gate consumption scan: which of them are referenced by files of ST-2..ST-6 (+UN) (class != d, C9A24CF text)."""
import re, subprocess, sys, json, collections
sys.path.insert(0, '.')
from inv import parse, KINDS, THM, strip_comments
from st1_list import sel, rows, ST1, MD
import st1_list
R = '/Users/junyin/Lean_proof/RBM2D'
def git(*a):
    return subprocess.run(['git', '-C', R, '--no-optional-locks', *a], capture_output=True, text=True, check=True).stdout
# groups (copy of the T2002 portmap predicate; first match wins)
def _p(*alts): return re.compile('^RBM2D/(' + '|'.join(alts) + ')\\.lean$')
GROUPS = [
 ('none', lambda p, c: c == 'd'),
 ('MD', _p('Defs/(Model|StochDom)', 'Gauss/(Model|Domination|MomentBridge|LinearForm|Envelope|SteinMatrix)',
        'Path/(PerTime|Walk|Transfer|Markov|Stop|Azuma|Step2Props)', 'Hierarchy/(Loops|Operations|OperationsPairWord)')),
 ('ST-1', _p('Gauss/.*', 'Green/.*', 'Hierarchy/.*', 'Induction/(Continuity|ConArg|ConArgDet|Step1)')),
 ('ST-2', _p('Path/.*', 'Induction/(Grid.*|AzumaProxyN|StepDecompN|LoopC2N|LoopGenN|QVN|Step2TargetV3|StoppedEndDefs)')),
 ('ST-3', _p('Induction/(?!(MainInd|Defs))[A-Za-z0-9]*')),
 ('ST-5', _p('Evolution/(Step61|MLExp.*)')),
 ('ST-4', _p('Evolution/.*')),
 ('ST-6', _p('Induction/(MainInd|Defs)', 'Main/(?!BUniv).*')),
 ('UN', _p('Universality/.*', 'Main/BUniv.*')),
]
def group_of(p, cl):
    for name, pred in GROUPS:
        if callable(pred):
            if pred(p, cl): return name
        elif pred.match(p): return name
    return None
allrows = {p: v for p, v in rows.items()}
grp = {p: group_of(p, v[2]) for p, v in allrows.items()}
st1 = [x[0] for x in sel]
assert all(grp[p] == 'ST-1' for p in st1) and sum(1 for p in grp if grp[p] == 'ST-1') == 86
decls = {}
for p in st1:
    t = git('show', f'c9a24cf:{p}')
    ds = parse(t, 240)
    decls[p] = [(ln, kind, full, sg) for (ln, kind, full, priv, sg) in ds if not priv and (kind in KINDS or kind in THM)]
# consumers: files of ST-2..ST-6, UN with class != d
cons = [p for p in allrows if grp[p] in ('ST-2', 'ST-3', 'ST-4', 'ST-5', 'ST-6')]
ctext = {}
for p in cons:
    t = strip_comments(git('show', f'c9a24cf:{p}'))
    ctext[p] = t
def tokens(t):
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", t))
ctok = {p: tokens(t) for p, t in ctext.items()}
# short-name multiplicity over the whole c9a24cf library (public decls of ST-1 files + all consumers' files do not matter: uniqueness over ST-1 decls)
short = collections.Counter()
for p in st1:
    for (ln, kind, full, sg) in decls[p]: short[full.split('.')[-1]] += 1
res = {}
for p in st1:
    lst = []
    for (ln, kind, full, sg) in decls[p]:
        sname = full.split('.')[-1]
        users = []
        for c in cons:
            toks = ctok[c]
            hit = False
            for tk in toks:
                if tk == full or full.endswith('.' + tk) and '.' in tk:
                    hit = True; break
                if '.' not in tk and tk == sname and short[sname] == 1 and len(sname) >= 6:
                    hit = True; break
                if '.' in tk and tk.split('.')[-1] == sname and short[sname] == 1 and len(sname) >= 6:
                    hit = True; break
            if hit: users.append(c)
        lst.append(dict(line=ln, kind=kind, name=full, sig=sg[:160], users=users, ambiguous=short[sname] > 1))
    res[p] = lst
json.dump(dict(decls=res, groups={p: grp[p] for p in cons}), open('st1_decls.json', 'w'), ensure_ascii=False, indent=1)
tot = sum(len(v) for v in res.values()); used = sum(1 for v in res.values() for x in v if x['users'])
print('ST-1 public decls', tot, 'consumed by ST-2..ST-6 files:', used, 'consumer files', len(cons))
```

### P.10 `closure1.py`

```python
#!/usr/bin/env python3
"""Transitive RBM2D import closure (c9a24cf) of given root files, annotated with the T2002 sub-gate group, class, lines, kept."""
import re, subprocess, sys, collections
sys.path.insert(0, '.')
from st1_list import rows
import importlib
R = '/Users/junyin/Lean_proof/RBM2D'
def git(*a):
    return subprocess.run(['git', '-C', R, '--no-optional-locks', *a], capture_output=True, text=True, check=True).stdout
files = [x for x in git('ls-tree', '-r', '--name-only', 'c9a24cf', '--', 'RBM2D').split('\n') if x.endswith('.lean')]
mod = lambda f: f[:-5].replace('/', '.')
file_of = {mod(f): f for f in files}
files_kept = set(x for x in git('ls-tree', '-r', '--name-only', '0c1330a', '--', 'RBM2D').split('\n') if x.endswith('.lean'))
imps = {}      # imports at 0c1330a (the kept text) for the files that survive, at c9a24cf otherwise; deleted files are dropped from the graph
imps_c9 = {}
for f in files:
    t9 = git('show', f'c9a24cf:{f}')
    imps_c9[f] = [file_of[m] for m in re.findall(r'^import\s+(RBM2D\.[A-Za-z0-9_.]+)', t9, re.M) if m in file_of]
    if f in files_kept:
        tk = git('show', f'0c1330a:{f}')
        imps[f] = [file_of[m] for m in re.findall(r'^import\s+(RBM2D\.[A-Za-z0-9_.]+)', tk, re.M) if m in file_of and file_of[m] in files_kept]
    else:
        imps[f] = []
def _p(*alts): return re.compile('^RBM2D/(' + '|'.join(alts) + ')\\.lean$')
GROUPS = [
 ('none', lambda p, c: c == 'd'),
 ('MD', _p('Defs/(Model|StochDom)', 'Gauss/(Model|Domination|MomentBridge|LinearForm|Envelope|SteinMatrix)',
        'Path/(PerTime|Walk|Transfer|Markov|Stop|Azuma|Step2Props)', 'Hierarchy/(Loops|Operations|OperationsPairWord)')),
 ('ST-1', _p('Gauss/.*', 'Green/.*', 'Hierarchy/.*', 'Induction/(Continuity|ConArg|ConArgDet|Step1)')),
 ('ST-2', _p('Path/.*', 'Induction/(Grid.*|AzumaProxyN|StepDecompN|LoopC2N|LoopGenN|QVN|Step2TargetV3|StoppedEndDefs)')),
 ('ST-3', _p('Induction/(?!(MainInd|Defs))[A-Za-z0-9]*')),
 ('ST-5', _p('Evolution/(Step61|MLExp.*)')),
 ('ST-4', _p('Evolution/.*')),
 ('ST-6', _p('Induction/(MainInd|Defs)', 'Main/(?!BUniv).*')),
 ('UN', _p('Universality/.*', 'Main/BUniv.*')),
]
def group_of(p):
    cl = rows[p][2] if p in rows else '?'
    for name, pred in GROUPS:
        if callable(pred):
            if pred(p, cl): return name
        elif pred.match(p): return name
    return 'other'
def closure(roots):
    seen = collections.OrderedDict(); q = collections.deque(roots)
    while q:
        f = q.popleft()
        if f in seen: continue
        seen[f] = 1
        for g in imps.get(f, []): q.append(g)
    return list(seen)
if __name__ == '__main__':
    roots = sys.argv[1:]
    cl = closure(['RBM2D/' + r + '.lean' for r in roots])
    by = collections.defaultdict(list)
    for f in cl:
        by[group_of(f)].append(f)
    for g in ['ST-1', 'MD', 'ST-2', 'ST-3', 'ST-4', 'ST-5', 'ST-6', 'UN', 'none', 'other']:
        if g in by:
            kept = sum(max(rows[p][1], 0) for p in by[g] if p in rows)
            print(f'{g}: {len(by[g])} files, kept {kept}')
            if g not in ('ST-1',):
                for p in by[g]: print('   ', p.replace('RBM2D/', ''), rows[p][0] if p in rows else '', rows[p][1] if p in rows else '', rows[p][2] if p in rows else '')
```

### P.10 `tokens.py`

```python
#!/usr/bin/env python3
"""d = 2 exponent tokens with file:line at c9a24cf in the Step 1 chain files (read-only git show).
Token kinds: W2 (W ^ 2), L2 (L ^ 2), N2 ((W * L) ^ 2, size ^ 2), inv2 (W⁻², L⁻², N⁻²), d2 (d = 2), e30 (exponent 30 or 29/30 of con_st_ind)."""
import re, subprocess, sys
R = '/Users/junyin/Lean_proof/RBM2D'
def git(*a): return subprocess.run(['git', '-C', R, '--no-optional-locks', *a], capture_output=True, text=True, check=True).stdout
KINDS = [('W2', re.compile(r'(?<![A-Za-z0-9_])\(?\(?W(?: : ℝ\)| : ℂ\)| : ℕ\))?\)?\s*\^\s*2\b')),
         ('L2', re.compile(r'(?<![A-Za-z0-9_])\(?\(?L(?: : ℝ\)| : ℂ\)| : ℕ\))?\)?\s*\^\s*2\b')),
         ('N2', re.compile(r'\(W \* L\) \^ 2|\(\(W \* L\) \^ 2|size\s*\^\s*2')),
         ('inv2', re.compile(r'[WLN]⁻²|W⁻¹\)? \^ 2|\(W : ℝ\)⁻¹ \^ 2')),
         ('d2', re.compile(r'\bd = 2\b')),
         ('e30', re.compile(r'\)\s*\^\s*30\b|\(29 : ℝ\) / 30|\^ 30\b'))]
FILES = ['Induction/Step1', 'Induction/ConArg', 'Induction/ConArgDet', 'Induction/Continuity', 'Induction/ScaleFacts', 'Induction/Split',
         'Path/Scales', 'Path/Step2Props', 'Green/Pins', 'Green/GbEXP', 'Gauss/LoopEnvelope']
def scan(files=FILES):
    out = []
    for f in files:
        t = git('show', f'c9a24cf:RBM2D/{f}.lean').split('\n')
        in_comment = 0
        for i, l in enumerate(t, 1):
            s = l.strip()
            # skip comment text: block comments (nested /- ... -/) and line comments
            if in_comment > 0 or s.startswith('/-'):
                in_comment += s.count('/-') - s.count('-/')
                continue
            if s.startswith('--'): continue
            ks = [k for k, p in KINDS if p.search(l)]
            if ks: out.append((f, i, ks, s))
    return out
if __name__ == '__main__':
    import collections
    res = scan()
    cnt = collections.Counter()
    for f, i, ks, s in res:
        cnt[f] += 1
    print(dict(cnt))
    for f, i, ks, s in res[:20]: print(f, i, ks, s[:100])
```

### P.10 `split_def.py`

```python
#!/usr/bin/env python3
"""The proposed split of ST-1 (T2015, item 7), in dependency order; ids S1-01.. are assigned by position.
Fields: title, rbm3d (target files under RBM3D/), rbm2d (ST-1 files of the T2002 portmap, `shares` when a file is cut between two tickets),
extra (RBM2D files of other T2002 sub-gates that Step 1 / Green import: re-assigned here), role, new (lines with no RBM2D source), discount, note."""
G = 'RBM2D/Gauss/'; H = 'RBM2D/Hierarchy/'; N = 'RBM2D/Green/'; I = 'RBM2D/Induction/'
def f(prefix, *names): return [prefix + n + '.lean' for n in names]
FLUC1, FLUC2 = 950 / 1877, 927 / 1877         # FlucIter cut at the heading "### The stratified weight sum" (c9a24cf:951)
CONT1, CONT2 = 764 / 1644, 880 / 1644         # Continuity cut at "## 4. Deterministic estimates along the flow" (c9a24cf:765)
STEP1, STEP2 = 966 / 1515, 549 / 1515         # Step1 cut at "## 6. The weak-law step at one time sequence" (c9a24cf:967)
_T = [
 dict(title='Flow calculus: spectral path, time and sample continuity, derivatives of the flow resolvent and loops',
      rbm3d=['Gauss/FlowCalculus'], rbm2d=f(G, 'SpectralWindow', 'SpectralAlgebra', 'SpectralDerivative', 'FlowTimeCont', 'GreenTimeCont',
      'LoopTimeCont', 'LoopSampleCont', 'GreenDerivative', 'LoopDerivative', 'LoopEnvelope'), role='prover', discount=222,
      note='merged mE/zt/lemE (Defs/Semicircle) and the GLoopFlow envelopes cover SpectralWindow (50), SpectralAlgebra (53), LoopEnvelope (119): estimate lowered by their 222 kept lines'),
 dict(title='Coordinate derivatives of loops: first, second, bounds, integrability',
      rbm3d=['Gauss/LoopCoordinate'], rbm2d=f(G, 'LoopCoordinateDerivative', 'LoopCoordinateSecondDerivative', 'GreenCoordinateSecondDerivative',
      'LoopCoordinateDerivativeBounds', 'LoopCoordinateIntegrability'), role='prover'),
 dict(title='Loop contraction I: elementary identities, coordinate directions, sums, unused coordinates, cut words, drift',
      rbm3d=['Hierarchy/ContractionBasic'], rbm2d=f(H, 'ContractionBasic', 'ContractionDirections', 'ContractionSum', 'ContractionUnused',
      'ContractionCutWords', 'ContractionDrift'), role='prover'),
 dict(title='Loop contraction II: second-derivative cuts, same-edge and pair splits, position sums and bridges',
      rbm3d=['Hierarchy/ContractionSecondLoop'], rbm2d=f(H, 'ContractionSecondLoop', 'ContractionSecondLoopSameEdge', 'ContractionSecondLoopSameEdgeWord',
      'ContractionSecondLoopSameEdgeCut', 'ContractionEdgeSplits', 'ContractionPairSplits', 'ContractionFirstDerivativePositionSum',
      'ContractionSecondDerivativePositionSum', 'ContractionSecondDerivativeTraceSum', 'ContractionPositionLoopBridge',
      'ContractionSameEdgePositionCut', 'ContractionPairPositionCut', 'ContractionSecondLoopAllCuts'), role='prover'),
 dict(title='Expected samplewise loop-flow derivative (Stein for loops)',
      rbm3d=['Gauss/LoopFlowStein'], rbm2d=f(G, 'LoopFlowCoordinateChain', 'LoopFlowDerivativeEnvelope', 'LoopFlowSteinExpectation',
      'LoopExpectationDerivative'), role='prover-hard'),
 dict(title='Loop generator (cut expressions), spectral drift cuts, initial values of loops',
      rbm3d=['Gauss/LoopGenerator'], rbm2d=f(G, 'LoopSpectralDriftCuts', 'LoopGeneratorSamplewise', 'LoopGeneratorExpectation', 'LoopInitialValue',
      'LoopInitialValueSupport', 'LoopInitialValueScalar', 'LoopInitialValueProjectionWords') +
      f(H, 'LoopHierarchyCutBlockSumBound', 'LoopHierarchyCutContinuity'), role='prover'),
 dict(title='Pins and vocabulary at d >= 3 (probe sections 1-3: STLK ... STStep1, STGbEXP, STConArg) and the lem_GbEXP shapes',
      key=[('Green/Pins','GbEXPHypV3'),('Green/Pins','GbEXPV3Theorem'),('Green/Pins','GijGEXPTSwap'),('Green/Pins','GiiGEXPT'),('Green/Pins','AsGMcPT'),('Green/Pins','gijGEXPTSwap_giiGEXPT_of_V3')], rbm3d=['Induction/Defs', 'Green/Pins', 'Test/Axioms'], rbm2d=f(N, 'Pins'), extra=[I + 'Defs.lean'], role='prover-max', new=450,
      note='Induction/Defs (ST-6 by T2002) is replaced by the probe vocabulary; Test/Axioms registers the pins (DECISIONS section 16)'),
 dict(title='Scale facts at d >= 3 (class c) and the per-time domination calculus (forbidden region, Step 1 bootstrap)',
      key=[('Induction/ScaleFacts','scaleFacts_R1'),('Induction/ScaleFacts','scaleFacts_R2_pt'),('Induction/ScaleFacts','scaleFacts_ellT_ratio'),('Induction/ScaleFacts','scaleFacts_ellT_pow_four'),('Induction/PerTimeCalc','forbidden_region'),('Induction/PerTimeCalc','stepOneBootstrap')], rbm3d=['Induction/ScaleFacts', 'Induction/PerTimeCalc'], rbm2d=[], extra=[I + 'ScaleFacts.lean', I + 'PerTimeCalc.lean'],
      role='prover-hard', new=200, note='ScaleFacts, PerTimeCalc are ST-3 files by T2002; Step 1 and Green import them; new = probe 4.1 (closure, monotonicity)'),
 dict(title='Deterministic loop splitting: (6.4), trace of E_a against a matrix, envelope at early times',
      key=[('Induction/Split','loopMax_odd_sq_le'),('Induction/Split','split_norm_trace_mul_Eblk_le'),('Induction/Split','norm_gloop_le_of_le_abs_im'),('Induction/Split','norm_gloop_symIdx_split_le')], rbm3d=['Induction/Split'], rbm2d=[], extra=[I + 'Split.lean'], role='prover-hard',
      note='Split is an ST-3 file by T2002; ConArgDet and Green/FlucAvg import it'),
 dict(title='Minor formulas and the dimension-free entry core ([39, Lemma 3.3] input)',
      rbm3d=['Green/EntryCore'], rbm2d=f(N, 'Minor', 'EntryCore'), role='prover'),
 dict(title='Row independence of the minor resolvent; the row LDE',
      rbm3d=['Green/RowIndep'], rbm2d=f(N, 'RowIndep'), role='prover-hard'),
 dict(title='Hanson-Wright layer I: polynomial weights, tame functions, the row chaos',
      rbm3d=['Green/LDEQuad'], rbm2d=f(N, 'LDEQuad'), role='prover'),
 dict(title='Hanson-Wright layer II: master identity, moment recursion, moment bound',
      rbm3d=['Green/LDEQuadMom'], rbm2d=f(N, 'LDEQuadMom'), role='prover'),
 dict(title='Positive chaos moment bound E[T^p] <= C_p E[V_q^p]',
      rbm3d=['Green/LDEQuadT'], rbm2d=f(N, 'LDEQuadT'), role='prover'),
 dict(title='Stability of 1 - t m^2 S at d >= 3 (class c: re-written on the d >= 3 lattice sums)',
      rbm3d=['Green/Stability'], rbm2d=f(N, 'Stability'), role='prover-max',
      note='Kstab2 = O(1 + log L) is a d = 2 lattice sum; the d >= 3 constants come from the merged Kernel/SumDecay and the PT pins (hypotheses)'),
 dict(title='Entry estimates: the block model and the dominated layer',
      rbm3d=['Green/EntryDom'], rbm2d=f(N, 'EntryBlock', 'EntryDom'), role='prover-hard'),
 dict(title='Row conditional expectations, resolvent differentiable in the coordinates, fluctuation vanishing',
      rbm3d=['Green/FlucVanish'], rbm2d=f(N, 'CondRow', 'GreenDeriv', 'FlucVanish'), role='prover-hard'),
 dict(title='Fluctuation averaging layer; large deviation inputs for the Gaussian flow',
      rbm3d=['Green/LDE'], rbm2d=f(N, 'FlucAvg', 'LDE'), role='prover-hard'),
 dict(title='Gaussian integration by parts: polynomial discharge; the row chaos of the model',
      rbm3d=['Green/IBPPoly'], rbm2d=f(N, 'IBPPoly', 'LDEQuadInst'), role='prover'),
 dict(title='Iterating the vanishing lemma to order 2p, part 1 (splits, words, pivot, admissible words, counting)',
      rbm3d=['Green/FlucIter'], rbm2d=f(N, 'FlucIter'), shares={N + 'FlucIter.lean': FLUC1}, role='prover-hard'),
 dict(title='Iterating the vanishing lemma to order 2p, part 2 (stratified weights, moment bound, graded iteration, gain interface)',
      rbm3d=['Green/FlucIterGain'], rbm2d=f(N, 'FlucIter'), shares={N + 'FlucIter.lean': FLUC2}, role='prover-hard'),
 dict(title='Higher-order minor expansion; level-budgeted minor good event',
      rbm3d=['Green/MinorGoodLe'], rbm2d=f(N, 'FlucIterHigh', 'MinorGoodLe'), role='prover-hard'),
 dict(title='The Gaussian integration-by-parts display as an identity',
      rbm3d=['Green/IBP'], rbm2d=f(N, 'IBP'), role='prover-hard'),
 dict(title='Conditional dominance and stability under E_k; (GijGEX), (GiiGEX) for the Gaussian flow',
      rbm3d=['Green/CondDom'], rbm2d=f(N, 'CondDom', 'CondStable', 'EntryGauss'), role='prover-hard'),
 dict(title='Iterated minor differences: the Delta_kappa calculus',
      rbm3d=['Green/MinorDiff'], rbm2d=f(N, 'MinorDiff'), role='prover-hard'),
 dict(title='Minor-difference gain on the good event (the tower of exceptional sets)',
      rbm3d=['Green/MinorDiffCond'], rbm2d=f(N, 'MinorDiffCond'), role='prover-hard'),
 dict(title='Averaging pins and the local law at a deterministic control',
      key=[('Green/AvgPins','LocalLawDetSeq'),('Green/AvgPins','FixedTimeFASeq'),('Green/AvgPins','IBPDetSeq'),('Green/AvgPins','LocalLawDetThm')], rbm3d=['Green/LocalLaw'], rbm2d=f(N, 'AvgPins', 'LocalLaw'), role='prover-hard',
      note='Green/LocalLaw imports Path/Step2Local only for two private helper lemmas: copy them, do not import ST-2'),
 dict(title='Bad-event tower (4.5) and the movable threshold for fluctuation averaging',
      rbm3d=['Green/FlucThreshold'], rbm2d=f(N, 'Eq45Small', 'FlucThreshold'), role='prover-hard'),
 dict(title='The per-time integration-by-parts remainder',
      rbm3d=['Green/IBPRem'], rbm2d=f(N, 'IBPRem'), role='prover-hard'),
 dict(title='Endpoint: fixed-time fluctuation averaging, IBP at a deterministic scale, lem_GbEXP (STGbEXP)',
      key=[('Green/FlucAvgDet','fixedTimeFAThm'),('Green/IBPDet','ibpDetThm'),('Green/GbEXP','gbEXPV3')], rbm3d=['Green/GbEXP'], rbm2d=f(N, 'FlucAvgDet', 'IBPDet', 'GbEXP'), role='prover-max'),
 dict(title='lem_ConArg, deterministic part: resolvent identity along the flow, (6.3)-(6.12); Ward identity for loops',
      key=[('Hierarchy/WardResolvent','green_sub_green'),('Hierarchy/WardResolvent','sum_gloop_ward_last_div'),('Induction/ConArgDet','ztTilde_arith'),('Induction/ConArgDet','loopMax_two_mul_le_tilde'),('Induction/ConArgDet','trace_gram_rpow_le')], rbm3d=['Induction/ConArgDet'], rbm2d=f(H, 'WardResolvent') + f(I, 'ConArgDet'), role='prover-hard'),
 dict(title='lem_ConArg, probabilistic part (STConArg)',
      key=[('Induction/ConArg','ConArgPin'),('Induction/ConArg','conArg')], rbm3d=['Induction/ConArg'], rbm2d=f(I, 'ConArg'), role='prover-hard'),
 dict(title='Continuity of G in time, part 1: abstract net lift, good event, operator-norm and scalar estimates',
      key=[('Induction/Continuity','GopboundPin')], rbm3d=['Induction/ContinuityNet'], rbm2d=f(I, 'Continuity'), shares={I + 'Continuity.lean': CONT1}, role='prover-hard'),
 dict(title='Continuity of G in time, part 2: estimates along the flow, closeness, Gopboundu, net lift (STNetLift)',
      key=[('Induction/Continuity','gopbound'),('Induction/Continuity','Step1NetLift'),('Induction/Continuity','step1NetLift')], rbm3d=['Induction/Continuity'], rbm2d=f(I, 'Continuity'), shares={I + 'Continuity.lean': CONT2}, role='prover-hard'),
 dict(title='Step 1, part A: standing hypotheses, scale facts along the window, loop family at max(s,1/2), matrix bridges',
      key=[('Induction/Step1','Step1TargetV3')], rbm3d=['Induction/Step1Setup'], rbm2d=f(I, 'Step1'), shares={I + 'Step1.lean': STEP1}, role='prover-hard'),
 dict(title='Step 1, part B: weak law at one time, net and forbidden region, continuity argument, STStep1 (probe 4.2-4.4)',
      key=[('Induction/Step1','step1')], rbm3d=['Induction/Step1'], rbm2d=f(I, 'Step1'), shares={I + 'Step1.lean': STEP2}, role='prover-max', new=250),
]
TICKETS = []
for i, t in enumerate(_T, 1):
    t = dict(t); t['id'] = 'S1-%02d' % i
    TICKETS.append(t)
```

### P.10 `splitcalc.py`

```python
#!/usr/bin/env python3
"""Sizes, dependencies and checks of the ST-1 split (T2015 item 7).  Reads split_def.py, the T2002 portmap rows, RBM2D imports at c9a24cf."""
import re, sys, collections, subprocess
sys.path.insert(0, '.')
from split_def import TICKETS
import closure1 as c
from st1_list import rows
FACTOR = {'a': 1.0, 'b': 1.1, 'c': 1.5}
MD_MAP = {  # T2002 portmap E.2: MD tickets and their RBM2D sources
 'MD-1': ['Defs/Model', 'Gauss/Model', 'Gauss/LinearForm'],
 'MD-2': ['Defs/StochDom', 'Path/PerTime', 'Gauss/Domination', 'Gauss/MomentBridge', 'Gauss/Envelope', 'Gauss/SteinMatrix'],
 'MD-3': ['Hierarchy/Loops', 'Hierarchy/Operations', 'Hierarchy/OperationsPairWord', 'Path/Step2Props'],
 'MD-4': ['Path/Walk', 'Path/Transfer'],
 'MD-5': ['Path/Markov', 'Path/Stop', 'Path/Azuma']}
MD_OF = {'RBM2D/' + p + '.lean': k for k, v in MD_MAP.items() for p in v}
MERGED = {'MD-1': 'merged (T2006, 0a873f1)', 'MD-2': 'merged (T2012, 9e2b00f)', 'MD-3': 'merged (T2013, 868b3b4)',
          'MD-4': 'merged (T2018, ddf5f74)', 'MD-5': 'merged (T2021, 58bedae)'}
file_ticket = {}      # file -> list of (ticket id, share)
for t in TICKETS:
    for p in t['rbm2d'] + t.get('extra', []):
        file_ticket.setdefault(p, []).append((t['id'], t.get('shares', {}).get(p, 1.0)))
def sizes(t):
    lines = kept = est = 0.0
    cls = collections.Counter()
    for p in t['rbm2d']:
        n, k, cl = rows[p][0], rows[p][1], rows[p][2]
        sh = t.get('shares', {}).get(p, 1.0)
        lines += n * sh; kept += max(k, 0) * sh; est += max(k, 0) * sh * FACTOR[cl]; cls[cl] += 1
    for p in t.get('extra', []):
        n, k, cl = rows[p][0], rows[p][1], rows[p][2]
        if p.endswith('Induction/Defs.lean'):    # replaced by the probe vocabulary
            lines += n; kept += k; cls[cl] += 1
            continue
        lines += n; kept += max(k, 0); est += max(k, 0) * FACTOR[cl]; cls[cl] += 1
    est += t.get('new', 0) + 60 - t.get('discount', 0)
    return round(lines), round(kept), round(est), cls
def deps(t):
    mine = set(t['rbm2d'] + t.get('extra', []))
    st1_deps = collections.OrderedDict(); md = collections.OrderedDict(); cross = collections.OrderedDict(); other = set(); none_ = set()
    seen = set(); q = collections.deque()
    for p in mine:
        if p.endswith('Induction/Defs.lean'): continue      # replaced by the probe vocabulary: its imports are not followed
        for g in c.imps.get(p, []):
            q.append((g, True))      # direct imports
    while q:
        g, direct = q.popleft()
        if g in seen and not direct: continue
        if g in mine: continue
        owners = file_ticket.get(g)
        if owners:
            for (tid, sh) in owners:
                if tid != t['id']: st1_deps[tid] = 1
            continue                       # stop at other tickets' files
        if (g, False) in seen: continue
        seen.add(g)
        grp = c.group_of(g)
        if g in MD_OF: md[MD_OF[g]] = 1
        elif grp == 'none':
            none_.add(g); continue                 # class d (merged, unreachable, deleted): no expansion
        elif grp in ('ST-2', 'ST-3', 'ST-6'):
            if direct: cross[g] = grp
            continue                               # cut or replaced in RBM3D: not followed
        elif grp == 'ST-1':
            pass
        else:
            other.add(g); continue                 # Loop/*, Propagator/*, root files: recorded, not expanded
        for h in c.imps.get(g, []): q.append((h, False))
    # a split part depends on the earlier part of the same file
    for p in t['rbm2d']:
        if len(file_ticket.get(p, [])) > 1:
            ids = [i for (i, s) in file_ticket[p]]
            k = ids.index(t['id'])
            for j in range(k): st1_deps[ids[j]] = 1
    return list(st1_deps), sorted(md), cross, other, none_
if __name__ == '__main__':
    order = [t['id'] for t in TICKETS]
    tot_l = tot_k = tot_e = 0
    for t in TICKETS:
        l, k, e, cls = sizes(t)
        s1, md, cross, other, none_ = deps(t)
        tot_l += l; tot_k += k; tot_e += e
        # topological sanity: dependencies must come earlier in the list
        bad = [d for d in s1 if order.index(d) > order.index(t['id'])]
        print(f"{t['id']} lines={l} kept={k} est={e} cls={dict(cls)} role={t['role']} deps={s1} md={md} cross={[ (p.replace('RBM2D/',''),g) for p,g in cross.items()]} {'BAD-ORDER'+str(bad) if bad else ''}")
    print('TOTAL lines', tot_l, 'kept', tot_k, 'est', tot_e, 'tickets', len(TICKETS))
```

### P.10 `extract.py`

```python
#!/usr/bin/env python3
"""Extract declarations from the probe by name (no docstrings): `extract.py FILE NAME... [--head]`
--head prints only the statement up to `:=` (instances: the proof is not printed)."""
import re, sys
args = sys.argv[1:]
head = '--head' in args
if head: args.remove('--head')
nomark = '--nomarkers' in args
if nomark: args.remove('--nomarkers')
path, names = args[0], args[1:]
lines = open(path, encoding='utf-8').read().split('\n')
def find(name):
    pat = re.compile(r'^(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|def|lemma|abbrev)\s+' + re.escape(name) + r'(?![\w\'.])')
    for i, l in enumerate(lines):
        if pat.match(l): return i
    raise SystemExit('not found: ' + name)
def head_end(i):
    """index (line, col) of the `:=` that ends the statement starting at line i: first `:=` at bracket depth 0."""
    depth = 0
    for j in range(i, min(i + 60, len(lines))):
        l = lines[j]
        k = 0
        while k < len(l):
            ch = l[k]
            if ch in '([{⟨': depth += 1
            elif ch in ')]}⟩': depth -= 1
            elif depth == 0 and l.startswith(':=', k): return j, k
            k += 1
    raise SystemExit('no := found')
for nm in names:
    i = find(nm)
    out = []
    if head:
        j, k = head_end(i)
        out = lines[i:j] + [lines[j][:k].rstrip()]
    else:
        j = i
        while True:
            out.append(lines[j])
            j += 1
            if j >= len(lines) or lines[j].strip() == '': break
            if lines[j].startswith(('theorem ', 'def ', '/-', 'end ', 'namespace ', 'private ', 'lemma ')): break
    if not nomark: print('-- probe line %d' % (i + 1))
    print('\n'.join(out))
```

### P.10 `clash.py`

```python
#!/usr/bin/env python3
"""Name-clash check of the probe's public declarations, by full (namespace-qualified) name:
(1) parse every .lean file of RBM3D/ (main worktree = merged library, and the branch worktree without the probe) with the declaration parser of inv.py,
(2) intersect the full names with those of the probe; (3) report also the short-name coincidences (same last component, different namespace)."""
import sys, glob, os
sys.path.insert(0, '.')
from inv import parse, KINDS, THM
PROBE = '/Users/junyin/Lean_proof/RBM3D-wt/T2015/RBM3D/Probe/T2015Pins.lean'
def decls(path):
    t = open(path, encoding='utf-8').read()
    return [(full, kind) for (ln, kind, full, priv, sg) in parse(t, 10) if not priv and (kind in KINDS or kind in THM)]
probe = decls(PROBE)
pfull = set(f for f, k in probe)
lib = {}
for root in ['/Users/junyin/Lean_proof/RBM3D/RBM3D', '/Users/junyin/Lean_proof/RBM3D-wt/T2015/RBM3D']:
    for p in glob.glob(root + '/**/*.lean', recursive=True):
        if '/Probe/' in p: continue
        for f, k in decls(p): lib.setdefault(f, set()).add(p.replace('/Users/junyin/Lean_proof/', ''))
inter = sorted(pfull & set(lib))
print('public declarations of the probe (full names):', len(pfull))
print('library files parsed:', len(set(p for v in lib.values() for p in v)), '; library full names:', len(lib))
print('full-name clashes (probe vs library):', len(inter))
for f in inter: print('  CLASH', f, sorted(lib[f])[:2])
short = {}
for f in lib: short.setdefault(f.split('.')[-1], []).append(f)
co = sorted(f for f in pfull if f.split('.')[-1] in short and f.split('.')[-1] not in ('of_subset',) )
print('same short name, different namespace (probe copies of merged declarations, section 0, and instance names):', len(co))
for f in co: print('  ', f, '~', short[f.split('.')[-1]][:2])
```

### P.10 `cite_check.py`

```python
#!/usr/bin/env python3
"""Verify RBM2D citations `Dir/File.lean:N[,M..]` (Dir in Induction|Path|Green|Gauss|Hierarchy|Defs|Loop|Evolution|Main) of a text file against RBM2D at c9a24cf.
For each citation, print the cited line (trimmed).  If a Lean identifier in backticks/parentheses follows the citation within 40 characters, check that it occurs in lines N-1..N+4 of the cited file.
usage: cite_check.py FILE [--quiet]"""
import re, subprocess, sys
R = '/Users/junyin/Lean_proof/RBM2D'
def git(*a): return subprocess.run(['git', '-C', R, '--no-optional-locks', *a], capture_output=True, text=True).stdout
cache = {}
def lines(f):
    if f not in cache: cache[f] = git('show', f'c9a24cf:RBM2D/{f}').split('\n')
    return cache[f]
text = open(sys.argv[1], encoding='utf-8').read()
quiet = '--quiet' in sys.argv
pat = re.compile(r'(?<!RBM3D/)((?:Induction|Path|Green|Gauss|Hierarchy|Defs|Loop|Evolution|Main)/[A-Za-z0-9_]+\.lean):(\d+(?:,\d+)*)([^\n]{0,60})')
n = bad = 0
for m in pat.finditer(text):
    f, nums, tail = m.group(1), m.group(2), m.group(3)
    ls = lines(f)
    before = text[max(0, m.start() - 70):m.start()]
    cand_after = re.findall(r'`([A-Za-z_][A-Za-z0-9_.\']*)`', tail)[:1]
    cand_before = re.findall(r'`([A-Za-z_][A-Za-z0-9_.\']*)`\s*\(?\s*(?:[A-Z][A-Za-z0-9_]*/)*$', before)[-1:]
    names = [x for x in (cand_before or cand_after) if ('_' in x or re.search(r'[a-z][A-Z]', x))]
    for num in nums.split(','):
        k = int(num); n += 1
        ok = 1 <= k <= len(ls)
        seg = ' '.join(ls[max(k - 2, 0):k + 4]) if ok else ''
        found = None
        if names and ok and len(names[0]) > 3:
            nm = names[0].split('.')[-1]
            found = nm in seg
        if not ok or found is False:
            bad += 1
            print(f'BAD  {f}:{k}  names={names}  line="{ls[k-1][:80] if ok else "out of range"}"')
        elif not quiet:
            print(f'ok   {f}:{k}  {"name " + names[0] + " found" if found else ""}  | {ls[k-1].strip()[:90]}')
print(f'citations checked: {n}; failures: {bad}')
```

### P.10 `mkbind.py`

```python
#!/usr/bin/env python3
"""Binding variants of the probe against the merged declarations of main (T2012 = MD-2, T2013 = MD-3).
usage: mkbind.py OUT [--merged-calculus]
 * delete section 0 (the verbatim copy of the T2002 probe) and add the three imports; `open RBM.Path RBM.Gauss` for TimeIcc, PerTimeDomAt, HighProbAt;
 * with --merged-calculus: also delete the probe's own `StochDomAt.of_subset`, `StochDomAt.of_subset_union` (the merged ones are used)."""
import sys
out = sys.argv[1]; merged_calc = '--merged-calculus' in sys.argv
src = open('/Users/junyin/Lean_proof/RBM3D-wt/T2015/RBM3D/Probe/T2015Pins.lean', encoding='utf-8').read()
src = src.replace("import RBM3D.Loop.KLTree\n", "import RBM3D.Loop.KLTree\nimport RBM3D.Defs.StochDomAt\nimport RBM3D.Loop.GLoopFlow\nimport RBM3D.Gauss.DominationAt\n", 1)
a = src.index("/-! ## 0. Copied from the T2002 probe"); b = src.index("/-! ## 1. Estimate-level definitions")
src = src[:a] + src[b:]
i4 = src.index("/-! ## 4. The skeleton of the Step 1 continuity argument")
head, tail = src[:i4], src[i4:]
head = head.replace("open RBM RBM.Loop RBM.Probe.T2015", "open RBM RBM.Loop RBM.Path RBM.Gauss")
head = head.replace("open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Probe.T2015 Filter", "open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Path Filter")
tail = tail.replace("open RBM RBM.Probe.T2015 Filter", "open RBM RBM.Probe.T2015 RBM.Path RBM.Gauss Filter")
tail = tail.replace("open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Probe.T2015 Filter", "open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Probe.T2015 RBM.Path Filter")
src = head + tail
if merged_calc:
    a = src.index("/-- A failure event eventually contained in the failure event of a single domination. -/")
    b = src.index("/-- A failure event eventually contained in a failure event or the complement of a `w.h.p.`")
    src = src[:a] + src[b:]
    for nm in ('of_subset', 'of_subset_union'):
        src = src.replace("#print axioms RBM.Probe.T2015.StochDomAt.%s\n" % nm, "")
open(out, 'w', encoding='utf-8').write(src)
```

### P.10 `names.py`

```python
#!/usr/bin/env python3
"""Mathlib names used by the probe: candidate identifiers are scanned from the probe text, then `#check @name` is run in a file that imports Mathlib only
(so that names of RBM3D and local hypotheses fail); the names that elaborate are the verified Mathlib names.  Writes Names.lean and prints the result."""
import re, subprocess, sys
PROBE = '/Users/junyin/Lean_proof/RBM3D-wt/T2015/RBM3D/Probe/T2015Pins.lean'
src = open(PROBE, encoding='utf-8').read()
# drop comments
src = re.sub(r'/-.*?-/', '', src, flags=re.S)
src = re.sub(r'--[^\n]*', '', src)
cands = set()
for m in re.finditer(r"(?<![\w.'])((?:[A-Z][A-Za-z]*\.)*[a-z][A-Za-z0-9₀'.]*(?:_[A-Za-z0-9₀'.]+)+|(?:Real|Finset|Filter|Matrix|Complex|ENNReal|MeasureTheory|Nat|Set|Equiv|List|Fintype|Metric)\.[A-Za-z0-9_₀'.]+)", src):
    t = m.group(1).rstrip('.')
    cands.add(t)
own = set(re.findall(r'^(?:theorem|def|lemma)\s+([^\s:({\[]+)', src, flags=re.M))
cands = sorted(c for c in cands if c not in own and not c.startswith(('ST', 'RBM', 'h', 'e1', 'e2')) or c.startswith(('Real.', 'Finset.', 'Filter.', 'Matrix.', 'Complex.', 'ENNReal.', 'MeasureTheory.', 'Nat.', 'Set.', 'Equiv.', 'List.', 'Fintype.')))
hdr = """import RBM3D.Gauss.FineModel
import RBM3D.Defs.Sizes
import RBM3D.Loop.KLTree
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal
"""
body = '\n'.join(f'#check @{c}' for c in cands)
open('Names.lean', 'w', encoding='utf-8').write(hdr + body + '\n')
r = subprocess.run(['lake', 'env', 'lean', '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2015b/Names.lean'],
                   cwd='/Users/junyin/Lean_proof/RBM3D-wt/T2015', capture_output=True, text=True)
out = r.stdout + r.stderr
bad = set(re.findall(r'Names\.lean:(\d+):\d+: error', out))
lines = body.split('\n')
ok = [lines[i][len('#check @'):] for i in range(len(lines)) if str(i + 6) not in bad]
print('candidates', len(cands), 'elaborated (verified present in Mathlib):', len(ok), '; failed (RBM3D names, local hypotheses, unfinished prefixes):', len(cands) - len(ok))
print(' '.join(ok))
open('names_ok.txt', 'w').write('\n'.join(ok))
# one line per verified name with its type (first 150 characters)
open('NamesSig.lean', 'w', encoding='utf-8').write(hdr + '\n'.join(f'#check @{c}' for c in ok) + '\n')
r2 = subprocess.run(['lake', 'env', 'lean', '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2015b/NamesSig.lean'],
                    cwd='/Users/junyin/Lean_proof/RBM3D-wt/T2015', capture_output=True, text=True)
msgs = []
for l in (r2.stdout + r2.stderr).split('\n'):
    if '.lean:' in l or not l.strip(): continue
    if l.startswith(' ') and msgs: msgs[-1] += ' ' + l.strip()
    else: msgs.append(l.strip())
open('names_sig.txt', 'w', encoding='utf-8').write('\n'.join(re.sub(r'\s+', ' ', m)[:150] for m in msgs))
print('signature lines:', len(msgs))
open('names_fail.txt', 'w').write('\n'.join(c for c in cands if c not in ok))
```

### P.10 `samebody.py`

```python
#!/usr/bin/env python3
"""samebody.py FILE REF NAME=OLD->NEW ... : for each NAME, the text of the declaration NAME (extract.py: no docstring, no line markers)
with OLD replaced by NEW and the name NAME replaced by REF equals the text of the declaration REF.  Prints one line per NAME."""
import subprocess, sys
f, ref = sys.argv[1], sys.argv[2]
def body(nm):
    return subprocess.run(['python3', 'extract.py', f, nm, '--nomarkers'], capture_output=True, text=True).stdout
refb = body(ref)
for spec in sys.argv[3:]:
    nm, rest = spec.split('=', 1)
    old, new = rest.split('->', 1)
    ok = body(nm).replace(old, new).replace(nm, ref) == refb
    print(f"{nm}: " + (f"identical to {ref} with {old} -> {new}" if ok else "DIFFERENT"))
```

### P.10 `vocabdiff.py`

```python
#!/usr/bin/env python3
"""vocabdiff.py PROBE VOCAB : the 14 declarations of section 0 of the probe against their text in the T2002 probe vocabulary (`5d2a4a8`, sections 6-7).
A declaration is `identical` if the extracted texts (extract.py, no docstring) are equal, `normalized` if they are equal after rewriting the dot notation
(`SeqΩ sz` -> `sz.SeqΩ`, `seqHflow sz n t ω` -> `sz.seqHflow n t ω`, `(seqP sz)` -> `(sz.seqP)`, `Path.PerTimeDomAt` -> `PerTimeDomAt`) and dropping the section
variables `(P : Measure Ω)`, `{U : ℕ → Type*}` from the binder list, and `DIFFERENT` otherwise."""
import subprocess, sys, re
probe, vocab = sys.argv[1], sys.argv[2]
NAMES = ['Gres', 'loopM', 'blockMat', 'loopFine', 'Gt', 'Lloop', 'badSetAt', 'StochDomAt', 'HighProbAt', 'PerTimeDomAt', 'TimeIcc', 'Prec', 'PrecPT', 'Whp']
def get(f, nm): return subprocess.run(['python3', 'extract.py', f, nm, '--nomarkers'], capture_output=True, text=True).stdout
def norm(t):
    t = t.replace('(P : Measure Ω) ', '').replace('{U : ℕ → Type*} ', '')
    t = t.replace('Set (SeqΩ sz)', 'Set sz.SeqΩ').replace('SeqΩ sz', 'sz.SeqΩ').replace('seqHflow sz n t ω', 'sz.seqHflow n t ω').replace('(seqP sz)', '(sz.seqP)')
    t = t.replace('Path.PerTimeDomAt', 'PerTimeDomAt')
    return re.sub(r'\s+', ' ', t).strip()
res = {'identical': [], 'normalized': [], 'DIFFERENT': []}
for nm in NAMES:
    a, b = get(vocab, nm), get(probe, nm)
    res['identical' if a == b else 'normalized' if norm(a) == norm(b) else 'DIFFERENT'].append(nm)
for k, v in res.items(): print(f'{k} ({len(v)}): ' + ' '.join(v))
```

### P.10 `usedby.py`

```python
#!/usr/bin/env python3
"""usedby.py FILE [--wrap N] NAME... : for each probe declaration (theorem/lemma/def, text up to the next declaration start, comments removed) print the
given names that occur in its text, as `decl: name name ...`; names that occur nowhere are printed as `unused: ...`."""
import re, sys, textwrap
args = sys.argv[1:]
wrap = 0
if '--wrap' in args:
    i = args.index('--wrap'); wrap = int(args[i + 1]); del args[i:i + 2]
f, names = args[0], args[1:]
src = open(f, encoding='utf-8').read()
src = re.sub(r'/-.*?-/', '', src, flags=re.S)
src = re.sub(r'--[^\n]*', '', src)
starts = [(m.start(), m.group(1)) for m in re.finditer(r'^(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev)\s+([^\s:({\[]+)', src, flags=re.M)]
blocks = [(nm, src[a:(starts[i + 1][0] if i + 1 < len(starts) else len(src))]) for i, (a, nm) in enumerate(starts)]
used = {}
for nm, txt in blocks:
    hit = [x for x in names if re.search(r"(?<![\w.'])" + re.escape(x) + r"(?![\w'])", txt)]
    if hit: used[nm] = hit
items = [f'{nm}: ' + ' '.join(hit) for nm, hit in used.items()]
un = [x for x in names if not any(x in h for h in used.values())]
if un: items.append('unused: ' + ' '.join(un))
if wrap: print(textwrap.fill('; '.join(items), width=wrap, break_long_words=False, break_on_hyphens=False))
else:
    for it in items: print(it)
```

### P.10 `pinuses.py`

```python
#!/usr/bin/env python3
"""pinuses.py PROBE PIN... : the merged (or section-0) declarations that each pin's statement uses, through the probe's own ST... definitions (transitively).
A pin's statement is the text of its `def` (comments removed); an identifier of that text that is the name of another `def` of the probe's sections 1, 1b, 2 is expanded; an identifier
in the list MERGED (after the pin text) is reported.  Prints `PIN: names`, the names in the order of MERGED."""
import re, sys
MERGED = ['Sizes', 'Admissible', 'locDomain', 'Idx', 'Zd', 'zdistInf', 'Prec', 'PrecPT', 'Whp', 'TimeIcc', 'Gt', 'Lloop', 'KLK', 'Bctl', 'Bparam', 'ellT', 'etaT', 'Eblk', 'mE', 'lemE', 'lemT', 'zt', 'Gres']
probe, pins = sys.argv[1], sys.argv[2:]
src = open(probe, encoding='utf-8').read()
src = re.sub(r'/-.*?-/', '', src, flags=re.S)
src = re.sub(r'--[^\n]*', '', src)
sec = src[src.index('namespace RBM.Gauss.Sizes'):]
sec = sec[:sec.index('theorem STBctl_pos')] if 'theorem STBctl_pos' in sec else sec
defs = {}
for m in re.finditer(r'^def (ST\w+)(.*?)(?=^def |^theorem |^end |^namespace |^section |^variable |^open |^noncomputable |\Z)', sec, flags=re.S | re.M):
    defs[m.group(1)] = m.group(2)
def toks(t): return set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", t))
for pin in pins:
    seen, todo, found = set(), [pin], set()
    while todo:
        x = todo.pop()
        if x in seen or x not in defs: continue
        seen.add(x)
        for w in toks(defs[x]):
            base = w.split('.')[-1]
            if base in defs and base not in seen: todo.append(base)
            for mname in MERGED:
                if w == mname or w.endswith('.' + mname): found.add(mname)
    print(f'{pin}: ' + ' '.join(n for n in MERGED if n in found) + f'   [via {len(seen)} probe definitions]')
```

### P.10 `mkportmap.py`

```python
#!/usr/bin/env python3
"""Generates docs/reports/T2015-portmap.md (T2015, ST-D1) from the RBM2D tree at c9a24cf / 0c1330a (read-only git), the T2002 portmap rows,
and the probe.  usage: mkportmap.py OUT.md"""
import sys, json, re, subprocess, collections, datetime
sys.path.insert(0, '.')
import closure1 as c
import splitcalc as sc
import tokens as tk
from st1_list import rows, sel
from split_def import TICKETS
META = {x['path']: x for x in json.load(open('st1_meta.json'))}
DJ = json.load(open('st1_decls.json')); DECL = DJ['decls']; CGROUP = DJ['groups']
PROBE = '/Users/junyin/Lean_proof/RBM3D-wt/T2015/RBM3D/Probe/T2015Pins.lean'
now = subprocess.run(['date', '-u'], capture_output=True, text=True).stdout.strip()
out = []
def P(*a): out.append(' '.join(str(x) for x in a))
short = lambda p: p.replace('RBM2D/', '').replace('.lean', '')
ST1 = [x[0] for x in sel]
tid_of = {}
for t in TICKETS:
    for p in t['rbm2d'] + t.get('extra', []): tid_of.setdefault(p, []).append(t['id'])

P('# T2015 port map of sub-gate ST-1: RBM2D `c9a24cf` -> RBM3D (design report ST-D1)')
P()
P(f'Generated {now} (`date -u`) by the scripts of P.10 (python3; read-only `git -C ../RBM2D --no-optional-locks show`; the class, the sub-gate and the paper labels of each file are those of '
  '`docs/reports/T2002-portmap.md` part C, re-derived and checked below).  RBM2D line numbers are those of commit `c9a24cf`; "kept" is the line count of the same file at `0c1330a` '
  '(`-1`: deleted as dead code by RBM2D T2274), i.e. the part the final d = 2 proof uses.  Dependencies between files are the imports of the **kept** text (`0c1330a`); an import is an upper bound of a real dependency.')
P()
# ------------------------------------------------------------------ P.1
P('## P.1 Inventory (ticket item 1): the 86 files of ST-1')
P()
P('Selection rule (T2002 portmap, `mkportmap.py`): groups `Gauss/.*`, `Green/.*`, `Hierarchy/.*`, `Induction/(Continuity|ConArg|ConArgDet|Step1)` minus the MD vocabulary files '
  '(`Gauss/{Model,Domination,MomentBridge,LinearForm,Envelope,SteinMatrix}`, `Hierarchy/{Loops,Operations,OperationsPairWord}`) minus class d.  '
  'Columns: lines at `c9a24cf` / kept at `0c1330a` (recomputed from git: equal to the T2002 numbers for all 86 rows), class (a: renaming only, b: exponents, c: re-written), '
  'exponent tokens by kind counted in the file text (`W2` = `W ^ 2`, `L2`, `N2` = `(W * L) ^ 2` or `size ^ 2`, `inv2` = `W⁻²`-type, `d=2`, `Z2` = `Z2`/`zdist2`, `1/5`, `scal` = uses of `scaleM/ellT/tailT/ellStar/Meta/ellz`), '
  'paper labels (this paper) cited by the file (T2002; `(dir)` = inferred from the directory), number of public declarations (defs/theorems), number referenced by files of ST-2..ST-6, and the ticket of P.7.')
P()
P('| # | RBM2D file | lines | kept | cl | exponent tokens | paper labels (T2002) | pub | used | ticket |')
P('|---|---|---|---|---|---|---|---|---|---|')
for i, p in enumerate(ST1, 1):
    m = META[p]
    toks = ' '.join(f'{k}:{v}' for k, v in m['tok'].items() if v)
    labs = m['labels'].replace('|', '/')
    labs = labs if len(labs) < 110 else labs[:107] + '...'
    nd = len(DECL[p]); nu = sum(1 for x in DECL[p] if x['users'])
    tids = ','.join(tid_of.get(p, ['-']))
    P(f"| {i} | {short(p)} | {m['lines']} | {m['kept']} | {m['cls']} | {toks or '-'} | {labs or '-'} | {nd} | {nu} | {tids} |")
P()
# ------------------------------------------------------------------ P.2
P('## P.2 Totals (checked against T2002 portmap part E)')
P()
by = collections.OrderedDict()
for p in ST1:
    d = p.split('/')[1]
    e = by.setdefault(d, [0, 0, 0, collections.Counter(), 0, 0])
    e[0] += 1; e[1] += META[p]['lines']; e[2] += META[p]['kept']; e[3][META[p]['cls']] += 1
    e[4] += len(DECL[p]); e[5] += sum(1 for x in DECL[p] if x['users'])
P('| dir | files | lines c9a24cf | kept 0c1330a | a/b/c | public decls | referenced by ST-2..6 |')
P('|---|---|---|---|---|---|---|')
T = [0, 0, 0, collections.Counter(), 0, 0]
for d, e in by.items():
    P(f"| {d} | {e[0]} | {e[1]} | {e[2]} | {e[3]['a']}/{e[3]['b']}/{e[3]['c']} | {e[4]} | {e[5]} |")
    T[0] += e[0]; T[1] += e[1]; T[2] += e[2]; T[3].update(e[3]); T[4] += e[4]; T[5] += e[5]
P(f"| **ST-1** | **{T[0]}** | **{T[1]}** | **{T[2]}** | **{T[3]['a']}/{T[3]['b']}/{T[3]['c']}** | **{T[4]}** | **{T[5]}** |")
P()
P(f"T2002 part E, row ST-1: 86 files / 38498 lines / 29932 kept / 29/56/1/0.  Recomputed: {T[0]} / {T[1]} / {T[2]} / {T[3]['a']}/{T[3]['b']}/{T[3]['c']}: "
  + ('equal.' if (T[0], T[1], T[2], T[3]['a'], T[3]['b'], T[3]['c']) == (86, 38498, 29932, 29, 56, 1) else 'DIFFERENT.'))
P()
# ------------------------------------------------------------------ P.3
P('## P.3 The interface of ST-1: declarations referenced by files of ST-2..ST-6 (ticket item 1)')
P()
P('A public declaration (def/theorem of an ST-1 file, name at `c9a24cf`) is "referenced" if its qualified name, a dotted suffix, or (when the short name is unique among the ST-1 declarations and has at least 6 characters) the short name occurs as an identifier in a file of '
  'ST-2, ST-3, ST-4, ST-5 or ST-6 (119 files, class != d, text at `c9a24cf`, comments stripped).  Short names of fewer than 6 characters (`h`, `U`, `w`, `congr`, `cons`) are excluded: with them the count was inflated by tactics and bound variables.')
P()
P('| ST-1 file:line | kind | declaration | referenced by (groups; files) | ticket |')
P('|---|---|---|---|---|')
nref = 0
for p in ST1:
    for x in DECL[p]:
        if not x['users']: continue
        nref += 1
        gs = collections.Counter(CGROUP[u] for u in x['users'])
        gtxt = ', '.join(f'{g}:{n}' for g, n in sorted(gs.items()))
        P(f"| {short(p)}:{x['line']} | {x['kind']} | {x['name'].replace('RBM.', '')} | {gtxt} | {','.join(tid_of.get(p, ['-']))} |")
P()
P(f'Total: {nref} declarations of {sum(len(v) for v in DECL.values())}, in {sum(1 for p in ST1 if any(x["users"] for x in DECL[p]))} of the 86 files.')
P()
# ------------------------------------------------------------------ P.4
P('## P.4 Prerequisites outside ST-1: the import closures (kept graph) of the two chains')
P()
for root, label in [('Induction/Step1', 'Step 1 chain (`Induction/Step1.lean`)'), ('Green/GbEXP', '`lem_GbEXP` chain (`Green/GbEXP.lean`)')]:
    cl = c.closure(['RBM2D/' + root + '.lean'])
    byg = collections.defaultdict(list)
    for p in cl: byg[c.group_of(p)].append(p)
    P(f'**{label}**: ' + ', '.join(f"{g}: {len(byg[g])} files / {sum(max(rows[p][1], 0) for p in byg[g] if p in rows)} kept" for g in ['ST-1', 'MD', 'ST-2', 'ST-3', 'ST-6', 'none', 'other'] if g in byg) + '.')
    P()
    for g in ['MD', 'ST-2', 'ST-3', 'ST-6']:
        if g in byg:
            P(f'* {g}: ' + '; '.join(f"{short(p)} ({rows[p][1]} kept, cl {rows[p][2]})" for p in byg[g]))
    P()
P('**After cutting the imports of ST-2 and ST-6 files** (the RBM3D tickets replace them by the merged `Bctl/ellT/etaT` and by the probe vocabulary, P.7), the closures are:')
P()
ST1set = set(ST1)
def closure_cut(roots, drop_groups=('ST-2', 'ST-6')):
    seen = collections.OrderedDict(); q = collections.deque(roots); dropped = []
    while q:
        f = q.popleft()
        if f in seen: continue
        seen[f] = 1
        for g in c.imps.get(f, []):
            if c.group_of(g) in drop_groups:
                if (f, g) not in dropped: dropped.append((f, g))
                continue
            q.append(g)
    return list(seen), dropped
for root in ['Induction/Step1', 'Green/GbEXP']:
    cl, dr = closure_cut(['RBM2D/' + root + '.lean'])
    S = set(cl)
    byg = collections.defaultdict(list)
    for p in cl: byg[c.group_of(p)].append(p)
    links = sorted({(short(p), short(o)) for p in cl if c.group_of(p) != 'other' for o in c.imps.get(p, []) if o in S and c.group_of(o) == 'other' and 'Delocalization' not in o})
    P(f'* `{root}`: ' + ', '.join(f"{g}: {len(v)}" for g, v in byg.items()) + '; ST-3 files reached: ' + (', '.join(short(p) for p in byg.get('ST-3', [])) or 'none')
      + '; MD files: ' + ', '.join(short(p) for p in byg.get('MD', [])) + '.  Cut edges (importer -> ST-2/ST-6 file): ' + '; '.join(f"{short(a)} -> {short(b)}" for a, b in dr)
      + '.  Links from non-`other` files to the Propagator/Loop layer (PT, KL): ' + '; '.join(f"{a} -> {b}" for a, b in links) + '.')
P()
P('Reading: the Step 1 chain is 13 ST-1 files (5577 kept) plus `Induction/{ScaleFacts, PerTimeCalc, Split}` (ST-3 by T2002, 1745 kept: re-assigned to S1-08, S1-09) and the vocabulary `Induction/Defs` (ST-6, replaced by the probe: S1-07); '
  'the `lem_GbEXP` chain is 44 ST-1 files (21279 kept) plus `Induction/{PerTimeCalc, Split}`.  After the cuts the two chains touch the propagator and K-loop layers only through the links listed (`Green/Stability` for `lem_GbEXP`; the merged definition of Theta through `Path/Step2Props` and the `Loop/Kcal` link of class-d `Path/ScalesBridge` for Step 1), '
  'so ST-1 takes `ML:Kbound` (`STKbound`) and the PT pins as hypotheses and needs no ST-2 file.  '
  'The 41 ST-1 files outside the `lem_GbEXP` chain are the Gaussian-calculus and loop-contraction files (consumed by ST-2/ST-5: P.3) and the Step 1 stream.')
P()
P('## P.5 Dependency layers of the ST-1 files (imports of the kept text; layer = longest import path inside ST-1)')
P()
layer = {}
def lay(p):
    if p in layer: return layer[p]
    layer[p] = 0
    layer[p] = 1 + max([lay(q) for q in c.imps[p] if q in ST1] + [-1])
    return layer[p]
for p in ST1: lay(p)
byl = collections.defaultdict(list)
for p, l in layer.items(): byl[l].append(p)
P('| layer | files (kept lines) |')
P('|---|---|')
for l in sorted(byl):
    P(f"| {l} | " + ', '.join(f"{short(p).split('/')[-1]} ({META[p]['kept']})" for p in sorted(byl[l])) + ' |')
P()
# ------------------------------------------------------------------ P.6
P('## P.6 Exponent tokens of d = 2 in the Step 1 chain: file:line at `c9a24cf` (code lines only)')
P()
P('Kinds: `W2` = `W ^ 2`, `L2`, `N2` = `(W * L) ^ 2` / `size ^ 2`, `inv2` = `W⁻²`-type, `d2` = `d = 2`, `e30` = the exponent `30` / `29/30` of `con_st_ind`.  Script `tokens.py`.')
P()
P('| file:line | kinds | line |')
P('|---|---|---|')
res = tk.scan()
for f, i, ks, s in res:
    P(f"| {f}:{i} | {','.join(ks)} | `{s[:120].replace('|', '/')}` |")
P()
P(f'Total {len(res)} lines in {len(set(f for f, i, ks, s in res))} files.')
P()
# ------------------------------------------------------------------ P.7
P('## P.7 Split table (ticket item 7): 36 proof tickets for ST-1')
P()
P('Rules.  Tickets follow a topological order of the kept import graph (the script checks that every dependency of a ticket is an earlier ticket).  Size: `est` = kept lines of the RBM2D sources x 1.0 (class a) / 1.1 (class b) / 1.5 (class c) '
  '+ the new lines named in the notes + 60 (the compiled nonempty instance of every endpoint theorem, CLAUDE.md section 4 step 2) - the discount named in the notes; a file cut between two tickets is divided in proportion to its line ranges (the cut is a heading of the file).  '
  'Roles: `prover` = class a or class b with few exponent tokens; `prover-hard` = class b with many exponent tokens or deep proofs; `prover-max` = class c, interface-heavy, or endpoint.  '
  '"MD-k" = vocabulary tickets of T2002 E.2 (MD-1 T2006, MD-2 T2012, MD-3 T2013, MD-4 T2018, MD-5 T2021: all merged on `main`; tickets of this table that depend on MD-4 or MD-5: ' + (', '.join(t['id'] for t in TICKETS if {'MD-4', 'MD-5'} & set(sc.deps(t)[1])) or 'none') + ').  "cut" = an import of an ST-2/ST-3/ST-6 file that the RBM3D ticket replaces by a merged declaration or cuts.')
P()
P('| id | RBM3D target (under `RBM3D/`) | RBM2D sources (kept) | kept | est | depends on (ST-1) | MD / external | role |')
P('|---|---|---|---|---|---|---|---|')
tot = collections.Counter()
for t in TICKETS:
    l, k, e, cls = sc.sizes(t)
    s1, md, cross, other, none_ = sc.deps(t)
    srcs = []
    for p in t['rbm2d']:
        sh = t.get('shares', {}).get(p, 1.0)
        srcs.append(f"{short(p)}" + (f" ({round(rows[p][1]*sh)} of {rows[p][1]})" if sh < 1 else f" ({rows[p][1]})"))
    for p in t.get('extra', []):
        srcs.append(f"[{short(p)} ({rows[p][1]}; from {c.group_of(p)})]")
    ext = []
    for k_ in md: ext.append(f"{k_} ok")
    if any('Loop/Kcal' in o for o in other): ext.append('KL: STKbound hyp.')
    if any('Propagator' in o for o in other): ext.append('PT pins hyp.')
    if cross: ext.append('cut: ' + ', '.join(short(p) for p in cross))
    P(f"| {t['id']} | {', '.join(t['rbm3d'])}.lean | {'; '.join(srcs) if srcs else '(new)'} | {k} | {e} | {','.join(s1) or '-'} | {'; '.join(ext) or '-'} | {t['role']} |")
    tot['kept'] += k; tot['est'] += e
P()
P(f"Totals: {len(TICKETS)} tickets, kept {tot['kept']} (86 files = 29932, plus `Induction/{{ScaleFacts,PerTimeCalc,Split,Defs}}` = 2071), estimated {tot['est']} lines.")
import glob as _g, os as _os
_roots = ['/Users/junyin/Lean_proof/RBM3D'] + sorted(_g.glob('/Users/junyin/Lean_proof/RBM3D-wt/*'))
_tn = [(t['id'], n) for t in TICKETS for n in t['rbm3d']]
_ex = sorted(set(n for _, n in _tn if any(_os.path.exists(_os.path.join(r, 'RBM3D', n + '.lean')) for r in _roots)))
P(f"Target modules: {len(_tn)} names ({len(set(n for _, n in _tn))} distinct), checked for an existing file `RBM3D/<name>.lean` in the main worktree and {len(_roots) - 1} ticket worktrees: existing: {', '.join(_ex) or 'none'} "
  "(`Test/Axioms` is the registry: S1-07 adds the pins to it); every other name is new.")
rc = collections.Counter(t['role'] for t in TICKETS)
P('Roles: ' + ', '.join(f'{k} {v}' for k, v in rc.items()) + '.  Estimates per ticket: min ' + str(min(sc.sizes(t)[2] for t in TICKETS)) + ', max ' + str(max(sc.sizes(t)[2] for t in TICKETS)) + '.')
P()
dep = {}; estd = {}
for t in TICKETS:
    s1_, md_, cr_, ot_, no_ = sc.deps(t); dep[t['id']] = s1_; estd[t['id']] = sc.sizes(t)[2]
depth = {}
def _d(i):
    if i in depth: return depth[i]
    depth[i] = 1 + max([_d(j) for j in dep[i]] + [0]); return depth[i]
for i in dep: _d(i)
mx = max(depth.values()); cur = [i for i in depth if depth[i] == mx][0]; chain = [cur]
while dep[cur]:
    cur = max(dep[cur], key=lambda j: depth[j]); chain.append(cur)
P(f"Critical path: {mx} tickets ({' -> '.join(reversed(chain))}), {sum(estd[i] for i in chain)} estimated lines.  First wave (no ST-1 dependency): {', '.join(i for i in dep if not dep[i])}.  Tickets per dependency depth: "
  + ', '.join(f'{k}: {sum(1 for v in depth.values() if v == k)}' for k in sorted(set(depth.values()))) + '.')
P()
P('Notes per ticket (new content, merged overlap, cuts):')
for t in TICKETS:
    if t.get('note'): P(f"* {t['id']}: {t['note']}")
P()
P('Key statements per ticket (RBM2D `file:line name` at `c9a24cf`; names listed in the ticket definition are looked up in the inventory and the script fails if one is missing; tickets without a list show the last public theorem of each source file):')
P()
import inv as _inv
def decls_of(p):
    if p in DECL: return [(x['line'], x['kind'], x['name']) for x in DECL[p]]
    t = subprocess.run(['git', '-C', '/Users/junyin/Lean_proof/RBM2D', '--no-optional-locks', 'show', f'c9a24cf:{p}'], capture_output=True, text=True, check=True).stdout
    return [(ln, kind, full) for (ln, kind, full, priv, sg) in _inv.parse(t, 10) if not priv and (kind in _inv.KINDS or kind in _inv.THM)]
for t in TICKETS:
    hs = []
    if t.get('key'):
        for f, nm in t['key']:
            p = 'RBM2D/' + f + '.lean'
            hit = [(ln, full) for (ln, kind, full) in decls_of(p) if full.split('.')[-1] == nm]
            assert hit, ('key statement not found', f, nm)
            hs.append(f"{f.split('/')[-1]}:{hit[0][0]} {nm}")
    else:
        for p in t['rbm2d'] + t.get('extra', []):
            th = [(ln, full) for (ln, kind, full) in decls_of(p) if kind in ('theorem', 'lemma')]
            if th and not p.endswith('Induction/Defs.lean'):
                ln, full = th[-1]; hs.append(f"{short(p).split('/')[-1]}:{ln} {full.split('.')[-1]}")
    P(f"* {t['id']}: " + ('; '.join(hs) if hs else '(new)'))
P()
P('Stream totals (kept lines / estimated lines / tickets):')
P()
streams = [('Gaussian calculus and loop algebra (S1-01..S1-06)', range(1, 7)), ('pins, Step 1 scale facts and calculus, loop splitting (S1-07..S1-09)', range(7, 10)),
           ('Green: `lem_GbEXP` (S1-10..S1-30)', range(10, 31)), ('Step 1 proper: `lem_ConArg`, continuity, Step 1 (S1-31..S1-36)', range(31, 37))]
for lab, rg in streams:
    ts = [t for t in TICKETS if int(t['id'][3:]) in rg]
    P(f"* {lab}: {sum(sc.sizes(t)[1] for t in ts)} / {sum(sc.sizes(t)[2] for t in ts)} / {len(ts)}")
P()
# ------------------------------------------------------------------ P.8
P('## P.8 Probe extracts (script `extract.py`; docstrings omitted; full text: `RBM3D/Probe/T2015Pins.lean` on branch `t/T2015`)')
P()
def ext(names, head=False):
    r = subprocess.run(['python3', 'extract.py', PROBE] + names + (['--head'] if head else []), capture_output=True, text=True)
    return r.stdout.rstrip('\n')
P('### P.8.1 Estimate-level definitions (probe sections 1, 1b) and the Step 1 conclusions')
P('```lean')
P(ext(['STKloop', 'STWB', 'STblk', 'STGM', 'STmaxLoop2', 'STomegaC', 'STgexRHS', 'STLK', 'STLmax', 'STDecay', 'STDecayStrong', 'STLocalMax', 'STLocalEntry',
       'STExp2', 'STConStInd', 'STKbound', 'STindMax', 'STGiiGEX', 'STGijGEX', 'STGavLGEX', 'STStep1Loop', 'STStep1Weak', 'STStep1LoopPT', 'STStep1WeakPT', 'STForbidden']))
P('```')
P()
P('### P.8.2 The pins (probe section 2) and the deterministic pins of the skeleton')
P('```lean')
P(ext(['STflowE', 'STFlow', 'STMainInd', 'STGbEXPii', 'STGbEXPij', 'STGbEXPav', 'STGbEXP', 'STConArg', 'STStep1', 'STBootstrap', 'STNetLift', 'STLoopBase', 'STEnvelope']))
P('```')
P()
P('### P.8.3 The skeleton and the compiled instances (statements only, `--head`)')
P('```lean')
P(ext(['ST_step1_skeleton', 'ST_apriori', 'inst_mainInd', 'inst_gbEXP', 'inst_conArg', 'inst_step1', 'inst_bootstrap', 'inst_netLift', 'inst_skeleton', 'inst_precPT',
       'inst_gbEXP_endT', 'inst_conArg_endT', 'sz1_admissible', 'inst_mainInd_lowg', 'inst_gbEXP_lowg', 'inst_conArg_lowg', 'inst_step1_lowg'], head=True))
P('```')
P()
P('### P.8.4 `bind2_extra.lean`: the text appended to `bind1.lean` to show that `STEnvelope` is the merged sharp envelope (report b.2)')
P('```lean')
P(open('bind2_extra.lean', encoding='utf-8').read().strip('\n'))
P('```')
P()
P('### P.8.5 Merged declarations used by each pin (script `pinuses.py`: the identifiers of the pin statement and of the probe `ST...` definitions it reaches; `Eblk` is inside `Lloop` (merged `loopM`), `Bparam` inside `Bctl`)')
P('```')
r_ = subprocess.run(['python3', 'pinuses.py', PROBE, 'STMainInd', 'STGbEXP', 'STConArg', 'STStep1', 'STBootstrap', 'STNetLift', 'STKbound', 'STFlow'], capture_output=True, text=True)
P('$ python3 pinuses.py T2015Pins.lean STMainInd STGbEXP STConArg STStep1 STBootstrap STNetLift STKbound STFlow')
P(r_.stdout.rstrip('\n'))
P('```')
P()
# ------------------------------------------------------------------ P.10 (placed before the scripts)
P('## P.9 Mathlib names used by the probe (script `names.py`: every candidate identifier of the probe text is `#check`ed in a file that imports the probe\'s modules and opens only `MeasureTheory ProbabilityTheory Filter Matrix`)')
P()
ok = open('names_ok.txt').read().split('\n'); fail = open('names_fail.txt').read().split('\n')
tactic = {'by_cases', 'by_contra', 'norm_num', 'field_simp', 'push_cast', 'exact_mod_cast', 'ring_nf', 'split_ifs', 'filter_upwards', 'set_option', 'le_rfl'}
P(f'Candidates {len(ok) + len(fail)}; elaborate (present in Lean core, Std or Mathlib): {len(ok)}; do not elaborate under these opens: {len(fail)} (names of RBM3D declarations, which live in namespace `RBM`, local hypotheses, field projections).  '
  'No name was invented: a name absent from Mathlib would be in the second list and would fail the build.')
P()
sigs = open('names_sig.txt', encoding='utf-8').read().split('\n')
P('Present, one line each (`#check @name`, the type cut at 150 characters; script `names.py`):')
P()
P('```')
for sline in sigs: P(sline)
P('```')
P()
P('Not elaborated (RBM3D, local): ' + ' '.join(fail))
P()
# ------------------------------------------------------------------ P.9
P('## P.10 Scripts (verbatim; run from one directory in this order: `st1_list.py`, `st1_meta.py`, `st1_decls.py`, `names.py`, `mkportmap.py OUT`; `inv.py`, `closure1.py`, `tokens.py`, `split_def.py`, `splitcalc.py`, `extract.py` are libraries; `clash.py`, `cite_check.py`, `mkbind.py`, `names.py`, `samebody.py`, `vocabdiff.py`, `usedby.py`, `pinuses.py` are the checks of the prove report; `bind2_extra.lean` is printed in P.8.4)')
P()
for fn in ['inv.py', 'st1_list.py', 'st1_meta.py', 'st1_decls.py', 'closure1.py', 'tokens.py', 'split_def.py', 'splitcalc.py', 'extract.py', 'clash.py', 'cite_check.py', 'mkbind.py', 'names.py', 'samebody.py', 'vocabdiff.py', 'usedby.py', 'pinuses.py', 'mkportmap.py']:
    P(f'### P.10 `{fn}`')
    P()
    P('```python')
    P(open(fn, encoding='utf-8').read().rstrip('\n'))
    P('```')
    P()
txt = '\n'.join(out)
open(sys.argv[1], 'w', encoding='utf-8').write(txt)
print('written', sys.argv[1], len(out), 'lines')
```
