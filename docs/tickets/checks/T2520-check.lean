/-
Release check for T2520 (dispatcher V5, 2026-10-16 12:58 UTC; DECISIONS §353; supervisor 2026-10-15-0643 Q1 (vi)-(vii), Q4 (b),
MNO-C1-C4; 2026-10-15-1044 Q1; 2026-10-16-1134 O3).  M/N N2, the last M/N row (drafted by the dispatcher's helper 11:08 UTC).
Part 1 (the release gate): merged names on `main` (checked at 43597737 with `docs/claude-team/tools/nsof.sh`; `main` has had
docs-only commits since).  Part 2: the five C5 (T2519) names N2 reads (activated 2026-10-16 19:10 UTC after rows a and d merged; two imports added).
The proposals `T2520_*` are in `docs/tickets/checks/T2520-pins.lean` (not a gate; they bind after N2's 1a).
Statements only; no proofs.
Run: lake env lean docs/tickets/checks/T2520-check.lean
-/
import RBM3D.Main.BandTerminal
import RBM3D.BA.UNPins
import RBM3D.BA.EMCTE2BA
import RBM3D.BA.RandomLayerBGBA
import RBM3D.BA.MReg
import RBM3D.BA.MALocal
import RBM3D.BA.MATrLocalBA
import RBM3D.BA.MAQDiff
import RBM3D.BA.MADecolQUE
import RBM3D.BA.GUEKPrim
import RBM3D.BA.MainIndTermBA
import RBM3D.Universality.GUEPhase.RandomLayerBG
import RBM3D.Universality.OUInterfaceK
import RBM3D.Universality.QUEFlow
import RBM3D.Universality.UnivMain
import RBM3D.Universality.NormBand
import RBM3D.Universality.GUELocalBootstrap
import RBM3D.Universality.GUELocalSchur
import RBM3D.BA.GUEProcBA
import RBM3D.BA.GUEHyp

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 1: merged names (release gate; `main` 43597737) -/

-- G1 sources: the merged generic pins that get a filtered successor (MN-D3 D1, report `:91-107`; statdiff 8 of 8, report §0)
#check @RBM.Univ.UNQuek                             -- Universality/PinsK:398
#check @RBM.Univ.UNLocAvgk                          -- PinsK:406
#check @RBM.Univ.UNOUClaimsk                        -- PinsK:421
#check @RBM.Univ.UNOURowk                           -- PinsK:426
#check @RBM.Univ.UNEMCTE2Rowk                       -- PinsK:429
#check @RBM.Univ.UNJakUywRowk                       -- PinsK:435
#check @RBM.Univ.UNClaimRowk                        -- PinsK:442
#check @RBM.Univ.UNG1Rowk                           -- Universality/OUInterfaceK:101 (registry `Test/Axioms:169`)
#check @RBM.Univ.UNOULLk                            -- OUInterfaceK:69 (registry `Test/Axioms:168`)
#check @RBM.Univ.UNOUEq747k                         -- OUInterfaceK:80
#check @RBM.Univ.UNG2bRowk                          -- OUInterfaceK:109 (not filtered: per `d` already)
#check @RBM.Univ.UNOUProfRowk                       -- OUInterfaceK:56 (not filtered; structural `Test/Axioms:386`)
#check @RBM.Univ.UNOUProfile                        -- OUInterfaceK:43
#check @RBM.Univ.UNOUQUEk                           -- PinsK:326 (structural `Test/Axioms:387`)
#check @RBM.Univ.UNOUDiagk                          -- PinsK:335
#check @RBM.Univ.UNClaimAllC                        -- PinsK:158
#check @RBM.Univ.UNKind                             -- PinsK:307
#check @RBM.Univ.UNKind.band                        -- PinsK:315
#check @RBM.Univ.ouTauMax                           -- Universality/ZeroModeProfile:78
#check @RBM.Univ.ouTauMax_pos                       -- ZeroModeProfile:530
-- the band recovery at `Dm = fun _ => True` (MNO-C1)
#check @RBM.Univ.UNLocAvgk_band                     -- PinsK:554
#check @RBM.Univ.UNOURowk_band                      -- PinsK:560
#check @RBM.Univ.UNLocAvgBand                       -- Universality/Pins:416
#check @RBM.Univ.UNQueBand                          -- Pins:404
#check @RBM.Univ.UNOURow                            -- Pins:793
#check @RBM.Univ.UNMLOut                            -- Pins:432
#check @RBM.Endpoints.band_terminal                 -- Main/BandTerminal:104 (`#print axioms` before and after, MNO-C1)
#check @RBM.Endpoints.bUniv_holds                   -- Main/BUnivHolds:227 (same)

-- G2 sources: the merged chain whose proofs get the filter threaded through (D2, report `:108-119`)
#check @RBM.Univ.un_claimAll_of_rowsk               -- PinsK:454
#check @RBM.Univ.unClaimRowk                        -- Universality/UnivMain:471
#check @RBM.Univ.ouRowk_of_pins                     -- OUInterfaceK:292
#check @RBM.Univ.ouDiagk_of_ouLLk                   -- OUInterfaceK:221
#check @RBM.Univ.GUEPhase.g1Rowk_of_inputsG         -- Universality/GUEPhase/RandomLayerBG:399 (privates `RandomLayerBG_oull_seq` :265, `RandomLayerBG_eq747_seq` :313)
#check @RBM.Univ.GUEPhase.RandomLayerBG_pad_subseq  -- RandomLayerBG:105
#check @RBM.Univ.GUEPhase.RBG_Flow                  -- RandomLayerBG:59
#check @RBM.Univ.GUEPhase.RBG_Dom                   -- RandomLayerBG:65
#check @RBM.Univ.GUEPhase.RBG_Prod                  -- RandomLayerBG:72
#check @RBM.Univ.GUEPhase.RBG_Que                   -- RandomLayerBG:87
#check @RBM.Univ.GUEPhase.RBG_Comp                  -- RandomLayerBG:115
#check @RBM.Univ.GUEPhase.RBG_ProfComp              -- RandomLayerBG:123
#check @RBM.Univ.GUEPhase.RandomLayerB_LL           -- Universality/GUEPhase/RandomLayerB:151
#check @RBM.Univ.GUEPhase.RandomLayerB_MLout        -- RandomLayerB:123
#check @RBM.Univ.GUEPhase.g1Rowk_band               -- RandomLayerB:454 (band half of `Test/Axioms:168-169`)
#check @RBM.Gauss.Sizes.comp_admissible             -- Induction/SizesComp:93
#check @RBM.Univ.unClaim417C_of_rows                -- UnivMain:398
#check @RBM.Univ.g2bRowk                            -- Universality/QUEFlow:898

-- the BA side: the UN pins of block Anderson, the rows, the merged `∀ d` assembly (left unedited, MNO-C1)
#check @RBM.Univ.UNKind.ba                          -- BA/UNPins:84
#check @RBM.Univ.UNModelC.ba                        -- UNPins:64
#check @RBM.Univ.UNQueBA                            -- UNPins:99
#check @RBM.Univ.UNLocAvgBA                         -- UNPins:103
#check @RBM.Univ.UNMLOutBA                          -- UNPins:110
#check @RBM.Univ.UNOURowBA                          -- UNPins:123 (owed `Test/Axioms:176`)
#check @RBM.Univ.UNEMCTE2RowBA                      -- UNPins:128 (owed `Test/Axioms:177`)
#check @RBM.Univ.UNJakUywRowBA                      -- UNPins:132 (owed `Test/Axioms:178`)
#check @RBM.Univ.UNClaimRowBA                       -- UNPins:136
#check @RBM.Univ.un_claimAll_of_rowsBA              -- UNPins:142
#check @RBM.Univ.UNDensBARow'                       -- UNPins:159
#check @RBM.Univ.UNTrLocalBARow                     -- UNPins:169
#check @RBM.Univ.UNTrLocalInitBARow'                -- UNPins:181
#check @RBM.Univ.UNNormBARow                        -- UNPins:190 (owed `Test/Axioms:179`)
#check @RBM.Univ.unMeanBound_ba                     -- UNPins:285 (private `UNPins_normBound_mono` :273, `UNPins_eig_le_rowsum` :201)
#check @RBM.BA.BAEnd_QUEL                           -- UNPins:333
#check @RBM.BA.BAEnd_BUnivL                         -- UNPins:343
#check @RBM.Univ.UNQueBA_of_BAEnd_QUEL              -- UNPins:357
#check @RBM.Univ.baBUniv_of_rows                    -- UNPins:367
#check @RBM.Gauss.Sizes.seqHBA                      -- Gauss/BlockAnderson:96 (`H = λΨ + V`, `V` of `sz.withLam 0`)
#check @RBM.Univ.UNNormBound                        -- Universality/Pins:477
#check @RBM.Univ.UNNormBandRow                      -- Pins:834
#check @RBM.Univ.unNormBandRow                      -- Universality/NormBand:173 (twin of `UNNormBARow`; privates `NormBand_eig_le` :66, `NormBand_tail_eventually` :122, `NormBand_gvar_le` :138)

-- M1 row a (3a67e18d), M1 row b (242d669e): the MN1 pins and the per-`d` texts and cores (MNO-C3; DECISIONS §340 (2))
#check @RBM.BA.BAEnd_locSCL                         -- BA/MAPins:97
#check @RBM.BA.BAEnd_QDiffL                         -- MAPins:107
#check @RBM.BA.BAEnd_decolL                         -- MAPins:121
#check @RBM.BA.BAThm27L                             -- MAPins:126 (the input of MA-06b)
#check @RBM.BA.UNLocAvgBAAt                         -- MAPins:170
#check @RBM.BA.UNTrLocalBAAt                        -- MAPins:180
#check @RBM.BA.UNTrLocalInitBAAt'                   -- MAPins:187
#check @RBM.BA.UNLocAvgBA_iff_at                    -- MAPins:196
#check @RBM.BA.UNTrLocalBARow_iff_at                -- MAPins:199
#check @RBM.BA.UNTrLocalInitBARow'_iff_at           -- MAPins:202
#check @RBM.BA.baEnd_locSCL                         -- BA/MALocal:834
#check @RBM.BA.baEnd_locSCL_three                   -- MALocal:839
#check @RBM.BA.unLocAvgBAAt_of_locSCL               -- MALocal:843
#check @RBM.BA.UNLocAvgBA_of_BAEnd_locSCL           -- MALocal:854
#check @RBM.BA.unLocAvgBAAt_of_ML                   -- MALocal:858
#check @RBM.BA.unTrLocalBAAt_of_locAvg              -- BA/MATrLocalBA:80
#check @RBM.BA.unTrLocalBARow_holds                 -- MATrLocalBA:92
#check @RBM.BA.unTrLocalInitBAAt'_of_locAvg         -- MATrLocalBA:237
#check @RBM.BA.unTrLocalInitBARow'_holds            -- MATrLocalBA:448
-- M2 (dec8e150), M3 (9c5fc941)
#check @RBM.BA.baEnd_QDiffL                         -- BA/MAQDiff:1012
#check @RBM.BA.baEnd_QDiffL_three                   -- MAQDiff:1016
#check @RBM.BA.UNQueBAAt                            -- BA/MADecolQUE:52
#check @RBM.BA.UNQueBA_iff_at                       -- MADecolQUE:60
#check @RBM.BA.baEnd_decolL                         -- MADecolQUE:143
#check @RBM.BA.baEnd_decolL_three                   -- MADecolQUE:147
#check @RBM.BA.baEnd_QUEL                           -- MADecolQUE:359
#check @RBM.BA.baEnd_QUEL_three                     -- MADecolQUE:363
#check @RBM.BA.unQueBAAt_of_QUEL                    -- MADecolQUE:373
#check @RBM.BA.unQueBAAt_of_ML                      -- MADecolQUE:378
#check @RBM.BA.unQueBAAt_three                      -- MADecolQUE:382
-- V terminal (T2511 b, c536c603) and the general-`d` step (closing (iii), (vii))
#check @RBM.BA.unMLOutBA_three                      -- BA/MainIndTermBA:47
#check @RBM.BA.baMainIndFamTL_any                   -- MainIndTermBA:53
#check @RBM.BA.unMLOutBA_of_famStep                 -- BA/MainIndOutBA:326
#check @RBM.BA.STStep5IIIgL                         -- Chain/Step5Gen:228
#check @RBM.BA.BAFlow                               -- BA/FlowPins:389
#check @RBM.BA.baFMz                                -- FlowPins:393
#check @RBM.BA.BAflowT0                             -- FlowPins:380
-- C3 (13b68cea, fde07256)
#check @RBM.Univ.UNOUProfile.ba                     -- BA/GUEKPrim:77
#check @RBM.BA.baOUProfRowk_holds                   -- GUEKPrim:584
#check @RBM.BA.baProfComp                           -- GUEKPrim:604
-- C5g (T2475): the BA vocabulary of the random layer and its N2 reading (`BA/RandomLayerBGBA:199-212`)
#check @RBM.BA.BAfT                                 -- BA/RandomLayerBGBA:49
#check @RBM.BA.BAfE                                 -- RandomLayerBGBA:52
#check @RBM.BA.BAEd                                 -- RandomLayerBGBA:56
#check @RBM.BA.BAMO                                 -- RandomLayerBGBA:61
#check @RBM.BA.ba_flowG                             -- RandomLayerBGBA:92
#check @RBM.BA.ba_domG                              -- RandomLayerBGBA:103
#check @RBM.BA.ba_mlout                             -- RandomLayerBGBA:115
#check @RBM.BA.RandomLayerBGBA_comp                 -- RandomLayerBGBA:126
-- N3a / N3b (T2476, T2477): the BA rows and the kind hypotheses
#check @RBM.Univ.jakUywRowk                         -- BA/EMCTE2BA:629
#check @RBM.Univ.unEMCTE2RowBA_holds                -- EMCTE2BA:656
#check @RBM.Univ.UNBulkWindowk                      -- EMCTE2BA:394
#check @RBM.Univ.UNBadBoundk                        -- EMCTE2BA:402
#check @RBM.Univ.UNBad2Boundk                       -- EMCTE2BA:418
#check @RBM.Univ.UNBulkWindowk_ba                   -- EMCTE2BA:684
#check @RBM.Univ.UNBadBoundk_ba                     -- EMCTE2BA:690
#check @RBM.Univ.UNBad2Boundk_ba                    -- EMCTE2BA:755
#check @RBM.Univ.unJakUywRowBA_holds                -- EMCTE2BA:766
#check @RBM.Univ.unJak_of_ouClaimsk                 -- EMCTE2BA:476
#check @RBM.Univ.unUyw_of_ouClaimsk                 -- EMCTE2BA:553
#check @RBM.Endpoints.unClaimRowBA_holds            -- Main/BandTerminal:88 (unfiltered; cannot feed the filtered chain, report F2 `:177`)
-- the proved leaves of the core (as in `T2513_n2_three`, probe :309-311)
#check @RBM.Univ.UNCoreC''                          -- Universality/PinsC2:106
#check @RBM.Univ.unCoreC''_holds                    -- UnivMain:652
#check @RBM.Univ.UNL32                              -- Universality/Pins:281 (borrowed, `Test/Axioms:93`; the only external hypothesis, closing (vi))
#check @RBM.Univ.UNGUELocal                         -- Pins:489
#check @RBM.Univ.un_gueLocal_of_tail                -- Universality/GUELocalBootstrap:952
#check @RBM.Univ.gueSchurTail                       -- Universality/GUELocalSchur:540
#check @RBM.Univ.UNGreenCorrAllC                    -- PinsK:204
#check @RBM.Univ.greenCorrAllC                      -- Universality/GreenCorr:956
#check @RBM.Univ.unDensBARow'_holds                 -- BA/MReg:333
-- vocabulary of the texts below
#check @RBM.Univ.UNTrLocal                          -- Pins:447
#check @RBM.Univ.UNTrLocalInit'                     -- Universality/PinsC2:72
#check @RBM.Univ.UNUnivDilAt                        -- Pins:195
#check @RBM.BA.BAbulk                               -- BA/MFixedPoint:429
#check @RBM.BA.BAm                                  -- MFixedPoint:379
#check @RBM.BA.BArho                                -- MFixedPoint:384

/-! ## Part 2: C5 (T2519) names (activated 2026-10-16 19:10 UTC: row a 9e07cc2e, row d bcdddd36 merged; DECISIONS §365) -/

#check @RBM.BA.BAKFam            -- T2519 row a, BA/GUEProcBA (target 1; text `T2519_KFamBA`, `T2519-pins.lean:45`)
#check @RBM.BA.BAPB              -- T2519 row a, BA/GUEProcBA (target 1; text `T2519_PBBA`, `T2519-pins.lean:125`)
#check @RBM.BA.ba_prodG          -- T2519 row d, BA/GUEHyp (target 16; `T2519_ProdBA BAKFam BAPB`, `T2519-pins.lean:28`)
#check @RBM.BA.ba_LLG            -- T2519 row d (target 16; `T2519_LLBA BAPB`, `:33`)
#check @RBM.BA.ba_QueG           -- T2519 row d (target 16; `T2519_QueBA BAKFam BAPB`, `:38`)
