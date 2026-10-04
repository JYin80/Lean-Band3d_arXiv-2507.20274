# T2162 port map: RBM2D `c9a24cf` Universality -> RBM3D `Universality/` (design report, ticket T2162)

Generated Sun Oct  4 22:35:05 UTC 2026 by the scripts of section P.5 (inv.py, deps.py, keydecls.py, consumers.py, split.py).  RBM2D is read at `c9a24cf` through `git archive` (read-only).  RBM3D file:line citations are on `main` at the branch point `a21a819` of `t/T2162`.  "Kept" lines are the lines at RBM2D `0c1330a` as recorded in `docs/reports/T2002-portmap.md` section C.

## P.1 Inventory of the import closure of `Main/BUnivHolds.lean` (ticket item 1): 58 files

Columns: lines at `c9a24cf`; kept lines; class a/b of T2002; d = 2 tokens by regex (`Z2`; `W^2`; `L^2`; `(W*L)^2`; scales `ellT/ellz/scaleM/Meta/tailT`; `log`); `out` = number of direct imports of an RBM2D layer outside `Universality/`; the row of `Universality/Pins.lean` the file serves; the proof ticket of P.3; the key declarations with their line at `c9a24cf`.

| file | lines | kept | cls | Z2 | W^2 | L^2 | (WL)^2 | scales | log | out | row | ticket | key declarations (RBM2D line) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Main/BUniv | 71 | 46 | a | 0 | 0 | 0 | 0 | 0 | 0 | 1 | final assembly | UN-52 | ouRow_of_g1Row:38, bUniv_of_g1Row:42 |
| Main/BUnivHolds | 76 | 62 | a | 0 | 0 | 0 | 0 | 0 | 0 | 1 | final assembly | UN-52 | bUniv_holds:32 |
| Universality/Apriori | 424 | 378 | b | 0 | 8 | 3 | 0 | 13 | 0 | 1 | UnivMainRow (a priori) | UN-18 | - |
| Universality/EMCTE2 | 726 | 631 | b | 0 | 0 | 0 | 0 | 0 | 0 | 2 | EMCTE2Row | UN-18 | eq225_interval:440, emcte2Row:567 |
| Universality/EigenInterlacing | 623 | 592 | a | 0 | 0 | 0 | 0 | 0 | 0 | 1 | GreenCorr (UNGreenCorrAll) | UN-03 | trace_green_submatrix_sub_le:467 |
| Universality/EigenMeasurable | 582 | 479 | a | 0 | 0 | 0 | 0 | 0 | 0 | 0 | GreenCorr (UNGreenCorrAll) | UN-05 | measurable_corrSum:347, measurable_kPoint_eigenvalues:447, integral_kPoint_eq_of_map_eq:459 |
| Universality/FreeConv | 719 | 667 | a | 0 | 0 | 0 | 0 | 0 | 0 | 0 | Infty1Row (Step 1, L32) | UN-06 | freeConv_existsUnique:636, freeConvST:653, isFreeConv51_freeConvST:657 |
| Universality/FreeConvStability | 835 | 788 | b | 0 | 0 | 0 | 0 | 0 | 0 | 1 | Infty1Row (Step 1, L32) | UN-06 | msc_tendsto_mE:240, freeConv_stable_local:765 |
| Universality/GUEInvariance | 1082 | 1004 | b | 0 | 0 | 2 | 2 | 0 | 0 | 0 | Infty1Row (Step 1, L32) | UN-08 | gueP_map_unitary_conj:999 |
| Universality/GUELocalBootstrap | 1042 | 995 | b | 0 | 0 | 0 | 0 | 0 | 0 | 4 | Infty1Row (Step 1, L32) | UN-09 | GUESchurTail:908, schurBud:446, sqrt_le_norm_two_msc_add_z:114 |
| Universality/GUELocalSchur | 673 | 578 | b | 0 | 0 | 12 | 12 | 0 | 0 | 4 | Infty1Row (Step 1, L32) | UN-10 | gueSchurTail:516 |
| Universality/GUEPhase/AuxCarrier | 1183 | 1082 | b | 3 | 0 | 8 | 8 | 0 | 0 | 6 | OURow (OU claims) | UN-25 | auxSizes:54, svar_aux_pos:127, auxT_law:203 |
| Universality/GUEPhase/Bootstrap | 1465 | 595 | b | 59 | 4 | 15 | 5 | 4 | 0 | 5 | OURow (OU claims) | UN-26 | SBgue:55, primBilGUE:152, primRhsGUE:157 |
| Universality/GUEPhase/BootstrapAt | 855 | 754 | b | 2 | 0 | 0 | 0 | 0 | 0 | 3 | OURow (OU claims) | UN-26 | UnifDetDomAt:532, eventually_size_rpow_le_of_neg:536, stochDomAt_of_forall_highProbAt:543 |
| Universality/GUEPhase/BoundsA | 884 | 746 | b | 11 | 0 | 0 | 0 | 0 | 0 | 2 | OURow (OU claims) | UN-33 | Bounds_path:436, pathBounds_of_forall_highProbAt:751, HC:623 |
| Universality/GUEPhase/Drift | 2184 | 2093 | b | 36 | 1 | 18 | 18 | 0 | 0 | 2 | OURow (OU claims) | UN-35 | condExp_loop_drift_gue:2052, oneStepEnvelopeGUE:1485, gueH_succ:1656 |
| Universality/GUEPhase/DuhamelA | 2355 | 2052 | b | 72 | 8 | 0 | 0 | 0 | 0 | 5 | OURow (OU claims) | UN-37 | Duhamel_vGue_le:226, Duhamel_frobSq_loopCut_le:393, DuhamelLoopCut:384 |
| Universality/GUEPhase/DuhamelB | 1344 | 1064 | b | 11 | 0 | 0 | 0 | 0 | 0 | 3 | OURow (OU claims) | UN-38 | DuhamelPhi:178, Duhamelv:182, DuhamelVp:186 |
| Universality/GUEPhase/DuhamelC | 1645 | 1543 | b | 25 | 0 | 0 | 0 | 0 | 3 | 3 | OURow (OU claims) | UN-40 | gueGrid_loop_duhamel:1507 |
| Universality/GUEPhase/EntryDet | 1362 | 837 | b | 12 | 9 | 26 | 11 | 1 | 8 | 1 | OURow (OU claims) | UN-30 | stable_mix:102, mix_offdiag_det:278, mix_diag_det:296 |
| Universality/GUEPhase/EntryGrid | 1042 | 925 | b | 5 | 0 | 1 | 0 | 0 | 0 | 1 | OURow (OU claims) | UN-43 | gueGrid_entry_bound:830, map_gueH_eq_mixMat:453, EntryGrid_var:409 |
| Universality/GUEPhase/EntryTail | 1675 | 1519 | b | 0 | 0 | 7 | 7 | 0 | 2 | 1 | OURow (OU claims) | UN-42 | ouMat_eq_mixMat:82, GUEEntryMix:112, mixSample:142 |
| Universality/GUEPhase/Eq729A | 1430 | 1087 | b | 114 | 10 | 25 | 11 | 0 | 0 | 1 | OURow (OU claims) | UN-44 | eq729F:274, eq729e:722, eq729_duhamel:373 |
| Universality/GUEPhase/Eq729B | 1631 | 1442 | b | 37 | 0 | 0 | 0 | 27 | 0 | 4 | OURow (OU claims) | UN-47 | gueGrid_eq729:541, Eq729B_eq747_of_eq729:1051, Eq729B_eq747_of_inputs:1395 |
| Universality/GUEPhase/Generator | 1199 | 1152 | b | 124 | 21 | 8 | 8 | 0 | 0 | 8 | OURow (OU claims) | UN-28 | genMatGUE:78, egtNGUE:86, loopGenGUE:1123 |
| Universality/GUEPhase/Grid | 888 | 768 | b | 9 | 0 | 0 | 0 | 0 | 0 | 5 | OURow (OU claims) | UN-27 | Pgue:67, gueH:83, map_gueH_zero:560 |
| Universality/GUEPhase/HypA | 1521 | 1032 | b | 74 | 0 | 3 | 3 | 1 | 0 | 2 | OURow (OU claims) | UN-48 | Hyp_grid:892, Hyp_Kt_disc:775, Hyp_interp_bound:212 |
| Universality/GUEPhase/HypB | 1814 | 1063 | b | 72 | 0 | 2 | 2 | 0 | 0 | 3 | OURow (OU claims) | UN-49 | HypB_entry_le:130, HypB_eG_745:240, HypB_eG_746:293 |
| Universality/GUEPhase/KPrim | 909 | 799 | b | 76 | 19 | 22 | 0 | 0 | 0 | 2 | OURow (OU claims) | UN-29 | gueShift:64, kTwoGUE:71, kTwoGUELoop:77 |
| Universality/GUEPhase/LLTransfer | 670 | 467 | b | 6 | 0 | 0 | 0 | 0 | 0 | 0 | OURow (OU claims) | UN-50 | oull_of_pathBounds:429 |
| Universality/GUEPhase/Markov | 1085 | 923 | b | 1 | 0 | 0 | 0 | 0 | 0 | 2 | OURow (OU claims) | UN-32 | gueHasCondSubgaussianMGF_of_frozen:173, gue_highProb_incr_le:848 |
| Universality/GUEPhase/OneLoop | 1848 | 1750 | b | 108 | 23 | 15 | 0 | 0 | 34 | 6 | OURow (OU claims) | UN-46 | gueGrid_expect_oneLoop:1660, ol_map_comb_slice:424, ol_gueH_eq:434 |
| Universality/GUEPhase/PathBounds | 680 | 566 | b | 15 | 0 | 0 | 0 | 3 | 0 | 2 | OURow (OU claims) | UN-50 | gueGrid_pathBounds:437, gueBds_h745E:230, gueBds_h746:328 |
| Universality/GUEPhase/Proc | 1768 | 1440 | b | 86 | 7 | 35 | 3 | 1 | 0 | 4 | OURow (OU claims) | UN-31 | gueDelta:59, gueTent:62, gueInterp:66 |
| Universality/GUEPhase/RandomLayerA | 820 | 549 | b | 4 | 0 | 0 | 0 | 0 | 0 | 4 | OURow (OU claims) | UN-51 | RandomLayer_rows:175, RandomLayer_integral_transfer:76, RandomLayer_measurable_green:67 |
| Universality/GUEPhase/RandomLayerB | 278 | 180 | b | 3 | 0 | 0 | 0 | 3 | 0 | 1 | OURow (OU claims) | UN-51 | g1Row:158 |
| Universality/GUETranslation | 1303 | 1171 | a | 1 | 0 | 0 | 0 | 0 | 0 | 1 | Infty1Row (Step 1, L32) | UN-14 | GUETranslation:59, GUETranslationRow:73, guetranslationRow:1057 |
| Universality/GreenCorr | 810 | 740 | a | 1 | 0 | 0 | 0 | 0 | 0 | 0 | GreenCorr (UNGreenCorrAll) | UN-05 | greenCorrAll:730 |
| Universality/InjSum | 601 | 537 | a | 0 | 0 | 0 | 0 | 0 | 0 | 0 | GreenCorr (UNGreenCorrAll) | UN-03 | InjSum_IsTestFun:28, InjSum_stieltjes:31 |
| Universality/Jak | 952 | 923 | b | 4 | 0 | 5 | 5 | 0 | 8 | 0 | JakUywRow | UN-21 | jakRow:903 |
| Universality/JakKernel | 1121 | 970 | b | 6 | 0 | 47 | 47 | 0 | 0 | 0 | JakUywRow | UN-20 | sum_mass_window_le_im_green:81, sum_mass_window_le_of_im_green_le:135, jakGridGood:155 |
| Universality/JakSpectral | 720 | 597 | b | 9 | 0 | 39 | 39 | 0 | 0 | 0 | JakUywRow | UN-19 | green_sq_apply_self:78, Gsig_apply_self_spectral:110, Gsig_sq_apply_self_spectral:122 |
| Universality/OU | 299 | 197 | b | 0 | 0 | 0 | 0 | 0 | 0 | 0 | pins / OU carrier | UN-02 | ouSample:42, ouSample_law:105, ouMat_zero_map:176 |
| Universality/OUContraction | 1109 | 1055 | a | 0 | 0 | 0 | 0 | 0 | 0 | 0 | pins / OU carrier | UN-17 | - |
| Universality/OUGenerator | 1223 | 1185 | b | 0 | 0 | 0 | 0 | 0 | 0 | 1 | pins / OU carrier | UN-15 | TestFunH:57 |
| Universality/OUHessian | 1242 | 1102 | b | 2 | 0 | 1 | 1 | 0 | 0 | 3 | pins / OU carrier | UN-16 | coordD1:127, coordD2:133, wirtSecond:141 |
| Universality/Pins | 683 | 550 | b | 3 | 0 | 3 | 3 | 0 | 0 | 5 | pins / OU carrier | UN-01 | ouP:53, ouMat:59, stieltjesN:72 |
| Universality/PoissonSmoothing | 1077 | 1034 | a | 0 | 0 | 0 | 0 | 0 | 0 | 0 | GreenCorr (UNGreenCorrAll) | UN-04 | poissonSmooth_error:975 |
| Universality/QUEFlow | 961 | 925 | b | 28 | 17 | 22 | 8 | 6 | 18 | 0 | OURow (OU claims) | UN-52 | - |
| Universality/Step1Band | 1259 | 1163 | b | 1 | 0 | 0 | 0 | 0 | 0 | 0 | Infty1Row (Step 1, L32) | UN-13 | step1Band:1072 |
| Universality/Step1Cond | 947 | 798 | a | 0 | 0 | 0 | 0 | 0 | 0 | 0 | Infty1Row (Step 1, L32) | UN-02 | integral_kPoint_ouMat_cond:261, gueP_prod_map_ouMat:146, Step1Cond_gueMatPairing_eq_integral:302 |
| Universality/Step1RegularityA | 978 | 927 | b | 15 | 30 | 6 | 1 | 48 | 0 | 1 | Infty1Row (Step 1, L32) | UN-10 | - |
| Universality/Step1RegularityB | 906 | 839 | b | 1 | 8 | 7 | 0 | 14 | 0 | 0 | Infty1Row (Step 1, L32) | UN-12 | vOU:68, step1Good_highProb:817 |
| Universality/Step1RegularityGUE | 1221 | 1051 | b | 2 | 0 | 20 | 20 | 2 | 0 | 0 | Infty1Row (Step 1, L32) | UN-11 | guelocalEventHighProb:381, guedetHalf:1109, gueGoodHighProb:1116 |
| Universality/UnivMain | 552 | 474 | b | 2 | 0 | 11 | 11 | 0 | 0 | 3 | UnivMainRow + ClaimRow | UN-24 | univMainRow:449, claimRow:432 |
| Universality/Uyw | 1021 | 972 | b | 4 | 0 | 5 | 5 | 0 | 0 | 0 | JakUywRow | UN-23 | uywRow:914, jakUywRow:951 |
| Universality/UywKernel | 1372 | 1170 | b | 13 | 0 | 41 | 41 | 0 | 0 | 0 | JakUywRow | UN-22 | blockM2:760, blockM2_self:769, blockM2_eq:800 |
| Universality/ZeroModeProfile | 1269 | 566 | b | 28 | 4 | 20 | 9 | 11 | 2 | 2 | OURow (OU claims) | UN-51 | norm_ThetaTilde_sub_le:391, ouTauMax:446, ouTauMax_slack:701 |
| **TOTAL (58 files)** | 61014 | 51594 | | 1085 | 169 | 429 | 280 | 134 | 75 | | | | |

Closure of `Main/BUnivHolds.lean`: 383 files / 260575 lines (Defs 7, Gauss 41, Green 34, Hierarchy 37, Induction 59, Loop 16, Main 9, Path 42, Propagator 56, Evolution 24, Universality 56, root 2); `Universality/` is 56 files of them plus `Main/BUniv*.lean` (2).

## P.2 RBM2D layers outside `Universality/` used by the 58 files, by declaration (ticket item 1)

Method (script deps.py): every non-private declaration of the 325 closure files outside `Universality/` (namespace-qualified; bare name of length >= 4) that occurs as a token outside comments in one of the 58 files; its replacement on RBM3D `main` is looked up **by bare declaration name** (a lead, not a proof of equality of statements: renamed or d-dependent declarations are listed as missing and every found one is re-checked by the proof ticket that uses it).  `found` = same bare name declared on main (first file:line), `missing` = no declaration of that name on main.

| RBM2D module | used | found | missing: names (RBM3D pin / replacement) |
|---|---|---|---|
| Defs/Block | 7 | 5 | card_sbSupport->flucVanish_card_sbSupport (Green/FlucVanish.lean:1079), sbSupport->flucVanish_sbSupport (Green/FlucVanish.lean:1070) |
| Defs/Dist | 1 | 0 | zdist2 |
| Defs/Domination | 6 | 6 | - |
| Defs/Model | 18 | 6 | BlockIndex, Eblk_conjTranspose, Eblk_mul_Eblk, Epaper->Eblk (merged), Epaper_conjTranspose, Spaper->svarF (Gauss/FineModel.lean:47), Spaper_indicator, Spaper_transpose, mem_Iblk, sum_Eblk, sum_Epaper, sum_Spaper_row |
| Defs/Semicircle | 10 | 5 | Meta->Sizes.Bctl (Defs/Sizes.lean:214), ellz->ellT (Defs/Params.lean:31), eq_inv_sqrt_mul_spectralZ, msc_eq_sqrt_mul_spectralM, zztE_quant |
| Defs/StochDom | 11 | 11 | - |
| Delocalization | 4 | 1 | green_apply_self, green_eq_spectral, im_green_apply_self |
| Endpoints | 16 | 2 | BUniv->UNBUniv (probe), IsOrthoEigenbasis, QDiff->MA, admissible_witnessSizes->sz0_admissible, gueP->gueP (probe), gueVar->gueVar (probe), kPoint->kPoint (probe), locSC->UNLocAvgBand (probe; MA freeze), mSC_eq_msc, profile, queBad->queBadMat (probe), trGEGE, window->queWindow (probe), witnessSizes->RBM.Gauss.SizesInst.sz0 (Defs/Sizes.lean checks) |
| Evolution/Defs | 2 | 0 | MLExpConcl->UNMLOut (STExp2), expLoopErr |
| Evolution/MLExpVocab | 4 | 0 | MLExpVocab_im_le_one, bandwidth, sizeTendsto, sizes |
| Evolution/XiBounds | 4 | 0 | cProp5, cShortRow, xiMat, xiRowBoundShort |
| Gauss/Domination | 3 | 3 | - |
| Gauss/Envelope | 5 | 1 | hasDerivAt_line, hasDerivAt_lineInverse, isHermitian_add_realSmul, norm_green_le |
| Gauss/GreenDerivative | 1 | 1 | - |
| Gauss/GreenTimeCont | 1 | 1 | - |
| Gauss/LinearForm | 4 | 4 | - |
| Gauss/LoopCoordinateDerivative | 4 | 4 | - |
| Gauss/LoopCoordinateSecondDerivative | 3 | 3 | - |
| Gauss/LoopDerivative | 1 | 1 | - |
| Gauss/LoopEnvelope | 5 | 5 | - |
| Gauss/LoopFlowCoordinateChain | 1 | 1 | - |
| Gauss/LoopInitialValueScalar | 1 | 1 | - |
| Gauss/LoopSampleCont | 2 | 2 | - |
| Gauss/LoopTimeCont | 3 | 3 | - |
| Gauss/Model | 47 | 39 | Xmat_apply, coordinateMatrix_apply, gvar_diag, gvar_offDiag, size_eq, svar_cast_eq_Spaper, svar_diag, svar_diag_pos |
| Gauss/SpectralAlgebra | 4 | 4 | - |
| Gauss/SpectralDerivative | 1 | 1 | - |
| Gauss/SpectralWindow | 6 | 4 | spectralM, spectralZ |
| Gauss/Stein | 1 | 1 | - |
| Gauss/SteinMatrix | 2 | 1 | update |
| Green/CondRow | 1 | 1 | - |
| Green/EntryBlock | 12 | 4 | Sblk2, Sblk2_eq_svar, Sblk2_nonneg, inv_W2_le_maxLoopPM, stable_relabel, sum_Sblk2_col, sum_Sblk2_row, sum_sum_Sblk2_le_maxLoopPM |
| Green/EntryCore | 16 | 16 | - |
| Green/EntryDom | 1 | 1 | - |
| Green/Eq45Small | 1 | 1 | - |
| Green/FlucAvg | 2 | 2 | - |
| Green/FlucIter | 3 | 3 | - |
| Green/FlucIterHigh | 1 | 1 | - |
| Green/GreenDeriv | 5 | 5 | - |
| Green/IBP | 1 | 0 | IBP_sum_svar_row |
| Green/IBPPoly | 1 | 1 | - |
| Green/LDE | 2 | 2 | - |
| Green/LDEQuad | 4 | 4 | - |
| Green/LDEQuadInst | 2 | 2 | - |
| Green/LDEQuadMom | 2 | 2 | - |
| Green/LDEQuadT | 4 | 4 | - |
| Green/Minor | 3 | 3 | - |
| Green/MinorDiff | 1 | 1 | - |
| Green/Pins | 7 | 3 | bandwidth, sizeTendsto, size_eq, sizes |
| Green/Stability | 3 | 1 | Kstab2, eventually_Kstab2_mul_rpow_le |
| Hierarchy/ContractionCutWords | 5 | 5 | - |
| Hierarchy/ContractionDirections | 3 | 3 | - |
| Hierarchy/ContractionDrift | 1 | 1 | - |
| Hierarchy/ContractionEdgeSplits | 4 | 4 | - |
| Hierarchy/ContractionPairSplits | 3 | 3 | - |
| Hierarchy/ContractionPositionLoopBridge | 3 | 3 | - |
| Hierarchy/ContractionSecondDerivativePositionSum | 5 | 5 | - |
| Hierarchy/ContractionSecondLoop | 1 | 1 | - |
| Hierarchy/ContractionSecondLoopSameEdge | 1 | 1 | - |
| Hierarchy/ContractionSecondLoopSameEdgeCut | 2 | 2 | - |
| Hierarchy/ContractionSecondLoopSameEdgeWord | 1 | 1 | - |
| Hierarchy/ContractionSum | 2 | 2 | - |
| Hierarchy/ContractionUnused | 2 | 2 | - |
| Hierarchy/Loops | 12 | 5 | Gsig_conjTranspose, Gsig_false, Gsig_true, gloopProd_append, gloopProd_cons, gloopProd_nil, gloop_two |
| Hierarchy/Operations | 3 | 1 | cutGlue_split, length_cutGlue |
| Hierarchy/OperationsPair | 5 | 5 | - |
| Hierarchy/WardResolvent | 2 | 2 | - |
| Induction/AltEnd | 1 | 0 | log_nonneg |
| Induction/AzumaProxyN | 1 | 0 | with |
| Induction/B45 | 1 | 0 | with |
| Induction/BcalEDecay | 1 | 1 | - |
| Induction/ConArgDet | 1 | 1 | - |
| Induction/Defs | 3 | 1 | InitLK, MLConcl->UNMLOut (probe; ST-6) |
| Induction/GridDriftN | 1 | 0 | sizes |
| Induction/GridGoodN | 4 | 0 | bandwidth, sizeTendsto, size_eq, sizes |
| Induction/LocalFormCalc | 1 | 1 | - |
| Induction/LocalFormCuts | 1 | 0 | zero |
| Induction/LoopC2N | 1 | 1 | - |
| Induction/PerTimeCalc | 3 | 3 | - |
| Induction/Split | 8 | 8 | - |
| Induction/Step1 | 1 | 0 | step1 |
| Induction/Step3 | 1 | 0 | step3 |
| Induction/Step45 | 2 | 0 | step4, step5 |
| Loop/KBound | 1 | 0 | Kbound_prec_uncond |
| Loop/Kcal | 8 | 5 | Kcal->STKloop/Kloop (Loop/*, Induction/Defs), Kgen->STKloop, mSig |
| Main/Endpoints | 5 | 0 | QDiff_holds, QUE_holds, locSC_holds, p7ExpOut_holds, p7Out_holds |
| Main/QUEFromQDiff | 1 | 0 | QUE_of_QDiff |
| Main/ZRescale | 8 | 0 | ZRescale_blockMat_Epaper, ZRescale_blockMat_mul, ZRescale_green_smul_mul, ZRescale_gsig_block, ZRescale_lemT_pos, ZRescale_rpow_neg_half, ZRescale_trace_block, zRange |
| Path/Azuma | 1 | 1 | - |
| Path/Bootstrap | 1 | 0 | firstHit_eq_of_below |
| Path/DriftLip | 1 | 1 | - |
| Path/GoodEvent | 5 | 0 | GoodEvent_gridStep_nonneg, GoodEvent_gridTime_le, GoodEvent_gridTime_mono, GoodEvent_gridTime_zero, GoodEvent_measurable_gloop |
| Path/Kernel | 1 | 1 | - |
| Path/Markov | 3 | 3 | - |
| Path/OneStep | 1 | 1 | - |
| Path/PerTime | 4 | 4 | - |
| Path/Scales | 4 | 3 | scaleM->Sizes.Bctl |
| Path/ScalesBridge | 1 | 0 | kloop_Mt_eq |
| Path/Step2Props | 6 | 4 | InitLocal, pmLoop |
| Path/Step2Vocab | 4 | 4 | - |
| Path/StepDecomp | 3 | 3 | - |
| Path/Stop | 4 | 4 | - |
| Path/Walk | 4 | 4 | - |
| Propagator/Basic | 9 | 9 | - |
| Propagator/Bounds | 1 | 1 | - |
| Propagator/CombesThomasFixedGap | 1 | 0 | norm_Theta_apply_le_two_geometric |
| Propagator/FiniteDiff | 1 | 0 | norm_Theta_sub_le_log |
| Propagator/LogIntegral | 1 | 1 | - |
| **TOTAL** (108 modules) | 415 | 284 | 131 missing by name |

## P.3 Split table into UN proof tickets (ticket item 6)

Rule: consecutive groups in dependency order, estimated lines = RBM2D kept lines plus the adjustment named in the statements column (all adjustments are estimates, not measured: `Pins` +350 new pins, GreenCorr +100 dilation sequences, `Step1RegularityA` -577 because `(G_bound_ave)` already holds with `∩_z` inside the probability (T2001b), `Step1RegularityB` +500 the density of `msc` for every bulk `E`, `JakSpectral` +300 the `d >= 3` weights, UN-07 new), cap 1500, files above the cap split in equal halves, final assembly (258 lines) merged into the last ticket.  **Count: 52 tickets, 53614 estimated lines (min 724, mean 1031, max 1455); 24 outside the GUE phase, 28 for the GUE phase (`Universality/GUEPhase/*`, `ZeroModeProfile`, `QUEFlow`).**  Sensitivity to the cap: 52 (cap 1500), 55 (1300), 64 (1000); at the mean ticket size of the T2134 design (885 lines) the estimate is 61.  Against DECISIONS §9 O2 (25 / 40 / 50): **above 50 under every rule.**

| id | group: RBM3D/Universality files (RBM2D kept lines) | statements | RBM2D sources (file: declaration:line at c9a24cf) | deps | est | role |
|---|---|---|---|---|---|---|
| UN-01 | pins+vocab: Pins(550) | RBM3D/Universality/Pins.lean: vocabulary (gueP, kPoint, UNModel, ouMat...), the pins of the probe (UNBUniv, UNL32, UNCore rows, UNOUQUE...), arithmetic lemmas; registry entries in Test/Axioms.lean (borrowed: UNL32) | Pins: ouP:53, ouMat:59; Pins: L32:156, GUELocal:189, OUQUE:206, EMCTE2:288, Jak:313, Uyw:331, GreenCorr:359; Endpoints.lean: BUniv:209, kPoint:202 | merged MD, StochDomAt; probe T2162Pins | 900 | prover-hard |
| UN-02 | OU carrier + conditioning: OU(197), Step1Cond(798) | OU marginal law (ouSample_law, ouMat_zero_map) on the abstract UNModel; conditioning on H (integral_kPoint_ouMat_cond), GUE stationarity, rescaling, counting | OU: ouSample:42, ouSample_law:105; Step1Cond: integral_kPoint_ouMat_cond:261, gueP_prod_map_ouMat:146 | UN-01 | 995 | prover |
| UN-03 | spectral: interlacing + inj. sums: EigenInterlacing(592), InjSum(537) | Cauchy interlacing, Stieltjes corollary; injective-sum decomposition, eta-monotonicity of eta Im m | EigenInterlacing: trace_green_submatrix_sub_le:467; InjSum: InjSum_IsTestFun:28, InjSum_stieltjes:31 | UN-01 | 1129 | prover |
| UN-04 | Poisson smoothing: PoissonSmoothing(1034) | Poisson-kernel smoothing of C_c^inf test functions; poissonSmooth_error | PoissonSmoothing: poissonSmooth_error:975 | UN-03 | 1034 | prover |
| UN-05 | GreenCorr + measurability: GreenCorr(740), EigenMeasurable(479) | greenCorrAll (UNGreenCorrAll, with dilation sequences r_n in [a,b]); Courant-Fischer/Weyl, measurable_kPoint_eigenvalues | GreenCorr: greenCorrAll:730; EigenMeasurable: measurable_corrSum:347, measurable_kPoint_eigenvalues:447 | UN-03, UN-04 | 1319 | prover-hard |
| UN-06 | free convolution (band): FreeConv(667), FreeConvStability(788) | existence/uniqueness of [32] (2.5), IsFreeConv32 bridge; stability near the semicircle (exact route m = msc) | FreeConv: freeConv_existsUnique:636, freeConvST:653; FreeConvStability: msc_tendsto_mE:240, freeConv_stable_local:765 | UN-01 | 1455 | prover-hard |
| UN-07 | free convolution of a regular density (NEW):  | NEW (no RBM2D source): |rho_{nu boxplus sc_t}(E) - rho_nu(E)| <= C t for nu with UNDens-regular density; needed only for BA consumption of UNCore | none (new work) | UN-06 | 800 | prover-max |
| UN-08 | GUE unitary invariance: GUEInvariance(1004) | gueP_map_unitary_conj: the GUE law is invariant under unitary conjugation, on Omega d L W with N=(WL)^d | GUEInvariance: gueP_map_unitary_conj:999 | UN-01 | 1004 | prover |
| UN-09 | GUE local law: bootstrap: GUELocalBootstrap(995) | GUELocal_of_tail: deterministic bootstrap from the Schur tail | GUELocalBootstrap: GUESchurTail:908, schurBud:446 | UN-01 | 995 | prover-hard |
| UN-10 | GUE local law: Schur tail + Step1 local event: GUELocalSchur(578), Step1RegularityA(927) | gueSchurTail; Step1RegularityA reduced to the tracial law from the block average (T2001b puts ∩_z inside the probability: the RBM2D grid/interpolation is not needed) = UNTrLocalBandRow; UNNormBandRow (entry event |h_xy| <= 1, |lambda| <= N) | GUELocalSchur: gueSchurTail:516 | UN-09, MA locSC | 928 | prover-hard |
| UN-11 | Step 1: GUE side regularity: Step1RegularityGUE(1051) | guelocalEventHighProb, guedetHalf, gueGoodHighProb | Step1RegularityGUE: guelocalEventHighProb:381, guedetHalf:1109 | UN-10, UN-05 | 1051 | prover-hard |
| UN-12 | Step 1: regularity of V, free-conv density; density of msc: Step1RegularityB(839) | UNStep1Good (tau_s <= c*d, floor W^{-2d}); UNDensBandRow: Im msc bounds, Lipschitz, limit (un_dens_msc_zero at E=0 is in the probe) | Step1RegularityB: vOU:68, step1Good_highProb:817 | UN-05, UN-06, UN-10 | 1339 | prover-max |
| UN-13 | Step 1: Step1Band: Step1Band(1163) | step1Band: k-point functional of H_{t*} vs GUE at energy 0 with dilated test function (L32 input) | Step1Band: step1Band:1072 | UN-02, UN-11, UN-12 | 1163 | prover-hard |
| UN-14 | GUE translation + Infty1Row: GUETranslation(1171) | GUETranslation (energy 0 -> E); UNInfty1Row assembled | GUETranslation: GUETranslation:59, GUETranslationRow:73 | UN-08, UN-11, UN-13 | 1321 | prover-hard |
| UN-15 | OU generator: OUGenerator(1185) | second-order Gaussian interpolation identity d/dt E Phi(H_t) = -1/2 e^{-t} sum S deg_{ab} deg_{ba} (centred Gaussian model) | OUGenerator: TestFunH:57 | UN-02 | 1185 | prover |
| UN-16 | OU Hessian: OUHessian(1102) | coordinate/Wirtinger derivatives, centred-variance Hessian, paperL1Kernel/L2Kernel bridges to L1t, L2t | OUHessian: coordD1:127, coordD2:133 | UN-15 | 1102 | prover |
| UN-17 | OU contraction: OUContraction(1055) | centred contraction of the Wirtinger Hessian, bound by L1, L2 | none (new work) | UN-16 | 1055 | prover |
| UN-18 | EMCTE2 + a priori: EMCTE2(631), Apriori(378) | UNEMCTE2Row (eq225_interval); UNApriori from the tracial law (Meta replaced by Bctl) | EMCTE2: eq225_interval:440, emcte2Row:567 | UN-15, UN-17, UN-04 | 1009 | prover-hard |
| UN-19 | Jak spectral + bad event: JakSpectral(597) | spectral expansion of the y-term, blockM (2d+1 weights: unMy_eq, unBadY_subset, unBadY_measure_le are proved in the probe) | JakSpectral: green_sq_apply_self:78, Gsig_apply_self_spectral:110 | UN-01 | 897 | prover-hard |
| UN-20 | Jak kernel: JakKernel(970) | covering lemma, single-scale grid event, jak_pointwise_good/crude | JakKernel: sum_mass_window_le_im_green:81, sum_mass_window_le_of_im_green_le:135 | UN-19 | 970 | prover-hard |
| UN-21 | Jak: Jak(923) | jakRow: UNJak at c' = c*d/30 (P(B) binds), C = 3nf+16 to be redone | Jak: jakRow:903 | UN-20, GUE-phase claims (pin) | 923 | prover-hard |
| UN-22 | Uyw kernel: UywKernel(1170) | pair kernel (blockM2, spectral expansion, union bound over 2d+1 blocks) | UywKernel: blockM2:760, blockM2_self:769 | UN-19, UN-20 | 1170 | prover-hard |
| UN-23 | Uyw: Uyw(972) | uywRow, jakUywRow: UNUyw and UNJakUywRow | Uyw: uywRow:914, jakUywRow:951 | UN-21, UN-22 | 972 | prover-hard |
| UN-24 | UnivMain + ClaimRow: UnivMain(474) | claimRow (Cn' = Cn + C + 1), UNUnivMainRow | UnivMain: univMainRow:449, claimRow:432 | UN-18, UN-23, UN-05 | 724 | prover-hard |
| UN-25 | GUE phase / OU claims: AuxCarrier(1082) | auxiliary carrier auxSizes, row-chaos (LDE) layer, Hanson-Wright chaos_tail (E0) | AuxCarrier: auxSizes:54, svar_aux_pos:127 | UN-01, merged ST/EK/KL/LW/PT, UNMLOut | 1082 | prover-hard |
| UN-26 | GUE phase / OU claims: Bootstrap(595), BootstrapAt(754) | (7.33)-(7.36) SBgue, primBilGUE/primRhsGUE, abstract ODE bootstrap, eq728G, eq727GE; the bootstraps on the size scale (StochDomAt) | Bootstrap: SBgue:55, primBilGUE:152; BootstrapAt: UnifDetDomAt:532, eventually_size_rpow_le_of_neg:536 | UN-01, UN-25 | 1349 | prover-hard |
| UN-27 | GUE phase / OU claims: Grid(768) | GUE-phase grid carrier Pgue, path gueH, one-time laws (7.25), (7.26), GUEPathBounds | Grid: Pgue:67, gueH:83 | UN-01, UN-26 | 768 | prover-hard |
| UN-28 | GUE phase / OU claims: Generator(1152) | Lemma 2.11 for the GUE profile: genMatGUE, egtNGUE, loopGenGUE | Generator: genMatGUE:78, egtNGUE:86 | UN-01, UN-27 | 1152 | prover-hard |
| UN-29 | GUE phase / OU claims: KPrim(799) | 2-loop primitive kTwoGUE and primitive loops gueK_exists (Theta~ = Theta_T + alpha J) | KPrim: gueShift:64, kTwoGUE:71 | UN-01, UN-28 | 799 | prover-hard |
| UN-30 | GUE phase / OU claims: EntryDet(837) | deterministic entry layer at the mixture profile S_u = aS + b/N (stable_mix, mix_offdiag_det, Ward) | EntryDet: stable_mix:102, mix_offdiag_det:278 | UN-01, UN-29 | 837 | prover-hard |
| UN-31 | GUE phase / OU claims: Proc(1440) | process layer: gueDelta, gueTent, gueStop, gueLproc, frozen processes | Proc: gueDelta:59, gueTent:62 | UN-01, UN-30 | 1440 | prover-hard |
| UN-32 | GUE phase / OU claims: Markov(923) | Pgue Markov toolkit: freezing, conditional sub-Gaussianity, gue_highProb_incr_le | Markov: gueHasCondSubgaussianMGF_of_frozen:173, gue_highProb_incr_le:848 | UN-01, UN-31 | 923 | prover-hard |
| UN-33 | GUE phase / OU claims: BoundsA(746) | unfreezing of the random layer: Bounds_path | BoundsA: Bounds_path:436, pathBounds_of_forall_highProbAt:751 | UN-01, UN-32 | 746 | prover-hard |
| UN-34 | GUE phase / OU claims: Drift#1/2(2093) | oneStepEnvelopeGUE, condExp_loop_drift_gue | Drift: condExp_loop_drift_gue:2052, oneStepEnvelopeGUE:1485 | UN-01, UN-33 | 1046 | prover-hard |
| UN-35 | GUE phase / OU claims: Drift#2/2(2093) | oneStepEnvelopeGUE, condExp_loop_drift_gue | Drift: condExp_loop_drift_gue:2052, oneStepEnvelopeGUE:1485 | UN-01, UN-34 | 1046 | prover-hard |
| UN-36 | GUE phase / OU claims: DuhamelA#1/2(2052) | loop Duhamel tail I: (7.38)/(7.43) variance, one-step decomposition | DuhamelA: Duhamel_vGue_le:226, Duhamel_frobSq_loopCut_le:393 | UN-01, UN-35 | 1026 | prover-hard |
| UN-37 | GUE phase / OU claims: DuhamelA#2/2(2052) | loop Duhamel tail I: (7.38)/(7.43) variance, one-step decomposition | DuhamelA: Duhamel_vGue_le:226, Duhamel_frobSq_loopCut_le:393 | UN-01, UN-36 | 1026 | prover-hard |
| UN-38 | GUE phase / OU claims: DuhamelB(1064) | Duhamel II: dyadic stopping levels + Azuma | DuhamelB: DuhamelPhi:178, Duhamelv:182 | UN-01, UN-37 | 1064 | prover-hard |
| UN-39 | GUE phase / OU claims: DuhamelC#1/2(1543) | Duhamel III: gueGrid_loop_duhamel | DuhamelC: gueGrid_loop_duhamel:1507 | UN-01, UN-38 | 771 | prover-hard |
| UN-40 | GUE phase / OU claims: DuhamelC#2/2(1543) | Duhamel III: gueGrid_loop_duhamel | DuhamelC: gueGrid_loop_duhamel:1507 | UN-01, UN-39 | 771 | prover-hard |
| UN-41 | GUE phase / OU claims: EntryTail#1/2(1519) | probabilistic half of Lemma 4.1 at the mixture profile: GUEEntryMix | EntryTail: ouMat_eq_mixMat:82, GUEEntryMix:112 | UN-01, UN-40 | 759 | prover-hard |
| UN-42 | GUE phase / OU claims: EntryTail#2/2(1519) | probabilistic half of Lemma 4.1 at the mixture profile: GUEEntryMix | EntryTail: ouMat_eq_mixMat:82, GUEEntryMix:112 | UN-01, UN-41 | 759 | prover-hard |
| UN-43 | GUE phase / OU claims: EntryGrid(925) | grid form of Lemma 4.1: gueGrid_entry_bound | EntryGrid: gueGrid_entry_bound:830, map_gueH_eq_mixMat:453 | UN-01, UN-42 | 925 | prover-hard |
| UN-44 | GUE phase / OU claims: Eq729A(1087) | (7.29) at t0, first half: 2-loop algebra, Duhamel in expectation | Eq729A: eq729F:274, eq729e:722 | UN-01, UN-43 | 1087 | prover-hard |
| UN-45 | GUE phase / OU claims: OneLoop#1/2(1750) | Lemma 5.15 for the GUE-phase grid: gueGrid_expect_oneLoop (log L tokens: d>=3 form) | OneLoop: gueGrid_expect_oneLoop:1660, ol_map_comb_slice:424 | UN-01, UN-44 | 875 | prover-max |
| UN-46 | GUE phase / OU claims: OneLoop#2/2(1750) | Lemma 5.15 for the GUE-phase grid: gueGrid_expect_oneLoop (log L tokens: d>=3 form) | OneLoop: gueGrid_expect_oneLoop:1660, ol_map_comb_slice:424 | UN-01, UN-45 | 875 | prover-max |
| UN-47 | GUE phase / OU claims: Eq729B(1442) | (7.29) second half, (7.47) step: gueGrid_eq729, Eq729B_eq747_of_inputs | Eq729B: gueGrid_eq729:541, Eq729B_eq747_of_eq729:1051 | UN-01, UN-46 | 1442 | prover-hard |
| UN-48 | GUE phase / OU claims: HypA(1032) | (7.45)G, (7.46)G I: deterministic inputs, Hyp_grid | HypA: Hyp_grid:892, Hyp_Kt_disc:775 | UN-01, UN-47 | 1032 | prover-hard |
| UN-49 | GUE phase / OU claims: HypB(1063) | (7.45)G, (7.46)G II: pathwise assembly | HypB: HypB_entry_le:130, HypB_eG_745:240 | UN-01, UN-48 | 1063 | prover-hard |
| UN-50 | GUE phase / OU claims: LLTransfer(467), PathBounds(566) | oull_of_pathBounds (OULL moment bound); gueGrid_pathBounds, gueBds_h745E/h746 | LLTransfer: oull_of_pathBounds:429; PathBounds: gueGrid_pathBounds:437, gueBds_h745E:230 | UN-01, UN-49 | 1033 | prover-hard |
| UN-51 | GUE phase / OU claims: RandomLayerA(549), RandomLayerB(180), ZeroModeProfile(566) | section 7.2 random layer rows S1-S6, Lemma 2.8 transfer (z,t) <-> (E',t1); g1Row: OULL, OUEq747 from the ML outputs (UNMLOut); profile S~, Theta~, OULL/OUEq747 interface, ouRow_of_pins; oscillation of Theta~ at d>=3 from Prop8ZeroMode (no log L) | RandomLayerA: RandomLayer_rows:175, RandomLayer_integral_transfer:76; RandomLayerB: g1Row:158; ZeroModeProfile: norm_ThetaTilde_sub_le:391, ouTauMax:446 | UN-01, UN-50 | 1295 | prover-max |
| UN-52 | GUE phase / OU claims + final assembly: QUEFlow(925), Main/BUniv(46), Main/BUnivHolds(62) | g2bRow: OUQUE for H_t from (7.47) at the QUE scale, Markov step; FINAL: un_bUniv_of_rows (UNBUniv from the rows), instances, connection to RBM3D/Endpoints.lean (MA freeze), registry cleanup of the UN pins | BUniv: ouRow_of_g1Row:38, bUniv_of_g1Row:42; BUnivHolds: bUniv_holds:32 | UN-01, UN-51, all UN, MA | 1183 | prover-max |

External gates: every ticket may use the merged MD, PT, KL, EK, ST-1 declarations; the GUE-phase tickets UN-25 .. UN-52 consume `UNMLOut` (ST-6/MA pin to be frozen) only in UN-51 (`RandomLayerB`) and use the d >= 3 propagator facts `prop5to8_holds` (Propagator/Prop6Hold.lean:433), `Prop8ZeroMode` (Propagator/Pins.lean:87); the BA consumption needs UN-07 and BA-D1.

## P.4 The pins of the probe `RBM3D/Probe/T2162Pins.lean` (branch `t/T2162`): sources, consumers, registry, checklist (DECISIONS §29 items (5)-(7), §45 O2)

(5) union over `z` inside / outside the probability, per time vs uniform in time; (6) parameter lower bounds from `(eq:WO)` and `SizeTendsto` written into the hypotheses; (7) the scale of the consumer.  "extreme" = the extreme input tried (compiled instance or lemma in the probe, section 7).

| pin (probe) | RBM2D source (c9a24cf) | consumer (RBM2D c9a24cf) | registry | (5) | (6) | (7) | extreme input tried |
|---|---|---|---|---|---|---|---|
| UNBUniv | Endpoints.lean:209 `BUniv`; T2001_BUniv `bd95cc9:RBM3D/Probe/T2001Endpoints.lean:230` | Main/BUnivHolds.lean:32 | owed | - | `Admissible` (WO, `N -> infty`, W >= N^c) | `kPoint` scale `N^{-1}` | `E = +-(2-kappa)`: `un_rhoSC_edge` equality; `k = 0`: `unUnivDilAt_zero` |
| UNUnivDilAt (dilated form) | Pins.lean:170-174 (L32 conclusion) | GUETranslation.lean:827 | owed | - | - | `rho_n` dilation | `k = 0`; `rho = rho_sc(E)` gives UNBUniv: `unBUniv_diff_eq` |
| UNL32 | Pins.lean:156 `L32` | GUETranslation.lean:827 (`hL32 d hd sigma sigma (1/2) (min kappa 1/960) 2 2 ...`) | borrowed | - | `Tendsto size` | only `N` | premises at `tau = 1/2` and at the threshold `N = 2^{2/tau}`: `inst_L32_arith_half`, `inst_L32_arith_sharp` |
| UNGUELocal | Pins.lean:189 `GUELocal` | GUETranslation.lean:60, Step1RegularityGUE.lean (hypothesis of `guetranslationRow`) | owed | `∩_z` inside | `Tendsto size` | `N^tau (N Im z)^{-1/2}` | nontrivial only for `Im z > N^{2 tau - 1}` (weak pin, as RBM2D) |
| UNTrLocal | Step1RegularityA.lean:748 `Step1LocalEvent` | Step1RegularityB.lean:339 | owed | `∩_z` inside (T2001b) | `W^tau Bctl`, `Bctl <= W^{-2d} + (N eta)^{-1}`: `un_Bctl_le` | `W^tau` | `inst_Bctl_le` at `eta = 1/100` |
| UNDens | - (new, DECISIONS §11) | Step1RegularityB.lean:228, 470 (`Step1RegularityB_msc_im_ge`: `Im m_sc >= kappa/12`) | structural | - | - | - | `un_dens_msc_zero`: proved at `msc`, `E = 0`, `delta = 1/2` (`9/100 <= Im msc <= 1`, Lipschitz `10000/81`, limit `1/pi`); `rho_sc` lower bound at the edge |
| UNNormBound / UNNormBandRow | Step1RegularityB.lean `Step1RegularityB_eigenvalue_le` (`|lambda| <= N` from the entry event of Step1RegularityA) | Step1RegularityB.lean (via `step1Good_highProb`: `|v_i| <= N^2`, CV = 2) | owed | union over `i` inside | `N^{CV0}`, `CV0 >= 0` (LSY (2.3)) | `N^{CV0+1}` | a deterministic diagonal model with semicircle quantiles plus one eigenvalue `N^10` has the local law and `UNDens` but violates (2.3): the abstract `UNStep1Good` is false without it (not compiled) |
| UNStep1Good | Step1RegularityB.lean:817 `step1Good_highProb` | Step1Band.lean:1037 | owed | union over `x`, `z` inside | `τ_s ≤ 𝔠𝔡` (RBM2D `τ_s ≤ 𝔠`); `UNNormBound` | `N^{-3 tau_s/8}` | `un_step1_floor` at `τ_s = 𝔠𝔡 = 1/60` (`inst_step1_floor`) |
| UNClaim417 / UNClaimAll | Pins.lean:267 `Claim417` | GreenCorr.lean:644 | owed | per `t` | `c' > 0`, `Cn` | `N^{-c'+Cn tau_U}` | `un_claim417_zero` (`n_f = 0`); `un_claim_exponent` at `tau_U = 1/79200` |
| UNApriori | Pins.lean:348 `AprioriImM` | GreenCorr.lean:693 | owed | per `n` | - | `N^eps` | - |
| UNGreenCorr(All) | Pins.lean:359 `GreenCorr` (+ dilation sequences `r_n in [a,b]`, T2162d) | UnivMain.lean:449 | owed | - | `Tendsto size` | `N` | `r = 1` is RBM2D |
| UNInfty1 / UNUnivMain / UNUnivDilAt | Pins.lean:375, 386 | UnivMain.lean:449, GUETranslation.lean:1151 | owed | - | - | - | `k = 0` |
| UNOUQUE | Pins.lean:206 `OUQUE` (`τ = 𝔠/3`, bound `N^{-τ/6}`) | Jak.lean:904 (`jakRow`) | owed | per `(t, E, a)` | `Admissible` in `UNOUClaims` | `W^{-𝔡/15+τ}` | `un_que_params`, `un_que_exponent`; window `un_window_sub` at `lam = W^{-d/2+𝔡}` and `lam = 𝔡⁻¹` |
| UNOUDiag | Pins.lean:218 `OUDiag` | Jak.lean:904 | owed | union over `x` inside | `Admissible` | `N^eps` | - |
| UNEMCTE2 | Pins.lean:288 `EMCTE2` | UnivMain.lean:362 | owed | - | `0 <= B` | `N^eps N^{-1+Cn tau_U}` | `un_emcte2_zero`, `un_not_emcte2_zero_noB` (without `0 <= B` false) |
| UNJak | Pins.lean:313 `Jak` | UnivMain.lean:362 | owed | - | `c'` = `𝔠𝔡/30` | `N^eps N^{1-c'+C tau_U}` | `n_f = 0`: no `i : Fin 0` (vacuous); union bound over `2d+1` blocks: `unBadY_measure_le` |
| UNUyw | Pins.lean:331 `Uyw` | UnivMain.lean:362 | owed | - | as UNJak | `N^{2-c'+C tau_U}` | `un_uyw_one` |
| UNBadY (+ `unBadY_subset`, `unBadY_measure_le`) | Jak.lean:837 / JakSpectral.lean:182-196 (five blocks, weight 1/5) | Jak.lean:837 | proved (theorem) | - | `(eq:WO)` for the window: `un_window_sub` | `W^{-𝔡/6}`, `N^{-1}W^{𝔡/3}` | `badY_zero`: nonempty event at `(3,4,32)` |
| UNQueBand / UNLocAvgBand / UNMLOut | Endpoints.lean `QUE`, `locSC`; Pins.lean:238, 250 `P7Out`, `P7ExpOut` | Step1RegularityA.lean (locSC), ZeroModeProfile.lean:712 (P7; QUE and locSC unused there), GUEPhase/RandomLayerA.lean:738 | owed (MA, ST-6) | `∩_z` inside / sequences | `Admissible`, `STFlow` | `W^tau` | - |

## P.5 Scripts (verbatim)

### inv.py

```
#!/usr/bin/env python3
"""T2162 inventory: RBM2D c9a24cf, import closure of Main/BUnivHolds.lean.
Reads the git archive in r2d/ (made with `git archive c9a24cf RBM2D`), the T2002 portmap for kept lines (0c1330a)."""
import re, os, collections, sys
S=os.path.dirname(os.path.abspath(__file__)); root=S+'/r2d'
files=[]
for dp,_,fs in os.walk(root+'/RBM2D'):
    for f in fs:
        if f.endswith('.lean'): files.append(os.path.relpath(dp+'/'+f,root))
files=sorted(files)
text={f:open(root+'/'+f,encoding='utf-8').read() for f in files}
mod=lambda f:f[:-5].replace('/','.')
fof={mod(f):f for f in files}
imps={f:re.findall(r'^import\s+(RBM2D\.[A-Za-z0-9_.]+)',t,re.M) for f,t in text.items()}
seen=set(); q=collections.deque(['RBM2D/Main/BUnivHolds.lean'])
while q:
    f=q.popleft()
    if f in seen: continue
    seen.add(f)
    for m in imps[f]:
        g=fof.get(m)
        if g and g not in seen: q.append(g)
# kept lines from the T2002 portmap
kept={}
pm=open('/Users/junyin/Lean_proof/RBM3D/docs/reports/T2002-portmap.md',encoding='utf-8').read().split('\n')
sec=None
for l in pm:
    m=re.match(r'### (\w+) -> RBM3D',l)
    if m: sec=m.group(1); continue
    if l.startswith('## '): sec=None
    if sec and l.startswith('| ') and not l.startswith('| RBM2D') and not l.startswith('|---'):
        c=[x.strip() for x in l.strip('|').split('|')]
        try: kept[sec+'/'+c[0]]=(int(c[1]),int(c[2]),c[3])
        except: pass
univ=[f for f in files if f in seen and (f.startswith('RBM2D/Universality/') or re.match(r'RBM2D/Main/BUniv',f))]
tok=[('Z2',r'\bZ2\b'),('W^2',r'(\bW\b|\(W : ℝ\)|\(W : ℂ\)|\(W : ℕ\))\)?\s*\^\s*2\b'),('L^2',r'(\bL\b|\(L : ℝ\)|\(L : ℕ\))\)?\s*\^\s*2\b'),
 ('N=(WL)^2',r'\(W \* L\)\)?\s*\^\s*2|\(\(W \* L\) \^ 2'),('ell_t',r'\bellT\b|\bellz\b|\bell_t\b|\bscaleM\b|\bMeta\b|\btailT\b'),('log L',r'Real\.log|\blog\b|\(1 \+ log')]
def cnt(t): return [len(re.findall(p,t)) for _,p in tok]
rows=[]
tot=[0,0,0]+[0]*len(tok)
print('# file | lines | kept(0c1330a) | Z2 | W^2 | L^2 | N=(WL)^2 | ell_t | logL | outside-Universality direct imports (count)')
for f in univ:
    n=len(text[f].split('\n'))-(1 if text[f].endswith('\n') else 0)
    key=('Universality/' + f[len('RBM2D/Universality/'):]) if f.startswith('RBM2D/Universality/') else 'Main/'+os.path.basename(f)
    k=kept.get(key,(n,None,'?'))[1]
    c=cnt(text[f])
    out=[m for m in imps[f] if not m.startswith('RBM2D.Universality')]
    rows.append((f,n,k,c,out))
    tot[0]+=1; tot[1]+=n; tot[2]+= (k if k and k>0 else 0)
    for i,x in enumerate(c): tot[3+i]+=x
    print(f'{f[6:]} | {n} | {k} | '+' | '.join(map(str,c))+f' | {len(out)}')
print('TOTAL files=%d lines=%d kept=%d tokens(Z2,W^2,L^2,N=(WL)^2,ell_t,logL)=%s'%(tot[0],tot[1],tot[2],tot[3:]))
# closure sizes by layer
lay=collections.Counter(); layl=collections.Counter()
for f in seen:
    parts=f.split('/')
    l=parts[1] if len(parts)>2 else 'root'
    lay[l]+=1; layl[l]+=len(text[f].split('\n'))
print('CLOSURE', len(seen),'files', sum(layl.values()),'lines; by layer:', dict(lay))
# direct outside imports of universality files
outs=collections.defaultdict(set)
for f,n,k,c,o in rows:
    for m in o: outs[m].add(f)
print('DIRECT outside-Universality modules imported by the universality closure files:',len(outs))
import json
json.dump({'rows':[(f,n,k,c) for f,n,k,c,o in rows],'outs':{m:sorted(v) for m,v in outs.items()},'seen':sorted(seen)},open(S+'/inv.json','w'))
```

### deps.py

```
#!/usr/bin/env python3
"""Declaration-level dependencies of the UN closure (58 files) on RBM2D modules outside Universality/,
and their replacement on RBM3D main (by bare declaration name; name equality is a lead, not a proof)."""
import re, os, json, collections, sys
S=os.path.dirname(os.path.abspath(__file__))
inv=json.load(open(S+'/inv.json'))
root=S+'/r2d'
R3='/Users/junyin/Lean_proof/RBM3D-wt/T2162'
declre=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\s+([^\s:({\[⦃]+)')
nsre=re.compile(r'^\s*namespace\s+(\S+)'); endre=re.compile(r'^\s*end\s*(\S*)')
def decls(path):
    out=[]; ns=[]; stack=[]
    for i,l in enumerate(open(path,encoding='utf-8').read().split('\n'),1):
        m=nsre.match(l)
        if m:
            ns.append(m.group(1)); stack.append(('ns',m.group(1))); continue
        m=re.match(r'^\s*section\b(?:\s+(\S+))?',l)
        if m: stack.append(('sec',m.group(1))); continue
        m=endre.match(l)
        if m:
            if stack:
                k,_=stack.pop()
                if k=='ns': ns.pop()
            continue
        m=declre.match(l)
        if m:
            kind,name=m.group(1),m.group(2)
            if 'private' in l.split(kind)[0]: continue
            out.append((kind,name.split('.')[-1],'.'.join(ns+[name]),i))
    return out
# index RBM3D main
idx3=collections.defaultdict(list)
for dp,_,fs in os.walk(R3+'/RBM3D'):
    for f in fs:
        if f.endswith('.lean') and 'Probe' not in dp:
            p=os.path.join(dp,f)
            for kind,bare,full,ln in decls(p):
                idx3[bare].append((full,os.path.relpath(p,R3)+':'+str(ln)))
# RBM2D closure files outside Universality
files=set(inv['seen'])
univ=set(f for f,*_ in inv['rows'])
outside=[f for f in files if f not in univ]
dec2={}
for f in outside:
    dec2[f]=decls(root+'/'+f)
bare2=collections.defaultdict(list)
for f,ds in dec2.items():
    for kind,bare,full,ln in ds:
        if len(bare)>=4: bare2[bare].append((f,full,ln))
tokre=re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*")
used=collections.defaultdict(lambda: collections.defaultdict(set))  # module file -> bare -> users
for uf in univ:
    t=open(root+'/'+uf,encoding='utf-8').read()
    # strip comments
    t=re.sub(r'/-.*?-/','',t,flags=re.S); t=re.sub(r'--.*','',t)
    own=set(b for kind,b,full,ln in decls(root+'/'+uf))
    toks=set()
    for tk in tokre.findall(t):
        toks.add(tk.split('.')[-1])
    for b in toks:
        if b in bare2 and b not in own:
            for (f,full,ln) in bare2[b]:
                used[f][b].add(uf)
mods=collections.defaultdict(lambda:[0,0,0,[]])
rows=[]
for f in sorted(used):
    layer=f.split('/')[1] if f.count('/')>=2 else 'root'
    n=len(used[f]); fnd=[b for b in used[f] if b in idx3]; miss=[b for b in used[f] if b not in idx3]
    rows.append((layer,f,n,len(fnd),len(miss),sorted(miss)))
detail={}
for f in used:
    det={}
    for b,users in used[f].items():
        det[b]={'main':(idx3[b][0][1] if b in idx3 else None),'users':sorted(u[6:-5] for u in users)[:3]}
    detail[f]=det
json.dump({'rows':rows,'detail':detail},open(S+'/deps.json','w'))
bylayer=collections.defaultdict(lambda:[0,0,0,0])
for layer,f,n,fnd,miss,ms in rows:
    bylayer[layer][0]+=1; bylayer[layer][1]+=n; bylayer[layer][2]+=fnd; bylayer[layer][3]+=miss
print('layer | modules used | declarations used | found by name on main | missing by name')
for l,v in sorted(bylayer.items()): print(l,'|',*v,sep=' | ')
print('TOTAL', [sum(v[i] for v in bylayer.values()) for i in range(4)])
if len(sys.argv)>1:
    for layer,f,n,fnd,miss,ms in rows:
        print(f'{f[6:-5]:55s} used={n:4d} found={fnd:4d} missing={miss:4d}')
```

### keydecls.py

```
import re,json,os
S=os.path.dirname(os.path.abspath(__file__))
d=json.load(open(S+'/inv.json'))
out={}
for f,n,k,c in d['rows']:
    t=open(S+'/r2d/'+f,encoding='utf-8').read()
    lines=t.split('\n')
    m=re.search(r'/-!(.*?)-/',t,re.S)
    head=m.group(1) if m else ''
    cands=[]
    for x in re.findall(r'`([A-Za-z_][A-Za-z0-9_.\']*)`',head):
        x=x.split('.')[-1]
        if x not in cands: cands.append(x)
    found=[]
    for x in cands:
        pat=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(theorem|def|lemma|structure|abbrev)\s+(?:[A-Za-z0-9_.]*\.)?'+re.escape(x)+r'(?![A-Za-z0-9_\'])')
        for i,l in enumerate(lines,1):
            if pat.match(l):
                found.append(f'{x}:{i}'); break
        if len(found)>=3: break
    out[f[6:-5]]=found
json.dump(out,open(S+'/keydecls.json','w'))
for k,v in out.items(): print(k,v)
```

### consumers.py

```
import re,os,json
root='r2d/RBM2D'
pins=['L32','GUELocal','OUQUE','OUDiag','OUClaims','Claim417','EMCTE2','Jak','Uyw','GreenCorr','AprioriImM','Infty1','UnivMain','P7Out','P7ExpOut','Infty1Row','UnivMainRow','ClaimRow','EMCTE2Row','JakUywRow','OURow','step1Good_highProb']
files=[]
for dp,_,fs in os.walk(root):
    for f in fs:
        if f.endswith('.lean') and (('/Universality' in dp) or dp.endswith('/Main')):
            files.append(os.path.join(dp,f))
files.sort()
out={}
for p in pins:
    hits=[]
    pat=re.compile(r'(?<![A-Za-z0-9_.\'])'+re.escape(p)+r'(?![A-Za-z0-9_\'])')
    for f in files:
        rel=f[len(root)+1:]
        if rel=='Universality/Pins.lean': continue
        in_c=False
        for i,l in enumerate(open(f,encoding='utf-8').read().split('\n'),1):
            s=l
            if '/-' in s: in_c=True
            if in_c:
                if '-/' in s: in_c=False
                continue
            s=re.sub(r'--.*','',s)
            if pat.search(s) and not re.match(r'\s*(theorem|def|private|lemma)\s+'+re.escape(p)+r'\b',s):
                hits.append(f'{rel}:{i}')
                break
    out[p]=hits
for p,h in out.items(): print(f'{p:20s}', h[0] if h else '-')
```

### exps2.py

```
#!/usr/bin/env python3
"""T2162 additions to the exponent table of (a): the Step-1 range, the N-scale window, the binding exponent of
Jak/Uyw, the orderings R1-R3 that replace the 'only signs matter' remark (1_2:579), exact Fractions, d = 3."""
from fractions import Fraction as F
d=3
rows=[(F(1,6),F(1,10)),(F(1,4),F(1,5)),(F(3,10),F(1,100)),(F(1,6),F(7,5))]
print('c,d | Step1 range tau_s<=cd (sharp 16cd/(3+c)) | floor N^-(2cd) vs target 15tau_s/16 at tau_s=cd | window exps in N [cd/3, d/(3d)) | theta exp cd/6, P(B) exp c(d/15-tQ), c\' | R1 c\'<=a_w=cd/3 | R2 tau_U<=c\'/44 < a_w/2 | sigma at tau_s=cd')
for c,dd in rows:
    assert c*d<1 and dd<F(d,2)
    ts=c*dd; sharp=16*c*dd/(3+c)
    floor=c*(2*dd-ts/8); target=15*ts/16
    aw=c*dd/3; aw_hi=dd/(3*d)
    tQ=dd/30
    th=c*dd/6; pb=c*(dd/15-tQ); cp=min(th,pb)
    tauU=cp/44
    sigma=min(ts/4,(1-ts)/3)
    print(f'{c},{dd} | {ts} ({float(sharp):.5f}) | {float(floor):.5f} >= {float(target):.5f}: {floor>=target} | [{aw}, {aw_hi}) | {th}, {pb}, {cp} | {cp<=aw} | {tauU} < {aw/2}: {tauU<aw/2} | {sigma}')
```

### lsycheck.py

```
#!/usr/bin/env python3
"""T2162: substring checks of the LSY v4 text (arxiv.org/html/1609.09011v4, tags -> alttext, saved as lsy.txt) against the premises of UNL32."""
t=open('lsy.txt').read()
keys=[r'N^{-\delta}\geq g\geq N^{\delta}/N and G\leq N^{-\delta}',                       # Def 2.1: N^delta/N <= g <= N^-delta, G <= N^-delta
      r'c\leq\mathrm{Im}\mbox{ }[m_{V}(E+\mathrm{i}\eta)]\leq C for |E|\leq G and g\leq\eta\leq 10',   # (2.2)
      r'||V||\leq N^{C_{V}}',                                                              # (2.3)
      r'gN^{\sigma}\leq t\leq N^{-\sigma}G^{2}',                                            # (2.8)
      r'\frac{1}{V_{i}-z-tm_{\mathrm{fc},t}(z)}',                                          # (2.5)
      r'\rho_{\mathrm{fc},t}(E):=\lim_{\eta\downarrow 0}\frac{1}{\pi}\mathrm{Im}',          # (2.6)
      r'{\rho_{\mathrm{sc}}(E)}^{k}',                                                     # placeholder (checked below in two spellings)
      'hold also for the compl']                                                           # Remark: complex Hermitian
for k in keys[:6]+keys[7:]: print(k in t, '|', k[:64])
i=t.find('(2.9)'); seg=t[i-900:i+60]
print('(2.9) has rho_fc,t(E)^k on the left and rho_sc(E)^k, p_GOE on the right at the same E:', 'rho_{\\mathrm{fc},t}(E))^{k}' in seg or '\\rho_{\\mathrm{fc},t}(E))^{k}' in seg)
```

### clash.py

```
import re,subprocess,sys
probe=open('/Users/junyin/Lean_proof/RBM3D-wt/T2162/RBM3D/Probe/T2162Pins.lean',encoding='utf-8').read().split('\n')
names=set()
for l in probe:
    m=re.match(r'^(?:noncomputable )?(def|theorem|structure|abbrev) +([^\s:({\[⦃]+)',l)
    if m and not m.group(2).startswith('inst_'): names.add(m.group(2).split('.')[-1])
pat='(def|theorem|structure|abbrev) ('+'|'.join(sorted(names))+r')\b'
r=subprocess.run(['grep','-rnE',pat,'RBM3D'],cwd='/Users/junyin/Lean_proof/RBM3D-wt/T2162',capture_output=True,text=True)
lines=[x for x in r.stdout.split('\n') if x and 'Probe' not in x]
print(len(lines))
for x in lines[:5]: print(x[:140])
print('names checked:',len(names),file=sys.stderr)
```

### split.py (packing function; the manual groups are the rows of P.3)

```
def pack(items,cap):
    units=[]
    for n,l in items:
        if l>cap:
            parts=-(-l//cap)
            for i in range(parts): units.append((f'{n}#{i+1}/{parts}',l//parts))
        else: units.append((n,l))
    bins=[];cur=[];s=0
    for n,l in units:
        if cur and s+l>cap: bins.append((cur,s));cur=[];s=0
        cur.append(n);s+=l
    if cur: bins.append((cur,s))
    return bins
```
