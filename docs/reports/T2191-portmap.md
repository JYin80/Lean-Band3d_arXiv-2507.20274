Prover model: claude-sonnet-5-5

# T2191 portmap (ST-D5: Step 6 of `lem:main_ind`, sub-gate ST-5)

Generated Mon Oct  5 17:29:45 UTC 2026 by the scripts of the appendix (python3, stdlib; RBM2D read at `c9a24cf` through `git show`, RBM2D `HEAD` = `9e0f275`; RBM3D branch `t/T2191`, base `0818c49`).
Companion of `docs/reports/T2191-prove.md` (items 1, 3, 4, 6 of the ticket in full; the prove report has the summaries).  Probe: `RBM3D/Probe/T2191Pins.lean` (branch `t/T2191`).

## P.1 Item 1: inventory of the seven RBM2D files and of `Evolution/Defs.lean:107-145`

### P.1a Sizes, class, public statements, `d = 2` tokens (script `inv.py summary`)
```
file                lines(c9a24cf) kept(c9a24cf) lines(HEAD 9e0f275) kept(0c1330a,T2002) class | public thm/def | occurrences Z2 scaleM ellT "log L" | lines W^2 L^2
Step61                1021        933          939              948     c |   1/1   |    81    10     2    13 |   13   11
MLExpVocab            1349       1213          760              774     c |  60/17  |    37    34     0     0 |   15    6
MLExpHier              731        648          670              673     c |   4/0   |    29     0     0     0 |    0    0
MLExpDuhamel           532        474          448              461     c |  25/0   |    59     0     0     0 |    0    0
MLExpDrift            1673       1545         1597             1614     c |   5/0   |    99    20    26     0 |   27   39
MLExpInv               878        766          815              818     c |  13/2   |   103     0     0     0 |    0    4
MLExpQ                1669       1533         1539             1558     c |  71/5   |   144    60    46    19 |   14    5
TOTAL                 7853       7112         6768             6846     c | 204 public decls
Evolution/Defs.lean:107-145 (oneLoopExpErr, expLoopErr, Step61Concl, DecayLoopPT, MLExpConcl): 219 lines in file, 39 lines in range, kept 32; occurrences Z2=5 W^2=0 L^2=0 scaleM=2 ellT=1 log L=0
```
The ticket's per-file `kept` figures (933, 1213, 648, 474, 1545, 766, 1533) are reproduced exactly by the column `kept(c9a24cf)` = non-blank lines that do not begin with `--` (sum 7112).  The ticket's header figure "6846 lines kept" is the sum of the T2002 column `kept(0c1330a)` (`docs/reports/T2002-portmap.md:375-381`), a different count; the two are not mixed here.  RBM2D `HEAD` is after the dead-code deletion T2274 (`99d6fe0`) and the comment clean-up T2278 (`ec26147`), both of which touch these files.  The ticket's `Z2`, `scaleM`, `ellT`, `log L` columns are reproduced exactly by the occurrence counts of the plain substrings (columns "occurrences"); its `W^2`, `L^2` columns are not reproduced (patterns not given): ours are the regexes `TOK` of the script, counted in lines.

### P.1b `d = 2` tokens with `file:line` (script `inv.py tokens`: occurrences, lines, and the first six lines per token)
```
-- Step61
   Z2      occ   81 lines   72: Step61.lean:66,Step61.lean:71,Step61.lean:115,Step61.lean:121,Step61.lean:130,Step61.lean:139 ...
   W^2     occ   14 lines   13: Step61.lean:84,Step61.lean:133,Step61.lean:144,Step61.lean:190,Step61.lean:246,Step61.lean:264 ...
   L^2     occ   11 lines   11: Step61.lean:32,Step61.lean:447,Step61.lean:633,Step61.lean:642,Step61.lean:646,Step61.lean:651 ...
   scaleM  occ   10 lines   10: Step61.lean:631,Step61.lean:633,Step61.lean:641,Step61.lean:689,Step61.lean:695,Step61.lean:696 ...
   ellT    occ    2 lines    2: Step61.lean:634,Step61.lean:642
   log L   occ   13 lines   13: Step61.lean:37,Step61.lean:38,Step61.lean:447,Step61.lean:452,Step61.lean:479,Step61.lean:480 ...
-- MLExpVocab
   Z2      occ   37 lines   34: MLExpVocab.lean:57,MLExpVocab.lean:62,MLExpVocab.lean:70,MLExpVocab.lean:78,MLExpVocab.lean:79,MLExpVocab.lean:80 ...
   W^2     occ   16 lines   15: MLExpVocab.lean:137,MLExpVocab.lean:396,MLExpVocab.lean:398,MLExpVocab.lean:401,MLExpVocab.lean:404,MLExpVocab.lean:405 ...
   L^2     occ    6 lines    6: MLExpVocab.lean:77,MLExpVocab.lean:402,MLExpVocab.lean:404,MLExpVocab.lean:406,MLExpVocab.lean:411,MLExpVocab.lean:413
   scaleM  occ   34 lines   32: MLExpVocab.lean:97,MLExpVocab.lean:176,MLExpVocab.lean:179,MLExpVocab.lean:397,MLExpVocab.lean:398,MLExpVocab.lean:399 ...
-- MLExpHier
   Z2      occ   29 lines   27: MLExpHier.lean:121,MLExpHier.lean:169,MLExpHier.lean:173,MLExpHier.lean:189,MLExpHier.lean:206,MLExpHier.lean:212 ...
-- MLExpDuhamel
   Z2      occ   59 lines   50: MLExpDuhamel.lean:28,MLExpDuhamel.lean:30,MLExpDuhamel.lean:55,MLExpDuhamel.lean:67,MLExpDuhamel.lean:74,MLExpDuhamel.lean:75 ...
-- MLExpDrift
   Z2      occ   99 lines   88: MLExpDrift.lean:79,MLExpDrift.lean:82,MLExpDrift.lean:97,MLExpDrift.lean:120,MLExpDrift.lean:125,MLExpDrift.lean:135 ...
   W^2     occ   29 lines   27: MLExpDrift.lean:35,MLExpDrift.lean:36,MLExpDrift.lean:244,MLExpDrift.lean:245,MLExpDrift.lean:258,MLExpDrift.lean:294 ...
   L^2     occ   40 lines   39: MLExpDrift.lean:140,MLExpDrift.lean:143,MLExpDrift.lean:156,MLExpDrift.lean:163,MLExpDrift.lean:185,MLExpDrift.lean:259 ...
   scaleM  occ   20 lines   19: MLExpDrift.lean:52,MLExpDrift.lean:922,MLExpDrift.lean:932,MLExpDrift.lean:958,MLExpDrift.lean:968,MLExpDrift.lean:1363 ...
   ellT    occ   26 lines   23: MLExpDrift.lean:923,MLExpDrift.lean:943,MLExpDrift.lean:963,MLExpDrift.lean:973,MLExpDrift.lean:1391,MLExpDrift.lean:1410 ...
-- MLExpInv
   Z2      occ  103 lines   65: MLExpInv.lean:74,MLExpInv.lean:75,MLExpInv.lean:77,MLExpInv.lean:81,MLExpInv.lean:86,MLExpInv.lean:88 ...
   L^2     occ    4 lines    4: MLExpInv.lean:26,MLExpInv.lean:72,MLExpInv.lean:724,MLExpInv.lean:820
-- MLExpQ
   Z2      occ  144 lines  118: MLExpQ.lean:93,MLExpQ.lean:97,MLExpQ.lean:101,MLExpQ.lean:102,MLExpQ.lean:117,MLExpQ.lean:124 ...
   W^2     occ   15 lines   14: MLExpQ.lean:44,MLExpQ.lean:48,MLExpQ.lean:744,MLExpQ.lean:796,MLExpQ.lean:871,MLExpQ.lean:902 ...
   L^2     occ    5 lines    5: MLExpQ.lean:1011,MLExpQ.lean:1012,MLExpQ.lean:1013,MLExpQ.lean:1018,MLExpQ.lean:1020
   scaleM  occ   60 lines   53: MLExpQ.lean:1013,MLExpQ.lean:1017,MLExpQ.lean:1027,MLExpQ.lean:1031,MLExpQ.lean:1032,MLExpQ.lean:1158 ...
   ellT    occ   46 lines   37: MLExpQ.lean:424,MLExpQ.lean:443,MLExpQ.lean:447,MLExpQ.lean:453,MLExpQ.lean:454,MLExpQ.lean:456 ...
   log L   occ   19 lines   19: MLExpQ.lean:50,MLExpQ.lean:54,MLExpQ.lean:57,MLExpQ.lean:423,MLExpQ.lean:424,MLExpQ.lean:428 ...
```

### P.1c Public statements (script `inv.py decls`: `name@line`, `inst_*`/`MLExpVocab_*`/`step61_*` helpers of the pin files included)
```
-- Step61: Step61Pin@843; step61@853
-- MLExpVocab: expErrT@57; expDriftT@62; qDriftT@70; TensorInvariant@78; MLExpHyps@83; ExpDriftBoundConcl@91; ExpHierPin@111; ExpDuhamelPin@124; ExpQDuhamelPin@131; ExpDriftBound@145; ExpInvariant@155; ExpQBound@168; uker_mul_thetaGenMat@190; qop_source@229; hierarchyN_two@239; TensorInvariant.symmetric@249; expErrT_zero@303; mlExp_of_pins@606; mlExpConcl_zero@753; w1Sizes@764; not_bandwidth_W1@772; sizes@794; E@801; size_eq_pow@803; E_bound@809; E_nonconst@817; sizeTendsto@821; bandwidth@830; rangeCond@841; rangeCond_zero@855; tEdge@866; rangeCond_edge@868; tEdge_nonneg@880; tEdge_lt_one@889; E_lt@894; instHyps@909; inst_hier@921; inst_duhamel@939; inst_qduhamel@948; inst_drift@958; inst_inv@968; inst_invtensor@974; inst_invsymm@979; inst_qbound@986; inst_assembly@1002; inst_assemblyEdge@1018; inst_zero@1034; inst_rangeZero@1037; inst_Enonconst@1040; inst_size81@1045; momentDomAt_of_perTime@1067; inst_expErrT_zero@1236; inst_uker_mul_thetaGenMat@1243; inst_qop_source@1249; inst_hierarchyN_two@1277; boolP@1294; inst_momentDomAt_of_perTime@1300; inst_step61_unif@1340
-- MLExpHier: expHierPin@643; inst_expHierPin_pm@677; inst_expHierPin_pp@695; inst_expHierPin_half@713
-- MLExpDuhamel: MLExpDuhamel_ukerMat_eq@50; MLExpDuhamel_hasDerivAt_ukerMat@55; MLExpDuhamel_continuous_ukerMat@67; MLExpDuhamel_sum_update_reindex@75; MLExpDuhamel_Uker_theta@96; MLExpDuhamel_continuousOn_Ugen@174; MLExpDuhamel_ftc@188; MLExpDuhamel_continuousOn_vartheta@279; MLExpDuhamel_continuousAt_Theta_entry@285; MLExpDuhamel_continuousOn_thetaGenMat@294; MLExpDuhamel_continuousOn_thetaSig@303; MLExpDuhamel_continuousOn_Psum@314; MLExpDuhamel_continuousOn_Qop@320; MLExpDuhamel_continuousOn_varthetaDot@329; MLExpDuhamel_hasDerivAt_Qop@367; MLExpDuhamel_continuousOn_qDriftT@387; expDuhamelPin_of_hier@412; expQDuhamelPin_of_hier@423; inst_expDuhamel_pin@466; inst_expQDuhamel_pin@470; inst_expDuhamel_alt@474; inst_expDuhamel_rep@484; inst_expQDuhamel_alt@494; inst_expQDuhamel_rep@504; inst_edge@514
-- MLExpDrift: expDriftBound@1327; inst_expDriftBound@1619; inst_expDriftBound_concl@1628; inst_expDriftBound_edge@1641; inst_expDriftBound_edge_concl@1652
-- MLExpInv: expInvariant@729; inst_expInvariant_alt@753; inst_expInvariant_rep@759; inst_expInvariant_all@765; inst_expInvariant_labels@773; MLExpInv_IsAut@822; MLExpInv_IsAut_addRight@825; MLExpInv_IsAut_neg@829; MLExpInv_IsAut_SB@832; MLExpInv_IsAut_Theta@836; MLExpInv_xi_norm@843; MLExpInv_relabel@849; MLExpInv_relabel_LLf@854; MLExpInv_relabel_avgErr@861; MLExpInv_relabel_integral@868
-- MLExpQ: MLExpQ_update_zero@93; MLExpQ_update_one@97; MLExpQ_Psum_two@101; MLExpQ_vartheta_two@117; MLExpQ_varthetaDot_two@124; MLExpQ_xi_one@139; MLExpQ_thetaSig_two@150; MLExpQ_K_symm@158; MLExpQ_K_colsum@167; MLExpQ_norm_ofReal_lt@176; MLExpQ_Psum_thetaSig@180; MLExpQ_qDrift_eq@199; MLExpQ_sumZero_qDrift@248; MLExpQ_MatInv@278; MLExpQ_VecInv@282; MLExpQ_MatInv_SB@286; MLExpQ_MatInv_Theta@291; MLExpQ_MatInv_mul@303; MLExpQ_VecInv_Psum@318; MLExpQ_TensorInv_vartheta@337; MLExpQ_TensorInv_Qop@347; MLExpQ_TensorInv_T2@358; MLExpQ_TensorInv_add@384; MLExpQ_TensorInv_qDrift@394; MLExpQ_C5@418; MLExpQ_C5_pos@421; MLExpQ_c@424; MLExpQ_c_nonneg@427; MLExpQ_norm_one_sub@435; MLExpQ_norm_Theta@441; MLExpQ_slot_le@462; MLExpQ_sum_norm_row_le_opNorm@471; MLExpQ_K_row_le@482; MLExpQ_Theta_col_le@494; MLExpQ_SB_row_norm@507; MLExpQ_K_decay@513; MLExpQ_vartheta_decay@574; MLExpQ_vartheta_col_le@579; MLExpQ_T2_size@601; MLExpQ_T2_decay@622; MLExpQ_green_comm@700; MLExpQ_spectralZ_im_ne@710; MLExpQ_LLf_false@717; MLExpQ_LKf_false@732; MLExpQ_ward_tf@746; MLExpQ_sum_two_swap@773; MLExpQ_ward_alt@797; MLExpQ_measurable_LLf@822; MLExpQ_integrable_LLf@829; MLExpQ_integrable_LKf@842; MLExpQ_expErrT_eq@849; MLExpQ_integral_LKf_one@859; MLExpQ_Psum_expErr@872; MLExpQ_norm_Psum_expErr@903; MLExpQ_N_poly@939; MLExpQ_absorb@950; MLExpQ_absorb_one@980; MLExpQ_expdecay@993; MLExpQ_scale_facts@1008; MLExpQ_T2@1067; MLExpQ_vartheta_le@1072; MLExpQ_eta_two@1080; MLExpQ_T2_le@1083; MLExpQ_T2_far@1094; MLExpQ_zdist2
```
The pins of RBM2D (the statements this ticket re-pins at `d >= 3`): `expErrT` `MLExpVocab.lean:57`, `expDriftT` `:62`, `qDriftT` `:70`, `ExpHierPin` `:111`, `ExpDuhamelPin` `:124`, `ExpQDuhamelPin` `:131`, `ExpDriftBound` `:145`, `ExpInvariant` `:155`, `ExpQBound` `:168`, `mlExp_of_pins` `:606`; `Step61Pin` `Step61.lean:843`, `step61` `:853`; `expHierPin` `MLExpHier.lean:643`; `expDuhamelPin_of_hier` `MLExpDuhamel.lean:412`, `expQDuhamelPin_of_hier` `:423`; `expDriftBound` `MLExpDrift.lean:1327`; `expInvariant` `MLExpInv.lean:729`; `expQBound` `MLExpQ.lean:1190`; vocabulary `oneLoopExpErr`, `expLoopErr`, `Step61Concl`, `DecayLoopPT`, `MLExpConcl` `Evolution/Defs.lean:107-145`.

### P.1d Paper labels: RBM2D label (`5-6` = `5-6_loop-hierarchy-analysis.tex`, `1-2` = `1-2_intro-results-new.tex`) -> label of this paper

| RBM2D label (file:line in the RBM2D paper) | d >= 3 label (file:line in `paper/tex/`) | in the probe |
|---|---|---|
| `lemma:step6-1` (5-6:1412-1438) | `lem:improve_exp_aver`, `(res_ELK_n=1)` (`6:12-21`) | `STImproveExpAver`, `STExpAvgAt` |
| `ML:exp`, `eq:step6main` (1-2:915-919) | `(Eq:Gtlp_exp)` (`1_2:1210`), `(Eq:Gtlp_exp_flow)` (`1_2:1390-1396`) | `STExp2U`, `STStep6R` |
| `eq:L-Keee` (5-6:85), `LK_SDE` (5-6:133) | `(eq_L-Keee)` (`3_5:73`), `lem:Sol_CalL` (`3_5:133`, the integrated form; the d >= 3 TeX has no label `LK_SDE`) | merged `HierarchyN`; `STExpHier` |
| `Eexpint_K-L` (5-6:1446-1451) | `(Eexpint_K-L)` (`6:3-7`) | `STExpDuhamelZ` |
| `int_K-L+Q2` (5-6:997), `pqthlk` (5-6:972) | `(int_K-L+QE)` (`6:109-116`) | `STExpDuhamelQ`, `STExpQsrc` |
| `eq:LKLKstep6` (5-6:1459) | `(eq:Exp(L-K)1)` (`6:58-62`), `(eq:Exp(L-K)2)` (`6:63-66`) | `STExpLKLKHi`, `STExpDriftLo` |
| `eq:wtGstep6` (5-6:1482) | `(eq:ExpLWn=2)` (`6:83-88`, `lem:LWterm_EXP`), `(eq:ExpLWn=2_smalleta)` (`6:73-79`) | `st6_EGtHi_of_LW` (from `LWtermEXP`), `STExpDriftLo` |
| `eq:step6_improvedexpectation` (5-6:1488) | `(res_ELK_n=1)` and `(eq:EPL-K)` (`6:104-107`) | `STExpWardI`, `STExpWardII` |
| `eq:p_term_step6` (5-6:1494) | `(eq:boundELKQ1)` (`6:121-123`) | `STExpWardI` |
| `commutator_step6` (5-6:1501) | `(eq:boundcommutator)` (`6:126-131`) | `STExpWardI` |
| `lem_+Q` (5-6:939), `jywiiwsoks` (5-6:1029), `kkuuwsaf` (5-6:1039), `kkuuwsaf5` (5-6:1043), `eq:thetadot_bound` | `lem_+Q` (`3_5:1285`), `(eq:Ward_typeP)`/`jywiiwsoks` (`3_5:1264-1271`), `(eq:derv_Theta)` | merged `stQopNorm_holds`, `STMollifierProps`; `STExpWardI` |
| `lem_decayLoop` (5-6:793) | `lem_decayLoop` (`3_5:1126`), `(res_decayLK)` (`3_5:1128`) | merged `STDecayLoopU`; `STExpDriftDecay` |
| `eq:case4_B` (`MLExpInv`) | none: no `Symmetric` hypothesis in the d >= 3 kernel pins | merged `stExpInv_holds` (`Evolution/ExpInv.lean:510`, S5-22a) is not used by Step 6 |
| `eq:double_sum_zero_tensor` (RBM2D `Defs.lean`, 7:119) | none in this paper | -- |

### P.1e Imports of the seven files and their replacements on `main` (script `inv.py imports`: public names of the imported file that the seven files use, and the same name on `main`)
```
RBM2D.Evolution.Defs (used by Step61; 219 lines): used names 8, same name on RBM3D main 0, absent 8
    absent: DecayLoopPT, MLExpConcl, Step61Concl, SumDecayDetPrec, cPrec, expLoopErr, oneLoopExpErr, ratioR
RBM2D.Evolution.XiBounds (used by Step61; 783 lines): used names 4, same name on RBM3D main 0, absent 4
    absent: cProp5, cShortRow, xiMat, xiRowBoundShort
RBM2D.Hierarchy.ContractionSecondLoopSameEdge (used by Step61; 129 lines): used names 1, same name on RBM3D main 1, absent 0
    found: sum_coordinateBlock_trace_pair RBM3D/Hierarchy/ContractionSecondLoop.lean:239
RBM2D.Gauss.LoopFlowCoordinateChain (used by Step61; 216 lines): used names 3, same name on RBM3D main 3, absent 0
    found: Xblock_eq_sum_coordinates RBM3D/Gauss/LoopFlowStein.lean:106; gsigSpectralFlowDeriv RBM3D/Gauss/LoopFlowStein.lean:168; spectralWordDeriv RBM3D/Gauss/LoopFlowStein.lean:185
RBM2D.Gauss.LoopCoordinateDerivativeBounds (used by Step61; 252 lines): used names 0, same name on RBM3D main 0, absent 0
RBM2D.Gauss.LoopInitialValueScalar (used by Step61,MLExpVocab; 119 lines): used names 4, same name on RBM3D main 4, absent 0
    found: initialGreenScalar RBM3D/Gauss/LoopGenerator.lean:436; initialLoopValue_one_edge RBM3D/Gauss/LoopGenerator.lean:450; initialLoopValue_two_edges RBM3D/Gauss/LoopGenerator.lean:487; trace_Eblk_eq_one RBM3D/Gauss/LoopGenerator.lean:431
RBM2D.Gauss.MomentBridge (used by Step61,MLExpVocab; 369 lines): used names 2, same name on RBM3D main 2, absent 0
    found: integrable_abs_evenPow_of_envelope RBM3D/Gauss/DominationAt.lean:314; momentDomAt_of_stochDomAt RBM3D/Gauss/DominationAt.lean:328
RBM2D.Gauss.SteinMatrix (used by Step61; 223 lines): used names 6, same name on RBM3D main 3, absent 3
    found: Sample RBM3D/Gauss/DominationAt.lean:497; law RBM3D/Gauss/DominationAt.lean:500; stein RBM3D/Gauss/DominationAt.lean:559
    absent: update, update_of_ne, update_self
RBM2D.Path.PerTime (used by Step61; 237 lines): used names 4, same name on RBM3D main 4, absent 0
    found: PerTimeDomAt RBM3D/Defs/StochDomAt.lean:105; TimeIcc RBM3D/Defs/StochDomAt.lean:100; perTimeDomAt_iff_forall_section RBM3D/Defs/StochDomAt.lean:213; stochDomAt_of_perTimeDomAt RBM3D/Defs/StochDomAt.lean:249
RBM2D.Induction.HierVocab (used by MLExpVocab; 664 lines): used names 17, same name on RBM3D main 1, absent 16
    found: HierarchyN RBM3D/Induction/HierarchyN.lean:56
    absent: Alternating, KcalDecay, LKf, LLf, LoopGenN, MLExpPin, Psum, Qop ...
RBM2D.Evolution.Bridge (used by MLExpVocab; 461 lines): used names 1, same name on RBM3D main 0, absent 1
    absent: sumDecayDetPrec
RBM2D.Induction.SumZeroQ (used by MLExpVocab; 455 lines): used names 6, same name on RBM3D main 0, absent 6
    absent: SumZeroQ_Psum_Qop, SumZeroQ_Psum_vartheta, SumZeroQ_commutator, SumZeroQ_hasDerivAt_vartheta, SumZeroQ_varthetaDot_eq, qopAlgebra
RBM2D.Induction.QopBounds (used by MLExpVocab; 747 lines): used names 2, same name on RBM3D main 0, absent 2
    absent: qopDecay, qopNorm
RBM2D.Induction.HierarchyN (used by MLExpVocab; 76 lines): used names 1, same name on RBM3D main 0, absent 1
    absent: hierarchyN
RBM2D.Hierarchy.LoopHierarchyCutContinuity (used by MLExpHier; 321 lines): used names 3, same name on RBM3D main 2, absent 1
    found: continuousOn_gloop_any_window RBM3D/Gauss/LoopGenerator.lean:696; norm_gloop_any_window_le RBM3D/Gauss/LoopGenerator.lean:725
    absent: continuousOn_expectedLoopCutRHS
RBM2D.Gauss.LoopGeneratorExpectation (used by MLExpHier; 106 lines): used names 2, same name on RBM3D main 2, absent 0
    found: deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts RBM3D/Gauss/LoopGenerator.lean:312; integrable_samplewiseLoopGeneratorCuts RBM3D/Gauss/LoopGenerator.lean:275
RBM2D.Gauss.LoopExpectationDerivative (used by MLExpHier; 102 lines): used names 1, same name on RBM3D main 1, absent 0
    found: hasDerivAt_integral_gloop_HflowBlock_spectralZ RBM3D/Gauss/LoopFlowStein.lean:810
RBM2D.Loop.TreeRep (used by MLExpHier; 2587 lines): used names 1, same name on RBM3D main 0, absent 1
    absent: isPrimitive_Kcal
RBM2D.Induction.BcalEDecay (used by MLExpDrift; 1314 lines): used names 6, same name on RBM3D main 5, absent 1
    found: far_cutGlueL_or_far_cutGlueR RBM3D/Induction/DecayLoopB.lean:177; mono RBM3D/Green/FlucIter.lean:624; norm_sum_SB_le_left RBM3D/Induction/DecayLoopB.lean:303; norm_sum_SB_le_right RBM3D/Induction/DecayLoopB.lean:346 ...
    absent: BcalEDecay_sum_sum_norm_SB
RBM2D.Induction.KcalDecay (used by MLExpDrift; 913 lines): used names 1, same name on RBM3D main 0, absent 1
    absent: kcalDecay
RBM2D.Path.ScalesBridge (used by MLExpDrift,MLExpQ; 72 lines): used names 3, same name on RBM3D main 0, absent 3
    absent: kloop_Mt_eq, kloop_ellT_eq, kloop_etaT_eq
RBM2D.Gauss.LoopSampleCont (used by MLExpDrift,MLExpQ; 85 lines): used names 4, same name on RBM3D main 4, absent 0
    found: continuous_gloopProd_HflowBlock_sample RBM3D/Gauss/FlowCalculus.lean:341; continuous_gloop_HflowBlock_sample RBM3D/Gauss/FlowCalculus.lean:348; continuous_green_HflowBlock_sample RBM3D/Gauss/FlowCalculus.lean:309; measurable_gloop_HflowBlock_sample RBM3D/Gauss/FlowCalculus.lean:356
RBM2D.Hierarchy.WardResolvent (used by MLExpQ; 193 lines): used names 1, same name on RBM3D main 1, absent 0
    found: sum_gloop_ward_last_div RBM3D/Induction/ConArgDet.lean:312
RBM2D.Gauss.LoopEnvelope (used by MLExpQ; 131 lines): used names 3, same name on RBM3D main 3, absent 0
    found: card_BlockIndex RBM3D/Gauss/FlowCalculus.lean:701; norm_gloop_le_crude RBM3D/Gauss/FlowCalculus.lean:708; norm_matrix_trace_le_card_mul RBM3D/Gauss/FlowCalculus.lean:600
RBM2D.Propagator.Bounds (used by MLExpQ; 86 lines): used names 1, same name on RBM3D main 1, absent 0
    found: norm_Theta_le RBM3D/Propagator/Props4.lean:218
RBM2D.Propagator.Prop5 (used by MLExpQ; 178 lines): used names 1, same name on RBM3D main 0, absent 1
    absent: norm_Theta_apply_le_prop5
```

Replacements (import -> RBM3D file:line on `main`; "absent" names above are renamed or re-derived):

| RBM2D import | RBM3D replacement (file:line) |
|---|---|
| `Evolution/Defs` (`oneLoopExpErr`, `expLoopErr`, `Step61Concl`, `MLExpConcl`, `DecayLoopPT`, `cPrec`, `ratioR`) | new `STExpErr`, `STExp2U` (probe); merged `STExp2` `Induction/Defs.lean:159`, `STDecayLoopU` `Induction/DecayLoopB.lean:792`, `STEKSumNdecay` ... `STEKNonzero` `Induction/Step34Pins.lean:613-666`; `ratioR`, `scaleM`: none (single scale `Bctl`, `Defs/Sizes.lean:214`) |
| `Evolution/XiBounds` | **missing**: no RBM3D file; the short-row bound of `Step61` is replaced by `ekSameRow_holds` `Evolution/XiPins.lean:357` (`‖uKer … (m m)‖ ≤ C`, no `log L`) |
| `Hierarchy/ContractionSecondLoopSameEdge` | `Hierarchy/ContractionSecondLoop.lean:239` (`sum_coordinateBlock_trace_pair`) |
| `Gauss/LoopFlowCoordinateChain`, `LoopCoordinateDerivativeBounds` | `Gauss/LoopFlowStein.lean:106, 168, 185`; the second imports no name used by the seven files |
| `Gauss/LoopInitialValueScalar` | `Gauss/LoopGenerator.lean:431, 436, 450, 487` |
| `Gauss/MomentBridge`, `Gauss/SteinMatrix`, `Gauss/LoopEnvelope`, `Gauss/LoopSampleCont` | `Gauss/DominationAt.lean:314, 328, 497-559`; `Gauss/FlowCalculus.lean:309, 341, 348, 356, 600, 701, 708` |
| `Path/PerTime` | `Defs/StochDomAt.lean:100, 105, 213, 249` |
| `Induction/HierVocab` | `Induction/Step34Pins.lean:87, 92, 543` (`STPsum`, `STQop`, `STAlternating`), `Induction/Step2Defs.lean:68, 99, 110, 119` (`STLKM`, `STEGtM`, `STELKLKM`, `STthetaOp`), `Induction/HierarchyN.lean:42` (`STLoopGenNForm`), `:56` (`HierarchyN`) |
| `Evolution/Bridge` | `Evolution/Prec.lean:215, 242, 391, 422` (`stek_*_holds`) |
| `Induction/SumZeroQ`, `Induction/QopBounds` | `Induction/QopAlgebra.lean:573` (`stMollifierEx_holds`) and its algebra section, `Induction/QopNorm.lean:261` (`stQopNorm_holds`) |
| `Induction/HierarchyN` | `Induction/LoopGenN.lean:621` (`hierarchyN_holds`) |
| `Hierarchy/LoopHierarchyCutContinuity`, `Gauss/LoopGeneratorExpectation`, `Gauss/LoopExpectationDerivative`, `Loop/TreeRep` | `Gauss/LoopGenerator.lean:275, 312, 696, 725`; `Gauss/LoopFlowStein.lean:810`; `Path/DriftAlgebra.lean:51` (`KpmODE`, replaces `isPrimitive_Kcal`); `continuousOn_expectedLoopCutRHS`: absent, re-derived in S6-04 |
| `Induction/BcalEDecay`, `Induction/KcalDecay` | `Induction/DecayLoopB.lean:177, 303, 346, 792`; `Induction/Step2Defs.lean:568` (`STK2decay`, `(eq:simpleboundK)`) |
| `Path/ScalesBridge` | none (merged single `ellT`, `etaT`; T2002 class d) |
| `Hierarchy/WardResolvent` | `Induction/ConArgDet.lean:312` (`sum_gloop_ward_last_div`), `Loop/KLWard.lean:1123` (`KLK_ward`) |
| `Propagator/Bounds`, `Propagator/Prop5` | `Propagator/Props4.lean:218` (`norm_Theta_le`); `Propagator/Pins.lean:34` (`Prop5Decay`), `Evolution/XiPins.lean:36` (`ek_norm_XiKer_apply_le`) |

### P.1f Which parts of `MLExpDrift` and `MLExpQ` survive the new exponents (script `parts.py`: per top-level block, d=2 exponent tokens `scaleM|ratioR|ellT|log|^2|etaT` against type tokens `Z2|Sizes`)
```
== MLExpDrift: 1673 lines, 53 blocks; blocks with exponent tokens (scaleM/ratioR/ellT/log/^2/etaT): 29, lines in them: 1271; type-only (Z2/Sizes): 18 blocks, 242 lines; generic: 6 blocks, 83 lines
   MLExpDrift.lean:1327  expDriftBound                                     292 lines  exp-tokens  50  type-tokens  67 
   MLExpDrift.lean:1092  MLExpDrift_bulk_num                               138 lines  exp-tokens  35  type-tokens   0 (private)
   MLExpDrift.lean:610   MLExpDrift_env_X                                  107 lines  exp-tokens  18  type-tokens  51 (private)
   MLExpDrift.lean:913   MLExpDrift_core                                   100 lines  exp-tokens   8  type-tokens  41 (private)
   MLExpDrift.lean:356   MLExpDrift_far                                     80 lines  exp-tokens   8  type-tokens   9 (private)
   MLExpDrift.lean:1230  MLExpDrift_far_num                                 79 lines  exp-tokens   6  type-tokens   1 (private)
   MLExpDrift.lean:775   MLExpDrift_expDriftT_eq                            78 lines  exp-tokens   1  type-tokens  32 (private)
== MLExpQ: 1669 lines, 77 blocks; blocks with exponent tokens (scaleM/ratioR/ellT/log/^2/etaT): 25, lines in them: 892; type-only (Z2/Sizes): 40 blocks, 584 lines; generic: 12 blocks, 102 lines
   MLExpQ.lean:1190  expQBound                                         381 lines  exp-tokens  79  type-tokens 149 
   MLExpQ.lean:622   MLExpQ_T2_decay                                    78 lines  exp-tokens   0  type-tokens   3 
   MLExpQ.lean:513   MLExpQ_K_decay                                     61 lines  exp-tokens   3  type-tokens   6 
   MLExpQ.lean:1008  MLExpQ_scale_facts                                 59 lines  exp-tokens  18  type-tokens   0 
   MLExpQ.lean:199   MLExpQ_qDrift_eq                                   49 lines  exp-tokens   0  type-tokens   8 
   MLExpQ.lean:903   MLExpQ_norm_Psum_expErr                            36 lines  exp-tokens   8  type-tokens  10 
   MLExpQ.lean:1639  inst_expQBound_edge_pt                             32 lines  exp-tokens   2  type-tokens   0 
```
Reading: `MLExpDrift` is exponent-bearing in 1271 of its 1673 lines (the drift bound `expDriftBound` `:1327`, `MLExpDrift_bulk_num` `:1092`, `_far_num` `:1230`, `_A_bulk` `:248`: the `M_u`, `η_u^{-1}M_u^{-3}` arithmetic): the statements and the sum structure survive (`W^d Σ_{x,y} S_{xy} …`, the `≺ → 𝔼` envelope `MLExpDrift_env_X` `:610`, the decay), the exponent arithmetic is re-derived with `Bctl`, `11/5`, `5/2`, `(1-u)^{-1}(N(1-u))^{-3}` (S6-06, S6-07).  `MLExpQ` is exponent-bearing in 892 lines (`expQBound` `:1190`, `MLExpQ_scale_facts` `:1008`, `_absorb` `:950`); 584 lines are type-only and port with `Z2 -> Zd d` (`MLExpQ_qDrift_eq` `:199`, `_sumZero_qDrift` `:248`, `_Psum_*`, `_TensorInv_*`: the algebra of `𝒬`, `𝒫`, `ϑ`), 102 are generic.

## P.2 Item 2: the pins (script `pinstab.py`; line numbers are those of the probe at commit shown in the prove report)
```
 line pin                    paper                  class    ticket    compiled consumers (file:line) | instances
L81   STExp2U                1_2:1390-1396,1_2:1400 owed     S6-13     STExp2_of_STExp2U:97 | inst_endpoints
L105  STStep2Core            1_2:1342-1344          struct   -         st6_expAvgU_of_pin:1062 st6_EGtHi_of_LW:1076 st6_restrict_Core:1627 | inst_restrict inst_expAvgU inst_EGtHi
L121  STIngR6                1_2:1281,6:93-152      struct   -         - | inst_ing6 inst_ing6_I inst_ing6_II inst_ing6_III inst_ing6_I
L133  STStep6Concl           -                      struct   -         - | inst_step6I inst_step6II inst_step6III inst_step6IV inst_ste
L136  STStep6R               1_2:1390-1396,6:93-152 struct   -         ST_step6R_of_any:159 ST_step6_compose:1650 ST_step6R_mono:1729 | -
L141  STStep6I               6:97,6:103-132         owed     S6-02+S6-09+S6-10+S6-11 caseI:1452 | inst_step6I inst_four inst_generic inst_compose
L144  STStep6II              6:97,6:136-147         owed     S6-02+S6-12 caseII:1370 | inst_step6II inst_four inst_generic inst_compose
L147  STStep6III             6:94-96                owed     S6-02+S6-08 caseIII:1242 | inst_step6III inst_four inst_generic
L150  STStep6IV              6:94-96                owed     S6-02+S6-07+S6-08 caseIV:1291 | inst_step6IV inst_four inst_generic
L155  STStep6                6:93-97                owed     S6-13     ST_step6R_of_any:159 ST_mainInd_of_steps:351 | inst_step6 inst_step6_atI inst_step6R_mono inst_assembly6 in
L421  STExpAvgAt             6:14-16                struct   -         - | inst_improveExpAver
L435  STImproveExpAver       6:12-21                owed     S6-03     st6_expAvgU_of_pin:1062 caseIV:1291 caseII:1370 caseI:1452 | inst_skeleton6I inst_skeleton6II inst_skeleton6IV inst_impro
L442  STExpAvgU              -                      struct   -         st6_expAvgU_of_pin:1062 | inst_expDriftLo inst_expWardI inst_expWardII inst_expAvgU
L457  STExpHier              3_5:73,6:90            owed     S6-04     S6-05:proof-of-STExpDuhamelZ/Q(RBM2D expDuhamelPin_of_hier MLExpDuhame | inst_expHier
L469  STExpDuhamelZ          6:3-7,6:142-146        owed     S6-05     st6_duhEq_of_pin:866 caseIII:1242 caseIV:1291 caseII:1370 caseI:1452 | inst_skeleton6I inst_skeleton6II inst_skeleton6III inst_skel
L490  STExpDuhamelQ          6:109-116              owed     S6-05     st6_duhEqQ_of_pin:1338 caseI:1452 | inst_skeleton6I inst_duhamelQ
L500  STExpDuhEq             -                      struct   -         st6_duhEq_of_pin:866 | inst_expIntI inst_expIntII inst_expIntIII inst_expIntIV inst
L510  STExpDuhEqQ            -                      struct   -         - | -
L530  STDriftHi              6:58,6:83              struct   -         st6_hi_of_reg5I:796 st6_hi_of_reg5II:800 st6_hi_of_reg5III:803 st6_EGt | inst_hiI inst_hiII inst_hiIII
L536  STExpLKLKHiConcl       6:58-62                struct   -         - | inst_expLKLK_I inst_expLKLK_II inst_expLKLK_III
L545  STExpLKLKHi            6:58-62                owed     S6-06     caseIII:1242 caseII:1370 caseI:1452 | inst_expLKLK_I inst_expLKLK_II inst_expLKLK_III inst_skeleto
L549  STExpEGtHiConcl        6:83-88                struct   -         st6_EGtHi_of_LW:1076 | inst_EGtHi
L555  STExpDriftHiConcl      -                      struct   -         - | inst_expIntI inst_expIntII inst_expIntIII
L559  STExpDriftLoConcl      6:63-66,6:73-79        struct   -         - | inst_expDriftLo inst_expIntIV
L567  STExpDriftLo           6:63-66,6:73-79        owed     S6-07     caseIV:1291 | inst_expDriftLo inst_skeleton6IV
L574  STExpDriftDecayConcl   3_5:1634               struct   -         - | inst_expDriftDecay inst_expIntI
L579  STExpDriftDecay        3_5:1634               owed     S6-07     caseI:1452 | inst_expDriftDecay inst_skeleton6I
L586  STExpWardIConcl        6:104-107,6:121-123,6: struct   -         - | inst_expWardI inst_expIntI
L605  STExpWardI             6:104-107,6:121-123,6: owed     S6-10     caseI:1452 | inst_expWardI inst_skeleton6I
L612  STExpWardIIConcl       6:137-141              struct   -         - | inst_expWardII
L620  STExpWardII            6:137-141              owed     S6-12     caseII:1370 | inst_expWardII inst_skeleton6II
L639  STExpIntConcl          -                      struct   -         - | inst_expIntI inst_expIntII inst_expIntIII inst_expIntIV
L653  STExpIntQConcl         6:109-116,3_5:1285,3_5 struct   -         - | inst_expIntI
L669  STExpIntIII            6:94-96                owed     S6-08     caseIII:1242 | inst_expIntIII inst_skeleton6III
L676  STExpIntIV             6:94-96                owed     S6-08     caseIV:1291 | inst_expIntIV inst_skeleton6IV
L685  STExpIntII             6:97,6:142-147,3_5:166 owed     S6-12     caseII:1370 | inst_expIntII inst_skeleton6II
L693  STExpIntI              3_5:1649               owed     S6-09     caseI:1452 | inst_expIntI inst_skeleton6I
L702  STExpIniIConcl         6:97,6:117             struct   -         - | inst_expIniI
L715  STExpIniI              6:97,6:117             owed     S6-11     caseI:1452 | inst_expIniI inst_skeleton6I
L1645 STRegSeq               -                      struct   -         ST_step6_compose:1650 st6_genericPos_regSeq:1694 | inst_genericPos_regSeq
L1690 STGenericPos           -                      struct   -         st6_genericPos_regSeq:1694 | inst_genericPos
-- pins (Prop defs): 41 ; classes: {'owed': 20, 'struct': 21}
```

### P.2a The §29 checklist (1)-(7), by pin group

| pin group | (1) times | (2) regime boundary | (3) `L^d ≤ W^K` | (4) `∀ n` / `∀ᶠ n` | (5) per time / uniform | (6) `lam`, `N` | (7) scale |
|---|---|---|---|---|---|---|---|
| the `STIngR6`-shaped pins (all owed pins except the four below) | `0 ≤ s < t ≤ lemT z`, `t < 1` by `st5_t_lt_one` | merged `STReg5I..IV` (`∀ n`, `0 ≤ s` explicit: no negative times at `ilambda > L`); window `STDriftHi`: `ilambda²/L^d ≤ 1-t` | not a premise; follows from `Bandwidth` in `STFlow` (`W ≥ N^𝔠`), used by `lem_+Q` and `(sum_res_2)` in the proofs | sequences `∀ n` (as `STIngR5`); mollifier properties and `STExpDuhEqQ` `∀ᶠ n` | uniform in `u` (`Prec` over `TimeIcc`, union inside `P`) | `WO`, `SizeTendsto` in `STFlow`: `0 < lam n` eventually (`st6_lam_pos`), `(ilambda² W^d)^{-1/5} > 0` (`inst_G_pos_*`) | `Prec`, scale `N` |
| `STExp2U` (the conclusion of every `STStep6R`) | `u ∈ [s_n, t_n]`, `0 ≤ s_n < t_n ≤ lemT z_n` | the regime `R` of the pin | -- | `Prec`: eventually in `n` inside the probability | **uniform in `u`** (union over `(u,σ,a)` inside `P`; the left side is deterministic) | `(ilambda² W^d)^{-1/5}` positive eventually | scale `N = (WL)^d` |
| `STImproveExpAver` | `0 ≤ u ≤ lemT z` | none (all four regimes) | not needed | `∀ n` hypothesis, eventual conclusion | **per time** (index `(σ,a)`) | as above | scale `N` |
| `STExpHier`, `STExpDuhamelZ`, `STExpDuhamelQ` | `|E| < 2`, `0 ≤ s ≤ t < 1`, `u ∈ (0,1)` | none | not needed | deterministic, fixed size: no `∀ᶠ` | fixed `n` | `3 ≤ L` is `sz.three_le_L` | -- |
| `LWtermEXP` (consumed, LW-14) | `0 ≤ t ≤ lemT z` | index set `ilambda²/L^d ≤ 1-t` | -- | `∀ n` | **per time**: made uniform in `u` by (g) `st6_precU_of_forall_seq` and the bridges | -- | scale `N` |

### P.2b Extreme input tried per regime (the boundary of the regime, compiled)

| regime | pin | extreme input | where |
|---|---|---|---|
| (iii) | `STExpIntIII` initial term | `1-u = ilambda²` (`x/(ilambda²+x) = 1/2` exactly), `s = 0` | `inst_cmp_III` (`sz0`, `n = 0`: `(1-s)B_s ≤ 2(1-u)B_u`, `((1-s)/(1-u))² T_s ≤ 4 T_u`) |
| (iv) | `STExpIntIV` initial term | `1-s = ilambda²/L^3 = 25/64` (`szG`), `u = 3/4` | `inst_cmp_IV` |
| (ii) | `STExpIntII` initial term | `1-s = ilambda²/L² = 1/16` (the boundary of `(sum_res_Ndecay_nonzero)`) | `inst_ini_nonzero` (`szB`, `A = {1,2}`) |
| (i) | `STExpIntI`, `STExpIniI` | `1-t = ilambda²/L² = 1/16` | data of `inst_step6I` (`szB`, `(7/8, 15/16)`) |
| all | `STExp2` at `lam = 0` | `lam n = 0` (excluded by `(eq:WO)`) | `inst_target_lam_zero`, `inst_lam_pos` |

### P.2c Statements of the pins and of the vocabulary, extracted by script (`stmts_full.py <probe> pins`; docstrings stripped: the docstrings carry the paper cites, the consumer and the registry class)
```
-- L55
def STExpErr (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) - STKloop sz n E u σ a
-- L59
def STExpELKLK (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STELKLK sz n E u σ a ω ∂(sz.seqP)
-- L64
def STExpEGt (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STEGt sz n E u σ a ω ∂(sz.seqP)
-- L69
def STExpDrift (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  STExpELKLK sz n E u σ a + STExpEGt sz n E u σ a
-- L75
def STExpTarget (n : ℕ) (u : ℝ) : ℝ :=
  (sz.Bctl n u) ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n u)
-- L81
def STExp2U (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω ∂(sz.seqP)) -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (p.1 : ℝ)))
-- L105
def STStep2Core (E s t : ℕ → ℝ) : Prop := STLocalEntryU sz E s t ∧ STAvgU sz E s t
-- L121
def STIngR6 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STExp2 sz (STflowE z) s →
          STConStInd sz 𝔠d s t → STStep2Core sz (STflowE z) s t → STLmaxU sz (STflowE z) s t →
          STLKU sz (STflowE z) s t → STGdecayW sz (STflowE z) s t 0 →
            Concl sz (STflowE z) s t
-- L133
def STStep6Concl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop := STExp2U sz E s t
-- L136
def STStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6 d R (fun sz E s t => STStep6Concl sz E s t)
-- L141
def STStep6I (d : ℕ) : Prop := STStep6R d STReg5I
-- L144
def STStep6II (d : ℕ) : Prop := STStep6R d STReg5II
-- L147
def STStep6III (d : ℕ) : Prop := STStep6R d STReg5III
-- L150
def STStep6IV (d : ℕ) : Prop := STStep6R d STReg5IV
-- L155
def STStep6 (d : ℕ) : Prop := STStep6R d STAny
-- L421
def STExpAvgAt (E u : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂(sz.seqP)) - mSigma (E n) p.1‖)
    (fun n _ _ => (sz.Bctl n (u n)) ^ 2)
-- L435
def STImproveExpAver (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ lemT (z n)) →
        LWAvgLaw sz (STflowE z) u → STLK sz (STflowE z) u → STExpAvgAt sz (STflowE z) u
-- L442
def STExpAvgU (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) (fun _ : Fin 1 => p.2.1) (fun _ => p.2.2) ω ∂(sz.seqP)) -
      mSigma (E n) p.2.1‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2)
-- L457
def STExpHier (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => STExpErr sz n E u σ a) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => STExpDrift sz n E u σ a) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => STExpErr sz n E v σ a)
      (STthetaOp sz n E u σ (fun b => STExpErr sz n E u σ b) a + STExpDrift sz n E u σ a) u
-- L469
def STExpDuhamelZ (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A (fun b => STExpErr sz n E t σ b) a =
        zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t (fun b => STExpErr sz n E s σ b)) a +
        ∫ u in s..t, zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (fun b => STExpDrift sz n E u σ b)) a
-- L480
def STExpQsrc (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    (Fin 2 → Zd d (sz.L n)) → ℂ := fun b =>
  STQop (d := d) ϑ u (fun c => STExpDrift sz n E u σ c) b +
    (STQop (d := d) ϑ u (STthetaOp sz n E u σ (fun c => STExpErr sz n E u σ c)) b -
      STthetaOp sz n E u σ (STQop (d := d) ϑ u (fun c => STExpErr sz n E u σ c)) b) -
    STPsum (d := d) (fun c => STExpErr sz n E u σ c) (b 0) * deriv (fun τ => ϑ τ b) u
-- L490
def STExpDuhamelQ (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    STMollifierProps (d := d) (sz.lam n) C c ϑ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STQop (d := d) ϑ t (fun b => STExpErr sz n E t σ b) a =
        RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t
          (STQop (d := d) ϑ s (fun b => STExpErr sz n E s σ b)) a +
        ∫ u in s..t, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (STExpQsrc sz n E u σ ϑ) a
-- L500
def STExpDuhEq (E s t : ℕ → ℝ) : Prop :=
  ∀ n (u : TimeIcc s t n) (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
    zeroModeSet d (sz.L n) A (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a =
      zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (u : ℝ) (fun b => STExpErr sz n (E n) (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b)) a
-- L510
def STExpDuhEqQ (E s t : ℕ → ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    STQop (d := d) (ϑ n) (u : ℝ) (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a =
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (u : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ)
        (STExpQsrc sz n (E n) v σ (ϑ n)) a
-- L530
def STDriftHi {d : ℕ} (sz : Sizes d) (_s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n
-- L536
def STExpLKLKHiConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))
-- L545
def STExpLKLKHi (d : ℕ) : Prop := STIngR6 d STDriftHi (fun sz E s t => STExpLKLKHiConcl sz E s t)
-- L549
def STExpEGtHiConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))
-- L555
def STExpDriftHiConcl (E s t : ℕ → ℝ) : Prop := STExpLKLKHiConcl sz E s t ∧ STExpEGtHiConcl sz E s t
-- L559
def STExpDriftLoConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpDrift sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - (p.1 : ℝ)))⁻¹) ^ 3)
-- L567
def STExpDriftLo (d : ℕ) : Prop :=
  STIngR6 d STReg5IV (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t)
-- L574
def STExpDriftDecayConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ σ : Fin 2 → Bool, STEKDecay sz s t (fun n v _ a => STExpDrift sz n (E n) (v : ℝ) σ a)
-- L579
def STExpDriftDecay (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpDriftDecayConcl sz E s t)
-- L586
def STExpWardIConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3) ∧
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ =>
        ‖STQop (d := d) (ϑ n) (q.1 : ℝ) (STthetaOp sz n (E n) (q.1 : ℝ) q.2.1.1
            (fun c => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 c)) q.2.2 -
          STthetaOp sz n (E n) (q.1 : ℝ) q.2.1.1
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (fun c => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 c)) q.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
          deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)
-- L605
def STExpWardI (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t)
-- L612
def STExpWardIIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q _ => ‖STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 -
      zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
    (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3)
-- L620
def STExpWardII (d : ℕ) : Prop :=
  STIngR6 d STReg5II (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t)
-- L639
def STExpIntConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (E s t : ℕ → ℝ) : Prop :=
  ∀ F : ∀ n, STIdx2P sz P s t n → ℝ, (∀ n p, 0 ≤ F n p) →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) Q
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p) →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) Q (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))
-- L653
def STExpIntQConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → STExpDuhEqQ sz E s t ϑ →
    ∀ F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ F n p) →
      Prec sz (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => F n p) →
      Prec sz (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
          (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
        (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))
-- L669
def STExpIntIII (d : ℕ) : Prop :=
  STIngR6 d STReg5III (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t)
-- L676
def STExpIntIV (d : ℕ) : Prop :=
  STIngR6 d STReg5IV (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t)
-- L685
def STExpIntII (d : ℕ) : Prop :=
  STIngR6 d STReg5II (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t)
-- L693
def STExpIntI (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t → STExpWardIConcl sz E s t →
      STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl sz E s t)
-- L702
def STExpIniIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2P sz STSigSame s t)
    (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
      (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b) p.2.2‖)
    (fun n p _ => STExpTarget sz n (p.1 : ℝ)) ∧
  ∀ (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))
-- L715
def STExpIniI (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpIniIConcl sz E s t)
-- L1645
def STRegSeq (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∃ m : ℕ → ℝ, (∀ n, s n < m n) ∧ (∀ n, m n < t n) ∧ R₁ sz s m ∧ R₂ sz m t
-- L1690
def STGenericPos {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∀ n, 0 < sz.lam n ∧ s n < 1 - sz.lam n ^ 2 ∧ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d < t n
```

### P.2d Statements of the endpoint, glue and bridge theorems (`stmts_full.py <probe> thms`)
```
-- L97
theorem STExp2_of_STExp2U {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STExp2U sz E s t) : STExp2 sz E t := by
-- L159
theorem ST_step6R_of_any {d : ℕ} (h : STStep6 d) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    STStep6R d R := by
-- L236
theorem st6_precU_of_forall_seq (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    {W : ℕ → Type*} (F G : ∀ n, ℝ → W n → ℝ)
    (h : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      sz.Prec (U := W) (fun n w _ => F n (u n) w) (fun n w _ => G n (u n) w)) :
    sz.Prec (U := fun n => TimeIcc s t n × W n) (fun n p _ => F n (p.1 : ℝ) p.2)
      (fun n p _ => G n (p.1 : ℝ) p.2) := by
-- L351
theorem ST_mainInd_of_steps (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3 d) (h4 : STStep4 d)
    (h5 : STStep5 d) (h6 : STStep6 d) : STMainInd d := by
-- L866
theorem st6_duhEq_of_pin (hDu : STExpDuhamelZ d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n)) :
    STExpDuhEq sz (STflowE z) s t := by
-- L1062
theorem st6_expAvgU_of_pin (hAvg : STImproveExpAver d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hS2 : STStep2Core sz (STflowE z) s t)
    (hLKU : STLKU sz (STflowE z) s t) : STExpAvgU sz (STflowE z) s t := by
-- L1076
theorem st6_EGtHi_of_LW (hLW : LWtermEXP d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hHi : STDriftHi sz s t) (hS2 : STStep2Core sz (STflowE z) s t)
    (hLmax : STLmaxU sz (STflowE z) s t) (hLKU : STLKU sz (STflowE z) s t)
    (hS5 : STGdecayW sz (STflowE z) s t 0) : STExpEGtHiConcl sz (STflowE z) s t := by
-- L1105
theorem st6_ini_sumNdecay (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hExp : STExp2 sz (STflowE z) s) :
    sz.Prec (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 (s n) (p.1 : ℝ)
        (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) := by
-- L1156
theorem st6_ini_nonzero (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) (hExp : STExp2 sz (STflowE z) s)
    (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop)
    (hA : ∀ σ, P σ → ∀ i, σ i ≠ σ (finRotate 2 i) → i ∈ A) :
    sz.Prec (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) A (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n)
        (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget sz n (s n)) := by
-- L1233
theorem st6_F1_window_vs_reg5II {s t : ℕ → ℝ} (hI : STCaseI sz s t) (hII : STReg5II sz s t) (n : ℕ) : t n ≤ s n := by
-- L1242
theorem ST_step6_caseIII_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hDu : STExpDuhamelZ d)
    (hInt : STExpIntIII d) : STStep6III d := by
-- L1291
theorem ST_step6_caseIV_of_pins (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hLo : STExpDriftLo d)
    (hInt : STExpIntIV d) : STStep6IV d := by
-- L1338
theorem st6_duhEqQ_of_pin (hDu : STExpDuhamelQ d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n))
    (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) :
    STExpDuhEqQ sz (STflowE z) s t ϑ := by
-- L1350
theorem st6_mollifier_family (hd : 3 ≤ d) {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hWO : sz.WO 𝔡) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
      ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n) := by
-- L1370
theorem ST_step6_caseII_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
    (hDu : STExpDuhamelZ d) (hInt : STExpIntII d) (hWd : STExpWardII d) : STStep6II d := by
-- L1452
theorem ST_step6_caseI_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
    (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d)
    (hIni : STExpIniI d) (hInt : STExpIntI d) : STStep6I d := by
-- L1560
theorem st6_restrict_LocalEntryU {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STLocalEntryU sz E s t) : STLocalEntryU sz E s' t' :=
-- L1566
theorem st6_restrict_AvgU {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STAvgU sz E s t) : STAvgU sz E s' t' :=
-- L1572
theorem st6_restrict_LmaxU {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STLmaxU sz E s t) : STLmaxU sz E s' t' := fun k hk =>
  StochDomAt.precomp_param (h k hk)
    (fun n (p : TimeIcc s' t' n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) =>
      ((st6_incl hs ht n p.1, p.2) : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))))

theorem st6_restrict_LKU {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STLKU sz E s t) : STLKU sz E s' t' := fun k hk =>
  StochDomAt.precomp_param (h k hk)
    (fun n (p : TimeIcc s' t' n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) =>
      ((st6_incl hs ht n p.1, p.2) : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))))

/-- `(Eq:Gdecay_flow)` without loss (`STGdecayW … 0`) restricts to a sub-interval. -/
theorem st6_restrict_GdecayW {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STGdecayW sz E s t 0) : STGdecayW sz E s' t' 0 := by
-- L1578
theorem st6_restrict_LKU {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STLKU sz E s t) : STLKU sz E s' t' := fun k hk =>
  StochDomAt.precomp_param (h k hk)
    (fun n (p : TimeIcc s' t' n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) =>
      ((st6_incl hs ht n p.1, p.2) : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))))

/-- `(Eq:Gdecay_flow)` without loss (`STGdecayW … 0`) restricts to a sub-interval. -/
theorem st6_restrict_GdecayW {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STGdecayW sz E s t 0) : STGdecayW sz E s' t' 0 := by
-- L1585
theorem st6_restrict_GdecayW {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STGdecayW sz E s t 0) : STGdecayW sz E s' t' 0 := by
-- L1596
theorem st6_GdecayW_of_zero (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (h : STGdecayW sz E s t 0) : STGdecayW sz E s t Cd := by
-- L1627
theorem st6_restrict_Core {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n)
    (h : STStep2Core sz E s t) : STStep2Core sz E s' t' :=
-- L1632
theorem st6_cover_two (hsz : sz.SizeTendsto) {s m t : ℕ → ℝ} (hsm : ∀ n, s n ≤ m n) (hmt : ∀ n, m n ≤ t n)
    {W : ℕ → Type*} (F G : ∀ n, ℝ → W n → ℝ)
    (h₁ : sz.Prec (U := fun n => TimeIcc s m n × W n) (fun n p _ => F n (p.1 : ℝ) p.2) (fun n p _ => G n (p.1 : ℝ) p.2))
    (h₂ : sz.Prec (U := fun n => TimeIcc m t n × W n) (fun n p _ => F n (p.1 : ℝ) p.2) (fun n p _ => G n (p.1 : ℝ) p.2)) :
    sz.Prec (U := fun n => TimeIcc s t n × W n) (fun n p _ => F n (p.1 : ℝ) p.2) (fun n p _ => G n (p.1 : ℝ) p.2) := by
-- L1650
theorem ST_step6_compose {R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    (h₁ : STStep6R d R₁) (h₂ : STStep6R d R₂) : STStep6R d (STRegSeq R₁ R₂) := by
-- L1684
theorem ST_step6_four_of_regimes (h1 : STStep6I d) (h2 : STStep6II d) (h3 : STStep6III d) (h4 : STStep6IV d) :
    STStep6R d (STRegSeq STReg5III (STRegSeq STReg5I (STRegSeq STReg5II STReg5IV))) :=
-- L1694
theorem st6_genericPos_regSeq (hd : 3 ≤ d) {s t : ℕ → ℝ} (h : STGenericPos sz s t) :
    STRegSeq STReg5III (STRegSeq STReg5I (STRegSeq STReg5II STReg5IV)) sz s t := by
-- L1722
theorem ST_step6_generic_of_regimes (h1 : STStep6I d) (h2 : STStep6II d) (h3 : STStep6III d) (h4 : STStep6IV d) :
    STStep6R d STGenericPos := by
-- L1729
theorem ST_step6R_mono {R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : STStep6R d R) : STStep6R d R' := by
```

## P.3 Item 3: exponent table (the table is section (a) of the prove report; this part adds the RBM2D replacements and the compiled constants)

| RBM2D exponent (file:line, `c9a24cf`) | d >= 3 exponent | pin |
|---|---|---|
| `M_u^{-2}` (`Evolution/Defs.lean:123`, `Step61.lean:853`) | `(W^{-d}B_{u,0})²` | `STExpAvgAt` |
| `η_u^{-1} M_u^{-3}` (`MLExpVocab.lean:97`, `eq:LKLKstep6` 5-6:1459) | `(1-u)^{-1}(W^{-d}B_{u,0})^{11/5}` (`6:61`), `(1-u)^{-1}(W^{-d}B_{u,0})^{5/2}` (`6:86`); `(1-u)^{-1}(N(1-u))^{-3}` (`6:65`, `6:77`) | `STExpLKLKHiConcl`, `STExpEGtHiConcl`, `STExpDriftLoConcl` |
| `M_t^{-3}` (`Evolution/Defs.lean:141`) | `(W^{-d}B_{t,0})² ((ilambda² W^d)^{-1/5} + W^{-d}B_{t,0})` | `STExpTarget` |
| `log L` of the row sum (`Step61.lean:37-38, 447-480`) | none: `‖Θ_{u m²}‖ ≤ C` (`ekSameRow_holds`) | `STImproveExpAver` |
| `log L` of the lattice sums and the time integral (`MLExpQ.lean:50-57, 423-428`; `MLExpVocab_norm_integral_le_log` `MLExpVocab.lean:349`) | the `u`-integral `∫ x⁻¹ dx = log(x_s/x_u) ≤ 2 log L` (i), `(d-2) log L` (ii) only; none in (iii), (iv) (`x^{-6/5}`, `x^{-3/2}`, `x^{-4}`); absorbed by `≺` (`log L ≤ N^τ`) | `STExpIntI`, `STExpIntII` |

Compiled constants (Lean, `Induction`-level facts of the probe, replace the numerics of (a) lines 18-19): `(1-s) B_s ≤ 2 (1-u) B_u` in regime (iii) (`st6_xB_III`, from `ilambda² ≤ 1-u`) and in regime (iv) (`st6_xB_IV`, from `1-s ≤ ilambda²/L^d`), hence `((1-s)/(1-u))² B_s² ≤ 4 B_u²` (`st6_ratio_sq`) and `((1-s)/(1-u))² T_s ≤ 4 T_u` (`st6_cmp_ini`), no power of `W`: **no `𝔠_d` loss**.  `B_u³ ≤ T_u` (`st6_cube_le_target`), `T_s ≤ T_u` (`st6_target_mono`).
**Does `𝔠_d` have to be lowered beyond Steps 2-5?**  No new upper bound from Step 6: the constant of each skeleton is the minimum of the constants of its pins (`min`, `st5_conStInd_mono`), and every kernel ratio above is a constant.  The one requirement is `d·𝔠_d < 1` for the kernel window `(1-t)/(1-s) ≥ W^{-1}` of `lem:sum_decay` (`STEKWin`, regime (i)): merged `st_EKWin` (`Induction/ScaleFacts3.lean:466`); with `𝔠_d ≤ 1/100` it holds for `d ≤ 99`, and for every `d` it is arranged inside the existential (`𝔠_d ≤ min(1/100, 1/(2d))`; the pins quantify `∃ 𝔠_d` and a smaller `𝔠_d` is the stronger hypothesis `(con_st_ind)`).

## P.4 Item 4: route for each pin (RBM2D source at `c9a24cf`, merged declarations reused, tickets: P.5)

| pin | route | RBM2D source (`c9a24cf`) | merged declarations reused | est. lines | risk |
|---|---|---|---|---|---|
| `STStep6I..IV`, `STExp2U` | skeleton compiled in the probe (`ST_step6_case*_of_pins`) | `MLExpVocab.lean:606` `mlExp_of_pins` (assembly of the d=2 pins) | `stek_*_holds`, `st5_conStInd_mono`, `st5_prec_mono` | 1000 (S6-02, moved) | low |
| `STStep6` | compiled: `ST_step6_compose` (one intermediate time), `ST_step6_generic_of_regimes` (all four regimes occur for every `n`); the general `STStep6` needs the split of `ℕ` into patterns of nonempty stages and a transfer to subsequences of the sizes (or regime pins with the regime inside the index set) | analogue of S5-29 | `st_conStInd_sub`, `st_split_I/II` (`ScaleFacts3.lean:478-514`), bridges `*_at`, `st6_restrict_*`, `ST_step6_compose` | 1000 (S6-13) | high |
| `STImproveExpAver` | port, row sum constant | `Step61.lean:853` (`step61`; `step61_stein`, `_selfcons`, `_theta_solve`, `_moment`) | `ekSameRow_holds` `XiPins.lean:357`, `stein` `DominationAt.lean:559`, `momentDomAt_of_stochDomAt` `:328`, `LoopFlowStein`, `initialLoopValue_one_edge` `LoopGenerator.lean:450` | 950 (S6-03) | medium |
| `STExpHier` | port | `MLExpHier.lean:643` `expHierPin`; `MLExpVocab.lean:111` | `hierarchyN_holds` `LoopGenN.lean:621`, `deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts` `LoopGenerator.lean:312`, `initialLoopValue_two_edges` `:487`, `KpmODE` `DriftAlgebra.lean:51` | 700 (S6-04) | medium |
| `STExpDuhamelZ`, `STExpDuhamelQ` | port, start at `s` | `MLExpDuhamel.lean:412, 423`; `MLExpVocab.lean:229` `qop_source` | `Ugen` `GridDuhamelN.lean:65`, `zeroModeSet_Ugen` `ZeroModeCalc.lean:450`, `STQop`/`STPsum` `Step34Pins.lean:87, 92` | 900 (S6-05) | medium |
| `STExpLKLKHi` | new exponents, same sum structure; new lattice sum | `MLExpDrift.lean:1327` `expDriftBound`, `:610` `_env_X` | `STDecayLoopU` `DecayLoopB.lean:792`, `STELKLKM` `Step2Defs.lean:110`, `STGdecayW`, `STLKU` | 1200 (S6-06) | medium-high |
| `STExpDriftLo`, `STExpDriftDecay` | new exponents | `MLExpDrift.lean:1092, 1230` | `stKbound_of_flow` `KLFinal.lean:302`, `STEGtM` `Step2Defs.lean:99`, `st6_expAvgU_of_pin` | 1200 (S6-07) | medium-high |
| `STExpIntIII`, `STExpIntIV` | new: `u`-integrals | pattern `MLExpVocab.lean:349-400` | `stek_sumNdecay_holds` `Prec.lean:215`, `STBctl_mono` `ScaleFacts.lean:74` | 1100 (S6-08) | medium |
| `STExpIntI` | port of the `𝒬` bounds, new `(sum_res_2)` integral | `MLExpQ.lean:1190` `expQBound`, `:199`, `:248` | `stek_sumRes2NAL_holds` `Prec.lean:242`, `stek_sumRes2_holds` `:391`, `stQopNorm_holds` `QopNorm.lean:261`, `stMollifierEx_holds` `QopAlgebra.lean:573` | 1500 (S6-09) | high |
| `STExpWardI` | port | `MLExpQ.lean` (`eq:p_term_step6`, `commutator_step6`) | `sum_gloop_ward_last_div` `ConArgDet.lean:312`, `KLK_ward` `KLWard.lean:1123` | 1100 (S6-10) | medium-high |
| `STExpIniI` | new: decay of `f_s` by `≺ → 𝔼`, kernel | none | `stek_sumRes2NAL_holds`, `stek_sumRes2_holds`, `stQopNorm_holds` | 900 (S6-11) | medium |
| `STExpIntII`, `STExpWardII` | new: regime (ii) is empty at `d = 2` (`L² = L^d`) | none | `stek_nonzero_holds` `Prec.lean:422`, `norm_zeroModeSet_le` `ZeroModeCalc.lean:163`, `zeroModeSet_Ugen` `:450` | 1300 (S6-12) | high |

## P.5 Item 6: split table (script `split.py`)

```
tickets 13; est lines 14000; mean 1076; min 700; max 1500
roles: {'prover': 3, 'prover-hard': 7, 'prover-max': 3} | risk: {'low': 2, 'medium': 5, 'medium-high': 3, 'high': 3}
DECISIONS §9 O2: ST-5 = 1 design + 13 proof tickets = 14: band under 25 (25/40/50): question to Jun: no
```

| ticket | file | statements | sources | depends on | role | est. lines | risk |
|---|---|---|---|---|---|---|---|
| S6-01 | Induction/Step6Pins.lean | vocabulary STExpErr/ELKLK/EGt/Drift/Target, STStep2Core, STIngR6, STExp2U(+_iff), STStep6R/I-IV/STStep6, STRegSeq, ST_step6R_of_any, the 20 ingredient pins and *Concl, registry lines (Test/Axioms.lean), instances §8 | probe T2191 §1, §4, §8 (moved) | merged Step5Pins, Step34Pins, Defs; none of S6 | prover | 900 | low |
| S6-02 | Induction/Step6Kit.lean | st6_prec_det_iff, st6_precU_of_forall_seq (g), bridges *_at, ST_mainInd_of_steps, st6_xB_III/IV, st6_cmp_ini, st6_EGt_eq_LWE, st6_EGtHi_of_LW, st6_expAvgU_of_pin, st6_ini_sumNdecay/nonzero, ST_step6_case{I,II,III,IV}_of_pins, st6_restrict_*, st6_cover_two, ST_step6_compose, ST_step6R_mono, ST_step6_four_of_regimes, STGenericPos, st6_genericPos_regSeq, ST_step6_generic_of_regimes | probe T2191 §2, §3, §5-§7b (moved, compiled) | S6-01; LW-14 (LWtermEXP, premise only); merged stek_*_holds, st_conStInd_sub | prover | 1250 | low |
| S6-03 | Induction/ExpAvg.lean | STImproveExpAver (lem:improve_exp_aver, 6:12-21) | RBM2D Evolution/Step61.lean (1021 lines, 933 kept; step61 :853: Stein, self-consistent equation, row sum, second moments); row sum from merged ekSameRow_holds | S6-01; Gauss/SteinMatrix, LoopFlowStein, DominationAt, XiPins | prover-hard | 950 | medium |
| S6-04 | Induction/ExpHier.lean | STExpHier ((eq_L-Keee) at n=2 after expectation) | RBM2D Evolution/MLExpHier.lean (731 lines, 648 kept; expHierPin :643) + MLExpVocab ExpHierPin :111 | S6-01; hierarchyN_holds, deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts, initialLoopValue_two_edges | prover | 700 | medium |
| S6-05 | Induction/ExpDuhamel.lean | STExpDuhamelZ, STExpDuhamelQ ((Eexpint_K-L), (int_K-L+QE)) | RBM2D Evolution/MLExpDuhamel.lean (532 lines, 474 kept; expDuhamelPin_of_hier :412, expQDuhamelPin_of_hier :423) + MLExpVocab qop_source | S6-04; GridDuhamelN (Ugen), zeroModeSet_Ugen, QopAlgebra | prover-hard | 900 | medium |
| S6-06 | Induction/ExpEtermsA.lean | STExpLKLKHi ((eq:Exp(L-K)1), 6:58-62) with the lattice sum of B e^{-(r/l)^{1/2}} | RBM2D Evolution/MLExpDrift.lean (1673 lines, 1545 kept; expDriftBound :1327: structure of the sums, the envelope, decay) re-derived with 11/5; lattice sum new | S6-01; Step 4/5 pins; DominationAt (momentDomAt_of_stochDomAt) | prover-hard | 1200 | medium-high |
| S6-07 | Induction/ExpEtermsB.lean | STExpDriftLo ((eq:Exp(L-K)2), (eq:ExpLWn=2_smalleta)), STExpDriftDecay ((deccA0) for D_u) | RBM2D MLExpDrift.lean (bulk/far numerics) re-derived: (1-u)^{-1}(N(1-u))^{-3}; decay from merged STDecayLoopU | S6-03, S6-06; STDecayLoopU (DecayLoopB), stKbound_of_flow | prover-hard | 1200 | medium-high |
| S6-08 | Induction/ExpIntEasy.lean | STExpIntIII, STExpIntIV (6:94-96) | new (u-integrals x^{-6/5}, x^{-3/2}, (N x)^{-3}); RBM2D MLExpVocab_core :~370 (log integral) as pattern | S6-05, S6-06, S6-07; stek_sumNdecay_holds | prover-hard | 1100 | medium |
| S6-09 | Induction/ExpIntI.lean | STExpIntI (6:97, 6:104-132) | RBM2D MLExpQ.lean (1669 lines, 1533 kept; expQBound :1190, Psum/Qop norm lemmas) + new sum_res_2 integral | S6-05, S6-07, S6-10; stek_sumRes2NAL_holds, stek_sumRes2_holds, stQopNorm_holds, stMollifierEx_holds | prover-max | 1500 | high |
| S6-10 | Induction/ExpWardI.lean | STExpWardI ((eq:EPL-K), (eq:boundELKQ1), (eq:boundcommutator)) | RBM2D MLExpQ.lean (eq:p_term_step6 :~1494, commutator_step6 :~1501, Ward) | S6-03; KLK_ward, sum_gloop_ward_last_div, STMollifierProps | prover-hard | 1100 | medium-high |
| S6-11 | Induction/ExpIniI.lean | STExpIniI (initial term of regime (i), 6:97, 6:117) | new (decay of f_s through ≺→𝔼, kernel (sum_res_2_NAL), (sum_res_2), lem_+Q) | S6-01; stek_sumRes2NAL_holds, stek_sumRes2_holds, stQopNorm_holds | prover-hard | 900 | medium |
| S6-12 | Induction/ExpIntII.lean | STExpIntII, STExpWardII (6:136-147, Ward decomposition 6:138-140) | new: regime (ii) is empty at d=2 (L^2 = L^d), no RBM2D source | S6-03, S6-05, S6-06; stek_nonzero_holds, norm_zeroModeSet_le, zeroModeSet_Ugen | prover-max | 1300 | high |
| S6-13 | Induction/Step6Glue.lean | STStep6 from STStep6I..IV for arbitrary (s,t) (6:93-97): the generic position (every n meets all four regimes) is compiled (ST_step6_generic_of_regimes, S6-02); remaining: the split of N into the finitely many patterns of nonempty stages and the transfer of a pin to a subsequence of the sizes; alternative: restate the regime pins with the regime condition inside the index set | analogue of S5-29; merged st_conStInd_sub, st_split_I/II (ScaleFacts3:478-514), bridges *_at, STExp2_of_STExp2U; no sizes-subsequence transfer on main (grep, report b) | S6-02, S6-08, S6-09, S6-12, S5-29 (STStep5 as pin) | prover-max | 1000 | high |

Against DECISIONS §9 O2: ST-5 is 1 design + 13 proof tickets = 14, below 25: no question to Jun.  The dispatcher's prior (about 11 tickets, about 10.8k lines) is exceeded by two tickets because the compiled probe (2348 lines) is moved in two files (S6-01, S6-02) and the Step-6 assembly of intermediate times is S6-13.  `MLExpInv` (878 lines) is not ported: the merged `stExpInv_holds` (`Evolution/ExpInv.lean:510`, S5-22a) is unused by the d >= 3 Step 6.  Dependencies on other gates enter as pins: `LWtermEXP` (LW-14), `STStep2`, `STStep3`, `STStep4` (ST-2, ST-3), `STStep5` (S5-29), `STDecayLoopU` (S3-07b).

## P.6 Item 7: compiled instances (script `insts.py`)
```
67 public instance theorems (RBM.Gauss.Step6Inst), by data:
  own data (deterministic pin / lemma): 28: inst_ing6 inst_improveExpAver inst_expHier inst_duhamelZ inst_duhamelQ inst_precU inst_cover_two inst_restrict inst_GdecayW_of_zero inst_F1 inst_bridges inst_endpoints inst_assembly6 inst_expAvgU inst_EGtHi inst_duhEq inst_A_value inst_G_pos_sz0 inst_G_pos_szB inst_G_pos_szG inst_target_pos_sz0 inst_target_pos_szB inst_target_pos_szG inst_normQA2 inst_lam_pos inst_target_lam_zero inst_ini_sumNdecay inst_mollifier_family
  (szB, zB, 7/8, 15/16)  regime (i): 12: inst_ing6_I inst_step6I inst_step6_atI inst_hiI inst_expLKLK_I inst_expDriftDecay inst_expWardI inst_expIniI inst_expIntI inst_skeleton6I inst_step6R_mono inst_step6R_of_any
  (szB, zB, 15/16, 31/32) regime (ii): 8: inst_ing6_II inst_step6II inst_hiII inst_expLKLK_II inst_expWardII inst_expIntII inst_skeleton6II inst_ini_nonzero
  (sz0, z0, 0, 1/16)     regime (iii): 8: inst_ing6_III inst_step6III inst_step6 inst_hiIII inst_expLKLK_III inst_expIntIII inst_skeleton6III inst_cmp_III
  (szG, zB, 5/8, 3/4)    regime (iv): 6: inst_ing6_IV inst_step6IV inst_expDriftLo inst_expIntIV inst_skeleton6IV inst_cmp_IV
  (szFour, zB, 0, 49/50) all four regimes (generic position): 4: inst_genericPos inst_genericPos_regSeq inst_four inst_generic
  (szB, zB, 7/8, 31/32) two stages (i)+(ii) cut at 15/16: 1: inst_compose
regime inequalities in exact fractions (g = ilambda; L = 4, except szFour: L = 3):
  szB      regime (i) : g^2=1 g^2/L^2=1/16 g^2/L^3=1/64 1-t=1/16 1-s=1/8 | (i) g2/L2<=1-t<=1-s<=g2: True | (ii) g2/L3<=1-t<=1-s<=g2/L2: False | (iii) g2<=1-t: False | (iv) 1-s<=g2/L3: False
  szB      regime (ii): g^2=1 g^2/L^2=1/16 g^2/L^3=1/64 1-t=1/32 1-s=1/16 | (i) g2/L2<=1-t<=1-s<=g2: False | (ii) g2/L3<=1-t<=1-s<=g2/L2: True | (iii) g2<=1-t: False | (iv) 1-s<=g2/L3: False
  sz0 n=0  regime (iii): g^2=1/4096 g^2/L^2=1/65536 g^2/L^3=1/262144 1-t=15/16 1-s=1 | (i) g2/L2<=1-t<=1-s<=g2: False | (ii) g2/L3<=1-t<=1-s<=g2/L2: False | (iii) g2<=1-t: True | (iv) 1-s<=g2/L3: False
  szG      regime (iv): g^2=25 g^2/L^2=25/16 g^2/L^3=25/64 1-t=1/4 1-s=3/8 | (i) g2/L2<=1-t<=1-s<=g2: False | (ii) g2/L3<=1-t<=1-s<=g2/L2: False | (iii) g2<=1-t: False | (iv) 1-s<=g2/L3: True
  szFour (L = 3, ilambda = 4/5): boundaries 1-g^2 = 9/25, 1-g^2/L^2 = 209/225, 1-g^2/L^3 = 659/675; s = 0 < 9/25 < 209/225 < 659/675 < t = 49/50: True
  A = g^2 W^d at sz0 n=0: (1/64)^2 * 32^3 = 8 ; G = A^(-1/5) = 0.6598
```

## P.7 Registry classes (DECISIONS §16, §20), proposed

* **owed** (20; proved by the tickets of P.5): `STStep6I`, `STStep6II`, `STStep6III`, `STStep6IV`, `STStep6`, `STExp2U`, `STImproveExpAver`, `STExpHier`, `STExpDuhamelZ`, `STExpDuhamelQ`, `STExpLKLKHi`, `STExpDriftLo`, `STExpDriftDecay`, `STExpWardI`, `STExpWardII`, `STExpIntI`, `STExpIntII`, `STExpIntIII`, `STExpIntIV`, `STExpIniI`.
* **structural** (21): `STStep2Core`, `STRegSeq`, `STGenericPos`, `STIngR6`, `STStep6R`, `STStep6Concl`, `STExpAvgAt`, `STExpAvgU`, `STExpDuhEq`, `STExpDuhEqQ`, `STDriftHi`, `STExpLKLKHiConcl`, `STExpEGtHiConcl`, `STExpDriftHiConcl`, `STExpDriftLoConcl`, `STExpDriftDecayConcl`, `STExpWardIConcl`, `STExpWardIIConcl`, `STExpIntConcl`, `STExpIntQConcl`, `STExpIniIConcl` (shapes and conclusion predicates; `STExpDuhEq`, `STExpDuhEqQ` are derived by `st6_duhEq_of_pin`, `st6_duhEqQ_of_pin`).
* **borrowed**: none (DECISIONS §5: only LSY).
* Premises taken from other gates, none left without a proving ticket: `LWtermEXP` (owed, LW-14), `STStep2..STStep5` (owed), `STLK`, `STDecay`, `STExp2` at `s` (owed, ST-6 chain), `STStep2Core` (the loss-free part of `STStep2Concl`; `STStep2Concl` itself enters `ST_mainInd_of_steps`), `STLmaxU`, `STLKU` (owed, ST-3), `STGdecayW` (owed, ST-4), `LWAvgLaw` (a section of `STAvgU`, `LWAvgLaw_of_STAvgU_at`) and `STLK` at `u` (a section of `STLKU`, `STLK_of_STLKU_at`), the two premises of `STImproveExpAver` = the two premises of `lem:improve_exp_aver`; `STStep1` is proved (`RBM.Green.stStep1_holds`).

## P.8 Findings

* **(F-shape)** `STIngR6` is the shape of `STIngR5` with the premises removed that Step 6 does not use and that a sub-interval does not inherit: `STKbound`, `STKward` (theorems of the flow), `STDecayStrong s`, `STDecayStrongU` (index `ilambda² ≤ 1-t`), `STStep1Loop`; and `STStep2Concl … C_d` replaced by its loss-free part `STStep2Core` (its third conjunct `(Eq:Gdecay_w)` has the loss `((1-s)/(1-u))^{C_d}` relative to the start `s`, so it does not restrict to `[s',t']` with `s' > s`; Step 6 does not use it, and `STGdecayW … 0` implies it: `st6_GdecayW_of_zero`), hence no `∀ C_d` (a deviation from `STIngR5`, paper-delta candidate `T2191b`).  With this shape every premise restricts to a sub-interval or is a section at its start (`st6_restrict_*`, `*_at`), `(d)` at the next stage is the endpoint of the previous one (`STExp2_of_STExp2U`), `(con_st_ind)` passes (`st_conStInd_sub`): compiled as `ST_step6_compose` (the pin of a two-stage regime from the two pins; instance `inst_compose`, `(szB, zB, 7/8, 31/32)` cut at `15/16`), `ST_step6_four_of_regimes` (stages (iii), (i), (ii), (iv)) and `ST_step6_generic_of_regimes` (every `[s_n,t_n]` contains `1-ilambda²`, `1-ilambda²/L²`, `1-ilambda²/L^d`: `STGenericPos`), with the instances `inst_four`, `inst_generic` at `(szFour, zB, 0, 49/50)` (`L = 3`, `ilambda = 4/5`: all four regimes inside `[0, lemT zB]`).  **Not compiled:** the general `STStep6` from the four regime pins: for arbitrary `(s,t)` the stages that are nonempty depend on `n`, while a pin needs `s_n < t_n` and `(con_st_ind)` for every `n`; S6-13 must split `ℕ` into the finitely many patterns and transfer a pin to a subsequence of the sizes (no `StrictMono` or subsequence declaration in `RBM3D/`, report b; `Sizes d` has five fields), or restate the regime pins with the regime condition inside the index set (as `LWtermEXP` does for `ilambda²/L^d ≤ 1-t`).  The merged `STStep3R`, `STStep4R`, `STStep5R` still carry `STStep2Concl … C_d`: if they are glued by sub-intervals (S5-29) the same restriction question arises there (not checked here).
* **(F-F1)** Regime (ii), `σ₁ = σ₂`: `6:97` cites `(sum_res_2_NAL)`, whose lemma `lem:sum_decay` (`3_5:1632-1637`) needs `t ≤ 1-ilambda²/L²`, incompatible with `1-t < 1-s ≤ ilambda²/L²`; `(sum_res_Ndecay_nonzero)` at `A = ∅` closes it (compiled: `st6_Idiff_same`, `ST_step6_caseII_of_pins`; the negative statement `st6_F1_window_vs_reg5II`: `STCaseI` and `STReg5II` give `t ≤ s`, instance `inst_F1` at `(szB, 15/16, 31/32)`).  Paper-delta candidate `T2191a`.
* **(F-LW)** `lem:LWterm_EXP` is per time; Step 6 integrates over `u`.  The per-time to uniform step is a compiled deterministic lemma (g) and the five bridges at a section; `STEGt = LWE` is the compiled copy of the private `STB_EGt_eq_LWE` (`Induction/Step2Events.lean:1294`, T2080).  `st6_EGtHi_of_LW` derives `(eq:ExpLWn=2)` uniformly from `LWtermEXP`: no separate LW-bridge ticket.
* **(F-ass)** `STMainInd` from the six steps compiles with no change to any merged signature (`ST_mainInd_of_steps`): `STStep1Weak` is consumed only by `STStep2`; Steps 3-6 carry `s < t ≤ lemT` and `STStep1`, `STStep2` carry `s ≤ lemT` (equal under `s < t`); `STStep2` has `∃ C_d ∃ 𝔠_d`, Steps 3-5 `∀ C_d ∃ 𝔠_d` (the assembly passes the `C_d` of Step 2), Step 6 (this probe) `∃ 𝔠_d` only (`STStep2Core`); `STKbound`, `STKward` are discharged by `stKbound_of_flow`, `stKward_of_flow`; Step 6 receives `⟨hS2.1, hS2.2.1⟩` (the loss-free conjuncts).
* **(F-lam)** `(eq:WO)` gives `0 < lam n` eventually (`st6_lam_pos`); the merged `STExp2` has no defect; at `lam n = 0` the target is `(W^{-d}B)^3` (`st6_target_lam_zero`).
* **(F-iv)** The step `(W^{-d}B_{u,0})^{1/5} ≤ C (ilambda² W^d)^{-1/5}` that turns `(eq:Exp(L-K)1)` into the target needs `ilambda² B_{u,0} ≤ C^5`: true in (i)-(iii), false in (iv) (`ilambda² B_{u,0}` is unbounded as `1-u → 0`, section (a) line 12); regime (iv) therefore uses `(eq:Exp(L-K)2)` (`6:63-66`, for `1-u ≤ ilambda²/L^d`) only (`STExpDriftLo`).
* **(F-Inv)** `MLExpInv` (ST-5 file, 878 lines) has no use at `d >= 3`; `STExpInv` stays with Step 5.

## P.9 Mathlib and core names used by the probe, resolved by Lean (script `mathlibnames.py`: each token of the probe, tried under the opened namespaces, with the module that declares it)
```
Classical.choose  [Init.Classical]
Classical.choose_spec  [Init.Classical]
ENNReal.ofReal  [Mathlib.Basic.ENNReal.Basic]
ENNReal.ofReal_le_ofReal  [Mathlib.Basic.ENNReal.Real]
ENNReal.ofReal_lt_ofReal_iff  [Mathlib.Basic.ENNReal.Real]
ENNReal.ofReal_mul  [Mathlib.Basic.ENNReal.Real]
ENNReal.ofReal_natCast  [Mathlib.Basic.ENNReal.Basic]
ENNReal.ofReal_one  [Mathlib.Basic.ENNReal.Basic]
Filter.Eventually.of_forall  [Mathlib.Order.Filter.Basic]
Filter.eventually_ge_atTop  [Mathlib.Order.Filter.AtTopBot.Defs]
Filter.not_eventually  [Mathlib.Order.Filter.Basic]
Filter.tendsto_atTop_mono  [Mathlib.Order.Filter.AtTopBot.Tendsto]
Fin.cast_eq_self  [Mathlib.Data.Fin.Basic]
Fin.isValue  [Lean.Meta.Tactic.Simp.BuiltinSimprocs.Fin]
Finset.card_univ  [Mathlib.Data.Fintype.Card]
Finset.mem_univ  [Mathlib.Data.Fintype.Defs]
Finset.sum_add_distrib  [Mathlib.Algebra.BigOperators.Group.Finset.Basic]
Finset.sum_const  [Mathlib.Algebra.BigOperators.Group.Finset.Basic]
Finset.sum_le_sum  [Mathlib.Algebra.Order.BigOperators.Group.Finset]
Finset.univ  [Mathlib.Data.Fintype.Defs]
Fintype.card  [Mathlib.Data.Fintype.Card]
Fintype.card_fin  [Mathlib.Data.Fintype.Card]
Fintype.ofFinite  [Mathlib.Data.Fintype.EquivFin]
Iff.rfl  [Init.Core]
List.ofFn_succ  [Init.Data.List.OfFn]
List.ofFn_zero  [Init.Data.List.OfFn]
List.prod_cons  [Init.Data.List.Basic]
List.prod_nil  [Init.Data.List.Basic]
Matrix.cons_val_fin_one  [Mathlib.Data.Fin.VecNotation]
Matrix.cons_val_succ  [Mathlib.Data.Fin.VecNotation]
Matrix.cons_val_zero  [Mathlib.Data.Fin.VecNotation]
Matrix.mul_assoc  [Mathlib.Data.Matrix.Mul]
Matrix.trace_mul_comm  [Mathlib.LinearAlgebra.Matrix.Trace]
Matrix.zero_mul  [Mathlib.Data.Matrix.Mul]
MeasureTheory.measure_iUnion_fintype_le  [Mathlib.MeasureTheory.OuterMeasure.Basic]
MeasureTheory.measure_mono  [Mathlib.MeasureTheory.OuterMeasure.Basic]
Nat.cast_nonneg  [Mathlib.Data.Nat.Cast.Order.Ring]
Nat.le_add_right  [Init.Data.Nat.Basic]
Nat.le_self_pow  [Init.Data.Nat.Lemmas]
Nat.pow_le_pow_left  [Init.Data.Nat.Basic]
Nat.reduceAdd  [Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat]
Nat.succ_eq_add_one  [Init.Data.Nat.Basic]
Or.inl  [Init.Prelude]
Or.inr  [Init.Prelude]
Pi.single  [Mathlib.Algebra.Notation.Pi.Basic]
Real  [Mathlib.Basic.Real.Basic]
Real.exp  [Mathlib.Analysis.Complex.Exponential]
Real.exp_pos  [Mathlib.Analysis.Complex.Exponential]
Real.one_le_rpow  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.pow_rpow_inv_natCast  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_le_rpow  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_le_rpow_of_exponent_le  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_le_rpow_of_nonpos  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_neg  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_neg_one  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_nonneg  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_one_add'  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_pos_of_pos  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.rpow_zero  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.sqrt  [Mathlib.Analysis.Real.Sqrt]
Real.sqrt_eq_rpow  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Real.sqrt_le_sqrt  [Mathlib.Analysis.Real.Sqrt]
Real.sqrt_one  [Mathlib.Analysis.Real.Sqrt]
Real.sqrt_sq  [Mathlib.Analysis.Real.Sqrt]
Real.zero_rpow  [Mathlib.Analysis.SpecialFunctions.Pow.Real]
Set.Ico  [Mathlib.Order.Interval.Set.Defs]
Set.Ioo  [Mathlib.Order.Interval.Set.Defs]
Set.mem_empty_iff_false  [Mathlib.Data.Set.Basic]
Set.mem_ofPred_eq  [Mathlib.Data.Set.Operations]
Set.mem_univ  [Mathlib.Data.Set.Operations]
Set.univ  [Mathlib.Data.Set.Defs]
abs_nonneg  [Mathlib.Algebra.Order.Group.Unbundled.Abs]
abs_of_pos  [Mathlib.Algebra.Order.Group.Unbundled.Abs]
add_nonneg  [Mathlib.Algebra.Order.Monoid.Unbundled.Basic]
by_cases  [Mathlib.Basic.Logic.Basic]
by_contra  [Mathlib.Basic.Logic.Basic]
div_le_div_of_nonneg_left  [Mathlib.Algebra.Order.GroupWithZero.Basic]
div_le_iff₀  [Mathlib.Algebra.Order.GroupWithZero.Basic]
div_le_one  [Mathlib.Algebra.Order.Field.Basic]
div_lt_div_of_pos_left  [Mathlib.Algebra.Order.GroupWithZero.Basic]
div_lt_self  [Mathlib.Algebra.Order.Field.Basic]
div_mul_eq_mul_div  [Mathlib.Algebra.Group.Basic]
div_nonneg  [Mathlib.Algebra.Order.GroupWithZero.Basic]
div_one  [Mathlib.Algebra.Group.Basic]
iff_false  [Init.SimpLemmas]
iff_true  [Init.SimpLemmas]
inv_anti₀  [Mathlib.Algebra.Order.GroupWithZero.Basic]
inv_lt_one_of_one_lt₀  [Mathlib.Algebra.Order.GroupWithZero.Basic]
inv_mul_eq_div  [Mathlib.Algebra.Group.Basic]
inv_one  [Mathlib.Algebra.Group.DivInvMonoid]
le_div_iff₀  [Mathlib.Algebra.Order.GroupWithZero.Basic]
le_rfl  [Mathlib.Order.Defs.PartialOrder]
lt_min  [Mathlib.Order.Defs.LinearOrder]
lt_of_le_of_lt  [Mathlib.Order.Defs.PartialOrder]
lt_of_lt_of_le  [Mathlib.Order.Defs.PartialOrder]
lt_trans  [Mathlib.Order.Defs.PartialOrder]
min_le_left  [Mathlib.Order.Defs.LinearOrder]
min_le_right  [Mathlib.Order.Defs.LinearOrder]
mul_comm  [Mathlib.Algebra.Group.Semigroup]
mul_inv  [Mathlib.Algebra.Group.Basic]
mul_le_mul  [Mathlib.Algebra.Order.GroupWithZero.Defs]
mul_le_mul_of_nonneg_left  [Mathlib.Algebra.Order.GroupWithZero.Defs]
mul_le_mul_of_nonneg_right  [Mathlib.Algebra.Order.GroupWithZero.Defs]
mul_nonneg  [Mathlib.Algebra.Order.GroupWithZero.Basic]
mul_one  [Mathlib.Algebra.Group.Monoid]
norm_add_le  [Mathlib.Analysis.Normed.Group.Basic]
norm_le_pi_norm  [Mathlib.Analysis.Normed.Group.Constructions]
norm_num  [Mathlib.Tactic.NormNum.Core]
not_exists  [Init.PropLemmas]
not_lt  [Mathlib.Order.Defs.LinearOrder]
nsmul_eq_mul  [Mathlib.Algebra.Ring.Defs]
one_le_pow₀  [Mathlib.Algebra.Order.GroupWithZero.Basic]
one_mul  [Mathlib.Algebra.Group.Monoid]
one_pos  [Mathlib.Algebra.Order.ZeroLEOne]
pi_norm_le_iff_of_nonneg  [Mathlib.Analysis.Normed.Group.Constructions]
pow_le_pow_left₀  [Mathlib.Algebra.Order.GroupWithZero.Basic]
pow_lt_pow_right₀  [Mathlib.Algebra.Order.GroupWithZero.Basic]
pow_nonneg  [Mathlib.Algebra.Order.GroupWithZero.Basic]
pow_one  [Mathlib.Algebra.Group.Monoid]
sq_abs  [Mathlib.Algebra.Order.Ring.Abs]
sq_nonneg  [Mathlib.Algebra.Order.Ring.Unbundled.Basic]
tendsto_natCast_atTop_atTop  [Mathlib.Order.Filter.AtTopBot.Archimedean]
zero_add  [Mathlib.Algebra.Group.Monoid]
zero_le_one  [Mathlib.Algebra.Order.ZeroLEOne]
zero_pow  [Mathlib.Algebra.GroupWithZero.Basic]
-- 125 names; stderr:  ; exit 0
```
Names that `lake env lean` reports as deprecated in this Mathlib: `dif_pos` ("Use `dite_eq_left` instead"; the probe uses `simp only [..., ↓reduceDIte]`), `Set.mem_setOf_eq` ("Use `Set.mem_ofPred_eq` instead"; used).  Names looked for and not present: none recorded.

## P.10 Scripts (verbatim; `final_run.sh` regenerates every output of the reports from the worktree `RBM3D-wt/T2191`)

### final_run.sh
```
#!/bin/zsh
# T2191: every command whose output the reports paste; outputs in $S/out/.  Run from anywhere.
S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191
WT=/Users/junyin/Lean_proof/RBM3D-wt/T2191
P=RBM3D/Probe/T2191Pins.lean
cd $WT
python3 $S/inv.py summary  > $S/out/inv_summary.txt
python3 $S/inv.py tokens   > $S/out/inv_tokens.txt
python3 $S/inv.py decls    > $S/out/inv_decls.txt
python3 $S/inv.py imports  > $S/out/inv_imports.txt
TOP=7 python3 $S/parts.py MLExpDrift MLExpQ > $S/out/parts.txt
python3 $S/pinstab.py $P   > $S/out/pinstab.txt
python3 $S/split.py        > $S/out/split_sum.txt
python3 $S/split.py table  > $S/out/split_table.txt
python3 $S/split.py compact > $S/out/split_compact.txt
python3 $S/insts.py $P     > $S/out/insts.txt
python3 $S/stmts_full.py $P pins > $S/out/stmts_pins.txt
python3 $S/stmts_full.py $P thms > $S/out/stmts_thms.txt
python3 $S/axioms.py       > $S/out/axioms.txt
python3 $S/axtargets.py    > $S/out/axtargets.txt
python3 $S/clash.py        > $S/out/clash.txt
python3 $S/stmts.py $P 230 STExp2U STIngR6 STStep6R STStep6I STStep6II STStep6III STStep6IV STStep6 STExp2_of_STExp2U ST_mainInd_of_steps ST_step6_caseI_of_pins ST_step6_caseII_of_pins ST_step6_caseIII_of_pins ST_step6_caseIV_of_pins st6_precU_of_forall_seq st6_expAvgU_of_pin st6_EGtHi_of_LW > $S/out/stmts_targets.txt
# --- evidence blocks of prove report (b)
python3 $S/mathlibnames.py > $S/out/mathlib_names.txt
python3 $S/stmts.py $P 200 STStep2Core STRegSeq ST_step6_compose ST_step6R_mono ST_step6_four_of_regimes STGenericPos st6_genericPos_regSeq ST_step6_generic_of_regimes st6_restrict_GdecayW st6_GdecayW_of_zero st6_F1_window_vs_reg5II > $S/out/stmts_glue.txt
cd /Users/junyin/Lean_proof/RBM3D
F="RBM2D/Evolution/Step61.lean RBM2D/Evolution/MLExpVocab.lean RBM2D/Evolution/MLExpHier.lean RBM2D/Evolution/MLExpDuhamel.lean RBM2D/Evolution/MLExpDrift.lean RBM2D/Evolution/MLExpInv.lean RBM2D/Evolution/MLExpQ.lean RBM2D/Evolution/Defs.lean"
{ echo "\$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- $F"; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- ${=F}; } > $S/out/port_diffstat.txt 2>&1
cd $WT
{ print -r -- '$ lake env lean RBM3D/Probe/T2191Pins.lean; echo "exit code $?"'; lake env lean $P; echo "exit code $?"; } > $S/out/lean_env.txt 2>&1
{ print -r -- '$ grep -c -E "\bsorry\b|\badmit\b|native_decide|^axiom |^\s*axiom " RBM3D/Probe/T2191Pins.lean'; grep -c -E "\bsorry\b|\badmit\b|native_decide|^axiom |^\s*axiom " $P; } > $S/out/hygiene.txt 2>&1
{ print -r -- '$ grep -rn "StrictMono\|[Ss]ubseq" RBM3D | grep -vc "^RBM3D/Probe/"'; grep -rn "StrictMono\|[Ss]ubseq" RBM3D | grep -vc "^RBM3D/Probe/"; } > $S/out/nosubseq.txt 2>&1
{ print -r -- '$ git rev-list --count 0818c49..t/T2191'; git rev-list --count 0818c49..t/T2191; print -r -- '$ git diff --stat 0818c49 t/T2191'; git diff --stat 0818c49 t/T2191; print -r -- '$ git status --short | wc -l'; git status --short | wc -l; } > $S/out/gitfacts.txt 2>&1
```

### inv.py
```
#!/usr/bin/env python3
"""T2191 item 1: inventory of the 7 RBM2D Step-6 files at c9a24cf (read-only git show) and the replacement of every import on RBM3D main."""
import subprocess, re, sys, os, collections
R2D = '/Users/junyin/Lean_proof/RBM2D'
R3D = '/Users/junyin/Lean_proof/RBM3D'          # main worktree (read only here)
C = 'c9a24cf'; HEAD = '9e0f275'
FILES = ['Step61', 'MLExpVocab', 'MLExpHier', 'MLExpDuhamel', 'MLExpDrift', 'MLExpInv', 'MLExpQ']
def show(commit, path):
    r = subprocess.run(['git', '-C', R2D, '--no-optional-locks', 'show', f'{commit}:{path}'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
# T2002 portmap: kept lines at 0c1330a, class
t2002 = {}
cur = None
for ln in open(f'{R3D}/docs/reports/T2002-portmap.md', encoding='utf-8'):
    m = re.match(r'^### (\w+) -> RBM3D/(\w+)', ln)
    if m: cur = m.group(1); continue
    m = re.match(r'^\| (\w+)\.lean \| (\d+) \| (-?\d+) \| ([abcd]) \|', ln)
    if m and cur: t2002[f'{cur}/{m.group(1)}'] = (int(m.group(2)), int(m.group(3)), m.group(4))
# plain substrings (occurrence counts reproduce the ticket's Z2 / scaleM / ellT / log L columns) and two regexes for W^2, L^2
TOK = collections.OrderedDict([('Z2', r'Z2'), ('W^2', r'W²|(?:\bW\b|d\.W n : ℝ\)|\(W : ℝ\))\s*\)?\s*\^\s*2\b'),
       ('L^2', r'L²|(?:\bL\b|d\.L n : ℝ\)|\(L : ℝ\))\s*\)?\s*\^\s*2\b'), ('scaleM', r'scaleM'), ('ellT', r'ellT'), ('log L', r'log L')])
def tokens(txt):
    """token -> list of (line number, occurrences on that line)"""
    out = {}
    for k, rx in TOK.items():
        hits = []
        for i, ln in enumerate(txt.split('\n')):
            c = len(re.findall(rx, ln))
            if c: hits.append((i + 1, c))
        out[k] = hits
    return out
def occ(h): return sum(c for _, c in h)
def kept(txt):
    """non-blank lines not starting with `--` (reproduces the ticket's per-file `kept` figures)"""
    return sum(1 for ln in txt.split('\n') if ln.strip() and not ln.strip().startswith('--'))
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|instance|class)\s+([^\s(:{\[⦃]+)')
def decls(txt):
    out = []
    for i, ln in enumerate(txt.split('\n')):
        m = DECL.match(ln)
        if m: out.append((i + 1, m.group(1), m.group(2), 'private' in ln.split(m.group(1))[0]))
    return out
mode = sys.argv[1] if len(sys.argv) > 1 else 'summary'
src = {f: show(C, f'RBM2D/Evolution/{f}.lean') for f in FILES}
hd = {f: show(HEAD, f'RBM2D/Evolution/{f}.lean') for f in FILES}
if mode == 'summary':
    print('file                lines(c9a24cf) kept(c9a24cf) lines(HEAD 9e0f275) kept(0c1330a,T2002) class | public thm/def | occurrences Z2 scaleM ellT "log L" | lines W^2 L^2')
    tot = [0, 0, 0, 0, 0]
    for f in FILES:
        t = src[f]; n = len(t.split('\n')) - 1; nh = len(hd[f].split('\n')) - 1 if hd[f] else -1
        k = t2002.get(f'Evolution/{f}', (0, -1, '?')); kc = kept(t)
        ds = [d for d in decls(t) if not d[3]]
        nth = sum(1 for d in ds if d[1] in ('theorem', 'lemma')); ndf = len(ds) - nth
        tk = tokens(t)
        o = ' '.join(f'{occ(tk[k_]):>5}' for k_ in ('Z2', 'scaleM', 'ellT', 'log L')); l2 = ' '.join(f'{len(tk[k_]):>4}' for k_ in ('W^2', 'L^2'))
        print(f'{f:<19} {n:>6} {kc:>10} {nh:>12} {k[1]:>16}     {k[2]} | {nth:>3}/{ndf:<3} | {o} | {l2}')
        tot[0] += n; tot[1] += kc; tot[2] += nh; tot[3] += k[1]; tot[4] += len(ds)
    print(f'TOTAL               {tot[0]:>6} {tot[1]:>10} {tot[2]:>12} {tot[3]:>16}     c | {tot[4]} public decls')
    d = show(C, 'RBM2D/Evolution/Defs.lean').split('\n')
    sub = '\n'.join(d[106:145]); tk = tokens(sub)
    print(f'Evolution/Defs.lean:107-145 (oneLoopExpErr, expLoopErr, Step61Concl, DecayLoopPT, MLExpConcl): {len(d)-1} lines in file, 39 lines in range, kept {kept(sub)}; occurrences ' + ' '.join(f'{k_}={occ(v)}' for k_, v in tk.items()))
elif mode == 'tokens':
    for f in FILES:
        tk = tokens(src[f])
        print(f'-- {f}')
        for k_, hits in tk.items():
            if hits: print(f'   {k_:<7} occ {occ(hits):>4} lines {len(hits):>4}: ' + ','.join(f'{f}.lean:{h}' for h, _ in hits[:6]) + (' ...' if len(hits) > 6 else ''))
elif mode == 'decls':
    for f in FILES:
        ds = [d for d in decls(src[f]) if not d[3]]
        print(f'-- {f}: ' + '; '.join(f'{d[2]}@{d[0]}' for d in ds if not d[2].startswith('MLExpVocab_') and not d[2].startswith('step61_'))[:1500])
elif mode == 'imports':
    # every import of the 7 files and the used names found in RBM3D main
    idx = collections.defaultdict(list)
    for root, _, fs in os.walk(f'{R3D}/RBM3D'):
        if 'Probe' in root: continue
        for fn in fs:
            if not fn.endswith('.lean'): continue
            p = os.path.join(root, fn)
            for i, ln in enumerate(open(p, encoding='utf-8')):
                m = DECL.match(ln)
                if m: idx[m.group(2).split('.')[-1]].append(f'{os.path.relpath(p, R3D)}:{i+1}')
    imps = collections.OrderedDict()
    for f in FILES:
        for ln in src[f].split('\n'):
            m = re.match(r'^import (RBM2D\.\S+)', ln)
            if m: imps.setdefault(m.group(1), []).append(f)
    alltxt = '\n'.join(src.values())
    idents = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", alltxt))
    for mod, users in imps.items():
        path = mod.replace('.', '/') + '.lean'
        if mod.startswith('RBM2D.Evolution.ML'): continue
        txt = show(C, path)
        if txt is None: print(f'{mod}: not found'); continue
        names = [d[2].split('.')[-1] for d in decls(txt) if not d[3]]
        used = sorted({n for n in names if n in idents})
        found = [(n, idx[n][0]) for n in used if n in idx]
        miss = [n for n in used if n not in idx]
        print(f'{mod} (used by {",".join(users)}; {len(txt.split(chr(10)))-1} lines): used names {len(used)}, same name on RBM3D main {len(found)}, absent {len(miss)}')
        if found: print('    found: ' + '; '.join(f'{n} {loc}' for n, loc in found[:4]) + (' ...' if len(found) > 4 else ''))
        if miss: print('    absent: ' + ', '.join(miss[:8]) + (' ...' if len(miss) > 8 else ''))
```

### decls.py
```
"""Parse the probe: public declarations with namespace, line, kind, name, statement text."""
import re, sys
def parse(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    ns = []
    out = []
    i = 0
    n = len(lines)
    decl_re = re.compile(r'^(private\s+)?(noncomputable\s+)?(theorem|def|abbrev|lemma|structure|instance)\s+([^\s(:{\[]+)')
    while i < n:
        ln = lines[i]
        m = re.match(r'^namespace\s+(\S+)', ln)
        if m: ns.append(m.group(1)); i += 1; continue
        m = re.match(r'^end\s+(\S+)', ln)
        if m and ns and ns[-1] == m.group(1): ns.pop(); i += 1; continue
        m = decl_re.match(ln)
        if m:
            priv = bool(m.group(1)); kind = m.group(3); name = m.group(4)
            # collect until ':=' at end of a line (depth-0 heuristic: first line containing ':=' )
            j = i; text = []
            while j < n:
                text.append(lines[j])
                if ':=' in lines[j]: break
                j += 1
            stmt = ' '.join(t.strip() for t in text)
            stmt = stmt.split(':=')[0].strip()
            # doc comment above
            k = i - 1; doc = []
            if k >= 0 and lines[k].strip().endswith('-/'):
                while k >= 0:
                    doc.append(lines[k])
                    if lines[k].lstrip().startswith('/--') or lines[k].lstrip().startswith('/-!'): break
                    k -= 1
                doc.reverse()
            # full text: until a blank line
            e = i
            while e + 1 < n and lines[e + 1].strip() != '' and not lines[e + 1].startswith('/-') and not decl_re.match(lines[e + 1]):
                e += 1
            full = ' '.join(t.strip() for t in lines[i:e + 1])
            out.append(dict(line=i+1, ns='.'.join(ns), kind=kind, name=name, priv=priv, stmt=stmt, doc='\n'.join(doc), full=full))
            i = j + 1
            continue
        i += 1
    return out
if __name__ == '__main__':
    ds = parse(sys.argv[1])
    for d in ds:
        print(d['line'], d['ns'], d['kind'], d['name'], 'PRIV' if d['priv'] else '')
```

### parts.py
```
#!/usr/bin/env python3
"""Which parts of MLExpDrift / MLExpQ survive the d>=3 exponents: per top-level block, d=2 exponent tokens vs generic content."""
import re, sys, subprocess
R2D='/Users/junyin/Lean_proof/RBM2D'
def show(f):
    return subprocess.run(['git','-C',R2D,'--no-optional-locks','show',f'c9a24cf:RBM2D/Evolution/{f}.lean'],capture_output=True,text=True).stdout
EXP = re.compile(r'scaleM|ratioR|ellT|Real\.log|\bM_u\b|\^\s*2\b|η_u\^{-1}|etaT')
TYP = re.compile(r'\bZ2\b|\bSizes\b|d\.L n|d\.W n')
DECL = re.compile(r'^(?:private\s+|protected\s+)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+(\S+)')
for f in sys.argv[1:]:
    t = show(f).split('\n')
    starts = [(i, DECL.match(l)) for i, l in enumerate(t) if DECL.match(l)]
    rows = []
    for k, (i, m) in enumerate(starts):
        j = starts[k+1][0] if k+1 < len(starts) else len(t)
        body = t[i:j]
        # strip docstring lines of the next decl (preceding comments)
        n = len(body)
        e = sum(1 for l in body if EXP.search(l) and not l.strip().startswith('--'))
        z = sum(1 for l in body if TYP.search(l))
        rows.append((i+1, n, m.group(2), e, z, 'private' in t[i].split(m.group(1))[0]))
    print(f'== {f}: {len(t)-1} lines, {len(rows)} blocks; blocks with exponent tokens (scaleM/ratioR/ellT/log/^2/etaT): {sum(1 for r in rows if r[3]>0)}, lines in them: {sum(r[1] for r in rows if r[3]>0)}; type-only (Z2/Sizes): {sum(1 for r in rows if r[3]==0 and r[4]>0)} blocks, {sum(r[1] for r in rows if r[3]==0 and r[4]>0)} lines; generic: {sum(1 for r in rows if r[3]==0 and r[4]==0)} blocks, {sum(r[1] for r in rows if r[3]==0 and r[4]==0)} lines')
    big = sorted(rows, key=lambda r: -r[1])[:int(__import__('os').environ.get('TOP','8'))]
    for r in big:
        print(f'   {f}.lean:{r[0]:<5} {r[2]:<48} {r[1]:>4} lines  exp-tokens {r[3]:>3}  type-tokens {r[4]:>3} {"(private)" if r[5] else ""}')
```

### pinstab.py
```
#!/usr/bin/env python3
"""Pins table of the T2191 probe: line, name, paper cite, registry class, proof ticket, compiled consumers (theorems whose statement mentions the pin), instances."""
import re, sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191')
from decls import parse
P = sys.argv[1]
ds = parse(P)
pins = [d for d in ds if d['kind'] == 'def' and not d['priv'] and (re.match(r'^(STExp\w+|STStep6\w*|STImproveExpAver|STIngR6|STDriftHi|STStep2Core|STRegSeq|STGenericPos)$', d['name'])) and d['stmt'].rstrip().endswith('Prop')]
pins = [d for d in pins if re.search(r'^\s*(def)', d['stmt'])]
thms = [d for d in ds if d['kind'] == 'theorem' and not d['priv']]
def cite(doc):
    m = re.findall(r'(?:`)?(\d_\d:\d+(?:-\d+)?|6:\d+(?:-\d+)?|3_5:\d+(?:-\d+)?)', doc)
    out = []
    for c in m:
        if c not in out: out.append(c)
    return ','.join(out[:3]) if out else '-'
def cls(doc):
    m = re.search(r'Registry class[^*]*\*\*(\w+)\*\*', doc)
    return m.group(1) if m else ('structural' if 'tructural' in doc else '-')
def ticket(doc):
    m = re.findall(r'S6-\d\d', doc)
    out = []
    for c in m:
        if c not in out: out.append(c)
    return '+'.join(out[:4]) if out else '-'
rows = []
for pd in pins:
    nm = pd['name']
    rx = re.compile(r'\b' + re.escape(nm) + r'\b')
    cons = [t['name'] for t in thms if rx.search(t['stmt']) and (t['name'].startswith('ST_step6_case') or t['name'].startswith('st6_') or t['name'].startswith('ST_mainInd') or t['name'].startswith('ST_step6R') or t['name'].startswith('STExp2_of') or t['name'].startswith('ST_step6_compose'))]
    ins = [t['name'] for t in thms if rx.search(t['stmt']) and t['name'].startswith('inst_')]
    # consumer lines
    cl = []
    for t in thms:
        if t['name'] in cons: cl.append(f"{t['name']}:{t['line']}")
    EXT = {'STExpHier': ['S6-05:proof-of-STExpDuhamelZ/Q(RBM2D expDuhamelPin_of_hier MLExpDuhamel.lean:412)']}
    cl += EXT.get(nm, [])
    cdoc = pd['doc']
    cn = [d for d in ds if d['name'] == nm + 'Concl']
    c1 = cite(cdoc)
    if c1 == '-' and cn: c1 = cite(cn[0]['doc'])
    k1 = cls(cdoc)
    if nm.endswith('Concl'): k1 = 'struct'
    if k1 == '-':
        k1 = 'struct' if (nm.endswith('Concl') or nm in ('STIngR6','STStep6R','STExpAvgAt','STExpAvgU','STExpDuhEq','STExpDuhEqQ','STDriftHi','STExpDriftHiConcl','STExpEGtHiConcl','STExpIntConcl','STExpIntQConcl','STStep2Core','STRegSeq','STGenericPos')) else '-'
    if k1 == 'structural': k1 = 'struct'
    rows.append((pd['line'], nm, c1, k1, ticket(pd['doc']), cl, ins))
mode = sys.argv[2] if len(sys.argv) > 2 else 'table'
if mode == 'table':
    print(f"{'line':>5} {'pin':<22} {'paper':<22} {'class':<8} {'ticket':<9} compiled consumers (file:line) | instances")
    for r in rows:
        print(f"L{r[0]:<4} {r[1]:<22} {r[2][:22]:<22} {r[3]:<8} {r[4]:<9} {' '.join(c.replace('ST_step6_case','case').replace('_of_pins','') for c in r[5])[:70] or '-'} | {' '.join(r[6])[:60] or '-'}")
    print('-- pins (Prop defs):', len(rows), '; classes:', {c: sum(1 for r in rows if r[3] == c) for c in sorted({r[3] for r in rows})})
elif mode == 'noclass':
    print([r[1] for r in rows if r[3] == '-'])
```

### stmts_full.py
```
#!/usr/bin/env python3
"""Full statements (docstrings stripped, source lines verbatim) of every pin (Prop def) and of the glue/endpoint theorems of the T2191 probe."""
import re, sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191')
from decls import parse
P = sys.argv[1]
lines = open(P, encoding='utf-8').read().split('\n')
ds = parse(P)
PIN = re.compile(r'^(STExp\w+|STStep6\w*|STImproveExpAver|STIngR6|STDriftHi|STStep2Core|STRegSeq|STGenericPos)$')
THM = re.compile(r'^(STExp2_of_STExp2U|ST_step6R_of_any|ST_step6R_mono|ST_step6_compose|ST_mainInd_of_steps|ST_step6_case\w+_of_pins|st6_precU_of_forall_seq|st6_expAvgU_of_pin|st6_EGtHi_of_LW|st6_duhEq_of_pin|st6_duhEqQ_of_pin|st6_ini_sumNdecay|st6_ini_nonzero|st6_restrict_\w+|st6_cover_two|st6_GdecayW_of_zero|st6_mollifier_family|ST_step6_four_of_regimes|ST_step6_generic_of_regimes|st6_genericPos_regSeq|st6_F1_window_vs_reg5II)$')
def body(i):
    j = i
    out = []
    while j < len(lines):
        out.append(lines[j])
        if ':=' in lines[j] and (j + 1 >= len(lines) or lines[j + 1].strip() == '' or not lines[j + 1].startswith(' ')):
            break
        if j + 1 < len(lines) and lines[j + 1].strip() == '':
            break
        j += 1
    return out
mode = sys.argv[2]
for d in ds:
    if d['priv']: continue
    if mode == 'pins' and d['kind'] == 'def' and PIN.match(d['name']):
        print(f"-- L{d['line']}"); print('\n'.join(body(d['line'] - 1)))
    if mode == 'thms' and d['kind'] == 'theorem' and THM.match(d['name']):
        # statement only: up to the line containing ':= by' or ':=' at end
        j = d['line'] - 1; out = []
        while j < len(lines):
            out.append(lines[j])
            if lines[j].rstrip().endswith(':= by') or lines[j].rstrip().endswith(':=') or ':= by' in lines[j]:
                break
            j += 1
        print(f"-- L{d['line']}"); print('\n'.join(out))
```

### split.py
```
#!/usr/bin/env python3
"""Split table of the Step-6 proof tickets (T2191 item 6)."""
import sys
# (id, file under RBM3D/Induction, statements, sources, depends, role, est lines, risk)
ROWS = [
 ('S6-01', 'Step6Pins.lean', 'vocabulary STExpErr/ELKLK/EGt/Drift/Target, STStep2Core, STIngR6, STExp2U(+_iff), STStep6R/I-IV/STStep6, STRegSeq, ST_step6R_of_any, the 20 ingredient pins and *Concl, registry lines (Test/Axioms.lean), instances §8', 'probe T2191 §1, §4, §8 (moved)', 'merged Step5Pins, Step34Pins, Defs; none of S6', 'prover', 900, 'low'),
 ('S6-02', 'Step6Kit.lean', 'st6_prec_det_iff, st6_precU_of_forall_seq (g), bridges *_at, ST_mainInd_of_steps, st6_xB_III/IV, st6_cmp_ini, st6_EGt_eq_LWE, st6_EGtHi_of_LW, st6_expAvgU_of_pin, st6_ini_sumNdecay/nonzero, ST_step6_case{I,II,III,IV}_of_pins, st6_restrict_*, st6_cover_two, ST_step6_compose, ST_step6R_mono, ST_step6_four_of_regimes, STGenericPos, st6_genericPos_regSeq, ST_step6_generic_of_regimes', 'probe T2191 §2, §3, §5-§7b (moved, compiled)', 'S6-01; LW-14 (LWtermEXP, premise only); merged stek_*_holds, st_conStInd_sub', 'prover', 1250, 'low'),
 ('S6-03', 'ExpAvg.lean', 'STImproveExpAver (lem:improve_exp_aver, 6:12-21)', 'RBM2D Evolution/Step61.lean (1021 lines, 933 kept; step61 :853: Stein, self-consistent equation, row sum, second moments); row sum from merged ekSameRow_holds', 'S6-01; Gauss/SteinMatrix, LoopFlowStein, DominationAt, XiPins', 'prover-hard', 950, 'medium'),
 ('S6-04', 'ExpHier.lean', 'STExpHier ((eq_L-Keee) at n=2 after expectation)', 'RBM2D Evolution/MLExpHier.lean (731 lines, 648 kept; expHierPin :643) + MLExpVocab ExpHierPin :111', 'S6-01; hierarchyN_holds, deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts, initialLoopValue_two_edges', 'prover', 700, 'medium'),
 ('S6-05', 'ExpDuhamel.lean', 'STExpDuhamelZ, STExpDuhamelQ ((Eexpint_K-L), (int_K-L+QE))', 'RBM2D Evolution/MLExpDuhamel.lean (532 lines, 474 kept; expDuhamelPin_of_hier :412, expQDuhamelPin_of_hier :423) + MLExpVocab qop_source', 'S6-04; GridDuhamelN (Ugen), zeroModeSet_Ugen, QopAlgebra', 'prover-hard', 900, 'medium'),
 ('S6-06', 'ExpEtermsA.lean', 'STExpLKLKHi ((eq:Exp(L-K)1), 6:58-62) with the lattice sum of B e^{-(r/l)^{1/2}}', 'RBM2D Evolution/MLExpDrift.lean (1673 lines, 1545 kept; expDriftBound :1327: structure of the sums, the envelope, decay) re-derived with 11/5; lattice sum new', 'S6-01; Step 4/5 pins; DominationAt (momentDomAt_of_stochDomAt)', 'prover-hard', 1200, 'medium-high'),
 ('S6-07', 'ExpEtermsB.lean', 'STExpDriftLo ((eq:Exp(L-K)2), (eq:ExpLWn=2_smalleta)), STExpDriftDecay ((deccA0) for D_u)', 'RBM2D MLExpDrift.lean (bulk/far numerics) re-derived: (1-u)^{-1}(N(1-u))^{-3}; decay from merged STDecayLoopU', 'S6-03, S6-06; STDecayLoopU (DecayLoopB), stKbound_of_flow', 'prover-hard', 1200, 'medium-high'),
 ('S6-08', 'ExpIntEasy.lean', 'STExpIntIII, STExpIntIV (6:94-96)', 'new (u-integrals x^{-6/5}, x^{-3/2}, (N x)^{-3}); RBM2D MLExpVocab_core :~370 (log integral) as pattern', 'S6-05, S6-06, S6-07; stek_sumNdecay_holds', 'prover-hard', 1100, 'medium'),
 ('S6-09', 'ExpIntI.lean', 'STExpIntI (6:97, 6:104-132)', 'RBM2D MLExpQ.lean (1669 lines, 1533 kept; expQBound :1190, Psum/Qop norm lemmas) + new sum_res_2 integral', 'S6-05, S6-07, S6-10; stek_sumRes2NAL_holds, stek_sumRes2_holds, stQopNorm_holds, stMollifierEx_holds', 'prover-max', 1500, 'high'),
 ('S6-10', 'ExpWardI.lean', 'STExpWardI ((eq:EPL-K), (eq:boundELKQ1), (eq:boundcommutator))', 'RBM2D MLExpQ.lean (eq:p_term_step6 :~1494, commutator_step6 :~1501, Ward)', 'S6-03; KLK_ward, sum_gloop_ward_last_div, STMollifierProps', 'prover-hard', 1100, 'medium-high'),
 ('S6-11', 'ExpIniI.lean', 'STExpIniI (initial term of regime (i), 6:97, 6:117)', 'new (decay of f_s through ≺→𝔼, kernel (sum_res_2_NAL), (sum_res_2), lem_+Q)', 'S6-01; stek_sumRes2NAL_holds, stek_sumRes2_holds, stQopNorm_holds', 'prover-hard', 900, 'medium'),
 ('S6-12', 'ExpIntII.lean', 'STExpIntII, STExpWardII (6:136-147, Ward decomposition 6:138-140)', 'new: regime (ii) is empty at d=2 (L^2 = L^d), no RBM2D source', 'S6-03, S6-05, S6-06; stek_nonzero_holds, norm_zeroModeSet_le, zeroModeSet_Ugen', 'prover-max', 1300, 'high'),
 ('S6-13', 'Step6Glue.lean', 'STStep6 from STStep6I..IV for arbitrary (s,t) (6:93-97): the generic position (every n meets all four regimes) is compiled (ST_step6_generic_of_regimes, S6-02); remaining: the split of N into the finitely many patterns of nonempty stages and the transfer of a pin to a subsequence of the sizes; alternative: restate the regime pins with the regime condition inside the index set', 'analogue of S5-29; merged st_conStInd_sub, st_split_I/II (ScaleFacts3:478-514), bridges *_at, STExp2_of_STExp2U; no sizes-subsequence transfer on main (grep, report b)', 'S6-02, S6-08, S6-09, S6-12, S5-29 (STStep5 as pin)', 'prover-max', 1000, 'high'),
]
if __name__ == '__main__':
    tot = sum(r[6] for r in ROWS)
    if len(sys.argv) > 1 and sys.argv[1] == 'compact':
        for r in ROWS:
            print(f'{r[0]}  Induction/{r[1]:<18} {r[6]:>5}  {r[5]:<12} {r[7]:<12} {r[2][:80]}')
    elif len(sys.argv) > 1 and sys.argv[1] == 'table':
        for r in ROWS:
            print(f'| {r[0]} | Induction/{r[1]} | {r[2]} | {r[3]} | {r[4]} | {r[5]} | {r[6]} | {r[7]} |')
    else:
        import collections
        roles = collections.Counter(r[5] for r in ROWS); risk = collections.Counter(r[7] for r in ROWS)
        n = len(ROWS)
        print(f'tickets {n}; est lines {tot}; mean {tot//n}; min {min(r[6] for r in ROWS)}; max {max(r[6] for r in ROWS)}')
        print('roles:', dict(roles), '| risk:', dict(risk))
        band = 'under 25' if n + 1 < 25 else ('25-40' if n + 1 <= 40 else ('40-50' if n + 1 <= 50 else 'over 50'))
        print(f'DECISIONS §9 O2: ST-5 = 1 design + {n} proof tickets = {n+1}: band {band} (25/40/50): question to Jun: {"no" if n + 1 <= 50 else "yes"}')
```

### insts.py
```
#!/usr/bin/env python3
"""Group the `inst_*` theorems of the probe by data; recompute the regime inequalities of the four data in exact fractions."""
import re, sys
from fractions import Fraction as F
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191')
from decls import parse
ds = [d for d in parse(sys.argv[1]) if d['kind'] == 'theorem' and d['name'].startswith('inst_') and not d['priv']]
def data(d):
    t = d['stmt']
    if d['name'] == 'inst_compose': return '(szB, zB, 7/8, 31/32) two stages (i)+(ii) cut at 15/16'
    if d['name'] in ('inst_four', 'inst_generic', 'inst_genericPos', 'inst_genericPos_regSeq'): return '(szFour, zB, 0, 49/50) all four regimes (generic position)'
    if re.search(r'szB zB \(fun _ => 7 / 8\)', t) or 'inst_hiI' == d['name']: return '(szB, zB, 7/8, 15/16)  regime (i)'
    if re.search(r'szB zB \(fun _ => 15 / 16\)', t) or 'inst_hiII' == d['name'] or d['name'] == 'inst_ini_nonzero': return '(szB, zB, 15/16, 31/32) regime (ii)'
    if re.search(r'szG zB', t) or d['name'] in ('inst_cmp_IV',): return '(szG, zB, 5/8, 3/4)    regime (iv)'
    if re.search(r'sz0 z0 sInst tInst', t) or d['name'] in ('inst_hiIII', 'inst_cmp_III'): return '(sz0, z0, 0, 1/16)     regime (iii)'
    return 'own data (deterministic pin / lemma)'
groups = {}
for d in ds: groups.setdefault(data(d), []).append(d['name'])
print(f'{len(ds)} public instance theorems (RBM.Gauss.Step6Inst), by data:')
for k, v in groups.items(): print(f'  {k}: {len(v)}: ' + ' '.join(v))
print('regime inequalities in exact fractions (g = ilambda; L = 4, except szFour: L = 3):')
rows = [('szB', 'regime (i) ', F(1), 4, F(7, 8), F(15, 16)), ('szB', 'regime (ii)', F(1), 4, F(15, 16), F(31, 32)),
        ('sz0 n=0', 'regime (iii)', F(1, 64), 4, F(0), F(1, 16)), ('szG', 'regime (iv)', F(5), 4, F(5, 8), F(3, 4))]
for name, reg, g, L, s, t in rows:
    g2 = g * g
    print(f'  {name:<8} {reg}: g^2={g2} g^2/L^2={g2/L**2} g^2/L^3={g2/L**3} 1-t={1-t} 1-s={1-s} | '
          f'(i) g2/L2<=1-t<=1-s<=g2: {g2/L**2 <= 1-t <= 1-s <= g2} | (ii) g2/L3<=1-t<=1-s<=g2/L2: {g2/L**3 <= 1-t <= 1-s <= g2/L**2} | '
          f'(iii) g2<=1-t: {g2 <= 1-t} | (iv) 1-s<=g2/L3: {1-s <= g2/L**3}')
g = F(4, 5); L = 3; u3 = 1 - g * g; u2 = 1 - g * g / L ** 2; u1 = 1 - g * g / L ** 3
print(f'  szFour (L = 3, ilambda = 4/5): boundaries 1-g^2 = {u3}, 1-g^2/L^2 = {u2}, 1-g^2/L^3 = {u1}; s = 0 < {u3} < {u2} < {u1} < t = 49/50: {F(0) < u3 < u2 < u1 < F(49, 50)}')
print('  A = g^2 W^d at sz0 n=0: (1/64)^2 * 32^3 =', F(1, 64) ** 2 * 32 ** 3, '; G = A^(-1/5) =', round(float(F(1, 64) ** 2 * 32 ** 3) ** (-0.2), 4))
```

### axioms.py
```
#!/usr/bin/env python3
"""Generate a Lean file importing the probe with `#print axioms` for every public theorem, run it, and summarise."""
import re, sys, subprocess, collections
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191')
from decls import parse
P = 'RBM3D/Probe/T2191Pins.lean'
ds = [d for d in parse(P) if d['kind'] == 'theorem' and not d['priv']]
names = [f"{d['ns']}.{d['name']}" for d in ds]
out = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191/axcheck.lean'
with open(out, 'w') as f:
    f.write('import RBM3D.Probe.T2191Pins\n')
    for n in names: f.write(f'#print axioms {n}\n')
r = subprocess.run(['lake', 'env', 'lean', out], capture_output=True, text=True)
lines = [l for l in r.stdout.split('\n') if 'depends on axioms' in l or 'does not depend' in l]
errs = [l for l in r.stdout.split('\n') if 'error' in l.lower()]
sets = collections.Counter()
got = set()
for l in lines:
    m = re.match(r"'([^']+)' depends on axioms: \[(.*)\]", l)
    if m:
        got.add(m.group(1)); sets[m.group(2)] += 1
    else:
        m2 = re.match(r"'([^']+)' does not depend", l)
        if m2: got.add(m2.group(1)); sets['(none)'] += 1
print(f'print-axioms lines: {len(lines)}; public theorems declared in the probe: {len(names)}; theorems without a line: {sorted(set(names) - got)}; errors: {len(errs)}')
for k, v in sets.items(): print(f'[{k}] : {v} declarations')
print('last line:', lines[-1] if lines else None)
```

### axtargets.py
```
#!/usr/bin/env python3
"""Raw `#print axioms` lines of the target theorems of T2191 (run in the worktree)."""
import subprocess
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191'
T = ['RBM.Gauss.Sizes.STExp2_of_STExp2U', 'RBM.Gauss.Sizes.ST_step6R_of_any', 'RBM.Gauss.Sizes.ST_step6R_mono', 'RBM.Gauss.Sizes.ST_step6_compose', 'RBM.Gauss.Sizes.ST_mainInd_of_steps',
     'RBM.Gauss.Sizes.ST_step6_caseI_of_pins', 'RBM.Gauss.Sizes.ST_step6_caseII_of_pins',
     'RBM.Gauss.Sizes.ST_step6_caseIII_of_pins', 'RBM.Gauss.Sizes.ST_step6_caseIV_of_pins',
     'RBM.Gauss.Sizes.st6_precU_of_forall_seq', 'RBM.Gauss.Sizes.st6_EGtHi_of_LW', 'RBM.Gauss.Sizes.st6_expAvgU_of_pin',
     'RBM.Gauss.Sizes.st6_EGt_eq_LWE', 'RBM.Gauss.Sizes.st6_ini_sumNdecay', 'RBM.Gauss.Sizes.st6_ini_nonzero',
     'RBM.Gauss.Sizes.st6_xB_III', 'RBM.Gauss.Sizes.st6_xB_IV', 'RBM.Gauss.Sizes.st6_cmp_ini',
     'RBM.Gauss.Step6Inst.inst_compose', 'RBM.Gauss.Step6Inst.inst_four', 'RBM.Gauss.Step6Inst.inst_generic', 'RBM.Gauss.Sizes.ST_step6_four_of_regimes', 'RBM.Gauss.Sizes.ST_step6_generic_of_regimes', 'RBM.Gauss.Step6Inst.inst_F1', 'RBM.Gauss.Sizes.st6_F1_window_vs_reg5II', 'RBM.Gauss.Step6Inst.inst_assembly6', 'RBM.Gauss.Step6Inst.inst_skeleton6I', 'RBM.Gauss.Step6Inst.inst_skeleton6II',
     'RBM.Gauss.Step6Inst.inst_skeleton6III', 'RBM.Gauss.Step6Inst.inst_skeleton6IV', 'RBM.Gauss.Step6Inst.inst_endpoints',
     'RBM.Gauss.Step6Inst.inst_precU', 'RBM.Gauss.Step6Inst.inst_G_pos_sz0', 'RBM.Gauss.Step6Inst.inst_normQA2']
open(f'{S}/axtargets.lean', 'w').write('import RBM3D.Probe.T2191Pins\n' + ''.join(f'#print axioms {n}\n' for n in T))
r = subprocess.run(['lake', 'env', 'lean', f'{S}/axtargets.lean'], capture_output=True, text=True)
print(r.stdout.strip()); print(r.stderr.strip()); print('exit', r.returncode)
```

### clash.py
```
#!/usr/bin/env python3
"""Name clash check of the public declarations of the T2191 probe against RBM3D (probe excluded), RBM2D at c9a24cf, RBM1D."""
import re, sys, subprocess, os
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191')
from decls import parse
P = 'RBM3D/Probe/T2191Pins.lean'
ds = [d for d in parse(P) if not d['priv']]
short = sorted({d['name'].split('.')[-1] for d in ds})
full = sorted({f"{d['ns']}.{d['name']}" for d in ds})
print(f'new public declarations in the probe: {len(ds)} ({sum(1 for d in ds if d["kind"]=="def")} def, {sum(1 for d in ds if d["kind"]=="theorem")} theorem); distinct short names {len(short)}; namespaces: {sorted({d["ns"] for d in ds})}')
def files(root, exclude_probe=True):
    out = []
    for r, _, fs in os.walk(root):
        if exclude_probe and 'Probe' in r: continue
        for f in fs:
            if f.endswith('.lean'): out.append(os.path.join(r, f))
    return out
def scan(paths, label):
    rx = re.compile(r'(?<![A-Za-z0-9_.\'])(' + '|'.join(re.escape(n) for n in short) + r')(?![A-Za-z0-9_\'])')
    hits = {}
    for p in paths:
        for i, ln in enumerate(open(p, encoding='utf-8', errors='replace')):
            for m in rx.finditer(ln):
                hits.setdefault(m.group(1), []).append(f'{p}:{i+1}')
    return hits
R3 = '/Users/junyin/Lean_proof/RBM3D-wt/T2191'
h3 = scan(files(R3 + '/RBM3D') + [R3 + '/RBM3D.lean'], 'RBM3D')
print(f'(1) RBM3D worktree (base 0818c49, Probe excluded): short names occurring in {len({v.split(":")[0] for l in h3.values() for v in l})} files: {sorted(h3)[:10]}')
# main HEAD too
mainp = '/Users/junyin/Lean_proof/RBM3D'
head = subprocess.run(['git', '-C', mainp, '--no-optional-locks', 'log', '-1', '--format=%h'], capture_output=True, text=True).stdout.strip()
h3m = scan(files(mainp + '/RBM3D') + [mainp + '/RBM3D.lean'], 'main')
print(f'(2) RBM3D main checkout (HEAD {head}, may hold uncommitted work): hits {sorted(h3m)[:10]}')
h2 = scan(files('/Users/junyin/Lean_proof/RBM2D/RBM2D', False), 'RBM2D')
h1 = scan(files('/Users/junyin/Lean_proof/RBM1D/RBM1D', False), 'RBM1D') if os.path.isdir('/Users/junyin/Lean_proof/RBM1D/RBM1D') else {}
print(f'(3) RBM2D working tree: hits {sorted(h2)[:10]} ; RBM1D: hits {sorted(h1)[:10]}')
```

### stmts.py
```
#!/usr/bin/env python3
"""Print declaration statements of the probe (script-extracted), one line each, truncated."""
import re, sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D-wt/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191')
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191')
from decls import parse
P = sys.argv[1]; mx = int(sys.argv[2]); names = sys.argv[3:]
ds = {d['name']: d for d in parse(P)}
for n in names:
    d = ds.get(n)
    if not d: print(f'?? {n}'); continue
    st = re.sub(r'\s+', ' ', d['full'] if d['kind'] == 'def' else d['stmt'])
    st = st if len(st) <= mx else st[:mx] + ' ...'
    print(f"L{d['line']}: {st}")
```

### cites.py
```
#!/usr/bin/env python3
"""Citation checker: every `File.lean:N[, M...]` in the reports; resolves File.lean in RBM3D (worktree) or RBM2D at c9a24cf; prints the declaration at/near line N and flags citations whose text neighbourhood does not mention it."""
import re, os, sys, subprocess, collections
R3 = '/Users/junyin/Lean_proof/RBM3D-wt/T2191'
R2 = '/Users/junyin/Lean_proof/RBM2D'
C = 'c9a24cf'
files3 = collections.defaultdict(list)
for root, _, fs in os.walk(R3 + '/RBM3D'):
    for f in fs:
        if f.endswith('.lean'): files3[f].append(os.path.join(root, f))
r2files = subprocess.run(['git', '-C', R2, '--no-optional-locks', 'ls-tree', '-r', '--name-only', C], capture_output=True, text=True).stdout.split('\n')
files2 = collections.defaultdict(list)
for p in r2files:
    if p.endswith('.lean'): files2[os.path.basename(p)].append(p)
cache = {}
def lines3(p):
    if p not in cache: cache[p] = open(p, encoding='utf-8').read().split('\n')
    return cache[p]
def lines2(p):
    if p not in cache: cache[p] = subprocess.run(['git', '-C', R2, '--no-optional-locks', 'show', f'{C}:{p}'], capture_output=True, text=True).stdout.split('\n')
    return cache[p]
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+([^\s(:{\[⦃]+)')
def decl_near(ls, n, w=3):
    out = []
    for i in range(max(1, n - w), min(len(ls), n + w) + 1):
        m = DECL.match(ls[i - 1])
        if m: out.append((i, m.group(1)))
    return out
CIT = re.compile(r'((?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+\.lean):(\d+(?:\s*[,\-]\s*\d+)*)')
for rep in sys.argv[1:]:
    txt = open(rep, encoding='utf-8').read().split('\n')
    print(f'== {rep}')
    nflag = 0; ntot = 0
    for ln_i, ln in enumerate(txt, 1):
        for m in CIT.finditer(ln):
            fpath, nums = m.group(1), m.group(2)
            base = os.path.basename(fpath)
            # resolve: Probe file or RBM3D file or RBM2D file
            cands3 = [p for p in files3.get(base, []) if p.endswith(fpath)]
            cands2 = [p for p in files2.get(base, []) if p.endswith(fpath)]
            ls = None; where = None
            # heuristic: RBM2D files for MLExp*/Step61/Defs-of-Evolution cited with c9a24cf context
            if cands3 and not (base.startswith('MLExp') or base == 'Step61.lean'):
                ls = lines3(cands3[0]); where = 'RBM3D'
            elif cands2:
                ls = lines2(cands2[0]); where = 'RBM2D'
            elif cands3:
                ls = lines3(cands3[0]); where = 'RBM3D'
            else:
                print(f'  L{ln_i}: {fpath}:{nums}  UNRESOLVED'); nflag += 1; continue
            first = int(re.split(r'[,\-]', nums)[0])
            ntot += 1
            ds = decl_near(ls, first)
            ctx = ln[max(0, m.start() - 160): m.end() + 160]
            names = set(re.findall(r'[A-Za-z_][A-Za-z0-9_\'.]*', ctx))
            ok = any(any(part in names for part in [d[1], d[1].split('.')[-1]]) for d in ds)
            if not ok:
                nflag += 1
                print(f'  L{ln_i}: {fpath}:{nums} ({where}) decl near {first}: {ds[:3]}  | line text: {ls[first-1].strip()[:90]!r}')
    print(f'   citations checked {ntot}, not matching a declaration name nearby: {nflag}')
```

### mathlibnames.py
```
#!/usr/bin/env python3
"""T2191 (c): Mathlib/core names used in the probe, resolved by Lean (module of each constant). Tokens of the probe are tried under the namespaces the probe opens."""
import re, subprocess, sys
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191'
P = 'RBM3D/Probe/T2191Pins.lean'
src = open(P, encoding='utf-8').read()
# strip comments and docstrings
src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
src = re.sub(r'--[^\n]*', ' ', src)
toks = sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.₀₁₂₃']*[A-Za-z0-9_'₀₁₂₃]|[A-Za-z_]", src)))
toks = [t for t in toks if len(t) > 3 and ('_' in t or '.' in t)]
lit = ', '.join('"' + t + '"' for t in toks)
lean = f'''import Lean
import RBM3D.Probe.T2191Pins
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  let nss : List Name := [Name.anonymous, `Real, `Finset, `Filter, `MeasureTheory, `ProbabilityTheory, `Matrix, `Set, `Nat, `Fintype, `ENNReal, `NNReal, `Complex, `Fin]
  let toks : List String := [{lit}]
  let mut out : Array String := #[]
  for t in toks do
    let n := t.toName
    for ns in nss do
      let full := ns ++ n
      if env.contains full && !full.isInternal then
        match env.getModuleIdxFor? full with
        | some idx =>
          let m := env.header.moduleNames[idx.toNat]!
          let ms := m.toString
          if ms.startsWith "Mathlib" || ms.startsWith "Init" || ms.startsWith "Std" || ms.startsWith "Lean" then
            out := out.push s!"{{full}}  [{{ms}}]"
          break
        | none => pure ()
  for o in out.qsort (· < ·) do
    logInfo o
'''
open(f'{S}/mathlibnames.lean', 'w').write(lean)
r = subprocess.run(['lake', 'env', 'lean', f'{S}/mathlibnames.lean'], capture_output=True, text=True)
lines = sorted({l for l in r.stdout.split('\n') if re.match(r'^\S+  \[', l)})
print('\n'.join(lines))
print('--', len(lines), 'names; stderr:', r.stderr.strip()[:200], '; exit', r.returncode)
```

