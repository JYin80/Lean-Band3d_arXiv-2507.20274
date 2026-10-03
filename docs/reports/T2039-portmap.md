# T2039 portmap (companion of `docs/reports/T2039-prove.md`; report only)

Ticket T2039 (ST-D2). Sources read, all read-only: RBM2D at `c9a24cf` (`git -C ../RBM2D --no-optional-locks show c9a24cf:<file>`; kept-lines column from `0c1330a`), the paper TeX (`paper/tex/`), `docs/reports/T2002-portmap.md` (classes), the merged RBM3D at `cca94be` (the base of branch `t/T2039`; the probe compiles against it), the T2015 probe `752e027`. `main` has merged since (T2028 `Induction/Defs` `64bdfd3`, T2040, T2041, T2049 `Induction/Step34Pins` `56c30fb`): P.8 F12-F15 record how the probe was reconciled with them (the 24 copied ST-1 pins are identical to the merged `Induction/Defs.lean`; the bundle `STStep2Concl` of T2049 is implied, compiled; one name clash found and removed). No RBM1D/RBM2D text was copied, built or modified. All numbers below are script output (scripts in the session scratchpad: `inv2039.py`, `deps.py`, `regimes.py`, `extract_stmt.py`); the Lean side is `RBM3D/Probe/T2039Pins.lean` on branch `t/T2039` at commit `509cf7d` (all `probe lines` below are those of that commit).

## P.1 Inventory of the 46 RBM2D ST-2 files (item 1)

Command: `python3 inv2039.py table` (files = `Path/*` minus MD (`PerTime, Walk, Transfer, Markov, Stop, Azuma, Step2Props`) minus class d (`ScalesBridge, TailSums`), plus `Induction/{Grid*, AzumaProxyN, StepDecompN, LoopC2N, LoopGenN, QVN, Step2TargetV3, StoppedEndDefs}`). Columns: lines at `c9a24cf`; lines kept at `0c1330a` (`-1` = the file is absent there: `Path/NetLift` was deleted by RBM2D T2274 as dead code; it exists at `c9a24cf` and is the source of `STNetLift2`); class (T2002 portmap section C: b = generalize, c = d=2 argument replaced); exponent tokens (T2002 `stats.py` rule); number of public declarations; public names that files of ST-3..ST-6 (T2002 grouping) mention (word-boundary match, first 6).

| # | file (RBM2D/) | lines c9a24cf | kept 0c1330a | class | tokens | #public | consumed by ST-3..6 (names; groups) |
|---|---|---|---|---|---|---|---|
| 1 | Induction/AzumaProxyN | 2469 | 1540 | b | 16 | 71 | with [ST-3,ST-4,ST-5,ST-6]; testFun_linComb [ST-3]; azumaSubGN [ST-3]; azumaSubGN_instance [ST-3]; azumaSubGN_goodExit_instance [ST-3]; trace_Eblk [ST-3] (+10) |
| 2 | Induction/GridAssemblyN | 1761 | 1171 | b | 4 | 24 | data [ST-3,ST-4,ST-5,ST-6]; assembledN [ST-3] |
| 3 | Induction/GridDriftN | 911 | 850 | b | 32 | 8 | gridDriftN [ST-3]; exists_norm_Kcal_le_win [ST-3]; sizes [ST-3,ST-4,ST-5,ST-6] |
| 4 | Induction/GridDuhamelN | 510 | 235 | b | 2 | 8 | GridDuhamelN_Ugen_add [ST-3]; GridDuhamelN_Ugen_self [ST-3]; GridDuhamelN_Ugen_comp [ST-3]; GridDuhamelN_UgenHom [ST-3]; GridDuhamelN_Ugen_duhamel_telescope [ST-3]; stoppedDuhamelN [ST-3] |
| 5 | Induction/GridEnvelopeN | 713 | 580 | b | 12 | 19 | gridDriftN_envelope [ST-3]; sum_gridStep_div_etaT_le [ST-3]; SumWeightedStepErrN_Stmt [ST-3]; sum_weighted_stepErrN_le [ST-3] |
| 6 | Induction/GridGoodEvent | 852 | 764 | b | 22 | 9 | gridGoodN [ST-3]; GridGoodEvent_exists_le [ST-3]; GridGoodEvent_forall_le [ST-3]; GridGoodEvent_card_Z2 [ST-3]; GridGoodEvent_card_lab [ST-3]; GridGoodEvent_absorb [ST-3] (+1) |
| 7 | Induction/GridGoodN | 1711 | 1074 | b | 2 | 87 | GoodSetN [ST-3]; gridExitTauN [ST-3]; goodExitTauN [ST-3]; gridExitTauN_le [ST-3]; mem_of_lt_gridExitTauN [ST-3]; gridExitTauN_eq_of_forall_mem [ST-3] (+46) |
| 8 | Induction/LoopC2N | 580 | 475 | b | 9 | 6 | hermTestFunLoopN [ST-3] |
| 9 | Induction/LoopGenN | 574 | 536 | b | 11 | 1 | loopGenN [ST-3,ST-5] |
| 10 | Induction/QVN | 738 | 704 | b | 17 | 1 | qvPropagatedN [ST-3] |
| 11 | Induction/Step2TargetV3 | 73 | 43 | c | 0 | 2 | - |
| 12 | Induction/StepDecompN | 1550 | 1154 | b | 4 | 19 | loopFamN [ST-3] |
| 13 | Induction/StoppedEndDefs | 1082 | 686 | b | 7 | 46 | STOeqLevels [ST-3]; G4Inputs [ST-3]; g4Inputs [ST-3]; altB [ST-3]; altQB [ST-3]; TensorInvariantK [ST-3] (+19) |
| 14 | Path/Bootstrap | 419 | 315 | c | 5 | 6 | - |
| 15 | Path/DriftAlgebra | 634 | 602 | b | 24 | 6 | LoopGenN2 [ST-3]; HierarchyN2 [ST-3]; hierarchyN2 [ST-3] |
| 16 | Path/DriftLip | 693 | 91 | b | 60 | 7 | - |
| 17 | Path/DriftPoint | 559 | 478 | c | 9 | 3 | - |
| 18 | Path/DuhamelTail | 967 | 654 | b | 2 | 8 | StoppedAzuma108 [ST-3] |
| 19 | Path/Expansion | 1159 | 978 | b | 19 | 29 | Avec [ST-3]; StoppedDuhamel105 [ST-3] |
| 20 | Path/GoodEvent | 1183 | 1037 | c | 10 | 31 | GoodEvent_gridStep_nonneg [ST-3]; GoodEvent_gridTime_mono [ST-3]; GoodEvent_gridTime_zero [ST-3]; GoodEvent_gridTime_nonneg [ST-3]; GoodEvent_gridTime_le [ST-3]; gridK [ST-3] (+6) |
| 21 | Path/GoodEventClose | 1393 | 1241 | c | 24 | 7 | - |
| 22 | Path/GoodEventGrid | 1336 | 1153 | c | 20 | 10 | - |
| 23 | Path/GoodSet | 873 | 847 | c | 5 | 5 | - |
| 24 | Path/KellStar | 406 | 355 | b | 34 | 6 | kellStarEv [ST-4] |
| 25 | Path/Kernel | 355 | 264 | b | 1 | 18 | ukerMat [ST-3,ST-4,ST-5,ST-6]; ukerMat_self [ST-5] |
| 26 | Path/LemDecCalE | 1258 | 857 | b | 110 | 26 | - |
| 27 | Path/LemDecCalEdif | 1691 | 1664 | b | 81 | 2 | - |
| 28 | Path/LemDecCalEwG | 1402 | 1385 | b | 80 | 2 | - |
| 29 | Path/LoopStep | 429 | 339 | b | 3 | 4 | condExp_loop_drift [ST-3] |
| 30 | Path/NetLift | 1784 | -1 | b | 50 | 6 | data [ST-3,ST-4,ST-5,ST-6] |
| 31 | Path/OneStep | 1692 | 1668 | b | 22 | 6 | genMat [ST-3,ST-5]; envConst [ST-3] |
| 32 | Path/QVForm | 325 | 157 | b | 2 | 7 | - |
| 33 | Path/QVIdentity | 844 | 814 | b | 40 | 6 | QVPropagated [ST-3] |
| 34 | Path/Scales | 344 | 263 | c | 48 | 17 | etaT [ST-3,ST-4,ST-5,ST-6]; ellT [ST-3,ST-4,ST-5,ST-6]; scaleM [ST-3,ST-4,ST-5,ST-6]; tailT [ST-3,ST-6]; ellStar [ST-3,ST-4,ST-6]; etaT_pos [ST-3,ST-5] (+11) |
| 35 | Path/Step2Close | 325 | 133 | c | 2 | 6 | step2TargetNV3_of_GbEXP [ST-6] |
| 36 | Path/Step2Grid | 984 | 836 | c | 2 | 7 | - |
| 37 | Path/Step2Local | 557 | 428 | c | 22 | 3 | - |
| 38 | Path/Step2PropsV3 | 110 | 47 | c | 0 | 2 | Step2Eq53PTV3 [ST-3] |
| 39 | Path/Step2Vocab | 141 | 116 | c | 6 | 15 | loopPM [ST-3,ST-4]; lkMat [ST-3]; greenBlk [ST-3,ST-4,ST-5]; avgErr [ST-3,ST-5]; LLpair [ST-3]; ELKLK [ST-3] (+1) |
| 40 | Path/StepArith | 155 | 120 | c | 0 | 6 | - |
| 41 | Path/StepBound | 1653 | 1618 | c | 14 | 2 | - |
| 42 | Path/StepDecomp | 1553 | 1321 | b | 18 | 19 | HermTestFun [ST-3] |
| 43 | Path/StepDecompLoop | 783 | 637 | b | 22 | 4 | - |
| 44 | Path/TimeSums | 691 | 402 | c | 6 | 5 | - |
| 45 | Path/UBounds | 731 | 657 | b | 4 | 16 | thetaGenMat [ST-3,ST-5]; thetaGen [ST-3]; normSqSpectralMOne [ST-4] |
| 46 | Path/UTransport | 665 | 542 | b | 31 | 7 | - |
| | TOTAL 46 files | 41618 | 31831 | classes {'b': 30, 'c': 16} | 914 | 605 | |

Paper labels (of this paper's TeX) cited by each file, command `python3 inv2039.py labels` (empty = none cited):

```
Induction/AzumaProxyN | alu9_STime, example
Induction/GridAssemblyN | alu9_STime, example, int_K-L_ST
Induction/GridDriftN | def_Ustz, pro_dyncalK
Induction/GridDuhamelN | alu9_STime, def_Ustz, int_K-L_ST
Induction/GridEnvelopeN | int_K-L_ST
Induction/GridGoodEvent | example, lem:STOeq_NQ, lem:STOeq_Qt, lem_decayLoop
Induction/GridGoodN | alu9_STime, def:CALE, example, int_K-L_ST, lem:DIfREP, lem:STOeq_NQ, lem:STOeq_Qt, lem_decayLoop
Induction/LoopC2N | example
Induction/LoopGenN | def_EwtG, eq:mainStoflow
Induction/QVN | def:CALE, defEOTE, def_diffakn_k
Induction/Step2TargetV3 | Eq:Gdecay_w, Gt_bound_flow
Induction/StepDecompN | alu9_STime, int_K-L_ST
Induction/StoppedEndDefs | NALsigm, int_K-L+QE, jywiiwsoks, lem:STOeq_NQ, lem:STOeq_Qt, lem:sum_decay
Path/Bootstrap | Eq:Gdecay_w, Main_DEL_COND, def_WTuD
Path/DriftAlgebra | DefTHUST, Kn2sol, def_ELKLK, def_EwtG, eq:mainStoflow, eq_L-Keee, pro_dyncalK
Path/DuhamelTail | alu9_STime
Path/Expansion | int_K-L_ST
Path/GoodEvent | Eq:Gdecay+IND
Path/GoodSet | GavLGEX, GiiGEX, GijGEX, Gtmwc, con_st_ind, lRB1, lem:main_ind, lem_GbEXP, lem_dec_calE
Path/Kernel | def_Ustz, int_K-L_ST
Path/LemDecCalE | GijGEX, def_ELKLK, def_WTuD, lem_dec_calE, res_deccalE_lk
Path/LemDecCalEdif | defEOTE, lRB1, lem_dec_calE, res_deccalE_dif
Path/LemDecCalEwG | GavLGEX, lRB1, lem_dec_calE, res_deccalE_wG
Path/NetLift | Eq:Gdecay_w, Gt_bound_flow
Path/QVIdentity | alu9_STime, defEOTE, def_diffakn_k
Path/Scales | con_st_ind, def_WTuD, eq:bcal_k, eta
Path/Step2Close | Eq:Gdecay_w, Gt_bound_flow, lem:main_ind, lem_GbEXP
Path/Step2Grid | con_st_ind, example, lem:main_ind
Path/Step2Local | Eq:Gdecay_w, GiiGEX, GijGEX, Gt_bound_flow, Gtmwc, con_st_ind, lem_GbEXP
Path/Step2Vocab | Eq:defGLoop, GijGEX, defEOTE, def_ELKLK, def_EwtG, def_diffakn_k, eq:mainStoflow
Path/UBounds | DefTHUST, def_Ustz, lem:sum_Ndecay
Path/UTransport | TailtoTail, neiwuj
```

Dependency levels inside the 46 files (command `python3 deps.py`; level 0 = no import among the 46):

```
0 Induction/QVN 738 704 b <- 
0 Path/DriftLip 693 91 b <- 
0 Path/GoodSet 873 847 c <- 
0 Path/Kernel 355 264 b <- 
0 Path/NetLift 1784 -1 b <- 
0 Path/Scales 344 263 c <- 
0 Path/Step2PropsV3 110 47 c <- 
0 Path/Step2Vocab 141 116 c <- 
0 Path/StepArith 155 120 c <- 
0 Path/StepDecomp 1553 1321 b <- 
1 Induction/Step2TargetV3 73 43 c <- Path/Step2PropsV3
1 Path/LemDecCalE 1258 857 b <- Path/GoodSet
1 Path/OneStep 1692 1668 b <- Path/DriftLip
1 Path/QVForm 325 157 b <- Path/StepDecomp
1 Path/QVIdentity 844 814 b <- Path/Step2Vocab
1 Path/TimeSums 691 402 c <- Path/Scales
1 Path/UBounds 731 657 b <- Path/Scales,Path/Kernel
2 Path/DriftAlgebra 634 602 b <- Path/Step2Vocab,Path/OneStep,Path/UBounds
2 Path/KellStar 406 355 b <- Path/UBounds
2 Path/LemDecCalEdif 1691 1664 b <- Path/LemDecCalE,Path/Step2Vocab
2 Path/LemDecCalEwG 1402 1385 b <- Path/LemDecCalE
2 Path/LoopStep 429 339 b <- Path/OneStep
2 Path/StepDecompLoop 783 637 b <- Path/StepDecomp,Path/Kernel,Path/UBounds
2 Path/UTransport 665 542 b <- Path/UBounds,Path/Scales,Path/Kernel
3 Induction/LoopGenN 574 536 b <- Path/DriftAlgebra
3 Path/DriftPoint 559 478 c <- Path/LemDecCalE,Path/LemDecCalEwG,Path/UTransport
3 Path/Expansion 1159 978 b <- Path/StepDecompLoop,Path/DriftAlgebra,Path/LoopStep,Path/UBounds,Path/Kernel
3 Path/Step2Local 557 428 c <- Path/GoodSet,Path/KellStar
4 Path/DuhamelTail 967 654 b <- Path/Expansion,Path/Kernel,Path/UBounds,Path/StepDecompLoop
5 Path/GoodEvent 1183 1037 c <- Path/DuhamelTail,Path/GoodSet
6 Induction/GridDriftN 911 850 b <- Path/LoopStep,Path/UBounds,Path/GoodEvent
6 Induction/GridDuhamelN 510 235 b <- Path/GoodEvent
6 Path/Bootstrap 419 315 c <- Path/GoodEvent,Path/Scales
6 Path/GoodEventGrid 1336 1153 c <- Path/GoodEvent,Path/LemDecCalEdif,Path/UTransport,Path/KellStar,Path/QVIdentity,Path/QVForm,Path/StepDecompLoop
7 Path/GoodEventClose 1393 1241 c <- Path/GoodEventGrid
8 Induction/GridGoodN 1711 1074 b <- Induction/GridDuhamelN,Induction/QVN,Path/GoodEventClose,Path/Bootstrap
8 Path/StepBound 1653 1618 c <- Path/GoodEventClose,Path/DriftPoint,Path/TimeSums
9 Induction/GridAssemblyN 1761 1171 b <- Induction/GridGoodN
9 Induction/GridEnvelopeN 713 580 b <- Induction/GridGoodN,Induction/GridDriftN
9 Induction/GridGoodEvent 852 764 b <- Induction/GridGoodN
9 Induction/LoopC2N 580 475 b <- Induction/GridGoodN,Path/StepDecomp
9 Path/Step2Grid 984 836 c <- Path/StepBound,Path/Bootstrap,Path/StepArith
10 Induction/StepDecompN 1550 1154 b <- Induction/LoopC2N,Path/LoopStep,Path/StepDecomp
10 Path/Step2Close 325 133 c <- Induction/Step2TargetV3,Path/Bootstrap,Path/NetLift,Path/Step2Grid,Path/Step2Local
11 Induction/AzumaProxyN 2469 1540 b <- Induction/StepDecompN,Induction/GridGoodN,Induction/LoopC2N,Path/QVForm
12 Induction/StoppedEndDefs 1082 686 b <- Induction/GridGoodEvent,Induction/GridAssemblyN,Induction/LoopC2N,Induction/QVN,Induction/GridEnvelopeN,Induction/AzumaProxyN
```

## P.2 The 16 class-c files: the d = 2 argument and the d ≥ 3 lines that replace it (item 1, second part)

The d = 2 Step 2 (RBM2D "route (D)", paper arXiv:2503.07606 5-6:455–492) propagates the error `𝓛−𝒦` by Duhamel with the transport `𝒰_{u,v}`, localises at `ℓ*_u = (log W)^{3/2} ℓ_u` and closes with the scale `M_u = W² ℓ_u² η_u` through exponents `29/30`; the d ≥ 3 paper replaces it by the self-improving iteration over length scales `K_u` with a Grönwall inequality on the weighted control `Ĵ` and the stopping time `T` (`3_5:345–609`). Column "probe" names the compiled replacement in `RBM3D/Probe/T2039Pins.lean` (`ST_*`, `STStep2…`); "paper" gives the lines of this paper. The file head quoted in each row is the module doc at `c9a24cf`.

| # | file (RBM2D/, lines / kept) | d = 2 argument carried (module doc, `c9a24cf`) | replaced by (paper lines of this paper) | probe |
|---|---|---|---|---|
| 11 | Induction/Step2TargetV3 (73 / 43) | pin `Step2TargetNV3` = `Step2Eq53PTV3` (near exponent 3, route (D), paper-delta #33): `\|𝓛−𝒦\| ≺ [(η_s/η_u)³·1(\|a−b\| ≤ 6ℓ*_u) + 1]·𝒯_{u,D}` | `(Gt_bound_flow)`, `(Gt_avgbound_flow)`, `(Eq:Gdecay_w)` with `((1−s)/(1−u))^{C_d}`, exponent `1/5`, `e^{−(\|a₁−a₂\|/ℓ_u)^{1/2}}`, `+W^{−D}` (1_2:1340–1357) | `STStep2`, `STStep2Local/Avg/Decay`, bridge to the merged bundle `STStep2Concl` (§12.1) |
| 14 | Path/Bootstrap (419 / 315) | grid hand-off `GridStep2PT` of `(Eq:Gdecay_w)`; `firstHit_eq_of_below`, `lk_le_of_jS` (`J* ≤ Λ ⇒ \|𝓛−𝒦\| ≤ Λ𝒯`), `pg_bad_eq_flow` (grid endpoint law = single-time law); port of RBM1D `GridBootstrap` | stopping time `(eq:def2_stopping)` (3_5:533), `(eq:Gronwall_dervJuD)` (3_5:529), Grönwall (3_5:493) | `ST_good_engine`, `ST_model_le_path`, `STstopIdx` |
| 17 | Path/DriftPoint (559 / 478) | the pointwise drift `𝓔^{LK×LK}+𝓔^{(G̃)}` transported to the endpoint by `𝒰_{u,v}` at radius `ℓ*_v`; loss `2e^{2(log W)^{3/4}}`; far cost `2L²W^{−D'}` | `lem:newKLK` (3_5:371–378, proof 610–668) bounds the drift at the grid state in `Ĵ` form; `lem:LWterm`, `lem: EWGn2_N` (3_5:385–415); no transport | `STNewKLKAt`, `STEGt`, `STELKLKM` |
| 20 | Path/GoodEvent (1183 / 1037) | stopping index `gridTau` ∧ good-set exit (`gridTauFull`), initial event `initSet`, grid size `CK/gridK`, `Y/Z` quadratic parts, Chebyshev event at the stopping index, labels `Z2 L × Z2 L` | `T` of `(eq:def2_stopping)`; initial value from `(Eq:Gdecay+IND)` (1_2:1268); grid size = the exponent `C_K` of `Sol_CalL`/`lem:DIfREP` (3_5:134–148, 218–228) | `STstopIdx`, `ST_event_init`, `STGridMartAt` |
| 21 | Path/GoodEventClose (1393 / 1241) | consequence of the Azuma event: `azumaMm`, `xZ_le_azumaMm` (four terms `r^{5/2}1(\|a\|≤5ℓ*)+N^δ r^{19/4}M^{-1/4}+N^{3δ/2}r^{6}M^{-1/2}+1`), `goodEvent_grid`; multiplier loss `e^{2(log W)^{3/4}}` | martingale term via `lem:DIfREP` (3_5:218–228) + `lem: EMn2_N` (3_5:427–440), random-proxy Azuma + Doob (DECISIONS §7) | `STGridMartAt`, `ST_event_mg`, event (E5) in `ST_good_prob` |
| 22 | Path/GoodEventGrid (1336 / 1153) | linear part of the good event: closed-form proxy `cZ` from `lemDecCalE_dif`, `uopPairLocalMax`, `qvPropagated`, `eeShift`; `xZ`, `highProb_azuma_grid'` | the quadratic variation proxy is the actual sum `Σ Δ‖(𝓔⊗𝓔)^{M,(2)}‖` bounded by `lem: EMn2_N` (no closed form) | `STEEM`, `STEMn2Exp`, `ST_event_mg` |
| 23 | Path/GoodSet (873 / 847) | route (D) good set `G(u)` = six clauses (`GijGEX, GiiGEX, asGMc, GavLGEX, lRB1, Gtmwc`), `goodSetPT` from `GbEXPHypV3`, `Step1LoopPT`, `Step1WeakLawPT`; union bound over `N⁹` labels | no good set: Step 1's `(lRB1)`, `(Gtmwc)` are premises (`STStep1Loop/Weak`); `(initialGT2)` is verified at every time section (3_5:28–30) and `lem_GbEXP` is used once at the end | `ST_LW_sections`, `STInitialGT2`, `STLocalAvgOfL2` |
| 34 | Path/Scales (344 / 263) | scales `etaT`, `ellT=min(1/√(1−u),L)` (no `g`), `scaleM` (`M_u=W²ℓ_u²η_u`), `tailT`, `ellStar` (`ℓ*=(log W)^{3/2}ℓ`, 5-6:313); facts F1–F4 (`scaleM_ge_pow29`: `(x_s/x_v)^{29} ≤ M_v`) | merged `etaT`, `ellT` (with `g`), `Bparam`, `tailT`, `tailW` (3_5:311–328, 1_2:1107–1121); `con_st_ind` (1_2:1296) | `ST_tailW_*`, `ST2_Bctl_pos/mono`, `ST_Bdata_holds` |
| 35 | Path/Step2Close (325 / 133) | closure `GbEXPHypV3 ⇒ Step2TargetNV3`; transfer `GridStep2Eq53PT ⇒ Step2Eq53PTV3`; `step2DecayUnif_of_closure` with `step2NetLift` | closing paragraph (3_5:455–465) and the `N^{−C}`-net (1_2:1400) | `STLocalAvgOfL2`, `STNetLift2`, `ST_step2_of_pins` |
| 36 | Path/Step2Grid (984 / 836) | the stopping argument on the grid (5-6:455–492): `K=gridK d D_g (D₁+1)`, profile `N^δ[r³1(\|a−b\|≤6ℓ*)+1]𝒯`, scale facts `scaleM_ge_pow29/anti_ratio/etaT_of_range` | self-improving step and iteration over `K_u`: `(kwr3juw)`–`(eq:def_ell1)` (3_5:520–577) | `ST_selfImprove_section`, `ST_iterate`, `ST_decay_pt` |
| 37 | Path/Step2Local (557 / 428) | `(Gt_bound_flow)` per time from `(Eq:Gdecay_w)` via `goodSetPT`, `kpmBoundProp5` (`\|𝒦\| ≤ 180·40002²(1+log L) M_u^{−1}`), `Step2Local_core` | `(eq:kn2sol_decay)`, `(eq:L2_decay)` (3_5:455–462) then `lem_GbEXP` (3_5:463–465) | `STK2decay`, `ST_L2_decay_pt`, `STLocalAvgOfL2` |
| 38 | Path/Step2PropsV3 (110 / 47) | pin (53) with the single token `5/2` replaced by `3` (route (D), paper-delta #33) | `STStep2Decay` (exponent `C_d`, no localisation) | `STStep2Decay` |
| 39 | Path/Step2Vocab (141 / 116) | 15 loop-vocabulary definitions on `Z2 L`: `loopPM, lkMat, greenBlk, avgErr, loop3, EGt, LLpair, ELKLK, maxLoopPM, gexRHS, loop6, EE, cutDeriv1, cutDeriv2, loopDeriv` | `n = 2` vocabulary of `(def_EwtG)`, `(def_ELKLK)`, `(defEOTE)`, `DefTHUST` (1_2:962, 3_5:97, 176–190, 109–113); general `n` is ST-D3 (T2041) | `STLM, STLKM, STEGtM, STELKLKM, STEEkM, STEEM, STthetaOp, STJhatM` |
| 40 | Path/StepArith (155 / 120) | regime-U arithmetic: `StepEExponentsD` (exponents `−21/29, −11/58, −5/58, −17/58`, `r^{29} ≤ M_t`), `StepECprimeD`, `ThrImproveD` (`J ≤ C N^ε(1+r³)+2, 4C<N^{δ−ε} ⇒ J<N^δ r⁴`) | closure of the bootstrap with the stopping threshold `b^{1/6}`: `c₁Λ²(1+q+log r) r^{3C} b^{1/30} < 1` (3_5:529–577) | `ST_closure_arith`, `ST_alpha_bound`, `ST_hsmall_aux`, `ST_hq_arith` |
| 41 | Path/StepBound (1653 / 1618) | grid step bound on the good event at the first-hit time: five-term split (initial via `sumNdecayEta`/`tailtoTail`, martingale, `Y`, drift via `driftPoint` + `driftTimeSumD`, remainder); constants `r^{5/2}`, `N^{6ε}r³` | pathwise stopped Grönwall on `STGoodAt` (3_5:493, 529–577) | `ST_engine`, `ST_good_engine` |
| 44 | Path/TimeSums (691 / 402) | time sums of the QV and the drift on the grid: Bernoulli left Riemann sums `Δ x_u^{−(p+1)} ≤ (x_v^{−p}−x_s^{−p})/p`, `ρ_u² ≤ r_u` (F1), `M_v ≤ M_u` (F2), `η_s/η_v=x_s/x_v` | only `Σ_j Δ/(1−u_j) ≤ log r` and `Π(1+3CΔ/(1−u_j)) ≤ r^{3C}` (Grönwall, 3_5:493) | `ST_logsum`, `ST_prod_le_rpow`, `ST_gronwall` |

Class-b files that import class-c files at `c9a24cf` (levels 8–12 of the dependency listing above: `GridGoodN`, `GridAssemblyN`, `GridEnvelopeN`, `GridGoodEvent`, `LoopC2N`, `StepDecompN`, `AzumaProxyN`, `StoppedEndDefs`) cannot be ported before ST-D3 (T2041) fixes the general-`n` good event without `GoodSet`/`GoodEventClose`/`Bootstrap`; they are marked in the split table (P.5).

## P.3 Exponent table (item 3)

Notation: `x = 1−u`, `g = ilambda`, `Δ_u = W^{−d}B_{u,0}` (merged `Bctl`), `B_{u,K} = (g²+x)^{−1}(K+1)^{2−d} + (L^d x)^{−1}` (`Bparam`), `ℓ_u = min(max(g x^{−1/2},1),L)` (`ellT`), `𝒯_u(r) = B_{u,r} exp(−(r/ℓ_u)^{1/2})` (`tailT`), `r_u = (1−s)/(1−u)`, `b_u = Δ_u`. Regimes of `1−t` (Step 2 runs over all of them, down to `1−t ≥ N^{−1+ε}`):

| | R1 `1−u ≥ g²` | R2 `g²/L² ≤ 1−u ≤ g²` | R3 `g²/L^d ≤ 1−u ≤ g²/L²` | (R4 `N^{−1+ε} ≤ 1−u ≤ g²/L^d`, needed) |
|---|---|---|---|---|
| `ℓ_u` | 1 | `g x^{−1/2} ∈ [1,L]` | `L` (`ℓ_u = L` for `x ≤ g²/L²`, `ellT_eq_of_le`) | `L` |
| `B_{u,0}` | `≍ x^{−1}` (first term) | `≍ g^{−2}` | `≍ g^{−2}` (zero mode `(L^d x)^{−1} ≤ g^{−2}`) | `≍ (L^d x)^{−1}` (zero mode) |
| `Δ_u` | `≍ W^{−d}x^{−1}` | `≍ (g²W^d)^{−1} ≤ W^{−2𝔡}` | `≍ (g²W^d)^{−1} ≤ W^{−2𝔡}` | `≍ (N x)^{−1} ≤ N^{−ε}` |
| `𝒯_u(r)` | `x^{−1}(r+1)^{2−d}` (`ℓ=1`: `e^{−r^{1/2}}` kills `r>0`) | `g^{−2}(r+1)^{2−d}e^{−(r/ℓ_u)^{1/2}}` | same with `ℓ=L`: `e^{−(r/L)^{1/2}}` of constant order | `(L^d x)^{−1}` flat for `r ≲ L` |
| tail floor | `𝒯̃^ℓ_{u,D} = max(𝒯_u(r∧ℓ), W^{−D})`, `W^{−D} ≤ N^{−𝔠D}` | | | |

Numbers at the preflight sequence `sz0`, `n = 0` and along `sz0` (command `python3 regimes.py`; identical to section (a) of the prove report):

```
d=3 L=4 W=32 g=0.015625 N=(WL)^d=2097152; thresholds: g^2=0.0002441  g^2/L^2=1.526e-05  g^2/L^d=3.815e-06  N^(-1+eps)=2.044e-06 (eps=1/10)
regime | x=1-u | ell_u | B_{u,0} | first term | zero-mode | W^-d B_{u,0} | W^-d B_{u,1} | T_u(L) | r=(1-s)/(1-u) at s=0.5
R1 x>=g^2                    | 0.5 | 1 | 2.03 | 1.999 | 0.03125 | 6.196e-05 | 3.146e-05 | 0.05834 | 1
R2 g^2/L^2<=x<=g^2           | 0.0001 | 1.562 | 3062 | 2906 | 156.2 | 0.09345 | 0.04911 | 148.9 | 5000
R3 g^2/L^d<=x<=g^2/L^2       | 8e-06 | 4 | 5919 | 3966 | 1953 | 0.1806 | 0.1201 | 1010 | 6.25e+04
R4 x<g^2/L^d (inside range)  | 3e-06 | 4 | 9255 | 4046 | 5208 | 0.2824 | 0.2207 | 2214 | 1.667e+05
exponents: weak law (Gtmwc) 1/4; output 1/5; stopping threshold 1/6 (J<Delta_u^(1/6)); stretched exp (r/ell)^(1/2); martingale (Delta^(1/2)+J^3)^(1/2)
closure of the skeleton: (3C+1) c_d <= 1/60, C_d=3C+1, c_d<=1/100; r^C_d Delta^(1/5)<=Delta^(1/6) needs C_d c_d<=1/30; Lambda=2N^eps1 absorbed by Delta^(1/60), eps1<=c/400
  C=1: C_d=4  c_d<=min(1/100,1/(60 C_d))=0.0041667  r_max=Delta_t^(-c_d)=1.0099 at Delta_t=0.0934
  C=3: C_d=10  c_d<=min(1/100,1/(60 C_d))=0.0016667  r_max=Delta_t^(-c_d)=1.004 at Delta_t=0.0934
  C=10: C_d=31  c_d<=min(1/100,1/(60 C_d))=0.00053763  r_max=Delta_t^(-c_d)=1.0013 at Delta_t=0.0934
limit along sz0: n, N^-1/2... see W^-d B_{t,0} <= (g^2 W^d)^-1+(N x)^-1 with x=N^(-1+eps):
  n=0: W=32 L=4 g=0.0156 (g^2 W^d)^-1=0.125  N^-eps=0.2333
  n=1: W=1024 L=8 g=0.000244 (g^2 W^d)^-1=0.01562  N^-eps=0.06699
  n=3: W=32768 L=16 g=3.81e-06 (g^2 W^d)^-1=0.001953  N^-eps=0.01924
  n=9: W=3200000 L=40 g=1.56e-08 (g^2 W^d)^-1=0.000125  N^-eps=0.003697
  n=99: W=320000000000 L=400 g=1.56e-14 (g^2 W^d)^-1=1.25e-07  N^-eps=5.859e-05
  n=999: W=32000000000000000 L=4000 g=1.56e-20 (g^2 W^d)^-1=1.25e-10  N^-eps=9.286e-07
```

Exponents and constants of the Step 2 closure (all constants before the sequence; `C` = the constant of `lem:newKLK`, a function of `(d, κ, 𝔡)`):

| quantity | value | where / constraint | slack |
|---|---|---|---|
| weak law `(Gtmwc)` (1_2:1327) | `1/4` | `lem:newKLK` needs `‖G−M‖_max ≤ δ₀`: `N^{ε₁}Δ^{1/4} ≤ δ₀` (`ST_event_weak`) | `Δ ≤ N^{−c}`, `ε₁ ≤ c/400` |
| output `(Eq:Gdecay_w)` (1_2:1350) | `1/5` | `Ĵ ≺ r^{C_d}Δ^{1/5}` | gap to the stopping threshold `1/30` |
| stopping threshold (3_5:533) | `1/6` | `T = inf{u: Ĵ ≥ Δ_u^{1/6}}`; `(Δ^{1/6})^{3/2} = Δ^{1/4}` closes the QV (3_5:542) | 0 (equality, by definition of `T`) |
| stretched exponent (3_5:311) | `1/2` | `𝒯_u(r) = B e^{−(r/ℓ_u)^{1/2}}`; `(ℓ ≤ (log W)^{10}ℓ_u)` of `lem: EWGn2_N` | `K_m ≤ ℓ_u (m/6)² (d log W+c)²` |
| Grönwall constant (3_5:493) | `3C` | `β_j = 3C/(1−u_j)` from `Θ∘(𝓛−𝒦)` (`C`) + `𝓔^{LK×LK}` (`C(Ĵ+Ĵ²) ≤ 2CĴ` once `Ĵ ≤ 1`) | `r^{3C}` |
| `C_d` (pin) | `3C + 1` | `1 + q + log r ≤ (1+q) r` | independent of `𝔠_d` |
| `𝔠_d` (pin, `con_st_ind` 1_2:1296) | `min(1/100, 1/(60 C_d), 𝔠₀)` | `C_d 𝔠_d ≤ 1/60`: `r^{C_d}b_k^{1/30} ≤ b_t^{1/60}` beats the losses `Λ² = 4N^{2ε₁}` | 1/60 of `Δ`; `𝔠₀` = the constant of `(eq:opt_L2)` |
| loss `Λ = q = 2N^{ε₁}` | `ε₁ = min(τ/6, c/400)` | `c₁Λ²(1+q)b_t^{1/60} ≤ 12c₁* N^{3ε₁−c/60} < 1` | `3ε₁ − c/60 ≤ −11c/1200` |
| closure (`ST_closure_arith`) | `(a₀+r₀+ΣΔ e_j+Λ(…)^{1/2}) r^{3C} < b^{1/6}` | pathwise on `STGoodAt` | `b^{1/30}` |
| scale step (3_5:571) | `𝒯_u(K'_u) = Δ_u^{1/6}𝒯_u(K_u)`, `K ↦ min(L, ·)` | `M(D) ≈ 6(1+D)/c` steps to `𝒯 ≤ W^{−D}` | `ST_decay_of_final` |

d = 2 tokens of RBM2D that change (file:line at `c9a24cf`; commands: `git show c9a24cf:RBM2D/<file> | grep -n <token>`):

| d = 2 token | file:line | d = 2 value | d ≥ 3 replacement |
|---|---|---|---|
| `ellT = min(1/√(1−u), L)` | Path/Scales:41 | no `g` | `min(max(g/√\|1−u\|,1),L)` (merged `ellT`, 1_2:1121) |
| `scaleM = W² ℓ² η` | Path/Scales:44, :115 | `M_u⁻¹ = W^{−2}ℓ_u^{−2}η_u^{−1}` | `Δ_u = W^{−d}B_{u,0}` (`Bctl`) |
| `ℓ* = (log W)^{3/2} ℓ` | Path/Scales:51 | localisation radius (5-6:313) | none: `e^{−(r/ℓ_u)^{1/2}}` inside `𝒯` (3_5:311) |
| `(scaleM)⁻¹ ≤ ((1−t)/(1−s))^{30}` | Path/Scales:197, Step2Local:198, GoodSet:514 | exponent `30` | `Δ_t^{𝔠_d} ≤ (1−t)/(1−s)` (1_2:1296), `C_d𝔠_d ≤ 1/60` |
| `r^{29} ≤ M_t`, `(x_s/x_v)^{29} ≤ M_v` | Path/StepArith:27, :49; Scales:25; Step2Local:219 | exponent `29` | `r^{C_d}Δ^{1/5} ≤ Δ^{1/6}` (`ST_hq_arith`) |
| exponents `21/29, 11/58, 5/58, 17/58` | Path/StepArith:38 | regime-U arithmetic | none (Grönwall closure) |
| `J ≤ C N^ε(1+r³)+2 ⇒ J < N^δ r⁴` | Path/StepArith:45 | thr-improve | `Ĵ ≤ c₁Λ²(1+q+log r)Δ^{1/5}r^{3C}` |
| `(η_s/η_u)^{3}·1(\|a−b\|≤6ℓ*)+1` | Path/Step2PropsV3:40, Step2Close:78 | profile of (53) | `r^{C_d}Δ^{1/5}·W^{−d}𝒯+W^{−D}` |
| `r^{5/2}, N^{6ε}r³, r^{19/4}M^{−1/4}, r⁶M^{−1/2}` | Path/StepBound:88, GoodEventClose:21 | good-event exponents | not present |
| `2e^{2(log W)^{3/4}}` | Path/DriftPoint:46, GoodEventGrid:62 | loss | `Λ = 2N^{ε₁}` |
| `W², L², N=(WL)², Z2 L` | throughout | `d = 2` | `W^d, L^d, N=(WL)^d`, `Zd d L` |

## P.4 Route per pin (item 4)

d-changes common to every row: `Z2 L → Zd d L`, `W² → W^d` (`W^d`-blocks), `N = (WL)² → (WL)^d`, `S^{(B)}` with `g = lam n` (merged `SB`), the d = 2 scales `ellT, scaleM, ellStar` → merged `ellT, Bparam, tailT, tailW, Bctl` (P.2 rows 34, 40), and every exponent redone (P.3). "merged" = declarations of `main` at `cca94be` that the pin uses. Estimated lines are those of the ST-2 split (P.5); "probe" = compiled in `RBM3D/Probe/T2039Pins.lean`.

| pin (probe name; paper lines) | RBM2D source (file:lines at `c9a24cf`) or new | d-changes beyond the common ones | merged declarations reused | est. lines | risk |
|---|---|---|---|---|---|
| `STStep2`, `STStep2Local/Avg/Decay` (1_2:1340–1357) | d = 2 analogue (class c): `Induction/Step2TargetV3:1–73`, `Path/Step2Close:1–325`; **new** assembly `ST_step2_of_pins` (probe §12) | `C_d` independent of `𝔠_d`; `𝔠_d ≤ 1/100`; `C_d𝔠_d ≤ 1/60` | `Sizes`, `Prec/PrecPT/PrecGrid/Whp`, `StochDomAt` calculus, `pathH/pathP/filt/gridStep/gridTime/transferLaw/firstHit/isStoppingTime_firstHit_grid`, `lemT`, `mE`, `Bctl`, `tailT/tailW`, `Gt`, `Lloop`, `KLK`, `Theta` | 4210 (probe: compiled, 4 tickets) | low |
| `STNewKLK` (`lem:newKLK`, 3_5:371–378; proof 610–668) | **new**; nearest d = 2 content: `Path/UBounds:48–97,416–486` (`thetaGenMat`, `sumNdecayEta`), `Path/KellStar:39–311` (`kpmBoundProp5`, `thetaMaxNorm`) | `(TTT2)` of `lem:propT`: merged `EKPropT` is in the `ℓ¹` distance, the paper's is `L^∞`: new row ST2-06b (F1, F14); `Θ` decay `prop:ThfadC` (borrowed `Prop5Decay`); profile `𝒯̃^ℓ_{u,D}` (`tailW`); Ward `KLK_ward` (merged, `Loop/KLWard.lean:1123`) | `EKPropT`, `ekPropT_holds`, `KLK_two`, `KLK_ward` (merged, `Loop/KLWard.lean:1123`), `Hierarchy/ContractionBasic`, `tailT_antitone` | 900 | medium |
| `STContractPt` (`ygdhmsgq0`, 3_5:751–797; the Step 2 pointwise form of the merged Step 3 pin `STContract`, F13) | **new**; no RBM2D counterpart | constant `3^d` = neighbour count of `{\|c−c'\| ≤ 1}`; numeric check ratio `0.40` (`W=2, L=3`), `0.39` (`L=4`) | `Hierarchy/ContractionBasic`, `Loop/GLoopFlow` (`norm_loopM_le_sharp`, `Gres`), Ward `Gres(+)Gres(−)` | 650 | medium |
| `STLWB`, `STLWT` (`lem:LWterm` 3_5:385–404, `lem: EWGn2_N` 406–415) | LW gate (T2040, LW-D1): no sister source | statements about the model alone, with the paper's quantifiers | `Gauss/Stein`, graph expansions (LW tickets) | LW gate | owed (LW) |
| `STEMn2Poly`, `STEMn2Exp` (`lem: EMn2_N`, 3_5:427–440; proofs 669–899) | **new**; no RBM2D source | `(𝓔⊗𝓔)^{M,(2;k)}` as 6-loops, contraction inequality, `Ĵ³` feedback (stopped at `Ĵ ≤ Δ^{1/6}`) | `STContractPt`, `STLWB/STLWT` outputs, `KLTree`, `KLCut` | 1000 + 2800 | **high** (d ≥ 3 new estimate) |
| `STGridRepN` (every loop length `m ≥ 2`; `Sol_CalL` 3_5:134–148, `lem:DIfREP` 218–240: `(aaswtghh)` and `(alu9_STime)`; `STGridMart` = case `m = 2`, `ST_gridMart_of_repN` compiled) | `Path/OneStep:49–86,1512`; `Path/StepDecomp:75–181,1160–1273`; `Path/DriftAlgebra:55–103,396,546`; `Path/LoopStep:205–307`; `Path/QVIdentity:345–378,487,705`; `Path/Expansion:48–71,124,406–636`; `Induction/AzumaProxyN` (random proxy); new: random-proxy tail | general-`m` drift `Θ^{(m)}∘(𝓛−𝒦)+Σ_{l=3}^m[𝒦^{(l)}∼(𝓛−𝒦)]+𝓔^{LK×LK}+𝓔^{G̃}` (`(eq_L-Keee)`; at `m = 2` `(LK_simple)`); BDG replaced by Azuma+Doob on the grid (DECISIONS §7); tails in terms of the actual QV `ΣΔ‖𝓔⊗𝓔‖` and of its `𝒰`-weighted form; vocabulary = merged `ThetaN`, `UN`, `uKer` and the copies of T2049's `STLI..STee` with `H` for `ω` | `Path/Azuma`, `Path/Markov`, `Path/Stop`, `Path/Walk` (MD-4/5), `Loop/KLTree` | 1800 + ports (P.5 group C) | medium–high |
| `STstopIdx` (`(eq:def2_stopping)`, 3_5:533) | RBM1D `Gauss/GridBootstrap` (via RBM2D `Path/Bootstrap:1–419`); **probe: compiled** (`STstopIdx_isStoppingTime`) | `T = inf{u: Ĵ ≥ Δ_u^{1/6}}` instead of `J*` threshold ∧ good-set exit | `firstHit`, `isStoppingTime_firstHit_grid`, `lt_firstHit_imp`, `firstHit_le` | 0 | low |
| `STK2decay` (`(eq:simpleboundK)` 3_5:518, `(eq:kn2sol_decay)` 457) | `Path/KellStar:39,240` (`kpmBoundProp5`: constant `180·40002²(1+log L)` of d = 2); **new** for d ≥ 3 | `𝒦^{(2)} ≺ W^{−d}𝒯̃^{L}`; no `ℓ¹`/`L^∞` bridge needed (pointwise, F1) | `KLK_two`, `Prop5Decay` (borrowed) | 450 | low–medium |
| `STStep2Concl` bridge (merged T2049 bundle; probe §12.1) | **probe: compiled** (`ST_concl_of_step2`, `ST_avgU_of_avg`, `ST_step2_concl`) | `STAvgU` is the two-charge `𝓛^{(1)} − 𝒦^{(1)}` form; `STStep2Avg` is the paper's single-charge `tr((G−M)E_a)` | merged `KLK_one`, `Gres`, `seqHflow_isHermitian` | 0 (moves with ST2-04) | low |
| `STNetLift2` (1_2:1400) | `Path/NetLift:1334–1518` (`Step2NetLift`, `Step2LocalUnif`, `Step2LocalNetLift`, `step2NetLift`, `step2LocalNetLift`; absent at `0c1330a`) | index sets, profile `STWB`, `C_d` | `perTimeDomAt_iff_forall_section`, `stochDomAt_of_perTimeDomAt` | 1800 | low |
| `STBdata` (size data) | **probe: proved** (`ST_Bdata_holds`, 150 lines) | `W^{−d}B_{u,0} ≤ W^{−2𝔡} + 4N^{−ε}`, `≥ cB W^{−d}` | `Sizes.lam_sq_mul_pow_ge`, `lemT_ge`, `msc_add_eq_neg_inv` | 0 (move) | low |
| `STScaleExists` (`(eq:def_ell1)`, 3_5:571–577) | **new**, deterministic | IVT on `r ↦ 𝒯_u(r)`; cap at `L`; `K_m ≤ ℓ_u (m/6)² (d log W + c)²`; `M(D) ≈ 6(1+D)/c` | `tailT_antitone`, `tailT_nonneg`, `ellT_*` | 450 | low–medium |
| `STOptL2` (`(eq:opt_L2)`, 3_5:466–512) | **new**; d = 2 has no `ℓ = 0` base (RBM2D starts at `J*` of `Path/GoodEvent`) | linear Grönwall `(eq:Gronwall_2L_max)` with polynomial LW pins, `𝔠_d ≤ 𝔠₀` | `STLWB`, `STEMn2Poly`, `STNewKLK (ℓ = 0)`, `ST_gronwall`, `ST_grid_whp_of_sections` | 1500 | medium |
| `STLocalAvgOfL2` (3_5:455–465) | `Path/Step2Local:198–219` (`Step2Local_core`, `kpmBoundProp5`) d = 2; **new** for d ≥ 3 | `(GijGEX)` neighbour sums `B_{u,r−2} ≤ 3^{d−2}B_{u,r}`, `(GiiGEX)`, `(GavLGEX)`, indicator `Ω(t,ε₀)` | merged ST-1 `STGbEXP` (`lem_GbEXP`, `T2015` pins), `Green/*` | 1500 | medium |

The 16 class-c files as rewrite rows: see P.2 (each row there names its d ≥ 3 replacement and the probe declarations).

## P.5 Split table of the ST-2 proof tickets (item 7)

Command: `python3 mksplit.py` (kept lines from `inv2039.py`; probe section sizes from `grep -n '^/-! ##' RBM3D/Probe/T2039Pins.lean`). Group A moves the compiled probe into `RBM3D/Induction` (pins first: ST2-01), group B proves the pins that are hypotheses of `ST_step2_of_pins` and the two compiled-in-the-probe pieces left (`STScaleExists`, `STNetLift2`), group C ports the class-b files (new names under `RBM3D/Path`, `RBM3D/Induction`). Changes against the first draft, from reconciling with the merged T2041/T2049 (F12-F16): `ST2-06b` is new (the `L^∞` form of `(TTT2)`, F1); `ST2-28a` is new (`HierAlgebra`, `HierarchyN`: T2041 F-D leaves them to ST-2); `StoppedEndDefs` is proposed dropped (F16; the dispatcher confirms); `ST2-08` proves `STContractPt`, not the merged `STContract` (F13). Rows ST2-32..35 need a route without the class-c imports `GoodSet`, `Bootstrap`, `GoodEventClose` (F16); rows ST2-36..39 (`lem_dec_calE` inputs, 3.9k lines; the paper uses `lem_dec_calE` at 3_5:2317, in Step 5) may move to ST-4. Each ticket is 600–1500 lines (the two halves of one RBM2D file are split at the middle). S3 consumers (T2041 P.7): S3-10 needs ST2-32..35, S3-13a needs ST2-27 and ST2-29, S3-21 needs ST2-27, 29, 32.

| ticket | files under RBM3D/ | statements | sources (RBM2D kept lines / probe) | source kept lines | est. lines | depends on | role |
|---|---|---|---|---|---|---|---|
| ST2-01 | Induction/Step2Defs.lean | vocabulary `STLM..STEEM`, measurability, the general-`n` vocabulary (`STLIM..STeeM`, `STgAN`, `STgDriftN`, `STeeUM`), all pins (`STStep2` with the conclusion `STStep2Concl`, `STNewKLK`, `STContractPt`, `STLWB/T`, `STEMn2Poly/Exp`, `STGridRepN` (every loop length; `STGridMart` is its case `m = 2`), `STK2decay`, `STNetLift2`, `STScaleExists`, `STOptL2`, `STLocalAvgOfL2`), registry | probe §1–§2, §12 pins, §12.2 vocabulary and pin | 0 | 930 | S1-07 (T2028, merged), S3-01 (T2049, merged: `STStep2Concl`), MD-3 | prover |
| ST2-02 | Induction/Step2Core.lean | real core, tails, transfer, engine, `STGoodAt`, `ST_good_engine` | probe §3–§8 | 0 | 1300 | ST2-01, MD-4/5 | prover (compiled port) |
| ST2-03 | Induction/Step2Events.lean | grid events from sections, LW premises, `ST_event_*`, `ST_good_prob`, arithmetic | probe §9, §11 (events) | 0 | 1160 | ST2-02, LW pins | prover (compiled port) |
| ST2-04 | Induction/Step2Iterate.lean | `ST_selfImprove_section`, `ST_iterate`, `ST_decay_pt`, `ST_L2_decay_pt`, `ST_base_inv`, `ST_Bdata_holds`, `ST_step2_of_pins`, `ST_avgU_of_avg`, `ST_step2_concl`, `ST_gridMart_of_repN`, `ST_step2_of_pinsN` | probe §10–§12.2 | 0 | 1450 | ST2-03 | prover (compiled port) |
| ST2-05 | Induction/Step2Scale.lean | `STScaleExists` (IVT, caps, floor) | new (3_5:571–577) | 0 | 450 | ST2-02 | prover |
| ST2-06 | Induction/Step2K2.lean | `STK2decay` | new; `Path/KellStar:39,240` | 355 | 450 | ST2-01, `Prop5Decay` (borrowed pin, `Propagator/Pins`), KL (`KLK_two`) | prover-hard |
| ST2-06b | Induction/PropTInf.lean | `(TTT2)` of `lem:propT` for the `L^∞` distance `zdistInf` (ingredient of `STNewKLK`; merged `EKPropT` is `ℓ¹`, F1) | new (paper A:230–258); `EKPropT` | 0 | 700 | EK (`EKPropT`, `tailT_antitone`) | prover-hard |
| ST2-07 | Induction/NewKLK.lean | `STNewKLK` (`lem:newKLK`) | new (3_5:610–668) | 0 | 900 | ST2-06, ST2-06b, `KLK_ward` | prover-hard |
| ST2-08 | Induction/ContractPt.lean | `STContractPt` (`ygdhmsgq0`; not the merged Step 3 `STContract`, F13) | new (3_5:751–797) | 0 | 650 | `Hierarchy/ContractionBasic`, S3-02 (T2054) technique | prover-hard |
| ST2-09 | Induction/EMn2Poly.lean | `STEMn2Poly` (first estimate) | new (3_5:800–825) | 0 | 1000 | ST2-08, LW pins | prover-max |
| ST2-10 | Induction/EMn2Exp1.lean | `STEMn2Exp` part 1 (6-loop bound, `Ĵ³` feedback) | new (3_5:829–860) | 0 | 1400 | ST2-08, ST2-09 | prover-max |
| ST2-11 | Induction/EMn2Exp2.lean | `STEMn2Exp` part 2 (tail profile, `𝒯̃^ℓ` sums) | new (3_5:860–899) | 0 | 1400 | ST2-10 | prover-max |
| ST2-12 | Path/DifREP1.lean | `STGridRepN` part 1 (`Sol_CalL` grid form at every loop length: drift algebra, remainder) | `Path/{OneStep,DriftAlgebra,LoopStep}` ports (group C) | 0 | 900 | ST2-20..22, MD-4/5 | prover-hard |
| ST2-13 | Path/DifREP2.lean | `STGridRepN` part 2 (random-proxy Azuma + Doob tail, plain and `𝒰`-weighted `(alu9_STime)`) | new + `Induction/{AzumaProxyN,GridDuhamelN}` | 0 | 900 | ST2-12, `Path/Azuma` | prover-hard |
| ST2-14 | Induction/OptL2a.lean | `STOptL2` part 1 (events with polynomial pins) | new (3_5:466–480) | 0 | 700 | ST2-03, ST2-07, ST2-09 | prover-hard |
| ST2-15 | Induction/OptL2b.lean | `STOptL2` part 2 (linear Grönwall, `𝔠_d ≤ 𝔠₀`) | new (3_5:481–512) | 0 | 800 | ST2-14 | prover-hard |
| ST2-16 | Induction/LocalAvg1.lean | `STLocalAvgOfL2` part 1 (`(initialGT2)` from `(eq:L2_decay)`, `(GavLGEX)`) | new; `Path/Step2Local:198–219` | 428 | 800 | S1-30 (`lem_GbEXP`) | prover-hard |
| ST2-17 | Induction/LocalAvg2.lean | `STLocalAvgOfL2` part 2 (`(GijGEX)` neighbour sums, `(GiiGEX)`, indicator) | new | 0 | 700 | ST2-16 | prover-hard |
| ST2-18 | Path/NetLift1.lean | `STNetLift2` part 1 (`Step2NetLift`) | `Path/NetLift:1334–1518` (1784 lines at `c9a24cf`) | 892 | 900 | ST2-01, MD-2 | prover |
| ST2-19 | Path/NetLift2.lean | `STNetLift2` part 2 (`Step2LocalNetLift`) | `Path/NetLift` | 892 | 900 | ST2-18 | prover |
| ST2-20 | Path/OneStep.lean (+DriftLip) | `genMat`, `envConst`, `OneStepEnvelope`, `norm_loopDrift_sub_le` | `Path/{OneStep,DriftLip}` | 1759 | 1760 | MD-3 | prover |
| ST2-21 | Path/LoopStep.lean, Path/DriftAlgebra.lean | `condExp_loop_step/drift`, `LoopGenN2`, `HierarchyN2` | `Path/{LoopStep,DriftAlgebra}` | 941 | 940 | ST2-20 | prover |
| ST2-22 | Path/StepDecomp.lean | `gradMat`, `HermTestFun`, `stepDecomp`, `stepDecomp_Z_subG` | `Path/StepDecomp` | 1321 | 1320 | MD-3 | prover |
| ST2-23 | Path/QVIdentity.lean (+QVForm) | `EECutIdentity`, `QVPropagated`, `EEShift`, `v_gradMat_eq_quadVar` | `Path/{QVForm,QVIdentity}` | 971 | 970 | ST2-22 | prover |
| ST2-24 | Path/StepDecompLoop.lean, Path/Kernel.lean | `stepDecomp_loopPM`, `ukerMat`, `Uop`, duhamel telescope | `Path/{StepDecompLoop,Kernel}` | 901 | 900 | ST2-22 | prover |
| ST2-25 | Path/UBounds.lean, UTransport.lean, KellStar.lean | `thetaGenMat`, `sumNdecayEta`, `uopLocalMax`, `tailtoTail`, `kellStarEv` | `Path/{UBounds,UTransport,KellStar}` | 1554 | 1550 | ST2-24, EK (`EKSumNdecay`) | prover |
| ST2-26 | Path/Expansion.lean | `Avec`, `martInc`, `stoppedDuhamel105`, `grid_expansion_all` | `Path/Expansion` | 978 | 980 | ST2-21, ST2-23, ST2-24 | prover |
| ST2-27 | Path/DuhamelTail.lean, Induction/GridDuhamelN.lean | `StoppedAzuma108`, `GridDuhamelN_*` | `Path/DuhamelTail`, `Induction/GridDuhamelN` | 889 | 890 | ST2-26, S3-01 | prover |
| ST2-28 | Induction/LoopGenN.lean, QVN.lean | `loopGenN`, `qvPropagatedN` | `Induction/{LoopGenN,QVN}` | 1240 | 1240 | ST2-21, ST2-23, S3-01 (HierVocab port, merged T2049) | prover |
| ST2-28a | Induction/HierAlgebra.lean, HierarchyN.lean | general-`n` drift algebra `hierarchyN`, hierarchy identities (T2041 F-D: ST-3 files left to ST-2) | `Induction/{HierAlgebra,HierarchyN}` (T2041 P.1; 704 + 38 kept) | 742 | 850 | S3-01 (T2049, merged: `STLI..STee`), ST2-21 | prover |
| ST2-29 | Induction/LoopC2N.lean, GridDriftN.lean | `hermTestFunLoopN`, `gridDriftN` | `Induction/{LoopC2N,GridDriftN}` | 1325 | 1330 | ST2-22, ST2-28, ST2-28a | prover |
| ST2-30 | Induction/StepDecompN.lean | `loopFamN` (general-`n` decomposition) | `Induction/StepDecompN` | 1154 | 1150 | ST2-29 | prover |
| ST2-31 | Induction/GridEnvelopeN.lean, GridGoodEvent.lean | `gridDriftN_envelope`, `GridGoodEvent_*` | `Induction/{GridEnvelopeN,GridGoodEvent}` | 1344 | 1340 | ST2-29, ST2-32, S3-06 (`KcalDecay`) | prover |
| ST2-32 | Induction/GridGoodN.lean | `GoodSetN`, `gridExitTauN` (rewritten without `GoodSet/Bootstrap`) | `Induction/GridGoodN` (imports class c) | 1074 | 1070 | ST2-27, S3-08/09 (`BcalE`), a route without the class-c imports (F-G) | prover-hard |
| ST2-33 | Induction/GridAssemblyN.lean | `assembledN` | `Induction/GridAssemblyN` | 1171 | 1170 | ST2-32 | prover |
| ST2-34 | Induction/AzumaProxyN.lean (part 1) | Azuma proxy, test-function linear combinations | `Induction/AzumaProxyN` lines 1–770 of 1540 kept | 770 | 770 | ST2-30, ST2-32 | prover |
| ST2-35 | Induction/AzumaProxyN.lean (part 2) | `azumaSubGN`, instances | `Induction/AzumaProxyN` | 770 | 770 | ST2-34 | prover |
| ST2-36 | Path/LemDecCalE.lean | `lem_dec_calE` (`GijGEX`, `def_ELKLK` inputs) | `Path/LemDecCalE` | 857 | 860 | ST2-01 | prover |
| ST2-37 | Path/LemDecCalEdif.lean (part 1) | `res_deccalE_dif` | `Path/LemDecCalEdif` | 832 | 830 | ST2-36 | prover |
| ST2-38 | Path/LemDecCalEdif.lean (part 2) | `res_deccalE_dif` | `Path/LemDecCalEdif` | 832 | 830 | ST2-37 | prover |
| ST2-39 | Path/LemDecCalEwG.lean | `res_deccalE_wG` | `Path/LemDecCalEwG` | 1385 | 1390 | ST2-36 | prover |
| total | | | | 25377 | 41300 | | A 4840 + B 13550 + C 22910 |

**Count against DECISIONS §9 O2** (25 / 40 / 50): **41 tickets, 41 300 lines** (group A 4 tickets / 4 840; B 16 / 13 550; C 21 / 22 910). Above 40, not above 50, so no question to Jun before an ST-2 proof ticket starts (the band 25–40 of O2 is exceeded by one: the dispatcher decides at sign-off whether ST2-36..39, which may move to ST-4, stay in ST-2; without them the count is 37); if the high-risk rows split further (ST2-09..11 `lem: EMn2_N`, ST2-12..13 `lem:DIfREP`, ST2-32 `GridGoodN`) the count is 45–47, still below 50. Critical path: ST2-01 → ST2-02 → ST2-03 → ST2-04 (compiled ports, low risk) in parallel with ST2-06b → ST2-07, ST2-08 → ST2-09 → ST2-10 → ST2-11 (`lem: EMn2_N`, the single high-risk chain) and ST2-20 → ST2-22 → ST2-23 → ST2-26 → ST2-12 → ST2-13 (`Sol_CalL` + `lem:DIfREP`); `STStep2` needs all of A, ST2-05, 06, 06b, 07, 11, 13, 15, 17, 19 and the LW tickets (`STLWB/T`).

## P.6 Block Anderson reuse (item 6)

`lem:main_ind_BA` (7_8:1825–1850) is "the same six-step strategy" for the flow `V_t + ilambda Ψ` of `zztE_BA` (7_8:1796): the initial matrix is `H_0 = ilambda Ψ`, `M = M^{(B)} ≠ m I`, `Θ` is built from `M^{(B)}` (`lem:propM`, 7_8:1847: translation invariance, Ward `Σ_b|M_{ab}|² = 1`, Combes–Thomas `C^{-1}ilambda 1(a∼b) ≤ |M_{ab}| ≤ (C ilambda)^{|a−b|}`), and the extra conclusion `(Eq:Gdecay+s<g)` for `1−t ≥ ilambda²` is added.

Carries over verbatim (they never mention the model, only the grid walk, the control `Δ_u`, `Ĵ`, the labels and the pins): `ST_gronwall`, `ST_bootstrap`, `ST_logsum`, `ST_prod_le_rpow`, `ST_pathwise_ineq` (§3); `ST_tail*` (§4, functions of `(d,L,g,u)` only); `ST_PT_of_sections`, `ST_sections_of_PT` (§5, model level only); `ST_whp_grid`, `ST_grid_whp_of_sections` (§5, §9) once the BA grid walk and its transfer law exist (they use `transferLaw` of `pathH`, which has `H_0 = 0`; the docstring of `pathH` in `Path/Walk.lean` says that BA adds `ilambda_0 Ψ` and uses `sz.withLam 0`); `ST_engine`, `STGoodAt`, `ST_good_engine`, `ST_good_prob`, `ST_next`, `ST_decay_of_final`, `ST_iterate`, `ST_decay_pt` (§6–§10: functionals of an abstract loop observable); the arithmetic `ST_hsmall_aux`, `ST_hq_arith`, `ST_L2_cmp`.

What gate BA must add: (1) the BA versions of the model-level vocabulary (`STLM`… are written for an arbitrary fine matrix `H` and `zt E u`, so they apply to `seqHBA`/`Gt_BA` once `STKloop` uses `Mres H_0 z m`); (2) BA versions of the pins `STNewKLK` (`Θ` from `M^{(B)}`), `STK2decay`, `STGridRepN` (drift with `M^{(B)}`, `m(σ_i)` replaced by the BA charge operators in `ThetaN`, `UN`), `STContractPt` (Ward for `M^{(B)}`), `STEMn2*`, `STLWB/T` (LW gate BA), `STLocalAvgOfL2` (`lem_GbEXP_BA` 7_8:1916, with `Φ_t(a,b)` and `c_ilambda` decay instead of the `W^{-d}1_{|a−b|≤1}` term), `STNetLift2`; (3) the size data `STBdata` for `ilambda` of order 1 (then `ℓ_u` and `B_{u,0}` change regime; `Δ_u ≍ W^{-d}` for `1−t ≥ ilambda²`) and the additional estimate `(Eq:Gdecay+s<g)`; (3b) the shifted grid walk `H_0 = ilambda_0 Ψ` and its `transferLaw`; (4) the statement of `STStep2` for the flow of `zztE_BA` (`t_0`, `E`, `ilambda_0 = √t_0 ilambda`), i.e. a second `STStep2_BA` pin with the same constants-before-sequence shape.

## P.7 Registry classes of the `Prop`s taken as hypotheses (DECISIONS §16, §20)

Every `Prop` that a compiled theorem of the probe takes as a hypothesis and that no existing ticket proves (class proposed; "owed" = proved by a later ticket, "borrowed" = external result authorised in DECISIONS §5, "structural" = data condition):

| Prop (probe) | used by | class | proving ticket |
|---|---|---|---|
| `STNewKLK` | `ST_step2_of_pins` | owed | ST2-07 (uses borrowed `Prop5Decay`, merged `EKPropT`, `KLK_ward`) |
| `STLWT` | `ST_step2_of_pins`, `ST_LW_sections` | owed | LW gate (T2040 LW-D1 pins the same statement; reconcile at sign-off) |
| `STLWB` | (base case `STOptL2`, not used by the skeleton) | owed | LW gate |
| `STEMn2Exp` | `ST_step2_of_pins`, `ST_LW_sections` | owed | ST2-10, ST2-11 |
| `STEMn2Poly` | (base case `STOptL2`) | owed | ST2-09 |
| `STContractPt` | (inside the proofs of `STEMn2*`) | owed | ST2-08 (the merged `STContract` of T2049 is the Step 3 pin, proved by T2054; different statement, F13) |
| `STGridRepN` | `ST_step2_of_pinsN` (via `ST_gridMart_of_repN`: `STGridMart` = its case `m = 2`, used by `ST_step2_of_pins`, `ST_selfImprove_section`); ST-3 (S3-10, S3-13a, S3-21) | owed | ST2-12, ST2-13 (+ ST2-27, 34, 35 for the weighted tail) |
| `STK2decay` | `ST_step2_of_pins` | owed (uses borrowed `Prop5Decay`) | ST2-06 |
| `STNetLift2` | `ST_step2_of_pins` | owed | ST2-18, ST2-19 |
| `STScaleExists` | `ST_step2_of_pins` | owed (deterministic) | ST2-05 |
| `STOptL2` | `ST_step2_of_pins` | owed | ST2-14, ST2-15 |
| `STLocalAvgOfL2` | `ST_step2_of_pins` | owed (uses merged-by-S1 `STGbEXP`) | ST2-16, ST2-17 |
| `STStep2` | consumer: ST-3..ST-6 (`STStep2Concl` of T2049 is implied: `ST_step2_concl`) | owed | `ST_step2_of_pins` (ST2-04) |
| `STInitialGT2`, `STLWassm`, `STLWassmExp` | premises of `STLWB/T`, `STEMn2*` | owed (ST chain) | Step 1 / ST-6 induction |
| `STPsiClass` | premise of `STLWB`, `STEMn2Poly` | structural | (data condition on a deterministic profile) |
| `STLK`, `STDecay`, `STStep1Loop`, `STStep1Weak`, `STConStInd`, `STFlow` | premises of `STStep2` (copies of T2015 pins, identical to the merged `Induction/Defs.lean`) | as registered by T2028 (§16, §19) | S1-07 (merged) |
| `STStep2Concl`, `STLocalEntryU`, `STAvgU`, `STGdecayW` | merged by T2049 (`Step34Pins.lean:192-226`); copied in the probe §12.1 | owed (proved by ST2-04 through `ST_step2_concl`) | ST2-04 |
| `STScaleAdm`, `STScaleOk`, `STScaleInv`, `STSelfImp`, `STL2decayPT` | internal predicates (no consumer outside ST-2) | not registered (definitions used inside ST-2 proofs and in `STScaleExists`) | — |

`STBdata` is **not** in the list: it is proved in the probe (`ST_Bdata_holds`).

## P.8 Findings (carried into section (d) of the prove report)

* **F1 (`ℓ¹` vs `L^∞`, `(TTT2)`).** The paper's `|·|` is the periodic `L^∞` norm (1_2:274) and `lem:propT` `(TTT2)` is stated for it (3_5:328, proof A:230-258). The merged `EKPropT` (`Evolution/Pins.lean:139`; EK design T2016, `ℓ¹` throughout, cf. T2016f) is stated for `zdistD` (`ℓ¹`): `ρ_∞ ≤ ρ_1 ≤ dρ_∞`, but `𝒯_u(r/d)` has the weaker exponential `e^{−(r/(dℓ_u))^{1/2}}`, so the `L^∞` convolution bound does not follow from the `ℓ¹` one by monotonicity or constants. `STNewKLK` (`(juwo2=klk)`, `(juwo=Lklk)` use `(TTT2)` with `|·|_∞`, 3_5:615-668) needs it in the paper's metric: new row ST2-06b (paper-delta candidate T2039f); numeric evidence F14. `STK2decay` needs **no** bridge: `Prop5Decay` is pointwise, `|Θ(0,a)| ≤ C B_{u,|a|_1}e^{−c|a|_1/ℓ_u} ≤ C e^{1/(4c)} B_{u,|a|_∞}e^{−(|a|_∞/ℓ_u)^{1/2}}` (`|a|_1 ≥ |a|_∞`, `B` nonincreasing in `K`, `cρ ≥ √ρ − 1/(4c)`).
* **F2 (no numerals).** The paper fixes no numeral for `C_0`, `C_d`, `𝔠_d` ("sufficiently small depending on `C_0`", 3_5:509). The pins keep them as constants before the sequence (`STStep2`: `∃ C_d, ∃ 𝔠_d ≤ 1/100`, `C_d` chosen first); the compiled closure fixes `C_d = 3C+1`, `𝔠_d = min(1/100, 1/(60C_d), 𝔠₀)` (`C` = constant of `lem:newKLK`, `𝔠₀` of `(eq:opt_L2)`).
* **F3 (two light-weight families).** The base `(eq:opt_L2)` (3_5:466–512) needs the polynomial pins (`STLWB`, `STEMn2Poly`, `Ψ_t² = W^{−c_0}`); `STLWT`/`STEMn2Exp` at `ℓ = 0` would be circular (their premise `(eq:LW_assm_exp)` at `ℓ = 0` is `(ksjjuw)`, which follows from `(eq:opt_L2)`). Both families are therefore inputs (LW gate).
* **F4 (contraction inequality).** `STContractPt` with the constant `3^d/(W^d Im z)` (`3^d` = number of `c` with `|c−c'| ≤ 1`): numeric ratio of the two sides `0.40` (`d=3, W=2, L=3`, N=216) and `0.39` (`L=4`, N=512); pointwise `𝓛^{(6)} ≤ (𝓛^{(4)})^{1/2}|𝓛^{(3)}|`-type factor max `0.97`/`0.91`; verbatim script output (`python3 contract.py`): `d=3 W=2 L=3 N=216: min Re L6 = 2.283e-12 (>=0); max pointwise L6/(sqrt(L4alt)*|L4'|) = 0.9734; max LHS/RHS(const 3^d) = 0.4018`. The constant is not sharp but valid in the samples.
* **F5 (`lem:newKLK` is deterministic).** The proof (3_5:610–668) uses Cauchy–Schwarz, Ward's identities and `(Gtmwc)` only through `Im tr(G E_a) ≤ Im m + δ₀`; the pin `STNewKLKAt` is therefore deterministic for every Hermitian `H` with `‖G−M‖_max ≤ δ₀` (the paper's "w.h.p." is the weak-law event); `lam` range `0 < ilambda ≤ 𝔡^{-1}` must be matched against the range of validity of `EKPropT`/`prop:ThfadC` by ST2-07.
* **F6 (quantifier over `D`).** "For any large `D`" in `lem: EWGn2_N`, `lem: EMn2_N` is equivalent to `∀ D > 0` because `𝒯̃^ℓ_{t,D}` decreases in `D` (assumption and conclusion); the pins quantify `∀ D > 0` in both.
* **F7 (scales beyond `L`).** The solution of `(eq:def_ell1)` may exceed `L` (the paper uses `𝒯̃^K ≍ 𝒯̃^L`, 3_5:578); `STScaleAdm` cuts the family at `L`: `𝒯_u(K_{m+1}) ≥ Δ_u^{1/6}𝒯_u(K_m)` and, after `M(D)` steps, `𝒯_u(K_M) ≤ W^{−D} ∨ K_M ≥ L`.
* **F8 (no stopping-time calculus in the skeleton).** The endpoint bound is proved pathwise on a good event of the grid walk (`ST_good_engine`, then `ST_model_le_path` and `transferLaw`); `STstopIdx` is a stopping time of the grid filtration (`STstopIdx_isStoppingTime`, compiled) and is needed only inside the proof of `STGridMart` (Azuma with the random proxy).
* **F9 (regime R4).** `N^{−1+ε} ≤ 1−t < g²/L^d` is inside the Step-2 range (preflight (a), table row R4); `Bparam` is used for every `x > 0` and `ST_Bdata_holds` covers it.
* **F10 (`W^τ` versus `N^τ`).** Every `W^{τ}` is converted at the scale `N`: `N^{−c} ≤ W^{−dc}` (`ST_size_rpow_neg_le`), `W^{−D_i} ≤ N^{−𝔠D_i}` (`(Main_DEL_COND)`), `W → ∞` from `W ≥ N^𝔠` (`ST_W_tendsto`); the losses `N^{ε₁}` of the bootstrap are absorbed by `Δ^{1/60}` with `ε₁ ≤ c/400`.
* **F11 (the closure needs `lam > 0` and `lam ≤ 𝔡^{-1}` only eventually).** `STK2decay`, `STNewKLK` carry these as premises; the skeleton obtains them from `(eq:WO)` eventually in `n`.
* **F12 (bridge to the merged Steps 3-4 bundle).** T2049 merged `STStep2Concl = STLocalEntryU ∧ STAvgU ∧ STGdecayW` (`Induction/Step34Pins.lean:221`); its docstring says the pins of T2039 must imply it. Probe §12.1 copies the four definitions verbatim (tagged with their lines at `56c30fb`; script `cmp_defs.py`: IDENTICAL) and compiles `ST_concl_of_step2`, `ST_step2_concl` (`STStep2` with the conclusion `STStep2Concl`), `inst_step2_concl`, `inst_skeleton_concl`. `STLocalEntryU`, `STGdecayW` are `STStep2Local`, `STStep2Decay` word for word; `STAvgU` is the two-charge form `Lloop − STKloop ≺ Bctl^1`, derived from `STStep2Avg` (single charge, `Lloop − mE`, the paper's `tr((G_u − M)E_a)`) by `𝓛^{(1)}_- = conj 𝓛^{(1)}_+` and `𝒦^{(1)}_σ = m(σ)` (`ST_Lloop_one_false`, `ST_Kloop_one`, `ST_avgU_of_avg`). The 24 ST-1 copies of the probe (§0) are identical to the merged `Induction/Defs.lean` (T2028): after merging, the probe's pins bind to the merged names unchanged.
* **F13 (name clash `STContract`).** T2049 merged `RBM.Gauss.Sizes.STContract` for the Step 3 inequality `(yi2oslxj2)`, `(u2jzooi-2)` (`Step34Pins.lean:307`, proved by T2054). The probe's pin for the Step 2 inequality `ygdhmsgq0` (3_5:751; the paper: "a pointwise version of `(u2jzooi-2)`") had the same full name with a different statement; renamed `STContractPt`. The pointwise form keeps the label-dependent maxima `max_{c'∈𝒜}(𝓛^{(4)}_{alt}(c',b,c',b))^{1/2}` and `𝓛^{(3)}(a,b,a)` that the merged form (maxima over all labels, `STmaxL`) does not give, so ST2-08 stays a separate ticket (same technique: Ward + Cauchy-Schwarz). Script `fqn_clash.py` (namespace-aware, against `main` at the check time): 1 clash before the rename, 0 after.
* **F14 (extreme inputs, TEAM §8 lesson 25).** (a) `(TTT2)`, the core of `STNewKLK` (`ttt2.py`, FFT on `Z_L^3`): `R = max_a (1−u)(𝒯_u*𝒯_t)(a)/𝒯_t(|a|)`. Extreme regime (ii) `u = t`, `1−t = g²/L^d`: `R_∞ ≤ 0.87` (`L = 6..24`, `g = 0.5, 0.1`); `1−u = g²/L²`, `1−t = g²/L^d`: `≤ 2.4`; `1−u = 1−t = 10^{-3}g²/L^d`: `≤ 0.62`. Regime (i) `u = t`, `1−t = 0.5`, `g = 0.1`: `R_∞` = 107 / 293 / 646 / 916 / 1111 and `R_{ℓ¹}` = 74 / 167 / 283 / 330 / 341 at `L` = 12 / 24 / 48 / 72 / 96: both saturate (increments shrink), the `L^∞` constant is about 3 times the `ℓ¹` one; consistent with a finite `d`-dependent constant (the pin has no explicit constant). (b) `STK2decay` (`theta_decay.py`): `max_a |Θ_{uM}(0,a)|/(B_{u,|a|_∞}e^{−(|a|_∞/ℓ_u)^{1/2}})` over 120 rows (`L ≤ 48`, `g ∈ {0.5, 0.1}`, `M ∈ {1, −1, e^{2πi/3}}`, `1−u` from 0.5 down to `10^{-3}g²/L^d`): maximum 2.028. (c) `STContractPt`: ratio ≤ 0.40 for `η` down to 0.005, band and full `H` (F4); the instance `inst_contractPt` is at the constant tensor `H = 0`, `z = i`. (d) `STNewKLK` at `H = 0`, `u = 0` (`G = M`, `Ĵ = 0`): `inst_newKLK`. (e) `STStep2Local/Avg` at the extreme `1−u = g²/L^d` (`mat_extreme.py`, output below in the prove report b.6: `d = 3`, `W = 2`, `g = 0.5`, `E = 0`, band `H`; `Nη = 2`, while Step 2 needs `Nη ≥ N^ε`): `L = 3` (N = 216, 80 samples): mean `|(G−M)_{xy}|²/(W^{-d}B_{u,|x−y|/W})` over the distance classes 0-5 in [0.68, 0.75], maximum over samples and entries 56, `max_a|tr((G−M)E_a)|/(W^{-d}B_{u,0})` 0.80; `L = 4` (N = 512, 40 samples): [0.71, 0.78], 41, 0.88; at `0.1 g²/L^d` (`Nη = 0.2`, outside the range) the means stay below 1.72. (f) `STScaleExists` (`scale_family.py`): along `sz0` (`n = 0, 1, 3, 9`) and `1−u` from 1 down to `N^{-1+ε}` (below `g²/L^d`), the family `K_{m+1} = min(L, root of 𝒯_u(r) = b_u^{1/6}𝒯_u(K_m))` has `u ↦ 𝒯_u(K_m(u))` nondecreasing in all 8 rows (`D = 3, 10`) and reaches `𝒯_u ≤ W^{-D}` or `K = L` in at most 8 steps.
* **F15 (reconciliation with the LW pins of T2040, merged report only; branch `t/T2040`, `RBM3D/Probe/T2040Graphs.lean:885-1011`).** Same conclusions: `STLWB` = `LWterm`, `STLWT` = `LWtermExp` (index `(Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))`, bounds `η_t⁻¹Ψ(0)Ψ(|a−b|)²` and `η_t⁻¹Bctl^{1/2}·STprof`, `∀ D > 0`). Differences for the sign-off: (1) the light-weight term: `STEGtM` (`(def_EwtG)`, cut `y` at the first/second slot) equals `LWE` (`LWcut`, `(eq:EGC)`) up to the cyclic rotation `((σ₀,σ₁,σ₁),(a₀,y,a₁)) ↦ ((σ₁,σ₁,σ₀),(y,a₁,a₀))` of a loop and the order of the two terms (not proved in either probe); (2) T2040 keeps the `(initialGT2)` control `Ψ` apart from the profile `Φ`; `STLWB` ties them (`Ψ_t := Ψ_t(0)`), as the application to `Ψ_t(r) = (W^{-c₀}B_{t,r∧K})^{1/2}` does; (3) the class `(eq:Psi)`: `STPsiClass` has `∃ C₁ C₂` inside, `LWAssm` takes `C₁ C₂ C₃ Cc` as universally quantified inputs (equivalent in an implication); (4) the range of `ℓ` (`0 ≤ ℓ_n ≤ (log W)^{10}ℓ_t`): `∀ᶠ n` here (`STLWT`, `STEMn2Exp`), `∀ n` in `LWAssmExp` (the `∀ᶠ` form is the weaker hypothesis; the window of `Ψ` is `∀ᶠ n` in both); (5) `STLWassm`/`STLWassmExp` are separate premises, bundled in T2040 as `LWAssm`/`LWAssmExp`. No difference in a bound or an exponent.
* **F16 (the general-`n` grid files and the ST-3 interface).** The RBM2D class-b files `Induction/*N` import ST-3 files (`HierVocab` → S3-01 merged, `HierAlgebra` + `HierarchyN` → row ST2-28a, `KcalDecay` → S3-06, `BcalE` → S3-08/09) and the class-c files `GoodSet`, `Bootstrap`, `GoodEventClose` (the `d = 2` good set with `M_u`): for `d ≥ 3` the Step 3-4 pins of T2049 take `STStep2Concl`, `STLmaxU`, `STLKU` as hypotheses (no good set), so `GridGoodN` (ST2-32) needs a rewrite without them. `StoppedEndDefs` imports `B45`, `DecayLoop`, `Step45` and defines the endpoint pins (`GridEndConcl`, `NonAltGridEnd`, `AltGridEnd`, ...) that T2049 merged as `STOeqNQ`, `STOeqQt`, `STOeqQtNZ`: it is not ported (686 kept lines dropped; the dispatcher confirms). The loop dynamics shared by Steps 2-4 is pinned for every loop length: `STGridRepN` (probe §12.2: `Sol_CalL` on the grid, `(aaswtghh)` and the `𝒰`-weighted `(alu9_STime)` for the same martingale `Mart`; vocabulary = the merged `ThetaN`, `UN`, `uKer` and the copies of T2049's `STLI..STee` with `H` for `ω`, `rfl` to the merged model-level terms); the loop-length-`2` pin `STGridMart` used by the skeleton is its case `m = 2` (`ST_gridMart_of_repN`, compiled). Not pinned (ports): the algebraic Duhamel telescope `GridDuhamelN_Ugen_duhamel_telescope` (deterministic, ST2-27), the grid good events and stopping-time exits of Steps 3-4 (S3-10, S3-13a own them).

## P.9 The pins and instances, extracted from the probe by script (items 2 and 8)

Command: `python3 extract_stmt.py RBM3D/Probe/T2039Pins.lean <names>`; text without docstrings (the docstrings state the paper lines and the registry class). Probe lines are those of the committed file.

```
-- STStep2Local (probe lines 457-460)
def STStep2Local (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))
-- STStep2Avg (probe lines 464-467)
def STStep2Avg (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Zd d (sz.L n))
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - mE (E n)‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ))
-- STStep2Decay (probe lines 472-481)
def STStep2Decay (Cd : ℝ) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
-- STStep2 (probe lines 805-814)
def STStep2 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep1Weak sz (STflowE z) s t →
            STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t ∧
              STStep2Decay sz Cd (STflowE z) s t
-- STNewKLKAt (probe lines 572-583)
def STNewKLKAt (d : ℕ) (κ 𝔡 C δ₀ : ℝ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMM sz n E u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOp sz n E u σ (STLKM sz n E u H σ) a‖ ≤
            C / (1 - u) * STJhatM sz n E D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKM sz n E u H σ a‖ ≤
            C / (1 - u) * (STJhatM sz n E D ℓ u H +
              STJhatM sz n E D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)
-- STNewKLK (probe lines 586-587)
def STNewKLK (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAt d κ 𝔡 C δ₀
-- STContractPt (probe lines 600-609)
def STContractPt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ),
    H.IsHermitian → 0 < z.im → ∀ (σ : Fin 2 → Bool) (a b : Zd d L) (𝒜 : Finset (Zd d L)) (M : ℝ),
      0 ≤ M →
      (∀ c' ∈ 𝒜, ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^ (1 / 2 : ℝ) ≤ M) →
        ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1),
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤
          3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * M *
            max ‖loopFine d L W H z ![true, σ 1, !(σ 1)] ![a, b, a]‖
              ‖loopFine d L W H z ![false, σ 1, !(σ 1)] ![a, b, a]‖
-- STLWassm (probe lines 551-554)
def STLWassm (E t : ℕ → ℝ) (Ψ : ℕ → ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖Lloop sz n (E n) (t n) p.1.1 p.2 ω‖)
    (fun n p _ => (Ψ n (zdistInf d (sz.L n) (p.2 0 - p.2 1))) ^ 2)
-- STLWassmExp (probe lines 558-561)
def STLWassmExp (E t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖Lloop sz n (E n) (t n) p.1.1 p.2 ω‖)
    (fun n p _ => STprof sz n (t n) D (ℓ n) (p.2 0) (p.2 1))
-- STInitialGT2 (probe lines 532-536)
def STInitialGT2 (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    Prec sz (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)
      (fun n _ _ => Ψ n ^ 2)
-- STPsiClass (probe lines 542-548)
def STPsiClass (ε₀ : ℝ) (Ψ : ℕ → ℕ → ℝ) : Prop :=
  (∀ n r, 0 < Ψ n r ∧ Ψ n r ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    (∀ n r r', r ≤ r' → Ψ n r' ≤ Ψ n r) ∧
    (∀ C : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ c⁻¹ * Ψ n 0 ∧ ∀ r ≤ C, c * Ψ n 0 ≤ Ψ n r) ∧
    (∃ C₁ C₂ : ℝ, 1 < C₁ ∧ 1 < C₂ ∧ ∀ n r₁ r₂ : ℕ, 1 ≤ r₁ → r₁ ≤ r₂ →
      Ψ n r₁ / Ψ n r₂ ≤ C₁ * ((r₂ : ℝ) / r₁) ^ C₂)
-- STLWB (probe lines 615-624)
def STLWB (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℕ → ℝ, STPsiClass sz ε₀ Ψ →
          STInitialGT2 sz (STflowE z) t ε₀ (fun n => Ψ n 0) → STLWassm sz (STflowE z) t Ψ →
            Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖STEGt sz n (STflowE z n) (t n) p.1 p.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 *
                (Ψ n (zdistInf d (sz.L n) (p.2 0 - p.2 1))) ^ 2)
-- STLWT (probe lines 630-645)
def STLWT (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2 sz (STflowE z) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => ‖STEGt sz n (STflowE z n) (t n) p.1 p.2 ω‖)
                (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  STprof sz n (t n) D (ℓ n) (p.2 0) (p.2 1))
-- STEMn2Poly (probe lines 650-659)
def STEMn2Poly (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℕ → ℝ, STPsiClass sz ε₀ Ψ →
          STInitialGT2 sz (STflowE z) t ε₀ (fun n => Ψ n 0) → STLWassm sz (STflowE z) t Ψ →
            Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖STEEk sz n (STflowE z n) (t n) p.1 p.2.1 p.2.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 *
                (Ψ n (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1))) ^ 4)
-- STEMn2Exp (probe lines 665-682)
def STEMn2Exp (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2 sz (STflowE z) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => ‖STEEk sz n (STflowE z n) (t n) p.1 p.2.1 p.2.2 ω‖)
                (fun n p ω => (etaT (STflowE z n) (t n))⁻¹ *
                  ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) +
                    (STJhat sz n (STflowE z n) D (ℓ n) (t n) ω) ^ 3) *
                  (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)
-- STGridMartAt (probe lines 722-743)
def STGridMartAt (d : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
              (∀ n i, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                STgA sz s t K n (STflowE z n) i.1 i.2 k ω =
                  STgA sz s t K n (STflowE z n) i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDrift sz s t K n (STflowE z n) i.1 i.2 j ω +
                    Rem n i k ω + Mart n i k ω) ∧
              (∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i,
                pathP sz {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STEEM sz n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
                          i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))
-- STGridMart (probe lines 746-746)
def STGridMart (d : ℕ) : Prop := ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridMartAt d C₀
-- STgDriftN (probe lines 5086-5094)
def STgDriftN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) (gridTime s t K n k)
      (fun a' => STLKIM sz n E (gridTime s t K n k) (pathH sz s t K n k ω)
        (KLloopOf d (sz.L n) σ a')) a +
    ∑ l ∈ Finset.Icc 3 m, STksimLKM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) l
      (KLloopOf d (sz.L n) σ a) +
    STelklkM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) (KLloopOf d (sz.L n) σ a) +
    STegtM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) (KLloopOf d (sz.L n) σ a)
-- STeeUM (probe lines 5099-5104)
def STeeUM (n : ℕ) (E v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) : ℂ :=
  ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
    (∏ i, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
      (∏ i, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) *
        STeeM sz n E v H σ b b'
-- STGridRepNAt (probe lines 5119-5152)
def STGridRepNAt (d m : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∃ Mart Rem : ∀ n, ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
              (∀ (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))), ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                STgAN sz s t K n (STflowE z n) i.1 i.2 k ω =
                  STgAN sz s t K n (STflowE z n) i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftN sz s t K n (STflowE z n) i.1 i.2 j ω +
                    Rem n i k ω + Mart n i k ω) ∧
              (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
                pathP sz {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STeeM sz n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
                          i.1 i.2 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
                pathP sz {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STeeUM sz n (STflowE z n) (gridTime s t K n j) (gridTime s t K n k)
                          (pathH sz s t K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                          (1 / 2 : ℝ) <
                    ‖∑ j ∈ Finset.range k,
                      UN d (sz.L n) (sz.lam n) (fun i' => mSigma (STflowE z n) (i.1 i'))
                        (gridTime s t K n j) (gridTime s t K n k)
                        (fun b => Mart n (i.1, b) (j + 1) ω - Mart n (i.1, b) j ω) i.2‖} ≤
                  ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))
-- STGridRepN (probe lines 5156-5156)
def STGridRepN (d : ℕ) : Prop := ∀ m : ℕ, 2 ≤ m → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridRepNAt d m C₀
-- ST_gridMart_of_repN (probe lines 5314-5314)
theorem ST_gridMart_of_repN {d : ℕ} (h : STGridRepN d) : STGridMart d := by
-- ST_step2_of_pinsN (probe lines 5341-5343)
theorem ST_step2_of_pinsN {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d)
    (hRep : STGridRepN d) (hK2 : STK2decay d) (hNet : STNetLift2 d) (hScale : STScaleExists d)
    (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d :=
-- STstopIdx (probe lines 753-757)
def STstopIdx (s t : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ → ℝ) (n : ℕ) :
    PathΩ sz → ℕ :=
  firstHit (fun j (ω : PathΩ sz) =>
    STJhatM sz n (E n) D (ℓ n (gridTime s t K n j)) (gridTime s t K n j) (pathH sz s t K n j ω) /
      (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ)) 1 (K n)
-- STstopIdx_isStoppingTime (probe lines 760-762)
theorem STstopIdx_isStoppingTime (s t : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ → ℝ)
    (n : ℕ) :
    MeasureTheory.IsStoppingTime (filt sz) (fun ω => (STstopIdx sz s t K E D ℓ n ω : ℕ)) :=
-- STK2decay (probe lines 777-781)
def STK2decay (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
      0 ≤ u → u < 1 → 0 ≤ D → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STKloop sz n E u σ a‖ ≤ C * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
-- STNetLift2 (probe lines 790-797)
def STNetLift2 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ Cd : ℝ, STStep2LocalPT sz (STflowE z) s t → STStep2AvgPT sz (STflowE z) s t →
          STStep2DecayPT sz Cd (STflowE z) s t →
            STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t ∧
              STStep2Decay sz Cd (STflowE z) s t
-- STBdata (probe lines 2542-2548)
def STBdata (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ cB : ℝ, 0 < cB ∧ ∀ 𝔠 : ℝ, ∃ c : ℝ, 0 < c ∧
    ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧
            sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)
-- STScaleOk (probe lines 2277-2281)
def STScaleOk (s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ) : Prop :=
  (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧ Kf n u ≤ ((sz.L n : ℕ) : ℝ) ∧
    Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) ∧
  (∀ᶠ n in atTop, ∀ u v, s n ≤ u → u ≤ v → v ≤ t n →
    tailT d (sz.L n) (sz.lam n) u (Kf n u) ≤ tailT d (sz.L n) (sz.lam n) v (Kf n v))
-- STScaleAdm (probe lines 2288-2296)
def STScaleAdm (s t : ℕ → ℝ) (Kseq : ℕ → ℕ → ℝ → ℝ) : Prop :=
  (∀ n u, Kseq 0 n u = 0) ∧ (∀ m, STScaleOk sz s t (Kseq m)) ∧
  (∀ m, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kseq m n u ∧ Kseq m n u ≤ Kseq (m + 1) n u) ∧
  (∀ m, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * tailT d (sz.L n) (sz.lam n) u (Kseq m n u) ≤
      tailT d (sz.L n) (sz.lam n) u (Kseq (m + 1) n u)) ∧
  (∀ D : ℝ, 0 < D → ∃ M : ℕ, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
    tailT d (sz.L n) (sz.lam n) u (Kseq M n u) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) ∨
      ((sz.L n : ℕ) : ℝ) ≤ Kseq M n u)
-- STScaleExists (probe lines 4106-4110)
def STScaleExists (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz s t Kseq
-- STOptL2 (probe lines 4117-4126)
def STOptL2 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep1Weak sz (STflowE z) s t →
          PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω -
              STKloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
            (fun n p _ => sz.Bctl n (p.1 : ℝ))
-- STL2decayPT (probe lines 4133-4136)
def STL2decayPT (E s t : ℕ → ℝ) : Prop :=
  PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) ![false, true] p.2 ω‖)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2 0 - p.2 1)))
-- STLocalAvgOfL2 (probe lines 4144-4149)
def STLocalAvgOfL2 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STStep1Weak sz (STflowE z) s t → STL2decayPT sz (STflowE z) s t →
          STStep2LocalPT sz (STflowE z) s t ∧ STStep2AvgPT sz (STflowE z) s t
-- ST_step2_of_pins (probe lines 4639-4641)
theorem ST_step2_of_pins (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d)
    (hMart : STGridMart d) (hK2 : STK2decay d) (hNet : STNetLift2 d)
    (hScale : STScaleExists d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d := by
-- STAvgU (probe lines 4752-4755)
def STAvgU (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 1)
-- STLocalEntryU (probe lines 4760-4763)
def STLocalEntryU (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))
-- STGdecayW (probe lines 4770-4778)
def STGdecayW (E s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
-- STStep2Concl (probe lines 4784-4785)
def STStep2Concl (E s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STLocalEntryU sz E s t ∧ STAvgU sz E s t ∧ STGdecayW sz E s t Cd
-- ST_concl_of_step2 (probe lines 4863-4864)
theorem ST_concl_of_step2 {E s t : ℕ → ℝ} {Cd : ℝ} (hL : STStep2Local sz E s t)
    (hA : STStep2Avg sz E s t) (hD : STStep2Decay sz Cd E s t) : STStep2Concl sz E s t Cd :=
-- ST_step2_concl (probe lines 4871-4879)
theorem ST_step2_concl {d : ℕ} (h : STStep2 d) :
    3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
            (∀ n, t n ≤ lemT (z n)) →
            STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t →
            STStep1Loop sz (STflowE z) s t → STStep1Weak sz (STflowE z) s t →
              STStep2Concl sz (STflowE z) s t Cd := by
```

### P.9b Instances at `d = 3` (item 8), statements

```
-- inst_step2 (probe lines 5489-5494)
theorem inst_step2 (h : STStep2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
          STStep2Decay sz0 Cd (STflowE z0) sInst tInst) := by
-- inst_step2_lowg (probe lines 5503-5508)
theorem inst_step2_lowg (h : STStep2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz1 (STflowE z0) sInst → STDecay sz1 (STflowE z0) sInst →
        STStep1Loop sz1 (STflowE z0) sInst tInst → STStep1Weak sz1 (STflowE z0) sInst tInst →
        STStep2Local sz1 (STflowE z0) sInst tInst ∧ STStep2Avg sz1 (STflowE z0) sInst tInst ∧
          STStep2Decay sz1 Cd (STflowE z0) sInst tInst) := by
-- inst_step2_concl (probe lines 5806-5810)
theorem inst_step2_concl (h : STStep2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) := by
-- inst_skeleton_concl (probe lines 5821-5827)
theorem inst_skeleton_concl (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
    (hMart : STGridMart 3) (hK2 : STK2decay 3) (hNet : STNetLift2 3)
    (hScale : STScaleExists 3) (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
-- inst_newKLK (probe lines 5548-5562)
theorem inst_newKLK (h : STNewKLK 3) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STthetaOp sz0 0 (1 / 2) 0 σ
          (STLKM sz0 0 (1 / 2) 0
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ) a‖ ≤
          C / (1 - 0) * STJhatM sz0 0 (1 / 2) 1 0 0
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) *
            STprof sz0 0 0 1 0 (a 0) (a 1) ∧
        ‖STELKLKM sz0 0 (1 / 2) 0
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ a‖ ≤
          C / (1 - 0) * (STJhatM sz0 0 (1 / 2) 1 0 0
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) +
            STJhatM sz0 0 (1 / 2) 1 0 0
              (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ^ 2 *
              (if 1 ≤ (0 : ℝ) then 1 else 0)) * STprof sz0 0 0 1 0 (a 0) (a 1) := by
-- inst_contractPt (probe lines 5576-5589)
theorem inst_contractPt (h : STContractPt 3) :
    ∑ c' ∈ ({0} : Finset (Zd 3 3)), ∑ c ∈ Finset.univ.filter
        (fun c : Zd 3 3 => zdistInf 3 3 (c - c') ≤ 1),
      ‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
        ![![true, false] 0, ![true, false] 1, ![true, false] 0, !(![true, false] 0),
          !(![true, false] 1), !(![true, false] 0)] ![0, 0, c', 0, 0, c]‖ ≤
      3 ^ 3 / (((2 : ℕ) : ℝ) ^ 3 * Complex.I.im) *
        (‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
          ![![true, false] 0, !(![true, false] 0), ![true, false] 0, !(![true, false] 0)]
          ![(0 : Zd 3 3), 0, 0, 0]‖ ^ (1 / 2 : ℝ)) *
        max ‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
            ![true, ![true, false] 1, !(![true, false] 1)] ![0, 0, 0]‖
          ‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
            ![false, ![true, false] 1, !(![true, false] 1)] ![0, 0, 0]‖ := by
-- Ψ0_class (probe lines 5611-5611)
theorem Ψ0_class : STPsiClass sz0 (1 / 20) Ψ0 := by
-- inst_LWB (probe lines 5632-5638)
theorem inst_LWB (h : STLWB 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEGt sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Ψ0 n 0 *
        (Ψ0 n (zdistInf 3 (sz0.L n) (p.2 0 - p.2 1))) ^ 2) :=
-- inst_EMn2Poly (probe lines 5644-5650)
theorem inst_EMn2Poly (h : STEMn2Poly 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Ψ0 n 0 *
        (Ψ0 n (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1))) ^ 4) :=
-- inst_LWT (probe lines 5667-5673)
theorem inst_LWT (h : STLWT 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D → STLWassmExp sz0 (STflowE z0) tInst D (fun _ => 0)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEGt sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        STprof sz0 n (tInst n) D 0 (p.2 0) (p.2 1)) :=
-- inst_EMn2Exp (probe lines 5679-5687)
theorem inst_EMn2Exp (h : STEMn2Exp 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D → STLWassmExp sz0 (STflowE z0) tInst D (fun _ => 0)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖)
      (fun n p ω => (etaT (STflowE z0 n) (tInst n))⁻¹ *
        ((sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) +
          (STJhat sz0 n (STflowE z0 n) D 0 (tInst n) ω) ^ 3) *
        (STprof sz0 n (tInst n) D 0 (p.2.2 0) (p.2.2 1)) ^ 2) :=
-- inst_gridMart (probe lines 5695-5704)
theorem inst_gridMart (h : STGridMart 3) :
    ∃ C₀ CK : ℝ, 0 ≤ C₀ ∧ 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n))) → ℕ → PathΩ sz0 → ℂ,
        ∀ n i, ∀ᵐ ω ∂(pathP sz0), ∀ k, k ≤ K n →
          STgA sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 k ω =
            STgA sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 0 ω +
              ((gridStep sInst tInst K n : ℝ) : ℂ) *
                ∑ j ∈ Finset.range k, STgDrift sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := by
-- inst_gridRepN (probe lines 5835-5844)
theorem inst_gridRepN (h : STGridRepN 3) :
    ∃ C₀ CK : ℝ, 0 ≤ C₀ ∧ 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      ∃ Mart Rem : ∀ n, ((Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n))) → ℕ → PathΩ sz0 → ℂ,
        ∀ n i, ∀ᵐ ω ∂(pathP sz0), ∀ k, k ≤ K n →
          STgAN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 k ω =
            STgAN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 0 ω +
              ((gridStep sInst tInst K n : ℝ) : ℂ) *
                ∑ j ∈ Finset.range k, STgDriftN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := by
-- inst_skeletonN (probe lines 5858-5865)
theorem inst_skeletonN (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
    (hRep : STGridRepN 3) (hK2 : STK2decay 3) (hNet : STNetLift2 3)
    (hScale : STScaleExists 3) (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
          STStep2Decay sz0 Cd (STflowE z0) sInst tInst) :=
-- inst_stop (probe lines 5719-5721)
theorem inst_stop :
    MeasureTheory.IsStoppingTime (filt sz0)
      (fun ω => (STstopIdx sz0 sInst tInst (fun _ => 8) (STflowE z0) 1 (fun _ _ => 0) 0 ω : ℕ)) :=
-- inst_K2decay (probe lines 5725-5728)
theorem inst_K2decay (h : STK2decay 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STKloop sz0 0 (1 / 2) 0 σ a‖ ≤
        C * STprof sz0 0 0 1 ((sz0.L 0 : ℕ) : ℝ) (a 0) (a 1) := by
-- inst_netLift2 (probe lines 5739-5744)
theorem inst_netLift2 (h : STNetLift2 3) (Cd : ℝ)
    (hL : STStep2LocalPT sz0 (STflowE z0) sInst tInst)
    (hA : STStep2AvgPT sz0 (STflowE z0) sInst tInst)
    (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
      STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
-- inst_Bdata (probe lines 5750-5753)
theorem inst_Bdata :
    ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ tInst n →
      cB * (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ sz0.Bctl n u ∧
        sz0.Bctl n u ≤ ((sz0.size n : ℕ) : ℝ) ^ (-c) := by
-- inst_scaleExists (probe lines 5761-5761)
theorem inst_scaleExists (h : STScaleExists 3) : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 sInst tInst Kseq :=
-- inst_optL2 (probe lines 5768-5775)
theorem inst_optL2 (h : STOptL2 3) :
    ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
      (STLK sz0 (STflowE z0) sInst → STStep1Loop sz0 (STflowE z0) sInst tInst →
        STStep1Weak sz0 (STflowE z0) sInst tInst →
        PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖)
          (fun n p _ => sz0.Bctl n (p.1 : ℝ))) := by
-- inst_localAvg (probe lines 5783-5785)
theorem inst_localAvg (h : STLocalAvgOfL2 3) :
    STStep1Weak sz0 (STflowE z0) sInst tInst → STL2decayPT sz0 (STflowE z0) sInst tInst →
      STStep2LocalPT sz0 (STflowE z0) sInst tInst ∧ STStep2AvgPT sz0 (STflowE z0) sInst tInst :=
-- inst_skeleton (probe lines 5793-5800)
theorem inst_skeleton (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
    (hMart : STGridMart 3) (hK2 : STK2decay 3) (hNet : STNetLift2 3)
    (hScale : STScaleExists 3) (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
          STStep2Decay sz0 Cd (STflowE z0) sInst tInst) :=
```

## P.10 Scripts (verbatim; the numbers of the prove report and of this file come from them; the RBM2D ones read it only through `git show` / `git ls-tree` at `c9a24cf`, `0c1330a`)

### inv2039.py  (item 1: inventory table, labels)

```python
#!/usr/bin/env python3
"""T2039 item 1: inventory of the 46 RBM2D ST-2 files at c9a24cf.
columns: file, lines at c9a24cf, lines kept at 0c1330a (-1 = deleted there), class (docs/reports/T2002-portmap.md section C, re-checked for the class-c list),
exponent tokens (T2002 stats.py rule: pow2+sup2+five), cited paper labels (that exist in this paper's TeX), public declarations, consumers outside ST-1/ST-2 (ST-3..ST-6 files of the T2002 grouping)."""
import subprocess, re, sys, glob, os, collections
repo='/Users/junyin/Lean_proof/RBM2D'; REF='c9a24cf'; KEPT='0c1330a'
def git(*a):
    return subprocess.run(['git','-C',repo,'--no-optional-locks',*a],capture_output=True,text=True).stdout
files=[x for x in git('ls-tree','-r','--name-only',REF,'--','RBM2D').split('\n') if x.endswith('.lean')]
keptfiles=set(x for x in git('ls-tree','-r','--name-only',KEPT,'--','RBM2D').split('\n') if x.endswith('.lean'))
text={f:git('show',f'{REF}:{f}') for f in files}
def nlines(t): return t.count('\n')
# class from the T2002 portmap
cls={}
for l in open('/Users/junyin/Lean_proof/RBM3D/docs/reports/T2002-portmap.md',encoding='utf-8'):
    m=re.match(r'^\| ([A-Za-z0-9_]+)\.lean \| (\d+) \| (-?\d+) \| ([abcd]) \|',l)
    if m: cls.setdefault(m.group(1),[]).append((int(m.group(2)),int(m.group(3)),m.group(4)))
# directories of the portmap sections in order
secdir=None; table={}
for l in open('/Users/junyin/Lean_proof/RBM3D/docs/reports/T2002-portmap.md',encoding='utf-8'):
    m=re.match(r'^### ([A-Za-z]+) -> RBM3D/',l)
    if m: secdir=m.group(1)
    m=re.match(r'^\| ([A-Za-z0-9_]+)\.lean \| (\d+) \| (-?\d+) \| ([abcd]) \|',l)
    if m and secdir: table[(secdir,m.group(1))]=(int(m.group(2)),int(m.group(3)),m.group(4))
MD=re.compile(r'^RBM2D/Path/(PerTime|Walk|Transfer|Markov|Stop|Azuma|Step2Props)\.lean$')
DD=re.compile(r'^RBM2D/Path/(ScalesBridge|TailSums)\.lean$')
IND=re.compile(r'^RBM2D/Induction/(Grid.*|AzumaProxyN|StepDecompN|LoopC2N|LoopGenN|QVN|Step2TargetV3|StoppedEndDefs)\.lean$')
st2=[f for f in files if (f.startswith('RBM2D/Path/') and not MD.match(f) and not DD.match(f)) or IND.match(f)]
def group(f):
    d=f.split('/')[1]; b=os.path.basename(f)[:-5]
    c=table.get((d,b),(0,0,'?'))[2]
    if c=='d': return 'none'
    if MD.match(f) or re.match(r'^RBM2D/(Defs/(Model|StochDom)|Gauss/(Model|Domination|MomentBridge|LinearForm|Envelope|SteinMatrix)|Hierarchy/(Loops|Operations|OperationsPairWord))\.lean$',f): return 'MD'
    if re.match(r'^RBM2D/(Gauss/.*|Green/.*|Hierarchy/.*|Induction/(Continuity|ConArg|ConArgDet|Step1))\.lean$',f): return 'ST-1'
    if f in st2: return 'ST-2'
    if re.match(r'^RBM2D/Induction/(?!(MainInd|Defs))[A-Za-z0-9]*\.lean$',f): return 'ST-3'
    if re.match(r'^RBM2D/Evolution/(Step61|MLExp.*)\.lean$',f): return 'ST-5'
    if re.match(r'^RBM2D/Evolution/.*\.lean$',f): return 'ST-4'
    if re.match(r'^RBM2D/(Induction/(MainInd|Defs)|Main/(?!BUniv).*)\.lean$',f): return 'ST-6'
    return 'other'
# tokens (T2002 stats.py)
tok=[('pow2',r'(\(W : ℝ\)|\(L : ℝ\)|\bW\b|\bL\b|\(W \* L\)|\(W : ℂ\)⁻¹|\(W : ℝ\)⁻¹|\(W : ℂ\)|\(\(W \* L\) \^ 2 : ℕ\)|size)\)?\s*\^\s*2\b'),
     ('sup2',r'(W|L|N)[⁻]?²|⁻²|\bd = 2\b|Z_L\^2|Z_\{WL\}\^2|\(W L\)²'),('five',r'\b5⁻¹|\(1 / 5\)|1/5\b')]
# TeX labels of this paper
texlab=set()
for fn in glob.glob('/Users/junyin/Lean_proof/RBM3D/paper/tex/*.tex'):
    for l in open(fn,encoding='utf-8',errors='replace'):
        if l.lstrip().startswith('%'): continue
        l2=re.sub(r'(?<!\\)%.*$','',l)
        texlab.update(re.findall(r'\\label\{([^}]*)\}',l2))
decl=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:protected\s+)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|instance|inductive|class)\s+([A-Za-z0-9_.\'!?]+)',re.M)
def publics(t):
    out=[]
    for m in re.finditer(r'^(private\s+)?(?:@\[[^\]]*\]\s*)?(?:protected\s+)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|instance|inductive|class)\s+([A-Za-z0-9_.\'!?]+)',t,re.M):
        if not m.group(1) and not m.group(3).startswith('_'): out.append(m.group(3))
    return out
cons_groups={'ST-3','ST-4','ST-5','ST-6'}
consfiles=[f for f in files if group(f) in cons_groups]
if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)>1 else 'table'
    rows=[]
    for f in st2:
        t=text[f]; d=f.split('/')[1]; b=os.path.basename(f)[:-5]
        cl=table.get((d,b),(0,0,'?'))[2]
        n=nlines(t); kept=nlines(git('show',f'{KEPT}:{f}')) if f in keptfiles else -1
        ntok=sum(len(re.findall(p,t)) for _,p in tok)
        cites=set(x.strip() for x in re.findall(r'`\(?([A-Za-z][A-Za-z0-9_:;+\-<>=.\[\]\' ]*?)\)?`',t))
        labs=sorted(c for c in cites if c in texlab)
        pub=publics(t)
        # consumers: word-boundary occurrences of each public name in ST-3..ST-6 files
        used={}
        for name in pub:
            short=name.split('.')[-1]
            if len(short)<4: continue
            pat=re.compile(r'(?<![A-Za-z0-9_\'.])'+re.escape(short)+r'(?![A-Za-z0-9_\'])')
            hit=sorted(set(group(g) for g in consfiles if g!=f and pat.search(text[g])))
            if hit: used[name]=hit
        rows.append((f,n,kept,cl,ntok,labs,pub,used))
    if mode=='table':
        print('| # | file (RBM2D/) | lines c9a24cf | kept 0c1330a | class | tokens | #public | consumed by ST-3..6 (names; groups) |')
        print('|---|---|---|---|---|---|---|---|')
        for i,(f,n,kept,cl,ntok,labs,pub,used) in enumerate(rows,1):
            u='; '.join(f"{k} [{','.join(v)}]" for k,v in list(used.items())[:6])+(f' (+{len(used)-6})' if len(used)>6 else '')
            print(f"| {i} | {f[6:-5]} | {n} | {kept} | {cl} | {ntok} | {len(pub)} | {u if u else '-'} |")
        tot=lambda i: sum(r[i] for r in rows)
        print(f"| | TOTAL {len(rows)} files | {tot(1)} | {sum(max(r[2],0) for r in rows)} | classes {dict(collections.Counter(r[3] for r in rows))} | {tot(4)} | {tot(6) if False else sum(len(r[6]) for r in rows)} | |")
    elif mode=='labels':
        for (f,n,kept,cl,ntok,labs,pub,used) in rows: print(f[6:-5],'|',', '.join(labs))
    elif mode=='used':
        for (f,n,kept,cl,ntok,labs,pub,used) in rows:
            print(f[6:-5],'|',json.dumps(used) if False else used)
```

### deps.py  (dependency levels of the 46 files)

```python
import re, subprocess, collections, os, sys
sys.path.insert(0,'.')
from st2files import st2, git, ref
import inv2039 as I
mods={f[:-5].replace('/','.'):f for f in st2}   # RBM2D.Path.Foo -> file
deps={}
for f in st2:
    t=I.text[f]
    imps=re.findall(r'^import\s+(RBM2D\.[A-Za-z0-9_.]+)',t,re.M)
    deps[f]=[mods[m] for m in imps if m in mods]
# topological levels
level={}
def lv(f):
    if f in level: return level[f]
    level[f]=0
    level[f]=1+max([lv(g) for g in deps[f]],default=-1) if deps[f] else 0
    return level[f]
for f in st2: lv(f)
rows=[]
for f in st2:
    d=os.path.basename(f)[:-5]; dd=f.split('/')[1]
    n=I.nlines(I.text[f]); kept=I.nlines(I.git('show',f'{I.KEPT}:{f}')) if f in I.keptfiles else -1
    cl=I.table.get((dd,d),(0,0,'?'))[2]
    rows.append((level[f],f[6:-5],n,kept,cl,[g[6:-5] for g in deps[f]]))
rows.sort()
for r in rows: print(r[0],r[1],r[2],r[3],r[4],'<-',','.join(r[5]))
```

### regimes.py  (P.3 numbers)

```python
#!/usr/bin/env python3
"""T2039 item 3: the exponent table in the regimes of 1-t at the preflight sequence sz0, n=0
(d=3, L=4, W=32, g=ilambda=1/64, N=(WL)^d), and its limit along sz0.  Formulas: B_{t,K}=(g^2+x)^{-1}(K+1)^{2-d}+(L^d x)^{-1}
(merged Bparam), ell_t=min(max(g/sqrt(x),1),L) (merged ellT), Delta_t=W^{-d}B_{t,0} (merged Bctl), T_t(r)=B_{t,r}exp(-sqrt(r/ell_t))."""
import math
d,L,W,g=3,4,32,1/64
N=(W*L)**d
def B(x,K): return 1/(g*g+x)*(K+1)**(2-d)+1/(L**d*x)
def ell(x): return min(max(g/math.sqrt(x),1),L)
print(f'd={d} L={L} W={W} g={g} N=(WL)^d={N}; thresholds: g^2={g*g:.4g}  g^2/L^2={g*g/L**2:.4g}  g^2/L^d={g*g/L**d:.4g}  N^(-1+eps)={N**(-0.9):.4g} (eps=1/10)')
print('regime | x=1-u | ell_u | B_{u,0} | first term | zero-mode | W^-d B_{u,0} | W^-d B_{u,1} | T_u(L) | r=(1-s)/(1-u) at s=0.5')
for name,x in [('R1 x>=g^2',0.5),('R2 g^2/L^2<=x<=g^2',1e-4),('R3 g^2/L^d<=x<=g^2/L^2',8e-6),('R4 x<g^2/L^d (inside range)',3e-6)]:
    first=1/(g*g+x); zero=1/(L**d*x)
    T=lambda r: B(x,r)*math.exp(-math.sqrt(r/ell(x)))
    print(f'{name:28s} | {x:.3g} | {ell(x):.4g} | {B(x,0):.4g} | {first:.4g} | {zero:.4g} | {B(x,0)/W**d:.4g} | {B(x,1)/W**d:.4g} | {T(L):.4g} | {0.5/x:.4g}')
print('exponents: weak law (Gtmwc) 1/4; output 1/5; stopping threshold 1/6 (J<Delta_u^(1/6)); stretched exp (r/ell)^(1/2); martingale (Delta^(1/2)+J^3)^(1/2)')
print('closure of the skeleton: (3C+1) c_d <= 1/60, C_d=3C+1, c_d<=1/100; r^C_d Delta^(1/5)<=Delta^(1/6) needs C_d c_d<=1/30; Lambda=2N^eps1 absorbed by Delta^(1/60), eps1<=c/400')
for C in (1,3,10):
    Cd=3*C+1; cd=min(1/100,1/(60*Cd))
    print(f'  C={C}: C_d={Cd}  c_d<=min(1/100,1/(60 C_d))={cd:.5g}  r_max=Delta_t^(-c_d)={ (0.0934)**(-cd):.5g} at Delta_t=0.0934')
print('limit along sz0: n, N^-1/2... see W^-d B_{t,0} <= (g^2 W^d)^-1+(N x)^-1 with x=N^(-1+eps):')
for n in (0,1,3,9,99,999):
    Wn=(2*(n+1))**5; Ln=4*(n+1); gn=1/(2*(n+1))**6; Nn=(Wn*Ln)**3
    print(f'  n={n}: W={Wn} L={Ln} g={gn:.3g} (g^2 W^d)^-1={1/(gn*gn*Wn**3):.4g}  N^-eps={Nn**(-0.1):.4g}')
```

### mksplit.py  (item 7: split table)

```python
#!/usr/bin/env python3
"""T2039 item 7: the split table.  kept lines come from inv2039.py (RBM2D at 0c1330a); est. lines of new tickets are the probe section sizes (compiled) or design estimates."""
import sys
sys.path.insert(0,'.')
import inv2039 as I, os
kept={}
for f in I.st2:
    d=f.split('/')[1]; b=os.path.basename(f)[:-5]
    kept[f'{d}/{b}']=I.nlines(I.git('show',f'{I.KEPT}:{f}')) if f in I.keptfiles else 0
def K(*names): return sum(kept[n] for n in names)
rows=[]  # (id, files under RBM3D, statements, sources, kept_src, est, deps, role)
def R(*a): rows.append(a)
# group A: probe -> RBM3D (compiled)
R('ST2-01','Induction/Step2Defs.lean','vocabulary `STLM..STEEM`, measurability, the general-`n` vocabulary (`STLIM..STeeM`, `STgAN`, `STgDriftN`, `STeeUM`), all pins (`STStep2` with the conclusion `STStep2Concl`, `STNewKLK`, `STContractPt`, `STLWB/T`, `STEMn2Poly/Exp`, `STGridRepN` (every loop length; `STGridMart` is its case `m = 2`), `STK2decay`, `STNetLift2`, `STScaleExists`, `STOptL2`, `STLocalAvgOfL2`), registry','probe §1–§2, §12 pins, §12.2 vocabulary and pin',0,930,'S1-07 (T2028, merged), S3-01 (T2049, merged: `STStep2Concl`), MD-3','prover')
R('ST2-02','Induction/Step2Core.lean','real core, tails, transfer, engine, `STGoodAt`, `ST_good_engine`','probe §3–§8',0,1300,'ST2-01, MD-4/5','prover (compiled port)')
R('ST2-03','Induction/Step2Events.lean','grid events from sections, LW premises, `ST_event_*`, `ST_good_prob`, arithmetic','probe §9, §11 (events)',0,1160,'ST2-02, LW pins','prover (compiled port)')
R('ST2-04','Induction/Step2Iterate.lean','`ST_selfImprove_section`, `ST_iterate`, `ST_decay_pt`, `ST_L2_decay_pt`, `ST_base_inv`, `ST_Bdata_holds`, `ST_step2_of_pins`, `ST_avgU_of_avg`, `ST_step2_concl`, `ST_gridMart_of_repN`, `ST_step2_of_pinsN`','probe §10–§12.2',0,1450,'ST2-03','prover (compiled port)')
# group B: proofs of the pins
R('ST2-05','Induction/Step2Scale.lean','`STScaleExists` (IVT, caps, floor)','new (3_5:571–577)',0,450,'ST2-02','prover')
R('ST2-06','Induction/Step2K2.lean','`STK2decay`','new; `Path/KellStar:39,240`',K('Path/KellStar'),450,'ST2-01, `Prop5Decay` (borrowed pin, `Propagator/Pins`), KL (`KLK_two`)','prover-hard')
R('ST2-06b','Induction/PropTInf.lean','`(TTT2)` of `lem:propT` for the `L^∞` distance `zdistInf` (ingredient of `STNewKLK`; merged `EKPropT` is `ℓ¹`, F1)','new (paper A:230–258); `EKPropT`',0,700,'EK (`EKPropT`, `tailT_antitone`)','prover-hard')
R('ST2-07','Induction/NewKLK.lean','`STNewKLK` (`lem:newKLK`)','new (3_5:610–668)',0,900,'ST2-06, ST2-06b, `KLK_ward`','prover-hard')
R('ST2-08','Induction/ContractPt.lean','`STContractPt` (`ygdhmsgq0`; not the merged Step 3 `STContract`, F13)','new (3_5:751–797)',0,650,'`Hierarchy/ContractionBasic`, S3-02 (T2054) technique','prover-hard')
R('ST2-09','Induction/EMn2Poly.lean','`STEMn2Poly` (first estimate)','new (3_5:800–825)',0,1000,'ST2-08, LW pins','prover-max')
R('ST2-10','Induction/EMn2Exp1.lean','`STEMn2Exp` part 1 (6-loop bound, `Ĵ³` feedback)','new (3_5:829–860)',0,1400,'ST2-08, ST2-09','prover-max')
R('ST2-11','Induction/EMn2Exp2.lean','`STEMn2Exp` part 2 (tail profile, `𝒯̃^ℓ` sums)','new (3_5:860–899)',0,1400,'ST2-10','prover-max')
R('ST2-12','Path/DifREP1.lean','`STGridRepN` part 1 (`Sol_CalL` grid form at every loop length: drift algebra, remainder)','`Path/{OneStep,DriftAlgebra,LoopStep}` ports (group C)',0,900,'ST2-20..22, MD-4/5','prover-hard')
R('ST2-13','Path/DifREP2.lean','`STGridRepN` part 2 (random-proxy Azuma + Doob tail, plain and `𝒰`-weighted `(alu9_STime)`)','new + `Induction/{AzumaProxyN,GridDuhamelN}`',0,900,'ST2-12, `Path/Azuma`','prover-hard')
R('ST2-14','Induction/OptL2a.lean','`STOptL2` part 1 (events with polynomial pins)','new (3_5:466–480)',0,700,'ST2-03, ST2-07, ST2-09','prover-hard')
R('ST2-15','Induction/OptL2b.lean','`STOptL2` part 2 (linear Grönwall, `𝔠_d ≤ 𝔠₀`)','new (3_5:481–512)',0,800,'ST2-14','prover-hard')
R('ST2-16','Induction/LocalAvg1.lean','`STLocalAvgOfL2` part 1 (`(initialGT2)` from `(eq:L2_decay)`, `(GavLGEX)`)','new; `Path/Step2Local:198–219`',K('Path/Step2Local'),800,'S1-30 (`lem_GbEXP`)','prover-hard')
R('ST2-17','Induction/LocalAvg2.lean','`STLocalAvgOfL2` part 2 (`(GijGEX)` neighbour sums, `(GiiGEX)`, indicator)','new',0,700,'ST2-16','prover-hard')
R('ST2-18','Path/NetLift1.lean','`STNetLift2` part 1 (`Step2NetLift`)','`Path/NetLift:1334–1518` (1784 lines at `c9a24cf`)',1784//2,900,'ST2-01, MD-2','prover')
R('ST2-19','Path/NetLift2.lean','`STNetLift2` part 2 (`Step2LocalNetLift`)','`Path/NetLift`',1784-1784//2,900,'ST2-18','prover')
# group C: ports of class b
R('ST2-20','Path/OneStep.lean (+DriftLip)','`genMat`, `envConst`, `OneStepEnvelope`, `norm_loopDrift_sub_le`','`Path/{OneStep,DriftLip}`',K('Path/OneStep','Path/DriftLip'),1760,'MD-3','prover')
R('ST2-21','Path/LoopStep.lean, Path/DriftAlgebra.lean','`condExp_loop_step/drift`, `LoopGenN2`, `HierarchyN2`','`Path/{LoopStep,DriftAlgebra}`',K('Path/LoopStep','Path/DriftAlgebra'),940,'ST2-20','prover')
R('ST2-22','Path/StepDecomp.lean','`gradMat`, `HermTestFun`, `stepDecomp`, `stepDecomp_Z_subG`','`Path/StepDecomp`',K('Path/StepDecomp'),1320,'MD-3','prover')
R('ST2-23','Path/QVIdentity.lean (+QVForm)','`EECutIdentity`, `QVPropagated`, `EEShift`, `v_gradMat_eq_quadVar`','`Path/{QVForm,QVIdentity}`',K('Path/QVForm','Path/QVIdentity'),970,'ST2-22','prover')
R('ST2-24','Path/StepDecompLoop.lean, Path/Kernel.lean','`stepDecomp_loopPM`, `ukerMat`, `Uop`, duhamel telescope','`Path/{StepDecompLoop,Kernel}`',K('Path/StepDecompLoop','Path/Kernel'),900,'ST2-22','prover')
R('ST2-25','Path/UBounds.lean, UTransport.lean, KellStar.lean','`thetaGenMat`, `sumNdecayEta`, `uopLocalMax`, `tailtoTail`, `kellStarEv`','`Path/{UBounds,UTransport,KellStar}`',K('Path/UBounds','Path/UTransport','Path/KellStar'),1550,'ST2-24, EK (`EKSumNdecay`)','prover')
R('ST2-26','Path/Expansion.lean','`Avec`, `martInc`, `stoppedDuhamel105`, `grid_expansion_all`','`Path/Expansion`',K('Path/Expansion'),980,'ST2-21, ST2-23, ST2-24','prover')
R('ST2-27','Path/DuhamelTail.lean, Induction/GridDuhamelN.lean','`StoppedAzuma108`, `GridDuhamelN_*`','`Path/DuhamelTail`, `Induction/GridDuhamelN`',K('Path/DuhamelTail','Induction/GridDuhamelN'),890,'ST2-26, S3-01','prover')
R('ST2-28','Induction/LoopGenN.lean, QVN.lean','`loopGenN`, `qvPropagatedN`','`Induction/{LoopGenN,QVN}`',K('Induction/LoopGenN','Induction/QVN'),1240,'ST2-21, ST2-23, S3-01 (HierVocab port, merged T2049)','prover')
R('ST2-28a','Induction/HierAlgebra.lean, HierarchyN.lean','general-`n` drift algebra `hierarchyN`, hierarchy identities (T2041 F-D: ST-3 files left to ST-2)','`Induction/{HierAlgebra,HierarchyN}` (T2041 P.1; 704 + 38 kept)',742,850,'S3-01 (T2049, merged: `STLI..STee`), ST2-21','prover')
R('ST2-29','Induction/LoopC2N.lean, GridDriftN.lean','`hermTestFunLoopN`, `gridDriftN`','`Induction/{LoopC2N,GridDriftN}`',K('Induction/LoopC2N','Induction/GridDriftN'),1330,'ST2-22, ST2-28, ST2-28a','prover')
R('ST2-30','Induction/StepDecompN.lean','`loopFamN` (general-`n` decomposition)','`Induction/StepDecompN`',K('Induction/StepDecompN'),1150,'ST2-29','prover')
R('ST2-31','Induction/GridEnvelopeN.lean, GridGoodEvent.lean','`gridDriftN_envelope`, `GridGoodEvent_*`','`Induction/{GridEnvelopeN,GridGoodEvent}`',K('Induction/GridEnvelopeN','Induction/GridGoodEvent'),1340,'ST2-29, ST2-32, S3-06 (`KcalDecay`)','prover')
R('ST2-32','Induction/GridGoodN.lean','`GoodSetN`, `gridExitTauN` (rewritten without `GoodSet/Bootstrap`)','`Induction/GridGoodN` (imports class c)',K('Induction/GridGoodN'),1070,'ST2-27, S3-08/09 (`BcalE`), a route without the class-c imports (F-G)','prover-hard')
R('ST2-33','Induction/GridAssemblyN.lean','`assembledN`','`Induction/GridAssemblyN`',K('Induction/GridAssemblyN'),1170,'ST2-32','prover')
R('ST2-34','Induction/AzumaProxyN.lean (part 1)','Azuma proxy, test-function linear combinations','`Induction/AzumaProxyN` lines 1–770 of 1540 kept',770,770,'ST2-30, ST2-32','prover')
R('ST2-35','Induction/AzumaProxyN.lean (part 2)','`azumaSubGN`, instances','`Induction/AzumaProxyN`',770,770,'ST2-34','prover')
R('ST2-36','Path/LemDecCalE.lean','`lem_dec_calE` (`GijGEX`, `def_ELKLK` inputs)','`Path/LemDecCalE`',K('Path/LemDecCalE'),860,'ST2-01','prover')
R('ST2-37','Path/LemDecCalEdif.lean (part 1)','`res_deccalE_dif`','`Path/LemDecCalEdif`',K('Path/LemDecCalEdif')//2,830,'ST2-36','prover')
R('ST2-38','Path/LemDecCalEdif.lean (part 2)','`res_deccalE_dif`','`Path/LemDecCalEdif`',K('Path/LemDecCalEdif')-K('Path/LemDecCalEdif')//2,830,'ST2-37','prover')
R('ST2-39','Path/LemDecCalEwG.lean','`res_deccalE_wG`','`Path/LemDecCalEwG`',K('Path/LemDecCalEwG'),1390,'ST2-36','prover')
n=len(rows)
print('| ticket | files under RBM3D/ | statements | sources (RBM2D kept lines / probe) | source kept lines | est. lines | depends on | role |')
print('|---|---|---|---|---|---|---|---|')
for r in rows: print('| '+' | '.join(str(x) for x in r)+' |')
A=sum(r[5] for r in rows[:4]); B=sum(r[5] for r in rows[4:20]); C=sum(r[5] for r in rows[20:])
print(f'| total | | | | {sum(r[4] for r in rows)} | {sum(r[5] for r in rows)} | | A {A} + B {B} + C {C} |')
print(f'\nTICKETS={n}  groupA={4} groupB={16} groupC={n-20}  lines={sum(r[5] for r in rows)}', file=sys.stderr)
cl=[f for f in kept]
print(f'\nclass-b kept lines of the 46 files = {sum(kept[k] for k in kept)} (class c included); NetLift kept=0 (absent at 0c1330a, 1784 at c9a24cf)', file=sys.stderr)
```

### extract_stmt.py  (statements of P.9, P.9b and of the prove report)

```python
#!/usr/bin/env python3
"""Extract declarations (statement text, no docstring) from the probe by name.  usage: extract_stmt.py FILE NAME [NAME...]
For `def`/`abbrev`/`structure`: from the header to the first blank line (the whole definition).  For `theorem`: from the header to the
line that ends the signature (`:= by` / `:=`)."""
import re, sys
f=sys.argv[1]; names=sys.argv[2:]
L=open(f,encoding='utf-8').read().split('\n')
for nm in names:
    pat=re.compile(r'^(?:set_option[^\n]* in\s*)?(?:private\s+)?(def|theorem|abbrev|structure|lemma)\s+'+re.escape(nm)+r'(?=[\s(\{\[:])')
    idx=[i for i,l in enumerate(L) if pat.match(l)]
    if not idx: print(f'-- {nm}: NOT FOUND'); continue
    i=idx[0]; kind=pat.match(L[i]).group(1); j=i
    if kind in ('def','abbrev','structure'):
        while j+1<len(L) and L[j+1].strip()!='': j+=1
    else:
        while j<len(L) and not re.search(r':=\s*(by)?\s*$',L[j]) and ':= by' not in L[j]: j+=1
    print(f'-- {nm} (probe lines {i+1}-{j+1})')
    for l in L[i:j+1]: print(l)
```

### fqn_clash.py  (namespace-aware name-clash check)

```python
#!/usr/bin/env python3
"""Namespace-aware name-clash check: fully qualified declaration names of the probe against those of the library at main (RBM3D/, without Probe/).
usage: fqn_clash.py PROBE MAINROOT"""
import re, sys, os
PROBE, ROOT = sys.argv[1], sys.argv[2]
decl=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*(?:set_option[^\n]*?\s+in\s+)?(def|theorem|lemma|abbrev|structure|inductive|class)\s+([^\s({\[:]+)')
priv=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?private\s')
def fqns(path):
    stack=[]; out=[]
    for l in open(path,encoding='utf-8'):
        s=l.rstrip('\n')
        m=re.match(r'^namespace\s+(\S+)',s)
        if m: stack.append(('ns',m.group(1))); continue
        m=re.match(r'^section(?:\s+(\S+))?\s*$',s)
        if m: stack.append(('sec',m.group(1) or '')); continue
        m=re.match(r'^end(?:\s+(\S+))?\s*$',s)
        if m and stack: stack.pop(); continue
        m=decl.match(s)
        if m:
            nm=m.group(2); pre='.'.join(n for k,n in stack if k=='ns')
            full=(pre+'.'+nm) if pre else nm
            out.append((full, bool(priv.match(s))))
    return out
pn=fqns(PROBE)
lib={}
for dp,dn,fn in os.walk(os.path.join(ROOT,'RBM3D')):
    if '/Probe' in dp: continue
    for f in fn:
        if f.endswith('.lean'):
            p=os.path.join(dp,f)
            for full,pv in fqns(p):
                lib.setdefault(full,[]).append(os.path.relpath(p,ROOT))
pub=[n for n,pv in pn if not pv]
clash=[(n,lib[n]) for n in pub if n in lib]
print(f'probe declarations: {len(pn)} ({len(pub)} public); library declarations at main (without Probe/): {len(lib)} fully qualified names')
print(f'fully qualified public probe names that also occur in the library: {len(clash)}')
for n,fs in clash: print(' ',n,'<-',', '.join(sorted(set(fs))))
# probe names in RBM.Gauss.Sizes / RBM (outside RBM.Probe) — the ones a later move into the library would have to keep distinct
ns=[n for n in pub if not n.startswith('RBM.Probe.')]
print(f'public probe names outside RBM.Probe.*: {len(ns)}; of them clashing: {len([n for n in ns if n in lib])}')
```

### cmp_defs.py  (copies against the merged pins)

```python
#!/usr/bin/env python3
"""Compare the ST-1 pin copies of the T2039 probe with the merged Induction/Defs.lean (T2028) and Step34Pins (T2049)."""
import re, sys, subprocess
PROBE='/Users/junyin/Lean_proof/RBM3D-wt/T2039/RBM3D/Probe/T2039Pins.lean'
MAIN='/Users/junyin/Lean_proof/RBM3D/RBM3D/Induction/Defs.lean'
MAIN2='/Users/junyin/Lean_proof/RBM3D/RBM3D/Induction/Step34Pins.lean'
def decls(path, lim=None):
    L=open(path,encoding='utf-8').read().split('\n')
    out={}
    pat=re.compile(r'^(?:private\s+)?(def|abbrev|structure|theorem|lemma)\s+([^\s({\[:]+)')
    i=0
    while i<len(L):
        m=pat.match(L[i])
        if m:
            name=m.group(2); j=i
            while j+1<len(L) and L[j+1].strip()!='' : j+=1
            body=' '.join(x.strip() for x in L[i:j+1])
            body=re.sub(r'\s+',' ',body)
            out.setdefault(name,(i+1,body))
            i=j+1
        else: i+=1
    return out
P=decls(PROBE)
M=decls(MAIN); M2=decls(MAIN2)
names=sys.argv[1:]
for nm in names:
    p=P.get(nm); m=M.get(nm) or M2.get(nm)
    if p is None: print(f'{nm}: not in probe'); continue
    if m is None: print(f'{nm}: not in merged'); continue
    print(f'{nm}: probe line {p[0]}, merged line {m[0]}: {"IDENTICAL" if p[1]==m[1] else "DIFFERENT"}')
    if p[1]!=m[1]:
        print('  probe :',p[1][:600]); print('  merged:',m[1][:600])
```

### mathlib_names.py  (Mathlib names of the probe (c))

```python
#!/usr/bin/env python3
"""Distinct Mathlib-namespace names used by the probe (comments and docstrings stripped, names defined in the probe removed);
writes mathlib_check.lean (`#check @name` for each) to be run with `lake env lean`; every name resolving means 'verified'."""
import re, sys
P = sys.argv[1]
src = open(P, encoding='utf-8').read()
src = re.sub(r'/-.*?-/', '', src, flags=re.S)
src = re.sub(r'--[^\n]*', '', src)
ns = ['Real','Finset','Filter','MeasureTheory','ProbabilityTheory','Complex','Matrix','ENNReal','NNReal','Nat','Fin','List','Set','Equiv','ZMod','Function','Measurable','Summable','Tendsto','Eventually','Int','Bool','Ring','Monotone','Antitone','IsStoppingTime','Measure']
pat = re.compile(r'(?<![A-Za-z0-9_.])((?:' + '|'.join(sorted(set(ns))) + r')\.[A-Za-z_][A-Za-z_0-9\'.]*[A-Za-z_0-9\'])')
names = sorted(set(m.group(1) for m in pat.finditer(src)))
local = set(re.findall(r'(?:theorem|def|lemma)\s+([A-Za-z_][A-Za-z_0-9\'.]*)', src))
names = [n for n in names if n not in local]
with open('mathlib_check.lean', 'w', encoding='utf-8') as f:
    f.write('import RBM3D.Probe.T2039Pins\nopen MeasureTheory ProbabilityTheory Filter Matrix\nopen scoped NNReal ENNReal\n')
    for n in names: f.write(f'#check @{n}\n')
print(len(names), 'names')
```

### cites.py  (RBM2D file:line citations of P.1-P.8 against c9a24cf)

```python
#!/usr/bin/env python3
"""Check every `Dir/File:line[–line]` citation of the portmap against RBM2D at c9a24cf (file exists, line range inside the file)."""
import re, subprocess, sys
REF = 'c9a24cf'; repo = '/Users/junyin/Lean_proof/RBM2D'
txt = open(sys.argv[1], encoding='utf-8').read()
# only the sections before P.10 (the scripts contain their own text)
txt = txt.split('## P.10')[0]
pat = re.compile(r'((?:Path|Induction|Hierarchy|Gauss|Green|Evolution|Loop|Defs|Main)/[A-Za-z0-9_]+)(?:\.lean)?:(\d+(?:[–-]\d+)?(?:,\d+(?:[–-]\d+)?)*)')
cache = {}
def nlines(f):
    if f not in cache:
        r = subprocess.run(['git', '-C', repo, '--no-optional-locks', 'show', f'{REF}:RBM2D/{f}.lean'], capture_output=True, text=True)
        cache[f] = None if r.returncode != 0 else r.stdout.count('\n')
    return cache[f]
import os
tot = bad = 0; missing = set(); outside = []; r3 = 0
for m in pat.finditer(txt):
    f, spec = m.group(1), m.group(2)
    n = nlines(f)
    for part in spec.split(','):
        nums = [int(x) for x in re.split(r'[–-]', part)]
        tot += 1
        if n is None:
            if os.path.exists(f'/Users/junyin/Lean_proof/RBM3D/RBM3D/{f}.lean'): r3 += 1   # a citation of an RBM3D file, not checked here
            else: missing.add(f); bad += 1
        elif max(nums) > n: outside.append((f, part, n)); bad += 1
print(f'citations {tot}; RBM2D files {len([k for k,v in cache.items() if v is not None])}; RBM3D citations (not checked) {r3}; not found anywhere: {sorted(missing)}; line range beyond the file: {outside}; failures {bad}')
```

### axcheck.lean  (axioms of every declaration of the compiled module)

```lean
import RBM3D.Probe.T2039Pins
open Lean Elab Command Meta

elab "#axcheck" : command => do
  let env ← getEnv
  let some mi := env.getModuleIdx? `RBM3D.Probe.T2039Pins | throwError "module not found"
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  let mut bad : Array Name := #[]
  let mut thms : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some mi then
      if n.isInternal || n.isInaccessibleUserName then continue
      let axs ← liftCoreM (collectAxioms n)
      total := total + 1
      if ci.isTheorem then thms := thms + 1
      if !(axs.all (fun a => std.contains a)) then bad := bad.push n
  logInfo m!"checked {total} declarations of RBM3D.Probe.T2039Pins ({thms} theorems); declarations using an axiom outside [propext, Classical.choice, Quot.sound] (incl. sorryAx): {bad}"
#axcheck
```

### contract.py  (F4: contraction inequality)

```python
import numpy as np, itertools, math, sys
rng=np.random.default_rng(7)
d,W,L=3,2,int(sys.argv[1]) if len(sys.argv)>1 else 3
n=W*L; N=n**d
pts=list(itertools.product(range(n),repeat=d)); blk=[tuple(c//W for c in p) for p in pts]
blocks=list(itertools.product(range(L),repeat=d)); bidx={b:i for i,b in enumerate(blocks)}
def zd(a,b,m): t=(a-b)%m; return min(t,m-t)
def dinf(a,b): return max(zd(a[i],b[i],L) for i in range(d))
E=[np.diag([1.0/W**d if blk[i]==a else 0.0 for i in range(N)]) for a in blocks]
def band_H(g):
    def SB(a,b):
        dist=sum(zd(a[i],b[i],L) for i in range(d))
        return (1.0 if dist==0 else (g*g if dist==1 else 0.0))/(1+2*d*g*g)
    S=np.array([[SB(blk[i],blk[j])/W**d for j in range(N)] for i in range(N)])
    X=rng.standard_normal((N,N))+1j*rng.standard_normal((N,N)); X=np.triu(X,1)/math.sqrt(2); X=X+X.conj().T+np.diag(rng.standard_normal(N))
    return X*np.sqrt(S)
def full_H():
    X=rng.standard_normal((N,N))+1j*rng.standard_normal((N,N)); X=(X+X.conj().T)/math.sqrt(2*N)*1.5
    return X
worst=0.0; worst_pt=0.0; minL6=1e9
for kind,Hf in (("band g=.5",lambda: band_H(0.5)),("full",full_H)):
    H=Hf()
    for eta in (0.5,0.05,0.005):
        z=0.3+1j*eta
        Gp=np.linalg.inv(H-z*np.eye(N)); Gm=Gp.conj().T
        for (s1,s2) in ((1,1),(1,-1),(-1,1),(-1,-1)):
            G1,G1b=(Gp,Gm) if s1==1 else (Gm,Gp)
            G2,G2b=(Gp,Gm) if s2==1 else (Gm,Gp)
            a=bidx[(0,0,0)]
            for bb in (bidx[(0,0,0)],bidx[(1,0,0)],bidx[(1,1,2%L)]):
                P=E[a]@G2@E[bb]
                A=[G1@E[c]@G1b for c in range(len(blocks))]
                B=[G1b@E[c]@G1 for c in range(len(blocks))]
                L6=np.zeros((len(blocks),len(blocks)),dtype=complex)
                for cp in range(len(blocks)):
                    Y=P@A[cp]@P.conj().T
                    for c in range(len(blocks)): L6[cp,c]=np.trace(B[c]@Y)
                minL6=min(minL6,L6.real.min()); 
                assert abs(L6.imag).max()<1e-9*max(1,abs(L6).max())
                L4alt=np.array([np.trace(A[cp]@E[bb]@A[cp]@E[bb]).real for cp in range(len(blocks))])
                L4p=np.array([np.trace(G1@E[a]@G2@E[bb]@G2b@E[a]@G1b@E[c]) for c in range(len(blocks))])
                L3=[abs(np.trace(Gs@E[a]@G2@E[bb]@G2b@E[a])) for Gs in (Gp,Gm)]
                # pointwise L6 <= sqrt(L4alt(c')) * L4'(c)
                pw=(L6.real/(np.sqrt(np.maximum(L4alt,1e-300))[:,None]*abs(L4p)[None,:])).max()
                worst_pt=max(worst_pt,pw)
                for 𝒜 in ([bidx[(0,0,0)]],[bidx[(1,0,0)],bidx[(0,1,0)]],list(range(len(blocks)))):
                    lhs=sum(L6[cp,c].real for cp in 𝒜 for c in range(len(blocks)) if dinf(blocks[cp],blocks[c])<=1)
                    rhs=3**d/(W**d*eta)*max(math.sqrt(L4alt[cp]) for cp in 𝒜)*max(L3)
                    worst=max(worst,lhs/rhs)
print("d=3 W=2 L=%d N=%d: min Re L6 = %.3e (>=0); max pointwise L6/(sqrt(L4alt)*|L4'|) = %.4f; max LHS/RHS(const 3^d) = %.4f"%(L,N,minL6,worst_pt,worst))
```

### ttt2.py  (F14 (a))

```python
#!/usr/bin/env python3
"""Extreme-input check of (TTT2) (lem:propT, 3_5:328) used by lem:newKLK (STNewKLK): the ratio
R = max_a  (1-u) * sum_c T_u(|a-c|) T_t(|c|) / T_t(|a|)   on Z_L^d, d = 3, both for the paper's L^infty distance and the l^1 distance (merged EKPropT),
T_t(r) = B_{t,r} exp(-sqrt(r/ell_t)), B_{t,r} = (g^2+x)^-1 (r+1)^(2-d) + (L^d x)^-1, x = 1-t, ell_t = min(max(g/sqrt x,1),L).
Regimes: (i) 1-t >= g^2/L^2 (any u<=t); (ii) 1-t <= 1-u <= g^2/L^2.  Extreme inputs: u = t, 1-t -> g^2/L^d, L large."""
import numpy as np, itertools, sys
d=3
def run(L,g,xu,xt):
    ax=np.arange(L); ax=np.minimum(ax,L-ax)
    I,J,K=np.meshgrid(ax,ax,ax,indexing='ij')
    rinf=np.maximum(np.maximum(I,J),K).astype(float); r1=(I+J+K).astype(float)
    def T(x,r):
        ell=min(max(g/np.sqrt(x),1.0),float(L))
        B=1.0/(g*g+x)*(r+1.0)**(2-d)+1.0/(L**d*x)
        return B*np.exp(-np.sqrt(r/ell))
    out={}
    for name,r in (('Linf',rinf),('l1',r1)):
        f=T(xu,r); h=T(xt,r)
        conv=np.real(np.fft.ifftn(np.fft.fftn(f)*np.fft.fftn(h)))
        ratio=conv*xu/h
        out[name]=ratio.max()
    return out
print('d=3; R = max_a (1-u) (T_u * T_t)(a) / T_t(|a|)  (should stay O(1) uniformly in L, g, u, t)')
print('%3s %7s %-34s %10s %10s'%('L','g','regime (1-u, 1-t)','R_Linf','R_l1'))
for L in (6,12,24):
    for g in (0.5,0.1):
        gl2=g*g/L**2; gld=g*g/L**d
        cases=[('(i) u=t, 1-t=0.5',0.5,0.5),
               ('(i) u=0, 1-t=g^2',1.0,g*g),
               ('(i) u=t, 1-t=g^2/L^2 (boundary)',gl2,gl2),
               ('(i) 1-u=1, 1-t=g^2/L^2',1.0,gl2),
               ('(ii) u=t, 1-t=g^2/L^2',gl2,gl2),
               ('(ii) u=t, 1-t=g^2/L^d (extreme)',gld,gld),
               ('(ii) 1-u=g^2/L^2, 1-t=g^2/L^d',gl2,gld),
               ('(ii) 1-u=1-t=1e-3 g^2/L^d',1e-3*gld,1e-3*gld)]
        for nm,xu,xt in cases:
            o=run(L,g,xu,xt)
            print('%3d %7.3g %-34s %10.3f %10.3f'%(L,g,nm,o['Linf'],o['l1']))
```

### ttt2big.py  (F14 (a), large L)

```python
import numpy as np
d=3
def run(L,g,xu,xt):
    ax=np.arange(L); ax=np.minimum(ax,L-ax)
    I,J,K=np.meshgrid(ax,ax,ax,indexing='ij')
    rinf=np.maximum(np.maximum(I,J),K).astype(np.float64); r1=(I+J+K).astype(np.float64)
    def T(x,r):
        ell=min(max(g/np.sqrt(x),1.0),float(L))
        B=1.0/(g*g+x)*(r+1.0)**(2-d)+1.0/(L**d*x)
        return B*np.exp(-np.sqrt(r/ell))
    res=[]
    for r in (rinf,r1):
        f=T(xu,r); h=T(xt,r)
        conv=np.real(np.fft.ifftn(np.fft.fftn(f)*np.fft.fftn(h)))
        res.append((conv*xu/h).max())
    return res
for L in (12,24,48,72,96):
    a=run(L,0.1,0.5,0.5); b=run(L,0.1,1.0,1e-2)
    print('L=%3d  (i) u=t, 1-t=0.5: R_Linf=%8.1f R_l1=%8.1f   |  (i) 1-u=1, 1-t=0.01: R_Linf=%8.1f R_l1=%8.1f'%(L,a[0],a[1],b[0],b[1]))
```

### theta_decay.py  (F14 (b))

```python
#!/usr/bin/env python3
"""Extreme-input check of STK2decay (3_5:457, 518): |K^(2)_{u,sigma,a}| = W^-d |Theta_{u m1 m2}(a1,a2)| <= C W^-d T~^L_{u,D}(|a1-a2|),
i.e.  max_a |Theta_{u M}(0,a)| / (B_{u,|a|_inf} exp(-sqrt(|a|_inf/ell_u)))  stays O(1) uniformly in L, g, u (Theta = (1 - u M S^B)^-1,
S^B = circulant(1/(1+2dg^2) at 0, g^2/(1+2dg^2) at l1-distance 1), M = m1 m2 with |m| = 1: M = 1 (sigma=(+,-)), M = e^{i t} for (+,+) at E=0: M=-1, E=1: M = e^{2 i pi/3} ...)."""
import numpy as np, cmath
d=3
def run(L,g,x,M):
    k=2*np.pi*np.arange(L)/L
    c=np.cos(k)
    K1,K2,K3=np.meshgrid(c,c,c,indexing='ij')
    Sh=(1+2*g*g*(K1+K2+K3))/(1+2*d*g*g)
    u=1-x
    Th=np.fft.ifftn(1.0/(1-u*M*Sh))
    ax=np.arange(L); ax=np.minimum(ax,L-ax)
    I,J,Kk=np.meshgrid(ax,ax,ax,indexing='ij')
    r=np.maximum(np.maximum(I,J),Kk).astype(float)
    ell=min(max(g/np.sqrt(x),1.0),float(L))
    B=1.0/(g*g+x)*(r+1.0)**(2-d)+1.0/(L**d*x)
    T=B*np.exp(-np.sqrt(r/ell))
    return (np.abs(Th)/T).max(), np.abs(Th)[0,0,0]/T[0,0,0]
Ms=[('M=1 (+,-)',1.0),('M=-1 (E=0,(+,+))',-1.0),('M=e^{2i pi/3} (E=1,(+,+))',cmath.exp(2j*cmath.pi/3))]
print('%3s %6s %-26s %-34s %9s %9s'%('L','g','M','regime (x=1-u)','max ratio','ratio a=0'))
for L in (6,12,24,48):
    for g in (0.5,0.1):
        gl2=g*g/L**2; gld=g*g/L**d
        for mn,M in Ms:
            for nm,x in (('x=0.5',0.5),('x=g^2',g*g),('x=g^2/L^2',gl2),('x=g^2/L^d (extreme)',gld),('x=1e-3 g^2/L^d',1e-3*gld)):
                mx,r0=run(L,g,x,M)
                print('%3d %6.2f %-26s %-34s %9.3f %9.3f'%(L,g,mn,nm,mx,r0))
```

### scale_family.py  (F14 (f): STScaleExists)

```python
#!/usr/bin/env python3
"""Extreme-input check of `STScaleExists` (STScaleAdm, (eq:def_ell1), 3_5:571-577) at d = 3 along the MD-1 sequence sz0 (L_n = 4(n+1), W_n = (2(n+1))^5, g_n = (2(n+1))^-6):
K_0 = 0; K_{m+1}(u) = min(L, inf{r >= K_m(u) : T_u(r) <= b_u^{1/6} T_u(K_m(u))}), T_u(r) = B_{u,r} exp(-sqrt(r/ell_u)), b_u = W^-d B_{u,0}.
Checks: (i) u -> T_u(K_m(u)) is nondecreasing on a grid of u in [0, 1-x_min] (x = 1-u from 1 down to x_min = N^(-1+eps) and below g^2/L^d);
        (ii) the number M of steps until T_u(K_M(u)) <= W^-D or K_M(u) = L, maximum over the grid."""
import math
d = 3
eps = 0.1
def run(n, D):
    L = 4 * (n + 1); W = float((2 * (n + 1)) ** 5); g = float(2 * (n + 1)) ** -6
    N = (W * L) ** d
    B = lambda x, r: 1 / (g * g + x) / (r + 1) ** (d - 2) + 1 / (L ** d * x)
    ell = lambda x: min(max(g / math.sqrt(x), 1.0), float(L))
    T = lambda x, r: B(x, r) * math.exp(-math.sqrt(r / ell(x)))
    b = lambda x: B(x, 0) / W ** d
    xmin = N ** (-1 + eps)
    xs = [10 ** (-k / 4) for k in range(0, 80)]
    xs = [x for x in xs if x >= xmin] + [xmin]
    xs = sorted(set(xs), reverse=True)            # x = 1-u decreasing = u increasing
    def Kseq(x):
        K = [0.0]
        while len(K) < 400:
            k = K[-1]; target = b(x) ** (1 / 6) * T(x, k)
            if T(x, L) > target: K.append(float(L)); break
            lo, hi = k, float(L)                  # T_u decreasing in r: bisection for T_u(r) = target
            for _ in range(80):
                mid = (lo + hi) / 2
                if T(x, mid) > target: lo = mid
                else: hi = mid
            K.append(hi)
            if T(x, K[-1]) <= W ** (-D): break
        return K
    worstM = 0; mono = True
    prev = None
    for x in xs:
        K = Kseq(x); worstM = max(worstM, len(K) - 1)
        vals = [T(x, k) for k in K]
        if prev is not None:
            for m in range(min(len(prev), len(vals))):
                if vals[m] < prev[m] * (1 - 1e-9): mono = False
        prev = vals
    return L, W, g, N, xmin, g * g / L ** d, len(xs), mono, worstM
print('%2s %4s %10s %10s %10s %10s %6s %8s %4s %3s' % ('n', 'L', 'W', 'g', 'x_min=N^-.9', 'g^2/L^d', 'grid', 'T_u(K_m) monotone in u', 'D', 'maxM'))
for n in (0, 1, 3, 9):
    for D in (3, 10):
        L, W, g, N, xmin, gld, ng, mono, M = run(n, D)
        print('%2d %4d %10.3g %10.3g %10.3g %10.3g %6d %8s %26d %3d' % (n, L, W, g, xmin, gld, ng, mono, D, M))
```

### mat_extreme.py  (F14 (e))

```python
#!/usr/bin/env python3
# Extreme-input check of the two Step 2 local laws (preflight (a) (ii) extended): 1-u down to and below g^2/L^d, d = 3, W = 2, L = 3 and 4.
import numpy as np, itertools, math, sys
rng = np.random.default_rng(20261003)
d, W = 3, 2
g = 0.5
E = 0.0
S_SAMP = int(sys.argv[2]) if len(sys.argv) > 2 else 60
L = int(sys.argv[1]) if len(sys.argv) > 1 else 3
n = W * L
N = n ** d
Bf = lambda x, K: 1 / (g * g + x) / (K + 1) ** (d - 2) + 1 / (L ** d * x)
pts = list(itertools.product(range(n), repeat=d))
blk = lambda p: tuple(c // W for c in p)
def zd(a, b, m): t = (a - b) % m; return min(t, m - t)
bl = [blk(p) for p in pts]
def SB(a, b):
    dist = sum(zd(a[i], b[i], L) for i in range(d))
    return (1.0 if dist == 0 else (g * g if dist == 1 else 0.0)) / (1 + 2 * d * g * g)
S = np.array([[SB(bl[i], bl[j]) / W ** d for j in range(N)] for i in range(N)])
Dist = np.array([[sum(zd(pts[i][c], pts[j][c], n) for c in range(d)) for j in range(N)] for i in range(N)])
blocks = sorted(set(bl))
Ea = [np.diag([1.0 / W ** d if bl[i] == a else 0.0 for i in range(N)]) for a in blocks]
m = (-E + 1j * math.sqrt(4 - E * E)) / 2
Dvals = sorted(int(v) for v in set(Dist.flatten()))
def sample():
    X = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
    X = np.triu(X, 1) / math.sqrt(2); X = X + X.conj().T
    X = X + np.diag(rng.standard_normal(N))
    return X * np.sqrt(S)
Hs = [sample() for _ in range(S_SAMP)]
gld = g * g / L ** d
print("d=3 W=%d L=%d N=%d g=%.2f samples=%d;  g^2=%.4g g^2/L^2=%.4g g^2/L^d=%.4g" % (W, L, N, g, S_SAMP, g * g, g * g / L ** 2, gld))
for name, x in [("1-u = 2 g^2/L^d", 2 * gld), ("1-u = g^2/L^d (extreme)", gld), ("1-u = 0.3 g^2/L^d", 0.3 * gld), ("1-u = 0.1 g^2/L^d", 0.1 * gld)]:
    u = 1 - x; z = E + x * m.real + 1j * x * m.imag
    ent = np.zeros(len(Dvals)); mx = np.zeros(len(Dvals)); tr = []
    for H in Hs:
        G = np.linalg.inv(math.sqrt(u) * H - z * np.eye(N)); D = G - m * np.eye(N)
        A = np.abs(D) ** 2
        for k, dv in enumerate(Dvals):
            msk = (Dist == dv); ent[k] += A[msk].mean(); mx[k] = max(mx[k], A[msk].max())
        tr.append(max(abs(np.trace(D @ Ea_)) for Ea_ in Ea))
    ent /= S_SAMP
    bound = np.array([Bf(x, dv / W) / W ** d for dv in Dvals])
    r1 = (ent / bound)[:6]; r2 = (mx / bound)[:6]
    print("%-24s x=%.3g N*eta=%.2f  mean-ratio[%.2f..%.2f]  max-ratio %.1f  trace-ratio %.2f" % (
        name, x, N * x, r1.min(), r1.max(), r2.max(), np.mean(tr) / (Bf(x, 0) / W ** d)))
```
