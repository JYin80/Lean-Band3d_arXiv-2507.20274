# T2326 pilot (BA-DP3): route G measured at two sites; chain estimate, route totals, recommended route and cap

Written Thu Oct  8 12:06:14 UTC 2026 (`date -u`). Prover `claude-sonnet-5-5` (prover-max). Branch `t/T2326`, commits `51ec793`, `688b372`, `4fca3d2` (probe files only, never merged): `RBM3D/Probe/T2326PilotStep2.lean` 909 lines, `RBM3D/Probe/T2326PilotQ.lean` 878 lines (1787 ≤ 2500). Evidence (commands, verbatim output): `docs/reports/T2326-prove.md` (b), cited "B0..B7", and section 10 below. Inputs: `T2325-portmap.md` (§3, §5, §7), `T2325-prove.md` B3-B6, supervisor `2026-10-08-0944.md`, DECISIONS §142, §144 (Jun: BA is proved in full, no cap, one supervisor gate per stage), `BA/FlowPins.lean:300-600`, the two merged blocks. `file:line` at base `cc1158a`; "tickets" = lines/1000 (T2325 §7).

## 0. The answer
| quantity | value |
|---|---|
| g, site 1: `ST_selfImprove_section`, `Step2Iterate.lean:277-667` (391 lines) | 58/391 = **0.148** (hunk-wise 61/391 = 0.156; tokens 0.048) |
| g, site 2: `QDriftA.lean:54-637` (584 lines; 22 declarations of the exact cone of `stStep3RegI_holds` + measurability) | 177/584 = **0.303** (added lines only 90/584 = 0.154; tokens 0.176) |
| g, both blocks | 235/975 = 0.241 |
| g calibrated for the chain | **0.20** = 1.99 edit lines per band-mention line (both sites) × 0.100 band-mention density of the chain (section 5, script output in section 10) |
| ST Steps 2-6 chain under route G | **38.9 tickets** [33 .. 61]; route I 78, route T 92 (T2325 §7) |
| BA total with the K/G correction (+22.5) | **G 141 [136 .. 163]**; I 185.5; T 196.5 |
| g at which route G stops beating route I on the chain | 0.70 (f_sem 0.125), 0.67 (f_sem 0.30) |
| recommended BA planning cap | **165 tickets**: route G for T/U/V (after ST-4..ST-6 close), route I for the graph layer; 200 if route G is not adopted (supervisor 0944 Q2). Under DECISIONS §144 this is a planning figure for the stage gates, not a request. |

Reading. Two blocks of different kinds (a stochastic bootstrap with 7 lemma calls; a deterministic operator-algebra file with measurability proofs) both restate over a carrier with 15% to 30% of their lines edited, and both band instances recover the merged statements by compiled theorems. The calibration on the density of band mentions gives 0.20 for the chain. Route G beats route I by about 44 tickets (185.5 against 141.4) and route T by 55. The saving is paid for by: in-place edits of the ST files after ST closes, about 15 carriers with band and BA instances, wrappers for at most 167 frozen signatures, and the semantic share of the chain (proof-level unfolding of primitive band objects, 12.5% of declaration lines by a proxy), which is counted at the twin rate.

## 1. What was restated
| | site 1 | site 2 |
|---|---|---|
| merged block | `Step2Iterate.lean:277-667`: option line and docstring 7, statement 19, proof 365 (391 lines) | `QDriftA.lean:54-637`, 584 lines: `:54-497` vocabulary and targets 2-6 (the 22 declarations reached from `stStep3RegI_holds`, B6), `:499-637` target 7 (measurability, not reached) |
| left out | rest of the file, 1670 lines (instance section `:1851-2061`, 211 lines) | instance section `:639-1341`, 703 lines |
| generic block | 391 lines, 333 equal to the merged text | 497 lines, 407 equal |
| carrier | `Step2Data sz extends FlowFM sz`: 19 fields (E, t₀, two laws, matrix flow, grid walk, `(L-K)` of a matrix, flow setting, `Im m` bound, 7 opaque predicates, 3 pins) + 6 base facts; `Step2Facts Cm`: the 7 lemmas of other blocks the proof calls | `QKerData d`: 3 data + EK-4; `QDriftData sz`: 9 data + 7 facts (Θ sum-zero, good-set class, 5 measurability facts) |
| merged statements recovered | `recovers_merged : type_of% @ST_selfImprove_section` | 11 `recovers_*` theorems (targets 2-7; statements about a real energy `E` through the constant sequence `fun _ => E`) |
| nonempty instances, `d = 3` | 1 `example` (data of `Step2Iterate.lean:1937-1948`) | 7 `example`s (targets 2, 3, 4a and the four measurability targets; data of `QDriftAInst`) |
| block Anderson reading compiled | base layer (5 declarations) and `baStep2`: the whole carrier at the BA flow, the 11 open obligations as arguments | none |
| build | `lake build` 21 s, axioms standard (15 declarations) | `lake build` 4.1 s, axioms standard (32 declarations) |
Why these sites. Site 1 is the supervisor's (0944 O2). Site 2 is the ticket's named Q-file: the exact cone of `stStep3RegI_holds` contains it (22 declarations) and the substitution suggested by (a) fails (`QtNonzeroFlow` is in the cone of `stStep3II_holds` only; prove report (a′)).

## 2. The edited fraction g (B5)
| | merged lines | `git diff --numstat` added / removed | g = max / merged | hunk-wise (difflib) | tokens |
|---|---|---|---|---|---|
| site 1 | 391 | 58 / 58 | 0.148 | 39 hunks, cost 61 (0.156) | 268 of 5567 (0.048) |
| site 2 | 584 | 90 / 177 | 0.303 | 62 hunks, cost 177 | 1390 of 7877 (0.176) |
| both | 975 | 148 / 235 | 0.241 | | |
Anatomy. Site 1: statement 12 of 19 lines edited, proof 49 of 365: flow facts (`(mE (STflowE z n)).im` becomes `(Cm.m n).im`, `lemT` becomes `Cm.T0`, `hflow.1..` becomes `Cm.flowOK_adm`) 25, matrix-level objects (`STJhatM`, `STGoodAt`, `seqHflow`, `pathH`, `STLKM`) 11, replacement of the 7 lemma calls by `Fa.*` 10, other 3. Site 2: 87 of the 177 removed lines are pure deletions whose text moves unchanged into the band instance (the private measurability helpers `:505-562`, 60 lines; `QDriftA_qProxy4C_spec`, 20; `QDriftA_meas_ThetaN`, 7); the other 90 are signatures (`(sz : Sizes d) (n : ℕ) (E u : ℝ)` becomes `(Cq : QDriftData sz) (n : ℕ) (u : ℝ)`) and field applications. Counting only changed or added lines (the ticket's wording) gives 0.148 and 0.154; the deletions count in g because the text has to be written again in the instance.

## 3. The interface the carriers need (line counts of the probe files by segment; script in section 10)
| segment | site 1 | site 2 |
|---|---|---|
| carrier structures | 66 (`Step2Data`) | 28 (`QKerData`) + 61 (`QDriftData`) |
| generic readings of definitions of other files | 47 (`JhatG`, `JhatG_measurable`, `STScaleInvgL`, `GridMartPin`) | 35 (`AvecN`, `aTrueQN`, `dGridQN`) |
| statements of lemmas of other blocks | 118 (`Step2Facts`, 7 lemmas) | in the carrier facts above |
| band instance | 93 (`bandStep2`, `bandStep2Facts`, pin bridge) | 111 (`bandKer`, `bandQ`, private copies of the moved text) |
| recovery theorems and examples | 8 + 18 | 40 + 52 |
| compiled block Anderson reading | 45 (section 7, base layer) + 54 (section 8, `baStep2`) | none |
The generic statements of other blocks (118 lines at site 1) are the statements those blocks have after their own conversion; in the chain count they are inside the `g` of those blocks. The carrier, the generic readings, the band instance and the recoveries are the overhead of a carrier family (214 lines at site 1, 275 at site 2).

## 4. What the block Anderson instance has to supply (merged BA files, cited; new work with size)
Site 1 (`Step2Data`, `Step2Facts`):
| field or fact | band reading | block Anderson | status, size |
|---|---|---|---|
| `toFlowFM` | `bandFM` (`FlowPins:469`) | `baFMz` (`FlowPins:550`, from `baFM` `:479`) | merged |
| `E`, `T0`, `flowOK`, `flowOK_adm` | `STflowE`, `lemT`, `STFlow` | `BAflowEs` (`:540`), `BAflowT0` (`:537`), `BAFlow` (`:546`) | merged; `flowOK_adm` is its first component |
| `μ`, `Pp`, `Hflow` | `seqP sz`, `pathP sz`, `seqHflow` | `seqP (sz.withLam 0)`, `pathP (sz.withLam 0)`, `seqHflowBA` (`Gauss/BlockAnderson:83`) | merged |
| `Hpath`, `LKM`, `LKM_eq`, `LKM_meas` | `pathH sz`, `STLKM`, `rfl`, `STLKM_measurable` | `baHpath`, `baLKM`, `baLKM_eq`, `baLKM_meas` | **compiled** in the probe (section 7, 45 lines with `flowOK_T`); `walk_measurable_loopFine` merged |
| `flowOK_T` | `lemT_lt_one` | `baFlow_T0_lt_one` from `BAt0_lt_one` (`MFixedPoint:285`); needs `0 < κ` (`Im m ≥ κ`), so the carrier fact takes `0 < κ` (found by this reading; the two generic-block lines that use it were already edited) | **compiled** |
| `imLow`, `flowOK_m`, `imLow_pos` | `ST_mE_im_ge` (`Step2Events:555`, 9 lines) | `Im m ≥ κ` at `(E, g₀)` from `BAWinBulk` (`CouplingWindow:799`) and `BAm_im_lower` (`ImmLower:391`) | new, about 40 lines, not compiled |
| `ev1`-`ev4`, `Good`, `ident`, `martTail` | `ST_event_*` conclusions, `STGoodAt` (`Step2Core:963`, 22 lines), `STGridMartAt` (22) | same text with BA objects | new statements, about 90 lines |
| `pLWT`, `pEMe`, `pNew`, `GridMartPin` | `STLWT` (20), `STEMn2Exp` (24), `STNewKLKAt` (12), `STGridMartAt` (22) | BA pins | other rows: T2, T3, LW graph layer; discharged by those rows, not by the carrier |
| `Step2Facts` (7) | `ST_event_weak/init/lw/mg` (26, 46, 60, 76 lines), `ST_good_prob` (149), `ST_model_le_path` (16), `ST_good_engine` (310): 683 band lines | the generic versions of these blocks | route G: those blocks are converted like this one (`g` of the chain); leaf inputs are the pins above |
| `baStep2` (section 8) | | `Step2Data` at the BA flow of `z`: the data and base facts above filled; **11 arguments** = the open obligations: `ev1`-`ev4`, `Good`, `ident`, `martTail`, `pLWT`, `pEMe`, `pNew`, `flowOK_m` | **compiled**; the 11 are the obligations of this table |
Site 2 (`QKerData`, `QDriftData`):
| field or fact | band reading | block Anderson | status, size |
|---|---|---|---|
| `Ugen`, `dom`, `imm` | `Ugen` (`GridDuhamelN:65`), `E` in `[-2, 2]`, `(mE E).im` | propagator of `K = M^{(+,-)}` on tensors (`BAK` doubly stochastic: `BA/KKernel:124-133`) | new definition; BA-U row |
| `ek4` | `ekSumDecay2_holds` (`Evolution/SumDecayZero:1411`, file 1746 lines) at `m = mE E` | EK-4 for BA | priced: BA-E2 (T2161 portmap 1000/1500/2100; T2325 §5 revised 1500) |
| `ksim`, `elk`, `egt` and 3 measurability facts | `STksimLKM`, `STelklkM`, `STegtM` (`Step2Defs:723,737,750`: 23 lines) + 60 lines of measurability | BA copies of the definitions and proofs | new, about 85 lines (mostly moved text) |
| `Theta`, `Theta_meas`, `Theta_sumZero` | `ThetaN` (`Kernel/Evolution:60`), `QopAlgebra_ThetaN_sumZero` (`QopAlgebra:786`, 20 lines) + `qa_slot_zero/succ` (71) | BA `Θ` on tensors, sum-zero proof | new, about 100 lines |
| `GoodSet`, `goodSet_cls` | `GoodSetN` (`GridGoodN:124`, 45 lines), `goodSetN_A0clsN` (`NQGood2:284`, 19) | BA good set | new, about 65 lines |

## 5. From two blocks to the chain
Calibration. The edit cost tracks the number of lines that mention a band object (T2325 token list closed under the 454 band definitions of `Induction/`): site 1, 35 of 391 lines (0.090), 1.66 edit lines per mention; site 2, 83 of 584 (0.142), 2.13; both, 1.99. The chain files (97 files, non-instance part) have 9055 band-mention lines of 90,226 (0.100). Calibrated chain g = 1.99 × 0.100 = 0.20; the pair average (0.241) is higher because the two blocks are denser than the chain (0.090 and 0.142 against 0.100).
Instance sections. 24,772 of the chain's 114,998 file lines (21.5%; 36.0% in row U3, the 27 files of Steps 3-4) are instance sections. They are not edited under route G (the wrappers keep the band signatures), so `g` is applied to the 90,226 other lines; the BA instances of the endpoints are counted separately.
Semantic share. The two blocks are plumbing: band objects enter through names. A proof that unfolds a primitive band object cannot be made generic by renaming. Proxy: theorem lines whose proof names a primitive band object after `unfold/rw/simp/show/change`: 10,575 of 84,460 declaration lines (12.5%; T2325 B4 gives 10% for matrix-level declarations). These lines are counted at the twin rate 0.8 (T2325 §1: 0.73 and 0.85), not at `g`.
Chain under route G (section 10, `routeG2.py`; assumptions A1-A5 printed there): chain = (1-f)·S·g + f·S·0.8 + ST overhead + BA wiring + B_new, S = 90,226.
| scenario | g | f_sem | B_new | plumbing | semantic | ST overhead | BA wiring | chain tickets |
|---|---|---|---|---|---|---|---|---|
| low | 0.15 | 0.10 | 3.8k | 12.2k | 7.2k | 6.2k | 4.1k | 33.5 |
| **central** (calibrated g, proxy f) | 0.20 | 0.125 | 3.8k | 15.8k | 9.0k | 6.2k | 4.1k | **38.9** |
| pair g | 0.24 | 0.125 | 3.8k | 18.9k | 9.0k | 6.2k | 4.1k | 42.0 |
| f_sem 0.20 | 0.20 | 0.20 | 3.8k | 14.4k | 14.4k | 6.2k | 4.1k | 42.9 |
| high | 0.30 | 0.30 | 10k | 18.9k | 21.7k | 6.2k | 4.1k | 60.9 |
ST overhead = 15 carriers × 245 lines (the two probes: 214 and 275) + 167 wrappers × 15 lines (section 7). BA wiring = 15 BA carrier instances × 100 lines (the band instances: 93 and 111) + 43 BA endpoint instances × 60 lines. B_new = U5 + V2a + V2b + V3 (T2325 §3, BA-new rows 1300 + 1100 + 700 + 700); 10k is the preflight's sensitivity value.

## 6. Totals (tickets; T2325 §7 components; the K/G correction of supervisor 0944 Q1 is +20 to +25, 22.5 used)
| route | used | group A | chain | graph L2c-L4 | publishing | total [range] | + K/G |
|---|---|---|---|---|---|---|---|
| **G** (chain generic in place, graph route I) | 26 | 25 | 38.9 [33..61] | 27 | 2 (LW) | **118.9 [113..141]** | **141.4 [136..163]** |
| I (instantiate where possible) | 26 | 25 | 78 | 27 | 7 | 163 [128..214] | 185.5 |
| T (twin everything) | 26 | 25 | 92 | 31 | 0 | 174 [141..223] | 196.5 |
The script reproduces T2325's totals 163 and 174 before adding anything (section 10). Under G the five ST publishing tickets are not counted (the generic theorems replace the references to private helpers); the two LW ones stay for route I at the graph layer. Route G on the graph layer is not measured (T2325 §2: 38.8k twin lines there; only `expandG_sum`, `lvl1_size_le` and the Anp family are parametric).

## 7. What route G requires of ST, and when
- **Files.** 97 ST files (`Induction/`, the T2325 chain rows), 114,998 lines, edited in place after their gate closes. ST-side volume: plumbing 15.8k + overhead 6.2k lines, about 22 conversion tickets whose sole-writable files are the ST files of a row (precedent for editing merged ST files: T2313, primed successors).
- **Frozen signatures.** 2,280 public declarations in those files, 1,419 (62.2%) read a band object in their signature (directly or through one of 454 band definitions: section 10). Of these, **167** are referenced from files outside the chain (word match on the short name; 266 outside files): T8 49, U3 28, U6 21, T5 18, T4 15, V1 15, T1 14, U4 4, U1 1, U2 1, U5 1. Those need a wrapper under the old name (the probes' `recovers_*` are compiled wrappers; each is checked by `type_of%`, so the acceptance of a conversion ticket is mechanical) or a primed successor; the other 1,252 are consumed inside the chain and convert with their consumers. Private declarations (2,911) are not frozen.
- **Endpoints** (T2325 §3 col. 2, 43 names, all found at the cited lines): T1 `ST_selfImprove_section` (`Step2Iterate:284`), `ST_iterate` (:725), `ST_step2_of_pins` (:1393); T2 `stEMn2Poly_holds` (`EMn2Poly:838`), `stEMn2Exp_holds` (`EMn2Exp2:1090`); T3 `stNewKLK_holds` (`NewKLK:1198`), `stNewKLKAt_holds` (:1321); T6 `stContractPt_holds` (`ContractPt:463`), `stContract_holds` (`Contract:1046`); T7 `ST_good_prob` (`Step2Events:853`), `stDecayLoopAt_holds` (`DecayLoopA:938`), `stDecayLoopU_of_step2` (`DecayLoopB:1637`); T8 `STStep2` (`Step2Defs:599`), `STStep2Concl` (`Step34Pins:221`), `stStep2LocalPT_of_L2decay` (`LocalAvg2:321`); U1 `stIterations'_holds` (`IterationsB:570`), `stNewPQ_holds` (`NewPQ:584`), `stMollifierEx_holds` (`QopAlgebra:573`), `stQopNorm_holds` (`QopNorm:261`); U2 `stSEforLn_holds` (`SEforLn2:1287`), `stB45Pin_holds` (`B45:2943`), `stKcalDecay_holds` (`KDecay:798`); U3 `stStep3RegIII_holds`, `stStep3RegI_holds`, `stStep3II_holds` (`Step3:377,408,432`), `stStep4I_holds` (`Step4:189`), `STStep3R` (`Step34Pins:250`); U4 `ST_step5_caseI_of_pins` (`Step5Kit:292`), `ST_step5_caseII_of_pins` (`Step5Cases:542`), `stNewKLKL_holds` (`NewKLKL:836`), `stTailtoTail_holds` (`TailtoTail:582`), `stWardII_holds` (`WardII:269`), `stLemDecCalE_holds` (`LemDecCalEPrec:1550`); U5 `stStep5III_holds` (`PfStep5:2473`); U6 `STStep5R` (`Step5Pins:101`); V1 `ST_step6_case{III,IV,II,I}_of_pins` (`Step6Kit:737,786,865,947`), `stStep6IV_holds` (`ExpIntEasy:626`), `ST_step6I_of_LW_Int` (`ExpIntI:660`); V2 `ST_mainIndR_of_steps`, `ST_mainInd_of_regimes` (`MainIndRegimes:165,616`). Only 8 of the 43 have a consumer outside the chain files today (`STStep2`, `STStep2Concl`, `STStep3R`, `STStep5R`, `stStep5III_holds`, `stStep6IV_holds`, `ST_mainIndR_of_steps`, `ST_mainInd_of_regimes`); 10 are named in `Test/`.
- **The 167** (upper bound: word match on short names, so bare names such as `htT`, `z1` are false positives), by row, from `S/frozen2.py`:
```
T1 (14): ST_Lloop_one_false ST_Kloop_one STLKM_eq_STLKIM STLM_eq_STLIM STgA_eq_STgAN STeeLoop_one STeeLoop_two STEEM_eq_STeeM STgDrift_eq_STgDriftN ST_gridMart_of_repN ST_step2_of_pins' ST_step2_of_pinsN' htT stOptL2_of_pins
T4 (15): Ugen GridDuhamelN_Ugen_self GridDuhamelN_Ugen_comp GridDuhamelN_UgenHom GridDuhamelN_UgenHom_apply AvecN martIncN predIncN azumaSubGN z1 AzumaProxyN_stopW AzumaProxyN_YfieldsW gridDriftN_envelope gridAsm_stronglyMeasurable_ZvecN gridAsm_stronglyMeasurable_YvecN
T5 (18): stepErrN GridDriftN exists_norm_Kcal_le_win AbCN stepZCN_re stepZCN_im stepZCN loopFamN ZfamN ZvecN YvecN stepDecompCN stepDecompCN_Z_subG integrable_stepZCN_re_of_hermTestFun integrable_stepZCN_im_of_hermTestFun hermTestFunLoopN loopDerivN qvPropagatedN
T8 (49): STmsig STLM STLM_seqHflow STLKM STJhatM STavgM STEGtM STELKLKM STthetaOp STEEkM STEEM STGMM STStep2Local STStep2Avg STStep2Decay STStep2LocalPT STStep2AvgPT STStep2DecayPT STEEk STInitialGT2 STLWassmExp STNewKLKAt STNewKLK STLWB STLWT STEMn2Exp STgA STgDrift STGridMartAt STGridMart STstopIdx STK2decay STNetLift2 STStep2 STScaleExists STOptL2 STLocalAvgOfL2 STLIM STLKIM STksimLKM STelklkM STegtM STeeM STgAN STgDriftN STeeUM STGridRepNAt STGridRepN inst_step2
U1 (1): zeroModeSet_UN
U2 (1): B45_far_main
U3 (28): STKI STee STLmaxU STLKU STAvgU STLocalEntryU STGdecayW STStep2Concl STKward STStep3R STStep4R STStep3I STStep3II STStep4I STStep4II STLmax_of_STLmaxU STLK_of_STLKU STEKSumNdecay STEKSumRes1 STEKSumRes2NAL STEKSumRes2 STEKNonzero sz0_ht szB_flow_ht qvFormN_eq_re_UgenPairN eeShiftErrN norm_STeeM_shiftN_le s
U4 (4): ST_step5_assembly st5_t_lt_one st5_Bctl_le_one stStep5IV_holds
U5 (1): stStep5III_holds
U6 (21): STIngR5 STStep5Concl STStep5R STLemDecCalEConcl STfFar STCltFarConcl STCltFar STcltB STcltX STCltIsoConcl STCltIso STExpInv STStep5I STStep5II STStep5III STStep5IV InstIng5Concl inst_ing5 lemT_zCL inst_cltFar inst_cltIso
V1 (15): STLocalEntry_of_STLocalEntryU st6_mE_im_ge ST_step6R_mono STExp2U STExp2_of_STExp2U STStep6R STStep6I STStep6II STStep6III STStep6IV STExpAvgAt expAvg_eta_inv_le STExpAvgAt_of_LWAvgLaw stImproveExpAver_holds stStep6IV_holds
```
- **Pins.** The band pins (`STLK`, `STDecay`, ..., `STStep2Concl`, `STStep3R`) keep their definitions; the generic pins exist for the Step 1 family (`BA/FlowPins:332-460`, `Iff.rfl` bridges) and are new for the rest (`STScaleInvgL`, `GridMartPin` in the pilot).
- **When.** Supervisor 0944 O3 and DECISIONS §142 (4), §144 (3): no BA-T/U/V, L3, L4 before ST-4 (31 of 35 used), ST-5 (17 of 18) and ST-6 (design; ST-D6 not written) close and their files are published (state of the supervisor's table at 09:44 UTC); ST-3 is closed (47 of 47). Meanwhile the route-independent rows run behind their stage gates (P, K, G/E: DECISIONS §144 (2)).

## 8. Recommendation
1. **Route G for the chain, route I for the graph layer, one BA planning cap of 165 tickets** (central 141, range 136-163 with the K/G correction). If the supervisor does not accept route G, 200 stays the number (route I 185, route T 196, K/G upside).
2. Open the T/U/V stage gate (DECISIONS §144) with this pilot as the route basis and add a tripwire: the first conversion ticket takes a semantic-heavy block (for example `LoopGenN`, `ZeroModeCalc` or `KDecay`) and reports g and the share of lines that move into the band instance; if g > 0.5 there, or f_sem > 0.30, return to route I (break-even g = 0.70).
3. Order inside the stage: carriers by row along the dependency (Step 2 events and pins first: T8, T7, T1; then T2, T3; Steps 3-4 Q-family; Steps 5, 6; main induction), each ST-side ticket paired with its BA instance ticket so that the carrier is exercised at BA before the next row starts.
4. What would change the number: f_sem (0.10 to 0.30 moves the chain from 37.5 to 48.3 tickets); a lower-level carrier (loop data `(H, z)` instead of the observables) lowers `g` of upper blocks and enlarges the carrier (not compared); the BA-E2 and BA-U rows (EK-4, `Θ_BA`) are counted in group A and chain rows already; B_new from 3.8k to 10k adds 6 tickets.

## 9. Limits of the pilot
- Two blocks, chosen by the ticket, both plumbing-type; the semantic share is bounded by a tactic-name proxy only. The calibration (band-mention density) fits two points.
- The generic statements of the 7 lemmas behind `Step2Facts` and of the BA readings (events, pins, `flowOK_m`) are not proved at BA. At BA the base layer and the carrier constructor `baStep2` (with the open obligations as arguments) are compiled; none of the obligations is proved.
- The overhead and wiring terms (15 carriers, 245 and 100 lines, 167 wrappers × 15, 43 BA instances × 60) are assumptions A1-A2 from the probes' sizes, not measurements of the chain.
- Concrete-data `example`s exist for the Step 2 theorem and for targets 2, 3, 4a, 7a-7d of site 2. Targets 4b, 4c, 5a, 5b, 6a, 6b have the `recovers_*` theorems (and 4b, 4c are unchanged copies) but no concrete-data example in the probe: their merged instances (`QDriftA.lean:711-1337`) rest on private numeric helpers of `QDriftAInst`. A generic theorem at the band carrier has the hypotheses of the merged one (definitionally), and the merged instances exist, so it is not vacuous; re-running those instances over `recovers_*` is mechanical.
- `g` is a line measure; the unit 'ticket = 1000 lines' comes from new-code tickets (T2325: 891 lines per merged BA code ticket); conversion tickets read more than they write.

Re-run: `cd RBM3D-wt/T2326; lake build RBM3D.Probe.T2326PilotStep2 RBM3D.Probe.T2326PilotQ` (compiles both generic blocks, the `recovers_*` theorems and the `example`s); `g` by the `git diff --no-index --numstat` commands of B5 in the prove report.

## 10. Script output (S = session scratchpad `T2326/`; scripts and logs not committed)
```
$ python3 -I S/proxy.py   # calibration
site 1 block: 391 lines, 35 lines mention a band token or band def (0.090); measured g = 0.148; rho = g / density = 1.66
site 2 block: 584 lines, 83 lines mention a band token or band def (0.142); measured g = 0.303; rho = g / density = 2.13
both sites: edit lines 58+177 = 235 over band-mention lines 35+83 = 118: rho = 1.99; calibrated chain g = rho x density
chain files (non-instance part): 90226 lines, 9055 lines mention a band token or band def (0.100)
```
```
$ python3 -I S/instfrac.py | tail -1; python3 -I S/fsem.py; python3 -I S/sigcount2.py; python3 -I S/frozen.py; python3 -I S/consumers.py | tail -1
TOTAL 114998 lines in 97 files; instance sections: 24772 lines (21.5%), in 97 of 97 files; non-instance lines 90226
non-instance declaration lines 84460; theorem/lemma lines 79215; theorem lines whose proof unfolds/rewrites a primitive band object: 10575 (12.5% of all declaration lines, 13.3% of theorem lines)
band defs found (closure over definitions in RBM3D/Induction): 454
TOTAL public 2280 ; signature reads a band token or a band def: 1419 (62.2%); private 2911
public declarations in the chain files: 2279; signature reads a band object: 1419; of these referenced from files outside the chain (Test/, Probe/ excluded; 266 outside files): 167
by row: {'T1': 14, 'T4': 15, 'T5': 18, 'T8': 49, 'U1': 1, 'U2': 1, 'U3': 28, 'U4': 4, 'U5': 1, 'U6': 21, 'V1': 15}
endpoints with at least one consumer outside the chain files (excluding Test/): 8 of 43 ; distinct outside files: 11
```
```
$ python3 -I S/routeG2.py   # chain estimate and totals
S_file 114998, instance sections 24772 (21.5%), S_math 90226
g site 1 0.148, site 2 0.303, pair 0.241; density-calibrated g_cal = rho 1.99 x density 0.100 = 0.200
A1 carriers: 15 x 245 ST-side lines + 100 BA-side lines; A2 wrappers: 167 frozen signatures x 15 lines; BA instances: 43 endpoints x 60 lines; A3 semantic part at twin ratio 0.80; A4 B_new 3800 (T2325 U5+V2a+V2b+V3), high 10000; A5 tickets = lines/1000
scenario                       g     f_sem  B_new | plumbing  semantic  ST-overhead  BA-wiring  B_new | chain lines  tickets
low                              0.15  0.100   3800 |    12181      7218        6180       4080   3800 |       33459    33.5
central (calibrated g, proxy f)  0.20  0.125   3800 |    15790      9023        6180       4080   3800 |       38872    38.9
pair g, proxy f                  0.24  0.125   3800 |    18947      9023        6180       4080   3800 |       42030    42.0
f_sem 0.20                       0.20  0.200   3800 |    14436     14436        6180       4080   3800 |       42932    42.9
high (site-2 g, f 0.30, B 10k)   0.30  0.300  10000 |    18947     21654        6180       4080  10000 |       60862    60.9

route  used groupA chain        graph G-pub | total [range]      + K/G (22.5)
G        26     25  38.9 [33..61]    27     2 |  118.9 [113..141]   141.4 [136..163]
I        26     25    78                 27     7 |    163 [128..214]        185.5
T        26     25    92                 31     0 |    174 [141..223]        196.5
check: route I total 163 and route T total 174 reproduce T2325 §7: True True
break-even g (route G chain = route I chain 78) at f_sem 0.125: 0.70
break-even g (route G chain = route I chain 78) at f_sem 0.3: 0.67
```
```
$ python3 -I S/ifacecount.py   # section 3
T2326PilotStep2.lean: 909 lines
      60  header (docstring, options, opens)
      66  1 carrier Step2Data
      47  2 generic readings (JhatG, STScaleInvgL, GridMartPin)
     118  3 Step2Facts (statements of 7 other blocks)
     400  4 generic block (markers + text)
      93  5 band instance: bandStep2, bandStep2Facts, martPin
       8  5b recovery theorem
      18  6 compiled nonempty instance
      45  7 BA reading of the base layer
      54  8 baStep2: BA carrier, open obligations as arguments
T2326PilotQ.lean: 878 lines
      49  header (docstring, options, opens)
      28  1 kernel carrier QKerData
      61  2 carrier QDriftData
      35  3 generic readings (AvecN, aTrueQN, dGridQN)
     502  4 generic block (markers + text)
     111  5 band instances: bandKer, bandQ, private copies
      40  5b recovery theorems
      52  6 compiled nonempty instances
```
