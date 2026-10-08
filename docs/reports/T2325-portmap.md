# T2325 portmap: model-generic instantiation probe (BA-DP2) and the BA re-portmap

Written Thu Oct  8 07:15:25 UTC 2026, last edited Thu Oct  8 07:32:07 UTC 2026 (date -u). Base `main` 044707b (T2315 merged); branch `t/T2325` 05b9293. Evidence (commands and verbatim output): `docs/reports/T2325-prove.md` (b), cited "(b) B1..B6". Probe: `RBM3D/Probe/T2325BAGen.lean` (213 lines, branch only, never merged). `file:line` are at the base. "Lines" are file lines (`wc -l`); "decl-lines" is the unit of T2161's `decl_inv.py` (`T2161-portmap.md:195-222`). Ticket reading: supervisor 2026-10-08-0344 Q1 and O1, DECISIONS §135 (1), §138.

## 0. The answers

- **(i) Graph layer: not parametric in the edge kernel or the propagator in any way that shortens BA-L3/L4.** Parametric as merged, and compiled at BA objects in the probe: `expandG_sum` (any carrier), `lvl1_size_le`/`lvl1Cutoff` (read `Counters` only), `Lvl1Lt`/`lvl1Lt_wf` (on ℕ⁴), and the whole deterministic Anp family `AnpKey*` (7157 lines; `NGraph`, a symmetric `ξ`, `ψ`, `θ`; no model object). Everything else reads the term shapes of Owx/Oe1x/Oe2x and `LGraph.partition m`, the scalar `M = m I` (`lwClaimSize`, `LWGtoAG`; the hypothesis fails at the merged BA datum, probe theorem `scalarM_hyp_fails_at_baD`, and the BA `M` has nonzero neighbour entries, `BAK_adj_sum_ge` KKernel:352), or `GaussIBP sz`/`lwS`: BA twin. Twin source for BA-L2c, L3, L4: 38.8k lines (Anp excluded); at the measured twin ratio 0.8 that is 31k lines, against 3.1k in T2161 for L3 plus L4.
- **(ii) Chain: the merged ST theorems cannot be consumed through a model-generic interface; BA-T/U/V are ports.** Their premises and conclusions are `Lloop sz`/`STKloop sz` predicates over `STflowE z` (`STStep3R`, `Step34Pins.lean:250`). BA-C1a/S3 made the pin *shapes* generic (`FlowFM`, `…gL`, `BA/FlowPins.lean:328-460`; its comment, `:324`: "it does **not** make the merged band *proofs* generic") and ported the proofs. UN-51g (`UNOURowk`, `PinsK.lean:426`) saved a twin because the interface was pinned before the UN proofs were written; the ST proofs exist, 46% of their decl-lines are `private`, 51% mention a band object (B4, B5). Twin volume for Steps 2-6: 92k lines (route T), 78k (route I), against 20.9k for T1-V3 in the portmap.
- **Why the portmap is low (new facts).** T2161 sized T/U/V when `Induction/` had 57,206 decl-lines; it has 114,342 (ST-3: 49,672 against 18,712; step 6: 12,279 against none). 23 files (NQ*, QBudget*, QDrift*, QEnd*, QLevels*, QProxy, Qt*; 32,874 lines) are named by no portmap row. Measured twin ratios: 0.73 (S-chain) and 0.85 (graph L2) of the source lines.
- **Re-portmap (§5):** 46 open rows (+ BA-P3 in flight) cost **163 tickets on route I** [128..214] and **174 on route T** [141..223] in total (26 used); the T2161 rows scaled by the measured class factors, ignoring source growth, give 96; the supervisor's projection is 80-85.
- **Recommended cap: 175** (§7). The lever that could lower it is not measured: a G-in-place pilot (§4).

## 1. Calibration measured on the merged BA files (B2, B3)

| class | merged files | actual / portmap central lines | ratio |
|---|---|---|---|
| new-math deterministic (D3 Ward, D6, D7, G1, P2) | 5 | 2398 / 5550 | **0.43** |
| twin deterministic (D4 `CombesThomas`, P1 `Prop5Short`) | 2 | 1488 / 1700 | **0.88** |
| supervisor's seven (D3 D4 D6 D7 G1 P1 P2) | 7 | 3886 / 7250 | 0.54 (his 0.55 holds) |
| stochastic chain S1-S3 (`ConArg`, `Step1Trivial/Boot/Setup/Step1`, `Step1Fam`) | 6 | 6115 / 3200 | **1.91** (S1 1.80, S2 2.82, S3 1.03) |
| the same plus `FlowPins` and `CouplingWindow` (supervisor's 8.6k) | 8 | 8618 / 3200 | 2.69 |
| graph L1 `BAVocab`; L2 (3 of 4 cuts) `BAExpand`, `BAExpandW`, `BAExpandWOrd` | 1; 3 | 1424 / 873; 2975 / 2400 | 1.63; 1.24 (L2c open) |
| twin against its source file lines | S-chain 4879 / 6658; L2 2975 / 3490 | | **0.73; 0.85** |

Other measured facts: a merged BA code ticket averages 891 lines (19,595 / 22). 57% of the S-chain twin decl-lines are near-copies (token similarity ≥ 0.5) of ST-1 declarations; 18% (756 of 4113 lines) copy a **private, band-free** ST helper (the copy tax a publishing ticket removes); 873 copy public band-mentioning ones. BA references directly 99 public `Induction/` declarations (1235 lines) against 5434 own lines.

## 2. (i) Graph layer, per declaration family (what a BA row would use)

| # | LW family (file:line) | reads (model object) | verdict | BA row; cost (lines, route T -> I) |
|---|---|---|---|---|
| 1 | vocabulary: `LData` LWVocab:73, `LGraph` :104, `LGraph.val` :135, `Normal` :990, `val_eq_partition` :1339 (hyp `D.M x x = m`), `PGraph` :653 | waved values `D.S`/`D.Sp`, `D.G`, `D.M`; molecules by `adj` (waved, `=`-dotted) | **parametric by extension**: `BAGraph extends LGraph` BAVocab:55, `BALData extends LData` :39, `counters_ofLGraph` :533 | merged BA-L1 (1424 vs LWVocab 2559) |
| 2 | Stein bridge `owx_integral` LWStein:1239 | `GaussIBP sz`, `lwG`, `lwS = u·svarF`, `Sizes.seqP` | twin | merged `baLanlw_holds` BAExpand:744 (904 vs 1983) |
| 3 | Owx/Oe2x as graph operations: `owxT1` LWWeightExp:658, `owxT1_counters` :741, `owx_graph_E` :1316; `oe2xR2..R8` LWGGExp:485-529, `oe2xR*_counters` :848-970, `oe2x_graph_E` :1550 | coefficient `m`, `S`, `S⁺`, `M a a = m` | twin; BA operations are built on `owxExt/owxEmb/owxDE` (BAExpandW:114-148) | merged lanlw (0.85 of source); **open BA-L2c** (GGGamma, `lem_lweight` graph operation): 2158 -> 1856 |
| 4 | symmetric forms `lwSymmTwistG` LWSymm:171 ff. (2326 lines) | `SEdge`/`WEdge` conj/transpose, hyp `S⁺ᵀ = S⁺` | generalization G inside L3a: the BA twist also acts on `psi`, `mdot` | owned by no BA row |
| 5 | `Lvl1Lt` LWLvl1:3782, `lvl1Lt_wf` :3785, `lvl1Cutoff` :3981, `lvl1_size_le` :3989 | ℕ⁴; `Counters` only (`nV` already documents the BA slot, ScalingOrder.lean:54) | **parametric as is**; probe `baMu_wf`, `baGraph_size_le`, `inst_size_le` (d = 3, W = 4) | 0 |
| 6 | `Lvl1Good` :989, `Lvl1Mu` :3778, `lvl1_mu_lt` :3790 | `Counters`, `lvl1NLoops`, `lvl1NPairs` of the solid list | G of 31 lines (probe: `BALvl1Good` 7, `BAMu` 3, `ba_mu_lt` 21; bridge `BALvl1Good_ofLGraph` 20): same proof text, not worth a ticket | 0 |
| 7 | step claims `lvl1_good_*` :1215-3075 (≈ 1860 lines), `LocStep` :3260, `lvl1_step_good` :3290, `lvl1_exists_step` :3655 | term shapes `lwSymmOwxT*`, `lwSymmOe1x*`, `lwSymmOe2xR*`; `LGraph.partition m` | **not parametric**: twin | L3a (rows 4, 7, 8): 5334 -> 4588 |
| 8 | `lvl1_step_identity` :3590, `Lvl1Ident` :3828, `lvl1_lemma` :3907 | `GaussIBP sz`, `lwS`, `m ≠ 0`, `M a a = m`, `M a b = 0` | twin (BA: `lanlw_val` BAExpandW:908 and the L2c operations) | in L3a |
| 9 | localregular: `PathInv` LocalRegular:1856, `pathInv_locStep` :1861, `lw_localregular` LocalRegular6d:1107, cost of a merge `scost` LocalRegular6a:157 (11,165 lines) | the 17 `LocStep` output shapes, `molSolid`, `fxyPowGraph` | not parametric, except the walk-family lemmas `localReg_Fam.map/thr/of_add_diag` (LocalRegular:230-495) and `localReg2_Fam.*` (LocalRegular2:147-560): multisets of `Sym2 N`, ≈ 670 lines (600 are taken out below) | L3b: 8452 -> 7269 |
| 10 | `lwClaimSize` LWSizeClaim:1118, `LWGtoAG` AuxGraph:979, `LGraph.auxVal` | hyp `D.M x y = if x = y then m else 0`; `scalingSize` with `nV` | twin or G (atoms, `M`-dotted bounds, `ζ`); the hypothesis fails at BA data (`BAK_adj_sum_ge` KKernel:352, probe) | L3c with row 11: 3865 -> 3324 |
| 11 | claim:xi `lwXiVar`, `lwXiClaim_holds` (AuxGraph2) | `Lloop sz`, `STgexRHS` | twin (`(eq:Gbyxi2_BA)`) | in L3c |
| 12 | Anp deterministic: `AnpDetGhAt` AnpKey:41, `anpDetGh_zero` :339, `anpDetGh_of_step` :649, `anpDetGh_holds` AnpKey6:862 (7157 lines) | `NGraph p q`, symmetric `ξ ≥ 0`, `ξ ≤ ψ(\|α-β\|)`, `Σ ξ² ≤ θ`, `zdistInf`; no model object | **parametric as is**; the BA auxiliary graph must be an `NGraph` with `ζ` as `ξ` | 0 (saves ≈ 5.7k) |
| 13 | lift `lwAnpKeyGh_of_det` AnpKey:689 (reads `LWXi`: `ξ` built from `Lloop sz`); near and far bounds `AnpDetNearAt` LWMomExp:900, `lwMomExp_near` :1023, `LWMomExpFar` (1604 lines in all) | `NGraph` and the band profile `sfT d L W g t`, `PsiT`, `ellT` (the paper's `𝖳_t`, built from the band `Θ`) | twin of the profile-specific statements (BA: `𝖳_t` from `Θ_BA`, rows BA-E); a G over the profile has the size of the twin | L3d: 2083 -> 1904 (adaptation 800) |
| 14 | engine `expandG` LWExpTerm5:189, `ExpandGSum` :199, `expandG_sum` :234 | any carrier `X` | **parametric as is**; probe `baEngine_sum` at `BAPGraph (Fin 2)` | 0 (≈ 60 lines) |
| 15 | identity half `RCand` :124, `RCand.kids` :147, `LWG5Identity` :76, `lwExpandIdentity_holds` :594 | `oe2xR2..R8`, `sz.seqP`, `LWG5Data`, `mE` | twin (GGGamma families) | L4 |
| 16 | certificate `MNode` LWExpCert:46, `cPartition` :100, `fams` :138, `goodB` :197, `cert_all` LWExpCertS1:297 (use `cert_all'`, T2319); Sim `partitionSim` LWExpSim:1093, `childrenSim` :1143; Sound (T2318, unmerged) | the computable model of `LGraph.partition` and `oe2xR*`; BA partition splits every non-circled solid edge (`baSplitSolid` BAVocab:163) | twin | L4 (rows 15, 16): 9361 -> 8050 |
| 17 | `LWPsi` (813): `LWWindow`, `LWClass`, `LWPsiRel`, `LWPsiAll` (:47-66) | real sequences `Ψ : ℕ → ℝ`, `Φ : ℕ → ℝ → ℝ` only | parametric as is | 0 |

Sources twinned (excluding Anp, vocabulary, Stein, merged lanlw): LWGGExp 1748 + 950 (Owx graph operation), LWSymm 2326, LWLvl1 4462, LocalRegular* 11,165, AuxGraph 3347, LWSizeClaim 1484, LWMomExp* 1604, LW-14 chain 11,761. Route T 31.3k lines, route I 27.0k (publishing removes the Graph copy tax, 21% private).

## 3. (ii) Chain, per BA row: what the ST theorem reads, verdict, cost

Source = ST files the row ports (file lines); D = lines of declarations that mention a band object (T2161 token list plus `Ugen`, `UN`, `uKer`, `AvecN`, `pathH`, `STLKM`, `STLM`); route T = 0.80 × source, route I = 1.45 × D (re-state the band-mentioning declarations, reference the rest after publishing; 1.45 = (1524 near-copy + 1747 new) / 2253 measured on ST-1). All rows are **twin** unless marked.

| row (portmap c) | ST theorems ported (file:line) | read at the band model | source / D | T -> I lines |
|---|---|---|---|---|
| T1 (1500) | `ST_selfImprove_section` Step2Iterate:284 (399 lines), `ST_iterate` :725, `ST_step2_of_pins` :1393; `OptL2a/b` | `Lloop sz`, `STKloop sz` (`KLK`, `mE`, `SB`), `STflowE z = lemE (z n)`, `lemT (z n)`; premises `STLWT`, `STEMn2Exp`, `STNewKLKAt`, `STGridMartAt` (Step2Defs:363-513) | 3947 / 2565 | 3158 -> 3719; BA-new: deterministic `J` (`eq:MG_conclusion3_BA`) |
| T2 (1700) | `stEMn2Poly_holds` EMn2Poly:838, `stEMn2Exp_holds` EMn2Exp2:1090 | `STEEk`, `STJhat` (from `Lloop`, `STKloop`), `STprof`, `etaT (STflowE z n) (t n)`, `STInitialGT2`, `STLWassmExp` (Step2Defs:456-470); BA: `(eq_resolventunderpoly)`, `(Mbound_AO)` | 4445 / 1332 | 3556 -> 1931 (70% generic after publishing) |
| T3 (1200) | `stNewKLK_holds` NewKLK:1198, `stNewKLKAt_holds` :1321 | `STNewKLKAt` Step2Defs:363: deterministic for any Hermitian `H`; `STthetaOp` (band `Θ`), `STLKM`, `STGMM` (`G - M`, scalar `M`), `STprof`; BA adds `(Mbound_AO)` | 1552 / 935 | 1242 -> 1356 |
| T4 (1400) | `Ugen` GridDuhamelN:65, `AvecN` :272, `assembledN` GridAssemblyN:1605, `StoppedAzumaN` :531, `AzumaProxyN*` | kernel `UN d L g (fun i => mSigma E (σ i))` (scalar `m(σ)`), `gvarF d L W (sz.lam n)`, `STKloop`, `pathH sz` | 8530 / 4338 | 6824 -> 6290 |
| T5 (1400) | `StepDecompN`, `LoopGenN`, `HierAlgebra`, `HierarchyN`, `LoopC2N`, `QVN`, `GridDriftN` | `loopGenN` LoopGenN:548 is stated at an arbitrary Hermitian `M` but fixes `zt E u` and `mSigma E` and the kernel `SB d L g` in `W^d Σ 𝓛 S^{(B)} 𝓛`; the rest reads `Lloop`, `STLM`, `CoordF/gvarF` | 6171 / 2983 | 4937 -> 4325 |
| T6 (1400) | `stContractPt_holds` ContractPt:463, `stContract_holds` Contract:1046 | ContractPt has **0** band tokens: matrix `H`, `Im z = η`, block projections; 73% private | 1781 / 117 | 1425 -> 170: **instantiate after publishing the matrix core** |
| T7 (1200) | `ST_good_prob` Step2Events:853, `stDecayLoopAt_holds` DecayLoopA:938, `stDecayLoopU_of_step2` DecayLoopB:1637 | `Lloop`, `Bctl`, `ellT (sz.lam)` | 5756 / 2288 | 4605 -> 3318 |
| T8 (1100) | `STStep2` Step2Defs:599, `STStep2Concl` Step34Pins:221, `stStep2LocalPT_of_L2decay` LocalAvg2:321 | band pins; the BA pin `STStep2ConclgL` is designed in T2205 P.2, not merged | 2128 / 1294 | 1702 -> 1876 |
| U1 (1200) | `ZeroModeCalc`, `stIterations'_holds` IterationsB:570, `stNewPQ_holds` NewPQ:584, `stMollifierEx_holds` QopAlgebra:573, `stQopNorm_holds` QopNorm:261, `QGridA/B` | zero mode of `SB`/`Θ` (`BAK` is doubly stochastic, KKernel) | 8886 / 2871 | 7109 -> 4163 |
| U2 (1200) | `stSEforLn_holds` SEforLn2:1287, `stB45Pin_holds` B45:2943, `stKcalDecay_holds` KDecay:798 | `KLK` decay, `Theta` | 6705 / 3175 | 5364 -> 4604 |
| U3 (1000) | `stStep3RegIII_holds` Step3:377, `stStep3RegI_holds` :408, `stStep3II_holds` :432, `stStep4I_holds` Step4:189; pins `STStep3R` Step34Pins:250; **plus 23 files named by no row** (32,874 lines) | premises `STKbound sz (STflowE z)`, `STKward`, `STLK`, `STStep2Concl`; `Lloop`, `Ugen` | 35,050 / 17,469 | 28,040 -> 25,330 |
| U4 (1200) | `ST_step5_caseI_of_pins` Step5Kit:292, `ST_step5_caseII_of_pins` Step5Cases:542, `stNewKLKL_holds` NewKLKL:836, `stTailtoTail_holds` TailtoTail:582, `stWardII_holds` WardII:269, `stLemDecCalE_holds` LemDecCalEPrec:1550 | `Lloop`, `Theta` tails; `Evolution/Clt*` stays generic | 10,304 / 4663 | 8243 -> 6761 |
| U5 (1300) | band `stStep5III_holds` PfStep5:2473 (`lem:pf_step5`, 4658 lines) is **not** the BA argument | BA case (iii) is `[RBSO1D S7.3]` with `lem_GbEXP_BA` (`3_5:2284`, `7_8:2101`), not in the paper | new mathematics | 1300 (portmap kept; paper gap) |
| U6 (900) | `STStep5R` Step5Pins:101 | band pins | 1044 / 243 | 835 -> 352 |
| V1 (1000) | `ST_step6_case{I..IV}_of_pins` Step6Kit:737-947, `stStep6IV_holds` ExpIntEasy:626, `ST_step6I_of_LW_Int` ExpIntI:660 | `Lloop` expectations; `LWtermEXP` (graph part BA-L4) | 13,944 / 7090 | 11,155 -> 10,280 |
| V2a, V2b (1100, 700) | `ST_mainIndR_of_steps` MainIndRegimes:165, `ST_mainInd_of_regimes` :616; `STMainIndG` FlowPins:565 is generic in the law | compiled in the T2205 probe (6.5-6.7) | T2205 sizes | 1100, 700 |
| V3 (700) | `ML:GLoop` ... at `t0` | portmap | - | 700 |
| **sum** | | | 115.8k / 53.8k | **92.0k -> 78.3k** (portmap 20.9k) |

Where the band model is read, object by object. **Scalar `m` against matrix `M`:** `STGM` Defs:77 is `Gt … - (if x = y then mE E else 0)` (`M = m(E) I`), the 1-loop value `Lloop … - mE (E n)` (Defs:229), `STmsig` and `mSigma E σ` in `STthetaOp` (Step2Defs:119) and `loopGenN`; BA has `M_aa = m` and `M_ab ≠ 0`. **`S^{(B)}` and `Θ` against `K = M^{(+,-)}` and `Θ_BA`:** `STthetaOp` is `Σ_b m(σ₀)m(σ₁) (SB d L lam · Theta d L lam (u m m'))(a_i, b)` (Step2Defs:119-126), `STKloop` is `KLK d L lam W E τ …` (Defs:64), `Ugen` GridDuhamelN:65; the BA kernel is `BAK` (KKernel). **`Sizes.seqP`:** the law of every `Prec` conclusion (`STLK`, Defs:104); BA uses `seqP (sz.withLam 0)` (`BAStep1`, Step1Fam:361). **`GaussIBP`:** in no `Induction/` file (`grep -l GaussIBP Induction/*.lean` is empty); it enters through `Graph/LWStein` and `Green/`. **The flow `STflowE`:** `lemE (z n)` (Defs:283); BA has `BAflowEs`, `BAflowT0` (FlowPins:540, :537).

Why no row collapses by instantiation: the step theorems quantify `sz : Sizes d` and `z` and conclude predicates built from `Lloop sz`, `STKloop sz`, `STflowE z` (Step34Pins:250-277). BA's `FlowFM` carrier (`BA/FlowPins.lean:332`: four objects `𝓛, 𝒦, G, M` plus `S`, `η`, `m`) states the same shapes; a theorem about the band carrier is not a theorem about `baFM`. Matrix-level deterministic declarations (an explicit Hermitian matrix in the signature, no stochastic marker) are 10,356 of the 103,910 decl-lines of Steps 2-6 (10%, B4; e.g. `loopGenN` fixes `zt E u` and `mSigma E`, the semicircle `m` with `|m| = 1`, while the BA `m` has `|m| < 1` for `g > 0` by the Ward row sum and `BAK_adj_sum_ge`): a cheap generalization reaches at most that tenth. The ST proofs reach the model through 146-210 distinct declarations of the model-base layer per step (B4), so a carrier structure with those facts as fields exists in principle; writing it is a rewrite of the same size as the port (frozen signatures, CLAUDE.md §5.3). The measured saving is therefore only the copy tax (18%) and the generic public declarations the S-chain already referenced.

## 4. Generalization tickets G

| G | gate | content | size | verdict |
|---|---|---|---|---|
| G-pub-ST (5 tickets: Step 2, Steps 3-4 twice, Step 5, Step 6) | ST | remove `private` (file-stem prefix, §3 E) from the band-free helpers a BA row references; no statement change; sole writable = the named ST files (precedent: DECISIONS §129 (6) for `LWExpSim`) | edit only; private band-free decl-lines in `Induction/`: 29,750 | **recommended**, saves the 18% copy tax |
| G-pub-LW (2) | LW | same for `LWLvl1`, `LWSymm`, `LocalRegular*`, `AuxGraph*`, `LWExp*` | edit only | recommended |
| G1 `Lvl1Good` family generic | LW | `Lvl1Good`, `Lvl1Mu`, `lvl1_mu_lt` over `Counters` plus solid lists | 31 lines (probe) | not worth a ticket |
| G-pilot (design probe, not a BA row) | ST | restate `ST_selfImprove_section` (399 lines) over `FlowFM` with the carrier facts as hypotheses; count edited lines | 1 probe | **needed before any cap below route I**: matrix-level declarations are only 10% of the chain (§3); the stochastic 90% decide. The 53.8k band-mentioning lines of the Steps 2-6 files (§3, D) are what a carrier refactor edits; if the edited fraction g is 0.25 the re-statement is ≈ 13k lines against 78k, before the BA-specific content; g is not measured |

## 5. The re-portmap (46 open rows; BA-P3 = T2324 is in flight; ticket numbers 1 per row unless split)

Group A, deterministic and twin-type rows. Rule: new-math rows 0.35/0.55/0.90 of the portmap lo/central/hi (merged analogues D3 .45, D6 .29, D7 .37, G1 .44, P2 .75); twin-type rows 0.70/1.00/1.30 (D4 .67, P1 1.16, L1 1.63, L2 1.24). Tickets = ceil(lines / 1500) per row (B6).

| row | type | portmap lo/c/hi | revised lo/c/hi | tk | | row | type | portmap lo/c/hi | revised lo/c/hi | tk |
|---|---|---|---|---|---|---|---|---|---|---|
| P4 | twin | 1000/1400/2000 | 700/1400/2600 | 1 | | G2 | twin | 1000/1400/2000 | 700/1400/2600 | 1 |
| P5 | twin | 700/1000/1400 | 490/1000/1820 | 1 | | G3 | twin | 1000/1400/2000 | 700/1400/2600 | 1 |
| P6 | twin | 1000/1400/2000 | 700/1400/2600 | 1 | | G4 | new | 1000/1400/2000 | 350/770/1800 | 1 |
| P7 | twin | 500/700/1000 | 350/700/1300 | 1 (c) | | G5 | twin | 1000/1400/2000 | 700/1400/2600 | 1 |
| P8 | twin | 600/800/1100 | 420/800/1430 | 0 (c) | | G6 | twin | 600/800/1100 | 420/800/1430 | 1 |
| K1 | new | 700/900/1200 | 245/495/1080 | 1 | | M1 | twin | 700/1000/1500 | 490/1000/1950 | 1 |
| K2 | twin | 1200/1600/2200 | 840/1600/2860 | 2 | | M2 | twin | 700/1000/1500 | 490/1000/1950 | 1 |
| K3 | new | 900/1200/1700 | 315/660/1530 | 1 | | M3 | twin | 900/1300/1900 | 630/1300/2470 | 1 |
| K4 | twin | 1200/1600/2200 | 840/1600/2860 | 2 | | N1 | new | 700/1200/2000 | 245/660/1800 | 0 (d) |
| K5 | twin | 600/800/1100 | 420/800/1430 | 1 | | N2 | new | 500/800/1500 | 175/440/1350 | 1 |
| E1 | new | 700/1000/1400 | 245/550/1260 | 1 (b) | | C3 | twin | 788/1102/1575 | 552/1102/2048 | 1 |
| E2 | twin | 1000/1500/2100 | 700/1500/2730 | 1 | | C4 | twin | 620/868/1240 | 434/868/1612 | 1 |
| E3 | twin | 500/700/1000 | 350/700/1300 | 0 (b) | | C5 | twin | 870/1217/1739 | 609/1217/2261 | 1 |

26 rows, 28 tickets before the merges, 25 after (b), (c), (d) [lo 23, hi 42]. Portmap central 29,487 lines, revised 26,562. Two rows exceed 1500 at the twin ratio (K2, K4: the KL-gate tree-representation files total 4.2k lines, the `Kbound` induction files 6.2k); K and G rows twin KL (19k) and Green (28k) sources, so their upside is the largest in group A.

Chain and graph rows (lines; tickets = lines / 1000, per-row sums 102 (T) and 88 (I) with ceilings, 891 lines per merged ticket would give 103 and 88):

| row | portmap c | route T | route I | | row | portmap c | route T | route I |
|---|---|---|---|---|---|---|---|---|
| T1 | 1500 | 3158 | 3719 | | U6 | 900 | 835 | 352 |
| T2 | 1700 | 3556 | 1931 | | V1 | 1000 | 11,155 | 10,280 |
| T3 | 1200 | 1242 | 1356 | | V2a | 1100 | 1100 | 1100 |
| T4 | 1400 | 6824 | 6290 | | V2b | 700 | 700 | 700 |
| T5 | 1400 | 4937 | 4325 | | V3 | 700 | 700 | 700 |
| T6 | 1400 | 1425 | 170 | | L2c | (in L2) | 2158 | 1856 |
| T7 | 1200 | 4605 | 3318 | | L3a | 1590 (L3) | 5334 | 4588 |
| T8 | 1100 | 1702 | 1876 | | L3b | | 8452 | 7269 |
| U1 | 1200 | 7109 | 4163 | | L3c | | 3865 | 3324 |
| U2 | 1200 | 5364 | 4604 | | L3d | | 2083 | 1904 |
| U3 | 1000 | 28,040 | 25,330 | | L4 | 1500 | 9361 | 8050 |
| U4 | 1200 | 8243 | 6761 | | | | | |
| U5 | 1300 | 1300 | 1300 | | **chain** | 20,900 | **91,994** | **78,276** |

## 6. Merge and drop candidates of supervisor Q1, checked against the merged code

- **(a) G2-G6 -> 4 rows: not supported.** `BA/GreenSchur.lean` (G1, 615 lines) states "no probability, no a.s. block support, no large-deviation estimate"; its 0.44 says nothing about G2 (large deviations for BA minors, a twin of `Green/LDE*` 4.6k + `EntryCore` 1.35k) or G3-G5 (`GbEXP` 1124, `LocalLaw` 1255, `Fluc*` 5.3k).
- **(b) E1+E3 -> 1 row: supported.** Twin base `XiPins` 485 + `Pins` 418 + `Prec` 657 = 1560 lines; E1 at 0.55 and E3 at 1.0 give 1250 lines (one ticket up to a common ratio of 0.88 on the portmap centrals 1000 + 700).
- **(c) P7+P8 -> 1 row: supported.** 700 + 800 at ratio 1.0 is 1500 (1275 at 0.85); sources `Prop5Hold` zero-mode part, `Prop6Hold` 560, `Props4` 281.
- **(d) N1 -> dropped or merged into C3/M1: supported.** `BA/MReg.lean:39` states "Not here: the coupling shift (BA-N1)"; `BAmWindow_holds` (CouplingWindow:688) already gives `‖m(E,g') - m(E,g)‖ ≤ C (g - g')` on the bulk window (real `E`), and `BAm_sub_le_of_im` (MReg:84) gives the `z` dependence; what is left is the dilation `g e^{t/2}`, about 300 lines.
- **(e) K5 dropped: not supported.** `BA/Ward.lean` (resolvent Ward row sums, translation invariance) and `BA/KKernel.lean` (double stochasticity of `BAK`) are not the K-loop Ward identities `lem_WI_K`, `lem_wardineq_K`, which need the BA K-loops of K1/K2; the band sources are `KLWard` 1224 + `KLWardIneq` 1083 (twin ≈ 1.8k: K5 may need 2 tickets).

## 7. Totals and the recommended cap (tickets; B6)

| component | route I (instantiate where possible) | route T (twin everything) |
|---|---|---|
| used: 22 merged code tickets + T2161, T2173, T2205 + T2324 in flight | 26 | 26 |
| group A, after merges (b), (c), (d) | 25 [23..42] | 25 |
| chain T1-V3 (lines / 1000) | 78 [54..103] | 92 [69..116] |
| graph L2c, L3, L4 | 27 [20..34] | 31 [23..39] |
| G tickets (publishing, ST 5 + LW 2) | 7 [5..9] | 0 |
| **total** | **163 [128..214]** | **174 [141..223]** |

Not in the totals: the P3b cut (+1 if T2324 triggers it, DECISIONS §136 (1)), a second Anp-side adaptation if the BA auxiliary graph is not an `NGraph`, and the K/G upside of §8.

Cross-checks: (1) 109 merge commits touch `Induction/`, 95 of them for Steps 2-6 (S3 42, ST2 24, S6 15, S5 14; S1 9); the BA S-chain used 9 tickets for ST-1's 9 (6 without C1a, C1b, D8), so 0.67-1.0 × 95 = 64-95 for the chain. (2) Top-down, the T2161 rows times the measured factors (T/U/V 20.9k × 1.91; graph × 1.3), ignoring the growth of `Induction/`: 96. (3) Supervisor 0344 Q1: 80-85 (76-95) at ×1.3-1.5.

**Recommended BA cap: 175** (route T central; route I central 163 plus 7%). It holds for both routes at their centrals, not at their upper ends (214, 223). A single number below 163 is not supported by anything measured here. If Jun prefers a smaller commitment, the honest alternative is the pilot of §4 first (one design ticket, no BA row), then one number.

## 8. Risks, and what would change the plan

- **Chain volume (the whole result).** It rests on two measured ratios (0.73 and 0.85) and on the claim that Steps 2-6 need an analogue of every file; the endpoint cones reach 59% of `Induction/` (67,894 lines; Step 3 endpoints alone 43,295, 62% private) and the rest is the proofs of pins the endpoints take as hypotheses (B5). Learning effects could lower the "new" fraction (43% of S-chain twin lines) from step to step: route I low 54.
- **K and G rows** twin the KL gate (`Loop/`, 19.0k lines) and the Green gate (28.2k); at ratio 0.8 that is 37.7k lines against 12.5k portmap central for K1-K5 and G2-G6, about 20-25 more tickets in group A (not in the central, which follows the ticket's rule and the merged analogues).
- **Paper gaps that become Lean work:** `B_graphical_lemmas.tex:416` asserts that `lem:localregular` holds for BA "including all properties (1)--(6)", `:409` says the BA proof is only sketched and `:497` that the Anp argument "carries over verbatim"; property (6) is proved in Lean by a local cost-of-merge argument because the paper's monotone step fails (LocalRegular6a docstring, DECISIONS §47), with `n_V` replaced by `n_A` for BA this needs a check. BA-U5 (`3_5:2284`, `7_8:2101`) cites `[RBSO1D S7.3]`.
- **Publishing tickets** edit merged files under a sole-writable list (`#assert_rbm_axioms` unaffected; name clashes avoided by the file-stem prefix); BA-L3/L4 and BA-T/U/V must not start before the publishing ticket of their source files, or they pay the copy tax.

Paper-delta candidates (T2325a-c, numbers assigned by the dispatcher): **T2325a** the BA proof of `lem:LW_moment` (`B:409-497`) is a sketch whose Lean cost is the twin of LW-08, LW-10, LW-11, LW-13 (31k lines at ratio 0.8), not 7 kchar × 151 lines/kchar; **T2325b** `LWGtoAG` and `lwClaimSize` carry `M = m I`; BA needs `Ǧ = G - M` bounds with a non-scalar `M` (probe); **T2325c** BA Step 5 large `t` is not in the paper (cited from `[RBSO1D]`).
