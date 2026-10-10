# T2378 (BA-DGE) stage-G and stage-E design: route, findings, row table

Prover `claude-sonnet-5-5` (prover-max, design only, CONTROL H173). Branch `t/T2378` (base `1f710ee`), probe `RBM3D/Probe/T2378Pins.lean` (367 lines, limit 400), commits `67dfde8`, `f2c609a`. Last edit: Sat Oct 10 11:08:03 UTC 2026.
Citations: `path:N` is relative to `RBM3D/` at the base (merged files of `1f710ee`); `1_2:N`, `3_5:N`, `A:N`, `7_8:N` are lines of `paper/tex/1_2_Intro_model_result.tex`, `3_5_Loop_Hierarchy.tex`, `A_deterministic_estimates.tex`, `7_8_light_weight.tex`; `probe N` is line N of the probe; `(a) row k` is row k of the exponent table of `docs/reports/T2378-prove.md`; `Bk` is block k of its (b). Counts are `wc -l`. The scripts are in the scratchpad subdirectory `T2378/` (not in the repository); their verbatim outputs are in (b).

## 0. The answer

| item | answer | where |
|---|---|---|
| GE1 | 28 files (22 `Green/` 28199 lines, 6 `Evolution/` 4164), 32363 lines; 8792 are docstrings and instances; of the other 23571: **R 10839 (reuse), G 4467 (generalise in place), T 8013 (twin), X 252**. Outside the list: `Kernel/Evolution`, `Kernel/SumDecay` (T 704, R 536, G 75). Route: R imported; G in place for groups A, C, D, E, F, twin for group B; T twin | §1 |
| GE2 | target `BAGbEXP` (probe 40) = the three owed pins unchanged; the data facts the rows use follow from `BAFlow` alone (`ba_G_data`, probe 53); instance `inst_BAGbEXP` (probe 99). **Gap F2:** the premise `g ≤ W^{-ε}` of `[RBSO1D] L6.1` is not derivable (`BAFlow_not_small`, probe 183). **Finding F1:** the pin `BAGijGEX` is not the paper's `(GijGEX_BA)` | §2 |
| GE3 | G: **no complete argument** (L6.1 text absent, "verbatim" at `7_8:1948`); R/G/T split by file in §1; rows G3a, G3b, G4, G5a, G5c need a design-gate 1a. E: **complete paper argument** (`A:114-228`), BA inputs merged | §3 |
| GE4 | no G/E row needs a stage-K, stage-L or T/U/V output; all 12 rows can run in parallel with stage K now; the old E2 <- K3 is a consumer dependency | §4 |
| GE5 | probe: 31 declarations on the three standard axioms; **12 rows, central 13.5k [9.5k .. 21.1k]**; exponent table; instances probe 99, 301 | §5 |
| GE6 | **12 rows (G 9, E 3)**: at, not above, the limit; lines classed T: central 9.5k (10.6k with the twinned group B): at the 10k line. Per-stage flag 1.5 x 12 = **18** | §6 |

Findings: **F1** `BAGijGEX`/`BAGiiGEX` have the band shape, not the paper's (§2). **F2** the range gap (§2). **F3** the band layer is written for `M = m I`, `‖m‖ = 1`; at BA data (`g = 1/64, 1, 10`) `|m₀| = 0.9995, 0.673, 0.561` and the largest `|M_{xy}|`, `x ≠ y`, is `0.013, 0.30, 0.55` (B8); inside one block `M_{xy} = 0` (probe 126). **F4** `Ξ = ((t-s)/t)(Θ - 1)` for BA: row E1 needs no `Mbound_AO` (probe 264).
Verdict: **design delivered, GE1-GE6 answered**; the paper does not prove the BA stage-G target, so rows G3a-G5c start from our argument (§7).

## 1. GE1: the band files

Classes: **R** no band object in the statements (the random part of BA is the band model of `sz.withLam 0`, `Gauss/BlockAnderson.lean:83`, so statements about `seqP`, `seqHflow`, coordinates, abstract matrices are R at `sz.withLam 0`); **G** the statement reads the flow resolvent `green (seqHflow sz n u ω) z` with `z`, `m` as parameters (`greenDiagCentered`, `Green/FlucVanish.lean:813`) and the proof uses only Hermitian, `Im z ≠ 0` and independent Gaussian rows: restate over `D + seqHflow` (`BAGt_eq_green`, probe 44); **T** the statement or its proof is about `M = mE E · I`, `‖m‖ = 1` (`GoodEvent … (mE E)`, `Stable S (t m²)`, `Kstab3`, scalar `μ` in `UN`/`Theta`); **X** not needed (the extreme-input checks of RBM2D, `Green/Pins.lean:1157-1408`); H header, I instances. A class is a reading of the statements (one class off at a boundary), not compiled. Table (script `ge1rows.py table`, B6):
```
file                     lines   H+I     R     G     T     X
Green/EntryCore           1352   304   418     0   630     0     Green/RowIndep     1595  221 1085  289    0    0
Green/EntryDom            1628   399   305    53   871     0     Green/FlucVanish   1613  342 1115  156    0    0
Green/LDE                 1404   319   435   650     0     0     Green/FlucIter     1085  345  714   26    0    0
Green/LDEQuad             1049   210   839     0     0     0     Green/FlucIterGain 1288  403  736  149    0    0
Green/LDEQuadMom           977   258   719     0     0     0     Green/MinorGoodLe  1326  385    0  749  192    0
Green/LDEQuadT            1200   245   955     0     0     0     Green/MinorDiff    1371  551  325   65  430    0
Green/MinorDiffCond       1418   593   254     0   571     0     Green/CondDom      1458  719  529    0  210    0
Green/IBP                 1687   379     0  1024   284     0     Green/IBPPoly      1157  127  348  682    0    0
Green/IBPRem               815   348     0     0   467     0     Green/LocalLaw     1255  382    0    0  873    0
Green/FlucThreshold       1295   440   721     0   134     0     Green/GbEXP        1124  387  108  144  485    0
Green/Pins                1643   280    52   317   742   252     Green/Stability     459  106    0    0  353    0
Evolution/XiPins           485    86     0     0   399     0     Evolution/Nonzero   227   67    0    0  160    0
Evolution/SumDecay         631   145   217    68   201     0     Evolution/Pins      418  236   75    5  102    0
Evolution/SumDecayZero    1746   263   802     0   681     0     Evolution/Prec      657  252   87   90  228    0
subtotal Green/          28199  7743  9658  4304  6242   252     subtotal Evolution/ 4164 1049 1181  163 1771    0
TOTAL                    32363  8792 10839  4467  8013   252     (non-H/I lines 23571: R 46%, G 19%, T 34%)
```
Segments (`a-b:C`, `ge1rows.py segments`, B6; `G/` = `Green/`, `E/` = `Evolution/`, `K/` = `Kernel/`, outside the ticket's list; `E/Prec` is E3's source). Boundaries are section headers or, inside a section, the first declaration of another kind:
```
G/EntryCore     1-28:H 29-405:R 406-513:T 514-554:R 555-1076:T 1077-1352:I
G/EntryDom      1-49:H 50-205:R 206-258:G 259-474:T 475-535:R 536-589:T 590-677:R 678-1278:T 1279-1628:I
G/LDE           1-73:H 74-101:R 102-398:G 399-463:R 464-602:G 603-717:R 718-931:G 932-1158:R 1159-1404:I
G/LDEQuad       1-61:H 62-900:R 901-1049:I
G/LDEQuadMom    1-65:H 66-784:R 785-977:I
G/LDEQuadT      1-69:H 70-1024:R 1025-1200:I
G/RowIndep      1-80:H 81-878:R 879-964:G 965-1251:R 1252-1454:G 1455-1595:I
G/FlucVanish    1-72:H 73-304:R 305-355:G 356-809:R 810-914:G 915-1343:R 1344-1613:I
G/FlucIter      1-59:H 60-729:R 730-755:G 756-799:R 800-1085:I
G/FlucIterGain  1-62:H 63-749:R 750-898:G 899-947:R 948-1288:I
G/MinorGoodLe   1-85:H 86-834:G 835-1026:T 1027-1326:I
G/MinorDiff     1-91:H 92-416:R 417-846:T 847-911:G 912-1371:I
G/MinorDiffCond 1-98:H 99-352:R 353-923:T 924-1418:I
G/CondDom       1-65:H 66-184:R 185-284:T 285-694:R 695-804:T 805-1458:I
G/IBP           1-72:H 73-111:T 112-1135:G 1136-1380:T 1381-1687:I
G/IBPPoly       1-48:H 49-396:R 397-1078:G 1079-1157:I
G/IBPRem        1-73:H 74-540:T 541-815:I
G/LocalLaw      1-79:H 80-952:T 953-1255:I
G/FlucThreshold 1-67:H 68-788:R 789-922:T 923-1295:I
G/GbEXP         1-83:H 84-191:R 192-365:T 366-509:G 510-820:T 821-1124:I
G/Pins          1-45:H 46-343:T 344-660:G 661-712:R 713-1156:T 1157-1408:X 1409-1643:I
G/Stability     1-41:H 42-394:T 395-459:I
E/XiPins        1-28:H 29-427:T 428-485:I
E/SumDecay      1-33:H 34-250:R 251-318:G 319-519:T 520-631:I
E/SumDecayZero  1-38:H 39-602:R 603-1160:T 1161-1398:R 1399-1521:T 1522-1746:I
E/Nonzero       1-26:H 27-186:T 187-227:I
E/Pins          1-39:H 40-141:T 142-170:R 171-175:G 176-221:R 222-418:I
E/Prec          1-35:H 36-122:R 123-212:G 213-440:T 441-657:I
K/Evolution     1-38:H 39-163:T 164-427:R 428-685:T
K/SumDecay      1-40:H 41-312:R 313-633:T 634-708:G
```
Evidence for the classes (B6): of 1282 declarations of the non-H/I segments, class R has 682 (3% mention `mE`, `zt`, `GoodEvent`, `Stable`, `Hflow` or the band profile in the statement), G 248 (20% mention `Hflow`, as the random matrix), T 333 (32% mention the scalar-`m` tokens; the others are helpers of the same segments). `‖m‖ = 1` or `‖mE` stands in 23 lines of 8 `Green/` files and 19 lines of 6 `Evolution/` files (B6, grep). 268 of the 1282 declarations are private (106 in R, 63 in G, 94 in T): a BA row that twins a segment copies the band-free private helpers, as T2325 `§4` (`G-pub`) notes; the publishing alternative is not costed here (the identity `Gres H z true = green H z` has 17 private copies, 5 of them in `Green/`, and one public statement, `cont_Gres_true_eq_green`, `Induction/ContinuityNet.lean:430`; prove report (c)). R is the Gaussian calculus (`LDEQuad*` 2513, `RowIndep`, `FlucIter` words in `P`, `Q`, counting and weights, real-variable thresholds) and the combinatorial cores of E (`ek_anchor_sum_le` `SumDecay.lean:104`, Part I and III of `SumDecayZero`, `latticesum_d3` `Kernel/SumDecay.lean`).

**Route, groups of G segments** (`rows.py groups`, B7): in place = edited fraction `g` 0.15/0.24/0.30 (`T2360-design.md` §4) + 15 lines per name used outside its file (`consumers2.py`, B6) + BA instance 0.15/0.25/0.40 of the G lines (assumed); twin = ratio 0.73/0.97/1.61 (§5).
```
group              G lines names | in place lo/c/hi | twin lo/c/hi | choice
A LDE inputs          1621    28 |   906  1214  1554 |  1183  1572  2610 | in place     (LDE, RowIndep, IBPPoly)
B FA machinery        1145    44 |  1004  1221  1462 |   836  1111  1843 | twin         (FlucVanish, FlucIter(Gain), MinorGoodLe, MinorDiff)
C IBP display         1024     0 |   308   502   717 |   748   993  1649 | in place     (IBP)
D EntryDom nbr          53     1 |    31    41    52 |    39    51    85 | in place
E GbEXP, Pins          461     0 |   138   226   322 |   337   447   742 | in place
F Evolution            163     1 |    63    95   129 |   119   158   262 | in place     (SumDecay, Pins, Prec)
```
G1 of supervisor 2051: of the 185 public declarations of the G segments 74 are named in another file (upper bound by name match; 44 of them in group B, which is twinned); the 30 of the in-place files (`LDE` 15, `RowIndep` 10, `IBPPoly` 3, `EntryDom` 1, `Evolution/Pins` 1) need the `example : <old> := <old name>` checks (list: `cons_names.py`, B6); 8 names are used outside `Green/` and `Evolution/`: `im_green_diag`, `green_diag_ne_zero`, `measurable_green_apply`, `norm_green_apply_le_etaT`, `sum_sum_svar_le_maxLoopPM`, `hwConst`, `hwConst_pos` (`Graph/LWMoment*`, `Universality/GUE*`) and `AgreeOffRows` (registry). The in-place merges of `Green/LDE` and `IBPPoly` rebuild the UN files (critical path; rule G2 of supervisor 2051: schedule after UN-52b). Group B has 44 names (wrappers 660 lines): the twin is the cheaper route there. If a G segment cannot keep its band statement (rule G3), it goes into a new generic file and the band file stays.

The names of the in-place files (`python3 cons_names.py`, verbatim):
```
Green/LDE             15: measurable_green_apply measurable_greenDiagCentered measurable_greenMinorDiagCentered norm_green_apply_le_etaT norm_greenMinorMat_apply_le_etaT norm_greenDiagCentered_le_env flucBound_env integrable_norm_flucAvg_pow condExpDiag im_green_diag green_diag_ne_zero isUnit_det_Hflow_sub green_Hflow_diag_ne_zero stochDom_ldeRow stochDom_ldeCol
Green/RowIndep        10: minorCol minorCol_congr measurable_minorCol ldeRowLHS_eq rowVarSum_eq minorRowConj minorRowConj_congr measurable_minorRowConj rowSum_ae_eq_zero_of_varSum_eq_zero rowSum_rowCoeffNorm
Green/IBPPoly          3: hwConst hwConst_pos stochDom_ldeQuad
Green/IBP              0: 
Green/EntryDom         1: sum_sum_svar_le_maxLoopPM
Green/GbEXP            0: 
Green/Pins             0: 
Evolution/SumDecay     0: 
Evolution/Pins         1: ekSumNdecay_holds
Evolution/Prec         0: 
total 30
```

## 2. GE2: inputs and quantifiers

* **Target** (probe 40): `BAGbEXP d := BAGbEXPii d ∧ BAGbEXPij d ∧ BAGbEXPav d`, the owed pins unchanged (`BA/Step1Boot.lean:108-123`, registry `Test/Axioms.lean:187-189`), carrier `baFMz sz z` (`FlowPins.lean:550`), law `seqP (sz.withLam 0)`. Order: `κ ε 𝔡`, `𝔠 sz z`, `BAFlow`, `t` with `0 ≤ t n ≤ BAflowT0 sz z n`, `ε₀`; `av` adds the window `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` and `STInitialGT2gL`. They involve the loops `𝓛` of the carrier, not `𝒦` (`Step1Boot.lean:75-123`). Merged consumers: `baBootstrap'_holds` (`BA/Step1.lean:576`) and `baStep1_holds` (`BA/Step1Fam.lean:695`) take `BAGbEXPii`, `BAGbEXPij`; `BAGbEXPav` has none (grep: `Step1Boot`, the registry, a docstring in `UNPins.lean:39`).
* **Instance** (probe 99): `inst_BAGbEXP` at `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), `flow_sz0` (`κ = 1/2`, `ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`), `t ≡ 1/2 ≤ T₀ (≥ 2/3)`, `ε₀ = 1/10`: the three pins applied, every deterministic hypothesis discharged. The window of `av` is nonempty iff `ε₀ ≤ d/2` (`ba_av_window`, probe 87: `Ψ = W^{-1}` at `ε₀ = 1/10`; empty at `ε₀ = 2`, B9).
* **BA data facts** (compiled: `ba_G_data` probe 53, `ba_M_decay` probe 75, `BAGt_eq_green` probe 44, `BAMfine_diag` probe 116, `BAMfine_block_zero` probe 126). Counts in brackets are lines of the 28 files that name the band fact (`facts.py`, B6):

| band fact | BA replacement | merged source | rows |
|---|---|---|---|
| `|E| ≤ 2 - κ` (39) | `BAReal d L g₀ κ E m₀`, every `n` | `BAflow_real` `GreenSchur.lean:59` | G2 G3a G3b G5b G6a G6b |
| `t < 1`, `0 ≤ t` (266) | `0 ≤ t ≤ BAflowT0 < 1` | `BAt0_lt_one` `MFixedPoint.lean:285` | all |
| `Admissible 𝔠 𝔡` (132) | `BAFlow.1` | `FlowPins.lean:546` | all |
| `zt E t`, `etaT` (444) | `ztOf m₀ E t`, `Im = (1-t) Im m₀ > 0` | `ztOf_im` `Loop/GLoopFlow.lean:64` | all G |
| `mE E`, `‖m‖ = 1` (306) | `M_xx = m₀` (probe 116); `|m₀| ≤ 1` (`Ward.lean:136`); `M ≠ m₀ I` | `BAMB_diag_eq` `Ward.lean:89` | G3a G3b G4 G5a-c G6a G6b, E1 E3 |
| `Kstab3 d 𝔡⁻¹ κ` (39) | stability constant from `BAProp5s` | `baProp5s_holds` `Prop5Short.lean:667` | G3b G6a |
| `svar d L W (sz.lam n)` (196) | `svar d L W 0`, law of `sz.withLam 0` | `BlockAnderson.lean:83` | G2 G3a G5b G5c G6b E3 |
| none (the shift `λΨ`) | `G - M = -M(√t V + t m)G`; Schur split `D + X`; `Ψ` has no in-block entries | `BAGt_sub_BAMfine` `GreenSchur.lean:219`, `green_diag_split` `:293`, `green_off_split` `:335`, `BAPsiI_inBlock` `:265` | G2 G3a G3b G4 G5a G5c G6a |
| `g ≤ 𝔡⁻¹` | eventually `0 < g₀ ≤ 𝔡⁻¹`; `‖M_xy‖ ≤ c⁻¹e^{-c|·|}` uniform in `n` | `BAflow_lam0_window` `:72`, `BAMfine_decay` `:124` | G3b G4 G6a, E1-E3 |
| coupling window | `BAWinBulk` (`CouplingWindow.lean:799`) | used only by `BA/Step1*` (grep, B6) | none of G, E |
| `g ≤ W^{-ε}` | **not derivable** | `7_8:1948` | the cited proof, G3a-G6b |

* **F2, the range (gap, not pinned around).** `BAFlow` gives, eventually in `n`, `W^{-d/2+𝔡} ≤ g ≤ 𝔡⁻¹` (`(eq:WO)`, `Sizes.lean:163-166`); `[RBSO1D] L6.1` is proved for `g ≤ W^{-ε}` (`7_8:1948`), its text is not in the repo (`Jun.bib:168` only). `BAFlow_not_small` (probe 183): the merged `BAFlow` instance `λ ≡ 1/100`, `W_n = n + 1` (`GreenSchur.lean:542`) has `λ_n ≤ W_n^{-ε₁}` false eventually for every `ε₁ > 0`. The paper covers `g ≳ 1` by `(Mbound_AO2)` (`7_8:1902`); for `W^{-ε} < g ≤ 𝔡⁻¹` the TeX has only "verbatim".
* **F1, the shape.** `BAGijGEX` (`Step1Boot.lean:88-94`) is the band `(GijGEX)` (`3_5:24`): `1_Ω |(G_t - M)_xy|² ≺ Σ_{σ} Σ_{|a'-a|_∞ ≤ 1, |b'-b|_∞ ≤ 1} ‖𝓛^{(2)}_{t,σ,(a',b')}‖ + W^{-d} 1_{|a-b| ≤ 1}` (`FlowFM.gexRHS`, `:59-66`), no control parameter. The paper's `(GijGEX_BA)` (`7_8:1940-1946`) is conditional: for deterministic `0 < Φ_t ≤ W^{-ε₀}` with `𝓛^{(2)}_{t,(-,+),(a,b)} ≺ Φ_t(a,b)²` (`7_8:1924`), `max_{x∈[a],y∈[b]} |(G_t - M)_xy| ≺ Σ_{a',b'} Φ_t(a',b') e^{-c_λ(|a'-a|+|b'-b|)} + Ψ_t e^{-c_λ|a-b|} + W^{-D}`: all pairs, exponential weights. Reading: the pin implies the paper's lemma under `(initialGT2)` (sum over the window, `Ψ_t ≥ W^{-d/2}`, `1_Ω` removed w.h.p.), the converse is not available. The BA Schur row has the deterministic part `Σ_k D_{xk} G^{(x)}_{ky}`, which re-enters entries `G_{x'y}` at the neighbours `x'`; solving that system by a series in `M` gives exponentially weighted sums, and the passage to the window of radius 1 needs `𝓛^{(2)}` at distance `r` against the window, which is in neither the TeX nor `𝓛 ≺ Φ²`. The paper itself applies `(GijGEX_BA)` at `7_8:2041, 2090`, `(GiiGEX_BA)` at `7_8:2085` and the lemma at `7_8:2002`; the merged Step 1 (`baBootstrap'_holds`, `baStep1_holds`) and the band files that BA-T2 and BA-U5 are modelled on (`Evolution/FarEntry.lean:24-36`, `Induction/Step5Pins.lean:416`, supervisor 2252 Q2) read the band shape. `BAGiiGEX` is `1_Ω ‖G-M‖²_max ≺ max 𝓛^{(2)}` against the paper's `‖G_t - M‖_max ≺ Ψ_t` (`7_8:1930-1938`): the pin gives the paper's statement under `(initialGT2)` (reading); the event form is the formalization requirement of the continuity argument (DECISIONS §72 (5), D539).
* **Probe pin of G2** (probe 143): `BALDEin d`, the four large deviation inputs `hLrow, hLcol, hLquad, hLdiag` of the band `(4.2)`/`(4.3)` layer (`Green/EntryDom.lean:874-886, 997-1021`) at the BA carrier: `X = V` of `sz.withLam 0` (`BAX`, probe 136) against the minors of `G_t`, profile `svar d L W 0`. The vocabulary `ldeRowLHS`, … (`EntryCore.lean:514-553`) is class R. Its fourth conjunct is the merged `stochDom_normSq_Hflow_diag` (`LDE.lean:1099`) at `sz.withLam 0` (`BALDEin_diag`, probe 168, instance probe 352). The row/column inputs are `stochDom_rowSum_general` (`RowIndep.lean:1237`, any coefficient reading only off-row coordinates, R) with the BA coefficient `G^{(i)}`: G2 owes measurability and off-row dependence of the minor of `D + X` (`minorCol`, `RowIndep.lean:879-964`, G), and a.s. block support of `X` (not merged: `GreenSchur.lean:18` says so; `gaussianReal_zero_var`, Mathlib `Probability/Distributions/Gaussian/Real.lean:229`, is the route).
* **E pins** (probe 208-250): `BAEKSumNdecay`, `BAEKSumDecay1`, `BAEKSumDecayNAL`, `BAEKSumDecay2`, `BAEKSumDecayNonzero` in the shape of `Evolution/Pins.lean:64-140`, with `BAReal d L g κ E m` for `‖m‖ = 1 ∧ κ ≤ Im m`, `BAUN` (probe 202, on `BAMss`, `BATheta`, `MFixedPoint.lean:511-515`) for `UN d L g (EKsgn m σ)`, no antecedent `Prop5Decay`, `Prop5Short`, `Prop6Diff1`, `Prop8ZeroMode` (merged: `baProp5_holds`, `baProp5s_holds`, `baProp6_holds`, `baProp8_holds`, `Prop6Path.lean:850-1009`), constants `(d, n, Λ[, K], κ)` before `L g W ε D s t E m σ A`; `4 ≤ W^ε`, `log L ≤ W^ε`, `L^d ≤ W^K` as in the band (T2016a/b, T2042a); `sum_decay_nonzero` loss-free (the paper writes `≺`), as in the band. Instance `inst_BAEKSumDecay1` (probe 301): `n = 2`, `σ = (+,-)`, `s = 0`, `t = 1/2 ≤ 1 - g₀²/L²` (`g₀²/L² ≤ 1.5e-5`), `W = 16`, `ε = 1/2`, `D = 2`, `A = δ₀`.

## 3. GE3: paper status

| item | paper | band proof transfers? | argument |
|---|---|---|---|
| `(GiiGEX_BA)` and the averaged law, `7_8:1930-1938` | cited: `[RBSO1D] L6.1`, `g ≤ W^{-ε}`, "verbatim" (`7_8:1948`) | R for the Gaussian calculus and the row LDE; G for the resolvent layer; T for the entry estimates, stability, minor gain, IBP display (§1) | **gap, no complete argument.** (i) the range `g > W^{-ε}` (F2); (ii) with `D = g₀Ψ` the Schur equation of `G_ii` carries `(D G^{(i)} D)_ii`, i.e. `g₀² Σ_{k,l∼i} G^{(i)}_{kl}`, of the order of the target, and so is the mixed term `Σ_{k∈[i]} X_ik (G^{(i)}D)_{ki}` (a Gaussian row sum with coefficients `O(Ψ)`, since `M_{kl} = 0` for `k ≠ i` in the block of `i` and `l` at the offset of `i`): diagonal and off-diagonal entries form a coupled linear system, whose stability operator replaces the scalar `1 - t m² S` of `Stable`/`Kstab3`; (iii) `GoodEvent` (`EntryCore.lean:406`) centres `G_xy` at 0 and the minor calculus (`MinorDiff`) gains `Ψ` per difference from `G_aκ = O(Ψ)`, while `M_xy = O(g)` at neighbours (F3); inside one block `M_xy = 0` for `x ≠ y` (`BAMfine_block_zero`, probe 126) and the fluctuation-averaging sums (`S^{(B)}(0) = I`, `blkCoef2`) run inside a block, so the gain may survive there: for G5a to check. Reading, not verified |
| `(GijGEX_BA)`, `7_8:1940-1946` | same | T (series in `M`) | gap as above, and F1 |
| `sum_res_1`, `A:122-153` | proved in the TeX; BA remark inline `A:114-116` | R: anchor combinatorics; T: `Ξ` pins | **complete.** BA inputs merged: `BAK_row_sum` (`KKernel.lean:124`), `baProp5_holds`; the `(eq:decayXi)` step needs no `Mbound_AO` (F4, probe 264) |
| `sum_res_2_NAL`, `A:154-158` | `Σ_b|Ξ| = O(1)` from `(prop:ThfadC_short)` | same | complete; `baProp5s_holds` |
| `sum_res_2`, `A:159-198` | near/far split, `(sumAzero)`, `(prop:BD1)`, `(eq:latticesum_d3)` | R Part I, III (802 lines), T Part II, IV (681) | complete; `baProp6_holds`; `log L ≤ W^ε` is the paper's absorption (`A:196`, T2016a) |
| `sum_decay_nonzero`, `A:204-228` | `Proj_{e⊥}` commutes with `M^{(σσ')}` (translation invariance), `(eq:samecolor)`, `(prop:ThfadC0)` | T (`Nonzero.lean`, 160) | complete; `baProp5s_holds`, `baProp8_holds` |

Per TEAM §3 no row without a complete paper argument: G3a, G3b, G4, G5a, G5c (and G6a, G6b through them) have none; the 1a of those rows is a **design gate** (a written BA argument, audited before 1b), as for K05/K08. E1-E3 and G2 (Gaussian calculus, complete) start directly.

## 4. GE4: dependencies

* **Stage K: none.** No band `G`/`E` file names a `𝒦`-loop object outside docstrings and instances (grep, B6: only `Green/GbEXP.lean:835, 970, 972`: two docstrings and the instance of `stStep1_holds`, whose premises BA does not need). The G pins use the loops `𝓛` and the entries of `G` and `M`. The E lemmas take `(sumAzero)` and `(deccA0)` as hypotheses on an arbitrary tensor (probe 235): the old `E2 <- K3` is a consumer dependency (the molecule sum-zero of K08 is what the chain feeds in).
* **Stage P (merged):** the band E files use `prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds`, `prop8ZeroMode_holds`, `Green/Stability` `prop5Short_holds` (B6 grep, among these four): BA has all four (`baProp5/5s/6/8_holds`), `baPropM_holds` (`CombesThomas.lean:562`), `BAK_row_sum`.
* **Stage L, T/U/V: none** as inputs. Outputs go there: G6b to `baBootstrap'_holds` (S2b, merged as a conditional), BA-T2 (`FarEntry`), BA-U5; E3 to the `STEK*` consumer forms of Steps 3-4 (`Induction/Step34Pins.lean:613-676`), whose BA shape T2379 fixes (the E pins here are the deterministic layer): the target of E3 waits for that shape, E1 and E2 do not.
* **Parallel now:** all 12 rows; none waits for the stage-K close REQ; the G in-place files (`Green/`, `Evolution/`) are disjoint from K's (`Loop/`). Waves: {G2, E1}; {G3a, E2}; {G3b, G5a, G5c, E3}; {G4, G5b}; {G6a}; {G6b}. Critical path G2, G3a, G3b, G4, G6a, G6b (6); E chain 3.

## 5. GE5: deliverables

**Pins and facts compiled** (`lake env lean` exit 0, `lake build RBM3D.Probe.T2378Pins` clean, 31 declarations on the three standard axioms, 0 forbidden tokens: B1, B2): `BAGbEXP` (40), `BAGt_eq_green` (44), `ba_G_data` (53), `ba_M_decay` (75), `ba_av_window` (87), `inst_BAGbEXP` (99), `BAMfine_diag` (116), `BAMfine_block_zero` (126), `BAX` (136), `BALDEin` (143), `BALDEin_diag` (168), `BAFlow_not_small` (183), `BAuKer` (198), `BAUN` (202), the five E pins (208-250), `BAuKer_eq_one_add` (253), `BAuKer_convex` (264), `inst_BAEKSumDecay1` (301), instances (326-366).

**Row table** (`rows.py rows`, B7; bases are sums of the segments of §1, non-H/I lines). Ratios, BA lines / band lines: measured twins (B7): `BA/Step1Setup` 0.82, `BA/Step1` 1.05, `BA/ConArg` 2.26, `BA/Prop5` 1.06, `PropUnit` 1.11, `Prop5Short` 1.61, `Prop6Path` 2.10, heat family 1.84; `T2325` 0.73 (S-chain), 0.85 (graph L2); stage K: 6108 net lines / 5339 design central = 1.14 (supervisor `2026-10-10-0853.md`). **TW** (same structure; scalar `m`/`μ` to matrix `M`/kernel): 0.73 / 0.97 (= 0.85 x 1.14) / 1.61. **NW** (the BA argument changes): 0.85 / 1.37 (= 1.20 x 1.14) / 2.10. G in place: §1 formula. **b** (no band base): assumed. These are assumptions with measured end points, not measurements of G or E.
```
row  kind    lo central    hi  deps           role         target / basis
G2   g      906    1214  1554  -              prover-hard  BALDEin (probe 143); G 1621 lines (group A), 28 names; Green/{LDE,RowIndep,IBPPoly} in place + BA/GreenLDE
G3a  t      796    1274  1942  G2             prover-max   BA (4.7)-(4.10), (4.3) with the deterministic part; T 900 x NW + group D; BA/GreenCore
G3b  t      300     484   741  G3a            prover-max   BA stability of the diagonal equation (BAProp5s); T 353 x NW; BA/GreenStab
G4   b      500     800  1200  G3a, G3b       prover-max   (GijGEX_BA): series in M, exponential weights; assumed; BA/GreenOff
G5a  t     1123    1642  2617  G3a            prover-max   BA minor good event and differences; T 622 x NW + G 814 x TW; BA/GreenMinor
G5b  t      910    1209  2006  G5a            prover-hard  conditionalisation, threshold, FA moment bound; T 915 x TW + G 331 x TW; BA/GreenCond
G5c  t      946    1531  2294  G2, G3a        prover-max   BA display of E_i(G_ii - m), remainder; T 751 x NW + group C; Green/IBP in place + BA/GreenIBP
G6a  t     1076    1430  2373  G3a, G3b, G4   prover-hard  BA local law at a deterministic control, per-sequence layer; T 1474 x TW; BA/GreenLocal
G6b  t     1034    1416  2297  G6a, G5b, G5c prover-hard  BAGbEXPii, BAGbEXPij, BAGbEXPav; T 1227 x TW + group E; BA/GbEXP, Green/{GbEXP,Pins} in place
E1   t      880    1169  1940  -              prover-hard  BAuKer, BAUN, five pins (probe 198-250), Xi bounds; T 1205 (E/Pins, E/XiPins, K/Evolution, K/SumDecay) x TW; BA/EKPins
E2   t      664     889  1467  E1             prover-hard  BAEKSumDecay1/NAL/2; T 882 x TW + G 68; BA/EKSum
E3   t      326     438   706  E1,E2,T2379    prover       BAEKSumDecayNonzero, EK conclusions at scale N (prec_core over the BA law); T 388 x TW + G 95; BA/EKPrec
sum        9461   13496 21137   rows = 12 (G 9, E 3); G 7591/11000/17024; E 1870/2496/4113
```
Old plan (`T2161-portmap.md:1015-1023`): G2-G6 6400, E1-E3 3200 central; `T2325-portmap.md:95-107` revised: 5770 and 2750. The segment reading replaces the twin fear of `T2325-portmap.md:157` (the Green gate, 28.2k lines at 0.8 = 22.6k) by 10.5k lines of work in `Green/` (T 6242 + G 4304) and 1.9k in `Evolution/` (T 1771 + G 163). Order: §4 waves; a design check at G3a (BA stability) before G4, G5a, G5c is advised. Rows with hi > 2000 (G5a, G5b, G5c, G6a, G6b) may split.

**Exponent table** (`exp.py`, B9; all hold along `sz0`, (a) (ii)):

| quantity | value | constraint | slack |
|---|---|---|---|
| window of `av` | `[W^{-3/2}, W^{-ε₀}] = [5.5e-3, 0.707]` at `n = 0`, `ε₀ = 1/10` | nonempty iff `ε₀ ≤ d/2 = 3/2` | 128; empty at `ε₀ = 2` (compiled, probe 87) |
| `g₀ ≤ g ≤ 𝔡⁻¹` | `0.0130 ≤ 1/64 ≤ 10` | `(eq:WO)`, `BAg0_le` | 770 |
| `g ≤ W^{-ε}` | holds at `n = 0` (`1/64 ≤ 0.707`); fails along `λ ≡ 1/100` | not implied by `BAFlow` | none; compiled (probe 183) |
| rate `c` of `M` | `0.004158` (`κ = 1/2`), `0.002081` (`κ = 1/4`), `d = 3`, `Λ = 10` | `BAct_rate`, uniform in `n` | (a) row 8: ratio 4.2e-3 |
| `δ ≤ 2^{-19}` (`hB1`, `M = 1`, `FlucThreshold`) | `W ≥ 2^{190}` at `c = 1/10`, `2^{19}` at `c = 1`, `2^{13}` at `c = 3/2` | `δ = W^{-c}`, `c ∈ [ε₀, d/2]` | eventual only |
| `4 ≤ W^ε` (E pins) | `W ≥ 16` at `ε = 1/2` (instance); `4^{10}` at `ε = 1/10`: `sz0` from `n = 7` | T2016b | eventual |
| `log L ≤ W^{1/10}` | ok `n = 0`, fails `n = 1, 2`, ok `n ≥ 3` | `(eq:latticesum_d3)`, `A:194-198` | eventual ((a) row 14) |
| `κ` of `BAdom` | `Im m = 0.8325, 0.3777, 0.2620` at `g = 1/64, 1, 10` | `κ ≤ Im m`: `κ = 1/2` impossible at `g ≥ 1` | (a) row 4 |
| `≺` constants | `τ, D > 0` arbitrary; E constants depend on `(d, n, Λ, κ[, K])`, fixed before `L g W ε D` | | |

## 6. GE6: flag and count

BA ticket 45 (wide count). **Row count 12** (G 9, E 3), against the old 8 (G2-G6, E1-E3): the old plan twinned the stage as five G and three E files, the segments show nine G units. The count is at, not above, the limit of 12. Lines classed T (T lines x ratio, `rows.py`): central 9507 [6679 .. 15320]; with the twinned G lines of group B (1111 [836 .. 1844]) 10618 [7515 .. 17164]: **at the 10k line, above it on the second reading**. Reason, file by file (class T lines of §1): `EntryCore` 630, `EntryDom` 871, `Stability` 353: the entry estimates (4.2)-(4.5) and the stability are written for `GoodEvent … (mE E)`, `‖m‖ = 1`, `Stable S (t m²)`; `MinorGoodLe` 192, `MinorDiff` 430, `MinorDiffCond` 571, `CondDom` 210, `FlucThreshold` 134: the minor calculus gains one `Ψ` per difference from `G_aκ = O(Ψ)`; `IBP` 284, `IBPRem` 467: the display `G - m = m(-H - tm)G`, BA has `G - M = -M(√t V + t m)G` (`GreenSchur.lean:219`); `LocalLaw` 873, `GbEXP` 485, `Pins` 742: the pins and their wiring at `mE E`, the bridges to `STGbEXP*`; `Evolution`: `XiPins` 399, `SumDecay` 201, `SumDecayZero` 681, `Nonzero` 160, `Pins` 102, `Prec` 228, plus `Kernel/*` 704: `Θ_{tμ}`, `SB`, `UN (EKsgn m σ)` with a scalar `μ`, where BA has the kernel family `M^{(σσ')}`. The common reason: the band layer is `M = m I` throughout and BA's `M` is a matrix with off-diagonal entries of order `g` at neighbours (F3). **Per-stage flag 1.5 x 12 = 18 tickets**, set at the opening REQ; G5a, G5b, G5c, G6a, G6b are the rows that may split (hi 2.0-2.6k).

## 7. Decisions requested and paper-delta candidates

1. **F1, shape of `BAGbEXPij`/`BAGbEXPii`** (before G4's ticket): keep the band shape (then G4/G6a must prove the window comparison, absent from the TeX) or re-pin as primed successors in the paper's shape (then `baBootstrap'_holds`, `BA/Step1.lean:576`, `baStep1_holds`, `BA/Step1Fam.lean:695`, and the T2/U5 designs change).
2. **F2, range:** a written argument for `W^{-ε} < g ≤ 𝔡⁻¹` in the 1a of G3a/G3b/G4, or Jun authorises `[RBSO1D] L6.1` as an external input with its range (DECISIONS §5 authorises only the LSY Thm 2.2) and the BA main theorem is restricted; not decided here and not pinned around.
3. **TEAM §3:** design-gate 1a for G3a, G3b, G4, G5a, G5c.
4. **Route:** in place for groups A, C, D, E, F, twin for B (the G1 check files carry the 30 names of B6); the in-place merges of `Green/LDE`, `IBPPoly` after UN-52b.
5. **Flag** 18 and the T count of §6.
6. **Closing conditions:** stage G closes with `BAGbEXPii`, `BAGbEXPij` (consumed by `baBootstrap'_holds`, `baStep1_holds`) and `BAGbEXPav` (G6b; registry `Test/Axioms.lean:187-189`); stage E with the five pins `BAEKSumNdecay`, `…1`, `…NAL`, `…2`, `…Nonzero` (E1-E3) and the BA forms of `STEK*` (their shape: T2379). `BALDEin` is an interface pin of G2 (not registered).

Paper-delta candidates (temporary tags): `T2378a` `BAGijGEX` (band shape, `Step1Boot.lean:88-94`) against `(GijGEX_BA)` (`7_8:1940-1946`); `T2378b` `BAGiiGEX` against `(GiiGEX_BA)`/`(GavLGEX_BA)` (`7_8:1930-1938`: the pin has `1_Ω ‖G-M‖² ≺ max 𝓛^{(2)}`, the paper `‖G-M‖ ≺ Ψ_t` under `(initialGT2)`); `T2378c` `lem_GbEXP_BA` is cited for `g ≤ W^{-ε}` and claimed for `g ≤ 𝔡⁻¹` (`7_8:1948`): a paper gap, not a Lean difference; `T2378d` route remark (no statement difference): `(eq:decayXi)` for BA follows from `Θ` alone, `Ξ = ((t-s)/t)(Θ - 1)` (probe 264).
