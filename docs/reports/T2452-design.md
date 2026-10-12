Producer rows by sub-stage: **T: 2 new rows** (P1 untwisted BA grid pin `STGridMartgL` at `baStep2Mat`, from the TL pin; P2 `STNetLift2gL` at `baFMz`); **U: 0 new rows** (five targets of existing rows: P3, P4, P6 in T1/T1-BA, P5 in U5, P7 in U3-BA). New T flag 28.5 + 3.0 = **31.5**; U flag **34.5** (unchanged); BA count +2. **No stop rule fired** (2 rows <= 3; no new mathematics; no C8 stop; report 207 lines, probe 371 lines).

# T2452 design: the C10 coverage census by use of sub-stage U and the five ST-side T rows (BA-U U-D)
Written Mon Oct 12 13:46:36 UTC 2026 (`date -u`) by the stage-1b prover (claude-sonnet-5-5). Base `main` 551fa94 (= the worktree base); `main` has since moved to 04118b1 (T2451 `BA/TwistLoop`, T2453 `Chain/GridDuhamelGen` merged: new files, no row file changed, same census, see D1).
Probe: `RBM3D/Probe/T2452Pins.lean` on `t/T2452`, commit 20d5f15, 371 lines, `lake env lean` exit 0, 11 theorems and 5 examples, standard axioms (prove report (b)).
Scripts (not merged): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2452` (`cenlib.py` 204 lines, `census.py` 174, `b5b.py` 73, `run_all.sh` 24, helpers; hashes in the prove report).

## 0. Answers
- **D1** 19 rows, 85 files (112,527 lines); 530 declarations read outside the 117 row files; **77 have more than 200 lines below**. B5b rebuilt: 147 facts / 3,065 lines (= T2379), 63 of the 147 over 200.
- **D2** Of the 77: reuse 21; covered by a stage (P, K, E, G; L is open) or a merged BA theorem 44; no BA reader 4; U5-internal 2; **needs producer 6**. Of the 9 REQ lines: 4 confirmed, 3 refined, 2 refuted.
- **D3** (i) every consumer reads `m = 2`; `baTwistGridMart_holds` gives the untwisted grid pin up to three identities (shape compiled) -> P1. (ii) NetLift: BA-direct, 1 row -> P2. (iii) no BA row reads `STLemDecCalE`: no producer. (iv) CondDom: one read, no producer. (v) `Step2Scale`, `Step2Core` give targets (P3, P4), not rows.
- **D4** `BAKellStarEv` compiled with its proof (probe `:38-46`, `:82-151`). FarEntry's far field is K-level (`baEMn2ExpHK`, merged), so the Theta-level statement serves U5 only: a target of U5, no row.
- **D5/D6** P1, P2 in T; T 28.5 -> 31.5. The ST-side T1 is unchanged in statement (+330 lines for P4).

## D1. Scope and method
- **Rows** (`census.py:SCOPED`): T7, T1, T4s1 = `GridDuhamelN` only, T4s2 = `AzumaProxyN`, `AzumaProxyN2`, `GridGoodN`, `GridEnvelopeN`, `GridAssemblyN` (the move: `T2454.md:46-48`), T5s2, U1s1, U1s2, U2, U3s1 = `Step34Pins`, `Step34PinsP`, U3s2, U3s3, U3s4 = `Step3` + `Step4` lines 1-200 (§1-§2; §3 starts at `Step4:201`; U-C3) + `QtNonzero*`, U4s1-U4s3, U5t = `PfStep5*` (U5's template), U6, X1a (7 files), X1b (4 files). The nine BA-side rows read the facts of their ST pair.
- "Outside" = not among the 117 row files (the scoped rows plus the merged T8, T2, T3, T5s1, T6 and the V rows).
- **By use**: identifiers of the comment-stripped text of each row file up to its first instance section (T2379's `INST` regex, `common.py`), resolved Lean-style (namespace prefixes, `open`, imports; private names only in their file; dotted tokens with a local-looking head by their last component) to a declaration of `RBM3D/` (505 files, 26,884 declarations; `Probe/`, `Test/` excluded).
- Facts reached through a pin: for each Prop-valued def named in a signature of a row declaration, the `*_holds` theorem outside the rows whose conclusion is that pin (14 facts; the TSV marks them `*`).
- **Closure rule**: `below(f)` = sum of the lines of the declarations reachable from `f` by identifier references in its statement and proof, through declarations outside the 117 row files. Mathlib is not entered; instances and `simp` sets used implicitly are not seen (lower bound). Lines of a declaration: first line (attribute included) to the last non-blank line before the next declaration or command. Not the import closure. Threshold: more than 200 (C10).
- **Checks**: `nsof.sh` agrees with the census (full name, `file:line`) on all 77 over-200 names. Of 23,455 tokens whose last component names a library declaration, 21,283 resolve; the 2,172 others are mostly Mathlib or structure methods (`trans` 1,293, `congr` 242, `comp` 109, `mono`, `cons`, `length`).
- **Sensitivity**: facts over 100 / 200 / 300 / 500 lines: 122 / 77 / 56 / 40. With T2379-style raw spans (docstrings included): 115 over 200, a superset of the 77 (+14 definitions, +24 theorems).
- **B5b** (`T2379-prove.md:174-181`; its scripts are not in the repository): ported from `t2_facts.py` (found in T2379's scratch; `S/orig` holds copies of `common.py` and `t2_facts.py` with only `ROOT` edited). On this tree the original and the port give the same set: **147 facts / 3,065 lines, 64 band defs** (sorted walk: 3,044, because the name `integrable` exists in `Green/FlucIter:154` and `Green/LDEQuad:312`).
- B5b against the by-use census: 119 of the 147 are read by a scoped row (46 over 200), 28 only by merged rows (17 over 200). The census adds 86 band theorems of the B5b directories (18 over 200) and 89 declarations of non-row `Induction/` files (11 over 200) that B5b does not list (it matches short names and its directories exclude `Induction/`; the 14 pin-reached producers are among the additions).
- Commands (repository root, `main` or worktree, 61 s) and selected summary lines:
```
$ bash $S/run_all.sh out
B5b rebuilt: 147 distinct band-specific facts (3065 lines), 64 band defs; band-layer declarations indexed 12702, band defs (closure) 568
declarations read from outside the row files by the scoped rows: 530 (theorems/lemmas: 345 )
B5b facts: 147 own lines (T2379 span): 3065 | joined to the index: 147  with > 200 lines below: 63  <= 200: 84
tokens whose last component names a library declaration: 23455  resolved: 21283  unresolved: 2172
over-200 names 77 nsof.sh agrees on full name and file:line: 77
classes: {'reuse': 21, 'covered': 44, 'noreader': 4, 'producer': 6, 'u5': 2} total 77 unassigned: []
```
- The same driver on `main` 04118b1 gives byte-identical `facts.json` and `facts.tsv` (`diff`); its printed output differs only in the index size (507 vs 505 files) and the module counts of reverse cones (+1 or +2).

## D2. The census
Per row (`rowtable.py`): read = declarations outside the row files; `<=200` = the facts under the threshold; `thm` = theorems and lemmas among them; `pin` = read through a pin.
```
row   files  lines  read  >200 <=200  thm pin max below | row   files  lines  read  >200 <=200  thm pin max below
T7        3   5756   135     7   128   63   2     43789 | U3s2      7   9790   151    11   140   77   1     16802
T1        3   3947   117     7   110   55   6     43789 | U3s3     10  15456   105     9    96   49   1     16802
T4s1      1    778    30     1    29   12   0       242 | U3s4      8   8492   112     8   104   56   1     16802
T4s2      5   7752   158     8   150   77   1     16802 | U4s1      7   5431   135    13   122   76   0      4296
T5s2      5   5198   116    10   106   57   1     16802 | U4s2      2   5627    96    13    83   49   0      4900
U1s1      4   3031    61     5    56   24   0      4266 | U4s3      5   7796   156    14   142   71   0     23181
U1s2      4   5855    90     5    85   40   0       430 | U5t       3   4658    80     7    73   32   0     23181
U2        4   6705   132     9   123   68   0      6671 | U6        1   1044    29     0    29    0   0       200
U3s1      2   1312    60     6    54   13   6     17019 | X1a       7   5792   106     4   102   44   0     12963
                                                       | X1b       4   8107    56     6    50   28   0      4944
total: 85 files, 112,527 lines; 530 distinct declarations read; 77 over 200
```
**The 77 facts by layer.** Format `name@file:line(lines below)`; `spec` = a statement mentions `mE`, `zt`, `etaT`, `lemT`, `lemE`, `mSigma`, `msc`, `STflowE`, `|E|<` or `2-κ` (script regex). BA status: reuse / covered (names) / no BA reader / needs producer (P-number, D5). Full per-fact rows (full name, producer `file:line`, own lines, spec, first use of every reader, group, status): prove report (b), 77 lines.
- **Defs lattice sums** [reuse] rows U4s2; spec no
  facts: sum_conv_le@Convolution:225(401), sum_radial_pow_le@RadialSum:192(251), sum_ball_pow_le@RadialSum:445(292)
  BA: model-free (sums over `Zd (k+2) L`)
- **Loop, any Hermitian H** [reuse] rows T5s2,T7,U1s1,U1s2,U2,U3s2,U3s3,X1b; spec yes
  facts: sum_gloop_ward_last_div@ConArgDet:312(216), norm_sq_gloop_le_symIdx@Split:444(222), loopMax_odd_sq_le@Split:598(296), loopXi_le@Split:640(430), norm_gloop_le_of_le_abs_im@Split:757(246), norm_Lloop_le@GLoopFlow:700(374)
  BA: matrix-level, any `H`, any `z` with `Im z != 0` (`norm_Lloop_le`: with `Im ztOf = etaOf`)
- **Gaussian path, any `sz`** [reuse] rows T4s2,T5s2,T7,U3s2,U3s3,U3s4,U4s3,U5t; spec no
  facts: ST_pathP_eq_seqP@Step2Core:400(449), ST_whp_grid@Step2Core:422(549), map_pathH_eq@Walk:598(395), integrable_normSq_incr@StepDecomp:687(252), integrable_normPow4_incr@StepDecomp:693(262), integral_normSq_incr_le@StepDecomp:699(449), integral_normPow4_incr_le@StepDecomp:708(550), condExp_linear_eq_zero@Markov:335(492), hasCondSubgaussianMGF_linear@Markov:636(711)
  BA: statements are for every `sz`: apply at `sz.withLam 0` (`baStep2Mat.Pp`, `Hpath`)
- **Net (ContinuityNet)** [reuse] rows U3s2,U3s4,U4s3; spec no
  facts: cont_core@ContinuityNet:142(268), cont_highProbAt_good@ContinuityNet:369(326)
  BA: `cont_core` is model-free; `cont_highProbAt_good` at `sz.withLam 0` is the good event of `baGopbound`
- **E: PropTInf** [reuse] rows U4s1,U4s2; spec no
  facts: ekPropTInf_holds@PropTInf:534(899)
  BA: `EKPropTInf` is about `tailT` only (the PropTInf pattern); T2-BA uses it
- **E: sums and kernel norms** [covered] rows U3s1,U3s2,U3s3,U3s4,U4s1,U5t; spec no; `*` = read through a pin
  facts: ekSumDecayNonzero_holds@Nonzero:146(1490), ekSumDecayNAL_holds@SumDecay:420(1953), ekSumDecay2_holds@SumDecayZero:1411(2834), stek_sumNdecay_holds@Prec:215(561), stek_sumRes1_holds@Prec:358(5719), stek_sumRes2NAL_holds@Prec:242(6221), stek_sumRes2_holds@Prec:391(8429), stek_nonzero_holds@Prec:422(5880), norm_uKer_le@Evolution:114(363), norm_UN_apply_le@Evolution:131(399), norm_UN_le@Evolution:157(405)
  BA: stage E: `baEKSumDecayNonzero_holds` (EKNonzero:261), `baEKSumDecayNAL_holds` (EKSum:290), `baEKSumDecay2_holds` (EKSum:1772), `baEKSumDecay1_holds` (EKSum:200), `baEKSumNdecay_holds` (EKPins:218), `BAuKer_convex` (EKPins:79); Sizes-level BA `STEK*` = U3-BA targets
- **K: loops** [covered] rows T4s2,T5s2,U1s1,U2,U3s1,U3s2,U3s3,U3s4,U4s1; spec yes; `*` = read through a pin
  facts: KLbound_holds@KLFinal:154(16705), stKbound_holds@KLFinal:243(16802), stKward_holds@KLFinal:260(17019), KLPT_holds@KLFinal:143(6671), KLK_ward@KLWard:1318(4266), KLK_rotate@KLUnique:713(3049), KLK_isKLoop@KLTreeDeriv:1049(2561), KLward_two@KLTree:457(355), KLIndStepA_Theta_apply_sub@KLIndStepA:109(213)
  BA: stage K: `baKbound_holds` (KBound:245), `baKward_holds` (:302), `baKBoundAt_holds` (:85), `baK_ward` (KWard:305), `BAKsol_isKLoopS` (KSolve:606), `BAKsol_rotate` (:619), `EMn2BA_theta_shift` (EMn2BA:424)
- **P: properties 5-8** [covered] rows U3s2,U3s3,U3s4,U4s1,U4s2,X1b; spec no
  facts: prop5Decay_holds@Prop5Hold:784(4296), prop5Short_holds@Prop5Short:400(600), prop6Diff1_holds@Prop6Hold:353(4717), prop7Diff2_holds@Prop6Hold:384(4944), prop8ZeroMode_holds@Prop5Hold:1266(4900)
  BA: stage P: `baProp5_holds` (Prop6Path:850), `baProp6_holds` (:891), `baProp7_holds` (:941), `baProp8_holds` (:1009), `baProp5s_holds` (Prop5Short:667); all in `baProp5to8_holds` (:1049)
- **P: Props4 (explicit Theta)** [covered] rows T4s2,T5s2,U1s1,U1s2,U2,U4s1,U4s2,U4s3,U5t,X1b; spec no
  facts: Theta_transpose_of_three_le@Props4:95(201), Theta_apply_add_right_of_three_le@Props4:100(208), sum_Theta_row_of_three_le@Props4:114(211), Theta_real_eq@Props4:173(207), Theta_real_nonneg@Props4:177(217), norm_Theta_apply_le@Props4:188(240), sum_Theta_real_row@Props4:203(217), sum_norm_Theta_row_le@Props4:210(293), norm_Theta_le@Props4:218(306), Theta0_apply_eq@Props4:243(227)
  BA: stage P / KBase: `baP8_BATheta_shift` (Prop6Path:497), `BATheta_isSymm` (KBase:371), `BATheta_swap` (:350), `BATheta_row_sum_pm` (:381), `baTheta_row_le` (EMn2BA:374); the `‖m‖ = 1` ones are band readings (X1-C2: abstract profile)
- **G: Green** [covered] rows U4s3,X1a; spec no
  facts: gbEXPV3@GbEXP:806(12963), stGbEXPij_of_v3@Pins:1137(651)
  BA: stage G (primed, C3): `baGbEXPii_holds` (GreenLocal:474), `baGbEXPij'_holds` (GreenOff:1289)
- **G: flow premises** [covered] rows T7,U1s2,U2,U3s2,U3s3,U3s4,U4s1,U4s3,U5t,X1a; spec yes
  facts: v3_premises_of_stFlow@Pins:1049(309), lemma28_quant@Semicircle:359(232)
  BA: pieces `EMn2BA_T0_lt_one`, `EMn2BA_one_sub_T0` (EMn2BA:106, 111); packaging P6 = probe `T2452_ba_premises` (17 lines, compiled); the spectral conjunct is dropped (X1-C1)
- **G: LemDecCalE input** [noreader] rows U4s3; spec yes
  facts: gijGEXPTSwap_giiGEXPT_of_V3@Pins:310(323)
  BA: only reader `LemDecCalEPrec:657`; no BA instance (D3 iii)
- **L: Graph pins** [covered] rows T1,T7; spec no; `*` = read through a pin
  facts: lwterm_holds@LWTermHolds:682(36208), lwtermExp_holds@LWTermHolds:1604(43789)
  BA: stage L (open, 30/50): `baPin` pins `LWtermG`, `LWtermExpG` (LWPinsBA:39, :57-58)
- **Step2Core / Step2Scale** [producer] rows T1; spec yes; `*` = read through a pin
  facts: ST_good_engine@Step2Core:997(1129), stScaleExists_holds@Step2Scale:430(982)
  BA: P4 generic `ST_good_engine` (target of T1); P3 generic `stScaleExists_holds` (target of T1-BA)
- **DifREP: grid pins** [producer] rows T1,U4s3,U5t; spec no; `*` = read through a pin
  facts: stGridMart_holds@DifREP2:2283(21028), stGridMartAt_holds@DifREP2:2288(21027), stGridRepN_holds@DifREP3:2381(23181)
  BA: P1 (T): `STGridMartgL` at `baStep2Mat` (clause 4 of `STGridRepNAtgL d 2` for U5)
- **DifREP: U5 template** [u5] rows U5t; spec yes
  facts: difRep_flow_bounds@DifREP1:600(306), difRep2_norm_STeeM_le_N@DifREP2:1277(552)
  BA: U5-internal (design gate, U-C5): QV and flow bounds with `C.eta`; <= 80 lines; PfStep5:1714, :2112
- **NetLift** [producer] rows T1; spec no; `*` = read through a pin
  facts: stNetLift2_holds@NetLift2:688(2165)
  BA: P2 (T): `STNetLift2gL` at `baFMz`
- **KellStar** [covered] rows U4s3,X1a; spec no
  facts: kellStarEv@KellStar:173(4560)
  BA: X1a/FarEntry: K-level `baEMn2ExpHK` (EMn2BA:637); U4s3: none; U5: `BAKellStarEv` (probe, P5)
- **LemDecCalE*** [noreader] rows U4s3; spec no
  facts: lemDecCalE_lk@LemDecCalE:786(940), lemDecCalE_dif@LemDecCalEdif2:852(2673), lemDecCalE_wG@LemDecCalEwG:1995(2811)
  BA: `STLemDecCalE` has no reader; no BA instance (D3 iii)
- **Kernel algebra** [covered] rows T4s1; spec no
  facts: ukerMat_mul@Kernel:77(242)
  BA: T4s1 (T2453) `Step2Gen_UN_comp`; BA `BAuKer_comp` (TwistGrid:188)
- **LoopStep drift** [covered] rows T5s2; spec yes
  facts: condExp_loop_drift@LoopStep:310(2683)
  BA: TL: `baTwistGridRem_holds` (TwistGridRem2:394) is the BA one-step drift and remainder; untwisted via P1
Counts: **reuse 21, covered 44, no BA reader 4, U5-internal 2, needs producer 6** (= 77).

**Each line of the REQ table (`REQ:21-34`) and the F2 false positives.**
- X1 (13.9k) -> U4s2: confirmed (`IniTermI:2000-2008`: `stCltFar_uniform` from `stCltFar_holds`); producers X1a, X1b.
- Propagator (2.9k): refined. 15 facts over 200, read by 13 rows (T4s2, T5s2, U1s1, U1s2, U2, U3s2-U3s4, U4s1-U4s3, U5t, X1b; for example `Step5Kernel:139`, `IniTermI:2158`, `CltMoments1:944`), not by `Step34Pins`. All covered by stage P.
- Evolution/Kernel (stage E): confirmed for U3s1-U3s4, U4s1, U4s2, U5t (E facts through the U3s1 pins `Step34Pins:613-666`; U1s1 reads only facts under 200). `PropTInf` is model-free reuse: `EKPropTInf` (`PropTInf:522`) mentions only `tailT`.
- Loop (stage K) and Green (stage G): confirmed. `v3_premises_of_stFlow` is read by nine rows (flow premises; its spectral conjunct is `|E_n| < 2-κ/2`).
- **DifREP1-3**: confirmed and refined. Readers: T1 through the pins `STGridMart`, `STGridMartAt`, `STGridRepN` (`Step2Iterate:289, 1394, 1729`), U4s3 (`DuhamelI:1446`, `DuhamelII:529`), U5t (`PfStep5:2170`); all at `m = 2`.
- LemDecCalE* + NetLift2 + KellStar (7.9k): **refuted as one group**. `stLemDecCalE_holds` has no reader; `LemDecCalE*` is read by U4s3 only (`lemDecCalE_lk/_wG/_dif` at `LemDecCalEPrec:912-942`; U5t reads the constant `lossE2wG`, `PfStep5:1065`); `NetLift2` is read by T1 only (`Step2Iterate:1394`, and by name `:1781, 1788`; the imports `LemDecCalELip:7`, `LemDecCalEPrec:9` have no name use); `kellStarEv` by X1a and U4s3.
- **NetLift1: refuted** (F2). No row reads a `NetLift1` declaration. `QGridA` and `GridDriftN` contain no `NetLift` token; `EtermsMid` has comments and a private copy (`:30`, `:817`). `NetLift1` is imported by `NetLift2` alone.
- CondDom: refined. One declaration is read, `etaT_le_of_le` (`CondDom:288`), by U3s2 (`NQGood2:467`) and U3s3 (`QEndA:565`, `QEndGrid:568, 667`); `condRowReal`, `perTimeDomAt_of_moment` are used by Green files only (`IBPRem`, `GbEXP`, `MinorDiffCond`).

## D3. The unowned layers
**(i) DifREP.**
- *Which m.* All readers use `m = 2`. `ST_gridMart_of_repN` takes `h 2 le_rfl` (`Step2Iterate:1729-1731`) and keeps conjuncts 1-3 (`obtain ⟨Mart, Rem, hid, hrem, htail, -⟩`). `PfStep5:2170` takes `stGridRepN_holds d hd 2` and reads conjuncts 1, 2, 4 (`:52`). V2's assemblies pass `stGridRepN_holds` to `ST_step2_of_pinsLW'` (`MainIndHolds:39`, `MainIndOut:160`), which converts it at `m = 2`.
- So **U-C6 (c) can be narrowed to `m = 2`**: three clauses (`STGridMartAtgL`, `Step2Gen:857`) for T1 and U4s3, clause 4 (the `𝒰`-weighted tail) only for U5. TL covers no `m > 2` (its observable is a 2-loop), and no reader needs one.
- *Paper.* `Sol_CalL`, `lem:DIfREP` = `3_5:134, 218`. At BA: `7_8:1994` ("the technical lemmas ... remain valid ... except that (eq:MG_conclusion3) is modified"), `:1999` (the modified bound, with a deterministic `J`), `:2016` ("using it together with `lem:DIfREP`").
- The modification replaces `Ĵ` by `J` in the **bound on the quadratic variation** (`(E⊗E)^M`; the T2-BA step: `stEMn2ExpJgL_of`, `EMn2Exp2:1226`, and its merged BA `J` form `EMn2BA:772-774`; 0853 Q2). The pin states the QV itself in clause (iii) (`Step2Gen:857-880`): **the pin's statement is untouched**.
- *Coverage by TL.* `BATwistGridMartAt` (`BA/TwistGrid2:195`) has the same carrier (`baStep2Mat`: `Pp = pathP (sz.withLam 0)`, `BAFlow`, `BAflowT0`), the same quantifier structure and `∃ Mart Rem`, and four clauses. The twisted observable is `Tr(G(σ₁)E_aG(σ₂)P_{c₁c₂})` with `P_{cc} = E_c` (`BA/TwistPins:57-70`; `Eblk`, `Loop/GLoop:55`), so at `c₁ = c₂ = c` it is `𝓛^{(2)}_{σ,(a,c)}` with the **same** `σ`.
- It is not `rfl`: the drift is `Θ̃∘Z + B̃₁ + B̃₂ + Ẽ^{G̊}` (`TwistGrid:112`) against `STthetaOpg + STELKLKMg + STEGtMg` (`Step2Gen:841`), and the QV is the derivative form `twEEM` (`TwistGrid:101`) against the 6-loop `STEEMg` (`Step2Gen:399`).
- **Probe `T2452_bridge`** (`:241-306`, compiled): `BATwistGridMartAt d C₀` plus `T2452_Bridge d` (the three identities at `c₁ = c₂`, for `k ≤ K_n`, eventually in `n` along `BAFlow`: observable, drift, QV) gives `STGridMartAtgL d C₀ BAFlow (baStep2Mat …) BAflowT0`. `T2452_bridge_holds` (`:308`) gives `STGridMartgL` from `baTwistGridMart_holds` (`TwistStep:73`). The canonical `Mart`, `Rem` serve the finitely many `n` where the identities need not hold (for example `lam0 n <= 0`, where `baKsol_two` does not apply).
- Proved so far: the `K`-part of the observable, `T2452_K_eq` (`:327-342`; `baKsol_two`, `BAMss` unfolded). Owed: the loop part of the observable (about 100 lines), the drift (about 250), the QV (about 250), and for U5 the clause-4 pair (`twEEUk` against `STeeUMg`, the `STgANg` list forms: about 280).
- *Sizes.* **Option A, TL bridge (P1):** 450 / 760 / 1,500 lines (analogy: glue 82 lines and `K`-part 26 lines compiled; the identities against TL's `TwistGrid_gen_core` 98 and `BATwistHier_holds` 40; TL rows landed at 1.14-2.74 x central, `T2451.md:5`). BA side only, no ST row, no certificate module (at 551fa94 the reverse cones of `BA/TwistStep` and `BA/TwistGrid2` are 2 and 8 modules, none a `LWExpCert*`).
- **Option B, route G (P1G):** `DifREP1-3` = 5,989 non-instance lines, 569 band-mention lines (T2379 rx). ST edit 1,023 / 1,185 / 1,392 (all-directory band-def closure: 1,174 lines, 1,851 / 2,184 / 2,612; model = T2379 §4 ST side = X1 method) + U-row inputs + BA instance (>= 0.8k): **2.1k / 3k / 4.5k, 2-3 rows**.
- *Inputs from other rows* (`bound.py`, `urows.py`; route G only; sizes = declarations/lines the closure of `stGridRepN_holds`, `stGridMart_holds` reads in row files). T-internal: T4s1 7/54 (`Ugen`, `martIncN`, ...; now `Chain/GridDuhamelGen`, T2453 merged), T4s2 5/279 (`AzumaProxyN_YfieldsW` 199, `gridDriftN_envelope` 64), T5s2 19/214, T1 4/31 (`Step2Iterate:1586-1709`), T7 1/2.
- **U rows: U3s2 `NQGood1` 4/65** (`norm_STeeM_shiftN_le` `:996`, with `|E|<2`; full closure 174 lines in the U3s2 files); **U1s1 `zeroModeSet_UN`** (`ZeroModeCalc:332`) 2/8, closure 120; **U3s1 `STeeLoop`** 1/4. All restatable inside the producer (about 300 lines; `|E|<2` becomes `etaOf` bounds): the C8 pattern does not stop. Under option A none of them is read.

**(ii) NetLift1-2.**
- `STNetLift2gL` (`Step2Gen:602`) carries no spectral premise; the band proofs read `v3_premises_of_stFlow` (`NetLift1:859`, `NetLift2:690`). BA premises: probe `T2452_ba_premises` (`:179`, 17 lines, compiled: `t_n < 1` and `RangeCond (ε/2)`, from `EMn2BA_T0_lt_one`, `EMn2BA_one_sub_T0`).
- *Route G:* `NetLift1-2` = 1,667 lines, 131 band-mention lines (207 all-directory). ST 424 / 461 / 509 (528 / 587 / 662) + BA side 223 / 336 / 537 = 0.65 / 0.80 / 1.05k, 2 rows. In place it is a certificate merge (reverse cones 108 and 107 modules with the six `LWExpCert*`); an additive file is not.
- *BA-direct (P2):* `cont_core` (`ContinuityNet:142`) + `baGopbound` (`Step1Setup:346`) + `cont_highProbAt_good` at `sz.withLam 0`, as the merged `BA/TwistLoop` does. Its net machinery (`TwistLoop:87-517`) is about 430 lines for one family; the three families (Local, Avg, Decay) share the moduli: **600 / 900 / 1,600**, 1 row.
- *Paper.* `1_2:1399-1400`: the uniformity in `u` is "a standard `N^{-C}`-net and perturbation argument"; no BA-specific text and no paper gap.
- Recommendation: BA-direct (equal size, half the rows, no lane). The `private` moduli of `TwistLoop` are copied or un-privated by amend (`BA/TwistLoop` has no downstream module on `main`).

**(iii) LemDecCalE*.**
- No BA row reads `STLemDecCalE`. `grep` finds its definition (`Step5Pins:193`), the producer (`LemDecCalEPrec:1550`), the instance lemma `inst_lemDecCalE` (`Step5Pins:596`) used only by an example (`LemDecCalEPrec:1694`). Band `STStep5III` comes from `STPfStep5` (`Step5Cases:311`). At BA case (iii) is U5's new argument.
- **No producer.** U4s3's `LemDecCalEPrec` and `LemDecCalELip` need no generic form. What U5 reads of them is `lemDecCalEPrec_kell` (replaced by `BAKellStarEv`) and the constant `lossE2wG` (2 lines, restate). `gijGEXPTSwap_giiGEXPT_of_V3` has the same single reader.

**(iv) CondDom.** The only read is `etaT_le_of_le` (3 lines on `mE_im_pos`). Carrier form (probe `:347`, compiled): `0 ≤ Im m → u ≤ t → etaOf m t ≤ etaOf m u`, i.e. `C.eta` antitone in `t`. The band `etaT_le_of_le` is the case `m = mE E` (`etaT_eq_etaOf`); BA has `eta = etaOf (BAmF …)` (`FlowPins:328`). **No producer**; a 3-line target of U3-BA.

**(v) Other layers** (reads / over 200 / decision).
- `Step2Core` (16/3): `ST_pathP_eq_seqP`, `ST_whp_grid` reuse at `sz.withLam 0`. **`ST_good_engine` needs a generic form (P4)**: `Step2Core:997`, 299 lines; `mE (E n)` enters only as the constant `mI` and `|E| <= 2-κ` only to feed the pin `hNew`; read at `Step2Iterate:609`. `STGoodAt` itself is 22 lines (52 below): T7's restatement (`T2454`).
- `Step2Scale` (1/1): **P3**. `stScaleExists_holds` (`:430`, 128 lines) reads `v3_premises_of_stFlow` once and `scaleFacts_R1`; the BA copy takes the premises of `T2452_ba_premises`.
- `ContinuityNet` (8/2), `Split` (18/4), `ConArgDet` (12/1): reuse (matrix-level, any `H`). `Path/Walk` (17/1), `StepDecomp` (7/4), `Markov` (6/2): Gaussian increments for every `sz`, reuse at `withLam 0`.
- `Stop`, `Azuma`, `Expansion`, `OneStep`, `QVIdentity`, `UBounds`, `PerTimeCalc`, `EntryCore`: all facts at most 200 lines below. `Green/MinorDiff`, `Path/DriftAlgebra`, `DuhamelTail`, `UTransport`, `StepDecompLoop`: no scoped row reads them. Nothing owed.
- `Path/Kernel` (`ukerMat_mul` 242): T4s1's `Step2Gen_UN_comp` (merged T2453), BA `BAuKer_comp` (`TwistGrid:188`). `Path/LoopStep` (`condExp_loop_drift` 2,683, `zt E`): T5s2's own; not needed at BA under option A (`baTwistGridRem_holds`, `TwistGridRem2:394`).

## D4. `BAKellStarEv`
- *Readers of `kellStarEv`.* `FarEntry:712` (`δ = 1`, `D = 2D'`; conjunct 1 at `s = 0`, `:799`), `LemDecCalEPrec:990` (`δ = 1/8`, conjunct 1, `s = 0`), T2 through `emn2Exp_kellStar_far` (`EMn2Exp1:1762`; `EMn2Exp2:953-960`, conjunct 1). **No row reads the `ukerMat` conjunct** (`Path/UTransport:43` is a docstring; the file is imported by nothing): dropped, with the quantifier `s`.
- *Statement* (probe `:38-46`): for `Λ κ`, `sz`, `𝔠 τ δ D`, `t`, `g E : ℕ → ℝ`, `m : ℕ → ℂ` with `3 ≤ d`, positivity, `SizeTendsto`, `Bandwidth`, `RangeCond τ t`, `t n < 1`, `0 < g n ≤ Λ` eventually, `BAReal d (sz.L n) (g n) κ (E n) (m n)` for all `n`, and every `σ₁ σ₂ : Bool`: eventually, for `u ∈ [0, t_n]` and `δ (log W)^{3/2} ellT L (g n) u ≤ |a-b|_∞`, `‖BATheta d L (g n) (E n) (m n) u σ₁ σ₂ a b‖ ≤ W^{-D}`.
- Constants in `(d, Λ, κ)` only; `κ ≤ Im m` inside `BAReal`; no smallness of `g`, no scalar `m`, no spectral premise; all four charge pairs.
- *Consumer side* (probe `:48-53`, `:152-224`, compiled): `KellFarGen sz ell Th δ D t` is the far field of a profile family. `lemDecCalEPrec_kell` has exactly this type at `δ = 1/8` (example `:172`). Band: `T2452_kellFarGen_band` from `kellStarEv`. BA: `T2452_kellFarGen_ba` from `BAKellStarEv`. Both end to end from `STFlow` / `BAFlow` (band example `:216`; BA `T2452_kellFarGen_ba_flow` `:197`, with `Λ = 𝔡⁻¹`, `g = BAflowLam0`).
- *Compiled nonempty instance* (probe `:209`): `baKellStarEv 3` at `d = 3`, the BA instance `sz0`, `zSeq`, `flow_sz0` (`FlowPins` §9; `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`), `t ≡ 1/2 < t₀_n` (`half_lt_t0`), `δ = 1/8`, `D = 1`, charges `(+,-)`: every deterministic hypothesis discharged. Nondegenerate: `ellT = 1` there (`g_n < 1`), and the far scale `(1/8)(log W_n)^{3/2}` is at most `⌊L_n/2⌋` for `n = 0, 1, 10, 100, 1000` (0.81 / 2.28 / 7.59 / 17.09 / 29.29 against 2 / 4 / 22 / 202 / 2002: python check), so far pairs exist.
- *Finding.* FarEntry turns the Theta bound into a bound on `𝒦^{(2)}` by `KLK_two` (`FarEntry:425-444`: `‖𝒦‖ = W^{-d}‖Θ‖`). At BA `𝒦^{(2)} = W^{-d}(ΘM)` (`EMn2BA_K_two:624`), which the Theta bound alone does not control. The generic FarEntry should take the K-level hypothesis `emn2ExpHK` (`EMn2Exp2:934`; band `emn2Exp2_bandHK:945`; BA **`baEMn2ExpHK`, `EMn2BA:637`, merged**): then X1a needs no BA statement. The Theta-level readers are `PfStep5:2205-2206` (U5's template) and `LemDecCalEPrec` (no BA instance, D3 iii).
- *Route and size.* `baProp5_holds` (`Prop6Path:850`), `EMn2BA_theta_shift` (`:424`), `EMn2BA_bparam_le` (`:431`), the amplitude `(1-u)⁻¹ ≤ W^{A/𝔠}` and the closing inequality. Proof 70 lines + closing inequality 22 (a copy of the `private` `EMn2BA_arith:597`) + statement 9 = **about 100 lines**.
- Recommended: delete `private` at `EMn2BA:597` by amend (§153 (1); reverse cone of `BA/EMn2BA` at 551fa94: 15 modules, no certificate module), so there is no third copy; `EMn2BA` is otherwise unedited.
- *Placement.* A target of **U5's first BA ticket**, not a row: single Theta-level reader, 100 lines, TEAM §3 (merge small rows). If U5's design gate (U-C5) takes the K-level route it is dropped, with no flag change.

## D5. Producer rows
Model: T2379 §4 ST side = X1 method (1.65 x band-mention lines + 245) where a band file is restated; analogy to merged BA files otherwise (stated per row).

| id | content / generic pin | band source | route; lane | lo / c / hi | role, dependencies | sub-stage | row or target |
|---|---|---|---|---|---|---|---|
| P1 | `STGridMartgL` (3 clauses; clause 4 for U5) at `baStep2Mat`/`BAFlow`, from `baTwistGridMart_holds` + H1-H3 | `DifREP2:2283`, `DifREP3:2381` | BA reuse, new file; no lane | 450 / 760 / 1,500 (+280 clause 4); analogy | `prover-hard`, 1a with probe of H1-H3; deps TL, T8b, T4s1 (merged); stop if H2 or H3 > 400 lines -> P1G | T | **new row** |
| P1G | fallback: route G over `DifREP1-3` (additive) | same | additive new file; `DifREP` in place has no lane (cones 9-17 modules) | 2.1k / 3k / 4.5k (ST 1.0 / 1.2 / 1.4k; all-dirs 2.0 / 2.2 / 2.6k); T2379 model | deps T4s2, T5s2, U-row inputs restated (298 lines) | T | 2-3 rows |
| P2 | `STNetLift2gL` (`Step2Gen:602`) at `baFMz` | `NetLift2:688` | BA-direct, new file; no lane | 600 / 900 / 1,600; analogy to `TwistLoop` (route G: 0.65 / 0.80 / 1.05k, T2379 model) | `prover-hard`; deps `cont_core`, `baGopbound`, `T2452_ba_premises` | T | **new row** |
| P3 | `STScaleExistsgL` (`Step2Gen:632`) | `Step2Scale:430` | BA copy of the 128-line body | 150 / 200 / 300 | deps P6 | T | target of T1-BA |
| P4 | generic `ST_good_engine` (`mI`, the `hNew` instance as hypotheses) | `Step2Core:997` | additive restatement | 280 / 330 / 420 | read at `Step2Iterate:609` | T | target of T1 (ST side) |
| P5 | `BAKellStarEv` | `KellStar:173` | probe, about 100 lines | 90 / 100 / 160 | + amend `private` at `EMn2BA:597` | U | target of U5 |
| P6 | BA flow premises (`t < 1`, `RangeCond`) | `Green/Pins:1049` | probe `:179`, 17 lines | 17 / 30 / 50 | | T | target of T1-BA |
| P7 | `C.eta` antitone | `CondDom:288` | probe `:347`, 3 lines | 3 / 10 / 20 | | U | target of U3-BA |

Rules kept: generic over the carrier; no spectral premise (`BAFlow`, `κ ≤ Im m`, `0 ≤ Im m`); one kernel (`Step2Gen_UN`); constants in `(d, Λ, κ)`. Spectral premises recorded: none in P1-P7 (the band readings `|E|<2`, `2-κ` are not used), so X1-C1 holds and T2449's MN0 is not needed for them.

## D6. Flags and gating
- **Flags.** T: 12 of 28.5 (T2454 ticket) -> 28.5 + 1.5 x 2 = **31.5**. U: 34.5 + 0 = **34.5**. BA count: 119 at this ticket, +2 (P1, P2; no cap, §144). P1G would add 1.5-3.0 more (above about three extra rows: a short REQ).
- **T1-BA pin REQ (C7).** Names (proposals): `baGridMart_holds : STGridMartgL d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0` (P1); `baNetLift2_holds : STNetLift2gL d (fun sz => Sizes.seqP (sz.withLam 0)) BAFlow baFMz BAflowT0` (P2); `baScaleExists_holds : STScaleExistsgL d BAFlow BAflowT0` (P3, target of T1-BA); `baFlow_premises` (P6). `STGridRepNgL` is not needed by T1-BA (D3 i).
- **T1 (ST side).** Unchanged in statement: `ST_step2_of_pins` keeps `STGridMart`, `STNetLift2`, `STScaleExists` as hypotheses (`Step2Iterate:1392-1394`; the producers are applied only in the band corollaries `:1763-1800`, by name at `:1781, 1788`). Its size grows by P4 (+330).
- **Closing conditions.** Add to 1152 Q5 item 3 (U): `BAKellStarEv` merged and public if U5 reads Theta-level (P5), with `EMn2BA_arith` un-privated; the `eta` carrier form in U3-BA; no `LemDecCalE*` or `CondDom` row. Add to T's closing conditions: P1 and P2 merged with compiled nonempty `d = 3` instances; P3, P4, P6 merged as targets; the BA readings `STGridMartgL`, `STNetLift2gL`, `STScaleExistsgL` proved at `baStep2Mat`/`baFMz`/`BAFlow`; the T1-BA pin REQ lists them.

## Stop rules (ticket) checked
- Semantic or paper risk: none found. `BAKellStarEv` is a BA statement the paper does not state, but so is the band `KellStarEv` (a registry pin, a consequence of `(prop:ThfadC)`); it is proved in the probe from merged theorems (T2452c). P1 carries an execution risk (three identities not yet proved), handled by the 1a design gate and the P1G fallback. No band fact false at BA. No producer carries `|E|` or `mE`, so no conflict with a BA spectral reading (T2449 MN0) can arise from them.
- More than about three producer rows: 2 (P1, P2); P1G would be 2-3 more and then a short REQ.
- A T-placed producer waiting for a U-row output that cannot be restated: none (option A reads no U row; option B restates 298 lines).
- Size: report 207 lines (limit 300), probe 371 lines (limit 400).

## Findings and paper-delta candidates
- **T2452a** (registry): the pin `STLemDecCalE` has no reader in the chain (band case (iii) uses `STPfStep5`); `Path/UTransport` is imported by nothing.
- **T2452b**: at BA the grid martingale pin follows from the twisted pin, not from `lem:DIfREP` as for the band (the paper says "remain valid", `7_8:1994`).
- **T2452c**: `BAKellStarEv` is a Lean statement the paper does not make (it is `(prop:ThfadC)`, `1_2:1144` in `lem_propTH`, at the far scale).
- Not verified: the three identities H1-H3 (only the `K`-part is proved); the loop part for same-charge pairs `σ₀ = σ₁` was not compiled (`baKsol_two` is stated for all `σ`).
