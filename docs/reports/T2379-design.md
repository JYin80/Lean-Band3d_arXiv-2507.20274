# T2379 (BA-DT) stage T/U/V design: route G re-measured on the final band chain, carriers and pins, dependencies, row table, flag, band side

Prover `claude-sonnet-5-5` (prover-max, design only, CONTROL H173). Branch `t/T2379` (base `1f710ee`; `main` has since added only `BA/KCactusCut.lean`, `BA/KMolecule.lean`: no chain file moved), probe `RBM3D/Probe/T2379Pins.lean` (397 lines, limit 400), commit `00a2206`. Last edit: Sat Oct 10 11:06:42 UTC 2026 (`date -u`).
Citations: `path:N` is relative to `RBM3D/` at the base; `probe N` is a line of the probe; `Bk` is block k of (b) in `docs/reports/T2379-prove.md` (commands, verbatim output); `pilot §k` is `docs/reports/T2326-pilot.md`; `portmap §k` is `T2325-portmap.md`; `sup 2051` and `sup 0853` are `docs/supervisor/2026-10-09-2051.md` and `2026-10-10-0853.md`; `K1`..`K6` are the sections of `T2360-design.md`. "Tickets" = lines/1000 (portmap §7). Scripts are in the scratchpad subdirectory `T2379/` (not in the repository).

## 0. The answer

| item | answer | where |
|---|---|---|
| TV1 | **Route G stands; the tripwire does not fire.** Final chain: 101 files, S = 98,552 non-instance lines (95,029 without the BA-new row U5), g_cal = 0.191 (three points, rho = 1.92), f_sem bracket 0.4% to 14% (B1, B2, B3). Measured block `LoopGenN.lean:55-622` (compiled generic text, probe 108-392): **g = 136/568 = 0.239**, **f_sem = 0** (no line moves into the band instance), rho = 1.81 (pilot sites 1.66, 2.13). Break-even g 0.735 (f = 0) to 0.707 (f = 0.30); the corner (0.5, 0.30) is 70.9 tickets against route I 84.7 (B9a). Caveat: the three blocks the pilot named are not semantic by its own proxy (10.0%, 1.1%, 6.2% against 14.0% for the chain); the star-tree / K-formula lines (class (t) of K1) are 0.52% of the chain (KDecay 31%, HierAlgebra 26%). | §1 |
| TV2 | 15 carriers (rows T1-T8, U1-U6, V1), 238 Prop-valued pins and predicates (B5a); 16 generic forms exist (`BA/FlowPins.lean:328-458`); the probe compiles the Step 2 family (4 pins, `STStep2G`, `BAStep2`, probe 39-104), each band pin recovered by `Iff.rfl`: no obstruction on these five. **L1: the carrier `FlowFM` sits below two chain files** (`Step2Defs`, `Step34Pins`: 73 of the 203 frozen declarations); row 0 moves it upstream (B8e). BA data facts: 147 band-specific facts, 3,065 lines (B5b). | §2 |
| TV3 | The 24 ST-side tickets need nothing from BA: they start at the opening REQ. BA-side rows: K12 is needed by U2, U3, U6, V1, V2; E by T2, T3, T7, U1, U3, U4, V1; L by T1, T2, T7, T8, U4, V1; G by U3, U5, V2. Free now (merged inputs): T4, T5, T6; the statements of T8, U6. Not a stage-K target: far decay of `K` (`STKcalDecay`) and `stKloop_lip`. | §3 |
| TV4 | 46 rows: row 0 (carrier), 24 ST-side, 21 BA-side (18 + V2a, V2b, V3); central 40.6 tickets [30.6, 57.0]; with the stage-K ratio 1.144: 46.4 [35.0, 65.2]. First tickets, in parallel: **row 0** and **T5s1 = `LoopGenN.lean` + `HierarchyN.lean`** (51-module cone, no certificate). | §4 |
| TV5 | Chain **40.6 [30.6, 57.0] against the pilot's 38.9 [37.5, 48.3]**; routes I and T on the final file list: 84.7 and 98.9 (pilot 78.3 and 92.0). 46 rows > 40: **sub-stages T (19 rows, flag 28.5), U (19, 28.5), V (8, 12.0)**, each with its own open and close REQ. BA ticket 46. | §5 |
| TV6 | 96 of the 101 chain files change; 203 frozen declarations in 42 files keep their statements (G1 `example`s). 12 of the 24 ST-side tickets edit a file upstream of the certificate modules: 52 to 62 min wall per merge, measured (B8b); the other 12 cost 1 to 15 module-minutes (B9d). Private-helper coupling: 7 `open private` statements in 2 files (B8d). No `Graph/` or `LW*` file is edited by this stage. | §6 |

Verdict: **design delivered, TV1-TV6 answered; route G for the chain, route I for the graph layer, as the pilot recommended.** Decisions requested: §7.

## 1. TV1: route G on the final chain

**1.1 The chain now** (B1, B2d, B4; the scripts of `pilot §5`, `§7` on the pilot's file list plus the files added since its base `cc1158a`).

| | pilot (97 files) | final (101 files) |
|---|---|---|
| file lines / instance sections | 114,998 / 24,772 (21.5%) | 123,552 / 25,000 (20.2%) |
| non-instance lines S | 90,226 | **98,552** |
| band-mention density; calibrated g | 0.100; 0.199 (rho 1.99, two sites) | 0.0995; **0.191** (rho 1.92, three points) |
| theorem-granularity f_sem proxy | 12.5% | 14.0% (13,001 of 92,571 declaration lines) |
| frozen band signatures (G1) | 167 (word match, upper bound) | 203 in 42 files |
| route I / route T chain | 78.3 / 92.0 | 84.7 / 98.9 |

Added since the pilot base (B1): `IniTermI` 3823, `DuhamelI` 1994, `EtermsMid` 1757, `DuhamelII` 976 lines (Step 5 cases (i), (ii), row U4: +8,554 file lines by the script's count, +4,435 direct-mention lines); `MainIndBase`, `MainIndChain`, `MainIndOut`, `MainIndHolds` (735 lines) are already generic over `FlowFM` (ST-6 R1-R3, `MainIndOut.lean:51,99,144`): route G has been run once on the band side. The pilot counted `PfStep5*` (3,523 lines) in S and again in B_new (1300, "BA case (iii) is another argument", `portmap §3` U5); corrected here, S is 95,029.

**1.2 The measured block.** `Induction/LoopGenN.lean:55-622` (568 lines): the loop-generator identity `loopGenN` (`eq:mainStoflow`) at a Hermitian `M`, kernel `S^{(B)}(g)`, flow `z_t`, one-loop value `m`. Of the three named blocks it is the highest on both proxies (declaration-granularity 10.0% against 6.2% KDecay and 1.1% ZeroModeCalc; band-mention 12.2% against 5.3% and 6.2%, B2a). Generic text: the 11 declarations that read `zt`, `spectralMSign`, `|E| < 2` are restated over `m` (`ztOf m E u`, `PropSpin m sigma`, `0 < m.im`); 3 declarations are new; 12 band-free private declarations are reused by `open private` (probe 29-32, plus two instance data), i.e. they are the unchanged lines of an in-place edit. The carrier of this block collapses to the pair `(g, m)` (class P of T2173): band `m = mE E`; block Anderson `g = 0` (the law `seqP (sz.withLam 0)`; `sbKernel d L 0` is `1_{x=0}`, `Defs/Block.lean:36`) and `m = BAmF`.

| quantity (B3) | value |
|---|---|
| g, `git diff --no-index --numstat` (pilot B5 primary) | 136 added, 99 removed, of 568: **0.239** |
| per-declaration alignment | 100 edited lines in 11 declarations + 18 new + 21 of the band corollary = 139: 0.245 (0.210 without its 20 unchanged statement lines) |
| hunk-wise difflib | 0.363, an alignment artefact (the 70-line theorem is read as 79 inserted and 51 removed lines because the band corollary keeps the merged statement) |
| the 99 removed lines | 43 `zt E` to `ztOf m E`; 13 the argument `m` threaded; 10 one-loop value; 9 window `hE` to `hm`; 4 spectral lemmas; 4 `genMat`; 16 other |
| f_sem (lines moved into the band instance) | **0**: band instance `recovers_loopGenN` (probe 369-371: three lines, `mE_im_pos hE`); BA instance: the same theorem at `g = 0`, `m = BAmF` (probe 385-388) |
| rho = edit lines per band-mention line | 1.81 (sites 1.66, 2.13; three points 1.92) |
| the repository already holds a twin | 74% of the block's lines occur verbatim, after renaming, in `Universality/GUEPhase/Generator.lean` (T2305, 1416 lines) |

**1.3 What is semantic on the final chain** (B2). The pilot's proxy counts a whole theorem if its proof unfolds a primitive band object: 14.0%, an upper bound (DuhamelII, 65%, counts three whole theorems of 22, 190 and 356 lines for one primitive mention each: `UN`, `STgDrift`/`etaT`, `STgA`; `S/t1_sem_detail.py DuhamelII`). At tactic-line granularity: 337 of 79,603 code lines (0.42%). The lines that name a star-tree or K closed form (`KLtreeValW`, `KLSigmaPi`, `kTwo`, `KLIsTSP`, ...: class (t) of K1): 483 lines, 0.52%: `KDecay` 258 of 825 (31%), `HierAlgebra` 190 of 721 (26%), `ExpHier` 35. Read, not compiled: `KDecay` is at the 0.30 line, but its tree sums are a twin row (the BA `K` sum is a cactus: K5); it is counted at 0.8 in the BA-side term of the model, not tested by the rule. f_sem of the chain lies in [0.4%, 14%].

**1.4 The decision rule on the final chain** (B9a; chain = (1-f) S g + f S 0.8 + overhead 6,720 + wiring 4,320 + B_new 3,800, S = 95,029).

| (g, f) | chain tickets | margin to route I (84.7) |
|---|---|---|
| central (0.191, 0.14) | 41.0 | 43.7 |
| measured block (0.239, 0) | 37.6 | 47.1 |
| (0.30, 0.30) | 57.6 | 27.1 |
| tripwire corner (0.5, 0.30) | 70.9 | 13.8 (3.6 if only route G is inflated by 1.144) |

Break-even g (G = I): 0.735 at f = 0, 0.725 at 0.14, 0.707 at 0.30; against route T 0.885 to 0.921. Break-even f at g = 0.24: 0.884. The thresholds g 0.5 and f 0.30 lie inside the break-even; no measurement reaches them. The paper supports the route: "the proof of `lem:main_ind_BA` follows the same six-step strategy ... we explain how the arguments ... for the random band matrix model extend to the block Anderson model" (`7_8:1841`).

**1.5 Recommendation.** Route G for the chain (G1: `example : <old> := <old name>` for every frozen declaration; G2: critical-path merges first), route I for the graph layer (unchanged). A second tripwire on the first merged tickets: T5s1 reports g and the lines moved (expected 0.24 and 0); the first ticket that converts a class (t) file (`HierAlgebra` in T5s2, `KDecay` in U2) reports f_sem of its own file; a value above 0.5 or 0.30 returns the remaining rows to route I.

## 2. TV2: carriers and pins

Generic forms that exist: `PrecL`, the twelve Step 1 pins, `STJhatg`, `STEEg`, `STmaxLoop2g` (`BA/FlowPins.lean:328-458`, B5a), `STMainIndG` (`:565`), `STMLOutG` (`MainIndOut.lean:51`), `STLK0`, `STG0M`, `STBaseG` (`MainIndBase.lean:50-58`), `STHorizonG` (`MainIndChain.lean:43`). New in the probe (39-104): `STAvgUgL`, `STLocalEntryUgL`, `STGdecayWgL`, `STStep2ConclgL`, `STStep2G` (the shape of `STMainIndG`: constants first, `forall sz z, Flow ... ->`), `BAStep2 d := STStep2G d (seqP (withLam 0)) BAFlow baFMz BAflowT0` (probe 95-96), and `Iff.rfl` bridges to `STAvgU`, `STLocalEntryU`, `STGdecayW`, `STStep2Concl`, `STStep2` (`Step34Pins.lean:221`, `Step2Defs.lean:599`). The nine step pins of `ST_mainInd_of_pins'` (`Step4.lean:209`) have this shape (`STStep3R`, `STStep5R`, `STStep6R`: `Step34Pins.lean:250`, `Step5Pins.lean:101`, `Step6Pins.lean:126`; the regime predicate `R` is a parameter).

**L1 (layering finding, B8e).** `BA/FlowPins.lean:7-8` imports `Induction/Defs` and `Induction/Step2Defs`, and through them `Step34Pins`; no chain file imports `BA/FlowPins` today. `Step2Defs` (T8: 49 frozen vocabulary definitions) and `Step34Pins` (U3: 24) are therefore upstream of `FlowFM` and cannot be restated over it in place; their generic readings are additive (new definitions and `Iff.rfl` bridges, the band text untouched). The other 99 files would import the carrier; importing `BA.FlowPins` would make the band chain depend on `BA/MFixedPoint` and rebuild it on every edit of `FlowPins` or `MFixedPoint`. **Row 0**: move `PrecL`, `FlowFM` and the generic Step 1 pins (`BA/FlowPins.lean:326-466`, 141 lines) into a neutral file `Chain/Carrier.lean` (names and statements kept; `FlowPins` imports it). Cone of `BA/FlowPins`: 33 modules, 27,955 lines, no certificate (about 8 module-minutes at the measured 16.8 s per 1000 lines).

The carriers, in dependency order (S = non-instance lines; pins = Prop-valued definitions, B5a; facts = distinct band-specific theorems the row's text uses outside `Induction/`, with their total lines, B5b: the data the BA instance supplies as carrier facts):

| carrier (rows: files; S) | pins | facts | what the BA instance reads and supplies |
|---|---|---|---|
| T8 `Step2Pins` (3; 1,699) | 30 | 2 / 17 | vocabulary `STLM`, `STLKM`, `STJhatM`, `STthetaOp`...; pilot `Step2Data` (19 fields + 6 facts); BA: `flowOK_T` needs `0 < kappa` (pilot §4), `flowOK_m` from `BAWinBulk`, `BAm_im_lower` |
| T7 `DecayEvents` (3; 4,779) | 6 | 14 / 158 | events (E1)-(E5), `ST_good_prob`, `stDecayLoopAt_holds`; inputs `inst_stKcalDecay_admissible`, `EKFastDecay`, `LWAssm` |
| T1 `Step2Iter` (3; 3,587) | 2 | 13 / 170 | pilot site 1 (g 0.148): `baStep2` with 11 open obligations (`ev1`-`ev4`, `Good`, `ident`, `martTail`, `pLWT`, `pEMe`, `pNew`, `flowOK_m`) |
| T2 `EMn2` (3; 3,850) | 0 | 11 / 230 | `STEEk`, `STJhat`, `STprof`; BA `(eq_resolventunderpoly)`, `(Mbound_AO)` (`portmap §3`); `ekPropTInf_holds` |
| T3 `NewKLK` (2; 1,382) | 0 | 12 / 105 | `STNewKLKAt`: deterministic for any Hermitian `H`; `Theta` symmetry, `SB` entries; `KLK_two` |
| T4 `GridDuhamel` (6; 6,361) | 14 | 41 / 512 | kernel `Ugen`/`UN d L g (mSigma E .)`, `AvecN`, `assembledN`; pilot `QKerData` (propagator family, domain, `Im m`, EK-4); BA: `K = M^{(+,-)}` doubly stochastic (`BA/KKernel.lean:124`) |
| T5 `Hierarchy` (7; 5,415) | 8 | 36 / 524 | `loopGenN` (class P, measured), `StepDecompN`, `QVN`, `GridDriftN`; `HierAlgebra`: `kTwo` (class (t)); `IsKLoopS` generic (K) |
| T6 `Contract` (2; 1,662) | 0 | 4 / 31 | matrix core (0 band tokens in `ContractPt`): instantiate |
| U1 `ZeroMode` (8; 7,883) | 1 | 28 / 309 | commutation of the zero-mode projection with `Theta`, `UN` (row sums `= 1`: `BAK_row_sum`); `KLK_rotate`, `KLK_ward` |
| U2 `KDecayEtc` (4; 5,862) | 1 | 26 / 290 | `STKcalDecay` is a carrier fact; its band proof (tree sums) is class (t): BA twin on K outputs |
| U3 `QFamily` (27; 22,433) | 75 | 37 / 944 | pilot `QDriftData` (9 data, 7 facts: `Theta` sum-zero, good set, 5 measurability); `STKbound`, `STKward`, `stKloop_lip` (`NQEndFlowLift.lean:581`) |
| U4 `Step5Cases` (14; 17,939) | 2 | 50 / 1,172 | `STEtermsMid`, Duhamel, `IniTerm`, `WardII`, `NewKLKL`, `TailtoTail`; `STLWT`, `ekPropTInf`, `stCltFar` |
| U5 `PfStep5` (3; 3,523) | 14 | 14 / 239 | not converted: BA case (iii) is `[RBSO1D S7.3]` with `lem_GbEXP_BA` (`portmap §3`, T2325c): new mathematics |
| U6 `Step5Pins` (1; 476) | 39 | 0 | pin vocabulary (`STReg5*`, `STIngR5`, `STStep5R`); 22 frozen |
| V1 `Step6` (15; 11,701) | 46 | 58 / 882 | `STStep6R/I/II/III`, `STExp2U`; `LWtermEXP`, `LWAvgLaw`, `LWcut`; `EKSumZero` |
| V2/V3 (B_new) | | | `STMainIndG` at BA (`ST_mainIndR_of_steps` `MainIndRegimes.lean:165`, `ST_mainInd_of_regimes` `:616`, with `Sizes.comp`); `STBaseG`, `STHorizonG` at BA: `unMLOutBA_of_pins` is a 6-line wrapper (`MainIndOut.lean:144`), so V3 is likely under its 700 lines (T2338 §6) |

## 3. TV3: dependencies on the other BA stages

Inputs found by word match on each row's text (B7b: first `file:line` of each name; B7a: counts). Merged: K00-K06 (`BA/KBase`, `KSolve` (`BAKsolve`, `n <= 3`), `KWard` (`baK_ward`), `KCactus`, `KTreeDeriv`, `KTreeRep` (`BAKsol_isKLoopS`), `KMolecule`); stage P closed (`BAProp5to8`); `BAStep1` (`baStep1_holds`, `Step1Fam.lean:695`) needs `BAGbEXPii`, `BAGbEXPij` (`Step1Boot.lean:108,116`).

| row | K | E | L | G | C and others | BA-side start |
|---|---|---|---|---|---|---|
| T8 | `KLloopOf` | | `STLWB`, `STLWT`, `STEMn2Exp` as pins (`Step2Defs.lean:406,421,456`) | | | now: statements; facts as arguments |
| T7 | `KLK_one`, `inst_stKcalDecay_admissible` (`DecayLoopA.lean:775`, `DecayLoopB.lean:1444,1774`) | `EKFastDecay`, `STEKDecay` (`DecayLoopB.lean:2006,2213`) | `LWAssm`, `LWcut` (`Step2Events.lean:1370,1296`) | | | E + L + `BAKcalDecay` (U2) |
| T1 | `KLK_one` (`Step2Iterate.lean:1243`) | | `LWtermExp`, `STLWB` | | T2, T3 | L (constructor now) |
| T2 | `KLK_two` (`EMn2Exp2.lean:725`) | `ekPropTInf_holds` (`:942`) | `STLWassm` | | | E |
| T3 | `KLK_two` (`NewKLK.lean:697`) | `ekPropTInf_holds` (`:996`) | | | | E |
| T4 | `KLK_isKLoop` (`AzumaProxyN.lean:503`) | | | | feeds BA-C5 (T4, T5) | now |
| T5 | `KLK_isKLoop` (`GridDriftN.lean:519`), `kTwo` (`HierAlgebra.lean:485`) | | | | feeds BA-C5 | now |
| T6 | | | | | | now |
| U1 | `KLK_rotate`, `KLK_ward` (`NewPQ.lean:639`) | `EKFastDecay` (`QopNorm.lean:384`) | | | | E |
| U2 | `KLK_*`, `inst_stKcalDecay_admissible` (`B45.lean:1560`) | | | | | K12 |
| U3 | `STKbound`, `STKward`, `KLbound_holds` (`NQEndFlowLift.lean:477`), `stKloop_lip` | `EKFastDecay`, `EKSumZero`, `STEKDecay` (`Step34Pins.lean:534,656,595`) | | `STStep1` (`Step4.lean:213`) | | K12 + E |
| U4 | `KLK_one/two/rotate` | `ekPropTInf`, `stCltFar` (`IniTermI.lean:2008`) | `STLWT` (`EtermsMid.lean:1212`) | `AsGMcPT` (owed, registry) | | E + L |
| U5 | | | | `BAGbEXPii/ij/av` | paper gap | G |
| U6 | `STKbound`, `STKward` (`Step5Pins.lean:88`) | | | | | K12 (statements: now) |
| V1 | `KLK_one/rotate`, `stKbound_of_flow` | `EKFastDecay`, `EKSumZero`, `STEKDecay` (`Step6Pins.lean:331`) | `LWAvgLaw`, `LWcut`, `LWtermEXP` (`Step6Kit.lean:190,329,571`) | | | K12 + E + L |
| V2/V3 | K12 | | | `BAStep1` unconditional | `UNMLOutBA` (`BA/UNPins`, merged); stage M (BA-M1) | after all step pins |

Which rows can start before K, G, E, L close: all 24 ST-side tickets; of the BA-side rows T4, T5, T6 now, T8 and U6 for their statements. Which wait for a stage-close REQ: the rest, for the unconditional BA theorem; a conditional BA ticket may start earlier with the other stage's pin as a hypothesis, as T2256 and `inst_baStep1` do (`Step1Fam.lean:982`), and is closed by the stage-close REQ. Not a stage-K target: far decay `STKcalDecay` and `stKloop_lip` are the K-derived carrier facts that `sup 2051` Q5 assigned to stage T/U/V: rows U2 and U3 own them (class (t), 258 lines of `KDecay` at the twin rate). `STKwardgL` does not exist yet (K12 pins it: `T2360-design.md` §7 item 4; `grep STKwardgL` on the base: 0). Sibling (`T2378-design.md` §0, an unaudited draft of 10:55 UTC): its F1, F2 report that `BAGijGEX` has the band shape and that the premise `g <= W^{-eps}` of the G-stage argument is not derivable; if the G pins change shape, `BAStep1` (`Step1Fam.lean:361`) changes with them, and U3 (`STStep1`), V2, V3 wait for that decision. Its GE4 says no stage G or E row needs a T/U/V output.

## 4. TV4: the row table

Model (pilot §5, per row; B9b): ST side = (1-f) S_r g_r + 245 + 15 x frozen_r, g_r = 1.92 x density_r (B2d), f = 0.14; BA side = f S_r 0.8 + 100 + 60 x endpoints_r. lo: g_r x 0.75, f 0.05; hi: g_r x 1.5, f 0.30 (the tripwire). Totals are the pilot's formula; the split puts the twin-rate lines where they are written. Ticket counts: an ST carrier needs max(1, ceil(ST central / 1,500), ceil(S / 7,000)) tickets, a BA carrier ceil(BA central / 1,500); the groups below are then balanced by band lines (largest: 8,173 lines, 1,486 edit lines). The stage-K ratio 6108/5339 = 1.144 (`sup 0853:160`) applies to the totals.

| carrier | ST tickets | ST lines lo / c / hi | BA tickets | BA lines lo / c / hi | BA side depends on |
|---|---|---|---|---|---|
| row 0 | 1: `Chain/Carrier` (new), `BA/FlowPins` | 250 | | | |
| T8 | 1 | 1,333 / 1,403 / 1,493 | 1 | 348 / 470 / 688 | L pins as arguments |
| T7 | 1 | 793 / 898 / 1,032 | 1 | 471 / 815 / 1,427 | E, L, `BAKcalDecay` (U2) |
| T1 | 1 | 1,027 / 1,136 / 1,276 | 1 | 423 / 682 / 1,141 | T2, T3, T8, L |
| T2 | 1 | 519 / 572 / 641 | 1 | 374 / 651 / 1,144 | E |
| T3 | 1 | 458 / 499 / 552 | 1 | 275 / 375 / 552 | E |
| T4 | 2 | 1,389 / 1,576 / 1,818 | 1 | 354 / 812 / 1,627 | K05b |
| T5 | 2 | 1,533 / 1,743 / 2,015 | 1 | 317 / 706 / 1,400 | K03, K05b |
| T6 | 1 | 276 / 283 / 291 | 1 | 286 / 406 / 619 | none |
| U1 | 2 | 1,192 / 1,384 / 1,633 | 1 | 655 / 1,223 / 2,232 | E, K02 |
| U2 | 1 | 1,034 / 1,195 / 1,401 | 1 | 514 / 937 / 1,687 | K12 |
| U3 | 4 | 3,841 / 4,486 / 5,317 | 2 | 1,297 / 2,912 / 5,784 | K12, E, G |
| U4 | 3 | 2,629 / 3,085 / 3,673 | 2 | 1,418 / 2,709 / 5,005 | E, L |
| U5 | (not converted) | | 1 | 1,300 | G, paper gap |
| U6 | 1 | 697 / 722 / 754 | 1 | 179 / 213 / 274 | K12 |
| V1 | 3 | 2,703 / 3,125 / 3,669 | 2 | 928 / 1,771 / 3,268 | K12, E, L |
| V2a, V2b, V3 | | | 3 | 800 / 1,100 / 1,600; 500 / 700 / 1,000; 700 | all step pins, K12, G |
| **sum** | **24 + row 0** | 19,425 / 22,108 / 25,566 | **21** | 7,841 / 14,683 / 26,847 (+ 3,800 B_new) | |

The 24 ST-side tickets (B9d; files in dependency order; edit = sum of 1.92 x density x band lines; cone = downstream modules of the files, with the non-certificate module-minutes from the measured times, B8c; every ticket adds its owed generic pins to `Test/Axioms.lean`):

| ticket | files | band lines | edit | frozen | cone modules / lines | min | cert |
|---|---|---|---|---|---|---|---|
| T8 | `Step2Defs`, `LocalAvg1`, `LocalAvg2` (additive: L1) | 1,699 | 474 | 50 | 173 / 203,813 | 56 | yes |
| T7 | `Step2Events`, `DecayLoopA`, `DecayLoopB` | 4,779 | 707 | 3 | 101 / 126,905 | 32 | yes |
| T1 | `Step2Iterate`, `OptL2a`, `OptL2b` | 3,587 | 739 | 17 | 72 / 81,826 | 20 | yes |
| T2 | `EMn2Poly`, `EMn2Exp1`, `EMn2Exp2` | 3,850 | 363 | 1 | 16 / 20,533 | 5 | no |
| T3 | `NewKLK`, `Step2K2` | 1,382 | 278 | 1 | 99 / 116,127 | 33 | yes |
| T4s1 | `GridDuhamelN`, `AzumaProxyN`, `AzumaProxyN2` | 2,980 | 685 | 13 | 112 / 137,792 | 37 | yes |
| T4s2 | `GridGoodN`, `GridEnvelopeN`, `GridAssemblyN` | 3,381 | 584 | 3 | 44 / 57,028 | 12 | no |
| **T5s1** | `LoopGenN`, `HierarchyN` | 804 | 202 | 0 | 51 / 61,585 | 13 | no |
| T5s2 | `StepDecompN`, `LoopC2N`, `HierAlgebra`, `QVN`, `GridDriftN` | 4,611 | 1,227 | 18 | 98 / 113,529 | 27 | yes |
| T6 | `ContractPt`, `Contract` | 1,662 | 44 | 0 | 54 / 69,112 | 15 | no |
| U1s1 | `ZeroModeCalc`, `NewPQ`, `QopAlgebra`, `QopNorm` | 2,621 | 142 | 1 | 72 / 83,834 | 21 | yes |
| U1s2 | `IterationsA/B`, `QGridA/B` | 5,262 | 1,165 | 0 | 21 / 24,670 | 5 | no |
| U2 | `SEforLn1/2`, `B45`, `KDecay` | 5,862 | 1,087 | 1 | 116 / 144,808 | 40 | yes |
| U3s1 | `Step34Pins`, `Step34PinsP`, `Step3`, `Step4` (additive: L1) | 1,539 | 492 | 28 | 192 / 220,799 | 62 | yes |
| U3s2 | `NQBudget`, `NQEnd*`, `NQGood1/2`, `NQLin` (7) | 6,947 | 1,386 | 3 | 35 / 46,649 | 10 | no |
| U3s3 | `QBudgetA/B`, `QDriftA/B`, `QEndA`, `QEndB1`, `QEndGrid`, `QLevelsA/B`, `QProxy` (10) | 8,173 | 1,486 | 0 | 16 / 17,909 | 3 | no |
| U3s4 | `QtNonzero*`, `QtXiRoundLift` (6) | 5,774 | 1,010 | 1 | 11 / 8,978 | 1 | no |
| U4s1 | `Step5Kit`, `Step5Cases`, `Step5Kernel`, `TailtoTail*`, `WardII`, `NewKLKL` | 4,961 | 870 | 7 | 61 / 64,294 | 19 | yes |
| U4s2 | `IniTermI`, `IniTermII` | 5,451 | 799 | 2 | 6 / 7,084 | 3 | no |
| U4s3 | `DuhamelI/II`, `EtermsMid`, `LemDecCalELip`, `LemDecCalEPrec` | 7,527 | 1,425 | 3 | 22 / 22,946 | 7 | no |
| U6 | `Step5Pins` | 476 | 171 | 22 | 78 / 86,695 | 27 | yes |
| V1s1 | `Step6Kit`, `Step6Pins`, `ExpAvg`, `ExpDuhamel`, `ExpHier` | 3,817 | 1,169 | 22 | 45 / 40,907 | 9 | yes |
| V1s2 | `ExpEtermsA/B`, `ExpIniI`, `ExpIntEasy`, `ExpIntI` | 4,176 | 995 | 3 | 18 / 13,510 | 3 | no |
| V1s3 | `ExpIntII`, `ExpIntIQ`, `ExpWardI/II`, `QopDecay` | 3,708 | 697 | 3 | 22 / 21,575 | 4 | no |

Pairing: `<carrier> BA` starts after the last ST ticket of its carrier merged and its stage inputs (last column of the model table). Roles: ST side `prover`; `prover-hard` for the vocabulary tickets (T8, U3s1, U6, V1s1: 122 frozen declarations) and for rows with proxy f above 0.19 (T3, U4, V1); BA side `prover-hard`; `prover-max` for U5 and V2a.

**First tickets (the tripwire block).** Row 0 and T5s1 in parallel; neither reaches a certificate module. T5s1: sole writable `Induction/LoopGenN.lean`, `Induction/HierarchyN.lean`; content = probe 118-364 plus the band corollary; G1 checks: the merged statement texts of `loopGenN`, `stLoopGenNForm_holds`, `hierarchyN_holds` as `example : <old> := <old name>` (the probe's `recovers_loopGenN` is the same check in the other direction); BA instance: probe 385-388. Expected g 0.24, 0 lines moved. Row 0 is the first merge for every carrier-based ticket.

## 5. TV5: count and flag

BA ticket 46 in the wide count (T2378 = 45; K07 = T2380 = 47, K10 = T2381 = 48). Rows: 1 + 24 + 21 = **46 > 40**, so the stage is proposed as three sub-stages, each with its own opening REQ (the pins and carrier facts of its rows) and closing REQ (its endpoints proved, public, with compiled nonempty instances, and the shape check against the next sub-stage):

| sub-stage | rows | flag 1.5 x rows | content |
|---|---|---|---|
| T | 19 | 28.5 | row 0; Step 2 and the machinery: T1-T8 (10 ST, 8 BA) |
| U | 19 | 28.5 | Steps 3-5: U1-U6 (11 ST, 8 BA) |
| V | 8 | 12.0 | Step 6 and the main induction: V1 (3 ST, 2 BA), V2a, V2b, V3 |

With one stage the flag would be 69. Against the pilot: chain 40.6 tickets (lo 30.6, hi 57.0) where the pilot had 38.9 [37.5, 48.3] (+1.7: the 9% longer chain, 203 wrappers against 167, per-row densities); with 1.144: 46.4. The pilot's BA total moves from 141 to 143 (design) or 149 (1.144). The width is f and the BA-side twin term (14.7k lines, 10.6k of it f x S x 0.8, an upper bound at theorem granularity); at the measured f_sem = 0 of the tripwire block the chain is 37.6 (B9a).

## 6. TV6: the band side

**Files.** 96 of the 101 chain files change (g_f = 1.92 x density at least 0.01; unchanged: `ContractPt`, `QopNorm`, `QEndA`, `QProxy`, `PfStep5Alg`; median g_f 0.198, maximum 0.49 `Step6Pins`); `BA/FlowPins.lean` once (row 0); `Test/Axioms.lean` (owed generic pins, H23 b). No `Graph/` or `LW*` file is edited by this stage: the chain tickets leave `LWTermHolds`, `LWExpTerm6` and the `LWExpCert*` modules unedited, and the graph layer stays route I (its publishing tickets are stage L). B4, B8.

**G1.** 203 public declarations whose signature reads a band object and whose name occurs outside the chain, in 42 files (`Step2Defs` 49, `Step34Pins` 24, `Step5Pins` 22, `Step2Iterate` 16, `Step6Pins` 13, `StepDecompN` 12, `GridDuhamelN` 8, `Step5Kit` 5; the list is `T2379/frozen_names.json`). Each ticket's check file holds `example : <old> := <old name>` for the names of its files, compiled on `main` before release and on the branch by the auditor. Pins stay additive (the band definitions are not edited: `Iff.rfl` bridges as `bandFM_STLK`, `BA/FlowPins.lean:490`), so no proof that unfolds a band pin changes.

**Rebuild cost** (B8). Measured on three stage-K in-place merges (hub logs, per-module times): T2366 193 modules, 52 min wall (the certificate critical path `LWExpCertBS0` + `BS1` = 1533 + 1592 s; 1668 + 2039 s = 62 min in T2365), module-time sum 131 min of which the six certificate modules 72; T2365 124 min, 83 of them certificates; T2369 223 min under swap pressure. 20 of the 101 chain files reach a certificate module (`Step2Defs`, `Step34Pins`, `Step5Pins`, `Step6Pins`, `Step6Kit`, `ExpAvg`, `Step2Iterate`, `NewKLK`, `Step2K2`, `GridDuhamelN`, `HierAlgebra`, `Step2Events`, `DecayLoopA/B`, `ZeroModeCalc`, `NewPQ`, `QopAlgebra`, `QopNorm`, `KDecay`, `Step5Kit`): 12 of the 24 tickets (table above, last column) pay 52 to 62 min wall each (72 to 83 module-minutes of certificates) plus 9 to 62 module-minutes; the other 12 pay 1 to 15 module-minutes; row 0 about 8. Twelve certificate rebuilds are 10 to 12 hours of merge lane, serial (rule (A) builds the whole library). G2 (`sup 2051`): T2356, T2361, T2363, T2364, T2375 are merged (`docs/queue`), the UN band is closed (DECISIONS §188), MA-06b waits for the BA terminal; the in-place tickets take the lane after the critical path. Request: release the 12 certificate tickets one at a time, T8 and U3s1 (the vocabulary every BA reading needs) first.

**Private-helper coupling** (B8d). `EMn2Exp2` (T2) opens private names of `EMn2Exp1`, `EMn2Poly` (T2), `ContractPt` (T6: `card_ball_le`), `Evolution/PropTInf`, `Loop/KLWard` (`KLWard_mSigma_mul`: kept by the in-place K02); `DuhamelII` (U4) opens `DuhamelI` (U4) and `EMn2Exp2` (T2: `emn2Exp2_exists_CR`). A converting ticket keeps those private declarations (names, types) or converts the opening file in the same ticket: the cross-row pairs are T2-T6 and U4-T2; two statements reach outside the chain.

## 7. Decisions requested, paper-delta candidates, limits

1. **Route** (`sup 2051` Q3, G1-G3): confirm route G for the chain, route I for the graph layer; the tripwire is applied again at T5s1 and at the first class (t) file.
2. **Stage shape**: row 0 (carrier relocation, L1) before any carrier-based ticket; sub-stages T, U, V with the flags of §5 (28.5, 28.5, 12.0; 46 rows); each opening REQ carries the generic pins of its rows (T: the Step 2 family of the probe).
3. **Merge lane**: the 12 certificate tickets one at a time, 52 to 62 min each (§6).
4. **K-derived facts**: `BAKcalDecay` and the BA twin of `stKloop_lip` are rows U2 and U3, not stage-K targets; the K12 close REQ lists `STKwardgL`.
5. **Planning ratio**: apply 1.144 to the totals (46.4 central); no cap (DECISIONS §144).

Paper-delta candidates (temporary tags): `T2379a` `loopGenNOf` (probe 302-364) states `eq:mainStoflow` for every `m` with `0 < m.im` and every `g`; the paper states the band case `m = m(E)`; the block Anderson flow is `g = 0`, `m = m_BA`, and the paper does not state it (`7_8:1841` says the arguments extend). `T2379b` `BAStep2` (probe 95-96) is Lean's reading of the "unchanged steps" of `lem:main_ind_BA` (`7_8:1825-1841`).

Limits. g is a line measure from one compiled block and the pilot's two; the per-row g_r use the calibrated density and f = 0.14 (the theorem-granularity upper bound) for every row. The BA-side rows T4, T5 have no endpoint in the pilot's list of 43 (wiring 100 lines); the BA readings of the events (T7, T1) are the pilot's 11 obligations, not proved here. The facts census is a word match (an upper bound). Row sizes are estimates with measured end points, not measurements. V2a, V2b, V3 keep the T2205 sizes; V3 may be smaller. The BA data facts of rows T2, T3, U1, U3, U4, V1 are inside the f-term (10.6k lines) and the wiring (4.3k); the census (3,065 band lines x 0.8 = 2.5k) is smaller than either.
