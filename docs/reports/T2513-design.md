Verdict: PASS, no stop rule fired; option (A) is implementable as stated, so (B) need not go to Jun (probe 392 lines ≤ 400; this report ≤ 250 lines; no merged file changed, `git diff --stat main...t/T2513 -- RBM3D` is the probe only; `BAEnd_BUnivL 3` needs only `UNL32` and `d = 3` pins; D2 has no "uses another dimension" row). (a) D1: eight filtered successors `T2513_UN…D` (probe :38-86), each equal to its merged text after deleting the filter (`statdiff.py`, section 0); band recovery at `Dm = fun _ => True` by `Iff` (:91-116); BA at `Dm = (· = 3)`. (b) D2: all 102 hits of the ticket's grep are placed (0 unplaced), and 27 further declarations of a by-name grep; every statement of the Q2 list is "per-`d`: mechanical copy", none "uses another dimension"; the producers and `baBUniv_of_rows` are compiled with the filter (:120-188, :266-293). (c) D3: `T2513_baBUniv_of_rowsD` (:273) and `T2513_n2_three` (:294: `BAEnd_BUnivL 3` from `UNL32` and `d = 3` pins, no `∀ d` BA input, no regime-(iii) hypothesis); 24 theorems, standard three axioms; six instances at the class sequence `S0` (:322, :330, :345, :361, :370, :381). (d) D4: implementation central 469 lines (calibrated 479-626) in three files; N2 plus implementation 700-920 (hi-case 1,189) ≪ 1,950: inside N2; the vocabulary file G1 must be merged before the first of M1's `d = 3` bridge, M1 row b and M3 (§4 order); no new row; M/N forecast ≈ 12 (11-14) unchanged; no REQ before N2. (e) D5, D6: §5, §6 (four per-`d` cores; final signatures `UNL32 → BAEnd_BUnivL 3`, `UNL32 → BAThm27L 3`).

# T2513 design: MN-D3, the `d = 3` form of the UN-side BA assembly (option (A): dimension-filtered successors)
Written Thu Oct 15 08:03:25 UTC 2026 (`date -u`) by the stage-1b prover (claude-sonnet-5-5) on branch `t/T2513` (base `main` a082fcfe; `main` has since merged T2511 row b, c536c603, whose `unMLOutBA_three : Univ.UNMLOutBA 3` is `BA/MainIndTermBA.lean:47`, read with `git show main:`). Probe `RBM3D/Probe/T2513Pins.lean`, 392 lines (cap 400), never merged; section (a) of `docs/reports/T2513-prove.md` is not edited (one correction in its (a′)). `X:N` = `RBM3D/X.lean:N` at the checkout; `:N` alone = a probe line; `T2449:N` = `t/T2449:RBM3D/Probe/T2449Pins.lean:N` (commit 921369b2, read with `git show`). Scripts (scratchpad `T2513/`) and their verbatim outputs are in section 0; every `file:line` citation below was checked by `cite_lines.py` (last line of section 0).

## 0. Script output
```
$ zsh probe_check.sh                                              # cwd = RBM3D-wt/T2513
lines:                392
lake env lean RBM3D/Probe/T2513Pins.lean: exit=0 output lines=0
lake build RBM3D.Probe.T2513Pins: exit=0 last line: Build completed successfully (4190 jobs)., warning/error lines in the probe file: 0
forbidden (sorry|admit|axiom|native_decide|inductive|structure): 0; STStep5IIIgL: 0
defs: 22, theorems: 24, examples: 6
#print axioms, every probe theorem: 24 of 24 with exactly [propext, Classical.choice, Quot.sound]; other lines: 0
$ lake env lean band_axioms.lean   # import RBM3D.Main.BandTerminal, RBM3D.Main.BUnivHolds, on t/T2513
band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --stat main...t/T2513 -- RBM3D
 RBM3D/Probe/T2513Pins.lean | 348 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 348 insertions(+)
$ lake env lean docs/tickets/checks/T2513-check.lean   # acceptance: the check compiles
exit=0 error lines: 0
$ grep -rn 'T2513_' RBM3D | grep -v Probe/T2513Pins.lean | wc -l   -> 0
$ git grep -l T2513_ over every refs/heads/t/* except t/T2513 (RBM3D/)   -> 0 files
$ C1 scan, generic texts (probe :36-88 and :118-190) for BA/band tokens   -> 0 hits
$ lake env lean scan_probe.lean   # RBM.Audit.scanPremises on the probe (registry rule of Test/Axioms.lean): Props assumed by a probe theorem and concluded by none
scanPremises over the probe: 8 premises assumed by a probe theorem and concluded by none: [RBM.Univ.T2513_BAEnd_locSCL, RBM.Univ.T2513_TrLocalInitCore, RBM.Univ.T2513_TrLocalCore, RBM.Univ.T2513_UNEMCTE2RowkD, RBM.Univ.T2513_UNOURowBAD, RBM.Univ.T2513_UNJakUywRowBAD, RBM.Univ.T2513_UNEMCTE2RowBAD, RBM.Univ.T2513_UNClaimRowBAD] 
$ python3 -I statdiff.py            # filtered text vs merged text after deleting the filter
UNQuek                               merged PinsK.lean:398-403  probe :38-43  identical after the filter map: True
UNLocAvgk                            merged PinsK.lean:406-414  probe :45-53  identical after the filter map: True
UNOUClaimsk                          merged PinsK.lean:421-423  probe :55-57  identical after the filter map: True
UNOURowk                             merged PinsK.lean:426-426  probe :59-60  identical after the filter map: True
UNEMCTE2Rowk                         merged PinsK.lean:429-432  probe :62-65  identical after the filter map: True
UNJakUywRowk                         merged PinsK.lean:435-439  probe :67-71  identical after the filter map: True
UNClaimRowk                          merged PinsK.lean:442-449  probe :73-80  identical after the filter map: True
UNG1Rowk                             merged OUInterfaceK.lean:101-105  probe :82-86  identical after the filter map: True
un_claimAll_of_rowsk (stmt+proof)    merged PinsK.lean:454-466  probe :120-132  identical after the filter map: True
unClaimRowk (stmt+proof)             merged UnivMain.lean:471-477  probe :134-140  identical after the filter map: True
jakUywRowk (stmt+proof)              merged EMCTE2BA.lean:629-637  probe :142-150  identical after the filter map: True
ouRowk_of_pins (stmt+proof)          merged OUInterfaceK.lean:292-298  probe :152-158  identical after the filter map: True
g1Rowk_of_inputsG (stmt+proof)       merged RandomLayerBG.lean:399-427  probe :160-188  identical after the filter map: True
ALL IDENTICAL: True
$ python3 -I d2use.py               # where each `forall d` input of a merged proof is used, and at which dimension argument
un_claimAll_of_rowsk                       454-466:  2 sites at lines 462,463 of {rE rJ}; dimension argument: ['d']
unClaimRowk                                471-477:  2 sites at lines 472,474 of {h}; dimension argument: ['d']
jakUywRowk                                 629-637:  2 sites at lines 631,632 of {hclaims}; dimension argument: ['d']
ouRowk_of_pins                             292-298:  4 sites at lines 295,297,298 of {hprof r1 r2b}; dimension argument: ['d']
g1Rowk_of_inputsG                          399-427: 14 sites at lines 418,420,421,424,426,427 of {hC hT1 hT1' hT2 hT3 hT4 hT5}; dimension argument: ['d']
baBUniv_of_rows                            367-379:  5 sites at lines 372,374,375,378 of {rD rN rT rT0 un_claimAll_of_rowsBA}; dimension argument: ['d']
UNQueBA_of_BAEnd_QUEL                      357-359:  1 sites at lines 359 of {h}; dimension argument: ['d']
UNLocAvgBA_of_BAEnd_locSCL (t/T2449 probe) 220-229:  1 sites at lines 222 of {h}; dimension argument: ['d']
UNOUQUEk_zero_of_UNQuek                    494-506:  1 sites at lines 502 of {hQ}; dimension argument: ['d']
$ grep -nE '∀ d[ :,]' RBM3D/BA/UNPins.lean RBM3D/BA/EMCTE2BA.lean RBM3D/BA/RandomLayerBGBA.lean RBM3D/Universality/PinsK.lean RBM3D/Universality/OUInterfaceK.lean RBM3D/Universality/GUEPhase/RandomLayerBG.lean RBM3D/Universality/PinsC2.lean | wc -l   -> 102 hits
$ python3 -I d2place.py --by-class   # each hit placed by its enclosing declaration (docstring lines belong to the next declaration)
B  band side: Dm = True instance (unchanged) [7 hits]
    PinsK: 561,583,584,585 ; OUInterfaceK: 394,412,429
I  merged instance (unchanged); filtered: probe examples [30 hits]
    UNPins: 1027,1041,1053,1066,1238 ; EMCTE2BA: 943,953,961,962 ; RandomLayerBGBA: 201,202,203,204,205,206,207,210 ; PinsK: 633,634,643,644,656,658 ; OUInterfaceK: 459,460,474,476,482 ; RandomLayerBG: 509,512
K  kind hypothesis (forall d over the kind, not an input) [3 hits]
    EMCTE2BA: 394,402,418
M  per-d, mechanical copy: compiled twin in the probe [23 hits]
    UNPins: 143,144,357,370 ; EMCTE2BA: 629 ; PinsK: 454,457,470,472 ; OUInterfaceK: 292,293 ; RandomLayerBG: 400,401,402,403,404,406,407,408,409,410,411,412
P  pin text with its own forall-d: D1 successor [19 hits]
    UNPins: 124 ; PinsK: 398,399,406,407,421,422,426,429,430,435,436,442,443,448 ; OUInterfaceK: 99,100,101,103
R  row with own forall-d, no BA-input premise [11 hits]
    UNPins: 160,191 ; PinsK: 205,276,294 ; OUInterfaceK: 109,110 ; PinsC2: 91,108,863,1346
T  owed TrLocal row (M1 b): D5 per-d core [2 hits]
    UNPins: 170,182
U  per-d already / reused unchanged by a compiled twin [7 hits]
    EMCTE2BA: 442,457,476,477,553,554 ; PinsK: 494
total hits 102  placed 102  UNPLACED 0
$ python3 -I d2place.py --second     # the by-name grep (UNLocAvgBA|UNQueBA|UNLocAvgk|UNQuek|UNOUClaimsk|UNOURowBA|... over RBM3D/, minus Probe/Test), declarations not in the first grep
supplementary grep by name (declarations not in the first grep): 27 declarations
  by class: B 4, D 1, I 10, M 2, P 5, U 5
$ python3 -I price.py
file                                                 probe decl  inst central      x lo      x hi  placement
G1  Universality/PinsKD (vocabulary + Iff)              66   18    16     166       176       227  before its first consumer (section 4 order)
G2  GUEPhase/RandomLayerBGD (chain)                     56    4    20     118       125       162  N2
BA  BA/UNBUniv (BA readings, assembly, instances)       56    8    75     185       178       237  N2
implementation total                                                      469       479       626
  inside the owner row, already in its price: M1 a core (locAvg bridge)     13 probe lines
  inside the owner row, already in its price: M3 core (QUE bridge)           6 probe lines
  inside the owner row, already in its price: M1 b cores (TrLocal)          14 probe lines
N2 (T2449 200 / 230 / 440; BA leaves x0.96-1.28): 221-294 central, hi 563
N2 + G2 + BA leaf: 524-693 (hi-case 962); with G1 also in N2: 700-920 (hi-case 1189); stop line 1950, ratio 1.64
probe totals: lines 392, instance lines (6 examples) 55
$ python3 -I cite_lines.py          # every file:line citation of this report against the file text
citations checked: 125, mismatches: 0
```

## 1. D1: the filter vocabulary (probe :36-116; the texts become binding after the 1a-audit)
The filter is `Dm : ℕ → Prop` (not `D`: the merged bodies bind the exponent `D : ℝ`). Each successor is the merged text with `(Dm : ℕ → Prop)` added first and `Dm d →` inserted before `3 ≤ d →`, quantifier order `∀ d : ℕ, Dm d → 3 ≤ d → …`; the two rows that consume the claim take the filtered claim (`UNOURowkD`, `UNJakUywRowkD`: `T2513_UNOUClaimskD Dm K`). New names only; `statdiff.py`: 8 of 8 identical to the merged text after deleting the filter. Proposed final names: the probe names without the prefix `T2513_` (`UNQuekD`, `UNLocAvgkD`, `UNOUClaimskD`, `UNOURowkD`, `UNEMCTE2RowkD`, `UNJakUywRowkD`, `UNClaimRowkD`, `UNG1RowkD`; BA readings `UNLocAvgBAD`, `UNQueBAD`, …).
| merged (X:N) | successor (probe line) | extra binders | `Iff` at `Dm = fun _ => True` |
|---|---|---|---|
| `UNQuek` PinsK:398 | `T2513_UNQuekD` :38 | `(K : ∀ d, UNKind d)` | :91 |
| `UNLocAvgk` PinsK:406 | `T2513_UNLocAvgkD` :45 | `(K)` | :93 |
| `UNOUClaimsk` PinsK:421 | `T2513_UNOUClaimskD` :55 | `(K)` | :95 |
| `UNOURowk` PinsK:426 | `T2513_UNOURowkD` :59 | `(K) (ML Loc Que : Prop)` | :97 |
| `UNEMCTE2Rowk` PinsK:429 | `T2513_UNEMCTE2RowkD` :62 | `(K)` | :100 |
| `UNJakUywRowk` PinsK:435 | `T2513_UNJakUywRowkD` :67 | `(K) (Loc : Prop)` | :102 |
| `UNClaimRowk` PinsK:442 | `T2513_UNClaimRowkD` :73 | `(K)` (hypothesis and conclusion filtered) | :106 |
| `UNG1Rowk` OUInterfaceK:101 | `T2513_UNG1RowkD` :82 | `(K) (P) (ML Loc Que : Prop)` | :108 |
- **BA readings** (new names, probe): `T2513_UNLocAvgBAD Dm := T2513_UNLocAvgkD Dm (fun d => UNKind.ba d)` (:217), `T2513_UNQueBAD` (:218), `T2513_UNOURowBAD Dm` with `ML := ∀ d, Dm d → UNMLOutBA d` (:260), `…EMCTE2RowBAD`, `…JakUywRowBAD`, `…ClaimRowBAD` (:262-264). BA uses `Dm = (· = 3)`. "`UNLocAvg` at `d`" (MNO-C3) is `Dm = (· = d)`: `T2513_UNLocAvgkD (· = d) K`; the merged reading gives it by `fun h d' _ => h d'` (:253).
- **Band**: `Dm = fun _ => True`: the eight generic `Iff`s (:91-110) and, at `UNKind.band`, `T2513_band_locAvg` (:113, with merged `UNLocAvgk_band` PinsK:554) and `T2513_band_ouRow` (:115, with `UNOURowk_band`): no band file touched; `band_terminal`, `bUniv_holds` print the standard axioms on `t/T2513` (section 0); the merged modules are byte-identical to `main`'s at the base (diff stat), and the same two lines are in `docs/reports/T2377-audit.md:36`, `T2371-audit.md:44`.
- **Not filtered** (no input at another dimension): `UNG2bRowk` (OUInterfaceK:109; `g2bRowk` QUEFlow:898 proves it for every `K P`), `UNOUProfRowk` (per kind), `UNDensBARow'` (`unDensBARow'_holds` MReg:333), `UNNormBARow` (UNPins:190), `UNCoreC''` (`unCoreC''_holds` UnivMain:652), `UNGreenCorrAllC` (`greenCorrAllC` GreenCorr:956), the kind hypotheses `UNBulkWindowk`, `UNBadBoundk`, `UNBad2Boundk` (EMCTE2BA:394-418). `T2513_UNEMCTE2RowkD` is optional for BA: the probe feeds it from the unfiltered `unEMCTE2RowBA_holds` by `fun d _ hd => …` (:310); it stays for generic kinds.
- **Registry** (`Test/Axioms.lean`, not counted by `wc`): the scan (`scanPremises`, section 0) lists a `Prop` that some theorem assumes and none concludes; on the probe that is `T2513_BAEnd_locSCL` (M1 a's pin), the two cores (M1 b's pins), `T2513_UNEMCTE2RowkD` and the four BA row readings: so G1, G2 and N2 add at most 5 structural lines (as `UNQuek` :390, `UNLocAvgk` :391), none if `UNEMCTE2RowkD` is dropped and the BA readings are written inline. The owner comments of `UNLocAvgBA` :178 and `UNOURowBA` :179 are rewritten (closing (vii): owed only at `d > 3`, "out of scope: Jun decision B, BA Thm 2.7 at d = 3 (D723; DECISIONS §316)"); `UNTrLocalBARow` :182 and `UNTrLocalInitBARow'` :183 close at M1 row b by the corollaries :252-255.

## 2. D2 (MNO-C2): every merged statement of the Q2 list, one row; no "uses another dimension"
| statement (X:N) | class | evidence (script output in section 0) |
|---|---|---|
| `UNTrLocalBARow` UNPins:169, `UNTrLocalInitBARow'` :181 (owed; M1 row b) | per-`d`: mechanical copy (D5 cores) | the statements take the all-`d` `UNLocAvgBA` as hypothesis and conclude per `d`; no proof is merged (owed), but its band twin `unTrLocalBandRow` (BUnivHolds:205) applies `hLoc d hd …` once, at its own `d` (:207); the dilation of the Init row changes `sz`, not `d` (`UNLocAvgk` binds `sz` inside `d`); cores :242, :247 and their one-line corollaries :252-255 compile |
| `unJakUywRowBA_holds` EMCTE2BA:766 = `jakUywRowk` :629-640 | per-`d`: mechanical copy | `Loc` is discarded (`_hloc`, :631); `UNOUClaimsk K` is read at `d hd 𝔠 𝔡 sz hadm` (:632); twin `T2513_jakUywRowkD` :142-150 compiles; `unJak_of_ouClaimsk` (:476) is reused unchanged |
| `g1Rowk_of_inputsG` RandomLayerBG:399-425 and its BA instance RandomLayerBGBA:200-212 | per-`d`: mechanical copy | the seven inputs are applied at `d` only (:418, 420, 421, 424, 426, 427; `hT5 hML d hd` :418); twin :160-188; the BA instance's one `ML` line `fun hML' d hd => ba_mlout d hd (hML' d)` (:212) becomes `fun hML' d hdd hd => ba_mlout d hd (hML' d hdd)` (:308) |
| `ouRowk_of_pins` OUInterfaceK:292-300 | per-`d`: mechanical copy | `r1 hML hLoc hQ d hd`, `r2b d hd (hprof d hd)` (:297-298); twin :152-158 |
| `un_claimAll_of_rowsBA` UNPins:142, `baBUniv_of_rows` :367-370, `UNQueBA_of_BAEnd_QUEL` :357, bridge `UNLocAvgBA_of_BAEnd_locSCL` T2449:220 | per-`d`: mechanical copy | uses at :372-378, :359, T2449:222 (section 0, `d2use.py`: dimension argument `d` only); twins :266, :273, cores :235, :221; generic `un_claimAll_of_rowsk` PinsK:454 and `unClaimRowk` UnivMain:471: twins :120, :134 |
| `inst_*` UNPins:1020-1070 (`inst_UNOURowBA` :1027, `inst_UNJakUywRowBA` :1041, `inst_claimAll_ba` :1052, `inst_univ_ba` :1063) | merged instances of the merged `∀ d` texts, unchanged | filtered instances: the six examples :322-381; N2 adds the `inst_*` twins (in its price, §4) |
| `UNCoreC''` PinsC2:106-113 | per `d` (own quantifier), proved | `unCoreC''_holds` UnivMain:652, read per `d` at :273 |
Grep placement (section 0): first grep 102 hits, 102 placed: P 19 (pin texts with their own `∀ d`: the D1 successors), M 23 (compiled twins), U 7 (per-`d` already or reused unchanged: `unJak_of_ouClaimsk`, `unUyw_of_ouClaimsk`, `EMCTE2BA_hbad_of_K`, `_hbad2_of_K`, `UNOUQUEk_zero_of_UNQuek`, whose one use is `hQ d hd`, PinsK:502), K 3, R 11, T 2, I 30, B 7. By-name grep: 27 more declarations (B 4, D 1, I 10, M 2 = `unJakUywRowBA_holds`, `unClaimRowBA_holds` (BandTerminal:88, the unfiltered row; N2 uses the twin `T2513_unClaimRowkD`), P 5 = the BA readings, U 5). **Result: no "uses another dimension" row; MNO-C2's REQ trigger is not met by D2.**

## 3. D3: the probe (392 lines; sections: pins :36-86, band `Iff`s :89-116, filtered chain :118-189, D5 :191-256, BA assembly :258-314, instances :316-388)
- **Chain** (merged proofs, `Dm d` threaded through, identical after the filter map): `un_claimAll_of_rowskD` :120, `unClaimRowkD` :134, `jakUywRowkD` :142, `ouRowk_of_pinsD` :152 (7 lines) and `g1Rowk_of_inputsGD` :160 (29 lines; private helpers by `open private … from`, :26): the last two together 36 lines (cap 120). All seven inputs of `g1Rowk_of_inputsGD` and `hprof` are filtered, so C3's and C5's pins may be proved at `d = 3` only.
- **`T2513_baBUniv_of_rowsD (Dm) … (d) (hD : Dm d) : BAEnd_BUnivL d`** (:273): hypotheses `UNCoreC''`, `UNL32`, `UNGUELocal`, `UNGreenCorrAllC`, `UNDensBARow'`, the two TrLocal cores (D5), `UNNormBARow`, the four filtered BA rows, `hML : ∀ d, Dm d → UNMLOutBA d`, filtered `hLoc`, `hQ`. It is the merged `baBUniv_of_rows` (UNPins:367) with the BA rows and the three inputs filtered and `rT0`, `rT` replaced by the cores.
- **`T2513_n2_three`** (:294), `Dm = (· = 3)`: `BAEnd_BUnivL 3` from `h32 : UNL32` and the `d = 3` pins: `UNMLOutBA 3` (V; merged as `unMLOutBA_three`), `T2513_BAEnd_locSCL 3` (M1; copy of T2449:158-198, :195-215), `BAEnd_QUEL 3` (M3), the two cores (M1 b), `UNNormBARow` (N2), `UNOUProfRowk (ba 3)`, `RBG_ProfComp` (C3), `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` (C5). Inside: `unCoreC''_holds`, `un_gueLocal_of_tail gueSchurTail`, `greenCorrAllC`, `unDensBARow'_holds`, `T2513_unClaimRowkD`, `unEMCTE2RowBA_holds`, `T2513_jakUywRowkD`, `g2bRowk`, the bridges `T2513_locAvg_core 3`, `T2513_que_core 3`. No `∀ d` form of `UNMLOutBA`/`UNLocAvgBA`/`UNQueBA`, no regime-(iii) hypothesis (grep: 0); the `∀ d` hypotheses left are `UNL32` (borrowed, Pins:281), `UNNormBARow` and the two cores (own quantifier; no input at another dimension). Closing condition (vi) holds for this assembly. Stop rule "needs a hypothesis beyond `UNL32` and per-`d = 3` inputs": not fired.
- **Instances** (six, nonempty, `d = 3`, merged class sequence `S0` of `UNPins` §8 (`(L, g) = (4, 3/10)`), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ_*`, `E_*` in the bulk (`S0_adm`, `S0_bulk`), `k = 1`, `E' = 0`, `𝒪 = bump`): :322 `T2513_un_claimAll_of_rowsBAD` (with `T2513_unClaimRowkD` as `rC`; `UNClaimAllC S0 (UNModelC.ba S0) E_*`); :330 `T2513_n2_three` (`UNUnivDilAt S0 (UNModel.ba S0) …`); :345 `T2513_g1Rowk_of_inputsGD` (`UNOULLk`, `UNOUEq747k` at `S0`); :361 `T2513_ouRowk_of_pinsD` (`UNOUQUEk`, `UNOUDiagk` at `S0`); :370 `T2513_baBUniv_of_rowsD`; :381 `T2513_jakUywRowkD` (`UNJakk`, `UNUywk` at `S0`, `n_f = 2`). Every deterministic hypothesis is discharged (`3 ≤ 3`, `3 = 3`, admissibility, bulk); the unproved pins of other gates stay hypotheses.

## 4. D4: price and placement (bottom-up, `price.py`, section 0)
Rule: central = probe lines of the declarations + 3 docstring lines per declaration + 30 header + instance allowance (G1 16, G2 20, BA: the 55 compiled instance lines + 20 for the `inst_*` twins); calibration generic ×1.06-1.37, BA leaves ×0.96-1.28 (DECISIONS §325-§334, as the ticket).
| file (new) | content (probe lines) | central | calibrated | home |
|---|---|---|---|---|
| G1 `Universality/PinsKD` | 8 pins, 8 `…_true`, 2 band `Iff` (:38-116; 66 lines, 18 declarations) | 166 | 176-227 | before M1 row b (below) |
| G2 `Universality/GUEPhase/RandomLayerBGD` | `un_claimAll_of_rowskD`, `unClaimRowkD`, `ouRowk_of_pinsD`, `g1Rowk_of_inputsGD` (56 lines; imports `RandomLayerBG`, `UnivMain`) | 118 | 125-162 | N2 |
| BA leaf, in N2's `BA/UNBUniv` | `jakUywRowkD` (imports `BA/EMCTE2BA`, so a BA leaf), 4 BA rows, `un_claimAll_of_rowsBAD`, `baBUniv_of_rowsD`, `n2_three` (56 lines) + the six instances (:322-387, 55 lines of code) | 185 | 178-237 | N2 |
| total | | 469 | 479-626 | |
Already in the owner rows' prices: M1's `d = 3` bridge :217, :221-232 (13 lines), M3's bridge :218, :235-239 (6), M1 b's cores :242-255 (14); the `BAEnd_locSCL` copy :195-215 is M1 a's own pin file (`BA/MAPins`).
- **N2**: T2449 200 / 230 / 440 × 0.96-1.28 = 221-294 (hi 563). N2 + G2 + BA leaf: 524-693 (hi-case 962); with G1 also in N2: 700-920 (hi-case 1,189, ratio to the stop line 1,950: 1.64). **Placement: inside N2** (the ticket's rule); no REQ before N2 (no D2 "uses another dimension" row, total ≤ 1,950). The decision is robust: the hi-case stays 1.64 times below the line.
- **Order (the one consequence)**: G1 is read by M1's `d = 3` bridge (:221), M1 row b's cores (:242, :247) and M3's bridge (:235), all before N2; T2514 (M1) is already released (CONTROL.md, header of 07:22 UTC and item 482), so the dispatcher chooses. (α, recommended) G1 as the first writable file of M1 row b, the `d = 3` bridge (13 lines, :217, :221-232, a corollary of `baEnd_locSCL_three` and G1) moving there if row a does not need it; no new row (M1 b's 1a reprices, +176-227, MNO-C4). (β) G1 as a small stand-alone generic row before the first consumer: M/N forecast ≈ 13 (12-15; a REQ only if M3, C3, C5 also split). (γ) G1 stays in N2; M1 b and M3 state their cores with the explicit body of the filtered pin as a private def, which N2 closes by `Iff.rfl` (about +10 lines each; not compiled here).

## 5. D5 (MNO-C3): the per-`d` cores (probe :221-255; each compiles; both consumer forms in one line)
```
def T2513_TrLocalCore : Prop :=
  ∀ d : ℕ, 3 ≤ d → T2513_UNLocAvgBAD (· = d) → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocal sz (UNModelC.ba sz).toUNModel (fun n => BAm d (sz.L n) (sz.lam n)) E δ
```
`T2513_TrLocalInitCore` (:247) is the same with conclusion `UNTrLocalInit' sz (UNModelC.ba sz) (fun n => BAm d (sz.L n) (sz.lam n)) E δ`. The `d = 3` form is the core at `d := 3` (`T2513_UNLocAvgBAD (· = 3) → …`); the merged `∀ d` texts follow by
```
theorem T2513_UNTrLocalBARow_of_core (h : T2513_TrLocalCore) : UNTrLocalBARow :=
  fun hLoc d hd => h d hd (fun d' _ => hLoc d')
theorem T2513_UNTrLocalInitBARow'_of_core (h : T2513_TrLocalInitCore) : UNTrLocalInitBARow' :=
  fun hLoc d hd => h d hd (fun d' _ => hLoc d')
```
M1's and M3's bridges (the T2449 probe text at `:220`, `UNQueBA_of_BAEnd_QUEL` UNPins:357; core, then the merged `∀ d` text in one line):
```
theorem T2513_locAvg_core (d : ℕ) (h : T2513_BAEnd_locSCL d) : T2513_UNLocAvgBAD (· = d) := by
theorem T2513_UNLocAvgBA_of_BAEnd_locSCL (h : ∀ d : ℕ, T2513_BAEnd_locSCL d) : UNLocAvgBA :=
  fun d hd => T2513_locAvg_core d (h d) d rfl hd
theorem T2513_que_core (d : ℕ) (h : BAEnd_QUEL d) : T2513_UNQueBAD (· = d) := by
theorem T2513_UNQueBA_of_BAEnd_QUEL (h : ∀ d : ℕ, BAEnd_QUEL d) : UNQueBA := fun d hd => T2513_que_core d (h d) d rfl hd
```

## 6. D6 (closing condition (vi)): final public signatures
```
theorem baEnd_BUnivL_three : UNL32 → BAEnd_BUnivL 3
theorem baThm27L_three : UNL32 → BAThm27L 3
```
Owner N2 (Q4 (b)); `BAThm27L d := BAEnd_decolL d ∧ BAEnd_locSCL d ∧ BAEnd_QUEL d ∧ BAEnd_BUnivL d ∧ BAEnd_QDiffL d` (T2449:217; M1 row a publishes it), proof shape `fun h32 => ⟨baEnd_decolL_three, baEnd_locSCL_three, baEnd_QUEL_three, baEnd_BUnivL_three h32, baEnd_QDiffL_three⟩`. The compiled core of the first is `T2513_n2_three` (:294-301), whose hypotheses besides `h32` are exactly the `d = 3` pins of V, M1, M1 b, M3, N2, C3, C5 (§3), each replaced by its owner's merged theorem at N2. No `STStep5IIIgL`, no `∀ d` form of `UNMLOutBA`/`UNLocAvgBA`/`UNQueBA`; the only external hypothesis is `UNL32`. The `d > 3` forms stay in hypothesis form, now per dimension: `T2513_baBUniv_of_rowsD (· = d)` with `UNMLOutBA d` from `baMainIndFamTL_any` (T2511-check:213-215) by `unMLOutBA_of_famStep` under `STStep5IIIgL d`; registry wording as §316 (closing (vii)).

## 7. Paper deltas
None new. D723 (BA Thm 2.7 at `d = 3` only, DECISIONS §316) covers the restriction; the filter is Lean-internal (no `T2513a` candidate).

## 8. The M/N forecast after this gate (MNO-C4)
Used 4 / 15 with this gate (T2475, T2477, T2476, T2513). Remaining rows (MN-plan §1): M1 (a, b), M2, M3, C3, C4, C5, N2 = 7 → 11 with M1 as one row, 12 with its pre-signed split; this gate adds no row (the implementation sits in N2, G1 before its first consumer: §4 option α), so the forecast stays ≈ 12 (11-14), below 15: no REQ. Option β would put it at ≈ 13 (12-15).

## 9. Findings, stop rules
- F1: the merged `∀ d` readings `UNLocAvgBA`, `UNOURowBA` (and `baBUniv_of_rows`, `un_claimAll_of_rowsBA`, `inst_*`) stay on `main` unedited and true, but are no longer on the `d = 3` terminal; for BA they can be discharged at `d > 3` only under regime (iii) (registry wording, §1).
- F2: `UNClaimRowk`'s hypothesis ranges over all `d`, so the proved unfiltered `unClaimRowBA_holds` (BandTerminal:88) cannot feed the filtered chain; `T2513_unClaimRowkD` (:134) can.
- F3: `T2513_BAEnd_locSCL` copies T2449:158-198 (unmerged, commit 921369b2: `BAGz` :158, `BAMz` :161, `BAendDom` :169, `BAlocBad1z` :172, `BAlocBad2z` :176, `BAEnd_locSCL` :192): re-check it against M1 row a's `BA/MAPins` at its merge, as for `T2503v1_`.
- F4: `hML : UNMLOutBA 3` has the exact type of the merged `unMLOutBA_three` (`BA/MainIndTermBA.lean:47`), so N2 supplies it by name.
- Stop rules (ticket): no merged file changes (diff stat, section 0): not fired. Probe 392 ≤ 400, report ≤ 250: not fired. `BAEnd_BUnivL 3` needs only `UNL32` and `d = 3` inputs: not fired. UBA-C1 (size/kernel comparison): n/a, because nothing here compares sizes or kernels.

## Fill-in table (stage-1a deliverables of T2513; line = line of this report)
| item | where |
|---|---|
| First line: stop rules, verdicts, D4 price and placement | line 1 |
| D1 filter vocabulary: names, quantifier order, band `Iff`, BA `Dm = (· = 3)` | 91-107; probe :36-116 |
| D1 rule "new names only; no merged statement edited" (MNO-C1) | 91-107; section 0 diff stat, `statdiff.py` |
| D1 `#print axioms band_terminal` / `bUniv_holds` on `t/T2513` equal to `main`'s | section 0 (16); §1 band bullet |
| D2 one row per statement of the Q2 list (`UNTrLocalBARow`, `UNTrLocalInitBARow'`, `unJakUywRowBA_holds`, `g1Rowk_of_inputsG` + BA instance, `ouRowk_of_pins`, `un_claimAll_of_rowsBA`, `baBUniv_of_rows`, bridges, `inst_*`) | 108-119 |
| D2 further statements: the grep pasted, each hit placed | section 0 (53-71); §2 last paragraph |
| D2 any "uses another dimension" row (REQ trigger) | none (108-119) |
| D3 probe: pins, filtered `ouRowk_of_pins` and `g1Rowk_of_inputsG` (≤ 120 lines together: 36), `baBUniv_of_rows` at `(· = 3)`, two band `Iff`s | 120-125; probe :38, :152-188, :273, :294, :113-115 |
| D3 `#print axioms` of each probe theorem, no `sorry` | section 0 (8-14) |
| D3 compiled nonempty instance | 120-125; probe :322, :330, :345, :361, :370, :381 |
| D4 bottom-up price (generic ×1.06-1.37, BA ×0.96-1.28) | 126-137 |
| D4 placement (inside N2 or own row), total vs 1,950 | 126-137 |
| D5 per-`d` cores for M1 b (two), M1's bridge, M3's bridge | 138-161; probe :221-255 |
| D6 final signatures of `BAThm27L 3`, `BAEnd_BUnivL 3`, quoted | 162-168 |
| Report (7) paper deltas | 169-171 |
| Report (8) M/N forecast (MNO-C4) | 172-174 |
| Rule C1 (generic texts without BA/band vocabulary) | section 0 (25): 0 hits in the pin texts :36-88 and the chain :118-190; the two band `Iff`s (:113-116) and the BA readings are instances in their own sections, as `PinsK` §5 |
| Rule X1-C4 (no restated merged text beyond the filtered successors) | the only non-successor copy is `T2513_BAEnd_locSCL` and its vocabulary (:195-215), unmerged T2449 text (F3) |
| Rule UBA-C1 | n/a, because no size or kernel comparison is made here |
| Acceptance: check compiles; probe `lake env lean` exit 0; standard axioms; no `sorry`/`admit`/`axiom`; `git diff` only the probe | section 0 (15-22) |
| Stop rules (ticket) | 175-181 |
