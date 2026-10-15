Auditor model: claude-opus-5-5
# T2513 audit (round 1): MN-D3 design gate, option (A) dimension-filtered successors
Written Thu Oct 15 08:11:36 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2513-audit1`, detached at `t/T2513` a6d9966e (base `main` a082fcfe).
Inputs: ticket `docs/tickets/T2513.md`; design `docs/reports/T2513-design.md` (205 lines, branch); probe `RBM3D/Probe/T2513Pins.lean` (392 lines, branch only, never merged); prove report section (a).
Scratch files (uncommitted): scratchpad `T2513/` (`audit_scratch.lean`, `gen_rfl.py`, `place.py`, `price_audit.py`, `band.lean`, `ml3.lean`).

**Verdict: PASS** (report-only design gate; merge `docs/reports/T2513-design.md` only). No dispatcher sign-off needed.

## 1. Build, axioms, hygiene, diff (acceptance list)
```
$ lake build RBM3D.Probe.T2513Pins            # audit worktree
✔ [4190/4190] Built RBM3D.Probe.T2513Pins (6.2s)
Build completed successfully (4190 jobs).      error lines: 0; warning lines in T2513Pins: 0
$ lake env lean RBM3D/Probe/T2513Pins.lean; echo exit=$?
exit=0                                         (no output)
$ grep -nE '\b(sorry|admit|axiom|native_decide)\b' RBM3D/Probe/T2513Pins.lean | wc -l   -> 0
$ grep -c STStep5IIIgL RBM3D/Probe/T2513Pins.lean -> 0 ;  wc -l -> 392 (cap 400)
$ lake env lean audit_scratch.lean   # #print axioms of every `theorem T2513_*` (grep: 24 theorems)
24 lines "depends on axioms: [propext, Classical.choice, Quot.sound]"; other output: exit=0 only
$ git diff --stat main...t/T2513
 RBM3D/Probe/T2513Pins.lean   | 392 ++++
 docs/reports/T2513-design.md | 205 ++++
$ lake env lean docs/tickets/checks/T2513-check.lean   # main worktree
exit=0 (no error lines)
$ lake env lean band.lean            # MNO-C1: band terminal axioms, t/T2513 vs main
branch: 'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
branch: 'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
main:   'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
main:   'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --stat a082fcfe main -- RBM3D/Main RBM3D/Universality RBM3D/BA/UNPins.lean   -> (empty)
```
No merged file changed (MNO-C1); only the two sole writable files are touched.

## 2. D1 pins against the merged texts (Iff.rfl, uncommitted scratch)
`gen_rfl.py` reads each merged `def` body from `PinsK.lean` / `OUInterfaceK.lean`, inserts `Dm d →` before `3 ≤ d →` and maps `UNOUClaimsk K ↦ T2513_UNOUClaimskD Dm K`, and emits `example : T2513_<pin>D Dm args ↔ (<generated body>) := Iff.rfl`.
```
-- UNQuek: filter inserted 1x        -- UNLocAvgk: 1x       -- UNOUClaimsk: 1x     -- UNOURowk: 0x (claims mapped)
-- UNEMCTE2Rowk: 1x                  -- UNJakUywRowk: 1x    -- UNClaimRowk: 2x     -- UNG1Rowk: 1x
example : T2513_UNLocAvgBAD (fun _ => True) ↔ UNLocAvgBA := T2513_UNLocAvgkD_true _
example : T2513_UNQueBAD (fun _ => True) ↔ UNQueBA := T2513_UNQuekD_true _
$ lake env lean audit_scratch.lean  -> exit=0 (all 8 Iff.rfl and the 2 BA readings elaborate)
```
So every D1 successor is the merged text with the filter added and nothing else: same quantifier order `∀ d : ℕ, Dm d → 3 ≤ d → …`, same exponents (`𝔠 * 𝔡 / 30`, `N^{-D}`, `ouTauMax 𝔠 𝔡`) and ranges. The eight band `Iff`s at `Dm = fun _ => True` (:91-110) and the two band instances (:113, :115, via the merged `UNLocAvgk_band`, `UNOURowk_band`) compile. The filter is a parameter, and the generic texts (:36-88, :118-190) contain no `UNKind.ba`, `UNKind.band`, `BAbulk` or `BAm` (grep: 0; the only case-insensitive "ba" hit is `queBadMat`, a false positive): C1 holds. All names carry the `T2513_` prefix.
`T2513_BAEnd_locSCL` (:209) and its vocabulary (:195-206) were compared with `t/T2449` 921369b2 `T2449Pins.lean:156-200` after removing the prefixes: identical, except that the unused `BAprof`, `BAqdBadz`, `BAdecolBad` and `BAEnd_QDiffL` are dropped (diff pasted in the scratch session; F3 of the design asks for a re-check at M1 row a's merge).

## 3. D2 re-derived (MNO-C2)
```
$ grep -nE '∀ d[ :,]' <the ticket's 7 files> | wc -l   -> 102
  UNPins 14, RandomLayerBGBA 8, PinsK 32, OUInterfaceK 16, EMCTE2BA 14, PinsC2 4, RandomLayerBG 14
$ python3 -I place.py <7 files>    # each hit placed by its enclosing declaration (or the next one, for a docstring hit)
102 hits placed, 0 unplaced. Hits whose declaration is not a pin text, an instance/example, or a band lemma:
  UNPins:143,144 un_claimAll_of_rowsBA | :160 UNDensBARow' | :170 UNTrLocalBARow | :182 UNTrLocalInitBARow' | :191 UNNormBARow
  :357 UNQueBA_of_BAEnd_QUEL | :370 baBUniv_of_rows | PinsK:205 UNGreenCorrAllC | :276 UNStep1GoodC | :294 UNCoreC
  :494 UNOUQUEk_zero_of_UNQuek | OUInterfaceK:109,110 UNG2bRowk | PinsC2:91 UNStep1GoodC'' | :108 UNCoreC''
  :863 not_UNStep1GoodC'_of_diag | :1346 step1GoodC''_det | EMCTE2BA 629 jakUywRowk, unJak/unUyw_of_ouClaimsk, _hbad_of_K
  RandomLayerBG 400-412 g1Rowk_of_inputsG (12)
```
My placement agrees line by line with the design's classes (P 19, M 23, U 7, K 3, R 11, T 2, I 30, B 7 = 102).
**Evidence for the "per-`d`: mechanical copy" rows.** The filtered twins are the merged proofs with `Dm d`/`hD` threaded through. A normalised diff (prefix and filter tokens removed) of merged vs probe gives only renames and line wrapping, plus the rename `hD ↦ hDg` in `jakUywRowk` (avoiding a clash with the filter hypothesis):
```
un_claimAll_of_rowsk  PinsK:454-466 vs :120-132        -> diff: header renames only (6 lines)
ouRowk_of_pins        OUInterfaceK:292-298 vs :152-158 -> diff: 2 renamed names
g1Rowk_of_inputsG     RandomLayerBG:399-427 vs :160-188 -> diff: 2 renamed names
jakUywRowk            EMCTE2BA:629-637 vs :142-150     -> diff: header renames + hD ↦ hDg
```
These twins compile at `Dm = (· = 3)`, where every filtered input exists only at `d = 3`. That is the decisive check: no input is read at another dimension. Merged `baBUniv_of_rows` (UNPins:367-379) reads `rD`, `un_claimAll_of_rowsBA`, `rN`, `rT0 hLoc d`, `rT hLoc d` at the theorem's own `d` (read). `UNQueBA_of_BAEnd_QUEL` (:357-359) uses `h d`. The band twin of TrLocal, `unTrLocalBandRow` (BUnivHolds:205-207), uses `hLoc d hd … (κ/2)`, i.e. its own `d`. `unJakUywRowBA_holds` (EMCTE2BA:766) is `jakUywRowk … UNLocAvgBA` (read). The BA `g1` example (RandomLayerBGBA:201-212) has its filtered twin at :345.
**Result: confirmed, no "uses another dimension" row.** MNO-C2's REQ trigger is not met.

## 4. D3: the target `T2513_n2_three` (:294-313) and closing condition (vi)
Statement (read): conclusion `BAEnd_BUnivL 3`. The hypotheses besides the data `P KF PB` are:
- `h32 : UNL32`;
- the `d = 3` inputs `UNMLOutBA 3`, `T2513_BAEnd_locSCL 3`, `BAEnd_QUEL 3`, `UNOUProfRowk (UNKind.ba 3) (P 3)`, `RBG_ProfComp … 3`, `RBG_Prod … 3`, `RandomLayerB_LL … 3`, `RBG_Que … 3`;
- the rows `T2513_TrLocalCore`, `T2513_TrLocalInitCore` (D5 cores) and `UNNormBARow`.

There is no `∀ d` form of `UNMLOutBA`/`UNLocAvgBA`/`UNQueBA` and no `STStep5IIIgL` (grep 0). `hML`'s type matches merged V:
```
$ lake env lean ml3.lean    # main worktree
RBM.BA.unMLOutBA_three : RBM.Univ.UNMLOutBA 3
'RBM.BA.unMLOutBA_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The proved leaves (`unCoreC''_holds`, `greenCorrAllC`, `un_gueLocal_of_tail gueSchurTail`, `unDensBARow'_holds`, `unEMCTE2RowBA_holds`, `g2bRowk`) are applied inside, not assumed. `T2513_baBUniv_of_rowsD` (:273) is the merged `baBUniv_of_rows` with the BA rows/inputs filtered and `rT0`/`rT` replaced by the D5 cores. Its proof body is the merged one plus one line (`hLd`, :279).
**Compiled nonempty instances** (six `example`s, :322, :330, :345, :361, :370, :381) all sit at `d = 3`, with:
- the merged class sequence `S0` (`(L,g) = (4, 3/10)`) and `(𝔠,𝔡) = (1/6, 1/10)`;
- `κ_* = clsκ 4 _` (`clsκ_pos`) and `E_* = (fp 4 _).E` (`S0_bulk`);
- `k = 1`, `E' = 0`, `O = UNInst.bump` (`bump_testFun`), `n_f = 2`.

Every deterministic hypothesis is discharged (`le_rfl : 3 ≤ 3`, `rfl : 3 = 3`, `S0_adm`, `S0_bulk`, `ouTauMax_pos`). Only other gates' pins stay hypotheses. The filter `(· = 3)` is inhabited, so nothing is vacuous. The probe declares no structure, so no hypothesis is hidden in a field. The probe imports only merged modules and the T2449 copy, so there is no cycle.

## 5. D4 price re-derived (`price_audit.py`, design's rule: probe lines + 3 per declaration + 30 header + instance allowance)
```
G1: probe lines 66, central 166, calibrated 176-227
G2: probe lines 56, central 118, calibrated 125-162
BA: probe lines 56, central 185, calibrated 178-237
impl central 469, calibrated 479-626; instance lines (code, docstrings excluded) 55
N2 central x0.96-1.28: (221, 294) hi 563
N2+impl: 700 - 920 hi-case 1189 | raw worst 440+626 = 1066 | stop 1950
```
This equals the design's §4 to the line. Placement "inside N2" (≤ 1,950 under every reading, including the uncalibrated N2 hi 440 + 626), so there is no new row and no REQ before N2. The M/N forecast stays ≈ 12 (11–14), checked against the design §8 row count (4 used + 7 remaining rows, 8 with M1's split).

## 6. D5, D6
D5 (:242-255): `T2513_TrLocalCore` / `T2513_TrLocalInitCore` have the shape `∀ d, 3 ≤ d → T2513_UNLocAvgBAD (· = d) → <merged body at d>`. The bodies are verbatim UNPins:170-174 / :182-186 (read). The merged `UNTrLocalBARow` / `UNTrLocalInitBARow'` follow in one line each (:252-255, compiled). The bridges `T2513_locAvg_core` (:221) and `T2513_que_core` (:235) are per-`d` cores, and the merged `∀ d` forms follow in one line (:231, :239, compiled).
D6 (design §6) quotes `baEnd_BUnivL_three : UNL32 → BAEnd_BUnivL 3` and `baThm27L_three : UNL32 → BAThm27L 3`; its compiled core is `T2513_n2_three` (§4 above).

## 7. Paper deltas
The design proposes none new. D723 (`docs/paper-deltas.md:1803`, BA Thm 2.7 at `d = 3` only, DECISIONS §316) covers the restriction. The filter `Dm` is Lean-internal and changes no statement relative to the merged pins (§2 Iff.rfl). Coverage: complete.

## 8. Observations (no statement, instance, build, axiom or paper-delta effect)
- O1: Design §0 pastes `git diff --stat … -- RBM3D` with "348 insertions"; at a6d9966e it is 392 (the paste predates the last commit). The quoted axiom lines read `band_terminal'`/`bUniv_holds'` (quote residue of `'RBM.Endpoints.band_terminal'`).
- O2: `T2513_n2_three` takes three rows with their own `∀ d` (`T2513_TrLocalCore`, `T2513_TrLocalInitCore`, `UNNormBARow`). None of them reads an input at another dimension: the cores take `UNLocAvgBAD (· = d)`, and `UNNormBARow` is a per-`d` Gaussian bound (UNPins:190-192). D6's `UNL32 →` signature therefore needs their owners (M1 b, N2) to prove them for every `d ≥ 3` with no regime-(iii) input, or N2 to specialise them to `d = 3` in one line.
- O3: The D5 cores refer to the G1 name `T2513_UNLocAvgBAD`. M1 b / M3 can state them before G1 merges only through option (γ) (an explicit private body closed by `Iff.rfl`). Choosing between α, β and γ is the dispatcher's ordinary release decision for M1 b / M3. It does not change this gate's statements or the price conclusion: α adds no row, and β adds +1 row, which stays ≤ 15.

## Per-target verdicts
| deliverable | verdict |
|---|---|
| D1 filter vocabulary (8 pins + BA readings, band `Iff`s) | PASS |
| D2 table + grep (102/102 placed, no "uses another dimension") | PASS |
| D3 probe (compiles, 24 theorems standard axioms, 6 nonempty `d = 3` instances, closing (vi)) | PASS |
| D4 price/placement (479–626; inside N2; no REQ) | PASS |
| D5 per-`d` cores, D6 signatures | PASS |
| Paper deltas (D723 covers; none new) | PASS |
