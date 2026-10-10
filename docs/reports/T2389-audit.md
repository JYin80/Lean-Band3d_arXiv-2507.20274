Auditor model: claude-opus-5-5

# T2389 audit (round 1) — BA-G2, `BALDEin` and the D-shift LDE layer
Written Sat Oct 10 16:42 UTC 2026 (`date -u`). Branch `t/T2389` at `b5dc671`; audit worktree `RBM3D-wt/T2389-audit1` (detached);
base worktree `RBM3D-wt/T2389-audit1-base` at merge-base `bf5f0d5` (for G1 only). Scratch: scratchpad `T2389/`.

## 1. Diff scope and stop line
```
$ git diff --name-only main...t/T2389
RBM3D.lean  RBM3D/BA/GreenLDE.lean  RBM3D/Green/IBPPoly.lean  RBM3D/Green/LDE.lean  RBM3D/Green/RowIndep.lean
$ git diff main...t/T2389 -- RBM3D.lean | grep '^[+-][^+-]'
+import RBM3D.BA.GreenLDE
$ git diff --numstat main...t/T2389 -- <3 in-place files>
256 213 RBM3D/Green/IBPPoly.lean ; 492 73 RBM3D/Green/LDE.lean ; 271 0 RBM3D/Green/RowIndep.lean   net3=733 ins3=1019
$ git show t/T2389:RBM3D/BA/GreenLDE.lean | wc -l        245      -> total 978 (net) / 1264 (insertions) < stop line 1800
$ git diff --stat bf5f0d5 main -- <the 4 source files>     (empty: main 2a05b1d has not touched them)
```
Only sole writable files touched; frozen signatures: see G1 (§3), all 28 unchanged.

## 2. Build, hygiene, axioms (audit worktree)
```
$ lake build RBM3D.BA.GreenLDE RBM3D.Green.LDE RBM3D.Green.RowIndep RBM3D.Green.IBPPoly
Build completed successfully (3758 jobs).        exit 0 ; error lines: 0 ; warnings: linter only (longLine, `show`)
$ git diff main...t/T2389 | grep '^+' | grep -cE '\bsorry\b|\badmit\b|native_decide|^\+(private )?axiom '
0
$ lake env lean ax.lean            (exit 0)
'RBM.BA.baLDEin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAGt_eq_green' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_G_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BALDEin_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenLDE_BAX_ae_block_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.LDE_stochDom_ldeRow_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.LDE_stochDom_ldeCol_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.IBPPoly_stochDom_ldeQuad_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeCol' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeQuad' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Full `lake build` + `#assert_rbm_axioms` (registry pre-check): not rerun here (hub runs it at merge); the prove report
(b2) records `Build completed successfully (4200 jobs)` and `0 axioms in RBM`.

## 3. Target 2 — G1 checks (28 names), statement text base vs branch
`g1.lean`: `#check @RBM.Green.<n>` for the 28 names of `T2378-design.md:91-93` (`cons_names.py`) and `#print` of the
defs `condExpDiag minorCol minorRowConj hwConst`; elaborated against each worktree's own build.
```
$ (cd RBM3D-wt/T2389-audit1-base && lake env lean g1.lean)   exit 0 lines 156 errors 0
$ (cd RBM3D-wt/T2389-audit1      && lake env lean g1.lean)   exit 0 lines 156 errors 0
$ diff g1.T2389-audit1-base.txt g1.T2389-audit1.txt          diff_exit 0
```
All 28 old statements (and the 4 def bodies) are byte-identical, so `example : <old> := <old name>` holds for each.
The dispatcher check file `docs/tickets/checks/T2389-check.lean` contains only `#check` lines (no G1 `example`s);
the diff above supplies the G1 check. Changed public IBPPoly declarations (22, the `D` argument added in place:
`minorRes`, `modelChaos(Eps)`, `vqM`, `sqVq`, ...) referenced outside `IBPPoly.lean`:
```
meas_lt_normSq_chaos_le / modelChaos / modelChaosEps: Universality/GUEPhase/AuxCarrier.lean:358,498,499  (docstrings only)
stochDom_ldeQuad: Test/Axioms.lean, Green/CondDom.lean   (G1 name, unchanged by the diff above)
```

## 4. Target 3 — pins against the probe (`t/T2378:RBM3D/Probe/T2378Pins.lean`), whitespace-normalised
```
$ python3 -I pindiff.py probe.lean RBM3D-wt/T2389-audit1/RBM3D/BA/GreenLDE.lean
BAGt_eq_green identical: True 285 285
ba_G_data identical: True 743 743
BAX identical: True 207 207
BALDEin identical: True 1730 1730
BALDEin_diag identical: True 235 235
```
`baLDEin_holds (d : ℕ) : BALDEin d` (GreenLDE.lean:199): no hypotheses. Proof: hLrow/hLcol/hLquad are
`LDE_stochDom_ldeRow_shift`, `LDE_stochDom_ldeCol_shift`, `IBPPoly_stochDom_ldeQuad_shift` at `sz.withLam 0`,
`D n = (g₀ : ℂ) • PsiI`, `z n = ztOf (BAmF ..) (E n) (t n)`, rewritten by `BAGt_eq_green`; hLdiag is `BALDEin_diag`
(= merged `stochDom_normSq_Hflow_diag (sz.withLam 0)`). Data from `ba_G_data` (hypotheses `0 < κ`, `BAFlow`,
`0 ≤ t ≤ T₀` only; no `g ≤ W^{-ε}`, no `‖M − m₀I‖` smallness: supervisor C1 satisfied).

## 5. Target 1 — the generic statements over D (hypotheses read from the signatures)
```
LDE_stochDom_ldeRow_shift / LDE_stochDom_ldeCol_shift (LDE.lean:1149, 1193),
IBPPoly_stochDom_ldeQuad_shift (IBPPoly.lean:1037):
  (hsz : sz.SizeTendsto) (D : ∀ n, Matrix (Idx ..) (Idx ..) ℂ) (hD : ∀ n, (D n).IsHermitian)
  {z : ℕ → ℂ} (hz : ∀ n, (z n).im ≠ 0) {t} (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1) :
  sz.PrecPT (LHS with row seqHflow, resolvent green (D n + seqHflow ..) (z n)) (RHS with svar .. (sz.lam n))
```
`D` is indexed by `n` only (deterministic, ω-free); hypotheses are exactly Hermitian / `Im z ≠ 0` / `0 ≤ t ≤ 1`
(+ `SizeTendsto`); no structure-field hypothesis; no spectral bound on `‖D‖`. The band `stochDom_ldeRow/Col/Quad`
are the `D = 0` corollaries (G1-identical, §3). Added declarations (from `git diff bf5f0d5`):
```
LDE:      LDE_{greenMinorMatD, greenDiagCenteredD, greenMinorDiagCenteredD, flucDiagD, flucDiagMinorD, flucAvgD,
          condExpDiagD} (defs), LDE_shift_zero, LDE_measurable_*D, LDE_norm_*D, structure LDE_FlucBoundD,
          LDE_flucBound_envD, LDE_integrable_norm_flucAvg_powD, LDE_stochDom_ld{eRow,eCol}_shift, ...
RowIndep: RowIndep_{minorColD, minorRowConjD} (defs), _congr, _measurable_*, _eq_greenMinor, RowIndep_ldeRowLHS_eqD,
          RowIndep_rowVarSum_eqD, RowIndep_ldeColLHS_eqD, RowIndep_rowVarSum_minorRowConjD_eq, *_zero bridges
IBPPoly:  minorRes, modelChaos(Eps), vqM, sqVq and their lemmas take `D` in place; IBPPoly_stochDom_ldeQuad_shift
```
`LDE_FlucBoundD` is a structure, but it is a conclusion-side bundle (`LDE_flucBound_envD`), not a hypothesis of
any target; the `‖m‖ ≤ 1` hypothesis it carries is used only by the fluctuation-layer twins, not by `BALDEin`.
No circularity: the shift theorems depend only on merged band machinery (`stochDom_rowSum_generalTime`,
`Hflow_submatrix_congr_offRowCoord`, `gaussIBP`); `baLDEin_holds` depends on them and on the merged `BAFlow` pins.

## 6. Compiled nonempty instances (all in the built modules above)
```
BA/GreenLDE.lean:227  example := baLDEin_holds 3 (1/2) (1/10) (1/10) .. (1/6) SizesInst.sz0 FlowPinsInst.zSeq
                       FlowPinsInst.flow_sz0 (fun _ => 1/2) (fun _ => by norm_num) (fun n => (FlowPinsInst.half_lt_t0 n).le)
BA/GreenLDE.lean:232  example : <hLquad conjunct at the same data, stated> := (baLDEin_holds 3 ..).2.2.1
Green/LDE.lean:1608,1612   LDE_stochDom_ldeRow_shift / _Col_shift at sz0, D = LDE_shiftD_sz0 = (1/2)•1 (≠ 0), z ≡ zt 0 (1/2), t ≡ 1/2
Green/IBPPoly.lean:1179    IBPPoly_stochDom_ldeQuad_shift at the same data
band corollaries at D = 0: LDE.lean:1670,1674 (measurable_green_apply, norm_green_apply_le_etaT from the D-versions);
  RowIndep.lean:1514 (ldeRowLHS_eq); IBPPoly.lean:1167 stochDom_ldeQuad_sz0
```
Data: `d = 3`, `sz0` (n = 0: L = 4, W = 32, N = 2^21), `t ≡ 1/2 ≤ T₀`, every deterministic hypothesis discharged
(`BAFlow` by `flow_sz0`, `t ≤ T₀` by `half_lt_t0`); no `N = 0`, empty index, collapsed window, or `False` premise.

## 7. Paper deltas
Proposed in the prove report (d): T2389a (X is the band model of `sz.withLam 0`, off-block entries vanish only
a.s., `GreenLDE_BAX_ae_block_support`); T2389b (generic D-statements assume `0 ≤ t ≤ 1`, `Im z ≠ 0` in place of
`t < 1`, `|E| ≤ 2 − κ`). `BALDEin` itself equals the probe pin (§4); no further Lean/paper difference found.

## 8. Name clashes
```
$ git grep -lw <n> main -- 'RBM3D/*.lean' | grep -v Probe | wc -l
BAX 0  BALDEin 0  BALDEin_diag 0  baLDEin_holds 0  BAGt_eq_green 0  ba_G_data 0  GreenLDE_BAX_ae_block_support 0
LDE_stochDom_ldeRow_shift 0  IBPPoly_stochDom_ldeQuad_shift 0  RowIndep_minorColD 0  LDE_shift_zero 0
```
Unprefixed public additions other than the pinned names are pre-existing IBPPoly names restated in place.

## Observations (no statement, instance, build, axiom or paper-delta effect)
- O1. Target 1 wording "each band theorem becomes the corollary at D = 0": literally true for
  `stochDom_ldeRow/Col/Quad` and the IBPPoly objects. For the LDE 102-398 fluctuation layer (defs live in the
  non-writable `Green/FlucVanish`) and the RowIndep minors, the generic statements are separate `LDE_*D` /
  `RowIndep_*D` twins tied to the band objects by `LDE_shift_zero`, `RowIndep_minor{Col,RowConj}D_zero`; the band
  declarations keep their old proofs. Statements are present and G1-identical; recorded by the prover as D1.
- O2. `isUnit_det_Hflow_sub`, `green_Hflow_diag_ne_zero` have no named D-twin; both are one-line applications of
  the Hermitian-generic `LDE_isUnit_det` / `green_diag_ne_zero` at `D + X` (`Matrix.IsHermitian.add`).
- O3. `GreenLDE_BAX_ae_block_support` is proved but unused by `BALDEin` (for G3a).
- O4. The check file has no G1 `example`s; §3's base/branch `#check` diff covers them.

## Verdicts
| target | verdict |
|---|---|
| 1. in-place G segments over D, band names kept | PASS (O1, O2) |
| 2. G1 checks, 28 names | PASS |
| 3. `BAGt_eq_green`, `BAX`, `BALDEin` (= probe), `baLDEin_holds : BALDEin d` | PASS |
| 4. `ba_G_data` (BAFlow, 0 ≤ t ≤ T₀ only) | PASS |
| 5. nonempty instances (d = 3, flow_sz0; one D = 0 band corollary per file) | PASS |
| 6. registry: none; axioms standard | PASS (full build at merge by the hub) |

Overall: **PASS**. No dispatcher sign-off needed.
