Auditor model: claude-opus-5-5

# T2404 audit (round 1) — BA-T T2: `lem: EMn2_N` (first and third estimate) over the carrier

Written Sun Oct 11 03:54:00 UTC 2026 (`date -u`). Branch `t/T2404` at 65cf42f; merge base 1181514; `main` 3e72137
(0 Lean files changed on `main` since). Worktree `RBM3D-wt/T2404-audit1` (detached 65cf42f); scratch `scratchpad/T2404/`.

## 1. Diff scope, stop line, hygiene
```
$ git diff main...t/T2404 --name-only
RBM3D/Induction/EMn2Exp1.lean
RBM3D/Induction/EMn2Exp2.lean
RBM3D/Induction/EMn2Poly.lean
$ git diff --numstat main...t/T2404 | awk (sum)
A=724 R=274 A+R=998 A-R=450
$ git diff main...HEAD | grep "^+" | grep -cE "\bsorry\b|\badmit\b|native_decide|^\+axiom "
0
$ git diff main...t/T2404 | grep -c "^[-+].*open private"  → 0;   git diff main...t/T2404 | grep "^+import"
+import RBM3D.BA.FlowPins          (EMn2Exp2 only; item 8 BA examples; resolved by 1a-audit round 2 §4, no cycle)
+import RBM3D.Chain.Step2Gen       (EMn2Poly)
```
Only the three sole writable files. Stop line 1,000: not hit under either reading (A+R = 998, net A-R = 450).

## 2. Statements (G1: old names, old statements; frozen pins)
Old declarations, `main` vs branch, whitespace-normalized header text (`stmt.py`):
```
$ python3 scratchpad/T2404/stmt.py
EMn2Poly stEMn2Poly_holds IDENTICAL 47
EMn2Exp1 emn2Exp_near IDENTICAL 546
EMn2Exp1 emn2Exp_far12 IDENTICAL 547
EMn2Exp1 emn2Exp_of_far3 IDENTICAL 553
EMn2Exp2 emn2Exp_far3 IDENTICAL 559
EMn2Exp2 stEMn2Exp_holds IDENTICAL 58
EMn2Exp2 emn2Exp2_exists_CR IDENTICAL 201
```
(`emn2Exp2_exists_CR` is the private coupling of item 7, opened by `DuhamelII:42`; name and type kept.)
`Chain/Step2Gen.lean` (pins `STEMn2PolygL :471`, `STEMn2ExpgL :483`) is not in the diff. The targets are checked against the
pins by type ascription in `audit.lean` (section 4): `stEMn2PolygL_of law hF.1 : STEMn2PolygL d law Flow mk T0` and
`stEMn2ExpgL_of law hd hF hHK : STEMn2ExpgL d law Flow mk T0` elaborate, for arbitrary `law Flow mk T0 Hf ζf`.

Target statements (from the file):
- T1 `stEMn2PolygL_of` (EMn2Poly:859): `emn2PolyFacts d Flow mk T0 Hf ζf → STEMn2PolygL d law Flow mk T0`. No `3 ≤ d` (as pin).
- T2 `stEMn2ExpgL_of` (EMn2Exp2:1260): `3 ≤ d → emn2ExpFacts … → emn2ExpHK d Flow mk T0 → STEMn2ExpgL d law Flow mk T0`
  (`3 ≤ d` as in the band theorem; ticket target 2 "as now").
- T5′ `stEMn2ExpJgL_of` (EMn2Exp2:1226): same hypotheses; conclusion `emn2ExpPrem d law Flow mk T0 Q` where `emn2ExpPrem`
  (Exp1:826) is the premise block of `STEMn2ExpgL` verbatim (κ ε 𝔡 > 0, 𝔠 sz z, Flow, `t ∈ [0,T0]`, ε₀ > 0, Ψ window,
  `STInitialGT2gL`, ℓ window, `∀ D>0, STLWassmExpgL`, `∀ D>0`), and `Q` = `∀ J ≥ 0, (Ĵ ≺ J) → ‖STEEg‖ ≺ η⁻¹(Bctl^{1/2}+J³)P²`.
  Quantifier order matches the pin (J introduced after D, inside the `PrecL` scope). It contains `(eq:MG_conclusion3_BA)`
  (`7_8:1999`, deterministic `J ≥ W^{-d}`) as a special case: a stronger variant, covered by paper-delta candidate `T2404a`.
- Item 3 (matrix-level lemmas): no matrix-level statement header appears in the declaration diff list except the new
  `emn2Poly_EEg_zero_eq/_one_eq` (public, file-stem prefixed; replace the private `STEEkM_zero_eq/_one_eq`, which had no
  user outside `EMn2Poly`: `git grep` on `main` finds only the separate `emn2Exp_STEEkM_*` in EMn2Exp1).

## 3. Hidden hypotheses, vacuity, cycles, C1
The facts bundles are explicit `def … : Prop` hypotheses of the theorems (not structure fields):
- `emn2PolyFacts` (Poly:835): (A) `sz.Admissible 𝔠 𝔡`; (R) for `0 ≤ u ≤ T0`: `Hf` Hermitian, `0 < Im ζf = C.eta n u`,
  `C.L n u σ a ω = loopFine … (Hf …) (ζf …) σ a`; (S) `∃ g, C.S n = SB d (sz.L n) g`.
- `emn2ExpFacts` (Exp1:811): `emn2PolyFacts` ∧ `T0 < 1` ∧ `C.eta n u ≤ 1 - u` ∧ (B) `∃ cB c > 0, ∀ᶠ n, ∀ u ∈ [0,T0],
  cB W^{-d} ≤ Bctl n u ≤ N^{-c}`.
- `emn2ExpHK` (Exp2:934): `∀ t ∈ [0,T0], ∀ D>0, ∀ᶠ n, ∀ x x' s, ℓ*_{t n} ≤ |x-x'|_∞ → ‖C.K n (t n) ![s,!s] ![x,x']‖ ≤
  W^{-d}·W^{-(D+d)}` — the single inequality hypothesis replacing `KLK_two` / `emn2Exp2_norm_STKloop` (item 4).
C1: none of them mentions `‖m‖=1`, scalar `m`, `mSigma`, `M = mI`, band `Theta`, or `sz.withLam 0`; they read only
`C.L, C.K, C.S, C.eta`, `sz`, `T0`, and the explicit realization `Hf, ζf`. Non-vacuity at the band: discharged by
the theorems `emn2Poly_bandFacts`, `emn2Exp_bandFacts`, `emn2Exp2_bandHK` (axioms below). At BA (spot check of (S),
`baFM.S = 1`, `FlowPins:322`) — compiled in `audit.lean`:
```
example (d L : ℕ) : SB d L 0 = 1 := by
  ext a b; simp only [SB_apply, sbKernel, Matrix.one_apply, sub_eq_zero]; split_ifs <;> simp_all     -- compiles
```
The remaining BA obligations (public Hermitian lemma for `seqHflowBA`, (B), (HK) composition `(Kn2sol)`+`baProp5_holds`)
are listed as owed by the BA twin (prove report (d) `T2404b`); the external (HK) has a limit check (report (a′-i) `hk2.py`:
thresholds in `log W` per decay rate, margin positive at `n=1e60` for rate 1). Cycle: `BA.FlowPins` closure contains no
`EMn2*` module (1a-audit round 2 §4); confirmed indirectly by the build below (a cycle would fail to build).
`ekPropTInf_holds` and `emn2Exp2_exists_CR` are reused model-free (H8, H9).

## 4. Build, check file, G1, axioms (audit worktree)
```
$ lake build RBM3D.Induction.EMn2Exp2 RBM3D.Induction.OptL2b RBM3D.Induction.DuhamelII RBM3D.Induction.OptL2a \
    RBM3D.Induction.EtermsMid RBM3D.Induction.MainIndHolds RBM3D.Induction.MainIndOut
⚠ [4051/4065] Built RBM3D.Induction.EMn2Poly (5.4s)
⚠ [4052/4065] Built RBM3D.Induction.OptL2a (9.6s)
⚠ [4053/4065] Built RBM3D.Induction.EMn2Exp1 (10s)
✔ [4054/4065] Built RBM3D.Induction.OptL2b (4.3s)
⚠ [4055/4065] Built RBM3D.Induction.EMn2Exp2 (16s)
⚠ [4057/4065] Built RBM3D.Induction.EtermsMid (14s)
✔ [4063/4065] Built RBM3D.Induction.DuhamelII (37s)
✔ [4064/4065] Built RBM3D.Induction.MainIndOut (4.3s)
✔ [4065/4065] Built RBM3D.Induction.MainIndHolds (2.9s)
Build completed successfully (4065 jobs).
EXIT=0
$ grep warnings of the three files | message | uniq -c        (linter only; no `declaration uses 'sorry'`)
   3 This line exceeds the 100 character limit, please shorten it!
  29 κ / 32 z / 20 sz / 10 u / 7 n / 1 D / 1 t : Variable name `…` is not explicitly referenced.
$ lake env lean docs/tickets/checks/T2404-check.lean >/dev/null; echo check exit $?
check exit 0
$ lake env lean scratchpad/T2404/audit.lean     (G1 examples, pin ascriptions, SB d L 0 = 1, #print axioms)
  example (d : ℕ) : STEMn2Poly d := stEMn2Poly_holds d                      -- ok
  example (d : ℕ) (hd : 3 ≤ d) : STEMn2Exp d := stEMn2Exp_holds d hd        -- ok
'RBM.Gauss.Sizes.stEMn2PolygL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stEMn2ExpgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stEMn2ExpJgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stEMn2Poly_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stEMn2Exp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_far3g' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_nearg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_far12g' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp2_bandHK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_bandFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_bandFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0          (other output: unused-variable linter warnings on binder names of audit.lean only)
```
Consumers build unchanged (sources untouched). Full `lake build` is the hub's at merge.

## 5. Compiled nonempty instances (d = 3, `sz0`, κ=ε=𝔡=1/10, 𝔠=1/6, `z0`, `t ≡ 1/16`, ε₀=1/20)
```
EMn2Poly:1018  stEMn2PolygL_of (fun sz => Sizes.seqP sz) (emn2Poly_bandFacts 3) … sz0 z0 flow_z0 tInst … Ψ0 Ψ0_class hI hA
EMn2Exp2:1458  stEMn2ExpgL_of (fun sz => Sizes.seqP sz) (by norm_num) (emn2Exp_bandFacts 3) (emn2Exp2_bandHK 3 _) … hI … hA D hD
EMn2Exp2:1476  stEMn2ExpJgL_of … at J = Ĵ + W^{-3} (J ≥ W^{-d}, hJ0 proved, Ĵ ≺ J by StochDomAt.of_le_left/refl)
EMn2Exp2:1522  BA carrier: stEMn2PolygL_of / stEMn2ExpgL_of / stEMn2ExpJgL_of at baFMz, seqP (sz.withLam 0), BAFlow,
               BAflowT0, Hf = seqHflowBA (BAflowLam0 sz z) n u ω, ζf = ztOf …, sz0 zSeq flow_sz0; hF, hHK hypotheses
```
Band examples: every deterministic hypothesis discharged (facts bundles and (HK) by proved theorems, windows by
`Ψ0_class`, `Ψ1_window`, `ℓ_range_inst`, `sixteenth_le_lemT`); what stays is `hI` (`STInitialGT2`) and `hA`
(`STLWassm`/`STLWassmExp`), other gates' pins — permitted. Nondegenerate: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `D > 0`
arbitrary, `t = 1/16 > 0`. The BA examples are statement level, as item 8 requires. The deterministic core `emn2_ee_le`
instance (`N = 216`, non-diagonal Hermitian `H`) is kept. Old band instances (`emn2Exp_far3`, `emn2Exp2_loop2_far_le`) kept.

## 6. Paper deltas
- `T2404a` (prove report (d)): the `J` form drops `J ≥ W^{-d}` and allows ω-dependent `J` vs `(eq:MG_conclusion3_BA)`.
- `T2404b`: the generic statements are conditional on `emn2PolyFacts`, `emn2ExpFacts`, `emn2ExpHK` (incl. the 2-loop
  formula replaced by the inequality (HK)); BA obligations listed.
- Existing: D208 (`T2102a`, `STEMn2Poly` without `STGbEXP*`), D269 (`T2118a`, every `D > 0`, `3 ≤ d` hypothesis).

## 7. Observations (no RETURN)
- O1. Margin to the stop line is 2 (A+R = 998); band lemmas `emn2Exp2_loop2_far_le`, `emn2Exp2_STLKM_le` are now read only
  by examples (report (d)). Future edits of these files should remove dead lemmas first.
- O2. `emn2Exp_far3g` docstring still names `emn2Exp2_loop2_far_le` (report (d)); docstrings are not evidence.
- O3. One `set_option linter.unusedVariables false` in `EMn2Poly`; 3 long-line linter warnings.
- O4. Report (b) claims the T2405 coordination clause is vacuous; DECISIONS §218 (5) has since voided that coordination.

## Verdicts
| target | statement | hyps / vacuity / cycle | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `stEMn2PolygL_of` (+ `stEMn2Poly_holds` corollary) | = pin `:471` | explicit, band-discharged, C1-clean | EMn2Poly:1018 + BA | ok | covered | **PASS** |
| 2 `stEMn2ExpgL_of` (+ `stEMn2Exp_holds` corollary) | = pin `:483`, `3 ≤ d` | explicit + (HK), limit check | EMn2Exp2:1458 + BA | ok | covered | **PASS** |
| 3 matrix-level lemmas | unchanged | — | kept | ok | — | **PASS** |
| 5′ `stEMn2ExpJgL_of` | pin premises + J form | as 2 | EMn2Exp2:1476 + BA | ok | T2404a | **PASS** |
| G1 / item 7 / item 8 | old statements identical; `exists_CR` kept; `open private` unchanged | | | | | **PASS** |

**Overall: PASS.** No dispatcher sign-off needed.
