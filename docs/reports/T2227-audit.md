Auditor model: claude-opus-5-5

# T2227 audit (round 1) — BA-D8 `RBM3D/BA/CouplingWindow.lean` — Mon Oct  5 23:44:51 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2227-audit1`, detached at `t/T2227` = 3e769f1 (base 0f44a56; `main` = 37289f6).
Scratch: `<scratchpad>/T2227/audit/` (`probe.lean` = `git show 96e4087:RBM3D/Probe/T2205Pins.lean`, `cw.lean` = the new file).

## 1. Diff scope
```
$ git diff --name-only main...t/T2227
RBM3D/BA/CouplingWindow.lean
```
Only the sole writable file. `RBM3D/BA/MFixedPoint.lean`, `RBM3D/Test/Axioms.lean`, `RBM3D.lean` untouched (no frozen signature touched).

## 2. Statements (verbatim move; ticket Targets 1, acceptance "verbatim (script)")
Independent script `verb.py`: blocks B1–B10 extracted from the probe at the ticket's ranges, (c1) applied to B2, `private ` inserted at
probe `:803,:845,:852,:878` of B4 (assert: each starts `private theorem`), searched as contiguous ordered substrings of the file:
```
B1 44 True ordered      B6 7 True ordered
B2 149 True ordered     B7 26 True ordered
B3 73 True ordered      B8 31 True ordered
B4 483 True ordered     B9 17 True ordered
B5 6 True ordered       B10 23 True ordered
c3 body in file: True
non-block lines: 63
```
The 63 non-block lines (non-blank ones printed by the script) are: copyright `:1-5`; imports `:7-8` (exactly
`RBM3D.BA.MFixedPoint`, `Mathlib.Topology.MetricSpace.Contracting`); new module docstring `:10-25`; the four `set_option`s,
`noncomputable section`, the two `open` lines, `namespace RBM.BA`, the `open RBM RBM.Loop …` line `:27-39` (= probe `:31-43` with
`RBM.Probe.T2205` → `RBM.BA`); the (c3) body `:800-803`; `namespace CouplingWindowInst` `:840`; the (c6) lines `:891-892`;
`end CouplingWindowInst`, `end RBM.BA`, `end` `:917-921`. Nothing else.
```
$ diff <(sed -n '173,176p' docs/tickets/checks/T2205-check.lean) <(sed -n '800,803p' cw.lean) && echo c3-byte-equal
c3-byte-equal
```
(c6) replaces probe `:3667-3668` (`rw [BAflowLam0_zP] at hlo hhi` / `rw [BAflowEs_zP]`) by
`have e : BAm 3 (szP.L n) (szP.lam n) (zP n) = mS 4 10 := BAm_zP` / `rw [e] at hlo hhi ⊢` (2 lines ≤ 4); example statement unchanged.

Check-file pin text vs T2205 design pin text (`T2205-check.lean:135-185` vs `T2227-check.lean:91-133`, comment lines removed):
`diff` shows only docstring lines and one indentation change (`BAflowE … = E` line of `BAzztE_inv`); no term differs.

Compiled equality (scratch `T2227AuditEq.lean` = check file + `import RBM3D.BA.CouplingWindow` + 17 examples: `rfl` for
`BAgapReal`, `BAzztE_inv`, `BAWinBulk_of_dom_stmt`, `@BAmWindow`, `@BAWinBulk d`; `T2227Check.Y_pin := @RBM.BA.Y` for the 12
public theorems; + `#print axioms`), run in the audit worktree, then moved to scratch:
```
$ lake env lean T2227AuditEq.lean ; echo exit $?
exit 0
$ grep -c "^example" T2227AuditEq.lean      # 8 check-file examples + 17 audit examples
25
$ grep -n "error" eq.log
(no output)
```
Per pin, against the ticket's mathematics:
- `BAgapReal d`: `∀ L ≥ 3, g > 0, E, m, BASelf d L g E m → 2 (Im m)² ≤ Re(1 − L^{-d} tr M²)`. D537 (T2205c): not in paper. PASS.
- `BAmWindow d Λ κ`: `3 ≤ d → 0 < Λ → 0 < κ → ∃ c₁ ∈ (0,1/2], ∃ C > 0, ∀ L ≥ 3, 0 < g ≤ Λ, E, m, BAReal κ → ∀ g' ∈ [√(1−c₁)g, g],
  BAReal (κ/2) at BAm g' ∧ ‖BAm g' − m‖ ≤ C(g−g')`. Constants chosen after `(d,Λ,κ)`, before `L g E m`: the order the ticket asks
  (§29 (4)). D537. PASS.
- `BAzztE_inv d`: `0 < τ < 1`, `BASelf (√τ g) E m₀` ⇒ `BAm g (z_τ/√τ) = √τ m₀ ∧ BAt0 = τ ∧ BAflowE = E`; matches `zztE_BA`
  `7_8:1796-1808` read backwards. PASS.
- `BAWinBulk` (structural): the (c3) written-out text, `rfl`-equal to the check pin (above). PASS.
- `BAWinBulk_of_dom_stmt d`: `3 ≤ d → ∀ κ Λ > 0, ∃ c₁ ∈ (0,1/2], ∀ ε sz z, (∀ n, 0 < lam n ≤ Λ) → (∀ n, BAdom … κ ε (z n)) →
  BAWinBulk sz z c₁ (κ/2)`; `c₁` before `ε, sz, z`; `∀ n, 0 < lam n` is D538; loss `κ ↦ κ/2` visible in the statement. PASS.
- The 12 public theorems: each is accepted at the check file's `*_pin` statement (above), so the signatures are the pinned ones.

## 3. Hidden hypotheses, vacuity, cycles
- No new structure. `Sizes` (merged) is used only via its fields `L`, `lam`, `three_le_L`, `size`; no hypothesis in a field.
- `BAWinBulk_of_dom (hw : ∀ Λ κ, BAmWindow d Λ κ)` is discharged in the same file: `BAWinBulk_of_dom_holds d := BAWinBulk_of_dom d (BAmWindow_holds d)`.
- The `*_holds` theorems take no hypothesis beyond the pin's own implication premises. No `Prop` hypothesis is external: no external input,
  so no limit check is needed (TEAM §8 lesson 14).
- No cycle: the only imports are merged `RBM3D.BA.MFixedPoint` (T2189) and Mathlib; `grep -n "Probe\|BAflowLam0\|BAflowEs\|BAflowT0"`
  hits only the module docstring (`:13`, `:21`).
- Private helpers (rule (E), ticket (c2)): `cw.lean:90,367,409,416,442` are `private theorem` (`T2205_inv_spectral`,
  `abs_eigenvalue_le`, `BASelf_iff_fixed`, `inv_mul_inv_sub_le`, `norm_inv_le_of_abs_im`).
- Name clash on `main` (37289f6), 33 names + `CouplingWindowInst`, declaration-form grep over `RBM3D/**/*.lean` excluding `Probe/`:
```
$ for n in …34 names…; do grep -rnE "^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|structure|instance|namespace) $n( |$)" RBM3D --include='*.lean' | grep -v Probe/; done | wc -l
       0
```

## 4. Compiled nonempty instances (`cw.lean:887-911`, namespace `RBM.BA.CouplingWindowInst`)
Data: `d = 3`, `szP` (`L ≡ 4`, `W ≡ 2`, `lam ≡ 10`, `N = 512`), `zP ≡ zS 4 10` (merged, `zS_im_pos`), flow data `t0P`, `EP`, `m0P`,
`g0P` defined explicitly from merged `BAt0`/`BAflowE` (`flowP_data` gives `0 < t0P < 1` and `BASelf 3 4 g0P EP m0P` from merged
`BAzztE_data`).
`grep -n "^example" cw.lean`: lines 887, 896, 902, 907 (the four below).
- `:887` window: `∃ c₁, 0 < c₁ ∧ c₁ ≤ 1/2 ∧ BAWinBulk szP zP c₁ ((mS 4 10).im / 2)`, via
  `BAmWindow_holds 3 10 (mS 4 10).im (3 ≤ 3) (0 < 10) (selfS 4 10).1` and `flowP_real`. Every hypothesis discharged; `κ = Im m_S > 0`,
  `Λ = 10`, `L = 4`. Non-degenerate.
- `:896` `BAzztE_inv_holds 3 4 _ 10 _ t0P EP m0P` with `0 < t0P`, `t0P < 1`, `BASelf` from `flowP_data`. Non-degenerate.
- `:902` `BAgapReal_holds 3 4 _ g0P g0P_pos EP m0P` (`BASelf` from `flowP_data`). Non-degenerate.
- `:907` `BAMB_trace_sq_eq_sum 3 4 g0P EP m0P` with `(EP + m0P).im ≠ 0` proved from `flowP_data`. Non-degenerate.
These are the four instances the ticket lists ("Instances to compile"); all compile (build §5).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.CouplingWindow ; echo exit $?
modifies the current goal, which was modified by the flexible tactic `simp` on line 473!
Build completed successfully (3334 jobs).
exit 0
$ grep -c warning build.log ; grep -n error build.log
14
(no output)
```
(14 warnings, style linters only.) `#print axioms` (from `T2227AuditEq.lean`, 17 lines, all identical form):
```
'RBM.BA.BAMB_trace_sq_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAgapReal_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAzztE_inv_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAzztE_inv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAself_im_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAwindow_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAmWindow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAwindow_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAwindow_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAWinBulk_of_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAWinBulk_of_dom_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.BAm_zP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.flowP_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.g0P_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.g0P_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.flowP_real' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " cw.lean`: no output.
Full `lake build` is the hub's at merge (root import not yet added).

## 6. Paper deltas
- Gap and window constants (`BAgapReal`, `BAmWindow`, `c₁ = min(1/2, κ⁹/(64dΛ))`, `C = 2d/κ⁴`): D537 (`docs/paper-deltas.md:1496`).
- `∀ n, 0 < sz.lam n` premise / tail consumers of `BAWinBulk_of_dom_stmt`: D538 (`:1497`).
- (c3) is `rfl`-equal to the design text, so it is not a statement difference. `BAzztE_inv` follows `zztE_BA` `7_8:1796-1808`.
No uncovered difference; no `T2227a` needed.

## 7. Observations (no effect on the verdict)
- O1. `BAWinBulk_of_dom_holds`, `BAwindow_iter`, `BAwindow_floor` have no direct `example` in this file. The ticket assigns their
  instances (the `sz0` window instances `sz0_win*`, `sz0_conArg_bulk`, and the `BAWinBulk_of_dom_holds` example) to BA-S3 under
  "Not targets" (DECISIONS §72 (2), supervisor 2252 `:59`), and the move rules allow no new lines here. A `BAWinBulk_of_dom_holds`
  instance at `szP/zP` would need `Im zS 4 10 ≤ 1`, i.e. `Im mS 4 10 ≥ 1/5`, which no merged lemma gives. The same conclusion,
  `BAWinBulk szP zP c₁ (κ/2)`, is compiled through `BAmWindow_holds` plus `flowP_real` (= `BAdom_real`), which is the proof route of
  `BAWinBulk_of_dom`. The dispatcher should check that the BA-S3 ticket carries these instances.
- O2. Prove report (b): the name-clash run on `main` covered a 14-name subset; this audit's run over all 34 names on 37289f6 gives 0 hits.

## Verdict
| Target | Verdict |
|---|---|
| 1. Copy B1–B10 with (c1)–(c6) (5 defs, 17 theorems, 11 instance decls, 4 examples) | PASS |
| 2. Imports exactly `RBM3D.BA.MFixedPoint`, `Mathlib.Topology.MetricSpace.Contracting` | PASS |
| 3. Registry: no line (no `Test/Axioms.lean` change) | PASS |

Overall: **PASS**. No dispatcher sign-off needed (O1 records a deferral the dispatcher already decided).
