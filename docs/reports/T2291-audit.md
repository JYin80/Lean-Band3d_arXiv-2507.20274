Auditor model: claude-opus-5-5
# T2291 audit (round 1) — BA-D7 `RBM3D/BA/ImmLower.lean` — Tue Oct  6 12:04:19 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2291-audit1`, detached at `t/T2291` = `58965b6`.

## 1. Diff scope and build
```
$ git diff --stat main...HEAD
 RBM3D/BA/ImmLower.lean | 479 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 479 insertions(+)
$ lake build RBM3D.BA.ImmLower 2>&1 | grep -E "error|ImmLower.lean|Build completed"
Build completed successfully (3338 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^\s*axiom|set_option|implemented_by|unsafe|opaque" RBM3D/BA/ImmLower.lean
39:set_option linter.style.longLine false
40:set_option linter.unusedSimpArgs false
41:set_option linter.unusedVariables false
42:set_option linter.style.setOption false
```
Only the sole writable file is touched; no merged file, no frozen signature changed. The four hits are linter options only.

## 2. Statements against the pins (compiled check-file equality + axioms)
Scratch file = imports of `docs/tickets/checks/T2291-check.lean` + `import RBM3D.BA.ImmLower` + the rest of the check
file + `example : RBM.BA.T2291Check.Y_pin := @RBM.BA.Y` for the 6 targets + `#print axioms`:
```
$ lake env lean $S/check_eq.lean > $S/check_eq.out 2>&1; echo exit=$?
exit=0
$ grep -E "error" check_eq.out | wc -l        -> 0
example : RBM.BA.T2291Check.BASelf_sub_le_pin := @RBM.BA.BASelf_sub_le
example : RBM.BA.T2291Check.BAm_im_ge_half_pin := @RBM.BA.BAm_im_ge_half
example : RBM.BA.T2291Check.BAm_im_ge_mul_pin := @RBM.BA.BAm_im_ge_mul
example : RBM.BA.T2291Check.BAm_im_lower_pin := @RBM.BA.BAm_im_lower
example : RBM.BA.T2291Check.baImmLower_holds_pin := @RBM.BA.baImmLower_holds
example : RBM.BA.T2291Check.BAm_im_lower_of_bulk_pin := @RBM.BA.BAm_im_lower_of_bulk
'RBM.BA.BASelf_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_ge_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baImmLower_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_lower_of_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The pin `BAImmLower` is the merged definition, unchanged (`git diff` touches no merged file):
```
$ sed -n 593-600p RBM3D/BA/MFixedPoint.lean
def BAImmLower (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ η : ℝ, 0 < η → η ≤ 1 →
          c ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im
```
`baImmLower_holds` (file `:414-420`): `c := κ ^ 5 / 64` chosen right after `0 < κ`, before `L, g, E, m, η`
(quantifier order of the pin kept, §18); premises `3 ≤ d`, `0 < Λ`, `0 < g`, `g ≤ Λ` introduced as `_` (unused,
listed in the prove report as the ticket requires); `3 ≤ L` used only for `NeZero L`. General at every `d`, `Λ`, `κ`:
not a special case or a conditional adapter.

Mathematics vs ticket (M2–M6): target 1 constant 2, hypotheses `0 ≤ Im z, Im z'` and two `BASelf`; target 2 window
`0 < η ≤ κ³/4`, bound `κ/2`; target 3 every `η > 0`, bound `ηκ²/(η+3)²`; target 4 `η ∈ (0,1]`, `κ⁵/64`; target 6
`BAbulk κ` gives `(πκ)⁵/64`. All six match the ticket and the check file (compiled equality above).

## 3. Hidden hypotheses, vacuity, cycles
- Hypotheses of the public theorems are merged data predicates only: `BASelf` (`0 < m.im ∧ m = N⁻¹ tr BAMB`),
  `BAReal` (`BASelf … E m ∧ κ ≤ m.im`), `BAbulk` (`κ ≤ BArho`), plus order relations. No new structure, no new
  public `def`, no `def … : Prop` (public declarations of the file):
```
252:theorem BASelf_sub_le ...   302:theorem BAm_im_ge_half ...   327:theorem BAm_im_ge_mul ...
391:theorem BAm_im_lower ...    414:theorem baImmLower_holds ... 424:theorem BAm_im_lower_of_bulk ...
```
  Every other declaration is `private` with prefix `ImmLower_` (§3 (E)).
- No external hypothesis (unconditional proof; §90 not triggered), so no limit check is owed.
- Imports: `RBM3D.BA.Ward`, `RBM3D.BA.CouplingWindow`, `Mathlib.Algebra.Order.Chebyshev`, `Mathlib.Analysis.Complex.Norm`
  (exactly the ticket's four; all merged; no `RBM3D`, no `BA.Boundary`). New file, so no cycle.
- Name clash (audit worktree, outside `ImmLower.lean`, `Probe/` excluded):
```
$ grep -rnw -E "BASelf_sub_le|BAm_im_ge_half|BAm_im_ge_mul|BAm_im_lower|baImmLower_holds|BAm_im_lower_of_bulk|ImmLowerInst" RBM3D --include='*.lean' | grep -v ImmLower.lean | grep -v Probe | wc -l
       0
$ grep -rn "ImmLower_" RBM3D --include='*.lean' | grep -v "^RBM3D/BA/ImmLower.lean" | wc -l
       0
```

## 4. Compiled nonempty instances (namespace `RBM.BA.ImmLowerInst`, file `:434-479`, built in §1)
Data: `d = 3`, `L = 4`, the merged flow point `g0P = √t0P·10` (`g0P_pos : 0 < g0P`, `g0P_le : g0P ≤ 10`),
`EP`, `m0P`, `κ = (mS 4 10).im > 0` (`(selfS 4 10).1`); `flowP_real : BAReal 3 4 g0P (mS 4 10).im EP m0P`
(`CouplingWindow.lean:878`, merged theorem). Every hypothesis discharged; none left open:
| target | instance | hypotheses discharged by |
|---|---|---|
| 1 `BASelf_sub_le` | (I3), `z = EP`, `z' = EP + iη` | `by simp`, `hz'.le`, `flowP_data.2.2`, `BAm_self … hz'` |
| 2 `BAm_im_ge_half` | `η = κ³/4` (end of range) | `(selfS 4 10).1`, `flowP_real`, `div_pos …`, `le_rfl` |
| 3 `BAm_im_ge_mul` | `η = 1` | `(selfS 4 10).1`, `flowP_real`, `one_pos` |
| 4 `BAm_im_lower` | (I2), `∀ η ∈ (0,1]` | `(selfS 4 10).1`, `flowP_real` |
| 5 `baImmLower_holds` | (I1) `BAImmLower 3 Λ κ` | no hypotheses (theorem is hypothesis-free); its body is a wrapper of target 4, exercised by (I2) |
| 6 `BAm_im_lower_of_bulk` | (I4), `κ = Im mS/π` | `div_pos … Real.pi_pos`; `BAbulk` proved from `BAm_real_eq_of_self` + `flowP_real.2` |
No `N = 0` (`N = 64`), no empty index, no collapsed window (`η` ranges `(0,1]`, `(0, κ³/4]`, `(0, ∞)`), no `False`
premise, no large witness (`κ ≈ 0.262`, `g0P ≈ 4.67` per the prove report's numerics).

## 5. Paper deltas
```
$ git show main:docs/paper-deltas.md | grep -n "D403"
1362:- **D403（T2161b）**：体内条件 `|E| ≤ e_λ − κ`（`1_2:649`、`7_8:1817`）与 `lem:propM`(2) 的 `Im m ≳ 1`（`7_8:1908`）…按 §51 改为 `ρ_N(E) ≥ κ`。…
$ sed -n 1867,1868p paper/tex/7_8_light_weight.tex
\item[(2)] {\bf Ward's identity}: We have \(|m|\le 1\),
\(\im m\gtrsim 1\), and %the following identity
```
The only Lean/paper difference of the targets (the `ρ`-bulk in place of `|E| ≤ e_λ − κ`) is D403. The off-axis
form (`η ∈ (0,1]`) is the shape of the merged pin `BAImmLower` (T2189/T2161), not introduced here; targets 1 and 3
are auxiliary lemmas with no paper statement to differ from. No new candidate needed.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. (I1) applies `baImmLower_holds` at `d = 3` with `Λ`, `κ` free, as the ticket specifies; since the theorem has no
  hypotheses, concrete nonvacuity of the pin's inner premise `BAReal` is shown by (I2) at the merged flow point.
- O2. Four `set_option linter.*` lines (`:39-42`) disable style/unused linters for the file; harmless.
- O3. The prove report did not rerun the ticket's Preflight (viii) multi-`(L, g)` numerics (it says so); the Lean
  statements are unconditional and compiled, so this changes nothing.

## Verdict
| target | statement | hidden hyp./vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `BASelf_sub_le` | = pin | none | (I3) | ok | n/a | PASS |
| 2 `BAm_im_ge_half` | = pin | none | `η = κ³/4` | ok | D403 | PASS |
| 3 `BAm_im_ge_mul` | = pin | none | `η = 1` | ok | D403 | PASS |
| 4 `BAm_im_lower` | = pin | none | (I2) | ok | D403 | PASS |
| 5 `baImmLower_holds` | = merged pin | none | (I1)+(I2) | ok | D403 | PASS |
| 6 `BAm_im_lower_of_bulk` | = pin | none | (I4) | ok | D403 | PASS |

**T2291: PASS.** No dispatcher sign-off needed.
