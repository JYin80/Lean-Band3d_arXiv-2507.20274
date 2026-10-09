Auditor model: claude-opus-5-5

# T2357 audit (round 1): BA-P8 `RBM3D/BA/Prop6Path.lean`

Written: Fri Oct  9 01:46:52 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2357-audit1`, detached at `t/T2357` = `67fa717`
(merge-base with `main` `01ea41d`; `main` now `5d7a660`).

## 1. Statements against the pins (check-file equality)

Scratch file = check-file imports + `import RBM3D.BA.Prop6Path` + check section 2 + one
`example : RBM.BA.T2357Check.T2357_X := RBM.BA.X` per target + `#print axioms`:
```
$ grep -c example eq.lean
5
$ lake env lean eq.lean; echo "exit $?"
'RBM.BA.baProp5_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProp6_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProp7_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProp8_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProp5to8_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop6PathInst.inst_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop6PathInst.inst_prop6_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop6PathInst.inst_reduction8' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Signatures (file, `grep -n '^theorem'`):
```
850:theorem baProp5_holds (d : ℕ) (Λ κ : ℝ) : BAProp5 d Λ κ := by
891:theorem baProp6_holds (d : ℕ) (Λ κ c : ℝ) : BAProp6 d Λ κ c := by
941:theorem baProp7_holds (d : ℕ) (Λ κ c : ℝ) : BAProp7 d Λ κ c := by
1009:theorem baProp8_holds (d : ℕ) (Λ κ : ℝ) : BAProp8 d Λ κ := by
1049:theorem baProp5to8_holds (d : ℕ) (Λ κ c : ℝ) : BAProp5to8 d Λ κ c :=
```
The targets are unconditional over `(d, Λ, κ, c)`; all hypotheses (`3 ≤ d`, `0 < Λ`, `0 < κ`, `0 < c < 1`,
then `∃ C` before `∀ L g E m`, `BAReal`, `t ∈ [0,1)`, all `σ₁ σ₂`, `|r| ≤ c|a|`) are those of the merged,
unmodified pin defs `FlowPins.lean:165-227` (read in full). Quantifier order: constants fixed before `L, g`,
as pinned; all four charge pairs covered (the proofs case-split `σ₁ = σ₂` / `σ₁ ≠ σ₂`, e.g. `:871 by_cases hσ`).
Not a special case.

## 2. Vacuity, hidden hypotheses, cycles

- No hypothesis in a structure field: `BAProp5to8` is the merged pin bundle; `baProp5to8_holds` builds all five
  fields (`:1049-1051`) from the four targets and the merged `baProp5s_holds`.
- Dependencies are merged results on `main`: `baProp5s_holds`, `baProp5mixed_holds`, `baProp8mixed_holds`,
  `baPropUnit1mixed_holds`, `baPropUnit2mixed_holds` (check section 1 compiled at release). No external
  hypothesis is introduced; nothing to limit-check.
- `BAReal` is nonvacuous: `MFixedPointInst.P : FlowPt 4 10` (`MFixedPoint.lean:877-893`) carries
  `real : BAReal 3 L g0 m0.im E m0` with `0 < g0 ≤ 10`, built from `exists_flowPt`.
- Copied band lemmas, verbatim up to renaming:
```
$ diff <(sed -n 45,349p RBM3D/Propagator/Prop6Hold.lean | sed -e "s/p6hQ/baP8_Q/g" -e "s/p6h_/baP8_/g") \
       <(sed -n 52,356p RBM3D/BA/Prop6Path.lean); echo diff-exit=$?
diff-exit=0
```
  `grep -cE "^private (theorem|lemma) baP8_"` = 30; the only public names are the five targets and the
  `Prop6PathInst` instances.

## 3. Compiled nonempty instances (`namespace RBM.BA.Prop6PathInst`, `:1060-1176`)

- `inst_bundle : BAProp5to8 3 10 P.m0.im (1 / 2)` (the ticket's instance).
- `example := inst_BAProp5/6/7/8 (baPropX_holds 3 10 P.m0.im …)`: applies each target to the merged FlowPins
  instances, e.g.
```
#check @RBM.BA.FlowPinsInst.inst_BAProp6
RBM.BA.FlowPinsInst.inst_BAProp6 : RBM.BA.BAProp6 3 10 RBM.BA.MFixedPointInst.P.m0.im (1 / 2) →
  ∃ C, 0 < C ∧ ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 (![2, 0, 0] + ![1, 0, 0]) -
            BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![2, 0, 0]‖ ≤
        C * (P.g0 ^ 2 + |1 - 1 / 2|)⁻¹ * ↑(zdistD 3 4 ![1, 0, 0]) * ((↑(zdistD 3 4 ![2, 0, 0]) + 1) ^ (3 - 1))⁻¹
```
- Equal-charge instances `inst_prop5_eq` (`σ=(-,-)`, `a=(2,0,0)`), `inst_prop5_eq_zero` (`a=0`),
  `inst_prop6_eq`, `inst_prop7_eq` (`a=(2,0,0)`, `r=(1,0,0)`, `|r| = 1 ≤ (1/2)·2`, window discharged by
  `rw [zd_a, zd_r]; norm_num`), `inst_prop8_eq` (`a=(1,0,0)`), and the reductions `inst_reduction5/6/8`
  (ticket: `d = 3`, `L = 4`, `a = ![1,0,0]`, present as `inst_reduction5`, `inst_reduction8`).
- Data: `d = 3`, `L = 4` (`3 ≤ L`), `Λ = 10`, `κ = Im m₀ > 0` (`P.real.1.1`), `g = P.g0 ∈ (0,10]`, `t = 1/2`,
  `c = 1/2`; every deterministic hypothesis discharged by `norm_num`/`P` fields; no open hypothesis. Not degenerate
  (no `N = 0`, nonempty lattice, nonzero `a`, non-collapsed window).

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.BA.Prop6Path RBM3D.Test.Axioms 2>&1 | grep -E "Prop6Path|Axioms|error|Build completed"
✔ [3748/3748] Built RBM3D.Test.Axioms (2.0s)
Build completed successfully (3748 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/BA/Prop6Path.lean; echo grep-exit $?
grep-exit 1
$ sed -n 1,30p RBM3D/BA/Prop6Path.lean | grep -n import
6:import RBM3D.BA.Prop5
7:import RBM3D.BA.PropUnit
8:import RBM3D.BA.Prop5Short
9:import RBM3D.BA.FlowPins
$ git diff --stat main...HEAD
 RBM3D/BA/Prop6Path.lean | 1178 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    5 -
 2 files changed, 1178 insertions(+), 5 deletions(-)
```
Axioms.lean hunk removes exactly `RBM.BA.BAProp5`, `BAProp6`, `BAProp7`, `BAProp8`, `BAProp5to8` (old lines
137-141); no line added. Frozen signatures: no other file touched.

Registry pre-check (root `RBM3D.lean` copied to scratch with `import RBM3D.BA.Prop6Path` inserted after the
last `import`, as the hub does at merge):
```
$ lake build RBM3D 2>&1 | grep -E "error" | head -2      # committed root, no new import yet (expected)
error: RBM3D.lean:398:0: axiom audit: 5 premise(s) that no theorem of this development proves are in none of …
error: build failed
$ lake env lean root.lean   (root + import RBM3D.BA.Prop6Path)
axiom audit: 10505 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: …
exit 0   (0 lines matching "error")
```
Merge against current `main`:
```
$ git merge-tree --write-tree main t/T2357 >/dev/null; echo merge-tree-exit=$?
merge-tree-exit=0
$ git diff --stat 01ea41d main -- RBM3D/BA/{FlowPins,Prop5,PropUnit,Prop5Short}.lean RBM3D/Propagator/Prop6Hold.lean RBM3D/Test/Axioms.lean
 RBM3D/Test/Axioms.lean | 1 -
```
(the T2355 line, disjoint hunk; upstream dependencies unchanged since the branch point).

Name clash: `grep -rln "baProp5_holds|…|baProp5to8_holds|Prop6PathInst" RBM3D | grep -v /Probe/` →
`RBM3D/BA/Prop6Path.lean` only.

## 5. Paper deltas

The Lean statements are the merged pins of T2197 (`FlowPins.lean`), unchanged; the ticket introduces no new
Lean/paper statement difference. The prove report proposes none (`(d) 2`); none needed.

## Verdicts

| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `baProp5_holds` | = pin | none | compiled | ok | n/a | PASS |
| `baProp6_holds` | = pin | none | compiled | ok | n/a | PASS |
| `baProp7_holds` | = pin | none | compiled | ok | n/a | PASS |
| `baProp8_holds` | = pin | none | compiled | ok | n/a | PASS |
| `baProp5to8_holds` | = pin | none | compiled | ok | n/a | PASS |

Observations (no effect on statement, instance, build, axioms, or deltas):
1. The file is 1178 lines (ticket size 600/800/1100; stop rule threshold 1300 not crossed).
2. `inst_reduction5/6/8` mention the private `baP8_S` in their statements (they compile; nothing imports them).
3. The committed root `RBM3D.lean` fails the root audit until the hub adds the import at merge (expected;
   verified exit 0 with the import).

**Overall: PASS.** No dispatcher sign-off needed.
