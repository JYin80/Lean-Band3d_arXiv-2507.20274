Auditor model: claude-opus-5-5

# T2027 audit (round 1) — Sat Oct  3 05:45:01 UTC 2026

Branch `t/T2027` @ ebdab34 (base 1892ec6). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2027-audit1` (detached at ebdab34).
Merge simulation worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2027-audit1-merge` (detached at main c8bedf7, the two branch files checked out, root import added; scratch only, nothing committed).

## 1. Files touched
```
$ git diff --stat main...t/T2027
 RBM3D/Propagator/Prop6Hold.lean | 560 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |  12 +-
$ git diff --stat 1892ec6 main -- RBM3D/Test/Axioms.lean     # main did not touch Axioms.lean since the base
(empty)
$ sed -n 1,25p Prop6Hold.lean | grep '^import'
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.PropUnit
import RBM3D.Propagator.Gap
```
Only the sole writable files; imports as the ticket allows (no `import RBM3D`).

## 2. Statements against the pins
Every target's type is the merged pin by name (`Pins.lean:58 Prop6Diff1`, `:73 Prop7Diff2`, `:98 Prop5to8`; `Interface.lean:77 ThetaDecay`, `:101 ThetaDecayShort`, `:149 ThetaZeroMode`); no pin edited (`git diff` touches neither file).
```
$ grep -nE '^\s*(theorem|lemma|def|abbrev|instance|structure)\s' Prop6Hold.lean   # non-private declarations
353:theorem prop6Diff1_holds (d : ℕ) (Λ κ c : ℝ) : Prop6Diff1 d Λ κ c := by
384:theorem prop7Diff2_holds (d : ℕ) (Λ κ c : ℝ) : Prop7Diff2 d Λ κ c := by
433:theorem prop5to8_holds (d : ℕ) (Λ κ c : ℝ) : Prop5to8 d Λ κ c :=
438:theorem thetaDecay_holds (d : ℕ) (g : ℝ) (m : ℂ) : ThetaDecay d g m :=
443:theorem thetaDecayShort_holds (d : ℕ) (g : ℝ) (m : ℂ) : ThetaDecayShort d g m :=
448:theorem thetaZeroMode_holds (d : ℕ) {Λ κ g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ)
489:theorem thetaZeroMode_unit_holds (d : ℕ) (g : ℝ) (μ : ℂ) : ThetaZeroMode d g μ := by
```
Ticket pins (T2027 targets 1–3) vs file: identical binder lists and conclusions for items 1, 2 and the `ThetaDecay`/`ThetaDecayShort` forms.
`thetaZeroMode_holds` has exactly the hypotheses of `Prop8ZeroMode.thetaZeroMode` (`Pins.lean:334`: `hg hgΛ hκ hm hmi σ₁ σ₂`, conclusion `ThetaZeroMode d g (PropSpin m σ₁ * PropSpin m σ₂)`), as item 3 requires.
`thetaZeroMode_unit_holds` is additional and stronger (all `d g μ`); it is proved from `thetaZeroMode_holds` via the private `p6h_exists_spin` (every unit `μ` equals `m(σ₁)m(σ₂)` with `‖m‖ = 1`, `Im m > 0`), so no consumer `μ` is left unlisted. This justifies removing `ThetaZeroMode` from the registry.
Type check by elaboration (merged tree, `lake env lean pre27.lean`, exit 0):
```
example : ∀ d Λ κ c, Prop6Diff1 d Λ κ c := prop6Diff1_holds
example : ∀ d Λ κ c, Prop7Diff2 d Λ κ c := prop7Diff2_holds
example : ∀ d Λ κ c, Prop5to8 d Λ κ c := prop5to8_holds
example : ∀ d g m, ThetaDecay d g m := thetaDecay_holds
example : ∀ d g m, ThetaDecayShort d g m := thetaDecayShort_holds
example : ∀ d g μ, ThetaZeroMode d g μ := thetaZeroMode_unit_holds
```
Pin content checked against the ticket's mathematics (Pins.lean:58–90): P6 is `‖Θ(a+r) − Θ(a)‖ ≤ C (g²+|1−t|)⁻¹ |r| (|a|+1)^{-(d−1)}` and P7 is `‖Θ(a+r)+Θ(a−r)−2Θ(a)‖ ≤ C (g²+|1−t|)⁻¹ |r|² (|a|+1)^{-d}`. In both, `C` depends on `(d,Λ,κ,c)` and is quantified before `L, g, t, m, σ₁, σ₂, a, r`; `|r| ≤ c|a|`; `0<c<1`; bulk `κ ≤ Im m`; no loss. The statements are the pins themselves, so no special case or adapter stands in for a target.

## 3. Hidden hypotheses, vacuity, cycles
- No target takes a `Prop` hypothesis. `prop5to8_holds` is built from `prop5Decay_holds`, `prop5Short_holds`, `prop8ZeroMode_holds` (all merged on main, T2023/T2024) and the two new theorems. `Prop5to8` is a pin structure whose fields are exactly the five pins, and nothing is hidden in it.
- No external hypothesis, so no limit check is needed. No cycle: the file imports only `Prop5Hold`, `PropUnit` and `Gap`.
- Pin premises `3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1` are satisfiable at the instance below, so the targets are not vacuous.

## 4. Compiled nonempty instances (Prop6Hold.lean:502–560, built)
- `prop6Diff1_holds 3 1 (1/2) (1/2)` and `prop7Diff2_holds 3 1 (1/2) (1/2)` are applied at `L = 9`, `g = 1/2`, `t = 9/10`, `m = Complex.I`, `σ = (true,false)`, `a = ![4,0,0]`, `r = ![1,0,0]`. Every hypothesis is discharged by `le_rfl`/`norm_num`/`Complex.norm_I`/`decide` (`zdistD 3 9 ![4,0,0] = 4`, `zdistD 3 9 ![1,0,0] = 1`, `1 ≤ (1/2)·4`). This is the ticket's data.
- `prop5to8_holds 3 1 (1/2) (1/2)` and its `.diffOne` are covered.
- `thetaDecay_holds 3 (1/2) I` and `thetaDecayShort_holds 3 (1/2) I` are covered.
- `thetaZeroMode_holds` is applied at `Λ = 1`, `κ = 1/2`, `g = 1/2`, `m = I`, `(true,false)` with all hypotheses discharged. `thetaZeroMode_unit_holds 3 (1/2) (-1)` is also covered.
- None is degenerate: `d = 3`, `L = 9`, `a ≠ 0`, `r ≠ 0`, the window `|r| ≤ c|a|` holds strictly, and no premise is `False`.

## 5. Builds and axioms
Target module, audit worktree:
```
$ lake build RBM3D.Propagator.Prop6Hold; echo exit=$?
exit=0
$ grep -cE 'Prop6Hold.lean:.*(error|warning)' b27.out
0
Build completed successfully (3410 jobs).
```
Full build on the branch as is, without the root import (observation, see §7):
```
$ lake build; echo exit=$?
error: RBM3D.lean:70:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Prop5to8]
exit=1
```
Merge simulation is hub steps A.3–A.5 on current main c8bedf7, with `import RBM3D.Propagator.Prop6Hold` added after the last import (`import RBM3D.Loop.KLUnique`):
```
$ git diff RBM3D.lean | grep '^[-+]'
+import RBM3D.Propagator.Prop6Hold
$ lake build; echo exit=$?
exit=0
info: RBM3D.lean:72:0: axiom audit: 1065 theorems, 400 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
theorems resting on each premise the PAPER borrows:
  RBM.ThetaDiffOne: 1 [certificate: RBM.Test.thetaDiffOne_fixedL]
  RBM.ThetaDiffTwo: 1 [certificate: RBM.Test.thetaDiffTwo_fixedL]
  RBM.PropTH: 1 [certificate: RBM.Test.propTH_fixedL]
  RBM.Loop.KTreeRep: 0 [no certificate]
  RBM.Loop.KLPT: 0 [no certificate]
theorems resting on each premise THIS FORMALIZATION owes:
  RBM.Loop.TwoLoopBounded: 7 [certificate: RBM.Test.twoLoopBounded_kTwoLoop]
  RBM.Loop.KLoopBound: 0 [no certificate]
premises found by scanning: 7 (borrowed 2, owed 0, structural 5).
registry: 5 borrowed + 2 owed + 13 structural; ...
Build completed successfully (3730 jobs).
```
DECISIONS §20 pre-check (Amend 1), with scratch file `import RBM3D`, `import RBM3D.Propagator.Prop6Hold`, the six type examples above, `#print axioms` and `#assert_rbm_axioms`, run in the merged tree:
```
$ lake env lean pre27.lean; echo exit=$?
exit=0
'RBM.prop6Diff1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.prop7Diff2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.prop5to8_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.thetaDecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.thetaDecayShort_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.thetaZeroMode_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.thetaZeroMode_unit_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 1065 theorems, 400 definitions, 0 axioms in `RBM` ...
```
Hygiene:
```
$ grep -nE 'sorry|admit|native_decide|^axiom|^\s*axiom ' Prop6Hold.lean | wc -l
       0
```

## 6. Registry diff (DECISIONS §16)
```
$ git diff main...t/T2027 -- RBM3D/Test/Axioms.lean | grep '^[-+]' (abridged to the changed lines)
-  [`RBM.ThetaDecay, `RBM.ThetaDecayShort, `RBM.ThetaDiffOne, `RBM.ThetaDiffTwo,
-   `RBM.ThetaZeroMode, `RBM.PropTH, `RBM.Loop.KTreeRep,
-   `RBM.Prop5Decay, `RBM.Prop8ZeroMode, `RBM.Prop5to8, `RBM.Loop.KLPT]
+  [`RBM.ThetaDiffOne, `RBM.ThetaDiffTwo, `RBM.PropTH, `RBM.Loop.KTreeRep, `RBM.Loop.KLPT]
-  [(`RBM.ThetaDecay, `RBM.Test.thetaDecay_fixedL),
-   (`RBM.ThetaZeroMode, `RBM.Test.thetaZeroMode_fixedL),
-   (`RBM.ThetaDiffOne, `RBM.Test.thetaDiffOne_fixedL),
+  [(`RBM.ThetaDiffOne, `RBM.Test.thetaDiffOne_fixedL),
+ ... so they must end up proved.  Route H proved `lem_propTH`
+5–8 for every `d ≥ 3` (T2023, T2024, T2027), so `Prop5Decay`, `Prop8ZeroMode`, `Prop5to8`,
+`ThetaDecay`, `ThetaDecayShort` and `ThetaZeroMode` left this list. -/
```
- The six listed premises are removed. `ThetaZeroMode` is removed because `thetaZeroMode_unit_holds` proves it for every `μ`.
- The two certificates whose premise was removed are dropped; the kept entries are exactly those the ticket lists; one docstring sentence added.
- No further `Prop` hypothesis is introduced, so no §20 registration is needed.

## 7. Paper deltas and observations
- Paper deltas: the targets are the merged pins, and the reading `|r| ≤ c|a|`, `0<c<1` is covered by D12 (`docs/paper-deltas.md:144`). `thetaZeroMode_unit_holds` proves the merged interface form without adding a new Lean/paper difference. No new candidate is needed, and the report proposes none. Coverage is complete.
- Observation 1: the branch alone fails `lake build` (unregistered premise `RBM.Prop5to8`) until the hub adds the root import. This is the expected merge-time state. The merge simulation in §5 (root import after `import RBM3D.Loop.KLUnique`, main c8bedf7) passes, so the hub should add the import after the current last import line.
- Observation 2: the prove report's (b) predates Amend 1. It has no separate §20 scratch pre-check; its full build with a temporary root import is equivalent. §5 above runs the pre-check (exit 0).
- Observation 3: at the ticket's instance, the P6 left side is 0 by symmetry, as the prove report says. The instance is still nondegenerate in the sense of CLAUDE.md §4: all hypotheses are discharged at nontrivial data, and the P7 instance has a nonzero left side.

## Verdicts
| target | verdict |
|---|---|
| `prop6Diff1_holds` | PASS |
| `prop7Diff2_holds` | PASS |
| `prop5to8_holds` | PASS |
| `thetaDecay_holds`, `thetaDecayShort_holds` | PASS |
| `thetaZeroMode_holds` (+ `thetaZeroMode_unit_holds`) | PASS |
| registry update (`Test/Axioms.lean`) | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
