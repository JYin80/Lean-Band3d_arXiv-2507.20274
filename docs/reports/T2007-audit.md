Auditor model: claude-opus-5-5

# T2007 audit (round 2, scope: Amend 1 only) — Sat Oct  3 00:45:03 UTC 2026
Branch `t/T2007` at `64e6082` (parent `29230e9` = round-1 audited commit; merge base with main `6a555f7`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2007-audit2` (detached).
Round 1 (`29230e9`, auditor claude-opus-5-5, Sat Oct 3 00:14:11 UTC 2026): "Ticket T2007: **PASS**. No dispatcher sign-off needed." (Target 1 Pins.lean PASS, Target 2 `prop5Short_holds` PASS.) That verdict carries over by hash (§2).
Merge simulation worktree (scratch, not committed): `.../scratchpad/merge2007` = `main` (`315e65e`) + the three branch files + the two root imports after the last `import` line.

## 1. Amend diff: confined to the two lists and the docstring
```
$ git diff --name-status 29230e9 HEAD
M	RBM3D/Test/Axioms.lean
$ git diff --name-status main...HEAD
A	RBM3D/Propagator/Pins.lean
A	RBM3D/Propagator/Prop5Short.lean
M	RBM3D/Test/Axioms.lean
$ git diff -U0 29230e9 HEAD -- RBM3D/Test/Axioms.lean | grep '^@@'
@@ -72 +72,4 @@ Reporting them in one list makes "zero axioms" look better than the situation is
@@ -75 +78,2 @@ def borrowedProps : List Name :=
@@ -97 +101,6 @@ def structuralProps : List Name :=
```
Hunk 1 = docstring of `borrowedProps`; hunk 2 = `borrowedProps` list tail; hunk 3 = `structuralProps` list tail. `owedProps`, certificate lists and all other code untouched.
```
$ git diff 29230e9 HEAD -- RBM3D/Test/Axioms.lean    (verbatim, hunks 1-3)
-/-- Premises the **paper** cites rather than proves. -/
+/-- Premises the **paper** cites rather than proves.  The pins of `lem_propTH` properties
+5–8 (T2003, DECISIONS §13) and their KL-local form (T2004, §15) replace the old `ThetaDecay`
+… `PropTH` as the statements route H (DECISIONS §14) discharges; they are not authorised
+external inputs (DECISIONS §5), so they must end up proved. -/
 def borrowedProps : List Name :=
   [`RBM.ThetaDecay, `RBM.ThetaDecayShort, `RBM.ThetaDiffOne, `RBM.ThetaDiffTwo,
-   `RBM.ThetaZeroMode, `RBM.PropTH, `RBM.Loop.KTreeRep]
+   `RBM.ThetaZeroMode, `RBM.PropTH, `RBM.Loop.KTreeRep,
+   `RBM.Prop5Decay, `RBM.Prop8ZeroMode, `RBM.Prop5to8, `RBM.Loop.KLPT]
...
-   `RBM.NormStochDom]         -- `‖A‖ ≺ ζ`: notation of `(stoch_domination)`, not a result
+   `RBM.NormStochDom,         -- `‖A‖ ≺ ζ`: notation of `(stoch_domination)`, not a result
+   `RBM.Gauss.Sizes.WO,       -- `(eq:WO)`: the window of the size sequence
+   `RBM.Gauss.Sizes.Bandwidth, -- `(Main_DEL_COND)`: `W ≥ N^𝔠`
+   `RBM.Gauss.Sizes.SizeTendsto, -- `N → ∞` along the size sequence
+   `RBM.Gauss.Sizes.Admissible, -- the standing hypotheses of the main results
+   `RBM.Gauss.Sizes.locDomain] -- the spectral domain `𝐃_{κ,ε}`
```
Net registry names (removed vs added backtick names in the diff):
```
net added:
RBM.Gauss.Sizes.Admissible
RBM.Gauss.Sizes.Bandwidth
RBM.Gauss.Sizes.locDomain
RBM.Gauss.Sizes.SizeTendsto
RBM.Gauss.Sizes.WO
RBM.Loop.KLPT
RBM.Prop5Decay
RBM.Prop5to8
RBM.Prop8ZeroMode
net removed:
end
```
Exactly the nine names of Amend 1 items 1–2, each in the list the amend names; docstring is the one sentence the amend prescribes; each structural entry carries the prescribed one-line comment.

Names resolve to real declarations:
```
$ grep -nE "^namespace|^def (WO|Bandwidth|SizeTendsto|Admissible|locDomain)\b" RBM3D/Defs/Sizes.lean   (main)
36:namespace RBM.Gauss      148:namespace Sizes
164:def WO   168:def Bandwidth   173:def SizeTendsto   177:def Admissible   186:def locDomain
$ git show t/T2008:RBM3D/Loop/KLTree.lean | grep -nE "^namespace|structure KLPT"
29:namespace RBM.Loop
321:structure KLPT (d : ℕ) (κ gmax : ℝ) : Prop where
```
(`Prop5Decay`, `Prop8ZeroMode`, `Prop5to8` are in namespace `RBM` in `Pins.lean`, round 1.)

## 2. Unchanged rest by hash
```
$ git rev-parse 29230e9:RBM3D/Propagator/Pins.lean HEAD:RBM3D/Propagator/Pins.lean \
                29230e9:RBM3D/Propagator/Prop5Short.lean HEAD:RBM3D/Propagator/Prop5Short.lean
e10c2bf1f2d17397bb11dd31b42425458ab42098
e10c2bf1f2d17397bb11dd31b42425458ab42098
06a0f608bc6c2060dc490491f9842ab4626516be
06a0f608bc6c2060dc490491f9842ab4626516be
$ git rev-parse 6a555f7:RBM3D/Test/Axioms.lean main:RBM3D/Test/Axioms.lean 29230e9:RBM3D/Test/Axioms.lean
8d2eae3961cddcb5ad9200c6a4e698dd61f0ac0a
8d2eae3961cddcb5ad9200c6a4e698dd61f0ac0a
8d2eae3961cddcb5ad9200c6a4e698dd61f0ac0a
```
Statements, proofs and instances of both targets are byte-identical to round 1 (PASS). `Axioms.lean` on `main` equals the base, so bringing in the branch file at merge drops no main change.
```
$ git diff 29230e9 HEAD | grep -nE '^\+.*(sorry|admit|native_decide|^\+\s*axiom )'; echo grep_exit=$?
grep_exit=1
```

## 3. Builds
Branch, full build (root does not import the two new modules; root imports are the hub's at merge):
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2007-audit2 && lake build 2>&1 | grep -E "error|axiom audit:|premises found|^registry|Build completed"
info: RBM3D.lean:45:0: axiom audit: 510 theorems, 173 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 11 (borrowed 4, owed 1, structural 6).
registry: 11 borrowed + 2 owed + 11 structural; 13 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
Build completed successfully (3254 jobs).
exit=0
$ lake build RBM3D.Propagator.Pins RBM3D.Propagator.Prop5Short RBM3D.Test.Axioms 2>&1 | grep -E "error|sorry|Build completed"
Build completed successfully (2436 jobs).
exit=0
```
Merge simulation (main `315e65e` + branch files + `import RBM3D.Propagator.Pins`, `import RBM3D.Propagator.Prop5Short` after line 47, `#assert_rbm_axioms` still last):
```
$ lake build 2>&1 | grep -E "error|axiom audit:|premises found|^registry|Build completed"
info: RBM3D.lean:52:0: axiom audit: 643 theorems, 239 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 11 (borrowed 4, owed 1, structural 6).
registry: 11 borrowed + 2 owed + 11 structural; 13 registered premise(s) carry nothing yet: [RBM.ThetaDecay,
Build completed successfully (3690 jobs).
exit=0
$ lake build RBM3D 2>&1 | sed -n '/axiom audit/,/non-vacuity/p'     (excerpt)
All within [propext, Classical.choice, Quot.sound]; no project axioms ...
  RBM.Prop5Decay: 0 [no certificate]
  RBM.Prop8ZeroMode: 0 [no certificate]
  RBM.Prop5to8: 0 [no certificate]
  RBM.Loop.KLPT: 0 [no certificate]
 ... carry nothing yet: [..., RBM.Loop.KLPT, RBM.Loop.KLoopBound, RBM.Gauss.Sizes.WO, RBM.Gauss.Sizes.Bandwidth,
 RBM.Gauss.Sizes.SizeTendsto, RBM.Gauss.Sizes.Admissible, RBM.Gauss.Sizes.locDomain].
```
Negative control (same simulation with main's `Axioms.lean`, i.e. without the amend):
```
$ git checkout HEAD -- RBM3D/Test/Axioms.lean && lake build 2>&1 | grep -E "^error|none of"
error: RBM3D.lean:52:0: axiom audit: 3 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
error: build failed
exit=1
```
The amend is what makes the root `#assert_rbm_axioms` pass at merge; axioms of the whole `RBM` namespace remain `propext`, `Classical.choice`, `Quot.sound`.

## 4. Prove report `Amend 1` section
Present (`docs/reports/T2007-prove.md:212`), with the `Axioms.lean` diff and the final info line `registry: 11 borrowed + 2 owed + 11 structural`; my counts agree. Report length 279 lines (≤ 300).

## 5. Paper deltas
The amend changes the registry only, no Lean statement; no new Lean/paper difference. Round-1 coverage (T2003a–f, T2004d) unchanged.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. On the branch (base `6a555f7`) `RBM.Gauss.Sizes.*` and `RBM.Loop.KLPT` do not exist; the single-backtick `Name` literals are not resolved, so the branch build passes; on main the Sizes names resolve (T2006 merged), `KLPT` resolves once T2008 merges.
- O2. In the merge simulation `Prop5Decay`, `Prop8ZeroMode`, `Prop5to8` show "0 theorems resting" but are absent from the "carry nothing" list (they are found by the scan); this is the registry's reporting, not a defect of the amend.
- O3. The hub must add the two root imports at merge; without them the root audit does not see the new modules (prove report says the same).

## Verdicts
- Amend 1 (`RBM3D/Test/Axioms.lean`: 4 names in `borrowedProps` + docstring sentence, 5 names in `structuralProps` with comments): **PASS**.
- Target 1 (`Propagator/Pins.lean`) and Target 2 (`prop5Short_holds`): unchanged by hash from round 1: **PASS** (carried).
Ticket T2007: **PASS**. No dispatcher sign-off needed.
