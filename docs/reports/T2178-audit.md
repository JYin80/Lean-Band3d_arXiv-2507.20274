Auditor model: claude-opus-5-5

# T2178 audit (round 2, amend 1). Mon Oct  5 06:44:56 UTC 2026

Scope (`docs/tickets/T2178-amend-1.md`): the `RBM3D/Test/Axioms.lean` diff (one registry line in `structuralProps`) and the registry pre-check. Branch `t/T2178` at `a28f98e`; merge-base `d5e2848`; `main` = `52c856e`. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2178-audit2` (detached at `a28f98e`). Endpoints `InjSum_IsTestFun`, `InjSum_stieltjes`, `poissonSmooth_error` were audited in round 1 (PASS at `e90fa53`); the Lean files are unchanged since:
```
$ git log --oneline main..t/T2178
a28f98e T2178: register RBM.Univ.InjSum_IsTestFun in structuralProps (amend 1)
e90fa53 T2178: port Universality/InjSum and PoissonSmoothing (UN-03a)
$ git diff e90fa53 a28f98e --stat
 RBM3D/Test/Axioms.lean | 1 +
 1 file changed, 1 insertion(+)
```

## 1. Statement (the registry line against the amend's pin)
```
$ git diff e90fa53 a28f98e
@@ -265,6 +265,7 @@ def structuralProps : List Name :=
    `RBM.Univ.InWindow, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
    `RBM.Univ.queBadMat, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
    `RBM.Univ.UNBadY, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
+   `RBM.Univ.InjSum_IsTestFun, -- T2178: test-function condition (smooth, compact support) on data; a hypothesis of deterministic lemmas (DECISIONS §20, §56)
    `RBM.Gauss.Sizes.STReg5IV] -- Step 5 regime (iv); S5-01 (T2138, DECISIONS §40)
```
Name and comment match the amend's pinned text character for character (`RBM.Univ.InjSum_IsTestFun`, comment `-- T2178: test-function condition (smooth, compact support) on data; a hypothesis of deterministic lemmas (DECISIONS §20, §56)`). Only the list gains one element; no other line of `Axioms.lean` changes. Classification check: the registered Prop is the deterministic data condition (round-1 elaboration, unchanged file):
```
def RBM.Univ.InjSum_IsTestFun : {k : ℕ} → ((Fin k → ℝ) → ℝ) → Prop := fun {k} O => ContDiff ℝ (↑⊤) O ∧ HasCompactSupport O
```
It is a condition on the test function (no probabilistic or cited content), so `structural` is the right class; it is not a borrowed/owed input.

## 2. Vacuity, hidden hypotheses, cycles
The amend adds no declaration, hypothesis or import; `Axioms.lean` is a registry consumed only by `#assert_rbm_axioms`. Nothing to check beyond round 1.

## 3. Compiled nonempty instances
Unchanged from round 1 (Lean files identical, §0 diff): `PoissonSmoothing.lean:1061` (`poissonSmooth_error` at `k = 1`, `UNInst.bump`, `ε = 1/1000`), `:1071` (`InjSum_IsTestFun` at `UNInst.bump`), `InjSum.lean:600–620` (`InjSum_stieltjes` at diag(1,2,3), `η = 1/10`). Recompiled in the build below.

## 4. Build, axioms, registry pre-check, scope
```
$ lake build RBM3D.Test.Axioms RBM3D.Universality.InjSum RBM3D.Universality.PoissonSmoothing; echo exit=$?
exit=0
$ grep -E "error|warning: declaration uses|sorry" build2.out    (no output)
$ tail -1 build2.out
Build completed successfully (3334 jobs).
$ cat precheck2.lean
import RBM3D
import RBM3D.Universality.InjSum
import RBM3D.Universality.PoissonSmoothing
#print axioms RBM.Univ.InjSum_IsTestFun
#print axioms RBM.Univ.InjSum_stieltjes
#print axioms RBM.Univ.poissonSmooth_error
#assert_rbm_axioms
$ lake env lean precheck2.lean > precheck2.out; echo exit=$?   (196 lines)
exit=0
$ grep -n -iE "error|unregistered|axioms:|^axiom audit|All within|premises found|registry:" precheck2.out
1:'RBM.Univ.InjSum_IsTestFun' depends on axioms: [propext, Classical.choice, Quot.sound]
2:'RBM.Univ.InjSum_stieltjes' depends on axioms: [propext, Classical.choice, Quot.sound]
3:'RBM.Univ.poissonSmooth_error' depends on axioms: [propext, Classical.choice, Quot.sound]
4:axiom audit: 5353 theorems, 1895 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
5:All within [propext,
7: Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
125:premises found by scanning: 102 (borrowed 1, owed 79, structural 22).
126:registry: 2 borrowed + 113 owed + 57 structural; 70 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
```
No `error` and no `unregistered` line: `#assert_rbm_axioms` accepts the library plus both new modules with the new registry.

Scope and hygiene:
```
$ git diff main...t/T2178 --stat
 RBM3D/Test/Axioms.lean                   |    1 +
 RBM3D/Universality/InjSum.lean           |  643 ++++++++++++++++++
 RBM3D/Universality/PoissonSmoothing.lean | 1092 ++++++++++++++++++++++++++++++
 3 files changed, 1736 insertions(+)
$ git diff main...t/T2178 | grep -nE "^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom "    (no output)
$ git diff --stat d5e2848 main -- RBM3D/Test/Axioms.lean RBM3D/Universality/Pins.lean RBM3D/Green/EntryCore.lean    (no output)
$ git diff --stat main t/T2178 -- RBM3D/Test/Axioms.lean
 RBM3D/Test/Axioms.lean | 1 +
 1 file changed, 1 insertion(+)
```
Touched files = the two sole writable files + `RBM3D/Test/Axioms.lean` (writable for this one line by amend 1). `Axioms.lean` and the imported dependencies are unchanged on `main` since the merge-base, so the line applies to current `main` as a one-line insertion. No frozen signature touched.

## 5. Paper deltas
The amend changes no Lean statement; no new Lean/paper difference. Round-1 coverage (T2178a, a non-paper note on `stieltjesN` vs `InjSum_stieltjes` being equal by theorem, not `rfl`) stands.

## Observations (no verdict effect)
- The prove report's pre-check header reads `5324 theorems, 1883 definitions`; this audit's pre-check prints `5353 theorems, 1895 definitions` (same scan totals `102 (borrowed 1, owed 79, structural 22)` and `registry: 2 + 113 + 57`). The verdict-relevant lines (exit 0, no `unregistered`, 0 axioms in `RBM`) agree.
- Pre-check run against the worktree's `RBM3D.lean` (from `d5e2848`); main's later root imports (T2176) are covered by the hub's full `lake build` at merge.

## Verdict
| target | verdict |
|---|---|
| `InjSum_IsTestFun` (+ registry line, amend 1) | PASS |
| `InjSum_stieltjes` | PASS (unchanged since round 1) |
| `poissonSmooth_error` | PASS (unchanged since round 1) |

T2178: **PASS**. Merge may resume at step 5 (full `lake build`).
