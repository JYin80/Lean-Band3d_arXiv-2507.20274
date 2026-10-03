Auditor model: claude-opus-5-5

# T2029 audit (round 2, scope: Amend 1 only): registry lines in `RBM3D/Test/Axioms.lean`

Written Sat Oct  3 05:50:45 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2029-audit2`, detached at `t/T2029` = `739783a`.

Round 1 (auditor claude-opus-5-5, worktree `T2029-audit1`, at `65181f4`) verdict line, kept by reference: **"T2029: PASS. No dispatcher sign-off needed."** (targets `RBM.Green.green_diag_paper`, `RBM.Green.norm_sum_coef_green_sub_le`, every other ported public declaration: PASS). Round 2 checks, per Amend 1 and DECISIONS §20: (1) the diff is confined to `structuralProps`, (2) the five names are exactly as listed and are structural, (3) the registry pre-check, (4) the full `lake build`, (5) the rest unchanged by hash.

## 1. Diff confined to `structuralProps`; rest unchanged by hash

```
$ git diff --stat main...t/T2029
 RBM3D/Green/EntryCore.lean | 1352 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |    7 +-
 2 files changed, 1358 insertions(+), 1 deletion(-)
$ git diff --stat 65181f4 739783a
 RBM3D/Test/Axioms.lean | 7 ++++++-
 1 file changed, 6 insertions(+), 1 deletion(-)
$ git rev-parse 65181f4:RBM3D/Green/EntryCore.lean HEAD:RBM3D/Green/EntryCore.lean
60944aa76808f09a067a95ba8b6f392699da88bd
60944aa76808f09a067a95ba8b6f392699da88bd
$ git diff 1892ec6 65181f4 -- RBM3D/Test/Axioms.lean | wc -l      # round-1 commit did not touch Axioms.lean
       0
$ git diff -U0 65181f4 739783a | grep '^[-+@]'
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
@@ -108 +108,6 @@ def structuralProps : List Name :=
-   `RBM.Gauss.Sizes.locDomain] -- the spectral domain `𝐃_{κ,ε}`
+   `RBM.Gauss.Sizes.locDomain, -- the spectral domain `𝐃_{κ,ε}`
+   `RBM.Green.GoodEvent,      -- the event Ω of (4.10): every entry of `G` within `δ` of `m·I`
+   `RBM.Green.LDERow,         -- row large-deviation event, input of `lem_GbEXP` (later ST-1)
+   `RBM.Green.LDECol,         -- column large-deviation event, input of `lem_GbEXP` (later ST-1)
+   `RBM.Green.LDEQuad,        -- quadratic large-deviation event; h.p. bound S1-19 `stochDom_ldeQuad`
+   `RBM.Green.Stable]         -- stability of `1 − ξS` with constant `K`; band profile S1-24
$ grep -n "^def \(borrowedProps\|owedProps\|structuralProps\|certificates\)" RBM3D/Test/Axioms.lean
76:def borrowedProps : List Name :=
88:def owedProps : List Name :=
95:def structuralProps : List Name :=
131:def certificates : List (Name × Name) :=
```
The only hunk is at line 108, inside `structuralProps` (95–113); the one deleted line is the old closing entry, re-added with `,` instead of `]`. No certificate entry, no other list touched. `EntryCore.lean` is byte-identical to the round-1 audited blob.

```
$ git diff main...t/T2029 | grep -nE '^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom '; echo $?
1
```
**Verdict (diff scope): PASS.**

## 2. Names as listed; classification structural (DECISIONS §20)

```
$ for n in GoodEvent LDERow LDECol LDEQuad Stable; do grep -n "^def $n " RBM3D/Green/EntryCore.lean; done
406:def GoodEvent (G : Matrix n n ℂ) (m : ℂ) (δ : ℝ) : Prop :=
541:def LDERow (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ : ℝ) : Prop :=
545:def LDECol (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ : ℝ) : Prop :=
549:def LDEQuad (H G : Matrix n n ℂ) (S : n → n → ℝ) (t Φ : ℝ) : Prop :=
911:def Stable (S : n → n → ℝ) (ξ : ℂ) (K : ℝ) : Prop :=
$ sed -n '407p;542p;546p;550p;912p' RBM3D/Green/EntryCore.lean
  ∀ x y, ‖G x y - (if x = y then m else 0)‖ ≤ δ
  ∀ i j, i ≠ j → ldeRowLHS H G i j ≤ Φ * ldeRowRHS S G i j
  ∀ k j, k ≠ j → ldeColLHS H G k j ≤ Φ * ldeColRHS S G k j
  ∀ i, ldeQuadLHS H G S t i ≤ Φ * ldeQuadRHS S G i
  ∀ (v : n → ℂ) (B : ℝ), (∀ i, ‖v i - ξ * ∑ k, (S i k : ℂ) * v k‖ ≤ B) → ∀ i, ‖v i‖ ≤ K * B
$ grep -n "^namespace" RBM3D/Green/EntryCore.lean
29:namespace RBM
39:namespace RBM.Green
```
Full names `RBM.Green.{GoodEvent,LDERow,LDECol,LDEQuad,Stable}` match Amend 1 exactly and in order. Each is a `Prop` condition on a matrix/sample (`G`, `H`) or on the variance profile (`S`, `ξ`, `K`), taken as a hypothesis by deterministic lemmas: the "structural" class of DECISIONS §20 (not a paper conclusion, not an external citation). The comments follow the style of the existing entries and name the downstream tickets as Amend 1 states.
**Verdict (names/classification): PASS.**

## 3. Registry pre-check (DECISIONS §20 (2)), in the audit worktree

```
$ cat $SCRATCH/T2029-audit2-precheck.lean
import RBM3D
import RBM3D.Green.EntryCore

#assert_rbm_axioms
$ lake build RBM3D.Green.EntryCore 2>&1 | grep -E "error|Build completed"; echo exit
Build completed successfully (2680 jobs).
exit 0
$ lake env lean $SCRATCH/T2029-audit2-precheck.lean > pre.log 2>&1; echo precheck exit $?
precheck exit 0
$ grep -n "axiom audit\|All within\|Classical.choice\|Quot.sound\|premises found\|registry:" pre.log
1:axiom audit: 1086 theorems, 415 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
2:All within [propext,
3: Classical.choice,
4: Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
20:premises found by scanning: 14 (borrowed 3, owed 1, structural 10).
21:registry: 11 borrowed + 2 owed + 18 structural; 17 registered premise(s) carry nothing yet: [RBM.ThetaDecay,
$ grep -c 'RBM.Green' pre.log
0
```
Structural premises found: 10 = the 5 found without EntryCore (§4) + the 5 new names; no "unregistered" error; none of the new names in the "carry nothing yet" list (each is used). Axioms only `propext`, `Classical.choice`, `Quot.sound`. Matches the prove report's Amend 1 section.
**Verdict (pre-check): PASS.**

## 4. Full `lake build` on the branch (root does not yet import EntryCore; the hub adds it at merge)

```
$ lake build > full.log; echo full-build exit $?
full-build exit 0
$ grep -n "axiom audit:\|premises found\|Build completed\|error" full.log
89:info: RBM3D.lean:70:0: axiom audit: 1041 theorems, 400 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
108:premises found by scanning: 9 (borrowed 3, owed 1, structural 5).
132:Build completed successfully (3728 jobs).
```
**Verdict (full build): PASS.**

## 5. Merge readiness against current `main` (information for the hub, step 5)

```
$ git merge-tree --write-tree --name-only main t/T2029; echo rc $?
06b51c83ec1619508752629c5bdd1d8bed7d5e53
merge-tree rc 0
$ git diff 1892ec6 main -- RBM3D/Test/Axioms.lean | grep '^@@'     # main-side changes since merge base
@@ -72,11 +72,11 @@ Reporting them in one list makes "zero axioms" look better than the situation is
@@ -124,9 +124,7 @@ halves and says, premise by premise, what a certificate would take.
```
No conflict: `main` changed `borrowedProps` and `certificates`, the branch only `structuralProps`. DECISIONS §20 (3) (union on registry-only conflicts) is not needed. The full build with the root import on the merged tree is the hub's step 5.

## 6. Paper deltas

Amend 1 changes registry lines only; no Lean statement changes, so no Lean/paper statement difference arises. Round 1's paper-delta finding (none) stands for the unchanged `EntryCore.lean` blob.

## Observations (no effect on verdict)

- The pre-check in this audit ran against the branch's `RBM3D.lean`/`Axioms.lean`, as Amend 1 specifies, not against the merged tree; the hub's step-5 full build covers the merged tree.

## Verdict

| Item (Amend 1 scope) | Verdict |
|---|---|
| Diff confined to `structuralProps`, no other list, no certificate | PASS |
| Five names exactly as listed, structural per §20 | PASS |
| Registry pre-check (`import RBM3D` + `import RBM3D.Green.EntryCore` + `#assert_rbm_axioms`): exit 0 | PASS |
| Full `lake build` on `t/T2029` at `739783a`: exit 0 | PASS |
| `RBM3D/Green/EntryCore.lean` unchanged by hash (`60944aa`) since round-1 PASS | PASS |

**T2029 (round 2, Amend 1): PASS.** No dispatcher sign-off needed. The hub may resume the merge from step 5.
