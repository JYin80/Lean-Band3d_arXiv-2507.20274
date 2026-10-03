Auditor model: claude-opus-5-5

# T2049 audit, round 2 (S3-01: Steps 3-4 pins into the library)

Time: Sat Oct  3 10:56:09 UTC 2026 (`date -u`). Branch `t/T2049` at `6d9ce32` (repair of round-1 D1 on `0d33ee7`);
audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2049-audit2` (detached). Scratch: `scratchpad/T2049/`.

## 1. Scope (diff against main)
```
$ git diff --stat main...HEAD
 RBM3D/Induction/Step34Pins.lean | 1091 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   26 +-
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   (changed lines, abridged)
-   `RBM.Green.AsGMcPT]   ->   +   `RBM.Green.AsGMcPT,     (list continuation only)
+   24 lines `RBM.Gauss.Sizes.{STLmaxU STLKU STStep3R STStep4R STStep3 STStep3I STStep3II STStep4 STStep4I
    STStep4II STIngR STIterR STContract STNewPQ STSEforLn STOeqNQ STOeqQt STOeqQtNZ STIterations
    STIterationsII STMollifierEx STQopNorm STWardTypePPin STB45Pin}` appended to `owedProps`
$ git diff main...t/T2049 --name-only | grep -v "Step34Pins\|Test/Axioms" | wc -l
       0
$ git show 6d9ce32 --stat
 RBM3D/Induction/Step34Pins.lean | 8 ++++++++
```
Only the two sole writable files; registry lines only in `Axioms.lean`; no frozen signature touched.

## 2. Statement (target 1: probe sections 1-4 verbatim; item 4 instances)
```
$ diff <(git show 3c58211:RBM3D/Probe/T2041Pins.lean | sed -n 45,683p) <(sed -n 38,676p RBM3D/Induction/Step34Pins.lean)
471c471
< `T2041c`).  The RBM2D choice `ϑ = (1-t)^{m} Π Θ_t(a₁,a_i)` (`HierVocab.lean:66`) violates the first bound at `d ≥ 3`:
---
> `T2041b`).  The RBM2D choice `ϑ = (1-t)^{m} Π Θ_t(a₁,a_i)` (`HierVocab.lean:66`) violates the first bound at `d ≥ 3`:
exit=1
$ diff <(probe 928,938) <(file 678,688)                         # st_Bctl_pos
exit=0
$ diff <(probe 1164,1553) <(file 692,1089 with the 8 repair lines 978-985 removed)   # instances
13c13
< namespace RBM.Gauss.T2041Inst
---
> namespace RBM.Gauss.Step34Inst
exit=1
```
The pinned text equals the probe's (the ticket's pin) except the O2 docstring tag ordered by the ticket and the
instance namespace rename. The repair added only the 8 lines 978-985; no statement changed since round 1. The
statements of `STStep3R`, `STStep4R`, `STLmaxU`, `STLKU`, `STStep2Concl`, the ingredients and `STEK*` are therefore
the T2041-accepted pins (DECISIONS §25). Item 2 bridges (unchanged):
```
284:theorem STLmax_of_STLmaxU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLmaxU sz E s t) :
285-    STLmax sz E t := by
291:theorem STLK_of_STLKU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLKU sz E s t) :
292-    STLK sz E t := by
```
`st_prec_of_xi`, `st_prec_one_add_sup` not copied (not used by sections 1-4 or the instances; round 1, accepted).
Item 3 (HierVocab skip list): accepted in round 1; unchanged.

## 3. Hidden hypotheses, vacuity, cycles
No `structure`/`class`/`instance` in the file (round 1, file unchanged outside the 8 repair lines); all pins are
`Prop` defs with explicit premises. Bridges depend only on merged `StochDomAt.precomp_param`. Imports are merged
modules only; no cycle.

## 4. Compiled nonempty instances
Round-1 defect D1 (no instance of the two bridges) is repaired:
```
$ sed -n 978,984p RBM3D/Induction/Step34Pins.lean
/-- The bridge `STLmax_of_STLmaxU` at `(sz0, z0, 0, 1/16)`; `hst` from `sz0_hst`, the owed `STLmaxU` stays a premise. -/
example (h : STLmaxU sz0 (STflowE z0) sInst tInst) : STLmax sz0 (STflowE z0) tInst :=
  STLmax_of_STLmaxU sz0 (fun n => (sz0_hst n).le) h

/-- The bridge `STLK_of_STLKU` at `(sz0, z0, 0, 1/16)`; `hst` from `sz0_hst`, the owed `STLKU` stays a premise. -/
example (h : STLKU sz0 (STflowE z0) sInst tInst) : STLK sz0 (STflowE z0) tInst :=
  STLK_of_STLKU sz0 (fun n => (sz0_hst n).le) h
$ grep -n "def sInst\|def tInst\|def sz0 \|def z0" RBM3D/Induction/Defs.lean RBM3D/Defs/Sizes.lean
RBM3D/Induction/Defs.lean:413:def z0 (n : ℕ) : ℂ := ⟨1 / 2, ((sz0.size n : ℕ) : ℝ) ^ (-(4 / 5 : ℝ))⟩
RBM3D/Induction/Defs.lean:439:def sInst : ℕ → ℝ := fun _ => 0
RBM3D/Induction/Defs.lean:440:def tInst : ℕ → ℝ := fun _ => 1 / 16
RBM3D/Defs/Sizes.lean:260:def sz0 : Sizes 3 where
$ grep -n "theorem sz0_hst" RBM3D/Induction/Step34Pins.lean
941:theorem sz0_hst : ∀ n, sInst n < tInst n := fun n => by simp only [sInst, tInst]; norm_num
```
The deterministic hypothesis `hst` is discharged at `d = 3`, `s ≡ 0 < t ≡ 1/16`, `sz0`, `z0`; the owed pins
`STLmaxU`/`STLKU` stay premises, as allowed (CLAUDE.md §4 step 2). Nondegenerate. Both compile (§5 build).
The other instances (`inst_step3/3I/3II/4/4I/4II`, `inst_contract`, `inst_SEforLn`, ...) are the verbatim probe
instances accepted in round 1 at `(sz0, z0, 0, 1/16)` and `(szB, zB, 15/16, 31/32)`; unchanged.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.Step34Pins ; echo exit=$?
exit=0
Build completed successfully (3703 jobs).
$ grep -E "^(warning|error)" build.out | grep Step34
warning: RBM3D/Induction/Step34Pins.lean:12:0: The module doc-string for a file should be the first command after the imports.
$ lake build RBM3D ; echo exit=$?
exit=0
Build completed successfully (3745 jobs).
$ cat precheck.lean   # import RBM3D / import RBM3D.Induction.Step34Pins / #assert_rbm_axioms
$ lake env lean precheck.lean ; echo exit=$?        (DECISIONS §20 registry pre-check)
exit=0
axiom audit: 1563 theorems, 628 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 50 (borrowed 2, owed 36, structural 12).
$ grep -ic unclassified precheck.out
0
$ lake env lean axioms.lean    (#print axioms of every public def/abbrev/theorem of the file)
$ grep -c "depends on axioms" axioms.out ; grep -c "does not depend" axioms.out ; grep -c error axioms.out
123
4
0
$ grep "depends on axioms" axioms.out | grep -v "\[propext, Classical.choice, Quot.sound\]"
'RBM.Gauss.Sizes.STAlternating' depends on axioms: [propext, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^\s*axiom " RBM3D/Induction/Step34Pins.lean | wc -l
       0
$ (name clash: every def/abbrev/theorem/lemma/structure name of the file vs `git grep` declarations on main)
clashes=0
```
Only standard axioms (subsets of `propext, Classical.choice, Quot.sound`).

## 6. Paper deltas
```
$ grep -n "paper-delta" docs/reports/T2049-prove.md
268:* Paper-delta candidates: none new; T2041a-i are cited as signed in DECISIONS §25. The one text change is the O2 docstring tag (`T2041c` to `T2041b`), no statement change.
```
Statement differences are those of the T2041 design (candidates T2041a-i, DECISIONS §25); the ticket says cite,
do not re-propose. The repair adds no statement. Covered.

## 7. Verdict per target
| target | verdict |
|---|---|
| 1. sections 1-4 verbatim (+ O2 tag) | PASS |
| 2. bridges `STLmax_of_STLmaxU`, `STLK_of_STLKU`; `st_Bctl_pos` | PASS (D1 repaired: instances lines 978-984) |
| 3. HierVocab port (skip list) | PASS |
| 4. instances (probe 1164-1553, `szB`) | PASS |
| registry (DECISIONS §20, §25) | PASS |
| build / axioms / scope | PASS |

**Ticket verdict: PASS.**

## 8. Observations (no RETURN)
- O1 (carried from round 1). Eleven registered names (`STLKU STStep3R STStep4R STStep3 STStep3I STStep3II STStep4
  STStep4I STStep4II STIngR STIterR`) are not in §25's registry list; registered as owed under §20 and proposed in
  the prove report (d). For the dispatcher's bookkeeping, not an audit sign-off.
- O2 (carried). §25 names not reported by the pre-check (`STKward`, `STStep2Concl` and parts, `STXiBoot`,
  `STIterHyp`, `STEK*`, structural predicates) are not registered; the ticket asks only for reported premises.
- O3 (carried). Linter warning: module docstring at line 12 follows `set_option`.
- O4 (carried). `inst_mollifier`, `inst_qopNorm` specialize only part of the parameters; they are instances of owed
  `Prop` pins, not endpoint theorems.
- O5. The round-1 requirement to paste the rebuilt pre-check in the prove report: the repair section (prove report
  line 270 ff.) records the change and commit; this audit reran build and pre-check (§5). No statement effect.
