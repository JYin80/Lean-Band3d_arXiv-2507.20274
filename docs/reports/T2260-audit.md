Auditor model: claude-opus-5-5

# T2260 audit (LW-12d, `Graph/AnpKey4`, case (III) of `lem:Anp_key_gh`), round 1 — Tue Oct  6 06:34:49 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2260-audit1`, detached at `t/T2260` = a588214 (merge base with main d0484be; main now 20de014). Scratch files in `scratchT2260/` of the worktree (untracked) and the scratchpad.

## 1. Diff scope and forbidden tokens
```
$ git diff --stat main...t/T2260
 RBM3D/Graph/AnpKey4.lean | 878 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   2 +
 2 files changed, 880 insertions(+)
$ git diff main...t/T2260 | grep -nE "^\+.*(sorry|admit|native_decide|^\+axiom )"; echo $?
1
$ git diff main...t/T2260 -- RBM3D/Test/Axioms.lean | grep "^[+-] "
+   `RBM.Graph.NGraph.IsB2, -- ending edge of type B2 (`7_8:1136`): a defining predicate of the case split, hypothesis of `anpKey4_caseIII_ne`, `anpKey4_solid` (T2260)
+   `RBM.Graph.AnpCaseIII, -- case (III) of the induction step (`7_8:1245`): two B2 ending edges at an internal vertex with `deg_s = 2`, a defining predicate of the case split, hypothesis of `anpKey4_
```
Only the two sole writable files; no deletion in the registry (owed `AnpDetGhCaseIII` stays, ticket rule); merged pins in `AnpKey2.lean` untouched (file not in the diff).

## 2. Build (audit worktree)
```
$ lake build RBM3D.Graph.AnpKey4 RBM3D.Test.Axioms   (errors / AnpKey4 lines / tail)
error lines: 0; warnings in AnpKey4.lean: 0
✔ [3349/3350] Built RBM3D.Test.Axioms (3.0s)
✔ [3350/3350] Built RBM3D.Graph.AnpKey4 (9.4s)
Build completed successfully (3350 jobs).
exit 0
$ lake build RBM3D   (branch library, does not yet import AnpKey4)
Build completed successfully (4063 jobs).
exit 0
```

## 3. Statements against the pins (check file section 2 copied verbatim into a scratch namespace)
```
$ lake env lean scratchT2260/PinCheck.lean   # = import RBM3D.Graph.AnpKey4 + check-file lines from `namespace RBM.Graph.T2260Check` to section 3 + figLoop/piLoop + the lines below
example : AnpKey4CaseIIIHoldsPin := @anpDetGhCaseIII_holds
example : AnpKey4NePin := @anpKey4_caseIII_ne
example : AnpKey4SolidPin := @anpKey4_solid
example : AnpKey4Gh2Pin := @anpKey4_gh2_props
example : AnpKey4ReducePin := @anpKey4_reduce
example : AnpKey4OfReducePin := @anpKey4_of_reduce
example : figLoop = anpKey4_figLoop := rfl
example : piLoop = anpKey4_piLoop := rfl
#print axioms anpDetGhCaseIII_holds
#print axioms RBM.Graph.anpKey4_caseIII_ne
#print axioms RBM.Graph.anpKey4_solid
#print axioms RBM.Graph.anpKey4_gh2_props
#print axioms RBM.Graph.anpKey4_reduce
#print axioms RBM.Graph.anpKey4_of_reduce
#print axioms RBM.Graph.anpKey4_inst_hyp
#print axioms RBM.Graph.anpKey4_inst_figLoop
#print axioms RBM.Graph.anpKey4_inst_figAuxGh
#print axioms RBM.Graph.anpKey4_inst_chain
#print axioms RBM.Graph.anpKey4_inst_reduce
#print axioms RBM.Graph.anpKey4_inst_ne_solid
#print axioms RBM.Graph.anpKey4_inst_gh2
exit 0; output:
'RBM.Graph.anpDetGhCaseIII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_caseIII_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_solid' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_gh2_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_reduce' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_of_reduce' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_inst_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_inst_figLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_inst_figAuxGh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_inst_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_inst_reduce' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_inst_ne_solid' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey4_inst_gh2' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All six pins are discharged by `@name`, so each statement is the pin with no added hypothesis; `figLoop`/`piLoop` equal the file's instance data by `rfl`. The target `anpDetGhCaseIII_holds : ∀ d, AnpDetGhCaseIII d` is the merged case pin (`AnpKey2.lean:177`) for every `d`; `AnpCaseIII` (`:166`) is the paper's case (III) (`7_8:1246`: two B2 ending edges at one internal vertex, `deg_s = 2`). Not a special case: no primed successor was needed. Constants `(C, c/2)` (`AnpKey4.lean:707`), as in `7_8:1347`. §29: deterministic, `(C,c)` before `L`, uniform in `a b`, no grid lift.

## 4. Hidden hypotheses, vacuity, cycles
- Every hypothesis is in the signatures (Prop-valued `def`s `AnpDetGhCaseIII`, `AnpIH`, `AnpCaseIII`, `IsB2`, `NoA2`; no structure carrying a field-hypothesis).
- `anpDetGhCaseIII_holds := anpKey4_of_reduce anpKey4_reduce` (`:784-785`): the reduction premise of `anpKey4_of_reduce` is discharged by the proved `anpKey4_reduce`; no theorem of the file assumes `AnpDetGhCaseIII`. Only premise left: `AnpIH d q` (inside the pin), the induction hypothesis, registered owed (`Axioms.lean:170`), discharged by `anpDetGh_of_step` in LW-12f (ticket). Dependencies are merged modules (`import RBM3D.Graph.AnpKey3` + Mathlib only).
- Registry pre-check (ticket acceptance):
```
$ lake env lean scratchT2260/Reg.lean   # import RBM3D; import RBM3D.Graph.AnpKey4; #assert_rbm_axioms
exit 0
axiom audit: 7645 theorems, 2561 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
premises found by scanning: 154 (borrowed 1, owed 97, structural 39, refuted 6, superseded 11).
... (126 registered premises carry nothing yet; this ticket's entries in that list:)
198: RBM.Graph.AnpDetGhStep,
199: RBM.Graph.AnpDetGhCaseI,
200: RBM.Graph.AnpDetGhCaseIII,
```
`AnpDetGhCaseIII` now "registered, carries nothing" (info line, as the ticket expects). Registered additions: `NGraph.IsB2` (expected) and `AnpCaseIII` (both `structuralProps`, defining case-split predicates; the prove report (b) item 9 states the first pre-check flagged both). Classification is correct: both are decidable data predicates, discharged by `decide +kernel` at the instance.

## 5. Compiled nonempty instances (check-file section 3 shapes)
```
$ lake env lean scratchT2260/InstCheck.lean
example : anpKey4_figLoop.GhostOK ∧ anpKey4_figLoop.IsNested ∧ anpKey4_figLoop.NoA2 anpKey4_piLoop ∧ ¬ AnpCaseI anpKey4_figLoop anpKey4_piLoop ∧
    AnpCaseIII anpKey4_figLoop anpKey4_piLoop ∧ anpKey4_figLoop.ordN = 1 ∧ anpKey4_figLoop.nngh = 0 := anpKey4_inst_hyp
example : AnpIH 3 1 → AnpDetGhRegAt 3 anpKey4_figLoop anpKey4_piLoop := anpKey4_inst_figLoop
example : AnpCaseIII anpKey2_figAuxGh (fun _ _ => false) ∧
    (AnpIH 3 2 → AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false)) := anpKey4_inst_figAuxGh
example : AnpDetGhCaseIV 3 → LWAnpKeyGh 3 := anpKey4_inst_chain
example : ∃ (p'' : ℕ) (Γ'' : NGraph p'' 0), Γ''.GhostOK ∧ Γ''.IsNested ∧ Γ''.ordN = anpKey4_figLoop.ordN := anpKey4_inst_reduce
#eval (anpKey4_figLoop.es.length, anpKey4_figLoop.degS 0, anpKey4_figLoop.ordN, anpKey4_figLoop.nngh, (anpKey4_figLoop.path 0).length, (anpKey4_figLoop.path 1).length)
exit 0; output (es.length, degS 0, ordN, nngh, |path 0|, |path 1|):
(5, 2, 1, 0, 3, 2)
```
- (1) `anpKey4_inst_hyp` (`:808`): every deterministic hypothesis of the target at `anpKey4_figLoop` (p = 2, q = 1, 5 edges, deg_s = 2, both paths nonempty) by `decide +kernel`, incl. `¬ AnpCaseI` (case (III) only) and the self-loop configuration `β_0 = a_0`.
- (2) `anpKey4_inst_figLoop`, (3) `anpKey4_inst_figAuxGh` (q = 2): target applied, only premise `AnpIH 3 k` (another gate's pin, allowed). (4) `anpKey4_inst_chain`: premise `AnpDetGhCaseIV 3` (LW-12e/f pin). (5) `anpKey4_inst_reduce`: unconditional, at the self-loop graph. Extra: (6) `anpKey4_inst_ne_solid`, (7) `anpKey4_inst_gh2` (three-step path, not one-step) instantiate the other three intermediate pins with all hypotheses discharged.
- No `N = 0`, empty index, `False` premise or large witness. Axioms of all instances: standard three (section 3).

## 6. Names
```
$ for n in <every theorem/def of AnpKey4.lean>; git grep definitions of $n on main -- RBM3D/; also every other t/* branch
30 names, all prefixed `anpKey4_` except the pinned `anpDetGhCaseIII_holds`; definitions on main: 0 each; on other t/* branches: none
```

## 7. Paper deltas
Prove report (d) proposes T2260a–e, covering every Lean/paper difference found: (a) no new ghost edges `(a_t, β_t)` (`7_8:1250-1254`), solid edges `m_t` made ghost after vertex fixing, no self-loop case; (b) no WLOG on the side of the B2 edge; (c) "B2 edges not on the same path" proved (`anpKey4_caseIII_ne`); (d) region, `(eq:noA2)`, `(eq:Psi)` unused; (e) `ord'' = ord`, `n_ngh'' ≥ n_ngh` absorbed, `c ↦ c/2`. These match the ticket's expected list; no further statement difference (target is the merged pin unchanged).

## 8. Observations (no verdict effect)
- The merged docstring of `AnpDetGhCaseIII` (`AnpKey2.lean:176`) cites `7_8:1376-1384`; the case is `:1245-1348` (already noted in the ticket; doc fix for the dispatcher, not in this ticket's files).
- Instance (1) uses `unfold NGraph.IsNested; decide +kernel` instead of a local `Decidable IsNested` instance; same content.

## Verdict
| Target | Verdict |
|---|---|
| `anpDetGhCaseIII_holds : AnpKey4CaseIIIHoldsPin` | PASS |
| `anpKey4_caseIII_ne`, `anpKey4_solid`, `anpKey4_gh2_props`, `anpKey4_reduce`, `anpKey4_of_reduce` (intermediate pins) | PASS |

**T2260: PASS.** No dispatcher sign-off needed.
