Auditor model: claude-opus-5-5

# T2203 audit (round 1) — LW-10c3 `Graph/LocalRegular6c`

Audit time (`date -u`): Mon Oct  5 20:37:44 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2203-audit1`, detached at `t/T2203` = `93bb007`.
Scratch files: `scratchpad/T2203/` (`audit_check.lean`, `reg.lean`, `build.log`, `reg.log`).

## 1. Diff scope, imports, forbidden tokens, name clashes

```
$ git diff --name-status main...t/T2203
A	RBM3D/Graph/LocalRegular6c.lean
$ git show t/T2203:RBM3D/Graph/LocalRegular6c.lean | grep -n '^import'
6:import RBM3D.Graph.LocalRegular6b
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom ' RBM3D/Graph/LocalRegular6c.lean
0
$ grep -c '^open Classical$' RBM3D/Graph/LocalRegular6c.lean
0
$ for n in scostLL_moveSC scostLL_moveOut scostLL_dmove localReg6c_; do git grep -c "$n" main -- RBM3D | wc -l; done
0  0  0  0
```
Only the sole writable file is touched; no merged file and no frozen signature changed; `RBM3D/Test/Axioms.lean` untouched (no new Prop-valued definition: the three public `def`s `localReg6c_map*` are `→ ℕ`).

## 2. Build and axioms

```
$ lake build RBM3D.Graph.LocalRegular6c        (audit worktree; module not in the copied cache, compiled fresh)
✔ [3387/3387] Built RBM3D.Graph.LocalRegular6c (14s)
Build completed successfully (3387 jobs).
exit 0
$ awk '/LocalRegular6c/{f=1} f' build.log | grep -E 'warning|error'      -> (no lines)
```
`#print axioms` (in `audit_check.lean`, `lake env lean`, exit 0):
```
'RBM.Graph.scostLL_moveSC' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.scostLL_moveOut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.scostLL_dmove' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg6c_alone_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg6c_inst_s55' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg6c_inst_dmove_cyc_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg6c_inst_moveSC_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg6c_inst_alone_values' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check (`reg.lean` = `import RBM3D` + `import RBM3D.Graph.LocalRegular6c` + `#assert_rbm_axioms`):
```
$ lake env lean reg.lean ; echo exit $?
exit 0
axiom audit: 6325 theorems, 2198 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
```

## 3. Statements against the pins (script)

Pin source identity:
```
$ sed -n 358,377p docs/tickets/checks/T2184-check.lean | md5
7205e0241cb5f47d0a8efde27f93c5a5
$ sed -n '/\/-- c3 \[`scostLL_moveSC`\]/,/LGraph.ScostLL Γ (lwPrimDmove Γ rest z v q)$/p' docs/tickets/checks/T2203-check.lean | md5
7205e0241cb5f47d0a8efde27f93c5a5
```
`audit_check.lean` = `import RBM3D.Graph.LocalRegular6c` + sections 2–3 of `T2203-check.lean` copied by `sed` (each section-3 `example : Prop :=` renamed `def shapeN : Prop :=`, N = 1..14), then:
```lean
example : ScostLLMoveSCPin := @scostLL_moveSC
example : ScostLLMoveOutPin := @scostLL_moveOut
example : ScostLLDmovePin := @scostLL_dmove
example : shape1 := localReg6c_inst_moveSC
example : shape2 := by have h := localReg6c_inst_moveSC_values; simpa [shape2, chkMapXYA, localReg6c_mapXYA] using h
example : shape3 := localReg6c_inst_moveSC_cyc
example : shape4 := localReg6c_inst_moveSC_cyc_values
example : shape5 := fun _ => localReg6c_inst_moveOut
example : shape6 := fun _ => localReg6c_inst_dmove
example : shape7 := localReg6c_inst_dmove_cyc
example : shape8 := localReg6c_inst_dmove_cyc_values
example : shape9 := @localReg6c_inst_P3
example : shape10 := @localReg6c_inst_P4
example : shape11 := @localReg6c_inst_D
example : shape12 := @localReg6c_inst_T3
example : shape13 := @localReg6c_inst_ET3
example : shape14 := localReg6c_inst_s55.1
```
```
$ lake env lean audit_check.lean      -> no errors, only the 8 #print axioms lines above; exit 0
```
The three pins are discharged by `@name` with no binder reordering: the Lean statements are exactly `ScostLLMoveSCPin`, `ScostLLMoveOutPin`, `ScostLLDmovePin` (hypotheses `u ≠ z`, `z ≠ v`, `Perm` for MoveSC; `z ≠ v`, `z ≠ d`, `Perm` for MoveOut; `z = v ↔ cp`, `q.src = q.dst ↔ q.circ`, `Perm` for Dmove). No added hypothesis. All 14 statement shapes of the check file are discharged by file instances.

Target 1 (`localReg6c_alone_diff`, `:282`, helper whose exact form the ticket leaves to the prover): hypotheses `Γ.solid.Perm (R ++ rest)`, `α` alone in `s'`, `C` containing the `s₀`-classes of the ends of `R` (`hR`) and of the non-`α` ends of `A` (`hA`); conclusion is the exact identity of the ticket's recommended shape with the single waved edge `[w]` generalised to a list `W` (`+ 2 * W.length`; for `W = [w]` it is the ticket's `+2`). An equality, not an inequality (T2184 (a) F1 respected). Proved from merged `scostLL_fresh_scost` and `scostLL_scost_eq`.

## 4. Hidden hypotheses, vacuity, cycles

- `LGraph.ScostLL` is the merged T2184 definition (`LocalRegular6a.lean:168`); no new structure, no new Prop-valued definition, nothing carried in a field.
- The only import is `RBM3D.Graph.LocalRegular6b` (merged, T2195); all upstream names cited are merged (`#check` section 1 of the check file compiles as part of the dispatcher's pre-release; the build above compiles every use). No cycle possible: the module is new and imported by nothing.
- The dispatch lemma `localReg6c_ll_of_cases` (private, `:1069`) takes the three cases as hypotheses, but each pin discharges them internally (`refine localReg6c_ll_of_cases … ?_ ?_ ?_`), so nothing is exported as a hypothesis; the pins' signatures (section 3) show it.
- No external hypothesis (deterministic graph combinatorics; §29 checklist items all void).

## 5. Compiled nonempty instances

| endpoint | instance (file line) | data | nondegenerate? |
|---|---|---|---|
| `scostLL_moveSC` | `localReg6c_inst_moveSC` `:1520`; values `_moveSC_values` `:1528` (5, 6, 5) | `fxyPowGraph 2`, `z = inr 0`, `u = inl 0`, `v = inl 1`, 4-edge `rest` | yes; all hyps by `decide` / merged `localReg6b_inst_contractPerm` |
| `scostLL_moveSC` (collapse) | `_moveSC_cyc` `:1555`, `_cyc_values` `:1561` (`−2`, `¬ 0 ≤ −2`) | `localReg6b_instCyc`, `u = v = inr 1` | yes; repair branch forced |
| `scostLL_moveOut` | `_moveOut` `:1592` (`Perm` `:1579`) | `Γ_2`, `z = inl 0`, `v = inr 0`, `d = inr 2` | yes |
| `scostLL_dmove` red | `_dmove` `:1609` (`Perm` `:1600`) | `Γ_2`, `z = v = inr 1`, `cp = true`, `q = ⟨false,false,inl 0,inr 2⟩` | yes |
| `scostLL_dmove` blue (collapse) | `_dmove_cyc` `:1617`, `_values` `:1622` (`−2`, `¬ 0 ≤ −2`) | `instCyc`, `z = inr 0`, `v = inr 1`, `q = ⟨true,false,inr 1,inr 0⟩` | yes; repair forced |
| P3, P4, D, T3, ET3 | `_inst_P3/P4/D/T3/ET3` `:1643-1676` | general `Γ` (consumer adapters, shapes 9–13) | n/a (adapters; concrete instances above) |
| §55 | `_inst_s55` `:1685` | instances (1), (3), (4) via merged `localReg6b_inst_s55` | yes |
| `localReg6c_alone_diff` | `example` `:1716`, values `_inst_alone_values` `:1742` (6, 6) | `Γ_2`, `R` = the two MoveSC edges, trivial setoid `ker localReg6c_mapInj`, `W` one waved edge, `C` 3 classes | yes; every hypothesis discharged |

All compile (section 2 build). No `N = 0`, empty index, `False` premise or collapsed data; every deterministic hypothesis is discharged.

## 6. Paper deltas

Prove report (d) `:243` proposes `T2203a` (local lemma for MoveSC/MoveOut/Dmove closes the edge/`GG`/weight terms omitted at `B:272-275`, on `T2184c`/D492) and `T2203b` (2-cycle collapse in MoveSC and blue Dmove at `k = 2`, repaired by merging the cycle's two classes, never two external ones; extends D491/`T2195b`), matching the ticket's expected candidates; `T2203c` is a proof-route note. The pins themselves are T2184's, so no new statement difference arises beyond these. Coverage complete.

## 7. Observations (no verdict effect)

- O1. Target 1 generalises the ticket's single waved edge `[w]` to a list `W`; strictly more general, and the ticket left the exact helper statement to the prover.
- O2. Instances (6)–(9) are general-`Γ` adapters (as the check-file shapes 9–13 demand); concrete nondegeneracy is carried by instances (1)–(5).
- O3. Prove report line 1 is `Prover model: claude-sonnet-5-5`; 245 lines (≤ 300).

## Verdict

| target | verdict |
|---|---|
| `localReg6c_alone_diff` (target 1) | PASS |
| `scostLL_moveSC` | PASS |
| `scostLL_moveOut` | PASS |
| `scostLL_dmove` | PASS |

**Ticket T2203: PASS.** No dispatcher sign-off needed.
