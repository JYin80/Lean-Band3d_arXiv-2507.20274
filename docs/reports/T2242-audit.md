Auditor model: claude-opus-5-5

# T2242 audit (round 1) — LW-12b `Graph/AnpKey2` — written Tue Oct  6 03:20 UTC 2026

Branch `t/T2242` at `da47890`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2242-audit1`; scratch `<scratchpad>/T2242/`.

## 1. Scope, hygiene, build

```
$ git diff --name-status main...HEAD
A	RBM3D/Graph/AnpKey2.lean
M	RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep -c '^-[^-]'     # deletions
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|^import" RBM3D/Graph/AnpKey2.lean
6:import RBM3D.Graph.AnpKey
7:import Mathlib.Data.Fin.Tuple.Basic
8:import Mathlib.Algebra.Order.BigOperators.Ring.Finset
9:import Mathlib.Algebra.BigOperators.Fin
$ lake build RBM3D.Graph.AnpKey2 2>&1 | grep -E "error|Build completed"
Build completed successfully (3347 jobs).
```
Only the two sole writable files; no merged file touched (no frozen signature changed); imports `AnpKey` + Mathlib only.

## 2. Statements against the pins (script)

`audit_pins.lean` = `import RBM3D.Graph.AnpKey2` + check file lines 77-273 verbatim (sections 2-3, namespace
`RBM.Graph.T2242Check`) + section 4's `figAuxGh` + the 28 links below + `#print axioms`.
```
example : @valOnPin = @NGraph.valOn := rfl            example : @regionPin = @anpKey2_region := rfl
example : @regionOnePin = @anpKey2_regionOne := rfl   example : @EndAtPin = @NGraph.EndAt := rfl
example : @IsA1Pin = @NGraph.IsA1 := rfl  (likewise IsA2, IsB1, IsB2, NoA2, degS, fixLab)
example : @AnpDetGhRegAtPin = @AnpDetGhRegAt := rfl   example : @AnpIHPin = @AnpIH := rfl
example : @AnpDetGhRegStepPin = @AnpDetGhRegStep := rfl
example : @CaseIPin = @AnpCaseI := rfl                example : @CaseIIIPin = @AnpCaseIII := rfl
example : @AnpDetGhCaseIPin = @AnpDetGhCaseI := rfl   (likewise CaseIII, CaseIV)
example : AnpDetGhOfRegPin := @anpDetGh_of_reg        example : AnpKey2HalfPin := @anpKey2_half
example : AnpKey2RegHalfPin := @anpKey2_reg_half      example : AnpKey2EndTypesPin := @anpKey2_endTypes
example : AnpDetGhRegOfNoA2Pin := @anpDetGhReg_of_noA2
example : AnpKey2FixPin := @anpKey2_fix
example : AnpDetGhStepOfRegPin := @anpDetGhStep_of_reg
example : AnpDetGhRegStepOfCasesPin := @anpDetGhRegStep_of_cases
example : figAuxGh = anpKey2_figAuxGh := rfl          -- instance (1) graph = check file section 4
$ lake env lean audit_pins.lean 2>&1 | grep error ; echo "exit ${pipestatus[1]}"
audit_pins exit 0
```
Every pinned definition is the file's by `rfl`; every target has exactly the pinned type (no added hypothesis;
quantifier order, ranges, `[NeZero L]`, `(C, c)` before `L`, `c ≤ 1` as pinned). Target 1 also `anpKey2_val_eq_valOn : Γ.val ξ a b = Γ.valOn ξ a b
Finset.univ := rfl` (file `:115`).

Mathematics vs `7_8:1111-1146` (by reading the pins): `π i j = true ↔ |ℓ_i-b_j| < |ℓ_i-a_j|` is the paper's
`π_{i,j}=1 ↔ |α_i-a_j| > |α_i-b_j|`; A1 at the `a`-end (`s = false`) needs `π = 0` (`|α-a| ≤ |α-b|`), at the
`b`-end `π = 1` (`|α-b| < |α-a|`), as `:1139-1141`; A2 = the complement on ghost-free paths; B1/B2 as `:1134-1136`.
Case I pin = paper (I)+(II) (two A1/B1 ending edges at one vertex), Case III = two B2 + `deg_s = 2` (`:1247`),
Case IV = `¬I ∧ ¬III` (`:1386`, `:1404`), as the ticket fixes.

## 3. Hidden hypotheses, vacuity, cycles

```
$ sed -n '/^structure NGraph/,/^$/p' RBM3D/Graph/LWVocab.lean     # (other audit_pins output: 2 linter warnings of the check file)
structure NGraph (p q : ℕ) where
  es : List (NEdge p q)
  path : Fin p → List (Fin es.length × NV p q)
```
- No proof fields: `GhostOK`, `IsNested`, `NoA2` are explicit premises.
- No cycle: the file imports only `Graph/AnpKey`; `anpDetGhStep_of_reg` goes from `AnpDetGhRegStep` (not derived
  from `AnpDetGhStep`) to the merged frozen `AnpDetGhStep`; `anpDetGhRegStep_of_cases` goes from the three case Props.
- The unproved inputs are the three case Props (LW-12c/d/e+f pins), registered as owed. They are not vacuous by
  construction: each is a consequence of `AnpDetGh d` restricted to a region (`valOn` on a subset ≤ `val`, `ξ ≥ 0`),
  so they are exactly as true as the merged `lem:Anp_key_gh` pin. Deterministic statements: no external or limit
  hypothesis (TEAM §8 lesson 14 is not triggered).

## 4. Compiled nonempty instances (file `:1900-2057`, all compile in the build above)

| Target | Instance | Concrete data; hypotheses discharged |
|---|---|---|
| T1 vocab, T3 endTypes | `anpKey2_inst_figAuxGh`, `anpKey2_inst_endTypes` | `figAuxGh` (p=q=2, 6 edges), π≡false: `GhostOK`, `IsNested`, `NoA2`, `AnpCaseI`, `AnpCaseIII`, `degS 1 = 2`, B1 edge, all by `decide +kernel` |
| T3 half | `anpKey2_inst_half` | `d=3, L=5`, `x=0, y=(2,2,2), z=(1,1,1)`; premise by `decide +kernel` (tight) |
| T3 reg_half | `anpKey2_inst_reg_half` | `d=3, L=5, p=q=1`; region membership for π≡false and π≡true by `decide +kernel` |
| T3 caseI_ne | `anpKey2_inst_caseI_ne` | `figAuxGh`, two B1 edges at `ℳ₁`; `GhostOK` discharged |
| T4 | `anpKey2_inst_figAux_a2`, `anpKey2_inst_figAux_reg` | `figAux`, π≡false: two A2 edges by `decide`; `GhostOK`, `IsNested` discharged; premise `hreg` = target 4's no-A2 hypothesis (content of LW-12c-f pins) |
| T2 | `anpKey2_inst_cover` | `figAuxGh`, d=3; premise = the per-region bound (LW-12c-f) |
| T6 | `anpKey2_inst_chain`, `anpKey2_inst_figAux_det` | `AnpDetGhCaseI/III/IV 3 → LWAnpKeyGh 3` (with merged `anpDetGh_of_step`, `anpDetGh_zero`, `lwAnpKeyGh_of_det`); `AnpDetGhRegStep 3 → AnpDetGhAt 3 figAux` with `GhostOK`, `IsNested` discharged |
| T5 fix | `anpKey2_inst_fix`, `anpKey2_inst_fixP` | `figAuxGh`, `i₀ = 0`: `GhostOK`, `IsNested` discharged; result `GhostOK ∧ IsNested`, `nSolid = 4`, both B1 ending edges one-step paths (F7); construction's `p' = 4` by `decide +kernel` |

No `N = 0`, empty index, collapsed window or `False` premise; remaining premises are only other gates' pins.

## 5. Axioms and registry pre-check

```
'RBM.Graph.anpDetGh_of_reg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_reg_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_endTypes' depends on axioms: [propext]
'RBM.Graph.anpDetGhReg_of_noA2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_fix' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGhStep_of_reg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGhRegStep_of_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_caseI_ne' depends on axioms: [propext, Quot.sound]
'RBM.Graph.anpKey2_inst_figAuxGh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_inst_figAux_a2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_inst_fix' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_inst_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D RBM3D.Test.Axioms 2>&1 | grep -E "error|Build completed"
Build completed successfully (4045 jobs).
$ printf 'import RBM3D\nimport RBM3D.Graph.AnpKey2\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean  (excerpt)
axiom audit: 7096 theorems, 2410 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Graph.AnpDetGhCaseI: 2 [no certificate]
  RBM.Graph.AnpDetGhCaseIII: 2 [no certificate]
  RBM.Graph.AnpDetGhCaseIV: 2 [no certificate]
pre exit 0
```
`import RBM3D` + `import RBM3D.Graph.AnpKey2` load together with no duplicate-declaration error (no name clash
with the library). `grep -rnw "def <name>" RBM3D` outside the file: 0 hits for `valOn`, `EndAt`, `IsA1`, `NoA2`,
`degS`, `AnpDetGhRegAt`, `AnpIH`, `AnpCaseI`, `AnpDetGhRegStep`.

## 6. Paper deltas

Differences between Lean and paper, and where they are proposed (prove report (d)):
- combinatorial regions/side bit, exact partition (paper: subregions that cover) → T2242a;
- `:1157` "by definition … distinct paths" as `anpKey2_caseI_ne` → T2242b;
- vertex fixing at arbitrary `i₀`, every path cut into `k_j+1` segments, one statement for (I) and (II); the
  paper's Case (I)/(II) delete `(a_1,α_q)`, `(a_2,α_q)` instead → T2242c;
- A2 replacement cost `c ↦ min c ½`, pointwise bound on the region → T2242d;
- stronger IH (all `k < q`, any `p`, any edge count) instead of "at most `K` solid edges" (`:1107`) → T2242e;
- Case I pin merges paper (I)+(II); Case IV = `¬I ∧ ¬III` (the paper sends `deg_s = 2` to (III) at `:1404`):
  covered by T2242c and the ticket's interface; deterministic `(C, c)` for `≺` is merged LW-12a convention. Complete.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)

1. Registry: the pre-check also listed `NGraph.EndAt`, `IsA1`, `IsA2`, `IsB1`, `NoA2`; the prover put them in
   `structuralProps` (`Axioms.lean:287-291`), next to `IsNested`/`NoGhost`/`GhostOK`, not in the owed table as the
   ticket's literal text says. They are data conditions on a graph, not unproved results; the classification
   matches precedent. The prove report flags it (d)1 for the dispatcher.
2. File is 2057 lines (ticket estimate 1250-1550; the 1500-line stop rule was tied to a stage-1a estimate).
3. The prove report lists public declarations by `line:name` only, not with full statements (ticket acceptance
   item); target statements and instances are listed in full.

## Verdict

| Target | Verdict |
|---|---|
| 1 vocabulary (`valOn`, `anpKey2_region(One)`, `EndAt`, `IsA1..IsB2`, `NoA2`, `degS`, `anpKey2_fixLab`, case Props) | PASS |
| 2 `anpDetGh_of_reg` | PASS |
| 3 `anpKey2_half`, `anpKey2_reg_half`, `anpKey2_endTypes` (+ `anpKey2_caseI_ne`) | PASS |
| 4 `anpDetGhReg_of_noA2` | PASS |
| 5 `anpKey2_fix` | PASS |
| 6 `anpDetGhStep_of_reg`, `anpDetGhRegStep_of_cases` | PASS |

**T2242: PASS.** No dispatcher sign-off required (observation 1 is a registry choice the dispatcher may revisit).
