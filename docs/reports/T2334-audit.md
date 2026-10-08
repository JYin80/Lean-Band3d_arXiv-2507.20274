Auditor model: claude-opus-5-5

# T2334 audit (round 1): LW-14f `RBM3D/Graph/LWExpTerm6.lean`
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2334-audit1`, detached at `4982248` (`t/T2334`). Scratch files are in `<scratchpad>/T2334/audit/`.

## 1. Diff scope (sole writable files)
```
$ git diff --stat main...t/T2334
 RBM3D/Graph/LWExpTerm6.lean | 754 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |   6 -
$ git diff main...t/T2334 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.LWtermEXP, -- `lem:LWterm_EXP` (`6:83-88`): LW-14
-   `RBM.Gauss.Sizes.LWCutExp, -- one cut of `(eq:EGC)` in expectation, ...: LW-14b
-   `RBM.Gauss.Sizes.LWExpG5', -- `I₄₂`, `J₄₂` ...: LW-14c
-   `RBM.Gauss.Sizes.STStep6I, -- `6:97` regime (i) pin ...
-   `RBM.Gauss.Sizes.STStep6II, -- `6:97` regime (ii) pin ...
-   `RBM.Gauss.Sizes.STStep6III, -- `6:94-96` regime (iii) pin ...
```
The diff touches only the two sole writable files. The registry change is exactly the six owed lines the ticket names, with nothing added. No frozen signature changes, and `RBM3D.lean` is unchanged.

## 2. Build, hygiene, axioms
```
$ lake build RBM3D.Graph.LWExpTerm6 2>&1 | grep -E 'error|Build completed|Built RBM3D.Graph.LWExpTerm6'
✔ [3918/3918] Built RBM3D.Graph.LWExpTerm6 (7.9s)
Build completed successfully (3918 jobs).
$ lake build RBM3D.Graph.LWExpTerm6 2>&1 | grep -c 'LWExpTerm6.lean'      # diagnostics from the new file
0
$ grep -nE 'sorry|admit|native_decide|^axiom |^\s*axiom ' RBM3D/Graph/LWExpTerm6.lean | wc -l
       0
$ lake env lean ax.lean     # #print axioms, 8 targets + 6 instances
'RBM.Gauss.Sizes.lwGraphPrecJoin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpG5'_of_expand'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpG5'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwCutExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwTermEXP_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep6I_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep6II_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep6III_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_join' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_step6I' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_step6II' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_step6III' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_term' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Registry pre-check: a scratch file outside the repo containing `import RBM3D` + `import RBM3D.Graph.LWExpTerm6` + `#assert_rbm_axioms`, run after `lake build RBM3D.Test.Axioms` on the branch registry.
```
$ lake env lean pre.lean > pre.log 2>&1 ; echo exit=$?
exit=0
axiom audit: 10128 theorems, 3013 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 141 (borrowed 1, owed 80, structural 41, refuted 6, superseded 13).
$ grep -c 'Classify' pre.log
0
```
The pre-check reports no newly unregistered premise. Without the root import, the branch's full build reports `LWExpG5'` as unregistered (prove report (d)), so the hub must add `import RBM3D.Graph.LWExpTerm6` at merge, as §3 (A) step 4 already requires.

## 3. Statements against the pin (check file `docs/tickets/checks/T2334-check.lean`)
```
$ python3 (extract `def LwGraphPrecJoin` .. blank line from check file and Lean file, whitespace-normalize, compare)
pin equal (whitespace-normalized): True 553 553
$ lake env lean eq.lean   # check file + `import RBM3D.Graph.LWExpTerm6`, then for the eight names
#   example : RBM.Gauss.Sizes.T2334Check.T2334_<n> := RBM.Gauss.Sizes.<n>
#   example : RBM.Gauss.Sizes.T2334Check.LwGraphPrecJoin = RBM.Gauss.Sizes.LwGraphPrecJoin := rfl
lean_exit=0   (grep 'error': no lines)
```
All eight theorems have exactly the check's types. The `rfl` example shows that the check-namespace `LwGraphPrecJoin` (used inside `T2334_lwExpG5'_of_expand'`) is the file's pin.

Pin content against `B:78-108` `(Gammamuxy)`: the Lean bound is `Prec` (with the `N^τ` loss) of `‖𝔼 Γ_{xy}‖ ≤ t^{n_W} η_t⁻¹ Bctl^{ord/2}`, where `Bctl` stands for the paper's `W^{-d}B_{t,0}`. It is restricted to joined graphs (`LWJoined`: one molecule, `n_M = 0`). The non-joined case is the merged twin `LwGraphPrec1`, and `lwExpG5'_of_expand'` uses both, so the restriction is a split of the general statement, not a special case standing in for it. The extra `t^{n_W}` factor (stronger, since `t ≤ 1`) is the existing delta D573 (T2255). Quantifier order: the fixed parameters `κ ε 𝔡 𝔠 sz z t` come first, then `P`, then `Prec` (eventual in `n`). Nothing is lost relative to the pin.

(B)–(D): `lwExpG5'_holds := lwExpG5'_of_expand' d (lwG5Expand'_holds d) (lwGraphPrecJoin_holds d)`. `lwCutExp_holds` and `lwTermEXP_holds` are the merged one-step adapters `lwCutExp_of_G5'` and `lwTermEXP_of_cut`. `stStep6I/II/III_holds` are `stStep6I_of_LW`, `ST_step6_caseII_of_pins` (six merged `_holds`) and `ST_step6_caseIII_of_pins` (four merged `_holds`). These match ticket (D) and the source lines 613-632 shown in the prove report.

## 4. Vacuity, hidden hypotheses, cycles
- `LwGraphPrecJoin` is a `def … : Prop` with every hypothesis in the binder list. No structure carries hidden fields.
- External hypothesis `STLocalEntry` (`Induction/Defs.lean:151`, the pin of the `(Gt_bound)` gate): the prove report (a) gives the concrete limit check (Ward sum `t/(1−t) = 1/15` against `Σ_y STWB ≥ 29.1`, diagonal `Bctl → 0`, script output). This satisfies lesson 14.
- `LWExpG5'`, `LWCutExp`, `LWtermEXP` and `STStep6I/II/III` keep their merged pin premises (`STLocalEntry`, `LWAvgLaw`, `STLmax`, `STLK`, `STDecay`, `STIngR`-type premises). Those are the pins' own binders, and this ticket adds none.
- No cycle: `lwGraphPrecJoin_holds` uses only the merged entry and decay lemmas from `LWExpTerm3` (it does not use `LWExpG5'`). The new file imports only merged modules (`LWExpSound`, `LWExpTerm4`, `ExpIntIQ`, `ExpWardII`, `ExpIntEasy`), and the build passes on the `main` cache.

## 5. Compiled nonempty instances (section 7 of the file)
- `lwExpTerm6_inst_join` applies `lwGraphPrecJoin_holds 3` at the merged `sz0`, `z0` (`flow_z0`), `tInst ≡ 1/16` (`tInst_range`), with `κ = ε = 𝔡 = 1/10` and `𝔠 = 1/6`. The graph is the explicit F2 term `Σ_γ S_{γx}S_{xy}G_{xγ}G_{γy}Ḡ_{xy}` (three solid edges, two waved, three dotted). `Normal`, `n_M = 0` and `LWJoined` are proved by `decide`, and the counters are `n_S=3, n_W=2, n_V=1, ord=5`. Only `STLocalEntry` stays as a hypothesis (another gate's pin). This instance is nondegenerate.
- `lwExpTerm6_inst_expand`, `_G5`, `_cut` and `_term` apply the consumer and the chain at the same data, taking `lwG5Expand'_holds 3` and `lwGraphPrecJoin_holds 3` as proved inputs. The pin premises (`STLocalEntry`, `LWAvgLaw`, `STLmax`, `STLK`, `STDecay`) remain hypotheses.
- `lwExpTerm6_inst_step6I/II/III` feed `stStep6*_holds 3` into the merged `inst_step6I/II/III` (`Step6Pins.lean:560-570`). Those discharge the deterministic data through `szB_reg5I`, `szB_reg5II` and `sz0_reg5III`. The stochastic premises of `InstIng6Concl` (`Step6Pins.lean:505-510`: `STLK, STDecay, STExp2, STStep2Core, STLmaxU, STLKU, STGdecayW`) are other gates' pins.
- All of these are compiled in the build above (axioms in §2).

## 6. Paper deltas
- T2334a (prove report (d)): for joined `Γ_μ`, `(Gammamuxy)` is proved directly, not through `GtoAG` as at `B:80`. This covers the route difference.
- `t^{n_W}` factor: already D573. The `N^τ` loss inside `Prec`: same as the twin `LwGraphPrec1`, covered by the existing `≺` convention.
- T2334b is a remark, not a statement difference: the proof uses only `n_M = 0` from `LWJoined`.
No uncovered Lean/paper statement difference was found.

## 7. Observations (no verdict impact)
- The consumer search for the old certificate modules is in the prove report: `LWExpCertS0/S1` and the unprimed `cert_all` have no consumer outside their root imports (`RBM3D.lean:350-351`). Deleting them is for the dispatcher to schedule.
- The prove report's pre-check count (10123 theorems) differs from this run's (10128). The difference comes from the root olean on the copied `main` cache (later merges) and affects nothing.

## Verdicts
| target | verdict |
|---|---|
| `LwGraphPrecJoin` (pin) / `lwGraphPrecJoin_holds` | PASS |
| `lwExpG5'_of_expand'` | PASS |
| `lwExpG5'_holds` | PASS |
| `lwCutExp_holds` | PASS |
| `lwTermEXP_holds` | PASS |
| `stStep6I_holds` | PASS |
| `stStep6II_holds` | PASS |
| `stStep6III_holds` | PASS |

Overall: **PASS**. No dispatcher sign-off needed. At merge the hub adds `import RBM3D.Graph.LWExpTerm6` after the last `import` line of `RBM3D.lean`.
