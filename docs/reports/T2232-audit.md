Auditor model: claude-opus-5-5
# T2232 audit (S6-10, `Induction/ExpWardI`), round 1 — Tue Oct  6 00:46:04 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2232-audit1`, detached at `37b7c91` (t/T2232); merge base `b750bf3`; `main` = `e64e4f0`.
Route taken: **U** (unsigned `STExpWardI` proved for every real `C, c`; primed `STExpWardI'` from it in one line). Scratch: `scratchpad/T2232/`.

## 1. Statement (check-file equality, by script)
`checkeq.lean` = check-file imports + `import RBM3D.Induction.ExpWardI` + check sections 1–2 (lines 1–244) + one
`example : RBM.Gauss.Sizes.T2232Check.X := @RBM.Gauss.Sizes.X` for the 9 route-U pins + two `rfl` examples for
`STExpWardI'`, `STExpWardIConcl'` + section 3 with each `example : Prop := S` rewritten to `example : S := @RBM.Gauss.Step6Inst.<inst>`.
```
$ grep -n "^example\|  @RBM.Gauss.Step6Inst" checkeq.lean
247:example : RBM.Gauss.Sizes.T2232Check.expWI_Psum_eq := @RBM.Gauss.Sizes.expWI_Psum_eq
248:example : RBM.Gauss.Sizes.T2232Check.expWI_Psum_prec := @RBM.Gauss.Sizes.expWI_Psum_prec
249:example : RBM.Gauss.Sizes.T2232Check.expWI_window := @RBM.Gauss.Sizes.expWI_window
250:example : RBM.Gauss.Sizes.T2232Check.expWI_vth_le := @RBM.Gauss.Sizes.expWI_vth_le
251:example : RBM.Gauss.Sizes.T2232Check.expWI_core' := @RBM.Gauss.Sizes.expWI_core'
252:example : RBM.Gauss.Sizes.T2232Check.expWI_core := @RBM.Gauss.Sizes.expWI_core
253:example : RBM.Gauss.Sizes.T2232Check.expWI_concl_prime := @RBM.Gauss.Sizes.expWI_concl_prime
254:example : RBM.Gauss.Sizes.T2232Check.stExpWardI'_holds := @RBM.Gauss.Sizes.stExpWardI'_holds
255:example : RBM.Gauss.Sizes.T2232Check.stExpWardI_holds := @RBM.Gauss.Sizes.stExpWardI_holds
256:example : @RBM.Gauss.Sizes.T2232Check.STExpWardI' = @RBM.Gauss.Sizes.STExpWardI' := rfl
257:example : @RBM.Gauss.Sizes.T2232Check.STExpWardIConcl' = @RBM.Gauss.Sizes.STExpWardIConcl' := rfl
265:example :
268:  @RBM.Gauss.Step6Inst.inst_expWardI'
272:example :
291:  @RBM.Gauss.Step6Inst.inst_expWardI'_mixed
294:example :
297:  @RBM.Gauss.Step6Inst.inst_expWardI_holds
$ lake env lean checkeq.lean 2>&1 | grep error | head; echo "exit=${pipestatus[1]}"
exit=0
```
Every public theorem of the file has exactly the check-file (dispatcher-pinned) statement; the two new `Prop`s are
definitionally the pinned ones. `stExpWardI_holds : STExpWardI d` proves the **merged** pin `Step6Pins.lean:361` (unchanged,
see §4), whose conclusion `STExpWardIConcl` (`:342`) quantifies over every real `C, c` and is uniform in `u ∈ TimeIcc s t`,
`σ₀ ≠ σ₁`, `a`, with the losses `Bctl³` and `(1-u)⁻¹Bctl³` of `(eq:EPL-K)`, `(eq:boundELKQ1)`, `(eq:boundcommutator)`
(`6:104-132`). `expWI_Psum_eq` is the expectation of Ward's identity: `(2iW^dη_u)⁻¹((𝔼L₊-m₊)-(𝔼L₋-m₋))` = `Im 𝔼tr((G-M)E_{a₁})/(W^dη_u)`, as at `6:105`.
Hypotheses of `expWI_core` (`3 ≤ d`, `0<κ,ε,𝔡`, `STFlow`, `0 ≤ s < t ≤ lemT`, `STReg5I`, `STExpAvgU`) are a subset of the
`STIngR6` premises; no new premise. Quantifier order: fixed parameters before the eventual `Prec`; `ϑ`'s mollifier property eventual.

## 2. Vacuity, hidden hypotheses, cycles
- New definitions are two `def … : Prop` (no `structure`); no hypothesis is carried in a structure field.
- Declarations (script): 9 public theorems + 2 defs in `RBM.Gauss.Sizes`, 7 instances in `RBM.Gauss.Step6Inst`; all other
  declarations `private` with prefix `expWI_` (`expWI_integrable_Lloop`, `_LK`, `expWI_int_LK`, `expWI_int_Psum`, `expWI_sgnCons`,
  `expWI_pw`, `expWI_scale`, `expWI_pt`, `expWI_K1`, `expWI_K2`, `expWI_step`).
- Imports (file lines 6–16) are the 11 check-file imports, all merged modules; no `import RBM3D`; no cycle.
- `stExpWardI_holds` uses only `STReg5I` and `STExpAvgU` among the `STIngR6` premises (the others are discarded by `_`),
  with `𝔠_d = 1/100`; the premise `STExpAvgU` is S6-03's merged conclusion (`stImproveExpAver_holds`), not a new external input.
  The preflight's limit check (report (a)(ii) last paragraph: `N^τ Bctl² ≍ W^{3τ-6} → 0`, envelope `‖Lloop^{(1)}‖ ≤ η_u⁻¹ = 16.5`) shows it is a genuine decay statement.

## 3. Compiled nonempty instances (file lines 469–550; all compiled in the build below)
| endpoint | instance | data / what stays a hypothesis |
|---|---|---|
| `stExpWardI'_holds` | `inst_expWardI'` = `inst_ing6_I STReg5I _ (stExpWardI'_holds 3) szB_reg5I` | `d=3`, `szB` (`L=4`, `W_n=n+4`, `lam=1`), `zB = 1/2+i/64`, `(7/8,15/16)`; flow/time/regime discharged; stochastic premises of `InstIng6Concl` (`Step6Pins.lean:505-510`) stay |
| `stExpWardI_holds` | `inst_expWardI_holds` = `inst_expWardI (stExpWardI_holds 3)` | same data; the merged `inst_expWardI` hypothesis `h` is now discharged |
| `expWI_core'`, `expWI_core`, `expWI_concl_prime` | `inst_expWardI'_mixed` | positive family from `st6_mollifier_family` (`0<C ∧ 0<c` exhibited), `flow_zB`, `szB_flow_ht`, `szB_reg5I`; only `STExpAvgU` at the instance stays |
| `expWI_Psum_eq` | `inst_expWI_Psum_eq` | `n=0` (`W=4`, `L=4`), `E=0`, `u=7/8`, `σ=![true,false]` (`decide`), `a₁=0`; no hypothesis left |
| `expWI_Psum_prec` | `inst_expWI_Psum_prec` | `szB`, `zB`, `(7/8,15/16)`; `STExpAvgU` stays |
| `expWI_window` | `inst_expWI_window` | `szB`, `u ∈ [7/8,15/16]` (positive-length window), `0 < lam` by `simp [szB]` |
| `expWI_vth_le` | `inst_expWI_vth_le` | `d=3`, `L=4`, `g=1`, `u=3/4` (`√(1/4)=1/2`, `ℓ_u=2 ∈ [1,4]`), mollifier of `stMollifierEx_holds` with `0<C`, `0<c` |
No `N = 0`, empty index, collapsed window, `False` premise or astronomically large witness. Hypotheses left are other gates'
pins/conclusions (`STExpAvgU`, the `InstIng6Concl` stochastic premises), as the ticket allows.

## 4. Build, axioms, scope
```
$ lake build RBM3D.Induction.ExpWardI 2>&1 | grep -E "error|declaration uses|Build completed"; echo "exit=${pipestatus[1]}"
Build completed successfully (3869 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/ExpWardI.lean; echo grep_exit=$?
grep_exit=1
$ lake env lean ax.lean | sed 's/depends on axioms: //'   # #print axioms of all 16 public names
'RBM.Gauss.Sizes.expWI_Psum_eq' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_Psum_prec' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_window' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_vth_le' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_core' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_concl_prime' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_core'' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpWardI_holds' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpWardI'_holds' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWardI'' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWardI_holds' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWardI'_mixed' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWI_Psum_eq' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWI_Psum_prec' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWI_window' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWI_vth_le' [propext, Classical.choice, Quot.sound]
$ git diff --stat main...t/T2232
 RBM3D/Induction/ExpWardI.lean | 550 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   2 +-
$ git diff main...t/T2232 -- Step6Pins.lean Step6Kit.lean ExpIniI.lean B45.lean | wc -l
       0
$ git merge-tree --write-tree main t/T2232 >/dev/null; echo merge_tree_exit=$?     # main = e64e4f0
merge_tree_exit=0
```
`Axioms.lean` diff (route U, exactly the ticket's lines): `-` owed `RBM.Gauss.Sizes.STExpWardI` (S6-10 line);
`+` structural `RBM.Gauss.Sizes.STExpWardIConcl'` after `STExpIniIConcl'`, before `RBM.Endpoints.locBad1]`.

Registry pre-check (`lake build RBM3D` in the audit worktree without the root import fails, as expected, since the owed line
is deleted while the module is not yet imported: `error: RBM3D.lean:275:0: axiom audit: 1 premise(s) that no theorem of this
development proves are in none of …`). With a scratch copy `root.lean` of `RBM3D.lean` plus `import RBM3D.Induction.ExpWardI`
after the last import line (no source edited):
```
$ lake env lean root.lean > root.out 2>&1; echo exit=$?
exit=0
$ grep -nE "axiom audit|premises found|registry:|error" root.out | cut -c1-120
1:axiom audit: 6819 theorems, 2330 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
155:premises found by scanning: 129 (borrowed 1, owed 95, structural 27, refuted 6).
156:registry: 2 borrowed + 146 owed + 85 structural + 7 refuted; 111 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
```
Owed 146 (= base 147 − 1), structural 85 (= base 84 + 1): matches the route-U plan. **Merge note for the hub:** the root
import `import RBM3D.Induction.ExpWardI` must land in the same commit as the `Axioms.lean` change (rule (A) step 4).

## 5. Paper deltas
- Lean stronger than the paper: `STExpWardIConcl` (hence `stExpWardI_holds`) holds for every real `C, c` (paper: mollifier
  with `c > 0`, `Def:QtPt` `3_5:1214`). Proposed as **T2232a** in prove report (d); the analogous S6-11 delta is D542 (T2223a)
  in `docs/paper-deltas.md:1501`. Covered.
- `(eq:boundELKQ1)` + `(eq:boundcommutator)` as one `Prec` of their sum: the shape of the merged pin (no loss); noted in (d).
- No step needed a hypothesis the pin lacks (no `T2232b`). No uncovered Lean/paper difference found.

## 6. Observations (no statement, instance, build, axiom or delta effect)
- The four public `inst_expWI_*` names carry the stem `expWI_` after `inst_`, not as a prefix; prove report name-clash grep: 0 hits on `main`.
- Prove report's line references to the ticket (`Axioms.lean:232`) were updated to the base `b750bf3` (`:239`); deletion is by text, so no effect.

## Verdict
| target | verdict |
|---|---|
| 1 `expWI_Psum_eq` | PASS |
| 2 `expWI_Psum_prec` | PASS |
| 3 `expWI_window`, 4 `expWI_vth_le` | PASS |
| 5 `STExpWardIConcl'`, `STExpWardI'`, `expWI_core'` | PASS |
| 6 `stExpWardI'_holds` | PASS |
| 7 (route U) `expWI_core`, `expWI_concl_prime`, `stExpWardI_holds` | PASS |
| 8 `inst_expWardI'`, `inst_expWardI'_mixed`, `inst_expWardI_holds` | PASS |
**Overall: PASS.** No dispatcher sign-off needed.
