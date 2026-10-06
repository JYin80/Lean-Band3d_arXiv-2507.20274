Auditor model: claude-opus-5-5

# T2253 audit (UN-17, `RBM3D/Universality/OUContraction.lean`) — round 1, Tue Oct  6 04:57:25 UTC 2026

Branch `t/T2253` at `acb8eef`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2253-audit1` (detached, build cache cloned).
Scratch files: scratchpad `T2253/` (`audit_check.lean`, `audit_check.out`, `main_pre.out`, `build.log`).

## 1. Diff scope
```
$ git diff --name-only main...t/T2253
RBM3D/Universality/OUContraction.lean
$ git diff main...t/T2253 -- RBM3D.lean RBM3D/Test/Axioms.lean | wc -l
       0
```
Only the new sole writable file is touched; `Axioms.lean` unchanged (as the ticket expects); no merged file or frozen signature touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.OUContraction ; grep error build.log ; tail -1
Build completed successfully (3353 jobs).   exit=0, 0 error lines
$ (the 19 `#print axioms` lines of the build log)
centeredVariance_single_contraction_eq depends on axioms: [propext, Classical.choice, Quot.sound]
centeredVariance_wirtingerFirst_product_eq depends on axioms: [propext, Classical.choice, Quot.sound]
centeredVariance_wirtProduct_contraction_eq depends on axioms: [propext, Classical.choice, Quot.sound]
paperK1Contraction_conj depends on axioms: [propext, Classical.choice, Quot.sound]
paperK1Contraction_im_abs_le depends on axioms: [propext, Classical.choice, Quot.sound]
paperK2Contraction_abs_le depends on axioms: [propext, Classical.choice, Quot.sound]
centeredVariance_wirtProduct_kernel_bound depends on axioms: [propext, Classical.choice, Quot.sound]
centeredVariance_wirtProduct_kernel_bound_Lt depends on axioms: [propext, Classical.choice, Quot.sound]
paperK1Contraction depends on axioms: [propext, Classical.choice, Quot.sound]
paperK2Contraction depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.diagH depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.diagH_herm depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.diagH_nonscalar depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.inst_single depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.inst_single_diag depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.inst_wirtFirst_product depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.inst_contraction depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.inst_kernel_bound depends on axioms: [propext, Classical.choice, Quot.sound]
OUContractionInst.inst_kernel_bound_Lt depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE "sorry|admit|native_decide|axiom" OUContraction.lean | grep -v "#print axioms"
(no output)
```

## 3. Statements against the pin (check file `docs/tickets/checks/T2253-check.lean`)
Audit scratch = the check file with `import RBM3D.Universality.OUContraction` added after `import RBM3D`, followed by
20 acceptance examples and `#assert_rbm_axioms` (the check's own consumer-shape `example` and the `UNEMCTE2k` `#check` kept):
```
example : @RBM.Univ.paperK1Contraction = @T2253Check.paperK1Contraction := rfl
example : @RBM.Univ.paperK2Contraction = @T2253Check.paperK2Contraction := rfl
example : RBM.Univ.OUContractionInst.diagH = T2253Check.T2253_diagH := rfl
example : T2253_<name> := @RBM.Univ.<name>            -- for the 8 theorems of targets 1-5 (incl. 4a-4d)
example : T2253_<inst> := RBM.Univ.OUContractionInst.<inst>   -- diagH_herm, diagH_nonscalar, inst_single,
        -- inst_single_diag, inst_wirtFirst_product, inst_contraction, inst_kernel_bound, inst_kernel_bound_Lt
example : ∀ d (sz : Sizes d) n nf H (z : Fin nf → ℂ), H.IsHermitian → (∀ i ∈ univ, 0 < (z i).im) →
    T2253_kernel_bound_Lt_at d (sz.L n) (sz.W n) (sz.lam n) univ H z :=
  fun d sz n nf H z hH hz => RBM.Univ.centeredVariance_wirtProduct_kernel_bound_Lt d _ _ _ _ H hH z hz
$ lake env lean audit_check.lean > audit_check.out 2>&1; echo EXIT $?; grep -c error audit_check.out
EXIT 0
0
```
All 8 theorem statements and both definitions agree with the pin (defeq through the `_at` bodies); hypotheses are exactly
`H.IsHermitian` and `z.im ≠ 0` (targets 1-3) / `0 < (z i).im` (4d, 5); `paperK2Contraction_abs_le` has no Hermitian
hypothesis, as pinned; `lam` is a free real after `d L W` everywhere; no `3 ≤ d`, no `L`–`W` relation (as pinned:
deterministic finite-matrix identities). The consumer example (target 5 at `sz.lam n`, `s = univ : Finset (Fin nf)`)
elaborates by direct application, so the summands match the `UNEMCTE2` integrand shape the ticket names.

Source comparison (target 4d, RBM2D `c9a24cf:…/OUContraction.lean:985-997` after the ticket's mechanical renames vs branch `:1013-1025`):
```
$ diff -w r2.txt r3.txt
1c1
< theorem centeredVariance_wirtProduct_kernel_bound (d L W : ℕ) [NeZero L] [NeZero W]
---
> theorem centeredVariance_wirtProduct_kernel_bound (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
```
Only the pinned new `lam` binder differs.

## 4. Hidden hypotheses, vacuity, cycles, helper naming
```
$ grep -nE "^(noncomputable |protected )?(theorem|lemma|def|abbrev|instance|structure|class|axiom)\b" OUContraction.lean | awk '{print $1,$2,$3}'
62:def paperK1Contraction     69:def paperK2Contraction
78:theorem centeredVariance_single_contraction_eq        215:theorem centeredVariance_wirtingerFirst_product_eq
823:theorem centeredVariance_wirtProduct_contraction_eq  927:theorem paperK1Contraction_conj
952:theorem paperK1Contraction_im_abs_le                 976:theorem paperK2Contraction_abs_le
1013:theorem centeredVariance_wirtProduct_kernel_bound   1077:theorem centeredVariance_wirtProduct_kernel_bound_Lt
1102:def diagH  1105:theorem diagH_herm  1110:theorem diagH_nonscalar  1119:theorem inst_single  1128:theorem inst_single_diag
1136:theorem inst_wirtFirst_product  1150:theorem inst_contraction  1174:theorem inst_kernel_bound  1194:theorem inst_kernel_bound_Lt
$ grep -cE "^private (noncomputable )?(theorem|lemma|def)" ; grep private decls without prefix OUContraction_
21
(no output)
$ grep -nE "\b(structure|class|opaque)\b" OUContraction.lean
(no output)
```
Public names = exactly the pinned ones (instances in `RBM.Univ.OUContractionInst`); 21 helpers all `private OUContraction_*`.
No structure-field hypothesis. Imports: `RBM3D.Universality.OUHessian` (UN-16, merged), `RBM3D.Universality.InjSum`
(UN-03a, merged); nothing imports the new file, so no cycle. No external hypothesis (no limit check needed).

Registry (uncommitted scratch, `import RBM3D` + new module + `#assert_rbm_axioms`, vs `import RBM3D` alone):
```
$ lake env lean audit_check.lean   (with new module)          | $ lake env lean main_pre.lean   (main library only)
EXIT 0                                                         | EXIT 0
premises found by scanning: 154 (borrowed 1, owed 98, structural 38, refuted 6, superseded 11).   (identical in both)
registry: 2 borrowed + 157 owed + 98 structural + 7 refuted + 12 superseded                        (identical in both)
axiom audit: … 0 axioms in `RBM`                                                                   (both)
```
No new premise; owed count unchanged; no refuted/superseded name enters.

## 5. Compiled nonempty instances (endpoint theorems)
File `:1100-1235`, all compiled in the module build (§2) and checked defeq to the check's §2.6 (§3):
| target | instance | data | hypotheses discharged |
|---|---|---|---|
| 1 | `inst_single`, `inst_single_diag` | `d=3,L=3,W=2` (`N=216`), `lam=1/2`, `H=1` / `diagH`, `z=I` | `isHermitian_one` / `diagH_herm`, `(by simp)` for `I.im ≠ 0` |
| 2 | `inst_wirtFirst_product` | `diagH`, `z₁=I`, `z₂=2I` | `diagH_herm`, two `(by simp)` |
| 3 | `inst_contraction` | `diagH`, `ι=Fin 2`, `s=univ`, `z=![I,2I]` | `diagH_herm`, `fin_cases i <;> simp` |
| 4d | `inst_kernel_bound` | `H=1`, `s=univ : Finset (Fin 2)`, `z=![I,2I]` | `isHermitian_one`, `fin_cases i <;> simp` |
| 5 | `inst_kernel_bound_Lt` | `diagH`, same `s`, `z` | `diagH_herm`, `fin_cases i <;> simp` |
`diagH` non-scalar (`diagH_nonscalar`: entries `0 ≠ 1/3` at `OUHessianInst.x0`, `x1`), compiled. No `N = 0`, no empty
index (`|s| = 2`, so both the single and the ordered-pair sums are nonempty), no `False` premise, no large witness.
Targets 4a-4c are intermediate lemmas (pinned in check §2.4 without instances); each is used by 4d, whose instance
compiles; this matches the ticket's instance list (target 6).

## 6. Paper deltas
No Lean/paper statement difference: the statements equal the pinned port (RBM2D up to `d`, `lam`), and §3 shows the
only source delta is the pinned `lam` binder (already in the merged UN-16 vocabulary). The prove report (d) proposes
**T2253a** (design notes, as the ticket specifies) and states T2253b: none. Coverage complete.

## 7. Observations (no verdict effect)
- Prove report (b) says "19 `#print axioms` lines"; the file has 19 (`grep -c "#print axioms"`), consistent.
- `inst_kernel_bound` uses `H = 1`, where `K₁ = 0` (preflight (a)); the non-scalar `diagH` instance of the same bound
  shape is `inst_kernel_bound_Lt`, so the bound is exercised at nontrivial data.

## Verdicts
| target | verdict |
|---|---|
| defs `paperK1Contraction`, `paperK2Contraction` | PASS |
| 1 `centeredVariance_single_contraction_eq` | PASS |
| 2 `centeredVariance_wirtingerFirst_product_eq` | PASS |
| 3 `centeredVariance_wirtProduct_contraction_eq` | PASS |
| 4a `paperK1Contraction_conj`, 4b `paperK1Contraction_im_abs_le`, 4c `paperK2Contraction_abs_le` | PASS |
| 4d `centeredVariance_wirtProduct_kernel_bound` | PASS |
| 5 `centeredVariance_wirtProduct_kernel_bound_Lt` | PASS |
| 6 instances `RBM.Univ.OUContractionInst.*` | PASS |

**Overall: PASS.** No dispatcher sign-off needed. Hub: add `import RBM3D.Universality.OUContraction` after the last
`import` line of `RBM3D.lean` and run the full `lake build` at merge.
