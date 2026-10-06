Auditor model: claude-opus-5-5

# T2247 audit (UN-16, `RBM3D/Universality/OUHessian.lean`), round 1, Tue Oct  6 03:37:48 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2247-audit1`, detached at `t/T2247` = `6386334`.
Scratch: `scratchpad/T2247/cmp.lean` = `docs/tickets/checks/T2247-check.lean` sections 1-2 verbatim, plus
`import RBM3D.Universality.OUHessian`, plus the audit `example`s and `#print axioms` lines below.

## 1. Diff scope, hygiene
```
$ git diff --stat main...t/T2247
 RBM3D/Universality/OUHessian.lean | 1322 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1322 insertions(+)
$ git diff main...t/T2247 --name-only | grep -v '^RBM3D/Universality/OUHessian.lean$'   -> (no output; exit 1)
$ grep -nE "sorry|admit|native_decide|^axiom|axiom " RBM3D/Universality/OUHessian.lean   -> grep exit 1
$ grep -n "^import" RBM3D/Universality/OUHessian.lean
6:import Mathlib.Analysis.Calculus.Deriv.Add
7:import Mathlib.Analysis.Calculus.Deriv.Mul
8:import Mathlib.Analysis.Calculus.FDeriv.Mul
9:import Mathlib.Analysis.Analytic.Constructions
10:import RBM3D.Universality.Pins
11:import RBM3D.Green.FlucVanish
12:import RBM3D.Induction.ConArgDet
```
Only the sole writable file; `Test/Axioms.lean` untouched (as the ticket expects); no merged file changed, so no
frozen signature touched. Imports are merged modules only (no `RBM3D`, no `Graph/*`): no cycle.
No `structure`/`class` declared (outline grep of `^(private )?(noncomputable )?(theorem|lemma|def|abbrev|instance|
structure|class|example)`: only `theorem`/`def`/`example`). Unpinned helpers are all `private OUHessian_*`
(lines 72-117, 285-478, 494-641, 895-934, 998); the only unpinned public name is `OUHessianInst.x0_ne_x1`
(instance namespace).

## 2. Build
```
$ lake build RBM3D.Universality.OUHessian; echo exit $?
(warnings only, all in other merged files: Defs/Tail.lean line length, Green/LDEQuad.lean `show` linter)
Build completed successfully (3350 jobs).
exit 0
```

## 3. Statements vs the ticket's pin (check file sections 2.1-2.6), by compilation
`cmp.lean` contains, after the check's sections 1-2:
```
example : @RBM.Univ.<v> = @RBM.Univ.T2247Check.<v> := rfl
  for v in coordD1 coordD2 wirtSecond stieltjesImAlong stieltjesImLineFirst stieltjesImLineSecond
  stieltjesImProductLineSecond signedGreen stieltjesImWirtingerFirst centeredVarianceEntry paperL1Kernel paperL2Kernel
example : RBM.Univ.OUHessianInst.x0 = T2247_x0 := rfl ;  example : RBM.Univ.OUHessianInst.x1 = T2247_x1 := rfl
example : T2247_<t> := @RBM.Univ.<t>
  for t in Bmat_swap_true Bmat_swap_false Bmat_isHermitian_of_ne_or hasDerivAt_deriv_finset_product_expansion
  hasDerivAt_green_hermitianLine hasDerivAt_stieltjesN_hermitianLine hasDerivAt_stieltjesFirstVariation
  fderiv_fderiv_stieltjesImProduct_hermitianLine wirtSecond_stieltjesImProduct_expansion
  stieltjesImWirtingerFirst_entry_formula stieltjesImWirtingerFirst_adjoint_formula
  wirtSecond_stieltjesIm_entry_formula centeredVarianceEntry_symm centeredVarianceEntry_cast signedGreen_eq_Gres
  paperL1Kernel_eq_L1t paperL2Kernel_eq_L2t
example : T2247_<i> := RBM.Univ.OUHessianInst.<i>
  for i in inst_directions inst_entry inst_product inst_wirtFirst inst_kernels inst_green_line inst_stieltjes_line
example (d) (sz : RBM.Gauss.Sizes d) (n) (H) (z) :      -- check section 3, UNEMCTE2 consumer shape (Pins.lean:675)
    paperL1Kernel d (sz.L n) (sz.W n) (sz.lam n) H z = L1t d (sz.L n) (sz.W n) (sz.lam n) H z :=
  paperL1Kernel_eq_L1t _ _ _ _ _ _
```
```
$ lake env lean scratchpad/T2247/cmp.lean; echo exit $?
exit 0
$ grep -c error cmp.out
0
```
All 12 vocabulary definitions are definitionally the pinned bodies; all 17 theorems (targets 1-4) and all 7
instances (target 5) inhabit the pinned `Prop`s with no adapter (no `fun … =>` needed; `Bmat_swap_*` omit
`NeZero` as the check states). Hypotheses, quantifier order, index types (`Idx d L W`, generic `n`, `ι`), `lam`
position (after `d L W`), `N = Fintype.card (Idx d L W)` and the `(N⁻¹)` powers match the pin exactly.
No special case: targets are stated for every `d L W` (resp. every finite `n`, `ι`), no `3 ≤ d`, as the ticket
specifies. `paperL1Kernel_eq_L1t`/`paperL2Kernel_eq_L2t` carry no `IsHermitian` hypothesis — this is the pin
(stronger than RBM2D `:1079, :1086`), covered by T2247a.

## 4. Axioms (same scratch file, 24 `#print axioms`)
```
Bmat_swap_true, Bmat_swap_false, Bmat_isHermitian_of_ne_or, hasDerivAt_deriv_finset_product_expansion,
hasDerivAt_green_hermitianLine, hasDerivAt_stieltjesN_hermitianLine, hasDerivAt_stieltjesFirstVariation,
fderiv_fderiv_stieltjesImProduct_hermitianLine, wirtSecond_stieltjesImProduct_expansion,
stieltjesImWirtingerFirst_entry_formula, stieltjesImWirtingerFirst_adjoint_formula,
wirtSecond_stieltjesIm_entry_formula, centeredVarianceEntry_symm, centeredVarianceEntry_cast, signedGreen_eq_Gres,
paperL1Kernel_eq_L1t, paperL2Kernel_eq_L2t, OUHessianInst.{inst_directions, inst_entry, inst_product,
inst_wirtFirst, inst_kernels, inst_green_line, inst_stieltjes_line}:  [propext, Classical.choice, Quot.sound]
OUHessianInst.x0_ne_x1:  [propext, Quot.sound]
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" cmp.out
24
```

## 5. Compiled nonempty instances (file lines 1173-1318; `d = 3, L = 3, W = 2`, `N = 216`, `lam = 1/2`)
Data: `H = 1` (`Matrix.isHermitian_one`), `z = I`, `2I` (`by simp` for `im ≠ 0`), `x0 = 0 ≠ x1 = Pi.single 0 1`
(`x0_ne_x1`, proved via `congrFun h 0` and `(0 : ZMod 6) ≠ 1` by `decide`), line instances at `n = Fin 2`,
`H = A = 1`, `t = 0`. No premise is kept; no empty index; `N = 216` (`inst_kernels` first conjunct).
| target | instance |
|---|---|
| 1a-1c `Bmat_swap_true/false`, `Bmat_isHermitian_of_ne_or` (both disjuncts) | `inst_directions` |
| 2a `hasDerivAt_deriv_finset_product_expansion` | `example` line 1293 (`Fin 2`, `f i t = t`) |
| 2b `hasDerivAt_green_hermitianLine` | `inst_green_line` |
| 2c `hasDerivAt_stieltjesN_hermitianLine` | `inst_stieltjes_line` |
| 2d `hasDerivAt_stieltjesFirstVariation` | `example` line 1308 |
| 2e `fderiv_fderiv_stieltjesImProduct_hermitianLine` | `example` line 1299 (`z = ![I, 2I]`) |
| 3a `wirtSecond_stieltjesImProduct_expansion` | `inst_product` (off-diagonal branch via `ite_eq_right x0_ne_x1`) |
| 3b `stieltjesImWirtingerFirst_entry_formula` | `example` line 1314 |
| 3c `stieltjesImWirtingerFirst_adjoint_formula` | `inst_wirtFirst` |
| 3d `wirtSecond_stieltjesIm_entry_formula` | `inst_entry` (2nd conjunct) |
| 4a, 4b `centeredVarianceEntry_symm/_cast` | `inst_kernels` (conj. 2, 3) |
| 4c `signedGreen_eq_Gres` (σ = false, the non-trivial tag) | `inst_kernels` (conj. 4) |
| 4d `paperL1Kernel_eq_L1t` / 4e `paperL2Kernel_eq_L2t` | `inst_entry` (conj. 1) / `inst_kernels` (conj. 5) |
Every endpoint theorem is applied at concrete nondegenerate data with every hypothesis discharged; all compile
(§2, §3).

## 6. Hidden hypotheses, vacuity, external inputs
Hypotheses of every target are `Matrix.IsHermitian`, `z.im ≠ 0`, `i ≠ j ∨ b = true`, `i ≠ j`, and the
differentiability premises of 2a — Mathlib predicates, all satisfiable together (§5). No new `Prop` pin, no
structure field, no external hypothesis (no limit check needed). Registry unchanged, consistent with the ticket
(no owed pin proved or added).

## 7. Name clashes (`git grep -nw <name> main -- RBM3D RBM3D.lean`, Probe excluded; 30 names incl. `OUHessianInst`)
```
Bmat_swap_true: 1   main:RBM3D/Green/IBP.lean:406:`Bmat_swap_true`, `Generator:916`). -/
Bmat_swap_false: 1  main:RBM3D/Green/IBP.lean:421:... (RBM1D `Bmat_swap_false`, `Generator:930`). -
(all other names: 0 hits)
```
Both hits are docstrings (declarations there are `private IBP_Bmat_swap_*`, as the ticket records): no clash.

## 8. Paper deltas
The file states nothing new about the paper's `L_{1,t}`, `L_{2,t}`; the bridges land on the merged `L1t`/`L2t`.
The only statement difference from the source (dropped `IsHermitian` in 4d/4e; private copies of RBM2D
`Gauss.hasDerivAt_line`/`_lineInverse`/`isHermitian_add_realSmul`; UN-16 precedes UN-15) is proposed as **T2247a**
in the prove report §(d). No uncovered difference.

## 9. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. Prove report §(b) labels `x0_ne_x1` as "(statement = check 2.6 `T2247_x0_ne_x1`)"; the check has no such
  def (it is the first conjunct of `T2247_inst_directions`). Harmless.
- O2. The `H = 1, z = I` instances make `L1t = 0` (row sums of `S°` vanish; prove report (a)(ii)); the identities
  are still applied at nondegenerate data, and the report's numerical run at a random Hermitian `H` has `L1t > 0`.
- O3. Docstring of `inst_directions` reads "`inst_directions` ." (stray space). Cosmetic.

## Verdict
| target | statement | hidden hyp./vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 directions | = pin | none | yes | ok | n/a | PASS |
| 2 line Hessian | = pin | none | yes | ok | n/a | PASS |
| 3 Wirtinger | = pin | none | yes | ok | n/a | PASS |
| 4 kernels/bridges | = pin (no `IsHermitian`, per pin) | none | yes | ok | T2247a | PASS |
| 5 instances | = pin | none | — | ok | n/a | PASS |

**T2247: PASS.** No dispatcher sign-off needed. Hub merge: add `import RBM3D.Universality.OUHessian` after the
last `import` line of `RBM3D.lean`; nothing to merge in `Test/Axioms.lean`.
