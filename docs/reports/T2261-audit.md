Auditor model: claude-opus-5-5

# T2261 audit (round 1): UN-15 `Universality/OUGenerator`. Time: Tue Oct  6 06:16:49 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2261-audit1`, detached at `t/T2261` = `335f9a2`; merge-base with main = `193512b` (main HEAD).

## 1. Scope: files touched
```
$ git diff --stat main...t/T2261
 RBM3D/Universality/OUGenerator.lean | 1369 +++++++++++++++++++++++++++++++++++
 1 file changed, 1369 insertions(+)
```
This is one of the sole writable files. `RBM3D/Test/Axioms.lean` is untouched, as the ticket expects (no owed pin is proved and no premise is added). No merged file and no frozen signature is touched. Imports (`sed -n 6,10p`): `RBM3D.Universality.OU`, `RBM3D.Universality.OUHessian`, `RBM3D.Gauss.SteinMatrix`, `RBM3D.Gauss.DominationAt`, `Mathlib.Analysis.Calculus.ContDiff.Bounds`. All are merged modules. The file does not import `RBM3D` or `Graph/*`, so there is no cycle.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.OUGenerator
⚠ [3356/3356] Built RBM3D.Universality.OUGenerator (5.7s)
warning: RBM3D/Universality/OUGenerator.lean:15:100: This line exceeds the 100 character limit ...   (14 such, lines 15-38: module docstring)
info: ...OUGenerator.lean:1356:0: 'RBM.Univ.TestFunH' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1357:0: 'RBM.Univ.ouGeneratorPair_hasDerivAt_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1358:0: 'RBM.Univ.ouGeneratorPair_integral_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1359:0: 'RBM.Univ.ouMat_band_eq_ouPairMat' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1360:0: 'RBM.Univ.ouP_band_map_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1361:0: 'RBM.Univ.ouGenerator_hasDerivAt_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1362:0: 'RBM.Univ.ouGenerator_integral_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1363:0: 'RBM.Univ.testFunH_stieltjesImProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1364:0: 'RBM.Univ.OUGeneratorInst.inst_testFunH' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1365:0: 'RBM.Univ.OUGeneratorInst.inst_pair_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1366:0: 'RBM.Univ.OUGeneratorInst.inst_band_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1367:0: 'RBM.Univ.OUGeneratorInst.inst_band_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3356 jobs).
exit=0
$ grep -E '^error' build.log | wc -l                                  -> 0
$ grep OUGenerator warnings other than 'exceeds the 100' | wc -l      -> 0
$ grep -nE 'sorry|admit|native_decide|^axiom|axiom ' RBM3D/Universality/OUGenerator.lean ; echo $?   -> 1 (no hit)
```
The `set_option` lines in the file (46-52) are linters only (`unusedSectionVars`, `unusedVariables`, `unusedSimpArgs`, `unnecessarySeqFocus`, `unusedDecidableInType`, `unusedFintypeInType`, `style.longLine`). None of them is `maxHeartbeats` or `autoImplicit`, so none affects soundness.

## 3. Statements against the pins (compiled diff)
Scratch file `scratchpad/T2261/audit_check.lean` is built as follows. Take the dispatcher check file `docs/tickets/checks/T2261-check.lean` verbatim. Add `import RBM3D.Universality.OUGenerator` after `import RBM3D`. Then append the following, inside `namespace RBM.Univ.T2261Check`:
```
example : T2261_ouGeneratorPair_hasDerivAt_integral := @RBM.Univ.ouGeneratorPair_hasDerivAt_integral
example : T2261_ouGeneratorPair_integral_sub_eq := @RBM.Univ.ouGeneratorPair_integral_sub_eq
example : T2261_ouMat_band_eq_ouPairMat := @RBM.Univ.ouMat_band_eq_ouPairMat
example : T2261_ouP_band_map_pair := @RBM.Univ.ouP_band_map_pair
example : T2261_ouGenerator_hasDerivAt_integral := @RBM.Univ.ouGenerator_hasDerivAt_integral
example : T2261_ouGenerator_integral_sub_eq := @RBM.Univ.ouGenerator_integral_sub_eq
example : T2261_testFunH_stieltjesImProduct := @RBM.Univ.testFunH_stieltjesImProduct
example : T2261_inst_testFunH := RBM.Univ.OUGeneratorInst.inst_testFunH
example : T2261_inst_pair_sub_eq := RBM.Univ.OUGeneratorInst.inst_pair_sub_eq
example : T2261_inst_band_hasDerivAt := RBM.Univ.OUGeneratorInst.inst_band_hasDerivAt
example : T2261_inst_band_sub_eq := RBM.Univ.OUGeneratorInst.inst_band_sub_eq
example : @RBM.Univ.TestFunH = @TestFunH := rfl
example : @RBM.Univ.ouPairP = @ouPairP := rfl
example : @RBM.Univ.ouPairMat = @ouPairMat := rfl
example : @RBM.Univ.OUGeneratorInst.Phi2 = @Phi2 := rfl
-- auditor extras: P1, T1, T2 at concrete data
example := RBM.Univ.ouGeneratorPair_hasDerivAt_integral 3 3 2 (1 / 2) _
  (RBM.Univ.OUGeneratorInst.inst_testFunH) 1 one_pos
example := RBM.Univ.ouP_band_map_pair 3 sz0 0
example (ω) := RBM.Univ.ouMat_band_eq_ouPairMat 3 sz0 0 1 ω
example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 := by decide
```
```
$ lake env lean scratchpad/T2261/audit_check.lean ; echo exit=$? ; grep -c error check.out
exit=0
0
```
Result: every target statement (P1, P2, T1, T2, B1, B2, S) and every instance statement compiles as the pinned `T2261_<name>` Prop, token for token up to definitional equality, with the binders, quantifier order and hypotheses of the check file. The vocabulary (`TestFunH`, `ouPairP`, `ouPairMat`, `Phi2`) is `rfl`-equal to the check vocabulary.

Statement-level points I checked against the ticket's mathematics:
- **Constant and weights.** The coefficient is `-(1/2) e^{-t}`. `S° = centeredVarianceEntry d L W g`, and `OUHessian.lean:1115` defines it as `svarF d L W lam a b - (card (Idx d L W))⁻¹`. `gueVar` (`Pins.lean:61`) uses `((W*L)^d)⁻¹` on the diagonal and `(2(W*L)^d)⁻¹` off it, so `N = card Idx`. This matches the ticket formula `d/dt E Φ(H_t) = -½ e^{-t} Σ S°_ab E wirtSecond Φ (H_t) a b`.
- **Time ranges.** P1 and B1 require `0 < t`; P2 and B2 require `0 ≤ T`. This is §29 (1) as pinned. There is no `∀ᶠ`, no grid, no `3 ≤ d`, and no relation between `L` and `W`.
- **Hypotheses.** The only hypotheses are `TestFunH Φ`, `0 < t` / `0 ≤ T`, and `0 < (z i).im` (for S).
  - `TestFunH` is a `def … : Prop` (four conjuncts). It is not a structure field, so it hides no hypothesis.
  - It is discharged at concrete data by S, through `phi2_testFunH`.
  - There is no external hypothesis, so the limit check of TEAM §8 lesson 14 does not apply.
- **Special-case status (§5.6).**
  - P1 and P2 are general: any `d`, any `L`, `W` with `NeZero`, and any real `g`.
  - B1 and B2 hold only for the band model `UNModel.band sz` at `g = sz.lam n`. This is exactly the pinned consumer form. They are not a general-`UNModel` generator. The ticket says so and so does the prove report ((b) narrative; T2261a (3)).
- **Proof chain.** B1 is proved from P1 and B2 from P2 (`sed -n 1057-1090`), via T2 (`ouP_band_map_pair`) and `integral_map` with measurability from `measurable_slice`. T1 is `rfl` (`:1002-1008`).
- **Private items.** The private instance `OUGenerator_isProbabilityMeasure_ouPairP` is `unfold ouPairP; infer_instance`. It is not a premise. There are 71 private declarations, all with the prefix `OUGenerator_`.

Name clash: `git grep -nwE 'def|theorem|lemma|abbrev|structure' main -- 'RBM3D/*.lean' | grep -wE '<the 11 new public names / OUGeneratorInst>' | wc -l` gives `0`.

## 4. Compiled nonempty instances (same file, `namespace RBM.Univ.OUGeneratorInst`, lines 1297-1350)
| target | instance | data | hypotheses discharged by |
|---|---|---|---|
| S | `inst_testFunH` (+ `phi2_testFunH`) | `d=3, L=3, W=2`, `z = ![I, 2I]` | `zIm_pos` (`fin_cases i <;> simp`) |
| P2 | `inst_pair_sub_eq` | `d=3,L=3,W=2`, `g=1/2`, `T=1`, `Φ=Phi2` | `inst_testFunH`, `zero_le_one` |
| B1 | `inst_band_hasDerivAt` | `UNModel.band sz0`, `n=0`, `t=1` | `phi2_testFunH`, `one_pos` |
| B2 | `inst_band_sub_eq` | `UNModel.band sz0`, `n=0`, `T = ouTStar sz0 (1/2) 0` | `phi2_testFunH`, `Real.rpow_nonneg (Nat.cast_nonneg _) _` |

- **No vacuity.** No hypothesis is left open. `Idx 3 3 2` has `N = 216`. `sz0` at `n = 0` has `L = 4`, `W = 32` (compiled `by decide` above), so `N = 2^21`. `T = 1` and `T = N^{-1/2}` are positive. There is no `False` premise and no collapsed window.
- **P1, T1, T2.** The ticket pins no instance of its own for these. They are exercised as follows:
  - P1 is applied by B1 at `sz0` and by the auditor's extra example at `d=3, L=3, W=2, g=1/2, t=1`.
  - T2 is applied inside B1 and B2 and by the auditor's extra example at `sz0, n=0`.
  - T1 has no hypotheses.
  - All extras compile (section 3).

## 5. Paper deltas
`grep -n T2261 docs/paper-deltas.md` returns no hit, which is expected before merge. The prove report (d) proposes the following:
- T2261a (1): pair carrier plus push-forward instead of the `ouSample_law` route.
- T2261a (2): the RBM2D names are used for the band consumer form.
- T2261a (3): B1 and B2 are band-only (no drift term).
- T2261a (4): the RBM2D source changed after `c9a24cf`; this is informational.

These cover every Lean-vs-paper difference I found: the band-only restriction, the coupling `g = sz.lam n`, the pair carrier, and `N = (WL)^d`. There is no `T2261c` (no deviation from the pinned statements).

## 6. Observations (no effect on verdict)
- **O1.** The module docstring has 14 long-line lint warnings (lines 15-38) because they come before `set_option linter.style.longLine false`. This is cosmetic.
- **O2.** The prove report's build tail reads `Replayed`; my fresh build in the audit worktree reads `Built`, with the same infos and no errors.
- **O3.** P1 has no dedicated pinned instance (the ticket's target 5 list does not ask for one). It is exercised through B1 and by the auditor's extra example. This is not a defect under the ticket.

## 7. Verdict per target
| target | verdict |
|---|---|
| P1 `ouGeneratorPair_hasDerivAt_integral` | PASS |
| P2 `ouGeneratorPair_integral_sub_eq` | PASS |
| T1 `ouMat_band_eq_ouPairMat` | PASS |
| T2 `ouP_band_map_pair` | PASS |
| B1 `ouGenerator_hasDerivAt_integral` (band-only consumer form, as pinned) | PASS |
| B2 `ouGenerator_integral_sub_eq` (band-only consumer form, as pinned) | PASS |
| S `testFunH_stieltjesImProduct` | PASS |
| vocabulary `TestFunH`, `ouPairP`, `ouPairMat`; instances `OUGeneratorInst.*` | PASS |

**Overall: PASS.** No dispatcher sign-off is needed. Merge note: `Axioms.lean` is untouched. The hub adds the root import `import RBM3D.Universality.OUGenerator` after the last `import` line.
