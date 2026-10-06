Auditor model: claude-opus-5-5
# T2278 audit (round 1) — UN-30 `Universality/GUEPhase/EntryDet`
Date (`date -u`): Tue Oct  6 10:12:41 UTC 2026. Branch `t/T2278` = 8e5f0b9, main = 95d8b2a.
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2278-audit1` (detached at 8e5f0b9).

## 1. Diff scope
```
$ git diff --name-status main...HEAD
A	RBM3D/Universality/GUEPhase/EntryDet.lean
$ grep -nE "sorry|admit|^axiom| axiom |native_decide|opaque|implemented_by|unsafe" EntryDet.lean
(no output)
$ grep -rn "EntryDet\|stable_mix\|mix_det" RBM3D/Test/Axioms.lean | wc -l
       0
```
Only the sole writable file is touched (new file; `Axioms.lean` untouched, no new `Prop`-valued def:
`Snorm`, `mixC`, `mixK`, `mixDelta`, `mixCdet` are `ℝ`-valued). No merged file or frozen signature touched.

## 2. Build
```
$ lake build RBM3D.Universality.GUEPhase.EntryDet ; echo exit $?
✔ [3359/3359] Built RBM3D.Universality.GUEPhase.EntryDet (13s)
Build completed successfully (3359 jobs).
exit 0
```
(`grep -c error build.log` = 0; the log's warnings are in upstream files, none in `EntryDet.lean`.)
## 3. Statements against the check file's pins (independent scratch file)
Scratch `AuditPins.lean`: `import RBM3D` + `import RBM3D.Universality.GUEPhase.EntryDet`, then §2 of
`docs/tickets/checks/T2278-check.lean` copied verbatim by `awk '/^noncomputable section/…/^end RBM.Univ.T2278Check/'`,
then (written by the auditor):
```
example : T2278_stable_mix := fun d L W _ _ => @stable_mix d L W _ _
example : T2278_svarF_le := fun d L W _ _ => @svarF_le d L W _ _
example : T2278_Snorm_le := fun d L W _ _ => @Snorm_le d L W _ _
example : T2278_Snorm_zero_left := fun d L W _ _ => @Snorm_zero_left d L W _ _
example : T2278_mix_offdiag_det := fun d L W _ _ => @mix_offdiag_det d L W _ _
example : T2278_mix_diag_det := fun d L W _ _ => @mix_diag_det d L W _ _
example : T2278_ward_col := @ward_col.{0}
example : T2278_ward_row := @ward_row.{0}
example : T2278_im_diag_le := @im_diag_le.{0}
example : T2278_inv_N_le_maxLoopPM := fun d L W _ _ => @inv_N_le_maxLoopPM d L W _ _
example : T2278_sum_Snorm_le := fun d L W _ _ => @sum_Snorm_le d L W _ _
example : T2278_mixC_pos := @mixC_pos
example : T2278_mixK_one_le := @mixK_one_le
example : T2278_mixDelta_pos := @mixDelta_pos
example : T2278_mixCdet_nonneg := @mixCdet_nonneg
example : T2278_mix_det := fun d L W _ _ => @mix_det d L W _ _
example (d L W : ℕ) [NeZero L] [NeZero W] (g a b : ℝ) : SnormV d L W g a b = Snorm d L W g a b := rfl
example (κ : ℝ) : mixCV κ = mixC κ := rfl
example (d : ℕ) (Λ κ : ℝ) : mixKV d Λ κ = mixK d Λ κ := rfl
example (d : ℕ) (Λ κ : ℝ) : mixDeltaV d Λ κ = mixDelta d Λ κ := rfl
example (d : ℕ) (Λ κ : ℝ) : mixCdetV d Λ κ = mixCdet d Λ κ := rfl
```
```
$ lake env lean AuditPins.lean ; echo exit=$?      (205 lines, 23 `example`s incl. the check file's 2)
exit=0
```
All 16 pins are the library theorems with exactly the pinned types (the `@name d L W _ _` terms leave no
argument for Lean to fill except the instances); the 5 vocabulary `rfl`s hold. In particular `stable_mix`,
`mix_diag_det`, `mix_det` carry `3 ≤ d`, `3 ≤ L`, `0 < g ≤ Λ`, `0 < κ`, `|E| ≤ 2-κ`, `0 ≤ a,b`, `0 < a+b < 1`;
the constant `Kstab3 d Λ κ (1 + 1/gapK κ)` depends only on `(d, Λ, κ)`:
```
$ grep -n "def Kstab3" -A3 RBM3D/Green/Stability.lean
212:noncomputable def Kstab3 (d : ℕ) (Λ κ : ℝ) : ℝ :=
213-  1 + pin5sC d Λ (Real.sqrt (κ * (4 - κ)) / 2) *
214-    (1 + Λ ^ 2 * expC (d - 2) (pin5sc d Λ (Real.sqrt (κ * (4 - κ)) / 2)))
```
Unpinned ported statements vs RBM2D `c9a24cf` (auditor script, headers whitespace-normalised):
```
Snorm_nonneg      2D {a b} (ha)(hb)(x y : Idx L W) : 0 ≤ Snorm L W a b x y
                  3D {g a b} (ha)(hb)(x y : Idx d L W) : 0 ≤ Snorm d L W g a b x y
sum_Snorm_row     2D (hL){a b}(hu)(x : Idx L W) : ∑ y, Snorm L W a b x y = 1
                  3D (hL){g a b}(hu)(x : Idx d L W) : ∑ y, Snorm d L W g a b x y = 1
sum_Snorm_col     same shape as row (3D adds g, d)
Snorm_symm        2D (a b)(x y) … = … y x      3D (g a b)(x y) … = … y x
Snorm_zero_right  2D {a}(ha : 0 < a)(x y) : Snorm L W a 0 x y = svar L W x y
                  3D {g a}(ha : 0 < a)(x y) : Snorm d L W g a 0 x y = svarF d L W g x y
green_transpose, ldeRowRHS_smul, ldeColRHS_smul, ldeQuadRHS_smul, ldeQuadLHS_smul : identical text
```
Every difference is the ticket's import map (`Smix L W ↦ Smix d L W g`, `svar ↦ svarF d … g`, `Idx L W ↦ Idx d L W`).
## 4. Hidden hypotheses, vacuity, cycles
- No structure or class is declared in the file (`grep -nE "^(structure|class|instance)"`: no hits). Hypotheses
  `GoodEvent`, `LDERow`, `LDECol`, `LDEQuad`, `Stable` are merged `Green/EntryCore` predicates appearing explicitly
  in the signatures (other gates' pins / outputs), not hidden fields.
- Imports: `AuxCarrier`, `Green/EntryDom`, `Green/LDE`, `Loop/KLSumZero` (all on main); `stable_mix` calls the
  merged `stable_svar_bulk` (hyps `3 ≤ d`, `3 ≤ L`, `0 < g ≤ Λ`); no cycle (new leaf module, nothing imports it).
- No external hypothesis introduced (deterministic file); no limit check needed.

## 5. Compiled nonempty instances (in `EntryDet.lean`, namespace `RBM.Univ.EntryDetCheck`; build of §2)
Data: `d = 3, L = 3, W = 2` (`|Vtx 3 3 2| = 216`), `g = Λ = κ = 1`, `E = 0`.
```
$ grep -nE "private def check_(dI|t) " EntryDet.lean
1265:private def check_dI : ℝ := min (1 / 1000) (mixDelta 3 1 1)
1275:private def check_t : ℝ := check_dI / 8
```
| endpoint | instance (line) | data / deterministic hyps |
|---|---|---|
| `stable_mix` | `stable_mix_inst` L969 | `(a,b)=(1/2,1/4)`, all hyps by `norm_num` |
| `mix_offdiag_det` | `mix_offdiag_det_inst` L1301 | `M=0`, `a=b=check_t>0`, `δ=check_dI`, `Φ=1`, `Λ=4`; GoodEvent, LDE, `hΛ1`, `hΛ2` discharged |
| `mix_diag_det` | `mix_diag_det_inst` L1341 | as above, `Λ'=4`, quadratic LDE by Cauchy–Schwarz (`216 u² ≤ 1`), `hKδ` from `check_dI ≤ mixDelta` |
| **`mix_det`** | `mix_det_inst` L1392 | `M=0`, `u=check_dI/4∈(0,1/4000]`, `δ=check_dI`, `Φ=216`; **no hypothesis left open** |
| `mix_det` (vars) | `mix_det_inst_vars` L1430 | `(a,b)=(1/2,1/4)`, `δ=mixDelta 3 1 1/3`; GoodEvent and 4 LDE inputs as hypotheses (other gates' pins) |
| `inv_N_le_maxLoopPM` | L980 | `u=3/4`, `M=0`, `m=4i` |
| `sum_Snorm_le` | L1010 | `s=0`, `M=0`, `(a,b)=(1/2,1/4)` |
| `ward_col/ward_row/green_transpose` | L992/L997/L1003 | `H=0`, `z=i` on `Idx 3 3 2` |
| remaining 17 public theorems | L1027-L1098 | one instance each at the same data |

Nondegeneracy: index set of size 216, `0 < u < 1`, `0 < δ` (`mixDelta_pos`), `Φ = 216` (not astronomical),
no `False` premise, no collapsed window. `check_dI` is symbolic through `Kstab3` but its positivity and
`check_dI ≤ 1/1000` are proved, so every scalar hypothesis is discharged.

## 6. Axioms
`#print axioms` (appended to `AuditPins.lean`) of the 26 public theorems and 4 headline instances:
```
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" pins.out
30
$ grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" pins.out
(no output)
$ printf 'import RBM3D\nimport RBM3D.Universality.GUEPhase.EntryDet\n\n#assert_rbm_axioms\n' > precheck.lean ; lake env lean precheck.lean
axiom audit: 8103 theorems, 2641 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit=0
```

## 7. Paper-delta coverage
Lean vs paper/RBM2D statement differences and their coverage in the prove report §(d):
- constant `Kstab3 d Λ κ (1+1/gapK κ)`, L-free (RBM2D `Kstab2 κ L ∝ 1+log L`) → `T2278a` (bookkeeping);
- `svarF_le` constant `1` (RBM2D `1/5`), `hΛ2` via `W^{-d} ≤ 4 maxLoopPM` → `T2278b`;
- band-only form (`0 < g ≤ Λ`, `m = mE E`; BA form in BA-C3), extra `hd hg hgΛ` → `T2278c`;
- `im_diag_le` keeps an unused `[Fintype ν]` to match the pin → `T2278d`.
All differences are covered.
## 8. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. `mix_diag_det_inst` repeats `have hδ12`, `have hδ0`, `have hK` twice (L1359-1364); harmless shadowing.
- O2. Prove report, last narrative bullet: "`Kstab3` is `Classical.choose`-valued". `Kstab3` is defined through
  `pin5sC`/`pin5sc`/`expC` (Stability.lean:212), with no explicit numeric value; the conclusion it draws (the
  instance uses the symbolic `check_dI`) is unaffected.
## 9. Verdict
| target | verdict |
|---|---|
| `stable_mix` | PASS |
| `Snorm` + `Snorm_nonneg`, `sum_Snorm_row/col`, `Snorm_symm`, `Snorm_zero_right`, `svarF_le`, `Snorm_le`, `Snorm_zero_left` | PASS |
| `mix_offdiag_det`, `mix_diag_det` | PASS |
| `ward_col`, `green_transpose`, `ward_row`, `im_diag_le` | PASS |
| `inv_N_le_maxLoopPM` | PASS |
| `sum_Snorm_le` | PASS |
| `mixC/mixK/mixDelta/mixCdet`, `mixC_pos`, `mixK_one_le`, `mixDelta_pos`, `mixCdet_nonneg`, `lde*_smul` | PASS |
| `mix_det` | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
