Auditor model: claude-opus-5-5

# T2224 audit (round 1) — S6-05 `Induction/ExpDuhamel` (proves `STExpDuhamelZ`, `STExpDuhamelQ`)

Written Mon Oct  5 23:24:04 UTC 2026. Branch `t/T2224` at a4d0978 (base cd6fcba); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2224-audit1` (detached, fresh build).

## 1. Diff scope and frozen files
```
$ git diff --stat main...t/T2224
 RBM3D/Induction/ExpDuhamel.lean | 798 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   2 -
 2 files changed, 798 insertions(+), 2 deletions(-)
$ git diff main...t/T2224 -- RBM3D/Test/Axioms.lean | grep "^[-+][^-+]" | cut -c1-70
-   `RBM.Gauss.Sizes.STExpDuhamelZ, -- `6:3-7`, `6:142-146` Duhamel fo
-   `RBM.Gauss.Sizes.STExpDuhamelQ, -- `6:109-116` Duhamel form with Q
$ git diff main...t/T2224 --stat -- RBM3D/Induction/Step6Pins.lean RBM3D/Induction/ExpHier.lean RBM3D/Induction/Step6Kit.lean | wc -l
       0
$ git merge-tree --write-tree --no-messages main t/T2224 >/dev/null; echo rc=$?     # main = f2766db
rc=0
```
Only the two sole writable files; the `Axioms.lean` diff is exactly the two owed lines named in the ticket. The merged pins are untouched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.ExpDuhamel   (log: grep summaries)
ℹ [3854/3854] Built RBM3D.Induction.ExpDuhamel (7.7s)
Build completed successfully (3854 jobs).
exit=0
$ grep -c "^error" build.log; grep -c "warning: RBM3D/Induction/ExpDuhamel" build.log
0
0
$ grep -c "info: RBM3D/Induction/ExpDuhamel.lean.*depends on axioms: \[propext, Classical.choice, Quot.sound\]" build.log
22
$ grep "depends on axioms" build.log | grep -vc "\[propext, Classical.choice, Quot.sound\]"
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|set_option (maxHeartbeats|debug)" RBM3D/Induction/ExpDuhamel.lean | wc -l
       0
```
22 = 17 public theorems + 5 instances, each printed with exactly the three standard axioms. (The module was compiled in this worktree: it was not in the copied cache.)

## 3. Statements against the pin (check file `docs/tickets/checks/T2224-check.lean`, by script)
Scratch `check_eq.lean` = check-file imports + `import RBM3D.Induction.ExpDuhamel` + sections 1–2 verbatim, then one
`example : RBM.Gauss.Sizes.T2224Check.X := @RBM.Gauss.Sizes.X` per `def X` of section 2 (generated from the file by regex),
`example (d : ℕ) : STExpDuhamelZ d := stExpDuhamelZ_holds d`, the same for `Q`, and for section 3 one
`example : <check-file statement, copied by script> := @RBM.Gauss.Step6Inst.<name>` per instance.
```
$ python3 gen.py   # 17 defs
17 defs; ['expDuh_hasDerivAt_uKer', 'expDuh_uKer_mul_thetaKer', 'expDuh_Ugen_ThetaN', 'expDuh_hasDerivAt_Ugen', 'expDuh_continuousOn_Ugen', 'expDuh_intervalIntegrable_Ugen', 'expDuh_duhamel', 'expDuh_STthetaOp_eq_ThetaN', 'expDuh_plain', 'expDuh_zeroModeSet_hasDerivAt', 'expDuh_zeroModeSet_continuousOn', 'stExpDuhamelZ_holds', 'expDuh_continuousOn_Qop', 'expDuh_Qop_hasDerivAt', 'expDuh_one_le_ellT', 'expDuh_intervalIntegrable_Qsrc', 'stExpDuhamelQ_holds']
$ grep -c "^example" check_eq.lean
24
$ lake env lean check_eq.lean > check_eq.out 2>&1; echo "exit $?"; grep -c error check_eq.out
exit 0
0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" check_eq.out; grep "depends on axioms" check_eq.out | grep -vc "\[propext, Classical.choice, Quot.sound\]"
22
0
```
24 = 17 section-2 equalities + 2 pin equalities + 5 section-3 instance equalities; all elaborate by `@name`, so every
public statement is definitionally the dispatcher's pin (hypotheses, binder/quantifier order, ranges `0 ≤ s ≤ t < 1`,
`|E| < 2` resp. `|E| ≤ 2`, `u ∈ Ioo 0 1`, all `d`). The pins themselves (`Step6Pins.lean:225, 246`) are merged and unchanged;
`stExpDuhamelZ_holds d`/`stExpDuhamelQ_holds d` prove them for every `d` (the pins' `3 ≤ d` premise is simply unused) —
the general statement, not a special case or conditional adapter.

## 4. Hidden hypotheses, vacuity, cycles
```
$ grep -E "^(theorem|lemma|def|noncomputable def|abbrev|instance|structure)" ExpDuhamel.lean | awk '{print $2}'
expDuh_hasDerivAt_uKer expDuh_uKer_mul_thetaKer expDuh_Ugen_ThetaN expDuh_hasDerivAt_Ugen expDuh_continuousOn_Ugen expDuh_intervalIntegrable_Ugen expDuh_duhamel expDuh_STthetaOp_eq_ThetaN expDuh_zeroModeSet_hasDerivAt expDuh_zeroModeSet_continuousOn expDuh_plain stExpDuhamelZ_holds expDuh_continuousOn_Qop expDuh_Qop_hasDerivAt expDuh_one_le_ellT expDuh_intervalIntegrable_Qsrc stExpDuhamelQ_holds inst_duhamelZ_holds inst_duhamelQ_holds inst_duhEq_holds inst_expDuh_plain inst_expDuh_single
$ grep -cE "^private (theorem|lemma|def)" ExpDuhamel.lean; grep -E "^private (theorem|lemma|def)" ExpDuhamel.lean | awk '{print $3}' | grep -vc "^expDuh_"
17
0
```
- The file defines no `def`/`structure`/`Prop`: no hypothesis can hide in a new structure field. All 22 public names are pinned; 17 helpers are `private` and `expDuh_`-prefixed (§3 (E)).
- The two pin theorems are closed (`(d : ℕ) : STExpDuhamelZ d`), with clean axioms (§2): no hypothesis, no unproved pin carried, no cycle. Inputs are merged results (`expHier_*` of T2218, `zeroModeSet_Ugen`, `zeroModeSet_ThetaN`, `QopAlgebra_Qop_hasDerivAt`, `stMollifierEx_holds`, …), elaborated in the clean build.
- No external hypothesis is introduced; `STMollifierProps` is the merged pin's own hypothesis, used only through its stated conjuncts (prove report (b) narrative 7: no sign of `C, c` needed, consistent with the theorem holding for all real `C, c` as stated).

## 5. Compiled nonempty instances (same file, `RBM.Gauss.Step6Inst`; data `d = 3`, `sz0` (`n = 0`), `E = 1/2`)
| endpoint | instance | data | discharged |
|---|---|---|---|
| `stExpDuhamelZ_holds` | `inst_duhamelZ_holds` = `inst_duhamelZ (stExpDuhamelZ_holds 3)` | `[1/4,1/2]`, `A = univ`, `σ = (+,-)`, `a = ![0, e₁]` | all (merged `inst_duhamelZ`) |
| `stExpDuhamelZ_holds` | `inst_expDuh_single` | `[0,1/2]`, `A = {1}`, `σ = (-,+)` | `3 ≤ 3`, `|1/2| < 2`, `0 ≤ 0 ≤ 1/2 < 1` by `norm_num` |
| `stExpDuhamelZ_holds` (sequence form) | `inst_duhEq_holds` = `inst_duhEq (stExpDuhamelZ_holds 3)` | flow `z0`, `[0,1/16]` | all |
| `stExpDuhamelQ_holds` | `inst_duhamelQ_holds` = `inst_duhamelQ (stExpDuhamelQ_holds 3)` | `∃ C c ϑ, STMollifierProps … ∧ …`, `ϑ` from `stMollifierEx_holds` | all |
| `expDuh_plain` | `inst_expDuh_plain` | `s = 0`, `t = 1/2`, `σ = (+,+)` | all by `norm_num` |
| 1a–1f, 2a, 2b, 3b, 3c, 4a–4d | 14 `example`s (file lines 685–772) | same data; `Y = STExpErr`, `D = STExpDrift`, `ϑ` of `stMollifierEx_holds` | all |

Nondegenerate: `L = 4 ≥ 3`, `d = 3`, `s < t` (or `s = 0` endpoint case), nonempty `A`, nonempty label space `Fin 2 → Zd 3 4`; the `Q` instance is a genuine `STMollifierProps` witness (not a `False` premise). No hypothesis is left open (none needed: `STExpHier` is proved). All compile (§2, §3).

## 6. Paper deltas
- No new Lean/paper statement difference is introduced: the pins are the merged texts (unchanged), and the sign of the last term of `STExpQsrc` (`- (𝒫 f_u) ∂_uϑ`) matches `(int_K-L+QE)` as printed:
```
$ sed -n 115p paper/tex/6_Step6_two_loop.tex | cut -c1-120
& - \int_{s}^t \left(\mathcal{U}^{(2)}_{u, t, \bsig} \circ \left\{\left[ {\cal P} \circ \E\left(\mathcal{L} - \mathcal{K}\right)^{(2)}_{u, \bsig}\right] \partial_u\dthn_{u}^{(2)} \right\}\right)_{\ba} \dd u.
```
- Prove report (d): no candidate; agreed.

## 7. Observations (no RETURN)
1. The pin docstring `Step6Pins.lean:234-235` and the ticket cite "paper-delta T2166a" for the sign; in `docs/paper-deltas.md` the only `T2166a` hit is `:1354` (D395, about `hker` coefficients), and the sign matches the paper as printed, so no delta is needed. Doc citation only (merged file, not this ticket's).
```
$ grep -n "T2166a" docs/paper-deltas.md | cut -c1-60
1354:- **D395（T2166a）**：非交错 `σ` 的 `hker` 系数是 EK-6 的 `W^{Cε} r^{k−1}`
```
2. `main` moved to f2766db (T2223) after the branch base; `git merge-tree` is clean (§1). The full `lake build` with `#assert_rbm_axioms` and the registry pre-check are the hub's merge step; the prove report pastes a passing run of both (owed 144 → 142, no unregistered premise).

## Verdict
| target | verdict |
|---|---|
| 1a–1f kernel / `𝒰` calculus | PASS |
| 2a `expDuh_duhamel`, 2b bridge | PASS |
| 3a–3c, 3d `stExpDuhamelZ_holds` | PASS |
| 4a–4d, 4e `stExpDuhamelQ_holds` | PASS |
| 5 instances (5) | PASS |
| registry edit (`Test/Axioms.lean`) | PASS |

**T2224: PASS.** No dispatcher sign-off needed.
