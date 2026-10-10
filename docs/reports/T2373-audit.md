Auditor model: claude-opus-5-5
# T2373 audit (round 1): UN-10b `EigenInterlacing`, `GUELocalSchur` (`gueSchurTail`, `gueLocal`)
Time: Sat Oct 10 07:55:24 UTC 2026 (`date -u`). Worktree `RBM3D-wt/T2373-audit1`, detached at `t/T2373` = `4aa6933`; merge-base = `main` = `c0a7747`.
Scratch: `scratchpad/T2373/` (`ax.lean`, `pre0.lean`, `pre2.lean`, `build.txt`, `buildall.txt`).

## 1. Diff scope
```
$ git diff --name-only main...t/T2373
RBM3D/Test/Axioms.lean
RBM3D/Universality/EigenInterlacing.lean
RBM3D/Universality/GUELocalSchur.lean
$ git diff main...t/T2373 -- RBM3D/Test/Axioms.lean | grep '^[-+]  '
-   `RBM.Univ.UNGUELocal, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
-   `RBM.Univ.UNGUESchurTail, -- bulk universality pin, the Schur tail of the GUE local law (T2244, UN-09: owed; ...)
$ git log --oneline t/T2373..main   # (empty: main has not moved)
```
Only the three sole writable files; in `Test/Axioms.lean` only the two target-4 lines. Pins (`GUELocalBootstrap.lean:915`, `Pins.lean:489`) and `un_gueLocal_of_tail` are untouched (not in the diff).

## 2. Statements
Targets 2 are typed by the merged pins themselves; elaborated in `ax.lean`:
```
example : RBM.Univ.UNGUESchurTail := RBM.Univ.gueSchurTail
example : RBM.Univ.UNGUELocal := RBM.Univ.gueLocal
$ grep -n '^theorem gue' RBM3D/Universality/GUELocalSchur.lean
540:theorem gueSchurTail : UNGUESchurTail := by
591:theorem gueLocal : UNGUELocal := un_gueLocal_of_tail gueSchurTail
```
`UNGUESchurTail` (read at `GUELocalBootstrap.lean:915`): `∀ d, 3 ≤ d → ∀ sz, Tendsto size → ∀ κ τ ε D > 0, ∀ q Γ, window(Γ n) → (∀ᶠ n, |Γ n| ≤ N^q) → ∀ᶠ n, gueP{∃ z ∈ Γ n, ∃ i, Im m_N ≤ 2 ∧ schurBud N ε z < ‖schurErr‖} ≤ N^{-D}`. The pin is the general statement exactly as the ticket asks (no special case, no extra hypothesis); `UNGUELocal` likewise.

Target 1, the two public interlacing lemmas against RBM2D (`9e0f275`), extracted by script:
```
$ diff <(ext RBM2D/.../EigenInterlacing.lean) <(ext RBM3D/.../EigenInterlacing.lean)  (ext = awk from `^theorem` to `:= by`; RBM.green→green)
statements identical to RBM2D (modulo RBM.green qualifier)
```
Both are generic in finite index types `m ↪ n`, Hermitian `A`, `0 < Im z` (trace bound `(card n - card m)(π+1)/Im z`). These are the general Cauchy-interlacing statements, not a special case.

Public declarations added (all others `private` with stems `EigenInterlacing_` / `GUELocalSchur_`):
```
$ grep -nE '^(theorem|lemma|def|abbrev|instance|structure|class)' <both files>
GUELocalSchur.lean:540 gueSchurTail   :591 gueLocal
GUELocalSchur.lean:609-771 H3, H3_isHermitian, green_diagonal, H3_ne_I, H3_minor, H3_minor_green, H3_Q, H3_trace,
    H3_hmim, H3_hdiag, H3_hquad, one_le_Nsz, schurBud_sz0_zero, final_arith_h2   (namespace RBM.Univ.GUELocalSchurInst, :604-821)
EigenInterlacing.lean:249 eigenvalues₀_submatrix_interlace   :507 trace_green_submatrix_sub_le
EigenInterlacing.lean:642-656 A3, A3_isHermitian, A3_minor, A3_eigenpairs   (namespace RBM.Univ.EigenInterlacingInst, :639-700)
```
Instance helpers sit in stem-named namespaces (§3 (E) satisfied).

## 3. Hidden hypotheses, vacuity, cycles
- No new `structure`/`class`/`instance`; no hypothesis carried in a structure field.
- `gueSchurTail` has no hypothesis beyond the pin's binders; `gueLocal := un_gueLocal_of_tail gueSchurTail` (merged deterministic bootstrap, `GUELocalBootstrap.lean:952`). No cycle: `GUELocalSchur` imports `GUELocalBootstrap`, `Pins`, `Step1RegularityGUE`, `GUEPhase.AuxCarrier`, `EigenInterlacing`, `Green.{EntryCore,LDE,IBPPoly}`, `Analysis.Resolvent`, `Defs.Sizes`, all merged on `main`; `EigenInterlacing` imports Mathlib + `Green.EntryCore`.
- No external hypothesis remains (both pins proved outright), so no limit check is owed.
```
$ grep -nE "sorry|admit|native_decide|^axiom|axiom |unsafe|implemented_by|opaque|extern|macro|elab |set_option" <both files>
EigenInterlacing.lean:32-34 set_option linter.{unusedSectionVars,style.longLine,unusedFintypeInType} false
EigenInterlacing.lean:653  set_option linter.flexible false in
GUELocalSchur.lean:64-65   set_option linter.{unusedSectionVars,style.longLine} false
```
Linter options only.

## 4. Compiled nonempty instances (same files, built in §5)
- `trace_green_submatrix_sub_le` / `eigenvalues₀_submatrix_interlace`: `A3 = !![2,1,0;1,2,1;0,1,2]` (3×3 Hermitian, proved by `A3_isHermitian`), minor via `Fin.succEmb 2` (= `!![2,1;1,2]`, `A3_minor`); `A3_eigenpairs` proves eigenpairs with distinct eigenvalues `2±√2, 2` and the minor's `3, 1`. The interlacing example applies the theorem at `i = 0, 1` (all hypotheses `by simp`); the trace example at `z = 3/10 + i` gives `≤ π + 1`. Nondegenerate (card 3 vs 2, distinct spectrum). The interlacing conclusion is left symbolic in `eigenvalues₀` (hypotheses concrete): accepted.
- `gueSchurTail` (`:793-806`): `d = 3`, `sz0` (`Step1RegularityGUEInst.inst_sz0_size_tendsto`), `κ = 1, τ = 1/10, ε = 1/40, D = 1, q = 9`, `Γ n = {i}`; window (`|Re i| = 0 ≤ 1`, `N^{-9/10} ≤ 1 ≤ 10` via `one_le_Nsz`) and card (`1 ≤ N^9`) discharged. Nonempty Γ, `N_n ≥ 2^21`.
- `gueLocal` (`:808-819`): `d = 3`, `sz0`, `κ = 1, τ = 1/10, D = 2`; all hypotheses discharged, none left.
- Deterministic lemmas at `H3 = diag(1,0,-1)`, `i = 0`, `z = i`, `a = 5`: `schurErr_le_of_good` with all five hypotheses discharged (`H3_hmim`, `H3_hdiag`, `H3_hquad`, ...), `schurErr_eq`, `trace_diff_le`, `ward_sum`; `schurBud_sz0_zero` (`0 < schurBud(N_0=2097152, 1/40, i) ≤ 1/100`); `gaussianReal_tail` (`v=t=1`), `gueP_diag_tail` (`d=3, L=4, W=32`), `schur_union_bound` (`Γ={i}, a=5`), `final_arith` (`N=10^10, q=0, D=ε=1, q'=2`). All concrete, nondegenerate.

## 5. Build, axioms, check file, registry pre-check
```
$ lake build RBM3D.Universality.EigenInterlacing RBM3D.Universality.GUELocalSchur; echo exit=$?
exit=0
Build completed successfully (3375 jobs).
$ grep -cE "^(error|warning): RBM3D/Universality/(EigenInterlacing|GUELocalSchur)" build.txt
0
$ lake env lean ax.lean; echo exit=$?
'RBM.Univ.gueSchurTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.gueLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.eigenvalues₀_submatrix_interlace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.trace_green_submatrix_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean docs/tickets/checks/T2373-check.lean; echo check_exit=$? errors=$(grep -c error)
check_exit=0 errors=0
```
Registry pre-check (no `RBM3D.olean` on the branch, so the root's import list is inlined: `pre2.lean` = every `import` line of the branch's `RBM3D.lean` + the two new modules + `#assert_rbm_axioms`; `pre0.lean` = the same without the new modules):
```
$ grep '^import' RBM3D.lean | awk '{print $2}' | xargs lake build; echo build_exit=$?
build_exit=0
Build completed successfully (4181 jobs).
$ lake env lean pre2.lean; echo exit=$?
exit=0
axiom audit: 10855 theorems, 3188 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c "UNGUELocal\|UNGUESchurTail" pre2.out
0
$ lake env lean pre0.lean; echo exit=$?      # control: branch root without the new imports
exit=1
pre0.lean:413:0: error: axiom audit: ...
  [RBM.Univ.UNGUESchurTail]
```
So the registry is consistent once the hub adds the two root imports at merge (§3 (A) step 4); without them the full build fails on `UNGUESchurTail`, as expected for a deleted owed line. Deleting `UNGUELocal` is also clean (pre-check exit 0); the ticket's default rule (delete) applies.

## 6. Paper deltas
`UNGUESchurTail` and `UNGUELocal` are project-internal pins (not paper statements; covered by existing delta T2162b, per the pin docstring at `Pins.lean:483-487`). The Lean statements are unchanged by this ticket; the interlacing lemmas are standard generic facts. The prove report proposes `T2373a` (no new statement difference; mark T2162b as proved by T2373). Coverage is complete.

## 7. Observations (no effect on verdict)
- O1. `Test/Axioms.lean` `UNBUniv` comment (T2371's line, `:183`) still calls `UNGUESchurTail` owed (producer T2373); stale after merge, outside this ticket's lines (prove report (d) records it).
- O2. `gueSchurTail` does not use `3 ≤ d`, `0 < κ`, `0 < τ`, `0 < D` (prove report narrative); the pin is a fixed statement, so no change.
- O3. The full `lake build` on the branch as committed fails on `UNGUESchurTail` until the hub adds the root imports; this is the merge procedure, not a defect.
- O4. The audit-worktree build cache was stale relative to `main` (4181-job rebuild for the pre-check); no effect on results.

## Verdicts
| target | verdict |
|---|---|
| 1 `EigenInterlacing.lean` (`eigenvalues₀_submatrix_interlace`, `trace_green_submatrix_sub_le`) | PASS |
| 2 `GUELocalSchur.lean` (`gueSchurTail : UNGUESchurTail`, `gueLocal : UNGUELocal`) | PASS |
| 3 instances | PASS |
| 4 registry (`UNGUESchurTail`, `UNGUELocal` deleted; pre-check exit 0) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
