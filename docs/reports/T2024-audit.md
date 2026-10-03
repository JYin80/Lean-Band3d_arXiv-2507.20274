Auditor model: claude-opus-5-5

# T2024 audit (round 1) — PT-F2 unit pins `PropUnit1`, `PropUnit2`

Written Sat Oct  3 04:55:05 UTC 2026 (`date -u`). Branch `t/T2024` = `d926433`; merge-base with main `58bedae`; main `3dc4f1c`.
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2024-audit1` (detached at `d926433`).

## 0. Diff scope

```
$ git diff --stat main...t/T2024
 RBM3D/Propagator/PropUnit.lean | 1008 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1008 insertions(+)
$ git log --oneline main..t/T2024
d926433 T2024: PropUnit1/PropUnit2 hold (route H unit first and second differences of Theta)
```
Only the sole writable file is touched (new file); no frozen signature changed. Imports (lines 6–9): `RBM3D.Propagator.{HeatProduct,LaplaceGauss,Pins,Prop5Short}` only, not `RBM3D`.

## 1. Statement vs pin (script diff)

```
$ awk '/^\/-- \*\*Unit pin 1/{f=1} f{print} /\^ d\)⁻¹$/{exit}' docs/tickets/checks/T2024-check.lean > pin.txt
$ sed -n '37,64p' RBM3D/Propagator/PropUnit.lean > lean.txt
$ wc -l pin.txt lean.txt ; diff pin.txt lean.txt
      27 pin.txt
      28 lean.txt
27a28
>
```
The only difference is one trailing blank line: both `def`s (with docstrings) are verbatim the check file's text, namespace `RBM.T2024Check` -> `RBM`.

Target theorem headers:
```
$ sed -n '747p;826p' RBM3D/Propagator/PropUnit.lean
theorem propUnit1_holds (d : ℕ) (Λ κ : ℝ) : PropUnit1 d Λ κ := by
theorem propUnit2_holds (d : ℕ) (Λ κ : ℝ) : PropUnit2 d Λ κ := by
```
These are exactly the ticket's types. Quantifier order (`3 ≤ d → 0 < Λ → 0 < κ → ∃ C, 0 < C ∧ ∀ L g t m σ₁ σ₂ a j`), constants depending only on `(d, Λ, κ)`, the loss-free shapes `(g²+|1−t|)⁻¹ (|a|+1)^{-(d−1)}` and `(|a|+1)^{-d}`, the range `0 ≤ t < 1`, and both sign pairs `σ₁, σ₂ : Bool` all match the pin. Both are general statements, with no special case and no adapter.

## 2. Vacuity, hidden hypotheses, cycles

- `PropUnit1`/`PropUnit2` are `Prop` `def`s with no structure; the theorems take only `(d Λ κ)` and prove the pins unconditionally, so no unproved `Prop` is a hypothesis (DECISIONS §16).
- Premises can all hold together (`d=3, Λ=1, κ=1/2, L=5, g=1/2, t=9/10, m=I`): see §3.
- The upstream results used are all merged theorems on main with no hypothesis beyond numeric ones:
```
$ grep -n "prop5Short_holds\|kProd_diff1_le\|kProd_diff2_le\|kProd_gap\|lg_bulk\|lg_zero\|lg_tail\|lg_convA\|Theta_eq_laplace_prod" PropUnit.lean   (uses)
136,552: lg_bulk   149,565: lg_zero   362: lg_tail   549: lg_convA   461: Theta_eq_laplace_prod
749/828: kProd_diff1_le / kProd_diff2_le   750/829: kProd_gap   751/830: prop5Short_holds
$ grep -n -A2 "^theorem prop5Short_holds\|^theorem kProd_gap\|^theorem kProd_diff1_le\|^theorem Theta_eq_laplace_prod" RBM3D/Propagator/*.lean
Prop5Short.lean:400:theorem prop5Short_holds (d : ℕ) (Λ κ : ℝ) : Prop5Short d Λ κ := by
HeatProduct.lean:462:theorem kProd_diff1_le : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ...
HeatProduct.lean:626:theorem kProd_gap : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ...
HeatProduct.lean:1171:theorem Theta_eq_laplace_prod :
    ∀ (d L : ℕ) (hL : 3 ≤ L) (g t : ℝ), 0 < g → 0 ≤ t → t < 1 → ∀ a : Zd d L, ...
```
None of them depends on T2024, so there is no cycle. No external hypothesis is introduced, so no limit check is needed.

## 3. Compiled nonempty instances (in the same file, lines 920–1006; they compile in the build of §4)

Ticket-required instances (lines 928–958): `propUnit1_holds 3 1 (1/2)` and `propUnit2_holds 3 1 (1/2)` applied with
```
  obtain ⟨C, hC, H⟩ := propUnit1_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false 0 0⟩
```
(and `... true false 0 0 0` for `propUnit2_holds`). That is `L = 5`, `g = 1/2`, `t = 9/10`, `m = I`, `σ₁ = true`, `σ₂ = false`, `a = 0`, `i = j = 0`, exactly the ticket's data. Every deterministic hypothesis is discharged (`3 ≤ 5`, `0 < 1/2 ≤ 1`, `0 ≤ 9/10 < 1`, `‖I‖ = 1`, `1/2 ≤ Im I`). Nothing is degenerate: there is no `N = 0`, no empty index and no `False` premise, and `C` is existential, not astronomically large.
Extra instances: the bulk branch `σ₁ = σ₂ = true` at `a = ![1,0,0]`, `j = 2` (line 961); `t = 0` at `a = ![-1,0,0]` (line 975); and the mixed second difference `(i,j) = (0,2)`, bulk, at `a = ![1,0,0]` (line 989).

## 4. Build, axioms, hygiene

```
$ lake build RBM3D.Propagator.PropUnit 2>&1 | grep -E "error|warning|Build completed"; echo exit $?
warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Propagator/HeatProduct.lean:218:0: `abs_prod_sub_prod_le` does not use the following hypothesis in its type:
warning: RBM3D/Propagator/PropUnit.lean:37:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Propagator/PropUnit.lean:59:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3408 jobs).
exit 0
$ cat Ax.lean   # import RBM3D.Propagator.PropUnit; #print axioms RBM.propUnit1_holds; #print axioms RBM.propUnit2_holds
$ lake env lean Ax.lean
'RBM.propUnit1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.propUnit2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b|native_decide" RBM3D/Propagator/PropUnit.lean; echo exit $?
exit 1
$ grep -rn -E "def PropUnit1|def PropUnit2|propUnit1_holds|propUnit2_holds" RBM3D | grep -v "Propagator/PropUnit.lean"; echo exit $?
exit 1
```
The two PropUnit warnings are style lints on the pinned docstring lines (37, 59), which are copied verbatim from the check file; the pin may not be changed. There are no errors. Unpinned helpers are all `private` (`pu_*`; listing via `grep -n "^private" ...`, lines 68–739), as §3(E) requires. The full `lake build` (`#assert_rbm_axioms`) is run by the hub at merge.

## 5. Paper deltas

```
$ grep -n "T2024a\|paper-delta" docs/reports/T2024-prove.md
251:## (d) Open issues and paper-delta candidates
252:- Paper-delta candidates: none (`T2024a`, … not needed): the unit pins are internal to route H; no statement was changed or weakened.
```
I agree. `PropUnit1`/`PropUnit2` are route-H intermediate pins with no paper counterpart (the ticket says "none expected"), and the Lean matches the pin verbatim, so there is no Lean/paper statement difference to cover.

## Observations (no effect on the verdict)

- O1. Pin lines 37 and 59 exceed 100 characters (lint warning). They are inherited from the check file and cannot be changed under the ticket.
- O2. Main has moved since the merge-base (`58bedae` -> `3dc4f1c`, with T2020 and T2022 merged). The diff is still confined to the new file, and the hub's full build at merge covers integration.

## Verdict

| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Paper deltas | Verdict |
|---|---|---|---|---|---|---|
| `propUnit1_holds` | = pin | none | ticket data, compiled | ok / 3 std | none needed | **PASS** |
| `propUnit2_holds` | = pin | none | ticket data, compiled | ok / 3 std | none needed | **PASS** |

Ticket T2024: **PASS**. No dispatcher sign-off needed.
