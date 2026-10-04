Auditor model: claude-opus-5-5

# T2093 audit (round 1) — ST2-06 `Induction/Step2K2.lean`, target `stK2decay_holds`

Written: Sun Oct  4 00:50:47 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2093-audit1`,
detached at `de6076c` (t/T2093); merge-base with main = `c7acfed` (= main HEAD).

## Verdict

| Target | Verdict |
|---|---|
| `RBM.Gauss.Sizes.stK2decay_holds (d : ℕ) : STK2decay d` | **PASS** |

No dispatcher sign-off needed.

## 1. Statement

```
$ grep -n "^theorem" RBM3D/Induction/Step2K2.lean
132:theorem stK2decay_holds (d : ℕ) : STK2decay d := by
$ lake env lean scratch/ax.lean      # #check @stK2decay_holds ; example (d) : STK2decay d := stK2decay_holds d
stK2decay_holds : ∀ (d : ℕ), STK2decay d
exit=0
```
The type is the merged pin itself (`Step2Defs.lean:568`, unchanged on the branch), so the statement equals the
ticket's pin by construction: `3 ≤ d → ∀ κ 𝔡, 0<κ → 0<𝔡 → ∃ C>0, ∀ sz n E u D, 0<lam ≤ 𝔡⁻¹ → |E| ≤ 2-κ →
0 ≤ u < 1 → 0 ≤ D → ∀ σ a, ‖STKloop sz n E u σ a‖ ≤ C * STprof sz n u D L (a 0) (a 1)`. Constants before the
sizes; no `λ`-lower bound, no `L^d ≤ W^K`, all `n`, all four `σ`. The pinned name is unchanged.

Paper (`3_5_Loop_Hierarchy.tex`):
```
456: \be\label{eq:kn2sol_decay}  {\cal K}^{(2)}_{u,(-,+),(a_1,a_2)} \prec W^{-d} B_{u,|a_1-a_2|}
518: \be\label{eq:simpleboundK}\cK^{(2)}_{u,\bsig,\ba}\prec W^{-d}\wT^{L}_{u,D}\p{|a-b|}\ee
```
The Lean pin is the `(eq:simpleboundK)` form with a deterministic `≤ C` (stronger than `≺`), all `D ≥ 0`
(paper: "any large D"; stronger), `L^∞` distance (D18 / T2002b). `STprof` = `W^{-d} · tailW(... ℓ = L ...)`,
`tailW = max(𝒯_u(min r ℓ), W^{-D})`, `𝒯_u(r) = B_{u,r} e^{-√(r/ℓ_u)}` (`Defs/Tail.lean:44–53`) — the
paper's `wT^L_{u,D}`. The `(eq:kn2sol_decay)` B-only form is not a separate Lean statement (candidate T2093c).

## 2. Vacuity, hidden hypotheses, cycles

- The theorem takes no hypotheses beyond the pin's; the pin is a `def ... : Prop` with explicit binders, no structure.
- Dependencies used, all merged on main:
  `prop5Decay_holds (d Λ) : Prop5Decay d Λ` (`Propagator/Prop5Hold.lean:784`, a proved theorem, not a hypothesis),
  `KLK_two` (`Loop/KLTree`), `Theta_apply_add_right_of_three_le`, `norm_mSigma`, `norm_mul_mSigma_lt_one`,
  `zdistInf_le_zdistD`, `BparamR_antitone`, `ellT_pos`, `Sizes.three_le_L`.
  `Prop5Decay` (`Pins.lean:35`) has the ranges `3 ≤ L`, `0 < g ≤ Λ`, `0 ≤ t < 1`, `‖m‖ = 1`, all `σ₁ σ₂`,
  all `a`; the proof applies it at `Λ = 𝔡⁻¹`, `g = lam`, `t = u`, `m = mE E` with `‖mE E‖ = 1` from `|E| ≤ 2`.
- No cycle: the new file imports `Step2Defs`, `Loop.KLTree`, `Propagator.Pins`, `Propagator.Prop5Hold`,
  `Propagator.Props4` (not `RBM3D`); nothing imports it yet.
- No external hypothesis is introduced, so no limit check is required.
- `Bparam`/`tailT` are positive (`|1-u| > 0`), `STprof ≥ W^{-d-D} > 0`: the bound is not vacuous on the left and
  the right side is a genuine profile; `κ` enters only through `|E| ≤ 2`.

## 3. Compiled nonempty instances

```
$ grep -n "^example" RBM3D/Induction/Step2K2.lean
189:example :
205:example :
```
- line 189: `stK2decay_holds 3 (by norm_num) (1/10) (1/10) …` applied at `sz0`, `n = 0`
  (`sz0_values`: `L = 4`, `W = 32`, `size = 2097152`, `lam = 1/64`), `E = 1/2`, `u = 1/2`, `D = 5`,
  for all `σ` and all `a ∈ (Z_4^3)^2`; `0 < lam`, `lam ≤ 10`, `|E| ≤ 19/10`, `0 ≤ u < 1`, `0 ≤ D` discharged.
- line 205: `sz0`, `n = 1` (`L = 8`, `W = 1024`, `lam = 1/4096`, proved in the example by `norm_num [sz0]`),
  `E = 0`, `u = 99/100`, `D = 0`, `σ = (+,-)`, `a = (0, e₁)` (off-diagonal); all deterministic hypotheses discharged.
Both compile in the module build below; no degenerate data (`L ≥ 4`, nonempty index, `u` near 1 covered).

## 4. Build, axioms, hygiene, diff

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2093-audit1 && lake build RBM3D.Induction.Step2K2 2>&1 | grep -E "error|warning|Build completed|sorry"
warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Path/Walk.lean:599:5: Variable name `hK` is not explicitly referenced.
warning: RBM3D/Propagator/HeatProduct.lean:218:0: `abs_prod_sub_prod_le` does not use the following hypothesis in its type:
warning: RBM3D/Propagator/PropUnit.lean:37:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Propagator/PropUnit.lean:59:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/Step34Pins.lean:12:0: The module doc-string for a file should be the first command after the imports.
warning: RBM3D/Path/Stop.lean:161:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/Step2Defs.lean:922:13: `if_true` has been deprecated: Use `ite_true` instead
warning: RBM3D/Induction/Step2Defs.lean:978:22: `simp at hc'` is a flexible tactic modifying `hc'`. ...
Build completed successfully (3717 jobs).
$ ls -la .lake/build/lib/lean/RBM3D/Induction/Step2K2.olean
-rw-r--r--@ 1 junyin  staff  427080 Oct  3 17:50 .lake/build/lib/lean/RBM3D/Induction/Step2K2.olean   (local time = 00:50 UTC, built in this run)
```
No error; no warning from `Step2K2.lean` (all warnings are in merged upstream files).
```
$ lake env lean scratch/ax.lean
'RBM.Gauss.Sizes.stK2decay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom" RBM3D/Induction/Step2K2.lean ; echo grep_exit=$?
grep_exit=1
$ git diff --name-status main...HEAD
A	RBM3D/Induction/Step2K2.lean
$ git diff main...HEAD -- RBM3D/Induction/Step2Defs.lean RBM3D/Propagator/Pins.lean RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
```
Only the sole writable file `RBM3D/Induction/Step2K2.lean` is touched; no frozen signature changed. Helpers are
`private` (`k2d_*`), §3 (E) satisfied.

## 5. Paper deltas

| Lean/paper difference | Coverage |
|---|---|
| `L^∞` distance `zdistInf` in the profile | existing D18 (T2002b) |
| `≺` replaced by deterministic `≤ C`, all `σ`, all `D ≥ 0`; B-only `(eq:kn2sol_decay)` not stated separately | candidate `T2093c` (prove report §d) |
| pin docstring "costs `c_d`" / "Prop5Decay borrowed" stale | candidates `T2093a`, `T2093b` (docstring only) |

Every statement difference is covered.

## Observations (no effect on verdict)

- O1. `Test/Axioms.lean:136` still lists `RBM.Gauss.Sizes.STK2decay` under owed; the ticket allows removal "once this
  merges (say so)", and the prove report says so (`T2093d`, scratch test of removal with `precheck.lean` exit 0).
  The dispatcher/hub should drop that line after merge.
- O2. The file imports `Propagator.Prop5Hold` and `Propagator.Props4` instead of the ticket's `Evolution.PropTInf`;
  the ticket allows "the merged files they need", and `PropTInf` is not used (only `zdistInf ≤ zdistD`).
- O3. The ticket text calls `Prop5Decay` a borrowed pin; it is proved (`prop5Decay_holds`), so the theorem is
  unconditional, which is stronger than the ticket required.
