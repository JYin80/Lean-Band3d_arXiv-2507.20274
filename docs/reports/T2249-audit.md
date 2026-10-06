Auditor model: claude-opus-5-5

# T2249 audit (round 2) — S6-09c `RBM3D/Induction/QopDecay.lean`

`date -u`: Tue Oct  6 04:32:14 UTC 2026. Branch `t/T2249` at 45d2123 (repair of round-1 RETURN, which was about the
target-4/5 instances only); audit worktree `RBM3D-wt/T2249-audit2` (detached, fresh).

## 1. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Induction.QopDecay 2>&1 | grep -E "error|warning: declaration uses|Build completed|sorry"; echo exit
Build completed successfully (3777 jobs).
exit 0
$ git diff --stat main...HEAD
 RBM3D/Induction/QopDecay.lean | 1078 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1078 insertions(+)
$ git diff main...HEAD -- RBM3D/Induction/QopAlgebra.lean RBM3D/Induction/QopNorm.lean RBM3D/Induction/Step34Pins.lean RBM3D/Test/Axioms.lean | wc -l
       0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^structure|^class|set_option" RBM3D/Induction/QopDecay.lean
27:set_option linter.style.longLine false
$ grep -nE "^(theorem|lemma|def|noncomputable def|abbrev|instance)" RBM3D/Induction/QopDecay.lean
497:theorem QopAlgebra_mollifier_derivDecay (d L m : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g)
514:theorem QopDecay_deriv_fastDecay (d m : ℕ) (K C₀ ε' D' : ℝ) (hε' : 0 < ε') :
636:theorem QopDecay_thetaKer_decay (d : ℕ) (hd : 3 ≤ d) (Λ : ℝ) (hΛ : 0 < Λ) :
762:theorem QopDecay_ThetaN_fastDecay (d n : ℕ) (hd : 3 ≤ d) (Λ K C₀ ε D : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) :
883:theorem QopDecay_STthetaOp_fastDecay {d : ℕ} (hd : 3 ≤ d) (Λ K C₀ ε D : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) :
```
Only the sole writable file is touched; no `Axioms.lean` hunk (none expected: no new `Prop`). All other declarations
are `private` (prefix `qdec_`/`qdecA`/`qdecSz`). Registry pre-check (scratch `import RBM3D` + `import
RBM3D.Induction.QopDecay` + `#assert_rbm_axioms`):
```
$ lake env lean Reg.lean > Reg.out 2>&1; echo "exit $?"; grep -ciE "error|unregistered|not registered" Reg.out
exit 0
0
registry: 2 borrowed + 157 owed + 98 structural + 7 refuted + 12 superseded; ...
```

## 2. Statements against the pin (check file section 2), compiled

Scratch `Eq.lean` = check-file lines 1–21 (imports) + `import RBM3D.Induction.QopDecay` + check lines 22–164 minus
`#check` lines + for each target `X`: `example : RBM.Gauss.Sizes.T2249Check.X := @RBM.Gauss.Sizes.X` and `#print axioms`:
```
$ lake env lean Eq.lean; echo "exit $?"
'RBM.Gauss.Sizes.QopAlgebra_mollifier_derivDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_deriv_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_thetaKer_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_ThetaN_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_STthetaOp_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
The repair did not touch any statement or proof (lines 1–899 identical to round-1 commit 03127a1):
```
$ awk 'NR<883' QopDecay.lean | md5 ; git show 03127a1:RBM3D/Induction/QopDecay.lean | awk 'NR<883' | md5
8a0e1e22a0bb3e75155c60baf04d4328
8a0e1e22a0bb3e75155c60baf04d4328
$ (same for lines 883–899, target 5)
645b23a4fcf85b7eeb04e931fb0072ea
645b23a4fcf85b7eeb04e931fb0072ea
$ git diff 03127a1 45d2123 | grep -E "^@@"
@@ -898,35 +898,77 @@ theorem QopDecay_STthetaOp_fastDecay ...     (section 7: instances only)
@@ -960,65 +1002,76 @@ example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
```
Pins vs ticket mathematics (re-read check lines 112–160): T1 constant `(1+40dm)6^{dm}`, `(1-t)⁻¹`, `((ℓ^d)⁻¹)^m`,
rate `1/4` on `S = Σ_{i≠0}|a_i-a_0|`, `0 ≤ t < 1`; T2 `∃ W₀` after `(d,m,K,C₀,ε',D')`, `(1-t)⁻¹ ≤ W^K`,
`‖B‖ ≤ W^{C₀}`, scale `ℓ_t`; T3 constants `(C,c)` depend on `(d,Λ)` only, every `‖μ‖ = 1`, prefactor `(1-u)⁻¹`, scale
`ℓ_u`; T4 any `n`, any unit charges, `L^d ≤ W^K`, `(1-u)⁻¹ ≤ W^K`, `‖A‖ ≤ W^{C₀}`, `(u,ε,D) → (u,2ε,D-(K+1))`, loss
`K+1` independent of `(ε,D)`, same `u` in and out, `W₀` before `L,g,W,u`; T5 = T4 through `STthetaOp` with every
`σ`, `|E| ≤ 2`. `g ≤ Λ` only in T3–T5. Matches §29/§45 O2 checklist. No special case or conditional adapter.

## 3. Vacuity, hidden hypotheses, cycles

- Premises: `NeZero L`, `3 ≤ L`, `0 < g`, `g ≤ Λ`, time bounds, `L^d ≤ W^K`, `(1-u)⁻¹ ≤ W^K`, norm bounds, `‖μ_i‖ = 1`,
  `|E| ≤ 2`, `EKFastDecay` (merged `def`, `Evolution/Pins.lean:51`, structural), `Sizes d` (data, no analytic field).
  No `Prop`-pin premise, no external hypothesis (no limit check needed).
- Dependencies: merged `prop5Decay_holds`, `B45_row_thetaKer`, `STthetaOp_eq_ThetaN`, `norm_mSigma`; imports only
  merged modules (`QopNorm`, `B45`, `Step2Iterate`, `Prop5Hold`); no cycle.

## 4. Compiled nonempty instances (`QopDecay.lean:973-1076`; all compile, build above)

- T1 (`:973`): `d=3, m=1, L=5, g=1, t=1/2, a=(0,(1,1,1))`. **PASS.**
- T2 (`:984`): `L=5, g=1, t=1/2, B≡1, W = max W₀ 2`; no window hypothesis (O1 of round 1, unchanged). **PASS.**
- T3 (`:998`): `μ = i, x = 0, y = (2,2,2), u = 1/2`. **PASS.**
- T4 (`:1009`, repaired): `d=3, n=2, Λ=1, K=4, C₀=0, ε=1/4, D=1, g=1, u=1/2, μs=(1,i)`, `W = L = N := ⌈W₀⌉₊+9`
  (L chosen after W₀, as the quantifier order allows), `A = qdecA N = 1_{b₀=b₁}`. Discharged in Lean: `N^3 ≤ N^4`,
  `(1-1/2)⁻¹ = 2 ≤ N^4`, `‖qdecA N‖ ≤ N^0`, `EKFastDecay … (qdecA N)` (`qdecA_fastDecay`), `‖μ_i‖ = 1`. The statement
  carries the conjunct `∃ a, N^{2·(1/4)}·ℓ_{1/2} ≤ zdistD(a₀-a₁)` (proved by `qdec_window`, `a = ((⌊N/2⌋)³, 0)`,
  `zdistD = 3⌊N/2⌋ ≥ 3·(N-1)/2 ≥ 2√N ≥ √N·ℓ`, using `ℓ_{1/2}(N,1) ≤ 2`, `qdec_ellT_le`). Since `N ≥ 9 > 1`,
  `N^{1/4}ℓ ≤ N^{1/2}ℓ`, so the hypothesis window is nonempty as well: the `EKFastDecay` premise is no longer vacuous.
  **PASS.**
- T5 (`:1045`, repaired): `qdecSz N` (`L ≡ W ≡ N`, `λ ≡ 1`), `n = 0`, `E = 0`, `u = 1/2`, `σ = (+,-)`, same exponents,
  same `A`, same nonempty-window conjunct. **PASS.**
- Round-1 "Required for resubmission" items 1–4: all met (items 1–3 by the two examples above; item 4 by §1–§2 here
  and report "Repair" section, `T2249-prove.md:217`).

## 5. Paper deltas

```
$ grep -n "D556" docs/paper-deltas.md | cut -c1-80
1515:- **D556（T2239a）**：`(eq:derv_Theta)`（`3_5:1215`）只给 `∂_tϑ` 的大小；论文在 `6:132` 与
$ grep -nE "T2249a|D556" docs/reports/T2249-prove.md | cut -c1-60
212:- `T2249a` (candidate, as the ticket): `(deccA0)` propagation
213:- D556 / `T2239a` (derivative-decay half): `QopAlgebra_mollifier
```
T1 (and its form T2) → D556 derivative-decay half; T3 (kernel decay) and T4 (and its form T5) → `T2249a`. Coverage
complete; no step needed a hypothesis a statement lacks (no `T2249b`).

## 6. Verdicts

| target | statement | vacuity/hidden/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `QopAlgebra_mollifier_derivDecay` | = pin | none | ok | ok | D556 | PASS |
| 2 `QopDecay_deriv_fastDecay` | = pin | none | ok (O1) | ok | D556 | PASS |
| 3 `QopDecay_thetaKer_decay` | = pin | none | ok | ok | T2249a | PASS |
| 4 `QopDecay_ThetaN_fastDecay` | = pin | none | ok (nonempty windows, proved) | ok | T2249a | PASS |
| 5 `QopDecay_STthetaOp_fastDecay` | = pin | none | ok (nonempty windows, proved) | ok | T2249a | PASS |

**Ticket verdict: PASS.** No dispatcher sign-off needed. Merge note: no `Axioms.lean` hunk; the hub adds
`import RBM3D.Induction.QopDecay` after the last `import` line of `RBM3D.lean`.

## 7. Observations (no RETURN)
- O1 (carried from round 1). T2's instance at `L = 5` may have an empty conclusion window once `W₀` is large; T2 has
  no window hypothesis, so this is not a collapsed hypothesis window.
- O2. T4/T5 instances use `D = 1`, so the conclusion's bound is `W^{-(1-5)} = N^4`, which the sup bound
  `‖Θ^{(2)}A‖ ≤ 2·(1-u)⁻¹·‖A‖ = 4` already gives. Every hypothesis is discharged with nonempty windows, so this is
  not degenerate in the sense of CLAUDE.md §4 step 2. Because `qdecA` vanishes on the window, any `D` would
  work, for example `D = 10`.
- O3. `qdecA_ne` (`:904`) is proved but no longer used by an example. It does no harm.
- O4. `set_option linter.style.longLine false` (`:27`) is a style option. It is not a hygiene issue.
