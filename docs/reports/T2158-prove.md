Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 19:46:03 UTC 2026

Notation. `g = sz.lam n`, `W = sz.W n`, `L = sz.L n`, `ρ = zdistInf`, `μ = cycProd m i = m(σ₁)m(σ₂)`, `‖μ‖ = 1`.
`𝒯̃^L_{u,D}(r) = tailW d L g u L W D r = max(tailT(min r L), W^{-D})`; `ρ ≤ L` (`pti_zdistInf_le_L`, private in `Evolution/PropTInf.lean:53`), so `min(ρ,L) = ρ`.

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `(eq:decompU)` | `uKer μ s t = (s/t)·1 + ((t-s)/t)·Theta(tμ)`; `UN` at `n=2`: `cycProd m 0 = cycProd m 1 = μ` | `3 ≤ L`, `0 < t < 1`, `‖μ‖ = 1` (`s` free: `t ≠ 0` is all the identity needs) | none (identity). Route: `mul_Theta_of_three_le` (`Props4.lean:90`, `(1-ξS)Θ = 1`), `1-sμS = (s/t)(1-tμS) + (t-s)/t`; `norm_t_mul_lt_one` for `‖tμ‖<1`. |
| 2 | `(eq:THETAinftinf)` | `Σ_b ‖Θ_{ab}‖ ≤ (1-t)⁻¹` | `3 ≤ L`, `0 ≤ t < 1`, `‖μ‖=1` | equality at `σ=(+,-)` (script below: max row sum `= 1/(1-t)`). Route: `sum_norm_row_le` (`Evolution.lean:78`) + `norm_Theta_le` (`Props4.lean:218`). No new statement needed. |
| 3 | `C_T` | constant of `ekPropTInf_holds d` (`PropTInf.lean:534`), depends on `d` only | `3 ≤ d`, `0 < g`, `0 ≤ u ≤ t < 1`, **`g²/L² ≤ 1-t ∨ 1-u ≤ g²/L²`** | The ticket's item 3 omits the disjunction; (TTT2) needs it. It holds at `u=t` always, and in paper cases (i)–(iii) (`1-t ≥ g²/L²`, or `1-u ≤ 1-s ≤ g²/L²` in (ii)), so add it as a hypothesis. |
| 4 | `(C₅, c₅)` | constants of `prop5Decay_holds d Λ` (`Prop5Hold.lean:784`): `‖Θ_{tμ}(0,a)‖ ≤ C₅ B(zdistD a) e^{-c₅ zdistD a/ℓ_t}` | `0 < g ≤ Λ`; depends on `(d, Λ)`, **not on `d` alone** | the ticket's `C = C(d)` must read `C(d, Λ)`, `Λ ≥ g` (`g = ilambda ≤ 𝔡⁻¹` by `(eq:WO)`). Instance: `Λ = 1/2`. |
| 5 | bridge `zdistD → ρ` | `C₆ = C₅·exp(1/(4c₅))`: `B(zdistD) ≤ B(ρ)` (`BparamR_antitone`, `ρ ≤ zdistD`: `zdistInf_le_zdistD`), `e^{-c₅x} ≤ e^{1/(4c₅)}e^{-√x}` (from `√x ≤ c₅x + 1/(4c₅)`), `x = ρ/ℓ_t` (`ellT_pos`) | `ℓ_t ≥ 1`, `L ≥ 1` | none. `Θ(a,b)=Θ(0,b-a)`: `Theta_apply_add_right_of_three_le` (`Props4.lean:100`). `Σ_b` with `𝒯_t(ρ(a₁-b))𝒯_u(ρ(b-a₂))` is (TTT2) after `b ↦ c`, `a:=a₂`, `b:=a₁` and `ρ(-x)=ρ(x)` (no merged public lemma; `Green/Pins.lean:501` has a private one; prove again, from `zdist_neg`, `Lattice.lean:53`). |
| 6 | `C₃` (item 3) | `C₃ = C₆·C_T + 1` | — | **see the floor row** |
| 7 | floor, `W^{-D}` term | `(1-u)Σ_b ‖Θ_{a₁b}‖ W^{-D} ≤ (1-u)/(1-t) W^{-D}` (row sum, item 2; no `C₆`) | the paper's `(1-u)/(1-t) W^{-D} ≲ 𝒯̃_{t,D-1}` needs `(1-u)/(1-t) ≤ W`, e.g. **`1 ≤ W(1-t)`**, equivalently `(1-t)⁻¹ ≤ W^θ` with `θ=1` | **FALSE as the paper states it, for `C=C(d)`.** Not implied by `(eq:WO)`: case (iii) has `1-t ≥ ilambda² ≥ W^{2𝔡-d}`, so `W(1-t)` can be `≪ 1`. Numbers below: `L=10⁴`, `1-t=10⁻¹²`, `W=2`, `D=2`, `u=0`: floor/`max(𝒯_t(L/2), W^{-(D-1)})` `= 5.0·10¹¹`. **Correct form (use this):** hypothesis `(1-t)⁻¹ ≤ W^θ` (`θ ≥ 0`, real) gives `(1-u)Σ ≤ C₃ 𝒯̃_{t,D-θ}`; `θ=1` is the ticket's `D-1`. Also state the explicit-factor form `(1-u)Σ ≤ C₆C_T 𝒯_t(ρ) + (1-u)/(1-t) W^{-D}` (no `θ`). |
| 8 | `D`-monotonicity | `tailW` non-decreasing in `W^{-D}`: `W ≥ 1 ⟹ W^{-D} ≤ W^{-(D-θ)}` (`θ ≥ 0`) | `W ≥ 1` (`W_pos` gives `W ≥ 1` as a natural) | none |
| 9 | `𝒯_u ≤ 𝒯_t` for `u ≤ t` | `B_{u,r} ≤ B_{t,r}` (`1-u ≥ 1-t`), `ℓ_u ≤ ℓ_t` (`ellT_mono`, `Kernel/PropT.lean:58`) so `e^{-√(r/ℓ_u)} ≤ e^{-√(r/ℓ_t)}` | `u ≤ t < 1` | term 1 of `𝒜`: `W^{-d}𝒯̃_{u,D}(ρ) ≤ W^{-d}𝒯̃_{t,D}(ρ) ≤ ρ_{st}·W^{-d}𝒯̃_{t,D-2θ}`, `ρ_{st} = (1-s)/(1-t) ≥ 1` |
| 10 | `C₄` (item 4) | `C₄ = 1 + 2C₃ + C₃² = (1+C₃)²` | `0 ≤ s ≤ u ≤ t < 1`; `(t-u) ≤ 1-u`, `(t-u) ≤ 1-s` | term 2 (×2): `(t-u)/(1-u) ≤ 1`, `C₃ 𝒯̃_{t,D-θ}`; term 3: inner `(t-u)Σ_{b₁} ≤ C₃ 𝒯̃_{t,D-θ}(a₁-b₂)`, outer item 3 at `u:=t` (TTT2 disjunction holds at `u=t`; `D:=D-θ`) with `(t-u)/(1-t) ≤ (1-s)/(1-t)`: `C₃² ρ_{st} 𝒯̃_{t,D-2θ}`. Conclusion: `max_{u∈[s,t]} 𝒜_{u,t,a} ≤ C₄ ρ_{st} W^{-d} 𝒯̃_{t,D-2θ}(ρ(a₁-a₂))` (`θ=1`: the ticket's `D-2`). |
| 11 | order of quantifiers | `d, Λ` fixed, then `C(d,Λ)`, then `∀ L g W t s u D` | `3 ≤ d`, `3 ≤ L` (Props4), `0 < g ≤ Λ` | the paper's `≺` is replaced by explicit `C`: paper-delta candidate `T2158a` (no `≺`, explicit `C(d,Λ)`); `T2158b` (hypothesis `(1-t)⁻¹ ≤ W^θ` and TTT2 disjunction added, `D-1`/`D-2` become `D-θ`/`D-2θ`). |

Definition of `𝒜` for the Lean statement (`3_5:2010-2015`, `Θ = Θ^{(+,-)}_t = Theta(t)` real, `≥ 0`, symmetric; `P_u(a,b) = W^{-d}𝒯̃_{u,D}(ρ(a-b))` = `STprof sz n u D L a b`): `𝒜_{u,t,a} = P_u(a₁,a₂) + (t-u)Σ_b[Θ_{a₁b}P_u(b,a₂) + P_u(a₁,b)Θ_{ba₂}] + (t-u)²Σ_{b₁b₂}Θ_{a₁b₁}P_u(b₁,b₂)Θ_{b₂a₂}`.

### (ii) Concrete nondegenerate instance

Ticket instance: `d=3, L=3, g=1/2, W=2, s=0, u=1/4, t=1/2, D=2`, `μ=1`, `θ=1`, `Λ=1/2`. Every hypothesis: `3 ≤ d`, `3 ≤ L`, `0<g≤Λ`, `0 ≤ s ≤ u ≤ t < 1`, `g²/L² = 1/36 ≤ 1-t = 1/2` (TTT2 case (i)), `(1-t)⁻¹ = 2 ≤ W^1 = 2` (slack 0, equality), `D-θ = 1`, `D-2θ = 0`. Items 1 (kernel identity, `t>0`), 2 (row sum), 3, 4 are evaluated on the full torus (`N_L = 27` points, dense inverse `Θ=(1-tS)^{-1}`, `S=S^{(B)}` of `Defs/Block.lean:38`).

Command (script in `scratchpad/T2158/inst.py`, uses the `build/T/tW` of `pre.py` in the same directory; python3 + numpy):
```
hyp: 3<=L True | 0<=u<=t<1 True | g^2/L^2= 0.027777777777777776 <= 1-t = 0.5 | 1<=W(1-t): 1.0 | row-sum max 2.0000000000000004 <= 1/(1-t)= 2.0
item1 maxdiff 0.0
item3 lhs 1.144446318788425 rhs 0.5 worst ratio 0.8568001199580141
item4 worst ratio over u in {0,1/4,1/2} 0.9199440032197584
L=10000 1-t=1e-12 W=2 D=2: floor term 2.500e+11 / max(T_t(r),W^-(D-1)) = 5.000e+11
L=100 1-t=1e-06 W=2 D=2: floor term 2.500e+05 / max(T_t(r),W^-(D-1)) = 4.702e+05
```

Grid of the ticket (`pre.py`; `d=3`, `L∈{7,11}`, `g=1/2`, `t∈{0.5,0.9}`, `u∈{0,t/2,t}`, `D∈{2,4}`, `W∈{2,16}` (ticket gives no `W`), `s=0` for item 4; `ratio = LHS/RHS` worst over all `a₂` (translation invariance); `θ_min = log_W (1-t)⁻¹`). Command `python3 pre.py > out.txt` then a regex max over `out.txt`:
```
item1 max maxdiff over 24 grid points (L,t,s,mu incl. complex mu=e^{2.1i}): 5.55e-15
item2 max row sum = 1/(1-t) exactly (2.000000 / 10.000000 at t=.5/.9, L=7,11)
item3 worst ratio(D-1), W=2,t=.5 : 1.3539      (hyp 1<=W(1-t) holds with equality)
item3 worst ratio(D-1), W=16     : 2.718       (hyp holds)
item3 worst ratio(D-1), W=2,t=.9 : 5.1276      (hyp FAILS, (1-t)W=0.2; ratio bounded here only because L is small)
item3 worst ratio(D-theta_min) W=2,t=.9 : 1.9851
item4 worst ratio(D-2), W=2,t=.5 : 1.3024
item4 worst ratio(D-2), t=.9,W=2 : 2.8806      (hyp FAILS)
item4 worst ratio(D-2), t=.9,W=16: 2.9365      (hyp holds)
```
The worst ratios are the empirical `C₃`, `C₄` of the grid (all `≤ 5.2`).  The ratio is bounded on the grid for every `(t,W)`, so the grid does not by itself exhibit the failure of the unconditional `D-1` form; the formula check in row 7 (printed at the end of the instance output) does.

External hypotheses (TEAM §8 lesson 14): none new. `ekPropTInf_holds`, `prop5Decay_holds`, `norm_Theta_le` are merged theorems, not pins; no limit computation is needed.

### Verdicts

- Target 1 `(eq:decompU)`: PASS (identity, hypotheses `3 ≤ L`, `0 < t < 1`, `‖μ‖=1`).
- Target 2 `(eq:THETAinftinf)`: PASS (cite `norm_Theta_le` + `sum_norm_row_le`; no restatement needed beyond a row-sum form).
- Target 3 `(uwp2-92kj)`: PASS with corrections: add the TTT2 disjunction, `C=C(d,Λ)`, and the floor hypothesis `(1-t)⁻¹ ≤ W^θ` (else give the explicit-factor form); the unconditional `D-1` form is not provable.
- Target 4 `(uwftgwesj)`: PASS with the same corrections (`D-2θ`).

## (a′) Preflight corrections — Sun Oct  4 20:14:25 UTC 2026

Row 7's numeric example of the floor (L=10⁴, 1-t=10⁻¹², g=1/2, u=0) lies outside the hypothesis
`g²/L² ≤ 1-t ∨ 1-u ≤ g²/L²` of (TTT2) that row 3 adds (first line of the last block of (b)), so it does not
refute the conditioned statement.  The verdict is unchanged: the failure of the `D-1` form is compiled at data
inside the disjunction (`step5Kernel_profile_not_unconditional`, (b) below).

## (b) Script output

### Branch, build, axioms
```
$ git -C /Users/junyin/Lean_proof/RBM3D-wt/T2158 log --oneline -3; git diff --stat main...t/T2158
272ef19 T2158: compiled negative statement for the floor, docstrings
e1e8d95 T2158: explicit forms and instances for S5-14
7df94da T2158: Step5Kernel (decompU, profile propagation, calA bound)
 RBM3D/Induction/Step5Kernel.lean | 1083 ++++++++++++++++++++++++++++++++++++++
 1 file changed, 1083 insertions(+)
$ lake build RBM3D.Induction.Step5Kernel   # run 2026-10-04 20:11:22 UTC, exit 0; lines mentioning the new file or errors:
✔ [3776/3776] Built RBM3D.Induction.Step5Kernel (22s)
Build completed successfully (3776 jobs).
$ lake env lean axioms.lean   # one #print axioms per public declaration of the file, run 20:11:27 UTC
  names (21): step5Kernel_decompU step5Kernel_UN_decompU step5Kernel_norm_Theta_eq_re step5Kernel_theta_decay step5Kernel_profile_explicit_holds 
step5Kernel_profile_holds step5Kernel_profile_not_unconditional step5Kernel_Th step5Kernel_calA step5Kernel_calA_holds 
step5Kernel_calA_explicit_holds step5Kernel_calA_sup_holds step5Kernel_instSz step5Kernel_decompU_inst step5Kernel_UN_decompU_inst 
step5Kernel_row_sum_inst step5Kernel_profile_inst step5Kernel_profile_explicit_inst step5Kernel_calA_inst step5Kernel_calA_explicit_inst 
step5Kernel_calA_sup_inst 
$ sed "s/.*depends on axioms: //" axioms.out | sort | uniq -c
  21 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/Step5Kernel.lean | wc -l
0
```

### Registry pre-check (DECISIONS §20) and full build
```
$ cat precheck.lean   # three lines: `import RBM3D`, `import RBM3D.Induction.Step5Kernel`, `#assert_rbm_axioms`
$ lake env lean precheck.lean   # run 20:11:50 UTC
exit 0; first line: axiom audit: 4711 theorems, 1678 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake build   # run 20:11:55 UTC (the root RBM3D.lean does not import the new module; the hub adds the import at merge)
exit 0; last line: Build completed successfully (3922 jobs).
$ names clash: git -C /Users/junyin/Lean_proof/RBM3D grep -nE "step5Kernel_|step5Ker_" main -- RBM3D | wc -l
0
$ grep -rnE "step5Kernel_|step5Ker_" RBM3D --include="*.lean" | grep -v "RBM3D/Induction/Step5Kernel.lean" | wc -l   # in the branch
0
```

### Target statements, extracted from the file (whitespace collapsed; `python3 extract.py <names>`; `d L g` of the two kernel theorems are section variables `{d L : ℕ} [NeZero L] {g : ℝ}`)
```
-- Step5Kernel.lean:57
theorem step5Kernel_decompU (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {s t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : uKer d L g μ s t = ((s / t : ℝ) : ℂ) • (1 :
    Matrix (Zd d L) (Zd d L) ℂ) + (((t - s) / t : ℝ) : ℂ) • Theta d L g ((t : ℂ) * μ) := by
-- Step5Kernel.lean:74
theorem step5Kernel_UN_decompU (hL : 3 ≤ L) {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1) {s t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (A : (Fin n → Zd d L)
    → ℂ) (a : Fin n → Zd d L) : UN d L g m s t A a = ∑ b : Fin n → Zd d L, (∏ i, ((((s / t : ℝ) : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ) + (((t - s) /
    t : ℝ) : ℂ) • Theta d L g ((t : ℂ) * cycProd m i)) (a i) (b i))) * A b := by
-- Step5Kernel.lean:199
theorem step5Kernel_profile_explicit_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g W D u t : ℝ,
    0 < g → g ≤ Λ → 0 < W → 0 ≤ u → u ≤ t → t < 1 → (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) → ∀ a₁ a₂ : Zd d L, (1 - u) * ∑ b : Zd
    d L, ‖Theta d L g (t : ℂ) a₁ b‖ * tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ) ≤ C * tailT d L g t (Gauss.zdistInf d L (a₁ - a₂) :
    ℕ) + (1 - u) / (1 - t) * W ^ (-D) := by
-- Step5Kernel.lean:282
theorem step5Kernel_profile_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g W D θ u t : ℝ, 0 < g
    → g ≤ Λ → 0 < W → 0 ≤ u → u ≤ t → t < 1 → (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) → (1 - u) / (1 - t) ≤ W ^ θ → ∀ a₁ a₂ : Zd d
    L, (1 - u) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ * tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ) ≤ C * tailW d L g t (L : ℝ) W
    (D - θ) (Gauss.zdistInf d L (a₁ - a₂) : ℕ) := by
-- Step5Kernel.lean:359
theorem step5Kernel_profile_not_unconditional (C : ℝ) : ∃ L : ℕ, ∃ _ : NeZero L, 3 ≤ L ∧ (0 ≤ 1 - 1 / (4 * (L : ℝ) ^ 2) ∧ 1 - 1 / (4 * (L : ℝ) ^ 2) <
    1 ∧ (1 / 2 : ℝ) ^ 2 / (L : ℝ) ^ 2 ≤ 1 - (1 - 1 / (4 * (L : ℝ) ^ 2)) ∧ (2 : ℝ) ^ (1 : ℝ) < (1 - 0 : ℝ) / (1 - (1 - 1 / (4 * (L : ℝ) ^ 2)))) ∧ C *
    tailW 3 L (1 / 2 : ℝ) (1 - 1 / (4 * (L : ℝ) ^ 2)) (L : ℝ) (2 : ℝ) (2 - 1 : ℝ) (Gauss.zdistInf 3 L ((0 : Zd 3 L) - 0) : ℕ) < (1 - 0 : ℝ) * ∑ b : Zd
    3 L, ‖Theta 3 L (1 / 2 : ℝ) (((1 - 1 / (4 * (L : ℝ) ^ 2) : ℝ)) : ℂ) 0 b‖ * tailW 3 L (1 / 2 : ℝ) 0 (L : ℝ) (2 : ℝ) (2 : ℝ) (Gauss.zdistInf 3 L (b
    - 0) : ℕ) := by
-- Step5Kernel.lean:456
noncomputable def step5Kernel_Th (n : ℕ) (t : ℝ) (a b : Zd d (sz.L n)) : ℝ := (Theta d (sz.L n) (sz.lam n) (t : ℂ) a b).re
-- Step5Kernel.lean:463
noncomputable def step5Kernel_calA (n : ℕ) (D u t : ℝ) (a : Fin 2 → Zd d (sz.L n)) : ℝ := STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + (t - u) * ∑
    b : Zd d (sz.L n), (step5Kernel_Th sz n t (a 0) b * STprof sz n u D ((sz.L n : ℕ) : ℝ) b (a 1) + STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) b *
    step5Kernel_Th sz n t b (a 1)) + (t - u) ^ 2 * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n), step5Kernel_Th sz n t (a 0) b₁ * STprof sz n u D ((sz.L
    n : ℕ) : ℝ) b₁ b₂ * step5Kernel_Th sz n t b₂ (a 1)
-- Step5Kernel.lean:529
theorem step5Kernel_calA_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D θ s u t : ℝ), 0 < sz.lam n →
    sz.lam n ≤ Λ → 0 ≤ s → s ≤ u → u ≤ t → t < 1 → (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t ∨ 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
    (1 - s) / (1 - t) ≤ ((sz.W n : ℕ) : ℝ) ^ θ → ∀ a : Fin 2 → Zd d (sz.L n), step5Kernel_calA sz n D u t a ≤ C * ((1 - s) / (1 - t)) * STprof sz n t
    (D - 2 * θ) ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
-- Step5Kernel.lean:739
theorem step5Kernel_calA_explicit_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D s u t : ℝ), 0 <
    sz.lam n → sz.lam n ≤ Λ → 0 ≤ s → s ≤ u → u ≤ t → t < 1 → (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t ∨ 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) :
    ℝ) ^ 2) → ∀ a : Fin 2 → Zd d (sz.L n), step5Kernel_calA sz n D u t a ≤ C * ((1 - s) / (1 - t)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (tailT d (sz.L n)
    (sz.lam n) t ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))) := by
-- Step5Kernel.lean:943
theorem step5Kernel_calA_sup_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D θ s t : ℝ), 0 < sz.lam n →
    sz.lam n ≤ Λ → 0 ≤ s → s ≤ t → t < 1 → (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t ∨ 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) → (1 - s) /
    (1 - t) ≤ ((sz.W n : ℕ) : ℝ) ^ θ → ∀ a : Fin 2 → Zd d (sz.L n), sSup ((fun u => step5Kernel_calA sz n D u t a) '' Set.Icc s t) ≤ C * ((1 - s) / (1
    - t)) * STprof sz n t (D - 2 * θ) ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
```

### Compiled nonempty instances (same file; `d=3, L=3, g=1/2, W=2, D=2, θ=1, Λ=1/2`; hypotheses all discharged by `norm_num`)
```
-- Step5Kernel.lean:972
noncomputable def step5Kernel_instSz : Gauss.Sizes 3 where L := fun _ => 3 W := fun _ => 2 lam := fun _ => 1 / 2 three_le_L := fun _ => le_rfl W_pos
    := fun _ => by norm_num
-- Step5Kernel.lean:980
theorem step5Kernel_decompU_inst : uKer 3 3 (1 / 2 : ℝ) Complex.I (1 / 4 : ℝ) (1 / 2 : ℝ) = (((1 / 4 : ℝ) / (1 / 2 : ℝ) : ℝ) : ℂ) • (1 : Matrix (Zd 3
    3) (Zd 3 3) ℂ) + ((((1 / 2 : ℝ) - (1 / 4 : ℝ)) / (1 / 2 : ℝ) : ℝ) : ℂ) • Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * Complex.I) :=
-- Step5Kernel.lean:988
theorem step5Kernel_UN_decompU_inst : UN 3 3 (1 / 2 : ℝ) ![Complex.I, (starRingEnd ℂ) Complex.I] (0 : ℝ) (1 / 2 : ℝ) (fun _ : Fin 2 → Zd 3 3 => (1 :
    ℂ)) ![0, ![1, 0, 0]] = ∑ b : Fin 2 → Zd 3 3, (∏ i, ((((0 / (1 / 2) : ℝ) : ℂ) • (1 : Matrix (Zd 3 3) (Zd 3 3) ℂ) + ((((1 / 2 : ℝ) - 0) / (1 / 2) :
    ℝ) : ℂ) • Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * cycProd ![Complex.I, (starRingEnd ℂ) Complex.I] i)) (![0, ![1, 0, 0]] i) (b i))) * 1 :=
-- Step5Kernel.lean:1002
theorem step5Kernel_row_sum_inst : (∑ b : Zd 3 3, ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * 1) 0 b‖ ≤ (1 - 1 / 2 : ℝ)⁻¹) ∧ (∑ b : Zd 3 3, ‖Theta 3 3
    (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * Complex.I) 0 b‖ ≤ (1 - 1 / 2 : ℝ)⁻¹) ∧ ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ (1 - 1 / 2 :
    ℝ)⁻¹ :=
-- Step5Kernel.lean:1013
theorem step5Kernel_profile_inst : ∃ C : ℝ, 0 < C ∧ (1 - 1 / 4 : ℝ) * ∑ b : Zd 3 3, ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ)) : ℂ) 0 b‖ * tailW 3 3 (1 / 2
    : ℝ) (1 / 4 : ℝ) ((3 : ℕ) : ℝ) (2 : ℝ) (2 : ℝ) (Gauss.zdistInf 3 3 (b - ![1, 0, 0]) : ℕ) ≤ C * tailW 3 3 (1 / 2 : ℝ) (1 / 2 : ℝ) ((3 : ℕ) : ℝ) (2
    : ℝ) (2 - 1 : ℝ) (Gauss.zdistInf 3 3 ((0 : Zd 3 3) - ![1, 0, 0]) : ℕ) := by
-- Step5Kernel.lean:1026
theorem step5Kernel_profile_explicit_inst : ∃ C : ℝ, 0 < C ∧ (1 - 1 / 4 : ℝ) * ∑ b : Zd 3 3, ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ)) : ℂ) 0 b‖ * tailW 3
    3 (1 / 2 : ℝ) (1 / 4 : ℝ) ((3 : ℕ) : ℝ) (2 : ℝ) (2 : ℝ) (Gauss.zdistInf 3 3 (b - ![1, 0, 0]) : ℕ) ≤ C * tailT 3 3 (1 / 2 : ℝ) (1 / 2 : ℝ)
    (Gauss.zdistInf 3 3 ((0 : Zd 3 3) - ![1, 0, 0]) : ℕ) + (1 - 1 / 4 : ℝ) / (1 - 1 / 2) * (2 : ℝ) ^ (-(2 : ℝ)) := by
-- Step5Kernel.lean:1039
theorem step5Kernel_calA_inst : ∃ C : ℝ, 0 < C ∧ Gauss.Sizes.step5Kernel_calA step5Kernel_instSz 0 2 (1 / 4) (1 / 2) ![0, ![1, 0, 0]] ≤ C * ((1 - 0 :
    ℝ) / (1 - 1 / 2)) * Gauss.Sizes.STprof step5Kernel_instSz 0 (1 / 2) (2 - 2 * 1) ((step5Kernel_instSz.L 0 : ℕ) : ℝ) ((![0, ![1, 0, 0]] : Fin 2 → Zd
    3 (step5Kernel_instSz.L 0)) 0) ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 1) := by
-- Step5Kernel.lean:1052
theorem step5Kernel_calA_explicit_inst : ∃ C : ℝ, 0 < C ∧ Gauss.Sizes.step5Kernel_calA step5Kernel_instSz 0 2 (1 / 4) (1 / 2) ![0, ![1, 0, 0]] ≤ C *
    ((1 - 0 : ℝ) / (1 - 1 / 2)) * ((((step5Kernel_instSz.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * (tailT 3 (step5Kernel_instSz.L 0) (step5Kernel_instSz.lam 0) (1 / 2)
    (Gauss.zdistInf 3 (step5Kernel_instSz.L 0) (((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 0) - ((![0, ![1, 0, 0]] : Fin 2 → Zd 3
    (step5Kernel_instSz.L 0)) 1)) : ℕ) + (1 - 0 : ℝ) / (1 - 1 / 2) * ((step5Kernel_instSz.W 0 : ℕ) : ℝ) ^ (-(2 : ℝ)))) := by
-- Step5Kernel.lean:1068
theorem step5Kernel_calA_sup_inst : ∃ C : ℝ, 0 < C ∧ sSup ((fun u => Gauss.Sizes.step5Kernel_calA step5Kernel_instSz 0 2 u (1 / 2) ![0, ![1, 0, 0]])
    '' Set.Icc (0 : ℝ) (1 / 2)) ≤ C * ((1 - 0 : ℝ) / (1 - 1 / 2)) * Gauss.Sizes.STprof step5Kernel_instSz 0 (1 / 2) (2 - 2 * 1) ((step5Kernel_instSz.L
    0 : ℕ) : ℝ) ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 0) ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 1) := by
```

### Numeric reading of the compiled negative statement (`python3 neg.py`, run 20:14:33 UTC)
```
(a) row 7 example: L=1e4, 1-t=1e-12:  g^2/L^2 = 2.5e-09  <= 1-t ? False  1-u <= g^2/L^2 ? False
L=    3 1-t=2.778e-02 g^2/L^2<=1-t:True (1-u)/(1-t)=36.0 > W=2.0: True  floor=9  rhs=4.933  ratio=1.824
L=   10 1-t=2.500e-03 g^2/L^2<=1-t:True (1-u)/(1-t)=400.0 > W=2.0: True  floor=100  rhs=4.36  ratio=22.93
L=  100 1-t=2.500e-05 g^2/L^2<=1-t:True (1-u)/(1-t)=40000.0 > W=2.0: True  floor=1e+04  rhs=4.04  ratio=2475
L= 1000 1-t=2.500e-07 g^2/L^2<=1-t:True (1-u)/(1-t)=4000000.0 > W=2.0: True  floor=1e+06  rhs=4.004  ratio=2.498e+05
```

### Narrative (facts only)
- All four items are in `RBM3D/Induction/Step5Kernel.lean` (1083 lines, three commits on `t/T2158`, last `272ef19`); `lake build` of the module, the registry pre-check and the full `lake build` exit 0 (blocks above).
- Item 1: `step5Kernel_decompU` is the kernel identity `uKer μ s t = (s/t)·1 + ((t-s)/t)·Theta(tμ)` for `3 ≤ L`, `0 < t < 1`, `‖μ‖ = 1` (`s` free); proof: `mul_Theta_of_three_le` and `1 - sμS = (s/t)(1 - tμS) + (t-s)/t`. `step5Kernel_UN_decompU` states it inside the merged `UN` for every `n` (factors `cycProd m i`).
- Item 2: no new statement; the merged `sum_norm_Theta_row_le` (`Props4.lean:210`) and `norm_Theta_le` (`Props4.lean:218`) are used in items 3-4 and instantiated in `step5Kernel_row_sum_inst`.
- Item 3: `step5Kernel_theta_decay`: `‖Θ_{t,ab}‖ ≤ C₆ 𝒯_t(|b-a|_∞)`, `C₆ = C₅ e^{1/(4c₅)}` from `prop5Decay_holds d Λ` at `m = 1`, `σ = (+,-)` (`zdistInf ≤ zdistD`, `BparamR_antitone`, `√x ≤ c x + 1/(4c)`). Then `step5Kernel_profile_explicit_holds`: `(1-u) Σ_b ‖Θ_{a₁b}‖ 𝒯̃_{u,D}(|b-a₂|) ≤ C 𝒯_t(|a₁-a₂|) + (1-u)/(1-t) W^{-D}`, `C = C₆ C_T` (`ekPropTInf_holds`, `max(x,y) ≤ x+y`, `|·|_∞ ≤ L` so `r ∧ L = r`, floor by the row sum), no hypothesis on `(1-t)W`. `step5Kernel_profile_holds` absorbs the floor under `(1-u)/(1-t) ≤ W^θ` into `𝒯̃_{t,D-θ}` (`C + 1`); `θ = 1` is the paper's `D-1`.
- The ticket's `C = C(d)` is `C(d, Λ)`, `0 < g ≤ Λ`; the `(TTT2)` disjunction `g²/L² ≤ 1-t ∨ 1-u ≤ g²/L²` is a hypothesis: both as (a) rows 3-4 say. `D ≥ 1` is not needed (`D` is any real).
- The unconditional `D-1` form is false: `step5Kernel_profile_not_unconditional` (compiled) gives, for every `C`, data with `g = 1/2`, `W = 2`, `D = 2`, `u = 0`, `t = 1 - 1/(4L²)`, `a₁ = a₂` inside the hypotheses of the explicit form, where `LHS ≥ L²` and `RHS ≤ 8`; only `(1-u)/(1-t) ≤ W^θ` fails.
- Item 4: `step5Kernel_calA` is `(eq:def_calA5)` with `STprof sz n u D L` and `Θ^{(+,-)}` as `Re Theta` (real, `≥ 0`: `step5Kernel_norm_Theta_eq_re`). `step5Kernel_calA_holds`: for every `u ∈ [s,t]`, `𝒜 ≤ (1+C₃)² (1-s)/(1-t) STprof sz n t (D-2θ)`, under `(1-s)/(1-t) ≤ W^θ` and `g²/L² ≤ 1-t ∨ 1-s ≤ g²/L²`; proof: item 3 at `(u,D)` and at `(t, D-θ)`, `t-u ≤ 1-u`, `t-u ≤ 1-s`, `𝒯̃_{u,D} ≤ 𝒯̃_{t,D}` (`ℓ_u ≤ ℓ_t`, `B_u ≤ B_t`), `W^{-D} ≤ W^{-(D-θ)}`.  `step5Kernel_calA_explicit_holds`: no floor hypothesis, `𝒜 ≤ C R W^{-d}[𝒯_t + R W^{-D}]`, `R = (1-s)/(1-t)`, `C = (1+C₃)²+C₃+4`.  `step5Kernel_calA_sup_holds`: the same bound for `sSup` over `Set.Icc s t` (the paper's `max_u`).
- Instances: each target has one at `d = 3, L = 3` (27 points), `g = 1/2`, `W = 2`, `D = 2`, and `a = (0, e₁)` where a point is needed (the kernel identity has none); item 1 at `s = 1/4`, `μ = i` (kernel) and `s = 0`, `m = (i, ī)` (inside `UN`); items 3-4 at `s = 0, u = 1/4, t = 1/2` (`(1-u)/(1-t) = 3/2`, `(1-s)/(1-t) = 2 = W^1`). The sizes are `step5Kernel_instSz` (constant `L, W, lam`), not `sz0` (`L = 4, W = 32`).
- No port: nothing was copied from `../RBM1D` or `../RBM2D` (none read), so no diff-stat applies. The file imports `Step5Pins` and `TailtoTail` as the ticket lists; no declaration of `TailtoTail` is used.
- Registry: the file defines no `Prop`-valued predicate; `RBM3D/Test/Axioms.lean` is untouched.

## (c) Mathlib and merged names used (the non-elementary ones; each compiled; `names.lean`, 49 `#check @` lines, run 20:13:08 UTC, exit 0, no error)
Finset: `sum_comm, mul_sum, sum_mul, sum_add_distrib, sum_le_sum, sum_nonneg, sum_congr, sup_congr, sup_le`. Real: `rpow_add, rpow_nonneg, rpow_neg, rpow_two, rpow_one, exp_le_exp, exp_add, exp_pos, sqrt_le_sqrt, sq_sqrt, norm_of_nonneg`. Complex: `norm_real, norm_I`.
Order/field: `inv_anti₀, div_le_div_of_nonneg_right, div_le_div_of_nonneg_left, le_div_iff₀, div_le_iff₀, one_le_div, div_le_one, div_self, one_div_one_div, le_mul_of_one_le_left, mul_le_mul, max_le, max_le_max, min_eq_left, le_total, le_add_of_nonneg_right, le_add_of_nonneg_left, sub_nonneg, abs_of_pos, abs_nonneg, le_abs_self`.
Other: `csSup_le, Set.left_mem_Icc, Set.mem_image_of_mem, Nat.le_ceil, Nat.cast_nonneg, Matrix.transpose_apply`, tactic `match_scalars`. Names verified absent: none searched.
Merged RBM3D (file:line): `prop5Decay_holds` Prop5Hold:784; `ekPropTInf_holds` PropTInf:534; `sum_norm_Theta_row_le` Props4:210; `norm_Theta_le` Props4:218; `sum_Theta_real_row` Props4:203; `Theta_apply_add_right_of_three_le` Props4:100; `Theta_transpose_of_three_le` Props4:95; `mul_Theta_of_three_le` Props4:90; `Theta_real_eq/_nonneg` Props4:173/177; `norm_t_mul_lt_one` Props4:182; `norm_cycProd` Evolution:73; `uKer, UN` Evolution:56, 65; `BparamR_antitone/_natCast` Tail:71/57; `tailT_zero, tailT_nonneg, rpow_neg_le_tailW, tailW_pos` Tail:84, 81, 101, 105; `ellT_pos` Params:44; `ellT_mono` Kernel/PropT:58; `zdistInf_le_zdistD` Defs/Sizes:117; `zdist_neg` Lattice:53; `zdist_le_L` RadialSum:40; `STprof` Step2Defs:75.

## (d) Open issues and paper-delta candidates
- `T2158a`: the paper's `≺`/`≲` in `(uwp2-92kj)`, `(uwftgwesj)` become explicit constants `C(d, Λ)` (`0 < g ≤ Λ`, from `prop5Decay_holds d Λ`), not `C(d)`.
- `T2158b`: `(TTT2)` needs `g²/L² ≤ 1-t ∨ 1-u ≤ g²/L²` (as `EKPropTInf`); item 4 carries `g²/L² ≤ 1-t ∨ 1-s ≤ g²/L²` (covers every `u ∈ [s,t]`).
- `T2158c`: the last `≲` of `(uwp2-92kj)`, `(1-u)/(1-t) W^{-D} ≲ 𝒯̃_{t,D-1}`, fails for `C` independent of `L` (`step5Kernel_profile_not_unconditional`). Correct forms: explicit (`C 𝒯_t + (1-u)/(1-t) W^{-D}`, `step5Kernel_calA_explicit_holds` for item 4) or hypothesis `(1-u)/(1-t) ≤ W^θ` with `D-θ`, `D-2θ`; the paper's `D-1`, `D-2` are `θ = 1`.
- `T2158d`: the paper's `max_{u∈[s,t]}` is `∀ u ∈ [s,t]` and `sSup` over `Set.Icc s t`; `Θ^{(+,-)}` enters `𝒜` as `Re Theta`; `(eq:decompU)` needs `t ≠ 0` (here `0 < t`).
- Open for the dispatcher / S5-15: which `θ` S5-15 can supply. If the flow keeps `1-t ≥ N^{-κ}` and `W ≥ N^𝔠`, then `(1-t)⁻¹ ≤ W^{κ/𝔠}`, i.e. `θ = κ/𝔠` (a conditional remark, not proved here); if no such lower bound is available, S5-15 should use the explicit forms.
- Remark (mathematics, not compiled): in `step5Kernel_calA_explicit_holds` the bracket is `𝒯_t + R W^{-D}`; under `R ≤ W^θ` it is `≤ 2 𝒯̃_{t,D-θ}` (`𝒯_t ≤ 𝒯̃`, `R W^{-D} ≤ W^{-(D-θ)} ≤ 𝒯̃_{t,D-θ}`), so with the prefactor `R` kept the loss would be `D-θ`, not the paper's `D-2` (`θ = 1`); `step5Kernel_calA_holds` states `D-2θ` as the ticket asks.
