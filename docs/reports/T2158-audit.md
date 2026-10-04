Auditor model: claude-opus-5-5

# T2158 audit (S5-14, `RBM3D/Induction/Step5Kernel.lean`), round 1 — Sun Oct  4 20:18:21 UTC 2026

Branch `t/T2158` at `272ef19`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2158-audit1` (detached).
No check-file pin (the check file only `#check`s upstream names); statements are judged against the
ticket's mathematics and `paper/tex/3_5_Loop_Hierarchy.tex:1983-2058`, `:338` (TTT2).

## 1. Scope, build, axioms, hygiene
```
$ git diff --name-only main...t/T2158
RBM3D/Induction/Step5Kernel.lean
$ lake build RBM3D.Induction.Step5Kernel        # error/summary lines only
✔ [3776/3776] Built RBM3D.Induction.Step5Kernel (30s)
Build completed successfully (3776 jobs).
exit 0          (grep -c "^error" build.out → 0; warnings only in other, merged files)
$ lake env lean ax.lean   # #print axioms for the 10 theorems + 8 instances below, | sort | uniq -c
  18 [propext, Classical.choice, Quot.sound]
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Induction/Step5Kernel.lean | wc -l
       0
```
Only the sole writable file is touched; `RBM3D/Test/Axioms.lean` untouched (no registry line expected).
Imports are merged modules (`Step5Pins`, `TailtoTail`, `Kernel/Evolution`, `Props4`, `Prop5Hold`,
`PropTInf`, `Defs/Tail`); no cycle. `Sizes` (`Defs/Sizes.lean:138`) has fields `L W lam three_le_L W_pos`
only: no hidden hypothesis.

## 2. Statements (extracted by script from the file)
```
L57: theorem step5Kernel_decompU (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {s t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : uKer d L g μ s t = ((s / t : ℝ) : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ) + (((t - s) / t : ℝ) : ℂ) • Theta d L g ((t : ℂ) * μ)
L74: theorem step5Kernel_UN_decompU (hL : 3 ≤ L) {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1) {s t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (A : (Fin n → Zd d L) → ℂ) (a : Fin n → Zd d L) : UN d L g m s t A a = ∑ b : Fin n → Zd d L, (∏ i, ((((s / t : ℝ) : ℂ) • 1 + (((t - s) / t : ℝ) : ℂ) • Theta d L g ((t : ℂ) * cycProd m i)) (a i) (b i))) * A b
L199: theorem step5Kernel_profile_explicit_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g W D u t : ℝ, 0 < g → g ≤ Λ → 0 < W → 0 ≤ u → u ≤ t → t < 1 → (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) → ∀ a₁ a₂ : Zd d L, (1 - u) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ * tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ) ≤ C * tailT d L g t (Gauss.zdistInf d L (a₁ - a₂) : ℕ) + (1 - u) / (1 - t) * W ^ (-D)
L282: theorem step5Kernel_profile_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g W D θ u t : ℝ, 0 < g → g ≤ Λ → 0 < W → 0 ≤ u → u ≤ t → t < 1 → (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) → (1 - u) / (1 - t) ≤ W ^ θ → ∀ a₁ a₂ : Zd d L, (1 - u) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ * tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ) ≤ C * tailW d L g t (L : ℝ) W (D - θ) (Gauss.zdistInf d L (a₁ - a₂) : ℕ)
L529: theorem step5Kernel_calA_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D θ s u t : ℝ), 0 < sz.lam n → sz.lam n ≤ Λ → 0 ≤ s → s ≤ u → u ≤ t → t < 1 → (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t ∨ 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) → (1 - s) / (1 - t) ≤ ((sz.W n : ℕ) : ℝ) ^ θ → ∀ a : Fin 2 → Zd d (sz.L n), step5Kernel_calA sz n D u t a ≤ C * ((1 - s) / (1 - t)) * STprof sz n t (D - 2 * θ) ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
L943: theorem step5Kernel_calA_sup_holds ... (same hypotheses, no u) ... sSup ((fun u => step5Kernel_calA sz n D u t a) '' Set.Icc s t) ≤ C * ((1 - s) / (1 - t)) * STprof sz n t (D - 2 * θ) ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
```
Merged definitions they use (grep):
```
Kernel/Evolution.lean:56  uKer μ s t := (1 - ((s : ℂ) * μ) • SB d L g) * Theta d L g ((t : ℂ) * μ)
Kernel/Evolution.lean:67  UN m s t A a := ∑ b, (∏ i, uKer d L g (cycProd m i) s t (a i) (b i)) * A b
Defs/Tail.lean:53         tailW ℓ W D r := max (tailT d L g t (min r ℓ)) (W ^ (-D))
Induction/Step2Defs.lean:75 STprof n u D ℓ a b := (W^d)⁻¹ * tailW d L lam u ℓ W D (zdistInf (a - b))
Evolution/PropTInf.lean:525-526 EKPropTInf: 0 ≤ u → u ≤ t → t < 1 → (g²/L² ≤ 1-t ∨ 1-u ≤ g²/L²) → ...
Propagator/Pins.lean:34-37 Prop5Decay d Λ: ∃ C c, ∀ L ≥ 3, ∀ g, 0 < g → g ≤ Λ → ...
paper 3_5:336  (TTT2) for 0≤u≤t<1 with (i) 1-u ≥ 1-t ≥ ilambda²/L², or (ii) 1-t ≤ 1-u ≤ ilambda²/L²
```

### Target 1 `(eq:decompU)` — PASS
`uKer μ s t = (s/t)·1 + ((t−s)/t)·Θ_{tμ}` is exactly `(1−sMS)/(1−tMS) = s/t + (t−s)/t Θ_t` with the merged
`uKer`; `UN` form for every `n`, factor `cycProd m i` (`= m(σ₁)m(σ₂)`). Hypotheses `3 ≤ L`, `0<t<1`,
`‖μ‖=1` are those the merged `Theta` facts need; `s` free (more general).

### Target 2 `(eq:THETAinftinf)` — PASS (cited)
Merged `sum_norm_Theta_row_le` (`Props4.lean:210`, `∑_b ‖Θ_{tm,ab}‖ ≤ (1-t)⁻¹`, any `‖m‖=1`) and
`norm_Theta_le` (`:218`); no restatement, as the ticket allows. Instance `step5Kernel_row_sum_inst`.

### Target 3 `(uwp2-92kj)` — PASS
- LHS is the paper's `(1-u)Σ_b Θ^{(+,-)}_{t,a₁b} 𝒯̃^L_{u,D}(|b-a₂|)` (`Θ^{(+,-)}` at `ξ = t`, `ℓ = L`, `zdistInf`).
- `profile_explicit_holds` is the paper's middle line `𝒯_t(|a₁-a₂|) + (1-u)/(1-t) W^{-D}` with no floor
  hypothesis. `profile_holds` is the last `≲` under `(1-u)/(1-t) ≤ W^θ` with `D-θ`. At `θ = 1` this is
  the ticket's `D-1`. Its hypothesis is implied by the ticket's suggested `1-t ≥ W^{-1}` (since `0 ≤ u`),
  so this is the ticket's form, slightly generalised. The ticket explicitly allows a hypothesis here.
- The added TTT2 disjunction is the paper's own condition in `lem:propT` (`3_5:336`), not a new restriction.
- `C = C(d,Λ)` with `0<g≤Λ`, not `C(d)`, is forced by the merged `Prop5Decay d Λ`. Quantifier order:
  `C` comes before `L, g, W, D, θ, u, t, a`. `D ≥ 1` is dropped (`D` is any real), which is more general.
- `step5Kernel_profile_not_unconditional` is a compiled negative statement: inside the TTT2 disjunction,
  the floor-free `D-1` form fails for every `C`. This supports making the hypothesis explicit.

### Target 4 `(uwftgwesj)` — PASS
- `step5Kernel_calA` (`:463`) matches `(eq:def_calA5)` term by term. It uses
  `P_u(x,y) = STprof sz n u D L x y = W^{-d} 𝒯̃^L_{u,D}(|x−y|)` and `Θ^{(+,-)}_t` as `Re Theta(t)`.
  `step5Kernel_norm_Theta_eq_re` proves `‖Θ‖ = Re Θ`, so `Re Θ` is the real kernel and is `≥ 0`.
- `calA_holds` gives the bound for every `u ∈ [s,t]`: `C·(1-s)/(1-t)·W^{-d}𝒯̃^L_{t,D-2θ}`. At `θ = 1`
  this is the ticket's `D-2`. Its hypotheses are `(1-s)/(1-t) ≤ W^θ` and the TTT2 disjunction at `s`,
  which covers every `u ∈ [s,t]` because `1-u ≤ 1-s`.
- `calA_sup_holds` is the `max_u` as an `sSup` over `Icc s t`. The `sSup` is not junk here: the set is
  nonempty and bounded by the pointwise bound.
- `calA_explicit_holds` is the floor-free variant.

## 3. Compiled nonempty instances (same file; ticket data `d=3, L=3, g=1/2, W=2, s=0, u=1/4, t=1/2, D=2`)
```
$ grep -nE "obtain ⟨C, hC, H⟩ :=|^  step5Kernel_|^  ⟨sum_norm" Step5Kernel.lean   (instances section)
985:  step5Kernel_decompU (by norm_num) Complex.norm_I (by norm_num) (by norm_num)
995:  step5Kernel_UN_decompU (by norm_num)
1007:  ⟨sum_norm_Theta_row_le (by norm_num) (by norm_num) (by norm_num) (by simp) 0,
1020:  obtain ⟨C, hC, H⟩ := step5Kernel_profile_holds 3 (1 / 2) le_rfl (by norm_num)
1034:  obtain ⟨C, hC, H⟩ := step5Kernel_profile_explicit_holds 3 (1 / 2) le_rfl (by norm_num)
1046:  obtain ⟨C, hC, H⟩ := Gauss.Sizes.step5Kernel_calA_holds 3 (1 / 2) le_rfl (by norm_num)
1062:  obtain ⟨C, hC, H⟩ := Gauss.Sizes.step5Kernel_calA_explicit_holds 3 (1 / 2) le_rfl (by norm_num)
1076:  obtain ⟨C, hC, H⟩ := Gauss.Sizes.step5Kernel_calA_sup_holds 3 (1 / 2) le_rfl (by norm_num)
```
- Each instance applies its theorem and discharges every hypothesis by `norm_num`, `le_rfl`, `Or.inl`
  or `Complex.norm_I`. The data are `step5Kernel_instSz` (`L=3`, `W=2`, `lam=1/2`), `a = (0, e₁)` and
  `θ = 1`, with item 1 at `μ = i` and `m = (i, ī)`.
- Checks at that data: `g²/L² = 1/36 ≤ 1/2`, `(1-u)/(1-t) = 3/2 ≤ 2`, `(1-s)/(1-t) = 2 ≤ 2`.
- The data are not degenerate: 27 lattice points, `a₁ ≠ a₂`, `0 < u < t < 1`, `W > 1`.
- The instances use ticket data, not `sz0`, which the ticket permits. All 8 compile (build above).

## 4. Paper deltas
- The prove report §(d) proposes four candidates:
  - `T2158a`: explicit `C(d,Λ)` in place of `≺`.
  - `T2158b`: the TTT2 disjunction.
  - `T2158c`: the floor hypothesis `(1-u)/(1-t) ≤ W^θ` with `D-θ`/`D-2θ`, and the failure of the
    unconditional form.
  - `T2158d`: `max_u` read as `∀u`/`sSup`, `Θ^{(+,-)}` as `Re Theta`, `t ≠ 0`.
- These cover every Lean/paper difference found above.
- `docs/paper-deltas.md` has no RBM3D T2158 entry yet (the only `T2158a` hit, line 897, is RBM2D's);
  the dispatcher appends them.

## 5. Observations (no effect on verdict)
- `T2158b` is not a real delta: `lem:propT` (`3_5:336`) already states the disjunction, and the paper
  uses it silently in `(uwp2-92kj)`. It could be recorded as "paper condition made explicit".
- Constants are `∃ C` rather than hard-coded (CLAUDE.md §7). This cannot be avoided, because the
  upstream `Prop5Decay` and `EKPropTInf` are existential. The order (`C` before all data) is correct.
- The public helpers `step5Kernel_theta_decay` and `step5Kernel_norm_Theta_eq_re` are not ticket
  targets and have no instance. They carry the file-stem prefix (§3 (E)).
- Open for S5-15 (prove report §(d)): which `θ` the flow supplies, or use the explicit forms.

## Verdict
Targets 1–4: **PASS**. The ticket overall passes. No dispatcher sign-off is needed for this audit. The
choice of `θ` for S5-15 is the dispatcher's, downstream.
