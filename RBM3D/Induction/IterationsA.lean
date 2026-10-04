/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Split

/-!
# S3-24a (ticket T2087): `lem:iterations` at `d ≥ 3`: the `Ψ`-calculus, the chain bound
`(xiu2n+2psi)` and the step

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `(rela_XILXILK)`
`3_5:1387`, `(sef8w483r324)` `3_5:1391`, `(adsyzz0s8d6)` (`Ψ`) `3_5:1396`, `lem:iterations`
`3_5:1407-1417`, its proof `3_5:1772-1864` (`(xiu2n+2psi)` `3_5:1785`, `(suauwiioo1)` `3_5:1832`,
`(eq:boundtwochains)` `3_5:1842`, `(auskoppw2)` `3_5:1857`).  Source of the port: RBM2D
`Induction/Step3.lean` at `c9a24cf`, lines 1-777 (the cut is `end Generic`, `:777`; `MatrixLevel`
`:781` onward is S3-24b / S3-25).

## The RBM2D calculus is not the `d ≥ 3` calculus

RBM2D's lines 1-777 are built on `step3_Psi As R n k = As^{1/2} + R^{n-1} As^{1-k/4}`, on the row
`R² As^{3/4} ≤ M_u ≤ As`, on the final choice `k = n + 1` and on the slot `Lemma514` (`X_n ≺
Λ^{1/2} + Φ`, `Y_{2n+2} ≺ Λ`); the real lemmas `step3_ineq_*` are statements about `b = As^{1/4}`.
At `d ≥ 3` the paper has `Ψ = A^{3/4} + ρ^{n-1} A^{1-k/8}` (`A = ilambda² W^d` or
`(W^{-d}B_{s,0})⁻¹`, `ρ = η_s/η_u`), no row `R² M^{3/4} ≤ M_u` (replaced by `ρ ≤ A^{𝔠d}`, `B_v ≤
c_B A^{-1+δ}`), the depth `k_min = ⌊2 + 8𝔠d(r-1)⌋ + 1` (`st_kmin`, `ScaleFacts3`), and the slot
`Lemma514` is the bootstrap bound `(am;asoi222)` = the merged `STXiBoot` (`3_5:1366`), whose chain
term is `B^{-1/(4p)} Ξ_{2n-1}^{1/2} Ξ_{4p}^{1/(4p)}`.  So the exponents `b³, b⁴, R²` of the ticket
are `d = 2` objects (paper-delta candidate `T2087a`), `step3_Psi` is not `STPsi` (no `As`, `k`
make them agree), and the RBM2D real lemmas are restated, not copied.

## Map RBM2D (`c9a24cf:RBM2D/Induction/Step3.lean`) → this file (all RBM2D names are `private`)

* `Step3Target` `:96` (`d`-dimensional form) = the merged `STStep3R` (`Step34Pins.lean:250`); no
  new `Prop`.
* section `Real` `:104-285` (`rpow_quarter`, `rpow_half_eq`, `rpow_three_quarter_eq`,
  `self_eq_rpow_quarter_pow`, `rpow_pred_eq`, `rpow_one_sub_le`, `scale_facts`, `ineq_5120`,
  `ineq_quad`, `ineq_quad_two`, `ineq_long`) → `iterationsA_rpow_pred`, `iterationsA_STPsi_eq`
  (`A^{3/4} = b⁶`, `b = A^{1/8}`), `iterationsA_ineq_long`, `iterationsA_ineq_quad`,
  `iterationsA_ineq_chain` and `iterationsA_chain_term` (`ineq_5120`: the chain bound
  `(xiu2n+2psi)`), `iterationsA_boot_bound` (their assembly into `STbootRHS ≤ C Ψ`);
  `ineq_quad_two` has no counterpart (the quadratic sum of `STbootRHS` starts at `⌈N/2⌉ + 1`
  and is empty unless `N ≥ 4`, so all its terms have `m ≥ 3`).
* section `PsiDefs` `:289-344` (`step3_Psi`, `step3_psi`, `psi_of_ne_zero`, `psi_zero`,
  `Psi_nonneg`, `psi_nonneg`, `Psi_eq`, `psi_pred_le`, `Psi_mono`) → the merged `STPsi` (the
  level `k = 0` is `STPsi A ρ n 0`, the a priori bound `(sef8w483r324)`),
  `iterationsA_STPsi_nonneg`,
  `iterationsA_STPsi_eq`, `iterationsA_STPsi_pred`, `iterationsA_STPsi_anti_k`,
  `iterationsA_STPsi_mono_n`, `iterationsA_one_le_STPsi`.
* section `Abstract` `:352-695`: `step3_trans`, `step3_one_add_inv_mul` → merged
  `StochDomAt.trans` and `iterationsA_prec_one_add_mul`; `Step3Scales` (+ `.kit`) →
  `IterationsAScale`, proved in both cases by `iterationsA_scale_I`, `iterationsA_scale_II`;
  `step3S` → `STIterHyp`; `step3Lemma514` → `STXiBoot`; `Step3Hyp` → `IterationsAScale` plus the
  hypotheses `hrela`, `havg`, `hapri` (proved from the merged pins by `iterationsA_rela_of_K`,
  `iterationsA_avg_of_STAvgU`, `iterationsA_apriori_of_lRB1`) and `(5.118)` = `RBM.Ind.loopXi_le`
  (`Split.lean`, S1-09) through `iterationsA_STXiL_eq`, `iterationsA_xiL_odd_le`; `xiL_5119`,
  `rhs5119_le`, `xiL_two_mul_add_two` (`Y_{2n+2}`) → the odd chain bound `Ξ̂_{2N-1}` of
  `(auskoppw2)`; `xiLK_two_le` (`S(2,3)`) has no counterpart; `quad_of`, `S_of_S` →
  `iterationsA_step`; `S_all` → `st_iterate` (`ScaleFacts3`); `Psi_succ_le`, `xiLK_le`,
  `xiL_le_one_of` → `st_hscale_I/II` (`ScaleFacts3`) and the skeleton of S3-25.
* section `Generic` `:699-777` (`rpow_mul_rpow_neg_add`, `of_forall_le_rpow_mul`, `mul_det`,
  `pullback`, `label_max`) → the four probe helpers of section 1 (`st_prec_one_add_sup` = the
  label maximum), `StochDomAt.precomp_param` (`pullback`), `StochDomAt.const_mul_*`.

## Contents

* §1 `st_prec_one_add_sup`, `st_prec_of_xi`, `st_one_le_XiL`, `st_one_le_XiLK`: verbatim from
  `3c58211:RBM3D/Probe/T2041Pins.lean` (`:840`, `:866`, `:1068`, `:1077`).
* §2 the real inequalities (polynomial in `b = A^{1/8}`, `ρ`, `e = A^{1-k/8}`, `T ≥
  W^{-d}B_{v,0}`); §3 the `Ψ`-calculus; §4 the chain bound `(xiu2n+2psi)`
  (`iterationsA_chain_term`) and the deterministic assembly `STbootRHS ≤ C Ψ(N,k)`
  (`iterationsA_boot_bound`), `p ≥ 2` (paper `p ≥ 4`); §5 `(5.118)` for the model.
* §6-§7 the `≺`-calculus and **the step** `iterationsA_step`: `(eq:iteration_induc)` at `(r,k)`,
  `2 ≤ r ≤ N-1`, and `(r,k-1)`, `2 ≤ r ≤ N+2`, give it at `(N,k)`; any `d` (the scale facts carry
  the dimension); `p = N + 4`; `N = 2` uses the control of `Ξ̂_3`, `N ≥ 3` the chain bound (the
  paper uses the a priori bound for `N ∈ {2,3}`).  §7b the hypotheses of the step from the merged
  pins.
* §8 `iterationsA_scale_I` (case (i), needs `2 ≤ d`, `𝔠d ≤ 1/16`) and `iterationsA_scale_II` (case
  (ii), `𝔠d ≤ 1/24`).  §9 the instances.

DECISIONS §29: no statement uses `0 ≤ s`, the boundary `1 - ilambda²/L²` or `L^d ≤ W^K`; the
constants (`2`, `1`) contain no `W`, `L`, `ilambda`; the `∀ n` facts (`A ≥ 0`, `T ≥ 0`, `t < 1`)
hold for every `n` in both cases, all others are `∀ᶠ n`.

-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The `≺`-helpers of the T2041 probe (verbatim) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

theorem st_prec_one_add_sup {U V : ℕ → Type*} [∀ n, Fintype (V n)] [hV : ∀ n, Nonempty (V n)]
    (hsize : Tendsto sz.size atTop atTop) (f : ∀ n, U n → V n → sz.SeqΩ → ℝ) (B : ∀ n, U n → ℝ)
    (hB : ∀ n u, 0 < B n u)
    (h : Prec sz (U := fun n => U n × V n) (fun n p ω => f n p.1 p.2 ω) (fun n p _ => B n p.1)) :
    Prec sz (U := U)
      (fun n u ω => 1 + Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) / B n u)
      (fun _ _ _ => 1) := by
  intro τ hτ D hD
  filter_upwards [h (τ / 2) (half_pos hτ) D hD,
    hsize.eventually (eventually_le_rpow 2 (half_pos hτ))] with n hn h2
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨u, hu⟩
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := V n)) (fun v => f n u v ω)
  refine ⟨(u, v), ?_⟩
  have hNN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hh : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ
  have hu' : ((sz.size n : ℕ) : ℝ) ^ τ < 1 + f n u v ω / B n u := by
    rw [← hv]; simpa using hu
  have hBpos := hB n u
  set a : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with ha
  have h3 : a < f n u v ω / B n u := by nlinarith
  change a * B n u < f n u v ω
  have := (lt_div_iff₀ hBpos).1 h3
  exact this

theorem st_prec_of_xi {U V : ℕ → Type*} [∀ n, Fintype (V n)] [hV : ∀ n, Nonempty (V n)]
    (f : ∀ n, U n → V n → sz.SeqΩ → ℝ) (B : ∀ n, U n → ℝ) (hB : ∀ n u, 0 < B n u)
    (h : Prec sz (U := U)
      (fun n u ω => 1 + Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) / B n u)
      (fun _ _ _ => 1)) :
    Prec sz (U := fun n => U n × V n) (fun n p ω => f n p.1 p.2 ω) (fun n p _ => B n p.1) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨⟨u, v⟩, hu⟩
  refine ⟨u, ?_⟩
  have hBpos := hB n u
  have h1 : f n u v ω ≤ Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) :=
    Finset.le_sup' (fun v => f n u v ω) (Finset.mem_univ v)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ τ < f n u v ω / B n u := by
    rw [lt_div_iff₀ hBpos]; exact hu
  have h3 : f n u v ω / B n u ≤ Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) / B n u :=
    div_le_div_of_nonneg_right h1 hBpos.le
  change ((sz.size n : ℕ) : ℝ) ^ τ * 1 < _
  linarith

/-- `0 ≤ max`, hence `Ξ̂ ≥ 1`, for a positive `W^{-d}B_{v,0}`. -/
theorem st_one_le_XiL {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) :
    1 ≤ STXiL sz n E v k ω := by
  unfold STXiL
  have h0 : 0 ≤ STmaxL sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB (k - 1)).le
  linarith

theorem st_one_le_XiLK {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) :
    1 ≤ STXiLK sz n E v k ω := by
  unfold STXiLK
  have h0 : 0 ≤ STmaxLK sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω - STKloop sz n E v p.1 p.2‖)
      (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB k).le
  linarith

end RBM.Gauss.Sizes

/-! ## 2. The real inequalities -/

namespace RBM.Ind


/-- `ρ ≤ ρ²` for `ρ ≥ 1`. -/
private theorem iterationsA_rho_le_sq {ρ : ℝ} (hρ : 1 ≤ ρ) : ρ ≤ ρ ^ 2 := by nlinarith

/-- (long) -/
theorem iterationsA_ineq_long {b ρ e T cB K : ℝ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ) (hK : 1 ≤ K) (hcB : 0 ≤ cB)
    (hT : 0 ≤ T) (he : 0 ≤ e) (hT1 : T * b ^ 6 ≤ cB) (hT2 : T * ρ ^ 2 * b ^ 7 ≤ cB * K)
    {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N + 1) :
    1 + T * (b ^ 6 + ρ ^ (m - 1) * (b * e)) ≤ (1 + cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
  have hb6 : 1 ≤ b ^ 6 := one_le_pow₀ hb
  have hb0 : 0 ≤ b := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρN : ρ ^ (m - 1) ≤ ρ ^ N := pow_le_pow_right₀ hρ (by omega)
  have hρN' : ρ ^ N = ρ ^ (N - 1) * ρ := by rw [← pow_succ]; congr 1; omega
  have hpe : 0 ≤ ρ ^ (N - 1) * e := by positivity
  have h1 : T * (ρ ^ (m - 1) * (b * e)) ≤ cB * K * (ρ ^ (N - 1) * e) := by
    have h2 : T * ρ * b ≤ cB * K := by
      calc T * ρ * b ≤ T * ρ ^ 2 * b ^ 7 := by
            have : ρ ≤ ρ ^ 2 := iterationsA_rho_le_sq hρ
            have : b ≤ b ^ 7 := by
              calc b = b ^ 1 := (pow_one b).symm
                _ ≤ b ^ 7 := pow_le_pow_right₀ hb (by norm_num)
            have h3 : T * ρ ≤ T * ρ ^ 2 := mul_le_mul_of_nonneg_left (iterationsA_rho_le_sq hρ) hT
            exact mul_le_mul h3 this hb0 (by positivity)
        _ ≤ cB * K := hT2
    calc T * (ρ ^ (m - 1) * (b * e)) ≤ T * (ρ ^ N * (b * e)) := by
          gcongr
      _ = (T * ρ * b) * (ρ ^ (N - 1) * e) := by rw [hρN']; ring
      _ ≤ (cB * K) * (ρ ^ (N - 1) * e) := mul_le_mul_of_nonneg_right h2 hpe
  have h4 : 1 + T * b ^ 6 ≤ (1 + cB) * b ^ 6 := by nlinarith
  calc 1 + T * (b ^ 6 + ρ ^ (m - 1) * (b * e)) = (1 + T * b ^ 6) + T * (ρ ^ (m - 1) * (b * e)) := by ring
    _ ≤ (1 + cB) * b ^ 6 + cB * K * (ρ ^ (N - 1) * e) := add_le_add h4 h1
    _ ≤ (1 + cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
        have hk : 0 ≤ cB * K := by positivity
        nlinarith [mul_nonneg hk (sq_nonneg b), mul_nonneg hcB hpe, mul_nonneg hk hpe, mul_nonneg hcB (show 0 ≤ b ^ 6 by positivity), mul_nonneg hk (show 0 ≤ b ^ 6 by positivity)]


/-- (quad) -/
theorem iterationsA_ineq_quad {b ρ e T cB K : ℝ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ) (hK : 1 ≤ K) (hcB : 0 ≤ cB)
    (hT : 0 ≤ T) (he : 0 ≤ e) (he7 : e ≤ b ^ 7) (hT1 : T * b ^ 6 ≤ cB) (hT2 : T * ρ ^ 2 * b ^ 7 ≤ cB * K)
    {N m j : ℕ} (_hj : 1 ≤ j) (hm : 1 ≤ m) (hjN : j ≤ N) (hmN : m ≤ N) (hjm : j + m = N + 2)
    {xj xa xb : ℝ} (hxj : xj ≤ 1 + (b ^ 6 + ρ ^ (j - 1) * e)) (hxj0 : 0 ≤ xj)
    (hxa : xa ≤ 1 + T * (b ^ 6 + ρ ^ (m - 1) * e))
    (hxb : xb ≤ 1 + T * (b ^ 6 + ρ ^ (m - 1) * e)) (hxb0 : 0 ≤ xb) :
    xj * (xa * xb) ^ (1 / 2 : ℝ) ≤ (2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
  have hb6 : 1 ≤ b ^ 6 := one_le_pow₀ hb
  have hb0 : 0 ≤ b := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  set X : ℝ := 1 + T * (b ^ 6 + ρ ^ (m - 1) * e) with hX
  have hX0 : 0 ≤ X := by positivity
  have hsq : (xa * xb) ^ (1 / 2 : ℝ) ≤ X := by
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sqrt_le_iff]
    refine ⟨hX0, ?_⟩
    calc xa * xb ≤ X * X := mul_le_mul hxa hxb hxb0 hX0
      _ = X ^ 2 := (sq X).symm
  have hρj : ρ ^ (j - 1) ≤ ρ ^ (N - 1) := pow_le_pow_right₀ hρ (by omega)
  have hρm : ρ ^ (m - 1) ≤ ρ ^ (N - 1) := pow_le_pow_right₀ hρ (by omega)
  have hpe : 0 ≤ ρ ^ (N - 1) * e := by positivity
  have hρN : ρ ^ (m - 1) * ρ ^ (j - 1) = ρ ^ (N - 1) * ρ := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  have hTρe : T * ρ * e ≤ cB * K := by
    calc T * ρ * e ≤ T * ρ ^ 2 * b ^ 7 := by
          have h3 : T * ρ ≤ T * ρ ^ 2 := mul_le_mul_of_nonneg_left (iterationsA_rho_le_sq hρ) hT
          exact mul_le_mul h3 he7 he (by positivity)
      _ ≤ cB * K := hT2
  have hXle : X ≤ (1 + cB) + T * (ρ ^ (m - 1) * e) := by
    have : T * b ^ 6 ≤ cB := hT1
    rw [hX]; nlinarith
  have hxj' : xj ≤ 2 * b ^ 6 + ρ ^ (j - 1) * e := by linarith
  have hY0 : 0 ≤ (1 + cB) + T * (ρ ^ (m - 1) * e) := by positivity
  have hxjb : xj * X ≤ (2 * b ^ 6 + ρ ^ (j - 1) * e) * ((1 + cB) + T * (ρ ^ (m - 1) * e)) :=
    mul_le_mul hxj' hXle hX0 (by positivity)
  have hpm : 0 ≤ ρ ^ (m - 1) * e := by positivity
  have hpj : 0 ≤ ρ ^ (j - 1) * e := by positivity
  have hterm1 : 2 * b ^ 6 * (T * (ρ ^ (m - 1) * e)) ≤ 2 * cB * (ρ ^ (N - 1) * e) := by
    calc 2 * b ^ 6 * (T * (ρ ^ (m - 1) * e)) = 2 * (T * b ^ 6) * (ρ ^ (m - 1) * e) := by ring
      _ ≤ 2 * cB * (ρ ^ (N - 1) * e) := by
          have h5 : ρ ^ (m - 1) * e ≤ ρ ^ (N - 1) * e := mul_le_mul_of_nonneg_right hρm he
          have : 2 * (T * b ^ 6) ≤ 2 * cB := by linarith
          exact mul_le_mul this h5 hpm (by positivity)
  have hterm2 : ρ ^ (j - 1) * e * (T * (ρ ^ (m - 1) * e)) ≤ cB * K * (ρ ^ (N - 1) * e) := by
    calc ρ ^ (j - 1) * e * (T * (ρ ^ (m - 1) * e))
        = (T * ρ * e) * (ρ ^ (N - 1) * e) := by
          have : ρ ^ (j - 1) * ρ ^ (m - 1) = ρ ^ (N - 1) * ρ := by
            rw [← pow_add, ← pow_succ]; congr 1; omega
          calc ρ ^ (j - 1) * e * (T * (ρ ^ (m - 1) * e)) = T * e * e * (ρ ^ (j - 1) * ρ ^ (m - 1)) := by ring
            _ = (T * ρ * e) * (ρ ^ (N - 1) * e) := by rw [this]; ring
      _ ≤ (cB * K) * (ρ ^ (N - 1) * e) := mul_le_mul_of_nonneg_right hTρe (by positivity)
  have hterm3 : (1 + cB) * (ρ ^ (j - 1) * e) ≤ (1 + cB) * (ρ ^ (N - 1) * e) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρj he) (by positivity)
  calc xj * (xa * xb) ^ (1 / 2 : ℝ) ≤ xj * X := mul_le_mul_of_nonneg_left hsq hxj0
    _ ≤ (2 * b ^ 6 + ρ ^ (j - 1) * e) * ((1 + cB) + T * (ρ ^ (m - 1) * e)) := hxjb
    _ = 2 * (1 + cB) * b ^ 6 + 2 * b ^ 6 * (T * (ρ ^ (m - 1) * e)) + (1 + cB) * (ρ ^ (j - 1) * e)
          + ρ ^ (j - 1) * e * (T * (ρ ^ (m - 1) * e)) := by ring
    _ ≤ 2 * (1 + cB) * b ^ 6 + 2 * cB * (ρ ^ (N - 1) * e) + (1 + cB) * (ρ ^ (N - 1) * e)
          + cB * K * (ρ ^ (N - 1) * e) := by gcongr
    _ ≤ (2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
        have hk : 0 ≤ cB * K := by positivity
        nlinarith [mul_nonneg hcB (show 0 ≤ b ^ 6 by positivity), mul_nonneg hk hpe, mul_nonneg hcB hpe]


/-- (chain) -/
theorem iterationsA_ineq_chain {b ρ e T cB cv K w x y : ℝ} {N p : ℕ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ)
    (hK : 1 ≤ K) (hcB : 0 ≤ cB) (hcv : 1 ≤ cv) (hT : 0 ≤ T) (he : 0 ≤ e) (hρK : ρ ^ 2 ≤ K * b)
    (hT2 : T * ρ ^ 2 * b ^ 7 ≤ cB * K) (hw1 : 1 ≤ w) (hwb : w ≤ b) (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 + cv * b ^ 8 * ((1 + cB) + T * ρ ^ N * (b * e)) ^ 2)
    (hy0 : 0 ≤ y) (hy : y ≤ (2 * ρ) ^ (4 * p)) :
    cv * w * (x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ)))) ≤
      (2 * cv * K + 2 * cv ^ 2 * (1 + cB) * K + 2 * cv ^ 2 * cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
  have hb0 : 0 ≤ b := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hcv0 : 0 ≤ cv := by linarith
  set Z : ℝ := (1 + cB) + T * ρ ^ N * (b * e) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hxs : x ^ (1 / 2 : ℝ) ≤ 1 + cv * b ^ 4 * Z := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : cv * b ^ 8 * Z ^ 2 ≤ 2 * (cv * b ^ 4 * Z) + (cv * b ^ 4 * Z) ^ 2 := by
      have h1 : 0 ≤ cv * b ^ 4 * Z := by positivity
      have h2 : cv * b ^ 8 * Z ^ 2 ≤ (cv * b ^ 4 * Z) ^ 2 := by
        have : (cv * b ^ 4 * Z) ^ 2 = cv * (cv * b ^ 8 * Z ^ 2) := by ring
        rw [this]
        have h3 : 0 ≤ cv * b ^ 8 * Z ^ 2 := by positivity
        nlinarith
      linarith
    nlinarith
  have hp' : (1 : ℝ) / (4 * (p : ℝ)) = (((4 * p : ℕ) : ℝ))⁻¹ := by
    push_cast; rw [one_div]
  have hys : y ^ (1 / (4 * (p : ℝ))) ≤ 2 * ρ := by
    have h1 : y ^ (1 / (4 * (p : ℝ))) ≤ ((2 * ρ) ^ (4 * p)) ^ (1 / (4 * (p : ℝ))) :=
      Real.rpow_le_rpow hy0 hy (by positivity)
    rw [hp'] at h1 ⊢
    refine h1.trans (le_of_eq ?_)
    exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
  have hx1 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0 _
  have hy1 : 0 ≤ y ^ (1 / (4 * (p : ℝ))) := Real.rpow_nonneg hy0 _
  have hρb : ρ ≤ K * b := hρK.trans' (by nlinarith)
  have hρ2 : ρ ≤ ρ ^ 2 := by nlinarith
  have hwρ : w * ρ ≤ K * b ^ 2 := by
    calc w * ρ ≤ b * (K * b) := mul_le_mul hwb hρb hρ0 hb0
      _ = K * b ^ 2 := by ring
  have hb2 : b ^ 2 ≤ b ^ 6 := pow_le_pow_right₀ hb (by norm_num)
  have hb6 : 1 ≤ b ^ 6 := one_le_pow₀ hb
  have hb67 : b ^ 6 ≤ b ^ 7 := pow_le_pow_right₀ hb (by norm_num)
  have hpe : 0 ≤ ρ ^ (N - 1) * e := by positivity
  have hρN : ρ ^ N = ρ ^ (N - 1) * ρ := by rw [← pow_succ]; congr 1; omega
  -- the three pieces
  have hP1 : cv * w * ρ ≤ cv * K * b ^ 6 := by
    calc cv * w * ρ = cv * (w * ρ) := by ring
      _ ≤ cv * (K * b ^ 2) := mul_le_mul_of_nonneg_left hwρ hcv0
      _ ≤ cv * (K * b ^ 6) := by gcongr
      _ = cv * K * b ^ 6 := by ring
  have hP2 : cv * w * ρ * (b ^ 4 * (1 + cB)) ≤ cv * K * (1 + cB) * b ^ 6 := by
    have h1 : w * ρ * b ^ 4 ≤ K * b ^ 2 * b ^ 4 := mul_le_mul_of_nonneg_right hwρ (by positivity)
    calc cv * w * ρ * (b ^ 4 * (1 + cB)) = cv * (1 + cB) * (w * ρ * b ^ 4) := by ring
      _ ≤ cv * (1 + cB) * (K * b ^ 2 * b ^ 4) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = cv * K * (1 + cB) * b ^ 6 := by ring
  have hP3 : cv * w * ρ * (b ^ 4 * (T * ρ ^ N * (b * e))) ≤ cv * (cB * K) * (ρ ^ (N - 1) * e) := by
    have h1 : cv * w * ρ * (b ^ 4 * (T * ρ ^ N * (b * e))) = (cv * w * b ^ 5) * (T * ρ ^ 2 * ρ ^ (N - 1) * e) := by
      rw [hρN]; ring
    have h2 : w * b ^ 5 ≤ b ^ 6 := by
      calc w * b ^ 5 ≤ b * b ^ 5 := mul_le_mul_of_nonneg_right hwb (by positivity)
        _ = b ^ 6 := by ring
    have h3 : T * ρ ^ 2 * b ^ 6 ≤ cB * K := by
      calc T * ρ ^ 2 * b ^ 6 ≤ T * ρ ^ 2 * b ^ 7 := by gcongr
        _ ≤ cB * K := hT2
    calc cv * w * ρ * (b ^ 4 * (T * ρ ^ N * (b * e)))
        = cv * (ρ ^ (N - 1) * e) * (T * ρ ^ 2 * (w * b ^ 5)) := by rw [hρN]; ring
      _ ≤ cv * (ρ ^ (N - 1) * e) * (T * ρ ^ 2 * b ^ 6) := by
          gcongr
      _ ≤ cv * (ρ ^ (N - 1) * e) * (cB * K) := by gcongr
      _ = cv * (cB * K) * (ρ ^ (N - 1) * e) := by ring
  calc cv * w * (x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ))))
      ≤ cv * w * ((1 + cv * b ^ 4 * Z) * (2 * ρ)) := by
        gcongr
    _ = 2 * (cv * w * ρ) + 2 * cv * (cv * w * ρ * (b ^ 4 * (1 + cB))) + 2 * cv * (cv * w * ρ * (b ^ 4 * (T * ρ ^ N * (b * e)))) := by
        rw [hZ]; ring
    _ ≤ 2 * (cv * K * b ^ 6) + 2 * cv * (cv * K * (1 + cB) * b ^ 6) + 2 * cv * (cv * (cB * K) * (ρ ^ (N - 1) * e)) := by
        gcongr
    _ ≤ (2 * cv * K + 2 * cv ^ 2 * (1 + cB) * K + 2 * cv ^ 2 * cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
        have hk : 0 ≤ K := by linarith
        nlinarith [mul_nonneg (mul_nonneg hcv0 hk) (show 0 ≤ b ^ 6 by positivity),
          mul_nonneg (mul_nonneg (mul_nonneg hcv0 hcv0) (show 0 ≤ 1 + cB by positivity)) (mul_nonneg hk (show 0 ≤ b ^ 6 by positivity)),
          mul_nonneg (mul_nonneg (mul_nonneg hcv0 hcv0) hcB) (mul_nonneg hk hpe),
          mul_nonneg (mul_nonneg hcv0 hk) hpe, mul_nonneg (mul_nonneg (mul_nonneg hcv0 hcv0) (show 0 ≤ 1 + cB by positivity)) (mul_nonneg hk hpe)]


/-- The sum of the `Ξ^{(𝓛-𝒦)}` controls: `∑_{m=1}^{N-1} XLK m ≤ 2 N Ψ(N,k)` (`≺` envelope `1 + Ψ(m,k)`). -/
private theorem iterationsA_sum_XLK {b ρ e : ℝ} {N : ℕ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ) (he : 0 ≤ e)
    {XLK : ℕ → ℝ} (h : ∀ m, 1 ≤ m → m + 1 ≤ N → XLK m ≤ 1 + (b ^ 6 + ρ ^ (m - 1) * e)) :
    ∑ m ∈ Finset.Icc 1 (N - 1), XLK m ≤ (2 * (N : ℝ)) * (b ^ 6 + ρ ^ (N - 1) * e) := by
  have hb6 : 1 ≤ b ^ 6 := one_le_pow₀ hb
  have hpe : 0 ≤ ρ ^ (N - 1) * e := by positivity
  have hterm : ∀ m ∈ Finset.Icc 1 (N - 1), XLK m ≤ 2 * (b ^ 6 + ρ ^ (N - 1) * e) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have h1 := h m hm.1 (by omega)
    have h2 : ρ ^ (m - 1) * e ≤ ρ ^ (N - 1) * e :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hρ (by omega)) he
    linarith
  calc ∑ m ∈ Finset.Icc 1 (N - 1), XLK m ≤ (Finset.Icc 1 (N - 1)).card • (2 * (b ^ 6 + ρ ^ (N - 1) * e)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((N - 1 : ℕ) : ℝ) * (2 * (b ^ 6 + ρ ^ (N - 1) * e)) := by
        have hcard : (Finset.Icc 1 (N - 1)).card = N - 1 := by rw [Nat.card_Icc]; omega
        rw [hcard, nsmul_eq_mul]
    _ ≤ (2 * (N : ℝ)) * (b ^ 6 + ρ ^ (N - 1) * e) := by
        have h1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
        have h0 : 0 ≤ b ^ 6 + ρ ^ (N - 1) * e := by positivity
        nlinarith

/-- The sum of the `Ξ^{(𝓛)}` controls over `m ∈ [N-1, N+1]` (`iterationsA_ineq_long`). -/
private theorem iterationsA_sum_XL {b ρ e T cB K : ℝ} {N : ℕ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ) (hK : 1 ≤ K)
    (hcB : 0 ≤ cB) (hT : 0 ≤ T) (he : 0 ≤ e) (hT1 : T * b ^ 6 ≤ cB) (hT2 : T * ρ ^ 2 * b ^ 7 ≤ cB * K)
    (hN : 2 ≤ N) {XL : ℕ → ℝ}
    (h : ∀ m, 1 ≤ m → m ≤ N + 1 → XL m ≤ 1 + T * (b ^ 6 + ρ ^ (m - 1) * (b * e))) :
    ∑ m ∈ Finset.Icc (N - 1) (N + 1), XL m ≤ (3 * (1 + cB + cB * K)) * (b ^ 6 + ρ ^ (N - 1) * e) := by
  have hterm : ∀ m ∈ Finset.Icc (N - 1) (N + 1), XL m ≤ (1 + cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact (h m (by omega) hm.2).trans
      (iterationsA_ineq_long hb hρ hK hcB hT he hT1 hT2 (N := N) (m := m) (by omega) (by omega) hm.2)
  calc ∑ m ∈ Finset.Icc (N - 1) (N + 1), XL m
      ≤ (Finset.Icc (N - 1) (N + 1)).card • ((1 + cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (3 * (1 + cB + cB * K)) * (b ^ 6 + ρ ^ (N - 1) * e) := by
        have hcard : (Finset.Icc (N - 1) (N + 1)).card = 3 := by rw [Nat.card_Icc]; omega
        rw [hcard, nsmul_eq_mul]; push_cast; ring

/-- `STn12 m` has both components in `[1, m]` for `m ≥ 3`. -/
private theorem iterationsA_STn12_bounds' {m : ℕ} (hm : 3 ≤ m) :
    (1 ≤ (if m % 2 = 0 then (m - 1, m - 1) else (m - 2, m)).1) ∧
    ((if m % 2 = 0 then (m - 1, m - 1) else (m - 2, m)).1 ≤ m) ∧
    (1 ≤ (if m % 2 = 0 then (m - 1, m - 1) else (m - 2, m)).2) ∧
    ((if m % 2 = 0 then (m - 1, m - 1) else (m - 2, m)).2 ≤ m) := by
  split_ifs <;> simp <;> omega

/-- The quadratic sum of the bootstrap right side: `∑_{m} XLK(N+2-m) (XL a_m XL b_m)^{1/2} ≤ N (2+3cB+cB K) Ψ(N,k)`
(`iterationsA_ineq_quad`); `(a_m, b_m) = (m-1, m-1)` or `(m-2, m)` is `STn12 m`, passed as the function `ab`. -/
private theorem iterationsA_sum_quad {b ρ e T cB K : ℝ} {N : ℕ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ) (hK : 1 ≤ K)
    (hcB : 0 ≤ cB) (hT : 0 ≤ T) (he : 0 ≤ e) (he7 : e ≤ b ^ 7) (hT1 : T * b ^ 6 ≤ cB)
    (hT2 : T * ρ ^ 2 * b ^ 7 ≤ cB * K) {XL XLK : ℕ → ℝ} {ab : ℕ → ℕ × ℕ}
    (hab : ∀ m, 3 ≤ m → 1 ≤ (ab m).1 ∧ (ab m).1 ≤ m ∧ 1 ≤ (ab m).2 ∧ (ab m).2 ≤ m)
    (hXL1' : ∀ m, 1 ≤ m → m + 1 ≤ N → XL m ≤ 1 + T * (b ^ 6 + ρ ^ (m - 1) * e))
    (hXL0 : ∀ m, 0 ≤ XL m) (hXLK0 : ∀ m, 0 ≤ XLK m)
    (hXLK2 : ∀ m, 1 ≤ m → m + 1 ≤ N → XLK m ≤ 1 + (b ^ 6 + ρ ^ (m - 1) * e)) :
    ∑ m ∈ Finset.Icc ((N + 1) / 2 + 1) (N - 1), XLK (N + 2 - m) * (XL (ab m).1 * XL (ab m).2) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ) * (2 + 3 * cB + cB * K)) * (b ^ 6 + ρ ^ (N - 1) * e) := by
  have hb6 : 1 ≤ b ^ 6 := one_le_pow₀ hb
  have hpe : 0 ≤ ρ ^ (N - 1) * e := by positivity
  have hterm : ∀ m ∈ Finset.Icc ((N + 1) / 2 + 1) (N - 1),
      XLK (N + 2 - m) * (XL (ab m).1 * XL (ab m).2) ^ (1 / 2 : ℝ) ≤
        (2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm3 : 3 ≤ m := by omega
    obtain ⟨ha1, ham, hb1', hbm⟩ := hab m hm3
    have hXa : XL (ab m).1 ≤ 1 + T * (b ^ 6 + ρ ^ (m - 1) * e) := by
      have h1 := hXL1' (ab m).1 ha1 (by omega)
      refine h1.trans ?_
      have h3 : ρ ^ ((ab m).1 - 1) ≤ ρ ^ (m - 1) := pow_le_pow_right₀ hρ (by omega)
      have h2 : T * (ρ ^ ((ab m).1 - 1) * e) ≤ T * (ρ ^ (m - 1) * e) := by gcongr
      linarith
    have hXb : XL (ab m).2 ≤ 1 + T * (b ^ 6 + ρ ^ (m - 1) * e) := by
      have h1 := hXL1' (ab m).2 hb1' (by omega)
      refine h1.trans ?_
      have h3 : ρ ^ ((ab m).2 - 1) ≤ ρ ^ (m - 1) := pow_le_pow_right₀ hρ (by omega)
      have h2 : T * (ρ ^ ((ab m).2 - 1) * e) ≤ T * (ρ ^ (m - 1) * e) := by gcongr
      linarith
    exact iterationsA_ineq_quad hb hρ hK hcB hT he he7 hT1 hT2 (N := N) (m := m) (j := N + 2 - m)
      (by omega) (by omega) (by omega) (by omega) (by omega) (hXLK2 (N + 2 - m) (by omega) (by omega))
      (hXLK0 _) hXa hXb (hXL0 _)
  calc ∑ m ∈ Finset.Icc ((N + 1) / 2 + 1) (N - 1), XLK (N + 2 - m) * (XL (ab m).1 * XL (ab m).2) ^ (1 / 2 : ℝ)
      ≤ (Finset.Icc ((N + 1) / 2 + 1) (N - 1)).card • ((2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((N - 1 + 1 - ((N + 1) / 2 + 1) : ℕ) : ℝ) * ((2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e)) := by
        rw [Nat.card_Icc, nsmul_eq_mul]
    _ ≤ ((N : ℝ) * (2 + 3 * cB + cB * K)) * (b ^ 6 + ρ ^ (N - 1) * e) := by
        have h1 : ((N - 1 + 1 - ((N + 1) / 2 + 1) : ℕ) : ℝ) ≤ N := by
          exact_mod_cast (by omega : N - 1 + 1 - ((N + 1) / 2 + 1) ≤ N)
        have h5 : 0 ≤ (2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) := by
          have : 0 ≤ K := by linarith
          positivity
        calc ((N - 1 + 1 - ((N + 1) / 2 + 1) : ℕ) : ℝ) * ((2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e))
            ≤ (N : ℝ) * ((2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e)) := mul_le_mul_of_nonneg_right h1 h5
          _ = ((N : ℝ) * (2 + 3 * cB + cB * K)) * (b ^ 6 + ρ ^ (N - 1) * e) := by ring

end RBM.Ind

/-! ## 3. The `Ψ`-calculus -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss


/-- `Ψ` in the variables `b = A^{1/8}`, `e = A^{1-k/8}`: `Ψ(m,k) = b^6 + ρ^{m-1} e`. -/
theorem iterationsA_STPsi_eq {A : ℝ} (hA : 0 ≤ A) (ρ : ℝ) (m k : ℕ) :
    STPsi A ρ m k = (A ^ (1 / 8 : ℝ)) ^ 6 + ρ ^ (m - 1) * A ^ (1 - (k : ℝ) / 8) := by
  unfold STPsi
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
  norm_num

/-- `A^{1-(k-1)/8} = A^{1/8} A^{1-k/8}` for `k ≥ 1`. -/
theorem iterationsA_rpow_pred {A : ℝ} (hA : 0 < A) {k : ℕ} (hk : 1 ≤ k) :
    A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) = A ^ (1 / 8 : ℝ) * A ^ (1 - (k : ℝ) / 8) := by
  rw [← Real.rpow_add hA]
  congr 1
  rw [Nat.cast_sub hk]
  push_cast
  ring

/-- `Ψ(m,k-1) = b^6 + ρ^{m-1} b e`. -/
theorem iterationsA_STPsi_pred {A : ℝ} (hA : 0 < A) (ρ : ℝ) (m : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    STPsi A ρ m (k - 1) = (A ^ (1 / 8 : ℝ)) ^ 6 + ρ ^ (m - 1) * (A ^ (1 / 8 : ℝ) * A ^ (1 - (k : ℝ) / 8)) := by
  rw [iterationsA_STPsi_eq hA.le, iterationsA_rpow_pred hA hk]

theorem iterationsA_STPsi_nonneg {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (m k : ℕ) : 0 ≤ STPsi A ρ m k := by
  unfold STPsi; positivity

theorem iterationsA_one_le_STPsi {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (m k : ℕ) : 1 ≤ STPsi A ρ m k := by
  have h1 : 1 ≤ A ^ (3 / 4 : ℝ) := Real.one_le_rpow hA (by norm_num)
  have h2 : 0 ≤ ρ ^ (m - 1) * A ^ (1 - (k : ℝ) / 8) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ A) (1 - (k : ℝ) / 8)
    positivity
  unfold STPsi; linarith

theorem iterationsA_STPsi_mono_n {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 1 ≤ ρ) {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    STPsi A ρ m k ≤ STPsi A ρ n k := by
  unfold STPsi
  have := Real.rpow_nonneg hA (1 - (k : ℝ) / 8)
  gcongr

theorem iterationsA_STPsi_anti_k {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (m : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    STPsi A ρ m k ≤ STPsi A ρ m (k - 1) := by
  unfold STPsi
  have hA0 : 0 < A := by linarith
  have : A ^ (1 - (k : ℝ) / 8) ≤ A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by
    apply Real.rpow_le_rpow_of_exponent_le hA
    rw [Nat.cast_sub hk]; push_cast; linarith
  have h2 : 0 ≤ ρ ^ (m - 1) := by positivity
  gcongr


end RBM.Gauss.Sizes

/-! ## 4. The deterministic assembly: `STbootRHS ≤ C Ψ(n,k)`

`lem:iterations`, proof `3_5:1772-1864`.  The controls `Ξ^{(𝓛)}_m`, `Ξ^{(𝓛-𝒦)}_m` enter `STbootRHS` through the
functions `XL`, `XLK`; the hypotheses are the envelopes the paper chooses (`3_5:1794-1808`): `Ξ^{(𝓛-𝒦)}_m ≤ 1 + Ψ(m,k)`
for `m ≤ n-1`; `Ξ^{(𝓛)}_m ≤ 1 + T Ψ(m,l)` (`T ≥ W^{-d}B_{v,0}`, `(rela_XILXILK)`) with `l = k` for `m ≤ n-1` and `l = k-1`
for `m ≤ n+1`; `Ξ^{(𝓛)}_{2n-1} ≤ 1 + cv A Z²` (`(auskoppw2)`, `3_5:1857-1862`); `Ξ^{(𝓛)}_{4p} ≤ 1 + ρ^{4p-1}` (the a priori
bound `(sef8w483r324)`, `3_5:1391`).  Scale facts: `ρ = η_s/η_u ≥ 1`, `ρ² ≤ K A^{1/8}` (`3_5:1422-1431`: `ρ ≤ A^{𝔠d}`, `𝔠d ≤ 1/100`),
`T A^{3/4} ≤ cB`, `T ρ² A^{7/8} ≤ cB K` (`B_v ≤ cB A^{-1+δ}`, `ρ² A^δ ≤ K A^{1/8}`), `W^{-d} B_{u,0} ≥ (cv A)⁻¹`.  The
constants `C` depend on `(cB, cv, K, N)` only. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The chain bound `(xiu2n+2psi)`** (`3_5:1785`, proof `3_5:1818-1864`), deterministic and dimension free, in the form of the
first term of `STbootRHS` (`(am;asoi222)`, `3_5:1366`): `B_u^{-1/(4p)} Ξ̂_{2N-1}^{1/2} Ξ̂_{4p}^{1/(4p)} ≤ C Ψ(N,k)` for the
controls `Ξ̂_{2N-1} ≤ x ≤ 1 + cv A Z²` (`(auskoppw2)`, `Z = 1 + cB + T ρ^N A^{1-(k-1)/8}`) and `Ξ̂_{4p} ≤ y ≤ 1 + ρ^{4p-1}` (the a
priori bound), `(cv A)⁻¹ ≤ B_u` (`B_u⁻¹ ≤ cv A`), `p ≥ 2` (paper `p ≥ 4`), under the scale facts of `IterationsAScale`.  The
constant depends on `(cB, cv, K)` only. -/
theorem iterationsA_chain_term (cB cv K : ℝ) (hcB : 0 ≤ cB) (hcv : 1 ≤ cv) (hK : 1 ≤ K) (N k : ℕ)
    (hN : 2 ≤ N) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A ρ T Bu x y : ℝ) (p : ℕ), 2 ≤ p → 1 ≤ A → 1 ≤ ρ →
      ρ ^ 2 ≤ K * A ^ (1 / 8 : ℝ) → 0 ≤ T → T * ρ ^ 2 * A ^ (7 / 8 : ℝ) ≤ cB * K → (cv * A)⁻¹ ≤ Bu →
      1 ≤ x → x ≤ 1 + cv * A * ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 →
      1 ≤ y → y ≤ 1 + ρ ^ (4 * p - 1) →
      Bu ^ (-(1 : ℝ) / (4 * (p : ℝ))) * x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ))) ≤ C * STPsi A ρ N k := by
  have hKpos : 0 < K := by linarith
  set C1 : ℝ := 2 * cv * K + 2 * cv ^ 2 * (1 + cB) * K + 2 * cv ^ 2 * cB * K with hC1
  have hC1p : 0 < C1 := by rw [hC1]; positivity
  refine ⟨C1, hC1p, ?_⟩
  intro A ρ T Bu x y p hp hA hρ hρK hT hT2 hBu hx1 hxc hy1 hy4p
  have hA0 : 0 < A := by linarith
  set b : ℝ := A ^ (1 / 8 : ℝ) with hb
  set e : ℝ := A ^ (1 - (k : ℝ) / 8) with heq
  have hb1 : 1 ≤ b := Real.one_le_rpow hA (by norm_num)
  have he0 : 0 ≤ e := Real.rpow_nonneg hA0.le _
  have hA78 : A ^ (7 / 8 : ℝ) = b ^ 7 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have hA8 : A = b ^ 8 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have hbe : A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) = b * e := iterationsA_rpow_pred hA0 hk
  rw [hA78] at hT2
  have hρK' : ρ ^ 2 ≤ K * b := hρK
  rw [iterationsA_STPsi_eq hA0.le ρ N k]
  -- the chain term
  have hz : -(1 : ℝ) / (4 * (p : ℝ)) ≤ 0 := by
    have : (0 : ℝ) < 4 * (p : ℝ) := by
      have : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
      positivity
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le
  have hcvA : 0 < cv * A := by positivity
  set w : ℝ := A ^ (1 / (4 * (p : ℝ))) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow hA (by positivity)
  have hwb : w ≤ b := by
    rw [hw, hb]
    apply Real.rpow_le_rpow_of_exponent_le hA
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hBw : Bu ^ (-(1 : ℝ) / (4 * (p : ℝ))) ≤ cv * w := by
    have h1 : Bu ^ (-(1 : ℝ) / (4 * (p : ℝ))) ≤ ((cv * A)⁻¹) ^ (-(1 : ℝ) / (4 * (p : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos (inv_pos.2 hcvA) hBu hz
    have h2 : ((cv * A)⁻¹) ^ (-(1 : ℝ) / (4 * (p : ℝ))) = (cv * A) ^ (1 / (4 * (p : ℝ))) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_mul hcvA.le]
      congr 1; ring
    have h3 : (cv * A) ^ (1 / (4 * (p : ℝ))) = cv ^ (1 / (4 * (p : ℝ))) * w := by
      rw [hw, Real.mul_rpow (by linarith) hA0.le]
    have h4 : cv ^ (1 / (4 * (p : ℝ))) ≤ cv := by
      apply Real.rpow_le_self_of_one_le hcv
      rw [div_le_one (by positivity)]
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    rw [h2, h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h4 (by linarith))
  have hx0 : 0 ≤ x := by linarith [hx1]
  have hy0 : 0 ≤ y := by linarith [hy1]
  have hxle : x ≤ 1 + cv * b ^ 8 * ((1 + cB) + T * ρ ^ N * (b * e)) ^ 2 := by
    rw [hbe, hA8] at hxc
    exact hxc
  have hyle : y ≤ (2 * ρ) ^ (4 * p) := by
    refine hy4p.trans ?_
    have h2 : (2 : ℝ) ≤ 2 ^ (4 * p) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : ρ ^ (4 * p - 1) ≤ ρ ^ (4 * p) := pow_le_pow_right₀ hρ (by omega)
    have h4 : 1 ≤ ρ ^ (4 * p - 1) := one_le_pow₀ hρ
    have h5 : 0 ≤ ρ ^ (4 * p) := by positivity
    rw [mul_pow]
    calc 1 + ρ ^ (4 * p - 1) ≤ 2 * ρ ^ (4 * p) := by linarith
      _ ≤ 2 ^ (4 * p) * ρ ^ (4 * p) := mul_le_mul_of_nonneg_right h2 h5
  have hchain := RBM.Ind.iterationsA_ineq_chain (b := b) (ρ := ρ) (e := e) (T := T) (cB := cB) (cv := cv)
    (K := K) (w := w) (x := x) (y := y) (N := N) (p := p) hb1 hρ hK hcB hcv hT he0 hρK'
    hT2 hw1 hwb (by omega) (by omega) hx0 hxle hy0 hyle
  have ht1 : Bu ^ (-(1 : ℝ) / (4 * (p : ℝ))) * x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ))) ≤
      C1 * (b ^ 6 + ρ ^ (N - 1) * e) := by
    have hnn : 0 ≤ x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ))) :=
      mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hy0 _)
    calc Bu ^ (-(1 : ℝ) / (4 * (p : ℝ))) * x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ)))
        = Bu ^ (-(1 : ℝ) / (4 * (p : ℝ))) * (x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ)))) := by ring
      _ ≤ (cv * w) * (x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ)))) :=
          mul_le_mul_of_nonneg_right hBw hnn
      _ ≤ C1 * (b ^ 6 + ρ ^ (N - 1) * e) := hchain
  exact ht1

/-- **The bootstrap right side** (deterministic, dimension free): under the envelopes above, `STbootRHS 1 XL XLK B_u N p ≤ C Ψ(N,k)`:
the first term is the chain bound `iterationsA_chain_term` (`(xiu2n+2psi)`), and the three sums are `≲ Ψ(N,k)` by
`iterationsA_ineq_long`, `iterationsA_ineq_quad` (`p ≥ 2`; paper `p ≥ 4`). -/
theorem iterationsA_boot_bound (cB cv K : ℝ) (hcB : 0 ≤ cB) (hcv : 1 ≤ cv) (hK : 1 ≤ K) (N k : ℕ)
    (hN : 2 ≤ N) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A ρ T Bu : ℝ) (p : ℕ) (XL XLK : ℕ → ℝ), 2 ≤ p → 1 ≤ A → 1 ≤ ρ →
      ρ ^ 2 ≤ K * A ^ (1 / 8 : ℝ) → 0 ≤ T → T * A ^ (3 / 4 : ℝ) ≤ cB →
      T * ρ ^ 2 * A ^ (7 / 8 : ℝ) ≤ cB * K → (cv * A)⁻¹ ≤ Bu →
      (∀ m, 1 ≤ m → m ≤ N + 1 → XL m ≤ 1 + T * STPsi A ρ m (k - 1)) →
      (∀ m, 1 ≤ m → m + 1 ≤ N → XL m ≤ 1 + T * STPsi A ρ m k) →
      (∀ m, 1 ≤ XL m) →
      XL (2 * N - 1) ≤ 1 + cv * A * ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 →
      XL (4 * p) ≤ 1 + ρ ^ (4 * p - 1) →
      (∀ m, 1 ≤ XLK m) → (∀ m, 1 ≤ m → m + 1 ≤ N → XLK m ≤ 1 + STPsi A ρ m k) →
      STbootRHS 1 XL XLK Bu N p ≤ C * STPsi A ρ N k := by
  obtain ⟨C1, hC1p, hC1⟩ := iterationsA_chain_term cB cv K hcB hcv hK N k hN hk
  have hKpos : 0 < K := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨C1 + 2 * (N : ℝ) + 3 * (1 + cB + cB * K) + (N : ℝ) * (2 + 3 * cB + cB * K), by positivity, ?_⟩
  intro A ρ T Bu p XL XLK hp hA hρ hρK hT hT1 hT2 hBu hXL1 hXL1' hXL0 hXLc hXL4p hXLK0 hXLK2
  have hchain := hC1 A ρ T Bu (XL (2 * N - 1)) (XL (4 * p)) p hp hA hρ hρK hT hT2 hBu (hXL0 _) hXLc (hXL0 _) hXL4p
  have hA0 : 0 < A := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  set b : ℝ := A ^ (1 / 8 : ℝ) with hb
  set e : ℝ := A ^ (1 - (k : ℝ) / 8) with heq
  have hb1 : 1 ≤ b := Real.one_le_rpow hA (by norm_num)
  have he0 : 0 ≤ e := Real.rpow_nonneg hA0.le _
  have hA34 : A ^ (3 / 4 : ℝ) = b ^ 6 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have hA78 : A ^ (7 / 8 : ℝ) = b ^ 7 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have hA8 : A = b ^ 8 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have he7 : e ≤ b ^ 7 := by
    rw [← hA78]
    apply Real.rpow_le_rpow_of_exponent_le hA
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hPsik : ∀ m, STPsi A ρ m k = b ^ 6 + ρ ^ (m - 1) * e := fun m => iterationsA_STPsi_eq hA0.le ρ m k
  have hPsik1 : ∀ m, STPsi A ρ m (k - 1) = b ^ 6 + ρ ^ (m - 1) * (b * e) := fun m =>
    iterationsA_STPsi_pred hA0 ρ m hk
  have hbe : A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) = b * e := iterationsA_rpow_pred hA0 hk
  rw [hA34] at hT1
  rw [hA78] at hT2
  have hρK' : ρ ^ 2 ≤ K * b := hρK
  have hb6 : 1 ≤ b ^ 6 := one_le_pow₀ hb1
  have hpe : 0 ≤ ρ ^ (N - 1) * e := by positivity
  rw [hPsik N]
  rw [hPsik N] at hchain
  -- the sums
  have hs1 := RBM.Ind.iterationsA_sum_XLK (N := N) hb1 hρ he0 (XLK := XLK) (fun m hm1 hm2 => by
    have := hXLK2 m hm1 hm2
    rwa [hPsik] at this)
  have hs2 := RBM.Ind.iterationsA_sum_XL hb1 hρ hK hcB hT he0 hT1 hT2 hN (XL := XL) (fun m hm1 hm2 => by
    have := hXL1 m hm1 hm2
    rwa [hPsik1] at this)
  have hs3 := RBM.Ind.iterationsA_sum_quad (N := N) hb1 hρ hK hcB hT he0 he7 hT1 hT2 (XL := XL) (XLK := XLK)
    (ab := STn12) (fun m hm => RBM.Ind.iterationsA_STn12_bounds' hm)
    (fun m hm1 hm2 => by
      have := hXL1' m hm1 hm2
      rwa [hPsik] at this)
    (fun m => by linarith [hXL0 m]) (fun m => by linarith [hXLK0 m])
    (fun m hm1 hm2 => by
      have := hXLK2 m hm1 hm2
      rwa [hPsik] at this)
  unfold STbootRHS
  have hsum : C1 * (b ^ 6 + ρ ^ (N - 1) * e) + (2 * (N : ℝ) * (b ^ 6 + ρ ^ (N - 1) * e) +
      3 * (1 + cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e) + (N : ℝ) * (2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e)) =
      (C1 + 2 * (N : ℝ) + 3 * (1 + cB + cB * K) + (N : ℝ) * (2 + 3 * cB + cB * K)) * (b ^ 6 + ρ ^ (N - 1) * e) := by ring
  rw [← hsum]
  exact add_le_add hchain (add_le_add (add_le_add hs1 hs2) hs3)

end RBM.Gauss.Sizes

/-! ## 5. `(5.118)` for the model: the odd chain bound

The loops `𝓛^{(m)}_{v,σ,a}` of the flow (`Lloop`) are the list-based loops `loopL` of the Hermitian matrix
`blockMat (seqHflow sz n v ω)` at `z = zt E v`, so `STmaxL` is `RBM.Ind.loopMax` (S1-09 `Split.lean`) and
`STXiL = 1 + loopXi` with the scale `A = (W^{-d}B_{v,0})⁻¹`.  The paper applies `(5.118)` of `[YY_25]`
(`3_5:1841`, `eq:boundtwochains`, factor `ilambda² W^d`) to the two chains of `(suauwiioo1)`; here the scale is the
free parameter `A = B_v⁻¹` of `loopXi_le`, and the Cauchy-Schwarz step `(suauwiioo1)` is `loopMax_odd_sq_le` (6.4). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `max_{σ,a} |𝓛^{(m)}_{v,σ,a}|` is the `loopMax` of the block matrix of the flow matrix. -/
theorem iterationsA_STmaxL_eq (n : ℕ) (E v : ℝ) (m : ℕ) (ω : sz.SeqΩ) :
    STmaxL sz n E v m ω = RBM.Ind.loopMax d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (seqHflow sz n v ω)) (zt E v) m := by
  have : Nonempty ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) := ⟨((fun _ => true), (fun _ => 0))⟩
  unfold STmaxL RBM.Ind.loopMax
  rw [← Finset.sup'_univ_eq_ciSup]
  congr 1
  funext p
  unfold Sizes.Lloop loopFine
  rw [loopM_eq_loopL]
  rfl

/-- `Ξ̂^{(𝓛)}_{v,m} = 1 + Ξ^{(𝓛)}_m` with `Ξ_m = max|𝓛^{(m)}| (B_v⁻¹)^{m-1}` (`RBM.Ind.loopXi`, scale `A = B_v⁻¹`). -/
theorem iterationsA_STXiL_eq (n : ℕ) (E v : ℝ) (m : ℕ) (ω : sz.SeqΩ) :
    STXiL sz n E v m ω = 1 + RBM.Ind.loopXi d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (seqHflow sz n v ω)) (zt E v) (sz.Bctl n v)⁻¹ m := by
  unfold STXiL RBM.Ind.loopXi
  rw [iterationsA_STmaxL_eq, div_eq_mul_inv, inv_pow]

/-- **`(5.118)` and `(6.4)` for the model, the odd chain bound** (`3_5:1832-1850`: `(suauwiioo1)`, `eq:boundtwochains`):
for `N ≥ 3` and `B_{v,0} > 0`,
`Ξ̂^{(𝓛)}_{v,2N-1} ≤ 1 + B_v⁻¹ (Ξ̂_{2l₁} Ξ̂_{2l₂} Ξ̂_{2l₃} Ξ̂_{2l₄})^{1/2}`, `l₁ = ⌈N/2⌉, l₂ = ⌊N/2⌋, l₃ = ⌈(N-1)/2⌉,
l₄ = ⌊(N-1)/2⌋` (natural division below), pointwise in `ω`: `Ξ_{2N-1}² ≤ Ξ_{2N-2} Ξ_{2N}` (6.4) and `Ξ_{2n+2} ≤ Ξ_{2l₁} Ξ_{2l₂} B⁻¹`
(5.118) twice, with `Ξ ≤ Ξ̂`. -/
theorem iterationsA_xiL_odd_le (n : ℕ) {E v : ℝ} (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) {N : ℕ} (hN : 3 ≤ N) :
    STXiL sz n E v (2 * N - 1) ω ≤ 1 + (sz.Bctl n v)⁻¹ *
      ((STXiL sz n E v (2 * ((N + 1) / 2)) ω * STXiL sz n E v (2 * (N / 2)) ω) *
        (STXiL sz n E v (2 * (N / 2)) ω * STXiL sz n E v (2 * ((N - 1) / 2)) ω)) ^ (1 / 2 : ℝ) := by
  set H := blockMat d (sz.L n) (sz.W n) (seqHflow sz n v ω) with hH
  set z := zt E v with hz
  set A' : ℝ := (sz.Bctl n v)⁻¹ with hA'
  have hA'0 : 0 ≤ A' := (inv_pos.2 hB).le
  have hHerm : H.IsHermitian := (seqHflow_isHermitian sz n v ω).submatrix _
  set X : ℕ → ℝ := fun m => RBM.Ind.loopXi d (sz.L n) (sz.W n) H z A' m with hX
  have hXe : ∀ m, STXiL sz n E v m ω = 1 + X m := fun m => iterationsA_STXiL_eq sz n E v m ω
  have hX0 : ∀ m, 0 ≤ X m := fun m => by
    simp only [hX, RBM.Ind.loopXi]
    exact mul_nonneg (RBM.Ind.loopMax_nonneg _) (pow_nonneg hA'0 _)
  -- (6.4)
  have hodd := RBM.Ind.loopMax_odd_sq_le (d := d) (L := sz.L n) (W := sz.W n) (z := z) hHerm (m := N - 1) (by omega)
  rw [show 2 * (N - 1) + 1 = 2 * N - 1 by omega, show 2 * (N - 1) + 2 = 2 * N by omega,
    show 2 * (N - 1) = 2 * N - 2 by omega] at hodd
  have hsq : X (2 * N - 1) ^ 2 ≤ X (2 * N - 2) * X (2 * N) := by
    simp only [hX, RBM.Ind.loopXi]
    have hp : A' ^ (2 * N - 1 - 1) * A' ^ (2 * N - 1 - 1) = A' ^ (2 * N - 2 - 1) * A' ^ (2 * N - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have hmul := mul_le_mul_of_nonneg_right hodd (show 0 ≤ A' ^ (2 * N - 1 - 1) * A' ^ (2 * N - 1 - 1) by positivity)
    calc (RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N - 1) * A' ^ (2 * N - 1 - 1)) ^ 2
        = RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N - 1) ^ 2 * (A' ^ (2 * N - 1 - 1) * A' ^ (2 * N - 1 - 1)) := by ring
      _ ≤ (RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N - 2) * RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N)) *
            (A' ^ (2 * N - 1 - 1) * A' ^ (2 * N - 1 - 1)) := hmul
      _ = (RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N - 2) * A' ^ (2 * N - 2 - 1)) *
            (RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N) * A' ^ (2 * N - 1)) := by
          rw [hp]; ring
  -- (5.118) twice
  have h1 : X (2 * N) ≤ X (2 * ((N + 1) / 2)) * X (2 * (N / 2)) * A' := by
    have := RBM.Ind.loopXi_le (d := d) (L := sz.L n) (W := sz.W n) (z := z) hHerm hA'0 (n := N - 1)
      (l₁ := (N + 1) / 2) (l₂ := N / 2) (by omega) (by omega) (by omega)
    rwa [show 2 * (N - 1) + 2 = 2 * N by omega] at this
  have h2 : X (2 * N - 2) ≤ X (2 * (N / 2)) * X (2 * ((N - 1) / 2)) * A' := by
    have := RBM.Ind.loopXi_le (d := d) (L := sz.L n) (W := sz.W n) (z := z) hHerm hA'0 (n := N - 2)
      (l₁ := N / 2) (l₂ := (N - 1) / 2) (by omega) (by omega) (by omega)
    rwa [show 2 * (N - 2) + 2 = 2 * N - 2 by omega] at this
  have hXX : X (2 * N - 1) ^ 2 ≤ A' ^ 2 * ((X (2 * ((N + 1) / 2)) * X (2 * (N / 2))) * (X (2 * (N / 2)) * X (2 * ((N - 1) / 2)))) := by
    refine hsq.trans ?_
    calc X (2 * N - 2) * X (2 * N)
        ≤ (X (2 * (N / 2)) * X (2 * ((N - 1) / 2)) * A') * (X (2 * ((N + 1) / 2)) * X (2 * (N / 2)) * A') :=
          mul_le_mul h2 h1 (hX0 _) (by have := hX0 (2 * (N / 2)); have := hX0 (2 * ((N - 1) / 2)); positivity)
      _ = A' ^ 2 * ((X (2 * ((N + 1) / 2)) * X (2 * (N / 2))) * (X (2 * (N / 2)) * X (2 * ((N - 1) / 2)))) := by ring
  -- from `Ξ ≤ Ξ̂`
  have hP : (X (2 * ((N + 1) / 2)) * X (2 * (N / 2))) * (X (2 * (N / 2)) * X (2 * ((N - 1) / 2))) ≤
      ((1 + X (2 * ((N + 1) / 2))) * (1 + X (2 * (N / 2)))) * ((1 + X (2 * (N / 2))) * (1 + X (2 * ((N - 1) / 2)))) := by
    have a1 := hX0 (2 * ((N + 1) / 2)); have a2 := hX0 (2 * (N / 2)); have a3 := hX0 (2 * ((N - 1) / 2))
    gcongr <;> linarith
  have hfin : X (2 * N - 1) ≤ A' * (((1 + X (2 * ((N + 1) / 2))) * (1 + X (2 * (N / 2)))) *
      ((1 + X (2 * (N / 2))) * (1 + X (2 * ((N - 1) / 2))))) ^ (1 / 2 : ℝ) := by
    set P : ℝ := ((1 + X (2 * ((N + 1) / 2))) * (1 + X (2 * (N / 2)))) * ((1 + X (2 * (N / 2))) * (1 + X (2 * ((N - 1) / 2)))) with hPdef
    have hP0 : 0 ≤ P := by
      have a1 := hX0 (2 * ((N + 1) / 2)); have a2 := hX0 (2 * (N / 2)); have a3 := hX0 (2 * ((N - 1) / 2))
      rw [hPdef]; positivity
    rw [← Real.sqrt_eq_rpow]
    have hle : X (2 * N - 1) ^ 2 ≤ (A' * Real.sqrt P) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP0]
      exact hXX.trans (mul_le_mul_of_nonneg_left hP (by positivity))
    exact le_of_sq_le_sq hle (by positivity) |>.trans (le_refl _)
  rw [hXe (2 * N - 1), hXe (2 * ((N + 1) / 2)), hXe (2 * (N / 2)), hXe (2 * ((N - 1) / 2))]
  linarith

end RBM.Gauss.Sizes

/-! ## 6. The `≺`-calculus used by the step (`RBM2D Step3.lean:355-376` `step3_trans`, `step3_one_add_inv_mul`)

`≺` is the merged `Prec` (union over the index inside `P`, scale `N = sz.size n`).  Small lemmas on monotone
changes of the two sides, absorption of a constant, powers and `1 + c ξ`; all private. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `ξ ≺ ζ` and `ζ ≤ ζ'` eventually give `ξ ≺ ζ'`. -/
theorem iterationsA_prec_mono_right {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hle] with n hn
  rintro ω ⟨u, hu⟩
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hn u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- `ξ ≤ ξ'` eventually and `ξ' ≺ ζ` give `ξ ≺ ζ`. -/
theorem iterationsA_prec_mono_left {U : ℕ → Type*} {ξ ξ' ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hle : ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ξ' n u ω) (h : sz.Prec ξ' ζ) : sz.Prec ξ ζ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hle] with n hn
  rintro ω ⟨u, hu⟩
  exact ⟨u, lt_of_lt_of_le hu (hn u ω)⟩

/-- A constant factor on the right is absorbed: `ξ ≺ c ζ` gives `ξ ≺ ζ` (`ζ ≥ 0`). -/
theorem iterationsA_prec_absorb (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ℝ} (hζ : ∀ᶠ n in atTop, ∀ u ω, 0 ≤ ζ n u ω)
    (h : sz.Prec ξ (fun n u ω => c * ζ n u ω)) : sz.Prec ξ ζ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hsize.eventually (eventually_le_rpow c (half_pos hτ)), hζ] with n hcN hζn
  rintro ω ⟨u, hu⟩
  refine ⟨u, lt_of_le_of_lt ?_ hu⟩
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : 0 ≤ ζ n u ω := hζn u ω
  calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (c * ζ n u ω)
      ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ n u ω) := by
        gcongr
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]

/-- Powers: `ξ ≺ ζ` gives `ξ^θ ≺ ζ^θ`, `θ > 0`, `ξ, ζ ≥ 0`. -/
theorem iterationsA_prec_rpow {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω, 0 ≤ ξ n u ω) (hζ : ∀ n u ω, 0 ≤ ζ n u ω) {θ : ℝ} (hθ : 0 < θ)
    (h : sz.Prec ξ ζ) : sz.Prec (fun n u ω => ξ n u ω ^ θ) (fun n u ω => ζ n u ω ^ θ) := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / θ, div_pos hτ hθ, Eventually.of_forall fun n => ?_⟩
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hN : 0 ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ τ = (((sz.size n : ℕ) : ℝ) ^ (τ / θ)) ^ θ := by
    rw [← Real.rpow_mul hN]; congr 1; field_simp
  have hu' : (((sz.size n : ℕ) : ℝ) ^ (τ / θ) * ζ n u ω) ^ θ < ξ n u ω ^ θ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hN _) (hζ n u ω), ← h1]
    exact hu
  exact (Real.rpow_lt_rpow_iff (mul_nonneg (Real.rpow_nonneg hN _) (hζ n u ω)) (hξ n u ω) hθ).1 hu'

/-- `ξ ≺ ζ` gives `1 + c ξ ≺ 1 + c ζ` for a deterministic `c ≥ 0` (RBM2D `step3_one_add_inv_mul`, `Step3.lean:375`). -/
theorem iterationsA_prec_one_add_mul (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ∀ n, U n → ℝ} (hc : ∀ n u, 0 ≤ c n u)
    (hξ : ∀ n u ω, 0 ≤ ξ n u ω) (h : sz.Prec ξ ζ) :
    sz.Prec (fun n u ω => 1 + c n u * ξ n u ω) (fun n u ω => 1 + c n u * ζ n u ω) := by
  have h1 : sz.Prec (U := U) (fun n _ _ => (1 : ℝ)) (fun _ _ _ => 1) :=
    StochDomAt.refl hsize fun _ _ _ => zero_le_one
  have h2 : sz.Prec (U := U) (fun n u _ => c n u) (fun n u _ => c n u) :=
    StochDomAt.refl hsize fun n u _ => hc n u
  have h3 := StochDomAt.mul hsize hξ (fun n u _ => hc n u) h2 h
  exact StochDomAt.add hsize h1 h3

private theorem iterationsA_one_le_ratio {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1) : 1 ≤ (1 - s) / (1 - v) := by
  have hxv : 0 < 1 - v := by linarith
  rw [le_div_iff₀ hxv]; linarith

/-- `Bctl ≥ 0`. -/
private theorem iterationsA_Bctl_nonneg (n : ℕ) (u : ℝ) : 0 ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
  positivity


/-! ### The controls of the step (value level)

`XLv A ρ T cB cv N k p m` is the control of `Ξ̂^{(𝓛)}_m` chosen in `3_5:1794-1808`, `3_5:1857-1862` (`Ξ^{(𝓛)}_m = 1 + T Ψ(m,l)`, `l = k` for
`m+1 ≤ N`, `l = k-1` for `N ≤ m ≤ N+1`; `(auskoppw2)` for `m = 2N-1`; the a priori level `ρ^{4p-1}` for `m = 4p`) and `XLKv`
that of `Ξ̂^{(𝓛-𝒦)}_m` (`1` for `m = 1`, `Ψ(m,k)` above). -/

/-- The control of `Ξ̂^{(𝓛)}_m`. -/
private noncomputable def iterationsA_XLv (A ρ T cB cv : ℝ) (N k p m : ℕ) : ℝ :=
  if m ≤ N + 1 then
    1 + T * (if m = 1 then 1 else if m + 1 ≤ N then STPsi A ρ m k else STPsi A ρ m (k - 1))
  else if m = 2 * N - 1 then
    1 + cv * A * ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2
  else if m = 4 * p then 1 + ρ ^ (4 * p - 1) else 1

/-- The control of `Ξ̂^{(𝓛-𝒦)}_m`. -/
private noncomputable def iterationsA_XLKv (A ρ : ℝ) (k m : ℕ) : ℝ :=
  1 + (if m = 1 then 0 else STPsi A ρ m k)

private theorem iterationsA_XLv_ge_one {A ρ T cB cv : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hT : 0 ≤ T) (hcB : 0 ≤ cB)
    (hcv : 0 ≤ cv) (N k p m : ℕ) : 1 ≤ iterationsA_XLv A ρ T cB cv N k p m := by
  have hP : ∀ j, 0 ≤ STPsi A ρ m j := fun j => iterationsA_STPsi_nonneg hA hρ m j
  unfold iterationsA_XLv
  split_ifs
  · have : 0 ≤ T * (1 : ℝ) := by positivity
    linarith
  · have := hP k
    have : 0 ≤ T * STPsi A ρ m k := by positivity
    linarith
  · have := hP (k - 1)
    have : 0 ≤ T * STPsi A ρ m (k - 1) := by positivity
    linarith
  · have : 0 ≤ cv * A * ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 := by
      have := Real.rpow_nonneg hA (1 - ((k - 1 : ℕ) : ℝ) / 8)
      positivity
    linarith
  · have : 0 ≤ ρ ^ (4 * p - 1) := by positivity
    linarith
  · exact le_rfl

/-- `(E1)`: `m ≤ N+1` gives `XLv ≤ 1 + T Ψ(m,k-1)`. -/
private theorem iterationsA_XLv_le_pred {A ρ T cB cv : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (hT : 0 ≤ T)
    {N k p m : ℕ} (hk : 1 ≤ k) (hmN : m ≤ N + 1) :
    iterationsA_XLv A ρ T cB cv N k p m ≤ 1 + T * STPsi A ρ m (k - 1) := by
  unfold iterationsA_XLv
  rw [ite_eq_left hmN]
  have h1 := iterationsA_one_le_STPsi hA hρ m (k - 1)
  have h2 := iterationsA_STPsi_anti_k hA hρ m hk
  have hP : 1 + T * (if m = 1 then 1 else if m + 1 ≤ N then STPsi A ρ m k else STPsi A ρ m (k - 1)) ≤
      1 + T * STPsi A ρ m (k - 1) := by
    have : (if m = 1 then (1 : ℝ) else if m + 1 ≤ N then STPsi A ρ m k else STPsi A ρ m (k - 1)) ≤
        STPsi A ρ m (k - 1) := by
      split_ifs
      · exact h1
      · exact h2
      · exact le_rfl
    gcongr
  exact hP

/-- `(E1')`: `m + 1 ≤ N` gives `XLv ≤ 1 + T Ψ(m,k)`. -/
private theorem iterationsA_XLv_le {A ρ T cB cv : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (hT : 0 ≤ T)
    {N k p m : ℕ} (hmN : m + 1 ≤ N) :
    iterationsA_XLv A ρ T cB cv N k p m ≤ 1 + T * STPsi A ρ m k := by
  unfold iterationsA_XLv
  rw [ite_eq_left (by omega : m ≤ N + 1)]
  have h1 := iterationsA_one_le_STPsi hA hρ m k
  have : (if m = 1 then (1 : ℝ) else if m + 1 ≤ N then STPsi A ρ m k else STPsi A ρ m (k - 1)) ≤
      STPsi A ρ m k := by
    split_ifs
    · exact h1
    · exact le_rfl
  gcongr

/-- `(E2)`: the control of `Ξ̂_{2N-1}`: `XLv ≤ 1 + cv A Z²`, `Z = 1 + cB + T ρ^N A^{1-(k-1)/8}`
(equality for `N ≥ 3`; for `N = 2` it is `Ξ̂_3 ≤ 1 + T Ψ(3,k-1) ≤ Z ≤ 1 + cv A Z²`). -/
private theorem iterationsA_XLv_le_chain {A ρ T cB cv : ℝ} (hA : 1 ≤ A) (hρ : 1 ≤ ρ) (hT : 0 ≤ T)
    (hcB : 0 ≤ cB) (hcv : 1 ≤ cv) (hT1 : T * A ^ (3 / 4 : ℝ) ≤ cB) {N k p : ℕ} (hN : 2 ≤ N) :
    iterationsA_XLv A ρ T cB cv N k p (2 * N - 1) ≤
      1 + cv * A * ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 := by
  have hA0 : 0 < A := by linarith
  set Z : ℝ := (1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) with hZ
  have hZ1 : 1 ≤ Z := by
    have := Real.rpow_nonneg hA0.le (1 - ((k - 1 : ℕ) : ℝ) / 8)
    have : 0 ≤ T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by positivity
    rw [hZ]; linarith
  by_cases h3 : 3 ≤ N
  · unfold iterationsA_XLv
    rw [ite_eq_right (by omega), ite_eq_left rfl]
  · have hN2 : N = 2 := by omega
    subst hN2
    unfold iterationsA_XLv
    rw [ite_eq_left (by omega)]
    -- `Ξ̂_3 ≤ 1 + T Ψ(3,k-1) ≤ Z ≤ 1 + cv A Z²`
    have hm : ¬ (2 * 2 - 1 = 1) := by omega
    have hm' : ¬ (2 * 2 - 1 + 1 ≤ 2) := by omega
    rw [ite_eq_right hm, ite_eq_right hm']
    have hPk : STPsi A ρ (2 * 2 - 1) (k - 1) = A ^ (3 / 4 : ℝ) + ρ ^ 2 * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by
      unfold STPsi; norm_num
    rw [hPk]
    have h1 : 1 + T * (A ^ (3 / 4 : ℝ) + ρ ^ 2 * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ≤ Z := by
      rw [hZ]; nlinarith
    have h2 : Z ≤ 1 + cv * A * Z ^ 2 := by
      have : 1 ≤ cv * A := by nlinarith
      have h3 : Z ≤ Z ^ 2 := by nlinarith
      have h4 : Z ^ 2 ≤ cv * A * Z ^ 2 := by nlinarith [sq_nonneg Z]
      linarith
    exact h1.trans h2

/-- `(E3)`: for `N + 1 < 4p`, `4p ≠ 2N - 1`: `XLv_{4p} = 1 + ρ^{4p-1}`. -/
private theorem iterationsA_XLv_four_p (A ρ T cB cv : ℝ) {N k p : ℕ} (h1 : N + 1 < 4 * p) (_h2 : 2 * N - 1 ≠ 4 * p) :
    iterationsA_XLv A ρ T cB cv N k p (4 * p) = 1 + ρ ^ (4 * p - 1) := by
  unfold iterationsA_XLv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

private theorem iterationsA_XLKv_ge_one {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (k m : ℕ) : 1 ≤ iterationsA_XLKv A ρ k m := by
  unfold iterationsA_XLKv
  have := iterationsA_STPsi_nonneg hA hρ m k
  split_ifs <;> linarith

private theorem iterationsA_XLKv_le {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) {k m : ℕ} :
    iterationsA_XLKv A ρ k m ≤ 1 + STPsi A ρ m k := by
  unfold iterationsA_XLKv
  have := iterationsA_one_le_STPsi hA hρ m k
  split_ifs <;> linarith


/-- `XLv ≤ Z` for `m ≤ N+1`, `Z = 1 + cB + T ρ^N A^{1-(k-1)/8}`. -/
private theorem iterationsA_XLv_le_Z {A ρ T cB cv : ℝ} (hA : 1 ≤ A) (hρ : 1 ≤ ρ) (hT : 0 ≤ T)
    (hT1 : T * A ^ (3 / 4 : ℝ) ≤ cB) {N k p m : ℕ} (hk : 1 ≤ k) (hmN : m ≤ N + 1) :
    iterationsA_XLv A ρ T cB cv N k p m ≤ (1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by
  have hA0 : 0 < A := by linarith
  have h1 := iterationsA_XLv_le_pred (cB := cB) (cv := cv) (p := p) hA (by linarith : 0 ≤ ρ) hT hk hmN
  refine h1.trans ?_
  unfold STPsi
  have hρN : ρ ^ (m - 1) ≤ ρ ^ N := pow_le_pow_right₀ hρ (by omega)
  have he : 0 ≤ A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := Real.rpow_nonneg hA0.le _
  have h2 : T * (ρ ^ (m - 1) * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ≤ T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by
    rw [mul_assoc]; gcongr
  nlinarith

/-- `Ξ̂^{(𝓛)}_m ≺ 1 + T Y` from `(rela_XILXILK)` and `Ξ̂^{(𝓛-𝒦)}_m ≺ Y` (`3_5:1387`, `3_5:1799-1805`): the transfer
`1 + B_v Ξ̂^{(𝓛-𝒦)} ≺ 1 + B_v Y ≤ 1 + T Y` for `W^{-d}B_{v,0} ≤ T`. -/
private theorem iterationsA_prec_XL_of (hsize : Tendsto sz.size atTop atTop) {E s t T : ℕ → ℝ} {m : ℕ}
    (hrela : sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω))
    {Y : ∀ n, STPair s t n → ℝ} (hY0 : ∀ n q, 0 ≤ Y n q)
    (hG : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => Y n q))
    (hT : ∀ᶠ n in atTop, ∀ q : STPair s t n, sz.Bctl n q.1.1 ≤ T n) (ht1 : ∀ n, t n < 1) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => 1 + T n * Y n q) := by
  have hGnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ STXiLK sz n (E n) q.1.1 m ω := fun n q ω => by
    have hu : q.1.1 < 1 := lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (ht1 n)
    linarith [st_one_le_XiLK sz (n := n) (E := E n) (v := q.1.1) m ω (st_Bctl_pos sz (n := n) hu)]
  have hA := iterationsA_prec_one_add_mul sz hsize (U := STPair s t) (c := fun n q => sz.Bctl n q.1.1)
    (fun n q => iterationsA_Bctl_nonneg sz n _) hGnn hG
  have hB := StochDomAt.trans hsize hrela hA
  refine iterationsA_prec_mono_right sz hB ?_
  filter_upwards [hT] with n hn q ω
  have := hY0 n q
  have := hn q
  nlinarith [mul_le_mul_of_nonneg_right (hn q) (hY0 n q)]


/-! ## 7. The step of `lem:iterations`

`IterationsAScale`: the deterministic facts of `3_5:1387-1431` that the step uses, for a scale sequence `A`
(`A = ilambda² W^d` in case (i), `A = (W^{-d}B_{s,0})⁻¹` in case (ii)), the number `T n ≥ W^{-d}B_{v,0}` (`v ∈ [s,t]`) and
`ρ = η_s/η_u = (1-s)/(1-u)`: `ρ ≥ 1`, `ρ² ≤ K A^{1/8}` (`ρ ≤ A^{𝔠d}`, `𝔠d ≤ 1/100`), `T A^{3/4} ≤ cB`, `T ρ² A^{7/8} ≤ cB K`
(`T = cB A^{-1+δ}`, `ρ² A^δ ≤ K A^{1/8}`), `(cv A)⁻¹ ≤ W^{-d}B_{v,0} ≤ T`.  It is proved in both cases by
`iterationsA_scale_I`, `iterationsA_scale_II` (section 8). -/

/-- The deterministic scale facts of the step of `lem:iterations` (`3_5:1387-1431`). -/
structure IterationsAScale (sz : Sizes d) (E s t A T : ℕ → ℝ) (cB cv K : ℝ) : Prop where
  cB_nonneg : 0 ≤ cB
  one_le_cv : 1 ≤ cv
  one_le_K : 1 ≤ K
  A_nonneg : ∀ n, 0 ≤ A n
  T_nonneg : ∀ n, 0 ≤ T n
  t_lt_one : ∀ n, t n < 1
  one_le_A : ∀ᶠ n in atTop, 1 ≤ A n
  rho : ∀ᶠ n in atTop, ∀ q : STPair s t n, 1 ≤ etaT (E n) (s n) / etaT (E n) q.1.2 ∧
    (etaT (E n) (s n) / etaT (E n) q.1.2) ^ 2 ≤ K * A n ^ (1 / 8 : ℝ) ∧
    T n * (etaT (E n) (s n) / etaT (E n) q.1.2) ^ 2 * A n ^ (7 / 8 : ℝ) ≤ cB * K
  TA : ∀ᶠ n in atTop, T n * A n ^ (3 / 4 : ℝ) ≤ cB
  Bctl : ∀ᶠ n in atTop, ∀ w : TimeIcc s t n, (cv * A n)⁻¹ ≤ sz.Bctl n (w : ℝ) ∧ sz.Bctl n (w : ℝ) ≤ T n

/-- The control `ρ_u = max 1 (η_s/η_u)` (equal to `η_s/η_u` on the pairs, where it is `≥ 1`). -/
private noncomputable def iterationsA_rho (E s : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  max 1 (etaT (E n) (s n) / etaT (E n) u)

/-- The control of `Ξ̂^{(𝓛)}_m` at the size `n` and the endpoint `u`. -/
private noncomputable def iterationsA_XL (E s A T : ℕ → ℝ) (cB cv : ℝ) (N k m n : ℕ) (u : ℝ) : ℝ :=
  iterationsA_XLv (A n) (iterationsA_rho E s n u) (T n) cB cv N k (N + 4) m

/-- The control of `Ξ̂^{(𝓛-𝒦)}_m`. -/
private noncomputable def iterationsA_XLK (E s A : ℕ → ℝ) (k m n : ℕ) (u : ℝ) : ℝ :=
  iterationsA_XLKv (A n) (iterationsA_rho E s n u) k m

private theorem iterationsA_rho_ge_one (E s : ℕ → ℝ) (n : ℕ) (u : ℝ) : 1 ≤ iterationsA_rho E s n u :=
  le_max_left _ _

private theorem iterationsA_rho_eq {E s : ℕ → ℝ} {n : ℕ} {u : ℝ} (h : 1 ≤ etaT (E n) (s n) / etaT (E n) u) :
    iterationsA_rho E s n u = etaT (E n) (s n) / etaT (E n) u := max_eq_right h

/-- **The obligations for `m ≤ N+1`**: `Ξ̂^{(𝓛)}_m ≺ 1 + T Y_m` with `Y_1 = 1`, `Y_m = Ψ(m,k)` for `m + 1 ≤ N`
(`eq:iteration_induc` at `(m,k)`), `Y_m = Ψ(m,k-1)` for `N ≤ m ≤ N+1` (at `(m,k-1)`), `3_5:1799-1805`. -/
private theorem iterationsA_obl_short (hsize : Tendsto sz.size atTop atTop)
    {E s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScale sz E s t A T cB cv K) {N k : ℕ}
    (hrela : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω))
    (havg : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1))
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHyp sz E s t A r (k - 1))
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ N + 1) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => iterationsA_XL E s A T cB cv N k m n q.1.2) := by
  set Y : ∀ n, STPair s t n → ℝ := fun n q =>
    if m = 1 then 1 else if m + 1 ≤ N then STPsi (A n) (iterationsA_rho E s n q.1.2) m k
    else STPsi (A n) (iterationsA_rho E s n q.1.2) m (k - 1) with hY
  have hY0 : ∀ n q, 0 ≤ Y n q := by
    intro n q
    have hρ0 : 0 ≤ iterationsA_rho E s n q.1.2 := by linarith [iterationsA_rho_ge_one E s n q.1.2]
    simp only [hY]
    split_ifs
    · norm_num
    · exact iterationsA_STPsi_nonneg (hS.A_nonneg n) hρ0 _ _
    · exact iterationsA_STPsi_nonneg (hS.A_nonneg n) hρ0 _ _
  have hG : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => Y n q) := by
    by_cases hm : m = 1
    · subst hm
      refine iterationsA_prec_mono_right sz havg ?_
      exact Eventually.of_forall fun n q ω => by simp [hY]
    · have hm2' : 2 ≤ m := by omega
      by_cases hmN : m + 1 ≤ N
      · have h : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
            (fun n q _ => STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) m k) := IH1 m hm2' hmN
        refine iterationsA_prec_mono_right sz h ?_
        filter_upwards [hS.rho] with n hn q ω
        have := (hn q).1
        simp only [hY, hm, hmN, ite_true, ite_false]
        rw [iterationsA_rho_eq this]
      · have h : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
            (fun n q _ => STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) m (k - 1)) := IH2 m hm2' (by omega)
        refine iterationsA_prec_mono_right sz h ?_
        filter_upwards [hS.rho] with n hn q ω
        have := (hn q).1
        simp only [hY, hm, hmN, ite_false]
        rw [iterationsA_rho_eq this]
  have hT : ∀ᶠ n in atTop, ∀ q : STPair s t n, sz.Bctl n q.1.1 ≤ T n := by
    filter_upwards [hS.Bctl] with n hn q
    exact (hn ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩).2
  have hmain := iterationsA_prec_XL_of sz hsize (hrela m hm1) hY0 hG hT hS.t_lt_one
  refine iterationsA_prec_mono_right sz hmain (Eventually.of_forall fun n q ω => le_of_eq ?_)
  unfold iterationsA_XL iterationsA_XLv
  rw [ite_eq_left hm2]

/-- The `≺` of `1 + c ((F₁F₂)(F₂F₃))^{1/2}` from `F_i ≺ X_i` (the four loops `2l₁, 2l₂, 2l₃ = 2l₂, 2l₄` of `(auskoppw2)`). -/
private theorem iterationsA_prec_chain_abs (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {F1 F2 F3 X1 X2 X3 : ∀ n, U n → sz.SeqΩ → ℝ} {c : ∀ n, U n → ℝ} (hc : ∀ n u, 0 ≤ c n u)
    (hF1 : ∀ n u ω, 0 ≤ F1 n u ω) (hF2 : ∀ n u ω, 0 ≤ F2 n u ω) (hF3 : ∀ n u ω, 0 ≤ F3 n u ω)
    (hX1 : ∀ n u ω, 0 ≤ X1 n u ω) (hX2 : ∀ n u ω, 0 ≤ X2 n u ω) (hX3 : ∀ n u ω, 0 ≤ X3 n u ω)
    (h1 : sz.Prec F1 X1) (h2 : sz.Prec F2 X2) (h3 : sz.Prec F3 X3) :
    sz.Prec (fun n u ω => 1 + c n u * ((F1 n u ω * F2 n u ω) * (F2 n u ω * F3 n u ω)) ^ (1 / 2 : ℝ))
      (fun n u ω => 1 + c n u * ((X1 n u ω * X2 n u ω) * (X2 n u ω * X3 n u ω)) ^ (1 / 2 : ℝ)) := by
  have h12 : sz.Prec (fun n u ω => F1 n u ω * F2 n u ω) (fun n u ω => X1 n u ω * X2 n u ω) :=
    StochDomAt.mul (ξ₁ := F1) (ξ₂ := F2) (ζ₁ := X1) (ζ₂ := X2) hsize hF2 hX1 h1 h2
  have h23 : sz.Prec (fun n u ω => F2 n u ω * F3 n u ω) (fun n u ω => X2 n u ω * X3 n u ω) :=
    StochDomAt.mul (ξ₁ := F2) (ξ₂ := F3) (ζ₁ := X2) (ζ₂ := X3) hsize hF3 hX2 h2 h3
  have hP : sz.Prec (fun n u ω => (F1 n u ω * F2 n u ω) * (F2 n u ω * F3 n u ω))
      (fun n u ω => (X1 n u ω * X2 n u ω) * (X2 n u ω * X3 n u ω)) :=
    StochDomAt.mul (ξ₁ := fun n u ω => F1 n u ω * F2 n u ω) (ξ₂ := fun n u ω => F2 n u ω * F3 n u ω)
      (ζ₁ := fun n u ω => X1 n u ω * X2 n u ω) (ζ₂ := fun n u ω => X2 n u ω * X3 n u ω) hsize
      (fun n u ω => mul_nonneg (hF2 n u ω) (hF3 n u ω)) (fun n u ω => mul_nonneg (hX1 n u ω) (hX2 n u ω)) h12 h23
  have hsq := iterationsA_prec_rpow sz
    (fun n u ω => mul_nonneg (mul_nonneg (hF1 n u ω) (hF2 n u ω)) (mul_nonneg (hF2 n u ω) (hF3 n u ω)))
    (fun n u ω => mul_nonneg (mul_nonneg (hX1 n u ω) (hX2 n u ω)) (mul_nonneg (hX2 n u ω) (hX3 n u ω)))
    (θ := 1 / 2) (by norm_num) hP
  exact iterationsA_prec_one_add_mul sz hsize hc
    (fun n u ω => Real.rpow_nonneg (mul_nonneg (mul_nonneg (hF1 n u ω) (hF2 n u ω))
      (mul_nonneg (hF2 n u ω) (hF3 n u ω))) _) hsq

/-- `((x₁x₂)(x₂x₃))^{1/2} ≤ Z²` for `0 ≤ x_i ≤ Z`. -/
private theorem iterationsA_sqrt_prod_le {x1 x2 x3 Z : ℝ} (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3)
    (a1 : x1 ≤ Z) (a2 : x2 ≤ Z) (a3 : x3 ≤ Z) : ((x1 * x2) * (x2 * x3)) ^ (1 / 2 : ℝ) ≤ Z ^ 2 := by
  have hZ : 0 ≤ Z := h1.trans a1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have e12 : x1 * x2 ≤ Z * Z := mul_le_mul a1 a2 h2 hZ
  have e23 : x2 * x3 ≤ Z * Z := mul_le_mul a2 a3 h3 hZ
  calc (x1 * x2) * (x2 * x3) ≤ (Z * Z) * (Z * Z) := mul_le_mul e12 e23 (mul_nonneg h2 h3) (by positivity)
    _ = (Z ^ 2) ^ 2 := by ring

/-- **The obligation for `m = 2N-1`, `N ≥ 3`** (`(auskoppw2)`, `3_5:1824-1862`): `Ξ̂^{(𝓛)}_{2N-1} ≺ 1 + cv A Z²`, from the
odd chain bound `iterationsA_xiL_odd_le` and the controls of the four loops `Ξ̂_{2l_i}`, `2 l_i ≤ N+1`. -/
private theorem iterationsA_obl_chain (hsize : Tendsto sz.size atTop atTop)
    {E s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScale sz E s t A T cB cv K) {N k : ℕ} (hN3 : 3 ≤ N)
    (hk : 1 ≤ k)
    (hshort : ∀ m, 1 ≤ m → m ≤ N + 1 → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => iterationsA_XL E s A T cB cv N k m n q.1.2)) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 (2 * N - 1) ω)
      (fun n q _ => iterationsA_XL E s A T cB cv N k (2 * N - 1) n q.1.2) := by
  have ht1 := hS.t_lt_one
  have hBpos : ∀ n (q : STPair s t n), 0 < sz.Bctl n q.1.1 := fun n q =>
    st_Bctl_pos sz (n := n) (lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (ht1 n))
  have hFge : ∀ m n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ STXiL sz n (E n) q.1.1 m ω := fun m n q ω => by
    linarith [st_one_le_XiL sz (n := n) (E := E n) (v := q.1.1) m ω (hBpos n q)]
  have hXge : ∀ m n (q : STPair s t n), 1 ≤ iterationsA_XL E s A T cB cv N k m n q.1.2 := fun m n q =>
    iterationsA_XLv_ge_one (hS.A_nonneg n) (by linarith [iterationsA_rho_ge_one E s n q.1.2]) (hS.T_nonneg n)
      hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m
  have hone := iterationsA_prec_chain_abs sz hsize (U := STPair s t) (c := fun n _ => cv * A n)
    (fun n _ => by have := hS.A_nonneg n; have := hS.one_le_cv; positivity)
    (fun n q ω => hFge _ n q ω) (fun n q ω => hFge _ n q ω) (fun n q ω => hFge _ n q ω)
    (fun n q _ => by linarith [hXge (2 * ((N + 1) / 2)) n q]) (fun n q _ => by linarith [hXge (2 * (N / 2)) n q])
    (fun n q _ => by linarith [hXge (2 * ((N - 1) / 2)) n q])
    (hshort (2 * ((N + 1) / 2)) (by omega) (by omega)) (hshort (2 * (N / 2)) (by omega) (by omega))
    (hshort (2 * ((N - 1) / 2)) (by omega) (by omega))
  -- the right side: `1 + cv A P^{1/2} ≤ XL (2N-1)`
  have hright : ∀ᶠ n in atTop, ∀ (q : STPair s t n) (ω : sz.SeqΩ),
      1 + cv * A n * (((iterationsA_XL E s A T cB cv N k (2 * ((N + 1) / 2)) n q.1.2 *
          iterationsA_XL E s A T cB cv N k (2 * (N / 2)) n q.1.2) *
        (iterationsA_XL E s A T cB cv N k (2 * (N / 2)) n q.1.2 *
          iterationsA_XL E s A T cB cv N k (2 * ((N - 1) / 2)) n q.1.2)) ^ (1 / 2 : ℝ)) ≤
        iterationsA_XL E s A T cB cv N k (2 * N - 1) n q.1.2 := by
    filter_upwards [hS.one_le_A, hS.TA] with n hAn hT1n q ω
    have hρ1 := iterationsA_rho_ge_one E s n q.1.2
    have hXZ : ∀ m, 1 ≤ m → m ≤ N + 1 → iterationsA_XL E s A T cB cv N k m n q.1.2 ≤
        (1 + cB) + T n * iterationsA_rho E s n q.1.2 ^ N * A n ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := fun m hm1 hm2 =>
      iterationsA_XLv_le_Z hAn hρ1 (hS.T_nonneg n) hT1n hk hm2
    have hsqrt := iterationsA_sqrt_prod_le (by linarith [hXge (2 * ((N + 1) / 2)) n q])
      (by linarith [hXge (2 * (N / 2)) n q]) (by linarith [hXge (2 * ((N - 1) / 2)) n q])
      (hXZ (2 * ((N + 1) / 2)) (by omega) (by omega)) (hXZ (2 * (N / 2)) (by omega) (by omega))
      (hXZ (2 * ((N - 1) / 2)) (by omega) (by omega))
    have hcvA : 0 ≤ cv * A n := by have := hS.A_nonneg n; have := hS.one_le_cv; positivity
    calc _ ≤ 1 + cv * A n * ((1 + cB) + T n * iterationsA_rho E s n q.1.2 ^ N * A n ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 := by
          gcongr
      _ = iterationsA_XL E s A T cB cv N k (2 * N - 1) n q.1.2 := by
          unfold iterationsA_XL iterationsA_XLv
          rw [ite_eq_right (by omega), ite_eq_left rfl]
  have hone' := iterationsA_prec_mono_right sz hone (Eventually.mono hright fun n hn q ω => hn q ω)
  -- the left side: `Ξ̂_{2N-1} ≤ 1 + cv A P^{1/2}`
  refine iterationsA_prec_mono_left sz ?_ hone'
  filter_upwards [hS.Bctl, hS.one_le_A] with n hn hAn q ω
  have hB0 := hBpos n q
  have hlow : (sz.Bctl n q.1.1)⁻¹ ≤ cv * A n := by
    have := (hn ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩).1
    have hcvA : 0 < cv * A n := by have := hS.one_le_cv; positivity
    exact inv_le_of_inv_le₀ hcvA this
  refine (iterationsA_xiL_odd_le sz n (E := E n) (v := q.1.1) ω hB0 hN3).trans ?_
  have hP0 := Real.rpow_nonneg (mul_nonneg (mul_nonneg (hFge (2 * ((N + 1) / 2)) n q ω) (hFge (2 * (N / 2)) n q ω))
    (mul_nonneg (hFge (2 * (N / 2)) n q ω) (hFge (2 * ((N - 1) / 2)) n q ω))) (1 / 2 : ℝ)
  gcongr


/-- **The obligation for `Ξ̂^{(𝓛)}_{4p}`**: the a priori level `ρ^{4p-1}` (`(sef8w483r324)`, `3_5:1391`), `p = N + 4`
(so that `4p > N + 1` and `4p ≠ 2N - 1`). -/
private theorem iterationsA_obl_four_p {E s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : IterationsAScale sz E s t A T cB cv K) {N k : ℕ}
    (hapri : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1))) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 (4 * (N + 4)) ω)
      (fun n q _ => iterationsA_XL E s A T cB cv N k (4 * (N + 4)) n q.1.2) := by
  refine iterationsA_prec_mono_right sz (hapri (4 * (N + 4)) (by omega)) ?_
  filter_upwards [hS.rho] with n hn q ω
  have hρ1 := (hn q).1
  unfold iterationsA_XL
  rw [iterationsA_XLv_four_p _ _ _ _ _ (by omega) (by omega), iterationsA_rho_eq hρ1]
  have : 0 ≤ (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (4 * (N + 4) - 1) := by positivity
  linarith

/-- **The obligations for `Ξ̂^{(𝓛-𝒦)}_m`, `m + 1 ≤ N`**: `m = 1` is the averaged law, `m ≥ 2` is `(eq:iteration_induc)` at `(m,k)`. -/
private theorem iterationsA_obl_K {E s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : IterationsAScale sz E s t A T cB cv K) {N k : ℕ}
    (havg : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1))
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r k)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m + 1 ≤ N) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
      (fun n q _ => iterationsA_XLK E s A k m n q.1.2) := by
  by_cases hm : m = 1
  · subst hm
    refine iterationsA_prec_mono_right sz havg ?_
    exact Eventually.of_forall fun n q ω => by simp [iterationsA_XLK, iterationsA_XLKv]
  · have h : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) m k) := IH1 m (by omega) hm2
    refine iterationsA_prec_mono_right sz h ?_
    filter_upwards [hS.rho] with n hn q ω
    have hρ1 := (hn q).1
    have hP := iterationsA_STPsi_nonneg (hS.A_nonneg n) (by linarith : 0 ≤ etaT (E n) (s n) / etaT (E n) q.1.2) m k
    unfold iterationsA_XLK iterationsA_XLKv
    rw [iterationsA_rho_eq hρ1, ite_eq_right hm]
    linarith

/-- **The step of `lem:iterations`** (`3_5:1407-1417`, proof `3_5:1772-1864`; RBM2D `step3_S_of_S`, `Step3.lean:540`, with the slot
`step3Lemma514` replaced by the bootstrap bound `(am;asoi222)` = `STXiBoot`, dimension free): under the scale facts
`IterationsAScale`, the bootstrap bound `STXiBoot`, the relation `(rela_XILXILK)` (`hrela`, `3_5:1387`: from `(eq:bcal_k)`), the
averaged law `Ξ̂^{(𝓛-𝒦)}_1 ≺ 1` (`havg`) and the a priori bound `(sef8w483r324)` (`hapri`, from `(lRB1)`), `(eq:iteration_induc)`
at `(r,k)`, `2 ≤ r ≤ N-1`, and at `(r,k-1)`, `2 ≤ r ≤ N+2`, give it at `(N,k)`, `N ≥ 2`, `k ≥ 1`.
`sup_{v ∈ [s,u]}` is the pair index `STPair`; the controls are `p = N + 4`, `XL`, `XLK` of `iterationsA_boot_bound`. -/
theorem iterationsA_step (hsize : Tendsto sz.size atTop atTop)
    {E s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScale sz E s t A T cB cv K)
    (hboot : STXiBoot sz E s t)
    (hrela : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω))
    (havg : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1))
    (hapri : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1)))
    {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k)
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHyp sz E s t A r (k - 1)) :
    STIterHyp sz E s t A N k := by
  have hshort : ∀ m, 1 ≤ m → m ≤ N + 1 → sz.Prec (U := STPair s t)
      (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => iterationsA_XL E s A T cB cv N k m n q.1.2) :=
    fun m hm1 hm2 => iterationsA_obl_short sz hsize hS hrela havg IH1 IH2 hm1 hm2
  have hFobl : ∀ m, 1 ≤ m → STlenL N (N + 4) m → sz.Prec (U := STPair s t)
      (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => iterationsA_XL E s A T cB cv N k m n q.1.2) := by
    intro m hm1 hlen
    by_cases hmN : m ≤ N + 1
    · exact hshort m hm1 hmN
    · have h2 : m = 2 * N - 1 ∨ m = 4 * (N + 4) := by unfold STlenL at hlen; omega
      rcases h2 with h | h
      · subst h
        exact iterationsA_obl_chain sz hsize hS (by omega) hk hshort
      · subst h
        exact iterationsA_obl_four_p sz hS hapri
  have hbootN := hboot N (N + 4) hN (by omega) (fun m n u => iterationsA_XL E s A T cB cv N k m n u)
    (fun m n u => iterationsA_XLK E s A k m n u)
    (fun m n u => iterationsA_XLv_ge_one (hS.A_nonneg n) (by linarith [iterationsA_rho_ge_one E s n u])
      (hS.T_nonneg n) hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m)
    (fun m n u => iterationsA_XLKv_ge_one (hS.A_nonneg n) (by linarith [iterationsA_rho_ge_one E s n u]) k m)
    hFobl (fun m hm1 hm2 => iterationsA_obl_K sz hS havg IH1 hm1 hm2)
  obtain ⟨C, hCpos, hC⟩ := iterationsA_boot_bound cB cv K hS.cB_nonneg hS.one_le_cv hS.one_le_K N k hN hk
  have hmain : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 N ω)
      (fun n q _ => C * STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) N k) := by
    refine iterationsA_prec_mono_right sz hbootN ?_
    filter_upwards [hS.one_le_A, hS.rho, hS.TA, hS.Bctl] with n hAn hρn hTAn hBn q ω
    have hρ1 := (hρn q).1
    have hρeq := iterationsA_rho_eq hρ1
    have hρ1' := iterationsA_rho_ge_one E s n q.1.2
    have hρ0 : 0 ≤ iterationsA_rho E s n q.1.2 := by linarith
    have hlow := (hBn ⟨q.1.2, q.2.1.trans q.2.2.1, q.2.2.2⟩).1
    have hb := hC (A n) (iterationsA_rho E s n q.1.2) (T n) (sz.Bctl n q.1.2) (N + 4)
      (fun m => iterationsA_XL E s A T cB cv N k m n q.1.2) (fun m => iterationsA_XLK E s A k m n q.1.2)
      (by omega) hAn hρ1' (by rw [hρeq]; exact (hρn q).2.1) (hS.T_nonneg n) hTAn
      (by rw [hρeq]; exact (hρn q).2.2) hlow
      (fun m hm1 hm2 => iterationsA_XLv_le_pred hAn hρ0 (hS.T_nonneg n) hk hm2)
      (fun m hm1 hm2 => iterationsA_XLv_le hAn hρ0 (hS.T_nonneg n) hm2)
      (fun m => iterationsA_XLv_ge_one (hS.A_nonneg n) hρ0 (hS.T_nonneg n) hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m)
      (iterationsA_XLv_le_chain hAn hρ1' (hS.T_nonneg n) hS.cB_nonneg hS.one_le_cv hTAn hN)
      (iterationsA_XLv_four_p _ _ _ _ _ (by omega) (by omega)).le
      (fun m => iterationsA_XLKv_ge_one (hS.A_nonneg n) hρ0 k m)
      (fun m hm1 hm2 => iterationsA_XLKv_le hAn hρ0)
    rw [hρeq] at hb
    exact hb
  refine iterationsA_prec_absorb sz hsize ?_ hmain
  filter_upwards [hS.one_le_A, hS.rho] with n hAn hρn q ω
  exact iterationsA_STPsi_nonneg (by linarith) (by linarith [(hρn q).1]) N k

end RBM.Gauss.Sizes

/-! ## 7b. The hypotheses of the step from the merged pins

`havg` is `STAvgU` (Step 2) restricted to the pairs, `hapri` is `(lRB1)` (`STStep1Loop`) and `hrela` is `(rela_XILXILK)`
from the `𝒦`-loop bound `(eq:bcal_k)` (`STKbound`) in its form uniform in `(v,u)` and the labels; `STKbound` itself is per time
sequence and its uniform form is the maximizing-time lemma of the portmap (F-H, S3-06), so `hrela` is derived from the uniform
form `hK`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- **The averaged law on the pairs** (`3_5:1386`, `3_5:1774`): `Ξ̂^{(𝓛-𝒦)}_{v,1} ≺ 1` uniformly in `(v,u)`, from `STAvgU`
(`(Gt_avgbound_flow)` uniform in `u`); the `k = 1` case of the probe's `st_step4_skeleton`. -/
theorem iterationsA_avg_of_STAvgU (hsize : Tendsto sz.size atTop atTop) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STAvgU sz E s t) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1) := by
  let φ : ∀ n, STPair s t n → TimeIcc s t n := fun n q => ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩
  have hBpos : ∀ n (v : TimeIcc s t n), 0 < (sz.Bctl n (v : ℝ)) ^ 1 := fun n v =>
    pow_pos (st_Bctl_pos sz (n := n) (lt_of_le_of_lt (v.2).2 (ht1 n))) 1
  exact StochDomAt.precomp_param
    (st_prec_one_add_sup sz hsize (U := fun n => TimeIcc s t n)
      (V := fun n => (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
      (fun n v p ω => ‖Lloop sz n (E n) (v : ℝ) p.1 p.2 ω - STKloop sz n (E n) (v : ℝ) p.1 p.2‖)
      (fun n v => (sz.Bctl n (v : ℝ)) ^ 1) (fun n v => hBpos n v) h) φ

/-- The real inequality behind `iterationsA_apriori_of_lRB1`: `1 + S/b_v ≤ r_u (1 + S/(r_v b_s))` for `0 ≤ S`,
`1 ≤ r_v ≤ r_u`, `0 < b_s ≤ b_v`. -/
private theorem iterationsA_apriori_aux {S rv ru bs bv : ℝ} (hS : 0 ≤ S) (hrv : 1 ≤ rv) (hru : rv ≤ ru)
    (hbs : 0 < bs) (hbv : bs ≤ bv) : 1 + S / bv ≤ ru * (1 + S / (rv * bs)) := by
  have hrv0 : 0 < rv := by linarith
  have hbv0 : 0 < bv := by linarith
  have h1 : S / bv ≤ S / bs := div_le_div_of_nonneg_left hS hbs hbv
  have h2 : S / bs = rv * (S / (rv * bs)) := by field_simp
  have h3 : 0 ≤ S / (rv * bs) := by positivity
  have h4 : rv * (S / (rv * bs)) ≤ ru * (S / (rv * bs)) := mul_le_mul_of_nonneg_right hru h3
  nlinarith

/-- **The a priori bound `(sef8w483r324)` on the pairs** (`3_5:1391`): `Ξ̂^{(𝓛)}_{v,m} ≺ (η_s/η_u)^{m-1}` uniformly in `(v,u)`, from
`(lRB1)` (`STStep1Loop`): `Ξ̂ = 1 + max|𝓛|/B_v^{m-1}`, `max|𝓛| ≺ ((1-s)/(1-v))^{m-1} B_s^{m-1}`, `B_s ≤ B_v`, `(1-s)/(1-v) ≤ (1-s)/(1-u)`. -/
theorem iterationsA_apriori_of_lRB1 (hsize : Tendsto sz.size atTop atTop) {E s t : ℕ → ℝ}
    (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) (h : STStep1Loop sz E s t) (m : ℕ) (hm : 1 ≤ m) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1)) := by
  let φ : ∀ n, STPair s t n → TimeIcc s t n := fun n q => ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩
  have hv1 : ∀ n (v : TimeIcc s t n), (v : ℝ) < 1 := fun n v => lt_of_le_of_lt (v.2).2 (ht1 n)
  have hBc : ∀ n (v : TimeIcc s t n), 0 < ((1 - s n) / (1 - (v : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1) :=
    fun n v => by
      have h1 : 0 < 1 - s n := by linarith [(v.2).1, hv1 n v]
      have h2 : 0 < 1 - (v : ℝ) := by linarith [hv1 n v]
      have h3 : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (n := n) (by linarith [(v.2).1, hv1 n v])
      positivity
  have hX := st_prec_one_add_sup sz hsize (U := fun n => TimeIcc s t n)
    (V := fun n => (Fin m → Bool) × (Fin m → Zd d (sz.L n)))
    (fun n v p ω => ‖Lloop sz n (E n) (v : ℝ) p.1 p.2 ω‖)
    (fun n v => ((1 - s n) / (1 - (v : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1)) hBc (h m hm)
  have hX' := StochDomAt.precomp_param hX φ
  have hXnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ 1 + (Finset.univ.sup' Finset.univ_nonempty
      (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Lloop sz n (E n) (φ n q : ℝ) p.1 p.2 ω‖)) /
        (((1 - s n) / (1 - (φ n q : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1)) := fun n q ω => by
    have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Lloop sz n (E n) (φ n q : ℝ) p.1 p.2 ω‖) :=
      le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
        ‖Lloop sz n (E n) (φ n q : ℝ) p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
    have := hBc n (φ n q)
    positivity
  -- ρ_u^{m-1} · X ≺ ρ_u^{m-1} · 1
  have hρu : ∀ n (q : STPair s t n), 0 ≤ (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1) := fun n q => by
    rw [RBM.Ind.scaleFacts_etaT_div_etaT (hE n)]
    have h1 : 0 ≤ 1 - s n := by linarith [q.2.1, hv1 n (φ n q)]
    have h2 : 0 ≤ 1 - q.1.2 := by linarith [q.2.2.2, ht1 n]
    positivity
  have hmul : sz.Prec (U := STPair s t)
      (fun n q ω => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1) * (1 + (Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Lloop sz n (E n) (φ n q : ℝ) p.1 p.2 ω‖)) /
          (((1 - s n) / (1 - (φ n q : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1))))
      (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1) * 1) :=
    StochDomAt.mul (ξ₁ := fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1))
      (ξ₂ := fun n q ω => 1 + (Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Lloop sz n (E n) (φ n q : ℝ) p.1 p.2 ω‖)) /
          (((1 - s n) / (1 - (φ n q : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1)))
      (ζ₁ := fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1)) (ζ₂ := fun _ _ _ => 1) hsize
      (fun n q ω => hXnn n q ω) (fun n q _ => hρu n q)
      (StochDomAt.refl hsize (fun n q _ => hρu n q)) hX'
  refine iterationsA_prec_mono_right sz (iterationsA_prec_mono_left sz ?_ hmul)
    (Eventually.of_forall fun n q ω => by rw [mul_one])
  refine Eventually.of_forall fun n q ω => ?_
  -- the pointwise bound `Ξ̂ ≤ ρ_u^{m-1} X`
  have hsv : s n ≤ q.1.1 := q.2.1
  have hvu : q.1.1 ≤ q.1.2 := q.2.2.1
  have hv1' : q.1.1 < 1 := hv1 n (φ n q)
  have hu1 : q.1.2 < 1 := lt_of_le_of_lt q.2.2.2 (ht1 n)
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (n := n) (lt_of_le_of_lt hsv hv1')
  have hBv : sz.Bctl n (s n) ≤ sz.Bctl n q.1.1 := STBctl_mono sz n hsv hv1'
  have hS0 : 0 ≤ STmaxL sz n (E n) q.1.1 m ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
      ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  rw [RBM.Ind.scaleFacts_etaT_div_etaT (hE n)]
  have hrv := iterationsA_one_le_ratio hsv hv1'
  have hrvu : (1 - s n) / (1 - q.1.1) ≤ (1 - s n) / (1 - q.1.2) := by
    have h2 : 0 < 1 - q.1.2 := by linarith
    exact div_le_div_of_nonneg_left (by linarith) h2 (by linarith)
  have key := iterationsA_apriori_aux hS0 (one_le_pow₀ hrv : 1 ≤ ((1 - s n) / (1 - q.1.1)) ^ (m - 1))
    (pow_le_pow_left₀ (by linarith) hrvu _) (pow_pos hBs (m - 1)) (pow_le_pow_left₀ hBs.le hBv _)
  change 1 + STmaxL sz n (E n) q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) ≤ _
  exact key

/-- **`(rela_XILXILK)` on the pairs** (`3_5:1387`): `Ξ̂^{(𝓛)}_{v,m} ≺ 1 + W^{-d}B_{v,0} Ξ̂^{(𝓛-𝒦)}_{v,m}`, from the `𝒦`-loop bound
`(eq:bcal_k)` uniform in `(v,u)` and the labels: `max|𝓛| ≤ max|𝒦| + max|𝓛-𝒦|`, `B Ξ̂^{(𝓛-𝒦)} = B + max|𝓛-𝒦|/B^{m-1}`. -/
theorem iterationsA_rela_of_K (hsize : Tendsto sz.size atTop atTop) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (m : ℕ) (hm : 1 ≤ m)
    (hK : sz.Prec (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖STKloop sz n (E n) p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1))) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω) := by
  have hBpos : ∀ n (q : STPair s t n), 0 < sz.Bctl n q.1.1 := fun n q =>
    st_Bctl_pos sz (n := n) (lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (ht1 n))
  have hX := st_prec_one_add_sup sz hsize (U := STPair s t)
    (V := fun n => (Fin m → Bool) × (Fin m → Zd d (sz.L n)))
    (fun n q p ω => ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) (fun n q => sz.Bctl n q.1.1 ^ (m - 1))
    (fun n q => pow_pos (hBpos n q) _) hK
  have hGnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω :=
    fun n q ω => by
      have := st_one_le_XiLK sz (n := n) (E := E n) (v := q.1.1) m ω (hBpos n q)
      have := hBpos n q
      positivity
  have hadd := StochDomAt.add hsize hX
    (StochDomAt.refl hsize (ζ := fun n q ω => sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω) hGnn)
  refine iterationsA_prec_mono_left sz ?_ hadd
  refine Eventually.of_forall fun n q ω => ?_
  have hB0 := hBpos n q
  have hBm : 0 < sz.Bctl n q.1.1 ^ (m - 1) := pow_pos hB0 _
  set SK : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) with hSK
  have hSL : STmaxL sz n (E n) q.1.1 m ω ≤ SK + STmaxLK sz n (E n) q.1.1 m ω := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    have h1 : ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω‖ ≤ ‖STKloop sz n (E n) q.1.1 p.1 p.2‖ +
        ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω - STKloop sz n (E n) q.1.1 p.1 p.2‖ := by
      calc ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω‖
          = ‖STKloop sz n (E n) q.1.1 p.1 p.2 + (Lloop sz n (E n) q.1.1 p.1 p.2 ω - STKloop sz n (E n) q.1.1 p.1 p.2)‖ := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖STKloop sz n (E n) q.1.1 p.1 p.2‖ ≤ SK :=
      Finset.le_sup' (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖STKloop sz n (E n) q.1.1 p.1 p.2‖)
        (Finset.mem_univ p)
    have h3 : ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω - STKloop sz n (E n) q.1.1 p.1 p.2‖ ≤ STmaxLK sz n (E n) q.1.1 m ω :=
      Finset.le_sup' (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
        ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω - STKloop sz n (E n) q.1.1 p.1 p.2‖) (Finset.mem_univ p)
    linarith
  have hGeq : sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω =
      sz.Bctl n q.1.1 + STmaxLK sz n (E n) q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) := by
    unfold STXiLK
    have : sz.Bctl n q.1.1 ^ m = sz.Bctl n q.1.1 * sz.Bctl n q.1.1 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; field_simp
  change 1 + STmaxL sz n (E n) q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) ≤
    (1 + SK / sz.Bctl n q.1.1 ^ (m - 1)) + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω
  rw [hGeq]
  have h4 : STmaxL sz n (E n) q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) ≤
      SK / sz.Bctl n q.1.1 ^ (m - 1) + STmaxLK sz n (E n) q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hSL hBm.le
  linarith

end RBM.Gauss.Sizes

/-! ## 8. The scale facts of the step, both cases

Case (i) (`A = ilambda² W^d`, `1 - s ≤ ilambda²`, `1 - t ≥ ilambda²/L²`): `T = 2 A⁻¹`, `cB = cv = K = 2`
(`B_v ≤ 2 A⁻¹` needs `2 ≤ d`, `B_v ≥ (2A)⁻¹`, `ρ ≤ (2A)^{𝔠d}`).  Case (ii) (`A = (W^{-d}B_{s,0})⁻¹`, `1 - s ≤ ilambda²/L²`):
`T = A^{-1+𝔠d}`, `cB = cv = K = 1` (`B_v ≤ B_s^{1-𝔠d}` by `scaleFacts_R2`, `B_v ≥ B_s`, `ρ ≤ B_t^{-𝔠d} ≤ A^{𝔠d}`); the exponent
counts need `𝔠d ≤ 1/16` (case (i): `ρ² ≤ 2 A^{1/8}`) and `𝔠d ≤ 1/24` (case (ii): `A^{3𝔠d - 1/8} ≤ 1`), both implied by the
`𝔠d ≤ 1/100` of `STIterR`.  The proofs of the first three helpers are those of the private `st_WO_pos`, `st_WO_AI`, `st_con_aux`,
`st_rho_le`, `st_BI_lower` of `ScaleFacts3.lean` (private there, so reproved here). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

private theorem iterationsA_WO_pos {𝔡 : ℝ} (hWO : sz.WO 𝔡) : 0 < 𝔡 := by
  obtain ⟨n, h1, h2⟩ := hWO.exists
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact inv_pos.1 (lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) (h1.trans h2))

private theorem iterationsA_WO_AI {𝔡 : ℝ} (hWO : sz.WO 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ 1 ≤ sz.STAI n := by
  have h𝔡 := iterationsA_WO_pos sz hWO
  filter_upwards [hWO] with n hn
  obtain ⟨h1, -⟩ := hn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  refine ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) h1, ?_⟩
  have h2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := Real.one_le_rpow hW1 (by linarith)
  exact h2.trans (Sizes.lam_sq_mul_pow_ge sz n h1)

private theorem iterationsA_con_aux {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ} (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) : ∀ᶠ n in atTop, s n < t n ∧ sz.Bctl n (t n) < 1 := by
  filter_upwards [hcon] with n hn
  obtain ⟨h1, h2⟩ := hn
  have hBt : 0 < sz.Bctl n (t n) := st_Bctl_pos sz (ht1 n)
  have hpos : 0 < sz.Bctl n (t n) ^ 𝔠d := Real.rpow_pos_of_pos hBt _
  have hxt : 0 < 1 - t n := by linarith [ht1 n]
  have hr0 : 0 < (1 - t n) / (1 - s n) := lt_of_lt_of_le hpos h1
  have hxs : 0 < 1 - s n := by
    rcases (div_pos_iff.1 hr0) with h | h
    · exact h.2
    · linarith [h.1]
  refine ⟨?_, ?_⟩
  · have := (div_lt_one hxs).1 h2
    linarith
  · by_contra h
    have := Real.one_le_rpow (not_lt.1 h) h𝔠d.le
    linarith

/-- `η_s/η_v = (1-s)/(1-v) ≤ B_t^{-𝔠d}` for `s ≤ v ≤ t < 1` from `(con_st_ind)` at `n`. -/
private theorem iterationsA_rho_le {n : ℕ} {c s v t : ℝ} (hsv : s ≤ v) (hvt : v ≤ t) (ht1 : t < 1)
    (hB : sz.Bctl n t ^ c ≤ (1 - t) / (1 - s)) :
    (1 - s) / (1 - v) ≤ (sz.Bctl n t) ^ (-c) := by
  have hBt : 0 < sz.Bctl n t := st_Bctl_pos sz ht1
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  calc (1 - s) / (1 - v) ≤ (1 - s) / (1 - t) := div_le_div_of_nonneg_left hxs.le hxt (by linarith)
    _ = ((1 - t) / (1 - s))⁻¹ := (inv_div _ _).symm
    _ ≤ (sz.Bctl n t ^ c)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hBt c) hB
    _ = sz.Bctl n t ^ (-c) := (Real.rpow_neg hBt.le c).symm

/-- Case (i): `B_{w} ≥ (2 A_I)⁻¹` for `s ≤ w < 1`, `1 - s ≤ ilambda²`. -/
private theorem iterationsA_BI_lower {n : ℕ} {s w : ℝ} (hsw : s ≤ w) (hw1 : w < 1) (hs : 1 - s ≤ sz.lam n ^ 2)
    (hlam : 0 < sz.lam n) : 1 / (2 * sz.STAI n) ≤ sz.Bctl n w := by
  unfold Sizes.Bctl Bparam STAI
  have hx : 0 < 1 - w := by linarith
  rw [abs_of_pos hx]
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  simp only [hz, inv_one, mul_one]
  have hg : 0 < sz.lam n ^ 2 := by positivity
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have h1 : (2 * sz.lam n ^ 2)⁻¹ ≤ (sz.lam n ^ 2 + (1 - w))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - w))⁻¹ := by positivity
  calc 1 / (2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d))
      = ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (2 * sz.lam n ^ 2)⁻¹ := by field_simp
    _ ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * ((sz.lam n ^ 2 + (1 - w))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - w))⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Case (i): `B_w ≤ 2 A_I⁻¹` for `1 - w ≥ ilambda²/L²` (`2 ≤ d`: `L^d ≥ L²`). -/
private theorem iterationsA_BI_upper (hd : 2 ≤ d) {n : ℕ} {w : ℝ} (hcase : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - w)
    (hlam : 0 < sz.lam n) : sz.Bctl n w ≤ 2 * (sz.STAI n)⁻¹ := by
  have hg : 0 < sz.lam n ^ 2 := by positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hLd2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
  have hq : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have hx : 0 < 1 - w := lt_of_lt_of_le hq hcase
  have hgL : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (1 - w) := by
    have h1 : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - w) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2)).1 hcase
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hLd2 hx.le)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  unfold Sizes.Bctl Bparam STAI
  rw [abs_of_pos hx]
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  simp only [hz, inv_one, mul_one]
  have h1 : (sz.lam n ^ 2 + (1 - w))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ :=
    inv_anti₀ hg (by linarith)
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - w))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ :=
    inv_anti₀ hg hgL
  calc ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * ((sz.lam n ^ 2 + (1 - w))⁻¹ +
        (((sz.L n : ℕ) : ℝ) ^ d * (1 - w))⁻¹)
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * ((sz.lam n ^ 2)⁻¹ + (sz.lam n ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
        rw [mul_inv]; ring


/-- **The scale facts of the step, case (i)** (`A = ilambda² W^d`, `T = 2 A⁻¹`, `cB = cv = K = 2`; `3_5:1387-1431`): under
`STRegIterI` (`1 - s ≤ ilambda²`, `1 - t ≥ ilambda²/L²`), `(con_st_ind)`, `(eq:WO)`, `t < 1`, `|E| < 2`, `2 ≤ d` and
`0 < 𝔠d ≤ 1/16` (`STIterR` has `𝔠d ≤ 1/100`). -/
theorem iterationsA_scale_I (hd : 2 ≤ d) {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ} (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 16)
    (hreg : STRegIterI sz s t) (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡) (ht1 : ∀ n, t n < 1)
    (hE : ∀ n, |E n| < 2) :
    IterationsAScale sz E s t (fun n => sz.STAI n) (fun n => 2 * (sz.STAI n)⁻¹) 2 2 2 := by
  have hAnn : ∀ n, 0 ≤ sz.STAI n := fun n => by unfold STAI; positivity
  refine ⟨by norm_num, by norm_num, by norm_num, hAnn, fun n => ?_, ht1, ?_, ?_, ?_, ?_⟩
  · have := hAnn n
    positivity
  · filter_upwards [iterationsA_WO_AI sz hWO] with n hn
    exact hn.2
  · filter_upwards [hcon, iterationsA_WO_AI sz hWO] with n hn hW q
    obtain ⟨hlam, hA⟩ := hW
    have hsu : s n ≤ q.1.2 := q.2.1.trans q.2.2.1
    have hut : q.1.2 ≤ t n := q.2.2.2
    have hst : s n ≤ t n := hsu.trans hut
    have hu1 : q.1.2 < 1 := lt_of_le_of_lt hut (ht1 n)
    rw [RBM.Ind.scaleFacts_etaT_div_etaT (hE n)]
    have hρ1 := iterationsA_one_le_ratio hsu hu1
    have hρ := iterationsA_rho_le sz hsu hut (ht1 n) hn.1
    have hA0 : 0 < sz.STAI n := lt_of_lt_of_le one_pos hA
    have h2A : 0 < 2 * sz.STAI n := by positivity
    have hBt : 0 < sz.Bctl n (t n) := st_Bctl_pos sz (ht1 n)
    have hlow := iterationsA_BI_lower sz hst (ht1 n) (hreg.2 n) hlam
    have hB : sz.Bctl n (t n) ^ (-𝔠d) ≤ (2 * sz.STAI n) ^ 𝔠d := by
      calc sz.Bctl n (t n) ^ (-𝔠d) ≤ (1 / (2 * sz.STAI n)) ^ (-𝔠d) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
        _ = (2 * sz.STAI n) ^ 𝔠d := by
            rw [one_div, Real.inv_rpow h2A.le, Real.rpow_neg h2A.le, inv_inv]
    have hρR : (1 - s n) / (1 - q.1.2) ≤ 2 ^ 𝔠d * sz.STAI n ^ 𝔠d := by
      rw [← Real.mul_rpow (by norm_num) hA0.le]; exact hρ.trans hB
    have hρ0 : 0 ≤ (1 - s n) / (1 - q.1.2) := by linarith
    have hsq : ((1 - s n) / (1 - q.1.2)) ^ 2 ≤ 2 * sz.STAI n ^ (1 / 8 : ℝ) := by
      calc ((1 - s n) / (1 - q.1.2)) ^ 2 ≤ (2 ^ 𝔠d * sz.STAI n ^ 𝔠d) ^ 2 := pow_le_pow_left₀ hρ0 hρR 2
        _ = 2 ^ (2 * 𝔠d) * sz.STAI n ^ (2 * 𝔠d) := by
            rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (sz.STAI n ^ 𝔠d),
              ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hA0.le]
            norm_num; ring_nf
        _ ≤ 2 * sz.STAI n ^ (1 / 8 : ℝ) := by
            have h1 : (2 : ℝ) ^ (2 * 𝔠d) ≤ 2 := by
              calc (2 : ℝ) ^ (2 * 𝔠d) ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 2 := Real.rpow_one 2
            have h2 : sz.STAI n ^ (2 * 𝔠d) ≤ sz.STAI n ^ (1 / 8 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hA (by linarith)
            have h3 : 0 ≤ sz.STAI n ^ (2 * 𝔠d) := Real.rpow_nonneg hA0.le _
            exact mul_le_mul h1 h2 h3 (by norm_num)
    refine ⟨hρ1, hsq, ?_⟩
    have h78 : sz.STAI n ^ (1 / 8 : ℝ) * sz.STAI n ^ (7 / 8 : ℝ) = sz.STAI n := by
      rw [← Real.rpow_add hA0]; norm_num
    have h7 : 0 ≤ sz.STAI n ^ (7 / 8 : ℝ) := Real.rpow_nonneg hA0.le _
    calc 2 * (sz.STAI n)⁻¹ * ((1 - s n) / (1 - q.1.2)) ^ 2 * sz.STAI n ^ (7 / 8 : ℝ)
        ≤ 2 * (sz.STAI n)⁻¹ * (2 * sz.STAI n ^ (1 / 8 : ℝ)) * sz.STAI n ^ (7 / 8 : ℝ) := by
          gcongr
      _ = 4 * ((sz.STAI n)⁻¹ * (sz.STAI n ^ (1 / 8 : ℝ) * sz.STAI n ^ (7 / 8 : ℝ))) := by ring
      _ = 2 * 2 := by rw [h78]; field_simp; norm_num
  · filter_upwards [iterationsA_WO_AI sz hWO] with n hn
    have hA0 : 0 < sz.STAI n := lt_of_lt_of_le one_pos hn.2
    have hle : sz.STAI n ^ (3 / 4 : ℝ) ≤ sz.STAI n := by
      calc sz.STAI n ^ (3 / 4 : ℝ) ≤ sz.STAI n ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn.2 (by norm_num)
        _ = sz.STAI n := Real.rpow_one _
    calc 2 * (sz.STAI n)⁻¹ * sz.STAI n ^ (3 / 4 : ℝ) ≤ 2 * (sz.STAI n)⁻¹ * sz.STAI n := by gcongr
      _ = 2 := by field_simp
  · filter_upwards [iterationsA_WO_AI sz hWO] with n hn w
    obtain ⟨hlam, hA⟩ := hn
    have hsw : s n ≤ (w : ℝ) := (w.2).1
    have hwt : (w : ℝ) ≤ t n := (w.2).2
    refine ⟨?_, iterationsA_BI_upper sz hd (by linarith [hreg.1 n]) hlam⟩
    have := iterationsA_BI_lower sz hsw (lt_of_le_of_lt hwt (ht1 n)) (hreg.2 n) hlam
    rwa [one_div] at this

/-- **The scale facts of the step, case (ii)** (`A = (W^{-d}B_{s,0})⁻¹`, `T = A^{-1+𝔠d}`, `cB = cv = K = 1`; `3_5:1575-1595`):
under `(con_st_ind)`, `t < 1`, `|E| < 2` and `0 < 𝔠d ≤ 1/24`; the regime `STCaseII` is not used (it enters through `A`). -/
theorem iterationsA_scale_II {E s t : ℕ → ℝ} {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 24)
    (hcon : sz.STConStInd 𝔠d s t) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) :
    IterationsAScale sz E s t (fun n => sz.STAII s n) (fun n => (sz.STAII s n) ^ (-1 + 𝔠d)) 1 1 1 := by
  have hAnn : ∀ n, 0 ≤ sz.STAII s n := fun n => inv_nonneg.2 (iterationsA_Bctl_nonneg sz n _)
  have hA1 : ∀ᶠ n in atTop, 1 ≤ sz.STAII s n := by
    filter_upwards [iterationsA_con_aux sz h𝔠d hcon ht1] with n hn
    have hst : s n ≤ t n := hn.1.le
    have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (lt_of_le_of_lt hst (ht1 n))
    have hmono : sz.Bctl n (s n) ≤ sz.Bctl n (t n) := STBctl_mono sz n hst (ht1 n)
    exact (one_le_inv₀ hBs).2 (hmono.trans hn.2.le)
  refine ⟨by norm_num, by norm_num, by norm_num, hAnn, fun n => Real.rpow_nonneg (hAnn n) _, ht1, hA1, ?_, ?_, ?_⟩
  · filter_upwards [hcon, hA1, iterationsA_con_aux sz h𝔠d hcon ht1] with n hn hA hcn q
    have hsu : s n ≤ q.1.2 := q.2.1.trans q.2.2.1
    have hut : q.1.2 ≤ t n := q.2.2.2
    have hst : s n ≤ t n := hsu.trans hut
    have hu1 : q.1.2 < 1 := lt_of_le_of_lt hut (ht1 n)
    rw [RBM.Ind.scaleFacts_etaT_div_etaT (hE n)]
    have hρ1 := iterationsA_one_le_ratio hsu hu1
    have hρ := iterationsA_rho_le sz hsu hut (ht1 n) hn.1
    have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (lt_of_le_of_lt hst (ht1 n))
    have hmono : sz.Bctl n (s n) ≤ sz.Bctl n (t n) := STBctl_mono sz n hst (ht1 n)
    have hA0 : 0 < sz.STAII s n := lt_of_lt_of_le one_pos hA
    have hB : sz.Bctl n (t n) ^ (-𝔠d) ≤ sz.STAII s n ^ 𝔠d := by
      calc sz.Bctl n (t n) ^ (-𝔠d) ≤ sz.Bctl n (s n) ^ (-𝔠d) :=
            Real.rpow_le_rpow_of_nonpos hBs hmono (by linarith)
        _ = sz.STAII s n ^ 𝔠d := by
            unfold STAII
            rw [Real.inv_rpow hBs.le, Real.rpow_neg hBs.le]
    have hρR := hρ.trans hB
    have hρ0 : 0 ≤ (1 - s n) / (1 - q.1.2) := by linarith
    have hsq : ((1 - s n) / (1 - q.1.2)) ^ 2 ≤ sz.STAII s n ^ (2 * 𝔠d) := by
      calc ((1 - s n) / (1 - q.1.2)) ^ 2 ≤ (sz.STAII s n ^ 𝔠d) ^ 2 := pow_le_pow_left₀ hρ0 hρR 2
        _ = sz.STAII s n ^ (2 * 𝔠d) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num; ring_nf
    refine ⟨hρ1, ?_, ?_⟩
    · rw [one_mul]
      exact hsq.trans (Real.rpow_le_rpow_of_exponent_le hA (by linarith))
    · calc sz.STAII s n ^ (-1 + 𝔠d) * ((1 - s n) / (1 - q.1.2)) ^ 2 * sz.STAII s n ^ (7 / 8 : ℝ)
          ≤ sz.STAII s n ^ (-1 + 𝔠d) * sz.STAII s n ^ (2 * 𝔠d) * sz.STAII s n ^ (7 / 8 : ℝ) := by
            gcongr
        _ = sz.STAII s n ^ (-1 + 𝔠d + 2 * 𝔠d + 7 / 8) := by
            rw [← Real.rpow_add hA0, ← Real.rpow_add hA0]
        _ ≤ 1 * 1 := by
            rw [mul_one]
            exact Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith)
  · filter_upwards [hA1] with n hA
    have hA0 : 0 < sz.STAII s n := lt_of_lt_of_le one_pos hA
    calc sz.STAII s n ^ (-1 + 𝔠d) * sz.STAII s n ^ (3 / 4 : ℝ) = sz.STAII s n ^ (-1 + 𝔠d + 3 / 4) := by
          rw [← Real.rpow_add hA0]
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith)
  · filter_upwards [RBM.Ind.scaleFacts_R2 sz h𝔠d hcon (Eventually.of_forall ht1), iterationsA_con_aux sz h𝔠d hcon ht1]
      with n hR2 hcn w
    have hsw : s n ≤ (w : ℝ) := (w.2).1
    have hwt : (w : ℝ) ≤ t n := (w.2).2
    have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (lt_of_le_of_lt (hsw.trans hwt) (ht1 n))
    refine ⟨?_, ?_⟩
    · have hmono : sz.Bctl n (s n) ≤ sz.Bctl n (w : ℝ) :=
        STBctl_mono sz n hsw (lt_of_le_of_lt hwt (ht1 n))
      rw [one_mul]
      unfold STAII
      rwa [inv_inv]
    · have := hR2 (w : ℝ) hsw hwt
      refine this.trans (le_of_eq ?_)
      unfold STAII
      rw [Real.inv_rpow hBs.le, ← Real.rpow_neg hBs.le]
      congr 1; ring

end RBM.Gauss.Sizes

/-! ## 9. Compiled nonempty instances (`d = 3`)

The real inequalities and the `Ψ`-calculus at `b = A^{1/8} = 2` (`A = 256`), `ρ = 3/2`, `T = 1/256`, `cB = 1`, `cv = 2`,
`K = 2` (every hypothesis holds: `ρ² = 9/4 ≤ K b = 4`, `T A^{3/4} = 1/4 ≤ 1`, `T ρ² A^{7/8} = 9/8 ≤ 2`); the scale facts and the
step at the merged second size sequence `szB` (`d = 3`, `L = 4`, `W_n = n + 4`, `ilambda = 1`, flow `zB`), case (i) at
`(s,t) = (7/8, 15/16)` and case (ii) at `(15/16, 31/32)`, `𝔠d = 1/100`; the probe helpers and the odd chain bound at `szB`, `n = 0`,
`E = 0`, `v = 1/2`.  What stays a hypothesis of the instance of `iterationsA_step` is stochastic: `STXiBoot`, `(rela_XILXILK)`,
the averaged law, the a priori bound and the two induction hypotheses. -/

namespace RBM.Gauss.IterationsAInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Path Filter

private theorem r256_18 : (256 : ℝ) ^ (1 / 8 : ℝ) = 2 := by
  rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

private theorem r256_34 : (256 : ℝ) ^ (3 / 4 : ℝ) = 64 := by
  rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

private theorem r256_78 : (256 : ℝ) ^ (7 / 8 : ℝ) = 128 := by
  rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `iterationsA_ineq_long` at `b = 2`, `ρ = 3/2`, `e = 4`, `T = 1/256`, `N = 3`, `m = 4`. -/
example : 1 + (1 / 256 : ℝ) * (2 ^ 6 + (3 / 2 : ℝ) ^ (4 - 1) * (2 * 4)) ≤
    (1 + 1 + 1 * 2) * (2 ^ 6 + (3 / 2 : ℝ) ^ (3 - 1) * 4) :=
  RBM.Ind.iterationsA_ineq_long (b := 2) (ρ := 3 / 2) (e := 4) (T := 1 / 256) (cB := 1) (K := 2) (N := 3) (m := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `iterationsA_ineq_quad` at `N = 6`, `m = 3`, `j = 5`, `x_j = 2`, `x_a = 6/5`, `x_b = 11/10`. -/
example : (2 : ℝ) * ((6 / 5) * (11 / 10)) ^ (1 / 2 : ℝ) ≤
    (2 + 3 * 1 + 1 * 2) * (2 ^ 6 + (3 / 2 : ℝ) ^ (6 - 1) * 4) :=
  RBM.Ind.iterationsA_ineq_quad (b := 2) (ρ := 3 / 2) (e := 4) (T := 1 / 256) (cB := 1) (K := 2) (N := 6) (m := 3)
    (j := 5) (xj := 2) (xa := 6 / 5) (xb := 11 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `iterationsA_ineq_chain` at `N = 3`, `p = 1`, `w = 3/2`, `x = 5`, `y = 2`. -/
example : (2 : ℝ) * (3 / 2) * ((5 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / (4 * ((1 : ℕ) : ℝ)))) ≤
    (2 * 2 * 2 + 2 * 2 ^ 2 * (1 + 1) * 2 + 2 * 2 ^ 2 * 1 * 2) * (2 ^ 6 + (3 / 2 : ℝ) ^ (3 - 1) * 4) :=
  RBM.Ind.iterationsA_ineq_chain (b := 2) (ρ := 3 / 2) (e := 4) (T := 1 / 256) (cB := 1) (cv := 2) (K := 2)
    (w := 3 / 2) (x := 5) (y := 2) (N := 3) (p := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `iterationsA_boot_bound` at `N = 3`, `k = 2`, `p = 7 = N + 4`, `A = 256`, `ρ = 3/2`, `T = 1/256`, `B_u = 1/100`, with the controls
`XLv`, `XLKv` of the step (the envelopes are `iterationsA_XLv_le_pred`, `iterationsA_XLv_le`, `iterationsA_XLv_le_chain`,
`iterationsA_XLv_four_p`). -/
example : ∃ C : ℝ, 0 < C ∧
    STbootRHS 1 (iterationsA_XLv 256 (3 / 2) (1 / 256) 1 2 3 2 7) (iterationsA_XLKv 256 (3 / 2) 2) (1 / 100) 3 7 ≤
      C * STPsi 256 (3 / 2) 3 2 := by
  obtain ⟨C, hC0, hC⟩ := iterationsA_boot_bound 1 2 2 (by norm_num) (by norm_num) (by norm_num) 3 2 (by norm_num)
    (by norm_num)
  refine ⟨C, hC0, hC 256 (3 / 2) (1 / 256) (1 / 100) 7 _ _ (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rw [r256_18]; norm_num
  · rw [r256_34]; norm_num
  · rw [r256_78]; norm_num
  · exact fun m hm1 hm2 => iterationsA_XLv_le_pred (by norm_num) (by norm_num) (by norm_num) (by norm_num) hm2
  · exact fun m hm1 hm2 => iterationsA_XLv_le (by norm_num) (by norm_num) (by norm_num) hm2
  · exact fun m => iterationsA_XLv_ge_one (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ _ m
  · refine iterationsA_XLv_le_chain (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num)
    rw [r256_34]; norm_num
  · exact (iterationsA_XLv_four_p _ _ _ _ _ (by norm_num) (by norm_num)).le
  · exact fun m => iterationsA_XLKv_ge_one (by norm_num) (by norm_num) _ m
  · exact fun m hm1 hm2 => iterationsA_XLKv_le (by norm_num) (by norm_num)

/-- `iterationsA_chain_term` at the same data: the chain term `B_u^{-1/(4p)} Ξ̂_{2N-1}^{1/2} Ξ̂_{4p}^{1/(4p)} ≤ C Ψ(N,k)`,
`x = XLv_{2N-1}`, `y = XLv_{4p}`. -/
example : ∃ C : ℝ, 0 < C ∧
    (1 / 100 : ℝ) ^ (-(1 : ℝ) / (4 * ((7 : ℕ) : ℝ))) *
        (iterationsA_XLv 256 (3 / 2) (1 / 256) 1 2 3 2 7 (2 * 3 - 1)) ^ (1 / 2 : ℝ) *
        (iterationsA_XLv 256 (3 / 2) (1 / 256) 1 2 3 2 7 (4 * 7)) ^ (1 / (4 * ((7 : ℕ) : ℝ))) ≤
      C * STPsi 256 (3 / 2) 3 2 := by
  obtain ⟨C, hC0, hC⟩ := iterationsA_chain_term 1 2 2 (by norm_num) (by norm_num) (by norm_num) 3 2 (by norm_num)
    (by norm_num)
  refine ⟨C, hC0, hC 256 (3 / 2) (1 / 256) (1 / 100) _ _ 7 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) ?_ ?_ ?_ ?_⟩
  · rw [r256_18]; norm_num
  · rw [r256_78]; norm_num
  · exact iterationsA_XLv_ge_one (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ _ _
  · refine iterationsA_XLv_le_chain (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num)
    rw [r256_34]; norm_num
  · exact iterationsA_XLv_ge_one (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ _ _
  · exact (iterationsA_XLv_four_p _ _ _ _ _ (by norm_num) (by norm_num)).le

/-- The `Ψ`-calculus at `A = 256`, `ρ = 3/2`, `m = 3`, `k = 2`. -/
example : STPsi 256 (3 / 2) 3 2 = ((256 : ℝ) ^ (1 / 8 : ℝ)) ^ 6 + (3 / 2 : ℝ) ^ (3 - 1) * (256 : ℝ) ^ (1 - ((2 : ℕ) : ℝ) / 8) :=
  iterationsA_STPsi_eq (by norm_num) _ _ _

example : STPsi 256 (3 / 2) 3 (2 - 1) = ((256 : ℝ) ^ (1 / 8 : ℝ)) ^ 6 +
    (3 / 2 : ℝ) ^ (3 - 1) * ((256 : ℝ) ^ (1 / 8 : ℝ) * (256 : ℝ) ^ (1 - ((2 : ℕ) : ℝ) / 8)) :=
  iterationsA_STPsi_pred (by norm_num) _ _ (by norm_num)

example : (256 : ℝ) ^ (1 - (((2 - 1 : ℕ)) : ℝ) / 8) = (256 : ℝ) ^ (1 / 8 : ℝ) * (256 : ℝ) ^ (1 - ((2 : ℕ) : ℝ) / 8) :=
  iterationsA_rpow_pred (by norm_num) (by norm_num)

example : 0 ≤ STPsi 256 (3 / 2) 3 2 := iterationsA_STPsi_nonneg (by norm_num) (by norm_num) _ _
example : 1 ≤ STPsi 256 (3 / 2) 3 2 := iterationsA_one_le_STPsi (by norm_num) (by norm_num) _ _
example : STPsi 256 (3 / 2) 2 2 ≤ STPsi 256 (3 / 2) 3 2 :=
  iterationsA_STPsi_mono_n (by norm_num) (by norm_num) (by norm_num) 2
example : STPsi 256 (3 / 2) 3 2 ≤ STPsi 256 (3 / 2) 3 (2 - 1) :=
  iterationsA_STPsi_anti_k (by norm_num) (by norm_num) 3 (by norm_num)

/-! ### The probe helpers and the odd chain bound at `szB` -/

private theorem szB_hsize : Tendsto szB.size atTop atTop := tendsto_size szB szB_tendsto

private theorem szB_B_pos : 0 < szB.Bctl 0 (1 / 2) := st_Bctl_pos szB (n := 0) (by norm_num)

/-- `st_one_le_XiL`, `st_one_le_XiLK` at `szB`, `n = 0`, `E = 0`, `v = 1/2`, `ω ≡ 0`, `k = 3`. -/
example : 1 ≤ szB.STXiL 0 0 (1 / 2) 3 (fun _ => 0) := st_one_le_XiL szB (n := 0) (E := 0) (v := 1 / 2) 3 _ szB_B_pos
example : 1 ≤ szB.STXiLK 0 0 (1 / 2) 3 (fun _ => 0) := st_one_le_XiLK szB (n := 0) (E := 0) (v := 1 / 2) 3 _ szB_B_pos

/-- `st_prec_one_add_sup` and `st_prec_of_xi` at `szB`: `U = Unit`, `V = Fin 2`, `f ≡ 1/2`, `B ≡ 1`. -/
example : szB.Prec (U := fun _ => Unit)
    (fun _ _ _ => 1 + Finset.univ.sup' Finset.univ_nonempty (fun _ : Fin 2 => (1 / 2 : ℝ)) / (1 : ℝ)) (fun _ _ _ => 1) :=
  st_prec_one_add_sup szB (U := fun _ => Unit) (V := fun _ => Fin 2) szB_hsize (fun _ _ _ _ => (1 / 2 : ℝ))
    (fun _ _ => 1) (fun _ _ => one_pos)
    (prec_of_le szB (fun _ _ _ => zero_le_one) (fun _ _ _ => by norm_num))

example : szB.Prec (U := fun _ => Unit × Fin 2) (fun _ _ _ => (1 / 2 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  st_prec_of_xi szB (U := fun _ => Unit) (V := fun _ => Fin 2) (fun _ _ _ _ => (1 / 2 : ℝ)) (fun _ _ => 1)
    (fun _ _ => one_pos)
    (st_prec_one_add_sup szB (U := fun _ => Unit) (V := fun _ => Fin 2) szB_hsize (fun _ _ _ _ => (1 / 2 : ℝ))
      (fun _ _ => 1) (fun _ _ => one_pos) (prec_of_le szB (fun _ _ _ => zero_le_one) (fun _ _ _ => by norm_num)))

/-- `iterationsA_STmaxL_eq`, `iterationsA_STXiL_eq` at the same data. -/
example : szB.STmaxL 0 0 (1 / 2) 3 (fun _ => 0) = RBM.Ind.loopMax 3 (szB.L 0) (szB.W 0)
    (blockMat 3 (szB.L 0) (szB.W 0) (szB.seqHflow 0 (1 / 2) (fun _ => 0))) (zt 0 (1 / 2)) 3 :=
  iterationsA_STmaxL_eq szB 0 0 (1 / 2) 3 _

example : szB.STXiL 0 0 (1 / 2) 3 (fun _ => 0) = 1 + RBM.Ind.loopXi 3 (szB.L 0) (szB.W 0)
    (blockMat 3 (szB.L 0) (szB.W 0) (szB.seqHflow 0 (1 / 2) (fun _ => 0))) (zt 0 (1 / 2)) (szB.Bctl 0 (1 / 2))⁻¹ 3 :=
  iterationsA_STXiL_eq szB 0 0 (1 / 2) 3 _

/-- The odd chain bound at `N = 3`: `Ξ̂_5 ≤ 1 + B⁻¹ ((Ξ̂_4 Ξ̂_2)(Ξ̂_2 Ξ̂_2))^{1/2}`. -/
example : szB.STXiL 0 0 (1 / 2) (2 * 3 - 1) (fun _ => 0) ≤ 1 + (szB.Bctl 0 (1 / 2))⁻¹ *
    ((szB.STXiL 0 0 (1 / 2) (2 * ((3 + 1) / 2)) (fun _ => 0) * szB.STXiL 0 0 (1 / 2) (2 * (3 / 2)) (fun _ => 0)) *
      (szB.STXiL 0 0 (1 / 2) (2 * (3 / 2)) (fun _ => 0) * szB.STXiL 0 0 (1 / 2) (2 * ((3 - 1) / 2)) (fun _ => 0))) ^
        (1 / 2 : ℝ) :=
  iterationsA_xiL_odd_le szB 0 (E := 0) (v := 1 / 2) (fun _ => 0) szB_B_pos (by norm_num)

/-! ### The scale facts and the step at `szB` -/

private theorem zB_abs_E (n : ℕ) : |STflowE zB n| < 2 := abs_lemE_lt_two (by simp [zB])

private theorem szB_conI {𝔠d : ℝ} (h : 0 < 𝔠d) :
    szB.STConStInd 𝔠d (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h

private theorem szB_conII {𝔠d : ℝ} (h : 0 < 𝔠d) :
    szB.STConStInd 𝔠d (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h

/-- `iterationsA_scale_I` at `(szB, zB, 7/8, 15/16)`, `𝔠d = 1/100`, `𝔡 = 1/10`, `d = 3 ≥ 2`. -/
private theorem szB_scaleI : IterationsAScale szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)
    (fun n => szB.STAI n) (fun n => 2 * (szB.STAI n)⁻¹) 2 2 2 :=
  iterationsA_scale_I szB (by norm_num) (E := STflowE zB) (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num)
    (by norm_num) szB_regIterI (szB_conI (by norm_num)) szB_WO (fun _ => by norm_num) zB_abs_E

/-- `iterationsA_scale_II` at `(szB, zB, 15/16, 31/32)`, `𝔠d = 1/100`. -/
private theorem szB_scaleII : IterationsAScale szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)
    (fun n => szB.STAII (fun _ => 15 / 16) n) (fun n => (szB.STAII (fun _ => 15 / 16) n) ^ (-1 + 1 / 100 : ℝ)) 1 1 1 :=
  iterationsA_scale_II szB (E := STflowE zB) (𝔠d := 1 / 100) (by norm_num) (by norm_num) (szB_conII (by norm_num))
    (fun _ => by norm_num) zB_abs_E

example : IterationsAScale szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => szB.STAI n)
    (fun n => 2 * (szB.STAI n)⁻¹) 2 2 2 := szB_scaleI

example : IterationsAScale szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)
    (fun n => szB.STAII (fun _ => 15 / 16) n) (fun n => (szB.STAII (fun _ => 15 / 16) n) ^ (-1 + 1 / 100 : ℝ)) 1 1 1 :=
  szB_scaleII

/-- **`iterationsA_step`, case (i)**, at `(szB, zB, 7/8, 15/16)`, `(N,k) = (3,2)`: `Ψ` with `A = ilambda² W^d`.  The stochastic
premises (`STXiBoot`, `(rela_XILXILK)`, the averaged law, the a priori bound, the induction hypotheses at `(2,2)` and at
`(r,1)`, `2 ≤ r ≤ 5`) stay hypotheses; every deterministic hypothesis is discharged by `szB_scaleI`. -/
example (hboot : STXiBoot szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hrela : ∀ m, 1 ≤ m → szB.Prec (U := STPair (fun _ => (7 / 8 : ℝ)) (fun _ => (15 / 16 : ℝ)))
      (fun n q ω => szB.STXiL n (STflowE zB n) q.1.1 m ω)
      (fun n q ω => 1 + szB.Bctl n q.1.1 * szB.STXiLK n (STflowE zB n) q.1.1 m ω))
    (havg : szB.Prec (U := STPair (fun _ => (7 / 8 : ℝ)) (fun _ => (15 / 16 : ℝ)))
      (fun n q ω => szB.STXiLK n (STflowE zB n) q.1.1 1 ω) (fun _ _ _ => 1))
    (hapri : ∀ m, 1 ≤ m → szB.Prec (U := STPair (fun _ => (7 / 8 : ℝ)) (fun _ => (15 / 16 : ℝ)))
      (fun n q ω => szB.STXiL n (STflowE zB n) q.1.1 m ω)
      (fun n q _ => (etaT (STflowE zB n) (7 / 8) / etaT (STflowE zB n) q.1.2) ^ (m - 1)))
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ 3 →
      STIterHyp szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => szB.STAI n) r 2)
    (IH2 : ∀ r, 2 ≤ r → r ≤ 3 + 2 →
      STIterHyp szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => szB.STAI n) r (2 - 1)) :
    STIterHyp szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => szB.STAI n) 3 2 :=
  iterationsA_step szB szB_hsize szB_scaleI hboot hrela havg hapri (by norm_num) (by norm_num) IH1 IH2

/-- **`iterationsA_step`, case (ii)**, at `(szB, zB, 15/16, 31/32)`, `(N,k) = (2,1)`: `Ψ` with `A = (W^{-d}B_{s,0})⁻¹`. -/
example (hboot : STXiBoot szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32))
    (hrela : ∀ m, 1 ≤ m → szB.Prec (U := STPair (fun _ => (15 / 16 : ℝ)) (fun _ => (31 / 32 : ℝ)))
      (fun n q ω => szB.STXiL n (STflowE zB n) q.1.1 m ω)
      (fun n q ω => 1 + szB.Bctl n q.1.1 * szB.STXiLK n (STflowE zB n) q.1.1 m ω))
    (havg : szB.Prec (U := STPair (fun _ => (15 / 16 : ℝ)) (fun _ => (31 / 32 : ℝ)))
      (fun n q ω => szB.STXiLK n (STflowE zB n) q.1.1 1 ω) (fun _ _ _ => 1))
    (hapri : ∀ m, 1 ≤ m → szB.Prec (U := STPair (fun _ => (15 / 16 : ℝ)) (fun _ => (31 / 32 : ℝ)))
      (fun n q ω => szB.STXiL n (STflowE zB n) q.1.1 m ω)
      (fun n q _ => (etaT (STflowE zB n) (15 / 16) / etaT (STflowE zB n) q.1.2) ^ (m - 1)))
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ 2 →
      STIterHyp szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => szB.STAII (fun _ => 15 / 16) n) r 1)
    (IH2 : ∀ r, 2 ≤ r → r ≤ 2 + 2 →
      STIterHyp szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => szB.STAII (fun _ => 15 / 16) n) r (1 - 1)) :
    STIterHyp szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => szB.STAII (fun _ => 15 / 16) n) 2 1 :=
  iterationsA_step szB szB_hsize szB_scaleII hboot hrela havg hapri (by norm_num) (by norm_num) IH1 IH2

/-! ### The plumbing lemmas at `szB` (the stochastic pin stays a hypothesis) -/

/-- `iterationsA_avg_of_STAvgU` at `(szB, zB, 7/8, 15/16)`. -/
example (h : STAvgU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    szB.Prec (U := STPair (fun _ => (7 / 8 : ℝ)) (fun _ => (15 / 16 : ℝ)))
      (fun n q ω => szB.STXiLK n (STflowE zB n) q.1.1 1 ω) (fun _ _ _ => 1) :=
  iterationsA_avg_of_STAvgU szB szB_hsize (fun _ => by norm_num) h

/-- `iterationsA_apriori_of_lRB1` at `(szB, zB, 7/8, 15/16)`, `m = 3`. -/
example (h : STStep1Loop szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    szB.Prec (U := STPair (fun _ => (7 / 8 : ℝ)) (fun _ => (15 / 16 : ℝ)))
      (fun n q ω => szB.STXiL n (STflowE zB n) q.1.1 3 ω)
      (fun n q _ => (etaT (STflowE zB n) (7 / 8) / etaT (STflowE zB n) q.1.2) ^ (3 - 1)) :=
  iterationsA_apriori_of_lRB1 szB szB_hsize (fun _ => by norm_num) zB_abs_E h 3 (by norm_num)

/-- `iterationsA_rela_of_K` at `(szB, zB, 7/8, 15/16)`, `m = 2`, from the uniform `𝒦`-loop bound. -/
example (hK : szB.Prec (U := fun n => STPair (fun _ => (7 / 8 : ℝ)) (fun _ => (15 / 16 : ℝ)) n ×
      ((Fin 2 → Bool) × (Fin 2 → Zd 3 (szB.L n))))
      (fun n p _ => ‖szB.STKloop n (STflowE zB n) p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => szB.Bctl n p.1.1.1 ^ (2 - 1))) :
    szB.Prec (U := STPair (fun _ => (7 / 8 : ℝ)) (fun _ => (15 / 16 : ℝ)))
      (fun n q ω => szB.STXiL n (STflowE zB n) q.1.1 2 ω)
      (fun n q ω => 1 + szB.Bctl n q.1.1 * szB.STXiLK n (STflowE zB n) q.1.1 2 ω) :=
  iterationsA_rela_of_K szB szB_hsize (fun _ => by norm_num) 2 (by norm_num) hK

/-- The `≺` helpers at `szB` (`U = Unit`): `ξ = 1/2 ≺ ζ = 1`, `ζ ≤ 2`, `ξ ≤ 1`, `c = 2`. -/
example : szB.Prec (U := fun _ => Unit) (fun _ _ _ => (1 / 2 : ℝ)) (fun _ _ _ => 2) :=
  iterationsA_prec_mono_right szB (prec_of_le szB (fun _ _ _ => zero_le_one) (fun _ _ _ => by norm_num))
    (Eventually.of_forall fun _ _ _ => by norm_num)

example : szB.Prec (U := fun _ => Unit) (fun _ _ _ => (1 / 4 : ℝ)) (fun _ _ _ => 1) :=
  iterationsA_prec_mono_left szB (ξ' := fun _ _ _ => (1 / 2 : ℝ))
    (Eventually.of_forall fun _ _ _ => by norm_num)
    (prec_of_le szB (fun _ _ _ => zero_le_one) (fun _ _ _ => by norm_num))

example : szB.Prec (U := fun _ => Unit) (fun _ _ _ => (1 / 2 : ℝ)) (fun _ _ _ => 1) :=
  iterationsA_prec_absorb szB szB_hsize (c := 2) (Eventually.of_forall fun _ _ _ => zero_le_one)
    (prec_of_le szB (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num))

example : szB.Prec (U := fun _ => Unit) (fun _ _ _ => 1 + (2 : ℝ) * (1 / 4)) (fun _ _ _ => 1 + (2 : ℝ) * (1 / 2)) :=
  iterationsA_prec_one_add_mul szB szB_hsize (c := fun _ _ => 2) (fun _ _ => by norm_num)
    (fun _ _ _ => by norm_num) (prec_of_le szB (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num))

example : szB.Prec (U := fun _ => Unit) (fun _ _ _ => (1 / 4 : ℝ) ^ (1 / 2 : ℝ)) (fun _ _ _ => (1 / 2 : ℝ) ^ (1 / 2 : ℝ)) :=
  iterationsA_prec_rpow szB (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num) (θ := 1 / 2) (by norm_num)
    (prec_of_le szB (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num))

end RBM.Gauss.IterationsAInst
