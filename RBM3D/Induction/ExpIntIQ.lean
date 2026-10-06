/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ExpIntI
import RBM3D.Induction.QopDecay
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.QopNorm
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.Step6Pins
import RBM3D.Induction.ExpWardI
import RBM3D.Induction.ExpIntII
import RBM3D.Induction.ExpDuhamel
import RBM3D.Induction.LemDecCalELip
import RBM3D.Loop.GLoopFlow
import RBM3D.Kernel.PropT
import RBM3D.Evolution.Prec

/-!
# S6-09b (T2257): the `𝒬` conjunct of the integrated estimate of regime (i), by transfer from `ϑ*`

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:97,104-132` (regime (i) with `σ₁ ≠ σ₂`:
`(eq:EPL-K)`, `(int_K-L+QE)`, `(eq:boundELKQ1)`, `(eq:boundcommutator)`),
`paper/tex/3_5_Loop_Hierarchy.tex:1204-1252` (`Def:QtPt`, `rmk:choosechi`), `:1284-1289` (`lem_+Q`),
`:1659` (`(sum_res_2)`).

This file proves the merged primed pin `STExpIntI'` (`Induction/ExpIntI.lean:71`, T2239; unchanged)
and its second conjunct `STExpIntQConcl'`, by the **transfer** of DECISIONS §81 (2), supervisor
`2026-10-06-0255.md` §2.2 route (d): the conclusion of `STExpIntQConcl'` depends on the mollifier
`ϑ` only through `ϑ_s` and `ϑ_u`, never through `∂ϑ`, so it follows from the same statement for
**one** decaying mollifier, the explicit `ϑ*_n = QopAlgebra_mollifier d L_n 1 ilambda_n`
(`QopAlgebra.lean:345`; derivative decay `QopDecay.lean:497`).
* `expIntIQ_star_props`: `ϑ*` is admissible, constants `((1 + 40 d) 6^d, 1/2)` (target 1);
* `expIntIQ_Qop_sub`, `expIntIQ_diff_sumZero`: changing the mollifier changes `𝒬` by the sum-zero
  tensor `(𝒫A)(ϑ - ϑ')` (targets 2, 3);
* `expIntIQ_src_sumZero`, `expIntIQ_src_decay`: the `𝒬`-source `A*_v` of `ϑ*` is sum-zero and
  `(v, ε', D)`-decaying, the hypotheses of `(sum_res_2)` (targets 4, 5; `stQop_sub_fastDecay`,
  `QopDecay_*`);
* `expIntIQ_ini`: `𝒰_{s,u} 𝒬*_s f_s = 𝒰_{s,u} 𝒬^ϑ_s f_s + 𝒰_{s,u} R_s` with
  `R_s = (𝒫 f_s)(ϑ_s - ϑ*_s)` sum-zero, deterministic, decaying and `‖R_s‖ ≺ B_s³` (first Ward
  conjunct), through the sum-zero branch of `expIntI_kernel_unif` (ratio² `≤ 4`) (target 6);
* `expIntIQ_star_bound`: the paper's route `6:109-132` for `ϑ*`: `𝒬`-Duhamel
  (`stExpDuhamelQ_holds`), the sup bound of `A*_v` (`lem_+Q` on the drift, the second Ward conjunct
  for `ϑ*`), the kernel, `∫ (1-v)⁻¹ ≤ 2 log L`, rates `≤ 4 T_u` (target 7);
* `expIntIQ_back`, `expIntIQ_concl`: back to `ϑ` by
  `𝒬^ϑ_u f_u = 𝒬*_u f_u + (𝒫 f_u)ϑ*_u - (𝒫 f_u)ϑ_u`; assembly (targets 8, 9);
* `stExpIntI'_holds`, `stStep6I_of_LW`: the pin, and Step 6 in regime (i) with only `LWtermEXP` open
  (targets 10, 11).

The kernel `(sum_res_2)` asks `(sumAzero)` for **every** `n` and `v`, while the mollifier hypotheses
are eventual and the source needs `0 < ilambda_n`, `0 ≤ v < 1`: the kernel lemma is applied to the
*guarded* families `if (guard) then 𝒜_v else 0`, equal to the real tensors eventually on `[s_n, u]`.
The side conditions of the decay lemmas (`L^d ≤ W^K`, `(1-v)⁻¹ ≤ W^K`, `‖·‖ ≤ W^{C₀}`, `K = 1/𝔠`)
are discharged from the flow: `(1-v)⁻¹ ≤ N` and `L^d ≤ N ≤ W^{1/𝔠}` (`expIntIQ_inv_le`),
`‖f_v‖ ≤ N³` (`expIntIQ_f_le`: `‖𝔼 𝓛‖ ≤ η_v⁻²`, `‖𝒦‖ ≤ (1-t)⁻¹`), `‖D_v‖ ≤ N⁶` (`expIntIQ_D_le`).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. The explicit family `ϑ*` and the algebra of the transfer (targets 1-3) -/

/-- **The explicit mollifier** `ϑ*_n = QopAlgebra_mollifier d (L_n) 1 (ilambda_n)` of `rmk:choosechi`
(`3_5:1250`) at `m = 1` (tensors of two indices), for every `n` (no case split: clause 1 holds for every
real `g` and `t`, `QopAlgebra_mollifier_sum`).  Supervisor `2026-10-06-0255.md` §2.2 step 1; the
vocabulary of the transfer (DECISIONS §81 (2)). -/
def expIntIQ_star {d : ℕ} (sz : Sizes d) : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ :=
  fun n => QopAlgebra_mollifier d (sz.L n) 1 (sz.lam n)

/-- **Target 1**: `ϑ*` is admissible eventually, with the constants `C* = (1 + 40 d) 6^d`, `c = 1/2` of
`QopAlgebra_mollifier_props` at `m = 1` (`0 < ilambda_n` eventually by `st6_lam_pos`, `3 ≤ L_n`).
The values of the mollifier constants occur only in the statements of this theorem and of `expIntIQ_back`
and in the instances (DECISIONS §73 (3)); the proofs use `expIntIQ_star_abs`. -/
theorem expIntIQ_star_props (d : ℕ) (sz : Sizes d) (𝔡 : ℝ) (h : sz.WO 𝔡) :
    ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) ((1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1)) (1 / 2)
      (expIntIQ_star sz n) := by
  filter_upwards [st6_lam_pos sz h] with n hn
  exact QopAlgebra_mollifier_props d (sz.L n) 1 (sz.three_le_L n) hn

/-- Target 1 with abstract positive constants: the form used in the proofs below, where only `0 < C`, `0 < c`
matter (the values of the mollifier constants occur only in the statements of `expIntIQ_star_props` and `expIntIQ_back` and in the instances). -/
private theorem expIntIQ_star_abs (d : ℕ) (sz : Sizes d) (𝔡 : ℝ) (h : sz.WO 𝔡) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (expIntIQ_star sz n) :=
  ⟨_, 1 / 2, by positivity, by norm_num, expIntIQ_star_props d sz 𝔡 h⟩

/-- **Target 2** (the algebra of the transfer): changing the mollifier changes `𝒬` by `(𝒫A)(ϑ - ϑ')`:
`𝒬^{ϑ'}A = 𝒬^{ϑ}A + (𝒫A)_{a₁}(ϑ_a - ϑ'_a)` (`Def:QtPt`, `(eq:sumzero_op)` `3_5:1210`). -/
theorem expIntIQ_Qop_sub (d L : ℕ) [NeZero L] (ϑ ϑ' : ℝ → (Fin 2 → Zd d L) → ℂ) (s : ℝ)
    (A : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    STQop (d := d) ϑ' s A a = STQop (d := d) ϑ s A a + STPsum (d := d) A (a 0) * (ϑ s a - ϑ' s a) := by
  unfold STQop
  ring

/-- **Target 3**: the difference `R = (𝒫A)(ϑ - ϑ')` of two admissible mollifiers is sum-zero (clause 1,
`(eq:suma1chi)`, of both): `Σ_{a₂} R_a = (𝒫A)_{a₁}(1 - 1) = 0` (`(sumAzero)`). -/
theorem expIntIQ_diff_sumZero (d L : ℕ) [NeZero L] (g C c C' c' : ℝ) (ϑ ϑ' : ℝ → (Fin 2 → Zd d L) → ℂ)
    (h : STMollifierProps (d := d) g C c ϑ) (h' : STMollifierProps (d := d) g C' c' ϑ')
    (s : ℝ) (A : (Fin 2 → Zd d L) → ℂ) :
    EKSumZero (fun a : Fin 2 → Zd d L => STPsum (d := d) A (a 0) * (ϑ s a - ϑ' s a)) := by
  intro i₀ hi₀ x
  have : i₀ = 0 := Fin.ext hi₀
  subst this
  have e : ∀ b ∈ Finset.univ.filter (fun b : Fin 2 → Zd d L => b 0 = x),
      STPsum (d := d) A (b 0) * (ϑ s b - ϑ' s b) = STPsum (d := d) A x * ϑ s b - STPsum (d := d) A x * ϑ' s b := by
    intro b hb
    rw [(Finset.mem_filter.1 hb).2]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h.1 s x, h'.1 s x]
  ring

/-! ## 2. The `ϑ*`-source is sum-zero (target 4) -/

/-- `𝒫` of the combination `X + (Y - Z) - W` of the shape of `STExpQsrc`. -/
private theorem expIntIQ_Psum_comb {d L : ℕ} [NeZero L] (X Y Z W : (Fin 2 → Zd d L) → ℂ) (x : Zd d L) :
    STPsum (d := d) (fun b => X b + (Y b - Z b) - W b) x =
      STPsum (d := d) X x + (STPsum (d := d) Y x - STPsum (d := d) Z x) - STPsum (d := d) W x := by
  unfold STPsum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- `𝒫 ((B ∘ a₁) V) = B · 𝒫 V` pointwise: if `𝒫 V = 0` then `𝒫 ((B ∘ a₁) V) = 0`. -/
private theorem expIntIQ_Psum_mul_zero {d L : ℕ} [NeZero L] (B : Zd d L → ℂ) (V : (Fin 2 → Zd d L) → ℂ)
    (x : Zd d L) (hV : STPsum (d := d) V x = 0) : STPsum (d := d) (fun b => B (b 0) * V b) x = 0 := by
  unfold STPsum at hV ⊢
  have e : ∀ b ∈ Finset.univ.filter (fun b : Fin 2 → Zd d L => b 0 = x), B (b 0) * V b = B x * V b := by
    intro b hb
    rw [(Finset.mem_filter.1 hb).2]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, hV, mul_zero]

/-- **Target 4**: the `𝒬`-source `A*_v = 𝒬*_v D_v + [𝒬*_v, Θ] f_v - (𝒫 f_v) ∂_vϑ*_v` (`STExpQsrc`,
`(int_K-L+QE)` `6:109-116`) of `ϑ*` is sum-zero, for every `n` with `0 < ilambda_n`, `|E| ≤ 2`,
`0 ≤ v < 1`: `QopAlgebra_Psum_Qop` (`𝒫∘𝒬 = 0`), `QopAlgebra_ThetaN_sumZero` (`‖mSigma E b‖ = 1`),
`QopAlgebra_Psum_deriv` with `QopAlgebra_mollifier_differentiableAt` (`𝒫 ∂_vϑ* = 0`). -/
theorem expIntIQ_src_sumZero (d : ℕ) (_hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) (E : ℝ) (hE : |E| ≤ 2)
    (hl : 0 < sz.lam n) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (σ : Fin 2 → Bool) :
    EKSumZero (STExpQsrc sz n E v σ (expIntIQ_star sz n)) := by
  intro i₀ hi₀ x
  have : i₀ = 0 := Fin.ext hi₀
  subst this
  change STPsum (d := d) (STExpQsrc sz n E v σ (expIntIQ_star sz n)) x = 0
  have hsum : ∀ (τ : ℝ) (a₁ : Zd d (sz.L n)),
      ∑ a ∈ Finset.univ.filter (fun a : Fin 2 → Zd d (sz.L n) => a 0 = a₁), expIntIQ_star sz n τ a = 1 :=
    fun τ a₁ => QopAlgebra_mollifier_sum d (sz.L n) 1 (sz.lam n) τ a₁
  have hL := sz.three_le_L n
  have h1 : STPsum (d := d) (STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpDrift sz n E v σ c)) x = 0 :=
    QopAlgebra_Psum_Qop (expIntIQ_star sz n) (hsum v) _ x
  have h2 : STPsum (d := d) (STQop (d := d) (expIntIQ_star sz n) v
      (STthetaOp sz n E v σ (fun c => STExpErr sz n E v σ c))) x = 0 :=
    QopAlgebra_Psum_Qop (expIntIQ_star sz n) (hsum v) _ x
  have h3 : STPsum (d := d) (STthetaOp sz n E v σ (STQop (d := d) (expIntIQ_star sz n) v
      (fun c => STExpErr sz n E v σ c))) x = 0 := by
    have hθ : STthetaOp sz n E v σ (STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpErr sz n E v σ c)) =
        ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) v
          (STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpErr sz n E v σ c)) :=
      funext (STthetaOp_eq_ThetaN sz n E v σ _)
    rw [hθ]
    exact QopAlgebra_ThetaN_sumZero (sz.lam n) hL (fun i => norm_mSigma hE _) hv0 hv1
      (fun a₁ => QopAlgebra_Psum_Qop (expIntIQ_star sz n) (hsum v) _ a₁) x
  have hdv : STPsum (d := d) (fun b : Fin 2 → Zd d (sz.L n) =>
      deriv (fun τ => expIntIQ_star sz n τ b) v) x = 0 :=
    QopAlgebra_Psum_deriv (m := 1) hsum (ϑ' := fun b => deriv (fun τ => expIntIQ_star sz n τ b) v)
      (fun b => (QopAlgebra_mollifier_differentiableAt d (sz.L n) 1 hL hl hv1 b).hasDerivAt) x
  have h4 := expIntIQ_Psum_mul_zero (STPsum (d := d) (fun c => STExpErr sz n E v σ c)) _ x hdv
  refine (expIntIQ_Psum_comb _ _ _ _ x).trans ?_
  rw [h1, h2, h3, h4]
  ring


/-! ## 3. Polynomial envelopes along the flow -/

/-- The fibre `{a : a₀ = x}` of the two-index tensors has at most `(L^d)²` elements. -/
private theorem expIntIQ_card_le {d L : ℕ} [NeZero L] (x : Zd d L) :
    (((Finset.univ.filter (fun a : Fin 2 → Zd d L => a 0 = x)).card : ℕ) : ℝ) ≤ ((L : ℝ) ^ d) ^ 2 := by
  have h1 : (Finset.univ.filter (fun a : Fin 2 → Zd d L => a 0 = x)).card ≤ Fintype.card (Fin 2 → Zd d L) :=
    by
      rw [← Finset.card_univ]
      exact Finset.card_filter_le _ _
  have h2 : Fintype.card (Fin 2 → Zd d L) = (L ^ d) ^ 2 := by simp [Zd, ZMod.card]
  rw [h2] at h1
  exact_mod_cast h1

/-- `‖(𝒫 A)_x‖ ≤ (L^d)² ‖A‖` (a crude count of the fibre). -/
private theorem expIntIQ_Psum_norm_le {d L : ℕ} [NeZero L] (A : (Fin 2 → Zd d L) → ℂ) (x : Zd d L) :
    ‖STPsum (d := d) A x‖ ≤ ((L : ℝ) ^ d) ^ 2 * ‖A‖ := by
  unfold STPsum
  calc ‖∑ a ∈ Finset.univ.filter (fun a : Fin 2 → Zd d L => a 0 = x), A a‖
      ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin 2 → Zd d L => a 0 = x), ‖A a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Finset.univ.filter (fun a : Fin 2 → Zd d L => a 0 = x), ‖A‖ :=
        Finset.sum_le_sum fun a _ => norm_le_pi_norm A a
    _ = ((Finset.univ.filter (fun a : Fin 2 → Zd d L => a 0 = x)).card : ℝ) * ‖A‖ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((L : ℝ) ^ d) ^ 2 * ‖A‖ := mul_le_mul_of_nonneg_right (expIntIQ_card_le x) (norm_nonneg _)

/-- `‖(𝒫 A)‖_∞ ≤ (L^d)² ‖A‖_∞`. -/
private theorem expIntIQ_Psum_pi_le {d L : ℕ} [NeZero L] (A : (Fin 2 → Zd d L) → ℂ) :
    ‖STPsum (d := d) A‖ ≤ ((L : ℝ) ^ d) ^ 2 * ‖A‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x => expIntIQ_Psum_norm_le A x

/-- `‖(𝒫 A)_{a₁} ϑ_{t,a}‖_∞ ≤ (L^d)² ‖A‖_∞ C` for a mollifier with `‖ϑ‖ ≤ C` (clause 2 at `m = 1`, `ℓ ≥ 1`, `c ≥ 0`). -/
private theorem expIntIQ_Pvth_le {d L : ℕ} [NeZero L] {g C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    {ϑ : ℝ → (Fin 2 → Zd d L) → ℂ} (h : STMollifierProps (d := d) g C c ϑ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (A : (Fin 2 → Zd d L) → ℂ) :
    ‖fun b => STPsum (d := d) A (b 0) * ϑ t b‖ ≤ ((L : ℝ) ^ d) ^ 2 * ‖A‖ * C := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hℓ : 1 ≤ ellT L g t := one_le_ellT hL1
  have hsup : ∀ b, ‖ϑ t b‖ ≤ C := by
    intro b
    refine (h.2.1 t ht0 ht1 b).trans ?_
    have hl0 : 0 < ellT L g t := lt_of_lt_of_le zero_lt_one hℓ
    have hS : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (1 + 1)), (zdistD d L (b i - b 0) : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h1 : ((ellT L g t ^ d)⁻¹) ^ 1 ≤ 1 := by
      rw [pow_one]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hℓ)
    have h2 : Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (1 + 1)), (zdistD d L (b i - b 0) : ℝ)) / ellT L g t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ c * (∑ i ∈ Finset.univ.erase (0 : Fin (1 + 1)), (zdistD d L (b i - b 0) : ℝ)) / ellT L g t :=
        div_nonneg (mul_nonneg hc hS) hl0.le
      linarith [show -c * (∑ i ∈ Finset.univ.erase (0 : Fin (1 + 1)), (zdistD d L (b i - b 0) : ℝ)) / ellT L g t =
        -(c * (∑ i ∈ Finset.univ.erase (0 : Fin (1 + 1)), (zdistD d L (b i - b 0) : ℝ)) / ellT L g t) by ring]
    have h3 : 0 ≤ ((ellT L g t ^ d)⁻¹) ^ 1 := by positivity
    calc C * ((ellT L g t ^ d)⁻¹) ^ 1 * Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (1 + 1)),
          (zdistD d L (b i - b 0) : ℝ)) / ellT L g t)
        ≤ C * 1 * 1 := by gcongr
      _ = C := by ring
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  rw [norm_mul]
  calc ‖STPsum (d := d) A (b 0)‖ * ‖ϑ t b‖ ≤ (((L : ℝ) ^ d) ^ 2 * ‖A‖) * C :=
      mul_le_mul (expIntIQ_Psum_norm_le A (b 0)) (hsup b) (norm_nonneg _) (by positivity)

/-- `‖Θ^{(2)}_{v,σ} A‖_∞ ≤ 2 (1-v)⁻¹ ‖A‖_∞` (row sums, `B45_norm_ThetaN_le`). -/
private theorem expIntIQ_theta_le {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) {v : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v < 1) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) :
    ‖STthetaOp sz n E v σ A‖ ≤ 2 * (1 - v)⁻¹ * ‖A‖ := by
  have hnn : 0 ≤ 2 * (1 - v)⁻¹ * ‖A‖ := by
    have : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun a => ?_
  rw [STthetaOp_eq_ThetaN]
  have := B45_norm_ThetaN_le (d := d) (L := sz.L n) (sz.lam n) (sz.three_le_L n) (k := 2)
    (μs := fun i => mSigma E (σ i)) (fun i => norm_mSigma hE _) hv0 hv1 (A := A) (M := ‖A‖)
    (fun b => norm_le_pi_norm A b) a
  simpa using this

/-- `‖𝔼 𝓛‖ ≤ η⁻²`, so `‖f_{v,σ,a}‖ ≤ η_v⁻² + ‖𝒦_{v,σ,a}‖` (a.s. envelope `norm_Lloop_le`; the expectation is over a probability
measure; pointwise copy of the `private` `expIniI_envelope`, `ExpIniI.lean:221`). -/
private theorem expIntIQ_expErr_le {d : ℕ} (sz : Sizes d) (n : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STExpErr sz n E v σ a‖ ≤ (etaT E v)⁻¹ ^ 2 + ‖STKloop sz n E v σ a‖ := by
  unfold STExpErr
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := sz.seqP)
    (f := fun ω => Lloop sz n E v σ a ω) (C := (etaT E v)⁻¹ ^ 2)
    (Filter.Eventually.of_forall fun ω => norm_Lloop_le sz n hE hv σ a ω)
  simpa using h


/-- `(1-v)⁻¹ ≤ N` for every `v ≤ t n` in regime (i), eventually: `1 - v ≥ ilambda²/L²` and `ilambda² W^d ≥ 1` (`(eq:WO)`),
`L² ≤ L^d`, `N = W^d L^d`. -/
private theorem expIntIQ_inv_le {d : ℕ} (hd : 3 ≤ d) {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (sz : Sizes d) (hWO : sz.WO 𝔡)
    {t : ℕ → ℝ} (hR : ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n) :
    ∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [st5_eventually_A_ge_one sz h𝔡 hWO] with n hn
  obtain ⟨hl, hA⟩ := hn
  intro v hv
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hA' : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hA
  have hLd : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL1 (by omega)
  have hpos : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have h1 : (1 - v)⁻¹ ≤ (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)⁻¹ := inv_anti₀ hpos (by linarith [hR n])
  refine h1.trans ?_
  rw [inv_div, div_le_iff₀ (by positivity), hN]
  calc ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := hLd
    _ = 1 * ((sz.L n : ℕ) : ℝ) ^ d := (one_mul _).symm
    _ ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) * ((sz.L n : ℕ) : ℝ) ^ d := by gcongr
    _ = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * sz.lam n ^ 2 := by ring

/-- **The envelope of `f_v`**: `‖f_{v,σ}‖_∞ ≤ N³` for all `v ∈ [s_n, t_n]` and `σ`, eventually (`‖𝔼 𝓛‖ ≤ η_v⁻²`,
`η_v ≥ (1-v) c₀`, `(1-v)⁻¹ ≤ N`, `‖𝒦‖ ≤ (1-t)⁻¹ ≤ N`; the polynomial bound `‖f_v‖ ≤ W^{C₀}` of the decay lemmas). -/
private theorem expIntIQ_f_le {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) (z : ℕ → ℂ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n))
    (hinv : ∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpErr sz n (STflowE z n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
  have hSz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  set c₀ : ℝ := Real.sqrt (2 * κ) / 2 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  filter_upwards [hinv, hSz.eventually (eventually_ge_atTop (c₀⁻¹ ^ 2 + 1))] with n hn hN
  intro v hv1 hv2 σ
  have hv0 : 0 ≤ v := (hs0 n).trans hv1
  have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hc2 : 0 ≤ c₀⁻¹ ^ 2 := by positivity
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hE2 : |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hflow n
  have hIm : c₀ ≤ (mE (STflowE z n)).im := st6_mE_im_ge hκ (st6_flowE_le sz hflow n)
  have hx0 : 0 < 1 - v := by linarith
  have hηlow : (1 - v) * c₀ ≤ etaT (STflowE z n) v := by
    unfold etaT
    exact mul_le_mul_of_nonneg_left hIm hx0.le
  have hη : (etaT (STflowE z n) v)⁻¹ ≤ N * c₀⁻¹ := by
    calc (etaT (STflowE z n) v)⁻¹ ≤ ((1 - v) * c₀)⁻¹ := inv_anti₀ (by positivity) hηlow
      _ = (1 - v)⁻¹ * c₀⁻¹ := mul_inv _ _
      _ ≤ N * c₀⁻¹ := by
        gcongr
        exact hn v hv2
  have hη2 : (etaT (STflowE z n) v)⁻¹ ^ 2 ≤ N ^ 2 * c₀⁻¹ ^ 2 := by
    have h0 : 0 ≤ (etaT (STflowE z n) v)⁻¹ := (inv_pos.2 (etaT_pos hE2 hvl)).le
    calc (etaT (STflowE z n) v)⁻¹ ^ 2 ≤ (N * c₀⁻¹) ^ 2 := pow_le_pow_left₀ h0 hη 2
      _ = N ^ 2 * c₀⁻¹ ^ 2 := by ring
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  have hK := LemDecCalELip_STKloop_two_norm sz n (E := STflowE z n) (t := t n) (u := v) (N := N) hE2.le (ht1 n)
    hv0 hv2 (hn (t n) le_rfl) σ a
  have h1 := expIntIQ_expErr_le sz n hE2 hvl σ a
  calc ‖STExpErr sz n (STflowE z n) v σ a‖ ≤ (etaT (STflowE z n) v)⁻¹ ^ 2 + ‖STKloop sz n (STflowE z n) v σ a‖ := h1
    _ ≤ N ^ 2 * c₀⁻¹ ^ 2 + N := add_le_add hη2 hK
    _ ≤ N ^ 3 := by nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.2 hN)]

/-- `W^{-d} B_{u,0} ≥ 0` (copy of the `private` `expIntI_Bctl_nonneg`, `ExpIntI.lean:422`). -/
private theorem expIntIQ_Bctl_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (v : ℝ) : 0 ≤ sz.Bctl n v := by
  unfold Sizes.Bctl Bparam
  positivity

/-- `W^{-d} B_{u,0} ≤ 2 (1-u)⁻¹` for `u < 1` (copy of the `private` `expIniI_Bctl_le`, `ExpIniI.lean:79`). -/
private theorem expIntIQ_Bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu1 : u < 1) :
    sz.Bctl n u ≤ 2 * (1 - u)⁻¹ := by
  have h1 : 0 < 1 - u := by linarith
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLd : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL
  have hWd : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos h1]
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  simp only [hz, inv_one, mul_one]
  have e1 : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1 (by nlinarith [sq_nonneg (sz.lam n)])
  have e2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1 (by nlinarith)
  have e3 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWd
  have e4 : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ 1 * ((1 - u)⁻¹ + (1 - u)⁻¹) := mul_le_mul e3 (add_le_add e1 e2) e4 zero_le_one
    _ = 2 * (1 - u)⁻¹ := by ring

/-- **(eq:Exp(L-K)1) + (eq:ExpLWn=2) for the drift tensor** (premise `STExpDriftHiConcl`): `‖D_v^σ‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} +
B_v^{5/2})` for all large `n`, all `v ∈ [s_n, t_n]` and `σ` (copy of the `private` `expIntI_drift_pi`, `ExpIntI.lean:429`). -/
private theorem expIntIQ_drift_pi {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STExpDriftHiConcl sz E s t) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (v : TimeIcc s t n) (σ : Fin 2 → Bool),
      ‖fun b => STExpDrift sz n (E n) (v : ℝ) σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by
  have h1 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))).1 h.1 τ hτ
  have h2 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))).1 h.2 τ hτ
  filter_upwards [h1, h2] with n hn1 hn2
  intro v σ
  have hv1 : (v : ℝ) < 1 := lt_of_le_of_lt v.2.2 (ht1 n)
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hB0 := (STBctl_pos sz n hv1).le
  have hinv : 0 ≤ (1 - (v : ℝ))⁻¹ := inv_nonneg.2 (by linarith)
  have hX : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) :=
    mul_nonneg hN0 (mul_nonneg hinv (add_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hB0 _)))
  rw [pi_norm_le_iff_of_nonneg hX]
  intro a
  calc ‖STExpDrift sz n (E n) (v : ℝ) σ a‖
      = ‖STExpELKLK sz n (E n) (v : ℝ) σ a + STExpEGt sz n (E n) (v : ℝ) σ a‖ := rfl
    _ ≤ ‖STExpELKLK sz n (E n) (v : ℝ) σ a‖ + ‖STExpEGt sz n (E n) (v : ℝ) σ a‖ := norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (v : ℝ))⁻¹ * sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ)) +
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (v : ℝ))⁻¹ * sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)) :=
        add_le_add (hn1 (v, σ, a)) (hn2 (v, σ, a))
    _ = ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by ring

/-- `B^p ≤ M^3` for `0 ≤ B ≤ M`, `1 ≤ M`, `0 ≤ p ≤ 3`. -/
private theorem expIntIQ_rpow_le_cube {B M p : ℝ} (hB : 0 ≤ B) (hBM : B ≤ M) (hM : 1 ≤ M) (hp : p ≤ 3)
    (hp0 : 0 ≤ p) : B ^ p ≤ M ^ 3 := by
  calc B ^ p ≤ M ^ p := Real.rpow_le_rpow hB hBM hp0
    _ ≤ M ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM hp
    _ = M ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The envelope of the drift tensor**: `‖D_v^σ‖_∞ ≤ N^6` for all `v ∈ [s_n, t_n]` and `σ`, eventually
(`STExpDriftHiConcl` at `τ = 1`, `(1-v)⁻¹ ≤ N`, `B_v ≤ 2 (1-v)⁻¹ ≤ 2N`). -/
private theorem expIntIQ_D_le {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STExpDriftHiConcl sz E s t)
    (hinv : ∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖fun b => STExpDrift sz n (E n) v σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 6 := by
  filter_upwards [expIntIQ_drift_pi sz hsz ht1 h one_pos, hinv, hsz.eventually (eventually_ge_atTop (16 : ℝ))]
    with n hn hi hN
  intro v hv1 hv2 σ
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
  have hx : (1 - v)⁻¹ ≤ N := hi v hv2
  have hx0 : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
  have hB := expIntIQ_Bctl_le sz n hvl
  have hB0 := expIntIQ_Bctl_nonneg sz n v
  have hM : 1 ≤ 2 * N := by linarith
  have hBM : sz.Bctl n v ≤ 2 * N := by linarith
  have h1 := expIntIQ_rpow_le_cube hB0 hBM hM (by norm_num : (11 / 5 : ℝ) ≤ 3) (by norm_num)
  have h2 := expIntIQ_rpow_le_cube hB0 hBM hM (by norm_num : (5 / 2 : ℝ) ≤ 3) (by norm_num)
  have hD := hn ⟨v, hv1, hv2⟩ σ
  refine hD.trans ?_
  have hN0 : 0 < N := by linarith
  have h3 : (1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) ≤ N * ((2 * N) ^ 3 + (2 * N) ^ 3) := by
    gcongr
  calc N ^ (1 : ℝ) * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))
      ≤ N ^ (1 : ℝ) * (N * ((2 * N) ^ 3 + (2 * N) ^ 3)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 16 * N ^ 5 := by rw [Real.rpow_one]; ring
    _ ≤ N ^ 6 := by nlinarith [pow_pos hN0 5]


/-! ## 4. Decay of the `ϑ*`-source (target 5) -/

private theorem expIntIQ_L_le_N {d : ℕ} (sz : Sizes d) (n : ℕ) :
    ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
  have hLW : (sz.L n) ^ d ≤ sz.size n := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  exact_mod_cast hLW

/-- `N^k ≤ W^{k/𝔠}` from `W ≥ N^𝔠` (`size_rpow_le_W_rpow` at a natural exponent). -/
private theorem expIntIQ_N_le_W {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (n : ℕ)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) (k : ℕ) :
    ((sz.size n : ℕ) : ℝ) ^ k ≤ ((sz.W n : ℕ) : ℝ) ^ ((k : ℝ) / 𝔠) := by
  have := sz.size_rpow_le_W_rpow h𝔠 n hb (τ := (k : ℝ)) (Nat.cast_nonneg k)
  rwa [Real.rpow_natCast] at this

/-- `A - 𝒬_t A = (𝒫 A)_{a₁} ϑ_t`. -/
private theorem expIntIQ_sub_Qop {d L : ℕ} [NeZero L] (ϑ : ℝ → (Fin 2 → Zd d L) → ℂ) (t : ℝ)
    (A : (Fin 2 → Zd d L) → ℂ) :
    A - STQop (d := d) ϑ t A = fun b => STPsum (d := d) A (b 0) * ϑ t b := by
  funext b
  simp only [Pi.sub_apply, STQop]
  ring

/-- The decomposition of the `ϑ`-source `A_v = 𝒬D + [𝒬, Θ] f - (𝒫 f) ∂ϑ` into five pieces, each of which decays:
`D - (D - 𝒬D)`, `Θ((𝒫f)ϑ)`, `(Θf - 𝒬(Θf))`, `(𝒫f) ∂ϑ` (`QopAlgebra_commutator_ThetaN`). -/
private theorem expIntIQ_src_decomp {d : ℕ} (sz : Sizes d) (n : ℕ) (E v : ℝ) (σ : Fin 2 → Bool)
    (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    STExpQsrc sz n E v σ ϑ a =
      (STExpDrift sz n E v σ a -
        ((fun c => STExpDrift sz n E v σ c) - STQop (d := d) ϑ v (fun c => STExpDrift sz n E v σ c)) a) +
      (STthetaOp sz n E v σ (fun b => STPsum (d := d) (fun c => STExpErr sz n E v σ c) (b 0) * ϑ v b) a -
        (STthetaOp sz n E v σ (fun c => STExpErr sz n E v σ c) -
          STQop (d := d) ϑ v (STthetaOp sz n E v σ (fun c => STExpErr sz n E v σ c))) a) -
      STPsum (d := d) (fun c => STExpErr sz n E v σ c) (a 0) * deriv (fun τ => ϑ τ a) v := by
  have hθ : ∀ A, STthetaOp sz n E v σ A =
      ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) v A :=
    fun A => funext (STthetaOp_eq_ThetaN sz n E v σ A)
  have hcomm := QopAlgebra_commutator_ThetaN (d := d) (sz.lam n) (fun i => mSigma E (σ i)) ϑ v
    (fun c => STExpErr sz n E v σ c) a
  unfold STExpQsrc
  simp only [hθ, Pi.sub_apply]
  simp only [STQop] at hcomm ⊢
  linear_combination hcomm


/-- The triangle inequality for the five pieces of the `ϑ*`-source. -/
private theorem expIntIQ_norm_five {a b c e f : ℂ} :
    ‖a - b + (c - e) - f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ + ‖f‖ := by
  calc ‖a - b + (c - e) - f‖ ≤ ‖a - b + (c - e)‖ + ‖f‖ := norm_sub_le _ _
    _ ≤ ‖a - b‖ + ‖c - e‖ + ‖f‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (‖a‖ + ‖b‖) + (‖c‖ + ‖e‖) + ‖f‖ := by gcongr <;> exact norm_sub_le _ _
    _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ + ‖f‖ := by ring

/-- **Target 5**: `(deccA0)` of the `ϑ*`-source on `[s,t]`, for every `σ`, at the scale `ℓ_v`, for every
`ε', D > 0`, eventually (supervisor `2026-10-06-0255.md` §2.2 step 4 (c)).  The five pieces of
`A*_v`: `D_v` (`STExpDriftDecayConcl`, deterministic through `HighProbAt.nonempty`), `D_v - 𝒬*D_v`
(`stQop_sub_fastDecay`), `Θ((𝒫f)ϑ*) = Θ(f - 𝒬*f)` (`QopDecay_STthetaOp_fastDecay` after
`stQop_sub_fastDecay`), `Θf - 𝒬*(Θf)` (`stQop_sub_fastDecay`), `(𝒫f) ∂ϑ*` (`QopDecay_deriv_fastDecay`);
`A*_v = D - (D - 𝒬*D) + (Θ(f - 𝒬*f) - (Θf - 𝒬*Θf)) - (𝒫f)∂ϑ*` (`QopAlgebra_commutator_ThetaN`).  The side
conditions `L^d ≤ W^K`, `(1-v)⁻¹ ≤ W^K` (`K = 1/𝔠`), `ilambda ≤ 𝔡⁻¹`, `‖·‖ ≤ W^{6/𝔠}` and `W ≥ W₀` are
discharged from `STFlow`, regime (i) and the envelopes, never assumed. -/
theorem expIntIQ_src_decay (d : ℕ) (hd : 3 ≤ d) (κ ε 𝔠 𝔡 : ℝ) (hκ : 0 < κ) (_hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (_hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5I sz s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t)
    (hdd : STExpDriftDecayConcl sz (STflowE z) s t) (ε' D : ℝ) (hε' : 0 < ε') (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D
        (STExpQsrc sz n (STflowE z n) v σ (expIntIQ_star sz n)) := by
  obtain ⟨h𝔠, -, hSz, hBw, hWO⟩ := hflow.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := scaleFacts3_W_tendsto sz hflow.1
  obtain ⟨Cs, cs, hCs0, hcs0, hstar⟩ := expIntIQ_star_abs d sz 𝔡 hWO
  set K : ℝ := 1 / 𝔠 with hK
  set C₀ : ℝ := (6 : ℕ) / 𝔠 with hC₀
  set D₁ : ℝ := D + 1 with hD₁
  set D₂ : ℝ := D₁ + K + 1 with hD₂
  have hD₁0 : 0 < D₁ := by rw [hD₁]; linarith
  have hD₂0 : 0 < D₂ := by
    have : 0 < K := one_div_pos.2 h𝔠
    rw [hD₂]; linarith
  obtain ⟨W₁, hW₁1, hW₁⟩ := stQop_sub_fastDecay d 1 K Cs cs C₀ ε' D₁ hCs0 hcs0 hε'
  obtain ⟨W₂, hW₂1, hW₂⟩ := stQop_sub_fastDecay d 1 K Cs cs C₀ (ε' / 2) D₂ hCs0 hcs0 (half_pos hε')
  obtain ⟨W₃, hW₃1, hW₃⟩ := QopDecay_STthetaOp_fastDecay hd 𝔡⁻¹ K C₀ (ε' / 2) D₂ (inv_pos.2 h𝔡) (half_pos hε')
  obtain ⟨W₄, hW₄1, hW₄⟩ := QopDecay_deriv_fastDecay d 1 K C₀ ε' D₁ hε'
  have hinv := expIntIQ_inv_le hd h𝔡 sz hWO (fun n => (hR n).1)
  have hf := expIntIQ_f_le hκ sz z hflow s t hs0 htT hinv
  have hDe := expIntIQ_D_le sz hSz ht1 hdr hinv
  have hdecD : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, ({ω | ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' D₁
        (fun a => STExpDrift sz n (STflowE z n) (v : ℝ) σ a)} : Set sz.SeqΩ).Nonempty :=
    fun σ => HighProbAt.nonempty (tendsto_size sz hSz) measure_univ (hdd σ ε' D₁ hε' hD₁0)
  have hall := Filter.eventually_all.2 hdecD
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO, st6_lam_pos sz hWO] with n h1 h2
    exact ⟨h2, h1.2⟩
  filter_upwards [hstar, hinv, hf, hDe, hall, hWt.eventually (eventually_ge_atTop (max (max (max W₁ W₂) (max W₃ W₄)) 5)),
    hBw, hlam, hSz.eventually (eventually_ge_atTop (max 16 Cs))] with n hs hi hfn hDn hdn hW hBn hlamn hN
  intro v hv1 hv2 σ a ha
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hv0 : 0 ≤ v := (hs0 n).trans hv1
  have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
  have hW5 : 5 ≤ W := ((le_max_right _ _).trans hW)
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hWW₂ : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hWW₃ : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
  have hWW₄ : W₄ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
  have hW0 : 0 < W := by linarith
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNCs : Cs ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  -- side conditions in terms of `W`
  have hN1W : N ≤ W ^ K := by
    have := expIntIQ_N_le_W sz h𝔠 n hBn 1
    simpa [hK] using this
  have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ K := (expIntIQ_L_le_N sz n).trans hN1W
  have hKv : (1 - v)⁻¹ ≤ W ^ K := (hi v hv2).trans hN1W
  have hN6W : N ^ 6 ≤ W ^ C₀ := by
    have := expIntIQ_N_le_W sz h𝔠 n hBn 6
    simpa [hC₀] using this
  -- the envelopes
  have hfn' := hfn v hv1 hv2 σ
  have hLd : ((sz.L n : ℕ) : ℝ) ^ d ≤ N := expIntIQ_L_le_N sz n
  have hLd0 : 0 ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hLd2 : (((sz.L n : ℕ) : ℝ) ^ d) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hLd0 hLd 2
  have hf3 : ‖(fun c => STExpErr sz n (STflowE z n) v σ c)‖ ≤ N ^ 3 := hfn'
  have hfW : ‖(fun c => STExpErr sz n (STflowE z n) v σ c)‖ ≤ W ^ C₀ :=
    hf3.trans ((pow_le_pow_right₀ hN1 (by norm_num : 3 ≤ 6)).trans hN6W)
  have hPf : ‖STPsum (d := d) (fun c => STExpErr sz n (STflowE z n) v σ c)‖ ≤ N ^ 6 := by
    refine (expIntIQ_Psum_pi_le _).trans ?_
    calc (((sz.L n : ℕ) : ℝ) ^ d) ^ 2 * ‖(fun c => STExpErr sz n (STflowE z n) v σ c)‖ ≤ N ^ 2 * N ^ 3 :=
          mul_le_mul hLd2 hf3 (norm_nonneg _) (by positivity)
      _ = N ^ 5 := by ring
      _ ≤ N ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
  have hPfW : ‖STPsum (d := d) (fun c => STExpErr sz n (STflowE z n) v σ c)‖ ≤ W ^ C₀ := hPf.trans hN6W
  have hg6 : ‖fun b => STPsum (d := d) (fun c => STExpErr sz n (STflowE z n) v σ c) (b 0) *
      expIntIQ_star sz n v b‖ ≤ N ^ 6 := by
    refine (expIntIQ_Pvth_le hCs0.le hcs0.le hs hv0 hvl _).trans ?_
    calc (((sz.L n : ℕ) : ℝ) ^ d) ^ 2 * ‖(fun c => STExpErr sz n (STflowE z n) v σ c)‖ * Cs
        ≤ N ^ 2 * N ^ 3 * N := by gcongr
      _ = N ^ 6 := by ring
  have hgW : ‖fun b => STPsum (d := d) (fun c => STExpErr sz n (STflowE z n) v σ c) (b 0) *
      expIntIQ_star sz n v b‖ ≤ W ^ C₀ := hg6.trans hN6W
  have hΘf : ‖STthetaOp sz n (STflowE z n) v σ (fun c => STExpErr sz n (STflowE z n) v σ c)‖ ≤ W ^ C₀ := by
    refine ((expIntIQ_theta_le sz n (st6_flowE_lt_two sz hκ hflow n).le hv0 hvl σ _).trans ?_).trans hN6W
    calc 2 * (1 - v)⁻¹ * ‖(fun c => STExpErr sz n (STflowE z n) v σ c)‖ ≤ 2 * N * N ^ 3 := by
          gcongr
          exact hi v hv2
      _ = 2 * N ^ 4 := by ring
      _ ≤ N ^ 2 * N ^ 4 := by
          have h2 : (2 : ℝ) ≤ N ^ 2 := by nlinarith
          gcongr
      _ = N ^ 6 := by ring
  have hDW : ‖fun c => STExpDrift sz n (STflowE z n) v σ c‖ ≤ W ^ C₀ := (hDn v hv1 hv2 σ).trans hN6W
  -- the five decays at a far index `a`
  have b1 : ‖STExpDrift sz n (STflowE z n) v σ a‖ ≤ W ^ (-D₁) := by
    obtain ⟨ω, hω⟩ := hdn σ
    exact hω ⟨v, hv1, hv2⟩ a ha
  have b2 := hW₁ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 W hWW₁ hLW (expIntIQ_star sz n) hs v hv0 hvl
    (fun c => STExpDrift sz n (STflowE z n) v σ c) hDW a ha
  have hdecg : EKFastDecay (sz.lam n) v W (ε' / 2) D₂
      (fun b => STPsum (d := d) (fun c => STExpErr sz n (STflowE z n) v σ c) (b 0) * expIntIQ_star sz n v b) := by
    rw [← expIntIQ_sub_Qop]
    exact hW₂ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 W hWW₂ hLW (expIntIQ_star sz n) hs v hv0 hvl
      (fun c => STExpErr sz n (STflowE z n) v σ c) hfW
  have b3 := hW₃ sz n (STflowE z n) (st6_flowE_lt_two sz hκ hflow n).le hlamn.1 hlamn.2 hWW₃ hLW v hv0 hvl hKv σ _ hgW
    hdecg
  have e2 : 2 * (ε' / 2) = ε' := by ring
  have e3 : D₂ - (K + 1) = D₁ := by rw [hD₂]; ring
  rw [e2, e3] at b3
  have b4 := hW₁ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 W hWW₁ hLW (expIntIQ_star sz n) hs v hv0 hvl
    (STthetaOp sz n (STflowE z n) v σ (fun c => STExpErr sz n (STflowE z n) v σ c)) hΘf a ha
  have b5 : ‖STPsum (d := d) (fun c => STExpErr sz n (STflowE z n) v σ c) (a 0) *
      deriv (fun τ => expIntIQ_star sz n τ a) v‖ ≤ W ^ (-D₁) :=
    hW₄ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 W hWW₄ v hv0 hvl hKv
      (STPsum (d := d) (fun c => STExpErr sz n (STflowE z n) v σ c)) hPfW a ha
  have b3' : ‖STthetaOp sz n (STflowE z n) v σ (fun b => STPsum (d := d) (fun c => STExpErr sz n (STflowE z n) v σ c) (b 0) *
      expIntIQ_star sz n v b) a‖ ≤ W ^ (-D₁) := b3 a ha
  -- combine
  change ‖STExpQsrc sz n (STflowE z n) v σ (expIntIQ_star sz n) a‖ ≤ W ^ (-D)
  rw [expIntIQ_src_decomp]
  have hWD : W ^ (-D₁) = W ^ (-D) * W⁻¹ := by
    rw [hD₁, show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
  have hWi : W⁻¹ ≤ 1 / 5 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hW5
  have hWD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  refine (expIntIQ_norm_five).trans ?_
  calc _ ≤ 5 * W ^ (-D₁) := by linarith
    _ = 5 * (W ^ (-D) * W⁻¹) := by rw [hWD]
    _ ≤ 5 * (W ^ (-D) * (1 / 5)) := by gcongr
    _ = W ^ (-D) := by ring


/-! ## 5. The initial term for `ϑ*` (target 6) -/

/-- **Target 6 (step 3, the initial term)**: from the bound `F` on `𝒰_{s,u} 𝒬^ϑ_s f_s` (any admissible `ϑ`,
`0 < C`, `0 < c`, eventually) to the bound `F + B_u³` on `𝒰_{s,u} 𝒬^{ϑ*}_s f_s`.  `𝒬*_s f_s = 𝒬^ϑ_s f_s + R_s`
with `R_s = (𝒫 f_s)(ϑ_s - ϑ*_s)` (target 2), which is sum-zero (target 3), deterministic,
`(s, ε', D)`-decaying (`stQop_sub_fastDecay` twice, `‖f_s‖ ≤ N³ ≤ W^{3/𝔠}`) and `‖R_s‖ ≤ 2 N^τ B_s³` (first
Ward conjunct at `u = s` for `ϑ` and for `ϑ*`, deterministic `Prec`).  The sum-zero branch of
`expIntI_kernel_unif` (ratio² `≤ 4`, `(sum_res_2)` `3_5:1659`) then gives `‖𝒰_{s,u} R_s‖ ≤ N^τ · 8 B_s³ ≤
N^τ · 8 B_u³` (`STBctl_mono`).  The kernel hypothesis `∀ n v, EKSumZero (𝒜 n v)` is met by the guarded family
`if (0 < ilambda_n ∧ props(ϑ_n) ∧ props(ϑ*_n) ∧ v = s_n) then R_{s_n} else 0`; the guard `v = s_n` also
settles the time scale of `R_s` (it decays at `ℓ_s`, which is `ℓ_v` at `v = s_n`). -/
theorem expIntIQ_ini (d : ℕ) (hd : 3 ≤ d) (κ ε 𝔠 𝔡 𝔠d : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d)
    (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (hW : STExpWardIConcl' sz (STflowE z) s t)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n))
    (F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ) (hF : ∀ n p, 0 ≤ F n p)
    (hF1 : Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p)) :
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p + sz.Bctl n (p.1 : ℝ) ^ 3) := by
  classical
  obtain ⟨h𝔠, -, hSz, hBw, hWO⟩ := hflow.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hs1 : ∀ n, s n < 1 := fun n => lt_trans (hst n) (ht1 n)
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := scaleFacts3_W_tendsto sz hflow.1
  obtain ⟨Cs, cs, hCs0, hcs0, hstar⟩ := expIntIQ_star_abs d sz 𝔡 hWO
  set K : ℝ := 1 / 𝔠 with hK
  set C₀ : ℝ := (3 : ℕ) / 𝔠 with hC₀
  have hinv := expIntIQ_inv_le hd h𝔡 sz hWO (fun n => (hR n).1)
  have hfenv := expIntIQ_f_le hκ sz z hflow s t hs0 htT hinv
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n := st6_lam_pos sz hWO
  -- the Ward bounds (first conjunct) for `ϑ` and `ϑ*`, in deterministic form
  have hw1 := (st6_prec_det_iff sz hSz
    (V := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q => ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
      ϑ n (q.1 : ℝ) q.2.2‖) (fun n q => (sz.Bctl n (q.1 : ℝ)) ^ 3)).1 (hW C c hC hc ϑ hϑ).1
  have hw2 := (st6_prec_det_iff sz hSz
    (V := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q => ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
      expIntIQ_star sz n (q.1 : ℝ) q.2.2‖) (fun n q => (sz.Bctl n (q.1 : ℝ)) ^ 3)).1
    (hW Cs cs hCs0 hcs0 (expIntIQ_star sz) hstar).1
  -- the difference tensor `R_s = (𝒫 f_s)(ϑ_s - ϑ*_s)`
  obtain ⟨R, hRdef⟩ : ∃ R : ∀ n : ℕ, (Fin 2 → Bool) → (Fin 2 → Zd d (sz.L n)) → ℂ, ∀ n σ a,
      R n σ a = STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (s n) σ b) (a 0) *
        (ϑ n (s n) a - expIntIQ_star sz n (s n) a) := ⟨_, fun _ _ _ => rfl⟩
  -- the kernel bound for `R_s`, one sign vector at a time
  have key : ∀ σ : {σ : Fin 2 → Bool // STSigMixed σ}, ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      ∀ (u : TimeIcc s t n) (a : Fin 2 → Zd d (sz.L n)),
        ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u : ℝ) (R n σ.1) a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * (8 * sz.Bctl n (u : ℝ) ^ 3) := by
    intro σ τ hτ
    obtain ⟨𝒜, h𝒜⟩ : ∃ 𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ, ∀ n v, 𝒜 n v =
        if (0 < sz.lam n ∧ STMollifierProps (d := d) (sz.lam n) C c (ϑ n) ∧
            STMollifierProps (d := d) (sz.lam n) Cs cs (expIntIQ_star sz n) ∧ v = s n)
        then R n σ.1 else 0 := ⟨_, fun _ _ => rfl⟩
    have hcase : ∀ n v, EKSumZero (𝒜 n v) := by
      intro n v
      rw [h𝒜]
      split_ifs with hg
      · obtain ⟨-, h1, h2, -⟩ := hg
        have : R n σ.1 = fun a : Fin 2 → Zd d (sz.L n) =>
            STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) (a 0) *
              (ϑ n (s n) a - expIntIQ_star sz n (s n) a) := funext (hRdef n σ.1)
        rw [this]
        exact expIntIQ_diff_sumZero d (sz.L n) (sz.lam n) C c Cs cs (ϑ n) (expIntIQ_star sz n) h1 h2 (s n) _
      · intro i₀ hi₀ x
        simp
    have hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v) := by
      intro ε' D hε' hD
      obtain ⟨W₁, hW₁1, hW₁⟩ := stQop_sub_fastDecay d 1 K C c C₀ ε' (D + 1) hC hc hε'
      obtain ⟨W₂, hW₂1, hW₂⟩ := stQop_sub_fastDecay d 1 K Cs cs C₀ ε' (D + 1) hCs0 hcs0 hε'
      filter_upwards [hfenv, hBw, hϑ, hstar, hlam,
        hWt.eventually (eventually_ge_atTop (max (max W₁ W₂) 2))] with n hfn hBn hϑn hsn hln hWn
      intro v hv1 hv2
      rw [h𝒜]
      split_ifs with hg
      · obtain ⟨hl, h1, h2, hvs⟩ := hg
        subst hvs
        set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
        have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWn)
        have hWW₂ : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWn)
        have hW2 : 2 ≤ W := (le_max_right _ _).trans hWn
        have hW0 : 0 < W := by linarith
        have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
        have hN1W : ((sz.size n : ℕ) : ℝ) ≤ W ^ K := by
          have := expIntIQ_N_le_W sz h𝔠 n hBn 1
          simpa [hK] using this
        have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ K := (expIntIQ_L_le_N sz n).trans hN1W
        have hfW : ‖(fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)‖ ≤ W ^ C₀ := by
          refine (hfn (s n) le_rfl (hst n).le σ.1).trans ?_
          have := expIntIQ_N_le_W sz h𝔠 n hBn 3
          simpa [hC₀] using this
        have e1 := hW₁ (sz.L n) (sz.three_le_L n) (sz.lam n) hl W hWW₁ hLW (ϑ n) h1 (s n) (hs0 n) (hs1 n)
          (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) hfW
        have e2 := hW₂ (sz.L n) (sz.three_le_L n) (sz.lam n) hl W hWW₂ hLW (expIntIQ_star sz n) h2 (s n) (hs0 n) (hs1 n)
          (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) hfW
        intro a ha
        have hRa : R n σ.1 a = ((fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) -
              STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a -
            ((fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) -
              STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a := by
          rw [hRdef, expIntIQ_sub_Qop, expIntIQ_sub_Qop]
          ring
        rw [hRa]
        have hWD : W ^ (-(D + 1)) = W ^ (-D) * W⁻¹ := by
          rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
        have hWi : W⁻¹ ≤ 1 / 2 := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) hW2
        have hWD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
        have b1 := e1 a ha
        have b2 := e2 a ha
        calc _ ≤ _ := norm_sub_le _ _
          _ ≤ 2 * W ^ (-(D + 1)) := by linarith
          _ = 2 * (W ^ (-D) * W⁻¹) := by rw [hWD]
          _ ≤ 2 * (W ^ (-D) * (1 / 2)) := by gcongr
          _ = W ^ (-D) := by ring
      · intro a _
        have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        simpa using hW0
    have hX0 : ∀ n (v : ℝ), 0 ≤ 2 * sz.Bctl n (s n) ^ 3 := fun n v => by
      have := expIntIQ_Bctl_nonneg sz n (s n)
      positivity
    have hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ 2 * sz.Bctl n (s n) ^ 3 := by
      refine ⟨3, Filter.Eventually.of_forall fun n v _ _ => ?_⟩
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hB := expAvg_Bctl_ge sz n (hs0 n) (hs1 n)
      have h1 : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ (sz.Bctl n (s n)) ^ 3 := by
        rw [Real.rpow_neg hN0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hB 3
      have h2 : 0 ≤ (sz.Bctl n (s n)) ^ 3 := by
        have := expIntIQ_Bctl_nonneg sz n (s n)
        positivity
      linarith
    have hbd : ∀ τ' : ℝ, 0 < τ' → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (2 * sz.Bctl n (s n) ^ 3) := by
      intro τ' hτ'
      filter_upwards [hw1 τ' hτ', hw2 τ' hτ'] with n h1 h2
      intro v hv1 hv2
      rw [h𝒜]
      split_ifs with hg
      · obtain ⟨-, -, -, hvs⟩ := hg
        subst hvs
        have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hB0 : 0 ≤ sz.Bctl n (s n) ^ 3 := by
          have := expIntIQ_Bctl_nonneg sz n (s n)
          positivity
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
        have q1 := h1 (⟨s n, le_rfl, (hst n).le⟩, ⟨σ.1, σ.2⟩, a)
        have q2 := h2 (⟨s n, le_rfl, (hst n).le⟩, ⟨σ.1, σ.2⟩, a)
        rw [hRdef, mul_sub]
        calc ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) (a 0) * ϑ n (s n) a -
              STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) (a 0) * expIntIQ_star sz n (s n) a‖
            ≤ _ := norm_sub_le _ _
          _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n (s n) ^ 3 + ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n (s n) ^ 3 :=
            add_le_add q1 q2
          _ = ((sz.size n : ℕ) : ℝ) ^ τ' * (2 * sz.Bctl n (s n) ^ 3) := by ring
      · rw [norm_zero]
        have hB0 : 0 ≤ sz.Bctl n (s n) ^ 3 := by
          have := expIntIQ_Bctl_nonneg sz n (s n)
          positivity
        positivity
    have hk := expIntI_kernel_unif hd hκ hε h𝔡 h𝔠d hdc sz z hflow s t hs0 hst htT hR hcon σ.1 𝒜
      (fun n _ => 2 * sz.Bctl n (s n) ^ 3) (Or.inr hcase) hdec hX0 hlow hbd τ hτ
    filter_upwards [hk, hϑ, hstar, hlam] with n hkn hϑn hsn hln u a
    have h0 := hkn u (s n) le_rfl u.2.1
    rw [h𝒜, ite_eq_left ⟨hln, hϑn, hsn, rfl⟩] at h0
    have hsu : s n ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
    have hmono := STBctl_mono sz n hsu hu1
    have hB0 := expIntIQ_Bctl_nonneg sz n (s n)
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    refine (norm_le_pi_norm _ a).trans (h0.trans ?_)
    have h3 : sz.Bctl n (s n) ^ 3 ≤ sz.Bctl n (u : ℝ) ^ 3 := pow_le_pow_left₀ hB0 hmono 3
    calc ((sz.size n : ℕ) : ℝ) ^ τ * (4 * (2 * sz.Bctl n (s n) ^ 3))
        = ((sz.size n : ℕ) : ℝ) ^ τ * (8 * sz.Bctl n (s n) ^ 3) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (8 * sz.Bctl n (u : ℝ) ^ 3) := by gcongr
  -- the family of `Prec`
  have hRprec : Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (R n p.2.1.1) p.2.2‖)
      (fun n p _ => 8 * sz.Bctl n (p.1 : ℝ) ^ 3) := by
    refine (st6_prec_det_iff sz hSz (V := STIdx2P sz STSigMixed s t)
      (fun n p => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ) (R n p.2.1.1) p.2.2‖)
      (fun n p => 8 * sz.Bctl n (p.1 : ℝ) ^ 3)).2 ?_
    intro τ hτ
    filter_upwards [Filter.eventually_all.2 (fun σ => key σ τ hτ)] with n hn p
    exact hn p.2.1 p.1 p.2.2
  have hsum := StochDomAt.add (tendsto_size sz hSz) hF1 hRprec
  refine st5_prec_mono sz hSz (c := 8) (StochDomAt.of_le_left (fun n p ω => ?_) hsum)
    (Eventually.of_forall fun n p ω => ?_) (fun n p ω => ?_)
  · have e : STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b) =
        STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b) + R n p.2.1.1 := by
      funext a
      rw [Pi.add_apply, expIntIQ_Qop_sub d (sz.L n) (ϑ n) (expIntIQ_star sz n) (s n), hRdef]
    change ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖ ≤
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖ +
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ) (R n p.2.1.1) p.2.2‖
    rw [e, RBM.Ind.GridDuhamelN_Ugen_add]
    exact norm_add_le _ _
  · have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) ^ 3 := by
      have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
      positivity
    have := hF n p
    change F n p + 8 * sz.Bctl n (p.1 : ℝ) ^ 3 ≤ 8 * (F n p + sz.Bctl n (p.1 : ℝ) ^ 3)
    linarith
  · have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) ^ 3 := by
      have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
      positivity
    have := hF n p
    change 0 ≤ F n p + sz.Bctl n (p.1 : ℝ) ^ 3
    linarith


/-! ## 6. The `ϑ*` bound (target 7) -/

/-- **The drift-type integral at one size** (`6:97`, `6:132`): a kernel bound `‖𝒰_{v,u} 𝒜_v‖_∞ ≤ M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2} +
B_v³)` on `[s,u]` gives `‖∫_s^u 𝒰_{v,u} 𝒜_v dv‖ ≤ M · 4 T_u · 2 log L` (`B_v ≤ B_u`, `B_u^{11/5} + B_u^{5/2} ≤ 3 T_u`, `B_u³ ≤ T_u`,
`∫_s^u (1-v)⁻¹ ≤ 2 log L`); copy of the `private` `expIntI_drift_integral_le` (`ExpIntI.lean:283`) with the third term `B³`. -/
private theorem expIntIQ_integral_le {d : ℕ} (sz : Sizes d) (n : ℕ) {E s u M : ℝ} (hd : 2 ≤ d) (hM : 0 ≤ M)
    (hsu : s ≤ u) (hu : u < 1) (hwin : 1 - s ≤ sz.lam n ^ 2)
    (hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u) (σ : Fin 2 → Bool)
    (𝒜 : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hker : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (𝒜 v)‖ ≤
        M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3)))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖∫ v in s..u, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (𝒜 v) a‖ ≤
      M * (4 * STExpTarget sz n u * (2 * Real.log ((sz.L n : ℕ) : ℝ))) := by
  have hx : 0 < 1 - u := by linarith
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hLr : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL1
  have hl : sz.lam n ≠ 0 := by
    intro h0
    rw [h0] at hwin
    norm_num at hwin
    linarith
  have hlo' : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u := by
    refine le_trans ?_ hlo
    have h2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hLr hd
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h2
  have hT0 : 0 ≤ STExpTarget sz n u := st6_target_nonneg sz n hu
  have hrate := expIntII_rates_le_target sz n hu hl hlo'
  have hcube := st6_cube_le_target sz n hu
  have hlogL : 0 ≤ 2 * Real.log ((sz.L n : ℕ) : ℝ) := mul_nonneg (by norm_num) (Real.log_nonneg hLr)
  have hbound : ∀ v : ℝ, s ≤ v → v ≤ u →
      M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3)) ≤
        (M * (4 * STExpTarget sz n u)) * (1 - v)⁻¹ := by
    intro v hv1 hv2
    have hvu : v < 1 := lt_of_le_of_lt hv2 hu
    have hmono := STBctl_mono sz n hv2 hu
    have hBv := (STBctl_pos sz n hvu).le
    have h1 : sz.Bctl n v ^ (11 / 5 : ℝ) ≤ sz.Bctl n u ^ (11 / 5 : ℝ) :=
      Real.rpow_le_rpow hBv hmono (by norm_num)
    have h2 : sz.Bctl n v ^ (5 / 2 : ℝ) ≤ sz.Bctl n u ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow hBv hmono (by norm_num)
    have h3 : sz.Bctl n v ^ 3 ≤ sz.Bctl n u ^ 3 := pow_le_pow_left₀ hBv hmono 3
    have hinv : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
    calc M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3))
        ≤ M * ((1 - v)⁻¹ * (4 * STExpTarget sz n u)) := by
          gcongr
          linarith
      _ = (M * (4 * STExpTarget sz n u)) * (1 - v)⁻¹ := by ring
  have hint : IntervalIntegrable (fun v : ℝ => (M * (4 * STExpTarget sz n u)) * (1 - v)⁻¹) volume s u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
    intro v hv
    rw [Set.uIcc_of_le hsu] at hv
    have : v ≤ u := hv.2
    change 1 - v ≠ 0
    linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun v => RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (𝒜 v) a)
    (g := fun v : ℝ => (M * (4 * STExpTarget sz n u)) * (1 - v)⁻¹) hsu
    (Filter.Eventually.of_forall fun v hv =>
      ((norm_le_pi_norm _ a).trans (hker v hv.1.le hv.2)).trans (hbound v hv.1.le hv.2)) hint
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hlog := expIntI_log_ratio (L := sz.L n) (g := sz.lam n) hL1 hsu hu hwin hlo
  calc M * (4 * STExpTarget sz n u) * ∫ v in s..u, (1 - v)⁻¹
      ≤ M * (4 * STExpTarget sz n u) * (2 * Real.log ((sz.L n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = M * (4 * STExpTarget sz n u * (2 * Real.log ((sz.L n : ℕ) : ℝ))) := by ring


/-- The triangle inequality for the three terms of `STExpQsrc`. -/
private theorem expIntIQ_norm_three {x y z : ℂ} : ‖x + y - z‖ ≤ ‖x‖ + (‖y‖ + ‖z‖) := by
  calc ‖x + y - z‖ ≤ ‖x + y‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by gcongr; exact norm_add_le _ _
    _ = ‖x‖ + (‖y‖ + ‖z‖) := by ring

/-- **The sup bound of the `ϑ*`-source** (`‖A*_v‖ ≺ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2} + B_v³)`): `lem_+Q` (`stQopNorm_holds`, `m = 1`,
`C_n ε` small) on the drift tensor `D_v` (`STExpDriftDecayConcl`, `STExpDriftHiConcl`), and the second conjunct of `STExpWardIConcl'`
for `ϑ*` for the commutator and `(𝒫f) ∂ϑ*`. -/
private theorem expIntIQ_src_sup {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (sz : Sizes d) (z : ℕ → ℂ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n))
    (hdr : STExpDriftHiConcl sz (STflowE z) s t) (hdd : STExpDriftDecayConcl sz (STflowE z) s t)
    (hW : STExpWardIConcl' sz (STflowE z) s t) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : {σ : Fin 2 → Bool // σ 0 ≠ σ 1},
      ‖STExpQsrc sz n (STflowE z n) v σ.1 (expIntIQ_star sz n)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) +
          sz.Bctl n v ^ 3)) := by
  obtain ⟨h𝔠, -, hSz, hBw, hWO⟩ := hflow.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := scaleFacts3_W_tendsto sz hflow.1
  have hd0 : 0 < d := by omega
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨Cs, cs, hCs0, hcs0, hstar⟩ := expIntIQ_star_abs d sz 𝔡 hWO
  set K : ℝ := 1 / 𝔠 with hK
  obtain ⟨Cn, hCn, hpin⟩ := stQopNorm_holds d hd 1 𝔡⁻¹ K Cs cs (inv_pos.2 h𝔡) (one_div_pos.2 h𝔠) hCs0 hcs0
  set τ₁ : ℝ := τ / 4 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  set εQ : ℝ := min (1 / 2) (τ * d / (4 * Cn)) with hεQ
  have hεQ0 : 0 < εQ := lt_min (by norm_num) (by positivity)
  have hεQ1 : εQ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set DQ : ℝ := Cn + 5 / 𝔠 + 1 with hDQ
  have h5c' : 0 < 5 / 𝔠 := by positivity
  have hDQ0 : 0 < DQ := by rw [hDQ]; linarith
  have hDQ1 : 1 < DQ := by rw [hDQ]; linarith
  have hdrift := expIntIQ_drift_pi sz hSz ht1 hdr hτ₁0
  have hw2 := (st6_prec_det_iff sz hSz
    (V := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q => ‖STQop (d := d) (expIntIQ_star sz n) (q.1 : ℝ) (STthetaOp sz n (STflowE z n) (q.1 : ℝ) q.2.1.1
        (fun c => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 c)) q.2.2 -
      STthetaOp sz n (STflowE z n) (q.1 : ℝ) q.2.1.1
        (STQop (d := d) (expIntIQ_star sz n) (q.1 : ℝ) (fun c => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 c)) q.2.2‖ +
      ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        deriv (fun τ => expIntIQ_star sz n τ q.2.2) (q.1 : ℝ)‖)
    (fun n q => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)).1
    (hW Cs cs hCs0 hcs0 (expIntIQ_star sz) hstar).2 τ₁ hτ₁0
  have hdecD : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, ({ω | ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) εQ DQ
        (fun a => STExpDrift sz n (STflowE z n) (v : ℝ) σ a)} : Set sz.SeqΩ).Nonempty :=
    fun σ => HighProbAt.nonempty (tendsto_size sz hSz) measure_univ (hdd σ εQ DQ hεQ0 hDQ0)
  have hall := Filter.eventually_all.2 hdecD
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO, st6_lam_pos sz hWO] with n h1 h2
    exact ⟨h2, h1.2⟩
  filter_upwards [hdrift, hw2, hall, hstar, hlam, hBw,
    ((tendsto_rpow_atTop hεQ0).comp hWt).eventually (eventually_ge_atTop (4 : ℝ)),
    hSz.eventually (eventually_ge_atTop (1 : ℝ)),
    ((tendsto_rpow_atTop (half_pos hτ)).comp hSz).eventually (eventually_ge_atTop (3 : ℝ))]
    with n hdrn hw2n hdn hstn hlamn hBn h4 hN1 hN3
  intro v hv1 hv2 σ
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hv0 : 0 ≤ v := (hs0 n).trans hv1
  have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
  have hN0 : 0 < N := by linarith
  have hW0 : 0 ≤ W := Nat.cast_nonneg _
  have h4' : 4 ≤ W ^ εQ := h4
  have hN3' : 3 ≤ N ^ (τ / 2) := hN3
  have hW1 : 1 < W := by
    by_contra hcon
    push Not at hcon
    have := Real.rpow_le_one hW0 hcon hεQ0.le
    linarith
  have hW0' : 0 < W := by linarith
  have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ K := by
    refine (expIntIQ_L_le_N sz n).trans ?_
    have := expIntIQ_N_le_W sz h𝔠 n hBn 1
    simpa [hK] using this
  -- `lem_+Q` on the drift tensor
  have hDdec : EKFastDecay (sz.lam n) v W εQ DQ (fun c => STExpDrift sz n (STflowE z n) v σ.1 c) := by
    obtain ⟨ω, hω⟩ := hdn σ.1
    exact hω ⟨v, hv1, hv2⟩
  have hQ := hpin (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 hlamn.2 W εQ DQ hW1 hεQ0 hεQ1 hDQ1 h4' hLW
    (expIntIQ_star sz n) hstn v hv0 hvl (fun c => STExpDrift sz n (STflowE z n) v σ.1 c) hDdec
  have hD := hdrn ⟨v, hv1, hv2⟩ σ.1
  have hWC : W ^ (Cn * εQ) ≤ N ^ τ₁ := by
    have h1 : W ^ (Cn * εQ) ≤ N ^ (Cn * εQ / d) := sz.W_rpow_le hd0 n (by positivity)
    refine h1.trans (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
    rw [div_le_iff₀ hd0']
    have : Cn * εQ ≤ Cn * (τ * d / (4 * Cn)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hCn.le
    have e : Cn * (τ * d / (4 * Cn)) = τ₁ * d := by rw [hτ₁]; field_simp
    linarith
  have hTail : W ^ (-DQ + Cn) ≤ N ^ (-(5 : ℝ)) := by
    have hexp : -DQ + Cn ≤ -(5 / 𝔠) := by rw [hDQ]; linarith
    have h1 : W ^ (-DQ + Cn) ≤ W ^ (-(5 / 𝔠)) := Real.rpow_le_rpow_of_exponent_le hW1.le hexp
    have hNc : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    have h2 : W ^ (-(5 / 𝔠)) ≤ (N ^ 𝔠) ^ (-(5 / 𝔠)) :=
      Real.rpow_le_rpow_of_nonpos hNc hBn (by linarith)
    have h3 : (N ^ 𝔠) ^ (-(5 / 𝔠)) = N ^ (-(5 : ℝ)) := by
      rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
    exact h1.trans (h2.trans h3.le)
  -- the control `X_v`
  set B : ℝ := sz.Bctl n v with hBdef
  have hB0 : 0 ≤ B := expIntIQ_Bctl_nonneg sz n v
  have hBge : N⁻¹ ≤ B := expAvg_Bctl_ge sz n hv0 hvl
  have hx1 : 1 ≤ (1 - v)⁻¹ := by
    refine (one_le_inv₀ (by linarith)).2 (by linarith)
  have hx0 : 0 ≤ (1 - v)⁻¹ := by linarith
  have hr1 : 0 ≤ B ^ (11 / 5 : ℝ) := Real.rpow_nonneg hB0 _
  have hr2 : 0 ≤ B ^ (5 / 2 : ℝ) := Real.rpow_nonneg hB0 _
  have hr3 : 0 ≤ B ^ 3 := by positivity
  set Xd : ℝ := (1 - v)⁻¹ * (B ^ (11 / 5 : ℝ) + B ^ (5 / 2 : ℝ)) with hXd
  set Xw : ℝ := (1 - v)⁻¹ * B ^ 3 with hXw
  have hXd0 : 0 ≤ Xd := by positivity
  have hXw0 : 0 ≤ Xw := by positivity
  have hXe : (1 - v)⁻¹ * (B ^ (11 / 5 : ℝ) + B ^ (5 / 2 : ℝ) + B ^ 3) = Xd + Xw := by
    rw [hXd, hXw]; ring
  have hNB3 : N ^ (-(3 : ℝ)) ≤ B ^ 3 := by
    have hN1' : (1 : ℝ) ≤ N := hN1
    rw [Real.rpow_neg hN0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hBge 3
  have hXlow : N ^ (-(5 : ℝ)) ≤ Xd + Xw := by
    have h1 : N ^ (-(5 : ℝ)) ≤ N ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have h2 : B ^ 3 ≤ Xw := by
      rw [hXw]
      exact le_mul_of_one_le_left hr3 hx1
    linarith
  -- the pointwise bound
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  have hw := hw2n (⟨v, hv1, hv2⟩, σ, a)
  have h0 : ‖STExpQsrc sz n (STflowE z n) v σ.1 (expIntIQ_star sz n) a‖ ≤
      ‖STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpDrift sz n (STflowE z n) v σ.1 c) a‖ +
      (‖STQop (d := d) (expIntIQ_star sz n) v (STthetaOp sz n (STflowE z n) v σ.1
            (fun c => STExpErr sz n (STflowE z n) v σ.1 c)) a -
          STthetaOp sz n (STflowE z n) v σ.1
            (STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpErr sz n (STflowE z n) v σ.1 c)) a‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) v σ.1 b) (a 0) *
          deriv (fun τ => expIntIQ_star sz n τ a) v‖) := expIntIQ_norm_three
  have h1 : ‖STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpDrift sz n (STflowE z n) v σ.1 c) a‖ ≤
      N ^ τ₁ * (N ^ τ₁ * Xd) + (Xd + Xw) := by
    refine (norm_le_pi_norm _ a).trans (hQ.trans ?_)
    have h2 : W ^ (Cn * εQ) * ‖(fun c => STExpDrift sz n (STflowE z n) v σ.1 c)‖ ≤ N ^ τ₁ * (N ^ τ₁ * Xd) :=
      mul_le_mul hWC hD (norm_nonneg _) (Real.rpow_nonneg hN0.le _)
    linarith [hTail.trans hXlow |>.trans le_rfl]
  have hP1 : 1 ≤ N ^ τ₁ := Real.one_le_rpow hN1 hτ₁0.le
  have hPP : N ^ τ₁ * N ^ τ₁ = N ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; rw [hτ₁]; ring
  have hQQ : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hP0 : 0 ≤ N ^ τ₁ := by linarith
  have hPP1 : 1 ≤ N ^ τ₁ * N ^ τ₁ := one_le_mul_of_one_le_of_one_le hP1 hP1
  have hPPP : N ^ τ₁ ≤ N ^ τ₁ * N ^ τ₁ := le_mul_of_one_le_right hP0 hP1
  have hPP3 : 3 ≤ N ^ τ₁ * N ^ τ₁ := by rw [hPP]; exact hN3'
  have hfin : N ^ τ₁ * (N ^ τ₁ * Xd) + (Xd + Xw) + N ^ τ₁ * Xw ≤ N ^ τ * (Xd + Xw) := by
    have e1 : 1 * Xd ≤ (N ^ τ₁ * N ^ τ₁) * Xd := mul_le_mul_of_nonneg_right hPP1 hXd0
    have e2 : 1 * Xw ≤ (N ^ τ₁ * N ^ τ₁) * Xw := mul_le_mul_of_nonneg_right hPP1 hXw0
    have e3 : N ^ τ₁ * Xw ≤ (N ^ τ₁ * N ^ τ₁) * Xw := mul_le_mul_of_nonneg_right hPPP hXw0
    have e0 : 0 ≤ (N ^ τ₁ * N ^ τ₁) * (Xd + Xw) := by positivity
    have e4 : (N ^ τ₁ * N ^ τ₁) * 3 ≤ (N ^ τ₁ * N ^ τ₁) * (N ^ τ₁ * N ^ τ₁) :=
      mul_le_mul_of_nonneg_left hPP3 (by positivity)
    have e5 : (N ^ τ₁ * N ^ τ₁) * (N ^ τ₁ * N ^ τ₁) = N ^ τ := by rw [hPP, hQQ]
    have e6 : (N ^ τ₁ * N ^ τ₁) * 3 * (Xd + Xw) ≤ N ^ τ * (Xd + Xw) := by
      rw [← e5]
      exact mul_le_mul_of_nonneg_right e4 (by positivity)
    linarith
  calc ‖STExpQsrc sz n (STflowE z n) v σ.1 (expIntIQ_star sz n) a‖
      ≤ _ := h0
    _ ≤ (N ^ τ₁ * (N ^ τ₁ * Xd) + (Xd + Xw)) + N ^ τ₁ * Xw := add_le_add h1 hw
    _ ≤ N ^ τ * (Xd + Xw) := hfin
    _ = N ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3)) := by
        rw [← hXe]


/-- **Target 7 (step 4, the `ϑ*` bound)**: the paper's route `6:109-132` for `ϑ*`.  The `𝒬`-Duhamel identity
of `ϑ*` (`stExpDuhamelQ_holds`, `st6_duhEqQ_of_pin`, target 1), every source sum-zero (target 4) and
decaying (target 5), the sup bound `‖A*_v‖ ≺ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2} + B_v³)` (`expIntIQ_src_sup`:
`lem_+Q`, `stQopNorm_holds`, for `𝒬*D`; the second Ward conjunct for `ϑ*` for the commutator and
`(𝒫f) ∂ϑ*`), the sum-zero branch of `expIntI_kernel_unif`, `∫_s^u (1-v)⁻¹ ≤ 2 log L` (`expIntI_log_ratio`),
the rates `B_v^{11/5} + B_v^{5/2} + B_v³ ≤ 4 T_u` (`expIntII_rates_le_target`, `st6_cube_le_target`) and
`log L ≺ 1` (`expIntII_log_eventually`): `‖𝒰_{s,u} 𝒬*_s f_s‖ ≺ G` gives `‖𝒬*_u f_u‖ ≺ G + T_u`.  The sum-zero
and decaying families are guarded by `0 < ilambda_n ∧ s_n ≤ v ≤ t_n`. -/
theorem expIntIQ_star_bound (d : ℕ) (hd : 3 ≤ d) (κ ε 𝔠 𝔡 𝔠d : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t)
    (hdd : STExpDriftDecayConcl sz (STflowE z) s t) (hW : STExpWardIConcl' sz (STflowE z) s t)
    (G : ∀ n, STIdx2P sz STSigMixed s t n → ℝ) (_hG : ∀ n p, 0 ≤ G n p)
    (hG1 : Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => G n p)) :
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ)
        (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p + STExpTarget sz n (p.1 : ℝ)) := by
  classical
  obtain ⟨h𝔠, -, hSz, hBw, hWO⟩ := hflow.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hs1 : ∀ n, s n < 1 := fun n => lt_trans (hst n) (ht1 n)
  obtain ⟨Cs, cs, hCs0, hcs0, hstar⟩ := expIntIQ_star_abs d sz 𝔡 hWO
  have hduh := st6_duhEqQ_of_pin sz (stExpDuhamelQ_holds d) hd hκ hflow hs0 htT Cs cs (expIntIQ_star sz) hstar
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n := st6_lam_pos sz hWO
  -- the kernel bound, integrated, one sign vector at a time
  have key : ∀ σ : {σ : Fin 2 → Bool // STSigMixed σ}, ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      ∀ (u : TimeIcc s t n) (a : Fin 2 → Zd d (sz.L n)),
        ‖∫ v in (s n)..(u : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 v (u : ℝ)
            (STExpQsrc sz n (STflowE z n) v σ.1 (expIntIQ_star sz n)) a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * (32 * (STExpTarget sz n (u : ℝ) * Real.log ((sz.L n : ℕ) : ℝ))) := by
    intro σ τ hτ
    obtain ⟨𝒜, h𝒜⟩ : ∃ 𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ, ∀ n v, 𝒜 n v =
        if (0 < sz.lam n ∧ s n ≤ v ∧ v ≤ t n)
        then STExpQsrc sz n (STflowE z n) v σ.1 (expIntIQ_star sz n) else 0 := ⟨_, fun _ _ => rfl⟩
    obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ → ℝ, ∀ n v, X n v = |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) +
        sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3) := ⟨_, fun _ _ => rfl⟩
    have hcase : ∀ n v, EKSumZero (𝒜 n v) := by
      intro n v
      rw [h𝒜]
      split_ifs with hg
      · exact expIntIQ_src_sumZero d hd sz n (STflowE z n) (st6_flowE_lt_two sz hκ hflow n).le hg.1 v
          ((hs0 n).trans hg.2.1) (lt_of_le_of_lt hg.2.2 (ht1 n)) σ.1
      · intro i₀ hi₀ x
        simp
    have hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v) := by
      intro ε' D hε' hD
      filter_upwards [expIntIQ_src_decay d hd κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow s t hs0 hst htT hR hdr hdd ε' D hε' hD,
        hlam] with n hn hl
      intro v hv1 hv2
      rw [h𝒜, ite_eq_left ⟨hl, hv1, hv2⟩]
      exact hn v hv1 hv2 σ.1
    have hX0 : ∀ n v, 0 ≤ X n v := by
      intro n v
      rw [hXdef]
      have hB0 := expIntIQ_Bctl_nonneg sz n v
      positivity
    have hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v := by
      refine ⟨3, Filter.Eventually.of_forall fun n v hv1 hv2 => ?_⟩
      have hv0 : 0 ≤ v := (hs0 n).trans hv1
      have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hB := expAvg_Bctl_ge sz n hv0 hvl
      have hB0 := expIntIQ_Bctl_nonneg sz n v
      have h1 : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ (sz.Bctl n v) ^ 3 := by
        rw [Real.rpow_neg hN0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hB 3
      have hx1 : 1 ≤ |1 - v|⁻¹ := by
        rw [abs_of_pos (by linarith : 0 < 1 - v)]
        exact (one_le_inv₀ (by linarith)).2 (by linarith)
      have h5 : 0 ≤ sz.Bctl n v ^ (5 / 2 : ℝ) := Real.rpow_nonneg hB0 _
      have h6 : 0 ≤ sz.Bctl n v ^ (11 / 5 : ℝ) := Real.rpow_nonneg hB0 _
      have h7 : 0 ≤ sz.Bctl n v ^ 3 := by positivity
      rw [hXdef]
      calc ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ sz.Bctl n v ^ 3 := h1
        _ ≤ sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3 := by linarith
        _ ≤ |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3) :=
            le_mul_of_one_le_left (by linarith) hx1
    have hbd : ∀ τ' : ℝ, 0 < τ' → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * X n v := by
      intro τ' hτ'
      filter_upwards [expIntIQ_src_sup hd h𝔡 sz z hflow s t hs0 htT hdr hdd hW τ' hτ', hlam] with n hn hl
      intro v hv1 hv2
      rw [h𝒜, ite_eq_left ⟨hl, hv1, hv2⟩, hXdef, abs_of_pos (by linarith [ht1 n] : 0 < 1 - v)]
      exact hn v hv1 hv2 σ
    have hk := expIntI_kernel_unif hd hκ hε h𝔡 h𝔠d hdc sz z hflow s t hs0 hst htT hR hcon σ.1 𝒜 X (Or.inr hcase)
      hdec hX0 hlow hbd τ hτ
    filter_upwards [hk, hlam] with n hkn hln
    intro u a
    have hsu : s n ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
    have hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - (u : ℝ) := by
      have := (hR n).1
      have h2 : (u : ℝ) ≤ t n := u.2.2
      linarith
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hint := expIntIQ_integral_le sz n (E := STflowE z n) (s := s n) (u := (u : ℝ))
      (M := ((sz.size n : ℕ) : ℝ) ^ τ * 4) (by omega) (by positivity) hsu hu1 (hR n).2 hlo σ.1
      (fun v => STExpQsrc sz n (STflowE z n) v σ.1 (expIntIQ_star sz n)) ?_ a
    · refine hint.trans (le_of_eq ?_)
      ring
    · intro v hv1 hv2
      have h0 := hkn u v hv1 hv2
      have hvl : 0 < 1 - v := by linarith [hu1]
      rw [h𝒜, ite_eq_left ⟨hln, hv1, hv2.trans u.2.2⟩, hXdef, abs_of_pos hvl] at h0
      refine h0.trans (le_of_eq ?_)
      ring
  -- assembly
  refine (st6_prec_det_iff sz hSz (V := STIdx2P sz STSigMixed s t)
    (fun n p => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ)
      (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
    (fun n p => G n p + STExpTarget sz n (p.1 : ℝ))).2 ?_
  intro τ hτ
  have hGdet := ((st6_prec_det_iff sz hSz (V := STIdx2P sz STSigMixed s t)
    (fun n p => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
      (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
    (fun n p => G n p)).1 hG1) τ hτ
  have hlog := expIntII_log_eventually sz hSz (by omega : 1 ≤ d) 32 (half_pos hτ)
  filter_upwards [hduh, hGdet, Filter.eventually_all.2 (fun σ => key σ (τ / 2) (half_pos hτ)), hlog]
    with n hd1 hG2 hk hlg
  intro p
  obtain ⟨u, σ, a⟩ := p
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
  have hT0 : 0 ≤ STExpTarget sz n (u : ℝ) := st6_target_nonneg sz n hu1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hxx : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hP0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  change ‖STQop (d := d) (expIntIQ_star sz n) (u : ℝ) (fun b => STExpErr sz n (STflowE z n) (u : ℝ) σ.1 b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (G n (u, σ, a) + STExpTarget sz n (u : ℝ))
  rw [hd1 u σ.1 a]
  refine (norm_add_le _ _).trans ?_
  have h1 := hG2 (u, σ, a)
  have h2 := hk σ u a
  calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (u, σ, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (32 * (STExpTarget sz n (u : ℝ) * Real.log ((sz.L n : ℕ) : ℝ))) :=
        add_le_add h1 h2
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * G n (u, σ, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) * (32 * Real.log ((sz.L n : ℕ) : ℝ))) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (u, σ, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) := by
        gcongr
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (G n (u, σ, a) + STExpTarget sz n (u : ℝ)) := by
        rw [← hxx]; ring


/-! ## 7. Back to `ϑ` and the assembly (targets 8-11) -/

/-- **Target 8 (step 5, back to `ϑ`)**: `𝒬^ϑ_u f_u = 𝒬^{ϑ*}_u f_u + (𝒫 f_u)ϑ*_u - (𝒫 f_u)ϑ_u` (target 2 at time
`u`), the last two terms `≺ B_u³` by the first Ward conjunct (`(eq:EPL-K)` `6:104-107`) for `ϑ*` and for `ϑ`;
only `ϑ_u` and `ϑ*_u` occur, never `∂ϑ`. -/
theorem expIntIQ_back (d : ℕ) (sz : Sizes d) (hsz : sz.SizeTendsto) (E s t : ℕ → ℝ) (_hst : ∀ n, s n < t n)
    (_ht1 : ∀ n, t n < 1) (hW : STExpWardIConcl' sz E s t) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n))
    (hstar : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) ((1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1)) (1 / 2)
      (expIntIQ_star sz n))
    (G : ∀ n, STIdx2P sz STSigMixed s t n → ℝ) (hG : ∀ n p, 0 ≤ G n p)
    (hG1 : Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ)
        (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p)) :
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
        (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p + sz.Bctl n (p.1 : ℝ) ^ 3) := by
  have hCs0 : 0 < (1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1) := by positivity
  have hw1 := (hW C c hC hc ϑ hϑ).1
  have hw2 := (hW _ (1 / 2) hCs0 (by norm_num) (expIntIQ_star sz) hstar).1
  have hsum := StochDomAt.add (tendsto_size sz hsz) (StochDomAt.add (tendsto_size sz hsz) hG1 hw2) hw1
  refine st5_prec_mono sz hsz (c := 2) (StochDomAt.of_le_left (fun n p ω => ?_) hsum)
    (Eventually.of_forall fun n p ω => ?_) (fun n p ω => ?_)
  · have e : STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2 =
        STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2 +
          (STPsum (d := d) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
            expIntIQ_star sz n (p.1 : ℝ) p.2.2 -
          STPsum (d := d) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) * ϑ n (p.1 : ℝ) p.2.2) := by
      rw [expIntIQ_Qop_sub d (sz.L n) (expIntIQ_star sz n) (ϑ n) (p.1 : ℝ)]
      ring
    change ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖ ≤
      ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
          expIntIQ_star sz n (p.1 : ℝ) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) * ϑ n (p.1 : ℝ) p.2.2‖
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (norm_sub_le _ _)
      _ = _ := by ring
  · have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) ^ 3 := by
      have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
      positivity
    have := hG n p
    change G n p + sz.Bctl n (p.1 : ℝ) ^ 3 + sz.Bctl n (p.1 : ℝ) ^ 3 ≤ 2 * (G n p + sz.Bctl n (p.1 : ℝ) ^ 3)
    linarith
  · have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) ^ 3 := by
      have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
      positivity
    have := hG n p
    change 0 ≤ G n p + sz.Bctl n (p.1 : ℝ) ^ 3
    linarith

/-- **Target 9 (assembly)**: the second conjunct `STExpIntQConcl'` of `STExpIntI'` under the premises of
`STIngR6`, regime (i): targets 6, 7 (`G = F + B³`), 8, then `F + B³ + T + B³ ≤ 3 (F + T)` (`B_u³ ≤ T_u`,
`st6_cube_le_target`) absorbed by `Prec`.  The `𝒬`-Duhamel premise for the given `ϑ` is not used: the identity
is the one of `ϑ*` (`st6_duhEqQ_of_pin`, inside target 7). -/
theorem expIntIQ_concl (d : ℕ) (hd : 3 ≤ d) (κ ε 𝔠 𝔡 𝔠d : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d)
    (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t)
    (hdd : STExpDriftDecayConcl sz (STflowE z) s t) (hW : STExpWardIConcl' sz (STflowE z) s t) :
    STExpIntQConcl' sz (STflowE z) s t := by
  intro C c hC hc ϑ hϑ _ F hF hini
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hstar := expIntIQ_star_props d sz 𝔡 hflow.1.2.2.2.2
  have hB : ∀ n (p : STIdx2P sz STSigMixed s t n), 0 ≤ F n p + sz.Bctl n (p.1 : ℝ) ^ 3 := fun n p => by
    have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
    have := hF n p
    positivity
  have h6 := expIntIQ_ini d hd κ ε 𝔠 𝔡 𝔠d hκ hε h𝔡 h𝔠d hdc sz z hflow s t hs0 hst htT hR hcon hW C c hC hc ϑ hϑ F hF
    hini
  have h7 := expIntIQ_star_bound d hd κ ε 𝔠 𝔡 𝔠d hκ hε h𝔡 h𝔠d hdc sz z hflow s t hs0 hst htT hR hcon hdr hdd hW
    (fun n p => F n p + sz.Bctl n (p.1 : ℝ) ^ 3) hB h6
  have hT : ∀ n (p : STIdx2P sz STSigMixed s t n),
      0 ≤ F n p + sz.Bctl n (p.1 : ℝ) ^ 3 + STExpTarget sz n (p.1 : ℝ) := fun n p => by
    have := st6_target_nonneg sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    have := hB n p
    linarith
  have h8 := expIntIQ_back d sz hsz (STflowE z) s t hst ht1 hW C c hC hc ϑ hϑ hstar
    (fun n p => F n p + sz.Bctl n (p.1 : ℝ) ^ 3 + STExpTarget sz n (p.1 : ℝ)) hT h7
  refine st5_prec_mono sz hsz (c := 3) h8 (Eventually.of_forall fun n p ω => ?_) (fun n p ω => ?_)
  · have hu1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
    have h2 := st6_cube_le_target sz n hu1
    have h3 := hF n p
    change F n p + sz.Bctl n (p.1 : ℝ) ^ 3 + STExpTarget sz n (p.1 : ℝ) + sz.Bctl n (p.1 : ℝ) ^ 3 ≤
      3 * (F n p + STExpTarget sz n (p.1 : ℝ))
    linarith
  · have := st6_target_nonneg sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    have := hF n p
    change 0 ≤ F n p + STExpTarget sz n (p.1 : ℝ)
    linarith

/-- **Target 10**: the merged primed pin `STExpIntI'` (`Induction/ExpIntI.lean:71`), proved.  The constant is
`𝔠_d = 1/(100 d)` (`𝔠_d ≤ 1/100`, `d 𝔠_d = 1/100 < 1`, as `stExpIniI'_holds`); the first conjunct is the merged
`expIntI_same`, the second is `expIntIQ_concl`. -/
theorem stExpIntI'_holds (d : ℕ) : STExpIntI' d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have h𝔠d : 0 < 1 / (100 * (d : ℝ)) := by positivity
  have hdc : (d : ℝ) * (1 / (100 * (d : ℝ))) < 1 := by
    rw [show (d : ℝ) * (1 / (100 * (d : ℝ))) = 1 / 100 by field_simp]; norm_num
  refine ⟨1 / (100 * (d : ℝ)), h𝔠d, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · intro 𝔠 sz z hflow s t hs0 hst htT hR _ _ _ hcon _ _ _ _ hduh hdr hdd hward
    exact ⟨expIntI_same hd hκ hε h𝔡 h𝔠d hdc sz z hflow s t hs0 hst htT hR hcon hduh hdr hdd,
      expIntIQ_concl d hd κ ε 𝔠 𝔡 (1 / (100 * (d : ℝ))) hκ hε h𝔡 h𝔠d hdc sz z hflow s t hs0 hst htT hR hcon hdr hdd
        hward⟩

/-- **Target 11**: Step 6, regime (i), with only `LWtermEXP` open: `ST_step6I_of_LW_Int` (T2239) discharges every
other regime-(i) pin by its merged proof, and `stExpIntI'_holds` the integrated pin. -/
theorem stStep6I_of_LW (d : ℕ) (h : LWtermEXP d) : STStep6I d :=
  ST_step6I_of_LW_Int d h (stExpIntI'_holds d)

end RBM.Gauss.Sizes

/-! ## 8. Compiled nonempty instances (`d = 3`, `szB`, `zB`, regime (i) times `(7/8, 15/16)`)

Data (merged, `Step34Inst`, `Step5Inst`): `L = 4`, `W_n = n + 4`, `ilambda = 1`, `z = 1/2 + i/64`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`𝔠_d = 1/300` (`d 𝔠_d = 1/100 < 1`); `1/16 = ilambda²/L² ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`.  Every deterministic hypothesis (flow, times,
regime, `(con_st_ind)` by `conStInd_const`, the `𝒬`-Duhamel identity by `st6_duhEqQ_of_pin`, the mollifier `ϑ*` by
`expIntIQ_star_props`) is discharged; what stays a hypothesis is another gate's pin: the drift conclusions `STExpDriftHiConcl`,
`STExpDriftDecayConcl`, the Ward conclusion `STExpWardIConcl'`, `LWtermEXP 3`, and the stochastic premises inside `InstIng6Concl`. -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- `stExpIntI'_holds 3` at the data of regime (i) (as `inst_expWardI'`, `ExpWardI.lean:469`). -/
theorem inst_expIntI' :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t →
        STExpWardIConcl' sz E s t → STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl' sz E s t)
      szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ (stExpIntI'_holds 3) szB_reg5I

/-- `expIntIQ_star_props` at `szB` (`ilambda ≡ 1`), constants `(121·216, 1/2)`. -/
theorem inst_expIntIQ_star_props :
    ∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1)) (1 / 2)
      (expIntIQ_star szB n) :=
  expIntIQ_star_props 3 szB (1 / 10) szB_WO

/-- `expIntIQ_concl` at `szB`, `zB`, `(7/8, 15/16)`, `𝔠_d = 1/300`, for the **positive** family `ϑ = ϑ*` (`0 < C*`, `0 < 1/2`,
admissible eventually, its `𝒬`-Duhamel identity discharged by `st6_duhEqQ_of_pin (stExpDuhamelQ_holds 3)`, `(con_st_ind)` by
`conStInd_const`); the drift and Ward conclusions stay hypotheses (as `inst_expWardI'_mixed`, `ExpWardI.lean:483`;
`inst_expIniI_mixed`, `ExpIniI.lean:1292`). -/
theorem inst_expIntI'_mixed :
    STExpDriftHiConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
    STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
    STExpWardIConcl' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
        (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧
        STExpDuhEqQ szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ϑ ∧
        ∀ F : ∀ n, STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n → ℝ, (∀ n p, 0 ≤ F n p) →
          Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
            (fun n p _ => ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (7 / 8) (p.1 : ℝ)
              (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErr szB n (STflowE zB n) (7 / 8) p.2.1.1 b)) p.2.2‖)
            (fun n p _ => F n p) →
          Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
            (fun n p _ => ‖STQop (d := 3) (ϑ n) (p.1 : ℝ)
              (fun b => STExpErr szB n (STflowE zB n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
            (fun n p _ => F n p + STExpTarget szB n (p.1 : ℝ)) := by
  intro hdr hdd hW
  have hduh : STExpDuhEqQ szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) (expIntIQ_star szB) :=
    st6_duhEqQ_of_pin szB (stExpDuhamelQ_holds 3) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
      (fun _ => by norm_num) (szB_flow_ht (by norm_num)) _ (1 / 2) (expIntIQ_star szB) inst_expIntIQ_star_props
  exact ⟨(1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1), 1 / 2, by norm_num, by norm_num, expIntIQ_star szB,
    inst_expIntIQ_star_props, hduh, fun F hF hini =>
    expIntIQ_concl 3 (by norm_num) (1 / 10) (1 / 10) (1 / 6) (1 / 10) (1 / 300) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16)
      (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5I
      (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hdr hdd hW _ (1 / 2)
      (by norm_num) (by norm_num) (expIntIQ_star szB) inst_expIntIQ_star_props hduh F hF hini⟩

/-- `stStep6I_of_LW` at `szB`, `zB`, `(7/8, 15/16)`: regime (i) of Step 6 with only `LWtermEXP 3` open (supersedes the second
hypothesis of `inst_skeleton6I''`). -/
theorem inst_stStep6I_of_LW :
    LWtermEXP 3 → InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  fun h => inst_step6I (stStep6I_of_LW 3 h)


/-- `expIntIQ_Qop_sub` at `d = 3`, `L = 4`, `s = 7/8`, the mollifiers `QopAlgebra_mollifier 3 4 1 g` at the two scales
`g = 1` and `g = 1/2`, and the diagonal tensor `A_a = 1_{a₁ = a₂}` (`𝒫A ≡ 1`). -/
theorem inst_expIntIQ_Qop_sub (a : Fin 2 → Zd 3 4) :
    STQop (d := 3) (QopAlgebra_mollifier 3 4 1 (1 / 2)) (7 / 8)
        (fun b : Fin 2 → Zd 3 4 => if b 0 = b 1 then (1 : ℂ) else 0) a =
      STQop (d := 3) (QopAlgebra_mollifier 3 4 1 1) (7 / 8)
        (fun b : Fin 2 → Zd 3 4 => if b 0 = b 1 then (1 : ℂ) else 0) a +
        STPsum (d := 3) (fun b : Fin 2 → Zd 3 4 => if b 0 = b 1 then (1 : ℂ) else 0) (a 0) *
          (QopAlgebra_mollifier 3 4 1 1 (7 / 8) a - QopAlgebra_mollifier 3 4 1 (1 / 2) (7 / 8) a) :=
  expIntIQ_Qop_sub 3 4 _ _ (7 / 8) _ a

/-- `expIntIQ_diff_sumZero` at `d = 3`, `L = 4`, `g = 1`, `s = 7/8`: the two admissible mollifiers `ϑ = QopAlgebra_mollifier 3 4 1 1`
(constants `(C*, 1/2)`, `QopAlgebra_mollifier_props`) and its index shift `ϑ'_a = ϑ_{(a₁, a₂ + 2e₀)}` (constants `(C*, 0)`,
`expIniI_props_shift`); `R = (𝒫A)(ϑ - ϑ')` for `A_a = 1_{a₁ = a₂}` is sum-zero. -/
theorem inst_expIntIQ_diff_sumZero :
    EKSumZero (fun a : Fin 2 → Zd 3 4 =>
      STPsum (d := 3) (fun b : Fin 2 → Zd 3 4 => if b 0 = b 1 then (1 : ℂ) else 0) (a 0) *
        (QopAlgebra_mollifier 3 4 1 1 (7 / 8) a -
          QopAlgebra_mollifier 3 4 1 1 (7 / 8) (fun i => if i = 0 then a 0 else a i + Pi.single 0 2))) :=
  expIntIQ_diff_sumZero 3 4 1 _ (1 / 2) _ 0 (QopAlgebra_mollifier 3 4 1 1)
    (fun t a => QopAlgebra_mollifier 3 4 1 1 t (fun i => if i = 0 then a 0 else a i + Pi.single 0 2))
    (QopAlgebra_mollifier_props 3 4 1 (by norm_num) one_pos)
    (expIniI_props_shift (d := 3) (L := 4) (m := 1) 1 _ (1 / 2) _ (Pi.single 0 2) (by norm_num)
      (QopAlgebra_mollifier_props 3 4 1 (by norm_num) one_pos)) (7 / 8) _

/-- `expIntIQ_src_sumZero` at `szB` (`d = 3`, `L = 4`, `ilambda = 1`), `n = 0`, `E = 0`, `v = 7/8`, `σ = (+,-)`: every hypothesis
is discharged. -/
theorem inst_expIntIQ_src_sumZero :
    EKSumZero (STExpQsrc szB 0 0 (7 / 8) ![true, false] (expIntIQ_star szB 0)) :=
  expIntIQ_src_sumZero 3 (by norm_num) szB 0 0 (by norm_num) (by simp [szB]) (7 / 8) (by norm_num) (by norm_num)
    ![true, false]

/-- `expIntIQ_src_decay` at `szB`, `zB`, `(7/8, 15/16)`: flow, times and regime are discharged; the drift conclusions
(`(eq:Exp(L-K)1)`, `(eq:ExpLWn=2)`, `(deccA0)` of the drift: S6-06, LW-14, S6-07) stay hypotheses. -/
theorem inst_expIntIQ_src_decay
    (hdr : STExpDriftHiConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hdd : STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, 7 / 8 ≤ v → v ≤ 15 / 16 → ∀ σ : Fin 2 → Bool,
      EKFastDecay (szB.lam n) v ((szB.W n : ℕ) : ℝ) ε' D
        (STExpQsrc szB n (STflowE zB n) v σ (expIntIQ_star szB n)) :=
  fun ε' D hε' hD => expIntIQ_src_decay 3 (by norm_num) (1 / 10) (1 / 10) (1 / 6) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5I hdr hdd ε' D hε' hD

/-- `expIntIQ_ini` at `szB`, `zB`, `(7/8, 15/16)`, `𝔠_d = 1/300`, for the positive mollifier family `st6_mollifier_family`
(`0 < C`, `0 < c`, admissible eventually); the Ward conclusion `STExpWardIConcl'` and the control `F` of the initial term of
`ϑ` stay hypotheses. -/
theorem inst_expIntIQ_ini
    (hW : STExpWardIConcl' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧
      ∀ F : ∀ n, STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n → ℝ, (∀ n p, 0 ≤ F n p) →
        Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
          (fun n p _ => ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (7 / 8) (p.1 : ℝ)
            (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErr szB n (STflowE zB n) (7 / 8) p.2.1.1 b)) p.2.2‖)
          (fun n p _ => F n p) →
        Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
          (fun n p _ => ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (7 / 8) (p.1 : ℝ)
            (STQop (d := 3) (expIntIQ_star szB n) (7 / 8)
              (fun b => STExpErr szB n (STflowE zB n) (7 / 8) p.2.1.1 b)) p.2.2‖)
          (fun n p _ => F n p + szB.Bctl n (p.1 : ℝ) ^ 3) := by
  obtain ⟨C, c, hC, hc, ϑ, hϑ⟩ := st6_mollifier_family szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10)
    flow_zB.1.2.2.2.2
  exact ⟨C, c, hC, hc, ϑ, hϑ, fun F hF hini =>
    expIntIQ_ini 3 (by norm_num) (1 / 10) (1 / 10) (1 / 6) (1 / 10) (1 / 300) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16)
      (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5I
      (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hW C c hC hc ϑ hϑ F hF hini⟩

/-- `expIntIQ_star_bound` at `szB`, `zB`, `(7/8, 15/16)`, `𝔠_d = 1/300`: the `ϑ*` bound; the drift and Ward conclusions and the
control `G` of the initial term stay hypotheses. -/
theorem inst_expIntIQ_star_bound
    (hdr : STExpDriftHiConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hdd : STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hW : STExpWardIConcl' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    ∀ G : ∀ n, STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n → ℝ, (∀ n p, 0 ≤ G n p) →
      Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
        (fun n p _ => ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (7 / 8) (p.1 : ℝ)
          (STQop (d := 3) (expIntIQ_star szB n) (7 / 8)
            (fun b => STExpErr szB n (STflowE zB n) (7 / 8) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => G n p) →
      Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
        (fun n p _ => ‖STQop (d := 3) (expIntIQ_star szB n) (p.1 : ℝ)
          (fun b => STExpErr szB n (STflowE zB n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
        (fun n p _ => G n p + STExpTarget szB n (p.1 : ℝ)) :=
  fun G hG hG1 => expIntIQ_star_bound 3 (by norm_num) (1 / 10) (1 / 10) (1 / 6) (1 / 10) (1 / 300) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16)
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5I
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hdr hdd hW G hG hG1

/-- `expIntIQ_back` at `szB`, `zB`, `(7/8, 15/16)`, for the positive mollifier family `st6_mollifier_family` and the explicit `ϑ*`
(`inst_expIntIQ_star_props`); the Ward conclusion and the bound `G` on `𝒬*_u f_u` stay hypotheses. -/
theorem inst_expIntIQ_back
    (hW : STExpWardIConcl' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧
      ∀ G : ∀ n, STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n → ℝ, (∀ n p, 0 ≤ G n p) →
        Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
          (fun n p _ => ‖STQop (d := 3) (expIntIQ_star szB n) (p.1 : ℝ)
            (fun b => STExpErr szB n (STflowE zB n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
          (fun n p _ => G n p) →
        Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
          (fun n p _ => ‖STQop (d := 3) (ϑ n) (p.1 : ℝ)
            (fun b => STExpErr szB n (STflowE zB n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
          (fun n p _ => G n p + szB.Bctl n (p.1 : ℝ) ^ 3) := by
  obtain ⟨C, c, hC, hc, ϑ, hϑ⟩ := st6_mollifier_family szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10)
    flow_zB.1.2.2.2.2
  exact ⟨C, c, hC, hc, ϑ, hϑ, fun G hG hG1 =>
    expIntIQ_back 3 szB flow_zB.1.2.2.1 (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num)
      (fun _ => by norm_num) hW C c hC hc ϑ hϑ inst_expIntIQ_star_props G hG hG1⟩

end RBM.Gauss.Step6Inst

end
