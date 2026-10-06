/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ExpEtermsB
import RBM3D.Induction.ExpDuhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.Filter.Finite

/-!
# S6-08 (T2235, ST-5): the integrated estimates of regimes (iii) and (iv), and `STStep6IV`

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:93-96` (regimes (iii), (iv)),
`(Eexpint_K-L)` (`6:3-7`) and `(sum_res_Ndecay)` (`paper/tex/3_5_Loop_Hierarchy.tex:1620-1622`).
No port: RBM2D `MLExpVocab_core` (`:~370`, a `log` integral from `0`) is a pattern only.

Duhamel with `A = ∅` (the premise `STExpDuhEq`) gives `f_u = 𝒰_{s,u} f_s + ∫_s^u 𝒰_{v,u} D_v dv`.
The kernel estimate `(sum_res_Ndecay)` with `n = 2` (`stek_sumNdecay_holds`) is used per time
sequence `u` on the deterministic drift `D_v`, with the factor `((1-v)/(1-u))²`.  The `u`-integral
is a deterministic one-size statement (`x^{-6/5}`, `x^{-3/2}` in regime (iii), `x^{-2}` in regime
(iv)).  The bound `∫_s^u 𝒰_{v,u} D_v dv ≺ T_u` is lifted from "per time sequence `u`" to "uniformly
in `u ∈ [s,t]`" once (`st6_precU_of_forall_seq`, both sides deterministic).  The pins
`STExpIntIII`, `STExpIntIV` follow (`Step6Pins.lean:425`, `:432`); `STStep6IV` is then the merged
skeleton `ST_step6_caseIV_of_pins`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The `u`-integral and the rates (deterministic, one size) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- The `u`-integrals of `6:94-96`: `∫_s^u (1-v)^{-r} dv = ((1-u)^{1-r} - (1-s)^{1-r})/(r-1) ≤ (1-u)^{1-r}/(r-1)`
for `r > 1` (used at `r = 6/5`, `3/2` (regime (iii)) and `r = 2` (regime (iv))). -/
theorem expIntEasy_integral_rpow {s u r : ℝ} (hsu : s ≤ u) (hu : u < 1) (hr : 1 < r) :
    ∫ v in s..u, (1 - v) ^ (-r) ≤ (r - 1)⁻¹ * (1 - u) ^ (1 - r) := by
  have hx : 0 < 1 - u := by linarith
  have hxs : 0 < 1 - s := by linarith
  have h1 : ∫ v in s..u, (1 - v) ^ (-r) = ∫ x in (1 - u)..(1 - s), x ^ (-r) :=
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-r)) 1
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 - u) (1 - s) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (not_le.2 hx)
  have h2 : ∫ x in (1 - u)..(1 - s), x ^ (-r) = ((1 - s) ^ (-r + 1) - (1 - u) ^ (-r + 1)) / (-r + 1) :=
    integral_rpow (Or.inr ⟨by linarith, h0⟩)
  rw [h1, h2]
  have hpos : 0 ≤ (1 - s) ^ (-r + 1) := Real.rpow_nonneg hxs.le _
  have hne : (-r + 1) ≠ 0 := by linarith
  have hrr : 1 - r = -r + 1 := by ring
  rw [hrr]
  have : ((1 - s) ^ (-r + 1) - (1 - u) ^ (-r + 1)) / (-r + 1) =
      (r - 1)⁻¹ * ((1 - u) ^ (-r + 1) - (1 - s) ^ (-r + 1)) := by
    have hneg : -r + 1 = -(r - 1) := by ring
    rw [hneg, div_neg, ← neg_div, neg_sub, div_eq_inv_mul]
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 (by linarith))

/-- `ilambda² ≤ 1-u`, `ilambda ≠ 0`: `B_u ≤ 2 (ilambda² W^d)⁻¹` (`B_u = W^{-d}(ilambda²+1-u)⁻¹ + (N(1-u))⁻¹`, `N ≥ W^d`). -/
private theorem expIntIII_Bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) (hl : sz.lam n ≠ 0)
    (hg : sz.lam n ^ 2 ≤ 1 - u) :
    sz.Bctl n u ≤ 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  have hx : 0 < 1 - u := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hl2 : 0 < sz.lam n ^ 2 := by positivity
  have hLd : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by
    have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
    exact one_le_pow₀ hL
  have hNeq : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hNeq]; nlinarith
  rw [st6_Bctl_eq sz n hu]
  have e1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hl2 (by linarith : sz.lam n ^ 2 ≤ sz.lam n ^ 2 + (1 - u)))
            (inv_nonneg.2 hWd.le)
      _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_inv, mul_comm]
  have e2 : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    apply inv_anti₀ (by positivity)
    calc sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d = ((sz.W n : ℕ) : ℝ) ^ d * sz.lam n ^ 2 := mul_comm _ _
      _ ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul hN hg hl2.le (by positivity)
  linarith

/-- Regime (iii) `ilambda² ≤ 1-u`: the rates against the target,
`5 (2B)^{11/5} + 2 (2B)^{5/2} ≤ 64 B²((ilambda²W^d)^{-1/5} + B)` (`B ≤ 2(ilambda²W^d)⁻¹`, so `B^{1/5} ≤ 2^{1/5}(ilambda²W^d)^{-1/5}`;
`B^{1/2} ≤ B^{1/5} + B`).  `ilambda ≠ 0`: at `ilambda = 0` Mathlib has `0^{-1/5} = 0`. -/
theorem expIntIII_rates_le_target {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) (hl : sz.lam n ≠ 0)
    (hg : sz.lam n ^ 2 ≤ 1 - u) :
    5 * (2 * sz.Bctl n u) ^ (11 / 5 : ℝ) + 2 * (2 * sz.Bctl n u) ^ (5 / 2 : ℝ) ≤ 64 * STExpTarget sz n u := by
  set B := sz.Bctl n u with hBdef
  have hB : 0 < B := STBctl_pos sz n hu
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set A := sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d with hAdef
  have hA : 0 < A := by positivity
  set G := A ^ (-(1 / 5 : ℝ)) with hGdef
  have hG : 0 < G := Real.rpow_pos_of_pos hA _
  have hBA : B ≤ 2 * A⁻¹ := expIntIII_Bctl_le sz n hu hl hg
  -- `B^{1/5} ≤ (6/5) G`
  have h2 : (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 6 / 5 := by
    have h5 : ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ 5 = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h0 : 0 ≤ (2 : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_nonneg (by norm_num) _
    by_contra hcon
    push Not at hcon
    have : (6 / 5 : ℝ) ^ 5 < ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ 5 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    rw [h5] at this
    norm_num at this
  have hB5 : B ^ (1 / 5 : ℝ) ≤ 6 / 5 * G := by
    calc B ^ (1 / 5 : ℝ) ≤ (2 * A⁻¹) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hB.le hBA (by norm_num)
      _ = (2 : ℝ) ^ (1 / 5 : ℝ) * G := by
          rw [Real.mul_rpow (by norm_num) (inv_nonneg.2 hA.le), Real.inv_rpow hA.le, hGdef, Real.rpow_neg hA.le]
      _ ≤ 6 / 5 * G := mul_le_mul_of_nonneg_right h2 hG.le
  -- `B^{1/2} ≤ B^{1/5} + B`
  have hBh : B ^ (1 / 2 : ℝ) ≤ B ^ (1 / 5 : ℝ) + B := by
    rcases le_or_gt B 1 with h1 | h1
    · have := Real.rpow_le_rpow_of_exponent_ge hB h1 (by norm_num : (1 / 5 : ℝ) ≤ 1 / 2)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num : (1 / 2 : ℝ) ≤ 1)
      rw [Real.rpow_one] at this
      have := Real.rpow_nonneg hB.le (1 / 5 : ℝ)
      linarith
  -- the two powers
  have e1 : (2 * B) ^ (11 / 5 : ℝ) = 4 * (2 : ℝ) ^ (1 / 5 : ℝ) * (B ^ 2 * B ^ (1 / 5 : ℝ)) := by
    have : (11 / 5 : ℝ) = 2 + 1 / 5 := by norm_num
    rw [Real.mul_rpow (by norm_num) hB.le, this, Real.rpow_add (by norm_num) , Real.rpow_add hB]
    have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    have hBB : B ^ (2 : ℝ) = B ^ 2 := by rw [← Real.rpow_natCast]; norm_num
    rw [h22, hBB]
  have e2 : (2 * B) ^ (5 / 2 : ℝ) = 4 * (2 : ℝ) ^ (1 / 2 : ℝ) * (B ^ 2 * B ^ (1 / 2 : ℝ)) := by
    have : (5 / 2 : ℝ) = 2 + 1 / 2 := by norm_num
    rw [Real.mul_rpow (by norm_num) hB.le, this, Real.rpow_add (by norm_num) , Real.rpow_add hB]
    have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    have hBB : B ^ (2 : ℝ) = B ^ 2 := by rw [← Real.rpow_natCast]; norm_num
    rw [h22, hBB]
  have h2h : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 2 := by
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h2n : 0 ≤ (2 : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h2hn : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hB5n : 0 ≤ B ^ (1 / 5 : ℝ) := Real.rpow_nonneg hB.le _
  have hB2 : 0 < B ^ 2 := by positivity
  -- first term: `5 (2B)^{11/5} ≤ 5 · 4 · (6/5) · (6/5) G B² = 28.8 G B²`
  have t1 : 5 * (2 * B) ^ (11 / 5 : ℝ) ≤ 29 * (B ^ 2 * G) := by
    rw [e1]
    have h3 : 4 * (2 : ℝ) ^ (1 / 5 : ℝ) * B ^ (1 / 5 : ℝ) ≤ 4 * (6 / 5) * (6 / 5 * G) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hB5 hB5n (by norm_num)
    calc 5 * (4 * (2 : ℝ) ^ (1 / 5 : ℝ) * (B ^ 2 * B ^ (1 / 5 : ℝ)))
        = 5 * B ^ 2 * (4 * (2 : ℝ) ^ (1 / 5 : ℝ) * B ^ (1 / 5 : ℝ)) := by ring
      _ ≤ 5 * B ^ 2 * (4 * (6 / 5) * (6 / 5 * G)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 29 * (B ^ 2 * G) := by nlinarith [mul_pos hB2 hG]
  -- second term: `2 (2B)^{5/2} ≤ 2 · 4 · (3/2) B² (B^{1/5} + B)`
  have t2 : 2 * (2 * B) ^ (5 / 2 : ℝ) ≤ 12 * (B ^ 2 * (B ^ (1 / 5 : ℝ) + B)) := by
    rw [e2]
    have h3 : 4 * (2 : ℝ) ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) ≤ 4 * (3 / 2) * (B ^ (1 / 5 : ℝ) + B) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h2h (by norm_num)) hBh (Real.rpow_nonneg hB.le _) (by norm_num)
    calc 2 * (4 * (2 : ℝ) ^ (1 / 2 : ℝ) * (B ^ 2 * B ^ (1 / 2 : ℝ)))
        = 2 * B ^ 2 * (4 * (2 : ℝ) ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) := by ring
      _ ≤ 2 * B ^ 2 * (4 * (3 / 2) * (B ^ (1 / 5 : ℝ) + B)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 12 * (B ^ 2 * (B ^ (1 / 5 : ℝ) + B)) := by ring
  have t3 : 12 * (B ^ 2 * (B ^ (1 / 5 : ℝ) + B)) ≤ 12 * (B ^ 2 * (6 / 5 * G + B)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hB2.le) (by norm_num)
  unfold STExpTarget
  rw [← hBdef, ← hAdef, ← hGdef]
  nlinarith [mul_pos hB2 hG, mul_pos hB2 hB]

/-- Regime (iv), the rate against the target (no regime hypothesis): `(N(1-u))^{-3} ≤ B_u³ ≤ T_u`. -/
theorem expIntIV_rate_le_target {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) :
    ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3 ≤ STExpTarget sz n u := by
  have hx : 0 < 1 - u := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have h1 : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ sz.Bctl n u := by
    rw [st6_Bctl_eq sz n hu]
    have : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ := by positivity
    linarith
  calc ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3 ≤ (sz.Bctl n u) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h1 3
    _ ≤ STExpTarget sz n u := st6_cube_le_target sz n hu

/-- `v ↦ (1-v)^p` is interval integrable on `[s,u]` for `u < 1`. -/
private theorem expIntEasy_ii_rpow {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) (p : ℝ) :
    IntervalIntegrable (fun v : ℝ => (1 - v) ^ p) volume s u := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hsu]
  apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
  intro x hx
  have := hx.2
  exact Or.inl (show 1 - x ≠ 0 from ne_of_gt (by linarith))

/-- The `u`-integral of one term: `∫_s^u (2B)^r (1-u)^{r-2} (1-v)^{-(r-1)} dv ≤ (r-2)⁻¹ (2B)^r` for `r > 2`
(the powers of `1-u` cancel exactly). -/
private theorem expIntEasy_term_integral {s u B r : ℝ} (hsu : s ≤ u) (hu : u < 1) (hB : 0 ≤ B) (hr : 2 < r) :
    ∫ v in s..u, (2 * B) ^ r * (1 - u) ^ (r - 2) * (1 - v) ^ (-(r - 1)) ≤ (r - 2)⁻¹ * (2 * B) ^ r := by
  have hx : 0 < 1 - u := by linarith
  rw [intervalIntegral.integral_const_mul]
  have h1 := expIntEasy_integral_rpow hsu hu (r := r - 1) (by linarith)
  have h2 : (1 - u) ^ (r - 2) * (1 - u) ^ (1 - (r - 1)) = 1 := by
    rw [← Real.rpow_add hx]
    have : r - 2 + (1 - (r - 1)) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hpos : 0 ≤ (2 * B) ^ r * (1 - u) ^ (r - 2) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hx.le _)
  calc (2 * B) ^ r * (1 - u) ^ (r - 2) * ∫ v in s..u, (1 - v) ^ (-(r - 1))
      ≤ (2 * B) ^ r * (1 - u) ^ (r - 2) * ((r - 1 - 1)⁻¹ * (1 - u) ^ (1 - (r - 1))) :=
        mul_le_mul_of_nonneg_left h1 hpos
    _ = (r - 2)⁻¹ * (2 * B) ^ r * ((1 - u) ^ (r - 2) * (1 - u) ^ (1 - (r - 1))) := by
        have : r - 1 - 1 = r - 2 := by ring
        rw [this]; ring
    _ = (r - 2)⁻¹ * (2 * B) ^ r := by rw [h2, mul_one]

/-- The pointwise step of regime (iii) (`(1-v)B_v ≤ 2(1-u)B_u`): for `0 < x_u ≤ x_v`, `B_v, B_u ≥ 0`, `r ≥ 0`,
`(x_v/x_u)² x_v⁻¹ B_v^r ≤ (2B_u)^r x_u^{r-2} x_v^{-(r-1)}`. -/
private theorem expIntIII_pointwise {xu xv Bv Bu r : ℝ} (hxu : 0 < xu) (hxv : xu ≤ xv) (hBv : 0 ≤ Bv)
    (hBu : 0 ≤ Bu) (hr : 0 ≤ r) (h : xv * Bv ≤ 2 * (xu * Bu)) :
    (xv / xu) ^ 2 * (xv⁻¹ * Bv ^ r) ≤ (2 * Bu) ^ r * xu ^ (r - 2) * xv ^ (-(r - 1)) := by
  have hxv0 : 0 < xv := lt_of_lt_of_le hxu hxv
  have h1 : Bv ^ r * xv ^ r = (xv * Bv) ^ r := by rw [Real.mul_rpow hxv0.le hBv, mul_comm]
  have h2 : (xv * Bv) ^ r ≤ (2 * (xu * Bu)) ^ r := Real.rpow_le_rpow (by positivity) h hr
  have h3 : (2 * (xu * Bu)) ^ r = (2 * Bu) ^ r * xu ^ r := by
    rw [show 2 * (xu * Bu) = xu * (2 * Bu) by ring, Real.mul_rpow hxu.le (by positivity), mul_comm]
  have hxr : 0 < xv ^ r := Real.rpow_pos_of_pos hxv0 _
  have h4 : Bv ^ r ≤ (2 * Bu) ^ r * xu ^ r * xv ^ (-r) := by
    rw [Real.rpow_neg hxv0.le, ← div_eq_mul_inv, le_div_iff₀ hxr, h1, ← h3]
    exact h2
  have e_xv : xv ^ (-(r - 1)) = xv * xv ^ (-r) := by
    rw [show -(r - 1) = 1 + -r by ring, Real.rpow_add hxv0, Real.rpow_one]
  have e_xu : xu ^ (r - 2) = xu ^ r / xu ^ 2 := by
    rw [Real.rpow_sub hxu, Real.rpow_two]
  have hcoef : 0 ≤ (xv / xu) ^ 2 * xv⁻¹ := by positivity
  calc (xv / xu) ^ 2 * (xv⁻¹ * Bv ^ r) = ((xv / xu) ^ 2 * xv⁻¹) * Bv ^ r := by ring
    _ ≤ ((xv / xu) ^ 2 * xv⁻¹) * ((2 * Bu) ^ r * xu ^ r * xv ^ (-r)) := mul_le_mul_of_nonneg_left h4 hcoef
    _ = (2 * Bu) ^ r * xu ^ (r - 2) * xv ^ (-(r - 1)) := by
        rw [e_xv, e_xu]
        field_simp

/-- Regime (iii), one size: a kernel bound `‖F v‖ ≤ M ((1-v)/(1-u))² (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` on `[s,u]`
(`(sum_res_Ndecay)`, `n = 2`) gives `‖∫_s^u F‖ ≤ M (5 (2B_u)^{11/5} + 2 (2B_u)^{5/2})`: `(1-v)B_v ≤ 2(1-u)B_u`
(`st6_xB_III` at `(v,u)`) turns the integrand into
`(1-u)^{-2}((2(1-u)B_u)^{11/5}(1-v)^{-6/5} + (2(1-u)B_u)^{5/2}(1-v)^{-3/2})`, then `expIntEasy_integral_rpow`
(no integrability of `F`: `norm_integral_le_of_norm_le`). -/
theorem expIntIII_drift_integral_le {d : ℕ} (sz : Sizes d) (n : ℕ) {s u M : ℝ} (F : ℝ → ℂ) (hM : 0 ≤ M)
    (hsu : s ≤ u) (hu : u < 1) (hg : sz.lam n ^ 2 ≤ 1 - u)
    (hF : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖F v‖ ≤ M * (((1 - v) / (1 - u)) ^ 2 *
        ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))))) :
    ‖∫ v in s..u, F v‖ ≤ M * (5 * (2 * sz.Bctl n u) ^ (11 / 5 : ℝ) + 2 * (2 * sz.Bctl n u) ^ (5 / 2 : ℝ)) := by
  have hx : 0 < 1 - u := by linarith
  have hBu : 0 ≤ sz.Bctl n u := (STBctl_pos sz n hu).le
  set Bu := sz.Bctl n u with hBu_def
  let ta : ℝ → ℝ := fun v => (2 * Bu) ^ (11 / 5 : ℝ) * (1 - u) ^ (11 / 5 - 2 : ℝ) * (1 - v) ^ (-(11 / 5 - 1 : ℝ))
  let tb : ℝ → ℝ := fun v => (2 * Bu) ^ (5 / 2 : ℝ) * (1 - u) ^ (5 / 2 - 2 : ℝ) * (1 - v) ^ (-(5 / 2 - 1 : ℝ))
  have hta : IntervalIntegrable ta volume s u := by
    have := (expIntEasy_ii_rpow hsu hu (-(11 / 5 - 1 : ℝ))).const_mul ((2 * Bu) ^ (11 / 5 : ℝ) * (1 - u) ^ (11 / 5 - 2 : ℝ))
    exact this
  have htb : IntervalIntegrable tb volume s u := by
    have := (expIntEasy_ii_rpow hsu hu (-(5 / 2 - 1 : ℝ))).const_mul ((2 * Bu) ^ (5 / 2 : ℝ) * (1 - u) ^ (5 / 2 - 2 : ℝ))
    exact this
  have hg_int : IntervalIntegrable (fun v => M * (ta v + tb v)) volume s u := (hta.add htb).const_mul M
  have hpt : ∀ v : ℝ, s ≤ v → v ≤ u → ‖F v‖ ≤ M * (ta v + tb v) := by
    intro v h1 h2
    have hxB := st6_xB_III sz n h2 hu hg
    have hBv : 0 ≤ sz.Bctl n v := (STBctl_pos sz n (lt_of_le_of_lt h2 hu)).le
    have hxv : 1 - u ≤ 1 - v := by linarith
    have p1 := expIntIII_pointwise hx hxv hBv hBu (r := 11 / 5) (by norm_num) hxB
    have p2 := expIntIII_pointwise hx hxv hBv hBu (r := 5 / 2) (by norm_num) hxB
    refine (hF v h1 h2).trans (mul_le_mul_of_nonneg_left ?_ hM)
    rw [mul_add, mul_add]
    exact add_le_add p1 p2
  have h1 : ‖∫ v in s..u, F v‖ ≤ ∫ v in s..u, M * (ta v + tb v) :=
    intervalIntegral.norm_integral_le_of_norm_le hsu
      (Filter.Eventually.of_forall fun v hv => hpt v hv.1.le hv.2) hg_int
  have h2 : ∫ v in s..u, M * (ta v + tb v) = M * ((∫ v in s..u, ta v) + ∫ v in s..u, tb v) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hta htb]
  have ia := expIntEasy_term_integral hsu hu (B := Bu) hBu (r := 11 / 5) (by norm_num)
  have ib := expIntEasy_term_integral hsu hu (B := Bu) hBu (r := 5 / 2) (by norm_num)
  have ea : ((11 / 5 : ℝ) - 2)⁻¹ = 5 := by norm_num
  have eb : ((5 / 2 : ℝ) - 2)⁻¹ = 2 := by norm_num
  rw [ea] at ia
  rw [eb] at ib
  calc ‖∫ v in s..u, F v‖ ≤ ∫ v in s..u, M * (ta v + tb v) := h1
    _ = M * ((∫ v in s..u, ta v) + ∫ v in s..u, tb v) := h2
    _ ≤ M * (5 * (2 * Bu) ^ (11 / 5 : ℝ) + 2 * (2 * Bu) ^ (5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add ia ib) hM

/-- Regime (iv), one size (no regime hypothesis): `‖F v‖ ≤ M ((1-v)/(1-u))² (1-v)⁻¹ (N(1-v))^{-3} = M N^{-3}(1-u)^{-2}(1-v)^{-2}`
on `[s,u]` gives `‖∫_s^u F‖ ≤ M (N(1-u))^{-3}` (`expIntEasy_integral_rpow` at `r = 2`). -/
theorem expIntIV_drift_integral_le {d : ℕ} (sz : Sizes d) (n : ℕ) {s u M : ℝ} (F : ℝ → ℂ) (hM : 0 ≤ M)
    (hsu : s ≤ u) (hu : u < 1)
    (hF : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖F v‖ ≤ M * (((1 - v) / (1 - u)) ^ 2 * ((1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3))) :
    ‖∫ v in s..u, F v‖ ≤ M * ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3 := by
  have hx : 0 < 1 - u := by linarith
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set K : ℝ := (N ^ 3)⁻¹ * ((1 - u) ^ 2)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  let g : ℝ → ℝ := fun v => M * (K * (1 - v) ^ (-(2 : ℝ)))
  have hgi : IntervalIntegrable g volume s u :=
    ((expIntEasy_ii_rpow hsu hu (-(2 : ℝ))).const_mul K).const_mul M
  have hpt : ∀ v : ℝ, s ≤ v → v ≤ u → ‖F v‖ ≤ g v := by
    intro v h1 h2
    have hxv : 0 < 1 - v := by linarith
    refine (hF v h1 h2).trans (le_of_eq ?_)
    simp only [g]
    rw [Real.rpow_neg hxv.le, Real.rpow_two, hK]
    congr 1
    field_simp
  have h1 : ‖∫ v in s..u, F v‖ ≤ ∫ v in s..u, g v :=
    intervalIntegral.norm_integral_le_of_norm_le hsu
      (Filter.Eventually.of_forall fun v hv => hpt v hv.1.le hv.2) hgi
  have h2 := expIntEasy_integral_rpow hsu hu (r := 2) (by norm_num)
  have h3 : ∫ v in s..u, g v = M * (K * ∫ v in s..u, (1 - v) ^ (-(2 : ℝ))) := by
    simp only [g]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h4 : (1 - u) ^ (1 - 2 : ℝ) = (1 - u)⁻¹ := by
    rw [show (1 - 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [h4] at h2
  calc ‖∫ v in s..u, F v‖ ≤ ∫ v in s..u, g v := h1
    _ = M * (K * ∫ v in s..u, (1 - v) ^ (-(2 : ℝ))) := h3
    _ ≤ M * (K * ((2 - 1 : ℝ)⁻¹ * (1 - u)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK0) hM
    _ = M * (N * (1 - u))⁻¹ ^ 3 := by
        rw [hK, show (2 - 1 : ℝ) = 1 by norm_num, inv_one, one_mul]
        field_simp

end RBM.Gauss.Sizes

/-! ## 2. The kernel estimate per time sequence (`(sum_res_Ndecay)`, `n = 2`, on the deterministic drift) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- `(sum_res_Ndecay)` (`stek_sumNdecay_holds`, `n = 2`, any `σ`, `m = mE E`) applied to the deterministic drift `D_v` along one
time sequence `u` (`s ≤ u < 1`): from an eventual bound `‖D_v^σ‖_∞ ≤ N^τ X_v` on `[s_n,u_n]` (every `τ > 0`) the same for
`‖𝒰_{v,u}D_v^σ‖_∞` with the factor `((1-v)/(1-u))²`, uniformly in `v ∈ [s_n,u_n]` and `σ` (no lift: `u` is one sequence). -/
theorem expIntEasy_kernel_seq {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s u : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsu : ∀ n, s n ≤ u n)
    (hu1 : ∀ n, u n < 1) (X : ℕ → ℝ → ℝ) (hX : ∀ n v, s n ≤ v → v ≤ u n → 0 ≤ X n v)
    (h : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpDrift sz n (STflowE z n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool,
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u n)
          (fun b => STExpDrift sz n (STflowE z n) v σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - v) / (1 - u n)) ^ 2 * X n v) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have key : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, ∀ v : TimeIcc s u n,
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ (v : ℝ) (u n)
          (fun b => STExpDrift sz n (STflowE z n) (v : ℝ) σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - (v : ℝ)) / (1 - u n)) ^ 2 * X n (v : ℝ)) := by
    intro σ
    have hdom : sz.Prec (U := fun n => TimeIcc s u n)
        (fun n v _ => ‖(fun b => STExpDrift sz n (STflowE z n) (v : ℝ) σ b)‖) (fun n v _ => X n (v : ℝ)) := by
      rw [st6_prec_det_iff sz hsz]
      intro τ' hτ'
      filter_upwards [h τ' hτ'] with n hn v
      exact hn v v.2.1 v.2.2 σ
    have hk := stek_sumNdecay_holds d hd 2 le_rfl 𝔠 𝔡 sz hflow.1 s u hs0 hsu hu1
      (fun n => mE (STflowE z n)) (fun n => norm_mE (st6_flowE_lt_two sz hκ hflow n).le) σ
      (fun n v _ => fun b => STExpDrift sz n (STflowE z n) (v : ℝ) σ b)
      (fun n v _ => X n (v : ℝ)) (fun n v _ => hX n v v.2.1 v.2.2) hdom
    rw [st6_prec_det_iff sz hsz] at hk
    exact hk τ hτ
  have hall := Filter.eventually_all.2 key
  filter_upwards [hall] with n hn v h1 h2 σ
  exact hn σ ⟨v, h1, h2⟩

end RBM.Gauss.Sizes

/-! ## 3. The drift bounds as pointwise eventual bounds, and the lift over `u` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- The drift premise of the window `1-u ≥ ilambda²/L^d`, regime (iii), as an eventual pointwise bound of `‖D_v^σ‖_∞`
(deterministic: `st6_prec_det_iff`, the triangle inequality `D = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}`, `pi_norm_le_iff_of_nonneg`). -/
private theorem expIntEasy_drift_pi_hi {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ}
    (ht1 : ∀ n, t n < 1) (hDr : STExpDriftHiConcl sz E s t) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpDrift sz n (E n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
  have h1 := (st6_prec_det_iff sz hsz _ _).1 hDr.1 τ hτ
  have h2 := (st6_prec_det_iff sz hsz _ _).1 hDr.2 τ hτ
  filter_upwards [h1, h2] with n hn1 hn2 v hsv hvt σ
  have hv1 : v < 1 := lt_of_le_of_lt hvt (ht1 n)
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hB : 0 < sz.Bctl n v := STBctl_pos sz n hv1
  have hxinv : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
  have hX : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) :=
    mul_nonneg hN (mul_nonneg hxinv (add_nonneg (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hB.le _)))
  rw [pi_norm_le_iff_of_nonneg hX]
  intro a
  have e1 := hn1 (⟨⟨v, hsv, hvt⟩, σ, a⟩ : STIdx2 sz s t n)
  have e2 := hn2 (⟨⟨v, hsv, hvt⟩, σ, a⟩ : STIdx2 sz s t n)
  change ‖STExpELKLK sz n (E n) v σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * sz.Bctl n v ^ (11 / 5 : ℝ)) at e1
  change ‖STExpEGt sz n (E n) v σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * sz.Bctl n v ^ (5 / 2 : ℝ)) at e2
  calc ‖STExpDrift sz n (E n) v σ a‖ = ‖STExpELKLK sz n (E n) v σ a + STExpEGt sz n (E n) v σ a‖ := rfl
    _ ≤ ‖STExpELKLK sz n (E n) v σ a‖ + ‖STExpEGt sz n (E n) v σ a‖ := norm_add_le _ _
    _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

/-- The drift premise of regime (iv) as an eventual pointwise bound of `‖D_v^σ‖_∞`. -/
private theorem expIntEasy_drift_pi_lo {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ}
    (ht1 : ∀ n, t n < 1) (hDr : STExpDriftLoConcl sz E s t) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpDrift sz n (E n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3) := by
  have h1 := (st6_prec_det_iff sz hsz _ _).1 hDr τ hτ
  filter_upwards [h1] with n hn v hsv hvt σ
  have hv1 : v < 1 := lt_of_le_of_lt hvt (ht1 n)
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hX : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      ((1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3) := by
    have : 0 < 1 - v := by linarith
    positivity
  rw [pi_norm_le_iff_of_nonneg hX]
  intro a
  exact hn (⟨⟨v, hsv, hvt⟩, σ, a⟩ : STIdx2 sz s t n)

/-- **The lift over `u`** (§64 (4), one lift per regime): given the eventual pointwise drift bound `‖D_v^σ‖_∞ ≤ N^τ X_v`
(`v ∈ [s_n,t_n]`), the one-size integral estimate (with the kernel factor `((1-v)/(1-u))²`) and the rate `R_u ≤ c T_u`
(eventually in `n`, every `u ∈ [s_n,t_n]`), the deterministic family `‖∫_{s_n}^u 𝒰_{v,u} D_v^σ dv‖_a` is `≺ T_u` uniformly in
`(u,σ,a)`: per time sequence `u` the kernel bound (`expIntEasy_kernel_seq`, at `τ/2`), then `st6_precU_of_forall_seq`
(both sides deterministic). -/
private theorem expIntEasy_lift_core {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (X R : ℕ → ℝ → ℝ) (c : ℝ)
    (hX : ∀ n v, s n ≤ v → v ≤ t n → 0 ≤ X n v)
    (hdrift : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpDrift sz n (STflowE z n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v)
    (hint : ∀ n (u M : ℝ) (F : ℝ → ℂ), 0 ≤ M → s n ≤ u → u ≤ t n →
      (∀ v : ℝ, s n ≤ v → v ≤ u → ‖F v‖ ≤ M * (((1 - v) / (1 - u)) ^ 2 * X n v)) →
        ‖∫ v in (s n)..u, F v‖ ≤ M * R n u)
    (hrate : ∀ᶠ n in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n → R n u ≤ c * STExpTarget sz n u) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 v (p.1 : ℝ)
          (fun b => STExpDrift sz n (STflowE z n) v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  refine st6_precU_of_forall_seq sz hsz (fun n => (hst n).le)
    (W := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖∫ v in (s n)..u, RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) w.1 v u
      (fun b => STExpDrift sz n (STflowE z n) v w.1 b) w.2‖)
    (fun n u _ => STExpTarget sz n u) ?_
  intro u hsu hut
  rw [st6_prec_det_iff sz hsz]
  intro τ hτ
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hk := expIntEasy_kernel_seq sz hd hκ hflow hs0 hsu hu1 X
    (fun n v h1 h2 => hX n v h1 (h2.trans (hut n)))
    (fun τ' hτ' => (hdrift τ' hτ').mono fun n hn v h1 h2 σ => hn v h1 (h2.trans (hut n)) σ)
    (τ / 2) (half_pos hτ)
  filter_upwards [hk, hrate, (tendsto_size sz hsz).eventually (eventually_le_rpow c (half_pos hτ))] with n hkn hrn hc
  rintro ⟨σ, a⟩
  have hM : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 := hint n (u n) (((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (fun v => RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u n)
      (fun b => STExpDrift sz n (STflowE z n) v σ b) a) hM (hsu n) (hut n)
    (fun v h1 h2 => (norm_le_pi_norm _ a).trans (hkn v h1 h2 σ))
  have hT := st6_target_nonneg sz n (hu1 n)
  change ‖∫ v in (s n)..(u n), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u n)
      (fun b => STExpDrift sz n (STflowE z n) v σ b) a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (u n)
  calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * R n (u n) := h1
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (c * STExpTarget sz n (u n)) :=
        mul_le_mul_of_nonneg_left (hrn (u n) (hsu n) (hut n)) hM
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * STExpTarget sz n (u n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hT) hM
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (u n) := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]

end RBM.Gauss.Sizes

/-! ## 4. The drift integrals, the assembly and the pins -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- Regime (iii): the drift integral `∫_s^u 𝒰_{v,u}D_v dv ≺ T_u`, uniformly in `(u,σ,a)`: per time sequence `u` the kernel bound
(`expIntEasy_kernel_seq` with `X_v = (1-v)⁻¹(B_v^{11/5} + B_v^{5/2})` from `STExpDriftHiConcl`), `expIntIII_drift_integral_le`
with `M = N^{τ/2}`, `expIntIII_rates_le_target` (`ilambda_n ≠ 0` eventually: `st6_lam_pos`), `64 ≤ N^{τ/2}`; then one lift
over `u` (`st6_precU_of_forall_seq`, deterministic both sides). -/
theorem expIntIII_int_unif {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5III sz s t) (hDr : STExpDriftHiConcl sz (STflowE z) s t) :
    Prec sz (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 v (p.1 : ℝ)
          (fun b => STExpDrift sz n (STflowE z n) v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  refine expIntEasy_lift_core sz hd hκ hflow hs0 hst htT
    (fun n v => (1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))
    (fun n u => 5 * (2 * sz.Bctl n u) ^ (11 / 5 : ℝ) + 2 * (2 * sz.Bctl n u) ^ (5 / 2 : ℝ)) 64
    ?_ (expIntEasy_drift_pi_hi sz hsz ht1 hDr) ?_ ?_
  · intro n v h1 h2
    have hv1 : v < 1 := lt_of_le_of_lt h2 (ht1 n)
    have hB : 0 < sz.Bctl n v := STBctl_pos sz n hv1
    exact mul_nonneg (inv_nonneg.2 (by linarith))
      (add_nonneg (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hB.le _))
  · intro n u M F hM hsu hut hF
    exact expIntIII_drift_integral_le sz n F hM hsu (lt_of_le_of_lt hut (ht1 n))
      ((hR n).trans (by linarith)) hF
  · filter_upwards [st6_lam_pos sz hflow.1.2.2.2.2] with n hn u hsu hut
    exact expIntIII_rates_le_target sz n (lt_of_le_of_lt hut (ht1 n)) hn.ne'
      ((hR n).trans (by linarith))

/-- Regime (iv): the same with `X_v = (1-v)⁻¹(N(1-v))^{-3}` from `STExpDriftLoConcl`, `expIntIV_drift_integral_le`,
`expIntIV_rate_le_target` (no regime hypothesis, no `ilambda ≠ 0`); one lift over `u`. -/
theorem expIntIV_int_unif {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hDr : STExpDriftLoConcl sz (STflowE z) s t) :
    Prec sz (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 v (p.1 : ℝ)
          (fun b => STExpDrift sz n (STflowE z n) v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  refine expIntEasy_lift_core sz hd hκ hflow hs0 hst htT
    (fun n v => (1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3)
    (fun n u => ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3) 1
    ?_ (expIntEasy_drift_pi_lo sz hsz ht1 hDr) ?_ ?_
  · intro n v h1 h2
    have hv1 : 0 < 1 - v := by linarith [ht1 n]
    have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    positivity
  · intro n u M F hM hsu hut hF
    exact expIntIV_drift_integral_le sz n F hM hsu (lt_of_le_of_lt hut (ht1 n)) hF
  · exact Filter.Eventually.of_forall fun n u hsu hut => by
      rw [one_mul]
      exact expIntIV_rate_le_target sz n (lt_of_le_of_lt hut (ht1 n))

/-- `(Eexpint_K-L)` (`6:3-7`) closed, `A = ∅`, all `σ`: the Duhamel identity (`STExpDuhEq` at `A = ∅`, `st5_zeroModeSet_empty`),
the initial-term control `F` and the drift-integral bound give `STExpIntConcl ∅ STSigAll` (`‖f_u‖ ≤ N^τ F + N^τ T_u`). -/
theorem STExpIntConcl_of_int {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (_ht1 : ∀ n, t n < 1)
    (hduh : STExpDuhEq sz E s t)
    (hint : Prec sz (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1 v (p.1 : ℝ)
          (fun b => STExpDrift sz n (E n) v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))) :
    STExpIntConcl sz ∅ STSigAll E s t := by
  intro F hF0 hini
  rw [st6_prec_det_iff sz hsz] at hini ⊢
  intro τ hτ
  have hint' := (st6_prec_det_iff sz hsz _ _).1 hint τ hτ
  filter_upwards [hini τ hτ, hint'] with n h1 h2 p
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp := h2 ((p.1, p.2.1.1, p.2.2) : STIdx2 sz s t n)
  have hi := h1 p
  have hd := hduh n p.1 p.2.1.1 ∅ p.2.2
  simp only [st5_zeroModeSet_empty] at hd hi ⊢
  rw [hd]
  calc ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b) p.2.2 +
      ∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 v (p.1 : ℝ)
        (fun b => STExpDrift sz n (E n) v p.2.1.1 b) p.2.2‖
      ≤ ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b) p.2.2‖ +
        ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 v (p.1 : ℝ)
        (fun b => STExpDrift sz n (E n) v p.2.1.1 b) p.2.2‖ := norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * F n p + ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (p.1 : ℝ) :=
        add_le_add hi hp
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (F n p + STExpTarget sz n (p.1 : ℝ)) := by ring

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- Regime (iii): the conclusion of the pin from the flow data (no stochastic premise of `STIngR6` is used). -/
theorem STExpIntIIIConcl_of_flow {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5III sz s t) (hduh : STExpDuhEq sz (STflowE z) s t)
    (hDr : STExpDriftHiConcl sz (STflowE z) s t) : STExpIntConcl sz ∅ STSigAll (STflowE z) s t :=
  STExpIntConcl_of_int sz hflow.1.2.2.1 (st5_t_lt_one sz hflow htT) hduh
    (expIntIII_int_unif sz hd hκ hflow hs0 hst htT hR hDr)

/-- Regime (iv): the same, without the regime (the drift premise carries it). -/
theorem STExpIntIVConcl_of_flow {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hduh : STExpDuhEq sz (STflowE z) s t)
    (hDr : STExpDriftLoConcl sz (STflowE z) s t) : STExpIntConcl sz ∅ STSigAll (STflowE z) s t :=
  STExpIntConcl_of_int sz hflow.1.2.2.1 (st5_t_lt_one sz hflow htT) hduh
    (expIntIV_int_unif sz hd hκ hflow hs0 hst htT hDr)

/-- **The pin `STExpIntIII`** (`Step6Pins.lean:425`, regime (iii), `6:94-96`), every `d`: `𝔠_d = 1/100`; the stochastic premises of
`STIngR6` are not used. -/
theorem stExpIntIII_holds (d : ℕ) : STExpIntIII d := by
  intro hd κ ε 𝔡 hκ _ _
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR _ _ _ _ _ _ _ _ hduh hDr
  exact STExpIntIIIConcl_of_flow sz hd hκ hflow hs0 hst htT hR hduh hDr

/-- **The pin `STExpIntIV`** (`Step6Pins.lean:432`, regime (iv), `6:94-96`), every `d`: `𝔠_d = 1/100`; the stochastic premises of
`STIngR6` and the regime hypothesis are not used. -/
theorem stExpIntIV_holds (d : ℕ) : STExpIntIV d := by
  intro hd κ ε 𝔡 hκ _ _
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT _ _ _ _ _ _ _ _ _ hduh hDr
  exact STExpIntIVConcl_of_flow sz hd hκ hflow hs0 hst htT hduh hDr

/-- **The regime pin `STStep6IV`** (`Step6Pins.lean:140`, `6:94-96`), every `d`: the merged skeleton `ST_step6_caseIV_of_pins` with
`stImproveExpAver_holds`, `stExpDuhamelZ_holds`, `stExpDriftLo_holds` (merged) and `stExpIntIV_holds` (above). -/
theorem stStep6IV_holds (d : ℕ) : STStep6IV d :=
  ST_step6_caseIV_of_pins (stImproveExpAver_holds d) (stExpDuhamelZ_holds d) (stExpDriftLo_holds d) (stExpIntIV_holds d)

end RBM.Gauss.Sizes

/-! ## 5. Compiled nonempty instances (`d = 3`; regime (iii) `(sz0, z0, 0, 1/16)`, regime (iv) `(szG, zB, 5/8, 3/4)`) -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- `stExpIntIII_holds 3` at the data of regime (iii) (`sz0`, `z0`, `[0, 1/16]`). -/
theorem inst_expIntIII_holds :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) sz0 z0 sInst tInst :=
  inst_expIntIII (stExpIntIII_holds 3)

/-- `stExpIntIV_holds 3` at the data of regime (iv) (`szG`, `zB`, `[5/8, 3/4]`). -/
theorem inst_expIntIV_holds :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_expIntIV (stExpIntIV_holds 3)

/-- The regime-(iii) skeleton with `hLK`, `hDu`, `hInt` merged or proved here: open is only `LWtermEXP 3` (LW-14). -/
theorem inst_skeleton6III_Int :
    LWtermEXP 3 → InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  fun hLW => inst_skeleton6III_LK hLW (stExpDuhamelZ_holds 3) (stExpIntIII_holds 3)

/-- The regime-(iv) skeleton: **no pin open** (`stStep6IV_holds 3`). -/
theorem inst_skeleton6IV_Int :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_step6IV (stStep6IV_holds 3)

/-- `STExpIntIIIConcl_of_flow` at `sz0`, `z0`, `κ = 1/10` (`flow_z0`), `[0, 1/16]` (`sz0_hs0`, `sz0_hst`, `sz0_ht`, `sz0_reg5III`), the
Duhamel identity from `inst_duhEq_holds`; the drift bounds stay a hypothesis (other gates' pins). -/
theorem inst_expIntIII_concl :
    STExpDriftHiConcl sz0 (STflowE z0) sInst tInst → STExpIntConcl sz0 ∅ STSigAll (STflowE z0) sInst tInst :=
  fun hDr => STExpIntIIIConcl_of_flow sz0 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 sz0_hs0 sz0_hst
    sz0_ht sz0_reg5III inst_duhEq_holds hDr

/-- `STExpIntIVConcl_of_flow` at `szG`, `zB` (`flow_zG`), `[5/8, 3/4]` (`szB_flow_ht`), Duhamel from `st6_duhEq_of_pin`; the drift bound
stays a hypothesis. -/
theorem inst_expIntIV_concl :
    STExpDriftLoConcl szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4) →
      STExpIntConcl szG ∅ STSigAll (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  fun hDr => STExpIntIVConcl_of_flow szG (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zG
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num))
    (st6_duhEq_of_pin szG (stExpDuhamelZ_holds 3) le_rfl (by norm_num : (0 : ℝ) < 1 / 10) flow_zG
      (fun _ => by norm_num) (szB_flow_ht (by norm_num))) hDr

/-- `expIntEasy_integral_rpow` at `r = 6/5`, `(s,u) = (0, 1/16)`: `0.0650 ≤ 5 (15/16)^{-1/5} = 5.065`. -/
theorem inst_expIntEasy_integral_rpow :
    ∫ v in (0 : ℝ)..(1 / 16), (1 - v) ^ (-(6 / 5 : ℝ)) ≤ (6 / 5 - 1 : ℝ)⁻¹ * (1 - 1 / 16 : ℝ) ^ (1 - 6 / 5 : ℝ) :=
  expIntEasy_integral_rpow (by norm_num) (by norm_num) (by norm_num)

/-- `expIntIII_rates_le_target` at `sz0`, `n = 0` (`L = 4`, `W = 32`, `ilambda = 1/64`), `u = 1/16`:
`B = 3.305e-5`, `3.26e-9 ≤ 64 · 7.21e-10 = 4.61e-8`. -/
theorem inst_expIntIII_rates_le_target :
    5 * (2 * sz0.Bctl 0 (1 / 16)) ^ (11 / 5 : ℝ) + 2 * (2 * sz0.Bctl 0 (1 / 16)) ^ (5 / 2 : ℝ) ≤
      64 * STExpTarget sz0 0 (1 / 16) := by
  have h : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
  exact expIntIII_rates_le_target sz0 0 (by norm_num) (by rw [h]; norm_num) (by rw [h]; norm_num)

/-- `expIntIV_rate_le_target` at `szG`, `n = 0` (`N = 4096`), `u = 3/4`: `9.31e-10 ≤ 5.86e-7`. -/
theorem inst_expIntIV_rate_le_target :
    ((((szG.size 0 : ℕ) : ℝ) * (1 - 3 / 4))⁻¹) ^ 3 ≤ STExpTarget szG 0 (3 / 4) :=
  expIntIV_rate_le_target szG 0 (by norm_num)

/-- `expIntIII_drift_integral_le` at `sz0`, `n = 0`, `[0, 1/16]`, `M = 1`, `F v = ` the drift bound itself (a nonzero real function):
`(1/64)² ≤ 15/16 = 1 - u`. -/
example :
    ‖∫ v in (0 : ℝ)..(1 / 16),
        ((((1 - v) / (1 - 1 / 16)) ^ 2 * ((1 - v)⁻¹ * (sz0.Bctl 0 v ^ (11 / 5 : ℝ) + sz0.Bctl 0 v ^ (5 / 2 : ℝ))) : ℝ) : ℂ)‖ ≤
      1 * (5 * (2 * sz0.Bctl 0 (1 / 16)) ^ (11 / 5 : ℝ) + 2 * (2 * sz0.Bctl 0 (1 / 16)) ^ (5 / 2 : ℝ)) := by
  have h : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
  refine expIntIII_drift_integral_le sz0 0 (s := 0) (u := 1 / 16) (M := 1) _ zero_le_one (by norm_num) (by norm_num)
    (by rw [h]; norm_num) ?_
  intro v h1 h2
  have hv : v < 1 := by linarith
  have hB := (STBctl_pos sz0 0 hv).le
  have hx : 0 < 1 - v := by linarith
  rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
  exact le_of_eq (abs_of_nonneg (by positivity))

/-- `expIntIV_drift_integral_le` at `szG`, `n = 0`, `[5/8, 3/4]`, `M = 1`, `F v = ` the drift bound itself. -/
example :
    ‖∫ v in (5 / 8 : ℝ)..(3 / 4),
        ((((1 - v) / (1 - 3 / 4)) ^ 2 * ((1 - v)⁻¹ * ((((szG.size 0 : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3) : ℝ) : ℂ)‖ ≤
      1 * ((((szG.size 0 : ℕ) : ℝ) * (1 - 3 / 4))⁻¹) ^ 3 := by
  refine expIntIV_drift_integral_le szG 0 (s := 5 / 8) (u := 3 / 4) (M := 1) _ zero_le_one (by norm_num) (by norm_num) ?_
  intro v h1 h2
  have hx : 0 < 1 - v := by linarith
  have hN : (0 : ℝ) < ((szG.size 0 : ℕ) : ℝ) := by exact_mod_cast szG.one_le_size 0
  rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
  exact le_of_eq (abs_of_nonneg (by positivity))

/-- `expIntEasy_kernel_seq` at `sz0`, `z0`, `(s, u) = (0, 1/16)` (a constant time sequence): the eventual drift bound stays a hypothesis. -/
example := expIntEasy_kernel_seq sz0 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 (s := sInst)
  (u := fun _ => (1 / 16 : ℝ)) sz0_hs0 (fun n => by simp only [sInst]; norm_num) (fun n => by norm_num)

/-- `expIntIII_int_unif` at `(sz0, z0, 0, 1/16)`: the drift bounds stay a hypothesis. -/
example := expIntIII_int_unif sz0 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 sz0_hs0 sz0_hst sz0_ht
  sz0_reg5III

/-- `expIntIV_int_unif` at `(szG, zB, 5/8, 3/4)`: the drift bound stays a hypothesis. -/
example := expIntIV_int_unif szG (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zG
  (s := fun _ => (5 / 8 : ℝ)) (t := fun _ => (3 / 4 : ℝ)) (fun _ => by norm_num)
  (fun _ => by norm_num) (szB_flow_ht (by norm_num))

/-- `STExpIntConcl_of_int` at `(sz0, z0, 0, 1/16)`: the drift-integral bound stays a hypothesis; Duhamel from `inst_duhEq_holds`. -/
example := STExpIntConcl_of_int sz0 sz0_tendsto (E := STflowE z0) (s := sInst) (t := tInst)
  (fun n => by simp only [tInst]; norm_num) inst_duhEq_holds

end RBM.Gauss.Step6Inst

#print axioms RBM.Gauss.Sizes.expIntEasy_integral_rpow
#print axioms RBM.Gauss.Sizes.expIntIII_rates_le_target
#print axioms RBM.Gauss.Sizes.expIntIV_rate_le_target
#print axioms RBM.Gauss.Sizes.expIntIII_drift_integral_le
#print axioms RBM.Gauss.Sizes.expIntIV_drift_integral_le
#print axioms RBM.Gauss.Sizes.expIntEasy_kernel_seq
#print axioms RBM.Gauss.Sizes.expIntIII_int_unif
#print axioms RBM.Gauss.Sizes.expIntIV_int_unif
#print axioms RBM.Gauss.Sizes.STExpIntConcl_of_int
#print axioms RBM.Gauss.Sizes.STExpIntIIIConcl_of_flow
#print axioms RBM.Gauss.Sizes.STExpIntIVConcl_of_flow
#print axioms RBM.Gauss.Sizes.stExpIntIII_holds
#print axioms RBM.Gauss.Sizes.stExpIntIV_holds
#print axioms RBM.Gauss.Sizes.stStep6IV_holds
#print axioms RBM.Gauss.Step6Inst.inst_expIntIII_holds
#print axioms RBM.Gauss.Step6Inst.inst_expIntIV_holds
#print axioms RBM.Gauss.Step6Inst.inst_skeleton6III_Int
#print axioms RBM.Gauss.Step6Inst.inst_skeleton6IV_Int
#print axioms RBM.Gauss.Step6Inst.inst_expIntIII_concl
#print axioms RBM.Gauss.Step6Inst.inst_expIntIV_concl
#print axioms RBM.Gauss.Step6Inst.inst_expIntEasy_integral_rpow
#print axioms RBM.Gauss.Step6Inst.inst_expIntIII_rates_le_target
#print axioms RBM.Gauss.Step6Inst.inst_expIntIV_rate_le_target
