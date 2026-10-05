/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.LemDecCalEdif2
import RBM3D.Path.LemDecCalEwG
import RBM3D.Green.GbEXP
import RBM3D.Path.NetLift2
import RBM3D.Path.KellStar
import RBM3D.Induction.Step5Kit
import RBM3D.Induction.LemDecCalELip

/-!
# `lem_dec_calE` in the `Prec` form (S5-09, ticket T2193 with Amend 1)

`stLemDecCalE_holds (d : ℕ) : STLemDecCalE d`: the three bounds `(res_deccalE_lk)`,
`(res_deccalE_wG)`, `(res_deccalE_dif)` of `lem_dec_calE`
(`paper/tex/3_5_Loop_Hierarchy.tex:2317-2338`; the paper omits the proof,
"a special case of [YY_25, Lemma 5.7]", `3_5:2338`), uniformly in
`u ∈ [s,t]` (the union over `u` inside `P`), for the pin `STLemDecCalE`
(`Induction/Step5Pins.lean`) after DECISIONS §61, §63.  No RBM2D counterpart for the `Prec` layer
(RBM2D stops at the deterministic `lemDecCalE_*`).

**Route (d)** (DECISIONS §64, `docs/tickets/T2193-amend-1.md`): no statement of `(P-e7/8)` uniform
in `u` is made.
* (P) per time: on the good event `lemDecCalEPrec_good` (the hypothesis `STLK2 ≤ N^{τ'} Jst T`,
  `STLocalEntryU`, `GijGEXPTSwap` per time, `STAvgU`, `STLmaxU` at `k = 3, 4, 6`;
  `lemDecCalEPrec_prob`) the realized control `J♯ = LemDecCalELip_Jsharp` satisfies
  `1 ≤ J♯ ≤ N^{τ'} Jst ≤ W`, `E2HypDif` and `E2HypWG` hold at `M = H_u` (`lemDecCalEPrec_det`) and
  `lemDecCalE_lk/_wG/_dif` give `‖ℰ_i‖ ≤ N^τ (R₀ᵢ + J♯^{m_i} Rᵢ)` (`lemDecCalEPrec_goodDet`),
  `m = 2, 3/2, 3`; hence `PrecPT` (`lemDecCalEPrec_precPT`).
* (N) net: `lemDecCalEPrec_lift` (from T2198's `LemDecCalELip_lift`, `_ELKLK`, `_EGt`, `_ee`,
  `_Jsharp_rel`, `_relcont`) turns `PrecPT(ξ ≺ R₀ + J♯^m R)` into `Prec`; the fourth conclusion is
  re-indexed by `StochDomAt.precomp_param`.
* (C) combine: `lemDecCalEPrec_combine` replaces `J♯` by `Jst` on the event of the hypothesis
  (`J♯(u) ≤ N^{τ'} Jst(u)` for every `u` at once, `τ' = τ/(m+1)`).

Sections: 1 real analysis (`lemDecCalEPrec_RA`); 2 the loss `≤ N^{τ/2}`; 3 bridges to the
conjuncts of `E2Hyp` (`B_{u,0} ≤ 2 (1-u)⁻¹`, `avgErr`, `𝒦^{(1)}`, `𝒦^{(2)}`, `(Kell*)`);
4 `GijGEXPTSwap` from `(Gt_bound_flow)`; 5-7 the good event, its probability and the per-time
bounds; 8 (N); 9 (C); 10 floors and relative continuity of the factors; 11 the endpoint theorem;
12 compiled instances.

Copies of private helpers (all inside RBM3D; no port from RBM1D/RBM2D): `kellStar_bparam_le`
(`Path/KellStar.lean:68`) as `lemDecCalEPrec_bparam_le`; `lemDecCalEwG_STavgM_eq_avgErr`
(`Path/LemDecCalEwG.lean:839`) as `lemDecCalEPrec_avgErr_eq`; `lemDecCalE_STKloop_two`
(`Path/LemDecCalE.lean:1276`) as `lemDecCalEPrec_STKloop_two_eq`; the floor `T ≥ W^{-D}` of the
proof of `LemDecCalELip_Jsharp_rel` (`Induction/LemDecCalELip.lean:1081-1086`) as
`lemDecCalEPrec_tail_ge`.

Differences from the paper (paper-delta candidates in the report): the floor
`(L^d W^{6d})² ≤ W^D` replaces `W^D ≥ N` (`3_5:2317`) and the premise `J*_{u,D} ≤ W^{1/2}` is added
(T2193a, T2193b); `(GijGEX)` is used per time in its one-orientation form and the conclusions are
lifted in `u` (T2193c′).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Gauss.Sizes

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Green
  RBM.Ind.ContinuityNet
open scoped NNReal ENNReal


/-! ## 1. Real analysis -/

/-- `A (1 + 6x)^k e^{8 x^{3/4}} ≤ e^{c x}` for large `x` (`c > 0`): the polynomial and the `exp(O(x^{3/4}))`
factors of the loss are `N^{o(1)}` with `x = log N`. -/
theorem lemDecCalEPrec_RA {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      A * (1 + 6 * x) ^ k * Real.exp (8 * x ^ ((3 : ℝ) / 4)) ≤ Real.exp (c * x) := by
  set c' : ℝ := c / 4 with hc'
  have hc'0 : 0 < c' := by positivity
  set A' : ℝ := A * 7 ^ k * (1 / c') ^ k * (k.factorial : ℝ) with hA'
  have hA'0 : 0 ≤ A' := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((8 / c') ^ 4),
    eventually_ge_atTop (A' / c')] with x hx1 hx2 hx3
  have hx0 : 0 < x := by linarith
  -- `y = x^{1/4}`
  set y : ℝ := x ^ ((1 : ℝ) / 4) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hy4 : y ^ 4 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hy3 : x ^ ((3 : ℝ) / 4) = y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hy8 : 8 / c' ≤ y := by
    by_contra hlt
    have hlt := not_le.1 hlt
    have : y ^ 4 < (8 / c') ^ 4 := pow_lt_pow_left₀ hlt hy0.le (by norm_num)
    linarith
  -- (a) `8 x^{3/4} ≤ c' x`
  have ha : 8 * x ^ ((3 : ℝ) / 4) ≤ c' * x := by
    rw [hy3, ← hy4]
    have h1 : 8 ≤ c' * y := by
      have := (div_le_iff₀ hc'0).1 hy8
      linarith
    have h3 : 0 < y ^ 3 := pow_pos hy0 3
    nlinarith
  -- (b), (c): `A (1 + 6x)^k ≤ A' e^{c' x}`
  have hb : (1 + 6 * x) ^ k ≤ (7 * x) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
  have hc2 := Real.pow_div_factorial_le_exp (c' * x) (by positivity) k
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hxk : x ^ k ≤ (1 / c') ^ k * (k.factorial : ℝ) * Real.exp (c' * x) := by
    have h1 : (c' * x) ^ k ≤ (k.factorial : ℝ) * Real.exp (c' * x) := by
      have := (div_le_iff₀ hfac).1 hc2
      linarith
    have h2 : x ^ k = (1 / c') ^ k * (c' * x) ^ k := by
      rw [← mul_pow]; field_simp
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hAx : A * (1 + 6 * x) ^ k ≤ A' * Real.exp (c' * x) := by
    calc A * (1 + 6 * x) ^ k ≤ A * (7 * x) ^ k := mul_le_mul_of_nonneg_left hb hA
      _ = A * 7 ^ k * x ^ k := by rw [mul_pow]; ring
      _ ≤ A * 7 ^ k * ((1 / c') ^ k * (k.factorial : ℝ) * Real.exp (c' * x)) :=
          mul_le_mul_of_nonneg_left hxk (by positivity)
      _ = A' * Real.exp (c' * x) := by rw [hA']; ring
  -- (d) `A' ≤ e^{c' x}`
  have hd : A' ≤ Real.exp (c' * x) := by
    have h1 : A' ≤ c' * x := by
      have := (div_le_iff₀ hc'0).1 hx3
      linarith
    have := Real.add_one_le_exp (c' * x)
    linarith
  have hE0 : 0 < Real.exp (c' * x) := Real.exp_pos _
  calc A * (1 + 6 * x) ^ k * Real.exp (8 * x ^ ((3 : ℝ) / 4))
      ≤ (A' * Real.exp (c' * x)) * Real.exp (c' * x) :=
        mul_le_mul hAx (Real.exp_le_exp.2 ha) (Real.exp_pos _).le (by positivity)
    _ ≤ (Real.exp (c' * x) * Real.exp (c' * x)) * Real.exp (c' * x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hE0.le) hE0.le
    _ = Real.exp ((3 * c') * x) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (c * x) := by
        refine Real.exp_le_exp.2 ?_
        rw [hc']; nlinarith


/-! ## 2. The loss is at most `N^{τ/2}` -/

section Loss

variable {d : ℕ}

/-- The numerical facts about `W, L, N = (W L)^d` used for the loss (`d ≥ 1`). -/
private theorem lemDecCalEPrec_sizes (sz : Sizes d) (n : ℕ) (hd : 1 ≤ d) :
    1 ≤ ((sz.W n : ℕ) : ℝ) ∧ 1 ≤ ((sz.L n : ℕ) : ℝ) ∧
      ((sz.size n : ℕ) : ℝ) = (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d ∧
      ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) := by
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hN : ((sz.size n : ℕ) : ℝ) = (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d := by
    simp [Sizes.size]
  have hWL : 1 ≤ ((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ) := by nlinarith
  refine ⟨hW, hL, hN, ?_, ?_⟩
  · rw [hN]
    calc ((sz.W n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ) := by nlinarith
      _ ≤ (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d := le_self_pow₀ hWL (by omega)
  · rw [hN]; exact one_le_pow₀ hWL

/-- `1 ≤ L^d W^{6d} ≤ N^6` and `L^d W^{2d} ≤ L^d W^{6d}` (`N = (W L)^d`). -/
private theorem lemDecCalEPrec_P (sz : Sizes d) (n : ℕ) (hd : 1 ≤ d) :
    1 ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) ∧
    ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤
      ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) ∧
    ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) ≤ ((sz.size n : ℕ) : ℝ) ^ 6 ∧
    ((sz.size n : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) := by
  obtain ⟨hW, hL, hN, -, -⟩ := lemDecCalEPrec_sizes sz n hd
  have hLd : 1 ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL
  have hW2 : ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤ ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    pow_le_pow_right₀ hW (by omega)
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    pow_le_pow_right₀ hW (by omega)
  have hW6 : 1 ≤ ((sz.W n : ℕ) : ℝ) ^ (6 * d) := one_le_pow₀ hW
  refine ⟨by nlinarith, mul_le_mul_of_nonneg_left hW2 (by linarith), ?_, ?_⟩
  · rw [hN, ← pow_mul, mul_pow]
    have hL6 : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.L n : ℕ) : ℝ) ^ (d * 6) :=
      pow_le_pow_right₀ hL (by omega)
    have : (6 * d) = d * 6 := by ring
    rw [this]
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ)) (d * 6)]
  · rw [hN, mul_pow]
    nlinarith

/-- **The loss of `lemDecCalE_wG`** at `Λ = 32 Q`, `K₀ = 1`: at most `A_d Q⁶ (1 + 6 log N)^{7+2d}
e^{8 (log N)^{3/4}}`; the loss of `_lk` and of `_dif` is at most this (`lossE2 ≤ lossE2dif ≤ lossE2wG`). -/
theorem lemDecCalEPrec_lossWG_le (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) :
    lossE2wG d (sz.L n) (sz.W n) (32 * Q) 1 ≤
      (10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * 32 ^ 6 * 1000 ^ d) * Q ^ 6 *
        (1 + 6 * Real.log ((sz.size n : ℕ) : ℝ)) ^ (7 + 2 * d) *
        Real.exp (8 * Real.log ((sz.size n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := by
  obtain ⟨hW, hL, hN, hWN, hN1⟩ := lemDecCalEPrec_sizes sz n hd
  obtain ⟨hP1, hP2, hP6, -⟩ := lemDecCalEPrec_P sz n hd
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set L : ℝ := ((sz.L n : ℕ) : ℝ) with hLdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set x : ℝ := Real.log N with hx
  have hN0 : 0 < N := by linarith
  have hx0 : 0 ≤ x := Real.log_nonneg hN1
  have hW0 : 0 < W := by linarith
  have hlogP : Real.log (L ^ d * W ^ (6 * d)) ≤ 6 * x := by
    have h1 := Real.log_le_log (by linarith) hP6
    rwa [Real.log_pow, show ((6 : ℕ) : ℝ) = 6 by norm_num] at h1
  have hlogP0 : 0 ≤ Real.log (L ^ d * W ^ (6 * d)) := Real.log_nonneg hP1
  have hlogP2 : Real.log (L ^ d * W ^ (2 * d)) ≤ 6 * x := by
    refine le_trans (Real.log_le_log (by positivity) hP2) hlogP
  have hlogP20 : 0 ≤ Real.log (L ^ d * W ^ (2 * d)) :=
    Real.log_nonneg (by
      have : 1 ≤ L ^ d := one_le_pow₀ hL
      have : 1 ≤ W ^ (2 * d) := one_le_pow₀ hW
      nlinarith)
  have hlogW : Real.log W ≤ x := Real.log_le_log hW0 hWN
  have hlogW0 : 0 ≤ Real.log W := Real.log_nonneg hW
  set ℓ : ℝ := 1 + 6 * x with hℓ
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hexp : Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) ≤ Real.exp (8 * x ^ ((3 : ℝ) / 4)) := by
    refine Real.exp_le_exp.2 ?_
    have := Real.rpow_le_rpow hlogW0 hlogW (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4)
    linarith
  have ha : 1 + Real.log (L ^ d * W ^ (2 * d)) ≤ ℓ := by linarith
  have hb : 1 + Real.log W ≤ ℓ := by linarith
  have hc : 1 + Real.log (L ^ d * W ^ (6 * d)) ≤ ℓ := by linarith
  have ha0 : 0 ≤ 1 + Real.log (L ^ d * W ^ (2 * d)) := by linarith
  have hb0 : 0 ≤ 1 + Real.log W := by linarith
  have hc0 : 0 ≤ 1 + Real.log (L ^ d * W ^ (6 * d)) := by linarith
  have hE0 : 0 ≤ Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) := (Real.exp_pos _).le
  unfold lossE2wG lossE2
  calc 10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * 1 ^ 2 * (32 * Q) ^ 6 *
        (1 + Real.log (L ^ d * W ^ (2 * d))) ^ 4 * (1 + Real.log W) ^ 3 *
        Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) *
        (1000 ^ d * (1 + Real.log (L ^ d * W ^ (6 * d))) ^ (2 * d))
      ≤ 10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * 1 ^ 2 * (32 * Q) ^ 6 * ℓ ^ 4 * ℓ ^ 3 *
        Real.exp (8 * x ^ ((3 : ℝ) / 4)) * (1000 ^ d * ℓ ^ (2 * d)) := by
        gcongr
    _ = _ := by ring

/-- **The loss is eventually at most `N^{τ/2}`** at `Λ = 32 N^{τ'}`, `K₀ = 1`, `6 τ' ≤ τ/4`
(`(log W)^{3/4} = o(log N)`, polylogarithmic factors). -/
theorem lemDecCalEPrec_lossWG_eventually (sz : Sizes d) (hd : 1 ≤ d) (hsize : sz.SizeTendsto)
    {τ τ' : ℝ} (hτ : 0 < τ) (hτ' : 0 ≤ τ') (h6 : 6 * τ' ≤ τ / 4) :
    ∀ᶠ n in atTop,
      lossE2wG d (sz.L n) (sz.W n) (32 * ((sz.size n : ℕ) : ℝ) ^ τ') 1 ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
  have hlog : Tendsto (fun n => Real.log ((sz.size n : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hsize
  have hRA := lemDecCalEPrec_RA (A := 10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * 32 ^ 6 * 1000 ^ d)
    (c := τ / 4) (by positivity) (by positivity) (7 + 2 * d)
  filter_upwards [hlog.eventually hRA, hsize.eventually_ge_atTop 1] with n h1 hN1
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hQ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'
  refine (lemDecCalEPrec_lossWG_le sz hd n hQ1).trans ?_
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set x : ℝ := Real.log N with hx
  have hQ6 : (N ^ τ') ^ 6 = N ^ (6 * τ') := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hexp : Real.exp (τ / 4 * x) = N ^ (τ / 4) := by
    rw [Real.rpow_def_of_pos hN0, mul_comm]
  have hN6 : N ^ (6 * τ') ≤ N ^ (τ / 4) := Real.rpow_le_rpow_of_exponent_le hN1 h6
  have hsum : N ^ (τ / 4) * N ^ (τ / 4) = N ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  calc (10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * 32 ^ 6 * 1000 ^ d) * (N ^ τ') ^ 6 *
        (1 + 6 * x) ^ (7 + 2 * d) * Real.exp (8 * x ^ ((3 : ℝ) / 4))
      = N ^ (6 * τ') * ((10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * 32 ^ 6 * 1000 ^ d) *
          (1 + 6 * x) ^ (7 + 2 * d) * Real.exp (8 * x ^ ((3 : ℝ) / 4))) := by rw [hQ6]; ring
    _ ≤ N ^ (τ / 4) * Real.exp (τ / 4 * x) :=
        mul_le_mul hN6 h1 (by positivity) (by positivity)
    _ = N ^ (τ / 2) := by rw [hexp, hsum]

/-- `lossE2 ≤ lossE2dif ≤ lossE2wG` (the extra factors `729^d (1 + log P)^{2d}`, `1000^d (1 + log P)^{2d}`
are `≥ 1` and increasing in the constant; `lossE2 ≥ 0`). -/
theorem lemDecCalEPrec_loss_mono (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) (Λ K₀ : ℝ) :
    lossE2 d (sz.L n) (sz.W n) Λ K₀ ≤ lossE2dif d (sz.L n) (sz.W n) Λ K₀ ∧
      lossE2dif d (sz.L n) (sz.W n) Λ K₀ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
  obtain ⟨hW, hL, -, -, -⟩ := lemDecCalEPrec_sizes sz n hd
  obtain ⟨hP1, hP2, -, -⟩ := lemDecCalEPrec_P sz n hd
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set L : ℝ := ((sz.L n : ℕ) : ℝ) with hLdef
  have hlogP0 : 0 ≤ Real.log (L ^ d * W ^ (6 * d)) := Real.log_nonneg hP1
  have hlogP20 : 0 ≤ Real.log (L ^ d * W ^ (2 * d)) :=
    Real.log_nonneg (by
      have : 1 ≤ L ^ d := one_le_pow₀ hL
      have : 1 ≤ W ^ (2 * d) := one_le_pow₀ hW
      nlinarith)
  have hlogW0 : 0 ≤ Real.log W := Real.log_nonneg hW
  have h0 : 0 ≤ lossE2 d (sz.L n) (sz.W n) Λ K₀ := by
    unfold lossE2
    have h1 : 0 ≤ 1 + Real.log (L ^ d * W ^ (2 * d)) := by linarith
    have h2 : 0 ≤ 1 + Real.log W := by linarith
    positivity
  have hc : 1 ≤ (1 + Real.log (L ^ d * W ^ (6 * d))) ^ (2 * d) :=
    one_le_pow₀ (by linarith)
  have h729 : (1 : ℝ) ≤ 729 ^ d := one_le_pow₀ (by norm_num)
  have h729' : (729 : ℝ) ^ d ≤ 1000 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  constructor
  · unfold lossE2dif
    have : (1 : ℝ) ≤ 729 ^ d * (1 + Real.log (L ^ d * W ^ (6 * d))) ^ (2 * d) := by nlinarith
    nlinarith
  · unfold lossE2dif lossE2wG
    refine mul_le_mul_of_nonneg_left ?_ h0
    exact mul_le_mul_of_nonneg_right h729' (by positivity)

end Loss

/-! ## 3. Deterministic bridges to the hypotheses of `E2Hyp` -/

section Bridge

variable {d : ℕ}

/-- `B_{u,K} ≤ 2 (1-u)⁻¹` for `u < 1`, `L ≥ 1` (copy of the private `kellStar_bparam_le`,
`Path/KellStar.lean:68`). -/
private theorem lemDecCalEPrec_bparam_le (d L : ℕ) (hL : 1 ≤ L) (g : ℝ) {u : ℝ} (hu : u < 1)
    (n : ℕ) : Bparam d L g u n ≤ 2 * (1 - u)⁻¹ := by
  have hx : 0 < 1 - u := by linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold Bparam
  rw [abs_of_pos hx]
  have hxi : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr hx.le
  have h1 : (g ^ 2 + (1 - u))⁻¹ * (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ := by
    have a1 : (g ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hx (by nlinarith [sq_nonneg g])
    have a2 : (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc (g ^ 2 + (1 - u))⁻¹ * (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ * 1 :=
          mul_le_mul a1 a2 (by positivity) hxi
      _ = (1 - u)⁻¹ := mul_one _
  have h2 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
    exact inv_anti₀ hx (by nlinarith)
  linarith

/-- `W^{-d} B_{u,K} ≤ 2 (W^d (1-u))⁻¹`: `STWB ≤ 2 M_u⁻¹`. -/
theorem lemDecCalEPrec_STWB_le (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) (K : ℕ) :
    STWB sz n u K ≤ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
  have hL : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have h := lemDecCalEPrec_bparam_le d (sz.L n) hL (sz.lam n) hu K
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (by exact_mod_cast sz.W_pos n) d
  unfold STWB
  rw [mul_inv]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u K
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (1 - u)⁻¹) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hW.le)
    _ = 2 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹) := by ring

/-- `W^{-d} B_{u,0} = STWB … 0 ≤ 2 M_u⁻¹`. -/
theorem lemDecCalEPrec_Bctl_le (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) :
    sz.Bctl n u ≤ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
  lemDecCalEPrec_STWB_le sz n hu 0

/-- `⟨G̃(σ) E_a⟩` is the merged `avgErr` (copy of the private `lemDecCalEwG_STavgM_eq_avgErr`,
`Path/LemDecCalEwG.lean:839`; `tr E_a = 1`). -/
theorem lemDecCalEPrec_avgErr_eq (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Bool)
    (x : Zd d (sz.L n)) :
    avgErr d (sz.L n) (sz.W n) E u M σ x =
      STLM sz n E u M (fun _ : Fin 1 => σ) (fun _ => x) - mSigma E σ := by
  unfold STLM loopFine loopM avgErr greenBlk
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, Matrix.one_mul,
    trace_Eblk]
  simp

/-- `𝒦^{(1)}_{u,σ,a} = m(σ)` for the model's `STKloop` (`KLK_one`). -/
theorem lemDecCalEPrec_STKloop_one (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Bool) (x : Zd d (sz.L n)) :
    STKloop sz n E u (fun _ : Fin 1 => σ) (fun _ => x) = mSigma E σ := by
  unfold STKloop
  have h : KLloopOf d (sz.L n) (fun _ : Fin 1 => σ) (fun _ => x) = ⟨[σ], [x]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [h]
  exact KLK_one d (sz.L n) (sz.lam n) (sz.W n) E u σ x

/-- `𝒦^{(2)}_{u,σ,a} = W^{-d} μ Θ_{uμ}(a₀, a₁)`, `μ = m(σ₀) m(σ₁)` (`KLK_two`; copy of the private
`lemDecCalE_STKloop_two`, `Path/LemDecCalE.lean:1276`). -/
theorem lemDecCalEPrec_STKloop_two_eq (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1) := by
  unfold STKloop
  have h : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [h]
  exact KLK_two d (sz.L n) (sz.lam n) (sz.W n) E u (σ 0) (σ 1) (a 0) (a 1)

/-- **The sharp size of `𝒦^{(2)}`**: `‖𝒦^{(2)}_{u,σ,a}‖ ≤ (W^d (1-u))⁻¹` (`K₀ = 1` of `E2Hyp`):
`‖Θ_{uμ}(a₀,a₁)‖ ≤ Σ_b ‖Θ_{uμ}(a₀,b)‖ ≤ (1-u)⁻¹` (`sum_norm_Theta_row_le`), `‖μ‖ = 1`. -/
theorem lemDecCalEPrec_Kbound (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STKloop sz n E u σ a‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
  have hμ : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (by exact_mod_cast sz.W_pos n) d
  have hrow := sum_norm_Theta_row_le (d := d) (L := sz.L n) (g := sz.lam n) (sz.three_le_L n)
    hu0 hu1 hμ (a 0)
  have hent : ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1)‖ ≤
      (1 - u)⁻¹ :=
    le_trans (Finset.single_le_sum (f := fun b => ‖Theta d (sz.L n) (sz.lam n)
      ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) b‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ (a 1))) hrow
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  rw [lemDecCalEPrec_STKloop_two_eq, norm_mul, norm_mul, hμ, mul_one, hWd, mul_inv]
  exact mul_le_mul_of_nonneg_left hent (inv_nonneg.2 hW.le)

/-- **The `(Kell*)` bridge**: `‖𝒦^{(2)}_{u,(+,-),(a,b)}‖ ≤ ‖Θ_u(a,b)‖` (`‖Θ_{uμ}(a,b)‖ ≤ Re Θ_u(a,b)`,
`norm_Theta_apply_le`, `‖μ‖ = 1`, `W^{-d} ≤ 1`). -/
theorem lemDecCalEPrec_Kell_bridge (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STKloop sz n E u σ a‖ ≤ ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) (a 0) (a 1)‖ := by
  have hμ : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]
  have h1 := norm_Theta_apply_le (d := d) (L := sz.L n) (g := sz.lam n) (sz.three_le_L n) hu0 hu1 hμ
    (a 0) (a 1)
  have h2 : (Theta d (sz.L n) (sz.lam n) (u : ℂ) (a 0) (a 1)).re ≤
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) (a 0) (a 1)‖ := Complex.re_le_norm _
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast sz.W_pos n))
  rw [lemDecCalEPrec_STKloop_two_eq, norm_mul, norm_mul, hμ, mul_one]
  calc ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ * ‖Theta d (sz.L n) (sz.lam n)
        ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1)‖
      ≤ 1 * ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) (a 0) (a 1)‖ :=
        mul_le_mul hWd (h1.trans h2) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- `a² ≤ 2 Q X`, `Q ≥ 1`, `0 < X ≤ 1` give `a ≤ 32 Q X^{1/4}` (`(P-e6)`). -/
private theorem lemDecCalEPrec_sqrt_le {a Q X : ℝ} (ha : 0 ≤ a) (hQ : 1 ≤ Q) (hX0 : 0 < X)
    (hX1 : X ≤ 1) (h : a ^ 2 ≤ Q * (2 * X)) : a ≤ 32 * Q * X ^ ((1 : ℝ) / 4) := by
  set Y : ℝ := X ^ ((1 : ℝ) / 4) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hY1 : Y ≤ 1 := Real.rpow_le_one hX0.le hX1 (by norm_num)
  have hY4 : Y ^ 4 = X := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hY2 : X ≤ Y ^ 2 := by
    rw [← hY4]
    have : Y ^ 2 ≤ 1 := pow_le_one₀ hY0.le hY1
    nlinarith [pow_pos hY0 2]
  have hQ0 : 0 < Q := by linarith
  have hsq : a ^ 2 ≤ (32 * Q * Y) ^ 2 := by
    calc a ^ 2 ≤ Q * (2 * X) := h
      _ ≤ Q * (2 * Y ^ 2) := by nlinarith
      _ ≤ (32 * Q * Y) ^ 2 := by nlinarith [mul_pos hQ0 (pow_pos hY0 2)]
  exact (pow_le_pow_iff_left₀ ha (by positivity) (by norm_num)).1 hsq

private theorem lemDecCalEPrec_gexRHS_nonneg (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a b : Zd d (sz.L n)) :
    0 ≤ gexRHS d (sz.L n) (sz.W n) E u M a b := by
  unfold gexRHS
  refine add_nonneg (Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ => ?_) ?_
  · split_ifs <;> positivity
  · split_ifs
    · positivity
    · exact le_rfl

/-- **The deterministic core at one time and one matrix** (`E2HypDif`, `E2HypWG` at `M = H_u`, `J := J`,
`Λ = 32 Q`, `K₀ = 1`): the twenty conjuncts of `E2Hyp` and the extras, from the numerical facts of
the size data, `1 ≤ J ≤ W` with `‖(𝓛-𝒦)^{(2)}‖ ≤ J T`, and the good-event bounds `g2` (`(P-e6)`), `g3`
(`(P-e7/8)`), `g4` (`(P-e9)`), `g53, g54, g56` (the three-, four-, six-loop clauses), each with the
loss `Q`.  The four-, six- and three-loop constants `2^{k-1} ≤ 32` use `B_{u,0} ≤ 2 (1-u)⁻¹`. -/
theorem lemDecCalEPrec_det (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E u D Q J : ℝ} (ω : sz.SeqΩ)
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hlam : 0 < sz.lam n)
    (hlamu : sz.lam n ^ 2 ≤ 1 - u) (hA : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)
    (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ)) (hQ : 1 ≤ Q)
    (hfl : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D)
    (hkell : ∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hJ1 : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ))
    (hJLK : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STLK2 sz n E u σ a ω ≤ J * STtailTD sz n u D a)
    (g2 : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n E u ω x y‖ ^ 2 ≤
      Q * STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)))
    (g3 : ∀ p q : Idx d (sz.L n) (sz.W n), p ≠ q → ‖Gt sz n E u true ω p q‖ ^ 2 ≤
      Q * gexRHS d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) (STblk sz n q) (STblk sz n p))
    (g4 : ∀ (σ : Fin 1 → Bool) (a : Fin 1 → Zd d (sz.L n)),
      ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ ≤ Q * sz.Bctl n u ^ 1)
    (g53 : ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)),
      ‖Lloop sz n E u σ a ω‖ ≤ Q * sz.Bctl n u ^ (3 - 1))
    (g54 : ∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)),
      ‖Lloop sz n E u σ a ω‖ ≤ Q * sz.Bctl n u ^ (4 - 1))
    (g56 : ∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)),
      ‖Lloop sz n E u σ a ω‖ ≤ Q * sz.Bctl n u ^ (6 - 1)) :
    E2HypDif sz n E u D (32 * Q) 1 J (sz.seqHflow n u ω) ∧
      E2HypWG sz n E u D (32 * Q) 1 J (sz.seqHflow n u ω) := by
  have hL3 := sz.three_le_L n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWd0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
  have hx : 0 < 1 - u := by linarith
  have hQ0 : 0 < Q := by linarith
  set X : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hX
  have hX0 : 0 < X := by rw [hX]; positivity
  have hX1 : X ≤ 1 := by
    rw [hX]
    refine inv_le_one_of_one_le₀ ?_
    nlinarith
  have hB : sz.Bctl n u ≤ 2 * X := lemDecCalEPrec_Bctl_le sz n hu1
  have hB0 : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hBk : ∀ k : ℕ, Q * sz.Bctl n u ^ k ≤ Q * (2 * X) ^ k := fun k =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0.le hB k) hQ0.le
  -- the loop clauses
  have l3 : ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)),
      ‖STLM sz n E u (sz.seqHflow n u ω) σ a‖ ≤ 32 * Q * X ^ 2 := by
    intro σ a
    calc ‖STLM sz n E u (sz.seqHflow n u ω) σ a‖ = ‖Lloop sz n E u σ a ω‖ := rfl
      _ ≤ Q * sz.Bctl n u ^ (3 - 1) := g53 σ a
      _ ≤ Q * (2 * X) ^ 2 := hBk 2
      _ ≤ 32 * Q * X ^ 2 := by nlinarith [mul_pos hQ0 (pow_pos hX0 2)]
  have l4 : ∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)),
      ‖STLM sz n E u (sz.seqHflow n u ω) σ a‖ ≤ 32 * Q * X ^ 3 := by
    intro σ a
    calc ‖STLM sz n E u (sz.seqHflow n u ω) σ a‖ = ‖Lloop sz n E u σ a ω‖ := rfl
      _ ≤ Q * sz.Bctl n u ^ (4 - 1) := g54 σ a
      _ ≤ Q * (2 * X) ^ 3 := hBk 3
      _ ≤ 32 * Q * X ^ 3 := by nlinarith [mul_pos hQ0 (pow_pos hX0 3)]
  have l6 : ∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)),
      ‖STLM sz n E u (sz.seqHflow n u ω) σ a‖ ≤ 32 * Q * X ^ 5 := by
    intro σ a
    calc ‖STLM sz n E u (sz.seqHflow n u ω) σ a‖ = ‖Lloop sz n E u σ a ω‖ := rfl
      _ ≤ Q * sz.Bctl n u ^ (6 - 1) := g56 σ a
      _ ≤ Q * (2 * X) ^ 5 := hBk 5
      _ ≤ 32 * Q * X ^ 5 := by nlinarith [mul_pos hQ0 (pow_pos hX0 5)]
  -- `E2Hyp`
  have hP := lemDecCalEPrec_P sz n (by omega)
  have hfloor2 : ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤ ((sz.W n : ℕ) : ℝ) ^ D :=
    hP.2.1.trans ((le_self_pow₀ hP.1 (by norm_num)).trans hfl)
  have e6 : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖Gres (sz.seqHflow n u ω) (zt E u) true x y - (if x = y then mE E else 0)‖ ≤
        (32 * Q) * X ^ ((1 : ℝ) / 4) := by
    intro x y
    have h := g2 x y
    have hw := lemDecCalEPrec_STWB_le sz n hu1
      (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
    have hsq : ‖STGM sz n E u ω x y‖ ^ 2 ≤ Q * (2 * X) :=
      h.trans (mul_le_mul_of_nonneg_left hw hQ0.le)
    exact lemDecCalEPrec_sqrt_le (norm_nonneg _) hQ hX0 hX1 hsq
  have e78 : ∀ p q : Idx d (sz.L n) (sz.W n), p ≠ q →
      ‖Gres (sz.seqHflow n u ω) (zt E u) true p q‖ ^ 2 ≤
        (32 * Q) * gexRHS d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) (STblk sz n q) (STblk sz n p) := by
    intro p q hpq
    have h := g3 p q hpq
    have hg := lemDecCalEPrec_gexRHS_nonneg sz n E u (sz.seqHflow n u ω) (STblk sz n q) (STblk sz n p)
    refine h.trans ?_
    nlinarith
  have e9 : ∀ (σ : Bool) (a : Zd d (sz.L n)),
      ‖avgErr d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) σ a‖ ≤ (32 * Q) * X := by
    intro σ a
    rw [lemDecCalEPrec_avgErr_eq]
    have h := g4 (fun _ => σ) (fun _ => a)
    rw [lemDecCalEPrec_STKloop_one] at h
    calc ‖STLM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => σ) (fun _ => a) - mSigma E σ‖
        ≤ Q * sz.Bctl n u ^ 1 := h
      _ ≤ Q * (2 * X) ^ 1 := hBk 1
      _ ≤ (32 * Q) * X := by nlinarith [mul_pos hQ0 hX0]
  have hE2 : E2Hyp sz n E u D (32 * Q) 1 J (sz.seqHflow n u ω) := by
    refine ⟨hd, hE, hu0, hu1, hlam, hlamu, hA, by linarith, le_rfl, hlog, hfloor2,
      seqHflow_isHermitian sz n u ω, e6, e78, e9, hJ1, hJW, ?_, ?_, ?_⟩
    · intro σ a
      exact hJLK σ a
    · intro a b
      have := lemDecCalEPrec_Kbound sz n hE.le hu0 hu1 ![true, false] ![a, b]
      rw [one_mul]
      exact this
    · intro a b hab
      have := lemDecCalEPrec_Kell_bridge sz n hE.le hu0 hu1 ![true, false] ![a, b]
      exact this.trans (hkell a b hab)
  exact ⟨⟨hE2, hfl, l4, l6⟩, ⟨hE2, hfl, l3⟩⟩

end Bridge

/-! ## 4. `(P-e7/8)` per time: `GijGEXPTSwap` from `(Gt_bound_flow)` -/

section Gij

variable {d : ℕ}

/-- `(W^d (1-u))⁻¹ ≤ W^{-2𝔡}` for `lam² ≤ 1-u` and `W^{2𝔡} ≤ lam² W^d` (`lam_sq_mul_pow_ge`). -/
theorem lemDecCalEPrec_X_le (sz : Sizes d) (n : ℕ) {u 𝔡 : ℝ}
    (hlamu : sz.lam n ^ 2 ≤ 1 - u)
    (hW : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) :
    (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (-𝔡)) ^ 2 := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
  have h2 : (((sz.W n : ℕ) : ℝ) ^ (-𝔡)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_neg hW0.le]
    congr 1; push_cast; ring
  rw [h2]
  have hpos : 0 < ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := Real.rpow_pos_of_pos hW0 _
  refine inv_anti₀ hpos ?_
  calc ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hW
    _ = ((sz.W n : ℕ) : ℝ) ^ d * sz.lam n ^ 2 := mul_comm _ _
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := mul_le_mul_of_nonneg_left hlamu hWd.le

/-- **`(asGMc)` per time, from `(Gt_bound_flow)` uniformly in `u`** (`c = 𝔡`): `|(G_u - M)_{xy}|² ≺ STWB
≤ 2 (W^d (1-u))⁻¹ ≤ 2 W^{-2𝔡}`, so `‖G_u - M‖_max ≺ W^{-𝔡}` per time (`W^{-2𝔡}` from `(eq:WO)` and
`lam² ≤ 1 - t`). -/
theorem lemDecCalEPrec_asGMcPT (sz : Sizes d) (E s t : ℕ → ℝ) {𝔡 : ℝ} (hWO : sz.WO 𝔡)
    (hsize : sz.SizeTendsto) (ht1 : ∀ n, t n < 1)
    (hReg : STReg5III sz s t) (hLoc : STLocalEntryU sz E s t) : AsGMcPT sz E s t 𝔡 := by
  intro τ hτ D hD
  filter_upwards [hLoc τ hτ D hD, hWO, hsize.eventually_ge_atTop (2 ^ (1 / τ))] with n h hWOn hN2
  intro p
  refine le_trans (measure_mono ?_) h
  intro ω hω
  refine ⟨p, ?_⟩
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hlamu : sz.lam n ^ 2 ≤ 1 - (p.1 : ℝ) := by
    have := hReg n
    have := p.1.2.2
    linarith
  have hX := lemDecCalEPrec_X_le sz n hlamu (lam_sq_mul_pow_ge sz n hWOn.1)
  have hw := lemDecCalEPrec_STWB_le sz n hu1 (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2))
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ 2 ^ (1 / τ) := Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  have hNτ : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    calc (2 : ℝ) = (2 ^ (1 / τ)) ^ τ := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_le_rpow (by positivity) hN2 hτ.le
  set w : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-𝔡) with hwdef
  have hw0 : 0 ≤ w := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set a : ℝ := llErrMat d (sz.L n) (sz.W n) (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2
    with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hω' : ((sz.size n : ℕ) : ℝ) ^ τ * w < a := hω
  have hNτ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg hN0.le _
  have hsq : (((sz.size n : ℕ) : ℝ) ^ τ * w) ^ 2 < a ^ 2 :=
    pow_lt_pow_left₀ hω' (mul_nonneg hNτ0 hw0) (by norm_num)
  change ((sz.size n : ℕ) : ℝ) ^ τ * STWB sz n (p.1 : ℝ) _ < ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2
  calc ((sz.size n : ℕ) : ℝ) ^ τ * STWB sz n (p.1 : ℝ)
        (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2))
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (2 * w ^ 2) :=
        mul_le_mul_of_nonneg_left (hw.trans (by nlinarith)) hNτ0
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) ^ τ * w ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg w]) hNτ0
    _ = (((sz.size n : ℕ) : ℝ) ^ τ * w) ^ 2 := by ring
    _ < a ^ 2 := hsq

/-- **`(GijGEX)` per time** (`GijGEXPTSwap`, the swapped one-orientation form of `E2Hyp`): `gbEXPV3` at
`(κ/2, 𝔠, 𝔡, ε/2)` with the premises of `v3_premises_of_stFlow`, and `(asGMc)` per time at `c = 𝔡`
(`lemDecCalEPrec_asGMcPT`). -/
theorem lemDecCalEPrec_gij (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) (z : ℕ → ℂ) (hκ : 0 < κ)
    (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5III sz s t)
    (hLoc : STLocalEntryU sz (STflowE z) s t) : GijGEXPTSwap sz (STflowE z) s t := by
  obtain ⟨hA, hE, ht1, hR⟩ := v3_premises_of_stFlow sz hκ hε hflow htz
  have hV3 := gbEXPV3 hd sz (κ / 2) 𝔠 𝔡 (ε / 2) (by positivity) hA.1 hA.2.1 (by positivity)
  have hAs : AsGMcPT sz (STflowE z) s t 𝔡 :=
    lemDecCalEPrec_asGMcPT sz (STflowE z) s t hA.2.2.2.2 hA.2.2.1 ht1 hReg hLoc
  exact (gijGEXPTSwap_giiGEXPT_of_V3 sz hV3 hA hE hs hst ht1 hR hA.2.1 hAs).1

end Gij

/-! ## 5. The per-time good event and its probability -/

section Good

variable {d : ℕ}

/-- **The per-time good event** at time `u`, loss `N^{τ'}`: the hypothesis `STLK2 ≤ N^{τ'} Jst T`,
`(P-e6)` (`STLocalEntryU`), `(P-e7/8)` (`GijGEXPTSwap`), `(P-e9)` (`STAvgU`) and the three-, four-,
six-loop clauses (`STLmaxU`, `k = 3, 4, 6`). -/
def lemDecCalEPrec_good (sz : Sizes d) (E : ℕ → ℝ) (D : ℝ) (Jst : ℕ → ℝ → ℝ → ℝ) (τ' : ℝ) (n : ℕ)
    (u : ℝ) : Set sz.SeqΩ :=
  {ω | (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        STLK2 sz n (E n) u σ a ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (Jst n u D * STtailTD sz n u D a)) ∧
    (∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (E n) u ω x y‖ ^ 2 ≤
        ((sz.size n : ℕ) : ℝ) ^ τ' *
          STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))) ∧
    (∀ p q : Idx d (sz.L n) (sz.W n), p ≠ q → ‖Gt sz n (E n) u true ω p q‖ ^ 2 ≤
        ((sz.size n : ℕ) : ℝ) ^ τ' *
          gexRHS d (sz.L n) (sz.W n) (E n) u (sz.seqHflow n u ω) (STblk sz n q) (STblk sz n p)) ∧
    (∀ (σ : Fin 1 → Bool) (a : Fin 1 → Zd d (sz.L n)),
        ‖Lloop sz n (E n) u σ a ω - STKloop sz n (E n) u σ a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n u ^ 1) ∧
    (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)),
        ‖Lloop sz n (E n) u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n u ^ (3 - 1)) ∧
    (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)),
        ‖Lloop sz n (E n) u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n u ^ (4 - 1)) ∧
    (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)),
        ‖Lloop sz n (E n) u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n u ^ (6 - 1))}

/-- A `Prec` statement on `TimeIcc × V` has, at every fixed time `u`, the failure event of the
`sup` over `v` of probability `≤ N^{-D}` (the union over `u` was inside `P`). -/
private theorem lemDecCalEPrec_fixed {V : ℕ → Type*} (sz : Sizes d) (s t : ℕ → ℝ)
    {ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ}
    (h : sz.Prec (U := fun n => TimeIcc s t n × V n) ξ ζ) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ u : TimeIcc s t n,
      sz.seqP {ω | ∃ v, ((sz.size n : ℕ) : ℝ) ^ τ * ζ n (u, v) ω < ξ n (u, v) ω} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  filter_upwards [h τ hτ D hD] with n hn u
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  obtain ⟨v, hv⟩ := hω
  exact ⟨(u, v), hv⟩

/-- Union bound for seven events of probability `≤ c`. -/
private theorem lemDecCalEPrec_union7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B₁ B₂ B₃ B₄ B₅ B₆ B₇ : Set Ω} {c : ℝ} (h₁ : P B₁ ≤ ENNReal.ofReal c)
    (h₂ : P B₂ ≤ ENNReal.ofReal c) (h₃ : P B₃ ≤ ENNReal.ofReal c) (h₄ : P B₄ ≤ ENNReal.ofReal c)
    (h₅ : P B₅ ≤ ENNReal.ofReal c) (h₆ : P B₆ ≤ ENNReal.ofReal c) (h₇ : P B₇ ≤ ENNReal.ofReal c) :
    P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ B₇) ≤ ENNReal.ofReal (7 * c) := by
  have e : ∀ A B : Set Ω, P (A ∪ B) ≤ P A + P B := fun A B => measure_union_le A B
  calc P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ B₇)
      ≤ P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆) + P B₇ := e _ _
    _ ≤ (P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅) + P B₆) + P B₇ := add_le_add (e _ _) le_rfl
    _ ≤ ((P (B₁ ∪ B₂ ∪ B₃ ∪ B₄) + P B₅) + P B₆) + P B₇ :=
        add_le_add (add_le_add (e _ _) le_rfl) le_rfl
    _ ≤ (((P (B₁ ∪ B₂ ∪ B₃) + P B₄) + P B₅) + P B₆) + P B₇ :=
        add_le_add (add_le_add (add_le_add (e _ _) le_rfl) le_rfl) le_rfl
    _ ≤ ((((P (B₁ ∪ B₂) + P B₃) + P B₄) + P B₅) + P B₆) + P B₇ :=
        add_le_add (add_le_add (add_le_add (add_le_add (e _ _) le_rfl) le_rfl) le_rfl) le_rfl
    _ ≤ (((((P B₁ + P B₂) + P B₃) + P B₄) + P B₅) + P B₆) + P B₇ :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (e _ _) le_rfl) le_rfl) le_rfl)
          le_rfl) le_rfl
    _ ≤ (((((ENNReal.ofReal c + ENNReal.ofReal c) + ENNReal.ofReal c) + ENNReal.ofReal c) +
          ENNReal.ofReal c) + ENNReal.ofReal c) + ENNReal.ofReal c := by gcongr
    _ = ENNReal.ofReal (7 * c) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring

/-- Union bound over a finite index: `P (⋃ i, S i) ≤ #ι · c`. -/
private theorem lemDecCalEPrec_iUnion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*}
    [Fintype ι] (S : ι → Set Ω) {c : ℝ} (h : ∀ i, P (S i) ≤ ENNReal.ofReal c) :
    P (⋃ i, S i) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * c) := by
  refine (measure_iUnion_fintype_le P S).trans ?_
  calc ∑ i, P (S i) ≤ ∑ _i : ι, ENNReal.ofReal c := Finset.sum_le_sum fun i _ => h i
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * c) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- **The probability of the per-time good event**: for `τ', D₁ > 0` and every time `u ∈ [s_n, t_n]`
(uniformly), eventually `P (good)ᶜ ≤ N^{-D₁}`: seven failure events, six from `Prec` statements (the union
over `u` inside `P`) and the `N²` entries `(p, q)` of `GijGEXPTSwap` at the fixed `u`
(`N² N^{-(D₁+3)} = N^{-(D₁+1)}`), `7 N^{-(D₁+1)} ≤ N^{-D₁}` for `N ≥ 7`. -/
theorem lemDecCalEPrec_prob (sz : Sizes d) (E s t : ℕ → ℝ) (Jst : ℕ → ℝ → ℝ → ℝ) (D : ℝ)
    (hsize : sz.SizeTendsto)
    (hLK : sz.Prec (U := STIdx2 sz s t) (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
        (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2))
    (hLoc : STLocalEntryU sz E s t) (hAvg : STAvgU sz E s t) (hLmax : STLmaxU sz E s t)
    (hGij : GijGEXPTSwap sz E s t) {τ' D₁ : ℝ} (hτ' : 0 < τ') (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, ∀ u : TimeIcc s t n,
      sz.seqP (lemDecCalEPrec_good sz E D Jst τ' n u)ᶜ ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  have hD1 : 0 < D₁ + 1 := by linarith
  have h1 := lemDecCalEPrec_fixed sz s t
    (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) hLK hτ' hD1
  have h2 := lemDecCalEPrec_fixed sz s t
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hLoc hτ' hD1
  have h4 := lemDecCalEPrec_fixed sz s t
    (V := fun n => (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))) hAvg hτ' hD1
  have h5 := lemDecCalEPrec_fixed sz s t
    (V := fun n => (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n))) (hLmax 3 (by norm_num)) hτ' hD1
  have h6 := lemDecCalEPrec_fixed sz s t
    (V := fun n => (Fin 4 → Bool) × (Fin 4 → Zd d (sz.L n))) (hLmax 4 (by norm_num)) hτ' hD1
  have h7 := lemDecCalEPrec_fixed sz s t
    (V := fun n => (Fin 6 → Bool) × (Fin 6 → Zd d (sz.L n))) (hLmax 6 (by norm_num)) hτ' hD1
  have h3 := hGij τ' hτ' (D₁ + 3) (by linarith)
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, hsize.eventually_ge_atTop 7] with n h1 h2 h3 h4 h5 h6
    h7 hN7
  intro u
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  -- the union over the `N²` entries
  have h3' : sz.seqP (⋃ pq : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      {ω | ((sz.size n : ℕ) : ℝ) ^ τ' *
          gexRHS d (sz.L n) (sz.W n) (E n) (u : ℝ) (sz.seqHflow n (u : ℝ) ω) (STblk sz n pq.2)
            (STblk sz n pq.1) <
        (if pq.1 = pq.2 then 0 else ‖Gt sz n (E n) (u : ℝ) true ω pq.1 pq.2‖ ^ 2)}) ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1))) := by
    refine (lemDecCalEPrec_iUnion sz.seqP _ (c := ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 3)))
      fun pq => h3 (u, pq)).trans ?_
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [Fintype.card_prod, sz.card_Idx n, Nat.cast_mul]
    have e1 : ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) := by
      rw [Real.rpow_two]; ring
    rw [← e1, ← Real.rpow_add hN0]
    congr 1; ring
  refine (measure_mono ?_).trans
    ((lemDecCalEPrec_union7 sz.seqP (h1 u) (h2 u) h3' (h4 u) (h5 u) (h6 u) (h7 u)).trans ?_)
  · -- the inclusion of the bad event
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, Set.mem_iUnion, not_exists, not_lt] at hnot
    obtain ⟨⟨⟨⟨⟨⟨hn1, hn2⟩, hn3⟩, hn4⟩, hn5⟩, hn6⟩, hn7⟩ := hnot
    refine hω ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro σ a; exact hn1 (σ, a)
    · intro x y; exact hn2 (x, y)
    · intro p q hpq
      have := hn3 (p, q)
      simpa [hpq] using this
    · intro σ a; exact hn4 (σ, a)
    · intro σ a; exact hn5 (σ, a)
    · intro σ a; exact hn6 (σ, a)
    · intro σ a; exact hn7 (σ, a)
  · -- `7 N^{-(D₁+1)} ≤ N^{-D₁}`
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) =
        ((sz.size n : ℕ) : ℝ) ^ (-D₁) * ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [e, Real.rpow_neg_one]
    have hp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have : 7 * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN7
    nlinarith

/-! ## 6. The deterministic conclusion on the good event -/

/-- `R₁ = (1-u)⁻¹ (W^d |1-u|)⁻¹ T_{u,D}(|a₁-a₂|)`: the deterministic factor of the first conclusion of
`STLemDecCalEConcl` (`Step5Pins.lean:169`). -/
def lemDecCalEPrec_R1 (sz : Sizes d) (n : ℕ) (D u : ℝ) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  (1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * STtailTD sz n u D a

/-- The indicator summand of the second conclusion: `(1-u)⁻¹ 1(|a₁-a₂| ≤ (log W)^{3/2}) T`. -/
def lemDecCalEPrec_R2₀ (sz : Sizes d) (n : ℕ) (D u : ℝ) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  (1 - u)⁻¹ * (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
    Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) * STtailTD sz n u D a

/-- The factor of `J^{3/2}` in the second conclusion: `(1-u)⁻¹ (W^d |1-u|)^{-1/2} T`. -/
def lemDecCalEPrec_R2 (sz : Sizes d) (n : ℕ) (D u : ℝ) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  (1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * STtailTD sz n u D a

/-- The indicator summand of the third conclusion: `(1-u)⁻¹ 1(|a₁-a₂| ≤ 4 (log W)^{3/2}) T²`. -/
def lemDecCalEPrec_R3₀ (sz : Sizes d) (n : ℕ) (D u : ℝ) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  (1 - u)⁻¹ * (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
    4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) * STtailTD sz n u D a ^ 2

/-- The factor of `J³` in the third conclusion: `(1-u)⁻¹ (W^d |1-u|)^{-1/2} T²`. -/
def lemDecCalEPrec_R3 (sz : Sizes d) (n : ℕ) (D u : ℝ) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  (1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * STtailTD sz n u D a ^ 2

/-- The three bounds of `STLemDecCalEConcl` at one time, one sample, with the realized control `J♯` and the
loss absorbed by `N^τ`: `ξ ≤ N^τ (R₀ + J♯^m R)`, `m = 2, 3/2, 3`. -/
def lemDecCalEPrec_Bounds (sz : Sizes d) (E : ℕ → ℝ) (D τ : ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) : Prop :=
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖STELKLK sz n (E n) u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (0 + LemDecCalELip_Jsharp sz E D n u ω ^ (2 : ℝ) * lemDecCalEPrec_R1 sz n D u a)) ∧
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖STEGt sz n (E n) u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (lemDecCalEPrec_R2₀ sz n D u a +
          LemDecCalELip_Jsharp sz E D n u ω ^ (3 / 2 : ℝ) * lemDecCalEPrec_R2 sz n D u a)) ∧
    (∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (a i - a' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STee sz n (E n) u ω σ a a'‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (lemDecCalEPrec_R3₀ sz n D u a +
          LemDecCalELip_Jsharp sz E D n u ω ^ (3 : ℝ) * lemDecCalEPrec_R3 sz n D u a))

/-- **Deterministic conclusions on the good event** (steps (P) of the amendment): on `ω ∈ good` the
realized control `J♯` satisfies `1 ≤ J♯ ≤ N^{τ'} Jst ≤ W` (the premise `Jst ≤ W^{1/2}` and
`N^{τ'} ≤ W^{1/2}`), so `E2HypDif`, `E2HypWG` hold at `M = H_u`, `J := J♯`, `Λ = 32 N^{τ'}`, `K₀ = 1`
(`lemDecCalEPrec_det`) and `lemDecCalE_lk/_wG/_dif` give the three bounds with the loss
`≤ N^{τ/2} ≤ N^τ`, in the form `ξ ≤ N^τ (R₀ + J♯^m R)`. -/
theorem lemDecCalEPrec_goodDet (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) (E : ℕ → ℝ)
    (Jst : ℕ → ℝ → ℝ → ℝ) {u D τ τ' : ℝ} (ω : sz.SeqΩ) (hτ' : 0 ≤ τ') (hτ : 0 < τ)
    (hJst1 : 1 ≤ Jst n u D) (hJstW : Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ))
    (hQW : ((sz.size n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ))
    (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (hE : |E n| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hlam : 0 < sz.lam n)
    (hlamu : sz.lam n ^ 2 ≤ 1 - u) (hA : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)
    (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hfl : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D)
    (hkell : ∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hloss : lossE2wG d (sz.L n) (sz.W n) (32 * ((sz.size n : ℕ) : ℝ) ^ τ') 1 ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hω : ω ∈ lemDecCalEPrec_good sz E D Jst τ' n u) :
    lemDecCalEPrec_Bounds sz E D τ n u ω := by
  obtain ⟨g1, g2, g3, g4, g53, g54, g56⟩ := hω
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hQ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set Q : ℝ := N ^ τ' with hQdef
  set J : ℝ := LemDecCalELip_Jsharp sz E D n u ω with hJdef
  have hb := LemDecCalELip_Jsharp_basic sz E D n u ω
  have hJ1 : 1 ≤ J := hb.1
  have hJX : J ≤ Q * Jst n u D := by
    refine hb.2.2 (Q * Jst n u D) (by nlinarith) fun σ a => ?_
    have := g1 σ a
    calc STLK2 sz n (E n) u σ a ω ≤ Q * (Jst n u D * STtailTD sz n u D a) := this
      _ = Q * Jst n u D * STtailTD sz n u D a := by ring
  have hJW : J ≤ ((sz.W n : ℕ) : ℝ) := by
    refine hJX.trans ?_
    calc Q * Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul hQW hJstW (by linarith) (Real.rpow_nonneg hW0.le _)
      _ = ((sz.W n : ℕ) : ℝ) := by
          rw [← Real.rpow_add hW0]; norm_num
  obtain ⟨hDif, hWG⟩ := lemDecCalEPrec_det hd sz n ω hE hu0 hu1 hlam hlamu hA hlog hQ1 hfl hkell hJ1
    hJW hb.2.1 g2 g3 g4 g53 g54 g56
  have hmono := lemDecCalEPrec_loss_mono sz (by omega) n (32 * Q) 1
  have hNτ : N ^ (τ / 2) ≤ N ^ τ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hl1 : lossE2 d (sz.L n) (sz.W n) (32 * Q) 1 ≤ N ^ τ :=
    hmono.1.trans (hmono.2.trans (hloss.trans hNτ))
  have hl2 : lossE2wG d (sz.L n) (sz.W n) (32 * Q) 1 ≤ N ^ τ := hloss.trans hNτ
  have hl3 : lossE2dif d (sz.L n) (sz.W n) (32 * Q) 1 ≤ N ^ τ := hmono.2.trans hl2
  have hx : 0 < 1 - u := by linarith
  have hxi : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hx.le
  have hX' : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by positivity
  have hJ0 : 0 ≤ J := by linarith
  have hT : ∀ a : Fin 2 → Zd d (sz.L n), 0 ≤ STtailTD sz n u D a := fun a =>
    (LemDecCalELip_tail_pos sz n u D a).le
  refine ⟨fun σ a => ?_, fun σ a => ?_, fun σ a a' hr => ?_⟩
  · have h := lemDecCalE_lk d sz n (E n) u D (32 * Q) 1 J (sz.seqHflow n u ω) hDif.1 σ a
    have hΦ : 0 ≤ (1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2 * STtailTD sz n u D a :=
      mul_nonneg (mul_nonneg (mul_nonneg hxi hX') (sq_nonneg _)) (hT a)
    calc ‖STELKLK sz n (E n) u σ a ω‖ = ‖STELKLKM sz n (E n) u (sz.seqHflow n u ω) σ a‖ := rfl
      _ ≤ lossE2 d (sz.L n) (sz.W n) (32 * Q) 1 *
          ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2) * STtailTD sz n u D a := h
      _ = lossE2 d (sz.L n) (sz.W n) (32 * Q) 1 *
          ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2 * STtailTD sz n u D a) := by
          ring
      _ ≤ N ^ τ * ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2 * STtailTD sz n u D a) :=
          mul_le_mul_of_nonneg_right hl1 hΦ
      _ = N ^ τ * (0 + J ^ (2 : ℝ) * lemDecCalEPrec_R1 sz n D u a) := by
          rw [Real.rpow_two, lemDecCalEPrec_R1]; ring
  · have h := lemDecCalE_wG d sz n (E n) u D (32 * Q) 1 J (sz.seqHflow n u ω) hWG σ a
    set ind : ℝ := (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) with hind
    have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
    have hΨ : 0 ≤ (1 - u)⁻¹ * (ind + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) *
        J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a :=
      mul_nonneg (mul_nonneg hxi (add_nonneg hind0 (mul_nonneg (Real.rpow_nonneg hX' _)
        (Real.rpow_nonneg hJ0 _)))) (hT a)
    calc ‖STEGt sz n (E n) u σ a ω‖ = ‖STEGtM sz n (E n) u (sz.seqHflow n u ω) σ a‖ := rfl
      _ ≤ lossE2wG d (sz.L n) (sz.W n) (32 * Q) 1 * ((1 - u)⁻¹ * (ind +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) *
            STtailTD sz n u D a) := h
      _ ≤ N ^ τ * ((1 - u)⁻¹ * (ind +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) *
            STtailTD sz n u D a) := mul_le_mul_of_nonneg_right hl2 hΨ
      _ = N ^ τ * (lemDecCalEPrec_R2₀ sz n D u a + J ^ (3 / 2 : ℝ) * lemDecCalEPrec_R2 sz n D u a) := by
          rw [lemDecCalEPrec_R2₀, lemDecCalEPrec_R2]; ring
  · have h := lemDecCalE_dif d sz n (E n) u D (32 * Q) 1 J (sz.seqHflow n u ω) hDif σ a a' hr
    set ind : ℝ := (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
      4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) with hind
    have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
    have hΨ : 0 ≤ (1 - u)⁻¹ * (ind + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) *
        J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2 :=
      mul_nonneg (mul_nonneg hxi (add_nonneg hind0 (mul_nonneg (Real.rpow_nonneg hX' _)
        (Real.rpow_nonneg hJ0 _)))) (sq_nonneg _)
    calc ‖STee sz n (E n) u ω σ a a'‖ = ‖STeeM sz n (E n) u (sz.seqHflow n u ω) σ a a'‖ := rfl
      _ ≤ lossE2dif d (sz.L n) (sz.W n) (32 * Q) 1 * ((1 - u)⁻¹ * (ind +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) *
            STtailTD sz n u D a ^ 2) := h
      _ ≤ N ^ τ * ((1 - u)⁻¹ * (ind +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) *
            STtailTD sz n u D a ^ 2) := mul_le_mul_of_nonneg_right hl3 hΨ
      _ = N ^ τ * (lemDecCalEPrec_R3₀ sz n D u a + J ^ (3 : ℝ) * lemDecCalEPrec_R3 sz n D u a) := by
          rw [lemDecCalEPrec_R3₀, lemDecCalEPrec_R3]; ring

/-! ## 7. The eventual numerical facts and the per-time bounds -/

/-- Eventually: `0 < lam`, `1 ≤ lam² W^d` (`(eq:WO)`), `4 ≤ log W` (`W ≥ N^𝔠 → ∞`) and `1 ≤ N`. -/
theorem lemDecCalEPrec_numeric (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧
      4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) := by
  obtain ⟨h𝔠, h𝔡, hsize, hBW, hWO⟩ := hA
  have hNc : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hsize
  filter_upwards [st5_eventually_A_ge_one sz h𝔡 hWO, hBW, hNc.eventually_ge_atTop (Real.exp 4),
    hsize.eventually_ge_atTop 1] with n h1 h2 h3 h4
  refine ⟨h1.1, h1.2, ?_, h4⟩
  have h5 : Real.exp 4 ≤ ((sz.W n : ℕ) : ℝ) := h3.trans h2
  calc (4 : ℝ) = Real.log (Real.exp 4) := (Real.log_exp 4).symm
    _ ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_le_log (Real.exp_pos 4) h5

/-- The `(Kell*)` premise of `E2Hyp`, eventually and uniformly in `u ∈ [0, t_n]`
(`kellStarEv` at `δ = 1/8`, `Λ = 𝔡⁻¹`, `τ = ε/2`, `s = 0`; `RangeCond (ε/2) t` from
`v3_premises_of_stFlow`). -/
theorem lemDecCalEPrec_kell (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) (z : ℕ → ℂ) (hκ : 0 < κ)
    (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (htz : ∀ n, t n ≤ lemT (z n)) (D : ℝ) :
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  obtain ⟨hA, hE, ht1, hR⟩ := v3_premises_of_stFlow sz hκ hε hflow htz
  obtain ⟨h𝔠, h𝔡, hsize, hBW, hWO⟩ := hA
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  filter_upwards [kellStarEv d sz 𝔠 𝔡⁻¹ (ε / 2) (1 / 8) D t hd h𝔠 (inv_pos.2 h𝔡) (by positivity)
    (by norm_num) hsize hBW hR ht1 hlam] with n hn u hu0 hut a b hab
  exact (hn 0 u le_rfl hu0 hut a b hab).1

/-- `N^{τ'} ≤ W^{1/2}` from the floor `(L^d W^{6d})² ≤ W^D` (`N ≤ L^d W^{6d} ≤ (L^d W^{6d})² ≤ W^D`) and
`D τ' ≤ 1/2`: the realized control `J♯ ≤ N^{τ'} Jst ≤ W^{1/2} W^{1/2}` (M3, DECISIONS §63). -/
theorem lemDecCalEPrec_QW (sz : Sizes d) (n : ℕ) (hd : 1 ≤ d) {D τ' : ℝ} (hτ' : 0 ≤ τ')
    (hDτ : D * τ' ≤ 1 / 2)
    (hfl : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) :
    ((sz.size n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨hW, hL, hN, hWN, hN1⟩ := lemDecCalEPrec_sizes sz n hd
  obtain ⟨hP1, -, -, hNP⟩ := lemDecCalEPrec_P sz n hd
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hND : ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ D :=
    hNP.trans ((le_self_pow₀ hP1 (by norm_num)).trans hfl)
  calc ((sz.size n : ℕ) : ℝ) ^ τ' ≤ (((sz.W n : ℕ) : ℝ) ^ D) ^ τ' :=
        Real.rpow_le_rpow (by linarith) hND hτ'
    _ = ((sz.W n : ℕ) : ℝ) ^ (D * τ') := by rw [← Real.rpow_mul hW0.le]
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW hDτ

/-- **The per-time bounds** (steps (P)): for `τ, D₁ > 0`, eventually, at every time `u ∈ [s_n, t_n]`, with
`τ' = min (τ/24) (1/(2D))`: the good event has probability `≥ 1 - N^{-D₁}` and on it the three bounds of
`STLemDecCalEConcl` hold with the realized control `J♯` and the factor `N^τ`. -/
theorem lemDecCalEPrec_perTime_bounds (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) (z : ℕ → ℂ)
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htz : ∀ n, t n ≤ lemT (z n))
    (hReg : STReg5III sz s t)
    (hLoc : STLocalEntryU sz (STflowE z) s t) (hAvg : STAvgU sz (STflowE z) s t)
    (hLmax : STLmaxU sz (STflowE z) s t) (Jst : ℕ → ℝ → ℝ → ℝ) (hJ1 : ∀ n u D, 1 ≤ Jst n u D)
    (hJW : ∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) {D : ℝ} (hD : 0 < D)
    (hfl : ∀ᶠ n in atTop,
      (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D)
    (hLK : sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => STLK2 sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω)
      (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2))
    {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, ∀ u : TimeIcc s t n,
      sz.seqP (lemDecCalEPrec_good sz (STflowE z) D Jst (min (τ / 24) (1 / (2 * D))) n u)ᶜ ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) ∧
      ∀ ω ∈ lemDecCalEPrec_good sz (STflowE z) D Jst (min (τ / 24) (1 / (2 * D))) n u,
        lemDecCalEPrec_Bounds sz (STflowE z) D τ n (u : ℝ) ω := by
  obtain ⟨hA, hE, ht1, hR⟩ := v3_premises_of_stFlow sz hκ hε hflow htz
  have hτ'0 : 0 < min (τ / 24) (1 / (2 * D)) := lt_min (by positivity) (by positivity)
  have hτ'a : min (τ / 24) (1 / (2 * D)) ≤ τ / 24 := min_le_left _ _
  have hτ'b : min (τ / 24) (1 / (2 * D)) ≤ 1 / (2 * D) := min_le_right _ _
  have hDτ : D * min (τ / 24) (1 / (2 * D)) ≤ 1 / 2 := by
    calc D * min (τ / 24) (1 / (2 * D)) ≤ D * (1 / (2 * D)) := mul_le_mul_of_nonneg_left hτ'b hD.le
      _ = 1 / 2 := by field_simp
  have hGij := lemDecCalEPrec_gij hd sz z hκ hε hflow hs (fun n => (hst n).le) htz hReg hLoc
  have hprob := lemDecCalEPrec_prob sz (STflowE z) s t Jst D hA.2.2.1 hLK hLoc hAvg hLmax hGij hτ'0 hD₁
  have hloss := lemDecCalEPrec_lossWG_eventually sz (by omega) hA.2.2.1 hτ hτ'0.le (by linarith)
  have hnum := lemDecCalEPrec_numeric sz hA
  have hkell := lemDecCalEPrec_kell hd sz z hκ hε hflow htz D
  filter_upwards [hprob, hloss, hnum, hkell, hfl] with n hp hl hn hk hf
  intro u
  have hu0 : 0 ≤ (u : ℝ) := (hs n).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 n)
  refine ⟨hp u, fun ω hω => ?_⟩
  exact lemDecCalEPrec_goodDet hd sz n (STflowE z) Jst ω hτ'0.le hτ (hJ1 n u D) (hJW n u D)
    (lemDecCalEPrec_QW sz n (by omega) hτ'0.le hDτ hf) hn.2.2.2 ((hE n).trans_le (by linarith)) hu0
    hu1 hn.1 (by have := hReg n; have := u.2.2; linarith) hn.2.1 hn.2.2.1 hf
    (fun a b => hk (u : ℝ) hu0 u.2.2 a b) hl hω

/-- The index set of the fourth conclusion without the time: `(σ, a, a')` with `|a_i - a'_i|_∞ ≤ (log W)^{3/2}`
(`Step5Pins.lean:179-180` without the time component; the re-indexing of the amendment, (N)). -/
abbrev lemDecCalEPrec_V3 (sz : Sizes d) (n : ℕ) : Type :=
  {r : ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) × (Fin 2 → Zd d (sz.L n)) //
    ∀ i : Fin 2, ((zdistInf d (sz.L n) (r.1.2 i - r.2 i) : ℕ) : ℝ) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)}

/-- **The three per-time statements** `PrecPT(‖ℰ_i‖ ≺ R₀ᵢ + J♯^{m_i} Rᵢ)`, `m = 2, 3/2, 3` (the deterministic
lemmas `lemDecCalE_lk/_wG/_dif` at the realized control `J♯`; step (P)). -/
theorem lemDecCalEPrec_precPT (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) (z : ℕ → ℂ)
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htz : ∀ n, t n ≤ lemT (z n))
    (hReg : STReg5III sz s t)
    (hLoc : STLocalEntryU sz (STflowE z) s t) (hAvg : STAvgU sz (STflowE z) s t)
    (hLmax : STLmaxU sz (STflowE z) s t) (Jst : ℕ → ℝ → ℝ → ℝ) (hJ1 : ∀ n u D, 1 ≤ Jst n u D)
    (hJW : ∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) {D : ℝ} (hD : 0 < D)
    (hfl : ∀ᶠ n in atTop,
      (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D)
    (hLK : sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => STLK2 sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω)
      (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2)) :
    sz.PrecPT (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
      (fun n p ω => ‖STELKLK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p ω => 0 +
        LemDecCalELip_Jsharp sz (STflowE z) D n (p.1 : ℝ) ω ^ (2 : ℝ) *
          lemDecCalEPrec_R1 sz n D (p.1 : ℝ) p.2.2) ∧
    sz.PrecPT (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
      (fun n p ω => ‖STEGt sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p ω => lemDecCalEPrec_R2₀ sz n D (p.1 : ℝ) p.2.2 +
        LemDecCalELip_Jsharp sz (STflowE z) D n (p.1 : ℝ) ω ^ (3 / 2 : ℝ) *
          lemDecCalEPrec_R2 sz n D (p.1 : ℝ) p.2.2) ∧
    sz.PrecPT (U := fun n => TimeIcc s t n × lemDecCalEPrec_V3 sz n)
      (fun n p ω => ‖STee sz n (STflowE z n) (p.1 : ℝ) ω p.2.1.1.1 p.2.1.1.2 p.2.1.2‖)
      (fun n p ω => lemDecCalEPrec_R3₀ sz n D (p.1 : ℝ) p.2.1.1.2 +
        LemDecCalELip_Jsharp sz (STflowE z) D n (p.1 : ℝ) ω ^ (3 : ℝ) *
          lemDecCalEPrec_R3 sz n D (p.1 : ℝ) p.2.1.1.2) := by
  have key : ∀ {τ D₁ : ℝ}, 0 < τ → 0 < D₁ → ∀ᶠ n in atTop, ∀ u : TimeIcc s t n,
      sz.seqP (lemDecCalEPrec_good sz (STflowE z) D Jst (min (τ / 24) (1 / (2 * D))) n u)ᶜ ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) ∧
      ∀ ω ∈ lemDecCalEPrec_good sz (STflowE z) D Jst (min (τ / 24) (1 / (2 * D))) n u,
        lemDecCalEPrec_Bounds sz (STflowE z) D τ n (u : ℝ) ω := fun {τ D₁} hτ hD₁ =>
    lemDecCalEPrec_perTime_bounds hd sz z hκ hε hflow hs hst htz hReg hLoc hAvg hLmax Jst hJ1 hJW hD
      hfl hLK hτ hD₁
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ D₁ hD₁
    filter_upwards [key hτ hD₁] with n hn p
    refine le_trans (measure_mono ?_) (hn p.1).1
    intro ω hω
    by_contra hgood
    have hb := (hn p.1).2 ω (not_not.1 hgood)
    exact absurd hω (not_lt.2 (hb.1 p.2.1 p.2.2))
  · intro τ hτ D₁ hD₁
    filter_upwards [key hτ hD₁] with n hn p
    refine le_trans (measure_mono ?_) (hn p.1).1
    intro ω hω
    by_contra hgood
    have hb := (hn p.1).2 ω (not_not.1 hgood)
    exact absurd hω (not_lt.2 (hb.2.1 p.2.1 p.2.2))
  · intro τ hτ D₁ hD₁
    filter_upwards [key hτ hD₁] with n hn p
    refine le_trans (measure_mono ?_) (hn p.1).1
    intro ω hω
    by_contra hgood
    have hb := (hn p.1).2 ω (not_not.1 hgood)
    exact absurd hω (not_lt.2 (hb.2.2 p.2.1.1.1 p.2.1.1.2 p.2.1.2 p.2.2))

end Good

/-! ## 8. (N): the net lift of the three conclusions -/

section Lift

variable {d : ℕ}

/-- `(1 + a x)^k ≤ 1 + ((1+a)^k - 1) x` for `a ≥ 0`, `0 ≤ x ≤ 1`. -/
private theorem lemDecCalEPrec_one_add_pow {a x : ℝ} (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (k : ℕ) : (1 + a * x) ^ k ≤ 1 + ((1 + a) ^ k - 1) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : 0 ≤ (1 + a) ^ k - 1 := by
      have := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + a) (n := k)
      linarith
    calc (1 + a * x) ^ (k + 1) = (1 + a * x) ^ k * (1 + a * x) := pow_succ _ _
      _ ≤ (1 + ((1 + a) ^ k - 1) * x) * (1 + a * x) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ 1 + ((1 + a) ^ (k + 1) - 1) * x := by
          have hx2 : x * x ≤ x := by nlinarith
          have h3 : 0 ≤ ((1 + a) ^ k - 1) * a := mul_nonneg hc ha
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_left hx2 h3]

/-- `ρ^k ≤ 1 + N^{2k} x` for `1 ≤ ρ ≤ 1 + N x`, `0 ≤ x ≤ 1`, `N ≥ 2` (the relative continuity of the
deterministic factors, as a power of `ρ`). -/
theorem lemDecCalEPrec_pow_rel {N x ρ : ℝ} (k : ℕ) (hN : 2 ≤ N) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ 1 + N * x) : ρ ^ k ≤ 1 + N ^ (2 * k) * x := by
  have h1 : ρ ^ k ≤ (1 + N * x) ^ k := pow_le_pow_left₀ (by linarith) hρ k
  have h2 := lemDecCalEPrec_one_add_pow (by linarith : 0 ≤ N) hx0 hx1 k
  have h3 : (1 + N) ^ k ≤ N ^ (2 * k) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by linarith) (by nlinarith) k
  have h4 : ((1 + N) ^ k - 1) * x ≤ N ^ (2 * k) * x :=
    mul_le_mul_of_nonneg_right (by linarith) hx0
  linarith

private theorem lemDecCalEPrec_card_Zd (L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

private theorem lemDecCalEPrec_Zd_le_size (sz : Sizes d) (n : ℕ) : (sz.L n) ^ d ≤ sz.size n := by
  rw [Sizes.size]
  exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d

private theorem lemDecCalEPrec_card_pair (L : ℕ) [NeZero L] :
    Fintype.card (Fin 2 → Zd d L) = (L ^ d) ^ 2 := by
  rw [Fintype.card_fun, lemDecCalEPrec_card_Zd, Fintype.card_fin]

private theorem lemDecCalEPrec_card_signs : Fintype.card (Fin 2 → Bool) = 4 := by
  simp

/-- `#((Fin 2 → Bool) × (Fin 2 → Z_L^d)) ≤ N³` once `N ≥ 4`. -/
theorem lemDecCalEPrec_card_V12 (sz : Sizes d) (n : ℕ) (hN : 4 ≤ ((sz.size n : ℕ) : ℝ)) :
    (Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
  have h1 : Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) ≤ 4 * (sz.size n) ^ 2 := by
    rw [Fintype.card_prod, lemDecCalEPrec_card_signs, lemDecCalEPrec_card_pair]
    exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (lemDecCalEPrec_Zd_le_size sz n) 2)
  have h2 : ((Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℕ) : ℝ) ≤
      4 * ((sz.size n : ℕ) : ℝ) ^ 2 := by exact_mod_cast h1
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  nlinarith [pow_nonneg hN0 2]

/-- `#V3 ≤ N⁵` once `N ≥ 4`. -/
theorem lemDecCalEPrec_card_V3 (sz : Sizes d) (n : ℕ) (hN : 4 ≤ ((sz.size n : ℕ) : ℝ)) :
    (Fintype.card (lemDecCalEPrec_V3 sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (5 : ℝ) := by
  have h1 : Fintype.card (lemDecCalEPrec_V3 sz n) ≤ 4 * (sz.size n) ^ 4 := by
    calc Fintype.card (lemDecCalEPrec_V3 sz n)
        ≤ Fintype.card (((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) × (Fin 2 → Zd d (sz.L n))) :=
          Fintype.card_subtype_le _
      _ = 4 * (sz.L n ^ d) ^ 2 * (sz.L n ^ d) ^ 2 := by
          rw [Fintype.card_prod, Fintype.card_prod, lemDecCalEPrec_card_signs,
            lemDecCalEPrec_card_pair]
      _ ≤ 4 * (sz.size n) ^ 2 * (sz.size n) ^ 2 := by
          have := Nat.pow_le_pow_left (lemDecCalEPrec_Zd_le_size sz n) 2
          exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl this) this
      _ = 4 * (sz.size n) ^ 4 := by ring
  have h2 : ((Fintype.card (lemDecCalEPrec_V3 sz n) : ℕ) : ℝ) ≤
      4 * ((sz.size n : ℕ) : ℝ) ^ 4 := by exact_mod_cast h1
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  nlinarith [pow_nonneg hN0 4]

/-- **(N) the net lift** (the amendment, step (N)): `PrecPT(ξ ≺ R₀ + J♯^m R)` gives `Prec(ξ ≺ R₀ + J♯^m R)` for
the realized control `J♯` (`LemDecCalELip_Jsharp`), when `ξ` is Hölder-1/2 in `u` on `contGood` (`hξ`, from
(L1)), `R₀ ≥ 0`, `R ≥ N^{-CR}`, and `R₀, R` are relatively continuous at the power `ρ^k`,
`ρ = 1 + (1-t)⁻¹ |u-u'|` (`hrel`, from (L2)); the relative continuity of `J♯` is
`LemDecCalELip_Jsharp_rel`, and `ρ^k ≤ 1 + N^{2k} √|u-u'|` (`lemDecCalEPrec_pow_rel`).  The exponent of
the lift is `C = max (C_ξ, C_J, 2k)`. -/
theorem lemDecCalEPrec_lift (hd : 3 ≤ d) (sz : Sizes d) (E s t : ℕ → ℝ) {κ D : ℝ} (hκ : 0 < κ)
    (hD : 0 < D) (hsize : sz.SizeTendsto) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (V : ℕ → Type) [∀ n, Fintype (V n)] (ξ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ)
    (hξ : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ contGood sz n, ∀ (u u' : TimeIcc s t n) (v : V n),
      |ξ n (u, v) ω - ξ n (u', v) ω| ≤
        ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|)
    (R₀ R : ∀ n, TimeIcc s t n × V n → ℝ) {m : ℝ} (k : ℕ) (Cv CR : ℝ) (hm : 0 ≤ m)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv)
    (hR₀ : ∀ n p, 0 ≤ R₀ n p)
    (hRlow : ∀ᶠ n in atTop, ∀ p, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ R n p)
    (hrel : ∀ n (u u' : TimeIcc s t n) (v : V n),
      R₀ n (u', v) ≤ (1 + (1 - t n)⁻¹ * |(u : ℝ) - (u' : ℝ)|) ^ k * R₀ n (u, v) ∧
      R n (u', v) ≤ (1 + (1 - t n)⁻¹ * |(u : ℝ) - (u' : ℝ)|) ^ k * R n (u, v))
    (hPT : sz.PrecPT ξ
      (fun n p ω => R₀ n p + LemDecCalELip_Jsharp sz E D n (p.1 : ℝ) ω ^ m * R n p)) :
    sz.Prec ξ (fun n p ω => R₀ n p + LemDecCalELip_Jsharp sz E D n (p.1 : ℝ) ω ^ m * R n p) := by
  obtain ⟨C₁, hC₁, hξ'⟩ := hξ
  obtain ⟨C₂, hC₂, hJ'⟩ := LemDecCalELip_Jsharp_rel sz E s t κ D hd hsize hκ hD hE hs ht htN
  set C : ℝ := max (max C₁ C₂) ((2 * k : ℕ) : ℝ) with hC
  have hC1 : C₁ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : C₂ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC3 : ((2 * k : ℕ) : ℝ) ≤ C := le_max_right _ _
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [ht n, hs n]
  refine LemDecCalELip_lift sz s t V ξ (fun n u ω => LemDecCalELip_Jsharp sz E D n u ω) R₀ R m Cv C
    CR hsize hst hlen hm hcard (fun n u ω => (LemDecCalELip_Jsharp_basic sz E D n u ω).1) hR₀ hRlow
    ?_ ?_ hPT
  · filter_upwards [htN, hRlow, hsize.eventually_ge_atTop 2] with n hN hRl hN2
    intro u u' v
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hΔ0 : 0 ≤ |(u : ℝ) - u'| := abs_nonneg _
    have hΔ1 : |(u : ℝ) - u'| ≤ 1 :=
      abs_le.2 ⟨by linarith [u.2.2, u'.2.2, ht n, u.2.1, u'.2.1, hs n],
        by linarith [u.2.2, u'.2.2, ht n, u.2.1, u'.2.1, hs n]⟩
    have hx0 : 0 ≤ Real.sqrt |(u : ℝ) - u'| := Real.sqrt_nonneg _
    have hx1 : Real.sqrt |(u : ℝ) - u'| ≤ 1 := by rw [Real.sqrt_le_one]; exact hΔ1
    have hΔx : |(u : ℝ) - u'| ≤ Real.sqrt |(u : ℝ) - u'| := by
      calc |(u : ℝ) - u'| = Real.sqrt |(u : ℝ) - u'| * Real.sqrt |(u : ℝ) - u'| :=
            (Real.mul_self_sqrt hΔ0).symm
        _ ≤ Real.sqrt |(u : ℝ) - u'| * 1 := by gcongr
        _ = Real.sqrt |(u : ℝ) - u'| := mul_one _
    have h1t : 0 < 1 - t n := by linarith [ht n]
    have hρ1 : 1 ≤ 1 + (1 - t n)⁻¹ * |(u : ℝ) - u'| := by
      have : 0 ≤ (1 - t n)⁻¹ * |(u : ℝ) - u'| := mul_nonneg (inv_nonneg.2 h1t.le) hΔ0
      linarith
    have hρ : 1 + (1 - t n)⁻¹ * |(u : ℝ) - u'| ≤ 1 + ((sz.size n : ℕ) : ℝ) * Real.sqrt |(u : ℝ) - u'| := by
      have : (1 - t n)⁻¹ * |(u : ℝ) - u'| ≤ ((sz.size n : ℕ) : ℝ) * Real.sqrt |(u : ℝ) - u'| :=
        mul_le_mul hN hΔx hΔ0 hN0.le
      linarith
    have hpow := lemDecCalEPrec_pow_rel k hN2 hx0 hx1 hρ1 hρ
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hexp : ((sz.size n : ℕ) : ℝ) ^ (2 * k) ≤ ((sz.size n : ℕ) : ℝ) ^ C := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by exact_mod_cast hC3)
    have hpow' : (1 + (1 - t n)⁻¹ * |(u : ℝ) - u'|) ^ k ≤
        1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - u'| :=
      hpow.trans (by nlinarith [mul_le_mul_of_nonneg_right hexp hx0])
    obtain ⟨h1, h2⟩ := hrel n u u' v
    have hR0 : 0 ≤ R n (u, v) := (Real.rpow_nonneg hN0.le _).trans (hRl _)
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hpow' (hR₀ n _)),
      h2.trans (mul_le_mul_of_nonneg_right hpow' hR0)⟩
  · filter_upwards [hξ', hJ', hsize.eventually_ge_atTop 1] with n hx hJ hN1
    intro ω hω u u'
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
    have hx0 : 0 ≤ Real.sqrt |(u : ℝ) - u'| := Real.sqrt_nonneg _
    refine ⟨fun v => (hx ω hω u u' v).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN1' hC1) hx0), ?_⟩
    have hJ1 : 0 ≤ LemDecCalELip_Jsharp sz E D n (u : ℝ) ω := by
      linarith [(LemDecCalELip_Jsharp_basic sz E D n (u : ℝ) ω).1]
    refine (hJ ω hω u u').trans (mul_le_mul_of_nonneg_right ?_ hJ1)
    have := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1' hC2) hx0
    linarith

end Lift

/-! ## 9. (C): from the realized control `J♯` to the given control `Jst` -/

section Combine

variable {d : ℕ}

/-- **(C) combine** (the amendment, step (C)): `Prec(ξ ≺ R₀ + J♯^m R)` and the hypothesis
`Prec(STLK2 ≺ Jst T)` (the union over `u` inside `P`) give `Prec(ξ ≺ R₀ + Jst^m R)`: on the complement of the
two failure events, `J♯(u) ≤ N^{τ'} Jst(u)` for every `u` at once (the third conjunct of
`LemDecCalELip_Jsharp_basic` at `X = N^{τ'} Jst ≥ 1`), `τ' = τ/(m+1)`. -/
theorem lemDecCalEPrec_combine (sz : Sizes d) (E s t : ℕ → ℝ) (hsize : sz.SizeTendsto)
    (Jst : ℕ → ℝ → ℝ → ℝ) (hJ1 : ∀ n u D, 1 ≤ Jst n u D) (D : ℝ) {U : ℕ → Type}
    (tm : ∀ n, U n → TimeIcc s t n) (ξ : ∀ n, U n → sz.SeqΩ → ℝ) (R₀ R : ∀ n, U n → ℝ) {m : ℝ}
    (hm : 0 ≤ m) (hR₀ : ∀ n p, 0 ≤ R₀ n p) (hR : ∀ n p, 0 ≤ R n p)
    (hLK : sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
      (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2))
    (h1 : sz.Prec ξ
      (fun n p ω => R₀ n p + LemDecCalELip_Jsharp sz E D n ((tm n p : TimeIcc s t n) : ℝ) ω ^ m * R n p)) :
    sz.Prec ξ (fun n p _ => R₀ n p + Jst n ((tm n p : TimeIcc s t n) : ℝ) D ^ m * R n p) := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsize) h1 hLK fun τ hτ =>
    ⟨τ / (m + 1), by positivity, Eventually.of_forall fun n => ?_⟩
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  by_contra hno
  simp only [Set.mem_union, not_or, badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  obtain ⟨hn1, hn2⟩ := hno
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set τ' : ℝ := τ / (m + 1) with hτ'
  have hτ'0 : 0 < τ' := by positivity
  set Q : ℝ := N ^ τ' with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hN1 hτ'0.le
  set u : TimeIcc s t n := tm n p with hu
  have hb := LemDecCalELip_Jsharp_basic sz E D n (u : ℝ) ω
  have hJ0 := hJ1 n (u : ℝ) D
  have hJX : LemDecCalELip_Jsharp sz E D n (u : ℝ) ω ≤ Q * Jst n (u : ℝ) D := by
    refine hb.2.2 (Q * Jst n (u : ℝ) D) (by nlinarith) fun σ a => ?_
    have := hn2 (u, σ, a)
    calc STLK2 sz n (E n) (u : ℝ) σ a ω ≤ Q * (Jst n (u : ℝ) D * STtailTD sz n (u : ℝ) D a) := this
      _ = Q * Jst n (u : ℝ) D * STtailTD sz n (u : ℝ) D a := by ring
  have hJ0' : 0 ≤ LemDecCalELip_Jsharp sz E D n (u : ℝ) ω := by linarith [hb.1]
  have hJm : LemDecCalELip_Jsharp sz E D n (u : ℝ) ω ^ m ≤ Q ^ m * Jst n (u : ℝ) D ^ m := by
    calc LemDecCalELip_Jsharp sz E D n (u : ℝ) ω ^ m ≤ (Q * Jst n (u : ℝ) D) ^ m :=
          Real.rpow_le_rpow hJ0' hJX hm
      _ = Q ^ m * Jst n (u : ℝ) D ^ m := Real.mul_rpow (by linarith) (by linarith)
  have hQm : 1 ≤ Q ^ m := Real.one_le_rpow hQ1 hm
  have hRp := hR n p
  have hR0p := hR₀ n p
  have hJst0 : 0 ≤ Jst n (u : ℝ) D ^ m := Real.rpow_nonneg (by linarith) _
  have hxi := hn1 p
  have hmain : R₀ n p + LemDecCalELip_Jsharp sz E D n (u : ℝ) ω ^ m * R n p ≤
      Q ^ m * (R₀ n p + Jst n (u : ℝ) D ^ m * R n p) := by
    have h2 : LemDecCalELip_Jsharp sz E D n (u : ℝ) ω ^ m * R n p ≤
        Q ^ m * Jst n (u : ℝ) D ^ m * R n p := mul_le_mul_of_nonneg_right hJm hRp
    nlinarith [mul_nonneg hR0p (sub_nonneg.2 hQm)]
  have hexp : N ^ τ = Q * Q ^ m := by
    rw [hQ, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    rw [hτ']
    field_simp
    ring
  have hfin : ξ n p ω ≤ N ^ τ * (R₀ n p + Jst n (u : ℝ) D ^ m * R n p) := by
    calc ξ n p ω ≤ Q * (R₀ n p + LemDecCalELip_Jsharp sz E D n (u : ℝ) ω ^ m * R n p) := hxi
      _ ≤ Q * (Q ^ m * (R₀ n p + Jst n (u : ℝ) D ^ m * R n p)) :=
          mul_le_mul_of_nonneg_left hmain (by linarith)
      _ = N ^ τ * (R₀ n p + Jst n (u : ℝ) D ^ m * R n p) := by rw [hexp]; ring
  exact absurd hp (not_lt.2 hfin)

end Combine

/-! ## 10. The floors and the relative continuity of the deterministic factors -/

section Factors

variable {d : ℕ}

/-- `T_{u,D}(r) ≥ W^{-D}` (the floor of the tail `tailTD`, as in the proof of `LemDecCalELip_Jsharp_rel`). -/
theorem lemDecCalEPrec_tail_ge (sz : Sizes d) (n : ℕ) (u D : ℝ) (a : Fin 2 → Zd d (sz.L n)) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ STtailTD sz n u D a := by
  unfold STtailTD tailTD
  have : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ 2 *
      Real.exp (-Real.sqrt ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) :=
    mul_nonneg (by positivity) (Real.exp_pos _).le
  linarith

/-- **The floors of the three factors**: for `0 ≤ u < 1`, `D ≥ 0`: `R₁, R₂, R₃ ≥ N^{-(1+2D)}`
(`(1-u)⁻¹ ≥ 1`, `(W^d |1-u|)⁻¹ ≥ N⁻¹`, `T ≥ W^{-D} ≥ N^{-D}`; `x^{1/2} ≥ x` for `x ≤ 1`). -/
theorem lemDecCalEPrec_floor (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) {u D : ℝ} (hD : 0 ≤ D)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Fin 2 → Zd d (sz.L n)) :
    ((sz.size n : ℕ) : ℝ) ^ (-(1 + 2 * D)) ≤ lemDecCalEPrec_R1 sz n D u a ∧
    ((sz.size n : ℕ) : ℝ) ^ (-(1 + 2 * D)) ≤ lemDecCalEPrec_R2 sz n D u a ∧
    ((sz.size n : ℕ) : ℝ) ^ (-(1 + 2 * D)) ≤ lemDecCalEPrec_R3 sz n D u a := by
  obtain ⟨hW, hL, hN, hWN, hN1⟩ := lemDecCalEPrec_sizes sz n hd
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hx : 0 < 1 - u := by linarith
  have hx1 : 1 - u ≤ 1 := by linarith
  have hWd : W ^ d ≤ N := by
    rw [hN]; exact pow_le_pow_left₀ hW0.le (by nlinarith) d
  have hWd0 : 0 < W ^ d := pow_pos hW0 d
  have h1 : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ hx).2 hx1
  have hX : N⁻¹ ≤ (W ^ d * |1 - u|)⁻¹ := by
    refine inv_anti₀ (by rw [abs_of_pos hx]; positivity) ?_
    rw [abs_of_pos hx]; nlinarith
  have hN1' : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have hX0 : 0 < N⁻¹ := inv_pos.2 hN0
  have hXh : N⁻¹ ≤ (W ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) := by
    calc N⁻¹ = (N⁻¹) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hX0 hN1' (by norm_num)
      _ ≤ (W ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hX0.le hX (by norm_num)
  have hT : N ^ (-D) ≤ STtailTD sz n u D a := by
    refine le_trans ?_ (lemDecCalEPrec_tail_ge sz n u D a)
    exact Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
  have hT0 : 0 ≤ N ^ (-D) := Real.rpow_nonneg hN0.le _
  have hND : N ^ (-(1 + 2 * D)) ≤ N⁻¹ * N ^ (-D) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hND2 : N ^ (-(1 + 2 * D)) ≤ N⁻¹ * (N ^ (-D)) ^ 2 := by
    refine le_of_eq ?_
    rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have hT2 : (N ^ (-D)) ^ 2 ≤ STtailTD sz n u D a ^ 2 := pow_le_pow_left₀ hT0 hT 2
  refine ⟨hND.trans ?_, hND.trans ?_, hND2.trans ?_⟩
  · unfold lemDecCalEPrec_R1
    calc N⁻¹ * N ^ (-D) = 1 * N⁻¹ * N ^ (-D) := by ring
      _ ≤ (1 - u)⁻¹ * (W ^ d * |1 - u|)⁻¹ * STtailTD sz n u D a :=
          mul_le_mul (mul_le_mul h1 hX hX0.le (by linarith)) hT hT0 (by positivity)
  · unfold lemDecCalEPrec_R2
    calc N⁻¹ * N ^ (-D) = 1 * N⁻¹ * N ^ (-D) := by ring
      _ ≤ (1 - u)⁻¹ * (W ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * STtailTD sz n u D a :=
          mul_le_mul (mul_le_mul h1 hXh hX0.le (by linarith)) hT hT0 (by positivity)
  · unfold lemDecCalEPrec_R3
    calc N⁻¹ * (N ^ (-D)) ^ 2 = 1 * N⁻¹ * (N ^ (-D)) ^ 2 := by ring
      _ ≤ (1 - u)⁻¹ * (W ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * STtailTD sz n u D a ^ 2 :=
          mul_le_mul (mul_le_mul h1 hXh hX0.le (by linarith)) hT2 (by positivity) (by positivity)

/-- **Relative continuity of the five deterministic factors** at the power `ρ^k` (`ρ = 1 + (1-t)⁻¹ |u-u'|`):
`R₁, R₂₀, R₂` by `ρ⁴`, `R₃₀, R₃` by `ρ⁶` (from `LemDecCalELip_relcont`; the indicators do not depend on `u`). -/
theorem lemDecCalEPrec_rel (sz : Sizes d) (n : ℕ) {t u u' D : ℝ} (a : Fin 2 → Zd d (sz.L n))
    (ht : t < 1) (hu : u ≤ t) (hu' : u' ≤ t) :
    lemDecCalEPrec_R1 sz n D u' a ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 4 * lemDecCalEPrec_R1 sz n D u a ∧
    lemDecCalEPrec_R2₀ sz n D u' a ≤
      (1 + (1 - t)⁻¹ * |u - u'|) ^ 4 * lemDecCalEPrec_R2₀ sz n D u a ∧
    lemDecCalEPrec_R2 sz n D u' a ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 4 * lemDecCalEPrec_R2 sz n D u a ∧
    lemDecCalEPrec_R3₀ sz n D u' a ≤
      (1 + (1 - t)⁻¹ * |u - u'|) ^ 6 * lemDecCalEPrec_R3₀ sz n D u a ∧
    lemDecCalEPrec_R3 sz n D u' a ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 6 * lemDecCalEPrec_R3 sz n D u a := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := LemDecCalELip_relcont sz n t u u' D a ht hu hu'
  have h1t : 0 < 1 - t := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hu'1 : 0 < 1 - u' := by linarith
  set ρ : ℝ := 1 + (1 - t)⁻¹ * |u - u'| with hρ
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ (1 - t)⁻¹ * |u - u'| := mul_nonneg (inv_nonneg.2 h1t.le) (abs_nonneg _)
    linarith
  have hρ0 : 0 < ρ := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hX : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by positivity
  have hX' : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ := by positivity
  have hXh : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX _
  have hXh' : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX' _
  have hT : 0 ≤ STtailTD sz n u D a := (LemDecCalELip_tail_pos sz n u D a).le
  have hT' : 0 ≤ STtailTD sz n u' D a := (LemDecCalELip_tail_pos sz n u' D a).le
  have hxi : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hu1.le
  have hxi' : 0 ≤ (1 - u')⁻¹ := inv_nonneg.2 hu'1.le
  have hind : ∀ r : ℝ, 0 ≤ (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ r then (1 : ℝ) else 0) := by
    intro r; split_ifs <;> norm_num
  have p2 : ρ ^ 2 ≤ ρ ^ 4 := pow_le_pow_right₀ hρ1 (by norm_num)
  have p3 : ρ ^ 3 ≤ ρ ^ 4 := pow_le_pow_right₀ hρ1 (by norm_num)
  have p4 : ρ ^ 4 ≤ ρ ^ 6 := pow_le_pow_right₀ hρ1 (by norm_num)
  have p5 : ρ ^ 5 ≤ ρ ^ 6 := pow_le_pow_right₀ hρ1 (by norm_num)
  have hρ2 : (0 : ℝ) ≤ ρ ^ 2 := by positivity
  have hρ4 : (0 : ℝ) ≤ ρ ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold lemDecCalEPrec_R1
    calc (1 - u')⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ * STtailTD sz n u' D a
        ≤ (ρ * (1 - u)⁻¹) * (ρ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹) *
            (ρ ^ 2 * STtailTD sz n u D a) :=
          mul_le_mul (mul_le_mul e1 e2 hX' (by positivity)) e4 hT' (by positivity)
      _ = ρ ^ 4 * ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * STtailTD sz n u D a) := by
          ring
  · unfold lemDecCalEPrec_R2₀
    set ind : ℝ := (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) with hindd
    have hi0 : 0 ≤ ind := hind _
    calc (1 - u')⁻¹ * ind * STtailTD sz n u' D a ≤ (ρ * (1 - u)⁻¹) * ind * (ρ ^ 2 * STtailTD sz n u D a) :=
          mul_le_mul (mul_le_mul_of_nonneg_right e1 hi0) e4 hT' (by positivity)
      _ = ρ ^ 3 * ((1 - u)⁻¹ * ind * STtailTD sz n u D a) := by ring
      _ ≤ ρ ^ 4 * ((1 - u)⁻¹ * ind * STtailTD sz n u D a) :=
          mul_le_mul_of_nonneg_right p3 (by positivity)
  · unfold lemDecCalEPrec_R2
    calc (1 - u')⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ (1 / 2 : ℝ) * STtailTD sz n u' D a
        ≤ (ρ * (1 - u)⁻¹) * (ρ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ)) *
            (ρ ^ 2 * STtailTD sz n u D a) :=
          mul_le_mul (mul_le_mul e1 e3 hXh' (by positivity)) e4 hT' (by positivity)
      _ = ρ ^ 4 * ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) *
            STtailTD sz n u D a) := by ring
  · unfold lemDecCalEPrec_R3₀
    set ind : ℝ := (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
      4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) with hindd
    have hi0 : 0 ≤ ind := hind _
    calc (1 - u')⁻¹ * ind * STtailTD sz n u' D a ^ 2
        ≤ (ρ * (1 - u)⁻¹) * ind * (ρ ^ 4 * STtailTD sz n u D a ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right e1 hi0) e5 (by positivity) (by positivity)
      _ = ρ ^ 5 * ((1 - u)⁻¹ * ind * STtailTD sz n u D a ^ 2) := by ring
      _ ≤ ρ ^ 6 * ((1 - u)⁻¹ * ind * STtailTD sz n u D a ^ 2) :=
          mul_le_mul_of_nonneg_right p5 (by positivity)
  · unfold lemDecCalEPrec_R3
    calc (1 - u')⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ (1 / 2 : ℝ) * STtailTD sz n u' D a ^ 2
        ≤ (ρ * (1 - u)⁻¹) * (ρ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ)) *
            (ρ ^ 4 * STtailTD sz n u D a ^ 2) :=
          mul_le_mul (mul_le_mul e1 e3 hXh' (by positivity)) e5 (by positivity) (by positivity)
      _ = ρ ^ 6 * ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) *
            STtailTD sz n u D a ^ 2) := by ring

/-- The indicator summands `R₂₀, R₃₀` are nonnegative (`u < 1`). -/
theorem lemDecCalEPrec_R0_nonneg (sz : Sizes d) (n : ℕ) {u : ℝ} (hu1 : u < 1) (D : ℝ)
    (a : Fin 2 → Zd d (sz.L n)) :
    0 ≤ lemDecCalEPrec_R2₀ sz n D u a ∧ 0 ≤ lemDecCalEPrec_R3₀ sz n D u a := by
  have hxi : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have hT : 0 ≤ STtailTD sz n u D a := (LemDecCalELip_tail_pos sz n u D a).le
  refine ⟨?_, ?_⟩
  · unfold lemDecCalEPrec_R2₀
    refine mul_nonneg (mul_nonneg hxi ?_) hT
    split_ifs <;> norm_num
  · unfold lemDecCalEPrec_R3₀
    refine mul_nonneg (mul_nonneg hxi ?_) (sq_nonneg _)
    split_ifs <;> norm_num

/-- `(1 - t_n)⁻¹ ≤ N` eventually in regime (iii): `lam² ≤ 1 - t` (`STReg5III`), `1 ≤ lam² W^d`
(`(eq:WO)`) and `W^d ≤ N`. -/
theorem lemDecCalEPrec_htN (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ}
    (hReg : STReg5III sz s t) (hd : 1 ≤ d) :
    ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [lemDecCalEPrec_numeric sz hA] with n hn
  obtain ⟨hl, hA1, -, hN1⟩ := hn
  obtain ⟨hW, hL, hN, hWN, -⟩ := lemDecCalEPrec_sizes sz n hd
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
  have hl2 : 0 < sz.lam n ^ 2 := by positivity
  have h1 : (1 - t n)⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hl2 (hReg n)
  have h2 : (sz.lam n ^ 2)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [inv_le_iff_one_le_mul₀' hl2]
    linarith
  have h3 : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hN]; exact pow_le_pow_left₀ hW0.le (by nlinarith) d
  exact h1.trans (h2.trans h3)

end Factors

/-! ## 11. The endpoint theorem -/

section Main

/-- **`lem_dec_calE` in the `Prec` form** (`stLemDecCalE_holds`, S5-09): the three bounds
`(res_deccalE_lk)`, `(res_deccalE_wG)`, `(res_deccalE_dif)` of `3_5:2317-2338`, uniformly in `u ∈ [s,t]`
(the union over `u` inside `P`), for the pin `STLemDecCalE` after DECISIONS §61, §63.  Route (d) of
DECISIONS §64: the deterministic `lemDecCalE_lk/_wG/_dif` are applied per time at the realized control
`J♯` (`lemDecCalEPrec_precPT`), the three conclusions are net-lifted (`lemDecCalEPrec_lift`, from
`LemDecCalELip_*`), and `J♯ ≤ N^{τ'} Jst` on the event of the hypothesis (`lemDecCalEPrec_combine`). -/
theorem stLemDecCalE_holds (d : ℕ) : STLemDecCalE d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg hKb hKw hLKs hDec hDecS hCon hStep1 hStep2 hLmax hLKU Jst
    hJ1 hJW D hD hfl hLK
  have hd1 : 1 ≤ d := by omega
  have hD0 : 0 ≤ D := hD.le
  obtain ⟨hA, hE, ht1, hR⟩ := v3_premises_of_stFlow sz hκ hε hflow htz
  have hsize : sz.SizeTendsto := hA.2.2.1
  have hE' : ∀ n, |STflowE z n| ≤ 2 - κ / 2 := fun n => (hE n).le
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hκ2 : 0 < κ / 2 := half_pos hκ
  have htN := lemDecCalEPrec_htN sz hA hReg hd1
  have hN4 : ∀ᶠ n in atTop, 4 ≤ ((sz.size n : ℕ) : ℝ) := hsize.eventually_ge_atTop 4
  obtain ⟨hPT1, hPT2, hPT3⟩ := lemDecCalEPrec_precPT hd sz z hκ hε hflow hs hst htz hReg hStep2.1
    hStep2.2.1 hLmax Jst hJ1 hJW hD hfl hLK
  have hu0 : ∀ n (u : TimeIcc s t n), 0 ≤ (u : ℝ) := fun n u => (hs n).trans u.2.1
  have hu1 : ∀ n (u : TimeIcc s t n), (u : ℝ) < 1 := fun n u => u.2.2.trans_lt (ht1 n)
  have hflo := fun n (u : TimeIcc s t n) a =>
    lemDecCalEPrec_floor sz hd1 n hD0 (hu0 n u) (hu1 n u) a
  refine ⟨?_, ?_, ?_⟩
  · -- `(res_deccalE_lk)`
    obtain ⟨C, hC0, hC⟩ :=
      LemDecCalELip_ELKLK sz (STflowE z) s t (κ / 2) hd hsize hκ2 hE' hs ht1 htN
    have h1 := lemDecCalEPrec_lift hd sz (STflowE z) s t hκ2 hD hsize hE' hs hst' ht1 htN
      (fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖STELKLK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      ⟨C, hC0, by
        filter_upwards [hC] with n hn ω hω u u' v
        exact (abs_norm_sub_norm_le _ _).trans (hn ω hω u u' v.1 v.2)⟩
      (fun n p => 0) (fun n p => lemDecCalEPrec_R1 sz n D (p.1 : ℝ) p.2.2) (m := 2) 4 3
      (1 + 2 * D) (by norm_num)
      (by filter_upwards [hN4] with n hn; exact lemDecCalEPrec_card_V12 sz n hn)
      (fun n p => le_rfl) (Eventually.of_forall fun n p => (hflo n p.1 p.2.2).1)
      (fun n u u' v => ⟨by simp, (lemDecCalEPrec_rel sz n v.2 (ht1 n) u.2.2 u'.2.2).1⟩) hPT1
    have h2 := lemDecCalEPrec_combine sz (STflowE z) s t hsize Jst hJ1 D
      (fun n (p : TimeIcc s t n × ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))) => p.1)
      (fun n p ω => ‖STELKLK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p => 0) (fun n p => lemDecCalEPrec_R1 sz n D (p.1 : ℝ) p.2.2) (m := 2) (by norm_num)
      (fun n p => le_rfl)
      (fun n p => (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (hflo n p.1 p.2.2).1) hLK h1
    convert h2 using 2
    funext p ω
    simp only [lemDecCalEPrec_R1, zero_add, Real.rpow_two]
    ring
  · -- `(res_deccalE_wG)`
    obtain ⟨C, hC0, hC⟩ := LemDecCalELip_EGt sz (STflowE z) s t (κ / 2) hd hsize hκ2 hE' hs ht1 htN
    have h1 := lemDecCalEPrec_lift hd sz (STflowE z) s t hκ2 hD hsize hE' hs hst' ht1 htN
      (fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖STEGt sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      ⟨C, hC0, by
        filter_upwards [hC] with n hn ω hω u u' v
        exact (abs_norm_sub_norm_le _ _).trans (hn ω hω u u' v.1 v.2)⟩
      (fun n p => lemDecCalEPrec_R2₀ sz n D (p.1 : ℝ) p.2.2)
      (fun n p => lemDecCalEPrec_R2 sz n D (p.1 : ℝ) p.2.2) (m := 3 / 2) 4 3 (1 + 2 * D)
      (by norm_num)
      (by filter_upwards [hN4] with n hn; exact lemDecCalEPrec_card_V12 sz n hn)
      (fun n p => (lemDecCalEPrec_R0_nonneg sz n (hu1 n p.1) D p.2.2).1)
      (Eventually.of_forall fun n p => (hflo n p.1 p.2.2).2.1)
      (fun n u u' v => ⟨(lemDecCalEPrec_rel sz n v.2 (ht1 n) u.2.2 u'.2.2).2.1,
        (lemDecCalEPrec_rel sz n v.2 (ht1 n) u.2.2 u'.2.2).2.2.1⟩) hPT2
    have h2 := lemDecCalEPrec_combine sz (STflowE z) s t hsize Jst hJ1 D
      (fun n (p : TimeIcc s t n × ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))) => p.1)
      (fun n p ω => ‖STEGt sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p => lemDecCalEPrec_R2₀ sz n D (p.1 : ℝ) p.2.2)
      (fun n p => lemDecCalEPrec_R2 sz n D (p.1 : ℝ) p.2.2) (m := 3 / 2) (by norm_num)
      (fun n p => (lemDecCalEPrec_R0_nonneg sz n (hu1 n p.1) D p.2.2).1)
      (fun n p => (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (hflo n p.1 p.2.2).2.1) hLK h1
    convert h2 using 2
    funext p ω
    simp only [lemDecCalEPrec_R2₀, lemDecCalEPrec_R2]
    ring
  · -- `(res_deccalE_dif)`
    obtain ⟨C, hC0, hC⟩ := LemDecCalELip_ee sz (STflowE z) s t (κ / 2) hd hsize hκ2 hE' hs ht1 htN
    have h1 := lemDecCalEPrec_lift hd sz (STflowE z) s t hκ2 hD hsize hE' hs hst' ht1 htN
      (lemDecCalEPrec_V3 sz)
      (fun n p ω => ‖STee sz n (STflowE z n) (p.1 : ℝ) ω p.2.1.1.1 p.2.1.1.2 p.2.1.2‖)
      ⟨C, hC0, by
        filter_upwards [hC] with n hn ω hω u u' v
        exact (abs_norm_sub_norm_le _ _).trans (hn ω hω u u' v.1.1.1 v.1.1.2 v.1.2)⟩
      (fun n p => lemDecCalEPrec_R3₀ sz n D (p.1 : ℝ) p.2.1.1.2)
      (fun n p => lemDecCalEPrec_R3 sz n D (p.1 : ℝ) p.2.1.1.2) (m := 3) 6 5 (1 + 2 * D)
      (by norm_num)
      (by filter_upwards [hN4] with n hn; exact lemDecCalEPrec_card_V3 sz n hn)
      (fun n p => (lemDecCalEPrec_R0_nonneg sz n (hu1 n p.1) D p.2.1.1.2).2)
      (Eventually.of_forall fun n p => (hflo n p.1 p.2.1.1.2).2.2)
      (fun n u u' v => ⟨(lemDecCalEPrec_rel sz n v.1.1.2 (ht1 n) u.2.2 u'.2.2).2.2.2.1,
        (lemDecCalEPrec_rel sz n v.1.1.2 (ht1 n) u.2.2 u'.2.2).2.2.2.2⟩) hPT3
    have h2 := lemDecCalEPrec_combine sz (STflowE z) s t hsize Jst hJ1 D
      (fun n (p : TimeIcc s t n × lemDecCalEPrec_V3 sz n) => p.1)
      (fun n p ω => ‖STee sz n (STflowE z n) (p.1 : ℝ) ω p.2.1.1.1 p.2.1.1.2 p.2.1.2‖)
      (fun n p => lemDecCalEPrec_R3₀ sz n D (p.1 : ℝ) p.2.1.1.2)
      (fun n p => lemDecCalEPrec_R3 sz n D (p.1 : ℝ) p.2.1.1.2) (m := 3) (by norm_num)
      (fun n p => (lemDecCalEPrec_R0_nonneg sz n (hu1 n p.1) D p.2.1.1.2).2)
      (fun n p => (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (hflo n p.1 p.2.1.1.2).2.2)
      hLK h1
    have h3 := StochDomAt.precomp_param h2
      (fun n (q : {q : STIdx2 sz s t n × (Fin 2 → Zd d (sz.L n)) //
          ∀ i : Fin 2, ((zdistInf d (sz.L n) (q.1.2.2 i - q.2 i) : ℕ) : ℝ) ≤
            Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)}) =>
        ((q.1.1.1 : TimeIcc s t n),
          (⟨((q.1.1.2.1, q.1.1.2.2), q.1.2), q.2⟩ : lemDecCalEPrec_V3 sz n)))
    unfold Prec
    convert h3 using 2
    funext q ω
    simp only [lemDecCalEPrec_R3₀, lemDecCalEPrec_R3]
    ring

end Main

/-! ## 12. Compiled nonempty instances at `d = 3`

The data are the merged preflight instance (`RBM3D/Induction/Step5Pins.lean:575-596`): the size sequence
`sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `N_n = (W_n L_n)^3`), the flow `z0`, `s = 0`, `t = 1/16`
(`sInst`, `tInst`), regime (iii) (`sz0_reg5III`); `D = 42`, `Jst ≡ 1`, `Cd = 1`. -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step5Inst

/-- The new floor of `STLemDecCalEConcl` at `sz0`, `D = 42`, for every `n`
(`L ≤ W`, `sz0_L_le_W`: `(L³ W^{18})² ≤ W⁴²`). -/
theorem lemDecCalEPrec_inst_floor (n : ℕ) :
    (((sz0.L n : ℕ) : ℝ) ^ 3 * ((sz0.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz0.W n : ℕ) : ℝ) ^ (42 : ℝ) := by
  have hLW : ((sz0.L n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by exact_mod_cast sz0_L_le_W n
  have hL0 : (0 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [show (42 : ℝ) = ((42 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (((sz0.L n : ℕ) : ℝ) ^ 3 * ((sz0.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2
      ≤ (((sz0.W n : ℕ) : ℝ) ^ 3 * ((sz0.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 := by
        gcongr
    _ = ((sz0.W n : ℕ) : ℝ) ^ 42 := by ring

/-- `Jst ≡ 1` meets both premises on `Jst` of the new pin at `sz0`: `1 ≤ 1` and `1 ≤ W^{1/2}`. -/
theorem lemDecCalEPrec_inst_Jst :
    (∀ (n : ℕ) (u D : ℝ), 1 ≤ (fun (_ : ℕ) (_ _ : ℝ) => (1 : ℝ)) n u D) ∧
    (∀ (n : ℕ) (u D : ℝ), (fun (_ : ℕ) (_ _ : ℝ) => (1 : ℝ)) n u D ≤
      ((sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) :=
  ⟨fun _ _ _ => le_rfl, fun n _ _ =>
    Real.one_le_rpow (by exact_mod_cast sz0.W_pos n) (by norm_num)⟩

/-- **`stLemDecCalE_holds` at the instance data** (the type `InstIng5Concl` of `inst_lemDecCalE`, at `Cd = 1`):
the constant `𝔠_d` and the conclusion `STLemDecCalEConcl` from the (stochastic, pin) hypotheses of
`STIngR5`, which stay hypotheses of the instance; every deterministic hypothesis (`3 ≤ 3`, the flow `z0`,
`0 ≤ s < t ≤ lemT`, the regime `sz0_reg5III`, `(con_st_ind)`) is discharged by the merged `inst_ing5_III`. -/
example := inst_lemDecCalE (stLemDecCalE_holds 3) 1 one_pos

/-- The conclusion `STLemDecCalEConcl` at the instance applied at concrete data: `Jst ≡ 1`, `D = 42` (both
new premises and the new floor discharged; the `Prec` hypothesis on `STLK2` stays a hypothesis). -/
example (h : STLemDecCalEConcl sz0 (STflowE z0) sInst tInst) :=
  h (fun _ _ _ => 1) lemDecCalEPrec_inst_Jst.1 lemDecCalEPrec_inst_Jst.2 42 (by norm_num)
    (Eventually.of_forall lemDecCalEPrec_inst_floor)

end Instances

end RBM.Gauss.Sizes
