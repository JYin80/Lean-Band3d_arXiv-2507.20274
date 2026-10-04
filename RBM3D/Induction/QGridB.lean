/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QGridA
import RBM3D.Induction.GridEnvelopeN

/-!
# The envelope of the `𝒬`-process remainder summed over the grid (`d ≥ 3`)

Ticket T2156 (S3-13b, stochastic layer ST-3).  Port of RBM2D `Induction/AltGridQ.lean` §10 at
commit `c9a24cf` (cited `AltGridQ:<line>`, `:1680-2262`).  Paper: arXiv:2507.20274, `3_5`
(`int_K-L+Q` `3_5:1337-1346`).

## Main result (namespace `RBM.Ind`)

* `sum_weighted_qErrQN_le` : on the grid `u_j = gridTime s t K n j` with `K n ≥ N^{C_K}`, the
  one-step remainders `qErrQN` of `gridDriftQN` at the envelope
  `B_{m+1} = N^{τ_K} η_{u_{j+1}}^{-(m+1)}`, weighted by `(1 + (1 - u_p)⁻¹)^{m+1}`, sum over `j <
  p` to at most `N^{-D_t}` for every
  `p ≤ K n`, eventually (RBM2D `sum_weighted_qErrQN_le`, `AltGridQ:2146`).

## Dictionary and `d ≥ 3` changes (CLAUDE.md §5.2)

`Z2 L ↦ Zd d L`; `d : Sizes ↦ sz : Sizes d`; tensors of `m + 1` indices, loop length `k = m + 1`
(RBM2D's `k`), `m ≥ 1`; `Lp = (L²)^{k-1} ↦ (L^d)^m ≤ N^m` (`L^d ≤ W^d L^d = N`); the sum length
is called `p` (the letter `m` is the tensor index); `W² L² = N ↦ W^d L^d = N`;
`spectralM ↦ mE`.  Paper-delta candidates:

* **T2156a** : the statement carries two fixed constants `0 ≤ C`, `0 ≤ C₂` (the sup bound of the
  mollifier and its second-order Taylor constant, the arguments of the merged `qStepErrN`),
  quantified before `∀ᶠ n`; RBM2D has none (`Lp` times the explicit constants of its `Θ`-product).
* **T2156b** : the decay exponent applied to the merged `sum_weighted_stepErrN_le` is
  `D_t + (m + 1)`, as in RBM2D (`D_t + k`), not `D_t + m`: the factor `1 + C Lp ≤ (1 + C) N^m` of
  `qStepErrN` costs `N^m`, and `(1 + C) N^m N^{-(D_t+m)} = (1+C) N^{-D_t}` cannot be `≤ N^{-D_t}/2`.
  The four rows of the statement are those of `SumWeightedStepErrN_Stmt` with `D_t + (m+1)` in
  place of `D_t`; the `Δ²`-part needs only `(m+1) + 2τ_K + (3(m+1)+2)(1-τ') + D_t < C_K`, which
  the second row implies.
* **T2156c** : no `STKbound` hypothesis: the sum theorem is deterministic (`STKbound` enters only
  through `gridDriftN_envelope`, at the consumer).  RBM2D has no pin for this statement.
* The statement has no `[NeZero k]` (as T2153b).

Every unpinned helper is `private` with the prefix `qGridB_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Path
open RBM.Gauss.Sizes
open scoped NNReal ENNReal

/-! ## 1. Grid and size helpers -/

section Helpers

private theorem qGridB_gridStep_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem qGridB_gridTime_le {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n)
    (hK0 : K n ≠ 0) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j ≤ t n := by
  have hΔ := qGridB_gridStep_nonneg (s := s) (t := t) (K := K) hst
  have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_right hj' hΔ
  have hlast := gridTime_last s t K n hK0
  unfold gridTime at hlast ⊢
  nlinarith

private theorem qGridB_one_le_size {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have : 1 ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega))
  exact_mod_cast this

private theorem qGridB_size_cast {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

/-- The grid-time facts: `Δ ≥ 0`, `u_j ≥ 0`, `u_{j+1} = u_j + Δ` (copy of the private
`QGridA_time_facts`, `QGridA.lean:507`). -/
private theorem qGridB_time_facts (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (hK : K n ≠ 0) :
    0 ≤ gridStep s t K n ∧ 0 ≤ gridTime s t K n j ∧
      gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) hKpos.le
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  refine ⟨hΔ, add_nonneg hs0 (mul_nonneg hj0 hΔ), ?_⟩
  unfold gridTime; push_cast; ring

end Helpers

/-! ## 2. The one-step `Δ²`-part -/

section Step

/-- `(1 + x)^k - 1 - k x ≤ k 2^k x²` for `0 ≤ x ≤ 1` (copy of the private `gridEnv_binom_rem`). -/
private theorem qGridB_binom_rem (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k - 1 - (k : ℝ) * x ≤ (k : ℝ) * 2 ^ k * x ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (1 + x) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * x =
        (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) + (k : ℝ) * x ^ 2 := by
      push_cast; ring
    rw [e]
    have hk2 : (k : ℝ) ≤ 2 ^ k := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hpk : (0 : ℝ) ≤ 2 ^ k := by positivity
    have h1 : (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) ≤
        (1 + x) * ((k : ℝ) * 2 ^ k * x ^ 2) := mul_le_mul_of_nonneg_left ih (by linarith)
    have hb : 0 ≤ (k : ℝ) * 2 ^ k * x ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_right hx1 hb
    have h3 := mul_le_mul_of_nonneg_right hk2 hx2
    have h4 := mul_nonneg hpk hx2
    push_cast
    rw [pow_succ (2 : ℝ) k]
    nlinarith [h1, h2, h3, h4]

private theorem qGridB_uStepC_nonneg (k : ℕ) {Δ v : ℝ} (hΔ0 : 0 ≤ Δ) (hv1 : 0 < 1 - v) :
    0 ≤ uStepC k Δ v := by
  unfold uStepC
  have hβ0 : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 hv1.le
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 hβ0
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * (1 - v)⁻¹ by linarith) k
  have e1 : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
  linarith [hb, e1]

/-- `uStepC k Δ v ≤ (k + k 2^k) H² Δ²` for `(1-v)⁻¹ ≤ H`, `Δ H ≤ 1` (the bound `hU` inside the
private `gridEnv_stepErr_le`). -/
private theorem qGridB_uStepC_le (k : ℕ) {Δ v H : ℝ} (hΔ0 : 0 ≤ Δ) (hv1 : 0 < 1 - v)
    (hv : (1 - v)⁻¹ ≤ H) (hΔH : Δ * H ≤ 1) :
    uStepC k Δ v ≤ ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2 := by
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 (inv_nonneg.2 hv1.le)
  have hxH : Δ * (1 - v)⁻¹ ≤ Δ * H := mul_le_mul_of_nonneg_left hv hΔ0
  have hx1 : Δ * (1 - v)⁻¹ ≤ 1 := hxH.trans hΔH
  have hrem := qGridB_binom_rem (Δ * (1 - v)⁻¹) hx0 hx1 k
  have hx2 : (Δ * (1 - v)⁻¹) ^ 2 ≤ Δ ^ 2 * H ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx0 hxH 2 |>.trans (by rw [mul_pow])
  have hiv2 : (1 - v)⁻¹ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hv1.le) hv 2
  unfold uStepC
  have e1 : (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 ≤ (k : ℝ) * Δ ^ 2 * H ^ 2 :=
    mul_le_mul_of_nonneg_left hiv2 (by positivity)
  have e2 : (k : ℝ) * 2 ^ k * (Δ * (1 - v)⁻¹) ^ 2 ≤ (k : ℝ) * 2 ^ k * (Δ ^ 2 * H ^ 2) :=
    mul_le_mul_of_nonneg_left hx2 (by positivity)
  linarith [hrem, e1, e2]

/-- The `(1 + C Lp) S` part of `qStepErrN` and its `Δ²` part (RBM2D `AltGridQ_qStepErrN_split`). -/
private theorem qGridB_qStepErrN_split (d L m : ℕ) (C C₂ u Δ Mk Dm S : ℝ) :
    qStepErrN d L m C C₂ u Δ Mk Dm S =
      (1 + C * ((L : ℝ) ^ d) ^ m) * S + qStepErrN d L m C C₂ u Δ Mk Dm 0 := by
  unfold qStepErrN
  ring

/-- The coefficient of the `Δ²`-part, `k = m + 1`:
`C (10 k³ + 4 (k + k 2^k) + 2 k) + 2 C₂` (derived from the four terms of `qStepErrN`). -/
private def qGridB_aQ (C C₂ : ℝ) (k : ℕ) : ℝ :=
  C * (10 * (k : ℝ) ^ 3 + 4 * ((k : ℝ) + (k : ℝ) * 2 ^ k) + 2 * (k : ℝ)) + 2 * C₂

private theorem qGridB_aQ_nonneg {C C₂ : ℝ} (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (k : ℕ) :
    0 ≤ qGridB_aQ C C₂ k := by
  unfold qGridB_aQ; positivity

/-- **The `Δ²`-part of `qStepErrN`, for `S = 0`** (per step), `k = m + 1`: with `N = W^d L^d`,
`H ≥ (1-v)⁻¹`, `H/c ≥ η_u⁻¹, η_v⁻¹`, `Y ≥ 1`, `Δ H ≤ 1`, the envelope `Bk = Y η_v^{-k}`:
`qStepErrN … 0 ≤ Δ² a_Q N^k (Y (H/c)^k)² H²` (RBM2D `AltGridQ_extra_le`, `AltGridQ:1739`). -/
private theorem qGridB_extra_le (d L W : ℕ) (E : ℝ) (m k : ℕ) (hk : k = m + 1) (hm : 1 ≤ m)
    (C C₂ u Δ N H Y c : ℝ) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hu0 : 0 ≤ u) (hN1 : 1 ≤ N)
    (hWL : (W : ℝ) ^ d * (L : ℝ) ^ d = N) (hW : (1 : ℝ) ≤ W) (hL1 : (1 : ℝ) ≤ L)
    (hH : 1 ≤ H) (hY : 1 ≤ Y) (hc0 : 0 < c) (hc1 : c ≤ 1) (hΔ0 : 0 ≤ Δ) (hΔH : Δ * H ≤ 1)
    (hηu0 : 0 < etaT E u) (hηv0 : 0 < etaT E (u + Δ)) (hηu : (etaT E u)⁻¹ ≤ H / c)
    (hηv : (etaT E (u + Δ))⁻¹ ≤ H / c) (hv1 : 0 < 1 - (u + Δ)) (hv : (1 - (u + Δ))⁻¹ ≤ H) :
    qStepErrN d L m C C₂ u Δ (lkEnvN d W E k u (Y * (etaT E (u + Δ))⁻¹ ^ k))
        (driftEnvN d L W E k u (Y * (etaT E (u + Δ))⁻¹ ^ k)) 0 ≤
      Δ ^ 2 * (qGridB_aQ C C₂ k * N ^ k * (Y * (H / c) ^ k) ^ 2 * H ^ 2) := by
  set Bk : ℝ := Y * (etaT E (u + Δ))⁻¹ ^ k with hBk
  set P : ℝ := (H / c) ^ k with hP
  set Q : ℝ := Y * P with hQ
  have hHc : 1 ≤ H / c := by rw [le_div_iff₀ hc0]; linarith
  have hP1 : 1 ≤ P := one_le_pow₀ hHc
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hY hP1
  have hPQ : P ≤ Q := le_mul_of_one_le_left (by linarith) hY
  have hη' : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu0.le
  have hηv' : 0 ≤ (etaT E (u + Δ))⁻¹ := inv_nonneg.2 hηv0.le
  have hBk0 : 0 ≤ Bk := by rw [hBk]; positivity
  have hBkQ : Bk ≤ Q :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hηv' hηv k) (by linarith)
  have hηuP : (etaT E u)⁻¹ ^ k ≤ P := pow_le_pow_left₀ hη' hηu k
  have hWi : (((W : ℝ) ^ d)⁻¹) ^ (k - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW))
  have hkR : (2 : ℝ) ≤ k := by rw [hk]; push_cast; have : (1 : ℝ) ≤ m := by exact_mod_cast hm
                               linarith
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hN0 : 0 ≤ N := by linarith
  -- the sup bounds
  have hMk0 : 0 ≤ lkEnvN d W E k u Bk := by unfold lkEnvN; positivity
  have hMk : lkEnvN d W E k u Bk ≤ 2 * Q := by
    unfold lkEnvN
    have h1 : (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) ≤ P :=
      (mul_le_of_le_one_right (by positivity) hWi).trans hηuP
    linarith
  have hBF : (etaT E u)⁻¹ ^ k + Bk ≤ 2 * Q := by linarith
  have hBF0 : 0 ≤ (etaT E u)⁻¹ ^ k + Bk := by positivity
  have hDm : driftEnvN d L W E k u Bk ≤ 10 * (k : ℝ) ^ 3 * N * Q ^ 2 := by
    unfold driftEnvN
    rw [hWL]
    have hη2 : (etaT E u)⁻¹ + 1 ≤ 2 * (H / c) := by linarith
    have h3 : (etaT E u)⁻¹ ^ (k + 1) ≤ (H / c) ^ (k + 1) := pow_le_pow_left₀ hη' hηu _
    have h4 : ((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1) ≤ 2 * (H / c) * (H / c) ^ (k + 1) :=
      mul_le_mul hη2 h3 (by positivity) (by positivity)
    have h5 : (H / c) ^ (k + 2) ≤ P ^ 2 := by
      rw [hP, ← pow_mul']
      exact pow_le_pow_right₀ hHc (by omega)
    have h6 : 2 * (H / c) * (H / c) ^ (k + 1) ≤ 2 * Q ^ 2 := by
      have : 2 * (H / c) * (H / c) ^ (k + 1) = 2 * (H / c) ^ (k + 2) := by ring
      rw [this]
      have hP2 : P ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by linarith) hPQ 2
      linarith
    have t1 : (k : ℝ) * (2 * (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * Bk)) ≤
        4 * (k : ℝ) ^ 3 * Q ^ 2 := by
      have : ((etaT E u)⁻¹ ^ k + Bk) * Bk ≤ (2 * Q) * Q :=
        mul_le_mul hBF hBkQ hBk0 (by linarith)
      calc (k : ℝ) * (2 * (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * Bk))
          ≤ (k : ℝ) * (2 * (k : ℝ) ^ 2 * ((2 * Q) * Q)) := by gcongr
        _ = 4 * (k : ℝ) ^ 3 * Q ^ 2 := by ring
    have t2 : (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk)) ≤
        4 * (k : ℝ) ^ 2 * Q ^ 2 := by
      have : ((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk) ≤ (2 * Q) * (2 * Q) :=
        mul_le_mul hBF hBF hBF0 (by linarith)
      calc (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk))
          ≤ (k : ℝ) ^ 2 * ((2 * Q) * (2 * Q)) := by gcongr
        _ = 4 * (k : ℝ) ^ 2 * Q ^ 2 := by ring
    have t3 : (k : ℝ) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) ≤ 2 * (k : ℝ) * Q ^ 2 := by
      calc (k : ℝ) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1))
          ≤ (k : ℝ) * (2 * Q ^ 2) := mul_le_mul_of_nonneg_left (h4.trans h6) hk0
        _ = 2 * (k : ℝ) * Q ^ 2 := by ring
    have hk1R : (1 : ℝ) ≤ k := by linarith
    have hk2 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hk1R (by norm_num)
    have hk1 : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
      calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hk1R (by norm_num)
    have hQ2 : 0 ≤ Q ^ 2 := by positivity
    calc N * ((k : ℝ) * (2 * (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * Bk)) +
          (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk)) +
          (k : ℝ) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)))
        ≤ N * (4 * (k : ℝ) ^ 3 * Q ^ 2 + 4 * (k : ℝ) ^ 2 * Q ^ 2 + 2 * (k : ℝ) * Q ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [t1, t2, t3]) hN0
      _ ≤ N * (10 * (k : ℝ) ^ 3 * Q ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hN0
          have e2 := mul_le_mul_of_nonneg_right hk2 hQ2
          have e1 := mul_le_mul_of_nonneg_right hk1 hQ2
          linarith [e1, e2]
      _ = 10 * (k : ℝ) ^ 3 * N * Q ^ 2 := by ring
  -- the pieces of `qStepErrN`
  have hLp1 : 1 ≤ ((L : ℝ) ^ d) ^ m := one_le_pow₀ (one_le_pow₀ hL1)
  have hL2N : (L : ℝ) ^ d ≤ N := by
    calc (L : ℝ) ^ d = 1 * (L : ℝ) ^ d := (one_mul _).symm
      _ ≤ (W : ℝ) ^ d * (L : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hW) (by positivity)
      _ = N := hWL
  have hLpN : ((L : ℝ) ^ d) ^ m ≤ N ^ m := pow_le_pow_left₀ (by positivity) hL2N _
  set M1 : ℝ := N ^ m with hM1
  have hM1N : M1 * N = N ^ k := by
    rw [hM1, ← pow_succ, hk]
  have hM10 : 0 ≤ M1 := by positivity
  have hM1le : M1 ≤ N ^ k := by
    rw [hM1]; exact pow_le_pow_right₀ hN1 (by omega)
  have hβ0 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.2 hv1.le
  have hUst := qGridB_uStepC_le k hΔ0 hv1 hv hΔH
  have hUst0 : 0 ≤ uStepC k Δ (u + Δ) := qGridB_uStepC_nonneg k hΔ0 hv1
  have hCβΔ : C * (1 - (u + Δ))⁻¹ * Δ ≤ C * H * Δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC) hΔ0
  have hCβΔ0 : 0 ≤ C * (1 - (u + Δ))⁻¹ * Δ := by positivity
  have hτB : C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2 ≤ C₂ * H ^ 2 * Δ ^ 2 := by
    have hiv2 : ((1 - (u + Δ))⁻¹) ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hβ0 hv 2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hiv2 hC₂) (by positivity)
  have hτB0 : 0 ≤ C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2 := by positivity
  -- the four terms
  set Lp : ℝ := ((L : ℝ) ^ d) ^ m with hLp
  have hLp0 : 0 ≤ Lp := by linarith
  have hDm0 : 0 ≤ driftEnvN d L W E k u Bk := by unfold driftEnvN; positivity
  have Ta : Δ * (Lp * driftEnvN d L W E k u Bk) * (C * (1 - (u + Δ))⁻¹ * Δ) ≤
      10 * C * (k : ℝ) ^ 3 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H)) := by
    calc Δ * (Lp * driftEnvN d L W E k u Bk) * (C * (1 - (u + Δ))⁻¹ * Δ)
        ≤ Δ * (M1 * (10 * (k : ℝ) ^ 3 * N * Q ^ 2)) * (C * H * Δ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hLpN hDm hDm0 hM10) hΔ0) hCβΔ hCβΔ0
            (by positivity)
      _ = 10 * C * (k : ℝ) ^ 3 * (Δ ^ 2 * ((M1 * N) * Q ^ 2 * H)) := by ring
      _ = 10 * C * (k : ℝ) ^ 3 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H)) := by rw [hM1N]
  have Tb : 2 * (C * (Lp * (uStepC k Δ (u + Δ) * lkEnvN d W E k u Bk))) ≤
      4 * C * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by
    calc 2 * (C * (Lp * (uStepC k Δ (u + Δ) * lkEnvN d W E k u Bk)))
        ≤ 2 * (C * (M1 * ((((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2) * (2 * Q)))) := by
          gcongr
      _ = 4 * C * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by ring
  have Tc : Lp * lkEnvN d W E k u Bk * (C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2) ≤
      2 * C₂ * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by
    calc Lp * lkEnvN d W E k u Bk * (C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2)
        ≤ M1 * (2 * Q) * (C₂ * H ^ 2 * Δ ^ 2) :=
          mul_le_mul (mul_le_mul hLpN hMk hMk0 hM10) hτB hτB0 (by positivity)
      _ = 2 * C₂ * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by ring
  have Td : Δ * (Lp * (((m : ℝ) + 1) * (1 - (u + Δ))⁻¹ * lkEnvN d W E k u Bk)) *
      (C * (1 - (u + Δ))⁻¹ * Δ) ≤
      2 * C * (k : ℝ) * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by
    have hmk1 : (m : ℝ) + 1 = k := by rw [hk]; push_cast; ring
    rw [hmk1]
    have hkβ : (k : ℝ) * (1 - (u + Δ))⁻¹ * lkEnvN d W E k u Bk ≤ (k : ℝ) * H * (2 * Q) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hv hk0) hMk hMk0 (by positivity)
    have hkβ0 : 0 ≤ (k : ℝ) * (1 - (u + Δ))⁻¹ * lkEnvN d W E k u Bk := by positivity
    calc Δ * (Lp * ((k : ℝ) * (1 - (u + Δ))⁻¹ * lkEnvN d W E k u Bk)) *
          (C * (1 - (u + Δ))⁻¹ * Δ)
        ≤ Δ * (M1 * ((k : ℝ) * H * (2 * Q))) * (C * H * Δ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hLpN hkβ hkβ0 hM10) hΔ0) hCβΔ hCβΔ0
            (by positivity)
      _ = 2 * C * (k : ℝ) * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by ring
  -- assemble
  have hH2 : H ≤ H ^ 2 := le_self_pow₀ hH (by norm_num)
  have hMQ : M1 * Q ≤ N ^ k * Q ^ 2 :=
    mul_le_mul hM1le (le_self_pow₀ hQ1 (by norm_num)) (by linarith) (by positivity)
  have hNQH : N ^ k * Q ^ 2 * H ≤ N ^ k * Q ^ 2 * H ^ 2 :=
    mul_le_mul_of_nonneg_left hH2 (by positivity)
  have hMQH : M1 * Q * H ^ 2 ≤ N ^ k * Q ^ 2 * H ^ 2 :=
    mul_le_mul_of_nonneg_right hMQ (by positivity)
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have hkk : 0 ≤ (k : ℝ) + (k : ℝ) * 2 ^ k := by positivity
  have Ta' : 10 * C * (k : ℝ) ^ 3 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H)) ≤
      10 * C * (k : ℝ) ^ 3 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by gcongr
  have Tb' : 4 * C * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (M1 * Q * H ^ 2)) ≤
      4 * C * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by gcongr
  have Tc' : 2 * C₂ * (Δ ^ 2 * (M1 * Q * H ^ 2)) ≤
      2 * C₂ * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by gcongr
  have Td' : 2 * C * (k : ℝ) * (Δ ^ 2 * (M1 * Q * H ^ 2)) ≤
      2 * C * (k : ℝ) * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by gcongr
  have hgoal : qStepErrN d L m C C₂ u Δ (lkEnvN d W E k u Bk) (driftEnvN d L W E k u Bk) 0 =
      Δ * (Lp * driftEnvN d L W E k u Bk) * (C * (1 - (u + Δ))⁻¹ * Δ) +
        2 * (C * (Lp * (uStepC k Δ (u + Δ) * lkEnvN d W E k u Bk))) +
        Lp * lkEnvN d W E k u Bk * (C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2) +
        Δ * (Lp * (((m : ℝ) + 1) * (1 - (u + Δ))⁻¹ * lkEnvN d W E k u Bk)) *
          (C * (1 - (u + Δ))⁻¹ * Δ) := by
    unfold qStepErrN
    rw [← hk]
    ring
  rw [hgoal]
  have hfin : Δ ^ 2 * (qGridB_aQ C C₂ k * N ^ k * Q ^ 2 * H ^ 2) =
      10 * C * (k : ℝ) ^ 3 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        4 * C * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        2 * C₂ * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        2 * C * (k : ℝ) * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by
    unfold qGridB_aQ; ring
  rw [hQ] at hfin
  rw [hQ] at Ta Tb Tc Td Ta' Tb' Tc' Td' ⊢
  rw [hfin]
  linarith [Ta, Ta', Tb, Tb', Tc, Tc', Td, Td']

end Step

/-! ## 3. The summed envelope -/

section Sum

/-- `N^a (N^θ)^p (N^τ)^q N^b = N^{a + θ p + τ q + b}` (copy of the private `gridEnv_mono`). -/
private theorem qGridB_mono (N : ℝ) (hN : 0 < N) (a : ℕ) (θ : ℝ) (p : ℕ) (τ : ℝ) (q : ℕ)
    (b : ℝ) :
    N ^ a * (N ^ θ) ^ p * (N ^ τ) ^ q * N ^ b = N ^ ((a : ℝ) + θ * p + τ * q + b) := by
  rw [← Real.rpow_natCast N a, ← Real.rpow_natCast (N ^ θ) p, ← Real.rpow_natCast (N ^ τ) q,
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN, ← Real.rpow_add hN,
    ← Real.rpow_add hN]

/-- `A N^e ≤ N^f` eventually, for `e < f` (copy of the private `gridEnv_eventually_le`). -/
private theorem qGridB_eventually_le {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto)
    (A e f : ℝ) (hef : e < f) :
    ∀ᶠ n : ℕ in atTop, A * ((sz.size n : ℕ) : ℝ) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ f := by
  have hT : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ) ^ (f - e)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hef)).comp hsize
  filter_upwards [hT.eventually_ge_atTop A, hsize.eventually_ge_atTop 1] with n hA hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  calc A * ((sz.size n : ℕ) : ℝ) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ (f - e) * ((sz.size n : ℕ) : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hN0.le _)
    _ = ((sz.size n : ℕ) : ℝ) ^ f := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- A uniform lower bound `0 < c ≤ 1`, `c ≤ Im m(E n)` in the bulk (copy of the private
`gridEnv_exists_c`). -/
private theorem qGridB_exists_c {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n, c ≤ (mE (E n)).im := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  refine ⟨min (Real.sqrt (2 * κ) / 2) 1, lt_min (by have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ); linarith) one_pos, min_le_right _ _, fun n => ?_⟩
  rw [mE_im]
  refine (min_le_left _ _).trans ?_
  have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
    have := abs_le.1 (hE n)
    nlinarith
  have h2 : 2 * κ ≤ 4 - E n ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

/-- **The `Δ²`-part summed over the grid**, at a fixed size index (per-step bound
`qGridB_extra_le`, `p Δ² ≤ K Δ² ≤ N^{-C_K}`, weight `≤ (2H)^k`), as one `N`-monomial:
`≤ 2^k a_Q c^{-2k} N^k H^{3k+2} Y² N^{-C_K}`, `H = N^{1-τ'}`, `Y = N^{τ_K}`, `c ≤ Im m(E n)`
(RBM2D `AltGridQ_extra_sum_le`, `AltGridQ:1951`). -/
private theorem qGridB_extra_sum_le {d : ℕ} (sz : Sizes d) {τ' τK C_K C C₂ : ℝ} {E s t : ℕ → ℝ}
    {K : ℕ → ℕ} (m k : ℕ) (hk : k = m + 1) (hm : 1 ≤ m) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (c : ℝ) (n : ℕ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcE : c ≤ (mE (E n)).im) (hτK : 0 < τK) (hτ'1 : τ' ≤ 1) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK0 : K n ≠ 0)
    (hR : ((sz.size n : ℕ) : ℝ) ^ (-1 + τ') ≤ 1 - t n)
    (hKn : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (h4 : 1 - τ' ≤ C_K) (p : ℕ) (hp : p ≤ K n) :
    ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ k *
        qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) (gridStep s t K n)
          (lkEnvN d (sz.W n) (E n) k (gridTime s t K n j)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
          (driftEnvN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0 ≤
      2 ^ k * qGridB_aQ C C₂ k * (c⁻¹) ^ (2 * k) *
        (((sz.size n : ℕ) : ℝ) ^ k * (((sz.size n : ℕ) : ℝ) ^ (1 - τ')) ^ (3 * k + 2) *
          (((sz.size n : ℕ) : ℝ) ^ τK) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ (-C_K)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := qGridB_one_le_size sz n
  have hN0 : 0 < N := by linarith
  set θ : ℝ := 1 - τ' with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  set H : ℝ := N ^ θ with hHdef
  set Y : ℝ := N ^ τK with hYdef
  have hH1 : 1 ≤ H := Real.one_le_rpow hN1 hθ0
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1 hτK.le
  have hH0 : 0 < H := by linarith
  have hHinv : H⁻¹ ≤ 1 - t n := by
    rw [hHdef, ← Real.rpow_neg hN0.le]
    have e : -θ = -1 + τ' := by rw [hθ]; ring
    rw [e]; exact hR
  have hinv : ∀ x, x ≤ t n → 0 < 1 - x ∧ (1 - x)⁻¹ ≤ H := fun x hx => by
    have h1 : H⁻¹ ≤ 1 - x := hHinv.trans (by linarith)
    have h1x : 0 < 1 - x := lt_of_lt_of_le (inv_pos.2 hH0) h1
    exact ⟨h1x, (inv_le_comm₀ h1x hH0).2 h1⟩
  have hη : ∀ x, x ≤ t n → 0 < etaT (E n) x ∧ (etaT (E n) x)⁻¹ ≤ H / c := fun x hx => by
    obtain ⟨h1x, hxH⟩ := hinv x hx
    have hpos : 0 < etaT (E n) x := etaT_pos hE (by linarith [ht1])
    refine ⟨hpos, ?_⟩
    have hle : (1 - x) * c ≤ etaT (E n) x := by
      unfold etaT; exact mul_le_mul_of_nonneg_left hcE h1x.le
    calc (etaT (E n) x)⁻¹ ≤ ((1 - x) * c)⁻¹ := inv_anti₀ (mul_pos h1x hc0) hle
      _ = (1 - x)⁻¹ * c⁻¹ := mul_inv _ _
      _ ≤ H * c⁻¹ := mul_le_mul_of_nonneg_right hxH (inv_nonneg.2 hc0.le)
      _ = H / c := (div_eq_mul_inv H c).symm
  -- the grid
  set Δ : ℝ := gridStep s t K n with hΔdef
  have hKpos : (0 : ℝ) < (K n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK0)
  have hΔ0 : 0 ≤ Δ := qGridB_gridStep_nonneg (K := K) hst
  have hKΔ : (K n : ℝ) * Δ = t n - s n := by
    rw [hΔdef]; unfold gridStep; field_simp
  have hKΔ1 : (K n : ℝ) * Δ ≤ 1 := by rw [hKΔ]; linarith
  have hNC : 0 < N ^ C_K := Real.rpow_pos_of_pos hN0 _
  have hΔD : Δ ≤ N ^ (-C_K) := by
    have h1 : Δ ≤ 1 / (K n : ℝ) := by
      rw [hΔdef]; unfold gridStep
      exact div_le_div_of_nonneg_right (by linarith) hKpos.le
    calc Δ ≤ 1 / (K n : ℝ) := h1
      _ ≤ 1 / N ^ C_K := one_div_le_one_div_of_le hNC hKn
      _ = N ^ (-C_K) := by rw [Real.rpow_neg hN0.le, one_div]
  have hΔH : Δ * H ≤ 1 := by
    calc Δ * H ≤ N ^ (-C_K) * N ^ θ := mul_le_mul hΔD le_rfl hH0.le (Real.rpow_nonneg hN0.le _)
      _ = N ^ (-C_K + θ) := (Real.rpow_add hN0 _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hWL : (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = N := qGridB_size_cast sz n
  have hW : (1 : ℝ) ≤ sz.W n := by exact_mod_cast sz.W_pos n
  have hL1 : (1 : ℝ) ≤ sz.L n := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 1 ≤ sz.L n)
  -- the per-step bound
  have hstep : ∀ j < K n,
      qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) Δ
        (lkEnvN d (sz.W n) (E n) k (gridTime s t K n j) (N ^ τK *
          (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
        (driftEnvN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (N ^ τK *
          (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0 ≤
      Δ ^ 2 * (qGridB_aQ C C₂ k * N ^ k * (Y * (H / c) ^ k) ^ 2 * H ^ 2) := by
    intro j hj
    obtain ⟨_, hu0, hvu⟩ := qGridB_time_facts s t K n j hs0 hst hK0
    have hu : gridTime s t K n j ≤ t n := qGridB_gridTime_le (K := K) hst hK0 hj.le
    have hv : gridTime s t K n (j + 1) ≤ t n := qGridB_gridTime_le (K := K) hst hK0 hj
    obtain ⟨hv1, hvH⟩ := hinv _ hv
    obtain ⟨hηu0, hηu⟩ := hη _ hu
    obtain ⟨hηv0, hηv⟩ := hη _ hv
    rw [hvu] at hv1 hvH hηv0 hηv ⊢
    exact qGridB_extra_le d (sz.L n) (sz.W n) (E n) m k hk hm C C₂ (gridTime s t K n j) Δ N H Y c
      hC hC₂ hu0 hN1 hWL hW hL1 hH1 hY1 hc0 hc1 hΔ0 hΔH hηu0 hηv0 hηu hηv hv1 hvH
  -- the weight
  have hum : gridTime s t K n p ≤ t n := qGridB_gridTime_le (K := K) hst hK0 hp
  obtain ⟨hum1, hwH⟩ := hinv _ hum
  have hinv0 : 0 ≤ (1 - gridTime s t K n p)⁻¹ := inv_nonneg.2 hum1.le
  have hw0 : 0 ≤ (1 + (1 - gridTime s t K n p)⁻¹) ^ k := by positivity
  have hw : (1 + (1 - gridTime s t K n p)⁻¹) ^ k ≤ (2 * H) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  set Z : ℝ := qGridB_aQ C C₂ k * N ^ k * (Y * (H / c) ^ k) ^ 2 * H ^ 2 with hZ
  have hZ0 : 0 ≤ Z := by
    have := qGridB_aQ_nonneg hC hC₂ k
    rw [hZ]; positivity
  have hpK : (p : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hp
  have hfull : (K n : ℝ) * Δ ^ 2 ≤ N ^ (-C_K) := by
    calc (K n : ℝ) * Δ ^ 2 = ((K n : ℝ) * Δ) * Δ := by ring
      _ ≤ 1 * Δ := mul_le_mul_of_nonneg_right hKΔ1 hΔ0
      _ ≤ N ^ (-C_K) := by rw [one_mul]; exact hΔD
  have h2H : 0 ≤ (2 * H) ^ k := by positivity
  calc ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ k *
        qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) Δ
          (lkEnvN d (sz.W n) (E n) k (gridTime s t K n j) (N ^ τK *
            (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
          (driftEnvN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (N ^ τK *
            (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0
      ≤ ∑ _j ∈ Finset.range p, (2 * H) ^ k * (Δ ^ 2 * Z) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have h1 := hstep j (lt_of_lt_of_le (Finset.mem_range.1 hj) hp)
        calc (1 + (1 - gridTime s t K n p)⁻¹) ^ k *
              qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) Δ
              (lkEnvN d (sz.W n) (E n) k (gridTime s t K n j) (N ^ τK *
                (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
              (driftEnvN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (N ^ τK *
                (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0
            ≤ (1 + (1 - gridTime s t K n p)⁻¹) ^ k * (Δ ^ 2 * Z) :=
              mul_le_mul_of_nonneg_left h1 hw0
          _ ≤ (2 * H) ^ k * (Δ ^ 2 * Z) := mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (p : ℝ) * ((2 * H) ^ k * (Δ ^ 2 * Z)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (K n : ℝ) * ((2 * H) ^ k * (Δ ^ 2 * Z)) :=
        mul_le_mul_of_nonneg_right hpK (by positivity)
    _ = (2 * H) ^ k * (((K n : ℝ) * Δ ^ 2) * Z) := by ring
    _ ≤ (2 * H) ^ k * (N ^ (-C_K) * Z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfull hZ0) h2H
    _ = 2 ^ k * qGridB_aQ C C₂ k * (c⁻¹) ^ (2 * k) *
        (N ^ k * H ^ (3 * k + 2) * Y ^ 2 * N ^ (-C_K)) := by
        rw [hZ, div_eq_mul_inv]
        ring

end Sum

/-! ## 4. Target 1: `sum_weighted_qErrQN_le` -/

section Main

/-- **Target 1 (`sum_weighted_qErrQN_le`)**: on the grid `u_j = gridTime s t K n j` with
`K n ≥ N^{C_K}`, the one-step remainders `qErrQN` of `gridDriftQN` (for the sup constant `C` and
the Taylor constant `C₂` of the mollifier, any `0 ≤ C, C₂`; `gridDriftQN` has
`C = (1 + 40 d m) 6^{d m}`, `C₂ = 1000 (1 + d m)²`) at the envelope
`B_{m+1} = N^{τ_K} η_{u_{j+1}}^{-(m+1)}`, weighted by the coarse row bound
`(1 + (1 - u_p)⁻¹)^{m+1}` of `Ugen`, sum over `j < p` to at most `N^{-D_t}` for every `p ≤ K n`,
eventually.  `m ≥ 1` is the tensor index (`m + 1` indices, loop length `k = m + 1`).  The four
rows are those of the merged `SumWeightedStepErrN_Stmt` (`θ = 1 - τ'`, `RangeCond τ' t`) with the
decay exponent `D_t + (m + 1)` (the factor `1 + C Lp ≤ (1 + C) N^m` of `qErrQN`); the `Δ²`-part
of `qErrQN` needs only `(m+1) + 2τ_K + (3(m+1)+2)θ + D_t < C_K`, which the second row implies.
RBM2D `sum_weighted_qErrQN_le` (`AltGridQ:2146`); new fixed constants `C, C₂` (T2156a), decay
exponent `D_t + (m + 1)` (T2156b), no `STKbound` (T2156c). -/
theorem sum_weighted_qErrQN_le (d : ℕ) (sz : Sizes d) {κ τ' τK C_K D_t C C₂ : ℝ}
    {E s t : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hκ : 0 < κ) (hτ' : 0 < τ') (hτ'1 : τ' ≤ 1) (hτK : 0 < τK) (hDt : 0 ≤ D_t) (hm : 1 ≤ m)
    (hsize : sz.SizeTendsto)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hK0 : ∀ n, K n ≠ 0) (hrange : sz.RangeCond τ' t)
    (h1 : 8 + (4 * ((m : ℝ) + 1) + 8) * (1 - τ') + 2 * (D_t + ((m : ℝ) + 1)) < C_K)
    (h2 : 3 + 4 * τK + 5 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K)
    (h3 : 2 * (1 - τ') + τK + 2 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K)
    (h4 : 1 - τ' < C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
          qErrQN sz E s t K n m C C₂ (((sz.size n : ℕ) : ℝ) ^ τK *
            (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by
  obtain ⟨c, hc0, hc1, hcE⟩ := qGridB_exists_c hκ hE
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hθ0 : 0 ≤ 1 - τ' := by linarith
  have hS := sum_weighted_stepErrN_le d sz (κ := κ) (τ' := τ') (τK := τK) (C_K := C_K)
    (D_t := D_t + ((m : ℝ) + 1)) (E := E) (s := s) (t := t) (K := K) (m + 1) hκ hτ' hτ'1 hτK
    (by positivity) (by omega) hsize hE hs0 hst ht1 hK0 hrange (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) h4 hKN
  set A : ℝ := 2 ^ (m + 1) * qGridB_aQ C C₂ (m + 1) * (c⁻¹) ^ (2 * (m + 1)) with hA
  have hef : ((m + 1 : ℕ) : ℝ) + (1 - τ') * ((3 * (m + 1) + 2 : ℕ) : ℝ) +
      τK * ((2 : ℕ) : ℝ) + (-C_K) < -D_t := by
    push_cast
    have hkθ : 0 ≤ (m : ℝ) * (1 - τ') := mul_nonneg (by linarith) hθ0
    nlinarith [hkθ]
  have hev := qGridB_eventually_le sz hsize (2 * A) _ (-D_t) hef
  filter_upwards [hrange, hKN, hS, hev, hsize.eventually_ge_atTop (2 * (1 + C)),
    hsize.eventually_ge_atTop 1] with n hR hKn hSn hevn hNC hN1
  intro p hp
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hsplit : ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
        qErrQN sz E s t K n m C C₂ (((sz.size n : ℕ) : ℝ) ^ τK *
          (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)) j =
      (1 + C * (((sz.L n : ℕ) : ℝ) ^ d) ^ m) * (∑ j ∈ Finset.range p,
        (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
          stepErrN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j)
            (gridTime s t K n (j + 1)) (gridStep s t K n) (((sz.size n : ℕ) : ℝ) ^ τK *
              (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1))) +
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
        qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) (gridStep s t K n)
          (lkEnvN d (sz.W n) (E n) (m + 1) (gridTime s t K n j)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)))
          (driftEnvN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1))) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold qErrQN
    rw [qGridB_qStepErrN_split]
    ring
  rw [hsplit]
  -- the `(1 + C Lp) stepErrN` part
  have hL2N : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have hWL := qGridB_size_cast sz n
    have hW : (1 : ℝ) ≤ sz.W n := by exact_mod_cast sz.W_pos n
    calc ((sz.L n : ℕ) : ℝ) ^ d = 1 * ((sz.L n : ℕ) : ℝ) ^ d := (one_mul _).symm
      _ ≤ (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hW) (by positivity)
      _ = ((sz.size n : ℕ) : ℝ) := hWL
  have hLp : (((sz.L n : ℕ) : ℝ) ^ d) ^ m ≤ ((sz.size n : ℕ) : ℝ) ^ m :=
    pow_le_pow_left₀ (by positivity) hL2N _
  have hNm1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ m := one_le_pow₀ hN1
  have h1Lp : 1 + C * (((sz.L n : ℕ) : ℝ) ^ d) ^ m ≤ (1 + C) * ((sz.size n : ℕ) : ℝ) ^ m := by
    nlinarith [mul_le_mul_of_nonneg_left hLp hC]
  have hpow : ((sz.size n : ℕ) : ℝ) ^ m * ((sz.size n : ℕ) : ℝ) ^ (-(D_t + ((m : ℝ) + 1))) =
      ((sz.size n : ℕ) : ℝ) ^ (-D_t) * ((sz.size n : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast ((sz.size n : ℕ) : ℝ) m, ← Real.rpow_add hN0]
    have e : ((m : ℕ) : ℝ) + (-(D_t + ((m : ℝ) + 1))) = -D_t + (-1) := by ring
    rw [e, Real.rpow_add hN0, Real.rpow_neg_one]
  have hNinv : (1 + C) * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hN0]
    linarith
  have hp1 : (1 + C * (((sz.L n : ℕ) : ℝ) ^ d) ^ m) * (∑ j ∈ Finset.range p,
        (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
          stepErrN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j)
            (gridTime s t K n (j + 1)) (gridStep s t K n) (((sz.size n : ℕ) : ℝ) ^ τK *
              (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t) / 2 := by
    have hp0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t) := Real.rpow_nonneg hN0.le _
    calc _ ≤ (1 + C * (((sz.L n : ℕ) : ℝ) ^ d) ^ m) *
          ((sz.size n : ℕ) : ℝ) ^ (-(D_t + ((m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (hSn p hp) (by positivity)
      _ ≤ ((1 + C) * ((sz.size n : ℕ) : ℝ) ^ m) *
          ((sz.size n : ℕ) : ℝ) ^ (-(D_t + ((m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right h1Lp (Real.rpow_nonneg hN0.le _)
      _ = (1 + C) * (((sz.size n : ℕ) : ℝ) ^ (-D_t) * ((sz.size n : ℕ) : ℝ)⁻¹) := by
          rw [mul_assoc, hpow]
      _ = ((sz.size n : ℕ) : ℝ) ^ (-D_t) * ((1 + C) * ((sz.size n : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t) * (1 / 2) := mul_le_mul_of_nonneg_left hNinv hp0
      _ = ((sz.size n : ℕ) : ℝ) ^ (-D_t) / 2 := by ring
  -- the `Δ²` part
  have hx := qGridB_extra_sum_le sz (m := m) (m + 1) rfl hm hC hC₂ c n hc0 hc1 (hcE n) hτK hτ'1
    (hE2 n) (hs0 n) (hst n) (ht1 n) (hK0 n) hR hKn h4.le p hp
  rw [qGridB_mono ((sz.size n : ℕ) : ℝ) hN0 (m + 1) (1 - τ') (3 * (m + 1) + 2) τK 2 (-C_K),
    ← hA] at hx
  have hp2 : ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
        qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) (gridStep s t K n)
          (lkEnvN d (sz.W n) (E n) (m + 1) (gridTime s t K n j)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)))
          (driftEnvN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1))) 0 ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t) / 2 := by
    refine hx.trans (le_of_mul_le_mul_left ?_ (two_pos : (0 : ℝ) < 2))
    calc 2 * (A * ((sz.size n : ℕ) : ℝ) ^ (((m + 1 : ℕ) : ℝ) + (1 - τ') * ((3 * (m + 1) + 2 : ℕ) : ℝ) +
          τK * ((2 : ℕ) : ℝ) + (-C_K))) =
        2 * A * ((sz.size n : ℕ) : ℝ) ^ (((m + 1 : ℕ) : ℝ) + (1 - τ') * ((3 * (m + 1) + 2 : ℕ) : ℝ) +
          τK * ((2 : ℕ) : ℝ) + (-C_K)) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t) := hevn
      _ = 2 * (((sz.size n : ℕ) : ℝ) ^ (-D_t) / 2) := by ring
  linarith [hp1, hp2]

end Main

/-! ## 5. The compiled nonempty instance at `d = 3`, on the merged `sz0`

`RBM.Gauss.SizesInst.sz0` (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `N_n = (W_n L_n)^3`) and the
grid data of the merged `sum_weighted_stepErrN_instance` (`E ≡ 0`, `s ≡ 0`, `t ≡ 1/2`,
`RangeCond sz0 (1/2) t`): `κ = 1`, `m = 3` (`m + 1 = 4` indices, as the merged `gridDriftQN_instance`),
`τ' = τ_K = 1/2`, `D_t = 1`, `C_K = 31`, `K n = N_n^{31}`, and the constants of the merged
`gridDriftQN` at `d = 3`, `m = 3`: `C = (1 + 40·9) 6^9`, `C₂ = 1000 (1 + 9)²`.  The four rows read
`30 < 31`, `20 < 31`, `10.5 < 31`, `0.5 < 31`.  Every hypothesis is discharged; nothing is left as
a hypothesis (the merged grid `K n = N_n^{21}` of `sum_weighted_stepErrN_instance` is too small:
the first row at `D_t + (m + 1)` is `30`). -/

namespace QGridBCheck

open RBM.Gauss.SizesInst RBM.Ind.GridEnvelopeNCheck

/-- `K n = N_n^{31}`: the grid with `K n ≥ N^{C_K}`, `C_K = 31`. -/
def Kc31 (n : ℕ) : ℕ := sz0.size n ^ 31

theorem Kc31_ne_zero (n : ℕ) : Kc31 n ≠ 0 := by
  unfold Kc31
  have : 0 < sz0.size n := by
    have := four_le_size n
    exact_mod_cast (by linarith : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ))
  positivity

theorem rpow_31_le_Kc31 (n : ℕ) : ((sz0.size n : ℕ) : ℝ) ^ (31 : ℝ) ≤ (Kc31 n : ℝ) := by
  unfold Kc31
  rw [show (31 : ℝ) = ((31 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  push_cast
  exact le_rfl

/-- **Instance of `sum_weighted_qErrQN_le`** at `sz0` (`d = 3`), `m = 3`, `τ' = τ_K = 1/2`,
`C_K = 31`, `D_t = 1`, `K n = N_n^{31}`, `C = (1 + 40·9) 6^9`, `C₂ = 1000 (1 + 9)²`: every
hypothesis is discharged (`SizeTendsto sz0`, `RangeCond`, the bulk energy, the grid, the four
numerical rows); nothing is left as a hypothesis. -/
theorem sum_weighted_qErrQN_instance :
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ Kc31 n,
      ∑ j ∈ Finset.range p,
          (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc31 n p)⁻¹) ^ (3 + 1) *
          qErrQN sz0 E1 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc31 n 3
            ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc31 n
                (j + 1)))⁻¹ ^ (3 + 1)) j ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  sum_weighted_qErrQN_le 3 sz0 (κ := 1) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 31) (D_t := 1)
    (C := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (C₂ := 1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2)
    (E := E1) (s := fun _ => 0) (t := fun _ => 1 / 2) (K := Kc31) 3 (by positivity)
    (by positivity) one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sz0_tendsto (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num)
    (fun _ => by norm_num) Kc31_ne_zero rangeCond_half (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Eventually.of_forall rpow_31_le_Kc31)

end QGridBCheck

end RBM.Ind

end

#print axioms RBM.Ind.sum_weighted_qErrQN_le
#print axioms RBM.Ind.QGridBCheck.Kc31
#print axioms RBM.Ind.QGridBCheck.Kc31_ne_zero
#print axioms RBM.Ind.QGridBCheck.rpow_31_le_Kc31
#print axioms RBM.Ind.QGridBCheck.sum_weighted_qErrQN_instance
