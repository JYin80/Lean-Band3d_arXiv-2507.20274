/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.GridDriftN

/-!
# The envelope bookkeeping of the grid drift (`d ≥ 3`)

Ticket T2153 (ST2-31, stochastic layer ST-2).  Port of `RBM2D/Induction/GridEnvelopeN.lean` at
`c9a24cf` (cited `GEN:<line>`; 713 lines there).  Paper: arXiv:2507.20274, `3_5` (`LK_SDE`,
`3_5:133`).  The RBM2D file `GridGoodEvent.lean` (the other half of row ST2-31) is superseded:
`gridGoodN_holds` is merged (T2146).

## Main results (namespace `RBM.Ind`)

* `gridDriftN_envelope` : `gridDriftN` holds a.e. with the step errors
  `stepErrN … (N^{τ_K} η_{u_{j+1}}^{-k})` for every grid step `j < K n` at once, eventually in `n`
  (RBM2D `gridDriftN_envelope`, `GEN:54`).
* `sum_gridStep_div_etaT_le` : `Σ_j Δ/η_{u_j} ≤ (Im m(E))^{-1} log N` on the grid under `RangeCond`
  (`GEN:96`).
* `SumWeightedStepErrN_Stmt`, `sum_weighted_stepErrN_le` : the step errors of
  `gridDriftN_envelope`, weighted by `(1 + (1 - u_m)^{-1})^k`, sum to at most `N^{-D_t}` for every
  `m ≤ K n`, eventually (`GEN:515, 534`).

## Dictionary and `d ≥ 3` changes (CLAUDE.md §5.2)

`d : Sizes ↦ sz : Sizes d`; `d.L n, d.W n, d.size n ↦ sz.L n, sz.W n, sz.size n = (W L)^d`;
`spectralM ↦ mE`; `RangeCond d τ' t ↦ sz.RangeCond τ' t`; `W² L² = N ↦ W^d L^d = N`; the
`((W⁻¹)^2)^(k-1)` factor of `stepErrN` is `(((W:ℝ)^d)⁻¹)^(k-1)` (merged `GridDriftN`).  All four
numerical inequalities of the pin are statements about powers of `N` and do not change with `d`.
Differences from RBM2D (paper-delta candidates):

* **T2153a** : `gridDriftN_envelope` has the new hypothesis `hKb : sz.STKbound E` (the owed pin
  KL7), because the merged `exists_norm_Kcal_le_win` (T2111a) takes it; RBM2D proved the bound
  unconditionally from `Kbound_prec_uncond`.  The merged lemma gives the bound along one fixed
  sequence `v n`; the uniformity in the grid index `j` of the pinned envelope
  `N^{τ_K} η_{u_{j+1}}^{-k}` is recovered by choosing a worst grid index `j*(n)` and
  `v n = u_{j*(n)+1}` (as `gdn_STKbound_win` chooses the worst `w`).
* **T2153b** : `[NeZero k]` is dropped from `gridDriftN_envelope` and `SumWeightedStepErrN_Stmt`
  (the merged `gridDriftN` has none; stronger).

Every unpinned helper is `private` with the prefix `gridEnv_`.
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

private theorem gridEnv_gridStep_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem gridEnv_gridTime_le {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n)
    (hK0 : K n ≠ 0) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j ≤ t n := by
  have hΔ := gridEnv_gridStep_nonneg (s := s) (t := t) (K := K) hst
  have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_right hj' hΔ
  have hlast := gridTime_last s t K n hK0
  unfold gridTime at hlast ⊢
  nlinarith

private theorem gridEnv_gridTime_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ := gridEnv_gridStep_nonneg (s := s) (t := t) (K := K) hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this hΔ]

private theorem gridEnv_one_le_size {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have : 1 ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega))
  exact_mod_cast this

private theorem gridEnv_size_cast {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

end Helpers

/-! ## 2. The envelope of the grid drift -/

section Ported

variable {d : ℕ}

/-- **(G2 ∘ G2 envelope)**: `exists_norm_Kcal_le_win` (eventually `‖𝒦‖ ≤ N^{τ_K} η_v^{-m}`)
supplies `B_k = N^{τ_K} η_{u_{j+1}}^{-k}` in `GridDriftN` for every grid step `j < K n` at once, so
`gridDriftN` holds with `stepErr_j = stepErrN … (N^{τ_K} η_{u_{j+1}}^{-k})`, a.e. in `ω`
simultaneously for all `j < K n` and all labels.  RBM2D `gridDriftN_envelope` (`GEN:54`);
new hypothesis `hKb : sz.STKbound E` (T2153a), `[NeZero k]` dropped (T2153b). -/
theorem gridDriftN_envelope (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (k : ℕ) (hk : 2 ≤ k) (τK : ℝ)
    (hτK : 0 < τK) {E s t : ℕ → ℝ} {K : ℕ → ℕ} (hsize : sz.SizeTendsto)
    (hKb : sz.STKbound E)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hK0 : ∀ n, K n ≠ 0) (σ : Fin k → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP sz), ∀ j, j < K n → ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncN sz E s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n (E n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ a) +
            sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a) +
            sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a))‖ ≤
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
          (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) := by
  classical
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hv1 : ∀ n j, j < K n → gridTime s t K n (j + 1) < 1 := fun n j hj =>
    (gridEnv_gridTime_le (hst n) (hK0 n) (show j + 1 ≤ K n by omega)).trans_lt (ht1 n)
  -- the deterministic envelope statement at the grid step `j`
  let P : ℕ → ℕ → Prop := fun n j => ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)),
    ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k
  have hP : ∀ᶠ n in atTop, ∀ j, j < K n → P n j := by
    by_contra hcon
    have hfreq := Filter.not_eventually.1 hcon
    let bad : ℕ → Prop := fun n => ∃ j, j < K n ∧ ¬ P n j
    have hbad : ∀ n, ¬ (∀ j, j < K n → P n j) → bad n := by
      intro n hn
      by_contra hb
      exact hn fun j hj => by
        by_contra hc
        exact hb ⟨j, hj, hc⟩
    let v : ℕ → ℝ := fun n =>
      if h : bad n then gridTime s t K n (Classical.choose h + 1) else 0
    have hvmem : ∀ n, 0 ≤ v n ∧ v n < 1 := by
      intro n
      by_cases h : bad n
      · have e : v n = gridTime s t K n (Classical.choose h + 1) := by simp [v, h]
        rw [e]
        exact ⟨gridEnv_gridTime_nonneg (hs0 n) (hst n) _, hv1 n _ (Classical.choose_spec h).1⟩
      · have e : v n = 0 := by simp [v, h]
        rw [e]
        exact ⟨le_rfl, one_pos⟩
    have hwin := exists_norm_Kcal_le_win sz hsize E hKb hE2 v (fun n => (hvmem n).1)
      (fun n => (hvmem n).2) k τK hτK
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hwin).exists
    have hbn : bad n := hbad n hn1
    obtain ⟨hjlt, hnP⟩ := Classical.choose_spec hbn
    have e : v n = gridTime s t K n (Classical.choose hbn + 1) := by simp [v, hbn]
    apply hnP
    intro w hw J hJ h2 hJk
    have hb := hn2 w (by rw [e]; exact hw) J hJ h2 hJk
    rw [e] at hb
    exact hb
  filter_upwards [hP] with n hn
  refine ae_all_iff.2 fun j => ?_
  by_cases hj : j < K n
  · have hη : 0 < etaT (E n) (gridTime s t K n (j + 1)) := etaT_pos (hE2 n) (hv1 n j hj)
    have hBk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη.le) _)
    have h := gridDriftN sz E s t K hE2 hs0 hst ht1 hK0 n j hj k hk σ _ hBk (hn j hj)
    exact h.mono fun ω hω _ => hω
  · exact Eventually.of_forall fun ω h => absurd h hj

/-- **`Σ_j Δ/η_{u_j} ≤ (Im m(E))^{-1} log N`** on the grid `u_j = s + jΔ` under `RangeCond`
(`1 - t ≥ N^{-(1-τ')}`, `τ' > 0`): each term is `≤ (Im m)^{-1}(log(1-u_j) - log(1-u_{j+1}))`
(`Real.one_sub_inv_le_log_of_pos`), the sum telescopes to `-log(1-t) ≤ (1-τ') log N`.  RBM2D
`sum_gridStep_div_etaT_le` (`GEN:96`); RBM1D `sum_step_div_eta_le_plainN`.  Dimension-free. -/
theorem sum_gridStep_div_etaT_le (sz : Sizes d) {τ' : ℝ} (hτ' : 0 < τ') {E s t : ℕ → ℝ}
    {K : ℕ → ℕ} (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hK0 : ∀ n, K n ≠ 0) (hrange : sz.RangeCond τ' t) :
    ∀ᶠ n : ℕ in atTop, ∑ j ∈ Finset.range (K n),
        gridStep s t K n / etaT (E n) (gridTime s t K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hrange] with n hn
  have hu1 : ∀ j ≤ K n, gridTime s t K n j < 1 := fun j hj =>
    (gridEnv_gridTime_le (hst n) (hK0 n) hj).trans_lt (ht1 n)
  have hpos : ∀ j ≤ K n, 0 < 1 - gridTime s t K n j := fun j hj => by linarith [hu1 j hj]
  have him : 0 < (mE (E n)).im := mE_im_pos (hE n)
  have hstep : ∀ j < K n, gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log (1 - gridTime s t K n j) - Real.log (1 - gridTime s t K n (j + 1)) := by
    intro j hj
    have h1 := hpos j hj.le
    have h2 := hpos (j + 1) hj
    have hx : 0 < (1 - gridTime s t K n j) / (1 - gridTime s t K n (j + 1)) := div_pos h1 h2
    have h3 := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div h1.ne' h2.ne', inv_div] at h3
    have hΔj : gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
      unfold gridTime; push_cast; ring
    have e : 1 - (1 - gridTime s t K n (j + 1)) / (1 - gridTime s t K n j) =
        gridStep s t K n / (1 - gridTime s t K n j) := by
      rw [hΔj]; field_simp; ring
    rwa [e] at h3
  have hsum : ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log (1 - gridTime s t K n 0) - Real.log (1 - gridTime s t K n (K n)) := by
    rw [← Finset.sum_range_sub' (fun j => Real.log (1 - gridTime s t K n j)) (K n)]
    exact Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.1 hj)
  have hs' : gridTime s t K n 0 = s n := by unfold gridTime; simp
  have hlast : gridTime s t K n (K n) = t n := gridTime_last s t K n (hK0 n)
  rw [hs', hlast] at hsum
  have hlog0 : Real.log (1 - s n) ≤ 0 :=
    Real.log_nonpos (by linarith [hst n, ht1 n]) (by linarith [hs0 n])
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := gridEnv_one_le_size sz n
  have hlogN : 0 ≤ Real.log ((sz.size n : ℕ) : ℝ) := Real.log_nonneg hN1
  have ht0 : 0 < 1 - t n := by linarith [ht1 n]
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hlogt : -Real.log (1 - t n) ≤ Real.log ((sz.size n : ℕ) : ℝ) := by
    have h4 := Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hn
    rw [Real.log_rpow hNpos] at h4
    nlinarith
  have hfin : ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log ((sz.size n : ℕ) : ℝ) := by linarith
  calc ∑ j ∈ Finset.range (K n), gridStep s t K n / etaT (E n) (gridTime s t K n j)
      = (mE (E n)).im⁻¹ *
          ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold etaT
        field_simp
    _ ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hfin (inv_nonneg.2 him.le)

end Ported

/-! ## 3. Deterministic bookkeeping of the weighted step errors -/

section Envelope

/-- `(1 + x)^k - 1 - k x ≤ k 2^k x²` for `0 ≤ x ≤ 1` (induction: `f_{k+1} = (1+x) f_k + k x²`). -/
private theorem gridEnv_binom_rem (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
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

/-- **The uniform one-step bound** (rows A, B, C): with `N = W^d L^d`, `H ≥ 1` a bound of
`(1 - v)^{-1}`, `H / c` a bound of `η_u^{-1}, η_v^{-1}`, `Y ≥ 1` (`= N^{τ_K}`) and `Δ H ≤ 1`, the
step error at `B_k = Y η_v^{-k}` is at most `Z₁ Δ^{3/2} + Z₂₃ Δ²`.  RBM2D `GridEnvelopeN_stepErr_le`
(`GEN:187`) with `W² L² = N ↦ W^d L^d = N`. -/
private theorem gridEnv_stepErr_le (d L W : ℕ) (E : ℝ) (k : ℕ) (u v Δ N H Y c : ℝ)
    (hN1 : 1 ≤ N) (hWL : (W : ℝ) ^ d * (L : ℝ) ^ d = N) (hW : (1 : ℝ) ≤ W)
    (hH : 1 ≤ H) (hY : 1 ≤ Y) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hΔ0 : 0 ≤ Δ) (hΔH : Δ * H ≤ 1)
    (hηu0 : 0 < etaT E u) (hηv0 : 0 < etaT E v)
    (hηu : (etaT E u)⁻¹ ≤ H / c) (hηv : (etaT E v)⁻¹ ≤ H / c)
    (hv1 : 0 < 1 - v) (hv : (1 - v)⁻¹ ≤ H) :
    stepErrN d L W E k u v Δ (Y * (etaT E v)⁻¹ ^ k) ≤
      16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) * Δ ^ ((3 : ℝ) / 2) +
        ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
          2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k)) * Δ ^ 2 := by
  unfold stepErrN
  set B := Y * (H / c) ^ k with hB
  have hHc : 1 ≤ H / c := by rw [le_div_iff₀ hc0]; linarith
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hY (one_le_pow₀ hHc)
  have hηu' : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu0.le
  have hηv' : 0 ≤ (etaT E v)⁻¹ := inv_nonneg.2 hηv0.le
  have hBk0 : 0 ≤ Y * (etaT E v)⁻¹ ^ k := mul_nonneg (by linarith) (pow_nonneg hηv' _)
  have hBk : Y * (etaT E v)⁻¹ ^ k ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hηv' hηv k)
    (by linarith)
  set Bk := Y * (etaT E v)⁻¹ ^ k with hBkdef
  -- term A
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hcast : ((((W * L) ^ d : ℕ)) : ℝ) = N := by
    push_cast; rw [← hWL]; ring
  have hone : 1 + (etaT E v)⁻¹ ≤ (1 + 1 / c) * H := by
    have : (etaT E v)⁻¹ ≤ H / c := hηv
    have h2 : H / c = (1 / c) * H := by ring
    linarith
  have hA : envConst d L W E k v ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) := by
    unfold envConst
    rw [hcast]
    have hbase : 0 ≤ 1 + (etaT E v)⁻¹ := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hone _) (by positivity)
  have hA' : envConst d L W E k v * Δ ^ ((3 : ℝ) / 2) ≤
      16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) * Δ ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hΔ0 _)
  -- term B
  have hk : kStepC d L W k Bk = 2 * (k : ℝ) ^ 4 * N ^ 2 * Bk ^ 3 + (k : ℝ) ^ 6 * N ^ 3 * Bk ^ 4 := by
    unfold kStepC
    rw [← hWL]; ring
  have hN23 : N ^ 2 ≤ N ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
  have hB3 : Bk ^ 3 ≤ B ^ 4 :=
    (pow_le_pow_left₀ hBk0 hBk 3).trans (pow_le_pow_right₀ hB1 (by norm_num))
  have hB4 : Bk ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hBk0 hBk 4
  have hkB : kStepC d L W k Bk ≤ (2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * B ^ 4 := by
    rw [hk]
    have hk4 : (0 : ℝ) ≤ (k : ℝ) ^ 4 := by positivity
    have hk6 : (0 : ℝ) ≤ (k : ℝ) ^ 6 := by positivity
    have e1 : 2 * (k : ℝ) ^ 4 * N ^ 2 * Bk ^ 3 ≤ 2 * (k : ℝ) ^ 4 * N ^ 3 * B ^ 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hN23 (by positivity)) hB3 (by positivity)
        (by positivity)
    have e2 : (k : ℝ) ^ 6 * N ^ 3 * Bk ^ 4 ≤ (k : ℝ) ^ 6 * N ^ 3 * B ^ 4 :=
      mul_le_mul_of_nonneg_left hB4 (by positivity)
    linarith [e1, e2]
  have hB' : kStepC d L W k Bk * Δ ^ 2 ≤
      (2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * B ^ 4 * Δ ^ 2 :=
    mul_le_mul_of_nonneg_right hkB (sq_nonneg Δ)
  -- term C
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 (inv_nonneg.2 hv1.le)
  have hxH : Δ * (1 - v)⁻¹ ≤ Δ * H := mul_le_mul_of_nonneg_left hv hΔ0
  have hx1 : Δ * (1 - v)⁻¹ ≤ 1 := hxH.trans hΔH
  have hrem := gridEnv_binom_rem (Δ * (1 - v)⁻¹) hx0 hx1 k
  have hx2 : (Δ * (1 - v)⁻¹) ^ 2 ≤ Δ ^ 2 * H ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx0 hxH 2 |>.trans (by rw [mul_pow])
  have hiv2 : (1 - v)⁻¹ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hv1.le) hv 2
  have hU : uStepC k Δ v ≤ ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2 := by
    unfold uStepC
    have e1 : (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 ≤ (k : ℝ) * Δ ^ 2 * H ^ 2 :=
      mul_le_mul_of_nonneg_left hiv2 (by positivity)
    have e2 : (k : ℝ) * 2 ^ k * (Δ * (1 - v)⁻¹) ^ 2 ≤ (k : ℝ) * 2 ^ k * (Δ ^ 2 * H ^ 2) :=
      mul_le_mul_of_nonneg_left hx2 (by positivity)
    linarith [hrem, e1, e2]
  have hWd0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := inv_nonneg.2 (by positivity)
  have hbr0 : 0 ≤ (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk :=
    add_nonneg (mul_nonneg (pow_nonneg hηu' _) (pow_nonneg hWd0 _)) hBk0
  have hW1 : (((W : ℝ) ^ d)⁻¹) ^ (k - 1) ≤ 1 :=
    pow_le_one₀ hWd0 (inv_le_one_of_one_le₀ (one_le_pow₀ hW))
  have hbr : (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk ≤ 2 * B := by
    have e1 : (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) ≤ B := by
      calc (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) ≤ (etaT E u)⁻¹ ^ k * 1 :=
            mul_le_mul_of_nonneg_left hW1 (pow_nonneg hηu' _)
        _ = (etaT E u)⁻¹ ^ k := mul_one _
        _ ≤ (H / c) ^ k := pow_le_pow_left₀ hηu' hηu k
        _ ≤ Y * (H / c) ^ k := by
          exact le_mul_of_one_le_left (by positivity) hY
    linarith
  have hC : uStepC k Δ v * ((etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk) ≤
      2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * B * Δ ^ 2 := by
    calc uStepC k Δ v * ((etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk)
        ≤ (((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2) * (2 * B) :=
          mul_le_mul hU hbr hbr0 (by positivity)
      _ = 2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * B * Δ ^ 2 := by ring
  linarith [hA', hB', hC]

/-- The three `k`-, `c`-dependent coefficients of the weighted sum. -/
private def gridEnv_a1 (k : ℕ) (c : ℝ) : ℝ :=
  2 ^ k * (16 * ((k : ℝ) + 3) ^ 4 * (1 + 1 / c) ^ (k + 4))

private def gridEnv_a2 (k : ℕ) (c : ℝ) : ℝ :=
  2 ^ k * ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * (c⁻¹) ^ (4 * k))

private def gridEnv_a3 (k : ℕ) (c : ℝ) : ℝ :=
  2 ^ k * (2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (c⁻¹) ^ k)

/-- The algebra of the three monomials (`X₁ = N^{-C_K/2}`, `X₂ = N^{-C_K}`). -/
private theorem gridEnv_alg (k : ℕ) (c H Y N X₁ X₂ : ℝ) :
    (2 * H) ^ k * ((16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4)) * X₁ +
        ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
          2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k)) * X₂) =
      2 ^ k * (16 * ((k : ℝ) + 3) ^ 4 * (1 + 1 / c) ^ (k + 4)) *
          (N ^ 4 * H ^ (2 * k + 4) * Y ^ 0 * X₁) +
        2 ^ k * ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * (c⁻¹) ^ (4 * k)) *
          (N ^ 3 * H ^ (5 * k) * Y ^ 4 * X₂) +
        2 ^ k * (2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (c⁻¹) ^ k) *
          (N ^ 0 * H ^ (2 * k + 2) * Y ^ 1 * X₂) := by
  have e1 : ((1 + 1 / c) * H) ^ (k + 4) = (1 + 1 / c) ^ (k + 4) * H ^ (k + 4) := mul_pow _ _ _
  have e2 : (H / c) ^ k = H ^ k * (c⁻¹) ^ k := by rw [div_eq_mul_inv, mul_pow]
  rw [e1, e2]
  generalize (1 + 1 / c) ^ (k + 4) = P
  ring

/-- **The weighted sum at a fixed size index**, as a sum of three `N`-monomials: for `m ≤ K n`,
`Σ_{j<m} (1 + (1-u_m)^{-1})^k stepErrN … ≤ a₁ N⁴ H^{2k+4} N^{-C_K/2} + a₂ N³ Y⁴ H^{5k} N^{-C_K}
+ a₃ Y H^{2k+2} N^{-C_K}`, `N = size n`, `H = N^{1-τ'}`, `Y = N^{τ_K}`, `c ≤ Im m(E n)`.
RBM2D `GridEnvelopeN_sum_le` (`GEN:314`). -/
private theorem gridEnv_sum_le {d : ℕ} (sz : Sizes d) {τ' τK C_K : ℝ} {E s t : ℕ → ℝ}
    {K : ℕ → ℕ}
    (k : ℕ) (c : ℝ) (n : ℕ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hcE : c ≤ (mE (E n)).im)
    (hτK : 0 < τK) (hτ'1 : τ' ≤ 1) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (ht1 : t n < 1) (hK0 : K n ≠ 0)
    (hR : ((sz.size n : ℕ) : ℝ) ^ (-1 + τ') ≤ 1 - t n)
    (hKn : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (h4 : 1 - τ' ≤ C_K) (m : ℕ) (hm : m ≤ K n) :
    ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
          (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
      gridEnv_a1 k c *
          (((sz.size n : ℕ) : ℝ) ^ 4 * (((sz.size n : ℕ) : ℝ) ^ (1 - τ')) ^ (2 * k + 4) *
            (((sz.size n : ℕ) : ℝ) ^ τK) ^ 0 * ((sz.size n : ℕ) : ℝ) ^ (-C_K / 2)) +
        gridEnv_a2 k c *
          (((sz.size n : ℕ) : ℝ) ^ 3 * (((sz.size n : ℕ) : ℝ) ^ (1 - τ')) ^ (5 * k) *
            (((sz.size n : ℕ) : ℝ) ^ τK) ^ 4 * ((sz.size n : ℕ) : ℝ) ^ (-C_K)) +
        gridEnv_a3 k c *
          (((sz.size n : ℕ) : ℝ) ^ 0 * (((sz.size n : ℕ) : ℝ) ^ (1 - τ')) ^ (2 * k + 2) *
            (((sz.size n : ℕ) : ℝ) ^ τK) ^ 1 * ((sz.size n : ℕ) : ℝ) ^ (-C_K)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := gridEnv_one_le_size sz n
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
  have hΔ0 : 0 ≤ Δ := gridEnv_gridStep_nonneg (s := s) (t := t) (K := K) hst
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
  -- per-step bound
  have hWL : (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = N := gridEnv_size_cast sz n
  have hW : (1 : ℝ) ≤ sz.W n := by exact_mod_cast sz.W_pos n
  have hstep : ∀ j < K n,
      stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1)) Δ
          (Y * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
        16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) * Δ ^ ((3 : ℝ) / 2) +
          ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
            2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k)) * Δ ^ 2 := by
    intro j hj
    have hu : gridTime s t K n j ≤ t n := gridEnv_gridTime_le hst hK0 hj.le
    have hv : gridTime s t K n (j + 1) ≤ t n := gridEnv_gridTime_le hst hK0 hj
    obtain ⟨hu1, _⟩ := hinv _ hu
    obtain ⟨hv1, hvH⟩ := hinv _ hv
    obtain ⟨hηu0, hηu⟩ := hη _ hu
    obtain ⟨hηv0, hηv⟩ := hη _ hv
    exact gridEnv_stepErr_le d (sz.L n) (sz.W n) (E n) k _ _ Δ N H Y c hN1 hWL hW hH1 hY1 hc0
      hc1 hΔ0 hΔH hηu0 hηv0 hηu hηv hv1 hvH
  -- the weight
  have hum : gridTime s t K n m ≤ t n := gridEnv_gridTime_le hst hK0 hm
  obtain ⟨_, hwH⟩ := hinv _ hum
  have hw0 : 0 ≤ (1 + (1 - gridTime s t K n m)⁻¹) ^ k := by
    have := inv_nonneg.2 (hinv _ hum).1.le
    positivity
  have hw : (1 + (1 - gridTime s t K n m)⁻¹) ^ k ≤ (2 * H) ^ k :=
    pow_le_pow_left₀ (by have := inv_nonneg.2 (hinv _ hum).1.le; linarith) (by linarith) k
  -- the sum
  set Z1 : ℝ := 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) with hZ1
  set Z2 : ℝ := (2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
            2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k) with hZ2
  have hZ1' : 0 ≤ Z1 := by rw [hZ1]; positivity
  have hZ2' : 0 ≤ Z2 := by rw [hZ2]; positivity
  have hT : 0 ≤ Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2 := by
    have := Real.rpow_nonneg hΔ0 ((3 : ℝ) / 2)
    positivity
  have hsumle : ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1)) Δ
          (Y * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
      (m : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2)) := by
    calc _ ≤ ∑ j ∈ Finset.range m, (2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h1 := hstep j (lt_of_lt_of_le (Finset.mem_range.1 hj) hm)
          calc (1 + (1 - gridTime s t K n m)⁻¹) ^ k * stepErrN d (sz.L n) (sz.W n) (E n) k
                (gridTime s t K n j) (gridTime s t K n (j + 1)) Δ
                (Y * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)
              ≤ (1 + (1 - gridTime s t K n m)⁻¹) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2) :=
                mul_le_mul_of_nonneg_left h1 hw0
            _ ≤ (2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2) :=
                mul_le_mul_of_nonneg_right hw hT
      _ = (m : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmK : (m : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hm
  have h2H : 0 ≤ (2 * H) ^ k := by positivity
  -- `K Δ^{3/2} ≤ N^{-C_K/2}` and `K Δ² ≤ N^{-C_K}`
  have hhalf : (K n : ℝ) * Δ ^ ((3 : ℝ) / 2) ≤ N ^ (-C_K / 2) := by
    have e : Δ ^ ((3 : ℝ) / 2) = Δ * Δ ^ ((1 : ℝ) / 2) := by
      rw [show ((3 : ℝ) / 2) = 1 + (1 : ℝ) / 2 by norm_num, Real.rpow_add' hΔ0 (by norm_num),
        Real.rpow_one]
    have h1 : Δ ^ ((1 : ℝ) / 2) ≤ N ^ (-C_K / 2) := by
      calc Δ ^ ((1 : ℝ) / 2) ≤ (N ^ (-C_K)) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow hΔ0 hΔD (by norm_num)
        _ = N ^ (-C_K / 2) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
    calc (K n : ℝ) * Δ ^ ((3 : ℝ) / 2) = ((K n : ℝ) * Δ) * Δ ^ ((1 : ℝ) / 2) := by rw [e]; ring
      _ ≤ 1 * N ^ (-C_K / 2) :=
          mul_le_mul hKΔ1 h1 (Real.rpow_nonneg hΔ0 _) zero_le_one
      _ = N ^ (-C_K / 2) := one_mul _
  have hfull : (K n : ℝ) * Δ ^ 2 ≤ N ^ (-C_K) := by
    calc (K n : ℝ) * Δ ^ 2 = ((K n : ℝ) * Δ) * Δ := by ring
      _ ≤ 1 * Δ := mul_le_mul_of_nonneg_right hKΔ1 hΔ0
      _ ≤ N ^ (-C_K) := by rw [one_mul]; exact hΔD
  have hmain : (m : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2)) ≤
      (2 * H) ^ k * (Z1 * N ^ (-C_K / 2) + Z2 * N ^ (-C_K)) := by
    calc (m : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2))
        ≤ (K n : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2)) :=
          mul_le_mul_of_nonneg_right hmK (mul_nonneg h2H hT)
      _ = (2 * H) ^ k * (Z1 * ((K n : ℝ) * Δ ^ ((3 : ℝ) / 2)) + Z2 * ((K n : ℝ) * Δ ^ 2)) := by
          ring
      _ ≤ (2 * H) ^ k * (Z1 * N ^ (-C_K / 2) + Z2 * N ^ (-C_K)) := by
          refine mul_le_mul_of_nonneg_left ?_ h2H
          exact add_le_add (mul_le_mul_of_nonneg_left hhalf hZ1')
            (mul_le_mul_of_nonneg_left hfull hZ2')
  refine hsumle.trans (hmain.trans (le_of_eq ?_))
  rw [hZ1, hZ2]
  unfold gridEnv_a1 gridEnv_a2 gridEnv_a3
  exact gridEnv_alg k c H Y N _ _

end Envelope

section Main

/-- `N^a (N^θ)^p (N^τ)^q N^b = N^{a + θ p + τ q + b}`. -/
private theorem gridEnv_mono (N : ℝ) (hN : 0 < N) (a : ℕ) (θ : ℝ) (p : ℕ) (τ : ℝ) (q : ℕ)
    (b : ℝ) :
    N ^ a * (N ^ θ) ^ p * (N ^ τ) ^ q * N ^ b = N ^ ((a : ℝ) + θ * p + τ * q + b) := by
  rw [← Real.rpow_natCast N a, ← Real.rpow_natCast (N ^ θ) p, ← Real.rpow_natCast (N ^ τ) q,
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN, ← Real.rpow_add hN,
    ← Real.rpow_add hN]

/-- `A N^e ≤ N^f` eventually, for `e < f` (`N → ∞`). -/
private theorem gridEnv_eventually_le {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto)
    (A e f : ℝ) (hef : e < f) :
    ∀ᶠ n : ℕ in atTop, A * ((sz.size n : ℕ) : ℝ) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ f := by
  have hT : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ) ^ (f - e)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hef)).comp hsize
  filter_upwards [hT.eventually_ge_atTop A, hsize.eventually_ge_atTop 1] with n hA hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  calc A * ((sz.size n : ℕ) : ℝ) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ (f - e) * ((sz.size n : ℕ) : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hN0.le _)
    _ = ((sz.size n : ℕ) : ℝ) ^ f := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- A uniform lower bound `0 < c ≤ 1`, `c ≤ Im m(E n)` in the bulk `|E n| ≤ 2 - κ`. -/
private theorem gridEnv_exists_c {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
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

/-- **Pin `SumWeightedStepErrN_Stmt`**: on the grid `u_j = gridTime s t K n j` with `K n ≥ N^{C_K}`,
the step errors of `gridDriftN_envelope` (`B_k = N^{τ_K} η_{u_{j+1}}^{-k}`), weighted by the coarse
row bound `(1 + (1 − u_m)^{-1})^k` of `Ugen`, sum to at most `N^{-D_t}` for every `m ≤ K n`,
eventually, as soon as `C_K` exceeds the three rows A, B, C and the expansion row D
(`θ = 1 − τ'`, `RangeCond τ' t`: `1 − t ≥ N^{-θ}`).  Strict inequalities absorb the `k`-dependent
constants.  RBM2D `SumWeightedStepErrN_Stmt` (`GEN:515`); `sz : Sizes d`, `W^d` in `stepErrN`,
`[NeZero k]` dropped (T2153b); the four inequalities are unchanged (they are about powers of `N`). -/
def SumWeightedStepErrN_Stmt : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) {κ τ' τK C_K D_t : ℝ} {E s t : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ),
    0 < κ → 0 < τ' → τ' ≤ 1 → 0 < τK → 0 ≤ D_t → 2 ≤ k → sz.SizeTendsto →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    (∀ n, K n ≠ 0) → sz.RangeCond τ' t →
    8 + (4 * (k : ℝ) + 8) * (1 - τ') + 2 * D_t < C_K →
    3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + D_t < C_K →
    2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + D_t < C_K →
    1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ m ≤ K n,
      ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
          stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t)

/-- **`sum_weighted_stepErrN_le`**: the pinned statement `SumWeightedStepErrN_Stmt`. -/
theorem sum_weighted_stepErrN_le : SumWeightedStepErrN_Stmt := by
  intro d sz κ τ' τK C_K D_t E s t K k hκ hτ' hτ'1 hτK hDt hk hsize hE hs0 hst ht1 hK0 hrange
    h1 h2 h3 h4 hKN
  obtain ⟨c, hc0, hc1, hcE⟩ := gridEnv_exists_c hκ hE
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hev1 := gridEnv_eventually_le sz hsize (3 * gridEnv_a1 k c)
    (((4 : ℕ) : ℝ) + (1 - τ') * ((2 * k + 4 : ℕ) : ℝ) + τK * ((0 : ℕ) : ℝ) + (-C_K / 2)) (-D_t)
    (by push_cast; linarith [h1])
  have hev2 := gridEnv_eventually_le sz hsize (3 * gridEnv_a2 k c)
    (((3 : ℕ) : ℝ) + (1 - τ') * ((5 * k : ℕ) : ℝ) + τK * ((4 : ℕ) : ℝ) + (-C_K)) (-D_t)
    (by push_cast; linarith [h2])
  have hev3 := gridEnv_eventually_le sz hsize (3 * gridEnv_a3 k c)
    (((0 : ℕ) : ℝ) + (1 - τ') * ((2 * k + 2 : ℕ) : ℝ) + τK * ((1 : ℕ) : ℝ) + (-C_K)) (-D_t)
    (by push_cast; linarith [h3])
  filter_upwards [hrange, hKN, hev1, hev2, hev3, hsize.eventually_ge_atTop 1] with n hR hKn hA1 hA2 hA3 hN1
  intro m hm
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hsum := gridEnv_sum_le sz k c n hc0 hc1 (hcE n) hτK hτ'1 (hE2 n) (hs0 n) (hst n)
    (ht1 n) (hK0 n) hR hKn h4.le m hm
  have m1 := gridEnv_mono ((sz.size n : ℕ) : ℝ) hN0 4 (1 - τ') (2 * k + 4) τK 0 (-C_K / 2)
  have m2 := gridEnv_mono ((sz.size n : ℕ) : ℝ) hN0 3 (1 - τ') (5 * k) τK 4 (-C_K)
  have m3 := gridEnv_mono ((sz.size n : ℕ) : ℝ) hN0 0 (1 - τ') (2 * k + 2) τK 1 (-C_K)
  rw [m1, m2, m3] at hsum
  calc _ ≤ _ := hsum
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t) / 3 + ((sz.size n : ℕ) : ℝ) ^ (-D_t) / 3 +
          ((sz.size n : ℕ) : ℝ) ^ (-D_t) / 3 :=
        add_le_add (add_le_add ((le_div_iff₀' (by norm_num : (0 : ℝ) < 3)).2 (by rw [← mul_assoc]; exact hA1))
          ((le_div_iff₀' (by norm_num : (0 : ℝ) < 3)).2 (by rw [← mul_assoc]; exact hA2)))
          ((le_div_iff₀' (by norm_num : (0 : ℝ) < 3)).2 (by rw [← mul_assoc]; exact hA3))
    _ = _ := by ring

end Main

/-! ## 4. The compiled nonempty instances at `d = 3`, on the merged `sz0`

`RBM.Gauss.SizesInst.sz0` (`RBM3D/Defs/Sizes.lean`): `d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`N_n = (W_n L_n)^3`, `N_0 = 2097152`.

* `sum_weighted_stepErrN_instance`: `κ = 1`, `E ≡ 0`, `s ≡ 0`, `t ≡ 1/2`, `k = 3`,
  `τ' = τ_K = 1/2`, `C_K = 21`, `D_t = 1`, `K n = N_n^{21}`; the four inequalities of the pin read
  `20 < 21`, `13.5 < 21`, `5.5 < 21`, `0.5 < 21`.  Every hypothesis is discharged.
* `sum_gridStep_instance`: `τ' = 2/3`, `E ≡ 0`, `s ≡ 0`, `K ≡ 4`, `t_n = 1 - N_n^{-1+2/3}` (the
  boundary of `RangeCond`, `t_n → 1`).  Every hypothesis is discharged.
* `gridDriftN_envelope_instance`: `κ = 1`, `k = 3`, `τ_K = 1/2`, `E ≡ 0`, `s ≡ 1/10`, `t ≡ 1/2`,
  `K ≡ 4` (the data of `GridDriftNCheck`).  The owed pin `STKbound sz0 E0` (KL7) stays a hypothesis
  of the example (CLAUDE.md §4 step 2); every deterministic hypothesis is discharged. -/

namespace GridEnvelopeNCheck

open RBM.Gauss.SizesInst

theorem four_le_size (n : ℕ) : (4 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by
  have hWL : 3 ≤ sz0.W n * sz0.L n := by
    have h1 := sz0.W_pos n
    have h2 := sz0.three_le_L n
    nlinarith
  have h : 4 ≤ sz0.size n :=
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ (sz0.W n * sz0.L n) ^ 3 := Nat.pow_le_pow_left hWL 3
  exact_mod_cast h

/-- `E ≡ 0`. -/
abbrev E1 : ℕ → ℝ := fun _ => 0

/-- `K n = N_n^{21}`: the grid with `K n ≥ N^{C_K}`, `C_K = 21`. -/
def Kc (n : ℕ) : ℕ := sz0.size n ^ 21

theorem Kc_ne_zero (n : ℕ) : Kc n ≠ 0 := by
  unfold Kc
  have : 0 < sz0.size n := by
    have := four_le_size n
    exact_mod_cast (by linarith : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ))
  positivity

theorem rpow_21_le_Kc (n : ℕ) : ((sz0.size n : ℕ) : ℝ) ^ (21 : ℝ) ≤ (Kc n : ℝ) := by
  unfold Kc
  rw [show (21 : ℝ) = ((21 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  push_cast
  exact le_rfl

theorem rangeCond_half : sz0.RangeCond (1 / 2) (fun _ => 1 / 2) := by
  refine Eventually.of_forall fun n => ?_
  calc ((sz0.size n : ℕ) : ℝ) ^ (-1 + 1 / 2 : ℝ) ≤ (4 : ℝ) ^ (-1 + 1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (four_le_size n) (by norm_num)
    _ = 1 - 1 / 2 := by
        rw [show (-1 + 1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
          ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        norm_num

/-- **Instance of `sum_weighted_stepErrN_le`** at `sz0` (`d = 3`), `k = 3`, `τ' = τ_K = 1/2`,
`C_K = 21`, `D_t = 1`, `K n = N_n^{21}`: every hypothesis is discharged (`SizeTendsto sz0`,
`RangeCond`, the bulk energy, the grid, and the four numerical inequalities); nothing is left as a
hypothesis. -/
theorem sum_weighted_stepErrN_instance :
    ∀ᶠ n : ℕ in atTop, ∀ m ≤ Kc n,
      ∑ j ∈ Finset.range m, (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n m)⁻¹) ^ 3 *
          stepErrN 3 (sz0.L n) (sz0.W n) (E1 n) 3
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j)
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1))
            (gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1)))⁻¹ ^ 3) ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  sum_weighted_stepErrN_le 3 sz0 (κ := 1) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 21) (D_t := 1)
    (E := E1) (s := fun _ => 0) (t := fun _ => 1 / 2) (K := Kc) 3 one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) sz0_tendsto
    (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    Kc_ne_zero rangeCond_half (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Eventually.of_forall rpow_21_le_Kc)

/-- `t_n = 1 - N_n^{-1+2/3}`: the boundary of `RangeCond` with `τ' = 2/3`. -/
def tBd (n : ℕ) : ℝ := 1 - ((sz0.size n : ℕ) : ℝ) ^ (-1 + 2 / 3 : ℝ)

theorem tBd_lt_one (n : ℕ) : tBd n < 1 := by
  unfold tBd
  have : 0 < ((sz0.size n : ℕ) : ℝ) ^ (-1 + 2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith [four_le_size n]) _
  linarith

theorem zero_le_tBd (n : ℕ) : (0 : ℝ) ≤ tBd n := by
  unfold tBd
  have : ((sz0.size n : ℕ) : ℝ) ^ (-1 + 2 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [four_le_size n]) (by norm_num)
  linarith

theorem rangeCond_tBd : sz0.RangeCond (2 / 3) tBd :=
  Eventually.of_forall fun n => le_of_eq (by unfold tBd; ring)

/-- **Instance of `sum_gridStep_div_etaT_le`** at `sz0` (`d = 3`), `τ' = 2/3`, `K ≡ 4`, at
`t_n = 1 - N_n^{-1/3}`, the boundary of `RangeCond`: every hypothesis proved. -/
theorem sum_gridStep_instance :
    ∀ᶠ n : ℕ in atTop, ∑ j ∈ Finset.range ((fun _ => 4 : ℕ → ℕ) n),
        gridStep (fun _ => (0 : ℝ)) tBd (fun _ => 4) n /
          etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) tBd (fun _ => 4) n j) ≤
      (mE (E1 n)).im⁻¹ * Real.log ((sz0.size n : ℕ) : ℝ) :=
  sum_gridStep_div_etaT_le sz0 (τ' := 2 / 3) (by norm_num) (E := E1) (s := fun _ => 0) (t := tBd)
    (K := fun _ => 4) (fun _ => by norm_num) (fun _ => le_rfl) (fun n => zero_le_tBd n) tBd_lt_one
    (fun _ => by norm_num) rangeCond_tBd

/-- **Instance of `gridDriftN_envelope`** at `sz0` (`d = 3`), `κ = 1`, `k = 3`, `τ_K = 1/2`,
`E ≡ 0`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, every sign vector `σ`.  The owed pin `STKbound sz0 E1`
(KL7) is the one hypothesis left open; `SizeTendsto` is `sz0_tendsto`. -/
theorem gridDriftN_envelope_instance (hKb : sz0.STKbound E1) (σ : Fin 3 → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP sz0), ∀ j, j < 4 → ∀ a : Fin 3 → Zd 3 (sz0.L n),
      ‖predIncN sz0 E1 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j σ ω a -
          (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n : ℂ) *
          (∑ l ∈ Finset.Icc 3 3, sz0.STksimLKM n (E1 n)
              (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j)
              (pathH sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j ω) l (loopOf σ a) +
            sz0.STelklkM n (E1 n)
              (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j)
              (pathH sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j ω) (loopOf σ a) +
            sz0.STegtM n (E1 n)
              (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j)
              (pathH sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j ω) (loopOf σ a))‖ ≤
        stepErrN 3 (sz0.L n) (sz0.W n) (E1 n) 3
          (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j)
          (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n (j + 1))
          (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n)
          (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
            (etaT (E1 n) (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n
              (j + 1)))⁻¹ ^ 3) :=
  gridDriftN_envelope sz0 1 one_pos 3 (by norm_num) (1 / 2) (by norm_num) sz0_tendsto hKb
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) σ

end GridEnvelopeNCheck

end RBM.Ind

end

#print axioms RBM.Ind.gridDriftN_envelope
#print axioms RBM.Ind.sum_gridStep_div_etaT_le
#print axioms RBM.Ind.SumWeightedStepErrN_Stmt
#print axioms RBM.Ind.sum_weighted_stepErrN_le
#print axioms RBM.Ind.GridEnvelopeNCheck.sum_weighted_stepErrN_instance
#print axioms RBM.Ind.GridEnvelopeNCheck.sum_gridStep_instance
#print axioms RBM.Ind.GridEnvelopeNCheck.gridDriftN_envelope_instance
