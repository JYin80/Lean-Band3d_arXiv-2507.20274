/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.LemDecCalEdif

/-!
# `lem_dec_calE`, third part, second half: `lemDecCalE_dif` (S5-07)

Ticket T2181 (S5-07, ST-4).  Port of `RBM2D/Path/LemDecCalEdif.lean` at commit `c9a24cf`
(cited `LemDecCalEdif:<line>`: §6 Sum `:1002-1058`, §7 Scalar `:1060-1186`, §8 Cases `:1188-1625`,
§9 `lemDecCalE_dif` `:1632`) to `d ≥ 3`, onto the merged cut bounds of T2171
(`Path/LemDecCalEdif`: `LemDecCalEdif_STeeM_le`, `LemDecCalEdif_cut_near`, `LemDecCalEdif_cut_far`).
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `res_deccalE_dif`
`3_5:2327-2334`; the paper omits the proof ("a special case of [YY_25, Lemma 5.7]", `3_5:2338`).

Contents (namespace `RBM.Path`): the theorem `lemDecCalE_dif (d : ℕ) : LemDecCalE_dif d` (every
`σ ∈ {±}²`, every `a'` in the range), and two compiled instances (near and far branch).

Differences from RBM2D (each forced by `d ≥ 3` or by the pinned statement):
* the scale is `M_u = W^d (1 - u)` (RBM2D `W² ℓ_u² η_u`); `ρ`, `η_u`, `η_v`, `v` disappear;
* RBM2D's two far terms `η_u⁻¹ ρ³ M_u^{-1/2} J² + η_v⁻¹ M_v⁻¹ J³` become the pin's single
  `(1-u)⁻¹ (W^d |1-u|)^{-1/2} J³` (`J² ≤ J³`, `M_u⁻¹ ≤ M_u^{-1/2}`);
* the near long-edge term `W^d L^d · 2 c_near Λ⁶ J P⁻¹ = 2 c_near Λ⁶ J W^{-5d}` is closed without
  `J ≤ W` (RBM2D `near_far_small` `:1164` uses it): `W^{-5d} ≤ M_u^{-5} ≤ M_u^{-1/2} M_u⁻⁴` and
  `J ≤ J³`; the conjunct `J ≤ W` of `E2Hyp` is not used;
* the convolution `convTailT` (`2500 ℓ_v² M_v^{-2}`, RBM2D `:1440`) is the merged
  `LemDecCalE_sum_tail_tail` (`2 S_d + 1`, `S_d = (1 + 1536 d⁴)^d`);
* the constants are the four rows `N1 = 2·9^d Λ (log P)^{2d} e^{4Y}`, `N2 = 2 c_near Λ⁶ e^{4Y}`,
  `F1 = 8 (2ℓ* + 3)^d c_e² Λ³ S³`, `F2 = 2 c_e³ (2 S_d + 1) Λ³ S³` against `lossE2dif`
  (`κ_dif = 729^d`), with `c_near = 32 · 3^{d+1}`, `c_e = 2 · 9^d`, `S = e² e^{2Y}`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Path

open Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Green

/-! ## 1. Copied helpers (the merged ones are private) -/

section Helpers

private theorem lemDecCalEdif2_W_pos {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
  exact_mod_cast sz.W_pos n

private theorem lemDecCalEdif2_L_pos {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
  have := sz.three_le_L n
  exact_mod_cast (by omega : 0 < sz.L n)

private theorem lemDecCalEdif2_L_one {d : ℕ} (sz : Sizes d) (n : ℕ) : 1 ≤ sz.L n := by
  have := sz.three_le_L n; omega

private theorem lemDecCalEdif2_zd_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private theorem lemDecCalEdif2_zd_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

/-- Symmetry of the `L^∞` distance (`LemDecCalEdif.lean:514`). -/
private theorem lemDecCalEdif2_zd_comm (d L : ℕ) [NeZero L] (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub b a, lemDecCalEdif2_zd_neg]

/-- Basic numeric consequences of `E2Hyp` (`LemDecCalEdif.lean:502`). -/
private theorem lemDecCalEdif2_basic {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (h : E2Hyp sz n E u D Λ K₀ J M) :
    0 ≤ u ∧ u < 1 ∧ 1 ≤ Λ ∧ 1 ≤ J ∧ 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ M.IsHermitian := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -⟩ := h
  exact ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩

/-- `log(L^d W^{6d}) ≥ 6 d log W` (`LemDecCalEdif.lean:593`). -/
private theorem lemDecCalEdif2_logP_ge {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (6 * (d : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) ≤
      Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
  have hL0 := lemDecCalEdif2_L_pos sz n
  have hW0 := lemDecCalEdif2_W_pos sz n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast lemDecCalEdif2_L_one sz n
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have h1 : 0 ≤ (d : ℝ) * Real.log ((sz.L n : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hL1)
  push_cast
  linarith

/-- `log P ≥ 72` for `P = L^d W^{6d}` (`d ≥ 3`, `log W ≥ 4`; `LemDecCalEdif.lean:616`). -/
private theorem lemDecCalEdif2_logP_ge72 {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (h : E2Hyp sz n E u D Λ K₀ J M) :
    72 ≤ Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast h.1
  have := lemDecCalEdif2_logP_ge sz n
  nlinarith

/-- `S^{(B)}_{xy} ≠ 0` forces `|x - y|_∞ ≤ 1` (`Path/LemDecCalE.lean:770`, copied). -/
private theorem lemDecCalEdif2_SB_support (d L : ℕ) [NeZero L] (g : ℝ) {x y : Zd d L}
    (h : SB d L g x y ≠ 0) : zdistInf d L (x - y) ≤ 1 := by
  rw [SB_apply] at h
  unfold sbKernel at h
  by_cases h0 : x - y = 0
  · rw [h0, lemDecCalEdif2_zd_zero]; exact zero_le_one
  · by_cases h1 : zdistD d L (x - y) = 1
    · exact (zdistInf_le_zdistD d L _).trans h1.le
    · simp [h0, h1] at h

end Helpers

/-! ## 2. Summation over `b, b'` (RBM2D §6 `:1033-1058`) -/

section Sum

/-- The `S^{(B)}` average: `Σ_{b'} |S_{bb'}| X(b') ≤ F` if `X(b') ≤ F` for `|b - b'|_∞ ≤ 1`
(RBM2D `sum_SB_le` `:1033`). -/
private theorem lemDecCalEdif2_sum_SB_le {d L : ℕ} [NeZero L] (hL : 3 ≤ L) (g : ℝ) (b : Zd d L)
    (X : Zd d L → ℝ) (F : ℝ)
    (hX : ∀ b' : Zd d L, zdistInf d L (b - b') ≤ 1 → X b' ≤ F) :
    ∑ b' : Zd d L, ‖SB d L g b b'‖ * X b' ≤ F := by
  calc ∑ b' : Zd d L, ‖SB d L g b b'‖ * X b' ≤ ∑ b' : Zd d L, ‖SB d L g b b'‖ * F := by
        refine Finset.sum_le_sum fun b' _ => ?_
        by_cases hb : SB d L g b b' = 0
        · rw [hb]; simp
        · exact mul_le_mul_of_nonneg_left (hX b' (lemDecCalEdif2_SB_support d L g hb))
            (norm_nonneg _)
    _ = F := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL b, one_mul]

/-- Ball count with indicators: `Σ_b 1(|c - b|_∞ ≤ R) ≤ (2R + 1)^d` (RBM2D `count_le` `:1048`). -/
private theorem lemDecCalEdif2_count_le {d L : ℕ} [NeZero L] (c : Zd d L) (R : ℝ) (hR : 0 ≤ R) :
    ∑ b : Zd d L, (if (zdistInf d L (c - b) : ℝ) ≤ R then (1 : ℝ) else 0) ≤ (2 * R + 1) ^ d := by
  rw [Finset.sum_boole]
  exact LemDecCalE_e10a c R hR

end Sum

/-! ## 3. Scalar facts (RBM2D §7 `:1060-1186`) -/

section Scalar

/-- `(e² e^{2Y})³ ≤ 404 e^{6Y}` (RBM2D `S3_le` `:1072`). -/
private theorem lemDecCalEdif2_S3_le (Y : ℝ) :
    (Real.exp 2 * Real.exp (2 * Y)) ^ 3 ≤ 404 * Real.exp (6 * Y) := by
  have e1 : (Real.exp 2 * Real.exp (2 * Y)) ^ 3 = Real.exp 1 ^ 6 * Real.exp (6 * Y) := by
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [e1]
  have h1 := Real.exp_one_lt_d9
  have h6 : Real.exp 1 ^ 6 ≤ 404 := by
    calc Real.exp 1 ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 6
      _ ≤ 404 := by norm_num
  exact mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le

/-- `Y = (log W)^{3/4}` has `Y² = (log W)^{3/2}`. -/
private theorem lemDecCalEdif2_Y_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((3 : ℝ) / 4)) ^ 2 = x ^ ((3 : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The loss absorbs the constants: `10¹² (1600 d⁴)^d 729^d (1 + log P)^{2d} Λ⁶ e^{8Y} ≤ lossE2dif`
(`K₀², (1 + log(L^d W^{2d}))⁴, (1 + log W)³ ≥ 1`; pattern of `LemDecCalEwG.lean:1777`). -/
private theorem lemDecCalEdif2_loss_ge (h : E2Hyp sz n E u D Λ K₀ J M) :
    10 ^ 12 * ((1600 * (d : ℝ) ^ 4) ^ d * 729 ^ d *
        (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) * Λ ^ 6 *
        Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ≤
      lossE2dif d (sz.L n) (sz.W n) Λ K₀ := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h
  have hK : 1 ≤ K₀ := h.2.2.2.2.2.2.2.2.1
  have hW0 := lemDecCalEdif2_W_pos sz n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast lemDecCalEdif2_L_one sz n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
    by_contra hcon
    have := Real.log_nonpos hW0.le (not_le.1 hcon).le
    linarith
  have hlp := lemDecCalEdif2_logP_ge sz n
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast h.1
  have hlogW0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  set Lg : ℝ := Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) with hLg
  have hLg0 : 0 ≤ Lg := by
    have : (0 : ℝ) ≤ (6 * (d : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) := by positivity
    linarith
  have hbase : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1)
  have hA : (1 : ℝ) ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 :=
    one_le_pow₀ (by linarith [Real.log_nonneg hbase])
  have hB : (1 : ℝ) ≤ (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 := one_le_pow₀ (by linarith)
  have hK2 : (1 : ℝ) ≤ K₀ ^ 2 := one_le_pow₀ hK
  have hX : (0 : ℝ) ≤ 10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * Λ ^ 6 *
      Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := by positivity
  have hprod : (1 : ℝ) ≤ K₀ ^ 2 *
      (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
        (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK2 hA) hB
  have hG : (0 : ℝ) ≤ 729 ^ d * (1 + Lg) ^ (2 * d) := by positivity
  unfold lossE2dif lossE2
  rw [← hLg]
  have e : (10 : ℝ) ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * K₀ ^ 2 * Λ ^ 6 *
      (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
      (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 *
      Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
      (729 ^ d * (1 + Lg) ^ (2 * d)) =
      (10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * Λ ^ 6 *
        Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) *
      (K₀ ^ 2 * (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
        (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3) * (729 ^ d * (1 + Lg) ^ (2 * d)) := by ring
  rw [e]
  have e2 : (10 : ℝ) ^ 12 * ((1600 * (d : ℝ) ^ 4) ^ d * 729 ^ d * (1 + Lg) ^ (2 * d) * Λ ^ 6 *
        Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) =
      (10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * Λ ^ 6 *
        Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) * 1 *
        (729 ^ d * (1 + Lg) ^ (2 * d)) := by ring
  rw [e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hX) hG

/-- Product of five termwise bounds on nonnegative reals. -/
private theorem lemDecCalEdif2_mul5_le {a b c d e a' b' c' d' e' : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (he0 : 0 ≤ e)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d') (he : e ≤ e') :
    a * b * c * d * e ≤ a' * b' * c' * d' * e' := by
  have ha1 : 0 ≤ a' := ha0.trans ha
  have hb1 : 0 ≤ b' := hb0.trans hb
  have hc1 : 0 ≤ c' := hc0.trans hc
  have hd1 : 0 ≤ d' := hd0.trans hd
  exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul ha hb hb0 ha1) hc hc0
    (mul_nonneg ha1 hb1)) hd hd0 (mul_nonneg (mul_nonneg ha1 hb1) hc1)) he he0
    (mul_nonneg (mul_nonneg (mul_nonneg ha1 hb1) hc1) hd1)

/-- Common facts for the constant rows. -/
private theorem lemDecCalEdif2_facts (h : E2Hyp sz n E u D Λ K₀ J M) :
    1 ≤ Λ ∧ 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧
      0 ≤ Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ∧
      72 ≤ Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast h.1
  have hlp := lemDecCalEdif2_logP_ge sz n
  have hlp72 := lemDecCalEdif2_logP_ge72 h
  have hlogW : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  refine ⟨hΛ, hlogW, hlog, by linarith, ?_, hlp72⟩
  nlinarith

/-- The near rows: `N1 = 2·9^d Λ (log P)^{2d} e^{4Y}` and `N2 = 2 c_near Λ⁶ e^{4Y}` are at most
`lossE2dif` (`κ_dif = 729^d`). -/
private theorem lemDecCalEdif2_rows_near (h : E2Hyp sz n E u D Λ K₀ J M) :
    2 * 9 ^ d * Λ *
        Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ (2 * d) *
        Real.exp (4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤
      lossE2dif d (sz.L n) (sz.W n) Λ K₀ ∧
    2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * Real.exp (4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤
      lossE2dif d (sz.L n) (sz.W n) Λ K₀ := by
  have hloss := lemDecCalEdif2_loss_ge h
  obtain ⟨hΛ, hlogW, hlog4, hLg0, hLgW, hLg72⟩ := lemDecCalEdif2_facts h
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by have := h.1; omega : 1 ≤ d)
  set Lg : ℝ := Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) with hLg
  set Y : ℝ := Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hlogW _
  have hΛ0 : 0 ≤ Λ := by linarith
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hx : (1 : ℝ) ≤ (1600 * (d : ℝ) ^ 4) ^ d := one_le_pow₀ (by linarith)
  have h9 : (9 : ℝ) ^ d ≤ 729 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h3 : (3 : ℝ) ^ d ≤ 729 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have hLgG : Lg ^ (2 * d) ≤ (1 + Lg) ^ (2 * d) := pow_le_pow_left₀ hLg0 (by linarith) _
  have hΛ6 : Λ ≤ Λ ^ 6 := by
    have := pow_le_pow_right₀ hΛ (show 1 ≤ 6 by norm_num); simpa using this
  have he : Real.exp (4 * Y) ≤ Real.exp (8 * Y) := Real.exp_le_exp.2 (by linarith)
  have hg1 : (1 : ℝ) ≤ (1 + Lg) ^ (2 * d) := one_le_pow₀ (by linarith)
  set Z : ℝ := (1600 * (d : ℝ) ^ 4) ^ d * 729 ^ d * (1 + Lg) ^ (2 * d) * Λ ^ 6 *
    Real.exp (8 * Y) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  constructor
  · have k : 1 * 9 ^ d * Lg ^ (2 * d) * Λ * Real.exp (4 * Y) ≤ Z :=
      lemDecCalEdif2_mul5_le (by norm_num) (by positivity) (by positivity) hΛ0 (by positivity)
        hx h9 hLgG hΛ6 he
    calc 2 * 9 ^ d * Λ * Lg ^ (2 * d) * Real.exp (4 * Y)
        = 2 * (1 * 9 ^ d * Lg ^ (2 * d) * Λ * Real.exp (4 * Y)) := by ring
      _ ≤ 10 ^ 12 * Z := by nlinarith
      _ ≤ _ := hloss
  · have k : 1 * 3 ^ d * 1 * Λ ^ 6 * Real.exp (4 * Y) ≤ Z :=
      lemDecCalEdif2_mul5_le (by norm_num) (by positivity) (by norm_num) (by positivity)
        (by positivity) hx h3 hg1 le_rfl he
    calc 2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * Real.exp (4 * Y)
        = 192 * (1 * 3 ^ d * 1 * Λ ^ 6 * Real.exp (4 * Y)) := by rw [pow_succ]; ring
      _ ≤ 10 ^ 12 * Z := by nlinarith
      _ ≤ _ := hloss

/-- The far rows: `F1 + F2 ≤ lossE2dif`, `F1 = 8 (2ℓ* + 3)^d c_e² Λ³ S³`,
`F2 = 2 c_e³ (2 S_d + 1) Λ³ S³`, `c_e = 2 · 9^d`, `S = e² e^{2Y}` (the slack is in the report). -/
private theorem lemDecCalEdif2_rows_far (h : E2Hyp sz n E u D Λ K₀ J M) :
    8 * (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 3) ^ d * (2 * 9 ^ d) ^ 2 * Λ ^ 3 *
        (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 +
      2 * (2 * 9 ^ d) ^ 3 * (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * Λ ^ 3 *
        (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 ≤
      lossE2dif d (sz.L n) (sz.W n) Λ K₀ := by
  have hloss := lemDecCalEdif2_loss_ge h
  obtain ⟨hΛ, hlogW, hlog4, hLg0, hLgW, hLg72⟩ := lemDecCalEdif2_facts h
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by have := h.1; omega : 1 ≤ d)
  set Lg : ℝ := Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) with hLg
  set lw : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hlw
  set Y : ℝ := lw ^ ((3 : ℝ) / 4) with hY
  set ls : ℝ := lw ^ ((3 : ℝ) / 2) with hls
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hlogW _
  have hls0 : 0 ≤ ls := Real.rpow_nonneg hlogW _
  have hΛ0 : 0 ≤ Λ := by linarith
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hx : (1 : ℝ) ≤ (1600 * (d : ℝ) ^ 4) ^ d := one_le_pow₀ (by linarith)
  have h243 : (243 : ℝ) ^ d ≤ 729 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have hg1 : (1 : ℝ) ≤ (1 + Lg) ^ (2 * d) := one_le_pow₀ (by linarith)
  have hΛ3 : Λ ^ 3 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ (by norm_num)
  have he : Real.exp (6 * Y) ≤ Real.exp (8 * Y) := Real.exp_le_exp.2 (by linarith)
  have he8 : 0 ≤ Real.exp (8 * Y) := (Real.exp_pos _).le
  have hS3 : (Real.exp 2 * Real.exp (2 * Y)) ^ 3 ≤ 404 * Real.exp (8 * Y) :=
    (lemDecCalEdif2_S3_le Y).trans (by nlinarith)
  -- `ℓ* ≤ (log W)² ≤ (log P)²`, hence `2ℓ* + 3 ≤ 3 (1 + log P)²`
  have hls2 : ls ≤ lw ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := lw) (by linarith)
      (show (3 : ℝ) / 2 ≤ ((2 : ℕ) : ℝ) by norm_num)
    rwa [Real.rpow_natCast] at this
  have hlw2 : lw ^ 2 ≤ Lg ^ 2 := pow_le_pow_left₀ hlogW hLgW 2
  have hbase : 2 * ls + 3 ≤ 3 * (1 + Lg) ^ 2 := by nlinarith
  have hcount : (2 * ls + 3) ^ d ≤ 3 ^ d * (1 + Lg) ^ (2 * d) := by
    calc (2 * ls + 3) ^ d ≤ (3 * (1 + Lg) ^ 2) ^ d := pow_le_pow_left₀ (by positivity) hbase d
      _ = 3 ^ d * (1 + Lg) ^ (2 * d) := by rw [mul_pow, ← pow_mul]
  -- `2 S_d + 1 ≤ 3 (1600 d⁴)^d`
  have hSd1 : (1 : ℝ) ≤ (1 + 1536 * (d : ℝ) ^ 4) ^ d := one_le_pow₀ (by linarith)
  have hSd : (1 + 1536 * (d : ℝ) ^ 4) ^ d ≤ (1600 * (d : ℝ) ^ 4) ^ d :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) d
  have h2S : 2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1 ≤ 3 * (1600 * (d : ℝ) ^ 4) ^ d := by linarith
  have hc2 : (2 * (9 : ℝ) ^ d) ^ 2 * 3 ^ d = 4 * 243 ^ d := by
    rw [mul_pow, ← pow_mul, mul_comm d 2, pow_mul, mul_assoc, ← mul_pow]; norm_num
  have hc3 : (2 * (9 : ℝ) ^ d) ^ 3 = 8 * 729 ^ d := by
    rw [mul_pow, ← pow_mul, mul_comm d 3, pow_mul]; norm_num
  set Z : ℝ := (1600 * (d : ℝ) ^ 4) ^ d * 729 ^ d * (1 + Lg) ^ (2 * d) * Λ ^ 6 *
    Real.exp (8 * Y) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hF1 : 8 * (2 * ls + 3) ^ d * (2 * 9 ^ d) ^ 2 * Λ ^ 3 *
      (Real.exp 2 * Real.exp (2 * Y)) ^ 3 ≤ 12928 * Z := by
    have k : 1 * 243 ^ d * (1 + Lg) ^ (2 * d) * Λ ^ 3 * Real.exp (8 * Y) ≤ Z :=
      lemDecCalEdif2_mul5_le (by norm_num) (by positivity) (by positivity) (by positivity) he8
        hx h243 le_rfl hΛ3 le_rfl
    calc 8 * (2 * ls + 3) ^ d * (2 * 9 ^ d) ^ 2 * Λ ^ 3 * (Real.exp 2 * Real.exp (2 * Y)) ^ 3
        ≤ 8 * (3 ^ d * (1 + Lg) ^ (2 * d)) * (2 * 9 ^ d) ^ 2 * Λ ^ 3 * (404 * Real.exp (8 * Y)) :=
          lemDecCalEdif2_mul5_le (by norm_num) (by positivity) (by positivity) (by positivity)
            (by positivity) le_rfl hcount le_rfl le_rfl hS3
      _ = 3232 * (((2 * 9 ^ d) ^ 2 * 3 ^ d) * (1 + Lg) ^ (2 * d) * Λ ^ 3 * Real.exp (8 * Y)) := by
          ring
      _ = 12928 * (1 * 243 ^ d * (1 + Lg) ^ (2 * d) * Λ ^ 3 * Real.exp (8 * Y)) := by
          rw [hc2]; ring
      _ ≤ 12928 * Z := by linarith
  have hF2 : 2 * (2 * 9 ^ d) ^ 3 * (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * Λ ^ 3 *
      (Real.exp 2 * Real.exp (2 * Y)) ^ 3 ≤ 19392 * Z := by
    have k : (1600 * (d : ℝ) ^ 4) ^ d * 729 ^ d * 1 * Λ ^ 3 * Real.exp (8 * Y) ≤ Z :=
      lemDecCalEdif2_mul5_le (by positivity) (by positivity) (by norm_num) (by positivity) he8
        le_rfl le_rfl hg1 hΛ3 le_rfl
    calc 2 * (2 * 9 ^ d) ^ 3 * (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * Λ ^ 3 *
          (Real.exp 2 * Real.exp (2 * Y)) ^ 3
        ≤ 2 * (2 * 9 ^ d) ^ 3 * (3 * (1600 * (d : ℝ) ^ 4) ^ d) * Λ ^ 3 *
          (404 * Real.exp (8 * Y)) :=
          lemDecCalEdif2_mul5_le (by norm_num) (by positivity) (by linarith) (by positivity)
            (by positivity) le_rfl le_rfl h2S le_rfl hS3
      _ = 19392 * ((1600 * (d : ℝ) ^ 4) ^ d * 729 ^ d * 1 * Λ ^ 3 * Real.exp (8 * Y)) := by
          rw [hc3]; ring
      _ ≤ 19392 * Z := by linarith
  nlinarith

end Scalar

/-! ## 4. The near case `|a₀ - a₁|_∞ ≤ 4ℓ*` (RBM2D §8 `:1188-1370`) -/

section Near

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Near lower bound for the tail: `M_u⁻⁴ ≤ e^{4Y} T_{u,D}(x)²` for `0 ≤ x ≤ 4ℓ*`
(RBM2D `tail_lower` `:1124`; `|1 - u| = 1 - u`, `√(4ℓ*) = 2Y`). -/
private theorem lemDecCalEdif2_tail_lower (h : E2Hyp sz n E u D Λ K₀ J M) {x : ℝ}
    (hx : x ≤ 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) :
    ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 4 ≤
      Real.exp (4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
        tailTD d ((sz.W n : ℕ) : ℝ) u D x ^ 2 := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h
  have h2 := LemDecCalE_e2 h
  have hW0 := lemDecCalEdif2_W_pos sz n
  have hlogW : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  have hxu : 0 < 1 - u := by linarith
  have hY0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hlogW _
  have hY2 := lemDecCalEdif2_Y_sq hlogW
  have hs : Real.sqrt x ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  unfold tailTD
  rw [abs_of_pos hxu]
  set Y := Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) with hY
  set m := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  have hm0 : 0 ≤ m := inv_nonneg.2 (by linarith [h2.1])
  have hT : m ^ 2 * Real.exp (-(2 * Y)) ≤
      m ^ 2 * Real.exp (-Real.sqrt x) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have h1 : Real.exp (-(2 * Y)) ≤ Real.exp (-Real.sqrt x) := Real.exp_le_exp.2 (by linarith)
    have hW : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg m)
    linarith
  set T := m ^ 2 * Real.exp (-Real.sqrt x) + ((sz.W n : ℕ) : ℝ) ^ (-D) with hTdef
  have hT' : m ^ 2 ≤ Real.exp (2 * Y) * T := by
    have e : m ^ 2 = Real.exp (2 * Y) * (m ^ 2 * Real.exp (-(2 * Y))) := by
      rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [e]
    exact mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le
  calc m ^ 4 = (m ^ 2) ^ 2 := by ring
    _ ≤ (Real.exp (2 * Y) * T) ^ 2 := pow_le_pow_left₀ (sq_nonneg m) hT' 2
    _ = Real.exp (4 * Y) * T ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- Near case, the sum over `b, b'` (RBM2D `near_sum` `:1197`):
`‖(ℰ⊗ℰ)^{M,(2)}‖ ≤ W^d (Λ M_u⁻⁵ · 2 · 9^d (log P)^{2d} + L^d · 2 · c_near Λ⁶ J P⁻¹)`,
`c_near = 32 · 3^{d+1}`. -/
private theorem lemDecCalEdif2_near_sum (h : E2HypDif sz n E u D Λ K₀ J M) (σ : Fin 2 → Bool)
    (a a' : Fin 2 → Zd d (sz.L n)) :
    ‖STeeM sz n E u M σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
      (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5 *
          (2 * (9 ^ d *
            Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ (2 * d))) +
        ((sz.L n : ℕ) : ℝ) ^ d * (2 * (32 * 3 ^ (d + 1) * Λ ^ 6 * J *
          (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹))) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h.1
  have hlp := lemDecCalEdif2_logP_ge72 h.1
  have hL3 := sz.three_le_L n
  set Lg : ℝ := Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) with hLg
  set P : ℝ := ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) with hP
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  set Cn : ℝ := 32 * 3 ^ (d + 1) * Λ ^ 6 * J * P⁻¹ with hCn
  set Fn : Zd d (sz.L n) → ℝ := fun b => Λ * m ^ 5 *
      ((if (zdistInf d (sz.L n) (a 0 - b) : ℝ) ≤ 4 * Lg ^ 2 then 1 else 0) +
        (if (zdistInf d (sz.L n) (a 1 - b) : ℝ) ≤ 4 * Lg ^ 2 then 1 else 0)) + 2 * Cn with hFn
  have hper : ∀ b b' : Zd d (sz.L n),
      ‖STLM sz n E u M ![σ 0, σ 1, σ 0, !σ 0, !σ 1, !σ 0] ![a 0, a 1, b', a' 1, a' 0, b]‖ +
        ‖STLM sz n E u M ![σ 1, σ 0, σ 1, !σ 1, !σ 0, !σ 1] ![a 1, a 0, b', a' 0, a' 1, b]‖ ≤
        Fn b := by
    intro b b'
    have c1 := LemDecCalEdif_cut_near h (σ 0) (σ 1) (a 0) (a 1) (a' 0) (a' 1) b b'
    have c2 := LemDecCalEdif_cut_near h (σ 1) (σ 0) (a 1) (a 0) (a' 1) (a' 0) b b'
    simp only [hFn]
    linarith
  have hsum : ‖STeeM sz n E u M σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ b : Zd d (sz.L n), Fn b := by
    refine (LemDecCalEdif_STeeM_le sz n E u M σ a a').trans ?_
    gcongr with b
    exact lemDecCalEdif2_sum_SB_le (sz.three_le_L n) (sz.lam n) b _ (Fn b)
      (fun b' _ => hper b b')
  have hR0 : 0 ≤ 4 * Lg ^ 2 := by positivity
  have hcnt : ∀ c : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      (if (zdistInf d (sz.L n) (c - b) : ℝ) ≤ 4 * Lg ^ 2 then (1 : ℝ) else 0) ≤
        9 ^ d * Lg ^ (2 * d) := by
    intro c
    refine (lemDecCalEdif2_count_le c _ hR0).trans ?_
    have h1 : 2 * (4 * Lg ^ 2) + 1 ≤ 9 * Lg ^ 2 := by nlinarith
    calc (2 * (4 * Lg ^ 2) + 1) ^ d ≤ (9 * Lg ^ 2) ^ d := pow_le_pow_left₀ (by positivity) h1 d
      _ = 9 ^ d * Lg ^ (2 * d) := by rw [mul_pow, ← pow_mul]
  have hsplit : ∑ b : Zd d (sz.L n), Fn b = Λ * m ^ 5 *
      (∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a 0 - b) : ℝ) ≤ 4 * Lg ^ 2 then (1 : ℝ) else 0) +
        ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a 1 - b) : ℝ) ≤ 4 * Lg ^ 2 then (1 : ℝ) else 0)) +
      ((sz.L n : ℕ) : ℝ) ^ d * (2 * Cn) := by
    simp only [hFn, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, card_Zd]
    push_cast
    ring
  have hc : 0 ≤ Λ * m ^ 5 := by
    have : 0 ≤ m := inv_nonneg.2 (by linarith [(LemDecCalE_e2 h.1).1])
    have : 0 ≤ Λ := by linarith
    positivity
  have hsc : ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a 0 - b) : ℝ) ≤ 4 * Lg ^ 2 then (1 : ℝ) else 0) +
      ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a 1 - b) : ℝ) ≤ 4 * Lg ^ 2 then (1 : ℝ) else 0) ≤
      2 * (9 ^ d * Lg ^ (2 * d)) := by linarith [hcnt (a 0), hcnt (a 1)]
  have hsumF : ∑ b : Zd d (sz.L n), Fn b ≤ Λ * m ^ 5 * (2 * (9 ^ d * Lg ^ (2 * d))) +
      ((sz.L n : ℕ) : ℝ) ^ d * (2 * Cn) := by
    rw [hsplit]
    exact add_le_add (mul_le_mul_of_nonneg_left hsc hc) le_rfl
  exact hsum.trans (mul_le_mul_of_nonneg_left hsumF (by positivity))

/-- **Near case** `|a₀ - a₁|_∞ ≤ 4ℓ*`: `‖(ℰ⊗ℰ)^{M,(2)}‖ ≤ lossE2dif · (1-u)⁻¹ [1 + M_u^{-1/2} J³] T²`.
The near long-edge term `W^d L^d · 2 c_near Λ⁶ J P⁻¹ = 2 c_near Λ⁶ J W^{-5d}` is closed without
`J ≤ W`: `W^{-5d} ≤ M_u⁻⁵ ≤ M_u^{-1/2} M_u⁻⁴ ≤ M_u^{-1/2} e^{4Y} T²` and `J ≤ J³`. -/
private theorem lemDecCalEdif2_near_case (h : E2HypDif sz n E u D Λ K₀ J M) (σ : Fin 2 → Bool)
    (a a' : Fin 2 → Zd d (sz.L n))
    (hn : (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤
      4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) :
    ‖STeeM sz n E u M σ a a'‖ ≤ lossE2dif d (sz.L n) (sz.W n) Λ K₀ *
      ((1 - u)⁻¹ * (1 + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) *
        STtailTD sz n u D a ^ 2) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h.1
  have h2 := LemDecCalE_e2 h.1
  have hsum := lemDecCalEdif2_near_sum h σ a a'
  have hlow := lemDecCalEdif2_tail_lower h.1 hn
  obtain ⟨hr1, hr2⟩ := lemDecCalEdif2_rows_near h.1
  have hW0 := lemDecCalEdif2_W_pos sz n
  have hL0 := lemDecCalEdif2_L_pos sz n
  have hxu : 0 < 1 - u := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ3 : J ^ (3 : ℝ) = J ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hST : STtailTD sz n u D a =
      tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := rfl
  rw [abs_of_pos hxu, hJ3, hST]
  have hq0 : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
  have hMu : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith [h2.1]
  have hlp := lemDecCalEdif2_logP_ge72 h.1
  set Lg : ℝ := Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) with hLg
  set P : ℝ := ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) with hP
  set q : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hq
  set m : ℝ := (q * (1 - u))⁻¹ with hm
  set e4 : ℝ := Real.exp (4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with he4
  set T : ℝ := tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hT
  set Φ : ℝ := lossE2dif d (sz.L n) (sz.W n) Λ K₀ with hΦ
  have hm0 : 0 < m := inv_pos.2 hMu
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ h2.1
  have hinvu : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ hxu).2 (by linarith)
  have hqm : q * m = (1 - u)⁻¹ := by rw [hm]; field_simp
  have hqinv : q⁻¹ ≤ m := by
    rw [hm]
    exact inv_anti₀ hMu (by linarith [h2.2])
  have hT0 : 0 ≤ T := tailTD_nonneg hW0.le
  have he40 : 0 ≤ e4 := (Real.exp_pos _).le
  have hLg0 : 0 ≤ Lg := by linarith
  have hsq : 0 ≤ m ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hm0.le _
  -- the first summand: `q Λ m⁵ · 2 · 9^d Lg^{2d} ≤ N1 (1-u)⁻¹ T²`
  have k1 : q * (Λ * m ^ 5 * (2 * (9 ^ d * Lg ^ (2 * d)))) ≤
      (2 * 9 ^ d * Λ * Lg ^ (2 * d) * e4) * ((1 - u)⁻¹ * T ^ 2) := by
    have e : q * (Λ * m ^ 5 * (2 * (9 ^ d * Lg ^ (2 * d)))) =
        (2 * 9 ^ d * Λ * Lg ^ (2 * d)) * ((1 - u)⁻¹ * m ^ 4) := by
      linear_combination (2 * 9 ^ d * Λ * Lg ^ (2 * d) * m ^ 4) * hqm
    rw [e]
    calc (2 * 9 ^ d * Λ * Lg ^ (2 * d)) * ((1 - u)⁻¹ * m ^ 4)
        ≤ (2 * 9 ^ d * Λ * Lg ^ (2 * d)) * ((1 - u)⁻¹ * (e4 * T ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow (by linarith)) (by positivity)
      _ = _ := by ring
  -- the second summand: `q L^d · 2 c_near Λ⁶ J P⁻¹ ≤ N2 (1-u)⁻¹ M_u^{-1/2} J³ T²`
  have hPq : P = ((sz.L n : ℕ) : ℝ) ^ d * q ^ 6 := by
    rw [hP, hq, ← pow_mul, mul_comm d 6]
  have hW5 : q * ((sz.L n : ℕ) : ℝ) ^ d * P⁻¹ = (q⁻¹) ^ 5 := by
    rw [hPq]
    have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL0 d
    field_simp
  have hm5 : m ^ 5 ≤ m ^ ((1 : ℝ) / 2) * m ^ 4 := by
    have h1 : m ^ (1 : ℝ) ≤ m ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (by norm_num)
    rw [Real.rpow_one] at h1
    calc m ^ 5 = m * m ^ 4 := by ring
      _ ≤ m ^ ((1 : ℝ) / 2) * m ^ 4 := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hqm5 : (q⁻¹) ^ 5 ≤ m ^ ((1 : ℝ) / 2) * (e4 * T ^ 2) :=
    calc (q⁻¹) ^ 5 ≤ m ^ 5 := pow_le_pow_left₀ (by positivity) hqinv 5
      _ ≤ m ^ ((1 : ℝ) / 2) * m ^ 4 := hm5
      _ ≤ m ^ ((1 : ℝ) / 2) * (e4 * T ^ 2) := mul_le_mul_of_nonneg_left hlow hsq
  have hJJ : J ≤ (1 - u)⁻¹ * J ^ 3 := by
    have h1 : J ≤ J ^ 3 := le_self_pow₀ hJ1 (by norm_num)
    have h3 : 0 ≤ J ^ 3 := by positivity
    nlinarith
  have k2 : q * (((sz.L n : ℕ) : ℝ) ^ d * (2 * (32 * 3 ^ (d + 1) * Λ ^ 6 * J * P⁻¹))) ≤
      (2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * e4) *
        ((1 - u)⁻¹ * (m ^ ((1 : ℝ) / 2) * J ^ 3) * T ^ 2) := by
    have e : q * (((sz.L n : ℕ) : ℝ) ^ d * (2 * (32 * 3 ^ (d + 1) * Λ ^ 6 * J * P⁻¹))) =
        (2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * J) * (q * ((sz.L n : ℕ) : ℝ) ^ d * P⁻¹) := by ring
    rw [e, hW5]
    have hc : 0 ≤ 2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 := by positivity
    calc (2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * J) * (q⁻¹) ^ 5
        ≤ (2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * J) * (m ^ ((1 : ℝ) / 2) * (e4 * T ^ 2)) :=
          mul_le_mul_of_nonneg_left hqm5 (by positivity)
      _ = (2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * e4) * (m ^ ((1 : ℝ) / 2) * T ^ 2) * J := by ring
      _ ≤ (2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * e4) * (m ^ ((1 : ℝ) / 2) * T ^ 2) *
            ((1 - u)⁻¹ * J ^ 3) := by
          refine mul_le_mul_of_nonneg_left hJJ (by positivity)
      _ = _ := by ring
  have hA0 : 0 ≤ (1 - u)⁻¹ * T ^ 2 := by positivity
  have hB0 : 0 ≤ (1 - u)⁻¹ * (m ^ ((1 : ℝ) / 2) * J ^ 3) * T ^ 2 := by positivity
  calc ‖STeeM sz n E u M σ a a'‖
      ≤ q * (Λ * m ^ 5 * (2 * (9 ^ d * Lg ^ (2 * d))) +
        ((sz.L n : ℕ) : ℝ) ^ d * (2 * (32 * 3 ^ (d + 1) * Λ ^ 6 * J * P⁻¹))) := hsum
    _ = q * (Λ * m ^ 5 * (2 * (9 ^ d * Lg ^ (2 * d)))) +
        q * (((sz.L n : ℕ) : ℝ) ^ d * (2 * (32 * 3 ^ (d + 1) * Λ ^ 6 * J * P⁻¹))) := by ring
    _ ≤ (2 * 9 ^ d * Λ * Lg ^ (2 * d) * e4) * ((1 - u)⁻¹ * T ^ 2) +
        (2 * (32 * 3 ^ (d + 1)) * Λ ^ 6 * e4) *
          ((1 - u)⁻¹ * (m ^ ((1 : ℝ) / 2) * J ^ 3) * T ^ 2) := add_le_add k1 k2
    _ ≤ Φ * ((1 - u)⁻¹ * T ^ 2) +
        Φ * ((1 - u)⁻¹ * (m ^ ((1 : ℝ) / 2) * J ^ 3) * T ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_right hr1 hA0) (mul_le_mul_of_nonneg_right hr2 hB0)
    _ = _ := by ring

end Near

/-! ## 5. The far case `4ℓ* < |a₀ - a₁|_∞` (RBM2D §8 `:1378-1625`) -/

section Far

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Far case, the sum over `b, b'` (RBM2D `far_sum` `:1378`): with `ℓ* = (log W)^{3/2}`,
`κ = 2·9^d Λ J`, `S = e² e^{2Y}`, `T_d = T_{u,D}(|a₀ - a₁|)`, `M_u⁻¹ = m`,
`‖(ℰ⊗ℰ)^{M,(2)}‖ ≤ W^d (2 Q · 4 (2ℓ* + 3)^d + 2 κ³ S³ T_d (2 S_d + 1) m² T_d)`,
`Q = κ² S³ T_d² Λ m^{3/2}`; the sum of products of tails is `LemDecCalE_sum_tail_tail`. -/
private theorem lemDecCalEdif2_far_sum (h : E2HypDif sz n E u D Λ K₀ J M) (σ : Fin 2 → Bool)
    (a a' : Fin 2 → Zd d (sz.L n))
    (h1 : (zdistInf d (sz.L n) (a 0 - a' 0) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (h2 : (zdistInf d (sz.L n) (a 1 - a' 1) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (hd : 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) <
      (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)) :
    ‖STeeM sz n E u M σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
      (2 * ((2 * 9 ^ d * Λ * J) ^ 2 *
          (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ^ 2 *
          (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ ((3 : ℝ) / 2))) *
        (4 * (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 3) ^ d) +
      2 * ((2 * 9 ^ d * Λ * J) ^ 3 *
          (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)) *
        ((2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h.1
  have h2e := LemDecCalE_e2 h.1
  have hxu : 0 < 1 - u := by linarith
  have hW0 := lemDecCalEdif2_W_pos sz n
  have hL0 := lemDecCalEdif2_L_pos sz n
  have hlogW : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  have hd1 : 1 ≤ d := by have := h.1.1; omega
  have hfl := LemDecCalE_floor_A h.1
  have hTeq : ∀ r : ℝ, tailTD d ((sz.W n : ℕ) : ℝ) u D r =
      ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-Real.sqrt r) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    intro r; unfold tailTD; rw [abs_of_pos hxu]
  -- the convolution of the two tails
  have hconv : ∑ b : Zd d (sz.L n),
      tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - b) : ℝ) *
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (b - a 1) : ℝ) ≤
      (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := by
    have hA0 : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := sq_nonneg _
    have hw0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    have key := LemDecCalE_sum_tail_tail (d := d) (L := sz.L n) hd1 hA0 hw0 hfl (a 0) (a 1)
    rw [hTeq (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)]
    refine le_trans (le_of_eq ?_) key
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hTeq, hTeq, mul_comm]
  set ls : ℝ := Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hls
  set κ : ℝ := 2 * 9 ^ d * Λ * J with hκ
  set S : ℝ := Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with hS
  set Td : ℝ := tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) with hTd
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  set Q : ℝ := κ ^ 2 * S ^ 3 * Td ^ 2 * (Λ * m ^ ((3 : ℝ) / 2)) with hQ
  set Sd : ℝ := 2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1 with hSd
  set Ff : Zd d (sz.L n) → ℝ := fun b => 2 * (Q *
      ((if (zdistInf d (sz.L n) (a 0 - b) : ℝ) ≤ ls + 1 then 1 else 0) +
        (if (zdistInf d (sz.L n) (a' 0 - b) : ℝ) ≤ ls + 1 then 1 else 0) +
        (if (zdistInf d (sz.L n) (a 1 - b) : ℝ) ≤ ls + 1 then 1 else 0) +
        (if (zdistInf d (sz.L n) (a' 1 - b) : ℝ) ≤ ls + 1 then 1 else 0))) +
      2 * (κ ^ 3 * S ^ 3 * Td * tailTD d ((sz.W n : ℕ) : ℝ) u D
          (zdistInf d (sz.L n) (a 0 - b) : ℝ) *
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (b - a 1) : ℝ)) with hFf
  have hd' : 4 * ls < (zdistInf d (sz.L n) (a 1 - a 0) : ℝ) := by
    rw [lemDecCalEdif2_zd_comm]; exact hd
  have hper : ∀ b b' : Zd d (sz.L n), zdistInf d (sz.L n) (b - b') ≤ 1 →
      ‖STLM sz n E u M ![σ 0, σ 1, σ 0, !σ 0, !σ 1, !σ 0] ![a 0, a 1, b', a' 1, a' 0, b]‖ +
        ‖STLM sz n E u M ![σ 1, σ 0, σ 1, !σ 1, !σ 0, !σ 1] ![a 1, a 0, b', a' 0, a' 1, b]‖ ≤
        Ff b := by
    intro b b' hb
    have hb' : (zdistInf d (sz.L n) (b - b') : ℝ) ≤ 1 := by exact_mod_cast hb
    have c1 := LemDecCalEdif_cut_far h (σ 0) (σ 1) (a 0) (a 1) (a' 0) (a' 1) b b' h1 h2 hb' hd
    have c2 := LemDecCalEdif_cut_far h (σ 1) (σ 0) (a 1) (a 0) (a' 1) (a' 0) b b' h2 h1 hb' hd'
    have eT1 : tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 1 - a 0) : ℝ) = Td := by
      rw [hTd, lemDecCalEdif2_zd_comm d (sz.L n) (a 1) (a 0)]
    have eT2 : tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 1 - b) : ℝ) =
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (b - a 1) : ℝ) := by
      rw [lemDecCalEdif2_zd_comm d (sz.L n) (a 1) b]
    have eT3 : tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (b - a 0) : ℝ) =
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - b) : ℝ) := by
      rw [lemDecCalEdif2_zd_comm d (sz.L n) b (a 0)]
    rw [eT1, eT2, eT3] at c2
    simp only [hFf]
    linarith [c1, c2]
  have hsum : ‖STeeM sz n E u M σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ b : Zd d (sz.L n), Ff b := by
    refine (LemDecCalEdif_STeeM_le sz n E u M σ a a').trans ?_
    gcongr with b
    exact lemDecCalEdif2_sum_SB_le (sz.three_le_L n) (sz.lam n) b _ (Ff b)
      (fun b' hb => hper b b' hb)
  have hcnt : ∀ c : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      (if (zdistInf d (sz.L n) (c - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0) ≤ (2 * ls + 3) ^ d := by
    intro c
    have hls0 : 0 ≤ ls := Real.rpow_nonneg hlogW _
    refine (lemDecCalEdif2_count_le c (ls + 1) (by linarith)).trans (le_of_eq ?_)
    rw [show 2 * (ls + 1) + 1 = 2 * ls + 3 by ring]
  have hsplit : ∑ b : Zd d (sz.L n), Ff b = 2 * (Q *
      (∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a 0 - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0) +
        ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a' 0 - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0) +
        ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a 1 - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0) +
        ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a' 1 - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0))) +
      2 * (κ ^ 3 * S ^ 3 * Td) * ∑ b : Zd d (sz.L n),
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - b) : ℝ) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (b - a 1) : ℝ) := by
    simp only [hFf, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine congrArg₂ _ rfl (Finset.sum_congr rfl fun b _ => by ring)
  have hm0 : 0 ≤ m := inv_nonneg.2 (by linarith [h2e.1])
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ J := by linarith
    have : 0 ≤ Td := tailTD_nonneg hW0.le
    have := Real.rpow_nonneg hm0 ((3 : ℝ) / 2)
    positivity
  have hk0 : 0 ≤ 2 * (κ ^ 3 * S ^ 3 * Td) := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ J := by linarith
    have : 0 ≤ Td := tailTD_nonneg hW0.le
    positivity
  have hsumF : ∑ b : Zd d (sz.L n), Ff b ≤ 2 * Q * (4 * (2 * ls + 3) ^ d) +
      2 * (κ ^ 3 * S ^ 3 * Td) * (Sd * m ^ 2 * Td) := by
    rw [hsplit]
    have e1 := hcnt (a 0)
    have e2 := hcnt (a' 0)
    have e3 := hcnt (a 1)
    have e4 := hcnt (a' 1)
    have hs4 : ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a 0 - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0) +
        ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a' 0 - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0) +
        ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a 1 - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0) +
        ∑ b : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a' 1 - b) : ℝ) ≤ ls + 1 then (1 : ℝ) else 0) ≤
        4 * (2 * ls + 3) ^ d := by linarith
    have k1 := mul_le_mul_of_nonneg_left hs4 hQ0
    have k2 := mul_le_mul_of_nonneg_left hconv hk0
    linarith
  exact hsum.trans (mul_le_mul_of_nonneg_left hsumF (by positivity))

/-- **Far case** `4ℓ* < |a₀ - a₁|_∞`: `‖(ℰ⊗ℰ)^{M,(2)}‖ ≤ lossE2dif · (1-u)⁻¹ M_u^{-1/2} J³ T²`
(RBM2D `far_case` `:1538` has two terms `η_u⁻¹ ρ³ M_u^{-1/2} J² + η_v⁻¹ M_v⁻¹ J³`; here
`J² ≤ J³` and `M_u⁻¹ ≤ M_u^{-1/2}` merge them into the single pinned term). -/
private theorem lemDecCalEdif2_far_case (h : E2HypDif sz n E u D Λ K₀ J M) (σ : Fin 2 → Bool)
    (a a' : Fin 2 → Zd d (sz.L n))
    (h1 : (zdistInf d (sz.L n) (a 0 - a' 0) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (h2 : (zdistInf d (sz.L n) (a 1 - a' 1) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (hd : 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) <
      (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)) :
    ‖STeeM sz n E u M σ a a'‖ ≤ lossE2dif d (sz.L n) (sz.W n) Λ K₀ *
      ((1 - u)⁻¹ * (0 + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) *
        STtailTD sz n u D a ^ 2) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h.1
  have h2e := LemDecCalE_e2 h.1
  have hsum := lemDecCalEdif2_far_sum h σ a a' h1 h2 hd
  have hrows := lemDecCalEdif2_rows_far h.1
  have hW0 := lemDecCalEdif2_W_pos sz n
  have hxu : 0 < 1 - u := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ3 : J ^ (3 : ℝ) = J ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hST : STtailTD sz n u D a =
      tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := rfl
  rw [abs_of_pos hxu, hJ3, hST, zero_add]
  have hq0 : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
  have hMu : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith [h2e.1]
  set q : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hq
  set m : ℝ := (q * (1 - u))⁻¹ with hm
  set ls : ℝ := Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hls
  set S : ℝ := Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with hS
  set T : ℝ := tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hT
  set Φ : ℝ := lossE2dif d (sz.L n) (sz.W n) Λ K₀ with hΦ
  have hm0 : 0 < m := inv_pos.2 hMu
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ h2e.1
  have hqm : q * m = (1 - u)⁻¹ := by rw [hm]; field_simp
  have hinvu : 0 < (1 - u)⁻¹ := inv_pos.2 hxu
  have hq32 : q * m ^ ((3 : ℝ) / 2) = (1 - u)⁻¹ * m ^ ((1 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hm0, Real.rpow_one,
      ← mul_assoc, hqm]
  have hmle : m ≤ m ^ ((1 : ℝ) / 2) := by
    have h1 : m ^ (1 : ℝ) ≤ m ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (by norm_num)
    rwa [Real.rpow_one] at h1
  have hsq : 0 ≤ m ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hm0.le _
  have hT0 : 0 ≤ T := tailTD_nonneg hW0.le
  have hJJ : J ^ 2 ≤ J ^ 3 := pow_le_pow_right₀ hJ1 (by norm_num)
  have hS0 : 0 ≤ S := by positivity
  have hC0 : 0 ≤ (2 * ls + 3) ^ d := by
    have : 0 ≤ ls := Real.rpow_nonneg (by linarith) _
    positivity
  have hSd0 : 0 ≤ 2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1 := by positivity
  set B : ℝ := (1 - u)⁻¹ * (m ^ ((1 : ℝ) / 2) * J ^ 3) * T ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  -- the two parts of the sum
  have kA : q * (2 * ((2 * 9 ^ d * Λ * J) ^ 2 * S ^ 3 * T ^ 2 * (Λ * m ^ ((3 : ℝ) / 2))) *
      (4 * (2 * ls + 3) ^ d)) ≤
      (8 * (2 * ls + 3) ^ d * (2 * 9 ^ d) ^ 2 * Λ ^ 3 * S ^ 3) * B := by
    have e : q * (2 * ((2 * 9 ^ d * Λ * J) ^ 2 * S ^ 3 * T ^ 2 * (Λ * m ^ ((3 : ℝ) / 2))) *
        (4 * (2 * ls + 3) ^ d)) =
        (8 * (2 * ls + 3) ^ d * (2 * 9 ^ d) ^ 2 * Λ ^ 3 * S ^ 3) *
          (J ^ 2 * ((1 - u)⁻¹ * m ^ ((1 : ℝ) / 2) * T ^ 2)) := by
      rw [← hq32]; ring
    rw [e, hB]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc J ^ 2 * ((1 - u)⁻¹ * m ^ ((1 : ℝ) / 2) * T ^ 2)
        ≤ J ^ 3 * ((1 - u)⁻¹ * m ^ ((1 : ℝ) / 2) * T ^ 2) :=
          mul_le_mul_of_nonneg_right hJJ (by positivity)
      _ = _ := by ring
  have kB : q * (2 * ((2 * 9 ^ d * Λ * J) ^ 3 * S ^ 3 * T) *
      ((2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * m ^ 2 * T)) ≤
      (2 * (2 * 9 ^ d) ^ 3 * (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * Λ ^ 3 * S ^ 3) * B := by
    have e : q * (2 * ((2 * 9 ^ d * Λ * J) ^ 3 * S ^ 3 * T) *
        ((2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * m ^ 2 * T)) =
        (2 * (2 * 9 ^ d) ^ 3 * (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * Λ ^ 3 * S ^ 3) *
          (J ^ 3 * ((1 - u)⁻¹ * m * T ^ 2)) := by
      rw [← hqm]; ring
    rw [e, hB]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc J ^ 3 * ((1 - u)⁻¹ * m * T ^ 2) ≤ J ^ 3 * ((1 - u)⁻¹ * m ^ ((1 : ℝ) / 2) * T ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmle hinvu.le) (by positivity)) (by positivity)
      _ = _ := by ring
  calc ‖STeeM sz n E u M σ a a'‖
      ≤ q * (2 * ((2 * 9 ^ d * Λ * J) ^ 2 * S ^ 3 * T ^ 2 * (Λ * m ^ ((3 : ℝ) / 2))) *
          (4 * (2 * ls + 3) ^ d) +
        2 * ((2 * 9 ^ d * Λ * J) ^ 3 * S ^ 3 * T) *
          ((2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * m ^ 2 * T)) := hsum
    _ = q * (2 * ((2 * 9 ^ d * Λ * J) ^ 2 * S ^ 3 * T ^ 2 * (Λ * m ^ ((3 : ℝ) / 2))) *
          (4 * (2 * ls + 3) ^ d)) +
        q * (2 * ((2 * 9 ^ d * Λ * J) ^ 3 * S ^ 3 * T) *
          ((2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * m ^ 2 * T)) := by ring
    _ ≤ (8 * (2 * ls + 3) ^ d * (2 * 9 ^ d) ^ 2 * Λ ^ 3 * S ^ 3) * B +
        (2 * (2 * 9 ^ d) ^ 3 * (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * Λ ^ 3 * S ^ 3) * B :=
        add_le_add kA kB
    _ = (8 * (2 * ls + 3) ^ d * (2 * 9 ^ d) ^ 2 * Λ ^ 3 * S ^ 3 +
        2 * (2 * 9 ^ d) ^ 3 * (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * Λ ^ 3 * S ^ 3) * B := by
        ring
    _ ≤ Φ * B := mul_le_mul_of_nonneg_right hrows hB0
    _ = _ := by rw [hB]

end Far

/-! ## 6. The theorem (RBM2D §9 `:1632`) -/

section Main

/-- **`res_deccalE_dif`** (`3_5:2327-2334`), deterministic at one time `u`, for every `σ ∈ {±}²` and
every `a'` with `|a_i - a'_i|_∞ ≤ (log W)^{3/2}`: near case `lemDecCalEdif2_near_case` (the indicator is `1`),
far case `lemDecCalEdif2_far_case` (the indicator is `0`).  The type is the merged pin `LemDecCalE_dif d`
(`Path/LemDecCalEdif.lean:80`), proved for every `d` (`E2HypDif` carries `3 ≤ d`). -/
theorem lemDecCalE_dif (d : ℕ) : LemDecCalE_dif d := by
  intro sz n E u D Λ K₀ J M h σ a a' hr
  by_cases hn : (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤
      4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
  · simp only [hn, ↓reduceIte]
    exact lemDecCalEdif2_near_case h σ a a' hn
  · simp only [hn, ↓reduceIte]
    exact lemDecCalEdif2_far_case h σ a a' (hr 0) (hr 1) (lt_of_not_ge hn)

end Main

/-! ## 7. Nondegenerate instances at `d = 3` -/

section Instance

open RBM.Gauss.SizesInst RBM.Gauss.Step5Inst

/-- The right side of `LemDecCalE_dif` is positive under `E2Hyp` and `J ≥ 1`, for every value
of the indicator in `[0, ∞)` and every tail argument. -/
private theorem lemDecCalEdif2_R_pos {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (h : E2Hyp sz n E u D Λ K₀ J M) {ind : ℝ} (hind : 0 ≤ ind) (x : ℝ) :
    0 < lossE2dif d (sz.L n) (sz.W n) Λ K₀ *
      ((1 - u)⁻¹ * (ind + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) *
        tailTD d ((sz.W n : ℕ) : ℝ) u D x ^ 2) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif2_basic h
  have h2 := LemDecCalE_e2 h
  have hW0 := lemDecCalEdif2_W_pos sz n
  have hxu : 0 < 1 - u := by linarith
  have hloss := lemDecCalEdif2_loss_ge h
  obtain ⟨-, hlogW, -, hLg0, -, -⟩ := lemDecCalEdif2_facts h
  have hZ : 0 < 10 ^ 12 * ((1600 * (d : ℝ) ^ 4) ^ d * 729 ^ d *
      (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) * Λ ^ 6 *
      Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) := by
    have hd1 : (0 : ℝ) < d := by exact_mod_cast (by have := h.1; omega : 0 < d)
    have hΛ0 : 0 < Λ := by linarith
    have h1 : 0 < 1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
      linarith
    positivity
  have hΦ := lt_of_lt_of_le hZ hloss
  have hMu : 0 < ((sz.W n : ℕ) : ℝ) ^ d * |1 - u| := by
    rw [abs_of_pos hxu]; have := pow_pos hW0 d; linarith [h2.1]
  have hJ0 : 0 < J := by linarith
  have hX : 0 < (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos (inv_pos.2 hMu) _) (Real.rpow_pos_of_pos hJ0 _)
  have hT : 0 < tailTD d ((sz.W n : ℕ) : ℝ) u D x := by
    unfold tailTD
    exact add_pos_of_nonneg_of_pos (by positivity) (Real.rpow_pos_of_pos hW0 _)
  exact mul_pos hΦ (mul_pos (mul_pos (inv_pos.2 hxu) (by linarith)) (pow_pos hT 2))

/-- `|0 - e₁|_∞ = 1` in `Z_8³`. -/
private theorem lemDecCalEdif2_inst_dist_a :
    zdistInf 3 (sz0.L 1) ((0 : Zd 3 (sz0.L 1)) - Pi.single 0 1) = 1 := by
  unfold zdistInf
  decide

/-- The periodic `L^∞` distance of `e = 300 · e₁` to `0` in `Z_L³`, `L = 2 · 24⁵`
(`LemDecCalEdif.lean:1560`). -/
private theorem lemDecCalEdif2_inst_dist :
    zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - Pi.single 0 300) = 300 := by
  unfold zdistInf
  decide

/-- `|0 - e₂|_∞ = 1` in `Z_L³`, `L = 2 · 24⁵`. -/
private theorem lemDecCalEdif2_inst_dist' :
    zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - Pi.single 1 1) = 1 := by
  unfold zdistInf
  decide

/-- `4 (log W)^{3/2} < 300` for `W = 2^24` (`LemDecCalEdif.lean:1576`). -/
private theorem lemDecCalEdif2_inst_ell :
    4 * Real.log ((szCL.W 0 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) < 300 := by
  rw [szCL_log_W]
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  set x : ℝ := ((0 : ℕ) : ℝ) + 24 with hx
  set y : ℝ := x * Real.log 2 with hy
  have hy0 : 0 < y := by rw [hy, hx]; norm_num; positivity
  have hy1 : y < 16.64 := by rw [hy, hx]; norm_num; linarith
  have h32 : y ^ ((3 : ℝ) / 2) = y * Real.sqrt y := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [h32]
  have hs : Real.sqrt y < 4.08 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  have := Real.sqrt_nonneg y
  nlinarith

/-- **Instance (a), near branch**: `lemDecCalE_dif 3` at T2171's `LemDecCalEdif_inst_a` (`sz0`, `n = 1`: `L = 8`,
`W = 1024`, `E = 1/2`, `u = 0`, `D = 38`, `Λ = K₀ = J = 1`, `M = 0`), `σ = (+,+)`, `a = a' = (0, e₁)`
(`|a₀ - a₁|_∞ = 1 ≤ 4 (log 1024)^{3/2} ≈ 73.0`); `R` is the right side of the pin at these data, and `R > 0`. -/
example :
  let a : Fin 2 → Zd 3 (sz0.L 1) := ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]
  let R : ℝ := lossE2dif 3 (sz0.L 1) (sz0.W 1) 1 1 *
    ((1 - (0 : ℝ))⁻¹ *
      ((if ((zdistInf 3 (sz0.L 1) (a 0 - a 1) : ℕ) : ℝ) ≤
            4 * Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
        (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 : ℝ)) *
      STtailTD sz0 1 0 38 a ^ 2)
  0 < R ∧
    ‖STeeM sz0 1 (1 / 2) 0
        (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true] a a‖ ≤ R := by
  intro a R
  have hI := LemDecCalEdif_inst_a
  obtain ⟨-, hlogW, hlog4, -, -, -⟩ := lemDecCalEdif2_facts hI.1
  have hls : (0 : ℝ) ≤ Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hlogW _
  have hrange : ∀ i : Fin 2, ((zdistInf 3 (sz0.L 1) (a i - a i) : ℕ) : ℝ) ≤
      Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
    intro i
    rw [sub_self, lemDecCalEdif2_zd_zero, Nat.cast_zero]
    exact hls
  -- the near branch: `|a₀ - a₁|_∞ = 1 ≤ 4 (log W)^{3/2}`, so the indicator is `1`
  have hbr : ((zdistInf 3 (sz0.L 1) (a 0 - a 1) : ℕ) : ℝ) ≤
      4 * Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
    have hd : zdistInf 3 (sz0.L 1) (a 0 - a 1) = 1 := lemDecCalEdif2_inst_dist_a
    have h1 : Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (1 : ℝ) ≤
        Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at h1
    rw [hd]
    push_cast
    linarith
  refine ⟨?_, lemDecCalE_dif 3 sz0 1 (1 / 2) 0 38 1 1 1 _ hI ![true, true] a a hrange⟩
  have hR := lemDecCalEdif2_R_pos (J := 1) hI.1 (ind := 1) zero_le_one
    ((zdistInf 3 (sz0.L 1) (a 0 - a 1) : ℕ) : ℝ)
  simp only [R, hbr, ↓reduceIte]
  exact hR

/-- **Instance (b), far branch**: `lemDecCalE_dif 3` at T2171's `LemDecCalEdif_inst_b` (`szCL`, `n = 0`:
`L = 2·24⁵`, `W = 2^24`, `E = 1/2`, `u = 0`, `D = 42`, `Λ = K₀ = J = 1`, `M = 0`), `σ = (+,-)`, `a = (0, 300 e₁)`,
`a' = (e₂, 300 e₁)` (`|a₀ - a₁|_∞ = 300 > 4 (24 log 2)^{3/2} ≈ 271.4`, `|a₀ - a'₀|_∞ = 1 ≤ (24 log 2)^{3/2}`,
`|a₁ - a'₁|_∞ = 0`); `R` is the right side of the pin at these data, and `R > 0`. -/
example :
  let a : Fin 2 → Zd 3 (szCL.L 0) := ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 300]
  let a' : Fin 2 → Zd 3 (szCL.L 0) := ![(Pi.single 1 1 : Zd 3 (szCL.L 0)), Pi.single 0 300]
  let R : ℝ := lossE2dif 3 (szCL.L 0) (szCL.W 0) 1 1 *
    ((1 - (0 : ℝ))⁻¹ *
      ((if ((zdistInf 3 (szCL.L 0) (a 0 - a 1) : ℕ) : ℝ) ≤
            4 * Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
        (((szCL.W 0 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 : ℝ)) *
      STtailTD szCL 0 0 42 a ^ 2)
  0 < R ∧
    ‖STeeM szCL 0 (1 / 2) 0
        (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ) ![true, false] a a'‖ ≤ R := by
  intro a a' R
  have hI := LemDecCalEdif_inst_b
  have hone := szCL_one_le_log_W 0
  have hls1 : (1 : ℝ) ≤ Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
    have h1 : Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (1 : ℝ) ≤
        Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
    rw [Real.rpow_one] at h1
    exact hone.trans h1
  have hrange : ∀ i : Fin 2, ((zdistInf 3 (szCL.L 0) (a i - a' i) : ℕ) : ℝ) ≤
      Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
    intro i
    fin_cases i
    · have hd : zdistInf 3 (szCL.L 0) (a 0 - a' 0) = 1 := lemDecCalEdif2_inst_dist'
      change ((zdistInf 3 (szCL.L 0) (a 0 - a' 0) : ℕ) : ℝ) ≤ _
      rw [hd]; exact_mod_cast hls1
    · change ((zdistInf 3 (szCL.L 0) (a 1 - a' 1) : ℕ) : ℝ) ≤ _
      have h0 : a 1 - a' 1 = 0 := sub_self _
      rw [h0, lemDecCalEdif2_zd_zero, Nat.cast_zero]
      linarith
  -- the far branch: `|a₀ - a₁|_∞ = 300 > 4 (log W)^{3/2}`, so the indicator is `0`
  have hbr : ¬ ((zdistInf 3 (szCL.L 0) (a 0 - a 1) : ℕ) : ℝ) ≤
      4 * Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
    have hd : zdistInf 3 (szCL.L 0) (a 0 - a 1) = 300 := lemDecCalEdif2_inst_dist
    rw [hd, not_le]
    push_cast
    exact_mod_cast lemDecCalEdif2_inst_ell
  refine ⟨?_, lemDecCalE_dif 3 szCL 0 (1 / 2) 0 42 1 1 1 _ hI ![true, false] a a' hrange⟩
  have hR := lemDecCalEdif2_R_pos (J := 1) hI.1 (ind := 0) le_rfl
    ((zdistInf 3 (szCL.L 0) (a 0 - a 1) : ℕ) : ℝ)
  simp only [R, hbr, ↓reduceIte]
  exact hR

end Instance

end RBM.Path

end
