/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Prop5Short

/-!
# The kernel `K = M^{(+,-)}` of the block Anderson model

`K_ab = |M^{(B)}_{ab}|²` as the real matrix `BAK d L g E m`
((2.59) `eq:Msig`, Subappendix A.1 `sec:pf_propTH`).  Proved unconditionally from
`Ward.lean`, `CombesThomas.lean`, `Prop5Short.lean`: symmetry and translation invariance,
the bridge to `BAMss`/`BATheta`, double stochasticity ((8.5) `eq:WardM`), laziness
`K_aa = |m|²`, the Markov facts for the powers `K^n`, the exponential tails (squares of
(8.6) `Mbound_AO`, (8.7) `Mbound_AO2` and `BAMB_sq_off_le`), the exponential moment `Σ_b K_ab e^{μ|a-b|}`
uniformly in `L`, the neighbour lower bound (8.6) `Mbound_AO` (small `g`) and, for every `g > 0`, the
neighbour-sum identity `Σ_{b∼a} M_ab = (1 + (E+m)m)/g` with the lower bound
`Σ_{b∼a} K_ab ≥ (κ(1-|m|²))²/(8dg²)`.

No law, no flow time except in the bridge `BATheta_pm_eq`; constants `C, c, A, S` are
`BAct_C`, `BAct_rate`, `BAp5s_A`, `BAp5s_S` (functions of `(d, Λ, κ)` only).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section

open Matrix

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The kernel, symmetries, bridges -/

section Kernel

variable (d L : ℕ) [NeZero L]

/-- The kernel `K = M^{(+,-)}` of the block Anderson model as a real matrix: `K_ab = |M^{(B)}_ab|²`
(`M^{(+,-)}_{ab} = M_{ba} conj(M_{ab})`, (2.59) `eq:Msig`; `M` symmetric), at the real-axis
data `(g, E, m)` of `BATheta`. -/
noncomputable def BAK (g E : ℝ) (m : ℂ) : Matrix (Zd d L) (Zd d L) ℝ :=
  Matrix.of fun a b => ‖BAMB d L g (E : ℂ) m a b‖ ^ 2

theorem BAK_apply (g E : ℝ) (m : ℂ) (a b : Zd d L) :
    BAK d L g E m a b = ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 := rfl

theorem BAK_nonneg (g E : ℝ) (m : ℂ) (a b : Zd d L) : 0 ≤ BAK d L g E m a b := by
  rw [BAK_apply]; positivity

theorem BAK_symm (g E : ℝ) (m : ℂ) (a b : Zd d L) :
    BAK d L g E m a b = BAK d L g E m b a := by
  rw [BAK_apply, BAK_apply, BAMB_symm d L g (E : ℂ) m a b]

theorem BAK_transpose (g E : ℝ) (m : ℂ) :
    Matrix.transpose (BAK d L g E m) = BAK d L g E m := by
  ext a b
  exact (BAK_symm d L g E m a b).symm

theorem BAK_shift (g E : ℝ) (m : ℂ) (a b r : Zd d L) :
    BAK d L g E m (a + r) (b + r) = BAK d L g E m a b := by
  rw [BAK_apply, BAK_apply, BAMB_shift d L g (E : ℂ) m a b r]

theorem BAK_zero_neg (g E : ℝ) (m : ℂ) (a : Zd d L) :
    BAK d L g E m 0 (-a) = BAK d L g E m 0 a := by
  have h := BAK_shift d L g E m 0 (-a) a
  rw [zero_add, neg_add_cancel] at h
  rw [← h, BAK_symm d L g E m a 0]

private theorem BKK_norm_sigma (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b‖ = ‖BAMB d L g (E : ℂ) m a b‖ := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.norm_conj]
    rw [BAMB_symm d L g (E : ℂ) m b a]
  · simp only [BAMsigma, ite_true]

theorem BAMss_pm_eq (g E : ℝ) (m : ℂ) :
    BAMss d L (BAMB d L g (E : ℂ) m) true false = Matrix.map (BAK d L g E m) Complex.ofReal := by
  ext a b
  simp only [BAMss, BAMsigma, Matrix.of_apply, ite_true, Bool.false_eq_true, ite_false,
    Matrix.conjTranspose_apply, Matrix.map_apply, BAK_apply]
  rw [BAMB_symm d L g (E : ℂ) m a b, Complex.star_def, Complex.mul_conj']
  push_cast
  rfl

theorem BAMss_mp_eq (g E : ℝ) (m : ℂ) :
    BAMss d L (BAMB d L g (E : ℂ) m) false true = Matrix.map (BAK d L g E m) Complex.ofReal := by
  ext a b
  simp only [BAMss, BAMsigma, Matrix.of_apply, ite_true, Bool.false_eq_true, ite_false,
    Matrix.conjTranspose_apply, Matrix.map_apply, BAK_apply]
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem BAMss_norm_eq_BAK (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b‖ = BAK d L g E m a b := by
  simp only [BAMss, Matrix.of_apply, norm_mul, BKK_norm_sigma, BAK_apply]
  rw [BAMB_symm d L g (E : ℂ) m b a, sq]

theorem BATheta_pm_eq (g E : ℝ) (m : ℂ) (t : ℝ) :
    BATheta d L g E m t true false = PropThetaQ (Matrix.map (BAK d L g E m) Complex.ofReal) t := by
  unfold BATheta
  rw [BAMss_pm_eq]

end Kernel

/-! ## 2. The Ward layer: laziness and double stochasticity -/

section Ward

variable (d L : ℕ) [NeZero L]

theorem BAK_diag (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) :
    BAK d L g E m a a = ‖m‖ ^ 2 := by
  rw [BAK_apply, BAMB_diag_eq d L g (E : ℂ) m h a]

theorem BAK_row_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) :
    ∑ b, BAK d L g E m a b = 1 :=
  BAMB_row_sq_real d L g E m h a

theorem BAK_col_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (b : Zd d L) :
    ∑ a, BAK d L g E m a b = 1 := by
  rw [← BAK_row_sum d L g E m h b]
  exact Finset.sum_congr rfl fun a _ => BAK_symm d L g E m a b

/-! ## 3. Powers of `K` -/

theorem BAK_pow_nonneg (g E : ℝ) (m : ℂ) (n : ℕ) (a b : Zd d L) : 0 ≤ (BAK d L g E m ^ n) a b := by
  induction n generalizing a b with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (ih a c) (BAK_nonneg d L g E m c b)

theorem BAK_pow_row_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (n : ℕ) (a : Zd d L) :
    ∑ b, (BAK d L g E m ^ n) a b = 1 := by
  induction n with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    rw [Finset.sum_ite_eq]
    simp
  | succ n ih =>
    rw [pow_succ]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, BAK_row_sum d L g E m h, mul_one]
    exact ih

theorem BAK_pow_transpose (g E : ℝ) (m : ℂ) (n : ℕ) :
    Matrix.transpose (BAK d L g E m ^ n) = BAK d L g E m ^ n := by
  rw [Matrix.transpose_pow, BAK_transpose]

theorem BAK_pow_shift (g E : ℝ) (m : ℂ) (n : ℕ) (a b r : Zd d L) :
    (BAK d L g E m ^ n) (a + r) (b + r) = (BAK d L g E m ^ n) a b := by
  induction n generalizing a b with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, add_left_inj]
  | succ n ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [← Equiv.sum_comp (Equiv.addRight r) (fun c => (BAK d L g E m ^ n) (a + r) c * BAK d L g E m c (b + r))]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Equiv.coe_addRight]
    rw [ih a c, BAK_shift]

end Ward

/-! ## 4. Exponential tails and the exponential moment -/

section Tails

variable (d L : ℕ) [NeZero L]

/-- Exponential tails for every `0 < g ≤ Λ`: `K_ab ≤ A g² e^{-2c|a-b|}` off the diagonal
(`BAMB_sq_off_le` in `K` form; `A = BAp5s_A d Λ κ`, `c = BAct_rate d Λ κ`). -/
theorem BAK_off_le (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a b : Zd d L) (hab : a ≠ b) :
    BAK d L g E m a b
      ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) :=
  BAMB_sq_off_le d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr a b hab

/-- The exponential moment of the kernel, uniformly in `L` (`2 ≤ d`): for `0 ≤ μ ≤ c`,
`Σ_b K_ab e^{μ|a-b|} ≤ |m|² + A g² S`, `S = BAp5s_S d Λ κ = expC (d-2) c`. -/
theorem BAK_exp_moment_le (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hμc : μ ≤ BAct_rate d Λ κ) (a : Zd d L) :
    ∑ b, BAK d L g E m a b * Real.exp (μ * (zdistD d L (a - b) : ℝ))
      ≤ ‖m‖ ^ 2 + BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ := by
  have hd0 : 0 < d := by omega
  have hc := BAct_rate_pos d Λ κ hd0 hΛ hκ
  have hA : 0 ≤ BAp5s_A d Λ κ := by unfold BAp5s_A; positivity
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
  have hdiag : BAK d L g E m a a * Real.exp (μ * (zdistD d L (a - a) : ℝ)) = ‖m‖ ^ 2 := by
    rw [sub_self, zdistD_zero, BAK_diag d L g E m hr.1 a]
    simp
  rw [hdiag]
  refine add_le_add le_rfl ?_
  have hterm : ∀ b ∈ Finset.univ.erase a,
      BAK d L g E m a b * Real.exp (μ * (zdistD d L (a - b) : ℝ))
        ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) := by
    intro b hb
    have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
    have h1 := BAK_off_le d L hL hd0 Λ g κ E m hΛ hg hgΛ hκ hr a b hab
    have hr0 : (0 : ℝ) ≤ (zdistD d L (a - b) : ℝ) := Nat.cast_nonneg _
    calc BAK d L g E m a b * Real.exp (μ * (zdistD d L (a - b) : ℝ))
        ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)))
            * Real.exp (μ * (zdistD d L (a - b) : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = BAp5s_A d Λ κ * g ^ 2
            * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)) + μ * (zdistD d L (a - b) : ℝ)) := by
          rw [Real.exp_add, mul_assoc]
      _ ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right hμc hr0]
  calc ∑ b ∈ Finset.univ.erase a, BAK d L g E m a b * Real.exp (μ * (zdistD d L (a - b) : ℝ))
      ≤ ∑ b ∈ Finset.univ.erase a,
          BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ b : Zd d L,
          BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)
    _ = BAp5s_A d Λ κ * g ^ 2 * ∑ b : Zd d L, Real.exp (-(BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ :=
        mul_le_mul_of_nonneg_left (BAsum_exp_decay_le d L hd _ hc a) (by positivity)

end Tails

/-! ## 5. The neighbour lower bounds -/

section Neighbour

variable (d L : ℕ) [NeZero L]

/-- The neighbour-sum identity, every `g > 0`: `Σ_{b∼a} M_ab = (1 + (E+m)m)/g`
(the diagonal entry of `(gΨ - E - m) M = 1`, with `M_aa = m` and `M_ca = M_ac`). -/
theorem BAMB_adj_sum (g E : ℝ) (m : ℂ) (hg : 0 < g) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) :
    ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L a b), BAMB d L g (E : ℂ) m a b
      = (1 + ((E : ℂ) + m) * m) / (g : ℂ) := by
  have hz : ((E : ℂ) + m).im ≠ 0 := by
    have : ((E : ℂ) + m).im = m.im := by simp
    rw [this]; exact h.1.ne'
  have hrow := BAMB_resolvent_row d L g (E : ℂ) m hz a a
  simp only [↓reduceIte] at hrow
  rw [BAMB_diag_eq d L g (E : ℂ) m h a] at hrow
  have hsym : ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c), BAMB d L g (E : ℂ) m c a
      = ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c), BAMB d L g (E : ℂ) m a c :=
    Finset.sum_congr rfl fun c _ => BAMB_symm d L g (E : ℂ) m c a
  rw [hsym] at hrow
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hg.ne')]
  linear_combination hrow

end Neighbour

/-- The scalar lower bound `(κ/2)(1 - |m|²) ≤ |1 + (E+m)m|` for `κ ≤ Im m`, `|m| ≤ 1`
(`1 + (E+m)m = (1 - |m|²) + u Re m + i u Im m`, `u = E + 2 Re m`; split on `|u| ≤ (1-|m|²)/2`). -/
theorem BAone_add_wm_ge (κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hκm : κ ≤ m.im) (hm : ‖m‖ ≤ 1) :
    κ / 2 * (1 - ‖m‖ ^ 2) ≤ ‖1 + ((E : ℂ) + m) * m‖ := by
  have hn : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs : 0 ≤ 1 - (m.re ^ 2 + m.im ^ 2) := by
    have := pow_le_one₀ (norm_nonneg m) hm (n := 2)
    linarith
  have hre : (1 + ((E : ℂ) + m) * m).re = (1 - (m.re ^ 2 + m.im ^ 2)) + (E + 2 * m.re) * m.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im]
    ring
  have him : (1 + ((E : ℂ) + m) * m).im = (E + 2 * m.re) * m.im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.ofReal_re, Complex.add_re,
      Complex.ofReal_im]
    ring
  have hp1 : |m.re| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hq1 : m.im ≤ 1 := by nlinarith
  have hq0 : 0 < m.im := lt_of_lt_of_le hκ hκm
  have hκ1 : κ ≤ 1 := hκm.trans hq1
  rw [hn]
  by_cases hu : |E + 2 * m.re| ≤ (1 - (m.re ^ 2 + m.im ^ 2)) / 2
  · have h1 : |(E + 2 * m.re) * m.re| ≤ (1 - (m.re ^ 2 + m.im ^ 2)) / 2 := by
      rw [abs_mul]
      calc |E + 2 * m.re| * |m.re| ≤ |E + 2 * m.re| * 1 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hu
    have h2 := (abs_le.mp h1).2
    have h3 := (abs_le.mp h1).1
    have h4 : (1 + ((E : ℂ) + m) * m).re ≤ ‖1 + ((E : ℂ) + m) * m‖ := Complex.re_le_norm _
    rw [hre] at h4
    nlinarith
  · have hu := not_le.mp hu
    have h1 : |(1 + ((E : ℂ) + m) * m).im| ≤ ‖1 + ((E : ℂ) + m) * m‖ := Complex.abs_im_le_norm _
    rw [him, abs_mul, abs_of_pos hq0] at h1
    nlinarith [mul_le_mul hu.le hκm hκ.le (abs_nonneg _)]

section Neighbour2

variable (d L : ℕ) [NeZero L]

/-- The neighbour-sum lower bound for every `g > 0` (no small-`g` restriction):
`Σ_{b∼a} K_ab ≥ (κ(1-|m|²))²/(8dg²)` (identity + scalar bound + Cauchy-Schwarz over the `2d` neighbours). -/
theorem BAK_adj_sum_ge (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (a : Zd d L) :
    (κ * (1 - ‖m‖ ^ 2)) ^ 2 / (8 * (d : ℝ) * g ^ 2)
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L a b), BAK d L g E m a b := by
  set N := Finset.univ.filter (fun b : Zd d L => Adj d L a b) with hN
  have hm1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  have hs : 0 ≤ 1 - ‖m‖ ^ 2 := by
    have := pow_le_one₀ (norm_nonneg m) hm1 (n := 2)
    linarith
  have hid := BAMB_adj_sum d L g E m hg hr.1 a
  have hsc := BAone_add_wm_ge κ E m hκ hr.2 hm1
  set T := ∑ b ∈ N, ‖BAMB d L g (E : ℂ) m a b‖ with hT
  have hX : κ / 2 * (1 - ‖m‖ ^ 2) / g ≤ T := by
    have h1 : ‖∑ b ∈ N, BAMB d L g (E : ℂ) m a b‖ ≤ T := norm_sum_le _ _
    rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg] at h1
    exact le_trans (div_le_div_of_nonneg_right hsc hg.le) h1
  have hX0 : 0 ≤ κ / 2 * (1 - ‖m‖ ^ 2) / g := by positivity
  have hcs : T ^ 2 ≤ (N.card : ℝ) * ∑ b ∈ N, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : (N.card : ℝ) = 2 * (d : ℝ) := by
    rw [hN, card_adj d L hL a]; push_cast; ring
  rw [hcard] at hcs
  have hK : ∑ b ∈ N, BAK d L g E m a b = ∑ b ∈ N, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 := rfl
  rw [hK]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h2 : (κ / 2 * (1 - ‖m‖ ^ 2) / g) ^ 2 ≤ 2 * (d : ℝ) * ∑ b ∈ N, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 :=
    le_trans (pow_le_pow_left₀ hX0 hX 2) hcs
  rw [div_le_iff₀ (by positivity)]
  have h3 : (κ / 2 * (1 - ‖m‖ ^ 2) / g) ^ 2 = (κ * (1 - ‖m‖ ^ 2)) ^ 2 / (4 * g ^ 2) := by
    field_simp; ring
  rw [h3, div_le_iff₀ (by positivity)] at h2
  nlinarith

end Neighbour2


end RBM.BA
