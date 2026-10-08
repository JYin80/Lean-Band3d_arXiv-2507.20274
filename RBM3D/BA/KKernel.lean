/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Prop5Short

/-!
# The kernel `K = M^{(+,-)}` of the block Anderson model (BA-P2)

Ticket T2317.  `K_ab = |M^{(B)}_{ab}|²` as the real matrix `BAK d L g E m`
(`(eq:Msig)` `1_2:1070-1071`, `A:18-19`, `A:59`).  Proved unconditionally from the merged D3/D4/P1
lemmas (`Ward.lean`, `CombesThomas.lean`, `Prop5Short.lean`): symmetry and translation invariance,
the bridge to `BAMss`/`BATheta`, double stochasticity (`(eq:WardM)`, `7_8:1869`), laziness
`K_aa = |m|²`, the Markov facts for the powers `K^n`, the exponential tails (squares of
`(Mbound_AO)`, `(Mbound_AO2)` and `BAMB_sq_off_le`), the exponential moment `Σ_b K_ab e^{μ|a-b|}`
uniformly in `L`, the neighbour lower bound `(Mbound_AO)` (small `g`) and, for every `g > 0`, the
neighbour-sum identity `Σ_{b∼a} M_ab = (1 + (E+m)m)/g` with the lower bound
`Σ_{b∼a} K_ab ≥ (κ(1-|m|²))²/(8dg²)`.

No law, no flow time except in the bridge `BATheta_pm_eq`; constants `C, c, A, S` are the merged
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
(`M^{(+,-)}_{ab} = M_{ba} conj(M_{ab})`, `(eq:Msig)` `1_2:1070-1071`; `M` symmetric), at the real-axis
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

theorem BAK_offdiag_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) :
    ∑ b ∈ Finset.univ.erase a, BAK d L g E m a b = 1 - ‖m‖ ^ 2 := by
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Zd d L))
    (fun b => BAK d L g E m a b) (Finset.mem_univ a)
  rw [BAK_row_sum d L g E m h a, BAK_diag d L g E m h a] at h2
  linarith

theorem BAK_diag_bounds (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a : Zd d L) :
    κ ^ 2 ≤ BAK d L g E m a a ∧ BAK d L g E m a a ≤ 1 := by
  rw [BAK_diag d L g E m hr.1 a]
  have h1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  have h2 : κ ≤ ‖m‖ := le_trans hr.2 (Complex.im_le_norm m)
  exact ⟨pow_le_pow_left₀ hκ.le h2 2, pow_le_one₀ (norm_nonneg m) h1⟩

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

/-- The square of the upper half of `(Mbound_AO)`, `g < (2C)⁻¹`: `K_ab ≤ (Cg)^{2|a-b|}`. -/
theorem BAK_le_small (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L) :
    BAK d L g E m a b ≤ (BAct_C d κ * g) ^ (2 * zdistD d L (a - b)) := by
  rw [BAK_apply]
  calc ‖BAMB d L g (E : ℂ) m a b‖ ^ 2
      ≤ ((BAct_C d κ * g) ^ zdistD d L (a - b)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (BAMB_upper_small d L hL hd g κ E m hg hκ hr hsm a b) 2
    _ = (BAct_C d κ * g) ^ (2 * zdistD d L (a - b)) := by rw [← pow_mul, Nat.mul_comm]

/-- The square of `(Mbound_AO2)`, every `0 < g ≤ Λ`, all entries: `K_ab ≤ c⁻² e^{-2c|a-b|}`. -/
theorem BAK_le_decay (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a b : Zd d L) :
    BAK d L g E m a b
      ≤ (BAct_rate d Λ κ)⁻¹ ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) := by
  rw [BAK_apply]
  have h := pow_le_pow_left₀ (norm_nonneg _) (BAMB_decay_large d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr a b) 2
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
  congr 2
  ring

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

/-- The neighbour lower bound of `(Mbound_AO)` squared, `g < (2C)⁻¹`: `(C⁻¹g)² ≤ K_ab`, `a ∼ b`. -/
theorem BAK_adj_ge_small (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L) (hab : Adj d L a b) :
    ((BAct_C d κ)⁻¹ * g) ^ 2 ≤ BAK d L g E m a b := by
  rw [BAK_apply]
  have hC := BAct_C_pos d κ hd hκ
  exact pow_le_pow_left₀ (by positivity)
    (BAMB_lower_small d L hL hd g κ E m hg hκ hr hsm a b hab) 2

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

/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`) -/

namespace KKernelInst

open RBM.BA.MFixedPointInst

/-- Ward: `Σ_b K_0b = 1` at the flow point `P`. -/
theorem inst_row_sum : ∑ b, BAK 3 4 P.g0 P.E P.m0 0 b = 1 :=
  BAK_row_sum 3 4 P.g0 P.E P.m0 P.real.1 0

theorem inst_col_sum : ∑ a, BAK 3 4 P.g0 P.E P.m0 a ![1, 0, 0] = 1 :=
  BAK_col_sum 3 4 P.g0 P.E P.m0 P.real.1 ![1, 0, 0]

theorem inst_diag : BAK 3 4 P.g0 P.E P.m0 0 0 = ‖P.m0‖ ^ 2 :=
  BAK_diag 3 4 P.g0 P.E P.m0 P.real.1 0

theorem inst_offdiag_sum :
    ∑ b ∈ Finset.univ.erase (0 : Zd 3 4), BAK 3 4 P.g0 P.E P.m0 0 b = 1 - ‖P.m0‖ ^ 2 :=
  BAK_offdiag_sum 3 4 P.g0 P.E P.m0 P.real.1 0

theorem inst_diag_bounds :
    P.m0.im ^ 2 ≤ BAK 3 4 P.g0 P.E P.m0 0 0 ∧ BAK 3 4 P.g0 P.E P.m0 0 0 ≤ 1 :=
  BAK_diag_bounds 3 4 P.g0 P.m0.im P.E P.m0 P.real.1.1 P.real 0

theorem inst_symm :
    BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] = BAK 3 4 P.g0 P.E P.m0 ![1, 0, 0] 0 :=
  BAK_symm 3 4 P.g0 P.E P.m0 0 ![1, 0, 0]

theorem inst_shift :
    BAK 3 4 P.g0 P.E P.m0 (0 + ![1, 1, 0]) (![1, 0, 0] + ![1, 1, 0])
      = BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] :=
  BAK_shift 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] ![1, 1, 0]

theorem inst_zero_neg :
    BAK 3 4 P.g0 P.E P.m0 0 (-![1, 0, 0]) = BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] :=
  BAK_zero_neg 3 4 P.g0 P.E P.m0 ![1, 0, 0]

theorem inst_Mss_pm :
    BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true false
      = Matrix.map (BAK 3 4 P.g0 P.E P.m0) Complex.ofReal :=
  BAMss_pm_eq 3 4 P.g0 P.E P.m0

theorem inst_Mss_mp :
    BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) false true
      = Matrix.map (BAK 3 4 P.g0 P.E P.m0) Complex.ofReal :=
  BAMss_mp_eq 3 4 P.g0 P.E P.m0

theorem inst_Mss_norm (σ₁ σ₂ : Bool) :
    ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ₁ σ₂ 0 ![1, 0, 0]‖
      = BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] :=
  BAMss_norm_eq_BAK 3 4 P.g0 P.E P.m0 σ₁ σ₂ 0 ![1, 0, 0]

/-- The bridge to the merged propagator `Θ_{1/2}^{(+,-)}` at `P`. -/
theorem inst_Theta_pm :
    BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false
      = PropThetaQ (Matrix.map (BAK 3 4 P.g0 P.E P.m0) Complex.ofReal) (1 / 2) :=
  BATheta_pm_eq 3 4 P.g0 P.E P.m0 (1 / 2)

/-- The three-step kernel at `P` is stochastic. -/
theorem inst_pow_row_sum : ∑ b, (BAK 3 4 P.g0 P.E P.m0 ^ 3) 0 b = 1 :=
  BAK_pow_row_sum 3 4 P.g0 P.E P.m0 P.real.1 3 0

theorem inst_pow_nonneg : 0 ≤ (BAK 3 4 P.g0 P.E P.m0 ^ 2) 0 ![1, 0, 0] :=
  BAK_pow_nonneg 3 4 P.g0 P.E P.m0 2 0 ![1, 0, 0]

theorem inst_pow_transpose :
    Matrix.transpose (BAK 3 4 P.g0 P.E P.m0 ^ 2) = BAK 3 4 P.g0 P.E P.m0 ^ 2 :=
  BAK_pow_transpose 3 4 P.g0 P.E P.m0 2

theorem inst_pow_shift :
    (BAK 3 4 P.g0 P.E P.m0 ^ 2) (0 + ![0, 1, 0]) (![1, 0, 0] + ![0, 1, 0])
      = (BAK 3 4 P.g0 P.E P.m0 ^ 2) 0 ![1, 0, 0] :=
  BAK_pow_shift 3 4 P.g0 P.E P.m0 2 0 ![1, 0, 0] ![0, 1, 0]

/-- The tail at `P`, entry `(0, (1,0,0))`, `Λ = 10`. -/
theorem inst_off_le :
    BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0]
      ≤ BAp5s_A 3 10 P.m0.im * P.g0 ^ 2
        * Real.exp (-(2 * BAct_rate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) :=
  BAK_off_le 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real 0 ![1, 0, 0] (by decide)

theorem inst_le_decay :
    BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0]
      ≤ (BAct_rate 3 10 P.m0.im)⁻¹ ^ 2
        * Real.exp (-(2 * BAct_rate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) :=
  BAK_le_decay 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real 0 ![1, 0, 0]

/-- The exponential moment at `P`, `μ = c`, row `0`. -/
theorem inst_exp_moment :
    ∑ b, BAK 3 4 P.g0 P.E P.m0 0 b * Real.exp (BAct_rate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - b) : ℝ))
      ≤ ‖P.m0‖ ^ 2 + BAp5s_A 3 10 P.m0.im * P.g0 ^ 2 * BAp5s_S 3 10 P.m0.im :=
  BAK_exp_moment_le 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num)
    P.g0_pos P.g0_le P.real.1.1 P.real (BAct_rate 3 10 P.m0.im)
    (BAct_rate_pos 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1).le le_rfl 0

/-- The exponential moment at `P`, `μ = 0` (total mass). -/
theorem inst_exp_moment_zero :
    ∑ b, BAK 3 4 P.g0 P.E P.m0 0 b * Real.exp (0 * (zdistD 3 4 ((0 : Zd 3 4) - b) : ℝ))
      ≤ ‖P.m0‖ ^ 2 + BAp5s_A 3 10 P.m0.im * P.g0 ^ 2 * BAp5s_S 3 10 P.m0.im :=
  BAK_exp_moment_le 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num)
    P.g0_pos P.g0_le P.real.1.1 P.real 0 le_rfl
    (BAct_rate_pos 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1).le 0

/-- The small-`g` neighbour lower bound at `P` (an implication: no datum has a provable `g₀ < (2C)⁻¹`). -/
theorem inst_adj_ge_small (h : P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹) :
    ((BAct_C 3 P.m0.im)⁻¹ * P.g0) ^ 2 ≤ BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] :=
  BAK_adj_ge_small 3 4 (by norm_num) (by norm_num) P.g0 P.m0.im P.E P.m0 P.g0_pos P.real.1.1
    P.real h 0 ![1, 0, 0] (by unfold Adj; decide)

/-- The small-`g` upper bound at `P` (an implication). -/
theorem inst_le_small (h : P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹) :
    BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0]
      ≤ (BAct_C 3 P.m0.im * P.g0) ^ (2 * zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0])) :=
  BAK_le_small 3 4 (by norm_num) (by norm_num) P.g0 P.m0.im P.E P.m0 P.g0_pos P.real.1.1
    P.real h 0 ![1, 0, 0]

/-- The neighbour-sum identity at `P`, row `0`. -/
theorem inst_adj_sum :
    ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => Adj 3 4 0 b), BAMB 3 4 P.g0 (P.E : ℂ) P.m0 0 b
      = (1 + ((P.E : ℂ) + P.m0) * P.m0) / (P.g0 : ℂ) :=
  BAMB_adj_sum 3 4 P.g0 P.E P.m0 P.g0_pos P.real.1 0

/-- The all-`g` neighbour-sum lower bound at `P`, row `0`. -/
theorem inst_adj_sum_ge :
    (P.m0.im * (1 - ‖P.m0‖ ^ 2)) ^ 2 / (8 * (3 : ℝ) * P.g0 ^ 2)
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => Adj 3 4 0 b), BAK 3 4 P.g0 P.E P.m0 0 b := by
  have h := BAK_adj_sum_ge 3 4 (by norm_num) (by norm_num) P.g0 P.m0.im P.E P.m0 P.g0_pos
    P.real.1.1 P.real 0
  simpa using h

/-- The scalar bound at the merged Ward scalar instance `κ = 1/2`, `m = (3/5) i`, `E = 0`. -/
theorem inst_scalar :
    (1 / 2 : ℝ) / 2 * (1 - ‖(3 / 5 : ℂ) * Complex.I‖ ^ 2)
      ≤ ‖1 + (((0 : ℝ) : ℂ) + (3 / 5 : ℂ) * Complex.I) * ((3 / 5 : ℂ) * Complex.I)‖ :=
  BAone_add_wm_ge (1 / 2) 0 ((3 / 5 : ℂ) * Complex.I) (by norm_num)
    RBM.BA.WardInst.ward_scalar_inst_im RBM.BA.WardInst.ward_scalar_inst_norm

end KKernelInst

end RBM.BA
