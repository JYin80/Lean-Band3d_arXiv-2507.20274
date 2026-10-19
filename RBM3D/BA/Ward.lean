/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MFixedPoint

/-!
# Ward's identity and the off-diagonal bound of the block Anderson model

The row-wise Ward identity, translation invariance and symmetry of
`M^{(B)} = (gΨ^{(B)} - z - m)⁻¹`, `M_aa = m`, `|m| ≤ 1` (Lemma 8.3 `lem:propM` (1)(2)), and
`(eq:off_diagM)` (A.4); items (1)(2) of `BAPropM` are stated as `BAPropM12`.
No statement mentions a law; the hypotheses `3 ≤ L`, `0 < g`, `3 ≤ d`, `0 < Λ`, `g ≤ Λ` are
not used by the proofs (`L ≥ 1` only through `NeZero L`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open Matrix

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The Ward half -/

section Ward

variable (d L : ℕ) [NeZero L]

private theorem Ward_BAMB_eq (g : ℝ) (z m : ℂ) :
    BAMB d L g z m = ((g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ))⁻¹ := by
  unfold BAMB Mres
  rw [Matrix.nonsing_inv_eq_ringInverse]

private theorem Ward_adj_symm (x y : Zd d L) : Adj d L x y ↔ Adj d L y x := by
  simp only [Adj]
  rw [show y - x = -(x - y) by ring, zdistD_neg]

omit [NeZero L] in
private theorem Ward_adj_shift (x y r : Zd d L) : Adj d L (x + r) (y + r) ↔ Adj d L x y := by
  simp only [Adj, add_sub_add_right_eq_sub]

/-- Translation invariance of `M^{(B)}`, unconditional. -/
theorem BAMB_shift (g : ℝ) (z m : ℂ) (a b r : Zd d L) :
    BAMB d L g z m (a + r) (b + r) = BAMB d L g z m a b := by
  have hA : ((g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ)).submatrix
      (Equiv.addRight r) (Equiv.addRight r)
      = (g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    ext x y
    have h1 : (x + r = y + r) ↔ (x = y) := add_left_inj r
    have h2 := Ward_adj_shift d L x y r
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, PsiB,
      Matrix.of_apply, Matrix.one_apply, Equiv.coe_addRight, h1]
    simp only [h2]
  have h2 := Matrix.inv_submatrix_equiv
    ((g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ)) (Equiv.addRight r)
    (Equiv.addRight r)
  rw [hA] at h2
  rw [Ward_BAMB_eq]
  have h3 := congrFun (congrFun h2 a) b
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- `M^{(B)}` is complex symmetric (`Ψ^{(B)}` is real symmetric), unconditional. -/
theorem BAMB_transpose (g : ℝ) (z m : ℂ) :
    Matrix.transpose (BAMB d L g z m) = BAMB d L g z m := by
  rw [Ward_BAMB_eq, Matrix.transpose_nonsing_inv]
  congr 1
  have hT : (PsiB d L)ᵀ = PsiB d L := by
    ext a b
    simp only [Matrix.transpose_apply, PsiB, Matrix.of_apply, Ward_adj_symm d L b a]
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, hT, Matrix.transpose_one]

theorem BAMB_symm (g : ℝ) (z m : ℂ) (a b : Zd d L) :
    BAMB d L g z m a b = BAMB d L g z m b a := by
  have := congrFun (congrFun (BAMB_transpose d L g z m) a) b
  simpa [Matrix.transpose_apply] using this.symm

/-- `M_aa = m` for a solution of `(self_m)` (any `z`). -/
theorem BAMB_diag_eq (g : ℝ) (z m : ℂ) (h : BASelf d L g z m) (a : Zd d L) :
    BAMB d L g z m a a = m := by
  have h0 : ∀ a : Zd d L, BAMB d L g z m a a = BAMB d L g z m 0 0 := by
    intro a
    have := BAMB_shift d L g z m 0 0 a
    simpa using this
  have hmeq := h.2
  have htr : (BAMB d L g z m).trace = ((L ^ d : ℕ) : ℂ) * BAMB d L g z m 0 0 := by
    rw [Matrix.trace]
    simp only [Matrix.diag, h0]
    rw [Finset.sum_const, Finset.card_univ, BAcard_Zd, nsmul_eq_mul]
  have hne : (((L ^ d : ℕ) : ℂ)) ≠ 0 := by
    have : 0 < L ^ d := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) d
    exact_mod_cast this.ne'
  rw [h0 a]
  rw [htr, ← mul_assoc, inv_mul_cancel₀ hne, one_mul] at hmeq
  exact hmeq.symm

/-- Ward's identity for each row, `0 ≤ Im z`. -/
theorem BAMB_ward_row (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) (h : BASelf d L g z m) (a : Zd d L) :
    (m.im + z.im) * ∑ b, ‖BAMB d L g z m a b‖ ^ 2 = m.im := by
  have hw : 0 < (z + m).im := by
    have := h.1
    simp only [Complex.add_im]; linarith
  have h1 := BAimInv_diag (BAPsi_isHermitian d L g) hw a
  have h2 : (BAMB d L g z m a a).im = (z + m).im * ∑ k, ‖BAMB d L g z m k a‖ ^ 2 := by
    simpa [BAMB, Mres] using h1
  rw [BAMB_diag_eq d L g z m h a] at h2
  have hsum : ∑ k, ‖BAMB d L g z m k a‖ ^ 2 = ∑ b, ‖BAMB d L g z m a b‖ ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [BAMB_symm d L g z m k a]
  rw [hsum] at h2
  have hzm : (z + m).im = m.im + z.im := by simp [add_comm]
  rw [hzm] at h2
  exact h2.symm

/-- `(eq:WardM)` at a real energy: `Σ_b |M_ab|² = 1`. -/
theorem BAMB_row_sq_real (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) :
    ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1 := by
  have h1 := BAMB_ward_row d L g (E : ℂ) m (by simp) h a
  have hm := h.1
  simp only [Complex.ofReal_im, add_zero] at h1
  have : m.im * (∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hm.ne'
  · linarith

/-- `|m| ≤ 1` for every `0 ≤ Im z`. -/
theorem BAm_norm_le_one (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) (h : BASelf d L g z m) : ‖m‖ ≤ 1 := by
  have h1 := BAMB_ward_row d L g z m hz h 0
  have hm := h.1
  set S := ∑ b, ‖BAMB d L g z m 0 b‖ ^ 2 with hS
  have hle : ‖BAMB d L g z m 0 0‖ ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun b => ‖BAMB d L g z m 0 b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ 0)
  rw [BAMB_diag_eq d L g z m h 0] at hle
  have hS1 : S ≤ 1 := by
    by_contra hc
    have hc := not_le.mp hc
    nlinarith
  have : ‖m‖ ^ 2 ≤ 1 := hle.trans hS1
  by_contra hc
  have hc := not_le.mp hc
  nlinarith [norm_nonneg m]

end Ward

/-! ## 2. The statement `BAPropM12` -/

section PropM12

variable (d : ℕ)

/-- Items (1)(2) of Lemma 8.3 (`lem:propM`) on the real axis: translation invariance, `M_aa = m`,
Ward's identity `Σ_b |M_ab|² = 1` (`(eq:WardM)`), `|m| ≤ 1` — the first four conjuncts of `BAPropM`
(`BA/MFixedPoint`) verbatim, under `BASelf` at a real energy instead of `BAReal` (no `κ`, no `C, c`).
The paper's `Im m ≳ 1` is the bulk premise `κ ≤ Im m` of `BAReal` (see `BAm_im_lower_of_bulk`), not a conjunct. -/
def BAPropM12 : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    BASelf d L g (E : ℂ) m →
      (∀ a b r : Zd d L, BAMB d L g (E : ℂ) m (a + r) (b + r) = BAMB d L g (E : ℂ) m a b) ∧
      (∀ a : Zd d L, BAMB d L g (E : ℂ) m a a = m) ∧
      (∀ a : Zd d L, ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1) ∧ ‖m‖ ≤ 1

end PropM12

/-- `BAPropM12` is proved. -/
theorem baPropM12_holds (d : ℕ) : BAPropM12 d := by
  intro L hL g hg E m
  have : NeZero L := ⟨by omega⟩
  intro hs
  exact ⟨BAMB_shift d L g (E : ℂ) m, BAMB_diag_eq d L g (E : ℂ) m hs,
    BAMB_row_sq_real d L g E m hs, BAm_norm_le_one d L g (E : ℂ) m (by simp) hs⟩

/-! ## 3. The off-diagonal half (`(eq:off_diagM)` (A.4)) -/

/-- `|1 - t m²|² = (1 - t|m|²)² + 4t (Im m)²` (every real `t`). -/
theorem BAnorm_one_sub_tm2_sq (t : ℝ) (m : ℂ) :
    ‖1 - (t : ℂ) * m ^ 2‖ ^ 2 = (1 - t * ‖m‖ ^ 2) ^ 2 + 4 * t * m.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two, zero_mul, mul_zero, sub_zero,
    zero_add, add_zero]
  ring

/-- The scalar inequalities of `(eq:off_diagM)` with `ε = κ²/4`. -/
theorem BAoffDiag_scalar (κ t : ℝ) (m : ℂ) (hκ : 0 < κ) (hκm : κ ≤ m.im) (hm : ‖m‖ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    κ ^ 2 / 4 ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧
      1 - ‖m‖ ^ 2 ≤ (1 - κ ^ 2 / 4) * ‖1 - (t : ℂ) * m ^ 2‖ := by
  have hq := BAnorm_one_sub_tm2_sq t m
  set q := ‖1 - (t : ℂ) * m ^ 2‖ with hqdef
  have hq0 : 0 ≤ q := norm_nonneg _
  set s := ‖m‖ ^ 2 with hsdef
  set y := m.im with hydef
  have hs1 : s ≤ 1 := by
    have := norm_nonneg m
    nlinarith
  have hys : y ^ 2 ≤ s := by
    rw [hsdef, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg m.re]
  have hky : κ ^ 2 ≤ y ^ 2 := by nlinarith
  have hks : κ ^ 2 ≤ s := hky.trans hys
  have hκ1 : κ ^ 2 ≤ 1 := hks.trans hs1
  have hκ1' : κ ≤ 1 := by nlinarith
  have hs0 : 0 ≤ s := by positivity
  set x := κ ^ 2 with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := hκ1
  constructor
  · -- the first conjunct
    have h1 : (1 - t) ^ 2 + 4 * t * x ≤ q ^ 2 := by
      have : (1 - t) ≤ 1 - t * s := by nlinarith
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hky)]
    have h2 : (x / 4) ^ 2 ≤ (1 - t) ^ 2 + 4 * t * x := by
      rcases le_total t (1 / 2) with h | h
      · nlinarith
      · nlinarith
    by_contra hc
    have hc := not_le.mp hc
    nlinarith [sq_nonneg (x / 4 - q), hx0]
  · -- the second conjunct
    have hs1' : 0 ≤ 1 - s := by linarith
    have e1 : q ^ 2 - (1 - s) ^ 2 = s * (1 - t) * (2 - s - t * s) + 4 * t * y ^ 2 := by
      rw [hq]; ring
    have h1 : x * (1 - s) ≤ s * (1 - t) * (2 - s - t * s) + 4 * t * y ^ 2 := by
      have a1 : 1 - s ≤ 2 - s - t * s := by nlinarith
      have a2 : x * ((1 - t) * (1 - s)) ≤ s * ((1 - t) * (2 - s - t * s)) := by
        apply mul_le_mul hks _ (by positivity) hs0
        have : 0 ≤ 1 - t := by linarith
        nlinarith
      have a3 : t * x * (1 - s) ≤ t * y ^ 2 := by
        have : x * (1 - s) ≤ y ^ 2 := by nlinarith
        nlinarith
      nlinarith [mul_nonneg ht0 hs1']
    have h2 : (1 + x) * (1 - s) ^ 2 ≤ q ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hx0.le hs1') hs0]
    have hpoly : 1 ≤ (1 - x / 4) ^ 2 * (1 + x) := by
      nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1), mul_nonneg hx0.le (mul_nonneg hx0.le (sub_nonneg.mpr hx1))]
    have h3 : (1 - s) ^ 2 ≤ ((1 - x / 4) * q) ^ 2 := by
      have : (1 - x / 4) ^ 2 * ((1 + x) * (1 - s) ^ 2) ≤ (1 - x / 4) ^ 2 * q ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      nlinarith [sq_nonneg (1 - s)]
    have hxq : 0 ≤ (1 - x / 4) * q := by
      have : 0 ≤ 1 - x / 4 := by linarith
      positivity
    by_contra hc
    have hc := not_le.mp hc
    nlinarith

/-- `M^{(+,+)}_{ab} = M_{ba} M_{ab}` (definitional). -/
theorem BAMss_pp_apply (d L : ℕ) [NeZero L] (M : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) :
    BAMss d L M true true a b = M b a * M a b := rfl

end RBM.BA

end
