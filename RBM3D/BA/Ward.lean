/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MFixedPoint

/-!
# Ward's identity and the off-diagonal bound of the block Anderson model (BA-D3)

Ticket T2283.  The row-wise Ward identity, translation invariance and symmetry of
`M^{(B)} = (gΨ^{(B)} - z - m)⁻¹`, `M_aa = m`, `|m| ≤ 1` (`lem:propM` (1)(2), `7_8:1853-1869`), and
`(eq:off_diagM)` (`A:32-34`): proofs of the merged pins `BAWard` and `BAoffDiag`
(`RBM3D/BA/MFixedPoint.lean`) and of items (1)(2) of `BAPropM`,
stated as the new pin `BAPropM12`.
No statement mentions a law; the hypotheses `3 ≤ L`, `0 < g`, `3 ≤ d`, `0 < Λ`, `g ≤ Λ` of the pins are
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

/-! ## 2. The pins `BAWard`, `BAPropM12` -/

/-- **`BAWard`** is proved: the merged pin (`MFixedPoint.lean`, `(eq:WardM)`, `7_8:1864-1869`). -/
theorem baWard_holds (d : ℕ) : BAWard d := by
  intro L hL g hg z m
  have : NeZero L := ⟨by omega⟩
  intro hz hs
  exact ⟨BAMB_shift d L g z m, BAMB_diag_eq d L g z m hs, BAMB_ward_row d L g z m hz hs⟩

section PropM12

variable (d : ℕ)

/-- **Items (1)(2) of `lem:propM`** (`7_8:1853-1869`) on the real axis: translation invariance, `M_aa = m`,
Ward's identity `Σ_b |M_ab|² = 1` (`(eq:WardM)`), `|m| ≤ 1` — the first four conjuncts of the merged `BAPropM`
(`MFixedPoint.lean:573-575`) verbatim, under `BASelf` at a real energy instead of `BAReal` (no `κ`, no `C, c`).
The paper's `Im m ≳ 1` is the bulk premise `κ ≤ Im m` of `BAReal` (and `BAImmLower`, BA-D7), not a conjunct. -/
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

/-! ## 3. The off-diagonal half (`(eq:off_diagM)`, `A:32-34`) -/

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
  · -- (A)
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
  · -- (B)
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

section OffDiag

variable (d L : ℕ) [NeZero L]

/-- The left side of `(eq:off_diagM)` is exactly `1 - |m|²` at a real energy. -/
theorem BAoffDiag_row_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) :
    ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
      = 1 - ‖m‖ ^ 2 := by
  have h1 : ∀ a : Zd d L, ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
      = ‖BAMB d L g (E : ℂ) m 0 a‖ ^ 2 := by
    intro a
    rw [BAMss_pp_apply, BAMB_symm d L g (E : ℂ) m a 0, norm_mul, sq]
  simp only [h1]
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Zd d L))
    (fun a => ‖BAMB d L g (E : ℂ) m 0 a‖ ^ 2) (Finset.mem_univ 0)
  rw [BAMB_row_sq_real d L g E m h 0, BAMB_diag_eq d L g (E : ℂ) m h 0] at h2
  linarith

/-- `(eq:off_diagM)` with the explicit `ε = κ²/4` at one datum. -/
theorem BAoffDiag_of_real (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    κ ^ 2 / 4 ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧
      ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
        ≤ (1 - κ ^ 2 / 4) * ‖1 - (t : ℂ) * m ^ 2‖ := by
  have hn := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  obtain ⟨h1, h2⟩ := BAoffDiag_scalar κ t m hκ hr.2 hn ht0 ht1
  refine ⟨h1, ?_⟩
  rw [BAoffDiag_row_sum d L g E m hr.1]
  exact h2

end OffDiag

/-- **`BAoffDiag`** is proved with `ε = κ²/4` (the premises `3 ≤ d`, `0 < Λ`, `g ≤ Λ` are unused). -/
theorem baOffDiag_holds (d : ℕ) (Λ κ : ℝ) : BAoffDiag d Λ κ := by
  intro _ _ hκ
  refine ⟨κ ^ 2 / 4, by positivity, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1
  have : NeZero L := ⟨by omega⟩
  exact BAoffDiag_of_real d L g κ E m hκ hr t ht0 ht1

/-! ## 4. Compiled nonempty instances (`d = 3`, `L = 4`, `card (Zd 3 4) = 64`)

The merged data of T2189: the complex point `(z_S, m_S)` of `(L, g) = (4, 10)` (`Im z_S > 0`) and the
flow point `P` (`g = P.g0`, a real energy `P.E`, `m = P.m0`, `BAReal 3 4 P.g0 (Im P.m0) P.E P.m0`). -/
namespace WardInst

open RBM.BA.MFixedPointInst

/-- `baWard_holds` at the complex point `(z_S, m_S)`, `g = 10`, `Im z_S > 0`. -/
example :
    (∀ a b r : Zd 3 4, BAMB 3 4 10 (zS 4 10) (mS 4 10) (a + r) (b + r) = BAMB 3 4 10 (zS 4 10) (mS 4 10) a b) ∧
    (∀ a : Zd 3 4, BAMB 3 4 10 (zS 4 10) (mS 4 10) a a = mS 4 10) ∧
    ∀ a : Zd 3 4, ((mS 4 10).im + (zS 4 10).im) * ∑ b, ‖BAMB 3 4 10 (zS 4 10) (mS 4 10) a b‖ ^ 2
      = (mS 4 10).im :=
  baWard_holds 3 4 (by norm_num) 10 (by norm_num) (zS 4 10) (mS 4 10) (zS_im_pos 4 10).le (selfS 4 10)

/-- `baWard_holds` at the real-axis flow point `P`. -/
example :
    (∀ a b r : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (a + r) (b + r) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b) ∧
    (∀ a : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a a = P.m0) ∧
    ∀ a : Zd 3 4, (P.m0.im + ((P.E : ℂ)).im) * ∑ b, ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ^ 2 = P.m0.im :=
  baWard_holds 3 4 (by norm_num) P.g0 P.g0_pos (P.E : ℂ) P.m0 (by simp) P.real.1

/-- `baPropM12_holds` at the flow point `P`. -/
example :
    (∀ a b r : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (a + r) (b + r) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b) ∧
    (∀ a : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a a = P.m0) ∧
    (∀ a : Zd 3 4, ∑ b, ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ^ 2 = 1) ∧ ‖P.m0‖ ≤ 1 :=
  baPropM12_holds 3 4 (by norm_num) P.g0 P.g0_pos P.E P.m0 P.real.1

/-- The row-wise pieces at `P`: symmetry, transpose, `M_aa = m`, Ward row, `|m| ≤ 1`. -/
example (a b : Zd 3 4) : BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 b a :=
  BAMB_symm 3 4 P.g0 (P.E : ℂ) P.m0 a b

example : Matrix.transpose (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 :=
  BAMB_transpose 3 4 P.g0 (P.E : ℂ) P.m0

example (a b r : Zd 3 4) :
    BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (a + r) (b + r) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b :=
  BAMB_shift 3 4 P.g0 (P.E : ℂ) P.m0 a b r

example (a : Zd 3 4) : BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a a = P.m0 :=
  BAMB_diag_eq 3 4 P.g0 (P.E : ℂ) P.m0 P.real.1 a

example (a : Zd 3 4) :
    ∑ b, ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ^ 2 = 1 :=
  BAMB_row_sq_real 3 4 P.g0 P.E P.m0 P.real.1 a

example : ‖P.m0‖ ≤ 1 := BAm_norm_le_one 3 4 P.g0 (P.E : ℂ) P.m0 (by simp) P.real.1

/-- `BAMB_ward_row` at the complex point `(z_S, m_S)`: factor `Im m + Im z > 0`. -/
example (a : Zd 3 4) :
    ((mS 4 10).im + (zS 4 10).im) * ∑ b, ‖BAMB 3 4 10 (zS 4 10) (mS 4 10) a b‖ ^ 2 = (mS 4 10).im :=
  BAMB_ward_row 3 4 10 (zS 4 10) (mS 4 10) (zS_im_pos 4 10).le (selfS 4 10) a

/-- `BAoffDiag_row_sum` at `P`. -/
example : ∑ a ∈ Finset.univ.erase (0 : Zd 3 4),
      ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true 0 a‖ = 1 - ‖P.m0‖ ^ 2 :=
  BAoffDiag_row_sum 3 4 P.g0 P.E P.m0 P.real.1

/-- `BAoffDiag_of_real` at `P`, `κ = Im m₀`, `t = 1/2`. -/
example :
    P.m0.im ^ 2 / 4 ≤ ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖ ∧
      ∑ a ∈ Finset.univ.erase (0 : Zd 3 4), ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true 0 a‖
        ≤ (1 - P.m0.im ^ 2 / 4) * ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖ :=
  BAoffDiag_of_real 3 4 P.g0 P.m0.im P.E P.m0 P.real.1.1 P.real (1 / 2) (by norm_num) (by norm_num)

/-- `baOffDiag_holds` at `d = 3`, `Λ = 10`, `κ = Im m₀`, applied at `L = 4`, `g = P.g0 ≤ 10`, `P.E`, `P.m0`,
`t = 1/2`: the `ε` is explicit, quantified before the data. -/
example : ∃ ε : ℝ, 0 < ε ∧
    (ε ≤ ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖ ∧
      ∑ a ∈ Finset.univ.erase (0 : Zd 3 4), ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true 0 a‖
        ≤ (1 - ε) * ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖) := by
  obtain ⟨ε, hε, h⟩ := baOffDiag_holds 3 10 P.m0.im (le_refl 3) (by norm_num) P.real.1.1
  exact ⟨ε, hε, h 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num)⟩

/-- `BAnorm_one_sub_tm2_sq` at `m = (3/5) i`, `t = 1/2`. -/
example : ‖1 - (((1 / 2 : ℝ)) : ℂ) * ((3 / 5 : ℂ) * Complex.I) ^ 2‖ ^ 2
    = (1 - (1 / 2 : ℝ) * ‖(3 / 5 : ℂ) * Complex.I‖ ^ 2) ^ 2
      + 4 * (1 / 2 : ℝ) * ((3 / 5 : ℂ) * Complex.I).im ^ 2 :=
  BAnorm_one_sub_tm2_sq (1 / 2) _

/-- `BAoffDiag_scalar` at `κ = 1/2`, `m = (3/5) i` (`Im m = 3/5`, `|m| = 3/5`), `t = 0` and `t = 1`. -/
theorem ward_scalar_inst_norm : ‖(3 / 5 : ℂ) * Complex.I‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_I, mul_one]
  have : ‖(3 / 5 : ℂ)‖ = 3 / 5 := by
    have h : (3 / 5 : ℂ) = ((3 / 5 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs]; norm_num
  rw [this]; norm_num

theorem ward_scalar_inst_im : (1 / 2 : ℝ) ≤ ((3 / 5 : ℂ) * Complex.I).im := by
  have : ((3 / 5 : ℂ) * Complex.I).im = 3 / 5 := by simp [Complex.mul_im]
  rw [this]; norm_num

example : (1 / 2 : ℝ) ^ 2 / 4 ≤ ‖1 - ((0 : ℝ) : ℂ) * ((3 / 5 : ℂ) * Complex.I) ^ 2‖ ∧
    1 - ‖(3 / 5 : ℂ) * Complex.I‖ ^ 2
      ≤ (1 - (1 / 2 : ℝ) ^ 2 / 4) * ‖1 - ((0 : ℝ) : ℂ) * ((3 / 5 : ℂ) * Complex.I) ^ 2‖ :=
  BAoffDiag_scalar (1 / 2) 0 _ (by norm_num) ward_scalar_inst_im ward_scalar_inst_norm le_rfl
    (by norm_num)

example : (1 / 2 : ℝ) ^ 2 / 4 ≤ ‖1 - ((1 : ℝ) : ℂ) * ((3 / 5 : ℂ) * Complex.I) ^ 2‖ ∧
    1 - ‖(3 / 5 : ℂ) * Complex.I‖ ^ 2
      ≤ (1 - (1 / 2 : ℝ) ^ 2 / 4) * ‖1 - ((1 : ℝ) : ℂ) * ((3 / 5 : ℂ) * Complex.I) ^ 2‖ :=
  BAoffDiag_scalar (1 / 2) 1 _ (by norm_num) ward_scalar_inst_im ward_scalar_inst_norm
    (by norm_num) le_rfl

/-- `BAMss_pp_apply` at `P`. -/
example (a b : Zd 3 4) :
    BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true a b
      = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 b a * BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b :=
  BAMss_pp_apply 3 4 _ a b

end WardInst

end RBM.BA

end
