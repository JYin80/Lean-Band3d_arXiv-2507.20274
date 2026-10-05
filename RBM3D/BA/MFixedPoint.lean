/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.BlockAnderson
import RBM3D.Propagator.Pins
import RBM3D.Analysis.Resolvent
import RBM3D.Universality.FreeConv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The deterministic layer of the block Anderson model: `(self_m)` (BA-D1a, BA-D2)

Ticket T2189.  The vocabulary of the block Anderson model (`m(z, g)`, `M^{(B)}`, `ρ_N`, the bulk
set `B_κ = {E : ρ_N(E) ≥ κ}`, `M^{(σ₁,σ₂)}`, `Θ^{(σ₁,σ₂)}`), the proved base copied from the T2161
probe (`RBM3D/Probe/T2161Pins.lean` on `t/T2161` at 82e72b3, sections 0-3, `:45-655`), the seven
deterministic pins of gate BA as `def … : Prop`, and the proofs of `BAmExists` and `BAmUniqReal`:

* `BAMB_trace_eq_sum`: the spectral bridge `tr M^{(B)} = Σ_i (v_i - z - m)⁻¹`, `v = BAspec d L g`;
* `BASelf_iff_freeConv`: `(self_m)` is `[32] (2.5)` at `t = 1` (paper `1_2:626-629`);
* `BASelf_exists`, `BASelf_unique`: existence (`Im z > 0`) and uniqueness (every `Im z ≥ 0`, the
  real axis included) of `m(z, g)`;
* `baMExists_holds`, `baMUniqReal_holds`, `BAm_self`, `BAm_eq_freeConvST`, `BAm_real_eq_of_self`,
  `BAbulk_iff_exists`.

Paper: `paper/tex/1_2_Intro_model_result.tex` (`1_2:line`), `paper/tex/7_8_light_weight.tex`
(`7_8:line`), `paper/tex/A_deterministic_estimates.tex` (`A:line`).  The bulk set is `BAbulk`
(`κ ≤ BArho`, DECISIONS §51); the bulk forms 0 and 1 of the probe are not ported.  No statement
of this file mentions a law.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open Filter Matrix
open scoped ComplexInnerProductSpace Topology

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 0. Resolvent identities (proved here; they are the whole of `Ward` at the averaged level) -/

/-- `Im ((H - w)⁻¹)_{ii} = Im w · Σ_k |((H - w)⁻¹)_{ki}|²` for Hermitian `H`, `Im w > 0` (Ward at the
level of a resolvent). -/
theorem BAimInv_diag {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {w : ℂ} (hw : 0 < w.im) (i : n) :
    (Ring.inverse (H - w • (1 : Matrix n n ℂ)) i i).im
      = w.im * ∑ k, ‖Ring.inverse (H - w • (1 : Matrix n n ℂ)) k i‖ ^ 2 := by
  set G := Ring.inverse (H - w • (1 : Matrix n n ℂ)) with hG
  set e : n → ℂ := Pi.single i 1 with he
  have hunit := RBM.isUnit_sub_smul_of_isHermitian hH hw.ne'
  have hsol : (H - w • (1 : Matrix n n ℂ)) *ᵥ (G *ᵥ e) = e := by
    rw [Matrix.mulVec_mulVec, hG, Ring.mul_inverse_cancel _ hunit, Matrix.one_mulVec]
  have hEuclid : Matrix.toEuclideanLin H (WithLp.toLp 2 (G *ᵥ e)) - w • WithLp.toLp 2 (G *ᵥ e)
      = WithLp.toLp 2 e := by
    have hrw : (H - w • (1 : Matrix n n ℂ)) *ᵥ (G *ᵥ e) = H *ᵥ (G *ᵥ e) - w • (G *ᵥ e) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hrw] at hsol
    ext k
    simpa [Matrix.toLpLin_apply] using congrFun hsol k
  set u : EuclideanSpace ℂ n := WithLp.toLp 2 (G *ᵥ e) with hu
  have hT : (Matrix.toEuclideanLin H).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hinner : ⟪u, Matrix.toEuclideanLin H u - w • u⟫ = ⟪u, Matrix.toEuclideanLin H u⟫ - w * ⟪u, u⟫ := by
    rw [inner_sub_right, inner_smul_right]
  have hre : (⟪u, u⟫ : ℂ).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have him : (⟪u, Matrix.toEuclideanLin H u - w • u⟫).im = -(w.im * ‖u‖ ^ 2) := by
    rw [hinner, Complex.sub_im, Complex.mul_im, RBM.im_inner_self_symm hT u,
      show (⟪u, u⟫ : ℂ).im = 0 from inner_self_im (𝕜 := ℂ) u, hre]
    ring
  rw [hEuclid] at him
  have hrhs : ⟪u, WithLp.toLp 2 e⟫ = starRingEnd ℂ (u.ofLp i) := by
    have := EuclideanSpace.inner_single_right (𝕜 := ℂ) i (1 : ℂ) u
    simpa [he, EuclideanSpace.single] using this
  rw [hrhs, Complex.conj_im] at him
  have hentry : (G *ᵥ e) i = G i i := by simp [he, Matrix.mulVec_single]
  have hui : u.ofLp i = G i i := by simpa [hu] using hentry
  rw [hui] at him
  have hnorm : ‖u‖ ^ 2 = ∑ k, ‖G k i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (G *ᵥ e) k = G k i := by simp [he, Matrix.mulVec_single]
    simp [hu, this]
  rw [hnorm] at him
  linarith


/-- column `ℓ²` bound `Σ_k |G_{ki}|² ≤ (Im w)⁻²`. -/
theorem BAcolSq_le {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {w : ℂ} (hw : 0 < w.im) (i : n) :
    ∑ k, ‖Ring.inverse (H - w • (1 : Matrix n n ℂ)) k i‖ ^ 2 ≤ (w.im ^ 2)⁻¹ := by
  set G := Ring.inverse (H - w • (1 : Matrix n n ℂ)) with hG
  set e : n → ℂ := Pi.single i 1 with he
  have hunit := RBM.isUnit_sub_smul_of_isHermitian hH hw.ne'
  have hsol : (H - w • (1 : Matrix n n ℂ)) *ᵥ (G *ᵥ e) = e := by
    rw [Matrix.mulVec_mulVec, hG, Ring.mul_inverse_cancel _ hunit, Matrix.one_mulVec]
  have hEuclid : Matrix.toEuclideanLin H (WithLp.toLp 2 (G *ᵥ e)) - w • WithLp.toLp 2 (G *ᵥ e)
      = WithLp.toLp 2 e := by
    have hrw : (H - w • (1 : Matrix n n ℂ)) *ᵥ (G *ᵥ e) = H *ᵥ (G *ᵥ e) - w • (G *ᵥ e) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hrw] at hsol
    ext k
    simpa [Matrix.toLpLin_apply] using congrFun hsol k
  have hnorm := RBM.norm_le_of_sub_smul_eq (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) hw.ne' hEuclid
  have hone : ‖WithLp.toLp 2 e‖ = 1 := by simp [he, PiLp.norm_single]
  rw [hone, mul_one, abs_of_pos hw] at hnorm
  have hsq : ‖WithLp.toLp 2 (G *ᵥ e)‖ ^ 2 ≤ (w.im ^ 2)⁻¹ := by
    have h0 : 0 ≤ ‖WithLp.toLp 2 (G *ᵥ e)‖ := norm_nonneg _
    calc ‖WithLp.toLp 2 (G *ᵥ e)‖ ^ 2 ≤ (w.im⁻¹) ^ 2 := pow_le_pow_left₀ h0 hnorm 2
      _ = (w.im ^ 2)⁻¹ := by rw [inv_pow]
  rw [EuclideanSpace.norm_sq_eq] at hsq
  have hcol : ∀ k, (G *ᵥ e) k = G k i := by
    intro k; simp [he, Matrix.mulVec_single]
  simpa [hcol] using hsq

/-- Cauchy–Schwarz lower bound `1 ≤ (Σ_k |(H-w)_{ik}|²)(Σ_k |G_{ki}|²)`. -/
theorem BAcolSq_ge {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {w : ℂ} (hw : 0 < w.im) (i : n) :
    1 ≤ (∑ k, ‖(H - w • (1 : Matrix n n ℂ)) i k‖ ^ 2) *
      ∑ k, ‖Ring.inverse (H - w • (1 : Matrix n n ℂ)) k i‖ ^ 2 := by
  set G := Ring.inverse (H - w • (1 : Matrix n n ℂ)) with hG
  have hunit := RBM.isUnit_sub_smul_of_isHermitian hH hw.ne'
  have h1 : ((H - w • (1 : Matrix n n ℂ)) * G) i i = 1 := by
    rw [hG, Ring.mul_inverse_cancel _ hunit]; simp
  rw [Matrix.mul_apply] at h1
  have h2 : (1 : ℝ) ≤ ∑ k, ‖(H - w • (1 : Matrix n n ℂ)) i k‖ * ‖G k i‖ := by
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖∑ k, (H - w • (1 : Matrix n n ℂ)) i k * G k i‖ := by rw [h1]
      _ ≤ ∑ k, ‖(H - w • (1 : Matrix n n ℂ)) i k * G k i‖ := norm_sum_le _ _
      _ = ∑ k, ‖(H - w • (1 : Matrix n n ℂ)) i k‖ * ‖G k i‖ := by simp
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n)
    (fun k => ‖(H - w • (1 : Matrix n n ℂ)) i k‖) (fun k => ‖G k i‖)
  have h4 : (1 : ℝ) ≤ (∑ k, ‖(H - w • (1 : Matrix n n ℂ)) i k‖ * ‖G k i‖) ^ 2 := by
    nlinarith
  exact h4.trans h3


theorem BAcard_Zd (d L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

theorem BArow_le (d L : ℕ) [NeZero L] (g : ℝ) (w : ℂ) (i : Zd d L) :
    ∑ k, ‖((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) i k‖ ^ 2
      ≤ ‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ) := by
  have hpt : ∀ k : Zd d L, ‖((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) i k‖ ^ 2
      ≤ g ^ 2 + (if i = k then ‖w‖ ^ 2 else 0) := by
    intro k
    by_cases hik : i = k
    · subst hik
      have hdiag : PsiB d L i i = 0 := by
        have : ¬ Adj d L i i := by simp [Adj, zdistD_zero]
        simp [PsiB, Matrix.of_apply, this]
      have hval : ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) i i = -w := by
        simp [hdiag, Matrix.sub_apply, Matrix.smul_apply]
      have hite : (if i = i then ‖w‖ ^ 2 else 0) = ‖w‖ ^ 2 := by simp
      rw [hval, norm_neg, hite]
      linarith [sq_nonneg g]
    · have h1 : (1 : Matrix (Zd d L) (Zd d L) ℂ) i k = 0 := by simp [Matrix.one_apply, hik]
      have hp : ‖PsiB d L i k‖ ≤ 1 := by
        by_cases h : Adj d L i k <;> simp [PsiB, Matrix.of_apply, h]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, h1, mul_zero, sub_zero, hik,
        ite_false, add_zero]
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have : ‖PsiB d L i k‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (PsiB d L i k)]
      nlinarith [sq_nonneg g]
  calc ∑ k, ‖((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) i k‖ ^ 2
      ≤ ∑ k : Zd d L, (g ^ 2 + (if i = k then ‖w‖ ^ 2 else 0)) := Finset.sum_le_sum fun k _ => hpt k
    _ = ‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ,
          BAcard_Zd, nsmul_eq_mul]
        simp
        ring



/-! ## 1. The deterministic layer: `(self_m)`, `(def_G0)`, `e_λ`-free bulk, `zztE_BA`, `lem:propM`

`m(z, g)` is the unique solution of `(self_m)` in `ℂ_+` (pin `BAmExists`); `M^{(B)}(z) = (gΨ^{(B)} - z - m)⁻¹`
lives on the block torus (`M = M^{(B)} ⊗ I_{W^d}`, `1_2:631`).  Nothing refers to the measure `μ_N`, to
`supp μ_N` or to the edge `e_λ`: the bulk is a condition on `m` itself (section 2). -/

section Det
variable (d L : ℕ) [NeZero L]

/-- `M^{(B)}(z) = (g Ψ^{(B)} - z - m)⁻¹` of `(def_G0)` (`1_2:631`), the value `m` given. -/
def BAMB (g : ℝ) (z m : ℂ) : Matrix (Zd d L) (Zd d L) ℂ := Mres ((g : ℂ) • PsiB d L) z m

/-- **`(self_m)`** (`1_2:626-629`): `m = L^{-d} tr (g Ψ^{(B)} - z - m)⁻¹`, `Im m > 0`. -/
def BASelf (g : ℝ) (z m : ℂ) : Prop :=
  0 < m.im ∧ m = (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g z m).trace

/-- The subordination datum `m_w = L^{-d} tr (g Ψ^{(B)} - w)⁻¹`. -/
def BAmSubord (g : ℝ) (w : ℂ) : ℂ :=
  (((L ^ d : ℕ) : ℂ))⁻¹ * (Ring.inverse ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ))).trace

theorem BAPsi_isHermitian (g : ℝ) : ((g : ℂ) • PsiB d L).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiB_isHermitian d L).eq, show star (g : ℂ) = (g : ℂ) from Complex.conj_ofReal _]

theorem BAmSubord_im (g : ℝ) {w : ℂ} (hw : 0 < w.im) :
    (BAmSubord d L g w).im = (((L ^ d : ℕ) : ℝ))⁻¹ * ∑ i, (w.im *
      ∑ k, ‖Ring.inverse ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) k i‖ ^ 2) := by
  unfold BAmSubord
  have hc : (((L ^ d : ℕ) : ℂ))⁻¹ = ((((L ^ d : ℕ) : ℝ))⁻¹ : ℝ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hc, Complex.im_ofReal_mul, Matrix.trace, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa [Matrix.diag] using BAimInv_diag (BAPsi_isHermitian d L g) hw i

theorem BASelf_subord (g : ℝ) {w : ℂ} (hw : 1 < w.im) :
    BASelf d L g (w - BAmSubord d L g w) (BAmSubord d L g w) ∧
      w.im / (‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ)) ≤ (BAmSubord d L g w).im ∧
      (BAmSubord d L g w).im ≤ w.im⁻¹ ∧ 0 < (w - BAmSubord d L g w).im := by
  have hw0 : 0 < w.im := by linarith
  have hH := BAPsi_isHermitian d L g
  have hN : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    exact_mod_cast this
  have him := BAmSubord_im d L g hw0
  have hRpos : 0 < ‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ) := by
    have : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw0)
    positivity
  -- lower and upper bounds for every column
  have hlow : ∀ i : Zd d L, 1 / (‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ)) ≤
      ∑ k, ‖Ring.inverse ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) k i‖ ^ 2 := by
    intro i
    have h1 := BAcolSq_ge hH hw0 i
    have h2 := BArow_le d L g w i
    have hS : 0 ≤ ∑ k, ‖Ring.inverse ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) k i‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    rw [div_le_iff₀ hRpos]
    nlinarith
  have hup : ∀ i : Zd d L, ∑ k, ‖Ring.inverse ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) k i‖ ^ 2
      ≤ (w.im ^ 2)⁻¹ := fun i => BAcolSq_le hH hw0 i
  have hcard : (Finset.univ : Finset (Zd d L)).card = L ^ d := by
    rw [Finset.card_univ, BAcard_Zd]
  have hlowIm : w.im / (‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ)) ≤ (BAmSubord d L g w).im := by
    rw [him]
    have : ∑ i : Zd d L, (w.im * ∑ k, ‖Ring.inverse ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) k i‖ ^ 2)
        ≥ ∑ i : Zd d L, w.im * (1 / (‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ))) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlow i) hw0.le
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
    have h3 : (((L ^ d : ℕ) : ℝ))⁻¹ * ((L ^ d : ℕ) * (w.im * (1 / (‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ)))))
        = w.im / (‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ)) := by
      field_simp
    calc w.im / (‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ))
        = (((L ^ d : ℕ) : ℝ))⁻¹ * ((L ^ d : ℕ) * (w.im * (1 / (‖w‖ ^ 2 + g ^ 2 * (L ^ d : ℕ))))) := h3.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have hupIm : (BAmSubord d L g w).im ≤ w.im⁻¹ := by
    rw [him]
    have : ∑ i : Zd d L, (w.im * ∑ k, ‖Ring.inverse ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) k i‖ ^ 2)
        ≤ ∑ i : Zd d L, w.im * (w.im ^ 2)⁻¹ :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hup i) hw0.le
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
    have h3 : (((L ^ d : ℕ) : ℝ))⁻¹ * ((L ^ d : ℕ) * (w.im * (w.im ^ 2)⁻¹)) = w.im⁻¹ := by
      field_simp
    calc (((L ^ d : ℕ) : ℝ))⁻¹ * _ ≤ (((L ^ d : ℕ) : ℝ))⁻¹ * ((L ^ d : ℕ) * (w.im * (w.im ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = w.im⁻¹ := h3
  have hmpos : 0 < (BAmSubord d L g w).im := by
    refine lt_of_lt_of_le ?_ hlowIm
    positivity
  have hzpos : 0 < (w - BAmSubord d L g w).im := by
    rw [Complex.sub_im]
    have : w.im⁻¹ < 1 := inv_lt_one_of_one_lt₀ hw
    linarith
  refine ⟨⟨?_, ?_⟩, hlowIm, hupIm, hzpos⟩
  · exact hmpos
  · have hz : (w - BAmSubord d L g w) + BAmSubord d L g w = w := sub_add_cancel _ _
    simp only [BAMB, Mres, hz]
    rfl


def BAt0 (z m : ℂ) : ℝ := m.im / (m.im + z.im)
def BAflowE (z m : ℂ) : ℝ := (BAt0 z m * z.re - (1 - BAt0 z m) * m.re) / Real.sqrt (BAt0 z m)

theorem BAt0_pos {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im) : 0 < BAt0 z m := by
  unfold BAt0; positivity

theorem BAt0_lt_one {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im) : BAt0 z m < 1 := by
  unfold BAt0
  rw [div_lt_one (by linarith)]
  linarith

theorem BAt0_mul {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im) :
    BAt0 z m * z.im = (1 - BAt0 z m) * m.im := by
  unfold BAt0
  have : m.im + z.im ≠ 0 := by linarith
  field_simp
  ring

theorem BAzztE_data (g : ℝ) {z m : ℂ} (hz : 0 < z.im) (hm : BASelf d L g z m) :
    0 < BAt0 z m ∧ BAt0 z m < 1 ∧
      BASelf d L (Real.sqrt (BAt0 z m) * g) (BAflowE z m : ℂ) (m / (Real.sqrt (BAt0 z m) : ℂ)) ∧
      ztOf (m / (Real.sqrt (BAt0 z m) : ℂ)) (BAflowE z m) (BAt0 z m) = (Real.sqrt (BAt0 z m) : ℂ) * z ∧
      (Real.sqrt (BAt0 z m) : ℂ) • BAMB d L (Real.sqrt (BAt0 z m) * g) (BAflowE z m : ℂ)
          (m / (Real.sqrt (BAt0 z m) : ℂ)) = BAMB d L g z m := by
  obtain ⟨hmpos, hmeq⟩ := hm
  have ht0 := BAt0_pos hz hmpos
  have ht1 := BAt0_lt_one hz hmpos
  have hmul := BAt0_mul hz hmpos
  set t0 := BAt0 z m with ht0def
  set s := Real.sqrt t0 with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr ht0
  have hss : s * s = t0 := Real.mul_self_sqrt ht0.le
  have hss2 : s ^ 2 = t0 := by rw [sq]; exact hss
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hEdef : BAflowE z m = (t0 * z.re - (1 - t0) * m.re) / s := rfl
  -- the key complex identities
  have hkey : (BAflowE z m : ℂ) + m / (s : ℂ) = (s : ℂ) * (z + m) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.div_ofReal_re, Complex.mul_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im]
      rw [hEdef]
      field_simp
      linear_combination (-(z.re + m.re)) * hss2
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.div_ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.add_re, zero_add]
      field_simp
      linear_combination (-(z.im + m.im)) * hss2 - hmul
  have hzt : ztOf (m / (s : ℂ)) (BAflowE z m) t0 = (s : ℂ) * z := by
    unfold ztOf
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.div_ofReal_re,
        Complex.div_ofReal_im, zero_mul, sub_zero]
      rw [hEdef]
      field_simp
      linear_combination (-z.re) * hss2
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.sub_re, Complex.one_re,
        Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.div_ofReal_re,
        Complex.div_ofReal_im, zero_add]
      field_simp
      linear_combination (-z.im) * hss2 - hmul
  -- the matrix identity
  set A := (g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ) with hA
  have hzm : 0 < (z + m).im := by simp; linarith
  have hAdet : IsUnit A.det := by
    have := isUnit_sub_smul_of_isHermitian (BAPsi_isHermitian d L g) hzm.ne'
    rw [Matrix.isUnit_iff_isUnit_det] at this
    exact this
  have hmat : ((s * g : ℝ) : ℂ) • PsiB d L - ((BAflowE z m : ℂ) + m / (s : ℂ)) • (1 : Matrix (Zd d L) (Zd d L) ℂ)
      = (s : ℂ) • A := by
    rw [hkey, hA, smul_sub, smul_smul, smul_smul, Complex.ofReal_mul]
  have hMB : (s : ℂ) • BAMB d L (s * g) (BAflowE z m : ℂ) (m / (s : ℂ)) = BAMB d L g z m := by
    unfold BAMB Mres
    rw [hmat, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse]
    have hinv : Invertible (s : ℂ) := invertibleOfNonzero hsc
    rw [Matrix.inv_smul A (s : ℂ) hAdet, smul_smul, invOf_eq_inv, mul_inv_cancel₀ hsc, one_smul]
  refine ⟨ht0, ht1, ⟨?_, ?_⟩, hzt, hMB⟩
  · -- Im m₀ > 0
    simp only [Complex.div_ofReal_im]
    exact div_pos hmpos hspos
  · -- m₀ = L^{-d} tr M₀
    have hM0 : BAMB d L (s * g) (BAflowE z m : ℂ) (m / (s : ℂ)) = (s : ℂ)⁻¹ • BAMB d L g z m := by
      rw [← hMB, smul_smul, inv_mul_cancel₀ hsc, one_smul]
    rw [hM0, Matrix.trace_smul, smul_eq_mul]
    calc m / (s : ℂ) = (s : ℂ)⁻¹ * m := by ring
      _ = (s : ℂ)⁻¹ * ((((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g z m).trace) := by rw [← hmeq]
      _ = _ := by ring

end Det

/-- Target 1 (new vocabulary): the spectrum of `g Ψ^{(B)}`, `v_i = g λ_i(Ψ^{(B)})` (the eigenvalues of the merged
`PsiB_isHermitian`, scaled; no proof term of the scaled matrix enters). -/
def BAspec (d L : ℕ) [NeZero L] (g : ℝ) : Zd d L → ℝ :=
  fun i => g * (PsiB_isHermitian d L).eigenvalues i

section DetPins

variable (d L : ℕ) [NeZero L]

/-- **`m(z, g)`** of `(self_m)`: the solution with `Im m > 0`; `0` if `(self_m)` has none. -/
def BAm (g : ℝ) (z : ℂ) : ℂ :=
  haveI := Classical.propDecidable (∃ m, BASelf d L g z m)
  if h : ∃ m, BASelf d L g z m then h.choose else 0

/-- **`ρ_N(E) = π⁻¹ Im m(E + i0)`** (`1_2:624`; DECISIONS §11, §51). -/
def BArho (g E : ℝ) : ℝ := (BAm d L g (E : ℂ)).im / Real.pi

/-- *Proved.* The averaged Ward identity for `(self_m)`: for `Im z ≥ 0` and a solution `m`,
`(Im m + Im z) · L^{-d} Σ_{a,b} |M^{(B)}_{ba}|² = Im m` (`= 1 · Im m` at real `z`: `(eq:WardM)`, `7_8:1869`,
summed over `a`; the row-wise identity is the pin `BAWard`). -/
theorem BAward_avg (g : ℝ) {z m : ℂ} (hz : 0 ≤ z.im) (hm : BASelf d L g z m) :
    (m.im + z.im) * ((((L ^ d : ℕ) : ℝ))⁻¹ * ∑ a : Zd d L, ∑ b : Zd d L, ‖BAMB d L g z m b a‖ ^ 2) = m.im := by
  obtain ⟨hmpos, hmeq⟩ := hm
  have hw : 0 < (z + m).im := by simp; linarith
  have hH := BAPsi_isHermitian d L g
  have hc : (((L ^ d : ℕ) : ℂ))⁻¹ = ((((L ^ d : ℕ) : ℝ))⁻¹ : ℝ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  have him : m.im = (((L ^ d : ℕ) : ℝ))⁻¹ * ∑ a : Zd d L, (z + m).im *
      ∑ b : Zd d L, ‖BAMB d L g z m b a‖ ^ 2 := by
    conv_lhs => rw [hmeq]
    rw [hc, Complex.im_ofReal_mul, Matrix.trace, Complex.im_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    have := BAimInv_diag hH hw a
    simpa [BAMB, Mres, Matrix.diag] using this
  have hsum : ∑ a : Zd d L, (z + m).im * ∑ b : Zd d L, ‖BAMB d L g z m b a‖ ^ 2 =
      (z + m).im * ∑ a : Zd d L, ∑ b : Zd d L, ‖BAMB d L g z m b a‖ ^ 2 := by
    rw [← Finset.mul_sum]
  rw [hsum] at him
  have hzm : (z + m).im = m.im + z.im := by simp [add_comm]
  rw [hzm] at him
  calc (m.im + z.im) * ((((L ^ d : ℕ) : ℝ))⁻¹ * ∑ a : Zd d L, ∑ b : Zd d L, ‖BAMB d L g z m b a‖ ^ 2)
      = (((L ^ d : ℕ) : ℝ))⁻¹ * ((m.im + z.im) * ∑ a : Zd d L, ∑ b : Zd d L, ‖BAMB d L g z m b a‖ ^ 2) := by
        ring
    _ = m.im := him.symm

end DetPins

/-! ## 2. The bulk condition (DECISIONS §51)

The bulk set is `B_κ = {E : ρ_N(E) ≥ κ}` with `ρ_N = π⁻¹ Im m(E + i0)` (`1_2:624`), `m` the real-axis
solution of `(self_m)` (unique, `BASelf_unique`); the chain domain `BAdom` is the complex-`z` condition
`Im m(z, g) ≥ κ`.  The edge forms of the probe (`|E| ≤ e_λ - κ`, `dist(E, ℝ ∖ supp μ_N) ≥ κ`) are not ported. -/

section Bulk

variable (d L : ℕ) [NeZero L]


/-- **The bulk set `B_κ = {E : ρ_N(E) ≥ κ}`** (DECISIONS §51). -/
def BAbulk (g κ E : ℝ) : Prop := κ ≤ BArho d L g E

/-- The data of the real-axis pins: `m` solves `(self_m)` at the real energy `E` and `κ ≤ Im m`. -/
def BAReal (g κ E : ℝ) (m : ℂ) : Prop := BASelf d L g (E : ℂ) m ∧ κ ≤ m.im

/-- The chain domain at a complex point: `Im m(z, g) ≥ κ`, `N^{-1+ε} ≤ Im z ≤ 1`. -/
def BAdom (N : ℕ) (g κ ε : ℝ) (z : ℂ) : Prop :=
  κ ≤ (BAm d L g z).im ∧ (N : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1

variable {d L}

/-- *Proved.* `m(z, g)` is a solution when one exists. -/
theorem BAm_spec {g : ℝ} {z : ℂ} (h : ∃ m, BASelf d L g z m) : BASelf d L g z (BAm d L g z) := by
  unfold BAm
  split_ifs
  exact h.choose_spec

/-- *Proved.* Form 3 is "a real-axis solution with `Im m ≥ πκ`" (uniqueness on the real axis,
pin `BAmUniqReal`, makes `ρ_N(E)` the imaginary part of that solution). -/
theorem BAbulk_iff {g κ E : ℝ} (hκ : 0 < κ)
    (huniq : ∀ m m' : ℂ, BASelf d L g (E : ℂ) m → BASelf d L g (E : ℂ) m' → m = m') :
    BAbulk d L g κ E ↔ ∃ m : ℂ, BASelf d L g (E : ℂ) m ∧ Real.pi * κ ≤ m.im := by
  have hpi := Real.pi_pos
  constructor
  · intro h
    have hρ : κ ≤ (BAm d L g (E : ℂ)).im / Real.pi := h
    have hne : ∃ m, BASelf d L g (E : ℂ) m := by
      by_contra hno
      have : BAm d L g (E : ℂ) = 0 := by
        unfold BAm
        split_ifs
        rfl
      rw [this] at hρ
      simp at hρ
      linarith
    refine ⟨BAm d L g (E : ℂ), BAm_spec hne, ?_⟩
    rw [le_div_iff₀ hpi] at hρ
    linarith
  · rintro ⟨m, hm, hle⟩
    have hne : ∃ m, BASelf d L g (E : ℂ) m := ⟨m, hm⟩
    have h1 := BAm_spec hne
    have h2 : BAm d L g (E : ℂ) = m := huniq _ _ h1 hm
    change κ ≤ (BAm d L g (E : ℂ)).im / Real.pi
    rw [h2, le_div_iff₀ hpi]
    linarith

/-- *Proved.* **The chain domain gives bulk data at the flow parameters** (`zztE_BA`, `7_8:1796`): if
`m = m(z, g)` solves `(self_m)` and `κ ≤ Im m`, then `m₀ = m/√t₀` solves `(self_m)` at the real energy
`E = E(z)` and the coupling `g₀ = √t₀ g ≤ g`, with `κ ≤ Im m₀` (`√t₀ ≤ 1`); so the real-axis pins
`BAPropM`, `BAProp5`-`BAProp8` apply at `(g₀, E, m₀)`. -/
theorem BAdom_real {g κ : ℝ} {z : ℂ} (hz : 0 < z.im) (hm : BASelf d L g z (BAm d L g z))
    (hκ : κ ≤ (BAm d L g z).im) :
    BAReal d L (Real.sqrt (BAt0 z (BAm d L g z)) * g) κ (BAflowE z (BAm d L g z))
      (BAm d L g z / (Real.sqrt (BAt0 z (BAm d L g z)) : ℂ)) := by
  obtain ⟨ht0, ht1, hself, -, -⟩ := BAzztE_data d L g hz hm
  set t0 := BAt0 z (BAm d L g z)
  have hs1 : Real.sqrt t0 ≤ 1 := Real.sqrt_le_one.mpr ht1.le
  have hspos : 0 < Real.sqrt t0 := Real.sqrt_pos.mpr ht0
  refine ⟨hself, ?_⟩
  simp only [Complex.div_ofReal_im]
  rw [le_div_iff₀ hspos]
  nlinarith [hm.1]

/-- *Proved.* The flow coupling is at most the coupling: `g₀ = √t₀ g ≤ g` for `g ≥ 0`, `t₀ < 1`. -/
theorem BAg0_le {g : ℝ} (hg : 0 ≤ g) {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im) :
    Real.sqrt (BAt0 z m) * g ≤ g := by
  have hs1 : Real.sqrt (BAt0 z m) ≤ 1 := Real.sqrt_le_one.mpr (BAt0_lt_one hz hm).le
  nlinarith

end Bulk

/-! ### The matrices `M^{(σ₁,σ₂)}` and the propagators `Θ_t^{(σ₁,σ₂)}` of the block Anderson model -/

section Thetas

variable (d L : ℕ) [NeZero L]

/-- `M(σ)`: `M(+) = M^{(B)}`, `M(-) = (M^{(B)})^*` (`1_2:1071`). -/
def BAMsigma (M : Matrix (Zd d L) (Zd d L) ℂ) (σ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  if σ then M else Mᴴ

/-- `M^{(σ₁,σ₂)}_{ab} = M^{(B)}_{ba}(σ₁) M^{(B)}_{ab}(σ₂)` (`(eq:Msig)`, `1_2:1070-1071`). -/
def BAMss (M : Matrix (Zd d L) (Zd d L) ℂ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun a b => BAMsigma d L M σ₁ b a * BAMsigma d L M σ₂ a b

/-- `Θ_t^{(σ₁,σ₂)} = (1 - t M^{(σ₁,σ₂)})⁻¹` (`(def_Thxi)`, `1_2:1073-1076`) at the real-axis data `(g, E, m)`. -/
def BATheta (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  PropThetaQ (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) t

/-- `Θ̊`: the propagator without its zero mode (`(def_Thxi0)`, `1_2:1105`). -/
def BATheta0 (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun a b => BATheta d L g E m t σ₁ σ₂ a b
    - ((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', BATheta d L g E m t σ₁ σ₂ a' b'

end Thetas

/-! ## 3. The pins of the deterministic layer (`lem:propM`, `(eq:off_diagM)`, BA-1, BA-2, BA-4)

All are quantified over the real-axis data `BAReal d L g κ E m`; constants `C, c, ε` are fixed before
`L`, `g`, `E`, `m` and depend on `(d, Λ, κ)` only (`Λ = 𝔡⁻¹`: DECISIONS §18; the numerics of the report
(b.4) show the `Λ`-dependence is real: `D_eff = (2d)⁻¹ Σ_a K_{0a}|a|²` saturates near `3` for `g ≥ 3`). -/

section DetPins2

variable (d : ℕ)

/-- **Pin BA-1, existence and uniqueness of `m(z, g)`** (`1_2:626-629`).  Proved by `baMExists_holds`. -/
def BAmExists : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ z : ℂ, 0 < z.im →
    haveI : NeZero L := ⟨by omega⟩
    ∃! m : ℂ, BASelf d L g z m

/-- **Pin BA-1, uniqueness on the real axis.**  Proved by `baMUniqReal_holds`. -/
def BAmUniqReal : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m m' : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BASelf d L g (E : ℂ) m → BASelf d L g (E : ℂ) m' → m = m'

/-- **Pin BA-2, the boundary value** (`1_2:715`).  Owed: BA-D6. -/
def BAmBoundary : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ E : ℝ,
    haveI : NeZero L := ⟨by omega⟩
    (∀ m : ℂ, BASelf d L g (E : ℂ) m →
      Tendsto (fun η : ℝ => BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m)) ∧
    ((¬ ∃ m : ℂ, BASelf d L g (E : ℂ) m) →
      Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0))

/-- **Pin BA-1, Ward's identity row by row** (`(eq:WardM)`, `7_8:1869`), translation invariance, `M_aa = m`.
Owed: BA-D3. -/
def BAWard : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (z m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    0 ≤ z.im → BASelf d L g z m →
      (∀ a b r : Zd d L, BAMB d L g z m (a + r) (b + r) = BAMB d L g z m a b) ∧
      (∀ a : Zd d L, BAMB d L g z m a a = m) ∧
      ∀ a : Zd d L, (m.im + z.im) * ∑ b, ‖BAMB d L g z m a b‖ ^ 2 = m.im

/-- **`lem:propM`** (`7_8:1847-1912`) in the bulk `κ ≤ Im m`.  Owed: BA-D3 (items (1)(2)), BA-D4 (item (3)). -/
def BAPropM (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m →
          (∀ a b r : Zd d L, BAMB d L g (E : ℂ) m (a + r) (b + r) = BAMB d L g (E : ℂ) m a b) ∧
          (∀ a : Zd d L, BAMB d L g (E : ℂ) m a a = m) ∧
          (∀ a : Zd d L, ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1) ∧ ‖m‖ ≤ 1 ∧
          (g < (2 * C)⁻¹ → ∀ a b : Zd d L,
            C⁻¹ * g * (if Adj d L a b then 1 else 0) ≤ ‖BAMB d L g (E : ℂ) m a b‖ ∧
              ‖BAMB d L g (E : ℂ) m a b‖ ≤ (C * g) ^ zdistD d L (a - b)) ∧
          ((2 * C)⁻¹ ≤ g → ∀ a b : Zd d L,
            ‖BAMB d L g (E : ℂ) m a b‖ ≤ c⁻¹ * Real.exp (-c * (zdistD d L (a - b) : ℝ)))

/-- **`(eq:off_diagM)`** (`A:32-34`).  Owed: BA-D3. -/
def BAoffDiag (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          ε ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧
          ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
            ≤ (1 - ε) * ‖1 - (t : ℂ) * m ^ 2‖

/-- **The bridge of the bulk forms** (`[LeeSchSteYau2015, Lemma 3.5]`, internal).  Owed: BA-D7. -/
def BAImmLower (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ η : ℝ, 0 < η → η ≤ 1 →
          c ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im

end DetPins2

/-! ## 4. `(self_m)` is the free-convolution equation `[32] (2.5)` at `t = 1`: existence and uniqueness

The spectral bridge (`BAMB_trace_eq_sum`, the model is `RBM.Univ.InjSum_green_eq_spectral`, a private
copy of RBM2D `Delocalization.lean:47` at `c9a24cf`, `RBM3D/Universality/InjSum.lean:43`), the
identification of `(self_m)` with the merged `freeConv_existsUnique` at `v = BAspec d L g`, `t = 1`
(`BASelf_iff_freeConv`), and uniqueness for every `Im z ≥ 0` from the averaged Ward identity and the
Hilbert-Schmidt identity (`BASelf_unique`; no spectral input). -/

/-- Spectral decomposition of `(g Ψ - w)⁻¹` for a Hermitian `Ψ` (the scaled eigenvalues `g λ_l`),
as in `RBM.Univ.InjSum_green_eq_spectral` (RBM2D `Delocalization.lean:47` at `c9a24cf`). -/
private theorem MFixedPoint_inv_spectral {n : Type*} [Fintype n] [DecidableEq n]
    {Ψ : Matrix n n ℂ} (hΨ : Ψ.IsHermitian) (g : ℝ) {w : ℂ}
    (hw : ∀ l, ((g * hΨ.eigenvalues l : ℝ) : ℂ) ≠ w) :
    Ring.inverse ((g : ℂ) • Ψ - w • (1 : Matrix n n ℂ)) =
      (hΨ.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun l => (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)⁻¹)
        * star (hΨ.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hΨ.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : Ψ = U * diagonal (fun l => (hΨ.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hΨ.spectral_theorem]
    rfl
  have hdiag : diagonal (fun l => ((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)
      = (g : ℂ) • diagonal (fun l => (hΨ.eigenvalues l : ℂ)) - w • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hsub : (g : ℂ) • Ψ - w • (1 : Matrix n n ℂ)
      = U * diagonal (fun l => ((g * hΨ.eigenvalues l : ℝ) : ℂ) - w) * star U := by
    have h2 : U * (w • (1 : Matrix n n ℂ)) * star U = w • (1 : Matrix n n ℂ) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU']
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, h2, Matrix.mul_smul, Matrix.smul_mul, ← hspec]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => ((g * hΨ.eigenvalues l : ℝ) : ℂ) - w) * star U
        * (U * diagonal (fun l => (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)⁻¹) * star U)
      = U * (diagonal (fun l => ((g * hΨ.eigenvalues l : ℝ) : ℂ) - w) * (star U * U)
          * diagonal (fun l => (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)
              * (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)⁻¹) = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hw l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

/-- **Spectral bridge**: `tr M^{(B)} = Σ_i (v_i - z - m)⁻¹` with `v = BAspec d L g`, when `Im (z + m) ≠ 0`
(`gΨ = U diag(gλ) U*`, trace cyclic). -/
theorem BAMB_trace_eq_sum (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
    (BAMB d L g z m).trace = ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹ := by
  intro g z m hzm
  have hw : ∀ l, ((g * (PsiB_isHermitian d L).eigenvalues l : ℝ) : ℂ) ≠ z + m := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact hzm this.symm
  unfold BAMB Mres
  rw [MFixedPoint_inv_spectral (PsiB_isHermitian d L) g hw]
  set U : Matrix (Zd d L) (Zd d L) ℂ := ((PsiB_isHermitian d L).eigenvectorUnitary : Matrix (Zd d L) (Zd d L) ℂ) with hU
  set D := diagonal (fun l => (((g * (PsiB_isHermitian d L).eigenvalues l : ℝ) : ℂ) - (z + m))⁻¹) with hD
  calc (U * D * star U).trace = (U * (D * star U)).trace := by rw [Matrix.mul_assoc]
    _ = ((D * star U) * U).trace := by rw [Matrix.trace_mul_comm]
    _ = (D * (star U * U)).trace := by rw [Matrix.mul_assoc]
    _ = D.trace := by rw [Unitary.coe_star_mul_self, Matrix.mul_one]
    _ = _ := by rw [hD, Matrix.trace_diagonal]; rfl


/-- **`(self_m)` is `[32] (2.5)` at `t = 1`**, in the exact form of `RBM.Univ.freeConv_existsUnique`
at `v = BAspec d L g` (`1_2:626-629`), for `0 ≤ Im z`. -/
theorem BASelf_iff_freeConv (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z m : ℂ), 0 ≤ z.im →
    (BASelf d L g z m ↔ 0 < m.im ∧
      m = ((Fintype.card (Zd d L) : ℕ) : ℂ)⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - z - ((1 : ℝ) : ℂ) * m)⁻¹) := by
  intro g z m hz
  unfold BASelf
  refine and_congr_right fun hm => ?_
  have hzm : (z + m).im ≠ 0 := by
    rw [Complex.add_im]; linarith
  rw [BAMB_trace_eq_sum d L g z m hzm, BAcard_Zd]
  have hi : ∀ i, (BAspec d L g i : ℂ) - z - ((1 : ℝ) : ℂ) * m = (BAspec d L g i : ℂ) - (z + m) := by
    intro i; push_cast; ring
  simp only [hi]

/-- **Existence** of a solution of `(self_m)` for `Im z > 0` (`RBM.Univ.freeConv_existsUnique` and
`BASelf_iff_freeConv`). -/
theorem BASelf_exists (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z : ℂ), 0 < z.im →
    ∃ m : ℂ, BASelf d L g z m := by
  intro g z hz
  obtain ⟨m, hm, -⟩ := RBM.Univ.freeConv_existsUnique (BAspec d L g) (t := 1) zero_le_one hz
  exact ⟨m, (BASelf_iff_freeConv d L g z m hz.le).mpr hm⟩

/-- Hilbert-Schmidt expansion `Σ |M_{ab} - conj M'_{ba}|² = Σ |M_{ab}|² + Σ |M'_{ba}|² - 2 Re tr (M M')`. -/
private theorem MFixedPoint_HS {n : Type*} [Fintype n] (M M' : Matrix n n ℂ) :
    ∑ a, ∑ b, ‖M a b - starRingEnd ℂ (M' b a)‖ ^ 2
      = ∑ a, ∑ b, ‖M a b‖ ^ 2 + ∑ a, ∑ b, ‖M' b a‖ ^ 2 - 2 * (M * M').trace.re := by
  have hpt : ∀ u v : ℂ, ‖u - starRingEnd ℂ v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (u * v).re := by
    intro u v
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im, Complex.mul_re]
    ring
  have htr : (M * M').trace.re = ∑ a, ∑ b, (M a b * M' b a).re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  rw [htr]
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- **Uniqueness** of the solution of `(self_m)` for every `Im z ≥ 0`, the real axis included, with no
spectral input: if `m ≠ m'` the resolvent identity gives `L^{-d} tr (M M') = 1`; the averaged Ward identity
(`BAward_avg`) gives `L^{-d} Σ |M_{ab}|² ≤ 1` for `M` and `M'`; then
`0 ≤ L^{-d} Σ |M_{ab} - conj M'_{ba}|² ≤ 0`, so `M = M'ᴴ`, `m = conj m'`, against `Im m, Im m' > 0`. -/
theorem BASelf_unique (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z m m' : ℂ), 0 ≤ z.im →
    BASelf d L g z m → BASelf d L g z m' → m = m' := by
  intro g z m m' hz hm hm'
  by_contra hne
  have hmim : 0 < m.im := hm.1
  have hmim' : 0 < m'.im := hm'.1
  have hH := BAPsi_isHermitian d L g
  have hnpos : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    exact_mod_cast this
  have hn0 : (((L ^ d : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hnpos.ne'
  set M := BAMB d L g z m with hM
  set M' := BAMB d L g z m' with hM'
  set P : Matrix (Zd d L) (Zd d L) ℂ := (g : ℂ) • PsiB d L - (z + m) • 1 with hP
  set Q : Matrix (Zd d L) (Zd d L) ℂ := (g : ℂ) • PsiB d L - (z + m') • 1 with hQ
  have hPu : IsUnit P := isUnit_sub_smul_of_isHermitian hH (by rw [Complex.add_im]; linarith)
  have hQu : IsUnit Q := isUnit_sub_smul_of_isHermitian hH (by rw [Complex.add_im]; linarith)
  have hMP : M * P = 1 := Ring.inverse_mul_cancel P hPu
  have hQM' : Q * M' = 1 := Ring.mul_inverse_cancel Q hQu
  -- traces
  have htr : M.trace = (((L ^ d : ℕ) : ℂ)) * m := by
    rw [hm.2]; field_simp [hn0]; rfl
  have htr' : M'.trace = (((L ^ d : ℕ) : ℂ)) * m' := by
    rw [hm'.2]; field_simp [hn0]; rfl
  -- the resolvent identity
  have hQP : Q - P = (m - m') • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    rw [hQ, hP, sub_sub_sub_cancel_left, ← sub_smul]
    congr 1; ring
  have hres : M - M' = (m - m') • (M * M') := by
    calc M - M' = M * (Q * M') - (M * P) * M' := by rw [hQM', hMP]; simp
      _ = M * (Q - P) * M' := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (m - m') • (M * M') := by
          rw [hQP, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have htrMM : (M * M').trace = (((L ^ d : ℕ) : ℂ)) := by
    have h1 := congrArg Matrix.trace hres
    rw [Matrix.trace_sub, Matrix.trace_smul, htr, htr', smul_eq_mul] at h1
    have hsub : m - m' ≠ 0 := sub_ne_zero.mpr hne
    apply mul_left_cancel₀ hsub
    linear_combination -h1
  -- Ward
  have hw1 := BAward_avg d L g hz hm
  have hw2 := BAward_avg d L g hz hm'
  have hT : ∑ a : Zd d L, ∑ b : Zd d L, ‖M b a‖ ^ 2 ≤ ((L ^ d : ℕ) : ℝ) := by
    have h1 : (m.im + z.im) * ((((L ^ d : ℕ) : ℝ))⁻¹ * ∑ a : Zd d L, ∑ b : Zd d L, ‖M b a‖ ^ 2)
        ≤ (m.im + z.im) * 1 := by linarith
    have h2 := le_of_mul_le_mul_left h1 (by linarith)
    rwa [inv_mul_le_iff₀ hnpos, mul_one] at h2
  have hT' : ∑ a : Zd d L, ∑ b : Zd d L, ‖M' b a‖ ^ 2 ≤ ((L ^ d : ℕ) : ℝ) := by
    have h1 : (m'.im + z.im) * ((((L ^ d : ℕ) : ℝ))⁻¹ * ∑ a : Zd d L, ∑ b : Zd d L, ‖M' b a‖ ^ 2)
        ≤ (m'.im + z.im) * 1 := by linarith
    have h2 := le_of_mul_le_mul_left h1 (by linarith)
    rwa [inv_mul_le_iff₀ hnpos, mul_one] at h2
  -- Hilbert-Schmidt
  have hHS := MFixedPoint_HS M M'
  rw [htrMM, Finset.sum_comm (f := fun a b => ‖M a b‖ ^ 2)] at hHS
  have hre : ((((L ^ d : ℕ) : ℂ))).re = ((L ^ d : ℕ) : ℝ) := Complex.natCast_re _
  rw [hre] at hHS
  have hS0 : ∑ a, ∑ b, ‖M a b - starRingEnd ℂ (M' b a)‖ ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity)
  have hterm : ∀ a b, M a b = starRingEnd ℂ (M' b a) := by
    intro a b
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)).mp hS0 a (Finset.mem_univ a)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg _)).mp h1 b (Finset.mem_univ b)
    have h3 : ‖M a b - starRingEnd ℂ (M' b a)‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hconj : (((L ^ d : ℕ) : ℂ)) * m = (((L ^ d : ℕ) : ℂ)) * starRingEnd ℂ m' := by
    have h1 : M.trace = starRingEnd ℂ M'.trace := by
      simp only [Matrix.trace, Matrix.diag, map_sum]
      exact Finset.sum_congr rfl fun a _ => hterm a a
    rw [htr, htr', map_mul, Complex.conj_natCast] at h1
    exact h1
  have hconj' := mul_left_cancel₀ hn0 hconj
  have him := congrArg Complex.im hconj'
  rw [Complex.conj_im] at him
  linarith


/-- **Pin BA-1, proved**: existence and uniqueness of `m(z, g)` for `Im z > 0`
(`BASelf_exists`, `BASelf_unique`).  The pin's `3 ≤ L` and `0 < g` are not needed. -/
theorem baMExists_holds (d : ℕ) : BAmExists d := by
  intro L hL g hg z hz
  have : NeZero L := ⟨by omega⟩
  obtain ⟨m, hm⟩ := BASelf_exists d L g z hz
  exact ⟨m, hm, fun m' hm' => BASelf_unique d L g z m' m hz.le hm' hm⟩

/-- **Pin BA-1, proved**: uniqueness on the real axis (`BASelf_unique` at `Im z = 0`).
The pin's `3 ≤ L` and `0 < g` are not needed. -/
theorem baMUniqReal_holds (d : ℕ) : BAmUniqReal d := by
  intro L hL g hg E m m' hm hm'
  have : NeZero L := ⟨by omega⟩
  exact BASelf_unique d L g (E : ℂ) m m' (by simp) hm hm'

/-- `m(z, g)` solves `(self_m)` for `Im z > 0`. -/
theorem BAm_self (d L : ℕ) [NeZero L] :
    ∀ (g : ℝ) (z : ℂ), 0 < z.im → BASelf d L g z (BAm d L g z) := by
  intro g z hz
  exact BAm_spec (BASelf_exists d L g z hz)

/-- `m(z, g)` is the merged free-convolution Stieltjes transform `freeConvST` of `v = BAspec d L g`,
`t = 1` (`[32] (2.5)`). -/
theorem BAm_eq_freeConvST (d L : ℕ) [NeZero L] :
    ∀ (g : ℝ) (z : ℂ), 0 < z.im → BAm d L g z = RBM.Univ.freeConvST (BAspec d L g) 1 z := by
  intro g z hz
  have h := RBM.Univ.isFreeConv51_freeConvST (BAspec d L g) (t := 1) zero_le_one z hz
  exact BASelf_unique d L g z _ _ hz.le (BAm_self d L g z hz)
    ((BASelf_iff_freeConv d L g z _ hz.le).mpr h)

/-- Unconditional form of the probe's `BAm_real_eq` (`:1740`): `m(E, g)` is any real-axis solution. -/
theorem BAm_real_eq_of_self (d L : ℕ) [NeZero L] :
    ∀ (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → BAm d L g (E : ℂ) = m := by
  intro g E m hm
  exact BASelf_unique d L g (E : ℂ) _ _ (by simp) (BAm_spec ⟨m, hm⟩) hm

/-- Unconditional form of the probe's `BAbulk_iff` (`:472`): the uniqueness hypothesis is `BASelf_unique`. -/
theorem BAbulk_iff_exists (d L : ℕ) [NeZero L] :
    ∀ (g κ E : ℝ), 0 < κ →
      (BAbulk d L g κ E ↔ ∃ m : ℂ, BASelf d L g (E : ℂ) m ∧ Real.pi * κ ≤ m.im) := by
  intro g κ E hκ
  exact BAbulk_iff hκ (fun m m' hm hm' => BASelf_unique d L g (E : ℂ) m m' (by simp) hm hm')

end RBM.BA

namespace RBM.BA.MFixedPointInst

open RBM RBM.Gauss

/-! ## 5. Compiled nonempty instances (`d = 3`, `L = 4`, `card (Zd 3 4) = 64`)

The data of the T2161 probe (`:1897-1953`, section 13): the subordination point `w = 6i/5`, the
point `(z_S, m_S)` with `z_S + m_S = w`, and a flow point `P` of `(L, g) = (4, 10)`
(`g₀ = √t₀ g`, a real energy `E`, `m₀`, `BAReal 3 4 g₀ (Im m₀) E m₀`). -/

/-- The subordination point `w = 6i/5`. -/
def wI : ℂ := ⟨0, 6 / 5⟩

private theorem MFixedPoint_wI_im : wI.im = 6 / 5 := rfl

theorem one_lt_wI : 1 < wI.im := by rw [MFixedPoint_wI_im]; norm_num

theorem wI_norm : ‖wI‖ = 6 / 5 := by
  have h : wI = ((6 / 5 : ℝ) : ℂ) * Complex.I := by apply Complex.ext <;> simp [wI]
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num

section Point

variable (L : ℕ) [NeZero L] (g : ℝ)

/-- `m_w = L^{-3} tr (g Ψ^{(B)} - w)⁻¹`. -/
def mS : ℂ := BAmSubord 3 L g wI

/-- `z_S = w - m_w ∈ ℂ_+`. -/
def zS : ℂ := wI - mS L g

theorem selfS : BASelf 3 L g (zS L g) (mS L g) := (BASelf_subord 3 L g one_lt_wI).1

theorem zS_im_pos : 0 < (zS L g).im := (BASelf_subord 3 L g one_lt_wI).2.2.2

end Point

/-- The flow data of the point: `κ = Im m₀ > 0`, `g₀ = √t₀ g ∈ (0, g]`, a real energy `E`, and `BAReal`. -/
structure FlowPt (L : ℕ) [NeZero L] (g : ℝ) where
  E : ℝ
  m0 : ℂ
  g0 : ℝ
  g0_pos : 0 < g0
  g0_le : g0 ≤ g
  real : BAReal 3 L g0 m0.im E m0

theorem exists_flowPt (L : ℕ) [NeZero L] {g : ℝ} (hg : 0 < g) : Nonempty (FlowPt L g) := by
  obtain ⟨ht0, ht1, hself0, hzt, hMB⟩ := BAzztE_data 3 L g (zS_im_pos L g) (selfS L g)
  have hm := (selfS L g).1
  refine ⟨⟨BAflowE (zS L g) (mS L g), mS L g / (Real.sqrt (BAt0 (zS L g) (mS L g)) : ℂ),
    Real.sqrt (BAt0 (zS L g) (mS L g)) * g, ?_, BAg0_le hg.le (zS_im_pos L g) hm, hself0, le_rfl⟩⟩
  exact mul_pos (Real.sqrt_pos.mpr ht0) hg

/-- The flow point of `(L, g) = (4, 10)`. -/
def P : FlowPt 4 10 := (exists_flowPt 4 (g := 10) (by norm_num)).some

/-! ### The pins `BAmExists`, `BAmUniqReal` at the data -/

/-- `baMExists_holds` at `(d, L, g, z) = (3, 4, 10, i)`: the solution of `(self_m)` exists and is unique. -/
example : ∃! m : ℂ, BASelf 3 4 10 Complex.I m :=
  baMExists_holds 3 4 (by norm_num) 10 (by norm_num) Complex.I (by simp)

/-- `baMUniqReal_holds` at the flow point `P` (real axis, `E = P.E`, `g = P.g0`). -/
example : BAm 3 4 P.g0 (P.E : ℂ) = P.m0 :=
  baMUniqReal_holds 3 4 (by norm_num) P.g0 P.g0_pos P.E _ _ (BAm_spec ⟨P.m0, P.real.1⟩) P.real.1

/-! ### The new theorems at `(L, g, z) = (4, 10, i)` -/

example : ∃ m : ℂ, BASelf 3 4 10 Complex.I m := BASelf_exists 3 4 10 Complex.I (by simp)

example : BASelf 3 4 10 Complex.I (BAm 3 4 10 Complex.I) := BAm_self 3 4 10 Complex.I (by simp)

example : BAm 3 4 10 Complex.I = RBM.Univ.freeConvST (BAspec 3 4 10) 1 Complex.I :=
  BAm_eq_freeConvST 3 4 10 Complex.I (by simp)

/-- `BAMB_trace_eq_sum` at `m = m(i, 10)`: `(z + m).im = 1 + Im m > 0`. -/
example : (BAMB 3 4 10 Complex.I (BAm 3 4 10 Complex.I)).trace
    = ∑ i, ((BAspec 3 4 10 i : ℂ) - (Complex.I + BAm 3 4 10 Complex.I))⁻¹ := by
  refine BAMB_trace_eq_sum 3 4 10 Complex.I _ ?_
  have h := (BAm_self 3 4 10 Complex.I (by simp)).1
  rw [Complex.add_im]
  simp only [Complex.I_im]
  linarith

example : 0 < (BAm 3 4 10 Complex.I).im ∧ BAm 3 4 10 Complex.I
    = ((Fintype.card (Zd 3 4) : ℕ) : ℂ)⁻¹ * ∑ i, ((BAspec 3 4 10 i : ℂ) - Complex.I
      - ((1 : ℝ) : ℂ) * BAm 3 4 10 Complex.I)⁻¹ :=
  (BASelf_iff_freeConv 3 4 10 Complex.I _ (by simp)).mp (BAm_self 3 4 10 Complex.I (by simp))

/-- `BASelf_unique` at `z = z_S` (`Im z > 0`). -/
example : mS 4 10 = BAm 3 4 10 (zS 4 10) :=
  BASelf_unique 3 4 10 (zS 4 10) _ _ (zS_im_pos 4 10).le (selfS 4 10)
    (BAm_self 3 4 10 _ (zS_im_pos 4 10))

/-- `BASelf_unique` at the flow point `(g₀, E)` (`Im z = 0`). -/
example : P.m0 = BAm 3 4 P.g0 (P.E : ℂ) :=
  BASelf_unique 3 4 P.g0 (P.E : ℂ) _ _ (by simp) P.real.1 (BAm_spec ⟨P.m0, P.real.1⟩)

example : BAm 3 4 P.g0 (P.E : ℂ) = P.m0 := BAm_real_eq_of_self 3 4 P.g0 P.E P.m0 P.real.1

/-- `BAbulk_iff_exists` at `P`, `κ = Im m₀ / π`: no uniqueness hypothesis. -/
example : BAbulk 3 4 P.g0 (P.m0.im / Real.pi) P.E :=
  (BAbulk_iff_exists 3 4 P.g0 (P.m0.im / Real.pi) P.E (div_pos P.real.1.1 Real.pi_pos)).mpr
    ⟨P.m0, P.real.1, le_of_eq (by field_simp)⟩

/-! ### The copied theorems of the proved base, through the data -/

example : (Ring.inverse ((10 : ℂ) • PsiB 3 4 - wI • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ)) 0 0).im
    = wI.im * ∑ k, ‖Ring.inverse ((10 : ℂ) • PsiB 3 4 - wI • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ)) k 0‖ ^ 2 :=
  BAimInv_diag (BAPsi_isHermitian 3 4 10) (by rw [MFixedPoint_wI_im]; norm_num) 0

example : ∑ k, ‖Ring.inverse ((10 : ℂ) • PsiB 3 4 - wI • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ)) k 0‖ ^ 2
    ≤ (wI.im ^ 2)⁻¹ :=
  BAcolSq_le (BAPsi_isHermitian 3 4 10) (by rw [MFixedPoint_wI_im]; norm_num) 0

example : 1 ≤ (∑ k, ‖((10 : ℂ) • PsiB 3 4 - wI • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ)) 0 k‖ ^ 2) *
    ∑ k, ‖Ring.inverse ((10 : ℂ) • PsiB 3 4 - wI • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ)) k 0‖ ^ 2 :=
  BAcolSq_ge (BAPsi_isHermitian 3 4 10) (by rw [MFixedPoint_wI_im]; norm_num) 0

example : Fintype.card (Zd 3 4) = 64 := by rw [BAcard_Zd]; norm_num

example : ∑ k, ‖(((10 : ℝ) : ℂ) • PsiB 3 4 - wI • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ)) 0 k‖ ^ 2
    ≤ ‖wI‖ ^ 2 + (10 : ℝ) ^ 2 * (4 ^ 3 : ℕ) :=
  BArow_le 3 4 10 wI 0

example : (((10 : ℝ) : ℂ) • PsiB 3 4).IsHermitian := BAPsi_isHermitian 3 4 10

example : (BAmSubord 3 4 10 wI).im = (((4 ^ 3 : ℕ) : ℝ))⁻¹ * ∑ i, (wI.im *
    ∑ k, ‖Ring.inverse (((10 : ℝ) : ℂ) • PsiB 3 4 - wI • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ)) k i‖ ^ 2) :=
  BAmSubord_im 3 4 10 (by rw [MFixedPoint_wI_im]; norm_num)

example := BASelf_subord 3 4 10 one_lt_wI

example := BAt0_pos (zS_im_pos 4 10) (selfS 4 10).1

example := BAt0_lt_one (zS_im_pos 4 10) (selfS 4 10).1

example := BAt0_mul (zS_im_pos 4 10) (selfS 4 10).1

example := BAzztE_data 3 4 10 (zS_im_pos 4 10) (selfS 4 10)

example := BAward_avg 3 4 10 (zS_im_pos 4 10).le (selfS 4 10)

example : BASelf 3 4 10 (zS 4 10) (BAm 3 4 10 (zS 4 10)) := BAm_spec ⟨_, selfS 4 10⟩

example : BAbulk 3 4 P.g0 (P.m0.im / Real.pi) P.E :=
  (BAbulk_iff (div_pos P.real.1.1 Real.pi_pos) (fun m m' hm hm' =>
    BASelf_unique 3 4 P.g0 (P.E : ℂ) m m' (by simp) hm hm')).mpr
    ⟨P.m0, P.real.1, le_of_eq (by field_simp)⟩

example := BAdom_real (g := 10) (κ := (BAm 3 4 10 (zS 4 10)).im) (zS_im_pos 4 10)
  (BAm_spec ⟨_, selfS 4 10⟩) le_rfl

example := BAg0_le (g := 10) (by norm_num) (zS_im_pos 4 10) (selfS 4 10).1

end RBM.BA.MFixedPointInst

end
