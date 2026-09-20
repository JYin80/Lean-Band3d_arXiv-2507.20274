/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Matrix.Hermitian

/-!
# The deterministic envelope: `‖(H - z)⁻¹‖ ≤ (Im z)⁻¹`

The bound that makes the moment route work without a smoothing cutoff: it holds on the
*whole* space, pointwise in `ω`, because Hermiticity of `H` is a pointwise fact.  Nothing
here is probabilistic, and nothing here is about random matrices; it is the elementary
estimate

  `|Im z| ‖v‖ ≤ ‖T v - z v‖`   for symmetric `T`,

from which invertibility of `T - z` and the bound on the inverse both follow.

## The shape of the statement

This project's matrices carry the `ℓ^∞` operator norm (`Matrix.Norms.Operator`), while the
resolvent bound is a statement about the **spectral** (`ℓ²`) norm: they are different
instances on the same type, and mixing them is the trap this file is written to avoid.  So
the content is stated for a symmetric operator on an inner product space, where no norm on
matrices appears at all, and `RBM.norm_sub_smul_ge_of_isHermitian` specializes it to a
Hermitian matrix acting on `EuclideanSpace ℂ n`.

## Main results

* `RBM.im_inner_self_symm` : `⟪v, T v⟫` is real for symmetric `T`
* `RBM.norm_sub_smul_ge` : `|Im z| ‖v‖ ≤ ‖T v - z • v‖`
* `RBM.injective_sub_smul` : `T - z` is injective when `Im z ≠ 0`
* `RBM.norm_le_of_sub_smul_eq` : the bound as it is used -- if `T u - z • u = w` then
  `‖u‖ ≤ |Im z|⁻¹ ‖w‖`
-/

namespace RBM

open RCLike ComplexConjugate
open scoped ComplexInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For a symmetric operator the quadratic form is real. -/
theorem im_inner_self_symm {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (v : E) :
    (⟪v, T v⟫).im = 0 := by
  have h : conj ⟪v, T v⟫ = ⟪v, T v⟫ := by
    rw [inner_conj_symm, hT v v]
  exact Complex.conj_eq_iff_im.mp h

/-- **The core estimate**: for symmetric `T`, `|Im z| ‖v‖ ≤ ‖T v - z v‖`.  Everything else
in this file is a corollary. -/
theorem norm_sub_smul_ge {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (z : ℂ) (v : E) :
    |z.im| * ‖v‖ ≤ ‖T v - z • v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hinner : ⟪v, T v - z • v⟫ = ⟪v, T v⟫ - z * ⟪v, v⟫ := by
    rw [inner_sub_right, inner_smul_right]
  have hre : (⟪v, v⟫ : ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  have him : (⟪v, T v - z • v⟫).im = -(z.im * ‖v‖ ^ 2) := by
    rw [hinner, Complex.sub_im, Complex.mul_im, im_inner_self_symm hT v,
      show (⟪v, v⟫ : ℂ).im = 0 from inner_self_im (𝕜 := ℂ) v, hre]
    ring
  have h1 : |z.im| * ‖v‖ ^ 2 = |(⟪v, T v - z • v⟫).im| := by
    rw [him, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖ ^ 2)]
  have h2 : |(⟪v, T v - z • v⟫).im| ≤ ‖v‖ * ‖T v - z • v‖ := by
    refine le_trans ?_ (norm_inner_le_norm (𝕜 := ℂ) v (T v - z • v))
    simpa using Complex.abs_im_le_norm (⟪v, T v - z • v⟫)
  have h3 : |z.im| * ‖v‖ ^ 2 ≤ ‖v‖ * ‖T v - z • v‖ := h1 ▸ h2
  have h4 : |z.im| * ‖v‖ * ‖v‖ ≤ ‖T v - z • v‖ * ‖v‖ := by nlinarith
  exact le_of_mul_le_mul_right h4 hvpos

/-- `T - z` is injective off the real axis. -/
theorem injective_sub_smul {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Injective fun v => T v - z • v := by
  intro u v huv
  have h : T (u - v) - z • (u - v) = 0 := by
    simp only [map_sub, smul_sub] at *
    rw [sub_sub_sub_comm] at *
    simpa [sub_eq_zero] using huv
  have := norm_sub_smul_ge hT z (u - v)
  rw [h, norm_zero] at this
  have habs : 0 < |z.im| := abs_pos.mpr hz
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v)]
  have : u - v = 0 := by
    simpa using norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
  exact sub_eq_zero.mp this

/-- **The envelope, in the form it is used**: a solution of `T u - z u = w` obeys
`‖u‖ ≤ |Im z|⁻¹ ‖w‖`. -/
theorem norm_le_of_sub_smul_eq {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {z : ℂ} (hz : z.im ≠ 0)
    {u w : E} (h : T u - z • u = w) : ‖u‖ ≤ |z.im|⁻¹ * ‖w‖ := by
  have habs : 0 < |z.im| := abs_pos.mpr hz
  have := norm_sub_smul_ge hT z u
  rw [h] at this
  rw [inv_mul_eq_div, le_div_iff₀ habs]
  linarith [this]

/-! ### The matrix form

`H` Hermitian, acting on `EuclideanSpace ℂ n`: this is the shape the envelope of the
stochastic layer needs.  Note again that the norm here is the `ℓ²` one carried by
`EuclideanSpace`, *not* this project's `ℓ^∞` operator norm on `Matrix`. -/

open Matrix in
/-- `|Im z| ‖v‖ ≤ ‖H v - z v‖` for a Hermitian matrix, in the `ℓ²` norm. -/
theorem norm_sub_smul_ge_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) (v : EuclideanSpace ℂ n) :
    |z.im| * ‖v‖ ≤ ‖Matrix.toEuclideanLin H v - z • v‖ :=
  norm_sub_smul_ge (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) z v

open Matrix in
/-- **The deterministic envelope for a Hermitian matrix**: a solution of `H u - z u = w`
obeys `‖u‖ ≤ |Im z|⁻¹ ‖w‖`, on the whole space and with no exceptional set. -/
theorem norm_le_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    {u w : EuclideanSpace ℂ n} (h : Matrix.toEuclideanLin H u - z • u = w) :
    ‖u‖ ≤ |z.im|⁻¹ * ‖w‖ :=
  norm_le_of_sub_smul_eq (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) hz h

/-! ### Consequences for the matrix inverse

What the loop estimates actually use: off the real axis `H - z` is invertible, and the
entries of its inverse are bounded by `|Im z|⁻¹`.  The entry bound is the one that survives
being multiplied together `n` times inside a `G`-loop. -/

open Matrix in
/-- Off the real axis, `H - z` is invertible. -/
theorem isUnit_sub_smul_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (H - z • (1 : Matrix n n ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hv0⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hmul : Matrix.toEuclideanLin H (WithLp.toLp 2 v) - z • (WithLp.toLp 2 v) = 0 := by
    have : (H - z • (1 : Matrix n n ℂ)) *ᵥ v = H *ᵥ v - z • v := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [this] at hv0
    ext i
    simpa [Matrix.toLpLin_apply] using congrFun hv0 i
  have hinj := injective_sub_smul (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) hz
  have : WithLp.toLp 2 v = 0 := by
    have h0 : (fun w => Matrix.toEuclideanLin H w - z • w) (WithLp.toLp 2 v)
        = (fun w => Matrix.toEuclideanLin H w - z • w) 0 := by simpa using hmul
    simpa using hinj h0
  exact hv (by simpa using congrArg (WithLp.ofLp) this)

open Matrix in
/-- **The entry bound**: `|((H - z)⁻¹)_{xy}| ≤ |Im z|⁻¹`, on the whole space. -/
theorem norm_inverse_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (x y : n) :
    ‖Ring.inverse (H - z • (1 : Matrix n n ℂ)) x y‖ ≤ |z.im|⁻¹ := by
  set G := Ring.inverse (H - z • (1 : Matrix n n ℂ)) with hG
  set e : n → ℂ := Pi.single y 1 with he
  have hunit := isUnit_sub_smul_of_isHermitian hH hz
  -- `u = G e` solves `(H - z) u = e`
  have hsol : (H - z • (1 : Matrix n n ℂ)) *ᵥ (G *ᵥ e) = e := by
    rw [Matrix.mulVec_mulVec, hG, Ring.mul_inverse_cancel _ hunit, Matrix.one_mulVec]
  have hEuclid : Matrix.toEuclideanLin H (WithLp.toLp 2 (G *ᵥ e)) - z • WithLp.toLp 2 (G *ᵥ e)
      = WithLp.toLp 2 e := by
    have hrw : (H - z • (1 : Matrix n n ℂ)) *ᵥ (G *ᵥ e) = H *ᵥ (G *ᵥ e) - z • (G *ᵥ e) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hrw] at hsol
    ext i
    simpa [Matrix.toLpLin_apply] using congrFun hsol i
  have hnorm := norm_le_of_sub_smul_eq (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) hz hEuclid
  have hone : ‖WithLp.toLp 2 e‖ = 1 := by
    simp [he, PiLp.norm_single]
  rw [hone, mul_one] at hnorm
  have hcoord : ‖(G *ᵥ e) x‖ ≤ ‖WithLp.toLp 2 (G *ᵥ e)‖ := by
    simpa using PiLp.norm_apply_le (WithLp.toLp 2 (G *ᵥ e)) x
  have hentry : (G *ᵥ e) x = G x y := by
    simp [he, Matrix.mulVec_single]
  rw [hentry] at hcoord
  exact le_trans hcoord hnorm

end RBM
