/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.CStarAlgebra.Hom
import RBM3D.Path.StepDecomp
import RBM3D.Path.Kernel
import RBM3D.Gauss.FlowCalculus
import RBM3D.Green.Pins

/-!
# Jets of the two-loop observable along a Hermitian line

Private helpers for the observable `Φ_a(M) = loopPM d L W E u M p q = tr (G(z) E_p G(z̄) E_q)`,
`z = zt E u`, of a two-loop label
`a = (p, q) ∈ Z_L^d × Z_L^d` (for `0 ≤ u < 1`, `|E| < 2`), on the block matrices of `Path/Walk`;
they follow RBM2D `StepDecompLoop`, on `Gauss/FlowCalculus`, `Green/Pins` and the kernel of
`Path/Kernel`.  In the vocabulary of this
development RBM2D `gloop L W (blockMat M) (spectralZ E u) (pmLoop p q)` is `loopPM d L W E u M p q`
(`= loopFine d L W M (zt E u) ![true, false] ![p, q]`), RBM2D `green H z` is `Gres H z true` (and
RBM2D `green H z̄` is `Gres H z false`), RBM2D `spectralM` is `mE`, RBM2D `BlockIndex L W` is
`Vtx d L W`.

The helpers are used through `open private` by `BA/TwistGridTail` and `Induction/LoopC2N`:

* `StepDecompLoop_word_jets` (with `StepDecompLoop_word_jet1`, `StepDecompLoop_word_jet2`): the
  first and second derivative
  of `s ↦ tr (R₁ E_p R₂ E_q)` along a line, where `R_i' = -R_i D R_i`.
* `StepDecompLoop_hasDerivAt_Gres`: the signed resolvent `Gres` along a Hermitian line has
  derivative `-G D G`.
* `StepDecompLoop_fderiv_of_line`, `StepDecompLoop_fderiv2_of_line`: the first and second Fréchet
  derivative of a function that is `C²` at Hermitian points, from its derivatives along Hermitian
  lines.
* `StepDecompLoop_gres_false`: `G(z̄) = G(z)ᴴ` for Hermitian `H`.

Along a Hermitian line `s ↦ M + s y`, `R' = -R D R`, so the first jet of `tr (R₁ E_p R₂ E_q)` is a
sum of two words and the second a sum of three words (each twice), with four resolvents, two `D`
and two `E`.  Each word has norm `≤ η⁻⁴ (W^{-d})² ‖D‖²` (`‖E_p‖ ≤ W^{-d}`,
`norm_Eblk_le_inv_W_sq`) and `|tr| ≤ N ‖·‖` with `N = (L W)^d` (`card_BlockIndex`).  Every helper is
`private` or carries the prefix `StepDecompLoop_`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Green
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-! ### 1. Block coordinates -/

section BlockCoordinates

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `blockMat` as a continuous real-linear map. -/
private def StepDecompLoop_blockCLM (d L W : ℕ) [NeZero L] [NeZero W] :
    Matrix (Idx d L W) (Idx d L W) ℂ →L[ℝ] Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockMat d L W
      map_add' := fun A C => by ext p q; simp [blockMat]
      map_smul' := fun r A => by ext p q; simp [blockMat] }

end BlockCoordinates

/-! ### 2. Jets of a word of two resolvents along a line -/

section Words

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace as a continuous real-linear map. -/
private def StepDecompLoop_trCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)

private theorem StepDecompLoop_trace_hasDerivAt {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ}
    {t : ℝ} (h : HasDerivAt P P' t) :
    HasDerivAt (fun s => Matrix.trace (P s)) (Matrix.trace P') t := by
  exact (StepDecompLoop_trCLM n).hasFDerivAt.comp_hasDerivAt t h

private theorem StepDecompLoop_word_jet1 {R₁ R₂ : ℝ → Matrix n n ℂ} {D Ep Eq : Matrix n n ℂ}
    (h₁ : ∀ t, HasDerivAt R₁ (-(R₁ t * D * R₁ t)) t)
    (h₂ : ∀ t, HasDerivAt R₂ (-(R₂ t * D * R₂ t)) t) (t : ℝ) :
    HasDerivAt (fun s => R₁ s * Ep * (R₂ s * Eq))
      (-(R₁ t * D * R₁ t) * Ep * (R₂ t * Eq) - R₁ t * Ep * (R₂ t * D * R₂ t * Eq)) t := by
  have h := ((h₁ t).mul_const Ep).mul ((h₂ t).mul_const Eq)
  refine h.congr_deriv ?_
  noncomm_ring

private theorem StepDecompLoop_word_jet2 {R₁ R₂ : ℝ → Matrix n n ℂ} {D Ep Eq : Matrix n n ℂ}
    (h₁ : ∀ t, HasDerivAt R₁ (-(R₁ t * D * R₁ t)) t)
    (h₂ : ∀ t, HasDerivAt R₂ (-(R₂ t * D * R₂ t)) t) (t : ℝ) :
    HasDerivAt
      (fun s => -(R₁ s * D * R₁ s) * Ep * (R₂ s * Eq) - R₁ s * Ep * (R₂ s * D * R₂ s * Eq))
      ((R₁ t * D * R₁ t * D * R₁ t * Ep * (R₂ t * Eq)
          + R₁ t * D * R₁ t * D * R₁ t * Ep * (R₂ t * Eq))
        + (R₁ t * D * R₁ t * Ep * (R₂ t * D * R₂ t * Eq)
          + R₁ t * D * R₁ t * Ep * (R₂ t * D * R₂ t * Eq))
        + (R₁ t * Ep * (R₂ t * D * R₂ t * D * R₂ t * Eq)
          + R₁ t * Ep * (R₂ t * D * R₂ t * D * R₂ t * Eq))) t := by
  have hQ1 := ((h₁ t).mul_const D).mul (h₁ t)
  have hQ2 := ((h₂ t).mul_const D).mul (h₂ t)
  have hA := (hQ1.neg.mul_const Ep).mul ((h₂ t).mul_const Eq)
  have hB := ((h₁ t).mul_const Ep).mul (hQ2.mul_const Eq)
  have h := hA.sub hB
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.neg_apply]
  noncomm_ring

private theorem StepDecompLoop_nmul {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a)
    (hB : ‖B‖ ≤ b) : ‖A * B‖ ≤ a * b :=
  (norm_mul_le _ _).trans (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

private theorem StepDecompLoop_nadd {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a)
    (hB : ‖B‖ ≤ b) : ‖A + B‖ ≤ a + b :=
  (norm_add_le _ _).trans (add_le_add hA hB)

/-- The first and second derivative of `s ↦ tr (R₁ E_p R₂ E_q)` along a line, where
`R_i' = -R_i D R_i` and `‖R_i‖ ≤ K`, `‖E_p‖, ‖E_q‖ ≤ e`: the second one is bounded by
`|n| · 6 K⁴ e² ‖D‖²`. -/
private theorem StepDecompLoop_word_jets {R₁ R₂ : ℝ → Matrix n n ℂ} {D Ep Eq : Matrix n n ℂ}
    (h₁ : ∀ t, HasDerivAt R₁ (-(R₁ t * D * R₁ t)) t)
    (h₂ : ∀ t, HasDerivAt R₂ (-(R₂ t * D * R₂ t)) t) {K e : ℝ}
    (hK₁ : ∀ t, ‖R₁ t‖ ≤ K) (hK₂ : ∀ t, ‖R₂ t‖ ≤ K) (hEp : ‖Ep‖ ≤ e) (hEq : ‖Eq‖ ≤ e) :
    ∃ φ₁ φ₂ : ℝ → ℂ,
      (∀ t, HasDerivAt (fun s => Matrix.trace (R₁ s * Ep * (R₂ s * Eq))) (φ₁ t) t) ∧
      (∀ t, HasDerivAt φ₁ (φ₂ t) t) ∧
      (∀ t, ‖φ₁ t‖ ≤ (Fintype.card n : ℝ) * (2 * K ^ 3 * e ^ 2 * ‖D‖)) ∧
      ∀ t, ‖φ₂ t‖ ≤ (Fintype.card n : ℝ) * (6 * K ^ 4 * e ^ 2 * ‖D‖ ^ 2) := by
  refine ⟨fun t => Matrix.trace (-(R₁ t * D * R₁ t) * Ep * (R₂ t * Eq)
      - R₁ t * Ep * (R₂ t * D * R₂ t * Eq)),
    fun t => Matrix.trace ((R₁ t * D * R₁ t * D * R₁ t * Ep * (R₂ t * Eq)
          + R₁ t * D * R₁ t * D * R₁ t * Ep * (R₂ t * Eq))
        + (R₁ t * D * R₁ t * Ep * (R₂ t * D * R₂ t * Eq)
          + R₁ t * D * R₁ t * Ep * (R₂ t * D * R₂ t * Eq))
        + (R₁ t * Ep * (R₂ t * D * R₂ t * D * R₂ t * Eq)
          + R₁ t * Ep * (R₂ t * D * R₂ t * D * R₂ t * Eq))), ?_, ?_, ?_, ?_⟩
  · intro t
    exact StepDecompLoop_trace_hasDerivAt (StepDecompLoop_word_jet1 h₁ h₂ t)
  · intro t
    exact StepDecompLoop_trace_hasDerivAt (StepDecompLoop_word_jet2 h₁ h₂ t)
  · intro t
    refine (norm_matrix_trace_le_card_mul _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hR1 := hK₁ t
    have hR2 := hK₂ t
    have hD : ‖D‖ ≤ ‖D‖ := le_rfl
    have hQ : ‖-(R₁ t * D * R₁ t)‖ ≤ K * ‖D‖ * K := by
      rw [norm_neg]
      exact StepDecompLoop_nmul (StepDecompLoop_nmul hR1 hD) hR1
    have w1 := StepDecompLoop_nmul (StepDecompLoop_nmul hQ hEp) (StepDecompLoop_nmul hR2 hEq)
    have w2 := StepDecompLoop_nmul (StepDecompLoop_nmul hR1 hEp)
      (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul hR2 hD) hR2) hEq)
    have h := (norm_sub_le _ _).trans (add_le_add w1 w2)
    refine h.trans (le_of_eq ?_)
    ring
  · intro t
    refine (norm_matrix_trace_le_card_mul _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hR1 := hK₁ t
    have hR2 := hK₂ t
    have hD : ‖D‖ ≤ ‖D‖ := le_rfl
    have w1 := StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul
      (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul hR1 hD) hR1) hD) hR1) hEp)
      (StepDecompLoop_nmul hR2 hEq)
    have w2 := StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul
      (StepDecompLoop_nmul hR1 hD) hR1) hEp)
      (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul hR2 hD) hR2) hEq)
    have w3 := StepDecompLoop_nmul (StepDecompLoop_nmul hR1 hEp)
      (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul
        (StepDecompLoop_nmul (StepDecompLoop_nmul hR2 hD) hR2) hD) hR2) hEq)
    have h := StepDecompLoop_nadd
      (StepDecompLoop_nadd (StepDecompLoop_nadd w1 w1) (StepDecompLoop_nadd w2 w2))
      (StepDecompLoop_nadd w3 w3)
    refine h.trans (le_of_eq ?_)
    ring

end Words

/-! ### 3. Lines through Hermitian points -/

section Lines

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The affine line `s ↦ M + s • A` has derivative `A` (RBM2D `hasDerivAt_line`). -/
private theorem StepDecompLoop_hasDerivAt_line (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

omit [Fintype n] [DecidableEq n] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian. -/
private theorem StepDecompLoop_isHermitian_add_realSmul {M A : Matrix n n ℂ}
    (hM : M.IsHermitian) (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

/-- The signed resolvent `Gres` along a Hermitian line has derivative `-G D G` (as RBM2D `hasDerivAt_green`). -/
private theorem StepDecompLoop_hasDerivAt_Gres {H D : Matrix n n ℂ} (hH : H.IsHermitian)
    (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Gres (H + (s : ℂ) • D) z σ)
      (-(Gres (H + (t : ℂ) • D) z σ * D * Gres (H + (t : ℂ) • D) z σ)) t := by
  have hline := StepDecompLoop_hasDerivAt_line H D t
  have hherm := StepDecompLoop_isHermitian_add_realSmul hH hD t
  cases σ with
  | true =>
    have h := hasDerivAt_green_moving (z := fun _ => z) hline (hasDerivAt_const t z) hherm hz
    simpa using h
  | false =>
    have h := hasDerivAt_green_moving (z := fun _ => (starRingEnd ℂ) z) hline
      (hasDerivAt_const t ((starRingEnd ℂ) z)) hherm (by simpa using hz)
    simpa [Gres] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `Φ` is `C²` at Hermitian points and its derivative along a Hermitian line
`s ↦ M + s y` is `φ₁`, then `fderiv ℝ Φ (M + t y) y = φ₁ t`. -/
private theorem StepDecompLoop_fderiv_of_line {Φ : Matrix ι ι ℂ → ℂ}
    (hΦ : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {M y : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) {φ₁ : ℝ → ℂ}
    (h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • y)) (φ₁ t) t) (t : ℝ) :
    φ₁ t = fderiv ℝ Φ (M + (t : ℂ) • y) y := by
  have hdiff : DifferentiableAt ℝ Φ (M + (t : ℂ) • y) :=
    ((hΦ _ (StepDecompLoop_isHermitian_add_realSmul hM hy t)).differentiableAt (by norm_num))
  have h := hdiff.hasFDerivAt.comp_hasDerivAt t (StepDecompLoop_hasDerivAt_line M y t)
  exact (h₀ t).unique h

/-- If `Φ` is `C²` at Hermitian points and its first two derivatives along a Hermitian line
`s ↦ M + s y` are `φ₁`, `φ₂`, then `fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0`. -/
private theorem StepDecompLoop_fderiv2_of_line {Φ : Matrix ι ι ℂ → ℂ}
    (hΦ : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {M y : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) {φ₁ φ₂ : ℝ → ℂ}
    (h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • y)) (φ₁ t) t)
    (h₁ : ∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) :
    fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => M + (s : ℂ) • y) y t := fun t =>
    StepDecompLoop_hasDerivAt_line M y t
  have hφ₁ := StepDecompLoop_fderiv_of_line hΦ hM hy h₀
  have hfd : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) M) M :=
    (((hΦ M hM).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hpt : M + ((0 : ℝ) : ℂ) • y = M := by simp
  have hΘ : HasFDerivAt (fun N : Matrix ι ι ℂ => fderiv ℝ Φ N y)
      ((ContinuousLinearMap.apply ℝ ℂ y).comp (fderiv ℝ (fderiv ℝ Φ) M)) M :=
    (ContinuousLinearMap.apply ℝ ℂ y).hasFDerivAt.comp M hfd
  have hev := hΘ.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hpt.symm
  have hfun : (fun t : ℝ => fderiv ℝ Φ (M + (t : ℂ) • y) y) = φ₁ := by
    funext t; exact (hφ₁ t).symm
  have hev' : HasDerivAt φ₁ (fderiv ℝ (fderiv ℝ Φ) M y y) 0 := by
    rw [← hfun]
    exact hev
  exact hev'.unique (h₁ 0)

end Lines

/-! ### 4. The adjoint of the resolvent -/

section Targets

private theorem StepDecompLoop_gres_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
  rfl

end Targets

end RBM.Path

end
