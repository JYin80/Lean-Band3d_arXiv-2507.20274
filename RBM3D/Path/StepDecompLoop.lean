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
# The two-loop family is in the Hermitian test class of `StepDecomp.lean` (`d ≥ 3`)

Ticket T2085 (ST2-24, part 2).  Port of `RBM2D/Path/StepDecompLoop.lean` at commit `c9a24cf` (cited
`SDL:<line>`) onto the merged MD layer (`RBM3D/Path/{Walk,Markov,StepDecomp}`,
`RBM3D/Loop/GLoopFlow`,
`RBM3D/Gauss/FlowCalculus`, `RBM3D/Green/Pins`) and the kernel of `RBM3D/Path/Kernel.lean`.
Renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md` and, for the merged vocabulary:
`gloop L W (blockMat M) (spectralZ E u) (pmLoop p q)` is `loopPM d L W E u M p q`
(`RBM3D/Green/Pins.lean`, `= loopFine d L W M (zt E u) ![true, false] ![p, q]`), `green H z` is
`Gres H z true` (and `green H z̄` is `Gres H z false`), `spectralM` is `mE`, `BlockIndex L W` is
`Vtx d L W`, `ukerMat (d.L n)` is `ukerMat d (sz.L n) (sz.lam n)`.

For `0 ≤ u < 1`, `|E| < 2` and a label `a = (p, q) ∈ Z_L^d × Z_L^d`, the observable
`Φ_a(M) = loopPM d L W E u M p q = tr (G(z) E_p G(z̄) E_q)`, `z = zt E u`, is a member of the
Hermitian test class `HermTestFun` of `Path/StepDecomp.lean`, is real on Hermitian matrices, and
satisfies the (H3) bound of `stepDecomp` with the explicit constant `C₂ = 6 N η_u⁻⁴`,
`N = (W L)^d`, `η_u = (1 - u) Im m`.  Then `stepDecomp` and `stepDecomp_Z_subG` are specialized to
this family with the weights `U b a = (𝒰_{v,w} (b₁,a₁) 𝒰_{v,w} (b₂,a₂)).re`, `ξ = |m|²`.

## Main results (namespace `RBM.Path`)

* `hermTestFun_loopPM` : `HermTestFun` for `Φ_a` and the (H3) bound with `C₂ = 6 N η_u⁻⁴`.
* `loopPM_real_of_herm` : `Φ_a` is real on Hermitian matrices.
* `stepDecomp_loopPM` : the decomposition `ξ_b = Z_b + Y_b` and the bounds on `Y_b`.
* `stepDecomp_Z_subG_loopPM` : the conditional sub-Gaussian bound of `Z_b`.

## `d ≥ 3` changes (CLAUDE.md §5.2)

Along a Hermitian line `s ↦ M + s y`, `R' = -R D R`, so the first jet of `tr (R₁ E_p R₂ E_q)` is a
sum of two words and the second a sum of three words (each twice), with four resolvents, two `D`
and two `E`.  Each word has norm `≤ η⁻⁴ (W^{-d})² ‖D‖²` (`‖E_p‖ ≤ W^{-d}`,
`norm_Eblk_le_inv_W_sq`) and `|tr| ≤ N ‖·‖` with `N = (L W)^d` (`card_BlockIndex`).  The constant
`C₂ = 6 N η_u⁻⁴` of the statement dominates the sharp one `6 N η_u⁻⁴ (W^{-d})²` since `W^{-d} ≤ 1`.
The sign of the weights `U b a` is not RBM2D's `ukerNonneg` of `Path/UBounds` (ST2-25, not yet
ported): the private `StepDecompLoop_ukerNonneg` proves it for `d ≥ 3` from the Neumann series
(`Theta_real_eq`, `Theta_real_nonneg`) and `ukerMat = 1 + (w - v) ξ S Θ_{wξ}`; `|m|² = 1` is
`norm_mE`.  Every helper is `private` or carries the prefix `StepDecompLoop_`.
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

/-- `blockMat` as a continuous real-linear map (`SDL:62`). -/
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
`|n| · 6 K⁴ e² ‖D‖²` (`SDL:164`). -/
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

/-- The affine line `s ↦ M + s • A` has derivative `A` (`SDL:221`, RBM2D `hasDerivAt_line`). -/
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

/-- The signed resolvent `Gres` along a Hermitian line has derivative `-G D G` (`SDL:221`,
`StepDecompLoop_hasDerivAt_green`). -/
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
`s ↦ M + s y` is `φ₁`, then `fderiv ℝ Φ (M + t y) y = φ₁ t` (`SDL:249`). -/
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
`s ↦ M + s y` are `φ₁`, `φ₂`, then `fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0` (`SDL:261`). -/
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

/-! ### 4. The observable: smoothness, bound, reality, second derivative -/

/-! ### 5. Signs of the weights -/

/-! ### 6. The four targets -/

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

/-! ### 7. Compile checks on a private size sequence at `d = 3`

`L n = n + 3`, `W n = n + 2`, `lam n = 1/2`: at `n = 0` this is `d = 3`, `L = 3`, `W = 2`,
`N = (W L)^3 = 216`, matrices of size `216 × 216` (`216` fine points, `27` blocks of `8`), `E = 0`
(`Im m = 1`), `u = 1/2` (`η = 1/2`), `v = 1/4`, `w = 1/2` (`ξ = |m|² = 1`), grid `s = 1/4`,
`t = 3/4`, `K = 2` (`Δ = 1/4`), `j = 0`.  The event of `stepDecomp_Z_subG_loopPM` is the whole
space, with a finite variance proxy `c` that does not depend on the sample: the first-derivative
bound of the two-loop family bounds `linTr n (Ab ω)` on the finitely many coordinate matrices. -/

end RBM.Path

end
