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

private theorem StepDecompLoop_blockMat_add_smul (A C : Matrix (Idx d L W) (Idx d L W) ℂ)
    (y : ℂ) : blockMat d L W (A + y • C) = blockMat d L W A + y • blockMat d L W C := by
  ext p q
  simp [blockMat]

/-- `blockMat` as a continuous real-linear map (`SDL:62`). -/
private def StepDecompLoop_blockCLM (d L W : ℕ) [NeZero L] [NeZero W] :
    Matrix (Idx d L W) (Idx d L W) ℂ →L[ℝ] Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockMat d L W
      map_add' := fun A C => by ext p q; simp [blockMat]
      map_smul' := fun r A => by ext p q; simp [blockMat] }

private theorem StepDecompLoop_blockCLM_apply (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    StepDecompLoop_blockCLM d L W A = blockMat d L W A := rfl

/-- Reindexing by an equivalence is a star algebra homomorphism of matrix algebras (`SDL:77`). -/
private def StepDecompLoop_reindexHom {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] (e : k ≃ m) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix k k ℂ where
  toFun A := A.submatrix e e
  map_smul' c A := rfl
  map_zero' := rfl
  map_add' A B := rfl
  map_mul' A B := by
    exact (Matrix.submatrix_mul_equiv A B e e e).symm
  map_star' A := by
    exact (Matrix.conjTranspose_submatrix A e e).symm

/-- `blockMat` preserves the operator norm (`SDL:90`). -/
private theorem StepDecompLoop_norm_blockMat (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ‖blockMat d L W A‖ = ‖A‖ := by
  have hinj : Function.Injective (StepDecompLoop_reindexHom (splitEquiv d L W).symm) := by
    intro A B h
    ext i j
    have := congrFun (congrFun h ((splitEquiv d L W) i)) ((splitEquiv d L W) j)
    change A ((splitEquiv d L W).symm ((splitEquiv d L W) i))
      ((splitEquiv d L W).symm ((splitEquiv d L W) j)) =
        B ((splitEquiv d L W).symm ((splitEquiv d L W) i))
          ((splitEquiv d L W).symm ((splitEquiv d L W) j)) at this
    simpa using this
  exact NonUnitalStarAlgHom.norm_map _ hinj A

private theorem StepDecompLoop_isHermitian_blockMat {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) : (blockMat d L W A).IsHermitian :=
  hA.submatrix _

/-- The two-loop observable of a block matrix `H` (`SDL:111`, `gloop_two`): the trace of a word of
two resolvents and two block insertions.  The observable of `stepDecomp_loopPM` is
`loopPM d L W E u M p q = StepDecompLoop_obs d L W (zt E u) p q M`. -/
private def StepDecompLoop_obs (d L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (p q : Zd d L)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  Matrix.trace (Gres (blockMat d L W M) z true * Eblk d L W p *
    (Gres (blockMat d L W M) z false * Eblk d L W q))

private theorem StepDecompLoop_loopPM_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (p q : Zd d L) : loopPM d L W E u M p q = StepDecompLoop_obs d L W (zt E u) p q M := by
  simp [loopPM, loopFine, loopM, StepDecompLoop_obs, Matrix.mul_assoc]

end BlockCoordinates

/-! ### 2. Jets of a word of two resolvents along a line -/

section Words

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace as a continuous real-linear map. -/
private def StepDecompLoop_trCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)

private theorem StepDecompLoop_trCLM_apply (A : Matrix n n ℂ) :
    StepDecompLoop_trCLM n A = Matrix.trace A := rfl

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

section Observable

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent of `blockMat M` is `C²` at every `M` for which `blockMat M - w` is invertible
(`SDL:295`). -/
private theorem StepDecompLoop_contDiffAt_Gres {w : ℂ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hu : IsUnit (blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M') w true)
      M := by
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      blockMat d L W M' - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    ((StepDecompLoop_blockCLM d L W).contDiff).sub contDiff_const
  have hinv : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix (Vtx d L W) (Vtx d L W) ℂ))
      (blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    exact contDiffAt_ringInverse ℝ u
  have h := hinv.comp M hA.contDiffAt
  have hfun : (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M') w true)
      = Ring.inverse ∘ (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
        blockMat d L W M' - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by
    funext M'
    simp [Gres]
  rw [hfun]
  exact h

/-- (H1) for the two-loop observable: `C²` at every Hermitian point (`SDL:317`). -/
private theorem StepDecompLoop_contDiffAt_obs {z : ℂ} (hz : z.im ≠ 0) (p q : Zd d L)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      StepDecompLoop_obs d L W z p q M') M := by
  have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
  have hMb : (blockMat d L W M).IsHermitian := StepDecompLoop_isHermitian_blockMat hM
  have hG₁ := StepDecompLoop_contDiffAt_Gres (d := d) (L := L) (W := W)
    (isUnit_sub_smul_of_isHermitian hMb hz)
  have hG₂ := StepDecompLoop_contDiffAt_Gres (d := d) (L := L) (W := W)
    (isUnit_sub_smul_of_isHermitian hMb hz')
  have hEp : ContDiffAt ℝ 2 (fun _ : Matrix (Idx d L W) (Idx d L W) ℂ => Eblk d L W p) M :=
    contDiffAt_const
  have hEq : ContDiffAt ℝ 2 (fun _ : Matrix (Idx d L W) (Idx d L W) ℂ => Eblk d L W q) M :=
    contDiffAt_const
  have hprod := (hG₁.mul hEp).mul (hG₂.mul hEq)
  have h := (StepDecompLoop_trCLM (Vtx d L W)).contDiff.contDiffAt.comp M hprod
  have hfun : (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => StepDecompLoop_obs d L W z p q M')
      = (StepDecompLoop_trCLM (Vtx d L W)) ∘ (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
        Gres (blockMat d L W M') z true * Eblk d L W p *
          (Gres (blockMat d L W M') ((starRingEnd ℂ) z) true * Eblk d L W q)) := by
    funext M'
    simp [StepDecompLoop_obs, Gres, StepDecompLoop_trCLM_apply]
  rw [hfun]
  exact h

/-- The first two derivatives of the two-loop observable along a Hermitian line, with their
bounds `|φ₁| ≤ N · 2 η⁻³ (W^{-d})² ‖y‖` and `|φ₂| ≤ N · 6 η⁻⁴ (W^{-d})² ‖y‖²`, `N = (L W)^d`
(`SDL:340`). -/
private theorem StepDecompLoop_line_jets {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (p q : Zd d L) {M y : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ∃ φ₁ φ₂ : ℝ → ℂ,
      (∀ t : ℝ, HasDerivAt (fun s : ℝ =>
        StepDecompLoop_obs d L W z p q (M + (s : ℂ) • y)) (φ₁ t) t) ∧
      (∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) ∧
      (∀ t : ℝ, ‖φ₁ t‖ ≤ (((L * W) ^ d : ℕ) : ℝ) *
        (2 * η⁻¹ ^ 3 * (((W : ℝ) ^ d)⁻¹) ^ 2 * ‖y‖)) ∧
      (∀ t : ℝ, ‖φ₂ t‖ ≤
        (((L * W) ^ d : ℕ) : ℝ) * (6 * η⁻¹ ^ 4 * (((W : ℝ) ^ d)⁻¹) ^ 2 * ‖y‖ ^ 2)) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hMb : (blockMat d L W M).IsHermitian := StepDecompLoop_isHermitian_blockMat hM
  have hyb : (blockMat d L W y).IsHermitian := StepDecompLoop_isHermitian_blockMat hy
  obtain ⟨φ₁, φ₂, hd1, hd2, hb1, hb2⟩ := StepDecompLoop_word_jets
    (R₁ := fun s : ℝ => Gres (blockMat d L W M + (s : ℂ) • blockMat d L W y) z true)
    (R₂ := fun s : ℝ => Gres (blockMat d L W M + (s : ℂ) • blockMat d L W y) z false)
    (D := blockMat d L W y) (Ep := Eblk d L W p) (Eq := Eblk d L W q) (K := η⁻¹)
    (e := ((W : ℝ) ^ d)⁻¹)
    (StepDecompLoop_hasDerivAt_Gres hMb hyb hz0 true)
    (StepDecompLoop_hasDerivAt_Gres hMb hyb hz0 false)
    (fun t => norm_Gsig_le_inv_eta (StepDecompLoop_isHermitian_add_realSmul hMb hyb t) hη hz true)
    (fun t => norm_Gsig_le_inv_eta (StepDecompLoop_isHermitian_add_realSmul hMb hyb t) hη hz false)
    (norm_Eblk_le_inv_W_sq d L W p) (norm_Eblk_le_inv_W_sq d L W q)
  have hDn : ‖blockMat d L W y‖ ≤ ‖y‖ := le_of_eq (StepDecompLoop_norm_blockMat y)
  have hD2 : ‖blockMat d L W y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [StepDecompLoop_norm_blockMat]
  refine ⟨φ₁, φ₂, ?_, hd2, ?_, ?_⟩
  · intro t
    have hfun : (fun s : ℝ => StepDecompLoop_obs d L W z p q (M + (s : ℂ) • y))
        = fun s : ℝ => Matrix.trace
          (Gres (blockMat d L W M + (s : ℂ) • blockMat d L W y) z true * Eblk d L W p
            * (Gres (blockMat d L W M + (s : ℂ) • blockMat d L W y) z false
              * Eblk d L W q)) := by
      funext s
      simp only [StepDecompLoop_obs, StepDecompLoop_blockMat_add_smul]
    rw [hfun]
    exact hd1 t
  · intro t
    rw [card_BlockIndex] at hb1
    refine (hb1 t).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hK : (0 : ℝ) ≤ 2 * η⁻¹ ^ 3 * (((W : ℝ) ^ d)⁻¹) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hDn hK
  · intro t
    rw [card_BlockIndex] at hb2
    refine (hb2 t).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hK : (0 : ℝ) ≤ 6 * η⁻¹ ^ 4 * (((W : ℝ) ^ d)⁻¹) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hD2 hK

/-- (H3), before the constant is simplified: the second derivative along a Hermitian line
(`SDL:394`). -/
private theorem StepDecompLoop_second_deriv_bound {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (p q : Zd d L) {M y : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ‖fderiv ℝ (fderiv ℝ
        (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => StepDecompLoop_obs d L W z p q M')) M y y‖
      ≤ (((L * W) ^ d : ℕ) : ℝ) * (6 * η⁻¹ ^ 4 * (((W : ℝ) ^ d)⁻¹) ^ 2 * ‖y‖ ^ 2) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  obtain ⟨φ₁, φ₂, h₀, hd2, -, hb⟩ := StepDecompLoop_line_jets (d := d) (L := L) (W := W)
    hη hz p q hM hy
  rw [StepDecompLoop_fderiv2_of_line
    (fun M' hM' => StepDecompLoop_contDiffAt_obs (d := d) (L := L) (W := W) hz0 p q hM') hM hy
    h₀ hd2]
  exact hb 0

/-- The first derivative of the two-loop observable in a Hermitian direction (`SDL:410`). -/
private theorem StepDecompLoop_first_deriv_bound {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (p q : Zd d L) {M X : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (hX : X.IsHermitian) :
    ‖fderiv ℝ (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
        StepDecompLoop_obs d L W z p q M') M X‖
      ≤ (((L * W) ^ d : ℕ) : ℝ) * (2 * η⁻¹ ^ 3 * (((W : ℝ) ^ d)⁻¹) ^ 2 * ‖X‖) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  obtain ⟨φ₁, φ₂, h₀, -, hb, -⟩ := StepDecompLoop_line_jets (d := d) (L := L) (W := W)
    hη hz p q hM hX
  have h := StepDecompLoop_fderiv_of_line
    (fun M' hM' => StepDecompLoop_contDiffAt_obs (d := d) (L := L) (W := W) hz0 p q hM') hM hX
    h₀ 0
  have hpt : M + ((0 : ℝ) : ℂ) • X = M := by simp
  rw [hpt] at h
  rw [← h]
  exact hb 0

end Observable

/-! ### 5. Signs of the weights -/

section Weights

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `z` is a nonnegative real number, viewed inside `ℂ` (bookkeeping for the sign arguments; the
method of RBM2D `RealNonneg`, `Path/UBounds.lean:105`, and RBM1D `IsRealNonneg`,
`Gauss/GridQVConv.lean:38`). -/
private def StepDecompLoop_RealNonneg (z : ℂ) : Prop := ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)

private theorem StepDecompLoop_RN_zero : StepDecompLoop_RealNonneg 0 := ⟨0, le_refl _, by simp⟩

private theorem StepDecompLoop_RN_one : StepDecompLoop_RealNonneg 1 := ⟨1, zero_le_one, by simp⟩

private theorem StepDecompLoop_RN_add {z w : ℂ} (hz : StepDecompLoop_RealNonneg z)
    (hw : StepDecompLoop_RealNonneg w) : StepDecompLoop_RealNonneg (z + w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 + r2, by positivity, by rw [e1, e2]; push_cast; ring⟩

private theorem StepDecompLoop_RN_mul {z w : ℂ} (hz : StepDecompLoop_RealNonneg z)
    (hw : StepDecompLoop_RealNonneg w) : StepDecompLoop_RealNonneg (z * w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 * r2, mul_nonneg hr1 hr2, by rw [e1, e2]; push_cast; ring⟩

private theorem StepDecompLoop_RN_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, StepDecompLoop_RealNonneg (f i)) : StepDecompLoop_RealNonneg (∑ i ∈ s, f i) :=
  Finset.sum_induction f StepDecompLoop_RealNonneg (fun _ _ ha hb => StepDecompLoop_RN_add ha hb)
    StepDecompLoop_RN_zero h

private theorem StepDecompLoop_SB_RN (a b : Zd d L) :
    StepDecompLoop_RealNonneg (SB d L g a b) := by
  rw [SB_apply, sbKernel_eq_ofReal]
  exact ⟨_, sbKernelR_nonneg d L g _, rfl⟩

private theorem StepDecompLoop_Theta_RN (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) : StepDecompLoop_RealNonneg (Theta d L g (t : ℂ) a b) :=
  ⟨(Theta d L g (t : ℂ) a b).re, Theta_real_nonneg hL ht0 ht1 a b,
    Theta_real_eq hL ht0 ht1 a b⟩

/-- The exact form `𝒰`-kernel `= 1 + (w - v) · (ξ S Θ_{wξ})`, from `(1 - wξS) Θ_{wξ} = 1`
(RBM2D `ukerMat_eq`, `Path/UBounds.lean:238`). -/
private theorem StepDecompLoop_ukerMat_eq (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ}
    (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat d L g ξ v w
      = 1 + ((w : ℂ) - (v : ℂ)) • (ξ • (SB d L g * Theta d L g ((w : ℂ) * ξ))) := by
  have h := mul_Theta_of_three_le (d := d) (L := L) (g := g) hL hw
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  unfold ukerMat
  rw [sub_mul, one_mul, smul_mul_assoc, smul_smul, ← h]
  module

/-- **Sign of the kernel** (RBM2D `ukerNonneg`, `Path/UBounds.lean:424`, with the same method): for
real `ξ ≥ 0`, `0 ≤ v ≤ w`, `wξ < 1`, `ukerMat` is entrywise a nonnegative real. -/
private theorem StepDecompLoop_ukerNonneg (hL : 3 ≤ L) {ξ v w : ℝ} (hξ : 0 ≤ ξ) (hv : 0 ≤ v)
    (hvw : v ≤ w) (hwξ : w * ξ < 1) (a b : Zd d L) :
    (ukerMat d L g (ξ : ℂ) v w a b).im = 0 ∧ 0 ≤ (ukerMat d L g (ξ : ℂ) v w a b).re := by
  have hw0 : 0 ≤ w := hv.trans hvw
  have hwξ0 : 0 ≤ w * ξ := mul_nonneg hw0 hξ
  have hnorm : ‖(w : ℂ) * (ξ : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hwξ0]; exact hwξ
  have hz : ((w : ℂ) * (ξ : ℂ)) = ((w * ξ : ℝ) : ℂ) := by push_cast; ring
  have h1 : StepDecompLoop_RealNonneg ((1 : Matrix (Zd d L) (Zd d L) ℂ) a b) := by
    rw [Matrix.one_apply]
    split_ifs
    · exact StepDecompLoop_RN_one
    · exact StepDecompLoop_RN_zero
  have hc : StepDecompLoop_RealNonneg ((w : ℂ) - (v : ℂ)) :=
    ⟨w - v, by linarith, by push_cast; ring⟩
  have hξc : StepDecompLoop_RealNonneg (ξ : ℂ) := ⟨ξ, hξ, rfl⟩
  have hgen : StepDecompLoop_RealNonneg
      (((ξ : ℂ) • (SB d L g * Theta d L g ((w : ℂ) * (ξ : ℂ)))) a b) := by
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine StepDecompLoop_RN_mul hξc (StepDecompLoop_RN_sum _ _ fun c _ => ?_)
    rw [hz]
    exact StepDecompLoop_RN_mul (StepDecompLoop_SB_RN a c)
      (StepDecompLoop_Theta_RN hL hwξ0 hwξ c b)
  rw [StepDecompLoop_ukerMat_eq hL hnorm]
  have hres := StepDecompLoop_RN_add h1 (StepDecompLoop_RN_mul hc hgen)
  obtain ⟨r, hr, hreq⟩ := hres
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hreq ⊢
  rw [hreq]
  simpa using hr

end Weights

section WeightsModel

variable {d : ℕ}

/-- The weights `U b a = (𝒰_{v,w} (b₁,a₁) 𝒰_{v,w} (b₂,a₂)).re`, `ξ = |m|²`, are nonnegative
(`SDL:468`; `|m|² = 1` is `norm_mE`). -/
private theorem StepDecompLoop_weight_nonneg (sz : Sizes d) (n : ℕ) (E : ℝ) (hE : |E| < 2)
    (v w : ℝ) (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1) (b a : Zd d (sz.L n) × Zd d (sz.L n)) :
    0 ≤ (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
        * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re := by
  have hξ : Complex.normSq (mE E) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_mE hE.le]
    norm_num
  have h1 := StepDecompLoop_ukerNonneg (g := sz.lam n) (sz.three_le_L n)
    (Complex.normSq_nonneg (mE E)) hv hvw (by rw [hξ]; linarith) b.1 a.1
  have h2 := StepDecompLoop_ukerNonneg (g := sz.lam n) (sz.three_le_L n)
    (Complex.normSq_nonneg (mE E)) hv hvw (by rw [hξ]; linarith) b.2 a.2
  rw [Complex.mul_re, h1.1, h2.1]
  nlinarith [h1.2, h2.2]

end WeightsModel

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

/-- **The two-loop family is in the Hermitian test class, with `C₂ = 6 N η_u⁻⁴`** (`SDL:432`).  For
`0 ≤ u < 1`, `|E| < 2` and a label `a = (p, q)`, `M ↦ loopPM d L W E u M p q` satisfies
`HermTestFun` (`C²` and bounded at Hermitian points) and the (H3) bound of `stepDecomp` (`hC₂`)
with `C₂ = 6 N η_u⁻⁴`, `N = (W L)^d`, `η_u = (1 - u) Im m`.  (`HermTestFun` has no `C₂` field.  The
proof gives the sharper constant `6 N η_u⁻⁴ (W^{-d})²`.) -/
theorem hermTestFun_loopPM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hE : |E| < 2) (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    HermTestFun sz n
        (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
      ∧ ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
          M.IsHermitian → y.IsHermitian →
          ‖fderiv ℝ (fderiv ℝ
              (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
                loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)) M y y‖
            ≤ 6 * (sz.size n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2 := by
  have _ := hu0
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hpos : 0 < (1 - u) * (mE E).im := mul_pos (by linarith) (mE_im_pos hE)
  have hz : etaT E u ≤ |(zt E u).im| := by
    rw [zt_im, abs_of_pos hpos]
    exact le_of_eq rfl
  have hz0 : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact hpos.ne'
  have hfun : (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
      = StepDecompLoop_obs d (sz.L n) (sz.W n) (zt E u) a.1 a.2 :=
    funext fun M => StepDecompLoop_loopPM_eq E u M a.1 a.2
  rw [hfun]
  refine ⟨⟨fun M hM => StepDecompLoop_contDiffAt_obs hz0 a.1 a.2 hM, ?_⟩, ?_⟩
  · refine ⟨(Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) *
      ((etaT E u)⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹ * ((etaT E u)⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹)), fun M hM => ?_⟩
    have hMb := StepDecompLoop_isHermitian_blockMat hM
    refine (norm_matrix_trace_le_card_mul _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact StepDecompLoop_nmul
      (StepDecompLoop_nmul (norm_Gsig_le_inv_eta hMb hη hz true)
        (norm_Eblk_le_inv_W_sq d (sz.L n) (sz.W n) a.1))
      (StepDecompLoop_nmul (norm_Gsig_le_inv_eta hMb hη hz false)
        (norm_Eblk_le_inv_W_sq d (sz.L n) (sz.W n) a.2))
  intro M y hM hy
  have h := StepDecompLoop_second_deriv_bound (d := d) (L := sz.L n) (W := sz.W n) hη hz a.1 a.2
    hM hy
  refine h.trans ?_
  have hN : (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) = (sz.size n : ℝ) := by
    rw [Sizes.size, mul_comm]
  rw [hN]
  have hW : (((sz.W n : ℝ) ^ d)⁻¹) ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (sz.W n : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
    have h2 : (1 : ℝ) ≤ (sz.W n : ℝ) ^ d := one_le_pow₀ h1
    have h3 : ((sz.W n : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
    have h4 : (0 : ℝ) ≤ ((sz.W n : ℝ) ^ d)⁻¹ := by positivity
    exact pow_le_one₀ h4 h3
  have hNn : (0 : ℝ) ≤ (sz.size n : ℝ) := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ (etaT E u)⁻¹ ^ 4 := by positivity
  calc (sz.size n : ℝ) * (6 * (etaT E u)⁻¹ ^ 4 * (((sz.W n : ℝ) ^ d)⁻¹) ^ 2 * ‖y‖ ^ 2)
      = (6 * (sz.size n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2) * (((sz.W n : ℝ) ^ d)⁻¹) ^ 2 := by
        ring
    _ ≤ (6 * (sz.size n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = 6 * (sz.size n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2 := mul_one _

/-- **`hReal` for the two-loop family** (`SDL:462`).  The `(+,-)` two-loop `tr (G E_p Ḡ E_q)` of a
Hermitian matrix is real, with no hypothesis on `E` or `u`.  Proof: with `Ḡ = Gᴴ` and
`E_p`, `E_q` Hermitian, `star tr (G E_p Gᴴ E_q) = tr (E_q G E_p Gᴴ) = tr (G E_p Gᴴ E_q)` by
cyclicity (RBM2D uses `gloop_two_plus_minus_nonneg`, which RBM3D does not have). -/
theorem loopPM_real_of_herm {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (a : Zd d (sz.L n) × Zd d (sz.L n))
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    (loopPM d (sz.L n) (sz.W n) E u M a.1 a.2).im = 0 := by
  rw [StepDecompLoop_loopPM_eq]
  have hHb := StepDecompLoop_isHermitian_blockMat hM
  unfold StepDecompLoop_obs
  rw [StepDecompLoop_gres_false _ hHb]
  set G := Gres (blockMat d (sz.L n) (sz.W n) M) (zt E u) true with hG
  set Ep := Eblk d (sz.L n) (sz.W n) a.1 with hEp
  set Eq := Eblk d (sz.L n) (sz.W n) a.2 with hEq
  have hEpH : Epᴴ = Ep := (Eblk_isHermitian a.1).eq
  have hEqH : Eqᴴ = Eq := (Eblk_isHermitian a.2).eq
  have h : star (Matrix.trace (G * Ep * (Gᴴ * Eq))) = Matrix.trace (G * Ep * (Gᴴ * Eq)) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hEpH, hEqH]
    calc Matrix.trace (Eq * G * (Ep * Gᴴ))
        = Matrix.trace (Eq * (G * Ep * Gᴴ)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((G * Ep * Gᴴ) * Eq) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (G * Ep * (Gᴴ * Eq)) := by simp only [Matrix.mul_assoc]
  exact Complex.conj_eq_iff_im.mp h

/-- **`stepDecomp` and `stepDecomp_Y_sq` for the two-loop family.**  With `Φ_a` the two-loop
observable, `C₂ = 6 N η_u⁻⁴` and the weights `U b a = (𝒰_{v,w} 𝒰_{v,w}).re`, `ξ = |m|²`: the
decomposition `ξ_b = Z_b + Y_b`, the measurability of `Ab`, the pathwise bound and the vanishing
conditional mean of `Y_b`, and the `L²` bound of `Y_b`.  The signs `0 ≤ v ≤ w < 1` of the
propagator times are what `ukerNonneg` needs to replace `∑ |U b a|` by `∑ U b a` (candidate
`T2085f`); the fifth conjunct is `stepDecomp_Y_sq` (candidate `T2085f`). -/
theorem stepDecomp_loopPM {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (E u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| < 2) (v w : ℝ) (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1)
    (hΔ : 0 ≤ gridStep s t K n) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    (∀ ω, stepXi sz s t K n j
          (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
              (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
            loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
          (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω
        = (stepZ sz s t K n j
            (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
                (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
              loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re)
            b ω : ℂ)
          + stepY sz s t K n j
            (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
                (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
              loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re)
            b ω)
      ∧ Measurable[filt sz j] (fun ω => Ab sz s t K n j
          (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
              (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
            loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
          (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω)
      ∧ (∀ᵐ ω ∂(pathP sz), ‖stepY sz s t K n j
            (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
                (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
              loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω‖
          ≤ (∑ a : Zd d (sz.L n) × Zd d (sz.L n),
                (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
                  * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re)
              * ((6 * (sz.size n : ℝ) * (etaT E u)⁻¹ ^ 4 / 2) * gridStep s t K n)
              * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2
            + (pathP sz)[fun ω' => (∑ a : Zd d (sz.L n) × Zd d (sz.L n),
                (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
                  * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re)
                * ((6 * (sz.size n : ℝ) * (etaT E u)⁻¹ ^ 4 / 2) * gridStep s t K n)
                * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω)
      ∧ ((pathP sz)[stepY sz s t K n j
            (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
                (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
              loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b
          | filt sz j] =ᵐ[pathP sz] (fun _ => (0 : ℂ)))
      ∧ ∫ ω, ‖stepY sz s t K n j
            (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
                (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
              loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω‖ ^ 2
            ∂(pathP sz)
          ≤ 4 * ((∑ a : Zd d (sz.L n) × Zd d (sz.L n),
                (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
                  * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re)
              * (6 * (sz.size n : ℝ) * (etaT E u)⁻¹ ^ 4 / 2)) ^ 2
            * (gridStep s t K n) ^ 2 * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) := by
  have hΦ := fun a => (hermTestFun_loopPM sz n E u hu0 hu1 hE a).1
  have hC := fun a => (hermTestFun_loopPM sz n E u hu0 hu1 hE a).2
  have hReal : ∀ (a : Zd d (sz.L n) × Zd d (sz.L n))
      (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), A.IsHermitian →
      ((fun (a : Zd d (sz.L n) × Zd d (sz.L n))
          (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
        loopPM d (sz.L n) (sz.W n) E u M a.1 a.2) a A).im = 0 :=
    fun a A hA => loopPM_real_of_herm sz n E u a hA
  have hIntReal := stepDecomp_integrable_stepZ sz s t K n j hΦ hReal hC hΔ
    (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b
  obtain ⟨h1, h2, h3, h4⟩ := stepDecomp sz s t K n j hΦ hReal hC hΔ
    (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b hIntReal
  have h5 := stepDecomp_Y_sq sz s t K n j hΦ hReal hC hΔ
    (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b hIntReal
  have hsum : (∑ a : Zd d (sz.L n) × Zd d (sz.L n),
      |(ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
        * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re|)
      = ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
        (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
          * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re :=
    Finset.sum_congr rfl fun a _ =>
      abs_of_nonneg (StepDecompLoop_weight_nonneg sz n E hE v w hv hvw hw b a)
  simp only [hsum] at h3 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **`stepDecomp_Z_subG` for the two-loop family**: for `S ∈ F_j` on which
`Δ · linTrVar n (Ab ω) ≤ c`, the indicator of `S` times `Z_b` is conditionally sub-Gaussian with
variance proxy `c`.  `v`, `w` are unconstrained: `stepDecomp_Z_subG` uses no property of the
weights. -/
theorem stepDecomp_Z_subG_loopPM {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (E u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| < 2) (v w : ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (S : Set (PathΩ sz)) (hS : MeasurableSet[filt sz j] S) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ ω ∈ S, gridStep s t K n * linTrVar n (Ab sz s t K n j
          (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
              (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
            loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
          (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω) ≤ c) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
      (fun ω => S.indicator (fun ω => stepZ sz s t K n j
          (fun (a : Zd d (sz.L n) × Zd d (sz.L n))
              (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
            loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
          (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω) ω)
      ⟨c, hc⟩ (pathP sz) :=
  stepDecomp_Z_subG sz s t K n j (fun a => (hermTestFun_loopPM sz n E u hu0 hu1 hE a).1)
    (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b S hS c hc hbound


end Targets

/-! ### 7. Compile checks on a private size sequence at `d = 3`

`L n = n + 3`, `W n = n + 2`, `lam n = 1/2`: at `n = 0` this is `d = 3`, `L = 3`, `W = 2`,
`N = (W L)^3 = 216`, matrices of size `216 × 216` (`216` fine points, `27` blocks of `8`), `E = 0`
(`Im m = 1`), `u = 1/2` (`η = 1/2`), `v = 1/4`, `w = 1/2` (`ξ = |m|² = 1`), grid `s = 1/4`,
`t = 3/4`, `K = 2` (`Δ = 1/4`), `j = 0`.  The event of `stepDecomp_Z_subG_loopPM` is the whole
space, with a finite variance proxy `c` that does not depend on the sample: the first-derivative
bound of the two-loop family bounds `linTr n (Ab ω)` on the finitely many coordinate matrices. -/

section Check

/-- A private size sequence at `d = 3` with `L n = n + 3`, `W n = n + 2`, `lam n = 1/2`. -/
private def StepDecompLoop_sizes : Sizes 3 where
  L := fun n => n + 3
  W := fun n => n + 2
  lam := fun _ => 1 / 2
  three_le_L := fun n => by omega
  W_pos := fun n => by omega

/-- The two-loop family, as in the statements of `stepDecomp_loopPM`. -/
private def StepDecompLoop_Phi {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) :
    Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
      ℂ :=
  fun a M => loopPM d (sz.L n) (sz.W n) E u M a.1 a.2

/-- The weights, as in the statements of `stepDecomp_loopPM`. -/
private def StepDecompLoop_Uw {d : ℕ} (sz : Sizes d) (n : ℕ) (E v w : ℝ) :
    Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ :=
  fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
    * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re

private theorem StepDecompLoop_linTr_sum {d : ℕ} (sz : Sizes d) (n : ℕ) {ι : Type*}
    (S : Finset ι) (u : ι → ℝ)
    (B : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr (sz := sz) n (∑ i ∈ S, (u i : ℂ) • B i) X = ∑ i ∈ S, u i * linTr (sz := sz) n (B i) X := by
  simp only [linTr, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

private theorem StepDecompLoop_linTrVar_eq_sum {d : ℕ} (sz : Sizes d) (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTrVar (sz := sz) n A = ∑ c ∈ coordFinset (sz := sz) n,
      (linTr (sz := sz) n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 * (Sizes.seqGvar sz c : ℝ) := by
  unfold linTrVar RBM.Gauss.LinearForm.linVar
  push_cast [NNReal.coe_mk]
  rfl

/-- **A global variance proxy.**  For every sample, `Δ · linTrVar n (Ab ω) ≤ c`, with a finite `c`
independent of `ω`: `|linTr n (Ab ω) X| ≤ (∑_a |U b a|) N · 2 η⁻³ (W^{-d})² ‖X‖` for Hermitian `X`
(the first-derivative bound), applied to the coordinate matrices. -/
private theorem StepDecompLoop_exists_variance_bound {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ)
    (K : ℕ → ℕ) (n j : ℕ) (E u : ℝ) (hu1 : u < 1) (hE : |E| < 2) (v w : ℝ)
    (hΔ : 0 ≤ gridStep s t K n) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ω : PathΩ sz, gridStep s t K n *
      linTrVar (sz := sz) n (Ab sz s t K n j (StepDecompLoop_Phi sz n E u)
        (StepDecompLoop_Uw sz n E v w) b ω) ≤ c := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hpos : 0 < (1 - u) * (mE E).im := mul_pos (by linarith) (mE_im_pos hE)
  have hz : etaT E u ≤ |(zt E u).im| := by
    rw [zt_im, abs_of_pos hpos]
    exact le_of_eq rfl
  set Cd : ℝ := (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |StepDecompLoop_Uw sz n E v w b a|)
    * ((((sz.L n * sz.W n) ^ d : ℕ) : ℝ) *
      (2 * (etaT E u)⁻¹ ^ 3 * (((sz.W n : ℝ) ^ d)⁻¹) ^ 2)) with hCd
  have hlin : ∀ (ω : PathΩ sz)
      (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), X.IsHermitian →
      |linTr (sz := sz) n (Ab sz s t K n j (StepDecompLoop_Phi sz n E u)
        (StepDecompLoop_Uw sz n E v w) b ω) X| ≤ Cd * ‖X‖ := by
    intro ω X hX
    unfold Ab
    rw [StepDecompLoop_linTr_sum]
    calc |∑ a : Zd d (sz.L n) × Zd d (sz.L n), StepDecompLoop_Uw sz n E v w b a
            * linTr (sz := sz) n (gradMat (StepDecompLoop_Phi sz n E u a) (pathH sz s t K n j ω)) X|
        ≤ ∑ a : Zd d (sz.L n) × Zd d (sz.L n), |StepDecompLoop_Uw sz n E v w b a
            * linTr (sz := sz) n (gradMat (StepDecompLoop_Phi sz n E u a)
              (pathH sz s t K n j ω)) X| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Zd d (sz.L n) × Zd d (sz.L n), |StepDecompLoop_Uw sz n E v w b a|
            * ((((sz.L n * sz.W n) ^ d : ℕ) : ℝ)
              * (2 * (etaT E u)⁻¹ ^ 3 * (((sz.W n : ℝ) ^ d)⁻¹) ^ 2 * ‖X‖)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [← lin_eq_fderiv sz n _ hX]
          refine (Complex.abs_re_le_norm _).trans ?_
          have hfun : StepDecompLoop_Phi sz n E u a
              = StepDecompLoop_obs d (sz.L n) (sz.W n) (zt E u) a.1 a.2 :=
            funext fun M => StepDecompLoop_loopPM_eq E u M a.1 a.2
          rw [hfun]
          exact StepDecompLoop_first_deriv_bound (d := d) (L := sz.L n) (W := sz.W n) hη hz a.1 a.2
            (pathH_isHermitian sz s t K n j ω) hX
      _ = Cd * ‖X‖ := by
          rw [← Finset.sum_mul, hCd]
          ring
  refine ⟨gridStep s t K n * ∑ c ∈ coordFinset (sz := sz) n,
    (Cd * ‖Sizes.seqXmat sz n (Pi.single c 1)‖) ^ 2 * (Sizes.seqGvar sz c : ℝ),
    mul_nonneg hΔ (Finset.sum_nonneg fun c _ => mul_nonneg (sq_nonneg _) (NNReal.coe_nonneg _)),
    fun ω => ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hΔ
  rw [StepDecompLoop_linTrVar_eq_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (NNReal.coe_nonneg _)
  have h := hlin ω (Sizes.seqXmat sz n (Pi.single c 1)) (Sizes.seqXmat_isHermitian sz n _)
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rwa [sq_abs] at h2

/-- **`hermTestFun_loopPM` at the concrete instance** `d = 3`, `L = 3`, `W = 2`, `E = 0`,
`u = 1/2`, label `(0, 0)`: the observable is in the class and satisfies (H3). -/
example := hermTestFun_loopPM StepDecompLoop_sizes 0 0 (1 / 2) (by norm_num) (by norm_num)
  (by norm_num [abs_of_nonneg]) (0, 0)

/-- **`loopPM_real_of_herm` at the concrete instance** (`M = 1` is Hermitian, `216 × 216`). -/
example : (loopPM 3 (StepDecompLoop_sizes.L 0) (StepDecompLoop_sizes.W 0) 0 (1 / 2)
    (1 : Matrix (Idx 3 (StepDecompLoop_sizes.L 0) (StepDecompLoop_sizes.W 0))
      (Idx 3 (StepDecompLoop_sizes.L 0) (StepDecompLoop_sizes.W 0)) ℂ) 0 0).im = 0 :=
  loopPM_real_of_herm StepDecompLoop_sizes 0 0 (1 / 2) (0, 0) Matrix.isHermitian_one

/-- **`stepDecomp_loopPM` at the concrete instance** `E = 0`, `u = 1/2`, `v = 1/4`, `w = 1/2`,
`j = 0`, on the private size sequence with `d = 3`, `L = 3`, `W = 2`. -/
example (b : Zd 3 (StepDecompLoop_sizes.L 0) × Zd 3 (StepDecompLoop_sizes.L 0)) :=
  stepDecomp_loopPM StepDecompLoop_sizes (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
    0 (1 / 2) (by norm_num) (by norm_num) (by norm_num [abs_of_nonneg]) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [gridStep]) b

/-- **`stepDecomp_Z_subG_loopPM` at the concrete instance** `E = 0`, `u = 1/2`, `j = 0`, on the
private size sequence with `d = 3`, `L = 3`, `W = 2`: the event is the whole space (`hS` is
`MeasurableSet.univ`) and the variance proxy `c` is finite (`StepDecompLoop_exists_variance_bound`),
so the hypothesis `hbound` holds on the whole space. -/
private theorem StepDecompLoop_check_Z_subG
    (b : Zd 3 (StepDecompLoop_sizes.L 0) × Zd 3 (StepDecompLoop_sizes.L 0)) :
    ∃ (c : ℝ) (hc : 0 ≤ c), HasCondSubgaussianMGF (filt StepDecompLoop_sizes 0)
      ((filt StepDecompLoop_sizes).le 0)
      (fun ω => (Set.univ : Set (PathΩ StepDecompLoop_sizes)).indicator
        (fun ω => stepZ StepDecompLoop_sizes (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
          (StepDecompLoop_Phi StepDecompLoop_sizes 0 0 (1 / 2))
          (StepDecompLoop_Uw StepDecompLoop_sizes 0 0 (1 / 4) (1 / 2)) b ω) ω)
      ⟨c, hc⟩ (pathP StepDecompLoop_sizes) := by
  obtain ⟨c, hc, hbound⟩ := StepDecompLoop_exists_variance_bound StepDecompLoop_sizes
    (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0 0 (1 / 2) (by norm_num)
    (by norm_num [abs_of_nonneg]) (1 / 4) (1 / 2) (by norm_num [gridStep]) b
  exact ⟨c, hc, stepDecomp_Z_subG_loopPM StepDecompLoop_sizes (fun _ => 1 / 4) (fun _ => 3 / 4)
    (fun _ => 2) 0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num [abs_of_nonneg]) (1 / 4)
    (1 / 2) b Set.univ MeasurableSet.univ c hc (fun ω _ => hbound ω)⟩

end Check

end RBM.Path

end
