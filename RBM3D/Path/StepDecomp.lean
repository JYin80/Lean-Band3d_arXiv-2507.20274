/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.Markov
import RBM3D.Path.Stop
import RBM3D.Gauss.Stein
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Algebra.Order.Chebyshev

/-!
# The one-step decomposition of a loop observable (`d ≥ 3`)

Ticket T2073 (ST2-22).  Port of RBM2D `RBM2D/Path/StepDecomp.lean` at `c9a24cf` (itself a port of
RBM1D `RBM1D/Gauss/GridStepDecomp.lean`, commit `86573b9`) to the grid walk `pathH` of
`RBM3D/Path/Walk.lean`: a family `Φ_a` of observables (real on Hermitian matrices), two-loop labels
`a ∈ Z_L^d × Z_L^d` and real weights `U(b,a)` give the propagated martingale increment
`ξ_b = Σ_a U(b,a) (Φ_a(H_{j+1}) - E[Φ_a(H_{j+1}) | F_j])`, split as `ξ_b = Z_b + Y_b` into a
conditionally sub-Gaussian linear part `Z_b = √Δ · linTr (Ab) X_{j+1}` and a quadratic remainder
(`stepDecomp`, `stepDecomp_Z_subG`).  Paper: arXiv:2507.20274, `(MBM)` `1_2:686`; the statements are
the one-step Taylor expansion of Step 2 of `lem:main_ind`.

Renaming (`docs/tickets/ST1-COMMON.md` items 2-3): `d : Sizes` becomes `sz : Sizes d`
(`{d : ℕ} (sz : Sizes d)`), `Z2 (d.L n)` becomes `Zd d (sz.L n)`, `Idx L W` becomes `Idx d L W`,
`Coord/P/gvar/svar` become `CoordF/PF/gvarF/svarF`, `Sizes.size d n` becomes `sz.size n`
(`N = (W L)^d`).  Everything else of the statements is RBM2D's.

`d ≥ 3` changes (CLAUDE.md §5.2):

* **`gvarF ≤ 1`** (`StepDecomp_gvar_le_one`): RBM2D bounds the five-point profile `svar` by `W⁻² ≤ 1`;
  here `svarF = W^{-d} S^(B)(g)` and `S^(B)(g)` has non-negative entries with row sum `1`
  (`sum_sbKernelR`, `3 ≤ L`), so `svarF ≤ W^{-d} ≤ 1`.  New private hypothesis `hL : 3 ≤ L` (taken
  from `Sizes.three_le_L`).
* **The moments of `X`** (`integral_normSq_incr_le`, `integral_normPow4_incr_le`) are polynomials in
  `N = (W L)^d` (`CoordF d L W` has `2 N²` elements, `card_Idx`): `E ‖X‖² ≤ 16 N⁴` and
  `E ‖X‖⁴ ≤ 768 N⁸`, the same constants as `d = 2` because only `#CoordF = 2 N²` and
  `gvarF ≤ 1` enter.
* **The sub-Gaussian constant** of `stepDecomp_Z_subG` is the hypothesis `c ≥ Δ · linTrVar n (Ab ω)`
  (`linTrVar` is built from the coordinate variances `Sizes.seqGvar`); for `A = 1` it is
  `linTrVar n 1 = L^d / (1 + 2 d g²)`, `g = sz.lam n`.

The class change (T2076a of RBM2D): RBM1D's `TestFun` asks for a *global* `C²` bound; a loop
observable is not even bounded off the Hermitian set.  `HermTestFun sz n Φ` asks (H1) `C²` at
Hermitian points and (H2) a bound at Hermitian points; the second-derivative bound (H3) is the
separate hypothesis `hC₂ : ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ ‖y‖²` for Hermitian `M`, `y`.
Where a proof needs a globally smooth function (continuity of `gradMat` along the walk) it composes
with the Hermitian projection `M ↦ ½ (M + Mᴴ)`.

Every helper is `private` or carries the prefix `StepDecomp_`.  The last section compiles `stepDecomp`
and `stepDecomp_Z_subG` on the elementary family `A ↦ sin (Re tr A)` at the merged `sz0` (`d = 3`).
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
-- ported statements keep the line structure of the RBM1D source
set_option linter.style.longLine false

/-! ### 1. The gradient matrix -/

section GradMat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The gradient matrix** of `Φ` at `M`, built from the real-linear derivative
`φ = fderiv ℝ Φ M` on the Hermitian basis `E_ii`, `S_ij = E_ij + E_ji`, `T_ij = I E_ij - I E_ji`:
`G_ii = φ(E_ii)` and, for `i ≠ j`, `G_ij = ½ (φ(S_ij) + I φ(T_ij))`.  For every Hermitian `X`,
`fderiv ℝ Φ M X = tr (gradMat Φ M * X)` (`fderiv_eq_trace_gradMat`).  (RBM1D `gradMat`,
`Gauss/GridStepDecomp.lean:89`, commit `86573b9`, is built from `wirtFirst`, which RBM2D lacks: T2076c.) -/
def gradMat (Φ : Matrix ι ι ℂ → ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    if i = j then fderiv ℝ Φ M (Matrix.single i i 1)
    else (1 / 2 : ℂ) * (fderiv ℝ Φ M (Matrix.single i j 1 + Matrix.single j i 1)
      + Complex.I * fderiv ℝ Φ M (Matrix.single i j Complex.I - Matrix.single j i Complex.I))

omit [Fintype ι] in
private theorem StepDecomp_single_pair {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {i j : ι}
    (hij : i ≠ j) :
    Matrix.single i j (X i j) + Matrix.single j i (X j i)
      = (X i j).re • (Matrix.single i j (1 : ℂ) + Matrix.single j i 1)
        + (X i j).im • (Matrix.single i j Complex.I - Matrix.single j i Complex.I) := by
  have hji : X j i = (starRingEnd ℂ) (X i j) := (hX.apply j i).symm
  ext k l
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply,
    Complex.real_smul]
  by_cases h1 : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h1
    have h2 : ¬(j = i ∧ i = j) := fun h => hij h.2
    simp only [and_self, ite_true, h2, ite_false, add_zero, sub_zero]
    apply Complex.ext <;> simp
  · by_cases h2 : j = k ∧ i = l
    · obtain ⟨rfl, rfl⟩ := h2
      have h3 : ¬(i = j ∧ j = i) := fun h => hij h.1
      simp only [h3, ite_false, and_self, ite_true, zero_add, hji]
      apply Complex.ext <;> simp
    · simp [h1, h2]

omit [Fintype ι] in
private theorem StepDecomp_single_diag {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (i : ι) :
    Matrix.single i i (X i i) = (X i i).re • Matrix.single i i (1 : ℂ) := by
  have hre : X i i = ((X i i).re : ℂ) := (Complex.conj_eq_iff_re.mp (hX.apply i i)).symm
  ext k l
  simp only [Matrix.smul_apply, Matrix.single_apply, Complex.real_smul]
  by_cases h : i = k ∧ i = l
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, mul_one]
    exact hre
  · simp only [h, ite_false, mul_zero]

/-- **The trace identity.**  For Hermitian `X`, `fderiv ℝ Φ M X = tr (gradMat Φ M * X)`; no
hypothesis on `Φ` (RBM1D `fderiv_eq_trace_gradMat`, `Gauss/GridStepDecomp.lean:282` at commit
`86573b9`, which has none either). -/
theorem fderiv_eq_trace_gradMat {Φ : Matrix ι ι ℂ → ℂ} (M : Matrix ι ι ℂ) {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) : fderiv ℝ Φ M X = Matrix.trace (gradMat Φ M * X) := by
  set φ : Matrix ι ι ℂ →L[ℝ] ℂ := fderiv ℝ Φ M with hφ
  have hpair : ∀ i j, φ (Matrix.single i j (X i j)) + φ (Matrix.single j i (X j i))
      = gradMat Φ M i j * X j i + gradMat Φ M j i * X i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have hre : X i i = ((X i i).re : ℂ) := (Complex.conj_eq_iff_re.mp (hX.apply i i)).symm
      rw [StepDecomp_single_diag hX, map_smul]
      simp only [gradMat, Matrix.of_apply, ite_true, Complex.real_smul]
      rw [← hφ]
      linear_combination (-2 * φ (Matrix.single i i 1)) * hre
    · have hji : X j i = (starRingEnd ℂ) (X i j) := (hX.apply j i).symm
      rw [← map_add, StepDecomp_single_pair hX hij, map_add, map_smul, map_smul]
      simp only [gradMat, Matrix.of_apply, hij, Ne.symm hij, ite_false]
      have hS : Matrix.single j i (1 : ℂ) + Matrix.single i j 1
          = Matrix.single i j 1 + Matrix.single j i 1 := add_comm _ _
      have hT : Matrix.single j i Complex.I - Matrix.single i j Complex.I
          = -(Matrix.single i j Complex.I - Matrix.single j i Complex.I) := by abel
      rw [hS, hT, hji, ← hφ]
      simp only [map_add, map_sub, map_neg, Complex.real_smul]
      have hx : X i j = ((X i j).re : ℂ) + ((X i j).im : ℂ) * Complex.I :=
        (Complex.re_add_im _).symm
      have hxc : (starRingEnd ℂ) (X i j) = ((X i j).re : ℂ) - ((X i j).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hxc]
      set a := (X i j).re
      set b := (X i j).im
      rw [hx]
      linear_combination (↑b * (φ (Matrix.single i j Complex.I) - φ (Matrix.single j i Complex.I)))
        * Complex.I_sq
  have hF : φ X = ∑ i, ∑ j, φ (Matrix.single i j (X i j)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
  have hT : Matrix.trace (gradMat Φ M * X) = ∑ i, ∑ j, gradMat Φ M i j * X j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have hsw : ∀ f : ι → ι → ℂ, ∑ i, ∑ j, f j i = ∑ i, ∑ j, f i j := fun f => Finset.sum_comm
  have h2 : 2 * φ X = 2 * Matrix.trace (gradMat Φ M * X) := by
    have e1 : ∑ i, ∑ j, φ (Matrix.single j i (X j i)) = φ X := by
      rw [hF]; exact hsw (fun i j => φ (Matrix.single i j (X i j)))
    have e2 : ∑ i, ∑ j, gradMat Φ M j i * X i j = Matrix.trace (gradMat Φ M * X) := by
      rw [hT]; exact hsw (fun i j => gradMat Φ M i j * X j i)
    calc 2 * φ X
        = ∑ i, ∑ j, φ (Matrix.single i j (X i j)) + ∑ i, ∑ j, φ (Matrix.single j i (X j i)) := by
          rw [e1, ← hF]; ring
      _ = ∑ i, ∑ j, (gradMat Φ M i j * X j i + gradMat Φ M j i * X i j) := by
          simp only [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpair i j
      _ = 2 * Matrix.trace (gradMat Φ M * X) := by
          simp only [Finset.sum_add_distrib]
          rw [e2, ← hT]; ring
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) h2

end GradMat

/-! ### 2. The Hermitian class and the Hermitian projection -/

/-- **The class change of T2076 (T2076a).**  RBM1D's `TestFun` asks for a *globally* smooth,
bounded `Φ`; a loop observable is neither off the Hermitian set (the resolvent is unbounded).
`HermTestFun sz n Φ` asks only for (H1) `C²` smoothness at every Hermitian point and (H2) a bound at
Hermitian points.  The Hermitian-direction bound (H3) on the second derivative is the separate
hypothesis `hC₂` of the theorems below, as in RBM1D. -/
structure HermTestFun {d : ℕ} (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) : Prop where
  contDiffAt : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M
  bdd₀ : ∃ C₀ : ℝ, ∀ M, M.IsHermitian → ‖Φ M‖ ≤ C₀

section Herm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian projection `M ↦ ½ (M + Mᴴ)` as a continuous `ℝ`-linear map (the pattern of
RBM1D `hermCLM`, `Gauss/Generator.lean:1397`, commit `86573b9`). -/
private def StepDecomp_hermCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
      map_add' := by
        intro M M'
        rw [Matrix.conjTranspose_add]
        module
      map_smul' := by
        intro r M
        rw [RingHom.id_apply, Matrix.conjTranspose_smul, star_trivial]
        module }

private theorem StepDecomp_hermCLM_apply (M : Matrix ι ι ℂ) :
    StepDecomp_hermCLM ι M = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M) := rfl

private theorem StepDecomp_isHermitian_hermCLM (M : Matrix ι ι ℂ) :
    (StepDecomp_hermCLM ι M).IsHermitian := by
  change Matrix.conjTranspose ((2⁻¹ : ℝ) • (M + Matrix.conjTranspose M))
      = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

private theorem StepDecomp_hermCLM_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    StepDecomp_hermCLM ι M = M := by
  rw [StepDecomp_hermCLM_apply, hM]
  module

omit [Fintype ι] in
private theorem StepDecomp_isHermitian_single_diag (i : ι) :
    (Matrix.single i i (1 : ℂ)).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_single]

omit [Fintype ι] in
private theorem StepDecomp_isHermitian_S (i j : ι) :
    (Matrix.single i j (1 : ℂ) + Matrix.single j i 1).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]

omit [Fintype ι] in
private theorem StepDecomp_isHermitian_T (i j : ι) :
    (Matrix.single i j Complex.I - Matrix.single j i Complex.I).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
  simp only [Complex.star_def, Complex.conj_I, ← Matrix.single_neg]
  abel

/-- `Φ ∘ P` is `C²` everywhere when `Φ` is `C²` at every Hermitian point. -/
private theorem StepDecomp_contDiff_comp {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) :
    ContDiff ℝ 2 (fun M => Φ (StepDecomp_hermCLM ι M)) :=
  contDiff_iff_contDiffAt.2 fun M =>
    (h _ (StepDecomp_isHermitian_hermCLM M)).comp M (StepDecomp_hermCLM ι).contDiff.contDiffAt

/-- The first derivative of `Φ ∘ P` at a Hermitian point, along a Hermitian direction, is that of
`Φ`. -/
private theorem StepDecomp_fderiv_comp {Φ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M) {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    fderiv ℝ (fun M' => Φ (StepDecomp_hermCLM ι M')) M B = fderiv ℝ Φ M B := by
  have hPM := StepDecomp_hermCLM_of_isHermitian hM
  have hf : DifferentiableAt ℝ Φ (StepDecomp_hermCLM ι M) := by rw [hPM]; exact hΦ
  have h : HasFDerivAt (fun M' => Φ (StepDecomp_hermCLM ι M'))
      ((fderiv ℝ Φ (StepDecomp_hermCLM ι M)).comp (StepDecomp_hermCLM ι)) M :=
    hf.hasFDerivAt.comp M (StepDecomp_hermCLM ι).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hPM, StepDecomp_hermCLM_of_isHermitian hB]

/-- The gradient matrix of `Φ ∘ P` at a Hermitian point is that of `Φ`: `gradMat` reads `Φ`
only along Hermitian directions. -/
private theorem StepDecomp_gradMat_comp {Φ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M) :
    gradMat (fun M' => Φ (StepDecomp_hermCLM ι M')) M = gradMat Φ M := by
  ext i j
  simp only [gradMat, Matrix.of_apply]
  rw [StepDecomp_fderiv_comp hM hΦ (StepDecomp_isHermitian_single_diag i),
    StepDecomp_fderiv_comp hM hΦ (StepDecomp_isHermitian_S i j),
    StepDecomp_fderiv_comp hM hΦ (StepDecomp_isHermitian_T i j)]

private theorem StepDecomp_continuous_gradMat {Ψ : Matrix ι ι ℂ → ℂ} (h : ContDiff ℝ 2 Ψ) :
    Continuous (gradMat Ψ) := by
  have hc : ∀ B : Matrix ι ι ℂ, Continuous fun M => fderiv ℝ Ψ M B :=
    fun B => (h.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine continuous_matrix fun i j => ?_
  simp only [gradMat, Matrix.of_apply]
  split_ifs
  · exact hc _
  · exact continuous_const.mul ((hc _).add (continuous_const.mul (hc _)))

end Herm

/-! ### 3. The second-order Taylor remainder along a Hermitian line -/

section Taylor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (RBM1D `hasDerivAt_add_smul`, `Gauss/GridStepDecomp.lean:331`.) -/
private theorem StepDecomp_hasDerivAt_add_smul (M y : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => M + t' • y) y t := by
  simpa using ((hasDerivAt_id t).smul_const y).const_add M

private theorem StepDecomp_isHermitian_add_smul {M y : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hy : y.IsHermitian) (t : ℝ) : (M + t • y).IsHermitian := by
  have hcast : M + t • y = M + (t : ℂ) • y := by rw [Complex.coe_smul]
  rw [hcast]
  exact hM.add (hy.smul (Complex.conj_ofReal t))

/-- `RBM1D` `hasFDerivAt_fderiv_apply'` (`Gauss/TestFunHerm.lean:104`, commit `86573b9`). -/
private theorem StepDecomp_hasFDerivAt_fderiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {M : E} (h : DifferentiableAt ℝ (fderiv ℝ f) M) (A : E) :
    HasFDerivAt (fun M' => fderiv ℝ f M' A) ((fderiv ℝ (fderiv ℝ f) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- **The pathwise second-order Taylor remainder bound along a Hermitian line** (RBM1D
`norm_taylor_remainder_le`, `Gauss/GridStepDecomp.lean:342`, commit `86573b9`).  Only (H1) at
Hermitian points and the Hermitian-direction bound (H3) are used; every point of the segment
`M + t y` is Hermitian. -/
private theorem StepDecomp_taylor {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {C₂ : ℝ}
    (hC₂ : ∀ M y : Matrix ι ι ℂ, M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {M y : Matrix ι ι ℂ} (hM : M.IsHermitian) (hy : y.IsHermitian) {s : ℝ} (hs : 0 ≤ s) :
    ‖Φ (M + s • y) - Φ M - s • fderiv ℝ Φ M y‖ ≤ (C₂ / 2) * s ^ 2 * ‖y‖ ^ 2 := by
  have hH := StepDecomp_isHermitian_add_smul hM hy
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ Φ (M + t • y) :=
    fun t => (h _ (hH t)).differentiableAt (by norm_num)
  have hdiff2 : ∀ t : ℝ, DifferentiableAt ℝ (fderiv ℝ Φ) (M + t • y) := fun t =>
    ((h _ (hH t)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y)) (fderiv ℝ Φ (M + t • y) y) t :=
    fun t => ((hdiff t).hasFDerivAt).comp_hasDerivAt t (StepDecomp_hasDerivAt_add_smul M y t)
  have hk : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => fderiv ℝ Φ (M + t' • y) y)
      (fderiv ℝ (fderiv ℝ Φ) (M + t • y) y y) t := by
    intro t
    have h1 := (StepDecomp_hasFDerivAt_fderiv_apply (hdiff2 t) y).comp_hasDerivAt t
      (StepDecomp_hasDerivAt_add_smul M y t)
    simp only [ContinuousLinearMap.flip_apply] at h1
    exact h1
  set k : ℝ → ℂ := fun t => fderiv ℝ Φ (M + t • y) y with hk_def
  have hkCont : Continuous k := continuous_iff_continuousAt.2 fun t => (hk t).continuousAt
  have hlevel1 : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖k t - k 0‖ ≤ C₂ * ‖y‖ ^ 2 * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment
      hkCont.continuousOn (fun t _ => (hk t).hasDerivWithinAt)
      (fun t _ => by simpa using hC₂ (M + t • y) y (hH t) hy)
  have hg : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y)
      (k t - k 0) t := by
    intro t
    have h1 := (hp t).sub_const (Φ M)
    have h2 : HasDerivAt (fun t' : ℝ => t' • fderiv ℝ Φ M y) (fderiv ℝ Φ M y) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ Φ M y)
    have h3 := h1.sub h2
    have hk0 : k 0 = fderiv ℝ Φ M y := by simp [hk_def]
    rw [hk0]
    exact h3
  set g : ℝ → ℂ := fun t' => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y with hg_def
  have hgCont : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  set B : ℝ → ℝ := fun t => (C₂ / 2) * ‖y‖ ^ 2 * t ^ 2 with hB_def
  have hB : ∀ t : ℝ, HasDerivAt B (C₂ * ‖y‖ ^ 2 * t) t := by
    intro t
    have h1 : HasDerivAt (fun t' : ℝ => t' ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 := h1.const_mul (C₂ / 2 * ‖y‖ ^ 2)
    have heq : C₂ / 2 * ‖y‖ ^ 2 * (2 * t) = C₂ * ‖y‖ ^ 2 * t := by ring
    rw [heq] at h2
    exact h2
  have ha0 : ‖g 0‖ ≤ B 0 := by simp [hg_def, hB_def]
  have hfinal := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    hgCont.continuousOn (fun t _ => (hg t).hasDerivWithinAt) ha0 hB
    (fun t ht => by simpa using hlevel1 t ⟨ht.1, ht.2.le⟩)
  have hgs := hfinal (Set.right_mem_Icc.2 hs)
  simp only [hg_def, hB_def] at hgs
  have heq : C₂ / 2 * ‖y‖ ^ 2 * s ^ 2 = C₂ / 2 * s ^ 2 * ‖y‖ ^ 2 := by ring
  linarith [hgs, heq]

end Taylor

/-! ### 4. Moments of one increment: `E ‖X‖² ≤ 16 N⁴` and `E ‖X‖⁴ ≤ 768 N⁸`, `N = (W L)^d`

RBM1D obtains integrability from `integrable_norm_Xmat_pow`, which RBM2D lacks; the private
`OneStep_` lemmas of `Path/OneStep.lean` are not importable, so the counting lemmas are re-proved
here (`CoordF d L W` has `2 N²` elements, `N = (W L)^d`). -/

section Moments

private theorem StepDecomp_norm_single_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι)
    (a : ℂ) : ‖(Matrix.single i j a : Matrix ι ι ℂ)‖ ≤ ‖a‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => ?_
  have h : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Matrix.single i j a) v
      = EuclideanSpace.single i (a * v j) := by
    ext k
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.single_mulVec, Function.update_apply]
  rw [h, EuclideanSpace.single, PiLp.norm_single, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)

/-- The `ℓ²` operator norm is at most the sum of the moduli of the entries. -/
private theorem StepDecomp_norm_le_sum_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => StepDecomp_norm_single_le i j _))

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

private theorem StepDecomp_norm_Xentry_le (ω : Ω d L W) (i j : Idx d L W) :
    ‖Xentry d L W ω i j‖ ≤
      (|ω (i, j, true)| + |ω (i, j, false)|) + (|ω (j, i, true)| + |ω (j, i, false)|) := by
  have h1 := abs_nonneg (ω (i, j, true))
  have h2 := abs_nonneg (ω (i, j, false))
  have h3 := abs_nonneg (ω (j, i, true))
  have h4 := abs_nonneg (ω (j, i, false))
  unfold Xentry
  split_ifs
  · refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

private theorem StepDecomp_sum_coord (f : CoordF d L W → ℝ) :
    ∑ c : CoordF d L W, f c = ∑ i : Idx d L W, ∑ j : Idx d L W, (f (i, j, true) + f (i, j, false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

/-- `‖X‖ ≤ 2 Σ_c |ω_c|` (RBM2D `OneStep_norm_blockMat_Xmat_le`, here in `Idx` coordinates). -/
private theorem StepDecomp_norm_Xmat_le (ω : Ω d L W) :
    ‖Xmat d L W ω‖ ≤ 2 * ∑ c : CoordF d L W, |ω c| := by
  refine (StepDecomp_norm_le_sum_entries _).trans ?_
  rw [StepDecomp_sum_coord]
  have hswap : ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (j, i, true)| + |ω (j, i, false)|)
      = ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (i, j, true)| + |ω (i, j, false)|) :=
    Finset.sum_comm
  calc ∑ i : Idx d L W, ∑ j : Idx d L W, ‖Xmat d L W ω i j‖
      ≤ ∑ i : Idx d L W, ∑ j : Idx d L W, ((|ω (i, j, true)| + |ω (i, j, false)|)
          + (|ω (j, i, true)| + |ω (j, i, false)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => StepDecomp_norm_Xentry_le ω i j
    _ = 2 * ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (i, j, true)| + |ω (i, j, false)|) := by
        simp only [Finset.sum_add_distrib] at hswap ⊢
        linarith [hswap]

/-- **`gvarF ≤ 1`** (`d ≥ 3` replacement of RBM2D `StepDecomp_gvar_le_one`, `Path/StepDecomp.lean:439`):
`svarF = W^{-d} S^(B)(g)` is `W^{-d}` times a kernel entry of the stochastic matrix `S^(B)`, whose
rows sum to `1` (`sum_sbKernelR`, which needs `3 ≤ L`); the proof is not RBM2D's (the fixed
five-point profile). -/
private theorem StepDecomp_gvar_le_one (hL : 3 ≤ L) (c : CoordF d L W) :
    (gvarF d L W g c : ℝ) ≤ 1 := by
  have hW : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h1 : ((W : ℝ) ^ d)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hW)
  have hk : ∀ i j : Idx d L W, svarF d L W g i j ≤ 1 := by
    intro i j
    have h2 : SBR d L g (split d L W i).1 (split d L W j).1 ≤ 1 := by
      simp only [SBR, Matrix.of_apply]
      calc sbKernelR d L g ((split d L W i).1 - (split d L W j).1)
          ≤ ∑ x, sbKernelR d L g x :=
            Finset.single_le_sum (f := sbKernelR d L g) (fun x _ => sbKernelR_nonneg d L g x)
              (Finset.mem_univ _)
        _ = 1 := sum_sbKernelR d L g hL
    have h3 : 0 ≤ SBR d L g (split d L W i).1 (split d L W j).1 := by
      simpa [SBR] using sbKernelR_nonneg d L g _
    unfold svarF
    calc ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j).1
        ≤ 1 * 1 := mul_le_mul h1 h2 h3 zero_le_one
      _ = 1 := one_mul 1
  have h0 := svarF_nonneg d L W g c.1 c.2.1
  have hs := hk c.1 c.2.1
  change (if c.1 = c.2.1 then svarF d L W g c.1 c.2.1 else svarF d L W g c.1 c.2.1 / 2) ≤ 1
  split_ifs <;> linarith

/-- `#Coord = 2 N²`, `N = (W L)^d` (`1_2:263`; rule R3): RBM2D `StepDecomp_card_Coord`,
`Path/StepDecomp.lean:451`. -/
private theorem StepDecomp_card_Coord :
    (Fintype.card (CoordF d L W) : ℝ) = 2 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 := by
  have : Fintype.card (CoordF d L W) = 2 * (Fintype.card (Idx d L W)) ^ 2 := by
    simp [CoordF, Fintype.card_prod, Fintype.card_bool]
    ring
  rw [this]
  push_cast
  have h2 : (Fintype.card (Idx d L W) : ℝ) = (((W * L) ^ d : ℕ) : ℝ) := by
    rw [card_Idx]
  rw [h2]
  push_cast
  ring

/-! #### The fourth moment of a centred Gaussian coordinate -/

private theorem StepDecomp_integrable_pow_mul_pdf {v : ℝ≥0} (hv : 0 < (v : ℝ)) (k : ℕ) :
    Integrable fun x : ℝ => x ^ k * gaussianPDFReal 0 v x := by
  have hb : (0 : ℝ) < 1 / (2 * (v : ℝ)) := by positivity
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hk).const_mul
      ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.rpow_natCast, gaussianPDFReal]
  rw [show -(1 / (2 * (v : ℝ))) * x ^ 2 = -(x - 0) ^ 2 / (2 * (v : ℝ)) by ring]
  ring

/-- `E x⁴ = 3 v²` for `x ~ N(0, v)`, by Stein's identity `E[x f(x)] = v E[f'(x)]` with `f = x³`;
only `E x⁴ ≤ 3` for `v ≤ 1` is kept. -/
private theorem StepDecomp_integral_pow4_gaussian {v : ℝ≥0} (hv1 : (v : ℝ) ≤ 1) :
    ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) ≤ 3 := by
  by_cases hv0 : v = 0
  · subst hv0
    rw [gaussianReal_zero_var, integral_dirac]
    norm_num
  · have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne v.coe_nonneg (Ne.symm (NNReal.coe_ne_zero.mpr hv0))
    have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := fun x => by
      simpa using hasDerivAt_pow 3 x
    have h1 : Integrable fun x : ℝ => x ^ 3 * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
      have := (StepDecomp_integrable_pow_mul_pdf hvpos 4).const_mul (-(1 / (v : ℝ)))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      field_simp
    have h2 : Integrable fun x : ℝ => (3 * x ^ 2) * gaussianPDFReal 0 v x := by
      have := (StepDecomp_integrable_pow_mul_pdf hvpos 2).const_mul 3
      exact this.congr (Filter.Eventually.of_forall fun x => by simp only; ring)
    have h3 := StepDecomp_integrable_pow_mul_pdf hvpos 3
    have hst := integral_mul_gaussianReal hv0 hf h1 h2 h3
    have hsq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = v := by
      have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
      rw [variance_eq_integral measurable_id'.aemeasurable] at h
      simpa using h
    have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
      (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
    rw [integral_const_mul, hsq] at hst
    have hx : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) = (v : ℝ) * (3 * (v : ℝ)) := by
      rw [← hst]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
    rw [hx]
    nlinarith [hvpos, hv1]

end Moments

section MomentsBound

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

private theorem StepDecomp_integrable_pow4_coord (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => (ω c) ^ 4) (PF d L W g) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) := (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 4) ((PF d L W g).map fun ω => ω c) := by
    rw [P_map_eval]
    have h := (memLp_id_gaussianReal (μ := 0) (v := gvarF d L W g c) 4).integrable_norm_pow
      (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [id, Real.norm_eq_abs]
    exact (Even.pow_abs (by decide) x)
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem StepDecomp_integral_pow4_coord_le (hL : 3 ≤ L) (c : CoordF d L W) :
    ∫ ω : Ω d L W, (ω c) ^ 4 ∂(PF d L W g) ≤ 3 := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) := (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 4) ((PF d L W g).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, P_map_eval]
  exact StepDecomp_integral_pow4_gaussian (StepDecomp_gvar_le_one hL c)

private theorem StepDecomp_norm_sq_le (ω : Ω d L W) :
    ‖Xmat d L W ω‖ ^ 2 ≤ 4 * (Fintype.card (CoordF d L W) : ℝ) * ∑ c : CoordF d L W, (ω c) ^ 2 := by
  have h := StepDecomp_norm_Xmat_le ω
  have h0 := norm_nonneg (Xmat d L W ω)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c : CoordF d L W => |ω c|)
  simp only [sq_abs, Finset.card_univ] at hcs
  calc ‖Xmat d L W ω‖ ^ 2 ≤ (2 * ∑ c : CoordF d L W, |ω c|) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 4 * (∑ c : CoordF d L W, |ω c|) ^ 2 := by ring
    _ ≤ 4 * ((Fintype.card (CoordF d L W) : ℝ) * ∑ c : CoordF d L W, (ω c) ^ 2) := by linarith
    _ = _ := by ring

private theorem StepDecomp_norm_pow4_le (ω : Ω d L W) :
    ‖Xmat d L W ω‖ ^ 4 ≤ 16 * (Fintype.card (CoordF d L W) : ℝ) ^ 3 * ∑ c : CoordF d L W, (ω c) ^ 4 := by
  have h := StepDecomp_norm_Xmat_le ω
  have h0 := norm_nonneg (Xmat d L W ω)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c : CoordF d L W => |ω c|)
  simp only [sq_abs, Finset.card_univ] at hcs
  have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c : CoordF d L W => (ω c) ^ 2)
  simp only [← pow_mul, Finset.card_univ] at hcs2
  have hcard : (0 : ℝ) ≤ (Fintype.card (CoordF d L W) : ℝ) := Nat.cast_nonneg _
  have hS0 : 0 ≤ ∑ c : CoordF d L W, |ω c| := Finset.sum_nonneg fun c _ => abs_nonneg _
  calc ‖Xmat d L W ω‖ ^ 4 ≤ (2 * ∑ c : CoordF d L W, |ω c|) ^ 4 := pow_le_pow_left₀ h0 h 4
    _ = 16 * ((∑ c : CoordF d L W, |ω c|) ^ 2) ^ 2 := by ring
    _ ≤ 16 * ((Fintype.card (CoordF d L W) : ℝ) * ∑ c : CoordF d L W, (ω c) ^ 2) ^ 2 := by
        gcongr
    _ = 16 * (Fintype.card (CoordF d L W) : ℝ) ^ 2 * (∑ c : CoordF d L W, (ω c) ^ 2) ^ 2 := by ring
    _ ≤ 16 * (Fintype.card (CoordF d L W) : ℝ) ^ 2
          * ((Fintype.card (CoordF d L W) : ℝ) * ∑ c : CoordF d L W, (ω c) ^ 4) := by
        gcongr
    _ = _ := by ring

private theorem StepDecomp_integrable_normSq :
    Integrable (fun ω : Ω d L W => ‖Xmat d L W ω‖ ^ 2) (PF d L W g) := by
  have hint : Integrable (fun ω : Ω d L W =>
      4 * (Fintype.card (CoordF d L W) : ℝ) * ∑ c : CoordF d L W, (ω c) ^ 2) (PF d L W g) :=
    (integrable_finsetSum _ fun c _ => integrable_sq_coord d L W g c).const_mul _
  refine hint.mono' ((continuous_norm.comp (continuous_Xmat d L W)).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact StepDecomp_norm_sq_le ω

private theorem StepDecomp_integrable_normPow4 :
    Integrable (fun ω : Ω d L W => ‖Xmat d L W ω‖ ^ 4) (PF d L W g) := by
  have hint : Integrable (fun ω : Ω d L W =>
      16 * (Fintype.card (CoordF d L W) : ℝ) ^ 3 * ∑ c : CoordF d L W, (ω c) ^ 4) (PF d L W g) :=
    (integrable_finsetSum _ fun c _ => StepDecomp_integrable_pow4_coord c).const_mul _
  refine hint.mono' ((continuous_norm.comp (continuous_Xmat d L W)).pow 4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact StepDecomp_norm_pow4_le ω

private theorem StepDecomp_integral_normSq_le (hL : 3 ≤ L) :
    ∫ ω : Ω d L W, ‖Xmat d L W ω‖ ^ 2 ∂(PF d L W g) ≤ 16 * (((W * L) ^ d : ℕ) : ℝ) ^ 4 := by
  have hcard := StepDecomp_card_Coord (d := d) (L := L) (W := W)
  calc ∫ ω : Ω d L W, ‖Xmat d L W ω‖ ^ 2 ∂(PF d L W g)
      ≤ ∫ ω : Ω d L W, 4 * (Fintype.card (CoordF d L W) : ℝ) * ∑ c : CoordF d L W, (ω c) ^ 2 ∂(PF d L W g) :=
        integral_mono StepDecomp_integrable_normSq
          ((integrable_finsetSum _ fun c _ => integrable_sq_coord d L W g c).const_mul _)
          fun ω => StepDecomp_norm_sq_le ω
    _ = 4 * (Fintype.card (CoordF d L W) : ℝ) * ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => integrable_sq_coord d L W g c]
        simp only [integral_sq_coord]
    _ ≤ 4 * (Fintype.card (CoordF d L W) : ℝ) * ∑ _c : CoordF d L W, (1 : ℝ) := by
        gcongr with c
        exact StepDecomp_gvar_le_one hL c
    _ = 16 * (((W * L) ^ d : ℕ) : ℝ) ^ 4 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
        ring

private theorem StepDecomp_integral_normPow4_le (hL : 3 ≤ L) :
    ∫ ω : Ω d L W, ‖Xmat d L W ω‖ ^ 4 ∂(PF d L W g) ≤ 768 * (((W * L) ^ d : ℕ) : ℝ) ^ 8 := by
  have hcard := StepDecomp_card_Coord (d := d) (L := L) (W := W)
  calc ∫ ω : Ω d L W, ‖Xmat d L W ω‖ ^ 4 ∂(PF d L W g)
      ≤ ∫ ω : Ω d L W, 16 * (Fintype.card (CoordF d L W) : ℝ) ^ 3 * ∑ c : CoordF d L W, (ω c) ^ 4
          ∂(PF d L W g) :=
        integral_mono StepDecomp_integrable_normPow4
          ((integrable_finsetSum _ fun c _ => StepDecomp_integrable_pow4_coord c).const_mul _)
          fun ω => StepDecomp_norm_pow4_le ω
    _ = 16 * (Fintype.card (CoordF d L W) : ℝ) ^ 3
          * ∑ c : CoordF d L W, ∫ ω : Ω d L W, (ω c) ^ 4 ∂(PF d L W g) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => StepDecomp_integrable_pow4_coord c]
    _ ≤ 16 * (Fintype.card (CoordF d L W) : ℝ) ^ 3 * ∑ _c : CoordF d L W, (3 : ℝ) := by
        gcongr with c
        exact StepDecomp_integral_pow4_coord_le hL c
    _ = 768 * (((W * L) ^ d : ℕ) : ℝ) ^ 8 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        ring

end MomentsBound

section MomentsPath

variable {d : ℕ} (sz : Sizes d)

private theorem StepDecomp_map_incr_slice (n j : ℕ) :
    (pathP sz).map (fun ω : PathΩ sz => Sizes.slice sz n (ω (j + 1))) = PF d (sz.L n) (sz.W n) (sz.lam n) := by
  have h := Measure.map_map (μ := pathP sz) (Sizes.measurable_slice sz n)
    (measurable_pi_apply (j + 1) : Measurable fun ω : PathΩ sz => ω (j + 1))
  rw [map_incr, Sizes.seqP_map_slice] at h
  exact h.symm

private theorem StepDecomp_measurable_incr (n j : ℕ) :
    Measurable fun ω : PathΩ sz => Sizes.slice sz n (ω (j + 1)) :=
  (Sizes.measurable_slice sz n).comp (measurable_pi_apply (j + 1))

/-- Transfer of a fixed-size function along one increment, through `map_incr` and
`Sizes.seqP_map_slice`: integrability, and the value of the integral. -/
private theorem StepDecomp_transfer (n j : ℕ) {f : Ω d (sz.L n) (sz.W n) → ℝ}
    (hf : Integrable f (PF d (sz.L n) (sz.W n) (sz.lam n))) :
    Integrable (fun ω : PathΩ sz => f (Sizes.slice sz n (ω (j + 1)))) (pathP sz) ∧
      ∫ ω : PathΩ sz, f (Sizes.slice sz n (ω (j + 1))) ∂(pathP sz)
        = ∫ x, f x ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
  have hmap := StepDecomp_map_incr_slice sz n j
  have hgm : AEStronglyMeasurable f
      ((pathP sz).map fun ω : PathΩ sz => Sizes.slice sz n (ω (j + 1))) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have hm : AEMeasurable (fun ω : PathΩ sz => Sizes.slice sz n (ω (j + 1))) (pathP sz) :=
    (StepDecomp_measurable_incr sz n j).aemeasurable
  refine ⟨(integrable_map_measure hgm hm).1 (by rw [hmap]; exact hf), ?_⟩
  have h := integral_map hm hgm
  rw [hmap] at h
  exact h.symm

/-- `‖X_{j+1}‖²` is integrable (RBM1D `integrable_normSq_incr`, `Gauss/GridStepDecomp.lean:577`). -/
theorem integrable_normSq_incr (n j : ℕ) :
    Integrable (fun ω : PathΩ sz => ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2) (pathP sz) :=
  (StepDecomp_transfer sz n j
    (f := fun x => ‖Xmat d (sz.L n) (sz.W n) x‖ ^ 2) StepDecomp_integrable_normSq).1

/-- `‖X_{j+1}‖⁴` is integrable (RBM1D `integrable_normPow4_incr`, `Gauss/GridStepDecomp.lean:592`). -/
theorem integrable_normPow4_incr (n j : ℕ) :
    Integrable (fun ω : PathΩ sz => ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4) (pathP sz) :=
  (StepDecomp_transfer sz n j
    (f := fun x => ‖Xmat d (sz.L n) (sz.W n) x‖ ^ 4) StepDecomp_integrable_normPow4).1

/-- **The second moment of one increment**: `E ‖X_{j+1}‖² ≤ 16 N⁴`, `N = (W L)²`. -/
theorem integral_normSq_incr_le (n j : ℕ) :
    ∫ ω : PathΩ sz, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 ∂(pathP sz)
      ≤ 16 * (sz.size n : ℝ) ^ 4 :=
  le_of_eq_of_le (StepDecomp_transfer sz n j
    (f := fun x => ‖Xmat d (sz.L n) (sz.W n) x‖ ^ 2) StepDecomp_integrable_normSq).2
    (StepDecomp_integral_normSq_le (d := d) (L := sz.L n) (W := sz.W n) (g := sz.lam n)
      (sz.three_le_L n))

/-- **The fourth moment of one increment**: `E ‖X_{j+1}‖⁴ ≤ 768 N⁸`, `N = (W L)²`. -/
theorem integral_normPow4_incr_le (n j : ℕ) :
    ∫ ω : PathΩ sz, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz)
      ≤ 768 * (sz.size n : ℝ) ^ 8 :=
  le_of_eq_of_le (StepDecomp_transfer sz n j
    (f := fun x => ‖Xmat d (sz.L n) (sz.W n) x‖ ^ 4) StepDecomp_integrable_normPow4).2
    (StepDecomp_integral_normPow4_le (d := d) (L := sz.L n) (W := sz.W n) (g := sz.lam n)
      (sz.three_le_L n))

end MomentsPath
/-! ### 5. The decomposition of one grid step -/

section StepDecomp

variable {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
  {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}

/-- **`Ab`**: the `filt sz j`-measurable direction attached to a label-indexed family `Φ`, a real
backward kernel `U` and a target label `b`: `Ab ω = Σ_a U(b,a) • gradMat (Φ a) (H_j ω)`
(RBM1D `Ab`, `Gauss/GridStepDecomp.lean:433`, commit `86573b9`). -/
noncomputable def Ab {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) • gradMat (Φ a) (pathH sz s t K n j ω)

/-- **`stepZ`**: the exactly linear part of one grid step, `Z b ω = √Δ · linTr n (Ab ω) X_{j+1}`
(RBM1D `stepZ`, `Gauss/GridStepDecomp.lean:441`). -/
noncomputable def stepZ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) : ℝ :=
  Real.sqrt (gridStep s t K n) *
    linTr n (Ab sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1)))

/-- **`stepXi`**: the propagated observable minus its `filt sz j`-conditional mean,
`ξ_b = Σ_a U(b,a) Φ_a(H_{j+1}) - E[Σ_a U(b,a) Φ_a(H_{j+1}) | F_j]`
(RBM1D `stepXi`, `Gauss/GridStepDecomp.lean:448`). -/
noncomputable def stepXi {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) : ℂ :=
  (∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω))
    - (pathP sz)[fun ω' => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
        (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω

/-- **`stepY`**: the quadratic remainder, `Y_b = ξ_b - Z_b` (RBM1D `stepY`, `Gauss/GridStepDecomp.lean:456`). -/
noncomputable def stepY {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) : ℂ :=
  stepXi sz s t K n j Φ U b ω - (stepZ sz s t K n j Φ U b ω : ℂ)

/-- `lin_eq_fderiv` (RBM1D, `Gauss/GridStepDecomp.lean:309`): the real part of the derivative in a
Hermitian direction is `linTr` of the gradient matrix. -/
theorem lin_eq_fderiv {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hX : X.IsHermitian) :
    (fderiv ℝ Ψ M X).re = linTr n (gradMat Ψ M) X := by
  rw [fderiv_eq_trace_gradMat M hX]; rfl

/-- The grid walk is `filt sz j`-measurable as a matrix-valued map, and measurable. -/
private theorem StepDecomp_measurable_pathH (k : ℕ) :
    Measurable fun ω : PathΩ sz => pathH sz s t K n k ω :=
  (pathH_measurable_filt sz s t K n k).mono ((filt sz).le k) le_rfl

private theorem StepDecomp_measurable_seqXmat (i : ℕ) :
    Measurable fun ω : PathΩ sz => Sizes.seqXmat sz n (ω i) :=
  ((continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice sz n)).comp
    (measurable_pi_apply i)

/-- The grid recursion `H_{k+1} = H_k + √Δ X_{k+1}` with the real scalar (RBM1D `H_succ_eq`,
`Gauss/GridStepDecomp.lean:532`; RBM2D `pathH_succ`, `Path/LoopStep.lean`, is not imported). -/
private theorem StepDecomp_pathH_succ (k : ℕ) (ω : PathΩ sz) :
    pathH sz s t K n (k + 1) ω
      = pathH sz s t K n k ω + Real.sqrt (gridStep s t K n) • Sizes.seqXmat sz n (ω (k + 1)) := by
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [← Complex.coe_smul]
  unfold pathH
  rw [hins, Finset.sum_insert (by simp), smul_add]
  abel


/-- `Ψ` along the walk is `filt sz k`-measurable: `Ψ` agrees with the `C²` function `Ψ ∘ P` at
every Hermitian point, and the walk is Hermitian (RBM1D `integrable_Phi_H`,
`Gauss/GridStepDecomp.lean:548`, for the measurability half). -/
private theorem StepDecomp_measurable_phi_filt {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΨ : HermTestFun sz n Ψ) (k : ℕ) :
    Measurable[filt sz k] fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω) := by
  have hcont := (StepDecomp_contDiff_comp hΨ.contDiffAt).continuous
  have heq : (fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω))
      = fun ω => Ψ (StepDecomp_hermCLM _ (pathH sz s t K n k ω)) := funext fun ω => by
    rw [StepDecomp_hermCLM_of_isHermitian (pathH_isHermitian sz s t K n k ω)]
  rw [heq]
  exact hcont.measurable.comp (pathH_measurable_filt sz s t K n k)

/-- `Ψ` along the walk is integrable: measurable and bounded by (H2) (RBM1D `integrable_Phi_H`,
`Gauss/GridStepDecomp.lean:548`). -/
private theorem StepDecomp_integrable_phi {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΨ : HermTestFun sz n Ψ) (k : ℕ) :
    Integrable (fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω)) (pathP sz) := by
  obtain ⟨C, hC⟩ := hΨ.bdd₀
  have hm : Measurable fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω) :=
    (StepDecomp_measurable_phi_filt sz s t K n hΨ k).mono ((filt sz).le k) le_rfl
  exact (memLp_top_of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ (pathH_isHermitian sz s t K n k ω))).integrable le_top

/-- A real-valued-on-Hermitian function has a real derivative along a Hermitian direction
(RBM1D `fderiv_im_eq_zero_of_herm`, `Gauss/GridStepDecomp.lean:406`; (H1) replaces `TestFun`). -/
private theorem StepDecomp_fderiv_im_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M X : Matrix ι ι ℂ} (hd : DifferentiableAt ℝ Ψ M)
    (hReal : ∀ A, A.IsHermitian → (Ψ A).im = 0) (hM : M.IsHermitian) (hX : X.IsHermitian) :
    (fderiv ℝ Ψ M X).im = 0 := by
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (StepDecomp_hasDerivAt_add_smul M X 0)
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  have hpath0 : ∀ t' : ℝ, (Ψ (M + t' • X)).im = 0 := fun t' =>
    hReal _ (StepDecomp_isHermitian_add_smul hM hX t')
  have him0 : HasDerivAt (fun t' : ℝ => (Ψ (M + t' • X)).im) ((fderiv ℝ Ψ M X).im) 0 := by
    have h1 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) Complex.imCLM.hasFDerivAt hp0
    simpa [Function.comp_def] using h1
  have hconst : (fun t' : ℝ => (Ψ (M + t' • X)).im) = fun _ : ℝ => (0 : ℝ) := funext hpath0
  rw [hconst] at him0
  exact him0.unique (hasDerivAt_const 0 0)

/-- `Ab` is `filt sz j`-measurable (RBM1D `measurable_Ab`, `Gauss/GridStepDecomp.lean:463`): `gradMat`
of a member of the Hermitian class is a continuous function of the Hermitian walk, through the
Hermitian projection. -/
private theorem StepDecomp_measurable_Ab (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    Measurable[filt sz j] (fun ω : PathΩ sz => Ab sz s t K n j Φ U b ω) := by
  have hgrad : ∀ a, Measurable[filt sz j] (fun ω : PathΩ sz => gradMat (Φ a) (pathH sz s t K n j ω)) := by
    intro a
    have hcont := StepDecomp_continuous_gradMat (StepDecomp_contDiff_comp (hΦ a).contDiffAt)
    have heq : (fun ω : PathΩ sz => gradMat (Φ a) (pathH sz s t K n j ω))
        = fun ω => gradMat (fun M' => Φ a (StepDecomp_hermCLM _ M')) (pathH sz s t K n j ω) :=
      funext fun ω => (StepDecomp_gradMat_comp (pathH_isHermitian sz s t K n j ω)
        (((hΦ a).contDiffAt _ (pathH_isHermitian sz s t K n j ω)).differentiableAt
          (by norm_num))).symm
    rw [heq]
    exact hcont.measurable.comp (pathH_measurable_filt sz s t K n j)
  exact Finset.measurable_sum _ fun a _ => (hgrad a).const_smul (U b a : ℂ)

/-- **`Rlabel`**: the per-label Taylor remainder of one grid step,
`Φ(H_{j+1}) - Φ(H_j) - √Δ · fderiv ℝ Φ (H_j) X_{j+1}` (RBM1D `Rlabel`, `Gauss/GridStepDecomp.lean:559`). -/
private def StepDecomp_Rlabel
    (Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (ω : PathΩ sz) : ℂ :=
  Ψ (pathH sz s t K n (j + 1) ω) - Ψ (pathH sz s t K n j ω)
    - Real.sqrt (gridStep s t K n) •
      fderiv ℝ Ψ (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1)))

/-- The pathwise Taylor remainder bound, from (H1) and the Hermitian-direction bound (H3) (RBM1D
`norm_Rlabel_le`, `Gauss/GridStepDecomp.lean:565`). -/
private theorem StepDecomp_norm_Rlabel_le
    {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΨ : HermTestFun sz n Ψ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Ψ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (ω : PathΩ sz) :
    ‖StepDecomp_Rlabel sz s t K n j Ψ ω‖
      ≤ (C₂ / 2) * gridStep s t K n * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 := by
  unfold StepDecomp_Rlabel
  rw [StepDecomp_pathH_succ]
  have hkey := StepDecomp_taylor hΨ.contDiffAt hC₂ (pathH_isHermitian sz s t K n j ω)
    (Sizes.seqXmat_isHermitian sz n (ω (j + 1))) (Real.sqrt_nonneg (gridStep s t K n))
  rwa [Real.sq_sqrt hΔ] at hkey

private theorem StepDecomp_measurable_Rlabel
    {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΨ : HermTestFun sz n Ψ) :
    Measurable (StepDecomp_Rlabel sz s t K n j Ψ) := by
  have h1 := (StepDecomp_measurable_phi_filt sz s t K n hΨ (j + 1)).mono ((filt sz).le (j + 1)) le_rfl
  have h2 := (StepDecomp_measurable_phi_filt sz s t K n hΨ j).mono ((filt sz).le j) le_rfl
  have hcont : Continuous fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
      × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      fderiv ℝ (fun M' => Ψ (StepDecomp_hermCLM _ M')) p.1 p.2 :=
    (((StepDecomp_contDiff_comp hΨ.contDiffAt).continuous_fderiv (by norm_num)).comp
      continuous_fst).clm_apply continuous_snd
  have h3 : Measurable fun ω : PathΩ sz =>
      fderiv ℝ Ψ (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))) := by
    have heq : (fun ω : PathΩ sz => fderiv ℝ Ψ (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))))
        = fun ω => fderiv ℝ (fun M' => Ψ (StepDecomp_hermCLM _ M')) (pathH sz s t K n j ω)
            (Sizes.seqXmat sz n (ω (j + 1))) := funext fun ω =>
      (StepDecomp_fderiv_comp (pathH_isHermitian sz s t K n j ω)
        ((hΨ.contDiffAt _ (pathH_isHermitian sz s t K n j ω)).differentiableAt (by norm_num))
        (Sizes.seqXmat_isHermitian sz n (ω (j + 1)))).symm
    rw [heq]
    exact hcont.measurable.comp
      ((StepDecomp_measurable_pathH sz s t K n j).prodMk (StepDecomp_measurable_seqXmat sz n (j + 1)))
  unfold StepDecomp_Rlabel
  simp only [Complex.real_smul]
  exact (h1.sub h2).sub (h3.const_mul _)

/-- **The pathwise bound on the `Ab`-weighted sum of Taylor remainders**: `O(Δ)` in `‖X_{j+1}‖²`
with the constant `(Σ_a |U(b,a)|)(C₂/2)` (RBM1D `norm_Rlabel_sum_le`, `Gauss/GridStepDecomp.lean:636`). -/
private theorem StepDecomp_norm_Rlabel_sum_le (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) :
    ‖∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω‖
      ≤ (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
        * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 := by
  calc ‖∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω‖
      ≤ ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
          ‖(U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω‖ := norm_sum_le _ _
    _ = ∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a| * ‖StepDecomp_Rlabel sz s t K n j (Φ a) ω‖ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [norm_mul, show ‖(U b a : ℂ)‖ = |U b a| from RCLike.norm_ofReal (U b a)]
    _ ≤ ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
          |U b a| * ((C₂ / 2) * gridStep s t K n * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left
          (StepDecomp_norm_Rlabel_le sz s t K n j (hΦ a) (hC₂ a) hΔ ω) (abs_nonneg _)
    _ = (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
          * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- The `Ab`-weighted sum of Taylor remainders is integrable (RBM1D `integrable_Rlabel_sum`,
`Gauss/GridStepDecomp.lean:660`): measurable and dominated by a
multiple of the integrable `‖X_{j+1}‖²`. -/
private theorem StepDecomp_integrable_Rlabel_sum (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    Integrable (fun ω : PathΩ sz => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
      (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω) (pathP sz) := by
  have hmeas : Measurable fun ω : PathΩ sz => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
      (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω :=
    Finset.measurable_sum _ fun a _ => (StepDecomp_measurable_Rlabel sz s t K n j (hΦ a)).const_mul _
  have hgint : Integrable (fun ω : PathΩ sz =>
      (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
        * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2) (pathP sz) :=
    (integrable_normSq_incr sz n j).const_mul _
  exact hgint.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => StepDecomp_norm_Rlabel_sum_le sz s t K n j hΦ hC₂ hΔ U b ω)

/-- `linTr` is real-linear in its direction argument, specialised to the `Ab` combination
(RBM1D `lin_Ab_eq_sum`, `Gauss/GridStepDecomp.lean:484`). -/
private theorem StepDecomp_lin_Ab_eq_sum
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n (Ab sz s t K n j Φ U b ω) X
      = ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
          U b a * linTr n (gradMat (Φ a) (pathH sz s t K n j ω)) X := by
  unfold linTr Ab
  rw [Matrix.sum_mul, Matrix.trace_sum]
  have hstep : ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      Matrix.trace ((U b a : ℂ) • gradMat (Φ a) (pathH sz s t K n j ω) * X)
        = (U b a : ℂ) * Matrix.trace (gradMat (Φ a) (pathH sz s t K n j ω) * X) := by
    intro a
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a _ => hstep a, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **The key algebraic bridge** (RBM1D `sum_fderiv_eq_stepZ`, `Gauss/GridStepDecomp.lean:504`): the `Ab`-weighted
first-order term is exactly `stepZ`, because each `Φ a` is real on Hermitian matrices and `U` is
real. -/
private theorem StepDecomp_sum_fderiv_eq_stepZ (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) :
    (Real.sqrt (gridStep s t K n) : ℂ) *
      (∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) *
        fderiv ℝ (Φ a) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))))
      = (stepZ sz s t K n j Φ U b ω : ℂ) := by
  have hHherm := pathH_isHermitian sz s t K n j ω
  have hXherm := Sizes.seqXmat_isHermitian sz n (ω (j + 1))
  have hterm : ∀ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) *
      fderiv ℝ (Φ a) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1)))
      = ((U b a * linTr n (gradMat (Φ a) (pathH sz s t K n j ω))
          (Sizes.seqXmat sz n (ω (j + 1))) : ℝ) : ℂ) := by
    intro a
    have h1 := StepDecomp_fderiv_im_eq_zero
      ((hΦ a).contDiffAt _ hHherm |>.differentiableAt (by norm_num)) (hReal a) hHherm hXherm
    have h2 := lin_eq_fderiv sz n (Ψ := Φ a) (pathH sz s t K n j ω) hXherm
    have h3 : fderiv ℝ (Φ a) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1)))
        = ((linTr n (gradMat (Φ a) (pathH sz s t K n j ω))
            (Sizes.seqXmat sz n (ω (j + 1))) : ℝ) : ℂ) :=
      Complex.ext (by simpa using h2) (by simpa using h1)
    rw [h3]; push_cast; ring
  simp only [hterm]
  rw [← Complex.ofReal_sum, ← StepDecomp_lin_Ab_eq_sum sz s t K n j U b ω
    (Sizes.seqXmat sz n (ω (j + 1)))]
  unfold stepZ
  push_cast
  ring

/-- `Z`, as a complex function, has conditional mean zero (RBM1D `condExp_stepZ_eq_zero`,
`Gauss/GridStepDecomp.lean:679`): the merged real-valued `condExp_linear_eq_zero`, lifted along `ℝ ↪ ℂ`. -/
private theorem StepDecomp_condExp_stepZ_eq_zero (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (hIntReal : Integrable (stepZ sz s t K n j Φ U b) (pathP sz)) :
    (pathP sz)[fun ω => (stepZ sz s t K n j Φ U b ω : ℂ) | filt sz j]
      =ᵐ[pathP sz] fun _ => (0 : ℂ) := by
  have hreal : (pathP sz)[stepZ sz s t K n j Φ U b | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K n j (StepDecomp_measurable_Ab sz s t K n j hΦ U b)
      Set.univ MeasurableSet.univ (show Integrable
        (fun ω => Real.sqrt (gridStep s t K n) *
          linTr n (Ab sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1)))) (pathP sz) from hIntReal)
    rw [Set.indicator_univ] at h
    unfold stepZ
    exact h
  have hlift := ContinuousLinearMap.comp_condExp_comm (μ := pathP sz) (m := filt sz j)
    hIntReal Complex.ofRealCLM
  have hlift' : (fun ω => (((pathP sz)[stepZ sz s t K n j Φ U b | filt sz j]) ω : ℂ))
      =ᵐ[pathP sz] (pathP sz)[fun ω => (stepZ sz s t K n j Φ U b ω : ℂ) | filt sz j] := by
    simpa [Function.comp_def] using hlift
  refine hlift'.symm.trans ?_
  filter_upwards [hreal] with ω hω
  simp [hω]

/-- **The pointwise identity** (RBM1D `g_eq_pointwise`, `Gauss/GridStepDecomp.lean:703`): `Σ_a U(b,a) Φ_a(H_{j+1})`
splits into the `F_j`-measurable term, `stepZ`, and the weighted Taylor remainder. -/
private theorem StepDecomp_g_eq_pointwise (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) :
    (∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω))
      = (∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * Φ a (pathH sz s t K n j ω))
        + (stepZ sz s t K n j Φ U b ω : ℂ)
        + ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω := by
  have hZ := StepDecomp_sum_fderiv_eq_stepZ sz s t K n j hΦ hReal U b ω
  have hexpand : ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω)
        = (U b a : ℂ) * Φ a (pathH sz s t K n j ω)
          + (Real.sqrt (gridStep s t K n) : ℂ) * ((U b a : ℂ) *
              fderiv ℝ (Φ a) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))))
          + (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω := by
    intro a
    have hR : StepDecomp_Rlabel sz s t K n j (Φ a) ω
        = Φ a (pathH sz s t K n (j + 1) ω) - Φ a (pathH sz s t K n j ω)
          - (Real.sqrt (gridStep s t K n) : ℂ) *
            fderiv ℝ (Φ a) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))) := by
      unfold StepDecomp_Rlabel; rw [Complex.real_smul]
    rw [hR]; ring
  rw [Finset.sum_congr rfl fun a _ => hexpand a, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hZ]

/-- `h0 := Σ_a U(b,a)·Φ_a(H_jω)` is `filt sz j`-measurable (RBM1D `measurable_h0`,
`Gauss/GridStepDecomp.lean:729`). -/
private theorem StepDecomp_measurable_h0
    (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    Measurable[filt sz j]
      (fun ω : PathΩ sz => ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * Φ a (pathH sz s t K n j ω)) := by
  exact Finset.measurable_sum _ fun a _ =>
    (StepDecomp_measurable_phi_filt sz s t K n (hΦ a) j).const_mul (U b a : ℂ)

/-- `h0` is integrable: it is a finite sum of bounded functions (RBM1D `integrable_h0`,
`Gauss/GridStepDecomp.lean:740`). -/
private theorem StepDecomp_integrable_h0
    (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    Integrable
      (fun ω : PathΩ sz => ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * Φ a (pathH sz s t K n j ω)) (pathP sz) :=
  integrable_finsetSum _ fun a _ =>
    (StepDecomp_integrable_phi sz s t K n (hΦ a) j).const_mul (U b a : ℂ)

/-- `Z`, cast to `ℂ`, is integrable (the real cast of an integrable real function; RBM1D
`integrable_stepZ_complex`, `Gauss/GridStepDecomp.lean:749`). -/
private theorem StepDecomp_integrable_stepZ_complex
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (hIntReal : Integrable (stepZ sz s t K n j Φ U b) (pathP sz)) :
    Integrable (fun ω => (stepZ sz s t K n j Φ U b ω : ℂ)) (pathP sz) :=
  hIntReal.ofReal

/-- **The a.e. identity behind `stepDecomp`** (RBM1D `stepXi_eq_ae`, `Gauss/GridStepDecomp.lean:758`).  `ξ b` agrees
a.e. with `Z b` plus the `Ab`-weighted Taylor-remainder martingale difference. -/
private theorem StepDecomp_stepXi_eq_ae
    (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (hIntReal : Integrable (stepZ sz s t K n j Φ U b) (pathP sz)) :
    stepXi sz s t K n j Φ U b
      =ᵐ[pathP sz] fun ω => (stepZ sz s t K n j Φ U b ω : ℂ)
        + ((∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω)
          - (pathP sz)[fun ω' => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
              (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω' | filt sz j] ω) := by
  set h0 : PathΩ sz → ℂ :=
    fun ω => ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * Φ a (pathH sz s t K n j ω) with hh0def
  set R : PathΩ sz → ℂ :=
    fun ω => ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω with hRdef
  set Zc : PathΩ sz → ℂ := fun ω => (stepZ sz s t K n j Φ U b ω : ℂ) with hZcdef
  set g : PathΩ sz → ℂ :=
    fun ω => ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω) with hgdef
  have hgeq : g = h0 + Zc + R := funext fun ω => StepDecomp_g_eq_pointwise sz s t K n j hΦ hReal U b ω
  have hh0meas := StepDecomp_measurable_h0 sz s t K n j hΦ U b
  have hh0int := StepDecomp_integrable_h0 sz s t K n j hΦ U b
  have hZcint := StepDecomp_integrable_stepZ_complex sz s t K n j U b hIntReal
  have hRint := StepDecomp_integrable_Rlabel_sum sz s t K n j hΦ hC₂ hΔ U b
  have hcondg : (pathP sz)[g | filt sz j]
      =ᵐ[pathP sz] (pathP sz)[h0 | filt sz j] + (pathP sz)[Zc | filt sz j] + (pathP sz)[R | filt sz j] := by
    rw [hgeq]
    exact (condExp_add (hh0int.add hZcint) hRint (filt sz j)).trans
      ((condExp_add hh0int hZcint (filt sz j)).add (EventuallyEq.refl _ _))
  have hh0cond : (pathP sz)[h0 | filt sz j] =ᵐ[pathP sz] h0 := by
    rw [condExp_of_stronglyMeasurable ((filt sz).le j) hh0meas.stronglyMeasurable hh0int]
  have hZccond : (pathP sz)[Zc | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) :=
    StepDecomp_condExp_stepZ_eq_zero sz s t K n j hΦ U b hIntReal
  have hstepXi : stepXi sz s t K n j Φ U b = fun ω => g ω - (pathP sz)[g | filt sz j] ω := rfl
  rw [hstepXi]
  filter_upwards [hcondg, hh0cond, hZccond] with ω hω1 hω2 hω3
  have hω1' : (pathP sz)[g | filt sz j] ω = h0 ω + (pathP sz)[R | filt sz j] ω := by
    rw [hω1]; simp only [Pi.add_apply, hω2, hω3, add_zero]
  rw [hω1']
  have hgω : g ω = h0 ω + Zc ω + R ω := by rw [hgeq]; rfl
  rw [hgω]
  ring

/-- **`stepY` a.e. equals the `Ab`-weighted Taylor remainder minus its own conditional mean**
(RBM1D `stepY_eq_ae`, `Gauss/GridStepDecomp.lean:802`).
Immediate from `stepXi_eq_ae` and `stepY := stepXi - Z` (pointwise). -/
private theorem StepDecomp_stepY_eq_ae
    (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (hIntReal : Integrable (stepZ sz s t K n j Φ U b) (pathP sz)) :
    stepY sz s t K n j Φ U b
      =ᵐ[pathP sz] fun ω => (∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω)
        - (pathP sz)[fun ω' => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
            (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω' | filt sz j] ω := by
  have hXi := StepDecomp_stepXi_eq_ae sz s t K n j hΦ hReal hC₂ hΔ U b hIntReal
  filter_upwards [hXi] with ω hω
  change stepXi sz s t K n j Φ U b ω - (stepZ sz s t K n j Φ U b ω : ℂ) = _
  rw [hω]; ring

/-- **The pathwise bound on `Y`, a.e.** (RBM1D `stepY_norm_le_ae`, `Gauss/GridStepDecomp.lean:823`).
`‖Y b ω‖ ≤ C₂'·Δ·‖X(ω(j+1))‖² + (its conditional
mean)`, with the explicit constant `C₂' := (Σ_a |U(b,a)|)·(C₂/2)`. -/
private theorem StepDecomp_stepY_norm_le_ae
    (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (hIntReal : Integrable (stepZ sz s t K n j Φ U b) (pathP sz)) :
    ∀ᵐ ω ∂(pathP sz), ‖stepY sz s t K n j Φ U b ω‖
      ≤ (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
          * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2
        + (pathP sz)[fun ω' => (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
            * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω := by
  have hY := StepDecomp_stepY_eq_ae sz s t K n j hΦ hReal hC₂ hΔ U b hIntReal
  set R : PathΩ sz → ℂ :=
    fun ω => ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω with hRdef
  set g : PathΩ sz → ℝ := fun ω => (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
      * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 with hgdef
  have hRnorm : ∀ ω, ‖R ω‖ ≤ g ω := fun ω => StepDecomp_norm_Rlabel_sum_le sz s t K n j hΦ hC₂ hΔ U b ω
  have hgint : Integrable g (pathP sz) := (integrable_normSq_incr sz n j).const_mul _
  have hRint : Integrable R (pathP sz) := StepDecomp_integrable_Rlabel_sum sz s t K n j hΦ hC₂ hΔ U b
  have hcondRmono : (pathP sz)[fun ω => ‖R ω‖ | filt sz j] ≤ᵐ[pathP sz] (pathP sz)[g | filt sz j] :=
    condExp_mono hRint.norm hgint (Filter.Eventually.of_forall hRnorm)
  have hnormcond : (fun x => ‖(pathP sz)[R | filt sz j] x‖) ≤ᵐ[pathP sz] (pathP sz)[fun x => ‖R x‖ | filt sz j] :=
    _root_.norm_condExp_le R
  filter_upwards [hY, hcondRmono, hnormcond] with ω hω h2 h3
  rw [hω]
  calc ‖R ω - (pathP sz)[R | filt sz j] ω‖
      ≤ ‖R ω‖ + ‖(pathP sz)[R | filt sz j] ω‖ := norm_sub_le _ _
    _ ≤ g ω + (pathP sz)[g | filt sz j] ω := add_le_add (hRnorm ω) (le_trans h3 h2)

/-- **`stepDecomp`: the one-step decomposition of a loop observable** (RBM1D `stepDecomp`,
`Gauss/GridStepDecomp.lean:860`, commit `86573b9`; the class change is `HermTestFun` and the
Hermitian-direction bound `hC₂`).  (i) `ξ_b = Z_b + Y_b` pointwise; (ii) `Ab` is
`filt sz j`-measurable; (iii) a.e., `‖Y_b‖ ≤ g + E[g | F_j]` with
`g = (Σ_a |U(b,a)|) ((C₂/2) Δ) ‖X_{j+1}‖²`; (iv) `E[Y_b | F_j] = 0`. -/
theorem stepDecomp {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (hIntReal : Integrable (stepZ sz s t K n j Φ U b) (pathP sz)) :
    (∀ ω, stepXi sz s t K n j Φ U b ω
        = (stepZ sz s t K n j Φ U b ω : ℂ) + stepY sz s t K n j Φ U b ω)
      ∧ Measurable[filt sz j] (fun ω => Ab sz s t K n j Φ U b ω)
      ∧ (∀ᵐ ω ∂(pathP sz), ‖stepY sz s t K n j Φ U b ω‖
          ≤ (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
              * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2
            + (pathP sz)[fun ω' => (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
                * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω)
      ∧ (pathP sz)[stepY sz s t K n j Φ U b | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) :=
  ⟨fun ω => by unfold stepY; ring, StepDecomp_measurable_Ab sz s t K n j hΦ U b,
    StepDecomp_stepY_norm_le_ae sz s t K n j hΦ hReal hC₂ hΔ U b hIntReal,
    by
      have hY := StepDecomp_stepY_eq_ae sz s t K n j hΦ hReal hC₂ hΔ U b hIntReal
      have hRint := StepDecomp_integrable_Rlabel_sum sz s t K n j hΦ hC₂ hΔ U b
      have hcond : (pathP sz)[fun ω => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
          (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω
            - (pathP sz)[fun ω' => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
                (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω' | filt sz j] ω | filt sz j]
          =ᵐ[pathP sz] fun _ => (0 : ℂ) := by
        set R : PathΩ sz → ℂ :=
          fun ω => ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω with hRdef
        have hsub := condExp_sub hRint (integrable_condExp (f := R) (m := filt sz j)) (filt sz j)
        have hidem : (pathP sz)[(pathP sz)[R | filt sz j] | filt sz j] =ᵐ[pathP sz] (pathP sz)[R | filt sz j] :=
          condExp_condExp_of_le (le_refl (filt sz j)) ((filt sz).le j)
        have hfe : (fun ω => ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * StepDecomp_Rlabel sz s t K n j (Φ a) ω
            - (pathP sz)[R | filt sz j] ω) = R - (pathP sz)[R | filt sz j] := by
          funext ω
          change R ω - (pathP sz)[R | filt sz j] ω = (R - (pathP sz)[R | filt sz j]) ω
          rw [Pi.sub_apply]
        rw [hfe]
        filter_upwards [hsub, hidem] with ω hω1 hω2
        rw [hω1]
        simp only [Pi.sub_apply]
        rw [hω2]
        ring
      exact (condExp_congr_ae hY).trans hcond⟩

/-- **`stepDecomp_Y_sq`: the `L²` bound on `Y`** (RBM1D `stepDecomp_Y_sq`, `Gauss/GridStepDecomp.lean:914`):
`∫ ‖Y_b‖² ≤ 4 ((Σ_a |U(b,a)|) C₂/2)² Δ² ∫ ‖X_{j+1}‖⁴`.  From (iii) of `stepDecomp`,
`(x+y)² ≤ 2x²+2y²`, conditional Jensen at `x ↦ x²` (`ConvexOn.map_condExp_le_univ`) and the
tower property (`integral_condExp`). -/
theorem stepDecomp_Y_sq {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (hIntReal : Integrable (stepZ sz s t K n j Φ U b) (pathP sz)) :
    ∫ ω, ‖stepY sz s t K n j Φ U b ω‖ ^ 2 ∂(pathP sz)
      ≤ 4 * ((∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
          * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) := by
  have hYbound := StepDecomp_stepY_norm_le_ae sz s t K n j hΦ hReal hC₂ hΔ U b hIntReal
  set g : PathΩ sz → ℝ := fun ω => (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
      * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 with hgdef
  -- the key algebraic identity behind `g²`, in the exact grouping the target constant needs
  have heqg2 : (fun ω => (g ω) ^ 2)
      = fun ω => (((∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2)
        * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 := by
    rw [hgdef]; funext ω; ring
  have hgint : Integrable g (pathP sz) := by
    rw [hgdef]
    exact (integrable_normSq_incr sz n j).const_mul
      ((∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n))
  have hg2int : Integrable (fun ω => (g ω) ^ 2) (pathP sz) := by
    rw [heqg2]
    exact (integrable_normPow4_incr sz n j).const_mul
      (((∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2)
  have hg2eq : ∫ ω, (g ω) ^ 2 ∂(pathP sz)
      = ((∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
          * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) := by
    rw [heqg2, integral_const_mul]
  -- the conditional Jensen inequality at the convex map `x ↦ x²`
  have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow even_two
  have hcont : LowerSemicontinuous (fun x : ℝ => x ^ 2) := (continuous_pow 2).lowerSemicontinuous
  have hJensen : (fun ω => ((pathP sz)[g | filt sz j] ω) ^ 2)
      ≤ᵐ[pathP sz] (pathP sz)[fun ω => (g ω) ^ 2 | filt sz j] :=
    hcvx.map_condExp_le_univ ((filt sz).le j) hcont hgint hg2int
  -- combine the pathwise bound with `(x+y)² ≤ 2x²+2y²` and the Jensen bound
  have hcomb : ∀ᵐ ω ∂(pathP sz), ‖stepY sz s t K n j Φ U b ω‖ ^ 2
      ≤ 2 * (g ω) ^ 2 + 2 * (pathP sz)[fun ω' => (g ω') ^ 2 | filt sz j] ω := by
    filter_upwards [hYbound, hJensen] with ω h1 h2
    have hsq : ‖stepY sz s t K n j Φ U b ω‖ ^ 2
        ≤ (g ω + (pathP sz)[g | filt sz j] ω) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [hsq, h2, sq_nonneg (g ω - (pathP sz)[g | filt sz j] ω)]
  have hRHSint : Integrable (fun ω => 2 * (g ω) ^ 2
      + 2 * (pathP sz)[fun ω' => (g ω') ^ 2 | filt sz j] ω) (pathP sz) :=
    (hg2int.const_mul 2).add (Integrable.const_mul integrable_condExp 2)
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    hRHSint hcomb
  rw [integral_add (hg2int.const_mul 2) (Integrable.const_mul integrable_condExp 2),
    integral_const_mul, integral_const_mul, integral_condExp ((filt sz).le j), hg2eq] at hmono
  have hgoal : (2 : ℝ) * (((∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * (C₂ / 2)) ^ 2
        * (gridStep s t K n) ^ 2 * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz))
      + 2 * (((∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * (C₂ / 2)) ^ 2
        * (gridStep s t K n) ^ 2 * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz))
      = 4 * ((∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
        * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) := by ring
  linarith [hmono, hgoal]

/-- **`stepDecomp_Z_subG`: `Z_b` is conditionally sub-Gaussian** (RBM1D `stepDecomp_Z_subG`,
`Gauss/GridStepDecomp.lean:982`): on a `filt sz j`-event `E` where `Δ · linTrVar (Ab ω) ≤ c`, the merged
`hasCondSubgaussianMGF_linear` applied to `A := Ab`, since `stepZ` is exactly
`√Δ · linTr n (Ab ω) X_{j+1}`. -/
theorem stepDecomp_Z_subG {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (E : Set (PathΩ sz)) (hE : MeasurableSet[filt sz j] E) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ ω ∈ E, gridStep s t K n * linTrVar n (Ab sz s t K n j Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
      (fun ω => E.indicator (fun ω => stepZ sz s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP sz) := by
  have h := hasCondSubgaussianMGF_linear (sz := sz) s t K n j (StepDecomp_measurable_Ab sz s t K n j hΦ U b) E hE c hc
    hbound
  simpa only [stepZ] using h

/-- **Extra public lemma (T2076e, no hypothesis added):** `hIntReal` is a consequence of the other
hypotheses of `stepDecomp`: `Z` is `Σ_a U Φ_a(H_{j+1}) - Σ_a U Φ_a(H_j) - Σ_a U R_a`, a difference
of integrable functions (bounded and measurable by (H1)-(H2); `R` by (H3)). -/
theorem stepDecomp_integrable_stepZ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    Integrable (stepZ sz s t K n j Φ U b) (pathP sz) := by
  have hg : Integrable (fun ω : PathΩ sz => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
      (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω)) (pathP sz) :=
    integrable_finsetSum _ fun a _ =>
      (StepDecomp_integrable_phi sz s t K n (hΦ a) (j + 1)).const_mul (U b a : ℂ)
  have hZc : Integrable (fun ω : PathΩ sz => (stepZ sz s t K n j Φ U b ω : ℂ)) (pathP sz) := by
    have h := (hg.sub (StepDecomp_integrable_h0 sz s t K n j hΦ U b)).sub
      (StepDecomp_integrable_Rlabel_sum sz s t K n j hΦ hC₂ hΔ U b)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    rw [StepDecomp_g_eq_pointwise sz s t K n j hΦ hReal U b ω]
    ring
  have h := hZc.re
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp

end StepDecomp

/-! ### 6. Compile check: `stepDecomp` and `stepDecomp_Z_subG` on `A ↦ sin (Re tr A)`

`A ↦ Re tr A` (the amendment's example) violates (H2) (it is unbounded on the Hermitian
matrices `t • 1`), so the elementary member used is its bounded sibling `A ↦ sin (Re tr A)`,
which satisfies (H1)-(H3) with `C₀ = 1` and `C₂ = ‖Re tr‖²`, is real, and has the nonzero
gradient matrix `cos (Re tr M) • 1`. -/

section Check

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuous real-linear functional `Re tr`. -/
private def StepDecomp_g (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (Matrix.trace A).re
      map_add' := fun A B => by simp
      map_smul' := fun r A => by simp }

private theorem StepDecomp_g_apply (A : Matrix ι ι ℂ) :
    StepDecomp_g ι A = (Matrix.trace A).re := rfl

private theorem StepDecomp_check_hasFDerivAt (M : Matrix ι ι ℂ) :
    HasFDerivAt (fun A : Matrix ι ι ℂ => (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ))
      (Complex.ofRealCLM.comp (Real.cos (StepDecomp_g ι M) • StepDecomp_g ι)) M :=
  Complex.ofRealCLM.hasFDerivAt.comp M ((StepDecomp_g ι).hasFDerivAt.sin)

private theorem StepDecomp_check_fderiv :
    fderiv ℝ (fun A : Matrix ι ι ℂ => (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ))
      = fun M => Real.cos (StepDecomp_g ι M) • Complex.ofRealCLM.comp (StepDecomp_g ι) := by
  funext M
  rw [(StepDecomp_check_hasFDerivAt M).fderiv, ContinuousLinearMap.comp_smul]

private theorem StepDecomp_check_fderiv_apply (M B : Matrix ι ι ℂ) :
    fderiv ℝ (fun A : Matrix ι ι ℂ => (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) M B
      = ((Real.cos (StepDecomp_g ι M) * StepDecomp_g ι B : ℝ) : ℂ) := by
  rw [StepDecomp_check_fderiv]
  simp

private theorem StepDecomp_check_fderiv2 (M y : Matrix ι ι ℂ) :
    fderiv ℝ (fderiv ℝ fun A : Matrix ι ι ℂ => (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) M y y
      = ((-Real.sin (StepDecomp_g ι M) * StepDecomp_g ι y * StepDecomp_g ι y : ℝ) : ℂ) := by
  rw [StepDecomp_check_fderiv]
  have h : HasFDerivAt (fun M : Matrix ι ι ℂ =>
      Real.cos (StepDecomp_g ι M) • Complex.ofRealCLM.comp (StepDecomp_g ι))
      ((-Real.sin (StepDecomp_g ι M) • StepDecomp_g ι).smulRight
        (Complex.ofRealCLM.comp (StepDecomp_g ι))) M :=
    ((StepDecomp_g ι).hasFDerivAt.cos).smul_const (Complex.ofRealCLM.comp (StepDecomp_g ι))
  rw [h.fderiv]
  simp


private theorem StepDecomp_check_gradMat (M : Matrix ι ι ℂ) :
    gradMat (fun A : Matrix ι ι ℂ => (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) M
      = ((Real.cos (StepDecomp_g ι M) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  ext i j
  simp only [gradMat, Matrix.of_apply, StepDecomp_check_fderiv_apply, Matrix.smul_apply,
    Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [StepDecomp_g_apply, Matrix.trace_single_eq_same]
  · simp [hij, StepDecomp_g_apply, Matrix.trace_single_eq_of_ne _ _ _ hij,
      Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hij)]

end Check

section CheckMain

/-- The elementary family `Φ_a = sin (Re tr)` (the same function for every label `a`). -/
private def StepDecomp_checkΦ {d : ℕ} (sz : Sizes d) (n : ℕ) :
    Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun _ A => (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)

/-- The real kernel `U = 1` on the diagonal. -/
private def StepDecomp_diag {d : ℕ} (sz : Sizes d) (n : ℕ) : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ :=
  fun b a => if a = b then 1 else 0

private theorem StepDecomp_check_class {d : ℕ} (sz : Sizes d) (n : ℕ) (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    HermTestFun sz n (StepDecomp_checkΦ sz n a) where
  contDiffAt M _ := (Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_sin.comp (StepDecomp_g (Idx d (sz.L n) (sz.W n))).contDiff)).contDiffAt
  bdd₀ := ⟨1, fun M _ => by
    change ‖(((Real.sin (Matrix.trace M).re : ℝ)) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _⟩

private theorem StepDecomp_check_hC₂ {d : ℕ} (sz : Sizes d) (n : ℕ) (a : Zd d (sz.L n) × Zd d (sz.L n))
    (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    ‖fderiv ℝ (fderiv ℝ (StepDecomp_checkΦ sz n a)) M y y‖
      ≤ ‖StepDecomp_g (Idx d (sz.L n) (sz.W n))‖ ^ 2 * ‖y‖ ^ 2 := by
  have h1 : |StepDecomp_g (Idx d (sz.L n) (sz.W n)) y|
      ≤ ‖StepDecomp_g (Idx d (sz.L n) (sz.W n))‖ * ‖y‖ := by
    simpa [Real.norm_eq_abs] using (StepDecomp_g (Idx d (sz.L n) (sz.W n))).le_opNorm y
  have h2 := StepDecomp_check_fderiv2 M y
  change ‖fderiv ℝ (fderiv ℝ fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
    (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) M y y‖ ≤ _
  rw [h2, Complex.norm_real, Real.norm_eq_abs]
  set g := StepDecomp_g (Idx d (sz.L n) (sz.W n)) y
  calc |-Real.sin (StepDecomp_g (Idx d (sz.L n) (sz.W n)) M) * g * g|
      = |Real.sin (StepDecomp_g (Idx d (sz.L n) (sz.W n)) M)| * (|g| * |g|) := by
        rw [abs_mul, abs_mul, abs_neg]; ring
    _ ≤ 1 * (|g| * |g|) := by gcongr; exact Real.abs_sin_le_one _
    _ ≤ (‖StepDecomp_g (Idx d (sz.L n) (sz.W n))‖ * ‖y‖) * (‖StepDecomp_g (Idx d (sz.L n) (sz.W n))‖ * ‖y‖) := by
        rw [one_mul]; gcongr
    _ = ‖StepDecomp_g (Idx d (sz.L n) (sz.W n))‖ ^ 2 * ‖y‖ ^ 2 := by ring

/-- `stepDecomp` on the elementary family `sin (Re tr)` with `U = 1` on the diagonal: the
hypotheses `hΦ`, `hReal`, `hC₂` (with `C₂ = ‖Re tr‖²`), `hΔ` and `hIntReal` (from
`stepDecomp_integrable_stepZ`) are satisfied at once, for every size, grid and step. -/
theorem StepDecomp_check_stepDecomp {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hΔ : 0 ≤ gridStep s t K n) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    (∀ ω, stepXi sz s t K n j (StepDecomp_checkΦ sz n) (StepDecomp_diag sz n) b ω
        = (stepZ sz s t K n j (StepDecomp_checkΦ sz n) (StepDecomp_diag sz n) b ω : ℂ)
          + stepY sz s t K n j (StepDecomp_checkΦ sz n) (StepDecomp_diag sz n) b ω)
      ∧ Measurable[filt sz j]
          (fun ω => Ab sz s t K n j (StepDecomp_checkΦ sz n) (StepDecomp_diag sz n) b ω)
      ∧ (∀ᵐ ω ∂(pathP sz),
          ‖stepY sz s t K n j (StepDecomp_checkΦ sz n) (StepDecomp_diag sz n) b ω‖
            ≤ (∑ a : Zd d (sz.L n) × Zd d (sz.L n),
                  |StepDecomp_diag sz n b a|)
                * ((‖StepDecomp_g (Idx d (sz.L n) (sz.W n))‖ ^ 2 / 2) * gridStep s t K n)
                * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2
              + (pathP sz)[fun ω' => (∑ a : Zd d (sz.L n) × Zd d (sz.L n),
                  |StepDecomp_diag sz n b a|)
                    * ((‖StepDecomp_g (Idx d (sz.L n) (sz.W n))‖ ^ 2 / 2) * gridStep s t K n)
                    * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω)
      ∧ (pathP sz)[stepY sz s t K n j (StepDecomp_checkΦ sz n)
            (StepDecomp_diag sz n) b | filt sz j]
          =ᵐ[pathP sz] fun _ => (0 : ℂ) := by
  have hΦ := StepDecomp_check_class sz n
  have hReal : ∀ a (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), A.IsHermitian →
      (StepDecomp_checkΦ sz n a A).im = 0 := fun a A _ => Complex.ofReal_im _
  have hC : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ (StepDecomp_checkΦ sz n a)) M y y‖
        ≤ ‖StepDecomp_g (Idx d (sz.L n) (sz.W n))‖ ^ 2 * ‖y‖ ^ 2 :=
    fun a M y _ _ => StepDecomp_check_hC₂ sz n a M y
  exact stepDecomp sz s t K n j hΦ hReal hC hΔ _ b
    (stepDecomp_integrable_stepZ sz s t K n j hΦ hReal hC hΔ _ b)


private theorem StepDecomp_linTrVar_smul {d : ℕ} (sz : Sizes d) (n : ℕ) (r : ℝ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTrVar n ((r : ℂ) • A) = r ^ 2 * linTrVar n A := by
  unfold linTrVar RBM.Gauss.LinearForm.linVar
  have hlin : ∀ X, linTr n ((r : ℂ) • A) X = r * linTr n A X := by
    intro X
    unfold linTr
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  simp only [hlin, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- `stepDecomp_Z_subG` on the same family, `E = univ`, `c = Δ · linTrVar n 1`:
`Ab ω = cos (Re tr H_j ω) • 1`, so `Δ · linTrVar (Ab ω) = cos² · Δ · linTrVar 1 ≤ c`. -/
theorem StepDecomp_check_Z_subG {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hΔ : 0 ≤ gridStep s t K n) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
      (fun ω => (Set.univ : Set (PathΩ sz)).indicator (fun ω =>
        stepZ sz s t K n j (StepDecomp_checkΦ sz n) (StepDecomp_diag sz n) b ω) ω)
      ⟨gridStep s t K n * linTrVar n (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        mul_nonneg hΔ (linTrVar_nonneg n _)⟩ (pathP sz) := by
  refine stepDecomp_Z_subG sz s t K n j (StepDecomp_check_class sz n) _ b Set.univ MeasurableSet.univ
    _ (mul_nonneg hΔ (linTrVar_nonneg n _)) fun ω _ => ?_
  have hAb : Ab sz s t K n j (StepDecomp_checkΦ sz n) (StepDecomp_diag sz n) b ω
      = ((Real.cos (StepDecomp_g (Idx d (sz.L n) (sz.W n)) (pathH sz s t K n j ω)) : ℝ) : ℂ)
          • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
    have hg : ∀ (a : Zd d (sz.L n) × Zd d (sz.L n)) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        gradMat (StepDecomp_checkΦ sz n a) M
          = ((Real.cos (StepDecomp_g (Idx d (sz.L n) (sz.W n)) M) : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) :=
      fun a M => StepDecomp_check_gradMat M
    unfold Ab
    simp only [hg, smul_smul, ← Finset.sum_smul]
    congr 1
    simp only [← Finset.sum_mul, ← Complex.ofReal_sum]
    simp [StepDecomp_diag]
  rw [hAb, StepDecomp_linTrVar_smul]
  refine mul_le_mul_of_nonneg_left ?_ hΔ
  calc _ ≤ 1 * linTrVar n (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
        gcongr
        · exact linTrVar_nonneg n _
        · exact (sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _)
    _ = _ := one_mul _

section Instances

open RBM.Gauss.SizesInst

/-- The hypotheses of `stepDecomp` at the merged instance `sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`,
`N = 2097152`): `Φ_a = sin (Re tr)` for every label, `U = 1` on the diagonal, `C₂ = ‖Re tr‖²`, grid
`s = 1/4`, `t = 3/4`, `K = 2` (`Δ = 1/4`), step `j = 0`, label `b = 0`: `stepDecomp` applies with
every hypothesis discharged; the gradient matrix is `cos (Re tr M) • 1` (`StepDecomp_check_gradMat`). -/
example :=
  stepDecomp sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
    (Φ := StepDecomp_checkΦ sz0 0) (StepDecomp_check_class sz0 0)
    (fun a A _ => Complex.ofReal_im _)
    (C₂ := ‖StepDecomp_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2)
    (fun a M y _ _ => StepDecomp_check_hC₂ sz0 0 a M y) (by norm_num [gridStep])
    (StepDecomp_diag sz0 0) 0
    (stepDecomp_integrable_stepZ sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
      (StepDecomp_check_class sz0 0) (fun a A _ => Complex.ofReal_im _)
      (fun a M y _ _ => StepDecomp_check_hC₂ sz0 0 a M y) (by norm_num [gridStep])
      (StepDecomp_diag sz0 0) 0)

/-- `stepDecomp_Z_subG` at the same data, `E = univ`, `c = Δ · linTrVar 1`
(`c ≥ 0` by `linTrVar_nonneg`). -/
example :
    HasCondSubgaussianMGF (filt sz0 0) ((filt sz0).le 0)
      (fun ω => (Set.univ : Set (PathΩ sz0)).indicator (fun ω =>
        stepZ sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
          (StepDecomp_checkΦ sz0 0) (StepDecomp_diag sz0 0) 0 ω) ω)
      ⟨gridStep (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0
          * linTrVar 0 (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ),
        mul_nonneg (by norm_num [gridStep]) (linTrVar_nonneg 0 _)⟩ (pathP sz0) :=
  StepDecomp_check_Z_subG sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
    (by norm_num [gridStep]) 0

/-- `HermTestFun` and `gradMat` at `sz0`: the family `sin (Re tr)` is in the class, and its gradient
matrix at `M = 0` is `cos 0 • 1 = 1`, nonzero. -/
example : HermTestFun sz0 0 (StepDecomp_checkΦ sz0 0 0) := StepDecomp_check_class sz0 0 0

example :
    gradMat (StepDecomp_checkΦ sz0 0 0)
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
      = (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) := by
  have h : gradMat (StepDecomp_checkΦ sz0 0 0)
      (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
      = ((Real.cos (StepDecomp_g (Idx 3 (sz0.L 0) (sz0.W 0))
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) : ℝ) : ℂ)
        • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) :=
    StepDecomp_check_gradMat _
  rw [h]
  simp [StepDecomp_g_apply]

/-- The moment bounds at `sz0`. -/
example : ∫ ω : PathΩ sz0, ‖Sizes.seqXmat sz0 0 (ω (0 + 1))‖ ^ 2 ∂(pathP sz0)
    ≤ 16 * (sz0.size 0 : ℝ) ^ 4 := integral_normSq_incr_le sz0 0 0

example : ∫ ω : PathΩ sz0, ‖Sizes.seqXmat sz0 0 (ω (0 + 1))‖ ^ 4 ∂(pathP sz0)
    ≤ 768 * (sz0.size 0 : ℝ) ^ 8 := integral_normPow4_incr_le sz0 0 0

end Instances

end CheckMain

/-- **The amendment's example is not in the class.**  `A ↦ Re tr A` is `C²` and has vanishing second
derivative, but it is unbounded on the Hermitian matrices `t • 1`, so (H2) fails; this is why the
check above uses `sin (Re tr A)`.  (RBM2D `StepDecomp_check_trace_not_hermTestFun`,
`Path/StepDecomp.lean:1515`.) -/
theorem StepDecomp_check_trace_not_hermTestFun {d : ℕ} (sz : Sizes d) (n : ℕ) :
    ¬ HermTestFun sz n (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (((Matrix.trace A).re : ℝ) : ℂ)) := by
  intro h
  obtain ⟨C, hC⟩ := h.bdd₀
  have hM : (((|C| + 1 : ℝ) : ℂ) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (Complex.conj_ofReal _)
  have h1 := hC _ hM
  have hcard : (1 : ℝ) ≤ (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) :=
    Nat.one_le_cast.2 Fintype.card_pos
  rw [Complex.norm_real, Real.norm_eq_abs, Matrix.trace_smul, Matrix.trace_one] at h1
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, Complex.natCast_re, Complex.natCast_im, mul_zero] at h1
  rw [abs_of_nonneg (by positivity)] at h1
  nlinarith [abs_nonneg C, le_abs_self C]

end RBM.Path

end
