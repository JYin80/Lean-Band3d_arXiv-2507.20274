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

/-! ### 3. The second-order Taylor remainder along a Hermitian line -/

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

/-! ### 6. Compile check: `stepDecomp` and `stepDecomp_Z_subG` on `A ↦ sin (Re tr A)`

`A ↦ Re tr A` (the amendment's example) violates (H2) (it is unbounded on the Hermitian
matrices `t • 1`), so the elementary member used is its bounded sibling `A ↦ sin (Re tr A)`,
which satisfies (H1)-(H3) with `C₀ = 1` and `C₂ = ‖Re tr‖²`, is real, and has the nonzero
gradient matrix `cos (Re tr M) • 1`. -/

end RBM.Path

end
