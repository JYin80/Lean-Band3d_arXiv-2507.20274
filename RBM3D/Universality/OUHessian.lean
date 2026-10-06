/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Analytic.Constructions
import RBM3D.Universality.Pins
import RBM3D.Green.FlucVanish
import RBM3D.Induction.ConArgDet

/-!
# Pointwise Hessian structure for the centered-variance Green comparison (T2247, UN-16)

The deterministic, finite-dimensional second-variation calculation behind the `L₁` and `L₂`
kernels of `(EMCTE2)` (RBM2D paper `1-2:364–376`).  No OU path, expectation or time integral occurs,
and no pin is proved or stated.

Port of RBM2D `Universality/OUHessian.lean` (commit `c9a24cf`, 1242 lines; itself a port of RBM1D
`c06b103`, `RBM1D/Flow/OUComparisonHessian.lean`) to `Idx d L W`, `svarF d L W lam`,
`N = (W L)^d`, with these changes:

* `Idx L W` ↦ `Idx d L W`, `Coord L W` ↦ `CoordF d L W`,
  `RBM.Green.Bmat L W` ↦ `RBM.Green.Bmat d L W`,
  `usedCoords L W` ↦ `RBM.Gauss.usedCoords d L W`,
  `svar L W` ↦ `svarF d L W lam`
  (the new explicit argument `lam : ℝ` of `centeredVarianceEntry`, `paperL1Kernel`,
  `paperL2Kernel`);
* the merged `stieltjesN` is `Gres`-based: the RBM2D `rfl` unfoldings to `green` go through the
  private bridge `OUHessian_Gres_true` (as `InjSum_Gres_true`, `Universality/InjSum.lean:76`);
* RBM2D `Gauss.hasDerivAt_line`, `hasDerivAt_lineInverse`, `isHermitian_add_realSmul`
  (`RBM2D/Gauss/Envelope.lean:144, 151, 268`) have no public RBM3D twin and are copied privately;
  `Gauss.isUnit_sub_smul_one_of_im_ne_zero` ↦ `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`;
  `RBM.Gsig_conjTranspose` ↦ the private `OUHessian_green_conj`;
* `card_Idx_eq` ↦ the merged `RBM.Gauss.card_Idx`; `Scirc`, `gSel` ↦ the merged `scirc`, `Gres`;
  `paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t` need no `IsHermitian` hypothesis
  (`signedGreen_eq_Gres` holds for every `H`);
* the instances are at `d = 3`, `L = 3`, `W = 2` (`N = 216`), in `RBM.Univ.OUHessianInst`.

On the diagonal the imaginary direction `Bmat i i false` is not Hermitian and is never used.
-/

noncomputable section

-- The ported proofs keep their RBM1D simp sets; the style linters below only report unused
-- simp arguments / section variables / `<;>` there.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal
open scoped Matrix.Norms.L2Operator

/-! ### Private bridges and line helpers -/

section Helpers

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`
(as `InjSum_Gres_true`, `Universality/InjSum.lean:76`, private there). -/
private theorem OUHessian_Gres_true (H : Matrix n n ℂ) (z : ℂ) :
    RBM.Gauss.Gres H z true = RBM.green H z := by
  simp only [RBM.green, RBM.Gauss.Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- The `Gres`-based `stieltjesN` is `N⁻¹ tr (green)` (replaces the RBM2D `rfl` unfoldings). -/
private theorem OUHessian_stieltjesN_eq (M : Matrix n n ℂ) (z : ℂ) :
    stieltjesN M z = (Fintype.card n : ℂ)⁻¹ * (RBM.green M z).trace := by
  simp only [stieltjesN, OUHessian_Gres_true]

/-- `G(z̄) = G(z)^*` for Hermitian `H` (the conjugate bridge; template `lwWx_Gres_conjTranspose`,
`Graph/LWWeightExp.lean:115`, not imported). -/
private theorem OUHessian_green_conj {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) :
    RBM.green H ((starRingEnd ℂ) z) = (RBM.green H z)ᴴ := by
  have hH' : Hᴴ = H := hH
  simp only [RBM.green, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH', Complex.star_def]

/-- The affine line `s ↦ M + s • A` has derivative `A` (RBM2D `Gauss/Envelope.lean:144`). -/
private theorem OUHessian_hasDerivAt_line (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

/-- Along the line `t ↦ M + t • A`, the inverse has derivative `-R A R`
(RBM2D `Gauss/Envelope.lean:151`). -/
private theorem OUHessian_hasDerivAt_lineInverse {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A))
      (-(Ring.inverse (M + (t : ℂ) • A) * A * Ring.inverse (M + (t : ℂ) • A))) t := by
  set u : (Matrix n n ℂ)ˣ := (hU t).unit
  have hus : (u : Matrix n n ℂ) = M + (t : ℂ) • A := IsUnit.unit_spec _
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
      = Ring.inverse (M + (t : ℂ) • A) := by
    rw [← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹)
      (M + (t : ℂ) • A) := by
    rw [← hus]; exact hasFDerivAt_ringInverse u
  have hcomp := hF.comp_hasDerivAt t (OUHessian_hasDerivAt_line M A t)
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinv] using hcomp

omit [Fintype n] [DecidableEq n] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian
(RBM2D `Gauss/Envelope.lean:268`). -/
private theorem OUHessian_isHermitian_add_realSmul {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

end Helpers

/-! ### The coordinate directions (RBM1D `Gauss/Generator.lean:497–505, 916–945`) -/

section Directions

variable (d L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
/-- The real direction is symmetric in the pair: `Bmat j i true = Bmat i j true`
(RBM1D `Bmat_swap_true`, `Gauss/Generator.lean:916`). -/
theorem Bmat_swap_true (i j : Idx d L W) :
    RBM.Green.Bmat d L W j i true = RBM.Green.Bmat d L W i j true := by
  ext k l
  rw [RBM.Green.GreenDeriv_Bmat_apply, RBM.Green.GreenDeriv_Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_left h1]
    · rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]

omit [NeZero L] [NeZero W] in
/-- The imaginary direction is antisymmetric in the pair (off the diagonal):
`Bmat j i false = -Bmat i j false` (RBM1D `Bmat_swap_false`, `Gauss/Generator.lean:930`). -/
theorem Bmat_swap_false {i j : Idx d L W} (hij : i ≠ j) :
    RBM.Green.Bmat d L W j i false = -RBM.Green.Bmat d L W i j false := by
  ext k l
  change RBM.Green.Bmat d L W j i false k l = -(RBM.Green.Bmat d L W i j false k l)
  rw [RBM.Green.GreenDeriv_Bmat_apply, RBM.Green.GreenDeriv_Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · have h2 : ¬ (k = j ∧ l = i) := by
      rintro ⟨hkj, _⟩
      refine hij ?_
      rw [← h1.1]
      exact hkj
    rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1, neg_zero]

/-- Every direction `Bmat i j b` with `i ≠ j` or `b = true` is Hermitian (the redundant
`Bmat i i false = I • E_ii` is the one exception and is never read). -/
theorem Bmat_isHermitian_of_ne_or {i j : Idx d L W} {b : Bool} (h : i ≠ j ∨ b = true) :
    (RBM.Green.Bmat d L W i j b).IsHermitian := by
  by_cases hij : i = j
  · subst hij
    have hb : b = true := h.resolve_left (fun hne => hne rfl)
    subst hb
    exact RBM.Green.GreenDeriv_Bmat_isHermitian (c := (i, i, true))
      (RBM.Green.GreenDeriv_mem_usedCoords.2 (Or.inr ⟨rfl, rfl⟩))
  · rcases RBM.Gauss.idxKey_lt_or_eq_or_lt d L W i j with hlt | heq | hgt
    · exact RBM.Green.GreenDeriv_Bmat_isHermitian (c := (i, j, b))
        (RBM.Green.GreenDeriv_mem_usedCoords.2 (Or.inl hlt))
    · exact (hij heq).elim
    · have hmem : (j, i, b) ∈ usedCoords d L W :=
        RBM.Green.GreenDeriv_mem_usedCoords.2 (Or.inl hgt)
      have hji := RBM.Green.GreenDeriv_Bmat_isHermitian (c := (j, i, b)) hmem
      cases b
      · have hswap := Bmat_swap_false d L W hij
        have hneg : -RBM.Green.Bmat d L W j i false = RBM.Green.Bmat d L W i j false := by
          rw [hswap]
          simp
        rw [← hneg]
        exact hji.neg
      · rw [← Bmat_swap_true d L W i j]
        exact hji

end Directions

/-! ### Coordinate derivatives (RBM1D `Gauss/Generator.lean:592–599, 971–974`) -/

section CoordDeriv

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `∂_c Φ (M)`: the first directional derivative of `Φ` at `M` along the direction `Bmat c` of
the coordinate `c` (RBM1D `coordD1`, `Gauss/Generator.lean:592`). -/
def coordD1 (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (c : CoordF d L W) : ℂ :=
  fderiv ℝ Φ M (RBM.Green.Bmat d L W c.1 c.2.1 c.2.2)

/-- `∂_c ∂_c Φ (M)`: the second directional derivative of `Φ` at `M`, twice along `Bmat c`
(RBM1D `coordD2`, `Gauss/Generator.lean:597`). -/
def coordD2 (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (c : CoordF d L W) : ℂ :=
  fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat d L W c.1 c.2.1 c.2.2)
    (RBM.Green.Bmat d L W c.1 c.2.1 c.2.2)

/-- `∂_ij ∂_ji Φ` in the Wirtinger convention of the paper: for `i ≠ j`,
`∂_ij ∂_ji = (∂_a² + ∂_b²)/4` with `∂_a² ↔ (i, j, true)` and `∂_b² ↔ (i, j, false)`; on the
diagonal `∂_ii ∂_ii = ∂_a²` (RBM1D `wirtSecond`, `Gauss/Generator.lean:971`). -/
def wirtSecond (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (i j : Idx d L W) : ℂ :=
  if i = j then coordD2 d L W Φ M (i, i, true)
  else (1 / 4 : ℝ) • (coordD2 d L W Φ M (i, j, true) + coordD2 d L W Φ M (i, j, false))

end CoordDeriv

/-! ### The Hessian along a Hermitian line (RBM1D `Flow/OUComparisonHessian.lean`) -/

section ResolventVariation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordinary second derivative of a finite product separates into the single-factor Hessians
and the ordered cross-factor products (RBM1D `:30`). -/
theorem hasDerivAt_deriv_finset_product_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f fp : ι → ℝ → ℝ) (fpp : ι → ℝ)
    (hf : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t)
    (hfp : ∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => ∏ i ∈ s, f i u) t)
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, f j 0) * fpp i +
          (∑ j ∈ s.erase i,
            (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0) * fp i 0)) 0 := by
  have hfirst (t : ℝ) :
      HasDerivAt (fun u : ℝ => ∏ i ∈ s, f i u)
        (∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t) t := by
    have h := HasDerivAt.fun_finsetProd (u := s) (f := fun i u => f i u)
      (f' := fun i => fp i t) (fun i hi => hf i hi t)
    simpa [smul_eq_mul] using h
  have hderiv :
      (fun t : ℝ => deriv (fun u : ℝ => ∏ i ∈ s, f i u) t) =
        fun t => ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t := by
    funext t
    exact (hfirst t).deriv
  let p : ι → ℝ := fun i => ∏ j ∈ s.erase i, f j 0
  let dp : ι → ℝ := fun i =>
    ∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0
  have hprod (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun t : ℝ => ∏ j ∈ s.erase i, f j t) (dp i) 0 := by
    have h := HasDerivAt.fun_finsetProd (u := s.erase i) (f := fun j t => f j t)
      (f' := fun j => fp j 0) (fun j hj => hf j (Finset.mem_of_mem_erase hj) 0)
    simpa [dp, smul_eq_mul] using h
  have hterm (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun t : ℝ => (∏ j ∈ s.erase i, f j t) * fp i t)
        (dp i * fp i 0 + p i * fpp i) 0 := by
    have h := (hprod i hi).mul (hfp i hi)
    refine h.congr_deriv ?_
    simp [p, dp, add_comm, mul_comm, mul_left_comm, mul_assoc]
  have hsum₀ : HasDerivAt
      (fun t : ℝ => ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t)
      (∑ i ∈ s, (dp i * fp i 0 + p i * fpp i)) 0 := by
    have h := HasDerivAt.sum (u := s)
      (A := fun i t => (∏ j ∈ s.erase i, f j t) * fp i t)
      (A' := fun i => dp i * fp i 0 + p i * fpp i)
      (fun i hi => hterm i hi)
    have heq : (fun t : ℝ => ∑ i ∈ s,
        (∏ j ∈ s.erase i, f j t) * fp i t) =
        ∑ i ∈ s, fun t : ℝ => (∏ j ∈ s.erase i, f j t) * fp i t := by
      funext t
      simp
    rw [heq]
    exact h
  rw [hderiv]
  refine hsum₀.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro i hi
  simp [p, dp, add_comm, mul_comm, mul_left_comm, mul_assoc]

private theorem OUHessian_fderiv_fderiv_eq_lineSecond {H A : Matrix n n ℂ}
    {f : Matrix n n ℂ → ℂ} (hf : ContDiffAt ℝ 2 f H)
    (hline : ∀ t : ℝ, DifferentiableAt ℝ f (H + (t : ℂ) • A)) :
    fderiv ℝ (fderiv ℝ f) H A A =
      deriv (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) H := hf.fderiv_right (by norm_num)
  have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) H) H :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have happly := hfd'.clm_apply (hasFDerivAt_const (𝕜 := ℝ) A H)
  have hline0 := OUHessian_hasDerivAt_line H A 0
  have happly0 : HasFDerivAt (fun K => fderiv ℝ f K A)
      ((fderiv ℝ (fderiv ℝ f) H).flip A) (H + (0 : ℝ) • A) := by
    simpa using happly
  have hcomp := HasFDerivAt.comp_hasDerivAt 0 happly0 hline0
  have hcomp' : HasDerivAt
      (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A)
      (fderiv ℝ (fderiv ℝ f) H A A) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.flip_apply] using hcomp
  have hfirst (t : ℝ) : HasDerivAt
      (fun s : ℝ => f (H + (s : ℂ) • A))
      (fderiv ℝ f (H + (t : ℂ) • A) A) t := by
    exact (hline t).hasFDerivAt.comp_hasDerivAt t (OUHessian_hasDerivAt_line H A t)
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) =
      fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A := by
    funext t
    exact (hfirst t).deriv
  calc
    fderiv ℝ (fderiv ℝ f) H A A =
        deriv (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A) 0 := hcomp'.deriv.symm
    _ = deriv (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by rw [← hderiv]

private theorem OUHessian_deriv_deriv_ofRealCLM {g dg : ℝ → ℝ} {d2g : ℝ}
    (hg : ∀ t : ℝ, HasDerivAt g (dg t) t)
    (hdg : HasDerivAt dg d2g 0) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => (g s : ℂ)) t) 0 = (d2g : ℂ) := by
  have hfirst (t : ℝ) : HasDerivAt (fun s : ℝ => (g s : ℂ)) (dg t : ℂ) t := by
    have h := HasFDerivAt.comp_hasDerivAt t Complex.ofRealCLM.hasFDerivAt (hg t)
    simpa [Function.comp_def] using h
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => (g s : ℂ)) t) =
      fun t => (dg t : ℂ) := by
    funext t
    exact (hfirst t).deriv
  have hsecond := HasFDerivAt.comp_hasDerivAt 0 Complex.ofRealCLM.hasFDerivAt hdg
  rw [hderiv]
  exact hsecond.deriv

private noncomputable def OUHessian_traceCLM : Matrix n n ℂ →L[ℝ] ℂ :=
  (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap

private def OUHessian_entryMatrix (i j : n) : Matrix n n ℂ := Matrix.single i j 1

private theorem OUHessian_matrix_mul_entryMatrix_apply (X : Matrix n n ℂ) (i j a b : n) :
    (X * OUHessian_entryMatrix i j) a b = if b = j then X a i else 0 := by
  by_cases hb : b = j
  · subst b
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [OUHessian_entryMatrix]
    · intro x hx hxi
      simp [OUHessian_entryMatrix, hxi.symm]
    · simp
  · simp [OUHessian_entryMatrix, Matrix.mul_apply, Matrix.single_apply, hb, Ne.symm hb]

private theorem OUHessian_matrix_mul_entryMatrix_mul_apply (X Y : Matrix n n ℂ)
    (i j a b : n) :
    (X * OUHessian_entryMatrix i j * Y) a b = X a i * Y j b := by
  rw [Matrix.mul_apply]
  simp_rw [OUHessian_matrix_mul_entryMatrix_apply]
  simp

private theorem OUHessian_trace_green_entryCross (G : Matrix n n ℂ) (i j : n) :
    (G * OUHessian_entryMatrix i j * G * OUHessian_entryMatrix j i * G).trace =
      (G * G) i i * G j j := by
  calc
    (G * OUHessian_entryMatrix i j * G * OUHessian_entryMatrix j i * G).trace =
        ((G * OUHessian_entryMatrix i j * G) * (OUHessian_entryMatrix j i * G)).trace := by
      simp [mul_assoc]
    _ = ((OUHessian_entryMatrix j i * G) * (G * OUHessian_entryMatrix i j * G)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (OUHessian_entryMatrix j i * (G * G * OUHessian_entryMatrix i j * G)).trace := by
      simp [mul_assoc]
    _ = (G * G * OUHessian_entryMatrix i j * G) i j := by
      simpa [OUHessian_entryMatrix] using
        (Matrix.trace_single_mul j i (1 : ℂ) (G * G * OUHessian_entryMatrix i j * G))
    _ = (G * G) i i * G j j :=
      OUHessian_matrix_mul_entryMatrix_mul_apply (G * G) G i j i j

private theorem OUHessian_trace_green_singleEntry (G : Matrix n n ℂ) (a b : n) :
    (G * OUHessian_entryMatrix a b * G).trace = (G * G) b a := by
  calc
    (G * OUHessian_entryMatrix a b * G).trace =
        (G * (OUHessian_entryMatrix a b * G)).trace := by
      congr 1
      simp [Matrix.mul_assoc]
    _ = ((OUHessian_entryMatrix a b * G) * G).trace := Matrix.trace_mul_comm _ _
    _ = (OUHessian_entryMatrix a b * (G * G)).trace := by
      congr 1 <;> simp [Matrix.mul_assoc]
    _ = (G * G) b a := by
      simpa [OUHessian_entryMatrix] using Matrix.trace_single_mul a b (1 : ℂ) (G * G)

private theorem OUHessian_trace_green_entryPair (G : Matrix n n ℂ) (i j : n) :
    (G * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) * G).trace =
      (G * G) j i + (G * G) i j := by
  calc
    (G * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) * G).trace =
        (G * OUHessian_entryMatrix i j * G + G * OUHessian_entryMatrix j i * G).trace := by
      congr 1 <;> simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = (G * OUHessian_entryMatrix i j * G).trace +
        (G * OUHessian_entryMatrix j i * G).trace :=
      Matrix.trace_add _ _
    _ = (G * G) j i + (G * G) i j := by
      rw [OUHessian_trace_green_singleEntry G i j, OUHessian_trace_green_singleEntry G j i]

private theorem OUHessian_trace_green_entryImagPair (G : Matrix n n ℂ) (i j : n) :
    (G * (Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i) *
        G).trace =
      Complex.I * ((G * G) j i - (G * G) i j) := by
  have hmul : G * (Complex.I • OUHessian_entryMatrix i j -
        Complex.I • OUHessian_entryMatrix j i) * G =
      Complex.I • (G * OUHessian_entryMatrix i j * G) -
        Complex.I • (G * OUHessian_entryMatrix j i * G) := by
    calc
      G * (Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i) * G =
          (Complex.I • (G * OUHessian_entryMatrix i j) -
            Complex.I • (G * OUHessian_entryMatrix j i)) * G := by
        simp [Matrix.mul_sub, Matrix.mul_smul]
      _ = Complex.I • (G * OUHessian_entryMatrix i j * G) -
          Complex.I • (G * OUHessian_entryMatrix j i * G) := by
        rw [Matrix.sub_mul, smul_mul_assoc, smul_mul_assoc]
  rw [hmul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    OUHessian_trace_green_singleEntry, OUHessian_trace_green_singleEntry]
  simp only [smul_eq_mul]
  ring

end ResolventVariation

section BmatEntry

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem OUHessian_Bmat_real_eq_entryMatrices {i j : Idx d L W} (hij : i ≠ j) :
    RBM.Green.Bmat d L W i j true = OUHessian_entryMatrix i j + OUHessian_entryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, h1, h2, h1', h2',
        and_comm]

private theorem OUHessian_Bmat_imag_eq_entryMatrices {i j : Idx d L W} (hij : i ≠ j) :
    RBM.Green.Bmat d L W i j false =
      Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, h1, h2, h1', h2',
        and_comm]

private theorem OUHessian_Bmat_diag_true_eq_entryMatrix (i : Idx d L W) :
    RBM.Green.Bmat d L W i i true = OUHessian_entryMatrix i i := by
  ext k l
  by_cases h : k = i ∧ l = i
  · rcases h with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply]
  · have h' : ¬ (i = k ∧ i = l) := by
      rintro ⟨hik, hil⟩
      exact h ⟨hik.symm, hil.symm⟩
    simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, h, h']

end BmatEntry

section ResolventVariation2

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem OUHessian_trace_green_Bmat_pair_sum {G : Matrix n n ℂ} {i j : n}
    (hij : i ≠ j) :
    (G * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) * G *
        (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) * G).trace +
      (G * (Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i) * G *
        (Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i) *
          G).trace =
      2 * ((G * G) i i * G j j + (G * G) j j * G i i) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp_rw [OUHessian_trace_green_entryCross]
  simp only [smul_eq_mul, Complex.I_mul_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem OUHessian_analyticAt_green_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => RBM.green K z) H := by
  let q : Matrix n n ℂ → Matrix n n ℂ := fun K => K - z • (1 : Matrix n n ℂ)
  have hq : AnalyticAt ℝ q H := by
    exact analyticAt_id.sub analyticAt_const
  have hU : IsUnit (q H) := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  let u : (Matrix n n ℂ)ˣ := hU.unit
  have hu : (u : Matrix n n ℂ) = q H := IsUnit.unit_spec _
  have hinv : AnalyticAt ℝ Ring.inverse (q H) := by
    rw [← hu]
    exact analyticAt_inverse u
  have hc := hinv.comp hq
  convert hc using 1
  funext K
  simp [q, RBM.green, Matrix.nonsing_inv_eq_ringInverse]

private theorem OUHessian_hasFDerivAt_green_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt (fun K : Matrix n n ℂ => RBM.green K z)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (RBM.green H z) (RBM.green H z))
      H := by
  let q : Matrix n n ℂ → Matrix n n ℂ := fun K => K - z • (1 : Matrix n n ℂ)
  have hq : HasFDerivAt q (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) H := by
    simpa [q] using (hasFDerivAt_id H).sub_const (z • (1 : Matrix n n ℂ))
  have hU : IsUnit (q H) := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  let u : (Matrix n n ℂ)ˣ := hU.unit
  have hu : (u : Matrix n n ℂ) = q H := IsUnit.unit_spec _
  have hinv := (hasFDerivAt_ringInverse u).comp H hq
  have hinvval : (↑u⁻¹ : Matrix n n ℂ) = RBM.green H z := by
    calc
      (↑u⁻¹ : Matrix n n ℂ) = Ring.inverse (↑u : Matrix n n ℂ) :=
        (Ring.inverse_unit u).symm
      _ = Ring.inverse (q H) := by rw [hu]
      _ = RBM.green H z := by simp [q, RBM.green, Matrix.nonsing_inv_eq_ringInverse]
  convert hinv using 1
  · funext K
    simp [q, Function.comp_def, RBM.green, Matrix.nonsing_inv_eq_ringInverse]
  · rw [← hinvval]
    simp

private theorem OUHessian_analyticAt_stieltjes_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => stieltjesN K z) H := by
  have hg := OUHessian_analyticAt_green_matrix hH z hz
  have ht : AnalyticAt ℝ
      (fun K : Matrix n n ℂ => OUHessian_traceCLM (n := n) (RBM.green K z)) H := by
    have ht0 : AnalyticAt ℝ (fun A : Matrix n n ℂ => OUHessian_traceCLM (n := n) A)
        (RBM.green H z) :=
      (OUHessian_traceCLM (n := n)).analyticAt (RBM.green H z)
    have hcomp : AnalyticAt ℝ
        ((fun A : Matrix n n ℂ => OUHessian_traceCLM (n := n) A) ∘
          (fun K : Matrix n n ℂ => RBM.green K z)) H :=
      AnalyticAt.comp (g := fun A : Matrix n n ℂ => OUHessian_traceCLM (n := n) A)
        (f := fun K : Matrix n n ℂ => RBM.green K z) (x := H) ht0 hg
    simpa [Function.comp_def] using hcomp
  have hc : AnalyticAt ℝ (fun K : Matrix n n ℂ =>
      (Fintype.card n : ℂ)⁻¹ * OUHessian_traceCLM (n := n) (RBM.green K z)) H := by
    exact (analyticAt_const (x := H)).mul ht
  convert hc using 1
  funext K
  rw [OUHessian_stieltjesN_eq]
  rfl

private theorem OUHessian_hasFDerivAt_stieltjes_matrix {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt (fun K : Matrix n n ℂ => stieltjesN K z)
      (((Fintype.card n : ℂ)⁻¹) •
        (OUHessian_traceCLM (n := n) ∘L
          (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (RBM.green H z)
            (RBM.green H z)))) H := by
  have hgreen := OUHessian_hasFDerivAt_green_matrix hH z hz
  have htrace := (OUHessian_traceCLM (n := n)).hasFDerivAt.comp H hgreen
  have hst := htrace.const_mul ((Fintype.card n : ℂ)⁻¹)
  have hEq : (fun K : Matrix n n ℂ => stieltjesN K z)
      = fun K => (Fintype.card n : ℂ)⁻¹ * OUHessian_traceCLM (n := n) (RBM.green K z) := by
    funext K
    rw [OUHessian_stieltjesN_eq]
    rfl
  rw [hEq]
  simpa [ContinuousLinearMap.comp_apply, Function.comp_def] using hst

private theorem OUHessian_fderiv_stieltjesIm_apply_matrix {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fun K : Matrix n n ℂ => (stieltjesN K z).im) H A =
      (-((Fintype.card n : ℂ)⁻¹) *
        (RBM.green H z * A * RBM.green H z).trace).im := by
  have h := (Complex.imCLM.hasFDerivAt.comp H
    (OUHessian_hasFDerivAt_stieltjes_matrix hH z hz)).fderiv
  have hA := congrArg (fun L : Matrix n n ℂ →L[ℝ] ℝ => L A) h
  calc
    fderiv ℝ (fun K : Matrix n n ℂ => (stieltjesN K z).im) H A =
        (fderiv ℝ (⇑Complex.imCLM ∘ fun K : Matrix n n ℂ => stieltjesN K z) H) A := rfl
    _ = (Complex.imCLM ∘SL
        ((Fintype.card n : ℂ)⁻¹ •
          OUHessian_traceCLM (n := n) ∘L
            (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (RBM.green H z)
              (RBM.green H z)))) A := hA
    _ = (-((Fintype.card n : ℂ)⁻¹) *
        (RBM.green H z * A * RBM.green H z).trace).im := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
        OUHessian_traceCLM, Matrix.traceLinearMap_apply, Complex.mul_im, mul_assoc]

private theorem OUHessian_analyticAt_stieltjesIm_matrix {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => (stieltjesN K z).im) H := by
  have hm := OUHessian_analyticAt_stieltjes_matrix hH z hz
  have hi0 : AnalyticAt ℝ (fun w : ℂ => Complex.imCLM w) (stieltjesN H z) :=
    Complex.imCLM.analyticAt (stieltjesN H z)
  have hi : AnalyticAt ℝ
      ((fun w : ℂ => Complex.imCLM w) ∘ (fun K : Matrix n n ℂ => stieltjesN K z)) H :=
    AnalyticAt.comp (g := fun w : ℂ => Complex.imCLM w)
      (f := fun K : Matrix n n ℂ => stieltjesN K z) (x := H) hi0 hm
  simpa [Function.comp_def] using hi

private theorem OUHessian_analyticAt_stieltjesImComplex_matrix {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => ((stieltjesN K z).im : ℂ)) H := by
  have hm := OUHessian_analyticAt_stieltjesIm_matrix hH z hz
  have ho : AnalyticAt ℝ (fun x : ℝ => Complex.ofRealCLM x)
      ((stieltjesN H z).im) := Complex.ofRealCLM.analyticAt _
  have hc : AnalyticAt ℝ
      ((fun x : ℝ => Complex.ofRealCLM x) ∘
        (fun K : Matrix n n ℂ => (stieltjesN K z).im)) H :=
    AnalyticAt.comp (g := fun x : ℝ => Complex.ofRealCLM x)
      (f := fun K : Matrix n n ℂ => (stieltjesN K z).im) (x := H) ho hm
  simpa [Function.comp_def] using hc

private theorem OUHessian_analyticAt_stieltjesImProduct_complex {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ =>
      ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H := by
  have hR : AnalyticAt ℝ
      (fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjesN K (z i)).im) H := by
    exact s.analyticAt_fun_prod
      (fun i hi => OUHessian_analyticAt_stieltjesIm_matrix hH (z i) (hz i hi))
  have hcast : AnalyticAt ℝ (fun x : ℝ => (x : ℂ))
      (∏ i ∈ s, (stieltjesN H (z i)).im) := Complex.ofRealCLM.analyticAt _
  have hcomp : AnalyticAt ℝ
      ((fun x : ℝ => (x : ℂ)) ∘
        (fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjesN K (z i)).im)) H :=
    AnalyticAt.comp (g := fun x : ℝ => (x : ℂ))
      (f := fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjesN K (z i)).im)
      (x := H) hcast hR
  simpa [Function.comp_def] using hcomp

private theorem OUHessian_fderiv_fderiv_stieltjesImComplex_eq_lineSecond
    {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ => ((stieltjesN K z).im : ℂ))) H A A =
      deriv (fun t : ℝ => deriv
        (fun s : ℝ => ((stieltjesN (H + (s : ℂ) • A) z).im : ℂ)) t) 0 := by
  let f : Matrix n n ℂ → ℂ := fun K => ((stieltjesN K z).im : ℂ)
  have hc : ContDiffAt ℝ 2 f H :=
    (OUHessian_analyticAt_stieltjesImComplex_matrix hH z hz).contDiffAt
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) H := hc.fderiv_right (by norm_num)
  have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) H) H :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have happly := hfd'.clm_apply (hasFDerivAt_const (𝕜 := ℝ) A H)
  have hline := OUHessian_hasDerivAt_line H A 0
  have happly0 : HasFDerivAt (fun K => fderiv ℝ f K A)
      ((fderiv ℝ (fderiv ℝ f) H).flip A) (H + (0 : ℝ) • A) := by
    simpa using happly
  have hcomp := HasFDerivAt.comp_hasDerivAt 0 happly0 hline
  have hcomp' : HasDerivAt
      (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A)
      (fderiv ℝ (fderiv ℝ f) H A A) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.flip_apply] using hcomp
  have hfirst (t : ℝ) : HasDerivAt
      (fun s : ℝ => f (H + (s : ℂ) • A))
      (fderiv ℝ f (H + (t : ℂ) • A) A) t := by
    have hHt := OUHessian_isHermitian_add_realSmul hH hA t
    exact (OUHessian_analyticAt_stieltjesImComplex_matrix hHt z hz).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt t (OUHessian_hasDerivAt_line H A t)
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) =
      fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A := by
    funext t
    exact (hfirst t).deriv
  change fderiv ℝ (fderiv ℝ f) H A A = _
  calc
    fderiv ℝ (fderiv ℝ f) H A A =
        deriv (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A) 0 := hcomp'.deriv.symm
    _ = deriv (fun t : ℝ => deriv
        (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by rw [← hderiv]

/-- The resolvent along a Hermitian real line has the usual first variation (RBM1D `:461`). -/
theorem hasDerivAt_green_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z)
      (-(RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z)) t := by
  have hU : ∀ s : ℝ, IsUnit (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    intro s
    have hsum : H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A
        = (H + (s : ℂ) • A) - z • (1 : Matrix n n ℂ) := by abel
    rw [hsum]
    exact RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero (OUHessian_isHermitian_add_realSmul hH hA s) hz
  have hEq : (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z)
      = fun s : ℝ => Ring.inverse (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    funext s
    change (H + (s : ℂ) • A - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hEq_t := congrFun hEq t
  have hline := OUHessian_hasDerivAt_lineInverse hU t
  rw [← hEq_t] at hline
  rw [hEq]
  exact hline

/-- The first derivative of the paper-normalized Stieltjes transform along a Hermitian line
(RBM1D `:485`, `stieltjes` ↦ `stieltjesN`). -/
theorem hasDerivAt_stieltjesN_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => stieltjesN (H + (s : ℂ) • A) z)
      (-((Fintype.card n : ℂ)⁻¹) *
        (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z).trace) t := by
  have hG := hasDerivAt_green_hermitianLine hH hA z hz t
  have htrace := HasFDerivAt.comp_hasDerivAt t
    (OUHessian_traceCLM (n := n)).hasFDerivAt hG
  have hmul := (htrace.const_mul ((Fintype.card n : ℂ)⁻¹))
  have hst : (fun s : ℝ => stieltjesN (H + (s : ℂ) • A) z)
      = fun s : ℝ => (Fintype.card n : ℂ)⁻¹ *
          OUHessian_traceCLM (n := n) (RBM.green (H + (s : ℂ) • A) z) := by
    funext s
    rw [OUHessian_stieltjesN_eq]
    rfl
  rw [hst]
  simpa [OUHessian_traceCLM, Matrix.traceLinearMap_apply] using hmul

/-- Along a Hermitian line, the derivative of the first Stieltjes variation is the usual
resolvent second variation (RBM1D `:502`). -/
theorem hasDerivAt_stieltjesFirstVariation {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => -((Fintype.card n : ℂ)⁻¹) *
        (RBM.green (H + (s : ℂ) • A) z * A * RBM.green (H + (s : ℂ) • A) z).trace)
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z * A *
          RBM.green (H + (t : ℂ) • A) z).trace) t := by
  have hG := hasDerivAt_green_hermitianLine hH hA z hz t
  set R := RBM.green (H + (t : ℂ) • A) z
  have hRA := hG.mul_const A
  have hRARA := hRA.mul hG
  have hfun : ((fun s : ℝ => RBM.green (H + (s : ℂ) • A) z * A) *
      (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z)) =
      (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z *
        (A * RBM.green (H + (s : ℂ) • A) z)) := by
    funext s
    simp [Pi.mul_apply, Matrix.mul_assoc]
  have hprod : HasDerivAt
      (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z *
        (A * RBM.green (H + (s : ℂ) • A) z))
      ((-(R * A * R) * A) * R + (R * A) * (-(R * A * R))) t := by
    rw [← hfun]
    simpa [R, Matrix.mul_assoc] using hRARA
  have htr := HasFDerivAt.comp_hasDerivAt t
    (OUHessian_traceCLM (n := n)).hasFDerivAt hprod
  have hconst := htr.const_mul (-((Fintype.card n : ℂ)⁻¹))
  convert hconst using 1 <;>
    simp [OUHessian_traceCLM, Matrix.traceLinearMap_apply, Matrix.mul_assoc] <;> ring

/-- The real Stieltjes factor along a Hermitian matrix line (D1, RBM1D `:533`). -/
def stieltjesImAlong (H A : Matrix n n ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (RBM.Univ.stieltjesN (H + (t : ℂ) • A) z).im

/-- Its first derivative, written as the imaginary part of the resolvent first variation
(D2, RBM1D `:537`). -/
def stieltjesImLineFirst (H A : Matrix n n ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (-((Fintype.card n : ℂ)⁻¹) *
    (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z).trace).im

/-- Its second derivative at the base point, written as the resolvent second variation
(D3, RBM1D `:542`). -/
def stieltjesImLineSecond (H A : Matrix n n ℂ) (z : ℂ) : ℝ :=
  (2 * (Fintype.card n : ℂ)⁻¹ *
    (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im

/-- The finite-product second line variation, including all single and ordered cross terms
(D4, RBM1D `:547`). -/
def stieltjesImProductLineSecond {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (z : ι → ℂ) : ℝ :=
  ∑ i ∈ s,
    ((∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0) *
        stieltjesImLineSecond H A (z i) +
      (∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0) *
          stieltjesImLineFirst H A (z j) 0) *
        stieltjesImLineFirst H A (z i) 0)

/-- The Fréchet Hessian of a finite product of real Stieltjes factors along any Hermitian
direction has the single-factor and ordered cross-factor expansion (RBM1D `:559`). -/
theorem fderiv_fderiv_stieltjesImProduct_hermitianLine {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (hH : H.IsHermitian) (hA : A.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ =>
      ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H A A =
      ((stieltjesImProductLineSecond s H A z : ℝ) : ℂ) := by
  let F : Matrix n n ℂ → ℂ := fun K =>
    ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)
  let f : ι → ℝ → ℝ := fun i t => stieltjesImAlong H A (z i) t
  let fp : ι → ℝ → ℝ := fun i t => stieltjesImLineFirst H A (z i) t
  let fpp : ι → ℝ := fun i => stieltjesImLineSecond H A (z i)
  let g : ℝ → ℝ := fun t => ∏ i ∈ s, f i t
  let d2g : ℝ := ∑ i ∈ s,
    ((∏ j ∈ s.erase i, f j 0) * fpp i +
      (∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0) * fp i 0)
  have hC2 : ContDiffAt ℝ 2 F H :=
    (OUHessian_analyticAt_stieltjesImProduct_complex s hH z hz).contDiffAt
  have hline : ∀ t : ℝ, DifferentiableAt ℝ F (H + (t : ℂ) • A) := by
    intro t
    have htH := OUHessian_isHermitian_add_realSmul hH hA t
    exact (OUHessian_analyticAt_stieltjesImProduct_complex s htH z hz).differentiableAt
  have hbridge := OUHessian_fderiv_fderiv_eq_lineSecond hC2 hline
  have hf : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t := by
    intro i hi t
    have hst := hasDerivAt_stieltjesN_hermitianLine hH hA (z i) (hz i hi) t
    have him := HasFDerivAt.comp_hasDerivAt t Complex.imCLM.hasFDerivAt hst
    simpa [f, fp, stieltjesImAlong, stieltjesImLineFirst, Function.comp_def] using him
  have hfp : ∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0 := by
    intro i hi
    have hst := hasDerivAt_stieltjesFirstVariation hH hA (z i) (hz i hi) 0
    have him := HasFDerivAt.comp_hasDerivAt 0 Complex.imCLM.hasFDerivAt hst
    simpa [fp, fpp, stieltjesImLineFirst, stieltjesImLineSecond,
      Function.comp_def] using him
  have hfirst (t : ℝ) : HasDerivAt g
      (∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t) t := by
    have h := HasDerivAt.fun_finsetProd (u := s) (f := fun i u => f i u)
      (f' := fun i => fp i t) (fun i hi => hf i hi t)
    simpa [g, smul_eq_mul] using h
  have hg : ∀ t : ℝ, HasDerivAt g (deriv g t) t := by
    intro t
    have heq : deriv g t =
        ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t := (hfirst t).deriv
    exact (hfirst t).congr_deriv heq.symm
  have hsecond := hasDerivAt_deriv_finset_product_expansion s f fp fpp hf hfp
  have hsecond' : HasDerivAt (fun t => deriv g t) d2g 0 := by
    simpa [g, d2g, f, fp, fpp] using hsecond
  have hcast := OUHessian_deriv_deriv_ofRealCLM hg hsecond'
  have hlineEq : (fun t : ℝ => F (H + (t : ℂ) • A)) = fun t => (g t : ℂ) := by
    funext t
    rfl
  rw [hlineEq] at hbridge
  rw [hbridge]
  simpa [stieltjesImProductLineSecond, d2g, f, fp, fpp] using hcast

/-! ### The Wirtinger Hessian of a product of `Im m` factors (RBM1D `:621`) -/

end ResolventVariation2

section WirtingerHessian

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The Wirtinger Hessian of a finite product is the real-coordinate combination of the single
and cross resolvent variations (RBM1D `:621`; target 7). -/
theorem wirtSecond_stieltjesImProduct_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (hH : H.IsHermitian) (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0)
    (a b : Idx d L W) :
    wirtSecond d L W
        (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b =
      if a = b then
        (stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a a true) z : ℂ)
      else
        (1 / 4 : ℝ) •
          ((stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a b true) z : ℂ) +
            (stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a b false) z : ℂ)) := by
  by_cases hab : a = b
  · subst b
    simp only [wirtSecond, ↓reduceIte]
    have hA : (RBM.Green.Bmat d L W a a true).IsHermitian :=
      Bmat_isHermitian_of_ne_or d L W (Or.inr rfl)
    change fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ =>
      ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H
        (RBM.Green.Bmat d L W a a true) (RBM.Green.Bmat d L W a a true) = _
    rw [fderiv_fderiv_stieltjesImProduct_hermitianLine s H
      (RBM.Green.Bmat d L W a a true) hH hA z hz]
  · simp only [wirtSecond, ite_eq_right hab]
    have hT : (RBM.Green.Bmat d L W a b true).IsHermitian :=
      Bmat_isHermitian_of_ne_or d L W (Or.inl hab)
    have hF : (RBM.Green.Bmat d L W a b false).IsHermitian :=
      Bmat_isHermitian_of_ne_or d L W (Or.inl hab)
    change (1 / 4 : ℝ) •
      (fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ =>
        ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H
          (RBM.Green.Bmat d L W a b true) (RBM.Green.Bmat d L W a b true) +
       fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ =>
        ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H
          (RBM.Green.Bmat d L W a b false) (RBM.Green.Bmat d L W a b false)) = _
    rw [fderiv_fderiv_stieltjesImProduct_hermitianLine s H
          (RBM.Green.Bmat d L W a b true) hH hT z hz,
        fderiv_fderiv_stieltjesImProduct_hermitianLine s H
          (RBM.Green.Bmat d L W a b false) hH hF z hz]

end WirtingerHessian

section FirstWirtinger

variable (d L W : ℕ) [NeZero L] [NeZero W]

private theorem OUHessian_deriv_deriv_stieltjes_im_complex_hermitianLine
    {n : Type*} [Fintype n] [DecidableEq n] {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    deriv (fun t : ℝ => deriv
      (fun s : ℝ => ((stieltjesN (H + (s : ℂ) • A) z).im : ℂ)) t) 0 =
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im : ℂ) := by
  let fR : ℝ → ℝ := fun s => (stieltjesN (H + (s : ℂ) • A) z).im
  let fC : ℝ → ℂ := fun s => (fR s : ℂ)
  let dR : ℝ → ℝ := fun s => Complex.imCLM
    (-((Fintype.card n : ℂ)⁻¹) *
      (RBM.green (H + (s : ℂ) • A) z * A * RBM.green (H + (s : ℂ) • A) z).trace)
  have hfirstR (t : ℝ) : HasDerivAt fR (dR t) t := by
    have hs := hasDerivAt_stieltjesN_hermitianLine hH hA z hz t
    have hi := HasFDerivAt.comp_hasDerivAt t Complex.imCLM.hasFDerivAt hs
    simpa [Function.comp_def, fR, dR] using hi
  have hfirstC (t : ℝ) : HasDerivAt fC ((dR t : ℂ)) t := by
    have hc := HasFDerivAt.comp_hasDerivAt t Complex.ofRealCLM.hasFDerivAt (hfirstR t)
    simpa [Function.comp_def, fC] using hc
  have hderiv : (fun t : ℝ => deriv fC t) = fun t => (dR t : ℂ) := by
    funext t
    exact (hfirstC t).deriv
  have hsecond := hasDerivAt_stieltjesFirstVariation hH hA z hz 0
  have hsecondR : HasDerivAt dR
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im 0 := by
    have hi := HasFDerivAt.comp_hasDerivAt 0 Complex.imCLM.hasFDerivAt hsecond
    simpa [Function.comp_def, dR] using hi
  have hsecondC : HasDerivAt (fun s : ℝ => (dR s : ℂ))
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im : ℂ) 0 := by
    have hc := HasFDerivAt.comp_hasDerivAt 0 Complex.ofRealCLM.hasFDerivAt hsecondR
    simpa [Function.comp_def] using hc
  change deriv (fun t : ℝ => deriv fC t) 0 = _
  calc
    deriv (fun t : ℝ => deriv fC t) 0 = deriv (fun t : ℝ => (dR t : ℂ)) 0 := by
      rw [hderiv]
    _ = _ := hsecondC.deriv

private theorem OUHessian_fderiv_fderiv_stieltjes_imComplex_hermitianLine
    {n : Type*} [Fintype n] [DecidableEq n] {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ => ((stieltjesN K z).im : ℂ))) H A A =
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im : ℂ) := by
  rw [OUHessian_fderiv_fderiv_stieltjesImComplex_eq_lineSecond hH hA z hz]
  exact OUHessian_deriv_deriv_stieltjes_im_complex_hermitianLine hH hA z hz

/-- The first Wirtinger derivative of the real-valued observable `Im m`, expressed through the
real-coordinate derivatives along `Bmat` (D9, RBM1D `:709`). -/
def stieltjesImWirtingerFirst (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (i j : Idx d L W) : ℂ :=
  if i = j then
    (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
      (RBM.Green.Bmat d L W i i true) : ℝ)
  else
    (2⁻¹ : ℂ) *
      ((fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
          (RBM.Green.Bmat d L W i j true) : ℝ) -
        Complex.I *
          (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
            (RBM.Green.Bmat d L W i j false) : ℝ))

/-- The first Wirtinger derivative of `Im m` is the difference of two resolvent-square entries;
the conjugated entry is the corresponding entry of `G*²` for Hermitian `H` (RBM1D `:723`;
target 8). -/
theorem stieltjesImWirtingerFirst_entry_formula
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx d L W) :
    stieltjesImWirtingerFirst d L W H z i j =
      (Complex.I * (Fintype.card (Idx d L W) : ℂ)⁻¹ / 2) *
        ((RBM.green H z * RBM.green H z) j i -
          (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j)) := by
  by_cases hij : i = j
  · subst j
    rw [stieltjesImWirtingerFirst, ite_eq_left rfl, OUHessian_Bmat_diag_true_eq_entryMatrix]
    rw [OUHessian_fderiv_stieltjesIm_apply_matrix hH z hz]
    rw [OUHessian_trace_green_singleEntry]
    let c : ℂ := (Fintype.card (Idx d L W) : ℂ)⁻¹
    have hc : c.im = 0 := by simp only [c, Complex.inv_im, Complex.natCast_im, zero_div, neg_zero]
    change ((-c * (RBM.green H z * RBM.green H z) i i).im : ℂ) =
      (Complex.I * c / 2) * ((RBM.green H z * RBM.green H z) i i -
        (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i i))
    apply Complex.ext <;> simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, hc] <;> ring
  · rw [stieltjesImWirtingerFirst, ite_eq_right hij,
      OUHessian_Bmat_real_eq_entryMatrices hij, OUHessian_Bmat_imag_eq_entryMatrices hij]
    rw [OUHessian_fderiv_stieltjesIm_apply_matrix hH z hz,
      OUHessian_fderiv_stieltjesIm_apply_matrix hH z hz,
      OUHessian_trace_green_entryPair, OUHessian_trace_green_entryImagPair]
    let c : ℂ := (Fintype.card (Idx d L W) : ℂ)⁻¹
    have hc : c.im = 0 := by simp only [c, Complex.inv_im, Complex.natCast_im, zero_div, neg_zero]
    change (2⁻¹ : ℂ) *
      (((-c * ((RBM.green H z * RBM.green H z) j i +
          (RBM.green H z * RBM.green H z) i j)).im : ℂ) -
        Complex.I * ((-c * (Complex.I * ((RBM.green H z * RBM.green H z) j i -
          (RBM.green H z * RBM.green H z) i j))).im : ℂ)) =
      (Complex.I * c / 2) * ((RBM.green H z * RBM.green H z) j i -
        (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j))
    apply Complex.ext <;> simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, hc] <;> ring

private theorem OUHessian_green_square_conj_entry
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ)
    (i j : Idx d L W) :
    (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j) =
      (RBM.green H ((starRingEnd ℂ) z) * RBM.green H ((starRingEnd ℂ) z)) j i := by
  have hG : RBM.green H ((starRingEnd ℂ) z) = (RBM.green H z)ᴴ := by
    exact OUHessian_green_conj hH z
  calc
    (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j) =
        ((RBM.green H z * RBM.green H z)ᴴ) j i := by
      simp [Matrix.conjTranspose_apply, Complex.star_def]
    _ = ((RBM.green H z)ᴴ * (RBM.green H z)ᴴ) j i := by rw [Matrix.conjTranspose_mul]
    _ = (RBM.green H ((starRingEnd ℂ) z) * RBM.green H ((starRingEnd ℂ) z)) j i := by
      rw [← hG]

/-- The first derivative formula in the notation of (2.25), with the conjugate entry written as
the corresponding entry of the adjoint resolvent square (RBM1D `:809`; target 9). -/
theorem stieltjesImWirtingerFirst_adjoint_formula
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx d L W) :
    stieltjesImWirtingerFirst d L W H z i j =
      (Complex.I * (Fintype.card (Idx d L W) : ℂ)⁻¹ / 2) *
        ((RBM.green H z * RBM.green H z) j i -
          (RBM.green H ((starRingEnd ℂ) z) * RBM.green H ((starRingEnd ℂ) z)) j i) := by
  rw [stieltjesImWirtingerFirst_entry_formula d L W H hH z hz i j,
    OUHessian_green_square_conj_entry d L W hH z i j]

/-- The Wirtinger Hessian of one real Stieltjes factor has the exact entry formula that
underlies the paper's `L₁` contraction (RBM1D `:821`; target 10). -/
theorem wirtSecond_stieltjesIm_entry_formula
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx d L W) :
    wirtSecond d L W (fun K => ((stieltjesN K z).im : ℂ)) H i j =
      ((((Fintype.card (Idx d L W) : ℂ)⁻¹) *
        ((RBM.green H z * RBM.green H z) i i * (RBM.green H z) j j +
          (RBM.green H z * RBM.green H z) j j * (RBM.green H z) i i)).im : ℂ) := by
  by_cases hij : i = j
  · subst j
    have hdiag : (RBM.Green.Bmat d L W i i true).IsHermitian :=
      Bmat_isHermitian_of_ne_or d L W (Or.inr rfl)
    rw [wirtSecond, ite_eq_left rfl]
    change fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ =>
      ((stieltjesN K z).im : ℂ))) H (RBM.Green.Bmat d L W i i true)
        (RBM.Green.Bmat d L W i i true) = _
    rw [OUHessian_fderiv_fderiv_stieltjes_imComplex_hermitianLine hH hdiag z hz]
    rw [OUHessian_Bmat_diag_true_eq_entryMatrix, OUHessian_trace_green_entryCross]
    simp [Complex.mul_im, mul_assoc]
    ring
  · rw [wirtSecond, ite_eq_right hij]
    change (1 / 4 : ℝ) •
      (fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ =>
        ((stieltjesN K z).im : ℂ))) H (RBM.Green.Bmat d L W i j true)
          (RBM.Green.Bmat d L W i j true) +
       fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ =>
        ((stieltjesN K z).im : ℂ))) H (RBM.Green.Bmat d L W i j false)
          (RBM.Green.Bmat d L W i j false)) = _
    rw [OUHessian_fderiv_fderiv_stieltjes_imComplex_hermitianLine hH
          (Bmat_isHermitian_of_ne_or d L W (Or.inl hij)) z hz,
        OUHessian_fderiv_fderiv_stieltjes_imComplex_hermitianLine hH
          (Bmat_isHermitian_of_ne_or d L W (Or.inl hij)) z hz,
        OUHessian_Bmat_real_eq_entryMatrices hij, OUHessian_Bmat_imag_eq_entryMatrices hij]
    let c : ℂ := (Fintype.card (Idx d L W) : ℂ)⁻¹
    let T₁ := (RBM.green H z * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) *
      RBM.green H z * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) *
      RBM.green H z).trace
    let T₂ := (RBM.green H z * (Complex.I • OUHessian_entryMatrix i j -
        Complex.I • OUHessian_entryMatrix j i) *
      RBM.green H z * (Complex.I • OUHessian_entryMatrix i j -
        Complex.I • OUHessian_entryMatrix j i) *
      RBM.green H z).trace
    have hcIm : c.im = 0 := by simp only [c, Complex.inv_im, Complex.natCast_im, zero_div, neg_zero]
    have hIm : (2 * c * T₁).im + (2 * c * T₂).im = (2 * c * (T₁ + T₂)).im := by
      simp [Complex.mul_im, hcIm]
      ring
    have hImC : ((2 * c * T₁).im : ℂ) + ((2 * c * T₂).im : ℂ) =
        ((2 * c * (T₁ + T₂)).im : ℂ) := by
      exact_mod_cast hIm
    change (1 / 4 : ℝ) •
      (((2 * c * T₁).im : ℂ) + ((2 * c * T₂).im : ℂ)) = _
    rw [hImC]
    have hT : T₁ + T₂ = 2 * ((RBM.green H z * RBM.green H z) i i * (RBM.green H z) j j +
        (RBM.green H z * RBM.green H z) j j * (RBM.green H z) i i) := by
      dsimp [T₁, T₂]
      exact OUHessian_trace_green_Bmat_pair_sum hij
    rw [hT]
    simp [Complex.mul_im, hcIm, c]
    ring

end FirstWirtinger

/-! ### The signed resolvent family and the `L₁`, `L₂` kernels (RBM1D `:775–805`) -/

section Kernels

section SignedGreen

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The signed resolvent family `{G, G*}` (D5, RBM1D `:784`). -/
def signedGreen (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ :=
  if σ then RBM.green H z else RBM.green H ((starRingEnd ℂ) z)

/-- `signedGreen` is the merged `Gres` family for every `H` (both are the nonsingular inverse of
`H - z` resp. `H - z̄`; replaces RBM2D `signedGreen_eq_gSel`, which needed `H.IsHermitian`). -/
theorem signedGreen_eq_Gres (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) :
    signedGreen H z σ = RBM.Gauss.Gres H z σ := by
  cases σ <;> simp [signedGreen, RBM.Gauss.Gres, RBM.green, Matrix.nonsing_inv_eq_ringInverse]

end SignedGreen

section KernelDefs

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The centered covariance entry `S°_{ab} = S_{ab} - N⁻¹`, with `S = svarF d L W lam` and the matrix
dimension `N = card (Idx d L W)` (D10, RBM1D `:775`; `lam = sz.lam n` for the band model,
`K.lamV sz n` model-generic, `0` for block Anderson). -/
def centeredVarianceEntry (lam : ℝ) (a b : Idx d L W) : ℝ :=
  svarF d L W lam a b - (Fintype.card (Idx d L W) : ℝ)⁻¹

/-- The deterministic pointwise `L₁` kernel in (2.25) (D11, RBM1D `:788`). -/
def paperL1Kernel (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) : ℝ :=
  ∑ σ : Bool, ∑ τ : Bool,
    ‖(Fintype.card (Idx d L W) : ℂ)⁻¹ *
      ∑ a : Idx d L W, ∑ b : Idx d L W,
        ((signedGreen H z σ * signedGreen H z σ) a a) *
          (centeredVarianceEntry d L W lam a b : ℂ) * (signedGreen H z τ) b b‖

/-- The deterministic pointwise `L₂` kernel in (2.25), for two spectral parameters (D12,
RBM1D `:797`). -/
def paperL2Kernel (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) : ℝ :=
  ∑ σ : Bool, ∑ τ : Bool,
    ‖(Fintype.card (Idx d L W) : ℂ)⁻¹ *
      (Fintype.card (Idx d L W) : ℂ)⁻¹ *
      ∑ a : Idx d L W, ∑ b : Idx d L W,
        ((signedGreen H z₁ σ * signedGreen H z₁ σ) a b) *
          (centeredVarianceEntry d L W lam a b : ℂ) *
          ((signedGreen H z₂ τ * signedGreen H z₂ τ) b a)‖

/-- `S°` is symmetric (RBM1D `centeredVarianceEntry_symm`). -/
theorem centeredVarianceEntry_symm (lam : ℝ) (a b : Idx d L W) :
    centeredVarianceEntry d L W lam a b = centeredVarianceEntry d L W lam b a := by
  simp [centeredVarianceEntry, svarF_comm d L W lam a b]

/-- `S°` of this file is the merged `scirc` (`Universality/Pins.lean:612`) after the cast to `ℂ`. -/
theorem centeredVarianceEntry_cast (lam : ℝ) (a b : Idx d L W) :
    ((centeredVarianceEntry d L W lam a b : ℝ) : ℂ) = scirc d L W lam a b := by
  rw [centeredVarianceEntry, scirc, RBM.Gauss.card_Idx]
  push_cast
  rfl

/-- `paperL1Kernel` is the merged `L1t` (no Hermitian hypothesis). -/
theorem paperL1Kernel_eq_L1t (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) :
    paperL1Kernel d L W lam H z = L1t d L W lam H z := by
  simp only [paperL1Kernel, L1t, signedGreen_eq_Gres, centeredVarianceEntry_cast,
    RBM.Gauss.card_Idx, Nat.cast_pow]

/-- `paperL2Kernel` is the merged `L2t` (`L2t` writes `(N⁻¹)^2` where `paperL2Kernel` writes
`N⁻¹ * N⁻¹`). -/
theorem paperL2Kernel_eq_L2t (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) :
    paperL2Kernel d L W lam H z₁ z₂ = L2t d L W lam H z₁ z₂ := by
  simp only [paperL2Kernel, L2t, signedGreen_eq_Gres, centeredVarianceEntry_cast,
    RBM.Gauss.card_Idx, sq]

end KernelDefs

end Kernels

/-! ### Compiled nonempty instances (target 5)

`d = 3`, `L = 3`, `W = 2` (`N = 216`), `lam = 1/2`, `H = 1`, `z = I` (and `2 I`), the sites
`x0 = 0 ≠ x1 = Pi.single 0 1`; the product instance uses `s = univ : Finset (Fin 2)` and
`z = ![I, 2 I]`; the line instances are at `n = Fin 2`, `H = A = 1`, `t = 0`.  Every hypothesis is
discharged. -/

namespace OUHessianInst

/-- The site `0`. -/
def x0 : Idx 3 3 2 := 0

/-- The site `Pi.single 0 1`. -/
def x1 : Idx 3 3 2 := Pi.single 0 1

theorem x0_ne_x1 : x0 ≠ x1 := by
  intro h
  have h0 := congrFun h 0
  have h1 : (0 : ZMod 6) = 1 := by simpa [x0, x1] using h0
  exact absurd h1 (by decide)

/-- `inst_directions` . -/
theorem inst_directions :
  x0 ≠ x1 ∧
    RBM.Green.Bmat 3 3 2 x1 x0 true = RBM.Green.Bmat 3 3 2 x0 x1 true ∧
    RBM.Green.Bmat 3 3 2 x1 x0 false = -RBM.Green.Bmat 3 3 2 x0 x1 false ∧
    (RBM.Green.Bmat 3 3 2 x0 x1 false).IsHermitian ∧
    (RBM.Green.Bmat 3 3 2 x0 x0 true).IsHermitian :=
  ⟨x0_ne_x1, Bmat_swap_true 3 3 2 x0 x1, Bmat_swap_false 3 3 2 x0_ne_x1,
    Bmat_isHermitian_of_ne_or 3 3 2 (Or.inl x0_ne_x1),
    Bmat_isHermitian_of_ne_or 3 3 2 (Or.inr rfl)⟩

/-- `inst_entry` : `paperL1Kernel = L1t` and the Hessian entry formula at `(x0, x1)`. -/
theorem inst_entry :
  paperL1Kernel 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I =
      RBM.Univ.L1t 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I ∧
    wirtSecond 3 3 2 (fun K => ((RBM.Univ.stieltjesN K Complex.I).im : ℂ))
        (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) x0 x1 =
      ((((Fintype.card (Idx 3 3 2) : ℂ)⁻¹) *
        ((RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I *
            RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) x0 x0 *
          (RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) x1 x1 +
         (RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I *
            RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) x1 x1 *
          (RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) x0 x0)).im : ℂ) :=
  ⟨paperL1Kernel_eq_L1t 3 3 2 (1 / 2) 1 Complex.I,
    wirtSecond_stieltjesIm_entry_formula 3 3 2 1 Matrix.isHermitian_one Complex.I (by simp) x0 x1⟩

/-- `inst_product` : the Wirtinger Hessian of `Im m(I) · Im m(2I)`. -/
theorem inst_product :
  wirtSecond 3 3 2
      (fun K => ((∏ i ∈ (Finset.univ : Finset (Fin 2)),
        (RBM.Univ.stieltjesN K (![Complex.I, 2 * Complex.I] i)).im : ℝ) : ℂ))
      (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) x0 x1 =
    (1 / 4 : ℝ) •
      ((stieltjesImProductLineSecond (Finset.univ : Finset (Fin 2))
          (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
          (RBM.Green.Bmat 3 3 2 x0 x1 true) ![Complex.I, 2 * Complex.I] : ℂ) +
        (stieltjesImProductLineSecond (Finset.univ : Finset (Fin 2))
          (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
          (RBM.Green.Bmat 3 3 2 x0 x1 false) ![Complex.I, 2 * Complex.I] : ℂ)) :=
  wirtSecond_stieltjesImProduct_expansion 3 3 2 Finset.univ 1 Matrix.isHermitian_one
    ![Complex.I, 2 * Complex.I]
    (by
      intro i _
      fin_cases i <;> simp)
    x0 x1 |>.trans (ite_eq_right x0_ne_x1)

/-- `inst_wirtFirst` : the adjoint form of the first Wirtinger derivative at `(x0, x1)`. -/
theorem inst_wirtFirst :
  stieltjesImWirtingerFirst 3 3 2 (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I x0 x1 =
    (Complex.I * (Fintype.card (Idx 3 3 2) : ℂ)⁻¹ / 2) *
      ((RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I *
          RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) x1 x0 -
        (RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) ((starRingEnd ℂ) Complex.I) *
          RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) ((starRingEnd ℂ) Complex.I)) x1 x0) :=
  stieltjesImWirtingerFirst_adjoint_formula 3 3 2 1 Matrix.isHermitian_one Complex.I (by simp) x0 x1

/-- `inst_kernels` : the size, `S°` symmetric and equal to `scirc`, the conjugate tag, `L₂`. -/
theorem inst_kernels :
  Fintype.card (Idx 3 3 2) = 216 ∧
    centeredVarianceEntry 3 3 2 (1 / 2) x0 x1 =
      centeredVarianceEntry 3 3 2 (1 / 2) x1 x0 ∧
    ((centeredVarianceEntry 3 3 2 (1 / 2) x0 x1 : ℝ) : ℂ) =
      RBM.Univ.scirc 3 3 2 (1 / 2) x0 x1 ∧
    signedGreen (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I false =
      RBM.Gauss.Gres (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I false ∧
    paperL2Kernel 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I (2 * Complex.I) =
      RBM.Univ.L2t 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I (2 * Complex.I) :=
  ⟨RBM.Gauss.card_Idx 3 3 2 ▸ by norm_num,
    centeredVarianceEntry_symm 3 3 2 (1 / 2) x0 x1,
    centeredVarianceEntry_cast 3 3 2 (1 / 2) x0 x1,
    signedGreen_eq_Gres _ _ _,
    paperL2Kernel_eq_L2t 3 3 2 (1 / 2) 1 Complex.I (2 * Complex.I)⟩

/-- `inst_green_line` : the resolvent line derivative at `n = Fin 2`, `H = A = 1`, `z = I`, `t = 0`. -/
theorem inst_green_line :
  HasDerivAt
    (fun s : ℝ => RBM.green
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) Complex.I)
    (-(RBM.green ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          Complex.I *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        RBM.green ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          Complex.I))
    0 :=
  hasDerivAt_green_hermitianLine (H := (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (A := (1 : Matrix (Fin 2) (Fin 2) ℂ)) Matrix.isHermitian_one Matrix.isHermitian_one
    Complex.I (by simp) 0

/-- `inst_stieltjes_line` : the Stieltjes line derivative at the same data (the `Gres` bridge at a concrete matrix). -/
theorem inst_stieltjes_line :
  HasDerivAt
    (fun s : ℝ => RBM.Univ.stieltjesN
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) Complex.I)
    (-((Fintype.card (Fin 2) : ℂ)⁻¹) *
      (RBM.green ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          Complex.I *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        RBM.green ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          Complex.I).trace)
    0 :=
  hasDerivAt_stieltjesN_hermitianLine (H := (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (A := (1 : Matrix (Fin 2) (Fin 2) ℂ)) Matrix.isHermitian_one Matrix.isHermitian_one
    Complex.I (by simp) 0

/-- Target 2a at `ι = Fin 2`, `s = univ`, `f i t = t`, `fp i t = 1`, `fpp i = 0`. -/
example :=
  hasDerivAt_deriv_finset_product_expansion (Finset.univ : Finset (Fin 2))
    (fun _ u => u) (fun _ _ => (1 : ℝ)) (fun _ => (0 : ℝ))
    (fun _ _ t => hasDerivAt_id t) (fun _ _ => hasDerivAt_const 0 1)

/-- Target 2e at `n = Fin 2`, `H = A = 1`, `z = ![I, 2 I]`. -/
example :=
  fderiv_fderiv_stieltjesImProduct_hermitianLine (Finset.univ : Finset (Fin 2))
    (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ)
    Matrix.isHermitian_one Matrix.isHermitian_one ![Complex.I, 2 * Complex.I]
    (by
      intro i _
      fin_cases i <;> simp)

/-- Target 2d at `n = Fin 2`, `H = A = 1`, `z = I`, `t = 0`. -/
example :=
  hasDerivAt_stieltjesFirstVariation (H := (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (A := (1 : Matrix (Fin 2) (Fin 2) ℂ)) Matrix.isHermitian_one Matrix.isHermitian_one
    Complex.I (by simp) 0

/-- Target 3b at `d = 3`, `L = 3`, `W = 2`, `H = 1`, `z = I`, `(x0, x1)`. -/
example :=
  stieltjesImWirtingerFirst_entry_formula 3 3 2 (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
    Matrix.isHermitian_one Complex.I (by simp) x0 x1

end OUHessianInst

end RBM.Univ

end
