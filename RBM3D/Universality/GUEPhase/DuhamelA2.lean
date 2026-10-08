/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Drift
import RBM3D.Path.StepDecomp

/-!
# The loop Duhamel tail of the GUE phase, part I, second half (UN-37)

Ticket T2346.  Port of `RBM2D/Universality/GUEPhase/DuhamelA.lean` §5-§7 (lines 1041-1985, RBM2D
commit `9e0f275`, cited `DA:<line>`): one step of the GUE-phase grid (linear part, Taylor
remainder, truncation), the truncation bias, the grid facts and the drift remainder.  Independent
of the first half (`DuhamelA1`, T2345): the one declaration of the first half that §5-§7 use,
`Duhamel_contDiffAt_loop` (`DA:690`), is re-derived here as the private
`DuhamelA2_contDiffAt_loop` (copy of `RBM3D/Induction/LoopC2N.lean:313-372`, with the word
`I.σ.zip I.a` of a list-based loop).

## Renaming (as T2343)

`d : Sizes` is `sz : Sizes d`; `d.L n`, `d.W n`, `d.size n` are `sz.L n`, `sz.W n`, `sz.size n`
(`= (W L)^d`); `Idx L W` is `Idx d L W`; `Z2 L` is `Zd d L`; `BlockIndex L W` is `Vtx d L W`;
`Coord L W` is `CoordF d L W`; `Ω L W` is `Ω d L W`; `gloop L W (blockMat M)` is
`loopL d L W (blockMat d L W M)`; `Gsig` is `Gres`; `spectralZ` is `zt`; `envConst L W` is
`envConst d L W`; `genMatGUE L W` is `genMatGUE d L W`; `gueUnit d`, `Pgue d`, `filt d`, `PathΩ d`
are `gueUnit sz`, `Pgue sz`, `filt sz`, `PathΩ sz`.  `Duhamel_gueH_succ` (`DA:1806`) is not
ported: it is the merged `gueH_succ` (`Drift.lean:925`) read through
`Sizes.seqHflow sz n v y = (√v : ℂ) • seqXmat` (`rfl`; in RBM2D `seqHflow` is `Hflow ∘ slice`,
so `Duhamel_Z_re_im`, `Duhamel_norm_R_le`, `Duhamel_measurable_R` convert `ℂ`-smul to `ℝ`-smul
with `Complex.coe_smul`).

## `d`-dependent lines

The truncation threshold `d.size n = (W L)²` is `sz.size n = (W L)^d` (`DuhamelGood`,
`Duhamel_norm_T_le`, `Duhamel_norm_B_le`), with `Fintype.card (Idx d L W) = sz.size n` the merged
`Sizes.card_Idx` (RBM2D `Duhamel_card_Idx` is not re-proved); `card (CoordF) = 2 (sz.size n)^2` is
`d`-free given that; the crude bound of `norm_gloop_le_crude` is
`(L W)^d (|Im z|⁻¹ (W^d)⁻¹)^{len}`.  No statement uses `3 ≤ d`.

Every unpinned helper is `private` with the prefix `DuhamelA2_`.  Compiled nonempty instances:
namespace `RBM.Univ.GUEPhase.DuhamelA2Inst` (section 8).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path RBM.Univ
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### 1. The loop observable is `C²` at Hermitian points (private; `DA:557-717`, `LoopC2N.lean:82-372`) -/

section LoopSmooth

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `blockMat` as a continuous real-linear map (`DA:557`). -/
private def DuhamelA2_blockCLM (d L W : ℕ) [NeZero L] [NeZero W] :
    Matrix (Idx d L W) (Idx d L W) ℂ →L[ℝ] Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockMat d L W
      map_add' := fun A C => by ext p q; simp [blockMat]
      map_smul' := fun r A => by ext p q; simp [blockMat] }

/-- The trace as a continuous real-linear map (`DA:567`). -/
private def DuhamelA2_trCLM (n : Type*) [Fintype n] [DecidableEq n] : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)

/-- The resolvent of `blockMat M` is `C²` at every `M` for which `blockMat M - w` is invertible
(`DA:673`, `LoopC2N.lean:313`). -/
private theorem DuhamelA2_contDiffAt_Gres {w : ℂ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hu : IsUnit (blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M') w true)
      M := by
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      blockMat d L W M' - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    ((DuhamelA2_blockCLM d L W).contDiff).sub contDiff_const
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

/-- The signed resolvent factor `G_σ(blockMat M')` is `C²` at Hermitian `M` (`DA:688`,
`LoopC2N.lean:331`). -/
private theorem DuhamelA2_contDiffAt_Gsig {z : ℂ} (hz : z.im ≠ 0) (σ : Bool)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M') z σ)
      M := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  cases σ with
  | true => exact DuhamelA2_contDiffAt_Gres (isUnit_sub_smul_of_isHermitian hMb hz)
  | false =>
    have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
    have h := DuhamelA2_contDiffAt_Gres (d := d) (L := L) (W := W) (w := (starRingEnd ℂ) z)
      (isUnit_sub_smul_of_isHermitian hMb hz')
    simpa [Gres] using h

/-- The resolvent word is `C²` at every Hermitian point (`DA:697`, `LoopC2N.lean:349`). -/
private theorem DuhamelA2_contDiffAt_word {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Zd d L))
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      l.foldr (fun p X => Gres (blockMat d L W M') z p.1 * Eblk d L W p.2 * X) 1) M := by
  induction l with
  | nil => exact contDiffAt_const
  | cons p l ih =>
    have hEp : ContDiffAt ℝ 2 (fun _ : Matrix (Idx d L W) (Idx d L W) ℂ => Eblk d L W p.2) M :=
      contDiffAt_const
    exact ((DuhamelA2_contDiffAt_Gsig hz p.1 hM).mul hEp).mul ih

/-- **The loop observable `M ↦ 𝓛(blockMat M, z, I)` is `C²` at every Hermitian point**
(`Duhamel_contDiffAt_loop`, `DA:711`; here for a list-based loop `I`). -/
private theorem DuhamelA2_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L))
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      loopL d L W (blockMat d L W M') z I) M :=
  (DuhamelA2_trCLM (Vtx d L W)).contDiff.contDiffAt.comp M
    (DuhamelA2_contDiffAt_word hz (I.σ.zip I.a) hM)

end LoopSmooth

/-! ### 5. One step: the linear part, the Taylor remainder, its truncation (`DA:1041-1636`) -/

section Step

/-- `‖A‖² ≤ ∑ |A_ij|²` (`DA:1050`). -/
private theorem DuhamelA2_opNorm_sq_le_frob {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  set F : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2 with hF
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  have hbd : ‖A‖ ≤ Real.sqrt F := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hsq : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x‖ ^ 2 ≤ F * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hF, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have hrow : ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x).ofLp i‖
          ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hrow 2) ?_
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    nlinarith [Real.sq_sqrt hF0, norm_nonneg ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x),
      norm_nonneg x, Real.sqrt_nonneg F, mul_nonneg (Real.sqrt_nonneg F) (norm_nonneg x)]
  nlinarith [Real.sq_sqrt hF0, norm_nonneg A, Real.sqrt_nonneg F]

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- The truncation set `{‖X_{il}‖ ≤ N}` of one increment, `N = sz.size n = (W L)^d` (the event of
`gue_highProb_incr_le`) (`DA:1069`). -/
def DuhamelGood : Set (Sizes.SeqΩ sz) :=
  {y | ∀ i l : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n y i l‖ ≤ ((sz.size n : ℕ) : ℝ)}

/-- The linear part `DΦ(M)[h(y)]` of one step (`DA:1073`). -/
def DuhamelZ (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (y : Sizes.SeqΩ sz) : ℂ :=
  fderiv ℝ Φ M (Sizes.seqHflow sz n v y)

/-- The Taylor remainder of one step (`DA:1079`). -/
def DuhamelR (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (y : Sizes.SeqΩ sz) : ℂ :=
  Φ (M + Sizes.seqHflow sz n v y) - Φ M - DuhamelZ sz n Φ v M y

/-- The truncated remainder (`DA:1085`). -/
def DuhamelT (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (y : Sizes.SeqΩ sz) : ℂ :=
  (DuhamelGood sz n).indicator (DuhamelR sz n Φ v M) y

/-- The truncation bias (`DA:1091`). -/
def DuhamelB (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℂ :=
  ∫ y, (DuhamelGood sz n)ᶜ.indicator (DuhamelR sz n Φ v M) y ∂(gueUnit sz)

variable {sz n}

private theorem DuhamelA2_measurable_seqXentry (i j : Idx d (sz.L n) (sz.W n)) :
    Measurable fun y : Sizes.SeqΩ sz => Sizes.seqXmat sz n y i j :=
  (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (Sizes.measurable_slice sz n)

private theorem DuhamelA2_measurable_seqXmat : Measurable (Sizes.seqXmat sz n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => DuhamelA2_measurable_seqXentry i j

private theorem DuhamelA2_measurable_seqHflow (v : ℝ) : Measurable (Sizes.seqHflow sz n v) :=
  (DuhamelA2_measurable_seqXmat (sz := sz) (n := n)).const_smul (Real.sqrt v : ℂ)

/-- The truncation set is measurable (`DA:1105`). -/
theorem Duhamel_measurableSet_good : MeasurableSet (DuhamelGood sz n) := by
  have h : DuhamelGood sz n = ⋂ i : Idx d (sz.L n) (sz.W n), ⋂ l : Idx d (sz.L n) (sz.W n),
      {y | ‖Sizes.seqXmat sz n y i l‖ ≤ ((sz.size n : ℕ) : ℝ)} := by
    ext y; simp [DuhamelGood]
  rw [h]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun l => ?_
  exact measurableSet_le (DuhamelA2_measurable_seqXentry i l).norm measurable_const

private theorem DuhamelA2_lin_eq_im
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n (-Complex.I • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- `Re Z = √v lin(A, X)`, `Im Z = √v lin(-iA, X)`, `A = gradMat Φ M` (`DA:1124`). -/
theorem Duhamel_Z_re_im (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    {v : ℝ} (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (y : Sizes.SeqΩ sz) :
    (DuhamelZ sz n Φ v M y).re = Real.sqrt v * linTr n (gradMat Φ M) (Sizes.seqXmat sz n y) ∧
      (DuhamelZ sz n Φ v M y).im
        = Real.sqrt v * linTr n (-Complex.I • gradMat Φ M) (Sizes.seqXmat sz n y) := by
  have h : DuhamelZ sz n Φ v M y
      = (Real.sqrt v : ℂ) * Matrix.trace (gradMat Φ M * Sizes.seqXmat sz n y) := by
    unfold DuhamelZ
    rw [Sizes.seqHflow_eq_smul, Complex.coe_smul, map_smul,
      fderiv_eq_trace_gradMat M (Sizes.seqXmat_isHermitian sz n y), Complex.real_smul]
  rw [h, DuhamelA2_lin_eq_im]
  constructor
  · rw [Complex.re_ofReal_mul]; rfl
  · rw [Complex.im_ofReal_mul]

private theorem DuhamelA2_integrable_lin
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Integrable (fun y => linTr n A (Sizes.seqXmat sz n y)) (gueUnit sz) ∧
      ∫ y, linTr n A (Sizes.seqXmat sz n y) ∂(gueUnit sz) = 0 := by
  have hmeas : Measurable (fun y : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n y)) := by
    unfold linTr
    exact Complex.measurable_re.comp
      ((Continuous.matrix_trace (continuous_const.matrix_mul continuous_id)).measurable.comp
        (DuhamelA2_measurable_seqXmat (sz := sz) (n := n)))
  have hmap := gueMap_lin_Xmat sz n A
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 (vGue sz n A)) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  refine ⟨?_, ?_⟩
  · rw [← hmap] at hid
    exact (integrable_map_measure hid.aestronglyMeasurable hmeas.aemeasurable).1 hid
  · have h := integral_map (μ := gueUnit sz) hmeas.aemeasurable
      (f := fun x : ℝ => x) (measurable_id.aestronglyMeasurable)
    rw [hmap, integral_id_gaussianReal] at h
    exact h.symm

private theorem DuhamelA2_integrable_Z
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Integrable (DuhamelZ sz n Φ v M) (gueUnit sz) ∧
      ∫ y, DuhamelZ sz n Φ v M y ∂(gueUnit sz) = 0 := by
  obtain ⟨h1, h1'⟩ := DuhamelA2_integrable_lin (sz := sz) (n := n) (gradMat Φ M)
  obtain ⟨h2, h2'⟩ := DuhamelA2_integrable_lin (sz := sz) (n := n) (-Complex.I • gradMat Φ M)
  have hre : (fun y => RCLike.re (DuhamelZ sz n Φ v M y))
      = fun y => Real.sqrt v * linTr n (gradMat Φ M) (Sizes.seqXmat sz n y) :=
    funext fun y => (Duhamel_Z_re_im Φ M y).1
  have him : (fun y => RCLike.im (DuhamelZ sz n Φ v M y))
      = fun y => Real.sqrt v * linTr n (-Complex.I • gradMat Φ M) (Sizes.seqXmat sz n y) :=
    funext fun y => (Duhamel_Z_re_im Φ M y).2
  have hint : Integrable (DuhamelZ sz n Φ v M) (gueUnit sz) := by
    rw [← Integrable.re_im_iff, hre, him]
    exact ⟨h1.const_mul _, h2.const_mul _⟩
  refine ⟨hint, ?_⟩
  apply Complex.ext
  · have := integral_re hint
    rw [hre, integral_const_mul, h1', mul_zero] at this
    simpa using this.symm
  · have := integral_im hint
    rw [him, integral_const_mul, h2', mul_zero] at this
    simpa using this.symm

end Step

section Taylor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem DuhamelA2_hasDerivAt_add_smul (M y : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => M + t' • y) y t := by
  simpa using ((hasDerivAt_id t).smul_const y).const_add M

private theorem DuhamelA2_isHermitian_add_smul {M y : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hy : y.IsHermitian) (t : ℝ) : (M + t • y).IsHermitian := by
  have hcast : M + t • y = M + (t : ℂ) • y := by rw [Complex.coe_smul]
  rw [hcast]
  exact hM.add (hy.smul (Complex.conj_ofReal t))

private theorem DuhamelA2_hasFDerivAt_fderiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {M : E} (h : DifferentiableAt ℝ (fderiv ℝ f) M) (A : E) :
    HasFDerivAt (fun M' => fderiv ℝ f M' A) ((fderiv ℝ (fderiv ℝ f) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- **The pathwise second-order Taylor remainder bound along a Hermitian line**.  Only (H1) at
Hermitian points and the Hermitian-direction bound (H3) are used (`DA:1190`). -/
private theorem DuhamelA2_taylor {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {C₂ : ℝ}
    (hC₂ : ∀ M y : Matrix ι ι ℂ, M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {M y : Matrix ι ι ℂ} (hM : M.IsHermitian) (hy : y.IsHermitian) {s : ℝ} (hs : 0 ≤ s) :
    ‖Φ (M + s • y) - Φ M - s • fderiv ℝ Φ M y‖ ≤ (C₂ / 2) * s ^ 2 * ‖y‖ ^ 2 := by
  have hH := DuhamelA2_isHermitian_add_smul hM hy
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ Φ (M + t • y) :=
    fun t => (h _ (hH t)).differentiableAt (by norm_num)
  have hdiff2 : ∀ t : ℝ, DifferentiableAt ℝ (fderiv ℝ Φ) (M + t • y) := fun t =>
    ((h _ (hH t)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y)) (fderiv ℝ Φ (M + t • y) y) t :=
    fun t => ((hdiff t).hasFDerivAt).comp_hasDerivAt t (DuhamelA2_hasDerivAt_add_smul M y t)
  have hk : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => fderiv ℝ Φ (M + t' • y) y)
      (fderiv ℝ (fderiv ℝ Φ) (M + t • y) y y) t := by
    intro t
    have h1 := (DuhamelA2_hasFDerivAt_fderiv_apply (hdiff2 t) y).comp_hasDerivAt t
      (DuhamelA2_hasDerivAt_add_smul M y t)
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

section Step2

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- The pathwise Taylor remainder bound: `‖R‖ ≤ (C₂/2) v ‖X‖²` (`DA:1280`). -/
private theorem DuhamelA2_norm_R_le
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {v : ℝ} (hv : 0 ≤ v) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) (y : Sizes.SeqΩ sz) :
    ‖DuhamelR sz n Φ v M y‖ ≤ C₂ / 2 * v * ‖Sizes.seqXmat sz n y‖ ^ 2 := by
  have h := DuhamelA2_taylor hΦ.contDiffAt hC₂ hM (Sizes.seqXmat_isHermitian sz n y)
    (Real.sqrt_nonneg v)
  have e : DuhamelR sz n Φ v M y = Φ (M + Real.sqrt v • Sizes.seqXmat sz n y) - Φ M
      - Real.sqrt v • fderiv ℝ Φ M (Sizes.seqXmat sz n y) := by
    unfold DuhamelR DuhamelZ
    rw [Sizes.seqHflow_eq_smul, Complex.coe_smul, map_smul]
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.sq_sqrt hv]

/-- `Φ(M + h(y))` is measurable in `y` for Hermitian `M`: `Φ` is continuous on the (closed)
Hermitian set and the increment is Hermitian (`DA:1294`). -/
private theorem DuhamelA2_measurable_Phi_line
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    (v : ℝ) :
    Measurable (fun y : Sizes.SeqΩ sz => Φ (M + Sizes.seqHflow sz n v y)) := by
  set S : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {A | A.IsHermitian} with hS
  have hcont : ContinuousOn Φ S := fun A hA =>
    (hΦ.contDiffAt A hA).continuousAt.continuousWithinAt
  have hherm : ∀ y : Sizes.SeqΩ sz, M + Sizes.seqHflow sz n v y ∈ S := fun y =>
    hM.add (Sizes.seqHflow_isHermitian sz n v y)
  have h1 : Measurable (S.domRestrict Φ) := hcont.domRestrict.measurable
  have h2 : Measurable (fun y : Sizes.SeqΩ sz =>
      (⟨M + Sizes.seqHflow sz n v y, hherm y⟩ : S)) :=
    Measurable.subtype_mk
      ((measurable_const (a := M)).add (DuhamelA2_measurable_seqHflow (sz := sz) (n := n) v))
  exact h1.comp h2

/-- Jointly measurable: for a measurable `Φ`, the remainder is measurable in `(M, y)`
(`DA:1309`). -/
theorem Duhamel_measurable_R
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦm : Measurable Φ)
    (v : ℝ) :
    Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
        Sizes.SeqΩ sz => DuhamelR sz n Φ v p.1 p.2) := by
  have hZ : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => DuhamelZ sz n Φ v p.1 p.2) := by
    have hrep : ∀ y : Sizes.SeqΩ sz, Sizes.seqHflow sz n v y
        = ∑ c : CoordF d (sz.L n) (sz.W n),
            (Real.sqrt v * y ⟨n, c⟩) • coordinateMatrix d (sz.L n) (sz.W n) c := by
      intro y
      rw [Sizes.seqHflow_eq_smul, Complex.coe_smul, Sizes.seqXmat_eq_sum_coordinates,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [smul_smul]
    have : (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
        Sizes.SeqΩ sz => DuhamelZ sz n Φ v p.1 p.2)
        = fun p => ∑ c : CoordF d (sz.L n) (sz.W n), (Real.sqrt v * p.2 ⟨n, c⟩) •
            fderiv ℝ Φ p.1 (coordinateMatrix d (sz.L n) (sz.W n) c) := by
      funext p
      unfold DuhamelZ
      rw [hrep, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul]
    rw [this]
    refine Finset.measurable_sum _ fun c _ => ?_
    exact (measurable_const.mul ((measurable_pi_apply (⟨n, c⟩ : Sizes.SeqCoord sz)).comp
      measurable_snd)).smul ((measurable_fderiv_apply_const ℝ Φ _).comp measurable_fst)
  have h1 : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => Φ (p.1 + Sizes.seqHflow sz n v p.2)) :=
    hΦm.comp (measurable_fst.add
      ((DuhamelA2_measurable_seqHflow (sz := sz) (n := n) v).comp measurable_snd))
  exact (h1.sub (hΦm.comp measurable_fst)).sub hZ

private theorem DuhamelA2_integrable_R
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    (v : ℝ) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) :
    Integrable (DuhamelR sz n Φ v M) (gueUnit sz) ∧
      Integrable (fun y => Φ (M + Sizes.seqHflow sz n v y)) (gueUnit sz) := by
  obtain ⟨C₀, hC₀⟩ := hΦ.bdd₀
  have hΦint : Integrable (fun y => Φ (M + Sizes.seqHflow sz n v y)) (gueUnit sz) :=
    (memLp_top_of_bound (DuhamelA2_measurable_Phi_line hΦ hM v).aestronglyMeasurable C₀
      (Eventually.of_forall fun y =>
        hC₀ _ (hM.add (Sizes.seqHflow_isHermitian sz n v y)))).integrable le_top
  refine ⟨?_, hΦint⟩
  have e : DuhamelR sz n Φ v M
      = fun y => Φ (M + Sizes.seqHflow sz n v y) - Φ M - DuhamelZ sz n Φ v M y := rfl
  rw [e]
  exact (hΦint.sub (integrable_const _)).sub (DuhamelA2_integrable_Z Φ v M).1

/-- **The mean of one step**: `∫ Φ(M + h) = Φ(M) + ∫ T + B`.  The bound `hC₂` on the second
derivative is part of the statement but not used (`DA:1357`). -/
theorem Duhamel_integral_step
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    {C₂ : ℝ} (_hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (v : ℝ) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) :
    ∫ y, Φ (M + Sizes.seqHflow sz n v y) ∂(gueUnit sz)
      = Φ M + ∫ y, DuhamelT sz n Φ v M y ∂(gueUnit sz) + DuhamelB sz n Φ v M := by
  obtain ⟨hR, hΦint⟩ := DuhamelA2_integrable_R hΦ v hM
  obtain ⟨hZ, hZ0⟩ := DuhamelA2_integrable_Z Φ v M
  have hpt : (fun y => Φ (M + Sizes.seqHflow sz n v y))
      = fun y => Φ M + (DuhamelZ sz n Φ v M y + DuhamelR sz n Φ v M y) := by
    funext y; unfold DuhamelR; ring
  have hZR : Integrable (fun y => DuhamelZ sz n Φ v M y + DuhamelR sz n Φ v M y) (gueUnit sz) :=
    hZ.add hR
  rw [hpt, integral_add (integrable_const _) hZR, integral_add hZ hR, hZ0,
    integral_const, probReal_univ, one_smul, zero_add]
  have hsplit : DuhamelR sz n Φ v M
      = fun y => DuhamelT sz n Φ v M y + (DuhamelGood sz n)ᶜ.indicator (DuhamelR sz n Φ v M) y := by
    funext y; unfold DuhamelT; rw [Set.indicator_self_add_compl_apply]
  have hT : Integrable (DuhamelT sz n Φ v M) (gueUnit sz) :=
    hR.indicator Duhamel_measurableSet_good
  have hB : Integrable ((DuhamelGood sz n)ᶜ.indicator (DuhamelR sz n Φ v M)) (gueUnit sz) :=
    hR.indicator Duhamel_measurableSet_good.compl
  conv_lhs => rw [hsplit]
  rw [integral_add hT hB]
  unfold DuhamelB
  ring

end Step2

section LoopMeasurable

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem DuhamelA2_measurable_mul {α : Type*} [MeasurableSpace α] {B : Type*} [Fintype B]
    {F G : α → Matrix B B ℂ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun a => F a * G a) := by
  refine measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun q => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_pi_iff.1 (measurable_pi_iff.1 hF p) k).mul
      (measurable_pi_iff.1 (measurable_pi_iff.1 hG k) q)

private theorem DuhamelA2_measurable_nonsing_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable (fun A : Matrix m m ℂ => A⁻¹) := by
  have h : (fun A : Matrix m m ℂ => A⁻¹) = fun A => Ring.inverse A.det • A.adjugate := by
    funext A; exact Matrix.inv_def A
  rw [h]
  have h1 : Measurable (fun A : Matrix m m ℂ => Ring.inverse A.det) := by
    rw [Ring.inverse_eq_inv']
    exact (Continuous.matrix_det continuous_id).measurable.inv
  have h2 : Measurable (fun A : Matrix m m ℂ => A.adjugate) :=
    (Continuous.matrix_adjugate continuous_id).measurable
  exact h1.smul h2

/-- **The loop observable is measurable on all matrices** (`Measurable Φ` is the hypothesis of
`Duhamel_measurable_R`; `Φ` is only `C²` at Hermitian points, but it is a Borel function of the
matrix: the resolvent is the Borel map `A ↦ A⁻¹ = det⁻¹ · adj A`, and `Gres H z σ` is
`Ring.inverse (H - w • 1) = (H - w • 1)⁻¹`) (`DA:1418`). -/
theorem Duhamel_measurable_loop (z : ℂ) (I : Loop.LoopIdx (Zd d L)) :
    Measurable (fun M : Matrix (Idx d L W) (Idx d L W) ℂ => loopL d L W (blockMat d L W M) z I) := by
  have hb : Continuous (fun M : Matrix (Idx d L W) (Idx d L W) ℂ => blockMat d L W M) := by
    unfold blockMat
    exact continuous_id.matrix_submatrix _ _
  have hG : ∀ s : Bool,
      Measurable (fun M : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M) z s) := by
    intro s
    have hfun : (fun M : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M) z s)
        = fun M => (blockMat d L W M - (if s then z else (starRingEnd ℂ) z) •
            (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))⁻¹ := by
      funext M
      exact (Matrix.nonsing_inv_eq_ringInverse _).symm
    rw [hfun]
    exact DuhamelA2_measurable_nonsing_inv.comp (hb.sub continuous_const).measurable
  have hw : ∀ l : List (Bool × Zd d L), Measurable (fun M : Matrix (Idx d L W) (Idx d L W) ℂ =>
      l.foldr (fun p X => Gres (blockMat d L W M) z p.1 * Eblk d L W p.2 * X) 1) := by
    intro l
    induction l with
    | nil => exact measurable_const
    | cons p l ih =>
      simp only [List.foldr_cons]
      exact DuhamelA2_measurable_mul (DuhamelA2_measurable_mul (hG p.1) measurable_const) ih
  unfold loopL
  exact (Continuous.matrix_trace continuous_id).measurable.comp (hw _)

end LoopMeasurable

section Bounds

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

private theorem DuhamelA2_norm_le_card_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A‖ ≤ (Fintype.card ι : ℝ) * B := by
  have h1 : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : ι, ∑ _j : ι, B ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  have h2 : ∑ _i : ι, ∑ _j : ι, B ^ 2 = ((Fintype.card ι : ℝ) * B) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
    ((DuhamelA2_opNorm_sq_le_frob A).trans (h1.trans h2.le))

/-- The second-derivative bound forces `0 ≤ C₂` (the replacement of the field `nonneg₂` of
`BddC2C`): evaluate it at `M = 0`, `y = E_{00}` (`DA:1456`). -/
private theorem DuhamelA2_nonneg_C2
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} {C₂ : ℝ}
    (hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2) :
    0 ≤ C₂ := by
  set i : Idx d (sz.L n) (sz.W n) := 0 with hi
  have hy : (Matrix.single i i (1 : ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_single]
  have h := hC₂ 0 (Matrix.single i i 1) Matrix.isHermitian_zero hy
  have hne : (Matrix.single i i (1 : ℂ) :
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 i) i
    simp at this
  have hpos : 0 < ‖(Matrix.single i i (1 : ℂ) : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)‖ ^ 2 := by
    have := norm_pos_iff.2 hne
    positivity
  by_contra hneg
  have hneg' : C₂ < 0 := not_le.mp hneg
  nlinarith [mul_neg_of_neg_of_pos hneg' hpos, norm_nonneg
    (fderiv ℝ (fderiv ℝ Φ) 0 (Matrix.single i i (1 : ℂ)) (Matrix.single i i (1 : ℂ)))]

/-- On the truncation set, `‖T‖ ≤ (C₂/2) v N⁴`, `N = sz.size n` (`card (Idx) = N` and the truncation
threshold is `N`) (`DA:1481`). -/
theorem Duhamel_norm_T_le
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {v : ℝ} (hv : 0 ≤ v) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) (y : Sizes.SeqΩ sz) :
    ‖DuhamelT sz n Φ v M y‖ ≤ C₂ / 2 * v * ((sz.size n : ℕ) : ℝ) ^ 4 := by
  have hC2 : 0 ≤ C₂ := DuhamelA2_nonneg_C2 hC₂
  unfold DuhamelT
  by_cases hy : y ∈ DuhamelGood sz n
  · rw [Set.indicator_of_mem hy]
    refine (DuhamelA2_norm_R_le hΦ hC₂ hv hM y).trans ?_
    have hX : ‖Sizes.seqXmat sz n y‖ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 4 := by
      have h1 := DuhamelA2_norm_le_card_mul (Sizes.seqXmat sz n y)
        (B := ((sz.size n : ℕ) : ℝ)) (by positivity) (fun i l => hy i l)
      rw [Sizes.card_Idx] at h1
      calc ‖Sizes.seqXmat sz n y‖ ^ 2
          ≤ (((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = ((sz.size n : ℕ) : ℝ) ^ 4 := by ring
    have h0 : 0 ≤ C₂ / 2 * v := by positivity
    exact mul_le_mul_of_nonneg_left hX h0
  · rw [Set.indicator_of_notMem hy, norm_zero]
    positivity

end Bounds

/-! ### 6. The truncation bias (`DA:1636-1820`) -/

section Tail

/-- An entry of `Xmat` is bounded by its (at most four) raw coordinates (`DA:1648`). -/
private theorem DuhamelA2_norm_Xentry_le {d L W : ℕ} [NeZero L] [NeZero W] (ω : Ω d L W)
    (i j : Idx d L W) :
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

/-- `∑_{ij} |X_ij|² ≤ 2 ∑_c ω_c²`: every raw coordinate enters at most two entries (`DA:1670`). -/
private theorem DuhamelA2_sumSq_Xentry_le {d L W : ℕ} [NeZero L] [NeZero W] (ω : Ω d L W) :
    ∑ i, ∑ l, ‖Xentry d L W ω i l‖ ^ 2 ≤ 2 * ∑ c : CoordF d L W, (ω c) ^ 2 := by
  set q : Idx d L W → Idx d L W → ℝ := fun i j => (ω (i, j, true)) ^ 2 + (ω (i, j, false)) ^ 2
    with hq
  have hq0 : ∀ i j, 0 ≤ q i j := fun i j => by simp only [hq]; positivity
  have hpt : ∀ i j : Idx d L W, ‖Xentry d L W ω i j‖ ^ 2 ≤ q i j + q j i := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
    · have hX : ‖Xentry d L W ω i j‖ ^ 2 = q i j := by
        rw [Xentry, ite_eq_left h, ← Complex.normSq_eq_norm_sq]
        simp only [hq, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      rw [hX]; linarith [hq0 j i]
    · subst h
      have hX : ‖Xentry d L W ω i i‖ ^ 2 = (ω (i, i, true)) ^ 2 := by
        rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), Complex.norm_real,
          Real.norm_eq_abs, sq_abs]
      rw [hX]
      have : 0 ≤ (ω (i, i, false)) ^ 2 := sq_nonneg _
      simp only [hq]
      nlinarith
    · have hX : ‖Xentry d L W ω i j‖ ^ 2 = q j i := by
        rw [Xentry, ite_eq_right (asymm h), ite_eq_left h, ← Complex.normSq_eq_norm_sq]
        simp only [hq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      rw [hX]; linarith [hq0 i j]
  have hsplit : ∑ c : CoordF d L W, (ω c) ^ 2 = ∑ i : Idx d L W, ∑ j : Idx d L W, q i j := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
  have hswap : ∑ i : Idx d L W, ∑ j : Idx d L W, q j i = ∑ i : Idx d L W, ∑ j : Idx d L W, q i j :=
    Finset.sum_comm
  calc ∑ i, ∑ l, ‖Xentry d L W ω i l‖ ^ 2 ≤ ∑ i : Idx d L W, ∑ j : Idx d L W, (q i j + q j i) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = 2 * ∑ i : Idx d L W, ∑ j : Idx d L W, q i j := by
        simp only [Finset.sum_add_distrib]
        rw [hswap]; ring
    _ = 2 * ∑ c : CoordF d L W, (ω c) ^ 2 := by rw [hsplit]

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

private theorem DuhamelA2_exp_coord (c : ℝ) (t : CoordF d (sz.L n) (sz.W n)) :
    Integrable (fun y : Sizes.SeqΩ sz => Real.exp (c * y ⟨n, t⟩)) (gueUnit sz) ∧
      ∫ y, Real.exp (c * y ⟨n, t⟩) ∂(gueUnit sz) ≤ Real.exp (c ^ 2 / 2) := by
  have hmeas : Measurable (fun y : Sizes.SeqΩ sz => y ⟨n, t⟩) := measurable_pi_apply _
  have hmap : (gueUnit sz).map (fun y : Sizes.SeqΩ sz => y ⟨n, t⟩)
      = gaussianReal 0 (gueUnitVar sz ⟨n, t⟩) := Measure.infinitePi_map_eval _ _
  have hlaw : HasLaw (fun y : Sizes.SeqΩ sz => y ⟨n, t⟩) (gaussianReal 0 (gueUnitVar sz ⟨n, t⟩))
      (gueUnit sz) := ⟨hmeas.aemeasurable, hmap⟩
  have hv : (gueUnitVar sz ⟨n, t⟩ : ℝ) ≤ 1 := by unfold gueUnitVar; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · have h := integrable_exp_mul_gaussianReal (μ := 0) (v := gueUnitVar sz ⟨n, t⟩) c
    rw [← hmap] at h
    exact (integrable_map_measure h.aestronglyMeasurable hmeas.aemeasurable).1 h
  · have h := mgf_gaussianReal hlaw c
    have e : ∫ y, Real.exp (c * y ⟨n, t⟩) ∂(gueUnit sz)
        = mgf (fun y : Sizes.SeqΩ sz => y ⟨n, t⟩) (gueUnit sz) c :=
      rfl
    rw [e, h]
    apply Real.exp_le_exp.2
    have : (gueUnitVar sz ⟨n, t⟩ : ℝ) * c ^ 2 ≤ c ^ 2 := by
      nlinarith [sq_nonneg c, NNReal.coe_nonneg (gueUnitVar sz ⟨n, t⟩)]
    linarith

/-- `ψ(t,t') = e^{2y_t} + e^{-2y_t} + e^{2y_{t'}} + e^{-2y_{t'}}`. -/
private def DuhamelA2_psi (n : ℕ) (y : Sizes.SeqΩ sz) (t t' : CoordF d (sz.L n) (sz.W n)) : ℝ :=
  Real.exp (2 * y ⟨n, t⟩) + Real.exp (-2 * y ⟨n, t⟩)
    + Real.exp (2 * y ⟨n, t'⟩) + Real.exp (-2 * y ⟨n, t'⟩)

private theorem DuhamelA2_psi_nonneg (y : Sizes.SeqΩ sz) (t t' : CoordF d (sz.L n) (sz.W n)) :
    0 ≤ DuhamelA2_psi n y t t' := by unfold DuhamelA2_psi; positivity

private theorem DuhamelA2_exp_two_abs_le (x : ℝ) :
    Real.exp (2 * |x|) ≤ Real.exp (2 * x) + Real.exp (-2 * x) := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-2 * x)]
  · rw [abs_of_nonpos h, show 2 * -x = -2 * x by ring]; linarith [Real.exp_pos (2 * x)]

/-- `x² ≤ 2 e^{|x|}`. -/
private theorem DuhamelA2_sq_le_two_exp (x : ℝ) : x ^ 2 ≤ 2 * Real.exp |x| := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  rw [sq_abs] at h
  nlinarith [abs_nonneg x]

/-- Off the truncation set, `∑_t y_t² ≤ e^{-N/4} ∑_{t,t'} ψ(t,t')`, `N = sz.size n` (`DA:1612`). -/
private theorem DuhamelA2_coordSq_le_of_not_good {y : Sizes.SeqΩ sz}
    (hy : y ∉ DuhamelGood sz n) :
    ∑ t : CoordF d (sz.L n) (sz.W n), (y ⟨n, t⟩) ^ 2
      ≤ Real.exp (-((sz.size n : ℕ) : ℝ) / 4) * ∑ t, ∑ t', DuhamelA2_psi n y t t' := by
  simp only [DuhamelGood, Set.mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨i, l, hil⟩ := hy
  have hent : ‖Sizes.seqXmat sz n y i l‖ ≤ (|y ⟨n, (i, l, true)⟩| + |y ⟨n, (i, l, false)⟩|)
      + (|y ⟨n, (l, i, true)⟩| + |y ⟨n, (l, i, false)⟩|) :=
    DuhamelA2_norm_Xentry_le (Sizes.slice sz n y) i l
  -- one of the four coordinates exceeds `N/4`
  obtain ⟨t', ht'⟩ : ∃ t' : CoordF d (sz.L n) (sz.W n),
      ((sz.size n : ℕ) : ℝ) / 4 < |y ⟨n, t'⟩| := by
    by_contra hno
    push Not at hno
    have := hno (i, l, true); have := hno (i, l, false); have := hno (l, i, true)
    have := hno (l, i, false)
    linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hone : 1 ≤ Real.exp (|y ⟨n, t'⟩| - N / 4) := Real.one_le_exp (by linarith)
  have hterm : ∀ t : CoordF d (sz.L n) (sz.W n),
      (y ⟨n, t⟩) ^ 2 ≤ Real.exp (-N / 4) * DuhamelA2_psi n y t t' := by
    intro t
    have h1 := DuhamelA2_sq_le_two_exp (y ⟨n, t⟩)
    have h2 : 2 * Real.exp |y ⟨n, t⟩| ≤ 2 * Real.exp |y ⟨n, t⟩|
        * Real.exp (|y ⟨n, t'⟩| - N / 4) := by
      have : 0 ≤ 2 * Real.exp |y ⟨n, t⟩| := by positivity
      nlinarith
    have h3 : 2 * Real.exp |y ⟨n, t⟩| * Real.exp (|y ⟨n, t'⟩| - N / 4)
        = Real.exp (-N / 4) * (2 * (Real.exp |y ⟨n, t⟩| * Real.exp |y ⟨n, t'⟩|)) := by
      rw [Real.exp_sub]
      have : Real.exp (N / 4) ≠ 0 := (Real.exp_pos _).ne'
      rw [show -N / 4 = -(N / 4) by ring, Real.exp_neg]
      field_simp
    have h4 : 2 * (Real.exp |y ⟨n, t⟩| * Real.exp |y ⟨n, t'⟩|)
        ≤ Real.exp (2 * |y ⟨n, t⟩|) + Real.exp (2 * |y ⟨n, t'⟩|) := by
      have e1 : Real.exp (2 * |y ⟨n, t⟩|) = Real.exp |y ⟨n, t⟩| ^ 2 := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have e2 : Real.exp (2 * |y ⟨n, t'⟩|) = Real.exp |y ⟨n, t'⟩| ^ 2 := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      rw [e1, e2]
      nlinarith [sq_nonneg (Real.exp |y ⟨n, t⟩| - Real.exp |y ⟨n, t'⟩|)]
    have h5 : Real.exp (2 * |y ⟨n, t⟩|) + Real.exp (2 * |y ⟨n, t'⟩|) ≤ DuhamelA2_psi n y t t' := by
      unfold DuhamelA2_psi
      have := DuhamelA2_exp_two_abs_le (y ⟨n, t⟩)
      have := DuhamelA2_exp_two_abs_le (y ⟨n, t'⟩)
      linarith
    have hE : 0 ≤ Real.exp (-N / 4) := (Real.exp_pos _).le
    calc (y ⟨n, t⟩) ^ 2 ≤ 2 * Real.exp |y ⟨n, t⟩| := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ Real.exp (-N / 4) * DuhamelA2_psi n y t t' :=
          mul_le_mul_of_nonneg_left (h4.trans h5) hE
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => (hterm t).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact Finset.single_le_sum (f := fun t'' => DuhamelA2_psi n y t t'')
    (fun _ _ => DuhamelA2_psi_nonneg y t _) (Finset.mem_univ t')

private theorem DuhamelA2_integrable_psi (t t' : CoordF d (sz.L n) (sz.W n)) :
    Integrable (fun y : Sizes.SeqΩ sz => DuhamelA2_psi n y t t') (gueUnit sz) ∧
      ∫ y, DuhamelA2_psi n y t t' ∂(gueUnit sz) ≤ 4 * Real.exp 2 := by
  obtain ⟨i1, j1⟩ := DuhamelA2_exp_coord (sz := sz) (n := n) 2 t
  obtain ⟨i2, j2⟩ := DuhamelA2_exp_coord (sz := sz) (n := n) (-2) t
  obtain ⟨i3, j3⟩ := DuhamelA2_exp_coord (sz := sz) (n := n) 2 t'
  obtain ⟨i4, j4⟩ := DuhamelA2_exp_coord (sz := sz) (n := n) (-2) t'
  have hint : Integrable (fun y : Sizes.SeqΩ sz => DuhamelA2_psi n y t t') (gueUnit sz) :=
    ((i1.add i2).add i3).add i4
  refine ⟨hint, ?_⟩
  unfold DuhamelA2_psi
  have i12 : Integrable (fun y : Sizes.SeqΩ sz => Real.exp (2 * y ⟨n, t⟩)
      + Real.exp (-2 * y ⟨n, t⟩)) (gueUnit sz) := i1.add i2
  have i123 : Integrable (fun y : Sizes.SeqΩ sz => Real.exp (2 * y ⟨n, t⟩)
      + Real.exp (-2 * y ⟨n, t⟩) + Real.exp (2 * y ⟨n, t'⟩)) (gueUnit sz) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2]
  have e : Real.exp ((2 : ℝ) ^ 2 / 2) = Real.exp 2 := by norm_num
  have e' : Real.exp ((-2 : ℝ) ^ 2 / 2) = Real.exp 2 := by norm_num
  rw [e] at j1 j3; rw [e'] at j2 j4
  linarith

/-- **The truncation bias**: `‖B‖ ≤ 16 e² C₂ v N⁴ e^{-N/4}`, `N = sz.size n` (`DA:1704`). -/
theorem Duhamel_norm_B_le
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {v : ℝ} (hv : 0 ≤ v) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) :
    ‖DuhamelB sz n Φ v M‖ ≤ 16 * Real.exp 2 * C₂ * v * ((sz.size n : ℕ) : ℝ) ^ 4
      * Real.exp (-((sz.size n : ℕ) : ℝ) / 4) := by
  have hC2 : 0 ≤ C₂ := DuhamelA2_nonneg_C2 hC₂
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set g : Sizes.SeqΩ sz → ℝ := fun y => C₂ / 2 * v * (2 * (Real.exp (-N / 4)
      * ∑ t, ∑ t', DuhamelA2_psi n y t t')) with hg
  have hgint : Integrable g (gueUnit sz) := by
    refine ((integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ =>
      (DuhamelA2_integrable_psi t t').1).const_mul _).const_mul _ |>.const_mul _
  have hpt : ∀ y, ‖(DuhamelGood sz n)ᶜ.indicator (DuhamelR sz n Φ v M) y‖ ≤ g y := by
    intro y
    have hg0 : 0 ≤ g y := by
      simp only [hg]
      have : 0 ≤ ∑ t, ∑ t', DuhamelA2_psi n y t t' :=
        Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun t' _ => DuhamelA2_psi_nonneg y t t'
      positivity
    by_cases hy : y ∈ DuhamelGood sz n
    · rw [Set.indicator_of_notMem (by simpa using hy), norm_zero]; exact hg0
    · rw [Set.indicator_of_mem (by simpa using hy)]
      refine (DuhamelA2_norm_R_le hΦ hC₂ hv hM y).trans ?_
      have hX : ‖Sizes.seqXmat sz n y‖ ^ 2 ≤ 2 * ∑ t : CoordF d (sz.L n) (sz.W n), (y ⟨n, t⟩) ^ 2 :=
        (DuhamelA2_opNorm_sq_le_frob _).trans (DuhamelA2_sumSq_Xentry_le (Sizes.slice sz n y))
      have hc := DuhamelA2_coordSq_le_of_not_good hy
      have h0 : 0 ≤ C₂ / 2 * v := by positivity
      simp only [hg]
      exact mul_le_mul_of_nonneg_left (by linarith) h0
  refine (norm_integral_le_of_norm_le hgint (Eventually.of_forall hpt)).trans ?_
  have hsum : ∫ y, ∑ t, ∑ t', DuhamelA2_psi n y t t' ∂(gueUnit sz)
      ≤ ((Fintype.card (CoordF d (sz.L n) (sz.W n)) : ℝ)) ^ 2 * (4 * Real.exp 2) := by
    rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ =>
      (DuhamelA2_integrable_psi t t').1]
    calc ∑ t, ∫ y, ∑ t', DuhamelA2_psi n y t t' ∂(gueUnit sz)
        = ∑ t : CoordF d (sz.L n) (sz.W n), ∑ t' : CoordF d (sz.L n) (sz.W n),
            ∫ y, DuhamelA2_psi n y t t' ∂(gueUnit sz) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact integral_finsetSum _ fun t' _ => (DuhamelA2_integrable_psi t t').1
      _ ≤ ∑ _t : CoordF d (sz.L n) (sz.W n), ∑ _t' : CoordF d (sz.L n) (sz.W n), 4 * Real.exp 2 :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun t' _ => (DuhamelA2_integrable_psi t t').2
      _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
  have hcard : ((Fintype.card (CoordF d (sz.L n) (sz.W n)) : ℕ) : ℝ) = 2 * N ^ 2 := by
    rw [show Fintype.card (CoordF d (sz.L n) (sz.W n))
        = Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) from rfl,
      Fintype.card_prod (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n) × Bool),
      Fintype.card_prod (Idx d (sz.L n) (sz.W n)) Bool, Fintype.card_bool, Sizes.card_Idx]
    push_cast; ring
  rw [hcard] at hsum
  simp only [hg]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hE : 0 ≤ Real.exp (-N / 4) := (Real.exp_pos _).le
  have h0 : 0 ≤ C₂ / 2 * v := by positivity
  calc C₂ / 2 * v * (2 * (Real.exp (-N / 4)
        * ∫ y, ∑ t, ∑ t', DuhamelA2_psi n y t t' ∂(gueUnit sz)))
      ≤ C₂ / 2 * v * (2 * (Real.exp (-N / 4)
        * ((2 * N ^ 2) ^ 2 * (4 * Real.exp 2)))) := by
        gcongr
    _ = _ := by ring

end Tail

/-! ### 7. The grid: measurability, freezing, and the D3 remainder (`DA:1820-1985`) -/

section Grid

variable {d : ℕ} (sz : Sizes d)

/-- `ω ↦ ω i` is `filt sz k`-measurable for `i ≤ k` (`DA:1824`). -/
theorem Duhamel_measurable_coord {i k : ℕ} (h : i ≤ k) :
    Measurable[filt sz k] (fun ω : PathΩ sz => ω i) := by
  have : (fun ω : PathΩ sz => ω i)
      = (fun g : Set.Iic k → Sizes.SeqΩ sz => g ⟨i, h⟩)
        ∘ (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k) := rfl
  rw [this]
  exact (measurable_pi_apply (⟨i, h⟩ : Set.Iic k)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k))

/-- A private copy of the (private) `StandardBorelSpace` instance of `Drift.lean`. -/
private instance DuhamelA2_standardBorelMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

/-- The grid path is `filt sz k`-measurable as a matrix-valued map (`DA:1836`). -/
theorem Duhamel_gueH_measurable_filt (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable[filt sz k] (gueH sz t1 t0 K n k) :=
  @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun i =>
    @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun j =>
      (gueH_adapted sz t1 t0 K n k i j).measurable

variable {sz}

/-- Complex freezing under `Pgue` (real and imaginary parts of `gueCondExp_freeze`) (`DA:1855`). -/
private theorem DuhamelA2_condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : PathΩ sz → β} (hY : Measurable[filt sz k] Y)
    {F : β → Sizes.SeqΩ sz → ℂ} (hF : Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2))
    (hFInt : ∀ p, Integrable (F p) (gueUnit sz))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue sz)) :
    (Pgue sz)[fun ω => F (Y ω) (ω (k + 1)) | filt sz k]
      =ᵐ[Pgue sz] fun ω => ∫ x, F (Y ω) x ∂(gueUnit sz) := by
  classical
  set f : PathΩ sz → ℂ := fun ω => F (Y ω) (ω (k + 1)) with hfdef
  set Fre : β → Sizes.SeqΩ sz → ℝ := fun p x => RCLike.re (F p x) with hFredef
  set Fim : β → Sizes.SeqΩ sz → ℝ := fun p x => RCLike.im (F p x) with hFimdef
  have hFre : Measurable (fun p : β × Sizes.SeqΩ sz => Fre p.1 p.2) :=
    RCLike.continuous_re.measurable.comp hF
  have hFim : Measurable (fun p : β × Sizes.SeqΩ sz => Fim p.1 p.2) :=
    RCLike.continuous_im.measurable.comp hF
  have hIntRe : Integrable (fun ω => Fre (Y ω) (ω (k + 1))) (Pgue sz) := hInt.re
  have hIntIm : Integrable (fun ω => Fim (Y ω) (ω (k + 1))) (Pgue sz) := hInt.im
  have hfreezeRe := gueCondExp_freeze sz k hY hFre hIntRe
  have hfreezeIm := gueCondExp_freeze sz k hY hFim hIntIm
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := filt sz k) hInt
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := filt sz k) hInt
  have hReComb : (fun ω => RCLike.re ((Pgue sz)[f | filt sz k] ω))
      =ᵐ[Pgue sz] fun ω => ∫ x, Fre (Y ω) x ∂(gueUnit sz) := by
    have hRe' : (fun ω => RCLike.re ((Pgue sz)[f | filt sz k] ω))
        =ᵐ[Pgue sz] (Pgue sz)[fun ω => Fre (Y ω) (ω (k + 1)) | filt sz k] := hRe
    exact hRe'.trans hfreezeRe
  have hImComb : (fun ω => RCLike.im ((Pgue sz)[f | filt sz k] ω))
      =ᵐ[Pgue sz] fun ω => ∫ x, Fim (Y ω) x ∂(gueUnit sz) := by
    have hIm' : (fun ω => RCLike.im ((Pgue sz)[f | filt sz k] ω))
        =ᵐ[Pgue sz] (Pgue sz)[fun ω => Fim (Y ω) (ω (k + 1)) | filt sz k] := hIm
    exact hIm'.trans hfreezeIm
  have hreEq : ∀ p, ∫ x, Fre p x ∂(gueUnit sz) = RCLike.re (∫ x, F p x ∂(gueUnit sz)) :=
    fun p => integral_re (hFInt p)
  have himEq : ∀ p, ∫ x, Fim p x ∂(gueUnit sz) = RCLike.im (∫ x, F p x ∂(gueUnit sz)) :=
    fun p => integral_im (hFInt p)
  filter_upwards [hReComb, hImComb] with ω hωre hωim
  refine Complex.ext ?_ ?_
  · change RCLike.re ((Pgue sz)[f | filt sz k] ω) = RCLike.re (∫ x, F (Y ω) x ∂(gueUnit sz))
    rw [hωre, hreEq]
  · change RCLike.im ((Pgue sz)[f | filt sz k] ω) = RCLike.im (∫ x, F (Y ω) x ∂(gueUnit sz))
    rw [hωim, himEq]

section Observable

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The Hermitian part `½ (A + Aᴴ)` (`DA:1898`). -/
private def DuhamelA2_herm (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  (1 / 2 : ℝ) • (A + Aᴴ)

private theorem DuhamelA2_herm_isHermitian (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    (DuhamelA2_herm A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (star_trivial (1 / 2 : ℝ))

private theorem DuhamelA2_herm_of_isHermitian {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) : DuhamelA2_herm A = A := by
  unfold DuhamelA2_herm
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem DuhamelA2_continuous_herm :
    Continuous (DuhamelA2_herm : Matrix (Idx d L W) (Idx d L W) ℂ → _) := by
  unfold DuhamelA2_herm
  have h1 : Continuous fun A : Matrix (Idx d L W) (Idx d L W) ℂ => Aᴴ :=
    continuous_id.matrix_conjTranspose
  exact Continuous.const_smul (continuous_id.add h1) (1 / 2 : ℝ)

/-- The loop observable of the Hermitian part of a matrix. -/
private def DuhamelA2_Phi (d L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (I : Loop.LoopIdx (Zd d L))
    (A : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  loopL d L W (blockMat d L W (DuhamelA2_herm A)) z I

private theorem DuhamelA2_continuous_Phi {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    Continuous (DuhamelA2_Phi d L W z I) := by
  refine continuous_iff_continuousAt.2 fun A => ?_
  exact (DuhamelA2_contDiffAt_loop hz I (DuhamelA2_herm_isHermitian A)).continuousAt.comp
    DuhamelA2_continuous_herm.continuousAt

/-- The crude loop bound along the Hermitian part: `‖Φ(A)‖ ≤ (L W)^d (|Im z|⁻¹ (W^d)⁻¹)^{len}`
(`DA:1927`, `Drift.lean:1034`). -/
private theorem DuhamelA2_norm_Phi_le {z : ℂ} (hz : z.im ≠ 0) {I : Loop.LoopIdx (Zd d L)}
    (hwf : I.WF) (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ‖DuhamelA2_Phi d L W z I A‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) * (|z.im|⁻¹ * (((W : ℝ) ^ d)⁻¹)) ^ I.a.length :=
  norm_gloop_le_crude d L W ((DuhamelA2_herm_isHermitian A).submatrix _) (abs_pos.mpr hz) le_rfl
    I hwf

end Observable

/-- **The drift remainder**: the conditional mean of the next loop minus the loop and its
drift is bounded by the remainder `envConst · Δ^{3/2}` of `condExp_loop_drift_gue`, almost
surely (`DA:1939`). -/
theorem Duhamel_drift_remainder_ae (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (e : ℝ)
    (he : |e| < 2) {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) :
    ∀ᵐ ω ∂(Pgue sz),
      ‖(∫ y, loopL d (sz.L n) (sz.W n)
            (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω
              + Sizes.seqHflow sz n (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) y))
            (zt e (gridTime t1 t0 K n (k + 1))) I ∂(gueUnit sz))
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
              (zt e (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) *
              genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n k) (gueH sz t1 t0 K n k ω) I‖
        ≤ envConst d (sz.L n) (sz.W n) e I.length (gridTime t1 t0 K n (k + 1))
            * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
  set z1 := zt e (gridTime t1 t0 K n (k + 1)) with hz1
  set v := gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ) with hv
  have hu1lt : gridTime t1 t0 K n (k + 1) < 1 := by
    have hKpos : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
    have hk1 : (k : ℝ) + 1 ≤ (K n : ℝ) := by exact_mod_cast hk
    have hΔ0 : 0 ≤ gridStep t1 t0 K n := by
      unfold gridStep; exact div_nonneg (by linarith) hKpos.le
    have hKΔ : (K n : ℝ) * gridStep t1 t0 K n = t0 n - t1 n := by unfold gridStep; field_simp
    have h : gridTime t1 t0 K n (k + 1) = t1 n + ((k : ℝ) + 1) * gridStep t1 t0 K n := by
      unfold gridTime; push_cast; ring
    rw [h]; nlinarith
  have hz1ne : z1.im ≠ 0 := by
    rw [hz1, zt_im]
    exact (mul_pos (sub_pos.2 hu1lt) (mE_im_pos he)).ne'
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ sz → ℂ :=
    fun p y => DuhamelA2_Phi d (sz.L n) (sz.W n) z1 I (p + Sizes.seqHflow sz n v y) with hF
  have hΦcont := DuhamelA2_continuous_Phi (d := d) (L := sz.L n) (W := sz.W n) hz1ne I
  have hFmeas : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => F p.1 p.2) :=
    hΦcont.measurable.comp (measurable_fst.add
      ((DuhamelA2_measurable_seqHflow (sz := sz) (n := n) v).comp measurable_snd))
  have hFbdd : ∀ p y, ‖F p y‖ ≤ (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) *
      (|z1.im|⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) ^ I.a.length :=
    fun p y => DuhamelA2_norm_Phi_le hz1ne hwf _
  have hFInt : ∀ p, Integrable (F p) (gueUnit sz) := by
    intro p
    have hm : Measurable (fun y : Sizes.SeqΩ sz => F p y) := by
      have h := hFmeas.comp (measurable_const.prodMk measurable_id :
        Measurable fun y : Sizes.SeqΩ sz => (p, y))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun y => hFbdd p y)).integrable le_top
  have hYmeas := Duhamel_gueH_measurable_filt sz t1 t0 K n k
  have hYmeas' : Measurable (gueH sz t1 t0 K n k) := hYmeas.mono ((filt sz).le k) le_rfl
  have hIntTarget : Integrable (fun ω : PathΩ sz => F (gueH sz t1 t0 K n k ω) (ω (k + 1)))
      (Pgue sz) := by
    have hm : Measurable (fun ω : PathΩ sz => F (gueH sz t1 t0 K n k ω) (ω (k + 1))) := by
      have h := hFmeas.comp (hYmeas'.prodMk (measurable_pi_apply (k + 1)))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hfreeze := DuhamelA2_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget
  have hsucc : ∀ ω : PathΩ sz, gueH sz t1 t0 K n (k + 1) ω
      = gueH sz t1 t0 K n k ω + Sizes.seqHflow sz n v (ω (k + 1)) :=
    fun ω => gueH_succ sz t1 t0 K n k ω
  have hEq : (fun ω' : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (k + 1) ω'))
          z1 I)
      = fun ω => F (gueH sz t1 t0 K n k ω) (ω (k + 1)) := by
    funext ω
    have hH : (gueH sz t1 t0 K n (k + 1) ω).IsHermitian := gueH_isHermitian sz t1 t0 K n (k + 1) ω
    simp only [hF, DuhamelA2_Phi]
    rw [← hsucc ω, DuhamelA2_herm_of_isHermitian hH]
  have hD3 := condExp_loop_drift_gue sz t1 t0 K n k e he hwf ht1 hst (by omega) hk hu1lt
  rw [hEq] at hD3
  filter_upwards [hD3, hfreeze] with ω h1 h2
  rw [h2] at h1
  have hFeq : ∀ y, F (gueH sz t1 t0 K n k ω) y = loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω + Sizes.seqHflow sz n v y)) z1 I := by
    intro y
    have hh : (gueH sz t1 t0 K n k ω + Sizes.seqHflow sz n v y).IsHermitian :=
      (gueH_isHermitian sz t1 t0 K n k ω).add (Sizes.seqHflow_isHermitian sz n v y)
    simp only [hF, DuhamelA2_Phi]
    rw [DuhamelA2_herm_of_isHermitian hh]
  simp only [hFeq] at h1
  exact h1

end Grid

/-! ### 8. Compiled nonempty instances

Namespace `RBM.Univ.GUEPhase.DuhamelA2Inst`.  Data: `sz0` of `RBM3D/Defs/Sizes.lean` (`d = 3`, `L_0 = 4`,
`W_0 = 32`, `N = (W L)^d = 2097152`), size index `n = 0`.

* `Duhamel_measurableSet_good`: at `sz0`, `n = 0`; the set contains `0` and misses a point of
  entry `N + 1` (`zero_mem_good`, `exists_not_mem_good`).
* `Duhamel_drift_remainder_ae`: the `Grid.lean` §`GridCheck` data `t₀ = 9/10`, `t₁ = (1 - ζ(1/20)) t₀`,
  `K = 4`, `k = 0`, `e = 0`, the two-loop `(+,-; 0, 1)` (`0 ≠ 1` in `Z_4^3`, `labels_sz0`); every
  deterministic hypothesis is discharged: `|e| < 2`, `I.WF`, `0 ≤ t₁`, `t₁ ≤ t₀`, `t₀ < 1`, `k < K`.
* the other targets: the observable `Φ(A) = sin (Re tr A)` (`C₂ = ‖Re tr‖²`, `C₀ = 1`; a copy of the
  private `StepDecomp_check_class`, `StepDecomp_check_hC₂`), `v = 1/4`, `M = 0`. -/

end RBM.Univ.GUEPhase

namespace RBM.Univ.GUEPhase.DuhamelA2Inst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
  RBM.Gauss.SizesInst RBM.Univ.GUEPhase
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! #### `Duhamel_measurableSet_good` -/

/-- `0 ∈ DuhamelGood sz0 0`. -/
theorem zero_mem_good : (0 : Sizes.SeqΩ sz0) ∈ DuhamelGood sz0 0 := by
  intro i l
  have h : Sizes.seqXmat sz0 0 (0 : Sizes.SeqΩ sz0) i l = 0 := by
    simp [Sizes.seqXmat, Sizes.slice, Xmat, Xentry]
  rw [h, norm_zero]
  positivity

/-- A point with the entry `(0, 0)` equal to `N + 1` is outside `DuhamelGood sz0 0`. -/
theorem exists_not_mem_good : ∃ y : Sizes.SeqΩ sz0, y ∉ DuhamelGood sz0 0 := by
  classical
  refine ⟨Function.update 0 ⟨0, ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)),
    true)⟩ (((sz0.size 0 : ℕ) : ℝ) + 1), fun h => ?_⟩
  have h0 := h 0 0
  have e : Sizes.seqXmat sz0 0 (Function.update (0 : Sizes.SeqΩ sz0)
      ⟨0, ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)), true)⟩
      (((sz0.size 0 : ℕ) : ℝ) + 1)) 0 0 = ((((sz0.size 0 : ℕ) : ℝ) + 1 : ℝ) : ℂ) := by
    simp [Sizes.seqXmat, Sizes.slice, Xmat, Xentry]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h0
  linarith

/-- `Duhamel_measurableSet_good` at `sz0`, `n = 0`: a measurable set that is neither empty nor
everything. -/
theorem measurableSet_good_check :
    MeasurableSet (DuhamelGood sz0 0) ∧ (0 : Sizes.SeqΩ sz0) ∈ DuhamelGood sz0 0 ∧
      ∃ y : Sizes.SeqΩ sz0, y ∉ DuhamelGood sz0 0 :=
  ⟨Duhamel_measurableSet_good, zero_mem_good, exists_not_mem_good⟩

/-! #### `Duhamel_drift_remainder_ae` -/

/-- The two-loop `(+,-; a₁, a₂)`. -/
private def DuhamelA2Inst_loop2 (L : ℕ) (a₁ a₂ : Zd 3 L) : Loop.LoopIdx (Zd 3 L) :=
  ⟨[true, false], [a₁, a₂]⟩

private theorem DuhamelA2Inst_loop2_wf (L : ℕ) (a₁ a₂ : Zd 3 L) :
    (DuhamelA2Inst_loop2 L a₁ a₂).WF := rfl

/-- The two labels of the instance loop differ (`0 ≠ 1` in `Z_4^3`; `Drift.lean`). -/
theorem labels_sz0 : (0 : Zd 3 (sz0.L 0)) ≠ 1 := DriftInst.labels_sz0

private abbrev DuhamelA2Inst_t1 : ℕ → ℝ := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)

private abbrev DuhamelA2Inst_t0 : ℕ → ℝ := fun _ => 9 / 10

private abbrev DuhamelA2Inst_K : ℕ → ℕ := fun _ => 4

private theorem DuhamelA2Inst_t1_nonneg : 0 ≤ DuhamelA2Inst_t1 0 := by
  unfold DuhamelA2Inst_t1 ouZeta
  have := Real.exp_pos (-(1 / 20 : ℝ))
  nlinarith

private theorem DuhamelA2Inst_t1_le_t0 : DuhamelA2Inst_t1 0 ≤ DuhamelA2Inst_t0 0 := by
  unfold DuhamelA2Inst_t1 DuhamelA2Inst_t0 ouZeta
  have : Real.exp (-(1 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  nlinarith

/-- `Duhamel_drift_remainder_ae` at `sz0`, `n = 0`, `k = 0`, `e = 0`, loop `(+,-; 0, 1)`: the
integral over one unit-GUE increment, against the loop and its drift. -/
theorem drift_remainder_ae_check :
    ∀ᵐ ω ∂(Pgue sz0),
      ‖(∫ y, loopL 3 (sz0.L 0) (sz0.W 0)
            (blockMat 3 (sz0.L 0) (sz0.W 0) (gueH sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0
              DuhamelA2Inst_K 0 0 ω
              + Sizes.seqHflow sz0 0 (gridStep DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0
                / ((sz0.size 0 : ℕ) : ℝ)) y))
            (zt 0 (gridTime DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 (0 + 1)))
            (DuhamelA2Inst_loop2 (sz0.L 0) 0 1) ∂(gueUnit sz0))
          - loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
              (gueH sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0 ω))
              (zt 0 (gridTime DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0))
              (DuhamelA2Inst_loop2 (sz0.L 0) 0 1)
          - (gridStep DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 : ℂ) *
              genMatGUE 3 (sz0.L 0) (sz0.W 0) 0
                (gridTime DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0)
                (gueH sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0 ω)
                (DuhamelA2Inst_loop2 (sz0.L 0) 0 1)‖
        ≤ envConst 3 (sz0.L 0) (sz0.W 0) 0 (DuhamelA2Inst_loop2 (sz0.L 0) 0 1).length
            (gridTime DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 (0 + 1))
          * gridStep DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 ^ ((3 : ℝ) / 2) :=
  Duhamel_drift_remainder_ae sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0 0
    (by norm_num) (DuhamelA2Inst_loop2_wf _ 0 1) DuhamelA2Inst_t1_nonneg DuhamelA2Inst_t1_le_t0
    (by norm_num [DuhamelA2Inst_t0]) (by norm_num [DuhamelA2Inst_K])

/-! #### The one-step targets at `Φ(A) = sin (Re tr A)` -/

section SinObservable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuous real-linear functional `Re tr` (copy of `StepDecomp_g`, `StepDecomp.lean:1346`). -/
private def DuhamelA2Inst_g (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (Matrix.trace A).re
      map_add' := fun A B => by simp
      map_smul' := fun r A => by simp }

/-- The bounded observable `A ↦ sin (Re tr A)`. -/
private def DuhamelA2Inst_Φ (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ → ℂ :=
  fun A => (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)

private theorem DuhamelA2Inst_continuous_Φ (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Continuous (DuhamelA2Inst_Φ ι) :=
  Complex.continuous_ofReal.comp (Real.continuous_sin.comp (DuhamelA2Inst_g ι).continuous)

private theorem DuhamelA2Inst_hasFDerivAt (M : Matrix ι ι ℂ) :
    HasFDerivAt (DuhamelA2Inst_Φ ι)
      (Complex.ofRealCLM.comp (Real.cos (DuhamelA2Inst_g ι M) • DuhamelA2Inst_g ι)) M :=
  Complex.ofRealCLM.hasFDerivAt.comp M ((DuhamelA2Inst_g ι).hasFDerivAt.sin)

private theorem DuhamelA2Inst_fderiv :
    fderiv ℝ (DuhamelA2Inst_Φ ι)
      = fun M => Real.cos (DuhamelA2Inst_g ι M) • Complex.ofRealCLM.comp (DuhamelA2Inst_g ι) := by
  funext M
  rw [(DuhamelA2Inst_hasFDerivAt M).fderiv, ContinuousLinearMap.comp_smul]

private theorem DuhamelA2Inst_fderiv2 (M y : Matrix ι ι ℂ) :
    fderiv ℝ (fderiv ℝ (DuhamelA2Inst_Φ ι)) M y y
      = ((-Real.sin (DuhamelA2Inst_g ι M) * DuhamelA2Inst_g ι y * DuhamelA2Inst_g ι y : ℝ) : ℂ) := by
  rw [DuhamelA2Inst_fderiv]
  have h : HasFDerivAt (fun M : Matrix ι ι ℂ =>
      Real.cos (DuhamelA2Inst_g ι M) • Complex.ofRealCLM.comp (DuhamelA2Inst_g ι))
      ((-Real.sin (DuhamelA2Inst_g ι M) • DuhamelA2Inst_g ι).smulRight
        (Complex.ofRealCLM.comp (DuhamelA2Inst_g ι))) M :=
    ((DuhamelA2Inst_g ι).hasFDerivAt.cos).smul_const (Complex.ofRealCLM.comp (DuhamelA2Inst_g ι))
  rw [h.fderiv]
  simp

/-- (H3): `‖∂²Φ(M)[y, y]‖ ≤ ‖Re tr‖² ‖y‖²` (copy of `StepDecomp_check_hC₂`). -/
private theorem DuhamelA2Inst_hC₂ (M y : Matrix ι ι ℂ) :
    ‖fderiv ℝ (fderiv ℝ (DuhamelA2Inst_Φ ι)) M y y‖ ≤ ‖DuhamelA2Inst_g ι‖ ^ 2 * ‖y‖ ^ 2 := by
  have h1 : |DuhamelA2Inst_g ι y| ≤ ‖DuhamelA2Inst_g ι‖ * ‖y‖ := by
    simpa [Real.norm_eq_abs] using (DuhamelA2Inst_g ι).le_opNorm y
  rw [DuhamelA2Inst_fderiv2, Complex.norm_real, Real.norm_eq_abs]
  set g := DuhamelA2Inst_g ι y
  calc |-Real.sin (DuhamelA2Inst_g ι M) * g * g|
      = |Real.sin (DuhamelA2Inst_g ι M)| * (|g| * |g|) := by
        rw [abs_mul, abs_mul, abs_neg]; ring
    _ ≤ 1 * (|g| * |g|) := by gcongr; exact Real.abs_sin_le_one _
    _ ≤ (‖DuhamelA2Inst_g ι‖ * ‖y‖) * (‖DuhamelA2Inst_g ι‖ * ‖y‖) := by
        rw [one_mul]; gcongr
    _ = ‖DuhamelA2Inst_g ι‖ ^ 2 * ‖y‖ ^ 2 := by ring

/-- (H1), (H2): `Φ` is `C²` and bounded by `1`. -/
private theorem DuhamelA2Inst_class (n : ℕ) {d : ℕ} (sz : Sizes d) :
    HermTestFun sz n (DuhamelA2Inst_Φ (Idx d (sz.L n) (sz.W n))) where
  contDiffAt M _ := (Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_sin.comp (DuhamelA2Inst_g (Idx d (sz.L n) (sz.W n))).contDiff)).contDiffAt
  bdd₀ := ⟨1, fun M _ => by
    change ‖(((Real.sin (Matrix.trace M).re : ℝ)) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _⟩

end SinObservable

/-- `Duhamel_Z_re_im` at `Φ = sin (Re tr)`, `v = 1/4`, `M = 0`, every `y`. -/
theorem Z_re_im_check (y : Sizes.SeqΩ sz0) :
    (DuhamelZ sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 y).re
        = Real.sqrt (1 / 4) * linTr 0 (gradMat (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) 0)
            (Sizes.seqXmat sz0 0 y) ∧
      (DuhamelZ sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 y).im
        = Real.sqrt (1 / 4) * linTr 0
            (-Complex.I • gradMat (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) 0)
            (Sizes.seqXmat sz0 0 y) :=
  Duhamel_Z_re_im _ 0 y

/-- `Duhamel_measurable_R` at `Φ = sin (Re tr)` (measurable: continuous), `v = 1/4`. -/
theorem measurable_R_check :
    Measurable (fun p : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ ×
        Sizes.SeqΩ sz0 => DuhamelR sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4)
          p.1 p.2) :=
  Duhamel_measurable_R (by
    exact (DuhamelA2Inst_continuous_Φ _).measurable) (1 / 4)

/-- `Duhamel_integral_step` at `Φ = sin (Re tr)`, `C₂ = ‖Re tr‖²`, `v = 1/4`, `M = 0`. -/
theorem integral_step_check :
    ∫ y, DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))
        (0 + Sizes.seqHflow sz0 0 (1 / 4) y) ∂(gueUnit sz0)
      = DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0)) 0
        + ∫ y, DuhamelT sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 y ∂(gueUnit sz0)
        + DuhamelB sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 :=
  Duhamel_integral_step (DuhamelA2Inst_class 0 sz0)
    (C₂ := ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2) (fun M y _ _ => DuhamelA2Inst_hC₂ M y)
    (1 / 4) Matrix.isHermitian_zero

/-- `Duhamel_norm_T_le` at the same data, every `y`. -/
theorem norm_T_le_check (y : Sizes.SeqΩ sz0) :
    ‖DuhamelT sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 y‖
      ≤ ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2 / 2 * (1 / 4)
        * ((sz0.size 0 : ℕ) : ℝ) ^ 4 :=
  Duhamel_norm_T_le (DuhamelA2Inst_class 0 sz0)
    (C₂ := ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2) (fun M y _ _ => DuhamelA2Inst_hC₂ M y)
    (by norm_num) Matrix.isHermitian_zero y

/-- `Duhamel_norm_B_le` at the same data. -/
theorem norm_B_le_check :
    ‖DuhamelB sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0‖
      ≤ 16 * Real.exp 2 * ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2 * (1 / 4)
        * ((sz0.size 0 : ℕ) : ℝ) ^ 4 * Real.exp (-((sz0.size 0 : ℕ) : ℝ) / 4) :=
  Duhamel_norm_B_le (DuhamelA2Inst_class 0 sz0)
    (C₂ := ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2) (fun M y _ _ => DuhamelA2Inst_hC₂ M y)
    (by norm_num) Matrix.isHermitian_zero

/-- `Duhamel_measurable_loop` at `d = 3`, `L = W = 2`, `z = i`, the two-loop `(+,-; 0, 1)`. -/
theorem measurable_loop_check :
    Measurable (fun M : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ =>
      loopL 3 2 2 (blockMat 3 2 2 M) Complex.I ⟨[true, false], [(0 : Zd 3 2), 1]⟩) :=
  Duhamel_measurable_loop Complex.I ⟨[true, false], [(0 : Zd 3 2), 1]⟩

/-- `Duhamel_measurable_coord` at `sz0`: the draw `ω 0` is `filt sz0 1`-measurable. -/
theorem measurable_coord_check : Measurable[filt sz0 1] (fun ω : PathΩ sz0 => ω 0) :=
  Duhamel_measurable_coord sz0 (by norm_num)

/-- `Duhamel_gueH_measurable_filt` at `sz0`, `n = 0`, `k = 4`, the `Grid.lean` data. -/
theorem gueH_measurable_filt_check :
    Measurable[filt sz0 4]
      (gueH sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 4) :=
  Duhamel_gueH_measurable_filt sz0 _ _ _ 0 4

end RBM.Univ.GUEPhase.DuhamelA2Inst

end
