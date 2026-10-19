/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.GLoopFlow
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The flow calculus

The deterministic calculus along the single-time Gaussian flow, in the vocabulary of
`RBM3D.Gauss.FineModel`, `RBM3D.Loop.GLoopFlow` and `RBM3D.Defs.Semicircle`: `mE` is the bulk
value `m^(E)`, `zt` the spectral path, `Gres H z σ` the resolvent of either sign,
`loopL d L W H z I` the loop, `Vtx d L W` the block-product index, `blockMat d L W` the block
reindexing of a matrix on the fine lattice, and `Ω d L W`, `PF d L W g` the one-size sample space
and law.

Everything here is deterministic along the single-time flow `H_u = √u X`
(`Hflow = √u • Xmat`, a coupling across times, not a matrix Brownian motion): spectral window
and derivative of `z_u = E + (1-u) m`, samplewise time and sample continuity of `G_u` and of the
`G`-loops, the fixed-sample derivative of loops along the flow, and the crude whole-space loop
envelope `(L W)^d (η⁻¹ W^{-d})^n`.  The only dimension-dependent statements are the envelope
(`W^{-d}`, `(L W)^d`) and the loop index types.
-/

noncomputable section

open MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator

namespace RBM.Gauss

/-! ## 1. The spectral path on a compact time window -/

section Spectral

/-- The explicit bulk value `mE E` has positive imaginary part for `|E| < 2`. -/
theorem spectralM_im_pos {E : ℝ} (hE : |E| < 2) : 0 < (mE E).im := mE_im_pos hE

/-- The imaginary part of `zt E u` is `(1 - u)` times that of `mE E`. -/
theorem spectralZ_im (E u : ℝ) : (zt E u).im = (1 - u) * (mE E).im := zt_im E u

/-- The spectral path `zt E` is continuous in time. -/
theorem continuous_spectralZ (E : ℝ) : Continuous (zt E) := by
  unfold zt
  fun_prop

/-- A uniform non-real gap on `[s,t]`, with the minimum attained at `t`. -/
theorem spectralZ_im_gap {E s t : ℝ} (hE : |E| < 2) (ht : t < 1)
    {u : ℝ} (hu : u ∈ Set.Icc s t) :
    (1 - t) * (mE E).im ≤ |(zt E u).im| := by
  rw [spectralZ_im, abs_of_pos (mul_pos (by linarith [hu.2]) (spectralM_im_pos hE))]
  exact mul_le_mul_of_nonneg_right (by linarith [hu.2]) (spectralM_im_pos hE).le

/-- The explicit bulk value solves the semicircle quadratic equation. -/
theorem spectralM_mul {E : ℝ} (hE : |E| ≤ 2) : mE E * (mE E + E) = -1 := mE_mul hE

/-- Equivalent monic quadratic equation `m² + E m + 1 = 0`. -/
theorem spectralM_quadratic {E : ℝ} (hE : |E| ≤ 2) :
    mE E ^ 2 + E * mE E + 1 = 0 := by
  have h := spectralM_mul hE
  linear_combination h

/-- The explicit bulk value lies on the unit circle. -/
theorem norm_spectralM {E : ℝ} (hE : |E| ≤ 2) : ‖mE E‖ = 1 := norm_mE hE

/-- The spectral path has constant complex derivative `-m^(E)`. -/
theorem hasDerivAt_spectralZ (E u : ℝ) : HasDerivAt (zt E) (-(mE E)) u := by
  have h : HasDerivAt (fun v : ℝ => v • (-(mE E) : ℂ)) (-(mE E)) u := by
    simpa using (hasDerivAt_id u).smul_const (-(mE E) : ℂ)
  have hsum := h.const_add ((E : ℂ) + mE E)
  have hfun : zt E = fun v : ℝ => ((E : ℂ) + mE E) + v • (-(mE E) : ℂ) := by
    funext v
    simp only [zt, Complex.real_smul]
    ring
  rw [hfun]
  exact hsum

end Spectral

/-! ## 2. Samplewise time continuity of the flow, of the resolvent and of the loops -/

section FlowTime

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- For each fixed Gaussian sample, the entire matrix flow is continuous in time. -/
theorem continuous_Hflow_time (ω : Ω d L W) :
    Continuous fun u : ℝ => Hflow d L W u ω := by
  change Continuous fun u : ℝ => (Real.sqrt u : ℂ) • Xmat d L W ω
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).smul continuous_const

end FlowTime

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- The common-probability-space flow is continuous in time at each fixed size and sample. -/
theorem continuous_seqHflow_time (n : ℕ) (ω : SeqΩ sz) :
    Continuous fun u : ℝ => seqHflow sz n u ω := by
  change Continuous fun u : ℝ => Hflow d (sz.L n) (sz.W n) u (slice sz n ω)
  exact continuous_Hflow_time _ _ _ _

/-- Entrywise time continuity on the common probability space. -/
theorem continuous_seqHflow_entry_time (n : ℕ) (ω : SeqΩ sz)
    (i j : Idx d (sz.L n) (sz.W n)) :
    Continuous fun u : ℝ => seqHflow sz n u ω i j :=
  (continuous_apply j).comp ((continuous_apply i).comp (continuous_seqHflow_time sz n ω))

end Sizes

section GreenCont

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Joint path continuity of the resolvent when both the Hermitian matrix and the non-real
spectral parameter vary continuously. -/
theorem continuous_green_of_isHermitian_moving {V : Type*} [TopologicalSpace V]
    {f : V → Matrix n n ℂ} (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian)
    {z : V → ℂ} (hzcont : Continuous z) (hzim : ∀ v, (z v).im ≠ 0) :
    Continuous fun v => Gres (f v) (z v) true := by
  rw [continuous_iff_continuousAt]
  intro v
  have hU : IsUnit (f v - z v • (1 : Matrix n n ℂ)) :=
    isUnit_sub_smul_of_isHermitian (hherm v) (hzim v)
  have hspec : ((hU.unit : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
      = f v - z v • (1 : Matrix n n ℂ) := IsUnit.unit_spec _
  have h1 : ContinuousAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (f v - z v • (1 : Matrix n n ℂ)) := by
    rw [← hspec]
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit).continuousAt
  have h2 : ContinuousAt (fun w => f w - z w • (1 : Matrix n n ℂ)) v :=
    hf.continuousAt.sub (hzcont.continuousAt.smul continuousAt_const)
  have := ContinuousAt.comp (g := Ring.inverse (M₀ := Matrix n n ℂ))
    (f := fun w => f w - z w • (1 : Matrix n n ℂ)) h1 h2
  simpa [Gres, Function.comp_def] using this

/-- The resolvent depends continuously on a continuously varying Hermitian matrix path, for a
fixed spectral parameter off the real axis. -/
theorem continuous_green_of_isHermitian {V : Type*} [TopologicalSpace V]
    {f : V → Matrix n n ℂ} (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) : Continuous fun v => Gres (f v) z true :=
  continuous_green_of_isHermitian_moving hf hherm continuous_const fun _ => hz

end GreenCont

section GreenTime

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The samplewise resolvent stays continuous when the spectral parameter follows any continuous
path in the upper or lower half-plane. -/
theorem continuous_green_Hflow_moving_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) :
    Continuous fun u : ℝ => Gres (Hflow d L W u ω) (z u) true :=
  continuous_green_of_isHermitian_moving (continuous_Hflow_time d L W ω)
    (fun u => Hflow_isHermitian d L W u ω) hzcont hzim

/-! ### The flow on the block-product index -/

/-- The fine-lattice flow reindexed by the paper's block and within-block coordinates
(through `blockMat`). -/
noncomputable def HflowBlock (u : ℝ) (ω : Ω d L W) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  blockMat d L W (Hflow d L W u ω)

/-- The reindexed flow is continuous in time. -/
theorem continuous_HflowBlock_time (ω : Ω d L W) :
    Continuous fun u : ℝ => HflowBlock d L W u ω :=
  (continuous_Hflow_time d L W ω).matrix_submatrix _ _

/-- The reindexed flow is Hermitian. -/
theorem HflowBlock_isHermitian (u : ℝ) (ω : Ω d L W) :
    (HflowBlock d L W u ω).IsHermitian :=
  (Hflow_isHermitian d L W u ω).submatrix _

/-- The reindexed flow has a continuous Green matrix for a moving non-real parameter. -/
theorem continuous_green_HflowBlock_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) :
    Continuous fun u : ℝ => Gres (HflowBlock d L W u ω) (z u) true :=
  continuous_green_of_isHermitian_moving (continuous_HflowBlock_time d L W ω)
    (fun u => HflowBlock_isHermitian d L W u ω) hzcont hzim

/-- Either spectral sign gives a continuous Green matrix along the fixed-sample flow. -/
theorem continuous_Gsig_Hflow_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) (σ : Bool) :
    Continuous fun u : ℝ => Gres (HflowBlock d L W u ω) (z u) σ := by
  cases σ with
  | true =>
      exact continuous_green_HflowBlock_time d L W ω hzcont hzim
  | false =>
      have hzconj : Continuous (fun u => (starRingEnd ℂ) (z u)) :=
        Complex.continuous_conj.comp hzcont
      have hzimconj : ∀ u, ((starRingEnd ℂ) (z u)).im ≠ 0 := by
        intro u
        simpa using hzim u
      have h := continuous_green_HflowBlock_time d L W ω hzconj hzimconj
      simpa [Gres] using h

/-- A finite list of signed Green factors and block insertions has a continuous product. -/
theorem continuous_foldr_Hflow_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0)
    (l : List (Bool × Zd d L)) :
    Continuous fun u : ℝ =>
      l.foldr (fun p M => Gres (HflowBlock d L W u ω) (z u) p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact ((continuous_Gsig_Hflow_time d L W ω hzcont hzim p.1).mul
        continuous_const).mul ih

/-- Continuity of the full finite loop word. -/
theorem continuous_gloopProd_Hflow_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) :
    Continuous fun u : ℝ => gloopProd d L W (HflowBlock d L W u ω) (z u) I :=
  continuous_foldr_Hflow_time d L W ω hzcont hzim (I.σ.zip I.a)

omit [NeZero W] in
/-- The trace of a finite complex matrix depends continuously on the matrix. -/
theorem continuous_matrixTrace :
    Continuous (Matrix.trace : Matrix (Vtx d L W) (Vtx d L W) ℂ → ℂ) :=
  LinearMap.continuous_of_finiteDimensional (Matrix.traceLinearMap (Vtx d L W) ℂ ℂ)

/-! ### Sample continuity and measurability at a fixed time -/

/-- Reindexing preserves continuity of the matrix flow as a function of the sample. -/
theorem continuous_HflowBlock_sample (u : ℝ) : Continuous (HflowBlock d L W u) :=
  (continuous_Hflow d L W u).matrix_submatrix _ _

/-- The fixed-parameter Green matrix is continuous in the Gaussian sample. -/
theorem continuous_green_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω d L W => Gres (HflowBlock d L W u ω) z true :=
  continuous_green_of_isHermitian (continuous_HflowBlock_sample d L W u)
    (fun ω => HflowBlock_isHermitian d L W u ω) hz

/-- Both signed resolvents are continuous in the sample. -/
theorem continuous_Gsig_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Continuous fun ω : Ω d L W => Gres (HflowBlock d L W u ω) z σ := by
  cases σ with
  | true => exact continuous_green_HflowBlock_sample d L W u hz
  | false =>
      have h := continuous_green_HflowBlock_sample d L W u (z := (starRingEnd ℂ) z)
        (by simpa using hz)
      simpa [Gres] using h

/-- The finite loop word is continuous in the Gaussian sample. -/
theorem continuous_foldr_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × Zd d L)) :
    Continuous fun ω : Ω d L W =>
      l.foldr (fun p M => Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact ((continuous_Gsig_HflowBlock_sample d L W u hz p.1).mul
        continuous_const).mul ih

/-- Sample continuity of the complete matrix product. -/
theorem continuous_gloopProd_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) :
    Continuous fun ω : Ω d L W => gloopProd d L W (HflowBlock d L W u ω) z I :=
  continuous_foldr_HflowBlock_sample d L W u hz (I.σ.zip I.a)

/-- A well-formed resolvent loop is continuous in the Gaussian sample at fixed time. -/
theorem continuous_gloop_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (_hwf : I.WF) :
    Continuous fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z I :=
  (continuous_matrixTrace d L W).comp
    (continuous_gloopProd_HflowBlock_sample d L W u hz I)

/-- The fixed-time loop is measurable under the Gaussian product law. -/
theorem measurable_gloop_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    Measurable fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z I :=
  (continuous_gloop_HflowBlock_sample d L W u hz I hwf).measurable

end GreenTime

/-! ## 3. Derivatives along the samplewise spectral flow -/

section Derivative

section Green

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Chain rule for a non-real resolvent with both matrix and spectral parameter moving. -/
theorem hasDerivAt_green_moving {H : ℝ → Matrix n n ℂ} {z : ℝ → ℂ}
    {H' : Matrix n n ℂ} {z' : ℂ} {u : ℝ}
    (hH : HasDerivAt H H' u) (hz : HasDerivAt z z' u)
    (hHerm : (H u).IsHermitian) (him : (z u).im ≠ 0) :
    HasDerivAt (fun v : ℝ => Gres (H v) (z v) true)
      (-(Gres (H u) (z u) true * (H' - z' • (1 : Matrix n n ℂ)) *
        Gres (H u) (z u) true)) u := by
  have hU : IsUnit (H u - z u • (1 : Matrix n n ℂ)) :=
    isUnit_sub_smul_of_isHermitian hHerm him
  set U : (Matrix n n ℂ)ˣ := hU.unit with hUdef
  have hus : (U : Matrix n n ℂ) = H u - z u • (1 : Matrix n n ℂ) :=
    IsUnit.unit_spec _
  have hG : ∀ v : ℝ, Gres (H v) (z v) true = Ring.inverse (H v - z v • (1 : Matrix n n ℂ)) := by
    intro v
    simp [Gres]
  have hinv : ((U⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = Gres (H u) (z u) true := by
    rw [hG, ← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹)
      (H u - z u • (1 : Matrix n n ℂ)) := by
    rw [← hus]
    exact hasFDerivAt_ringInverse U
  have hpath : HasDerivAt (fun v : ℝ => H v - z v • (1 : Matrix n n ℂ))
      (H' - z' • (1 : Matrix n n ℂ)) u :=
    hH.sub (hz.smul_const (1 : Matrix n n ℂ))
  have hcomp := hF.comp_hasDerivAt u hpath
  have hval :
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹)
        (H' - z' • (1 : Matrix n n ℂ)) =
      -(Gres (H u) (z u) true * (H' - z' • (1 : Matrix n n ℂ)) *
        Gres (H u) (z u) true) := by
    simp [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hinv]
  rw [hval] at hcomp
  have hfun : (fun v : ℝ => Gres (H v) (z v) true) =
      (Ring.inverse (M₀ := Matrix n n ℂ)) ∘
        (fun v : ℝ => H v - z v • (1 : Matrix n n ℂ)) := by
    funext v
    exact hG v
  rw [hfun]
  exact hcomp

end Green

section LoopDeriv

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The reindexed Gaussian flow has the same square-root derivative. -/
theorem hasDerivAt_HflowBlock_time (ω : Ω d L W) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => HflowBlock d L W v ω)
      ((1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω)) u := by
  have hfun : (fun v : ℝ => HflowBlock d L W v ω) =
      fun v : ℝ => Real.sqrt v • blockMat d L W (Xmat d L W ω) := by
    funext v
    ext i j
    simp [HflowBlock, blockMat, Hflow_eq_realSmul]
  rw [hfun]
  exact (Real.hasDerivAt_sqrt hu.ne').smul_const _

/-- Fixed-sample Green derivative along `H_u=√u X` and `z_u=E+(1-u)m^(E)`.
The sign follows from differentiating `(H_u-z_u I)⁻¹`.  The block reindexing of `Xmat ω` is
written `blockMat d L W (Xmat ω)`. -/
theorem hasDerivAt_green_HflowBlock_spectralZ (ω : Ω d L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt
      (fun v : ℝ => Gres (HflowBlock d L W v ω) (zt E v) true)
      (-(Gres (HflowBlock d L W u ω) (zt E u) true *
        ((1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω) +
          mE E • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        Gres (HflowBlock d L W u ω) (zt E u) true)) u := by
  have him : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have h := hasDerivAt_green_moving
    (hasDerivAt_HflowBlock_time d L W ω hu)
    (hasDerivAt_spectralZ E u)
    (HflowBlock_isHermitian d L W u ω) him
  simpa only [neg_smul, sub_neg_eq_add] using h

/-- The spectral drift for either Green sign: `m^(E)` for `σ = true` and its complex conjugate
otherwise. -/
noncomputable def spectralMSign (E : ℝ) (σ : Bool) : ℂ :=
  if σ then mE E else (starRingEnd ℂ) (mE E)

/-- The derivative of one signed Green factor along the samplewise flow. -/
noncomputable def gsigFlowDeriv (ω : Ω d L W) (E u : ℝ) (σ : Bool) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  let G := Gres (HflowBlock d L W u ω) (zt E u) σ;
  let X := blockMat d L W (Xmat d L W ω);
  -(G * ((1 / (2 * Real.sqrt u)) • X +
      spectralMSign E σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G)

/-- Each signed resolvent has the stated fixed-sample derivative. -/
theorem hasDerivAt_Gsig_HflowBlock_spectralZ (ω : Ω d L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) (σ : Bool) :
    HasDerivAt
      (fun v : ℝ => Gres (HflowBlock d L W v ω) (zt E v) σ)
      (gsigFlowDeriv d L W ω E u σ) u := by
  cases σ with
  | true =>
      simpa only [gsigFlowDeriv, spectralMSign, ite_true] using
        hasDerivAt_green_HflowBlock_spectralZ d L W ω hE hu hu1
  | false =>
      have hz : HasDerivAt
          (fun v : ℝ => (starRingEnd ℂ) (zt E v))
          (-((starRingEnd ℂ) (mE E))) u := by
        simpa using (hasDerivAt_spectralZ E u).star
      have him : ((starRingEnd ℂ) (zt E u)).im ≠ 0 := by
        have hpos : (zt E u).im ≠ 0 := by
          rw [spectralZ_im]
          exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
        simpa using hpos
      have h := hasDerivAt_green_moving
        (hasDerivAt_HflowBlock_time d L W ω hu) hz
        (HflowBlock_isHermitian d L W u ω) him
      have hGf : ∀ v : ℝ, Gres (HflowBlock d L W v ω) (zt E v) false =
          Gres (HflowBlock d L W v ω) ((starRingEnd ℂ) (zt E v)) true := by
        intro v
        simp [Gres]
      have hfun : (fun v : ℝ => Gres (HflowBlock d L W v ω) (zt E v) false) =
          fun v : ℝ => Gres (HflowBlock d L W v ω) ((starRingEnd ℂ) (zt E v)) true :=
        funext hGf
      rw [hfun]
      simpa only [gsigFlowDeriv, spectralMSign, hGf, Bool.false_eq_true, ↓reduceIte,
        neg_smul, sub_neg_eq_add] using h

/-- Recursive Leibniz derivative of the signed Green/block word. -/
noncomputable def loopWordDeriv (ω : Ω d L W) (E u : ℝ) :
    List (Bool × Zd d L) → Matrix (Vtx d L W) (Vtx d L W) ℂ
  | [] => 0
  | p :: l =>
      (gsigFlowDeriv d L W ω E u p.1 * Eblk d L W p.2) *
        l.foldr (fun q M => Gres (HflowBlock d L W u ω) (zt E u) q.1 *
          Eblk d L W q.2 * M) 1 +
      (Gres (HflowBlock d L W u ω) (zt E u) p.1 * Eblk d L W p.2) *
        loopWordDeriv ω E u l

/-- List induction proves the product rule for every finite signed word. -/
theorem hasDerivAt_loopWord_HflowBlock_spectralZ (ω : Ω d L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (l : List (Bool × Zd d L)) :
    HasDerivAt
      (fun v : ℝ => l.foldr (fun p M =>
        Gres (HflowBlock d L W v ω) (zt E v) p.1 * Eblk d L W p.2 * M) 1)
      (loopWordDeriv d L W ω E u l) u := by
  induction l with
  | nil =>
      simpa only [List.foldr_nil, loopWordDeriv] using
        hasDerivAt_const u (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have hhead :=
        (hasDerivAt_Gsig_HflowBlock_spectralZ d L W ω hE hu hu1 p.1).mul_const
          (Eblk d L W p.2)
      have h := hhead.mul ih
      have hfun :
          (fun v : ℝ => Gres (HflowBlock d L W v ω) (zt E v) p.1 *
            Eblk d L W p.2) *
            (fun v : ℝ => l.foldr (fun q M =>
              Gres (HflowBlock d L W v ω) (zt E v) q.1 * Eblk d L W q.2 * M) 1) =
          (fun v : ℝ => Gres (HflowBlock d L W v ω) (zt E v) p.1 *
            Eblk d L W p.2 *
            l.foldr (fun q M =>
              Gres (HflowBlock d L W v ω) (zt E v) q.1 * Eblk d L W q.2 * M) 1) := by
        funext v
        rfl
      rw [hfun] at h
      simpa only [List.foldr_cons, loopWordDeriv] using h

/-- The matrix-product form of the loop derivative. -/
theorem hasDerivAt_gloopProd_HflowBlock_spectralZ (ω : Ω d L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (_hwf : I.WF) :
    HasDerivAt
      (fun v : ℝ => gloopProd d L W (HflowBlock d L W v ω) (zt E v) I)
      (loopWordDeriv d L W ω E u (I.σ.zip I.a)) u :=
  hasDerivAt_loopWord_HflowBlock_spectralZ d L W ω hE hu hu1 (I.σ.zip I.a)

/-- Taking the trace gives the fixed-sample derivative of the complete loop. -/
theorem hasDerivAt_gloop_HflowBlock_spectralZ (ω : Ω d L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    HasDerivAt
      (fun v : ℝ => loopL d L W (HflowBlock d L W v ω) (zt E v) I)
      (Matrix.trace (loopWordDeriv d L W ω E u (I.σ.zip I.a))) u := by
  set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt u
    (hasDerivAt_gloopProd_HflowBlock_spectralZ d L W ω hE hu hu1 I hwf)
  simpa only [hT, Function.comp_def, loopL, gloopProd] using h

end LoopDeriv

end Derivative

/-! ## 4. The crude whole-space loop envelope -/

section Envelope

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix entry is bounded by the `ℓ² → ℓ²` operator norm. -/
theorem norm_matrix_entry_le_opNorm (M : Matrix n n ℂ) (p q : n) : ‖M p q‖ ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single q 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  refine le_of_eq_of_le ?_ (PiLp.norm_apply_le _ p)
  simp

/-- Crude trace bound, with the full dimension as constant. -/
theorem norm_matrix_trace_le_card_mul (M : Matrix n n ℂ) :
    ‖Matrix.trace M‖ ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  calc
    ‖∑ p, M p p‖ ≤ ∑ p, ‖M p p‖ := norm_sum_le _ _
    _ ≤ ∑ _p : n, ‖M‖ := Finset.sum_le_sum fun p _ => norm_matrix_entry_le_opNorm M p p
    _ = (Fintype.card n : ℝ) * ‖M‖ := by simp

/-- `‖(H - z)⁻¹‖ ≤ η⁻¹` in the `ℓ²` operator norm, on the whole space.  (Helper of
`norm_Gsig_le_inv_eta`; the proof uses the vector estimate `norm_sub_smul_ge_of_isHermitian` and
`Ring.inverse`, as in `GLoopFlow`.) -/
private theorem flowCalculus_norm_resolvent_le {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖Ring.inverse (H - z • (1 : Matrix n n ℂ))‖ ≤ η⁻¹ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  set A : Matrix n n ℂ := H - z • (1 : Matrix n n ℂ) with hA
  have hAu : IsUnit A := isUnit_sub_smul_of_isHermitian hH hzim
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  set w := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹ v with hw
  have hAw : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A w = v := by
    have hmul : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
        * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹ = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv A hdet, map_one]
    calc Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A w
        = (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
            * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹) v := rfl
      _ = v := by rw [hmul]; rfl
  have hkey := norm_sub_smul_ge_of_isHermitian hH z w
  have hTw : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A w
      = Matrix.toEuclideanLin H w - z • w := by
    have hH' : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H w = Matrix.toEuclideanLin H w :=
      congrArg (fun f => f w) (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin H)
    simp [hA, map_sub, map_smul, hH']
  rw [← hTw, hAw] at hkey
  have hfin : η * ‖w‖ ≤ ‖v‖ := le_trans (by nlinarith [norm_nonneg w]) hkey
  rw [inv_mul_eq_div, le_div_iff₀ hη]
  linarith [hfin]

/-- Both spectral signs have the same whole-space resolvent bound. -/
theorem norm_Gsig_le_inv_eta {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (σ : Bool) : ‖Gres H z σ‖ ≤ η⁻¹ := by
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte]
    exact flowCalculus_norm_resolvent_le hH hη hz
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte]
    exact flowCalculus_norm_resolvent_le hH hη (by simpa using hz)

end Generic

section LoopEnvelope

variable (d L W : ℕ) [NeZero L]

/-- Each normalized block insertion has operator norm at most `W^{-d}`. -/
theorem norm_Eblk_le_inv_W_sq (a : Zd d L) :
    ‖Eblk d L W a‖ ≤ ((W : ℝ) ^ d)⁻¹ := by
  rw [Eblk, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  split_ifs with h
  · simp
  · simp

/-- Operator norm of a finite signed Green and block-insertion word. -/
theorem norm_foldr_Gsig_Eblk_le [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (l : List (Bool × Zd d L)) :
    ‖l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖
      ≤ (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ]
      calc
        ‖Gres H z p.1 * Eblk d L W p.2 *
            l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1‖
          ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ *
              ‖l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1‖ := by
                exact (norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ η⁻¹ * ((W : ℝ) ^ d)⁻¹ *
              (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ l.length := by
                gcongr
                · exact norm_Gsig_le_inv_eta hH hη hz p.1
                · exact norm_Eblk_le_inv_W_sq d L W p.2
        _ = (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ l.length *
              (η⁻¹ * ((W : ℝ) ^ d)⁻¹) := by ring

/-- The block-product index has `(L W)^d = N` points; `N = (W L)^d` is the
fine-lattice dimension (`card_Idx`). -/
theorem card_BlockIndex : Fintype.card (Vtx d L W) = (L * W) ^ d := by
  simp only [Vtx, Zd, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [mul_pow]

/-- A crude but global finite-loop envelope; no exceptional event is removed.  It costs the factor
`L^d` against the sharp `norm_gloop_le_sharp`. -/
theorem norm_gloop_le_crude [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    ‖loopL d L W H z I‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) *
        (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ I.a.length := by
  have htrace := norm_matrix_trace_le_card_mul (gloopProd d L W H z I)
  have hword := norm_foldr_Gsig_Eblk_le d L W hH hη hz (I.σ.zip I.a)
  calc
    ‖loopL d L W H z I‖
      ≤ (Fintype.card (Vtx d L W) : ℝ) *
          ‖(I.σ.zip I.a).foldr
            (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1‖ := htrace
    _ ≤ (Fintype.card (Vtx d L W) : ℝ) *
          (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ (I.σ.zip I.a).length := by
            exact mul_le_mul_of_nonneg_left hword (Nat.cast_nonneg _)
    _ = (((L * W) ^ d : ℕ) : ℝ) *
          (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ I.a.length := by
            rw [card_BlockIndex, List.length_zip]
            simp only [Loop.LoopIdx.WF] at hwf
            rw [hwf, min_self]

end LoopEnvelope

end Envelope

end RBM.Gauss
