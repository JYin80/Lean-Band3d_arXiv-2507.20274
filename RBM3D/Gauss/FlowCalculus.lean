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
# The flow calculus (ST-1, ticket S1-01 = T2030)

Port of the ten files `Gauss/{SpectralWindow, SpectralAlgebra, SpectralDerivative, FlowTimeCont,
GreenTimeCont, LoopTimeCont, LoopSampleCont, GreenDerivative, LoopDerivative, LoopEnvelope}` of
`RBM2D` at commit `c9a24cf` (cited `RBM2D/Gauss/<File>.lean:<line>`), onto the merged MD layer
(`FineModel`, `GLoopFlow`, `Defs/Semicircle`).  Renaming rules R1-R4 of
`docs/tickets/ST1-COMMON.md`;
in addition (merged vocabulary): `spectralM` is `mE`, `spectralZ` is `zt` (`Defs/Semicircle`),
RBM2D's `green H z` is `Gres H z true` and `Gsig H z σ` is `Gres H z σ`, `gloop L W H z I` is
`loopL d L W H z I`, `BlockIndex L W` is `Vtx d L W`, the submatrix
`(·).submatrix (splitEquiv L W).symm (splitEquiv L W).symm` is `blockMat d L W`, `LoopIdx (Z2 L)` is
`Loop.LoopIdx (Zd d L)`, `Ω L W` and `P L W` are `Ω d L W` and `PF d L W g`.

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

/-- `RBM2D/Gauss/SpectralWindow.lean:24` (`spectralM_im`), `spectralM = mE`. -/
theorem spectralM_im (E : ℝ) : (mE E).im = Real.sqrt (4 - E ^ 2) / 2 := mE_im E

/-- `RBM2D/Gauss/SpectralWindow.lean:27` (`spectralM_im_pos`). -/
theorem spectralM_im_pos {E : ℝ} (hE : |E| < 2) : 0 < (mE E).im := mE_im_pos hE

/-- `RBM2D/Gauss/SpectralWindow.lean:36` (`spectralZ_im`), `spectralZ = zt`. -/
theorem spectralZ_im (E u : ℝ) : (zt E u).im = (1 - u) * (mE E).im := zt_im E u

/-- `RBM2D/Gauss/SpectralWindow.lean:39` (`continuous_spectralZ`). -/
theorem continuous_spectralZ (E : ℝ) : Continuous (zt E) := by
  unfold zt
  fun_prop

/-- A uniform non-real gap on `[s,t]`, with the minimum attained at `t`.
`RBM2D/Gauss/SpectralWindow.lean:44` (`spectralZ_im_gap`). -/
theorem spectralZ_im_gap {E s t : ℝ} (hE : |E| < 2) (ht : t < 1)
    {u : ℝ} (hu : u ∈ Set.Icc s t) :
    (1 - t) * (mE E).im ≤ |(zt E u).im| := by
  rw [spectralZ_im, abs_of_pos (mul_pos (by linarith [hu.2]) (spectralM_im_pos hE))]
  exact mul_le_mul_of_nonneg_right (by linarith [hu.2]) (spectralM_im_pos hE).le

/-- The gap remains valid under the paper's bulk condition `|E| ≤ 2-κ`.
`RBM2D/Gauss/SpectralWindow.lean:51` (`spectralZ_window_gap_of_bulk`). -/
theorem spectralZ_window_gap_of_bulk {E κ s t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht : t < 1) :
    0 < (1 - t) * (mE E).im ∧
      ∀ u ∈ Set.Icc s t, (1 - t) * (mE E).im ≤ |(zt E u).im| := by
  have hE' : |E| < 2 := by linarith
  constructor
  · exact mul_pos (by linarith) (spectralM_im_pos hE')
  · intro u hu
    exact spectralZ_im_gap hE' ht hu

/-- The real square root in the explicit bulk value has the expected square.
`RBM2D/Gauss/SpectralAlgebra.lean:20` (`spectralM_sqrt_sq`). -/
theorem spectralM_sqrt_sq {E : ℝ} (hE : |E| ≤ 2) :
    Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := sq_sqrt_four_sub hE

/-- The explicit bulk value solves the semicircle quadratic equation.
`RBM2D/Gauss/SpectralAlgebra.lean:27` (`spectralM_mul`). -/
theorem spectralM_mul {E : ℝ} (hE : |E| ≤ 2) : mE E * (mE E + E) = -1 := mE_mul hE

/-- Equivalent monic quadratic equation `m² + E m + 1 = 0`.
`RBM2D/Gauss/SpectralAlgebra.lean:37` (`spectralM_quadratic`). -/
theorem spectralM_quadratic {E : ℝ} (hE : |E| ≤ 2) :
    mE E ^ 2 + E * mE E + 1 = 0 := by
  have h := spectralM_mul hE
  linear_combination h

/-- The explicit bulk value lies on the unit circle.
`RBM2D/Gauss/SpectralAlgebra.lean:43` (`norm_spectralM`). -/
theorem norm_spectralM {E : ℝ} (hE : |E| ≤ 2) : ‖mE E‖ = 1 := norm_mE hE

/-- The spectral path has constant complex derivative `-m^(E)`.
`RBM2D/Gauss/SpectralDerivative.lean:18` (`hasDerivAt_spectralZ`). -/
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

/-- The imaginary gap has derivative `-Im m^(E)`.
`RBM2D/Gauss/SpectralDerivative.lean:33` (`hasDerivAt_spectralZ_im`). -/
theorem hasDerivAt_spectralZ_im (E u : ℝ) :
    HasDerivAt (fun v : ℝ => (zt E v).im) (-(mE E).im) u := by
  simpa only [spectralZ_im, id_eq, neg_one_mul] using
    (((hasDerivAt_id u).const_sub 1).mul_const (mE E).im)

end Spectral

/-! ## 2. Samplewise time continuity of the flow, of the resolvent and of the loops -/

section FlowTime

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- For each fixed Gaussian sample, the entire matrix flow is continuous in time.
`RBM2D/Gauss/FlowTimeCont.lean:23` (`continuous_Hflow_time`). -/
theorem continuous_Hflow_time (ω : Ω d L W) :
    Continuous fun u : ℝ => Hflow d L W u ω := by
  change Continuous fun u : ℝ => (Real.sqrt u : ℂ) • Xmat d L W ω
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).smul continuous_const

/-- Every matrix entry is continuous along the fixed-sample flow.
`RBM2D/Gauss/FlowTimeCont.lean:29` (`continuous_Hflow_entry_time`). -/
theorem continuous_Hflow_entry_time (ω : Ω d L W) (i j : Idx d L W) :
    Continuous fun u : ℝ => Hflow d L W u ω i j :=
  (continuous_apply j).comp ((continuous_apply i).comp (continuous_Hflow_time d L W ω))

end FlowTime

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- The common-probability-space flow is continuous in time at each fixed size and sample.
`RBM2D/Gauss/FlowTimeCont.lean:44` (`continuous_seqHflow_time`). -/
theorem continuous_seqHflow_time (n : ℕ) (ω : SeqΩ sz) :
    Continuous fun u : ℝ => seqHflow sz n u ω := by
  change Continuous fun u : ℝ => Hflow d (sz.L n) (sz.W n) u (slice sz n ω)
  exact continuous_Hflow_time _ _ _ _

/-- Entrywise time continuity on the common probability space.
`RBM2D/Gauss/FlowTimeCont.lean:53` (`continuous_seqHflow_entry_time`). -/
theorem continuous_seqHflow_entry_time (n : ℕ) (ω : SeqΩ sz)
    (i j : Idx d (sz.L n) (sz.W n)) :
    Continuous fun u : ℝ => seqHflow sz n u ω i j :=
  (continuous_apply j).comp ((continuous_apply i).comp (continuous_seqHflow_time sz n ω))

end Sizes

section GreenCont

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Joint path continuity of the resolvent when both the Hermitian matrix and the non-real
spectral parameter vary continuously (RBM2D's `green H z` is `Gres H z true`).
`RBM2D/Gauss/GreenTimeCont.lean:53` (`continuous_green_of_isHermitian_moving`). -/
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
fixed spectral parameter off the real axis.
`RBM2D/Gauss/GreenTimeCont.lean:28` (`continuous_green_of_isHermitian`). -/
theorem continuous_green_of_isHermitian {V : Type*} [TopologicalSpace V]
    {f : V → Matrix n n ℂ} (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) : Continuous fun v => Gres (f v) z true :=
  continuous_green_of_isHermitian_moving hf hherm continuous_const fun _ => hz

end GreenCont

section GreenTime

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- Fixed-sample time continuity of the full resolvent for a fixed non-real `z`.
`RBM2D/Gauss/GreenTimeCont.lean:78` (`continuous_green_Hflow_time`). -/
theorem continuous_green_Hflow_time (ω : Ω d L W) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun u : ℝ => Gres (Hflow d L W u ω) z true :=
  continuous_green_of_isHermitian (continuous_Hflow_time d L W ω)
    (fun u => Hflow_isHermitian d L W u ω) hz

/-- The samplewise resolvent stays continuous when the spectral parameter follows any continuous
path in the upper or lower half-plane.
`RBM2D/Gauss/GreenTimeCont.lean:84` (`continuous_green_Hflow_moving_time`). -/
theorem continuous_green_Hflow_moving_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) :
    Continuous fun u : ℝ => Gres (Hflow d L W u ω) (z u) true :=
  continuous_green_of_isHermitian_moving (continuous_Hflow_time d L W ω)
    (fun u => Hflow_isHermitian d L W u ω) hzcont hzim

/-! ### The flow on the block-product index -/

/-- The fine-lattice flow reindexed by the paper's block and within-block coordinates.
`RBM2D/Gauss/LoopTimeCont.lean:27` (`HflowBlock`); the merged `blockMat`. -/
noncomputable def HflowBlock (u : ℝ) (ω : Ω d L W) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  blockMat d L W (Hflow d L W u ω)

/-- `RBM2D/Gauss/LoopTimeCont.lean:31` (`continuous_HflowBlock_time`). -/
theorem continuous_HflowBlock_time (ω : Ω d L W) :
    Continuous fun u : ℝ => HflowBlock d L W u ω :=
  (continuous_Hflow_time d L W ω).matrix_submatrix _ _

/-- `RBM2D/Gauss/LoopTimeCont.lean:35` (`HflowBlock_isHermitian`). -/
theorem HflowBlock_isHermitian (u : ℝ) (ω : Ω d L W) :
    (HflowBlock d L W u ω).IsHermitian :=
  (Hflow_isHermitian d L W u ω).submatrix _

/-- The reindexed flow has a continuous Green matrix for a moving non-real parameter.
`RBM2D/Gauss/LoopTimeCont.lean:39` (`continuous_green_HflowBlock_time`). -/
theorem continuous_green_HflowBlock_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) :
    Continuous fun u : ℝ => Gres (HflowBlock d L W u ω) (z u) true :=
  continuous_green_of_isHermitian_moving (continuous_HflowBlock_time d L W ω)
    (fun u => HflowBlock_isHermitian d L W u ω) hzcont hzim

/-- Either spectral sign gives a continuous Green matrix along the fixed-sample flow
(RBM2D's `Gsig` is the merged `Gres`).
`RBM2D/Gauss/LoopTimeCont.lean:46` (`continuous_Gsig_Hflow_time`). -/
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

/-- A finite list of signed Green factors and block insertions has a continuous product.
`RBM2D/Gauss/LoopTimeCont.lean:58` (`continuous_foldr_Hflow_time`). -/
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

/-- Continuity of the full finite loop word.
`RBM2D/Gauss/LoopTimeCont.lean:70` (`continuous_gloopProd_Hflow_time`). -/
theorem continuous_gloopProd_Hflow_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) :
    Continuous fun u : ℝ => gloopProd d L W (HflowBlock d L W u ω) (z u) I :=
  continuous_foldr_Hflow_time d L W ω hzcont hzim (I.σ.zip I.a)

omit [NeZero W] in
/-- The trace of a finite complex matrix depends continuously on the matrix.
`RBM2D/Gauss/LoopTimeCont.lean:83` (`continuous_matrixTrace`). -/
theorem continuous_matrixTrace :
    Continuous (Matrix.trace : Matrix (Vtx d L W) (Vtx d L W) ℂ → ℂ) :=
  LinearMap.continuous_of_finiteDimensional (Matrix.traceLinearMap (Vtx d L W) ℂ ℂ)

/-- A well-formed finite resolvent loop is continuous in time at a fixed Gaussian sample
(RBM2D's `gloop` is the merged `loopL`).
`RBM2D/Gauss/LoopTimeCont.lean:88` (`continuous_gloop_Hflow_time`). -/
theorem continuous_gloop_Hflow_time (ω : Ω d L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (_hwf : I.WF) :
    Continuous fun u : ℝ => loopL d L W (HflowBlock d L W u ω) (z u) I :=
  (continuous_matrixTrace d L W).comp
    (continuous_gloopProd_Hflow_time d L W ω hzcont hzim I)

/-! ### Sample continuity and measurability at a fixed time -/

/-- Reindexing preserves continuity of the matrix flow as a function of the sample.
`RBM2D/Gauss/LoopSampleCont.lean:25` (`continuous_HflowBlock_sample`). -/
theorem continuous_HflowBlock_sample (u : ℝ) : Continuous (HflowBlock d L W u) :=
  (continuous_Hflow d L W u).matrix_submatrix _ _

/-- The fixed-parameter Green matrix is continuous in the Gaussian sample.
`RBM2D/Gauss/LoopSampleCont.lean:30` (`continuous_green_HflowBlock_sample`). -/
theorem continuous_green_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω d L W => Gres (HflowBlock d L W u ω) z true :=
  continuous_green_of_isHermitian (continuous_HflowBlock_sample d L W u)
    (fun ω => HflowBlock_isHermitian d L W u ω) hz

/-- Both signed resolvents are continuous in the sample.
`RBM2D/Gauss/LoopSampleCont.lean:36` (`continuous_Gsig_HflowBlock_sample`). -/
theorem continuous_Gsig_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Continuous fun ω : Ω d L W => Gres (HflowBlock d L W u ω) z σ := by
  cases σ with
  | true => exact continuous_green_HflowBlock_sample d L W u hz
  | false =>
      have h := continuous_green_HflowBlock_sample d L W u (z := (starRingEnd ℂ) z)
        (by simpa using hz)
      simpa [Gres] using h

/-- The finite loop word is continuous in the Gaussian sample.
`RBM2D/Gauss/LoopSampleCont.lean:45` (`continuous_foldr_HflowBlock_sample`). -/
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

/-- Sample continuity of the complete matrix product.
`RBM2D/Gauss/LoopSampleCont.lean:58` (`continuous_gloopProd_HflowBlock_sample`). -/
theorem continuous_gloopProd_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) :
    Continuous fun ω : Ω d L W => gloopProd d L W (HflowBlock d L W u ω) z I :=
  continuous_foldr_HflowBlock_sample d L W u hz (I.σ.zip I.a)

/-- A well-formed resolvent loop is continuous in the Gaussian sample at fixed time.
`RBM2D/Gauss/LoopSampleCont.lean:64` (`continuous_gloop_HflowBlock_sample`). -/
theorem continuous_gloop_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (_hwf : I.WF) :
    Continuous fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z I :=
  (continuous_matrixTrace d L W).comp
    (continuous_gloopProd_HflowBlock_sample d L W u hz I)

/-- The fixed-time loop is measurable under the Gaussian product law.
`RBM2D/Gauss/LoopSampleCont.lean:71` (`measurable_gloop_HflowBlock_sample`). -/
theorem measurable_gloop_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    Measurable fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z I :=
  (continuous_gloop_HflowBlock_sample d L W u hz I hwf).measurable

end GreenTime

/-! ## 3. Derivatives along the samplewise spectral flow -/

section Derivative

section Green

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Chain rule for a non-real resolvent with both matrix and spectral parameter moving
(RBM2D's `green H z` is `Gres H z true`).
`RBM2D/Gauss/GreenDerivative.lean:25` (`hasDerivAt_green_moving`). -/
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

/-- The reindexed Gaussian flow has the same square-root derivative.
`RBM2D/Gauss/GreenDerivative.lean:61` (`hasDerivAt_HflowBlock_time`). -/
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
The sign follows from differentiating `(H_u-z_u I)⁻¹`.
`RBM2D/Gauss/GreenDerivative.lean:82` (`hasDerivAt_green_HflowBlock_spectralZ`);
`(Xmat ω).submatrix (splitEquiv).symm (splitEquiv).symm` is written `blockMat d L W (Xmat ω)`. -/
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

/-- The spectral drift for either Green sign.
`RBM2D/Gauss/LoopDerivative.lean:25` (`spectralMSign`); the merged `mSigma`
(`spectralMSign_eq_mSigma`). -/
noncomputable def spectralMSign (E : ℝ) (σ : Bool) : ℂ :=
  if σ then mE E else (starRingEnd ℂ) (mE E)

theorem spectralMSign_eq_mSigma (E : ℝ) (σ : Bool) : spectralMSign E σ = mSigma E σ := rfl

/-- The derivative of one signed Green factor along the samplewise flow.
`RBM2D/Gauss/LoopDerivative.lean:29` (`gsigFlowDeriv`). -/
noncomputable def gsigFlowDeriv (ω : Ω d L W) (E u : ℝ) (σ : Bool) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  let G := Gres (HflowBlock d L W u ω) (zt E u) σ;
  let X := blockMat d L W (Xmat d L W ω);
  -(G * ((1 / (2 * Real.sqrt u)) • X +
      spectralMSign E σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G)

/-- Each signed resolvent has the stated fixed-sample derivative.
`RBM2D/Gauss/LoopDerivative.lean:38` (`hasDerivAt_Gsig_HflowBlock_spectralZ`). -/
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

/-- Recursive Leibniz derivative of the signed Green/block word.
`RBM2D/Gauss/LoopDerivative.lean:63` (`loopWordDeriv`). -/
noncomputable def loopWordDeriv (ω : Ω d L W) (E u : ℝ) :
    List (Bool × Zd d L) → Matrix (Vtx d L W) (Vtx d L W) ℂ
  | [] => 0
  | p :: l =>
      (gsigFlowDeriv d L W ω E u p.1 * Eblk d L W p.2) *
        l.foldr (fun q M => Gres (HflowBlock d L W u ω) (zt E u) q.1 *
          Eblk d L W q.2 * M) 1 +
      (Gres (HflowBlock d L W u ω) (zt E u) p.1 * Eblk d L W p.2) *
        loopWordDeriv ω E u l

/-- List induction proves the product rule for every finite signed word.
`RBM2D/Gauss/LoopDerivative.lean:74` (`hasDerivAt_loopWord_HflowBlock_spectralZ`). -/
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

/-- The matrix-product form of the loop derivative.
`RBM2D/Gauss/LoopDerivative.lean:101` (`hasDerivAt_gloopProd_HflowBlock_spectralZ`). -/
theorem hasDerivAt_gloopProd_HflowBlock_spectralZ (ω : Ω d L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (_hwf : I.WF) :
    HasDerivAt
      (fun v : ℝ => gloopProd d L W (HflowBlock d L W v ω) (zt E v) I)
      (loopWordDeriv d L W ω E u (I.σ.zip I.a)) u :=
  hasDerivAt_loopWord_HflowBlock_spectralZ d L W ω hE hu hu1 (I.σ.zip I.a)

/-- Taking the trace gives the fixed-sample derivative of the complete loop.
`RBM2D/Gauss/LoopDerivative.lean:114` (`hasDerivAt_gloop_HflowBlock_spectralZ`). -/
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

/-- A matrix entry is bounded by the `ℓ² → ℓ²` operator norm.
`RBM2D/Gauss/LoopEnvelope.lean:24` (`norm_matrix_entry_le_opNorm`). -/
theorem norm_matrix_entry_le_opNorm (M : Matrix n n ℂ) (p q : n) : ‖M p q‖ ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single q 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  refine le_of_eq_of_le ?_ (PiLp.norm_apply_le _ p)
  simp

/-- Crude trace bound, with the full dimension as constant.
`RBM2D/Gauss/LoopEnvelope.lean:32` (`norm_matrix_trace_le_card_mul`). -/
theorem norm_matrix_trace_le_card_mul (M : Matrix n n ℂ) :
    ‖Matrix.trace M‖ ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  calc
    ‖∑ p, M p p‖ ≤ ∑ p, ‖M p p‖ := norm_sum_le _ _
    _ ≤ ∑ _p : n, ‖M‖ := Finset.sum_le_sum fun p _ => norm_matrix_entry_le_opNorm M p p
    _ = (Fintype.card n : ℝ) * ‖M‖ := by simp

/-- `‖(H - z)⁻¹‖ ≤ η⁻¹` in the `ℓ²` operator norm, on the whole space.  (Helper of
`norm_Gsig_le_inv_eta`; the proof of `RBM2D/Gauss/Envelope.lean:116` (`norm_green_le`) with the
vector estimate `norm_sub_smul_ge_of_isHermitian` and `Ring.inverse`, as in `GLoopFlow`.) -/
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

/-- Both spectral signs have the same whole-space resolvent bound.
`RBM2D/Gauss/LoopEnvelope.lean:55` (`norm_Gsig_le_inv_eta`), with `Gsig` the merged `Gres`. -/
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

/-- Each normalized block insertion has operator norm at most `W^{-d}` (RBM2D: `W⁻²`).
`RBM2D/Gauss/LoopEnvelope.lean:45` (`norm_Eblk_le_inv_W_sq`), rule R3. -/
theorem norm_Eblk_le_inv_W_sq (a : Zd d L) :
    ‖Eblk d L W a‖ ≤ ((W : ℝ) ^ d)⁻¹ := by
  rw [Eblk, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  split_ifs with h
  · simp
  · simp

/-- Operator norm of a finite signed Green and block-insertion word.
`RBM2D/Gauss/LoopEnvelope.lean:65` (`norm_foldr_Gsig_Eblk_le`), rule R3. -/
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

/-- The block-product index has `(L W)^d = N` points (RBM2D: `(L W)^2`); `N = (W L)^d` is the
fine-lattice dimension (`card_Idx`).
`RBM2D/Gauss/LoopEnvelope.lean:92` (`card_BlockIndex`), rule R3. -/
theorem card_BlockIndex : Fintype.card (Vtx d L W) = (L * W) ^ d := by
  simp only [Vtx, Zd, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [mul_pow]

/-- A crude but global finite-loop envelope; no exceptional event is removed.  It costs the factor
`L^d` against the sharp `norm_gloop_le_sharp`.
`RBM2D/Gauss/LoopEnvelope.lean:97` (`norm_gloop_le_crude`), rule R3; `gloop` is `loopL`. -/
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

/-- A deterministic loop envelope uniform in time and over every Gaussian sample.
`RBM2D/Gauss/LoopEnvelope.lean:120` (`norm_gloop_HflowBlock_le_crude_on_Icc`), rule R3. -/
theorem norm_gloop_HflowBlock_le_crude_on_Icc [NeZero W] {s t η : ℝ} (hη : 0 < η)
    {z : ℝ → ℂ} (hz : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    ∀ u ∈ Set.Icc s t, ∀ ω : Ω d L W,
      ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖ ≤
        (((L * W) ^ d : ℕ) : ℝ) *
          (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ I.a.length := by
  intro u hu ω
  exact norm_gloop_le_crude d L W (HflowBlock_isHermitian d L W u ω)
    hη (hz u hu) I hwf

end LoopEnvelope

end Envelope

/-! ## 5. Continuity of the Gaussian loop moment along the spectral path -/

section Moment

/-- Under a uniform deterministic envelope, dominated convergence makes the `q`-th absolute
moment continuous in time.  (Helper, copy of `RBM2D/Gauss/MomentTimeCont.lean:26`
(`continuousOn_integral_abs_pow_of_envelope`); dimension-free.) -/
private theorem flowCalculus_continuousOn_integral_abs_pow_of_envelope
    {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    {S : Set ℝ} {f : ℝ → α → ℝ} {C : ℝ} (q : ℕ)
    (hmeas : ∀ u ∈ S, AEStronglyMeasurable (f u) P)
    (hbd : ∀ u ∈ S, ∀ ω, |f u ω| ≤ C)
    (hcont : ∀ ω, ContinuousOn (fun u => f u ω) S) :
    ContinuousOn (fun u => ∫ ω, |f u ω| ^ q ∂P) S := by
  refine MeasureTheory.continuousOn_of_dominated (bound := fun _ : α => |C| ^ q) ?_ ?_
    (integrable_const _) ?_
  · intro u hu
    have h := ((hmeas u hu).norm).pow q
    have he : ((fun ω => ‖f u ω‖) ^ q) = fun ω => |f u ω| ^ q := by
      funext ω
      simp [Real.norm_eq_abs]
    rwa [he] at h
  · refine fun u hu => Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) q)]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hbd u hu ω).trans (le_abs_self C)) q
  · exact Filter.Eventually.of_forall fun ω => ((hcont ω).abs).pow q

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- Samplewise loop continuity on a window whose spectral path stays off the real axis.
Clamping the spectral path to the window reuses the global path theorem.  (Helper, copy of
`RBM2D/Gauss/LoopMomentCont.lean:26` (`continuousOn_gloop_HflowBlock_window`).) -/
private theorem flowCalculus_continuousOn_gloop_HflowBlock_window {s t : ℝ} (hst : s ≤ t)
    (ω : Ω d L W) {z : ℝ → ℂ} (hzcont : Continuous z)
    (hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    ContinuousOn (fun u : ℝ => loopL d L W (HflowBlock d L W u ω) (z u) I)
      (Set.Icc s t) := by
  let clamp : ℝ → ℝ := fun u => max s (min t u)
  have hclamp_cont : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem : ∀ u, clamp u ∈ Set.Icc s t := by
    intro u
    exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩
  have hclamp_eq : ∀ u ∈ Set.Icc s t, clamp u = u := by
    intro u hu
    simp [clamp, min_eq_right hu.2, max_eq_right hu.1]
  have hglobal := continuous_gloop_Hflow_time d L W ω
    (z := fun u => z (clamp u)) (hzcont.comp hclamp_cont)
    (fun u => hzim (clamp u) (hclamp_mem u)) I hwf
  exact hglobal.continuousOn.congr (fun u hu => by
    change loopL d L W (HflowBlock d L W u ω) (z u) I =
      loopL d L W (HflowBlock d L W u ω) (z (clamp u)) I
    rw [hclamp_eq u hu])

/-- The `q`-th absolute moment of a finite resolvent loop is continuous in time.  (Helper, copy of
`RBM2D/Gauss/LoopMomentCont.lean:51` (`continuousOn_integral_norm_gloop_pow`), rule R3: the
envelope constant is `(L W)^d (η⁻¹ W^{-d})^n`.) -/
private theorem flowCalculus_continuousOn_integral_norm_gloop_pow (g : ℝ) {s t η : ℝ}
    (hst : s ≤ t) (hη : 0 < η) {z : ℝ → ℂ} (hzcont : Continuous z)
    (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) (q : ℕ) :
    ContinuousOn
      (fun u : ℝ => ∫ ω : Ω d L W,
        ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖ ^ q ∂(PF d L W g))
      (Set.Icc s t) := by
  let C : ℝ := (((L * W) ^ d : ℕ) : ℝ) *
    (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ I.a.length
  have hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0 := by
    intro u hu
    exact abs_pos.mp (hη.trans_le (hzlow u hu))
  have hmeas : ∀ u ∈ Set.Icc s t,
      AEStronglyMeasurable
        (fun ω : Ω d L W => ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖) (PF d L W g) := by
    intro u hu
    exact ((measurable_gloop_HflowBlock_sample d L W u (hzim u hu) I hwf).norm).aestronglyMeasurable
  have hbd : ∀ u ∈ Set.Icc s t, ∀ ω : Ω d L W,
      |‖loopL d L W (HflowBlock d L W u ω) (z u) I‖| ≤ C := by
    intro u hu ω
    rw [abs_of_nonneg (norm_nonneg _)]
    exact norm_gloop_HflowBlock_le_crude_on_Icc d L W hη hzlow I hwf u hu ω
  have hcont : ∀ ω : Ω d L W,
      ContinuousOn (fun u : ℝ => ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖)
        (Set.Icc s t) := by
    intro ω
    exact (flowCalculus_continuousOn_gloop_HflowBlock_window d L W hst ω hzcont hzim I hwf).norm
  have h := flowCalculus_continuousOn_integral_abs_pow_of_envelope (P := PF d L W g)
    (S := Set.Icc s t)
    (f := fun u ω => ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖)
    (C := C) q hmeas hbd hcont
  simpa only [abs_of_nonneg (norm_nonneg _)] using h

/-- The actual finite Gaussian loop moment has a continuous time dependence along the paper's bulk
spectral path, on every window ending before `u=1`.
`RBM2D/Gauss/SpectralWindow.lean:64` (`continuousOn_integral_norm_gloop_pow_spectralZ`),
`P L W` becoming `PF d L W g`. -/
theorem continuousOn_integral_norm_gloop_pow_spectralZ (g : ℝ)
    {E κ s t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hst : s ≤ t) (ht : t < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) (q : ℕ) :
    ContinuousOn
      (fun u : ℝ => ∫ ω : Ω d L W,
        ‖loopL d L W (HflowBlock d L W u ω) (zt E u) I‖ ^ q ∂(PF d L W g))
      (Set.Icc s t) := by
  obtain ⟨hη, hgap⟩ := spectralZ_window_gap_of_bulk (s := s) hκ hE ht
  exact flowCalculus_continuousOn_integral_norm_gloop_pow d L W g hst hη
    (continuous_spectralZ E) hgap I hwf q

end Moment

/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `N = (W L)^d = 216`) -/

section Instances

/-- A loop of length `3` with charges `(+, -, +)` and three distinct nonzero block labels in
`Z_3^3` (27 blocks of `W^d = 8` sites). -/
private def flowCalculusLoop : Loop.LoopIdx (Zd 3 3) :=
  ⟨[true, false, true], [![1, 0, 2], ![0, 1, 0], ![2, 2, 1]]⟩

private theorem flowCalculusLoop_wf : flowCalculusLoop.WF := rfl

/-- The spectral path at `E = 1/2`: `|E| < 2`, unit modulus, positive imaginary part, and the
derivative of the gap at the interior time `u = 1/2`. -/
example : |(1 / 2 : ℝ)| < 2 ∧ ‖mE (1 / 2)‖ = 1 ∧ 0 < (mE (1 / 2)).im ∧
    HasDerivAt (fun v : ℝ => (zt (1 / 2) v).im) (-(mE (1 / 2)).im) (1 / 2) ∧
    HasDerivAt (zt (1 / 2)) (-(mE (1 / 2))) (1 / 2) ∧
    (mE (1 / 2)) ^ 2 + ((1 / 2 : ℝ) : ℂ) * mE (1 / 2) + 1 = 0 :=
  have h2 : |(1 / 2 : ℝ)| < 2 := by rw [abs_of_pos (by norm_num)]; norm_num
  ⟨h2, norm_spectralM h2.le, spectralM_im_pos h2, hasDerivAt_spectralZ_im _ _,
    hasDerivAt_spectralZ _ _, spectralM_quadratic h2.le⟩

/-- The spectral window `[1/5, 3/5]`, `t = 3/5 < 1`, `κ = 1`: a positive uniform gap. -/
example : 0 < (1 - 3 / 5 : ℝ) * (mE (1 / 2)).im ∧
    ∀ u ∈ Set.Icc (1 / 5 : ℝ) (3 / 5), (1 - 3 / 5 : ℝ) * (mE (1 / 2)).im ≤ |(zt (1 / 2) u).im| :=
  spectralZ_window_gap_of_bulk (κ := 1) (s := 1 / 5) (t := 3 / 5) one_pos
    (by rw [abs_of_pos (by norm_num)]; norm_num) (by norm_num)

/-- Entrywise time continuity of the flow at `d = 3`, `L = 3`, `W = 2` and along the size
sequence `sz0` (`d = 3`, `L = 4`, `W = 32`), at the zero lattice point. -/
example (ω : Ω 3 3 2) (ω' : Sizes.SeqΩ SizesInst.sz0) :
    Continuous (fun u : ℝ => Hflow 3 3 2 u ω 0 0) ∧
      Continuous (fun u : ℝ => SizesInst.sz0.seqHflow 0 u ω' 0 0) :=
  ⟨continuous_Hflow_entry_time 3 3 2 ω 0 0,
    Sizes.continuous_seqHflow_entry_time SizesInst.sz0 0 ω' 0 0⟩

/-- Time continuity of the resolvent (fixed `z = i`, and moving `z_u = u + i`) and of a 3-loop
along the flow, at every sample. -/
example (ω : Ω 3 3 2) :
    Continuous (fun u : ℝ => Gres (Hflow 3 3 2 u ω) Complex.I true 0 0) ∧
    Continuous (fun u : ℝ => Gres (Hflow 3 3 2 u ω) ((u : ℂ) + Complex.I) true) ∧
    Continuous (fun u : ℝ =>
      loopL 3 3 2 (HflowBlock 3 3 2 u ω) ((u : ℂ) + Complex.I) flowCalculusLoop) := by
  have hz : Continuous fun u : ℝ => (u : ℂ) + Complex.I :=
    Complex.continuous_ofReal.add continuous_const
  have him : ∀ u : ℝ, ((u : ℂ) + Complex.I).im ≠ 0 := fun u => by simp
  exact ⟨(continuous_apply _).comp ((continuous_apply _).comp
      (continuous_green_Hflow_time 3 3 2 ω (z := Complex.I) (by norm_num))),
    continuous_green_Hflow_moving_time 3 3 2 ω hz him,
    continuous_gloop_Hflow_time 3 3 2 ω hz him flowCalculusLoop flowCalculusLoop_wf⟩

/-- Sample continuity and measurability of the 3-loop at the time `u = 1/2`, `z = i`. -/
example :
    Continuous (fun ω : Ω 3 3 2 =>
      loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) Complex.I flowCalculusLoop) ∧
    Measurable (fun ω : Ω 3 3 2 =>
      loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) Complex.I flowCalculusLoop) :=
  ⟨continuous_gloop_HflowBlock_sample 3 3 2 (1 / 2) (by norm_num) _ flowCalculusLoop_wf,
    measurable_gloop_HflowBlock_sample 3 3 2 (1 / 2) (by norm_num) _ flowCalculusLoop_wf⟩

/-- The derivative of the Green function and of the 3-loop along the spectral flow at `E = 1/2`,
`u = 1/2`, at every sample. -/
example (ω : Ω 3 3 2) :
    HasDerivAt (fun v : ℝ => Gres (HflowBlock 3 3 2 v ω) (zt (1 / 2) v) true)
      (-(Gres (HflowBlock 3 3 2 (1 / 2) ω) (zt (1 / 2) (1 / 2)) true *
        ((1 / (2 * Real.sqrt (1 / 2)) : ℝ) • blockMat 3 3 2 (Xmat 3 3 2 ω) +
          mE (1 / 2) • (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)) *
        Gres (HflowBlock 3 3 2 (1 / 2) ω) (zt (1 / 2) (1 / 2)) true)) (1 / 2) ∧
    HasDerivAt (fun v : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 v ω) (zt (1 / 2) v) flowCalculusLoop)
      (Matrix.trace (loopWordDeriv 3 3 2 ω (1 / 2) (1 / 2)
        (flowCalculusLoop.σ.zip flowCalculusLoop.a))) (1 / 2) := by
  have hE : |(1 / 2 : ℝ)| < 2 := by rw [abs_of_pos (by norm_num)]; norm_num
  exact ⟨hasDerivAt_green_HflowBlock_spectralZ 3 3 2 ω hE (by norm_num) (by norm_num),
    hasDerivAt_gloop_HflowBlock_spectralZ 3 3 2 ω hE (by norm_num) (by norm_num)
      flowCalculusLoop flowCalculusLoop_wf⟩

/-- The crude envelope on the window `[1/5, 3/5]` along `z_u = zt (1/2) u`, for every sample;
the constant is `(L W)^d (η⁻¹ W^{-d})^3` with `(L W)^d = 216`, `W^d = 8`. -/
example : ∀ u ∈ Set.Icc (1 / 5 : ℝ) (3 / 5), ∀ ω : Ω 3 3 2,
    ‖loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (1 / 2) u) flowCalculusLoop‖ ≤
      (((3 * 2) ^ 3 : ℕ) : ℝ) *
        (((1 - 3 / 5 : ℝ) * (mE (1 / 2)).im)⁻¹ * (((2 : ℕ) : ℝ) ^ 3)⁻¹) ^ 3 := by
  have hE : |(1 / 2 : ℝ)| ≤ 2 - 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  obtain ⟨hη, hgap⟩ := spectralZ_window_gap_of_bulk (s := 1 / 5) (t := 3 / 5) one_pos hE
    (by norm_num)
  exact norm_gloop_HflowBlock_le_crude_on_Icc 3 3 2 hη hgap flowCalculusLoop flowCalculusLoop_wf

/-- The Gaussian second moment of the 3-loop along the spectral path is continuous on the window
`[1/5, 3/5]`, for the law `PF 3 3 2 1`. -/
example :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω 3 3 2,
      ‖loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (1 / 2) u) flowCalculusLoop‖ ^ 2 ∂(PF 3 3 2 1))
      (Set.Icc (1 / 5 : ℝ) (3 / 5)) :=
  continuousOn_integral_norm_gloop_pow_spectralZ 3 3 2 1 (κ := 1) (s := 1 / 5) (t := 3 / 5)
    one_pos (by rw [abs_of_pos (by norm_num)]; norm_num) (by norm_num) (by norm_num)
    flowCalculusLoop flowCalculusLoop_wf 2

/-- The block-product index has `(L W)^d = 216 = (W L)^d` points, and the block insertion has
norm at most `W^{-d} = 1/8`. -/
example : Fintype.card (Vtx 3 3 2) = 216 ∧ Fintype.card (Vtx 3 3 2) = Fintype.card (Idx 3 3 2) ∧
    ‖Eblk 3 3 2 (![1, 0, 2] : Zd 3 3)‖ ≤ (((2 : ℕ) : ℝ) ^ 3)⁻¹ :=
  ⟨by rw [card_BlockIndex]; norm_num, by rw [card_BlockIndex, card_Idx, mul_comm],
    norm_Eblk_le_inv_W_sq 3 3 2 _⟩

end Instances

end RBM.Gauss
