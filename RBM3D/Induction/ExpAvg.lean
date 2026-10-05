/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ConArgDet
import RBM3D.Gauss.LoopGenerator
import RBM3D.Gauss.DominationAt
import RBM3D.Evolution.XiPins
import RBM3D.Propagator.Pins

/-!
# S6-03 (T2217, ST-5): `lem:improve_exp_aver`, the proof of the pin `STImproveExpAver`

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:10-21` (`lem:improve_exp_aver`: "the same
as [YY_25, Lemma 5.15] by using `(Gt_avgbound_flow)` and `(Eq:L-KGt-flow)`").  Port of RBM2D
`Evolution/Step61.lean` at `c9a24cf` (`step61` `:853`, cited `RBM2D/Evolution/Step61.lean:<line>`)
to `d ≥ 3`, onto the merged `Induction/Step6Pins` (`STExpAvgAt`, `STImproveExpAver`),
`Induction/Step6Kit`, `Gauss/LoopFlowStein`, `Gauss/LoopCoordinate`, `Gauss/LoopGenerator`,
`Gauss/DominationAt`, `Hierarchy/ContractionSecondLoop`, `Evolution/XiPins`.  Renaming rules R1-R4
of `docs/tickets/ST1-COMMON.md`; vocabulary: `green H z` is `Gres H z true`, `gloop L W H z I` is
`loopL d L W H z I`, `BlockIndex L W` is `Vtx d L W`, `Z2 L` is `Zd d L`, `Ω L W`, `P L W`,
`Coord`, `gvar` are `Ω d L W`, `PF d L W g`, `CoordF d L W`, `gvarF d L W g`, `SB L` is
`SB d L g`, `Theta L` is `Theta d L g`, `spectralM`, `spectralZ` are `mE`, `zt`, `scaleM⁻¹` is
the control `Bctl`.

Route.  Stein for `H_u = √u X` gives `𝔼 tr(H G E_a) = -u Σ_p S_{pa} 𝔼[g_p g_a]` (`expAvg_stein`),
with `z_u m + u m² = -1` the self-consistent equation `x = u m² S x + y` on `Z_L^d`
(`expAvg_selfcons`), `y_a = u m Σ_b S_{ba} 𝔼[Z_b Z_a]`.  `Θ_{u m²}` inverts it, with the row sum
of `Θ_{u m²}` bounded by the constant of the merged `ekSameRow_holds` (`d ≥ 3`: no `log L`; RBM2D
has `1 + cShortRow κ (1 + log L)`), `expAvg_norm_solve`; the second moments of `g_b - m` bound
`y` (`expAvg_expErr_le`).  Along the sequence the second moments come from `(Gt_avgbound_flow)`
(`LWAvgLaw`) through the reverse bridge `momentDomAt_of_stochDomAt_of_nonneg` (`expAvg_moment`);
the envelope `‖G_u‖ ≤ η_u⁻¹ ≤ N` along the flow is `expAvg_eta_inv_le`, the floor `N⁻¹ ≤ Bctl` is
`expAvg_Bctl_ge`.  The premise `STLK` of the pin is not used (RBM2D's `Step61Pin` uses
`(Eq:L-KGt)` at `k = 1` only, which is `LWAvgLaw`).

Statement differences with RBM2D: charge `-` (`expAvg_integral_conj`), the control `Bctl` replaces
`scaleM⁻¹`, the range condition `RangeCond` is `u ≤ lemT z` (envelope `expAvg_eta_inv_le`), the row
sum has no `log L`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss RBM.Loop RBM.Path

/-! ## 1. Fixed size: Stein, the self-consistent equation -/

section FixedSize

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W]

private theorem expAvg_sub_mul_green {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Gres H z true = 1 := by
  have hU := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  simp only [Gres, ↓reduceIte]
  exact Ring.mul_inverse_cancel _ hU

private theorem expAvg_gloop_one (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (b : Zd d L) :
    loopL d L W H z ⟨[true], [b]⟩ = Matrix.trace (Gres H z true * Eblk d L W b) := by
  simp [loopL]

/-- Resolvent identity at the level of a single sample: `tr(H G E_a) = 1 + z tr(G E_a)`. -/
private theorem expAvg_trace_HGE (u : ℝ) (ω : Ω d L W) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) :
    Matrix.trace (HflowBlock d L W u ω * Gres (HflowBlock d L W u ω) z true * Eblk d L W a) =
      1 + z * loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩ := by
  have h := expAvg_sub_mul_green L W (HflowBlock_isHermitian d L W u ω) hz
  have hHG : HflowBlock d L W u ω * Gres (HflowBlock d L W u ω) z true =
      1 + z • Gres (HflowBlock d L W u ω) z true := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  rw [hHG, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.one_mul, trace_Eblk_eq_one, expAvg_gloop_one, smul_eq_mul]

private theorem expAvg_norm_trace_mul3_le (A M C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ‖Matrix.trace (A * M * C)‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * (‖A‖ * ‖M‖ * ‖C‖) := by
  have h := norm_matrix_trace_le_card_mul (A * M * C)
  rw [card_BlockIndex] at h
  refine h.trans ?_
  gcongr
  exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)

/-- A Gaussian coordinate times a bounded measurable complex observable is integrable. -/
private theorem expAvg_integrable_coord_smul (g : ℝ) (c : CoordF d L W)
    (f : Ω d L W → ℂ) (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable (fun ω : Ω d L W => ω c • f ω) (PF d L W g) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x) ((PF d L W g).map fun ω => ω c) := by
    rw [P_map_eval]
    exact RBM.integrable_id_gaussianReal (var := gvarF d L W g c)
  have hcoord : Integrable (fun ω : Ω d L W => ω c) (PF d L W g) :=
    (integrable_map_measure hg.aestronglyMeasurable hf).1 hg
  have h := hcoord.ofReal.bdd_mul hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall hfb)
  simpa [Complex.real_smul, mul_comm] using h

private theorem expAvg_integrable_of_cont_bdd (g : ℝ) {f : Ω d L W → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (PF d L W g) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

private theorem expAvg_green_norm_le (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (ω : Ω d L W) :
    ‖Gres (HflowBlock d L W u ω) z true‖ ≤ (|z.im|)⁻¹ :=
  norm_Gsig_le_inv_eta (HflowBlock_isHermitian d L W u ω) (abs_pos.mpr hz) le_rfl true

private theorem expAvg_g_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) (c : CoordF d L W) :
    Continuous fun ω : Ω d L W => Matrix.trace
      (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a) :=
  (continuous_matrixTrace d L W).comp
    ((continuous_const.mul (continuous_green_HflowBlock_sample d L W u hz)).mul continuous_const)

private theorem expAvg_g'_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) (c : CoordF d L W) :
    Continuous fun ω : Ω d L W => Matrix.trace
      (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
        (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
        Eblk d L W a) := by
  have hGc := continuous_green_HflowBlock_sample d L W u hz
  exact (continuous_matrixTrace d L W).comp
    ((continuous_const.mul (((hGc.mul continuous_const).mul hGc).neg)).mul continuous_const)

private theorem expAvg_g_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) (c : CoordF d L W) :
    ∃ C : ℝ, ∀ ω : Ω d L W, ‖Matrix.trace
      (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a)‖ ≤ C := by
  refine ⟨(((L * W) ^ d : ℕ) : ℝ) *
    (‖coordinateBlock d L W c‖ * (|z.im|)⁻¹ * ‖Eblk d L W a‖), fun ω => ?_⟩
  refine (expAvg_norm_trace_mul3_le L W _ _ _).trans ?_
  gcongr
  exact expAvg_green_norm_le L W u hz ω

private theorem expAvg_g'_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) (c : CoordF d L W) :
    ∃ C : ℝ, ∀ ω : Ω d L W, ‖Matrix.trace
      (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
        (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
        Eblk d L W a)‖ ≤ C := by
  refine ⟨(((L * W) ^ d : ℕ) : ℝ) *
    (‖coordinateBlock d L W c‖ * ((|z.im|)⁻¹ * ‖Real.sqrt u • coordinateBlock d L W c‖ *
      (|z.im|)⁻¹) * ‖Eblk d L W a‖), fun ω => ?_⟩
  refine (expAvg_norm_trace_mul3_le L W _ _ _).trans ?_
  gcongr
  rw [norm_neg]
  refine (norm_mul_le _ _).trans ?_
  gcongr
  · exact (norm_mul_le _ _).trans (by gcongr; exact expAvg_green_norm_le L W u hz ω)
  · exact expAvg_green_norm_le L W u hz ω

/-- One-coordinate Stein identity for `tr(B_c G E_a)`. -/
private theorem expAvg_stein_coord (g u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L)
    (c : CoordF d L W) :
    ∫ ω : Ω d L W, ω c • Matrix.trace
        (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a)
          ∂(PF d L W g) =
      (gvarF d L W g c : ℝ) • ∫ ω : Ω d L W, Matrix.trace
        (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
          (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
          Eblk d L W a) ∂(PF d L W g) := by
  set B := coordinateBlock d L W c with hB
  set E := Eblk d L W a with hE
  let f : Ω d L W → ℂ := fun ω => Matrix.trace (B * Gres (HflowBlock d L W u ω) z true * E)
  let f' : Ω d L W → ℂ := fun ω => Matrix.trace (B * (-(Gres (HflowBlock d L W u ω) z true *
    (Real.sqrt u • B) * Gres (HflowBlock d L W u ω) z true)) * E)
  have hgc : Continuous f := expAvg_g_cont L W u hz a c
  have hg'c : Continuous f' := expAvg_g'_cont L W u hz a c
  have hderiv : ∀ ω : Ω d L W,
      HasDerivAt (fun t : ℝ => f (Function.update ω c t)) (f' ω) (ω c) := by
    intro ω
    set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
    have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
    have h1 := hasDerivAt_green_HflowBlock_update d L W u ω c hz
    have h2 := ((hasDerivAt_const (ω c) B).mul h1).mul_const E
    have h3 := T.hasFDerivAt.comp_hasDerivAt (ω c) h2
    refine h3.congr_deriv ?_
    simp only [hT, f', zero_mul, zero_add, hB]
  have hgb : ∃ C : ℝ, ∀ ω : Ω d L W, ‖f ω‖ ≤ C := expAvg_g_bdd L W u hz a c
  have hg'b : ∃ C : ℝ, ∀ ω : Ω d L W, ‖f' ω‖ ≤ C := expAvg_g'_bdd L W u hz a c
  have h := GaussianProduct.stein (gvarF d L W g) c f f' hgc hg'c hderiv hgb hg'b
  have hlaw : PF d L W g = GaussianProduct.law (gvarF d L W g) := rfl
  rw [hlaw]
  exact h

omit [NeZero W] in
private theorem expAvg_Eblk_mul_Eblk (a b : Zd d L) :
    Eblk d L W a * Eblk d L W b =
      if a = b then (((W : ℂ) ^ d)⁻¹) • Eblk d L W a else 0 := by
  unfold Eblk
  rw [diagonal_mul_diagonal]
  ext p q
  by_cases hab : a = b
  · subst hab
    simp only [ite_true, diagonal_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp_all
  · simp only [hab, ite_false, diagonal_apply, Matrix.zero_apply]
    split_ifs <;> simp_all

/-- The contraction of the two `B_c` insertions: the `W^d` of the block covariance cancels the
`W^{-d}` of `E_a E_a`. -/
private theorem expAvg_contraction (g u : ℝ) (hu : 0 ≤ u)
    (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) :
    ∑ c : CoordF d L W, ((Real.sqrt u : ℂ) * ((gvarF d L W g c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock d L W c *
        (-(G * (Real.sqrt u • coordinateBlock d L W c) * G)) * Eblk d L W a) =
    -(u : ℂ) * ∑ p : Zd d L, SB d L g p a *
      (Matrix.trace (G * Eblk d L W p) * Matrix.trace (G * Eblk d L W a)) := by
  have hterm : ∀ c : CoordF d L W,
      ((Real.sqrt u : ℂ) * ((gvarF d L W g c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock d L W c *
        (-(G * (Real.sqrt u • coordinateBlock d L W c) * G)) * Eblk d L W a) =
      -(u : ℂ) * (((gvarF d L W g c : ℝ) : ℂ) *
        Matrix.trace (G * coordinateBlock d L W c * (G * Eblk d L W a) *
          coordinateBlock d L W c)) := by
    intro c
    set B := coordinateBlock d L W c
    have h1 : B * (-(G * (Real.sqrt u • B) * G)) * Eblk d L W a =
        -(Real.sqrt u • (B * (G * B * (G * Eblk d L W a)))) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]
    have h2 : Matrix.trace (B * (G * B * (G * Eblk d L W a))) =
        Matrix.trace (G * B * (G * Eblk d L W a) * B) :=
      Matrix.trace_mul_comm _ _
    rw [h1, Matrix.trace_neg, Matrix.trace_smul, h2, Complex.real_smul]
    have h3 : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
    linear_combination
      (-(((gvarF d L W g c : ℝ) : ℂ) * Matrix.trace (G * B * (G * Eblk d L W a) * B))) * h3
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_coordinateBlock_trace_pair d L W g G (G * Eblk d L W a)]
  congr 1
  have hq : ∀ q : Zd d L, Matrix.trace (G * Eblk d L W a * Eblk d L W q) =
      if a = q then (W : ℂ)⁻¹ ^ d * Matrix.trace (G * Eblk d L W a) else 0 := by
    intro q
    rw [Matrix.mul_assoc, expAvg_Eblk_mul_Eblk]
    split_ifs
    · rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, inv_pow]
    · simp
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  simp_rw [hq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hWd : (W : ℂ) ^ d ≠ 0 := pow_ne_zero _ hW
  rw [inv_pow]
  field_simp

private theorem expAvg_HflowBlock_eq (u : ℝ) (ω : Ω d L W) :
    HflowBlock d L W u ω =
      (Real.sqrt u : ℂ) • ∑ c : CoordF d L W, ω c • coordinateBlock d L W c := by
  rw [← Xblock_eq_sum_coordinates]
  ext i j
  simp [HflowBlock, Hflow, blockMat]

private theorem expAvg_gloop_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Zd d L) (ω : Ω d L W) :
    ‖loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) * ((|z.im|)⁻¹ * (((W : ℝ) ^ d)⁻¹)) := by
  have h := norm_gloop_le_crude d L W (HflowBlock_isHermitian d L W u ω)
    (abs_pos.mpr hz) le_rfl ⟨[true], [b]⟩ (by simp [LoopIdx.WF])
  simpa using h

private theorem expAvg_gloop_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Zd d L) :
    Continuous fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩ :=
  continuous_gloop_HflowBlock_sample d L W u hz _ (by simp [LoopIdx.WF])

private theorem expAvg_integrable_gloop (g u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Zd d L) :
    Integrable (fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩)
      (PF d L W g) :=
  expAvg_integrable_of_cont_bdd L W g (expAvg_gloop_cont L W u hz b) (expAvg_gloop_bdd L W u hz b)

private theorem expAvg_integrable_gloop_mul (g u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b a : Zd d L) :
    Integrable (fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩ *
      loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩) (PF d L W g) := by
  refine expAvg_integrable_of_cont_bdd L W g
    ((expAvg_gloop_cont L W u hz b).mul (expAvg_gloop_cont L W u hz a))
    (C := ((((L * W) ^ d : ℕ) : ℝ) * ((|z.im|)⁻¹ * (((W : ℝ) ^ d)⁻¹))) *
      ((((L * W) ^ d : ℕ) : ℝ) * ((|z.im|)⁻¹ * (((W : ℝ) ^ d)⁻¹)))) (fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul (expAvg_gloop_bdd L W u hz b ω) (expAvg_gloop_bdd L W u hz a ω)
    (norm_nonneg _) ((norm_nonneg _).trans (expAvg_gloop_bdd L W u hz b ω))

/-- **Stein step** (RBM2D `step61_stein`, `Step61.lean:271`): for `H_u = √u X`,
`𝔼 tr(H G E_a) = -u Σ_p S_{pa} 𝔼[g_p g_a]`, `g_b = tr(G E_b)`; the variance profile of `PF d L W g` is
`SB d L g` (`sum_coordinateBlock_trace_pair`, with the `W^d` cancelling `trace (E_a E_q) = δ_{aq} W^{-d}`). -/
theorem expAvg_stein {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g u : ℝ) (hu : 0 ≤ u) {z : ℂ}
    (hz : z.im ≠ 0) (a : Zd d L) :
    ∫ ω : Ω d L W, Matrix.trace (HflowBlock d L W u ω * Gres (HflowBlock d L W u ω) z true *
        Eblk d L W a) ∂(PF d L W g) =
      -(u : ℂ) * ∑ p : Zd d L, SB d L g p a * ∫ ω : Ω d L W,
        loopL d L W (HflowBlock d L W u ω) z ⟨[true], [p]⟩ *
          loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩ ∂(PF d L W g) := by
  classical
  have hI1 : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => ω c • Matrix.trace
      (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a))
        (PF d L W g) := by
    intro c
    obtain ⟨C, hC⟩ := expAvg_g_bdd L W u hz a c
    exact expAvg_integrable_coord_smul L W g c _ (expAvg_g_cont L W u hz a c).measurable hC
  have hI2 : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => Matrix.trace
      (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
        (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
        Eblk d L W a)) (PF d L W g) := by
    intro c
    obtain ⟨C, hC⟩ := expAvg_g'_bdd L W u hz a c
    exact expAvg_integrable_of_cont_bdd L W g (expAvg_g'_cont L W u hz a c) hC
  have hexp : ∀ ω : Ω d L W, Matrix.trace (HflowBlock d L W u ω *
      Gres (HflowBlock d L W u ω) z true * Eblk d L W a) =
      ∑ c : CoordF d L W, (Real.sqrt u : ℂ) * (ω c • Matrix.trace
        (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a)) := by
    intro ω
    generalize Gres (HflowBlock d L W u ω) z true = G
    rw [expAvg_HflowBlock_eq L W u ω]
    simp only [Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
      Complex.real_smul, smul_eq_mul, Finset.mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun c _ => (hI1 c).const_mul _)]
  have hstein : ∀ c : CoordF d L W, ∫ ω : Ω d L W, (Real.sqrt u : ℂ) * (ω c • Matrix.trace
      (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a))
        ∂(PF d L W g) =
      ∫ ω : Ω d L W, ((Real.sqrt u : ℂ) * ((gvarF d L W g c : ℝ) : ℂ)) * Matrix.trace
        (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
          (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
          Eblk d L W a) ∂(PF d L W g) := by
    intro c
    rw [integral_const_mul, expAvg_stein_coord L W g u hz a c, integral_const_mul,
      Complex.real_smul, mul_assoc]
  simp_rw [hstein]
  rw [← integral_finsetSum _ (fun c _ => (hI2 c).const_mul _)]
  have hpt : ∀ ω : Ω d L W, ∑ c : CoordF d L W, ((Real.sqrt u : ℂ) * ((gvarF d L W g c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
        (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
        Eblk d L W a) =
      -(u : ℂ) * ∑ p : Zd d L, SB d L g p a * (loopL d L W (HflowBlock d L W u ω) z ⟨[true], [p]⟩ *
        loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩) := by
    intro ω
    rw [expAvg_contraction L W g u hu]
    simp only [expAvg_gloop_one]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _
    (fun p _ => (expAvg_integrable_gloop_mul L W g u hz p a).const_mul _)]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul]

private theorem expAvg_SB_symm (g : ℝ) (a b : Zd d L) : SB d L g b a = SB d L g a b :=
  congrFun (congrFun (SB_transpose d L g) a) b

omit [NeZero W] in
private theorem expAvg_sum_SB_col (g : ℝ) (hL : 3 ≤ L) (a : Zd d L) : ∑ b : Zd d L, SB d L g b a = 1 := by
  simp_rw [expAvg_SB_symm L g a]
  exact sum_SB_row d L g hL a

private theorem expAvg_hz {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) : (zt E u).im ≠ 0 := by
  rw [zt_im]
  exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))

/-- **The self-consistent equation** (RBM2D `step61_selfcons`, `Step61.lean:339`): with
`x_b = 𝔼 g_b - m`, `Z_b = g_b - m`, `ξ = u m²`, `x_a = ξ Σ_b S_{ba} x_b + u m Σ_b S_{ba} 𝔼[Z_b Z_a]`
at `z = z_u`. -/
theorem expAvg_selfcons {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (hL : 3 ≤ L) {E u : ℝ}
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Zd d L) :
    (∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ ∂(PF d L W g)) - mE E =
      (u : ℂ) * mE E ^ 2 * ∑ b : Zd d L, SB d L g b a *
          ((∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ ∂(PF d L W g)) -
            mE E) +
        (u : ℂ) * mE E * ∑ b : Zd d L, SB d L g b a * ∫ ω : Ω d L W,
          (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - mE E) *
            (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ - mE E) ∂(PF d L W g) := by
  have hz : (zt E u).im ≠ 0 := expAvg_hz hE hu1
  set z := zt E u with hzdef
  set m := mE E with hm
  set f : Zd d L → Ω d L W → ℂ := fun b ω =>
    loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩ with hf
  have hgI : ∀ b, Integrable (f b) (PF d L W g) := fun b => expAvg_integrable_gloop L W g u hz b
  have hgg : ∀ b, Integrable (fun ω => f b ω * f a ω) (PF d L W g) :=
    fun b => expAvg_integrable_gloop_mul L W g u hz b a
  have hres : ∫ ω : Ω d L W, Matrix.trace (HflowBlock d L W u ω *
      Gres (HflowBlock d L W u ω) z true * Eblk d L W a) ∂(PF d L W g) =
      1 + z * ∫ ω, f a ω ∂(PF d L W g) := by
    simp_rw [expAvg_trace_HGE L W u _ hz a]
    rw [integral_add (integrable_const _) ((hgI a).const_mul z), integral_const_mul,
      integral_const]
    simp
  have hst : 1 + z * ∫ ω, f a ω ∂(PF d L W g) =
      -(u : ℂ) * ∑ p : Zd d L, SB d L g p a * ∫ ω, f p ω * f a ω ∂(PF d L W g) := by
    have h := expAvg_stein L W g u hu0 hz a
    rw [hres] at h
    exact h
  have hmz : m * z + (u : ℂ) * m ^ 2 = -1 := by
    have hq := spectralM_quadratic (E := E) hE.le
    simp only [hzdef, zt]
    linear_combination hq
  have hSum1 := expAvg_sum_SB_col L g hL a
  change (∫ ω, f a ω ∂(PF d L W g)) - m =
    (u : ℂ) * m ^ 2 * ∑ b : Zd d L, SB d L g b a * ((∫ ω, f b ω ∂(PF d L W g)) - m) +
      (u : ℂ) * m * ∑ b : Zd d L, SB d L g b a * ∫ ω, (f b ω - m) * (f a ω - m) ∂(PF d L W g)
  have hZ : ∀ b, ∫ ω : Ω d L W, (f b ω - m) * (f a ω - m) ∂(PF d L W g) =
      (∫ ω, f b ω * f a ω ∂(PF d L W g)) - m * (∫ ω, f b ω ∂(PF d L W g)) -
        m * (∫ ω, f a ω ∂(PF d L W g)) + m ^ 2 := by
    intro b
    have i1 : Integrable (fun ω : Ω d L W => f b ω * f a ω) (PF d L W g) := hgg b
    have i2 : Integrable (fun ω : Ω d L W => m * f b ω) (PF d L W g) := (hgI b).const_mul m
    have i3 : Integrable (fun ω : Ω d L W => m * f a ω) (PF d L W g) := (hgI a).const_mul m
    have hfun : (fun ω : Ω d L W => (f b ω - m) * (f a ω - m)) =
        fun ω => f b ω * f a ω - m * f b ω - m * f a ω + m ^ 2 := by
      funext ω; ring
    have i12 : Integrable (fun ω : Ω d L W => f b ω * f a ω - m * f b ω) (PF d L W g) := i1.sub i2
    have i123 : Integrable (fun ω : Ω d L W => f b ω * f a ω - m * f b ω - m * f a ω)
        (PF d L W g) := i12.sub i3
    rw [hfun, integral_add i123 (integrable_const _), integral_sub i12 i3, integral_sub i1 i2,
      integral_const_mul, integral_const_mul, integral_const]
    simp
  simp_rw [hZ]
  set Ia := ∫ ω, f a ω ∂(PF d L W g) with hIa
  have e1 : ∑ b : Zd d L, SB d L g b a * ((∫ ω, f b ω ∂(PF d L W g)) - m) =
      (∑ b : Zd d L, SB d L g b a * ∫ ω, f b ω ∂(PF d L W g)) - m := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hSum1, one_mul]
  have e2 : ∑ b : Zd d L, SB d L g b a * ((∫ ω, f b ω * f a ω ∂(PF d L W g)) -
      m * (∫ ω, f b ω ∂(PF d L W g)) - m * Ia + m ^ 2) =
      (∑ b : Zd d L, SB d L g b a * ∫ ω, f b ω * f a ω ∂(PF d L W g)) -
        m * (∑ b : Zd d L, SB d L g b a * ∫ ω, f b ω ∂(PF d L W g)) - m * Ia + m ^ 2 := by
    have hb : ∀ b : Zd d L, SB d L g b a * ((∫ ω, f b ω * f a ω ∂(PF d L W g)) -
        m * (∫ ω, f b ω ∂(PF d L W g)) - m * Ia + m ^ 2) =
        SB d L g b a * (∫ ω, f b ω * f a ω ∂(PF d L W g)) -
          m * (SB d L g b a * ∫ ω, f b ω ∂(PF d L W g)) + SB d L g b a * (m ^ 2 - m * Ia) :=
      fun b => by ring
    simp_rw [hb]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hSum1]
    ring
  rw [e1, e2]
  set T1 := ∑ b : Zd d L, SB d L g b a * ∫ ω, f b ω ∂(PF d L W g)
  set T2 := ∑ b : Zd d L, SB d L g b a * ∫ ω, f b ω * f a ω ∂(PF d L W g)
  linear_combination (-m) * hst + Ia * hmz

end FixedSize

/-! ## 2. Deterministic inversion and the fixed-size bound -/

section Deterministic

open scoped Matrix.Norms.Operator

/-- Port of RBM1D `eq_Theta_of_selfConsistent` (RBM2D `step61_theta_solve`, `Step61.lean:428`):
`x = ξ S x + y` is solved by `x = Θ_ξ y`. -/
private theorem expAvg_theta_solve {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    {x y : Zd d L → ℂ} (h : ∀ a, x a = ξ * ∑ b, SB d L g b a * x b + y a) (a : Zd d L) :
    x a = ∑ a', Theta d L g ξ a a' * y a' := by
  have hy : y = (1 - ξ • SB d L g) *ᵥ x := by
    funext c
    have hc := h c
    have hm : ((1 - ξ • SB d L g) *ᵥ x) c = x c - ξ * ∑ b, SB d L g c b * x b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      simp [Matrix.mulVec, dotProduct]
    rw [hm]
    have e : ∑ b, SB d L g b c * x b = ∑ b, SB d L g c b * x b :=
      Finset.sum_congr rfl fun b _ => by rw [expAvg_SB_symm L g c b]
    rw [e] at hc
    linear_combination -hc
  have hx : Theta d L g ξ *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Theta_mul_of_three_le hL hξ, Matrix.one_mulVec]
  rw [← hx]
  rfl

/-- **Deterministic inversion** (RBM2D `step61_theta_solve` + `step61_theta_row_sum` + `step61_norm_solve`,
`Step61.lean:428-504`), `d ≥ 3`: `Θ_{u m²}` inverts `x = u m² S x + y` and its row sums are bounded by the
constant of `ekSameRow_holds` (`EKSameRow` at `s = 0`, `σ = +`, `κ' = √(2κ)/2`), with no `log L`
(RBM2D: `1 + cShortRow κ (1 + log L)`).  The constant depends on `d, Λ, κ` only. -/
theorem expAvg_norm_solve {d : ℕ} (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ E u : ℝ, |E| ≤ 2 - κ → 0 ≤ u → u < 1 →
        ∀ x y : Zd d L → ℂ, (∀ a, x a = ((u : ℂ) * mE E ^ 2) * ∑ b, SB d L g b a * x b + y a) →
          ∀ K : ℝ, (∀ a, ‖y a‖ ≤ K) → ∀ a, ‖x a‖ ≤ C * K := by
  obtain ⟨C, hC, hrow⟩ := ekSameRow_holds d Λ (Real.sqrt (2 * κ) / 2) hd hΛ (by positivity)
  refine ⟨C, hC, ?_⟩
  intro L _ hL g hg hgΛ E u hE hu0 hu1 x y h K hy a
  have hE2 : |E| ≤ 2 := by linarith [abs_nonneg E]
  have hm : ‖mE E‖ = 1 := norm_mE hE2
  have him := st6_mE_im_ge hκ hE
  have hU := hrow L hL g hg hgΛ (mE E) hm him true 0 u le_rfl hu0 hu1
  have hξ : ‖(u : ℂ) * mE E ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, hm, Complex.norm_of_nonneg hu0]
    simpa using hu1
  have hK : 0 ≤ K := (norm_nonneg _).trans (hy a)
  have hukernel : uKer d L g (PropSpin (mE E) true * PropSpin (mE E) true) 0 u =
      Theta d L g ((u : ℂ) * mE E ^ 2) := by
    simp [uKer, PropSpin, sq]
  rw [hukernel] at hU
  have hrowsum : ∑ a', ‖Theta d L g ((u : ℂ) * mE E ^ 2) a a'‖ ≤ C :=
    (RBM.sum_norm_row_le _ a).trans hU
  rw [expAvg_theta_solve g hL hξ h a]
  calc ‖∑ a', Theta d L g ((u : ℂ) * mE E ^ 2) a a' * y a'‖
      ≤ ∑ a', ‖Theta d L g ((u : ℂ) * mE E ^ 2) a a'‖ * K := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hy a') (norm_nonneg _)
    _ = (∑ a', ‖Theta d L g ((u : ℂ) * mE E ^ 2) a a'‖) * K := by rw [Finset.sum_mul]
    _ ≤ C * K := mul_le_mul_of_nonneg_right hrowsum hK

end Deterministic

section Combine

variable {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W]

private theorem expAvg_integrable_normsq (g u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (m : ℂ) (b : Zd d L) :
    Integrable (fun ω : Ω d L W =>
      ‖loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩ - m‖ ^ 2) (PF d L W g) := by
  refine Integrable.of_bound (C := ((((L * W) ^ d : ℕ) : ℝ) * ((|z.im|)⁻¹ * (((W : ℝ) ^ d)⁻¹)) +
    ‖m‖) ^ 2) (((expAvg_gloop_cont L W u hz b).sub continuous_const).norm.pow 2
      |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sub_le _ _).trans (add_le_add_left (expAvg_gloop_bdd L W u hz b ω) _)) 2

end Combine

/-- **The fixed-size deterministic core** (RBM2D `step61_expErr_le`, `Step61.lean:528`): second moments of
`g_b - m` bound `|𝔼 g_a - m|`; the constant depends on `d, Λ, κ` only (no `L`, `W`, `g`, `u`, `E`). -/
theorem expAvg_expErr_le {d : ℕ} (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ E u : ℝ, |E| ≤ 2 - κ → 0 ≤ u → u < 1 → ∀ K : ℝ,
        (∀ b : Zd d L, ∫ ω : Ω d L W,
          ‖loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - mE E‖ ^ 2 ∂(PF d L W g) ≤ K) →
        ∀ a : Zd d L,
          ‖(∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ ∂(PF d L W g)) - mE E‖ ≤
            C * K := by
  obtain ⟨C, hC, hsolve⟩ := expAvg_norm_solve hd Λ κ hΛ hκ
  refine ⟨C, hC, ?_⟩
  intro L W _ _ hL g hg hgΛ E u hE hu0 hu1 K hK a
  have hE' : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE'.le
  have hz := expAvg_hz hE' hu1
  set m := mE E with hm
  set y : Zd d L → ℂ := fun a => (u : ℂ) * m * ∑ b : Zd d L, SB d L g b a * ∫ ω : Ω d L W,
    (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - m) *
      (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ - m) ∂(PF d L W g) with hy
  have hself := expAvg_selfcons (d := d) L W g hL hE' hu0 hu1
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) ≤ ∫ ω : Ω d L W, ‖loopL d L W (HflowBlock d L W u ω) (zt E u)
      ⟨[true], [a]⟩ - m‖ ^ 2 ∂(PF d L W g) := integral_nonneg fun ω => sq_nonneg _
    exact this.trans (hK a)
  have hpair : ∀ b a : Zd d L, ‖∫ ω : Ω d L W,
      (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - m) *
        (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ - m) ∂(PF d L W g)‖ ≤ K := by
    intro b a
    refine (norm_integral_le_integral_norm _).trans ?_
    have hg : Integrable (fun ω : Ω d L W => (1 / 2 : ℝ) *
        (‖loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - m‖ ^ 2 +
          ‖loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ - m‖ ^ 2)) (PF d L W g) :=
      ((expAvg_integrable_normsq L W g u hz m b).add
        (expAvg_integrable_normsq L W g u hz m a)).const_mul _
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hg
      (Filter.Eventually.of_forall fun ω => ?_)).trans ?_
    · beta_reduce
      rw [norm_mul]
      nlinarith [sq_nonneg (‖loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - m‖ -
        ‖loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ - m‖)]
    · rw [integral_const_mul, integral_add (expAvg_integrable_normsq L W g u hz m b)
        (expAvg_integrable_normsq L W g u hz m a)]
      have := hK b
      have := hK a
      linarith
  have hyK : ∀ a : Zd d L, ‖y a‖ ≤ K := by
    intro a
    have hum : ‖(u : ℂ) * m‖ ≤ 1 := by
      rw [norm_mul, hm, norm_mE hE2, Complex.norm_of_nonneg hu0]
      simpa using hu1.le
    have hrow : ∑ b : Zd d L, ‖SB d L g b a‖ = 1 := by
      simp_rw [expAvg_SB_symm L g a]
      exact sum_norm_SB_row d L g hL a
    calc ‖y a‖ = ‖(u : ℂ) * m‖ * ‖∑ b : Zd d L, SB d L g b a * ∫ ω : Ω d L W,
          (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - m) *
            (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ - m) ∂(PF d L W g)‖ := by
          rw [hy]; simp only [mul_assoc, norm_mul]
      _ ≤ 1 * (∑ b : Zd d L, ‖SB d L g b a‖ * K) := by
          refine mul_le_mul hum ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_))
            (norm_nonneg _) zero_le_one
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hpair b a) (norm_nonneg _)
      _ = K := by rw [← Finset.sum_mul, hrow, one_mul, one_mul]
  exact hsolve L hL g hg hgΛ E u hE hu0 hu1 (fun b => (∫ ω : Ω d L W,
    loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ ∂(PF d L W g)) - m) y
    (fun a => hself a) K hyK a

/-! ## 3. Along the sequence: the floor, the envelope, the moments -/

section Sequence

variable {d : ℕ} (sz : Sizes d)

/-- **The floor** (new, `d ≥ 3`; RBM2D `scaleM ≤ N`, `Step61.lean:631`): `N⁻¹ ≤ W^{-d} B_{u,0}` for
`0 ≤ u < 1`: the first term of `B` is `≥ 0` and `W^{-d} (L^d (1-u))⁻¹ ≥ (W L)^{-d}`. -/
theorem expAvg_Bctl_ge {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n u := by
  have h1 : 0 < 1 - u := by linarith
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsize : ((sz.size n : ℕ) : ℝ)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow, mul_inv]
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    calc ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) ≤ ((sz.L n : ℕ) : ℝ) ^ d * 1 := by
          gcongr; linarith
      _ = ((sz.L n : ℕ) : ℝ) ^ d := mul_one _
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos h1, hsize]
  have h4 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h4.trans ?_
  rw [mul_add]
  have h5 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
      ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) := by positivity
  linarith

/-- **The envelope** (new, `d ≥ 3`; RBM2D has the hypothesis `RangeCond` and the block `hEnvpoly` of `step61_moment`, `Step61.lean:752-791`): `η_u⁻¹ ≤ N` along the flow for
`u ≤ lemT z`, eventually: `1 - u ≥ 1 - lemT z ≥ Im z/(1+|z|) ≥ N^{-1+ε}/4` (`ST_one_sub_lemT`, `‖z‖ ≤ 3`),
`Im m ≥ √(2κ)/2` (`st6_mE_im_ge`), and `N^ε ≥ 8/√(2κ)`. -/
theorem expAvg_eta_inv_le {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ lemT (z n) → (etaT (STflowE z n) u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hsz : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hz.1.2.2.1
  set c0 : ℝ := Real.sqrt (2 * κ) / 2 with hc0def
  have hc0 : 0 < c0 := by positivity
  have hev := ((tendsto_rpow_atTop hε).comp hsz).eventually (eventually_ge_atTop (4 / c0))
  filter_upwards [hev] with n hn u hu
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  obtain ⟨hre, him1, him2⟩ := hz.2 n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) him1
  have hzn : ‖z n‖ ≤ 3 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (z n)
    rw [abs_of_pos him] at h1
    linarith
  have h1 := ST_one_sub_lemT him
  have hlow : N ^ (-1 + ε) / 4 ≤ 1 - lemT (z n) := by
    refine le_trans ?_ h1
    rw [div_le_div_iff₀ (by norm_num) (by linarith [norm_nonneg (z n)])]
    nlinarith [Real.rpow_pos_of_pos hNpos (-1 + ε), norm_nonneg (z n)]
  have h1u : N ^ (-1 + ε) / 4 ≤ 1 - u := by linarith
  have hIm : c0 ≤ (mE (STflowE z n)).im := st6_mE_im_ge hκ (st6_flowE_le sz hz n)
  set a : ℝ := N ^ (1 - ε) with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hNa : N ^ (-1 + ε) = a⁻¹ := by
    rw [ha, ← Real.rpow_neg hNpos.le]; congr 1; ring
  have hNab : a * N ^ ε = N := by
    rw [ha, ← Real.rpow_add hNpos]
    simp
  have hηlow : a⁻¹ / 4 * c0 ≤ etaT (STflowE z n) u := by
    unfold etaT
    rw [hNa] at h1u
    exact mul_le_mul h1u hIm hc0.le (by linarith [inv_pos.2 hapos])
  have hpos : 0 < a⁻¹ / 4 * c0 := by positivity
  calc (etaT (STflowE z n) u)⁻¹ ≤ (a⁻¹ / 4 * c0)⁻¹ := inv_anti₀ hpos hηlow
    _ = a * (4 / c0) := by field_simp
    _ ≤ a * N ^ ε := by gcongr; exact hn
    _ = N := hNab

private theorem expAvg_Lloop_eq {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (σ : Bool)
    (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E t (fun _ : Fin 1 => σ) (fun _ => a) ω =
      loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) t (sz.slice n ω)) (zt E t)
        ⟨[σ], [a]⟩ := by
  unfold Lloop loopFine
  rw [loopM_eq_loopL]
  simp only [loopOf, List.ofFn_succ, List.ofFn_zero]
  rfl

private theorem expAvg_integral_slice {d : ℕ} (sz : Sizes d) {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] (n : ℕ) (F : Ω d (sz.L n) (sz.W n) → F')
    (hF : AEStronglyMeasurable F (PF d (sz.L n) (sz.W n) (sz.lam n))) :
    ∫ ω, F (sz.slice n ω) ∂(sz.seqP) = ∫ ω, F ω ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
  have hm : AEMeasurable (sz.slice n) sz.seqP := (sz.measurable_slice n).aemeasurable
  have hF' : AEStronglyMeasurable F (Measure.map (sz.slice n) sz.seqP) := by
    rw [sz.seqP_map_slice]; exact hF
  rw [← integral_map hm hF', sz.seqP_map_slice]

/-- **The envelope of one loop**: `‖𝓛^{(1)}_{u,+,a}‖ ≤ L^d η_u⁻¹` (`norm_gloop_le_crude`, `W` cancels). -/
private theorem expAvg_norm_loop_one_le (L W : ℕ) [NeZero L] [NeZero W] {d : ℕ} {E u : ℝ}
    (hE : |E| < 2) (hu1 : u < 1) (ω : Ω d L W) (b : Zd d L) :
    ‖loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩‖ ≤ (L : ℝ) ^ d * (etaT E u)⁻¹ := by
  have hz := expAvg_hz hE hu1
  have h := expAvg_gloop_bdd L W u hz b ω
  have him : |(zt E u).im| = etaT E u := by
    rw [etaT_eq_zt_im, abs_of_pos]
    rw [← etaT_eq_zt_im]
    exact etaT_pos hE hu1
  rw [him] at h
  refine h.trans (le_of_eq ?_)
  have hW : (W : ℝ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  push_cast
  rw [mul_pow]
  field_simp

/-- **The second moments** (RBM2D `step61_moment`, `Step61.lean:683`): `MomentDomAt` of `|𝓛^{(1)}_{u,+,b} - m|`
against `Bctl n (u n)`, from `(Gt_avgbound_flow)` (`LWAvgLaw`, a `Prec`, uniform over `b`) through the reverse
bridge `momentDomAt_of_stochDomAt_of_nonneg` with `B = 1` (`expAvg_Bctl_ge`), `Env n = L^d η⁻¹ + 1`,
`Kenv = 3` (`expAvg_eta_inv_le`, `L^d ≤ N`). -/
theorem expAvg_moment {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hut : ∀ n, u n ≤ lemT (z n))
    (hLW : LWAvgLaw sz (STflowE z) u) :
    MomentDomAt sz.seqP sz.size (U := fun n => Zd d (sz.L n))
      (fun n b ω => ‖Lloop sz n (STflowE z n) (u n) (fun _ : Fin 1 => true) (fun _ => b) ω -
        mE (STflowE z n)‖)
      (fun n _ => sz.Bctl n (u n)) := by
  have hsz : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hz.1.2.2.1
  have hu1 : ∀ n, u n < 1 := st5_t_lt_one sz hz hut
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => by linarith [st6_flowE_le sz hz n]
  refine momentDomAt_of_stochDomAt_of_nonneg sz.size hsz
    (Env := fun n => ((sz.L n : ℕ) : ℝ) ^ d * (etaT (STflowE z n) (u n))⁻¹ + 1)
    (Kenv := 3) (B := 1) (fun n b ω => norm_nonneg _) ?_
    (fun n _ => STBctl_pos sz n (hu1 n)) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ hLW
  · -- `hmeas`
    intro n b
    have hz' := expAvg_hz (hE2 n) (hu1 n)
    have h1 := (measurable_gloop_HflowBlock_sample d (sz.L n) (sz.W n) (u n) hz'
      ⟨[true], [b]⟩ (by simp [LoopIdx.WF])).comp (sz.measurable_slice n)
    simp only [expAvg_Lloop_eq]
    exact (h1.sub_const _).norm
  · -- `hΦlow`
    refine Filter.Eventually.of_forall fun n b => ?_
    rw [Real.rpow_neg_one]
    exact expAvg_Bctl_ge sz n (hu0 n) (hu1 n)
  · -- `hEnv0`
    intro n
    have := etaT_pos (hE2 n) (hu1 n)
    positivity
  · -- `henv`
    intro n b ω
    simp only [expAvg_Lloop_eq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mE (hE2 n).le]
    gcongr
    exact expAvg_norm_loop_one_le (sz.L n) (sz.W n) (hE2 n) (hu1 n) _ b
  · -- `hEnvpoly`
    filter_upwards [expAvg_eta_inv_le sz hκ hε hz, hsz.eventually (eventually_ge_atTop 2)] with n hη hN2
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have hN : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN2
    have hLd : ((sz.L n : ℕ) : ℝ) ^ d ≤ N := by
      rw [hNdef]
      have h1 : sz.L n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_left _ (sz.W_pos n)
      have h2 : (sz.L n) ^ d ≤ sz.size n := Nat.pow_le_pow_left h1 d
      exact_mod_cast h2
    have hη' := hη (u n) (hut n)
    have hη0 : 0 ≤ (etaT (STflowE z n) (u n))⁻¹ := (inv_pos.mpr (etaT_pos (hE2 n) (hu1 n))).le
    have h3' : (N : ℝ) ^ (3 : ℝ) = N ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    change ((sz.L n : ℕ) : ℝ) ^ d * (etaT (STflowE z n) (u n))⁻¹ + 1 ≤ N ^ (3 : ℝ)
    rw [h3']
    have h4 : ((sz.L n : ℕ) : ℝ) ^ d * (etaT (STflowE z n) (u n))⁻¹ ≤ N * N :=
      mul_le_mul hLd hη' hη0 (by linarith)
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ N) (by linarith : (0 : ℝ) ≤ N))
      (sub_nonneg.mpr hN)]

/-- **The charge `-`** (new; RBM2D `Step61Concl` has charge `+` only): `𝔼 𝓛^{(1)}_{u,-,a} = conj 𝔼 𝓛^{(1)}_{u,+,a}`
(`ST_Lloop_one_false` under the integral). -/
theorem expAvg_integral_conj {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (a : Zd d (sz.L n)) :
    ∫ ω, Lloop sz n E u (fun _ : Fin 1 => false) (fun _ => a) ω ∂(sz.seqP) =
      (starRingEnd ℂ) (∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP)) := by
  simp_rw [ST_Lloop_one_false sz n E u a]
  exact integral_conj

/-- **The boundary `u = 0`** (RBM2D `step61_check_u_zero`, `Step61.lean:998`): `G_0 = m I`, so the left side
of the pin vanishes (`integral_gloop_HflowBlock_zero`, `initialLoopValue_one_edge`, `mE_mul`). -/
theorem expAvg_u_zero {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (a : Zd d (sz.L n)) :
    ∫ ω, Lloop sz n E 0 (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP) = mE E := by
  have hm : initialGreenScalar E true = mE E := by
    have hmul := mE_mul hE.le
    unfold initialGreenScalar
    simp only [ite_true]
    exact inv_eq_of_mul_eq_one_right (by linear_combination (-1 : ℂ) * hmul)
  have h : ∀ ω, Lloop sz n E 0 (fun _ : Fin 1 => true) (fun _ => a) ω = mE E := by
    intro ω
    rw [expAvg_Lloop_eq, gloop_HflowBlock_zero, initialLoopValue_one_edge _ _ _ hE, hm]
  simp [h]

end Sequence

/-! ## 4. The pin -/

/-- **The pin's conclusion from `LWAvgLaw` alone** (RBM2D `step61`, `Step61.lean:853`), `d ≥ 3`, both charges:
`st6_prec_det_iff` reduces `STExpAvgAt` to "for every `τ > 0`, eventually, for all `(σ, a)`:
`‖𝔼 𝓛^{(1)}_{u,σ,a} - m(σ)‖ ≤ N^τ Bctl²`"; `σ = -` follows from `σ = +` by `expAvg_integral_conj`; for
`σ = +` the fixed-size bound `expAvg_expErr_le` (constant `C(d, 𝔡⁻¹, κ)`, `0 < lam ≤ 𝔡⁻¹` from `WO`) is applied at
`K = C₁ N^{τ/2} Bctl²` (`expAvg_moment` at `(τ/2, p = 1)`, slice integrals by `seqP_map_slice`), and
`C C₁ ≤ N^{τ/2}` eventually.  The premise `STLK` of the pin is not used. -/
theorem STExpAvgAt_of_LWAvgLaw {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hut : ∀ n, u n ≤ lemT (z n))
    (hLW : LWAvgLaw sz (STflowE z) u) : STExpAvgAt sz (STflowE z) u := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have h𝔡 : 0 < 𝔡 := hz.1.2.1
  have hWO : sz.WO 𝔡 := hz.1.2.2.2.2
  have hu1 : ∀ n, u n < 1 := st5_t_lt_one sz hz hut
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => by linarith [st6_flowE_le sz hz n]
  unfold STExpAvgAt
  refine (st6_prec_det_iff sz hsz (V := fun n => Bool × Zd d (sz.L n))
    (fun n p => ‖(∫ ω, Lloop sz n (STflowE z n) (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂(sz.seqP)) -
      mSigma (STflowE z n) p.1‖) (fun n _ => (sz.Bctl n (u n)) ^ 2)).2 ?_
  intro τ hτ
  obtain ⟨C, hC, hsolve⟩ := expAvg_expErr_le hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  obtain ⟨C₁, hC₁, hCn⟩ := expAvg_moment sz hκ hε hz u hu0 hut hLW (τ / 2) (half_pos hτ) 1
  have hlim : ∀ᶠ n in atTop, C * C₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually (eventually_ge_atTop (C * C₁))
  filter_upwards [hWO, hCn, hlim] with n hWOn hn hlimn
  have hlam0 : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hWOn.1
  have hlamle : sz.lam n ≤ 𝔡⁻¹ := hWOn.2
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  have hEκ := st6_flowE_le sz hz n
  have hz' := expAvg_hz (hE2 n) (hu1 n)
  set B : ℝ := sz.Bctl n (u n) with hBdef
  have hBpos : 0 < B := STBctl_pos sz n (hu1 n)
  have htrue : ∀ a : Zd d (sz.L n),
      ‖(∫ ω, Lloop sz n (STflowE z n) (u n) (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP)) -
        mE (STflowE z n)‖ ≤ N ^ τ * B ^ 2 := by
    intro a
    set K : ℝ := C₁ * (N ^ (τ / 2) * B ^ 2) with hKdef
    have hKint : ∀ b : Zd d (sz.L n), ∫ ω : Ω d (sz.L n) (sz.W n),
        ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) (u n) ω) (zt (STflowE z n) (u n))
          ⟨[true], [b]⟩ - mE (STflowE z n)‖ ^ 2 ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) ≤ K := by
      intro b
      have hcont : Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
          ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) (u n) ω') (zt (STflowE z n) (u n))
            ⟨[true], [b]⟩ - mE (STflowE z n)‖ ^ 2 :=
        (((expAvg_gloop_cont (sz.L n) (sz.W n) (u n) hz' b).sub continuous_const).norm).pow 2
      have hslice := expAvg_integral_slice sz n (fun ω' : Ω d (sz.L n) (sz.W n) =>
        ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) (u n) ω') (zt (STflowE z n) (u n))
          ⟨[true], [b]⟩ - mE (STflowE z n)‖ ^ 2) hcont.aestronglyMeasurable
      have h' := hn b
      simp only [Nat.cast_one, mul_one] at h'
      calc _ = ∫ ω, ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) (u n) (sz.slice n ω))
              (zt (STflowE z n) (u n)) ⟨[true], [b]⟩ - mE (STflowE z n)‖ ^ 2 ∂(sz.seqP) := hslice.symm
        _ = ∫ ω, |‖Lloop sz n (STflowE z n) (u n) (fun _ : Fin 1 => true) (fun _ => b) ω -
              mE (STflowE z n)‖| ^ 2 ∂(sz.seqP) := by
            congr 1; funext ω; simp only [abs_norm, expAvg_Lloop_eq]
        _ ≤ K := h'
    have hbound := hsolve (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) hlam0 hlamle (STflowE z n) (u n)
      hEκ (hu0 n) (hu1 n) K hKint a
    have hint_a : ∫ ω, Lloop sz n (STflowE z n) (u n) (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP) =
        ∫ ω : Ω d (sz.L n) (sz.W n), loopL d (sz.L n) (sz.W n)
          (HflowBlock d (sz.L n) (sz.W n) (u n) ω) (zt (STflowE z n) (u n)) ⟨[true], [a]⟩
          ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
      have := expAvg_integral_slice sz n (fun ω' : Ω d (sz.L n) (sz.W n) => loopL d (sz.L n) (sz.W n)
        (HflowBlock d (sz.L n) (sz.W n) (u n) ω') (zt (STflowE z n) (u n)) ⟨[true], [a]⟩)
        (expAvg_gloop_cont (sz.L n) (sz.W n) (u n) hz' a).aestronglyMeasurable
      simp only [expAvg_Lloop_eq]
      exact this
    rw [hint_a]
    refine hbound.trans ?_
    have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have ht0 : 0 ≤ N ^ (τ / 2) * B ^ 2 := by positivity
    calc C * K = (C * C₁) * (N ^ (τ / 2) * B ^ 2) := by rw [hKdef]; ring
      _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * B ^ 2) := mul_le_mul_of_nonneg_right hlimn ht0
      _ = N ^ τ * B ^ 2 := by rw [hNτ]; ring
  rintro ⟨σ, a⟩
  cases σ
  · simp only [mSigma, Bool.false_eq_true, ↓reduceIte]
    rw [expAvg_integral_conj sz n (STflowE z n) (u n) a, ← map_sub, Complex.norm_conj]
    exact htrue a
  · simp only [mSigma, ite_true]
    exact htrue a

/-- **`lem:improve_exp_aver`** (`6:12-21`), proved: the merged pin `STImproveExpAver` (`Step6Pins.lean:191`,
text unchanged) from `STExpAvgAt_of_LWAvgLaw`; the premise `STLK` is unused. -/
theorem stImproveExpAver_holds (d : ℕ) : STImproveExpAver d :=
  fun hd _κ _ε _𝔡 hκ hε _h𝔡 _𝔠 sz _z hz u hu0 hut hLW _hLK =>
    STExpAvgAt_of_LWAvgLaw sz hd hκ hε hz u hu0 hut hLW

end RBM.Gauss.Sizes

/-! ## 5. Compiled nonempty instances at `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`
(the merged Step-6 instance data `sz0, z0, tInst`, `szB, zB`, `szG`) -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- `STExpAvgAt_of_LWAvgLaw` at `(sz0, z0, u ≡ 1/16)`: every deterministic hypothesis is discharged
(`3 ≤ 3`, `0 < 1/10`, `flow_z0`, `0 ≤ 1/16`, `sz0_ht`); `LWAvgLaw` (`(Gt_avgbound_flow)`) stays a hypothesis. -/
theorem inst_expAvgAt_holds (hA : LWAvgLaw sz0 (STflowE z0) tInst) :
    STExpAvgAt sz0 (STflowE z0) tInst :=
  STExpAvgAt_of_LWAvgLaw sz0 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sz0_ht hA

/-- The merged `inst_improveExpAver` with the pin proved. -/
theorem inst_improveExpAver_holds (hA : LWAvgLaw sz0 (STflowE z0) tInst)
    (hK : STLK sz0 (STflowE z0) tInst) : STExpAvgAt sz0 (STflowE z0) tInst :=
  inst_improveExpAver (stImproveExpAver_holds 3) hA hK

/-- The merged `inst_expAvgU` with `hAvg` discharged. -/
theorem inst_expAvgU_holds (hS2 : STStep2Core sz0 (STflowE z0) sInst tInst)
    (hLKU : STLKU sz0 (STflowE z0) sInst tInst) : STExpAvgU sz0 (STflowE z0) sInst tInst :=
  inst_expAvgU (stImproveExpAver_holds 3) hS2 hLKU

/-- The merged `inst_skeleton6I` with `hAvg` discharged (regime (i)). -/
theorem inst_skeleton6I_avg (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3)
    (hDuQ : STExpDuhamelQ 3) (hDec : STExpDriftDecay 3) (hWd : STExpWardI 3) (hIni : STExpIniI 3)
    (hInt : STExpIntI 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_skeleton6I hLK hLW (stImproveExpAver_holds 3) hDu hDuQ hDec hWd hIni hInt

/-- The merged `inst_skeleton6II` with `hAvg` discharged (regime (ii)). -/
theorem inst_skeleton6II_avg (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3)
    (hInt : STExpIntII 3) (hWd : STExpWardII 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_skeleton6II hLK hLW (stImproveExpAver_holds 3) hDu hInt hWd

/-- The merged `inst_skeleton6IV` with `hAvg` discharged (regime (iv)). -/
theorem inst_skeleton6IV_avg (hDu : STExpDuhamelZ 3) (hLo : STExpDriftLo 3) (hInt : STExpIntIV 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_skeleton6IV (stImproveExpAver_holds 3) hDu hLo hInt

/-- `expAvg_eta_inv_le` at `(sz0, z0)` (eventual: do not look for a concrete `n`). -/
theorem inst_eta_inv_le :
    ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ lemT (z0 n) → (etaT (STflowE z0 n) u)⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) :=
  expAvg_eta_inv_le sz0 (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0

/-- `expAvg_u_zero` at `sz0`, `n = 0` (`L = 4`, `W = 32`), `E = 1/2`, `a = 0`. -/
theorem inst_expAvg_u_zero :
    ∫ ω, Lloop sz0 0 (1 / 2) 0 (fun _ : Fin 1 => true) (fun _ => 0) ω ∂(sz0.seqP) = mE (1 / 2) :=
  expAvg_u_zero sz0 0 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) 0

/-! ### Instances of the fixed-size and sequence lemmas (`d = 3`, `L = 4`, `W = 32`, `g = 1/64`, `E = 1/2`,
`u = 1/16`: the data of `sz0` at `n = 0`) -/

/-- The one-edge loop `𝓛^{(1)}_{u,+,b}` at the data of `sz0`, `n = 0`, `E = 1/2`, `u = 1/16`. -/
private def instLoop (b : Zd 3 4) (ω : Ω 3 4 32) : ℂ :=
  loopL 3 4 32 (HflowBlock 3 4 32 (1 / 16) ω) (zt (1 / 2) (1 / 16)) ⟨[true], [b]⟩

private theorem inst_E_lt : |(1 / 2 : ℝ)| < 2 := by
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num

/-- `expAvg_stein` at `d = 3`, `L = 4`, `W = 32`, `g = 1/64`, `u = 1/16`, `z = i`, `a = 0`. -/
theorem inst_expAvg_stein :
    ∫ ω : Ω 3 4 32, Matrix.trace (HflowBlock 3 4 32 (1 / 16) ω *
        Gres (HflowBlock 3 4 32 (1 / 16) ω) Complex.I true * Eblk 3 4 32 0) ∂(PF 3 4 32 (1 / 64)) =
      -((1 / 16 : ℝ) : ℂ) * ∑ p : Zd 3 4, SB 3 4 (1 / 64) p 0 * ∫ ω : Ω 3 4 32,
        loopL 3 4 32 (HflowBlock 3 4 32 (1 / 16) ω) Complex.I ⟨[true], [p]⟩ *
          loopL 3 4 32 (HflowBlock 3 4 32 (1 / 16) ω) Complex.I ⟨[true], [0]⟩ ∂(PF 3 4 32 (1 / 64)) :=
  expAvg_stein (d := 3) 4 32 (1 / 64) (1 / 16) (by norm_num) (z := Complex.I) (by simp) 0

/-- `expAvg_selfcons` at the same data, `E = 1/2`, `a = 0`. -/
theorem inst_expAvg_selfcons :
    (∫ ω : Ω 3 4 32, instLoop 0 ω ∂(PF 3 4 32 (1 / 64))) - mE (1 / 2) =
      ((1 / 16 : ℝ) : ℂ) * mE (1 / 2) ^ 2 * ∑ b : Zd 3 4, SB 3 4 (1 / 64) b 0 *
          ((∫ ω : Ω 3 4 32, instLoop b ω ∂(PF 3 4 32 (1 / 64))) - mE (1 / 2)) +
        ((1 / 16 : ℝ) : ℂ) * mE (1 / 2) * ∑ b : Zd 3 4, SB 3 4 (1 / 64) b 0 * ∫ ω : Ω 3 4 32,
          (instLoop b ω - mE (1 / 2)) * (instLoop 0 ω - mE (1 / 2)) ∂(PF 3 4 32 (1 / 64)) :=
  expAvg_selfcons (d := 3) 4 32 (1 / 64) (by norm_num) inst_E_lt (by norm_num) (by norm_num) 0

/-- `expAvg_norm_solve` at `d = 3`, `Λ = 1`, `κ = 1/10`, `L = 4`, `g = 1/64`, `E = 1/2`, `u = 1/16`, the
solution `x ≡ 1` of `x = u m² S x + y` (`y ≡ 1 - u m²`, `‖y‖ ≤ 2`), `K = 2`. -/
theorem inst_expAvg_norm_solve :
    ∃ C : ℝ, 0 < C ∧ ‖(fun _ : Zd 3 4 => (1 : ℂ)) 0‖ ≤ C * 2 := by
  obtain ⟨C, hC, h⟩ := expAvg_norm_solve (d := 3) (by norm_num) 1 (1 / 10) one_pos (by norm_num)
  have hrow : ∀ a : Zd 3 4, ∑ b : Zd 3 4, SB 3 4 (1 / 64) b a * (1 : ℂ) = 1 := fun a => by
    simpa using expAvg_sum_SB_col (d := 3) 4 (1 / 64) (by norm_num) a
  have hm : ‖mE (1 / 2)‖ = 1 := norm_mE inst_E_lt.le
  refine ⟨C, hC, h 4 (by norm_num) (1 / 64) (by norm_num) (by norm_num) (1 / 2) (1 / 16)
    (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => 1 - ((1 / 16 : ℝ) : ℂ) * mE (1 / 2) ^ 2) ?_ 2 ?_ 0⟩
  · intro a
    rw [hrow a]
    ring
  · intro a
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_pow, hm, Complex.norm_real]
    norm_num

/-- `expAvg_expErr_le` at `d = 3`, `Λ = 1`, `κ = 1/10`, `L = 4`, `W = 32`, `g = 1/64`, `E = 1/2`, `u = 1/16`,
`K = Σ_b 𝔼|𝓛_b - m|²` (each `𝔼|𝓛_b - m|² ≤ K`, `a = 0`). -/
theorem inst_expAvg_expErr_le :
    ∃ C : ℝ, 0 < C ∧
      ‖(∫ ω : Ω 3 4 32, instLoop 0 ω ∂(PF 3 4 32 (1 / 64))) - mE (1 / 2)‖ ≤
        C * ∑ b : Zd 3 4, ∫ ω : Ω 3 4 32, ‖instLoop b ω - mE (1 / 2)‖ ^ 2 ∂(PF 3 4 32 (1 / 64)) := by
  obtain ⟨C, hC, h⟩ := expAvg_expErr_le (d := 3) (by norm_num) 1 (1 / 10) one_pos (by norm_num)
  refine ⟨C, hC, h 4 32 (by norm_num) (1 / 64) (by norm_num) (by norm_num) (1 / 2) (1 / 16)
    (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num) (by norm_num) _ ?_ 0⟩
  intro b
  exact Finset.single_le_sum (f := fun b : Zd 3 4 => ∫ ω : Ω 3 4 32,
    ‖instLoop b ω - mE (1 / 2)‖ ^ 2 ∂(PF 3 4 32 (1 / 64)))
    (fun b _ => integral_nonneg fun ω => sq_nonneg _) (Finset.mem_univ b)

/-- `expAvg_Bctl_ge` at `sz0`, `n = 0`, `u = 1/16`. -/
theorem inst_expAvg_Bctl_ge : ((sz0.size 0 : ℕ) : ℝ)⁻¹ ≤ sz0.Bctl 0 (1 / 16) :=
  expAvg_Bctl_ge sz0 0 (by norm_num) (by norm_num)

/-- `expAvg_moment` at `(sz0, z0, u ≡ 1/16)`; `LWAvgLaw` stays a hypothesis. -/
theorem inst_expAvg_moment (hA : LWAvgLaw sz0 (STflowE z0) tInst) :
    MomentDomAt sz0.seqP sz0.size (U := fun n => Zd 3 (sz0.L n))
      (fun n b ω => ‖Lloop sz0 n (STflowE z0 n) (tInst n) (fun _ : Fin 1 => true) (fun _ => b) ω -
        mE (STflowE z0 n)‖)
      (fun n _ => sz0.Bctl n (tInst n)) :=
  expAvg_moment sz0 (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 tInst
    (fun n => by simp only [tInst]; norm_num) sz0_ht hA

/-- `expAvg_integral_conj` at `sz0`, `n = 0`, `E = 1/2`, `u = 1/16`, `a = 0`. -/
theorem inst_expAvg_integral_conj :
    ∫ ω, Lloop sz0 0 (1 / 2) (1 / 16) (fun _ : Fin 1 => false) (fun _ => 0) ω ∂(sz0.seqP) =
      (starRingEnd ℂ) (∫ ω, Lloop sz0 0 (1 / 2) (1 / 16) (fun _ : Fin 1 => true) (fun _ => 0) ω
        ∂(sz0.seqP)) :=
  expAvg_integral_conj sz0 0 (1 / 2) (1 / 16) 0

end RBM.Gauss.Step6Inst
