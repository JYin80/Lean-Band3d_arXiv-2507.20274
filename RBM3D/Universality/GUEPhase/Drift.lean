/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.LoopStep
import RBM3D.Universality.GUEPhase.Generator
import RBM3D.Universality.GUEPhase.Markov

/-!
# The one-step drift of the GUE-phase grid (UN-34, UN-35)

Ticket T2343.  Port of `RBM2D/Universality/GUEPhase/Drift.lean` (2067 lines, RBM2D commit `9e0f275`,
cited `Drift:<line>`) onto the merged `d`-general band layer.  The GUE analogue of the band
statements `oneStepEnvelope` (`RBM3D/Path/OneStep.lean`) and `condExp_loop_drift`
(`RBM3D/Path/LoopStep.lean`).  Renaming as in T2330: `d : Sizes` is `sz : Sizes d`, `Idx L W` is
`Idx d L W`, `Z2 L` is `Zd d L`, `BlockIndex L W` is `Vtx d L W`, `gloop L W (blockMat M)` is
`loopL d L W (blockMat d L W M)`, `spectralZ` is `zt`, `Gsig` is `Gres`, `Coord L W` is
`CoordF d L W`, `RBM.Endpoints.gueP/gueVar` are `RBM.Univ.gueP/gueVar`.

## Main results (namespace `RBM.Univ.GUEPhase`)

* `oneStepEnvelopeGUE` (`Drift:1474`): for Hermitian `M`, `|E| < 2`, a well-formed loop of length
  `k`, `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1` and `X ~ gueP d L W`,
  `‖E Φ_{u+Δ}(M + √Δ X) - Φ_u(M) - Δ · genMatGUE‖ ≤ envConst · Δ^{3/2}`, with the merged band
  envelope constant `envConst d L W` (`N^4`, `N = (W L)^d`), unchanged.
* `gueH_succ` (`Drift:1643`): `H_{k+1} = H_k + √(Δ/N) · seqXmat (ω (k+1))`.
* `condExp_loop_step_gue` (`Drift:1924`): the conditional step given `filt sz k` is the integral
  over one GUE increment `√Δ X`, `X ~ gueP`, added to `gueH k ω`.
* `condExp_loop_drift_gue` (`Drift:2034`): the conditional drift along the grid, bounded by the
  envelope (`K n ≠ 0` and `k < K n` are not used by the proof, as in the source).

## Reuse instead of copy (DECISIONS §153 (1))

Source §1-§3 (`Drift:60-707`: jets of a word of resolvent factors, the loop functional along a line
and the spectral path, their norm and Lipschitz bounds) and the law-free counts of source §4 are
not ported: the port calls the `OneStep_` twins of `RBM3D/Path/OneStep.lean` (`OneStep_J1`,
`OneStep_J2`, `OneStep_Dsp`, `OneStep_w1Lin`, `OneStep_continuous_w0/w1/w2`,
`OneStep_hasDerivAt_line0/1`, `OneStep_hasDerivAt_spec0/1`, `OneStep_norm_J1_le`,
`OneStep_norm_J2_le`, `OneStep_norm_J1_sub_le`, `OneStep_norm_J2_sub_le`, `OneStep_norm_one_le`,
`OneStep_norm_blockMat_Xmat_le`, `OneStep_card_Idx`, `OneStep_continuous_blockMat`,
`OneStep_sum_coord`, `OneStep_isHermitian_add_realSmul`), whose keyword `private` was deleted in
`OneStep.lean` (nothing else changed there).  GUE-specific counts (`gueVar_c ≤ N⁻¹`,
`Σ_c gueVar_c ≤ 2N`, the `gueP` marginals and moments) and source §5-§13 are ported.

## `d`-dependent lines

`(W L)^2` is `(W L)^d` (`Drift_one_le_N`, `Drift_gueVar_diag/offDiag/le_inv`, `E‖X‖ ≤ 4 N²`,
`Drift_size_pos`, `Drift_unitVar_div`, the crude bound of `Drift_norm_Phi_le`: `W⁻¹^2` is
`(W^d)⁻¹`); `|Coord| = 2 |Idx|²` is `d`-free.  No statement uses `3 ≤ d`.

Compiled nonempty instances: namespace `RBM.Univ.GUEPhase.DriftInst` (§14).  Every unpinned helper
is `private` and carries the source prefix `Drift_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix Finset RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 4. Counts: `Σ_c gueVar_c ≤ 2N`, and `‖X‖ ≤ 2 Σ_c |ω_c|` -/

section Counts

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `N = (W L)^d ≥ 1`. -/
private theorem Drift_one_le_N : (1 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
  have : 1 ≤ (W * L) ^ d :=
    Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
      (Nat.pos_of_ne_zero (NeZero.ne L)))
  exact_mod_cast this

/-! ### The GUE coordinate variances: `gueVar_c ≤ N⁻¹ ≤ 1` and `Σ_c gueVar_c ≤ 2 N`

(These replace the band counts through the row sums of `S^{(B)}`.) -/

/-- A diagonal GUE coordinate has variance `N⁻¹`, `N = (W L)^d`. -/
private theorem Drift_gueVar_diag (i : Idx d L W) (b : Bool) :
    ((gueVar d L W (i, i, b) : NNReal) : ℝ) = ((((W * L) ^ d : ℕ) : ℝ))⁻¹ := by
  simp [RBM.Univ.gueVar]

/-- An off-diagonal GUE coordinate has variance `(2N)⁻¹`. -/
private theorem Drift_gueVar_offDiag {i j : Idx d L W} (b : Bool) (hij : i ≠ j) :
    ((gueVar d L W (i, j, b) : NNReal) : ℝ) = (2 * (((W * L) ^ d : ℕ) : ℝ))⁻¹ := by
  simp [RBM.Univ.gueVar, hij]

/-- Every GUE coordinate has variance at most `N⁻¹`. -/
private theorem Drift_gueVar_le_inv (c : CoordF d L W) :
    (gueVar d L W c : ℝ) ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ := by
  obtain ⟨i, j, b⟩ := c
  by_cases hij : i = j
  · subst hij
    rw [Drift_gueVar_diag]
  · rw [Drift_gueVar_offDiag b hij, mul_inv]
    have h0 : (0 : ℝ) ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ := by positivity
    linarith

/-- Every GUE coordinate has variance at most `1`. -/
private theorem Drift_gueVar_le_one (c : CoordF d L W) : (gueVar d L W c : ℝ) ≤ 1 :=
  (Drift_gueVar_le_inv c).trans (inv_le_one_of_one_le₀ Drift_one_le_N)

/-- `Σ_c gueVar_c ≤ 2 N`, `N = |Idx|` (the exact value is `N + 1`: the unused coordinates
`(i, i, false)` and the lower triangle carry variance but a zero direction). -/
private theorem Drift_sum_gueVar_le :
    ∑ c : CoordF d L W, (gueVar d L W c : ℝ) ≤ 2 * (Fintype.card (Idx d L W) : ℝ) := by
  rw [OneStep_sum_coord]
  have hN0 : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := lt_of_lt_of_le one_pos Drift_one_le_N
  calc ∑ i : Idx d L W, ∑ j : Idx d L W,
        ((gueVar d L W (i, j, true) : ℝ) + (gueVar d L W (i, j, false) : ℝ))
      ≤ ∑ i : Idx d L W, ∑ j : Idx d L W, 2 * ((((W * L) ^ d : ℕ) : ℝ))⁻¹ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have h1 := Drift_gueVar_le_inv (L := L) (W := W) (i, j, true)
          have h2 := Drift_gueVar_le_inv (L := L) (W := W) (i, j, false)
          linarith
    _ = 2 * (Fintype.card (Idx d L W) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [OneStep_card_Idx]
        field_simp

/-! ### The coordinate law `gueP`: marginals and second moments -/

private theorem Drift_gueP_map_eval (c : CoordF d L W) :
    (gueP d L W).map (fun ω => ω c) = gaussianReal 0 (gueVar d L W c) :=
  Measure.infinitePi_map_eval _ c

private theorem Drift_integrable_sq_coord (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => (ω c) ^ 2) (gueP d L W) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (gueP d L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 2) ((gueP d L W).map fun ω => ω c) := by
    rw [Drift_gueP_map_eval]
    exact (memLp_id_gaussianReal (μ := 0) (v := gueVar d L W c) 2).integrable_sq
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem Drift_integral_sq_coord (c : CoordF d L W) :
    ∫ ω, (ω c) ^ 2 ∂(gueP d L W) = (gueVar d L W c : ℝ) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (gueP d L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ((gueP d L W).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, Drift_gueP_map_eval]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := gueVar d L W c)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-! ### First absolute moments of the Gaussian coordinates -/

private theorem Drift_integrable_abs_coord (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => |ω c|) (gueP d L W) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (Drift_integrable_sq_coord c))
    (continuous_abs.comp (continuous_apply c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|ω c| - 1), sq_abs (ω c)]

private theorem Drift_integral_abs_coord_le (c : CoordF d L W) :
    ∫ ω : Ω d L W, |ω c| ∂(gueP d L W) ≤ 1 := by
  have hint : Integrable (fun ω : Ω d L W => (1 + (ω c) ^ 2) / 2) (gueP d L W) :=
    ((integrable_const (1 : ℝ)).add (Drift_integrable_sq_coord c)).div_const 2
  have hmono : ∫ ω : Ω d L W, |ω c| ∂(gueP d L W) ≤ ∫ ω : Ω d L W, (1 + (ω c) ^ 2) / 2 ∂(gueP d L W) := by
    refine integral_mono (Drift_integrable_abs_coord c) hint fun ω => ?_
    nlinarith [sq_nonneg (|ω c| - 1), sq_abs (ω c)]
  refine hmono.trans ?_
  rw [integral_div, integral_add (integrable_const _) (Drift_integrable_sq_coord c),
    Drift_integral_sq_coord]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have := Drift_gueVar_le_one (L := L) (W := W) c
  linarith

private theorem Drift_integrable_sum_abs :
    Integrable (fun ω : Ω d L W => 2 * ∑ c : CoordF d L W, |ω c|) (gueP d L W) :=
  (integrable_finsetSum _ fun c _ => Drift_integrable_abs_coord c).const_mul 2

private theorem Drift_integrable_normX :
    Integrable (fun ω : Ω d L W => ‖blockMat d L W (Xmat d L W ω)‖) (gueP d L W) := by
  refine Integrable.mono' Drift_integrable_sum_abs ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (continuous_norm.comp
      (OneStep_continuous_blockMat.comp (continuous_Xmat d L W))).aestronglyMeasurable
  · rw [norm_norm]
    exact OneStep_norm_blockMat_Xmat_le ω

/-- `E ‖X‖ ≤ 4 N²` (in block coordinates), `N = (W L)^d`. -/
private theorem Drift_integral_normX_le :
    ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(gueP d L W) ≤ 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 := by
  calc ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(gueP d L W)
      ≤ ∫ ω : Ω d L W, 2 * ∑ c : CoordF d L W, |ω c| ∂(gueP d L W) :=
        integral_mono Drift_integrable_normX Drift_integrable_sum_abs
          fun ω => OneStep_norm_blockMat_Xmat_le ω
    _ = 2 * ∑ c : CoordF d L W, ∫ ω : Ω d L W, |ω c| ∂(gueP d L W) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => Drift_integrable_abs_coord c]
    _ ≤ 2 * ∑ _c : CoordF d L W, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => Drift_integral_abs_coord_le c)
          zero_le_two
    _ = 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        have : Fintype.card (CoordF d L W) = 2 * (Fintype.card (Idx d L W)) ^ 2 := by
          simp [Fintype.card_prod, Fintype.card_bool]
          ring
        rw [this]
        push_cast
        rw [OneStep_card_Idx]
        push_cast
        ring

end Counts

/-! ## 5. The derivative of `x ↦ E f(M + x X)` by Stein's identity -/

section Fine

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem Drift_blockMat_add_smul (A C : Matrix (Idx d L W) (Idx d L W) ℂ) (y : ℂ) :
    blockMat d L W (A + y • C) = blockMat d L W A + y • blockMat d L W C := by
  ext p q
  simp [blockMat]

/-- The reindexed sample matrix `M + x X_ω`. -/
private def Drift_Hs (M : Matrix (Idx d L W) (Idx d L W) ℂ) (x : ℝ) (ω : Ω d L W) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  blockMat d L W (M + (x : ℂ) • Xmat d L W ω)

private theorem Drift_Hs_eq (M : Matrix (Idx d L W) (Idx d L W) ℂ) (x : ℝ) (ω : Ω d L W) :
    Drift_Hs M x ω = blockMat d L W M + (x : ℂ) • blockMat d L W (Xmat d L W ω) :=
  Drift_blockMat_add_smul _ _ _

private theorem Drift_Hs_herm {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (x : ℝ)
    (ω : Ω d L W) : (Drift_Hs M x ω).IsHermitian :=
  (OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d L W ω) x).submatrix _

private theorem Drift_continuous_Hs (M : Matrix (Idx d L W) (Idx d L W) ℂ) (x : ℝ) :
    Continuous (Drift_Hs M x) :=
  OneStep_continuous_blockMat.comp
    (continuous_const.add ((continuous_Xmat d L W).const_smul (x : ℂ)))

private theorem Drift_Hs_update {M : Matrix (Idx d L W) (Idx d L W) ℂ} (x : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) (t : ℝ) :
    Drift_Hs M x (Function.update ω c t) = Drift_Hs M x ω
      + ((x * (t - ω c) : ℝ) : ℂ) • blockMat d L W (coordinateMatrix d L W c) := by
  rw [Drift_Hs, Drift_Hs, Xmat_update]
  ext p q
  simp only [blockMat, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Complex.real_smul, smul_eq_mul]
  push_cast
  ring

private theorem Drift_continuous_Gres {V : Type*} [TopologicalSpace V]
    {f : V → Matrix (Vtx d L W) (Vtx d L W) ℂ} (hf : Continuous f)
    (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun v => Gres (f v) z σ := by
  cases σ
  · exact continuous_green_of_isHermitian hf hh (by simpa using hz)
  · exact continuous_green_of_isHermitian hf hh hz

section Cont

variable {V : Type*} [TopologicalSpace V] {f : V → Matrix (Vtx d L W) (Vtx d L W) ℂ}
  (hf : Continuous f) (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
  (I : Loop.LoopIdx (Zd d L)) (D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ)
include hf hh hz

private theorem Drift_continuous_gloop : Continuous fun v => loopL d L W (f v) z I :=
  (continuous_matrixTrace d L W).comp
    (OneStep_continuous_w0 (fun σ => Drift_continuous_Gres hf hh hz σ) _)

private theorem Drift_continuous_J1 : Continuous fun v => OneStep_J1 (f v) z D I :=
  (continuous_matrixTrace d L W).comp
    (OneStep_continuous_w1 (fun σ => Drift_continuous_Gres hf hh hz σ) _)

private theorem Drift_continuous_J2 : Continuous fun v => OneStep_J2 (f v) z D I :=
  (continuous_matrixTrace d L W).comp
    (OneStep_continuous_w2 (fun σ => Drift_continuous_Gres hf hh hz σ) _)

end Cont

/-- Linearity of the first jet in the direction: `X = Σ_c ω_c C_c`. -/
private theorem Drift_J1_Xmat (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : Loop.LoopIdx (Zd d L)) (ω : Ω d L W) :
    OneStep_J1 H z (fun _ => blockMat d L W (Xmat d L W ω)) I
      = ∑ c : CoordF d L W, (ω c : ℂ) *
          OneStep_J1 H z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I := by
  have hX : (fun _ : Bool => blockMat d L W (Xmat d L W ω))
      = ∑ c : CoordF d L W, (ω c) • (fun _ : Bool => blockMat d L W (coordinateMatrix d L W c)) := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply]
    ext p q
    rw [Xmat_eq_sum_coordinates]
    simp [blockMat, Matrix.sum_apply]
  have hlin := map_sum (OneStep_w1Lin (fun σ => Gres H z σ) (Eblk d L W) (I.σ.zip I.a))
    (fun c : CoordF d L W => (ω c) • (fun _ : Bool => blockMat d L W (coordinateMatrix d L W c)))
    Finset.univ
  simp only [map_smul] at hlin
  unfold OneStep_J1
  rw [hX]
  change Matrix.trace ((OneStep_w1Lin (fun σ => Gres H z σ) (Eblk d L W) (I.σ.zip I.a)) _) = _
  rw [hlin, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.trace_smul, Complex.real_smul]
  rfl

/-- A Gaussian coordinate times a bounded continuous observable is integrable. -/
private theorem Drift_integrable_coord_mul (c : CoordF d L W) {g : Ω d L W → ℂ}
    (hg : Continuous g) {C : ℝ} (hb : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω : Ω d L W => (ω c : ℂ) * g ω) (gueP d L W) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (gueP d L W) := (measurable_pi_apply c).aemeasurable
  have hg' : Integrable (fun x : ℝ => x) ((gueP d L W).map fun ω => ω c) := by
    rw [Drift_gueP_map_eval]
    exact RBM.integrable_id_gaussianReal (var := gueVar d L W c)
  have hcoord : Integrable (fun ω : Ω d L W => ω c) (gueP d L W) :=
    (integrable_map_measure hg'.aestronglyMeasurable hf).1 hg'
  have h := hcoord.ofReal.bdd_mul hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa [Complex.real_smul, mul_comm] using h

section SteinStep

variable {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
  {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF)
include hM hz hwf

/-- The coordinate Stein identity, for the first jet along the coordinate direction. -/
private theorem Drift_stein_coord (x : ℝ) (c : CoordF d L W) :
    ∫ ω : Ω d L W, (ω c : ℂ) *
        OneStep_J1 (Drift_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W)
      = ((gueVar d L W c : ℝ) : ℂ) * ((x : ℂ) * ∫ ω : Ω d L W,
        OneStep_J2 (Drift_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W))
    := by
  set Cb := blockMat d L W (coordinateMatrix d L W c) with hCb
  have hCh : Cb.IsHermitian := (coordinateMatrix_isHermitian d L W c).submatrix _
  set g : Ω d L W → ℂ := fun ω => OneStep_J1 (Drift_Hs M x ω) z (fun _ => Cb) I with hg
  set g' : Ω d L W → ℂ := fun ω => (x : ℂ) * OneStep_J2 (Drift_Hs M x ω) z (fun _ => Cb) I
    with hg'
  have hgc : Continuous g :=
    Drift_continuous_J1 (Drift_continuous_Hs M x) (Drift_Hs_herm hM x) hz I _
  have hg'c : Continuous g' :=
    continuous_const.mul
      (Drift_continuous_J2 (Drift_continuous_Hs M x) (Drift_Hs_herm hM x) hz I _)
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hgb : ∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C := ⟨_, fun ω =>
    OneStep_norm_J1_le (Drift_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb) (fun _ => le_rfl) hwf⟩
  have hg'b : ∃ C : ℝ, ∀ ω, ‖g' ω‖ ≤ C := ⟨|x| * _, fun ω => by
    rw [hg', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (OneStep_norm_J2_le (Drift_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb)
        (fun _ => le_rfl) hwf) (abs_nonneg _)⟩
  have hderiv : ∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c) := by
    intro ω
    have hAh := Drift_Hs_herm hM x ω
    have hφ := OneStep_hasDerivAt_line1 hAh hCh hz I (x * (ω c - ω c))
    have hh : HasDerivAt (fun t : ℝ => x * (t - ω c)) x (ω c) := by
      simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul x
    have hcomp := hφ.scomp (ω c) hh
    have hfun : (fun t : ℝ => g (Function.update ω c t)) =
        ((fun s : ℝ => OneStep_J1 (Drift_Hs M x ω + (s : ℂ) • Cb) z (fun _ => Cb) I) ∘
          fun t : ℝ => x * (t - ω c)) := by
      funext t
      simp only [Function.comp, hg, Drift_Hs_update, hCb]
    rw [hfun]
    refine hcomp.congr_deriv ?_
    simp [hg']
  have h := GaussianProduct.stein (gueVar d L W) c g g' hgc hg'c hderiv hgb hg'b
  have hlaw : gueP d L W = GaussianProduct.law (gueVar d L W) := rfl
  rw [← hlaw] at h
  simp only [Complex.real_smul] at h
  rw [h, hg', integral_const_mul]

/-- **The derivative of `x ↦ E f(M + x X)`**: `x Σ_c gueVar_c E ∂²_c f(M + x X)`, by Stein. -/
private theorem Drift_hasDerivAt_F (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ ω : Ω d L W, loopL d L W (Drift_Hs M y ω) z I ∂(gueP d L W))
      ((x : ℂ) * ∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M x ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W)) x := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hcontgl : ∀ y : ℝ, Continuous fun ω : Ω d L W => loopL d L W (Drift_Hs M y ω) z I :=
    fun y => Drift_continuous_gloop (Drift_continuous_Hs M y) (Drift_Hs_herm hM y) hz I
  have hint : ∀ y : ℝ, Integrable (fun ω : Ω d L W => loopL d L W (Drift_Hs M y ω) z I) (gueP d L W) :=
    fun y => Integrable.of_bound (hcontgl y).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude d L W (Drift_Hs_herm hM y ω) hη le_rfl I hwf)
  have hJc : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      OneStep_J1 (Drift_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I :=
    fun c => Drift_continuous_J1 (Drift_continuous_Hs M x) (Drift_Hs_herm hM x) hz I _
  have hF'cont : Continuous fun ω : Ω d L W =>
      OneStep_J1 (Drift_Hs M x ω) z (fun _ => blockMat d L W (Xmat d L W ω)) I := by
    simp only [Drift_J1_Xmat]
    exact continuous_finsetSum _ fun c _ =>
      (Complex.continuous_ofReal.comp (continuous_apply c)).mul (hJc c)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gueP d L W)
    (s := Set.univ) (x₀ := x)
    (F := fun y ω => loopL d L W (Drift_Hs M y ω) z I)
    (F' := fun y ω => OneStep_J1 (Drift_Hs M y ω) z (fun _ => blockMat d L W (Xmat d L W ω)) I)
    (bound := fun ω => ((Fintype.card (Vtx d L W) : ℝ) *
      ((I.length : ℝ) * |z.im|⁻¹ ^ (I.length + 1))) * ‖blockMat d L W (Xmat d L W ω)‖)
    Filter.univ_mem (Filter.Eventually.of_forall fun y => (hcontgl y).aestronglyMeasurable)
    (hint x) hF'cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω y _ =>
      (OneStep_norm_J1_le (Drift_Hs_herm hM y ω) hη le_rfl (norm_nonneg _) (fun _ => le_rfl)
        hwf).trans (le_of_eq (by ring)))
    (Drift_integrable_normX.const_mul _)
    (Filter.Eventually.of_forall fun ω y _ => by
      have hXb : (blockMat d L W (Xmat d L W ω)).IsHermitian := (Xmat_isHermitian d L W ω).submatrix _
      have := OneStep_hasDerivAt_line0 hMb hXb hz I y
      simpa only [Drift_Hs_eq] using this)
  refine hD.congr_deriv ?_
  simp only [Drift_J1_Xmat]
  rw [integral_finsetSum _ fun c _ => Drift_integrable_coord_mul c (hJc c)
    (fun ω => OneStep_norm_J1_le (Drift_Hs_herm hM x ω) hη le_rfl (norm_nonneg _)
      (fun _ => le_rfl) hwf)]
  simp_rw [Drift_stein_coord hM hz hwf x]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

end SteinStep

end Fine


/-! ## 6. The space step: `E f(M + τ X) - f(M) - τ² g(M)` -/

section SpaceStep

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem Drift_card_Block :
    (Fintype.card (Vtx d L W) : ℝ) = (((W * L) ^ d : ℕ) : ℝ) := by
  rw [card_BlockIndex, mul_comm]

/-- The coordinate directions have norm at most `2` (in block coordinates). -/
private theorem Drift_norm_Cb_le (c : CoordF d L W) : ‖blockMat d L W (coordinateMatrix d L W c)‖ ≤ 2 := by
  have h := OneStep_norm_blockMat_Xmat_le (L := L) (W := W) (Pi.single c (1 : ℝ))
  have h1 : ∑ c' : CoordF d L W, |(Pi.single c (1 : ℝ) : CoordF d L W → ℝ) c'| = 1 := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ c) h
  rw [h1] at h
  simpa [coordinateMatrix] using h

/-- The `g`-part: `g_u(M) = ½ Σ_c gueVar_c ∂²_c f(M)`. -/
private def Drift_g (z : ℂ) (I : Loop.LoopIdx (Zd d L)) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) *
    OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I

variable {M : Matrix (Idx d L W) (Idx d L W) ℂ} {z : ℂ} {I : Loop.LoopIdx (Zd d L)}

/-- The Lipschitz estimate of one coordinate second jet along the Gaussian sample. -/
private theorem Drift_coord_sub_le (hM : M.IsHermitian) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) (c : CoordF d L W) (y : ℝ) (ω : Ω d L W) :
    ‖OneStep_J2 (Drift_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I‖
      ≤ (((Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (I.length + 2) * η⁻¹ ^ (I.length + 3)) * 4) * |y|) * ‖blockMat d L W (Xmat d L W ω)‖ := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have h := OneStep_norm_J2_sub_le (Drift_Hs_herm hM y ω) hMb hη hz (D := fun _ =>
    blockMat d L W (coordinateMatrix d L W c)) (b := 2) zero_le_two (fun _ => Drift_norm_Cb_le c) hwf
  have hd : ‖Drift_Hs M y ω - blockMat d L W M‖ = |y| * ‖blockMat d L W (Xmat d L W ω)‖ := by
    rw [Drift_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [hd] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- The key size estimate: the derivative of `ψ(y) = F(y) - F(0) - y² g(M)` is `O(y²)`. -/
private theorem Drift_psi_deriv_le (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) {y : ℝ} (hy : 0 ≤ y) :
    ‖(y : ℂ) * ∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W)
      - ((2 * y : ℝ) : ℂ) * Drift_g z I M‖
      ≤ (32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
          ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3))) * y ^ 2 := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  set C₃ : ℝ := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
    (I.length + 2) * η⁻¹ ^ (I.length + 3)) * 4 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  have hcont : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      OneStep_J2 (Drift_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I :=
    fun c => Drift_continuous_J2 (Drift_continuous_Hs M y) (Drift_Hs_herm hM y) hz' I _
  have hint : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W =>
      OneStep_J2 (Drift_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) (gueP d L W) :=
    fun c => Integrable.of_bound (hcont c).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        OneStep_norm_J2_le (Drift_Hs_herm hM y ω) hη hz (norm_nonneg _) (fun _ => le_rfl) hwf)
  -- one coordinate
  have hone : ∀ c : CoordF d L W,
      ‖(∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I‖
      ≤ (C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
    intro c
    have hsub : (∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I
        = ∫ ω : Ω d L W, (OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I
          - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) ∂(gueP d L W) := by
      rw [integral_sub (hint c) (integrable_const _)]
      simp
    rw [hsub]
    refine (norm_integral_le_of_norm_le ((Drift_integrable_normX.const_mul (C₃ * |y|)))
      (Filter.Eventually.of_forall fun ω =>
        Drift_coord_sub_le hM hη hz hwf c y ω)).trans ?_
    rw [integral_const_mul, abs_of_nonneg hy]
    have := Drift_integral_normX_le (d := d) (L := L) (W := W)
    rw [← OneStep_card_Idx] at this
    calc C₃ * y * ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(gueP d L W)
        ≤ C₃ * y * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := rfl
  have hsum : ∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) * ∫ ω : Ω d L W, OneStep_J2
        (Drift_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W)
      - 2 * Drift_g z I M
      = ∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) := by
    simp only [Drift_g, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hmain : (y : ℂ) * ∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) * ∫ ω : Ω d L W, OneStep_J2
        (Drift_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W)
      - ((2 * y : ℝ) : ℂ) * Drift_g z I M
      = (y : ℂ) * ∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) := by
    rw [← hsum]
    push_cast
    ring
  rw [hmain, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
  have hsn : ‖∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I)‖
      ≤ (2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : CoordF d L W, ‖((gueVar d L W c : ℝ) : ℂ) *
          ((∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
            (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W))
          - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I)‖
        ≤ ∑ c : CoordF d L W, (gueVar d L W c : ℝ) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun c _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gueVar d L W c).coe_nonneg]
            exact mul_le_mul_of_nonneg_left (hone c) (gueVar d L W c).coe_nonneg
      _ = (∑ c : CoordF d L W, (gueVar d L W c : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right Drift_sum_gueVar_le (by positivity)
  calc y * ‖∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I)‖
      ≤ y * ((2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hsn hy
    _ = _ := by rw [hC₃]; ring

/-- **The space step** for the law `gueP`: `‖E f(M + τ X) - f(M) - τ² g(M)‖ ≤ (Λ'/3) τ³`. -/
private theorem Drift_space_step (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) z I ∂(gueP d L W)) - loopL d L W (blockMat d L W M) z I
        - ((τ ^ 2 : ℝ) : ℂ) * Drift_g z I M‖
      ≤ ((32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
          ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3))) / 3)
        * τ ^ 3 := by
  set Λ : ℝ := 32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
    ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3)) with hΛ
  set F : ℝ → ℂ := fun y => ∫ ω : Ω d L W, loopL d L W (Drift_Hs M y ω) z I ∂(gueP d L W) with hF
  have hF0 : F 0 = loopL d L W (blockMat d L W M) z I := by
    simp [hF, Drift_Hs]
  set ψ : ℝ → ℂ := fun y => F y - F 0 - ((y ^ 2 : ℝ) : ℂ) * Drift_g z I M with hψ
  set ψ' : ℝ → ℂ := fun y => (y : ℂ) * ∑ c : CoordF d L W, ((gueVar d L W c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, OneStep_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(gueP d L W)
      - ((2 * y : ℝ) : ℂ) * Drift_g z I M with hψ'
  have hd : ∀ y : ℝ, HasDerivAt ψ (ψ' y) y := by
    intro y
    have h1 := ((Drift_hasDerivAt_F hM hz' hwf y).sub_const (F 0)).sub
      ((((hasDerivAt_pow 2 y).ofReal_comp)).mul_const (Drift_g z I M))
    refine h1.congr_deriv ?_
    simp only [hψ']
    push_cast
    ring
  have hcont : ContinuousOn ψ (Set.Icc 0 τ) := fun y _ => (hd y).continuousAt.continuousWithinAt
  have hB : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Λ / 3 * y ^ 3) (Λ * y ^ 2) y := by
    intro y
    refine ((hasDerivAt_pow 3 y).const_mul (Λ / 3)).congr_deriv ?_
    push_cast
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (f' := ψ') (a := 0)
    (b := τ) hcont (fun y _ => (hd y).hasDerivWithinAt)
    (by simp [hψ]) hB
    (fun y hy => Drift_psi_deriv_le hM hz' hη hz hwf hy.1)
  have := key (x := τ) ⟨hτ, le_rfl⟩
  simp only [hψ] at this
  rw [hF0] at this
  exact this

end SpaceStep

/-! ## 7. The time step, the closure of the constant, and the envelope -/

section TimeStep

/-- Second-order Taylor bound (the fencing lemma twice). -/
private theorem Drift_taylor2 {f f₁ f₂ : ℝ → ℂ} {a b B : ℝ} (hab : a ≤ b)
    (h1 : ∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x)
    (h2 : ∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x) (hB : ∀ x ∈ Set.Icc a b, ‖f₂ x‖ ≤ B) :
    ‖f b - f a - ((b - a : ℝ) : ℂ) * f₁ a‖ ≤ B * (b - a) ^ 2 / 2 := by
  have hc1 : ContinuousOn f₁ (Set.Icc a b) := fun x hx => (h2 x hx).continuousAt.continuousWithinAt
  have hs1 := norm_image_sub_le_of_norm_deriv_right_le_segment (f := f₁) (f' := f₂) (C := B) hc1
    (fun x hx => (h2 x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) (fun x hx => hB x ⟨hx.1, hx.2.le⟩)
  set ψ : ℝ → ℂ := fun x => f x - f a - ((x - a : ℝ) : ℂ) * f₁ a with hψ
  have hd : ∀ x ∈ Set.Icc a b, HasDerivAt ψ (f₁ x - f₁ a) x := by
    intro x hx
    have h := ((h1 x hx).sub_const (f a)).sub
      ((((hasDerivAt_id x).sub_const a).ofReal_comp).mul_const (f₁ a))
    refine h.congr_deriv ?_
    simp
  have hB' : ∀ x : ℝ, HasDerivAt (fun x : ℝ => B * (x - a) ^ 2 / 2) (B * (x - a)) x := by
    intro x
    refine ((((hasDerivAt_id x).sub_const a).pow 2).const_mul B |>.div_const 2).congr_deriv ?_
    simp
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ)
    (f' := fun x => f₁ x - f₁ a) (a := a) (b := b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) (by simp [hψ]) hB'
    (fun x hx => by simpa [mul_comm] using hs1 x ⟨hx.1, hx.2.le⟩)
  exact key ⟨hab, le_rfl⟩

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem Drift_norm_Dsp_le {E : ℝ} (hE : |E| < 2) (σ : Bool) :
    ‖OneStep_Dsp d L W E σ‖ ≤ 1 := by
  have hm : ‖spectralMSign E σ‖ = 1 := by
    cases σ <;> simp [spectralMSign, norm_spectralM hE.le]
  unfold OneStep_Dsp
  rw [norm_smul, hm, one_mul]
  exact OneStep_norm_one_le

private theorem Drift_eta_pos {E u : ℝ} (hE : |E| < 2) (hu : u < 1) : 0 < etaT E u :=
  mul_pos (by linarith) (spectralM_im_pos hE)

/-- **The time step**: Taylor expansion of `v ↦ f_v(A)` at fixed `A`. -/
private theorem Drift_time_step {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1) {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) :
    ‖loopL d L W (blockMat d L W A) (zt E (u + Δ)) I - loopL d L W (blockMat d L W A) (zt E u) I
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W A) (zt E u) (OneStep_Dsp d L W E) I‖
      ≤ ((Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) * Δ ^ 2 / 2 := by
  have hAb : (blockMat d L W A).IsHermitian := hA.submatrix _
  have hη := Drift_eta_pos hE hu1
  have hv : ∀ v ∈ Set.Icc u (u + Δ), (zt E v).im ≠ 0 := fun v hv => by
    rw [spectralZ_im]
    exact (mul_pos (by linarith [hv.2]) (spectralM_im_pos hE)).ne'
  have hvη : ∀ v ∈ Set.Icc u (u + Δ), etaT E (u + Δ) ≤ |(zt E v).im| :=
    fun v hv => spectralZ_im_gap hE hu1 hv
  have h := Drift_taylor2 (f := fun v => loopL d L W (blockMat d L W A) (zt E v) I)
    (f₁ := fun v => OneStep_J1 (blockMat d L W A) (zt E v) (OneStep_Dsp d L W E) I)
    (f₂ := fun v => OneStep_J2 (blockMat d L W A) (zt E v) (OneStep_Dsp d L W E) I)
    (a := u) (b := u + Δ)
    (B := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
      (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) (by linarith)
    (fun v hv' => OneStep_hasDerivAt_spec0 hAb (hv v hv') I)
    (fun v hv' => OneStep_hasDerivAt_spec1 hAb (hv v hv') I)
    (fun v hv' => by
      have := OneStep_norm_J2_le hAb hη (hvη v hv') zero_le_one (D := OneStep_Dsp d L W E)
        (Drift_norm_Dsp_le hE) hwf
      simpa using this)
  simpa using h

end TimeStep

section Assembly

/-- The closure of the constant: `⅔·16·… ≤ 16 (k+3)⁴ N⁴ (1 + q)^{k+4}` with `q = η⁻¹`. -/
private theorem Drift_closure (k : ℕ) {N q : ℝ} (hN : 1 ≤ N) (hq : 0 ≤ q) :
    32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
      + (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
    ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * (1 + q) ^ (k + 4) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hK : (1 : ℝ) ≤ 1 + q := by linarith
  have hq3 : q ^ (k + 3) ≤ (1 + q) ^ (k + 3) := pow_le_pow_left₀ hq (by linarith) _
  have hq2 : q ^ (k + 2) ≤ (1 + q) ^ (k + 3) :=
    (pow_le_pow_left₀ hq (by linarith) _).trans (pow_le_pow_right₀ hK (by omega))
  have h4 : (1 + q) ^ (k + 3) ≤ (1 + q) ^ (k + 4) := pow_le_pow_right₀ hK (by omega)
  have ha3 : (k : ℝ) * (k + 1) * (k + 2) ≤ ((k : ℝ) + 3) ^ 3 := by nlinarith [sq_nonneg (k : ℝ)]
  have ha2 : (k : ℝ) * (k + 1) ≤ ((k : ℝ) + 3) ^ 3 := by nlinarith [sq_nonneg (k : ℝ)]
  have hN4 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have hN1 : N ≤ N ^ 4 := by nlinarith [pow_le_pow_right₀ hN (show 1 ≤ 4 by norm_num)]
  have hP : 0 ≤ ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3) := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hq0 : 0 ≤ q ^ (k + 3) := by positivity
  have e1 : 32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
      ≤ (32 / 3) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)) := by
    have : (k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3) ≤ ((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3) :=
      mul_le_mul ha3 hq3 hq0 (by positivity)
    calc 32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
        = (32 / 3) * N ^ 4 * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) := by ring
      _ ≤ (32 / 3) * N ^ 4 * (((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3)) := by gcongr
      _ = _ := by ring
  have e2 : (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
      ≤ (9 / 2) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)) := by
    have h5 : (k : ℝ) * (k + 1) * q ^ (k + 2) ≤ ((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3) :=
      mul_le_mul ha2 hq2 (by positivity) (by positivity)
    have h6 : N * (1 / 2 + 4 * N ^ 2) ≤ (9 / 2) * N ^ 4 := by nlinarith
    calc (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
        = (N * (1 / 2 + 4 * N ^ 2)) * ((k : ℝ) * (k + 1) * q ^ (k + 2)) := by ring
      _ ≤ ((9 / 2) * N ^ 4) * (((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3)) :=
          mul_le_mul h6 h5 (by positivity) (by positivity)
      _ = _ := by ring
  have e3 : (32 / 3 + 9 / 2) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3))
      ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * (1 + q) ^ (k + 4) := by
    have h7 : ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)
        ≤ ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4) := by gcongr
    have h8 : 3 * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4))
        ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [h7, h8]
  linarith

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The mixed second derivative along a coordinate line, as the second jet. -/
private theorem Drift_deriv_deriv {M C : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (hC : C.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    deriv (deriv (fun y : ℝ => loopL d L W (blockMat d L W (M + (y : ℂ) • C)) z I)) 0
      = OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W C) I := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hCb : (blockMat d L W C).IsHermitian := hC.submatrix _
  simp only [Drift_blockMat_add_smul]
  have h1 : deriv (fun y : ℝ => loopL d L W (blockMat d L W M + (y : ℂ) • blockMat d L W C) z I)
      = fun y : ℝ => OneStep_J1 (blockMat d L W M + (y : ℂ) • blockMat d L W C) z (fun _ => blockMat d L W C) I := by
    funext y
    exact (OneStep_hasDerivAt_line0 hMb hCb hz I y).deriv
  rw [h1]
  simpa using (OneStep_hasDerivAt_line1 hMb hCb hz I 0).deriv

/-- **The one-step expansion with its envelope for one GUE increment** (the GUE analogue of
`oneStepEnvelope` of `Path/OneStep.lean`): for Hermitian `M`, `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1` and a
well-formed loop of length `k`,
`‖E Φ_{u+Δ}(M + √Δ X) - Φ_u(M) - Δ · genMatGUE_u(M)‖ ≤ envConst · Δ^{3/2}` with `X ~ gueP d L W`
and the band envelope `envConst`.  The proof splits the error into the space step at fixed time
`u` (`Drift_space_step`, by Stein for the product law `gueP`) and the time step at fixed sample
(`Drift_time_step`, by Taylor), and closes the constant with `Drift_closure`. -/
theorem oneStepEnvelopeGUE :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), |E| < 2 → ∀ (I : Loop.LoopIdx (Zd d L)), I.WF →
      ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
        ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
          ‖(∫ ω', loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω'))
                (zt E (u + Δ)) I ∂(gueP d L W)) -
              loopL d L W (blockMat d L W M) (zt E u) I -
              (Δ : ℂ) * genMatGUE d L W E u M I‖ ≤
            envConst d L W E I.length (u + Δ) * Δ ^ ((3 : ℝ) / 2) := by
  intro d L W _ _ E hE I hwf u Δ hu hΔ hu1 M hM
  have hΔ1 : Δ < 1 := by linarith
  set τ : ℝ := Real.sqrt Δ with hτ
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg Δ
  have hτ2 : τ ^ 2 = Δ := Real.sq_sqrt hΔ
  have hτΔ : Δ ≤ τ := by nlinarith
  have hτ3 : Δ ^ ((3 : ℝ) / 2) = τ ^ 3 := by
    rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hΔ]
    norm_num
  have hη : 0 < etaT E (u + Δ) := Drift_eta_pos hE hu1
  have hzu : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'
  have hηu : etaT E (u + Δ) ≤ |(zt E u).im| :=
    spectralZ_im_gap hE hu1 ⟨le_rfl, by linarith⟩
  have hηv : etaT E (u + Δ) ≤ |(zt E (u + Δ)).im| :=
    spectralZ_im_gap (s := u) hE hu1 ⟨by linarith, le_rfl⟩
  have hzv : (zt E (u + Δ)).im ≠ 0 := fun h => absurd hηv (by rw [h]; simpa using hη)
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  set c₁ : ℝ := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
    (etaT E (u + Δ))⁻¹ ^ (I.length + 2)) with hc₁
  -- the generator, in the jets
  have hgen : genMatGUE d L W E u M I = Drift_g (zt E u) I M
      + OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I := by
    unfold genMatGUE Drift_g
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Drift_deriv_deriv hM (coordinateMatrix_isHermitian d L W c) hzu I]
    · exact (OneStep_hasDerivAt_spec0 hMb hzu I).deriv
  -- integrability of the sample functionals
  have hint : ∀ v : ℝ, (zt E v).im ≠ 0 → Integrable
      (fun ω : Ω d L W => loopL d L W (Drift_Hs M τ ω) (zt E v) I) (gueP d L W) := fun v hv => by
    have hv' : 0 < |(zt E v).im| := abs_pos.mpr hv
    exact Integrable.of_bound (Drift_continuous_gloop (Drift_continuous_Hs M τ)
      (Drift_Hs_herm hM τ) hv I).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude d L W (Drift_Hs_herm hM τ ω) hv' le_rfl I hwf)
  -- the space step
  have hT2 := Drift_space_step hM hzu hη hηu hwf hτ0
  -- the time step, integrated
  have hT1 : ‖(∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (zt E (u + Δ)) I ∂(gueP d L W))
      - (∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (zt E u) I ∂(gueP d L W))
      - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I‖
      ≤ c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
    have hpt : ∀ ω : Ω d L W, ‖loopL d L W (Drift_Hs M τ ω) (zt E (u + Δ)) I
        - loopL d L W (Drift_Hs M τ ω) (zt E u) I
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I‖
        ≤ c₁ * Δ ^ 2 / 2 + (c₁ * Δ * τ) * ‖blockMat d L W (Xmat d L W ω)‖ := by
      intro ω
      have hA : (M + (τ : ℂ) • Xmat d L W ω).IsHermitian :=
        OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d L W ω) τ
      have h1 := Drift_time_step hA hE hΔ hu1 hwf
      have h2 := OneStep_norm_J1_sub_le (Drift_Hs_herm hM τ ω) hMb hη hηu zero_le_one
        (D := OneStep_Dsp d L W E) (Drift_norm_Dsp_le hE) hwf
      have hd : ‖Drift_Hs M τ ω - blockMat d L W M‖ = τ * ‖blockMat d L W (Xmat d L W ω)‖ := by
        rw [Drift_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hτ0]
      rw [hd] at h2
      have hsplit : loopL d L W (Drift_Hs M τ ω) (zt E (u + Δ)) I
          - loopL d L W (Drift_Hs M τ ω) (zt E u) I
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I
          = (loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E (u + Δ)) I
            - loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E u) I
            - (Δ : ℂ) * OneStep_J1 (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E u)
              (OneStep_Dsp d L W E) I)
            + (Δ : ℂ) * (OneStep_J1 (Drift_Hs M τ ω) (zt E u) (OneStep_Dsp d L W E) I
              - OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I) := by
        simp only [Drift_Hs]
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h3 : ‖(Δ : ℂ) * (OneStep_J1 (Drift_Hs M τ ω) (zt E u) (OneStep_Dsp d L W E) I
          - OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I)‖
          ≤ Δ * (c₁ * (τ * ‖blockMat d L W (Xmat d L W ω)‖)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
        refine mul_le_mul_of_nonneg_left ?_ hΔ
        refine h2.trans (le_of_eq ?_)
        rw [hc₁]
        ring
      have h1' : ‖loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E (u + Δ)) I
            - loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E u) I
            - (Δ : ℂ) * OneStep_J1 (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E u)
              (OneStep_Dsp d L W E) I‖ ≤ c₁ * Δ ^ 2 / 2 := h1
      calc _ ≤ c₁ * Δ ^ 2 / 2 + Δ * (c₁ * (τ * ‖blockMat d L W (Xmat d L W ω)‖)) := add_le_add h1' h3
        _ = _ := by ring
    have hsub : (∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (zt E (u + Δ)) I ∂(gueP d L W))
        - (∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (zt E u) I ∂(gueP d L W))
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I
        = ∫ ω : Ω d L W, (loopL d L W (Drift_Hs M τ ω) (zt E (u + Δ)) I
          - loopL d L W (Drift_Hs M τ ω) (zt E u) I
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I)
            ∂(gueP d L W) := by
      have i12 : Integrable (fun ω : Ω d L W => loopL d L W (Drift_Hs M τ ω) (zt E (u + Δ)) I
          - loopL d L W (Drift_Hs M τ ω) (zt E u) I) (gueP d L W) :=
        (hint _ hzv).sub (hint _ hzu)
      rw [integral_sub i12 (integrable_const _), integral_sub (hint _ hzv) (hint _ hzu)]
      simp
    rw [hsub]
    have ib : Integrable (fun ω : Ω d L W => c₁ * Δ ^ 2 / 2
        + (c₁ * Δ * τ) * ‖blockMat d L W (Xmat d L W ω)‖) (gueP d L W) :=
      (integrable_const _).add (Drift_integrable_normX.const_mul (c₁ * Δ * τ))
    refine (norm_integral_le_of_norm_le ib (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) (Drift_integrable_normX.const_mul _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hν := Drift_integral_normX_le (d := d) (L := L) (W := W)
    rw [← OneStep_card_Idx] at hν
    have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
    have hΔ2 : Δ ^ 2 ≤ Δ * τ := by nlinarith
    calc c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(gueP d L W)
        ≤ c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          gcongr
      _ ≤ c₁ * (Δ * τ) / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          gcongr
      _ = c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          rw [← hτ2]
          ring
  -- assembly
  have hLHS : (∫ ω : Ω d L W, loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω))
        (zt E (u + Δ)) I ∂(gueP d L W)) - loopL d L W (blockMat d L W M) (zt E u) I
        - (Δ : ℂ) * genMatGUE d L W E u M I
      = ((∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (zt E u) I ∂(gueP d L W))
          - loopL d L W (blockMat d L W M) (zt E u) I
          - ((τ ^ 2 : ℝ) : ℂ) * Drift_g (zt E u) I M)
        + ((∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (zt E (u + Δ)) I ∂(gueP d L W))
          - (∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (zt E u) I ∂(gueP d L W))
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I) := by
    rw [hgen, hτ2]
    simp only [Drift_Hs]
    ring
  rw [hLHS]
  refine (norm_add_le _ _).trans ((add_le_add hT2 hT1).trans ?_)
  rw [hτ3, OneStep_card_Idx, Drift_card_Block]
  have hN : (1 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    have : 1 ≤ (W * L) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
        (Nat.pos_of_ne_zero (NeZero.ne L)))
    exact_mod_cast this
  have hcl := Drift_closure I.length hN (inv_nonneg.mpr hη.le)
  unfold envConst
  have hτ3' : 0 ≤ τ ^ 3 := by positivity
  rw [hc₁, Drift_card_Block]
  calc _ = (32 * (((W * L) ^ d : ℕ) : ℝ) ^ 3 * (((W * L) ^ d : ℕ) : ℝ) *
            ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * (etaT E (u + Δ))⁻¹ ^ (I.length + 3))
            / 3
          + ((((W * L) ^ d : ℕ) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
            (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) * (1 / 2 + 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2))
          * τ ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcl hτ3'

end Assembly

/-! ## 8. The one-step recursion of the GUE-phase grid path -/

section Step

variable {d : ℕ} (sz : Sizes d)

/-- **The GUE-phase grid one-step recursion** `H_{k+1} = H_k + √(Δ/N) X_{k+1}`, `N = sz.size n`. -/
theorem gueH_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    gueH sz t1 t0 K n (k + 1) ω
      = gueH sz t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ) •
          Sizes.seqXmat sz n (ω (k + 1)) := by
  have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  unfold gueH
  rw [hins, Finset.sum_insert hnotmem, smul_add]
  abel

end Step

/-! ## 9. The complex-valued freezing lemma for `Pgue sz` -/

section FreezeC

variable {d : ℕ} {sz : Sizes d}

/-- The complex-valued freezing lemma for `Pgue sz`.  `gueCondExp_freeze` is real-valued; the
complex case
is its real and imaginary parts, glued with `ContinuousLinearMap.comp_condExp_comm`. -/
private theorem Drift_condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
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

end FreezeC


/-! ## 10. The observable of the Hermitian part: continuity and a global bound

(Copies of the private `LoopStep_herm`, `LoopStep_Phi` of `Path/LoopStep.lean`.) -/

section Observable

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The Hermitian part `½ (A + Aᴴ)`. -/
private def Drift_herm (A : Matrix (Idx d L W) (Idx d L W) ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  (1 / 2 : ℝ) • (A + Aᴴ)

private theorem Drift_herm_isHermitian (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    (Drift_herm A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (star_trivial (1 / 2 : ℝ))

private theorem Drift_herm_of_isHermitian {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) : Drift_herm A = A := by
  unfold Drift_herm
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem Drift_continuous_herm :
    Continuous (Drift_herm : Matrix (Idx d L W) (Idx d L W) ℂ → _) := by
  unfold Drift_herm
  have h1 : Continuous fun A : Matrix (Idx d L W) (Idx d L W) ℂ => Aᴴ :=
    continuous_id.matrix_conjTranspose
  exact Continuous.const_smul (continuous_id.add h1) (1 / 2 : ℝ)

/-- The loop observable of the Hermitian part of a matrix. -/
private def Drift_Phi (d L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (I : Loop.LoopIdx (Zd d L))
    (A : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  loopL d L W (blockMat d L W (Drift_herm A)) z I

private theorem Drift_continuous_Phi {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    Continuous (Drift_Phi d L W z I) := by
  unfold Drift_Phi
  exact Drift_continuous_gloop (f := fun A => blockMat d L W (Drift_herm A))
    ((Drift_continuous_herm (L := L) (W := W)).matrix_submatrix _ _)
    (fun A => (Drift_herm_isHermitian A).submatrix _) hz I

private theorem Drift_norm_Phi_le {z : ℂ} (hz : z.im ≠ 0) {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF)
    (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ‖Drift_Phi d L W z I A‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) * (|z.im|⁻¹ * (((W : ℝ) ^ d)⁻¹)) ^ I.a.length :=
  norm_gloop_le_crude d L W ((Drift_herm_isHermitian A).submatrix _) (abs_pos.mpr hz) le_rfl I hwf

private theorem Drift_isHermitian_add_smul {p X : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hp : p.IsHermitian) (hX : X.IsHermitian) (r : ℝ) :
    (p + (r : ℂ) • X).IsHermitian :=
  hp.add (hX.smul (by simp [IsSelfAdjoint]))

end Observable


/-! ## 11. The law of the unit slice, rescaled to `gueP`

Under `gueUnit sz` the matrix `N^{-1/2} · slice d n x` has the law `gueP d (sz.L n) (sz.W n)`.  Copies
of the private lemmas `GUEPhaseGrid_map_slice_infinitePi`, `GUEPhaseGrid_map_smul_infinitePi` of
`Grid.lean` and of the variance step `hunit` of `map_gueH_last`. -/

section LawTransfer

variable {d : ℕ} {sz : Sizes d}

/-- The size-`n` slice of an independent Gaussian family on `SeqCoord d`. -/
private lemma Drift_map_slice_infinitePi (w : Sizes.SeqCoord sz → ℝ≥0) (n : ℕ) :
    (Measure.infinitePi fun c => gaussianReal 0 (w c)).map (Sizes.slice sz n)
      = Measure.infinitePi fun c : CoordF d (sz.L n) (sz.W n) => gaussianReal 0 (w ⟨n, c⟩) := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  let e : CoordF d (sz.L n) (sz.W n) → Sizes.SeqCoord sz := fun c => ⟨n, c⟩
  have he : Function.Injective e := by
    intro c c' h
    simpa [e] using h
  let t' : Sizes.SeqCoord sz → Set ℝ := fun c =>
    if h : c.1 = n then t (h ▸ c.2) else Set.univ
  have hpre : Sizes.slice sz n ⁻¹' Set.pi (↑s) t = Set.pi (↑(s.image e)) t' := by
    ext ω
    constructor
    · intro h c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      simpa [t', e, Sizes.slice] using h a ha
    · intro h a ha
      have hc : e a ∈ s.image e := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa [t', e, Sizes.slice] using h (e a) hc
  have ht' : ∀ c ∈ s.image e, MeasurableSet (t' c) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    simpa [t', e] using ht a
  rw [Measure.map_apply (Sizes.measurable_slice sz n)
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)),
    hpre, Measure.infinitePi_pi _ ht']
  rw [Finset.prod_image he.injOn]
  apply Finset.prod_congr rfl
  intro a ha
  simp [t', e]

/-- Scaling every coordinate of an independent centred Gaussian family by `s` multiplies the
variances by `s²`. -/
private lemma Drift_map_smul_infinitePi {ι : Type*} (s : ℝ) (v : ι → ℝ≥0) :
    (Measure.infinitePi fun c => gaussianReal 0 (v c)).map (fun x : ι → ℝ => s • x)
      = Measure.infinitePi (fun c => gaussianReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s) * v c)) := by
  have hfmeas : ∀ c : ι, Measurable (s * ·) := fun c => by fun_prop
  have h1 : (Measure.infinitePi fun c => gaussianReal 0 (v c)).map
        (fun x : ι → ℝ => fun c => s * x c)
      = Measure.infinitePi (fun c => (gaussianReal 0 (v c)).map (s * ·)) :=
    Measure.infinitePi_map_pi (μ := fun c => gaussianReal 0 (v c)) (f := fun _ => (s * ·)) hfmeas
  have heq : (fun x : ι → ℝ => s • x) = (fun x : ι → ℝ => fun c => s * x c) := by
    funext x c; simp [smul_eq_mul]
  rw [heq, h1]
  congr 1
  funext c
  rw [gaussianReal_map_const_mul, mul_zero]

/-- The rescaled slice `x ↦ N^{-1/2} · slice d n x`, `N = sz.size n`. -/
private def Drift_scaledSlice {d : ℕ} (sz : Sizes d) (n : ℕ) (x : Sizes.SeqΩ sz) : Ω d (sz.L n) (sz.W n) :=
  (Real.sqrt ((sz.size n : ℕ) : ℝ))⁻¹ • Sizes.slice sz n x

private lemma Drift_measurable_scaledSlice (n : ℕ) : Measurable (Drift_scaledSlice sz n) := by
  unfold Drift_scaledSlice
  exact (Sizes.measurable_slice sz n).const_smul ((Real.sqrt ((sz.size n : ℕ) : ℝ))⁻¹)

private lemma Drift_size_pos (n : ℕ) : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
  have h1 : 0 < sz.W n := sz.W_pos n
  have h2 : 0 < sz.L n := by have := sz.three_le_L n; omega
  have : 0 < sz.size n := by
    unfold Sizes.size; positivity
  exact_mod_cast this

/-- The unit variance `1` (diagonal) or `1/2` (off the diagonal), divided by `N`, is `gueVar`. -/
private lemma Drift_unitVar_div (n : ℕ) (c : CoordF d (sz.L n) (sz.W n)) :
    ((gueUnitVar sz ⟨n, c⟩ : ℝ≥0) : ℝ) / ((sz.size n : ℕ) : ℝ)
      = (gueVar d (sz.L n) (sz.W n) c : ℝ) := by
  have hsz : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  unfold gueUnitVar RBM.Univ.gueVar
  by_cases hc : c.1 = c.2.1
  · simp only [hc, ite_true, hsz]
    push_cast
    simp
  · simp only [hc, ite_false, hsz]
    push_cast
    field_simp

/-- **The law of the rescaled unit slice**: `(gueUnit sz).map (N^{-1/2} · slice d n) = gueP`. -/
private lemma Drift_map_scaledSlice (n : ℕ) :
    (gueUnit sz).map (Drift_scaledSlice sz n) = gueP d (sz.L n) (sz.W n) := by
  have hN := Drift_size_pos (sz := sz) n
  have hsm : Measurable (fun x : Ω d (sz.L n) (sz.W n) => (Real.sqrt ((sz.size n : ℕ) : ℝ))⁻¹ • x) :=
    by fun_prop
  have hcomp : Drift_scaledSlice sz n =
      (fun x : Ω d (sz.L n) (sz.W n) => (Real.sqrt ((sz.size n : ℕ) : ℝ))⁻¹ • x) ∘
        Sizes.slice sz n := rfl
  rw [hcomp, ← Measure.map_map hsm (Sizes.measurable_slice sz n)]
  unfold gueUnit
  rw [Drift_map_slice_infinitePi (gueUnitVar sz) n, Drift_map_smul_infinitePi]
  unfold gueP
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  congr 1
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_mk, ← Drift_unitVar_div n c]
  have h2 : ((Real.sqrt ((sz.size n : ℕ) : ℝ))⁻¹) ^ 2 = (((sz.size n : ℕ) : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hN.le]
  rw [h2]
  ring

/-- Pointwise: `√(Δ/N) · seqXmat d n x = √Δ · Xmat (N^{-1/2} · slice d n x)`. -/
private lemma Drift_seqXmat_scaled (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (x : Sizes.SeqΩ sz) :
    (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ) • Sizes.seqXmat sz n x
      = (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
        Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x) := by
  have hN := Drift_size_pos (sz := sz) n
  unfold Drift_scaledSlice
  rw [Xmat_smul]
  have hreal : ∀ (r : ℝ) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      r • M = (r : ℂ) • M := fun r M => by
    ext i j
    simp [Complex.real_smul]
  rw [hreal, smul_smul, Real.sqrt_div' _ hN.le, div_eq_mul_inv, Complex.ofReal_mul]
  rfl

private lemma Drift_gueH_succ' (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    gueH sz t1 t0 K n (k + 1) ω
      = gueH sz t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
          Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n (ω (k + 1))) := by
  rw [gueH_succ, Drift_seqXmat_scaled]

end LawTransfer

/-! ## 12. The one-step conditional expectation -/

section LoopStepGUE

variable {d : ℕ} (sz : Sizes d)

/-- A private copy of the (private) `StandardBorelSpace` instance of `Markov.lean`. -/
private instance Drift_instStandardBorelSpaceMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

/-- The grid path is `filt sz k`-measurable as a matrix-valued map (entrywise from
`gueH_adapted`). -/
private theorem Drift_measurable_gueH_filt (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable[filt sz k] (gueH sz t1 t0 K n k) :=
  @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun i =>
    @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun j =>
      (gueH_adapted sz t1 t0 K n k i j).measurable

/-- **The GUE analogue of `condExp_loop_step`** (`Path/LoopStep.lean`): the freezing lemma
applied to the one-step recursion `gueH_succ`, for the loop observable
`Φ_{u_{k+1}} = 𝓛(blockMat d (sz.L n) (sz.W n) ·, z_{u_{k+1}}, I)`.  The conditional expectation given `filt sz k` is the
integral of the observable over one GUE increment `√Δ X`, `X ~ gueP d (sz.L n) (sz.W n)`, added to the
`gueH k ω`.  Under `gueUnit sz` the matrix `√(Δ/N) seqXmat d n x` has the law of `√Δ Xmat` under
`gueP`, because `gueVar = gueUnitVar / N`. -/
theorem condExp_loop_step_gue (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ)
    (hE : |E| < 2) {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    (hu1 : gridTime t1 t0 K n (k + 1) < 1) :
    (Pgue sz)[fun ω : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (k + 1) ω))
          (zt E (gridTime t1 t0 K n (k + 1))) I | filt sz k]
      =ᵐ[Pgue sz] fun ω =>
        ∫ x, loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω
            + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) x))
          (zt E (gridTime t1 t0 K n (k + 1))) I ∂(gueP d (sz.L n) (sz.W n)) := by
  classical
  have hz : (zt E (gridTime t1 t0 K n (k + 1))).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (sub_pos.2 hu1) (spectralM_im_pos hE)).ne'
  set z : ℂ := zt E (gridTime t1 t0 K n (k + 1)) with hzdef
  set Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
    Drift_Phi d (sz.L n) (sz.W n) z I with hΦdef
  have hΦcont : Continuous Φ := Drift_continuous_Phi hz I
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ sz → ℂ :=
    fun p x => Φ (p + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
      Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x)) with hFdef
  have hXmeas : Measurable (fun x : Sizes.SeqΩ sz =>
      Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x)) :=
    (continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Drift_measurable_scaledSlice n)
  have hFmeas : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => F p.1 p.2) := by
    have h2 : Measurable fun x : Sizes.SeqΩ sz =>
        (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
          Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x) :=
      hXmeas.const_smul (Real.sqrt (gridStep t1 t0 K n) : ℂ)
    have h3 : Measurable fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
        Sizes.SeqΩ sz => p.1 + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
          Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n p.2) :=
      measurable_fst.add (h2.comp measurable_snd)
    have h4 := hΦcont.measurable.comp h3
    exact h4
  have hFbdd : ∀ p x, ‖F p x‖ ≤ (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) *
      (|z.im|⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) ^ I.a.length :=
    fun p x => Drift_norm_Phi_le hz hwf _
  have hYmeas : Measurable[filt sz k] (gueH sz t1 t0 K n k) :=
    Drift_measurable_gueH_filt sz t1 t0 K n k
  have hYmeas' : Measurable (gueH sz t1 t0 K n k) := hYmeas.mono ((filt sz).le k) le_rfl
  have hFInt : ∀ p, Integrable (F p) (gueUnit sz) := by
    intro p
    have hpair : Measurable (fun x : Sizes.SeqΩ sz => (p, x)) :=
      measurable_const.prodMk measurable_id
    have hm : Measurable (fun x : Sizes.SeqΩ sz => F p x) := by
      have h := hFmeas.comp hpair
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun x => hFbdd p x)).integrable le_top
  have hIntTarget : Integrable (fun ω : PathΩ sz => F (gueH sz t1 t0 K n k ω) (ω (k + 1)))
      (Pgue sz) := by
    have hm : Measurable (fun ω : PathΩ sz => F (gueH sz t1 t0 K n k ω) (ω (k + 1))) := by
      have h := hFmeas.comp (hYmeas'.prodMk (measurable_pi_apply (k + 1)))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hEq : (fun ω : PathΩ sz =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (k + 1) ω)) z I)
      = fun ω => F (gueH sz t1 t0 K n k ω) (ω (k + 1)) := by
    funext ω
    have hH : (gueH sz t1 t0 K n (k + 1) ω).IsHermitian :=
      gueH_isHermitian sz t1 t0 K n (k + 1) ω
    change _ = Drift_Phi d (sz.L n) (sz.W n) z I _
    rw [← Drift_gueH_succ' (sz := sz) t1 t0 K n k ω]
    unfold Drift_Phi
    rw [Drift_herm_of_isHermitian hH]
  rw [hEq]
  filter_upwards [Drift_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget] with ω hω
  rw [hω]
  have hp : (gueH sz t1 t0 K n k ω).IsHermitian := gueH_isHermitian sz t1 t0 K n k ω
  set f : Ω d (sz.L n) (sz.W n) → ℂ := fun y =>
    loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y)) z I with hfdef
  have hfeq : f = fun y => Φ (gueH sz t1 t0 K n k ω
      + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y) := by
    funext y
    have hh := Drift_isHermitian_add_smul hp (Xmat_isHermitian d (sz.L n) (sz.W n) y)
      (Real.sqrt (gridStep t1 t0 K n))
    simp only [hΦdef, Drift_Phi, Drift_herm_of_isHermitian hh, hfdef]
  have hfcont : Continuous f := by
    rw [hfeq]
    have h2 : Continuous fun y : Ω d (sz.L n) (sz.W n) =>
        (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y :=
      (continuous_Xmat d (sz.L n) (sz.W n)).const_smul (Real.sqrt (gridStep t1 t0 K n) : ℂ)
    exact hΦcont.comp (continuous_const.add h2)
  have hFf : ∀ x, F (gueH sz t1 t0 K n k ω) x = f (Drift_scaledSlice sz n x) := by
    intro x
    have hh := Drift_isHermitian_add_smul hp
      (Xmat_isHermitian d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x))
      (Real.sqrt (gridStep t1 t0 K n))
    simp only [hFdef, hΦdef, Drift_Phi, Drift_herm_of_isHermitian hh, hfdef]
  calc ∫ x, F (gueH sz t1 t0 K n k ω) x ∂(gueUnit sz)
      = ∫ x, f (Drift_scaledSlice sz n x) ∂(gueUnit sz) := by simp only [hFf]
    _ = ∫ y, f y ∂((gueUnit sz).map (Drift_scaledSlice sz n)) :=
        (integral_map (Drift_measurable_scaledSlice n).aemeasurable
          hfcont.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(gueP d (sz.L n) (sz.W n)) := by rw [Drift_map_scaledSlice]

end LoopStepGUE

/-! ## 13. The conditional drift along the GUE-phase grid -/

/-- **The conditional drift of the loop observable along the GUE-phase grid path**, bounded by the
one-step envelope (`oneStepEnvelopeGUE`) applied pointwise at `M = gueH k ω` (Hermitian); the form
of `condExp_loop_drift` (`Path/LoopStep.lean`) with `pathP ↦ Pgue`, `pathH ↦ gueH`,
`genMat ↦ genMatGUE`.  The hypotheses `K n ≠ 0`, `k < K n` are not used by the proof. -/
theorem condExp_loop_drift_gue :
    ∀ {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ), |E| < 2 →
    ∀ {I : Loop.LoopIdx (Zd d (sz.L n))}, I.WF → 0 ≤ t1 n → t1 n ≤ t0 n → K n ≠ 0 → k < K n →
    gridTime t1 t0 K n (k + 1) < 1 →
    ∀ᵐ ω ∂(Pgue sz),
      ‖(Pgue sz)[fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (k + 1) ω'))
              (zt E (gridTime t1 t0 K n (k + 1))) I | filt sz k] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
              (zt E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * genMatGUE d (sz.L n) (sz.W n) E
              (gridTime t1 t0 K n k) (gueH sz t1 t0 K n k ω) I‖
        ≤ envConst d (sz.L n) (sz.W n) E I.length (gridTime t1 t0 K n (k + 1))
            * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
  intro d sz t1 t0 K n k E hE I hwf ht1 ht10 _hK _hk hu1
  filter_upwards [condExp_loop_step_gue sz t1 t0 K n k E hE hwf hu1] with ω hω
  rw [hω]
  have hΔ : 0 ≤ gridStep t1 t0 K n := div_nonneg (sub_nonneg.2 ht10) (Nat.cast_nonneg _)
  have hu : gridTime t1 t0 K n (k + 1) = gridTime t1 t0 K n k + gridStep t1 t0 K n := by
    unfold gridTime
    push_cast
    ring
  have hu0 : 0 ≤ gridTime t1 t0 K n k := by
    unfold gridTime
    positivity
  have key := oneStepEnvelopeGUE d (sz.L n) (sz.W n) E hE I hwf (gridTime t1 t0 K n k)
    (gridStep t1 t0 K n) hu0 hΔ (hu ▸ hu1) (gueH sz t1 t0 K n k ω)
    (gueH_isHermitian sz t1 t0 K n k ω)
  rw [← hu] at key
  exact key

/-! ## 14. Compiled nonempty instances

* `oneStepEnvelopeGUE` at `d = 3`, `L = W = 2` (`N = (W L)^3 = 64`), `E = 0`, `u = 0`, `Δ = 1/4`,
  `M = 0` (Hermitian), the one-edge loop `(+; 0)` of length `1`.
* the three grid statements at `RBM.Gauss.SizesInst.sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`,
  `N = 2097152`), the `Grid.lean` §`GridCheck` data `t₀ = 9/10`, `t₁ = (1 - ζ(1/20)) t₀`,
  `K = 4`, size index `n = 0`, step `k = 0`, `E = 0`, the two-loop `(+,-; 0, 1)` (`0 ≠ 1` in
  `Z_4^3`).  Every deterministic hypothesis is discharged: `|E| < 2`, `I.WF`, `0 ≤ t₁`,
  `t₁ ≤ t₀`, `K ≠ 0`, `k < K`, `u_1 < 1`. -/

end RBM.Univ.GUEPhase

namespace RBM.Univ.GUEPhase.DriftInst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ RBM.Gauss.SizesInst

/-- The one-edge loop `(+; 0)`. -/
private def DriftInst_loop1 (d L : ℕ) : Loop.LoopIdx (Zd d L) := ⟨[true], [0]⟩

private theorem DriftInst_loop1_wf (d L : ℕ) : (DriftInst_loop1 d L).WF := rfl

/-- `oneStepEnvelopeGUE` at `d = 3`, `L = W = 2`, `E = 0`, `u = 0`, `Δ = 1/4`, `M = 0`. -/
theorem oneStepEnvelopeGUE_check :
    ‖(∫ ω', loopL 3 2 2 (blockMat 3 2 2 ((0 : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ)
          + (Real.sqrt (1 / 4) : ℂ) • Xmat 3 2 2 ω')) (zt 0 (0 + 1 / 4))
          (DriftInst_loop1 3 2) ∂(gueP 3 2 2)) -
        loopL 3 2 2 (blockMat 3 2 2 (0 : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ)) (zt 0 0)
          (DriftInst_loop1 3 2) -
        ((1 / 4 : ℝ) : ℂ) * genMatGUE 3 2 2 0 0 (0 : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ)
          (DriftInst_loop1 3 2)‖ ≤
      envConst 3 2 2 0 (DriftInst_loop1 3 2).length (0 + 1 / 4) * (1 / 4 : ℝ) ^ ((3 : ℝ) / 2) :=
  oneStepEnvelopeGUE 3 2 2 0 (by norm_num) (DriftInst_loop1 3 2) (DriftInst_loop1_wf 3 2)
    0 (1 / 4) le_rfl (by norm_num) (by norm_num) 0 Matrix.isHermitian_zero

/-- The two-loop `(+,-; a₁, a₂)`. -/
private def DriftInst_loop2 (L : ℕ) (a₁ a₂ : Zd 3 L) : Loop.LoopIdx (Zd 3 L) :=
  ⟨[true, false], [a₁, a₂]⟩

private theorem DriftInst_loop2_wf (L : ℕ) (a₁ a₂ : Zd 3 L) : (DriftInst_loop2 L a₁ a₂).WF :=
  rfl

/-- The two labels of the instance loop differ (`0 ≠ 1` in `Z_4^3`). -/
theorem labels_sz0 : (0 : Zd 3 (sz0.L 0)) ≠ 1 := fun h => by
  have h0 := congrFun h 0
  revert h0
  decide

/-- `t₁ = (1 - ζ(1/20)) · 9/10 = e^{-1/20} · 9/10`. -/
private abbrev DriftInst_t1 : ℕ → ℝ := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)

private abbrev DriftInst_t0 : ℕ → ℝ := fun _ => 9 / 10

private abbrev DriftInst_K : ℕ → ℕ := fun _ => 4

private theorem DriftInst_t1_nonneg : 0 ≤ DriftInst_t1 0 := by
  unfold DriftInst_t1 ouZeta
  have := Real.exp_pos (-(1 / 20 : ℝ))
  nlinarith

private theorem DriftInst_t1_le_t0 : DriftInst_t1 0 ≤ DriftInst_t0 0 := by
  unfold DriftInst_t1 DriftInst_t0 ouZeta
  have : Real.exp (-(1 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  nlinarith

private theorem DriftInst_gridTime_lt : gridTime DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1) < 1 := by
  have h := DriftInst_t1_le_t0
  have h0 := DriftInst_t1_nonneg
  unfold gridTime gridStep
  simp only [DriftInst_t1, DriftInst_t0, DriftInst_K] at h h0 ⊢
  norm_num at h h0 ⊢
  linarith

/-- `gueH_succ` at `sz0`, `n = 0`, `k = 0`. -/
theorem gueH_succ_check (ω : PathΩ sz0) :
    gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1) ω
      = gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 ω
        + (Real.sqrt (gridStep DriftInst_t1 DriftInst_t0 DriftInst_K 0 / ((sz0.size 0 : ℕ) : ℝ)) : ℂ)
          • Sizes.seqXmat sz0 0 (ω (0 + 1)) :=
  gueH_succ sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 ω

/-- `condExp_loop_step_gue` at `sz0`: the conditional mean at the next grid time, given
`filt sz0 0`, is the integral over `gueP 3 4 32` of the observable at `H_0 + √Δ X`. -/
theorem condExp_loop_step_gue_check :
    (Pgue sz0)[fun ω : PathΩ sz0 =>
        loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
          (gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1) ω))
          (zt 0 (gridTime DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1)))
          (DriftInst_loop2 (sz0.L 0) 0 1) | filt sz0 0]
      =ᵐ[Pgue sz0] fun ω =>
        ∫ x, loopL 3 (sz0.L 0) (sz0.W 0)
          (blockMat 3 (sz0.L 0) (sz0.W 0)
            (gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 ω
              + (Real.sqrt (gridStep DriftInst_t1 DriftInst_t0 DriftInst_K 0) : ℂ)
                • Xmat 3 (sz0.L 0) (sz0.W 0) x))
          (zt 0 (gridTime DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1)))
          (DriftInst_loop2 (sz0.L 0) 0 1) ∂(gueP 3 (sz0.L 0) (sz0.W 0)) :=
  condExp_loop_step_gue sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 0 (by norm_num)
    (DriftInst_loop2_wf _ 0 1) DriftInst_gridTime_lt

/-- `condExp_loop_drift_gue` at `sz0`: the envelope bound at the same data. -/
theorem condExp_loop_drift_gue_check :
    ∀ᵐ ω ∂(Pgue sz0),
      ‖(Pgue sz0)[fun ω' : PathΩ sz0 =>
            loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
              (gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1) ω'))
              (zt 0 (gridTime DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1)))
              (DriftInst_loop2 (sz0.L 0) 0 1) | filt sz0 0] ω
          - loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
              (gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 ω))
              (zt 0 (gridTime DriftInst_t1 DriftInst_t0 DriftInst_K 0 0))
              (DriftInst_loop2 (sz0.L 0) 0 1)
          - (gridStep DriftInst_t1 DriftInst_t0 DriftInst_K 0 : ℂ) *
              genMatGUE 3 (sz0.L 0) (sz0.W 0) 0
                (gridTime DriftInst_t1 DriftInst_t0 DriftInst_K 0 0)
                (gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 ω)
                (DriftInst_loop2 (sz0.L 0) 0 1)‖
        ≤ envConst 3 (sz0.L 0) (sz0.W 0) 0 (DriftInst_loop2 (sz0.L 0) 0 1).length
            (gridTime DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1))
          * gridStep DriftInst_t1 DriftInst_t0 DriftInst_K 0 ^ ((3 : ℝ) / 2) :=
  condExp_loop_drift_gue sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 0 (by norm_num)
    (DriftInst_loop2_wf _ 0 1) DriftInst_t1_nonneg DriftInst_t1_le_t0 (by norm_num) (by norm_num)
    DriftInst_gridTime_lt

end RBM.Univ.GUEPhase.DriftInst

end
