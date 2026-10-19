/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.LoopCoordinate
import RBM3D.Gauss.Stein
import RBM3D.Gauss.SteinMatrix
import RBM3D.Gauss.DominationAt
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The loop-flow Stein chain

In the vocabulary of `RBM3D.Gauss.FlowCalculus` and `RBM3D.Gauss.LoopCoordinate`: `Gres` is the
resolvent of either sign, `loopL` the loop, `zt` the spectral path, `mE` the bulk value,
`Vtx d L W` the block-product index, `CoordF d L W` the coordinates, `gvarF d L W g` their
variances and `PF d L W g` the one-size law, which carries the real parameter `g` of `svarF`
(every statement about the law takes `g`).  The block reindexing of the Gaussian matrix is
`blockMat d L W (Xmat d L W ω)`.  The file has four parts: the coordinate chain, the Stein
expectation, the envelope, and the expected derivative.

Dimension-dependent statements: the bound of one block insertion `W^{-d}` (in
`spectralWordBound`, `driftA`, `driftD`), the trace constant `(L W)^d` (in
`flowDerivativeEnvelope`), and the index types.  Everything else is dimension-free.

For a fixed sample `ω` and the flow `H_v = √v X`, `z_v = E + (1-v) m(E)`: the samplewise derivative
`∂_v 𝓛_v` splits into `(1/(2u)) Σ_c ω_c ∂_c 𝓛` (coordinate chain rule) plus a spectral drift;
the envelope `flowDerivativeEnvelope` dominates it on `[u/2, (1+u)/2]` and is integrable; Stein's
identity turns `E[ω_c ∂_c 𝓛]` into `gvarF_c E[∂_c² 𝓛]`; and `d/du E 𝓛_u` is the resulting
expression.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset Filter
open scoped Matrix.Norms.L2Operator Topology

variable (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)

/-! ## 1. The matrix-flow term as a finite sum of coordinate derivatives -/

private abbrev BlockMat (d L W : ℕ) :=
  Matrix (Vtx d L W) (Vtx d L W) ℂ

/-- Linear dependence of one signed resolvent derivative on its matrix direction. -/
noncomputable def gsigDirectionMap (u : ℝ) (ω : Ω d L W) (z : ℂ) (σ : Bool) :
    BlockMat d L W →ₗ[ℝ] BlockMat d L W :=
  let G := Gres (HflowBlock d L W u ω) z σ
  (-(ContinuousLinearMap.mulLeftRight ℝ (BlockMat d L W) G G)).toLinearMap

/-- The direction map of one signed resolvent is `B ↦ -(G B G)`. -/
@[simp] theorem gsigDirectionMap_apply (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (σ : Bool) (B : BlockMat d L W) :
    gsigDirectionMap d L W u ω z σ B =
      -(Gres (HflowBlock d L W u ω) z σ * B *
        Gres (HflowBlock d L W u ω) z σ) := by
  simp [gsigDirectionMap, ContinuousLinearMap.mulLeftRight_apply]

/-- The finite-word directional derivative as a real-linear map of the matrix direction. -/
noncomputable def wordDirectionMap (u : ℝ) (ω : Ω d L W) (z : ℂ) :
    (l : List (Bool × Zd d L)) → BlockMat d L W →ₗ[ℝ] BlockMat d L W
  | [] => 0
  | p :: l =>
      let G := Gres (HflowBlock d L W u ω) z p.1
      let E := Eblk d L W p.2
      let tail := l.foldr (fun q M =>
        Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1
      { toFun := fun B =>
          (gsigDirectionMap d L W u ω z p.1 B * E) * tail +
            (G * E) * wordDirectionMap u ω z l B
        map_add' := by
          intro B C
          simp only [map_add, mul_add, add_mul]
          noncomm_ring
        map_smul' := by
          intro r B
          simp only [map_smul, RingHom.id_apply, mul_smul_comm, smul_mul_assoc,
            smul_add] }

/-- The direction map of the empty word is `0`. -/
@[simp] theorem wordDirectionMap_nil (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (B : BlockMat d L W) :
    wordDirectionMap d L W u ω z [] B = 0 := rfl

/-- The Leibniz recursion for the direction map of a word `p :: l`. -/
@[simp] theorem wordDirectionMap_cons (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) (B : BlockMat d L W) :
    wordDirectionMap d L W u ω z (p :: l) B =
      (gsigDirectionMap d L W u ω z p.1 B * Eblk d L W p.2) *
        l.foldr (fun q M => Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1 +
      (Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2) *
        wordDirectionMap d L W u ω z l B := rfl

/-- Reindexing the finite coordinate expansion of the Gaussian matrix (through `blockMat`). -/
theorem Xblock_eq_sum_coordinates (ω : Ω d L W) :
    blockMat d L W (Xmat d L W ω) =
      ∑ c : CoordF d L W, (ω c) • coordinateBlock d L W c := by
  rw [Xmat_eq_sum_coordinates]
  ext i j
  simp [coordinateBlock, blockMat, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply]

/-- The directional map at one Gaussian coordinate equals its established derivative. -/
theorem wordDirectionMap_coordinate (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) (z : ℂ) (l : List (Bool × Zd d L)) :
    wordDirectionMap d L W u ω z l (Real.sqrt u • coordinateBlock d L W c) =
      coordinateWordDeriv d L W u ω c z l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [wordDirectionMap_cons, coordinateWordDeriv, ih,
        gsigDirectionMap_apply, gsigCoordinateDeriv]

/-- The matrix-flow direction is the weighted sum of coordinate directions. -/
theorem time_direction_eq_coordinate_sum (ω : Ω d L W) {u : ℝ} (hu : 0 < u) :
    (1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω) =
      (1 / (2 * u)) • ∑ c : CoordF d L W,
        (ω c) • (Real.sqrt u • coordinateBlock d L W c) := by
  have hsqrt : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
  have hscalar : (1 / (2 * u)) * Real.sqrt u = 1 / (2 * Real.sqrt u) := by
    field_simp
    nlinarith [Real.sq_sqrt hu.le]
  rw [Xblock_eq_sum_coordinates d L W ω]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  rw [← hscalar]
  ring

/-- Matrix-flow contribution to a finite word equals its weighted coordinate sum. -/
theorem wordDirectionMap_time_eq_coordinate_sum (ω : Ω d L W) {u : ℝ}
    (hu : 0 < u) (z : ℂ) (l : List (Bool × Zd d L)) :
    wordDirectionMap d L W u ω z l
        ((1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω)) =
      (1 / (2 * u)) • ∑ c : CoordF d L W,
        (ω c) • coordinateWordDeriv d L W u ω c z l := by
  rw [time_direction_eq_coordinate_sum d L W ω hu]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [← map_smul, wordDirectionMap_coordinate]

/-- The spectral part of a signed Green derivative, kept separate from matrix motion. -/
noncomputable def gsigSpectralFlowDeriv (ω : Ω d L W) (E u : ℝ) (σ : Bool) :
    BlockMat d L W :=
  let G := Gres (HflowBlock d L W u ω) (zt E u) σ;
  -(G * (spectralMSign E σ • (1 : BlockMat d L W)) * G)

/-- The flow derivative of one factor splits into matrix and spectral terms. -/
theorem gsigFlowDeriv_split (ω : Ω d L W) (E u : ℝ) (σ : Bool) :
    gsigFlowDeriv d L W ω E u σ =
      gsigDirectionMap d L W u ω (zt E u) σ
        ((1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω)) +
      gsigSpectralFlowDeriv d L W ω E u σ := by
  simp only [gsigFlowDeriv, gsigDirectionMap_apply, gsigSpectralFlowDeriv]
  noncomm_ring

/-- Recursive spectral drift of a finite signed word. -/
noncomputable def spectralWordDeriv (ω : Ω d L W) (E u : ℝ) :
    List (Bool × Zd d L) → BlockMat d L W
  | [] => 0
  | p :: l =>
      (gsigSpectralFlowDeriv d L W ω E u p.1 * Eblk d L W p.2) *
        l.foldr (fun q M => Gres (HflowBlock d L W u ω) (zt E u) q.1 *
          Eblk d L W q.2 * M) 1 +
      (Gres (HflowBlock d L W u ω) (zt E u) p.1 * Eblk d L W p.2) *
        spectralWordDeriv ω E u l

/-- The established fixed-sample word derivative splits into matrix and spectral parts. -/
theorem loopWordDeriv_split (ω : Ω d L W) (E u : ℝ)
    (l : List (Bool × Zd d L)) :
    loopWordDeriv d L W ω E u l =
      wordDirectionMap d L W u ω (zt E u) l
        ((1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω)) +
      spectralWordDeriv d L W ω E u l := by
  induction l with
  | nil => simp [loopWordDeriv, spectralWordDeriv]
  | cons p l ih =>
      simp only [loopWordDeriv, wordDirectionMap_cons, spectralWordDeriv,
        gsigFlowDeriv_split, ih]
      noncomm_ring

/-- The matrix-flow part of the loop derivative is the coordinate-weighted sum. -/
theorem trace_wordDirectionMap_time_eq_coordinate_sum (ω : Ω d L W)
    {u : ℝ} (hu : 0 < u) (z : ℂ) (I : Loop.LoopIdx (Zd d L)) :
    Matrix.trace (wordDirectionMap d L W u ω z (I.σ.zip I.a)
      ((1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω))) =
      (1 / (2 * u)) • ∑ c : CoordF d L W,
        (ω c) • Matrix.trace
          (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a)) := by
  rw [wordDirectionMap_time_eq_coordinate_sum d L W ω hu]
  simp only [Matrix.trace_smul, Matrix.trace_sum]

/-- The full fixed-sample loop derivative, with its spectral drift displayed separately. -/
theorem loop_flow_derivative_coordinate_chain (ω : Ω d L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    deriv (fun v : ℝ =>
      loopL d L W (HflowBlock d L W v ω) (zt E v) I) u =
      (1 / (2 * u)) • ∑ c : CoordF d L W,
        (ω c) • Matrix.trace
          (coordinateWordDeriv d L W u ω c (zt E u) (I.σ.zip I.a)) +
      Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a)) := by
  rw [(hasDerivAt_gloop_HflowBlock_spectralZ d L W ω hE hu hu1 I hwf).deriv]
  rw [loopWordDeriv_split, Matrix.trace_add]
  rw [trace_wordDirectionMap_time_eq_coordinate_sum d L W ω hu]

/-! ## 2. The expected samplewise derivative: Stein on the coordinate sum

The matrix-flow term is replaced using finite-coordinate Gaussian Stein; the left side is an
expectation of a samplewise derivative, not a derivative of expectation. -/

omit [NeZero W] in
/-- `η⁻¹ W^{-d}`, the bound of one `G E` block. -/
private noncomputable def driftA (η : ℝ) : ℝ :=
  η⁻¹ * ((W : ℝ) ^ d)⁻¹

omit [NeZero W] in
/-- `η⁻¹ ‖m^(E)‖ η⁻¹ W^{-d}`, the bound of one drift factor `G m^(E) G E`. -/
private noncomputable def driftD (E η : ℝ) : ℝ :=
  (η⁻¹ * ‖mE E‖ * η⁻¹) * ((W : ℝ) ^ d)⁻¹

omit [NeZero W] in
/-- A deterministic recursive bound for the spectral drift of a word (each block insertion costs
`W^{-d}`). -/
noncomputable def spectralWordBound (E η : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => driftD d W E η * (driftA d W η) ^ n +
      driftA d W η * spectralWordBound E η n

omit [NeZero W] in
private theorem driftA_nonneg {η : ℝ} (hη : 0 < η) :
    0 ≤ driftA d W η := by unfold driftA; positivity

omit [NeZero W] in
private theorem driftD_nonneg {E η : ℝ} (hη : 0 < η) :
    0 ≤ driftD d W E η := by unfold driftD; positivity

/-- The spectral drift of one signed factor is continuous in the sample. -/
theorem continuous_gsigSpectralFlowDeriv_sample (E u : ℝ)
    (hE : |E| < 2) (hu1 : u < 1) (σ : Bool) :
    Continuous fun ω : Ω d L W => gsigSpectralFlowDeriv d L W ω E u σ := by
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hG := continuous_Gsig_HflowBlock_sample d L W u hz σ
  change Continuous fun ω : Ω d L W =>
    -(Gres (HflowBlock d L W u ω) (zt E u) σ *
      (spectralMSign E σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
      Gres (HflowBlock d L W u ω) (zt E u) σ)
  exact ((hG.mul continuous_const).mul hG).neg

/-- The finite spectral drift word is continuous in the sample. -/
theorem continuous_spectralWordDeriv_sample (E u : ℝ)
    (hE : |E| < 2) (hu1 : u < 1) (l : List (Bool × Zd d L)) :
    Continuous fun ω : Ω d L W => spectralWordDeriv d L W ω E u l := by
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact (((continuous_gsigSpectralFlowDeriv_sample d L W E u hE hu1 p.1).mul
        continuous_const).mul (continuous_foldr_HflowBlock_sample d L W u hz l)).add
        (((continuous_Gsig_HflowBlock_sample d L W u hz p.1).mul
          continuous_const).mul ih)

private theorem norm_spectral_head_le {E u η : ℝ} (hη : 0 < η)
    (ω : Ω d L W) (hz : η ≤ |(zt E u).im|)
    (p : Bool × Zd d L) :
    ‖gsigSpectralFlowDeriv d L W ω E u p.1 * Eblk d L W p.2‖ ≤
      driftD d W E η := by
  let G := Gres (HflowBlock d L W u ω) (zt E u) p.1
  let M : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    spectralMSign E p.1 • 1
  let B := Eblk d L W p.2
  have hG : ‖G‖ ≤ η⁻¹ :=
    norm_Gsig_le_inv_eta (HflowBlock_isHermitian d L W u ω) hη hz p.1
  have hM : ‖M‖ = ‖mE E‖ := by
    have hm : ‖spectralMSign E p.1‖ = ‖mE E‖ := by
      cases p.1 <;> simp [spectralMSign]
    simp [M, norm_smul, hm]
  have hB : ‖B‖ ≤ ((W : ℝ) ^ d)⁻¹ := norm_Eblk_le_inv_W_sq d L W p.2
  change ‖-(G * M * G) * B‖ ≤ driftD d W E η
  calc
    ‖-(G * M * G) * B‖ ≤ ‖-(G * M * G)‖ * ‖B‖ := norm_mul_le _ _
    _ = ‖G * M * G‖ * ‖B‖ := by rw [norm_neg]
    _ ≤ (‖G‖ * ‖M‖ * ‖G‖) * ‖B‖ := by
      have h3 : ‖G * M * G‖ ≤ ‖G‖ * ‖M‖ * ‖G‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ ≤ (η⁻¹ * ‖M‖ * η⁻¹) * ‖B‖ := by
      have hq : 0 ≤ η⁻¹ := by positivity
      have hgm : ‖G‖ * ‖M‖ ≤ η⁻¹ * ‖M‖ :=
        mul_le_mul_of_nonneg_right hG (norm_nonneg M)
      have hggm : ‖G‖ * ‖M‖ * ‖G‖ ≤ η⁻¹ * ‖M‖ * η⁻¹ :=
        mul_le_mul hgm hG (norm_nonneg G) (mul_nonneg hq (norm_nonneg M))
      exact mul_le_mul_of_nonneg_right hggm (norm_nonneg B)
    _ ≤ (η⁻¹ * ‖M‖ * η⁻¹) * ((W : ℝ) ^ d)⁻¹ := by
      have hq : 0 ≤ η⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left hB
        (mul_nonneg (mul_nonneg hq (norm_nonneg M)) hq)
    _ = (η⁻¹ * ‖mE E‖ * η⁻¹) * ((W : ℝ) ^ d)⁻¹ := by rw [hM]
    _ = driftD d W E η := rfl

/-- Deterministic sample-uniform bound for the finite spectral drift word. -/
theorem norm_spectralWordDeriv_le {E u η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(zt E u).im|) (l : List (Bool × Zd d L))
    (ω : Ω d L W) :
    ‖spectralWordDeriv d L W ω E u l‖ ≤ spectralWordBound d W E η l.length := by
  induction l with
  | nil => simp [spectralWordDeriv, spectralWordBound]
  | cons p l ih =>
      have hD := norm_spectral_head_le d L W hη ω hz p
      have hA := norm_Gsig_le_inv_eta
        (HflowBlock_isHermitian d L W u ω) hη hz p.1
      have hE := norm_Eblk_le_inv_W_sq d L W p.2
      have htail := norm_foldr_Gsig_Eblk_le d L W
        (HflowBlock_isHermitian d L W u ω) hη hz l
      have htail' :
          ‖l.foldr (fun q M => Gres (HflowBlock d L W u ω) (zt E u) q.1 *
              Eblk d L W q.2 * M) 1‖ ≤ driftA d W η ^ l.length := by
        simpa only [driftA] using htail
      have hhead :
          ‖Gres (HflowBlock d L W u ω) (zt E u) p.1 * Eblk d L W p.2‖ ≤
            driftA d W η := by
        calc
          _ ≤ ‖Gres (HflowBlock d L W u ω) (zt E u) p.1‖ *
              ‖Eblk d L W p.2‖ := norm_mul_le _ _
          _ ≤ _ := by
            unfold driftA
            gcongr
      have hD0 : 0 ≤ driftD d W E η := driftD_nonneg d W hη
      have hA0 : 0 ≤ driftA d W η := driftA_nonneg d W hη
      rw [spectralWordDeriv, List.length_cons, spectralWordBound]
      calc
        ‖_ + _‖ ≤
            ‖gsigSpectralFlowDeriv d L W ω E u p.1 * Eblk d L W p.2 *
              l.foldr (fun q M => Gres (HflowBlock d L W u ω) (zt E u) q.1 *
                Eblk d L W q.2 * M) 1‖ +
            ‖(Gres (HflowBlock d L W u ω) (zt E u) p.1 * Eblk d L W p.2) *
              spectralWordDeriv d L W ω E u l‖ := norm_add_le _ _
        _ ≤ ‖gsigSpectralFlowDeriv d L W ω E u p.1 * Eblk d L W p.2‖ *
              ‖l.foldr (fun q M => Gres (HflowBlock d L W u ω) (zt E u) q.1 *
                Eblk d L W q.2 * M) 1‖ +
            ‖Gres (HflowBlock d L W u ω) (zt E u) p.1 * Eblk d L W p.2‖ *
              ‖spectralWordDeriv d L W ω E u l‖ :=
                add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ driftD d W E η * driftA d W η ^ l.length +
              driftA d W η * spectralWordBound d W E η l.length := by gcongr

/-- The traced spectral drift is integrable under the Gaussian product law `PF d L W g`.
`g` is an extra argument (the one-size law carries the parameter `g`). -/
theorem integrable_trace_spectralWordDeriv (E u : ℝ) (hE : |E| < 2)
    (hu1 : u < 1) (l : List (Bool × Zd d L)) :
    Integrable (fun ω : Ω d L W => Matrix.trace (spectralWordDeriv d L W ω E u l))
      (PF d L W g) := by
  have hη : 0 < |(zt E u).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (by linarith) (spectralM_im_pos hE))]
    exact mul_pos (by linarith) (spectralM_im_pos hE)
  have hm := ((continuous_matrixTrace d L W).comp
    (continuous_spectralWordDeriv_sample d L W E u hE hu1 l)).measurable
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((Fintype.card (Vtx d L W) : ℝ) *
      spectralWordBound d W E |(zt E u).im| l.length)
  exact Filter.Eventually.of_forall fun ω => by
    calc
      ‖Matrix.trace (spectralWordDeriv d L W ω E u l)‖ ≤
          (Fintype.card (Vtx d L W) : ℝ) *
            ‖spectralWordDeriv d L W ω E u l‖ := norm_matrix_trace_le_card_mul _
      _ ≤ (Fintype.card (Vtx d L W) : ℝ) *
          spectralWordBound d W E |(zt E u).im| l.length := by
            exact mul_le_mul_of_nonneg_left
              (norm_spectralWordDeriv_le d L W hη le_rfl l ω) (Nat.cast_nonneg _)

omit [NeZero L] in
-- A Gaussian coordinate times a bounded measurable complex observable is integrable.
private theorem integrable_coord_smul_of_bounded (c : CoordF d L W)
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

/-- Stein applied to the first coordinate derivative yields the second derivative.
`GaussianProduct.stein` is applied to the law `law (gvarF d L W g) = PF d L W g` (`rfl`). -/
theorem stein_gloop_first_coordinate_derivative (u : ℝ) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    ∫ ω : Ω d L W, ω c • Matrix.trace
        (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a)) ∂(PF d L W g) =
      (gvarF d L W g c : ℝ) • ∫ ω : Ω d L W, Matrix.trace
        (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a)) ∂(PF d L W g) := by
  let f : Ω d L W → ℂ := fun ω =>
    Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))
  let f' : Ω d L W → ℂ := fun ω =>
    Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))
  have hfc : Continuous f := (continuous_matrixTrace d L W).comp
    (continuous_coordinateWordDeriv_sample d L W u c hz _)
  have hf'c : Continuous f' := (continuous_matrixTrace d L W).comp
    (continuous_coordinateSecondWordDeriv_sample d L W u c hz _)
  have hderiv : ∀ ω : Ω d L W,
      HasDerivAt (fun t : ℝ => f (Function.update ω c t)) (f' ω) (ω c) := by
    intro ω
    set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
    have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
    have h := T.hasFDerivAt.comp_hasDerivAt (ω c)
      (hasDerivAt_coordinateWordDeriv d L W u ω c hz (I.σ.zip I.a))
    simpa only [f, f', hT, Function.comp_def] using h
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hfb : ∃ C : ℝ, ∀ ω : Ω d L W, ‖f ω‖ ≤ C := by
    refine ⟨(((L * W) ^ d : ℕ) : ℝ) *
      coordinateFirstWordBound d L W u |z.im| c I.a.length, ?_⟩
    intro ω
    exact (norm_gloop_coordinate_derivatives_le d L W hη c le_rfl I hwf ω).1
  have hf'b : ∃ C : ℝ, ∀ ω : Ω d L W, ‖f' ω‖ ≤ C := by
    refine ⟨(((L * W) ^ d : ℕ) : ℝ) *
      coordinateSecondWordBound d L W u |z.im| c I.a.length, ?_⟩
    intro ω
    exact (norm_gloop_coordinate_derivatives_le d L W hη c le_rfl I hwf ω).2
  have h := GaussianProduct.stein (gvarF d L W g) c f f' hfc hf'c hderiv hfb hf'b
  have hlaw : PF d L W g = GaussianProduct.law (gvarF d L W g) := rfl
  rw [hlaw]
  exact h

/-- Finite sum of the second-level Stein identities. -/
theorem stein_gloop_first_coordinate_derivative_sum (u : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    ∫ ω : Ω d L W, ∑ c : CoordF d L W, ω c • Matrix.trace
        (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a)) ∂(PF d L W g) =
    ∫ ω : Ω d L W, ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) • Matrix.trace
        (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))
          ∂(PF d L W g) := by
  classical
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hleft (c : CoordF d L W) : Integrable (fun ω : Ω d L W =>
      ω c • Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a)))
      (PF d L W g) := by
    have hgb (ω : Ω d L W) :
        ‖Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))‖ ≤
          (((L * W) ^ d : ℕ) : ℝ) *
            coordinateFirstWordBound d L W u |z.im| c I.a.length :=
      (norm_gloop_coordinate_derivatives_le d L W hη c le_rfl I hwf ω).1
    exact integrable_coord_smul_of_bounded d L W g c _
      ((continuous_matrixTrace d L W).comp
        (continuous_coordinateWordDeriv_sample d L W u c hz _)).measurable hgb
  have hright (c : CoordF d L W) : Integrable (fun ω : Ω d L W =>
      (gvarF d L W g c : ℝ) • Matrix.trace
        (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))) (PF d L W g) := by
    exact ((integrable_gloop_coordinate_derivatives d L W g u c hz I hwf).2).smul
      (gvarF d L W g c : ℝ)
  calc
    ∫ ω : Ω d L W, ∑ c : CoordF d L W, ω c • Matrix.trace
        (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a)) ∂(PF d L W g) =
      ∑ c : CoordF d L W, ∫ ω : Ω d L W, ω c • Matrix.trace
        (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a)) ∂(PF d L W g) := by
          exact integral_finsetSum univ (fun c _ => hleft c)
    _ = ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) • ∫ ω : Ω d L W,
        Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))
          ∂(PF d L W g) := by
          apply sum_congr rfl
          intro c _
          exact stein_gloop_first_coordinate_derivative d L W g u c hz I hwf
    _ = ∑ c : CoordF d L W, ∫ ω : Ω d L W, (gvarF d L W g c : ℝ) • Matrix.trace
        (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))
          ∂(PF d L W g) := by simp only [integral_smul]
    _ = ∫ ω : Ω d L W, ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) • Matrix.trace
        (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))
          ∂(PF d L W g) := by
          exact (integral_finsetSum univ (fun c _ => hright c)).symm

/-- **The Stein expectation of the samplewise loop-flow derivative**: after second-level Stein the
spectral drift remains.
`g` is an extra argument (the one-size law carries the parameter `g`). -/
theorem expected_samplewise_loop_flow_derivative
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    Integrable (fun ω : Ω d L W => deriv (fun v : ℝ =>
      loopL d L W (HflowBlock d L W v ω) (zt E v) I) u) (PF d L W g) ∧
    (∫ ω : Ω d L W, deriv (fun v : ℝ =>
      loopL d L W (HflowBlock d L W v ω) (zt E v) I) u ∂(PF d L W g)) =
      (1 / (2 * u)) • ∫ ω : Ω d L W,
        ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv d L W u ω c
            (zt E u) (I.σ.zip I.a)) ∂(PF d L W g) +
      ∫ ω : Ω d L W,
        Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))
          ∂(PF d L W g) := by
  classical
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hleft : Integrable (fun ω : Ω d L W =>
      ∑ c : CoordF d L W, ω c • Matrix.trace
        (coordinateWordDeriv d L W u ω c (zt E u) (I.σ.zip I.a)))
      (PF d L W g) := by
    have hη : 0 < |(zt E u).im| := abs_pos.mpr hz
    apply integrable_finsetSum univ
    intro c _
    have hgb (ω : Ω d L W) :
        ‖Matrix.trace (coordinateWordDeriv d L W u ω c (zt E u)
            (I.σ.zip I.a))‖ ≤
          (((L * W) ^ d : ℕ) : ℝ) *
            coordinateFirstWordBound d L W u |(zt E u).im| c I.a.length :=
      (norm_gloop_coordinate_derivatives_le d L W hη c le_rfl I hwf ω).1
    exact integrable_coord_smul_of_bounded d L W g c _
      ((continuous_matrixTrace d L W).comp
        (continuous_coordinateWordDeriv_sample d L W u c hz _)).measurable hgb
  have hspec : Integrable (fun ω : Ω d L W =>
      Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))) (PF d L W g) :=
    integrable_trace_spectralWordDeriv d L W g E u hE hu1 (I.σ.zip I.a)
  have hfun : (fun ω : Ω d L W => deriv (fun v : ℝ =>
      loopL d L W (HflowBlock d L W v ω) (zt E v) I) u) =
      (fun ω : Ω d L W => (1 / (2 * u)) •
        (∑ c : CoordF d L W, ω c • Matrix.trace
          (coordinateWordDeriv d L W u ω c (zt E u) (I.σ.zip I.a))) +
        Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))) := by
    funext ω
    exact loop_flow_derivative_coordinate_chain d L W ω hE hu hu1 I hwf
  have hscaled : Integrable (fun ω : Ω d L W => (1 / (2 * u)) •
      (∑ c : CoordF d L W, ω c • Matrix.trace
        (coordinateWordDeriv d L W u ω c (zt E u) (I.σ.zip I.a))))
      (PF d L W g) := by
    exact hleft.smul (1 / (2 * u))
  constructor
  · rw [hfun]
    exact hscaled.add hspec
  · rw [hfun, integral_add hscaled hspec, integral_smul]
    rw [stein_gloop_first_coordinate_derivative_sum d L W g u hz I hwf]

/-! ## 3. An integrable time-neighbourhood envelope for samplewise loop derivatives

For fixed `0 < u < 1`, the interval `[u/2, (1+u)/2]` contains `u` in its interior and stays
inside `(0,1)`.  The derivative bound is a constant plus a finite weighted sum of absolute
Gaussian coordinates. -/

/-- The closed neighborhood of a positive time before the singular endpoint. -/
def flowWindow (u : ℝ) : Set ℝ := Set.Icc (u / 2) ((1 + u) / 2)

/-- The time `u` is an interior point of `flowWindow u`: `u/2 < u < (1 + u)/2`. -/
theorem flowWindow_strict (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    u / 2 < u ∧ u < (1 + u) / 2 := by
  constructor <;> linarith

/-- The window `flowWindow u` stays inside `(0, 1)`. -/
theorem flowWindow_subset_Ioo (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    {v : ℝ} (hv : v ∈ flowWindow u) : v ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [flowWindow, Set.mem_Icc] at hv
  exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- The first-coordinate word bound grows with `√v` on `[0,1]`. -/
theorem coordinateFirstWordBound_le_one (c : CoordF d L W) {v η : ℝ}
    (hv1 : v ≤ 1) (hη : 0 < η) (n : ℕ) :
    coordinateFirstWordBound d L W v η c n ≤
      coordinateFirstWordBound d L W 1 η c n := by
  have hsqrt : Real.sqrt v ≤ 1 := by
    have h := Real.sqrt_le_sqrt hv1
    simpa using h
  have hB : ‖Real.sqrt v • coordinateBlock d L W c‖ ≤
      ‖Real.sqrt (1 : ℝ) • coordinateBlock d L W c‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_one, abs_one]
    exact mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coordinateFirstWordBound]
      have hA : 0 ≤ η⁻¹ * ((W : ℝ) ^ d)⁻¹ := by positivity
      have hD :
          (η⁻¹ * ‖Real.sqrt v • coordinateBlock d L W c‖ * η⁻¹) *
              ((W : ℝ) ^ d)⁻¹ ≤
          (η⁻¹ * ‖Real.sqrt (1 : ℝ) • coordinateBlock d L W c‖ * η⁻¹) *
              ((W : ℝ) ^ d)⁻¹ := by
        gcongr
      change _ ≤ _
      gcongr
      exact hD

/-- A fixed integrable majorant: one constant plus finitely many absolute coordinates; the trace
constant is `(L W)^d`. -/
noncomputable def flowDerivativeEnvelope (E u : ℝ) (I : Loop.LoopIdx (Zd d L))
    (ω : Ω d L W) : ℝ :=
  let η := (1 - (1 + u) / 2) * (mE E).im
  (1 / u) * ∑ c : CoordF d L W,
    ((((L * W) ^ d : ℕ) : ℝ) *
      coordinateFirstWordBound d L W 1 η c I.a.length) * |ω c| +
    (((L * W) ^ d : ℕ) : ℝ) * spectralWordBound d W E η I.a.length

/-- The majorant is integrable by the first absolute moments of the coordinates.
`g` is an extra argument (the one-size law carries the parameter `g`). -/
theorem integrable_flowDerivativeEnvelope (E u : ℝ)
    (I : Loop.LoopIdx (Zd d L)) :
    Integrable (flowDerivativeEnvelope d L W E u I) (PF d L W g) := by
  let η := (1 - (1 + u) / 2) * (mE E).im
  have hcoord (c : CoordF d L W) :
      Integrable (fun ω : Ω d L W => ω c) (PF d L W g) := by
    have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) :=
      (measurable_pi_apply c).aemeasurable
    have hg : Integrable (fun x : ℝ => x) ((PF d L W g).map fun ω => ω c) := by
      rw [P_map_eval]
      exact RBM.integrable_id_gaussianReal (var := gvarF d L W g c)
    exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg
  change Integrable (fun ω : Ω d L W =>
    (1 / u) * ∑ c : CoordF d L W,
      ((((L * W) ^ d : ℕ) : ℝ) *
        coordinateFirstWordBound d L W 1 η c I.a.length) * |ω c| +
      (((L * W) ^ d : ℕ) : ℝ) * spectralWordBound d W E η I.a.length)
    (PF d L W g)
  apply Integrable.add
  · apply Integrable.const_mul
    apply integrable_finsetSum univ
    intro c _
    exact (hcoord c).abs.const_mul _
  · exact integrable_const _

/-- **The envelope bound**: the explicit majorant bounds the actual samplewise time derivative
throughout the closed neighborhood `[u/2,(1+u)/2]`. -/
theorem norm_samplewise_loop_flow_derivative_le_envelope
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF)
    {v : ℝ} (hv : v ∈ flowWindow u) (ω : Ω d L W) :
    ‖deriv (fun t : ℝ =>
      loopL d L W (HflowBlock d L W t ω) (zt E t) I) v‖ ≤
      flowDerivativeEnvelope d L W E u I ω := by
  let η := (1 - (1 + u) / 2) * (mE E).im
  have hv' : v ∈ Set.Icc (u / 2) ((1 + u) / 2) := hv
  have hmid : v ∈ Set.Ioo (0 : ℝ) 1 :=
    flowWindow_subset_Ioo u hu hu1 hv
  have ht : (1 + u) / 2 < (1 : ℝ) := by linarith
  have hη : 0 < η := mul_pos (by linarith)
    (spectralM_im_pos hE)
  have hgap : η ≤ |(zt E v).im| :=
    spectralZ_im_gap hE ht hv'
  have hcoef : |1 / (2 * v)| ≤ 1 / u := by
    have hvpos : 0 < 2 * v := by linarith [hmid.1]
    have hcoef' : 1 / (2 * v) ≤ 1 / u := by
      apply (div_le_div_iff₀ hvpos hu).2
      linarith [hv'.1]
    have hcoefpos : 0 < (1 : ℝ) / (2 * v) :=
      div_pos (by norm_num) hvpos
    rwa [abs_of_pos hcoefpos]
  have hD (c : CoordF d L W) :
      ‖Matrix.trace (coordinateWordDeriv d L W v ω c (zt E v)
        (I.σ.zip I.a))‖ ≤
        ((((L * W) ^ d : ℕ) : ℝ) *
          coordinateFirstWordBound d L W 1 η c I.a.length) := by
    have hb := (norm_gloop_coordinate_derivatives_le d L W
      (u := v) hη c hgap I hwf ω).1
    exact hb.trans (mul_le_mul_of_nonneg_left
      (coordinateFirstWordBound_le_one d L W c hmid.2.le hη I.a.length)
      (Nat.cast_nonneg _))
  have hsum :
      ‖∑ c : CoordF d L W, (ω c) • Matrix.trace
          (coordinateWordDeriv d L W v ω c (zt E v) (I.σ.zip I.a))‖ ≤
        ∑ c : CoordF d L W,
          ((((L * W) ^ d : ℕ) : ℝ) *
            coordinateFirstWordBound d L W 1 η c I.a.length) * |ω c| := by
    calc
      ‖∑ c : CoordF d L W, (ω c) • Matrix.trace
          (coordinateWordDeriv d L W v ω c (zt E v) (I.σ.zip I.a))‖ ≤
        ∑ c : CoordF d L W, ‖(ω c) • Matrix.trace
          (coordinateWordDeriv d L W v ω c (zt E v) (I.σ.zip I.a))‖ :=
            norm_sum_le _ _
      _ ≤ ∑ c : CoordF d L W,
          ((((L * W) ^ d : ℕ) : ℝ) *
            coordinateFirstWordBound d L W 1 η c I.a.length) * |ω c| := by
        apply sum_le_sum
        intro c _
        rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hD c) (abs_nonneg _)
  have hspec :
      ‖Matrix.trace (spectralWordDeriv d L W ω E v (I.σ.zip I.a))‖ ≤
        (((L * W) ^ d : ℕ) : ℝ) * spectralWordBound d W E η I.a.length := by
    have hb := norm_spectralWordDeriv_le d L W hη hgap (I.σ.zip I.a) ω
    have hlen : (I.σ.zip I.a).length = I.a.length := by
      rw [List.length_zip]
      simp only [Loop.LoopIdx.WF] at hwf
      rw [hwf, min_self]
    calc
      _ ≤ (Fintype.card (Vtx d L W) : ℝ) *
          ‖spectralWordDeriv d L W ω E v (I.σ.zip I.a)‖ :=
            norm_matrix_trace_le_card_mul _
      _ ≤ (Fintype.card (Vtx d L W) : ℝ) *
          spectralWordBound d W E η (I.σ.zip I.a).length := by
            exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = _ := by rw [card_BlockIndex, hlen]
  rw [(hasDerivAt_gloop_HflowBlock_spectralZ d L W ω hE hmid.1 hmid.2 I hwf).deriv]
  rw [loopWordDeriv_split, Matrix.trace_add]
  rw [trace_wordDirectionMap_time_eq_coordinate_sum d L W ω hmid.1]
  change ‖(1 / (2 * v)) • (∑ c : CoordF d L W, (ω c) • Matrix.trace
      (coordinateWordDeriv d L W v ω c (zt E v) (I.σ.zip I.a))) +
      Matrix.trace (spectralWordDeriv d L W ω E v (I.σ.zip I.a))‖ ≤
    (1 / u) * ∑ c : CoordF d L W,
      ((((L * W) ^ d : ℕ) : ℝ) *
        coordinateFirstWordBound d L W 1 η c I.a.length) * |ω c| +
      (((L * W) ^ d : ℕ) : ℝ) * spectralWordBound d W E η I.a.length
  calc
    ‖_ + _‖ ≤ ‖(1 / (2 * v)) • (∑ c : CoordF d L W, (ω c) • Matrix.trace
        (coordinateWordDeriv d L W v ω c (zt E v) (I.σ.zip I.a)))‖ +
      ‖Matrix.trace (spectralWordDeriv d L W ω E v (I.σ.zip I.a))‖ :=
        norm_add_le _ _
    _ = |1 / (2 * v)| * ‖∑ c : CoordF d L W, (ω c) • Matrix.trace
        (coordinateWordDeriv d L W v ω c (zt E v) (I.σ.zip I.a))‖ +
      ‖Matrix.trace (spectralWordDeriv d L W ω E v (I.σ.zip I.a))‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (1 / u) * ∑ c : CoordF d L W,
        ((((L * W) ^ d : ℕ) : ℝ) *
          coordinateFirstWordBound d L W 1 η c I.a.length) * |ω c| +
        (((L * W) ^ d : ℕ) : ℝ) * spectralWordBound d W E η I.a.length := by
      apply add_le_add _ hspec
      exact mul_le_mul hcoef hsum (norm_nonneg _) (by positivity)

/-! ## 4. Differentiating an expected finite Gaussian resolvent loop

The explicit integrable envelope on a closed neighborhood permits differentiation under the
product Gaussian integral; the finite coordinate Stein identity then gives the exact
second-coordinate and spectral terms. -/

/-- The expected finite loop has the expected samplewise derivative at an interior time.
`g` is an extra argument (the one-size law carries the parameter `g`). -/
theorem hasDerivAt_integral_gloop_HflowBlock_spectralZ
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    HasDerivAt (fun v : ℝ => ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W v ω) (zt E v) I ∂(PF d L W g))
      (∫ ω : Ω d L W, deriv (fun v : ℝ =>
        loopL d L W (HflowBlock d L W v ω) (zt E v) I) u ∂(PF d L W g))
      u := by
  let F : ℝ → Ω d L W → ℂ := fun v ω =>
    loopL d L W (HflowBlock d L W v ω) (zt E v) I
  let F' : ℝ → Ω d L W → ℂ := fun v ω => deriv (F · ω) v
  let bound : Ω d L W → ℝ := flowDerivativeEnvelope d L W E u I
  have hstrict := flowWindow_strict u hu hu1
  have hOpen : Set.Ioo (u / 2) ((1 + u) / 2) ∈ 𝓝 u :=
    isOpen_Ioo.mem_nhds hstrict
  have hs : flowWindow u ∈ 𝓝 u := by
    apply Filter.mem_of_superset hOpen
    intro v hv
    exact ⟨hv.1.le, hv.2.le⟩
  have hF_meas : ∀ᶠ v in 𝓝 u, AEStronglyMeasurable (F v) (PF d L W g) := by
    filter_upwards [hs] with v hv
    have hv' := flowWindow_subset_Ioo u hu hu1 hv
    have hz : (zt E v).im ≠ 0 := by
      rw [spectralZ_im]
      exact ne_of_gt (mul_pos (by linarith [hv'.2]) (spectralM_im_pos hE))
    exact (measurable_gloop_HflowBlock_sample d L W v hz I hwf).aestronglyMeasurable
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hη : 0 < |(zt E u).im| := abs_pos.mpr hz
  have hF_int : Integrable (F u) (PF d L W g) := by
    apply Integrable.of_bound
      (measurable_gloop_HflowBlock_sample d L W u hz I hwf).aestronglyMeasurable
      ((((L * W) ^ d : ℕ) : ℝ) *
        (|(zt E u).im|⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ I.a.length)
    exact Filter.Eventually.of_forall fun ω =>
      norm_gloop_le_crude d L W (HflowBlock_isHermitian d L W u ω)
        hη le_rfl I hwf
  have hF'_meas : AEStronglyMeasurable (F' u) (PF d L W g) :=
    (expected_samplewise_loop_flow_derivative d L W g hE hu hu1 I hwf).1.aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂(PF d L W g), ∀ v ∈ flowWindow u,
      ‖F' v ω‖ ≤ bound ω :=
    Filter.Eventually.of_forall fun ω v hv =>
      norm_samplewise_loop_flow_derivative_le_envelope d L W hE hu hu1 I hwf hv ω
  have hbound_int : Integrable bound (PF d L W g) :=
    integrable_flowDerivativeEnvelope d L W g E u I
  have hdiff : ∀ᵐ ω ∂(PF d L W g), ∀ v ∈ flowWindow u,
      HasDerivAt (F · ω) (F' v ω) v := by
    apply Filter.Eventually.of_forall
    intro ω v hv
    have hv' := flowWindow_subset_Ioo u hu hu1 hv
    have h := hasDerivAt_gloop_HflowBlock_spectralZ d L W ω hE hv'.1 hv'.2 I hwf
    have hval : F' v ω = Matrix.trace (loopWordDeriv d L W ω E v (I.σ.zip I.a)) :=
      h.deriv
    rw [hval]
    exact h
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) hs hF_meas hF_int
    hF'_meas hbound hbound_int hdiff
  exact h.2

/-- **`d/du E 𝓛_u`**: the derivative of the expected finite loop, with its exact Gaussian
second-coordinate sum.
`g` is an extra argument (the one-size law carries the parameter `g`). -/
theorem deriv_integral_gloop_HflowBlock_spectralZ
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    deriv (fun v : ℝ => ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W v ω) (zt E v) I ∂(PF d L W g)) u =
      (1 / (2 * u)) • ∫ ω : Ω d L W,
        ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv d L W u ω c
            (zt E u) (I.σ.zip I.a)) ∂(PF d L W g) +
      ∫ ω : Ω d L W,
        Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))
          ∂(PF d L W g) := by
  rw [(hasDerivAt_integral_gloop_HflowBlock_spectralZ d L W g hE hu hu1 I hwf).deriv]
  exact (expected_samplewise_loop_flow_derivative d L W g hE hu hu1 I hwf).2

end RBM.Gauss
