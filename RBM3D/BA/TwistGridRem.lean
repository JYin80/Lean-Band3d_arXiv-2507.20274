/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGrid

/-!
# The twisted one-step envelope at the matrix level

Clause (ii) of the grid martingale statement `BATwistGridMartAt` (`BA/TwistGrid2`): the one-step expansion of the twisted loop.  No measure of the path occurs in
this file (the grid walk is in `BA/TwistGridRem2`); the Gaussian law of one step is the
fine model `PF d L W g`.

The band's envelope `oneStepEnvelope` (`Path/OneStep`) is for `loopL` at `zt E u`.  The
twisted observable `L̃ = Tr(G₁ E_a G₂ P_{c₁c₂})` at `z_u = ztOf m_F E u` is a word `∏ R_{σᵢ} Eᵢ`
whose letters are `E_a` and `P_{c₁c₂}` (norms `≤ 1`).  Everything below is therefore written for an
arbitrary word `(l, Eᵢ)`: the analogue of the corresponding part of `Path/OneStep` with `Eblk` replaced by a family of letters.
It uses, through `open private`, the private generic jets
of `Path/OneStep` (`OneStep_w0`, `OneStep_w1`, `OneStep_w2`, their norm bounds and derivative
lemmas) and its counts, and the private `TwistGrid_*` lemmas of `BA/TwistGrid`.

* section 1 the word functional `TwistGridRem_F` and its jets `TwistGridRem_J1`, `TwistGridRem_J2`;
* section 2 derivatives, continuity, linearity; section 3 the Stein step; section 4 the space step;
* section 5 the time step and the envelope of a word `TwistGridRem_envelope_word`;
* section 6 the twisted word: `L̃`, `twGenM`, and the envelope `TwistGridRem_envelope`;
* section 7 the Taylor bound of `K̃`, `TwistGridRem_twK_taylor` (the resolvent identity);
* section 8 the one-step bound `TwistGridRem_step` at a Hermitian matrix.

Every statement is for every `d` (no `3 ≤ d`).  Every helper is `private` or prefixed
`TwistGridRem_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open private TwistGrid_hasDerivAt_Gsig_spec TwistGrid_Pb TwistGrid_twL2M_trace TwistGrid_twK_eq TwistGrid_hasDerivAt_twK
  from RBM3D.BA.TwistGrid

open private TwistPins_M_le_one from RBM3D.BA.TwistPins

open private OneStep_w0 OneStep_w1 OneStep_w2 OneStep_Data OneStep_Diff
  OneStep_norm_w0_le OneStep_norm_w1_le OneStep_norm_w2_le OneStep_norm_w1_sub_le OneStep_norm_w2_sub_le
  OneStep_hasDerivAt_w0 OneStep_hasDerivAt_w1 OneStep_hasDerivAt_trace OneStep_hasDerivAt_lineR
  OneStep_norm_Gsig_sub_le OneStep_continuous_Gsig OneStep_Hs OneStep_Hs_eq OneStep_Hs_herm OneStep_continuous_Hs
  OneStep_Hs_update OneStep_integrable_coord_mul OneStep_integrable_normX OneStep_integral_normX_le OneStep_sum_gvar_le
  OneStep_norm_Cb_le OneStep_card_Block OneStep_taylor2 OneStep_closure OneStep_norm_le_sum_entries OneStep_blockMat_add_smul
  OneStep_norm_Eblk_le_one from RBM3D.Path.OneStep

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The word functional and its jets -/

section Word

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W] {ι : Type} (Ei : ι → Matrix (Vtx d L W) (Vtx d L W) ℂ)
  (l : List (Bool × ι))

/-- `Φ(H, z) = tr ∏ᵢ R_{σᵢ} Eᵢ`, `R = Gres H z`: the observable of a word (`loopL` with arbitrary letters). -/
def TwistGridRem_F (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) : ℂ :=
  Matrix.trace (OneStep_w0 (fun σ => Gres H z σ) Ei l)

/-- The first jet `tr w₁` along the direction family `D` (`OneStep_J1` for a word). -/
def TwistGridRem_J1 (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  Matrix.trace (OneStep_w1 (fun σ => Gres H z σ) D Ei l)

/-- The second jet `tr w₂` (`OneStep_J2` for a word). -/
def TwistGridRem_J2 (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  Matrix.trace (OneStep_w2 (fun σ => Gres H z σ) D Ei l)

variable {Ei l}

private theorem TwistGridRem_data (hE : ∀ i, ‖Ei i‖ ≤ 1) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ}
    {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) : OneStep_Data (fun σ => Gres H z σ) D Ei η⁻¹ b :=
  OneStep_Data.mk (by positivity) hb (fun σ => norm_Gsig_le_inv_eta hH hη hz σ) hD hE

/-- `‖Φ‖ ≤ N K^{k}`, `K = η⁻¹`, `k = |l|`. -/
theorem TwistGridRem_norm_F_le (hE : ∀ i, ‖Ei i‖ ≤ 1) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ}
    {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖TwistGridRem_F Ei l H z‖ ≤ (Fintype.card (Vtx d L W) : ℝ) * η⁻¹ ^ l.length := by
  have h := OneStep_norm_w0_le (TwistGridRem_data hE hH hη hz (D := fun _ => 0) (b := 0) le_rfl (fun _ => by simp)) l
  exact (norm_matrix_trace_le_card_mul _).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J1‖ ≤ N k K^{k+1} b`. -/
theorem TwistGridRem_norm_J1_le (hE : ∀ i, ‖Ei i‖ ≤ 1) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ}
    {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) :
    ‖TwistGridRem_J1 Ei l H z D‖ ≤ (Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * η⁻¹ ^ (l.length + 1) * b) := by
  have h := OneStep_norm_w1_le (TwistGridRem_data hE hH hη hz hb hD) l
  exact (norm_matrix_trace_le_card_mul _).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J2‖ ≤ N k (k+1) K^{k+2} b²`. -/
theorem TwistGridRem_norm_J2_le (hE : ∀ i, ‖Ei i‖ ≤ 1) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ}
    {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) :
    ‖TwistGridRem_J2 Ei l H z D‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * (l.length + 1) * η⁻¹ ^ (l.length + 2) * b ^ 2) := by
  have h := OneStep_norm_w2_le (TwistGridRem_data hE hH hη hz hb hD) l
  exact (norm_matrix_trace_le_card_mul _).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

private theorem TwistGridRem_diff (hE : ∀ i, ‖Ei i‖ ≤ 1) {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH₁ : H₁.IsHermitian)
    (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b) (hD : ∀ σ, ‖D σ‖ ≤ b) :
    OneStep_Diff (fun σ => Gres H₁ z σ) (fun σ => Gres H₂ z σ) D Ei η⁻¹ b ‖H₁ - H₂‖ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  refine OneStep_Diff.mk (TwistGridRem_data hE hH₁ hη hz hb hD) (fun σ => norm_Gsig_le_inv_eta hH₂ hη hz σ)
    (norm_nonneg _) (fun σ => ?_)
  refine (OneStep_norm_Gsig_sub_le hH₁ hH₂ hzim σ).trans ?_
  have h1 : |z.im|⁻¹ ≤ η⁻¹ := inv_anti₀ hη hz
  have h2 : |z.im|⁻¹ ^ 2 ≤ η⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- `‖J1(H₁) - J1(H₂)‖ ≤ N k (k+1) K^{k+2} b ‖H₁ - H₂‖`. -/
theorem TwistGridRem_norm_J1_sub_le (hE : ∀ i, ‖Ei i‖ ≤ 1) {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH₁ : H₁.IsHermitian)
    (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b) (hD : ∀ σ, ‖D σ‖ ≤ b) :
    ‖TwistGridRem_J1 Ei l H₁ z D - TwistGridRem_J1 Ei l H₂ z D‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * (l.length + 1) * η⁻¹ ^ (l.length + 2) * b * ‖H₁ - H₂‖) := by
  have h := OneStep_norm_w1_sub_le (TwistGridRem_diff hE hH₁ hH₂ hη hz hb hD) l
  have := norm_matrix_trace_le_card_mul (OneStep_w1 (fun σ => Gres H₁ z σ) D Ei l - OneStep_w1 (fun σ => Gres H₂ z σ) D Ei l)
  rw [Matrix.trace_sub] at this
  exact this.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J2(H₁) - J2(H₂)‖ ≤ N k (k+1) (k+2) K^{k+3} b² ‖H₁ - H₂‖`. -/
theorem TwistGridRem_norm_J2_sub_le (hE : ∀ i, ‖Ei i‖ ≤ 1) {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH₁ : H₁.IsHermitian)
    (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b) (hD : ∀ σ, ‖D σ‖ ≤ b) :
    ‖TwistGridRem_J2 Ei l H₁ z D - TwistGridRem_J2 Ei l H₂ z D‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * (l.length + 1) * (l.length + 2) * η⁻¹ ^ (l.length + 3) * b ^ 2 *
          ‖H₁ - H₂‖) := by
  have h := OneStep_norm_w2_sub_le (TwistGridRem_diff hE hH₁ hH₂ hη hz hb hD) l
  have := norm_matrix_trace_le_card_mul (OneStep_w2 (fun σ => Gres H₁ z σ) D Ei l - OneStep_w2 (fun σ => Gres H₂ z σ) D Ei l)
  rw [Matrix.trace_sub] at this
  exact this.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

end Word

/-! ## 2. Derivatives along a Hermitian line and along the spectral flow, continuity, linearity -/

section Calculus

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W] {ι : Type} {Ei : ι → Matrix (Vtx d L W) (Vtx d L W) ℂ} {l : List (Bool × ι)}

section Line

variable {H B : Matrix (Vtx d L W) (Vtx d L W) ℂ}

/-- First derivative of the word functional along a Hermitian line. -/
theorem TwistGridRem_hasDerivAt_line0 (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (y : ℝ) :
    HasDerivAt (fun s : ℝ => TwistGridRem_F Ei l (H + (s : ℂ) • B) z)
      (TwistGridRem_J1 Ei l (H + (y : ℂ) • B) z (fun _ => B)) y :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w0 (Rt := fun s σ => Gres (H + (s : ℂ) • B) z σ) (D := fun _ => B) (Ei := Ei)
      (OneStep_hasDerivAt_lineR hH hB hz y) l)

/-- Second derivative of the word functional along a Hermitian line. -/
theorem TwistGridRem_hasDerivAt_line1 (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (y : ℝ) :
    HasDerivAt (fun s : ℝ => TwistGridRem_J1 Ei l (H + (s : ℂ) • B) z (fun _ => B))
      (TwistGridRem_J2 Ei l (H + (y : ℂ) • B) z (fun _ => B)) y :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w1 (Rt := fun s σ => Gres (H + (s : ℂ) • B) z σ) (D := fun _ => B) (Ei := Ei)
      (OneStep_hasDerivAt_lineR hH hB hz y) l)

end Line

/-- The spectral direction of the factor `G(σ)` along `z_v = E + (1-v) m`: `m_σ · 1`, `m_+ = m`, `m_- = m̄` (`PropSpin`); `∂_v z_v = -m`. -/
def TwistGridRem_Dsp (d L W : ℕ) (m : ℂ) : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)

section Spec

variable {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}

/-- First derivative of the word functional along the spectral flow `v ↦ ztOf m E v` (`v < 1`, `0 < Im m`). -/
theorem TwistGridRem_hasDerivAt_spec0 (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) (E : ℝ) {v : ℝ} (hv : v < 1) :
    HasDerivAt (fun s : ℝ => TwistGridRem_F Ei l H (ztOf m E s))
      (TwistGridRem_J1 Ei l H (ztOf m E v) (TwistGridRem_Dsp d L W m)) v :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w0 (Rt := fun s σ => Gres H (ztOf m E s) σ) (D := TwistGridRem_Dsp d L W m) (Ei := Ei)
      (fun σ => TwistGrid_hasDerivAt_Gsig_spec hH hm E hv σ) l)

/-- Second derivative of the word functional along the spectral flow. -/
theorem TwistGridRem_hasDerivAt_spec1 (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) (E : ℝ) {v : ℝ} (hv : v < 1) :
    HasDerivAt (fun s : ℝ => TwistGridRem_J1 Ei l H (ztOf m E s) (TwistGridRem_Dsp d L W m))
      (TwistGridRem_J2 Ei l H (ztOf m E v) (TwistGridRem_Dsp d L W m)) v :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w1 (Rt := fun s σ => Gres H (ztOf m E s) σ) (D := TwistGridRem_Dsp d L W m) (Ei := Ei)
      (fun σ => TwistGrid_hasDerivAt_Gsig_spec hH hm E hv σ) l)

end Spec

section Cont

variable {V : Type*} [TopologicalSpace V] {f : V → Matrix (Vtx d L W) (Vtx d L W) ℂ} (hf : Continuous f)
  (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ)
include hf hh hz

theorem TwistGridRem_continuous_F : Continuous fun v => TwistGridRem_F Ei l (f v) z :=
  (continuous_matrixTrace d L W).comp (OneStep_continuous_w0 (fun σ => OneStep_continuous_Gsig hf hh hz σ) l)

theorem TwistGridRem_continuous_J1 : Continuous fun v => TwistGridRem_J1 Ei l (f v) z D :=
  (continuous_matrixTrace d L W).comp (OneStep_continuous_w1 (fun σ => OneStep_continuous_Gsig hf hh hz σ) l)

theorem TwistGridRem_continuous_J2 : Continuous fun v => TwistGridRem_J2 Ei l (f v) z D :=
  (continuous_matrixTrace d L W).comp (OneStep_continuous_w2 (fun σ => OneStep_continuous_Gsig hf hh hz σ) l)

end Cont

/-- Linearity of the first jet in the direction: `X = Σ_c ω_c C_c`. -/
theorem TwistGridRem_J1_Xmat (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (ω : Ω d L W) :
    TwistGridRem_J1 Ei l H z (fun _ => blockMat d L W (Xmat d L W ω))
      = ∑ c : CoordF d L W, (ω c : ℂ) *
          TwistGridRem_J1 Ei l H z (fun _ => blockMat d L W (coordinateMatrix d L W c)) := by
  have hX : (fun _ : Bool => blockMat d L W (Xmat d L W ω))
      = ∑ c : CoordF d L W, (ω c) • (fun _ : Bool => blockMat d L W (coordinateMatrix d L W c)) := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply]
    ext p q
    rw [Xmat_eq_sum_coordinates]
    simp [blockMat, Matrix.sum_apply]
  have hlin := map_sum (OneStep_w1Lin (fun σ => Gres H z σ) Ei l)
    (fun c : CoordF d L W => (ω c) • (fun _ : Bool => blockMat d L W (coordinateMatrix d L W c))) Finset.univ
  simp only [map_smul] at hlin
  unfold TwistGridRem_J1
  rw [hX]
  change Matrix.trace ((OneStep_w1Lin (fun σ => Gres H z σ) Ei l) _) = _
  rw [hlin, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.trace_smul, Complex.real_smul]
  rfl

end Calculus

/-! ## 3. The Stein step: the derivative of `x ↦ E Φ(M + x X)` -/

section Stein

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W] {ι : Type} {Ei : ι → Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {l : List (Bool × ι)} {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
  (hE : ∀ i, ‖Ei i‖ ≤ 1)
include hM hz hE

/-- The coordinate Stein identity, for the first jet along the coordinate direction (`OneStep_stein_coord`). -/
private theorem TwistGridRem_stein_coord (x : ℝ) (c : CoordF d L W) :
    ∫ ω : Ω d L W, (ω c : ℂ) *
        TwistGridRem_J1 Ei l (OneStep_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g)
      = ((gvarF d L W g c : ℝ) : ℂ) * ((x : ℂ) * ∫ ω : Ω d L W,
        TwistGridRem_J2 Ei l (OneStep_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g)) := by
  set Cb := blockMat d L W (coordinateMatrix d L W c) with hCb
  have hCh : Cb.IsHermitian := (coordinateMatrix_isHermitian d L W c).submatrix _
  set φ : Ω d L W → ℂ := fun ω => TwistGridRem_J1 Ei l (OneStep_Hs M x ω) z (fun _ => Cb) with hg
  set φ' : Ω d L W → ℂ := fun ω => (x : ℂ) * TwistGridRem_J2 Ei l (OneStep_Hs M x ω) z (fun _ => Cb) with hg'
  have hgc : Continuous φ :=
    TwistGridRem_continuous_J1 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz _
  have hg'c : Continuous φ' :=
    continuous_const.mul (TwistGridRem_continuous_J2 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz _)
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hgb : ∃ C : ℝ, ∀ ω, ‖φ ω‖ ≤ C := ⟨_, fun ω =>
    TwistGridRem_norm_J1_le hE (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb) (fun _ => le_rfl)⟩
  have hg'b : ∃ C : ℝ, ∀ ω, ‖φ' ω‖ ≤ C := ⟨|x| * _, fun ω => by
    rw [hg', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (TwistGridRem_norm_J2_le hE (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb) (fun _ => le_rfl)) (abs_nonneg _)⟩
  have hderiv : ∀ ω, HasDerivAt (fun t : ℝ => φ (Function.update ω c t)) (φ' ω) (ω c) := by
    intro ω
    have hAh := OneStep_Hs_herm hM x ω
    have hφ := TwistGridRem_hasDerivAt_line1 (Ei := Ei) (l := l) hAh hCh hz (x * (ω c - ω c))
    have hh : HasDerivAt (fun t : ℝ => x * (t - ω c)) x (ω c) := by
      simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul x
    have hcomp := hφ.scomp (ω c) hh
    have hfun : (fun t : ℝ => φ (Function.update ω c t)) =
        ((fun s : ℝ => TwistGridRem_J1 Ei l (OneStep_Hs M x ω + (s : ℂ) • Cb) z (fun _ => Cb)) ∘
          fun t : ℝ => x * (t - ω c)) := by
      funext t
      simp only [Function.comp, hg, OneStep_Hs_update, hCb]
    rw [hfun]
    refine hcomp.congr_deriv ?_
    simp [hg']
  have h := GaussianProduct.stein (gvarF d L W g) c φ φ' hgc hg'c hderiv hgb hg'b
  have hlaw : PF d L W g = GaussianProduct.law (gvarF d L W g) := rfl
  rw [← hlaw] at h
  simp only [Complex.real_smul] at h
  rw [h, hg', integral_const_mul]

/-- **The derivative of `x ↦ E Φ(M + x X)`**: `x Σ_c gvar_c E ∂²_c Φ(M + x X)`, by Stein (`OneStep_hasDerivAt_F`). -/
private theorem TwistGridRem_hasDerivAt_F (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M y ω) z ∂(PF d L W g))
      ((x : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M x ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g)) x := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hcontgl : ∀ y : ℝ, Continuous fun ω : Ω d L W => TwistGridRem_F Ei l (OneStep_Hs M y ω) z :=
    fun y => TwistGridRem_continuous_F (OneStep_continuous_Hs M y) (OneStep_Hs_herm hM y) hz
  have hint : ∀ y : ℝ, Integrable (fun ω : Ω d L W => TwistGridRem_F Ei l (OneStep_Hs M y ω) z) (PF d L W g) :=
    fun y => Integrable.of_bound (hcontgl y).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => TwistGridRem_norm_F_le hE (OneStep_Hs_herm hM y ω) hη le_rfl)
  have hJc : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      TwistGridRem_J1 Ei l (OneStep_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) :=
    fun c => TwistGridRem_continuous_J1 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz _
  have hF'cont : Continuous fun ω : Ω d L W =>
      TwistGridRem_J1 Ei l (OneStep_Hs M x ω) z (fun _ => blockMat d L W (Xmat d L W ω)) := by
    simp only [TwistGridRem_J1_Xmat]
    exact continuous_finsetSum _ fun c _ =>
      (Complex.continuous_ofReal.comp (continuous_apply c)).mul (hJc c)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := PF d L W g)
    (s := Set.univ) (x₀ := x)
    (F := fun y ω => TwistGridRem_F Ei l (OneStep_Hs M y ω) z)
    (F' := fun y ω => TwistGridRem_J1 Ei l (OneStep_Hs M y ω) z (fun _ => blockMat d L W (Xmat d L W ω)))
    (bound := fun ω => ((Fintype.card (Vtx d L W) : ℝ) *
      ((l.length : ℝ) * |z.im|⁻¹ ^ (l.length + 1))) * ‖blockMat d L W (Xmat d L W ω)‖)
    Filter.univ_mem (Filter.Eventually.of_forall fun y => (hcontgl y).aestronglyMeasurable)
    (hint x) hF'cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω y _ =>
      (TwistGridRem_norm_J1_le hE (OneStep_Hs_herm hM y ω) hη le_rfl (norm_nonneg _) (fun _ => le_rfl)).trans
        (le_of_eq (by ring)))
    ((OneStep_integrable_normX g).const_mul _)
    (Filter.Eventually.of_forall fun ω y _ => by
      have hXb : (blockMat d L W (Xmat d L W ω)).IsHermitian := (Xmat_isHermitian d L W ω).submatrix _
      have := TwistGridRem_hasDerivAt_line0 (Ei := Ei) (l := l) hMb hXb hz y
      simpa only [OneStep_Hs_eq] using this)
  refine hD.congr_deriv ?_
  simp only [TwistGridRem_J1_Xmat]
  rw [integral_finsetSum _ fun c _ => OneStep_integrable_coord_mul g c (hJc c)
    (fun ω => TwistGridRem_norm_J1_le hE (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg _) (fun _ => le_rfl))]
  simp_rw [TwistGridRem_stein_coord g hM hz hE x]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

end Stein

/-! ## 4. The space step: `E Φ(M + τ X) - Φ(M) - τ² g(M)` -/

section SpaceStep

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W] {ι : Type} (Ei : ι → Matrix (Vtx d L W) (Vtx d L W) ℂ)
  (l : List (Bool × ι))

/-- The `g`-part: `g_z(M) = ½ Σ_c gvar_c ∂²_c Φ(M)` (`OneStep_g`). -/
def TwistGridRem_g (z : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
    TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c))

variable {Ei l} {M : Matrix (Idx d L W) (Idx d L W) ℂ} {z : ℂ} (hE : ∀ i, ‖Ei i‖ ≤ 1)
include hE

/-- The Lipschitz estimate of one coordinate second jet along the Gaussian sample (`OneStep_coord_sub_le`). -/
private theorem TwistGridRem_coord_sub_le (hM : M.IsHermitian) {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    (c : CoordF d L W) (y : ℝ) (ω : Ω d L W) :
    ‖TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c))
        - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c))‖
      ≤ (((Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * (l.length + 1) *
          (l.length + 2) * η⁻¹ ^ (l.length + 3)) * 4) * |y|) * ‖blockMat d L W (Xmat d L W ω)‖ := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have h := TwistGridRem_norm_J2_sub_le (l := l) hE (OneStep_Hs_herm hM y ω) hMb hη hz (D := fun _ =>
    blockMat d L W (coordinateMatrix d L W c)) (b := 2) zero_le_two (fun _ => OneStep_norm_Cb_le c)
  have hd : ‖OneStep_Hs M y ω - blockMat d L W M‖ = |y| * ‖blockMat d L W (Xmat d L W ω)‖ := by
    rw [OneStep_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [hd] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- The key size estimate: the derivative of `ψ(y) = F(y) - F(0) - y² g(M)` is `O(y²)` (`OneStep_psi_deriv_le`). -/
private theorem TwistGridRem_psi_deriv_le (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) {y : ℝ} (hy : 0 ≤ y) :
    ‖(y : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g)
      - ((2 * y : ℝ) : ℂ) * TwistGridRem_g g Ei l z M‖
      ≤ (32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
          ((l.length : ℝ) * (l.length + 1) * (l.length + 2) * η⁻¹ ^ (l.length + 3))) * y ^ 2 := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  set C₃ : ℝ := (Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * (l.length + 1) *
    (l.length + 2) * η⁻¹ ^ (l.length + 3)) * 4 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  have hcont : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) :=
    fun c => TwistGridRem_continuous_J2 (OneStep_continuous_Hs M y) (OneStep_Hs_herm hM y) hz' _
  have hint : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W =>
      TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c))) (PF d L W g) :=
    fun c => Integrable.of_bound (hcont c).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        TwistGridRem_norm_J2_le hE (OneStep_Hs_herm hM y ω) hη hz (norm_nonneg _) (fun _ => le_rfl))
  -- one coordinate
  have hone : ∀ c : CoordF d L W,
      ‖(∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g))
        - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c))‖
      ≤ (C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
    intro c
    have hsub : (∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g))
        - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c))
        = ∫ ω : Ω d L W, (TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c))
          - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c))) ∂(PF d L W g) := by
      rw [integral_sub (hint c) (integrable_const _)]
      simp
    rw [hsub]
    refine (norm_integral_le_of_norm_le (((OneStep_integrable_normX g).const_mul (C₃ * |y|)))
      (Filter.Eventually.of_forall fun ω =>
        TwistGridRem_coord_sub_le hE hM hη hz c y ω)).trans ?_
    rw [integral_const_mul, abs_of_nonneg hy]
    have := OneStep_integral_normX_le (d := d) (L := L) (W := W) g
    rw [← OneStep_card_Idx] at this
    calc C₃ * y * ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(PF d L W g)
        ≤ C₃ * y * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := rfl
  have hsum : ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) * ∫ ω : Ω d L W, TwistGridRem_J2 Ei l
        (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g)
      - 2 * TwistGridRem_g g Ei l z M
      = ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g))
        - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c))) := by
    simp only [TwistGridRem_g, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hmain : (y : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) * ∫ ω : Ω d L W, TwistGridRem_J2 Ei l
        (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g)
      - ((2 * y : ℝ) : ℂ) * TwistGridRem_g g Ei l z M
      = (y : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g))
        - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c))) := by
    rw [← hsum]
    push_cast
    ring
  rw [hmain, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
  have hsn : ‖∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g))
        - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)))‖
      ≤ (2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : CoordF d L W, ‖((gvarF d L W g c : ℝ) : ℂ) *
          ((∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
            (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g))
          - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)))‖
        ≤ ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun c _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gvarF d L W g c).coe_nonneg]
            exact mul_le_mul_of_nonneg_left (hone c) (gvarF d L W g c).coe_nonneg
      _ = (∑ c : CoordF d L W, (gvarF d L W g c : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right (OneStep_sum_gvar_le g) (by positivity)
  calc y * ‖∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g))
        - TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)))‖
      ≤ y * ((2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hsn hy
    _ = _ := by rw [hC₃]; ring

/-- **The space step**: `‖E Φ(M + τ X) - Φ(M) - τ² g(M)‖ ≤ (Λ/3) τ³` (`OneStep_space_step`). -/
private theorem TwistGridRem_space_step (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M τ ω) z ∂(PF d L W g)) - TwistGridRem_F Ei l (blockMat d L W M) z
        - ((τ ^ 2 : ℝ) : ℂ) * TwistGridRem_g g Ei l z M‖
      ≤ ((32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
          ((l.length : ℝ) * (l.length + 1) * (l.length + 2) * η⁻¹ ^ (l.length + 3))) / 3) * τ ^ 3 := by
  set Λ : ℝ := 32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
    ((l.length : ℝ) * (l.length + 1) * (l.length + 2) * η⁻¹ ^ (l.length + 3)) with hΛ
  set F : ℝ → ℂ := fun y => ∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M y ω) z ∂(PF d L W g) with hF
  have hF0 : F 0 = TwistGridRem_F Ei l (blockMat d L W M) z := by
    simp [hF, OneStep_Hs]
  set ψ : ℝ → ℂ := fun y => F y - F 0 - ((y ^ 2 : ℝ) : ℂ) * TwistGridRem_g g Ei l z M with hψ
  set ψ' : ℝ → ℂ := fun y => (y : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, TwistGridRem_J2 Ei l (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) ∂(PF d L W g)
      - ((2 * y : ℝ) : ℂ) * TwistGridRem_g g Ei l z M with hψ'
  have hd : ∀ y : ℝ, HasDerivAt ψ (ψ' y) y := by
    intro y
    have h1 := ((TwistGridRem_hasDerivAt_F (l := l) g hM hz' hE y).sub_const (F 0)).sub
      ((((hasDerivAt_pow 2 y).ofReal_comp)).mul_const (TwistGridRem_g g Ei l z M))
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
    (fun y hy => TwistGridRem_psi_deriv_le g hE hM hz' hη hz hy.1)
  have := key (x := τ) ⟨hτ, le_rfl⟩
  simp only [hψ] at this
  rw [hF0] at this
  exact this

end SpaceStep

/-! ## 5. The time step and the envelope of a word -/

section Envelope

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W] {ι : Type} {Ei : ι → Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {l : List (Bool × ι)}

/-- `η_w = (1-w) Im m ≤ |Im z_v|` for `v ≤ w < 1` (the gap of `spectralZ_im_gap` (`Gauss/FlowCalculus`), at `z_v = E + (1-v) m`). -/
theorem TwistGridRem_eta_le {m : ℂ} (hm : 0 < m.im) (E : ℝ) {v w : ℝ} (hvw : v ≤ w) (hw : w < 1) :
    etaOf m w ≤ |(ztOf m E v).im| := by
  rw [ztOf_im, etaOf, etaOf, abs_of_pos (mul_pos (by linarith) hm)]
  exact mul_le_mul_of_nonneg_right (by linarith) hm.le

theorem TwistGridRem_eta_pos {m : ℂ} (hm : 0 < m.im) {w : ℝ} (hw : w < 1) : 0 < etaOf m w :=
  mul_pos (by linarith) hm

private theorem TwistGridRem_norm_Dsp_le {m : ℂ} (hmn : ‖m‖ ≤ 1) (σ : Bool) : ‖TwistGridRem_Dsp d L W m σ‖ ≤ 1 := by
  have hn : ‖PropSpin m σ‖ ≤ 1 := by
    cases σ <;> simpa [PropSpin] using hmn
  unfold TwistGridRem_Dsp
  rw [norm_smul]
  calc ‖PropSpin m σ‖ * ‖(1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul hn OneStep_norm_one_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **The time step**: Taylor expansion of `v ↦ Φ(A, z_v)` at fixed `A` (`OneStep_time_step`). -/
private theorem TwistGridRem_time_step (hE : ∀ i, ‖Ei i‖ ≤ 1) {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {m : ℂ} (hm : 0 < m.im) (hmn : ‖m‖ ≤ 1) (E : ℝ) {u Δ : ℝ} (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1) :
    ‖TwistGridRem_F Ei l (blockMat d L W A) (ztOf m E (u + Δ)) - TwistGridRem_F Ei l (blockMat d L W A) (ztOf m E u)
        - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W A) (ztOf m E u) (TwistGridRem_Dsp d L W m)‖
      ≤ ((Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * (l.length + 1) *
          (etaOf m (u + Δ))⁻¹ ^ (l.length + 2))) * Δ ^ 2 / 2 := by
  have hAb : (blockMat d L W A).IsHermitian := hA.submatrix _
  have hη := TwistGridRem_eta_pos hm hu1
  have h := OneStep_taylor2 (f := fun v => TwistGridRem_F Ei l (blockMat d L W A) (ztOf m E v))
    (f₁ := fun v => TwistGridRem_J1 Ei l (blockMat d L W A) (ztOf m E v) (TwistGridRem_Dsp d L W m))
    (f₂ := fun v => TwistGridRem_J2 Ei l (blockMat d L W A) (ztOf m E v) (TwistGridRem_Dsp d L W m))
    (a := u) (b := u + Δ)
    (B := (Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * (l.length + 1) *
      (etaOf m (u + Δ))⁻¹ ^ (l.length + 2))) (by linarith)
    (fun v hv' => TwistGridRem_hasDerivAt_spec0 hAb hm E (by linarith [hv'.2]))
    (fun v hv' => TwistGridRem_hasDerivAt_spec1 hAb hm E (by linarith [hv'.2]))
    (fun v hv' => by
      have := TwistGridRem_norm_J2_le (l := l) hE hAb hη (TwistGridRem_eta_le hm E hv'.2 hu1) zero_le_one
        (D := TwistGridRem_Dsp d L W m) (TwistGridRem_norm_Dsp_le hmn)
      simpa using this)
  simpa using h

/-- The one-step expansion of a word with its envelope: for Hermitian `M` and `u + Δ < 1`,
`‖E Φ_{u+Δ}(M + √Δ X) - Φ_u(M) - Δ (g_u(M) + J1_u(M))‖ ≤ 16 (k+3)⁴ N⁴ (1 + η_{u+Δ}⁻¹)^{k+4} Δ^{3/2}`
(`OneStepEnvelope`, `Path/OneStep`, for the word `(l, Eᵢ)` at the flow `z_v = E + (1-v) m`). -/
theorem TwistGridRem_envelope_word (hE : ∀ i, ‖Ei i‖ ≤ 1) {m : ℂ} (hm : 0 < m.im) (hmn : ‖m‖ ≤ 1) (E : ℝ) {u Δ : ℝ}
    (hu : 0 ≤ u) (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ‖(∫ ω : Ω d L W, TwistGridRem_F Ei l (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω)) (ztOf m E (u + Δ))
          ∂(PF d L W g)) - TwistGridRem_F Ei l (blockMat d L W M) (ztOf m E u) -
        (Δ : ℂ) * (TwistGridRem_g g Ei l (ztOf m E u) M +
          TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m))‖ ≤
      16 * ((l.length : ℝ) + 3) ^ 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 4 * (1 + (etaOf m (u + Δ))⁻¹) ^ (l.length + 4) *
        Δ ^ ((3 : ℝ) / 2) := by
  have hΔ1 : Δ < 1 := by linarith
  set τ : ℝ := Real.sqrt Δ with hτ
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg Δ
  have hτ2 : τ ^ 2 = Δ := Real.sq_sqrt hΔ
  have hτΔ : Δ ≤ τ := by nlinarith
  have hτ3 : Δ ^ ((3 : ℝ) / 2) = τ ^ 3 := by
    rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hΔ]
    norm_num
  have hη : 0 < etaOf m (u + Δ) := TwistGridRem_eta_pos hm hu1
  have hηu : etaOf m (u + Δ) ≤ |(ztOf m E u).im| := TwistGridRem_eta_le hm E (by linarith) hu1
  have hzu : (ztOf m E u).im ≠ 0 := fun h => absurd hηu (by rw [h]; simpa using hη)
  have hηv : etaOf m (u + Δ) ≤ |(ztOf m E (u + Δ)).im| := TwistGridRem_eta_le hm E le_rfl hu1
  have hzv : (ztOf m E (u + Δ)).im ≠ 0 := fun h => absurd hηv (by rw [h]; simpa using hη)
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  set c₁ : ℝ := (Fintype.card (Vtx d L W) : ℝ) * ((l.length : ℝ) * (l.length + 1) *
    (etaOf m (u + Δ))⁻¹ ^ (l.length + 2)) with hc₁
  -- integrability of the sample functionals
  have hint : ∀ v : ℝ, (ztOf m E v).im ≠ 0 → Integrable
      (fun ω : Ω d L W => TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E v)) (PF d L W g) := fun v hv => by
    have hv' : 0 < |(ztOf m E v).im| := abs_pos.mpr hv
    exact Integrable.of_bound (TwistGridRem_continuous_F (OneStep_continuous_Hs M τ)
      (OneStep_Hs_herm hM τ) hv).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => TwistGridRem_norm_F_le hE (OneStep_Hs_herm hM τ ω) hv' le_rfl)
  -- the space step
  have hT2 := TwistGridRem_space_step (l := l) g hE hM hzu hη hηu hτ0
  -- the time step, integrated
  have hT1 : ‖(∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E (u + Δ)) ∂(PF d L W g))
      - (∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E u) ∂(PF d L W g))
      - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m)‖
      ≤ c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
    have hpt : ∀ ω : Ω d L W, ‖TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E (u + Δ))
        - TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E u)
        - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m)‖
        ≤ c₁ * Δ ^ 2 / 2 + (c₁ * Δ * τ) * ‖blockMat d L W (Xmat d L W ω)‖ := by
      intro ω
      have hA : (M + (τ : ℂ) • Xmat d L W ω).IsHermitian :=
        OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d L W ω) τ
      have h1 := TwistGridRem_time_step (l := l) hE hA hm hmn E hΔ hu1
      have h2 := TwistGridRem_norm_J1_sub_le (l := l) hE (OneStep_Hs_herm hM τ ω) hMb hη hηu zero_le_one
        (D := TwistGridRem_Dsp d L W m) (TwistGridRem_norm_Dsp_le hmn)
      have hd : ‖OneStep_Hs M τ ω - blockMat d L W M‖ = τ * ‖blockMat d L W (Xmat d L W ω)‖ := by
        rw [OneStep_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hτ0]
      rw [hd] at h2
      have hsplit : TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E (u + Δ))
          - TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E u)
          - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m)
          = (TwistGridRem_F Ei l (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E (u + Δ))
            - TwistGridRem_F Ei l (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E u)
            - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E u)
              (TwistGridRem_Dsp d L W m))
            + (Δ : ℂ) * (TwistGridRem_J1 Ei l (OneStep_Hs M τ ω) (ztOf m E u) (TwistGridRem_Dsp d L W m)
              - TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m)) := by
        simp only [OneStep_Hs]
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h3 : ‖(Δ : ℂ) * (TwistGridRem_J1 Ei l (OneStep_Hs M τ ω) (ztOf m E u) (TwistGridRem_Dsp d L W m)
          - TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m))‖
          ≤ Δ * (c₁ * (τ * ‖blockMat d L W (Xmat d L W ω)‖)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
        refine mul_le_mul_of_nonneg_left ?_ hΔ
        refine h2.trans (le_of_eq ?_)
        rw [hc₁]
        ring
      have h1' : ‖TwistGridRem_F Ei l (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E (u + Δ))
            - TwistGridRem_F Ei l (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E u)
            - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E u)
              (TwistGridRem_Dsp d L W m)‖ ≤ c₁ * Δ ^ 2 / 2 := h1
      calc _ ≤ c₁ * Δ ^ 2 / 2 + Δ * (c₁ * (τ * ‖blockMat d L W (Xmat d L W ω)‖)) := add_le_add h1' h3
        _ = _ := by ring
    have hsub : (∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E (u + Δ)) ∂(PF d L W g))
        - (∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E u) ∂(PF d L W g))
        - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m)
        = ∫ ω : Ω d L W, (TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E (u + Δ))
          - TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E u)
          - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m))
            ∂(PF d L W g) := by
      have i12 : Integrable (fun ω : Ω d L W => TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E (u + Δ))
          - TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E u)) (PF d L W g) :=
        (hint _ hzv).sub (hint _ hzu)
      rw [integral_sub i12 (integrable_const _), integral_sub (hint _ hzv) (hint _ hzu)]
      simp
    rw [hsub]
    have ib : Integrable (fun ω : Ω d L W => c₁ * Δ ^ 2 / 2
        + (c₁ * Δ * τ) * ‖blockMat d L W (Xmat d L W ω)‖) (PF d L W g) :=
      (integrable_const _).add ((OneStep_integrable_normX g).const_mul (c₁ * Δ * τ))
    refine (norm_integral_le_of_norm_le ib (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) ((OneStep_integrable_normX g).const_mul _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hν := OneStep_integral_normX_le (d := d) (L := L) (W := W) g
    rw [← OneStep_card_Idx] at hν
    have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; have := hη.le; positivity
    have hΔ2 : Δ ^ 2 ≤ Δ * τ := by nlinarith
    calc c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(PF d L W g)
        ≤ c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          gcongr
      _ ≤ c₁ * (Δ * τ) / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          gcongr
      _ = c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          rw [← hτ2]
          ring
  -- assembly
  have hLHS : (∫ ω : Ω d L W, TwistGridRem_F Ei l (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω))
        (ztOf m E (u + Δ)) ∂(PF d L W g)) - TwistGridRem_F Ei l (blockMat d L W M) (ztOf m E u)
        - (Δ : ℂ) * (TwistGridRem_g g Ei l (ztOf m E u) M +
          TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m))
      = ((∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E u) ∂(PF d L W g))
          - TwistGridRem_F Ei l (blockMat d L W M) (ztOf m E u)
          - ((τ ^ 2 : ℝ) : ℂ) * TwistGridRem_g g Ei l (ztOf m E u) M)
        + ((∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E (u + Δ)) ∂(PF d L W g))
          - (∫ ω : Ω d L W, TwistGridRem_F Ei l (OneStep_Hs M τ ω) (ztOf m E u) ∂(PF d L W g))
          - (Δ : ℂ) * TwistGridRem_J1 Ei l (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m)) := by
    rw [hτ2]
    simp only [OneStep_Hs]
    ring
  rw [hLHS]
  refine (norm_add_le _ _).trans ((add_le_add hT2 hT1).trans ?_)
  rw [hτ3, OneStep_card_Idx, OneStep_card_Block]
  have hN : (1 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    have : 1 ≤ (W * L) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
        (Nat.pos_of_ne_zero (NeZero.ne L)))
    exact_mod_cast this
  have hcl := OneStep_closure l.length hN (inv_nonneg.mpr hη.le)
  have hτ3' : 0 ≤ τ ^ 3 := by positivity
  rw [hc₁, OneStep_card_Block]
  calc _ = (32 * (((W * L) ^ d : ℕ) : ℝ) ^ 3 * (((W * L) ^ d : ℕ) : ℝ) *
            ((l.length : ℝ) * (l.length + 1) * (l.length + 2) * (etaOf m (u + Δ))⁻¹ ^ (l.length + 3))
            / 3
          + ((((W * L) ^ d : ℕ) : ℝ) * ((l.length : ℝ) * (l.length + 1) *
            (etaOf m (u + Δ))⁻¹ ^ (l.length + 2))) * (1 / 2 + 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2))
          * τ ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcl hτ3'

end Envelope

section DerivDeriv

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W] {ι : Type} {Ei : ι → Matrix (Vtx d L W) (Vtx d L W) ℂ} {l : List (Bool × ι)}

/-- The mixed second derivative along a coordinate line, as the second jet (`OneStep_deriv_deriv`). -/
theorem TwistGridRem_deriv_deriv {M C : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (hC : C.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    deriv (deriv (fun y : ℝ => TwistGridRem_F Ei l (blockMat d L W (M + (y : ℂ) • C)) z)) 0
      = TwistGridRem_J2 Ei l (blockMat d L W M) z (fun _ => blockMat d L W C) := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hCb : (blockMat d L W C).IsHermitian := hC.submatrix _
  simp only [OneStep_blockMat_add_smul]
  have h1 : deriv (fun y : ℝ => TwistGridRem_F Ei l (blockMat d L W M + (y : ℂ) • blockMat d L W C) z)
      = fun y : ℝ => TwistGridRem_J1 Ei l (blockMat d L W M + (y : ℂ) • blockMat d L W C) z (fun _ => blockMat d L W C) := by
    funext y
    exact (TwistGridRem_hasDerivAt_line0 hMb hCb hz y).deriv
  rw [h1]
  simpa using (TwistGridRem_hasDerivAt_line1 (Ei := Ei) (l := l) hMb hCb hz 0).deriv

end DerivDeriv

/-! ## 6. The twisted word: `L̃ = Tr(G₁ E_a G₂ P_{c₁c₂})`, `twGenM`, and the envelope -/

section Twisted

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- The letters `E_a`, `P_{c₁c₂}` of the twisted word. -/
def TwistGridRem_letters (d L W : ℕ) [NeZero L] (a c₁ c₂ : Zd d L) : Fin 2 → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  ![Eblk d L W a, TwistGrid_Pb c₁ c₂]

/-- The word `G(σ₁) E_a G(σ₂) P_{c₁c₂}`: `[(σ₁, 0), (σ₂, 1)]` over the letters of `TwistGridRem_letters`. -/
def TwistGridRem_word (σ : Fin 2 → Bool) : List (Bool × Fin 2) := [(σ 0, 0), (σ 1, 1)]

/-- `‖P_{c₁c₂}‖ ≤ 1`: `P = W^{-d} Σ_o |(c₁,o)⟩⟨(c₂,o)|` has `W^d` entries of modulus `W^{-d}`. -/
private theorem TwistGridRem_norm_Pb_le {d L W : ℕ} [NeZero L] [NeZero W] (c₁ c₂ : Zd d L) : ‖TwistGrid_Pb (W := W) c₁ c₂‖ ≤ 1 := by
  refine (OneStep_norm_le_sum_entries _).trans ?_
  have hent : ∀ p q : Vtx d L W, ‖TwistGrid_Pb (W := W) c₁ c₂ p q‖ =
      if p.1 = c₁ ∧ q.1 = c₂ ∧ p.2 = q.2 then ((W : ℝ) ^ d)⁻¹ else 0 := by
    intro p q
    simp only [TwistGrid_Pb, Matrix.of_apply]
    split_ifs
    · simp
    · simp
  simp only [hent, Fintype.sum_prod_type]
  have h1 : ∀ (x : Zd d L) (x_1 : Fin (W ^ d)) (x_2 : Zd d L), ∑ x_3 : Fin (W ^ d),
      (if x = c₁ ∧ x_2 = c₂ ∧ x_1 = x_3 then ((W : ℝ) ^ d)⁻¹ else 0) =
      if x = c₁ ∧ x_2 = c₂ then ((W : ℝ) ^ d)⁻¹ else 0 := by
    intro x x_1 x_2
    by_cases h : x = c₁ ∧ x_2 = c₂
    · simp [h.1, h.2]
    · have h' : ∀ y : Fin (W ^ d), ¬ (x = c₁ ∧ x_2 = c₂ ∧ x_1 = y) := fun y hh => h ⟨hh.1, hh.2.1⟩
      simp [h, h']
  simp only [h1]
  simp [ite_and, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem TwistGridRem_letters_norm (a c₁ c₂ : Zd d (sz.L n)) :
    ∀ i, ‖TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂ i‖ ≤ 1 := by
  intro i
  fin_cases i
  · exact OneStep_norm_Eblk_le_one a
  · exact TwistGridRem_norm_Pb_le c₁ c₂

/-- `L̃ = Tr(G₁ E_a G₂ P_{c₁c₂})` is the word functional of the twisted word (Hermitian `H`). -/
theorem TwistGridRem_twL2M_eq {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) (u : ℝ)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    twL2M sz lam0 E n u H σ a c₁ c₂ = TwistGridRem_F (TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂) (TwistGridRem_word σ)
      (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) := by
  rw [TwistGrid_twL2M_trace sz lam0 E n u hH σ a c₁ c₂]
  simp [TwistGridRem_F, TwistGridRem_word, TwistGridRem_letters, OneStep_w0, Matrix.mul_assoc]

/-- `twGenM` in the jets: for Hermitian `H`, `u < 1`, `0 < Im m_F`: `twGenM = g_z(H) + J1_z(H; TwistGridRem_Dsp)` (`genMat = OneStep_g + J1`, `Path/OneStep`). -/
theorem TwistGridRem_twGenM_eq {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (hm : 0 < (BAmF sz lam0 E n).im) {u : ℝ} (hu1 : u < 1) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    twGenM sz lam0 E n u H σ a c₁ c₂ =
      TwistGridRem_g 0 (TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂) (TwistGridRem_word σ)
        (ztOf (BAmF sz lam0 E n) (E n) u) H +
      TwistGridRem_J1 (TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂) (TwistGridRem_word σ)
        (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (TwistGridRem_Dsp d (sz.L n) (sz.W n) (BAmF sz lam0 E n)) := by
  have hz : (ztOf (BAmF sz lam0 E n) (E n) u).im ≠ 0 := by
    rw [ztOf_im]
    exact (TwistGridRem_eta_pos hm hu1).ne'
  have hHb : (blockMat d (sz.L n) (sz.W n) H).IsHermitian := hH.submatrix _
  unfold twGenM TwistGridRem_g
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    have hF : (fun y : ℝ => twL2M sz lam0 E n u (H + (y : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c) σ a c₁ c₂) =
        fun y : ℝ => TwistGridRem_F (TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂) (TwistGridRem_word σ)
          (blockMat d (sz.L n) (sz.W n) (H + (y : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c))
          (ztOf (BAmF sz lam0 E n) (E n) u) :=
      funext fun y => TwistGridRem_twL2M_eq sz lam0 E n
        (OneStep_isHermitian_add_realSmul hH (coordinateMatrix_isHermitian d (sz.L n) (sz.W n) c) y) u σ a c₁ c₂
    rw [hF]
    exact TwistGridRem_deriv_deriv hH (coordinateMatrix_isHermitian d (sz.L n) (sz.W n) c) hz
  · have hG : (fun v : ℝ => twL2M sz lam0 E n v H σ a c₁ c₂) =
        fun v : ℝ => TwistGridRem_F (TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂) (TwistGridRem_word σ)
          (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) v) :=
      funext fun v => TwistGridRem_twL2M_eq sz lam0 E n hH v σ a c₁ c₂
    rw [hG]
    exact (TwistGridRem_hasDerivAt_spec0 hHb hm (E n) hu1).deriv

/-- The twisted one-step envelope (the analogue of `oneStepEnvelope`, `Path/OneStep`, for `L̃` at `z_v = E + (1-v) m_F`):
for Hermitian `M`, `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1`, `‖E L̃_{u+Δ}(M + √Δ X) - L̃_u(M) - Δ twGenM_u(M)‖ ≤ 10⁴ N⁴ (1 + η⁻¹)⁶ Δ^{3/2}`,
`N = (WL)^d`, `η = (1 - u - Δ) Im m_F`, for the Gaussian law of the coupling `0` (`PF d L W 0`), every `d`. -/
theorem TwistGridRem_envelope (hm : 0 < (BAmF sz lam0 E n).im) (hmn : ‖BAmF sz lam0 E n‖ ≤ 1) (σ : Fin 2 → Bool)
    (a c₁ c₂ : Zd d (sz.L n)) {u Δ : ℝ} (hu : 0 ≤ u) (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    ‖(∫ ω : Ω d (sz.L n) (sz.W n), twL2M sz lam0 E n (u + Δ) (M + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂
          ∂(PF d (sz.L n) (sz.W n) 0)) - twL2M sz lam0 E n u M σ a c₁ c₂ - (Δ : ℂ) * twGenM sz lam0 E n u M σ a c₁ c₂‖ ≤
      10000 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 * (1 + (etaOf (BAmF sz lam0 E n) (u + Δ))⁻¹) ^ 6 * Δ ^ ((3 : ℝ) / 2) := by
  have hlen : (TwistGridRem_word σ).length = 2 := rfl
  have h := TwistGridRem_envelope_word (g := 0) (Ei := TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂) (l := TwistGridRem_word σ)
    (TwistGridRem_letters_norm sz n a c₁ c₂) hm hmn (E n) hu hΔ hu1 hM
  rw [hlen] at h
  have e1 : (∫ ω : Ω d (sz.L n) (sz.W n), twL2M sz lam0 E n (u + Δ) (M + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂
          ∂(PF d (sz.L n) (sz.W n) 0)) = ∫ ω : Ω d (sz.L n) (sz.W n), TwistGridRem_F (TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂)
          (TwistGridRem_word σ) (blockMat d (sz.L n) (sz.W n) (M + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) ω))
          (ztOf (BAmF sz lam0 E n) (E n) (u + Δ)) ∂(PF d (sz.L n) (sz.W n) 0) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => TwistGridRem_twL2M_eq sz lam0 E n
      (OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d (sz.L n) (sz.W n) ω) _) _ σ a c₁ c₂)
  rw [e1, TwistGridRem_twL2M_eq sz lam0 E n hM u σ a c₁ c₂, TwistGridRem_twGenM_eq sz lam0 E n hM hm (by linarith) σ a c₁ c₂]
  refine h.trans (le_of_eq ?_)
  norm_num

end Twisted

/-! ## 7. The Taylor bound of `K̃` (the exact resolvent identity, no second derivative) -/

section KTaylor

open scoped Matrix.Norms.Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- `Θ_{u+Δ} - Θ_u - Δ Θ_u Q Θ_u = Δ² Θ_{u+Δ} Q Θ_u Q Θ_u` (`Θ_t = (1 - tQ)⁻¹`, `Q = M^{(σ₁σ₂)}`). -/
private theorem TwistGridRem_theta_taylor {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {u Δ : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u + Δ < 1) (hΔ : 0 ≤ Δ) (σ₁ σ₂ : Bool) :
    BATheta d L g E m (u + Δ) σ₁ σ₂ - BATheta d L g E m u σ₁ σ₂ - (Δ : ℂ) • (BATheta d L g E m u σ₁ σ₂ *
        BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m u σ₁ σ₂) =
      ((Δ : ℂ) ^ 2) • (BATheta d L g E m (u + Δ) σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ *
        BATheta d L g E m u σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m u σ₁ σ₂) := by
  have h1 := BATheta_resolvent d L g κ E m hr u hu0 (by linarith) σ₁ σ₂
  have h2 := BATheta_resolvent d L g κ E m hr (u + Δ) (by linarith) hu1 σ₁ σ₂
  set Θ := BATheta d L g E m u σ₁ σ₂
  set Θ' := BATheta d L g E m (u + Δ) σ₁ σ₂
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂
  have hl : Θ - (u : ℂ) • (Q * Θ) = 1 := by rw [sub_eq_iff_eq_add]; exact h1.1
  have hr' : Θ' - ((u + Δ : ℝ) : ℂ) • (Θ' * Q) = 1 := by rw [sub_eq_iff_eq_add]; exact h2.2
  have key : Θ' - Θ = (Δ : ℂ) • (Θ' * Q * Θ) := by
    calc Θ' - Θ = Θ' * (Θ - (u : ℂ) • (Q * Θ)) - (Θ' - ((u + Δ : ℝ) : ℂ) • (Θ' * Q)) * Θ := by
          rw [hl, hr', mul_one, one_mul]
      _ = (Δ : ℂ) • (Θ' * Q * Θ) := by
          simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_assoc]
          push_cast
          module
  have key2 : Θ' - Θ - (Δ : ℂ) • (Θ * Q * Θ) = (Δ : ℂ) • ((Θ' - Θ) * Q * Θ) := by
    simp only [sub_mul, smul_sub]
    rw [key]
  rw [key2, key]
  simp only [smul_mul_assoc, smul_smul, Matrix.mul_assoc, pow_two]

/-- `Z ↦ W^{-d} Σ_{a'} Z(a,a') M(σ₁)_{c₂a'} M(σ₂)_{a'c₁}`: the functional by which `K̃` is built from `Θ`. -/
private def TwistGridRem_S (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (Z : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n), Z a a' *
    BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
    BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁

private theorem TwistGridRem_S_sub (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (Z₁ Z₂ : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) :
    TwistGridRem_S sz lam0 E n σ a c₁ c₂ (Z₁ - Z₂) = TwistGridRem_S sz lam0 E n σ a c₁ c₂ Z₁ - TwistGridRem_S sz lam0 E n σ a c₁ c₂ Z₂ := by
  simp only [TwistGridRem_S, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

private theorem TwistGridRem_S_smul (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (c : ℂ) (Z : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) :
    TwistGridRem_S sz lam0 E n σ a c₁ c₂ (c • Z) = c * TwistGridRem_S sz lam0 E n σ a c₁ c₂ Z := by
  simp only [TwistGridRem_S, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  ring

private theorem TwistGridRem_S_norm_le {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (σ : Fin 2 → Bool)
    (a c₁ c₂ : Zd d (sz.L n)) (Z : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) : ‖TwistGridRem_S sz lam0 E n σ a c₁ c₂ Z‖ ≤ ‖Z‖ := by
  unfold TwistGridRem_S
  have hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
  have hsum : ‖∑ a' : Zd d (sz.L n), Z a a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁‖ ≤ ‖Z‖ := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a' _ => ?_).trans (sum_norm_row_le Z a))
    rw [norm_mul, norm_mul]
    have h0 := TwistPins_M_le_one hr (σ 0) c₂ a'
    have h1 := TwistPins_M_le_one hr (σ 1) a' c₁
    calc ‖Z a a'‖ * ‖BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a'‖ *
          ‖BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁‖ ≤ ‖Z a a'‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h0 (norm_nonneg _)) h1 (norm_nonneg _) (by positivity)
      _ = ‖Z a a'‖ := by ring
  rw [norm_mul]
  have hn : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ ≤ 1 := by simpa using hW
  calc ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ * ‖_‖ ≤ 1 * ‖Z‖ := mul_le_mul hn hsum (norm_nonneg _) zero_le_one
    _ = ‖Z‖ := one_mul _

/-- The Taylor bound of `K̃` in the grid step: `‖K̃_{u+Δ} - K̃_u - Δ ∂_u K̃_u‖ ≤ (1 - u - Δ)^{-3} Δ²` for `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1`, `BAReal`
(`Θ_{u+Δ} - Θ_u - ΔΘ_uQΘ_u = Δ²Θ_{u+Δ}QΘ_uQΘ_u`, `‖Θ_v‖ ≤ (1 - v)⁻¹`, `‖Q‖ ≤ 1`, `|M(σ)_{xy}| ≤ 1`, `W^{-d} ≤ 1`; every `d`). -/
theorem TwistGridRem_twK_taylor {κ : ℝ} (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n))
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1) :
    ‖twK (baFM sz lam0 E) n (u + Δ) σ a c₁ c₂ - twK (baFM sz lam0 E) n u σ a c₁ c₂ -
        (Δ : ℂ) * deriv (fun v : ℝ => twK (baFM sz lam0 E) n v σ a c₁ c₂) u‖ ≤ ((1 - (u + Δ))⁻¹) ^ 3 * Δ ^ 2 := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hu1' : u < 1 := by linarith
  have hd := (TwistGrid_hasDerivAt_twK sz lam0 E n hκ hr hu0 hu1' σ a c₁ c₂).deriv
  rw [hd, TwistGrid_twK_eq sz lam0 E n hm (u + Δ) σ a c₁ c₂, TwistGrid_twK_eq sz lam0 E n hm u σ a c₁ c₂]
  set Θ := BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) with hΘ
  set Θ' := BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (u + Δ) (σ 0) (σ 1) with hΘ'
  set Q := BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) with hQ
  have hX := TwistGridRem_theta_taylor hr hu0 hu1 hΔ (σ 0) (σ 1)
  have e : ∀ Z : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ, TwistGridRem_S sz lam0 E n σ a c₁ c₂ Z =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n), Z a a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁ := fun Z => rfl
  have hS : (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n), Θ' a a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁ -
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n), Θ a a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁ -
      (Δ : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n), (Θ * Q * Θ) a a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁) =
      TwistGridRem_S sz lam0 E n σ a c₁ c₂ (((Δ : ℂ) ^ 2) • (Θ' * Q * Θ * Q * Θ)) := by
    rw [← hX, TwistGridRem_S_sub, TwistGridRem_S_sub, TwistGridRem_S_smul]
    rfl
  rw [hS]
  refine (TwistGridRem_S_norm_le sz lam0 E n hr σ a c₁ c₂ _).trans ?_
  have hc : ‖((Δ : ℂ) ^ 2)‖ = Δ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hΔ]
  have hΘn : ‖Θ‖ ≤ (1 - u)⁻¹ := EKPins_norm_Theta_le hr hu0 hu1' (σ 0) (σ 1)
  have hΘ'n : ‖Θ'‖ ≤ (1 - (u + Δ))⁻¹ := EKPins_norm_Theta_le hr (by linarith) hu1 (σ 0) (σ 1)
  have hQn : ‖Q‖ ≤ 1 := EKPins_norm_Q_le hr (σ 0) (σ 1)
  have hinv : (1 - u)⁻¹ ≤ (1 - (u + Δ))⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have h1u : 0 < 1 - (u + Δ) := by linarith
  have hY : ‖Θ' * Q * Θ * Q * Θ‖ ≤ ((1 - (u + Δ))⁻¹) ^ 3 := by
    calc ‖Θ' * Q * Θ * Q * Θ‖ ≤ ‖Θ'‖ * ‖Q‖ * ‖Θ‖ * ‖Q‖ * ‖Θ‖ := by
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 - (u + Δ))⁻¹ * 1 * (1 - (u + Δ))⁻¹ * 1 * (1 - (u + Δ))⁻¹ := by
          have hp : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.2 h1u.le
          have hΘ2 : ‖Θ‖ ≤ (1 - (u + Δ))⁻¹ := hΘn.trans hinv
          gcongr
      _ = ((1 - (u + Δ))⁻¹) ^ 3 := by ring
  rw [norm_smul, hc]
  calc Δ ^ 2 * ‖Θ' * Q * Θ * Q * Θ‖ ≤ Δ ^ 2 * ((1 - (u + Δ))⁻¹) ^ 3 := mul_le_mul_of_nonneg_left hY (sq_nonneg Δ)
    _ = _ := mul_comm _ _

end KTaylor

/-! ## 8. The one-step bound at a Hermitian matrix: `‖E A_{u+Δ}(M + √Δ X) - A_u(M) - Δ Drift_u(M)‖ ≤ Z₁ Δ^{3/2} + Z₂ Δ²` -/

section Step

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- `L̃(M + τ X)` is integrable over the Gaussian law (continuous and bounded). -/
theorem TwistGridRem_integrable_twL2M (hm : 0 < (BAmF sz lam0 E n).im) {v : ℝ} (hv : v < 1) (σ : Fin 2 → Bool)
    (a c₁ c₂ : Zd d (sz.L n)) (g : ℝ) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    (τ : ℝ) :
    Integrable (fun ω : Ω d (sz.L n) (sz.W n) => twL2M sz lam0 E n v (M + (τ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂)
      (PF d (sz.L n) (sz.W n) g) := by
  have hz : (ztOf (BAmF sz lam0 E n) (E n) v).im ≠ 0 := by
    rw [ztOf_im]
    exact (TwistGridRem_eta_pos hm hv).ne'
  have hη : 0 < |(ztOf (BAmF sz lam0 E n) (E n) v).im| := abs_pos.mpr hz
  have hherm : ∀ ω : Ω d (sz.L n) (sz.W n), (M + (τ : ℂ) • Xmat d (sz.L n) (sz.W n) ω).IsHermitian := fun ω =>
    OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d (sz.L n) (sz.W n) ω) τ
  have hfun : (fun ω : Ω d (sz.L n) (sz.W n) => twL2M sz lam0 E n v (M + (τ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂) =
      fun ω => TwistGridRem_F (TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂) (TwistGridRem_word σ)
        (blockMat d (sz.L n) (sz.W n) (M + (τ : ℂ) • Xmat d (sz.L n) (sz.W n) ω)) (ztOf (BAmF sz lam0 E n) (E n) v) :=
    funext fun ω => TwistGridRem_twL2M_eq sz lam0 E n (hherm ω) v σ a c₁ c₂
  rw [hfun]
  refine Integrable.of_bound ?_ _ (Filter.Eventually.of_forall fun ω =>
    TwistGridRem_norm_F_le (TwistGridRem_letters_norm sz n a c₁ c₂) ((hherm ω).submatrix _) hη le_rfl)
  exact (TwistGridRem_continuous_F (f := fun ω : Ω d (sz.L n) (sz.W n) => blockMat d (sz.L n) (sz.W n) (M + (τ : ℂ) • Xmat d (sz.L n) (sz.W n) ω))
    (OneStep_continuous_blockMat.comp (continuous_const.add ((continuous_Xmat d (sz.L n) (sz.W n)).const_smul (τ : ℂ))))
    (fun ω => (hherm ω).submatrix _) hz).aestronglyMeasurable

/-- The one-step bound (the twisted analogue of the deterministic content of `condExp_loop_drift`): for Hermitian `M`, `A_v(M) = L̃_v(M) - K̃_v`, `Drift = twDriftM`
(`BATwistHier_holds`), `‖E A_{u+Δ}(M + √Δ X) - A_u(M) - Δ Drift_u(M)‖ ≤ 10⁴ N⁴ (1 + η⁻¹)⁶ Δ^{3/2} + (1 - u - Δ)^{-3} Δ²`, `η = (1 - u - Δ) Im m_F`. -/
theorem TwistGridRem_step {κ : ℝ} (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hg : 0 < lam0 n)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) {u Δ : ℝ} (hu : 0 ≤ u) (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    ‖(∫ ω : Ω d (sz.L n) (sz.W n), (twL2M sz lam0 E n (u + Δ) (M + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂ -
          twK (baFM sz lam0 E) n (u + Δ) σ a c₁ c₂) ∂(PF d (sz.L n) (sz.W n) 0)) -
        (twL2M sz lam0 E n u M σ a c₁ c₂ - twK (baFM sz lam0 E) n u σ a c₁ c₂) -
        (Δ : ℂ) * twDriftM sz lam0 E n u M σ a c₁ c₂‖ ≤
      10000 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 * (1 + (etaOf (BAmF sz lam0 E n) (u + Δ))⁻¹) ^ 6 * Δ ^ ((3 : ℝ) / 2) +
        ((1 - (u + Δ))⁻¹) ^ 3 * Δ ^ 2 := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hmn : ‖BAmF sz lam0 E n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (lam0 n) ((E n : ℝ) : ℂ) (BAmF sz lam0 E n) (by simp) hr.1
  have hu1' : u < 1 := by linarith
  have hint := TwistGridRem_integrable_twL2M sz lam0 E n hm (show u + Δ < 1 from hu1) σ a c₁ c₂ 0 hM (Real.sqrt Δ)
  have hI : (∫ ω : Ω d (sz.L n) (sz.W n), (twL2M sz lam0 E n (u + Δ) (M + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂ -
          twK (baFM sz lam0 E) n (u + Δ) σ a c₁ c₂) ∂(PF d (sz.L n) (sz.W n) 0)) =
      (∫ ω : Ω d (sz.L n) (sz.W n), twL2M sz lam0 E n (u + Δ) (M + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂
          ∂(PF d (sz.L n) (sz.W n) 0)) - twK (baFM sz lam0 E) n (u + Δ) σ a c₁ c₂ := by
    rw [integral_sub hint (integrable_const _)]
    simp
  have hH := BATwistHier_holds d sz lam0 E n κ hκ hg hr u hu hu1' M hM σ a c₁ c₂
  have h1 := TwistGridRem_envelope sz lam0 E n hm hmn σ a c₁ c₂ hu hΔ hu1 hM
  have h2 := TwistGridRem_twK_taylor sz lam0 E n hκ hr σ a c₁ c₂ hu hΔ hu1
  have e : (∫ ω : Ω d (sz.L n) (sz.W n), (twL2M sz lam0 E n (u + Δ) (M + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂ -
          twK (baFM sz lam0 E) n (u + Δ) σ a c₁ c₂) ∂(PF d (sz.L n) (sz.W n) 0)) -
        (twL2M sz lam0 E n u M σ a c₁ c₂ - twK (baFM sz lam0 E) n u σ a c₁ c₂) -
        (Δ : ℂ) * twDriftM sz lam0 E n u M σ a c₁ c₂ =
      ((∫ ω : Ω d (sz.L n) (sz.W n), twL2M sz lam0 E n (u + Δ) (M + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) ω) σ a c₁ c₂
          ∂(PF d (sz.L n) (sz.W n) 0)) - twL2M sz lam0 E n u M σ a c₁ c₂ - (Δ : ℂ) * twGenM sz lam0 E n u M σ a c₁ c₂) -
      (twK (baFM sz lam0 E) n (u + Δ) σ a c₁ c₂ - twK (baFM sz lam0 E) n u σ a c₁ c₂ -
        (Δ : ℂ) * deriv (fun v : ℝ => twK (baFM sz lam0 E) n v σ a c₁ c₂) u) := by
    rw [hI, ← hH]
    ring
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

end Step

end RBM.BA
