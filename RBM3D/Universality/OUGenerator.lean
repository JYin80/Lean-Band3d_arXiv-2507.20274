/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.OU
import RBM3D.Universality.OUHessian
import RBM3D.Gauss.SteinMatrix
import RBM3D.Gauss.DominationAt
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The OU generator identity (T2261, UN-15)

The second-order Gaussian interpolation identity behind `(EMCTE2)` (RBM2D paper `1-2:333–341, 364–369`),

  `d/dt E Φ(𝐇_t) = -½ e^{-t} ∑_{ab} S°_{ab} E ∂_{ab}∂_{ba} Φ(𝐇_t)`,

for `𝐇_t = e^{-t/2} H + √(1 - e^{-t}) H'`, `S°_{ab} = centeredVarianceEntry d L W g a b = svarF - N⁻¹`, and test
functions `Φ` that are `C²` near every Hermitian matrix with value and first two Fréchet derivatives bounded
on Hermitian matrices (`TestFunH`).  No pin is proved or stated.

Port of RBM2D `Universality/OUGenerator.lean` (commit `c9a24cf`, 1223 lines) to `Idx d L W`, `svarF d L W g`,
`N = (W L)^d`, with these changes:

* the RBM2D proof (Stein's identity for each of the two independent Gaussian fields under Fubini) is ported on
  the **pair carrier** `ouPairP d L W g = PF d L W g ⊗ gueP d L W` on `Ω d L W × Ω d L W`, with
  `ouPairMat d L W t ω = e^{-t/2} X(ω.1) + √(1 - e^{-t}) X(ω.2)` (targets P1, P2: every `g`, every `d`);
* it is transferred to the merged model-generic carrier `ouP (UNModel.band sz) n` by the push-forward along
  `Prod.map (slice sz n) id` (T1 `ouMat_band_eq_ouPairMat`, T2 `ouP_band_map_pair`, the inner `this` of
  `ouSample_law`, `OU.lean:215-220`), giving the consumer forms B1, B2 (the RBM2D names
  `ouGenerator_hasDerivAt_integral`, `ouGenerator_integral_sub_eq`) at `g = sz.lam n`; band model only;
* `Idx L W` ↦ `Idx d L W`, `Coord L W` ↦ `CoordF d L W`, `Ω L W` ↦ `Ω d L W`, `P L W` ↦ `PF d L W g`,
  `gvar L W` ↦ `gvarF d L W g` (the diagonal/off-diagonal read-off is `rfl`), `svar` ↦ `svarF d L W g`,
  `RBM.Endpoints.gueVar L W` ↦ `RBM.Univ.gueVar d L W`, `RBM.Green.Bmat L W` ↦ `RBM.Green.Bmat d L W`,
  `usedCoords L W` ↦ `RBM.Gauss.usedCoords d L W`, `card_Idx_eq L W` ↦ `RBM.Gauss.card_Idx` (`(W * L)^d`);
* the merged `stieltjesN` is `Gres`-based: the RBM2D `green` unfoldings (section 9) go through
  `Gres H z true = Ring.inverse (H - z • 1)` by `simp [Gres]`, and `RBM.Gauss.norm_green_le` is replaced by
  the merged `norm_Gsig_le_inv_eta`; `isUnit_sub_smul_one_of_im_ne_zero` ↦ `RBM.Ind.…`;
* the instances are at `d = 3`, `L = 3`, `W = 2` (`N = 216`) and at `UNModel.band sz0`, in
  `RBM.Univ.OUGeneratorInst`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal
open scoped Matrix.Norms.L2Operator

section Defs

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- **Test functions for the OU generator identity** (RBM2D `TestFunH`, `OUGenerator.lean:57`,
`Idx L W` ↦ `Idx d L W`): `C²` near every Hermitian matrix, with the value and the first two Fréchet
derivatives bounded on Hermitian matrices. -/
def TestFunH (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) : Prop :=
  (∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ContDiffAt ℝ 2 Φ M) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖Φ M‖ ≤ C) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
    ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)

/-- The pair carrier (RBM2D `ouP L W = P ⊗ gueP`, `Universality/Pins.lean:53`), law
`PF d L W g ⊗ gueP d L W`. -/
def ouPairP (g : ℝ) : Measure (Ω d L W × Ω d L W) :=
  (PF d L W g).prod (gueP d L W)

/-- The OU matrix on the pair carrier (RBM2D `ouMat L W`, `Universality/Pins.lean:59`). -/
def ouPairMat (t : ℝ) (ω : Ω d L W × Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Real.exp (-t / 2) • Xmat d L W ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω.2

end Defs

private instance OUGenerator_isProbabilityMeasure_ouPairP (d L W : ℕ) [NeZero L] [NeZero W]
    (g : ℝ) : IsProbabilityMeasure (ouPairP d L W g) := by
  unfold ouPairP; infer_instance

private theorem OUGenerator_ouPairMat_isHermitian (d L W : ℕ) [NeZero L] [NeZero W] (t : ℝ)
    (z : Ω d L W × Ω d L W) : (ouPairMat d L W t z).IsHermitian :=
  ((Xmat_isHermitian d L W z.1).smul (IsSelfAdjoint.all _)).add
    ((Xmat_isHermitian d L W z.2).smul (IsSelfAdjoint.all _))

/-! ## 1. Calculus at Hermitian points -/

section Basic

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W] {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ}

private theorem OUGenerator_continuousAt_fderiv (h : TestFunH d L W Φ)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) : ContinuousAt (fderiv ℝ Φ) M :=
  ((h.1 M hM).fderiv_right (m := 1) (by norm_num)).continuousAt

private theorem OUGenerator_continuousAt_fderiv2 (h : TestFunH d L W Φ)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContinuousAt (fderiv ℝ (fderiv ℝ Φ)) M :=
  (((h.1 M hM).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
    (by norm_num)).continuousAt

private theorem OUGenerator_differentiableAt_fderiv (h : TestFunH d L W Φ)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    DifferentiableAt ℝ (fderiv ℝ Φ) M :=
  ((h.1 M hM).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- A function continuous at every Hermitian matrix, composed with a continuous map into the
Hermitian matrices, is continuous. -/
private theorem OUGenerator_continuous_comp {α E : Type*} [TopologicalSpace α]
    [TopologicalSpace E] {F : Matrix (Idx d L W) (Idx d L W) ℂ → E}
    (hF : ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ContinuousAt F M)
    {f : α → Matrix (Idx d L W) (Idx d L W) ℂ} (hf : Continuous f) (hherm : ∀ a, (f a).IsHermitian) :
    Continuous fun a => F (f a) :=
  continuous_iff_continuousAt.2 fun a => (hF _ (hherm a)).comp hf.continuousAt

private theorem OUGenerator_continuous_Phi (h : TestFunH d L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx d L W) (Idx d L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) : Continuous fun a => Φ (f a) :=
  OUGenerator_continuous_comp (fun M hM => (h.1 M hM).continuousAt) hf hherm

private theorem OUGenerator_continuous_coordD1 (h : TestFunH d L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx d L W) (Idx d L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (p : CoordF d L W) :
    Continuous fun a => coordD1 d L W Φ (f a) p :=
  (OUGenerator_continuous_comp (fun M hM => OUGenerator_continuousAt_fderiv h hM) hf
    hherm).clm_apply continuous_const

private theorem OUGenerator_continuous_coordD2 (h : TestFunH d L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx d L W) (Idx d L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (p : CoordF d L W) :
    Continuous fun a => coordD2 d L W Φ (f a) p :=
  ((OUGenerator_continuous_comp (fun M hM => OUGenerator_continuousAt_fderiv2 h hM) hf
    hherm).clm_apply continuous_const).clm_apply continuous_const

private theorem OUGenerator_norm_coordD1_le {C : ℝ}
    (hC : ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (p : CoordF d L W) :
    ‖coordD1 d L W Φ M p‖ ≤ C * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ Φ M).le_opNorm _) (mul_le_mul_of_nonneg_right (hC M hM) (norm_nonneg _))

private theorem OUGenerator_norm_coordD2_le {C : ℝ}
    (hC : ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (p : CoordF d L W) :
    ‖coordD2 d L W Φ M p‖
      ≤ C * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat d L W p.1 p.2.1 p.2.2)).le_opNorm _)
    (mul_le_mul_of_nonneg_right
      (le_trans ((fderiv ℝ (fderiv ℝ Φ) M).le_opNorm _)
        (mul_le_mul_of_nonneg_right (hC M hM) (norm_nonneg _))) (norm_nonneg _))

/-- Differentiating `M ↦ fderiv ℝ Φ M A` in `M`, where `fderiv ℝ Φ` is differentiable. -/
private theorem OUGenerator_hasFDerivAt_fderiv_apply {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (h : DifferentiableAt ℝ (fderiv ℝ Φ) M) (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    HasFDerivAt (fun M' => fderiv ℝ Φ M' A) ((fderiv ℝ (fderiv ℝ Φ) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- The first derivative of `Φ` in the direction `Xmat ω` is the coordinate sum of the
directional derivatives. -/
private theorem OUGenerator_fderiv_apply_Xmat (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (ω : Ω d L W) :
    fderiv ℝ Φ M (Xmat d L W ω) = ∑ p ∈ usedCoords d L W, ω p • coordD1 d L W Φ M p := by
  conv_lhs => rw [RBM.Green.Xmat_eq_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

end Basic


/-! ## 2. The interpolation coefficients and the pointwise chain rule -/

section Chain

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `d/dt e^{-t/2}`. -/
private def OUGenerator_aC (x : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.exp (-x / 2)

/-- `d/dt √(1 - e^{-t})`. -/
private def OUGenerator_bC (x : ℝ) : ℝ := Real.exp (-x) / (2 * Real.sqrt (1 - Real.exp (-x)))

/-- The band-field coordinate sum `∑_p ω₁_p ∂_p Φ(𝐇_x(ω))`. -/
private def OUGenerator_S1 (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (x : ℝ)
    (z : Ω d L W × Ω d L W) : ℂ :=
  ∑ p ∈ usedCoords d L W, z.1 p • coordD1 d L W Φ (ouPairMat d L W x z) p

/-- The GUE-field coordinate sum `∑_p ω₂_p ∂_p Φ(𝐇_x(ω))`. -/
private def OUGenerator_S2 (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (x : ℝ)
    (z : Ω d L W × Ω d L W) : ℂ :=
  ∑ p ∈ usedCoords d L W, z.2 p • coordD1 d L W Φ (ouPairMat d L W x z) p

/-- The pointwise `t`-derivative of `Φ (𝐇_t(ω))`. -/
private def OUGenerator_dF (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (x : ℝ)
    (z : Ω d L W × Ω d L W) : ℂ :=
  OUGenerator_aC x • OUGenerator_S1 d L W Φ x z + OUGenerator_bC x • OUGenerator_S2 d L W Φ x z

end Chain

private theorem OUGenerator_hasDerivAt_band (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (OUGenerator_aC t) t := by
  unfold OUGenerator_aC
  have hg : HasDerivAt (fun s : ℝ => -s / 2) (-(1 / 2 : ℝ)) t := by
    have h := (hasDerivAt_id t).neg.div_const (2 : ℝ)
    norm_num at h
    convert h using 1
  have h2 := hg.exp
  rw [mul_comm] at h2
  exact h2

private theorem OUGenerator_hasDerivAt_zeta (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - Real.exp (-s)) (Real.exp (-t)) t := by
  have hg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := (hasDerivAt_id t).neg
  have h2 := hg.exp
  have h3 := h2.const_sub (1 : ℝ)
  simp only [mul_neg_one, neg_neg] at h3
  exact h3

private theorem OUGenerator_zeta_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

private theorem OUGenerator_hasDerivAt_gue {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-s))) (OUGenerator_bC t) t :=
  (OUGenerator_hasDerivAt_zeta t).sqrt (OUGenerator_zeta_pos ht).ne'

section Chain2

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W] {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ}

/-- **The pointwise `t`-derivative of `Φ` along the OU interpolation.** -/
private theorem OUGenerator_hasDerivAt_pointwise (h : TestFunH d L W Φ) (z : Ω d L W × Ω d L W)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Φ (ouPairMat d L W s z)) (OUGenerator_dF d L W Φ t z) t := by
  have hM : HasDerivAt (fun s : ℝ => ouPairMat d L W s z)
      (OUGenerator_aC t • Xmat d L W z.1 + OUGenerator_bC t • Xmat d L W z.2) t :=
    ((OUGenerator_hasDerivAt_band t).smul_const (Xmat d L W z.1)).add
      ((OUGenerator_hasDerivAt_gue ht).smul_const (Xmat d L W z.2))
  have key := ((h.1 _ (OUGenerator_ouPairMat_isHermitian d L W t z)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hM
  rw [map_add, map_smul, map_smul, OUGenerator_fderiv_apply_Xmat,
    OUGenerator_fderiv_apply_Xmat] at key
  exact key

end Chain2

/-! ## 3. Integrability of the coordinates, continuity of `ouMat` -/

section Integrability

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

private theorem OUGenerator_integrable_coord (v : CoordF d L W → ℝ≥0) (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => ω c) (Measure.infinitePi fun c => gaussianReal 0 (v c)) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c)
      (Measure.infinitePi fun c => gaussianReal 0 (v c)) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x)
      ((Measure.infinitePi fun c => gaussianReal 0 (v c)).map fun ω => ω c) := by
    rw [Measure.infinitePi_map_eval]
    exact RBM.integrable_id_gaussianReal
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem OUGenerator_integrable_fst (c : CoordF d L W) :
    Integrable (fun z : Ω d L W × Ω d L W => z.1 c) (ouPairP d L W g) :=
  (OUGenerator_integrable_coord (gvarF d L W g) c).comp_fst (gueP d L W)

private theorem OUGenerator_integrable_snd (c : CoordF d L W) :
    Integrable (fun z : Ω d L W × Ω d L W => z.2 c) (ouPairP d L W g) :=
  (OUGenerator_integrable_coord (gueVar d L W) c).comp_snd (PF d L W g)

private theorem OUGenerator_continuous_ouPairMat (s : ℝ) :
    Continuous fun z : Ω d L W × Ω d L W => ouPairMat d L W s z :=
  (((continuous_Xmat d L W).comp continuous_fst).const_smul (Real.exp (-s / 2))).add
    (((continuous_Xmat d L W).comp continuous_snd).const_smul (Real.sqrt (1 - Real.exp (-s))))

end Integrability

/-! ## 4. Differentiating under the joint integral -/

section Dominated

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W] {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ}

private theorem OUGenerator_abs_aC_le {x : ℝ} (hx : 0 ≤ x) : |OUGenerator_aC x| ≤ 1 / 2 := by
  unfold OUGenerator_aC
  have he1 : Real.exp (-x / 2) ≤ 1 := by
    have : -x / 2 ≤ 0 := by linarith
    exact Real.exp_le_one_iff.mpr this
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    abs_of_pos (Real.exp_pos _)]
  nlinarith [Real.exp_pos (-x / 2)]

private theorem OUGenerator_abs_bC_le {t x : ℝ} (ht : 0 < t / 2) (hx : t / 2 < x) :
    |OUGenerator_bC x| ≤ Real.exp (-(t / 2)) / (2 * Real.sqrt (1 - Real.exp (-(t / 2)))) := by
  have hzt2 : 0 < 1 - Real.exp (-(t / 2)) := OUGenerator_zeta_pos ht
  have hzx : 0 < 1 - Real.exp (-x) := OUGenerator_zeta_pos (lt_trans ht hx)
  have hexp : Real.exp (-x) ≤ Real.exp (-(t / 2)) := Real.exp_le_exp.mpr (by linarith)
  have hmono : 1 - Real.exp (-(t / 2)) ≤ 1 - Real.exp (-x) := by linarith
  unfold OUGenerator_bC
  rw [abs_of_pos (by positivity)]
  gcongr

/-- The norm bound for the two coordinate sums. -/
private theorem OUGenerator_norm_S1_le {C₁ : ℝ}
    (hC₁ : ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C₁)
    (x : ℝ) (z : Ω d L W × Ω d L W) :
    ‖OUGenerator_S1 d L W Φ x z‖ ≤ ∑ p ∈ usedCoords d L W,
      |z.1 p| * (C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (OUGenerator_norm_coordD1_le hC₁ (OUGenerator_ouPairMat_isHermitian d L W x z) p) (abs_nonneg _)

private theorem OUGenerator_norm_S2_le {C₁ : ℝ}
    (hC₁ : ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C₁)
    (x : ℝ) (z : Ω d L W × Ω d L W) :
    ‖OUGenerator_S2 d L W Φ x z‖ ≤ ∑ p ∈ usedCoords d L W,
      |z.2 p| * (C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (OUGenerator_norm_coordD1_le hC₁ (OUGenerator_ouPairMat_isHermitian d L W x z) p) (abs_nonneg _)

private theorem OUGenerator_continuous_S1 (h : TestFunH d L W Φ) (x : ℝ) :
    Continuous fun z : Ω d L W × Ω d L W => OUGenerator_S1 d L W Φ x z :=
  continuous_finsetSum _ fun p _ => ((continuous_apply p).comp continuous_fst).smul
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouPairMat x)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W x z) p)

private theorem OUGenerator_continuous_S2 (h : TestFunH d L W Φ) (x : ℝ) :
    Continuous fun z : Ω d L W × Ω d L W => OUGenerator_S2 d L W Φ x z :=
  continuous_finsetSum _ fun p _ => ((continuous_apply p).comp continuous_snd).smul
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouPairMat x)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W x z) p)

private theorem OUGenerator_integrable_S1 (h : TestFunH d L W Φ) (x : ℝ) :
    Integrable (fun z : Ω d L W × Ω d L W => OUGenerator_S1 d L W Φ x z) (ouPairP d L W g) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  refine integrable_finsetSum _ fun p _ => ?_
  exact (OUGenerator_integrable_fst p).smul_bdd (C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖)
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouPairMat x)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W x z) p).aestronglyMeasurable
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD1_le hC₁ (OUGenerator_ouPairMat_isHermitian d L W x z) p)

private theorem OUGenerator_integrable_S2 (h : TestFunH d L W Φ) (x : ℝ) :
    Integrable (fun z : Ω d L W × Ω d L W => OUGenerator_S2 d L W Φ x z) (ouPairP d L W g) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  refine integrable_finsetSum _ fun p _ => ?_
  exact (OUGenerator_integrable_snd p).smul_bdd (C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖)
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouPairMat x)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W x z) p).aestronglyMeasurable
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD1_le hC₁ (OUGenerator_ouPairMat_isHermitian d L W x z) p)

/-- **The generator identity, joint-integral form, before Stein.**  Differentiation under the
integral sign over `ouPairP d L W g`, dominated on `Set.Ioi (t/2)` (the coefficient `√(1 - e^{-t})` has a
square-root singularity at `0`, hence `t > 0` and the `t/2` margin). -/
private theorem OUGenerator_hasDerivAt_integral_joint (h : TestFunH d L W Φ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ z, Φ (ouPairMat d L W s z) ∂(ouPairP d L W g))
      (∫ z, OUGenerator_dF d L W Φ t z ∂(ouPairP d L W g)) t := by
  obtain ⟨C₀, hC₀⟩ := h.2.1
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  have ht2 : 0 < t / 2 := by linarith
  have hcontF : ∀ x : ℝ, Continuous fun z : Ω d L W × Ω d L W => Φ (ouPairMat d L W x z) :=
    fun x => OUGenerator_continuous_Phi h (OUGenerator_continuous_ouPairMat x)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W x z)
  have hcontdF : ∀ x : ℝ, Continuous fun z : Ω d L W × Ω d L W => OUGenerator_dF d L W Φ x z :=
    fun x => ((OUGenerator_continuous_S1 h x).const_smul (OUGenerator_aC x)).add
      ((OUGenerator_continuous_S2 h x).const_smul (OUGenerator_bC x))
  set B1 : ℝ := Real.exp (-(t / 2)) / (2 * Real.sqrt (1 - Real.exp (-(t / 2)))) with hB1
  set bound : Ω d L W × Ω d L W → ℝ := fun z =>
    (1 / 2 : ℝ) * (∑ p ∈ usedCoords d L W,
        |z.1 p| * (C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖))
      + B1 * (∑ p ∈ usedCoords d L W,
        |z.2 p| * (C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖)) with hbound_def
  have hbound : ∀ᵐ z ∂(ouPairP d L W g), ∀ x ∈ Set.Ioi (t / 2),
      ‖OUGenerator_dF d L W Φ x z‖ ≤ bound z := by
    refine Eventually.of_forall fun z x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := by
      have : t / 2 < x := hx
      linarith
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (OUGenerator_abs_aC_le hx0) (OUGenerator_norm_S1_le hC₁ x z)
        (norm_nonneg _) (by norm_num)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (OUGenerator_abs_bC_le ht2 hx) (OUGenerator_norm_S2_le hC₁ x z)
        (norm_nonneg _) (by positivity)
  have hbndint : Integrable bound (ouPairP d L W g) := by
    refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
    · exact integrable_finsetSum _ fun p _ => (OUGenerator_integrable_fst p).abs.mul_const _
    · exact integrable_finsetSum _ fun p _ => (OUGenerator_integrable_snd p).abs.mul_const _
  have hdiff : ∀ᵐ z ∂(ouPairP d L W g), ∀ x ∈ Set.Ioi (t / 2),
      HasDerivAt (fun s : ℝ => Φ (ouPairMat d L W s z)) (OUGenerator_dF d L W Φ x z) x :=
    Eventually.of_forall fun z x hx => OUGenerator_hasDerivAt_pointwise h z (lt_trans ht2 hx)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ouPairP d L W g) (𝕜 := ℝ)
    (F := fun (s : ℝ) (z : Ω d L W × Ω d L W) => Φ (ouPairMat d L W s z))
    (F' := fun (s : ℝ) (z : Ω d L W × Ω d L W) => OUGenerator_dF d L W Φ s z)
    (x₀ := t) (s := Set.Ioi (t / 2))
    (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall fun x => (hcontF x).aestronglyMeasurable)
    ((memLp_top_of_bound (hcontF t).aestronglyMeasurable C₀
      (Eventually.of_forall fun z => hC₀ _ (OUGenerator_ouPairMat_isHermitian d L W t z))).integrable le_top)
    (hcontdF t).aestronglyMeasurable hbound hbndint hdiff).2

end Dominated

/-! ## 5. Stein's identity for each field, under Fubini -/

section Stein

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W] {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ}

private theorem OUGenerator_isHermitian_shift {Y : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hY : Y.IsHermitian) (a : ℝ) (ω : Ω d L W) : (Y + a • Xmat d L W ω).IsHermitian :=
  hY.add ((Xmat_isHermitian d L W ω).smul (IsSelfAdjoint.all _))

/-- **The coordinate derivative of `coordD1` along a shifted scalar-linear line.**  Moving the
Gaussian coordinate `p` of `ω` moves the matrix argument along `a • Bmat p`; this is where
Stein's identity turns a coordinate value into a second derivative. -/
private theorem OUGenerator_hasDerivAt_coordD1_shift (h : TestFunH d L W Φ)
    (Y : Matrix (Idx d L W) (Idx d L W) ℂ) (hY : Y.IsHermitian) (a : ℝ) (ω : Ω d L W)
    {p : CoordF d L W} (hp : p ∈ usedCoords d L W) :
    HasDerivAt
      (fun t : ℝ => coordD1 d L W Φ (Y + a • Xmat d L W (Function.update ω p t)) p)
      (a • coordD2 d L W Φ (Y + a • Xmat d L W ω) p) (ω p) := by
  set B := RBM.Green.Bmat d L W p.1 p.2.1 p.2.2 with hB
  have hline : ∀ t : ℝ, Y + a • Xmat d L W (Function.update ω p t)
      = (Y + a • Xmat d L W ω) + (a * (t - ω p)) • B := by
    intro t
    rw [RBM.Green.GreenDeriv_Xmat_update ω hp t, smul_add, smul_smul]
    abel
  have hscal : HasDerivAt (fun t : ℝ => a * (t - ω p)) a (ω p) := by
    simpa using ((hasDerivAt_id (ω p)).sub_const (ω p)).const_mul a
  have hpath : HasDerivAt (fun t : ℝ => Y + a • Xmat d L W (Function.update ω p t))
      (a • B) (ω p) := by
    have h1 : HasDerivAt (fun t : ℝ => (Y + a • Xmat d L W ω) + (a * (t - ω p)) • B)
        (a • B) (ω p) := (hscal.smul_const B).const_add _
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun t => hline t)
  have hself : Y + a • Xmat d L W (Function.update ω p (ω p)) = Y + a • Xmat d L W ω := by
    rw [Function.update_eq_self]
  have hF : HasFDerivAt (fun M' => fderiv ℝ Φ M' B)
      ((fderiv ℝ (fderiv ℝ Φ) (Y + a • Xmat d L W ω)).flip B) (Y + a • Xmat d L W ω) :=
    OUGenerator_hasFDerivAt_fderiv_apply
      (OUGenerator_differentiableAt_fderiv h (OUGenerator_isHermitian_shift hY a ω)) B
  have hF' : HasFDerivAt (fun M' => fderiv ℝ Φ M' B)
      ((fderiv ℝ (fderiv ℝ Φ) (Y + a • Xmat d L W ω)).flip B)
      (Y + a • Xmat d L W (Function.update ω p (ω p))) := by
    rw [hself]; exact hF
  have key := hF'.comp_hasDerivAt (ω p) hpath
  have hval : ((fderiv ℝ (fderiv ℝ Φ) (Y + a • Xmat d L W ω)).flip B) (a • B)
      = a • coordD2 d L W Φ (Y + a • Xmat d L W ω) p := by
    rw [ContinuousLinearMap.flip_apply, map_smul]
    rfl
  rw [hval] at key
  exact key

/-- **Stein's identity for one Gaussian field, under a fixed Hermitian shift.** -/
private theorem OUGenerator_stein_shift (v : CoordF d L W → ℝ≥0) (h : TestFunH d L W Φ)
    (Y : Matrix (Idx d L W) (Idx d L W) ℂ) (hY : Y.IsHermitian) (a : ℝ) {p : CoordF d L W}
    (hp : p ∈ usedCoords d L W) :
    ∫ ω, ω p • coordD1 d L W Φ (Y + a • Xmat d L W ω) p ∂(GaussianProduct.law v)
      = (v p : ℝ) •
          ∫ ω, a • coordD2 d L W Φ (Y + a • Xmat d L W ω) p ∂(GaussianProduct.law v) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  obtain ⟨C₂, hC₂⟩ := h.2.2.2
  have hcont : Continuous fun ω : Ω d L W => Y + a • Xmat d L W ω :=
    continuous_const.add ((continuous_Xmat d L W).const_smul a)
  have hherm := OUGenerator_isHermitian_shift hY a
  exact GaussianProduct.stein v p
    (fun ω => coordD1 d L W Φ (Y + a • Xmat d L W ω) p)
    (fun ω => a • coordD2 d L W Φ (Y + a • Xmat d L W ω) p)
    (OUGenerator_continuous_coordD1 h hcont hherm p)
    ((OUGenerator_continuous_coordD2 h hcont hherm p).const_smul a)
    (fun ω => OUGenerator_hasDerivAt_coordD1_shift h Y hY a ω hp)
    ⟨C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖,
      fun ω => OUGenerator_norm_coordD1_le hC₁ (hherm ω) p⟩
    ⟨|a| * (C₂ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖),
      fun ω => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (OUGenerator_norm_coordD2_le hC₂ (hherm ω) p)
          (abs_nonneg _)⟩

private theorem OUGenerator_integrable_coordD2 (h : TestFunH d L W Φ) (x : ℝ) (p : CoordF d L W) :
    Integrable (fun z : Ω d L W × Ω d L W => coordD2 d L W Φ (ouPairMat d L W x z) p) (ouPairP d L W g) := by
  obtain ⟨C₂, hC₂⟩ := h.2.2.2
  exact (memLp_top_of_bound
    (OUGenerator_continuous_coordD2 h (OUGenerator_continuous_ouPairMat x)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W x z) p).aestronglyMeasurable
    (C₂ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖)
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD2_le hC₂ (OUGenerator_ouPairMat_isHermitian d L W x z) p)).integrable le_top

private theorem OUGenerator_integrable_term_fst (h : TestFunH d L W Φ) (x : ℝ) (p : CoordF d L W) :
    Integrable (fun z : Ω d L W × Ω d L W => z.1 p • coordD1 d L W Φ (ouPairMat d L W x z) p)
      (ouPairP d L W g) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  exact (OUGenerator_integrable_fst p).smul_bdd (C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖)
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouPairMat x)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W x z) p).aestronglyMeasurable
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD1_le hC₁ (OUGenerator_ouPairMat_isHermitian d L W x z) p)

private theorem OUGenerator_integrable_term_snd (h : TestFunH d L W Φ) (x : ℝ) (p : CoordF d L W) :
    Integrable (fun z : Ω d L W × Ω d L W => z.2 p • coordD1 d L W Φ (ouPairMat d L W x z) p)
      (ouPairP d L W g) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  exact (OUGenerator_integrable_snd p).smul_bdd (C₁ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖)
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouPairMat x)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W x z) p).aestronglyMeasurable
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD1_le hC₁ (OUGenerator_ouPairMat_isHermitian d L W x z) p)

/-- **The band-field Stein identity, at the level of the joint measure.** -/
private theorem OUGenerator_joint_stein_fst (h : TestFunH d L W Φ) (t : ℝ) {p : CoordF d L W}
    (hp : p ∈ usedCoords d L W) :
    ∫ z, z.1 p • coordD1 d L W Φ (ouPairMat d L W t z) p ∂(ouPairP d L W g)
      = (gvarF d L W g p : ℝ) • Real.exp (-t / 2) •
          ∫ z, coordD2 d L W Φ (ouPairMat d L W t z) p ∂(ouPairP d L W g) := by
  have hInt1 := OUGenerator_integrable_term_fst (g := g) h t p
  have hInt2 := OUGenerator_integrable_coordD2 (g := g) h t p
  unfold ouPairP
  have hstep : ∀ ω2 : Ω d L W, ∫ ω1, ω1 p • coordD1 d L W Φ (ouPairMat d L W t (ω1, ω2)) p ∂(PF d L W g)
      = (gvarF d L W g p : ℝ) • Real.exp (-t / 2) •
          ∫ ω1, coordD2 d L W Φ (ouPairMat d L W t (ω1, ω2)) p ∂(PF d L W g) := by
    intro ω2
    have hs : ∫ ω1, ω1 p • coordD1 d L W Φ
          (Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω2 + Real.exp (-t / 2) • Xmat d L W ω1) p
          ∂(PF d L W g)
        = (gvarF d L W g p : ℝ) • ∫ ω1, Real.exp (-t / 2) • coordD2 d L W Φ
          (Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω2 + Real.exp (-t / 2) • Xmat d L W ω1) p
          ∂(PF d L W g) :=
      OUGenerator_stein_shift (gvarF d L W g) h _
        ((Xmat_isHermitian d L W ω2).smul (IsSelfAdjoint.all _)) _ hp
    have hcomm : ∀ ω1 : Ω d L W, ouPairMat d L W t (ω1, ω2)
        = Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω2 + Real.exp (-t / 2) • Xmat d L W ω1 :=
      fun ω1 => add_comm _ _
    simp only [hcomm] at hs ⊢
    rw [hs, integral_smul]
  rw [integral_prod_symm _ hInt1, funext hstep]
  simp_rw [integral_smul]
  rw [← integral_prod_symm _ hInt2]

/-- **The GUE-field Stein identity, at the level of the joint measure.** -/
private theorem OUGenerator_joint_stein_snd (h : TestFunH d L W Φ) (t : ℝ) {p : CoordF d L W}
    (hp : p ∈ usedCoords d L W) :
    ∫ z, z.2 p • coordD1 d L W Φ (ouPairMat d L W t z) p ∂(ouPairP d L W g)
      = (gueVar d L W p : ℝ) • Real.sqrt (1 - Real.exp (-t)) •
          ∫ z, coordD2 d L W Φ (ouPairMat d L W t z) p ∂(ouPairP d L W g) := by
  have hInt1 := OUGenerator_integrable_term_snd (g := g) h t p
  have hInt2 := OUGenerator_integrable_coordD2 (g := g) h t p
  unfold ouPairP
  have hstep : ∀ ω1 : Ω d L W, ∫ ω2, ω2 p • coordD1 d L W Φ (ouPairMat d L W t (ω1, ω2)) p ∂(gueP d L W)
      = (gueVar d L W p : ℝ) • Real.sqrt (1 - Real.exp (-t)) •
          ∫ ω2, coordD2 d L W Φ (ouPairMat d L W t (ω1, ω2)) p ∂(gueP d L W) := by
    intro ω1
    have hs : ∫ ω2, ω2 p • coordD1 d L W Φ
          (Real.exp (-t / 2) • Xmat d L W ω1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω2) p
          ∂(gueP d L W)
        = (gueVar d L W p : ℝ) • ∫ ω2, Real.sqrt (1 - Real.exp (-t)) • coordD2 d L W Φ
          (Real.exp (-t / 2) • Xmat d L W ω1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω2) p
          ∂(gueP d L W) :=
      OUGenerator_stein_shift (gueVar d L W) h _
        ((Xmat_isHermitian d L W ω1).smul (IsSelfAdjoint.all _)) _ hp
    change ∫ ω2, ω2 p • coordD1 d L W Φ
          (Real.exp (-t / 2) • Xmat d L W ω1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω2) p
          ∂(gueP d L W) = _
    rw [hs, integral_smul]
    rfl
  rw [integral_prod _ hInt1, funext hstep]
  simp_rw [integral_smul]
  rw [← integral_prod _ hInt2]

end Stein

/-! ## 6. The coordinate sum collapses to the index-pair sum

Ported from RBM1D `Gauss/Generator.lean:948–1110` (`coordD2_swap`, `gvar_crd`,
`eq_of_add_self_eq_add_self`, `smul_quarter_pair`, `sum_sum_eq_of_swap_add_eq`,
`sum_used_eq_sum_pairs`, `integral_wirtSecond`); the bookkeeping lemma is a private re-proof of
the private `IBP_sum_used_eq_sum_pairs` of `Green/IBP.lean:481`. -/

section Collapse

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W] {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ}

/-- `coordD2` is unchanged when the two indices of the coordinate are swapped (RBM1D
`coordD2_swap`, `Generator:948`). -/
private theorem OUGenerator_coordD2_swap (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) (b : Bool) :
    coordD2 d L W Φ M (i, j, b) = coordD2 d L W Φ M (j, i, b) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  cases b
  · change fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat d L W i j false) (RBM.Green.Bmat d L W i j false)
      = fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat d L W j i false) (RBM.Green.Bmat d L W j i false)
    rw [Bmat_swap_false d L W hij]
    simp
  · change fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat d L W i j true) (RBM.Green.Bmat d L W i j true)
      = fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat d L W j i true) (RBM.Green.Bmat d L W j i true)
    rw [Bmat_swap_true d L W i j]

/-- The variance of a coordinate, read off from the index pair (RBM1D `gvar_crd`). -/
private theorem OUGenerator_gvar_eq (p : CoordF d L W) :
    (gvarF d L W g p : ℝ)
      = if p.1 = p.2.1 then svarF d L W g p.1 p.2.1 else svarF d L W g p.1 p.2.1 / 2 := by
  obtain ⟨i, j, b⟩ := p
  unfold gvarF
  rfl

/-- The GUE coordinate variance, read off from the index pair: `N⁻¹` on the diagonal and
`N⁻¹ / 2` off it, `N = card (Idx d L W) = (W L)²`. -/
private theorem OUGenerator_gueVar_eq (p : CoordF d L W) :
    (gueVar d L W p : ℝ)
      = if p.1 = p.2.1 then (Fintype.card (Idx d L W) : ℝ)⁻¹
        else (Fintype.card (Idx d L W) : ℝ)⁻¹ / 2 := by
  rw [RBM.Gauss.card_Idx]
  unfold gueVar
  by_cases hp : p.1 = p.2.1
  · simp [hp]
  · simp only [hp, ite_false]
    push_cast
    rw [mul_inv]
    ring

/-- Halving is injective on an `ℝ`-module: `X + X = Y + Y` forces `X = Y`. -/
private theorem OUGenerator_eq_of_add_self_eq_add_self {V : Type*} [AddCommGroup V]
    [Module ℝ V] {X Y : V} (h : X + X = Y + Y) : X = Y := by
  have h2 : ((2 : ℝ)⁻¹ * 2) • X = ((2 : ℝ)⁻¹ * 2) • Y := by
    rw [mul_smul, mul_smul, two_smul, two_smul, h]
  have hc : ((2 : ℝ)⁻¹ * 2) = 1 := by norm_num
  rwa [hc, one_smul, one_smul] at h2

/-- The off-diagonal bookkeeping: a quarter of each of the two copies, twice over, is a half. -/
private theorem OUGenerator_smul_quarter_pair {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : ℝ) (A B : V) :
    (c / 2) • A + (c / 2) • B =
      c • (1 / 4 : ℝ) • (A + B) + c • (1 / 4 : ℝ) • (A + B) := by
  rw [smul_smul, ← two_smul ℝ, smul_smul,
    show (2 * (c * (1 / 4)) : ℝ) = c / 2 by ring, smul_add]

/-- A double sum over a square index set is determined by the swap-symmetrization of its
summand. -/
private theorem OUGenerator_sum_sum_eq_of_swap_add_eq {ι : Type*} [Fintype ι] {V : Type*}
    [AddCommGroup V] [Module ℝ V] (g h : ι → ι → V)
    (key : ∀ i j, g i j + g j i = h i j + h j i) :
    (∑ i, ∑ j, g i j) = ∑ i, ∑ j, h i j := by
  have e1 : ∀ F : ι → ι → V,
      (∑ i, ∑ j, (F i j + F j i)) = (∑ i, ∑ j, F i j) + (∑ i, ∑ j, F j i) := by
    intro F
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hg : (∑ i, ∑ j, g i j) = ∑ i, ∑ j, g j i := Finset.sum_comm
  have hh : (∑ i, ∑ j, h i j) = ∑ i, ∑ j, h j i := Finset.sum_comm
  refine OUGenerator_eq_of_add_self_eq_add_self ?_
  calc (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g i j)
      = (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g j i) := by rw [← hg]
    _ = ∑ i, ∑ j, (g i j + g j i) := (e1 g).symm
    _ = ∑ i, ∑ j, (h i j + h j i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h j i) := e1 h
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h i j) := by rw [← hh]

/-- **The bookkeeping lemma** (RBM1D `sum_used_eq_sum_pairs`, `Generator:1058`).  Summing a
symmetric weight `S` against a symmetric family `f` over the "used" index set equals the full
double sum over ordered pairs, the diagonal separately and the off-diagonal terms weighted by
`1/4`. -/
private theorem OUGenerator_sum_used_eq_sum_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (κ : ι → ℕ) (hκ : Function.Injective κ)
    (S : ι → ι → ℝ) (hS : ∀ i j, S i j = S j i)
    (f : ι × ι × Bool → V)
    (htt : ∀ i j, f (i, j, true) = f (j, i, true))
    (hff : ∀ i j, f (i, j, false) = f (j, i, false)) :
    ∑ p ∈ Finset.univ.filter
        (fun p : ι × ι × Bool => κ p.1 < κ p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)),
      (if p.1 = p.2.1 then S p.1 p.2.1 else S p.1 p.2.1 / 2) • f p
      = ∑ i : ι, ∑ j : ι, S i j •
          (if i = j then f (i, i, true)
           else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine OUGenerator_sum_sum_eq_of_swap_add_eq _ _ ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬ (j = i) := fun hh => hij hh.symm
    rcases lt_trichotomy (κ i) (κ j) with hlt | heq | hgt
    · simp only [hij, hji, hlt, asymm hlt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero]
      exact OUGenerator_smul_quarter_pair _ _ _
    · exact absurd (hκ heq) hij
    · simp only [hij, hji, hgt, asymm hgt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero, zero_add]
      exact OUGenerator_smul_quarter_pair _ _ _

/-- The `wirtSecond` expectation over the joint measure, in terms of the two real directional
derivatives (RBM1D `integral_wirtSecond`, `Generator:993`). -/
private theorem OUGenerator_integral_wirtSecond (h : TestFunH d L W Φ) (t : ℝ) (i j : Idx d L W) :
    ∫ z, wirtSecond d L W Φ (ouPairMat d L W t z) i j ∂(ouPairP d L W g)
      = if i = j then ∫ z, coordD2 d L W Φ (ouPairMat d L W t z) (i, i, true) ∂(ouPairP d L W g)
        else (1 / 4 : ℝ) • (∫ z, coordD2 d L W Φ (ouPairMat d L W t z) (i, j, true) ∂(ouPairP d L W g)
          + ∫ z, coordD2 d L W Φ (ouPairMat d L W t z) (i, j, false) ∂(ouPairP d L W g)) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    change wirtSecond d L W Φ (ouPairMat d L W t z) i i = _
    rw [wirtSecond, ite_eq_left rfl]
  · rw [ite_eq_right hij]
    have hpt : (fun z : Ω d L W × Ω d L W => wirtSecond d L W Φ (ouPairMat d L W t z) i j)
        = fun z : Ω d L W × Ω d L W => (1 / 4 : ℝ) • (coordD2 d L W Φ (ouPairMat d L W t z) (i, j, true)
            + coordD2 d L W Φ (ouPairMat d L W t z) (i, j, false)) := by
      funext z
      rw [wirtSecond, ite_eq_right hij]
    rw [hpt, integral_smul, integral_add (OUGenerator_integrable_coordD2 h t _)
      (OUGenerator_integrable_coordD2 h t _)]

/-- Combining two weighted double sums that share the same values `W i j`: pure `Finset`
algebra. -/
private theorem OUGenerator_sum2_combine {ι : Type*} [Fintype ι] (S1 S2 : ι → ι → ℝ)
    (c1 c2 : ℝ) (V : ι → ι → ℂ) :
    c1 • (∑ i, ∑ j, S1 i j • V i j) + c2 • (∑ i, ∑ j, S2 i j • V i j)
      = ∑ i, ∑ j, (c1 * S1 i j + c2 * S2 i j) • V i j := by
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul, ← add_smul]

end Collapse

/-! ## 7. The generator identity in the paper's `∑_{ab} S°_{ab} ∂_{ab}∂_{ba}` form -/

section Pairs

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W] {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ}

/-- **The generator identity for a `TestFunH`, with `t > 0`.**  The `svar` collapse (band field)
and the constant-weight `N⁻¹` collapse (GUE field) use the same family
`p ↦ ∫ z, coordD2 Φ (𝐇_t z) p` and combine into the single weight
`svar - N⁻¹ = centeredVarianceEntry`, because `a'(t) a(t) = -½ e^{-t}` and
`b'(t) b(t) = ½ e^{-t}`. -/
private theorem OUGenerator_hasDerivAt_integral_pairs (h : TestFunH d L W Φ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ z, Φ (ouPairMat d L W s z) ∂(ouPairP d L W g))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
          (centeredVarianceEntry d L W g a b : ℂ) *
            ∫ z, wirtSecond d L W Φ (ouPairMat d L W t z) a b ∂(ouPairP d L W g)) t := by
  have hbase := OUGenerator_hasDerivAt_integral_joint (g := g) h ht
  set f : CoordF d L W → ℂ := fun p => ∫ z, coordD2 d L W Φ (ouPairMat d L W t z) p ∂(ouPairP d L W g)
    with hf
  have hswap : ∀ (i j : Idx d L W) (b : Bool), f (i, j, b) = f (j, i, b) := by
    intro i j b
    simp only [hf]
    exact integral_congr_ae (Eventually.of_forall fun z =>
      OUGenerator_coordD2_swap Φ _ i j b)
  have hband : ∑ p ∈ usedCoords d L W, (gvarF d L W g p : ℝ) • f p
      = ∑ i : Idx d L W, ∑ j : Idx d L W, svarF d L W g i j •
          (if i = j then f (i, i, true) else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
    have hlhs : ∑ p ∈ usedCoords d L W, (gvarF d L W g p : ℝ) • f p
        = ∑ p ∈ usedCoords d L W,
          (if p.1 = p.2.1 then svarF d L W g p.1 p.2.1 else svarF d L W g p.1 p.2.1 / 2) • f p :=
      Finset.sum_congr rfl fun p _ => by rw [OUGenerator_gvar_eq]
    rw [hlhs, show usedCoords d L W = Finset.univ.filter
        (fun p : Idx d L W × Idx d L W × Bool =>
          idxKey d L W p.1 < idxKey d L W p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
      OUGenerator_sum_used_eq_sum_pairs (idxKey d L W) (idxKey_injective d L W) (svarF d L W g)
        (svarF_comm d L W g) f (fun i j => hswap i j true) (fun i j => hswap i j false)]
  have hgue : ∑ p ∈ usedCoords d L W, (gueVar d L W p : ℝ) • f p
      = ∑ i : Idx d L W, ∑ j : Idx d L W, (Fintype.card (Idx d L W) : ℝ)⁻¹ •
          (if i = j then f (i, i, true) else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
    have hlhs : ∑ p ∈ usedCoords d L W, (gueVar d L W p : ℝ) • f p
        = ∑ p ∈ usedCoords d L W,
          (if p.1 = p.2.1 then (Fintype.card (Idx d L W) : ℝ)⁻¹
           else (Fintype.card (Idx d L W) : ℝ)⁻¹ / 2) • f p :=
      Finset.sum_congr rfl fun p _ => by rw [OUGenerator_gueVar_eq]
    rw [hlhs, show usedCoords d L W = Finset.univ.filter
        (fun p : Idx d L W × Idx d L W × Bool =>
          idxKey d L W p.1 < idxKey d L W p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
      OUGenerator_sum_used_eq_sum_pairs (idxKey d L W) (idxKey_injective d L W)
        (fun _ _ => (Fintype.card (Idx d L W) : ℝ)⁻¹) (fun _ _ => rfl) f
        (fun i j => hswap i j true) (fun i j => hswap i j false)]
  have hIeq : (∫ z, OUGenerator_dF d L W Φ t z ∂(ouPairP d L W g))
      = OUGenerator_aC t • (∑ p ∈ usedCoords d L W,
              (gvarF d L W g p : ℝ) • Real.exp (-t / 2) • f p)
        + OUGenerator_bC t • (∑ p ∈ usedCoords d L W,
              (gueVar d L W p : ℝ) • Real.sqrt (1 - Real.exp (-t)) • f p) := by
    have hA : Integrable (fun z : Ω d L W × Ω d L W => OUGenerator_aC t •
        OUGenerator_S1 d L W Φ t z) (ouPairP d L W g) :=
      Integrable.smul (OUGenerator_aC t) (OUGenerator_integrable_S1 h t)
    have hB : Integrable (fun z : Ω d L W × Ω d L W => OUGenerator_bC t •
        OUGenerator_S2 d L W Φ t z) (ouPairP d L W g) :=
      Integrable.smul (OUGenerator_bC t) (OUGenerator_integrable_S2 h t)
    have hS1 : ∫ z, OUGenerator_S1 d L W Φ t z ∂(ouPairP d L W g)
        = ∑ p ∈ usedCoords d L W, ∫ z, z.1 p • coordD1 d L W Φ (ouPairMat d L W t z) p ∂(ouPairP d L W g) :=
      integral_finsetSum _ (fun p _ => OUGenerator_integrable_term_fst h t p)
    have hS2 : ∫ z, OUGenerator_S2 d L W Φ t z ∂(ouPairP d L W g)
        = ∑ p ∈ usedCoords d L W, ∫ z, z.2 p • coordD1 d L W Φ (ouPairMat d L W t z) p ∂(ouPairP d L W g) :=
      integral_finsetSum _ (fun p _ => OUGenerator_integrable_term_snd h t p)
    change ∫ z, (OUGenerator_aC t • OUGenerator_S1 d L W Φ t z
        + OUGenerator_bC t • OUGenerator_S2 d L W Φ t z) ∂(ouPairP d L W g) = _
    rw [integral_add hA hB, integral_smul, integral_smul, hS1, hS2,
      Finset.sum_congr rfl (fun p hp => OUGenerator_joint_stein_fst h t hp),
      Finset.sum_congr rfl (fun p hp => OUGenerator_joint_stein_snd h t hp)]
  have hcomm1 : ∀ p : CoordF d L W,
      (gvarF d L W g p : ℝ) • Real.exp (-t / 2) • f p
        = Real.exp (-t / 2) • (gvarF d L W g p : ℝ) • f p := fun p => by
    rw [smul_smul, smul_smul, mul_comm]
  have hcomm2 : ∀ p : CoordF d L W,
      (gueVar d L W p : ℝ) • Real.sqrt (1 - Real.exp (-t)) • f p
        = Real.sqrt (1 - Real.exp (-t)) • (gueVar d L W p : ℝ) • f p := fun p => by
    rw [smul_smul, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl (fun p _ => hcomm1 p), Finset.sum_congr rfl (fun p _ => hcomm2 p),
    ← Finset.smul_sum, ← Finset.smul_sum, smul_smul, smul_smul, hband, hgue] at hIeq
  set V : Idx d L W → Idx d L W → ℂ := fun a b =>
    if a = b then f (a, a, true) else (1 / 4 : ℝ) • (f (a, b, true) + f (a, b, false))
    with hV
  have hcoef : OUGenerator_aC t * Real.exp (-t / 2) = -(1 / 2 : ℝ) * Real.exp (-t) := by
    unfold OUGenerator_aC
    rw [show -(1 / 2 : ℝ) * Real.exp (-t / 2) * Real.exp (-t / 2)
        = -(1 / 2 : ℝ) * (Real.exp (-t / 2) * Real.exp (-t / 2)) by ring,
      ← Real.exp_add, show -t / 2 + -t / 2 = -t by ring]
  have hcoef2 : OUGenerator_bC t * Real.sqrt (1 - Real.exp (-t)) = (1 / 2 : ℝ) * Real.exp (-t) := by
    unfold OUGenerator_bC
    have hpos : 0 < Real.sqrt (1 - Real.exp (-t)) := Real.sqrt_pos.mpr (OUGenerator_zeta_pos ht)
    field_simp
  have hscalar : ∀ a b : Idx d L W,
      (OUGenerator_aC t * Real.exp (-t / 2)) * svarF d L W g a b
        + (OUGenerator_bC t * Real.sqrt (1 - Real.exp (-t))) * (Fintype.card (Idx d L W) : ℝ)⁻¹
        = -(1 / 2 : ℝ) * Real.exp (-t) * (centeredVarianceEntry d L W g a b : ℝ) := by
    intro a b
    rw [hcoef, hcoef2]
    unfold centeredVarianceEntry
    ring
  have hcombine : (OUGenerator_aC t * Real.exp (-t / 2)) •
        (∑ i : Idx d L W, ∑ j : Idx d L W, svarF d L W g i j • V i j)
      + (OUGenerator_bC t * Real.sqrt (1 - Real.exp (-t))) •
        (∑ i : Idx d L W, ∑ j : Idx d L W, (Fintype.card (Idx d L W) : ℝ)⁻¹ • V i j)
      = (-(1 / 2 : ℝ) * Real.exp (-t)) •
        ∑ i : Idx d L W, ∑ j : Idx d L W, (centeredVarianceEntry d L W g i j : ℝ) • V i j := by
    rw [OUGenerator_sum2_combine, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hscalar i j, smul_smul]
  have hfinal : ∑ a : Idx d L W, ∑ b : Idx d L W, (centeredVarianceEntry d L W g a b : ℂ) *
        ∫ z, wirtSecond d L W Φ (ouPairMat d L W t z) a b ∂(ouPairP d L W g)
      = ∑ a : Idx d L W, ∑ b : Idx d L W, (centeredVarianceEntry d L W g a b : ℝ) • V a b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [OUGenerator_integral_wirtSecond h t a b]
    exact Complex.real_smul.symm
  rw [hfinal, ← hcombine, ← hIeq]
  exact hbase

end Pairs

/-! ## 8. Continuity at `t = 0`, the FTC form, and targets 1–2 -/

section FTC

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W] {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ}

/-- `s ↦ 𝐇_s(z)` is continuous **everywhere**, including at `s = 0`: only its `t`-derivative
(through `√(1 - e^{-s})`) is singular there. -/
private theorem OUGenerator_continuous_ouPairMat_in_s (z : Ω d L W × Ω d L W) :
    Continuous fun s : ℝ => ouPairMat d L W s z := by
  have h1 : Continuous fun s : ℝ => Real.exp (-s / 2) := by fun_prop
  have h2 : Continuous fun s : ℝ => Real.sqrt (1 - Real.exp (-s)) := by fun_prop
  exact (h1.smul continuous_const).add (h2.smul continuous_const)

/-- **`s ↦ ∫ Φ (𝐇_s) ∂ouP` is continuous everywhere**, in particular at `s = 0` where it is not
differentiable. -/
private theorem OUGenerator_continuous_integral (h : TestFunH d L W Φ) :
    Continuous (fun s : ℝ => ∫ z, Φ (ouPairMat d L W s z) ∂(ouPairP d L W g)) := by
  obtain ⟨C₀, hC₀⟩ := h.2.1
  refine continuous_of_dominated
    (fun s => (OUGenerator_continuous_Phi h (OUGenerator_continuous_ouPairMat s)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W s z)).aestronglyMeasurable)
    (fun s => Eventually.of_forall fun z => hC₀ _ (OUGenerator_ouPairMat_isHermitian d L W s z))
    (integrable_const C₀) (Eventually.of_forall fun z => ?_)
  exact OUGenerator_continuous_Phi h (OUGenerator_continuous_ouPairMat_in_s z)
    (fun s => OUGenerator_ouPairMat_isHermitian d L W s z)

/-- A global bound on `wirtSecond` at Hermitian matrices, for a fixed index pair. -/
private theorem OUGenerator_exists_bound_wirtSecond (h : TestFunH d L W Φ) (a b : Idx d L W) :
    ∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ‖wirtSecond d L W Φ M a b‖ ≤ C := by
  obtain ⟨C₂, hC₂⟩ := h.2.2.2
  rcases eq_or_ne a b with rfl | hab
  · refine ⟨C₂ * ‖RBM.Green.Bmat d L W a a true‖ * ‖RBM.Green.Bmat d L W a a true‖,
      fun M hM => ?_⟩
    unfold wirtSecond
    rw [ite_eq_left rfl]
    exact OUGenerator_norm_coordD2_le hC₂ hM (a, a, true)
  · refine ⟨(1 / 4 : ℝ) * (C₂ * ‖RBM.Green.Bmat d L W a b true‖ * ‖RBM.Green.Bmat d L W a b true‖
        + C₂ * ‖RBM.Green.Bmat d L W a b false‖ * ‖RBM.Green.Bmat d L W a b false‖),
      fun M hM => ?_⟩
    unfold wirtSecond
    rw [ite_eq_right hab]
    calc ‖(1 / 4 : ℝ) • (coordD2 d L W Φ M (a, b, true) + coordD2 d L W Φ M (a, b, false))‖
        = (1 / 4 : ℝ) * ‖coordD2 d L W Φ M (a, b, true) + coordD2 d L W Φ M (a, b, false)‖ := by
          rw [norm_smul]; simp
      _ ≤ (1 / 4 : ℝ) * (‖coordD2 d L W Φ M (a, b, true)‖ + ‖coordD2 d L W Φ M (a, b, false)‖) := by
          gcongr
          exact norm_add_le _ _
      _ ≤ (1 / 4 : ℝ) * (C₂ * ‖RBM.Green.Bmat d L W a b true‖ * ‖RBM.Green.Bmat d L W a b true‖
            + C₂ * ‖RBM.Green.Bmat d L W a b false‖ * ‖RBM.Green.Bmat d L W a b false‖) := by
          gcongr
          · exact OUGenerator_norm_coordD2_le hC₂ hM (a, b, true)
          · exact OUGenerator_norm_coordD2_le hC₂ hM (a, b, false)

private theorem OUGenerator_continuous_wirtSecond_comp (h : TestFunH d L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx d L W) (Idx d L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (i j : Idx d L W) :
    Continuous fun a => wirtSecond d L W Φ (f a) i j := by
  unfold wirtSecond
  by_cases hij : i = j
  · simp only [hij, ite_true]
    exact OUGenerator_continuous_coordD2 h hf hherm (j, j, true)
  · simp only [hij, ite_false]
    exact ((OUGenerator_continuous_coordD2 h hf hherm (i, j, true)).add
      (OUGenerator_continuous_coordD2 h hf hherm (i, j, false))).const_smul (1 / 4 : ℝ)

/-- `s ↦ ∫ wirtSecond Φ (𝐇_s) a b ∂ouP` is continuous everywhere. -/
private theorem OUGenerator_continuous_integral_wirtSecond (h : TestFunH d L W Φ)
    (a b : Idx d L W) :
    Continuous (fun s : ℝ => ∫ z, wirtSecond d L W Φ (ouPairMat d L W s z) a b ∂(ouPairP d L W g)) := by
  obtain ⟨C, hC⟩ := OUGenerator_exists_bound_wirtSecond h a b
  refine continuous_of_dominated
    (fun s => (OUGenerator_continuous_wirtSecond_comp h (OUGenerator_continuous_ouPairMat s)
      (fun z => OUGenerator_ouPairMat_isHermitian d L W s z) a b).aestronglyMeasurable)
    (fun s => Eventually.of_forall fun z => hC _ (OUGenerator_ouPairMat_isHermitian d L W s z))
    (integrable_const C) (Eventually.of_forall fun z => ?_)
  exact OUGenerator_continuous_wirtSecond_comp h (OUGenerator_continuous_ouPairMat_in_s z)
    (fun s => OUGenerator_ouPairMat_isHermitian d L W s z) a b

/-- The continuity of the right-hand side of the generator identity, for interval
integrability. -/
private theorem OUGenerator_continuous_rhs (h : TestFunH d L W Φ) :
    Continuous (fun t : ℝ => (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
      (centeredVarianceEntry d L W g a b : ℂ) *
        ∫ z, wirtSecond d L W Φ (ouPairMat d L W t z) a b ∂(ouPairP d L W g)) := by
  have hc : Continuous fun t : ℝ => -(1 / 2 : ℝ) * Real.exp (-t) := by fun_prop
  have hs : Continuous fun t : ℝ => ∑ a : Idx d L W, ∑ b : Idx d L W,
      (centeredVarianceEntry d L W g a b : ℂ) *
        ∫ z, wirtSecond d L W Φ (ouPairMat d L W t z) a b ∂(ouPairP d L W g) :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_const.mul (OUGenerator_continuous_integral_wirtSecond h a b)
  exact hc.smul hs

end FTC

/-- **Target P1 (RBM2D `ouGenerator_hasDerivAt_integral`, `:940`; pair carrier).**  The OU generator
identity `d/dt E Φ(𝐇_t) = -½ e^{-t} ∑_{ab} S°_{ab} E ∂_{ab}∂_{ba} Φ(𝐇_t)` for `t > 0`, `S° = S - N⁻¹` with
`S = svarF d L W g`. -/
theorem ouGeneratorPair_hasDerivAt_integral (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)
    (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (hΦ : TestFunH d L W Φ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (ouPairMat d L W s ω) ∂(ouPairP d L W g))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
        (centeredVarianceEntry d L W g a b : ℂ) *
          ∫ ω, wirtSecond d L W Φ (ouPairMat d L W t ω) a b ∂(ouPairP d L W g)) t :=
  OUGenerator_hasDerivAt_integral_pairs hΦ ht

/-- **Target P2 (RBM2D `ouGenerator_integral_sub_eq`, `:951`; pair carrier).**  The FTC form of the generator
identity from `t = 0`. -/
theorem ouGeneratorPair_integral_sub_eq (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)
    (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (hΦ : TestFunH d L W Φ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, Φ (ouPairMat d L W T ω) ∂(ouPairP d L W g)) -
        ∫ ω, Φ (ouPairMat d L W 0 ω) ∂(ouPairP d L W g) =
      ∫ t in (0 : ℝ)..T, (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
        (centeredVarianceEntry d L W g a b : ℂ) *
          ∫ ω, wirtSecond d L W Φ (ouPairMat d L W t ω) a b ∂(ouPairP d L W g) := by
  set F : ℝ → ℂ := fun s => ∫ ω, Φ (ouPairMat d L W s ω) ∂(ouPairP d L W g) with hF
  set G : ℝ → ℂ := fun t => (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
      (centeredVarianceEntry d L W g a b : ℂ) *
        ∫ ω, wirtSecond d L W Φ (ouPairMat d L W t ω) a b ∂(ouPairP d L W g) with hG
  rcases eq_or_lt_of_le hT with hT0 | hT0
  · simp [← hT0]
  have hcont : ContinuousOn F (Set.Icc 0 T) := (OUGenerator_continuous_integral hΦ).continuousOn
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt F (G t) t := fun t ht =>
    OUGenerator_hasDerivAt_integral_pairs hΦ ht.1
  have hint : IntervalIntegrable G MeasureTheory.volume 0 T :=
    (OUGenerator_continuous_rhs hΦ).intervalIntegrable 0 T
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT0.le hcont hderiv hint).symm

/-! ### The carrier transfer (targets T1, T2, B1, B2) -/

/-- **Target T1.**  The merged band OU matrix is the pair OU matrix of the slice. -/
theorem ouMat_band_eq_ouPairMat (d : ℕ) (sz : Sizes d) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat (UNModel.band sz) n t ω =
      ouPairMat d (sz.L n) (sz.W n) t
        (Prod.map (Sizes.slice sz n) (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n)) ω) :=
  rfl

/-- **Target T2.**  The band carrier pushes forward to the pair carrier at coupling `g = sz.lam n` (the inner
`this` of `ouSample_law`, `OU.lean:215-220`). -/
theorem ouP_band_map_pair (d : ℕ) (sz : Sizes d) (n : ℕ) :
    (ouP (UNModel.band sz) n).map
        (Prod.map (Sizes.slice sz n) (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n))) =
      ouPairP d (sz.L n) (sz.W n) (sz.lam n) := by
  unfold ouP ouPairP
  rw [← Measure.map_prod_map _ _ (measurable_slice sz n) measurable_id, Measure.map_id]
  change ((seqP sz).map (slice sz n)).prod _ = _
  rw [seqP_map_slice]

/-- Integrals over the band carrier of a continuous function of the sliced pair are integrals over the pair
carrier. -/
private theorem OUGenerator_integral_band {d : ℕ} (sz : Sizes d) (n : ℕ)
    (F : Ω d (sz.L n) (sz.W n) × Ω d (sz.L n) (sz.W n) → ℂ) (hF : Continuous F) :
    ∫ ω, F (Prod.map (Sizes.slice sz n) (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n)) ω)
        ∂(ouP (UNModel.band sz) n)
      = ∫ z, F z ∂(ouPairP d (sz.L n) (sz.W n) (sz.lam n)) := by
  have hm : Measurable (Prod.map (Sizes.slice sz n)
      (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n))) :=
    (measurable_slice sz n).prodMap measurable_id
  rw [← ouP_band_map_pair d sz n]
  exact (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm

private theorem OUGenerator_band_Phi {d : ℕ} (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (hΦ : TestFunH d (sz.L n) (sz.W n) Φ) (s : ℝ) :
    ∫ ω, Φ (ouMat (UNModel.band sz) n s ω) ∂(ouP (UNModel.band sz) n)
      = ∫ z, Φ (ouPairMat d (sz.L n) (sz.W n) s z) ∂(ouPairP d (sz.L n) (sz.W n) (sz.lam n)) :=
  OUGenerator_integral_band sz n (fun z => Φ (ouPairMat d (sz.L n) (sz.W n) s z))
    (OUGenerator_continuous_Phi hΦ (OUGenerator_continuous_ouPairMat s)
      (fun z => OUGenerator_ouPairMat_isHermitian _ _ _ s z))

private theorem OUGenerator_band_wirt {d : ℕ} (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (hΦ : TestFunH d (sz.L n) (sz.W n) Φ) (t : ℝ) (a b : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n t ω) a b
        ∂(ouP (UNModel.band sz) n)
      = ∫ z, wirtSecond d (sz.L n) (sz.W n) Φ (ouPairMat d (sz.L n) (sz.W n) t z) a b
          ∂(ouPairP d (sz.L n) (sz.W n) (sz.lam n)) :=
  OUGenerator_integral_band sz n
    (fun z => wirtSecond d (sz.L n) (sz.W n) Φ (ouPairMat d (sz.L n) (sz.W n) t z) a b)
    (OUGenerator_continuous_wirtSecond_comp hΦ (OUGenerator_continuous_ouPairMat t)
      (fun z => OUGenerator_ouPairMat_isHermitian _ _ _ t z) a b)

/-- **Target B1 (RBM2D `ouGenerator_hasDerivAt_integral`; the form UN-18 calls).**  The OU generator identity
on the band carrier `ouP (UNModel.band sz) n`, `S° = centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n)`,
for `t > 0`.  Band model only (the law is Gaussian only there, `Pins.lean:600-603`). -/
theorem ouGenerator_hasDerivAt_integral (d : ℕ) (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (hΦ : TestFunH d (sz.L n) (sz.W n) Φ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (ouMat (UNModel.band sz) n s ω) ∂(ouP (UNModel.band sz) n))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) •
        ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
          (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
            ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n t ω) a b
              ∂(ouP (UNModel.band sz) n)) t := by
  have h := ouGeneratorPair_hasDerivAt_integral d (sz.L n) (sz.W n) (sz.lam n) Φ hΦ t ht
  rw [funext (OUGenerator_band_Phi sz n Φ hΦ)]
  simp only [OUGenerator_band_wirt sz n Φ hΦ t]
  exact h

/-- **Target B2 (RBM2D `ouGenerator_integral_sub_eq`; the form UN-18 calls).**  The FTC form on the band
carrier, from `t = 0`. -/
theorem ouGenerator_integral_sub_eq (d : ℕ) (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (hΦ : TestFunH d (sz.L n) (sz.W n) Φ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, Φ (ouMat (UNModel.band sz) n T ω) ∂(ouP (UNModel.band sz) n)) -
        ∫ ω, Φ (ouMat (UNModel.band sz) n 0 ω) ∂(ouP (UNModel.band sz) n) =
      ∫ t in (0 : ℝ)..T, (-(1 / 2 : ℝ) * Real.exp (-t)) •
        ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
          (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
            ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n t ω) a b
              ∂(ouP (UNModel.band sz) n) := by
  have h := ouGeneratorPair_integral_sub_eq d (sz.L n) (sz.W n) (sz.lam n) Φ hΦ T hT
  rw [OUGenerator_band_Phi sz n Φ hΦ, OUGenerator_band_Phi sz n Φ hΦ]
  simp only [OUGenerator_band_wirt sz n Φ hΦ]
  exact h

/-! ## 9. Target 3: `∏ Im m(z_i)` is a `TestFunH`

Near a Hermitian `x`, each factor is `K ↦ ℓ(Ring.inverse (K - w))` with
`ℓ = Im ∘ (|ι|⁻¹ tr)` real-linear; `Ring.inverse` is smooth on the open set of units,
`D inv(u) = -mulLeftRight u⁻¹ u⁻¹` (`fderiv_inverse`), and on the units
`D inv(y) = mulLeftRight (-y⁻¹) y⁻¹`, whose derivative is bounded by Mathlib's bilinear Leibniz
bound `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear`, giving
`‖D^k inv(u)‖ ≤ ‖u⁻¹‖, ‖u⁻¹‖², 2‖u⁻¹‖³` for `k = 0, 1, 2`.  At Hermitian `x` with `Im w > 0`,
`‖(x - w)⁻¹‖ ≤ (Im w)⁻¹` (`RBM.Gauss.norm_Gsig_le_inv_eta`).  The finite product is handled by
Mathlib's `norm_iteratedFDerivWithin_prod_le` on the open set where every factor's shift is a
unit.  Port of RBM1D `Flow/OUGenerator.lean:1167–1358` (`ouGen_*`), with
`stieltjes` ↦ `stieltjesN`. -/

section StieltjesTestFun

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem OUGenerator_inv_norm_iter_one {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    ‖iteratedFDeriv ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ ≤
      ‖Ring.inverse u‖ * ‖Ring.inverse u‖ := by
  rw [norm_iteratedFDeriv_one]
  obtain ⟨v, rfl⟩ := hu
  rw [fderiv_inverse, norm_neg, ← Ring.inverse_unit]
  exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le _ _ _ _

private theorem OUGenerator_inv_fderiv_eventually {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    fderiv ℝ (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) =ᶠ[𝓝 u]
      fun y => ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ) (-Ring.inverse y)
        (Ring.inverse y) := by
  filter_upwards [Units.isOpen.mem_nhds hu] with y hy
  obtain ⟨v, rfl⟩ := hy
  rw [fderiv_inverse, Ring.inverse_unit]
  ext h : 1
  simp

private theorem OUGenerator_inv_norm_iter_two {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    ‖iteratedFDeriv ℝ 2 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ ≤
      2 * (‖Ring.inverse u‖ * ‖Ring.inverse u‖ * ‖Ring.inverse u‖) := by
  set s : Set (Matrix ι ι ℂ) := {x | IsUnit x}
  have hs : IsOpen s := Units.isOpen
  have hcd : ContDiffOn ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) s := fun y hy => by
    obtain ⟨v, rfl⟩ := hy
    exact ((contDiffAt_ringInverse ℝ v).of_le (by exact_mod_cast le_top)).contDiffWithinAt
  have hcd' : ContDiffOn ℝ 1 (fun y : Matrix ι ι ℂ => -Ring.inverse y) s := hcd.neg
  rw [← norm_iteratedFDeriv_fderiv,
    ((OUGenerator_inv_fderiv_eventually hu).iteratedFDeriv ℝ 1).eq_of_nhds,
    ← iteratedFDerivWithin_of_isOpen 1 hs hu]
  have hB :=
    (ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ)).norm_iteratedFDerivWithin_le_of_bilinear
      hcd' hcd hs.uniqueDiffOn hu (n := 1) le_rfl
  refine hB.trans ?_
  refine le_trans (mul_le_of_le_one_left (by positivity) ?_) ?_
  · exact ContinuousLinearMap.opNorm_mulLeftRight_le ℝ (Matrix ι ι ℂ)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one, one_mul, zero_add, Nat.sub_zero]
  rw [iteratedFDerivWithin_of_isOpen 0 hs hu, iteratedFDerivWithin_of_isOpen 1 hs hu,
    iteratedFDerivWithin_of_isOpen 0 hs hu, iteratedFDerivWithin_of_isOpen 1 hs hu,
    norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero, norm_neg]
  have hneg : ‖iteratedFDeriv ℝ 1 (fun y : Matrix ι ι ℂ => -Ring.inverse y) u‖ =
      ‖iteratedFDeriv ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ := by
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, fderiv_fun_neg, norm_neg]
  rw [hneg]
  have h1 := OUGenerator_inv_norm_iter_one hu
  have h0 := norm_nonneg (Ring.inverse u)
  nlinarith [mul_le_mul_of_nonneg_left h1 h0]

/-- `K ↦ Im (|ι|⁻¹ tr K)`, the real-linear functional through which `Im m` factors. -/
private noncomputable def OUGenerator_stImCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (Complex.imLm.comp (((Fintype.card ι : ℂ)⁻¹ • Matrix.traceLinearMap ι ℂ ℂ).restrictScalars ℝ))

private theorem OUGenerator_stieltjes_im_eq (K : Matrix ι ι ℂ) (w : ℂ) :
    (stieltjesN K w).im
      = OUGenerator_stImCLM ι (Ring.inverse (K - w • (1 : Matrix ι ι ℂ))) := by
  simp [OUGenerator_stImCLM, stieltjesN, Gres]

private theorem OUGenerator_contDiffAt_inv_shift {x : Matrix ι ι ℂ} {w : ℂ}
    (hx : IsUnit (x - w • (1 : Matrix ι ι ℂ))) :
    ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => Ring.inverse (K - w • (1 : Matrix ι ι ℂ))) x := by
  obtain ⟨v, hv⟩ := hx
  have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := 2) v
  rw [hv] at h
  exact h.comp x (contDiffAt_id.sub contDiffAt_const)

private theorem OUGenerator_contDiffAt_stieltjes_im {x : Matrix ι ι ℂ} {w : ℂ}
    (hx : IsUnit (x - w • (1 : Matrix ι ι ℂ))) :
    ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => (stieltjesN K w).im) x := by
  have : (fun K : Matrix ι ι ℂ => (stieltjesN K w).im) =
      OUGenerator_stImCLM ι ∘ fun K : Matrix ι ι ℂ =>
        Ring.inverse (K - w • (1 : Matrix ι ι ℂ)) := by
    funext K; exact OUGenerator_stieltjes_im_eq K w
  rw [this]
  exact (OUGenerator_stImCLM ι).contDiff.contDiffAt.comp x (OUGenerator_contDiffAt_inv_shift hx)

/-- The derivatives of order `≤ 2` of one factor `Im m(w)`, at a Hermitian matrix, in every
real direction. -/
private theorem OUGenerator_norm_iteratedFDeriv_stieltjes_im_le {x : Matrix ι ι ℂ}
    (hx : x.IsHermitian) {w : ℂ} (hw : 0 < w.im) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun K : Matrix ι ι ℂ => (stieltjesN K w).im) x‖ ≤
      ‖OUGenerator_stImCLM ι‖ *
        (w.im⁻¹ + w.im⁻¹ * w.im⁻¹ + 2 * (w.im⁻¹ * w.im⁻¹ * w.im⁻¹)) := by
  have hu : IsUnit (x - w • (1 : Matrix ι ι ℂ)) :=
    RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hx hw.ne'
  have hg : ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ ≤ w.im⁻¹ := by
    have := norm_Gsig_le_inv_eta hx hw (le_abs_self w.im) true
    simpa [Gres] using this
  have h0 : 0 ≤ ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ := norm_nonneg _
  have hr : 0 ≤ w.im⁻¹ := inv_nonneg.mpr hw.le
  have : (fun K : Matrix ι ι ℂ => (stieltjesN K w).im) =
      OUGenerator_stImCLM ι ∘ fun K : Matrix ι ι ℂ =>
        Ring.inverse (K - w • (1 : Matrix ι ι ℂ)) := by
    funext K; exact OUGenerator_stieltjes_im_eq K w
  rw [this]
  refine ((OUGenerator_stImCLM ι).norm_iteratedFDeriv_comp_left (N := 2)
    (OUGenerator_contDiffAt_inv_shift hu)
    (by exact_mod_cast hk)).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [iteratedFDeriv_comp_sub]
  have hB : ‖iteratedFDeriv ℝ k (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ)
      (x - w • (1 : Matrix ι ι ℂ))‖ ≤
      ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ +
        ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ *
          ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ +
        2 * (‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ *
          ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ *
          ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖) := by
    interval_cases k
    · rw [norm_iteratedFDeriv_zero]
      nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
    · have := OUGenerator_inv_norm_iter_one hu
      nlinarith [mul_nonneg (mul_nonneg h0 h0) h0]
    · have := OUGenerator_inv_norm_iter_two hu
      nlinarith [mul_nonneg h0 h0]
  refine hB.trans ?_
  gcongr

/-- **`Φ = ∏ Im m(z_i)` lifted to `ℂ` has bounded derivatives of order `≤ 2` at Hermitian
matrices.** -/
private theorem OUGenerator_norm_iteratedFDeriv_stieltjesImProduct_le {m : ℕ} (z : Fin m → ℂ)
    (hz : ∀ i, 0 < (z i).im) {k : ℕ} (hk : k ≤ 2) :
    ∃ C : ℝ, ∀ x : Matrix ι ι ℂ, x.IsHermitian →
      ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ)) x ∧
      ‖iteratedFDeriv ℝ k
        (fun K : Matrix ι ι ℂ => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ)) x‖ ≤ C := by
  set β : Fin m → ℝ := fun i => ‖OUGenerator_stImCLM ι‖ *
    ((z i).im⁻¹ + (z i).im⁻¹ * (z i).im⁻¹ + 2 * ((z i).im⁻¹ * (z i).im⁻¹ * (z i).im⁻¹))
  refine ⟨‖Complex.ofRealCLM‖ * ∑ p ∈ (Finset.univ : Finset (Fin m)).sym k,
    ((p : Multiset (Fin m)).countPerms : ℝ) * ∏ j, β j, fun x hx => ?_⟩
  set s : Set (Matrix ι ι ℂ) := {K | ∀ i, IsUnit (K - z i • (1 : Matrix ι ι ℂ))}
  have hs : IsOpen s := by
    have : s = ⋂ i, (fun K : Matrix ι ι ℂ => K - z i • (1 : Matrix ι ι ℂ)) ⁻¹'
        {y | IsUnit y} := by
      ext K; simp [s]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      Units.isOpen.preimage (continuous_id.sub continuous_const)
  have hxs : x ∈ s := fun i =>
    RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hx (hz i).ne'
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ContDiffOn ℝ 2 (fun K : Matrix ι ι ℂ => (stieltjesN K (z i)).im) s :=
    fun i _ K hK => (OUGenerator_contDiffAt_stieltjes_im (hK i)).contDiffWithinAt
  have hP : ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => ∏ i, (stieltjesN K (z i)).im) x :=
    contDiffAt_prod fun i _ => OUGenerator_contDiffAt_stieltjes_im (hxs i)
  refine ⟨Complex.ofRealCLM.contDiff.contDiffAt.comp x hP, ?_⟩
  have hcomp : (fun K : Matrix ι ι ℂ => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ fun K : Matrix ι ι ℂ => ∏ i, (stieltjesN K (z i)).im := rfl
  rw [hcomp]
  refine (Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (N := 2) hP
    (by exact_mod_cast hk)).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [← iteratedFDerivWithin_of_isOpen k hs hxs]
  refine (norm_iteratedFDerivWithin_prod_le hfac hs.uniqueDiffOn hxs
    (by exact_mod_cast hk)).trans ?_
  refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  have hcnt : Multiset.count j (p : Multiset (Fin m)) ≤ 2 :=
    ((Multiset.count_le_card _ _).trans_eq p.2).trans hk
  rw [iteratedFDerivWithin_of_isOpen _ hs hxs]
  exact OUGenerator_norm_iteratedFDeriv_stieltjes_im_le hx (hz j) hcnt

end StieltjesTestFun

/-- **Target 3 (RBM1D `testFun'_stieltjesImProduct`, `:1342`, d = 2).**  A product of imaginary
parts of Stieltjes transforms at spectral parameters in the upper half-plane is a `TestFunH`:
`C²` near every Hermitian matrix and bounded value, first and second Fréchet derivatives there. -/
theorem testFunH_stieltjesImProduct (d L W : ℕ) [NeZero L] [NeZero W] (n : ℕ) (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    TestFunH d L W (fun K => ((∏ i, (RBM.Univ.stieltjesN K (z i)).im : ℝ) : ℂ)) := by
  obtain ⟨C0, hC0⟩ :=
    OUGenerator_norm_iteratedFDeriv_stieltjesImProduct_le (ι := Idx d L W) z hz (k := 0)
      (by norm_num)
  obtain ⟨C1, hC1⟩ :=
    OUGenerator_norm_iteratedFDeriv_stieltjesImProduct_le (ι := Idx d L W) z hz (k := 1)
      (by norm_num)
  obtain ⟨C2, hC2⟩ :=
    OUGenerator_norm_iteratedFDeriv_stieltjesImProduct_le (ι := Idx d L W) z hz (k := 2) le_rfl
  refine ⟨fun M hM => (hC0 M hM).1, ⟨C0, fun M hM => ?_⟩, ⟨C1, fun M hM => ?_⟩,
    ⟨C2, fun M hM => ?_⟩⟩
  · have h := (hC0 M hM).2
    rwa [norm_iteratedFDeriv_zero] at h
  · have h := (hC1 M hM).2
    rwa [norm_iteratedFDeriv_one] at h
  · have h := (hC2 M hM).2
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h

/-! ## Compiled nonempty instances (CLAUDE.md §4 step 2)

Pair carrier: `d = 3`, `L = 3`, `W = 2` (`N = 216`), `g = 1/2`; band carrier: `UNModel.band sz0`, `n = 0`
(`L = 4`, `W = 32`).  `z = ![I, 2 I]` (`Im z = 1, 2 > 0`), `Φ(K) = Im m(K, I) · Im m(K, 2I)`.  Every
hypothesis is discharged; no external hypothesis occurs. -/

namespace OUGeneratorInst

open RBM.Gauss.SizesInst

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `Φ(K) = Im m(K, I) · Im m(K, 2I)` (RBM2D `OUGeneratorCheck.Phi2`, `:1186`). -/
def Phi2 (K : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  ((∏ i : Fin 2, (stieltjesN K (![Complex.I, 2 * Complex.I] i)).im : ℝ) : ℂ)

theorem zIm_pos : ∀ i : Fin 2, 0 < (![Complex.I, 2 * Complex.I] i).im := by
  intro i
  fin_cases i <;> simp

/-- `Phi2` is a `TestFunH` at every size (target S at `z = ![I, 2 I]`). -/
theorem phi2_testFunH : TestFunH d L W (Phi2 d L W) :=
  testFunH_stieltjesImProduct d L W 2 ![Complex.I, 2 * Complex.I] zIm_pos

/-- `inst_testFunH`. -/
theorem inst_testFunH : TestFunH 3 3 2 (Phi2 3 3 2) := phi2_testFunH 3 3 2

/-- `inst_pair_sub_eq` (target P2 at `T = 1`, `g = 1/2`). -/
theorem inst_pair_sub_eq :
    (∫ ω, Phi2 3 3 2 (ouPairMat 3 3 2 1 ω) ∂(ouPairP 3 3 2 (1 / 2))) -
        ∫ ω, Phi2 3 3 2 (ouPairMat 3 3 2 0 ω) ∂(ouPairP 3 3 2 (1 / 2)) =
      ∫ t in (0 : ℝ)..1, (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx 3 3 2, ∑ b : Idx 3 3 2,
        (centeredVarianceEntry 3 3 2 (1 / 2) a b : ℂ) *
          ∫ ω, wirtSecond 3 3 2 (Phi2 3 3 2) (ouPairMat 3 3 2 t ω) a b ∂(ouPairP 3 3 2 (1 / 2)) :=
  ouGeneratorPair_integral_sub_eq 3 3 2 (1 / 2) _ inst_testFunH 1 zero_le_one

/-- `inst_band_hasDerivAt` (target B1 at `t = 1`). -/
theorem inst_band_hasDerivAt :
    HasDerivAt (fun s : ℝ => ∫ ω, Phi2 3 (sz0.L 0) (sz0.W 0) (ouMat (UNModel.band sz0) 0 s ω)
        ∂(ouP (UNModel.band sz0) 0))
      ((-(1 / 2 : ℝ) * Real.exp (-1)) •
        ∑ a : Idx 3 (sz0.L 0) (sz0.W 0), ∑ b : Idx 3 (sz0.L 0) (sz0.W 0),
          (centeredVarianceEntry 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) a b : ℂ) *
            ∫ ω, wirtSecond 3 (sz0.L 0) (sz0.W 0) (Phi2 3 (sz0.L 0) (sz0.W 0))
              (ouMat (UNModel.band sz0) 0 1 ω) a b ∂(ouP (UNModel.band sz0) 0)) 1 :=
  ouGenerator_hasDerivAt_integral 3 sz0 0 _ (phi2_testFunH 3 (sz0.L 0) (sz0.W 0)) 1 one_pos

/-- `inst_band_sub_eq` (target B2 at `T = ouTStar sz0 (1/2) 0`, the time `UNEMCTE2` reads). -/
theorem inst_band_sub_eq :
    (∫ ω, Phi2 3 (sz0.L 0) (sz0.W 0) (ouMat (UNModel.band sz0) 0 (ouTStar sz0 (1 / 2) 0) ω)
        ∂(ouP (UNModel.band sz0) 0)) -
        ∫ ω, Phi2 3 (sz0.L 0) (sz0.W 0) (ouMat (UNModel.band sz0) 0 0 ω) ∂(ouP (UNModel.band sz0) 0) =
      ∫ t in (0 : ℝ)..(ouTStar sz0 (1 / 2) 0), (-(1 / 2 : ℝ) * Real.exp (-t)) •
        ∑ a : Idx 3 (sz0.L 0) (sz0.W 0), ∑ b : Idx 3 (sz0.L 0) (sz0.W 0),
          (centeredVarianceEntry 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) a b : ℂ) *
            ∫ ω, wirtSecond 3 (sz0.L 0) (sz0.W 0) (Phi2 3 (sz0.L 0) (sz0.W 0))
              (ouMat (UNModel.band sz0) 0 t ω) a b ∂(ouP (UNModel.band sz0) 0) :=
  ouGenerator_integral_sub_eq 3 sz0 0 _ (phi2_testFunH 3 (sz0.L 0) (sz0.W 0)) _
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end OUGeneratorInst

end RBM.Univ

#print axioms RBM.Univ.TestFunH
#print axioms RBM.Univ.ouGeneratorPair_hasDerivAt_integral
#print axioms RBM.Univ.ouGeneratorPair_integral_sub_eq
#print axioms RBM.Univ.ouMat_band_eq_ouPairMat
#print axioms RBM.Univ.ouP_band_map_pair
#print axioms RBM.Univ.ouGenerator_hasDerivAt_integral
#print axioms RBM.Univ.ouGenerator_integral_sub_eq
#print axioms RBM.Univ.testFunH_stieltjesImProduct
#print axioms RBM.Univ.OUGeneratorInst.inst_testFunH
#print axioms RBM.Univ.OUGeneratorInst.inst_pair_sub_eq
#print axioms RBM.Univ.OUGeneratorInst.inst_band_hasDerivAt
#print axioms RBM.Univ.OUGeneratorInst.inst_band_sub_eq

end
