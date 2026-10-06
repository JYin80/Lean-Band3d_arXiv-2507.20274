/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.OUGenerator
import RBM3D.Universality.OUContraction
import RBM3D.Universality.OUHessian
import RBM3D.Universality.PinsK
import RBM3D.Universality.InjSum
import RBM3D.Path.Walk
import RBM3D.Gauss.FlowCalculus
import RBM3D.Induction.Split

/-!
# The weighted `(EMCTE2)` from the OU generator identity (T2266, UN-18, EMCTE2 half)

Paper: RBM2D paper `1-2:364–376` ("argue as in Step 3 of the proof of Theorem 2.6 in [YY_25]").
Port of RBM2D `Universality/EMCTE2.lean` (commit `c9a24cf`, 726 lines) onto the band carrier
`ouP (UNModel.band sz) n`, on top of the merged UN-15 forms B1/B2/S (`OUGenerator.lean`) and the UN-17
kernel bound (`OUContraction.lean`).

* `eq225_interval` (target 1): for `0 ≤ t ≤ T`, a bound `Bd` on the expected weighted kernel sum
  `E[∑_i (∏_{j≠i} Im m_j) L1t(z_i) + ∑_{i≠j} (∏_{k∉{i,j}} Im m_k) L2t(z_i,z_j)]` along the band OU flow
  on `(t, T)` bounds `|E ∏ Im m_t - E ∏ Im m_T| ≤ ½ (T - t) Bd`.
* `unEMCTE2_of_sizeTendsto` (target 2): the pin `UNEMCTE2 sz E nf τU Cn` at every size sequence with
  `N → ∞` and `τU ≤ Cn τU` (the merged pin has no size hypothesis; the step `½ nf² ≤ N^ε` needs
  `N → ∞`; paper-delta candidate T2266a (1)).
* `unEMCTE2Row` (target 3): the row `UNEMCTE2Row`, `Cn = 1`, `τ₀ = 1`.
* `unEMCTE2Rowk_band` (target 4): the model-generic row at the band kind.

Changes against RBM2D: `Idx L W` ↦ `Idx d (sz.L n) (sz.W n)`; `gSel`/`green` ↦ the merged `Gres`
(`Gres M z false = (M - z̄)⁻¹`), whose entries are measurable by `walk_measurable_Gres_apply` and
bounded by `norm_Gsig_le_inv_eta` with `norm_apply_le_l2_opNorm`; `L1t`, `L2t` carry `d` and `lam`; the
kernel bound is the merged `centeredVariance_wirtProduct_kernel_bound_Lt`; the measurability of
`ω ↦ wirtSecond Φ (ouMat (band) n s ω) a b` is by T1 (`ouMat_band_eq_ouPairMat`, `rfl`): continuous on
the pair carrier, composed with the measurable `Prod.map (slice sz n) id` (RBM2D used continuity of
`ouMat` on `Ω × Ω`); the final arithmetic carries a general `Cn` through `τU ≤ Cn τU`.
No `3 ≤ d` is used.
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

/-! ## 1. Bounded measurable functions (port of the private `UnivMain_BM` toolkit) -/

section BM

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- A bounded measurable function `Ω' → ℂ`. -/
private def EMCTE2_BM (f : Ω' → ℂ) : Prop :=
  Measurable f ∧ ∃ K : ℝ, ∀ ω, ‖f ω‖ ≤ K

private theorem EMCTE2_BM_const (c : ℂ) : EMCTE2_BM (fun _ : Ω' => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

private theorem EMCTE2_BM_add {f g : Ω' → ℂ} (hf : EMCTE2_BM f) (hg : EMCTE2_BM g) :
    EMCTE2_BM (fun ω => f ω + g ω) := by
  obtain ⟨hfm, Kf, hKf⟩ := hf
  obtain ⟨hgm, Kg, hKg⟩ := hg
  exact ⟨hfm.add hgm, Kf + Kg, fun ω => (norm_add_le _ _).trans (add_le_add (hKf ω) (hKg ω))⟩

private theorem EMCTE2_BM_mul {f g : Ω' → ℂ} (hf : EMCTE2_BM f) (hg : EMCTE2_BM g) :
    EMCTE2_BM (fun ω => f ω * g ω) := by
  obtain ⟨hfm, Kf, hKf⟩ := hf
  obtain ⟨hgm, Kg, hKg⟩ := hg
  refine ⟨hfm.mul hgm, |Kf| * |Kg|, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hKf ω).trans (le_abs_self _)) ((hKg ω).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

private theorem EMCTE2_BM_sum {ι : Type*} (s : Finset ι) {f : ι → Ω' → ℂ}
    (hf : ∀ i ∈ s, EMCTE2_BM (f i)) : EMCTE2_BM (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EMCTE2_BM_const (Ω' := Ω') 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact EMCTE2_BM_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem EMCTE2_BM_prod {ι : Type*} (s : Finset ι) {f : ι → Ω' → ℂ}
    (hf : ∀ i ∈ s, EMCTE2_BM (f i)) : EMCTE2_BM (fun ω => ∏ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EMCTE2_BM_const (Ω' := Ω') 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact EMCTE2_BM_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The real-valued norm of a bounded measurable function, as a complex-valued one. -/
private theorem EMCTE2_BM_norm {f : Ω' → ℂ} (hf : EMCTE2_BM f) :
    EMCTE2_BM (fun ω => ((‖f ω‖ : ℝ) : ℂ)) := by
  obtain ⟨hfm, K, hK⟩ := hf
  refine ⟨Complex.measurable_ofReal.comp hfm.norm, K, fun ω => ?_⟩
  simpa using hK ω

/-- The imaginary part of a bounded measurable function, as a complex-valued one. -/
private theorem EMCTE2_BM_im {f : Ω' → ℂ} (hf : EMCTE2_BM f) :
    EMCTE2_BM (fun ω => (((f ω).im : ℝ) : ℂ)) := by
  obtain ⟨hfm, K, hK⟩ := hf
  refine ⟨Complex.measurable_ofReal.comp (Complex.measurable_im.comp hfm), K, fun ω => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans (hK ω)

/-- A real function whose complex lift is bounded measurable is integrable on a finite measure. -/
private theorem EMCTE2_integrable_of_BM {f : Ω' → ℝ} (μ : Measure Ω') [IsFiniteMeasure μ]
    (hf : EMCTE2_BM (fun ω => ((f ω : ℝ) : ℂ))) : Integrable f μ := by
  obtain ⟨hfm, K, hK⟩ := hf
  have hm : Measurable f := by
    have h := Complex.measurable_re.comp hfm
    have h2 : (Complex.re ∘ fun ω => ((f ω : ℝ) : ℂ)) = f := by
      funext ω
      simp
    rwa [h2] at h
  refine Integrable.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall fun ω => ?_)
  simpa using hK ω

end BM

/-! ## 2. Measurability and boundedness of the resolvent entries (`Gres` bridge) -/

section GreenBM

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- `|Gres H z b x y| ≤ (Im z)⁻¹` for Hermitian `H`, `Im z > 0`, both signs `b`. -/
private theorem EMCTE2_norm_Gres_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (b : Bool) (x y : ι) :
    ‖Gres H z b x y‖ ≤ (z.im)⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (RBM.Gauss.norm_Gsig_le_inv_eta hH hz (le_of_eq (abs_of_pos hz).symm) b)

variable {d L W : ℕ} {lam : ℝ} [NeZero L] [NeZero W]

/-- Entries of `Gres` of a measurable Hermitian-valued `M` are bounded measurable. -/
private theorem EMCTE2_BM_Gres {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) (b : Bool) (x y : Idx d L W) :
    EMCTE2_BM (fun ω => Gres (M ω) z b x y) :=
  ⟨(RBM.Gauss.walk_measurable_Gres_apply z b x y).comp hM, (z.im)⁻¹,
    fun ω => EMCTE2_norm_Gres_entry_le (hH ω) hz b x y⟩

/-- Entries of a product `Gres(z₁,b₁) * Gres(z₂,b₂)`. -/
private theorem EMCTE2_BM_Gres_mul {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (b₁ b₂ : Bool) (x y : Idx d L W) :
    EMCTE2_BM (fun ω => (Gres (M ω) z₁ b₁ * Gres (M ω) z₂ b₂) x y) := by
  simp only [Matrix.mul_apply]
  exact EMCTE2_BM_sum _ fun c _ =>
    EMCTE2_BM_mul (EMCTE2_BM_Gres hM hH hz₁ b₁ x c) (EMCTE2_BM_Gres hM hH hz₂ b₂ c y)

/-- The normalized trace `m(z) = N⁻¹ tr G(z)` is bounded measurable. -/
private theorem EMCTE2_BM_stieltjes {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    EMCTE2_BM (fun ω => stieltjesN (M ω) z) := by
  have h : (fun ω => stieltjesN (M ω) z) =
      fun ω => (Fintype.card (Idx d L W) : ℂ)⁻¹ * ∑ i, Gres (M ω) z true i i := rfl
  rw [h]
  exact EMCTE2_BM_mul (EMCTE2_BM_const _)
    (EMCTE2_BM_sum _ fun i _ => EMCTE2_BM_Gres hM hH hz true i i)

/-- `Im m(z) ≥ 0` for Hermitian `H` and `Im z > 0`. -/
private theorem EMCTE2_im_stieltjesN_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (stieltjesN H z).im := by
  have h := stieltjesN_im_eq_normalized_specWeight H hH z.re z.im hz
  rw [Complex.re_add_im] at h
  rw [h]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun l _ => ?_)
  positivity

/-- `L1t` as a bounded measurable function (complex lift). -/
private theorem EMCTE2_BM_L1t {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    EMCTE2_BM (fun ω => ((L1t d L W lam (M ω) z : ℝ) : ℂ)) := by
  unfold L1t
  simp only [Complex.ofReal_sum]
  refine EMCTE2_BM_sum _ fun b₁ _ => EMCTE2_BM_sum _ fun b₂ _ => ?_
  exact EMCTE2_BM_norm (EMCTE2_BM_mul (EMCTE2_BM_const _)
    (EMCTE2_BM_sum _ fun a _ => EMCTE2_BM_sum _ fun b _ => EMCTE2_BM_mul
      (EMCTE2_BM_mul (EMCTE2_BM_Gres_mul hM hH hz hz b₁ b₁ a a) (EMCTE2_BM_const _))
      (EMCTE2_BM_Gres hM hH hz b₂ b b)))

/-- `L2t` as a bounded measurable function (complex lift). -/
private theorem EMCTE2_BM_L2t {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    EMCTE2_BM (fun ω => ((L2t d L W lam (M ω) z₁ z₂ : ℝ) : ℂ)) := by
  unfold L2t
  simp only [Complex.ofReal_sum]
  refine EMCTE2_BM_sum _ fun b₁ _ => EMCTE2_BM_sum _ fun b₂ _ => ?_
  exact EMCTE2_BM_norm (EMCTE2_BM_mul (EMCTE2_BM_const _)
    (EMCTE2_BM_sum _ fun a _ => EMCTE2_BM_sum _ fun b _ => EMCTE2_BM_mul
      (EMCTE2_BM_mul (EMCTE2_BM_Gres_mul hM hH hz₁ hz₁ b₁ b₁ a b) (EMCTE2_BM_const _))
      (EMCTE2_BM_Gres_mul hM hH hz₂ hz₂ b₂ b₂ b a)))

end GreenBM

/-! ## 3. Integrability and positivity of the weighted kernel integrands -/

section Terms

variable {Ω' : Type*} [MeasurableSpace Ω'] {d L W : ℕ} {lam : ℝ} [NeZero L] [NeZero W]

/-- `(∏_{j∈s} Im m(z_j)) · L1t(z_i)` is integrable along a measurable Hermitian-valued `M`. -/
private theorem EMCTE2_integrable_L1t_term (μ : Measure Ω') [IsFiniteMeasure μ]
    {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    {ι : Type*} (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) (i : ι) :
    Integrable (fun ω => (∏ j ∈ s, (stieltjesN (M ω) (zs j)).im) *
      L1t d L W lam (M ω) (zs i)) μ := by
  refine EMCTE2_integrable_of_BM μ ?_
  have h := EMCTE2_BM_mul
    (EMCTE2_BM_prod s fun j _ => EMCTE2_BM_im (EMCTE2_BM_stieltjes hM hH (hz j)))
    (EMCTE2_BM_L1t (lam := lam) hM hH (hz i))
  simpa [Complex.ofReal_mul, Complex.ofReal_prod] using h

/-- `(∏_{k∈s} Im m(z_k)) · L2t(z_i, z_j)` is integrable along a measurable Hermitian-valued `M`. -/
private theorem EMCTE2_integrable_L2t_term (μ : Measure Ω') [IsFiniteMeasure μ]
    {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    {ι : Type*} (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) (i j : ι) :
    Integrable (fun ω => (∏ k ∈ s, (stieltjesN (M ω) (zs k)).im) *
      L2t d L W lam (M ω) (zs i) (zs j)) μ := by
  refine EMCTE2_integrable_of_BM μ ?_
  have h := EMCTE2_BM_mul
    (EMCTE2_BM_prod s fun k _ => EMCTE2_BM_im (EMCTE2_BM_stieltjes hM hH (hz k)))
    (EMCTE2_BM_L2t (lam := lam) hM hH (hz i) (hz j))
  simpa [Complex.ofReal_mul, Complex.ofReal_prod] using h

/-- The weighted kernel sum of `eq225_interval` at a matrix `M`. -/
private def EMCTE2_hsum (d L W : ℕ) (lam : ℝ) [NeZero L] [NeZero W] {n : ℕ} (z : Fin n → ℂ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℝ :=
  (∑ i, (∏ j ∈ Finset.univ.erase i, (stieltjesN M (z j)).im) * L1t d L W lam M (z i)) +
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      (∏ k ∈ (Finset.univ.erase i).erase j, (stieltjesN M (z k)).im) * L2t d L W lam M (z i) (z j)

private theorem EMCTE2_integrable_hsum (μ : Measure Ω') [IsFiniteMeasure μ]
    {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).im) :
    Integrable (fun ω => EMCTE2_hsum d L W lam z (M ω)) μ := by
  unfold EMCTE2_hsum
  exact (integrable_finsetSum _ fun i _ => EMCTE2_integrable_L1t_term μ hM hH z hz _ i).add
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      EMCTE2_integrable_L2t_term μ hM hH z hz _ i j)

private theorem EMCTE2_hsum_nonneg {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : M.IsHermitian)
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).im) : 0 ≤ EMCTE2_hsum d L W lam z M := by
  have hL1 : ∀ w : ℂ, 0 ≤ L1t d L W lam M w := fun w =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL2 : ∀ w₁ w₂ : ℂ, 0 ≤ L2t d L W lam M w₁ w₂ := fun w₁ w₂ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hIm : ∀ i, 0 ≤ (stieltjesN M (z i)).im := fun i =>
    EMCTE2_im_stieltjesN_nonneg hH (hz i)
  unfold EMCTE2_hsum
  refine add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg
    (Finset.prod_nonneg fun j _ => hIm j) (hL1 _)) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (Finset.prod_nonneg fun k _ => hIm k) (hL2 _ _))

/-- The weighted kernel sum is a bounded measurable function (complex lift). -/
private theorem EMCTE2_BM_hsum {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).im) :
    EMCTE2_BM (fun ω => ((EMCTE2_hsum d L W lam z (M ω) : ℝ) : ℂ)) := by
  unfold EMCTE2_hsum
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]
  refine EMCTE2_BM_add (EMCTE2_BM_sum _ fun i _ => EMCTE2_BM_mul
    (EMCTE2_BM_prod _ fun j _ => EMCTE2_BM_im (EMCTE2_BM_stieltjes hM hH (hz j)))
    (EMCTE2_BM_L1t (lam := lam) hM hH (hz i))) (EMCTE2_BM_sum _ fun i _ =>
      EMCTE2_BM_sum _ fun j _ =>
      EMCTE2_BM_mul (EMCTE2_BM_prod _ fun k _ => EMCTE2_BM_im (EMCTE2_BM_stieltjes hM hH (hz k)))
        (EMCTE2_BM_L2t (lam := lam) hM hH (hz i) (hz j)))

end Terms

/-- The weighted kernel sum is bounded uniformly over Hermitian matrices (at fixed `z`). -/
private theorem EMCTE2_hsum_bdd (d L W : ℕ) (lam : ℝ) [NeZero L] [NeZero W] {n : ℕ}
    (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).im) :
    ∃ K : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      EMCTE2_hsum d L W lam z M ≤ K := by
  obtain ⟨-, K, hK⟩ := EMCTE2_BM_hsum (d := d) (L := L) (W := W) (lam := lam)
    (Ω' := {M : Matrix (Idx d L W) (Idx d L W) ℂ // M.IsHermitian}) (M := Subtype.val)
    measurable_subtype_coe (fun ω => ω.2) z hz
  refine ⟨K, fun M hM => ?_⟩
  have h := hK ⟨M, hM⟩
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-! ## 4. Integrability of the `wirtSecond` terms along the band flow (the Hermitian bounds of
`TestFunH`; measurability by T1 and `measurable_slice`) -/

section Wirt

variable {d L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ}

private theorem EMCTE2_continuousAt_fderiv2 (h : TestFunH d L W Φ)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContinuousAt (fderiv ℝ (fderiv ℝ Φ)) M :=
  (((h.1 M hM).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
    (by norm_num)).continuousAt

private theorem EMCTE2_continuous_comp {α E : Type*} [TopologicalSpace α]
    [TopologicalSpace E] {F : Matrix (Idx d L W) (Idx d L W) ℂ → E}
    (hF : ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ContinuousAt F M)
    {f : α → Matrix (Idx d L W) (Idx d L W) ℂ} (hf : Continuous f) (hherm : ∀ a, (f a).IsHermitian) :
    Continuous fun a => F (f a) :=
  continuous_iff_continuousAt.2 fun a => (hF _ (hherm a)).comp hf.continuousAt

private theorem EMCTE2_continuous_coordD2 (h : TestFunH d L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx d L W) (Idx d L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (p : CoordF d L W) :
    Continuous fun a => coordD2 d L W Φ (f a) p :=
  ((EMCTE2_continuous_comp (fun M hM => EMCTE2_continuousAt_fderiv2 h hM) hf
    hherm).clm_apply continuous_const).clm_apply continuous_const

private theorem EMCTE2_norm_coordD2_le {C : ℝ}
    (hC : ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (p : CoordF d L W) :
    ‖coordD2 d L W Φ M p‖
      ≤ C * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖ * ‖RBM.Green.Bmat d L W p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat d L W p.1 p.2.1 p.2.2)).le_opNorm _)
    (mul_le_mul_of_nonneg_right
      (le_trans ((fderiv ℝ (fderiv ℝ Φ) M).le_opNorm _)
        (mul_le_mul_of_nonneg_right (hC M hM) (norm_nonneg _))) (norm_nonneg _))

/-- A global bound on `wirtSecond` at Hermitian matrices, for a fixed index pair. -/
private theorem EMCTE2_exists_bound_wirtSecond (h : TestFunH d L W Φ) (a b : Idx d L W) :
    ∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ‖wirtSecond d L W Φ M a b‖ ≤ C := by
  obtain ⟨C₂, hC₂⟩ := h.2.2.2
  rcases eq_or_ne a b with rfl | hab
  · refine ⟨C₂ * ‖RBM.Green.Bmat d L W a a true‖ * ‖RBM.Green.Bmat d L W a a true‖,
      fun M hM => ?_⟩
    unfold wirtSecond
    rw [ite_eq_left rfl]
    exact EMCTE2_norm_coordD2_le hC₂ hM (a, a, true)
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
          · exact EMCTE2_norm_coordD2_le hC₂ hM (a, b, true)
          · exact EMCTE2_norm_coordD2_le hC₂ hM (a, b, false)

private theorem EMCTE2_continuous_wirtSecond_comp (h : TestFunH d L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx d L W) (Idx d L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (i j : Idx d L W) :
    Continuous fun a => wirtSecond d L W Φ (f a) i j := by
  unfold wirtSecond
  by_cases hij : i = j
  · simp only [hij, ite_true]
    exact EMCTE2_continuous_coordD2 h hf hherm (j, j, true)
  · simp only [hij, ite_false]
    exact ((EMCTE2_continuous_coordD2 h hf hherm (i, j, true)).add
      (EMCTE2_continuous_coordD2 h hf hherm (i, j, false))).const_smul (1 / 4 : ℝ)

private theorem EMCTE2_continuous_ouPairMat (s : ℝ) :
    Continuous fun z : Ω d L W × Ω d L W => ouPairMat d L W s z :=
  (((continuous_Xmat d L W).comp continuous_fst).const_smul (Real.exp (-s / 2))).add
    (((continuous_Xmat d L W).comp continuous_snd).const_smul (Real.sqrt (1 - Real.exp (-s))))

private theorem EMCTE2_ouPairMat_isHermitian (s : ℝ) (z : Ω d L W × Ω d L W) :
    (ouPairMat d L W s z).IsHermitian :=
  ((Xmat_isHermitian d L W z.1).smul (IsSelfAdjoint.all _)).add
    ((Xmat_isHermitian d L W z.2).smul (IsSelfAdjoint.all _))

end Wirt

section WirtBand

variable {d : ℕ} (sz : Sizes d) (n : ℕ)
  {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}

/-- Each `wirtSecond` term along the band flow is integrable: by T1 it is a continuous function of the
sliced pair, composed with the measurable `Prod.map (slice sz n) id`. -/
private theorem EMCTE2_integrable_wirtSecond (h : TestFunH d (sz.L n) (sz.W n) Φ) (s : ℝ)
    (a b : Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b)
      (ouP (UNModel.band sz) n) := by
  obtain ⟨C, hC⟩ := EMCTE2_exists_bound_wirtSecond h a b
  have hc := EMCTE2_continuous_wirtSecond_comp h (EMCTE2_continuous_ouPairMat s)
    (fun z => EMCTE2_ouPairMat_isHermitian s z) a b
  have hm : Measurable (Prod.map (Sizes.slice sz n)
      (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n))) :=
    (measurable_slice sz n).prodMap measurable_id
  exact Integrable.of_bound (hc.measurable.comp hm).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ (ouMat_isHermitian (UNModel.band sz) n s ω))

/-- `∑ a b, S°_{ab} ∫ wirtSecond a b = ∫ ∑ a b, S°_{ab} wirtSecond a b`. -/
private theorem EMCTE2_sum_integral_swap (h : TestFunH d (sz.L n) (sz.W n) Φ) (s : ℝ) :
    ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
        (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n) =
      ∫ ω, ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
        (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n) := by
  have hb : ∀ a : Idx d (sz.L n) (sz.W n),
      (∑ b : Idx d (sz.L n) (sz.W n),
        (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n)) =
      ∫ ω, ∑ b : Idx d (sz.L n) (sz.W n),
        (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n) := by
    intro a
    have hterm : ∀ b : Idx d (sz.L n) (sz.W n),
        (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
          ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
            ∂(ouP (UNModel.band sz) n) =
        ∫ ω, (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
          wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
            ∂(ouP (UNModel.band sz) n) := by
      intro b
      rw [MeasureTheory.integral_const_mul]
    rw [Finset.sum_congr rfl fun b _ => hterm b,
      MeasureTheory.integral_finsetSum Finset.univ
        (fun b _ => (EMCTE2_integrable_wirtSecond sz n h s a b).const_mul _)]
  rw [Finset.sum_congr rfl fun a _ => hb a,
    MeasureTheory.integral_finsetSum Finset.univ
      (fun a _ => integrable_finsetSum Finset.univ
        (fun b _ => (EMCTE2_integrable_wirtSecond sz n h s a b).const_mul _))]

end WirtBand

/-! ## 5. Target 1: `eq225_interval` -/

/-- **Target 1 (RBM1D `eq225`, `Flow/GreenComparisonOU.lean:607`; RBM2D `EMCTE2.lean:440`), band carrier at
size `n`, on `[t, T]`.**  A bound `Bd` on the expected weighted kernels `L1t`, `L2t` along the OU flow on
`(t, T)` bounds the change of `E ∏ Im m` between the times `t` and `T` by `½ (T - t) Bd`
(1-2:364–376; hypotheses on the spectral parameters: `0 < Im z_i` only). -/
theorem eq225_interval (d : ℕ) (sz : Sizes d) (n nf : ℕ) (z : Fin nf → ℂ)
    (hz : ∀ i : Fin nf, 0 < (z i).im) (t T Bd : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (hB : ∀ s ∈ Set.Ioo t T,
      ∫ ω, ((∑ i : Fin nf, (∏ j ∈ Finset.univ.erase i,
              (stieltjesN (ouMat (UNModel.band sz) n s ω) (z j)).im) *
              L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i)) +
            ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i,
              (∏ k ∈ (Finset.univ.erase i).erase j,
                (stieltjesN (ouMat (UNModel.band sz) n s ω) (z k)).im) *
              L2t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i) (z j))
        ∂(ouP (UNModel.band sz) n) ≤ Bd) :
    |(∫ ω, ∏ i : Fin nf, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z i)).im
          ∂(ouP (UNModel.band sz) n)) -
      ∫ ω, ∏ i : Fin nf, (stieltjesN (ouMat (UNModel.band sz) n T ω) (z i)).im
          ∂(ouP (UNModel.band sz) n)| ≤
      (1 / 2) * (T - t) * Bd := by
  classical
  set Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
    fun K => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ) with hΦdef
  have hΦ : TestFunH d (sz.L n) (sz.W n) Φ := testFunH_stieltjesImProduct d (sz.L n) (sz.W n) nf z hz
  set F : ℝ → ℂ := fun s => ∫ ω, Φ (ouMat (UNModel.band sz) n s ω) ∂(ouP (UNModel.band sz) n)
    with hFdef
  set g : ℝ → ℂ := fun s => (-(1 / 2 : ℝ) * Real.exp (-s)) •
      ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
      (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n) with hgdef
  have hcast : ∀ s : ℝ, F s =
      ((∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n s ω) (z i)).im
        ∂(ouP (UNModel.band sz) n) : ℝ) : ℂ) := by
    intro s
    simp only [hFdef, hΦdef]
    exact integral_ofReal
  have hFd : ∀ s : ℝ, 0 < s → HasDerivAt F (g s) s := fun s hs =>
    ouGenerator_hasDerivAt_integral d sz n Φ hΦ s hs
  have hFT : F T - F 0 = ∫ s in (0 : ℝ)..T, g s :=
    ouGenerator_integral_sub_eq d sz n Φ hΦ T (ht.trans htT)
  have hFt : F t - F 0 = ∫ s in (0 : ℝ)..t, g s :=
    ouGenerator_integral_sub_eq d sz n Φ hΦ t ht
  -- the hypothesis forces `0 ≤ Bd` as soon as `(t, T)` is nonempty
  have hBd : t < T → 0 ≤ Bd := by
    intro htT'
    have hmid : (t + T) / 2 ∈ Set.Ioo t T := ⟨by linarith, by linarith⟩
    refine le_trans ?_ (hB _ hmid)
    exact integral_nonneg fun ω =>
      EMCTE2_hsum_nonneg (lam := sz.lam n) (ouMat_isHermitian (UNModel.band sz) n _ ω) z hz
  -- the norm of the weighted sum of expected Hessians is at most `Bd`
  have hS : ∀ s ∈ Set.Ioo t T,
      ‖∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
        (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n)‖ ≤ Bd := by
    intro s hs
    rw [EMCTE2_sum_integral_swap sz n hΦ s]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hbound : ∀ᵐ ω ∂(ouP (UNModel.band sz) n),
        ‖∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
          (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
          wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b‖ ≤
          EMCTE2_hsum d (sz.L n) (sz.W n) (sz.lam n) z (ouMat (UNModel.band sz) n s ω) := by
      refine Filter.Eventually.of_forall fun ω => ?_
      have hH := ouMat_isHermitian (UNModel.band sz) n s ω
      exact centeredVariance_wirtProduct_kernel_bound_Lt d (sz.L n) (sz.W n) (sz.lam n)
        (Finset.univ : Finset (Fin nf)) (ouMat (UNModel.band sz) n s ω) hH z (fun i _ => hz i)
    exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
      (EMCTE2_integrable_hsum (ouP (UNModel.band sz) n) (measurable_ouMat (UNModel.band sz) n s)
        (ouMat_isHermitian (UNModel.band sz) n s) z hz)
      hbound).trans (hB s hs)
  -- the generator integrand is bounded by `½ Bd` on `(t, T)` (`e^{-s} ≤ 1` for `s ≥ 0`)
  have hg : ∀ s ∈ Set.Ioo t T, ‖g s‖ ≤ (1 / 2) * Bd := by
    intro s hs
    have hS' := hS s hs
    have hexp : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    have hexppos : 0 < Real.exp (-s) := Real.exp_pos _
    have habs : ‖(-(1 / 2 : ℝ) * Real.exp (-s))‖ = (1 / 2 : ℝ) * Real.exp (-s) := by
      rw [Real.norm_eq_abs, abs_of_neg (by nlinarith [hexppos])]
      ring
    have hSnn := norm_nonneg (∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
      (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n))
    calc ‖g s‖ = ‖(-(1 / 2 : ℝ) * Real.exp (-s))‖ *
          ‖∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
          (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
            ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
              ∂(ouP (UNModel.band sz) n)‖ := by
          rw [hgdef]; exact norm_smul _ _
      _ ≤ (1 / 2 : ℝ) * Bd := by
          rw [habs]
          nlinarith [mul_le_mul_of_nonneg_right hexp hSnn, hS']
  -- `g` is interval integrable on `[t, T]`: it is `deriv F` (measurable) on `(0, ∞)` and bounded
  have hIntTT : IntervalIntegrable g MeasureTheory.volume t T := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le htT]
    have hm : AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioc t T)) := by
      have hm' : AEStronglyMeasurable (deriv F)
          (MeasureTheory.volume.restrict (Set.Ioc t T)) :=
        (measurable_deriv F).aestronglyMeasurable
      refine hm'.congr ?_
      exact (ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun s hs => (hFd s (lt_of_le_of_lt ht hs.1)).deriv)
    refine Integrable.of_bound (C := (1 / 2) * Bd) hm ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [MeasureTheory.volume.ae_ne T] with s hsne hs
    exact hg s ⟨hs.1, hs.2.lt_of_ne hsne⟩
  have hnn : 0 ≤ (1 / 2 * Bd) * |T - t| := by
    rcases eq_or_lt_of_le htT with h | h
    · simp [h]
    · exact mul_nonneg (by have := hBd h; positivity) (abs_nonneg _)
  have hmain : ‖F T - F t‖ ≤ (1 / 2 * Bd) * |T - t| := by
    by_cases h0t : IntervalIntegrable g MeasureTheory.volume 0 t
    · have hsum := intervalIntegral.integral_add_adjacent_intervals h0t hIntTT
      have hdiff : F T - F t = ∫ s in t..T, g s := by
        linear_combination hFT - hFt - hsum
      rw [hdiff]
      refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
      filter_upwards [MeasureTheory.volume.ae_ne T] with s hsne hs
      rw [Set.uIoc_of_le htT] at hs
      exact hg s ⟨hs.1, hs.2.lt_of_ne hsne⟩
    · have hnot : ¬ IntervalIntegrable g MeasureTheory.volume 0 T := fun h =>
        h0t (h.mono_set (by
          rw [Set.uIcc_of_le ht, Set.uIcc_of_le (ht.trans htT)]
          exact Set.Icc_subset_Icc_right htT))
      rw [intervalIntegral.integral_undef hnot] at hFT
      rw [intervalIntegral.integral_undef h0t] at hFt
      have : F T - F t = 0 := by linear_combination hFT - hFt
      rw [this, norm_zero]
      exact hnn
  calc _ = |(∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n T ω) (z i)).im
            ∂(ouP (UNModel.band sz) n)) -
        ∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z i)).im
            ∂(ouP (UNModel.band sz) n)| := abs_sub_comm _ _
    _ = ‖F T - F t‖ := by
        rw [hcast T, hcast t, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / 2 * Bd) * |T - t| := hmain
    _ = (1 / 2) * (T - t) * Bd := by rw [abs_of_nonneg (sub_nonneg.2 htT)]; ring

/-! ## 6. Targets 2-4: the pin, the row, the band-kind row -/

/-- **Target 2 (the pin `UNEMCTE2`, `Pins.lean`; RBM2D `emcte2Row`, `EMCTE2.lean:567`, at general `Cn`).**
At every size sequence with `N → ∞` and `τU ≤ Cn τU`: for `0 ≤ t ≤ t*`,
`|E ∏ Im m_t - E ∏ Im m_{t*}| ≤ ½ (t* - t) nf² B ≤ ½ nf² N^{-1+τU} B ≤ N^ε N^{-1+Cn τU} B` once
`½ nf² ≤ N^ε` (eventually in `n`, `N → ∞`); `nf = 0` is `un_emcte2_zero`.  `E` is not used. -/
theorem unEMCTE2_of_sizeTendsto (d : ℕ) (sz : Sizes d) (hd : sz.SizeTendsto) (E : ℝ) (nf : ℕ)
    (τU Cn : ℝ) (hτ : τU ≤ Cn * τU) : UNEMCTE2 sz E nf τU Cn := by
  rcases Nat.eq_zero_or_pos nf with rfl | hpos
  · exact UNInst.un_emcte2_zero sz E τU Cn
  intro C₀ ε hC₀ hε
  have hNε : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp hd
  filter_upwards [hNε.eventually_ge_atTop ((1 / 2) * (nf : ℝ) ^ 2)] with n hn
  intro z hz B hB0 hB1 hB2 t ht htT
  have hNnat : 0 < sz.size n := by
    simp only [Sizes.size]
    have := sz.three_le_L n
    have := sz.W_pos n
    positivity
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hNnat
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hNnat
  have hzim : ∀ i, 0 < (z i).im := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (hz i).2.1
  have hT0 : 0 ≤ ouTStar sz τU n := Real.rpow_nonneg hNpos.le _
  have hnf : 0 ≤ (nf : ℝ) ^ 2 * B := by positivity
  have key := eq225_interval d sz n nf z hzim t (ouTStar sz τU n) ((nf : ℝ) ^ 2 * B)
    ht htT (fun s hs => by
      have hs0 : 0 ≤ s := ht.trans hs.1.le
      have hsT : s ≤ ouTStar sz τU n := hs.2.le
      have hH := ouMat_isHermitian (UNModel.band sz) n s
      have hM := measurable_ouMat (UNModel.band sz) n s
      have iL1 := fun i => EMCTE2_integrable_L1t_term (lam := sz.lam n) (ouP (UNModel.band sz) n)
        hM hH z hzim (Finset.univ.erase i) i
      have iL2 := fun i j => EMCTE2_integrable_L2t_term (lam := sz.lam n)
        (ouP (UNModel.band sz) n) hM hH z hzim ((Finset.univ.erase i).erase j) i j
      rw [integral_add (integrable_finsetSum _ fun i _ => iL1 i)
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iL2 i j),
        integral_finsetSum _ fun i _ => iL1 i,
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iL2 i j]
      have e2 : ∀ i, ∫ ω, ∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j,
            (stieltjesN (ouMat (UNModel.band sz) n s ω) (z k)).im) *
            L2t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i) (z j)
              ∂(ouP (UNModel.band sz) n) =
          ∑ j ∈ Finset.univ.erase i, ∫ ω, (∏ k ∈ (Finset.univ.erase i).erase j,
            (stieltjesN (ouMat (UNModel.band sz) n s ω) (z k)).im) *
            L2t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i) (z j)
              ∂(ouP (UNModel.band sz) n) := fun i =>
        integral_finsetSum _ fun j _ => iL2 i j
      simp only [e2]
      have h1 : ∑ i : Fin nf, ∫ ω, (∏ j ∈ Finset.univ.erase i,
          (stieltjesN (ouMat (UNModel.band sz) n s ω) (z j)).im) *
          L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i)
            ∂(ouP (UNModel.band sz) n) ≤
          ∑ _i : Fin nf, B := Finset.sum_le_sum fun i _ => hB1 s hs0 hsT i
      have h2 : ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i, ∫ ω, (∏ k ∈ (Finset.univ.erase i).erase j,
          (stieltjesN (ouMat (UNModel.band sz) n s ω) (z k)).im) *
          L2t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i) (z j)
            ∂(ouP (UNModel.band sz) n) ≤ ∑ _i : Fin nf, ∑ _j ∈ Finset.univ.erase _i, B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
          hB2 s hs0 hsT i j (Finset.ne_of_mem_erase hj).symm
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Finset.card_erase_of_mem (Finset.mem_univ _), nsmul_eq_mul]
      rw [Nat.cast_sub hpos]
      push_cast
      ring)
  refine key.trans ?_
  have hq : (1 / 2 : ℝ) * (ouTStar sz τU n - t) * ((nf : ℝ) ^ 2 * B) ≤
      (1 / 2 : ℝ) * ouTStar sz τU n * ((nf : ℝ) ^ 2 * B) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_self (ouTStar sz τU n) ht) (by norm_num : (0 : ℝ) ≤ 1 / 2))
      hnf
  refine hq.trans ?_
  have hTB : 0 ≤ ouTStar sz τU n * B := mul_nonneg hT0 hB0
  have h3 : (1 / 2 : ℝ) * ouTStar sz τU n * ((nf : ℝ) ^ 2 * B) =
      ((1 / 2) * (nf : ℝ) ^ 2) * (ouTStar sz τU n * B) := by ring
  have hexp : ouTStar sz τU n ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + Cn * τU) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h4 : ((sz.size n : ℕ) : ℝ) ^ ε * ouTStar sz τU n * B ≤
      ((sz.size n : ℕ) : ℝ) ^ ε * ((sz.size n : ℕ) : ℝ) ^ (-1 + Cn * τU) * B :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hNpos.le _)) hB0
  calc _ = ((1 / 2) * (nf : ℝ) ^ 2) * (ouTStar sz τU n * B) := h3
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (ouTStar sz τU n * B) :=
        mul_le_mul_of_nonneg_right hn hTB
    _ = ((sz.size n : ℕ) : ℝ) ^ ε * ouTStar sz τU n * B := by ring
    _ ≤ _ := h4

/-- **Target 3 (row `UNEMCTE2Row`; RBM2D `emcte2Row`, `EMCTE2.lean:567`).**  `Cn = 1`, `τ₀ = 1`; the size
hypothesis is the third conjunct of `Admissible`; `|E| ≤ 2 - κ` is not used. -/
theorem unEMCTE2Row : UNEMCTE2Row := by
  intro d _ 𝔠 𝔡 sz hA κ _ E _ nf
  exact ⟨1, 1, one_pos, fun τU _ _ =>
    unEMCTE2_of_sizeTendsto d sz hA.2.2.1 E nf τU 1 (one_mul τU).ge⟩

/-- **Target 4.**  The model-generic row at the band kind (`UNEMCTE2k_band`, `PinsK.lean`); the bulk
premise `∀ᶠ n, (UNKind.band d).bulk sz κ E n` is not used. -/
theorem unEMCTE2Rowk_band : UNEMCTE2Rowk (fun d => UNKind.band d) := by
  intro d _ 𝔠 𝔡 sz hA κ _ E _ nf
  exact ⟨1, 1, one_pos, fun τU _ _ =>
    (UNEMCTE2k_band sz E nf τU 1).2
      (unEMCTE2_of_sizeTendsto d sz hA.2.2.1 E nf τU 1 (one_mul τU).ge)⟩

/-! ## Compiled nonempty instances (CLAUDE.md §4 step 2)

`d = 3`, `sz0` (`L 0 = 4`, `W 0 = 32`, `N = 2^21`), `n = 0`.
* `inst_eq225_interval`: target 1 at `nf = 1`, `z = ![I]`, `t = 0`, `T = 1`, the kernel hypothesis
  discharged by the uniform bound of the kernel sum over Hermitian matrices.
* `inst_unEMCTE2_sz0`: target 2 at `sz0` (`sz0_tendsto`), `E = 0`, `nf = 2`, `τU = 1/2`, `Cn = 1`.
* `inst_unEMCTE2Row_sz0`: target 3 at `𝔠 = 1/6`, `𝔡 = 1/10`, `sz0` (`UNInst.sz0_adm`), `κ = 1/2`,
  `E = 1`, `nf = 2`.
* `inst_unEMCTE2Rowk_band_sz0`: target 4 at the same data. -/

namespace EMCTE2Inst

open RBM.Gauss.SizesInst

theorem inst_eq225_interval : ∃ Bd : ℝ,
    (∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, ((∑ i : Fin 1, (∏ j ∈ Finset.univ.erase i,
              (stieltjesN (ouMat (UNModel.band sz0) 0 s ω) (![Complex.I] j)).im) *
              L1t 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (ouMat (UNModel.band sz0) 0 s ω)
                (![Complex.I] i)) +
            ∑ i : Fin 1, ∑ j ∈ Finset.univ.erase i,
              (∏ k ∈ (Finset.univ.erase i).erase j,
                (stieltjesN (ouMat (UNModel.band sz0) 0 s ω) (![Complex.I] k)).im) *
              L2t 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (ouMat (UNModel.band sz0) 0 s ω)
                (![Complex.I] i) (![Complex.I] j))
        ∂(ouP (UNModel.band sz0) 0) ≤ Bd) ∧
    |(∫ ω, ∏ i : Fin 1, (stieltjesN (ouMat (UNModel.band sz0) 0 0 ω) (![Complex.I] i)).im
          ∂(ouP (UNModel.band sz0) 0)) -
      ∫ ω, ∏ i : Fin 1, (stieltjesN (ouMat (UNModel.band sz0) 0 1 ω) (![Complex.I] i)).im
          ∂(ouP (UNModel.band sz0) 0)| ≤
      (1 / 2) * (1 - 0) * Bd := by
  have hz : ∀ i : Fin 1, 0 < (![Complex.I] i).im := fun i => by fin_cases i; simp
  obtain ⟨K, hK⟩ := EMCTE2_hsum_bdd 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) ![Complex.I] hz
  have hB : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, ((∑ i : Fin 1, (∏ j ∈ Finset.univ.erase i,
              (stieltjesN (ouMat (UNModel.band sz0) 0 s ω) (![Complex.I] j)).im) *
              L1t 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (ouMat (UNModel.band sz0) 0 s ω)
                (![Complex.I] i)) +
            ∑ i : Fin 1, ∑ j ∈ Finset.univ.erase i,
              (∏ k ∈ (Finset.univ.erase i).erase j,
                (stieltjesN (ouMat (UNModel.band sz0) 0 s ω) (![Complex.I] k)).im) *
              L2t 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (ouMat (UNModel.band sz0) 0 s ω)
                (![Complex.I] i) (![Complex.I] j))
        ∂(ouP (UNModel.band sz0) 0) ≤ K := by
    intro s _
    calc _ ≤ ∫ _ω, K ∂(ouP (UNModel.band sz0) 0) :=
          integral_mono (EMCTE2_integrable_hsum (lam := sz0.lam 0) (ouP (UNModel.band sz0) 0)
            (measurable_ouMat (UNModel.band sz0) 0 s)
            (ouMat_isHermitian (UNModel.band sz0) 0 s) ![Complex.I] hz) (integrable_const K)
            (fun ω => hK _ (ouMat_isHermitian (UNModel.band sz0) 0 s ω))
      _ = K := by simp
  exact ⟨K, hB, eq225_interval 3 sz0 0 1 ![Complex.I] hz 0 1 K le_rfl zero_le_one hB⟩

theorem inst_unEMCTE2_sz0 : UNEMCTE2 sz0 0 2 (1 / 2) 1 :=
  unEMCTE2_of_sizeTendsto 3 sz0 sz0_tendsto 0 2 (1 / 2) 1 (one_mul _).ge

theorem inst_unEMCTE2Row_sz0 : ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧ UNEMCTE2 sz0 1 2 τ₀ Cn := by
  obtain ⟨Cn, τ₀, hτ₀, h⟩ := unEMCTE2Row 3 le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm (1 / 2)
    (by norm_num) 1 (by norm_num) 2
  exact ⟨Cn, τ₀, hτ₀, h τ₀ hτ₀ le_rfl⟩

theorem inst_unEMCTE2Rowk_band_sz0 : ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
    UNEMCTE2k (UNKind.band 3) sz0 1 2 τ₀ Cn := by
  obtain ⟨Cn, τ₀, hτ₀, h⟩ := unEMCTE2Rowk_band 3 le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm
    (1 / 2) (by norm_num) 1 (Eventually.of_forall fun n => by
      change |(1 : ℝ)| ≤ 2 - 1 / 2
      norm_num) 2
  exact ⟨Cn, τ₀, hτ₀, h τ₀ hτ₀ le_rfl⟩

end EMCTE2Inst

end RBM.Univ

#print axioms RBM.Univ.eq225_interval
#print axioms RBM.Univ.unEMCTE2_of_sizeTendsto
#print axioms RBM.Univ.unEMCTE2Row
#print axioms RBM.Univ.unEMCTE2Rowk_band
#print axioms RBM.Univ.EMCTE2Inst.inst_eq225_interval
#print axioms RBM.Univ.EMCTE2Inst.inst_unEMCTE2_sz0
#print axioms RBM.Univ.EMCTE2Inst.inst_unEMCTE2Row_sz0
#print axioms RBM.Univ.EMCTE2Inst.inst_unEMCTE2Rowk_band_sz0

end
