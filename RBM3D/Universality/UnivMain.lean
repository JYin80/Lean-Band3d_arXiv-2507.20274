/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Apriori
import RBM3D.Universality.GreenCorr
import RBM3D.Universality.EigenMeasurable
import RBM3D.Universality.PinsK
import RBM3D.Universality.PinsC2
import RBM3D.Universality.GUETranslation
import RBM3D.Path.Walk
import RBM3D.Universality.EMCTE2
import RBM3D.Universality.Uyw

/-!
# The arithmetic statements of the bulk-universality chain

The statements `UNUnivMainRow` and `UNClaimRow` (`Pins.lean`) are proved here, together with the centred forms
for every centred model.

Paper: arXiv:2507.20274, the proof of Theorem 2.4 `Thm: B_Univ` (the comparison of `H` with `𝐇_{t*}` and the Claim
[DYYY25, (2.20)]); the arguments are those of [DYYY25] for the comparison of `H` with `𝐇_{t*}` and for the Claim,
[DYYY25, (2.21)], [DYYY25, (2.22)], [DYYY25, (2.23)].  The proofs follow the two-dimensional formalization
(`UnivMain` of RBM2D).

* `unClaim417C_of_rows`: the arithmetic core, for every model class `K : UNKind d`:
  `UNEMCTE2k`, `UNJakk`, `UNUywk` give `UNClaim417C` with `C_n' = C_n + C + 1`.
* `unClaimRowk`: the model-generic statement `UNClaimRowk` (`PinsK.lean`).
* `unClaimRow`: the band statement `UNClaimRow`, `UNClaimRowk_band.1 (unClaimRowk _)`.
* `unDens_rho_bounds`: the density of `UNDens` is eventually in `[c/π, C/π]`.
* `univMain_transfer`: the law transfer at `t = 0`, for every test function.
* `univMainRow`: the statement `UNUnivMainRow`.
* The centred forms for every centred model `M : UNModelC sz`: `un_infty1RowC''` (the centred comparison of
  `𝐇_{t*}` with the GUE at every GUE energy, from `step1Band_rowC''` and `guetranslation`),
  `univMain_transferC`, `univMainRowC` (the centred comparison of `H` with `𝐇_{t*}`), `unCoreC''_holds`
  (the statement `UNCoreC''`, `PinsC2.lean`).

Correspondence with RBM2D (RBM2D declaration -> here):
* `UnivMain_BM*` -> same names (private, verbatim).
* `UnivMain_measurable_matrix_inv_apply` -> not needed: `walk_measurable_Gres_apply`
  (`Path/Walk.lean`) composed with the measurable matrix map.
* `UnivMain_norm_green_entry_le` (uses `RBM.Gauss.norm_green_le`, no counterpart here) ->
  private copy of the entry bound `norm_Gres_entry_le` (private in `Loop/GLoopFlow.lean`), at `η = Im z`.
* `gSel L W M z b` -> `Gres M z b` (`Gres M z false = (M - z̄)⁻¹`: the RBM2D `conjTranspose` case
  split disappears).
* `UnivMain_BM_stieltjes` -> `stieltjesN M z = N⁻¹ tr Gres M z true`; `UnivMain_im_stieltjesN_nonneg` -> same
  proof with `stieltjesN_im_eq_normalized_specWeight` (`Universality/InjSum.lean`).
* the `L1t`/`L2t` bounds -> `Idx d L W`, `(W L)^d`, the extra argument `lam`.
* `UnivMain_claim417_of` -> `unClaim417C_of_rows` (generic `K`: `ouMatC`, `ouP (K.M sz).toUNModel`,
  `K.lamV`; measurability of `ouMatC` from `ouMatC_eq_ouMat_add`).
* `claimRow` -> `unClaimRowk`, `unClaimRow`.
* `univMainRow` -> `univMainRow` (new: the dilation `ρ` of `UNGreenCorr` with the range of
  `unDens_rho_bounds`; the transfer is `univMain_transfer` by `apriori_ouMat_zero_integral`, no measurability).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology
open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ### Bounded measurable complex-valued functions -/

section BM

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- A bounded measurable function `Ω' → ℂ`. -/
private def UnivMain_BM (f : Ω' → ℂ) : Prop :=
  Measurable f ∧ ∃ K : ℝ, ∀ ω, ‖f ω‖ ≤ K

private theorem UnivMain_BM_const (c : ℂ) : UnivMain_BM (fun _ : Ω' => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

private theorem UnivMain_BM_add {f g : Ω' → ℂ} (hf : UnivMain_BM f) (hg : UnivMain_BM g) :
    UnivMain_BM (fun ω => f ω + g ω) := by
  obtain ⟨hfm, Kf, hKf⟩ := hf
  obtain ⟨hgm, Kg, hKg⟩ := hg
  exact ⟨hfm.add hgm, Kf + Kg, fun ω => (norm_add_le _ _).trans (add_le_add (hKf ω) (hKg ω))⟩

private theorem UnivMain_BM_mul {f g : Ω' → ℂ} (hf : UnivMain_BM f) (hg : UnivMain_BM g) :
    UnivMain_BM (fun ω => f ω * g ω) := by
  obtain ⟨hfm, Kf, hKf⟩ := hf
  obtain ⟨hgm, Kg, hKg⟩ := hg
  refine ⟨hfm.mul hgm, |Kf| * |Kg|, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hKf ω).trans (le_abs_self _)) ((hKg ω).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

private theorem UnivMain_BM_sum {ι : Type*} (s : Finset ι) {f : ι → Ω' → ℂ}
    (hf : ∀ i ∈ s, UnivMain_BM (f i)) : UnivMain_BM (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UnivMain_BM_const (Ω' := Ω') 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact UnivMain_BM_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem UnivMain_BM_prod {ι : Type*} (s : Finset ι) {f : ι → Ω' → ℂ}
    (hf : ∀ i ∈ s, UnivMain_BM (f i)) : UnivMain_BM (fun ω => ∏ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UnivMain_BM_const (Ω' := Ω') 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact UnivMain_BM_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The real-valued norm of a bounded measurable function, as a complex-valued one. -/
private theorem UnivMain_BM_norm {f : Ω' → ℂ} (hf : UnivMain_BM f) :
    UnivMain_BM (fun ω => ((‖f ω‖ : ℝ) : ℂ)) := by
  obtain ⟨hfm, K, hK⟩ := hf
  refine ⟨Complex.measurable_ofReal.comp hfm.norm, K, fun ω => ?_⟩
  simpa using hK ω

/-- The imaginary part of a bounded measurable function, as a complex-valued one. -/
private theorem UnivMain_BM_im {f : Ω' → ℂ} (hf : UnivMain_BM f) :
    UnivMain_BM (fun ω => (((f ω).im : ℝ) : ℂ)) := by
  obtain ⟨hfm, K, hK⟩ := hf
  refine ⟨Complex.measurable_ofReal.comp (Complex.measurable_im.comp hfm), K, fun ω => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans (hK ω)

/-- A real function whose complex lift is bounded measurable is integrable on a finite measure. -/
private theorem UnivMain_integrable_of_BM {f : Ω' → ℝ} (μ : Measure Ω') [IsFiniteMeasure μ]
    (hf : UnivMain_BM (fun ω => ((f ω : ℝ) : ℂ))) : Integrable f μ := by
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

/-! ### Measurability and boundedness of the Green-function entries -/

section GreenBM

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- `|G_{xy}| ≤ (Im z)⁻¹` for `G ∈ {(H - z)⁻¹, (H - z̄)⁻¹}`, `H` Hermitian, `Im z > 0`: the entry bound
`norm_Gres_entry_le` of `Loop/GLoopFlow.lean` (private there), at `η = Im z` (`|Im z| = Im z`). -/
private theorem UnivMain_norm_Gres_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (σ : Bool) (x y : ι) :
    ‖Gres H z σ x y‖ ≤ (z.im)⁻¹ := by
  have hzim : z.im ≠ 0 := hz.ne'
  have hinv : |z.im|⁻¹ ≤ (z.im)⁻¹ := by rw [abs_of_pos hz]
  unfold Gres
  cases σ with
  | true =>
    simp only [↓reduceIte]
    exact (norm_inverse_entry_le hH hzim x y).trans hinv
  | false =>
    have hzc : (starRingEnd ℂ z).im ≠ 0 := by simpa using hzim
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (norm_inverse_entry_le hH hzc x y).trans ?_
    simpa [abs_neg] using hinv

/-- Entries of `Gres` of a measurable Hermitian-valued `M` are bounded measurable. -/
private theorem UnivMain_BM_Gres {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Ω' → Matrix ι ι ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) (b : Bool) (x y : ι) :
    UnivMain_BM (fun ω => Gres (M ω) z b x y) :=
  ⟨(walk_measurable_Gres_apply z b x y).comp hM, (z.im)⁻¹,
    fun ω => UnivMain_norm_Gres_entry_le (hH ω) hz b x y⟩

/-- Entries of a product `Gres(z₁,b₁) * Gres(z₂,b₂)`. -/
private theorem UnivMain_BM_Gres_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Ω' → Matrix ι ι ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (b₁ b₂ : Bool) (x y : ι) :
    UnivMain_BM (fun ω => (Gres (M ω) z₁ b₁ * Gres (M ω) z₂ b₂) x y) := by
  simp only [Matrix.mul_apply]
  exact UnivMain_BM_sum _ fun c _ =>
    UnivMain_BM_mul (UnivMain_BM_Gres hM hH hz₁ b₁ x c) (UnivMain_BM_Gres hM hH hz₂ b₂ c y)

/-- The normalized trace `m(z) = N⁻¹ tr G(z)` is bounded measurable. -/
private theorem UnivMain_BM_stieltjes {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Ω' → Matrix ι ι ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    UnivMain_BM (fun ω => stieltjesN (M ω) z) := by
  have h : (fun ω => stieltjesN (M ω) z) =
      fun ω => (Fintype.card ι : ℂ)⁻¹ * ∑ i, Gres (M ω) z true i i := rfl
  rw [h]
  exact UnivMain_BM_mul (UnivMain_BM_const _)
    (UnivMain_BM_sum _ fun i _ => UnivMain_BM_Gres hM hH hz true i i)

/-- `Im m(z) ≥ 0` for Hermitian `H` and `Im z > 0`. -/
private theorem UnivMain_im_stieltjesN_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (stieltjesN H z).im := by
  have h := stieltjesN_im_eq_normalized_specWeight H hH z.re z.im hz
  rw [Complex.re_add_im] at h
  rw [h]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun l _ => ?_)
  positivity

end GreenBM

/-! ### The `L₁`, `L₂` terms against the weights: `∫ w · L ≤ 4 · (bound of one summand)` -/

section LBound

variable {Ω' : Type*} [MeasurableSpace Ω'] {d L W : ℕ} [NeZero L] [NeZero W]

/-- Triangle inequality in `b` for `L_{1,t}`: `L1t ≤ ∑_{b₁ b₂} N⁻¹ ∑_y ‖∑_x …‖`. -/
private theorem UnivMain_L1t_le (lam : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) :
    L1t d L W lam M z ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, ((((W * L) ^ d : ℕ) : ℝ))⁻¹ *
      ∑ y, ‖∑ x, (Gres M z b₁ * Gres M z b₁) x x * scirc d L W lam x y *
        Gres M z b₂ y y‖ := by
  unfold L1t
  refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [Finset.sum_comm]
  exact norm_sum_le _ _

/-- Triangle inequality in `b` for `L_{2,t}`: `L2t ≤ ∑_{b₁ b₂} N⁻² ∑_y ‖∑_x …‖`. -/
private theorem UnivMain_L2t_le (lam : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) :
    L2t d L W lam M z₁ z₂ ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, (((((W * L) ^ d : ℕ) : ℝ))⁻¹) ^ 2 *
      ∑ y, ‖∑ x, (Gres M z₁ b₁ * Gres M z₁ b₁) x y * scirc d L W lam x y *
        (Gres M z₂ b₂ * Gres M z₂ b₂) y x‖ := by
  unfold L2t
  refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_comm]
  exact norm_sum_le _ _

private theorem UnivMain_L1t_nonneg (lam : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) :
    0 ≤ L1t d L W lam M z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem UnivMain_L2t_nonneg (lam : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) :
    0 ≤ L2t d L W lam M z₁ z₂ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The abstract integration step: `R ≤ ∑_{b₁ b₂} c ∑_y F` pointwise, `w ≥ 0`, and each
`∫ w F ≤ b` give `∫ w R ≤ 4 c #ι b`. -/
private theorem UnivMain_integral_mul_le {ι : Type*} [Fintype ι] (μ : Measure Ω')
    [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 ≤ c) (w : Ω' → ℝ) (hw0 : ∀ ω, 0 ≤ w ω)
    (F : Bool → Bool → ι → Ω' → ℝ)
    (hF : ∀ b₁ b₂ y, Integrable (fun ω => w ω * F b₁ b₂ y ω) μ)
    (R : Ω' → ℝ) (hR0 : ∀ ω, 0 ≤ R ω)
    (hR : ∀ ω, R ω ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, F b₁ b₂ y ω)
    {b : ℝ} (hb : ∀ b₁ b₂ y, ∫ ω, w ω * F b₁ b₂ y ω ∂μ ≤ b) :
    ∫ ω, w ω * R ω ∂μ ≤ 4 * (c * ((Fintype.card ι : ℝ) * b)) := by
  have hint2 : ∀ b₁ b₂ : Bool, Integrable (fun ω => c * ∑ y, w ω * F b₁ b₂ y ω) μ :=
    fun b₁ b₂ => (integrable_finsetSum _ fun y _ => hF b₁ b₂ y).const_mul c
  have hint : Integrable (fun ω => ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, w ω * F b₁ b₂ y ω) μ :=
    integrable_finsetSum _ fun b₁ _ => integrable_finsetSum _ fun b₂ _ => hint2 b₁ b₂
  calc ∫ ω, w ω * R ω ∂μ
      ≤ ∫ ω, ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, w ω * F b₁ b₂ y ω ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => mul_nonneg (hw0 ω) (hR0 ω)) hint
          (ae_of_all _ fun ω => ?_)
        calc w ω * R ω
            ≤ w ω * ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, F b₁ b₂ y ω :=
              mul_le_mul_of_nonneg_left (hR ω) (hw0 ω)
          _ = ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, w ω * F b₁ b₂ y ω := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b₁ _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b₂ _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, ∫ ω, w ω * F b₁ b₂ y ω ∂μ := by
        rw [integral_finsetSum _ fun b₁ _ => integrable_finsetSum _ fun b₂ _ => hint2 b₁ b₂]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [integral_finsetSum _ fun b₂ _ => hint2 b₁ b₂]
        refine Finset.sum_congr rfl fun b₂ _ => ?_
        rw [integral_const_mul, integral_finsetSum _ fun y _ => hF b₁ b₂ y]
    _ ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ _y : ι, b := by
        refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hb b₁ b₂ y) hc
    _ = 4 * (c * ((Fintype.card ι : ℝ) * b)) := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

/-- The integrand `w · ‖F‖` is integrable for a bounded measurable `F`. -/
private theorem UnivMain_integrable_w_mul_norm {ι : Type*} (μ : Measure Ω') [IsFiniteMeasure μ]
    {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) {F : Ω' → ℂ} (hF : UnivMain_BM F) :
    Integrable (fun ω => (∏ j ∈ s, (stieltjesN (M ω) (zs j)).im) * ‖F ω‖) μ := by
  refine UnivMain_integrable_of_BM μ ?_
  have h := UnivMain_BM_mul
    (UnivMain_BM_prod s fun j _ => UnivMain_BM_im (UnivMain_BM_stieltjes hM hH (hz j)))
    (UnivMain_BM_norm hF)
  simpa [Complex.ofReal_mul, Complex.ofReal_prod] using h

/-- `(W L)^d` as a real number is positive. -/
private theorem UnivMain_cardN_pos : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
  have : 0 < (W * L) ^ d := pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
    (Nat.pos_of_ne_zero (NeZero.ne L))) d
  exact_mod_cast this

private theorem UnivMain_card_Idx_real :
    (Fintype.card (Idx d L W) : ℝ) = (((W * L) ^ d : ℕ) : ℝ) := by
  rw [RBM.Gauss.card_Idx]

/-- `∫ w · L1t ≤ 4 b` if each of the `4 N` summands of `Jak` is `≤ b`. -/
private theorem UnivMain_integral_L1t_le {ι : Type*} (μ : Measure Ω') [IsProbabilityMeasure μ]
    (lam : ℝ) {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian)
    (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) (i : ι) {b : ℝ}
    (hJ : ∀ (y : Idx d L W) (b₁ b₂ : Bool),
      ∫ ω, (∏ j ∈ s, (stieltjesN (M ω) (zs j)).im) *
        ‖∑ x, (Gres (M ω) (zs i) b₁ * Gres (M ω) (zs i) b₁) x x * scirc d L W lam x y *
          Gres (M ω) (zs i) b₂ y y‖ ∂μ ≤ b) :
    ∫ ω, (∏ j ∈ s, (stieltjesN (M ω) (zs j)).im) * L1t d L W lam (M ω) (zs i) ∂μ ≤ 4 * b := by
  have hNpos := UnivMain_cardN_pos (d := d) (L := L) (W := W)
  have key := UnivMain_integral_mul_le (ι := Idx d L W) μ ((((W * L) ^ d : ℕ) : ℝ))⁻¹
    (inv_nonneg.2 hNpos.le) (fun ω => ∏ j ∈ s, (stieltjesN (M ω) (zs j)).im)
    (fun ω => Finset.prod_nonneg fun j _ => UnivMain_im_stieltjesN_nonneg (hH ω) (hz j))
    (fun b₁ b₂ y ω => ‖∑ x, (Gres (M ω) (zs i) b₁ * Gres (M ω) (zs i) b₁) x x *
      scirc d L W lam x y * Gres (M ω) (zs i) b₂ y y‖)
    (fun b₁ b₂ y => UnivMain_integrable_w_mul_norm μ hM hH zs hz s
      (UnivMain_BM_sum _ fun x _ => UnivMain_BM_mul
        (UnivMain_BM_mul (UnivMain_BM_Gres_mul hM hH (hz i) (hz i) b₁ b₁ x x)
          (UnivMain_BM_const _)) (UnivMain_BM_Gres hM hH (hz i) b₂ y y)))
    (fun ω => L1t d L W lam (M ω) (zs i)) (fun ω => UnivMain_L1t_nonneg _ _ _)
    (fun ω => UnivMain_L1t_le _ _ _) (fun b₁ b₂ y => hJ y b₁ b₂)
  refine key.trans (le_of_eq ?_)
  rw [UnivMain_card_Idx_real]
  field_simp

/-- `∫ w · L2t ≤ 4 N⁻¹ b` if each summand of `Uyw` is `≤ b`. -/
private theorem UnivMain_integral_L2t_le {ι : Type*} (μ : Measure Ω') [IsProbabilityMeasure μ]
    (lam : ℝ) {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian)
    (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) (i j : ι) {b : ℝ}
    (hU : ∀ (y : Idx d L W) (b₁ b₂ : Bool),
      ∫ ω, (∏ k ∈ s, (stieltjesN (M ω) (zs k)).im) *
        ‖∑ x, (Gres (M ω) (zs i) b₁ * Gres (M ω) (zs i) b₁) x y * scirc d L W lam x y *
          (Gres (M ω) (zs j) b₂ * Gres (M ω) (zs j) b₂) y x‖ ∂μ ≤ b) :
    ∫ ω, (∏ k ∈ s, (stieltjesN (M ω) (zs k)).im) * L2t d L W lam (M ω) (zs i) (zs j) ∂μ ≤
      4 * ((((W * L) ^ d : ℕ) : ℝ)⁻¹ * b) := by
  have hNpos := UnivMain_cardN_pos (d := d) (L := L) (W := W)
  have key := UnivMain_integral_mul_le (ι := Idx d L W) μ ((((W * L) ^ d : ℕ) : ℝ)⁻¹ ^ 2)
    (by positivity) (fun ω => ∏ k ∈ s, (stieltjesN (M ω) (zs k)).im)
    (fun ω => Finset.prod_nonneg fun k _ => UnivMain_im_stieltjesN_nonneg (hH ω) (hz k))
    (fun b₁ b₂ y ω => ‖∑ x, (Gres (M ω) (zs i) b₁ * Gres (M ω) (zs i) b₁) x y *
      scirc d L W lam x y * (Gres (M ω) (zs j) b₂ * Gres (M ω) (zs j) b₂) y x‖)
    (fun b₁ b₂ y => UnivMain_integrable_w_mul_norm μ hM hH zs hz s
      (UnivMain_BM_sum _ fun x _ => UnivMain_BM_mul
        (UnivMain_BM_mul
          (UnivMain_BM_Gres_mul hM hH (hz i) (hz i) b₁ b₁ x y) (UnivMain_BM_const _))
        (UnivMain_BM_Gres_mul hM hH (hz j) (hz j) b₂ b₂ y x)))
    (fun ω => L2t d L W lam (M ω) (zs i) (zs j)) (fun ω => UnivMain_L2t_nonneg _ _ _ _)
    (fun ω => UnivMain_L2t_le _ _ _ _) (fun b₁ b₂ y => hU y b₁ b₂)
  refine key.trans (le_of_eq ?_)
  rw [UnivMain_card_Idx_real]
  field_simp

end LBound

/-! ### The arithmetic core of the Claim [DYYY25, (2.20)] -/

section Claim

variable {d : ℕ}

/-- The centred flow is measurable in the sample for every model (`ouMatC_eq_ouMat_add` and
`measurable_ouMat`: it differs from the non-centred flow by the constant `(1 - e^{-t/2}) μ`). -/
private theorem UnivMain_measurable_ouMatC {sz : Sizes d} (M : UNModelC sz) (n : ℕ) (t : ℝ) :
    Measurable (ouMatC M n t) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have h1 : Measurable fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) => ouMat M.toUNModel n t ω i j :=
    (measurable_pi_iff.1 (measurable_pi_iff.1 (measurable_ouMat M.toUNModel n t) i)) j
  have h2 : (fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) => ouMatC M n t ω i j) = fun ω =>
      ouMat M.toUNModel n t ω i j + ((1 - Real.exp (-t / 2)) • M.mean n) i j := by
    funext ω
    rw [ouMatC_eq_ouMat_add]
    rfl
  rw [h2]
  exact h1.add_const _

/-- **The arithmetic core of `UNClaimRowk`**, for every model class `K`.  [DYYY25, (2.21)] with
[DYYY25, (2.22)], [DYYY25, (2.23)] (all weighted) give the Claim [DYYY25, (2.20)] with `C_n' = C_n + C + 1`, for
`size → ∞`.
`UNJakk` at `s = univ.erase u`, `i = u` bounds the `L₁` hypothesis of `UNEMCTE2k` by
`B = 4 N^{τ_U/4} N^{1 - c' + C τ_U}`; `UNUywk` at `s = (univ.erase u).erase v`, `i = u`, `j = v` bounds the
`L₂` hypothesis by the same `B` (`4 N⁻¹ N^{τ_U/4} N^{2 - c' + C τ_U}`).  Then `UNEMCTE2k` at slack `τ_U/4` gives
`N^{τ_U/4} N^{-1 + Cn τ_U} B = 4 N^{-c' + (Cn + C + 1/2) τ_U} ≤ N^{-c' + (Cn + C + 1) τ_U}` as soon as
`N^{τ_U/2} ≥ 4` (eventually, `size → ∞`).  RBM2D `UnivMain_claim417_of`. -/
theorem unClaim417C_of_rows {d : ℕ} (K : UNKind d) (sz : Sizes d) (hsize : sz.SizeTendsto)
    (E : ℝ) (nf : ℕ) (τU c' Cn C : ℝ) (hτ : 0 < τU)
    (hEM : UNEMCTE2k K sz E nf τU Cn) (hJ : UNJakk K sz E nf τU C c')
    (hU : UNUywk K sz E nf τU C c') :
    UNClaim417C sz (K.M sz) E nf τU c' (Cn + C + 1) := by
  intro C₀ hC₀
  have h1 := hEM C₀ (τU / 4) hC₀ (by positivity)
  have h2 := hJ C₀ (τU / 4) hC₀ (by positivity)
  have h3 := hU C₀ (τU / 4) hC₀ (by positivity)
  have h4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τU / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τU / 2)).comp hsize).eventually_ge_atTop 4
  filter_upwards [h1, h2, h3, h4] with n e1 j1 u1 f4
  intro z hz t ht0 htT
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    have : 0 < sz.size n := pow_pos (Nat.mul_pos (sz.W_pos n)
      (lt_of_lt_of_le (by norm_num) (sz.three_le_L n))) d
    rw [hNdef]
    exact_mod_cast this
  have hzim : ∀ i, 0 < (z i).im := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (hz i).2.1
  have hmeas : ∀ s : ℝ, Measurable (ouMatC (K.M sz) n s) := fun s =>
    UnivMain_measurable_ouMatC (K.M sz) n s
  set B : ℝ := 4 * (N ^ (τU / 4) * N ^ (1 - c' + C * τU)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hL1 : ∀ s : ℝ, 0 ≤ s → s ≤ ouTStar sz τU n → ∀ u : Fin nf,
      ∫ ω, (∏ j ∈ Finset.univ.erase u,
          (stieltjesN (ouMatC (K.M sz) n s ω) (z j)).im) *
        L1t d (sz.L n) (sz.W n) (K.lamV sz n) (ouMatC (K.M sz) n s ω) (z u)
        ∂(ouP (K.M sz).toUNModel n) ≤ B := by
    intro s hs0 hsT u
    exact UnivMain_integral_L1t_le (ouP (K.M sz).toUNModel n) (K.lamV sz n) (hmeas s)
      (ouMatC_isHermitian (K.M sz) n s) z hzim (Finset.univ.erase u) u
      (b := N ^ (τU / 4) * N ^ (1 - c' + C * τU))
      (fun y b₁ b₂ => j1 z hz s hs0 hsT (Finset.univ.erase u) u y b₁ b₂)
  have hL2 : ∀ s : ℝ, 0 ≤ s → s ≤ ouTStar sz τU n → ∀ u v : Fin nf, u ≠ v →
      ∫ ω, (∏ k ∈ (Finset.univ.erase u).erase v,
          (stieltjesN (ouMatC (K.M sz) n s ω) (z k)).im) *
        L2t d (sz.L n) (sz.W n) (K.lamV sz n) (ouMatC (K.M sz) n s ω) (z u) (z v)
        ∂(ouP (K.M sz).toUNModel n) ≤ B := by
    intro s hs0 hsT u v huv
    have key := UnivMain_integral_L2t_le (ouP (K.M sz).toUNModel n) (K.lamV sz n) (hmeas s)
      (ouMatC_isHermitian (K.M sz) n s) z hzim ((Finset.univ.erase u).erase v) u v
      (b := N ^ (τU / 4) * N ^ (2 - c' + C * τU))
      (fun y b₁ b₂ => u1 z hz s hs0 hsT ((Finset.univ.erase u).erase v) u v huv y b₁ b₂)
    refine key.trans (le_of_eq ?_)
    have h2e : N ^ (2 - c' + C * τU) = N * N ^ (1 - c' + C * τU) := by
      have : (2 - c' + C * τU) = 1 + (1 - c' + C * τU) := by ring
      rw [this, Real.rpow_add hNpos, Real.rpow_one]
    rw [hBdef, h2e]
    change 4 * (N⁻¹ * (N ^ (τU / 4) * (N * N ^ (1 - c' + C * τU)))) = _
    field_simp
  have e := e1 z hz B hB0 hL1 hL2 t ht0 htT
  refine e.trans ?_
  have hX : 0 ≤ N ^ (-c' + (Cn + C + 1 / 2) * τU) := Real.rpow_nonneg hNpos.le _
  have hlhs : N ^ (τU / 4) * N ^ (-1 + Cn * τU) * B =
      4 * N ^ (-c' + (Cn + C + 1 / 2) * τU) := by
    rw [hBdef, show -c' + (Cn + C + 1 / 2) * τU =
      (τU / 4 + (-1 + Cn * τU)) + (τU / 4 + (1 - c' + C * τU)) by ring,
      Real.rpow_add hNpos (τU / 4 + (-1 + Cn * τU)), Real.rpow_add hNpos (τU / 4),
      Real.rpow_add hNpos (τU / 4)]
    ring
  have hrhs : N ^ (-c' + (Cn + C + 1) * τU) =
      N ^ (τU / 2) * N ^ (-c' + (Cn + C + 1 / 2) * τU) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  rw [hlhs, hrhs]
  exact mul_le_mul_of_nonneg_right f4 hX

/-- **The model-generic statement `UNClaimRowk`**: [DYYY25, (2.21)] with [DYYY25, (2.22)],
[DYYY25, (2.23)] (weighted) give the Claim [DYYY25, (2.20)] at `c' = 𝔠𝔡/30` with `C_n' = C_n + C + 1`, for every
class `K`.  RBM2D `claimRow`. -/
theorem unClaimRowk : ∀ K : ∀ d, UNKind d, UNClaimRowk K := by
  intro K h d hd 𝔠 𝔡 sz hA κ hκ E hE
  refine ⟨𝔠 * 𝔡 / 30, by have := hA.1; have := hA.2.1; positivity, fun nf => ?_⟩
  obtain ⟨Cn, C, τ₀, hτ₀, hh⟩ := h d hd 𝔠 𝔡 sz hA κ hκ E hE nf
  refine ⟨Cn + C + 1, τ₀, hτ₀, fun τU hτU hτU0 => ?_⟩
  obtain ⟨hEM, hJ, hU⟩ := hh τU hτU hτU0
  exact unClaim417C_of_rows (K d) sz hA.2.2.1 E nf τU _ Cn C hτU hEM hJ hU

/-- **The band statement `UNClaimRow`** (`Pins.lean`), from the model-generic one at the band kind
(`UNClaimRowk_band`, `PinsK.lean`). -/
theorem unClaimRow : UNClaimRow := UNClaimRowk_band.1 (unClaimRowk _)

end Claim

/-! ### The range of the density sequence -/

/-- **The density sequence of `UNDens` is eventually in `[c/π, C/π]`**, with `0 < c`: at `x = E`,
`c ≤ Im m_n(E + iη) ≤ C` for `0 < η ≤ 10`, and `Im m_n(E + iη)/π → ρ_n` along `𝓝[>] 0`
(`ge_of_tendsto`, `le_of_tendsto`).  As the private `Step1Band_density_range` (`Universality/Step1Band.lean`),
without the conclusion `c ≤ C`. -/
theorem unDens_rho_bounds (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (h : UNDens m E ρ δ) :
    ∃ a b : ℝ, 0 < a ∧ ∀ᶠ n in atTop, a ≤ ρ n ∧ ρ n ≤ b := by
  obtain ⟨hδ, cD, CD, Lp, hcD, hCD, hLp, hev⟩ := h
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨cD / Real.pi, CD / Real.pi, div_pos hcD hpi, ?_⟩
  filter_upwards [hev] with n hn
  obtain ⟨hb, -, hlim⟩ := hn
  have hev0 : ∀ᶠ η : ℝ in 𝓝[>] 0, η ∈ Set.Ioo (0 : ℝ) 10 := Ioo_mem_nhdsGT (by norm_num)
  constructor
  · refine ge_of_tendsto hlim ?_
    filter_upwards [hev0] with η hη
    have := (hb E η (by simpa using hδ.le) hη.1 hη.2.le).1
    exact div_le_div_of_nonneg_right this hpi.le
  · refine le_of_tendsto hlim ?_
    filter_upwards [hev0] with η hη
    have := (hb E η (by simpa using hδ.le) hη.1 hη.2.le).2
    exact div_le_div_of_nonneg_right this hpi.le

/-! ### The law transfer at `t = 0` -/

/-- **The `k`-point functional of the model equals that of `𝐇_0`** (law transfer at `t = 0`),
for every test function `O` (no measurability): `apriori_ouMat_zero_integral` (`Apriori.lean`) with the
test function `A ↦ if h : A.IsHermitian then kPoint k O E h.eigenvalues else 0`, by `dite_eq_left`. -/
theorem univMain_transfer {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) :
    ∫ ω, kPoint k O E (M.herm n ω).eigenvalues ∂M.μ =
      ∫ ω, kPoint k O E (ouMat_isHermitian M n 0 ω).eigenvalues ∂(ouP M n) := by
  classical
  have h := apriori_ouMat_zero_integral sz M n
    (fun A => if hA : A.IsHermitian then kPoint k O E hA.eigenvalues else 0)
  have e1 : ∀ ω, (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      if hA : A.IsHermitian then kPoint k O E hA.eigenvalues else 0) (M.H n ω) =
        kPoint k O E (M.herm n ω).eigenvalues := fun ω => dite_eq_left (M.herm n ω)
  have e2 : ∀ ω, (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      if hA : A.IsHermitian then kPoint k O E hA.eigenvalues else 0) (ouMat M n 0 ω) =
        kPoint k O E (ouMat_isHermitian M n 0 ω).eigenvalues := fun ω =>
    dite_eq_left (ouMat_isHermitian M n 0 ω)
  simp_rw [e1, e2] at h
  exact h.symm

/-! ### The statement `UNUnivMainRow` -/

/-- **`UNUnivMainRow`**: the comparison of `H` with `𝐇_{t*}` from the
Claim family `UNClaimAll` (at `c'`), the a priori bound (`unApriori_of_trLocal`, from `UNTrLocal`) and
`UNGreenCorrAll`, plus the law transfer at `t = 0` (`univMain_transfer`) and the range of the dilation
(`unDens_rho_bounds`).
`τ₀ := min τ' (inf'_{nf ≤ k} τ₀(nf))` depends on `E, k, c', C_n` only (`τ'` of `UNGreenCorr`, `τ₀(nf)` of
`UNClaimAll`), not on `τ_U` or `O`.  RBM2D `univMainRow`. -/
theorem univMainRow : UNUnivMainRow := by
  intro hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hClaim k
  obtain ⟨c', hc', hCl⟩ := hClaim
  choose Cn τ0 hτ0 hCl' using hCl
  obtain ⟨τ', hτ', hGC'⟩ := hGC d hd sz (tendsto_natCast_atTop_iff.1 hA.2.2.1) M E k c' hc' Cn
  have hap : UNApriori sz M E := unApriori_of_trLocal d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT
  obtain ⟨a, b, ha, hρ⟩ := unDens_rho_bounds m E ρ δ hD
  have hne : (Finset.range (k + 1)).Nonempty := ⟨0, by simp⟩
  have hτm_pos : 0 < (Finset.range (k + 1)).inf' hne τ0 :=
    (Finset.lt_inf'_iff hne).2 fun i _ => hτ0 i
  refine ⟨min τ' ((Finset.range (k + 1)).inf' hne τ0), lt_min hτ' hτm_pos,
    fun τU hτU hτUle O hO => ?_⟩
  have h417 : ∀ nf ≤ k, UNClaim417 sz M E nf τU c' (Cn nf) := fun nf hnf =>
    hCl' nf τU hτU (hτUle.trans ((min_le_right _ _).trans
      (Finset.inf'_le τ0 (Finset.mem_range.2 (Nat.lt_succ_of_le hnf)))))
  have hGCl := hGC' τU hτU (hτUle.trans (min_le_left _ _)) h417 hap O hO ρ a b ha hρ
  refine hGCl.congr fun n => ?_
  rw [univMain_transfer sz M n k (fun α => O (ρ n • α)) E]


/-! ### The centred forms for every centred model -/

/-- The eigenvalues of Hermitian matrices that are equal are equal. -/
private theorem UnivMain_eigenvalues_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hA.eigenvalues = hB.eigenvalues := by
  subst h; rfl

/-- **`un_infty1RowC''`**: the centred comparison of `𝐇_{t*}` with the GUE at every GUE energy `|E'| < 2`
(the centred form of `un_infty1Row'_of_translation guetranslation`).  `step1Band_rowC''`
(`E' = 0`, `τ₁ = 𝔠𝔡`) plus the GUE translation `guetranslation` at `κ = (2 - |E'|)/2`, test function
`O(ρ_sc(E') ·)` (`isTestFun_comp_smul`; `ρ_sc(E') • ((ρ_sc(0)/ρ_sc(E')) • α) = ρ_sc(0) • α`), added in `ℝ`.  The text
of the band proof, with `UNInfty1 ↦ UNInfty1C` and `step1Band_row ↦ step1Band_rowC''`. -/
theorem un_infty1RowC'' :
    UNL32 → UNGUELocal →
      ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
        ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
          UNDens' m E ρ δ → UNTrLocalInit' sz M m E δ →
            (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀ ∧ UNMeanBound sz M CV₀) →
              ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
                ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1C sz M ρ E E' k O τU := by
  intro h32 hGUE d hd 𝔠 𝔡 sz hA M m E ρ δ hD hTr hCV E' hE' k O hO
  obtain ⟨τ₁, hτ₁, hband⟩ := step1Band_rowC'' h32 hGUE d hd 𝔠 𝔡 sz hA M m E ρ δ hD hTr hCV k O hO
  refine ⟨τ₁, hτ₁, fun τU hτU hle => ?_⟩
  have hsz : Tendsto (fun n => sz.size n) atTop atTop := tendsto_natCast_atTop_iff.1 hA.2.2.1
  have hρ' : 0 < rhoSC E' := rhoSC_pos hE'
  have hO' : IsTestFun (fun α : Fin k → ℝ => O (rhoSC E' • α)) := isTestFun_comp_smul hO hρ'.ne'
  have habs := abs_nonneg E'
  have hgue := guetranslation h32 hGUE d hd sz hsz k ((2 - |E'|) / 2) (by linarith) E' (by linarith) _ hO'
  have e0 : rhoSC E' * (rhoSC 0 / rhoSC E') = rhoSC 0 := by field_simp
  have e' : ∀ α : Fin k → ℝ, O (rhoSC E' • (rhoSC 0 / rhoSC E') • α) = O (rhoSC 0 • α) := fun α => by
    rw [smul_smul, e0]
  have h := (hband τU hτU hle).add hgue
  rw [add_zero] at h
  unfold UNInfty1C
  refine h.congr fun n => ?_
  simp only [e']
  ring

/-- **`univMain_transferC`** (the centred form of `univMain_transfer`): the law transfer at `t = 0` for the
centred flow: `ouMatC M n 0 = M.H n = ouMat M.toUNModel n 0` (`ouMatC_zero`, `ouMat_zero`), so the band transfer at
`M.toUNModel` applies, then the eigenvalues of equal Hermitian matrices agree. -/
theorem univMain_transferC {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (n k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) :
    ∫ ω, kPoint k O E (M.herm n ω).eigenvalues ∂M.μ =
      ∫ ω, kPoint k O E (ouMatC_isHermitian M n 0 ω).eigenvalues ∂(ouP M.toUNModel n) := by
  rw [univMain_transfer sz M.toUNModel n k O E]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only
  rw [UnivMain_eigenvalues_congr (by rw [ouMatC_zero, ouMat_zero])
    (ouMat_isHermitian M.toUNModel n 0 ω) (ouMatC_isHermitian M n 0 ω)]

/-- **`univMainRowC`** (the centred form of `univMainRow`): the centred comparison of `H` with `𝐇_{t*}`, from
`UNClaimAllC` (at `c'`), the a priori bound (`unApriori_of_trLocal` at `M.toUNModel`, from `UNTrLocal` of the
underlying model), `UNGreenCorrAllC` (concluded by `greenCorrAllC`; here a premise as in `UNCoreC''`) and the law
transfer (`univMain_transferC`).  `τ₀ := min τ' (inf'_{nf ≤ k} τ₀(nf))` depends on `E, k, c', C_n` only. -/
theorem univMainRowC :
    UNGreenCorrAllC →
      ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
        ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
          UNDens m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNClaimAllC sz M E →
            ∀ k : ℕ, ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
              ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → UNUnivMainC sz M ρ E k O τU := by
  intro hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hClaim k
  obtain ⟨c', hc', hCl⟩ := hClaim
  choose Cn τ0 hτ0 hCl' using hCl
  obtain ⟨τ', hτ', hGC'⟩ := hGC d hd sz (tendsto_natCast_atTop_iff.1 hA.2.2.1) M E k c' hc' Cn
  have hap : UNApriori sz M.toUNModel E :=
    unApriori_of_trLocal d hd 𝔠 𝔡 sz hA M.toUNModel m E ρ δ hD hT
  obtain ⟨a, b, ha, hρ⟩ := unDens_rho_bounds m E ρ δ hD
  have hne : (Finset.range (k + 1)).Nonempty := ⟨0, by simp⟩
  have hτm_pos : 0 < (Finset.range (k + 1)).inf' hne τ0 :=
    (Finset.lt_inf'_iff hne).2 fun i _ => hτ0 i
  refine ⟨min τ' ((Finset.range (k + 1)).inf' hne τ0), lt_min hτ' hτm_pos,
    fun τU hτU hτUle O hO => ?_⟩
  have h417 : ∀ nf ≤ k, UNClaim417C sz M E nf τU c' (Cn nf) := fun nf hnf =>
    hCl' nf τU hτU (hτUle.trans ((min_le_right _ _).trans
      (Finset.inf'_le τ0 (Finset.mem_range.2 (Nat.lt_succ_of_le hnf)))))
  have hGCl := hGC' τU hτU (hτUle.trans (min_le_left _ _)) h417 hap O hO ρ a b ha hρ
  refine hGCl.congr fun n => ?_
  rw [univMain_transferC sz M n k (fun α => O (ρ n • α)) E]

/-- **`unCoreC''_holds`** (the statement `UNCoreC''`, `PinsC2.lean`; the centred form of the band argument): the
two limits compose, `un_core_of_rows'` (`PinsDens.lean`) over the centred statements `un_infty1RowC''` and
`univMainRowC`: `UNUnivMainC + UNInfty1C = UNUnivDilAt sz M.toUNModel` at `τ_U := min τ₀ τ₁`.  Every centred model; at
block Anderson it is applied at `UNModelC.ba sz`, `m = BAm`, `ρ = BArho` (`baBUniv_of_rowsD`, `BA/UNBUniv.lean`). -/
theorem unCoreC''_holds : UNCoreC'' := by
  intro h32 hGL hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hTi hN hC E' hE' k _ O hO
  obtain ⟨τ₀, hτ₀, hU⟩ := univMainRowC hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD.toUNDens hT hC k
  obtain ⟨τ₁, hτ₁, hI⟩ := un_infty1RowC'' h32 hGL d hd 𝔠 𝔡 sz hA M m E ρ δ hD hTi hN E' hE' k O hO
  have hpos : 0 < min τ₀ τ₁ := lt_min hτ₀ hτ₁
  have h3 := (hU _ hpos (min_le_left _ _) O hO).add (hI _ hpos (min_le_right _ _))
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  ring


end RBM.Univ


end
