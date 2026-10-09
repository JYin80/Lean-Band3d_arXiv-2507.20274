/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Grid
import RBM3D.Universality.ZeroModeProfile

/-!
# The `OULL` transfer of the §7.2 random layer, `d ≥ 3` (T2354, UN-50a)

Port of RBM2D `Universality/GUEPhase/LLTransfer.lean` (440 lines, `9e0f275`).
`oull_of_pathBounds`: per sequence `(E_n, t_n)` with `|E_n| ≤ 2 - κ`, `t_n ≥ 0`,
`z_n = E_n + i η_n`, `η_n = ouEtaLL sz τU n = N^{-1+2τ_U}`, `N = sz.size n = (W L)^d`, the
hypothesis `GUEPathBounds` at `E' = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀` gives the
moment bound
`E ‖G(𝐇_{t_n}, z_n)_{xx}‖^{2p} ≤ N^δ` of the pin `UNOULL sz τU` (`ZeroModeProfile.lean:97`, its body
at fixed `(κ, E, t, δ, p)`), for `ouMat (UNModel.band sz) n (t n)` under `ouP (UNModel.band sz) n`.

Proof outline:
(i) the Lemma 2.8 facts at `z_n` (`lemma28_quant`, `norm_msc_lt_one`, `eq_inv_sqrt_mul_zt`: the
bounds on `lemE z`, `lemT z` and `η_{t₀} = √t₀ η ≥ η/4`);
(ii) the pointwise scaling `G(H, z) = √t₀ G(√t₀ H, z_{t₀})`;
(iii) the one-time law `map_gueH_last` (`√t₀ 𝐇_t ~ H_K`; `0 ≤ t₀`, `0 ≤ t`, `K ≠ 0`), integrated
against a measurable functional of the matrix;
(iv) the `localLaw` field of `GUEPathBounds` at the last grid step `k = K` (`gridTime_last`), at
the cutoff `τ' = τ_U/2` and the failure rate `D = 2p + 1`: off the bad event
`|G_{xx}| ≤ |m| + N^{τ_U/2} (N η_{t₀})^{-1/2} ≤ 2` (`N η_{t₀} ≥ N^{2τ_U}/4`, and `N^{τ_U/2} ≥ 2`
eventually), on it `|G_{xx}| ≤ (Im z_{t₀})⁻¹ ≤ 4N` (`norm_Gsig_le_inv_eta`);
(v) the moment `≤ 2^{2p} + (4N)^{2p} N^{-(2p+1)} ≤ 2^{2p} + 4^{2p} ≤ N^δ` eventually (`N → ∞`).
The bad event is dominated by the global envelope, so no cutoff function is needed.

Port map (`d = 2` to `d ≥ 3`): `d : Sizes` becomes `sz : Sizes d`; `Idx (d.L n) (d.W n)` becomes
`Idx d (sz.L n) (sz.W n)`; `Z2 L` becomes `Zd d L`; `spectralZ` becomes `zt`; `ouMat L W t`,
`ouP L W` become `ouMat (UNModel.band sz) n t`, `ouP (UNModel.band sz) n`; `green … x x` in the
conclusion becomes `Gres … true x x` (the pinned body of `UNOULL`; `Gres H z true = green H z`);
`N = (W L)^2` becomes `N = (W L)^d = sz.size n`, the only `d`-dependent token.  The merged
twins used: `lemma28_quant` (for `zztE_quant`), `eq_inv_sqrt_mul_zt`, `lemT_pos`,
`norm_Gsig_le_inv_eta` (for `norm_green_le`), `measurable_ouMat` (the source proves continuity of
`ouMat`, the merged `ouMat` has the model matrix `M.H n ω.1`, measurable only).  Re-derived
privately (the merged twins are private): `size_eq` (positivity of `N`), the scaling
`green (c • H) (c * z) = c⁻¹ • green H z` (`ZRescale_green_smul_mul`),
`zt (lemE z) (lemT z) = √t₀ z`, measurability of `M ↦ G(M, z)_{ij}`.  Helpers are `private` and
carry the prefix `LLTransfer_`; the only public declaration is `oull_of_pathBounds`.  Departure
from the source statement: none beyond the form of the conclusion (`UNOULL` body) and `0 ≤ t n`
as the only time hypothesis.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ### Sizes and the scale `η = N^{-1+2τ_U}` -/

/-- `N = sz.size n > 0` (`L ≥ 3`, `W > 0`). -/
private lemma LLTransfer_size_pos (n : ℕ) : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
  have h1 : 0 < sz.W n := sz.W_pos n
  have h2 : 0 < sz.L n := by have := sz.three_le_L n; omega
  have : 0 < sz.size n := by unfold Sizes.size; positivity
  exact_mod_cast this

/-- `1 ≤ N`. -/
private lemma LLTransfer_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : 0 < sz.W n := sz.W_pos n
  have h2 : 0 < sz.L n := by have := sz.three_le_L n; omega
  have : 1 ≤ sz.size n := by
    unfold Sizes.size; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact_mod_cast this

/-- `0 < η = N^{-1+2τ_U}`. -/
private lemma LLTransfer_etaLL_pos {τU : ℝ} (n : ℕ) : 0 < ouEtaLL sz τU n :=
  Real.rpow_pos_of_pos (LLTransfer_size_pos sz n) _

/-- `η ≤ 1` for `τ_U < 1/2`. -/
private lemma LLTransfer_etaLL_le_one {τU : ℝ} (hτU1 : τU < 1 / 2) (n : ℕ) :
    ouEtaLL sz τU n ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (LLTransfer_one_le_size sz n) (by linarith)

/-- `N⁻¹ ≤ η`. -/
private lemma LLTransfer_inv_size_le_etaLL {τU : ℝ} (hτU : 0 < τU) (n : ℕ) :
    ((sz.size n : ℕ) : ℝ)⁻¹ ≤ ouEtaLL sz τU n := by
  unfold ouEtaLL
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (LLTransfer_one_le_size sz n) (by linarith)

/-- `N η = N^{2τ_U}` (the scale of `localLaw` is `N η_{t₀} ≥ N η/4`). -/
private lemma LLTransfer_size_mul_etaLL {τU : ℝ} (n : ℕ) :
    ((sz.size n : ℕ) : ℝ) * ouEtaLL sz τU n = ((sz.size n : ℕ) : ℝ) ^ (2 * τU) := by
  have h := LLTransfer_size_pos sz n
  unfold ouEtaLL Nsz
  calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + 2 * τU)
      = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + 2 * τU) := by
        rw [Real.rpow_one]
    _ = ((sz.size n : ℕ) : ℝ) ^ (2 * τU) := by
        rw [← Real.rpow_add h]; congr 1; ring

/-! ### Lemma 2.8 at `z = e + iη` -/

/-- `z_u^{(E)} = √u z` for `(E, u) = (lemE z, lemT z)` (`eq:zztE`). -/
private lemma LLTransfer_zt_eq {z : ℂ} (hz : 0 < z.im) :
    zt (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z := by
  have hu := lemT_pos hz
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
  have h := eq_inv_sqrt_mul_zt hz
  calc zt (lemE z) (lemT z)
      = (Real.sqrt (lemT z) : ℂ) *
          ((Real.sqrt (lemT z) : ℂ)⁻¹ * zt (lemE z) (lemT z)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    _ = (Real.sqrt (lemT z) : ℂ) * z := by rw [← h]

/-- Lemma 2.8 at `z = e + iη`, `|e| ≤ 2 - κ`, `0 < η ≤ 1`: the facts used by `oull_of_pathBounds`.
The bound `η/4 ≤ η_{t₀}` is `η_{t₀} = Im z_{t₀} = √t₀ η` with `√t₀ ≥ 1/4`. -/
private lemma LLTransfer_lem28 {κ e η : ℝ} (hκ : 0 < κ) (he : |e| ≤ 2 - κ) (hη0 : 0 < η)
    (hη1 : η ≤ 1) {z : ℂ} (hz : z = (e : ℂ) + (η : ℂ) * Complex.I) :
    0 < z.im ∧ |lemE z| ≤ 2 - κ ∧ 1 / 16 ≤ lemT z ∧ lemT z < 1 ∧
      etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * η ∧ η / 4 ≤ etaT (lemE z) (lemT z) := by
  have hre : z.re = e := by simp [hz]
  have him : z.im = η := by simp [hz]
  have hzim : 0 < z.im := him ▸ hη0
  obtain ⟨hE', ht16, -, -⟩ := lemma28_quant hκ hzim (him ▸ hη1) (hre ▸ he)
  have ht1 : lemT z < 1 := lemT_lt_one hzim
  have heta : etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * η := by
    rw [etaT_eq_zt_im, zt_im_lemma28 hzim, him]
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt (lemT z) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  refine ⟨hzim, hE', ht16, ht1, heta, ?_⟩
  rw [heta]
  nlinarith

/-! ### The pointwise scaling `G(H, z) = √t₀ G(√t₀ H, z_{t₀})` -/

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for a nonzero scalar (private copy of `Grid.lean:682`). -/
private theorem LLTransfer_inv_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℂ} (hc : c ≠ 0)
    (A : Matrix ι ι ℂ) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul A c h, invOf_eq_inv c]
  · have hdet : A.det = 0 := by simpa [isUnit_iff_ne_zero] using h
    have h2 : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet, mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

/-- `G(cH, cz) = c⁻¹ G(H, z)` (`ZRescale_green_smul_mul`; private copy of `Grid.lean:695`). -/
private theorem LLTransfer_green_smul_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℂ}
    (hc : c ≠ 0) (H : Matrix ι ι ℂ) (z : ℂ) :
    green (c • H) (c * z) = c⁻¹ • green H z := by
  have hsub : c • H - (c * z) • (1 : Matrix ι ι ℂ) = c • (H - z • (1 : Matrix ι ι ℂ)) := by
    rw [smul_sub, smul_smul]
  unfold green
  rw [hsub, LLTransfer_inv_smul hc]

/-- `Gres H z true = green H z` (`Ring.inverse` is `⁻¹`; twin of the private `IBPRem_Gres_true`). -/
private theorem LLTransfer_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, Matrix.nonsing_inv_eq_ringInverse, ite_true]

/-- The pointwise scaling `G(H, z) = √t₀ G(√t₀ H, z_{t₀}^{(E')})` in moment form, for `0 < Im z`,
`(E', t₀) = (lemE z, lemT z)`. -/
private lemma LLTransfer_green_scale {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ℂ}
    (hz : 0 < z.im) (H : Matrix ι ι ℂ) (x : ι) (p : ℕ) :
    ‖green H z x x‖ ^ (2 * p) = Real.sqrt (lemT z) ^ (2 * p) *
      ‖green (((Real.sqrt (lemT z) : ℝ) : ℂ) • H) (zt (lemE z) (lemT z)) x x‖ ^ (2 * p) := by
  have hs : 0 < Real.sqrt (lemT z) := Real.sqrt_pos.2 (lemT_pos hz)
  have hc : ((Real.sqrt (lemT z) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hg : green (((Real.sqrt (lemT z) : ℝ) : ℂ) • H) (zt (lemE z) (lemT z)) x x =
      ((Real.sqrt (lemT z) : ℝ) : ℂ)⁻¹ * green H z x x := by
    rw [LLTransfer_zt_eq hz, LLTransfer_green_smul_mul hc]
    rfl
  rw [hg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow,
    ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs.ne', one_pow, one_mul]

/-! ### Measurability -/

section Measurability

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- Entries of `A⁻¹` are measurable in `A` (a private copy of `measurable_matrix_inv_apply` of
`Green/RowIndep.lean:269`, which is private). -/
private theorem LLTransfer_measurable_matrix_inv_apply {Θ : Type*} [MeasurableSpace Θ]
    {M : Θ → Matrix ν ν ℂ} (hM : Measurable M) (i j : ν) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

/-- `M ↦ G(M, z)_{ij}` is measurable on all matrices. -/
private theorem LLTransfer_measurable_green (z : ℂ) (i j : ν) :
    Measurable fun M : Matrix ν ν ℂ => green M z i j :=
  LLTransfer_measurable_matrix_inv_apply (M := fun M : Matrix ν ν ℂ => M - z • (1 : Matrix ν ν ℂ))
    (continuous_sub_right (z • (1 : Matrix ν ν ℂ))).measurable i j

end Measurability

/-! ### The one-time law, integrated -/

/-- Integrals of a measurable matrix functional of `√t₀ 𝐇_τ` under `ouP` equal the integrals of the
same functional of the last grid matrix under `Pgue`, by the one-time law `map_gueH_last`. -/
private theorem LLTransfer_integral_transfer (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (ht0 : 0 ≤ t0 n) (hτ : 0 ≤ τ n) (hK : K n ≠ 0)
    (f : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ) (hf : Measurable f) :
    ∫ ω, f (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (τ n) ω)
        ∂(ouP (UNModel.band sz) n) =
      ∫ ω, f (gueH sz (fun n => (1 - ouZeta (τ n)) * t0 n) t0 K n (K n) ω) ∂(Pgue sz) := by
  have h1 : Measurable fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (τ n) ω :=
    (measurable_ouMat (UNModel.band sz) n (τ n)).const_smul ((Real.sqrt (t0 n) : ℝ) : ℂ)
  have h2 := gueH_measurable sz (fun n => (1 - ouZeta (τ n)) * t0 n) t0 K n (K n)
  rw [← integral_map h1.aemeasurable hf.aestronglyMeasurable,
    ← map_gueH_last sz t0 τ K n ht0 hτ hK]
  exact integral_map h2.aemeasurable hf.aestronglyMeasurable

/-! ### The good/bad split of a bounded integrand -/

/-- `∫ g ≤ a + A q` for a measurable `0 ≤ g ≤ A` with `g ≤ a` off a set `B` of mass `≤ q`
(the bad event of `localLaw` is dominated by the deterministic envelope, no cutoff is needed). -/
private lemma LLTransfer_split_bound {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    [IsProbabilityMeasure μ] {g : Ω' → ℝ} (hg : Measurable g) {a A q : ℝ} {B : Set Ω'}
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hq : 0 ≤ q) (hg0 : ∀ ω, 0 ≤ g ω) (hgA : ∀ ω, g ω ≤ A)
    (hga : ∀ ω, ω ∉ B → g ω ≤ a) (hB : μ B ≤ ENNReal.ofReal q) :
    ∫ ω, g ω ∂μ ≤ a + A * q := by
  set Bm : Set Ω' := toMeasurable μ B with hBmdef
  have hBm : MeasurableSet Bm := measurableSet_toMeasurable _ _
  have hgint : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable A (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]
    exact hgA ω
  have hgint2 : Integrable (fun ω => a + Bm.indicator (fun _ => A) ω) μ :=
    (integrable_const _).add ((integrable_const _).indicator hBm)
  have hptw : ∀ ω, g ω ≤ a + Bm.indicator (fun _ => A) ω := by
    intro ω
    by_cases hω : ω ∈ Bm
    · rw [Set.indicator_of_mem hω]
      have := hgA ω
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact hga ω fun h => hω (subset_toMeasurable _ _ h)
  have hPB : μ.real Bm ≤ q := by
    rw [measureReal_def, hBmdef, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hq hB
  calc ∫ ω, g ω ∂μ ≤ ∫ ω, (a + Bm.indicator (fun _ => A) ω) ∂μ :=
        integral_mono hgint hgint2 hptw
    _ = a + A * μ.real Bm := by
        rw [integral_add (integrable_const _) ((integrable_const _).indicator hBm), integral_const,
          integral_indicator_const _ hBm, probReal_univ, one_smul, smul_eq_mul]
        ring
    _ ≤ a + A * q := by gcongr

/-! ### Real-analysis steps of the moment estimate -/

/-- The scale step: from `gs ≥ a⁴/4` and `a ≥ 2` (`a = N^{τ_U/2}`, `gs = N η_{t₀} ≥ N^{2τ_U}/4`),
`N^{τ_U/2} gs^{-1/2} ≤ 1`. -/
private lemma LLTransfer_scale_bound {a gs : ℝ} (ha : 2 ≤ a) (hgs : a ^ 4 / 4 ≤ gs) :
    a * gs⁻¹ ^ ((1 : ℝ) / 2) ≤ 1 := by
  have ha0 : 0 < a := by linarith
  have hgs0 : 0 < a ^ 4 / 4 := by positivity
  have h1 : gs⁻¹ ≤ (2 / a ^ 2) ^ 2 := by
    calc gs⁻¹ ≤ (a ^ 4 / 4)⁻¹ := inv_anti₀ hgs0 hgs
      _ = (2 / a ^ 2) ^ 2 := by field_simp; ring
  have h2 : gs⁻¹ ^ ((1 : ℝ) / 2) ≤ 2 / a ^ 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
    exact ⟨by positivity, h1⟩
  calc a * gs⁻¹ ^ ((1 : ℝ) / 2) ≤ a * (2 / a ^ 2) := mul_le_mul_of_nonneg_left h2 ha0.le
    _ = 2 / a := by field_simp
    _ ≤ 1 := by rw [div_le_one ha0]; exact ha

/-- `|G| ≤ |G - m| + |m| ≤ 2` on the good event (`|m| = 1`, `|G - m| ≤ 1`). -/
private lemma LLTransfer_norm_le_two {G m : ℂ} (hm : ‖m‖ = 1) (h : ‖G - m‖ ≤ 1) : ‖G‖ ≤ 2 := by
  calc ‖G‖ = ‖(G - m) + m‖ := by rw [sub_add_cancel]
    _ ≤ ‖G - m‖ + ‖m‖ := norm_add_le _ _
    _ ≤ 2 := by rw [hm]; linarith

open scoped Matrix.Norms.L2Operator in
/-- The deterministic envelope on the bad event: `|G_{xx}(w)| ≤ (Im w)⁻¹ ≤ 4/η ≤ 4N` for
Hermitian `H`, `Im w ≥ η/4`, `η ≥ N⁻¹`. -/
private lemma LLTransfer_envelope {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {w : ℂ} {S η : ℝ} (hS : 1 ≤ S) (hη : S⁻¹ ≤ η) (hη0 : 0 < η)
    (hw : η / 4 ≤ w.im) (x : ι) : ‖green H w x x‖ ≤ 4 * S := by
  have hS0 : 0 < S := by linarith
  have h1 : ‖green H w x x‖ ≤ (η / 4)⁻¹ := by
    rw [← LLTransfer_Gres_true]
    exact (RBM.Ind.norm_apply_le_l2_opNorm (Gres H w true) x x).trans
      (norm_Gsig_le_inv_eta hH (by positivity : 0 < η / 4) (hw.trans (le_abs_self _)) true)
  have h2 : η⁻¹ ≤ S := by
    have := inv_anti₀ (inv_pos.2 hS0) hη
    rwa [inv_inv] at this
  calc ‖green H w x x‖ ≤ (η / 4)⁻¹ := h1
    _ = 4 * η⁻¹ := by rw [inv_div]; ring
    _ ≤ 4 * S := by linarith

/-- The bad-event term: `(4N)^{2p} N^{-(2p+1)} ≤ 4^{2p}`. -/
private lemma LLTransfer_bad_term {S : ℝ} (hS : 1 ≤ S) (p : ℕ) :
    ((4 : ℝ) * S) ^ (2 * p) * S ^ (-((2 * p + 1 : ℕ) : ℝ)) ≤ (4 : ℝ) ^ (2 * p) := by
  have hS0 : 0 < S := by linarith
  rw [Real.rpow_neg hS0.le, Real.rpow_natCast, ← div_eq_mul_inv,
    div_le_iff₀ (by positivity), mul_pow, pow_succ]
  have h0 : (0 : ℝ) ≤ (4 : ℝ) ^ (2 * p) * S ^ (2 * p) := by positivity
  nlinarith [mul_nonneg h0 (sub_nonneg.2 hS)]

/-! ### The moment estimate, per sequence -/

/-- **The moment bound along one sequence**, with the Lemma 2.8 data as variables:
`z_n = e_n + i η_n`, `E'_n = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀`.  The pointwise
scaling, the one-time law `map_gueH_last` and the good/bad split of `GUEPathBounds.localLaw` at the
last grid step. -/
private theorem LLTransfer_main {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτU1 : τU < 1 / 2) (n0 : ℕ) (hd : Tendsto sz.size atTop atTop)
    {e t : ℕ → ℝ} (he : ∀ n, |e n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) {z : ℕ → ℂ}
    (hz : ∀ n, z n = (e n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)
    {E' t0 t1 : ℕ → ℝ} (hE' : ∀ n, E' n = lemE (z n)) (ht0 : ∀ n, t0 n = lemT (z n))
    (ht1 : ∀ n, t1 n = (1 - ouZeta (t n)) * t0 n)
    (hP : GUEPathBounds sz E' t1 t0 (gueGridK sz n0) n0 Kt) (δ : ℝ) (hδ : 0 < δ) (p : ℕ) :
    ∀ᶠ n in atTop, ∀ x : Idx d (sz.L n) (sz.W n),
      ∫ ω, ‖green (ouMat (UNModel.band sz) n (t n) ω) (z n) x x‖ ^ (2 * p)
        ∂(ouP (UNModel.band sz) n) ≤ Nsz sz n ^ δ := by
  have ht1fun : t1 = fun n => (1 - ouZeta (t n)) * t0 n := funext ht1
  subst ht1fun
  have hbad := hP.localLaw (τU / 2) (by positivity) ((2 * p + 1 : ℕ) : ℝ) (by positivity)
  set C : ℝ := (2 : ℝ) ^ (2 * p) + (4 : ℝ) ^ (2 * p) with hCdef
  have hSat : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hCev : ∀ᶠ n in atTop, C ≤ ((sz.size n : ℕ) : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp hSat).eventually_ge_atTop C
  have h2ev : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τU / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τU / 2)).comp hSat).eventually_ge_atTop 2
  filter_upwards [hbad, hCev, h2ev] with n hbadn hCn h2n x
  set S : ℝ := ((sz.size n : ℕ) : ℝ) with hSdef
  have hS0 : 0 < S := LLTransfer_size_pos sz n
  have hS1 : 1 ≤ S := LLTransfer_one_le_size sz n
  have hη0 : 0 < ouEtaLL sz τU n := LLTransfer_etaLL_pos sz n
  have hη1 : ouEtaLL sz τU n ≤ 1 := LLTransfer_etaLL_le_one sz hτU1 n
  obtain ⟨hzim, hE2, ht16, ht1lt, hetaeq, hetaL⟩ := LLTransfer_lem28 hκ (he n) hη0 hη1 (hz n)
  have hE'n : E' n = lemE (z n) := hE' n
  have ht0n : t0 n = lemT (z n) := ht0 n
  rw [← hE'n] at hE2
  rw [← hE'n, ← ht0n] at hetaL
  rw [← ht0n] at ht1lt
  have ht0pos : 0 < t0 n := by rw [ht0n]; exact lemT_pos hzim
  have hE2' : |E' n| ≤ 2 := by linarith
  set K : ℕ → ℕ := gueGridK sz n0 with hKdef
  have hKne : K n ≠ 0 := gueGridK_ne_zero sz n0 n
  -- the pointwise scaling `G(H, z) = √t₀ G(√t₀ H, z_{t₀}^{(E')})`
  have hscale : ∀ ω, ‖green (ouMat (UNModel.band sz) n (t n) ω) (z n) x x‖ ^ (2 * p) =
      Real.sqrt (t0 n) ^ (2 * p) *
        ‖green (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (t n) ω)
          (zt (E' n) (t0 n)) x x‖ ^ (2 * p) := fun ω => by
    rw [hE'n, ht0n]
    exact LLTransfer_green_scale hzim _ x p
  -- the one-time law
  have hstep1 : ∫ ω, ‖green (ouMat (UNModel.band sz) n (t n) ω) (z n) x x‖ ^ (2 * p)
        ∂(ouP (UNModel.band sz) n) = Real.sqrt (t0 n) ^ (2 * p) *
      ∫ ω, ‖green (gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω)
        (zt (E' n) (t0 n)) x x‖ ^ (2 * p) ∂(Pgue sz) := by
    simp_rw [hscale]
    rw [integral_const_mul]
    congr 1
    exact LLTransfer_integral_transfer sz t0 t K n ht0pos.le (ht n) hKne
      (fun M => ‖green M (zt (E' n) (t0 n)) x x‖ ^ (2 * p))
      ((LLTransfer_measurable_green _ x x).norm.pow_const _)
  -- the bound on the `Pgue` side
  have hgmeas : Measurable fun ω => ‖green
      (gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω)
      (zt (E' n) (t0 n)) x x‖ ^ (2 * p) :=
    ((LLTransfer_measurable_green _ x x).norm.pow_const _).comp
      (gueH_measurable sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n))
  have hevery : ∀ ω, ‖green (gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω)
      (zt (E' n) (t0 n)) x x‖ ≤ 4 * S := fun ω => by
    refine LLTransfer_envelope (gueH_isHermitian sz _ t0 K n (K n) ω) hS1
      (LLTransfer_inv_size_le_etaLL sz hτU n) hη0 ?_ x
    have : (zt (E' n) (t0 n)).im = etaT (E' n) (t0 n) := (etaT_eq_zt_im).symm
    rw [this]
    exact hetaL
  have hgs : (S ^ (τU / 2)) ^ 4 / 4 ≤ gueScale sz E' n (t0 n) := by
    have h4 : (S ^ (τU / 2)) ^ 4 = S ^ (2 * τU) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; congr 1; push_cast; ring
    rw [h4, ← LLTransfer_size_mul_etaLL sz (τU := τU) n]
    unfold gueScale
    have := mul_le_mul_of_nonneg_left hetaL hS0.le
    linarith
  have hint : ∫ ω, ‖green (gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω)
      (zt (E' n) (t0 n)) x x‖ ^ (2 * p) ∂(Pgue sz) ≤ C := by
    have hNp := LLTransfer_bad_term hS1 p
    have ha : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * p) := pow_nonneg (by norm_num) _
    have hA : (0 : ℝ) ≤ (4 * S) ^ (2 * p) := pow_nonneg (by linarith) _
    have hq : (0 : ℝ) ≤ S ^ (-((2 * p + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hS0.le _
    have hg0 : ∀ ω, 0 ≤ ‖green (gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω)
        (zt (E' n) (t0 n)) x x‖ ^ (2 * p) := fun ω => pow_nonneg (norm_nonneg _) _
    refine (LLTransfer_split_bound (Pgue sz) hgmeas (a := (2 : ℝ) ^ (2 * p))
      (A := (4 * S) ^ (2 * p)) (q := S ^ (-((2 * p + 1 : ℕ) : ℝ))) ha hA hq hg0
      (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hevery ω) _) ?_ hbadn).trans ?_
    · intro ω hω
      simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hω
      have hu := hω (Fin.last (K n), (x, x))
      simp only [Fin.val_last] at hu
      rw [gridTime_last (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n hKne] at hu
      have hdev := hu.trans (LLTransfer_scale_bound h2n hgs)
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hdev
      exact pow_le_pow_left₀ (norm_nonneg _) (LLTransfer_norm_le_two (norm_mE hE2') hdev) _
    · linarith
  rw [hstep1]
  have hsp : Real.sqrt (t0 n) ^ (2 * p) ≤ 1 :=
    pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr ht1lt.le)
  have hI0 : 0 ≤ ∫ ω, ‖green (gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω)
      (zt (E' n) (t0 n)) x x‖ ^ (2 * p) ∂(Pgue sz) :=
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  calc _ ≤ 1 * C := mul_le_mul hsp hint hI0 zero_le_one
    _ = C := one_mul C
    _ ≤ S ^ δ := hCn

/-! ### The `OULL` transfer (T1) -/

/-- **`oull_of_pathBounds`: the moment bound of `UNOULL` for `ouMat t` from `GUEPathBounds`.**
For a sequence of energies `|E_n| ≤ 2 - κ`, times `t_n ≥ 0` and `z_n = E_n + i η_n`,
`η_n = ouEtaLL sz τU n = N^{-1+2τ_U}`, `N = sz.size n = (W L)^d`, `0 < τ_U < 1/2`: if
`GUEPathBounds` holds at the Lemma 2.8 parameters `E' = lemE z_n`, `t₀ = lemT z_n`,
`t₁ = (1 - ζ(t_n)) t₀` (grid size `gueGridK sz n₀`), then for every `δ > 0` and `p`, eventually in
`n` and for every `x`, `E ‖G(𝐇_{t_n}, z_n)_{xx}‖^{2p} ≤ N^δ` under `ouP`; the conclusion is the body
of the pin `UNOULL sz τU` (`ZeroModeProfile.lean:97`) at fixed `(κ, E, t, δ, p)`.

The `localLaw` field at the last grid step, `|G_{xx}| ≤ |m| + N^{τ_U/2} (N η_{t₀})^{-1/2} ≤ 2` off
the bad event of probability `≤ N^{-(2p+1)}`, and `|G_{xx}| ≤ (Im z_{t₀})^{-1} ≤ 4N` on it, give
the bound `2^{2p} + 4^{2p} ≤ N^δ` for `𝐇_t` after the pointwise scaling and the one-time law
(7.26). -/
theorem oull_of_pathBounds {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτU1 : τU < 1 / 2) (n0 : ℕ) (_hn0 : 1 ≤ n0) (hd : Tendsto sz.size atTop atTop)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hP : GUEPathBounds sz
      (fun n => lemE ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
      (fun n => (1 - ouZeta (t n)) *
        lemT ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
      (fun n => lemT ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
      (gueGridK sz n0) n0 Kt)
    (δ : ℝ) (hδ : 0 < δ) (p : ℕ) :
    ∀ᶠ n in atTop, ∀ x : Idx d (sz.L n) (sz.W n),
      ∫ ω, ‖Gres (ouMat (UNModel.band sz) n (t n) ω)
          ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
        ∂(ouP (UNModel.band sz) n) ≤ Nsz sz n ^ δ := by
  have h := LLTransfer_main sz hκ hτU hτU1 n0 hd hE ht Kt
    (z := fun n => (E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) (fun _ => rfl)
    (E' := fun n => lemE ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
    (t0 := fun n => lemT ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
    (t1 := fun n => (1 - ouZeta (t n)) *
      lemT ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hP δ hδ p
  filter_upwards [h] with n hn x
  simpa only [LLTransfer_Gres_true] using hn x

end RBM.Univ.GUEPhase

/-! ## Compiled instance

The merged instance sizes `sz0` (`d = 3`, `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `κ = 1/10`,
`E ≡ 0`, `τ_U = 1/1000`, `n₀ = 2`, `t_n = ouTStar sz0 τ_U n = N^{-1+τ_U} > 0` (so `ζ(t_n) > 0` and
the window `t₁ = (1 - ζ(t_n)) t₀ < t₀` is not collapsed), `δ = 1/10`.  `GUEPathBounds` at the
Lemma 2.8 parameters is the output of the §7.2 random layer (UN-50b), another gate's pin: it stays a
hypothesis of the example (the limit check of its `localLaw` field is in the prove report,
section (a)). -/

namespace RBM.Univ.GUEPhase.LLTransferInst

open MeasureTheory ProbabilityTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open RBM.Gauss.SizesInst

private def zq (n : ℕ) : ℂ := ((0 : ℝ) : ℂ) + ((ouEtaLL sz0 (1 / 1000) n : ℝ) : ℂ) * Complex.I
private def tq (n : ℕ) : ℝ := ouTStar sz0 (1 / 1000) n

/-- **`oull_of_pathBounds`** at `sz0`, `E ≡ 0`, `t_n = N^{-1+τ_U}`: every deterministic hypothesis is
discharged (`κ`, `τ_U`, `τ_U < 1/2`, `n₀`, `N → ∞`, `|E| ≤ 2 - κ`, `0 ≤ t_n`, `δ > 0`); the output is
the body of `UNOULL sz0 (1/1000)` at `(κ, E, t, δ, p) = (1/10, 0, t, 1/10, p)`. -/
example (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ)
    (hP : GUEPathBounds sz0 (fun n => lemE (zq n)) (fun n => (1 - ouZeta (tq n)) * lemT (zq n))
      (fun n => lemT (zq n)) (gueGridK sz0 2) 2 Kt) (p : ℕ) :
    ∀ᶠ n in atTop, ∀ x : Idx 3 (sz0.L n) (sz0.W n),
      ∫ ω, ‖Gres (ouMat (UNModel.band sz0) n (tq n) ω) (zq n) true x x‖ ^ (2 * p)
        ∂(ouP (UNModel.band sz0) n) ≤ Nsz sz0 n ^ (1 / 10 : ℝ) :=
  oull_of_pathBounds sz0 (κ := 1 / 10) (τU := 1 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 2 (by norm_num) (Sizes.tendsto_size sz0 sz0_tendsto) (E := fun _ => 0) (t := tq)
    (fun n => by norm_num) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) Kt hP (1 / 10)
    (by norm_num) p

end RBM.Univ.GUEPhase.LLTransferInst

end
