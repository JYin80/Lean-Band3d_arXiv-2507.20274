/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.QopNorm
import RBM3D.Evolution.Prec
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step2Events
import RBM3D.Gauss.DominationAt
import RBM3D.Path.Walk
import RBM3D.Loop.GLoopFlow
import RBM3D.Loop.KLFinal

/-!
# S6-11 (T2223): the initial term of regime (i) (Step 6 of `lem:main_ind`)

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:97,117` (initial term of regime (i)) and
`paper/tex/3_5_Loop_Hierarchy.tex:1285` (`lem_+Q`), `:1649` (`(sum_res_2_NAL)`), `:1659`
(`(sum_res_2)`).

This file proves, for `f_s = 𝔼(𝓛-𝒦)^{(2)}_s` (`STExpErr`) and the target `T_u = STExpTarget`:
* `expIniI_fastDecay`, `expIniI_fastDecay_mono`: the decay `(deccA0)` of `f_s` from
  `(Eq:Gdecay+IND)` at `s` (`STDecay`) through `≺ → 𝔼` at the fixed time `s` (the a.s. envelope
  `|𝓛^{(2)}| ≤ η_s^{-2}`);
* `expIniI_same`: `𝒰_{s,u,σ} f_s ≺ T_u` for `σ₁ = σ₂` by `(sum_res_2_NAL)`, ratio `≤ 2`;
* `expIniI_Qop`, `expIniI_mixed`: `𝒰_{s,u,σ} 𝒬_s f_s ≺ T_u` for `σ₁ ≠ σ₂` by `lem_+Q` and
  `(sum_res_2)`, ratio `≤ 4`, for positive mollifier constants;
* `expIniI_props_shift` (finding T2223a): the merged second conjunct of `STExpIniIConcl`
  quantifies also over mollifier families with `c = 0` (no decay), which the paper's mollifier
  (`Def:QtPt`, `c > 0`) is not;
* the primed pin `STExpIniI'` (`STExpIniIConcl'`: `0 < C → 0 < c →` in the second conjunct), its
  proof `stExpIniI'_holds`, and the consumer `ST_step6_caseI_of_pins'`.
The merged pin `STExpIniI` (`Step6Pins.lean:471`) is unchanged and stays owed.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology

/-! ## 1. Polynomial facts along the flow and the expectation step -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `N⁻¹ ≤ W^{-d} B_{u,0}` for `0 ≤ u < 1` (copy of the merged `expAvg_Bctl_ge`, `Induction/ExpAvg.lean:604`). -/
private theorem expIniI_Bctl_ge (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
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

/-- `W^{-d} B_{u,0} ≤ 2 (1-u)⁻¹` for `u < 1`. -/
private theorem expIniI_Bctl_le (n : ℕ) {u : ℝ} (hu1 : u < 1) : sz.Bctl n u ≤ 2 * (1 - u)⁻¹ := by
  have h1 : 0 < 1 - u := by linarith
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLd : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL
  have hWd : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos h1]
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  simp only [hz, inv_one, mul_one]
  have e1 : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1 (by nlinarith [sq_nonneg (sz.lam n)])
  have e2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1 (by nlinarith)
  have e3 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWd
  have e4 : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ 1 * ((1 - u)⁻¹ + (1 - u)⁻¹) := mul_le_mul e3 (add_le_add e1 e2) e4 zero_le_one
    _ = 2 * (1 - u)⁻¹ := by ring

/-- `W^{-d} B_{u,K} ≤ W^{-d} B_{u,0}`. -/
private theorem expIniI_STWB_le (n : ℕ) (u : ℝ) (K : ℕ) : STWB sz n u K ≤ sz.Bctl n u := by
  unfold STWB Sizes.Bctl Bparam
  have hW : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hW
  have hK : (1 : ℝ) ≤ (((K : ℕ) : ℝ) + 1) ^ (d - 2) := one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  rw [hz, inv_one, mul_one]
  have hK' : ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hg : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
  calc (sz.lam n ^ 2 + |1 - u|)⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹
      ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ * 1 + (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by gcongr
    _ = _ := by rw [mul_one]

/-- `(1-u)⁻¹ ≤ 4 N^{1+|ε|}` for `u ≤ lemT z_n` along the flow (`1 - lemT z ≥ Im z/(1+|z|) ≥ N^{-1+ε}/4`,
`ST_one_sub_lemT`, `‖z‖ ≤ 3`); no restriction on the sign of `ε`. -/
private theorem expIniI_inv_one_sub_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u : ℝ} (hu : u ≤ lemT (z n)) :
    (1 - u)⁻¹ ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ (1 + |ε|) := by
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  obtain ⟨hre, him1, him2⟩ := hz.2 n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) him1
  have hzn : ‖z n‖ ≤ 3 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (z n)
    rw [abs_of_pos him] at h1
    linarith
  have h1 := ST_one_sub_lemT him
  have hlow : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4 ≤ 1 - lemT (z n) := by
    refine le_trans ?_ h1
    rw [div_le_div_iff₀ (by norm_num) (by linarith [norm_nonneg (z n)])]
    nlinarith [Real.rpow_pos_of_pos hNpos (-1 + ε), norm_nonneg (z n)]
  have h1u : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4 ≤ 1 - u := by linarith
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4 := by
    have := Real.rpow_pos_of_pos hNpos (-1 + ε)
    positivity
  have hexp : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≥ ((sz.size n : ℕ) : ℝ) ^ (-(1 + |ε|)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [neg_abs_le ε])
  calc (1 - u)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4)⁻¹ := inv_anti₀ hpos h1u
    _ = 4 * ((sz.size n : ℕ) : ℝ) ^ (-(-1 + ε)) := by
        rw [inv_div, Real.rpow_neg hNpos.le]; ring
    _ ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ (1 + |ε|) := by
        gcongr
        linarith [le_abs_self ε, neg_abs_le ε]


/-- `‖∫ f‖ ≤ M + C · P(‖f‖ > M)` for `‖f‖ ≤ C` (copy of the `private` `meanFar_norm_integral_le`,
`Evolution/MeanFar.lean:845`). -/
private theorem expIniI_norm_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℂ) (hf : Measurable f) (M C : ℝ) (hM : 0 ≤ M)
    (hall : ∀ ω, ‖f ω‖ ≤ C) :
    ‖∫ ω, f ω ∂P‖ ≤ M + C * P.real {ω | M < ‖f ω‖} := by
  have hint : Integrable f P :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hall)
  have hS : MeasurableSet {ω | M < ‖f ω‖} := measurableSet_lt measurable_const hf.norm
  set S := {ω | M < ‖f ω‖} with hSdef
  have hpt : ∀ ω, ‖f ω‖ ≤ M + C * S.indicator (1 : Ω → ℝ) ω := by
    intro ω
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h]
      have := hall ω
      simp only [Pi.one_apply]
      linarith
    · rw [Set.indicator_of_notMem h]
      simpa using not_lt.1 h
  have hind : Integrable (S.indicator (1 : Ω → ℝ)) P := (integrable_const (1 : ℝ)).indicator hS
  calc ‖∫ ω, f ω ∂P‖ ≤ ∫ ω, ‖f ω‖ ∂P := norm_integral_le_integral_norm f
    _ ≤ ∫ ω, (M + C * S.indicator (1 : Ω → ℝ) ω) ∂P :=
        integral_mono hint.norm ((integrable_const M).add (hind.const_mul C)) hpt
    _ = M + C * P.real S := by
        rw [integral_add (integrable_const M) (hind.const_mul C), integral_const_mul,
          integral_indicator_one hS, integral_const]
        simp

/-- The loops `𝓛^{(2)}_{u,σ,a}` are integrable (measurable and bounded by `η_u^{-2}`; copy of
`meanFar_integrable_L`, `MeanFar.lean:874`). -/
private theorem expIniI_integrable_L (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Integrable (fun ω => Lloop sz n E u σ a ω) sz.seqP :=
  Integrable.of_bound (walk_measurable_Lloop sz n E u σ a).aestronglyMeasurable
    ((etaT E u)⁻¹ ^ 2) (Filter.Eventually.of_forall fun ω => norm_Lloop_le sz n hE hu σ a ω)

/-- `f_u = 𝔼(𝓛 - 𝒦)^{(2)}_u` as the integral of `𝓛 - 𝒦`. -/
private theorem expIniI_expErr_eq (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErr sz n E u σ a =
      ∫ ω, (Lloop sz n E u σ a ω - STKloop sz n E u σ a) ∂(sz.seqP) := by
  unfold STExpErr
  rw [integral_sub (expIniI_integrable_L sz n hE hu σ a) (integrable_const _), integral_const]
  simp

/-- **The pointwise `≺ → 𝔼` bound** (pattern: `meanFar_B_bound`, `MeanFar.lean:964`): if the `≺` bound `N^τ Z`
fails with probability `≤ N^{-D₁}`, then `‖f_{u,σ,a}‖ ≤ N^τ Z + (η_u^{-2} + |𝒦_{σ,a}|) N^{-D₁}` (a.s. envelope
`|𝓛^{(2)}| ≤ η_u^{-2}`, `norm_Lloop_le`). -/
private theorem expIniI_bound (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) {τ Z D₁ : ℝ} (hZ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z)
    (hP : sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z <
        ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))) :
    ‖STExpErr sz n E u σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z +
      ((etaT E u)⁻¹ ^ 2 + ‖STKloop sz n E u σ a‖) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
  have hmeas : Measurable fun ω => Lloop sz n E u σ a ω - STKloop sz n E u σ a :=
    (walk_measurable_Lloop sz n E u σ a).sub measurable_const
  have hall : ∀ ω, ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ ≤
      (etaT E u)⁻¹ ^ 2 + ‖STKloop sz n E u σ a‖ := by
    intro ω
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_Lloop_le sz n hE hu σ a ω
  have h := expIniI_norm_integral_le sz.seqP (fun ω => Lloop sz n E u σ a ω - STKloop sz n E u σ a)
    hmeas _ _ hZ hall
  have hreal : sz.seqP.real {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z <
        ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖} ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
    rw [Measure.real]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at this
  have hC : 0 ≤ (etaT E u)⁻¹ ^ 2 + ‖STKloop sz n E u σ a‖ := by positivity
  rw [expIniI_expErr_eq sz n hE hu]
  refine h.trans ?_
  gcongr

/-- `|f_{u,σ,a}| ≤ η_u^{-2} + |𝒦_{σ,a}|` (a.s. envelope of `𝓛^{(2)}`). -/
private theorem expIniI_envelope (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖STExpErr sz n E u σ a‖ ≤ (etaT E u)⁻¹ ^ 2 + ‖STKloop sz n E u σ a‖ := by
  have hmeas : Measurable fun ω => Lloop sz n E u σ a ω - STKloop sz n E u σ a :=
    (walk_measurable_Lloop sz n E u σ a).sub measurable_const
  have hall : ∀ ω, ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ ≤
      (etaT E u)⁻¹ ^ 2 + ‖STKloop sz n E u σ a‖ := by
    intro ω
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_Lloop_le sz n hE hu σ a ω
  have h := expIniI_norm_integral_le sz.seqP (fun ω => Lloop sz n E u σ a ω - STKloop sz n E u σ a)
    hmeas 0 _ le_rfl hall
  have hC : 0 ≤ (etaT E u)⁻¹ ^ 2 + ‖STKloop sz n E u σ a‖ := by positivity
  rw [expIniI_expErr_eq sz n hE hu]
  refine h.trans ?_
  have : sz.seqP.real {ω | (0 : ℝ) < ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖} ≤ 1 :=
    measureReal_le_one
  nlinarith

/-- `W^c e^{-(W^{ε'}/d)^{1/2}} ≤ W^{-D}/3` for `W` large: the stretched exponential beats every power. -/
private theorem expIniI_superpoly {d : ℕ} (hd : 0 < d) (ε' c D : ℝ) (hε' : 0 < ε') :
    ∀ᶠ W : ℝ in atTop, W ^ c * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) ≤ W ^ (-D) / 3 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set y : ℝ → ℝ := fun W => (W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ) with hy
  have hyt : Tendsto y atTop atTop := by
    have h1 : Tendsto (fun W : ℝ => W ^ ε') atTop atTop := tendsto_rpow_atTop hε'
    have h2 : Tendsto (fun W : ℝ => W ^ ε' / (d : ℝ)) atTop atTop := h1.atTop_div_const hd0
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h2
  set p : ℝ := 2 * (c + D) / ε' with hp
  have hlim : Tendsto (fun W : ℝ => (d : ℝ) ^ ((c + D) / ε') * (y W ^ p * Real.exp (-1 * y W))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p 1 one_pos).comp hyt).const_mul ((d : ℝ) ^ ((c + D) / ε'))
    simpa using this
  have hid : ∀ W : ℝ, 0 < W → W ^ (c + D) * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) =
      (d : ℝ) ^ ((c + D) / ε') * (y W ^ p * Real.exp (-1 * y W)) := by
    intro W hW
    have h1 : y W ^ p = W ^ (c + D) / (d : ℝ) ^ ((c + D) / ε') := by
      rw [hy]
      simp only
      rw [← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) hd0.le, ← Real.rpow_mul hW.le]
      congr 2
      · rw [hp]; field_simp
      · rw [hp]; field_simp
    have h2 : (d : ℝ) ^ ((c + D) / ε') ≠ 0 := (Real.rpow_pos_of_pos hd0 _).ne'
    have h3 : W ^ (c + D) = (d : ℝ) ^ ((c + D) / ε') * y W ^ p := by rw [h1]; field_simp
    have e : Real.exp (-1 * y W) = Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) := by simp [hy]
    rw [h3, e]; ring
  have hlt : ∀ᶠ W : ℝ in atTop, (d : ℝ) ^ ((c + D) / ε') * (y W ^ p * Real.exp (-1 * y W)) < 1 / 3 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hlt, eventually_gt_atTop 0] with W hW hW0
  rw [← hid W hW0] at hW
  have hWc : W ^ (c + D) = W ^ c * W ^ D := Real.rpow_add hW0 _ _
  have hWD : W ^ (-D) * W ^ D = 1 := by rw [← Real.rpow_add hW0]; simp
  have hWDpos : 0 < W ^ D := Real.rpow_pos_of_pos hW0 _
  have hnn : 0 ≤ W ^ c * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) := by positivity
  have : W ^ c * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) * W ^ D < 1 / 3 := by
    have e : W ^ c * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) * W ^ D =
        W ^ (c + D) * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) := by rw [hWc]; ring
    rw [e]; exact hW
  have hWm : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  calc W ^ c * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ))
      = W ^ c * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) * (W ^ (-D) * W ^ D) := by
        rw [hWD, mul_one]
    _ = W ^ (-D) * (W ^ c * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) * W ^ D) := by ring
    _ ≤ W ^ (-D) * (1 / 3) := by gcongr
    _ = W ^ (-D) / 3 := by ring

/-- `W ≤ N = (W L)^d` (`d ≥ 1`). -/
private theorem expIniI_W_le_size (hd : 0 < d) (n : ℕ) : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have h1 : sz.W n ≤ sz.W n ^ d := Nat.le_self_pow hd.ne' _
  have h2 : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hL) d
  exact_mod_cast h1.trans h2

end RBM.Gauss.Sizes

/-! ## 2. The decay `(deccA0)` of `f_s` (`≺ → 𝔼` at the fixed time `s`) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The decay `(deccA0)` of `f_s = 𝔼(𝓛-𝒦)^{(2)}_s`** for every `(ε', D)` (`EKFastDecay`, scale `W^{ε'} ℓ_s`), from
`(Eq:Gdecay+IND)` at `s` (`STDecay`) through `≺ → 𝔼`: with `τ = 𝔠`, `D' = D + 2`,
`D₁ = (2q+1)/𝔠 + D + 1`, `q = 2 + |ε|`, off an event of probability `≤ N^{-D₁}`
`|𝓛-𝒦| ≤ N^𝔠 (B^{1/5} W^{-d}B_{|a₁-a₂|} e^{-(|a₁-a₂|/ℓ)^{1/2}} + W^{-D'})`; the a.s. envelope `η_s^{-2}`
and `|𝒦| ≤ N B` (`stKbound_of_flow`) are polynomial in `N`, `W ≤ N ≤ W^{1/𝔠}`, and the stretched
exponential `e^{-(W^{ε'}/d)^{1/2}}` beats every power of `W`.  Deterministic conclusion. -/
theorem expIniI_fastDecay {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) (z : ℕ → ℂ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ lemT (z n))
    (hDec : STDecay sz (STflowE z) s) (ε' D : ℝ) (hε' : 0 < ε') (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKFastDecay (sz.lam n) (s n) ((sz.W n : ℕ) : ℝ) ε' D
        (fun b => STExpErr sz n (STflowE z n) (s n) σ b) := by
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hflow.1
  have hs1 : ∀ n, s n < 1 := st5_t_lt_one sz hflow hsT
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hflow
  have hd0 : 0 < d := by omega
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  set e : ℝ := 1 + |ε| with he
  set q : ℝ := e + 1 with hq
  have hq1 : 1 ≤ q := by have := abs_nonneg ε; rw [hq, he]; linarith
  set c0 : ℝ := Real.sqrt (2 * κ) / 2 with hc0
  have hc0pos : 0 < c0 := by positivity
  set D' : ℝ := D + 2 with hD'
  set D₁ : ℝ := (2 * q + 1) / 𝔠 + D + 1 with hD₁
  have hD₁pos : 0 < D₁ := by positivity
  set c₁ : ℝ := 1 + 6 * q / (5 * 𝔠) with hc₁
  have hP := hDec D' (by linarith) 𝔠 h𝔠 D₁ hD₁pos
  have hKb := (st6_prec_det_iff sz hSz (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p => ‖STKloop sz n (STflowE z n) (s n) p.1 p.2‖) (fun n _ => (sz.Bctl n (s n)) ^ (2 - 1))).1
    (stKbound_of_flow sz hd hκ hflow s hs0 hs1 2 (by norm_num)) 1 one_pos
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := scaleFacts3_W_tendsto sz hflow.1
  have hWsuper := hWt.eventually (expIniI_superpoly hd0 ε' c₁ D hε')
  have hWge : ∀ᶠ n in atTop, max 8 (4 / c0) ≤ ((sz.W n : ℕ) : ℝ) := hWt.eventually (eventually_ge_atTop _)
  filter_upwards [hP, hKb, hBw, hWsuper, hWge] with n hPn hKn hBn hSn hWn
  intro σ a ⟨i, j, hij⟩
  -- notation
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set ℓ : ℝ := ellT (sz.L n) (sz.lam n) (s n) with hℓdef
  set B : ℝ := sz.Bctl n (s n) with hBdef
  have hW8 : 8 ≤ W := (le_max_left _ _).trans hWn
  have hWc0 : 4 / c0 ≤ W := (le_max_right _ _).trans hWn
  have hW0 : 0 < W := by linarith
  have hWN : W ≤ N := expIniI_W_le_size sz hd0 n
  have hN8 : 8 ≤ N := hW8.trans hWN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hBpos : 0 < B := STBctl_pos sz n (hs1 n)
  -- the polynomial bounds
  have hxinv : (1 - s n)⁻¹ ≤ 4 * N ^ e := expIniI_inv_one_sub_le sz hκ hflow n (hsT n)
  have hNq : N ^ q = N ^ e * N := by
    rw [hq, Real.rpow_add hN0, Real.rpow_one]
  have hNe0 : 0 < N ^ e := Real.rpow_pos_of_pos hN0 _
  have hB : B ≤ N ^ q := by
    have h1 := expIniI_Bctl_le sz n (hs1 n)
    rw [hNq]
    nlinarith
  have hη : (etaT (STflowE z n) (s n))⁻¹ ≤ N ^ q := by
    have hIm : c0 ≤ (mE (STflowE z n)).im := st6_mE_im_ge hκ (st6_flowE_le sz hflow n)
    have hx0 : 0 < 1 - s n := by linarith [hs1 n]
    have hηlow : (1 - s n) * c0 ≤ etaT (STflowE z n) (s n) := by
      unfold etaT; exact mul_le_mul_of_nonneg_left hIm hx0.le
    have hpos : 0 < (1 - s n) * c0 := by positivity
    calc (etaT (STflowE z n) (s n))⁻¹ ≤ ((1 - s n) * c0)⁻¹ := inv_anti₀ hpos hηlow
      _ = (1 - s n)⁻¹ * c0⁻¹ := mul_inv _ _
      _ ≤ (4 * N ^ e) * c0⁻¹ := by gcongr
      _ = N ^ e * (4 / c0) := by field_simp
      _ ≤ N ^ e * N := by gcongr; exact hWc0.trans hWN
      _ = N ^ q := hNq.symm
  have hK : ‖STKloop sz n (STflowE z n) (s n) σ a‖ ≤ N * B := by
    have := hKn (σ, a)
    simpa [Real.rpow_one] using this
  -- the `≺` bound at `(σ, a)`
  set r : ℕ := zdistInf d (sz.L n) (a 0 - a 1) with hr
  set Y₀ : ℝ := Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) with hY₀
  have hfar : W ^ ε' * ℓ ≤ (d : ℝ) * (r : ℝ) := by
    have hWe : 0 < W ^ ε' := Real.rpow_pos_of_pos hW0 _
    have hpos : 0 < W ^ ε' * ℓ := by positivity
    have hD01 : (zdistD d (sz.L n) (a 0 - a 1) : ℝ) ≤ (d : ℝ) * (r : ℝ) := by
      have := zdistD_le_mul_zdistInf d (sz.L n) (a 0 - a 1)
      exact_mod_cast this
    have hcase : (zdistD d (sz.L n) (a i - a j) : ℝ) ≤ (zdistD d (sz.L n) (a 0 - a 1) : ℝ) := by
      fin_cases i <;> fin_cases j
      · simp only [Fin.zero_eta, sub_self, zdistD_zero, Nat.cast_zero] at hij ⊢; linarith
      · exact le_rfl
      · have : a 1 - a 0 = -(a 0 - a 1) := by ring
        simp only [Fin.mk_one, Fin.zero_eta, this, zdistD_neg]
        exact le_rfl
      · simp only [Fin.mk_one, sub_self, zdistD_zero, Nat.cast_zero] at hij ⊢; linarith
    linarith
  have hYle : Real.exp (-(((r : ℕ) : ℝ) / ℓ) ^ (1 / 2 : ℝ)) ≤ Y₀ := by
    rw [hY₀]
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [div_le_div_iff₀ hd0' (by linarith)]
    nlinarith
  -- the `≺ → 𝔼` bound
  have hSTWB0 : 0 ≤ STWB sz n (s n) r := by
    unfold STWB Bparam; positivity
  have hZnn : 0 ≤ N ^ 𝔠 * (B ^ (1 / 5 : ℝ) * STWB sz n (s n) r *
      Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) + W ^ (-D')) := by positivity
  have hbd := expIniI_bound sz n (hE2 n) (hs1 n) σ a (τ := 𝔠) (D₁ := D₁)
    (Z := B ^ (1 / 5 : ℝ) * STWB sz n (s n) r * Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) + W ^ (-D')) hZnn
    (by
      refine le_trans (measure_mono ?_) hPn
      intro ω hω
      exact ⟨(σ, a), hω⟩)
  have hB65 : B ^ (1 / 5 : ℝ) * B = B ^ (6 / 5 : ℝ) := by
    rw [show (6 / 5 : ℝ) = 1 / 5 + 1 by norm_num, Real.rpow_add hBpos, Real.rpow_one]
  have hZle : B ^ (1 / 5 : ℝ) * STWB sz n (s n) r * Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) + W ^ (-D') ≤
      B ^ (6 / 5 : ℝ) * Y₀ + W ^ (-D') := by
    have h1 : B ^ (1 / 5 : ℝ) * STWB sz n (s n) r ≤ B ^ (6 / 5 : ℝ) := by
      rw [← hB65]
      exact mul_le_mul_of_nonneg_left (expIniI_STWB_le sz n (s n) r) (Real.rpow_nonneg hBpos.le _)
    have h2 := mul_le_mul h1 hYle (Real.exp_pos _).le (Real.rpow_nonneg hBpos.le _)
    linarith
  -- `T1`: `N^𝔠 B^{6/5} Y₀ ≤ W^{c₁} Y₀`
  have hB65N : B ^ (6 / 5 : ℝ) ≤ W ^ (6 * q / (5 * 𝔠)) := by
    have h1 : B ^ (6 / 5 : ℝ) ≤ (N ^ q) ^ (6 / 5 : ℝ) := Real.rpow_le_rpow hBpos.le hB (by norm_num)
    rw [← Real.rpow_mul hN0.le] at h1
    have h2 := size_rpow_le_W_rpow sz h𝔠 n hBn (τ := q * (6 / 5)) (by positivity)
    have e : q * (6 / 5) / 𝔠 = 6 * q / (5 * 𝔠) := by field_simp
    rw [e] at h2
    exact h1.trans h2
  have hT1 : N ^ 𝔠 * (B ^ (6 / 5 : ℝ) * Y₀) ≤ W ^ c₁ * Y₀ := by
    have hY0 : 0 ≤ Y₀ := (Real.exp_pos _).le
    have hWc : W ^ c₁ = W * W ^ (6 * q / (5 * 𝔠)) := by
      rw [hc₁, Real.rpow_add hW0, Real.rpow_one]
    rw [hWc]
    have h1 : N ^ 𝔠 * B ^ (6 / 5 : ℝ) ≤ W * W ^ (6 * q / (5 * 𝔠)) :=
      mul_le_mul hBn hB65N (Real.rpow_nonneg hBpos.le _) hW0.le
    calc N ^ 𝔠 * (B ^ (6 / 5 : ℝ) * Y₀) = (N ^ 𝔠 * B ^ (6 / 5 : ℝ)) * Y₀ := by ring
      _ ≤ (W * W ^ (6 * q / (5 * 𝔠))) * Y₀ := mul_le_mul_of_nonneg_right h1 hY0
  -- `T2`: `N^𝔠 W^{-D'} ≤ W^{-D}/8`
  have hWD1 : W ^ (-D') = W ^ (-D) * W⁻¹ ^ 2 := by
    rw [hD', show -(D + 2) = -D + (-1) + (-1) by ring, Real.rpow_add hW0, Real.rpow_add hW0,
      Real.rpow_neg_one]; ring
  have hWm1 : W⁻¹ ≤ 1 / 8 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW8
  have hWD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hT2 : N ^ 𝔠 * W ^ (-D') ≤ W ^ (-D) / 8 := by
    have hexp : W * W ^ (-D') = W ^ (-D) * W⁻¹ := by
      rw [hWD1]; field_simp
    calc N ^ 𝔠 * W ^ (-D') ≤ W * W ^ (-D') := mul_le_mul_of_nonneg_right hBn (Real.rpow_nonneg hW0.le _)
      _ = W ^ (-D) * W⁻¹ := hexp
      _ ≤ W ^ (-D) * (1 / 8) := by gcongr
      _ = W ^ (-D) / 8 := by ring
  -- `T3`: `(η⁻² + |𝒦|) N^{-D₁} ≤ W^{-D}/4`
  have hη2 : (etaT (STflowE z n) (s n))⁻¹ ^ 2 ≤ N ^ (2 * q) := by
    have h0 : 0 ≤ (etaT (STflowE z n) (s n))⁻¹ := (inv_pos.2 (etaT_pos (hE2 n) (hs1 n))).le
    calc (etaT (STflowE z n) (s n))⁻¹ ^ 2 ≤ (N ^ q) ^ 2 := pow_le_pow_left₀ h0 hη 2
      _ = N ^ (2 * q) := by
        rw [← Real.rpow_natCast (N ^ q) 2, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hK2 : ‖STKloop sz n (STflowE z n) (s n) σ a‖ ≤ N ^ (1 + q) := by
    refine hK.trans ?_
    rw [Real.rpow_add hN0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hB hN0.le
  have hsum : (etaT (STflowE z n) (s n))⁻¹ ^ 2 + ‖STKloop sz n (STflowE z n) (s n) σ a‖ ≤
      2 * N ^ (2 * q + 1) := by
    have h1 : N ^ (2 * q) ≤ N ^ (2 * q + 1) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : N ^ (1 + q) ≤ N ^ (2 * q + 1) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    linarith
  have hN21 : N ^ (2 * q + 1) ≤ W ^ ((2 * q + 1) / 𝔠) :=
    size_rpow_le_W_rpow sz h𝔠 n hBn (τ := 2 * q + 1) (by positivity)
  have hND : N ^ (-D₁) ≤ W ^ (-D₁) :=
    Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
  have hT3 : ((etaT (STflowE z n) (s n))⁻¹ ^ 2 + ‖STKloop sz n (STflowE z n) (s n) σ a‖) * N ^ (-D₁) ≤
      W ^ (-D) / 4 := by
    have hpp : W ^ ((2 * q + 1) / 𝔠) * W ^ (-D₁) = W ^ (-D) * W⁻¹ := by
      rw [← Real.rpow_add hW0, show (2 * q + 1) / 𝔠 + -D₁ = -D + (-1) by rw [hD₁]; ring,
        Real.rpow_add hW0, Real.rpow_neg_one]
    calc ((etaT (STflowE z n) (s n))⁻¹ ^ 2 + ‖STKloop sz n (STflowE z n) (s n) σ a‖) * N ^ (-D₁)
        ≤ (2 * W ^ ((2 * q + 1) / 𝔠)) * W ^ (-D₁) := by
          apply mul_le_mul (hsum.trans (by linarith)) hND (Real.rpow_nonneg hN0.le _) (by positivity)
      _ = 2 * (W ^ (-D) * W⁻¹) := by rw [mul_assoc, hpp]
      _ ≤ 2 * (W ^ (-D) * (1 / 8)) := by gcongr
      _ = W ^ (-D) / 4 := by ring
  -- assembly
  change ‖STExpErr sz n (STflowE z n) (s n) σ a‖ ≤ W ^ (-D)
  refine hbd.trans ?_
  have hmul := mul_le_mul_of_nonneg_left hZle (Real.rpow_nonneg hN0.le 𝔠)
  have hexp : N ^ 𝔠 * (B ^ (6 / 5 : ℝ) * Y₀ + W ^ (-D')) = N ^ 𝔠 * (B ^ (6 / 5 : ℝ) * Y₀) + N ^ 𝔠 * W ^ (-D') := by
    ring
  linarith


/-- **`(deccA0)` at the start `s` passes to every later start `v`** (`ℓ_s ≤ ℓ_v`, `g ≥ 0`, `s ≤ v < 1`): the kernel pins ask
for the decay at every `v ∈ [s_n, u_n]` of their index set (`STEKDecay`). -/
theorem expIniI_fastDecay_mono {d L n : ℕ} {g s v W ε D : ℝ} (A : (Fin n → Zd d L) → ℂ) (hg : 0 ≤ g)
    (hW : 0 ≤ W) (hsv : s ≤ v) (hv : v < 1) (h : EKFastDecay g s W ε D A) :
    EKFastDecay g v W ε D A := by
  have hell : ellT L g s ≤ ellT L g v := by
    unfold ellT
    refine min_le_min (max_le_max ?_ le_rfl) le_rfl
    have hv0 : 0 < 1 - v := by linarith
    have hs0 : 0 < 1 - s := by linarith
    rw [abs_of_pos hv0, abs_of_pos hs0]
    exact div_le_div_of_nonneg_left hg (Real.sqrt_pos.2 hv0) (Real.sqrt_le_sqrt (by linarith))
  intro a ⟨i, j, hij⟩
  exact h a ⟨i, j, (mul_le_mul_of_nonneg_left hell (Real.rpow_nonneg hW _)).trans hij⟩


/-! ## 3. The kernel side conditions (window, lower control) -/

/-- The window `STEKWin sz s u` of the kernel pins on `u ∈ [s,t]` in regime (i): `u ≤ t ≤ 1 - ilambda²/L²` from
`STReg5I`, and `W⁻¹ ≤ (1-t)/(1-s) ≤ (1-u)/(1-s)` from `(con_st_ind)` (`st_window`, `d 𝔠_d < 1`). -/
private theorem expIniI_window {d : ℕ} {𝔠d 𝔡 : ℝ} (sz : Sizes d) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1)
    (hWO : sz.WO 𝔡) (hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop) {s t u : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hcon : STConStInd sz 𝔠d s t) (hR : STReg5I sz s t) : STEKWin sz s u := by
  refine ⟨hs0, hsu, fun n => by linarith [(hR n).1, hut n], fun n => lt_of_le_of_lt (hut n) (ht1 n), ?_⟩
  filter_upwards [st_window sz h𝔠d hdc hcon hWO hW hs0 ht1] with n hn
  refine hn.trans ?_
  have hxs : 0 < 1 - s n := by linarith [hst n, ht1 n]
  exact div_le_div_of_nonneg_right (by linarith [hut n]) hxs.le

/-- `T_s ≥ N^{-3}` (`T_s ≥ B_s³ ≥ N^{-3}`, `expIniI_Bctl_ge`). -/
private theorem expIniI_Ts_ge {d : ℕ} (sz : Sizes d) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ STExpTarget sz n s := by
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hB := expIniI_Bctl_ge sz n hs0 hs1
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ (sz.Bctl n s) ^ 3 := by
    rw [Real.rpow_neg hN0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hB 3
  exact h1.trans (st6_cube_le_target sz n hs1)

/-- `X = T_s` is polynomially bounded below by `N^{-3}`, for every `n`: the event of `STEKLow` is the whole space. -/
private theorem expIniI_low {d : ℕ} (sz : Sizes d) {s u : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n < 1) :
    STEKLow sz s u (fun n _ _ => STExpTarget sz n (s n)) :=
  ⟨3, HighProbAt.of_eventually_univ (Eventually.of_forall fun n _ _ => expIniI_Ts_ge sz n (hs0 n) (hs1 n))⟩

/-- `M ≤ W^a` eventually, for `a > 0` (`W ≥ N^𝔠 → ∞`; copy of the `private` `prec_W_rpow_ge`, `Evolution/Prec.lean:54`). -/
private theorem expIniI_W_rpow_ge {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hSz : sz.SizeTendsto)
    (hBw : sz.Bandwidth 𝔠) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∀ᶠ n in atTop, M ≤ ((sz.W n : ℕ) : ℝ) ^ a := by
  have hf : ∀ᶠ n in atTop, M ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * a) :=
    ((tendsto_rpow_atTop (mul_pos h𝔠 ha)).comp hSz).eventually (eventually_ge_atTop M)
  filter_upwards [hf, hBw] with n hn hb
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc M ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * a) := hn
    _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ a := Real.rpow_mul hN _ _
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hb ha.le

/-- `L^d ≤ N ≤ W^{1/𝔠}` from `W ≥ N^𝔠` (copy of the `private` `prec_L_pow_le`, `Evolution/Prec.lean:73`). -/
private theorem expIniI_L_pow_le {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (n : ℕ)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) :
    ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
  have hLW : (sz.L n) ^ d ≤ sz.size n := by
    have hW : 0 < sz.W n := sz.W_pos n
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW) d
  have h1 : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hLW
  have h2 := sz.size_rpow_le_W_rpow h𝔠 n hb (τ := 1) zero_le_one
  rw [Real.rpow_one] at h2
  exact h1.trans h2

/-- **A polynomial bound on `f_s`**: `‖f_{s,σ}‖_∞ ≤ N^{2q+2}`, `q = 2 + |ε|` (a.s. envelope `η_s^{-2}`, `|𝒦| ≤ N B`
from `stKbound_of_flow`, `η_s⁻¹, B ≤ N^q`). -/
private theorem expIniI_env_poly {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) (z : ℕ → ℂ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * (2 + |ε|) + 2) := by
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hflow.1
  have hs1 : ∀ n, s n < 1 := st5_t_lt_one sz hflow hsT
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hflow
  have hd0 : 0 < d := by omega
  set e : ℝ := 1 + |ε| with he
  set q : ℝ := e + 1 with hq
  have hq1 : 1 ≤ q := by have := abs_nonneg ε; rw [hq, he]; linarith
  set c0 : ℝ := Real.sqrt (2 * κ) / 2 with hc0
  have hc0pos : 0 < c0 := by positivity
  have hKb := (st6_prec_det_iff sz hSz (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p => ‖STKloop sz n (STflowE z n) (s n) p.1 p.2‖) (fun n _ => (sz.Bctl n (s n)) ^ (2 - 1))).1
    (stKbound_of_flow sz hd hκ hflow s hs0 hs1 2 (by norm_num)) 1 one_pos
  have hNge : ∀ᶠ n in atTop, max 8 (4 / c0) ≤ ((sz.size n : ℕ) : ℝ) := hSz.eventually (eventually_ge_atTop _)
  filter_upwards [hKb, hNge] with n hKn hNn
  intro σ
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN8 : 8 ≤ N := (le_max_left _ _).trans hNn
  have hNc0 : 4 / c0 ≤ N := (le_max_right _ _).trans hNn
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hxinv : (1 - s n)⁻¹ ≤ 4 * N ^ e := expIniI_inv_one_sub_le sz hκ hflow n (hsT n)
  have hNq : N ^ q = N ^ e * N := by rw [hq, Real.rpow_add hN0, Real.rpow_one]
  have hNe0 : 0 < N ^ e := Real.rpow_pos_of_pos hN0 _
  have hB : sz.Bctl n (s n) ≤ N ^ q := by
    have h1 := expIniI_Bctl_le sz n (hs1 n)
    rw [hNq]
    nlinarith
  have hη : (etaT (STflowE z n) (s n))⁻¹ ≤ N ^ q := by
    have hIm : c0 ≤ (mE (STflowE z n)).im := st6_mE_im_ge hκ (st6_flowE_le sz hflow n)
    have hx0 : 0 < 1 - s n := by linarith [hs1 n]
    have hηlow : (1 - s n) * c0 ≤ etaT (STflowE z n) (s n) := by
      unfold etaT; exact mul_le_mul_of_nonneg_left hIm hx0.le
    have hpos : 0 < (1 - s n) * c0 := by positivity
    calc (etaT (STflowE z n) (s n))⁻¹ ≤ ((1 - s n) * c0)⁻¹ := inv_anti₀ hpos hηlow
      _ = (1 - s n)⁻¹ * c0⁻¹ := mul_inv _ _
      _ ≤ (4 * N ^ e) * c0⁻¹ := by gcongr
      _ = N ^ e * (4 / c0) := by field_simp
      _ ≤ N ^ e * N := by gcongr
      _ = N ^ q := hNq.symm
  have hnn : 0 ≤ N ^ (2 * (2 + |ε|) + 2) := Real.rpow_nonneg hN0.le _
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun a => ?_
  have hK : ‖STKloop sz n (STflowE z n) (s n) σ a‖ ≤ N * sz.Bctl n (s n) := by
    have := hKn (σ, a)
    simpa [Real.rpow_one] using this
  have hη2 : (etaT (STflowE z n) (s n))⁻¹ ^ 2 ≤ N ^ (2 * q) := by
    have h0 : 0 ≤ (etaT (STflowE z n) (s n))⁻¹ := (inv_pos.2 (etaT_pos (hE2 n) (hs1 n))).le
    calc (etaT (STflowE z n) (s n))⁻¹ ^ 2 ≤ (N ^ q) ^ 2 := pow_le_pow_left₀ h0 hη 2
      _ = N ^ (2 * q) := by
        rw [← Real.rpow_natCast (N ^ q) 2, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hK2 : ‖STKloop sz n (STflowE z n) (s n) σ a‖ ≤ N ^ (1 + q) := by
    refine hK.trans ?_
    rw [Real.rpow_add hN0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hB hN0.le
  have h1 : N ^ (2 * q) ≤ N ^ (2 * q + 1) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h2 : N ^ (1 + q) ≤ N ^ (2 * q + 1) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h3 : 2 * N ^ (2 * q + 1) ≤ N ^ (2 * (2 + |ε|) + 2) := by
    have e1 : N ^ (2 * (2 + |ε|) + 2) = N * N ^ (2 * q + 1) := by
      rw [← Real.rpow_one_add' hN0.le (by linarith)]
      congr 1
      rw [hq, he]; ring
    rw [e1]
    have : 0 ≤ N ^ (2 * q + 1) := Real.rpow_nonneg hN0.le _
    nlinarith
  have := expIniI_envelope sz n (hE2 n) (hs1 n) σ a
  linarith

end RBM.Gauss.Sizes

/-! ## 4. `σ₁ = σ₂`: `(sum_res_2_NAL)` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`(sum_res_2_NAL)` applied to `f_s`** (`3_5:1649`): for `σ₁ = σ₂`, regime (i), `𝒰_{s,u,σ} f_s ≺ T_u` uniformly in
`u ∈ [s,t]` (the ratio `(ilambda² + 1-s)/(ilambda² + 1-u) ≤ 2` since `1-s ≤ ilambda²`; the decay of `f_s` is
`expIniI_fastDecay`, `L^∞` is `(Eq:Gtlp_exp+IND)`); the first conjunct of `STExpIniIConcl` with an explicit
`𝔠_d` (`d 𝔠_d < 1`). -/
theorem expIniI_same {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1)
    (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t)
    (hDec : STDecay sz (STflowE z) s) (hExp : STExp2 sz (STflowE z) s) (hcon : STConStInd sz 𝔠d s t) :
    Prec sz (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hs1 : ∀ n, s n < 1 := fun n => lt_trans (hst n) (ht1 n)
  have hX : ∀ n, 0 ≤ STExpTarget sz n (s n) := fun n => st6_target_nonneg sz n (hs1 n)
  have hκ' : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  have hlam0 : ∀ᶠ n in atTop, 0 ≤ sz.lam n := (st6_lam_pos sz hflow.1.2.2.2.2).mono fun n h => h.le
  refine st6_precU_of_forall_seq sz hsz (fun n => (hst n).le)
    (W := fun n => {σ : Fin 2 → Bool // STSigSame σ} × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) w.1.1 (s n) u
      (fun b => STExpErr sz n (STflowE z n) (s n) w.1.1 b) w.2‖)
    (fun n u _ => STExpTarget sz n u) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hwin := expIniI_window sz h𝔠d hdc hflow.1.2.2.2.2 (scaleFacts3_W_tendsto sz hflow.1) hs0 hst hsu hut ht1 hcon hR
  have key : ∀ σ : {σ : Fin 2 → Bool // STSigSame σ}, sz.Prec (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) a‖)
      (fun n _ _ => STExpTarget sz n (u n)) := by
    intro σ
    have hσ : ∃ k, σ.1 k = σ.1 (finRotate 2 k) := by
      refine ⟨0, ?_⟩
      have : finRotate 2 (0 : Fin 2) = 1 := by decide
      rw [this]; exact σ.2
    have hdec : STEKDecay sz s u (fun n _ _ => fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) := by
      intro ε' D hε' hD
      refine HighProbAt.of_eventually_univ ?_
      filter_upwards [expIniI_fastDecay hd hκ sz z hflow s hs0 (fun n => (hst n).le.trans (htT n)) hDec ε' D hε' hD,
        hlam0] with n hn hl ω v
      exact expIniI_fastDecay_mono _ hl (Nat.cast_nonneg _) v.2.1 (lt_of_le_of_lt v.2.2 (hu1 n)) (hn σ.1)
    have hdom := st6_prec_pi_norm sz hsz (E := STflowE z) (s := s) hX hExp σ.1 (V := fun n => TimeIcc s u n)
    have hk := stek_sumRes2NAL_holds d hd 2 le_rfl (Real.sqrt (2 * κ) / 2) 𝔠 𝔡 hκ' sz hflow.1 s u hwin
      (fun n => mE (STflowE z n)) (fun n => norm_mE (st6_flowE_lt_two sz hκ hflow n).le)
      (fun n => st6_mE_im_ge hκ (st6_flowE_le sz hflow n)) σ.1 hσ
      (fun n _ _ => fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) hdec
      (fun n _ _ => STExpTarget sz n (s n)) (expIniI_low sz hs0 hs1) hdom
    have h2 := StochDomAt.precomp_param hk
      (fun n (_ : Fin 2 → Zd d (sz.L n)) => (⟨s n, le_rfl, hsu n⟩ : TimeIcc s u n))
    have h3 : sz.Prec (U := fun n => Fin 2 → Zd d (sz.L n))
        (fun n a _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
          (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) a‖)
        (fun n _ _ => ((sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|)) ^ (2 - 1) * STExpTarget sz n (s n)) := by
      refine StochDomAt.of_le_left (ξ₁ := fun n (_ : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
        ‖UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ.1) (s n) (u n)
          (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)‖) (fun n a ω => ?_) h2
      exact norm_le_pi_norm (UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ.1) (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a
    refine st5_prec_mono sz hsz (c := 2) h3 (Eventually.of_forall fun n a ω => ?_)
      (fun n a ω => st6_target_nonneg sz n (hu1 n))
    have hx0 : 0 < 1 - u n := by linarith [hu1 n]
    have hxs : 0 ≤ 1 - s n := by linarith [hs1 n]
    have hden : 0 < sz.lam n ^ 2 + |1 - u n| := by
      rw [abs_of_pos hx0]; positivity
    have hratio : (sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|) ≤ 2 := by
      rw [div_le_iff₀ hden, abs_of_nonneg hxs, abs_of_pos hx0]
      nlinarith [(hR n).2, sq_nonneg (sz.lam n)]
    have hTs := st6_target_mono sz n (hsu n) (hu1 n)
    have hT0 := hX n
    have hr0 : 0 ≤ (sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|) := by positivity
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    calc (sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|) * STExpTarget sz n (s n)
        ≤ 2 * STExpTarget sz n (s n) := mul_le_mul_of_nonneg_right hratio hT0
      _ ≤ 2 * STExpTarget sz n (u n) := by linarith
  exact st6_prec_of_forall_fin sz hsz
    (fun n (σ : {σ : Fin 2 → Bool // STSigSame σ}) (a : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) a‖)
    (fun n _ _ _ => STExpTarget sz n (u n)) key

end RBM.Gauss.Sizes

/-! ## 5. `𝒬_s f_s`: `lem_+Q` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The three inputs of `(sum_res_2)` for `𝒬_s f_s`** (deterministic, eventually): (i) `‖𝒬_s f_s‖_∞ ≤ N^τ T_s` by
`lem_+Q` (`stQopNorm_holds`, `m = 1`, `Λ = 𝔡⁻¹`, `K = 1/𝔠`; `ε_Q = min(1/2, τ d/(4 C_n))`, `D_Q = C_n + 5/𝔠 + 1`) from
`‖f_s‖ ≤ N^{τ/4} T_s` (`STExp2`) and the decay of `f_s` (`expIniI_fastDecay`); (ii) `(deccA0)` of
`𝒬_s f_s = f_s - (f_s - 𝒬_s f_s)` (`expIniI_fastDecay`, `stQop_sub_fastDecay`, `‖f_s‖ ≤ W^{C₀}`); (iii) `(sumAzero)`
(`𝒫 ∘ 𝒬_s = 0`, `QopAlgebra_Psum_Qop`). Positive mollifier constants: both lemmas of `lem_+Q` use `0 < c`. -/
theorem expIniI_Qop {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) (z : ℕ → ℂ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ lemT (z n))
    (hDec : STDecay sz (STflowE z) s) (hExp : STExp2 sz (STflowE z) s) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) :
    (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      ‖STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (s n)) ∧
    (∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKFastDecay (sz.lam n) (s n) ((sz.W n : ℕ) : ℝ) ε' D
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b))) ∧
    (∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKSumZero (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b))) := by
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hflow.1
  have hs1 : ∀ n, s n < 1 := st5_t_lt_one sz hflow hsT
  have hsT' : ∀ n, s n ≤ lemT (z n) := hsT
  have hd0 : 0 < d := by omega
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := scaleFacts3_W_tendsto sz hflow.1
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `lem_+Q`
    intro τ hτ
    obtain ⟨Cn, hCn, hpin⟩ := stQopNorm_holds d hd 1 𝔡⁻¹ (1 / 𝔠) C c (inv_pos.2 h𝔡) (one_div_pos.2 h𝔠) hC hc
    set εQ : ℝ := min (1 / 2) (τ * d / (4 * Cn)) with hεQ
    have hεQ0 : 0 < εQ := lt_min (by norm_num) (by positivity)
    have hεQ1 : εQ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    set DQ : ℝ := Cn + 5 / 𝔠 + 1 with hDQ
    have h5c' : 0 < 5 / 𝔠 := by positivity
    have hDQ1 : 1 < DQ := by rw [hDQ]; linarith
    have hf1 := fun ε' D (hε' : 0 < ε') (hD : 0 < D) =>
      expIniI_fastDecay hd hκ sz z hflow s hs0 hsT' hDec ε' D hε' hD
    have hExpD := (st6_prec_det_iff sz hSz (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p => ‖STExpErr sz n (STflowE z n) (s n) p.1 p.2‖)
      (fun n _ => (sz.Bctl n (s n)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (s n)))).1 hExp (τ / 4) (by positivity)
    filter_upwards [hϑ, hf1 εQ DQ hεQ0 (by linarith), hExpD, hBw, hlam,
      expIniI_W_rpow_ge sz h𝔠 hSz hBw hεQ0 4, hSz.eventually (eventually_ge_atTop (1 : ℝ)),
      ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τ / 2)).comp hSz).eventually (eventually_ge_atTop (2 : ℝ))]
      with n hϑn hfn hExpn hBn hlamn h4 hN1 hN2 σ
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
    have hN0 : 0 < N := by linarith
    have hW0 : 0 ≤ W := Nat.cast_nonneg _
    have hW1 : 1 < W := by
      by_contra hcon
      push Not at hcon
      have := Real.rpow_le_one hW0 hcon hεQ0.le
      linarith
    have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ (1 / 𝔠) := expIniI_L_pow_le sz h𝔠 n hBn
    have hQ := hpin (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 hlamn.2 W εQ DQ hW1 hεQ0 hεQ1 hDQ1 h4 hLW
      (ϑ n) hϑn (s n) (hs0 n) (hs1 n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b) (hfn σ)
    have hT0 : 0 ≤ STExpTarget sz n (s n) := st6_target_nonneg sz n (hs1 n)
    have hfnorm : ‖(fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖ ≤
        N ^ (τ / 4) * STExpTarget sz n (s n) :=
      (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) hT0)).2 fun a => hExpn (σ, a)
    have hWC : W ^ (Cn * εQ) ≤ N ^ (τ / 4) := by
      have h1 : W ^ (Cn * εQ) ≤ N ^ (Cn * εQ / d) := sz.W_rpow_le hd0 n (by positivity)
      refine h1.trans (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
      rw [div_le_iff₀ hd0']
      have : Cn * εQ ≤ Cn * (τ * d / (4 * Cn)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hCn.le
      have e : Cn * (τ * d / (4 * Cn)) = τ / 4 * d := by field_simp
      linarith
    have hTail : W ^ (-DQ + Cn) ≤ N ^ (-(5 : ℝ)) := by
      have hexp : -DQ + Cn ≤ -(5 / 𝔠) := by rw [hDQ]; linarith
      have h1 : W ^ (-DQ + Cn) ≤ W ^ (-(5 / 𝔠)) := Real.rpow_le_rpow_of_exponent_le hW1.le hexp
      have hNc : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
      have h5c : 0 < 5 / 𝔠 := by positivity
      have h2 : W ^ (-(5 / 𝔠)) ≤ (N ^ 𝔠) ^ (-(5 / 𝔠)) :=
        Real.rpow_le_rpow_of_nonpos hNc hBn (by linarith)
      have h3 : (N ^ 𝔠) ^ (-(5 / 𝔠)) = N ^ (-(5 : ℝ)) := by
        rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
      exact h1.trans (h2.trans h3.le)
    have hN35 : N ^ (-(5 : ℝ)) ≤ N ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have hTs : N ^ (-(3 : ℝ)) ≤ STExpTarget sz n (s n) := expIniI_Ts_ge sz n (hs0 n) (hs1 n)
    have hxx : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hyy : N ^ (τ / 4) * N ^ (τ / 4) = N ^ (τ / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    set x : ℝ := N ^ (τ / 2) with hx
    set T : ℝ := STExpTarget sz n (s n) with hT
    have ha : W ^ (Cn * εQ) * ‖(fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖ ≤ x * T := by
      calc W ^ (Cn * εQ) * ‖(fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖
          ≤ N ^ (τ / 4) * (N ^ (τ / 4) * T) :=
            mul_le_mul hWC hfnorm (norm_nonneg _) (Real.rpow_nonneg hN0.le _)
        _ = x * T := by rw [← mul_assoc, hyy]
    have hkey : x * x * T - x * T - T = T * (x * x - x - 1) := by ring
    have hN2' : 2 ≤ x := hN2
    have hpos : 0 ≤ x * x - x - 1 := by nlinarith
    calc ‖STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖
        ≤ W ^ (Cn * εQ) * ‖(fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖ + W ^ (-DQ + Cn) := hQ
      _ ≤ x * T + T := add_le_add ha (hTail.trans (hN35.trans hTs))
      _ ≤ N ^ τ * T := by
        rw [← hxx]; nlinarith [mul_nonneg hT0 hpos]
  · -- (ii) `(deccA0)` of `𝒬_s f_s`
    intro ε' D hε' hD
    obtain ⟨W₀, hW₀1, hW₀⟩ := stQop_sub_fastDecay d 1 (1 / 𝔠) C c ((2 * (2 + |ε|) + 2) / 𝔠) ε' (D + 1)
      hC hc hε'
    filter_upwards [hϑ, expIniI_fastDecay hd hκ sz z hflow s hs0 hsT' hDec ε' (D + 1) hε' (by linarith),
      expIniI_env_poly hd hκ sz z hflow s hs0 hsT', hBw, hlam,
      hWt.eventually (eventually_ge_atTop (max W₀ 2))] with n hϑn hfn henv hBn hlamn hWn σ
    intro a ⟨i, j, hij⟩
    set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
    have hW0 : W₀ ≤ W := (le_max_left _ _).trans hWn
    have hW2 : 2 ≤ W := (le_max_right _ _).trans hWn
    have hWpos : 0 < W := by linarith
    have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ (1 / 𝔠) := expIniI_L_pow_le sz h𝔠 n hBn
    have hA : ‖(fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖ ≤ W ^ ((2 * (2 + |ε|) + 2) / 𝔠) :=
      (henv σ).trans (sz.size_rpow_le_W_rpow h𝔠 n hBn (τ := 2 * (2 + |ε|) + 2) (by positivity))
    have h1 := hfn σ a ⟨i, j, hij⟩
    have h2 := hW₀ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 W hW0 hLW (ϑ n) hϑn (s n) (hs0 n) (hs1 n)
      (fun b => STExpErr sz n (STflowE z n) (s n) σ b) hA a ⟨i, j, hij⟩
    change ‖STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b) a‖ ≤ W ^ (-D)
    have e : STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b) a =
        STExpErr sz n (STflowE z n) (s n) σ a -
          ((fun b => STExpErr sz n (STflowE z n) (s n) σ b) -
            STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)) a := by
      simp only [Pi.sub_apply]; ring
    rw [e]
    have hWD : W ^ (-(D + 1)) = W ^ (-D) * W⁻¹ := by
      rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have hWi : W⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
    have hWD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hWpos _
    calc ‖STExpErr sz n (STflowE z n) (s n) σ a -
          ((fun b => STExpErr sz n (STflowE z n) (s n) σ b) -
            STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)) a‖
        ≤ ‖STExpErr sz n (STflowE z n) (s n) σ a‖ +
          ‖((fun b => STExpErr sz n (STflowE z n) (s n) σ b) -
            STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)) a‖ := norm_sub_le _ _
      _ ≤ 2 * W ^ (-(D + 1)) := by linarith
      _ = 2 * (W ^ (-D) * W⁻¹) := by rw [hWD]
      _ ≤ 2 * (W ^ (-D) * (1 / 2)) := by gcongr
      _ = W ^ (-D) := by ring
  · -- (iii) `(sumAzero)`
    filter_upwards [hϑ] with n hn σ
    intro i₀ hi₀ x
    have : i₀ = 0 := Fin.ext hi₀
    subst this
    exact QopAlgebra_Psum_Qop (ϑ n) (hn.1 (s n)) _ x

end RBM.Gauss.Sizes

/-! ## 6. `σ₁ ≠ σ₂`: `(sum_res_2)` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

open Classical in
/-- **`(sum_res_2)` applied to `𝒬_s f_s`** (`3_5:1659`): for `σ₁ ≠ σ₂`, regime (i), positive mollifier constants,
`𝒰_{s,u,σ} 𝒬_s f_s ≺ T_u` uniformly in `u ∈ [s,t]`: the three inputs are `expIniI_Qop`; the kernel pin
`STEKSumRes2` asks `(sumAzero)` for every `n` while the mollifier hypothesis is eventual, so the tensor is
`if STMollifierProps … then 𝒬_s f_s else 0` (equal to `𝒬_s f_s` eventually; the ratio `≤ 2` gives `≤ 4`).
The second conjunct of `STExpIniIConcl` for `0 < C`, `0 < c`. -/
theorem expIniI_mixed {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1)
    (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t)
    (hDec : STDecay sz (STflowE z) s) (hExp : STExp2 sz (STflowE z) s) (hcon : STConStInd sz 𝔠d s t)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) :
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hs1 : ∀ n, s n < 1 := fun n => lt_trans (hst n) (ht1 n)
  have hsT : ∀ n, s n ≤ lemT (z n) := fun n => (hst n).le.trans (htT n)
  have hX : ∀ n, 0 ≤ STExpTarget sz n (s n) := fun n => st6_target_nonneg sz n (hs1 n)
  have hκ' : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  have hlam0 : ∀ᶠ n in atTop, 0 ≤ sz.lam n := (st6_lam_pos sz hflow.1.2.2.2.2).mono fun n h => h.le
  obtain ⟨hQ1, hQ2, hQ3⟩ := expIniI_Qop hd hκ sz z hflow s hs0 hsT hDec hExp C c hC hc ϑ hϑ
  refine st6_precU_of_forall_seq sz hsz (fun n => (hst n).le)
    (W := fun n => {σ : Fin 2 → Bool // STSigMixed σ} × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) w.1.1 (s n) u
      (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) w.1.1 b)) w.2‖)
    (fun n u _ => STExpTarget sz n u) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hwin := expIniI_window sz h𝔠d hdc hflow.1.2.2.2.2 (scaleFacts3_W_tendsto sz hflow.1) hs0 hst hsu hut ht1 hcon hR
  have key : ∀ σ : {σ : Fin 2 → Bool // STSigMixed σ}, sz.Prec (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a‖)
      (fun n _ _ => STExpTarget sz n (u n)) := by
    intro σ
    -- the tensor of the kernel pin: `𝒬_s f_s` where the mollifier hypothesis holds, `0` elsewhere
    let Q0 : ∀ n, (Fin 2 → Zd d (sz.L n)) → ℂ := fun n =>
      if STMollifierProps (d := d) (sz.lam n) C c (ϑ n) then
        STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) else 0
    let 𝒜 : ∀ n, TimeIcc s u n → sz.SeqΩ → (Fin 2 → Zd d (sz.L n)) → ℂ := fun n _ _ => Q0 n
    have hQ0 : ∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n) →
        Q0 n = STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b) :=
      fun n hn => by simp [Q0, hn]
    have hdec : STEKDecay sz s u 𝒜 := by
      intro ε' D hε' hD
      refine HighProbAt.of_eventually_univ ?_
      filter_upwards [hQ2 ε' D hε' hD, hϑ, hlam0] with n hn hϑn hl ω v
      change EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' D (Q0 n)
      rw [hQ0 n hϑn]
      exact expIniI_fastDecay_mono _ hl (Nat.cast_nonneg _) v.2.1 (lt_of_le_of_lt v.2.2 (hu1 n)) (hn σ.1)
    have hzero : ∀ n v ω, EKSumZero (𝒜 n v ω) := by
      intro n v ω
      change EKSumZero (Q0 n)
      by_cases hn : STMollifierProps (d := d) (sz.lam n) C c (ϑ n)
      · rw [hQ0 n hn]
        intro i₀ hi₀ x
        have : i₀ = 0 := Fin.ext hi₀
        subst this
        exact QopAlgebra_Psum_Qop (ϑ n) (hn.1 (s n)) _ x
      · have : Q0 n = 0 := by simp [Q0, hn]
        rw [this]
        intro i₀ hi₀ x
        simp
    have hdom : sz.Prec (U := fun n => TimeIcc s u n) (fun n v ω => ‖𝒜 n v ω‖)
        (fun n _ _ => STExpTarget sz n (s n)) := by
      refine (st6_prec_det_iff sz hsz (V := fun n => TimeIcc s u n)
        (fun n _ => ‖Q0 n‖) (fun n _ => STExpTarget sz n (s n))).2 ?_
      intro τ hτ
      filter_upwards [hQ1 τ hτ, hϑ] with n hn hϑn v
      rw [hQ0 n hϑn]
      exact hn σ.1
    have hk := stek_sumRes2_holds d hd 2 le_rfl (Real.sqrt (2 * κ) / 2) 𝔠 𝔡 hκ' sz hflow.1 s u hwin
      (fun n => mE (STflowE z n)) (fun n => norm_mE (st6_flowE_lt_two sz hκ hflow n).le)
      (fun n => st6_mE_im_ge hκ (st6_flowE_le sz hflow n)) σ.1 𝒜 hdec hzero
      (fun n _ _ => STExpTarget sz n (s n)) (expIniI_low sz hs0 hs1) hdom
    have h2 := StochDomAt.precomp_param hk
      (fun n (_ : Fin 2 → Zd d (sz.L n)) => (⟨s n, le_rfl, hsu n⟩ : TimeIcc s u n))
    have h3 : sz.Prec (U := fun n => Fin 2 → Zd d (sz.L n))
        (fun n a _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a‖)
        (fun n _ _ => ((sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|)) ^ 2 * STExpTarget sz n (s n)) := by
      refine StochDomAt.of_subset (ξ₁ := fun n (_ : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) =>
        ‖UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ.1) (s n) (u n) (Q0 n)‖)
        (ζ₁ := fun n _ _ => ((sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|)) ^ 2 * STExpTarget sz n (s n))
        h2 (fun τ hτ => ⟨τ, hτ, ?_⟩)
      filter_upwards [hϑ] with n hn ω ⟨a, ha⟩
      refine ⟨a, lt_of_lt_of_le ha ?_⟩
      change ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a‖ ≤
        ‖UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ.1) (s n) (u n) (Q0 n)‖
      rw [hQ0 n hn]
      exact norm_le_pi_norm (UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ.1) (s n) (u n)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b))) a
    refine st5_prec_mono sz hsz (c := 4) h3 (Eventually.of_forall fun n a ω => ?_)
      (fun n a ω => st6_target_nonneg sz n (hu1 n))
    have hx0 : 0 < 1 - u n := by linarith [hu1 n]
    have hxs : 0 ≤ 1 - s n := by linarith [hs1 n]
    have hden : 0 < sz.lam n ^ 2 + |1 - u n| := by
      rw [abs_of_pos hx0]; positivity
    have hratio : (sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|) ≤ 2 := by
      rw [div_le_iff₀ hden, abs_of_nonneg hxs, abs_of_pos hx0]
      nlinarith [(hR n).2, sq_nonneg (sz.lam n)]
    have hr0 : 0 ≤ (sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|) := by positivity
    have hr2 : ((sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|)) ^ 2 ≤ 4 := by nlinarith
    have hTs := st6_target_mono sz n (hsu n) (hu1 n)
    have hT0 := hX n
    calc ((sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|)) ^ 2 * STExpTarget sz n (s n)
        ≤ 4 * STExpTarget sz n (s n) := mul_le_mul_of_nonneg_right hr2 hT0
      _ ≤ 4 * STExpTarget sz n (u n) := by linarith
  exact st6_prec_of_forall_fin sz hsz
    (fun n (σ : {σ : Fin 2 → Bool // STSigMixed σ}) (a : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a‖)
    (fun n _ _ _ => STExpTarget sz n (u n)) key

end RBM.Gauss.Sizes

/-! ## 7. Finding T2223a: the class of the merged second conjunct contains non-decaying mollifiers -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **T2223a**: a mollifier family with `c ≥ 0`, translated in the indices `a_i`, `i ≠ 0`, through a fixed shift `v`,
satisfies `STMollifierProps` with `c = 0` (no decay): the merged `STExpIniIConcl`, `STExpIntQConcl`, `STExpWardIConcl`
quantify over every `(C, c)`, hence also over such families, which are not the mollifier of `Def:QtPt`
(`rmk:choosechi`, `c > 0`).  The shift is a bijection of `{a : a 0 = a₁}`, and `exp(-c S/ℓ) ≤ 1` for `c, S ≥ 0`, `ℓ ≥ 1`. -/
theorem expIniI_props_shift {d L m : ℕ} [NeZero L] (g C c : ℝ) (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ)
    (v : Zd d L) (hc : 0 ≤ c) (h : STMollifierProps (d := d) g C c ϑ) :
    STMollifierProps (d := d) g C 0 (fun t a => ϑ t (fun i => if i = 0 then a 0 else a i + v)) := by
  set φ : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) := fun a i => if i = 0 then a 0 else a i + v with hφ
  have hφ0 : ∀ a, φ a 0 = a 0 := fun a => by simp [hφ]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- clause 1: the shift permutes `{a : a 0 = a₁}`
    intro t a₁
    let e : (Fin (m + 1) → Zd d L) ≃ (Fin (m + 1) → Zd d L) :=
      { toFun := φ
        invFun := fun a i => if i = 0 then a 0 else a i - v
        left_inv := fun a => by
          funext i; by_cases hi : i = 0 <;> simp [hφ, hi]
        right_inv := fun a => by
          funext i; by_cases hi : i = 0 <;> simp [hφ, hi] }
    have := Finset.sum_equiv e (s := Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁))
      (t := Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁))
      (f := fun a => ϑ t (φ a)) (g := fun a => ϑ t a)
      (fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨fun h' => by rw [← h']; exact hφ0 a, fun h' => by rw [← hφ0 a]; exact h'⟩)
      (fun a _ => rfl)
    rw [show (∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ t (φ a)) = _ from this]
    exact h.1 t a₁
  · -- clause 2: `c = 0`, no decay needed
    intro t ht0 ht1 a
    have hℓ1 : 1 ≤ ellT L g t := one_le_ellT hL1
    have hℓ0 : 0 < ellT L g t := by linarith
    have hX : 0 < ((ellT L g t ^ d)⁻¹) ^ m := by positivity
    have hC : 0 ≤ C := by
      have h0 := h.2.1 0 le_rfl zero_lt_one 0
      have hℓ1' : 1 ≤ ellT L g 0 := one_le_ellT hL1
      have hX' : 0 < ((ellT L g 0 ^ d)⁻¹) ^ m := by positivity
      have hE : 0 < Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
          (zdistD d L ((0 : Fin (m + 1) → Zd d L) i - (0 : Fin (m + 1) → Zd d L) 0) : ℝ)) / ellT L g 0) :=
        Real.exp_pos _
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg (mul_pos hX' hE)
      nlinarith [norm_nonneg (ϑ 0 0)]
    have h1 := h.2.1 t ht0 ht1 (φ a)
    have hS : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (φ a i - φ a 0) : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hE1 : Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (φ a i - φ a 0) : ℝ)) /
        ellT L g t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (φ a i - φ a 0) : ℝ)) / ellT L g t := by
        positivity
      have e : -c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (φ a i - φ a 0) : ℝ)) / ellT L g t =
          -(c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (φ a i - φ a 0) : ℝ)) / ellT L g t) := by
        ring
      rw [e]; linarith
    simp only [neg_zero, zero_mul, zero_div, Real.exp_zero, mul_one]
    refine h1.trans ?_
    calc C * ((ellT L g t ^ d)⁻¹) ^ m * Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
          (zdistD d L (φ a i - φ a 0) : ℝ)) / ellT L g t) ≤ C * ((ellT L g t ^ d)⁻¹) ^ m * 1 :=
          mul_le_mul_of_nonneg_left hE1 (by positivity)
      _ = _ := mul_one _
  · exact fun a => h.2.2.1 (φ a)
  · intro t ht0 ht1 a
    exact h.2.2.2 t ht0 ht1 (φ a)

end RBM.Gauss.Sizes

/-! ## 8. The primed pin `STExpIniI'` (positive mollifier constants), its proof and its consumer -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `STExpIniIConcl` with `0 < C → 0 < c →` in the second conjunct (the constants of `STQopNorm`,
`stQop_sub_fastDecay`, and of the family `st6_mollifier_family` the consumer builds). -/
def STExpIniIConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2P sz STSigSame s t)
    (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
      (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b) p.2.2‖)
    (fun n p _ => STExpTarget sz n (p.1 : ℝ)) ∧
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))

/-- The primed pin: the shape `STIngR6` of the merged `STExpIniI` (`Step6Pins.lean:471`) with `STExpIniIConcl'`. -/
def STExpIniI' (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpIniIConcl' sz E s t)

/-- **The primed pin, proved** (`𝔠_d = 1/(100 d)`: `𝔠_d ≤ 1/100`, `d 𝔠_d = 1/100 < 1`): the first conjunct is
`expIniI_same`, the second is `expIniI_mixed`. -/
theorem stExpIniI'_holds (d : ℕ) : STExpIniI' d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have h𝔠d : 0 < 1 / (100 * (d : ℝ)) := by positivity
  have hdc : (d : ℝ) * (1 / (100 * (d : ℝ))) < 1 := by
    rw [show (d : ℝ) * (1 / (100 * (d : ℝ))) = 1 / 100 by field_simp]; norm_num
  refine ⟨1 / (100 * (d : ℝ)), h𝔠d, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · intro 𝔠 sz z hflow s t hs0 hst htT hR _ hDec hExp hcon _ _ _ _
    exact ⟨expIniI_same hd hκ h𝔠d hdc sz z hflow s t hs0 hst htT hR hDec hExp hcon,
      fun C c hC hc ϑ hϑ => expIniI_mixed hd hκ h𝔠d hdc sz z hflow s t hs0 hst htT hR hDec hExp hcon C c hC hc ϑ hϑ⟩

/-- **Step 6, regime (i), from its pins, with the primed initial-term pin `STExpIniI'`** (T2223): the merged
`ST_step6_caseI_of_pins` (`Induction/Step6Kit.lean:947-1028`, copied) with `hIni : STExpIniI' d`; the only change
of the proof is the application `hini.2 C c' hC hc' ϑ hϑ` (the family `st6_mollifier_family` has `0 < C`,
`0 < c'`).  `σ₁ = σ₂`: the plain Duhamel (`STExpIntI.1`) with the initial term `STExpIniI'.1`
(`(sum_res_2_NAL)`, ratio `≤ 2`); `σ₁ ≠ σ₂`: for a mollifier family (`st6_mollifier_family`, from the proved
`stMollifierEx_holds`) the `𝒬`-Duhamel (`STExpIntI.2`, identity from `STExpDuhamelQ`) with the initial term
`STExpIniI'.2` and `f_u = 𝒬_u f_u + (𝒫 f_u) ϑ_u`, `(𝒫 f_u) ϑ_u ≺ B³` from `STExpWardI` (`(eq:EPL-K)`); the premise
`(res_ELK_n=1)` of the Ward pin is compiled from `STImproveExpAver`. -/
theorem ST_step6_caseI_of_pins' {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
    (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d)
    (hIni : STExpIniI' d) (hInt : STExpIntI d) : STStep6I d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hDec hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := hIni hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ (min c₃ (min c₄ c₅))) :=
    lt_min hc₁ (lt_min hc₂ (lt_min hc₃ (lt_min hc₄ hc₅)))
  refine ⟨min c₁ (min c₂ (min c₃ (min c₄ c₅))), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5
  have ht1 := st5_t_lt_one sz hflow htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have m : ∀ c', min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c' → STConStInd sz c' s t :=
    fun c' hcc => st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hm1 := m c₁ (min_le_left _ _)
  have hm2 := m c₂ ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 := m c₃ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm4 := m c₄ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hm5 := m c₅ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hHi := st6_hi_of_reg5I sz (by omega) hR
  have hAvgU := st6_expAvgU_of_pin sz hAvg hd hκ hε h𝔡 hflow hs0 hst htT hS2 hLKU
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec0 hExp hm1 hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LW sz hLW hd hκ hε h𝔡 hflow hs0 hst htT hHi hS2 hLmax hLKU hS5
  have hdec := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm2 hS2 hLmax hLKU hS5
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm3 hS2 hLmax hLKU hS5 hAvgU
  have hini := H₄ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm4 hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_pin sz hDu hd hκ hflow hs0 htT
  have hint := H₅ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm5 hS2 hLmax hLKU hS5
    hduh ⟨hlk, hegt⟩ hdec hward
  have hT0 : ∀ n (u : ℝ), u ≤ t n → 0 ≤ STExpTarget sz n u := fun n u hu =>
    st6_target_nonneg sz n (lt_of_le_of_lt hu (ht1 n))
  -- `σ₁ = σ₂`
  have hS : sz.Prec (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hiniS : sz.Prec (U := STIdx2P sz STSigSame s t)
        (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n)
          (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
      simp only [st5_zeroModeSet_empty]
      exact hini.1
    have hmainS := hint.1 (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2) hiniS
    simp only [st5_zeroModeSet_empty] at hmainS
    refine st5_prec_mono sz hsz (c := 2) hmainS (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    linarith
  -- `σ₁ ≠ σ₂`
  obtain ⟨C, c', hC, hc', ϑ, hϑ⟩ := st6_mollifier_family sz hd h𝔡 hflow.1.2.2.2.2
  have hduhQ := st6_duhEqQ_of_pin sz hDuQ hd hκ hflow hs0 htT C c' ϑ hϑ
  have hmainQ := hint.2 C c' ϑ hϑ hduhQ (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2)
    (hini.2 C c' hC hc' ϑ hϑ)
  have hw := (hward C c' ϑ hϑ).1
  have hM : sz.Prec (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hsum := StochDomAt.add (tendsto_size sz hsz) hmainQ hw
    have hsum' : sz.Prec (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
        (fun n p _ => (STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ)) + (sz.Bctl n (p.1 : ℝ)) ^ 3) := by
      refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
      change ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖ ≤
        ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
          ϑ n (p.1 : ℝ) p.2.2‖
      calc ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖
          = ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2 +
            STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
              ϑ n (p.1 : ℝ) p.2.2‖ := by
            unfold STQop; ring_nf
        _ ≤ _ := norm_add_le _ _
    refine st5_prec_mono sz hsz (c := 3) hsum' (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have h2 := st6_cube_le_target sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ) + (sz.Bctl n (p.1 : ℝ)) ^ 3 ≤
      3 * STExpTarget sz n (p.1 : ℝ)
    linarith
  exact st6_cover_exp2U sz (ξ := fun n u σ a => ‖STExpErr sz n (STflowE z n) (u : ℝ) σ a‖)
    (ζ := fun n u _ _ => STExpTarget sz n (u : ℝ)) hsz (P₁ := STSigSame) (P₂ := STSigMixed)
    (fun σ => by by_cases h : σ 0 = σ 1 <;> simp [STSigSame, STSigMixed, h]) hS hM

end RBM.Gauss.Sizes

/-! ## 9. Compiled nonempty instances at `d = 3` (`szB`, `zB`, `(s, t) = (7/8, 15/16)`, regime (i))

Data (merged, `Step34Inst`, `Step5Inst`): `L = 4`, `W_n = n + 4`, `ilambda = 1`, `z = 1/2 + i/64`, `κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`; `1/16 = ilambda²/L² ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`.  Every deterministic hypothesis (flow, times, regime,
`(con_st_ind)`, mollifier family) is discharged; what stays a hypothesis is `STDecay`, `STExp2` at `s ≡ 7/8`
(stochastic premises of other gates) and the other regime-(i) pins of `inst_skeleton6I'`. -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- `stExpIniI'_holds 3` at the data of regime (i): the initial term of regime (i) (primed). -/
theorem inst_expIniI' :
    InstIng6Concl (fun sz E s t => STExpIniIConcl' sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ (stExpIniI'_holds 3) szB_reg5I

/-- The regime-(i) skeleton with the primed initial-term pin, applied at the data of regime (i). -/
theorem inst_skeleton6I' (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3)
    (hDuQ : STExpDuhamelQ 3) (hDec : STExpDriftDecay 3) (hWd : STExpWardI 3) (hInt : STExpIntI 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I (ST_step6_caseI_of_pins' hLK hLW hAvg hDu hDuQ hDec hWd (stExpIniI'_holds 3) hInt)

/-- `expIniI_fastDecay` at `szB`, `zB`, `s ≡ 7/8`: the stochastic premise `STDecay` at `s` stays a hypothesis. -/
theorem inst_expIniI_fastDecay (hDec : STDecay szB (STflowE zB) (fun _ => 7 / 8)) :
    ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKFastDecay (szB.lam n) (7 / 8) ((szB.W n : ℕ) : ℝ) ε' D
        (fun b => STExpErr szB n (STflowE zB n) (7 / 8) σ b) :=
  fun ε' D hε' hD => expIniI_fastDecay (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB zB flow_zB
    (fun _ => 7 / 8) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) hDec ε' D hε' hD

/-- `expIniI_fastDecay_mono` at `d = 3`, `L = 4`, `n = 2`, `g = 1`, `s = 7/8`, `v = 15/16`, `W = 5`, `ε = 1/100`,
`D = 5` for the tensor `A_a = 1_{a₁ = a₂}` (the hypothesis `EKFastDecay` at `s` is proved: a far pair has `a₁ ≠ a₂`). -/
theorem inst_expIniI_fastDecay_mono :
    EKFastDecay (d := 3) (L := 4) (n := 2) 1 (15 / 16) 5 (1 / 100) 5
      (fun a => if a 0 = a 1 then (1 : ℂ) else 0) := by
  have hpos : 0 < (5 : ℝ) ^ (1 / 100 : ℝ) * ellT 4 1 (7 / 8) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (ellT_pos (by norm_num))
  refine expIniI_fastDecay_mono (d := 3) (L := 4) (n := 2) (g := 1) (s := 7 / 8) (v := 15 / 16) (W := 5)
    (ε := 1 / 100) (D := 5) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro a ⟨i, j, hij⟩
  have hne : a 0 ≠ a 1 := by
    intro h
    have hz : a i - a j = 0 := by fin_cases i <;> fin_cases j <;> simp [h]
    rw [hz] at hij
    simp at hij
    linarith
  simp [hne]

/-- `expIniI_same` at `szB`, `zB`, `(7/8, 15/16)`, `𝔠_d = 1/300`. -/
theorem inst_expIniI_same (hDec : STDecay szB (STflowE zB) (fun _ => 7 / 8))
    (hExp : STExp2 szB (STflowE zB) (fun _ => 7 / 8)) :
    Prec szB (U := STIdx2P szB STSigSame (fun _ => 7 / 8) (fun _ => 15 / 16))
      (fun n p _ => ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (7 / 8) (p.1 : ℝ)
        (fun b => STExpErr szB n (STflowE zB n) (7 / 8) p.2.1.1 b) p.2.2‖)
      (fun n p _ => STExpTarget szB n (p.1 : ℝ)) :=
  expIniI_same (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (𝔠d := 1 / 300) (by norm_num) (by norm_num)
    szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5I hDec hExp
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num))

/-- `expIniI_Qop` at `szB`, `zB`, `s ≡ 7/8`, for the mollifier family `st6_mollifier_family` (positive `C`, `c`). -/
theorem inst_expIniI_Qop (hDec : STDecay szB (STflowE zB) (fun _ => 7 / 8))
    (hExp : STExp2 szB (STflowE zB) (fun _ => 7 / 8)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧
      (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
        ‖STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErr szB n (STflowE zB n) (7 / 8) σ b)‖ ≤
          ((szB.size n : ℕ) : ℝ) ^ τ * STExpTarget szB n (7 / 8)) ∧
      (∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
        EKFastDecay (szB.lam n) (7 / 8) ((szB.W n : ℕ) : ℝ) ε' D
          (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErr szB n (STflowE zB n) (7 / 8) σ b))) ∧
      (∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
        EKSumZero (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErr szB n (STflowE zB n) (7 / 8) σ b))) := by
  obtain ⟨C, c, hC, hc, ϑ, hϑ⟩ := st6_mollifier_family szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10)
    flow_zB.1.2.2.2.2
  exact ⟨C, c, hC, hc, ϑ, hϑ, expIniI_Qop (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB zB flow_zB
    (fun _ => 7 / 8) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) hDec hExp C c hC hc ϑ hϑ⟩

/-- `expIniI_mixed` at `szB`, `zB`, `(7/8, 15/16)`, `𝔠_d = 1/300`, for the mollifier family `st6_mollifier_family`. -/
theorem inst_expIniI_mixed (hDec : STDecay szB (STflowE zB) (fun _ => 7 / 8))
    (hExp : STExp2 szB (STflowE zB) (fun _ => 7 / 8)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧
      Prec szB (U := STIdx2P szB STSigMixed (fun _ => 7 / 8) (fun _ => 15 / 16))
        (fun n p _ => ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (7 / 8) (p.1 : ℝ)
          (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErr szB n (STflowE zB n) (7 / 8) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => STExpTarget szB n (p.1 : ℝ)) := by
  obtain ⟨C, c, hC, hc, ϑ, hϑ⟩ := st6_mollifier_family szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10)
    flow_zB.1.2.2.2.2
  exact ⟨C, c, hC, hc, ϑ, hϑ, expIniI_mixed (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (𝔠d := 1 / 300)
    (by norm_num) (by norm_num) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5I hDec hExp
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) C c hC hc ϑ hϑ⟩

/-- `expIniI_props_shift` at `d = 3`, `L = 4`, `g = 1`, `m = 1`, shift `v = 2 e₀`: no hypothesis on `ϑ` beyond
`STMollifierProps … C c`, `c ≥ 0`. -/
theorem inst_expIniI_props_shift :
    ∀ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 4) → ℂ), 0 ≤ c → STMollifierProps (d := 3) 1 C c ϑ →
      STMollifierProps (d := 3) 1 C 0 (fun t a => ϑ t (fun i => if i = 0 then a 0 else a i + Pi.single 0 2)) :=
  fun C c ϑ hc h => expIniI_props_shift (d := 3) (L := 4) (m := 1) 1 C c ϑ (Pi.single 0 2) hc h

/-- `expIniI_props_shift` at a concrete mollifier: the proved `stMollifierEx_holds` gives `C, c > 0` and a family `ϑ`
with `STMollifierProps … C c` at `d = 3`, `L = 4`, `g = 1`; its translate satisfies `STMollifierProps … C 0`
(the premises of the theorem hold, so this is not vacuous). -/
theorem inst_expIniI_props_shift_ex :
    ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 4) → ℂ), 0 < C ∧ 0 < c ∧ STMollifierProps (d := 3) 1 C c ϑ ∧
      STMollifierProps (d := 3) 1 C 0 (fun t a => ϑ t (fun i => if i = 0 then a 0 else a i + Pi.single 0 2)) := by
  obtain ⟨C, c, hC, hc, hex⟩ := stMollifierEx_holds 3 (by norm_num) 1 1 one_pos
  obtain ⟨ϑ, hϑ⟩ := hex 4 (by norm_num) 1 one_pos le_rfl
  exact ⟨C, c, ϑ, hC, hc, hϑ, inst_expIniI_props_shift C c ϑ hc.le hϑ⟩

end RBM.Gauss.Step6Inst
