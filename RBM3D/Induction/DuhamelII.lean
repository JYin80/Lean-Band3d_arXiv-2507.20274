/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.DuhamelI2
import RBM3D.Induction.WardII
import RBM3D.Induction.IniTermII

/-!
# The integrated hierarchy with `Q^{(1)}`, case (ii), over a carrier

Step 5, case (ii) (`ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`), (5.40) `zYU2`: for `σ₁ ≠ σ₂` the
zero-mode removed loop `Q^{(1)} ∘ (𝓛-𝒦)^{(2)}` (`Q^{(1)} = zeroModeSet {0}`), for `σ₁ = σ₂` no
zero-mode removal (`stDuhamelConclgL_engine`, `hTTT` through `Or.inr`), over a carrier family: the
statement `stDuhamelIIgL_of` (`STDuhamelIIgL`, `Chain/Step5Gen.lean`) with the engine of the mixed
conjunct `stDuhamelConclgL_engineQ1` (any sign class `P`; `Q = {0}`); `stDuhamelII_holds : ∀ d,
STDuhamelII d` for the band matrix model is a corollary through `STDuhamelII_iff_gL`.

The proof differs from the paper's: instead of the `Θ̊` kernel estimates (5.38) `ThetaBcirc_infint`
and (5.39) `uwp2-92kj00`, `Q^{(1)}` is applied to the pathwise remainder
`R = (𝓛-𝒦)_{tt} - 𝒰_{s,tt} (𝓛-𝒦)_s` of the grid Duhamel form.  `R` is bounded at every label by
the drift and martingale terms of `Induction/DuhamelI2` (`duhamelIG_path_rem`: the pathwise bound
without the initial term), `Q^{(1)} 𝒰 (𝓛-𝒦)_s` is the hypothesis, and `‖Q^{(1)} R_a‖ ≤ ‖R_a‖ +
L^{-d} Σ_c ‖R_{(c,a₂)}‖`, the average of the profile being bounded by the zero mode of `𝒯_t` in
the regime `1-t ≤ ilambda²/L²` (`duhamelII_prof_avg`).  The private helpers of `DuhamelI`,
`DuhamelI2` are reached with `open private` instead of being copied.

Sections: 1 `Q^{(1)}` on the first index; 2 the average of the profile; 3 Hölder continuity of
`Q^{(1)}(𝓛-𝒦)_u`; 4 the per-section statement; 5 the engine, `stDuhamelIIgL_of` and the band
corollaries.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open private duhamelI_tailW_eq duhamelI_cardK duhamelI_measure_le from RBM3D.Induction.DuhamelI
open private duhamelI_absorb duhamelIG_prec_congr duhamelIG_whp_sec duhamelIG_ELKLK_meas duhamelIG_ELKLK_eq duhamelIG_pair duhamelIG_theta_rows
  from RBM3D.Induction.DuhamelI2
open private emn2Exp2_exists_CR from RBM3D.Induction.EMn2Exp2
open private lemDecCalELipG_Ks from RBM3D.Induction.EtermsMid2
open private lemDecCalELipG_absorb from RBM3D.Induction.LemDecCalELip

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.BA

/-! ## 1. `Q^{(1)}` on the first index -/

section Zero

variable {d L : ℕ} [NeZero L]

/-- `Q^{(1)} = zeroModeSet {0}` removes the average over the first index. -/
private theorem duhamelII_Q_apply (T : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    zeroModeSet d L {0} T a = T a - ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, T (Function.update a 0 c) := by
  simp [zeroModeSet, Finset.toList_singleton, zeroModeOp, avgOp]

/-- `‖Q^{(1)}X_a - Q^{(1)}I_a‖ ≤ ‖X_a - I_a‖ + L^{-d} Σ_c ‖X_{(c,a₂)} - I_{(c,a₂)}‖`. -/
private theorem duhamelII_Q_sub_le (X I : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    ‖zeroModeSet d L {0} X a - zeroModeSet d L {0} I a‖ ≤
      ‖X a - I a‖ + ((L : ℝ) ^ d)⁻¹ *
        ∑ c : Zd d L, ‖X (Function.update a 0 c) - I (Function.update a 0 c)‖ := by
  rw [duhamelII_Q_apply, duhamelII_Q_apply]
  have e : (X a - ((L : ℂ) ^ d)⁻¹ * ∑ c, X (Function.update a 0 c)) -
      (I a - ((L : ℂ) ^ d)⁻¹ * ∑ c, I (Function.update a 0 c)) =
      (X a - I a) - ((L : ℂ) ^ d)⁻¹ * ∑ c, (X (Function.update a 0 c) - I (Function.update a 0 c)) := by
    simp only [Finset.sum_sub_distrib]; ring
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_mul]
  have hinv : ‖((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by simp
  rw [hinv]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

omit [NeZero L] in
/-- `(update a 0 c) 0 = c`, `(update a 0 c) 1 = a 1`. -/
private theorem duhamelII_update_apply (a : Fin 2 → Zd d L) (c : Zd d L) :
    (Function.update a 0 c) 0 = c ∧ (Function.update a 0 c) 1 = a 1 :=
  ⟨Function.update_self .., Function.update_of_ne (by decide) _ _⟩

end Zero


section ZeroMeas

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ}

/-- `Q^{(1)} ∘ 𝒰_{v,w} (𝓛-𝒦)_u` is a measurable function of the matrix (`Step2EventsGen_Grid`). -/
private theorem duhamelIIG_QUgen_meas (hG : Step2EventsGen_Grid Cm μ) (n : ℕ) (u v w : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖zeroModeSet d (sz.L n) {0} (Step2Gen_UN Cm.toFlowFM n σ v w (fun b => STLKMg Cm n u H σ b)) a‖ := by
  have hU : ∀ b, Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Step2Gen_UN Cm.toFlowFM n σ v w (fun b' => STLKMg Cm n u H σ b') b := fun b => by
    unfold Step2Gen_UN
    exact Finset.measurable_sum _ fun b' _ => measurable_const.mul (Step2EventsGen_STLKMg_measurable hG n u σ b')
  simp only [duhamelII_Q_apply]
  exact ((hU a).sub (measurable_const.mul (Finset.measurable_sum _ fun c _ => hU _))).norm

/-- `Q^{(1)}(𝓛-𝒦)_u` is a measurable function of the matrix (`Step2EventsGen_Grid`). -/
private theorem duhamelIIG_QLK_meas (hG : Step2EventsGen_Grid Cm μ) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖zeroModeSet d (sz.L n) {0} (fun a' => STLKMg Cm n u H σ a') a‖ := by
  simp only [duhamelII_Q_apply]
  exact ((Step2EventsGen_STLKMg_measurable hG n u σ a).sub (measurable_const.mul
    (Finset.measurable_sum _ fun c _ => Step2EventsGen_STLKMg_measurable hG n u σ _))).norm

end ZeroMeas

/-! ## 2. The profile averaged over the first index (the zero mode of `𝒯_t`, `1-t ≤ ilambda²/L²`) -/

section Averaging

variable {d : ℕ}

/-- **The average of the profile**: for `1 - u ≤ ilambda²/L²` the profile `P_u(x,y) = W^{-d} max(𝒯_u(|x-y|_∞), W^{-D})`
has `L^{-d} Σ_c P_u(c,y) ≤ C P_u(x,y)` for all `x, y`, `C = 3 C_rad + 1` depending on `d` only: the radial sum
`Σ_c 𝒯_u(|c-y|_∞) ≤ C_rad/(1-u)` (`emn2Exp2_exists_CR`) against the zero mode of `𝒯_u` (`ℓ_u = L`, so
`exp(-√(r/ℓ_u)) ≥ e⁻¹` for `r ≤ L`, and `B_{u,r} ≥ (L^d(1-u))⁻¹`). -/
private theorem duhamelII_prof_avg (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D u : ℝ), 0 ≤ sz.lam n → u < 1 →
      1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 → ∀ x y : Zd d (sz.L n),
        (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) c y ≤
          C * STprof sz n u D ((sz.L n : ℕ) : ℝ) x y := by
  obtain ⟨CR, hCR, hsum⟩ := emn2Exp2_exists_CR d hd
  refine ⟨3 * CR + 1, by positivity, ?_⟩
  intro sz n D u hg hu1 hreg x y
  have hL3 := sz.three_le_L n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by linarith
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have h1u : 0 < 1 - u := by linarith
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  set Wm := ((sz.W n : ℕ) : ℝ) ^ (-D) with hWm
  have hWd0 : 0 ≤ Wd := by positivity
  have hWm0 : 0 ≤ Wm := Real.rpow_nonneg hW.le _
  have hprof : ∀ a b : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) a b =
      Wd * max (tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b) : ℕ)) Wm := fun a b => by
    unfold STprof; rw [duhamelI_tailW_eq]
  have hT0 : ∀ a b : Zd d (sz.L n), 0 ≤ tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b) : ℕ) :=
    fun a b => tailT_nonneg (Nat.cast_nonneg _)
  -- the sum of the profile
  have hup : ∑ c : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) c y ≤
      Wd * (CR / (1 - u) + ((sz.L n : ℕ) : ℝ) ^ d * Wm) := by
    calc ∑ c : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) c y
        = ∑ c : Zd d (sz.L n), Wd * max (tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - y) : ℕ)) Wm :=
          Finset.sum_congr rfl fun c _ => hprof c y
      _ ≤ ∑ c : Zd d (sz.L n), Wd * (tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - y) : ℕ) + Wm) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
            (max_le (le_add_of_nonneg_right hWm0) (le_add_of_nonneg_left (hT0 c y))) hWd0
      _ = Wd * (∑ c : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - y) : ℕ) +
            ((sz.L n : ℕ) : ℝ) ^ d * Wm) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            card_Zd]
          push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hsum (sz.L n) (sz.lam n) u hg hu1 y) le_rfl) hWd0
  -- the zero mode of the profile at `(x, y)`
  have hrL : ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have : zdistInf d (sz.L n) (x - y) ≤ sz.L n := Finset.sup_le fun i _ => zdist_le_L _
    exact_mod_cast this
  have hlow : Real.exp (-1) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤
      tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) := by
    unfold tailT BparamR
    have hexp := exp_tail_ge hg hu1 hL1 hreg hrL
    have hB : (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ≤
        (sz.lam n ^ 2 + |1 - u|)⁻¹ * ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by
      have : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ * ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
        mul_nonneg (inv_nonneg.2 (by positivity)) (inv_nonneg.2 (by positivity))
      linarith
    rw [abs_of_pos h1u] at hB ⊢
    calc Real.exp (-1) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ =
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * Real.exp (-1) := mul_comm _ _
      _ ≤ _ := mul_le_mul hB hexp (Real.exp_pos _).le (by
          have : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
            mul_nonneg (inv_nonneg.2 (by positivity)) (inv_nonneg.2 (by positivity))
          have : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := inv_nonneg.2 (by positivity)
          positivity)
  have he3 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have hZ : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ 3 * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) := by
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ = Real.exp 1 * (Real.exp (-1) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [h1]
    calc Real.exp 1 * (Real.exp (-1) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
        ≤ Real.exp 1 * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) :=
          mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
      _ ≤ 3 * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) :=
          mul_le_mul_of_nonneg_right he3 (hT0 x y)
  -- conclusion
  set Tx := tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) with hTx
  have hTx0 : 0 ≤ Tx := hT0 x y
  rw [hprof x y]
  have e1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (Wd * (CR / (1 - u) + ((sz.L n : ℕ) : ℝ) ^ d * Wm)) =
      Wd * (CR * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ + Wm) := by
    rw [mul_inv]; field_simp
  calc (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) c y
      ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (Wd * (CR / (1 - u) + ((sz.L n : ℕ) : ℝ) ^ d * Wm)) :=
        mul_le_mul_of_nonneg_left hup (inv_nonneg.2 hLd.le)
    _ = Wd * (CR * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ + Wm) := e1
    _ ≤ Wd * (CR * (3 * Tx) + Wm) := by gcongr
    _ ≤ (3 * CR + 1) * (Wd * max Tx Wm) := by
        have h1 : Tx ≤ max Tx Wm := le_max_left _ _
        have h2 : Wm ≤ max Tx Wm := le_max_right _ _
        have h3 : 0 ≤ max Tx Wm := le_trans hTx0 h1
        nlinarith [mul_le_mul_of_nonneg_left h1 hWd0, mul_le_mul_of_nonneg_left h2 hWd0,
          mul_nonneg hWd0 (sub_nonneg.2 h1), mul_nonneg hCR.le (mul_nonneg hWd0 (sub_nonneg.2 h1))]

end Averaging

/-! ## 3. Hölder continuity of `Q^{(1)}(𝓛-𝒦)_u` in `u` over a carrier -/

section Holder

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ}
  {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {G : ℕ → Set sz.SeqΩ} {c : ℝ} {s t : ℕ → ℝ}

/-- `u ↦ ‖Q^{(1)}(𝓛-𝒦)^{(2)}_{u,σ,a}‖` is Hölder-1/2 on `G`, constant `N^{11+c}`: `LemDecCalELip_LK_subg` (the norm of the difference of the
loops, not the difference of the norms) at the labels `a` and `(c', a₂)`, and `‖Q X‖ ≤ ‖X_a‖ + L^{-d} Σ_{c'} ‖X_{(c',a₂)}‖`. -/
theorem duhamelIIG_holder (hL : StepDecompGen_LoopForm Cm E)
    (hLM : ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω)
    (hc : 0 ≤ c) (hmod : LemDecCalELipG_Mod Hm G c) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n < 1)
    (hsize : sz.SizeTendsto) (hQ : ∀ᶠ n in atTop, (Cm.eta n (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2)
    (hKs : ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖Cm.K n u σ a - Cm.K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ G n, ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      |‖zeroModeSet d (sz.L n) {0} (fun a' => Cm.L n (u : ℝ) σ a' ω - Cm.K n (u : ℝ) σ a') a‖ -
          ‖zeroModeSet d (sz.L n) {0} (fun a' => Cm.L n (u' : ℝ) σ a' ω - Cm.K n (u' : ℝ) σ a') a‖| ≤
        ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := by
  refine ⟨((10 + 1 : ℕ) : ℝ) + c, by positivity, ?_⟩
  filter_upwards [lemDecCalELipG_loops hL hLM hc hmod hm ht hQ, hKs, hsize.eventually_ge_atTop 14] with n hn0 hK h14 ω hω u u' σ a
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hb : ∀ b : Fin 2 → Zd d (sz.L n), ‖(Cm.L n (u : ℝ) σ b ω - Cm.K n (u : ℝ) σ b) - (Cm.L n (u' : ℝ) σ b ω - Cm.K n (u' : ℝ) σ b)‖ ≤
      7 * ((sz.size n : ℕ) : ℝ) ^ 10 * ((sz.size n : ℕ) : ℝ) ^ c * Real.sqrt |(u : ℝ) - (u' : ℝ)| := fun b =>
    LemDecCalELip_LK_subg Cm.toFlowFM n ω hN1 (Real.one_le_rpow hN1 hc)
      (fun σ a => (hn0 ω hω).1 u u' ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1) u'.2.2 σ a)
      (fun σ a => lemDecCalELipG_Ks ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1) u'.2.2 (ht n) hK σ a) σ b
  have h14' : (14 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast h14
  refine (abs_norm_sub_norm_le _ _).trans ((duhamelII_Q_sub_le _ _ a).trans ?_)
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have := sz.three_le_L n
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  set x : ℝ := Real.sqrt |(u : ℝ) - (u' : ℝ)| with hx
  set Bd : ℝ := 7 * ((sz.size n : ℕ) : ℝ) ^ 10 * ((sz.size n : ℕ) : ℝ) ^ c * x with hBd
  have hsum : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c' : Zd d (sz.L n),
      ‖(Cm.L n (u : ℝ) σ (Function.update a 0 c') ω - Cm.K n (u : ℝ) σ (Function.update a 0 c')) -
        (Cm.L n (u' : ℝ) σ (Function.update a 0 c') ω - Cm.K n (u' : ℝ) σ (Function.update a 0 c'))‖ ≤ Bd := by
    calc _ ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ _c' : Zd d (sz.L n), Bd :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c' _ => hb _) (inv_nonneg.2 hL0.le)
      _ = Bd := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Zd]
          push_cast
          field_simp
  have h2 : 2 * Bd ≤ ((sz.size n : ℕ) : ℝ) ^ (((10 + 1 : ℕ) : ℝ) + c) * x := by
    have := lemDecCalELipG_absorb (e := 10) (k := 14) (c := c) (x := x) h14' hN1 (Real.sqrt_nonneg _)
    calc 2 * Bd = 14 * ((sz.size n : ℕ) : ℝ) ^ 10 * ((sz.size n : ℕ) : ℝ) ^ c * x := by rw [hBd]; ring
      _ ≤ _ := this
  calc _ ≤ Bd + Bd := add_le_add (hb a) hsum
    _ = 2 * Bd := by ring
    _ ≤ _ := h2

end Holder

/-! ## 4. The per-section statement with `Q^{(1)}` -/

/-- `1 - s ≤ ilambda²/L²` gives `1 - s ≤ ilambda²` (`L ≥ 1`). -/
private theorem duhamelII_mid (sz : Sizes d) (n : ℕ) {s : ℝ} (h : 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) :
    1 - s ≤ sz.lam n ^ 2 := by
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  exact h.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hL))

/-- The chain `‖Q X‖ ≤ ‖Q I‖ + ‖Q X - Q I‖`, `‖Q X - Q I‖ ≤ R₀ + R_s` and the bounds of the three terms (plain arithmetic, a small context). -/
private theorem duhamelII_chain {QX QI QD R0 Rs Λ F Bk CA P Wm : ℝ} (hins : QX ≤ QI + QD) (hQ : QD ≤ R0 + Rs)
    (hI : QI ≤ Λ * F) (hR0 : R0 ≤ Bk * P + Wm) (hsum : Rs ≤ Bk * (CA * P) + Wm) :
    QX ≤ Λ * F + (Bk * P + Bk * (CA * P)) + 2 * Wm := by
  linarith

/-- The exponent closure with the doubled floor (`duhamelI_absorb` at `W_m = 2 W^{-D}`):
`Y ≤ Λ F + Λ² κ ρ³ A^{-1/4} P + 2 W^{-D}` gives `Y ≤ N^τ (F + A^{-1/5} P + W^{-D})` if `2 (2κ+1) Λ² ≤ N^τ`. -/
private theorem duhamelII_close {Λ κ F P Wm A ρ Nτ Y : ℝ} (hΛ : 1 ≤ Λ) (hκ : 0 ≤ κ) (hF : 0 ≤ F) (hP : 0 ≤ P)
    (hWm : 0 ≤ Wm) (hA : 1 ≤ A) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ (2 * A) ^ (1 / 100 : ℝ))
    (hN : 2 * ((2 * κ + 1) * Λ ^ 2) ≤ Nτ) (hY : Y ≤ Λ * F + Λ ^ 2 * κ * (ρ ^ 3 * A ^ (-(1 / 4) : ℝ)) * P + 2 * Wm) :
    Y ≤ Nτ * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) := by
  have habs := duhamelI_absorb (Λ := Λ) (κ := κ) (F := F) (P := P) (Wm := 2 * Wm) (A := A) (ρ := ρ)
    (Nτ := (2 * κ + 1) * Λ ^ 2) hΛ hκ hF hP (by linarith) hA hρ1 hρ le_rfl
  have hA5 : 0 ≤ A ^ (-(1 / 5) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hX0 : 0 ≤ F + A ^ (-(1 / 5) : ℝ) * P := add_nonneg hF (mul_nonneg hA5 hP)
  have hc : 0 ≤ (2 * κ + 1) * Λ ^ 2 := by positivity
  have h2c : (2 * κ + 1) * Λ ^ 2 * (F + A ^ (-(1 / 5) : ℝ) * P + 2 * Wm) ≤
      2 * ((2 * κ + 1) * Λ ^ 2) * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) := by
    nlinarith [mul_nonneg hc hX0, mul_nonneg hc hWm]
  have h3c : 2 * ((2 * κ + 1) * Λ ^ 2) * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) ≤ Nτ * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) :=
    mul_le_mul_of_nonneg_right hN (by linarith)
  linarith

section SectionMainII

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
-- the six grid events and the pathwise case analysis elaborate a long `have` list: 200000 is not enough
/-- **The per-section statement with `Q^{(1)}` over a carrier**: at a section `tt n ∈ [s_n, t_n]` the family
`‖Q^{(1)}(𝓛-𝒦)^{(2)}_{tt,σ,a}‖` is dominated by `F + A^{-1/5} W^{-d}𝒯̃^L_{tt,D} + W^{-D}` at the law `law sz`, given `‖Q^{(1)} 𝒰_{s,tt}(𝓛-𝒦)_s‖ ≺ F`,
`STEtermsMidConclgL` and (2.83) `con_st_ind`, in the regime `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`.  The grid and the six events are those of `duhamelIG_section`
(the events at the grid times are over all labels); the initial-term event is the `Q^{(1)}`-form, and at the end `Q^{(1)}` is applied to the remainder
at the labels `(σ, (c, a₂))`, `c ∈ Z_L^d` (`duhamelIG_path_rem`, `duhamelII_prof_avg`). -/
private theorem duhamelIIG_section (hd : 3 ≤ d) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hGMA : STGridMartAtgL d C₀ Flow mkM T0)
    {κ ε 𝔡 𝔠 c₀ : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) {z : ℕ → ℂ} (hflow : Flow sz κ ε 𝔠 𝔡 z)
    (hAd : sz.Admissible 𝔠 𝔡) (hc₀ : 0 < c₀) (hIm : ∀ n, c₀ ≤ ((mkM sz z).m n).im)
    (hη : ∀ n u, (mkM sz z).eta n u = (1 - u) * ((mkM sz z).m n).im)
    {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm (mkM sz z) E) (hGrid : Step2EventsGen_Grid (mkM sz z) (law sz))
    (hHerm : ∀ s t K n k ω, ((mkM sz z).Hpath s t K n k ω).IsHermitian)
    (hker : ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hpair : ∀ (n : ℕ) (σ : Fin 2 → Bool) (w : ℝ), 0 < w → w < 1 →
      Step2Gen_thetaKer (mkM sz z).toFlowFM n (σ 1) (σ 0) w = Step2Gen_thetaKer (mkM sz z).toFlowFM n (σ 0) (σ 1) w)
    {C : ℝ} (hC : 0 < C)
    (hΦC : ∀ (n : ℕ) (σ σ' : Bool) (D v w : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → 0 ≤ v → v ≤ w → w < 1 →
      (∀ x, ∑ y, ‖Step2Gen_thetaKer (mkM sz z).toFlowFM n σ σ' w x y‖ ≤ (1 - w)⁻¹) →
      (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - w ∨ 1 - v ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
      ∀ a : Fin 2 → Zd d (sz.L n),
        duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer (mkM sz z).toFlowFM n σ σ' w x y‖) (2 * (1 - v))
            (fun x y => STprof sz n v D ((sz.L n : ℕ) : ℝ) x y) a ≤
          C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
              (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D))))
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htz : ∀ n, t n ≤ T0 sz z n) (ht1 : ∀ n, t n < 1)
    (hKn : ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ t n → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖(mkM sz z).K n v σ a‖ ≤ ((sz.size n : ℕ) : ℝ))
    (hReg : STReg5II sz s t)
    (hCon : STConStInd sz (1 / 100) s t) (hE : STEtermsMidConclgL (mkM sz z).toFlowFM (law sz) s t)
    {D : ℝ} (hD : 0 < D) (P : (Fin 2 → Bool) → Prop) (F : ∀ n, STIdx2P sz P s t n → ℝ)
    (hF0 : ∀ n p, 0 ≤ F n p)
    (hini : PrecL sz (law sz) (U := STIdx2P sz P s t) (fun n p ω => ‖zeroModeSet d (sz.L n) {0} (Step2Gen_UN (mkM sz z).toFlowFM n p.2.1.1 (s n) (p.1 : ℝ)
      (fun b => (mkM sz z).L n (s n) p.2.1.1 b ω - (mkM sz z).K n (s n) p.2.1.1 b)) p.2.2‖) (fun n p _ => F n p))
    (tt : ∀ n, TimeIcc s t n) :
    PrecL sz (law sz) (U := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖zeroModeSet d (sz.L n) {0}
        (fun a' => (mkM sz z).L n (tt n : ℝ) v.1.1 a' ω - (mkM sz z).K n (tt n : ℝ) v.1.1 a') v.2‖)
      (fun n v _ => F n (tt n, v) + STAI sz n ^ (-(1 / 5) : ℝ) *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  classical
  set Cm : Step2Mat sz := mkM sz z with hCm
  by_cases hP : ∃ σ, P σ
  swap
  · exact Step2EventsGen_prec_of_le_ev (law sz) (fun n v ω => by
      exact absurd ⟨v.1.1, v.1.2⟩ hP) (Eventually.of_forall fun n v ω => absurd ⟨v.1.1, v.1.2⟩ hP)
  have : ∀ n, Nonempty ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) :=
    fun n => ⟨(⟨hP.choose, hP.choose_spec⟩, fun _ => 0)⟩
  have hsN := tendsto_size sz hAd.2.2.1
  obtain ⟨Hm', hGMM', hLM', hMeasLM, hMeasGMM, hlaw⟩ := hGrid
  have hGrid' : Step2EventsGen_Grid Cm (law sz) := ⟨Hm', hGMM', hLM', hMeasLM, hMeasGMM, hlaw⟩
  intro τ hτ D' hD'
  obtain ⟨CA, hCA, hAvg⟩ := duhamelII_prof_avg hd
  have hmid : ∀ n, 1 - s n ≤ sz.lam n ^ 2 := fun n => duhamelII_mid sz n (hReg n).2
  set κs : ℝ := 4 * C / c₀ + 8 * C * (2 / c₀ + 1) with hκs
  set κq : ℝ := κs * (1 + CA) with hκq
  have hκs0 : 0 ≤ κs := by rw [hκs]; positivity
  have hκq0 : 0 ≤ κq := by rw [hκq]; positivity
  set DE : ℝ := D + d + 2 with hDE
  set Dm : ℝ := 2 * (D + D' + 6 + τ) with hDm
  obtain ⟨CK, hCK0, hK⟩ := hGMA κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s (fun n => (tt n : ℝ)) hs (fun n => (tt n).2.1)
    (fun n => (tt n).2.2.trans (htz n)) Dm (by positivity)
  set x₀ : ℝ := max CK (2 * (C₀ + D + 12)) with hx₀
  set m : ℕ := ⌈x₀⌉₊ with hm
  set K : ℕ → ℕ := fun n => (sz.size n) ^ m with hKdef
  have hKne : ∀ n, K n ≠ 0 := fun n => pow_ne_zero _ (by have := sz.one_le_size n; omega)
  have hKbig : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    have h1 : CK ≤ (m : ℝ) := (le_max_left _ _).trans (Nat.le_ceil x₀)
    calc ((sz.size n : ℕ) : ℝ) ^ CK ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 h1
      _ = K n := by rw [Real.rpow_natCast]; simp [hKdef]
  obtain ⟨Mart, Rem, hid, hrem, hmart⟩ := hK K hKne hKbig
  set τ₁ : ℝ := τ / 4 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨hE1, hE2, hE3⟩ := hE DE (by positivity)
  -- card bounds
  have hcardV : ∀ᶠ n in atTop, (Fintype.card ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    exact duhamelI_card_le sz P n hn
  have hcardK : ∀ (c : ℕ → ℕ), (∀ᶠ n in atTop, (c n : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ)) →
      ∀ᶠ n in atTop, (((K n + 1) * c n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (((m + 5 : ℕ) : ℝ)) := fun c hc => by
    filter_upwards [hc, hsN.eventually (eventually_ge_atTop 4)] with n h1 h2
    exact duhamelI_cardK (sz.size n) m (c n) h2 h1
  -- the initial term at the grid index `0`
  have hΞ1 := Step2EventsGen_grid_whp_zero Cm (law sz) hlaw (V := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) s
    (fun n => (tt n : ℝ)) K hs (fun n => (tt n).2.1) hKne (C := 3) (by norm_num) hcardV
    (fun n v u H => ‖zeroModeSet d (sz.L n) {0} (Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ) (fun b => STLKMg Cm n u H v.1.1 b)) v.2‖)
    (fun n v u H => F n (tt n, v))
    (fun n v u => duhamelIIG_QUgen_meas hGrid' n u _ _ _ v.2) (fun n v u => measurable_const) τ₁ hτ₁0
    (duhamelIG_prec_congr (fun n v ω => by
        simp only [Step2EventsGen_STLKMg_eq Cm hLM']) (fun n v ω => rfl)
      (StochDomAt.precomp_param hini (fun n v => (tt n, v))))
  -- the three error terms at every grid index
  have hcardL : ∀ᶠ n in atTop, (Fintype.card (sz.STLab n) : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    have := ST_card_lab_le sz n hn
    have h0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hcardL2 : ∀ᶠ n in atTop, (Fintype.card (sz.STLab n × Fin 2) : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    have := ST_card_lab_le sz n hn
    rw [Fintype.card_prod, Fintype.card_fin]; push_cast
    linarith
  have hΞ2 := duhamelIG_whp_sec (V := fun n => sz.STLab n) hlaw tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL)
    (fun n v u H => ‖STELKLKMg Cm n u H v.1 v.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 3) : ℝ) * (Cm.eta n u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1))
    (fun n v u => (duhamelIG_ELKLK_meas hGrid' n u v.1 v.2).norm) (fun n v u => measurable_const) hτ₁0
    (duhamelIG_prec_congr (fun n p ω => by
        simp only [duhamelIG_ELKLK_eq Cm hLM']) (fun n p ω => rfl) hE1)
  have hΞ3 := duhamelIG_whp_sec (V := fun n => sz.STLab n) hlaw tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL)
    (fun n v u H => ‖STEGtMg Cm n u H v.1 v.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1))
    (fun n v u => (Step2EventsGen_STEGtMg_measurable hGrid' n u v.1 v.2).norm) (fun n v u => measurable_const) hτ₁0
    (duhamelIG_prec_congr (fun n p ω => by
        simp only [Step2EventsGen_STEGtMg_eq Cm hLM']) (fun n p ω => rfl) hE2)
  have hΞ4 := duhamelIG_whp_sec (V := fun n => sz.STLab n × Fin 2) hlaw tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL2)
    (fun n v u H => ‖STEEkMg Cm n u H v.2 v.1.1 v.1.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.1.2 0) (v.1.2 1) ^ 2)
    (fun n v u => (Step2EventsGen_STEEkMg_measurable hGrid' n u v.2 v.1.1 v.1.2).norm) (fun n v u => measurable_const) hτ₁0
    (duhamelIG_prec_congr (fun n p ω => by
        simp only [Step2EventsGen_STEEkMg_eq Cm hLM']) (fun n p ω => rfl)
      (StochDomAt.precomp_param hE3 (fun n (p : TimeIcc s t n × (sz.STLab n × Fin 2)) =>
        (((p.1, p.2.1), p.2.2) : STIdx2 sz s t n × Fin 2))))
  have hΞ := hΞ1.inter hsN (hΞ2.inter hsN (hΞ3.inter hsN hΞ4))
  -- the martingale tails of all labels
  have hmartE : ∀ᶠ n in atTop, Cm.Pp (⋃ i : sz.STLab n, {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ τ₁ * (∑ j ∈ Finset.range k, gridStep s (fun m => (tt m : ℝ)) K n *
        ‖STEEMg Cm n (gridTime s (fun m => (tt m : ℝ)) K n j)
          (Cm.Hpath s (fun m => (tt m : ℝ)) K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) <
        ‖Mart n i k ω‖}) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) := by
    filter_upwards [hmart τ₁ hτ₁0, hsN.eventually (eventually_ge_atTop 4)] with n hn h4
    exact ST_union_prob Cm.Pp _ (by exact_mod_cast (by omega : 1 ≤ sz.size n)) (ST_card_lab_le sz n h4)
      (by rw [hDm]; nlinarith) hn
  -- the almost sure identities
  have hae : ∀ᶠ n in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ i : sz.STLab n,
      (∀ k, k ≤ K n → STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 k ω =
        STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 0 ω +
          ((gridStep s (fun m => (tt m : ℝ)) K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDriftg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 j ω + Rem n i k ω + Mart n i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n)) := by
    filter_upwards [hrem] with n hn
    exact ae_all_iff.2 fun i => (hid n i).and (hn i)
  -- numerical facts
  have hWO := hAd.2.2.2.2
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hWbig : ∀ᶠ n in atTop, 2 * 𝔡⁻¹ ^ 2 ≤ ((sz.W n : ℕ) : ℝ) := by
    filter_upwards [hAd.2.2.2.1, hsN.eventually (eventually_le_rpow (2 * 𝔡⁻¹ ^ 2) hAd.1)] with n h1 h2
    exact h2.trans h1
  have hNc : ∀ᶠ n in atTop, c₀⁻¹ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := hAd.2.2.1.eventually (eventually_ge_atTop _)
  have hNτ : ∀ᶠ n in atTop, 2 * (2 * κq + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    hsN.eventually (eventually_le_rpow _ (half_pos hτ))
  have hiniE := StochDomAt.precomp_param hini (fun n v => (tt n, v))
  filter_upwards [hiniE τ hτ D' hD', hev, hWO, hWbig, hNc, hNτ, hCon, hmartE, hae, hΞ (D' + 1) (by linarith),
    hsN.eventually (eventually_ge_atTop 256), hKn] with n hini1 hAn hWOn hWb hNcn hNτn hCon1 hmartn haen hΞn h256 hKnn
  obtain ⟨hlam, hA1⟩ := hAn
  have hlamle : sz.lam n ≤ 𝔡⁻¹ := hWOn.2
  have htt1 : (tt n : ℝ) < 1 := (tt n).2.2.trans_lt (ht1 n)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN256 : (256 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast h256
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hΛ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1 hτ₁0.le
  by_cases hsn : s n < (tt n : ℝ)
  swap
  · -- the section is the initial time: `𝒰_{s,s} = 1`
    have hts : (tt n : ℝ) = s n := le_antisymm (not_lt.1 hsn) (tt n).2.1
    refine le_trans (measure_mono ?_) hini1
    rintro ω ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have hs1 : s n < 1 := (hst n).trans (ht1 n)
    have hU := Step2Gen_UN_self Cm.toFlowFM n (hker n).1 v.1.1 (hs n) hs1
      (fun b => Cm.L n (s n) v.1.1 b ω - Cm.K n (s n) v.1.1 b)
    have hF1 : 0 ≤ STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) := add_nonneg (mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) _)
          (ST_STprof_pos sz n _ _ _ _ _).le) (Real.rpow_nonneg hW0.le _)
    simp only [hts] at hv hF1 ⊢
    change _ < ‖zeroModeSet d (sz.L n) {0} (Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (s n) (fun b => Cm.L n (s n) v.1.1 b ω - Cm.K n (s n) v.1.1 b)) v.2‖
    rw [hU]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)) hv
    linarith [hF0 n (tt n, v)]
  -- the main case: `s n < tt n`
  have hs1 : s n < 1 := (hst n).trans (ht1 n)
  have h1tt : 0 < 1 - (tt n : ℝ) := by linarith
  have htN : (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := duhamelI_htN sz n hlam hA1 (hReg n).1
  have hTi : (1 - (tt n : ℝ))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) :=
    (inv_anti₀ (by linarith [ht1 n]) (by linarith [(tt n).2.2])).trans htN
  have hρA := duhamelI_rho sz n hlam (tt n).2.1 (tt n).2.2 (ht1 n) (by linarith [hmid n, (hst n)]) hCon1.1
  set ρ : ℝ := (1 - s n) / (1 - (tt n : ℝ)) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1tt]; linarith
  have hρN : ρ ≤ ((sz.size n : ℕ) : ℝ) :=
    ((div_le_div_of_nonneg_right (by linarith [hs n]) h1tt.le).trans_eq (one_div _)).trans hTi
  have hx₀m : x₀ ≤ (m : ℝ) := Nat.le_ceil x₀
  have hKx : ((sz.size n : ℕ) : ℝ) ^ x₀ ≤ K n := by
    calc ((sz.size n : ℕ) : ℝ) ^ x₀ ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hx₀m
      _ = K n := by rw [Real.rpow_natCast]; simp [hKdef]
  have hΔ : gridStep s (fun m => (tt m : ℝ)) K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-x₀) := by
    have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero (hKne n)
    have hNx : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ x₀ := Real.rpow_pos_of_pos (by linarith) _
    unfold gridStep
    calc ((tt n : ℝ) - s n) / K n ≤ 1 / K n := div_le_div_of_nonneg_right (by linarith [(tt n).2.2, ht1 n, hs n]) hKpos.le
      _ ≤ 1 / ((sz.size n : ℕ) : ℝ) ^ x₀ := one_div_le_one_div_of_le hNx hKx
      _ = _ := by rw [Real.rpow_neg (by linarith), one_div]
  have hWN := duhamelI_W_le_size sz (by omega : d ≠ 0) n
  have hWm : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_nonpos hW0 hWN (neg_nonpos.2 hD.le)
  have hfloor := duhamelI_floor (Δ := gridStep s (fun m => (tt m : ℝ)) K n) (Wm := ((sz.W n : ℕ) : ℝ) ^ (-D))
    (C₀ := C₀) (c₀ := c₀) (D := D) (τ := τ) (Dm := Dm) (x := x₀) (ρ := ρ) (Ti := (1 - (tt n : ℝ))⁻¹) hN256 hNcn hτ hD hC₀
    (by linarith) hρN (inv_nonneg.2 h1tt.le) hTi (div_nonneg (by linarith [(tt n).2.1]) (by exact_mod_cast Nat.zero_le _)) hΔ hWm
    (by rw [hDm]; linarith) (le_max_right _ _)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hDEn : ρ * ((sz.W n : ℕ) : ℝ) ^ (-DE) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have h2A : (1 : ℝ) ≤ 2 * STAI sz n := by linarith
    have hρ2 : ρ ≤ 2 * STAI sz n := hρA.trans (by
      calc (2 * STAI sz n) ^ (1 / 100 : ℝ) ≤ (2 * STAI sz n) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h2A (by norm_num)
        _ = 2 * STAI sz n := Real.rpow_one _)
    have hA2 : 2 * STAI sz n ≤ ((sz.W n : ℕ) : ℝ) ^ (d + 1) := by
      unfold STAI
      calc 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ≤ 2 * (𝔡⁻¹ ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by
            gcongr
        _ = (2 * 𝔡⁻¹ ^ 2) * ((sz.W n : ℕ) : ℝ) ^ d := by ring
        _ ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_right hWb (by positivity)
        _ = _ := by ring
    calc ρ * ((sz.W n : ℕ) : ℝ) ^ (-DE) ≤ ((sz.W n : ℕ) : ℝ) ^ (d + 1) * ((sz.W n : ℕ) : ℝ) ^ (-DE) :=
          mul_le_mul_of_nonneg_right (hρ2.trans hA2) (Real.rpow_nonneg hW0.le _)
      _ = ((sz.W n : ℕ) : ℝ) ^ (-D - 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hW0]; congr 1; push_cast; rw [hDE]; ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hNτ' : 2 * ((2 * κq + 1) * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    have e1 : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; rw [hτ₁]; push_cast; ring
    have e2 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    rw [e1, ← e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hNτn (Real.rpow_nonneg (by linarith) _)
  have hΦn : ∀ (σ : Fin 2 → Bool) (D'' v w : ℝ), s n ≤ v → v ≤ w → w ≤ (tt n : ℝ) → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Cm.toFlowFM n (σ 0) (σ 1) w x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D'' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
    intro σ D'' v w hv hvw hw a
    have hw1 : w < 1 := hw.trans_lt htt1
    refine hΦC n (σ 0) (σ 1) D'' v w hlam hlamle ((hs n).trans hv) hvw hw1
      (fun x => duhamelIG_theta_rows (hker n) (σ 0) (σ 1) ((hs n).trans (hv.trans hvw)) hw1 x) ?_ a
    exact Or.inr (by linarith [(hReg n).2])
  -- the bad event at the section, as a measurable set of matrices
  set ζ : ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) → ℝ := fun v => F n (tt n, v) +
    STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
      ((sz.W n : ℕ) : ℝ) ^ (-D) with hζ
  set Sset : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    ⋃ v, {H | ((sz.size n : ℕ) : ℝ) ^ τ * ζ v <
      ‖zeroModeSet d (sz.L n) {0} (fun a' => STLKMg Cm n (tt n : ℝ) H v.1.1 a') v.2‖} with hSset
  have hSm : MeasurableSet Sset := MeasurableSet.iUnion fun v =>
    measurableSet_lt measurable_const (duhamelIIG_QLK_meas hGrid' n _ _ _)
  have heq := hlaw s (fun m => (tt m : ℝ)) K n (K n) (hs n) (tt n).2.1 (hKne n) Sset hSm
  rw [gridTime_last s (fun m => (tt m : ℝ)) K n (hKne n)] at heq
  have hbad : badSetAt sz.size (fun n v ω => ‖zeroModeSet d (sz.L n) {0}
        (fun a' => Cm.L n (tt n : ℝ) v.1.1 a' ω - Cm.K n (tt n : ℝ) v.1.1 a') v.2‖)
      (fun n v _ => F n (tt n, v) + STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) τ n = {ω | Hm' n (tt n : ℝ) ω ∈ Sset} := by
    ext ω; simp [badSetAt, hSset, hζ, STLKMg, STLMg, hLM']
  rw [hbad, ← heq]
  set Gset : Set (PathΩ sz) := {ω | ∀ i : sz.STLab n,
      (∀ k, k ≤ K n → STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 k ω =
        STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 0 ω +
          ((gridStep s (fun m => (tt m : ℝ)) K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDriftg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 j ω + Rem n i k ω + Mart n i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n))}
    with hGset
  have hG : Cm.Pp Gsetᶜ = 0 := ae_iff.1 haen
  refine duhamelI_measure_le Cm.Pp (G := Gset) (by linarith) ?_ hΞn hmartn hG
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
  obtain ⟨⟨hA, hB⟩, hGω⟩ := hcon
  obtain ⟨h1, h2, h3, h4⟩ := hA
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hω
  have hv' : ((sz.size n : ℕ) : ℝ) ^ τ * ζ v < ‖zeroModeSet d (sz.L n) {0}
      (fun a' => STLKMg Cm n (tt n : ℝ) (Cm.Hpath s (fun m => (tt m : ℝ)) K n (K n) ω) v.1.1 a') v.2‖ := hv
  have hc : c₀ ≤ (Cm.m n).im := hIm n
  have hMa : ∀ i : sz.STLab n, ∀ k, k ≤ K n → ‖STgAg Cm s (fun m => (tt m : ℝ)) K n i.1 i.2 k ω‖ ≤
      (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ) := by
    intro i k hk
    have hmem := ST_gridTime_mem s (fun m => (tt m : ℝ)) K n k (tt n).2.1 (hKne n) hk
    exact duhamelIG_apriori hL n (hη n) hmem.2 htt1 hTi hc₀ hc (hHerm s (fun m => (tt m : ℝ)) K n k ω) i.1 i.2
      (hKnn _ ((hs n).trans hmem.1) (hmem.2.trans (tt n).2.2) i.1 i.2)
  have hMart' : ∀ i : sz.STLab n, ∀ k, k ≤ K n → ‖Mart n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ *
      Real.sqrt (∑ j ∈ Finset.range k, gridStep s (fun m => (tt m : ℝ)) K n *
        ‖STEEMg Cm n (gridTime s (fun m => (tt m : ℝ)) K n j)
          (Cm.Hpath s (fun m => (tt m : ℝ)) K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) := by
    intro i k hk
    by_contra hlt
    rw [not_le, Real.sqrt_eq_rpow] at hlt
    exact hB (Set.mem_iUnion.2 ⟨i, k, hk, hlt⟩)
  have hrem : ∀ b : Fin 2 → Zd d (sz.L n),
      ‖STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b (K n) ω -
          Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ)
            (fun b' => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b' 0 ω) b‖ ≤
        κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
            STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (b 0) (b 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) := fun b =>
    duhamelIG_path_rem Cm n s (fun m => (tt m : ℝ)) K ω (Mart n) (Rem n)
      (Λ := ((sz.size n : ℕ) : ℝ) ^ τ₁) (D := D) (DE := DE) (Dm := Dm)
      (M := (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ))
      (R := ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n)) (C := C) (c₀ := c₀)
      v.1.1 b (hs n) hsn htt1 (hKne n) hlam hΛ hA1 hc₀ hc hC.le (hker n) (hpair n v.1.1) (hη n) (hΦn v.1.1) hDEn
      (fun i k hk => (hGω i).1 k hk) (fun i k hk => (hGω i).2 k hk) hMa hMart'
      (fun j hj σ b => h2 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, b))
      (fun j hj σ b => h3 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, b))
      (fun j hj σ b k => h4 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) ((σ, b), k)) hfloor
  have hSTgA : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      STgAg Cm s (fun m => (tt m : ℝ)) K n σ b (K n) ω =
        STLKMg Cm n (tt n : ℝ) (Cm.Hpath s (fun m => (tt m : ℝ)) K n (K n) ω) σ b := by
    intro σ b; unfold STgAg; rw [gridTime_last s (fun m => (tt m : ℝ)) K n (hKne n)]
  have hXeq : (fun a' => STLKMg Cm n (tt n : ℝ) (Cm.Hpath s (fun m => (tt m : ℝ)) K n (K n) ω) v.1.1 a') =
      fun b => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b (K n) ω := by
    funext b; exact (hSTgA v.1.1 b).symm
  rw [hXeq] at hv'
  -- `Q^{(1)}` of the initial term (the initial-term event) and of the remainder (`duhamelIG_path_rem` at every label)
  have hI := h1 v
  have hQ := duhamelII_Q_sub_le (fun b => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b (K n) ω)
    (Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ)
      (fun b' => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b' 0 ω)) v.2
  have hins := norm_le_insert'
    (zeroModeSet d (sz.L n) {0} (fun b => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b (K n) ω) v.2)
    (zeroModeSet d (sz.L n) {0} (Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ)
      (fun b' => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b' 0 ω)) v.2)
  have hR0 := hrem v.2
  have hRc : ∀ c' : Zd d (sz.L n),
      ‖STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 (Function.update v.2 0 c') (K n) ω -
          Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ)
            (fun b' => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b' 0 ω) (Function.update v.2 0 c')‖ ≤
        κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
            STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) c' (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) := fun c' => by
    have := hrem (Function.update v.2 0 c')
    rwa [(duhamelII_update_apply v.2 c').1, (duhamelII_update_apply v.2 c').2] at this
  have hreg2 : 1 - (tt n : ℝ) ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    linarith [(hReg n).2, (tt n).2.1]
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
    positivity
  have hsum : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c' : Zd d (sz.L n),
      ‖STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 (Function.update v.2 0 c') (K n) ω -
          Step2Gen_UN Cm.toFlowFM n v.1.1 (s n) (tt n : ℝ)
            (fun b' => STgAg Cm s (fun m => (tt m : ℝ)) K n v.1.1 b' 0 ω) (Function.update v.2 0 c')‖ ≤
      κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
          (CA * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1)) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have havg := hAvg sz n D (tt n : ℝ) hlam.le htt1 hreg2 (v.2 0) (v.2 1)
    calc _ ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c' : Zd d (sz.L n),
          (κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
            STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) c' (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c' _ => hRc c') (inv_nonneg.2 hLd.le)
      _ = κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
            ((((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c' : Zd d (sz.L n), STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) c' (v.2 1)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Zd]
          push_cast
          field_simp
      _ ≤ _ := by gcongr
  -- the exponent closure
  have hP0 : 0 ≤ STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) := (ST_STprof_pos sz n _ _ _ _ _).le
  have hWm0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hBk0 : 0 ≤ κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) := by
    have : 0 ≤ STAI sz n ^ (-(1 / 4) : ℝ) := by unfold STAI; exact Real.rpow_nonneg (by positivity) _
    positivity
  have hchain := duhamelII_chain hins hQ hI hR0 hsum
  have e : κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
      κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
        (CA * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1)) =
      (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * κq * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ)) *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) := by
    rw [hκq]; ring
  rw [e] at hchain
  have hfin := duhamelII_close hΛ hκq0 (hF0 n (tt n, v)) hP0 hWm0 hA1 hρ1 hρA hNτ' hchain
  exact absurd hfin (not_le.2 hv')

end SectionMainII

/-! ## 5. The engine, `STDuhamelIIgL` and the band corollaries -/

section Main

variable {d : ℕ}

/-- `STReg5II` is `STReg5Mid` with the second bound strengthened (`ilambda²/L² ≤ ilambda²`). -/
private theorem duhamelII_reg5II_mid {sz : Sizes d} {s t : ℕ → ℝ} (h : STReg5II sz s t) : STReg5Mid sz s t :=
  fun n => ⟨(h n).1, duhamelII_mid sz n (h n).2⟩

/-- **The engine of `STDuhamelIIgL`, mixed conjunct, over a carrier family** ((5.40) `zYU2`), zero-mode set `Q = {0}` (`Q^{(1)}`), any
sign class `P` (the argument does not use the signs): if `‖Q^{(1)} 𝒰_{s,u}(𝓛-𝒦)^{(2)}_{s,σ}‖_a ≺ F`, then `‖Q^{(1)}(𝓛-𝒦)^{(2)}_{u,σ}‖_a ≺ F + A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}`
uniformly in `u ∈ [s,t]`, `σ ∈ P`.  The window is `STReg5II` (`ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`: the second half is (3.21) `TTT2` through `Or.inr` and the saturation
`ℓ_u = L` of the profile).  The proof applies `Q^{(1)}` to the pathwise remainder of the grid Duhamel form (`duhamelIG_path_rem`) instead of the paper's `Θ̊`-weighted kernel
estimates.  Family premises as in `stDuhamelConclgL_engine`: `hF` the flow facts, `hKer` the kernel facts at the coupling `gK`, `hGR` `GridRepTailGen_Ker`,
`hGM` the grid decomposition and martingale tail, `hBd, hK2` the size data and the decay of `𝒦^{(2)}`, `hFM` the flow modulus
(the constant `c` is chosen before `(sz, 𝔠, z)`), `hmn` the inline `‖m‖ ≤ 1`, `hKs` the time modulus of `𝒦^{(2)}` (the text of `NQEndFlowGen_KLipFam` at `k = 2`, inline), `hLF` the
loop form, `hGrid` the grid-law facts `Step2EventsGen_Grid` and `hHerm` the Hermitian grid walk. -/
theorem _root_.RBM.BA.stDuhamelConclgL_engineQ1 (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hF : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hKer : IniTermGen_KerFacts d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hGR : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hGM : STGridMartgL d Flow mkM T0) (hBd : STBdatagL d Flow T0) (hK2 : Step2IterGen_K2 d Flow mkM)
    (hFM : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c)
    (hmn : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hKs : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, t n ≤ T0 sz z n) →
        ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
          ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
            ‖(mkM sz z).K n u σ a - (mkM sz z).K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'|)
    (hLF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mkM sz z) (law sz))
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mkM sz z).Hpath s t K n k ω).IsHermitian)
    (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ T0 sz z n) (hReg : STReg5II sz s t)
    (hCon : STConStInd sz (1 / 100) s t) (hE : ∀ D : ℝ, 0 < D →
      PrecL sz (law sz) (U := STIdx2 sz s t) (fun n p ω => ‖STELKLKg (mkM sz z).toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * ((mkM sz z).eta n (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      PrecL sz (law sz) (U := STIdx2 sz s t) (fun n p ω => ‖STEGtg (mkM sz z).toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * ((mkM sz z).eta n (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      PrecL sz (law sz) (U := fun n => STIdx2 sz s t n × Fin 2)
        (fun n p ω => ‖STEEg (mkM sz z).toFlowFM n (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * ((mkM sz z).eta n (p.1.1 : ℝ))⁻¹ *
          STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2))
    (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConclgL (mkM sz z).toFlowFM (law sz) {0} P s t := by
  classical
  intro D hD F hF0 hini
  obtain ⟨κm, hκm, hFm⟩ := hF κ hκ
  obtain ⟨hAd, hT1, hIm, hηeq⟩ := hFm sz ε 𝔠 𝔡 z hflow
  have hsize : sz.SizeTendsto := hAd.2.2.1
  have hsN := tendsto_size sz hsize
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htz n) (hT1 n)
  have ht0 : ∀ n, 0 ≤ t n := fun n => (hs n).trans (hst n).le
  have hm := hmn sz κ ε 𝔠 𝔡 z hκ hflow
  have hL := hLF sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨C₀, hC₀, hGMA⟩ := hGM
  -- the kernel facts, `Φ` of a profile and the swap
  obtain ⟨C₆, C₈, Cs, c₀k, A, hC₆, hC₈, hCs, hc₀k, hA, Hk⟩ := hKer hd κ 𝔡 hκ h𝔡
  obtain ⟨hUsg, hdec, hcmp, hswap, -⟩ := Hk sz ε 𝔠 z hflow
  obtain ⟨C, hC, hΦ⟩ := duhamelIG_Phi_lam hd (Λ := 𝔡⁻¹) (inv_pos.2 h𝔡) hC₆ hA
  have hΦC := hΦ sz (mkM sz z).toFlowFM (gK sz z) hdec hcmp
  -- the size of `𝒦^{(2)}` and its time modulus
  obtain ⟨CK, hCK, hdec2⟩ := hK2 hd κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow (fun _ => 0) t (fun _ => le_rfl) ht1
  obtain ⟨cB, hcB, hBdata⟩ := hBd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hBdz⟩ := hBdata 𝔠
  have hKn := lemDecCalELipG_Kn hCK.le hcB hc hsize
    (hdec2.mono fun n h u D σ a hu hut hD => h u D σ a hu hut hD) (hBdz sz z hflow t ht0 htz)
  have hKsz := hKs sz κ ε 𝔠 𝔡 z hκ hε hflow t htz
  -- the flow modulus
  obtain ⟨c₁, hc₁, hFMz⟩ := hFM κ ε 𝔡 hκ hε h𝔡
  obtain ⟨Hm, G, hLM, hGMM, hG, hmod⟩ := hFMz sz 𝔠 z hflow
  by_cases hP : ∃ σ, P σ
  swap
  · exact Step2EventsGen_prec_of_le_ev (law sz) (fun n p ω => absurd ⟨p.2.1.1, p.2.1.2⟩ hP)
      (Eventually.of_forall fun n p ω => absurd ⟨p.2.1.1, p.2.1.2⟩ hP)
  have hne : ∀ n, Nonempty ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) :=
    fun n => ⟨(⟨hP.choose, hP.choose_spec⟩, fun _ => 0)⟩
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [ht1 n, hs n]
  have hev := st5_eventually_A_ge_one sz h𝔡 hAd.2.2.2.2
  have htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [hev] with n hn
    exact duhamelI_htN sz n hn.1 hn.2 (hReg n).1
  have hQ := (LemDecCalELip_envg hκm hIm hηeq hsize htN 0).mono fun n h => h.2.2.1
  obtain ⟨CH, hCH0, hCH⟩ := duhamelIIG_holder hL hLM hc₁ hmod hm hs ht1 hsize hQ hKsz
  refine duhamelIG_lift sz (law sz) G hG hsize (fun n => (hst n).le) hlen
    (V := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) (Cv := 3) (CR := D) (by norm_num) hD.le ?_
    (fun n p ω => ‖zeroModeSet d (sz.L n) {0}
      (fun a' => (mkM sz z).L n (p.1 : ℝ) p.2.1.1 a' ω - (mkM sz z).K n (p.1 : ℝ) p.2.1.1 a') p.2.2‖)
    (fun n p => F n p + STAI sz n ^ (-(1 / 5) : ℝ) *
      STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ?_ ?_ ?_ ⟨CH, hCH0, ?_⟩
  · filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    exact duhamelI_card_le sz P n hn
  · intro n p
    exact add_nonneg (add_nonneg (hF0 n p) (mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) _)
      (ST_STprof_pos sz n _ _ _ _ _).le)) (Real.rpow_nonneg (by positivity) _)
  · exact Step2EventsGen_PT_of_sections (law sz) (fun n => (hst n).le) _ _ fun tt =>
      duhamelIIG_section hd law Flow mkM T0 hC₀ hGMA hκ hε h𝔡 sz hflow hAd hκm hIm hηeq hL (hGrid sz z) (hHerm sz z)
        (hGR sz κ ε 𝔠 𝔡 z hκ hflow) (fun n σ w hw0 hw1 => duhamelIG_pair n (hUsg n) (hswap n) σ hw0 hw1) hC hΦC hs hst htz ht1 hKn hReg
        hCon hE hD P F hF0 hini tt
  · filter_upwards with n p
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWm : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hW0 (duhamelI_W_le_size sz (by omega) n) (neg_nonpos.2 hD.le)
    have := mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) (-(1 / 5) : ℝ) : (0 : ℝ) ≤ STAI sz n ^ (-(1 / 5) : ℝ))
      (ST_STprof_pos sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)).le
    linarith [hF0 n p]
  · filter_upwards [hCH] with n hn ω hω u u' v
    exact hn ω hω u u' v.1.1 v.2


/-- **`STDuhamelIIgL`** (case (ii), the integrated hierarchy: `Q^{(1)}` for `σ₁ ≠ σ₂`, no zero-mode removal for `σ₁ = σ₂`) over a carrier family: the mixed conjunct is
`stDuhamelConclgL_engineQ1`, the equal-sign conjunct is `stDuhamelConclgL_engine` (`Q = ∅`) with (3.21) `TTT2` through `Or.inr`; `𝔠_d = 1/100`.  The premises are those of the engines;
`stDuhamelII_holds` is its corollary for the band matrix model through `STDuhamelII_iff_gL`. -/
theorem _root_.RBM.BA.stDuhamelIIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hF : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hKer : IniTermGen_KerFacts d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hGR : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hGM : STGridMartgL d Flow mkM T0) (hBd : STBdatagL d Flow T0) (hK2 : Step2IterGen_K2 d Flow mkM)
    (hFM : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c)
    (hmn : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hKs : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, t n ≤ T0 sz z n) →
        ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
          ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
            ‖(mkM sz z).K n u σ a - (mkM sz z).K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'|)
    (hLF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mkM sz z) (law sz))
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mkM sz z).Hpath s t K n k ω).IsHermitian) :
    STDuhamelIIgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg _ _ _ _ _ hCon _ _ _ _ hE
  exact ⟨RBM.BA.stDuhamelConclgL_engineQ1 d law Flow mkM T0 E gK hF hKer hGR hGM hBd hK2 hFM hmn hKs hLF hGrid hHerm hd hκ hε h𝔡 sz
      hflow hs hst htz hReg hCon hE STSigMixed,
    RBM.BA.stDuhamelConclgL_engine d law Flow mkM T0 E gK hF hKer hGR hGM hBd hK2 hFM hmn hKs hLF hGrid hHerm hd hκ hε h𝔡 sz
      hflow hs hst htz (duhamelII_reg5II_mid hReg) (fun n => Or.inr (hReg n).2) hCon hE STSigSame⟩

/-- **`STDuhamelIIgL` for the band matrix model**: `stDuhamelIIgL_of` at `(seqP, STFlow, bandStep2Mat ∘ STflowE, lemT)` with `gK = lam`; every premise is discharged by an existing
band result (as in `duhamelI_band_gL`). -/
theorem duhamelII_band_gL (d : ℕ) (hd : 3 ≤ d) :
    STDuhamelIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  RBM.BA.stDuhamelIIgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) (fun _ z => STflowE z) (fun sz _ => sz.lam)
    (step5CasesGen_flowFacts_band d) (iniTermGen_kerFacts_band d)
    (fun sz κ ε 𝔠 𝔡 z _ h n => gridRepTailGen_ker_band sz (STflowE z) n (abs_lemE_lt_two (ST_flow_im_pos sz h n)).le)
    (bandStep2_STGridMart.1 (ST_gridMart_of_repN (RBM.Ind.stGridRepN_holds d hd)))
    ((bandFM_STBdata d).1 (ST_Bdata_holds (by omega))) (step2IterGen_K2_band d)
    (fun _ _ _ _ _ _ => ⟨1, zero_le_one, fun sz _ z h => lemDecCalELipG_flowMod_band sz (tendsto_size sz h.1.2.2.1) _⟩)
    (fun sz κ ε 𝔠 𝔡 z _ h n => (norm_mE (abs_lemE_lt_two (ST_flow_im_pos sz h n)).le).le)
    (fun sz κ ε 𝔠 𝔡 z hκ hε h t ht => duhamelI_Ks_band d sz κ ε 𝔠 𝔡 z hκ hε h t ht)
    (fun sz κ ε 𝔠 𝔡 z _ h => stepDecompGen_loopForm_band sz (STflowE z) fun n => abs_lemE_lt_two (ST_flow_im_pos sz h n))
    (fun sz z => Step2EventsGen_bandGrid sz (STflowE z)) (fun sz z s t K n k ω => pathH_isHermitian sz s t K n k ω)

/-- **`STDuhamelII`** (case (ii), the integrated hierarchy: `Q^{(1)}` for `σ₁ ≠ σ₂`, no zero-mode removal for `σ₁ = σ₂`): the band corollary of
`stDuhamelIIgL_of` through `STDuhamelII_iff_gL`. -/
theorem stDuhamelII_holds (d : ℕ) : STDuhamelII d :=
  (RBM.BA.STDuhamelII_iff_gL d).2 fun hd => duhamelII_band_gL d hd hd

end Main

end RBM.Gauss.Sizes
