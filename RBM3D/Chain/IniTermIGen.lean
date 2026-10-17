/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.CltFarUGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.B45Gen

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The initial term of Step 5, case (i), over the carrier (T2484, U4s2b)

Additive generic form of `Induction/IniTermI.lean` (not edited) over a carrier tuple `(law, Flow, mk, T0)` of
`Chain/Step5Gen.lean`, on the one kernel `Step2Gen_UN` and the one propagator `STThg` (U-C4: no kernel, no propagator and no bridge
is defined here).  Paper: arXiv:2507.20274, case (i) is `(iksjuwjx0)`, `3_5:2072-2172`; `(eq:decompU)` is `3_5:1983`;
`(prop:ThfadC)`, `(prop:ThfadC_short)` are Proposition 5.  No new mathematics.

* **Target 8 (a).**  The deterministic cores `iniTermIGen_core_same`, `iniTermIGen_core_mixed`, `iniTermIGen_core_lossy` on the
  representation `𝒰 = K ⊗ K` of `IniTermIIGen_UN_rep` (`σ₁ = σ₂`: the short-range bound `iniTermI_bil_same`; `σ₁ ≠ σ₂`: `(eq:decompU)`,
  the profile `(uwp2-92kj)` in regime (i) `IniTermIGen_stageA`, the second-index smoothing `IniTermIIGen_ZA`).
* **Target 8 (b).**  The bounds on `Θ_u`: the decay in the size-level tail `IniTermIGen_Th_decay`, `theta_pi`, `theta_far` (from
  `STThPropsg`, X1a's text), `theta_conv` (decay twice and `ekPropTInf_holds`).
* **Target 8 (c).**  `(1-s)² Θ 𝓑 Θ = f^{near} + f^{far} + g` over an abstract propagator, with `f^{far} = STfFarg` (definitional,
  `CltFarUGen`); the mixed bound and the tail bound.
* **Targets 8 (d) and 9** are in the reserve file `Chain/IniTermIGen2.lean` (it imports this file): the Ward step at the last
  label (`B45_ward_fing`, `ZeroModeGen_WardCls`), the real-level estimates, `iniTermIGen_concl`, the pin `stIniTermIgL_of` and the
  band re-derivation `iniTermIGen_band_holds` of `stIniTermI_holds`.

Coupling (UBA-C1): the decay of `Θ` is read at `gK` and crosses to the size-level tail at `sz.lam` through R1
(`Step5KerGen_tailT_cross`, in `IniTermIGen_Th_decay` only), the guard (g) is `CltFarUGen_guard`.

Ported from `Induction/IniTermI.lean` of this project (last commit of the file `850a8a3b`): §3' `stageA` (`:301`), §7 `Ugen_rep` (`:454`), §7'
`U0`, `bil_lossy` (`:931`, `:1021`), §8'-§9' cores (`:1143`, `:1191`, `:1229`), §10 (`:1280-1322`), §12 `tail` (`:1511`), §16
`theta_pi/far/conv` (`:2135-2223`), §17 `mixed_bound`, `mixed_tail` (`:2254`, `:2489`) for the carrier.  The model-free lemmas of
the band file are reused by name.  The d = 1 and d = 2 projects are not used.
-/

open private IniTermIIGen_ZA IniTermIIGen_Kf_norm_le from RBM3D.Chain.IniTermIIGen
open private CltFarUGen_fSum from RBM3D.Chain.CltFarUGen
open private Step5KerGen_cmp_pos Step5KerGen_tailT_cross from RBM3D.Chain.Step5KerGen

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-! ## 1. Target 8 (b): the bounds on `Θ_u` -/

section ThetaB

variable {d : ℕ} {sz : Sizes d}

/-- **Decay of `Θ_u` in the size-level tail**: `Θ = 1 + uθ`, the decay of `θ` at `gK` (`Step5KerGen_ThDecay`), the crossing
`𝒯^{gK} ≤ A 𝒯^{lam}` (R1, `Step5KerGen_tailT_cross`) and `1 ≤ (AΛ²+1) 𝒯^{lam}_u(0)`:
`|Θ_u(x,y)| ≤ (C₆ A + (AΛ²+1)) 𝒯^{lam}_u(|y-x|_∞)` (band `step5Kernel_theta_decay`, `Step5Kernel:135`). -/
private theorem IniTermIGen_Th_decay (C : FlowFM sz) (gK : ℕ → ℝ) (n : ℕ) (hU : Step2Gen_USemigroup C n) {Λ C₆ A : ℝ}
    (hC₆ : 0 ≤ C₆) (hA : 1 ≤ A) (hdec : Step5KerGen_ThDecay C gK Λ C₆)
    (hcmp : 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2)
    (hg : 0 < gK n) (hgΛ : gK n ≤ Λ) (p q : Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y : Zd d (sz.L n)) :
    ‖STThg C n p q u x y‖ ≤
      (C₆ * A + (A * Λ ^ 2 + 1)) * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (y - x) : ℕ) := by
  obtain ⟨hlam, hc1⟩ := Step5KerGen_cmp_pos hcmp hg
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  obtain ⟨hθ, -⟩ := hdec n hg hgΛ p q u hu0 hu1
  have hcr := Step5KerGen_tailT_cross (d := d) (L := sz.L n) (t := u)
    (r := ((zdistInf d (sz.L n) (y - x) : ℕ) : ℝ)) hL1 hg hc1 hcmp.2.2 hA hu1 (Nat.cast_nonneg _)
  have hT0 : 0 ≤ tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (y - x) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
  have hθ' : ‖Step2Gen_thetaKer C n p q u x y‖ ≤
      C₆ * A * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (y - x) : ℕ) :=
    (hθ x y).trans (by
      calc _ ≤ C₆ * (A * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (y - x) : ℕ)) :=
            mul_le_mul_of_nonneg_left hcr hC₆
        _ = _ := by ring)
  have e : ‖STThg C n p q u x y‖ ≤ (if x = y then (1 : ℝ) else 0) + ‖Step2Gen_thetaKer C n p q u x y‖ := by
    rw [IniTermIIGen_Theta_eq C n hU p q hu0 hu1, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
      exact mul_le_of_le_one_left (norm_nonneg _) hu1.le
  by_cases hxy : x = y
  · subst hxy
    simp only [ite_true] at e
    have hge := iniTermI_tailT_ge_PI (d := d) (L := sz.L n) hlam hu1 (0 : Zd d (sz.L n))
    have hP : iniTermI_PI d (sz.L n) 0 = 1 := by simp [iniTermI_PI, iniTermI_zdistInf_zero]
    rw [hP, mul_one, iniTermI_zdistInf_zero, Nat.cast_zero, zero_div, Real.sqrt_zero, neg_zero, Real.exp_zero, mul_one] at hge
    rw [sub_self, iniTermI_zdistInf_zero, Nat.cast_zero] at hθ' hT0 ⊢
    have hlt : sz.lam n ^ 2 + (1 - u) ≤ A * Λ ^ 2 + 1 := by
      have : sz.lam n ^ 2 ≤ A * Λ ^ 2 := (hcmp.2.2).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le hgΛ 2) (by linarith))
      linarith
    have hpos : 0 < sz.lam n ^ 2 + (1 - u) := by have := sq_nonneg (sz.lam n); linarith
    have h1 : 1 ≤ (A * Λ ^ 2 + 1) * (sz.lam n ^ 2 + (1 - u))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]; linarith
    have h2 : (A * Λ ^ 2 + 1) * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (A * Λ ^ 2 + 1) * tailT d (sz.L n) (sz.lam n) u 0 :=
      mul_le_mul_of_nonneg_left hge (by have := sq_nonneg Λ; nlinarith)
    nlinarith
  · simp only [hxy, ite_false] at e
    nlinarith [mul_nonneg (by nlinarith [sq_nonneg Λ] : 0 ≤ A * Λ ^ 2 + 1) hT0]

/-- `Θ_u` is bounded by the power kernel (band `iniTermI_theta_pi`, `IniTermI:2135`), from the decay in the tail. -/
private theorem IniTermIGen_theta_pi {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) {g u CΘ : ℝ} (hg : 0 < g) (hu : u < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) (hCΘ : 0 ≤ CΘ) {Th : Zd d L → Zd d L → ℂ}
    (hdec : ∀ x y, ‖Th x y‖ ≤ CΘ * tailT d L g u (zdistInf d L (y - x) : ℕ)) (x y : Zd d L) :
    ‖Th x y‖ ≤ (CΘ * (1 + 2 ^ (d - 1))) * (g ^ 2)⁻¹ * iniTermI_PI d L (x - y) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  refine (hdec x y).trans ?_
  have h1 := iniTermI_tailT_le_PI' hd hL1 hu hreg (y - x)
  have h2 : (g ^ 2 + (1 - u))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hP := iniTermI_PI_nonneg (d := d) (L := L) (y - x)
  rw [iniTermI_PI_sub_comm y x] at h1 hP
  calc CΘ * tailT d L g u (zdistInf d L (y - x) : ℕ)
      ≤ CΘ * ((1 + 2 ^ (d - 1)) * ((g ^ 2 + (1 - u))⁻¹ * iniTermI_PI d L (x - y))) :=
        mul_le_mul_of_nonneg_left h1 hCΘ
    _ ≤ CΘ * ((1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ * iniTermI_PI d L (x - y))) := by
        gcongr
    _ = _ := by ring

/-- **The far decay of `Θ_u`** (band `iniTermI_theta_far`, `IniTermI:2154`) from X1a's `STThPropsg` (`(prop:ThfadC)`, shift): for
mixed `σ`, `r < |y-x|_∞`, `|Θ_u(x,y)| ≤ 2 C₅ (1-u)⁻¹ e^{-c₅ r/ℓ_u}`, eventually in `n`. -/
private theorem IniTermIGen_theta_far {d : ℕ} {sz : Sizes d} {C : FlowFM sz} (hTh : STThPropsg C) :
    ∃ Cf cf : ℝ, 0 < Cf ∧ 0 < cf ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
      ∀ (x y : Zd d (sz.L n)) (r : ℝ), r < ((zdistInf d (sz.L n) (y - x) : ℕ) : ℝ) →
        ‖STThg C n (σ 0) (σ 1) u x y‖ ≤ Cf * (1 - u)⁻¹ * Real.exp (-(cf * r / ellT (sz.L n) (sz.lam n) u)) := by
  obtain ⟨C₅, c₅, C₆, C₇, hC₅, hc₅, -, -, hev⟩ := hTh
  refine ⟨2 * C₅, c₅, by positivity, hc₅, ?_⟩
  filter_upwards [hev] with n hn u hu0 hu σ hσ x y r hr
  obtain ⟨hshift, -, hdecay, -⟩ := hn u hu0 hu σ hσ
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  rw [hshift x y]
  refine (hdecay (y - x)).trans ?_
  have hu1 : 0 < 1 - u := by linarith
  have hℓ : 0 < ellT (sz.L n) (sz.lam n) u := ellT_pos hL1
  have hB : Bparam d (sz.L n) (sz.lam n) u (zdistD d (sz.L n) (y - x)) ≤ 2 * (1 - u)⁻¹ := by
    unfold Bparam
    rw [abs_of_pos hu1]
    have h1 : (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ := by
      have : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hu1 (by nlinarith [sq_nonneg (sz.lam n)])
      have h2 : ((((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) := Nat.cast_nonneg _; linarith))
      calc _ ≤ (1 - u)⁻¹ * 1 := mul_le_mul this h2 (by positivity) (by positivity)
        _ = _ := mul_one _
    have h3 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
      inv_anti₀ hu1 (le_mul_of_one_le_left hu1.le (one_le_pow₀ hL1))
    linarith
  have hD : r ≤ ((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) :=
    hr.le.trans (by exact_mod_cast zdistInf_le_zdistD d (sz.L n) (y - x))
  have hE : Real.exp (-c₅ * ((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ≤
      Real.exp (-(c₅ * r / ellT (sz.L n) (sz.lam n) u)) := by
    refine Real.exp_le_exp.mpr ?_
    have : c₅ * r / ellT (sz.L n) (sz.lam n) u ≤ c₅ * ((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD hc₅.le) hℓ.le
    have e : -c₅ * ((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u =
        -(c₅ * ((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) := by ring
    linarith
  calc C₅ * Bparam d (sz.L n) (sz.lam n) u (zdistD d (sz.L n) (y - x)) *
        Real.exp (-c₅ * ((zdistD d (sz.L n) (y - x) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u)
      ≤ C₅ * (2 * (1 - u)⁻¹) * Real.exp (-(c₅ * r / ellT (sz.L n) (sz.lam n) u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB hC₅.le) hE (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The convolution of `Θ` with itself (band `iniTermI_theta_conv`, `IniTermI:2196`): decay twice and `ekPropTInf_holds` (`(TTT2)`). -/
private theorem IniTermIGen_theta_conv (d : ℕ) (hd : 3 ≤ d) : ∃ CT : ℝ, 0 < CT ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ {g u CΘ : ℝ}, 0 < g → 0 ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 0 ≤ CΘ →
      ∀ (Th : Zd d L → Zd d L → ℂ), (∀ x y, ‖Th x y‖ ≤ CΘ * tailT d L g u (zdistInf d L (y - x) : ℕ)) →
        ∀ a₀ a₁ : Zd d L, ∑ b : Zd d L, ‖Th a₀ b‖ * ‖Th b a₁‖ ≤
          CΘ ^ 2 * CT * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a₀ - a₁) : ℕ) := by
  obtain ⟨CT, hCT, hT⟩ := ekPropTInf_holds d hd
  refine ⟨CT, hCT, fun L _ hL g u CΘ hg hu0 hu hreg hCΘ Th hdec a₀ a₁ => ?_⟩
  have hu1 : 0 < 1 - u := by linarith
  have hS := hT L g u u hg hu0 le_rfl hu (Or.inl hreg) a₀ a₁
  have hpt : ∀ b : Zd d L, ‖Th a₀ b‖ * ‖Th b a₁‖ ≤
      CΘ ^ 2 * (tailT d L g u (zdistInf d L (a₀ - b) : ℕ) * tailT d L g u (zdistInf d L (b - a₁) : ℕ)) := by
    intro b
    have h1 := hdec a₀ b
    have h2 := hdec b a₁
    rw [iniTermI_zdistInf_sub_comm b a₀] at h1
    rw [iniTermI_zdistInf_sub_comm a₁ b] at h2
    calc _ ≤ (CΘ * tailT d L g u (zdistInf d L (a₀ - b) : ℕ)) * (CΘ * tailT d L g u (zdistInf d L (b - a₁) : ℕ)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by have := tailT_nonneg (d := d) (L := L) (g := g) (t := u)
                                                  (Nat.cast_nonneg (zdistInf d L (a₀ - b))); positivity)
      _ = _ := by ring
  calc ∑ b : Zd d L, ‖Th a₀ b‖ * ‖Th b a₁‖
      ≤ ∑ b : Zd d L, CΘ ^ 2 * (tailT d L g u (zdistInf d L (a₀ - b) : ℕ) * tailT d L g u (zdistInf d L (b - a₁) : ℕ)) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = CΘ ^ 2 * ∑ b : Zd d L, tailT d L g u (zdistInf d L (a₀ - b) : ℕ) * tailT d L g u (zdistInf d L (b - a₁) : ℕ) := by
        rw [Finset.mul_sum]
    _ ≤ CΘ ^ 2 * (CT / (1 - u) * tailT d L g u (zdistInf d L (a₀ - a₁) : ℕ)) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring


end ThetaB

/-! ## 2. Target 8 (a): the profile in regime (i), the one-index kernel and the deterministic cores -/

section Cores

/-- **`(uwp2-92kj)` without the floor, regime (i)** for the carrier propagator (band `iniTermI_stageA`, `IniTermI:301`): with
`Θ = 1 + uθ` the profile `step5KerGen_profile_holds` of `θ` (at `(u, t) ↦ (s, u)`, decay at `gK`, windows at `sz.lam`, R1; the
window `lam²/L² ≤ 1 - u` of regime (i)) gives `(1-s) Σ_b |Θ_u(a₁,b)| 𝒯_s(|b-a₂|) ≤ C 𝒯_u(|a₁-a₂|)` with `C = Cp + 1`; the floor
`w` is arbitrary. -/
private theorem IniTermIGen_stageA (d : ℕ) (hd : 3 ≤ d) (Λ C₆ A : ℝ) (hΛ : 0 < Λ) (hC₆ : 0 < C₆) (hA : 1 ≤ A) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ →
      (∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) →
      ∀ (n : ℕ), Step2Gen_USemigroup C n → ∀ (σ σ' : Bool) (s u : ℝ), 0 < gK n → gK n ≤ Λ → 0 ≤ s → s ≤ u → u < 1 →
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u → ∀ a₁ a₂ : Zd d (sz.L n),
          (1 - s) * ∑ b : Zd d (sz.L n), ‖STThg C n σ σ' u a₁ b‖ *
              tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b - a₂) : ℕ) ≤
            CA * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) := by
  obtain ⟨Cp, hCp, H⟩ := step5KerGen_profile_holds d hd Λ C₆ A hΛ hC₆ hA
  refine ⟨Cp + 1, by positivity, ?_⟩
  intro sz C gK hdec hcmp n hU σ σ' s u hg hgΛ hs hsu hu hreg a₁ a₂
  obtain ⟨hlam, hc1⟩ := Step5KerGen_cmp_pos (hcmp n) hg
  have hs1 : 0 ≤ 1 - s := by linarith
  have hu0 : 0 < 1 - u := by linarith
  have hu0' : 0 ≤ u := hs.trans hsu
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  set ρ : ℝ := (1 - s) / (1 - u) with hρdef
  have hρ : 0 ≤ ρ := div_nonneg hs1 hu0.le
  have hρ1 : 1 - s ≤ ρ := le_div_self hs1 hu0 (by linarith)
  apply le_of_forall_pos_le_add
  intro ε hε
  set w : ℝ := ε / ((Cp + 1) * (1 + ρ)) with hwdef
  have hw : 0 < w := div_pos hε (by positivity)
  have h := H sz C gK hdec hcmp n σ σ' w⁻¹ 1 s u hg hgΛ (inv_pos.mpr hw) hs hsu hu (Or.inl hreg) a₁ a₂
  rw [Real.rpow_neg_one, inv_inv] at h
  have hW : ∀ r : ℝ, tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 r =
      max (tailT d (sz.L n) (sz.lam n) s (min r ((sz.L n : ℕ) : ℝ))) w := fun r => by
    unfold tailW; rw [Real.rpow_neg_one, inv_inv]
  have hle : ∀ b : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b - a₂) : ℕ) ≤
      tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (b - a₂) : ℕ) := fun b => by
    rw [hW, min_eq_left (iniTermI_zdistInf_le_L _)]
    exact le_max_left _ _
  have hTW : tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) ≤
      tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) + w := by
    rw [hW, min_eq_left (iniTermI_zdistInf_le_L _)]
    exact max_le ((iniTermI_tailT_mono hlam.le hL1 hsu hu (Nat.cast_nonneg _)).trans (le_add_of_nonneg_right hw.le))
      (le_add_of_nonneg_left (tailT_nonneg (Nat.cast_nonneg _)))
  have e : ∀ b, ‖STThg C n σ σ' u a₁ b‖ ≤ (if a₁ = b then (1 : ℝ) else 0) + ‖Step2Gen_thetaKer C n σ σ' u a₁ b‖ := by
    intro b
    rw [IniTermIIGen_Theta_eq C n hU σ σ' hu0' hu, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0']
      exact mul_le_of_le_one_left (norm_nonneg _) hu.le
  have hTWn : ∀ r : ℝ, 0 ≤ tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 r := fun r => by
    rw [hW]; exact le_max_of_le_right hw.le
  have hsum : ∑ b : Zd d (sz.L n), ‖STThg C n σ σ' u a₁ b‖ *
        tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b - a₂) : ℕ) ≤
      tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) +
        ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' u a₁ b‖ *
          tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (b - a₂) : ℕ) := by
    calc _ ≤ ∑ b : Zd d (sz.L n), (((if a₁ = b then (1 : ℝ) else 0) + ‖Step2Gen_thetaKer C n σ σ' u a₁ b‖) *
          tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (b - a₂) : ℕ)) :=
          Finset.sum_le_sum fun b _ => mul_le_mul (e b) (hle b) (tailT_nonneg (Nat.cast_nonneg _))
            (add_nonneg (by split_ifs <;> norm_num) (norm_nonneg _))
      _ = _ := by
          simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
            ite_true]
  have hρw : (Cp + 1) * (ρ * w) ≤ ε := by
    have hCp1 : (Cp + 1) ≠ 0 := by positivity
    have hρ1' : (1 + ρ) ≠ 0 := by positivity
    have e : (Cp + 1) * (ρ * w) = ρ / (1 + ρ) * ε := by rw [hwdef]; field_simp
    rw [e]
    have : ρ / (1 + ρ) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    nlinarith [hε]
  have hT0 : 0 ≤ tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
  calc (1 - s) * ∑ b : Zd d (sz.L n), ‖STThg C n σ σ' u a₁ b‖ *
          tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b - a₂) : ℕ)
      ≤ (1 - s) * (tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) +
        ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' u a₁ b‖ *
          tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (b - a₂) : ℕ)) :=
        mul_le_mul_of_nonneg_left hsum hs1
    _ ≤ (1 - s) * (tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) + w) +
          (Cp * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) + Cp * (ρ * w)) := by
        rw [mul_add]
        refine add_le_add (mul_le_mul_of_nonneg_left hTW hs1) ?_
        exact h
    _ ≤ (Cp + 1) * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) + (Cp + 1) * (ρ * w) := by
        have h1 : (1 - s) * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) ≤
            tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) := by nlinarith
        have h2 : (1 - s) * w ≤ ρ * w := mul_le_mul_of_nonneg_right hρ1 hw.le
        nlinarith
    _ ≤ _ := by linarith


/-- The one-index kernel `K = α 1 + β Θ_u` of `(eq:decompU)` over an abstract propagator (band `iniTermI_Kf`, `IniTermI:663`). -/
private def IniTermIGen_Kf {d L : ℕ} [NeZero L] (Th : Zd d L → Zd d L → ℂ) (α β : ℝ) (a b : Zd d L) : ℂ :=
  (if a = b then (α : ℂ) else 0) + (β : ℂ) * Th a b

private theorem IniTermIGen_Kf_norm_le {d L : ℕ} [NeZero L] (Th : Zd d L → Zd d L → ℂ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (a b : Zd d L) : ‖IniTermIGen_Kf Th α β a b‖ ≤ α * (if a = b then 1 else 0) + β * ‖Th a b‖ :=
  IniTermIIGen_Kf_norm_le Th hα hβ a b


variable {d L : ℕ} [NeZero L]

/-- The three terms of `(uwkxkisjwj0)` other than `(1-s)² (Θ 𝓑 Θ)` (band `iniTermI_U0`, `IniTermI:931`), for an abstract propagator
with row sums `≤ CR (1-u)⁻¹`: `|ΣΣ (K₁K₂ - β² Θ₁Θ₂) X| ≤ 2(1+C_A) C_R M (q 𝒯_u(|a₁-a₂|) + ρ F)`. -/
private theorem IniTermIGen_U0 (Th : Zd d L → Zd d L → ℂ) {g s u α β M q F CA CR : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 - s)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u))
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hF : 0 ≤ F) (hCA : 0 ≤ CA) (hCR : 1 ≤ CR) (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L)
    (hrowsum : ∀ a : Zd d L, ∑ b : Zd d L, ‖Th a b‖ ≤ CR * (1 - u)⁻¹)
    (hA : ∀ a₁ a₂ : Zd d L, (1 - s) * ∑ b : Zd d L, ‖Th a₁ b‖ *
        tailT d L g s (zdistInf d L (b - a₂) : ℕ) ≤ CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ))
    (a₁ a₂ : Zd d L) (X : Zd d L → Zd d L → ℂ)
    (hX : ∀ b₁ b₂, ‖X b₁ b₂‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) :
    ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (IniTermIGen_Kf Th α β a₁ b₁ * IniTermIGen_Kf Th α β a₂ b₂ -
        (β : ℂ) ^ 2 * (Th a₁ b₁ * Th a₂ b₂)) * X b₁ b₂‖ ≤
      ((2 + 2 * CA) * CR) * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + (1 - s) / (1 - u) * F) := by
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : 0 ≤ 1 - s := by linarith
  set ρ : ℝ := (1 - s) / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hs1 hu0.le
  have hid : ∀ b₁ b₂ : Zd d L, (IniTermIGen_Kf Th α β a₁ b₁ * IniTermIGen_Kf Th α β a₂ b₂ -
        (β : ℂ) ^ 2 * (Th a₁ b₁ * Th a₂ b₂)) * X b₁ b₂ =
      (if a₁ = b₁ then ((α : ℂ) * IniTermIGen_Kf Th α β a₂ b₂ * X b₁ b₂) else 0) +
        (if a₂ = b₂ then ((β : ℂ) * Th a₁ b₁ * (α : ℂ) * X b₁ b₂) else 0) := by
    intro b₁ b₂; unfold IniTermIGen_Kf; split_ifs <;> ring
  simp_rw [hid, Finset.sum_add_distrib]
  have h1 : ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (if a₁ = b₁ then ((α : ℂ) * IniTermIGen_Kf Th α β a₂ b₂ * X b₁ b₂) else 0)
      = ∑ b₂ : Zd d L, (α : ℂ) * IniTermIGen_Kf Th α β a₂ b₂ * X a₁ b₂ := by
    have : ∀ b₁ : Zd d L, ∑ b₂ : Zd d L, (if a₁ = b₁ then ((α : ℂ) * IniTermIGen_Kf Th α β a₂ b₂ * X b₁ b₂) else 0)
        = if a₁ = b₁ then ∑ b₂ : Zd d L, (α : ℂ) * IniTermIGen_Kf Th α β a₂ b₂ * X b₁ b₂ else 0 := by
      intro b₁; split_ifs <;> simp
    simp_rw [this]; rw [Finset.sum_ite_eq]; simp
  have h2 : ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (if a₂ = b₂ then ((β : ℂ) * Th a₁ b₁ * (α : ℂ) * X b₁ b₂) else 0)
      = ∑ b₁ : Zd d L, (β : ℂ) * Th a₁ b₁ * (α : ℂ) * X b₁ a₂ := by
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.sum_ite_eq]; simp
  rw [h1, h2]
  refine (norm_add_le _ _).trans ?_
  -- first sum: `ZA` with `b₁ := a₁`
  have hz := IniTermIIGen_ZA Th (g := g) (s := s) (u := u) (α := α) (β := β) (M := M) (q := q) (F := F) (CA := CA) (CR := CR)
    hs hsu hu hα0 hα1 hβ0 hβ1 hαβ hM hq hF hCA hCR hg hL1 hrowsum hA a₂ a₁
  have hf : ‖∑ b₂ : Zd d L, (α : ℂ) * IniTermIGen_Kf Th α β a₂ b₂ * X a₁ b₂‖ ≤
      (1 + CA) * CR * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F) := by
    refine (norm_sum_le _ _).trans (le_trans ?_ hz)
    refine Finset.sum_le_sum fun b₂ _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0]
    have hk := IniTermIGen_Kf_norm_le Th hα0 hβ0 a₂ b₂
    have hn := norm_nonneg (IniTermIGen_Kf Th α β a₂ b₂)
    calc α * ‖IniTermIGen_Kf Th α β a₂ b₂‖ * ‖X a₁ b₂‖
        ≤ 1 * ‖IniTermIGen_Kf Th α β a₂ b₂‖ * ‖X a₁ b₂‖ := by
          gcongr
      _ ≤ (α * (if a₂ = b₂ then 1 else 0) + β * ‖Th a₂ b₂‖) *
            (M * (q * tailT d L g s (zdistInf d L (a₁ - b₂) : ℕ) + F)) := by
          rw [one_mul]; exact mul_le_mul hk (hX a₁ b₂) (norm_nonneg _) (by positivity)
  have hs2 : ‖∑ b₁ : Zd d L, (β : ℂ) * Th a₁ b₁ * (α : ℂ) * X b₁ a₂‖ ≤
      M * (q * (CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + F * (CR * ρ)) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ b₁ : Zd d L, ‖(β : ℂ) * Th a₁ b₁ * (α : ℂ) * X b₁ a₂‖ ≤
        M * q * (β * (‖Th a₁ b₁‖ * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ))) +
          M * F * (β * ‖Th a₁ b₁‖) := by
      intro b₁
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hα0,
        Real.norm_of_nonneg hβ0]
      have hxb := hX b₁ a₂
      have hn := norm_nonneg (Th a₁ b₁)
      have hT : 0 ≤ tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
      calc β * ‖Th a₁ b₁‖ * α * ‖X b₁ a₂‖
          ≤ β * ‖Th a₁ b₁‖ * 1 * (M * (q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) + F)) := by
            gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum fun b₁ _ => hpt b₁).trans ?_
    have hsum1 : ∑ b₁ : Zd d L, M * q * (β * (‖Th a₁ b₁‖ * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ)))
        = M * q * (β * ∑ b₁ : Zd d L, (‖Th a₁ b₁‖ * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ))) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hsum2 : ∑ b₁ : Zd d L, M * F * (β * ‖Th a₁ b₁‖)
        = M * F * (β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_add_distrib, hsum1, hsum2]
    have e1 : β * ∑ b₁ : Zd d L, (‖Th a₁ b₁‖ * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ)) ≤
        CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) :=
      (mul_le_mul_of_nonneg_right hβ1 (Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _)
        (tailT_nonneg (Nat.cast_nonneg _)))).trans (hA a₁ a₂)
    have e2 : β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ ≤ CR * ρ := by
      have h4 : β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ ≤ β * (CR * (1 - u)⁻¹) := mul_le_mul_of_nonneg_left (hrowsum a₁) hβ0
      have h5 : β * (CR * (1 - u)⁻¹) ≤ CR * ρ := by
        have : β * (1 - u)⁻¹ ≤ ρ := by rw [← hαβ]; linarith
        calc β * (CR * (1 - u)⁻¹) = CR * (β * (1 - u)⁻¹) := by ring
          _ ≤ CR * ρ := mul_le_mul_of_nonneg_left this (by linarith)
      linarith
    have e3 : 0 ≤ M * q := mul_nonneg hM hq
    have e4 : 0 ≤ M * F := mul_nonneg hM hF
    nlinarith [mul_le_mul_of_nonneg_left e1 e3, mul_le_mul_of_nonneg_left e2 e4]
  have hρ1 : 0 ≤ q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := mul_nonneg hq (tailT_nonneg (Nat.cast_nonneg _))
  have hCR0 : 0 ≤ CR := by linarith
  nlinarith [hf, hs2, mul_nonneg hM hρ1, mul_nonneg (mul_nonneg hM hF) hρ0, mul_nonneg hCA (mul_nonneg hM hρ1),
    mul_nonneg (sub_nonneg.2 hCR) (mul_nonneg hM hρ1), mul_nonneg (sub_nonneg.2 hCR) (mul_nonneg (mul_nonneg hM hF) hρ0),
    mul_nonneg (sub_nonneg.2 hCR) (mul_nonneg hCA (mul_nonneg hM hρ1)), mul_nonneg hCR0 (mul_nonneg hCA (mul_nonneg hM hρ1)),
    mul_nonneg hCR0 (mul_nonneg (mul_nonneg hM hF) hρ0)]

/-- **The `ρ`-lossy bound** (band `iniTermI_bil_lossy`, `IniTermI:1021`; two applications of `(uwp2-92kj)`, the case
`ρ ≤ (log W)^{10}` of `3_5:2119`): `|ΣΣ K₁K₂ X| ≤ (1+C_A) C_R (1+C_A+C_R) M ρ (q 𝒯_u(|a₁-a₂|) + ρ F)`, `ρ = (1-s)/(1-u)`. -/
private theorem IniTermIGen_bil_lossy (Th : Zd d L → Zd d L → ℂ) {g s u α β M q F CA CR : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u)
    (hu : u < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 - s)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u))
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hF : 0 ≤ F) (hCA : 0 ≤ CA) (hCR : 1 ≤ CR) (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L)
    (hrowsum : ∀ a : Zd d L, ∑ b : Zd d L, ‖Th a b‖ ≤ CR * (1 - u)⁻¹)
    (hA : ∀ a₁ a₂ : Zd d L, (1 - s) * ∑ b : Zd d L, ‖Th a₁ b‖ *
        tailT d L g s (zdistInf d L (b - a₂) : ℕ) ≤ CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ))
    (hAu : ∀ a₁ a₂ : Zd d L, (1 - u) * ∑ b : Zd d L, ‖Th a₁ b‖ *
        tailT d L g u (zdistInf d L (b - a₂) : ℕ) ≤ CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ))
    (a₁ a₂ : Zd d L) (X : Zd d L → Zd d L → ℂ)
    (hX : ∀ b₁ b₂, ‖X b₁ b₂‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) :
    ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L, IniTermIGen_Kf Th α β a₁ b₁ * IniTermIGen_Kf Th α β a₂ b₂ * X b₁ b₂‖ ≤
      ((1 + CA) * CR * (1 + CA + CR)) * M * ((1 - s) / (1 - u) *
        (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + (1 - s) / (1 - u) * F)) := by
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : 0 ≤ 1 - s := by linarith
  set ρ : ℝ := (1 - s) / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hs1 hu0.le
  have hρ1 : 1 ≤ ρ := (one_le_div hu0).mpr (by linarith)
  have hCR0 : 0 ≤ CR := by linarith
  set C₁ : ℝ := (1 + CA) * CR with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hTn : ∀ x : Zd d L, 0 ≤ tailT d L g u (zdistInf d L x : ℕ) := fun x => tailT_nonneg (Nat.cast_nonneg _)
  set R : Zd d L → ℝ := fun b => C₁ * M * (q * tailT d L g u (zdistInf d L (b - a₂) : ℕ) + ρ * F) with hR
  have hRnn : ∀ b, 0 ≤ R b := fun b => by simp only [hR]; have := hTn (b - a₂); positivity
  -- step 1
  have hstep1 : ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L, IniTermIGen_Kf Th α β a₁ b₁ * IniTermIGen_Kf Th α β a₂ b₂ * X b₁ b₂‖
      ≤ ∑ b₁ : Zd d L, (α * (if a₁ = b₁ then 1 else 0) + β * ‖Th a₁ b₁‖) * R b₁ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₁ _ => ?_)
    have hz := IniTermIIGen_ZA Th (g := g) (s := s) (u := u) (α := α) (β := β) (M := M) (q := q) (F := F) (CA := CA) (CR := CR)
      hs hsu hu hα0 hα1 hβ0 hβ1 hαβ hM hq hF hCA hCR hg hL1 hrowsum hA a₂ b₁
    calc ‖∑ b₂ : Zd d L, IniTermIGen_Kf Th α β a₁ b₁ * IniTermIGen_Kf Th α β a₂ b₂ * X b₁ b₂‖
        ≤ ∑ b₂ : Zd d L, ‖IniTermIGen_Kf Th α β a₁ b₁‖ * (‖IniTermIGen_Kf Th α β a₂ b₂‖ * ‖X b₁ b₂‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₂ _ => ?_)
          rw [norm_mul, norm_mul]; ring_nf; exact le_rfl
      _ = ‖IniTermIGen_Kf Th α β a₁ b₁‖ * ∑ b₂ : Zd d L, ‖IniTermIGen_Kf Th α β a₂ b₂‖ * ‖X b₁ b₂‖ := by
          rw [Finset.mul_sum]
      _ ≤ (α * (if a₁ = b₁ then 1 else 0) + β * ‖Th a₁ b₁‖) * R b₁ := by
          refine mul_le_mul (IniTermIGen_Kf_norm_le Th hα0 hβ0 a₁ b₁) ?_
            (Finset.sum_nonneg fun b₂ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
          refine le_trans (Finset.sum_le_sum fun b₂ _ => mul_le_mul (IniTermIGen_Kf_norm_le Th hα0 hβ0 a₂ b₂)
            (hX b₁ b₂) (norm_nonneg _) (by positivity)) ?_
          exact hz
  -- step 2
  have hsplit : ∑ b₁ : Zd d L, (α * (if a₁ = b₁ then 1 else 0) + β * ‖Th a₁ b₁‖) * R b₁ =
      α * R a₁ + β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * R b₁ := by
    have h1 : ∀ b₁ : Zd d L, (α * (if a₁ = b₁ then 1 else 0) + β * ‖Th a₁ b₁‖) * R b₁
        = (if a₁ = b₁ then α * R b₁ else 0) + β * (‖Th a₁ b₁‖ * R b₁) := by
      intro b₁; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun b₁ _ => h1 b₁, Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.mul_sum]
    simp
  -- step 3
  have hT0 : 0 ≤ q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := mul_nonneg hq (hTn _)
  have hi : α * R a₁ ≤ C₁ * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F) :=
    (mul_le_mul_of_nonneg_right hα1 (hRnn a₁)).trans (by rw [one_mul])
  have hrow := hrowsum a₁
  have hβρ : β * (1 - u)⁻¹ ≤ ρ := by rw [← hαβ]; linarith
  have hβrow : β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ ≤ CR * ρ := by
    calc β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ ≤ β * (CR * (1 - u)⁻¹) := mul_le_mul_of_nonneg_left hrow hβ0
      _ = CR * (β * (1 - u)⁻¹) := by ring
      _ ≤ CR * ρ := mul_le_mul_of_nonneg_left hβρ hCR0
  have hii : β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * R b₁ ≤
      C₁ * M * (CA * ρ * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + ρ * F * (CR * ρ)) := by
    have e0 : ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * R b₁ =
        C₁ * M * (q * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
          + ρ * F * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖) := by
      simp only [hR, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b₁ _ => by ring
    have e1 : ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) ≤
        CA * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
      have h2 := hAu a₁ a₂
      have h3 : ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
          = (1 - u)⁻¹ * ((1 - u) * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ *
              tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) := by field_simp
      rw [h3]
      calc (1 - u)⁻¹ * ((1 - u) * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ *
              tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))
          ≤ (1 - u)⁻¹ * (CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hu0.le)
        _ = _ := by ring
    rw [e0]
    have hc : 0 ≤ C₁ * M := by positivity
    calc β * (C₁ * M * (q * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
          + ρ * F * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖))
        = C₁ * M * (q * (β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))
          + ρ * F * (β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖)) := by ring
      _ ≤ C₁ * M * (q * (CA * ρ * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + ρ * F * (CR * ρ)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hc
          · refine mul_le_mul_of_nonneg_left ?_ hq
            calc β * ∑ b₁ : Zd d L, ‖Th a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
                ≤ β * (CA * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) :=
                  mul_le_mul_of_nonneg_left e1 hβ0
              _ = CA * (β * (1 - u)⁻¹) * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by ring
              _ ≤ CA * ρ * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβρ hCA) (hTn _)
          · exact mul_le_mul_of_nonneg_left hβrow (by positivity)
      _ = _ := by ring
  refine hstep1.trans (hsplit.le.trans ((add_le_add hi hii).trans ?_))
  have hF0 : 0 ≤ ρ * F := mul_nonneg hρ0 hF
  have hC0 : 0 ≤ C₁ * M := by positivity
  have key : C₁ * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F) +
      C₁ * M * (CA * ρ * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + ρ * F * (CR * ρ)) =
      C₁ * M * ((1 + CA * ρ) * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + (ρ + CR * ρ * ρ) * F) := by ring
  rw [key]
  have : (1 + CA * ρ) * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + (ρ + CR * ρ * ρ) * F ≤
      (1 + CA + CR) * (ρ * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F)) := by
    nlinarith [mul_nonneg hCA (sub_nonneg.2 hρ1), mul_nonneg hT0 (sub_nonneg.2 hρ1), mul_nonneg hF (sub_nonneg.2 hρ1),
      mul_nonneg (mul_nonneg hF hρ0) (sub_nonneg.2 hρ1), mul_nonneg (mul_nonneg hCA hT0) (sub_nonneg.2 hρ1),
      mul_nonneg (mul_nonneg hF hCA) hρ0, mul_nonneg (mul_nonneg hF hρ0) hρ0, mul_nonneg hCR0 (mul_nonneg hF hρ0),
      mul_nonneg (mul_nonneg hCR0 hF) (mul_nonneg hρ0 hρ0), mul_nonneg hCA (mul_nonneg hT0 hρ0), mul_nonneg hCR0 (mul_nonneg hT0 hρ0),
      mul_nonneg (mul_nonneg hCA hF) (mul_nonneg hρ0 hρ0), mul_nonneg hT0 (sub_nonneg.2 hρ1),
      mul_nonneg hCR0 (mul_nonneg hT0 (sub_nonneg.2 hρ1))]
  calc C₁ * M * ((1 + CA * ρ) * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + (ρ + CR * ρ * ρ) * F)
      ≤ C₁ * M * ((1 + CA + CR) * (ρ * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F))) :=
        mul_le_mul_of_nonneg_left this hC0
    _ = _ := by rw [hC₁]; ring

end Cores

section CoreTheorems

variable {d : ℕ}

private theorem IniTermIGen_not_of_ne {σ : Fin 2 → Bool} (h : σ 0 ≠ σ 1) : σ 1 = !σ 0 := by
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all

/-- **Target 8 (a), `σ₁ = σ₂`: the short-range initial term** (`3_5:2253`, `(prop:ThfadC_short)`; band `iniTermI_core_same`,
`IniTermI:1229`) over the carrier: `|[𝒰_{s,u,σ} X]_a| ≤ C M ((λ W^{-d}) 𝒯_u(|a₁-a₂|) + W^{-D})` in regime (i)
`lam²/L² ≤ 1-u`.  The class `IniTermGen_KerFacts` is the only kernel input; the short-range field is read at `gK`, `gK² ≤ lam²`
(R1) turns it into the band shape at `g = sz.lam ≤ A 𝔡⁻¹`. -/
theorem iniTermIGen_core_same (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n →
      gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 →
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
            W ^ (-D))) →
          ∀ a, ‖Step2Gen_UN (mk sz z) n σ s u X a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) + W ^ (-D)) := by
  obtain ⟨C₆, C₈, Cs, c₀, A, hC₆, hC₈, hCs, hc₀, hA, H⟩ := hKF hd κ 𝔡 hκ h𝔡
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨C, hC, Hb⟩ := iniTermI_bil_same d hd Cs c₀ (A * 𝔡⁻¹) hCs.le hc₀
  refine ⟨C, hC, ?_⟩
  intro sz ε 𝔠 z hflow n hg hgΛ W D s u M lam hW hs hsu hu hreg hM hlam σ hσ X hX a
  obtain ⟨hU, hdec, hR1, hE1, hG⟩ := H sz ε 𝔠 z hflow
  have hu0 : 0 ≤ u := hs.trans hsu
  obtain ⟨hlamn, hgl⟩ := Step5KerGen_cmp_pos (hR1 n) hg
  have hlamΛ : sz.lam n ≤ A * 𝔡⁻¹ := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : gK sz z n ^ 2 ≤ (𝔡⁻¹) ^ 2 := by nlinarith
    have h2 := (hR1 n).2.2
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hΛ.le]
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hαβ, hrep⟩ := IniTermIIGen_UN_rep (mk sz z) n (hU n)
    (σ := σ) (fun v _ _ => by rw [hσ]) hs hsu hu
  obtain ⟨-, -, hshort⟩ := hG n hg hgΛ u hu0 hu
  have hΘ : ∀ a' b' : Zd d (sz.L n), ‖STThg (mk sz z) n (σ 0) (σ 1) u a' b'‖ ≤
      Cs * ((if a' = b' then 1 else 0) + sz.lam n ^ 2 * Real.exp (-(c₀ * ((zdistD d (sz.L n) (b' - a') : ℕ) : ℝ)))) := by
    intro a' b'
    rw [← hσ]
    refine (hshort (σ 0) a' b').trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hCs.le
    exact mul_le_mul_of_nonneg_right (hR1 n).2.1 (Real.exp_pos _).le
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d (sz.L n), ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  rw [hrep X a]
  exact Hb (sz.L n) (sz.three_le_L n) (sz.lam n) s u α β M (lam * (W ^ d)⁻¹) (W ^ (-D)) hlamn hlamΛ hsu hu hreg hα0 hα1 hβ0
    (by linarith) hM hq hF (STThg (mk sz z) n (σ 0) (σ 1) u) hΘ (a 0) (a 1) (fun b₁ b₂ => X ![b₁, b₂]) hX'

/-- The `UN`-representation and the profile data of a mixed core: the common prefix of `iniTermIGen_core_mixed` and
`iniTermIGen_core_lossy`. -/
private theorem IniTermIGen_core_data (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ (CA CR : ℝ), 0 < CA ∧ 1 ≤ CR ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ,
      0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ (s u : ℝ), 0 ≤ s → s ≤ u → u < 1 →
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
        0 < sz.lam n ∧ ∃ α β : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 - s ∧ α + β * (1 - u)⁻¹ = (1 - s) / (1 - u) ∧
          (∀ (X : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)),
            Step2Gen_UN (mk sz z) n σ s u X a = ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
              IniTermIGen_Kf (STThg (mk sz z) n (σ 0) (σ 1) u) α β (a 0) b₁ *
                IniTermIGen_Kf (STThg (mk sz z) n (σ 0) (σ 1) u) α β (a 1) b₂ * X ![b₁, b₂]) ∧
          (∀ a : Zd d (sz.L n), ∑ b, ‖STThg (mk sz z) n (σ 0) (σ 1) u a b‖ ≤ CR * (1 - u)⁻¹) ∧
          (∀ s' : ℝ, 0 ≤ s' → s' ≤ u → ∀ a₁ a₂ : Zd d (sz.L n), (1 - s') * ∑ b : Zd d (sz.L n),
              ‖STThg (mk sz z) n (σ 0) (σ 1) u a₁ b‖ * tailT d (sz.L n) (sz.lam n) s' (zdistInf d (sz.L n) (b - a₂) : ℕ) ≤
            CA * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ)) := by
  obtain ⟨C₆, C₈, Cs, c₀, A, hC₆, hC₈, hCs, hc₀, hA, H⟩ := hKF hd κ 𝔡 hκ h𝔡
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨CA, hCA, hAL⟩ := IniTermIGen_stageA d hd 𝔡⁻¹ C₆ A hΛ hC₆ hA
  refine ⟨CA, 1 + C₆, hCA, by linarith, ?_⟩
  intro sz ε 𝔠 z hflow n hg hgΛ s u hs hsu hu hreg σ hσ
  obtain ⟨hU, hdec, hR1, hE1, hG⟩ := H sz ε 𝔠 z hflow
  have hu0 : 0 ≤ u := hs.trans hsu
  have h10 : σ 1 = !σ 0 := IniTermIGen_not_of_ne hσ
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hαβ, hrep⟩ := IniTermIIGen_UN_rep (mk sz z) n (hU n)
    (σ := σ) (fun v hv0 hv1 => by
      have := hE1 n v hv0.le hv1 (σ 0); rw [← h10] at this; exact this.symm) hs hsu hu
  refine ⟨(Step5KerGen_cmp_pos (hR1 n) hg).1, α, β, hα0, hα1, hβ0, hβ1, hαβ, fun X a => ?_, fun a => ?_, fun s' hs' hs'u a₁ a₂ => ?_⟩
  · rw [hrep X a]; rfl
  · exact IniTermIIGen_row_le (mk sz z) n (hU n) (σ 0) (σ 1) hu0 hu a ((hdec n hg hgΛ (σ 0) (σ 1) u hu0 hu).2 a)
  · exact hAL sz (mk sz z) (gK sz z) hdec hR1 n (hU n) (σ 0) (σ 1) s' u hg hgΛ hs' hs'u hu hreg a₁ a₂

/-- **Target 8 (a), `σ₁ ≠ σ₂`, large part** (`(uwkxkisjwj0)`, `3_5:2086-2092`; band `iniTermI_core_mixed`, `IniTermI:1143`): the first
three terms of the expansion of `𝒰_{s,u,σ} X` are `≤ C M (λ W^{-d} 𝒯_u + ρ W^{-D})` and the fourth is `c (1-s)² (Θ X Θ)`,
`c = ((u-s)/(u(1-s)))² ∈ [0,1]`, with `Θ = Θ^{(σ₀σ₁)}_u`. -/
theorem iniTermIGen_core_mixed (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n →
      gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 →
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
            W ^ (-D))) →
          ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ a, ‖Step2Gen_UN (mk sz z) n σ s u X a - (c : ℂ) * ((((1 - s) ^ 2 : ℝ) : ℂ) *
              ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n), STThg (mk sz z) n (σ 0) (σ 1) u (a 0) b₁ *
                STThg (mk sz z) n (σ 0) (σ 1) u (a 1) b₂ * X ![b₁, b₂])‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) +
              (1 - s) / (1 - u) * W ^ (-D)) := by
  obtain ⟨CA, CR, hCA, hCR, Hd⟩ := IniTermIGen_core_data d Flow mk gK hKF hd κ 𝔡 hκ h𝔡
  refine ⟨(2 + 2 * CA) * CR, by positivity, ?_⟩
  intro sz ε 𝔠 z hflow n hg hgΛ W D s u M lam hW hs hsu hu hreg hM hlam σ hσ X hX
  obtain ⟨hlamn, α, β, hα0, hα1, hβ0, hβ1, hαβ, hfun, hrow, hA⟩ := Hd sz ε 𝔠 z hflow n hg hgΛ s u hs hsu hu hreg σ hσ
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hs1 : 0 < 1 - s := by linarith
  refine ⟨β ^ 2 / (1 - s) ^ 2, by positivity, ?_, fun a => ?_⟩
  · rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ hβ0 hβ1 2
  have hid : Step2Gen_UN (mk sz z) n σ s u X a - ((β ^ 2 / (1 - s) ^ 2 : ℝ) : ℂ) * ((((1 - s) ^ 2 : ℝ) : ℂ) *
      ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n), STThg (mk sz z) n (σ 0) (σ 1) u (a 0) b₁ *
        STThg (mk sz z) n (σ 0) (σ 1) u (a 1) b₂ * X ![b₁, b₂]) =
      ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
        (IniTermIGen_Kf (STThg (mk sz z) n (σ 0) (σ 1) u) α β (a 0) b₁ *
          IniTermIGen_Kf (STThg (mk sz z) n (σ 0) (σ 1) u) α β (a 1) b₂ -
          (β : ℂ) ^ 2 * (STThg (mk sz z) n (σ 0) (σ 1) u (a 0) b₁ * STThg (mk sz z) n (σ 0) (σ 1) u (a 1) b₂)) * X ![b₁, b₂] := by
    have hcβ : ((β ^ 2 / (1 - s) ^ 2 : ℝ) : ℂ) * (((1 - s) ^ 2 : ℝ) : ℂ) = (β : ℂ) ^ 2 := by
      have : (1 - (s : ℂ)) ≠ 0 := by exact_mod_cast hs1.ne'
      push_cast; field_simp
    rw [hfun X a, ← mul_assoc, hcβ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b₂ _ => by ring
  rw [hid]
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d (sz.L n), ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  exact IniTermIGen_U0 (STThg (mk sz z) n (σ 0) (σ 1) u) (g := sz.lam n) (M := M) (q := lam * (W ^ d)⁻¹) (F := W ^ (-D))
    (CA := CA) (CR := CR) hs hsu hu hα0 hα1 hβ0 hβ1 hαβ hM hq hF hCA.le hCR hlamn.le hL1 hrow (fun a₁ a₂ => hA s hs hsu a₁ a₂)
    (a 0) (a 1) (fun b₁ b₂ => X ![b₁, b₂]) hX'

/-- **Target 8 (a), `σ₁ ≠ σ₂`, `ρ`-lossy** (`ρ ≤ (log W)^{10}`, `3_5:2119`, "two applications of `(uwp2-92kj)`"; band
`iniTermI_core_lossy`, `IniTermI:1191`). -/
theorem iniTermIGen_core_lossy (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n →
      gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 →
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
            W ^ (-D))) →
          ∀ a, ‖Step2Gen_UN (mk sz z) n σ s u X a‖ ≤
            C * M * ((1 - s) / (1 - u) * (lam * (W ^ d)⁻¹ *
              tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D))) := by
  obtain ⟨CA, CR, hCA, hCR, Hd⟩ := IniTermIGen_core_data d Flow mk gK hKF hd κ 𝔡 hκ h𝔡
  refine ⟨(1 + CA) * CR * (1 + CA + CR), by positivity, ?_⟩
  intro sz ε 𝔠 z hflow n hg hgΛ W D s u M lam hW hs hsu hu hreg hM hlam σ hσ X hX a
  obtain ⟨hlamn, α, β, hα0, hα1, hβ0, hβ1, hαβ, hfun, hrow, hA⟩ := Hd sz ε 𝔠 z hflow n hg hgΛ s u hs hsu hu hreg σ hσ
  have hu0 : 0 ≤ u := hs.trans hsu
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  rw [hfun X a]
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d (sz.L n), ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  exact IniTermIGen_bil_lossy (STThg (mk sz z) n (σ 0) (σ 1) u) (g := sz.lam n) (M := M) (q := lam * (W ^ d)⁻¹) (F := W ^ (-D))
    (CA := CA) (CR := CR) hs hsu hu hα0 hα1 hβ0 hβ1 hαβ hM hq hF hCA.le hCR hlamn.le hL1 hrow
    (fun a₁ a₂ => hA s hs hsu a₁ a₂) (fun a₁ a₂ => hA u hu0 le_rfl a₁ a₂) (a 0) (a 1) (fun b₁ b₂ => X ![b₁, b₂]) hX'

end CoreTheorems

/-! ## 3. Target 8 (c): `(1-s)² (Θ 𝓑 Θ) = f^{near} + f^{far} + g`, the mixed bound and the tail bound -/

section Mixed

variable {d L : ℕ} [NeZero L]

/-- `(1-s)² Σ_{b₁,b₂} Θ_{a₁b₁} Θ_{a₂b₂} X(b₁,b₂)`: the term `(iksjuwjx)` of `3_5:2096` (band `iniTermI_Sfull`, `IniTermI:1137`). -/
private def IniTermIGen_Sfull (Th : Zd d L → Zd d L → ℂ) (s : ℝ) (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, Th (a 0) b₁ * Th (a 1) b₂ * X ![b₁, b₂]

/-- `g_a` of `3_5:2098`, before the Ward identity (band `iniTermI_Gward`, `IniTermI:1298`). -/
private def IniTermIGen_Gward (Th : Zd d L → Zd d L → ℂ) (s : ℝ) (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ : Zd d L, Th (a 0) b₁ * Th b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂]

/-- `(1-s)² (Θ 𝓑 Θ) = f^{near} + f^{far} + g` (`3_5:2130-2135`; band `iniTermI_Sfull_decomp`, `IniTermI:1302`), for a symmetric `Th`. -/
private theorem IniTermIGen_Sfull_decomp (Th : Zd d L → Zd d L → ℂ) (hsymm : ∀ x y, Th x y = Th y x) (s : ℝ)
    (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) (P : Zd d L → Prop) [DecidablePred P] :
    IniTermIGen_Sfull Th s X a =
      CltFarUGen_fSum Th s X a (fun b => ¬ P b) + CltFarUGen_fSum Th s X a P + IniTermIGen_Gward Th s X a := by
  unfold IniTermIGen_Sfull CltFarUGen_fSum IniTermIGen_Gward
  have hb : ∀ b₁ : Zd d L, ∑ b₂ : Zd d L, Th (a 0) b₁ * Th (a 1) b₂ * X ![b₁, b₂] =
      (∑ b₂ : Zd d L, Th (a 0) b₁ * X ![b₁, b₂] * (Th b₂ (a 1) - Th b₁ (a 1))) +
      Th (a 0) b₁ * Th b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂] := by
    intro b₁
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    rw [hsymm (a 1) b₂]; ring
  have hsplit := Finset.sum_filter_not_add_sum_filter (Finset.univ : Finset (Zd d L)) P
    (fun b₁ => ∑ b₂ : Zd d L, Th (a 0) b₁ * X ![b₁, b₂] * (Th b₂ (a 1) - Th b₁ (a 1)))
  rw [Finset.sum_congr rfl fun b₁ _ => hb b₁, Finset.sum_add_distrib, ← hsplit]
  ring

/-- `|a₁-a₂| > 2 r₁ + Y₀` forces, for every pair of labels `(b₁,b₂)`, `|b₁-a₁| > r₁` or `|b₂-a₂| > r₁` (decay of `Θ`) or
`|b₁-b₂| > Y₀` (decay of `𝓑`): `|S| ≤ (1-s)² N² (2 E₀ T_m X_m + T_m² X_t)`. -/
private theorem IniTermIGen_tail (Th : Zd d L → Zd d L → ℂ) {s Tm Xm Xt E₀ r₁ Y₀ : ℝ} (hTm : 0 ≤ Tm) (hXm : 0 ≤ Xm) (hXt : 0 ≤ Xt) (hE₀ : 0 ≤ E₀)
    (hT : ∀ x y : Zd d L, ‖Th x y‖ ≤ Tm)
    (hTd : ∀ x y : Zd d L, r₁ < ((zdistInf d L (y - x) : ℕ) : ℝ) → ‖Th x y‖ ≤ E₀)
    (X : (Fin 2 → Zd d L) → ℂ) (hX : ∀ b, ‖X b‖ ≤ Xm)
    (hXd : ∀ b, Y₀ < ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) → ‖X b‖ ≤ Xt) (a : Fin 2 → Zd d L)
    (hr : 2 * r₁ + Y₀ < ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ)) :
    ‖IniTermIGen_Sfull Th s X a‖ ≤ (1 - s) ^ 2 * ((Fintype.card (Zd d L) : ℝ) ^ 2 * (2 * E₀ * Tm * Xm + Tm ^ 2 * Xt)) := by
  unfold IniTermIGen_Sfull
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hpt : ∀ b₁ b₂ : Zd d L, ‖Th (a 0) b₁ * Th (a 1) b₂ * X ![b₁, b₂]‖ ≤
      2 * E₀ * Tm * Xm + Tm ^ 2 * Xt := by
    intro b₁ b₂
    rw [norm_mul, norm_mul]
    have h1 := hT (a 0) b₁
    have h2 := hT (a 1) b₂
    have h3 := hX ![b₁, b₂]
    have n1 := norm_nonneg (Th (a 0) b₁)
    have n2 := norm_nonneg (Th (a 1) b₂)
    have n3 := norm_nonneg (X ![b₁, b₂])
    have htri : ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ≤ ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) +
        ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a 1) : ℕ) : ℝ) := by
      exact_mod_cast iniTermI_tri (a 0) (a 1) b₁ b₂
    by_cases c1 : r₁ < ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ)
    · have := hTd (a 0) b₁ c1
      calc ‖Th (a 0) b₁‖ * ‖Th (a 1) b₂‖ * ‖X ![b₁, b₂]‖ ≤ E₀ * Tm * Xm := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hE₀ hTm) hXm, mul_nonneg (sq_nonneg Tm) hXt]
    by_cases c2 : r₁ < ((zdistInf d L (b₂ - a 1) : ℕ) : ℝ)
    · have := hTd (a 1) b₂ c2
      calc ‖Th (a 0) b₁‖ * ‖Th (a 1) b₂‖ * ‖X ![b₁, b₂]‖ ≤ Tm * E₀ * Xm := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hE₀ hTm) hXm, mul_nonneg (sq_nonneg Tm) hXt]
    have c3 : Y₀ < ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) := by
      by_contra hc
      push Not at c1 c2 hc
      linarith
    have := hXd ![b₁, b₂] (by simpa using c3)
    calc ‖Th (a 0) b₁‖ * ‖Th (a 1) b₂‖ * ‖X ![b₁, b₂]‖ ≤ Tm * Tm * Xt := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hE₀ hTm) hXm, mul_nonneg (sq_nonneg Tm) hXt]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun b₁ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₂ _ => hpt b₁ b₂)).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact le_of_eq (by ring)

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **The mixed bound** (`(uwkxkisjwj0)` and `(eq:boundga)`, `(iksjuwjx3)`, `3_5:2086-2171`; band `iniTermI_mixed_bound`,
`IniTermI:2254`) over an abstract propagator `Th` (symmetric, `|Th| ≤ C_θ (g²)⁻¹ (|x-y|+1)^{-(d-2)}`, entries `≤ C_R (1-u)⁻¹`, the
convolution bound `hv`): from the core `‖Uv - c (1-s)² (Th X Th)‖ ≤ C₁ M (…)` (`hU`), for `σ₁ ≠ σ₂`,
`|Uv| ≤ |f^{far}| + K (M (λ W^{-d} 𝒯_u + ρ F) + M q g^{-2} (log W)^{14} P + [floor] + ρ Y₀ 𝒯_u)`; the profile bound on `X`, the Ward
sum `|Σ_{b₂} X| ≤ Y₀/(1-s)` and nothing else enter. -/
private theorem IniTermIGen_mixed_bound (hd : 3 ≤ d) (hL : 3 ≤ L) (Th : Zd d L → Zd d L → ℂ)
    {g W D s u M lam lW Y₀ C₁ Cθ Cv CR K c : ℝ} {Uv : ℂ} (hg : 0 < g) (hW : 0 < W) (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) (hregs1 : 1 - s ≤ g ^ 2) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hlW : 1 ≤ lW) (hY : 0 ≤ Y₀)
    (hC₁ : 0 ≤ C₁) (hCθ : 0 ≤ Cθ) (hCv : 0 ≤ Cv) (hCR : 1 ≤ CR)
    (hK : C₁ + 2 * (iniTermI_CW d + iniTermI_CB d) * iniTermI_CW d * (1 + 2 ^ (d - 1)) * Cθ ^ 2 +
      2 * Cθ * (1 + 2 ^ (d - 1)) * CR + Cv ≤ K)
    (hsymm : ∀ x y, Th x y = Th y x)
    (hT1 : ∀ x y, ‖Th x y‖ ≤ (Cθ * (g ^ 2)⁻¹) * iniTermI_PI d L (x - y))
    (hTm' : ∀ x y, ‖Th x y‖ ≤ CR * (1 - u)⁻¹)
    (hv : ∀ a₀ a₁ : Zd d L, ∑ b : Zd d L, ‖Th a₀ b‖ * ‖Th b a₁‖ ≤
      Cv * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a₀ - a₁) : ℕ))
    (X : (Fin 2 → Zd d L) → ℂ)
    (hX : ∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D)))
    (hXY : ∀ b₁ : Zd d L, ‖∑ b₂ : Zd d L, X ![b₁, b₂]‖ ≤ Y₀ / (1 - s))
    (a : Fin 2 → Zd d L) (P : Zd d L → Prop) [DecidablePred P]
    (hP : ∀ b₁, P b₁ ↔ (lW ^ 4 * ellT L g s < ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) ∧
      lW ^ 4 * ellT L g s < ((zdistInf d L (b₁ - a 1) : ℕ) : ℝ)))
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hU : ‖Uv - (c : ℂ) * IniTermIGen_Sfull Th s X a‖ ≤ C₁ * M *
      (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D))) :
    ‖Uv‖ ≤ ‖CltFarUGen_fSum Th s X a P‖ + K *
      (M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) +
        M * (lam * (W ^ d)⁻¹) * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (a 0 - a 1) +
        M * (Fintype.card (Zd d L) : ℝ) ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ *
          (W ^ (-D) + lam * (W ^ d)⁻¹ * (g ^ 2)⁻¹ * Real.exp (-Real.sqrt (lW ^ 3))) +
        (1 - s) / (1 - u) * Y₀ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ)) := by
  set c₀ : ℝ := 1 + 2 ^ (d - 1) with hc₀
  have hc₀1 : 1 ≤ c₀ := by have : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
                           linarith
  set Kn : ℝ := 2 * (iniTermI_CW d + iniTermI_CB d) * iniTermI_CW d with hKn
  have hKn0 : 0 ≤ Kn := by
    have := iniTermI_CW_nonneg d; have := iniTermI_CB_nonneg d; rw [hKn]; positivity
  have hs1 : s < 1 := by linarith
  have hKterm1 : 0 ≤ Kn * c₀ * Cθ ^ 2 := by positivity
  have hKterm2 : 0 ≤ 2 * Cθ * c₀ * CR := by positivity
  have hu0 : 0 ≤ u := hs.trans hsu
  have hu1 : 0 < 1 - u := by linarith
  have hs1' : 0 < 1 - s := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hregs : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - s := hreg.trans (by linarith)
  have hg2 : 0 < g ^ 2 := by positivity
  -- `ℓ_s`
  have hℓ : ellT L g s = g / Real.sqrt (1 - s) := iniTermI_ellT_eq hg hs1 hregs1 hregs (by linarith)
  set ℓs : ℝ := ellT L g s with hℓdef
  have hℓ1 : 1 ≤ ℓs := one_le_ellT hL1
  have hℓsq : (1 - s) * ℓs ^ 2 = g ^ 2 := by
    rw [hℓ, div_pow, Real.sq_sqrt hs1'.le]; field_simp
  set R : ℝ := lW ^ 3 * ℓs with hR
  set R' : ℝ := lW ^ 4 * ℓs with hR'
  have hlW3 : 1 ≤ lW ^ 3 := one_le_pow₀ hlW
  have hlW4 : 1 ≤ lW ^ 4 := one_le_pow₀ hlW
  have hR1 : 1 ≤ R := by nlinarith
  have hR'1 : 1 ≤ R' := by nlinarith
  have hRR : (1 - s) ^ 2 * (R ^ 2 * R' ^ 2) = lW ^ 14 * (g ^ 2) ^ 2 := by
    have : (1 - s) ^ 2 * (R ^ 2 * R' ^ 2) = lW ^ 14 * ((1 - s) * ℓs ^ 2) ^ 2 := by rw [hR, hR']; ring
    rw [this, hℓsq]
  set q : ℝ := lam * (W ^ d)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  set E₃ : ℝ := Real.exp (-Real.sqrt (lW ^ 3)) with hE₃
  have hE₃0 : 0 ≤ E₃ := (Real.exp_pos _).le
  set M₁ : ℝ := M * q * (c₀ * (g ^ 2)⁻¹) with hM₁
  set M₄ : ℝ := M * (W ^ (-D) + q * (c₀ * ((g ^ 2)⁻¹ * E₃))) with hM₄
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₄0 : 0 ≤ M₄ := by positivity
  -- the profile of `X`
  have hXn : ∀ b₁ b₂ : Zd d L, ‖X ![b₁, b₂]‖ ≤
      (if ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R then M₁ * iniTermI_PI d L (b₁ - b₂) else 0) + M₄ := by
    intro b₁ b₂
    have hx : ‖X ![b₁, b₂]‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + W ^ (-D)) := by
      simpa using hX ![b₁, b₂]
    have ht := iniTermI_tailT_le_PI hd hL1 hs1 hregs (b₁ - b₂)
    have hPI0 := iniTermI_PI_nonneg (d := d) (L := L) (b₁ - b₂)
    have hPI1 := iniTermI_PI_le_one (d := d) (L := L) (b₁ - b₂)
    have hinv : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have hexp1 : Real.exp (-Real.sqrt (((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) / ellT L g s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := Real.sqrt_nonneg (((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) / ellT L g s); linarith)
    split_ifs with hle
    · have : tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) ≤ c₀ * ((g ^ 2)⁻¹ * iniTermI_PI d L (b₁ - b₂)) := by
        refine ht.trans ?_
        calc _ ≤ c₀ * ((g ^ 2 + (1 - s))⁻¹ * iniTermI_PI d L (b₁ - b₂)) * 1 :=
              mul_le_mul_of_nonneg_left hexp1 (by positivity)
          _ = c₀ * ((g ^ 2 + (1 - s))⁻¹ * iniTermI_PI d L (b₁ - b₂)) := mul_one _
          _ ≤ _ := by gcongr
      calc ‖X ![b₁, b₂]‖ ≤ M * (q * (c₀ * ((g ^ 2)⁻¹ * iniTermI_PI d L (b₁ - b₂))) + W ^ (-D)) :=
            hx.trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left this hq0) le_rfl) hM)
        _ ≤ _ := by
          have h1 : 0 ≤ M * (q * (c₀ * ((g ^ 2)⁻¹ * E₃))) := by positivity
          have e : M * (q * (c₀ * ((g ^ 2)⁻¹ * iniTermI_PI d L (b₁ - b₂))) + W ^ (-D)) =
              M₁ * iniTermI_PI d L (b₁ - b₂) + M * W ^ (-D) := by simp only [hM₁]; ring
          have e' : M₄ = M * W ^ (-D) + M * (q * (c₀ * ((g ^ 2)⁻¹ * E₃))) := by simp only [hM₄]; ring
          rw [e]; linarith
    · push Not at hle
      have hy : lW ^ 3 ≤ ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) / ellT L g s := by
        rw [le_div_iff₀ (by linarith)]; linarith
      have hexp : Real.exp (-Real.sqrt (((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) / ellT L g s)) ≤ E₃ :=
        Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt hy))
      have : tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) ≤ c₀ * ((g ^ 2)⁻¹ * E₃) := by
        refine ht.trans ?_
        calc _ ≤ c₀ * ((g ^ 2 + (1 - s))⁻¹ * iniTermI_PI d L (b₁ - b₂)) * E₃ :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ c₀ * ((g ^ 2)⁻¹ * 1) * E₃ := by gcongr
          _ = _ := by ring
      calc ‖X ![b₁, b₂]‖ ≤ M * (q * (c₀ * ((g ^ 2)⁻¹ * E₃)) + W ^ (-D)) :=
            hx.trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left this hq0) le_rfl) hM)
        _ = 0 + M₄ := by simp only [hM₄]; ring
        _ ≤ _ := by simp
  -- the near part
  have hT₁0 : 0 ≤ Cθ * (g ^ 2)⁻¹ := by positivity
  have hTm0 : 0 ≤ CR * (1 - u)⁻¹ := by have := inv_nonneg.2 hu1.le; positivity
  have hQ : ∀ b₁, ¬ P b₁ → ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) ≤ R' ∨ ((zdistInf d L (b₁ - a 1) : ℕ) : ℝ) ≤ R' := by
    intro b₁ hn
    rw [hP] at hn
    by_contra hc
    rw [not_or] at hc
    exact hn ⟨not_le.1 hc.1, not_le.1 hc.2⟩
  have hnear := iniTermI_near hd hR1 hR'1 hT₁0 hTm0 hM₁0 hM₄0 (fun x y => Th x y) hT1 hTm'
    (fun b₁ b₂ => X ![b₁, b₂]) hXn (a 0) (a 1) (fun b => ¬ P b) hQ
  have hfN : ‖CltFarUGen_fSum Th s X a (fun b => ¬ P b)‖ ≤
      Kn * c₀ * Cθ ^ 2 * (M * q * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (a 0 - a 1)) +
        2 * Cθ * c₀ * CR * (M * (Fintype.card (Zd d L) : ℝ) ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ *
          (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃)) := by
    unfold CltFarUGen_fSum
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1s : (1 - s) ^ 2 ≤ 1 := by nlinarith
    have hP0 := iniTermI_PI_nonneg (d := d) (L := L) (a 0 - a 1)
    set Nd : ℝ := (Fintype.card (Zd d L) : ℝ) with hNd
    have hNd0 : 0 ≤ Nd := Nat.cast_nonneg _
    calc (1 - s) ^ 2 * ‖∑ b₁ ∈ Finset.univ.filter (fun b => ¬ P b), ∑ b₂ : Zd d L,
          Th (a 0) b₁ * X ![b₁, b₂] * (Th b₂ (a 1) - Th b₁ (a 1))‖
        ≤ (1 - s) ^ 2 * (Kn * M₁ * (Cθ * (g ^ 2)⁻¹) ^ 2 * (R ^ 2 * R' ^ 2) * iniTermI_PI d L (a 0 - a 1) +
            2 * Nd ^ 2 * (Cθ * (g ^ 2)⁻¹) * (CR * (1 - u)⁻¹) * M₄) :=
          mul_le_mul_of_nonneg_left hnear (sq_nonneg _)
      _ = Kn * M₁ * (Cθ * (g ^ 2)⁻¹) ^ 2 * ((1 - s) ^ 2 * (R ^ 2 * R' ^ 2)) * iniTermI_PI d L (a 0 - a 1) +
            (1 - s) ^ 2 * (2 * Nd ^ 2 * (Cθ * (g ^ 2)⁻¹) * (CR * (1 - u)⁻¹) * M₄) := by ring
      _ ≤ Kn * c₀ * Cθ ^ 2 * (M * q * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (a 0 - a 1)) +
            1 * (2 * Cθ * c₀ * CR * (M * Nd ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃))) := by
          refine add_le_add ?_ ?_
          · rw [hRR]
            have : Kn * M₁ * (Cθ * (g ^ 2)⁻¹) ^ 2 * (lW ^ 14 * (g ^ 2) ^ 2) = Kn * c₀ * Cθ ^ 2 * (M * q * (g ^ 2)⁻¹ * lW ^ 14) := by
              simp only [hM₁]; field_simp
            refine le_of_eq ?_
            calc Kn * M₁ * (Cθ * (g ^ 2)⁻¹) ^ 2 * (lW ^ 14 * (g ^ 2) ^ 2) * iniTermI_PI d L (a 0 - a 1)
                = Kn * c₀ * Cθ ^ 2 * (M * q * (g ^ 2)⁻¹ * lW ^ 14) * iniTermI_PI d L (a 0 - a 1) := by rw [this]
              _ = _ := by ring
          · refine mul_le_mul h1s ?_ (by positivity) zero_le_one
            have : M₄ ≤ c₀ * (M * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃)) := by
              simp only [hM₄]
              have h0 : 0 ≤ M * (W ^ (-D)) := by positivity
              have e : c₀ * (M * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃)) - M * (W ^ (-D) + q * (c₀ * ((g ^ 2)⁻¹ * E₃))) =
                  (c₀ - 1) * (M * W ^ (-D)) := by ring
              have := mul_nonneg (sub_nonneg.2 hc₀1) h0
              linarith
            calc 2 * Nd ^ 2 * (Cθ * (g ^ 2)⁻¹) * (CR * (1 - u)⁻¹) * M₄
                ≤ 2 * Nd ^ 2 * (Cθ * (g ^ 2)⁻¹) * (CR * (1 - u)⁻¹) * (c₀ * (M * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃))) :=
                  mul_le_mul_of_nonneg_left this (by positivity)
              _ = _ := by ring
      _ = _ := by rw [one_mul]
  -- the Ward term
  have hG : ‖IniTermIGen_Gward Th s X a‖ ≤ Cv * ((1 - s) / (1 - u) * Y₀ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ)) := by
    unfold IniTermIGen_Gward
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have hv := hv (a 0) (a 1)
    have hsum : ‖∑ b₁ : Zd d L, Th (a 0) b₁ * Th b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂]‖ ≤
        Y₀ / (1 - s) * (Cv * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b₁ : Zd d L, ‖Th (a 0) b₁ * Th b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂]‖
          ≤ ∑ b₁ : Zd d L, (‖Th (a 0) b₁‖ * ‖Th b₁ (a 1)‖) * (Y₀ / (1 - s)) :=
            Finset.sum_le_sum fun b₁ _ => by
              rw [norm_mul, norm_mul]
              exact mul_le_mul_of_nonneg_left (hXY b₁) (by positivity)
        _ = (∑ b₁ : Zd d L, ‖Th (a 0) b₁‖ * ‖Th b₁ (a 1)‖) * (Y₀ / (1 - s)) := by
            rw [Finset.sum_mul]
        _ ≤ (Cv * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ)) * (Y₀ / (1 - s)) :=
            mul_le_mul_of_nonneg_right hv (by positivity)
        _ = _ := by ring
    calc (1 - s) ^ 2 * ‖∑ b₁ : Zd d L, Th (a 0) b₁ * Th b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂]‖
        ≤ (1 - s) ^ 2 * (Y₀ / (1 - s) * (Cv * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ))) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by field_simp
  -- assembly
  have hdec := IniTermIGen_Sfull_decomp Th hsymm s X a P
  have hSfull : ‖IniTermIGen_Sfull Th s X a‖ ≤ ‖CltFarUGen_fSum Th s X a P‖ +
      (‖CltFarUGen_fSum Th s X a (fun b => ¬ P b)‖ + ‖IniTermIGen_Gward Th s X a‖) := by
    rw [hdec]
    calc _ ≤ ‖CltFarUGen_fSum Th s X a (fun b => ¬ P b) + CltFarUGen_fSum Th s X a P‖ +
          ‖IniTermIGen_Gward Th s X a‖ := norm_add_le _ _
      _ ≤ (‖CltFarUGen_fSum Th s X a (fun b => ¬ P b)‖ + ‖CltFarUGen_fSum Th s X a P‖) +
          ‖IniTermIGen_Gward Th s X a‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by ring
  have hcS : ‖(c : ℂ) * IniTermIGen_Sfull Th s X a‖ ≤ ‖IniTermIGen_Sfull Th s X a‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
    exact mul_le_of_le_one_left (norm_nonneg _) hc1
  have hsub := norm_sub_norm_le (Uv) ((c : ℂ) * IniTermIGen_Sfull Th s X a)
  set T₁' : ℝ := M * (q * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) with hT₁'
  set T₂' : ℝ := M * q * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (a 0 - a 1) with hT₂'
  set T₃' : ℝ := M * (Fintype.card (Zd d L) : ℝ) ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃) with hT₃'
  set T₄' : ℝ := (1 - s) / (1 - u) * Y₀ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) with hT₄'
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg hs1'.le hu1.le
  have hTu0 : 0 ≤ tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
  have hP0 := iniTermI_PI_nonneg (d := d) (L := L) (a 0 - a 1)
  have h1 : 0 ≤ T₁' := by simp only [hT₁']; positivity
  have h2 : 0 ≤ T₂' := by simp only [hT₂']; positivity
  have h3 : 0 ≤ T₃' := by simp only [hT₃']; positivity
  have h4 : 0 ≤ T₄' := by simp only [hT₄']; positivity
  have hKc : 0 ≤ Kn * c₀ * Cθ ^ 2 := by positivity
  have hCθc : 0 ≤ 2 * Cθ * c₀ * CR := by positivity
  calc ‖Uv‖
      ≤ ‖Uv - (c : ℂ) * IniTermIGen_Sfull Th s X a‖ + ‖(c : ℂ) * IniTermIGen_Sfull Th s X a‖ := by
        linarith
    _ ≤ C₁ * T₁' + (‖CltFarUGen_fSum Th s X a P‖ +
          (Kn * c₀ * Cθ ^ 2 * T₂' + 2 * Cθ * c₀ * CR * T₃' + Cv * T₄')) := by
        have := hU
        have e : C₁ * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) +
            (1 - s) / (1 - u) * W ^ (-D)) = C₁ * T₁' := by simp only [hT₁', hq]; ring
        rw [e] at this
        linarith
    _ ≤ _ := by
        have hK1 : C₁ ≤ K := by linarith
        have hK2 : Kn * c₀ * Cθ ^ 2 ≤ K := by linarith
        have hK3 : 2 * Cθ * c₀ * CR ≤ K := by linarith
        have hK4 : Cv ≤ K := by linarith
        have e1 := mul_le_mul_of_nonneg_right hK1 h1
        have e2 := mul_le_mul_of_nonneg_right hK2 h2
        have e3 := mul_le_mul_of_nonneg_right hK3 h3
        have e4 := mul_le_mul_of_nonneg_right hK4 h4
        have e : K * (T₁' + T₂' + T₃' + T₄') = K * T₁' + K * T₂' + K * T₃' + K * T₄' := by ring
        have e5 : Kn * c₀ * Cθ ^ 2 * T₂' + 2 * Cθ * c₀ * CR * T₃' + Cv * T₄' + C₁ * T₁' ≤ K * (T₁' + T₂' + T₃' + T₄') := by
          rw [e]; linarith
        linarith
set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **Outside the window** (`(eq:ells_to_ellt2)`, `3_5:2119-2128`; band `iniTermI_mixed_tail`, `IniTermI:2489`) over an abstract
propagator `Th` (entries `≤ C_R (1-u)⁻¹`, exponential decay `hTd` beyond `r₁`): if `|a₁-a₂| > 2 r₁ + Y_w`, every pair of labels
`(b₁,b₂)` has `Θ` or `𝓑` exponentially small (`prop:ThfadC`, `Eq:Gdecay+IND`), so
`|Uv| ≤ C₁ M (q 𝒯_u + ρ F) + C_R² N² (1-u)⁻² (2 C_f e^{-c r₁/ℓ_u} X_m + X_t)`, from the core `hU`. -/
private theorem IniTermIGen_mixed_tail (hd : 3 ≤ d) (hL : 3 ≤ L) (Th : Zd d L → Zd d L → ℂ)
    {g W D s u M lam r₁ Yw C₁ Cf cf CR c : ℝ} {Uv : ℂ} (hg : 0 < g) (hW : 0 < W) (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hCf : 0 ≤ Cf) (hCR : 1 ≤ CR)
    (hTm' : ∀ x y, ‖Th x y‖ ≤ CR * (1 - u)⁻¹)
    (hTd : ∀ x y : Zd d L, r₁ < ((zdistInf d L (y - x) : ℕ) : ℝ) →
      ‖Th x y‖ ≤ Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u)))
    (X : (Fin 2 → Zd d L) → ℂ)
    (hX : ∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D)))
    (a : Fin 2 → Zd d L) (hr : 2 * r₁ + Yw < ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ))
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hU : ‖Uv - (c : ℂ) * IniTermIGen_Sfull Th s X a‖ ≤ C₁ * M *
      (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D))) :
    ‖Uv‖ ≤ C₁ * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) +
      CR ^ 2 * ((Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
        (2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (lam * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * (g ^ 2)⁻¹) + W ^ (-D))) +
          M * (lam * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ *
            Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) := by
  have hs1 : s < 1 := by linarith
  have hu0 : 0 ≤ u := hs.trans hsu
  have hu1 : 0 < 1 - u := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hregs : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - s := hreg.trans (by linarith)
  have hg2 : 0 < g ^ 2 := by positivity
  set c₀ : ℝ := 1 + 2 ^ (d - 1) with hc₀
  set q : ℝ := lam * (W ^ d)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  -- bounds for `X`
  have hTs : ∀ y : Zd d L, tailT d L g s (zdistInf d L y : ℕ) ≤ c₀ * ((g ^ 2)⁻¹ * 1) := by
    intro y
    refine (iniTermI_tailT_le_PI' hd hL1 hs1 hregs y).trans ?_
    have hinv : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have := iniTermI_PI_le_one (d := d) (L := L) y
    have := iniTermI_PI_nonneg (d := d) (L := L) y
    gcongr
  have hXm : ∀ b, ‖X b‖ ≤ M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D)) := fun b =>
    (hX b).trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
      (by simpa using hTs (b 0 - b 1)) hq0) le_rfl) hM)
  have hXt : ∀ b, Yw < ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) → ‖X b‖ ≤
      M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)) := by
    intro b hb
    have hℓ0 : 0 < ellT L g s := ellT_pos hL1
    have ht := iniTermI_tailT_le_PI hd hL1 hs1 hregs (b 0 - b 1)
    have hinv : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have h1 := iniTermI_PI_le_one (d := d) (L := L) (b 0 - b 1)
    have h2 := iniTermI_PI_nonneg (d := d) (L := L) (b 0 - b 1)
    have hy : Yw / ellT L g s ≤ ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) / ellT L g s :=
      div_le_div_of_nonneg_right hb.le hℓ0.le
    have hexp : Real.exp (-Real.sqrt (((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) / ellT L g s)) ≤
        Real.exp (-Real.sqrt (Yw / ellT L g s)) := Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt hy))
    have : tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) ≤ c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s))) := by
      refine ht.trans ?_
      calc _ ≤ c₀ * ((g ^ 2 + (1 - s))⁻¹ * iniTermI_PI d L (b 0 - b 1)) * Real.exp (-Real.sqrt (Yw / ellT L g s)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ c₀ * ((g ^ 2)⁻¹ * 1) * Real.exp (-Real.sqrt (Yw / ellT L g s)) := by gcongr
        _ = _ := by ring
    exact (hX b).trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left this hq0) le_rfl) hM)
  have hXm0 : 0 ≤ M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D)) := by positivity
  have hXt0 : 0 ≤ M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)) := by positivity
  have hS := IniTermIGen_tail Th (s := s) (Tm := CR * (1 - u)⁻¹) (Xm := M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D)))
    (Xt := M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))
    (E₀ := Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u))) (r₁ := r₁) (Y₀ := Yw)
    (by have := inv_nonneg.2 hu1.le; positivity) hXm0 hXt0 (by positivity) hTm' hTd X hXm hXt a hr
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg (by linarith) hu1.le
  have hcS : ‖(c : ℂ) * IniTermIGen_Sfull Th s X a‖ ≤ ‖IniTermIGen_Sfull Th s X a‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
    exact mul_le_of_le_one_left (norm_nonneg _) hc1
  have hsub := norm_sub_norm_le (Uv) ((c : ℂ) * IniTermIGen_Sfull Th s X a)
  have h1s : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have hrest : ‖IniTermIGen_Sfull Th s X a‖ ≤ CR ^ 2 * ((Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
      (2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) +
        M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) := by
    refine hS.trans ?_
    have he0 : 0 ≤ Real.exp (-(cf * r₁ / ellT L g u)) := (Real.exp_pos _).le
    have hI := inv_nonneg.2 hu1.le
    have hCR2 : CR ≤ CR ^ 2 := by nlinarith
    have hY : 0 ≤ 2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) := by positivity
    have hin : (Fintype.card (Zd d L) : ℝ) ^ 2 * (2 * (Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u))) * (CR * (1 - u)⁻¹) *
          (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) + (CR * (1 - u)⁻¹) ^ 2 *
            (M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) ≤
        CR ^ 2 * ((Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
          (2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) +
            M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) := by
      have hc : (0 : ℝ) ≤ (Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 := by positivity
      have e1 : (Fintype.card (Zd d L) : ℝ) ^ 2 * (2 * (Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u))) * (CR * (1 - u)⁻¹) *
          (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) + (CR * (1 - u)⁻¹) ^ 2 *
            (M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) =
          ((Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2) *
            ((2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D)))) * CR + CR ^ 2 *
              (M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) := by ring
      rw [e1]
      have e2' : CR ^ 2 * ((Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
          (2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) +
            M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) =
          ((Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2) *
            (CR ^ 2 * (2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D)))) + CR ^ 2 *
              (M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) := by ring
      rw [e2']
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hc
      nlinarith [mul_nonneg hY (sub_nonneg.2 hCR2)]
    have h1s : (1 - s) ^ 2 ≤ 1 := by nlinarith
    calc (1 - s) ^ 2 * _ ≤ 1 * _ := mul_le_mul h1s le_rfl (by positivity) zero_le_one
      _ ≤ _ := by rw [one_mul]; exact hin
  have e2 : C₁ * M * (q * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) =
      C₁ * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) := by
    simp only [hq]
  linarith [hU, hcS, hsub, hrest, e2]
end Mixed

/-! ## 4. Compiled nonempty instances of target 8 (a) (target 10; `d = 3`, `szB`, `zB`) -/

end RBM.BA

end
