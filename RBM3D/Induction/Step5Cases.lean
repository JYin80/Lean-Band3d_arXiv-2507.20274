/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Kit

/-!
# S5-03 (ST-4): Step 5, cases (iii) and (ii) from their ingredients

Case (iii) of Step 5 from `lem:pf_step5` (`ST_step5_caseIII_of_pf`), case (ii) from its ingredient
pins (`ST_step5_caseII_of_pins`), with their deterministic comparisons, and the skeleton instances
`inst_skeletonII`, `inst_skeletonIII`.

Moved from the T2134 design probe (`7b2b789`, `RBM3D/Probe/T2134Pins.lean`, never merged), lines
`1040-1702` (`### Case (iii)` and `### Case (ii)`) and `2263-2272`; the instance namespace
`RBM.Gauss.T2134Inst` is `RBM.Gauss.Step5Inst`.
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (Step 5 is `3_5:1935-2383`).
Registry (DECISIONS §16, §20, §40): `STStep5II`, `STStep5III` stay owed (proved here only from
`STEtermsMid`, `STDuhamelII`, `STIniTermII`, `STWardII`, resp. `STPfStep5`).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ### Case (iii): from `lem:pf_step5` -/

/-- `ξ ≺ ζ₁` and the deterministic domination `ζ₁ ≺ ζ₂` (`ζ₁ ≤ N^τ ζ₂` eventually, every `τ > 0`) give `ξ ≺ ζ₂`. -/
theorem st5_prec_mono' {U : ℕ → Type*} {ξ ζ₁ ζ₂ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ₁)
    (hle : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ u ω, ζ₁ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω) :
    sz.Prec ξ ζ₂ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle (τ / 2) (half_pos hτ)] with n hn
  intro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₁ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω := by
    calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₁ n u ω
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₂ n u ω) :=
          mul_le_mul_of_nonneg_left (hn u ω) hpos
      _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω := by
          rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]
  exact lt_of_le_of_lt h1 hu

/-- `(1 + log W)^m ≤ 2^{m+1} W^τ` eventually, for every fixed `m` and `τ > 0` (`W → ∞`): a power of `log W` is below any power of `W`. -/
theorem st5_one_add_log_pow_le {W : ℕ → ℕ} (hW : Tendsto W atTop atTop) (m : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, (1 + Real.log ((W n : ℕ) : ℝ)) ^ m ≤ 2 ^ (m + 1) * ((W n : ℕ) : ℝ) ^ τ := by
  have h := detDom_log_pow m τ hτ
  filter_upwards [hW.eventually h, hW.eventually (eventually_ge_atTop 1)] with n hn hn1
  have hn' : Real.log ((W n : ℕ) : ℝ) ^ m ≤ ((W n : ℕ) : ℝ) ^ τ * 1 := hn ()
  have hW1 : (1 : ℝ) ≤ ((W n : ℕ) : ℝ) := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log ((W n : ℕ) : ℝ) := Real.log_nonneg hW1
  have hWτ : 1 ≤ ((W n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have h1 : (1 + Real.log ((W n : ℕ) : ℝ)) ^ m ≤ 2 ^ m * (1 + Real.log ((W n : ℕ) : ℝ) ^ m) := by
    have h2 : 1 + Real.log ((W n : ℕ) : ℝ) ≤ 2 * max 1 (Real.log ((W n : ℕ) : ℝ)) := by
      have := le_max_left 1 (Real.log ((W n : ℕ) : ℝ))
      have := le_max_right 1 (Real.log ((W n : ℕ) : ℝ))
      linarith
    calc (1 + Real.log ((W n : ℕ) : ℝ)) ^ m ≤ (2 * max 1 (Real.log ((W n : ℕ) : ℝ))) ^ m :=
          pow_le_pow_left₀ (by positivity) h2 m
      _ = 2 ^ m * max 1 (Real.log ((W n : ℕ) : ℝ)) ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + Real.log ((W n : ℕ) : ℝ) ^ m) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total 1 (Real.log ((W n : ℕ) : ℝ)) with h3 | h3
          · rw [max_eq_right h3]; linarith [one_pos.le.trans (one_le_pow₀ h3 : (1 : ℝ) ≤ Real.log ((W n : ℕ) : ℝ) ^ m)]
          · rw [max_eq_left h3, one_pow]; linarith [pow_nonneg hlog m]
  calc (1 + Real.log ((W n : ℕ) : ℝ)) ^ m ≤ 2 ^ m * (1 + Real.log ((W n : ℕ) : ℝ) ^ m) := h1
    _ ≤ 2 ^ m * (1 + ((W n : ℕ) : ℝ) ^ τ * 1) := by gcongr
    _ ≤ 2 ^ m * (2 * ((W n : ℕ) : ℝ) ^ τ) := by gcongr; linarith
    _ = 2 ^ (m + 1) * ((W n : ℕ) : ℝ) ^ τ := by ring

/-- `ℓ_u = 1` for `ilambda² ≤ 1 - u` (`3_5:2287`: "the length scale `ℓ_u` remains identically equal to `1`"). -/
theorem st5_ellT_one {L : ℕ} {g u : ℝ} (hL : 1 ≤ (L : ℝ)) (hx : g ^ 2 ≤ 1 - u) : ellT L g u = 1 := by
  unfold ellT
  have h1 : g / Real.sqrt |1 - u| ≤ 1 := by
    rcases le_or_gt g 0 with hg | hg
    · exact (div_nonpos_of_nonpos_of_nonneg hg (Real.sqrt_nonneg _)).trans zero_le_one
    · have hx0 : 0 < 1 - u := by nlinarith [sq_pos_of_pos hg]
      rw [abs_of_pos hx0]
      have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx0
      rw [div_le_one hs]
      calc g = Real.sqrt (g ^ 2) := (Real.sqrt_sq hg.le).symm
        _ ≤ Real.sqrt (1 - u) := Real.sqrt_le_sqrt hx
  rw [max_eq_right h1]
  exact min_eq_left hL

/-- `(W^d (1-u))⁻¹ ≤ 2 W^{-d} B_{u,0}` and `STWB(u, r) ≥ (2 W^d(1-u))⁻¹ (r+1)^{-(d-2)}` for `ilambda² ≤ 1 - u`: in the regime
`1 - u ≥ ilambda²` the control `W^{-d}B_{u,0}` is of order `(W^d(1-u))⁻¹` (`3_5:2288`: "of order `(W^d|1-u|)⁻¹`"). -/
theorem st5_Bctl_ge_III (n : ℕ) {u : ℝ} (hu : u < 1) (hx : sz.lam n ^ 2 ≤ 1 - u) :
    (2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)))⁻¹ ≤ sz.Bctl n u := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hx0 : 0 < 1 - u := by linarith
  have hg2 : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos hx0]
  have h0 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [h0, inv_one, mul_one]
  have h1 : (2 * (1 - u))⁻¹ ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
    positivity
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)))⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (1 - u))⁻¹ := by
        rw [show 2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)) = ((sz.W n : ℕ) : ℝ) ^ d * (2 * (1 - u)) by ring, mul_inv]
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem st5_STWB_ge_III (n : ℕ) {u : ℝ} (hu : u < 1) (hx : sz.lam n ^ 2 ≤ 1 - u) (k : ℕ) :
    (2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)))⁻¹ * (((k : ℝ) + 1) ^ (d - 2))⁻¹ ≤ STWB sz n u k := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hx0 : 0 < 1 - u := by linarith
  have hg2 : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  unfold STWB Bparam
  rw [abs_of_pos hx0]
  have h1 : (2 * (1 - u))⁻¹ ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
    positivity
  have hK : 0 ≤ (((k : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)))⁻¹ * (((k : ℝ) + 1) ^ (d - 2))⁻¹
      = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((2 * (1 - u))⁻¹ * (((k : ℝ) + 1) ^ (d - 2))⁻¹) := by
        rw [show 2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)) = ((sz.W n : ℕ) : ℝ) ^ d * (2 * (1 - u)) by ring, mul_inv]
        ring
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * (((k : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := mul_le_mul_of_nonneg_right h1 hK
        linarith

/-- **Case (iii), the strong estimate from `lem:pf_step5`**: `T_{u,D}(r) ≤ 4 ((W^{-d}B_{u,0})² e^{-√r} + W^{-D})` for
`ilambda² ≤ 1 - u` (`(W^d(1-u))^{-2} ≤ 4 (W^{-d}B_{u,0})²`: constants in `[1/4, (1+L^{-d})²]`, preflight table). -/
theorem st5_compare_IIIa (n : ℕ) {u D : ℝ} (hu : u < 1) (hx : sz.lam n ^ 2 ≤ 1 - u) (a : Fin 2 → Zd d (sz.L n)) :
    STtailTD sz n u D a ≤
      4 * ((sz.Bctl n u) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  have hx0 : 0 < 1 - u := by linarith [sq_nonneg (sz.lam n)]
  have hΔ := st5_Bctl_ge_III sz n hu hx
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hy : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ 2 * sz.Bctl n u := by
    have : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ = 2 * (2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)))⁻¹ := by
      field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hΔ (by norm_num)
  have hy0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  have hsq : ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 ≤ 4 * (sz.Bctl n u) ^ 2 := by
    calc ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 ≤ (2 * sz.Bctl n u) ^ 2 := pow_le_pow_left₀ hy0 hy 2
      _ = 4 * (sz.Bctl n u) ^ 2 := by ring
  have hE : 0 < Real.exp (-((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := Real.exp_pos _
  have hWD : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold STtailTD tailTD
  rw [abs_of_pos hx0, Real.sqrt_eq_rpow]
  nlinarith [mul_le_mul_of_nonneg_right hsq hE.le]


/-- **Case (iii), `(Eq:Gdecay+s<g_flow)` is stronger than `(Eq:Gdecay_flow)`** (`3_5:2383`), made explicit: for `ilambda² ≤ 1 - u`
(so `ℓ_u = 1`) and `y = (W^d(1-u))⁻¹ ≤ 1`, `T_{u,D}(r) ≤ 4 (Δ_u^{1/5} W^{-d}B_{u,r} e^{-(r/ℓ_u)^{1/2}} + W^{-D})`
provided `y^{4/5} ((D log W)² + 1)^{d-2} ≤ 1`.  Beyond `r ≥ (D log W)²` the factor `e^{-√r} ≤ W^{-D}` absorbs everything; below it
`B_{u,r}` loses `(r+1)^{-(d-2)}`, a polylogarithm, which `y^{4/5} ≤ (ilambda² W^d)^{-4/5} ≤ W^{-8𝔡/5}` beats: the
paper's "stronger" holds up to the `(log W)^{2(d-2)}` that `≺` absorbs. -/
theorem st5_compare_IIIb (n : ℕ) {u D : ℝ} (hD : 0 < D) (hu : u < 1) (hx : sz.lam n ^ 2 ≤ 1 - u)
    (hy1 : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ 1)
    (hcond : ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ (1 / 5 : ℝ)) ^ 4 *
      ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2) ≤ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STtailTD sz n u D a ≤
      4 * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hx0 : 0 < 1 - u := by linarith [sq_nonneg (sz.lam n)]
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hell : ellT (sz.L n) (sz.lam n) u = 1 := st5_ellT_one hL1 hx
  have hB0 : 0 < sz.Bctl n u := st_Bctl_pos sz hu
  have hΔ := st5_Bctl_ge_III sz n hu hx
  set y := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hy
  have hy0 : 0 < y := by positivity
  set k := zdistInf d (sz.L n) (a 0 - a 1) with hk
  have hWD : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hE0 : 0 < Real.exp (-((k : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := Real.exp_pos _
  have h0 : ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) = 1 := by simp
  rw [h0, hell, div_one]
  set E := Real.exp (-((k : ℕ) : ℝ) ^ (1 / 2 : ℝ)) with hE
  have hS0 : 0 ≤ STWB sz n u k := by
    unfold STWB Bparam
    have hx0' : 0 ≤ |1 - u| := abs_nonneg _
    positivity
  have h15 : 0 ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hB0.le _
  have hQ0 : 0 ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u k := mul_nonneg h15 hS0
  have htail : STtailTD sz n u D a = y ^ 2 * E + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    unfold STtailTD tailTD
    rw [abs_of_pos hx0, Real.sqrt_eq_rpow]
  rw [htail]
  by_cases hcase : (D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 ≤ (k : ℝ)
  · -- far: `e^{-√k} ≤ W^{-D}`
    have hlog : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
    have hsq : D * Real.log ((sz.W n : ℕ) : ℝ) ≤ (k : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      calc D * Real.log ((sz.W n : ℕ) : ℝ) = Real.sqrt ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hcase
    have hEW : E ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
      rw [hE, Real.rpow_def_of_pos hW0]
      apply Real.exp_le_exp.2
      nlinarith [hsq]
    have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy1, hy0]
    have : y ^ 2 * E ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
      calc y ^ 2 * E ≤ 1 * E := mul_le_mul_of_nonneg_right hy2 hE0.le
        _ ≤ _ := by linarith
    nlinarith [mul_nonneg hQ0 hE0.le]
  · -- near: `B_{u,k}` loses `(k+1)^{-(d-2)}`, beaten by `y^{4/5}`
    have hk' : (k : ℝ) < (D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 := not_le.1 hcase
    set z := y ^ (1 / 5 : ℝ) with hz
    have hz0 : 0 < z := Real.rpow_pos_of_pos hy0 _
    have hz5 : z ^ 5 = y := by
      rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
    set h := (2 : ℝ) ^ (1 / 5 : ℝ) with hh
    have hh1 : 1 ≤ h := Real.one_le_rpow (by norm_num) (by norm_num)
    have hh2 : h ≤ 2 := by
      calc h ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hh0 : 0 < h := by linarith
    set M := ((k : ℝ) + 1) ^ (d - 2) with hM
    have hM1 : 1 ≤ M := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hM0 : 0 < M := by linarith
    have hMM : M ≤ ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    -- lower bounds
    have hΔ' : y / 2 ≤ sz.Bctl n u := by
      have : y / 2 = (2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)))⁻¹ := by rw [hy]; field_simp
      rw [this]; exact hΔ
    have hΔ15 : z / h ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) := by
      calc z / h = (y / 2) ^ (1 / 5 : ℝ) := by rw [Real.div_rpow hy0.le (by norm_num)]
        _ ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) hΔ' (by norm_num)
    have hS : (z ^ 5 / 2) * M⁻¹ ≤ STWB sz n u k := by
      have := st5_STWB_ge_III sz n hu hx k
      have e : (2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)))⁻¹ = y / 2 := by rw [hy]; field_simp
      rw [e] at this
      rw [hz5]; simpa [hM] using this
    have hQ : (z / h) * ((z ^ 5 / 2) * M⁻¹) ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u k :=
      mul_le_mul hΔ15 hS (by positivity) h15
    have hmul := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 2 * h * z ^ 4 * M)
    have e : 2 * h * z ^ 4 * M * ((z / h) * ((z ^ 5 / 2) * M⁻¹)) = z ^ 10 := by
      field_simp
    rw [e] at hmul
    have hz4M : z ^ 4 * M ≤ 1 := by
      calc z ^ 4 * M ≤ z ^ 4 * ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2) :=
            mul_le_mul_of_nonneg_left hMM (by positivity)
        _ ≤ 1 := hcond
    have hy2 : y ^ 2 ≤ 4 * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u k) := by
      have h1 : y ^ 2 = z ^ 10 := by rw [← hz5]; ring
      rw [h1]
      calc z ^ 10 ≤ 2 * h * z ^ 4 * M * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u k) := hmul
        _ = 2 * h * (z ^ 4 * M) * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u k) := by ring
        _ ≤ 2 * h * 1 * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u k) := by
            apply mul_le_mul_of_nonneg_right _ hQ0
            exact mul_le_mul_of_nonneg_left hz4M (by positivity)
        _ ≤ 4 * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u k) := by
            apply mul_le_mul_of_nonneg_right _ hQ0
            linarith
    nlinarith [mul_le_mul_of_nonneg_right hy2 hE0.le, hWD]


/-- `((D log W)² + 1)^{d-2} ≤ W^{8𝔡/5}` eventually (a power of a logarithm against a power of `W`). -/
theorem st5_polylog_le_W {W : ℕ → ℕ} (hW : Tendsto W atTop atTop) (d : ℕ) {D 𝔡 : ℝ} (h𝔡 : 0 < 𝔡) :
    ∀ᶠ n in atTop, ((D * Real.log ((W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2) ≤ ((W n : ℕ) : ℝ) ^ (8 * 𝔡 / 5) := by
  have h1 := st5_one_add_log_pow_le hW (2 * (d - 2)) (show 0 < 4 * 𝔡 / 5 by positivity)
  have hWr : Tendsto (fun n => ((W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  have h2 : ∀ᶠ n in atTop, (D ^ 2 + 1) ^ (d - 2) * 2 ^ (2 * (d - 2) + 1) ≤ ((W n : ℕ) : ℝ) ^ (4 * 𝔡 / 5) :=
    ((tendsto_rpow_atTop (show 0 < 4 * 𝔡 / 5 by positivity)).comp hWr).eventually_ge_atTop _
  filter_upwards [h1, h2, hW.eventually (eventually_ge_atTop 1)] with n hn1 hn2 hn3
  have hW1 : (1 : ℝ) ≤ ((W n : ℕ) : ℝ) := by exact_mod_cast hn3
  have hlog : 0 ≤ Real.log ((W n : ℕ) : ℝ) := Real.log_nonneg hW1
  have hbase : (D * Real.log ((W n : ℕ) : ℝ)) ^ 2 + 1 ≤ (D ^ 2 + 1) * (1 + Real.log ((W n : ℕ) : ℝ)) ^ 2 := by
    have h3 : (1 : ℝ) ≤ (1 + Real.log ((W n : ℕ) : ℝ)) ^ 2 := by nlinarith
    have h4 : (Real.log ((W n : ℕ) : ℝ)) ^ 2 ≤ (1 + Real.log ((W n : ℕ) : ℝ)) ^ 2 := by nlinarith
    nlinarith [sq_nonneg D]
  calc ((D * Real.log ((W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2)
      ≤ ((D ^ 2 + 1) * (1 + Real.log ((W n : ℕ) : ℝ)) ^ 2) ^ (d - 2) :=
        pow_le_pow_left₀ (by positivity) hbase _
    _ = (D ^ 2 + 1) ^ (d - 2) * (1 + Real.log ((W n : ℕ) : ℝ)) ^ (2 * (d - 2)) := by
        rw [mul_pow, ← pow_mul]
    _ ≤ (D ^ 2 + 1) ^ (d - 2) * (2 ^ (2 * (d - 2) + 1) * ((W n : ℕ) : ℝ) ^ (4 * 𝔡 / 5)) :=
        mul_le_mul_of_nonneg_left hn1 (by positivity)
    _ = ((D ^ 2 + 1) ^ (d - 2) * 2 ^ (2 * (d - 2) + 1)) * ((W n : ℕ) : ℝ) ^ (4 * 𝔡 / 5) := by ring
    _ ≤ ((W n : ℕ) : ℝ) ^ (4 * 𝔡 / 5) * ((W n : ℕ) : ℝ) ^ (4 * 𝔡 / 5) :=
        mul_le_mul_of_nonneg_right hn2 (Real.rpow_nonneg (by linarith) _)
    _ = ((W n : ℕ) : ℝ) ^ (8 * 𝔡 / 5) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf

/-- **Case (iii) from `lem:pf_step5`**: the pin `STPfStep5` (`T ≥ t` w.h.p.) gives `(Eq:Gdecay+s<g_flow)` (`T_{u,D} ≤ 4(Δ_u² e^{-√r}
+ W^{-D})`, `st5_compare_IIIa`) and `(Eq:Gdecay_flow)` (`T_{u,D} ≤ 4 (Δ_u^{1/5} W^{-d}B_{u,r} e^{-(r/ℓ_u)^{1/2}} + W^{-D})` up to the
`(log W)^{2(d-2)}` that `≺` absorbs, `st5_compare_IIIb`, `(eq:WO)`). -/
theorem ST_step5_caseIII_of_pf (hPf : STPfStep5 d) : STStep5III d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hPf hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨c₁, hc₁, hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  have hPfc := H₁ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow ht
  have hWO := hflow.1.2.2.2.2
  have hbw := hflow.1.2.2.2.1
  have h𝔠 := hflow.1.1
  have hN : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsz
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hbw.mono fun n hn => hn) ((tendsto_rpow_atTop h𝔠).comp hN)
  have hWt' : Tendsto sz.W atTop atTop := tendsto_natCast_atTop_iff.1 hWt
  refine ⟨fun D hD0 => ?_, fun D hD0 => ?_⟩
  · -- `(Eq:Gdecay_flow)` from the `T_{u,D}` bound
    have h1 := StochDomAt.precomp_param (hPfc D hD0)
      (fun n (p : STIdx2 sz s t n) => (⟨p, hR n⟩ : {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n}))
    refine st5_prec_mono' sz h1 ?_
    intro τ hτ
    have hlog := st5_polylog_le_W hWt' d (D := D) h𝔡
    filter_upwards [hWO, hlog, (tendsto_size sz hsz).eventually (eventually_le_rpow 4 hτ)] with n hn hl h4 p ω
    have hu : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
    have hx : sz.lam n ^ 2 ≤ 1 - (p.1 : ℝ) := by linarith [hR n, p.1.2.2]
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hA := lam_sq_mul_pow_ge sz n hn.1
    have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hn.1
    -- `y ≤ W^{-2𝔡}`
    have hy : (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := by
      have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
      have h2 : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)) := by
        calc ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hA
          _ = ((sz.W n : ℕ) : ℝ) ^ d * sz.lam n ^ 2 := by ring
          _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)) := mul_le_mul_of_nonneg_left hx hWd.le
      rw [Real.rpow_neg hW0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hW0 _) h2
    have hy1 : (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ≤ 1 :=
      hy.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
    have hy0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ := by
      have : 0 < 1 - (p.1 : ℝ) := by linarith [sq_nonneg (sz.lam n)]
      have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
      positivity
    have hcond : ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (1 / 5 : ℝ)) ^ 4 *
        ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2) ≤ 1 := by
      have e1 : ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (1 / 5 : ℝ)) ^ 4 =
          (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (4 / 5 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
      have e2 : (((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡))) ^ (4 / 5 : ℝ) = ((sz.W n : ℕ) : ℝ) ^ (-(8 * 𝔡 / 5)) := by
        rw [← Real.rpow_mul hW0.le]; ring_nf
      have h3 : (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (4 / 5 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(8 * 𝔡 / 5)) := by
        rw [← e2]; exact Real.rpow_le_rpow hy0 hy (by norm_num)
      rw [e1]
      calc (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (4 / 5 : ℝ) *
            ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2)
          ≤ ((sz.W n : ℕ) : ℝ) ^ (-(8 * 𝔡 / 5)) * ((sz.W n : ℕ) : ℝ) ^ (8 * 𝔡 / 5) :=
            mul_le_mul h3 hl (by positivity) (Real.rpow_nonneg hW0.le _)
        _ = 1 := by rw [← Real.rpow_add hW0]; simp
    have key := st5_compare_IIIb sz n hD0 hu hx hy1 hcond p.2.2
    have h0 : ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) = 1 := by rw [Real.rpow_zero]
    have hT : STtailTD sz n (p.1 : ℝ) D p.2.2 ≤ 4 * (((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
      rw [h0]; simpa using key
    have hnonneg : 0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) := by
      have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) := (st_Bctl_pos sz hu).le
      have hS0 : 0 ≤ STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
        unfold STWB Bparam
        have hx0' : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have : 0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) := by rw [Real.rpow_zero]; norm_num
      positivity
    calc STtailTD sz n (p.1 : ℝ) D p.2.2 ≤ 4 * _ := hT
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * _ := mul_le_mul_of_nonneg_right h4 hnonneg
  · -- `(Eq:Gdecay+s<g_flow)`
    refine st5_prec_mono sz hsz (c := 4) (hPfc D hD0) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      intro p ω
      have hu : (p.1.1 : ℝ) < 1 := lt_of_le_of_lt p.1.1.2.2 (ht1 n)
      have hx : sz.lam n ^ 2 ≤ 1 - (p.1.1 : ℝ) := by linarith [p.2, p.1.1.2.2]
      exact st5_compare_IIIa sz n (D := D) hu hx p.1.2.2
    · intro n p ω
      have hB0 : 0 ≤ sz.Bctl n (p.1.1 : ℝ) := by
        unfold Sizes.Bctl Bparam
        have hx0 : 0 ≤ |1 - (p.1.1 : ℝ)| := abs_nonneg _
        positivity
      have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity


/-! ### Case (ii): the zero-mode part -/

/-- `Im m(E) ≥ √(2κ)/2` for `|E| ≤ 2 - κ`. -/
theorem st5_mE_im_ge {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : Real.sqrt (2 * κ) / 2 ≤ (mE E).im := by
  rw [mE_im]
  have h1 := abs_le.1 hE
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have h2 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

/-- `A^{-1/5} ≤ 2 Δ_u^{1/5}` for `1 - u ≤ ilambda²` (`Δ_u ≥ (2A)⁻¹`). -/
theorem st5_A15_le (n : ℕ) (hlam : 0 < sz.lam n) (hA1 : 1 ≤ STAI sz n) {u : ℝ} (hu : u < 1) (hx : 1 - u ≤ sz.lam n ^ 2) :
    (STAI sz n) ^ (-(1 / 5) : ℝ) ≤ 2 * (sz.Bctl n u) ^ (1 / 5 : ℝ) := by
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hΔ := st5_Bctl_ge sz n hlam hu hx
  have hB0 : 0 < sz.Bctl n u := st_Bctl_pos sz hu
  have h1 : (STAI sz n)⁻¹ ≤ 2 * sz.Bctl n u := by
    have : (STAI sz n)⁻¹ = 2 * (2 * STAI sz n)⁻¹ := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hΔ (by norm_num)
  rw [Real.rpow_neg hA0.le, ← Real.inv_rpow hA0.le]
  calc ((STAI sz n)⁻¹) ^ (1 / 5 : ℝ) ≤ (2 * sz.Bctl n u) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (inv_nonneg.2 hA0.le) h1 (by norm_num)
    _ = 2 ^ (1 / 5 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) := Real.mul_rpow (by norm_num) hB0.le
    _ ≤ 2 * (sz.Bctl n u) ^ (1 / 5 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hB0.le _)
        calc (2 : ℝ) ^ (1 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2

/-- **Case (ii), the Ward term `(zYU1)`**: `A⁻¹ (N η_u)⁻¹ ≤ (6/c) Δ_u^{1/5} W^{-d}B_{u,r} e^{-(r/ℓ_u)^{1/2}}` for `1 - u ≤ ilambda²/L²`
(`ℓ_u = L`), `Im m ≥ c`: the zero mode `(L^d(1-u))⁻¹` of `B_{u,r}` carries it (`3_5:2258`, preflight table row 20). -/
theorem st5_compare_IIward (n : ℕ) (hlam : 0 < sz.lam n) (hA1 : 1 ≤ STAI sz n) {u E : ℝ} (hu : u < 1)
    (hx : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) {c : ℝ} (hc : 0 < c) (hIm : c ≤ (mE E).im)
    (a : Fin 2 → Zd d (sz.L n)) :
    (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹ ≤
      (6 / c) * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ))) := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by linarith
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hx0 : 0 < 1 - u := by linarith
  have hL2 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ 2 := one_le_pow₀ hL1
  have hxg : 1 - u ≤ sz.lam n ^ 2 := by
    refine hx.trans ?_
    exact div_le_self hg2.le hL2
  have hell : ellT (sz.L n) (sz.lam n) u = ((sz.L n : ℕ) : ℝ) := ellT_eq_of_le hlam.le hu hL1 hx
  have hr : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast st5_zdistInf_le sz n (a 0 - a 1)
  have hr0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexp : Real.exp (-1) ≤ Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    rw [hell]
    apply Real.exp_le_exp.2
    have h1 : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ((sz.L n : ℕ) : ℝ) ≤ 1 :=
      (div_le_one hL0).2 hr
    have h2 : (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ((sz.L n : ℕ) : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 := by
      calc _ ≤ (1 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (div_nonneg hr0 hL0.le) h1 (by norm_num)
        _ = 1 := Real.one_rpow _
    linarith
  have hexp' : 1 ≤ Real.exp 1 * Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_pos 1).le
  set E' := Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) with hE'
  have hE0 : 0 < E' := Real.exp_pos _
  have h3 := st5_exp_one_lt_three
  have hA15 := st5_A15_le sz n hlam hA1 hu hxg
  have hA1' : (STAI sz n)⁻¹ ≤ (STAI sz n) ^ (-(1 / 5) : ℝ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
  -- `(N η_u)⁻¹ ≤ c⁻¹ W^{-d} (L^d (1-u))⁻¹ ≤ c⁻¹ STWB`
  have hNeq : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hη : (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹ ≤ c⁻¹ * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
    have hZ : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
      unfold STWB Bparam
      rw [abs_of_pos hx0, hNeq]
      have : (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ =
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
        rw [mul_assoc, mul_inv]
      rw [this]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
        positivity
      linarith
    unfold etaT
    have hNp : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    calc (((sz.size n : ℕ) : ℝ) * ((1 - u) * (mE E).im))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * ((1 - u) * c))⁻¹ :=
          inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIm hx0.le) hNp.le)
      _ = c⁻¹ * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
          rw [show ((sz.size n : ℕ) : ℝ) * ((1 - u) * c) = c * (((sz.size n : ℕ) : ℝ) * (1 - u)) by ring, mul_inv]
      _ ≤ c⁻¹ * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) :=
          mul_le_mul_of_nonneg_left hZ (inv_nonneg.2 hc.le)
  have hS0 : 0 ≤ STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
    unfold STWB Bparam
    have hx0' : 0 ≤ |1 - u| := abs_nonneg _
    positivity
  have hB0 : 0 < sz.Bctl n u := st_Bctl_pos sz hu
  have h15 : 0 ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hB0.le _
  have h0 : ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) = 1 := by simp
  rw [h0]
  have hAη : (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹ ≤
      (2 * (sz.Bctl n u) ^ (1 / 5 : ℝ)) * (c⁻¹ * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1))) :=
    mul_le_mul (hA1'.trans hA15) hη
      (inv_pos.2 (mul_pos (by exact_mod_cast sz.one_le_size n) (mul_pos hx0 (lt_of_lt_of_le hc hIm)))).le
      (mul_nonneg (by norm_num) h15)
  have hS1 : STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) ≤
      3 * (STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) * E') := by
    have h5 : 1 ≤ 3 * E' := by nlinarith [hexp', Real.exp_pos 1]
    nlinarith [mul_le_mul_of_nonneg_left h5 hS0]
  calc (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹
      ≤ (2 * (sz.Bctl n u) ^ (1 / 5 : ℝ)) * (c⁻¹ * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1))) := hAη
    _ = (2 / c) * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1))) := by ring
    _ ≤ (2 / c) * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * (3 * (STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) * E'))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hS1 h15
    _ = (6 / c) * (1 * (sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) * E') := by ring


theorem st5_reg5II_mid {sz : Sizes d} {s t : ℕ → ℝ} (h : STReg5II sz s t) : STReg5Mid sz s t := by
  intro n
  refine ⟨(h n).1, (h n).2.trans ?_⟩
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  exact div_le_self (sq_nonneg _) (one_le_pow₀ hL)

/-- **Case (ii) from its ingredients** (`3_5:2251-2283`): the three error terms (`STEtermsMid`), the integrated hierarchy with
`Q^{(1)}` for `σ₁ ≠ σ₂` and without `Q` for `σ₁ = σ₂` (`STDuhamelII`), the initial terms (`STIniTermII`) and the Ward term
`(zYU1)` (`STWardII`) give `(Eq:Gdecay_flow)`: for `σ₁ ≠ σ₂`, `|𝓛-𝒦| ≤ |𝓛-𝒦 - Q^{(1)}(𝓛-𝒦)| + |Q^{(1)}(𝓛-𝒦)|`, the first
bounded by the zero mode of `B_{u,r}` (`st5_compare_IIward`), the second as in case (i) (`st5_compare_I`); the strong estimate is void. -/
theorem ST_step5_caseII_of_pins (hE : STEtermsMid d) (hD : STDuhamelII d) (hI : STIniTermII d) (hWd : STWardII d) :
    STStep5II d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hE hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hD hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hI hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hcpos : 0 < min c₁ (min c₂ (min c₃ c₄)) := lt_min hc₁ (lt_min hc₂ (lt_min hc₃ hc₄))
  refine ⟨min c₁ (min c₂ (min c₃ c₄)), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow ht
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hm₁ := st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)
  have hm₂ := st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_left _ _))
  have hm₃ := st5_conStInd_mono sz hcon ht1 hcpos
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hm₄ := st5_conStInd_mono sz hcon ht1 hcpos
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hE' := H₁ 𝔠 sz z hflow s t hs0 hst ht (st5_reg5II_mid hR) hKb hKw hLK hDec hDecS hm₁ hS1 hS2
    hLmax hLKU
  obtain ⟨hDQ, hDS⟩ := H₂ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₂ hS1 hS2 hLmax hLKU hE'
  obtain ⟨hIQ, hIS⟩ := H₃ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₃ hS1 hS2 hLmax hLKU
  have hW' := H₄ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₄ hS1 hS2 hLmax hLKU
  have hev := st5_eventually_A_ge_one sz hflow.1.2.1 hflow.1.2.2.2.2
  -- `Im m(E_n) ≥ c_κ`
  have hIm : ∀ n, Real.sqrt (2 * κ) / 2 ≤ (mE (STflowE z n)).im := fun n => by
    have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (hflow.2 n).2.1
    exact st5_mE_im_ge hκ (lemma28_quant hκ him (hflow.2 n).2.2 (hflow.2 n).1).1
  have hcκ : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  refine ⟨fun D hD0 => ?_, fun D hD0 => ?_⟩
  · -- the two sign classes
    have hmix : sz.Prec (U := STIdx2P sz STSigMixed s t)
        (fun n v ω => ‖Lloop sz n (STflowE z n) (v.1 : ℝ) v.2.1.1 v.2.2 ω - STKloop sz n (STflowE z n) (v.1 : ℝ) v.2.1.1 v.2.2‖)
        (fun n v _ => ((((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) * (sz.Bctl n (v.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (v.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)))) := by
      have hQ := hDQ D hD0
        (fun n p => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
        (fun n p => add_nonneg (mul_nonneg (Real.rpow_nonneg (st5_STAI_nonneg sz n) _)
          (st5_STprof_nonneg sz n _ _ _ _ _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hIQ D hD0)
      have hsum := StochDomAt.add (tendsto_size sz hsz) hW' hQ
      have hle : ∀ (n : ℕ) (v : STIdx2P sz STSigMixed s t n) (ω : sz.SeqΩ),
          ‖Lloop sz n (STflowE z n) (v.1 : ℝ) v.2.1.1 v.2.2 ω - STKloop sz n (STflowE z n) (v.1 : ℝ) v.2.1.1 v.2.2‖ ≤
            ((fun n (v : STIdx2P sz STSigMixed s t n) ω =>
              ‖STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 v.2.2 -
                zeroModeSet d (sz.L n) {0}
                  (fun a' => STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 a') v.2.2‖) +
            (fun n (v : STIdx2P sz STSigMixed s t n) ω =>
              ‖zeroModeSet d (sz.L n) {0}
                (fun a' => STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 a') v.2.2‖)) n v ω := by
        intro n v ω
        change ‖STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 v.2.2‖ ≤
          ‖STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 v.2.2 -
            zeroModeSet d (sz.L n) {0}
              (fun a' => STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 a') v.2.2‖ +
          ‖zeroModeSet d (sz.L n) {0}
            (fun a' => STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 a') v.2.2‖
        have := norm_add_le (STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 v.2.2 -
            zeroModeSet d (sz.L n) {0}
              (fun a' => STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 a') v.2.2)
          (zeroModeSet d (sz.L n) {0}
            (fun a' => STLKM sz n (STflowE z n) (v.1 : ℝ) (sz.seqHflow n (v.1 : ℝ) ω) v.2.1.1 a') v.2.2)
        rwa [sub_add_cancel] at this
      have hsum' := StochDomAt.of_le_left hle hsum
      refine st5_prec_mono sz hsz (c := 6 / (Real.sqrt (2 * κ) / 2) + 4) hsum' ?_ ?_
      · filter_upwards [hev] with n hn
        intro v ω
        have hu : (v.1 : ℝ) < 1 := lt_of_le_of_lt v.1.2.2 (ht1 n)
        have hxL : 1 - (v.1 : ℝ) ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by linarith [(hR n).2, v.1.2.1]
        have hxg : 1 - (v.1 : ℝ) ≤ sz.lam n ^ 2 := by
          have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
          exact hxL.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hL))
        have h1 := st5_compare_IIward sz n hn.1 hn.2 hu hxL hcκ (hIm n) v.2.2
        have h2 := st5_compare_I sz n hn.1 hn.2 (D := D) hu hxg v.2.2
        have hP : 0 ≤ ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n (v.1 : ℝ)) ^ (1 / 5 : ℝ) *
              STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) *
              Real.exp (-(((zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (v.1 : ℝ)) ^ (1 / 2 : ℝ)) := by
          have hB0 : 0 ≤ sz.Bctl n (v.1 : ℝ) := (st_Bctl_pos sz hu).le
          have hS0 : 0 ≤ STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) := by
            unfold STWB Bparam
            have hx0' : 0 ≤ |1 - (v.1 : ℝ)| := abs_nonneg _
            positivity
          have : 0 ≤ ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) := by rw [Real.rpow_zero]; norm_num
          positivity
        have hWD : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h0 : ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) = 1 := by simp
        have h0' : ((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) = 1 := by rw [Real.rpow_zero]
        rw [h0] at h1 h2 hP
        simp only [Pi.add_apply]
        rw [h0']
        have hcc : 0 < 6 / (Real.sqrt (2 * κ) / 2) := by positivity
        nlinarith [h1, h2, hP, hWD, mul_nonneg hcc.le hWD]
      · intro n v ω
        have hu : (v.1 : ℝ) < 1 := lt_of_le_of_lt v.1.2.2 (ht1 n)
        have hB0 : 0 ≤ sz.Bctl n (v.1 : ℝ) := (st_Bctl_pos sz hu).le
        have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hS0 : 0 ≤ STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) := by
          unfold STWB Bparam
          have hx0' : 0 ≤ |1 - (v.1 : ℝ)| := abs_nonneg _
          positivity
        have : 0 ≤ ((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) := by rw [Real.rpow_zero]; norm_num
        positivity
    have hsame : sz.Prec (U := STIdx2P sz STSigSame s t)
        (fun n v ω => ‖Lloop sz n (STflowE z n) (v.1 : ℝ) v.2.1.1 v.2.2 ω - STKloop sz n (STflowE z n) (v.1 : ℝ) v.2.1.1 v.2.2‖)
        (fun n v _ => ((((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) * (sz.Bctl n (v.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (v.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)))) := by
      have hDu := hDS D hD0
        (fun n p => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
        (fun n p => add_nonneg (mul_nonneg (Real.rpow_nonneg (st5_STAI_nonneg sz n) _)
          (st5_STprof_nonneg sz n _ _ _ _ _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hIS D hD0)
      simp only [st5_zeroModeSet_empty] at hDu
      refine st5_prec_mono sz hsz (c := 4) hDu ?_ ?_
      · filter_upwards [hev] with n hn
        intro v ω
        have hu : (v.1 : ℝ) < 1 := lt_of_le_of_lt v.1.2.2 (ht1 n)
        have hxg : 1 - (v.1 : ℝ) ≤ sz.lam n ^ 2 := by
          have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
          have : 1 - (v.1 : ℝ) ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by linarith [(hR n).2, v.1.2.1]
          exact this.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hL))
        have h2 := st5_compare_I sz n hn.1 hn.2 (D := D) hu hxg v.2.2
        have h0 : ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) = 1 := by simp
        have h0' : ((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) = 1 := by rw [Real.rpow_zero]
        rw [h0] at h2
        rw [h0']
        exact h2
      · intro n v ω
        have hu : (v.1 : ℝ) < 1 := lt_of_le_of_lt v.1.2.2 (ht1 n)
        have hB0 : 0 ≤ sz.Bctl n (v.1 : ℝ) := (st_Bctl_pos sz hu).le
        have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hS0 : 0 ≤ STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) := by
          unfold STWB Bparam
          have hx0' : 0 ≤ |1 - (v.1 : ℝ)| := abs_nonneg _
          positivity
        have : 0 ≤ ((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) := by rw [Real.rpow_zero]; norm_num
        positivity
    exact st5_prec_cover sz hsz
      (fun n (v : STIdx2P sz STSigMixed s t n) => ((v.1, v.2.1.1, v.2.2) : STIdx2 sz s t n))
      (fun n (v : STIdx2P sz STSigSame s t n) => ((v.1, v.2.1.1, v.2.2) : STIdx2 sz s t n))
      (fun n u => by
        by_cases h : u.2.1 0 = u.2.1 1
        · exact Or.inr ⟨(u.1, ⟨u.2.1, h⟩, u.2.2), rfl⟩
        · exact Or.inl ⟨(u.1, ⟨u.2.1, h⟩, u.2.2), rfl⟩) hmix hsame
  · refine st5_prec_of_isEmpty sz fun n => ⟨fun p => ?_⟩
    have h1 := (hR n).2
    have h2 := p.2
    have h3 := hst n
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have h4 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 := div_le_self (sq_nonneg _) hL1
    linarith

end RBM.Gauss.Sizes

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter

/-! ### The skeletons at the data (ingredients as hypotheses) -/

/-- Case (ii) from its ingredients, at `(szB, zB, 15/16, 31/32)`. -/
theorem inst_skeletonII (hE : STEtermsMid 3) (hD : STDuhamelII 3) (hI : STIniTermII 3) (hW : STWardII 3)
    (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_step5II (ST_step5_caseII_of_pins hE hD hI hW) Cd hCd

/-- Case (iii) from `lem:pf_step5`, at `(sz0, z0, 0, 1/16)`. -/
theorem inst_skeletonIII (hPf : STPfStep5 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_step5III (ST_step5_caseIII_of_pf hPf) Cd hCd

end RBM.Gauss.Step5Inst
