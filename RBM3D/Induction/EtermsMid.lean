/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.EMn2Exp2
import RBM3D.Induction.NewKLKL
import RBM3D.Induction.LemDecCalELip

/-!
# S5-13 (ticket T2328): the three error terms of `(int_K-LcalE_n=2)` at `ℓ = L`

`stEtermsMid_of_LWT (d : ℕ) : STLWT d → STEtermsMid d` (`Induction/Step5Pins.lean:275`; paper
`paper/tex/3_5_Loop_Hierarchy.tex:1961-1979`, inputs `(eq:Step2_inputs)` `3_5:1340-1357`): in the window
`ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²` (`STReg5Mid`), uniformly in `u ∈ [s,t]` and every `D > 0`,
`ℰ^{LK×LK} ≺ A^{-1/3} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`, `ℰ^{G̃} ≺ A^{-1/2} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`,
`(ℰ⊗ℰ)^{M,(2;k)} ≺ A^{-1/2} η_u⁻¹ (W^{-d}𝒯̃^L_{u,D})²`, `A = ilambda² W^d`.  `STLWT` stays a hypothesis (LW gate).

Route (sections).  1 the window `1/(2A) ≤ W^{-d}B_{u,0} ≤ 2/A` and the loss `ρ_u^{C_d} Δ_u^{1/5} ≤ 2 A^{-1/6}`
(`ρ_u ≤ ρ_t ≤ (2A)^{𝔠_d}`, `𝔠_d = min (1/100, 1/(30 C_d))`, so `𝔠_d C_d ≤ 1/30`); 2 the profile and the scale
family `K_u = min (L, (log W)^{10} ℓ_u)` (`ℓ = L` is admissible for `STLWT` only if `L ≤ (log W)^{10} ℓ_u`; one has
`𝒯̃^{K_u} = 𝒯̃^L` for large `W`); 3 `≺` glue; 4 `Ĵ^L ≺ A^{-1/6}` from `STGdecayW` at `D + 2d`, `ℰ^{LK×LK}` from the
deterministic `STNewKLKLAt` (`stNewKLKL_holds`) at `D + d` on the good event `‖G-M‖_max ≤ δ₀` (`STLocalEntryU`);
5-6 the slow variation of the control in `u` (factor `2` at the mesh `N^{-A}`) and the Hölder modulus of
`(ℰ⊗ℰ)^{M,(2;k)}`; 7 the sections: `STLWT`, `stEMn2Exp_holds` at `K_u` through the merged `ST_LW_sections`, `Ĵ^{K_u} ≤ Ĵ^L`;
8 the net lift (`cont_core`, Hölder moduli `LemDecCalELip_EGt`, `etermsMid_EEk_sub`); 9 the target; 10 instances.

Copies of private helpers (all inside RBM3D, no port from RBM1D/RBM2D): `etermsMid_nl_one_div_sqrt_diff`,
`_nl_ellT_diff`, `_nl_exp_ell`, `_nl_STWB_ratio` are `nl_one_div_sqrt_diff`, `nl_ellT_diff`, `nl_exp_ell`,
`nl_STWB_ratio` of `Path/NetLift1.lean:314-418` (`06b49b2`); `etermsMid_exp_half_le` is `nl_exp_half_le` (`:450`);
`etermsMid_STWB_le` is `lwExpTerm3_STWB_le` (`Graph/LWExpTerm3.lean:834`); `etermsMid_Wd_card` is
`lemDecCalELip_Wd_card` (`Induction/LemDecCalELip.lean:421`); `etermsMid_EEk_sub` is the per-`k` form of
`LemDecCalELip_ee_sub` (`:646`).

The import `RBM3D.Induction.LemDecCalELip` is not in the ticket's list: it is not in the import closure of
`EMn2Exp2`, `NewKLKL` (preflight finding F1) and supplies `LemDecCalELip_EGt`, `_env`, `_Lloop_sub` (paper-delta
candidates `T2328a-c` in the prove report).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Scalar facts: the window, the loss, the profile -/

section Scalar

variable {d : ℕ} (sz : Sizes d)

/-- In the window `ilambda²/L^d ≤ 1-u ≤ ilambda²`: `1/(2A) ≤ W^{-d}B_{u,0} ≤ 2/A`, `A = ilambda² W^d`. -/
private theorem etermsMid_Bctl_window (n : ℕ) {u : ℝ} (hg : 0 < sz.lam n)
    (hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u) (hhi : 1 - u ≤ sz.lam n ^ 2) :
    1 / (2 * STAI sz n) ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ 2 / STAI sz n := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hx : 0 < 1 - u := lt_of_lt_of_le (div_pos hg2 hLd) hlo
  have hlo' : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) := by
    rwa [div_le_iff₀ hLd, mul_comm] at hlo
  have hB : sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hx]
    simp
  have hA : STAI sz n = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := rfl
  rw [hB, hA]
  constructor
  · have h1 : (2 * sz.lam n ^ 2)⁻¹ ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by positivity
    calc 1 / (2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d))
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * sz.lam n ^ 2)⁻¹ := by
          field_simp
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hWd.le)
  · have h1 : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 hlo'
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (sz.lam n ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hWd.le)
      _ = 2 / (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by field_simp

end Scalar

/-- The loss `ρ^{C_d} (W^{-d}B_{u,0})^{1/5} ≤ 2 A^{-1/6}`: `ρ ≤ (2A)^{𝔠_d}`, `𝔠_d C_d ≤ 1/30`. -/
private theorem etermsMid_q_le {A ρ b bt Cd c : ℝ} (hA : 1 ≤ A) (hρ0 : 0 ≤ ρ)
    (hcC : c * Cd ≤ 1 / 30) (hc : 0 < c) (hCd : 0 < Cd)
    (hρ : ρ ≤ bt ^ (-c)) (hbt : 1 / (2 * A) ≤ bt) (hb : b ≤ 2 / A) (hb0 : 0 ≤ b) :
    ρ ^ Cd * b ^ (1 / 5 : ℝ) ≤ 2 * A ^ (-(1 / 6) : ℝ) := by
  have hA0 : 0 < A := by linarith
  have h2A : (1 : ℝ) ≤ 2 * A := by linarith
  have h1 : bt ^ (-c) ≤ (2 * A) ^ c := by
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 / (2 * A)) hbt
      (show -c ≤ 0 by linarith)
    refine h.trans (le_of_eq ?_)
    rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  have h3 : ρ ^ Cd ≤ (2 * A) ^ (1 / 30 : ℝ) := by
    calc ρ ^ Cd ≤ ((2 * A) ^ c) ^ Cd := Real.rpow_le_rpow hρ0 (hρ.trans h1) hCd.le
      _ = (2 * A) ^ (c * Cd) := by rw [← Real.rpow_mul (by positivity)]
      _ ≤ (2 * A) ^ (1 / 30 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2A hcC
  have h4 : b ^ (1 / 5 : ℝ) ≤ (2 / A) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hb0 hb (by norm_num)
  have h5 : (2 * A) ^ (1 / 30 : ℝ) * (2 / A) ^ (1 / 5 : ℝ) = 2 ^ (7 / 30 : ℝ) * A ^ (-(1 / 6) : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hA0.le, Real.div_rpow (by norm_num) hA0.le]
    have e1 : (2 : ℝ) ^ (7 / 30 : ℝ) = 2 ^ (1 / 30 : ℝ) * 2 ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have e2 : A ^ (-(1 / 6) : ℝ) = A ^ (1 / 30 : ℝ) / A ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_sub hA0]; norm_num
    rw [e1, e2]; ring
  have h6 : (2 : ℝ) ^ (7 / 30 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (7 / 30 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hAp : 0 ≤ A ^ (-(1 / 6) : ℝ) := Real.rpow_nonneg hA0.le _
  calc ρ ^ Cd * b ^ (1 / 5 : ℝ) ≤ (2 * A) ^ (1 / 30 : ℝ) * (2 / A) ^ (1 / 5 : ℝ) :=
        mul_le_mul h3 h4 (Real.rpow_nonneg hb0 _) (Real.rpow_nonneg (by positivity) _)
    _ = 2 ^ (7 / 30 : ℝ) * A ^ (-(1 / 6) : ℝ) := h5
    _ ≤ 2 * A ^ (-(1 / 6) : ℝ) := mul_le_mul_of_nonneg_right h6 hAp

/-! ## 2. The profile `W^{-d} 𝒯̃^ℓ_{u,D}` and the scale family `K_u = min (L, (log W)^{10} ℓ_u)` -/

section Profile

variable {d : ℕ} (sz : Sizes d)

/-- `W^{-d} B_{u,r} e^{-(r/ℓ_u)^{1/2}} ≤ W^{-d} 𝒯̃^L_{u,D}(r)` at the distance `r = |a-b|_L ≤ L`. -/
private theorem etermsMid_prof_main (n : ℕ) (u D : ℝ) (a b : Zd d (sz.L n)) :
    STWB sz n u (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤
      STprof sz n u D ((sz.L n : ℕ) : ℝ) a b := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρL := ST_zdistInf_le sz n (a - b)
  have h : tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ≤
      tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := by
    unfold tailW
    rw [min_eq_left hρL]
    exact le_max_left _ _
  have e : tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) =
      Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    unfold tailT
    rw [BparamR_natCast, Real.sqrt_eq_rpow]
  unfold STprof STWB
  rw [mul_assoc, ← e]
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 (pow_nonneg hW.le d))

/-- The profile decreases with the scale `ℓ`: `W^{-d} 𝒯̃^L ≤ W^{-d} 𝒯̃^ℓ` for `ℓ ≥ 0`. -/
private theorem etermsMid_prof_L_le (n : ℕ) (u D : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (a b : Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ≤ STprof sz n u D ℓ a b := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hρL := ST_zdistInf_le sz n (a - b)
  unfold STprof
  exact mul_le_mul_of_nonneg_left (ST_tailW_L_le (d := d) (L := sz.L n) hℓ hρ0 hρL)
    (inv_nonneg.mpr (pow_nonneg hW.le d))

/-- The profile decreases with `D` (for `W ≥ 1`). -/
private theorem etermsMid_prof_D_mono (n : ℕ) (u : ℝ) {D D' : ℝ} (ℓ : ℝ) (hW : 1 ≤ ((sz.W n : ℕ) : ℝ))
    (hDD : D ≤ D') (a b : Zd d (sz.L n)) :
    STprof sz n u D' ℓ a b ≤ STprof sz n u D ℓ a b := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  unfold STprof tailW
  refine mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) (inv_nonneg.mpr (pow_nonneg hW0.le d))
  exact Real.rpow_le_rpow_of_exponent_le hW (by linarith)

/-- The scale family `K_u = min (L, (log W)^{10} ℓ_u)` of the admissible range of `lem: EWGn2_N`
(`ℓ = L` itself is admissible only when `L ≤ (log W)^{10} ℓ_u`). -/
private def etermsMid_Kf (n : ℕ) (u : ℝ) : ℝ :=
  min ((sz.L n : ℕ) : ℝ) (Real.log ((sz.W n : ℕ) : ℝ) ^ 10 * ellT (sz.L n) (sz.lam n) u)

private theorem etermsMid_Kf_nonneg (n : ℕ) (u : ℝ) : 0 ≤ etermsMid_Kf sz n u :=
  le_min (Nat.cast_nonneg _) (mul_nonneg (by positivity) ellT_nonneg)

private theorem etermsMid_Kf_le (n : ℕ) (u : ℝ) :
    etermsMid_Kf sz n u ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 10 * ellT (sz.L n) (sz.lam n) u :=
  min_le_right _ _

private theorem etermsMid_Kf_le_L (n : ℕ) (u : ℝ) : etermsMid_Kf sz n u ≤ ((sz.L n : ℕ) : ℝ) :=
  min_le_left _ _

/-- **The scale `K_u` loses nothing** (`3_5:1961`: "at `ℓ = L`"): once `(d + D) log W ≤ (log W)^5` and
`W^{-d} B_{u,0} ≤ 1`, `𝒯̃^{K_u}_{u,D} = 𝒯̃^L_{u,D}` (`𝒯_u((log W)^{10} ℓ_u) ≤ W^d e^{-(log W)^5} ≤ W^{-D}`). -/
private theorem etermsMid_prof_Kf_le (n : ℕ) {u D : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ))
    (hlog : ((d : ℝ) + D) * Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 5)
    (hB : sz.Bctl n u ≤ 1) (a b : Zd d (sz.L n)) :
    STprof sz n u D (etermsMid_Kf sz n u) a b ≤ STprof sz n u D ((sz.L n : ℕ) : ℝ) a b := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hρL := ST_zdistInf_le sz n (a - b)
  by_cases h : ((sz.L n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 10 * ellT (sz.L n) (sz.lam n) u
  · have : etermsMid_Kf sz n u = ((sz.L n : ℕ) : ℝ) := min_eq_left h
    rw [this]
  · have hK : etermsMid_Kf sz n u = Real.log ((sz.W n : ℕ) : ℝ) ^ 10 * ellT (sz.L n) (sz.lam n) u :=
      min_eq_right (not_le.1 h).le
    set x : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hx
    have hx0 : 0 ≤ x := Real.log_nonneg hW.le
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    have hell : 0 < ellT (sz.L n) (sz.lam n) u := ellT_pos hL1
    have hK0 := etermsMid_Kf_nonneg sz n u
    -- `𝒯_u(K_u) ≤ W^{-D}`
    have hT : tailT d (sz.L n) (sz.lam n) u (etermsMid_Kf sz n u) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
      unfold tailT
      have hexp : Real.sqrt (etermsMid_Kf sz n u / ellT (sz.L n) (sz.lam n) u) = x ^ 5 := by
        rw [hK, mul_div_assoc, div_self hell.ne', mul_one,
          show x ^ 10 = (x ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      rw [hexp]
      have hB1 : BparamR d (sz.L n) (sz.lam n) u (etermsMid_Kf sz n u) ≤
          ((sz.W n : ℕ) : ℝ) ^ d := by
        have h0 := BparamR_antitone (d := d) (L := sz.L n) (g := sz.lam n) (t := u) (le_refl (0 : ℝ)) hK0
        have h00 : BparamR d (sz.L n) (sz.lam n) u 0 = ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n u := by
          have := BparamR_natCast (d := d) (L := sz.L n) (g := sz.lam n) (t := u) 0
          simp only [Nat.cast_zero] at this
          rw [this]
          unfold Sizes.Bctl
          field_simp
        have hWd : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW.le
        calc _ ≤ BparamR d (sz.L n) (sz.lam n) u 0 := h0
          _ = ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n u := h00
          _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * 1 := mul_le_mul_of_nonneg_left hB (by positivity)
          _ = _ := mul_one _
      have hWx : ((sz.W n : ℕ) : ℝ) = Real.exp x := by rw [hx, Real.exp_log hW0]
      calc BparamR d (sz.L n) (sz.lam n) u (etermsMid_Kf sz n u) * Real.exp (-x ^ 5)
          ≤ ((sz.W n : ℕ) : ℝ) ^ d * Real.exp (-x ^ 5) :=
            mul_le_mul_of_nonneg_right hB1 (Real.exp_pos _).le
        _ = Real.exp (d * x - x ^ 5) := by
            rw [hWx, ← Real.exp_nat_mul, sub_eq_add_neg, Real.exp_add]
        _ ≤ Real.exp (x * (-D)) := Real.exp_le_exp.2 (by nlinarith)
        _ = ((sz.W n : ℕ) : ℝ) ^ (-D) := by
            rw [Real.rpow_def_of_pos hW0]
    have hfin := ST_tailW_final (d := d) (L := sz.L n) (g := sz.lam n) (u := u) (W := ((sz.W n : ℕ) : ℝ))
      (D := D) (ρ := ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)) hK0 hT
    have hLeq : tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) =
        max (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))
          (((sz.W n : ℕ) : ℝ) ^ (-D)) := by
      unfold tailW
      rw [min_eq_left hρL]
    unfold STprof
    rw [hfin, hLeq]

end Profile

/-! ## 3. Glue for `≺` -/

section Glue

variable {d : ℕ} (sz : Sizes d)

/-- Two failure events: if on the intersection of the good events of `ξ₁ ≺ ζ₁` and `ξ₂ ≺ ζ₂` (at the exponent
`τ'`) a deterministic inequality gives `ξ ≤ N^τ ζ`, then `ξ ≺ ζ`. -/
private theorem etermsMid_prec_two {U U₁ U₂ : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    {ξ₁ ζ₁ : ∀ n, U₁ n → sz.SeqΩ → ℝ} {ξ₂ ζ₂ : ∀ n, U₂ n → sz.SeqΩ → ℝ}
    (hsize : Tendsto sz.size atTop atTop) (h₁ : sz.Prec ξ₁ ζ₁) (h₂ : sz.Prec ξ₂ ζ₂)
    (hdet : ∀ τ : ℝ, 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∀ᶠ n in atTop, ∀ ω : sz.SeqΩ,
      (∀ v, ξ₁ n v ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * ζ₁ n v ω) →
      (∀ w, ξ₂ n w ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * ζ₂ n w ω) →
      ∀ u, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω) : sz.Prec ξ ζ := by
  refine StochDomAt.of_subset_union hsize h₁ h₂ fun τ hτ => ?_
  obtain ⟨τ', hτ', h⟩ := hdet τ hτ
  refine ⟨τ', hτ', ?_⟩
  filter_upwards [h] with n hn ω hω
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨u, hu⟩ := hω
  exact absurd (hn ω hno.1 hno.2 u) (not_le.2 hu)

/-- A failure event contained in that of another family with another index set. -/
private theorem etermsMid_of_subset {U U₁ : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    {ξ₁ ζ₁ : ∀ n, U₁ n → sz.SeqΩ → ℝ} (h : sz.Prec ξ₁ ζ₁)
    (hsub : ∀ τ : ℝ, 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∀ᶠ n in atTop,
      badSetAt sz.size ξ ζ τ n ⊆ badSetAt sz.size ξ₁ ζ₁ τ' n) : sz.Prec ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with n h1 h2
  exact (measure_mono h1).trans h2

/-- One failure event: a deterministic comparison `ξ ≤ ξ₁ + b`, `b ≤ K ζ`, `ζ₁ ≤ K ζ` and `ξ₁ ≺ ζ₁` give `ξ ≺ ζ`. -/
private theorem etermsMid_prec_lin {U : ℕ → Type*} {ξ ζ ξ₁ ζ₁ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hsize : Tendsto sz.size atTop atTop) (h₁ : sz.Prec ξ₁ ζ₁) {b : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ξ₁ n u ω + b n u ω) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᶠ n in atTop, ∀ u ω, b n u ω ≤ K * ζ n u ω)
    (hζ : ∀ᶠ n in atTop, ∀ u ω, ζ₁ n u ω ≤ K * ζ n u ω) (hζ0 : ∀ n u ω, 0 ≤ ζ n u ω) :
    sz.Prec ξ ζ := by
  refine StochDomAt.of_subset h₁ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hξ, hb, hζ, ST_size_pow_big sz hsize (a := τ / 2) (M := 2 * K) (half_pos hτ),
    hsize.eventually (eventually_ge_atTop 1)] with n hξn hbn hζn hN hN1
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hx1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (half_pos hτ).le
  have h1 := hno u
  have hz := hζ0 n u ω
  have e : ((sz.size n : ℕ) : ℝ) ^ τ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have h2 : ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (K * ζ n u ω) + K * ζ n u ω :=
    (hξn u ω).trans (add_le_add (h1.trans (mul_le_mul_of_nonneg_left (hζn u ω) (by linarith))) (hbn u ω))
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (K * ζ n u ω) + K * ζ n u ω ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
    rw [e]
    set x : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)
    have hKz : 0 ≤ K * ζ n u ω := mul_nonneg hK hz
    nlinarith [mul_le_mul_of_nonneg_right hN hz, mul_nonneg (sub_nonneg.2 hx1) hKz,
      mul_nonneg (sub_nonneg.2 hN) hz]
  exact absurd (lt_of_lt_of_le hu (h2.trans h3)) (lt_irrefl _)

end Glue

/-! ## 4. The control `Ĵ^L ≺ A^{-1/6}` from `(Eq:Gdecay_w)` -/

section Control

variable {d : ℕ} (sz : Sizes d)

/-- `A = ilambda² W^d` is eventually larger than every constant (`(eq:WO)`: `A ≥ W^{2𝔡}`, `W → ∞`). -/
private theorem etermsMid_A_big {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (M : ℝ) :
    ∀ᶠ n in atTop, M ≤ STAI sz n := by
  obtain ⟨h𝔠, h𝔡, hsz, hband, hWO⟩ := hA
  have hWt := ST_W_tendsto sz hsz h𝔠 hband
  have h1 : Tendsto (fun n => ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 * 𝔡)).comp hWt
  filter_upwards [h1.eventually (eventually_ge_atTop M), hWO] with n hn hwo
  exact hn.trans (sz.lam_sq_mul_pow_ge n hwo.1)

/-- `0 < ilambda ≤ 𝔡⁻¹` and `W ≥ 1`, eventually. -/
private theorem etermsMid_lam {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hA.2.2.2.2] with n hn
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩

/-- The loss in the window: `((1-s)/(1-u))^{C_d} (W^{-d}B_{u,0})^{1/5} ≤ 2 A^{-1/6}`
(`ρ_u ≤ ρ_t ≤ (W^{-d}B_{t,0})^{-𝔠_d} ≤ (2A)^{𝔠_d}`, `𝔠_d C_d ≤ 1/30`). -/
private theorem etermsMid_loss (n : ℕ) {s t u 𝔠d Cd : ℝ} (hlam : 0 < sz.lam n) (hA : 1 ≤ STAI sz n)
    (hRegt : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t) (hRegs : 1 - s ≤ sz.lam n ^ 2)
    (hsu : s ≤ u) (hut : u ≤ t) (hcon : sz.Bctl n t ^ 𝔠d ≤ (1 - t) / (1 - s))
    (h𝔠d : 0 < 𝔠d) (hCd : 0 < Cd) (hcC : 𝔠d * Cd ≤ 1 / 30) :
    0 ≤ ((1 - s) / (1 - u)) ^ Cd * sz.Bctl n u ^ (1 / 5 : ℝ) ∧
      ((1 - s) / (1 - u)) ^ Cd * sz.Bctl n u ^ (1 / 5 : ℝ) ≤ 2 * STAI sz n ^ (-(1 / 6) : ℝ) := by
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have ht1 : 0 < 1 - t := lt_of_lt_of_le (div_pos hg2 hLd) hRegt
  have hu1 : 0 < 1 - u := by linarith
  have hs1 : 0 < 1 - s := by linarith
  have hwt := etermsMid_Bctl_window sz n hlam hRegt (by linarith)
  have hwu := etermsMid_Bctl_window sz n (u := u) hlam (hRegt.trans (by linarith)) (by linarith)
  have hA0 : 0 < STAI sz n := by linarith
  have hbt : 0 < sz.Bctl n t := lt_of_lt_of_le (by positivity) hwt.1
  have hbu : 0 ≤ sz.Bctl n u := (lt_of_lt_of_le (by positivity) hwu.1).le
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := by positivity
  refine ⟨mul_nonneg (Real.rpow_nonneg hρ0 _) (Real.rpow_nonneg hbu _), ?_⟩
  refine etermsMid_q_le hA hρ0 hcC h𝔠d hCd ?_ hwt.1 hwu.2 hbu
  calc (1 - s) / (1 - u) ≤ (1 - s) / (1 - t) :=
        div_le_div_of_nonneg_left hs1.le ht1 (by linarith)
    _ = ((1 - t) / (1 - s))⁻¹ := (inv_div _ _).symm
    _ ≤ (sz.Bctl n t ^ 𝔠d)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hbt _) hcon
    _ = sz.Bctl n t ^ (-𝔠d) := (Real.rpow_neg hbt.le _).symm

/-- `Θ_n = 2 A^{-1/6} + W^{-d}`: the control of `Ĵ^L` (`W^{-d}` is the floor `W^{-D₁}` of `(Eq:Gdecay_w)`). -/
private def etermsMid_Theta (n : ℕ) : ℝ := 2 * STAI sz n ^ (-(1 / 6) : ℝ) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹

private theorem etermsMid_Theta_nonneg (n : ℕ) : 0 ≤ etermsMid_Theta sz n := by
  unfold etermsMid_Theta STAI
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  positivity

/-- The scalar comparison of `(Eq:Gdecay_w)` at `D₁ = D + 2d` with `Θ W^{-d} 𝒯̃^L_{u,D}`. -/
private theorem etermsMid_J_scalar (n : ℕ) {u D q : ℝ} (hq : q ≤ 2 * STAI sz n ^ (-(1 / 6) : ℝ))
    (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) (a b : Zd d (sz.L n)) :
    q * STWB sz n u (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-(D + 2 * (d : ℝ))) ≤
    etermsMid_Theta sz n * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hM := etermsMid_prof_main sz n u D a b
  have hF := ST_prof_lower sz n u D ((sz.L n : ℕ) : ℝ) a b
  have hWB : 0 ≤ STWB sz n u (zdistInf d (sz.L n) (a - b)) := by
    unfold STWB Bparam
    have : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by positivity
    have h2 : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
    have h3 : 0 ≤ ((((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    positivity
  have hE0 : 0 ≤ Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) :=
    (Real.exp_pos _).le
  have hP0 : 0 ≤ STprof sz n u D ((sz.L n : ℕ) : ℝ) a b := (ST_STprof_pos sz n u D _ a b).le
  have hfl : ((sz.W n : ℕ) : ℝ) ^ (-(D + 2 * (d : ℝ))) =
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D)) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    have e : -(D + 2 * (d : ℝ)) = -D + (-(d : ℝ)) + (-(d : ℝ)) := by ring
    have hd1 : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
      rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
    rw [e, Real.rpow_add hW0, Real.rpow_add hW0, hd1]
    ring
  have hA6 : 0 ≤ STAI sz n ^ (-(1 / 6) : ℝ) := by
    unfold STAI
    have : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hW0.le
    exact Real.rpow_nonneg (by positivity) _
  have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have h1 : q * STWB sz n u (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤
      (2 * STAI sz n ^ (-(1 / 6) : ℝ)) * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b := by
    calc _ = q * (STWB sz n u (zdistInf d (sz.L n) (a - b)) *
          Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ))) := by ring
      _ ≤ (2 * STAI sz n ^ (-(1 / 6) : ℝ)) * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b :=
        mul_le_mul hq hM (mul_nonneg hWB hE0) (by positivity)
  have h2 : ((sz.W n : ℕ) : ℝ) ^ (-(D + 2 * (d : ℝ))) ≤
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b := by
    rw [hfl]
    calc _ ≤ STprof sz n u D ((sz.L n : ℕ) : ℝ) a b * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ :=
          mul_le_mul_of_nonneg_right hF hWd
      _ = _ := mul_comm _ _
  unfold etermsMid_Theta
  nlinarith [h1, h2]

/-- **`Ĵ^L_{u,D} ≺ A^{-1/6}`, uniformly in `u ∈ [s,t]`** (`(eq:Step2_inputs)`, `3_5:1340-1357`): from
`(Eq:Gdecay_w)` at `D + 2d` (`STGdecayW`) and `ρ^{C_d} Δ^{1/5} ≤ 2 A^{-1/6}` (`𝔠_d C_d ≤ 1/30`),
`|𝓛-𝒦|^{(2)}_{u,σ,a} ≺ Θ W^{-d} 𝒯̃^L_{u,D}(|a₁-a₂|)`, `Θ = 2A^{-1/6} + W^{-d}`. -/
private theorem etermsMid_J {E s t : ℕ → ℝ} {Cd 𝔠d 𝔠 𝔡 : ℝ} (hAd : sz.Admissible 𝔠 𝔡)
    (hReg : STReg5Mid sz s t) (hCon : STConStInd sz 𝔠d s t) (h𝔠d : 0 < 𝔠d) (hCd : 0 < Cd)
    (hcC : 𝔠d * Cd ≤ 1 / 30) (hGd : STGdecayW sz E s t Cd) {D : ℝ} (hD : 0 < D) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => etermsMid_Theta sz n *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ST_prec_mono_eventually sz ?_ (hGd (D + 2 * (d : ℝ)) (by linarith))
  filter_upwards [etermsMid_lam sz hAd, etermsMid_A_big sz hAd 1, hCon] with n hl hA1 hcon p ω
  obtain ⟨⟨u, hsu, hut⟩, σ, a⟩ := p
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hloss := etermsMid_loss sz n hl.1 hA1 (hReg n).1 (hReg n).2 hsu hut hcon.1 h𝔠d hCd hcC
  exact etermsMid_J_scalar sz n hloss.2 hW1 (a 0) (a 1)

/-- `W^{-d} ≤ 𝔡^{-1/3} A^{-1/6}` (`A = ilambda² W^d ≤ 𝔡⁻² W^d`, `W ≥ 1`). -/
private theorem etermsMid_Wd_le (n : ℕ) {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hl : 0 < sz.lam n) (hl' : sz.lam n ≤ 𝔡⁻¹)
    (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (𝔡⁻¹) ^ (1 / 3 : ℝ) * STAI sz n ^ (-(1 / 6) : ℝ) := by
  set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hX
  have hX1 : 1 ≤ X := one_le_pow₀ hW
  have hX0 : 0 < X := by linarith
  have hA0 : 0 < STAI sz n := by
    unfold STAI; rw [← hX]; positivity
  have hAle : STAI sz n ≤ (𝔡⁻¹) ^ 2 * X := by
    unfold STAI; rw [← hX]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl.le hl' 2) hX0.le
  have h1 : X⁻¹ ≤ X ^ (-(1 / 6) : ℝ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have h2 : ((𝔡⁻¹) ^ 2 * X) ^ (-(1 / 6) : ℝ) ≤ STAI sz n ^ (-(1 / 6) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hA0 hAle (by norm_num)
  have hc : 0 < (𝔡⁻¹) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (inv_pos.2 h𝔡) _
  have h3 : ((𝔡⁻¹) ^ 2 * X) ^ (-(1 / 6) : ℝ) = ((𝔡⁻¹) ^ (1 / 3 : ℝ))⁻¹ * X ^ (-(1 / 6) : ℝ) := by
    have hb : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
    rw [Real.mul_rpow (by positivity) hX0.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le, ← Real.rpow_neg hb.le]
    congr 1; norm_num
  have h4 : X ^ (-(1 / 6) : ℝ) = (𝔡⁻¹) ^ (1 / 3 : ℝ) * ((𝔡⁻¹) ^ 2 * X) ^ (-(1 / 6) : ℝ) := by
    rw [h3]; field_simp
  calc X⁻¹ ≤ X ^ (-(1 / 6) : ℝ) := h1
    _ = (𝔡⁻¹) ^ (1 / 3 : ℝ) * ((𝔡⁻¹) ^ 2 * X) ^ (-(1 / 6) : ℝ) := h4
    _ ≤ (𝔡⁻¹) ^ (1 / 3 : ℝ) * STAI sz n ^ (-(1 / 6) : ℝ) := mul_le_mul_of_nonneg_left h2 hc.le

/-- `(1-u)⁻¹ ≤ η_u⁻¹` (`η_u = (1-u) Im m(E)`, `Im m(E) ≤ 1`). -/
private theorem etermsMid_inv_le_eta {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) :
    (1 - u)⁻¹ ≤ (etaT E u)⁻¹ := by
  have hm := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  have h1 : 0 < 1 - u := by linarith
  unfold etaT
  refine inv_anti₀ (mul_pos h1 hm) ?_
  nlinarith

/-- **`ℰ^{LK×LK}` pathwise** (`(S5WG+M000)`, `3_5:1961-1968`): at a Hermitian `H` with `‖G_u - M‖_max ≤ δ₀` and
`|(𝓛-𝒦)^{(2)}| ≤ X Θ W^{-d} 𝒯̃^L_{u,D+d}`: `|ℰ^{LK×LK}| ≤ C/(1-u) X² (C₀² + C₀ C₁) A^{-1/3} W^{-d} 𝒯̃^L_{u,D}`
(`STNewKLKLAt` at `D + d`, the floor `Ĵ W^{-2d-D}` is absorbed by `W^{-d} ≤ C₁ A^{-1/6}`). -/
private theorem etermsMid_ELKLK_det (n : ℕ) {κ' 𝔡 C δ₀ E u D X C₀ C₁ : ℝ}
    (hnew : STNewKLKLAt d κ' 𝔡 C δ₀) (hC : 0 < C) (hl : 0 < sz.lam n) (hl' : sz.lam n ≤ 𝔡⁻¹)
    (hE : |E| ≤ 2 - κ') (hu0 : 0 ≤ u) (hu1 : u < 1) (hD : 0 ≤ D) (hW : 1 ≤ ((sz.W n : ℕ) : ℝ))
    (hX : 1 ≤ X) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hΘ : etermsMid_Theta sz n ≤ C₀ * STAI sz n ^ (-(1 / 6) : ℝ))
    (hW' : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₁ * STAI sz n ^ (-(1 / 6) : ℝ))
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (hGM : ∀ x y, ‖STGMM sz n E u H x y‖ ≤ δ₀)
    (hLK : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKM sz n E u H σ a‖ ≤
      X * etermsMid_Theta sz n * STprof sz n u (D + d) ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STELKLKM sz n E u H σ a‖ ≤ C * (1 - u)⁻¹ *
      (X ^ 2 * ((C₀ ^ 2 + C₀ * C₁) * (STAI sz n ^ (-(1 / 6) : ℝ)) ^ 2)) *
        STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have h := hnew sz n E u (D + d) hl hl' hE hu0 hu1 (by linarith) H hH hGM σ a
  set J : ℝ := STJhatM sz n E (D + d) ((sz.L n : ℕ) : ℝ) u H with hJdef
  set Θ : ℝ := etermsMid_Theta sz n with hΘdef
  set a6 : ℝ := STAI sz n ^ (-(1 / 6) : ℝ) with ha6
  set P : ℝ := STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) with hPdef
  set Wi : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWi
  have hΘ0 : 0 ≤ Θ := etermsMid_Theta_nonneg sz n
  have hJ0 : 0 ≤ J := ST_JhatM_nonneg sz n E (D + d) _ u H
  have hX0 : 0 ≤ X := by linarith
  have hx0 : 0 ≤ X * Θ := mul_nonneg hX0 hΘ0
  have hJ : J ≤ X * Θ := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    rw [div_le_iff₀ (ST_STprof_pos sz n u (D + d) _ (p.2 0) (p.2 1))]
    exact hLK p.1 p.2
  have hP0 : 0 ≤ P := (ST_STprof_pos sz n u D _ (a 0) (a 1)).le
  have hPN0 : 0 ≤ STprof sz n u (D + d) ((sz.L n : ℕ) : ℝ) (a 0) (a 1) :=
    (ST_STprof_pos sz n u (D + d) _ (a 0) (a 1)).le
  have hPN : STprof sz n u (D + d) ((sz.L n : ℕ) : ℝ) (a 0) (a 1) ≤ P :=
    etermsMid_prof_D_mono sz n u _ hW (by linarith) (a 0) (a 1)
  have hF : Wi * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ P := ST_prof_lower sz n u D _ (a 0) (a 1)
  have hWi0 : 0 ≤ Wi := by rw [hWi]; positivity
  have hfl : ((sz.W n : ℕ) : ℝ) ^ (-(D + d)) = ((sz.W n : ℕ) : ℝ) ^ (-D) * Wi := by
    have e : -(D + (d : ℝ)) = -D + (-(d : ℝ)) := by ring
    have hd1 : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) = Wi := by
      rw [hWi, Real.rpow_neg hW0.le, Real.rpow_natCast]
    rw [e, Real.rpow_add hW0, hd1]
  have hWD0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  -- the two terms
  have t1 : J ^ 2 * STprof sz n u (D + d) ((sz.L n : ℕ) : ℝ) (a 0) (a 1) ≤ (X * Θ) ^ 2 * P :=
    mul_le_mul (pow_le_pow_left₀ hJ0 hJ 2) hPN hPN0 (by positivity)
  have t2 : J * Wi * ((sz.W n : ℕ) : ℝ) ^ (-(D + d)) ≤ (X * Θ) * (P * Wi) := by
    rw [hfl]
    calc J * Wi * (((sz.W n : ℕ) : ℝ) ^ (-D) * Wi)
        = J * ((Wi * ((sz.W n : ℕ) : ℝ) ^ (-D)) * Wi) := by ring
      _ ≤ (X * Θ) * ((Wi * ((sz.W n : ℕ) : ℝ) ^ (-D)) * Wi) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
      _ ≤ (X * Θ) * (P * Wi) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hF hWi0) hx0
  -- sizes of `X Θ` and `Wi`
  have hxa : X * Θ ≤ X * (C₀ * a6) := mul_le_mul_of_nonneg_left hΘ hX0
  have ha60 : 0 ≤ a6 := by
    rw [ha6]; unfold STAI
    exact Real.rpow_nonneg (by positivity) _
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hsum : (X * Θ) ^ 2 * P + (X * Θ) * (P * Wi) ≤
      (X ^ 2 * ((C₀ ^ 2 + C₀ * C₁) * a6 ^ 2)) * P := by
    have h1 : (X * Θ) ^ 2 ≤ (X * (C₀ * a6)) ^ 2 := pow_le_pow_left₀ hx0 hxa 2
    have h2 : (X * Θ) * Wi ≤ (X * (C₀ * a6)) * (C₁ * a6) :=
      mul_le_mul hxa hW' hWi0 (by positivity)
    have h3 : (X * (C₀ * a6)) * (C₁ * a6) ≤ X ^ 2 * (C₀ * C₁ * a6 ^ 2) := by
      calc (X * (C₀ * a6)) * (C₁ * a6) = X * (C₀ * C₁ * a6 ^ 2) := by ring
        _ ≤ X ^ 2 * (C₀ * C₁ * a6 ^ 2) := mul_le_mul_of_nonneg_right hXX (by positivity)
    have h4 : (X * (C₀ * a6)) ^ 2 = X ^ 2 * (C₀ ^ 2 * a6 ^ 2) := by ring
    calc (X * Θ) ^ 2 * P + (X * Θ) * (P * Wi) = ((X * Θ) ^ 2 + (X * Θ) * Wi) * P := by ring
      _ ≤ (X ^ 2 * (C₀ ^ 2 * a6 ^ 2) + X ^ 2 * (C₀ * C₁ * a6 ^ 2)) * P :=
          mul_le_mul_of_nonneg_right (by linarith) hP0
      _ = _ := by ring
  have hC1u : 0 ≤ C / (1 - u) := div_nonneg hC.le (by linarith)
  calc ‖STELKLKM sz n E u H σ a‖ ≤ C / (1 - u) * (J ^ 2 * STprof sz n u (D + d) ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
        J * Wi * ((sz.W n : ℕ) : ℝ) ^ (-(D + d))) := h
    _ ≤ C / (1 - u) * ((X * Θ) ^ 2 * P + (X * Θ) * (P * Wi)) :=
        mul_le_mul_of_nonneg_left (add_le_add t1 t2) hC1u
    _ ≤ C / (1 - u) * ((X ^ 2 * ((C₀ ^ 2 + C₀ * C₁) * a6 ^ 2)) * P) :=
        mul_le_mul_of_nonneg_left hsum hC1u
    _ = C * (1 - u)⁻¹ * (X ^ 2 * ((C₀ ^ 2 + C₀ * C₁) * a6 ^ 2)) * P := by
        rw [div_eq_mul_inv]; ring

/-- `A^{-1/3} = (A^{-1/6})²`, `A^{-1/2} = (A^{-1/6})³`. -/
private theorem etermsMid_rpow_sq {A : ℝ} (hA : 0 ≤ A) : A ^ (-(1 / 3) : ℝ) = (A ^ (-(1 / 6) : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA]; norm_num

private theorem etermsMid_rpow_cube {A : ℝ} (hA : 0 ≤ A) : A ^ (-(1 / 2) : ℝ) = (A ^ (-(1 / 6) : ℝ)) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA]; norm_num

/-- `W^{-d} B_{u,K} ≤ W^{-d} B_{u,0}` (copy of `lwExpTerm3_STWB_le`, `Graph/LWExpTerm3.lean:834`). -/
private theorem etermsMid_STWB_le (n : ℕ) (u : ℝ) (K : ℕ) : STWB sz n u K ≤ sz.Bctl n u := by
  unfold STWB Sizes.Bctl Bparam
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ (d - 2) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
  have h2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hA : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
  have h3 : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h2 hA]

/-- **`ℰ^{LK×LK} ≺ A^{-1/3} η_u⁻¹ W^{-d} 𝒯̃^L_{u,D}`** (`(S5WG+M000)`, `3_5:1961-1968`), uniformly in `u ∈ [s,t]`:
the good event `‖G_u - M‖_max ≤ δ₀` (`STLocalEntryU`, `STWB ≤ N^{-c}`) and `Ĵ^L_{D+d} ≺ A^{-1/6}`
(`etermsMid_J`) feed the deterministic `STNewKLKLAt` (`etermsMid_ELKLK_det`). -/
private theorem etermsMid_A_prec {E s t : ℕ → ℝ} {Cd 𝔠d 𝔠 𝔡 κ' C δ₀ c : ℝ} (hAd : sz.Admissible 𝔠 𝔡)
    (hReg : STReg5Mid sz s t) (hCon : STConStInd sz 𝔠d s t) (h𝔠d : 0 < 𝔠d) (hCd : 0 < Cd)
    (hcC : 𝔠d * Cd ≤ 1 / 30) (hGd : STGdecayW sz E s t Cd) (hLoc : STLocalEntryU sz E s t)
    (hnew : STNewKLKLAt d κ' 𝔡 C δ₀) (hC : 0 < C) (hδ₀ : 0 < δ₀) (hE : ∀ n, |E n| ≤ 2 - κ')
    (hE2 : ∀ n, |E n| < 2) (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (h𝔡 : 0 < 𝔡) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    {D : ℝ} (hD : 0 < D) :
    sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 3) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) := by
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hAd.2.2.1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set C₁ : ℝ := (𝔡⁻¹) ^ (1 / 3 : ℝ) with hC₁def
  have hC₁ : 0 < C₁ := Real.rpow_pos_of_pos (inv_pos.2 h𝔡) _
  set C₀ : ℝ := 2 + C₁ with hC₀def
  have hC₀ : 0 < C₀ := by linarith
  have hJ := etermsMid_J sz hAd hReg hCon h𝔠d hCd hcC hGd (D := D + d) (by linarith)
  refine etermsMid_prec_two sz hsize hLoc hJ ?_
  intro τ hτ
  refine ⟨min (τ / 4) (c / 2), lt_min (by linarith) (by linarith), ?_⟩
  filter_upwards [etermsMid_lam sz hAd, hBd, ST_size_pow_small sz hsize (a := -c / 2) (δ := δ₀ ^ 2)
    (by linarith) (by positivity), ST_size_pow_big sz hsize (a := τ / 2) (M := C * (C₀ ^ 2 + C₀ * C₁))
    (by linarith), hsize.eventually (eventually_ge_atTop 1)] with n hl hB hsmall hbig hN1
  intro ω hξ₁ hξ₂ p
  obtain ⟨⟨u, hsu, hut⟩, σ, a⟩ := p
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set τ' : ℝ := min (τ / 4) (c / 2) with hτ'
  have hτ'1 : τ' ≤ τ / 4 := min_le_left _ _
  have hτ'2 : τ' ≤ c / 2 := min_le_right _ _
  have hτ'0 : 0 < τ' := lt_min (by linarith) (by linarith)
  set X : ℝ := ((sz.size n : ℕ) : ℝ) ^ τ' with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1' hτ'0.le
  have hX2 : X ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by push_cast; linarith)
  have hu0 : 0 ≤ u := (hs n).trans hsu
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht1 n)
  -- the weak law at `u`
  have hGM : ∀ x y, ‖STGMM sz n (E n) u (sz.seqHflow n u ω) x y‖ ≤ δ₀ := by
    intro x y
    have h1 := hξ₁ (⟨u, hsu, hut⟩, x, y)
    have h2 := etermsMid_STWB_le sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
    have h3 := (hB u hu0 hut)
    have h4 : ((sz.size n : ℕ) : ℝ) ^ τ' * ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ δ₀ ^ 2 := by
      calc _ = ((sz.size n : ℕ) : ℝ) ^ (τ' + -c) := (Real.rpow_add hN0 _ _).symm
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-c / 2) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
        _ ≤ δ₀ ^ 2 := hsmall
    have h5 : ‖STGM sz n (E n) u ω x y‖ ^ 2 ≤ δ₀ ^ 2 := by
      refine h1.trans ?_
      refine le_trans (mul_le_mul_of_nonneg_left (h2.trans h3) (Real.rpow_nonneg hN0.le _)) h4
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ₀.le (by norm_num)).1 h5
  -- the control of `𝓛 - 𝒦`
  have hLK : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Zd d (sz.L n)),
      ‖STLKM sz n (E n) u (sz.seqHflow n u ω) σ' a'‖ ≤
        X * etermsMid_Theta sz n * STprof sz n u (D + d) ((sz.L n : ℕ) : ℝ) (a' 0) (a' 1) := by
    intro σ' a'
    have h1 := hξ₂ (⟨u, hsu, hut⟩, σ', a')
    have e : STLKM sz n (E n) u (sz.seqHflow n u ω) σ' a' =
        Lloop sz n (E n) u σ' a' ω - STKloop sz n (E n) u σ' a' := by
      unfold STLKM; rw [STLM_seqHflow]
    rw [e]
    refine h1.trans (le_of_eq ?_)
    ring
  obtain ⟨hΘC, hWC⟩ : etermsMid_Theta sz n ≤ C₀ * STAI sz n ^ (-(1 / 6) : ℝ) ∧
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₁ * STAI sz n ^ (-(1 / 6) : ℝ) := by
    have h := etermsMid_Wd_le sz n h𝔡 hl.1 hl.2 hW1
    refine ⟨?_, h⟩
    unfold etermsMid_Theta
    rw [hC₀def]; linarith
  have hdet := etermsMid_ELKLK_det sz n hnew hC hl.1 hl.2 (hE n) hu0 hu1 hD.le hW1 hX1 hC₀.le hC₁.le hΘC hWC
    (seqHflow_isHermitian sz n u ω) hGM hLK σ a
  have hηle := etermsMid_inv_le_eta (hE2 n) hu1
  have hA0 : 0 ≤ STAI sz n := by unfold STAI; positivity
  have ha6 : 0 ≤ STAI sz n ^ (-(1 / 6) : ℝ) := Real.rpow_nonneg hA0 _
  have hP0 := (ST_STprof_pos sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)).le
  have hKC : 0 ≤ C₀ ^ 2 + C₀ * C₁ := by positivity
  change ‖STELKLKM sz n (E n) u (sz.seqHflow n u ω) σ a‖ ≤ _
  refine hdet.trans ?_
  change _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(1 / 3) : ℝ) * (etaT (E n) u)⁻¹ *
    STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
  rw [etermsMid_rpow_sq hA0]
  have hNτ : ((sz.size n : ℕ) : ℝ) ^ τ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hCK : C * (C₀ ^ 2 + C₀ * C₁) * X ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [hNτ]
    exact mul_le_mul hbig hX2 (by positivity) (Real.rpow_nonneg hN0.le _)
  have hη0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  calc C * (1 - u)⁻¹ * (X ^ 2 * ((C₀ ^ 2 + C₀ * C₁) * (STAI sz n ^ (-(1 / 6) : ℝ)) ^ 2)) *
        STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
      = (C * (C₀ ^ 2 + C₀ * C₁) * X ^ 2) * ((1 - u)⁻¹ * (STAI sz n ^ (-(1 / 6) : ℝ)) ^ 2 *
        STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((STAI sz n ^ (-(1 / 6) : ℝ)) ^ 2 * (etaT (E n) u)⁻¹ *
        STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)) := by
        refine mul_le_mul hCK ?_ (by positivity) (Real.rpow_nonneg hN0.le _)
        calc (1 - u)⁻¹ * (STAI sz n ^ (-(1 / 6) : ℝ)) ^ 2 * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
            = (STAI sz n ^ (-(1 / 6) : ℝ)) ^ 2 * (1 - u)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by ring
          _ ≤ (STAI sz n ^ (-(1 / 6) : ℝ)) ^ 2 * (etaT (E n) u)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηle (by positivity)) hP0
    _ = _ := rfl

end Control

/-! ## 5. Slow variation of the control in the time (for the net lift) -/

section Cont

open RBM.Ind.ContinuityNet

/-- `|(1-u)^{-1/2} - (1-u')^{-1/2}| ≤ (1-t)⁻¹ |u-u'|^{1/2}` for `u, u' ≤ t < 1`.
`NetLift:884` (`netLift_one_div_sqrt_diff`). -/
private theorem etermsMid_nl_one_div_sqrt_diff {t u u' : ℝ} (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t) :
    |1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - u')| ≤ (1 - t)⁻¹ * Real.sqrt |u - u'| := by
  have h1t : 0 < 1 - t := by linarith
  have hx : 0 < 1 - u := by linarith
  have hx' : 0 < 1 - u' := by linarith
  have ha0 : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx
  have hb0 : 0 < Real.sqrt (1 - u') := Real.sqrt_pos.2 hx'
  have hab : 1 - t ≤ Real.sqrt (1 - u) * Real.sqrt (1 - u') := by
    have hta : Real.sqrt (1 - t) ≤ Real.sqrt (1 - u) := Real.sqrt_le_sqrt (by linarith)
    have htb : Real.sqrt (1 - t) ≤ Real.sqrt (1 - u') := Real.sqrt_le_sqrt (by linarith)
    calc 1 - t = Real.sqrt (1 - t) * Real.sqrt (1 - t) := (Real.mul_self_sqrt h1t.le).symm
      _ ≤ _ := mul_le_mul hta htb (Real.sqrt_nonneg _) ha0.le
  have heq : 1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - u') =
      (Real.sqrt (1 - u') - Real.sqrt (1 - u)) / (Real.sqrt (1 - u) * Real.sqrt (1 - u')) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0)]
  have hba : |Real.sqrt (1 - u') - Real.sqrt (1 - u)| ≤ Real.sqrt |u - u'| := by
    have h := cont_abs_sqrt_sub_sqrt_le hx'.le hx.le
    have h2 : |(1 - u') - (1 - u)| = |u - u'| := by
      rw [show (1 - u') - (1 - u) = -(u' - u) by ring, abs_neg, abs_sub_comm]
    rwa [h2] at h
  calc |Real.sqrt (1 - u') - Real.sqrt (1 - u)| / (Real.sqrt (1 - u) * Real.sqrt (1 - u'))
      ≤ Real.sqrt |u - u'| / (1 - t) := by gcongr
    _ = (1 - t)⁻¹ * Real.sqrt |u - u'| := by rw [div_eq_inv_mul]

/-- The range `ℓ_u` is Hölder-`1/2` in `u`: `|ℓ_u - ℓ_{u'}| ≤ ĝ (1-t)⁻¹ |u-u'|^{1/2}` (`ĝ ≥ 0`).
`NetLift:909` (`netLift_ellT_diff`); new: `ellT` carries the coupling `ĝ`. -/
private theorem etermsMid_nl_ellT_diff {L : ℕ} {g t u u' : ℝ} (hg : 0 ≤ g) (ht : t < 1) (hut : u ≤ t)
    (hu't : u' ≤ t) :
    |ellT L g u - ellT L g u'| ≤ g * ((1 - t)⁻¹ * Real.sqrt |u - u'|) := by
  have hx : 0 < 1 - u := by linarith
  have hx' : 0 < 1 - u' := by linarith
  unfold ellT
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le ?_ (by have := Real.sqrt_nonneg |u - u'|; positivity)
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le ?_ (by have := Real.sqrt_nonneg |u - u'|; positivity)
  rw [abs_of_pos hx, abs_of_pos hx']
  have e : g / Real.sqrt (1 - u) - g / Real.sqrt (1 - u') =
      g * (1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - u')) := by ring
  rw [e, abs_mul, abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left (etermsMid_nl_one_div_sqrt_diff ht hut hu't) hg

/-- `e^{-√(z/ℓ_{u'})} ≤ e^{δ} e^{-√(z/ℓ_u)}` with `δ = √(z ĝ (1-t)⁻¹ |u-u'|^{1/2})`
(`ℓ ≥ 1`, `z ≥ 0`).  `NetLift:916` (`netLift_exp_ell_diff`), multiplicative form. -/
private theorem etermsMid_nl_exp_ell {L : ℕ} (hL : 1 ≤ L) {g t u u' z : ℝ} (hg : 0 ≤ g) (ht : t < 1)
    (hut : u ≤ t) (hu't : u' ≤ t) (hz : 0 ≤ z) :
    Real.exp (-(z / ellT L g u') ^ (1 / 2 : ℝ)) ≤
      Real.exp (Real.sqrt (z * (g * ((1 - t)⁻¹ * Real.sqrt |u - u'|)))) *
        Real.exp (-(z / ellT L g u) ^ (1 / 2 : ℝ)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hℓ : 1 ≤ ellT L g u := one_le_ellT hL1
  have hℓ' : 1 ≤ ellT L g u' := one_le_ellT hL1
  have h2 := cont_abs_sqrt_sub_sqrt_le (div_nonneg hz (by linarith : (0 : ℝ) ≤ ellT L g u))
    (div_nonneg hz (by linarith : (0 : ℝ) ≤ ellT L g u'))
  have h3 : |z / ellT L g u - z / ellT L g u'| ≤ z * |ellT L g u - ellT L g u'| := by
    have hpos : 0 < ellT L g u * ellT L g u' := by nlinarith
    have heq : z / ellT L g u - z / ellT L g u' =
        z * (ellT L g u' - ellT L g u) / (ellT L g u * ellT L g u') := by
      field_simp
    rw [heq, abs_div, abs_of_pos hpos, abs_mul, abs_of_nonneg hz, abs_sub_comm (ellT L g u')]
    refine div_le_self (by positivity) (by nlinarith)
  have h4 : z * |ellT L g u - ellT L g u'| ≤ z * (g * ((1 - t)⁻¹ * Real.sqrt |u - u'|)) :=
    mul_le_mul_of_nonneg_left (etermsMid_nl_ellT_diff hg ht hut hu't) hz
  have h5 := h2.trans (Real.sqrt_le_sqrt (h3.trans h4))
  rw [← Real.exp_add, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  refine Real.exp_le_exp.2 ?_
  have := (abs_le.1 h5).2
  linarith

/-- The ratio of `W^{-d} B_{u,K}` at two times, for every block distance `K`:
`STWB_{u,K} ≤ (1 + (1-t)⁻¹ |u-u'|) STWB_{u',K}` (`u, u' ≤ t < 1`); the two terms of `B` are ratios
of the type `cont_inv_add_one_sub_ratio` (as `cont_Bctl_ratio` for `K = 0`). -/
private theorem etermsMid_nl_STWB_ratio {d : ℕ} (sz : Sizes d) (n K : ℕ) {t u u' : ℝ} (ht : t < 1)
    (hut : u ≤ t) (hu't : u' ≤ t) :
    STWB sz n u K ≤ (1 + (1 - t)⁻¹ * |u - u'|) * STWB sz n u' K := by
  have hu : u < 1 := by linarith
  have hu' : u' < 1 := by linarith
  unfold STWB Bparam
  rw [abs_of_pos (by linarith : 0 < 1 - u), abs_of_pos (by linarith : 0 < 1 - u')]
  have hA := cont_inv_add_one_sub_ratio (γ := sz.lam n ^ 2) (sq_nonneg _) ht hut hu't
  have hB := cont_inv_add_one_sub_ratio (γ := 0) le_rfl ht hut hu't
  have hLi : (0 : ℝ) ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hWi : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hc : (0 : ℝ) ≤ ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hBe : ∀ v : ℝ, (((sz.L n : ℕ) : ℝ) ^ d * (1 - v))⁻¹ =
      (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - v))⁻¹ := by
    intro v; rw [zero_add, mul_inv]
  rw [hBe u, hBe u']
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
        (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        (((1 + (1 - t)⁻¹ * |u - u'|) * (sz.lam n ^ 2 + (1 - u'))⁻¹) *
            ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ((1 + (1 - t)⁻¹ * |u - u'|) * (0 + (1 - u'))⁻¹)) := by
        gcongr
    _ = (1 + (1 - t)⁻¹ * |u - u'|) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        ((sz.lam n ^ 2 + (1 - u'))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - u'))⁻¹)) := by
        ring

/-- `exp (1/2) ≤ 2` (copy of the private `nl_exp_half_le`, `Path/NetLift1.lean`). -/
private theorem etermsMid_exp_half_le : Real.exp (1 / 2) ≤ 2 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

variable {d : ℕ} (sz : Sizes d)

/-- `W^{-d} 𝒯̃^L_{u,D}(r) = max (W^{-d} B_{u,r} e^{-(r/ℓ_u)^{1/2}}, W^{-d} W^{-D})` at `r = |a-b|_L ≤ L`. -/
private theorem etermsMid_prof_eq (n : ℕ) (u D : ℝ) (a b : Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) a b =
      max (STWB sz n u (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)))
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρL := ST_zdistInf_le sz n (a - b)
  have e : tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) =
      Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    unfold tailT
    rw [BparamR_natCast, Real.sqrt_eq_rpow]
  unfold STprof STWB tailW
  rw [min_eq_left hρL, mul_max_of_nonneg _ _ (inv_nonneg.2 (pow_nonneg hW.le d)), e, mul_assoc]

/-- **The profile moves by a factor `(1+x) e^δ` under a time change** (`x ≥ (1-t)⁻¹|u-u'|`, `δ` the modulus of
`ℓ_u`): `W^{-d} 𝒯̃^L_{u',D}(r) ≤ (1+x) e^δ W^{-d} 𝒯̃^L_{u,D}(r)`. -/
private theorem etermsMid_prof_ratio (n : ℕ) {t u u' D x δ : ℝ} (hg : 0 ≤ sz.lam n) (ht : t < 1)
    (hut : u ≤ t) (hu't : u' ≤ t) (hx0 : 0 ≤ x) (hx : (1 - t)⁻¹ * |u - u'| ≤ x) (a b : Zd d (sz.L n))
    (hδ : Real.sqrt (((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) *
      (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|))) ≤ δ) :
    STprof sz n u' D ((sz.L n : ℕ) : ℝ) a b ≤
      ((1 + x) * Real.exp δ) * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b := by
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hδ
  have hq1 : 1 ≤ (1 + x) * Real.exp δ := by
    have := Real.one_le_exp hδ0
    nlinarith
  have hSW := etermsMid_nl_STWB_ratio sz n (zdistInf d (sz.L n) (a - b)) ht hu't hut
  rw [abs_sub_comm u' u] at hSW
  have hSW' : STWB sz n u' (zdistInf d (sz.L n) (a - b)) ≤
      (1 + x) * STWB sz n u (zdistInf d (sz.L n) (a - b)) :=
    hSW.trans (mul_le_mul_of_nonneg_right (by linarith) (by
      unfold STWB Bparam; positivity))
  have hE := etermsMid_nl_exp_ell hL1 hg ht hut hu't (z := ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))
    (Nat.cast_nonneg _)
  have hE' : Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u') ^ (1 / 2 : ℝ)) ≤
      Real.exp δ * Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) :=
    hE.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hδ) (Real.exp_pos _).le)
  have hWB0 : 0 ≤ STWB sz n u' (zdistInf d (sz.L n) (a - b)) := by unfold STWB Bparam; positivity
  have hWB1 : 0 ≤ STWB sz n u (zdistInf d (sz.L n) (a - b)) := by unfold STWB Bparam; positivity
  rw [etermsMid_prof_eq, etermsMid_prof_eq]
  have hF0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D) := by positivity
  have hM : STWB sz n u' (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u') ^ (1 / 2 : ℝ)) ≤
      ((1 + x) * Real.exp δ) * (STWB sz n u (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ))) := by
    calc _ ≤ ((1 + x) * STWB sz n u (zdistInf d (sz.L n) (a - b))) * (Real.exp δ *
          Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ))) :=
          mul_le_mul hSW' hE' (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  refine max_le ?_ ?_
  · exact hM.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
  · calc _ ≤ ((1 + x) * Real.exp δ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
        le_mul_of_one_le_left hF0 hq1
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)

/-- **The control `η_u⁻¹ (W^{-d} 𝒯̃^L_{u,D})^m` moves by at most a factor `2`** under a small time change
(`m ≤ 2`, `3x + 2δ ≤ 1/2`). -/
private theorem etermsMid_zeta_ratio (n : ℕ) {E t u u' D x δ : ℝ} (m : ℕ) (hm : m ≤ 2) (hE : |E| < 2)
    (hg : 0 ≤ sz.lam n) (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t) (hx0 : 0 ≤ x)
    (hx : (1 - t)⁻¹ * |u - u'| ≤ x) (a b : Zd d (sz.L n))
    (hδ : Real.sqrt (((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) *
      (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|))) ≤ δ) (hsmall : 3 * x + 2 * δ ≤ 1 / 2) :
    (etaT E u')⁻¹ * STprof sz n u' D ((sz.L n : ℕ) : ℝ) a b ^ m ≤
      2 * ((etaT E u)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m) := by
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hδ
  have hP := etermsMid_prof_ratio sz n (D := D) hg ht hut hu't hx0 hx a b hδ
  have hP0 : 0 ≤ STprof sz n u' D ((sz.L n : ℕ) : ℝ) a b := (ST_STprof_pos sz n u' D _ a b).le
  have hP1 : 0 ≤ STprof sz n u D ((sz.L n : ℕ) : ℝ) a b := (ST_STprof_pos sz n u D _ a b).le
  have hu1 : 0 < 1 - u := by linarith
  have hu'1 : 0 < 1 - u' := by linarith
  have hmI := mE_im_pos hE
  have hη : (etaT E u')⁻¹ ≤ (1 + x) * (etaT E u)⁻¹ := by
    have h := cont_inv_add_one_sub_ratio (γ := 0) le_rfl ht hu't hut
    rw [zero_add, zero_add] at h
    have h2 : (1 - u')⁻¹ ≤ (1 + x) * (1 - u)⁻¹ :=
      h.trans (mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; linarith) (inv_nonneg.2 hu1.le))
    unfold etaT
    rw [mul_inv, mul_inv]
    calc (1 - u')⁻¹ * ((mE E).im)⁻¹ ≤ ((1 + x) * (1 - u)⁻¹) * ((mE E).im)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hmI.le)
      _ = _ := by ring
  have hq : (1 + x) * Real.exp δ ≤ Real.exp (x + δ) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp x]) (Real.exp_pos _).le
  have hq0 : 0 ≤ (1 + x) * Real.exp δ := by positivity
  have hqm : ((1 + x) * Real.exp δ) ^ m ≤ Real.exp (m * (x + δ)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hq0 hq m
  have hPm : STprof sz n u' D ((sz.L n : ℕ) : ℝ) a b ^ m ≤
      ((1 + x) * Real.exp δ) ^ m * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hP0 hP m
  have hc : (1 + x) * ((1 + x) * Real.exp δ) ^ m ≤ 2 := by
    have h1 : (1 + x) ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hm' : (m : ℝ) ≤ 2 := by exact_mod_cast hm
    calc (1 + x) * ((1 + x) * Real.exp δ) ^ m ≤ Real.exp x * Real.exp (m * (x + δ)) :=
          mul_le_mul h1 hqm (by positivity) (Real.exp_pos _).le
      _ = Real.exp (x + m * (x + δ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by nlinarith)
      _ ≤ 2 := etermsMid_exp_half_le
  have hη0 : 0 ≤ (etaT E u)⁻¹ := by
    unfold etaT; positivity
  calc (etaT E u')⁻¹ * STprof sz n u' D ((sz.L n : ℕ) : ℝ) a b ^ m
      ≤ ((1 + x) * (etaT E u)⁻¹) * (((1 + x) * Real.exp δ) ^ m *
          STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m) :=
        mul_le_mul hη hPm (pow_nonneg hP0 m) (by positivity)
    _ = ((1 + x) * ((1 + x) * Real.exp δ) ^ m) * ((etaT E u)⁻¹ *
          STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m) := by ring
    _ ≤ 2 * ((etaT E u)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m) :=
        mul_le_mul_of_nonneg_right hc (by positivity)

end Cont

/-! ## 6. The modulus of `(ℰ⊗ℰ)^{M,(2;k)}` in the time -/

section EEkSub

variable {d : ℕ} (sz : Sizes d)

/-- `W^d · #Z_L^d = N` (copy of the private `lemDecCalELip_Wd_card`, `Induction/LemDecCalELip.lean:421`). -/
private theorem etermsMid_Wd_card (n : ℕ) {N : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) :
    ((sz.W n : ℕ) : ℝ) ^ d * (Fintype.card (Zd d (sz.L n)) : ℝ) = N := by
  rw [card_Zd, hN]
  simp [Sizes.size, mul_pow]

/-- **`(ℰ⊗ℰ)^{M,(2;k)}` is Hölder-1/2 in `u` on `contGood`**: `‖STEEk_u - STEEk_{u'}‖ ≤ 18 N^{20} √|u-u'|`
(`W^d Σ_{c,c'} |S_{cc'}| |𝓛^{(6)}_u - 𝓛^{(6)}_{u'}|`, the per-`k` form of `LemDecCalELip_ee_sub`). -/
private theorem etermsMid_EEk_sub (n : ℕ) (E : ℝ) {t u u' N : ℝ} (ω : sz.SeqΩ)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N) (hE : |E| < 2) (ht : t < 1) (hu0 : 0 ≤ u)
    (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hQ : (etaT E t)⁻¹ ≤ N ^ 2)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N) (k : Fin 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STEEk sz n E u k σ a ω - STEEk sz n E u' k σ a ω‖ ≤ 18 * N ^ 20 * Real.sqrt |u - u'| := by
  have hs0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by linarith
  have key : ∀ (σ6 : Fin 6 → Bool) (a6 : Zd d (sz.L n) → Zd d (sz.L n) → Fin 6 → Zd d (sz.L n)),
      ‖(((sz.W n : ℕ) : ℂ) ^ d * ∑ c, ∑ c', SB d (sz.L n) (sz.lam n) c c' *
          Lloop sz n E u σ6 (a6 c c') ω) -
        (((sz.W n : ℕ) : ℂ) ^ d * ∑ c, ∑ c', SB d (sz.L n) (sz.lam n) c c' *
          Lloop sz n E u' σ6 (a6 c c') ω)‖ ≤ 18 * N ^ 20 * Real.sqrt |u - u'| := by
    intro σ6 a6
    rw [← mul_sub, norm_mul, norm_pow, Complex.norm_natCast]
    have hterm : ∀ c c' : Zd d (sz.L n),
        ‖SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u σ6 (a6 c c') ω -
          SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u' σ6 (a6 c c') ω‖ ≤
        ‖SB d (sz.L n) (sz.lam n) c c'‖ * (18 * N ^ 19 * Real.sqrt |u - u'|) := by
      intro c c'
      rw [← mul_sub, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h := LemDecCalELip_Lloop_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood σ6 (a6 c c')
      refine h.trans (le_of_eq ?_)
      norm_num
    have hrow : ∀ c : Zd d (sz.L n),
        ‖∑ c', (SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u σ6 (a6 c c') ω -
          SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u' σ6 (a6 c c') ω)‖ ≤
        18 * N ^ 19 * Real.sqrt |u - u'| := by
      intro c
      refine (norm_sum_le _ _).trans ?_
      calc ∑ c', ‖SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u σ6 (a6 c c') ω -
            SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u' σ6 (a6 c c') ω‖
          ≤ ∑ c', ‖SB d (sz.L n) (sz.lam n) c c'‖ * (18 * N ^ 19 * Real.sqrt |u - u'|) :=
            Finset.sum_le_sum fun c' _ => hterm c c'
        _ = 18 * N ^ 19 * Real.sqrt |u - u'| := by
            rw [← Finset.sum_mul, sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n), one_mul]
    simp only [← Finset.sum_sub_distrib]
    have htot : ‖∑ c, ∑ c', (SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u σ6 (a6 c c') ω -
          SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u' σ6 (a6 c c') ω)‖ ≤
        (Fintype.card (Zd d (sz.L n)) : ℝ) * (18 * N ^ 19 * Real.sqrt |u - u'|) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ c, ‖∑ c', (SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u σ6 (a6 c c') ω -
            SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u' σ6 (a6 c c') ω)‖
          ≤ ∑ _c : Zd d (sz.L n), 18 * N ^ 19 * Real.sqrt |u - u'| := Finset.sum_le_sum fun c _ => hrow c
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ c, ∑ c', (SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u σ6 (a6 c c') ω -
            SB d (sz.L n) (sz.lam n) c c' * Lloop sz n E u' σ6 (a6 c c') ω)‖
        ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((Fintype.card (Zd d (sz.L n)) : ℝ) * (18 * N ^ 19 * Real.sqrt |u - u'|)) :=
          mul_le_mul_of_nonneg_left htot hWd
      _ = (((sz.W n : ℕ) : ℝ) ^ d * (Fintype.card (Zd d (sz.L n)) : ℝ)) * (18 * N ^ 19 * Real.sqrt |u - u'|) := by ring
      _ = 18 * N ^ 20 * Real.sqrt |u - u'| := by rw [etermsMid_Wd_card sz n hN]; ring
  by_cases hk : k = 0
  · have eq : ∀ v : ℝ, STEEk sz n E v k σ a ω = ((sz.W n : ℕ) : ℂ) ^ d * ∑ c, ∑ c', SB d (sz.L n) (sz.lam n) c c' *
        Lloop sz n E v ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c', a 1, a 0, c] ω := by
      intro v
      simp only [STEEk, STEEkM, hk, ite_true, STLM_seqHflow]
    rw [eq u, eq u']
    exact key _ (fun c c' => ![a 0, a 1, c', a 1, a 0, c])
  · have eq : ∀ v : ℝ, STEEk sz n E v k σ a ω = ((sz.W n : ℕ) : ℂ) ^ d * ∑ c, ∑ c', SB d (sz.L n) (sz.lam n) c c' *
        Lloop sz n E v ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, c', a 0, a 1, c] ω := by
      intro v
      simp only [STEEk, STEEkM, hk, ite_false, STLM_seqHflow]
    rw [eq u, eq u']
    exact key _ (fun c c' => ![a 1, a 0, c', a 0, a 1, c])

end EEkSub

/-! ## 7. Sections: the premises of `lem: EWGn2_N`, `lem: EMn2_N` at a time section -/

section Sections

variable {d : ℕ} (sz : Sizes d)

/-- `Θ ≤ 3` once `A ≥ 1` (`A^{-1/6} ≤ 1`, `W^{-d} ≤ 1`). -/
private theorem etermsMid_Theta_le_three (n : ℕ) (hA : 1 ≤ STAI sz n) (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) :
    etermsMid_Theta sz n ≤ 3 := by
  unfold etermsMid_Theta
  have h1 : STAI sz n ^ (-(1 / 6) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num)
  have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW)
  linarith

/-- **`|𝓛^{(2)}| ≺ W^{-d} 𝒯̃^L`, uniformly in `u ∈ [s,t]`** (`(eq:Step2_inputs)`, `3_5:1340-1357`):
`𝓛 = (𝓛-𝒦) + 𝒦`, `etermsMid_J` and `|𝒦^{(2)}| ≤ C_K W^{-d} 𝒯̃^L` (`STK2decay`). -/
private theorem etermsMid_L2 {E s t : ℕ → ℝ} {Cd 𝔠d 𝔠 𝔡 CK : ℝ} (hAd : sz.Admissible 𝔠 𝔡)
    (hReg : STReg5Mid sz s t) (hCon : STConStInd sz 𝔠d s t) (h𝔠d : 0 < 𝔠d) (hCd : 0 < Cd)
    (hcC : 𝔠d * Cd ≤ 1 / 30) (hGd : STGdecayW sz E s t Cd) (hCK : 0 < CK)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u → u ≤ t n →
      0 ≤ D → ‖STKloop sz n (E n) u σ a‖ ≤ CK * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    {D : ℝ} (hD : 0 < D) :
    sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) := by
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hAd.2.2.1
  have hJ := etermsMid_J sz hAd hReg hCon h𝔠d hCd hcC hGd hD
  refine etermsMid_prec_lin sz hsize hJ (b := fun n p _ => CK * STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ)
    (p.2.2 0) (p.2.2 1)) ?_ (K := CK + 3) (by linarith) ?_ ?_ ?_
  · filter_upwards [hK2] with n hn
    rintro ⟨⟨u, hsu, hut⟩, σ, a⟩ ω
    have h := hn u D σ a hsu hut hD.le
    calc ‖Lloop sz n (E n) u σ a ω‖ = ‖(Lloop sz n (E n) u σ a ω - STKloop sz n (E n) u σ a) +
          STKloop sz n (E n) u σ a‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl h)
  · filter_upwards with n
    rintro ⟨⟨u, hsu, hut⟩, σ, a⟩ ω
    have := (ST_STprof_pos sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)).le
    change CK * _ ≤ (CK + 3) * _
    nlinarith
  · filter_upwards [etermsMid_A_big sz hAd 1] with n hA1
    rintro ⟨⟨u, hsu, hut⟩, σ, a⟩ ω
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have h3 := etermsMid_Theta_le_three sz n hA1 hW1
    have := (ST_STprof_pos sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)).le
    change etermsMid_Theta sz n * _ ≤ (CK + 3) * _
    nlinarith
  · intro n p ω
    exact (ST_STprof_pos sz n _ D _ _ _).le

/-- **`(Gtmwc)` from `(Gt_bound_flow)`**: `‖G_u - M‖_max ≺ (W^{-d}B_{u,0})^{1/4}` from `STLocalEntryU`
(`|G_{xy} - M|² ≺ W^{-d}B_{u,|x-y|} ≤ W^{-d}B_{u,0} ≤ (W^{-d}B_{u,0})^{1/2}`, `W^{-d}B_{u,0} ≤ 1`). -/
private theorem etermsMid_S1W {E s t : ℕ → ℝ} (hLoc : STLocalEntryU sz E s t)
    (hB1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → sz.Bctl n u ≤ 1) (hs : ∀ n, 0 ≤ s n) :
    STStep1Weak sz E s t := by
  refine StochDomAt.of_subset hLoc fun τ hτ => ⟨2 * τ, by linarith, ?_⟩
  filter_upwards [hB1] with n hB
  rintro ω ⟨⟨⟨u, hsu, hut⟩, x, y⟩, hω⟩
  refine ⟨(⟨u, hsu, hut⟩, x, y), ?_⟩
  have hb1 := hB u ((hs n).trans hsu) hut
  have hb0 : 0 ≤ sz.Bctl n u := by
    unfold Sizes.Bctl Bparam
    positivity
  have h14 : sz.Bctl n u ≤ (sz.Bctl n u ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]
    norm_num
    rcases hb0.eq_or_lt with h | h
    · rw [← h]; simp
    · calc sz.Bctl n u = sz.Bctl n u ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ sz.Bctl n u ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge h hb1 (by norm_num)
  have hW := etermsMid_STWB_le sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN2 : ((sz.size n : ℕ) : ℝ) ^ (2 * τ) = (((sz.size n : ℕ) : ℝ) ^ τ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; congr 1; push_cast; ring
  change ((sz.size n : ℕ) : ℝ) ^ (2 * τ) * _ < ‖STGM sz n (E n) u ω x y‖ ^ 2
  rw [hN2]
  have hlt : ((sz.size n : ℕ) : ℝ) ^ τ * sz.Bctl n u ^ (1 / 4 : ℝ) < ‖STGM sz n (E n) u ω x y‖ := hω
  have hprod : (((sz.size n : ℕ) : ℝ) ^ τ * sz.Bctl n u ^ (1 / 4 : ℝ)) ^ 2 < ‖STGM sz n (E n) u ω x y‖ ^ 2 :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  calc (((sz.size n : ℕ) : ℝ) ^ τ) ^ 2 * STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
      ≤ (((sz.size n : ℕ) : ℝ) ^ τ) ^ 2 * sz.Bctl n u := mul_le_mul_of_nonneg_left hW (by positivity)
    _ ≤ (((sz.size n : ℕ) : ℝ) ^ τ) ^ 2 * (sz.Bctl n u ^ (1 / 4 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left h14 (by positivity)
    _ = (((sz.size n : ℕ) : ℝ) ^ τ * sz.Bctl n u ^ (1 / 4 : ℝ)) ^ 2 := by ring
    _ < _ := hprod

/-- `log W` is eventually larger than every constant, and `W > 1`: `(d + D) log W ≤ (log W)^5`. -/
private theorem etermsMid_log_ev {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (D : ℝ) :
    ∀ᶠ n in atTop, 1 < ((sz.W n : ℕ) : ℝ) ∧
      ((d : ℝ) + D) * Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 5 := by
  have hWt := ST_W_tendsto sz hA.2.2.1 hA.1 hA.2.2.2.1
  have hlog : Tendsto (fun n => Real.log ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hWt
  filter_upwards [hWt.eventually (eventually_gt_atTop 1), hlog.eventually (eventually_ge_atTop (max 1 ((d : ℝ) + D)))]
    with n h1 h2
  refine ⟨h1, ?_⟩
  set x : ℝ := Real.log ((sz.W n : ℕ) : ℝ)
  have hx1 : 1 ≤ x := (le_max_left _ _).trans h2
  have hxd : (d : ℝ) + D ≤ x := (le_max_right _ _).trans h2
  have hx4 : x ≤ x ^ 4 := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  calc ((d : ℝ) + D) * x ≤ x ^ 4 * x := mul_le_mul_of_nonneg_right (hxd.trans hx4) (by linarith)
    _ = x ^ 5 := by ring

/-- `Ĵ^ℓ ≤ Ĵ^L` for `ℓ ≥ 0` (`𝒯̃^L ≤ 𝒯̃^ℓ`). -/
private theorem etermsMid_Jhat_mono (n : ℕ) (E D u : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    STJhatM sz n E D ℓ u H ≤ STJhatM sz n E D ((sz.L n : ℕ) : ℝ) u H := by
  unfold STJhatM
  refine Finset.sup'_le _ _ fun p _ => ?_
  refine le_trans ?_ (Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
    ‖STLKM sz n E u H p.1 p.2‖ / STprof sz n u D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1))
    (Finset.mem_univ p))
  exact div_le_div_of_nonneg_left (norm_nonneg _) (ST_STprof_pos sz n u D _ _ _)
    (etermsMid_prof_L_le sz n u D hℓ (p.2 0) (p.2 1))

/-- `Ĵ^L_{tt,D} ≺ Θ` at a time section, from `|𝓛-𝒦|_{σ,a} ≺ Θ W^{-d} 𝒯̃^L` (`etermsMid_J`). -/
private theorem etermsMid_Jhat_sec {E s t : ℕ → ℝ} {D : ℝ}
    (hJ : sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => etermsMid_Theta sz n *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)))
    (tt : ∀ n, TimeIcc s t n) :
    sz.Prec (U := fun _ => Unit) (fun n _ ω => STJhat sz n (E n) D ((sz.L n : ℕ) : ℝ) (tt n : ℝ) ω)
      (fun n _ _ => etermsMid_Theta sz n) := by
  have h := StochDomAt.precomp_param (V := fun n => STLab sz n) hJ (fun n v => (tt n, v.1, v.2))
  refine etermsMid_of_subset sz h fun τ hτ => ⟨τ, hτ, Filter.Eventually.of_forall fun n => ?_⟩
  rintro ω ⟨_, hω⟩
  have hω' : ((sz.size n : ℕ) : ℝ) ^ τ * etermsMid_Theta sz n <
      Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
        (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
          ‖STLKM sz n (E n) (tt n : ℝ) (sz.seqHflow n (tt n : ℝ) ω) p.1 p.2‖ /
            STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1)) := hω
  obtain ⟨p, -, hp⟩ := (Finset.lt_sup'_iff _).1 hω'
  refine ⟨p, ?_⟩
  have hpos := ST_STprof_pos sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1)
  rw [lt_div_iff₀ hpos] at hp
  have e : STLKM sz n (E n) (tt n : ℝ) (sz.seqHflow n (tt n : ℝ) ω) p.1 p.2 =
      Lloop sz n (E n) (tt n : ℝ) p.1 p.2 ω - STKloop sz n (E n) (tt n : ℝ) p.1 p.2 := by
    unfold STLKM; rw [STLM_seqHflow]
  rw [e] at hp
  change ((sz.size n : ℕ) : ℝ) ^ τ * (etermsMid_Theta sz n * _) < _
  linarith

/-- `(eq:LW_assm_exp)` at the scale family `K_u`: `STScaleInv`, from `|𝓛^{(2)}| ≺ W^{-d} 𝒯̃^L ≤ W^{-d} 𝒯̃^{K}`. -/
private theorem etermsMid_hinv {E s t : ℕ → ℝ}
    (hL2 : ∀ D : ℝ, 0 < D → sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1))) :
    STScaleInv sz E s t (etermsMid_Kf sz) := by
  intro tt D hD
  have h := StochDomAt.precomp_param
    (V := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) (hL2 D hD)
    (fun n p => (tt n, p.1.1, p.2))
  refine ST_prec_mono_eventually sz (Filter.Eventually.of_forall fun n p ω => ?_) h
  exact etermsMid_prof_L_le sz n _ D (etermsMid_Kf_nonneg sz n _) _ _

/-- `(W^{-d}B_{u,0})^{1/2} ≤ 2 A^{-1/2}` in the window. -/
private theorem etermsMid_sqrtB_le (n : ℕ) {u : ℝ} (hA : 1 ≤ STAI sz n) (hb : sz.Bctl n u ≤ 2 / STAI sz n)
    (hb0 : 0 ≤ sz.Bctl n u) : sz.Bctl n u ^ (1 / 2 : ℝ) ≤ 2 * STAI sz n ^ (-(1 / 2) : ℝ) := by
  have hA0 : 0 < STAI sz n := by linarith
  have h1 : sz.Bctl n u ^ (1 / 2 : ℝ) ≤ (2 / STAI sz n) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hb0 hb (by norm_num)
  have h2 : (2 / STAI sz n) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) * STAI sz n ^ (-(1 / 2) : ℝ) := by
    rw [Real.div_rpow (by norm_num) hA0.le, Real.rpow_neg hA0.le, div_eq_mul_inv]
  have h3 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h4 : 0 ≤ STAI sz n ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hA0.le _
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right h3 h4)

/-- `Θ ≤ (2 + 𝔡^{-1/3}) A^{-1/6}`. -/
private theorem etermsMid_Theta_le (n : ℕ) {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hl : 0 < sz.lam n) (hl' : sz.lam n ≤ 𝔡⁻¹)
    (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) :
    etermsMid_Theta sz n ≤ (2 + (𝔡⁻¹) ^ (1 / 3 : ℝ)) * STAI sz n ^ (-(1 / 6) : ℝ) := by
  have h := etermsMid_Wd_le sz n h𝔡 hl hl' hW
  unfold etermsMid_Theta
  linarith

/-- `0 < η_u` for `|E| < 2`, `u < 1`. -/
private theorem etermsMid_eta_pos {E u : ℝ} (hE : |E| < 2) (hu : u < 1) : 0 < etaT E u :=
  mul_pos (by linarith) (mE_im_pos hE)

/-- **The three error terms at a time section** (`(S5WG+M)`, `3_5:1969-1979`): `lem: EWGn2_N` and `lem: EMn2_N`
(`STLWT`, `STEMn2Exp`) at the scale `K_u`, with `W^{-d}B_{u,0} ≤ 2/A`, `𝒯̃^{K_u} = 𝒯̃^L` and `Ĵ^{K_u} ≤ Ĵ^L ≺ A^{-1/6}`. -/
private theorem etermsMid_sections (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n))
    (hReg : STReg5Mid sz s t) (hS1W : STStep1Weak sz (STflowE z) s t) {cB c : ℝ} (hcB : 0 < cB) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (hL2 : ∀ D : ℝ, 0 < D → sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)))
    (hJ : ∀ D : ℝ, 0 < D → sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω -
        STKloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => etermsMid_Theta sz n *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)))
    (tt : ∀ n, TimeIcc s t n) {D : ℝ} (hD : 0 < D) :
    sz.Prec (U := STLab sz) (fun n v ω => ‖STEGt sz n (STflowE z n) (tt n : ℝ) v.1 v.2 ω‖)
      (fun n v _ => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (tt n : ℝ))⁻¹ *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1)) ∧
    sz.Prec (U := fun n => Fin 2 × STLab sz n)
      (fun n v ω => ‖STEEk sz n (STflowE z n) (tt n : ℝ) v.1 v.2.1 v.2.2 ω‖)
      (fun n v _ => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (tt n : ℝ))⁻¹ *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2.2 0) (v.2.2 1) ^ 2) := by
  have hAd : sz.Admissible 𝔠 𝔡 := hflow.1
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hAd.2.2.1
  obtain ⟨-, hEb, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => by have := hEb n; linarith
  obtain ⟨h1, h2⟩ := ST_LW_sections sz hLWT hEMe hd hκ hε h𝔡 hflow hs htT hS1W hcB hc hBd (etermsMid_Kf sz)
    (Filter.Eventually.of_forall fun n u _ _ => ⟨etermsMid_Kf_nonneg sz n u, etermsMid_Kf_le sz n u⟩)
    (etermsMid_hinv sz hL2) tt
  have h1D := h1 D hD
  have h2D := h2 D hD
  set C₁ : ℝ := (𝔡⁻¹) ^ (1 / 3 : ℝ) with hC₁def
  have hC₁ : 0 < C₁ := Real.rpow_pos_of_pos (inv_pos.2 h𝔡) _
  set C₀ : ℝ := 2 + C₁ with hC₀def
  have hC₀ : 0 < C₀ := by linarith
  -- the numerical facts at the section
  have hfacts : ∀ᶠ n in atTop, 1 < ((sz.W n : ℕ) : ℝ) ∧
      ((d : ℝ) + D) * Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 5 ∧ 2 ≤ STAI sz n ∧
      sz.Bctl n (tt n : ℝ) ≤ 2 / STAI sz n ∧ 0 ≤ sz.Bctl n (tt n : ℝ) ∧ sz.Bctl n (tt n : ℝ) ≤ 1 ∧
      etermsMid_Theta sz n ≤ C₀ * STAI sz n ^ (-(1 / 6) : ℝ) := by
    filter_upwards [etermsMid_log_ev sz hAd D, etermsMid_A_big sz hAd 2, etermsMid_lam sz hAd] with n hlog hA2 hl
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hwin := etermsMid_Bctl_window sz n (u := (tt n : ℝ)) hl.1
      (((hReg n).1).trans (by linarith [(tt n).2.2])) (by linarith [(hReg n).2, (tt n).2.1])
    have hA0 : 0 < STAI sz n := by linarith
    have hb0 : 0 ≤ sz.Bctl n (tt n : ℝ) := (lt_of_lt_of_le (by positivity) hwin.1).le
    refine ⟨hlog.1, hlog.2, hA2, hwin.2, hb0, ?_, etermsMid_Theta_le sz n h𝔡 hl.1 hl.2 hW1⟩
    calc sz.Bctl n (tt n : ℝ) ≤ 2 / STAI sz n := hwin.2
      _ ≤ 1 := by rw [div_le_one hA0]; exact hA2
  have hηnn : ∀ n, 0 ≤ (etaT (STflowE z n) (tt n : ℝ))⁻¹ := fun n =>
    inv_nonneg.2 (etermsMid_eta_pos (hE2 n) (lt_of_le_of_lt (tt n).2.2 (ht1 n))).le
  have hA6nn : ∀ (n : ℕ) (e : ℝ), 0 ≤ STAI sz n ^ e := fun n e => by
    unfold STAI; exact Real.rpow_nonneg (by positivity) _
  refine ⟨?_, ?_⟩
  · -- `ℰ^{G̃}`
    refine etermsMid_prec_lin sz hsize h1D (b := fun _ _ _ => 0) (Filter.Eventually.of_forall fun n u ω => by
      simp) (K := 2) (by norm_num) (Filter.Eventually.of_forall fun n u ω => by
      have := hηnn n
      have := hA6nn n (-(1 / 2))
      have := (ST_STprof_pos sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (u.2 0) (u.2 1)).le
      positivity) ?_ ?_
    · filter_upwards [hfacts] with n hf u ω
      obtain ⟨hW1, hlog, hA2, hb2, hb0, hb1, -⟩ := hf
      have hsq := etermsMid_sqrtB_le sz n (by linarith) hb2 hb0
      have hP := etermsMid_prof_Kf_le sz n (u := (tt n : ℝ)) (D := D) hW1 hlog hb1 (u.2 0) (u.2 1)
      have hPpos := (ST_STprof_pos sz n (tt n : ℝ) D (etermsMid_Kf sz n (tt n : ℝ)) (u.2 0) (u.2 1)).le
      have hη := hηnn n
      change (etaT (STflowE z n) (tt n : ℝ))⁻¹ * sz.Bctl n (tt n : ℝ) ^ (1 / 2 : ℝ) *
        STprof sz n (tt n : ℝ) D (etermsMid_Kf sz n (tt n : ℝ)) (u.2 0) (u.2 1) ≤
        2 * (STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (tt n : ℝ))⁻¹ *
          STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (u.2 0) (u.2 1))
      calc (etaT (STflowE z n) (tt n : ℝ))⁻¹ * sz.Bctl n (tt n : ℝ) ^ (1 / 2 : ℝ) *
            STprof sz n (tt n : ℝ) D (etermsMid_Kf sz n (tt n : ℝ)) (u.2 0) (u.2 1)
          ≤ (etaT (STflowE z n) (tt n : ℝ))⁻¹ * (2 * STAI sz n ^ (-(1 / 2) : ℝ)) *
            STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (u.2 0) (u.2 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsq hη) hP hPpos (by positivity)
        _ = _ := by ring
    · exact fun n u ω => by
        have := hηnn n
        have := hA6nn n (-(1 / 2))
        have := (ST_STprof_pos sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (u.2 0) (u.2 1)).le
        positivity
  · -- `(ℰ⊗ℰ)^{M}`
    refine etermsMid_prec_two sz hsize h2D (etermsMid_Jhat_sec sz (hJ D hD) tt) ?_
    intro τ hτ
    refine ⟨τ / 8, by linarith, ?_⟩
    filter_upwards [hfacts, ST_size_pow_big sz hsize (a := τ / 2) (M := 2 + C₀ ^ 3) (by linarith),
      hsize.eventually (eventually_ge_atTop 1)] with n hf hbig hN1 ω hE1 hE2' v
    obtain ⟨hW1, hlog, hA2, hb2, hb0, hb1, hΘ⟩ := hf
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    set X : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 8) with hX
    have hX1 : 1 ≤ X := Real.one_le_rpow hN1' (by linarith)
    have hX4 : X ^ 4 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    set a6 : ℝ := STAI sz n ^ (-(1 / 6) : ℝ) with ha6
    have ha60 : 0 ≤ a6 := hA6nn n _
    have hA0 : 0 ≤ STAI sz n := by linarith
    have hJL := hE2' ()
    have hJK : STJhat sz n (STflowE z n) D (etermsMid_Kf sz n (tt n : ℝ)) (tt n : ℝ) ω ≤ X * (C₀ * a6) := by
      refine le_trans (etermsMid_Jhat_mono sz n _ D _ (etermsMid_Kf_nonneg sz n _) _) ?_
      refine hJL.trans ?_
      exact mul_le_mul_of_nonneg_left hΘ (Real.rpow_nonneg hN0.le _)
    have hJ0 : 0 ≤ STJhat sz n (STflowE z n) D (etermsMid_Kf sz n (tt n : ℝ)) (tt n : ℝ) ω :=
      ST_JhatM_nonneg sz n _ _ _ _ _
    have hsq := etermsMid_sqrtB_le sz n (by linarith) hb2 hb0
    rw [etermsMid_rpow_cube hA0] at hsq
    have hP := etermsMid_prof_Kf_le sz n (u := (tt n : ℝ)) (D := D) hW1 hlog hb1 (v.2.2 0) (v.2.2 1)
    have hPpos := (ST_STprof_pos sz n (tt n : ℝ) D (etermsMid_Kf sz n (tt n : ℝ)) (v.2.2 0) (v.2.2 1)).le
    have hη := hηnn n
    have hE1v := hE1 v
    change ‖STEEk sz n (STflowE z n) (tt n : ℝ) v.1 v.2.1 v.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      (STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (tt n : ℝ))⁻¹ *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2.2 0) (v.2.2 1) ^ 2)
    rw [etermsMid_rpow_cube hA0]
    set P := STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2.2 0) (v.2.2 1) with hPdef
    set PK := STprof sz n (tt n : ℝ) D (etermsMid_Kf sz n (tt n : ℝ)) (v.2.2 0) (v.2.2 1) with hPKdef
    set Jh := STJhat sz n (STflowE z n) D (etermsMid_Kf sz n (tt n : ℝ)) (tt n : ℝ) ω with hJh
    have hP2 : PK ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hPpos hP 2
    have hJ3 : Jh ^ 3 ≤ (X * (C₀ * a6)) ^ 3 := pow_le_pow_left₀ hJ0 hJK 3
    have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX1
    have ha63 : 0 ≤ a6 ^ 3 := pow_nonneg ha60 3
    have hin : sz.Bctl n (tt n : ℝ) ^ (1 / 2 : ℝ) + Jh ^ 3 ≤ a6 ^ 3 * (X ^ 3 * (2 + C₀ ^ 3)) := by
      have h3 : (X * (C₀ * a6)) ^ 3 = a6 ^ 3 * (X ^ 3 * C₀ ^ 3) := by ring
      have h4 : 2 * a6 ^ 3 ≤ a6 ^ 3 * (X ^ 3 * 2) := by nlinarith
      calc sz.Bctl n (tt n : ℝ) ^ (1 / 2 : ℝ) + Jh ^ 3 ≤ 2 * a6 ^ 3 + (X * (C₀ * a6)) ^ 3 := add_le_add hsq hJ3
        _ = 2 * a6 ^ 3 + a6 ^ 3 * (X ^ 3 * C₀ ^ 3) := by rw [h3]
        _ ≤ a6 ^ 3 * (X ^ 3 * 2) + a6 ^ 3 * (X ^ 3 * C₀ ^ 3) := by linarith
        _ = a6 ^ 3 * (X ^ 3 * (2 + C₀ ^ 3)) := by ring
    have hfin : X * ((etaT (STflowE z n) (tt n : ℝ))⁻¹ * (sz.Bctl n (tt n : ℝ) ^ (1 / 2 : ℝ) + Jh ^ 3) * PK ^ 2) ≤
        X * ((etaT (STflowE z n) (tt n : ℝ))⁻¹ * (a6 ^ 3 * (X ^ 3 * (2 + C₀ ^ 3))) * P ^ 2) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hin hη) hP2 (sq_nonneg _) (by positivity))
        (by linarith)
    have hNτ : ((sz.size n : ℕ) : ℝ) ^ τ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hX4C : X ^ 4 * (2 + C₀ ^ 3) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [hNτ, hX4]
      exact mul_le_mul_of_nonneg_left hbig (Real.rpow_nonneg hN0.le _) |>.trans (le_of_eq rfl)
    calc ‖STEEk sz n (STflowE z n) (tt n : ℝ) v.1 v.2.1 v.2.2 ω‖
        ≤ X * ((etaT (STflowE z n) (tt n : ℝ))⁻¹ * (sz.Bctl n (tt n : ℝ) ^ (1 / 2 : ℝ) + Jh ^ 3) * PK ^ 2) := hE1v
      _ ≤ X * ((etaT (STflowE z n) (tt n : ℝ))⁻¹ * (a6 ^ 3 * (X ^ 3 * (2 + C₀ ^ 3))) * P ^ 2) := hfin
      _ = (X ^ 4 * (2 + C₀ ^ 3)) * (a6 ^ 3 * (etaT (STflowE z n) (tt n : ℝ))⁻¹ * P ^ 2) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (a6 ^ 3 * (etaT (STflowE z n) (tt n : ℝ))⁻¹ * P ^ 2) :=
          mul_le_mul_of_nonneg_right hX4C (by positivity)

end Sections

/-! ## 8. The net lift from the time sections to `u ∈ [s,t]` -/

section Lift

open RBM.Ind.ContinuityNet

variable {d : ℕ} (sz : Sizes d)

/-- `L ≤ N`. -/
private theorem etermsMid_L_le_size (hd : 1 ≤ d) (n : ℕ) : ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hW : 1 ≤ sz.W n := sz.W_pos n
  have h1 : sz.L n ≤ sz.L n ^ d := Nat.le_self_pow (by omega) _
  have h2 : sz.L n ^ d ≤ (sz.W n * sz.L n) ^ d :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  exact_mod_cast h1.trans h2

/-- **The net lift** (`1_2:1400`, the standard `N^{-C}`-net argument; the merged `cont_core` with `P = seqP sz`,
`Ξ = contGood`, `ε = N^{-CR}`): a per-section domination with a deterministic control `ζ ≥ N^{-CR}` that moves by at most
a factor `2` under a time change of size `N^{-A}`, for a family that moves by at most `N^{-CR}` on `contGood`, is uniform in
`u ∈ [s,t]`. -/
private theorem etermsMid_lift {s t : ℕ → ℝ} {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (hsize : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) (hlen : ∀ n, t n - s n ≤ 1) {Cv A CR : ℝ} (hCv : 0 ≤ Cv)
    (hA : 0 ≤ A) (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv)
    (ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ)
    (hsec : ∀ tt : ∀ n, TimeIcc s t n,
      sz.Prec (fun n v ω => ξ n (tt n, v) ω) (fun n v ω => ζ n (tt n, v) ω))
    (hlow : ∀ᶠ n in atTop, ∀ p ω, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ ζ n p ω)
    (hclose : ∀ᶠ n in atTop, ∀ ω ∈ contGood sz n, ∀ u u' : TimeIcc s t n,
      |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-A) → ∀ v : V n,
        ξ n (u, v) ω ≤ ξ n (u', v) ω + ((sz.size n : ℕ) : ℝ) ^ (-CR) ∧ ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) :
    sz.Prec ξ ζ := by
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_size sz hsize
  exact cont_core (V := V) (P := sz.seqP) (size := sz.size) hsizeN hst hlen hA hCv hcard
    (ST_PT_of_sections sz hst ξ ζ hsec) (cont_highProbAt_good sz hsizeN)
    (ε := fun n => ((sz.size n : ℕ) : ℝ) ^ (-CR)) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hlow hclose

/-- **The time change at the mesh `N^{-A}`** (`A ≥ 6`): `η_{u'}⁻¹ (W^{-d} 𝒯̃^L_{u',D})^m ≤ 2 η_u⁻¹ (W^{-d} 𝒯̃^L_{u,D})^m`
for `m ≤ 2`, `|u-u'| ≤ N^{-A}`, `u, u' ≤ t`, `(1-t)⁻¹ ≤ N`, `ilambda ≤ 𝔡⁻¹`, `256 𝔡⁻¹ ≤ N`, `L ≤ N`. -/
private theorem etermsMid_zeta_close (n : ℕ) {E t u u' D A 𝔡 : ℝ} (hd : 1 ≤ d) (m : ℕ) (hm : m ≤ 2)
    (hE : |E| < 2) (hg : 0 ≤ sz.lam n) (hg' : sz.lam n ≤ 𝔡⁻¹) (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t)
    (hN : (1 - t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hN2 : 2 ≤ ((sz.size n : ℕ) : ℝ))
    (hbig : 256 * 𝔡⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hA : 6 ≤ A)
    (hΔ : |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-A)) (a b : Zd d (sz.L n)) :
    (etaT E u')⁻¹ * STprof sz n u' D ((sz.L n : ℕ) : ℝ) a b ^ m ≤
      2 * ((etaT E u)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hΔ
  have h1t : 0 < 1 - t := by linarith
  have hy : N ^ (-A / 2) ≤ (N ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hz : N ^ (-A) ≤ (N ^ 6)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hN3 : (0 : ℝ) < N ^ 3 := by positivity
  have hN6 : (0 : ℝ) < N ^ 6 := by positivity
  -- `x = 1/32`
  have hx : (1 - t)⁻¹ * |u - u'| ≤ 1 / 32 := by
    calc (1 - t)⁻¹ * |u - u'| ≤ N * (N ^ 6)⁻¹ := mul_le_mul hN (hΔ.trans hz) (abs_nonneg _) hN0.le
      _ ≤ N * (N ^ 5 * 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hN0.le
          calc N ^ 5 * 2 ≤ N ^ 5 * N := mul_le_mul_of_nonneg_left hN2 (by positivity)
            _ = N ^ 6 := by ring
      _ = 1 / 2 * (N ^ 4)⁻¹ := by field_simp
      _ ≤ 1 / 32 := by
          have h4 : (16 : ℝ) ≤ N ^ 4 := by
            calc (16 : ℝ) = 2 ^ 4 := by norm_num
              _ ≤ N ^ 4 := pow_le_pow_left₀ (by norm_num) hN2 4
          have : (N ^ 4)⁻¹ ≤ 1 / 16 := by rw [one_div]; exact inv_anti₀ (by norm_num) h4
          linarith
  -- `δ = 1/16`
  have hr : ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ≤ N :=
    (ST_zdistInf_le sz n (a - b)).trans (etermsMid_L_le_size sz hd n)
  have hr0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hδ : Real.sqrt (((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) *
      (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|))) ≤ 1 / 16 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have hprod : ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) * (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|)) ≤
        N * (𝔡⁻¹ * (N * (N ^ 3)⁻¹)) :=
      mul_le_mul hr (mul_le_mul hg' (mul_le_mul hN (hsq.trans hy) (Real.sqrt_nonneg _) hN0.le)
        (by positivity) (by linarith [hg, hg'])) (by positivity) hN0.le
    refine hprod.trans ?_
    have hinv : N * (𝔡⁻¹ * (N * (N ^ 3)⁻¹)) = 𝔡⁻¹ * (N ^ 2 * (N ^ 3)⁻¹) := by ring
    rw [hinv]
    have h5 : N ^ 2 * (N ^ 3)⁻¹ = N⁻¹ := by field_simp
    rw [h5]
    have : 𝔡⁻¹ * N⁻¹ ≤ 1 / 256 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hN0]
      linarith
    nlinarith
  exact etermsMid_zeta_ratio sz n m hm hE hg ht hut hu't (by norm_num) hx a b hδ (by norm_num)

/-- The net lift in the form used below: the Hölder-`1/2` modulus of `ξ` on `contGood` (any constant `CH`) and the
factor-`2` slow variation of `ζ` at every mesh `N^{-A}`, `A ≥ 6`, give the uniform domination. -/
private theorem etermsMid_lift2 {s t : ℕ → ℝ} {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (hsize : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) (hlen : ∀ n, t n - s n ≤ 1) {Cv CR : ℝ} (hCv : 0 ≤ Cv)
    (hCR : 0 ≤ CR) (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv)
    (ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ)
    (hsec : ∀ tt : ∀ n, TimeIcc s t n,
      sz.Prec (fun n v ω => ξ n (tt n, v) ω) (fun n v ω => ζ n (tt n, v) ω))
    (hlow : ∀ᶠ n in atTop, ∀ p ω, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ ζ n p ω)
    (hH : ∃ CH : ℝ, 0 ≤ CH ∧ ∀ᶠ n in atTop, ∀ ω ∈ contGood sz n, ∀ (u u' : TimeIcc s t n) (v : V n),
      |ξ n (u, v) ω - ξ n (u', v) ω| ≤ ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - (u' : ℝ)|)
    (hζ : ∀ A : ℝ, 6 ≤ A → ∀ᶠ n in atTop, ∀ u u' : TimeIcc s t n,
      |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-A) → ∀ (v : V n) (ω : sz.SeqΩ),
        ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) :
    sz.Prec ξ ζ := by
  obtain ⟨CH, hCH0, hH'⟩ := hH
  have hA : (6 : ℝ) ≤ 2 * (CH + CR) + 6 := by linarith
  refine etermsMid_lift sz hsize hst hlen hCv (A := 2 * (CH + CR) + 6) (by linarith) hcard ξ ζ hsec hlow ?_
  filter_upwards [hH', hζ _ hA, hsize.eventually_ge_atTop 1] with n hn hz hN1
  intro ω hω u u' hΔ v
  refine ⟨?_, hz u u' hΔ v ω⟩
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hsq : Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * (CH + CR) + 6) / 2) :=
    cont_sqrt_abs_le hN0.le hΔ
  have h1 := (abs_le.1 (hn ω hω u u' v)).2
  have h2 : ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-CR) := by
    calc ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - (u' : ℝ)|
        ≤ ((sz.size n : ℕ) : ℝ) ^ CH * ((sz.size n : ℕ) : ℝ) ^ (-(2 * (CH + CR) + 6) / 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (CH + -(2 * (CH + CR) + 6) / 2) := (Real.rpow_add hN0 _ _).symm
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-CR) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  linarith

/-- The floor of the control: `N^{-(3+2D)} ≤ A^{-1/2} η_u⁻¹ (W^{-d} 𝒯̃^L_{u,D})^m` for `m ∈ {1,2}`, `N ≥ 𝔡⁻²`. -/
private theorem etermsMid_floor (hd : 1 ≤ d) (n : ℕ) {E u D 𝔡 : ℝ} (m : ℕ) (hm2 : m ≤ 2)
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (h𝔡 : 0 < 𝔡) (hl : 0 < sz.lam n) (hl' : sz.lam n ≤ 𝔡⁻¹)
    (hD : 0 ≤ D) (hbig : (𝔡⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (a b : Zd d (sz.L n)) :
    ((sz.size n : ℕ) : ℝ) ^ (-(3 + 2 * D)) ≤ STAI sz n ^ (-(1 / 2) : ℝ) * (etaT E u)⁻¹ *
      STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ N := ST_Wpow_le_size sz n
  have hA0 : 0 < STAI sz n := by unfold STAI; positivity
  have hAle : STAI sz n ≤ N ^ 2 := by
    unfold STAI
    calc sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ (𝔡⁻¹) ^ 2 * N :=
          mul_le_mul (pow_le_pow_left₀ hl.le hl' 2) hWd (by positivity) (by positivity)
      _ ≤ N * N := mul_le_mul hbig le_rfl hN0.le hN0.le
      _ = N ^ 2 := by ring
  have hA6 : N ^ (-1 : ℝ) ≤ STAI sz n ^ (-(1 / 2) : ℝ) := by
    have h := Real.rpow_le_rpow_of_nonpos hA0 hAle (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
    refine le_trans (le_of_eq ?_) h
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hη : 1 ≤ (etaT E u)⁻¹ := by
    have hpos := etermsMid_eta_pos hE hu1
    refine (one_le_inv₀ hpos).2 ?_
    have hm := mE_im_pos hE
    have hm1' : (mE E).im ≤ 1 := by
      rw [mE_im]
      have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
        Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
      linarith
    unfold etaT
    nlinarith
  have hP := ST_prof_lower_N sz (by omega : 0 < d) n hD u ((sz.L n : ℕ) : ℝ) a b
  have hP0 : 0 < N ^ (-(1 + D)) := Real.rpow_pos_of_pos hN0 _
  have hPm : (N ^ (-(1 + D))) ^ m ≤ STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m := pow_le_pow_left₀ hP0.le hP m
  have hPm' : (N ^ (-(1 + D))) ^ m = N ^ (-(1 + D) * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have hA6' : 0 ≤ STAI sz n ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hA0.le _
  have hm2' : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
  calc N ^ (-(3 + 2 * D)) ≤ N ^ (-1 : ℝ) * N ^ (-(1 + D) * m) := by
        rw [← Real.rpow_add hN0]
        refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
        nlinarith
    _ = N ^ (-1 : ℝ) * 1 * (N ^ (-(1 + D))) ^ m := by rw [hPm']; ring
    _ ≤ STAI sz n ^ (-(1 / 2) : ℝ) * (etaT E u)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m :=
        mul_le_mul (mul_le_mul hA6 hη (by norm_num) hA6') hPm (by positivity) (by positivity)

/-- `(1-t)⁻¹ ≤ N` in the window: `1 - t ≥ ilambda²/L^d`, `A ≥ 1`. -/
private theorem etermsMid_htN (n : ℕ) {t : ℝ} (hl : 0 < sz.lam n) (hA : 1 ≤ STAI sz n)
    (hRegt : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t) :
    (1 - t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have h1 : (1 - t)⁻¹ ≤ (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := inv_anti₀ (div_pos hg2 hLd) hRegt
  refine h1.trans ?_
  rw [inv_div, hsz]
  have hA' : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hA
  rw [div_le_iff₀ hg2]
  nlinarith [mul_pos hWd hLd]

/-- **The three error terms, uniformly in `u ∈ [s,t]`** (`(S5WG+M)`, the last two conjuncts): the net lift of
`etermsMid_sections` for `ℰ^{G̃}` (Hölder: `LemDecCalELip_EGt`) and for `(ℰ⊗ℰ)^{M,(2;k)}` (Hölder: `etermsMid_EEk_sub`). -/
private theorem etermsMid_BC_prec (hd : 3 ≤ d) {κ' 𝔡 𝔠 : ℝ} {E s t : ℕ → ℝ} (hAd : sz.Admissible 𝔠 𝔡)
    (hκ' : 0 < κ') (h𝔡 : 0 < 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ') (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hReg : STReg5Mid sz s t) {D : ℝ} (hD : 0 < D)
    (hsecG : ∀ tt : ∀ n, TimeIcc s t n,
      sz.Prec (U := STLab sz) (fun n v ω => ‖STEGt sz n (E n) (tt n : ℝ) v.1 v.2 ω‖)
        (fun n v _ => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (tt n : ℝ))⁻¹ *
          STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1)))
    (hsecE : ∀ tt : ∀ n, TimeIcc s t n,
      sz.Prec (U := fun n => Fin 2 × STLab sz n)
        (fun n v ω => ‖STEEk sz n (E n) (tt n : ℝ) v.1 v.2.1 v.2.2 ω‖)
        (fun n v _ => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (tt n : ℝ))⁻¹ *
          STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2.2 0) (v.2.2 1) ^ 2)) :
    sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    sz.Prec (U := fun n => STIdx2 sz s t n × Fin 2)
      (fun n p ω => ‖STEEk sz n (E n) (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1.1 : ℝ))⁻¹ *
        STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hsize : sz.SizeTendsto := hAd.2.2.1
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_size sz hsize
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [ht1 n, hs n]
  have hevent : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [etermsMid_lam sz hAd, etermsMid_A_big sz hAd 1] with n hl hA1
    exact etermsMid_htN sz n hl.1 hA1 (hReg n).1
  have hbigN : ∀ᶠ n in atTop, 4 ≤ sz.size n ∧ (𝔡⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ∧
      256 * 𝔡⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ 2 ≤ ((sz.size n : ℕ) : ℝ) ∧ 18 ≤ ((sz.size n : ℕ) : ℝ) ∧
      1 ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [hsize.eventually_ge_atTop (max 4 (max ((𝔡⁻¹) ^ 2) (max (256 * 𝔡⁻¹) 18)))] with n hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hn
      exact_mod_cast this
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hn
    · exact (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
    · exact (by norm_num : (2 : ℝ) ≤ 4).trans ((le_max_left _ _).trans hn)
    · exact (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
    · exact (by norm_num : (1 : ℝ) ≤ 4).trans ((le_max_left _ _).trans hn)
  refine ⟨?_, ?_⟩
  · -- `ℰ^{G̃}`
    obtain ⟨C, hC0, hCH⟩ := LemDecCalELip_EGt sz E s t κ' hd hsize hκ' hE hs ht1 hevent
    refine etermsMid_lift2 sz (V := STLab sz) hsize hst hlen (Cv := 3) (CR := 3 + 2 * D) (by norm_num)
      (by linarith) ?_ (fun n p ω => ‖STEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) hsecG ?_ ⟨C, hC0, ?_⟩ ?_
    · filter_upwards [hbigN] with n hb
      exact ST_card_lab_le sz n hb.1
    · filter_upwards [etermsMid_lam sz hAd, hbigN] with n hl hb p ω
      obtain ⟨⟨u, hsu, hut⟩, v⟩ := p
      have := etermsMid_floor sz hd1 n 1 (by norm_num) (hE2 n) ((hs n).trans hsu) (lt_of_le_of_lt hut (ht1 n)) h𝔡
        hl.1 hl.2 hD.le hb.2.1 hb.2.2.2.2.2 (v.2 0) (v.2 1)
      simpa only [pow_one] using this
    · filter_upwards [hCH, hsizeN.eventually (eventually_ge_atTop 1)] with n hn hN1 ω hω u u' v
      exact (abs_norm_sub_norm_le _ _).trans (hn ω hω u u' v.1 v.2)
    · intro A hA
      filter_upwards [etermsMid_lam sz hAd, hevent, hbigN] with n hl hN hb u u' hΔ v ω
      have := etermsMid_zeta_close sz n (E := E n) (D := D) hd1 1 (by norm_num) (hE2 n) hl.1.le hl.2 (ht1 n) u.2.2 u'.2.2
        hN hb.2.2.2.1 hb.2.2.1 hA hΔ (v.2 0) (v.2 1)
      simp only [pow_one] at this
      change STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (u' : ℝ))⁻¹ * _ ≤ 2 * (STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (u : ℝ))⁻¹ * _)
      have hA6 : 0 ≤ STAI sz n ^ (-(1 / 2) : ℝ) := by
        unfold STAI; exact Real.rpow_nonneg (by positivity) _
      calc _ = STAI sz n ^ (-(1 / 2) : ℝ) * ((etaT (E n) (u' : ℝ))⁻¹ * _) := by ring
        _ ≤ STAI sz n ^ (-(1 / 2) : ℝ) * (2 * ((etaT (E n) (u : ℝ))⁻¹ * _)) :=
          mul_le_mul_of_nonneg_left this hA6
        _ = _ := by ring
  · -- `(ℰ⊗ℰ)^{M}`
    have h := etermsMid_lift2 sz (V := fun n => Fin 2 × STLab sz n) hsize hst hlen (Cv := 4) (CR := 3 + 2 * D)
      (by norm_num) (by linarith) ?_ (fun n p ω => ‖STEEk sz n (E n) (p.1 : ℝ) p.2.1 p.2.2.1 p.2.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2.2 0) (p.2.2.2 1) ^ 2) hsecE ?_ ⟨21, by norm_num, ?_⟩ ?_
    · have h' := StochDomAt.precomp_param h (fun n (p : STIdx2 sz s t n × Fin 2) => (p.1.1, (p.2, p.1.2.1, p.1.2.2)))
      exact h'
    · filter_upwards [hbigN] with n hb
      exact ST_card_fin2_lab_le sz n hb.1
    · filter_upwards [etermsMid_lam sz hAd, hbigN] with n hl hb p ω
      obtain ⟨⟨u, hsu, hut⟩, v⟩ := p
      exact etermsMid_floor sz hd1 n 2 (le_refl 2) (hE2 n) ((hs n).trans hsu) (lt_of_le_of_lt hut (ht1 n)) h𝔡
        hl.1 hl.2 hD.le hb.2.1 hb.2.2.2.2.2 (v.2.2 0) (v.2.2 1)
    · filter_upwards [LemDecCalELip_env sz E t κ' hκ' hE hsize hevent 18] with n hn ω hω u u' v
      obtain ⟨h18, h1, hE', hQ, hN1⟩ := hn
      have hsub := etermsMid_EEk_sub sz n (E n) ω (N := ((sz.size n : ℕ) : ℝ)) rfl h1 hE' (ht1 n)
        ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1) u'.2.2 hQ (fun c => hω c) v.1 v.2.1 v.2.2
      refine (abs_norm_sub_norm_le _ _).trans (hsub.trans ?_)
      have hs0 : 0 ≤ Real.sqrt |(u : ℝ) - (u' : ℝ)| := Real.sqrt_nonneg _
      have hN20 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ 20 := by positivity
      have e : ((sz.size n : ℕ) : ℝ) ^ (21 : ℝ) = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 20 := by
        rw [show (21 : ℝ) = ((21 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right h18 (mul_nonneg hN20 hs0)]
    · intro A hA
      filter_upwards [etermsMid_lam sz hAd, hevent, hbigN] with n hl hN hb u u' hΔ v ω
      have := etermsMid_zeta_close sz n (E := E n) (D := D) hd1 2 (le_refl 2) (hE2 n) hl.1.le hl.2 (ht1 n) u.2.2 u'.2.2
        hN hb.2.2.2.1 hb.2.2.1 hA hΔ (v.2.2 0) (v.2.2 1)
      change STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (u' : ℝ))⁻¹ * _ ≤ 2 * (STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (E n) (u : ℝ))⁻¹ * _)
      have hA6 : 0 ≤ STAI sz n ^ (-(1 / 2) : ℝ) := by
        unfold STAI; exact Real.rpow_nonneg (by positivity) _
      calc _ = STAI sz n ^ (-(1 / 2) : ℝ) * ((etaT (E n) (u' : ℝ))⁻¹ * _) := by ring
        _ ≤ STAI sz n ^ (-(1 / 2) : ℝ) * (2 * ((etaT (E n) (u : ℝ))⁻¹ * _)) :=
          mul_le_mul_of_nonneg_left this hA6
        _ = _ := by ring

end Lift

/-! ## 9. The target -/

/-- **`(S5WG+M000)`, `(S5WG+M)`** (`3_5:1961-1979`; the target `STEtermsMid`, `Induction/Step5Pins.lean:275`, S5-13)
from the light-weight pin `STLWT` (the LW gate proves it, `STLWT_of_LWtermExp`): in the window
`ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²`, uniformly in `u ∈ [s,t]` and every `D > 0`,
`ℰ^{LK×LK} ≺ A^{-1/3} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`, `ℰ^{G̃} ≺ A^{-1/2} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`,
`(ℰ⊗ℰ)^{M,(2;k)} ≺ A^{-1/2} η_u⁻¹ (W^{-d}𝒯̃^L_{u,D})²`, `A = ilambda² W^d`.  The constant `𝔠_d` of the pin is
`min (1/100, 1/(30 C_d))`, so that `ρ_u^{C_d} Δ_u^{1/5} ≤ 2 A^{-1/6}`. -/
theorem stEtermsMid_of_LWT (d : ℕ) (hLWT : STLWT d) : STEtermsMid d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨min (1 / 100) (1 / (30 * Cd)), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg _hKb _hKw _hLKs _hDec _hDecS hCon _hStep1 hStep2 _hLmax _hLKU D hD
  obtain ⟨hLoc, -, hGd⟩ := hStep2
  have h𝔠d : 0 < min (1 / 100) (1 / (30 * Cd)) := lt_min (by norm_num) (by positivity)
  have hcC : min (1 / 100) (1 / (30 * Cd)) * Cd ≤ 1 / 30 := by
    calc min (1 / 100) (1 / (30 * Cd)) * Cd ≤ (1 / (30 * Cd)) * Cd :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hCd.le
      _ = 1 / 30 := by field_simp
  have hAd : sz.Admissible 𝔠 𝔡 := hflow.1
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hAd.2.2.1
  obtain ⟨-, hEb, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htz
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ / 2 := fun n => (hEb n).le
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => by have := hEb n; linarith
  have hd0 : 0 < d := by omega
  have ht0 : ∀ n, 0 ≤ t n := fun n => (hs n).trans (hst n).le
  -- the size data `cB W^{-d} ≤ W^{-d} B_{u,0} ≤ N^{-c}`
  obtain ⟨cB, hcB, hBdata⟩ := ST_Bdata_holds hd0 κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hBdz⟩ := hBdata 𝔠
  have hBd := hBdz sz z hflow t ht0 htz
  have hB1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → sz.Bctl n u ≤ 1 := by
    filter_upwards [hBd, hsize.eventually (eventually_ge_atTop 1)] with n hn hN1 u hu0 hut
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    exact (hn u hu0 hut).2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  have hBdc : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    filter_upwards [hBd] with n hn u hu0 hut using (hn u hu0 hut).2
  -- the deterministic pins
  obtain ⟨CK, hCK, hK2d⟩ := stK2decay_holds d hd (κ / 2) 𝔡 (half_pos hκ) h𝔡
  have hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u → u ≤ t n →
      0 ≤ D → ‖STKloop sz n (STflowE z n) u σ a‖ ≤ CK * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
    filter_upwards [etermsMid_lam sz hAd] with n hl u D σ a hsu hut hD0
    exact hK2d sz n (STflowE z n) u D hl.1 hl.2 (hE n) ((hs n).trans hsu) (lt_of_le_of_lt hut (ht1 n)) hD0 σ a
  obtain ⟨C, δ₀, hC, hδ₀, hnew⟩ := stNewKLKL_holds d hd (κ / 2) 𝔡 (half_pos hκ) h𝔡
  have hEMe : STEMn2Exp d := stEMn2Exp_holds d hd
  have hS1W : STStep1Weak sz (STflowE z) s t := etermsMid_S1W sz hLoc hB1 hs
  have hL2 := fun D (hD : 0 < D) => etermsMid_L2 sz hAd hReg hCon h𝔠d hCd hcC hGd hCK hK2 hD
  have hJ := fun D (hD : 0 < D) => etermsMid_J sz hAd hReg hCon h𝔠d hCd hcC hGd hD
  have hsec := fun (tt : ∀ n, TimeIcc s t n) =>
    etermsMid_sections sz hLWT hEMe hd0 hκ hε h𝔡 hflow hs htz hReg hS1W hcB hc hBd hL2 hJ tt hD
  have hBC := etermsMid_BC_prec sz hd hAd (half_pos hκ) h𝔡 hE hs (fun n => (hst n).le) ht1 hReg hD
    (fun tt => (hsec tt).1) (fun tt => (hsec tt).2)
  exact ⟨etermsMid_A_prec sz hAd hReg hCon h𝔠d hCd hcC hGd hLoc hnew hC hδ₀ hE hE2 hs ht1 h𝔡 hc hBdc hD,
    hBC.1, hBC.2⟩

end RBM.Gauss.Sizes

/-! ## 10. Compiled nonempty instances (`d = 3`)

The merged Step-5 data of case (i) (`RBM.Gauss.Step5Inst`): `szB` (`L = 4`, `W_n = n + 4`, `ilambda = 1`), the flow
`zB_n = 1/2 + i/64`, `(s, t) = (7/8, 15/16)`, i.e. `1/64 = ilambda²/L^3 ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ ilambda² = 1`
(`STReg5Mid`).  Every deterministic hypothesis (flow, time ranges, window, `(con_st_ind)` at every `𝔠_d > 0`) is discharged
by the merged `inst_ing5_I`; what stays a hypothesis is `STLWT 3` (the LW gate's pin) and the stochastic premises of
Steps 1-4 inside `InstIng5Concl`. -/

namespace RBM.Gauss.EtermsMidInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst

/-- **The target `stEtermsMid_of_LWT` at `d = 3`**: at `(szB, zB, 7/8, 15/16)` and `C_d = 1`, the constant `𝔠_d` of the pin
exists, and the three bounds follow from the Step 1-4 premises (hypotheses) and `STLWT 3` (hypothesis). -/
example (hLWT : STLWT 3) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) 1 :=
  inst_etermsMid (stEtermsMid_of_LWT 3 hLWT) 1 one_pos

/-- The same at `C_d = 100`. -/
example (hLWT : STLWT 3) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) 100 :=
  inst_etermsMid (stEtermsMid_of_LWT 3 hLWT) 100 (by norm_num)

/-- The window `1/(2A) ≤ W^{-d}B_{u,0} ≤ 2/A` at `(szB, n, u = 15/16)`, `A = (n+4)^3`. -/
example (n : ℕ) : 1 / (2 * STAI szB n) ≤ szB.Bctl n (15 / 16) ∧ szB.Bctl n (15 / 16) ≤ 2 / STAI szB n :=
  etermsMid_Bctl_window szB n (by simp [szB]) (by norm_num [szB]) (by norm_num [szB])

/-- The exponent arithmetic `ρ^{C_d} Δ^{1/5} ≤ 2 A^{-1/6}` (`𝔠_d C_d ≤ 1/30`, `ρ ≤ Δ_t^{-𝔠_d}`) at `A = 8`, `C_d = 1`,
`𝔠_d = 1/100`, `ρ = 101/100`, `Δ_t = 1/12 ∈ [1/(2A), 2/A]`, `Δ_u = 1/8 ≤ 2/A`. -/
example : ((101 / 100 : ℝ)) ^ (1 : ℝ) * (1 / 8 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 * (8 : ℝ) ^ (-(1 / 6) : ℝ) := by
  refine etermsMid_q_le (A := 8) (ρ := 101 / 100) (b := 1 / 8) (bt := 1 / 12) (Cd := 1) (c := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (1 / 12 : ℝ) = 12⁻¹ by norm_num, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  calc (101 / 100 : ℝ) = ((101 / 100 : ℝ) ^ 100) ^ (((100 : ℕ) : ℝ)⁻¹) := by
        rw [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    _ ≤ 12 ^ (1 / 100 : ℝ) := by
        rw [show (1 / 100 : ℝ) = ((100 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)

end RBM.Gauss.EtermsMidInst
