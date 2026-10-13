/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.IniTermIGen

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The initial term of Step 5, case (i), over the carrier: the Ward step, the real-level estimates and the pin (T2484, U4s2b)

Second part of `Chain/IniTermIGen.lean` (the reserve file of the ticket, used under the 1,800-line rule): target 8 (d) (the Ward
step at the last label from `B45_ward_fing` and `ZeroModeGen_WardCls`, one Ward text; the real-level estimates of each case,
`σ₁ = σ₂`, `ρ`-lossy, outside and inside the window), target 9 (`iniTermIGen_concl` and the pin `stIniTermIgL_of`), and the band
re-derivation `iniTermIGen_band_holds` of `stIniTermI_holds` (`IniTermI:3715`).  Paper: arXiv:2507.20274, `(iksjuwjx0)`,
`3_5:2072-2172`.  No new mathematics.

The real-level lemmas of §20 of `Induction/IniTermI.lean` (ported below) are pure real inequalities for `U = ‖𝒰 X‖` with the
core bounds as hypotheses: the band model enters only through the cores (`IniTermIGen`), so the lemmas are stated for reals.

Ported from `Induction/IniTermI.lean` of this project (last commit of the file `850a8a3b`): §18 `ward` (`:2646`), `ward_bound` (`:3455`), §20
`rl_same/lossy/tail/in/all` (`:2818-3199`), §22 `concl` (`:3509`), `holds` (`:3715`) for the carrier.  The d = 1 and d = 2
projects are not used.
-/

open private IniTermIGen_mixed_bound IniTermIGen_mixed_tail IniTermIGen_Sfull IniTermIGen_Kf IniTermIGen_Th_decay
  IniTermIGen_theta_pi IniTermIGen_theta_far IniTermIGen_theta_conv IniTermIGen_core_data from RBM3D.Chain.IniTermIGen
open private CltFarUGen_fSum CltFarUGen_guard from RBM3D.Chain.CltFarUGen
open private Step5KerGen_cmp_pos from RBM3D.Chain.Step5KerGen

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-! ## 1. Target 8 (d): the real-level estimates -/

section RealLevel

variable {d : ℕ}

/-- `σ₁ = σ₂`: the short-range initial term is `≤ 2 C_s Θ (a P₀ + W^{-D})` (band `iniTermI_rl_same`, `IniTermI:2818`). -/
private theorem IniTermIGen_rl_same {W D D₁ Θ a P₀ lam₀ Tu Cs U : ℝ} (hW : 0 < W) (hΘ : 1 ≤ Θ) (hlam : 0 ≤ lam₀)
    (hlam2 : lam₀ ≤ 2 * a) (ha : 0 ≤ a) (hF : W ^ (-D₁) ≤ W ^ (-D)) (hCs : 0 ≤ Cs) (hK : 2 * Cs ≤ Θ ^ 3) (hTu : 0 ≤ Tu)
    (hP : (W ^ d)⁻¹ * Tu ≤ P₀) (h : U ≤ Cs * Θ * (lam₀ * (W ^ d)⁻¹ * Tu + W ^ (-D₁))) :
    U ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  have hτ0 : 0 ≤ (W ^ d)⁻¹ * Tu := by positivity
  have hP0 : 0 ≤ P₀ := hτ0.trans hP
  have h1 : lam₀ * (W ^ d)⁻¹ * Tu ≤ 2 * a * P₀ := by
    rw [mul_assoc]; exact mul_le_mul hlam2 hP hτ0 (by positivity)
  have hF0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hΘ0 : 0 ≤ Θ := by linarith
  have haP : 0 ≤ a * P₀ := mul_nonneg ha hP0
  calc U ≤ Cs * Θ * (lam₀ * (W ^ d)⁻¹ * Tu + W ^ (-D₁)) := h
    _ ≤ Cs * Θ * (2 * (a * P₀) + W ^ (-D)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ ≤ (2 * Cs) * Θ * (a * P₀ + W ^ (-D)) := by
        have : 0 ≤ Cs * Θ := by positivity
        nlinarith [mul_nonneg this haP, mul_nonneg this hF0]
    _ ≤ Θ ^ 3 * Θ * (a * P₀ + W ^ (-D)) := by
        gcongr
    _ = _ := by ring

/-- `σ₁ ≠ σ₂`, `ρ ≤ Γ₀` (`ρ ≤ (log W)^{10}` or any polylog): the `ρ`-lossy bound (band `iniTermI_rl_lossy`, `IniTermI:2851`). -/
private theorem IniTermIGen_rl_lossy {W D D₁ Θ a P₀ lam₀ Tu Cl Γ₀ ρ U : ℝ} (hW : 0 < W) (hΘ : 1 ≤ Θ) (hlam : 0 ≤ lam₀)
    (hlam2 : lam₀ ≤ 2 * a) (ha : 0 ≤ a) (hΓ : 1 ≤ Γ₀) (hρ0 : 0 ≤ ρ) (hρΓ : ρ ≤ Γ₀) (hρF : ρ * ρ * W ^ (-D₁) ≤ W ^ (-D))
    (hCl : 0 ≤ Cl) (hK : 2 * Cl * Γ₀ ≤ Θ ^ 3) (hTu : 0 ≤ Tu) (hP : (W ^ d)⁻¹ * Tu ≤ P₀)
    (h : U ≤ Cl * Θ * (ρ * (lam₀ * (W ^ d)⁻¹ * Tu + ρ * W ^ (-D₁)))) : U ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  have hτ0 : 0 ≤ (W ^ d)⁻¹ * Tu := by positivity
  have hP0 : 0 ≤ P₀ := hτ0.trans hP
  have h1 : ρ * (lam₀ * (W ^ d)⁻¹ * Tu) ≤ Γ₀ * (2 * a * P₀) := by
    rw [mul_assoc]
    exact mul_le_mul hρΓ (mul_le_mul hlam2 hP hτ0 (by positivity)) (by positivity) (by linarith)
  have hF0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hΘ0 : 0 ≤ Θ := by linarith
  have haP : 0 ≤ a * P₀ := mul_nonneg ha hP0
  have hCΘ : 0 ≤ Cl * Θ := by positivity
  calc U ≤ Cl * Θ * (ρ * (lam₀ * (W ^ d)⁻¹ * Tu + ρ * W ^ (-D₁))) := h
    _ ≤ Cl * Θ * (Γ₀ * (2 * a * P₀) + W ^ (-D)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCΘ
        have : ρ * (lam₀ * (W ^ d)⁻¹ * Tu + ρ * W ^ (-D₁)) =
            ρ * (lam₀ * (W ^ d)⁻¹ * Tu) + ρ * ρ * W ^ (-D₁) := by ring
        rw [this]; linarith
    _ ≤ (2 * Cl * Γ₀) * Θ * (a * P₀ + W ^ (-D)) := by
        have e : 2 * Cl * Γ₀ * Θ * (a * P₀ + W ^ (-D)) - Cl * Θ * (Γ₀ * (2 * a * P₀) + W ^ (-D)) =
            Cl * Θ * ((2 * Γ₀ - 1) * W ^ (-D)) := by ring
        have : 0 ≤ Cl * Θ * ((2 * Γ₀ - 1) * W ^ (-D)) := by
          have : 0 ≤ 2 * Γ₀ - 1 := by linarith
          positivity
        linarith
    _ ≤ Θ ^ 3 * Θ * (a * P₀ + W ^ (-D)) := by
        gcongr
    _ = _ := by ring

/-- `σ₁ ≠ σ₂`, outside the window `(eq:ells_to_ellt2)`: the whole term is `ρ`-lossless up to the explicit floor
`Tail ≤ W^{-D}` (band `iniTermI_rl_tail`, `IniTermI:2897`). -/
private theorem IniTermIGen_rl_tail {W D D₁ Θ a P₀ lam₀ Tu K ρ Tail U : ℝ} (hW : 0 < W) (hΘ : 1 ≤ Θ) (hlam : 0 ≤ lam₀)
    (hlam2 : lam₀ ≤ 2 * a) (ha : 0 ≤ a) (hρF : ρ * W ^ (-D₁) ≤ W ^ (-D)) (hK0 : 0 ≤ K) (hK : 2 * K + 1 ≤ Θ ^ 3)
    (hTu : 0 ≤ Tu) (hP : (W ^ d)⁻¹ * Tu ≤ P₀) (htail : Tail ≤ W ^ (-D))
    (h : U ≤ K * Θ * (lam₀ * (W ^ d)⁻¹ * Tu + ρ * W ^ (-D₁)) + Tail) : U ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  have hτ0 : 0 ≤ (W ^ d)⁻¹ * Tu := by positivity
  have hP0 : 0 ≤ P₀ := hτ0.trans hP
  have h1 : lam₀ * (W ^ d)⁻¹ * Tu ≤ 2 * a * P₀ := by
    rw [mul_assoc]; exact mul_le_mul hlam2 hP hτ0 (by positivity)
  have hF0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hΘ0 : 0 ≤ Θ := by linarith
  have haP : 0 ≤ a * P₀ := mul_nonneg ha hP0
  have hKΘ : 0 ≤ K * Θ := by positivity
  calc U ≤ K * Θ * (lam₀ * (W ^ d)⁻¹ * Tu + ρ * W ^ (-D₁)) + Tail := h
    _ ≤ K * Θ * (2 * (a * P₀) + W ^ (-D)) + W ^ (-D) :=
        add_le_add (mul_le_mul_of_nonneg_left (by linarith) hKΘ) htail
    _ ≤ ((2 * K + 1) * Θ) * (a * P₀ + W ^ (-D)) := by
        have e : (2 * K + 1) * Θ * (a * P₀ + W ^ (-D)) - (K * Θ * (2 * (a * P₀) + W ^ (-D)) + W ^ (-D)) =
            K * Θ * W ^ (-D) + (Θ - 1) * W ^ (-D) + Θ * (a * P₀) := by ring
        have : 0 ≤ K * Θ * W ^ (-D) + (Θ - 1) * W ^ (-D) + Θ * (a * P₀) := by
          have : 0 ≤ Θ - 1 := by linarith
          positivity
        linarith
    _ ≤ Θ ^ 3 * Θ * (a * P₀ + W ^ (-D)) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- `σ₁ ≠ σ₂`, in the window (`ρ > (log W)^{10}`, `|a₁-a₂| ≲ (log W)^{3/2} ℓ_u`): `f^{near}`, the Ward term and `f^{far}`
(`(iksjuwjx3)`, `(eq:boundga)`, `lem;CLT`) give `≤ Θ⁴ (a P₀ + W^{-D})` (band `iniTermI_rl_in`, `IniTermI:2980`); `U` is the norm of
the term, `hh` the mixed bound, `Fn = ‖f^{far}‖`, `PIv = (|a₁-a₂|+1)^{-(d-2)}`, `Pr = (|a₁-a₂|^{d-2}+1)⁻¹`. -/
private theorem IniTermIGen_rl_in {W D D₁ Θ a P₀ lam₀ Tu Bs κm Km ρ lW g PIv Pr Fn T3 U : ℝ} (hW : 0 < W) (hκm : 0 < κm)
    (hlW : 1 ≤ lW) (hΘ : 1 ≤ Θ) (hlam : 0 ≤ lam₀) (hlam2 : lam₀ ≤ 2 * a) (ha : 0 ≤ a) (hBs : 0 ≤ Bs) (hρ0 : 0 ≤ ρ)
    (hρF : ρ * W ^ (-D₁) ≤ W ^ (-D)) (hρB : ρ * Bs ≤ 4 * a) (hKm : 0 ≤ Km)
    (hK : (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm)) * (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) ≤ Θ ^ 3) (hTu : 0 ≤ Tu)
    (hh : U ≤ Fn + Km * (Θ * (lam₀ * (W ^ d)⁻¹ * Tu + ρ * W ^ (-D₁)) + Θ * (lam₀ * (W ^ d)⁻¹) * (g ^ 2)⁻¹ * lW ^ 14 * PIv +
      T3 + ρ * (Θ * (Bs * (W ^ d)⁻¹ / κm)) * Tu))
    (hcmp : (g ^ 2 * W ^ d)⁻¹ * Pr ≤ 2 ^ d * Real.exp (lW ^ (3 / 4 : ℝ)) * ((W ^ d)⁻¹ * Tu))
    (hPI : PIv ≤ Pr) (hPI0 : 0 ≤ PIv) (hτ : (W ^ d)⁻¹ * Tu ≤ P₀) (hT3 : T3 ≤ W ^ (-D))
    (hfar : Fn ≤ Θ * (a * ((g ^ 2 * W ^ d)⁻¹ * Pr))) : U ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  set τu : ℝ := (W ^ d)⁻¹ * Tu with hτu
  have hτ0 : 0 ≤ τu := by positivity
  have hP0 : 0 ≤ P₀ := hτ0.trans hτ
  have hΘ0 : 0 ≤ Θ := by linarith
  have hF0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  set e : ℝ := Real.exp (lW ^ (3 / 4 : ℝ)) with he
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  set Γ : ℝ := lW ^ 14 * e with hΓ
  have hlW14 : 1 ≤ lW ^ 14 := one_le_pow₀ hlW
  have hΓ1 : 1 ≤ Γ := by nlinarith
  have heΓ : e ≤ Γ := by nlinarith
  have hΓ0 : 0 ≤ Γ := by linarith
  have haP : 0 ≤ a * P₀ := mul_nonneg ha hP0
  set Bq : ℝ := (g ^ 2 * W ^ d)⁻¹ * Pr with hBq
  have hBq' : Bq ≤ 2 ^ d * e * τu := hcmp
  have hlW0 : 0 ≤ lW := by linarith
  have hT1 : Θ * (lam₀ * (W ^ d)⁻¹ * Tu + ρ * W ^ (-D₁)) ≤ Θ * (2 * (a * P₀) + W ^ (-D)) := by
    refine mul_le_mul_of_nonneg_left ?_ hΘ0
    have : lam₀ * (W ^ d)⁻¹ * Tu ≤ 2 * a * P₀ := by
      rw [mul_assoc]; exact mul_le_mul hlam2 hτ hτ0 (by positivity)
    linarith
  have hT2 : Θ * (lam₀ * (W ^ d)⁻¹) * (g ^ 2)⁻¹ * lW ^ 14 * PIv ≤ 2 * 2 ^ d * Θ * Γ * (a * P₀) := by
    have e1 : Θ * (lam₀ * (W ^ d)⁻¹) * (g ^ 2)⁻¹ * lW ^ 14 * PIv =
        Θ * lW ^ 14 * lam₀ * ((g ^ 2 * W ^ d)⁻¹ * PIv) := by
      rw [mul_inv]; ring
    have e3 : (g ^ 2 * W ^ d)⁻¹ * PIv ≤ 2 ^ d * e * P₀ :=
      (mul_le_mul_of_nonneg_left hPI (by positivity)).trans (hBq'.trans (mul_le_mul_of_nonneg_left hτ (by positivity)))
    rw [e1]
    calc Θ * lW ^ 14 * lam₀ * ((g ^ 2 * W ^ d)⁻¹ * PIv)
        ≤ Θ * lW ^ 14 * (2 * a) * (2 ^ d * e * P₀) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlam2 (by positivity)) e3 (mul_nonneg (by positivity) hPI0) (by positivity)
      _ = _ := by rw [hΓ]; ring
  have hT4 : ρ * (Θ * (Bs * (W ^ d)⁻¹ / κm)) * Tu ≤ 4 / κm * Θ * (a * P₀) := by
    have e1 : ρ * (Θ * (Bs * (W ^ d)⁻¹ / κm)) * Tu = Θ / κm * (ρ * Bs) * τu := by rw [hτu]; field_simp
    rw [e1]
    calc Θ / κm * (ρ * Bs) * τu ≤ Θ / κm * (4 * a) * P₀ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hρB (by positivity)) hτ hτ0 (by positivity)
      _ = _ := by field_simp
  have hfar' : Fn ≤ 2 ^ d * Θ * Γ * (a * P₀) := by
    refine hfar.trans ?_
    have e1 : Bq ≤ 2 ^ d * e * P₀ := hBq'.trans (mul_le_mul_of_nonneg_left hτ (by positivity))
    have e2 : 2 ^ d * e * P₀ ≤ 2 ^ d * Γ * P₀ := by gcongr
    calc Θ * (a * Bq) ≤ Θ * (a * (2 ^ d * Γ * P₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (e1.trans e2) ha) hΘ0
      _ = _ := by ring
  have hfin := iniTermI_assemble hΘ hΓ1 haP hF0 hKm (by positivity : (0 : ℝ) ≤ 2 ^ d) (by positivity : (0 : ℝ) ≤ 4 / κm)
    hfar' hT1 hT2 hT3 hT4 hh
  calc U ≤ Θ * ((2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm)) * Γ) * (a * P₀ + W ^ (-D)) := hfin
    _ ≤ Θ * Θ ^ 3 * (a * P₀ + W ^ (-D)) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **All cases at once** (`(iksjuwjx0)`, `3_5:2072`, case (i); band `iniTermI_rl_all`, `IniTermI:3099`): `σ₁ = σ₂`
(`prop:ThfadC_short`); `σ₁ ≠ σ₂` with `ρ ≤ (log W)^{10}` (`(uwp2-92kj)` twice); `ρ > (log W)^{10}`, outside the window
`(eq:ells_to_ellt2)` (exponential decay), inside the window (`f^{near}`, Ward, `lem;CLT`).  The core bounds on `U = ‖𝒰 X‖` are the
hypotheses `hsameU`, `hlossyU`, `hmbU`, `htailU`; `hin`/`hout` are the window facts; the conclusion is `U ≤ Θ⁴ (a P₀ + W^{-D})`,
`Θ = N^{τ/4}`, `a = A^{-1/5}`, `P₀ = W^{-d}𝒯̃`. -/
private theorem IniTermIGen_rl_all {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L)
    {g W D D₁ s u Θ a P₀ lam₀ lW Bs κm Cs Cl Kt Km U Fn T3 Tail : ℝ} {σ : Fin 2 → Bool} {x : Fin 2 → Zd d L}
    (X : (Fin 2 → Zd d L) → ℂ) (hg : 0 < g) (hW : 0 < W) (hκm : 0 < κm) (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) (hregs1 : 1 - s ≤ g ^ 2) (hlW : 2 ≤ lW) (hΘ : 1 ≤ Θ) (hlam : 0 ≤ lam₀)
    (hlam2 : lam₀ ≤ 2 * a) (ha : 0 ≤ a) (hBs : 0 ≤ Bs) (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl) (hKt : 0 ≤ Kt) (hKm : 0 ≤ Km)
    (hF : W ^ (-D₁) ≤ W ^ (-D)) (hρF1 : (1 - s) / (1 - u) * W ^ (-D₁) ≤ W ^ (-D))
    (hρF2 : (1 - s) / (1 - u) * ((1 - s) / (1 - u)) * W ^ (-D₁) ≤ W ^ (-D))
    (hρB : (1 - s) / (1 - u) * Bs ≤ 4 * a)
    (hK : (2 * Cs + 2 * Cl + (2 * Kt + 1) + (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm))) *
      (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) ≤ Θ ^ 3)
    (hP₀ : (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ P₀)
    (hsameU : σ 0 = σ 1 → U ≤ Cs * Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) + W ^ (-D₁)))
    (hlossyU : σ 0 ≠ σ 1 → U ≤ Cl * Θ * ((1 - s) / (1 - u) * (lam₀ * (W ^ d)⁻¹ *
      tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D₁))))
    (hmbU : σ 0 ≠ σ 1 → (∀ b₁ : Zd d L, ‖∑ b₂ : Zd d L, X ![b₁, b₂]‖ ≤ Θ * (Bs * (W ^ d)⁻¹ / κm) / (1 - s)) →
      U ≤ Fn + Km * (Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D₁)) +
        Θ * (lam₀ * (W ^ d)⁻¹) * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (x 0 - x 1) + T3 +
        (1 - s) / (1 - u) * (Θ * (Bs * (W ^ d)⁻¹ / κm)) * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ)))
    (htailU : σ 0 ≠ σ 1 → (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ellT L g u + lW ^ (5 / 2 : ℝ) * ellT L g s <
        ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) →
      U ≤ Kt * Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D₁)) + Tail)
    (hin : σ 0 ≠ σ 1 → lW ^ 10 < (1 - s) / (1 - u) →
      ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ellT L g u + lW ^ (5 / 2 : ℝ) * ellT L g s →
        (∀ b₁ : Zd d L, ‖∑ b₂ : Zd d L, X ![b₁, b₂]‖ ≤ Θ * (Bs * (W ^ d)⁻¹ / κm) / (1 - s)) ∧ T3 ≤ W ^ (-D) ∧
          Fn ≤ Θ * (a * ((g ^ 2 * W ^ d)⁻¹ * ((((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹))))
    (hout : σ 0 ≠ σ 1 → lW ^ 10 < (1 - s) / (1 - u) →
      (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ellT L g u + lW ^ (5 / 2 : ℝ) * ellT L g s < ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) →
        Tail ≤ W ^ (-D)) :
    U ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  have hlW1 : 1 ≤ lW := by linarith
  have hTu : 0 ≤ tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
  have hlW14 : 1 ≤ lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ)) := by
    have := one_le_pow₀ (n := 14) hlW1
    have h2 : 1 ≤ Real.exp (lW ^ (3 / 4 : ℝ)) := Real.one_le_exp (by positivity)
    nlinarith
  have hKsum : 0 ≤ 2 * Cs + 2 * Cl + (2 * Kt + 1) + (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm)) := by positivity
  have hKΘ : ∀ K : ℝ, 0 ≤ K → K ≤ 2 * Cs + 2 * Cl + (2 * Kt + 1) + (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm)) →
      K ≤ Θ ^ 3 := fun K hK0 hKle =>
    hKle.trans (by
      have : (2 * Cs + 2 * Cl + (2 * Kt + 1) + (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm))) * 1 ≤
          (2 * Cs + 2 * Cl + (2 * Kt + 1) + (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm))) *
            (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hlW14 hKsum
      linarith)
  by_cases hσ : σ 0 = σ 1
  · exact IniTermIGen_rl_same hW hΘ hlam hlam2 ha hF hCs (hKΘ _ (by positivity) (by nlinarith [mul_nonneg hKm (by positivity : (0 : ℝ) ≤ 4 + 2 * 2 ^ d + 4 / κm), mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCl, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hKt, (by positivity : (0 : ℝ) ≤ 2 ^ d)])) hTu hP₀ (hsameU hσ)
  have hσ' : σ 0 ≠ σ 1 := hσ
  have hu1 : 0 < 1 - u := by linarith
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg (by linarith) hu1.le
  by_cases hρ : (1 - s) / (1 - u) ≤ lW ^ 10
  · refine IniTermIGen_rl_lossy hW hΘ hlam hlam2 ha (one_le_pow₀ hlW1) hρ0 hρ hρF2 hCl ?_ hTu hP₀ (hlossyU hσ')
    have : 2 * Cl * lW ^ 10 ≤ (2 * Cs + 2 * Cl + (2 * Kt + 1) + (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm))) *
        (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) := by
      have h1 : lW ^ 10 ≤ lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ)) := by
        have : lW ^ 10 ≤ lW ^ 14 := pow_le_pow_right₀ hlW1 (by norm_num)
        have h2 : 1 ≤ Real.exp (lW ^ (3 / 4 : ℝ)) := Real.one_le_exp (by positivity)
        nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ lW) 14]
      have : 2 * Cl ≤ 2 * Cs + 2 * Cl + (2 * Kt + 1) + (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm)) := by
        have := mul_nonneg hKm (by positivity : (0 : ℝ) ≤ 4 + 2 * 2 ^ d + 4 / κm)
        have := (by positivity : (0 : ℝ) ≤ 2 ^ d)
        linarith
      exact mul_le_mul this h1 (by positivity) hKsum
    exact this.trans hK
  push Not at hρ
  by_cases hwin : ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ellT L g u + lW ^ (5 / 2 : ℝ) * ellT L g s
  · obtain ⟨hXY, hT3, hfar⟩ := hin hσ' hρ hwin
    have hs1 : s < 1 := by linarith
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have hℓ1 : 1 ≤ ellT L g s := one_le_ellT hL1
    have hℓ5 : lW ^ 5 * ellT L g s ≤ ellT L g u := iniTermI_ell5 hL hg hsu hu hreg hregs1 (by linarith) hρ
    have hlW0 : 0 ≤ lW := by linarith
    have hl32 : 0 ≤ lW ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlW0 _
    have hl52 : lW ^ (5 / 2 : ℝ) = lW ^ (3 / 2 : ℝ) * lW := by
      rw [← Real.rpow_add_one' hlW0 (by norm_num)]; norm_num
    have hlW5 : 2 * lW ≤ lW ^ 5 := by
      have : 2 ≤ lW ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hlW 4]
      nlinarith
    have hr : ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ≤ lW ^ (3 / 2 : ℝ) * ellT L g u := by
      have h1 : lW ^ (5 / 2 : ℝ) * ellT L g s ≤ 1 / 2 * lW ^ (3 / 2 : ℝ) * ellT L g u := by
        rw [hl52]
        have h2 : 2 * (lW * ellT L g s) ≤ ellT L g u := by
          have := mul_le_mul_of_nonneg_right hlW5 (by linarith : (0 : ℝ) ≤ ellT L g s)
          linarith
        have h3 := mul_le_mul_of_nonneg_left h2 hl32
        linarith
      linarith
    have hθ : Real.sqrt (((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) / ellT L g u) ≤ lW ^ (3 / 4 : ℝ) := by
      have hℓu0 : 0 < ellT L g u := lt_of_lt_of_le one_pos (hℓ1.trans (ellT_mono hg.le hsu hu))
      have : ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) / ellT L g u ≤ lW ^ (3 / 2 : ℝ) := by
        rw [div_le_iff₀ hℓu0]; exact hr
      calc _ ≤ Real.sqrt (lW ^ (3 / 2 : ℝ)) := Real.sqrt_le_sqrt this
        _ = lW ^ (3 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlW0]; norm_num
    have hWd : (0 : ℝ) < W ^ d := by positivity
    have hcmp := iniTermI_cmp hd hL1 hg hu (by linarith) hWd (x 0 - x 1) hθ
    have hpa : ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1 ≤ (((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) + 1) ^ (d - 2) := by
      have := pow_add_pow_le (Nat.cast_nonneg (zdistInf d L (x 0 - x 1))) (zero_le_one' ℝ) (n := d - 2) (by omega)
      simpa using this
    have hPI : iniTermI_PI d L (x 0 - x 1) ≤ ((((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹) := by
      unfold iniTermI_PI
      exact inv_anti₀ (by positivity) hpa
    have hPI0 := iniTermI_PI_nonneg (d := d) (L := L) (x 0 - x 1)
    refine IniTermIGen_rl_in hW hκm hlW1 hΘ hlam hlam2 ha hBs hρ0 hρF1 hρB hKm ?_ hTu (hmbU hσ' hXY) hcmp hPI hPI0 hP₀ hT3 hfar
    have : (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm)) * (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) ≤
        (2 * Cs + 2 * Cl + (2 * Kt + 1) + (2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm))) *
          (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact this.trans hK
  · push Not at hwin
    refine IniTermIGen_rl_tail hW hΘ hlam hlam2 ha hρF1 hKt ?_ hTu hP₀ (hout hσ' hρ hwin) (htailU hσ' hwin)
    exact hKΘ _ (by positivity) (by
      have := mul_nonneg hKm (by positivity : (0 : ℝ) ≤ 4 + 2 * 2 ^ d + 4 / κm)
      have := (by positivity : (0 : ℝ) ≤ 2 ^ d)
      linarith)

end RealLevel

/-! ## 2. Target 8 (d): the Ward step at the last label -/

section Ward

variable {d : ℕ} {sz : Sizes d}

/-- **Ward's identity at the last label** (`(eq:PcalBterm)`, `3_5:2141`; `(WI_calL)`, `(WI_calK)`; band `iniTermI_ward`,
`IniTermI:2646`) over a carrier, from `B45_ward_fing` (the `m = 0` instance, one Ward text `ZeroModeGen_WardCls`): for
`σ₁ ≠ σ₂`, `|Σ_{b₂} (𝓛-𝒦)^{(2)}_{s,σ,(b₁,b₂)}| ≤ (2 W^d η_s)⁻¹ (|(𝓛-𝒦)^{(1)}_{s,+,b₁}| + |(𝓛-𝒦)^{(1)}_{s,-,b₁}|)`. -/
private theorem IniTermIGen_ward (C : FlowFM sz) (hward : ZeroModeGen_WardCls sz C) (n : ℕ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hη : 0 < C.eta n s) (ω : sz.SeqΩ) {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (b₁ : Zd d (sz.L n)) :
    ‖∑ b₂ : Zd d (sz.L n), (C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂])‖ ≤
      (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n s))⁻¹ *
        (‖C.L n s (fun _ : Fin 1 => true) (fun _ => b₁) ω - C.K n s (fun _ : Fin 1 => true) (fun _ => b₁)‖ +
          ‖C.L n s (fun _ : Fin 1 => false) (fun _ => b₁) ω - C.K n s (fun _ : Fin 1 => false) (fun _ => b₁)‖) := by
  have hσl : σ (Fin.last 1) = !σ 0 := by
    have : σ 1 ≠ σ 0 := fun h => hσ h.symm
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all [Fin.last]
  have hw := B45_ward_fing C hward n hs0 hs1 ω (m := 0) σ hσl (fun _ : Fin 1 => b₁)
  have hsn : ∀ x : Zd d (sz.L n), (Fin.snoc (α := fun _ => Zd d (sz.L n)) (fun _ : Fin 1 => b₁) x : Fin 2 → Zd d (sz.L n)) = ![b₁, x] := by
    intro x; funext i; fin_cases i <;> simp [Fin.snoc]
  simp only [hsn] at hw
  have hc : ∀ b : Bool, B45_sgnCons b σ = fun _ : Fin 1 => b := fun b => by funext i; fin_cases i; rfl
  rw [hc true, hc false] at hw
  simp only [STLKtensorg] at hw
  rw [hw, norm_mul]
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hn : ‖(2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n s : ℂ))⁻¹‖ = (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n s))⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hη.le]
    simp; ring
  rw [hn]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)

/-- **Ward + `(Gt_avgbound_flow)`** (`(eq:PcalBterm)`, `3_5:2141`; band `iniTermI_ward_bound`, `IniTermI:3455`): `|Σ_{b₂} 𝓑_{b₁b₂}| ≤
Θ (Bs W^{-d}/κ_m)/(1-s)` from `|(𝓛-𝒦)^{(1)}_{s,±,b₁}| ≤ Θ Bs` and `η_s = (1-s) Im m ≥ (1-s) κ_m` (the flow facts). -/
private theorem IniTermIGen_ward_bound (C : FlowFM sz) (hward : ZeroModeGen_WardCls sz C) (n : ℕ) {s Θ κm : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hκm : 0 < κm) (hη : C.eta n s = (1 - s) * (C.m n).im) (hκ : κm ≤ (C.m n).im)
    (ω : sz.SeqΩ) {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (hΘ : 0 ≤ Θ)
    (h1 : ∀ p : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)),
      ‖C.L n s p.1 p.2 ω - C.K n s p.1 p.2‖ ≤ Θ * (sz.Bctl n s) ^ 1) (b₁ : Zd d (sz.L n)) :
    ‖∑ b₂ : Zd d (sz.L n), (C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂])‖ ≤
      Θ * (sz.Bctl n s * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ / κm) / (1 - s) := by
  have hs1' : 0 < 1 - s := by linarith
  have hη0 : (1 - s) * κm ≤ C.eta n s := by rw [hη]; exact mul_le_mul_of_nonneg_left hκ hs1'.le
  have hηp : 0 < C.eta n s := lt_of_lt_of_le (by positivity) hη0
  have hw := IniTermIGen_ward C hward n hs0 hs1 hηp ω hσ b₁
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hB0 : 0 ≤ sz.Bctl n s := (st_Bctl_pos sz hs1).le
  have e1 := h1 (fun _ => true, fun _ => b₁)
  have e2 := h1 (fun _ => false, fun _ => b₁)
  refine hw.trans ?_
  have hsum : ‖C.L n s (fun _ : Fin 1 => true) (fun _ => b₁) ω - C.K n s (fun _ : Fin 1 => true) (fun _ => b₁)‖ +
      ‖C.L n s (fun _ : Fin 1 => false) (fun _ => b₁) ω - C.K n s (fun _ : Fin 1 => false) (fun _ => b₁)‖ ≤
      2 * (Θ * sz.Bctl n s) := by
    rw [pow_one] at e1 e2; linarith
  have hinv : (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n s))⁻¹ ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * ((1 - s) * κm)))⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith)
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n s))⁻¹ * (_ + _) ≤
        (2 * (((sz.W n : ℕ) : ℝ) ^ d * ((1 - s) * κm)))⁻¹ * (2 * (Θ * sz.Bctl n s)) :=
        mul_le_mul hinv hsum (by positivity) (by positivity)
    _ = _ := by field_simp

end Ward

/-! ## 3. Target 9: the `Prec` lift of the initial term of case (i) -/

section Concl

variable {d : ℕ}

set_option maxHeartbeats 4000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **The initial term of Step 5, case (i)** (`(iksjuwjx0)`, `3_5:2072-2172`; band `iniTermI_concl`, `IniTermI:3509`) over a carrier
tuple, from the hypotheses of `STIngR5gL` that it uses: `STDecaygL` at `s` (the profile of `𝓑`), `STAvgUgL` (the Ward term),
`lem;CLT` uniformly in `u` (`hCLT`, the conclusion `STCltFarUConclgL` spelled out), `(con_st_ind)` and the regime; the kernel facts
(target 1), the flow facts, the Ward class (one Ward text) and `STThPropsg` (X1a, from the class of target 5). -/
private theorem IniTermIGen_concl (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hF : Step5CasesGen_FlowFacts d Flow mk T0) (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d)
    {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (h𝔠d : 0 < 𝔠d) (h𝔠d' : 𝔠d ≤ 1 / 100) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) (hward : ZeroModeGen_WardCls sz (mk sz z)) (hTh : STThPropsg (mk sz z))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ T0 sz z n) (hR : STReg5I sz s t)
    (hDec : STDecaygL (mk sz z) (law sz) s) (hCon : sz.STConStInd 𝔠d s t) (hAvg : STAvgUgL (mk sz z) (law sz) s t)
    (hCLT : PrecL sz (law sz) (U := fun n => Σ u : TimeIcc s t n, sz.STCltFarIdx s n (u : ℝ))
      (fun n q ω => ‖STfFarg (mk sz z) n (s n) (q.1 : ℝ) q.2.1.1.1 q.2.1.2 ω‖)
      (fun n q _ => sz.STCltFarZeta n q.2.1.2)) :
    STIniTermConclgL (mk sz z) (law sz) ∅ STSigAll s t := by
  classical
  obtain ⟨κm, hκm0, hFl⟩ := hF κ hκ
  obtain ⟨⟨h𝔠, h𝔡, hSz, hBw, hWO⟩, hT1, hIm, hη⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT1 n)
  obtain ⟨C₆, C₈, Cs, c₀k, A, hC₆, hC₈, hCs, hc₀k, hA, HK⟩ := hKF hd κ 𝔡 hκ h𝔡
  obtain ⟨hUs, hdec, hR1, hE1, hG⟩ := HK sz ε 𝔠 z hflow
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨Cs', hCs', HsC⟩ := iniTermIGen_core_same d Flow mk gK hKF hd κ 𝔡 hκ h𝔡
  obtain ⟨Cl', hCl', HlC⟩ := iniTermIGen_core_lossy d Flow mk gK hKF hd κ 𝔡 hκ h𝔡
  obtain ⟨Cm', hCm', HmC⟩ := iniTermIGen_core_mixed d Flow mk gK hKF hd κ 𝔡 hκ h𝔡
  obtain ⟨CT, hCT, HconvC⟩ := IniTermIGen_theta_conv d hd
  obtain ⟨Cf, cf, hCf, hcf, hfarev⟩ := IniTermIGen_theta_far hTh
  obtain ⟨C₅, c₅, C₆', C₇, hC₅, hc₅, -, -, hevTh⟩ := hTh
  set CΘ : ℝ := C₆ * A + (A * 𝔡⁻¹ ^ 2 + 1) with hCΘ
  have hCΘ0 : 0 ≤ CΘ := by positivity
  set CR : ℝ := 1 + C₆ with hCR
  have hCR1 : 1 ≤ CR := by linarith
  set c₀ : ℝ := 1 + 2 ^ (d - 1) with hc₀
  have hc₀1 : 1 ≤ c₀ := by have : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
                           linarith
  set Cθ : ℝ := CΘ * c₀ with hCθ
  have hCθ0 : 0 ≤ Cθ := by positivity
  set Cv : ℝ := CΘ ^ 2 * CT with hCv
  have hCv0 : 0 ≤ Cv := by positivity
  set Kn : ℝ := 2 * (iniTermI_CW d + iniTermI_CB d) * iniTermI_CW d with hKn
  have hKn0 : 0 ≤ Kn := by
    have := iniTermI_CW_nonneg d; have := iniTermI_CB_nonneg d; rw [hKn]; positivity
  set Kmb : ℝ := Cm' + Kn * c₀ * Cθ ^ 2 + 2 * Cθ * c₀ * CR + Cv with hKmb
  have hKmb0 : 0 ≤ Kmb := by positivity
  set K₀ : ℝ := 2 * Cs' + 2 * Cl' + (2 * Cm' + 1) + (2 ^ d + Kmb * (4 + 2 * 2 ^ d + 4 / κm)) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set K₃ : ℝ := CR ^ 2 * (2 * Cf * (2 * c₀ + 1) + 2 * c₀ + 2) with hK₃
  have hK₃2 : 2 ≤ K₃ := by
    have h1 : 2 ≤ 2 * Cf * (2 * c₀ + 1) + 2 * c₀ + 2 := by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCf.le) (by linarith : (0 : ℝ) ≤ 2 * c₀ + 1)
      linarith
    have h2 : 1 ≤ CR ^ 2 := one_le_pow₀ hCR1
    nlinarith
  set c₂ : ℝ := min 1 (cf / 4) with hc₂
  have hc₂0 : 0 < c₂ := lt_min one_pos (by positivity)
  intro D hD
  apply iniTermI_prec_of_whp
  intro τ hτ
  set D₁ : ℝ := D + (7 + τ) / 𝔠 + 1 with hD₁
  have hD₁0 : 0 < D₁ := by positivity
  have hE1' := StochDomAt.highProb (hDec D₁ hD₁0) (τ := τ / 4) (by positivity)
  have hAvg' : PrecL sz (law sz) (U := fun n => (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
      (fun n p ω => ‖(mk sz z).L n (s n) p.1 p.2 ω - (mk sz z).K n (s n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (s n)) ^ 1) :=
    StochDomAt.precomp_param hAvg (fun n p => ((⟨s n, le_rfl, (hst n).le⟩ : TimeIcc s t n), p))
  have hE2' := StochDomAt.highProb hAvg' (τ := τ / 4) (by positivity)
  have hE3 := StochDomAt.highProb hCLT (τ := τ / 4) (by positivity)
  have hΞ := Gauss.HighProbAt.inter (tendsto_size sz hSz) (Gauss.HighProbAt.inter (tendsto_size sz hSz) hE1' hE2') hE3
  refine ⟨_, hΞ, ?_⟩
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ ∧ 1 ≤ STAI sz n := by
    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n h1 h2
    exact ⟨h2.1, h1.2, h2.2⟩
  have hfl := iniTermI_ev_floor sz (by omega : 1 ≤ d) (D := D) (c₂ := c₂) (K₃ := K₃) h𝔠 hτ hc₂0 (by linarith) hSz hBw
  have hKK := iniTermI_ev_K sz (by omega : 1 ≤ d) h𝔠 hτ K₀ hSz hBw
  filter_upwards [hlam, hBw, hCon, hfl, hKK, hfarev, hevTh] with n hl hBwn hCn hfln hKKn hfn hTn
  intro ω hω q
  obtain ⟨⟨h1, h2⟩, h3⟩ := hω
  obtain ⟨⟨u, hu⟩, ⟨σ, -⟩, x⟩ := q
  obtain ⟨hg, hgΛ, hA1⟩ := hl
  obtain ⟨hK, hlW2⟩ := hKKn
  obtain ⟨hgK, hgKΛ⟩ := CltFarUGen_guard (hR1 n) hg hgΛ
  change ‖zeroModeSet d (sz.L n) ∅ (Step2Gen_UN (mk sz z) n σ (s n) u
      (fun b => (mk sz z).L n (s n) σ b ω - (mk sz z).K n (s n) σ b)) x‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * ((STAI sz n) ^ (-(1 / 5) : ℝ) *
      STprof sz n u D ((sz.L n : ℕ) : ℝ) (x 0) (x 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
  rw [st5_zeroModeSet_empty]
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast sz.W_pos n
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast sz.one_le_size n
  have hs1 : s n < 1 := (hst n).trans (ht1 n)
  have hs1' : 0 < 1 - s n := by linarith
  have hu1 : 0 < 1 - u := by linarith [hu.2, ht1 n]
  have hregt := (hR n).1
  have hregs1 := (hR n).2
  have hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u := hregt.trans (by linarith [hu.2])
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s n :=
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_right₀ hL1 (by omega : 2 ≤ d))).trans
      (hregt.trans (by linarith [hst n, ht1 n]))
  set Θ : ℝ := N ^ (τ / 4) with hΘ
  have hΘ1 : 1 ≤ Θ := Real.one_le_rpow hN1 (by positivity)
  have hΘ0 : 0 ≤ Θ := by linarith
  have hΘ4 : Θ ^ 4 = N ^ τ := by
    rw [hΘ, show (N ^ (τ / 4)) ^ 4 = (N ^ (τ / 4)) ^ ((4 : ℕ) : ℝ) from (Real.rpow_natCast _ 4).symm,
      ← Real.rpow_mul (by linarith)]
    norm_num
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  set a : ℝ := (STAI sz n) ^ (-(1 / 5 : ℝ)) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hA0.le _
  have hlam2 := iniTermI_lam_le sz n hg hs1 hlow
  have hBs0 : 0 ≤ sz.Bctl n (s n) := (st_Bctl_pos sz hs1).le
  have hNW : N ≤ W ^ (1 / 𝔠) := iniTermI_N_le_W sz n h𝔠 hBwn
  have hβ : 0 ≤ 1 / 𝔠 := by positivity
  have hD1D : D ≤ D₁ := by
    have : 0 ≤ (7 + τ) / 𝔠 := by positivity
    rw [hD₁]; linarith
  have hF : W ^ (-D₁) ≤ W ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW1 (neg_le_neg hD1D)
  set ρ : ℝ := (1 - s n) / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hs1'.le hu1.le
  have hρL : ρ ≤ ((sz.L n : ℕ) : ℝ) ^ 2 := by
    rw [hρ, div_le_iff₀ hu1]
    have : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - u) := by
      rw [div_le_iff₀ (by positivity)] at hreg; linarith
    linarith
  have hρN : ρ ≤ N := hρL.trans (iniTermI_L2_le_N sz (by omega) n)
  have hexp1 : ((1 : ℕ) : ℝ) * (1 / 𝔠) + D ≤ D₁ := by
    have : 1 / 𝔠 ≤ (7 + τ) / 𝔠 := div_le_div_of_nonneg_right (by linarith) h𝔠.le
    rw [hD₁]; push_cast; linarith
  have hexp2 : ((2 : ℕ) : ℝ) * (1 / 𝔠) + D ≤ D₁ := by
    have : 2 * (1 / 𝔠) ≤ (7 + τ) / 𝔠 := by
      rw [← mul_div_assoc, mul_one]; exact div_le_div_of_nonneg_right (by linarith) h𝔠.le
    rw [hD₁]; push_cast; linarith
  have hρF1 : ρ * W ^ (-D₁) ≤ W ^ (-D) := by
    have := iniTermI_pow_floor hW1 (by linarith) hNW 1 hβ hexp1
    calc ρ * W ^ (-D₁) ≤ N * W ^ (-D₁) := mul_le_mul_of_nonneg_right hρN (Real.rpow_nonneg (by linarith) _)
      _ = N ^ 1 * W ^ (-D₁) := by rw [pow_one]
      _ ≤ _ := this
  have hρF2 : ρ * ρ * W ^ (-D₁) ≤ W ^ (-D) := by
    have := iniTermI_pow_floor hW1 (by linarith) hNW 2 hβ hexp2
    calc ρ * ρ * W ^ (-D₁) ≤ N ^ 2 * W ^ (-D₁) :=
          mul_le_mul_of_nonneg_right ((mul_self_le_mul_self hρ0 hρN).trans (le_of_eq (sq N).symm))
            (Real.rpow_nonneg (by linarith) _)
      _ ≤ _ := this
  have hρB := iniTermI_rho_B sz n hg hA1 hu.1 hu.2 (ht1 n) hregt hregs1 (by omega) h𝔠d h𝔠d' hCn.1
  have hX : ∀ b : Fin 2 → Zd d (sz.L n), ‖(mk sz z).L n (s n) σ b ω - (mk sz z).K n (s n) σ b‖ ≤
      Θ * (sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) (s n) (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
        W ^ (-D₁)) := by
    intro b
    have := h1 (σ, b)
    dsimp only at this
    rw [iniTermI_prem_eq] at this
    exact this
  have hP₀ := iniTermI_prof_ge sz n u D x
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1' : u < 1 := hu.2.trans_lt (ht1 n)
  have hW0 : 0 < W := by linarith
  have hlW0 : 0 ≤ Real.log W := by linarith
  have hlam0 : 0 ≤ sz.Bctl n (s n) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hBs0 _
  have hlW1' : 1 ≤ Real.log W := by linarith
  -- common quantities
  have hWd0 : (0 : ℝ) < W ^ d := by positivity
  have hAeq : STAI sz n = sz.lam n ^ 2 * W ^ d := rfl
  have hGinv : (sz.lam n ^ 2)⁻¹ ≤ W ^ d := by
    have hg2 : 0 < sz.lam n ^ 2 := by positivity
    calc (sz.lam n ^ 2)⁻¹ = (sz.lam n ^ 2)⁻¹ * 1 := by rw [mul_one]
      _ ≤ (sz.lam n ^ 2)⁻¹ * (sz.lam n ^ 2 * W ^ d) := mul_le_mul_of_nonneg_left (hAeq ▸ hA1) (inv_nonneg.2 hg2.le)
      _ = _ := by field_simp
  have hWN : W ^ d ≤ N := by
    have : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    rw [hNdef, hWdef]; unfold Sizes.size; exact_mod_cast this
  have hG : (sz.lam n ^ 2)⁻¹ ≤ N := hGinv.trans hWN
  have hU : (1 - u)⁻¹ ≤ N ^ 2 := iniTermI_oneSub_inv_le sz (by omega) n hA1 hg hreg
  have hQeq : sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ =
      sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (STAI sz n)⁻¹ := by
    rw [hAeq, mul_inv]; ring
  have hQ : sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ ≤ 2 := by
    rw [hQeq]
    have : (STAI sz n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA1
    have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by norm_num)
    calc _ ≤ (2 * a) * 1 := mul_le_mul hlam2 this (inv_nonneg.2 hA0.le) (by positivity)
      _ ≤ 2 := by linarith
  have hQ0 : 0 ≤ sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ := by positivity
  have hcard : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ N := by
    rw [iniTermI_card_Zd]
    have : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    rw [hNdef]; unfold Sizes.size; exact_mod_cast this
  have hF₁0 : 0 ≤ W ^ (-D₁) := Real.rpow_nonneg (by linarith) _
  -- the propagator at `u`
  have hdecΘ : ∀ x y : Zd d (sz.L n), ‖STThg (mk sz z) n (σ 0) (σ 1) u x y‖ ≤
      CΘ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (y - x) : ℕ) := fun x y =>
    IniTermIGen_Th_decay (mk sz z) (gK sz z) n (hUs n) hC₆.le hA hdec (hR1 n) hgK hgKΛ (σ 0) (σ 1) hu0 hu1' x y
  have hTm : ∀ x y : Zd d (sz.L n), ‖STThg (mk sz z) n (σ 0) (σ 1) u x y‖ ≤ CR * (1 - u)⁻¹ := fun x y =>
    CltFarUGen_Th_entry (mk sz z) n (hUs n) (σ 0) (σ 1) hu0 hu1'
      (fun a' => (hdec n hgK hgKΛ (σ 0) (σ 1) u hu0 hu1').2 a') x y
  have hT1' : ∀ x y : Zd d (sz.L n), ‖STThg (mk sz z) n (σ 0) (σ 1) u x y‖ ≤
      (Cθ * (sz.lam n ^ 2)⁻¹) * iniTermI_PI d (sz.L n) (x - y) := fun x y =>
    IniTermIGen_theta_pi hd (sz.three_le_L n) hg hu1' hreg hCΘ0 hdecΘ x y
  have hv : ∀ a₀ a₁ : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖STThg (mk sz z) n (σ 0) (σ 1) u a₀ b‖ *
      ‖STThg (mk sz z) n (σ 0) (σ 1) u b a₁‖ ≤
      Cv * (1 - u)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₀ - a₁) : ℕ) := fun a₀ a₁ =>
    HconvC (sz.L n) (sz.three_le_L n) hg hu0 hu1' hreg hCΘ0 (STThg (mk sz z) n (σ 0) (σ 1) u) hdecΘ a₀ a₁
  have hK' : K₀ * (Real.log W ^ 14 * Real.exp (Real.log W ^ (3 / 4 : ℝ))) ≤ Θ ^ 3 := hK
  set lam₀ : ℝ := sz.Bctl n (s n) ^ (1 / 5 : ℝ) with hlam₀
  set lW : ℝ := Real.log W with hlWdef
  set ℓu : ℝ := ellT (sz.L n) (sz.lam n) u with hℓudef
  set ℓs : ℝ := ellT (sz.L n) (sz.lam n) (s n) with hℓsdef
  set X : (Fin 2 → Zd d (sz.L n)) → ℂ := fun b => (mk sz z).L n (s n) σ b ω - (mk sz z).K n (s n) σ b with hXdef
  set Pfar : Zd d (sz.L n) → Prop := fun b₁ => lW ^ 4 * ℓs < ((zdistInf d (sz.L n) (b₁ - x 0) : ℕ) : ℝ) ∧
    lW ^ 4 * ℓs < ((zdistInf d (sz.L n) (b₁ - x 1) : ℕ) : ℝ) with hPfar
  set Fn : ℝ := ‖CltFarUGen_fSum (STThg (mk sz z) n (σ 0) (σ 1) u) (s n) X x Pfar‖ with hFn
  set T3e : ℝ := Θ * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * (sz.lam n ^ 2)⁻¹ * (1 - u)⁻¹ *
    (W ^ (-D₁) + lam₀ * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ * Real.exp (-Real.sqrt (lW ^ 3))) with hT3e
  set Taile : ℝ := CR ^ 2 * ((Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
    (2 * Cf * Real.exp (-(cf * (1 / 4 * lW ^ (3 / 2 : ℝ) * ℓu) / ℓu)) *
        (Θ * (lam₀ * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * (sz.lam n ^ 2)⁻¹) + W ^ (-D₁))) +
      Θ * (lam₀ * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * ((sz.lam n ^ 2)⁻¹ *
        Real.exp (-Real.sqrt (lW ^ (5 / 2 : ℝ) * ℓs / ℓs)))) + W ^ (-D₁)))) with hTaile
  have hsameU : σ 0 = σ 1 → ‖Step2Gen_UN (mk sz z) n σ (s n) u X x‖ ≤ Cs' * Θ *
      (lam₀ * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x 0 - x 1) : ℕ) + W ^ (-D₁)) := fun hσ =>
    HsC sz ε 𝔠 z hflow n hgK hgKΛ W D₁ (s n) u Θ lam₀ hW0 (hs0 n) hu.1 hu1' hreg hΘ0 hlam0 σ hσ X hX x
  have hlossyU : σ 0 ≠ σ 1 → ‖Step2Gen_UN (mk sz z) n σ (s n) u X x‖ ≤ Cl' * Θ * ((1 - s n) / (1 - u) *
      (lam₀ * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x 0 - x 1) : ℕ) +
        (1 - s n) / (1 - u) * W ^ (-D₁))) := fun hσ' =>
    HlC sz ε 𝔠 z hflow n hgK hgKΛ W D₁ (s n) u Θ lam₀ hW0 (hs0 n) hu.1 hu1' hreg hΘ0 hlam0 σ hσ' X hX x
  have hmbU : σ 0 ≠ σ 1 → (∀ b₁ : Zd d (sz.L n), ‖∑ b₂ : Zd d (sz.L n), X ![b₁, b₂]‖ ≤
      Θ * (sz.Bctl n (s n) * (W ^ d)⁻¹ / κm) / (1 - s n)) →
      ‖Step2Gen_UN (mk sz z) n σ (s n) u X x‖ ≤ Fn + Kmb * (Θ * (lam₀ * (W ^ d)⁻¹ *
        tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x 0 - x 1) : ℕ) + (1 - s n) / (1 - u) * W ^ (-D₁)) +
        Θ * (lam₀ * (W ^ d)⁻¹) * (sz.lam n ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d (sz.L n) (x 0 - x 1) + T3e +
        (1 - s n) / (1 - u) * (Θ * (sz.Bctl n (s n) * (W ^ d)⁻¹ / κm)) *
          tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x 0 - x 1) : ℕ)) := fun hσ' hXY => by
    obtain ⟨hshift, hsymm, -, -⟩ := hTn u hu0 hu1' σ hσ'
    obtain ⟨c, hc0, hc1, hcore⟩ := HmC sz ε 𝔠 z hflow n hgK hgKΛ W D₁ (s n) u Θ lam₀ hW0 (hs0 n) hu.1 hu1' hreg hΘ0 hlam0
      σ hσ' X hX
    have hY : 0 ≤ Θ * (sz.Bctl n (s n) * (W ^ d)⁻¹ / κm) := by positivity
    exact IniTermIGen_mixed_bound hd (sz.three_le_L n) (STThg (mk sz z) n (σ 0) (σ 1) u) hg hW0 (hs0 n) hu.1 hu1' hreg
      hregs1 hΘ0 hlam0 (by linarith) hY hCm'.le hCθ0 hCv0 hCR1 (le_refl _) hsymm hT1' hTm hv X hX hXY x Pfar
      (fun b₁ => Iff.rfl) hc0 hc1 (hcore x)
  have htailU : σ 0 ≠ σ 1 → (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ℓu + lW ^ (5 / 2 : ℝ) * ℓs <
        ((zdistInf d (sz.L n) (x 0 - x 1) : ℕ) : ℝ) →
      ‖Step2Gen_UN (mk sz z) n σ (s n) u X x‖ ≤ Cm' * Θ * (lam₀ * (W ^ d)⁻¹ *
        tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x 0 - x 1) : ℕ) + (1 - s n) / (1 - u) * W ^ (-D₁)) + Taile :=
      fun hσ' hwin => by
    obtain ⟨c, hc0, hc1, hcore⟩ := HmC sz ε 𝔠 z hflow n hgK hgKΛ W D₁ (s n) u Θ lam₀ hW0 (hs0 n) hu.1 hu1' hreg hΘ0 hlam0
      σ hσ' X hX
    have hTd := hfn u hu0 hu1' σ hσ'
    exact IniTermIGen_mixed_tail hd (sz.three_le_L n) (STThg (mk sz z) n (σ 0) (σ 1) u) (r₁ := 1 / 4 * lW ^ (3 / 2 : ℝ) * ℓu)
      (Yw := lW ^ (5 / 2 : ℝ) * ℓs) hg hW0 (hs0 n) hu.1 hu1' hreg hΘ0 hlam0 hCf.le hCR1 hTm
      (fun x' y' hxy => hTd x' y' _ hxy) X hX x (by linarith) hc0 hc1 (hcore x)
  have hℓs1 : 1 ≤ ℓs := one_le_ellT hL1
  have hℓu0 : 0 < ℓu := lt_of_lt_of_le one_pos (hℓs1.trans (ellT_mono hg.le hu.1 hu1'))
  have hℓs0 : 0 < ℓs := lt_of_lt_of_le one_pos hℓs1
  obtain ⟨hE₃, he₁, he₂⟩ := iniTermI_Estar (lW := lW) (c := cf) (c₂ := c₂) hlW1' hc₂0.le (min_le_left _ _)
    (min_le_right _ _) hℓu0 hℓs0
  have hin : σ 0 ≠ σ 1 → lW ^ 10 < (1 - s n) / (1 - u) →
      ((zdistInf d (sz.L n) (x 0 - x 1) : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ℓu + lW ^ (5 / 2 : ℝ) * ℓs →
        (∀ b₁ : Zd d (sz.L n), ‖∑ b₂ : Zd d (sz.L n), X ![b₁, b₂]‖ ≤ Θ * (sz.Bctl n (s n) * (W ^ d)⁻¹ / κm) / (1 - s n)) ∧
          T3e ≤ W ^ (-D) ∧ Fn ≤ Θ * (a * ((sz.lam n ^ 2 * W ^ d)⁻¹ *
            ((((zdistInf d (sz.L n) (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹))) := by
    intro hσ' hρbig hwin
    have hℓ5 : lW ^ 5 * ℓs ≤ ℓu := iniTermI_ell5 (sz.three_le_L n) hg hu.1 hu1' hreg hregs1 hlW0 hρbig
    refine ⟨fun b₁ => IniTermIGen_ward_bound (mk sz z) hward n (hs0 n) hs1 hκm0 (hη n (s n)) (hIm n) ω hσ' hΘ0
      (fun p => h2 p) b₁, ?_, ?_⟩
    · exact (iniTermI_floor_T3 (Nat.cast_nonneg _) hcard (by positivity) hG (inv_nonneg.2 hu1.le) hU hQ0 hQ hΘ0 hN1 hF₁0
        (Real.exp_pos _).le hE₃ hK₃2).trans hfln
    · have hcond : lW ^ 5 * ℓs ≤ ℓu ∧ ((zdistInf d (sz.L n) (x 0 - x 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ℓu + lW ^ (5 / 2 : ℝ) * ℓs := ⟨hℓ5, hwin⟩
      have hq : Fn ≤ Θ * sz.STCltFarZeta n x := h3 ⟨⟨u, hu⟩, ⟨(⟨σ, hσ'⟩, x), hcond⟩⟩
      have hζ : sz.STCltFarZeta n x = a * ((sz.lam n ^ 2 * W ^ d)⁻¹ *
          ((((zdistInf d (sz.L n) (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹)) := by
        unfold Sizes.STCltFarZeta
        have e : (STAI sz n) ^ (-(6 / 5) : ℝ) = a * (STAI sz n)⁻¹ := by
          rw [show (-(6 / 5) : ℝ) = -(1 / 5) + (-1) by norm_num, Real.rpow_add hA0, Real.rpow_neg_one]
        rw [e, hAeq, div_eq_mul_inv]; ring
      rw [hζ] at hq
      exact hq
  have hout : σ 0 ≠ σ 1 → lW ^ 10 < (1 - s n) / (1 - u) →
      (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ℓu + lW ^ (5 / 2 : ℝ) * ℓs < ((zdistInf d (sz.L n) (x 0 - x 1) : ℕ) : ℝ) →
        Taile ≤ W ^ (-D) := by
    intro hσ' hρbig hwin
    have hfin := iniTermI_floor_tail (Nd := (Fintype.card (Zd d (sz.L n)) : ℝ)) (N := N) (U := (1 - u)⁻¹)
      (Q := lam₀ * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹) (Θ := Θ) (F₁ := W ^ (-D₁))
      (e₁ := Real.exp (-(cf * (1 / 4 * lW ^ (3 / 2 : ℝ) * ℓu) / ℓu)))
      (e₂ := Real.exp (-Real.sqrt (lW ^ (5 / 2 : ℝ) * ℓs / ℓs))) (Es := Real.exp (-(c₂ * lW ^ (5 / 4 : ℝ))))
      (C := Cf) (c₀ := c₀) (K₃ := 2 * Cf * (2 * c₀ + 1) + 2 * c₀ + 2)
      (Nat.cast_nonneg _) hcard (inv_nonneg.2 hu1.le) hU hQ0 hQ hΘ0 hN1 hF₁0
      (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le he₁ he₂ hCf.le hc₀1
      le_rfl
    calc Taile = CR ^ 2 * ((Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
          (2 * Cf * Real.exp (-(cf * (1 / 4 * lW ^ (3 / 2 : ℝ) * ℓu) / ℓu)) *
              (Θ * (c₀ * (lam₀ * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹) + W ^ (-D₁))) +
            Θ * (c₀ * (lam₀ * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹) * Real.exp (-Real.sqrt (lW ^ (5 / 2 : ℝ) * ℓs / ℓs)) +
              W ^ (-D₁)))) := by rw [hTaile]; ring
      _ ≤ CR ^ 2 * (Θ * N ^ 6 * (2 * Cf * (2 * c₀ + 1) + 2 * c₀ + 2) * (Real.exp (-(c₂ * lW ^ (5 / 4 : ℝ))) + W ^ (-D₁))) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = Θ * N ^ 6 * K₃ * (Real.exp (-(c₂ * lW ^ (5 / 4 : ℝ))) + W ^ (-D₁)) := by rw [hK₃]; ring
      _ ≤ W ^ (-D) := hfln
  refine le_of_le_of_eq (IniTermIGen_rl_all hd (sz.three_le_L n) X hg hW0 hκm0 (hs0 n) hu.1 hu1' hreg hregs1 hlW2 hΘ1 hlam0
    hlam2 ha0 hBs0 hCs'.le hCl'.le hCm'.le hKmb0 hF hρF1 hρF2 hρB hK' hP₀ hsameU hlossyU hmbU htailU hin hout) (by rw [hΘ4])

end Concl

/-! ## 4. Target 9: the pin `stIniTermIgL_of` -/

/-- **Target 9, the pin `stIniTermIgL_of`** (`T2484_IniTermIOf`; band `stIniTermI_holds`, `IniTermI:3715`): the initial term of case (i)
over a carrier tuple, for every law that is a probability measure.  The `u`-uniform `lem;CLT` is `stCltFarUgL_of` (target 7) from the
flow facts, the kernel facts and the class of target 5; the Ward step reads the one Ward text `ZeroModeGen_WardCls` for each flow
member; `STThPropsg` is a field of the class of target 5. -/
theorem stIniTermIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) →
    Step5CasesGen_FlowFacts d Flow mk T0 → IniTermGen_KerFacts d Flow mk gK →
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (mk sz z)) →
    IniTermGen_CltFlow d law Flow mk T0 → STIniTermIgL d law Flow mk T0 := by
  intro hP hF hKF hW hFlow hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d, h𝔠d', H⟩ := stCltFarUgL_of d law Flow mk T0 gK hP hF hKF hFlow hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d, h𝔠d', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hCon hS1 hS2 hLmax hLKU
  have hCLT := H 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hCon hS1 hS2 hLmax hLKU
  obtain ⟨κ', δ, -, -, -, H5⟩ := hFlow hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨H₀, g', E, -, -, -, -, hTh, -, -⟩ := H5 𝔠 sz z hflow
  exact IniTermIGen_concl d law Flow mk T0 gK hF hKF hd hκ h𝔠d h𝔠d' sz hflow (hW sz κ ε 𝔠 𝔡 z hκ hflow) hTh hs0 hst ht hR
    hDec hCon hS2.2.1 hCLT

/-! ## 5. Band re-derivation and compiled nonempty instances (target 10; `d = 3`, `szB`, `zB`) -/

/-- **Target 9 at the band** (re-derivation of `stIniTermI_holds`, `IniTermI:3715`): the generic pin at the band tuple
`(seqP, STFlow, bandFM ∘ STflowE, lemT)`, `gK = sz.lam`, through `STIniTermI_iff_gL`; the Ward class is `zeroModeGen_wardCls_band`
(`|E n| < 2` from `Im z_n > 0`). -/
theorem iniTermIGen_band_holds (d : ℕ) : STIniTermI d :=
  (STIniTermI_iff_gL d).2 (stIniTermIgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz _ => sz.lam) (fun sz => inferInstance)
    (step5CasesGen_flowFacts_band d) (iniTermGen_kerFacts_band d)
    (fun sz κ ε 𝔠 𝔡 z _ hflow => zeroModeGen_wardCls_band sz (STflowE z) fun n => abs_lemE_lt_two
      (lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hflow.2 n).2.1))
    (iniTermGen_cltFlow_band d))

section Inst

open RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst

/-- **Target 9 at the band, instantiated**: the generic pin `stIniTermIgL_of`, applied to the band tuple, gives the instance of
`Step5Pins` at `(szB, zB, 7/8, 15/16)` for every `Cd > 0` (as `inst_iniTermI_proved`, `IniTermI:3819`): the five hypotheses of the
pin are discharged by the band results (`step5CasesGen_flowFacts_band`, `iniTermGen_kerFacts_band`, `zeroModeGen_wardCls_band`,
`iniTermGen_cltFlow_band`, `isProbabilityMeasure_seqP`); the stochastic premises of Steps 1-4 are the premises of the instance. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_iniTermI ((STIniTermI_iff_gL 3).2 (stIniTermIgL_of 3 (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
    (fun sz _ => sz.lam) (fun sz => inferInstance) (step5CasesGen_flowFacts_band 3) (iniTermGen_kerFacts_band 3)
    (fun sz κ ε 𝔠 𝔡 z _ hflow => zeroModeGen_wardCls_band sz (STflowE z) fun n => abs_lemE_lt_two
      (lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hflow.2 n).2.1))
    (iniTermGen_cltFlow_band 3))) Cd hCd

/-- **Target 9, band re-derivation, instantiated**: `iniTermIGen_band_holds` gives the instance of `Step5Pins` at
`(szB, zB, 7/8, 15/16)` with the pin proved. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_iniTermI (iniTermIGen_band_holds 3) Cd hCd

/-- **Target 9 applied at `(szB, zB, 7/8, 15/16)`**: the pin `stIniTermIgL_of` at the band tuple, as the previous example. -/
example (Cd : ℝ) (hCd : 0 < Cd)
    (hKb : STKboundgL (bandFM szB (STflowE zB)) (Sizes.seqP szB)) (hKw : STKwardgL (bandFM szB (STflowE zB)) (Sizes.seqP szB))
    (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hDec : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hDecS : STDecayStronggL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hS1 : STStep1LoopgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hS2 : STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd)
    (hLmax : STLmaxUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hLKU : STLKUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      STIniTermConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigAll (fun _ => 7 / 8) (fun _ => 15 / 16) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := stIniTermIgL_of 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz _ => sz.lam) (fun sz => inferInstance)
    (step5CasesGen_flowFacts_band 3) (iniTermGen_kerFacts_band 3)
    (fun sz κ ε 𝔠 𝔡 z _ hflow => zeroModeGen_wardCls_band sz (STflowE z) fun n => abs_lemE_lt_two
      (lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hflow.2 n).2.1))
    (iniTermGen_cltFlow_band 3) le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, H (1 / 6) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5I hKb hKw hLK hDec hDecS
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h0) hS1 hS2 hLmax hLKU⟩

end Inst

end RBM.BA

end
