/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.Prop6Path
import RBM3D.BA.CombesThomas
import RBM3D.BA.GreenSchur
import RBM3D.BA.EMn2BA

/-!
# T2429 probe step (DECISIONS §238): the pin T.1 (iii) `BATwKDecay` and its compiled instance

Probe of `docs/tickets/T2429.md`; never merged, no root import.  Section 1: `#check` of the four inputs named by the
ticket, three merged twins of `BA/EMn2BA.lean`, the instance data (all on `main`).  Section 2: the new public pin of T.1 (iii) (`docs/tickets/T2398-TL-proofs.md:37-38`,
the twisted analogue of the fast-decay property `Def_decay`, `paper/tex/3_5_Loop_Hierarchy.tex:1115-1120`; design
`docs/reports/T2413-design.md` F6).  Section 3: its instance as an `example` at the flow datum `sz0`, `zSeq`,
`flow_sz0`: every deterministic hypothesis is discharged and the cut-off region is nonempty for every `n`.
No theorem, no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Inputs (`#check`): the four named by the ticket, the merged twins found (`BA/EMn2BA.lean`), the instance data -/

#check @twK_ba
#check @baProp5_holds
#check @BAMB_decay_large
#check @BAflow_lam0_window
#check @EMn2BA_ellT_mono_g
#check @EMn2BA_one_sub_T0
#check @baComp_holds
#check @zdistInf_le_zdistD
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## 2. The pin -/

/-- **T.1 (iii)** (`TP:37-38`; paper `Def_decay`, `3_5:1115-1120`): the twisted tree `K̃_{σ,(a;c₁,c₂)}` (`twK` at the carrier
`baFMz sz z`; its kernels are at the flow coupling `g₀ = BAflowLam0 sz z n = √t₀ · sz.lam n`) is `≤ W^{-D}` when
`|a - c₁| ≥ W^{ε₁} ℓ_v`, for every `ε₁, D > 0` and every large `n`, uniformly in `v ∈ [0, t₀]`, `σ`, `a`, `c₁`, `c₂`.
The cut is at the model scale `ellT (sz.L n) (sz.lam n) v` and in `zdistInf`, exactly as `twDec` (T.11 (v)); the step to the
kernel's own scale is `ℓ_v(g₀) ≤ ℓ_v(lam)` (`EMn2BA_ellT_mono_g`).  The constants of the proof (Property 5, `BAMB_decay_large`)
and the polynomial size of `B_{v,0}` are absorbed by `e^{-c W^{ε₁}}` for `n` large (`W_n → ∞`). -/
def BATwKDecay (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ ε₁ D : ℝ, 0 < ε₁ → 0 < D →
      ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ BAflowT0 sz z n → ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
        ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ) →
        ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

#print axioms BATwKDecay

/-! ## 3. The instance: `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`), `zSeq`, `flow_sz0`
(`(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`), `ε₁ = 1/10`, `D = 2`.  For every `n` and every `v ∈ [0, 1/2]` (`1/2 < t₀`, `half_lt_t0`)
the pair `a = (2(n+1), 0, 0)`, `c₁ = 0` lies in the cut-off region: `|a - c₁|_∞ ≥ 2(n+1) ≥ W_n^{1/10} = ((2(n+1))^5)^{1/10}` and
`ℓ_v(lam_n) ≤ 1`.  The pin is applied to it for large `n`, every charge `σ` and every `c₂`. -/

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst in
example (h : BATwKDecay 3) : ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 2 → ∃ a c₁ : Zd 3 (sz0.L n),
    ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ellT (sz0.L n) (sz0.lam n) v ≤ (zdistInf 3 (sz0.L n) (a - c₁) : ℝ) ∧
    ∀ (σ : Fin 2 → Bool) (c₂ : Zd 3 (sz0.L n)),
      ‖twK (baFMz sz0 zSeq) n v σ a c₁ c₂‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (-2 : ℝ) := by
  filter_upwards [h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (1 / 10) 2 (by norm_num) (by norm_num)] with n hn
  intro v hv0 hv1
  have hy1 : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- `zdistInf (a - 0) ≥ 2(n+1)` for `a = (2(n+1), 0, 0)` in `Z_{4(n+1)}^3`
  have h1 : 2 * (n + 1) ≤ zdistInf 3 (sz0.L n) (![((2 * (n + 1) : ℕ) : ZMod (sz0.L n)), 0, 0] - 0) := by
    have h := Finset.le_sup (f := fun j => zdist (sz0.L n)
      ((![((2 * (n + 1) : ℕ) : ZMod (sz0.L n)), 0, 0] - 0 : Zd 3 (sz0.L n)) j)) (Finset.mem_univ (0 : Fin 3))
    refine le_trans ?_ h
    have hL : sz0.L n = 4 * (n + 1) := rfl
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, Matrix.cons_val_zero, zdist, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (by rw [hL]; omega)]
    rw [hL]; omega
  have h1' : (2 * ((n : ℝ) + 1)) ≤ (zdistInf 3 (sz0.L n) (![((2 * (n + 1) : ℕ) : ZMod (sz0.L n)), 0, 0] - 0) : ℝ) := by
    exact_mod_cast h1
  -- `ℓ_v(lam_n) ≤ 1` for `v ≤ 1/2`: `lam_n ≤ 1/64`, `√|1 - v| ≥ 1/2`
  have hell : ellT (sz0.L n) (sz0.lam n) v ≤ 1 := by
    refine (min_le_left _ _).trans (max_le ?_ le_rfl)
    have hs : (1 / 2 : ℝ) ≤ Real.sqrt |1 - v| := by
      rw [Real.le_sqrt (by norm_num) (abs_nonneg _), abs_of_nonneg (by linarith)]
      linarith
    have hlam : sz0.lam n ≤ 1 / 2 := by
      have e : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
      rw [e]
      have h6 : (2 : ℝ) ^ 6 ≤ (2 * ((n : ℝ) + 1)) ^ 6 := pow_le_pow_left₀ (by norm_num) hy1 6
      calc ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ ((2 : ℝ) ^ 6)⁻¹ := inv_anti₀ (by norm_num) h6
        _ ≤ 1 / 2 := by norm_num
    rw [div_le_one (by linarith)]
    linarith
  -- `W_n^{1/10} = ((2(n+1))^5)^{1/10} ≤ 2(n+1)`
  have hW : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have hWn : ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [sz0]
    rw [hWn]
    calc ((2 * ((n : ℝ) + 1)) ^ 5) ^ (1 / 10 : ℝ) = (2 * ((n : ℝ) + 1)) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ (2 * ((n : ℝ) + 1)) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = _ := Real.rpow_one _
  have hWpos : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcut : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ellT (sz0.L n) (sz0.lam n) v ≤
      (zdistInf 3 (sz0.L n) (![((2 * (n + 1) : ℕ) : ZMod (sz0.L n)), 0, 0] - 0) : ℝ) :=
    calc _ ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * 1 := mul_le_mul_of_nonneg_left hell hWpos
      _ ≤ _ := by rw [mul_one]; exact hW.trans h1'
  exact ⟨_, 0, hcut, fun σ c₂ => hn v hv0 (hv1.trans (half_lt_t0 n).le) σ _ 0 c₂ hcut⟩

end RBM.BA

end
