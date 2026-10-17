/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Prop5Short
import RBM3D.BA.Prop6Path
import RBM3D.BA.Ward
import RBM3D.BA.GreenSchur
import RBM3D.BA.CombesThomas

/-!
# The BA stability bound and the `M`, `Θ` row facts

Deterministic inputs of the coupled bound `GreenCore_coupled` and of the off-diagonal decay `BA/GreenOff.lean`; paper:
Lemma 8.3 (`lem:propM`) with (8.5) `eq:WardM`, (8.6) `Mbound_AO`, (8.7) `Mbound_AO2`, and Subappendix A.1 (`sec:pf_propTH`).

* Section 1: `baStab_of_real`, the body of the `BAStab` statement of `BA/GreenCore.lean` with `K = 16 κ⁻⁴`:
  if `|v_a - t Σ_b M^{(++)}_{ab} v_b| ≤ B` for all `a` then `|v_a| ≤ 16 κ⁻⁴ B`, at `BAReal` data, `0 ≤ t ≤ 1`
  (no `g`, no `Λ`, no `L`).  `BAStab` itself is not defined here.
* Section 2: the row facts of `M`: `ρ` (`ℓ¹` column), `ρ₂ ≤ 1`, the weighted row `ρ̂ ≤ c₀⁻¹ S_{c₀/2}`
  (block and fine lattice).
* Section 3: the weighted `ℓ¹` row bound of `Θ_t` with `C_Θ̂ = C₅ (1 + Λ² S_{2μ/3})`; the translation
  invariance of `Θ` is `baP8_BATheta_shift` (`BA/Prop6Path.lean`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The stability bound `K = 16 κ⁻⁴` -/

/-- **The stability bound** at the real axis: if `|v_a - t Σ_b M^{(++)}_{ab} v_b| ≤ B` for all `a` then `|v_a| ≤ 16 κ⁻⁴ B`.
The body of `BAStab d L g E m t (16 κ⁻⁴)`.  Proof at a maximiser `a₀` of `|v|`: `M^{(++)}_{a₀a₀} = m²`
(`BAMss_ss_diag`), `Σ_{b≠a₀} |M^{(++)}_{a₀b}| = 1 - |m|²` (`BAMss_row_offdiag_sum`) and
`ε ≤ |1 - t m²|`, `1 - |m|² ≤ (1 - ε)|1 - t m²|` (`BAoffDiag_scalar`, `ε = κ²/4`). -/
theorem baStab_of_real (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ (v : Zd d L → ℂ) (B : ℝ),
      (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) →
        ∀ a, ‖v a‖ ≤ 16 * κ⁻¹ ^ 4 * B := by
  intro v B hB a
  have hn : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  obtain ⟨hD1, hD2⟩ := BAoffDiag_scalar κ t m hκ hr.2 hn ht0 ht1
  obtain ⟨a0, ha0⟩ := Finite.exists_max (fun a : Zd d L => ‖v a‖)
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) true true with hQ
  set D : ℝ := ‖1 - (t : ℂ) * m ^ 2‖ with hD
  set V : ℝ := ‖v a0‖ with hV
  have hV0 : 0 ≤ V := norm_nonneg _
  have hdiag : Q a0 a0 = m ^ 2 := by
    have := BAMss_ss_diag d L g (E : ℂ) m hr.1 true a0
    simpa using this
  have hoff : ∑ b ∈ Finset.univ.erase a0, ‖Q a0 b‖ = 1 - ‖m‖ ^ 2 :=
    BAMss_row_offdiag_sum d L g E m hr.1 true a0
  have hsplit : ∑ b, Q a0 b * v b
      = Q a0 a0 * v a0 + ∑ b ∈ Finset.univ.erase a0, Q a0 b * v b :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ a0)).symm
  have hid : (1 - (t : ℂ) * m ^ 2) * v a0
      = (v a0 - (t : ℂ) * ∑ b, Q a0 b * v b)
        + (t : ℂ) * ∑ b ∈ Finset.univ.erase a0, Q a0 b * v b := by
    rw [hsplit, hdiag]; ring
  have h1 : D * V ≤ B + t * ((1 - ‖m‖ ^ 2) * V) := by
    calc D * V = ‖(1 - (t : ℂ) * m ^ 2) * v a0‖ := (norm_mul _ _).symm
      _ = ‖(v a0 - (t : ℂ) * ∑ b, Q a0 b * v b)
            + (t : ℂ) * ∑ b ∈ Finset.univ.erase a0, Q a0 b * v b‖ := by rw [hid]
      _ ≤ ‖v a0 - (t : ℂ) * ∑ b, Q a0 b * v b‖
            + ‖(t : ℂ) * ∑ b ∈ Finset.univ.erase a0, Q a0 b * v b‖ := norm_add_le _ _
      _ ≤ B + t * ((1 - ‖m‖ ^ 2) * V) := by
        refine add_le_add (hB a0) ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
        refine mul_le_mul_of_nonneg_left ?_ ht0
        calc ‖∑ b ∈ Finset.univ.erase a0, Q a0 b * v b‖
            ≤ ∑ b ∈ Finset.univ.erase a0, ‖Q a0 b * v b‖ := norm_sum_le _ _
          _ ≤ ∑ b ∈ Finset.univ.erase a0, ‖Q a0 b‖ * V :=
              Finset.sum_le_sum fun b _ => by
                rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ha0 b) (norm_nonneg _)
          _ = (1 - ‖m‖ ^ 2) * V := by rw [← Finset.sum_mul, hoff]
  have h1m : 0 ≤ 1 - ‖m‖ ^ 2 := by nlinarith [norm_nonneg m]
  have h2 : t * ((1 - ‖m‖ ^ 2) * V) ≤ (1 - κ ^ 2 / 4) * D * V := by
    have h3 : t * ((1 - ‖m‖ ^ 2) * V) ≤ (1 - ‖m‖ ^ 2) * V := by
      have := mul_nonneg h1m hV0
      nlinarith
    have h4 : (1 - ‖m‖ ^ 2) * V ≤ ((1 - κ ^ 2 / 4) * D) * V := mul_le_mul_of_nonneg_right hD2 hV0
    linarith
  have hε : 0 < κ ^ 2 / 4 := by positivity
  have h4 : κ ^ 2 / 4 * D * V ≤ B := by nlinarith
  have h5 : (κ ^ 2 / 4) ^ 2 * V ≤ B := by
    have h6 : (κ ^ 2 / 4) * (κ ^ 2 / 4) * V ≤ κ ^ 2 / 4 * D * V :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1 hε.le) hV0
    nlinarith
  calc ‖v a‖ ≤ V := ha0 a
    _ = 16 * κ⁻¹ ^ 4 * ((κ ^ 2 / 4) ^ 2 * V) := by
        have : κ ≠ 0 := hκ.ne'
        field_simp
        norm_num
    _ ≤ 16 * κ⁻¹ ^ 4 * B := mul_le_mul_of_nonneg_left h5 (by positivity)

/-! ## 2. The row facts of `M`

`c₀ = BAct_rate d Λ κ`, `S_c = expC (d - 2) c ≥ Σ_x e^{-c|y-x|}`.  All uniform in `L` (and in `W`). -/

section Rows

variable {d L : ℕ} [NeZero L]

/-- The `ℓ¹` row of `M^{(B)}` for every `2 ≤ d` (`BAMB_row_l1` at `d = k + 2`): `Σ_b |M_ab| ≤ c₀⁻¹ S_{c₀}`. -/
theorem baM_row_l1 (hd : 2 ≤ d) (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a : Zd d L) :
    ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  simpa using BAMB_row_l1 k L hL Λ g κ E m hΛ hg hgΛ hκ hr a

/-- **`ρ`**: the `ℓ¹` column of `M^{(B)}`, `sup_c Σ_b |M_bc| ≤ c₀⁻¹ S_{c₀}` (`BAMB_symm`, `BAMB_row_l1`). -/
theorem baM_col_l1 (hd : 2 ≤ d) (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (c : Zd d L) :
    ∑ b, ‖BAMB d L g (E : ℂ) m b c‖ ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) := by
  have h := baM_row_l1 hd hL Λ g κ E m hΛ hg hgΛ hκ hr c
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) h
  rw [BAMB_symm d L g (E : ℂ) m b c]

/-- **`ρ₂ ≤ 1`**: `Σ_b |M_ab||M_bc| ≤ 1` (Ward `Σ_b |M_ab|² = 1`, `BAMB_symm`, Cauchy-Schwarz).  Only
`BASelf` is used (no `κ`, no `Λ`, no `L ≥ 3`). -/
theorem baM_rho2 (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a c : Zd d L) :
    ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ * ‖BAMB d L g (E : ℂ) m b c‖ ≤ 1 := by
  have h1 := BAMB_row_sq_real d L g E m h a
  have h2 : ∑ b, ‖BAMB d L g (E : ℂ) m b c‖ ^ 2 = 1 := by
    rw [← BAMB_row_sq_real d L g E m h c]
    exact Finset.sum_congr rfl fun b _ => by rw [BAMB_symm d L g (E : ℂ) m b c]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => ‖BAMB d L g (E : ℂ) m a b‖) (fun b => ‖BAMB d L g (E : ℂ) m b c‖)
  simp only [h1, h2, mul_one] at hcs
  have h0 : 0 ≤ ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ * ‖BAMB d L g (E : ℂ) m b c‖ :=
    Finset.sum_nonneg fun b _ => by positivity
  nlinarith

end Rows

/-! ## 3. The weighted `ℓ¹` row bound of `Θ_t`

Translation invariance: `baP8_BATheta_shift` (`BA/Prop6Path.lean`):
`Θ_t(a + r, b + r) = Θ_t(a, b)`. -/

/-- `c_λ = min (c₀/12) (μ/6)`, `c₀ = BAct_rate`, `μ = BAp5s_rate`. -/
def GreenStab_clam (d : ℕ) (Λ κ : ℝ) : ℝ := min (BAct_rate d Λ κ / 12) (BAp5s_rate d Λ κ / 6)

/-- `C_Θ̂ = C₅ (1 + Λ² S_{2μ/3})`, `C₅ = BAp5s_C`, `S_c = expC (d - 2) c`. -/
def GreenStab_CTheta (d : ℕ) (Λ κ : ℝ) : ℝ :=
  BAp5s_C d Λ κ * (1 + Λ ^ 2 * expC (d - 2) (2 * BAp5s_rate d Λ κ / 3))

theorem GreenStab_clam_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < GreenStab_clam d Λ κ := by
  have h1 := BAct_rate_pos d Λ κ hd hΛ hκ
  have h2 := BAp5s_rate_pos d Λ κ hd hΛ hκ
  unfold GreenStab_clam
  exact lt_min (by positivity) (by positivity)

theorem GreenStab_clam_le_c0 (d : ℕ) (Λ κ : ℝ) : 12 * GreenStab_clam d Λ κ ≤ BAct_rate d Λ κ := by
  have := min_le_left (BAct_rate d Λ κ / 12) (BAp5s_rate d Λ κ / 6)
  unfold GreenStab_clam
  linarith

theorem GreenStab_clam_le_mu (d : ℕ) (Λ κ : ℝ) : 6 * GreenStab_clam d Λ κ ≤ BAp5s_rate d Λ κ := by
  have := min_le_right (BAct_rate d Λ κ / 12) (BAp5s_rate d Λ κ / 6)
  unfold GreenStab_clam
  linarith

section Theta

variable {d L : ℕ} [NeZero L]

/-- **`C_Θ̂`**: `sup_b Σ_{a'} |Θ_{t,ba'}| e^{2c_λ|b-a'|} ≤ C₅ (1 + Λ² S_{2μ/3})`, every `σ`, `t ∈ [0, 1]`,
`0 < g ≤ Λ`, uniform in `L`.  Translation invariance (`baP8_BATheta_shift`) reduces it to
`|Θ_{t,0x}| ≤ C₅ (1_{x=0} + g² e^{-μ|x|})` (`baProp5s_of_real`, explicit `C₅, μ`) and `2c_λ ≤ μ/3`. -/
theorem baTheta_weighted_l1 (hd : 2 ≤ d) (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ)
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (σ : Bool) (b : Zd d L) :
    ∑ a', ‖BATheta d L g E m t σ σ b a'‖ *
        Real.exp (2 * GreenStab_clam d Λ κ * (zdistD d L (b - a') : ℝ))
      ≤ GreenStab_CTheta d Λ κ := by
  have hd0 : 0 < d := by omega
  have hμ : 0 < BAp5s_rate d Λ κ := BAp5s_rate_pos d Λ κ hd0 hΛ hκ
  have hC : 0 < BAp5s_C d Λ κ := BAp5s_C_pos d Λ κ hd0 hΛ hκ
  have hcl := GreenStab_clam_le_mu d Λ κ
  have hcl0 := GreenStab_clam_pos d Λ κ hd0 hΛ hκ
  set μ := BAp5s_rate d Λ κ with hμdef
  set C := BAp5s_C d Λ κ with hCdef
  set cl := GreenStab_clam d Λ κ with hcldef
  -- reindex `a' = x + b`
  have hre : ∑ a', ‖BATheta d L g E m t σ σ b a'‖ * Real.exp (2 * cl * (zdistD d L (b - a') : ℝ))
      = ∑ x, ‖BATheta d L g E m t σ σ 0 x‖ * Real.exp (2 * cl * (zdistD d L x : ℝ)) := by
    refine Fintype.sum_equiv (Equiv.subRight b) _ _ fun a' => ?_
    have hs := baP8_BATheta_shift g E m t σ σ 0 (a' - b) b
    rw [zero_add, sub_add_cancel] at hs
    have hdist : zdistD d L (b - a') = zdistD d L (a' - b) := by
      rw [show b - a' = -(a' - b) by ring, zdistD_neg]
    simp only [Equiv.subRight_apply, hs, hdist]
  rw [hre]
  -- termwise bound
  have hterm : ∀ x : Zd d L, ‖BATheta d L g E m t σ σ 0 x‖ * Real.exp (2 * cl * (zdistD d L x : ℝ))
      ≤ C * (if x = 0 then 1 else 0)
        + C * g ^ 2 * Real.exp (-(2 * μ / 3 * (zdistD d L x : ℝ))) := by
    intro x
    have h5 := baProp5s_of_real d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr t ht0 ht1 σ x
    have hr0 : (0 : ℝ) ≤ (zdistD d L x : ℝ) := Nat.cast_nonneg _
    have hexp : Real.exp (-μ * (zdistD d L x : ℝ)) * Real.exp (2 * cl * (zdistD d L x : ℝ))
        ≤ Real.exp (-(2 * μ / 3 * (zdistD d L x : ℝ))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hE0 : 0 ≤ Real.exp (2 * cl * (zdistD d L x : ℝ)) := (Real.exp_pos _).le
    calc ‖BATheta d L g E m t σ σ 0 x‖ * Real.exp (2 * cl * (zdistD d L x : ℝ))
        ≤ (C * ((if x = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-μ * (zdistD d L x : ℝ))))
            * Real.exp (2 * cl * (zdistD d L x : ℝ)) := mul_le_mul_of_nonneg_right h5 hE0
      _ = C * ((if x = 0 then (1 : ℝ) else 0) * Real.exp (2 * cl * (zdistD d L x : ℝ)))
            + C * g ^ 2 * (Real.exp (-μ * (zdistD d L x : ℝ)) * Real.exp (2 * cl * (zdistD d L x : ℝ))) := by
          ring
      _ ≤ C * (if x = 0 then 1 else 0) + C * g ^ 2 * Real.exp (-(2 * μ / 3 * (zdistD d L x : ℝ))) := by
          refine add_le_add (le_of_eq ?_) (mul_le_mul_of_nonneg_left hexp (by positivity))
          by_cases hx : x = 0
          · subst hx; simp
          · simp [hx]
  calc ∑ x, ‖BATheta d L g E m t σ σ 0 x‖ * Real.exp (2 * cl * (zdistD d L x : ℝ))
      ≤ ∑ x : Zd d L, (C * (if x = 0 then (1 : ℝ) else 0)
          + C * g ^ 2 * Real.exp (-(2 * μ / 3 * (zdistD d L x : ℝ)))) := Finset.sum_le_sum fun x _ => hterm x
    _ = C + C * g ^ 2 * ∑ x : Zd d L, Real.exp (-(2 * μ / 3 * (zdistD d L (0 - x) : ℝ))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one, zero_sub, zdistD_neg]
    _ ≤ C + C * g ^ 2 * expC (d - 2) (2 * μ / 3) := by
        have hCg : 0 ≤ C * g ^ 2 := by positivity
        have h23 : 0 < 2 * μ / 3 := by positivity
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hCg)
        exact BAsum_exp_decay_le d L hd _ h23 0
    _ ≤ GreenStab_CTheta d Λ κ := by
        unfold GreenStab_CTheta
        have hS : 0 ≤ expC (d - 2) (2 * μ / 3) := by
          unfold RBM.expC; positivity
        have hg2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
        have : C * g ^ 2 * expC (d - 2) (2 * μ / 3) ≤ C * (Λ ^ 2 * expC (d - 2) (2 * μ / 3)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg2 hS) hC.le
        nlinarith

end Theta


end RBM.BA
