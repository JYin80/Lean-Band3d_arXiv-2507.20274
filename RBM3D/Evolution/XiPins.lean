/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.Pins
import RBM3D.Kernel.SumDecay
import RBM3D.Kernel.Evolution
import RBM3D.Propagator.Prop5Short

/-!
# Evolution kernel EK-2: the bounds of the one-index kernel `Ξ` on the propagator pins

Pins `EKXiDecay` (`(eq:decayXi)`), `EKXiBall` (ball sums of `Ξ`), `EKSameRow` (`(eq:samecolor)`)
and their proofs `ekXiDecay_holds`, `ekXiBall_holds`, `ekSameRow_holds`, uniform in `g ∈ (0, Λ]`
and in the unit `μ`.  The decay antecedent is `Prop5Decay` (the first two) and nothing for the
same-sign row (`prop5Short_holds` is proved).

* `ek_norm_XiKer_apply_le`, `ek_sum_ball_norm_XiKer_le` are the lemmas of the T2016 probe
  (`c961e62:RBM3D/Probe/T2016Pins.lean`, lines 210-447), copied unchanged: the decay bound of
  `Θ_{tμ}(0, ·)` enters as an explicit hypothesis `hbd` with visible constants.
* `hbd` is discharged from `Prop5Decay` at `m` with `m * m = μ` and `σ₁ = σ₂ = true`.
* `ekSameRow_holds` ports `exists_norm_uKer_same_le` (`Kernel/Evolution.lean:445-510`), with
  `prop5Short_holds` instead of `ThetaDecayShort`.
-/

set_option linter.style.longLine false

namespace RBM

/-! ### The probe lemmas (copied unchanged) -/

section Skeleton

/-- `(eq:decayXi)` with the constants of the decay bound visible (uniform in `g`). -/
theorem ek_norm_XiKer_apply_le {k : ℕ} {g : ℝ} {μ : ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g)
    (hμ : ‖μ‖ = 1) {Cd cd : ℝ} (hCd : 0 < Cd) (hcd : 0 < cd)
    (hbd : ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd (k + 2) L,
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta (k + 2) L g ((t : ℂ) * μ) 0 a‖
        ≤ Cd * Bparam (k + 2) L g t (zdistD (k + 2) L a)
            * Real.exp (-cd * (zdistD (k + 2) L a : ℝ) / ellT L g t)) :
    ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
      haveI : NeZero L := ⟨by omega⟩
      ∀ a b : Zd (k + 2) L,
        ‖XiKer (k + 2) L g μ s t a b‖
          ≤ (Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * 2 ^ k * Real.exp cd) * (1 - s)
            * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD (k + 2) L (a - b) : ℝ) + 1) ^ k)⁻¹
            * Real.exp (-(cd * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t) := by
  intro L hL s t hs hst ht hgt
  have : NeZero L := ⟨by omega⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  have ht0 : 0 ≤ t := hs.trans hst
  have hξ : ‖(t : ℂ) * μ‖ < 1 := norm_t_mul_lt_one ht0 ht hμ
  have hℓ : 1 ≤ ellT L g t := one_le_ellT hL1
  have hℓ0 : 0 < ellT L g t := by linarith
  intro a b
  set A : ℝ := (g ^ 2 + |1 - t|)⁻¹ with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set R : ℝ := (zdistD (k + 2) L (a - b) : ℝ) with hR
  set C₀ : ℝ := Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * 2 ^ k * Real.exp cd with hC₀
  -- the profile at a neighbour of `a` is the profile at `a`, up to constants
  have hprof : ∀ c : Zd (k + 2) L, zdistD (k + 2) L (a - c) ≤ 1 →
      ‖Theta (k + 2) L g ((t : ℂ) * μ) c b‖
        ≤ C₀ * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t) := by
    intro c hc
    have htrans : Theta (k + 2) L g ((t : ℂ) * μ) c b
        = Theta (k + 2) L g ((t : ℂ) * μ) 0 (b - c) := by
      have h := Theta_apply_add_right_of_three_le (g := g) hL hξ 0 (b - c) c
      simpa using h
    rw [htrans]
    have hb := hbd L hL t ht0 ht (b - c)
    set r : ℝ := (zdistD (k + 2) L (b - c) : ℝ) with hr
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    -- the triangle inequality, with `|a - c| ≤ 1`
    have htri : zdistD (k + 2) L (a - b)
        ≤ zdistD (k + 2) L (a - c) + zdistD (k + 2) L (c - b) := by
      have h := zdistD_add_le (k + 2) L (a - c) (c - b)
      rwa [sub_add_sub_cancel] at h
    have hcb : zdistD (k + 2) L (c - b) = zdistD (k + 2) L (b - c) := by
      rw [← zdistD_neg (k + 2) L (b - c), neg_sub]
    have hRr : R ≤ 1 + r := by
      rw [hR, hr, ← hcb]
      have : zdistD (k + 2) L (a - b) ≤ 1 + zdistD (k + 2) L (c - b) := by omega
      exact_mod_cast this
    -- the zero mode is dominated by the decay term
    have hzm : Bparam (k + 2) L g t (zdistD (k + 2) L (b - c))
        ≤ (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * (A * ((r + 1) ^ k)⁻¹) := by
      have hz := zeroMode_le_of_ge_mul (k := k) (L := L) (g := g) (t := t) (m := k + 2)
        (by omega) hL1 ht (zdistD_le (k + 2) (b - c)) hgt
      have hcast : ((2 : ℝ) * ((k + 2 : ℕ) : ℝ)) ^ k = (2 * ((k : ℝ) + 2)) ^ k := by
        push_cast; ring_nf
      rw [hcast] at hz
      simp only [Bparam, powW, hA, hr] at hz ⊢
      have hpow : (0 : ℝ) < ((zdistD (k + 2) L (b - c) : ℝ) + 1) ^ (k + 2 - 2) := by
        norm_num
        positivity
      simp only [show k + 2 - 2 = k from rfl] at hpow ⊢
      nlinarith [hz, inv_nonneg.mpr hpow.le]
    -- the shift in the power and in the exponential
    have hshift : ((r + 1) ^ k)⁻¹ ≤ 2 ^ k * ((R + 1) ^ k)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div,
        div_le_iff₀ (by positivity)]
      calc (R + 1) ^ k ≤ (2 * (r + 1)) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 2 ^ k * (r + 1) ^ k := mul_pow _ _ _
    have hexp : Real.exp (-cd * r / ellT L g t)
        ≤ Real.exp cd * Real.exp (-(cd * R) / ellT L g t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hdiff : cd + -(cd * R) / ellT L g t - -cd * r / ellT L g t
          = cd - cd * (R - r) / ellT L g t := by field_simp; ring
      have hle : cd * (R - r) / ellT L g t ≤ cd := by
        rw [div_le_iff₀ hℓ0]
        nlinarith [hcd.le, hℓ, hRr]
      rw [← sub_nonneg, hdiff]
      linarith
    have hB0 : 0 ≤ Bparam (k + 2) L g t (zdistD (k + 2) L (b - c)) := by
      simp only [Bparam]
      have h1 : (0 : ℝ) ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
      have h2 : (0 : ℝ) ≤ (((zdistD (k + 2) L (b - c) : ℝ)) + 1) ^ (k + 2 - 2) := by positivity
      have h3 : (0 : ℝ) ≤ ((L : ℝ) ^ (k + 2) * |1 - t|)⁻¹ := by positivity
      positivity
    calc ‖Theta (k + 2) L g ((t : ℂ) * μ) 0 (b - c)‖
        ≤ Cd * Bparam (k + 2) L g t (zdistD (k + 2) L (b - c))
            * Real.exp (-cd * r / ellT L g t) := hb
      _ ≤ Cd * ((1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * (A * ((r + 1) ^ k)⁻¹))
            * (Real.exp cd * Real.exp (-(cd * R) / ellT L g t)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hzm hCd.le) hexp (Real.exp_pos _).le
          positivity
      _ ≤ Cd * ((1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * (A * (2 ^ k * ((R + 1) ^ k)⁻¹)))
            * (Real.exp cd * Real.exp (-(cd * R) / ellT L g t)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ hCd.le
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hshift hA0.le
      _ = C₀ * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t) := by
          rw [hC₀]; ring
  -- sum over the neighbours of `a`
  have hrow : ∑ c : Zd (k + 2) L, ‖SB (k + 2) L g a c‖ = 1 := sum_norm_SB_row (k + 2) L g hL a
  have hterm : ∀ c : Zd (k + 2) L,
      ‖SB (k + 2) L g a c‖ * ‖Theta (k + 2) L g ((t : ℂ) * μ) c b‖
        ≤ ‖SB (k + 2) L g a c‖
          * (C₀ * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t)) := by
    intro c
    by_cases hc : zdistD (k + 2) L (a - c) ≤ 1
    · exact mul_le_mul_of_nonneg_left (hprof c hc) (norm_nonneg _)
    · rw [SB_apply_eq_zero_of_one_lt (by omega)]
      simp
  have hmul : ‖XiKer (k + 2) L g μ s t a b‖
      ≤ (t - s) * ∑ c : Zd (k + 2) L,
          ‖SB (k + 2) L g a c‖ * ‖Theta (k + 2) L g ((t : ℂ) * μ) c b‖ := by
    rw [XiKer]
    have hcoef : ‖((t : ℂ) - s) * μ‖ = t - s := by
      rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, hcoef, Matrix.mul_apply]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc ‖∑ c : Zd (k + 2) L, SB (k + 2) L g a c * Theta (k + 2) L g ((t : ℂ) * μ) c b‖
        ≤ ∑ c : Zd (k + 2) L, ‖SB (k + 2) L g a c * Theta (k + 2) L g ((t : ℂ) * μ) c b‖ :=
          norm_sum_le _ _
      _ = _ := Finset.sum_congr rfl fun c _ => norm_mul _ _
  calc ‖XiKer (k + 2) L g μ s t a b‖
      ≤ (t - s) * ∑ c : Zd (k + 2) L,
          ‖SB (k + 2) L g a c‖ * ‖Theta (k + 2) L g ((t : ℂ) * μ) c b‖ := hmul
    _ ≤ (t - s) * ∑ c : Zd (k + 2) L, ‖SB (k + 2) L g a c‖
          * (C₀ * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hterm c) (by linarith)
    _ = (t - s) * (C₀ * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t)) := by
        rw [← Finset.sum_mul, hrow, one_mul]
    _ ≤ (1 - s) * (C₀ * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t)) := by
        refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = C₀ * (1 - s) * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t) := by ring

/-- One factor of `(sum_res_1)` over a ball, constants of the decay bound visible (uniform in
`g`). -/
theorem ek_sum_ball_norm_XiKer_le {k : ℕ} {g : ℝ} {μ : ℂ} (hg : 0 < g)
    {C₀ c : ℝ} (hC₀ : 0 < C₀) (hc : 0 < c)
    (hbd : ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
      haveI : NeZero L := ⟨by omega⟩
      ∀ a b : Zd (k + 2) L,
        ‖XiKer (k + 2) L g μ s t a b‖
          ≤ C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
            * (((zdistD (k + 2) L (a - b) : ℝ) + 1) ^ k)⁻¹
            * Real.exp (-(c * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t)) :
    ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 →
      g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t → ∀ Λ : ℝ, 1 ≤ Λ → ∀ R : ℝ, 1 ≤ R →
      R ≤ Λ * ellT L g s →
      haveI : NeZero L := ⟨by omega⟩
      ∀ (a ctr : Zd (k + 2) L) (D : Finset (Zd (k + 2) L)),
        (∀ b ∈ D, ((zdistD (k + 2) L (ctr - b) : ℕ) : ℝ) ≤ R) →
        ∑ b ∈ D, ‖XiKer (k + 2) L g μ s t a b‖
          ≤ (4 * C₀ * ballC k) * Λ ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) := by
  intro L hL s t hs hst ht hgt Λ hΛ R hR hRℓ a ctr D hD
  have : NeZero L := ⟨by omega⟩
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans (by norm_num) hL
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have habs : |1 - s| = 1 - s := abs_of_pos (by linarith)
  have hgt0 : (0 : ℝ) < g ^ 2 + |1 - t| := by positivity
  -- the entries, with the exponential thrown away
  have hpt : ∀ b ∈ D, ‖XiKer (k + 2) L g μ s t a b‖
      ≤ (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹)
        * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by
    intro b _
    refine (hbd L hL s t hs hst ht hgt a b).trans ?_
    have hexp : Real.exp (-(c * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hℓ : 0 < ellT L g t := ellT_pos hL1
      have : 0 ≤ c * (zdistD (k + 2) L (a - b) : ℝ) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le
    have hnn : (0 : ℝ) ≤ C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
        * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by
      have : (0 : ℝ) ≤ 1 - s := by linarith
      positivity
    calc C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
          * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹
          * Real.exp (-(c * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t)
        ≤ C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
          * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp hnn
      _ = C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
          * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := mul_one _
  -- the ball sum of the polynomial factor
  -- the ball is around `ctr`, the `Ξ` factor around `a`: the truncated form of the Q20
  -- lemma is what allows the two centres to differ
  have hball : ∑ b ∈ D, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹
      ≤ ballC k * R ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun b _ => ?_)
      (sum_ball_min_pow_le (L := L) k hR D ctr a hD)
    have hmin : min ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) R
        ≤ ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) := min_le_left _ _
    have h1 : (0 : ℝ) < (min ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) R + 1) ^ k := by
      have : (0 : ℝ) ≤ min ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) R :=
        le_min (Nat.cast_nonneg _) (by linarith)
      positivity
    exact inv_anti₀ h1 (pow_le_pow_left₀ (by positivity) (by linarith) k)
  have hcoef : (0 : ℝ) ≤ C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹ := by
    have : (0 : ℝ) ≤ 1 - s := by linarith
    positivity
  -- `R² ≤ 4 Λ² ℓ_s²`, and `(1-s) ℓ_s² ≤ ĝ² + |1-s|`
  have hℓs : (1 : ℝ) ≤ ellT L g s := one_le_ellT hL1
  have hR2 : R ^ 2 ≤ Λ ^ 2 * ellT L g s ^ 2 := by
    have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ R) hRℓ 2
    rwa [mul_pow] at this
  have hkey : (1 - s) * (Λ ^ 2 * ellT L g s ^ 2) ≤ Λ ^ 2 * (g ^ 2 + |1 - s|) := by
    have h := one_sub_mul_ellT_sq_le (L := L) (g := g) (s := s) hg.le hs1
    rw [habs] at h
    nlinarith [sq_nonneg Λ, ellT_pos hL1 (L := L) (g := g) (t := s)]
  calc ∑ b ∈ D, ‖XiKer (k + 2) L g μ s t a b‖
      ≤ ∑ b ∈ D, (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹)
          * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := Finset.sum_le_sum hpt
    _ = (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹)
          * ∑ b ∈ D, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹) * (ballC k * R ^ 2) :=
        mul_le_mul_of_nonneg_left hball hcoef
    _ ≤ (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹) * (ballC k * (Λ ^ 2 * ellT L g s ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        exact mul_le_mul_of_nonneg_left hR2 (ballC_nonneg k)
    _ = C₀ * ballC k * ((1 - s) * (Λ ^ 2 * ellT L g s ^ 2)) * (g ^ 2 + |1 - t|)⁻¹ := by ring
    _ ≤ C₀ * ballC k * (Λ ^ 2 * (g ^ 2 + |1 - s|)) * (g ^ 2 + |1 - t|)⁻¹ := by
        have h0 : (0 : ℝ) ≤ C₀ * ballC k := mul_nonneg hC₀.le (ballC_nonneg k)
        have := mul_le_mul_of_nonneg_left hkey h0
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = C₀ * ballC k * Λ ^ 2 * ((g ^ 2 + |1 - s|) * (g ^ 2 + |1 - t|)⁻¹) := by ring
    _ ≤ 4 * C₀ * ballC k * Λ ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) := by
        rw [div_eq_mul_inv]
        have h0 : (0 : ℝ) ≤ C₀ * ballC k * Λ ^ 2 * ((g ^ 2 + |1 - s|) * (g ^ 2 + |1 - t|)⁻¹) := by
          refine mul_nonneg (mul_nonneg (mul_nonneg hC₀.le (ballC_nonneg k)) (sq_nonneg Λ)) ?_
          have h1 : (0:ℝ) ≤ g ^ 2 + |1 - s| := by positivity
          have h2 : (0:ℝ) ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
          exact mul_nonneg h1 h2
        linarith

end Skeleton

/-! ### The pins -/

open scoped Matrix.Norms.Operator

/-- `(eq:decayXi)`, uniform in `g ∈ (0, Λ]` and in the unit `μ`, from pin 5 (`Prop5Decay`). -/
def EKXiDecay (d : ℕ) (Λ : ℝ) : Prop :=
  Prop5Decay d Λ → 3 ≤ d → 0 < Λ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ μ : ℂ, ‖μ‖ = 1 →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
          haveI : NeZero L := ⟨by omega⟩
          ∀ a b : Zd d L,
            ‖XiKer d L g μ s t a b‖
              ≤ C * (1 - s) * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L (a - b) : ℝ) + 1) ^ (d - 2))⁻¹
                * Real.exp (-(c * (zdistD d L (a - b) : ℝ)) / ellT L g t)

/-- Ball sums of `Ξ` over any set within distance `R ≤ Λ' ℓ_s` of a centre (pin 5 again). -/
def EKXiBall (d : ℕ) (Λ : ℝ) : Prop :=
  Prop5Decay d Λ → 3 ≤ d → 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ μ : ℂ, ‖μ‖ = 1 →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
          ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
          haveI : NeZero L := ⟨by omega⟩
          ∀ (a ctr : Zd d L) (D : Finset (Zd d L)), (∀ b ∈ D, (zdistD d L (ctr - b) : ℝ) ≤ R) →
            ∑ b ∈ D, ‖XiKer d L g μ s t a b‖ ≤ C * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))

/-- `(eq:samecolor)`: at a same-sign index the one-index factor `(1 − sμS)Θ_{tμ}`, `μ = m(σ)²`, is bounded in
the `∞ → ∞` norm, uniformly in `L, g ≤ Λ, s, t`; bulk `κ ≤ Im m`. -/
def EKSameRow (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im →
        ∀ σ : Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
          haveI : NeZero L := ⟨by omega⟩
          ‖uKer d L g (PropSpin m σ * PropSpin m σ) s t‖ ≤ C

/-! ### The proofs -/

/-- a unit `μ` is `m * m` for a unit `m` -/
private theorem xp_exists_sqrt {μ : ℂ} (hμ : ‖μ‖ = 1) : ∃ m : ℂ, ‖m‖ = 1 ∧ m * m = μ := by
  have hμ0 : μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hμ; exact zero_ne_one hμ
  have hm : Complex.exp (Complex.log μ / 2) * Complex.exp (Complex.log μ / 2) = μ := by
    rw [← Complex.exp_add, add_halves, Complex.exp_log hμ0]
  set m : ℂ := Complex.exp (Complex.log μ / 2) with hmdef
  refine ⟨m, ?_, hm⟩
  have h : ‖m‖ * ‖m‖ = 1 := by rw [← norm_mul, hm, hμ]
  have h0 : 0 ≤ ‖m‖ := norm_nonneg _
  nlinarith

/-- `(eq:decayXi)` from pin 5. -/
theorem ekXiDecay_holds (d : ℕ) (Λ : ℝ) : EKXiDecay d Λ := by
  intro h5 hd hΛ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := h5 hd hΛ
  refine ⟨Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * 2 ^ k * Real.exp cd, cd, by positivity, hcd, ?_⟩
  intro L hL g hg hgΛ μ hμ s t hs hst ht hgt
  obtain ⟨m, hm, hmm⟩ := xp_exists_sqrt hμ
  have hbd' : ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd (k + 2) L,
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta (k + 2) L g ((t : ℂ) * μ) 0 a‖
        ≤ Cd * Bparam (k + 2) L g t (zdistD (k + 2) L a)
            * Real.exp (-cd * (zdistD (k + 2) L a : ℝ) / ellT L g t) := by
    intro L hL t ht0 ht1 a
    have h := hbd L hL g hg hgΛ t ht0 ht1 m hm true true a
    simpa [PropSpin, hmm] using h
  exact ek_norm_XiKer_apply_le hd hg hμ hCd hcd hbd' L hL s t hs hst ht hgt

/-- ball sums of `Ξ` from pin 5. -/
theorem ekXiBall_holds (d : ℕ) (Λ : ℝ) : EKXiBall d Λ := by
  intro h5 hd hΛ
  obtain ⟨C₀, c, hC₀, hc, hdec⟩ := ekXiDecay_holds d Λ h5 hd hΛ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  refine ⟨4 * C₀ * ballC k, mul_pos (by positivity) (ballC_pos k), ?_⟩
  intro L hL g hg hgΛ μ hμ s t hs hst ht hgt Λ' hΛ' R hR hRℓ a ctr D hD
  exact ek_sum_ball_norm_XiKer_le (g := g) (μ := μ) hg hC₀ hc
    (fun L hL s t hs hst ht hgt => hdec L hL g hg hgΛ μ hμ s t hs hst ht hgt)
    L hL s t hs hst ht hgt Λ' hΛ' R hR hRℓ a ctr D hD

/-- `(eq:samecolor)` from pin 5s (proved). -/
theorem ekSameRow_holds (d : ℕ) (Λ κ : ℝ) : EKSameRow d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cκ, hCκ, cκ, hcκ, hbd⟩ := prop5Short_holds (k + 2) Λ κ hd hΛ hκ
  have hexp0 : 0 ≤ expC k cκ := by
    unfold expC
    have : (0 : ℝ) < cκ ^ (k + 3) := by positivity
    positivity
  refine ⟨1 + Cκ * (1 + Λ ^ 2 * expC k cκ), by positivity, ?_⟩
  intro L hL g hg hgΛ m hm hκm σ s t hs hst ht
  have : NeZero L := ⟨by omega⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℂ, μ = PropSpin m σ * PropSpin m σ := ⟨_, rfl⟩
  rw [← hμdef]
  have hμ : ‖μ‖ = 1 := by
    rw [hμdef, norm_mul, ek_norm_spin hm σ, mul_one]
  have ht0 : 0 ≤ t := hs.trans hst
  have hξ : ‖(t : ℂ) * μ‖ < 1 := norm_t_mul_lt_one ht0 ht hμ
  -- the propagator at a same-sign parameter has bounded `(∞→∞)`-norm
  have hTheta : ‖Theta (k + 2) L g ((t : ℂ) * μ)‖ ≤ Cκ * (1 + Λ ^ 2 * expC k cκ) := by
    have htrans : ∀ a b c : Zd (k + 2) L,
        Theta (k + 2) L g ((t : ℂ) * μ) (a + c) (b + c)
          = Theta (k + 2) L g ((t : ℂ) * μ) a b :=
      fun a b c => Theta_apply_add_right_of_three_le hL hξ a b c
    refine (norm_le_sum_row_zero _ htrans).trans ?_
    calc ∑ b : Zd (k + 2) L, ‖Theta (k + 2) L g ((t : ℂ) * μ) 0 b‖
        ≤ ∑ b : Zd (k + 2) L, Cκ * ((if b = 0 then 1 else 0)
            + g ^ 2 * Real.exp (-cκ * (zdistD (k + 2) L b : ℝ))) :=
          Finset.sum_le_sum fun b _ => by
            rw [hμdef]; exact hbd L hL g hg hgΛ t ht0 ht m hm hκm σ b
      _ = Cκ * (1 + g ^ 2 * ∑ b : Zd (k + 2) L,
            Real.exp (-(cκ * (zdistD (k + 2) L b : ℝ)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 2
          · simp
          · exact congrArg _ (Finset.sum_congr rfl fun b _ => by ring_nf)
      _ ≤ Cκ * (1 + Λ ^ 2 * expC k cκ) := by
          have hsum := sum_radial_exp_decay_le (L := L) k hcκ
          have hg2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
          have hs0 : 0 ≤ ∑ b : Zd (k + 2) L, Real.exp (-(cκ * (zdistD (k + 2) L b : ℝ))) :=
            Finset.sum_nonneg fun b _ => (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_left ?_ hCκ.le
          have h1 := mul_le_mul_of_nonneg_left hsum (sq_nonneg g)
          have h2 := mul_le_mul_of_nonneg_right hg2 hexp0
          linarith
  -- and `uKer = 1 + Ξ` with `‖Ξ‖ ≤ (t - s) ‖Θ‖ ≤ ‖Θ‖`
  rw [uKer_eq_one_add hL hξ]
  have hc : ‖((t : ℂ) - s) * μ‖ ≤ 1 := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  calc ‖(1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ)
        + (((t : ℂ) - s) * μ) • (SB (k + 2) L g * Theta (k + 2) L g ((t : ℂ) * μ))‖
      ≤ 1 + ‖(((t : ℂ) - s) * μ)
          • (SB (k + 2) L g * Theta (k + 2) L g ((t : ℂ) * μ))‖ := by
        have := norm_add_le (1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ)
          ((((t : ℂ) - s) * μ) • (SB (k + 2) L g * Theta (k + 2) L g ((t : ℂ) * μ)))
        rwa [norm_one] at this
    _ ≤ 1 + Cκ * (1 + Λ ^ 2 * expC k cκ) := by
        have hsmul := norm_smul_le (((t : ℂ) - s) * μ)
          (SB (k + 2) L g * Theta (k + 2) L g ((t : ℂ) * μ))
        have hmul := norm_mul_le (SB (k + 2) L g) (Theta (k + 2) L g ((t : ℂ) * μ))
        rw [norm_SB (k + 2) L g hL, one_mul] at hmul
        have h1 : ‖(((t : ℂ) - s) * μ)
            • (SB (k + 2) L g * Theta (k + 2) L g ((t : ℂ) * μ))‖
            ≤ 1 * ‖Theta (k + 2) L g ((t : ℂ) * μ)‖ := by
          refine hsmul.trans ?_
          exact mul_le_mul hc hmul (norm_nonneg _) zero_le_one
        rw [one_mul] at h1
        linarith

/-! ### Compiled instances at `d = 3`, `Λ = 1`, `κ = 1/2`, `L = 5`, `g = 1/2`, `s = 1/2`, `t = 9/10`, `μ = 1`

`g² / L² = 1/100 ≤ 1 - t = 1/10`.  `Prop5Decay 3 1` (external, PT-F1 in flight) is the only
hypothesis of the first two instances; every deterministic hypothesis is discharged. -/

section Instances

/-- the lattice ball of radius `1` around `0` in `Z_5^3` (7 points) -/
private def xpBall : Finset (Zd 3 5) := Finset.univ.filter fun b => zdistD 3 5 (0 - b) ≤ 1

private theorem xp_zero_mem : (0 : Zd 3 5) ∈ xpBall := by
  simp [xpBall, zdistD, zdist]

private theorem xp_ball_dist : ∀ b ∈ xpBall, (zdistD 3 5 (0 - b) : ℝ) ≤ 1 := fun b hb => by
  exact_mod_cast (Finset.mem_filter.1 hb).2

/-- instance of `ekXiDecay_holds` at `L = 5`, `g = 1/2`, `s = 1/2`, `t = 9/10`, `μ = 1`. -/
example (h5 : Prop5Decay 3 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      haveI : NeZero 5 := ⟨by norm_num⟩
      ∀ a b : Zd 3 5,
        ‖XiKer 3 5 (1 / 2 : ℝ) 1 (1 / 2) (9 / 10) a b‖
          ≤ C * (1 - 1 / 2) * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
              * (((zdistD 3 5 (a - b) : ℝ) + 1) ^ (3 - 2))⁻¹
              * Real.exp (-(c * (zdistD 3 5 (a - b) : ℝ)) / ellT 5 (1 / 2 : ℝ) (9 / 10)) := by
  obtain ⟨C, c, hC, hc, H⟩ := ekXiDecay_holds 3 1 h5 le_rfl one_pos
  refine ⟨C, c, hC, hc, fun a b => ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1 (by simp) (1 / 2) (9 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) a b

/-- instance of `ekXiBall_holds` at the 7-point ball `D` around `ctr = 0`, `a = 0`, `Λ' = 1`,
`R = 1 ≤ ℓ_s`. -/
example (h5 : Prop5Decay 3 1) :
    ∃ C : ℝ, 0 < C ∧ (0 : Zd 3 5) ∈ xpBall ∧
      haveI : NeZero 5 := ⟨by norm_num⟩
      ∑ b ∈ xpBall, ‖XiKer 3 5 (1 / 2 : ℝ) 1 (1 / 2) (9 / 10) 0 b‖
        ≤ C * 1 ^ 2 * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) := by
  obtain ⟨C, hC, H⟩ := ekXiBall_holds 3 1 h5 le_rfl one_pos
  refine ⟨C, hC, xp_zero_mem, ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1 (by simp) (1 / 2) (9 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 le_rfl 1 le_rfl
    (by rw [one_mul]; exact one_le_ellT (by norm_num)) 0 0 xpBall xp_ball_dist

/-- instance of `ekSameRow_holds` at `m = i` (`Im m = 1 ≥ 1/2`), both signs. -/
example :
    ∃ C : ℝ, 0 < C ∧
      haveI : NeZero 5 := ⟨by norm_num⟩
      ∀ σ : Bool,
        ‖uKer 3 5 (1 / 2 : ℝ) (PropSpin Complex.I σ * PropSpin Complex.I σ) (1 / 2) (9 / 10)‖
          ≤ C := by
  obtain ⟨C, hC, H⟩ := ekSameRow_holds 3 1 (1 / 2) le_rfl one_pos (by norm_num)
  refine ⟨C, hC, fun σ => ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) Complex.I Complex.norm_I
    (by rw [Complex.I_im]; norm_num) σ (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num)

end Instances

end RBM
