/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4
import RBM3D.Propagator.Interface
import RBM3D.Defs.RadialSum

/-!
# A shape test for the interface: `(prop:ThfadC_short)` is a `σ₁ = σ₂` statement

`RBM.ThetaDecayShort` (`(prop:ThfadC_short)`, property 5' of `lem_propTH`) is stated for
the spectral parameter `m(σ)²` of the equal-sign case, with `0 < m.im`.  This file proves
that the restriction is *necessary*: the same bound at the spectral parameter `1` -- that
is, at `σ₁ ≠ σ₂`, where `m(+)m(-) = |m|² = 1` -- is **false**.

The argument is the one the paper's own structure suggests.  Summing the claimed bound
over `a` gives a constant, because `Σ_a e^{-c|a|}` is bounded uniformly in `L`
(`RBM.sum_radial_exp_decay_le`), while the row sum of the propagator is
`Σ_a Θ_{t,0a} = (1-t)⁻¹` (`RBM.sum_Theta_row_of_three_le`), which is unbounded as
`t → 1`.

This matters because an assumption that is false is not a harmless over-statement: every
theorem taking it as a hypothesis would be vacuous.  The interface was stated in that
form while properties 5–8 were axioms, where the same defect would have been an
inconsistency; `docs/paper-deltas.md` D11 records the correction.
-/

namespace RBM.Test

open Real

/-- **The equal-sign restriction in `RBM.ThetaDecayShort` is necessary.**  At the spectral
parameter `1`, which is the `σ₁ ≠ σ₂` case `m(+)m(-) = |m|² = 1`, the strong-decay bound
of `(prop:ThfadC_short)` fails. -/
theorem not_decayShort_at_one (k : ℕ) {g : ℝ} (hg : 0 < g) :
    ¬ ∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ),
        ∀ (L : ℕ) (_ : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd (k + 2) L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta (k + 2) L g ((t : ℂ) * 1) 0 a‖
            ≤ Cκ * ((if a = 0 then 1 else 0)
                + g ^ 2 * Real.exp (-cκ * (zdistD (k + 2) L a : ℝ))) := by
  rintro ⟨Cκ, hCκ, cκ, hcκ, h⟩
  have : NeZero 3 := ⟨by norm_num⟩
  -- the claimed bound sums to a constant, uniformly in `t`
  set M : ℝ := Cκ * (1 + g ^ 2 * expC k cκ) with hM
  have hM0 : 0 < M := by
    have : 0 ≤ expC k cκ := by
      unfold expC
      have : (0 : ℝ) < cκ ^ (k + 3) := by positivity
      positivity
    rw [hM]; positivity
  -- pick `t` so close to `1` that the row sum exceeds that constant
  set t : ℝ := 1 - 1 / (M + 2) with ht_def
  have hM2 : (0 : ℝ) < M + 2 := by linarith
  have ht0 : 0 ≤ t := by
    rw [ht_def]
    have : 1 / (M + 2) ≤ 1 := by
      rw [div_le_one hM2]; linarith
    linarith
  have ht1 : t < 1 := by
    rw [ht_def]
    have : 0 < 1 / (M + 2) := by positivity
    linarith
  have h1t : (1 : ℝ) - t = 1 / (M + 2) := by rw [ht_def]; ring
  -- the row sum of `Θ_t` at spectral parameter `1`
  have hξ : ‖((t : ℂ) * 1)‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]; exact ht1
  have hrow := sum_Theta_row_of_three_le (d := k + 2) (L := 3) (g := g) (by norm_num) hξ 0
  have hrow' : ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ = M + 2 := by
    rw [hrow, mul_one]
    have : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (by
      rw [h1t]; positivity)]
    rw [h1t, one_div, inv_inv]
  -- but the hypothesis bounds it by `M`
  have hsum_le : ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ ≤ M := by
    calc ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖
        ≤ ∑ b : Zd (k + 2) 3, ‖Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ := norm_sum_le _ _
      _ ≤ ∑ b : Zd (k + 2) 3, Cκ * ((if b = 0 then 1 else 0)
            + g ^ 2 * Real.exp (-cκ * (zdistD (k + 2) 3 b : ℝ))) :=
          Finset.sum_le_sum fun b _ => h 3 (by norm_num) t ht0 ht1 b
      _ = Cκ * (1 + g ^ 2 * ∑ b : Zd (k + 2) 3,
            Real.exp (-(cκ * (zdistD (k + 2) 3 b : ℝ)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 2
          · simp
          · exact congrArg _ (Finset.sum_congr rfl fun b _ => by ring_nf)
      _ ≤ M := by
          rw [hM]
          have hsum := sum_radial_exp_decay_le (L := 3) k hcκ
          have hg2 : (0 : ℝ) ≤ g ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left
            (by linarith [mul_le_mul_of_nonneg_left hsum hg2]) hCκ.le
  rw [hrow'] at hsum_le
  linarith

/-- **The zero-mode removal in `RBM.ThetaZeroMode` is essential.**  `(prop:ThfadC0)` is a
statement about `Θ̊_t`; the same bound for `Θ_t` itself is false at the spectral parameter
`1` -- the `σ₁ ≠ σ₂` case -- because the zero mode `(L^d|1-t|)⁻¹` that `Θ̊` subtracts off
is exactly what diverges as `t → 1`, while the right-hand side stays bounded. -/
theorem not_zeroMode_without_removal (k : ℕ) {g : ℝ} (hg : 0 < g) (τ : ℝ) :
    ¬ ∃ C > (0 : ℝ),
        ∀ (L : ℕ) (_ : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd (k + 2) L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta (k + 2) L g ((t : ℂ) * 1) 0 a‖
            ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
                * (((zdistD (k + 2) L a : ℝ) + 1) ^ (k + 2 - 2))⁻¹ := by
  rintro ⟨C, hC, h⟩
  have : NeZero 3 := ⟨by norm_num⟩
  have hL1 : (1 : ℝ) ≤ ((3 : ℕ) : ℝ) := by norm_num
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  set S : ℝ := Real.exp (Real.sqrt ((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1 * ((3 : ℕ) : ℝ) ^ 2)
    with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    have := radC_pos (one_pos : (0 : ℝ) < 1)
    have := Real.exp_pos (Real.sqrt ((k : ℝ) + 2))
    positivity
  set M : ℝ := C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2)⁻¹ * S with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (0 : ℝ) < ((3 : ℕ) : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set t : ℝ := 1 - 1 / (M + 2) with ht_def
  have hM2 : (0 : ℝ) < M + 2 := by linarith
  have ht0 : 0 ≤ t := by
    rw [ht_def]
    have : 1 / (M + 2) ≤ 1 := by rw [div_le_one hM2]; linarith
    linarith
  have ht1 : t < 1 := by
    rw [ht_def]
    have : 0 < 1 / (M + 2) := by positivity
    linarith
  have h1t : (1 : ℝ) - t = 1 / (M + 2) := by rw [ht_def]; ring
  have hξ : ‖((t : ℂ) * 1)‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]; exact ht1
  have hrow := sum_Theta_row_of_three_le (d := k + 2) (L := 3) (g := g) (by norm_num) hξ 0
  have hrow' : ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ = M + 2 := by
    rw [hrow, mul_one]
    have hcast : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (by
      rw [h1t]; positivity), h1t, one_div, inv_inv]
  have hsum_le : ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ ≤ M := by
    have habs : |1 - t| = 1 - t := abs_of_pos (by linarith)
    calc ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖
        ≤ ∑ b : Zd (k + 2) 3, ‖Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ := norm_sum_le _ _
      _ ≤ ∑ b : Zd (k + 2) 3, C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * (((zdistD (k + 2) 3 b : ℝ) + 1) ^ (k + 2 - 2))⁻¹ :=
          Finset.sum_le_sum fun b _ => h 3 (by norm_num) t ht0 ht1 b
      _ = C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * ∑ b : Zd (k + 2) 3, (((zdistD (k + 2) 3 b : ℝ) + 1) ^ k)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by norm_num
      _ ≤ C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2)⁻¹ * S := by
          have hmono : (g ^ 2 + |1 - t|)⁻¹ ≤ (g ^ 2)⁻¹ :=
            inv_anti₀ hg2 (by have := abs_nonneg (1 - t); linarith)
          have hpos : (0 : ℝ) < C * ((3 : ℕ) : ℝ) ^ τ := by
            have : (0 : ℝ) < ((3 : ℕ) : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) _
            positivity
          have hsum := sum_radial_pow_le (L := 3) k hL1
          calc C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
                * ∑ b : Zd (k + 2) 3, (((zdistD (k + 2) 3 b : ℝ) + 1) ^ k)⁻¹
              ≤ C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2)⁻¹ * S := by
                apply mul_le_mul (mul_le_mul_of_nonneg_left hmono hpos.le) hsum
                  (Finset.sum_nonneg fun b _ => by positivity)
                positivity
      _ = M := by rw [hM]
  rw [hrow'] at hsum_le
  linarith

end RBM.Test
