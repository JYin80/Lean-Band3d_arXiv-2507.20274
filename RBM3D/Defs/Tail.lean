/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RBM3D.Defs.Params

/-!
# The tail functions `𝒯_t` and `wT^ℓ_{t,D}`

`\Cref{def: TTfunc}` (Section 3):

* `(defTUL)`   `𝒯_t(r) := B_{t,r} · exp(-(r/ℓ_t)^{1/2})`, `r ≥ 0`;
* `(defWTTlD)` `wT^ℓ_{t,D}(r) := max(𝒯_t(r ∧ ℓ), W^{-D})`, `0 ≤ ℓ ≤ L`.

`𝒯_t` takes a real argument (it is evaluated at `r ∧ ℓ` with `ℓ` real), so this file uses
`RBM.BparamR`, the profile `B_{t,r}` of `(eq_B_param)` at real `r`; `BparamR_natCast`
identifies it with `RBM.Bparam` at natural `r`.  As in `Defs/Params.lean`, the square
root is `Real.sqrt` and `(r+1)^{d-2}` is a natural power; `W^{-D}` is `Real.rpow`.

## What the paper takes as evident, proved here

* `𝒯_t ≥ 0`, `𝒯_t(0) = B_{t,0}`, and `𝒯_t` is non-increasing on `[0, ∞)` (`tailT_antitone`);
* `wT ≥ W^{-D} > 0` and `wT` is non-increasing on `[0, ∞)`;
* the remark after `def: TTfunc` (L325), in two halves:
  - `zeroMode_le_of_ge`: for `0 ≤ r ≤ L` and `1 - t ≥ g²/L²`, the zero-mode term
    `(L^d|1-t|)⁻¹` of `B_{t,r}` is dominated by the decay term,
    `(L^d|1-t|)⁻¹ ≤ 2^{d-1} (g²+|1-t|)⁻¹ (r+1)^{-(d-2)}`;
  - `ellT_eq_of_le` / `exp_tail_ge`: for `1 - t ≤ g²/L²`, `ℓ_t = L`, and the exponential
    factor of `𝒯_t(r)` is at least `e⁻¹` for `0 ≤ r ≤ L`.
  The paper says "dominated" and "of constant order"; the constants `2^{d-1}` and `e⁻¹`
  are what the argument gives.
-/

namespace RBM

open Real

variable (d L : ℕ) (g t : ℝ)

/-- `B_{t,r}` of `(eq_B_param)` at a real argument `r`. -/
noncomputable def BparamR (r : ℝ) : ℝ :=
  (g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹

/-- `(defTUL)`: the tail function `𝒯_t(r) = B_{t,r} exp(-(r/ℓ_t)^{1/2})`. -/
noncomputable def tailT (r : ℝ) : ℝ :=
  BparamR d L g t r * Real.exp (-Real.sqrt (r / ellT L g t))

/-- `(defWTTlD)`: the truncated tail function `wT^ℓ_{t,D}(r) = max(𝒯_t(r ∧ ℓ), W^{-D})`. -/
noncomputable def tailW (ℓ W D r : ℝ) : ℝ :=
  max (tailT d L g t (min r ℓ)) (W ^ (-D))

variable {d L g t}

theorem BparamR_natCast (K : ℕ) : BparamR d L g t K = Bparam d L g t K := by
  simp [BparamR, Bparam]

theorem ellT_nonneg : 0 ≤ ellT L g t :=
  le_min (zero_le_one.trans (le_max_right _ _)) (Nat.cast_nonneg L)

theorem BparamR_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ BparamR d L g t r := by
  unfold BparamR
  have h1 : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
  have h2 : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) _)
  have h3 : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
  exact add_nonneg (mul_nonneg h1 h2) h3

/-- `B_{t,r}` is non-increasing in `r ≥ 0`. -/
theorem BparamR_antitone {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ ≤ r₂) :
    BparamR d L g t r₂ ≤ BparamR d L g t r₁ := by
  unfold BparamR
  have hpow : (r₁ + 1) ^ (d - 2) ≤ (r₂ + 1) ^ (d - 2) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hinv : ((r₂ + 1) ^ (d - 2))⁻¹ ≤ ((r₁ + 1) ^ (d - 2))⁻¹ :=
    inv_anti₀ (pow_pos (by linarith) _) hpow
  have hc : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
  linarith [mul_le_mul_of_nonneg_left hinv hc]

theorem tailT_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ tailT d L g t r :=
  mul_nonneg (BparamR_nonneg hr) (Real.exp_pos _).le

theorem tailT_zero : tailT d L g t 0 = Bparam d L g t 0 := by
  simp [tailT, ← BparamR_natCast]

/-- `𝒯_t` is non-increasing on `[0, ∞)`. -/
theorem tailT_antitone {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ ≤ r₂) :
    tailT d L g t r₂ ≤ tailT d L g t r₁ := by
  unfold tailT
  have hexp : Real.exp (-Real.sqrt (r₂ / ellT L g t)) ≤ Real.exp (-Real.sqrt (r₁ / ellT L g t)) :=
    Real.exp_le_exp.mpr (neg_le_neg (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right h ellT_nonneg)))
  exact mul_le_mul (BparamR_antitone hr₁ h) hexp (Real.exp_pos _).le
    (BparamR_nonneg hr₁)

section Truncated

variable {ℓ W D : ℝ}

theorem rpow_neg_le_tailW (r : ℝ) : W ^ (-D) ≤ tailW d L g t ℓ W D r :=
  le_max_right _ _

/-- `wT ≥ W^{-D} > 0`: every division by `wT` in the paper is legitimate. -/
theorem tailW_pos (hW : 0 < W) (r : ℝ) : 0 < tailW d L g t ℓ W D r :=
  (Real.rpow_pos_of_pos hW _).trans_le (rpow_neg_le_tailW r)

/-- `wT^ℓ_{t,D}` is non-increasing on `[0, ∞)`. -/
theorem tailW_antitone (hℓ : 0 ≤ ℓ) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ ≤ r₂) :
    tailW d L g t ℓ W D r₂ ≤ tailW d L g t ℓ W D r₁ :=
  max_le_max (tailT_antitone (le_min hr₁ hℓ) (min_le_min_right ℓ h)) le_rfl

end Truncated

/-! ### The remark after `def: TTfunc` -/

/-- For `0 ≤ r ≤ L` and `1 - t ≥ g²/L²`, the zero-mode term of `B_{t,r}` is dominated by the
decay term: `(L^d|1-t|)⁻¹ ≤ 2^{d-1} (g²+|1-t|)⁻¹ (r+1)^{-(d-2)}`. -/
theorem zeroMode_le_of_ge (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hrL : r ≤ L) (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) :
    ((L : ℝ) ^ d * |1 - t|)⁻¹ ≤ 2 ^ (d - 1) * ((g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  simp only [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega]
  set u := 1 - t with hu
  have hu0 : 0 < u := by linarith
  rw [abs_of_pos hu0]
  have hL0 : 0 < (L : ℝ) := by linarith
  have hg2 : g ^ 2 ≤ (L : ℝ) ^ 2 * u := by
    rw [div_le_iff₀ (by positivity)] at hgt; linarith
  have hL2 : 1 ≤ (L : ℝ) ^ 2 := by nlinarith
  have huL : u ≤ (L : ℝ) ^ 2 * u := le_mul_of_one_le_left hu0.le hL2
  have hA : g ^ 2 + u ≤ 2 * (L : ℝ) ^ 2 * u := by linarith
  have hB : (r + 1) ^ k ≤ (2 * (L : ℝ)) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) _
  have hP0 : 0 < (g ^ 2 + u) * (r + 1) ^ k := by positivity
  have hP : (g ^ 2 + u) * (r + 1) ^ k ≤ 2 ^ (k + 1) * ((L : ℝ) ^ (k + 2) * u) := by
    calc (g ^ 2 + u) * (r + 1) ^ k ≤ (2 * (L : ℝ) ^ 2 * u) * (2 * (L : ℝ)) ^ k :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = 2 ^ (k + 1) * ((L : ℝ) ^ (k + 2) * u) := by ring
  rw [← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) hP0]
  linarith

/-- For `1 - t ≤ g²/L²` (with `g ≥ 0`, `t < 1`, `L ≥ 1`), the range saturates: `ℓ_t = L`. -/
theorem ellT_eq_of_le (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ (L : ℝ))
    (h : 1 - t ≤ g ^ 2 / (L : ℝ) ^ 2) : ellT L g t = L := by
  have hu0 : 0 < 1 - t := by linarith
  have hL0 : 0 < (L : ℝ) := by linarith
  have hsq : 0 < Real.sqrt |1 - t| := Real.sqrt_pos.mpr (by rw [abs_of_pos hu0]; exact hu0)
  have hkey : (L : ℝ) ≤ g / Real.sqrt |1 - t| := by
    rw [le_div_iff₀ hsq, abs_of_pos hu0]
    have h2 : (L : ℝ) ^ 2 * (1 - t) ≤ g ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at h; linarith
    have h3 : Real.sqrt ((L : ℝ) ^ 2 * (1 - t)) ≤ Real.sqrt (g ^ 2) := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hL0.le, Real.sqrt_sq hg] at h3
  exact min_eq_right (le_max_of_le_left hkey)

/-- In the same regime the exponential factor of `𝒯_t(r)` is of constant order:
`exp(-(r/ℓ_t)^{1/2}) ≥ e⁻¹` for `r ≤ L` (the paper has `0 ≤ r ≤ L`; `r ≥ 0` is not needed). -/
theorem exp_tail_ge (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ (L : ℝ))
    (h : 1 - t ≤ g ^ 2 / (L : ℝ) ^ 2) {r : ℝ} (hrL : r ≤ L) :
    Real.exp (-1) ≤ Real.exp (-Real.sqrt (r / ellT L g t)) := by
  rw [ellT_eq_of_le hg ht hL h]
  have hL0 : 0 < (L : ℝ) := by linarith
  have h1 : r / (L : ℝ) ≤ 1 := (div_le_one hL0).mpr hrL
  have h2 : Real.sqrt (r / (L : ℝ)) ≤ 1 := by
    calc Real.sqrt (r / (L : ℝ)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  exact Real.exp_le_exp.mpr (neg_le_neg h2)

end RBM
