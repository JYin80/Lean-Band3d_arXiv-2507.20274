/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.RadialSum

/-!
# The convolution estimate behind `lem:propT`

Write `P(x) = (|x|+1)^{-(d-2)}` and `E_ℓ(x) = exp(-(|x|/ℓ)^{1/2})`.  For `1 ≤ ℓ₁ ≤ ℓ₂`,

  `Σ_c P(a-c) E_{ℓ₁}(a-c) · P(c-b) E_{ℓ₂}(c-b) ≤ C_d ℓ₁² · P(a-b) E_{ℓ₂}(a-b)`
                                                              (`sum_conv_le`).

This is step K3 of the plan for `lem:propT` (`docs/QUEUE.md`, Q11), the lattice
version of the "basic calculus fact" that Appendix A.3 states on `ℝ^d` without proof.
Regime (i) of `lem:propT` uses it with `ℓ₁ = ℓ_u ≤ ℓ₂ = ℓ_t`, regime (ii) with
`ℓ₁ = ℓ₂ = L`.

The proof is pointwise in `c`, then K2:

* `sqrt_add_sqrt_sub_ge`: for `r ≤ p + q`,
  `√(p/ℓ₁) + √(q/ℓ₂) - √(r/ℓ₂) ≥ (2-√2) √(min(p,q)/ℓ₁)`.  With `p = |a-c|`, `q = |c-b|`,
  `r = |a-b|` this is where the triangle inequality enters; it holds for every
  `ℓ₁ ≤ ℓ₂`, i.e. for every `ε = (ℓ₁/ℓ₂)^{1/2} ∈ (0,1]` in the paper's notation.
* whichever of `|a-c|`, `|c-b|` is larger is at least `|a-b|/2`, so its `P` factor is at
  most `2^{d-2} P(a-b)`;
* what remains is `P(x) e^{-(2-√2)√(|x|/ℓ₁)}` summed over `x`, which is K2.
-/

namespace RBM

open Finset Real

/-! ### A square-root inequality -/

/-- `x + y - √(x² + y²) ≥ (2 - √2) min(x, y)` for `x, y ≥ 0`. -/
theorem add_sub_sqrt_sq_add_sq_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (2 - √2) * min x y ≤ x + y - √(x ^ 2 + y ^ 2) := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h2' : 1 ≤ √2 := by
    rw [show (1 : ℝ) = √1 by rw [sqrt_one]]; exact sqrt_le_sqrt (by norm_num)
  have h2'' : √2 ≤ 2 := by nlinarith
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy]
    have hb : 0 ≤ y + (√2 - 1) * x := by nlinarith
    have : √(x ^ 2 + y ^ 2) ≤ y + (√2 - 1) * x := by
      rw [sqrt_le_left hb]
      have e : (y + (√2 - 1) * x) ^ 2
          = x ^ 2 + y ^ 2 + 2 * ((√2 - 1) * x * (y - x)) + (√2 ^ 2 - 2) * x ^ 2 := by ring
      rw [e, h2]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h2') hx) (sub_nonneg.mpr hxy)]
    linarith
  · rw [min_eq_right hxy]
    have hb : 0 ≤ x + (√2 - 1) * y := by nlinarith
    have : √(x ^ 2 + y ^ 2) ≤ x + (√2 - 1) * y := by
      rw [sqrt_le_left hb]
      have e : (x + (√2 - 1) * y) ^ 2
          = x ^ 2 + y ^ 2 + 2 * ((√2 - 1) * y * (x - y)) + (√2 ^ 2 - 2) * y ^ 2 := by ring
      rw [e, h2]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h2') hy) (sub_nonneg.mpr hxy)]
    linarith

/-- The exponent inequality: for `r ≤ p + q` and `0 < ℓ₁ ≤ ℓ₂`,
`√(p/ℓ₁) + √(q/ℓ₂) - √(r/ℓ₂) ≥ (2-√2) √(min(p,q)/ℓ₁)`. -/
theorem sqrt_add_sqrt_sub_ge {p q r ℓ₁ ℓ₂ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpqr : r ≤ p + q) (hℓ₁ : 0 < ℓ₁) (hℓ : ℓ₁ ≤ ℓ₂) :
    (2 - √2) * √(min p q / ℓ₁) ≤ √(p / ℓ₁) + √(q / ℓ₂) - √(r / ℓ₂) := by
  have hℓ₂ : 0 < ℓ₂ := hℓ₁.trans_le hℓ
  have s₁ : 0 < √ℓ₁ := sqrt_pos.mpr hℓ₁
  have s₂ : 0 < √ℓ₂ := sqrt_pos.mpr hℓ₂
  have s12 : √ℓ₁ ≤ √ℓ₂ := sqrt_le_sqrt hℓ
  simp only [sqrt_div' _ hℓ₁.le, sqrt_div' _ hℓ₂.le]
  have hκ : 0 ≤ 2 - √2 := by
    have : √2 ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt (by norm_num)
    linarith
  have hκ1 : 2 - √2 ≤ 1 := by
    have : (1 : ℝ) ≤ √2 := by
      rw [show (1 : ℝ) = √1 by rw [sqrt_one]]; exact sqrt_le_sqrt (by norm_num)
    linarith
  have hmin : √(min p q) = min (√p) (√q) := by
    rcases le_total p q with h | h
    · rw [min_eq_left h, min_eq_left (sqrt_le_sqrt h)]
    · rw [min_eq_right h, min_eq_right (sqrt_le_sqrt h)]
  rw [hmin]
  rcases le_total r q with hrq | hrq
  · -- `q ≥ r`: the last two terms are non-negative together
    have h1 : √r / √ℓ₂ ≤ √q / √ℓ₂ := div_le_div_of_nonneg_right (sqrt_le_sqrt hrq) s₂.le
    have h2 : (2 - √2) * (min (√p) (√q) / √ℓ₁) ≤ √p / √ℓ₁ := by
      calc (2 - √2) * (min (√p) (√q) / √ℓ₁) ≤ 1 * (min (√p) (√q) / √ℓ₁) :=
            mul_le_mul_of_nonneg_right hκ1 (div_nonneg (le_min (sqrt_nonneg _) (sqrt_nonneg _))
              s₁.le)
        _ ≤ √p / √ℓ₁ := by
            rw [one_mul]; exact div_le_div_of_nonneg_right (min_le_left _ _) s₁.le
    rw [mul_div_assoc']
    rw [mul_div_assoc'] at h2
    linarith
  · -- `q ≤ r`: replace `√ℓ₂` by the smaller `√ℓ₁`, then use the square-root inequality
    have hneg : √q - √r ≤ 0 := by linarith [sqrt_le_sqrt hrq]
    have h1 : (√q - √r) / √ℓ₁ ≤ (√q - √r) / √ℓ₂ := by
      rw [div_le_div_iff₀ s₁ s₂]
      exact mul_le_mul_of_nonpos_left s12 hneg
    have hZ : √r ≤ √(√p ^ 2 + √q ^ 2) := by
      rw [sq_sqrt hp, sq_sqrt hq]; exact sqrt_le_sqrt hpqr
    have hkey := add_sub_sqrt_sq_add_sq_ge (sqrt_nonneg p) (sqrt_nonneg q)
    have h3 : (2 - √2) * min (√p) (√q) ≤ √p + √q - √r := by linarith
    have h4 : (2 - √2) * min (√p) (√q) / √ℓ₁ ≤ (√p + √q - √r) / √ℓ₁ :=
      div_le_div_of_nonneg_right h3 s₁.le
    have h5 : (√p + √q - √r) / √ℓ₁ = √p / √ℓ₁ + (√q - √r) / √ℓ₁ := by ring
    have h6 : √q / √ℓ₂ - √r / √ℓ₂ = (√q - √r) / √ℓ₂ := by ring
    rw [mul_div_assoc']
    linarith

/-! ### The pointwise bound -/

variable {L : ℕ} [NeZero L]

/-- `P(x) = (|x|+1)^{-k}` as a real function of the distance. -/
noncomputable def powW (k r : ℕ) : ℝ := (((r : ℝ) + 1) ^ k)⁻¹

theorem powW_nonneg (k r : ℕ) : 0 ≤ powW k r := by unfold powW; positivity

/-- If `r ≤ 2 q` then `P(q) ≤ 2^k P(r)`. -/
theorem powW_le_of_le_two_mul {k q r : ℕ} (h : r ≤ 2 * q) : powW k q ≤ 2 ^ k * powW k r := by
  unfold powW
  have h' : (r : ℝ) + 1 ≤ 2 * ((q : ℝ) + 1) := by
    have : (r : ℝ) ≤ 2 * q := by exact_mod_cast h
    linarith
  have h1 : ((r : ℝ) + 1) ^ k ≤ 2 ^ k * ((q : ℝ) + 1) ^ k := by
    calc ((r : ℝ) + 1) ^ k ≤ (2 * ((q : ℝ) + 1)) ^ k := pow_le_pow_left₀ (by positivity) h' k
      _ = 2 ^ k * ((q : ℝ) + 1) ^ k := mul_pow _ _ _
  rw [show (2 : ℝ) ^ k * (((r : ℝ) + 1) ^ k)⁻¹ = (((r : ℝ) + 1) ^ k / 2 ^ k)⁻¹ by
    rw [inv_div]; ring]
  apply inv_anti₀ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The constant `κ₀ = 2 - √2` of the exponent inequality. -/
noncomputable def κ₀ : ℝ := 2 - √2

theorem κ₀_pos : 0 < κ₀ := by
  unfold κ₀
  have : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- The pointwise bound: the summand of the convolution at `c` is at most
`2^k P(a-b) E_{ℓ₂}(a-b)` times `P(x) e^{-κ₀√(|x|/ℓ₁)}` at `x = a - c` or at `x = c - b`. -/
theorem conv_term_le (d k : ℕ) {ℓ₁ ℓ₂ : ℝ} (hℓ₁ : 0 < ℓ₁) (hℓ : ℓ₁ ≤ ℓ₂) (a b c : Zd d L) :
    powW k (zdistD d L (a - c)) * exp (-√((zdistD d L (a - c) : ℝ) / ℓ₁))
        * (powW k (zdistD d L (c - b)) * exp (-√((zdistD d L (c - b) : ℝ) / ℓ₂)))
      ≤ 2 ^ k * (powW k (zdistD d L (a - b)) * exp (-√((zdistD d L (a - b) : ℝ) / ℓ₂)))
        * (powW k (zdistD d L (a - c)) * exp (-(κ₀ * √((zdistD d L (a - c) : ℝ) / ℓ₁)))
          + powW k (zdistD d L (c - b)) * exp (-(κ₀ * √((zdistD d L (c - b) : ℝ) / ℓ₁)))) := by
  set p := zdistD d L (a - c)
  set q := zdistD d L (c - b)
  set r := zdistD d L (a - b)
  have htri : r ≤ p + q := by
    have := zdistD_add_le d L (a - c) (c - b)
    rwa [sub_add_sub_cancel] at this
  have htri' : (r : ℝ) ≤ p + q := by exact_mod_cast htri
  have hexp := sqrt_add_sqrt_sub_ge (Nat.cast_nonneg p) (Nat.cast_nonneg q) htri' hℓ₁ hℓ
  -- the exponential factors: `E₁(p) E₂(q) ≤ E₂(r) e^{-κ₀ √(min(p,q)/ℓ₁)}`
  have hE : exp (-√((p : ℝ) / ℓ₁)) * exp (-√((q : ℝ) / ℓ₂))
      ≤ exp (-√((r : ℝ) / ℓ₂)) * exp (-(κ₀ * √(min (p : ℝ) q / ℓ₁))) := by
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    unfold κ₀
    linarith
  have hPa := powW_nonneg k p
  have hPb := powW_nonneg k q
  have hPr := powW_nonneg k r
  have hEr := (exp_pos (-√((r : ℝ) / ℓ₂))).le
  rcases le_total p q with hpq | hpq
  · -- `|a-c| ≤ |c-b|`: then `|c-b| ≥ |a-b|/2`
    have hq2 : powW k q ≤ 2 ^ k * powW k r := powW_le_of_le_two_mul (by omega)
    have hmin : min (p : ℝ) q = p := min_eq_left (by exact_mod_cast hpq)
    rw [hmin] at hE
    have hEp := (exp_pos (-(κ₀ * √((p : ℝ) / ℓ₁)))).le
    have hEq := (exp_pos (-(κ₀ * √((q : ℝ) / ℓ₁)))).le
    calc powW k p * exp (-√((p : ℝ) / ℓ₁)) * (powW k q * exp (-√((q : ℝ) / ℓ₂)))
        = powW k p * powW k q * (exp (-√((p : ℝ) / ℓ₁)) * exp (-√((q : ℝ) / ℓ₂))) := by ring
      _ ≤ powW k p * (2 ^ k * powW k r)
            * (exp (-√((r : ℝ) / ℓ₂)) * exp (-(κ₀ * √((p : ℝ) / ℓ₁)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hq2 hPa) hE
            (mul_nonneg (exp_pos _).le (exp_pos _).le) (by positivity)
      _ = 2 ^ k * (powW k r * exp (-√((r : ℝ) / ℓ₂)))
            * (powW k p * exp (-(κ₀ * √((p : ℝ) / ℓ₁)))) := by ring
      _ ≤ 2 ^ k * (powW k r * exp (-√((r : ℝ) / ℓ₂)))
            * (powW k p * exp (-(κ₀ * √((p : ℝ) / ℓ₁)))
              + powW k q * exp (-(κ₀ * √((q : ℝ) / ℓ₁)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [mul_nonneg hPb hEq]
  · -- `|c-b| ≤ |a-c|`: then `|a-c| ≥ |a-b|/2`
    have hp2 : powW k p ≤ 2 ^ k * powW k r := powW_le_of_le_two_mul (by omega)
    have hmin : min (p : ℝ) q = q := min_eq_right (by exact_mod_cast hpq)
    rw [hmin] at hE
    have hEp := (exp_pos (-(κ₀ * √((p : ℝ) / ℓ₁)))).le
    have hEq := (exp_pos (-(κ₀ * √((q : ℝ) / ℓ₁)))).le
    calc powW k p * exp (-√((p : ℝ) / ℓ₁)) * (powW k q * exp (-√((q : ℝ) / ℓ₂)))
        = powW k p * powW k q * (exp (-√((p : ℝ) / ℓ₁)) * exp (-√((q : ℝ) / ℓ₂))) := by ring
      _ ≤ (2 ^ k * powW k r) * powW k q
            * (exp (-√((r : ℝ) / ℓ₂)) * exp (-(κ₀ * √((q : ℝ) / ℓ₁)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hp2 hPb) hE
            (mul_nonneg (exp_pos _).le (exp_pos _).le) (by positivity)
      _ = 2 ^ k * (powW k r * exp (-√((r : ℝ) / ℓ₂)))
            * (powW k q * exp (-(κ₀ * √((q : ℝ) / ℓ₁)))) := by ring
      _ ≤ 2 ^ k * (powW k r * exp (-√((r : ℝ) / ℓ₂)))
            * (powW k p * exp (-(κ₀ * √((p : ℝ) / ℓ₁)))
              + powW k q * exp (-(κ₀ * √((q : ℝ) / ℓ₁)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [mul_nonneg hPa hEp]

/-! ### Summing over `c` -/

/-- The convolution constant `C = 2^{k+1} · 2^{k+2} · C(κ₀)`. -/
noncomputable def convC (k : ℕ) : ℝ := 2 ^ (k + 1) * (2 ^ (k + 2) * radC κ₀)

/-- **K3.** For `d = k + 2` and `1 ≤ ℓ₁ ≤ ℓ₂`:
`Σ_c P(a-c) E_{ℓ₁}(a-c) · P(c-b) E_{ℓ₂}(c-b) ≤ C ℓ₁² · P(a-b) E_{ℓ₂}(a-b)`. -/
theorem sum_conv_le (k : ℕ) {ℓ₁ ℓ₂ : ℝ} (hℓ₁ : 1 ≤ ℓ₁) (hℓ : ℓ₁ ≤ ℓ₂) (a b : Zd (k + 2) L) :
    ∑ c : Zd (k + 2) L,
        powW k (zdistD (k + 2) L (a - c)) * exp (-√((zdistD (k + 2) L (a - c) : ℝ) / ℓ₁))
          * (powW k (zdistD (k + 2) L (c - b)) * exp (-√((zdistD (k + 2) L (c - b) : ℝ) / ℓ₂)))
      ≤ convC k * ℓ₁ ^ 2
          * (powW k (zdistD (k + 2) L (a - b))
            * exp (-√((zdistD (k + 2) L (a - b) : ℝ) / ℓ₂))) := by
  have hℓ₁0 : 0 < ℓ₁ := by linarith
  set F : Zd (k + 2) L → ℝ := fun x =>
    powW k (zdistD (k + 2) L x) * exp (-(κ₀ * √((zdistD (k + 2) L x : ℝ) / ℓ₁)))
  set R := powW k (zdistD (k + 2) L (a - b)) * exp (-√((zdistD (k + 2) L (a - b) : ℝ) / ℓ₂))
  have hR : 0 ≤ R := mul_nonneg (powW_nonneg _ _) (exp_pos _).le
  have hK2 : ∑ x, F x ≤ 2 ^ (k + 2) * radC κ₀ * ℓ₁ ^ 2 := sum_radial_exp_le k κ₀_pos hℓ₁
  have hA : ∑ c : Zd (k + 2) L, F (a - c) = ∑ x, F x :=
    Fintype.sum_equiv (Equiv.subLeft a) _ _ fun c => rfl
  have hB : ∑ c : Zd (k + 2) L, F (c - b) = ∑ x, F x :=
    Fintype.sum_equiv (Equiv.subRight b) _ _ fun c => rfl
  calc _ ≤ ∑ c : Zd (k + 2) L, 2 ^ k * R * (F (a - c) + F (c - b)) :=
        sum_le_sum fun c _ => conv_term_le (k + 2) k hℓ₁0 hℓ a b c
    _ = 2 ^ k * R * (∑ c : Zd (k + 2) L, F (a - c) + ∑ c : Zd (k + 2) L, F (c - b)) := by
        rw [← mul_sum, sum_add_distrib]
    _ = 2 ^ k * R * (2 * ∑ x, F x) := by rw [hA, hB]; ring
    _ ≤ 2 ^ k * R * (2 * (2 ^ (k + 2) * radC κ₀ * ℓ₁ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = convC k * ℓ₁ ^ 2 * R := by unfold convC; ring

end RBM
