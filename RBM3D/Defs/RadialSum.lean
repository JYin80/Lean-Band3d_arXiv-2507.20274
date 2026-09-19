/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Factorial.Basic
import RBM3D.Defs.Shells

/-!
# Radial lattice sums with a stretched-exponential cutoff

For `d = k + 2 ≥ 2`, `κ > 0` and `ℓ ≥ 1`,

  `Σ_{x ∈ Z_L^d} (|x|+1)^{-(d-2)} exp(-κ (|x|/ℓ)^{1/2}) ≤ 2^d · C(κ) · ℓ²`,
  `C(κ) = 32 (1 + 720/κ⁶)`                                   (`sum_radial_exp_le`).

This is step K2 of the plan for `lem:propT` (`docs/QUEUE.md`, Q11).  The proof:

1. `sum_radial`: a sum of a function of `|x|` is a sum over spheres, weighted by
   `sphereCard`; with `card_sphere_le` the weight `(r+1)^{d-1}` cancels `(r+1)^{-(d-2)}`
   down to `r + 1`.
2. `succ_mul_exp_le`: termwise, `(r+1) e^{-κ√(r/ℓ)} ≤ C(κ) ℓ³ / ((ℓ+r)(ℓ+r+1))`, from
   `e^y ≥ y⁶/6!` -- no comparison with an integral.
3. `sum_telescope_le`: `Σ_r ℓ/((ℓ+r)(ℓ+r+1)) ≤ 1`, a telescoping sum.

Taking `ℓ = L` (where `|x| ≤ dL` makes the cutoff harmless) gives the `≲ L²` bound used
in regime (ii) of `lem:propT`.
-/

namespace RBM

open Finset Real

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
theorem zdist_le_L (u : ZMod L) : zdist L u ≤ L := by
  simp only [zdist]; omega

omit [NeZero L] in
theorem zdistD_le (d : ℕ) (x : Zd d L) : zdistD d L x ≤ d * L := by
  unfold zdistD
  calc ∑ i, zdist L (x i) ≤ ∑ _i : Fin d, L := sum_le_sum fun i _ => zdist_le_L (x i)
    _ = d * L := by simp

/-- A sum of a function of `|x|` is a sum over spheres. -/
theorem sum_radial (d : ℕ) (F : ℕ → ℝ) :
    ∑ x : Zd d L, F (zdistD d L x) = ∑ r ∈ range (d * L + 1), (sphereCard d L r : ℝ) * F r := by
  have hmaps : ∀ x ∈ (univ : Finset (Zd d L)), zdistD d L x ∈ range (d * L + 1) :=
    fun x _ => mem_range.mpr (Nat.lt_succ_of_le (zdistD_le d x))
  rw [← sum_fiberwise_of_maps_to' hmaps]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_const, nsmul_eq_mul]
  rfl

/-! ### One-dimensional estimates -/

/-- `(1+s)³ e^{-κ√s} ≤ 8 (1 + 720/κ⁶)` for `s ≥ 0`. -/
theorem one_add_pow_three_mul_exp_le {κ : ℝ} (hκ : 0 < κ) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ 3 * exp (-(κ * √s)) ≤ 8 * (1 + 720 / κ ^ 6) := by
  have he : 0 < exp (-(κ * √s)) := exp_pos _
  have hc : 0 ≤ 720 / κ ^ 6 := by positivity
  rcases le_total s 1 with h1 | h1
  · have hA : (1 + s) ^ 3 ≤ 8 := by
      have : 1 + s ≤ 2 := by linarith
      calc (1 + s) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) this 3
        _ = 8 := by norm_num
    have hB : exp (-(κ * √s)) ≤ 1 := exp_le_one_iff.mpr (by
      have := sqrt_nonneg s; nlinarith)
    calc (1 + s) ^ 3 * exp (-(κ * √s)) ≤ 8 * 1 := mul_le_mul hA hB he.le (by norm_num)
      _ ≤ 8 * (1 + 720 / κ ^ 6) := by linarith
  · -- `s ≥ 1`: `(1+s)³ ≤ 8 s³` and `s³ e^{-κ√s} ≤ 720/κ⁶`
    have hA : (1 + s) ^ 3 ≤ 8 * s ^ 3 := by
      have : 1 + s ≤ 2 * s := by linarith
      calc (1 + s) ^ 3 ≤ (2 * s) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
        _ = 8 * s ^ 3 := by ring
    have hy : 0 ≤ κ * √s := by positivity
    have hexp := Real.pow_div_factorial_le_exp _ hy 6
    have hsq : (κ * √s) ^ 6 = κ ^ 6 * s ^ 3 := by
      rw [mul_pow, show (√s) ^ 6 = ((√s) ^ 2) ^ 3 by ring, sq_sqrt hs]
    rw [hsq, show (Nat.factorial 6 : ℝ) = 720 by norm_num [Nat.factorial]] at hexp
    have hκ6 : 0 < κ ^ 6 := by positivity
    have hB : s ^ 3 * exp (-(κ * √s)) ≤ 720 / κ ^ 6 := by
      rw [exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) hκ6]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 720)] at hexp
      linarith
    calc (1 + s) ^ 3 * exp (-(κ * √s)) ≤ 8 * s ^ 3 * exp (-(κ * √s)) :=
          mul_le_mul_of_nonneg_right hA he.le
      _ = 8 * (s ^ 3 * exp (-(κ * √s))) := by ring
      _ ≤ 8 * (720 / κ ^ 6) := by linarith
      _ ≤ 8 * (1 + 720 / κ ^ 6) := by linarith

/-- The constant `C(κ) = 32 (1 + 720/κ⁶)`. -/
noncomputable def radC (κ : ℝ) : ℝ := 32 * (1 + 720 / κ ^ 6)

theorem radC_pos {κ : ℝ} (hκ : 0 < κ) : 0 < radC κ := by
  unfold radC; positivity

/-- Termwise: `(r+1) e^{-κ√(r/ℓ)} ≤ C(κ) ℓ³ / ((ℓ+r)(ℓ+r+1))` for `ℓ ≥ 1`. -/
theorem succ_mul_exp_le {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 1 ≤ ℓ) (r : ℕ) :
    ((r : ℝ) + 1) * exp (-(κ * √((r : ℝ) / ℓ)))
      ≤ radC κ * ℓ ^ 3 / ((ℓ + r) * (ℓ + r + 1)) := by
  have hℓ0 : 0 < ℓ := by linarith
  set s : ℝ := (r : ℝ) / ℓ with hs
  have hs0 : 0 ≤ s := by positivity
  have hr : (r : ℝ) = s * ℓ := by rw [hs, div_mul_cancel₀ _ hℓ0.ne']
  have hD : 0 < (ℓ + r) * (ℓ + r + 1) := by positivity
  rw [le_div_iff₀ hD]
  have h1 : (r : ℝ) + 1 ≤ (1 + s) * ℓ := by rw [hr]; nlinarith
  have h2 : (ℓ + r) * (ℓ + r + 1) ≤ (2 * (1 + s) * ℓ) ^ 2 := by
    rw [hr]; nlinarith
  have hkey := one_add_pow_three_mul_exp_le hκ hs0
  have he : 0 < exp (-(κ * √s)) := exp_pos _
  calc ((r : ℝ) + 1) * exp (-(κ * √s)) * ((ℓ + r) * (ℓ + r + 1))
      ≤ ((1 + s) * ℓ) * exp (-(κ * √s)) * (2 * (1 + s) * ℓ) ^ 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 he.le) h2 hD.le
        exact mul_nonneg (by positivity) he.le
    _ = 4 * ℓ ^ 3 * ((1 + s) ^ 3 * exp (-(κ * √s))) := by ring
    _ ≤ 4 * ℓ ^ 3 * (8 * (1 + 720 / κ ^ 6)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = radC κ * ℓ ^ 3 := by unfold radC; ring

/-- `Σ_{r<R} ℓ/((ℓ+r)(ℓ+r+1)) ≤ 1`: a telescoping sum. -/
theorem sum_telescope_le {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℕ) :
    ∑ r ∈ range R, ℓ / ((ℓ + r) * (ℓ + r + 1)) ≤ 1 := by
  have hterm : ∀ r : ℕ, ℓ / ((ℓ + r) * (ℓ + r + 1))
      = ℓ * (1 / (ℓ + r)) - ℓ * (1 / (ℓ + ((r + 1 : ℕ) : ℝ))) := by
    intro r
    have h1 : 0 < ℓ + r := by positivity
    push_cast
    field_simp
    ring
  simp only [hterm]
  rw [sum_range_sub' (fun r : ℕ => ℓ * (1 / (ℓ + (r : ℝ)))) R]
  simp only [Nat.cast_zero, add_zero]
  have h0 : ℓ * (1 / ℓ) = 1 := by field_simp
  have hR : 0 ≤ ℓ * (1 / (ℓ + R)) := by positivity
  linarith

/-- `Σ_{r<R} (r+1) e^{-κ√(r/ℓ)} ≤ C(κ) ℓ²` for `ℓ ≥ 1`, uniformly in `R`. -/
theorem sum_succ_mul_exp_le {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 1 ≤ ℓ) (R : ℕ) :
    ∑ r ∈ range R, ((r : ℝ) + 1) * exp (-(κ * √((r : ℝ) / ℓ))) ≤ radC κ * ℓ ^ 2 := by
  have hℓ0 : 0 < ℓ := by linarith
  calc ∑ r ∈ range R, ((r : ℝ) + 1) * exp (-(κ * √((r : ℝ) / ℓ)))
      ≤ ∑ r ∈ range R, radC κ * ℓ ^ 3 / ((ℓ + r) * (ℓ + r + 1)) :=
        sum_le_sum fun r _ => succ_mul_exp_le hκ hℓ r
    _ = radC κ * ℓ ^ 2 * ∑ r ∈ range R, ℓ / ((ℓ + r) * (ℓ + r + 1)) := by
        rw [mul_sum]
        refine sum_congr rfl fun r _ => ?_
        ring
    _ ≤ radC κ * ℓ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (sum_telescope_le hℓ0 R) (by
          have := radC_pos hκ; positivity)
    _ = radC κ * ℓ ^ 2 := mul_one _

/-! ### The radial sum -/

/-- **K2.** For `d = k + 2`, `κ > 0`, `ℓ ≥ 1`:
`Σ_{x ∈ Z_L^d} (|x|+1)^{-(d-2)} e^{-κ√(|x|/ℓ)} ≤ 2^d C(κ) ℓ²`. -/
theorem sum_radial_exp_le (k : ℕ) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 1 ≤ ℓ) :
    ∑ x : Zd (k + 2) L, (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
        * exp (-(κ * √((zdistD (k + 2) L x : ℝ) / ℓ)))
      ≤ 2 ^ (k + 2) * radC κ * ℓ ^ 2 := by
  rw [sum_radial (k + 2) (fun r : ℕ => (((r : ℝ) + 1) ^ k)⁻¹ * exp (-(κ * √((r : ℝ) / ℓ))))]
  calc ∑ r ∈ range ((k + 2) * L + 1),
        (sphereCard (k + 2) L r : ℝ) * ((((r : ℝ) + 1) ^ k)⁻¹ * exp (-(κ * √((r : ℝ) / ℓ))))
      ≤ ∑ r ∈ range ((k + 2) * L + 1),
        (2 : ℝ) ^ (k + 2) * (((r : ℝ) + 1) * exp (-(κ * √((r : ℝ) / ℓ)))) := by
        refine sum_le_sum fun r _ => ?_
        have hc : (sphereCard (k + 2) L r : ℝ) ≤ 2 ^ (k + 2) * ((r : ℝ) + 1) ^ (k + 1) := by
          exact_mod_cast card_sphere_le (L := L) (k + 1) r
        have hpos : 0 < ((r : ℝ) + 1) ^ k := by positivity
        have he : 0 ≤ exp (-(κ * √((r : ℝ) / ℓ))) := (exp_pos _).le
        calc (sphereCard (k + 2) L r : ℝ) * ((((r : ℝ) + 1) ^ k)⁻¹ * exp (-(κ * √((r : ℝ) / ℓ))))
            ≤ (2 ^ (k + 2) * ((r : ℝ) + 1) ^ (k + 1))
                * ((((r : ℝ) + 1) ^ k)⁻¹ * exp (-(κ * √((r : ℝ) / ℓ)))) :=
              mul_le_mul_of_nonneg_right hc (mul_nonneg (inv_nonneg.mpr hpos.le) he)
          _ = (2 : ℝ) ^ (k + 2) * (((r : ℝ) + 1) * exp (-(κ * √((r : ℝ) / ℓ)))) := by
              field_simp
              ring
    _ = (2 : ℝ) ^ (k + 2) * ∑ r ∈ range ((k + 2) * L + 1),
          ((r : ℝ) + 1) * exp (-(κ * √((r : ℝ) / ℓ))) := by rw [mul_sum]
    _ ≤ (2 : ℝ) ^ (k + 2) * (radC κ * ℓ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_succ_mul_exp_le hκ hℓ _) (by positivity)
    _ = 2 ^ (k + 2) * radC κ * ℓ ^ 2 := by ring

end RBM
