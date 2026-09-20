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

/-- The radial sum without a cutoff: on the torus `|x| ≤ dL`, so the stretched
exponential of K2 costs only a constant. -/
theorem sum_radial_pow_le (k : ℕ) (hL : 1 ≤ (L : ℝ)) :
    ∑ x : Zd (k + 2) L, (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
      ≤ exp (√((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1 * (L : ℝ) ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hstep : ∀ x : Zd (k + 2) L, (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
      ≤ exp (√((k : ℝ) + 2)) * ((((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
        * exp (-(1 * √((zdistD (k + 2) L x : ℝ) / L)))) := by
    intro x
    have hx : ((zdistD (k + 2) L x : ℝ)) / L ≤ (k : ℝ) + 2 := by
      rw [div_le_iff₀ hL0]
      have : ((zdistD (k + 2) L x : ℕ) : ℝ) ≤ ((k + 2) * L : ℕ) := by
        exact_mod_cast zdistD_le (k + 2) x
      push_cast at this
      linarith
    have hsq : √((zdistD (k + 2) L x : ℝ) / L) ≤ √((k : ℝ) + 2) := sqrt_le_sqrt hx
    have hexp : exp (-√((k : ℝ) + 2)) ≤ exp (-(1 * √((zdistD (k + 2) L x : ℝ) / L))) := by
      rw [one_mul]
      exact exp_le_exp.mpr (neg_le_neg hsq)
    have hinv : (0 : ℝ) ≤ (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹ := by positivity
    have hcancel : exp (√((k : ℝ) + 2)) * exp (-√((k : ℝ) + 2)) = 1 := by
      rw [← exp_add]; simp
    calc (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
        = exp (√((k : ℝ) + 2)) * (exp (-√((k : ℝ) + 2))
            * (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹) := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ exp (√((k : ℝ) + 2)) * ((((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
            * exp (-(1 * √((zdistD (k + 2) L x : ℝ) / L)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hexp hinv
  calc ∑ x : Zd (k + 2) L, (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
      ≤ ∑ x : Zd (k + 2) L, exp (√((k : ℝ) + 2)) * ((((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
          * exp (-(1 * √((zdistD (k + 2) L x : ℝ) / L)))) := sum_le_sum fun x _ => hstep x
    _ = exp (√((k : ℝ) + 2)) * ∑ x : Zd (k + 2) L, (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
          * exp (-(1 * √((zdistD (k + 2) L x : ℝ) / L))) := by rw [Finset.mul_sum]
    _ ≤ exp (√((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1 * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_radial_exp_le k one_pos hL) (exp_pos _).le

/-! ### A purely exponential radial sum

`Σ_x e^{-c|x|} ≤ C(c, d)`, uniformly in `L`.  This is what turns the strong decay of
`(prop:ThfadC_short)` into an `(∞→∞)`-norm bound on `Θ_t^{(σ,σ)}`. -/

/-- `r^m e^{-cr} ≤ m!/c^m` for `r ≥ 0`, `c > 0`. -/
theorem pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ m * exp (-(c * r)) ≤ (Nat.factorial m : ℝ) / c ^ m := by
  have h := Real.pow_div_factorial_le_exp _ (by positivity : (0 : ℝ) ≤ c * r) m
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hcm : (0 : ℝ) < c ^ m := by positivity
  rw [div_le_iff₀ hfac] at h
  rw [exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) hcm]
  calc r ^ m * c ^ m = (c * r) ^ m := by rw [mul_pow]; ring
    _ ≤ exp (c * r) * (Nat.factorial m : ℝ) := h
    _ = (Nat.factorial m : ℝ) * exp (c * r) := by ring

/-- `Σ_{r<R} (r+1)^{-2} ≤ 2`. -/
theorem sum_inv_sq_le (R : ℕ) : ∑ r ∈ range R, (((r : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have hterm : ∀ r : ℕ, (((r : ℝ) + 1) ^ 2)⁻¹
      ≤ 2 * (1 / ((r : ℝ) + 1)) - 2 * (1 / (((r + 1 : ℕ) : ℝ) + 1)) := by
    intro r
    have h1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (r : ℝ) + 2 := by positivity
    push_cast
    have hkey : 2 * (1 / ((r : ℝ) + 1)) - 2 * (1 / ((r : ℝ) + 1 + 1))
        = 2 / (((r : ℝ) + 1) * ((r : ℝ) + 1 + 1)) := by field_simp; ring
    rw [hkey, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∑ r ∈ range R, (((r : ℝ) + 1) ^ 2)⁻¹
      ≤ ∑ r ∈ range R, (2 * (1 / ((r : ℝ) + 1)) - 2 * (1 / (((r + 1 : ℕ) : ℝ) + 1))) :=
        sum_le_sum fun r _ => hterm r
    _ = 2 * (1 / ((0 : ℝ) + 1)) - 2 * (1 / ((R : ℝ) + 1)) := by
        rw [sum_range_sub' (fun r : ℕ => 2 * (1 / ((r : ℝ) + 1))) R]
        norm_num
    _ ≤ 2 := by
        have : 0 ≤ 2 * (1 / ((R : ℝ) + 1)) := by positivity
        norm_num
        linarith

/-- The constant of `sum_radial_exp_decay_le`. -/
noncomputable def expC (k : ℕ) (c : ℝ) : ℝ :=
  2 ^ (k + 2) * (2 * (2 ^ (k + 3) * (1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3))))

/-- `Σ_{x ∈ Z_L^d} e^{-c|x|} ≤ C(c, d)`, uniformly in `L`. -/
theorem sum_radial_exp_decay_le (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∑ x : Zd (k + 2) L, exp (-(c * (zdistD (k + 2) L x : ℝ))) ≤ expC k c := by
  have hbound : ∀ r : ℕ, ((r : ℝ) + 1) ^ (k + 1) * exp (-(c * (r : ℝ)))
      ≤ 2 ^ (k + 3) * (1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3))
        * ((((r : ℝ) + 1) ^ 2)⁻¹) := by
    intro r
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hE : 0 < exp (-(c * (r : ℝ))) := exp_pos _
    have hsq : (0 : ℝ) < ((r : ℝ) + 1) ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hsq]
    have key : ((r : ℝ) + 1) ^ (k + 3) * exp (-(c * (r : ℝ)))
        ≤ 2 ^ (k + 3) * (1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3)) := by
      have h1 : ((r : ℝ) + 1) ^ (k + 3) ≤ 2 ^ (k + 3) * (1 + (r : ℝ) ^ (k + 3)) := by
        rcases le_total (r : ℝ) 1 with h | h
        · calc ((r : ℝ) + 1) ^ (k + 3) ≤ (2 : ℝ) ^ (k + 3) :=
                pow_le_pow_left₀ (by linarith) (by linarith) _
            _ ≤ 2 ^ (k + 3) * (1 + (r : ℝ) ^ (k + 3)) :=
                le_mul_of_one_le_right (by positivity)
                  (by have := pow_nonneg hr (k + 3); linarith)
        · calc ((r : ℝ) + 1) ^ (k + 3) ≤ (2 * (r : ℝ)) ^ (k + 3) :=
                pow_le_pow_left₀ (by linarith) (by linarith) _
            _ = 2 ^ (k + 3) * (r : ℝ) ^ (k + 3) := mul_pow _ _ _
            _ ≤ 2 ^ (k + 3) * (1 + (r : ℝ) ^ (k + 3)) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2 : (r : ℝ) ^ (k + 3) * exp (-(c * (r : ℝ)))
          ≤ (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3) :=
        pow_mul_exp_neg_le hc (k + 3) hr
      have h3 : exp (-(c * (r : ℝ))) ≤ 1 :=
        exp_le_one_iff.mpr (by nlinarith)
      calc ((r : ℝ) + 1) ^ (k + 3) * exp (-(c * (r : ℝ)))
          ≤ (2 ^ (k + 3) * (1 + (r : ℝ) ^ (k + 3))) * exp (-(c * (r : ℝ))) :=
            mul_le_mul_of_nonneg_right h1 hE.le
        _ = 2 ^ (k + 3) * (exp (-(c * (r : ℝ))) + (r : ℝ) ^ (k + 3) * exp (-(c * (r : ℝ)))) := by
            ring
        _ ≤ 2 ^ (k + 3) * (1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3)) := by
            have : (0 : ℝ) < 2 ^ (k + 3) := by positivity
            nlinarith
    calc ((r : ℝ) + 1) ^ (k + 1) * exp (-(c * (r : ℝ))) * ((r : ℝ) + 1) ^ 2
        = ((r : ℝ) + 1) ^ (k + 3) * exp (-(c * (r : ℝ))) := by ring
      _ ≤ 2 ^ (k + 3) * (1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3)) := key
  rw [sum_radial (k + 2) (fun r : ℕ => exp (-(c * (r : ℝ))))]
  set M : ℝ := 2 ^ (k + 3) * (1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3)) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  calc ∑ r ∈ range ((k + 2) * L + 1), (sphereCard (k + 2) L r : ℝ) * exp (-(c * (r : ℝ)))
      ≤ ∑ r ∈ range ((k + 2) * L + 1),
          (2 : ℝ) ^ (k + 2) * (M * ((((r : ℝ) + 1) ^ 2)⁻¹)) := by
        refine sum_le_sum fun r _ => ?_
        have hc' : (sphereCard (k + 2) L r : ℝ) ≤ 2 ^ (k + 2) * ((r : ℝ) + 1) ^ (k + 1) := by
          exact_mod_cast card_sphere_le (L := L) (k + 1) r
        calc (sphereCard (k + 2) L r : ℝ) * exp (-(c * (r : ℝ)))
            ≤ (2 ^ (k + 2) * ((r : ℝ) + 1) ^ (k + 1)) * exp (-(c * (r : ℝ))) :=
              mul_le_mul_of_nonneg_right hc' (exp_pos _).le
          _ = (2 : ℝ) ^ (k + 2) * (((r : ℝ) + 1) ^ (k + 1) * exp (-(c * (r : ℝ)))) := by ring
          _ ≤ (2 : ℝ) ^ (k + 2) * (M * ((((r : ℝ) + 1) ^ 2)⁻¹)) :=
              mul_le_mul_of_nonneg_left (hbound r) (by positivity)
    _ = (2 : ℝ) ^ (k + 2) * (M * ∑ r ∈ range ((k + 2) * L + 1), ((((r : ℝ) + 1) ^ 2)⁻¹)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (k + 2) * (M * 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_inv_sq_le _) hM0)
          (by positivity)
    _ = expC k c := by rw [expC, hM]; ring

/-! ### A ball-restricted sum with a hard cutoff

`(eq:key_T_reudce)` of Appendix A.4 sums `(|x-α| ∧ ℓ + 1)^{-(d-2)}` over the internal
domain `D_{≤ℓ} = {α : |a-α| ∨ |b-α| ≤ ℓ}`.  Because of the hard cutoff `∧ ℓ` the summand
does not decay: outside the ball of radius `ℓ` around `x` it is the constant
`(ℓ+1)^{-(d-2)}`, and the bound `≲ ℓ²` there comes from the volume `≲ ℓ^d` of `D_{≤ℓ}`.

The proof below avoids counting that volume.  On `D_{≤ℓ}` the point `α` is within `ℓ`
of `a`, so the *second* copy of K2 -- the one centred at `a` -- already carries the
volume: for `|a-α| ≤ ℓ` the K2 summand at `a` is `≥ e^{-1}(ℓ+1)^{-(d-2)}`, which is the
constant we have to sum.  So both regions are paid for by `sum_radial_exp_le`, and the
`ℓ²` is the same `ℓ²` in both. -/

/-- Re-indexing a lattice sum by `α ↦ a - α`. -/
theorem sum_shift (d : ℕ) (a : Zd d L) (F : ℕ → ℝ) :
    ∑ α : Zd d L, F (zdistD d L (a - α)) = ∑ β : Zd d L, F (zdistD d L β) :=
  Fintype.sum_equiv (Equiv.subLeft a) _ _ fun _ => rfl

/-- The constant of `sum_ball_min_pow_le`. -/
noncomputable def ballC (k : ℕ) : ℝ := 2 * exp 1 * (2 ^ (k + 2) * radC 1)

theorem ballC_nonneg (k : ℕ) : 0 ≤ ballC k := by
  have := radC_pos (κ := (1 : ℝ)) one_pos
  unfold ballC; positivity

/-- **The lattice sum of Appendix A.4**: for `d = k + 2` and any finite set `D` contained
in the ball of radius `ℓ` around `a`,
`Σ_{α ∈ D} (|x-α| ∧ ℓ + 1)^{-(d-2)} ≤ C_d ℓ²`, uniformly in `x` and in `L`. -/
theorem sum_ball_min_pow_le (k : ℕ) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (D : Finset (Zd (k + 2) L))
    (a x : Zd (k + 2) L)
    (hD : ∀ α ∈ D, ((zdistD (k + 2) L (a - α) : ℕ) : ℝ) ≤ ℓ) :
    ∑ α ∈ D, ((min ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹ ≤ ballC k * ℓ ^ 2 := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  -- `(r+1)^{-k}` is antitone
  have hanti : ∀ r s : ℝ, 0 ≤ r → r ≤ s → (((s : ℝ) + 1) ^ k)⁻¹ ≤ (((r : ℝ) + 1) ^ k)⁻¹ := by
    intro r s hr hrs
    have h1 : (0 : ℝ) < (r + 1) ^ k := by positivity
    have h2 : (r + 1) ^ k ≤ (s + 1) ^ k := by
      exact pow_le_pow_left₀ (by linarith) (by linarith) k
    exact inv_anti₀ h1 h2
  -- on `[0, ℓ]` the K2 exponential costs at most `e`
  have hexp : ∀ r : ℝ, 0 ≤ r → r ≤ ℓ → (1 : ℝ) ≤ exp 1 * exp (-(1 * √(r / ℓ))) := by
    intro r hr hrℓ
    have hdiv : r / ℓ ≤ 1 := (div_le_one hℓ0).mpr hrℓ
    have hsq : √(r / ℓ) ≤ 1 := by
      have := Real.sqrt_le_sqrt hdiv
      simpa using this
    rw [← exp_add]
    have : (0 : ℝ) ≤ 1 + -(1 * √(r / ℓ)) := by simp; linarith
    calc (1 : ℝ) = exp 0 := (exp_zero).symm
      _ ≤ exp (1 + -(1 * √(r / ℓ))) := exp_le_exp.mpr this
  set G : Zd (k + 2) L → ℝ := fun α =>
    exp 1 * (((((zdistD (k + 2) L (x - α) : ℕ) : ℝ) + 1) ^ k)⁻¹
        * exp (-(1 * √(((zdistD (k + 2) L (x - α) : ℕ) : ℝ) / ℓ))))
      + exp 1 * (((((zdistD (k + 2) L (a - α) : ℕ) : ℝ) + 1) ^ k)⁻¹
        * exp (-(1 * √(((zdistD (k + 2) L (a - α) : ℕ) : ℝ) / ℓ)))) with hG
  have hG0 : ∀ α, 0 ≤ G α := by intro α; rw [hG]; positivity
  have hkey : ∀ α ∈ D, ((min ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹ ≤ G α := by
    intro α hα
    have hax := hD α hα
    have hx0 : (0 : ℝ) ≤ ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) := Nat.cast_nonneg _
    have ha0 : (0 : ℝ) ≤ ((zdistD (k + 2) L (a - α) : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hG]
    rcases le_total ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) ℓ with hx | hx
    · rw [min_eq_left hx]
      have h1 := hexp _ hx0 hx
      have hpos : (0 : ℝ) ≤ ((((zdistD (k + 2) L (x - α) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by positivity
      have hsecond : (0 : ℝ) ≤ exp 1 * (((((zdistD (k + 2) L (a - α) : ℕ) : ℝ) + 1) ^ k)⁻¹
          * exp (-(1 * √(((zdistD (k + 2) L (a - α) : ℕ) : ℝ) / ℓ)))) := by positivity
      nlinarith
    · rw [min_eq_right hx]
      have h1 := hexp _ ha0 hax
      have h2 := hanti _ _ ha0 hax
      have hfirst : (0 : ℝ) ≤ exp 1 * (((((zdistD (k + 2) L (x - α) : ℕ) : ℝ) + 1) ^ k)⁻¹
          * exp (-(1 * √(((zdistD (k + 2) L (x - α) : ℕ) : ℝ) / ℓ)))) := by positivity
      have hposa : (0 : ℝ) ≤ ((((zdistD (k + 2) L (a - α) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by positivity
      nlinarith
  calc ∑ α ∈ D, ((min ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
      ≤ ∑ α ∈ D, G α := sum_le_sum hkey
    _ ≤ ∑ α : Zd (k + 2) L, G α :=
        sum_le_sum_of_subset_of_nonneg (subset_univ D) fun α _ _ => hG0 α
    _ = exp 1 * ∑ α : Zd (k + 2) L, ((((zdistD (k + 2) L (x - α) : ℕ) : ℝ) + 1) ^ k)⁻¹
            * exp (-(1 * √(((zdistD (k + 2) L (x - α) : ℕ) : ℝ) / ℓ)))
        + exp 1 * ∑ α : Zd (k + 2) L, ((((zdistD (k + 2) L (a - α) : ℕ) : ℝ) + 1) ^ k)⁻¹
            * exp (-(1 * √(((zdistD (k + 2) L (a - α) : ℕ) : ℝ) / ℓ))) := by
        rw [hG, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ = exp 1 * ∑ β : Zd (k + 2) L, (((zdistD (k + 2) L β : ℝ) + 1) ^ k)⁻¹
            * exp (-(1 * √((zdistD (k + 2) L β : ℝ) / ℓ)))
        + exp 1 * ∑ β : Zd (k + 2) L, (((zdistD (k + 2) L β : ℝ) + 1) ^ k)⁻¹
            * exp (-(1 * √((zdistD (k + 2) L β : ℝ) / ℓ))) := by
        rw [sum_shift (k + 2) x (fun r : ℕ => (((r : ℝ) + 1) ^ k)⁻¹ * exp (-(1 * √((r : ℝ) / ℓ)))),
          sum_shift (k + 2) a (fun r : ℕ => (((r : ℝ) + 1) ^ k)⁻¹ * exp (-(1 * √((r : ℝ) / ℓ))))]
    _ ≤ exp 1 * (2 ^ (k + 2) * radC 1 * ℓ ^ 2) + exp 1 * (2 ^ (k + 2) * radC 1 * ℓ ^ 2) := by
        have h := sum_radial_exp_le (L := L) k (κ := 1) one_pos hℓ
        have he : (0 : ℝ) ≤ exp 1 := (exp_pos _).le
        exact add_le_add (mul_le_mul_of_nonneg_left h he) (mul_le_mul_of_nonneg_left h he)
    _ = ballC k * ℓ ^ 2 := by rw [ballC]; ring

end RBM
