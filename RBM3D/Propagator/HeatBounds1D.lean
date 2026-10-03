/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.HeatKernel1D
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Decay bounds for the one-dimensional heat kernel on `ℤ`

Route H, ticket B2 (design `docs/reports/T2003-prove.md` b8 row S3; Fable review
`docs/claude-team/fable/2026-10-02-routeH.md` F2 (iii)–(v), §2 S3-Z).  For the kernel
`h_τ(n) = e^{-2τ} I_n(2τ)` of `RBM3D.Propagator.HeatKernel1D` the proofs use only the tilted
inversion formula `hkZ_tilt` (no contour shift, no Poisson measure, no Bessel function):

* Esscher tilt `ν = ± min (|n| / (4τ)) 1`, so that `e^{νn} h_τ(n)` is the Fourier integral of
  `exp (2τ (cosh (ν + ik) - 1))`, whose modulus is `e^{2τ (cosh ν - 1)} e^{-2τ cosh ν (1 - cos k)}`;
* Chernoff exponent `-νn + 2τ (cosh ν - 1) ≤ -(1/8) min (n² / τ) |n|` (from `cosh ν - 1 ≤ ν²` on
  `[-1, 1]`, via `Real.cosh_le_exp_half_sq`);
* Jordan `1 - cos k ≥ k² / 8` on `[-π, π]` (`Real.cos_le_one_sub_mul_cos_sq`, `π ≤ 4`) and the
  Gaussian integral (`integral_gaussian`); the moments `∫ |k|^j e^{-b k²}` are dominated by the
  sup bounds `|k| e^{-b k²} ≤ 2 / s`, `k² e^{-b k²} ≤ 8 / s²` against `e^{-(s²/8) k²}`;
* the differences use the symbols `e^{-(ν+ik)} - 1` and `e^{ν+ik} + e^{-(ν+ik)} - 2
  = e^{ν+ik} (e^{-(ν+ik)} - 1)²`, of modulus `≤ 3 (|k| + |ν|)` and `≤ 27 (|k| + |ν|)²`; the term
  `|ν|` is absorbed into the exponential since `τ ν² ≤ min (n² / τ) |n| / 4`.

## Main results (namespace `RBM.Heat`)

* `hkZ_le`: `h_τ(n) ≤ C min (1, τ^{-1/2}) exp (-c min (n² / τ, |n|))`
  (`C = max 1 ((2π)⁻¹ 2 √(2π))`, `c = 1/8`).
* `hkZ_diff1_le`: `|h_τ(n+1) - h_τ(n)| ≤ C min (1, τ⁻¹) exp (-c min (n² / τ, |n|))`
  (`c = 1/16`).
* `hkZ_diff2_le`: `|h_τ(n+1) + h_τ(n-1) - 2 h_τ(n)|
  ≤ C min (1, τ^{-3/2}) exp (-c min (n² / τ, |n|))` (`c = 1/16`).

All three are proved here; there is no new hypothesis.
-/

namespace RBM.Heat

/-! ### Real-variable estimates -/

private lemma cosh_sub_one_le_sq {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.cosh u - 1 ≤ u ^ 2 := by
  have h1 : Real.cosh u ≤ Real.exp (u ^ 2 / 2) := Real.cosh_le_exp_half_sq u
  have hy0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hy1 : u ^ 2 / 2 < 1 := by nlinarith
  have h2 : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hy0 hy1
  have h3 : 1 / (1 - u ^ 2 / 2) ≤ 1 + u ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.2 hu2)]
  linarith

/-- The Chernoff exponent for `u = min (x / (4τ)) 1`. -/
private lemma chernoff_exp {τ x : ℝ} (hτ : 0 < τ) (hx : 0 ≤ x) :
    -(min (x / (4 * τ)) 1 * x) + 2 * τ * (Real.cosh (min (x / (4 * τ)) 1) - 1)
      ≤ -(1 / 8) * min (x ^ 2 / τ) x := by
  rcases le_total x (4 * τ) with h | h
  · have hu1 : x / (4 * τ) ≤ 1 := by rw [div_le_one (by positivity)]; exact h
    rw [min_eq_left hu1]
    have hu0 : 0 ≤ x / (4 * τ) := by positivity
    have hc := cosh_sub_one_le_sq hu0 hu1
    have hm : min (x ^ 2 / τ) x ≤ x ^ 2 / τ := min_le_left _ _
    have e1 : -(x / (4 * τ) * x) + 2 * τ * (x / (4 * τ)) ^ 2 = -(1 / 8) * (x ^ 2 / τ) := by
      field_simp
      ring
    have h2 : 2 * τ * (Real.cosh (x / (4 * τ)) - 1) ≤ 2 * τ * (x / (4 * τ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    linarith
  · have hu1 : 1 ≤ x / (4 * τ) := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [min_eq_right hu1]
    have hc := cosh_sub_one_le_sq (zero_le_one) le_rfl
    have hm : min (x ^ 2 / τ) x ≤ x := min_le_right _ _
    have h2 : 2 * τ * (Real.cosh 1 - 1) ≤ 2 * τ * 1 ^ 2 :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    linarith

/-- `τ u² ≤ m / 4` for `u = min (x / (4τ)) 1` and `m = min (x² / τ) x`. -/
private lemma tau_mul_sq_le {τ x : ℝ} (hτ : 0 < τ) (hx : 0 ≤ x) :
    τ * (min (x / (4 * τ)) 1) ^ 2 ≤ min (x ^ 2 / τ) x / 4 := by
  rcases le_total x (4 * τ) with h | h
  · have hu1 : x / (4 * τ) ≤ 1 := by rw [div_le_one (by positivity)]; exact h
    rw [min_eq_left hu1]
    have e : τ * (x / (4 * τ)) ^ 2 = x ^ 2 / (16 * τ) := by
      field_simp
      ring
    rw [e]
    have h1 : 4 * (x ^ 2 / (16 * τ)) ≤ x ^ 2 / τ := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hτ]
      nlinarith [sq_nonneg x, hτ]
    have h2 : 4 * (x ^ 2 / (16 * τ)) ≤ x := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hx (sub_nonneg.2 h)]
    have := le_min h1 h2
    linarith
  · have hu1 : 1 ≤ x / (4 * τ) := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [min_eq_right hu1]
    have h1 : 4 * τ ≤ x ^ 2 / τ := by
      rw [le_div_iff₀ hτ]
      nlinarith
    have := le_min h1 h
    linarith

/-! ### The tilted integrand -/

/-- Jordan's inequality in the form `k² / 8 ≤ 1 - cos k` on `[-π, π]`. -/
private lemma jordan {k : ℝ} (hk : |k| ≤ Real.pi) : k ^ 2 / 8 ≤ 1 - Real.cos k := by
  have h1 := Real.cos_le_one_sub_mul_cos_sq hk
  have hπ : Real.pi ≤ 4 := Real.pi_le_four
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have h2 : (1 : ℝ) / 8 ≤ 2 / Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  nlinarith [sq_nonneg k]

/-- The tilted integrand `exp (2τ (cosh (ν + ik) - 1))` of `hkZ_tilt`. -/
private noncomputable def tiltF (τ ν k : ℝ) : ℂ :=
  Complex.exp (2 * (τ : ℂ) * (Complex.cosh ((ν : ℂ) + (k : ℂ) * Complex.I) - 1))

private lemma re_cosh_tilt (ν k : ℝ) :
    (Complex.cosh ((ν : ℂ) + (k : ℂ) * Complex.I)).re = Real.cosh ν * Real.cos k := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma norm_tiltF (τ ν k : ℝ) :
    ‖tiltF τ ν k‖ = Real.exp (2 * τ * (Real.cosh ν * Real.cos k - 1)) := by
  unfold tiltF
  rw [Complex.norm_exp]
  congr 1
  simp [re_cosh_tilt]

private lemma norm_tiltF_le (τ ν k : ℝ) (hτ : 0 ≤ τ) (hk : |k| ≤ Real.pi) :
    ‖tiltF τ ν k‖ ≤ Real.exp (2 * τ * (Real.cosh ν - 1)) * Real.exp (-(τ / 4) * k ^ 2) := by
  rw [norm_tiltF, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : 1 ≤ Real.cosh ν := Real.one_le_cosh ν
  have h2 := jordan hk
  have h3 : 0 ≤ 1 - Real.cos k := by linarith [Real.cos_le_one k]
  have h4 : Real.cosh ν * (1 - Real.cos k) ≥ 1 - Real.cos k := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hτ, mul_le_mul_of_nonneg_left h4 hτ]

/-- The tilted integrand with the Fourier phase of the integer `m`. -/
private noncomputable def tiltI (τ ν : ℝ) (m : ℤ) (k : ℝ) : ℂ :=
  Complex.exp (-((k : ℂ) * (m : ℂ)) * Complex.I) * tiltF τ ν k

private lemma tiltI_continuous (τ ν : ℝ) (m : ℤ) : Continuous (tiltI τ ν m) := by
  unfold tiltI tiltF
  fun_prop

private lemma tilt_formula (τ : ℝ) (hτ : 0 ≤ τ) (ν : ℝ) (m : ℤ) :
    ((Real.exp (ν * m) * hkZ τ m : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi, tiltI τ ν m k :=
  hkZ_tilt τ hτ ν m

/-- A linear combination of `h(n + 1)`, `h(n)`, `h(n - 1)` against the tilt. -/
private lemma tilt_combo (τ : ℝ) (hτ : 0 ≤ τ) (α β γ ν : ℝ) (n : ℤ) :
    ((Real.exp (ν * n) * (α * hkZ τ (n + 1) + β * hkZ τ n + γ * hkZ τ (n - 1)) : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi,
        (Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I) *
          ((α : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + (β : ℂ)
            + (γ : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I))) * tiltF τ ν k := by
  have hp := tilt_formula τ hτ ν (n + 1)
  have h0 := tilt_formula τ hτ ν n
  have hm := tilt_formula τ hτ ν (n - 1)
  have hpt : ∀ k : ℝ, (Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I) *
          ((α : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + (β : ℂ)
            + (γ : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I))) * tiltF τ ν k
      = ((α : ℂ) * Complex.exp (-(ν : ℂ))) * tiltI τ ν (n + 1) k + (β : ℂ) * tiltI τ ν n k
        + ((γ : ℂ) * Complex.exp (ν : ℂ)) * tiltI τ ν (n - 1) k := by
    intro k
    unfold tiltI
    have e1 : Complex.exp (-((k : ℂ) * ((n + 1 : ℤ) : ℂ)) * Complex.I)
        = Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I)
          * Complex.exp (-((k : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have e2 : Complex.exp (-((k : ℂ) * ((n - 1 : ℤ) : ℂ)) * Complex.I)
        = Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I)
          * Complex.exp ((k : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have e3 : Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I))
        = Complex.exp (-(ν : ℂ)) * Complex.exp (-((k : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have e4 : Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)
        = Complex.exp (ν : ℂ) * Complex.exp ((k : ℂ) * Complex.I) := by
      rw [Complex.exp_add]
    rw [e1, e2, e3, e4]
    ring
  have hreal : Real.exp (ν * n) * (α * hkZ τ (n + 1) + β * hkZ τ n + γ * hkZ τ (n - 1))
      = α * Real.exp (-ν) * (Real.exp (ν * ((n + 1 : ℤ) : ℝ)) * hkZ τ (n + 1))
        + β * (Real.exp (ν * n) * hkZ τ n)
        + γ * Real.exp ν * (Real.exp (ν * ((n - 1 : ℤ) : ℝ)) * hkZ τ (n - 1)) := by
    have e1 : Real.exp (ν * ((n + 1 : ℤ) : ℝ)) = Real.exp (ν * n) * Real.exp ν := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have e2 : Real.exp (ν * ((n - 1 : ℤ) : ℝ)) = Real.exp (ν * n) * Real.exp (-ν) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have e3 : Real.exp (-ν) * Real.exp ν = 1 := by
      rw [← Real.exp_add]
      simp
    rw [e1, e2]
    linear_combination (-(α * Real.exp (ν * n) * hkZ τ (n + 1))
      - γ * Real.exp (ν * n) * hkZ τ (n - 1)) * e3
  have hI : ∀ m : ℤ, IntervalIntegrable (tiltI τ ν m) MeasureTheory.volume (-Real.pi) Real.pi :=
    fun m => (tiltI_continuous τ ν m).intervalIntegrable _ _
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((hI _).const_mul _ |>.add ((hI _).const_mul _))
      ((hI _).const_mul _),
    intervalIntegral.integral_add ((hI _).const_mul _) ((hI _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [hreal]
  generalize Real.exp (ν * ((n + 1 : ℤ) : ℝ)) * hkZ τ (n + 1) = Ep at hp ⊢
  generalize Real.exp (ν * ((n : ℤ) : ℝ)) * hkZ τ n = E0 at h0 ⊢
  generalize Real.exp (ν * ((n - 1 : ℤ) : ℝ)) * hkZ τ (n - 1) = Em at hm ⊢
  push_cast at hp h0 hm ⊢
  rw [hp, h0, hm]
  ring

private lemma norm_phase (k : ℝ) (n : ℤ) :
    ‖Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The Gaussian-majorant bound for a combination of `h(n + 1)`, `h(n)`, `h(n - 1)`. -/
private lemma tilt_combo_bound (τ : ℝ) (hτ : 0 < τ) (α β γ ν : ℝ) (n : ℤ) (g : ℝ → ℝ)
    (hgc : Continuous g)
    (hg : ∀ k : ℝ, |k| ≤ Real.pi →
      ‖(α : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + (β : ℂ)
        + (γ : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)‖ ≤ g k) :
    |α * hkZ τ (n + 1) + β * hkZ τ n + γ * hkZ τ (n - 1)| ≤
      Real.exp (-(ν * n) + 2 * τ * (Real.cosh ν - 1)) *
        ((2 * Real.pi)⁻¹ * ∫ k in (-Real.pi)..Real.pi, g k * Real.exp (-(τ / 4) * k ^ 2)) := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = α * hkZ τ (n + 1) + β * hkZ τ n + γ * hkZ τ (n - 1) :=
    ⟨_, rfl⟩
  rw [← hD]
  have h := tilt_combo τ hτ.le α β γ ν n
  rw [← hD] at h
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle : -Real.pi ≤ Real.pi := by linarith
  set Φ : ℝ → ℂ := fun k => (Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I) *
          ((α : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + (β : ℂ)
            + (γ : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I))) * tiltF τ ν k with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ]
    unfold tiltF
    fun_prop
  have hnorm : Real.exp (ν * n) * |D| ≤ Real.exp (2 * τ * (Real.cosh ν - 1)) *
        ((2 * Real.pi)⁻¹ * ∫ k in (-Real.pi)..Real.pi, g k * Real.exp (-(τ / 4) * k ^ 2)) := by
    have h1 : ‖((Real.exp (ν * n) * D : ℝ) : ℂ)‖ = Real.exp (ν * n) * |D| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h2 : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← h1, h, norm_mul, h2]
    have h3 : ‖∫ k in (-Real.pi)..Real.pi, Φ k‖ ≤ ∫ k in (-Real.pi)..Real.pi, ‖Φ k‖ :=
      intervalIntegral.norm_integral_le_integral_norm hle
    have h4 : ∫ k in (-Real.pi)..Real.pi, ‖Φ k‖ ≤
        ∫ k in (-Real.pi)..Real.pi, Real.exp (2 * τ * (Real.cosh ν - 1)) *
          (g k * Real.exp (-(τ / 4) * k ^ 2)) := by
      refine intervalIntegral.integral_mono_on hle (hΦc.norm.intervalIntegrable _ _) ?_ ?_
      · exact (by fun_prop : Continuous fun k : ℝ => Real.exp (2 * τ * (Real.cosh ν - 1)) *
          (g k * Real.exp (-(τ / 4) * k ^ 2))).intervalIntegrable _ _
      · intro k hk
        have hk' : |k| ≤ Real.pi := abs_le.2 ⟨hk.1, hk.2⟩
        have hF := norm_tiltF_le τ ν k hτ.le hk'
        have hP := hg k hk'
        rw [hΦ]
        simp only [norm_mul, norm_phase, one_mul]
        calc ‖(α : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + (β : ℂ)
              + (γ : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)‖ * ‖tiltF τ ν k‖
            ≤ g k * (Real.exp (2 * τ * (Real.cosh ν - 1)) * Real.exp (-(τ / 4) * k ^ 2)) :=
              mul_le_mul hP hF (norm_nonneg _) ((norm_nonneg _).trans hP)
          _ = Real.exp (2 * τ * (Real.cosh ν - 1)) * (g k * Real.exp (-(τ / 4) * k ^ 2)) := by
              ring
    rw [intervalIntegral.integral_const_mul] at h4
    have h5 : (2 * Real.pi)⁻¹ * ‖∫ k in (-Real.pi)..Real.pi, Φ k‖ ≤
        (2 * Real.pi)⁻¹ * (Real.exp (2 * τ * (Real.cosh ν - 1)) *
          ∫ k in (-Real.pi)..Real.pi, g k * Real.exp (-(τ / 4) * k ^ 2)) :=
      mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    calc (2 * Real.pi)⁻¹ * ‖∫ k in (-Real.pi)..Real.pi, Φ k‖ ≤ _ := h5
      _ = _ := by ring
  have hexp : Real.exp (-(ν * n) + 2 * τ * (Real.cosh ν - 1))
      = Real.exp (-(ν * n)) * Real.exp (2 * τ * (Real.cosh ν - 1)) := Real.exp_add _ _
  have hcancel : Real.exp (-(ν * n)) * Real.exp (ν * n) = 1 := by
    rw [← Real.exp_add]
    simp
  calc |D| = Real.exp (-(ν * n)) * (Real.exp (ν * n) * |D|) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp (-(ν * n)) * (Real.exp (2 * τ * (Real.cosh ν - 1)) *
        ((2 * Real.pi)⁻¹ * ∫ k in (-Real.pi)..Real.pi, g k * Real.exp (-(τ / 4) * k ^ 2))) :=
        mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    _ = _ := by rw [hexp]; ring

/-! ### Gaussian majorants -/

private lemma integral_gauss_le (b : ℝ) (hb : 0 < b) :
    ∫ k in (-Real.pi)..Real.pi, Real.exp (-b * k ^ 2) ≤ Real.sqrt (Real.pi / b) := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hle, ← integral_gaussian b]
  exact MeasureTheory.setIntegral_le_integral (integrable_exp_neg_mul_sq hb)
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)

private lemma sqrt_gauss_eq (s : ℝ) (hs : 0 < s) :
    Real.sqrt (Real.pi / (s ^ 2 / 8)) = 2 * Real.sqrt (2 * Real.pi) / s := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have h : Real.pi / (s ^ 2 / 8) = (2 * Real.sqrt (2 * Real.pi) / s) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hπ]
    field_simp
    ring
  rw [h]
  exact Real.sqrt_sq (by positivity)

/-- A continuous function dominated by `K exp (-(s²/8) k²)` has small integral over `[-π, π]`. -/
private lemma integral_le_gauss (s : ℝ) (hs : 0 < s) (g : ℝ → ℝ) (hgc : Continuous g) (K : ℝ)
    (hK : 0 ≤ K) (hg : ∀ k : ℝ, g k ≤ K * Real.exp (-(s ^ 2 / 8) * k ^ 2)) :
    ∫ k in (-Real.pi)..Real.pi, g k ≤ K * (2 * Real.sqrt (2 * Real.pi) / s) := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hKc : Continuous fun k : ℝ => K * Real.exp (-(s ^ 2 / 8) * k ^ 2) := by fun_prop
  calc ∫ k in (-Real.pi)..Real.pi, g k
      ≤ ∫ k in (-Real.pi)..Real.pi, K * Real.exp (-(s ^ 2 / 8) * k ^ 2) :=
        intervalIntegral.integral_mono_on hle (hgc.intervalIntegrable _ _)
          (hKc.intervalIntegrable _ _) (fun k _ => hg k)
    _ = K * ∫ k in (-Real.pi)..Real.pi, Real.exp (-(s ^ 2 / 8) * k ^ 2) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ K * Real.sqrt (Real.pi / (s ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_left (integral_gauss_le _ (by positivity)) hK
    _ = K * (2 * Real.sqrt (2 * Real.pi) / s) := by rw [sqrt_gauss_eq s hs]

/-- A continuous function bounded by `K` has integral at most `2π K` over `[-π, π]`. -/
private lemma integral_le_const (g : ℝ → ℝ) (hgc : Continuous g) (K : ℝ)
    (hg : ∀ k : ℝ, |k| ≤ Real.pi → g k ≤ K) :
    ∫ k in (-Real.pi)..Real.pi, g k ≤ 2 * Real.pi * K := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  calc ∫ k in (-Real.pi)..Real.pi, g k ≤ ∫ k in (-Real.pi)..Real.pi, K :=
        intervalIntegral.integral_mono_on hle (hgc.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
          (fun k hk => hg k (abs_le.2 ⟨hk.1, hk.2⟩))
    _ = 2 * Real.pi * K := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

private lemma abs_mul_exp_le {s : ℝ} (hs : 0 < s) (k : ℝ) :
    |k| * Real.exp (-(s ^ 2 / 8) * k ^ 2) ≤ 2 / s := by
  have hy0 : 0 ≤ s * |k| := by positivity
  have h1 := Real.add_one_le_exp ((s * |k|) ^ 2 / 8)
  have hy : s * |k| ≤ 2 * Real.exp ((s * |k|) ^ 2 / 8) := by
    nlinarith [sq_nonneg (s * |k| - 2)]
  have e1 : (s * |k|) ^ 2 / 8 = (s ^ 2 / 8) * k ^ 2 := by
    rw [mul_pow, sq_abs]
    ring
  rw [e1] at hy
  have e2 : Real.exp (-(s ^ 2 / 8) * k ^ 2) = (Real.exp ((s ^ 2 / 8) * k ^ 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [e2, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hs]
  linarith [mul_comm |k| s]

private lemma sq_mul_exp_le {s : ℝ} (hs : 0 < s) (k : ℝ) :
    k ^ 2 * Real.exp (-(s ^ 2 / 8) * k ^ 2) ≤ 8 / s ^ 2 := by
  have hy := Real.add_one_le_exp ((s ^ 2 / 8) * k ^ 2)
  have e2 : Real.exp (-(s ^ 2 / 8) * k ^ 2) = (Real.exp ((s ^ 2 / 8) * k ^ 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [e2, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith [hy]

/-! ### The three symbols -/

private lemma exp_le_three {ν : ℝ} (hν : |ν| ≤ 1) : Real.exp ν ≤ 3 := by
  have h1 : ν ≤ 1 := (le_abs_self ν).trans hν
  calc Real.exp ν ≤ Real.exp 1 := Real.exp_le_exp.2 h1
    _ ≤ 3 := Real.exp_one_lt_three.le

private lemma norm_exp_neg_sub_one_le {ν k : ℝ} (hν : |ν| ≤ 1) :
    ‖Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) - 1‖ ≤ 3 * (|k| + |ν|) := by
  have e1 : Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) - 1 =
      Complex.exp (-(ν : ℂ)) * (Complex.exp (-((k : ℂ) * Complex.I)) - 1)
        + (Complex.exp (-(ν : ℂ)) - 1) := by
    rw [neg_add, Complex.exp_add]
    ring
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖Complex.exp (-(ν : ℂ))‖ ≤ 3 := by
    rw [Complex.norm_exp]
    have : (-(ν : ℂ)).re = -ν := by simp
    rw [this]
    exact exp_le_three (by rwa [abs_neg])
  have h2 : ‖Complex.exp (-((k : ℂ) * Complex.I)) - 1‖ ≤ |k| := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -k)
    have e : Complex.exp (Complex.I * ((-k : ℝ) : ℂ)) = Complex.exp (-((k : ℂ) * Complex.I)) := by
      congr 1
      push_cast
      ring
    rw [e] at h
    simpa using h
  have h3 : ‖Complex.exp (-(ν : ℂ)) - 1‖ ≤ 2 * |ν| := by
    have hn : ‖-(ν : ℂ)‖ ≤ 1 := by simpa using hν
    have := Complex.norm_exp_sub_one_le hn
    simpa using this
  rw [norm_mul]
  have h4 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
  nlinarith [abs_nonneg k, abs_nonneg ν]

private lemma norm_P1_le {ν k : ℝ} (hν : |ν| ≤ 1) :
    ‖((1 : ℝ) : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + ((-1 : ℝ) : ℂ)
        + ((0 : ℝ) : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)‖ ≤ 3 * (|k| + |ν|) := by
  have e : ((1 : ℝ) : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + ((-1 : ℝ) : ℂ)
        + ((0 : ℝ) : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)
      = Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) - 1 := by
    push_cast
    ring
  rw [e]
  exact norm_exp_neg_sub_one_le hν

private lemma norm_P2_le {ν k : ℝ} (hν : |ν| ≤ 1) :
    ‖((1 : ℝ) : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + ((-2 : ℝ) : ℂ)
        + ((1 : ℝ) : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)‖
      ≤ 27 * (|k| + |ν|) ^ 2 := by
  have h : Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)
      * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have e : ((1 : ℝ) : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + ((-2 : ℝ) : ℂ)
        + ((1 : ℝ) : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)
      = Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)
        * (Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) - 1) ^ 2 := by
    push_cast
    linear_combination (2 - Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I))) * h
  rw [e, norm_mul, norm_pow]
  have h1 : ‖Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)‖ ≤ 3 := by
    rw [Complex.norm_exp]
    have : ((ν : ℂ) + (k : ℂ) * Complex.I).re = ν := by simp
    rw [this]
    exact exp_le_three hν
  have h2 := norm_exp_neg_sub_one_le (k := k) hν
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 := mul_le_mul h1 h3 (sq_nonneg _) (by norm_num)
  nlinarith [h4]

private lemma norm_P0_le {ν k : ℝ} :
    ‖((0 : ℝ) : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + ((1 : ℝ) : ℂ)
        + ((0 : ℝ) : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)‖ ≤ 1 := by
  simp

/-! ### The tilt parameter and the two generic bounds -/

/-- The tilt `ν = ± min (|n| / (4τ)) 1` with its Chernoff exponent and `τ ν² ≤ m / 4`. -/
private lemma exists_tilt (τ : ℝ) (hτ : 0 < τ) (n : ℤ) :
    ∃ ν : ℝ, |ν| ≤ 1 ∧
      -(ν * n) + 2 * τ * (Real.cosh ν - 1) ≤ -(1 / 8) * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)| ∧
      τ * ν ^ 2 ≤ min ((n : ℝ) ^ 2 / τ) |(n : ℝ)| / 4 := by
  have hx : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hu0 : 0 ≤ min (|(n : ℝ)| / (4 * τ)) 1 := le_min (by positivity) zero_le_one
  have hu1 : min (|(n : ℝ)| / (4 * τ)) 1 ≤ 1 := min_le_right _ _
  have hc := chernoff_exp hτ hx
  have ht := tau_mul_sq_le hτ hx
  rw [sq_abs] at hc ht
  by_cases h : 0 ≤ (n : ℝ)
  · refine ⟨min (|(n : ℝ)| / (4 * τ)) 1, by rwa [abs_of_nonneg hu0], ?_, ht⟩
    rw [abs_of_nonneg h] at hc ⊢
    exact hc
  · have hn : (n : ℝ) < 0 := not_le.1 h
    refine ⟨-min (|(n : ℝ)| / (4 * τ)) 1, by rwa [abs_neg, abs_of_nonneg hu0], ?_, ?_⟩
    · rw [Real.cosh_neg]
      have e : -(-min (|(n : ℝ)| / (4 * τ)) 1 * (n : ℝ))
          = -(min (|(n : ℝ)| / (4 * τ)) 1 * |(n : ℝ)|) := by
        rw [abs_of_neg hn]
        ring
      rw [e]
      exact hc
    · rw [neg_sq]
      exact ht

private lemma exp_quarter_le_eighth (s k : ℝ) :
    Real.exp (-(s ^ 2 / 4) * k ^ 2) ≤ Real.exp (-(s ^ 2 / 8) * k ^ 2) := by
  apply Real.exp_le_exp.2
  nlinarith [sq_nonneg (s * k)]

/-- Trivial bound: the factor is bounded, hence so is the symbol integral. -/
private lemma trivial_bound (τ : ℝ) (hτ : 0 < τ) (α β γ ν : ℝ) (n : ℤ) (K : ℝ) (hK : 0 ≤ K)
    (g : ℝ → ℝ) (hgc : Continuous g)
    (hg : ∀ k : ℝ, |k| ≤ Real.pi →
      ‖(α : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + (β : ℂ)
        + (γ : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)‖ ≤ g k)
    (hgK : ∀ k : ℝ, |k| ≤ Real.pi → g k ≤ K) :
    |α * hkZ τ (n + 1) + β * hkZ τ n + γ * hkZ τ (n - 1)| ≤
      Real.exp (-(ν * n) + 2 * τ * (Real.cosh ν - 1)) * K := by
  have hb := tilt_combo_bound τ hτ α β γ ν n g hgc hg
  have hI : ∫ k in (-Real.pi)..Real.pi, g k * Real.exp (-(τ / 4) * k ^ 2) ≤ 2 * Real.pi * K := by
    refine integral_le_const _ (by fun_prop) K (fun k hk => ?_)
    have h1 : Real.exp (-(τ / 4) * k ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg k]
    calc g k * Real.exp (-(τ / 4) * k ^ 2) ≤ K * 1 :=
          mul_le_mul (hgK k hk) h1 (Real.exp_pos _).le hK
      _ = K := mul_one K
  have h2 : (2 * Real.pi)⁻¹ * ∫ k in (-Real.pi)..Real.pi, g k * Real.exp (-(τ / 4) * k ^ 2)
      ≤ K := by
    calc (2 * Real.pi)⁻¹ * ∫ k in (-Real.pi)..Real.pi, g k * Real.exp (-(τ / 4) * k ^ 2)
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * K) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = K := by field_simp
  exact hb.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)

/-- Gaussian bound: the factor is dominated by `K exp (-(s²/8) k²)` against the Gaussian. -/
private lemma gauss_bound (s : ℝ) (hs : 0 < s) (α β γ ν : ℝ) (n : ℤ) (K : ℝ) (hK : 0 ≤ K)
    (g : ℝ → ℝ) (hgc : Continuous g)
    (hg : ∀ k : ℝ, |k| ≤ Real.pi →
      ‖(α : ℂ) * Complex.exp (-((ν : ℂ) + (k : ℂ) * Complex.I)) + (β : ℂ)
        + (γ : ℂ) * Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)‖ ≤ g k)
    (hgK : ∀ k : ℝ, g k * Real.exp (-(s ^ 2 / 4) * k ^ 2) ≤ K * Real.exp (-(s ^ 2 / 8) * k ^ 2)) :
    |α * hkZ (s ^ 2) (n + 1) + β * hkZ (s ^ 2) n + γ * hkZ (s ^ 2) (n - 1)| ≤
      Real.exp (-(ν * n) + 2 * s ^ 2 * (Real.cosh ν - 1)) *
        ((2 * Real.pi)⁻¹ * (K * (2 * Real.sqrt (2 * Real.pi) / s))) := by
  have hτ : 0 < s ^ 2 := by positivity
  have hb := tilt_combo_bound (s ^ 2) hτ α β γ ν n g hgc hg
  have hI : ∫ k in (-Real.pi)..Real.pi, g k * Real.exp (-(s ^ 2 / 4) * k ^ 2)
      ≤ K * (2 * Real.sqrt (2 * Real.pi) / s) :=
    integral_le_gauss s hs _ (by fun_prop) K hK hgK
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hI (by positivity)) (Real.exp_pos _).le)

/-! ### Pointwise Gaussian domination, absorption, and the `min` combination -/

private lemma exp_sq_split (s k : ℝ) :
    Real.exp (-(s ^ 2 / 4) * k ^ 2)
      = Real.exp (-(s ^ 2 / 8) * k ^ 2) * Real.exp (-(s ^ 2 / 8) * k ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

private lemma pt0 (s k : ℝ) :
    1 * Real.exp (-(s ^ 2 / 4) * k ^ 2) ≤ 1 * Real.exp (-(s ^ 2 / 8) * k ^ 2) := by
  rw [one_mul, one_mul]
  exact exp_quarter_le_eighth s k

private lemma pt1 {s : ℝ} (hs : 0 < s) (u k : ℝ) (hu : 0 ≤ u) :
    3 * (|k| + u) * Real.exp (-(s ^ 2 / 4) * k ^ 2)
      ≤ 3 * (2 / s + u) * Real.exp (-(s ^ 2 / 8) * k ^ 2) := by
  have h1 := abs_mul_exp_le hs k
  have h2 := exp_quarter_le_eighth s k
  have e := exp_sq_split s k
  have hE8 := Real.exp_pos (-(s ^ 2 / 8) * k ^ 2)
  have h3 : |k| * Real.exp (-(s ^ 2 / 4) * k ^ 2) ≤ 2 / s * Real.exp (-(s ^ 2 / 8) * k ^ 2) := by
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 hE8.le
  have h4 : u * Real.exp (-(s ^ 2 / 4) * k ^ 2) ≤ u * Real.exp (-(s ^ 2 / 8) * k ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hu
  nlinarith [h3, h4]

private lemma pt2 {s : ℝ} (hs : 0 < s) (u k : ℝ) :
    27 * (|k| + u) ^ 2 * Real.exp (-(s ^ 2 / 4) * k ^ 2)
      ≤ 54 * (8 / s ^ 2 + u ^ 2) * Real.exp (-(s ^ 2 / 8) * k ^ 2) := by
  have h1 := sq_mul_exp_le hs k
  have h2 := exp_quarter_le_eighth s k
  have e := exp_sq_split s k
  have hE8 := Real.exp_pos (-(s ^ 2 / 8) * k ^ 2)
  have h3 : k ^ 2 * Real.exp (-(s ^ 2 / 4) * k ^ 2)
      ≤ 8 / s ^ 2 * Real.exp (-(s ^ 2 / 8) * k ^ 2) := by
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 hE8.le
  have h4 : u ^ 2 * Real.exp (-(s ^ 2 / 4) * k ^ 2) ≤ u ^ 2 * Real.exp (-(s ^ 2 / 8) * k ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg u)
  have h5 : (|k| + u) ^ 2 ≤ 2 * k ^ 2 + 2 * u ^ 2 := by
    nlinarith [sq_nonneg (|k| - u), sq_abs k]
  have hE4 := Real.exp_pos (-(s ^ 2 / 4) * k ^ 2)
  nlinarith [mul_le_mul_of_nonneg_right h5 hE4.le, h3, h4]

private lemma abs_mul_le_exp {s ν m : ℝ} (h : s ^ 2 * ν ^ 2 ≤ m / 4) :
    |ν| * s ≤ Real.exp (m / 16) := by
  have hy : (|ν| * s) ^ 2 ≤ m / 4 := by
    rw [mul_pow, sq_abs]
    linarith [mul_comm (s ^ 2) (ν ^ 2)]
  have h1 := Real.add_one_le_exp (m / 16)
  nlinarith [sq_nonneg (|ν| * s - 2)]

private lemma sq_mul_le_exp {s ν m : ℝ} (h : s ^ 2 * ν ^ 2 ≤ m / 4) :
    (|ν| * s) ^ 2 ≤ 4 * Real.exp (m / 16) := by
  have hy : (|ν| * s) ^ 2 ≤ m / 4 := by
    rw [mul_pow, sq_abs]
    linarith [mul_comm (s ^ 2) (ν ^ 2)]
  have h1 := Real.add_one_le_exp (m / 16)
  nlinarith

private lemma min_combine {X E A B t : ℝ} (hE : 0 ≤ E) (ht : 0 ≤ t)
    (h1 : X ≤ A * E) (h2 : X ≤ B * t * E) : X ≤ max A B * min 1 t * E := by
  rcases le_total 1 t with h | h
  · rw [min_eq_left h]
    calc X ≤ A * E := h1
      _ ≤ max A B * 1 * E := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hE
  · rw [min_eq_right h]
    calc X ≤ B * t * E := h2
      _ ≤ max A B * t * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) ht) hE

private lemma rpow_neg_half {s : ℝ} (hs : 0 < s) : (s ^ 2) ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
  rw [Real.rpow_neg (by positivity)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hs.le]

private lemma rpow_neg_three_halves {s : ℝ} (hs : 0 < s) :
    (s ^ 2) ^ (-(3 / 2 : ℝ)) = (s ^ 3)⁻¹ := by
  rw [Real.rpow_neg (by positivity)]
  congr 1
  rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le]
  norm_num

/-! ### The three bounds -/

/-- Target 1 (`Bound`): Gaussian/exponential decay of the heat kernel on `ℤ`. -/
theorem hkZ_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    hkZ τ n ≤ C * min 1 (τ ^ (-(1 / 2 : ℝ))) * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|) := by
  refine ⟨max 1 ((2 * Real.pi)⁻¹ * (1 * (2 * Real.sqrt (2 * Real.pi)))), 1 / 8,
    lt_of_lt_of_le one_pos (le_max_left _ _), by norm_num, ?_⟩
  intro τ hτ n
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ τ = s ^ 2 :=
    ⟨Real.sqrt τ, Real.sqrt_pos.2 hτ, (Real.sq_sqrt hτ.le).symm⟩
  obtain ⟨ν, hν1, hchern, hτν⟩ := exists_tilt (s ^ 2) hτ n
  rw [rpow_neg_half hs]
  have hE : Real.exp (-(ν * n) + 2 * s ^ 2 * (Real.cosh ν - 1))
      ≤ Real.exp (-(1 / 8) * min ((n : ℝ) ^ 2 / s ^ 2) |(n : ℝ)|) := Real.exp_le_exp.2 hchern
  have hh : hkZ (s ^ 2) n ≤
      |0 * hkZ (s ^ 2) (n + 1) + 1 * hkZ (s ^ 2) n + 0 * hkZ (s ^ 2) (n - 1)| := by
    simp only [zero_mul, one_mul, zero_add, add_zero]
    exact le_abs_self _
  have hT := trivial_bound (s ^ 2) hτ 0 1 0 ν n 1 zero_le_one (fun _ => 1) continuous_const
    (fun k _ => norm_P0_le) (fun _ _ => le_rfl)
  have hG := gauss_bound s hs 0 1 0 ν n 1 zero_le_one (fun _ => 1) continuous_const
    (fun k _ => norm_P0_le) (fun k => pt0 s k)
  refine min_combine (Real.exp_pos _).le (inv_nonneg.2 hs.le) ?_ ?_
  · calc hkZ (s ^ 2) n ≤ _ := hh
      _ ≤ _ := hT
      _ ≤ 1 * Real.exp (-(1 / 8) * min ((n : ℝ) ^ 2 / s ^ 2) |(n : ℝ)|) := by
        rw [mul_one, one_mul]
        exact hE
  · calc hkZ (s ^ 2) n ≤ _ := hh
      _ ≤ _ := hG
      _ ≤ Real.exp (-(1 / 8) * min ((n : ℝ) ^ 2 / s ^ 2) |(n : ℝ)|) *
            ((2 * Real.pi)⁻¹ * (1 * (2 * Real.sqrt (2 * Real.pi) / s))) :=
        mul_le_mul_of_nonneg_right hE (by positivity)
      _ = (2 * Real.pi)⁻¹ * (1 * (2 * Real.sqrt (2 * Real.pi))) * s⁻¹ *
            Real.exp (-(1 / 8) * min ((n : ℝ) ^ 2 / s ^ 2) |(n : ℝ)|) := by
        field_simp

/-- Target 2 (`Diff1`): the first difference gains `min (1, τ⁻¹)`. -/
theorem hkZ_diff1_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    |hkZ τ (n + 1) - hkZ τ n|
      ≤ C * min 1 τ⁻¹ * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|) := by
  refine ⟨max (3 * (Real.pi + 1)) (9 * ((2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi)))), 1 / 16,
    lt_of_lt_of_le (by positivity) (le_max_left _ _), by norm_num, ?_⟩
  intro τ hτ n
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ τ = s ^ 2 :=
    ⟨Real.sqrt τ, Real.sqrt_pos.2 hτ, (Real.sq_sqrt hτ.le).symm⟩
  obtain ⟨ν, hν1, hchern, hτν⟩ := exists_tilt (s ^ 2) hτ n
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min ((n : ℝ) ^ 2 / s ^ 2) |(n : ℝ)| := ⟨_, rfl⟩
  rw [← hm] at hchern hτν ⊢
  have hm0 : 0 ≤ m := by
    rw [hm]
    exact le_min (by positivity) (abs_nonneg _)
  have hE : Real.exp (-(ν * n) + 2 * s ^ 2 * (Real.cosh ν - 1)) ≤ Real.exp (-(1 / 8) * m) :=
    Real.exp_le_exp.2 hchern
  have hE' : Real.exp (-(1 / 8) * m) ≤ Real.exp (-(1 / 16) * m) :=
    Real.exp_le_exp.2 (by linarith)
  have hus := abs_mul_le_exp hτν
  have h1 : 1 ≤ Real.exp (m / 16) := Real.one_le_exp (by positivity)
  have hD : |hkZ (s ^ 2) (n + 1) - hkZ (s ^ 2) n| =
      |1 * hkZ (s ^ 2) (n + 1) + (-1) * hkZ (s ^ 2) n + 0 * hkZ (s ^ 2) (n - 1)| := by
    congr 1
    ring
  have hT := trivial_bound (s ^ 2) hτ 1 (-1) 0 ν n (3 * (Real.pi + 1)) (by positivity)
    (fun k => 3 * (|k| + |ν|)) (by fun_prop) (fun k _ => norm_P1_le hν1)
    (fun k hk => by
      have := Real.pi_pos
      have h2 : |ν| ≤ 1 := hν1
      nlinarith)
  have hG := gauss_bound s hs 1 (-1) 0 ν n (3 * (2 / s + |ν|)) (by positivity)
    (fun k => 3 * (|k| + |ν|)) (by fun_prop) (fun k _ => norm_P1_le hν1)
    (fun k => pt1 hs |ν| k (abs_nonneg ν))
  have hkey : Real.exp (-(1 / 8) * m) * (2 + |ν| * s) ≤ 3 * Real.exp (-(1 / 16) * m) := by
    calc Real.exp (-(1 / 8) * m) * (2 + |ν| * s)
        ≤ Real.exp (-(1 / 8) * m) * (3 * Real.exp (m / 16)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 3 * Real.exp (-(1 / 16) * m) := by
          rw [mul_left_comm, ← Real.exp_add]
          rw [show -(1 / 8) * m + m / 16 = -(1 / 16) * m by ring]
  rw [hD]
  refine min_combine (Real.exp_pos _).le (inv_nonneg.2 (by positivity)) ?_ ?_
  · calc _ ≤ _ := hT
      _ ≤ Real.exp (-(1 / 8) * m) * (3 * (Real.pi + 1)) :=
        mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ Real.exp (-(1 / 16) * m) * (3 * (Real.pi + 1)) :=
        mul_le_mul_of_nonneg_right hE' (by positivity)
      _ = 3 * (Real.pi + 1) * Real.exp (-(1 / 16) * m) := by ring
  · calc _ ≤ _ := hG
      _ ≤ Real.exp (-(1 / 8) * m) *
            ((2 * Real.pi)⁻¹ * (3 * (2 / s + |ν|) * (2 * Real.sqrt (2 * Real.pi) / s))) :=
        mul_le_mul_of_nonneg_right hE (by positivity)
      _ = (3 * (2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi)) / s ^ 2) *
            (Real.exp (-(1 / 8) * m) * (2 + |ν| * s)) := by
        field_simp
      _ ≤ (3 * (2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi)) / s ^ 2) *
            (3 * Real.exp (-(1 / 16) * m)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 9 * ((2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi))) * (s ^ 2)⁻¹ *
            Real.exp (-(1 / 16) * m) := by
        field_simp
        ring

/-- Target 3 (`Diff2`): the second difference gains `min (1, τ^{-3/2})`. -/
theorem hkZ_diff2_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    |hkZ τ (n + 1) + hkZ τ (n - 1) - 2 * hkZ τ n|
      ≤ C * min 1 (τ ^ (-(3 / 2 : ℝ))) * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|) := by
  refine ⟨max (27 * (Real.pi + 1) ^ 2) (648 * ((2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi)))),
    1 / 16, lt_of_lt_of_le (by positivity) (le_max_left _ _), by norm_num, ?_⟩
  intro τ hτ n
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ τ = s ^ 2 :=
    ⟨Real.sqrt τ, Real.sqrt_pos.2 hτ, (Real.sq_sqrt hτ.le).symm⟩
  obtain ⟨ν, hν1, hchern, hτν⟩ := exists_tilt (s ^ 2) hτ n
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min ((n : ℝ) ^ 2 / s ^ 2) |(n : ℝ)| := ⟨_, rfl⟩
  rw [← hm] at hchern hτν ⊢
  have hm0 : 0 ≤ m := by
    rw [hm]
    exact le_min (by positivity) (abs_nonneg _)
  have hE : Real.exp (-(ν * n) + 2 * s ^ 2 * (Real.cosh ν - 1)) ≤ Real.exp (-(1 / 8) * m) :=
    Real.exp_le_exp.2 hchern
  have hE' : Real.exp (-(1 / 8) * m) ≤ Real.exp (-(1 / 16) * m) :=
    Real.exp_le_exp.2 (by linarith)
  have hus := sq_mul_le_exp hτν
  have h1 : 1 ≤ Real.exp (m / 16) := Real.one_le_exp (by positivity)
  have hD : |hkZ (s ^ 2) (n + 1) + hkZ (s ^ 2) (n - 1) - 2 * hkZ (s ^ 2) n| =
      |1 * hkZ (s ^ 2) (n + 1) + (-2) * hkZ (s ^ 2) n + 1 * hkZ (s ^ 2) (n - 1)| := by
    congr 1
    ring
  have hT := trivial_bound (s ^ 2) hτ 1 (-2) 1 ν n (27 * (Real.pi + 1) ^ 2) (by positivity)
    (fun k => 27 * (|k| + |ν|) ^ 2) (by fun_prop) (fun k _ => norm_P2_le hν1)
    (fun k hk => by
      have := Real.pi_pos
      have h2 : |ν| ≤ 1 := hν1
      have h3 : |k| + |ν| ≤ Real.pi + 1 := by linarith
      have h4 := pow_le_pow_left₀ (by positivity) h3 2
      linarith)
  have hG := gauss_bound s hs 1 (-2) 1 ν n (54 * (8 / s ^ 2 + |ν| ^ 2)) (by positivity)
    (fun k => 27 * (|k| + |ν|) ^ 2) (by fun_prop) (fun k _ => norm_P2_le hν1)
    (fun k => pt2 hs |ν| k)
  have hkey : Real.exp (-(1 / 8) * m) * (8 + (|ν| * s) ^ 2) ≤ 12 * Real.exp (-(1 / 16) * m) := by
    calc Real.exp (-(1 / 8) * m) * (8 + (|ν| * s) ^ 2)
        ≤ Real.exp (-(1 / 8) * m) * (12 * Real.exp (m / 16)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 12 * Real.exp (-(1 / 16) * m) := by
          rw [mul_left_comm, ← Real.exp_add]
          rw [show -(1 / 8) * m + m / 16 = -(1 / 16) * m by ring]
  rw [hD, rpow_neg_three_halves hs]
  refine min_combine (Real.exp_pos _).le (inv_nonneg.2 (by positivity)) ?_ ?_
  · calc _ ≤ _ := hT
      _ ≤ Real.exp (-(1 / 8) * m) * (27 * (Real.pi + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ Real.exp (-(1 / 16) * m) * (27 * (Real.pi + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right hE' (by positivity)
      _ = 27 * (Real.pi + 1) ^ 2 * Real.exp (-(1 / 16) * m) := by ring
  · calc _ ≤ _ := hG
      _ ≤ Real.exp (-(1 / 8) * m) *
            ((2 * Real.pi)⁻¹ * (54 * (8 / s ^ 2 + |ν| ^ 2) * (2 * Real.sqrt (2 * Real.pi) / s))) :=
        mul_le_mul_of_nonneg_right hE (by positivity)
      _ = (54 * (2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi)) / s ^ 3) *
            (Real.exp (-(1 / 8) * m) * (8 + (|ν| * s) ^ 2)) := by
        field_simp
      _ ≤ (54 * (2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi)) / s ^ 3) *
            (12 * Real.exp (-(1 / 16) * m)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 648 * ((2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi))) * (s ^ 3)⁻¹ *
            Real.exp (-(1 / 16) * m) := by
        field_simp
        ring

/-! ### Compiled instances

Each bound applied at `τ = 100`, with `n = 0` (where `min (1, τ^{-j}) = 10^{-j}` is the whole
gain) and with `n = 7` (where the exponential factor `exp (-c · 49/100)` is nontrivial). -/

private lemma rpow_hundred_neg_half : (100 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 10 := by
  have h := rpow_neg_half (s := 10) (by norm_num)
  rw [show ((10 : ℝ) ^ 2) = 100 by norm_num] at h
  rw [h]
  norm_num

private lemma rpow_hundred_neg_three_halves : (100 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 1000 := by
  have h := rpow_neg_three_halves (s := 10) (by norm_num)
  rw [show ((10 : ℝ) ^ 2) = 100 by norm_num] at h
  rw [h]
  norm_num

-- `hkZ_le` at `τ = 100`, `n = 0`: `h_100(0) ≤ C / 10`.
example : ∃ C : ℝ, hkZ 100 0 ≤ C * (1 / 10) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_le
  refine ⟨C, ?_⟩
  have h0 := h 100 (by norm_num) 0
  rw [rpow_hundred_neg_half] at h0
  norm_num at h0
  linarith

-- `hkZ_diff1_le` at `τ = 100`, `n = 0`: `|h_100(1) - h_100(0)| ≤ C / 100`.
example : ∃ C : ℝ, |hkZ 100 1 - hkZ 100 0| ≤ C / 100 := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_diff1_le
  refine ⟨C, ?_⟩
  have h0 := h 100 (by norm_num) 0
  norm_num at h0
  linarith

-- `hkZ_diff2_le` at `τ = 100`, `n = 0`: `|h_100(1) + h_100(-1) - 2 h_100(0)| ≤ C / 1000`.
example : ∃ C : ℝ, |hkZ 100 1 + hkZ 100 (-1) - 2 * hkZ 100 0| ≤ C / 1000 := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_diff2_le
  refine ⟨C, ?_⟩
  have h0 := h 100 (by norm_num) 0
  rw [rpow_hundred_neg_three_halves] at h0
  norm_num at h0
  linarith

-- `hkZ_le` at `τ = 100`, `n = 7`: the exponential factor `exp (-c · 49/100)` is nontrivial.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    hkZ 100 7 ≤ C * (1 / 10) * Real.exp (-(c * (49 / 100))) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_le
  refine ⟨C, c, hC, hc, ?_⟩
  have h0 := h 100 (by norm_num) 7
  rw [rpow_hundred_neg_half] at h0
  norm_num at h0
  linarith

-- `hkZ_diff1_le` at `τ = 100`, `n = 7`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkZ 100 8 - hkZ 100 7| ≤ C / 100 * Real.exp (-(c * (49 / 100))) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_diff1_le
  refine ⟨C, c, hC, hc, ?_⟩
  have h0 := h 100 (by norm_num) 7
  norm_num at h0
  linarith

-- `hkZ_diff2_le` at `τ = 100`, `n = 7`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkZ 100 8 + hkZ 100 6 - 2 * hkZ 100 7| ≤ C / 1000 * Real.exp (-(c * (49 / 100))) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_diff2_le
  refine ⟨C, c, hC, hc, ?_⟩
  have h0 := h 100 (by norm_num) 7
  rw [rpow_hundred_neg_three_halves] at h0
  norm_num at h0
  linarith

end RBM.Heat
