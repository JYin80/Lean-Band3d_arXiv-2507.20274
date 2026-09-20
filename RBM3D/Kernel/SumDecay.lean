/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import RBM3D.Defs.RadialSum
import RBM3D.Kernel.Evolution
import RBM3D.Kernel.PropT

/-!
# `(eq:latticesum_d3)`: the borderline lattice sum of Appendix A.2

The third proofreading round added one estimate to the paper that was not there before --
`(eq:latticesum_d3)`, used in the third step of `(eq:bddfA)`:

  `Σ_{b : |a₁-b| ∧ |a₂-b| > R} exp(-c|a₁-b|/ℓ_t) / (|a₁-b|^{d-2} |a₂-b|^{d-1})
      ≲ log L / R^{d-3}`,    for all `1 ≤ R ≤ L`,

for every `d ≥ 3`.  The original argument reached `W^{(n+4)ε}` directly at that step; in
`d = 3` the summand decays exactly like `|b|^{-d}` and the sum over `R ≤ |b| ≲ ℓ_t` costs a
logarithm, which is why the exponent became `W^{(n+5)ε}`.

This file proves it.  The proof does **not** split on `d = 3` versus `d ≥ 4`: for every
`b` in the sum, with `u = |a₁-b|` and `v = |a₂-b|`,

* if `v ≥ u/2` the summand is at most `2^{d-1} u^{-(2d-3)}`,
* if `v < u/2` then `u > 2v` and it is at most `v^{-(2d-3)}`,

so in both cases it is at most `2^{d-1}(u^{-(2d-3)} + v^{-(2d-3)})`, a sum of two radial
functions.  Summing each over spheres (`RBM.card_sphere_le`) leaves `Σ_{r>R} r^{2-d}`, and
`r^{2-d} = r^{-1} r^{3-d} ≤ r^{-1} R^{3-d}` for `r > R` reduces that to the harmonic sum
`Σ_{r ≤ M} r⁻¹ ≤ 1 + log M`.  The logarithm therefore appears for every `d` but is only
*needed* at `d = 3`, exactly as the paper says.

The exponential factor is carried along and bounded by `1`: the cutoff at `ℓ_t` is not
what produces the bound, the torus diameter is.
-/

namespace RBM

open Finset Real

/-! ### The harmonic sum -/

/-- `1/(M+1) ≤ log (M+1) - log M` for `M ≥ 1`. -/
theorem inv_succ_le_log_sub_log {M : ℕ} (hM : 1 ≤ M) :
    ((M : ℝ) + 1)⁻¹ ≤ Real.log ((M : ℝ) + 1) - Real.log M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  have hfrac : (0 : ℝ) < (M : ℝ) / ((M : ℝ) + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos hfrac
  rw [Real.log_div hM0.ne' hM1.ne'] at h
  have hval : (M : ℝ) / ((M : ℝ) + 1) - 1 = -(((M : ℝ) + 1)⁻¹) := by
    field_simp
    ring
  rw [hval] at h
  linarith

/-- `Σ_{r = 1}^{M} 1/r ≤ 1 + log M`. -/
theorem sum_inv_Icc_le (M : ℕ) : ∑ r ∈ Icc 1 M, ((r : ℝ))⁻¹ ≤ 1 + Real.log M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      have hstep := inv_succ_le_log_sub_log hM
      push_cast
      linarith

/-! ### The lattice sum -/

variable {L : ℕ} [NeZero L]

/-- The constant of `(eq:latticesum_d3)`. -/
noncomputable def latC (k : ℕ) : ℝ := 2 ^ (3 * k + 9) * (2 + Real.log ((k : ℝ) + 3))

theorem latC_pos (k : ℕ) : 0 < latC k := by
  unfold latC
  have : 0 ≤ Real.log ((k : ℝ) + 3) := Real.log_nonneg (by linarith)
  positivity

/-- A radial tail sum: `Σ_{|x| > R} |x|^{-(2k+3)} ≤ 2^{2k+5} R^{-k} (1 + log((k+3)L))`. -/
theorem sum_radial_tail_le (k : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    ∑ x : Zd (k + 3) L,
        (if R < zdistD (k + 3) L x then ((zdistD (k + 3) L x : ℝ) ^ (2 * k + 3))⁻¹ else 0)
      ≤ 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹ * (1 + Real.log (((k + 3) * L : ℕ) : ℝ)) := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  rw [sum_radial (k + 3)
    (fun r : ℕ => if R < r then ((r : ℝ) ^ (2 * k + 3))⁻¹ else 0)]
  -- termwise: sphere count times the radial weight
  have hterm : ∀ r ∈ range ((k + 3) * L + 1),
      (sphereCard (k + 3) L r : ℝ) * (if R < r then ((r : ℝ) ^ (2 * k + 3))⁻¹ else 0)
        ≤ 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹
          * (if r ∈ Icc 1 ((k + 3) * L) then ((r : ℝ))⁻¹ else 0) := by
    intro r hrange
    have hrL : r ≤ (k + 3) * L := by
      have := Finset.mem_range.mp hrange
      omega
    split_ifs with hr hmem hmem
    · -- `r > R`: the main term
      have hr1 : 1 ≤ r := by omega
      have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
      have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      have hcard : (sphereCard (k + 3) L r : ℝ) ≤ 2 ^ (k + 3) * ((r : ℝ) + 1) ^ (k + 2) := by
        exact_mod_cast card_sphere_le (L := L) (k + 2) r
      have hplus : ((r : ℝ) + 1) ^ (k + 2) ≤ 2 ^ (k + 2) * (r : ℝ) ^ (k + 2) := by
        calc ((r : ℝ) + 1) ^ (k + 2) ≤ (2 * (r : ℝ)) ^ (k + 2) :=
              pow_le_pow_left₀ (by linarith) (by linarith) _
          _ = 2 ^ (k + 2) * (r : ℝ) ^ (k + 2) := mul_pow _ _ _
      have hRk : ((r : ℝ) ^ k)⁻¹ ≤ ((R : ℝ) ^ k)⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_left₀ hR0.le (by exact_mod_cast hr.le) _
      have hne : (r : ℝ) ≠ 0 := ne_of_gt hr0
      have hsplit : ((r : ℝ) ^ (2 * k + 3))⁻¹
          = ((r : ℝ) ^ (k + 2))⁻¹ * (((r : ℝ) ^ k)⁻¹ * ((r : ℝ))⁻¹) := by
        field_simp
        ring
      rw [hsplit]
      calc (sphereCard (k + 3) L r : ℝ)
            * (((r : ℝ) ^ (k + 2))⁻¹ * (((r : ℝ) ^ k)⁻¹ * ((r : ℝ))⁻¹))
          ≤ (2 ^ (k + 3) * (2 ^ (k + 2) * (r : ℝ) ^ (k + 2)))
              * (((r : ℝ) ^ (k + 2))⁻¹ * (((r : ℝ) ^ k)⁻¹ * ((r : ℝ))⁻¹)) := by
            refine mul_le_mul_of_nonneg_right (hcard.trans ?_) (by positivity)
            exact mul_le_mul_of_nonneg_left hplus (by positivity)
        _ = 2 ^ (2 * k + 5) * (((r : ℝ) ^ k)⁻¹ * ((r : ℝ))⁻¹) := by
            field_simp
            ring
        _ ≤ 2 ^ (2 * k + 5) * (((R : ℝ) ^ k)⁻¹ * ((r : ℝ))⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hRk (by positivity)
        _ = 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹ * ((r : ℝ))⁻¹ := by ring
    · -- `r > R` but `r ∉ Icc 1 ((k+3)L)` cannot happen
      exact absurd (Finset.mem_Icc.mpr ⟨by omega, hrL⟩) hmem
    · -- `r ≤ R`: the left-hand side vanishes
      simp only [mul_zero]
      positivity
    · simp
  calc ∑ r ∈ range ((k + 3) * L + 1),
        (sphereCard (k + 3) L r : ℝ) * (if R < r then ((r : ℝ) ^ (2 * k + 3))⁻¹ else 0)
      ≤ ∑ r ∈ range ((k + 3) * L + 1), 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹
          * (if r ∈ Icc 1 ((k + 3) * L) then ((r : ℝ))⁻¹ else 0) := sum_le_sum hterm
    _ = 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹
          * ∑ r ∈ range ((k + 3) * L + 1),
            (if r ∈ Icc 1 ((k + 3) * L) then ((r : ℝ))⁻¹ else 0) := by rw [Finset.mul_sum]
    _ = 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹ * ∑ r ∈ Icc 1 ((k + 3) * L), ((r : ℝ))⁻¹ := by
        rw [← Finset.sum_filter]
        congr 2
        ext r
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        omega
    _ ≤ 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹ * (1 + Real.log (((k + 3) * L : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_Icc_le _) (by positivity)

omit [NeZero L] in
/-- `1 ≤ log L` for `L ≥ 3`, since `e < 3`. -/
theorem one_le_log_of_three_le (hL : 3 ≤ L) : (1 : ℝ) ≤ Real.log L := by
  have h3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) h3.le
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  exact hlog3.trans (Real.log_le_log (by norm_num) hL3)

/-- **`(eq:latticesum_d3)`**, the lattice sum added in the third proofreading round: for
`d = k + 3 ≥ 3`, `1 ≤ R` and `L ≥ 3`,

  `Σ_{b : |a₁-b| ∧ |a₂-b| > R} exp(-c|a₁-b|/ℓ) / (|a₁-b|^{d-2} |a₂-b|^{d-1})
      ≤ C_d · log L / R^{d-3}`.

The logarithm is what the borderline case `d = 3` costs; for `d ≥ 4` the factor `R^{3-d}`
already makes the sum converge, and the same proof gives both. -/
theorem latticesum_d3 (k : ℕ) {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {R : ℕ} (hR : 1 ≤ R)
    (hL : 3 ≤ L)
    (a₁ a₂ : Zd (k + 3) L) :
    ∑ b ∈ Finset.univ.filter (fun b : Zd (k + 3) L =>
          R < zdistD (k + 3) L (a₁ - b) ∧ R < zdistD (k + 3) L (a₂ - b)),
        Real.exp (-(c * (zdistD (k + 3) L (a₁ - b) : ℝ) / ℓ))
          / ((zdistD (k + 3) L (a₁ - b) : ℝ) ^ (k + 1)
            * (zdistD (k + 3) L (a₂ - b) : ℝ) ^ (k + 2))
      ≤ latC k * Real.log L / (R : ℝ) ^ k := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hRk : (0 : ℝ) < (R : ℝ) ^ k := by positivity
  -- the two radial tails
  set F : Zd (k + 3) L → ℝ := fun x =>
    (if R < zdistD (k + 3) L x then ((zdistD (k + 3) L x : ℝ) ^ (2 * k + 3))⁻¹ else 0) with hF
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    rw [hF]
    dsimp only
    split_ifs <;> positivity
  have htail := sum_radial_tail_le (L := L) k hR
  have hA : ∑ b : Zd (k + 3) L, F (a₁ - b)
      ≤ 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹ * (1 + Real.log (((k + 3) * L : ℕ) : ℝ)) := by
    rw [show ∑ b : Zd (k + 3) L, F (a₁ - b) = ∑ x : Zd (k + 3) L, F x from
      Fintype.sum_equiv (Equiv.subLeft a₁) _ _ fun b => rfl]
    exact htail
  have hB : ∑ b : Zd (k + 3) L, F (a₂ - b)
      ≤ 2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹ * (1 + Real.log (((k + 3) * L : ℕ) : ℝ)) := by
    rw [show ∑ b : Zd (k + 3) L, F (a₂ - b) = ∑ x : Zd (k + 3) L, F x from
      Fintype.sum_equiv (Equiv.subLeft a₂) _ _ fun b => rfl]
    exact htail
  -- pointwise bound on the filtered set
  have hpt : ∀ b ∈ Finset.univ.filter (fun b : Zd (k + 3) L =>
      R < zdistD (k + 3) L (a₁ - b) ∧ R < zdistD (k + 3) L (a₂ - b)),
      Real.exp (-(c * (zdistD (k + 3) L (a₁ - b) : ℝ) / ℓ))
          / ((zdistD (k + 3) L (a₁ - b) : ℝ) ^ (k + 1)
            * (zdistD (k + 3) L (a₂ - b) : ℝ) ^ (k + 2))
        ≤ 2 ^ (k + 2) * (F (a₁ - b) + F (a₂ - b)) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hu, hv⟩ := hb
    set u : ℝ := (zdistD (k + 3) L (a₁ - b) : ℝ) with hudef
    set v : ℝ := (zdistD (k + 3) L (a₂ - b) : ℝ) with hvdef
    have hu0 : 0 < u := by
      rw [hudef]; exact_mod_cast Nat.lt_of_lt_of_le hR (by omega : R ≤ zdistD (k + 3) L (a₁ - b))
    have hv0 : 0 < v := by
      rw [hvdef]; exact_mod_cast Nat.lt_of_lt_of_le hR (by omega : R ≤ zdistD (k + 3) L (a₂ - b))
    have hFu : F (a₁ - b) = (u ^ (2 * k + 3))⁻¹ := by
      rw [hF]; dsimp only; split_ifs; rfl
    have hFv : F (a₂ - b) = (v ^ (2 * k + 3))⁻¹ := by
      rw [hF]; dsimp only; split_ifs; rfl
    rw [hFu, hFv]
    have hexp : Real.exp (-(c * u / ℓ)) ≤ 1 ∨ True := Or.inr trivial
    have hnum : Real.exp (-(c * u / ℓ)) / (u ^ (k + 1) * v ^ (k + 2))
        ≤ (Real.exp (-(c * u / ℓ))) * ((u ^ (k + 1) * v ^ (k + 2))⁻¹) := by
      rw [div_eq_mul_inv]
    rcases le_total u (2 * v) with hcase | hcase
    · -- `v ≥ u/2`
      have hvu : u ^ (k + 2) ≤ 2 ^ (k + 2) * v ^ (k + 2) := by
        calc u ^ (k + 2) ≤ (2 * v) ^ (k + 2) := pow_le_pow_left₀ hu0.le hcase _
          _ = 2 ^ (k + 2) * v ^ (k + 2) := mul_pow _ _ _
      have hkey : (u ^ (k + 1) * v ^ (k + 2))⁻¹ ≤ 2 ^ (k + 2) * (u ^ (2 * k + 3))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div,
          div_le_iff₀ (by positivity)]
        calc u ^ (2 * k + 3) = u ^ (k + 1) * u ^ (k + 2) := by ring
          _ ≤ u ^ (k + 1) * (2 ^ (k + 2) * v ^ (k + 2)) :=
              mul_le_mul_of_nonneg_left hvu (by positivity)
          _ = 2 ^ (k + 2) * (u ^ (k + 1) * v ^ (k + 2)) := by ring
      calc Real.exp (-(c * u / ℓ)) / (u ^ (k + 1) * v ^ (k + 2))
          ≤ 1 / (u ^ (k + 1) * v ^ (k + 2)) := by
            apply div_le_div_of_nonneg_right ?_ (by positivity)
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
        _ = (u ^ (k + 1) * v ^ (k + 2))⁻¹ := by rw [one_div]
        _ ≤ 2 ^ (k + 2) * (u ^ (2 * k + 3))⁻¹ := hkey
        _ ≤ 2 ^ (k + 2) * ((u ^ (2 * k + 3))⁻¹ + (v ^ (2 * k + 3))⁻¹) := by
            have : (0 : ℝ) ≤ (v ^ (2 * k + 3))⁻¹ := by positivity
            have h2 : (0 : ℝ) < 2 ^ (k + 2) := by positivity
            nlinarith
    · -- `u > 2v`
      have huv : (2 * v) ^ (k + 1) ≤ u ^ (k + 1) := pow_le_pow_left₀ (by positivity) hcase _
      have hkey : (u ^ (k + 1) * v ^ (k + 2))⁻¹ ≤ 2 ^ (k + 2) * (v ^ (2 * k + 3))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div,
          div_le_iff₀ (by positivity)]
        calc v ^ (2 * k + 3) = v ^ (k + 1) * v ^ (k + 2) := by ring
          _ ≤ 2 ^ (k + 2) * (u ^ (k + 1) * v ^ (k + 2)) := by
              have h1 : v ^ (k + 1) ≤ 2 ^ (k + 2) * u ^ (k + 1) := by
                have h2 : (2 * v) ^ (k + 1) = 2 ^ (k + 1) * v ^ (k + 1) := mul_pow _ _ _
                have h3 : v ^ (k + 1) ≤ 2 ^ (k + 1) * v ^ (k + 1) := by
                  have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
                  nlinarith [pow_nonneg hv0.le (k + 1)]
                have h4 : 2 ^ (k + 1) * v ^ (k + 1) ≤ u ^ (k + 1) := by
                  rw [← h2]; exact huv
                have h5 : u ^ (k + 1) ≤ 2 ^ (k + 2) * u ^ (k + 1) := by
                  have : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
                  nlinarith [pow_nonneg hu0.le (k + 1)]
                linarith
              calc v ^ (k + 1) * v ^ (k + 2) ≤ (2 ^ (k + 2) * u ^ (k + 1)) * v ^ (k + 2) :=
                    mul_le_mul_of_nonneg_right h1 (by positivity)
                _ = 2 ^ (k + 2) * (u ^ (k + 1) * v ^ (k + 2)) := by ring
      calc Real.exp (-(c * u / ℓ)) / (u ^ (k + 1) * v ^ (k + 2))
          ≤ 1 / (u ^ (k + 1) * v ^ (k + 2)) := by
            apply div_le_div_of_nonneg_right ?_ (by positivity)
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
        _ = (u ^ (k + 1) * v ^ (k + 2))⁻¹ := by rw [one_div]
        _ ≤ 2 ^ (k + 2) * (v ^ (2 * k + 3))⁻¹ := hkey
        _ ≤ 2 ^ (k + 2) * ((u ^ (2 * k + 3))⁻¹ + (v ^ (2 * k + 3))⁻¹) := by
            have : (0 : ℝ) ≤ (u ^ (2 * k + 3))⁻¹ := by positivity
            have h2 : (0 : ℝ) < 2 ^ (k + 2) := by positivity
            nlinarith
  -- sum up
  calc ∑ b ∈ Finset.univ.filter (fun b : Zd (k + 3) L =>
        R < zdistD (k + 3) L (a₁ - b) ∧ R < zdistD (k + 3) L (a₂ - b)),
        Real.exp (-(c * (zdistD (k + 3) L (a₁ - b) : ℝ) / ℓ))
          / ((zdistD (k + 3) L (a₁ - b) : ℝ) ^ (k + 1)
            * (zdistD (k + 3) L (a₂ - b) : ℝ) ^ (k + 2))
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd (k + 3) L =>
          R < zdistD (k + 3) L (a₁ - b) ∧ R < zdistD (k + 3) L (a₂ - b)),
          2 ^ (k + 2) * (F (a₁ - b) + F (a₂ - b)) := Finset.sum_le_sum hpt
    _ ≤ ∑ b : Zd (k + 3) L, 2 ^ (k + 2) * (F (a₁ - b) + F (a₂ - b)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro b _ _
        have := hF0 (a₁ - b)
        have := hF0 (a₂ - b)
        positivity
    _ = 2 ^ (k + 2) * ((∑ b : Zd (k + 3) L, F (a₁ - b)) + ∑ b : Zd (k + 3) L, F (a₂ - b)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 ^ (k + 2) * (2 * (2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹
          * (1 + Real.log (((k + 3) * L : ℕ) : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ ≤ latC k * Real.log L / (R : ℝ) ^ k := by
      -- `1 + log((k+3)L) ≤ (2 + log(k+3)) log L`, using `1 ≤ log L`
      have hlogL : (1 : ℝ) ≤ Real.log L := one_le_log_of_three_le hL
      have hk0 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have hL0 : (0 : ℝ) < (L : ℝ) := by
        have : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
        linarith
      have hlogk : 0 ≤ Real.log ((k : ℝ) + 3) := Real.log_nonneg (by linarith)
      have hsplit : Real.log (((k + 3) * L : ℕ) : ℝ)
          = Real.log ((k : ℝ) + 3) + Real.log L := by
        push_cast
        rw [Real.log_mul hk0.ne' hL0.ne']
      have hbound : 1 + Real.log (((k + 3) * L : ℕ) : ℝ)
          ≤ (2 + Real.log ((k : ℝ) + 3)) * Real.log L := by
        rw [hsplit]
        nlinarith
      rw [latC, div_eq_mul_inv]
      have hpow : (2 : ℝ) ^ (k + 2) * (2 * 2 ^ (2 * k + 5)) = 2 ^ (3 * k + 8) := by
        rw [← pow_succ']
        rw [← pow_add]
        ring_nf
      have h89 : (2 : ℝ) ^ (3 * k + 8) ≤ 2 ^ (3 * k + 9) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc (2 : ℝ) ^ (k + 2) * (2 * (2 ^ (2 * k + 5) * ((R : ℝ) ^ k)⁻¹
            * (1 + Real.log (((k + 3) * L : ℕ) : ℝ))))
          = (2 ^ (k + 2) * (2 * 2 ^ (2 * k + 5)))
            * ((1 + Real.log (((k + 3) * L : ℕ) : ℝ)) * ((R : ℝ) ^ k)⁻¹) := by ring
        _ = 2 ^ (3 * k + 8) * ((1 + Real.log (((k + 3) * L : ℕ) : ℝ)) * ((R : ℝ) ^ k)⁻¹) := by
            rw [hpow]
        _ ≤ 2 ^ (3 * k + 9) * (((2 + Real.log ((k : ℝ) + 3)) * Real.log L) * ((R : ℝ) ^ k)⁻¹) := by
            apply mul_le_mul h89 _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right hbound (by positivity)
        _ = 2 ^ (3 * k + 9) * (2 + Real.log ((k : ℝ) + 3)) * Real.log L * ((R : ℝ) ^ k)⁻¹ := by
            ring

/-! ### `(eq:decomp_U2)` and `(eq:decayXi)`: the two ingredients of `lem:sum_decay`

`(eq:decompUalt)` writes each one-index factor of `U^(n)` as `1 + Ξ^(i)`.  Expanding the
product over the `n` indices gives `(eq:decomp_U2)`,

  `(U^(n) ∘ 𝒜)_a = Σ_{A ⊆ [n]} Σ_b ∏_{i∈A} δ_{a_i b_i} ∏_{i∉A} Ξ^(i)_{a_i b_i} 𝒜_b`,

and `(eq:decayXi)` bounds a single entry of `Ξ^(i)` using `(prop:ThfadC)`. -/

section Xi

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `Ξ^(i) = (t-s) M^{(σ_i,σ_{i+1})} S^(B) Θ_t` of `(eq:decompUalt)`. -/
noncomputable def XiKer (d L : ℕ) [NeZero L] (g : ℝ) (μ : ℂ) (s t : ℝ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  (((t : ℂ) - s) * μ) • (SB d L g * Theta d L g ((t : ℂ) * μ))

theorem uKer_eq_one_add_XiKer {μ : ℂ} {s t : ℝ} (hL : 3 ≤ L) (hξ : ‖(t : ℂ) * μ‖ < 1) :
    uKer d L g μ s t = 1 + XiKer d L g μ s t :=
  uKer_eq_one_add hL hξ

omit [NeZero L] in
/-- `S^(B)(g)` is supported on the nearest neighbours: its entry vanishes beyond
distance `1`. -/
theorem SB_apply_eq_zero_of_one_lt {a b : Zd d L} (h : 1 < zdistD d L (a - b)) :
    SB d L g a b = 0 := by
  rw [SB_apply, sbKernel]
  have h0 : a - b ≠ 0 := by
    intro hab
    rw [hab, zdistD_zero] at h
    omega
  simp only [h0, ite_false, show ¬(zdistD d L (a - b) = 1) by omega, ite_false]

/-- **`(eq:decomp_U2)`**: expanding `∏_i (δ + Ξ^(i))` over subsets. -/
theorem UN_apply_eq_sum_powerset {n : ℕ} {m : Fin n → ℂ} (hL : 3 ≤ L)
    (hm : ∀ i, ‖m i‖ = 1) {s t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (𝒜 : (Fin n → Zd d L) → ℂ) (a : Fin n → Zd d L) :
    UN d L g m s t 𝒜 a
      = ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ b : Fin n → Zd d L,
          ((∏ i ∈ A, (1 : Matrix (Zd d L) (Zd d L) ℂ) (a i) (b i))
            * ∏ i ∈ Finset.univ \ A, XiKer d L g (cycProd m i) s t (a i) (b i)) * 𝒜 b := by
  have hfac : ∀ i : Fin n, uKer d L g (cycProd m i) s t
      = 1 + XiKer d L g (cycProd m i) s t := fun i =>
    uKer_eq_one_add_XiKer hL (norm_t_mul_lt_one ht0 ht1 (norm_cycProd hm i))
  rw [UN_eq_tensorKer, tensorKer]
  simp only [hfac]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show (∏ i, ((1 : Matrix (Zd d L) (Zd d L) ℂ) + XiKer d L g (cycProd m i) s t) (a i) (b i))
      = ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ A, (1 : Matrix (Zd d L) (Zd d L) ℂ) (a i) (b i))
          * ∏ i ∈ Finset.univ \ A, XiKer d L g (cycProd m i) s t (a i) (b i) from
    Finset.prod_add _ _ _]
  rw [Finset.sum_mul]

/-- **`(eq:decayXi)`**: a single entry of `Ξ^(i)` inherits the decay of `(prop:ThfadC)`,

  `|Ξ^(i)_{ab}| ≤ C (1-s) (g²+|1-t|)⁻¹ (|a-b|+1)^{-(d-2)} e^{-c|a-b|/ℓ_t}`.

The zero-mode part of `B_{t,|a-b|}` is absorbed into the decay term, which is legitimate
in the regime `t ≤ 1 - g²/L²` that `lem:sum_decay` assumes; the nearest-neighbour support
of `S^(B)` moves the profile from `|c-b|` to `|a-b|` at the cost of a constant. -/
theorem norm_XiKer_apply_le {k : ℕ} {μ : ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hμ : ‖μ‖ = 1)
    (hdecay : ThetaDecay (k + 2) g μ) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 →
      g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
      haveI : NeZero L := ⟨by omega⟩
      ∀ a b : Zd (k + 2) L,
        ‖XiKer (k + 2) L g μ s t a b‖
          ≤ C * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
            * (((zdistD (k + 2) L (a - b) : ℝ) + 1) ^ k)⁻¹
            * Real.exp (-(c * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t) := by
  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := hdecay hd hg hμ
  -- constants: the zero-mode absorption, the shift by one lattice step, and the exponential
  refine ⟨Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * 2 ^ k * Real.exp cd, by positivity,
    cd, hcd, ?_⟩
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

end Xi


/-! ### One `Ξ` factor, summed over the fast-decay ball

This is the accounting step at the heart of `lem:sum_decay`, and the one place where a
shortcut gives the wrong answer.  Bounding a factor by `‖Ξ‖_{∞→∞} ≤ (t-s)/(1-t)` and
summing freely produces `((t-s)/(1-t))^{n-k}`, which is **weaker** than the
`((ĝ²+|1-s|)/(ĝ²+|1-t|))^{n-k}` the lemma claims.  The claimed shape comes out only if
the sum is restricted to the ball `|a-b| ≲ ℓ_s` supplied by `(deccA0)`, where

* the entries obey `(eq:decayXi)`: `|Ξ(a,b)| ≲ (1-s)(ĝ²+|1-t|)^{-1}(|a-b|+1)^{-(d-2)}`;
* the polynomial factor sums to `≍ R²` over that ball (`RBM.sum_ball_min_pow_le`, whose
  truncated form lets the centre of the ball differ from the centre of the factor);
* and `R ≍ ℓ_s` turns `(1-s)ℓ_s²` into `ĝ²+|1-s|` (`RBM.one_sub_mul_ellT_sq_le`).

The three together give exactly one factor of `(ĝ²+|1-s|)/(ĝ²+|1-t|)`, with `Λ²` standing
for the paper's `W^{Cε}`.
-/

/-- **One factor of `(sum_res_1)`.**  For any set `D` of summation points inside the ball
of radius `R ≤ Λ ℓ_s` around `a`,

`Σ_{b ∈ D} |Ξ_{s,t}(a,b)| ≤ C Λ² (ĝ²+|1-s|)/(ĝ²+|1-t|)`,

with `C` depending only on `d` and the constants of `(prop:ThfadC)`. -/
theorem sum_ball_norm_XiKer_le {k : ℕ} {μ : ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hμ : ‖μ‖ = 1)
    (hdecay : ThetaDecay (k + 2) g μ) :
    ∃ C > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 →
      g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t → ∀ Λ : ℝ, 1 ≤ Λ → ∀ R : ℝ, 1 ≤ R →
      R ≤ Λ * ellT L g s →
      haveI : NeZero L := ⟨by omega⟩
      ∀ (a ctr : Zd (k + 2) L) (D : Finset (Zd (k + 2) L)),
        (∀ b ∈ D, ((zdistD (k + 2) L (ctr - b) : ℕ) : ℝ) ≤ R) →
        ∑ b ∈ D, ‖XiKer (k + 2) L g μ s t a b‖
          ≤ C * Λ ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) := by
  obtain ⟨C₀, hC₀, c, hc, hbd⟩ := norm_XiKer_apply_le (g := g) hd hg hμ hdecay
  refine ⟨4 * C₀ * ballC k, mul_pos (by positivity) (ballC_pos k), ?_⟩
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


/-! ### The product over the factors: `(sum_res_1_red0)`'s combinatorial core

`(eq:decomp_U2)` expands `U^(n) ∘ 𝒜` over subsets `A ⊂ [n]`: the indices in `A` contribute
a Kronecker delta and those outside contribute a factor `Ξ^(i)`.  The fast-decay property
`(deccA0)` confines the summation variables `b_i` to a ball of radius `≍ W^ε ℓ_s` (around
`a_1`, which is pinned by a delta when `A ≠ ∅`), and inside that ball each factor costs
`C Λ² (ĝ²+|1-s|)/(ĝ²+|1-t|)` by `sum_ball_norm_XiKer_le`.

What is left is to see that the sum of the products is the product of the sums.  That is
`Finset.prod_univ_sum`, and it is the content of the two lemmas below; the first is stated
for an arbitrary non-negative family, because nothing about `Ξ` is used.
-/

/-- The sum over a product region of a product of non-negative factors is at most the
product of the individual sums, hence at most `M^n` when each sum is at most `M`. -/
theorem sum_prod_le_pow {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    (D : Finset α) (F : ι → α → ℝ) (hF : ∀ i, ∀ b ∈ D, 0 ≤ F i b) {M : ℝ}
    (hsum : ∀ i, ∑ b ∈ D, F i b ≤ M) :
    ∑ β ∈ Fintype.piFinset fun _ : ι => D, ∏ i, F i (β i) ≤ M ^ Fintype.card ι := by
  rw [← Finset.prod_univ_sum]
  calc ∏ i : ι, ∑ b ∈ D, F i b ≤ ∏ _i : ι, M :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun b hb => hF i b hb)
          (fun i _ => hsum i)
    _ = M ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

/-- **One subset's worth of factors.**  With the summation variables confined to a ball of
radius `R ≤ Λ ℓ_s` -- around whichever point `(deccA0)` pins down, not necessarily the
centre of any single factor -- the `Ξ`-factors of `(eq:decomp_U2)` cost

`(C Λ² (ĝ²+|1-s|)/(ĝ²+|1-t|))^k`

in total, which is the shape claimed in `(sum_res_1_red0)` with `Λ²` standing for the
paper's `W^{Cε}`. -/
theorem sum_prod_norm_XiKer_le {k n : ℕ} {μ : Fin n → ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g)
    (hμ : ∀ i, ‖μ i‖ = 1) (hdecay : ∀ i, ThetaDecay (k + 2) g (μ i)) :
    ∃ C > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 →
      g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t → ∀ Λ : ℝ, 1 ≤ Λ → ∀ R : ℝ, 1 ≤ R →
      R ≤ Λ * ellT L g s →
      haveI : NeZero L := ⟨by omega⟩
      ∀ (ctr : Zd (k + 2) L) (D : Finset (Zd (k + 2) L)),
        (∀ b ∈ D, ((zdistD (k + 2) L (ctr - b) : ℕ) : ℝ) ≤ R) →
        ∀ (a : Fin n → Zd (k + 2) L),
        ∑ β ∈ Fintype.piFinset fun _ : Fin n => D,
            ∏ i : Fin n, ‖XiKer (k + 2) L g (μ i) s t (a i) (β i)‖
          ≤ (C * Λ ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))) ^ n := by
  have hbd : ∀ i : Fin n, ∃ C > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t →
      t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t → ∀ Λ : ℝ, 1 ≤ Λ → ∀ R : ℝ, 1 ≤ R →
      R ≤ Λ * ellT L g s →
      haveI : NeZero L := ⟨by omega⟩
      ∀ (a ctr : Zd (k + 2) L) (D : Finset (Zd (k + 2) L)),
        (∀ b ∈ D, ((zdistD (k + 2) L (ctr - b) : ℕ) : ℝ) ≤ R) →
        ∑ b ∈ D, ‖XiKer (k + 2) L g (μ i) s t a b‖
          ≤ C * Λ ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) := fun i =>
    sum_ball_norm_XiKer_le (g := g) hd hg (hμ i) (hdecay i)
  choose C hC hCbd using hbd
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, ?_⟩
    intro L hL s t hs hst ht hgt Λ hΛ R hR hRℓ ctr D hD a
    simp
  · have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hsup : ∀ i, C i ≤ ⨆ j, C j := fun i => le_ciSup (Finite.bddAbove_range _) i
    refine ⟨⨆ j, C j, lt_of_lt_of_le (hC hne.some) (hsup hne.some), ?_⟩
    intro L hL s t hs hst ht hgt Λ hΛ R hR hRℓ ctr D hD a
    have : NeZero L := ⟨by omega⟩
    have hratio : (0 : ℝ) ≤ (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|) := by positivity
    refine le_trans (sum_prod_le_pow D (fun i b => ‖XiKer (k + 2) L g (μ i) s t (a i) b‖)
      (fun i b _ => norm_nonneg _) (M := (⨆ j, C j) * Λ ^ 2
        * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))) ?_) (le_of_eq (by rw [Fintype.card_fin]))
    intro i
    refine le_trans (hCbd i L hL s t hs hst ht hgt Λ hΛ R hR hRℓ (a i) ctr D hD) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hsup i) (by positivity)) hratio

end RBM
