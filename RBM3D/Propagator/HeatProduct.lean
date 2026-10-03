/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.HeatTorus1D
import RBM3D.Propagator.LaplaceGauss
import RBM3D.Propagator.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The product kernel `K_τ(a) = ∏_j hk(τ, a_j)` and the Laplace representation of `Θ_t`

Route H, ticket T2019 (design `docs/reports/T2003-prove.md` b8 rows S1, S4 and ticket D; Fable
review `docs/claude-team/fable/2026-10-02-routeH.md` §1 F1, F4, §2 S4).

## Main definitions

* `RBM.Heat.kProd`: `K_τ(a) = ∏_j hk(τ, a_j)` on `ℤ_L^d`.

## Main results

* `RBM.Heat.Theta_eq_laplace_prod` (F1, exact): for `3 ≤ L`, `g > 0` and real `t ∈ [0, 1)`,
  `Θ_t(0, a) = ∫₀^∞ e^{-(1-t)s} K_{γs}(a) ds` with `γ = t g²/(1 + 2dg²) = lgGam d g t`.
  Route (b) of the ticket: with `m(y,z) = δ_{yz} - t S^(B)_{yz}` one has, from `s₀(1 + 2dg²) = 1`,
  `Σ_y K_τ(y-x) m(y,z) = (1-t) K_τ(a) - γ ∂_τ K_τ(a)`, `a = z - x`, and the heat equation
  `∂_τ hk(τ,x) = hk(τ,x+1) + hk(τ,x-1) - 2 hk(τ,x)` (direct differentiation of the finite
  Fourier sum defining `hkT`); integration by parts in `s` gives `∫₀^∞ e^{-es}((1-t)K - γ ∂_τ K) ds
  = K_0(a) = δ_{a,0}`, i.e. the matrix `B(x,y) = ∫ e^{-es} K_{γs}(y - x) ds` is a left inverse of
  `1 - t S^(B)`, and `eq_Theta_of_mul` identifies it with `Θ_t`.
* `RBM.Heat.sum_min_ge` (F4): `(1/d) min(X²/τ, X) ≤ Σ_j min(x_j²/τ, x_j)`, `X = Σ_j x_j`
  (the version without `1/d` is false).
* `RBM.Heat.kProd_le`, `kProd_diff1_le`, `kProd_diff2_le` (`τ ≤ L²`): the product bound and its unit
  first and second differences, exponents `d/2`, `(d+1)/2`, `(d+2)/2`, Gaussian/exponential loss
  with `c/d` (from `sum_min_ge`).
* `RBM.Heat.kProd_gap` (`τ ≥ L²`): the zero mode `L^{-d}` and the gap, for the kernel and its unit
  differences.

The one-dimensional inputs are the merged `hkT_le`, `hkT_diff1_le`, `hkT_diff2_le`, `hkT_gap`,
`hkT_mass`.  The private lemmas `hp_cos_phase`, `hkT_rep`, `hp_sum_exp_orth`, `hp_sum_cos_orth`
re-prove (with the file stem as prefix) the private lemmas `cos_phase`, `hkT_form`, `sum_exp_orth`,
`sum_cos_orth` of `HeatTorus1D.lean` / `HeatKernel1D.lean`.  Nothing is copied from `RBM1D` or
`RBM2D`.
-/

open MeasureTheory Set Filter Topology

namespace RBM.Heat

/-! ### The `1/d` sum-of-minima lemma -/

private lemma min_sq_ge_linear {τ x : ℝ} (hτ : 0 < τ) (hx : 0 ≤ x) (d : ℕ) (hd : 1 ≤ d) :
    x / d - τ / (4 * (d : ℝ) ^ 2) ≤ min (x ^ 2 / τ) x := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  refine le_min ?_ ?_
  · -- `x²/τ ≥ x/d - τ/(4d²)`: `(x/√τ - √τ/(2d))² ≥ 0`
    have h : 0 ≤ (d : ℝ) * (2 * d * x - τ) ^ 2 := mul_nonneg hdpos.le (sq_nonneg _)
    rw [div_sub_div _ _ hdpos.ne' (by positivity), div_le_div_iff₀ (by positivity) hτ]
    nlinarith [h]
  · have : x / d ≤ x := div_le_self hx hd'
    have h2 : 0 ≤ τ / (4 * (d : ℝ) ^ 2) := by positivity
    linarith

theorem sum_min_ge : ∀ d : ℕ, 1 ≤ d → ∀ τ : ℝ, 0 < τ → ∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j) →
    (d : ℝ)⁻¹ * min ((∑ j, x j) ^ 2 / τ) (∑ j, x j) ≤ ∑ j, min (x j ^ 2 / τ) (x j) := by
  intro d hd τ hτ x hx
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  by_cases hall : ∀ j, x j ≤ τ
  · -- Cauchy–Schwarz
    have h1 : ∀ j, min (x j ^ 2 / τ) (x j) = x j ^ 2 / τ := by
      intro j
      refine min_eq_left ?_
      rw [div_le_iff₀ hτ]
      nlinarith [hall j, hx j]
    simp_rw [h1]
    have hcs : (∑ j, x j) ^ 2 ≤ (d : ℝ) * ∑ j, x j ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := x)
      simpa using this
    calc (d : ℝ)⁻¹ * min ((∑ j, x j) ^ 2 / τ) (∑ j, x j)
        ≤ (d : ℝ)⁻¹ * ((∑ j, x j) ^ 2 / τ) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (inv_nonneg.2 hdpos.le)
      _ ≤ (d : ℝ)⁻¹ * ((d : ℝ) * ∑ j, x j ^ 2) / τ := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcs hτ.le)
            (inv_nonneg.2 hdpos.le)
      _ = ∑ j, x j ^ 2 / τ := by
          rw [← Finset.sum_div, inv_mul_cancel_left₀ hdpos.ne']
  · push Not at hall
    obtain ⟨j₀, hj₀⟩ := hall
    have hX : (0 : ℝ) ≤ ∑ j, x j := Finset.sum_nonneg fun j _ => hx j
    have hf0 : min (x j₀ ^ 2 / τ) (x j₀) = x j₀ := by
      refine min_eq_right ?_
      rw [le_div_iff₀ hτ]
      nlinarith [hj₀, hx j₀]
    have hrest : ∑ j ∈ Finset.univ.erase j₀, (x j / d - τ / (4 * (d : ℝ) ^ 2))
        ≤ ∑ j ∈ Finset.univ.erase j₀, min (x j ^ 2 / τ) (x j) :=
      Finset.sum_le_sum fun j _ => min_sq_ge_linear hτ (hx j) d hd
    have hsplit : ∑ j, min (x j ^ 2 / τ) (x j)
        = min (x j₀ ^ 2 / τ) (x j₀) + ∑ j ∈ Finset.univ.erase j₀, min (x j ^ 2 / τ) (x j) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j₀)).symm
    have hsx : ∑ j, x j = x j₀ + ∑ j ∈ Finset.univ.erase j₀, x j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j₀)).symm
    have hlin : ∑ j ∈ Finset.univ.erase j₀, (x j / d - τ / (4 * (d : ℝ) ^ 2))
        = (∑ j ∈ Finset.univ.erase j₀, x j) / d
          - ((d : ℝ) - 1) * (τ / (4 * (d : ℝ) ^ 2)) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_erase_of_mem
        (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_sub hd]
      simp
    have hmin : min ((∑ j, x j) ^ 2 / τ) (∑ j, x j) ≤ ∑ j, x j := min_le_right _ _
    have hmain : (∑ j, x j) / d ≤ ∑ j, min (x j ^ 2 / τ) (x j) := by
      rw [hsplit, hf0]
      have h3 : (∑ j, x j) / d = x j₀ / d + (∑ j ∈ Finset.univ.erase j₀, x j) / d := by
        rw [hsx, add_div]
      have h4 : ((d : ℝ) - 1) * (τ / (4 * (d : ℝ) ^ 2)) ≤ (1 - 1 / d) * x j₀ := by
        have : ((d : ℝ) - 1) * (τ / (4 * (d : ℝ) ^ 2)) ≤ ((d : ℝ) - 1) * (τ / d) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine div_le_div_of_nonneg_left hτ.le hdpos ?_
          nlinarith
        have h5 : ((d : ℝ) - 1) * (τ / d) = (1 - 1 / d) * τ := by field_simp
        rw [h5] at this
        have h6 : 0 ≤ 1 - 1 / (d : ℝ) := by
          rw [sub_nonneg, div_le_one hdpos]; exact hd'
        calc _ ≤ (1 - 1 / (d : ℝ)) * τ := this
          _ ≤ (1 - 1 / d) * x j₀ := mul_le_mul_of_nonneg_left hj₀.le h6
      have h7 : x j₀ = x j₀ / d + (1 - 1 / d) * x j₀ := by field_simp; ring
      linarith
    calc (d : ℝ)⁻¹ * min ((∑ j, x j) ^ 2 / τ) (∑ j, x j)
        ≤ (d : ℝ)⁻¹ * ∑ j, x j := mul_le_mul_of_nonneg_left hmin (inv_nonneg.2 hdpos.le)
      _ = (∑ j, x j) / d := by rw [inv_mul_eq_div]
      _ ≤ _ := hmain

/-! ### Product bounds from one-dimensional bounds -/

/-- `min 1 τ^{-1/2}`, the one-dimensional decay factor. -/
private noncomputable def hpU (τ : ℝ) : ℝ := min 1 (τ ^ (-(1 / 2 : ℝ)))

private lemma hpU_nonneg (τ : ℝ) (hτ : 0 < τ) : 0 ≤ hpU τ :=
  le_min zero_le_one (Real.rpow_nonneg hτ.le _)

private lemma hpU_pow {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    hpU τ ^ n = min 1 (τ ^ (-(n : ℝ) / 2)) := by
  have hy : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ.le _
  have hyn : (τ ^ (-(1 / 2 : ℝ))) ^ n = τ ^ (-(n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    congr 1
    ring
  rw [← hyn, hpU]
  rcases le_total (τ ^ (-(1 / 2 : ℝ))) 1 with h | h
  · rw [min_eq_right h, min_eq_right (pow_le_one₀ hy h)]
  · rw [min_eq_left h, min_eq_left (one_le_pow₀ h), one_pow]

private lemma min_one_inv_eq {τ : ℝ} (hτ : 0 < τ) : min 1 τ⁻¹ = hpU τ ^ 2 := by
  rw [hpU_pow hτ 2]
  congr 1
  rw [show -((2 : ℕ) : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]

private lemma min_one_rpow_three {τ : ℝ} (hτ : 0 < τ) :
    min 1 (τ ^ (-(3 / 2 : ℝ))) = hpU τ ^ 3 := by
  rw [hpU_pow hτ 3]
  congr 2
  norm_num

private lemma prod_bound {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) {A c : ℝ} (hA : 0 ≤ A)
    (hc : 0 < c) (n : Fin d → ℕ) (F x : Fin d → ℝ) (hx : ∀ k, 0 ≤ x k)
    (hF : ∀ k, |F k| ≤ A * hpU τ ^ n k * Real.exp (-c * min (x k ^ 2 / τ) (x k))) :
    |∏ k, F k| ≤ A ^ d * hpU τ ^ (∑ k, n k)
      * Real.exp (-(c / d) * min ((∑ k, x k) ^ 2 / τ) (∑ k, x k)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ∏ k, |F k| ≤ ∏ k, (A * hpU τ ^ n k * Real.exp (-c * min (x k ^ 2 / τ) (x k))) :=
    Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) (fun k _ => hF k)
  have h2 : ∏ k, (A * hpU τ ^ n k * Real.exp (-c * min (x k ^ 2 / τ) (x k)))
      = A ^ d * hpU τ ^ (∑ k, n k) * Real.exp (-c * ∑ k, min (x k ^ 2 / τ) (x k)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum, ← Real.exp_sum, ← Finset.mul_sum]
  have hsm := sum_min_ge d hd τ hτ x hx
  have hexp : Real.exp (-c * ∑ k, min (x k ^ 2 / τ) (x k))
      ≤ Real.exp (-(c / d) * min ((∑ k, x k) ^ 2 / τ) (∑ k, x k)) := by
    apply Real.exp_le_exp.mpr
    have : (c / d) * min ((∑ k, x k) ^ 2 / τ) (∑ k, x k) ≤ c * ∑ k, min (x k ^ 2 / τ) (x k) := by
      calc (c / d) * min ((∑ k, x k) ^ 2 / τ) (∑ k, x k)
          = c * ((d : ℝ)⁻¹ * min ((∑ k, x k) ^ 2 / τ) (∑ k, x k)) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ c * ∑ k, min (x k ^ 2 / τ) (x k) := mul_le_mul_of_nonneg_left hsm hc.le
    linarith
  have hu := hpU_nonneg τ hτ
  have hAu : 0 ≤ A ^ d * hpU τ ^ (∑ k, n k) := by positivity
  rw [Finset.abs_prod]
  calc ∏ k, |F k| ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hAu

/-- `n ↦ min (n²/τ) n` moves by at most `3` under a unit shift of `n`. -/
private lemma f_shift {τ n n' : ℝ} (hτ : 0 < τ) (hn : 0 ≤ n) (hn' : 0 ≤ n') (h : n ≤ n' + 1) :
    min (n ^ 2 / τ) n ≤ min (n' ^ 2 / τ) n' + 3 := by
  have h1 : min (n ^ 2 / τ) n ≤ n := min_le_right _ _
  have h2 : min (n ^ 2 / τ) n ≤ n ^ 2 / τ := min_le_left _ _
  have hf' : 0 ≤ min (n' ^ 2 / τ) n' := le_min (by positivity) hn'
  rcases le_total τ n' with hτn | hτn
  · have : min (n' ^ 2 / τ) n' = n' := min_eq_right (by rw [le_div_iff₀ hτ]; nlinarith)
    rw [this]
    linarith
  · have : min (n' ^ 2 / τ) n' = n' ^ 2 / τ := min_eq_left (by rw [div_le_iff₀ hτ]; nlinarith)
    rw [this]
    rcases lt_or_ge τ 1 with hτ1 | hτ1
    · have : 0 ≤ n' ^ 2 / τ := by positivity
      linarith
    · have h3 : n ^ 2 / τ ≤ n' ^ 2 / τ + 3 := by
        rw [div_le_iff₀ hτ, add_mul, div_mul_cancel₀ _ hτ.ne']
        nlinarith
      linarith

/-- Telescoping bound for a difference of products with a common sup bound `M`. -/
private lemma abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {x y : ι → ℝ}
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η) (hx : ∀ i ∈ s, |x i| ≤ M) (hy : ∀ i ∈ s, |y i| ≤ M)
    (hxy : ∀ i ∈ s, |x i - y i| ≤ η * M) :
    |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ (s.card : ℝ) * M ^ s.card * η := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (fun i hi => hy i (Finset.mem_insert_of_mem hi))
      (fun i hi => hxy i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hQ : |∏ i ∈ s, y i| ≤ M ^ s.card := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ s, |y i| ≤ ∏ _i ∈ s, M :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
              (fun i hi => hy i (Finset.mem_insert_of_mem hi))
        _ = M ^ s.card := Finset.prod_const _
    have hxa := hx a (Finset.mem_insert_self a s)
    have hxya := hxy a (Finset.mem_insert_self a s)
    calc |x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i|
        = |x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i| := by ring_nf
      _ ≤ |x a| * |∏ i ∈ s, x i - ∏ i ∈ s, y i| + |x a - y a| * |∏ i ∈ s, y i| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ M * ((s.card : ℝ) * M ^ s.card * η) + (η * M) * M ^ s.card := by
          gcongr
      _ = (((s.card + 1 : ℕ) : ℝ)) * M ^ (s.card + 1) * η := by
          push_cast
          ring

/-- Product of per-factor gap bounds. -/
private lemma gap_prod {d : ℕ} {Lr δ A' : ℝ} (hLr : 0 < Lr) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : 0 ≤ A')
    (m e : Fin d → ℕ) (hesum : 1 ≤ ∑ k, e k) (F : Fin d → ℝ)
    (hF : ∀ k, |F k| ≤ A' * (Lr⁻¹) ^ m k * δ ^ e k) :
    |∏ k, F k| ≤ A' ^ d * (Lr⁻¹) ^ (∑ k, m k) * δ := by
  rw [Finset.abs_prod]
  have h1 : ∏ k, |F k| ≤ ∏ k, (A' * (Lr⁻¹) ^ m k * δ ^ e k) :=
    Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) (fun k _ => hF k)
  have h2 : ∏ k, (A' * (Lr⁻¹) ^ m k * δ ^ e k)
      = A' ^ d * (Lr⁻¹) ^ (∑ k, m k) * δ ^ (∑ k, e k) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  have h3 : δ ^ (∑ k, e k) ≤ δ := pow_le_of_le_one hδ0.le hδ1 (by omega)
  refine h1.trans (h2.le.trans ?_)
  have : 0 ≤ A' ^ d * (Lr⁻¹) ^ (∑ k, m k) := by positivity
  exact mul_le_mul_of_nonneg_left h3 this

/-! ### The product kernel and its factorisation -/

/-- The product kernel `K_τ(a) = ∏_j hk(τ, a_j)` on `ℤ_L^d` (route H, step S4). -/
noncomputable def kProd (d L : ℕ) [NeZero L] (τ : ℝ) (a : Zd d L) : ℝ := ∏ j, hkT L τ (a j)

section Prod

variable {d L : ℕ} [NeZero L]

private lemma kProd_single (τ : ℝ) (a : Zd d L) (j : Fin d) (c : ZMod L) :
    kProd d L τ (a + Pi.single j c)
      = hkT L τ (a j + c) * ∏ k ∈ Finset.univ.erase j, hkT L τ (a k) := by
  unfold kProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl (fun k hk => ?_)
    simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk)]

private lemma kProd_split (τ : ℝ) (a : Zd d L) (j : Fin d) :
    kProd d L τ a = hkT L τ (a j) * ∏ k ∈ Finset.univ.erase j, hkT L τ (a k) := by
  have := kProd_single τ a j 0
  simpa using this

private lemma kProd_two {i j : Fin d} (hij : i ≠ j) (τ : ℝ) (a : Zd d L) (ci cj : ZMod L) :
    kProd d L τ (a + Pi.single i ci + Pi.single j cj)
      = hkT L τ (a i + ci) * hkT L τ (a j + cj)
        * ∏ k ∈ (Finset.univ.erase i).erase j, hkT L τ (a k) := by
  unfold kProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _
      (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc]
  congr 1
  · congr 1
    · simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hij.symm]
  · refine Finset.prod_congr rfl (fun k hk => ?_)
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

private lemma prod_ite_split (j : Fin d) (P Q : Fin d → ℝ) :
    ∏ k, (if k = j then P k else Q k) = P j * ∏ k ∈ Finset.univ.erase j, Q k := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [ite_true]
  congr 1
  exact Finset.prod_congr rfl (fun k hk => by simp [Finset.ne_of_mem_erase hk])

private lemma prod_ite_split2 {i j : Fin d} (hij : i ≠ j) (P Q R : Fin d → ℝ) :
    ∏ k, (if k = i then P k else if k = j then Q k else R k)
      = P i * Q j * ∏ k ∈ (Finset.univ.erase i).erase j, R k := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _
      (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc]
  simp only [ite_true, hij.symm, ite_false]
  congr 1
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have hkj := Finset.ne_of_mem_erase hk
  have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
  simp [hki, hkj]

omit [NeZero L] in
private lemma sum_zdist_cast (a : Zd d L) :
    ∑ k, ((zdist L (a k) : ℕ) : ℝ) = (zdistD d L a : ℝ) := by
  simp [zdistD]

private lemma zdist_succ_le (x : ZMod L) : zdist L x ≤ zdist L (x + 1) + 1 := by
  have h := zdist_add_le L (x + 1) (-1)
  rw [add_neg_cancel_right, zdist_neg] at h
  have h1 : zdist L 1 ≤ 1 := by
    unfold zdist
    refine (min_le_left _ _).trans ?_
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_le _ _
  omega

/-! ### One common triple of one-dimensional constants, in the shape needed by `prod_bound` -/

private lemma factor_bounds : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ x : ZMod L,
      hkT L τ x ≤ A * hpU τ ^ 1
        * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) ∧
      |hkT L τ (x + 1) - hkT L τ x| ≤ A * hpU τ ^ 2
        * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) ∧
      |hkT L τ (x + 1 + 1) - 2 * hkT L τ (x + 1) + hkT L τ x| ≤ A * hpU τ ^ 3
        * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, h₀⟩ := hkT_le
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := hkT_diff1_le
  obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := hkT_diff2_le
  have hc : 0 < min c₀ (min c₁ c₂) := lt_min hc₀ (lt_min hc₁ hc₂)
  set c := min c₀ (min c₁ c₂) with hcdef
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  have hcc₁ : c ≤ c₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hcc₂ : c ≤ c₂ := (min_le_right _ _).trans (min_le_right _ _)
  have he3 : 1 ≤ Real.exp (3 * c) := Real.one_le_exp (by positivity)
  set M := max C₀ (max C₁ C₂) with hM
  have hM₀ : C₀ ≤ M := le_max_left _ _
  have hM₁ : C₁ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM₂ : C₂ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hMpos : 0 < M := lt_of_lt_of_le hC₀ hM₀
  refine ⟨M * Real.exp (3 * c), c, by positivity, hc, ?_⟩
  intro L _ τ hτ hτL x
  have hu := hpU_nonneg τ hτ
  have hexp : ∀ c' : ℝ, c ≤ c' → ∀ f : ℝ, 0 ≤ f →
      Real.exp (-c' * f) ≤ Real.exp (-c * f) := by
    intro c' hcc f hf
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hf0 : ∀ y : ZMod L, 0 ≤ min ((zdist L y : ℝ) ^ 2 / τ) (zdist L y : ℝ) :=
    fun y => le_min (by positivity) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · calc hkT L τ x ≤ C₀ * min 1 (τ ^ (-(1 / 2 : ℝ)))
          * Real.exp (-c₀ * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) := h₀ L τ hτ hτL x
      _ ≤ (M * Real.exp (3 * c)) * hpU τ ^ 1
          * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) := by
          rw [pow_one]
          have h1 : C₀ ≤ M * Real.exp (3 * c) := by nlinarith
          have := hexp c₀ hcc₀ _ (hf0 x)
          unfold hpU
          gcongr
  · calc |hkT L τ (x + 1) - hkT L τ x| ≤ C₁ * min 1 τ⁻¹
          * Real.exp (-c₁ * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) := h₁ L τ hτ hτL x
      _ ≤ (M * Real.exp (3 * c)) * hpU τ ^ 2
          * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) := by
          rw [min_one_inv_eq hτ]
          have h1 : C₁ ≤ M * Real.exp (3 * c) := by nlinarith
          have := hexp c₁ hcc₁ _ (hf0 x)
          gcongr
  · have hb := h₂ L τ hτ hτL (x + 1)
    rw [add_sub_cancel_right] at hb
    have heq : hkT L τ (x + 1 + 1) - 2 * hkT L τ (x + 1) + hkT L τ x
        = hkT L τ (x + 1 + 1) + hkT L τ x - 2 * hkT L τ (x + 1) := by ring
    rw [heq]
    have hn' : (0 : ℝ) ≤ (zdist L (x + 1) : ℝ) := by positivity
    have hshift : (zdist L x : ℝ) ≤ (zdist L (x + 1) : ℝ) + 1 := by
      exact_mod_cast zdist_succ_le x
    have hfs := f_shift hτ (by positivity) hn' hshift
    have hE : Real.exp (-c₂ * min ((zdist L (x + 1) : ℝ) ^ 2 / τ) (zdist L (x + 1) : ℝ))
        ≤ Real.exp (3 * c) * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 := hf0 (x + 1)
      nlinarith [mul_le_mul_of_nonneg_left hfs hc.le, mul_le_mul_of_nonneg_right hcc₂ h1]
    rw [min_one_rpow_three hτ] at hb
    calc _ ≤ C₂ * hpU τ ^ 3
          * Real.exp (-c₂ * min ((zdist L (x + 1) : ℝ) ^ 2 / τ) (zdist L (x + 1) : ℝ)) := hb
      _ ≤ C₂ * hpU τ ^ 3 * (Real.exp (3 * c)
          * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ))) := by
          gcongr
      _ ≤ (M * Real.exp (3 * c)) * hpU τ ^ 3
          * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) := by
          have h1 : C₂ ≤ M := hM₂
          have : 0 ≤ hpU τ ^ 3 * Real.exp (3 * c)
            * Real.exp (-c * min ((zdist L x : ℝ) ^ 2 / τ) (zdist L x : ℝ)) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right h1 this]

private lemma conclude {d L : ℕ} [NeZero L] (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) {A c : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (a : Zd d L) (n : Fin d → ℕ) (F : Fin d → ℝ)
    (hF : ∀ k, |F k| ≤ A * hpU τ ^ n k
      * Real.exp (-c * min ((zdist L (a k) : ℝ) ^ 2 / τ) (zdist L (a k) : ℝ)))
    (N : ℕ) (hN : ∑ k, n k = N) :
    |∏ k, F k| ≤ A ^ d * min 1 (τ ^ (-(N : ℝ) / 2))
      * Real.exp (-(c / d) * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) := by
  have h := prod_bound hd hτ hA hc n F (fun k => (zdist L (a k) : ℝ)) (fun k => by positivity) hF
  rw [hN, hpU_pow hτ N, sum_zdist_cast] at h
  exact h

end Prod

/-! ### The bounds for `τ ≤ L²` -/

/-- Target 3 (`τ ≤ L²`): `K_τ(a) ≤ C min(1, τ^{-d/2}) e^{-c min(|a|²/τ, |a|)}`, `|a|` the torus
`ℓ¹` norm. -/
theorem kProd_le : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
      kProd d L τ a ≤ C * min 1 (τ ^ (-(d : ℝ) / 2))
        * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) := by
  intro d hd
  obtain ⟨A, c, hA, hc, hfb⟩ := factor_bounds
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨A ^ d, c / d, by positivity, by positivity, ?_⟩
  intro L _ τ hτ hτL a
  have hmass := fun k => (hkT_mass L τ hτ.le).1 (a k)
  have h := conclude hd hτ hA.le hc a (fun _ => 1) (fun k => hkT L τ (a k))
    (fun k => by
      rw [abs_of_nonneg (hmass k)]
      exact (hfb L τ hτ hτL (a k)).1) d (by simp)
  calc kProd d L τ a ≤ |∏ k, hkT L τ (a k)| := le_abs_self _
    _ ≤ _ := h

private lemma kProd_diff1_eq {d L : ℕ} [NeZero L] (τ : ℝ) (a : Zd d L) (j : Fin d) :
    kProd d L τ (a + Pi.single j 1) - kProd d L τ a
      = ∏ k, (if k = j then hkT L τ (a k + 1) - hkT L τ (a k) else hkT L τ (a k)) := by
  rw [prod_ite_split, kProd_single, kProd_split τ a j, ← sub_mul]

/-- Target 4 (`τ ≤ L²`): unit first differences, `min(1, τ^{-(d+1)/2})`. -/
theorem kProd_diff1_le : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (j : Fin d),
      |kProd d L τ (a + Pi.single j 1) - kProd d L τ a| ≤ C * min 1 (τ ^ (-((d : ℝ) + 1) / 2))
        * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) := by
  intro d hd
  obtain ⟨A, c, hA, hc, hfb⟩ := factor_bounds
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨A ^ d, c / d, by positivity, by positivity, ?_⟩
  intro L _ τ hτ hτL a j
  have hmass := fun k => (hkT_mass L τ hτ.le).1 (a k)
  have hsum : ∑ k : Fin d, (if k = j then 2 else 1 : ℕ) = d + 1 := by
    have : ∀ k : Fin d, (if k = j then 2 else 1 : ℕ) = 1 + (if k = j then 1 else 0) := by
      intro k; split_ifs <;> rfl
    simp [this, Finset.sum_add_distrib]
  have h := conclude hd hτ hA.le hc a (fun k => if k = j then 2 else 1)
    (fun k => if k = j then hkT L τ (a k + 1) - hkT L τ (a k) else hkT L τ (a k))
    (fun k => by
      by_cases hk : k = j
      · simp only [hk, ite_true]
        exact (hfb L τ hτ hτL (a j)).2.1
      · simp only [hk, ite_false]
        rw [abs_of_nonneg (hmass k)]
        exact (hfb L τ hτ hτL (a k)).1) (d + 1) hsum
  rw [kProd_diff1_eq]
  have : (((d + 1 : ℕ) : ℝ)) = (d : ℝ) + 1 := by push_cast; ring
  rw [this] at h
  exact h

private lemma kProd_diff2_eq_mixed {d L : ℕ} [NeZero L] {i j : Fin d} (hij : i ≠ j) (τ : ℝ)
    (a : Zd d L) :
    kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
        - kProd d L τ (a + Pi.single j 1) + kProd d L τ a
      = ∏ k, (if k = i then hkT L τ (a k + 1) - hkT L τ (a k)
          else if k = j then hkT L τ (a k + 1) - hkT L τ (a k) else hkT L τ (a k)) := by
  rw [prod_ite_split2 hij]
  have h11 := kProd_two hij τ a 1 1
  have h10 := kProd_two hij τ a 1 0
  have h01 := kProd_two hij τ a 0 1
  have h00 := kProd_two hij τ a 0 0
  simp only [Pi.single_zero, add_zero] at h10 h01 h00
  rw [h11, h10, h01, h00]
  ring

private lemma kProd_diff2_eq_same {d L : ℕ} [NeZero L] (i : Fin d) (τ : ℝ) (a : Zd d L) :
    kProd d L τ (a + Pi.single i 1 + Pi.single i 1) - kProd d L τ (a + Pi.single i 1)
        - kProd d L τ (a + Pi.single i 1) + kProd d L τ a
      = ∏ k, (if k = i then hkT L τ (a k + 1 + 1) - 2 * hkT L τ (a k + 1) + hkT L τ (a k)
          else hkT L τ (a k)) := by
  rw [prod_ite_split]
  have h2 : a + Pi.single i 1 + Pi.single i 1 = a + Pi.single i (1 + 1) := by
    rw [add_assoc, ← Pi.single_add]
  rw [h2, kProd_single, kProd_single, kProd_split τ a i, add_assoc (a i) 1 1]
  ring

/-- Target 5 (`τ ≤ L²`): unit second differences, mixed (`i ≠ j`) and same-direction (`i = j`),
`min(1, τ^{-(d+2)/2})` (Fable F7: both are needed). -/
theorem kProd_diff2_le : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (i j : Fin d),
      |kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
          - kProd d L τ (a + Pi.single j 1) + kProd d L τ a|
        ≤ C * min 1 (τ ^ (-((d : ℝ) + 2) / 2))
          * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) := by
  intro d hd
  obtain ⟨A, c, hA, hc, hfb⟩ := factor_bounds
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨A ^ d, c / d, by positivity, by positivity, ?_⟩
  intro L _ τ hτ hτL a i j
  have hmass := fun k => (hkT_mass L τ hτ.le).1 (a k)
  have hcast : (((d + 2 : ℕ) : ℝ)) = (d : ℝ) + 2 := by push_cast; ring
  by_cases hij : i = j
  · subst hij
    have hsum : ∑ k : Fin d, (if k = i then 3 else 1 : ℕ) = d + 2 := by
      have : ∀ k : Fin d, (if k = i then 3 else 1 : ℕ) = 1 + (if k = i then 2 else 0) := by
        intro k; split_ifs <;> rfl
      simp [this, Finset.sum_add_distrib]
    have h := conclude hd hτ hA.le hc a (fun k => if k = i then 3 else 1)
      (fun k => if k = i then hkT L τ (a k + 1 + 1) - 2 * hkT L τ (a k + 1) + hkT L τ (a k)
        else hkT L τ (a k))
      (fun k => by
        by_cases hk : k = i
        · simp only [hk, ite_true]
          exact (hfb L τ hτ hτL (a i)).2.2
        · simp only [hk, ite_false]
          rw [abs_of_nonneg (hmass k)]
          exact (hfb L τ hτ hτL (a k)).1) (d + 2) hsum
    rw [kProd_diff2_eq_same, ← hcast]
    exact h
  · have hji : ¬ j = i := fun h => hij h.symm
    have hsum : ∑ k : Fin d, (if k = i then 2 else if k = j then 2 else 1 : ℕ) = d + 2 := by
      have : ∀ k : Fin d, (if k = i then 2 else if k = j then 2 else 1 : ℕ)
          = 1 + (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
        intro k
        by_cases hki : k = i
        · simp [hki, hij]
        · by_cases hkj : k = j
          · simp [hkj, hji]
          · simp [hki, hkj]
      simp [this, Finset.sum_add_distrib]
    have h := conclude hd hτ hA.le hc a (fun k => if k = i then 2 else if k = j then 2 else 1)
      (fun k => if k = i then hkT L τ (a k + 1) - hkT L τ (a k)
        else if k = j then hkT L τ (a k + 1) - hkT L τ (a k) else hkT L τ (a k))
      (fun k => by
        by_cases hki : k = i
        · simp only [hki, ite_true]
          exact (hfb L τ hτ hτL (a i)).2.1
        · by_cases hkj : k = j
          · simp only [hkj, hji, ite_true, ite_false]
            exact (hfb L τ hτ hτL (a j)).2.1
          · simp only [hki, hkj, ite_false]
            rw [abs_of_nonneg (hmass k)]
            exact (hfb L τ hτ hτL (a k)).1) (d + 2) hsum
    rw [kProd_diff2_eq_mixed hij, ← hcast]
    exact h

/-! ### The gap for `τ ≥ L²` -/

private lemma gap_factor : ∃ Cg cg : ℝ, 0 < Cg ∧ 0 < cg ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ x : ZMod L,
      |hkT L τ x - (L : ℝ)⁻¹| ≤ Cg * (L : ℝ)⁻¹ * Real.exp (-cg * τ / (L : ℝ) ^ 2) ∧
      |hkT L τ x| ≤ (1 + Cg) * ((L : ℝ)⁻¹) ^ 1 * Real.exp (-cg * τ / (L : ℝ) ^ 2) ^ 0 ∧
      |hkT L τ (x + 1) - hkT L τ x|
        ≤ (1 + Cg) * ((L : ℝ)⁻¹) ^ 2 * Real.exp (-cg * τ / (L : ℝ) ^ 2) ^ 1 ∧
      |hkT L τ (x + 1 + 1) - 2 * hkT L τ (x + 1) + hkT L τ x|
        ≤ (1 + Cg) * ((L : ℝ)⁻¹) ^ 3 * Real.exp (-cg * τ / (L : ℝ) ^ 2) ^ 1 := by
  obtain ⟨Cg, cg, hCg, hcg, hg⟩ := hkT_gap
  refine ⟨Cg, cg, hCg, hcg, ?_⟩
  intro L _ τ hτ x
  have hLpos : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hLinv : (0 : ℝ) < (L : ℝ)⁻¹ := inv_pos.mpr hLpos
  have hδ1 : Real.exp (-cg * τ / (L : ℝ) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ τ := le_trans (by positivity) hτ
    have : 0 ≤ cg * τ / (L : ℝ) ^ 2 := by positivity
    have h2 : -cg * τ / (L : ℝ) ^ 2 = -(cg * τ / (L : ℝ) ^ 2) := by ring
    linarith
  have hδ0 := Real.exp_pos (-cg * τ / (L : ℝ) ^ 2)
  obtain ⟨h1, h2, h3⟩ := hg L τ hτ x
  have hA : Cg ≤ 1 + Cg := by linarith
  refine ⟨h1, ?_, ?_, ?_⟩
  · have : |hkT L τ x| ≤ |hkT L τ x - (L : ℝ)⁻¹| + |(L : ℝ)⁻¹| := by
      calc |hkT L τ x| = |(hkT L τ x - (L : ℝ)⁻¹) + (L : ℝ)⁻¹| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_of_pos hLinv] at this
    have h4 : Cg * (L : ℝ)⁻¹ * Real.exp (-cg * τ / (L : ℝ) ^ 2) ≤ Cg * (L : ℝ)⁻¹ := by
      have := mul_le_mul_of_nonneg_left hδ1 (by positivity : 0 ≤ Cg * (L : ℝ)⁻¹)
      linarith
    simp only [pow_one, pow_zero, mul_one]
    nlinarith
  · rw [← inv_pow] at h2
    have hX : 0 ≤ ((L : ℝ)⁻¹) ^ 2 := by positivity
    rw [pow_one]
    exact h2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hX) hδ0.le)
  · obtain ⟨-, -, h3⟩ := hg L τ hτ (x + 1)
    rw [add_sub_cancel_right] at h3
    have heq : hkT L τ (x + 1 + 1) - 2 * hkT L τ (x + 1) + hkT L τ x
        = hkT L τ (x + 1 + 1) + hkT L τ x - 2 * hkT L τ (x + 1) := by ring
    rw [heq]
    rw [← inv_pow] at h3
    have hX : 0 ≤ ((L : ℝ)⁻¹) ^ 3 := by positivity
    rw [pow_one]
    refine h3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hX) hδ0.le)

/-- Target 6 (`τ ≥ L²`): the zero mode `L^{-d}` and the gap, for the kernel and its unit
differences. -/
theorem kProd_gap : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ (a : Zd d L) (i j : Fin d),
      |kProd d L τ a - ((L : ℝ) ^ d)⁻¹| ≤ C * ((L : ℝ) ^ d)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
      |kProd d L τ (a + Pi.single j 1) - kProd d L τ a|
        ≤ C * ((L : ℝ) ^ (d + 1))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
      |kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
          - kProd d L τ (a + Pi.single j 1) + kProd d L τ a|
        ≤ C * ((L : ℝ) ^ (d + 2))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) := by
  intro d hd
  obtain ⟨Cg, cg, hCg, hcg, hg⟩ := gap_factor
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hA1 : (1 : ℝ) ≤ 1 + Cg := by linarith
  have hApos : (0 : ℝ) < 1 + Cg := by linarith
  refine ⟨d * (1 + Cg) ^ d, cg, by positivity, hcg, ?_⟩
  intro L _ τ hτ a i j
  have hLpos : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hLinv : (0 : ℝ) < (L : ℝ)⁻¹ := inv_pos.mpr hLpos
  have hδ1 : Real.exp (-cg * τ / (L : ℝ) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ τ := le_trans (by positivity) hτ
    have : 0 ≤ cg * τ / (L : ℝ) ^ 2 := by positivity
    have h2 : -cg * τ / (L : ℝ) ^ 2 = -(cg * τ / (L : ℝ) ^ 2) := by ring
    linarith
  have hδ0 := Real.exp_pos (-cg * τ / (L : ℝ) ^ 2)
  set δ := Real.exp (-cg * τ / (L : ℝ) ^ 2) with hδ
  have hAd : (1 + Cg) ^ d ≤ d * (1 + Cg) ^ d := by
    have : 0 ≤ (1 + Cg) ^ d := by positivity
    nlinarith
  have hAdL : ∀ m : ℕ, (1 + Cg) ^ d * (((L : ℝ) ^ m)⁻¹) * δ
      ≤ d * (1 + Cg) ^ d * ((L : ℝ) ^ m)⁻¹ * δ := by
    intro m
    have : 0 ≤ ((L : ℝ) ^ m)⁻¹ * δ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hAd this]
  refine ⟨?_, ?_, ?_⟩
  · -- the zero mode
    have hy : ((L : ℝ) ^ d)⁻¹ = ∏ _k : Fin d, (L : ℝ)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
    have hlhs : |kProd d L τ a - ((L : ℝ) ^ d)⁻¹|
        = |∏ k, hkT L τ (a k) - ∏ _k : Fin d, (L : ℝ)⁻¹| := by rw [← hy]; rfl
    rw [hlhs]
    have h := abs_prod_sub_prod_le (Finset.univ : Finset (Fin d))
      (x := fun k => hkT L τ (a k)) (y := fun _ => (L : ℝ)⁻¹)
      (M := (1 + Cg) * (L : ℝ)⁻¹) (η := Cg * δ / (1 + Cg)) (by positivity) (by positivity)
      (fun k _ => by
        have := (hg L τ hτ (a k)).2.1
        simpa using this)
      (fun k _ => by
        rw [abs_of_pos hLinv]
        nlinarith)
      (fun k _ => by
        have := (hg L τ hτ (a k)).1
        have e : Cg * δ / (1 + Cg) * ((1 + Cg) * (L : ℝ)⁻¹) = Cg * (L : ℝ)⁻¹ * δ := by
          field_simp
        rw [e]
        exact this)
    rw [Finset.card_univ, Fintype.card_fin] at h
    refine h.trans ?_
    have e : (d : ℝ) * ((1 + Cg) * (L : ℝ)⁻¹) ^ d * (Cg * δ / (1 + Cg))
        = ((d : ℝ) * (1 + Cg) ^ d * (((L : ℝ) ^ d)⁻¹) * δ) * (Cg / (1 + Cg)) := by
      rw [mul_pow, inv_pow]
      ring
    rw [e]
    have hr : Cg / (1 + Cg) ≤ 1 := by rw [div_le_one hApos]; linarith
    have : 0 ≤ (d : ℝ) * (1 + Cg) ^ d * (((L : ℝ) ^ d)⁻¹) * δ := by positivity
    nlinarith
  · -- first difference
    have hsumm : ∑ k : Fin d, (if k = j then 2 else 1 : ℕ) = d + 1 := by
      have : ∀ k : Fin d, (if k = j then 2 else 1 : ℕ) = 1 + (if k = j then 1 else 0) := by
        intro k; split_ifs <;> rfl
      simp [this, Finset.sum_add_distrib]
    have hsume : 1 ≤ ∑ k : Fin d, (if k = j then 1 else 0 : ℕ) := by simp
    have h := gap_prod hLpos hδ0 hδ1 hApos.le (fun k => if k = j then 2 else 1)
      (fun k => if k = j then 1 else 0) hsume
      (fun k => if k = j then hkT L τ (a k + 1) - hkT L τ (a k) else hkT L τ (a k))
      (fun k => by
        by_cases hk : k = j
        · simp only [hk, ite_true]
          exact (hg L τ hτ (a j)).2.2.1
        · simp only [hk, ite_false]
          exact (hg L τ hτ (a k)).2.1)
    rw [hsumm, ← kProd_diff1_eq, inv_pow] at h
    exact h.trans (hAdL (d + 1))
  · -- second difference
    have hsume : ∀ f : Fin d → ℕ, (∃ k, 1 ≤ f k) → 1 ≤ ∑ k, f k := by
      rintro f ⟨k, hk⟩
      exact hk.trans (Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    by_cases hij : i = j
    · subst hij
      have hsumm : ∑ k : Fin d, (if k = i then 3 else 1 : ℕ) = d + 2 := by
        have : ∀ k : Fin d, (if k = i then 3 else 1 : ℕ) = 1 + (if k = i then 2 else 0) := by
          intro k; split_ifs <;> rfl
        simp [this, Finset.sum_add_distrib]
      have h := gap_prod hLpos hδ0 hδ1 hApos.le (fun k => if k = i then 3 else 1)
        (fun k => if k = i then 1 else 0) (hsume _ ⟨i, by simp⟩)
        (fun k => if k = i then hkT L τ (a k + 1 + 1) - 2 * hkT L τ (a k + 1) + hkT L τ (a k)
          else hkT L τ (a k))
        (fun k => by
          by_cases hk : k = i
          · simp only [hk, ite_true]
            exact (hg L τ hτ (a i)).2.2.2
          · simp only [hk, ite_false]
            exact (hg L τ hτ (a k)).2.1)
      rw [hsumm, ← kProd_diff2_eq_same, inv_pow] at h
      exact h.trans (hAdL (d + 2))
    · have hji : ¬ j = i := fun h => hij h.symm
      have hsumm : ∑ k : Fin d, (if k = i then 2 else if k = j then 2 else 1 : ℕ) = d + 2 := by
        have : ∀ k : Fin d, (if k = i then 2 else if k = j then 2 else 1 : ℕ)
            = 1 + (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
          intro k
          by_cases hki : k = i
          · simp [hki, hij]
          · by_cases hkj : k = j
            · simp [hkj, hji]
            · simp [hki, hkj]
        simp [this, Finset.sum_add_distrib]
      have h := gap_prod hLpos hδ0 hδ1 hApos.le
        (fun k => if k = i then 2 else if k = j then 2 else 1)
        (fun k => if k = i then 1 else if k = j then 1 else 0) (hsume _ ⟨i, by simp⟩)
        (fun k => if k = i then hkT L τ (a k + 1) - hkT L τ (a k)
          else if k = j then hkT L τ (a k + 1) - hkT L τ (a k) else hkT L τ (a k))
        (fun k => by
          by_cases hki : k = i
          · simp only [hki, ite_true]
            exact (hg L τ hτ (a i)).2.2.1
          · by_cases hkj : k = j
            · simp only [hkj, hji, ite_true, ite_false]
              exact (hg L τ hτ (a j)).2.2.1
            · simp only [hki, hkj, ite_false]
              exact (hg L τ hτ (a k)).2.1)
      rw [hsumm, ← kProd_diff2_eq_mixed hij, inv_pow] at h
      exact h.trans (hAdL (d + 2))

/-! ### The heat equation for `hkT` and the value at `τ = 0` -/

section HeatEq

variable {L : ℕ} [NeZero L]

/-- The angle of the mode `k`. -/
private noncomputable def hpAng (L : ℕ) (k : ZMod L) : ℝ := 2 * Real.pi * (k.val : ℝ) / L

/-- The cosine of the phase `2π k m / L` depends only on the class of `m` in `ℤ_L`
(same argument as the private `cos_phase` of `HeatTorus1D.lean`). -/
private lemma hp_cos_phase (k : ZMod L) (m : ℤ) (x : ZMod L) (hm : (m : ZMod L) = x) :
    Real.cos (hpAng L k * (x.val : ℝ)) = Real.cos (hpAng L k * (m : ℝ)) := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have h0 : (((x.val : ℤ) - m : ℤ) : ZMod L) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, hm, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp h0
  have hx : (x.val : ℝ) = (m : ℝ) + (L : ℝ) * (t : ℝ) := by
    have : (x.val : ℤ) = m + (L : ℤ) * t := by linarith
    exact_mod_cast this
  have h2 : hpAng L k * (x.val : ℝ)
      = hpAng L k * (m : ℝ) + (((k.val : ℤ) * t : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hx]
    unfold hpAng
    push_cast
    field_simp
  rw [h2, Real.cos_add_int_mul_two_pi]

/-- The finite Fourier sum read at an integer representative `m` of `x`. -/
private lemma hkT_rep (τ : ℝ) (x : ZMod L) (m : ℤ) (hm : (m : ZMod L) = x) :
    hkT L τ x = (L : ℝ)⁻¹ * ∑ k : ZMod L,
      Real.cos (hpAng L k * (m : ℝ)) * Real.exp (-2 * τ * (1 - Real.cos (hpAng L k))) := by
  unfold hkT
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h1 := hp_cos_phase k m x hm
  have h2 : Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
      = Real.cos (hpAng L k * (x.val : ℝ)) := by
    unfold hpAng
    congr 1
    ring
  rw [h2, h1]
  rfl

/-- The heat equation `∂_τ hk(τ, x) = hk(τ, x+1) + hk(τ, x-1) - 2 hk(τ, x)`. -/
private lemma hkT_hasDerivAt (τ : ℝ) (x : ZMod L) :
    HasDerivAt (fun τ => hkT L τ x)
      (hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x) τ := by
  have hx1 := hkT_rep τ (x + 1) ((x.val : ℤ) + 1) (by push_cast; rw [ZMod.natCast_zmod_val])
  have hx2 := hkT_rep τ (x - 1) ((x.val : ℤ) - 1) (by push_cast; rw [ZMod.natCast_zmod_val])
  have hx0 := hkT_rep τ x (x.val : ℤ) (by simp)
  have hterm : ∀ k : ZMod L, HasDerivAt
      (fun τ => Real.cos (hpAng L k * ((x.val : ℤ) : ℝ))
        * Real.exp (-2 * τ * (1 - Real.cos (hpAng L k))))
      (Real.cos (hpAng L k * ((x.val : ℤ) : ℝ))
        * (Real.exp (-2 * τ * (1 - Real.cos (hpAng L k))) * (-2 * (1 - Real.cos (hpAng L k)))))
      τ := by
    intro k
    have h1 : HasDerivAt (fun τ : ℝ => -2 * τ * (1 - Real.cos (hpAng L k)))
        (-2 * (1 - Real.cos (hpAng L k))) τ := by
      simpa using ((hasDerivAt_id τ).const_mul (-2 : ℝ)).mul_const (1 - Real.cos (hpAng L k))
    exact (h1.exp).const_mul _
  have hsum := (HasDerivAt.fun_sum (u := (Finset.univ : Finset (ZMod L)))
    (fun k _ => hterm k)).const_mul ((L : ℝ)⁻¹)
  have hfun : (fun τ => hkT L τ x) = fun τ => (L : ℝ)⁻¹ * ∑ k : ZMod L,
      Real.cos (hpAng L k * ((x.val : ℤ) : ℝ))
        * Real.exp (-2 * τ * (1 - Real.cos (hpAng L k))) := by
    funext τ
    exact hkT_rep τ x (x.val : ℤ) (by simp)
  rw [hfun]
  convert hsum using 1
  rw [hx1, hx2, hx0]
  push_cast
  have hsumeq : ∑ k : ZMod L, Real.cos (hpAng L k * (x.val : ℝ))
        * (Real.exp (-2 * τ * (1 - Real.cos (hpAng L k))) * (-2 * (1 - Real.cos (hpAng L k))))
      = ∑ k : ZMod L, Real.cos (hpAng L k * ((x.val : ℝ) + 1))
          * Real.exp (-2 * τ * (1 - Real.cos (hpAng L k)))
        + ∑ k : ZMod L, Real.cos (hpAng L k * ((x.val : ℝ) - 1))
          * Real.exp (-2 * τ * (1 - Real.cos (hpAng L k)))
        - 2 * ∑ k : ZMod L, Real.cos (hpAng L k * (x.val : ℝ))
          * Real.exp (-2 * τ * (1 - Real.cos (hpAng L k))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h1 : Real.cos (hpAng L k * ((x.val : ℝ) + 1))
        = Real.cos (hpAng L k * (x.val : ℝ)) * Real.cos (hpAng L k)
          - Real.sin (hpAng L k * (x.val : ℝ)) * Real.sin (hpAng L k) := by
      rw [mul_add, mul_one, Real.cos_add]
    have h2 : Real.cos (hpAng L k * ((x.val : ℝ) - 1))
        = Real.cos (hpAng L k * (x.val : ℝ)) * Real.cos (hpAng L k)
          + Real.sin (hpAng L k * (x.val : ℝ)) * Real.sin (hpAng L k) := by
      rw [mul_sub, mul_one, Real.cos_sub]
    rw [h1, h2]
    ring
  rw [hsumeq]
  ring

/-- Finite orthogonality of the exponentials `k ↦ e^{2πi k u / L}` on `ℤ_L`
(`sum_exp_orth` of `HeatKernel1D.lean`, which is private there; same proof). -/
private lemma hp_sum_exp_orth (u : ℤ) :
    ∑ k : ZMod L, Complex.exp (2 * Real.pi * Complex.I * (((k.val : ℤ) * u : ℤ) : ℂ) / (L : ℂ))
      = if (u : ZMod L) = 0 then (L : ℂ) else 0 := by
  have h1 : ∀ k : ZMod L,
      Complex.exp (2 * Real.pi * Complex.I * (((k.val : ℤ) * u : ℤ) : ℂ) / (L : ℂ))
        = ZMod.stdAddChar (k * (u : ZMod L)) := by
    intro k
    have hk : k * (u : ZMod L) = (((k.val : ℤ) * u : ℤ) : ZMod L) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hk, ZMod.stdAddChar_coe]
  simp_rw [h1]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar L), ZMod.card]
  split_ifs <;> simp

/-- The cosine version of the orthogonality (`sum_cos_orth` of `HeatKernel1D.lean`). -/
private lemma hp_sum_cos_orth (k : ZMod L) :
    ∑ x : ZMod L, Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
      = if k = 0 then (L : ℝ) else 0 := by
  have h := hp_sum_exp_orth (L := L) (k.val : ℤ)
  have hk : (((k.val : ℤ)) : ZMod L) = k := by simp
  rw [hk] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have h3 : ∀ x : ZMod L,
      (Complex.exp (2 * Real.pi * Complex.I * (((x.val : ℤ) * (k.val : ℤ) : ℤ) : ℂ)
        / (L : ℂ))).re = Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L) := by
    intro x
    have : 2 * (Real.pi : ℂ) * Complex.I * (((x.val : ℤ) * (k.val : ℤ) : ℤ) : ℂ) / (L : ℂ)
        = ((2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  simp_rw [h3] at h2
  rw [h2]
  split_ifs <;> simp

/-- At `τ = 0` the torus kernel is the point mass at `0`. -/
private lemma hkT_zero (x : ZMod L) : hkT L 0 x = if x = 0 then 1 else 0 := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  unfold hkT
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
  have h := hp_sum_cos_orth x
  have h2 : ∑ k : ZMod L, Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
      = ∑ k : ZMod L, Real.cos (2 * Real.pi * (x.val : ℝ) * (k.val : ℝ) / L) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    ring
  rw [h2, h]
  split_ifs
  · field_simp
  · simp

end HeatEq

/-! ### The heat equation for the product kernel -/

section ProdDeriv

variable {d L : ℕ} [NeZero L]

private lemma kProd_hasDerivAt (a : Zd d L) (τ : ℝ) :
    HasDerivAt (fun τ => kProd d L τ a)
      (∑ p : Fin d × Bool, kProd d L τ (a + unitVec d L p) - 2 * (d : ℝ) * kProd d L τ a) τ := by
  have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin d)))
    (f := fun j τ => hkT L τ (a j))
    (f' := fun j => hkT L τ (a j + 1) + hkT L τ (a j - 1) - 2 * hkT L τ (a j))
    (x := τ) (fun j _ => hkT_hasDerivAt τ (a j))
  refine HasDerivAt.congr_deriv h ?_
  have hu1 : ∀ j : Fin d, unitVec d L (j, true) = Pi.single j 1 := by
    intro j; simp [unitVec]
  have hu2 : ∀ j : Fin d, unitVec d L (j, false) = Pi.single j (-1) := by
    intro j; simp [unitVec]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, hu1, hu2, kProd_single, ← sub_eq_add_neg]
  have h2dK : 2 * (d : ℝ) * kProd d L τ a
      = ∑ j : Fin d, 2 * (hkT L τ (a j) * ∏ k ∈ Finset.univ.erase j, hkT L τ (a k)) := by
    calc 2 * (d : ℝ) * kProd d L τ a = ∑ _j : Fin d, 2 * kProd d L τ a := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ = _ := Finset.sum_congr rfl (fun j _ => by rw [← kProd_split])
  rw [h2dK, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [smul_eq_mul]
  ring

private lemma kProd_continuous (a : Zd d L) : Continuous (fun τ => kProd d L τ a) :=
  continuous_iff_continuousAt.2 fun τ => (kProd_hasDerivAt a τ).continuousAt

private lemma kProd_nonneg_le_one {τ : ℝ} (hτ : 0 ≤ τ) (a : Zd d L) :
    0 ≤ kProd d L τ a ∧ kProd d L τ a ≤ 1 := by
  obtain ⟨h0, h1⟩ := hkT_mass L τ hτ
  have hle : ∀ x : ZMod L, hkT L τ x ≤ 1 := fun x => by
    calc hkT L τ x ≤ ∑ y : ZMod L, hkT L τ y :=
          Finset.single_le_sum (f := fun y => hkT L τ y) (fun y _ => h0 y) (Finset.mem_univ x)
      _ = 1 := h1
  exact ⟨Finset.prod_nonneg (fun j _ => h0 _), Finset.prod_le_one₀ (fun j _ => h0 _)
    (fun j _ => hle _)⟩

private lemma kProd_zero (a : Zd d L) : kProd d L 0 a = if a = 0 then 1 else 0 := by
  unfold kProd
  simp only [hkT_zero]
  by_cases h : a = 0
  · subst h; simp
  · obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h (funext hcon)
    have h0 : (if a = 0 then (1 : ℝ) else 0) = 0 := by simp [h]
    rw [h0]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

end ProdDeriv

/-! ### The Laplace–product representation -/

section Laplace

variable {d L : ℕ} [NeZero L]

/-- The Laplace integrand `e^{-es} K_{γs}(a)`. -/
private noncomputable def phi (d L : ℕ) [NeZero L] (γ e : ℝ) (a : Zd d L) (s : ℝ) : ℝ :=
  Real.exp (-e * s) * kProd d L (γ * s) a

/-- The real entries of `1 - t S^(B)`. -/
private noncomputable def hpM (d L : ℕ) [NeZero L] (g t : ℝ) (y z : Zd d L) : ℝ :=
  (if y = z then 1 else 0) - t * sbKernelR d L g (y - z)

private lemma sum_adj (hL : 3 ≤ L) (f : Zd d L → ℝ) (z : Zd d L) :
    ∑ y, (if zdistD d L (y - z) = 1 then f y else 0)
      = ∑ p : Fin d × Bool, f (z + unitVec d L p) := by
  have h1 : ∑ y, (if zdistD d L (y - z) = 1 then f y else 0)
      = ∑ w, (if zdistD d L w = 1 then f (w + z) else 0) :=
    (Fintype.sum_equiv (Equiv.addRight z) (fun w => if zdistD d L w = 1 then f (w + z) else 0)
      (fun y => if zdistD d L (y - z) = 1 then f y else 0) (fun w => by simp)).symm
  rw [h1, ← Finset.sum_filter, filter_zdistD_eq_one hL,
    Finset.sum_image (fun p _ q _ h => unitVec_injective hL h)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [add_comm]

private lemma sum_kernel_mul (hL : 3 ≤ L) (g t τ : ℝ) (x z : Zd d L) :
    ∑ y, kProd d L τ (y - x) * hpM d L g t y z
      = (1 - t) * kProd d L τ (z - x)
        - lgGam d g t * (∑ p : Fin d × Bool, kProd d L τ (z - x + unitVec d L p)
          - 2 * (d : ℝ) * kProd d L τ (z - x)) := by
  have hD : (1 + 2 * (d : ℝ) * g ^ 2) ≠ 0 := by positivity
  unfold hpM sbKernelR
  have hexp : ∀ y : Zd d L, kProd d L τ (y - x) * ((if y = z then (1 : ℝ) else 0)
      - t * ((if y - z = 0 then (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ else 0)
        + (if zdistD d L (y - z) = 1 then g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ else 0)))
      = kProd d L τ (y - x) * (if y = z then (1 : ℝ) else 0)
        - t * (kProd d L τ (y - x) * (if y - z = 0 then (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ else 0))
        - t * (if zdistD d L (y - z) = 1
            then kProd d L τ (y - x) * (g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹) else 0) := by
    intro y
    split_ifs <;> ring
  simp_rw [hexp]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 : ∑ y : Zd d L, kProd d L τ (y - x) * (if y = z then (1 : ℝ) else 0)
      = kProd d L τ (z - x) := by
    simp [mul_ite]
  have e2 : ∑ y : Zd d L, kProd d L τ (y - x)
        * (if y - z = 0 then (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ else 0)
      = kProd d L τ (z - x) * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := by
    simp [mul_ite, sub_eq_zero]
  have e3 := sum_adj hL (fun y => kProd d L τ (y - x) * (g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹)) z
  rw [e1, e2, e3]
  have e4 : ∀ p : Fin d × Bool,
      kProd d L τ (z + unitVec d L p - x) = kProd d L τ (z - x + unitVec d L p) := by
    intro p; rw [add_sub_right_comm]
  simp_rw [e4, ← Finset.sum_mul]
  unfold lgGam
  field_simp
  ring

private lemma phi_hasDerivAt (γ e : ℝ) (a : Zd d L) (s : ℝ) :
    HasDerivAt (phi d L γ e a)
      (γ * (∑ p : Fin d × Bool, phi d L γ e (a + unitVec d L p) s
        - 2 * (d : ℝ) * phi d L γ e a s) - e * phi d L γ e a s) s := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-e * s)) (Real.exp (-e * s) * (-e)) s := by
    simpa using ((hasDerivAt_id s).const_mul (-e)).exp
  have h2 : HasDerivAt (fun s : ℝ => kProd d L (γ * s) a)
      ((∑ p : Fin d × Bool, kProd d L (γ * s) (a + unitVec d L p)
        - 2 * (d : ℝ) * kProd d L (γ * s) a) * γ) s := by
    have h := (kProd_hasDerivAt a (γ * s)).comp s ((hasDerivAt_id s).const_mul γ)
    rw [mul_one] at h
    exact h
  have h3 := h1.mul h2
  unfold phi
  convert h3 using 1
  rw [← Finset.mul_sum]
  ring

private lemma phi_continuous (γ e : ℝ) (a : Zd d L) : Continuous (phi d L γ e a) := by
  unfold phi
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((kProd_continuous a).comp (continuous_const.mul continuous_id))

private lemma phi_nonneg_le {γ e : ℝ} (hγ : 0 ≤ γ) (a : Zd d L) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ phi d L γ e a s ∧ phi d L γ e a s ≤ Real.exp (-e * s) := by
  obtain ⟨h0, h1⟩ := kProd_nonneg_le_one (mul_nonneg hγ hs) a
  unfold phi
  refine ⟨mul_nonneg (Real.exp_pos _).le h0, ?_⟩
  calc Real.exp (-e * s) * kProd d L (γ * s) a ≤ Real.exp (-e * s) * 1 :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := mul_one _

private lemma phi_integrable {γ e : ℝ} (hγ : 0 ≤ γ) (he : 0 < e) (a : Zd d L) :
    IntegrableOn (phi d L γ e a) (Ioi 0) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 he)
    (phi_continuous γ e a).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have := phi_nonneg_le hγ (e := e) a (le_of_lt (mem_Ioi.1 hs))
  rw [Real.norm_of_nonneg this.1]
  exact this.2

private lemma phi_tendsto {γ e : ℝ} (hγ : 0 ≤ γ) (he : 0 < e) (a : Zd d L) :
    Tendsto (phi d L γ e a) atTop (𝓝 0) := by
  have hexp : Tendsto (fun s : ℝ => Real.exp (-e * s)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop he)
    refine this.congr (fun s => ?_)
    simp [neg_mul]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with s hs using (phi_nonneg_le hγ a hs).1
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with s hs using (phi_nonneg_le hγ a hs).2

private lemma phi_integral {γ e : ℝ} (hγ : 0 ≤ γ) (he : 0 < e) (a : Zd d L) :
    ∫ s in Ioi (0 : ℝ), (e * phi d L γ e a s
        - γ * (∑ p : Fin d × Bool, phi d L γ e (a + unitVec d L p) s
          - 2 * (d : ℝ) * phi d L γ e a s)) = kProd d L 0 a := by
  set f' : ℝ → ℝ := fun s => γ * (∑ p : Fin d × Bool, phi d L γ e (a + unitVec d L p) s
        - 2 * (d : ℝ) * phi d L γ e a s) - e * phi d L γ e a s with hf'
  have hint : IntegrableOn f' (Ioi 0) := by
    have h1 : IntegrableOn (fun s => ∑ p : Fin d × Bool, phi d L γ e (a + unitVec d L p) s)
        (Ioi 0) := integrable_finsetSum _ (fun p _ => phi_integrable hγ he _)
    have h2 := phi_integrable hγ he a
    exact ((h1.sub (h2.const_mul (2 * (d : ℝ)))).const_mul γ).sub (h2.const_mul e)
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (f := phi d L γ e a)
    (f' := f') (m := 0) (phi_continuous γ e a).continuousWithinAt
    (fun s _ => phi_hasDerivAt γ e a s) hint (phi_tendsto hγ he a)
  have h0 : phi d L γ e a 0 = kProd d L 0 a := by simp [phi]
  rw [h0] at hmain
  have : (fun s => e * phi d L γ e a s
        - γ * (∑ p : Fin d × Bool, phi d L γ e (a + unitVec d L p) s
          - 2 * (d : ℝ) * phi d L γ e a s)) = fun s => -f' s := by
    funext s; simp only [hf']; ring
  rw [this, integral_neg, hmain]
  ring

private lemma laplace_matrix (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (Matrix.of fun x y : Zd d L =>
        ((∫ s in Ioi (0 : ℝ), phi d L (lgGam d g t) (1 - t) (y - x) s : ℝ) : ℂ))
      * (1 - (t : ℂ) • SB d L g) = 1 := by
  have hγ : 0 ≤ lgGam d g t := by unfold lgGam; positivity
  have he : 0 < 1 - t := by linarith
  ext x z
  have hent : ∀ y : Zd d L, (1 - (t : ℂ) • SB d L g) y z = ((hpM d L g t y z : ℝ) : ℂ) := by
    intro y
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, SB_apply,
      sbKernel_eq_ofReal, hpM]
    push_cast
    split_ifs <;> simp
  rw [Matrix.mul_apply]
  simp_rw [Matrix.of_apply, hent]
  have hsum : (∑ y : Zd d L, ((∫ s in Ioi (0 : ℝ), phi d L (lgGam d g t) (1 - t) (y - x) s : ℝ) : ℂ)
      * ((hpM d L g t y z : ℝ) : ℂ))
      = ((∑ y : Zd d L, (∫ s in Ioi (0 : ℝ), phi d L (lgGam d g t) (1 - t) (y - x) s)
          * hpM d L g t y z : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hsum, Matrix.one_apply]
  have hint : ∀ y : Zd d L, IntegrableOn
      (fun s => phi d L (lgGam d g t) (1 - t) (y - x) s * hpM d L g t y z) (Ioi 0) :=
    fun y => (phi_integrable hγ he _).mul_const _
  have hreal : ∑ y : Zd d L, (∫ s in Ioi (0 : ℝ), phi d L (lgGam d g t) (1 - t) (y - x) s)
      * hpM d L g t y z = if x = z then 1 else 0 := by
    calc ∑ y : Zd d L, (∫ s in Ioi (0 : ℝ), phi d L (lgGam d g t) (1 - t) (y - x) s)
          * hpM d L g t y z
        = ∑ y : Zd d L, ∫ s in Ioi (0 : ℝ),
            phi d L (lgGam d g t) (1 - t) (y - x) s * hpM d L g t y z := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [integral_mul_const]
      _ = ∫ s in Ioi (0 : ℝ), ∑ y : Zd d L,
            phi d L (lgGam d g t) (1 - t) (y - x) s * hpM d L g t y z :=
          (integral_finsetSum _ (fun y _ => hint y)).symm
      _ = ∫ s in Ioi (0 : ℝ), ((1 - t) * phi d L (lgGam d g t) (1 - t) (z - x) s
          - lgGam d g t * (∑ p : Fin d × Bool,
              phi d L (lgGam d g t) (1 - t) (z - x + unitVec d L p) s
            - 2 * (d : ℝ) * phi d L (lgGam d g t) (1 - t) (z - x) s)) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
          have h := sum_kernel_mul hL g t (lgGam d g t * s) x z
          calc ∑ y : Zd d L, phi d L (lgGam d g t) (1 - t) (y - x) s * hpM d L g t y z
              = ∑ y : Zd d L, Real.exp (-(1 - t) * s)
                  * (kProd d L (lgGam d g t * s) (y - x) * hpM d L g t y z) := by
                refine Finset.sum_congr rfl (fun y _ => ?_)
                simp only [phi]
                ring
            _ = Real.exp (-(1 - t) * s)
                * ∑ y : Zd d L, kProd d L (lgGam d g t * s) (y - x) * hpM d L g t y z :=
                (Finset.mul_sum _ _ _).symm
            _ = _ := by
                rw [h]
                simp only [phi]
                rw [← Finset.mul_sum]
                ring
      _ = kProd d L 0 (z - x) := phi_integral hγ he (z - x)
      _ = if x = z then 1 else 0 := by
          rw [kProd_zero]
          simp [sub_eq_zero, eq_comm]
  rw [hreal]
  split_ifs <;> simp

/-- Target 1 (F1, exact): `Θ_t(0, a) = ∫₀^∞ e^{-(1-t)s} K_{γs}(a) ds`, `γ = t g²/(1 + 2dg²)`, for
real `t ∈ [0, 1)` (the sign pairs with `m(σ₁)m(σ₂) = 1`). -/
theorem Theta_eq_laplace_prod :
    ∀ (d L : ℕ) (hL : 3 ≤ L) (g t : ℝ), 0 < g → 0 ≤ t → t < 1 → ∀ a : Zd d L,
    haveI : NeZero L := ⟨by omega⟩
    Theta d L g (t : ℂ) 0 a =
      ((∫ s in Ioi (0 : ℝ), Real.exp (-(1 - t) * s) * kProd d L (lgGam d g t * s) a : ℝ) : ℂ) := by
  intro d L hL g t hg ht0 ht1 a
  have : NeZero L := ⟨by omega⟩
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0]
    exact ht1
  have h := eq_Theta_of_mul d L g (norm_SB d L g hL) hnorm (laplace_matrix hL hg ht0 ht1)
  have h2 := congrFun (congrFun h 0) a
  simpa [Matrix.of_apply, phi] using h2.symm

end Laplace

/-! ### Compiled instances

Each target theorem applied at concrete nondegenerate data; every deterministic hypothesis is
discharged (the constants of the bounds stay existential, as in the statements). -/

-- `Theta_eq_laplace_prod` at `d = 3`, `L = 3`, `g = 1`, `t = 1/2`, `a = 0`
-- (`γ = 1/14`, `1 - t = 1/2`).
example : Theta 3 3 1 (((1 / 2 : ℝ)) : ℂ) 0 0
    = ((∫ s in Ioi (0 : ℝ), Real.exp (-(1 - 1 / 2) * s) * kProd 3 3 (lgGam 3 1 (1 / 2) * s) 0
        : ℝ) : ℂ) :=
  Theta_eq_laplace_prod 3 3 le_rfl 1 (1 / 2) one_pos (by norm_num) (by norm_num) 0

-- `sum_min_ge` at `d = 3`, `x = (1, 50, 0)`, `τ = 10`: `(1/3) * min (51²/10) 51 ≤ 0.1 + 50 + 0`.
example : ((3 : ℕ) : ℝ)⁻¹ * min ((∑ j, (![1, 50, 0] : Fin 3 → ℝ) j) ^ 2 / 10)
      (∑ j, (![1, 50, 0] : Fin 3 → ℝ) j)
    ≤ ∑ j, min ((![1, 50, 0] : Fin 3 → ℝ) j ^ 2 / 10) ((![1, 50, 0] : Fin 3 → ℝ) j) :=
  sum_min_ge 3 (by norm_num) 10 (by norm_num) ![1, 50, 0]
    (fun j => by fin_cases j <;> simp)

-- `kProd_le` at `d = 3`, `L = 5`, `τ = 4`, `a = (0, 1, 2)` (`|a| = 3`).
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    kProd 3 5 4 ![0, 1, 2] ≤ C * min 1 ((4 : ℝ) ^ (-((3 : ℕ) : ℝ) / 2))
      * Real.exp (-c * min ((zdistD 3 5 ![0, 1, 2] : ℝ) ^ 2 / 4) (zdistD 3 5 ![0, 1, 2] : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := kProd_le 3 (by norm_num)
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _⟩

-- `kProd_diff1_le` at `d = 3`, `L = 5`, `τ = 4`, `a = (0, 1, 2)`, `j = 1`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |kProd 3 5 4 (![0, 1, 2] + Pi.single 1 1) - kProd 3 5 4 ![0, 1, 2]|
      ≤ C * min 1 ((4 : ℝ) ^ (-(((3 : ℕ) : ℝ) + 1) / 2))
        * Real.exp (-c * min ((zdistD 3 5 ![0, 1, 2] : ℝ) ^ 2 / 4)
          (zdistD 3 5 ![0, 1, 2] : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := kProd_diff1_le 3 (by norm_num)
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _ 1⟩

-- `kProd_diff2_le` at `d = 3`, `L = 5`, `τ = 4`, `a = (0, 1, 2)`, mixed `(i, j) = (0, 2)`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |kProd 3 5 4 (![0, 1, 2] + Pi.single 0 1 + Pi.single 2 1)
        - kProd 3 5 4 (![0, 1, 2] + Pi.single 0 1) - kProd 3 5 4 (![0, 1, 2] + Pi.single 2 1)
        + kProd 3 5 4 ![0, 1, 2]|
      ≤ C * min 1 ((4 : ℝ) ^ (-(((3 : ℕ) : ℝ) + 2) / 2))
        * Real.exp (-c * min ((zdistD 3 5 ![0, 1, 2] : ℝ) ^ 2 / 4)
          (zdistD 3 5 ![0, 1, 2] : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := kProd_diff2_le 3 (by norm_num)
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _ 0 2⟩

-- `kProd_diff2_le` at the same data, same direction `(i, j) = (1, 1)`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |kProd 3 5 4 (![0, 1, 2] + Pi.single 1 1 + Pi.single 1 1)
        - kProd 3 5 4 (![0, 1, 2] + Pi.single 1 1) - kProd 3 5 4 (![0, 1, 2] + Pi.single 1 1)
        + kProd 3 5 4 ![0, 1, 2]|
      ≤ C * min 1 ((4 : ℝ) ^ (-(((3 : ℕ) : ℝ) + 2) / 2))
        * Real.exp (-c * min ((zdistD 3 5 ![0, 1, 2] : ℝ) ^ 2 / 4)
          (zdistD 3 5 ![0, 1, 2] : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := kProd_diff2_le 3 (by norm_num)
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _ 1 1⟩

-- `kProd_gap` at `d = 3`, `L = 5`, `τ = 50 ≥ 25 = L²`, `a = (0, 1, 2)`, `(i, j) = (0, 2)`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (|kProd 3 5 50 ![0, 1, 2] - (((5 : ℕ) : ℝ) ^ 3)⁻¹|
        ≤ C * (((5 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2) ∧
      |kProd 3 5 50 (![0, 1, 2] + Pi.single 2 1) - kProd 3 5 50 ![0, 1, 2]|
        ≤ C * (((5 : ℕ) : ℝ) ^ (3 + 1))⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2) ∧
      |kProd 3 5 50 (![0, 1, 2] + Pi.single 0 1 + Pi.single 2 1)
          - kProd 3 5 50 (![0, 1, 2] + Pi.single 0 1) - kProd 3 5 50 (![0, 1, 2] + Pi.single 2 1)
          + kProd 3 5 50 ![0, 1, 2]|
        ≤ C * (((5 : ℕ) : ℝ) ^ (3 + 2))⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨C, c, hC, hc, h⟩ := kProd_gap 3 (by norm_num)
  exact ⟨C, c, hC, hc, h 5 50 (by norm_num) _ 0 2⟩

end RBM.Heat
