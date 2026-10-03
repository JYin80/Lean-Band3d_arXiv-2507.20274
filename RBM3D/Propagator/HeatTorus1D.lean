/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.HeatBounds1D
import RBM3D.Defs.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Bounds of the one-dimensional heat kernel on the torus `ℤ_L`

Route H, ticket PT-C (design `docs/reports/T2003-prove.md` b8 row S3; Fable review
`docs/claude-team/fable/2026-10-02-routeH.md` F3, §2 S3-L).  Two regimes for `hk(τ, ·) = hkT L τ`:

* `τ ≤ L²`: the image sum `hk(τ, x) = Σ_y h_τ(x̂ + L y)` (`hkT_hasSum_images`, `x̂` the
  representative of `x` with `|x̂| = |x|_L`) is estimated termwise with the bounds of
  `RBM3D.Propagator.HeatBounds1D`; for `y ≠ 0` one has `|x̂ + L y| ≥ |x̂|` and
  `|x̂ + L y| ≥ L|y|/2`, hence `m(x̂ + L y) ≥ m(x̂)` and `m(x̂ + L y) ≥ |y|/4` for
  `m(n) = min (n²/τ, |n|)` and `τ ≤ L²`, and the series `Σ_y e^{-c|y|/8}` converges;
* `τ ≥ L²`: the finite Fourier sum has the zero mode `1/L`; for `k ≠ 0` the Jordan inequality
  `1 - cos (2πk/L) ≥ 8 |k|_L²/L²` and the elementary bounds `t e^{-t} ≤ 1` give the gap.

## Main results (namespace `RBM.Heat`)

* `hkT_le`, `hkT_diff1_le`, `hkT_diff2_le`: for `τ ≤ L²` the bounds of `hkZ_le`, `hkZ_diff1_le`,
  `hkZ_diff2_le` with `|n|` replaced by `|x|_L = zdist L x`.
* `hkT_gap`: for `τ ≥ L²`, `|hk - 1/L| ≤ (C/L) e^{-cτ/L²}`, `|Δ₁ hk| ≤ (C/L²) e^{-cτ/L²}`,
  `|Δ₂ hk| ≤ (C/L³) e^{-cτ/L²}` (`C = 1`, `c = 4`).

No new hypothesis; all four are proved here.
-/

namespace RBM.Heat

/-! ### The representative of `x ∈ ℤ_L` with `|x̂| = |x|_L`, and the shifted image sums -/

/-- The representative `a` of `x ∈ ℤ_L` with `|a| = |x|_L`. -/
private lemma exists_rep (L : ℕ) [NeZero L] (x : ZMod L) :
    ∃ a : ℤ, (a : ZMod L) = x ∧ ((RBM.zdist L x : ℕ) : ℤ) = |a| := by
  have hv : x.val < L := ZMod.val_lt x
  by_cases h : 2 * x.val ≤ L
  · refine ⟨(x.val : ℤ), by simp, ?_⟩
    have : RBM.zdist L x = x.val := by unfold RBM.zdist; omega
    rw [this, abs_of_nonneg (Int.natCast_nonneg _)]
  · refine ⟨(x.val : ℤ) - L, ?_, ?_⟩
    · push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_self, sub_zero]
    · have : RBM.zdist L x = L - x.val := by unfold RBM.zdist; omega
      rw [this, abs_of_nonpos (by omega)]
      omega

/-- The image sum over any integer representative of `x`. -/
private lemma hasSum_images_rep {L : ℕ} [NeZero L] {τ : ℝ} (hτ : 0 ≤ τ) {x : ZMod L} {a : ℤ}
    (ha : (a : ZMod L) = x) :
    HasSum (fun y : ℤ => hkZ τ (a + (L : ℤ) * y)) (hkT L τ x) := by
  have h := hkT_hasSum_images L τ hτ x
  obtain ⟨t, ht⟩ : ∃ t : ℤ, a = (x.val : ℤ) + L * t := by
    have h0 : (((x.val : ℤ) - a : ℤ) : ZMod L) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ha, sub_self]
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp h0
    exact ⟨-t, by linarith⟩
  have h2 := (Equiv.addRight t).hasSum_iff.mpr h
  convert h2 using 1
  funext y
  simp only [Function.comp, Equiv.coe_addRight, ht]
  congr 1
  ring

/-! ### The termwise estimate for `τ ≤ L²` -/

private lemma summable_exp_abs (b : ℝ) (hb : 0 < b) :
    Summable (fun y : ℤ => Real.exp (-b * |(y : ℝ)|)) := by
  have hr : Real.exp (-b) < 1 := by
    have := Real.exp_lt_exp.2 (show -b < 0 by linarith)
    simpa using this
  have hg := summable_geometric_of_lt_one (Real.exp_pos (-b)).le hr
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hg.congr (fun n => ?_)
    simp only [Int.cast_natCast, Nat.abs_cast]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  · refine hg.congr (fun n => ?_)
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
    rw [← Real.exp_nat_mul]
    congr 1
    ring

/-- The geometry of the images: for `|a| ≤ L/2`, `τ ≤ L²` and `n = a + L y`,
`m(n) ≥ m(a)` and `m(n) ≥ |y|/4`, with `m(n) = min (n²/τ, |n|)`. -/
private lemma image_geometry {τ Lr A Y : ℝ} (hτ : 0 < τ) (hτL : τ ≤ Lr ^ 2) (hL1 : 1 ≤ Lr)
    (hA : 2 * |A| ≤ Lr) (hY : Y = 0 ∨ 1 ≤ |Y|) :
    min (A ^ 2 / τ) |A| ≤ min ((A + Lr * Y) ^ 2 / τ) |A + Lr * Y| ∧
      |Y| / 4 ≤ min ((A + Lr * Y) ^ 2 / τ) |A + Lr * Y| := by
  have hLpos : 0 < Lr := by linarith
  have hm0 : 0 ≤ min ((A + Lr * Y) ^ 2 / τ) |A + Lr * Y| :=
    le_min (by positivity) (abs_nonneg _)
  rcases hY with rfl | hY1
  · simp only [mul_zero, add_zero, abs_zero, zero_div]
    exact ⟨le_rfl, by simpa using hm0⟩
  · -- `|n| ≥ L |Y| - |A|`
    have hn1 : Lr * |Y| - |A| ≤ |A + Lr * Y| := by
      have : |Lr * Y| ≤ |A + Lr * Y| + |A| := by
        calc |Lr * Y| = |(A + Lr * Y) - A| := by ring_nf
          _ ≤ |A + Lr * Y| + |A| := abs_sub _ _
      rw [abs_mul, abs_of_pos hLpos] at this
      linarith
    have hn2 : Lr * |Y| / 2 ≤ |A + Lr * Y| := by nlinarith
    have hn3 : |A| ≤ |A + Lr * Y| := by nlinarith
    have hsq : (A + Lr * Y) ^ 2 = |A + Lr * Y| ^ 2 := (sq_abs _).symm
    refine ⟨le_min ?_ ?_, le_min ?_ ?_⟩
    · -- `A²/τ ≤ n²/τ`
      calc min (A ^ 2 / τ) |A| ≤ A ^ 2 / τ := min_le_left _ _
        _ ≤ (A + Lr * Y) ^ 2 / τ := by
          rw [hsq, ← sq_abs A]
          exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hn3 2) hτ.le
    · exact (min_le_right _ _).trans hn3
    · -- `|Y|/4 ≤ n²/τ`
      have h1 : (Lr * |Y| / 2) ^ 2 ≤ (A + Lr * Y) ^ 2 := by
        rw [hsq]
        exact pow_le_pow_left₀ (by positivity) hn2 2
      have h2 : (Lr * |Y| / 2) ^ 2 / Lr ^ 2 ≤ (A + Lr * Y) ^ 2 / τ := by
        calc (Lr * |Y| / 2) ^ 2 / Lr ^ 2 ≤ (A + Lr * Y) ^ 2 / Lr ^ 2 :=
              div_le_div_of_nonneg_right h1 (by positivity)
          _ ≤ (A + Lr * Y) ^ 2 / τ :=
              div_le_div_of_nonneg_left (by positivity) hτ hτL
      have h3 : (Lr * |Y| / 2) ^ 2 / Lr ^ 2 = |Y| ^ 2 / 4 := by
        field_simp
        norm_num
      have h4 : |Y| ≤ |Y| ^ 2 := by nlinarith
      calc |Y| / 4 ≤ |Y| ^ 2 / 4 := by linarith
        _ ≤ _ := by rw [← h3]; exact h2
    · -- `|Y|/4 ≤ |n|`
      have : |Y| / 4 ≤ Lr * |Y| / 2 := by nlinarith [abs_nonneg Y]
      exact this.trans hn2

/-- One image term against the product of the two exponential factors. -/
private lemma image_term_le {L : ℕ} [NeZero L] {τ : ℝ} (hτ : 0 < τ) (hτL : τ ≤ (L : ℝ) ^ 2)
    {a : ℤ} (ha : 2 * |(a : ℝ)| ≤ L) (c : ℝ) (hc : 0 < c) (y : ℤ) :
    Real.exp (-c * min ((((a + (L : ℤ) * y : ℤ)) : ℝ) ^ 2 / τ) |(((a + (L : ℤ) * y : ℤ)) : ℝ)|)
      ≤ Real.exp (-(c / 2) * min ((a : ℝ) ^ 2 / τ) |(a : ℝ)|)
        * Real.exp (-(c / 8) * |(y : ℝ)|) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hY : (y : ℝ) = 0 ∨ 1 ≤ |(y : ℝ)| := by
    by_cases h0 : y = 0
    · left; simp [h0]
    · right
      have : (1 : ℤ) ≤ |y| := Int.one_le_abs h0
      exact_mod_cast this
  obtain ⟨h1, h2⟩ := image_geometry hτ hτL hL1 ha hY
  push_cast
  set M := min (((a : ℝ) + L * y) ^ 2 / τ) |(a : ℝ) + L * y| with hM
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc2 : 0 < c / 2 := by positivity
  nlinarith

/-- The abstract termwise estimate: the sum over the images of a function bounded by
`B e^{-c m(n)}`. -/
private lemma torus_abs_le {L : ℕ} [NeZero L] {τ : ℝ} (hτ : 0 < τ) (hτL : τ ≤ (L : ℝ) ^ 2)
    {a : ℤ} (ha : 2 * |(a : ℝ)| ≤ L) {F : ℤ → ℝ} {V B c : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hV : HasSum (fun y : ℤ => F (a + (L : ℤ) * y)) V)
    (hF : ∀ n : ℤ, |F n| ≤ B * Real.exp (-c * min (((n : ℤ) : ℝ) ^ 2 / τ) |((n : ℤ) : ℝ)|)) :
    |V| ≤ B * (∑' y : ℤ, Real.exp (-(c / 8) * |(y : ℝ)|))
      * Real.exp (-(c / 2) * min ((a : ℝ) ^ 2 / τ) |(a : ℝ)|) := by
  have hs := summable_exp_abs (c / 8) (by positivity)
  have hG : HasSum (fun y : ℤ => B * Real.exp (-(c / 2) * min ((a : ℝ) ^ 2 / τ) |(a : ℝ)|)
      * Real.exp (-(c / 8) * |(y : ℝ)|))
      (B * Real.exp (-(c / 2) * min ((a : ℝ) ^ 2 / τ) |(a : ℝ)|)
        * ∑' y : ℤ, Real.exp (-(c / 8) * |(y : ℝ)|)) := hs.hasSum.mul_left _
  have h := hV.norm_le_of_bounded hG (fun y => by
    rw [Real.norm_eq_abs]
    calc |F (a + (L : ℤ) * y)|
        ≤ B * Real.exp (-c * min ((((a + (L : ℤ) * y : ℤ)) : ℝ) ^ 2 / τ)
            |(((a + (L : ℤ) * y : ℤ)) : ℝ)|) := hF _
      _ ≤ B * (Real.exp (-(c / 2) * min ((a : ℝ) ^ 2 / τ) |(a : ℝ)|)
            * Real.exp (-(c / 8) * |(y : ℝ)|)) :=
          mul_le_mul_of_nonneg_left (image_term_le hτ hτL ha c hc y) hB
      _ = _ := by ring)
  rw [Real.norm_eq_abs] at h
  calc |V| ≤ _ := h
    _ = _ := by ring

/-- The real-variable form of `exists_rep`. -/
private lemma exists_rep_real (L : ℕ) [NeZero L] (x : ZMod L) :
    ∃ a : ℤ, (a : ZMod L) = x ∧ ((RBM.zdist L x : ℕ) : ℝ) = |(a : ℝ)| ∧ 2 * |(a : ℝ)| ≤ L := by
  obtain ⟨a, hax, hza⟩ := exists_rep L x
  have hle : 2 * ((RBM.zdist L x : ℕ) : ℤ) ≤ (L : ℤ) := by
    unfold RBM.zdist
    have := ZMod.val_lt x
    omega
  have hz : ((RBM.zdist L x : ℕ) : ℝ) = |(a : ℝ)| := by
    have : (((RBM.zdist L x : ℕ) : ℤ) : ℝ) = ((|a| : ℤ) : ℝ) := by rw [hza]
    simpa [Int.cast_abs] using this
  refine ⟨a, hax, hz, ?_⟩
  rw [← hz]
  have : (2 * ((RBM.zdist L x : ℕ) : ℤ) : ℤ) ≤ (L : ℤ) := hle
  exact_mod_cast this

private lemma shift_fun {L : ℕ} (τ : ℝ) (a b : ℤ) :
    (fun y : ℤ => hkZ τ (a + b + (L : ℤ) * y)) = fun y : ℤ => hkZ τ ((a + (L : ℤ) * y) + b) := by
  funext y
  congr 1
  ring

private lemma shift_fun' {L : ℕ} (τ : ℝ) (a b : ℤ) :
    (fun y : ℤ => hkZ τ (a - b + (L : ℤ) * y)) = fun y : ℤ => hkZ τ ((a + (L : ℤ) * y) - b) := by
  funext y
  congr 1
  ring

/-- Target 1 (`TorusBound`, `τ ≤ L²`, (a)):
`hk(τ, x) ≤ C min(1, τ^{-1/2}) e^{-c min(|x|_L²/τ, |x|_L)}`. -/
theorem hkT_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
    ∀ x : ZMod L,
      hkT L τ x ≤ C * min 1 (τ ^ (-(1 / 2 : ℝ)))
        * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_le
  have hK : 0 < ∑' y : ℤ, Real.exp (-(c / 8) * |(y : ℝ)|) :=
    (summable_exp_abs (c / 8) (by positivity)).tsum_pos (fun _ => (Real.exp_pos _).le) 0
      (Real.exp_pos _)
  refine ⟨C * ∑' y : ℤ, Real.exp (-(c / 8) * |(y : ℝ)|), c / 2, by positivity, by positivity, ?_⟩
  intro L _ τ hτ hτL x
  obtain ⟨a, hax, hza, ha⟩ := exists_rep_real L x
  have hmin : 0 ≤ min 1 (τ ^ (-(1 / 2 : ℝ))) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  have hV := hasSum_images_rep hτ.le hax
  have key := torus_abs_le hτ hτL ha hc (mul_nonneg hC.le hmin) hV (F := hkZ τ) (fun n => by
    rw [abs_of_nonneg (hkZ_nonneg τ hτ.le n)]
    exact h τ hτ n)
  rw [hza, sq_abs]
  calc hkT L τ x ≤ |hkT L τ x| := le_abs_self _
    _ ≤ _ := key
    _ = _ := by ring1

/-- Target 2 (`TorusDiff1`, `τ ≤ L²`, (b)): first difference. -/
theorem hkT_diff1_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ →
    τ ≤ (L : ℝ) ^ 2 → ∀ x : ZMod L,
      |hkT L τ (x + 1) - hkT L τ x| ≤ C * min 1 τ⁻¹
        * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_diff1_le
  have hK : 0 < ∑' y : ℤ, Real.exp (-(c / 8) * |(y : ℝ)|) :=
    (summable_exp_abs (c / 8) (by positivity)).tsum_pos (fun _ => (Real.exp_pos _).le) 0
      (Real.exp_pos _)
  refine ⟨C * ∑' y : ℤ, Real.exp (-(c / 8) * |(y : ℝ)|), c / 2, by positivity, by positivity, ?_⟩
  intro L _ τ hτ hτL x
  obtain ⟨a, hax, hza, ha⟩ := exists_rep_real L x
  have hmin : 0 ≤ min 1 τ⁻¹ := le_min zero_le_one (inv_nonneg.2 hτ.le)
  have hax1 : ((a + 1 : ℤ) : ZMod L) = x + 1 := by push_cast; rw [hax]
  have hV : HasSum (fun y : ℤ => hkZ τ ((a + (L : ℤ) * y) + 1) - hkZ τ (a + (L : ℤ) * y))
      (hkT L τ (x + 1) - hkT L τ x) := by
    have h1 := hasSum_images_rep hτ.le hax1
    have h0 := hasSum_images_rep hτ.le hax
    rw [shift_fun (L := L) τ a 1] at h1
    exact h1.sub h0
  have key := torus_abs_le hτ hτL ha hc (mul_nonneg hC.le hmin) hV
    (F := fun n => hkZ τ (n + 1) - hkZ τ n) (fun n => h τ hτ n)
  rw [hza, sq_abs]
  calc |hkT L τ (x + 1) - hkT L τ x| ≤ _ := key
    _ = _ := by ring1

/-- Target 3 (`TorusDiff2`, `τ ≤ L²`, (c)): second difference. -/
theorem hkT_diff2_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ →
    τ ≤ (L : ℝ) ^ 2 → ∀ x : ZMod L,
      |hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x|
        ≤ C * min 1 (τ ^ (-(3 / 2 : ℝ)))
          * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_diff2_le
  have hK : 0 < ∑' y : ℤ, Real.exp (-(c / 8) * |(y : ℝ)|) :=
    (summable_exp_abs (c / 8) (by positivity)).tsum_pos (fun _ => (Real.exp_pos _).le) 0
      (Real.exp_pos _)
  refine ⟨C * ∑' y : ℤ, Real.exp (-(c / 8) * |(y : ℝ)|), c / 2, by positivity, by positivity, ?_⟩
  intro L _ τ hτ hτL x
  obtain ⟨a, hax, hza, ha⟩ := exists_rep_real L x
  have hmin : 0 ≤ min 1 (τ ^ (-(3 / 2 : ℝ))) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  have hax1 : ((a + 1 : ℤ) : ZMod L) = x + 1 := by push_cast; rw [hax]
  have hax2 : ((a - 1 : ℤ) : ZMod L) = x - 1 := by push_cast; rw [hax]
  have hV : HasSum (fun y : ℤ => hkZ τ ((a + (L : ℤ) * y) + 1) + hkZ τ ((a + (L : ℤ) * y) - 1)
      - 2 * hkZ τ (a + (L : ℤ) * y))
      (hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x) := by
    have h1 := hasSum_images_rep hτ.le hax1
    have h2 := hasSum_images_rep hτ.le hax2
    have h0 := (hasSum_images_rep hτ.le hax).mul_left 2
    rw [shift_fun (L := L) τ a 1] at h1
    rw [shift_fun' (L := L) τ a 1] at h2
    exact (h1.add h2).sub h0
  have key := torus_abs_le hτ hτL ha hc (mul_nonneg hC.le hmin) hV
    (F := fun n => hkZ τ (n + 1) + hkZ τ (n - 1) - 2 * hkZ τ n) (fun n => h τ hτ n)
  rw [hza, sq_abs]
  calc |hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x| ≤ _ := key
    _ = _ := by ring1

/-! ### The spectral gap for `τ ≥ L²` -/

/-- `t e^{-t} ≤ 1` for `t ≥ 0`. -/
private lemma mul_exp_neg_le_one (t : ℝ) : t * Real.exp (-t) ≤ 1 := by
  have h : t < Real.exp t := by linarith [Real.add_one_le_exp t]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
  exact h.le

/-- Jordan's inequality for the integer `j ≤ L/2`: `1 - cos (2πj/L) ≥ 8 j²/L²`. -/
private lemma jordan_nat (j L : ℕ) (hL : 0 < L) (hj : 2 * j ≤ L) :
    8 * (j : ℝ) ^ 2 / (L : ℝ) ^ 2 ≤ 1 - Real.cos (2 * Real.pi * j / L) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hj' : 2 * (j : ℝ) ≤ L := by exact_mod_cast hj
  have hπ := Real.pi_pos
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.pi * j / L := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ Real.pi / 2 := by
    rw [hθ, div_le_div_iff₀ hLr two_pos]
    nlinarith
  have hs := Real.mul_le_sin hθ0 hθ1
  have h2 : 2 * (j : ℝ) / L ≤ Real.sin θ := by
    calc 2 * (j : ℝ) / L = 2 / Real.pi * θ := by rw [hθ]; field_simp
      _ ≤ _ := hs
  have hc : Real.cos (2 * Real.pi * j / L) = 1 - 2 * Real.sin θ ^ 2 := by
    have : 2 * Real.pi * j / L = 2 * θ := by rw [hθ]; ring
    rw [this, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hc]
  have h3 : (2 * (j : ℝ) / L) ^ 2 ≤ Real.sin θ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have h4 : 8 * (j : ℝ) ^ 2 / (L : ℝ) ^ 2 = 2 * (2 * (j : ℝ) / L) ^ 2 := by
    field_simp
    ring
  rw [h4]
  linarith

/-- Jordan's inequality on the torus: `1 - cos (2πk/L) ≥ 8 |k|_L²/L²`. -/
private lemma jordan_torus (L : ℕ) [NeZero L] (k : ZMod L) :
    8 * (RBM.zdist L k : ℝ) ^ 2 / (L : ℝ) ^ 2
      ≤ 1 - Real.cos (2 * Real.pi * (k.val : ℝ) / L) := by
  have hv : k.val < L := ZMod.val_lt k
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  by_cases h : 2 * k.val ≤ L
  · have hz : RBM.zdist L k = k.val := by unfold RBM.zdist; omega
    rw [hz]
    exact jordan_nat k.val L (NeZero.pos L) h
  · have hz : RBM.zdist L k = L - k.val := by unfold RBM.zdist; omega
    have hj : 2 * (L - k.val) ≤ L := by omega
    have h1 := jordan_nat (L - k.val) L (NeZero.pos L) hj
    have hc : Real.cos (2 * Real.pi * (k.val : ℝ) / L)
        = Real.cos (2 * Real.pi * ((L - k.val : ℕ) : ℝ) / L) := by
      rw [Nat.cast_sub hv.le]
      have : 2 * Real.pi * ((L : ℝ) - k.val) / L = 2 * Real.pi - 2 * Real.pi * (k.val : ℝ) / L := by
        field_simp
      rw [this, Real.cos_two_pi_sub]
    rw [hz, hc]
    exact h1

/-- A geometric series over the nonzero elements of `ℤ_L`, indexed by the torus distance. -/
private lemma sum_geom_zdist {L : ℕ} [NeZero L] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ RBM.zdist L k ≤ 2 * (r / (1 - r)) := by
  classical
  have key : ∀ g : ZMod L → ℕ, Function.Injective g →
      (∀ k : ZMod L, k ≠ 0 → g k ∈ Finset.Ico 1 L) →
      ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ g k ≤ r / (1 - r) := by
    intro g hg hmem
    have h1 : ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ g k
        = ∑ v ∈ ((Finset.univ : Finset (ZMod L)).erase 0).image g, r ^ v :=
      (Finset.sum_image (fun a _ b _ hab => hg hab)).symm
    rw [h1]
    calc ∑ v ∈ ((Finset.univ : Finset (ZMod L)).erase 0).image g, r ^ v
        ≤ ∑ v ∈ Finset.Ico 1 L, r ^ v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro v hv
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
            exact hmem k (Finset.ne_of_mem_erase hk)
          · intro v _ _
            positivity
      _ ≤ r ^ 1 / (1 - r) := geom_sum_Ico_le_of_lt_one hr0 hr1
      _ = r / (1 - r) := by rw [pow_one]
  have hval := key (fun k => k.val) (ZMod.val_injective L) (fun k hk => by
    simp only [Finset.mem_Ico]
    exact ⟨ZMod.val_pos.mpr hk, ZMod.val_lt k⟩)
  have hneg := key (fun k => (-k).val) ((ZMod.val_injective L).comp neg_injective) (fun k hk => by
    simp only [Finset.mem_Ico]
    have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
    exact ⟨ZMod.val_pos.mpr hk', ZMod.val_lt _⟩)
  calc ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ RBM.zdist L k
      ≤ ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, (r ^ k.val + r ^ (-k).val) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
        have hn : (-k).val = L - k.val := by rw [ZMod.neg_val]; simp [hk0]
        unfold RBM.zdist
        rw [hn]
        rcases min_choice k.val (L - k.val) with h | h
        · rw [h]; exact le_add_of_nonneg_right (by positivity)
        · rw [h]; exact le_add_of_nonneg_left (by positivity)
    _ = ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ k.val
          + ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ (-k).val :=
        Finset.sum_add_distrib
    _ ≤ 2 * (r / (1 - r)) := by linarith

/-- The angle of the mode `k`. -/
private noncomputable def ang (L : ℕ) (k : ZMod L) : ℝ := 2 * Real.pi * (k.val : ℝ) / L

/-- The tail of the spectral sum: `Σ_{k ≠ 0} e^{-τ (1 - cos θ_k)} ≤ e^{-4τ/L²} / 2` for `τ ≥ L²`. -/
private lemma tail_sum {L : ℕ} [NeZero L] {τ : ℝ} (hτ : (L : ℝ) ^ 2 ≤ τ) :
    ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, Real.exp (-(τ * (1 - Real.cos (ang L k))))
      ≤ (1 / 2) * Real.exp (-4 * τ / (L : ℝ) ^ 2) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.exp (-4) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hr1 : r ≤ 1 / 5 := by
    rw [hr, Real.exp_neg]
    have h5 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    calc (Real.exp 4)⁻¹ ≤ (5 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h5
      _ = 1 / 5 := by norm_num
  have hs : 1 ≤ τ / (L : ℝ) ^ 2 := (one_le_div hL2).mpr hτ
  have hpt : ∀ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
      Real.exp (-(τ * (1 - Real.cos (ang L k))))
        ≤ Real.exp (-4 * τ / (L : ℝ) ^ 2) * r ^ RBM.zdist L k := by
    intro k hk
    have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
    have hj1 : 1 ≤ RBM.zdist L k :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hk0 ((RBM.zdist_eq_zero_iff L).mp h))
    have hj1' : (1 : ℝ) ≤ (RBM.zdist L k : ℝ) := by exact_mod_cast hj1
    have hJ := jordan_torus L k
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = τ / (L : ℝ) ^ 2 := ⟨_, rfl⟩
    rw [← hsdef] at hs
    obtain ⟨j, hjdef⟩ : ∃ j : ℝ, j = (RBM.zdist L k : ℝ) := ⟨_, rfl⟩
    rw [← hjdef] at hj1' hJ
    have h1 : 4 * s + 4 * j ≤ τ * (1 - Real.cos (ang L k)) := by
      have h8 : 8 * s * j ^ 2 = τ * (8 * j ^ 2 / (L : ℝ) ^ 2) := by
        rw [hsdef]; field_simp
      have hj2 : (0 : ℝ) ≤ 2 * j ^ 2 - 1 := by nlinarith
      calc 4 * s + 4 * j ≤ 8 * s * j ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.2 hs) hj2,
              mul_nonneg (show (0 : ℝ) ≤ 2 * j + 1 by linarith) (sub_nonneg.2 hj1')]
        _ = τ * (8 * j ^ 2 / (L : ℝ) ^ 2) := h8
        _ ≤ τ * (1 - Real.cos (ang L k)) :=
            mul_le_mul_of_nonneg_left hJ (by linarith)
    calc Real.exp (-(τ * (1 - Real.cos (ang L k)))) ≤ Real.exp (-(4 * s + 4 * j)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-4 * τ / (L : ℝ) ^ 2) * r ^ RBM.zdist L k := by
          rw [hr, ← Real.exp_nat_mul, ← Real.exp_add, hjdef, hsdef]
          congr 1
          field_simp
          ring
  calc ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, Real.exp (-(τ * (1 - Real.cos (ang L k))))
      ≤ ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
          Real.exp (-4 * τ / (L : ℝ) ^ 2) * r ^ RBM.zdist L k := Finset.sum_le_sum hpt
    _ = Real.exp (-4 * τ / (L : ℝ) ^ 2)
          * ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ RBM.zdist L k := by
        rw [← Finset.mul_sum]
    _ ≤ Real.exp (-4 * τ / (L : ℝ) ^ 2) * (2 * (r / (1 - r))) :=
        mul_le_mul_of_nonneg_left (sum_geom_zdist hr0.le (by linarith)) (Real.exp_pos _).le
    _ ≤ Real.exp (-4 * τ / (L : ℝ) ^ 2) * (1 / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
        linarith
    _ = _ := by ring

/-- The three per-mode bounds, with `q = 1 - cos a`, `w = e^{-τ q}` and `E = e^{-2τ q}`:
`|cos u E| ≤ w`, `|(cos (u + a) - cos u) E| ≤ 2 w / L`,
`|(cos (u + a) + cos (u - a) - 2 cos u) E| ≤ 2 w / L²` (for `τ ≥ L²`). -/
private lemma mode_bounds {τ Lr : ℝ} (hLr : 1 ≤ Lr) (hτ : Lr ^ 2 ≤ τ) (u a : ℝ) :
    |Real.cos u * Real.exp (-2 * τ * (1 - Real.cos a))|
        ≤ Real.exp (-(τ * (1 - Real.cos a))) ∧
    |(Real.cos (u + a) - Real.cos u) * Real.exp (-2 * τ * (1 - Real.cos a))|
        ≤ 2 * Lr⁻¹ * Real.exp (-(τ * (1 - Real.cos a))) ∧
    |(Real.cos (u + a) + Real.cos (u - a) - 2 * Real.cos u)
        * Real.exp (-2 * τ * (1 - Real.cos a))|
        ≤ 2 * (Lr⁻¹) ^ 2 * Real.exp (-(τ * (1 - Real.cos a))) := by
  have hLpos : 0 < Lr := by linarith
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hq0 : 0 ≤ 1 - Real.cos a := by linarith [Real.cos_le_one a]
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - Real.cos a := ⟨_, rfl⟩
  rw [← hq] at hq0 ⊢
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = Real.exp (-(τ * q)) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact Real.exp_pos _
  have hw1 : w ≤ 1 := by
    rw [hw, Real.exp_le_one_iff]
    nlinarith
  have hE : Real.exp (-2 * τ * q) = w * w := by
    rw [hw, ← Real.exp_add]
    congr 1
    ring
  rw [hE, ← hw]
  -- `q w ≤ L⁻²`
  have hqw : q * w ≤ (Lr⁻¹) ^ 2 := by
    have h1 := mul_exp_neg_le_one (τ * q)
    rw [← hw] at h1
    have h2 : q * w = (τ * q * w) / τ := by field_simp
    calc q * w = (τ * q * w) / τ := h2
      _ ≤ 1 / τ := div_le_div_of_nonneg_right h1 hτpos.le
      _ ≤ 1 / Lr ^ 2 := one_div_le_one_div_of_le (by positivity) hτ
      _ = (Lr⁻¹) ^ 2 := by rw [inv_pow, one_div]
  -- `|sin a| w ≤ L⁻¹`
  have hsw : |Real.sin a| * w ≤ Lr⁻¹ := by
    have hsin : Real.sin a ^ 2 ≤ 2 * q := by
      have := Real.sin_sq_add_cos_sq a
      nlinarith [Real.cos_le_one a, Real.neg_one_le_cos a]
    have h1 := mul_exp_neg_le_one (2 * τ * q)
    have h2 : Real.exp (-(2 * τ * q)) = w * w := by
      rw [← hE]; congr 1; ring
    rw [h2] at h1
    have h3 : (|Real.sin a| * w) ^ 2 ≤ (Lr⁻¹) ^ 2 := by
      calc (|Real.sin a| * w) ^ 2 = Real.sin a ^ 2 * (w * w) := by
            rw [mul_pow, sq_abs]; ring
        _ ≤ (2 * q) * (w * w) := mul_le_mul_of_nonneg_right hsin (by positivity)
        _ = (2 * τ * q * (w * w)) / τ := by field_simp
        _ ≤ 1 / τ := div_le_div_of_nonneg_right h1 hτpos.le
        _ ≤ 1 / Lr ^ 2 := one_div_le_one_div_of_le (by positivity) hτ
        _ = (Lr⁻¹) ^ 2 := by rw [inv_pow, one_div]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp h3
  have hLinv1 : Lr⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLr
  have hLinv0 : 0 ≤ Lr⁻¹ := by positivity
  have hLinv2 : (Lr⁻¹) ^ 2 ≤ Lr⁻¹ := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ w * w)]
    calc |Real.cos u| * (w * w) ≤ 1 * (w * w) :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one u) (by positivity)
      _ ≤ w := by nlinarith
  · have hid : Real.cos (u + a) - Real.cos u
        = Real.cos u * (Real.cos a - 1) - Real.sin u * Real.sin a := by
      rw [Real.cos_add]; ring
    have hb : |Real.cos (u + a) - Real.cos u| ≤ q + |Real.sin a| := by
      rw [hid]
      calc |Real.cos u * (Real.cos a - 1) - Real.sin u * Real.sin a|
          ≤ |Real.cos u * (Real.cos a - 1)| + |Real.sin u * Real.sin a| := abs_sub _ _
        _ ≤ q + |Real.sin a| := by
          rw [abs_mul, abs_mul]
          have h1 : |Real.cos a - 1| = q := by
            rw [abs_sub_comm, ← hq, abs_of_nonneg hq0]
          rw [h1]
          have h2 := Real.abs_cos_le_one u
          have h3 := Real.abs_sin_le_one u
          have h4 := abs_nonneg (Real.sin a)
          nlinarith [abs_nonneg (Real.cos u)]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ w * w)]
    calc |Real.cos (u + a) - Real.cos u| * (w * w) ≤ (q + |Real.sin a|) * (w * w) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (q * w) * w + (|Real.sin a| * w) * w := by ring
      _ ≤ (Lr⁻¹) ^ 2 * w + Lr⁻¹ * w := by
          gcongr
      _ ≤ 2 * Lr⁻¹ * w := by nlinarith
  · have hid : Real.cos (u + a) + Real.cos (u - a) - 2 * Real.cos u
        = -(2 * Real.cos u * q) := by
      rw [Real.cos_add, Real.cos_sub, hq]; ring
    rw [hid]
    simp only [abs_mul, abs_neg, abs_two, abs_of_nonneg hq0, abs_of_nonneg hw0.le]
    calc 2 * |Real.cos u| * q * (w * w) ≤ 2 * 1 * q * (w * w) := by
          have := Real.abs_cos_le_one u
          gcongr
      _ = 2 * ((q * w) * w) := by ring
      _ ≤ 2 * ((Lr⁻¹) ^ 2 * w) := by gcongr
      _ = _ := by ring

/-- The cosine of the phase `2π k m / L` depends only on the class of `m` in `ℤ_L`. -/
private lemma cos_phase {L : ℕ} [NeZero L] (k : ZMod L) (m : ℤ) (x : ZMod L)
    (hm : (m : ZMod L) = x) :
    Real.cos (ang L k * (x.val : ℝ)) = Real.cos (ang L k * (m : ℝ)) := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have h0 : (((x.val : ℤ) - m : ℤ) : ZMod L) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, hm, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp h0
  have hx : (x.val : ℝ) = (m : ℝ) + (L : ℝ) * (t : ℝ) := by
    have : (x.val : ℤ) = m + (L : ℤ) * t := by linarith
    exact_mod_cast this
  have h2 : ang L k * (x.val : ℝ)
      = ang L k * (m : ℝ) + (((k.val : ℤ) * t : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hx]
    unfold ang
    push_cast
    field_simp
  rw [h2, Real.cos_add_int_mul_two_pi]

/-- The finite Fourier sum, read at any integer representative `m` of `x` (real value `r`). -/
private lemma hkT_form {L : ℕ} [NeZero L] (τ : ℝ) (x : ZMod L) (m : ℤ) (hm : (m : ZMod L) = x)
    (r : ℝ) (hr : (m : ℝ) = r) :
    hkT L τ x = (L : ℝ)⁻¹ * ∑ k : ZMod L,
      Real.cos (ang L k * r) * Real.exp (-2 * τ * (1 - Real.cos (ang L k))) := by
  unfold hkT
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h1 := cos_phase k m x hm
  rw [hr] at h1
  have h2 : Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
      = Real.cos (ang L k * (x.val : ℝ)) := by
    unfold ang
    congr 1
    ring
  rw [h2, h1]
  rfl

/-- The sum over the nonzero modes is bounded by the tail sum. -/
private lemma erase_sum_bound {L : ℕ} [NeZero L] {τ : ℝ} (hτ : (L : ℝ) ^ 2 ≤ τ)
    {F : ZMod L → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ k : ZMod L, |F k| ≤ M * Real.exp (-(τ * (1 - Real.cos (ang L k))))) :
    |∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, F k|
      ≤ M * ((1 / 2) * Real.exp (-4 * τ / (L : ℝ) ^ 2)) := by
  calc |∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, F k|
      ≤ ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, |F k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
          M * Real.exp (-(τ * (1 - Real.cos (ang L k)))) := Finset.sum_le_sum (fun k _ => hF k)
    _ = M * ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
          Real.exp (-(τ * (1 - Real.cos (ang L k)))) := by rw [← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (tail_sum hτ) hM

/-- Target 4 (`TorusGap`, `τ ≥ L²`): the zero mode and the spectral gap,
`|hk - 1/L| ≤ (C/L) e^{-cτ/L²}`, `|Δ₁ hk| ≤ (C/L²) e^{-cτ/L²}`, `|Δ₂ hk| ≤ (C/L³) e^{-cτ/L²}`. -/
theorem hkT_gap : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →
    ∀ x : ZMod L,
    |hkT L τ x - (L : ℝ)⁻¹| ≤ C * (L : ℝ)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
    |hkT L τ (x + 1) - hkT L τ x| ≤ C * ((L : ℝ) ^ 2)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
    |hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x|
      ≤ C * ((L : ℝ) ^ 3)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) := by
  refine ⟨1, 4, one_pos, by norm_num, ?_⟩
  intro L _ τ hτ x
  have hLpos : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hLinv : (0 : ℝ) < (L : ℝ)⁻¹ := inv_pos.mpr hLpos
  have hexp := Real.exp_pos (-4 * τ / (L : ℝ) ^ 2)
  -- the three representations of the kernel
  have hx0 := hkT_form τ x (x.val : ℤ) (by simp) (x.val : ℝ) (by simp)
  have hx1 := hkT_form τ (x + 1) ((x.val : ℤ) + 1) (by push_cast; rw [ZMod.natCast_zmod_val])
    ((x.val : ℝ) + 1) (by push_cast; rfl)
  have hx2 := hkT_form τ (x - 1) ((x.val : ℤ) - 1) (by push_cast; rw [ZMod.natCast_zmod_val])
    ((x.val : ℝ) - 1) (by push_cast; rfl)
  -- the mode bounds
  have hmode : ∀ k : ZMod L,
      |Real.cos (ang L k * (x.val : ℝ)) * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))|
          ≤ Real.exp (-(τ * (1 - Real.cos (ang L k)))) ∧
      |(Real.cos (ang L k * (x.val : ℝ) + ang L k) - Real.cos (ang L k * (x.val : ℝ)))
          * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))|
          ≤ 2 * (L : ℝ)⁻¹ * Real.exp (-(τ * (1 - Real.cos (ang L k)))) ∧
      |(Real.cos (ang L k * (x.val : ℝ) + ang L k) + Real.cos (ang L k * (x.val : ℝ) - ang L k)
          - 2 * Real.cos (ang L k * (x.val : ℝ)))
          * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))|
          ≤ 2 * ((L : ℝ)⁻¹) ^ 2 * Real.exp (-(τ * (1 - Real.cos (ang L k)))) :=
    fun k => mode_bounds hL1 hτ _ _
  have hang0 : ang L 0 = 0 := by simp [ang]
  have hE0 : ∀ (f : ZMod L → ℝ), f 0 = 0 →
      ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, f k = ∑ k : ZMod L, f k :=
    fun f hf => Finset.sum_erase _ hf
  refine ⟨?_, ?_, ?_⟩
  · -- the zero mode
    have hsplit : hkT L τ x - (L : ℝ)⁻¹ = (L : ℝ)⁻¹ * ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
        Real.cos (ang L k * (x.val : ℝ)) * Real.exp (-2 * τ * (1 - Real.cos (ang L k))) := by
      rw [hx0, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod L)), hang0]
      simp only [zero_mul, Real.cos_zero, sub_self, mul_zero, Real.exp_zero, mul_one]
      ring
    rw [hsplit, abs_mul, abs_of_pos hLinv]
    have h := erase_sum_bound hτ (M := 1) zero_le_one
      (fun k => by rw [one_mul]; exact (hmode k).1) (F := fun k =>
      Real.cos (ang L k * (x.val : ℝ)) * Real.exp (-2 * τ * (1 - Real.cos (ang L k))))
    calc (L : ℝ)⁻¹ * |∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
          Real.cos (ang L k * (x.val : ℝ)) * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))|
        ≤ (L : ℝ)⁻¹ * (1 * ((1 / 2) * Real.exp (-4 * τ / (L : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left h hLinv.le
      _ ≤ 1 * (L : ℝ)⁻¹ * Real.exp (-4 * τ / (L : ℝ) ^ 2) := by nlinarith
  · -- the first difference
    have hsplit : hkT L τ (x + 1) - hkT L τ x = (L : ℝ)⁻¹ *
        ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
          (Real.cos (ang L k * (x.val : ℝ) + ang L k) - Real.cos (ang L k * (x.val : ℝ)))
            * Real.exp (-2 * τ * (1 - Real.cos (ang L k))) := by
      rw [hx1, hx0, ← mul_sub, ← Finset.sum_sub_distrib]
      rw [hE0 _ (by simp [hang0])]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← sub_mul]
      congr 2
      rw [mul_add, mul_one]
    rw [hsplit, abs_mul, abs_of_pos hLinv]
    have h := erase_sum_bound hτ (M := 2 * (L : ℝ)⁻¹) (by positivity) (fun k => (hmode k).2.1)
      (F := fun k =>
        (Real.cos (ang L k * (x.val : ℝ) + ang L k) - Real.cos (ang L k * (x.val : ℝ)))
          * Real.exp (-2 * τ * (1 - Real.cos (ang L k))))
    calc (L : ℝ)⁻¹ * |∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
          (Real.cos (ang L k * (x.val : ℝ) + ang L k) - Real.cos (ang L k * (x.val : ℝ)))
            * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))|
        ≤ (L : ℝ)⁻¹ * (2 * (L : ℝ)⁻¹ * ((1 / 2) * Real.exp (-4 * τ / (L : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left h hLinv.le
      _ = 1 * ((L : ℝ) ^ 2)⁻¹ * Real.exp (-4 * τ / (L : ℝ) ^ 2) := by
          field_simp
  · -- the second difference
    have hsplit : hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x = (L : ℝ)⁻¹ *
        ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
          (Real.cos (ang L k * (x.val : ℝ) + ang L k) + Real.cos (ang L k * (x.val : ℝ) - ang L k)
            - 2 * Real.cos (ang L k * (x.val : ℝ)))
            * Real.exp (-2 * τ * (1 - Real.cos (ang L k))) := by
      have hpt : ∀ k : ZMod L,
          (Real.cos (ang L k * (x.val : ℝ) + ang L k) + Real.cos (ang L k * (x.val : ℝ) - ang L k)
            - 2 * Real.cos (ang L k * (x.val : ℝ)))
            * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))
          = (Real.cos (ang L k * ((x.val : ℝ) + 1)) * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))
            + Real.cos (ang L k * ((x.val : ℝ) - 1)) * Real.exp (-2 * τ * (1 - Real.cos (ang L k))))
            - 2 * (Real.cos (ang L k * (x.val : ℝ))
              * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))) := by
        intro k
        have e1 : ang L k * ((x.val : ℝ) + 1) = ang L k * (x.val : ℝ) + ang L k := by ring
        have e2 : ang L k * ((x.val : ℝ) - 1) = ang L k * (x.val : ℝ) - ang L k := by ring
        rw [e1, e2]
        ring
      simp_rw [hpt]
      rw [hE0 _ (by simp [hang0]; norm_num), Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx1, hx2, hx0]
      ring
    rw [hsplit, abs_mul, abs_of_pos hLinv]
    have h := erase_sum_bound hτ (M := 2 * ((L : ℝ)⁻¹) ^ 2) (by positivity)
      (fun k => (hmode k).2.2)
      (F := fun k =>
        (Real.cos (ang L k * (x.val : ℝ) + ang L k) + Real.cos (ang L k * (x.val : ℝ) - ang L k)
          - 2 * Real.cos (ang L k * (x.val : ℝ)))
          * Real.exp (-2 * τ * (1 - Real.cos (ang L k))))
    calc (L : ℝ)⁻¹ * |∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0,
          (Real.cos (ang L k * (x.val : ℝ) + ang L k) + Real.cos (ang L k * (x.val : ℝ) - ang L k)
            - 2 * Real.cos (ang L k * (x.val : ℝ)))
            * Real.exp (-2 * τ * (1 - Real.cos (ang L k)))|
        ≤ (L : ℝ)⁻¹ * (2 * ((L : ℝ)⁻¹) ^ 2 * ((1 / 2) * Real.exp (-4 * τ / (L : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left h hLinv.le
      _ = 1 * ((L : ℝ) ^ 3)⁻¹ * Real.exp (-4 * τ / (L : ℝ) ^ 2) := by
          field_simp

/-! ### Compiled instances

Each target theorem applied at `L = 5`, `x = 2` (`|x|_L = 2`): `τ = 4 ≤ 25 = L²` for the three
bounds and `τ = 50 ≥ 25 = L²` for the gap.  Every deterministic hypothesis is discharged; the
constants stay existential, as in the statements. -/

-- `hkT_le` at `L = 5`, `τ = 4`, `x = 2`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    hkT 5 4 2 ≤ C * min 1 ((4 : ℝ) ^ (-(1 / 2 : ℝ)))
      * Real.exp (-c * min ((RBM.zdist 5 2 : ℝ) ^ 2 / 4) (RBM.zdist 5 2 : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkT_le
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) 2⟩

-- `hkT_diff1_le` at `L = 5`, `τ = 4`, `x = 2`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkT 5 4 (2 + 1) - hkT 5 4 2| ≤ C * min 1 ((4 : ℝ)⁻¹)
      * Real.exp (-c * min ((RBM.zdist 5 2 : ℝ) ^ 2 / 4) (RBM.zdist 5 2 : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkT_diff1_le
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) 2⟩

-- `hkT_diff2_le` at `L = 5`, `τ = 4`, `x = 2`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkT 5 4 (2 + 1) + hkT 5 4 (2 - 1) - 2 * hkT 5 4 2|
      ≤ C * min 1 ((4 : ℝ) ^ (-(3 / 2 : ℝ)))
        * Real.exp (-c * min ((RBM.zdist 5 2 : ℝ) ^ 2 / 4) (RBM.zdist 5 2 : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkT_diff2_le
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) 2⟩

-- `hkT_gap` at `L = 5`, `τ = 50`, `x = 2`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (|hkT 5 50 2 - ((5 : ℕ) : ℝ)⁻¹|
        ≤ C * ((5 : ℕ) : ℝ)⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2) ∧
      |hkT 5 50 (2 + 1) - hkT 5 50 2|
        ≤ C * (((5 : ℕ) : ℝ) ^ 2)⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2) ∧
      |hkT 5 50 (2 + 1) + hkT 5 50 (2 - 1) - 2 * hkT 5 50 2|
        ≤ C * (((5 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkT_gap
  exact ⟨C, c, hC, hc, h 5 50 (by norm_num) 2⟩

end RBM.Heat
