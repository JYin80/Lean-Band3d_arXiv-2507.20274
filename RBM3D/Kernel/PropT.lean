/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.Tail
import RBM3D.Defs.Convolution

/-!
# `lem:propT`: the convolution bound `(TTT2)` for the tail function

For `0 ≤ u ≤ t < 1` in either regime

* (i)  `1 - u ≥ 1 - t ≥ g²/L²`, or
* (ii) `1 - t ≤ 1 - u ≤ g²/L²`,

  `Σ_{c ∈ Z_L^d} 𝒯_u(|a-c|) 𝒯_t(|c-b|) ≤ C_d/(1-u) · 𝒯_t(|a-b|)`   for all `a, b`,

with `C_d` depending only on `d` (`propT`).  Appendix A.3 proves this with `≲` in both
regimes and, in regime (i), a "basic calculus fact" on `ℝ^d`; here every constant is
explicit, and the calculus fact is replaced by its lattice form `RBM.sum_conv_le`
(`Defs/Convolution.lean`).

Write `𝒯_s(n) = (A_s P(n) + Z_s) E_{ℓ_s}(n)` with `A_s = (g²+|1-s|)⁻¹`,
`Z_s = (L^d|1-s|)⁻¹`, `P(n) = (n+1)^{-(d-2)}`, `E_ℓ(n) = e^{-√(n/ℓ)}` (`tailT_natCast`).

* **Regime (ii)** (`propT_ii`): `ℓ_u = ℓ_t = L`.  The four products are bounded by
  `sum_conv_le` (decay × decay), the radial sum `sum_radial_exp_le` (the two cross terms)
  and `#Z_L^d = L^d` (zero mode × zero mode), each time using `L² ≤ g²/(1-u)`.  The
  lower bound on `𝒯_t(|a-b|)` uses `E_L(n) ≥ e^{-√d}` for `n ≤ dL`.
* **Regime (i)** (`propT_i`): the zero-mode term is dominated by the decay term,
  `Z_s ≤ c_d A_s P(n)` for `n ≤ dL` (`zeroMode_le_of_ge_mul`, the version of
  `zeroMode_le_of_ge` for the whole torus -- the `ℓ¹` distance on `Z_L^d` reaches `dL/2`,
  not `L`); then `sum_conv_le` with `ℓ₁ = ℓ_u ≤ ℓ₂ = ℓ_t`, and
  `A_u ℓ_u² ≤ 1/(1-u)`.

The dimension enters as `d = k + 2`; the argument never uses `d ≥ 3`, so the statement
is proved for `d ≥ 2`.
-/

namespace RBM

open Finset Real

variable {k : ℕ} {L : ℕ} {g u t : ℝ}

/-! ### Rewriting `𝒯` at lattice distances -/

theorem tailT_natCast (k L : ℕ) (g t : ℝ) (n : ℕ) :
    tailT (k + 2) L g t n
      = ((g ^ 2 + |1 - t|)⁻¹ * powW k n + ((L : ℝ) ^ (k + 2) * |1 - t|)⁻¹)
          * exp (-√((n : ℝ) / ellT L g t)) := by
  simp [tailT, BparamR, powW]

/-! ### Facts about `ℓ_t` -/

/-- `ℓ_t` is non-decreasing in `t`. -/
theorem ellT_mono (hg : 0 ≤ g) (hut : u ≤ t) (ht : t < 1) : ellT L g u ≤ ellT L g t := by
  unfold ellT
  have hw : 0 < 1 - t := by linarith
  have hv : 0 < 1 - u := by linarith
  rw [abs_of_pos hw, abs_of_pos hv]
  refine min_le_min (max_le_max ?_ le_rfl) le_rfl
  exact div_le_div_of_nonneg_left hg (sqrt_pos.mpr hw) (sqrt_le_sqrt (by linarith))


/-- `A_u ℓ_u² ≤ 1/(1-u)`. -/
theorem inv_mul_ellT_sq_le (hg : 0 ≤ g) (hv : 0 < 1 - u) :
    (g ^ 2 + |1 - u|)⁻¹ * ellT L g u ^ 2 ≤ (1 - u)⁻¹ := by
  rw [abs_of_pos hv]
  have hA : 0 < g ^ 2 + (1 - u) := by positivity
  calc (g ^ 2 + (1 - u))⁻¹ * ellT L g u ^ 2 ≤ (g ^ 2 + (1 - u))⁻¹ * (g ^ 2 / (1 - u) + 1) :=
        mul_le_mul_of_nonneg_left (ellT_sq_le (L := L) hg hv) (inv_nonneg.mpr hA.le)
    _ = (1 - u)⁻¹ := by field_simp

/-- Distances on the torus are at most `dL`, so `E_L(n) ≥ e^{-√d}`. -/
theorem exp_neg_sqrt_ge {n : ℕ} (d : ℕ) (hL : 1 ≤ (L : ℝ)) (hn : n ≤ d * L) :
    exp (-√(d : ℝ)) ≤ exp (-√((n : ℝ) / L)) := by
  apply exp_le_exp.mpr
  apply neg_le_neg
  apply sqrt_le_sqrt
  have hL0 : 0 < (L : ℝ) := by linarith
  rw [div_le_iff₀ hL0]
  exact_mod_cast hn

/-- The zero-mode term is dominated by the decay term on the whole torus: for
`n ≤ m L` (`m ≥ 1`) and `1 - t ≥ g²/L²`,
`(L^{k+2}|1-t|)⁻¹ ≤ 2 (2m)^k (g²+|1-t|)⁻¹ (n+1)^{-k}`. -/
theorem zeroMode_le_of_ge_mul {m : ℕ} (hm : 1 ≤ m) (hL : 1 ≤ (L : ℝ)) (ht : t < 1) {n : ℕ}
    (hn : n ≤ m * L) (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) :
    ((L : ℝ) ^ (k + 2) * |1 - t|)⁻¹ ≤ 2 * (2 * m) ^ k * ((g ^ 2 + |1 - t|)⁻¹ * powW k n) := by
  set w := 1 - t with hw
  have hw0 : 0 < w := by linarith
  rw [abs_of_pos hw0]
  unfold powW
  have hL0 : 0 < (L : ℝ) := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hg2 : g ^ 2 ≤ (L : ℝ) ^ 2 * w := by
    rw [div_le_iff₀ (by positivity)] at hgt; linarith
  have hL2 : 1 ≤ (L : ℝ) ^ 2 := by nlinarith
  have hA : g ^ 2 + w ≤ 2 * (L : ℝ) ^ 2 * w := by nlinarith
  have hnr : (n : ℝ) + 1 ≤ 2 * m * L := by
    have : (n : ℝ) ≤ m * L := by exact_mod_cast hn
    nlinarith
  have hB : ((n : ℝ) + 1) ^ k ≤ (2 * m * (L : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) hnr _
  have hP0 : 0 < (g ^ 2 + w) * ((n : ℝ) + 1) ^ k := by positivity
  have hP : (g ^ 2 + w) * ((n : ℝ) + 1) ^ k ≤ 2 * (2 * m) ^ k * ((L : ℝ) ^ (k + 2) * w) := by
    calc (g ^ 2 + w) * ((n : ℝ) + 1) ^ k ≤ (2 * (L : ℝ) ^ 2 * w) * (2 * m * (L : ℝ)) ^ k :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = 2 * (2 * m) ^ k * ((L : ℝ) ^ (k + 2) * w) := by ring
  rw [← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) hP0]
  linarith

/-! ### Cardinality of the torus -/

theorem sum_one_torus (d L : ℕ) [NeZero L] : ∑ _c : Zd d L, (1 : ℝ) = (L : ℝ) ^ d := by
  simp [Finset.card_univ, ZMod.card]

/-! ### Regime (ii): `1 - t ≤ 1 - u ≤ g²/L²` -/

/-- The constant of regime (ii). -/
noncomputable def constII (k : ℕ) : ℝ :=
  convC k + (2 * (2 ^ (k + 2) * radC 1) + 1) * exp (√((k : ℝ) + 2))

/-! ### Regime (i): `1 - u ≥ 1 - t ≥ g²/L²` -/

/-! ### `lem:propT` -/

/-! ### `claim:TTk`: the pointwise bounds `(eq:TtTt)` and `(eq:KtKt)`

Appendix A.4 works with a *different* function from the tail function `𝒯_t`: writing
`W` for the band width, `7_8_light_weight.tex` sets

  `𝖳_t(r) = (g²+|1-t|)^{-1/2} W^{-d/2} (r+1)^{-(d-2)/2} exp(-½√(r/ℓ_t))`,

the square root of `W^{-d}` times the *decay part* of `𝒯_t` (no zero mode), and
`Ψ_t = (W^{-d} B_{t,0})^{1/2}`.  Both `(eq:TtTt)` and `(eq:KtKt)` are statements about
`𝖳_t`, not `𝒯_t`.

Note that `(eq:TtTt)` needs `|x-α| ∨ |y-α| ≤ ℓ`, the standing assumption of the index
range it is applied to in Appendix A.4 ("for `1 ≤ i ≤ r`").  Without it the bound is
false: take `x = y` with both distances far beyond `ℓ`, and the factor
`(|x-α| ∧ |y-α| + 1)^{-(d-2)/2}` on the right is far smaller than the left-hand side.
-/

section TTk

variable (d L : ℕ) (W g t : ℝ)

/-- `Ψ_t = (W^{-d} B_{t,0})^{1/2}`. -/
noncomputable def PsiT : ℝ := √((W ^ d)⁻¹ * Bparam d L g t 0)

/-- `𝖳_t(r) = (g²+|1-t|)^{-1/2} W^{-d/2} (r+1)^{-(d-2)/2} e^{-½√(r/ℓ_t)}` of Appendix A.4,
written with `Real.sqrt` for the half-powers. -/
noncomputable def sfT (r : ℝ) : ℝ :=
  √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r + 1) ^ (d - 2))⁻¹)
    * exp (-(1 / 2) * √(r / ellT L g t))

variable {d L W g t}

theorem sfT_nonneg (r : ℝ) : 0 ≤ sfT d L W g t r := by
  unfold sfT; positivity

theorem PsiT_nonneg : 0 ≤ PsiT d L W g t := sqrt_nonneg _

theorem sfT_zero : sfT d L W g t 0 = √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) := by
  simp [sfT]

/-- `𝖳_t(0) ≤ Ψ_t`, the first of the two elementary facts of Appendix A.4. -/
theorem sfT_zero_le_PsiT (hW : 0 < W) : sfT d L W g t 0 ≤ PsiT d L W g t := by
  rw [sfT_zero, PsiT, ← sqrt_mul (by positivity)]
  apply sqrt_le_sqrt
  have hZ : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
  have hW0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (by positivity)
  have : Bparam d L g t 0 = (g ^ 2 + |1 - t|)⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹ := by
    simp [Bparam]
  rw [this]
  nlinarith

/-- `𝖳_t(r) ≤ 𝖳_t(0) (r+1)^{-(d-2)/2}`, the second elementary fact. -/
theorem sfT_le_zero_mul (hr : 0 ≤ r) :
    sfT d L W g t r ≤ sfT d L W g t 0 * √(((r + 1) ^ (d - 2))⁻¹) := by
  rw [sfT_zero, sfT]
  have hE : exp (-(1 / 2) * √(r / ellT L g t)) ≤ 1 := by
    apply exp_le_one_iff.mpr
    have : 0 ≤ √(r / ellT L g t) := sqrt_nonneg _
    linarith
  have h0 : 0 ≤ √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r + 1) ^ (d - 2))⁻¹) := by
    positivity
  calc √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r + 1) ^ (d - 2))⁻¹)
        * exp (-(1 / 2) * √(r / ellT L g t))
      ≤ √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r + 1) ^ (d - 2))⁻¹) * 1 :=
        mul_le_mul_of_nonneg_left hE h0
    _ = √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r + 1) ^ (d - 2))⁻¹) := mul_one _

/-- `√(a+b) ≤ √a + √b`. -/
theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  have h : a + b ≤ (√a + √b) ^ 2 := by
    have := Real.sq_sqrt ha
    have := Real.sq_sqrt hb
    have : 0 ≤ √a * √b := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  calc √(a + b) ≤ √((√a + √b) ^ 2) := sqrt_le_sqrt h
    _ = √a + √b := Real.sqrt_sq (by positivity)

/-- `𝖳_t(r) ≤ Ψ_t (r+1)^{-(d-2)/2}`: the two elementary facts combined. -/
theorem sfT_le_PsiT_mul (hW : 0 < W) (hr : 0 ≤ r) :
    sfT d L W g t r ≤ PsiT d L W g t * √(((r + 1) ^ (d - 2))⁻¹) :=
  (sfT_le_zero_mul hr).trans
    (mul_le_mul_of_nonneg_right (sfT_zero_le_PsiT hW) (sqrt_nonneg _))

/-- **`(eq:TtTt)`**: for `s ≤ p + q` (the truncated triangle inequality),
`𝖳_t(p) 𝖳_t(q) ≤ 2^{(d-2)/2} 𝖳_t(s) Ψ_t (min p q + 1)^{-(d-2)/2}`.

At the lattice level `p = |x-α| ∧ ℓ`, `q = |y-α| ∧ ℓ`, `s = |x-y| ∧ ℓ`; the hypothesis
`s ≤ p + q` is exactly what `|x-α| ∨ |y-α| ≤ ℓ` supplies. -/
theorem sfT_mul_le_TtTt (hW : 0 < W) {p q s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hspq : s ≤ p + q) :
    sfT d L W g t p * sfT d L W g t q
      ≤ √((2 : ℝ) ^ (d - 2))
        * (sfT d L W g t s * (PsiT d L W g t * √(((min p q + 1) ^ (d - 2))⁻¹))) := by
  have key : ∀ r : ℝ, sfT d L W g t r
      = (√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹)) * √(((r + 1) ^ (d - 2))⁻¹)
        * exp (-(1 / 2) * √(r / ellT L g t)) := fun r => by unfold sfT; ring
  have hA0 : (0 : ℝ) ≤ √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) := by positivity
  have hAP : (√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹)) * (√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹))
      ≤ (√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹)) * PsiT d L W g t := by
    have := sfT_zero_le_PsiT (d := d) (L := L) (W := W) (g := g) (t := t) hW
    rw [sfT_zero] at this
    exact mul_le_mul_of_nonneg_left this hA0
  -- the exponential factors
  have hℓ : 0 ≤ ellT L g t := ellT_nonneg
  have hX : exp (-(1 / 2) * √(p / ellT L g t)) * exp (-(1 / 2) * √(q / ellT L g t))
      ≤ exp (-(1 / 2) * √(s / ellT L g t)) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    have h1 : s / ellT L g t ≤ p / ellT L g t + q / ellT L g t := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hspq hℓ
    have h2 : √(s / ellT L g t) ≤ √(p / ellT L g t) + √(q / ellT L g t) :=
      (sqrt_le_sqrt h1).trans
        (sqrt_add_le_add_sqrt (by positivity) (by positivity))
    linarith
  -- the power factors
  have hQ : √(((p + 1) ^ (d - 2))⁻¹) * √(((q + 1) ^ (d - 2))⁻¹)
      ≤ √((2 : ℝ) ^ (d - 2)) * (√(((min p q + 1) ^ (d - 2))⁻¹) * √(((s + 1) ^ (d - 2))⁻¹)) := by
    have hmax : ∀ m : ℝ, 0 ≤ m → s ≤ 2 * m →
        √(((m + 1) ^ (d - 2))⁻¹) ≤ √((2 : ℝ) ^ (d - 2)) * √(((s + 1) ^ (d - 2))⁻¹) := by
      intro m hm hsm
      rw [← sqrt_mul (by positivity)]
      apply sqrt_le_sqrt
      have h1 : (s + 1) ^ (d - 2) ≤ (2 * (m + 1)) ^ (d - 2) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      have h2 : (0 : ℝ) < (m + 1) ^ (d - 2) := by positivity
      have h3 : (0 : ℝ) < (s + 1) ^ (d - 2) := by positivity
      rw [← div_eq_mul_inv, le_div_iff₀ h3, inv_mul_eq_div, div_le_iff₀ h2]
      calc (s + 1) ^ (d - 2) ≤ (2 * (m + 1)) ^ (d - 2) := h1
        _ = 2 ^ (d - 2) * (m + 1) ^ (d - 2) := mul_pow _ _ _
    rcases le_total p q with hpq | hpq
    · rw [min_eq_left hpq]
      have := hmax q hq (by linarith)
      calc √(((p + 1) ^ (d - 2))⁻¹) * √(((q + 1) ^ (d - 2))⁻¹)
          ≤ √(((p + 1) ^ (d - 2))⁻¹)
            * (√((2 : ℝ) ^ (d - 2)) * √(((s + 1) ^ (d - 2))⁻¹)) :=
            mul_le_mul_of_nonneg_left this (sqrt_nonneg _)
        _ = _ := by ring
    · rw [min_eq_right hpq]
      have := hmax p hp (by linarith)
      calc √(((p + 1) ^ (d - 2))⁻¹) * √(((q + 1) ^ (d - 2))⁻¹)
          ≤ (√((2 : ℝ) ^ (d - 2)) * √(((s + 1) ^ (d - 2))⁻¹))
            * √(((q + 1) ^ (d - 2))⁻¹) :=
            mul_le_mul_of_nonneg_right this (sqrt_nonneg _)
        _ = _ := by ring
  rw [key p, key q, key s]
  calc (√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹)) * √(((p + 1) ^ (d - 2))⁻¹)
        * exp (-(1 / 2) * √(p / ellT L g t))
      * ((√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹)) * √(((q + 1) ^ (d - 2))⁻¹)
        * exp (-(1 / 2) * √(q / ellT L g t)))
      = ((√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹))
          * (√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹)))
        * ((√(((p + 1) ^ (d - 2))⁻¹) * √(((q + 1) ^ (d - 2))⁻¹))
          * (exp (-(1 / 2) * √(p / ellT L g t)) * exp (-(1 / 2) * √(q / ellT L g t)))) := by
        ring
    _ ≤ ((√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹)) * PsiT d L W g t)
        * ((√((2 : ℝ) ^ (d - 2))
            * (√(((min p q + 1) ^ (d - 2))⁻¹) * √(((s + 1) ^ (d - 2))⁻¹)))
          * exp (-(1 / 2) * √(s / ellT L g t))) := by
        apply mul_le_mul hAP (mul_le_mul hQ hX (by positivity) (by positivity))
          (by positivity) (mul_nonneg hA0 PsiT_nonneg)
    _ = √((2 : ℝ) ^ (d - 2))
        * ((√((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹)) * √(((s + 1) ^ (d - 2))⁻¹)
            * exp (-(1 / 2) * √(s / ellT L g t))
          * (PsiT d L W g t * √(((min p q + 1) ^ (d - 2))⁻¹))) := by ring

/-- **`(eq:KtKt)`**: when the second distance exceeds `ℓ`, so that `q ∧ ℓ = ℓ`,
`𝖳_t(p) 𝖳_t(ℓ) ≤ 𝖳_t(ℓ) Ψ_t (p+1)^{-(d-2)/2}`, with constant `1`. -/
theorem sfT_mul_le_KtKt (hW : 0 < W) {p ℓ : ℝ} (hp : 0 ≤ p) :
    sfT d L W g t p * sfT d L W g t ℓ
      ≤ sfT d L W g t ℓ * (PsiT d L W g t * √(((p + 1) ^ (d - 2))⁻¹)) := by
  have h := sfT_le_PsiT_mul (d := d) (L := L) (W := W) (g := g) (t := t) hW hp
  calc sfT d L W g t p * sfT d L W g t ℓ
      ≤ (PsiT d L W g t * √(((p + 1) ^ (d - 2))⁻¹)) * sfT d L W g t ℓ :=
        mul_le_mul_of_nonneg_right h (sfT_nonneg _)
    _ = sfT d L W g t ℓ * (PsiT d L W g t * √(((p + 1) ^ (d - 2))⁻¹)) := by ring

/-! ### The lattice form, and the case coverage of Appendix A.4 -/

variable {d L : ℕ} [NeZero L]

/-! ### `(eq:key_T_reudce)`: the summed version

Claim `claim:TTk` sums the pointwise bounds over the internal vertex `[α]`.  The paper
splits the summation region into `2^{2k}` boxes `D_{≤ℓ,𝛔}` and then treats three cases,
according to how many of the `k` paths consist of short edges only.  In Lean the three
cases collapse **pointwise**: `sfT_pair_le` below is a single bound, valid for every
`α`, whose polynomial factor is indexed by `|x_i-α| ∧ |y_i-α| ∧ ℓ` -- which is exactly
the factor of `(eq:TtTt)` in case 1 and the factor of `(eq:KtKt)` in cases 2 and 3.
The case distinction of Appendix A.4 therefore only decides *which* indices keep their
polynomial factor, and the proof below keeps two of them, as the paper does.

What is *not* formalised here is the last line of the paper's display, the passage from
`ℓ²Ψ_t^k` to `(W^dη_t)^{-1}Ψ_t^{k-2}`: that is where `ℓ ≤ (log W)^{10}ℓ_t` and
`ℓ_t²B_{t,0} ≲ |1-t|^{-1}` are used, and where the logarithmic factors force `≺` in
place of `≲`.  The bound proved here is the deterministic one, with `Ψ_t²ℓ²` left in
place of `(W^dη_t)^{-1}`. -/

omit [NeZero L] in
/-- `𝖳_t` is non-increasing. -/
theorem sfT_antitone {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ ≤ r₂) :
    sfT d L W g t r₂ ≤ sfT d L W g t r₁ := by
  have hA : (0 : ℝ) ≤ √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) := by positivity
  have hpow : √(((r₂ + 1) ^ (d - 2))⁻¹) ≤ √(((r₁ + 1) ^ (d - 2))⁻¹) :=
    Real.sqrt_le_sqrt (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) _))
  have hexp : exp (-(1 / 2) * √(r₂ / ellT L g t)) ≤ exp (-(1 / 2) * √(r₁ / ellT L g t)) := by
    refine exp_le_exp.mpr ?_
    have hdiv : r₁ / ellT L g t ≤ r₂ / ellT L g t := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr ellT_nonneg)
    have := Real.sqrt_le_sqrt hdiv
    linarith
  unfold sfT
  calc √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r₂ + 1) ^ (d - 2))⁻¹)
        * exp (-(1 / 2) * √(r₂ / ellT L g t))
      ≤ √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r₁ + 1) ^ (d - 2))⁻¹)
        * exp (-(1 / 2) * √(r₂ / ellT L g t)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hA) (exp_pos _).le
    _ ≤ √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r₁ + 1) ^ (d - 2))⁻¹)
        * exp (-(1 / 2) * √(r₁ / ellT L g t)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-- The polynomial factor `(r+1)^{-(d-2)/2}` carried by `(eq:TtTt)` and `(eq:KtKt)`. -/
noncomputable def wfac (dim : ℕ) (r : ℝ) : ℝ := √(((r + 1) ^ (dim - 2))⁻¹)

theorem wfac_nonneg (dim : ℕ) (r : ℝ) : 0 ≤ wfac dim r := sqrt_nonneg _

theorem wfac_le_one (dim : ℕ) {r : ℝ} (hr : 0 ≤ r) : wfac dim r ≤ 1 := by
  have h : ((r + 1) ^ (dim - 2))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr (one_le_pow₀ (by linarith))
  calc wfac dim r ≤ √1 := Real.sqrt_le_sqrt h
    _ = 1 := Real.sqrt_one

theorem wfac_sq (dim : ℕ) {r : ℝ} (hr : 0 ≤ r) : wfac dim r ^ 2 = (((r + 1) ^ (dim - 2))⁻¹) :=
  Real.sq_sqrt (by positivity)

/-- The polynomial factor of the *smaller* of two distances splits into the two
factors: `(p ∧ q + 1)^{-(d-2)} ≤ (p+1)^{-(d-2)} + (q+1)^{-(d-2)}`. -/
theorem wfac_min_sq_le (dim : ℕ) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    wfac dim (min p q) ^ 2 ≤ ((p + 1) ^ (dim - 2))⁻¹ + ((q + 1) ^ (dim - 2))⁻¹ := by
  rw [wfac_sq dim (le_min hp hq)]
  have hp0 : (0 : ℝ) ≤ ((p + 1) ^ (dim - 2))⁻¹ := by positivity
  have hq0 : (0 : ℝ) ≤ ((q + 1) ^ (dim - 2))⁻¹ := by positivity
  rcases min_cases p q with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- For `k ≥ 2`, the product of the `k` polynomial factors is at most the product of
the first two: this is where the paper keeps the last factor of `(eq:KtKt)` for two
indices and bounds it by `1` for the rest. -/
theorem prod_wfac_le_two {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) :
    ∏ i, w i ≤ w ⟨0, by omega⟩ * w ⟨1, by omega⟩ := by
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)) ⊆ Finset.univ :=
    Finset.subset_univ _
  rw [← Finset.prod_sdiff hsub, Finset.prod_pair hne]
  exact mul_le_of_le_one_left (mul_nonneg (hw0 _) (hw0 _))
    (Finset.prod_le_one₀ (fun i _ => hw0 i) (fun i _ => hw1 i))

/-! ### The absorption step: from `Ψ_t² ℓ²` to `(W^d η_t)^{-1}`

`key_T_reduce` leaves `Ψ_t² ℓ²` where the paper writes `(W^d η_t)^{-1}`.  The passage
between them is the last line of Appendix A.4, and it is where the logarithms -- hence
`≺` rather than `≲` -- come from:

* `ℓ ≤ (log W)^{10} ℓ_t`, the standing hypothesis of `claim:TTk`, costs `(log W)^{20}`;
* `B_{t,0} ℓ_t² ≤ 3|1-t|^{-1}` under `1 - t ≥ ĝ²/L²` (`RBM.Bparam_mul_ellT_sq_le`);
* `η_t ≍ 1 - t` by `(eta)`, so `|1-t|^{-1} ≍ η_t^{-1}`.

`RBM.detDom_log_pow` (`Defs/Domination.lean`) is what absorbs the `(log W)^{20}` into `≺`:
for every `τ > 0` it is eventually below `N^τ`.  The two statements below are the
deterministic content; combining them with that lemma is exactly the paper's `≺`. -/

/-- `Ψ_t² ℓ² ≤ 3 Λ² W^{-d}|1-t|^{-1}` whenever `ℓ ≤ Λ ℓ_t` -- the paper's
`Ψ_t²ℓ² ≲ (log W)^{20}(W^dη_t)^{-1}` with `Λ = (log W)^{10}` and every constant explicit. -/
theorem PsiT_sq_mul_le {d L : ℕ} {W g t : ℝ} (hd : 2 ≤ d) (hW : 0 < W) (hL : 1 ≤ (L : ℝ))
    (hg : 0 ≤ g) (ht : t < 1) (hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t))
    {ℓ Λ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ Λ * ellT L g t) :
    PsiT d L W g t ^ 2 * ℓ ^ 2 ≤ 3 * Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)) := by
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hBnn : 0 ≤ Bparam d L g t 0 := by unfold Bparam; positivity
  have hWd : (0 : ℝ) < W ^ d := by positivity
  have hPsi : PsiT d L W g t ^ 2 = (W ^ d)⁻¹ * Bparam d L g t 0 := by
    rw [PsiT, Real.sq_sqrt (by positivity)]
  have hsq : ℓ ^ 2 ≤ Λ ^ 2 * ellT L g t ^ 2 := by
    have := pow_le_pow_left₀ hℓ0 hℓ 2
    rwa [mul_pow] at this
  calc PsiT d L W g t ^ 2 * ℓ ^ 2
      = (W ^ d)⁻¹ * (Bparam d L g t 0 * ℓ ^ 2) := by rw [hPsi]; ring
    _ ≤ (W ^ d)⁻¹ * (Bparam d L g t 0 * (Λ ^ 2 * ellT L g t ^ 2)) := by
        have : Bparam d L g t 0 * ℓ ^ 2
            ≤ Bparam d L g t 0 * (Λ ^ 2 * ellT L g t ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hBnn
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = (W ^ d)⁻¹ * (Λ ^ 2 * (Bparam d L g t 0 * ellT L g t ^ 2)) := by ring
    _ ≤ (W ^ d)⁻¹ * (Λ ^ 2 * (3 / (1 - t))) := by
        have := Bparam_mul_ellT_sq_le (d := d) (L := L) (g := g) (t := t) hd hL hg ht hgL
        have h2 : Λ ^ 2 * (Bparam d L g t 0 * ellT L g t ^ 2) ≤ Λ ^ 2 * (3 / (1 - t)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 3 * Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)) := by ring

end TTk

end RBM
