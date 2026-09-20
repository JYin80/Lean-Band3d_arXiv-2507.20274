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

/-- `ℓ_u² ≤ g²/(1-u) + 1`. -/
theorem ellT_sq_le (hg : 0 ≤ g) (hv : 0 < 1 - u) :
    ellT L g u ^ 2 ≤ g ^ 2 / (1 - u) + 1 := by
  have h0 : 0 ≤ ellT L g u := ellT_nonneg
  have hx : 0 ≤ g / √|1 - u| := div_nonneg hg (sqrt_nonneg _)
  have hle : ellT L g u ≤ max (g / √|1 - u|) 1 := min_le_left _ _
  have hsq : (g / √|1 - u|) ^ 2 = g ^ 2 / (1 - u) := by
    rw [div_pow, sq_sqrt (abs_nonneg _), abs_of_pos hv]
  calc ellT L g u ^ 2 ≤ (max (g / √|1 - u|) 1) ^ 2 := pow_le_pow_left₀ h0 hle 2
    _ ≤ (g / √|1 - u|) ^ 2 + 1 := by
        rcases le_total (g / √|1 - u|) 1 with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; linarith
    _ = g ^ 2 / (1 - u) + 1 := by rw [hsq]

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

/-- **`lem:propT`, regime (ii).** -/
theorem propT_ii [NeZero L] (hg : 0 < g) (hut : u ≤ t) (ht : t < 1)
    (h : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) (a b : Zd (k + 2) L) :
    ∑ c : Zd (k + 2) L, tailT (k + 2) L g u (zdistD (k + 2) L (a - c))
        * tailT (k + 2) L g t (zdistD (k + 2) L (c - b))
      ≤ constII k / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b)) := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := NeZero.ne L
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hL0 : (0 : ℝ) < L := by linarith
  set v := 1 - u with hv_def
  set w := 1 - t with hw_def
  have hw : 0 < w := by linarith
  have hv : 0 < v := by linarith
  have hwv : w ≤ v := by linarith
  have hlu : ellT L g u = L := ellT_eq_of_le hg.le (by linarith) hL1 h
  have hlt : ellT L g t = L := ellT_eq_of_le hg.le ht hL1 (by linarith)
  simp only [tailT_natCast, hlu, hlt]
  rw [abs_of_pos hv, abs_of_pos hw]
  -- abbreviations
  set Au := (g ^ 2 + v)⁻¹ with hAu
  set At := (g ^ 2 + w)⁻¹ with hAt
  set Zu := ((L : ℝ) ^ (k + 2) * v)⁻¹ with hZu
  set Zt := ((L : ℝ) ^ (k + 2) * w)⁻¹ with hZt
  set P : Zd (k + 2) L → ℝ := fun x => powW k (zdistD (k + 2) L x) with hP
  set E : Zd (k + 2) L → ℝ := fun x => exp (-√((zdistD (k + 2) L x : ℝ) / L)) with hE
  change ∑ c, (Au * P (a - c) + Zu) * E (a - c) * ((At * P (c - b) + Zt) * E (c - b))
      ≤ constII k / v * ((At * P (a - b) + Zt) * E (a - b))
  have hAu0 : 0 ≤ Au := inv_nonneg.mpr (by positivity)
  have hAt0 : 0 ≤ At := inv_nonneg.mpr (by positivity)
  have hZu0 : 0 ≤ Zu := inv_nonneg.mpr (by positivity)
  have hZt0 : 0 ≤ Zt := inv_nonneg.mpr (by positivity)
  have hP0 : ∀ x, 0 ≤ P x := fun x => powW_nonneg _ _
  have hE0 : ∀ x, 0 ≤ E x := fun x => (exp_pos _).le
  have hE1 : ∀ x, E x ≤ 1 := fun x => exp_le_one_iff.mpr (neg_nonpos.mpr (sqrt_nonneg _))
  -- pointwise expansion
  have hpt : ∀ c : Zd (k + 2) L,
      (Au * P (a - c) + Zu) * E (a - c) * ((At * P (c - b) + Zt) * E (c - b))
        ≤ Au * At * (P (a - c) * E (a - c) * (P (c - b) * E (c - b)))
          + Au * Zt * (P (a - c) * E (a - c)) + Zu * At * (P (c - b) * E (c - b))
          + Zu * Zt * 1 := by
    intro c
    have e1 := hE0 (a - c); have e2 := hE0 (c - b)
    have f1 := hE1 (a - c); have f2 := hE1 (c - b)
    have p1 := hP0 (a - c); have p2 := hP0 (c - b)
    have i1 : P (a - c) * E (a - c) * E (c - b) ≤ P (a - c) * E (a - c) :=
      mul_le_of_le_one_right (mul_nonneg p1 e1) f2
    have i2 : E (a - c) * (P (c - b) * E (c - b)) ≤ P (c - b) * E (c - b) :=
      mul_le_of_le_one_left (mul_nonneg p2 e2) f1
    have i3 : E (a - c) * E (c - b) ≤ 1 := by
      calc E (a - c) * E (c - b) ≤ 1 * E (c - b) := mul_le_mul_of_nonneg_right f1 e2
        _ ≤ 1 := by linarith
    calc (Au * P (a - c) + Zu) * E (a - c) * ((At * P (c - b) + Zt) * E (c - b))
        = Au * At * (P (a - c) * E (a - c) * (P (c - b) * E (c - b)))
          + Au * Zt * (P (a - c) * E (a - c) * E (c - b))
          + Zu * At * (E (a - c) * (P (c - b) * E (c - b)))
          + Zu * Zt * (E (a - c) * E (c - b)) := by ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left i1 (mul_nonneg hAu0 hZt0)
          have := mul_le_mul_of_nonneg_left i2 (mul_nonneg hZu0 hAt0)
          have := mul_le_mul_of_nonneg_left i3 (mul_nonneg hZu0 hZt0)
          linarith
  -- the four sums
  set K := 2 ^ (k + 2) * radC 1 with hK
  have hK0 : 0 ≤ K := by have := radC_pos one_pos; positivity
  have hS1 : ∑ c, P (a - c) * E (a - c) * (P (c - b) * E (c - b))
      ≤ convC k * (L : ℝ) ^ 2 * (P (a - b) * E (a - b)) :=
    sum_conv_le k hL1 le_rfl a b
  have hrad : ∑ x : Zd (k + 2) L, P x * E x ≤ K * (L : ℝ) ^ 2 := by
    have := sum_radial_exp_le (L := L) k one_pos hL1
    simp only [one_mul] at this
    exact this
  have hS2 : ∑ c, P (a - c) * E (a - c) ≤ K * (L : ℝ) ^ 2 := by
    rw [show ∑ c, P (a - c) * E (a - c) = ∑ x, P x * E x from
      Fintype.sum_equiv (Equiv.subLeft a) _ _ fun c => rfl]
    exact hrad
  have hS3 : ∑ c, P (c - b) * E (c - b) ≤ K * (L : ℝ) ^ 2 := by
    rw [show ∑ c, P (c - b) * E (c - b) = ∑ x, P x * E x from
      Fintype.sum_equiv (Equiv.subRight b) _ _ fun c => rfl]
    exact hrad
  have hS4 : ∑ _c : Zd (k + 2) L, (1 : ℝ) = (L : ℝ) ^ (k + 2) := sum_one_torus _ _
  -- the scalar inequalities of regime (ii)
  have hLv : (L : ℝ) ^ 2 * v ≤ g ^ 2 := by
    rw [le_div_iff₀ (by positivity)] at h; linarith
  have hAuL : Au * (L : ℝ) ^ 2 ≤ v⁻¹ := by
    rw [hAu, inv_mul_eq_div, div_le_iff₀ (by positivity), inv_mul_eq_div,
      le_div_iff₀ hv]
    nlinarith
  have hAtL : At * (L : ℝ) ^ 2 ≤ v⁻¹ := by
    rw [hAt, inv_mul_eq_div, div_le_iff₀ (by positivity), inv_mul_eq_div,
      le_div_iff₀ hv]
    nlinarith
  have hZuL : Zu * (L : ℝ) ^ (k + 2) = v⁻¹ := by
    rw [hZu, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hZuZt : Zu ≤ Zt := by
    rw [hZu, hZt]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hwv (by positivity))
  -- lower bound on `E(a-b)`
  set ε := exp (-√((k : ℝ) + 2)) with hε
  have hε0 : 0 < ε := exp_pos _
  have hEr : ε ≤ E (a - b) := by
    have h := exp_neg_sqrt_ge (L := L) (k + 2) hL1 (zdistD_le (k + 2) (a - b))
    push_cast at h
    exact h
  have hZtY : Zt ≤ exp (√((k : ℝ) + 2)) * (Zt * E (a - b)) := by
    have h1 : exp (√((k : ℝ) + 2)) * ε = 1 := by rw [hε, ← exp_add]; simp
    calc Zt = exp (√((k : ℝ) + 2)) * ε * Zt := by rw [h1, one_mul]
      _ ≤ exp (√((k : ℝ) + 2)) * (Zt * E (a - b)) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hEr hZt0
  -- assemble
  set X := At * P (a - b) * E (a - b) with hX
  set Y := Zt * E (a - b) with hY
  have hX0 : 0 ≤ X := mul_nonneg (mul_nonneg hAt0 (hP0 _)) (hE0 _)
  have hY0 : 0 ≤ Y := mul_nonneg hZt0 (hE0 _)
  have hvi : 0 ≤ v⁻¹ := inv_nonneg.mpr hv.le
  have T1 : Au * At * (convC k * (L : ℝ) ^ 2 * (P (a - b) * E (a - b)))
      ≤ v⁻¹ * (convC k * X) := by
    have hc : 0 ≤ convC k := by unfold convC; have := radC_pos κ₀_pos; positivity
    calc Au * At * (convC k * (L : ℝ) ^ 2 * (P (a - b) * E (a - b)))
        = (Au * (L : ℝ) ^ 2) * (convC k * X) := by rw [hX]; ring
      _ ≤ v⁻¹ * (convC k * X) := mul_le_mul_of_nonneg_right hAuL (mul_nonneg hc hX0)
  have T2 : Au * Zt * (K * (L : ℝ) ^ 2) ≤ v⁻¹ * (K * Zt) := by
    calc Au * Zt * (K * (L : ℝ) ^ 2) = (Au * (L : ℝ) ^ 2) * (K * Zt) := by ring
      _ ≤ v⁻¹ * (K * Zt) := mul_le_mul_of_nonneg_right hAuL (mul_nonneg hK0 hZt0)
  have T3 : Zu * At * (K * (L : ℝ) ^ 2) ≤ v⁻¹ * (K * Zt) := by
    calc Zu * At * (K * (L : ℝ) ^ 2) = (At * (L : ℝ) ^ 2) * (K * Zu) := by ring
      _ ≤ v⁻¹ * (K * Zu) := mul_le_mul_of_nonneg_right hAtL (mul_nonneg hK0 hZu0)
      _ ≤ v⁻¹ * (K * Zt) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hZuZt hK0) hvi
  have T4 : Zu * Zt * (L : ℝ) ^ (k + 2) = v⁻¹ * Zt := by
    rw [mul_comm Zu Zt, mul_assoc, hZuL, mul_comm]
  calc ∑ c, (Au * P (a - c) + Zu) * E (a - c) * ((At * P (c - b) + Zt) * E (c - b))
      ≤ ∑ c, (Au * At * (P (a - c) * E (a - c) * (P (c - b) * E (c - b)))
          + Au * Zt * (P (a - c) * E (a - c)) + Zu * At * (P (c - b) * E (c - b))
          + Zu * Zt * 1) := sum_le_sum fun c _ => hpt c
    _ = Au * At * ∑ c, P (a - c) * E (a - c) * (P (c - b) * E (c - b))
          + Au * Zt * ∑ c, P (a - c) * E (a - c) + Zu * At * ∑ c, P (c - b) * E (c - b)
          + Zu * Zt * ∑ _c : Zd (k + 2) L, (1 : ℝ) := by
        simp only [sum_add_distrib, mul_sum]
    _ ≤ Au * At * (convC k * (L : ℝ) ^ 2 * (P (a - b) * E (a - b)))
          + Au * Zt * (K * (L : ℝ) ^ 2) + Zu * At * (K * (L : ℝ) ^ 2)
          + Zu * Zt * (L : ℝ) ^ (k + 2) := by
        rw [hS4]
        have := mul_le_mul_of_nonneg_left hS1 (mul_nonneg hAu0 hAt0)
        have := mul_le_mul_of_nonneg_left hS2 (mul_nonneg hAu0 hZt0)
        have := mul_le_mul_of_nonneg_left hS3 (mul_nonneg hZu0 hAt0)
        linarith
    _ ≤ v⁻¹ * (convC k * X + (2 * K + 1) * Zt) := by
        rw [T4]; linarith [T1, T2, T3]
    _ ≤ v⁻¹ * (constII k * (X + Y)) := by
        apply mul_le_mul_of_nonneg_left _ hvi
        have hc1 : convC k ≤ constII k := by
          unfold constII
          have : 0 ≤ (2 * (2 ^ (k + 2) * radC 1) + 1) * exp (√((k : ℝ) + 2)) :=
            mul_nonneg (by rw [← hK]; linarith) (exp_pos _).le
          linarith
        have hc2 : (2 * K + 1) * exp (√((k : ℝ) + 2)) ≤ constII k := by
          unfold constII; have : 0 ≤ convC k := by
            unfold convC; have := radC_pos κ₀_pos; positivity
          rw [hK]; linarith
        have hZtY' : (2 * K + 1) * Zt ≤ (2 * K + 1) * exp (√((k : ℝ) + 2)) * Y := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hZtY (by linarith)
        have := mul_le_mul_of_nonneg_right hc1 hX0
        have := mul_le_mul_of_nonneg_right hc2 hY0
        linarith
    _ = constII k / v * ((At * P (a - b) + Zt) * E (a - b)) := by
        rw [hX, hY, div_eq_mul_inv]; ring

/-! ### Regime (i): `1 - u ≥ 1 - t ≥ g²/L²` -/

/-- The zero-mode constant `c_d = 2 (2d)^{d-2}` of `zeroMode_le_of_ge_mul` with `m = d`. -/
noncomputable def zmC (k : ℕ) : ℝ := 2 * (2 * ((k + 2 : ℕ) : ℝ)) ^ k

theorem zmC_nonneg (k : ℕ) : 0 ≤ zmC k := by unfold zmC; positivity

/-- The constant of regime (i). -/
noncomputable def constI (k : ℕ) : ℝ := (1 + zmC k) ^ 2 * convC k

/-- In regime (i), `𝒯_s(n) ≤ (1 + c_d) A_s P(n) E_{ℓ_s}(n)` for every lattice distance `n`. -/
theorem tailT_le_decay [NeZero L] {s : ℝ} (hs : s < 1) (h : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - s)
    (x : Zd (k + 2) L) :
    tailT (k + 2) L g s (zdistD (k + 2) L x)
      ≤ (1 + zmC k) * ((g ^ 2 + |1 - s|)⁻¹
          * (powW k (zdistD (k + 2) L x)
            * exp (-√((zdistD (k + 2) L x : ℝ) / ellT L g s)))) := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := NeZero.ne L
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  rw [tailT_natCast]
  have hZ := zeroMode_le_of_ge_mul (k := k) (m := k + 2) (by omega) hL1 hs
    (zdistD_le (k + 2) x) h
  have hE := (exp_pos (-√((zdistD (k + 2) L x : ℝ) / ellT L g s))).le
  have hA : 0 ≤ (g ^ 2 + |1 - s|)⁻¹ * powW k (zdistD (k + 2) L x) :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) (powW_nonneg _ _)
  unfold zmC
  calc ((g ^ 2 + |1 - s|)⁻¹ * powW k (zdistD (k + 2) L x) + ((L : ℝ) ^ (k + 2) * |1 - s|)⁻¹)
        * exp (-√((zdistD (k + 2) L x : ℝ) / ellT L g s))
      ≤ ((g ^ 2 + |1 - s|)⁻¹ * powW k (zdistD (k + 2) L x)
          + 2 * (2 * ((k + 2 : ℕ) : ℝ)) ^ k
            * ((g ^ 2 + |1 - s|)⁻¹ * powW k (zdistD (k + 2) L x)))
        * exp (-√((zdistD (k + 2) L x : ℝ) / ellT L g s)) :=
        mul_le_mul_of_nonneg_right (by linarith) hE
    _ = _ := by ring

/-- **`lem:propT`, regime (i).** -/
theorem propT_i [NeZero L] (hg : 0 < g) (hut : u ≤ t) (ht : t < 1)
    (h : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (a b : Zd (k + 2) L) :
    ∑ c : Zd (k + 2) L, tailT (k + 2) L g u (zdistD (k + 2) L (a - c))
        * tailT (k + 2) L g t (zdistD (k + 2) L (c - b))
      ≤ constI k / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b)) := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := NeZero.ne L
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hu1 : u < 1 := hut.trans_lt ht
  have hv : 0 < 1 - u := by linarith
  have hhu : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u := by linarith
  have hℓ : ellT L g u ≤ ellT L g t := ellT_mono hg.le hut ht
  have hℓu : 1 ≤ ellT L g u := one_le_ellT hL1
  set Au := (g ^ 2 + |1 - u|)⁻¹ with hAu
  set At := (g ^ 2 + |1 - t|)⁻¹ with hAt
  have hAu0 : 0 ≤ Au := inv_nonneg.mpr (by positivity)
  have hAt0 : 0 ≤ At := inv_nonneg.mpr (by positivity)
  set c1 := 1 + zmC k with hc1
  have hc10 : 0 ≤ c1 := by have := zmC_nonneg k; linarith
  set Pu : Zd (k + 2) L → ℝ := fun x =>
    powW k (zdistD (k + 2) L x) * exp (-√((zdistD (k + 2) L x : ℝ) / ellT L g u)) with hPu
  set Pt : Zd (k + 2) L → ℝ := fun x =>
    powW k (zdistD (k + 2) L x) * exp (-√((zdistD (k + 2) L x : ℝ) / ellT L g t)) with hPt
  have hPu0 : ∀ x, 0 ≤ Pu x := fun x => mul_nonneg (powW_nonneg _ _) (exp_pos _).le
  have hPt0 : ∀ x, 0 ≤ Pt x := fun x => mul_nonneg (powW_nonneg _ _) (exp_pos _).le
  -- the pointwise upper bound
  have hpt : ∀ c : Zd (k + 2) L,
      tailT (k + 2) L g u (zdistD (k + 2) L (a - c))
          * tailT (k + 2) L g t (zdistD (k + 2) L (c - b))
        ≤ c1 ^ 2 * (Au * At) * (Pu (a - c) * Pt (c - b)) := by
    intro c
    have h1 := tailT_le_decay (k := k) (L := L) hu1 hhu (a - c)
    have h2 := tailT_le_decay (k := k) (L := L) ht h (c - b)
    have h20 := tailT_nonneg (d := k + 2) (L := L) (g := g) (t := t)
      (Nat.cast_nonneg (zdistD (k + 2) L (c - b)))
    calc tailT (k + 2) L g u (zdistD (k + 2) L (a - c))
          * tailT (k + 2) L g t (zdistD (k + 2) L (c - b))
        ≤ (c1 * (Au * Pu (a - c))) * (c1 * (At * Pt (c - b))) :=
          mul_le_mul h1 h2 h20 (mul_nonneg hc10 (mul_nonneg hAu0 (hPu0 _)))
      _ = c1 ^ 2 * (Au * At) * (Pu (a - c) * Pt (c - b)) := by ring
  -- the lower bound on the right-hand side
  have hlow : At * Pt (a - b) ≤ tailT (k + 2) L g t (zdistD (k + 2) L (a - b)) := by
    rw [tailT_natCast]
    have hE := (exp_pos (-√((zdistD (k + 2) L (a - b) : ℝ) / ellT L g t))).le
    have hZ : 0 ≤ ((L : ℝ) ^ (k + 2) * |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
    have : At * Pt (a - b)
        = (At * powW k (zdistD (k + 2) L (a - b)))
          * exp (-√((zdistD (k + 2) L (a - b) : ℝ) / ellT L g t)) := by
      rw [hPt]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hE
  -- K3 with `ℓ₁ = ℓ_u ≤ ℓ₂ = ℓ_t`
  have hconv : ∑ c, Pu (a - c) * Pt (c - b) ≤ convC k * ellT L g u ^ 2 * Pt (a - b) :=
    sum_conv_le k hℓu hℓ a b
  have hAℓ : Au * ellT L g u ^ 2 ≤ (1 - u)⁻¹ := inv_mul_ellT_sq_le hg.le hv
  have hcC : 0 ≤ convC k := by unfold convC; have := radC_pos κ₀_pos; positivity
  calc ∑ c, tailT (k + 2) L g u (zdistD (k + 2) L (a - c))
          * tailT (k + 2) L g t (zdistD (k + 2) L (c - b))
      ≤ ∑ c, c1 ^ 2 * (Au * At) * (Pu (a - c) * Pt (c - b)) := sum_le_sum fun c _ => hpt c
    _ = c1 ^ 2 * (Au * At) * ∑ c, Pu (a - c) * Pt (c - b) := by rw [mul_sum]
    _ ≤ c1 ^ 2 * (Au * At) * (convC k * ellT L g u ^ 2 * Pt (a - b)) :=
        mul_le_mul_of_nonneg_left hconv (by positivity)
    _ = (c1 ^ 2 * convC k) * (Au * ellT L g u ^ 2) * (At * Pt (a - b)) := by ring
    _ ≤ (c1 ^ 2 * convC k) * (1 - u)⁻¹ * tailT (k + 2) L g t (zdistD (k + 2) L (a - b)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hAℓ (by positivity)) hlow
          (mul_nonneg hAt0 (hPt0 _))
        exact mul_nonneg (by positivity) (inv_nonneg.mpr hv.le)
    _ = constI k / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b)) := by
        rw [constI, hc1, div_eq_mul_inv]

/-! ### `lem:propT` -/

/-- **`lem:propT`, `(TTT2)`.**  There is a constant `C_d > 0` depending only on
`d = k + 2` such that for `0 < g`, `0 ≤ u ≤ t < 1` with (i) `1 - u ≥ 1 - t ≥ g²/L²` or
(ii) `1 - t ≤ 1 - u ≤ g²/L²`,
`Σ_c 𝒯_u(|a-c|) 𝒯_t(|c-b|) ≤ C_d/(1-u) · 𝒯_t(|a-b|)` for all `a, b ∈ Z_L^d`. -/
theorem propT (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ (L : ℕ) [NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 →
      (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) →
      ∀ a b : Zd (k + 2) L,
        ∑ c : Zd (k + 2) L, tailT (k + 2) L g u (zdistD (k + 2) L (a - c))
            * tailT (k + 2) L g t (zdistD (k + 2) L (c - b))
          ≤ C / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b)) := by
  have hcC : 0 < convC k := by unfold convC; have := radC_pos κ₀_pos; positivity
  have hI : 0 ≤ constI k := by unfold constI; have := zmC_nonneg k; positivity
  have hII : 0 ≤ constII k := by
    unfold constII; have := radC_pos (one_pos : (0 : ℝ) < 1); positivity
  refine ⟨constI k + constII k, by
    have : convC k ≤ constII k := by
      unfold constII
      have := radC_pos (one_pos : (0 : ℝ) < 1)
      have : 0 ≤ (2 * (2 ^ (k + 2) * radC 1) + 1) * exp (√((k : ℝ) + 2)) := by positivity
      linarith
    linarith, ?_⟩
  intro L _ g u t hg hu hut ht hreg a b
  have hv : 0 < 1 - u := by linarith
  have hT0 := tailT_nonneg (d := k + 2) (L := L) (g := g) (t := t)
    (Nat.cast_nonneg (zdistD (k + 2) L (a - b)))
  rcases hreg with h | h
  · calc _ ≤ constI k / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b)) :=
          propT_i hg hut ht h a b
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hT0
          exact div_le_div_of_nonneg_right (by linarith) hv.le
  · calc _ ≤ constII k / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b)) :=
          propT_ii hg hut ht h a b
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hT0
          exact div_le_div_of_nonneg_right (by linarith) hv.le

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

/-- The truncated triangle inequality: `s ≤ p + q` gives `s ∧ ℓ ≤ (p ∧ ℓ) + (q ∧ ℓ)`. -/
theorem min_le_add_min {p q s ℓ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hℓ : 0 ≤ ℓ)
    (hspq : s ≤ p + q) : min s ℓ ≤ min p ℓ + min q ℓ := by
  rcases le_total ℓ p with h | h
  · calc min s ℓ ≤ ℓ := min_le_right _ _
      _ = min p ℓ + 0 := by rw [min_eq_right h, add_zero]
      _ ≤ min p ℓ + min q ℓ := by
          have : 0 ≤ min q ℓ := le_min hq hℓ
          linarith
  rcases le_total ℓ q with h' | h'
  · calc min s ℓ ≤ ℓ := min_le_right _ _
      _ = 0 + min q ℓ := by rw [min_eq_right h', zero_add]
      _ ≤ min p ℓ + min q ℓ := by
          have : 0 ≤ min p ℓ := le_min hp hℓ
          linarith
  · rw [min_eq_left h, min_eq_left h']
    exact (min_le_left _ _).trans hspq

variable {d L : ℕ} [NeZero L]

/-- **`(eq:TtTt)` on the lattice**, under its standing hypothesis
`|x-α| ∨ |y-α| ≤ ℓ`. -/
theorem sfT_TtTt (hW : 0 < W) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x y α : Zd d L)
    (hx : ((zdistD d L (x - α) : ℕ) : ℝ) ≤ ℓ) (hy : ((zdistD d L (y - α) : ℕ) : ℝ) ≤ ℓ) :
    sfT d L W g t (min ((zdistD d L (x - α) : ℕ) : ℝ) ℓ)
        * sfT d L W g t (min ((zdistD d L (y - α) : ℕ) : ℝ) ℓ)
      ≤ √((2 : ℝ) ^ (d - 2))
        * (sfT d L W g t (min ((zdistD d L (x - y) : ℕ) : ℝ) ℓ)
          * (PsiT d L W g t
            * √(((min ((zdistD d L (x - α) : ℕ) : ℝ) ((zdistD d L (y - α) : ℕ) : ℝ) + 1)
                  ^ (d - 2))⁻¹))) := by
  set p := ((zdistD d L (x - α) : ℕ) : ℝ) with hpdef
  set q := ((zdistD d L (y - α) : ℕ) : ℝ) with hqdef
  set r := ((zdistD d L (x - y) : ℕ) : ℝ) with hrdef
  have hp0 : 0 ≤ p := Nat.cast_nonneg _
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have htri : r ≤ p + q := by
    have h := zdistD_add_le d L (x - α) (α - y)
    rw [sub_add_sub_cancel] at h
    have hneg : zdistD d L (α - y) = zdistD d L (y - α) := by
      rw [← zdistD_neg d L (y - α), neg_sub]
    rw [hneg] at h
    simp only [hpdef, hqdef, hrdef]
    exact_mod_cast h
  rw [min_eq_left hx, min_eq_left hy]
  exact sfT_mul_le_TtTt hW hp0 hq0 (le_min (Nat.cast_nonneg _) hℓ)
    ((min_le_left _ _).trans htri)

omit [NeZero L] in
/-- **`(eq:KtKt)` on the lattice**: when `|y-α| ≥ ℓ`, so that `|y-α| ∧ ℓ = ℓ`. -/
theorem sfT_KtKt (hW : 0 < W) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x y α : Zd d L)
    (hy : ℓ ≤ ((zdistD d L (y - α) : ℕ) : ℝ)) :
    sfT d L W g t (min ((zdistD d L (x - α) : ℕ) : ℝ) ℓ)
        * sfT d L W g t (min ((zdistD d L (y - α) : ℕ) : ℝ) ℓ)
      ≤ sfT d L W g t ℓ
        * (PsiT d L W g t
          * √(((min ((zdistD d L (x - α) : ℕ) : ℝ) ℓ + 1) ^ (d - 2))⁻¹)) := by
  rw [min_eq_right hy]
  exact sfT_mul_le_KtKt hW (le_min (Nat.cast_nonneg _) hℓ)

/-- **The case coverage of Appendix A.4.**  For every pair `(x, y)` and every internal
vertex `α`, one of the two bounds applies: `(eq:TtTt)` when both distances are `≤ ℓ`, and
`(eq:KtKt)` otherwise -- after exchanging `x` and `y` if necessary.

This is what makes the index ranges of the third proofreading round -- `(eq:KtKt)` for
`2 ≤ i ≤ k` in case 2 and for `1 ≤ i ≤ k` in case 3, rather than `3 ≤ i ≤ k` -- exactly
right: outside the indices covered by `(eq:TtTt)`, some distance exceeds `ℓ`, which is
precisely the hypothesis of `(eq:KtKt)`. -/
theorem sfT_pair_cases (hW : 0 < W) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x y α : Zd d L) :
    sfT d L W g t (min ((zdistD d L (x - α) : ℕ) : ℝ) ℓ)
        * sfT d L W g t (min ((zdistD d L (y - α) : ℕ) : ℝ) ℓ)
      ≤ √((2 : ℝ) ^ (d - 2))
        * (sfT d L W g t (min ((zdistD d L (x - y) : ℕ) : ℝ) ℓ)
          * (PsiT d L W g t
            * √(((min ((zdistD d L (x - α) : ℕ) : ℝ) ((zdistD d L (y - α) : ℕ) : ℝ) + 1)
                  ^ (d - 2))⁻¹)))
    ∨ sfT d L W g t (min ((zdistD d L (x - α) : ℕ) : ℝ) ℓ)
        * sfT d L W g t (min ((zdistD d L (y - α) : ℕ) : ℝ) ℓ)
      ≤ sfT d L W g t ℓ
        * (PsiT d L W g t
          * √(((min ((zdistD d L (x - α) : ℕ) : ℝ) ℓ + 1) ^ (d - 2))⁻¹))
    ∨ sfT d L W g t (min ((zdistD d L (x - α) : ℕ) : ℝ) ℓ)
        * sfT d L W g t (min ((zdistD d L (y - α) : ℕ) : ℝ) ℓ)
      ≤ sfT d L W g t ℓ
        * (PsiT d L W g t
          * √(((min ((zdistD d L (y - α) : ℕ) : ℝ) ℓ + 1) ^ (d - 2))⁻¹)) := by
  rcases le_total ((zdistD d L (y - α) : ℕ) : ℝ) ℓ with hy | hy
  · rcases le_total ((zdistD d L (x - α) : ℕ) : ℝ) ℓ with hx | hx
    · exact Or.inl (sfT_TtTt hW hℓ x y α hx hy)
    · refine Or.inr (Or.inr ?_)
      rw [mul_comm]
      exact sfT_KtKt hW hℓ y x α hx
  · exact Or.inr (Or.inl (sfT_KtKt hW hℓ x y α hy))

end TTk

end RBM
