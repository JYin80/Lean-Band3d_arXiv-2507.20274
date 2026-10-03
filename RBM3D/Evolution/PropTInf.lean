/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.Pins
import RBM3D.Defs.Sizes

/-!
# `lem:propT`, `(TTT2)`, for the `L^∞` distance `zdistInf`

The paper's `|x|` is the periodic `L^∞` norm (`Gauss.zdistInf`, `Defs/Sizes.lean`); the merged
`EKPropT` / `ekPropT_holds` (`Evolution/Pins.lean`, `Kernel/PropT.lean`) is the same statement for
the `ℓ¹` distance `zdistD`.  `EKPropTInf d` is `EKPropT d` with `Gauss.zdistInf d L` in place of
`zdistD d L` in all three places, `ekPropTInf_holds` proves it.

The comparison route (`zdistInf ≤ zdistD ≤ d · zdistInf` plus a doubling inequality
`𝒯_t(d r) ≥ c_d 𝒯_t(r)`) is **not** available: the doubling constant must depend on `L`
(`T2075-prove.md` (a), part 3).  The proof is the direct one, the proof of `Kernel/PropT.lean`
with `ρ = zdistInf`:

* the triangle inequality for `zdistInf` (coordinatewise `zdist_add_le`);
* the range `ρ ≤ L` (so `m = 1` in `zeroMode_le_of_ge_mul`, `d = 1` in `exp_neg_sqrt_ge`);
* the radial sum K2 for `ρ = zdistInf`, from `zdistInf ≤ zdistD ≤ d · zdistInf` and
  `sum_radial_exp_le` at the scale `d ℓ` (`pti_sum_radial`);
* the pointwise bound and K3 (`pti_conv_term_le`, `pti_sum_conv_le`) with `ρ = zdistInf`.

Merged declarations used unchanged: `tailT_natCast`, `ellT_mono`, `inv_mul_ellT_sq_le`,
`exp_neg_sqrt_ge`, `zeroMode_le_of_ge_mul`, `sum_one_torus`, `sqrt_add_sqrt_sub_ge`,
`powW_le_of_le_two_mul`, `sum_radial_exp_le`.  The proofs of `Kernel/PropT.lean`
(`propT_i`, `propT_ii`), `Defs/Convolution.lean` (`conv_term_le`, `sum_conv_le`) are re-done here
(not copied by import) because they mention `zdistD`.
-/

namespace RBM

open Finset Real

variable {L : ℕ}

/-! ### The `L^∞` distance: triangle inequality and range -/

private theorem pti_zdistInf_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    Gauss.zdistInf d L (x + y) ≤ Gauss.zdistInf d L x + Gauss.zdistInf d L y := by
  unfold Gauss.zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

private theorem pti_zdistInf_le_L (d : ℕ) (x : Zd d L) : Gauss.zdistInf d L x ≤ L :=
  Finset.sup_le fun i _ => zdist_le_L (x i)

/-! ### The radial sum K2 for `zdistInf` -/

/-- the termwise comparison `ρ₁ ≤ d ρ`: `P(ρ) e^{-κ√(ρ/ℓ)} ≤ d^k P(ρ₁) e^{-κ√(ρ₁/(dℓ))}`. -/
private theorem pti_term_le (k d : ℕ) (hd : 1 ≤ d) {κ ℓ : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ)
    {ρ ρ₁ : ℕ} (h : ρ₁ ≤ d * ρ) :
    (((ρ : ℝ) + 1) ^ k)⁻¹ * exp (-(κ * √((ρ : ℝ) / ℓ)))
      ≤ (d : ℝ) ^ k * ((((ρ₁ : ℝ) + 1) ^ k)⁻¹ * exp (-(κ * √((ρ₁ : ℝ) / (d * ℓ))))) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hh : (ρ₁ : ℝ) ≤ d * ρ := by exact_mod_cast h
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
  have h1 : (ρ₁ : ℝ) + 1 ≤ d * ((ρ : ℝ) + 1) := by nlinarith
  have h2 : (((ρ₁ : ℝ) + 1) ^ k) ≤ (d : ℝ) ^ k * (((ρ : ℝ) + 1) ^ k) := by
    calc (((ρ₁ : ℝ) + 1) ^ k) ≤ ((d : ℝ) * ((ρ : ℝ) + 1)) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
      _ = _ := mul_pow _ _ _
  have ha : 0 < (((ρ : ℝ) + 1) ^ k) := by positivity
  have hb : 0 < (((ρ₁ : ℝ) + 1) ^ k) := by positivity
  have h3 : (((ρ : ℝ) + 1) ^ k)⁻¹ ≤ (d : ℝ) ^ k * (((ρ₁ : ℝ) + 1) ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ ha hb]
    linarith
  have h4 : (ρ₁ : ℝ) / (d * ℓ) ≤ (ρ : ℝ) / ℓ := by
    rw [div_le_div_iff₀ (by positivity) hℓ]
    nlinarith [mul_le_mul_of_nonneg_right hh hℓ.le]
  have hexp : exp (-(κ * √((ρ : ℝ) / ℓ))) ≤ exp (-(κ * √((ρ₁ : ℝ) / (d * ℓ)))) :=
    exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (sqrt_le_sqrt h4) hκ))
  calc (((ρ : ℝ) + 1) ^ k)⁻¹ * exp (-(κ * √((ρ : ℝ) / ℓ)))
      ≤ ((d : ℝ) ^ k * (((ρ₁ : ℝ) + 1) ^ k)⁻¹) * exp (-(κ * √((ρ₁ : ℝ) / (d * ℓ)))) :=
        mul_le_mul h3 hexp (exp_pos _).le (by positivity)
    _ = _ := by ring

/-- **K2 for `zdistInf`**: `Σ_x (|x|_∞+1)^{-k} e^{-κ√(|x|_∞/ℓ)} ≤ d^d 2^d C(κ) ℓ²`, `d = k+2`. -/
private theorem pti_sum_radial [NeZero L] (k : ℕ) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 1 ≤ ℓ) :
    ∑ x : Zd (k + 2) L, (((Gauss.zdistInf (k + 2) L x : ℝ) + 1) ^ k)⁻¹
        * exp (-(κ * √((Gauss.zdistInf (k + 2) L x : ℝ) / ℓ)))
      ≤ ((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC κ) * ℓ ^ 2 := by
  have hd1 : 1 ≤ k + 2 := by omega
  have hD1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast hd1
  have hdℓ : 1 ≤ ((k + 2 : ℕ) : ℝ) * ℓ := by nlinarith
  have hK2 := sum_radial_exp_le (L := L) k hκ hdℓ
  calc ∑ x : Zd (k + 2) L, (((Gauss.zdistInf (k + 2) L x : ℝ) + 1) ^ k)⁻¹
        * exp (-(κ * √((Gauss.zdistInf (k + 2) L x : ℝ) / ℓ)))
      ≤ ∑ x : Zd (k + 2) L, ((k + 2 : ℕ) : ℝ) ^ k *
          ((((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
            * exp (-(κ * √((zdistD (k + 2) L x : ℝ) / (((k + 2 : ℕ) : ℝ) * ℓ))))) :=
        sum_le_sum fun x _ =>
          pti_term_le k (k + 2) hd1 hκ.le (by linarith)
            (Gauss.zdistD_le_mul_zdistInf (k + 2) L x)
    _ = ((k + 2 : ℕ) : ℝ) ^ k *
          ∑ x : Zd (k + 2) L, (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
            * exp (-(κ * √((zdistD (k + 2) L x : ℝ) / (((k + 2 : ℕ) : ℝ) * ℓ)))) := by
        rw [← mul_sum]
    _ ≤ ((k + 2 : ℕ) : ℝ) ^ k * (2 ^ (k + 2) * radC κ * (((k + 2 : ℕ) : ℝ) * ℓ) ^ 2) :=
        mul_le_mul_of_nonneg_left hK2 (by positivity)
    _ = _ := by ring

/-! ### The pointwise bound and K3 for `zdistInf` -/

private theorem pti_conv_term_le [NeZero L] (d k : ℕ) {ℓ₁ ℓ₂ : ℝ} (hℓ₁ : 0 < ℓ₁)
    (hℓ : ℓ₁ ≤ ℓ₂) (a b c : Zd d L) :
    powW k (Gauss.zdistInf d L (a - c)) * exp (-√((Gauss.zdistInf d L (a - c) : ℝ) / ℓ₁))
        * (powW k (Gauss.zdistInf d L (c - b))
            * exp (-√((Gauss.zdistInf d L (c - b) : ℝ) / ℓ₂)))
      ≤ 2 ^ k * (powW k (Gauss.zdistInf d L (a - b))
            * exp (-√((Gauss.zdistInf d L (a - b) : ℝ) / ℓ₂)))
        * (powW k (Gauss.zdistInf d L (a - c))
              * exp (-(κ₀ * √((Gauss.zdistInf d L (a - c) : ℝ) / ℓ₁)))
          + powW k (Gauss.zdistInf d L (c - b))
              * exp (-(κ₀ * √((Gauss.zdistInf d L (c - b) : ℝ) / ℓ₁)))) := by
  set p := Gauss.zdistInf d L (a - c)
  set q := Gauss.zdistInf d L (c - b)
  set r := Gauss.zdistInf d L (a - b)
  have htri : r ≤ p + q := by
    have := pti_zdistInf_add_le d L (a - c) (c - b)
    rwa [sub_add_sub_cancel] at this
  have htri' : (r : ℝ) ≤ p + q := by exact_mod_cast htri
  have hexp := sqrt_add_sqrt_sub_ge (Nat.cast_nonneg p) (Nat.cast_nonneg q) htri' hℓ₁ hℓ
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
  · have hq2 : powW k q ≤ 2 ^ k * powW k r := powW_le_of_le_two_mul (by omega)
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
  · have hp2 : powW k p ≤ 2 ^ k * powW k r := powW_le_of_le_two_mul (by omega)
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

/-- The convolution constant for `zdistInf`: `2^{k+1} · d^d · 2^{k+2} · C(κ₀)`, `d = k+2`. -/
private noncomputable def ptiConvC (k : ℕ) : ℝ :=
  2 ^ (k + 1) * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC κ₀))

/-- **K3 for `zdistInf`.** For `1 ≤ ℓ₁ ≤ ℓ₂`:
`Σ_c P(a-c) E_{ℓ₁}(a-c) · P(c-b) E_{ℓ₂}(c-b) ≤ C ℓ₁² · P(a-b) E_{ℓ₂}(a-b)`. -/
private theorem pti_sum_conv_le [NeZero L] (k : ℕ) {ℓ₁ ℓ₂ : ℝ} (hℓ₁ : 1 ≤ ℓ₁) (hℓ : ℓ₁ ≤ ℓ₂)
    (a b : Zd (k + 2) L) :
    ∑ c : Zd (k + 2) L,
        powW k (Gauss.zdistInf (k + 2) L (a - c))
            * exp (-√((Gauss.zdistInf (k + 2) L (a - c) : ℝ) / ℓ₁))
          * (powW k (Gauss.zdistInf (k + 2) L (c - b))
              * exp (-√((Gauss.zdistInf (k + 2) L (c - b) : ℝ) / ℓ₂)))
      ≤ ptiConvC k * ℓ₁ ^ 2
          * (powW k (Gauss.zdistInf (k + 2) L (a - b))
            * exp (-√((Gauss.zdistInf (k + 2) L (a - b) : ℝ) / ℓ₂))) := by
  have hℓ₁0 : 0 < ℓ₁ := by linarith
  set F : Zd (k + 2) L → ℝ := fun x =>
    powW k (Gauss.zdistInf (k + 2) L x)
      * exp (-(κ₀ * √((Gauss.zdistInf (k + 2) L x : ℝ) / ℓ₁)))
  set R := powW k (Gauss.zdistInf (k + 2) L (a - b))
    * exp (-√((Gauss.zdistInf (k + 2) L (a - b) : ℝ) / ℓ₂))
  have hR : 0 ≤ R := mul_nonneg (powW_nonneg _ _) (exp_pos _).le
  have hK2 : ∑ x, F x ≤ ((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC κ₀) * ℓ₁ ^ 2 :=
    pti_sum_radial k κ₀_pos hℓ₁
  have hA : ∑ c : Zd (k + 2) L, F (a - c) = ∑ x, F x :=
    Fintype.sum_equiv (Equiv.subLeft a) _ _ fun c => rfl
  have hB : ∑ c : Zd (k + 2) L, F (c - b) = ∑ x, F x :=
    Fintype.sum_equiv (Equiv.subRight b) _ _ fun c => rfl
  calc _ ≤ ∑ c : Zd (k + 2) L, 2 ^ k * R * (F (a - c) + F (c - b)) :=
        sum_le_sum fun c _ => pti_conv_term_le (k + 2) k hℓ₁0 hℓ a b c
    _ = 2 ^ k * R * (∑ c : Zd (k + 2) L, F (a - c) + ∑ c : Zd (k + 2) L, F (c - b)) := by
        rw [← mul_sum, sum_add_distrib]
    _ = 2 ^ k * R * (2 * ∑ x, F x) := by rw [hA, hB]; ring
    _ ≤ 2 ^ k * R * (2 * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC κ₀) * ℓ₁ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = ptiConvC k * ℓ₁ ^ 2 * R := by unfold ptiConvC; ring

variable {k : ℕ} {g u t : ℝ}

/-! ### Regime (ii): `1 - t ≤ 1 - u ≤ g²/L²` -/

/-- The constant of regime (ii). -/
private noncomputable def ptiConstII (k : ℕ) : ℝ :=
  ptiConvC k + (2 * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1)) + 1) * exp 1

/-- **`lem:propT`, regime (ii).** -/
private theorem pti_ii [NeZero L] (hg : 0 < g) (hut : u ≤ t) (ht : t < 1)
    (h : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) (a b : Zd (k + 2) L) :
    ∑ c : Zd (k + 2) L, tailT (k + 2) L g u (Gauss.zdistInf (k + 2) L (a - c))
        * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (c - b))
      ≤ ptiConstII k / (1 - u) * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (a - b)) := by
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
  set P : Zd (k + 2) L → ℝ := fun x => powW k (Gauss.zdistInf (k + 2) L x) with hP
  set E : Zd (k + 2) L → ℝ := fun x => exp (-√((Gauss.zdistInf (k + 2) L x : ℝ) / L)) with hE
  change ∑ c, (Au * P (a - c) + Zu) * E (a - c) * ((At * P (c - b) + Zt) * E (c - b))
      ≤ ptiConstII k / v * ((At * P (a - b) + Zt) * E (a - b))
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
  set K := ((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1) with hK
  have hK0 : 0 ≤ K := by have := radC_pos (one_pos : (0 : ℝ) < 1); positivity
  have hS1 : ∑ c, P (a - c) * E (a - c) * (P (c - b) * E (c - b))
      ≤ ptiConvC k * (L : ℝ) ^ 2 * (P (a - b) * E (a - b)) :=
    pti_sum_conv_le k hL1 le_rfl a b
  have hrad : ∑ x : Zd (k + 2) L, P x * E x ≤ K * (L : ℝ) ^ 2 := by
    have := pti_sum_radial (L := L) k one_pos hL1
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
  set ε := exp (-1) with hε
  have hε0 : 0 < ε := exp_pos _
  have hEr : ε ≤ E (a - b) := by
    have h := exp_neg_sqrt_ge (L := L) 1 hL1
      (by simpa using pti_zdistInf_le_L (L := L) (k + 2) (a - b))
    simp only [Nat.cast_one, Real.sqrt_one] at h
    exact h
  have hZtY : Zt ≤ exp 1 * (Zt * E (a - b)) := by
    have h1 : exp 1 * ε = 1 := by rw [hε, ← exp_add]; simp
    calc Zt = exp 1 * ε * Zt := by rw [h1, one_mul]
      _ ≤ exp 1 * (Zt * E (a - b)) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hEr hZt0
  -- assemble
  set X := At * P (a - b) * E (a - b) with hX
  set Y := Zt * E (a - b) with hY
  have hX0 : 0 ≤ X := mul_nonneg (mul_nonneg hAt0 (hP0 _)) (hE0 _)
  have hY0 : 0 ≤ Y := mul_nonneg hZt0 (hE0 _)
  have hvi : 0 ≤ v⁻¹ := inv_nonneg.mpr hv.le
  have T1 : Au * At * (ptiConvC k * (L : ℝ) ^ 2 * (P (a - b) * E (a - b)))
      ≤ v⁻¹ * (ptiConvC k * X) := by
    have hc : 0 ≤ ptiConvC k := by unfold ptiConvC; have := radC_pos κ₀_pos; positivity
    calc Au * At * (ptiConvC k * (L : ℝ) ^ 2 * (P (a - b) * E (a - b)))
        = (Au * (L : ℝ) ^ 2) * (ptiConvC k * X) := by rw [hX]; ring
      _ ≤ v⁻¹ * (ptiConvC k * X) := mul_le_mul_of_nonneg_right hAuL (mul_nonneg hc hX0)
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
    _ ≤ Au * At * (ptiConvC k * (L : ℝ) ^ 2 * (P (a - b) * E (a - b)))
          + Au * Zt * (K * (L : ℝ) ^ 2) + Zu * At * (K * (L : ℝ) ^ 2)
          + Zu * Zt * (L : ℝ) ^ (k + 2) := by
        rw [hS4]
        have := mul_le_mul_of_nonneg_left hS1 (mul_nonneg hAu0 hAt0)
        have := mul_le_mul_of_nonneg_left hS2 (mul_nonneg hAu0 hZt0)
        have := mul_le_mul_of_nonneg_left hS3 (mul_nonneg hZu0 hAt0)
        linarith
    _ ≤ v⁻¹ * (ptiConvC k * X + (2 * K + 1) * Zt) := by
        rw [T4]; linarith [T1, T2, T3]
    _ ≤ v⁻¹ * (ptiConstII k * (X + Y)) := by
        apply mul_le_mul_of_nonneg_left _ hvi
        have hc1 : ptiConvC k ≤ ptiConstII k := by
          unfold ptiConstII
          have : 0 ≤ (2 * K + 1) * exp 1 :=
            mul_nonneg (by linarith) (exp_pos _).le
          linarith
        have hc2 : (2 * K + 1) * exp 1 ≤ ptiConstII k := by
          unfold ptiConstII; have : 0 ≤ ptiConvC k := by
            unfold ptiConvC; have := radC_pos κ₀_pos; positivity
          rw [hK]; linarith
        have hZtY' : (2 * K + 1) * Zt ≤ (2 * K + 1) * exp 1 * Y := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hZtY (by linarith)
        have := mul_le_mul_of_nonneg_right hc1 hX0
        have := mul_le_mul_of_nonneg_right hc2 hY0
        linarith
    _ = ptiConstII k / v * ((At * P (a - b) + Zt) * E (a - b)) := by
        rw [hX, hY, div_eq_mul_inv]; ring

/-! ### Regime (i): `1 - u ≥ 1 - t ≥ g²/L²` -/

/-- The zero-mode constant `2^{k+1}` of `zeroMode_le_of_ge_mul` with `m = 1` (`ρ ≤ L`). -/
private noncomputable def ptiZC (k : ℕ) : ℝ := 2 * 2 ^ k

private theorem ptiZC_nonneg (k : ℕ) : 0 ≤ ptiZC k := by unfold ptiZC; positivity

/-- The constant of regime (i). -/
private noncomputable def ptiConstI (k : ℕ) : ℝ := (1 + ptiZC k) ^ 2 * ptiConvC k

/-- In regime (i), `𝒯_s(n) ≤ (1 + c_d) A_s P(n) E_{ℓ_s}(n)` for every lattice distance `n`. -/
private theorem pti_tailT_le_decay [NeZero L] {s : ℝ} (hs : s < 1) (h : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - s)
    (x : Zd (k + 2) L) :
    tailT (k + 2) L g s (Gauss.zdistInf (k + 2) L x)
      ≤ (1 + ptiZC k) * ((g ^ 2 + |1 - s|)⁻¹
          * (powW k (Gauss.zdistInf (k + 2) L x)
            * exp (-√((Gauss.zdistInf (k + 2) L x : ℝ) / ellT L g s)))) := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := NeZero.ne L
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  rw [tailT_natCast]
  have hZ := zeroMode_le_of_ge_mul (k := k) (m := 1) le_rfl hL1 hs
    (by simpa using pti_zdistInf_le_L (L := L) (k + 2) x) h
  simp only [Nat.cast_one, mul_one] at hZ
  have hE := (exp_pos (-√((Gauss.zdistInf (k + 2) L x : ℝ) / ellT L g s))).le
  have hA : 0 ≤ (g ^ 2 + |1 - s|)⁻¹ * powW k (Gauss.zdistInf (k + 2) L x) :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) (powW_nonneg _ _)
  unfold ptiZC
  calc ((g ^ 2 + |1 - s|)⁻¹ * powW k (Gauss.zdistInf (k + 2) L x) + ((L : ℝ) ^ (k + 2) * |1 - s|)⁻¹)
        * exp (-√((Gauss.zdistInf (k + 2) L x : ℝ) / ellT L g s))
      ≤ ((g ^ 2 + |1 - s|)⁻¹ * powW k (Gauss.zdistInf (k + 2) L x)
          + 2 * 2 ^ k
            * ((g ^ 2 + |1 - s|)⁻¹ * powW k (Gauss.zdistInf (k + 2) L x)))
        * exp (-√((Gauss.zdistInf (k + 2) L x : ℝ) / ellT L g s)) :=
        mul_le_mul_of_nonneg_right (by linarith) hE
    _ = _ := by ring

/-- **`lem:propT`, regime (i).** -/
private theorem pti_i [NeZero L] (hg : 0 < g) (hut : u ≤ t) (ht : t < 1)
    (h : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (a b : Zd (k + 2) L) :
    ∑ c : Zd (k + 2) L, tailT (k + 2) L g u (Gauss.zdistInf (k + 2) L (a - c))
        * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (c - b))
      ≤ ptiConstI k / (1 - u) * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (a - b)) := by
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
  set c1 := 1 + ptiZC k with hc1
  have hc10 : 0 ≤ c1 := by have := ptiZC_nonneg k; linarith
  set Pu : Zd (k + 2) L → ℝ := fun x =>
    powW k (Gauss.zdistInf (k + 2) L x)
      * exp (-√((Gauss.zdistInf (k + 2) L x : ℝ) / ellT L g u)) with hPu
  set Pt : Zd (k + 2) L → ℝ := fun x =>
    powW k (Gauss.zdistInf (k + 2) L x)
      * exp (-√((Gauss.zdistInf (k + 2) L x : ℝ) / ellT L g t)) with hPt
  have hPu0 : ∀ x, 0 ≤ Pu x := fun x => mul_nonneg (powW_nonneg _ _) (exp_pos _).le
  have hPt0 : ∀ x, 0 ≤ Pt x := fun x => mul_nonneg (powW_nonneg _ _) (exp_pos _).le
  -- the pointwise upper bound
  have hpt : ∀ c : Zd (k + 2) L,
      tailT (k + 2) L g u (Gauss.zdistInf (k + 2) L (a - c))
          * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (c - b))
        ≤ c1 ^ 2 * (Au * At) * (Pu (a - c) * Pt (c - b)) := by
    intro c
    have h1 := pti_tailT_le_decay (k := k) (L := L) hu1 hhu (a - c)
    have h2 := pti_tailT_le_decay (k := k) (L := L) ht h (c - b)
    have h20 := tailT_nonneg (d := k + 2) (L := L) (g := g) (t := t)
      (Nat.cast_nonneg (Gauss.zdistInf (k + 2) L (c - b)))
    calc tailT (k + 2) L g u (Gauss.zdistInf (k + 2) L (a - c))
          * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (c - b))
        ≤ (c1 * (Au * Pu (a - c))) * (c1 * (At * Pt (c - b))) :=
          mul_le_mul h1 h2 h20 (mul_nonneg hc10 (mul_nonneg hAu0 (hPu0 _)))
      _ = c1 ^ 2 * (Au * At) * (Pu (a - c) * Pt (c - b)) := by ring
  -- the lower bound on the right-hand side
  have hlow : At * Pt (a - b) ≤ tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (a - b)) := by
    rw [tailT_natCast]
    have hE := (exp_pos (-√((Gauss.zdistInf (k + 2) L (a - b) : ℝ) / ellT L g t))).le
    have hZ : 0 ≤ ((L : ℝ) ^ (k + 2) * |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
    have : At * Pt (a - b)
        = (At * powW k (Gauss.zdistInf (k + 2) L (a - b)))
          * exp (-√((Gauss.zdistInf (k + 2) L (a - b) : ℝ) / ellT L g t)) := by
      rw [hPt]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hE
  -- K3 with `ℓ₁ = ℓ_u ≤ ℓ₂ = ℓ_t`
  have hconv : ∑ c, Pu (a - c) * Pt (c - b) ≤ ptiConvC k * ellT L g u ^ 2 * Pt (a - b) :=
    pti_sum_conv_le k hℓu hℓ a b
  have hAℓ : Au * ellT L g u ^ 2 ≤ (1 - u)⁻¹ := inv_mul_ellT_sq_le hg.le hv
  have hcC : 0 ≤ ptiConvC k := by unfold ptiConvC; have := radC_pos κ₀_pos; positivity
  calc ∑ c, tailT (k + 2) L g u (Gauss.zdistInf (k + 2) L (a - c))
          * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (c - b))
      ≤ ∑ c, c1 ^ 2 * (Au * At) * (Pu (a - c) * Pt (c - b)) := sum_le_sum fun c _ => hpt c
    _ = c1 ^ 2 * (Au * At) * ∑ c, Pu (a - c) * Pt (c - b) := by rw [mul_sum]
    _ ≤ c1 ^ 2 * (Au * At) * (ptiConvC k * ellT L g u ^ 2 * Pt (a - b)) :=
        mul_le_mul_of_nonneg_left hconv (by positivity)
    _ = (c1 ^ 2 * ptiConvC k) * (Au * ellT L g u ^ 2) * (At * Pt (a - b)) := by ring
    _ ≤ (c1 ^ 2 * ptiConvC k) * (1 - u)⁻¹
          * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (a - b)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hAℓ (by positivity)) hlow
          (mul_nonneg hAt0 (hPt0 _))
        exact mul_nonneg (by positivity) (inv_nonneg.mpr hv.le)
    _ = ptiConstI k / (1 - u) * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (a - b)) := by
        rw [ptiConstI, hc1, div_eq_mul_inv]



private theorem ptiConvC_pos (k : ℕ) : 0 < ptiConvC k := by
  unfold ptiConvC; have := radC_pos κ₀_pos; positivity

/-! ### `lem:propT`, `(TTT2)`, for the `L^∞` distance -/

/-- **Pin `lem:propT`, `(TTT2)`, `L^∞` form**: `Σ_c 𝒯_u(|a-c|_∞) 𝒯_t(|c-b|_∞) ≤ C_d/(1-u) ·
𝒯_t(|a-b|_∞)` for `0 ≤ u ≤ t < 1` with (i) `1-t ≥ g²/L²` or (ii) `1-u ≤ g²/L²`; `C_d` depends on `d`
only.  `EKPropT` (`Evolution/Pins.lean`) with `Gauss.zdistInf` in place of `zdistD` in all three
places; no propagator pin. -/
def EKPropTInf (d : ℕ) : Prop :=
  3 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 →
        (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) →
        ∀ a b : Zd d L,
          ∑ c : Zd d L, tailT d L g u (Gauss.zdistInf d L (a - c))
              * tailT d L g t (Gauss.zdistInf d L (c - b))
            ≤ C / (1 - u) * tailT d L g t (Gauss.zdistInf d L (a - b))

/-- **`lem:propT`, `(TTT2)`, for `|·|_∞`.**  The constant is
`ptiConstI k + ptiConstII k` with `d = k + 2`; it depends on `d` only. -/
theorem ekPropTInf_holds (d : ℕ) : EKPropTInf d := by
  intro hd
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hcC := ptiConvC_pos k
  have hI : 0 ≤ ptiConstI k := by
    unfold ptiConstI
    have : 0 ≤ ptiZC k := by unfold ptiZC; positivity
    positivity
  have hII : ptiConvC k ≤ ptiConstII k := by
    unfold ptiConstII
    have : 0 ≤ (2 * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1)) + 1) * exp 1 := by
      have := radC_pos (one_pos : (0 : ℝ) < 1)
      positivity
    linarith
  refine ⟨ptiConstI k + ptiConstII k, by linarith, ?_⟩
  intro L _ g u t hg hu hut ht hreg a b
  have hv : 0 < 1 - u := by linarith
  have hT0 := tailT_nonneg (d := k + 2) (L := L) (g := g) (t := t)
    (Nat.cast_nonneg (Gauss.zdistInf (k + 2) L (a - b)))
  rcases hreg with h | h
  · calc _ ≤ ptiConstI k / (1 - u) * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (a - b)) :=
          pti_i hg hut ht h a b
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hT0
          exact div_le_div_of_nonneg_right (by linarith) hv.le
  · calc _ ≤ ptiConstII k / (1 - u) * tailT (k + 2) L g t (Gauss.zdistInf (k + 2) L (a - b)) :=
          pti_ii hg hut ht h a b
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hT0
          exact div_le_div_of_nonneg_right (by linarith) hv.le

/-! ### Compiled nonempty instances

`d = 3`, `L = 5`, `a = 0`, `b = (2, 2, 2)`: `|b|_∞ = 2` and `|b|_{ℓ¹} = 6` (`pti_inst_dist`), so the
two distances differ at the data.  `g = 1/2` (`g²/L² = 1/100`) unless stated.  No hypothesis of
`ekPropTInf_holds` is left open.
* case (i): `u = 1/2`, `t = 9/10`;
* case (ii): `u = 199/200`, `t = 999/1000` (`1 - u = 1/200 ≤ 1/100`);
* boundary `1 - t = g²/L²` exactly, `u = 0`, `t = 99/100`;
* boundary `u = t = 99/100` (`1 - t = g²/L²`, both cases hold);
* boundary `1 - u = g²/L²` exactly, case (ii): `u = 99/100`, `t = 995/1000`;
* `g = 10 > L = 5`, `u = 0`, `t = 1/2` (case (ii): `1 - u = 1 ≤ g²/L² = 4`);
* one constant `C` at two torus sizes, `L = 5` (case (i)) and `L = 7` (case (ii)). -/

section Instances

private abbrev ptiB : Zd 3 5 := ![2, 2, 2]

private theorem pti_inst_dist :
    Gauss.zdistInf 3 5 (0 - ptiB) = 2 ∧ zdistD 3 5 (0 - ptiB) = 6 := by
  decide +kernel

/-- case (i), `u = 1/2`, `t = 9/10`. -/
private theorem ptiInst_i : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 (1 / 2) (1 / 2) (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (9 / 10) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 1 / 2) * tailT 3 5 (1 / 2) (9 / 10) (Gauss.zdistInf 3 5 (0 - ptiB)) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 (1 / 2) (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl (by norm_num)) 0 ptiB⟩

/-- case (ii), `u = 199/200`, `t = 999/1000`. -/
private theorem ptiInst_ii : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 (1 / 2) (199 / 200) (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (999 / 1000) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 199 / 200) *
        tailT 3 5 (1 / 2) (999 / 1000) (Gauss.zdistInf 3 5 (0 - ptiB)) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 (1 / 2) (199 / 200) (999 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr (by norm_num)) 0 ptiB⟩

/-- boundary `1 - t = g²/L²` exactly, `u = 0`, `t = 99/100`. -/
private theorem ptiInst_bdry_t : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 (1 / 2) 0 (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (99 / 100) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 0) * tailT 3 5 (1 / 2) (99 / 100) (Gauss.zdistInf 3 5 (0 - ptiB)) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 (1 / 2) 0 (99 / 100) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (Or.inl (by norm_num)) 0 ptiB⟩

/-- boundary `u = t = 99/100`, `1 - t = g²/L²`. -/
private theorem ptiInst_bdry_ut : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 (1 / 2) (99 / 100) (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (99 / 100) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 99 / 100) * tailT 3 5 (1 / 2) (99 / 100) (Gauss.zdistInf 3 5 (0 - ptiB)) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 (1 / 2) (99 / 100) (99 / 100) (by norm_num) (by norm_num) le_rfl
    (by norm_num) (Or.inl (by norm_num)) 0 ptiB⟩

/-- boundary `1 - u = g²/L²` exactly (case (ii)), `u = 99/100`, `t = 995/1000`. -/
private theorem ptiInst_bdry_u : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 (1 / 2) (99 / 100) (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (995 / 1000) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 99 / 100) *
        tailT 3 5 (1 / 2) (995 / 1000) (Gauss.zdistInf 3 5 (0 - ptiB)) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 (1 / 2) (99 / 100) (995 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr (by norm_num)) 0 ptiB⟩

/-- `g = 10 > L = 5`, `u = 0`, `t = 1/2` (case (ii)). -/
private theorem ptiInst_gL : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 10 0 (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 10 (1 / 2) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 0) * tailT 3 5 10 (1 / 2) (Gauss.zdistInf 3 5 (0 - ptiB)) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 10 0 (1 / 2) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (Or.inr (by norm_num)) 0 ptiB⟩

/-- one constant `C` at two different torus sizes: `L = 5` (case (i), `a = 0`, `b = (2,2,2)`) and
`L = 7` (case (ii): `g = 8`, `u = 1/50`, `t = 1/2`, `1 - u = 49/50 ≤ g²/L² = 64/49`;
`a = (1,0,0)`, `b = (1,2,3)`). -/
private theorem ptiInst_uniform : ∃ C : ℝ, 0 < C ∧
    (∑ c : Zd 3 5, tailT 3 5 (1 / 2) (1 / 2) (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (9 / 10) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 1 / 2) * tailT 3 5 (1 / 2) (9 / 10) (Gauss.zdistInf 3 5 (0 - ptiB))) ∧
    (∑ c : Zd 3 7, tailT 3 7 8 (1 / 50) (Gauss.zdistInf 3 7 (![1, 0, 0] - c)) *
        tailT 3 7 8 (1 / 2) (Gauss.zdistInf 3 7 (c - ![1, 2, 3]))
      ≤ C / (1 - 1 / 50) *
        tailT 3 7 8 (1 / 2) (Gauss.zdistInf 3 7 (![1, 0, 0] - ![1, 2, 3]))) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC,
    H 5 (1 / 2) (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Or.inl (by norm_num)) 0 ptiB,
    H 7 8 (1 / 50) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Or.inr (by norm_num)) ![1, 0, 0] ![1, 2, 3]⟩

end Instances

end RBM
