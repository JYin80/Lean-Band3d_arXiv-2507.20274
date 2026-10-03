/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.HeatProduct
import RBM3D.Propagator.LaplaceGauss
import RBM3D.Propagator.Pins
import RBM3D.Propagator.Prop5Short

/-!
# The unit first and second differences of `Θ` (route H, ticket T2024; design `T2003` split row F
and N5, Fable review `docs/claude-team/fable/2026-10-02-routeH.md` F5, F7)

For `σ₁ ≠ σ₂` one has `μ = m m̄ = 1`, `Θ_t = Theta d L g t` with real `t`, and by the merged
`RBM.Heat.Theta_eq_laplace_prod` and the substitution `τ = γ s` (`γ = lgGam d g t`),
`Θ_t(0, a) = γ⁻¹ ∫₀^∞ e^{-ετ} K_τ(a) dτ`, `ε = (1 - t)/γ`.  Hence the unit differences are
`γ⁻¹ ∫₀^∞ e^{-ετ} (ΔK_τ)(a) dτ`.  On `(0, L²]` the merged `kProd_diff1_le` / `kProd_diff2_le`
bound `|ΔK_τ|` by the Laplace–Gauss integrand `lgIntegrand (d+1)` resp. `(d+2)`, whose integral is
controlled by `lg_bulk` / `lg_zero`; on `(L², ∞)` the merged `kProd_gap` gives `|ΔK_τ| ≤
C L^{-(d+1)} e^{-cτ/L²}` (resp. `L^{-(d+2)}`) and `lg_tail` the integral.  `lg_convA` turns `γ⁻¹`,
`(1 - t)⁻¹` into `C (g² + 1 - t)⁻¹`.  There is no zero-mode term, so the pinned shapes
`(g² + |1-t|)⁻¹ (|a|+1)^{-(d-1)}` and `(g² + |1-t|)⁻¹ (|a|+1)^{-d}` have no loss.
For `σ₁ = σ₂` (bulk `κ ≤ Im m`) the merged `prop5Short_holds` bounds each term by
`C (1_{·=0} + g² e^{-c|·|})`; `t = 0` is `Θ_0 = 1`.

## Main results

* `RBM.PropUnit1`, `RBM.PropUnit2`: the pinned statements (the unit pins U1, U2s, U2m).
* `RBM.propUnit1_holds`, `RBM.propUnit2_holds`: `∀ d Λ κ, PropUnit1 d Λ κ` resp. `PropUnit2 d Λ κ`.
-/

open MeasureTheory Set RBM.Heat

namespace RBM

/-- **Unit pin 1**: `|Θ_t(0, a + e_j) − Θ_t(0, a)| ≤ C (g² + |1−t|)⁻¹ (|a| + 1)^{-(d−1)}`; constants `(d, Λ, κ)`;
bulk `κ ≤ Im m` (idle for `σ₁ ≠ σ₂`, as in the merged P6–P8 pins). -/
def PropUnit1 (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool,
          ∀ (a : Zd d L) (j : Fin d),
            haveI : NeZero L := ⟨by omega⟩
            ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single j 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
              ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Unit pin 2**: the unit second differences, mixed (`i ≠ j`) and same-direction (`i = j`):
`|Θ(a+e_i+e_j) − Θ(a+e_i) − Θ(a+e_j) + Θ(a)| ≤ C (g² + |1−t|)⁻¹ (|a| + 1)^{-d}`. -/
def PropUnit2 (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool,
          ∀ (a : Zd d L) (i j : Fin d),
            haveI : NeZero L := ⟨by omega⟩
            ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single i 1 + Pi.single j 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single i 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single j 1)
                + Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
              ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-! ### Lattice facts -/

/-- `2 |u|_L ≤ L` on the cycle `ℤ_L`. -/
private lemma pu_zdist_two_le (L : ℕ) (u : ZMod L) : 2 * zdist L u ≤ L := by
  unfold zdist
  omega

/-- `2 |x| ≤ d L` on the torus (`|x|` the periodic `ℓ¹` distance). -/
private lemma pu_zdistD_two_le (d L : ℕ) (x : Zd d L) : 2 * zdistD d L x ≤ d * L := by
  unfold zdistD
  rw [Finset.mul_sum]
  calc ∑ i, 2 * zdist L (x i) ≤ ∑ _i : Fin d, L :=
        Finset.sum_le_sum (fun i _ => pu_zdist_two_le L (x i))
    _ = d * L := by simp

/-- The unit step has length `≤ 1` on the cycle. -/
private lemma pu_zdist_one_le (L : ℕ) : zdist L (1 : ZMod L) ≤ 1 := by
  unfold zdist
  refine (min_le_left _ _).trans ?_
  rw [ZMod.val_one_eq_one_mod]
  exact Nat.mod_le _ _

/-- The unit vector `e_j` has length `≤ 1`. -/
private lemma pu_zdistD_single_le (d L : ℕ) (j : Fin d) :
    zdistD d L (Pi.single j (1 : ZMod L)) ≤ 1 := by
  unfold zdistD
  rw [Finset.sum_eq_single j]
  · simpa using pu_zdist_one_le L
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `|a| ≤ |a + u| + |u|`. -/
private lemma pu_shift {d L : ℕ} [NeZero L] (a u : Zd d L) :
    zdistD d L a ≤ zdistD d L (a + u) + zdistD d L u := by
  have h := zdistD_add_le d L (a + u) (-u)
  rw [add_neg_cancel_right, zdistD_neg] at h
  exact h

/-- `(x + 1)^k e^{-c x} ≤ k! (2/c)^k e^{c/2}` for `x ≥ 0`, `c > 0`. -/
private lemma pu_pow_exp_le {c : ℝ} (hc : 0 < c) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ k * Real.exp (-c * x) ≤ (k.factorial : ℝ) * (2 / c) ^ k * Real.exp (c / 2) := by
  have h := Real.pow_div_factorial_le_exp ((c / 2) * (x + 1)) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  have h2 : ((c / 2) * (x + 1)) ^ k * (2 / c) ^ k = (x + 1) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have h3 : Real.exp ((c / 2) * (x + 1)) * Real.exp (-c * x) ≤ Real.exp (c / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hc.le hx]
  calc (x + 1) ^ k * Real.exp (-c * x)
      = ((c / 2) * (x + 1)) ^ k * (2 / c) ^ k * Real.exp (-c * x) := by rw [h2]
    _ ≤ (Real.exp ((c / 2) * (x + 1)) * k.factorial) * (2 / c) ^ k * Real.exp (-c * x) := by
        gcongr
    _ = (Real.exp ((c / 2) * (x + 1)) * Real.exp (-c * x)) * (k.factorial * (2 / c) ^ k) := by
        ring
    _ ≤ Real.exp (c / 2) * (k.factorial * (2 / c) ^ k) := by gcongr
    _ = _ := by ring

/-! ### The real-variable estimates: head, tail, integral bound -/

/-- The head: `γ⁻¹ ∫₀^∞ lgIntegrand ≤ C_H (g² + e)⁻¹ (N + 1)^{-p}` (`m = p + 2`, `ε = e/γ`; the
cases `N = 0`, `N ≥ 1` and `ε ≶ 1` of `lg_zero`, `lg_bulk`, with `lg_convA`'s hypotheses). -/
private lemma pu_head {m p : ℕ} (hm : m = p + 2) (hp : 2 ≤ p) {cK CA : ℝ} (hcK : 0 < cK)
    (hCA : 0 < CA) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ (γ e g2 : ℝ) (N : ℕ), 0 < γ → 0 < e → 0 < g2 →
      (1 ≤ e / γ → 1 / e ≤ CA / (g2 + e)) → (e / γ < 1 → 1 / γ ≤ CA / (g2 + e)) →
      γ⁻¹ * ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK (N : ℝ) (e / γ) τ
        ≤ CH * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
  have hm3 : 3 ≤ m := by omega
  obtain ⟨CB, hCB, c', hc', hbulk⟩ := lg_bulk m hm3 cK hcK
  set Mp : ℝ := (p.factorial : ℝ) * (2 / c') ^ p * Real.exp (c' / 2) with hMp
  have hMp0 : 0 < Mp := by positivity
  refine ⟨CA * (2 + CB * 2 ^ p + 2 * Mp), by positivity, ?_⟩
  intro γ e g2 N hγ he hg2 hA1 hA2
  have hε : 0 < e / γ := div_pos he hγ
  have hge : γ⁻¹ * (1 / (e / γ)) = 1 / e := by field_simp
  have hg2e : 0 < g2 + e := by positivity
  have hp' : ((m : ℝ) - 2) = (p : ℝ) := by rw [hm]; push_cast; ring
  have hCAe : CA / (g2 + e) = CA * (g2 + e)⁻¹ := div_eq_mul_inv _ _
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- `N = 0`
    subst hN
    obtain ⟨-, hz1, hz2⟩ := lg_zero m hm3 cK (e / γ) hε.le
    have hT : (g2 + e)⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ p)⁻¹ = (g2 + e)⁻¹ := by simp
    rw [hT]
    simp only [Nat.cast_zero]
    have hK0 : 0 ≤ (g2 + e)⁻¹ := by positivity
    rcases lt_or_ge (e / γ) 1 with hlt | hge1
    · have h2 : 1 + 2 / ((m : ℝ) - 2) ≤ 2 := by
        rw [hp']
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
        have : 2 / (p : ℝ) ≤ 1 := by
          rw [div_le_one hp0]; exact_mod_cast hp
        linarith
      calc γ⁻¹ * ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK 0 (e / γ) τ
          ≤ γ⁻¹ * 2 := by
            apply mul_le_mul_of_nonneg_left (hz1.trans h2) (by positivity)
        _ = 2 * (1 / γ) := by ring
        _ ≤ 2 * (CA / (g2 + e)) := mul_le_mul_of_nonneg_left (hA2 hlt) (by norm_num)
        _ = 2 * CA * (g2 + e)⁻¹ := by rw [hCAe]; ring
        _ ≤ CA * (2 + CB * 2 ^ p + 2 * Mp) * (g2 + e)⁻¹ := by
            have h1 : 0 ≤ CA * (CB * 2 ^ p + 2 * Mp) := by positivity
            nlinarith [mul_nonneg h1 hK0]
    · calc γ⁻¹ * ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK 0 (e / γ) τ
          ≤ γ⁻¹ * (1 / (e / γ)) := by
            apply mul_le_mul_of_nonneg_left (hz2 hε) (by positivity)
        _ = 1 / e := hge
        _ ≤ CA / (g2 + e) := hA1 hge1
        _ = CA * (g2 + e)⁻¹ := hCAe
        _ ≤ CA * (2 + CB * 2 ^ p + 2 * Mp) * (g2 + e)⁻¹ := by
            have h1 : 0 ≤ CA * (1 + CB * 2 ^ p + 2 * Mp) := by positivity
            nlinarith [mul_nonneg h1 hK0]
  · -- `N ≥ 1`
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    obtain ⟨-, hb1, hb2⟩ := hbulk (N : ℝ) (e / γ) hN1 hε.le
    have hNp : 0 < (N : ℝ) ^ p := by positivity
    have hN1p : 0 < ((N : ℝ) + 1) ^ p := by positivity
    have hK0 : 0 ≤ (g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹ := by positivity
    rcases lt_or_ge (e / γ) 1 with hlt | hge1
    · have hJ := hb1 hlt.le
      have hex : Real.exp (-c' * (N : ℝ) * Real.sqrt (e / γ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ c' * (N : ℝ) * Real.sqrt (e / γ) := by positivity
        linarith
      have hpow : (N : ℝ) ^ (-((m : ℝ) - 2)) = ((N : ℝ) ^ p)⁻¹ := by
        rw [hp', Real.rpow_neg hN0.le, Real.rpow_natCast]
      rw [hpow] at hJ
      have hJ' : ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK (N : ℝ) (e / γ) τ ≤ CB * ((N : ℝ) ^ p)⁻¹ := by
        refine hJ.trans ?_
        have h0 : 0 ≤ CB * ((N : ℝ) ^ p)⁻¹ := by positivity
        calc CB * ((N : ℝ) ^ p)⁻¹ * Real.exp (-c' * (N : ℝ) * Real.sqrt (e / γ))
            ≤ CB * ((N : ℝ) ^ p)⁻¹ * 1 := mul_le_mul_of_nonneg_left hex h0
          _ = _ := mul_one _
      have hNN : ((N : ℝ) ^ p)⁻¹ ≤ 2 ^ p * (((N : ℝ) + 1) ^ p)⁻¹ := by
        rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hNp hN1p, one_mul]
        have h2 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
        calc ((N : ℝ) + 1) ^ p ≤ (2 * (N : ℝ)) ^ p := pow_le_pow_left₀ (by positivity) h2 p
          _ = 2 ^ p * (N : ℝ) ^ p := mul_pow _ _ _
      calc γ⁻¹ * ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK (N : ℝ) (e / γ) τ
          ≤ γ⁻¹ * (CB * (2 ^ p * (((N : ℝ) + 1) ^ p)⁻¹)) := by
            apply mul_le_mul_of_nonneg_left (hJ'.trans _) (by positivity)
            exact mul_le_mul_of_nonneg_left hNN hCB.le
        _ = (1 / γ) * (CB * 2 ^ p) * (((N : ℝ) + 1) ^ p)⁻¹ := by ring
        _ ≤ (CA / (g2 + e)) * (CB * 2 ^ p) * (((N : ℝ) + 1) ^ p)⁻¹ := by
            have h0 : 0 ≤ (CB * 2 ^ p) * (((N : ℝ) + 1) ^ p)⁻¹ := by positivity
            nlinarith [mul_le_mul_of_nonneg_right (hA2 hlt) h0]
        _ = CA * (CB * 2 ^ p) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by rw [hCAe]; ring
        _ ≤ CA * (2 + CB * 2 ^ p + 2 * Mp) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
            have h1 : 0 ≤ CA * (2 + 2 * Mp) := by positivity
            nlinarith [mul_nonneg h1 hK0]
    · have hJ := hb2 hge1
      have hexp : Real.exp (-c' * (N : ℝ)) ≤ Mp * (((N : ℝ) + 1) ^ p)⁻¹ := by
        have := pu_pow_exp_le hc' p hN0.le
        rw [← div_eq_mul_inv, le_div_iff₀ hN1p]
        linarith [mul_comm (((N : ℝ) + 1) ^ p) (Real.exp (-c' * (N : ℝ)))]
      calc γ⁻¹ * ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK (N : ℝ) (e / γ) τ
          ≤ γ⁻¹ * (2 / (e / γ) * Real.exp (-c' * (N : ℝ))) := by
            apply mul_le_mul_of_nonneg_left hJ (by positivity)
        _ = 2 * (1 / e) * Real.exp (-c' * (N : ℝ)) := by field_simp
        _ ≤ 2 * (CA / (g2 + e)) * Real.exp (-c' * (N : ℝ)) := by
            have h0 := (Real.exp_pos (-c' * (N : ℝ))).le
            have := hA1 hge1
            nlinarith [mul_le_mul_of_nonneg_right this h0]
        _ ≤ 2 * (CA / (g2 + e)) * (Mp * (((N : ℝ) + 1) ^ p)⁻¹) := by
            gcongr
        _ = 2 * CA * Mp * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by rw [hCAe]; ring
        _ ≤ CA * (2 + CB * 2 ^ p + 2 * Mp) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
            have h1 : 0 ≤ CA * (2 + CB * 2 ^ p) := by positivity
            nlinarith [mul_nonneg h1 hK0]

/-- The tail: `γ⁻¹ L^{-m} min(1/ε, L²/c_G) ≤ C_T (g² + e)⁻¹ (N + 1)^{-p}` for `N ≤ dL/2`. -/
private lemma pu_tail {m p : ℕ} (hm : m = p + 2) {cG CA : ℝ} (hcG : 0 < cG) (hCA : 0 < CA)
    (d : ℕ) :
    ∃ CT : ℝ, 0 < CT ∧ ∀ (γ e g2 : ℝ) (L N : ℕ), 0 < γ → 0 < e → 0 < g2 → 1 ≤ L →
      2 * N ≤ d * L →
      (1 ≤ e / γ → 1 / e ≤ CA / (g2 + e)) → (e / γ < 1 → 1 / γ ≤ CA / (g2 + e)) →
      γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * min (1 / (e / γ)) ((L : ℝ) ^ 2 / cG))
        ≤ CT * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
  set Pp : ℝ := ((d : ℝ) / 2 + 1) ^ p with hPp
  have hPp0 : 0 < Pp := by positivity
  refine ⟨CA * Pp * (1 + 1 / cG), by positivity, ?_⟩
  intro γ e g2 L N hγ he hg2 hL hNL hA1 hA2
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  have hg2e : 0 < g2 + e := by positivity
  have hLp : 0 < (L : ℝ) ^ p := by positivity
  have hN1p : 0 < ((N : ℝ) + 1) ^ p := by positivity
  have hNL' : 2 * (N : ℝ) ≤ (d : ℝ) * L := by exact_mod_cast hNL
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hCAe : CA / (g2 + e) = CA * (g2 + e)⁻¹ := div_eq_mul_inv _ _
  have hLN : ((L : ℝ) ^ p)⁻¹ ≤ Pp * (((N : ℝ) + 1) ^ p)⁻¹ := by
    have h1 : (N : ℝ) + 1 ≤ ((d : ℝ) / 2 + 1) * (L : ℝ) := by nlinarith
    have h2 : ((N : ℝ) + 1) ^ p ≤ Pp * (L : ℝ) ^ p := by
      calc ((N : ℝ) + 1) ^ p ≤ (((d : ℝ) / 2 + 1) * (L : ℝ)) ^ p :=
            pow_le_pow_left₀ (by positivity) h1 p
        _ = Pp * (L : ℝ) ^ p := mul_pow _ _ _
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hLp hN1p, one_mul]
    exact h2
  have hLm : ((L : ℝ) ^ m)⁻¹ ≤ ((L : ℝ) ^ p)⁻¹ := by
    apply inv_anti₀ hLp
    exact pow_le_pow_right₀ hLr (by omega)
  have hLm2 : ((L : ℝ) ^ m)⁻¹ * (L : ℝ) ^ 2 = ((L : ℝ) ^ p)⁻¹ := by
    rw [hm, pow_add]; field_simp
  have hTg : 0 ≤ (g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹ := by positivity
  have hmin0 : ∀ x y : ℝ, min x y ≤ x := fun x y => min_le_left x y
  have hmin1 : ∀ x y : ℝ, min x y ≤ y := fun x y => min_le_right x y
  rcases lt_or_ge (e / γ) 1 with hlt | hge1
  · calc γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * min (1 / (e / γ)) ((L : ℝ) ^ 2 / cG))
        ≤ γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * ((L : ℝ) ^ 2 / cG)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmin1 _ _) (by positivity)
      _ = (1 / γ) * (1 / cG) * ((((L : ℝ) ^ m)⁻¹ * (L : ℝ) ^ 2)) := by
          field_simp
      _ = (1 / γ) * (1 / cG) * ((L : ℝ) ^ p)⁻¹ := by rw [hLm2]
      _ ≤ (CA / (g2 + e)) * (1 / cG) * (Pp * (((N : ℝ) + 1) ^ p)⁻¹) := by
          have h1 : 0 ≤ (1 / cG) * ((L : ℝ) ^ p)⁻¹ := by positivity
          have h2 : 0 ≤ (CA / (g2 + e)) * (1 / cG) := by positivity
          calc (1 / γ) * (1 / cG) * ((L : ℝ) ^ p)⁻¹
              = (1 / γ) * ((1 / cG) * ((L : ℝ) ^ p)⁻¹) := by ring
            _ ≤ (CA / (g2 + e)) * ((1 / cG) * ((L : ℝ) ^ p)⁻¹) :=
                mul_le_mul_of_nonneg_right (hA2 hlt) h1
            _ = (CA / (g2 + e)) * (1 / cG) * ((L : ℝ) ^ p)⁻¹ := by ring
            _ ≤ (CA / (g2 + e)) * (1 / cG) * (Pp * (((N : ℝ) + 1) ^ p)⁻¹) :=
                mul_le_mul_of_nonneg_left hLN h2
      _ = CA * Pp * (1 / cG) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by rw [hCAe]; ring
      _ ≤ CA * Pp * (1 + 1 / cG) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
          have h1 : 0 ≤ CA * Pp := by positivity
          nlinarith [mul_nonneg h1 hTg]
  · calc γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * min (1 / (e / γ)) ((L : ℝ) ^ 2 / cG))
        ≤ γ⁻¹ * (((L : ℝ) ^ m)⁻¹ * (1 / (e / γ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmin0 _ _) (by positivity)
      _ = ((L : ℝ) ^ m)⁻¹ * (1 / e) := by field_simp
      _ ≤ ((L : ℝ) ^ p)⁻¹ * (CA / (g2 + e)) := by
          have h1 : 0 ≤ 1 / e := by positivity
          have h2 : 0 ≤ ((L : ℝ) ^ p)⁻¹ := by positivity
          calc ((L : ℝ) ^ m)⁻¹ * (1 / e) ≤ ((L : ℝ) ^ p)⁻¹ * (1 / e) :=
                mul_le_mul_of_nonneg_right hLm h1
            _ ≤ ((L : ℝ) ^ p)⁻¹ * (CA / (g2 + e)) :=
                mul_le_mul_of_nonneg_left (hA1 hge1) h2
      _ ≤ (Pp * (((N : ℝ) + 1) ^ p)⁻¹) * (CA / (g2 + e)) :=
          mul_le_mul_of_nonneg_right hLN (by positivity)
      _ = CA * Pp * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by rw [hCAe]; ring
      _ ≤ CA * Pp * (1 + 1 / cG) * ((g2 + e)⁻¹ * (((N : ℝ) + 1) ^ p)⁻¹) := by
          have h1 : 0 ≤ CA * Pp := by positivity
          have h2 : 0 ≤ CA * Pp * (1 / cG) := by positivity
          nlinarith [mul_nonneg h2 hTg]

/-- The Laplace–Gauss integrand is nonnegative for `τ > 0`. -/
private lemma pu_lg_nonneg (m : ℕ) (c n ε : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ lgIntegrand m c n ε τ := by
  unfold lgIntegrand
  have : 0 ≤ min 1 (τ ^ (-(m : ℝ) / 2)) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  positivity

/-- The abstract integral bound: a continuous `f` with the head bound on `(0, L²]` and the tail
bound on `[L², ∞)` has `∫ e^{-ετ} f ≤ C_K ∫ lgIntegrand + C_G L^{-m} min(1/ε, L²/c_G)`. -/
private lemma pu_int_bound {m : ℕ} {Lr : ℝ} (hLr : 0 < Lr) {f : ℝ → ℝ}
    (hf : Continuous f) {CK cK CG cG n ε : ℝ} (hCK : 0 ≤ CK) (hCG : 0 ≤ CG) (hcG : 0 < cG)
    (hε : 0 < ε) (hJ : IntegrableOn (lgIntegrand m cK n ε) (Ioi 0))
    (hhead : ∀ τ : ℝ, 0 < τ → τ ≤ Lr ^ 2 →
      |f τ| ≤ CK * min 1 (τ ^ (-(m : ℝ) / 2)) * Real.exp (-cK * min (n ^ 2 / τ) n))
    (htail : ∀ τ : ℝ, Lr ^ 2 ≤ τ → |f τ| ≤ CG * (Lr ^ m)⁻¹ * Real.exp (-cG * τ / Lr ^ 2)) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * f τ) (Ioi 0) ∧
    |∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) * f τ|
      ≤ CK * (∫ τ in Ioi (0 : ℝ), lgIntegrand m cK n ε τ)
        + CG * (Lr ^ m)⁻¹ * min (1 / ε) (Lr ^ 2 / cG) := by
  set T : ℝ := Lr ^ 2 with hT
  have hT0 : 0 < T := by positivity
  set fe : ℝ → ℝ := fun τ => Real.exp (-ε * τ) * f τ with hfe
  have hfe_cont : Continuous fe :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf
  have hheadb : ∀ τ ∈ Ioc 0 T, |fe τ| ≤ CK * lgIntegrand m cK n ε τ := by
    intro τ hτ
    have h := hhead τ hτ.1 hτ.2
    have he0 := Real.exp_pos (-ε * τ)
    simp only [hfe, abs_mul, abs_of_pos he0]
    unfold lgIntegrand
    calc Real.exp (-ε * τ) * |f τ|
        ≤ Real.exp (-ε * τ) * (CK * min 1 (τ ^ (-(m : ℝ) / 2))
            * Real.exp (-cK * min (n ^ 2 / τ) n)) := mul_le_mul_of_nonneg_left h he0.le
      _ = _ := by ring
  have htailb : ∀ τ ∈ Ioi T, |fe τ| ≤ CG * (Lr ^ m)⁻¹ * Real.exp (-ε * τ - cG * τ / T) := by
    intro τ hτ
    have h := htail τ (le_of_lt hτ)
    have he0 := Real.exp_pos (-ε * τ)
    simp only [hfe, abs_mul, abs_of_pos he0]
    have e1 : Real.exp (-ε * τ - cG * τ / T) = Real.exp (-ε * τ) * Real.exp (-cG * τ / T) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1]
    calc Real.exp (-ε * τ) * |f τ|
        ≤ Real.exp (-ε * τ) * (CG * (Lr ^ m)⁻¹ * Real.exp (-cG * τ / T)) :=
          mul_le_mul_of_nonneg_left h he0.le
      _ = _ := by ring
  have ht := lg_tail T hT0
  obtain ⟨hI1, hV1⟩ := ht.1 ε cG hε.le hcG
  obtain ⟨-, hV2⟩ := ht.2.1 ε cG hε hcG.le
  have hHi : IntegrableOn fe (Ioc 0 T) := by
    refine Integrable.mono' ((hJ.mono_set Ioc_subset_Ioi_self).const_mul CK)
      hfe_cont.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [Real.norm_eq_abs]
    exact hheadb τ hτ
  have hTi : IntegrableOn fe (Ioi T) := by
    refine Integrable.mono' (hI1.const_mul (CG * (Lr ^ m)⁻¹)) hfe_cont.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [Real.norm_eq_abs]
    exact htailb τ hτ
  have hint : IntegrableOn fe (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hT0.le]
    exact hHi.union hTi
  refine ⟨hint, ?_⟩
  have hsplit : ∫ τ in Ioi (0 : ℝ), fe τ = (∫ τ in Ioc 0 T, fe τ) + ∫ τ in Ioi T, fe τ := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hHi hTi,
      Ioc_union_Ioi_eq_Ioi hT0.le]
  have hH : |∫ τ in Ioc 0 T, fe τ| ≤ CK * ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK n ε τ := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ τ in Ioc 0 T, fe τ‖ ≤ ∫ τ in Ioc 0 T, CK * lgIntegrand m cK n ε τ := by
          refine norm_integral_le_of_norm_le ((hJ.mono_set Ioc_subset_Ioi_self).const_mul CK) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).2
            (Filter.Eventually.of_forall fun τ hτ => ?_)
          rw [Real.norm_eq_abs]
          exact hheadb τ hτ
      _ = CK * ∫ τ in Ioc 0 T, lgIntegrand m cK n ε τ := integral_const_mul _ _
      _ ≤ CK * ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK n ε τ := by
          apply mul_le_mul_of_nonneg_left _ hCK
          refine setIntegral_mono_set hJ ?_ (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
          exact pu_lg_nonneg m cK n ε hτ
  have hεT : Real.exp (-ε * T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hTl : |∫ τ in Ioi T, fe τ| ≤ CG * (Lr ^ m)⁻¹ * min (1 / ε) (T / cG) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ τ in Ioi T, fe τ‖
        ≤ ∫ τ in Ioi T, CG * (Lr ^ m)⁻¹ * Real.exp (-ε * τ - cG * τ / T) := by
          refine norm_integral_le_of_norm_le (hI1.const_mul _) ?_
          refine (ae_restrict_iff' measurableSet_Ioi).2
            (Filter.Eventually.of_forall fun τ hτ => ?_)
          rw [Real.norm_eq_abs]
          exact htailb τ hτ
      _ = CG * (Lr ^ m)⁻¹ * ∫ τ in Ioi T, Real.exp (-ε * τ - cG * τ / T) :=
          integral_const_mul _ _
      _ ≤ CG * (Lr ^ m)⁻¹ * min (1 / ε) (T / cG) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine le_min ?_ ?_
          · calc _ ≤ Real.exp (-ε * T) / ε := hV2
              _ ≤ 1 / ε := by
                  rw [div_le_div_iff_of_pos_right hε]; exact hεT
          · calc _ ≤ Real.exp (-ε * T) * (T / cG) := hV1
              _ ≤ 1 * (T / cG) := mul_le_mul_of_nonneg_right hεT (by positivity)
              _ = _ := one_mul _
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hH hTl)

/-! ### The Laplace representation of the unit differences -/

/-- `τ ↦ K_τ(x)` is continuous (`hkT` is a finite sum of cosines times exponentials). -/
private lemma pu_kProd_cont (d L : ℕ) [NeZero L] (x : Zd d L) :
    Continuous (fun τ : ℝ => kProd d L τ x) := by
  unfold kProd hkT
  fun_prop

/-- `0 ≤ K_τ ≤ 1` for `τ ≥ 0` (from the merged `hkT_mass`). -/
private lemma pu_kProd_nonneg_le_one (d L : ℕ) [NeZero L] {τ : ℝ} (hτ : 0 ≤ τ) (a : Zd d L) :
    0 ≤ kProd d L τ a ∧ kProd d L τ a ≤ 1 := by
  obtain ⟨h0, h1⟩ := hkT_mass L τ hτ
  have hle : ∀ x : ZMod L, hkT L τ x ≤ 1 := fun x => by
    calc hkT L τ x ≤ ∑ y : ZMod L, hkT L τ y :=
          Finset.single_le_sum (f := fun y => hkT L τ y) (fun y _ => h0 y) (Finset.mem_univ x)
      _ = 1 := h1
  exact ⟨Finset.prod_nonneg (fun j _ => h0 _), Finset.prod_le_one₀ (fun j _ => h0 _)
    (fun j _ => hle _)⟩

/-- `e^{-ετ} K_τ(a)` is integrable on `(0, ∞)` for `ε > 0`. -/
private lemma pu_int_K (d L : ℕ) [NeZero L] {ε : ℝ} (hε : 0 < ε) (a : Zd d L) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kProd d L τ a) (Ioi 0) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hε)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (pu_kProd_cont d L a)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
  have h := pu_kProd_nonneg_le_one d L (le_of_lt (mem_Ioi.1 hτ)) a
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le h.1)]
  calc Real.exp (-ε * τ) * kProd d L τ a ≤ Real.exp (-ε * τ) * 1 :=
        mul_le_mul_of_nonneg_left h.2 (Real.exp_pos _).le
    _ = Real.exp (-ε * τ) := mul_one _

/-- `Θ_t(0, a) = γ⁻¹ ∫₀^∞ e^{-ετ} K_τ(a) dτ` (`Theta_eq_laplace_prod` and `τ = γ s`). -/
private lemma pu_Theta_eq {d L : ℕ} (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht0 : 0 < t)
    (ht1 : t < 1) (a : Zd d L) :
    haveI : NeZero L := ⟨by omega⟩
    Theta d L g (t : ℂ) 0 a
      = (((lgGam d g t)⁻¹ * ∫ τ in Ioi (0 : ℝ),
          Real.exp (-(lgEps d g t) * τ) * kProd d L τ a : ℝ) : ℂ) := by
  have : NeZero L := ⟨by omega⟩
  rw [Theta_eq_laplace_prod d L hL g t hg ht0.le ht1 a]
  congr 1
  have hγ : 0 < lgGam d g t := by unfold lgGam; positivity
  have h := integral_comp_mul_left_Ioi
    (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ) * kProd d L τ a) 0 hγ
  simp only [mul_zero, smul_eq_mul] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  have hεγ : lgEps d g t * lgGam d g t = 1 - t := by
    unfold lgEps; field_simp
  change Real.exp (-(1 - t) * s) * kProd d L (lgGam d g t * s) a
    = Real.exp (-(lgEps d g t) * (lgGam d g t * s)) * kProd d L (lgGam d g t * s) a
  congr 2
  linear_combination s * hεγ

/-- The unit first difference as `γ⁻¹ |∫ e^{-ετ} (K_τ(a + e_j) - K_τ(a))|`. -/
private lemma pu_diff1_eq {d L : ℕ} (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht0 : 0 < t)
    (ht1 : t < 1) (a : Zd d L) (j : Fin d) :
    haveI : NeZero L := ⟨by omega⟩
    ‖Theta d L g (t : ℂ) 0 (a + Pi.single j 1) - Theta d L g (t : ℂ) 0 a‖
      = (lgGam d g t)⁻¹ * |∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) *
          (kProd d L τ (a + Pi.single j 1) - kProd d L τ a)| := by
  have : NeZero L := ⟨by omega⟩
  have hγ : 0 < lgGam d g t := by unfold lgGam; positivity
  have hε : 0 < lgEps d g t := by unfold lgEps; exact div_pos (by linarith) hγ
  rw [pu_Theta_eq hL hg ht0 ht1, pu_Theta_eq hL hg ht0 ht1, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have hI : ∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) *
        (kProd d L τ (a + Pi.single j 1) - kProd d L τ a)
      = (∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) * kProd d L τ (a + Pi.single j 1))
        - ∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) * kProd d L τ a := by
    simp_rw [mul_sub]
    exact integral_sub (pu_int_K d L hε _) (pu_int_K d L hε _)
  rw [hI, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hγ)]

/-- The unit second difference as `γ⁻¹ |∫ e^{-ετ} (Δ_i Δ_j K_τ)(a)|`. -/
private lemma pu_diff2_eq {d L : ℕ} (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht0 : 0 < t)
    (ht1 : t < 1) (a : Zd d L) (i j : Fin d) :
    haveI : NeZero L := ⟨by omega⟩
    ‖Theta d L g (t : ℂ) 0 (a + Pi.single i 1 + Pi.single j 1)
        - Theta d L g (t : ℂ) 0 (a + Pi.single i 1)
        - Theta d L g (t : ℂ) 0 (a + Pi.single j 1) + Theta d L g (t : ℂ) 0 a‖
      = (lgGam d g t)⁻¹ * |∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) *
          (kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
            - kProd d L τ (a + Pi.single j 1) + kProd d L τ a)| := by
  have : NeZero L := ⟨by omega⟩
  have hγ : 0 < lgGam d g t := by unfold lgGam; positivity
  have hε : 0 < lgEps d g t := by unfold lgEps; exact div_pos (by linarith) hγ
  rw [pu_Theta_eq hL hg ht0 ht1 (a + Pi.single i 1 + Pi.single j 1),
    pu_Theta_eq hL hg ht0 ht1 (a + Pi.single i 1), pu_Theta_eq hL hg ht0 ht1 (a + Pi.single j 1),
    pu_Theta_eq hL hg ht0 ht1 a, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
    ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  have i1 := pu_int_K d L hε (a + Pi.single i 1 + Pi.single j 1)
  have i2 := pu_int_K d L hε (a + Pi.single i 1)
  have i3 := pu_int_K d L hε (a + Pi.single j 1)
  have i4 := pu_int_K d L hε a
  have e : ∀ τ : ℝ, Real.exp (-(lgEps d g t) * τ) *
        (kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
          - kProd d L τ (a + Pi.single j 1) + kProd d L τ a)
      = Real.exp (-(lgEps d g t) * τ) * kProd d L τ (a + Pi.single i 1 + Pi.single j 1)
        - Real.exp (-(lgEps d g t) * τ) * kProd d L τ (a + Pi.single i 1)
        - Real.exp (-(lgEps d g t) * τ) * kProd d L τ (a + Pi.single j 1)
        + Real.exp (-(lgEps d g t) * τ) * kProd d L τ a := fun τ => by ring
  simp_rw [e]
  have i12 : IntegrableOn (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ)
      * kProd d L τ (a + Pi.single i 1 + Pi.single j 1)
      - Real.exp (-(lgEps d g t) * τ) * kProd d L τ (a + Pi.single i 1)) (Ioi 0) := i1.sub i2
  have i123 : IntegrableOn (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ)
      * kProd d L τ (a + Pi.single i 1 + Pi.single j 1)
      - Real.exp (-(lgEps d g t) * τ) * kProd d L τ (a + Pi.single i 1)
      - Real.exp (-(lgEps d g t) * τ) * kProd d L τ (a + Pi.single j 1)) (Ioi 0) := i12.sub i3
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2,
    ← mul_sub, ← mul_sub, ← mul_add, abs_mul, abs_of_pos (inv_pos.mpr hγ)]

/-- The glue: for a continuous `f` with the head and tail bounds, `γ⁻¹ |∫ e^{-ετ} f|` is bounded
by `C (g² + e)⁻¹ (|a| + 1)^{-p}` (`m = p + 2`). -/
private lemma pu_master (d : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) {m p : ℕ} (hm : m = p + 2) (hp : 2 ≤ p)
    {CK cK CG cG : ℝ} (hCK : 0 < CK) (hcK : 0 < cK) (hCG : 0 < CG) (hcG : 0 < cG) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ), 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (a : Zd d L) (f : ℝ → ℝ), Continuous f →
      (∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → |f τ| ≤ CK * min 1 (τ ^ (-(m : ℝ) / 2)) *
          Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ))) →
      (∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →
          |f τ| ≤ CG * ((L : ℝ) ^ m)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) →
      IntegrableOn (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ) * f τ) (Ioi 0) ∧
      (lgGam d g t)⁻¹ * |∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) * f τ|
        ≤ C * ((g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ p)⁻¹) := by
  have hm3 : 3 ≤ m := by omega
  obtain ⟨CA, hCA, hconv⟩ := lg_convA d Λ hΛ
  obtain ⟨CH, hCH, hhead⟩ := pu_head hm hp hcK hCA
  obtain ⟨CT, hCT, htail⟩ := pu_tail hm hcG hCA d
  obtain ⟨CB, hCB, c', hc', hbulk⟩ := lg_bulk m hm3 cK hcK
  refine ⟨CK * CH + CG * CT, by positivity, ?_⟩
  intro L hL g hg hgΛ t ht0 ht1 a f hf hh ht
  have hγ : 0 < lgGam d g t := by unfold lgGam; positivity
  have he : 0 < 1 - t := by linarith
  have hε : 0 < lgEps d g t := by unfold lgEps; exact div_pos he hγ
  have hg2 : 0 < g ^ 2 := by positivity
  have hLr : (0 : ℝ) < (L : ℝ) := by
    have : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  obtain ⟨hA1, hA2⟩ := hconv g t hg hgΛ ht0 ht1
  have hJ : IntegrableOn (lgIntegrand m cK (zdistD d L a : ℝ) (lgEps d g t)) (Ioi 0) := by
    rcases Nat.eq_zero_or_pos (zdistD d L a) with h0 | h0
    · rw [h0, Nat.cast_zero]; exact (lg_zero m hm3 cK _ hε.le).1
    · exact (hbulk _ _ (by exact_mod_cast h0) hε.le).1
  obtain ⟨hint, hbd⟩ := pu_int_bound hLr hf hCK.le hCG.le hcG hε hJ hh ht
  refine ⟨hint, ?_⟩
  have hN2 : 2 * zdistD d L a ≤ d * L := pu_zdistD_two_le d L a
  have h1 := hhead (lgGam d g t) (1 - t) (g ^ 2) (zdistD d L a) hγ he hg2 hA1 hA2
  have h2 := htail (lgGam d g t) (1 - t) (g ^ 2) L (zdistD d L a) hγ he hg2 (by omega) hN2
    hA1 hA2
  have hεeq : lgEps d g t = (1 - t) / lgGam d g t := rfl
  rw [← hεeq] at h1 h2
  calc (lgGam d g t)⁻¹ * |∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) * f τ|
      ≤ (lgGam d g t)⁻¹ * (CK * (∫ τ in Ioi (0 : ℝ), lgIntegrand m cK (zdistD d L a : ℝ)
            (lgEps d g t) τ)
          + CG * ((L : ℝ) ^ m)⁻¹ * min (1 / lgEps d g t) ((L : ℝ) ^ 2 / cG)) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = CK * ((lgGam d g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), lgIntegrand m cK (zdistD d L a : ℝ)
            (lgEps d g t) τ)
          + CG * ((lgGam d g t)⁻¹ * (((L : ℝ) ^ m)⁻¹ * min (1 / lgEps d g t)
            ((L : ℝ) ^ 2 / cG))) := by ring
    _ ≤ CK * (CH * ((g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ p)⁻¹))
          + CG * (CT * ((g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ p)⁻¹)) := by
        gcongr
    _ = (CK * CH + CG * CT) * ((g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ p)⁻¹) := by ring

/-! ### The case `σ₁ = σ₂`: the shape `1_{a=0} + g² e^{-c|a|}` of `(prop:ThfadC_short)` -/

/-- The constant of the `σ₁ = σ₂` bulk reduction. -/
private noncomputable def pu_KS (Λ cs : ℝ) (q : ℕ) : ℝ :=
  3 ^ q * (Λ ^ 2 + 1) + Λ ^ 2 * (Λ ^ 2 + 1) * Real.exp (2 * cs) *
    ((q.factorial : ℝ) * (2 / cs) ^ q * Real.exp (cs / 2))

/-- `pu_KS` is positive. -/
private lemma pu_KS_pos {Λ cs : ℝ} (hΛ : 0 < Λ) (hcs : 0 < cs) (q : ℕ) : 0 < pu_KS Λ cs q := by
  unfold pu_KS; positivity

/-- One term of the `σ₁ = σ₂` reduction: `ι + g² e^{-c|x|} ≤ K (g² + e)⁻¹ (n + 1)^{-q}` when
`n ≤ |x| + 2`, `ι ≤ 1` and `ι ≠ 0 → |x| = 0` (`g² ≤ Λ² (Λ² + 1) (g² + e)⁻¹`,
`1 ≤ (Λ² + 1)/(g² + e)`, `e^{-c(n-2)} ≤ e^{2c} M_q (n + 1)^{-q}`). -/
private lemma pu_S_bound {Λ cs g e : ℝ} (hcs : 0 < cs) (hg : 0 < g) (hgΛ : g ≤ Λ) (he : 0 < e)
    (he1 : e ≤ 1) (q : ℕ) (n nx : ℕ) (hn : n ≤ nx + 2) (ι : ℝ) (hι1 : ι ≤ 1)
    (hι : ι ≠ 0 → nx = 0) :
    ι + g ^ 2 * Real.exp (-cs * (nx : ℝ))
      ≤ pu_KS Λ cs q * ((g ^ 2 + e)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹) := by
  have hg2e : 0 < g ^ 2 + e := by positivity
  have hn1q : 0 < ((n : ℝ) + 1) ^ q := by positivity
  have hTg : 0 ≤ (g ^ 2 + e)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹ := by positivity
  have hg2L : g ^ 2 ≤ Λ ^ 2 := by nlinarith
  have hsum : g ^ 2 + e ≤ Λ ^ 2 + 1 := by linarith
  set Mq : ℝ := (q.factorial : ℝ) * (2 / cs) ^ q * Real.exp (cs / 2) with hMq
  have hMq0 : 0 < Mq := by positivity
  -- (i) the indicator
  have hind : ι ≤ 3 ^ q * (Λ ^ 2 + 1) * ((g ^ 2 + e)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹) := by
    by_cases h0 : ι = 0
    · rw [h0]
      have : 0 ≤ Λ ^ 2 + 1 := by positivity
      positivity
    · have hnx := hι h0
      have hn2' : (n : ℝ) + 1 ≤ 3 := by exact_mod_cast (by omega : n + 1 ≤ 3)
      have h1 : ((n : ℝ) + 1) ^ q ≤ 3 ^ q := pow_le_pow_left₀ (by positivity) hn2' q
      have h2 : (Λ ^ 2 + 1)⁻¹ ≤ (g ^ 2 + e)⁻¹ := inv_anti₀ hg2e hsum
      have h3 : ((3 : ℝ) ^ q)⁻¹ ≤ (((n : ℝ) + 1) ^ q)⁻¹ := inv_anti₀ hn1q h1
      calc ι ≤ 1 := hι1
        _ = 3 ^ q * (Λ ^ 2 + 1) * ((Λ ^ 2 + 1)⁻¹ * ((3 : ℝ) ^ q)⁻¹) := by
            have : (Λ ^ 2 + 1) ≠ 0 := by positivity
            field_simp
        _ ≤ 3 ^ q * (Λ ^ 2 + 1) * ((g ^ 2 + e)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹) := by gcongr
  -- (ii) the exponential
  have hexp : Real.exp (-cs * (nx : ℝ)) ≤ Real.exp (2 * cs) * (Mq * (((n : ℝ) + 1) ^ q)⁻¹) := by
    have h1 : -cs * (nx : ℝ) ≤ 2 * cs + -cs * (n : ℝ) := by
      have : (n : ℝ) ≤ nx + 2 := by exact_mod_cast hn
      nlinarith
    calc Real.exp (-cs * (nx : ℝ)) ≤ Real.exp (2 * cs + -cs * (n : ℝ)) := Real.exp_le_exp.mpr h1
      _ = Real.exp (2 * cs) * Real.exp (-cs * (n : ℝ)) := Real.exp_add _ _
      _ ≤ Real.exp (2 * cs) * (Mq * (((n : ℝ) + 1) ^ q)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          have := pu_pow_exp_le hcs q (Nat.cast_nonneg n)
          rw [← div_eq_mul_inv, le_div_iff₀ hn1q]
          linarith [mul_comm (((n : ℝ) + 1) ^ q) (Real.exp (-cs * (n : ℝ)))]
  have hg2' : g ^ 2 ≤ Λ ^ 2 * (Λ ^ 2 + 1) * (g ^ 2 + e)⁻¹ := by
    have h1 : g ^ 2 * (g ^ 2 + e) ≤ Λ ^ 2 * (Λ ^ 2 + 1) := by nlinarith [sq_nonneg g]
    calc g ^ 2 = g ^ 2 * (g ^ 2 + e) * (g ^ 2 + e)⁻¹ := by field_simp
      _ ≤ Λ ^ 2 * (Λ ^ 2 + 1) * (g ^ 2 + e)⁻¹ := by gcongr
  have hmain : g ^ 2 * Real.exp (-cs * (nx : ℝ))
      ≤ Λ ^ 2 * (Λ ^ 2 + 1) * Real.exp (2 * cs) * Mq * ((g ^ 2 + e)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹) := by
    calc g ^ 2 * Real.exp (-cs * (nx : ℝ))
        ≤ (Λ ^ 2 * (Λ ^ 2 + 1) * (g ^ 2 + e)⁻¹) *
            (Real.exp (2 * cs) * (Mq * (((n : ℝ) + 1) ^ q)⁻¹)) :=
          mul_le_mul hg2' hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  unfold pu_KS
  rw [← hMq]
  nlinarith [hind, hmain]

/-- `pu_S_bound` at `x = a + u`, `|u| ≤ 2`, with `ι = 1_{x = 0}`. -/
private lemma pu_S_point {d L : ℕ} [NeZero L] {Λ cs g e : ℝ} (hcs : 0 < cs) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (he : 0 < e) (he1 : e ≤ 1) (q : ℕ) (a u x : Zd d L) (hx : x = a + u)
    (hu : zdistD d L u ≤ 2) :
    (if x = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-cs * (zdistD d L x : ℝ))
      ≤ pu_KS Λ cs q * ((g ^ 2 + e)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ q)⁻¹) := by
  have hn : zdistD d L a ≤ zdistD d L x + 2 := by
    have := pu_shift a u
    rw [← hx] at this
    omega
  refine pu_S_bound hcs hg hgΛ he he1 q (zdistD d L a) (zdistD d L x) hn _ ?_ ?_
  · split_ifs <;> norm_num
  · intro h
    have hx0 : x = 0 := by
      by_contra hne
      exact h (by simp [hne])
    rw [hx0, zdistD_zero]

/-! ### The case `t = 0`, `Θ_0 = 1` -/

/-- `Θ_0 = 1`. -/
private lemma pu_Theta_zero (d L : ℕ) [NeZero L] (g : ℝ) : Theta d L g 0 = 1 := by
  simp [Theta]

/-- The entries of the identity matrix have norm `≤ 1`. -/
private lemma pu_one_norm_le {d L : ℕ} (x : Zd d L) :
    ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 x‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-- The off-diagonal entries of the identity matrix vanish. -/
private lemma pu_one_eq_zero {d L : ℕ} {x : Zd d L} (hx : x ≠ 0) :
    (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 x = 0 := by
  simp [Ne.symm hx]

/-- `t = 0`: a quantity `D ≤ 4`, vanishing for `n > 2`, is
`≤ 4 (Λ² + 1) 3^d (g² + 1)⁻¹ (n + 1)^{-q}`. -/
private lemma pu_t0_bound {Λ g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {d q : ℕ} (hq : q ≤ d) (n : ℕ)
    (D : ℝ) (hD4 : D ≤ 4) (hDn : 2 < n → D = 0) :
    D ≤ 4 * (Λ ^ 2 + 1) * 3 ^ d * ((g ^ 2 + 1)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹) := by
  have hg2 : 0 < g ^ 2 + 1 := by positivity
  have hn1q : 0 < ((n : ℝ) + 1) ^ q := by positivity
  have hΛ0 : 0 < Λ := lt_of_lt_of_le hg hgΛ
  have hTg : 0 ≤ (g ^ 2 + 1)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹ := by positivity
  by_cases hn : n ≤ 2
  · have hn2' : (n : ℝ) + 1 ≤ 3 := by exact_mod_cast (by omega : n + 1 ≤ 3)
    have h1 : ((n : ℝ) + 1) ^ q ≤ 3 ^ d := by
      calc ((n : ℝ) + 1) ^ q ≤ 3 ^ q := pow_le_pow_left₀ (by positivity) hn2' q
        _ ≤ 3 ^ d := pow_le_pow_right₀ (by norm_num) hq
    have h2 : (Λ ^ 2 + 1)⁻¹ ≤ (g ^ 2 + 1)⁻¹ := inv_anti₀ hg2 (by nlinarith)
    have h3 : ((3 : ℝ) ^ d)⁻¹ ≤ (((n : ℝ) + 1) ^ q)⁻¹ := inv_anti₀ hn1q h1
    calc D ≤ 4 := hD4
      _ = 4 * (Λ ^ 2 + 1) * 3 ^ d * ((Λ ^ 2 + 1)⁻¹ * ((3 : ℝ) ^ d)⁻¹) := by
          have : (Λ ^ 2 + 1) ≠ 0 := by positivity
          field_simp
      _ ≤ 4 * (Λ ^ 2 + 1) * 3 ^ d * ((g ^ 2 + 1)⁻¹ * (((n : ℝ) + 1) ^ q)⁻¹) := by gcongr
  · rw [hDn (by omega)]
    positivity

/-- `σ₁ ≠ σ₂` and `‖m‖ = 1` give `m(σ₁) m(σ₂) = m m̄ = 1`. -/
private lemma pu_spin_ne {m : ℂ} (hm : ‖m‖ = 1) {σ₁ σ₂ : Bool} (h : σ₁ ≠ σ₂) :
    PropSpin m σ₁ * PropSpin m σ₂ = 1 := by
  have h1 : m * (starRingEnd ℂ) m = 1 := by
    rw [Complex.mul_conj', hm]; simp
  cases σ₁ <;> cases σ₂
  · exact absurd rfl h
  · simp only [PropSpin, Bool.false_eq_true, ite_false, ite_true]
    rw [mul_comm]; exact h1
  · simp only [PropSpin, ite_true, Bool.false_eq_true, ite_false]
    exact h1
  · exact absurd rfl h

/-- A point `x = a + u` with `|u| ≤ 2` is nonzero when `|a| > 2`. -/
private lemma pu_ne_zero {d L : ℕ} [NeZero L] (a u x : Zd d L) (hx : x = a + u)
    (hu : zdistD d L u ≤ 2) (hn : 2 < zdistD d L a) : x ≠ 0 := by
  intro h0
  have := pu_shift a u
  rw [← hx, h0, zdistD_zero] at this
  omega

/-- The four-term triangle inequality for the second difference. -/
private lemma pu_norm4 (A B C D : ℂ) : ‖A - B - C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  calc ‖A - B - C + D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_add_le _ _
    _ ≤ (‖A - B‖ + ‖C‖) + ‖D‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by gcongr; exact norm_sub_le _ _

/-! ### The pinned statements are proved -/

/-- **`PropUnit1` holds** for every `d`, `Λ`, `κ` (route H; the unit first difference, no loss). -/
theorem propUnit1_holds (d : ℕ) (Λ κ : ℝ) : PropUnit1 d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨CK, cK, hCK, hcK, hK⟩ := kProd_diff1_le d (by omega)
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := kProd_gap d (by omega)
  obtain ⟨Cs, hCs, cs, hcs, hS⟩ := prop5Short_holds d Λ κ hd hΛ hκ
  obtain ⟨CM, hCM, hM⟩ := pu_master d hΛ (m := d + 1) (p := d - 1) (by omega) (by omega)
    hCK hcK hCG hcG
  have hKS := pu_KS_pos hΛ hcs (d - 1)
  refine ⟨max CM (max (4 * (Λ ^ 2 + 1) * 3 ^ d) (2 * Cs * pu_KS Λ cs (d - 1))), ?_, ?_⟩
  · exact lt_max_of_lt_left hCM
  intro L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ a j
  have : NeZero L := ⟨by omega⟩
  have he : 0 < 1 - t := by linarith
  have hTg0 : 0 ≤ (g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by positivity
  rw [abs_of_pos he, mul_assoc]
  have hu1 : zdistD d L (Pi.single j (1 : ZMod L)) ≤ 2 :=
    (pu_zdistD_single_le d L j).trans (by omega)
  by_cases hσ : σ₁ = σ₂
  · -- `σ₁ = σ₂`: property `(prop:ThfadC_short)`
    subst hσ
    have h1 := hS L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ (a + Pi.single j 1)
    have h0 := hS L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ a
    have s1 := pu_S_point (e := 1 - t) hcs hg hgΛ he (by linarith) (d - 1) a (Pi.single j 1)
      (a + Pi.single j 1) rfl hu1
    have s0 := pu_S_point (e := 1 - t) hcs hg hgΛ he (by linarith) (d - 1) a 0 a (add_zero a).symm
      (by simp)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _) : 2 * Cs * pu_KS Λ cs (d - 1) ≤ _) hTg0)
    calc _ ≤ ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₁)) 0 (a + Pi.single j 1)‖
          + ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₁)) 0 a‖ := norm_sub_le _ _
      _ ≤ Cs * (pu_KS Λ cs (d - 1) * ((g ^ 2 + (1 - t))⁻¹
            * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹))
          + Cs * (pu_KS Λ cs (d - 1) * ((g ^ 2 + (1 - t))⁻¹
            * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹)) :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left s1 hCs.le))
            (h0.trans (mul_le_mul_of_nonneg_left s0 hCs.le))
      _ = _ := by ring
  · -- `σ₁ ≠ σ₂`: `μ = 1`
    have hμ := pu_spin_ne hm hσ
    rw [hμ, mul_one]
    rcases ht0.eq_or_lt with h0 | h0
    · -- `t = 0`
      subst h0
      simp only [Complex.ofReal_zero, pu_Theta_zero]
      refine le_trans ?_ (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _) : 4 * (Λ ^ 2 + 1) * 3 ^ d ≤ _) hTg0)
      have hT := pu_t0_bound (d := d) (q := d - 1) hg hgΛ (by omega) (zdistD d L a)
        ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 (a + Pi.single j 1)
          - (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 a‖ ?_ ?_
      · simpa using hT
      · have n1 := pu_one_norm_le (a + Pi.single j 1)
        have n0 := pu_one_norm_le a
        exact (norm_sub_le _ _).trans (by linarith)
      · intro hn
        have hx1 := pu_ne_zero a (Pi.single j 1) _ rfl hu1 hn
        have hx0 := pu_ne_zero a 0 a (add_zero a).symm (by simp) hn
        rw [pu_one_eq_zero hx1, pu_one_eq_zero hx0]
        simp
    · -- `0 < t`
      have hf : Continuous (fun τ : ℝ => kProd d L τ (a + Pi.single j 1) - kProd d L τ a) :=
        (pu_kProd_cont d L _).sub (pu_kProd_cont d L _)
      have hcast : (((d + 1 : ℕ) : ℝ)) = (d : ℝ) + 1 := by push_cast; ring
      have hhead : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
          |kProd d L τ (a + Pi.single j 1) - kProd d L τ a|
            ≤ CK * min 1 (τ ^ (-(((d + 1 : ℕ) : ℝ)) / 2)) *
              Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) := by
        intro τ hτ hτL
        rw [hcast]
        exact hK L τ hτ hτL a j
      have htail : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →
          |kProd d L τ (a + Pi.single j 1) - kProd d L τ a|
            ≤ CG * (((L : ℝ) ^ (d + 1))⁻¹) * Real.exp (-cG * τ / (L : ℝ) ^ 2) :=
        fun τ hτ => (hG L τ hτ a j j).2.1
      obtain ⟨-, hbd⟩ := hM L hL g hg hgΛ t h0 ht1 a _ hf hhead htail
      rw [pu_diff1_eq hL hg h0 ht1 a j]
      exact hbd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hTg0)

/-- **`PropUnit2` holds** for every `d`, `Λ`, `κ` (route H; the unit second differences, mixed and
same-direction, no loss). -/
theorem propUnit2_holds (d : ℕ) (Λ κ : ℝ) : PropUnit2 d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨CK, cK, hCK, hcK, hK⟩ := kProd_diff2_le d (by omega)
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := kProd_gap d (by omega)
  obtain ⟨Cs, hCs, cs, hcs, hS⟩ := prop5Short_holds d Λ κ hd hΛ hκ
  obtain ⟨CM, hCM, hM⟩ := pu_master d hΛ (m := d + 2) (p := d) (by omega) (by omega)
    hCK hcK hCG hcG
  have hKS := pu_KS_pos hΛ hcs d
  refine ⟨max CM (max (4 * (Λ ^ 2 + 1) * 3 ^ d) (4 * Cs * pu_KS Λ cs d)), ?_, ?_⟩
  · exact lt_max_of_lt_left hCM
  intro L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ a i j
  have : NeZero L := ⟨by omega⟩
  have he : 0 < 1 - t := by linarith
  have hTg0 : 0 ≤ (g ^ 2 + (1 - t))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by positivity
  rw [abs_of_pos he, mul_assoc]
  have hui : zdistD d L (Pi.single i (1 : ZMod L)) ≤ 1 := pu_zdistD_single_le d L i
  have huj : zdistD d L (Pi.single j (1 : ZMod L)) ≤ 1 := pu_zdistD_single_le d L j
  have huij : zdistD d L (Pi.single i (1 : ZMod L) + Pi.single j 1) ≤ 2 := by
    have := zdistD_add_le d L (Pi.single i (1 : ZMod L)) (Pi.single j 1)
    omega
  by_cases hσ : σ₁ = σ₂
  · -- `σ₁ = σ₂`: property `(prop:ThfadC_short)`
    subst hσ
    have h1 := hS L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ (a + Pi.single i 1 + Pi.single j 1)
    have h2 := hS L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ (a + Pi.single i 1)
    have h3 := hS L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ (a + Pi.single j 1)
    have h4 := hS L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ a
    have s1 := pu_S_point (e := 1 - t) hcs hg hgΛ he (by linarith) d a
      (Pi.single i 1 + Pi.single j 1) (a + Pi.single i 1 + Pi.single j 1) (add_assoc _ _ _) huij
    have s2 := pu_S_point (e := 1 - t) hcs hg hgΛ he (by linarith) d a (Pi.single i 1)
      (a + Pi.single i 1) rfl (by omega)
    have s3 := pu_S_point (e := 1 - t) hcs hg hgΛ he (by linarith) d a (Pi.single j 1)
      (a + Pi.single j 1) rfl (by omega)
    have s4 := pu_S_point (e := 1 - t) hcs hg hgΛ he (by linarith) d a 0 a (add_zero a).symm
      (by simp)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _) : 4 * Cs * pu_KS Λ cs d ≤ _) hTg0)
    refine (pu_norm4 _ _ _ _).trans ?_
    have b1 := h1.trans (mul_le_mul_of_nonneg_left s1 hCs.le)
    have b2 := h2.trans (mul_le_mul_of_nonneg_left s2 hCs.le)
    have b3 := h3.trans (mul_le_mul_of_nonneg_left s3 hCs.le)
    have b4 := h4.trans (mul_le_mul_of_nonneg_left s4 hCs.le)
    linarith
  · -- `σ₁ ≠ σ₂`: `μ = 1`
    have hμ := pu_spin_ne hm hσ
    rw [hμ, mul_one]
    rcases ht0.eq_or_lt with h0 | h0
    · -- `t = 0`
      subst h0
      simp only [Complex.ofReal_zero, pu_Theta_zero]
      refine le_trans ?_ (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _) : 4 * (Λ ^ 2 + 1) * 3 ^ d ≤ _) hTg0)
      have hT := pu_t0_bound (d := d) (q := d) hg hgΛ le_rfl (zdistD d L a)
        ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 (a + Pi.single i 1 + Pi.single j 1)
          - (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 (a + Pi.single i 1)
          - (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 (a + Pi.single j 1)
          + (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 a‖ ?_ ?_
      · simpa using hT
      · have n1 := pu_one_norm_le (a + Pi.single i 1 + Pi.single j 1)
        have n2 := pu_one_norm_le (a + Pi.single i 1)
        have n3 := pu_one_norm_le (a + Pi.single j 1)
        have n4 := pu_one_norm_le a
        exact (pu_norm4 _ _ _ _).trans (by linarith)
      · intro hn
        have hx1 := pu_ne_zero a (Pi.single i 1 + Pi.single j 1) _ (add_assoc _ _ _) huij hn
        have hx2 := pu_ne_zero a (Pi.single i 1) _ rfl (by omega) hn
        have hx3 := pu_ne_zero a (Pi.single j 1) _ rfl (by omega) hn
        have hx4 := pu_ne_zero a 0 a (add_zero a).symm (by simp) hn
        rw [pu_one_eq_zero hx1, pu_one_eq_zero hx2, pu_one_eq_zero hx3, pu_one_eq_zero hx4]
        simp
    · -- `0 < t`
      have hf : Continuous (fun τ : ℝ => kProd d L τ (a + Pi.single i 1 + Pi.single j 1)
          - kProd d L τ (a + Pi.single i 1) - kProd d L τ (a + Pi.single j 1)
          + kProd d L τ a) :=
        (((pu_kProd_cont d L _).sub (pu_kProd_cont d L _)).sub (pu_kProd_cont d L _)).add
          (pu_kProd_cont d L _)
      have hcast : (((d + 2 : ℕ) : ℝ)) = (d : ℝ) + 2 := by push_cast; ring
      have hhead : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
          |kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
              - kProd d L τ (a + Pi.single j 1) + kProd d L τ a|
            ≤ CK * min 1 (τ ^ (-(((d + 2 : ℕ) : ℝ)) / 2)) *
              Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) := by
        intro τ hτ hτL
        rw [hcast]
        exact hK L τ hτ hτL a i j
      have htail : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →
          |kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
              - kProd d L τ (a + Pi.single j 1) + kProd d L τ a|
            ≤ CG * (((L : ℝ) ^ (d + 2))⁻¹) * Real.exp (-cG * τ / (L : ℝ) ^ 2) :=
        fun τ hτ => (hG L τ hτ a i j).2.2
      obtain ⟨-, hbd⟩ := hM L hL g hg hgΛ t h0 ht1 a _ hf hhead htail
      rw [pu_diff2_eq hL hg h0 ht1 a i j]
      exact hbd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hTg0)

/-! ### Compiled nonempty instances

Each theorem applied at `d = 3`, `Λ = 1`, `κ = 1/2` (every deterministic hypothesis discharged) at
`L = 5`, `g = 1/2`, `t = 9/10`, `m = I` (`‖I‖ = 1`, `1/2 ≤ Im I = 1`), `σ₁ = true`, `σ₂ = false`
(`μ = I · conj I = 1`), `a = 0`, `i = j = 0`; and, for the other branches of the proof, at
`σ₁ = σ₂ = true` (`μ = I² = -1`, the bulk), at `t = 0`, and at `a = (1, 0, 0) ≠ 0`
with mixed directions `(i, j) = (0, 2)`. -/

example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((0 : Zd 3 5) + Pi.single 0 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (0 : Zd 3 5)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
        * (((zdistD 3 5 (0 : Zd 3 5) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := propUnit1_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false 0 0⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((0 : Zd 3 5) + Pi.single 0 1 + Pi.single 0 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((0 : Zd 3 5) + Pi.single 0 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((0 : Zd 3 5) + Pi.single 0 1)
        + Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (0 : Zd 3 5)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
        * (((zdistD 3 5 (0 : Zd 3 5) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := propUnit2_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false 0 0 0⟩

/-- The bulk branch `σ₁ = σ₂`, at `a = (1, 0, 0)`, `j = 2`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
          0 ((![1, 0, 0] : Zd 3 5) + Pi.single 2 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
          0 (![1, 0, 0] : Zd 3 5)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
        * (((zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := propUnit1_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true true ![1, 0, 0] 2⟩

/-- The `t = 0` branch (`Θ_0 = 1`), at `a = (-1, 0, 0)`, `j = 0`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 5 (1 / 2)
          (((0 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((![-1, 0, 0] : Zd 3 5) + Pi.single 0 1)
        - Theta 3 5 (1 / 2)
          (((0 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (![-1, 0, 0] : Zd 3 5)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 0|)⁻¹
        * (((zdistD 3 5 (![-1, 0, 0] : Zd 3 5) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := propUnit1_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 0 le_rfl
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false ![-1, 0, 0] 0⟩

/-- Mixed second difference `(i, j) = (0, 2)`, at `a = (1, 0, 0)`, `σ₁ = σ₂ = true`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
          0 ((![1, 0, 0] : Zd 3 5) + Pi.single 0 1 + Pi.single 2 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
          0 ((![1, 0, 0] : Zd 3 5) + Pi.single 0 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
          0 ((![1, 0, 0] : Zd 3 5) + Pi.single 2 1)
        + Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
          0 (![1, 0, 0] : Zd 3 5)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
        * (((zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := propUnit2_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true true ![1, 0, 0] 0 2⟩

end RBM
