/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.HeatProduct
import RBM3D.Propagator.LaplaceGauss
import RBM3D.Propagator.Pins
import RBM3D.Propagator.Prop5Short
import RBM3D.Propagator.Props4

/-!
# Properties 5 and 8 of `lem_propTH` (proved): `(prop:ThfadC)` and `(prop:ThfadC0)`

`prop5Decay_holds : ∀ d Λ, Prop5Decay d Λ` and `prop8ZeroMode_holds : ∀ d Λ κ, Prop8ZeroMode d Λ κ`
(route H, ticket T2023; Fable review `docs/claude-team/fable/2026-10-02-routeH.md` §1 F5, F7).

Notation: `e = 1 - t`, `γ = lgGam d g t`, `ε = lgEps d g t = e / γ`, `n = zdistD d L a`,
`ℓ = ellT L g t`, `T = L²`, `K_τ = kProd d L τ`.

* **Reduction** (property 4): `‖Θ_{tμ}(0,a)‖ ≤ Re Θ_t(0,a)` for `‖μ‖ = 1`; `t = 0` is `Θ = 1`.
* **Representation** (`Theta_eq_laplace_prod`, `τ = γ s`): for `0 < t < 1`,
  `Θ_t(0,a) = γ⁻¹ ∫₀^∞ e^{-ετ} K_τ(a) dτ`, split at `τ = T`.
* **Head** `(0, T]`: `kProd_le` and the Laplace–Gauss bounds `lg_bulk` (`n ≥ 1`), `lg_zero`
  (`n = 0`).
* **Tail** `(T, ∞)`: `K_τ ≤ (1 + C) L^{-d}` (`kProd_gap`) and `∫_T^∞ e^{-ετ} = e^{-εT}/ε`.
* **Regimes by `ε`** (not by `e ≷ g²`; Fable F5): `ε ≥ 1`, `L⁻² ≤ ε < 1`, `ε < L⁻²`, `n = 0`;
  `lg_convA` (`Λ` enters here), `lg_convB`, `lg_convC` convert `ε`, `γ`, `ℓ`.
* **Property 8, `σ₁ ≠ σ₂`**: `Θ̊_t(0,a) = γ⁻¹ ∫ e^{-ετ} (K_τ(a) - L^{-d}) dτ` with `e^{-ετ}` kept on
  the `L^{-d}` piece (Fable F5 (d)); **`σ₁ = σ₂`**: `prop5Short_holds` and `|1 - tμ| ≥ κ²`.

The constants depend on `(d, Λ)` (resp. `(d, Λ, κ)`) only, exactly as the pins quantify.
-/

open MeasureTheory Set

namespace RBM

open Heat

/-! ### The product kernel as a function of `τ`: continuity, `0 ≤ K ≤ 1`, integrability -/

private lemma p5h_hkT_continuous (L : ℕ) [NeZero L] (x : ZMod L) :
    Continuous (fun τ : ℝ => hkT L τ x) := by
  unfold hkT
  fun_prop

private lemma p5h_kProd_continuous (d L : ℕ) [NeZero L] (a : Zd d L) :
    Continuous (fun τ : ℝ => kProd d L τ a) := by
  unfold kProd
  exact continuous_finsetProd _ fun j _ => p5h_hkT_continuous L (a j)

private lemma p5h_kProd_nonneg_le_one (d L : ℕ) [NeZero L] {τ : ℝ} (hτ : 0 ≤ τ) (a : Zd d L) :
    0 ≤ kProd d L τ a ∧ kProd d L τ a ≤ 1 := by
  obtain ⟨h0, h1⟩ := hkT_mass L τ hτ
  have hle : ∀ x : ZMod L, hkT L τ x ≤ 1 := fun x => by
    calc hkT L τ x ≤ ∑ y : ZMod L, hkT L τ y :=
          Finset.single_le_sum (f := fun y => hkT L τ y) (fun y _ => h0 y) (Finset.mem_univ x)
      _ = 1 := h1
  exact ⟨Finset.prod_nonneg (fun j _ => h0 _), Finset.prod_le_one₀ (fun j _ => h0 _)
    (fun j _ => hle _)⟩

/-- `e^{-ετ} K_τ(a)` is integrable on `(0, ∞)` for `ε > 0`. -/
private lemma p5h_F_integrable (d L : ℕ) [NeZero L] {ε : ℝ} (hε : 0 < ε) (a : Zd d L) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kProd d L τ a) (Ioi 0) := by
  have hg : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hc := p5h_kProd_continuous d L a
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => Real.exp (-ε * τ) * kProd d L τ a)
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-ε * τ) * kProd d L τ a).aestronglyMeasurable
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hτ' : 0 ≤ τ := le_of_lt hτ
  obtain ⟨h0, h1⟩ := p5h_kProd_nonneg_le_one d L hτ' a
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h0)]
  calc Real.exp (-ε * τ) * kProd d L τ a ≤ Real.exp (-ε * τ) * 1 :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := mul_one _

/-! ### `γ`, `ε` and the Laplace representation in the variable `τ = γ s` -/

private lemma p5h_gam_pos (d : ℕ) {g t : ℝ} (hg : 0 < g) (ht : 0 < t) : 0 < lgGam d g t := by
  unfold lgGam; positivity

private lemma p5h_eps_pos (d : ℕ) {g t : ℝ} (hg : 0 < g) (ht : 0 < t) (ht1 : t < 1) :
    0 < lgEps d g t := by
  unfold lgEps
  exact div_pos (by linarith) (p5h_gam_pos d hg ht)

private lemma p5h_gam_mul_eps (d : ℕ) {g t : ℝ} (hg : 0 < g) (ht : 0 < t) :
    lgGam d g t * lgEps d g t = 1 - t := by
  have := (p5h_gam_pos d hg ht).ne'
  unfold lgEps
  field_simp

/-- `Θ_t(0,a) = γ⁻¹ ∫₀^∞ e^{-ετ} K_τ(a) dτ`: `Theta_eq_laplace_prod` and `τ = γ s`. -/
private lemma p5h_theta_eq (d L : ℕ) (hL : 3 ≤ L) (g t : ℝ) (hg : 0 < g) (ht0 : 0 < t)
    (ht1 : t < 1) (a : Zd d L) :
    haveI : NeZero L := ⟨by omega⟩
    Theta d L g (t : ℂ) 0 a =
      (((lgGam d g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) * kProd d L τ a
        : ℝ) : ℂ) := by
  have : NeZero L := ⟨by omega⟩
  rw [Theta_eq_laplace_prod d L hL g t hg ht0.le ht1 a]
  congr 1
  have hγ := p5h_gam_pos d hg ht0
  have key := integral_comp_mul_left_Ioi
    (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ) * kProd d L τ a) 0 hγ
  rw [mul_zero] at key
  simp only [smul_eq_mul] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  have h1 : -(lgEps d g t) * (lgGam d g t * s) = -(1 - t) * s := by
    rw [← p5h_gam_mul_eps d hg ht0]; ring
  rw [h1]

/-! ### Elementary real inequalities -/

/-- `n^{-(d-2)}` as a real power. -/
private lemma p5h_rpow_eq {d : ℕ} (hd : 2 ≤ d) {n : ℝ} (hn : 0 ≤ n) :
    n ^ (-((d : ℝ) - 2)) = (n ^ (d - 2))⁻¹ := by
  have : -((d : ℝ) - 2) = -((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd]; push_cast; ring
  rw [this, Real.rpow_neg hn, Real.rpow_natCast]

private lemma p5h_inv_pow_le {n : ℝ} (hn : 1 ≤ n) (k : ℕ) :
    (n ^ k)⁻¹ ≤ 2 ^ k * ((n + 1) ^ k)⁻¹ := by
  have h1 : (n + 1) ^ k ≤ (2 * n) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
  rw [mul_pow] at h1
  have hn0 : 0 < n ^ k := by positivity
  have hn1 : 0 < (n + 1) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hn1, inv_mul_le_iff₀ hn0]
  linarith

/-- `(n+1)^k e^{-bn} ≤ k! b^{-k} e^b`. -/
private lemma p5h_poly_exp_le {b : ℝ} (hb : 0 < b) (k : ℕ) {n : ℝ} (hn : 0 ≤ n) :
    (n + 1) ^ k * Real.exp (-b * n) ≤ (k.factorial : ℝ) * (1 / b) ^ k * Real.exp b := by
  have h := Real.pow_div_factorial_le_exp (b * (n + 1)) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  have hb' : (0 : ℝ) < b ^ k := by positivity
  have h2 : (n + 1) ^ k ≤ (k.factorial : ℝ) * (1 / b) ^ k * Real.exp (b * (n + 1)) := by
    have : (1 / b) ^ k * b ^ k = 1 := by rw [← mul_pow]; simp [hb.ne']
    calc (n + 1) ^ k = (1 / b) ^ k * (b ^ k * (n + 1) ^ k) := by
          rw [← mul_assoc, this, one_mul]
      _ ≤ (1 / b) ^ k * (Real.exp (b * (n + 1)) * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  have h3 : Real.exp (b * (n + 1)) * Real.exp (-b * n) = Real.exp b := by
    rw [← Real.exp_add]; congr 1; ring
  calc (n + 1) ^ k * Real.exp (-b * n)
      ≤ ((k.factorial : ℝ) * (1 / b) ^ k * Real.exp (b * (n + 1))) * Real.exp (-b * n) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (k.factorial : ℝ) * (1 / b) ^ k * (Real.exp (b * (n + 1)) * Real.exp (-b * n)) := by ring
    _ = _ := by rw [h3]

/-! ### Torus distances -/

private lemma p5h_zdist_le (L : ℕ) [NeZero L] (u : ZMod L) : 2 * zdist L u ≤ L := by
  have := ZMod.val_lt u
  unfold zdist
  omega

/-- `|a| ≤ dL/2`: every torus `ℓ¹` distance. -/
private lemma p5h_zdistD_le (d L : ℕ) [NeZero L] (a : Zd d L) :
    (zdistD d L a : ℝ) ≤ (d : ℝ) * (L : ℝ) / 2 := by
  have h : 2 * zdistD d L a ≤ d * L := by
    unfold zdistD
    calc 2 * ∑ i, zdist L (a i) = ∑ i, 2 * zdist L (a i) := by rw [Finset.mul_sum]
      _ ≤ ∑ _i : Fin d, L := Finset.sum_le_sum fun i _ => p5h_zdist_le L (a i)
      _ = d * L := by simp
  have h' : (2 : ℝ) * (zdistD d L a : ℝ) ≤ (d : ℝ) * (L : ℝ) := by exact_mod_cast h
  linarith

/-- `L^{-k} ≤ (d/2 + 1)^k (|a| + 1)^{-k}`, since `|a| + 1 ≤ (d/2 + 1) L`. -/
private lemma p5h_Linv_le (d L : ℕ) [NeZero L] (a : Zd d L) (k : ℕ) :
    ((L : ℝ) ^ k)⁻¹ ≤ ((d : ℝ) / 2 + 1) ^ k * ((((zdistD d L a : ℝ) + 1) ^ k)⁻¹) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hn := p5h_zdistD_le d L a
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (zdistD d L a : ℝ) + 1 ≤ ((d : ℝ) / 2 + 1) * L := by nlinarith
  have h2 : ((zdistD d L a : ℝ) + 1) ^ k ≤ (((d : ℝ) / 2 + 1) * L) ^ k :=
    pow_le_pow_left₀ (by positivity) h1 k
  rw [mul_pow] at h2
  have hLk : 0 < (L : ℝ) ^ k := by positivity
  have hnk : 0 < ((zdistD d L a : ℝ) + 1) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hnk, inv_mul_le_iff₀ hLk]
  linarith

private lemma p5h_Linv_d_le (d L : ℕ) [NeZero L] (hd : 2 ≤ d) :
    ((L : ℝ) ^ d)⁻¹ ≤ ((L : ℝ) ^ (d - 2))⁻¹ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega))

/-! ### The exponential factors: regimes of `ε` against `L⁻²` -/

/-- `e^{-b n √ε} ≤ e^{bd/2} e^{-b n/ℓ}` for `0 ≤ n ≤ dL/2`: if `ε ≥ L⁻²` then `ℓ⁻¹ ≤ √ε`
(`lg_convB`), otherwise `ℓ = L` and `n/ℓ ≤ d/2`. -/
private lemma p5h_exp_bulk (d L : ℕ) (hL : 1 ≤ L) {ε ℓ n b : ℝ} (hb : 0 ≤ b)
    (hn : 0 ≤ n) (hnL : n ≤ (d : ℝ) * L / 2)
    (hB1 : ((L : ℝ)⁻¹) ^ 2 ≤ ε → ℓ⁻¹ ≤ Real.sqrt ε) (hB2 : ε < ((L : ℝ)⁻¹) ^ 2 → ℓ = L) :
    Real.exp (-b * n * Real.sqrt ε) ≤ Real.exp (b * d / 2) * Real.exp (-b * n / ℓ) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have h1 : (1 : ℝ) ≤ Real.exp (b * d / 2) := Real.one_le_exp (by positivity)
  rcases le_or_gt (((L : ℝ)⁻¹) ^ 2) ε with h | h
  · have hs := hB1 h
    have hbn : 0 ≤ b * n := mul_nonneg hb hn
    have : -b * n * Real.sqrt ε ≤ -b * n / ℓ := by
      have h2 : b * n * ℓ⁻¹ ≤ b * n * Real.sqrt ε := mul_le_mul_of_nonneg_left hs hbn
      rw [div_eq_mul_inv]
      nlinarith
    calc Real.exp (-b * n * Real.sqrt ε) ≤ Real.exp (-b * n / ℓ) := Real.exp_le_exp.mpr this
      _ ≤ Real.exp (b * d / 2) * Real.exp (-b * n / ℓ) :=
          le_mul_of_one_le_left (Real.exp_pos _).le h1
  · have hℓL := hB2 h
    have hbn : 0 ≤ b * n := mul_nonneg hb hn
    have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
    have h2 : Real.exp (-b * n * Real.sqrt ε) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hbn hs0]
    have h4 : n / (L : ℝ) ≤ (d : ℝ) / 2 := by rw [div_le_iff₀ hL']; linarith
    have h5 : -b * n / (L : ℝ) = -(b * (n / L)) := by ring
    have h3 : -(b * d / 2) ≤ -b * n / ℓ := by
      rw [hℓL, h5]
      nlinarith [mul_le_mul_of_nonneg_left h4 hb]
    calc Real.exp (-b * n * Real.sqrt ε) ≤ 1 := h2
      _ = Real.exp (b * d / 2) * Real.exp (-(b * d / 2)) := by
          rw [← Real.exp_add]; simp
      _ ≤ Real.exp (b * d / 2) * Real.exp (-b * n / ℓ) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3) (Real.exp_pos _).le

/-- The zero-mode exponential `e^{-εL²} ≤ e^{cd/2} e^{-c n/ℓ}` for `c d ≤ 2` (Fable F5 (c)): if
`ε ≥ L⁻²` then `n/ℓ ≤ (d/2) ε L²` (`lg_convC`), otherwise `ℓ = L`. -/
private lemma p5h_exp_zero (d L : ℕ) (hL : 1 ≤ L) {ε ℓ n c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hcd : c * d ≤ 2) (hnL : n ≤ (d : ℝ) * L / 2)
    (hB2 : ε < ((L : ℝ)⁻¹) ^ 2 → ℓ = L)
    (hC : ((L : ℝ)⁻¹) ^ 2 ≤ ε → n / ℓ ≤ (d : ℝ) / 2 * (ε * (L : ℝ) ^ 2)) :
    Real.exp (-(ε * (L : ℝ) ^ 2)) ≤ Real.exp (c * d / 2) * Real.exp (-c * n / ℓ) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have h1 : (1 : ℝ) ≤ Real.exp (c * d / 2) := Real.one_le_exp (by positivity)
  rcases le_or_gt (((L : ℝ)⁻¹) ^ 2) ε with h | h
  · have hh := hC h
    have hεL : 0 ≤ ε * (L : ℝ) ^ 2 := by positivity
    have h2 : c * (n / ℓ) ≤ ε * (L : ℝ) ^ 2 := by
      calc c * (n / ℓ) ≤ c * ((d : ℝ) / 2 * (ε * (L : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hh hc
        _ = (c * d / 2) * (ε * (L : ℝ) ^ 2) := by ring
        _ ≤ 1 * (ε * (L : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ hεL; linarith
        _ = _ := one_mul _
    have h3 : -(ε * (L : ℝ) ^ 2) ≤ -c * n / ℓ := by
      have : -c * n / ℓ = -(c * (n / ℓ)) := by ring
      rw [this]; linarith
    calc Real.exp (-(ε * (L : ℝ) ^ 2)) ≤ Real.exp (-c * n / ℓ) := Real.exp_le_exp.mpr h3
      _ ≤ Real.exp (c * d / 2) * Real.exp (-c * n / ℓ) :=
          le_mul_of_one_le_left (Real.exp_pos _).le h1
  · have hℓL := hB2 h
    have h2 : Real.exp (-(ε * (L : ℝ) ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ε * (L : ℝ) ^ 2 := by positivity
      linarith
    have h4 : n / (L : ℝ) ≤ (d : ℝ) / 2 := by rw [div_le_iff₀ hL']; linarith
    have h5 : -c * n / (L : ℝ) = -(c * (n / L)) := by ring
    have h3 : -(c * d / 2) ≤ -c * n / ℓ := by
      rw [hℓL, h5]
      nlinarith [mul_le_mul_of_nonneg_left h4 hc]
    calc Real.exp (-(ε * (L : ℝ) ^ 2)) ≤ 1 := h2
      _ = Real.exp (c * d / 2) * Real.exp (-(c * d / 2)) := by
          rw [← Real.exp_add]; simp
      _ ≤ Real.exp (c * d / 2) * Real.exp (-c * n / ℓ) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3) (Real.exp_pos _).le

/-! ### The head, regime by regime (pure real algebra)

`J` stands for `∫₀^∞ lgIntegrand d c_K n ε`; `X = (g² + e)⁻¹`, `k = d - 2`. -/

/-- `n = 0`: `J ≤ C₀` (`ε < 1`) or `J ≤ 1/ε` (`ε ≥ 1`); both give `≲ X`. -/
private lemma p5h_shape_zero {γ ε e g J C₀ CA : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (he : γ * ε = e)
    (hC₀ : 0 ≤ C₀) (hCA : 0 ≤ CA)
    (hA1 : 1 ≤ ε → 1 / e ≤ CA / (g ^ 2 + e)) (hA2 : ε < 1 → 1 / γ ≤ CA / (g ^ 2 + e))
    (hJ1 : J ≤ C₀) (hJ2 : J ≤ 1 / ε) :
    γ⁻¹ * J ≤ CA * (C₀ + 1) * (g ^ 2 + e)⁻¹ := by
  have he0 : 0 < e := by rw [← he]; positivity
  have hX : 0 ≤ (g ^ 2 + e)⁻¹ := inv_nonneg.mpr (by positivity)
  have hγ' : 0 ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
  rcases lt_or_ge ε 1 with h | h
  · have h1 := hA2 h
    rw [one_div, div_eq_mul_inv] at h1
    calc γ⁻¹ * J ≤ γ⁻¹ * C₀ := mul_le_mul_of_nonneg_left hJ1 hγ'
      _ = C₀ * γ⁻¹ := by ring
      _ ≤ C₀ * (CA * (g ^ 2 + e)⁻¹) := mul_le_mul_of_nonneg_left h1 hC₀
      _ ≤ CA * (C₀ + 1) * (g ^ 2 + e)⁻¹ := by
          have : 0 ≤ CA * (g ^ 2 + e)⁻¹ := mul_nonneg hCA hX
          nlinarith
  · have h1 := hA1 h
    rw [one_div, div_eq_mul_inv] at h1
    have h2 : γ⁻¹ * (1 / ε) = e⁻¹ := by
      rw [← he]; field_simp
    calc γ⁻¹ * J ≤ γ⁻¹ * (1 / ε) := mul_le_mul_of_nonneg_left hJ2 hγ'
      _ = e⁻¹ := h2
      _ ≤ CA * (g ^ 2 + e)⁻¹ := h1
      _ ≤ CA * (C₀ + 1) * (g ^ 2 + e)⁻¹ := by
          have : 0 ≤ CA * (g ^ 2 + e)⁻¹ := mul_nonneg hCA hX
          nlinarith

/-- `n ≥ 1`, `ε ≥ 1`: `J ≤ (2/ε) e^{-c'n}`; the polynomial factor is paid by half the exponent. -/
private lemma p5h_shape_big {γ ε e g J CA c' c ℓ n : ℝ} (k : ℕ) (hγ : 0 < γ) (hε : 0 < ε)
    (he : γ * ε = e) (hCA : 0 ≤ CA) (hc' : 0 < c') (hc : 0 ≤ c) (hcc : c ≤ c' / 2)
    (hn : 0 ≤ n) (hℓ : 1 ≤ ℓ) (hε1 : 1 ≤ ε) (hA1 : 1 ≤ ε → 1 / e ≤ CA / (g ^ 2 + e))
    (hJ : J ≤ 2 / ε * Real.exp (-c' * n)) :
    γ⁻¹ * J ≤ 2 * CA * ((k.factorial : ℝ) * (1 / (c' / 2)) ^ k * Real.exp (c' / 2))
      * ((g ^ 2 + e)⁻¹ * ((n + 1) ^ k)⁻¹) * Real.exp (-c * n / ℓ) := by
  have he0 : 0 < e := by rw [← he]; positivity
  have hX : 0 ≤ (g ^ 2 + e)⁻¹ := inv_nonneg.mpr (by positivity)
  have hγ' : 0 ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
  have h1 := hA1 hε1
  rw [one_div, div_eq_mul_inv] at h1
  have h2 : γ⁻¹ * (2 / ε * Real.exp (-c' * n)) = 2 * e⁻¹ * Real.exp (-c' * n) := by
    rw [← he]; field_simp
  set M : ℝ := (k.factorial : ℝ) * (1 / (c' / 2)) ^ k * Real.exp (c' / 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hpoly : (n + 1) ^ k * Real.exp (-(c' / 2) * n) ≤ M := p5h_poly_exp_le (by positivity) k hn
  have hnk : 0 < (n + 1) ^ k := by positivity
  have hE1 : Real.exp (-(c' / 2) * n) ≤ M * ((n + 1) ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hnk, mul_comm]; exact hpoly
  have hE2 : Real.exp (-(c' / 2) * n) ≤ Real.exp (-c * n / ℓ) := by
    apply Real.exp_le_exp.mpr
    have hℓ0 : 0 < ℓ := by linarith
    have h3 : c * n / ℓ ≤ c * n := by
      rw [div_le_iff₀ hℓ0]; nlinarith [mul_nonneg hc hn]
    have h4 : c * n ≤ c' / 2 * n := mul_le_mul_of_nonneg_right hcc hn
    have h5 : -c * n / ℓ = -(c * n / ℓ) := by ring
    rw [h5]; nlinarith
  have hexp : Real.exp (-c' * n) = Real.exp (-(c' / 2) * n) * Real.exp (-(c' / 2) * n) := by
    rw [← Real.exp_add]; congr 1; ring
  calc γ⁻¹ * J ≤ γ⁻¹ * (2 / ε * Real.exp (-c' * n)) := mul_le_mul_of_nonneg_left hJ hγ'
    _ = 2 * e⁻¹ * Real.exp (-c' * n) := h2
    _ ≤ 2 * (CA * (g ^ 2 + e)⁻¹) * Real.exp (-c' * n) := by gcongr
    _ = 2 * CA * (g ^ 2 + e)⁻¹ * (Real.exp (-(c' / 2) * n) * Real.exp (-(c' / 2) * n)) := by
        rw [hexp]; ring
    _ ≤ 2 * CA * (g ^ 2 + e)⁻¹ * ((M * ((n + 1) ^ k)⁻¹) * Real.exp (-c * n / ℓ)) := by
        gcongr
    _ = _ := by ring

/-- `n ≥ 1`, `ε < 1`: `J ≤ C_B n^{-k} e^{-c'n√ε}`, and `e^{-c'n√ε} ≤ E_d e^{-c'n/ℓ}`
(`p5h_exp_bulk`), `n^{-k} ≤ 2^k (n+1)^{-k}`. -/
private lemma p5h_shape_small {γ ε e g J CA CB c' c ℓ n Ed : ℝ} (k : ℕ) (hγ : 0 < γ)
    (hε : 0 < ε) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hEd : 0 ≤ Ed) (hcc : c ≤ c')
    (hn : 1 ≤ n) (hℓ : 0 < ℓ) (he0 : 0 < e) (hε1 : ε < 1)
    (hA2 : ε < 1 → 1 / γ ≤ CA / (g ^ 2 + e))
    (hJ : J ≤ CB * (n ^ k)⁻¹ * Real.exp (-c' * n * Real.sqrt ε))
    (hU : Real.exp (-c' * n * Real.sqrt ε) ≤ Ed * Real.exp (-c' * n / ℓ)) :
    γ⁻¹ * J ≤ CA * CB * 2 ^ k * Ed * ((g ^ 2 + e)⁻¹ * ((n + 1) ^ k)⁻¹) * Real.exp (-c * n / ℓ) := by
  have hX : 0 ≤ (g ^ 2 + e)⁻¹ := inv_nonneg.mpr (by positivity)
  have hγ' : 0 ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
  have h1 := hA2 hε1
  rw [one_div, div_eq_mul_inv] at h1
  have hn0 : 0 < n := by linarith
  have hN := p5h_inv_pow_le hn k
  have hE : Real.exp (-c' * n / ℓ) ≤ Real.exp (-c * n / ℓ) := by
    apply Real.exp_le_exp.mpr
    have h3 : c * n / ℓ ≤ c' * n / ℓ := by
      apply div_le_div_of_nonneg_right _ hℓ.le
      exact mul_le_mul_of_nonneg_right hcc hn0.le
    have h4 : -c' * n / ℓ = -(c' * n / ℓ) := by ring
    have h5 : -c * n / ℓ = -(c * n / ℓ) := by ring
    rw [h4, h5]; linarith
  have hU' : Real.exp (-c' * n * Real.sqrt ε) ≤ Ed * Real.exp (-c * n / ℓ) :=
    hU.trans (mul_le_mul_of_nonneg_left hE hEd)
  have hnk : 0 ≤ (n ^ k)⁻¹ := by positivity
  have hnk1 : 0 ≤ ((n + 1) ^ k)⁻¹ := by positivity
  calc γ⁻¹ * J ≤ γ⁻¹ * (CB * (n ^ k)⁻¹ * Real.exp (-c' * n * Real.sqrt ε)) :=
        mul_le_mul_of_nonneg_left hJ hγ'
    _ ≤ (CA * (g ^ 2 + e)⁻¹) * (CB * (n ^ k)⁻¹ * Real.exp (-c' * n * Real.sqrt ε)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (CA * (g ^ 2 + e)⁻¹) * (CB * (2 ^ k * ((n + 1) ^ k)⁻¹) * (Ed * Real.exp (-c * n / ℓ))) := by
        gcongr
    _ = _ := by ring

/-- The head `γ⁻¹ J ≲ (g²+e)⁻¹ (n+1)^{-k} e^{-c n/ℓ}` in every regime of `ε` and every `n ≥ 0`,
with `c ≤ c'/2`: the constant is `Ch = CA (C₀ + 1 + 2 M + C_B 2^k E_d)`,
`M = k! (2/c')^k e^{c'/2}`, `E_d = e^{c'd/2}`. -/
private lemma p5h_head_shape {γ ε e g J CA CB C₀ c' c ℓ Ed : ℝ} (k n : ℕ) (hγ : 0 < γ)
    (hε : 0 < ε) (he : γ * ε = e) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hC₀ : 0 ≤ C₀) (hEd : 0 ≤ Ed)
    (hc' : 0 < c') (hc : 0 ≤ c) (hcc : c ≤ c' / 2) (hℓ : 1 ≤ ℓ)
    (hA1 : 1 ≤ ε → 1 / e ≤ CA / (g ^ 2 + e)) (hA2 : ε < 1 → 1 / γ ≤ CA / (g ^ 2 + e))
    (hJ0 : n = 0 → J ≤ C₀ ∧ J ≤ 1 / ε)
    (hJ1 : 1 ≤ n → ε < 1 → J ≤ CB * ((n : ℝ) ^ k)⁻¹ * Real.exp (-c' * n * Real.sqrt ε))
    (hJ2 : 1 ≤ n → 1 ≤ ε → J ≤ 2 / ε * Real.exp (-c' * n))
    (hU : 1 ≤ n → ε < 1 →
      Real.exp (-c' * n * Real.sqrt ε) ≤ Ed * Real.exp (-c' * n / ℓ)) :
    γ⁻¹ * J ≤ CA * (C₀ + 1 + 2 * ((k.factorial : ℝ) * (1 / (c' / 2)) ^ k * Real.exp (c' / 2))
        + CB * 2 ^ k * Ed) * ((g ^ 2 + e)⁻¹ * (((n : ℝ) + 1) ^ k)⁻¹) * Real.exp (-c * n / ℓ) := by
  have he0 : 0 < e := by rw [← he]; positivity
  have hX : 0 ≤ (g ^ 2 + e)⁻¹ := inv_nonneg.mpr (by positivity)
  have hℓ0 : 0 < ℓ := by linarith
  set M : ℝ := (k.factorial : ℝ) * (1 / (c' / 2)) ^ k * Real.exp (c' / 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hP : 0 ≤ (g ^ 2 + e)⁻¹ * (((n : ℝ) + 1) ^ k)⁻¹ := by positivity
  have hExp : 0 ≤ Real.exp (-c * n / ℓ) := (Real.exp_pos _).le
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- `n = 0`
    obtain ⟨h1, h2⟩ := hJ0 h0
    have := p5h_shape_zero hγ hε he hC₀ hCA hA1 hA2 h1 h2
    subst h0
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one, mul_zero, zero_div,
      Real.exp_zero]
    calc γ⁻¹ * J ≤ CA * (C₀ + 1) * (g ^ 2 + e)⁻¹ := this
      _ ≤ _ := by
          have : 0 ≤ CA * (g ^ 2 + e)⁻¹ := mul_nonneg hCA hX
          have h3 : 0 ≤ CB * 2 ^ k * Ed := by positivity
          nlinarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    have hn0 : (0 : ℝ) ≤ n := by linarith
    rcases lt_or_ge ε 1 with hε1 | hε1
    · have := p5h_shape_small (c := c) k hγ hε hCA hCB hEd (by linarith) hn1 hℓ0 he0 hε1 hA2
        (hJ1 hpos hε1) (hU hpos hε1)
      refine this.trans ?_
      have h3 : CA * CB * 2 ^ k * Ed ≤ CA * (C₀ + 1 + 2 * M + CB * 2 ^ k * Ed) := by
        have : 0 ≤ CA * (C₀ + 1 + 2 * M) := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hP) hExp
    · have := p5h_shape_big k hγ hε he hCA hc' hc hcc hn0 hℓ hε1 hA1 (hJ2 hpos hε1)
      refine this.trans ?_
      have h3 : 2 * CA * M ≤ CA * (C₀ + 1 + 2 * M + CB * 2 ^ k * Ed) := by
        have : 0 ≤ CA * (C₀ + 1) := by positivity
        have : 0 ≤ CA * (CB * 2 ^ k * Ed) := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hP) hExp

/-! ### The head and the tail integrals -/

private lemma p5h_lg_nonneg (m : ℕ) (c n ε : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ lgIntegrand m c n ε τ := by
  unfold lgIntegrand
  have : 0 ≤ min 1 (τ ^ (-(m : ℝ) / 2)) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  positivity

/-- Split of `∫_{(0,∞)}` at `T`. -/
private lemma p5h_split {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : IntegrableOn f (Ioi 0)) :
    ∫ τ in Ioi (0 : ℝ), f τ = (∫ τ in Ioc 0 T, f τ) + ∫ τ in Ioi T, f τ := by
  have hU : Ioc (0 : ℝ) T ∪ Ioi T = Ioi 0 := Ioc_union_Ioi_eq_Ioi hT.le
  have h1 : IntegrableOn f (Ioc 0 T) := hf.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn f (Ioi T) := hf.mono_set (Ioi_subset_Ioi hT.le)
  rw [← hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2]

/-- The head `(0, L²]`: `e^{-ετ} K_τ ≤ C_K · lgIntegrand` (`kProd_le`), so the head integral is
at most `C_K ∫_{(0,∞)} lgIntegrand` (`n` is `|a|`). -/
private lemma p5h_head_le (d L : ℕ) [NeZero L] {CK cK : ℝ} (hCK : 0 ≤ CK) {ε : ℝ} (hε : 0 < ε)
    (a : Zd d L) (n : ℕ)
    (hK : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → kProd d L τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
      Real.exp (-cK * min ((n : ℝ) ^ 2 / τ) (n : ℝ)))
    (hI : IntegrableOn (lgIntegrand d cK (n : ℝ) ε) (Ioi 0)) :
    ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kProd d L τ a
      ≤ CK * ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) ε τ := by
  have hF : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kProd d L τ a) (Ioc 0 ((L : ℝ) ^ 2)) :=
    (p5h_F_integrable d L hε a).mono_set Ioc_subset_Ioi_self
  have hI' : IntegrableOn (lgIntegrand d cK (n : ℝ) ε) (Ioc 0 ((L : ℝ) ^ 2)) :=
    hI.mono_set Ioc_subset_Ioi_self
  calc ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kProd d L τ a
      ≤ ∫ τ in Ioc 0 ((L : ℝ) ^ 2), CK * lgIntegrand d cK (n : ℝ) ε τ := by
        refine setIntegral_mono_on hF (hI'.const_mul CK) measurableSet_Ioc ?_
        intro τ hτ
        have h := hK τ hτ.1 hτ.2
        unfold lgIntegrand
        calc Real.exp (-ε * τ) * kProd d L τ a
            ≤ Real.exp (-ε * τ) * (CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
                Real.exp (-cK * min ((n : ℝ) ^ 2 / τ) (n : ℝ))) :=
              mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
          _ = _ := by ring
    _ = CK * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), lgIntegrand d cK (n : ℝ) ε τ :=
        integral_const_mul _ _
    _ ≤ CK * ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) ε τ := by
        refine mul_le_mul_of_nonneg_left ?_ hCK
        refine setIntegral_mono_set hI ?_ (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
        exact p5h_lg_nonneg d cK _ ε hτ

/-- `K_τ ≤ (1 + C) L^{-d}` for `τ ≥ 0` from `|K_τ - L^{-d}| ≤ C L^{-d} e^{-cτ/L²}`. -/
private lemma p5h_K_le_tail {d L : ℕ} [NeZero L] {CG cG τ : ℝ} (hCG : 0 ≤ CG) (hcG : 0 ≤ cG)
    (hτ : 0 ≤ τ) (a : Zd d L)
    (h : |kProd d L τ a - ((L : ℝ) ^ d)⁻¹|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) :
    kProd d L τ a ≤ (1 + CG) * ((L : ℝ) ^ d)⁻¹ := by
  have hLd : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  have he : Real.exp (-cG * τ / (L : ℝ) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ cG * τ / (L : ℝ) ^ 2 := by positivity
    have h2 : -cG * τ / (L : ℝ) ^ 2 = -(cG * τ / (L : ℝ) ^ 2) := by ring
    linarith
  have h1 : kProd d L τ a - ((L : ℝ) ^ d)⁻¹ ≤ CG * ((L : ℝ) ^ d)⁻¹ := by
    refine (le_abs_self _).trans (h.trans ?_)
    calc CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)
        ≤ CG * ((L : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := mul_one _
  linarith

/-- `∫_{(0,∞)} e^{-ετ} = 1/ε`. -/
private lemma p5h_integral_exp {ε : ℝ} (hε : 0 < ε) :
    ∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) = 1 / ε := by
  have ha : -ε < 0 := by linarith
  rw [integral_exp_mul_Ioi ha 0]
  simp [neg_div]

/-- `∫_{(T,∞)} e^{-ετ} = e^{-εT}/ε`. -/
private lemma p5h_integral_exp_Ioi {ε T : ℝ} (hε : 0 < ε) :
    ∫ τ in Ioi T, Real.exp (-ε * τ) = Real.exp (-ε * T) / ε := by
  have ha : -ε < 0 := by linarith
  rw [integral_exp_mul_Ioi ha T, neg_div, div_neg, neg_neg]

/-- The tail `(L², ∞)`: `K_τ ≤ (1 + C) L^{-d}` gives `(1 + C) L^{-d} e^{-εL²}/ε`. -/
private lemma p5h_tail_le (d L : ℕ) [NeZero L] {CG : ℝ} {ε : ℝ} (hε : 0 < ε)
    (a : Zd d L)
    (hG : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → kProd d L τ a ≤ (1 + CG) * ((L : ℝ) ^ d)⁻¹) :
    ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kProd d L τ a
      ≤ (1 + CG) * ((L : ℝ) ^ d)⁻¹ * (Real.exp (-ε * (L : ℝ) ^ 2) / ε) := by
  have hT : (0 : ℝ) < (L : ℝ) ^ 2 := by have := Nat.pos_of_neZero L; positivity
  have hF : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kProd d L τ a) (Ioi ((L : ℝ) ^ 2)) :=
    (p5h_F_integrable d L hε a).mono_set (Ioi_subset_Ioi hT.le)
  have hE : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioi ((L : ℝ) ^ 2)) :=
    integrableOn_exp_mul_Ioi (by linarith) _
  calc ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kProd d L τ a
      ≤ ∫ τ in Ioi ((L : ℝ) ^ 2), (1 + CG) * ((L : ℝ) ^ d)⁻¹ * Real.exp (-ε * τ) := by
        refine setIntegral_mono_on hF (hE.const_mul _) measurableSet_Ioi ?_
        intro τ hτ
        have h := hG τ hτ.le
        calc Real.exp (-ε * τ) * kProd d L τ a
            ≤ Real.exp (-ε * τ) * ((1 + CG) * ((L : ℝ) ^ d)⁻¹) :=
              mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
          _ = _ := by ring
    _ = (1 + CG) * ((L : ℝ) ^ d)⁻¹ * (Real.exp (-ε * (L : ℝ) ^ 2) / ε) := by
        rw [integral_const_mul, p5h_integral_exp_Ioi hε]

/-- The tail in the pinned shape: `γ⁻¹ (1 + C) L^{-d} e^{-εL²}/ε = (1 + C) e^{-εL²} (L^d e)⁻¹`,
and `e^{-εL²} ≤ E_z e^{-cn/ℓ}` (`p5h_exp_zero`). -/
private lemma p5h_tail_shape {γ ε e CG c ℓ n Ld L2 Ez : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
    (he : γ * ε = e) (hCG : 0 ≤ CG) (hLd : 0 < Ld)
    (hZ : Real.exp (-(ε * L2)) ≤ Ez * Real.exp (-c * n / ℓ)) :
    γ⁻¹ * ((1 + CG) * Ld⁻¹ * (Real.exp (-ε * L2) / ε))
      ≤ (1 + CG) * Ez * (Ld * e)⁻¹ * Real.exp (-c * n / ℓ) := by
  have he0 : 0 < e := by rw [← he]; positivity
  have h1 : γ⁻¹ * ((1 + CG) * Ld⁻¹ * (Real.exp (-ε * L2) / ε))
      = (1 + CG) * (Ld * e)⁻¹ * Real.exp (-(ε * L2)) := by
    rw [← he, neg_mul]; field_simp
  rw [h1]
  calc (1 + CG) * (Ld * e)⁻¹ * Real.exp (-(ε * L2))
      ≤ (1 + CG) * (Ld * e)⁻¹ * (Ez * Real.exp (-c * n / ℓ)) :=
        mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = _ := by ring

/-- The constant of the head in the pinned shape (`p5h_head_shape` times `C_K`). -/
private noncomputable def p5hCh (d : ℕ) (CK CA CB c' : ℝ) : ℝ :=
  CK * (CA * ((1 + 2 / ((d : ℝ) - 2)) + 1
    + 2 * (((d - 2).factorial : ℝ) * (1 / (c' / 2)) ^ (d - 2) * Real.exp (c' / 2))
    + CB * 2 ^ (d - 2) * Real.exp (c' * d / 2)))

private lemma p5hCh_nonneg {d : ℕ} (hd : 3 ≤ d) {CK CA CB c' : ℝ} (hCK : 0 ≤ CK) (hCA : 0 ≤ CA)
    (hCB : 0 ≤ CB) (hc' : 0 < c') : 0 ≤ p5hCh d CK CA CB c' := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : 0 ≤ 2 / ((d : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
  have h3 : 0 ≤ (1 + 2 / ((d : ℝ) - 2)) + 1 := by linarith
  have h4 : 0 ≤ 2 * (((d - 2).factorial : ℝ) * (1 / (c' / 2)) ^ (d - 2) * Real.exp (c' / 2)) := by
    positivity
  have h5 : 0 ≤ CB * 2 ^ (d - 2) * Real.exp (c' * d / 2) := by positivity
  unfold p5hCh
  exact mul_nonneg hCK (mul_nonneg hCA (by linarith))

/-- **The head in the pinned shape** (`0 < t < 1`): `γ⁻¹ ∫_{(0,L²]} e^{-ετ} K_τ(a) dτ
≤ Ch (g² + e)⁻¹ (n+1)^{-(d-2)} e^{-c n/ℓ_t}` for `0 ≤ c ≤ c'/2`; `kProd_le`, `lg_bulk`, `lg_zero`,
`lg_convA`, `lg_convB`, in the regimes `n = 0`, `ε ≥ 1`, `ε < 1`. -/
private lemma p5h_head5 (d : ℕ) (hd : 3 ≤ d) {Λ : ℝ} {CK cK CB c' CA : ℝ}
    (hCK : 0 < CK) (hCB : 0 < CB) (hc' : 0 < c') (hCA : 0 < CA)
    (hK : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
      kProd d L τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
        Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)))
    (hB : ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε → IntegrableOn (lgIntegrand d cK n ε) (Ioi 0) ∧
      (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ
        ≤ CB * n ^ (-((d : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
      (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ ≤ 2 / ε * Real.exp (-c' * n)))
    (hA : ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ lgEps d g t → 1 / (1 - t) ≤ CA / (g ^ 2 + (1 - t))) ∧
      (lgEps d g t < 1 → 1 / lgGam d g t ≤ CA / (g ^ 2 + (1 - t))))
    (L : ℕ) (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (hgΛ : g ≤ Λ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Zd d L) {c : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c' / 2) :
    haveI : NeZero L := ⟨by omega⟩
    (lgGam d g t)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ) * kProd d L τ a
      ≤ p5hCh d CK CA CB c' * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
        * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
  have : NeZero L := ⟨by omega⟩
  have hL1 : 1 ≤ L := by omega
  have hγ := p5h_gam_pos d hg ht0
  have hε := p5h_eps_pos d hg ht0 ht1
  have he := p5h_gam_mul_eps d hg ht0
  have hnL := p5h_zdistD_le d L a
  have hKa : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → kProd d L τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
      Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) :=
    fun τ hτ hτL => hK L τ hτ hτL a
  generalize zdistD d L a = n at hKa hnL ⊢
  have hcn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT (by exact_mod_cast hL1)
  have hℓ0 : 0 < ellT L g t := lt_of_lt_of_le one_pos hℓ1
  obtain ⟨hB1, hB2⟩ := lg_convB d L g t hL1 hg ht0 ht1
  obtain ⟨hA1, hA2⟩ := hA g t hg hgΛ ht0 ht1
  have hd2 : 2 ≤ d := by omega
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hI : IntegrableOn (lgIntegrand d cK (n : ℝ) (lgEps d g t)) (Ioi 0) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simpa using (lg_zero d hd cK (lgEps d g t) hε.le).1
    · exact (hB n (lgEps d g t) (by exact_mod_cast hpos) hε.le).1
  have hhead := p5h_head_le d L hCK.le hε a n hKa hI
  have hJ0 : n = 0 → (∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (lgEps d g t) τ)
      ≤ 1 + 2 / ((d : ℝ) - 2) ∧
      (∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (lgEps d g t) τ) ≤ 1 / lgEps d g t := by
    intro h0
    subst h0
    obtain ⟨-, h1, h2⟩ := lg_zero d hd cK (lgEps d g t) hε.le
    exact ⟨by simpa using h1, by simpa using h2 hε⟩
  have hJ1 : 1 ≤ n → lgEps d g t < 1 →
      (∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (lgEps d g t) τ)
      ≤ CB * ((n : ℝ) ^ (d - 2))⁻¹ * Real.exp (-c' * n * Real.sqrt (lgEps d g t)) := by
    intro h1 h2
    have := (hB n (lgEps d g t) (by exact_mod_cast h1) hε.le).2.1 h2.le
    rwa [p5h_rpow_eq hd2 hcn] at this
  have hJ2 : 1 ≤ n → 1 ≤ lgEps d g t →
      (∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (lgEps d g t) τ)
      ≤ 2 / lgEps d g t * Real.exp (-c' * n) := by
    intro h1 h2
    exact (hB n (lgEps d g t) (by exact_mod_cast h1) hε.le).2.2 h2
  have hU : 1 ≤ n → lgEps d g t < 1 →
      Real.exp (-c' * n * Real.sqrt (lgEps d g t))
        ≤ Real.exp (c' * d / 2) * Real.exp (-c' * n / ellT L g t) := fun _ _ =>
    p5h_exp_bulk d L hL1 hc'.le hcn hnL hB1 hB2
  have hC₀ : (0 : ℝ) ≤ 1 + 2 / ((d : ℝ) - 2) := by
    have : 0 ≤ 2 / ((d : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
    linarith
  have hshape := p5h_head_shape (d - 2) n hγ hε he hCA.le hCB.le hC₀ (Real.exp_pos _).le hc' hc
    hcc hℓ1 hA1 hA2 hJ0 hJ1 hJ2 hU
  calc (lgGam d g t)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ) * kProd d L τ a
      ≤ (lgGam d g t)⁻¹ * (CK * ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (lgEps d g t) τ) :=
        mul_le_mul_of_nonneg_left hhead (inv_nonneg.mpr hγ.le)
    _ = CK * ((lgGam d g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (lgEps d g t) τ) := by
        ring
    _ ≤ CK * (CA * ((1 + 2 / ((d : ℝ) - 2)) + 1
          + 2 * (((d - 2).factorial : ℝ) * (1 / (c' / 2)) ^ (d - 2) * Real.exp (c' / 2))
          + CB * 2 ^ (d - 2) * Real.exp (c' * d / 2)) *
          ((g ^ 2 + (1 - t))⁻¹ * (((n : ℝ) + 1) ^ (d - 2))⁻¹) * Real.exp (-c * n / ellT L g t)) :=
        mul_le_mul_of_nonneg_left hshape hCK.le
    _ = _ := by unfold p5hCh; ring

/-- **The tail in the pinned shape** (`0 < t < 1`): `γ⁻¹ ∫_{(L²,∞)} e^{-ετ} K_τ(a) dτ
≤ (1 + C_G) e^{cd/2} (L^d e)⁻¹ e^{-c n/ℓ_t}` for `0 ≤ c`, `c d ≤ 2` (zero mode, Fable F5 (c)). -/
private lemma p5h_tail5 (d : ℕ) {CG cG : ℝ} (hCG : 0 < CG) (hcG : 0 ≤ cG)
    (hG : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ a : Zd d L,
      |kProd d L τ a - ((L : ℝ) ^ d)⁻¹|
        ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2))
    (L : ℕ) (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Zd d L) {c : ℝ} (hc : 0 ≤ c) (hcd : c * d ≤ 2) :
    haveI : NeZero L := ⟨by omega⟩
    (lgGam d g t)⁻¹ * ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ) * kProd d L τ a
      ≤ (1 + CG) * Real.exp (c * d / 2) * (((L : ℝ) ^ d * (1 - t))⁻¹)
        * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
  have : NeZero L := ⟨by omega⟩
  have hL1 : 1 ≤ L := by omega
  have hγ := p5h_gam_pos d hg ht0
  have hε := p5h_eps_pos d hg ht0 ht1
  have he := p5h_gam_mul_eps d hg ht0
  have hGa : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → kProd d L τ a ≤ (1 + CG) * ((L : ℝ) ^ d)⁻¹ := fun τ hτ =>
    p5h_K_le_tail hCG.le hcG (le_trans (by positivity) hτ) a (hG L τ hτ a)
  have htail := p5h_tail_le d L hε a hGa
  have hnL := p5h_zdistD_le d L a
  generalize zdistD d L a = n at hnL ⊢
  have hcn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT (by exact_mod_cast hL1)
  have hℓ0 : 0 < ellT L g t := lt_of_lt_of_le one_pos hℓ1
  obtain ⟨-, hB2⟩ := lg_convB d L g t hL1 hg ht0 ht1
  have hC := lg_convC d L g t n hL1 hg ht0 ht1 hcn hnL
  have hZ := p5h_exp_zero d L hL1 hε hc hcd hnL hB2 hC
  have hLd : 0 < (L : ℝ) ^ d := by positivity
  calc (lgGam d g t)⁻¹ * ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ) * kProd d L τ a
      ≤ (lgGam d g t)⁻¹ * ((1 + CG) * ((L : ℝ) ^ d)⁻¹
          * (Real.exp (-(lgEps d g t) * (L : ℝ) ^ 2) / lgEps d g t)) :=
        mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hγ.le)
    _ ≤ _ := p5h_tail_shape hγ hε he hCG.le hLd hZ

/-! ### Property 5 -/

private lemma p5h_norm_spin (m : ℂ) (hm : ‖m‖ = 1) (σ : Bool) : ‖PropSpin m σ‖ = 1 := by
  cases σ <;> simp [PropSpin, hm]

private lemma p5h_norm_mu (m : ℂ) (hm : ‖m‖ = 1) (σ₁ σ₂ : Bool) :
    ‖PropSpin m σ₁ * PropSpin m σ₂‖ = 1 := by
  rw [norm_mul, p5h_norm_spin m hm σ₁, p5h_norm_spin m hm σ₂, one_mul]

private lemma p5h_Theta_zero (d L : ℕ) [NeZero L] (g : ℝ) : Theta d L g 0 = 1 := by
  simp [Theta]

/-- `t = 0`: `Θ = 1`, `B_{0,0} ≥ (Λ²+1)⁻¹`. -/
private lemma p5h_zero5 (d L : ℕ) [NeZero L] {Λ g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (μ : ℂ)
    (a : Zd d L) {c C : ℝ} (hC : Λ ^ 2 + 1 ≤ C) :
    ‖Theta d L g (((0 : ℝ) : ℂ) * μ) 0 a‖
      ≤ C * Bparam d L g 0 (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g 0) := by
  rw [Complex.ofReal_zero, zero_mul, p5h_Theta_zero]
  by_cases ha : a = 0
  · subst ha
    simp only [zdistD_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one,
      Matrix.one_apply_eq, norm_one, Bparam, sub_zero, abs_one, zero_add, one_pow, inv_one]
    have hg2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
    have hP : (0 : ℝ) < g ^ 2 + 1 := by positivity
    have h1 : 1 ≤ C * (g ^ 2 + 1)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hP]; nlinarith
    have h2 : 0 ≤ C * (((L : ℝ) ^ d)⁻¹) := by
      have : 0 < C := by nlinarith [sq_nonneg Λ]
      positivity
    calc (1 : ℝ) ≤ C * (g ^ 2 + 1)⁻¹ := h1
      _ ≤ C * ((g ^ 2 + 1)⁻¹ + ((L : ℝ) ^ d)⁻¹) := by nlinarith
  · rw [Matrix.one_apply_ne (Ne.symm ha)]
    simp only [norm_zero]
    have : 0 < C := by nlinarith [sq_nonneg Λ]
    have hB : 0 ≤ Bparam d L g 0 (zdistD d L a) := by unfold Bparam; positivity
    positivity

/-- **Property 5 for real `t ∈ (0,1)`**: `Re Θ_t(0,a) ≤ C B_{t,|a|} e^{-c|a|/ℓ_t}`. -/
private lemma p5h_core5 (d : ℕ) (hd : 3 ≤ d) {Λ : ℝ} {CK cK CG cG CB c' CA : ℝ}
    (hCK : 0 < CK) (hCG : 0 < CG) (hcG : 0 ≤ cG) (hCB : 0 < CB) (hc' : 0 < c') (hCA : 0 < CA)
    (hK : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
      kProd d L τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
        Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)))
    (hG : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ a : Zd d L,
      |kProd d L τ a - ((L : ℝ) ^ d)⁻¹|
        ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2))
    (hB : ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε → IntegrableOn (lgIntegrand d cK n ε) (Ioi 0) ∧
      (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ
        ≤ CB * n ^ (-((d : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
      (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ ≤ 2 / ε * Real.exp (-c' * n)))
    (hA : ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ lgEps d g t → 1 / (1 - t) ≤ CA / (g ^ 2 + (1 - t))) ∧
      (lgEps d g t < 1 → 1 / lgGam d g t ≤ CA / (g ^ 2 + (1 - t))))
    (L : ℕ) (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (hgΛ : g ≤ Λ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Zd d L) {c : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c' / 2) (hcd : c * d ≤ 2) {C : ℝ}
    (hC1 : p5hCh d CK CA CB c' ≤ C) (hC2 : (1 + CG) * Real.exp (c * d / 2) ≤ C) :
    haveI : NeZero L := ⟨by omega⟩
    (Theta d L g (t : ℂ) 0 a).re
      ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
  have : NeZero L := ⟨by omega⟩
  have hγ := p5h_gam_pos d hg ht0
  have hε := p5h_eps_pos d hg ht0 ht1
  have hT : (0 : ℝ) < (L : ℝ) ^ 2 := by have := Nat.pos_of_neZero L; positivity
  rw [p5h_theta_eq d L hL g t hg ht0 ht1 a, Complex.ofReal_re,
    p5h_split hT (p5h_F_integrable d L hε a), mul_add]
  have h1 := p5h_head5 d hd hCK hCB hc' hCA hK hB hA L hL g hg hgΛ t ht0 ht1 a hc hcc
  have h2 := p5h_tail5 d hCG hcG hG L hL g hg t ht0 ht1 a hc hcd
  have hBp : Bparam d L g t (zdistD d L a)
      = (g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
        + ((L : ℝ) ^ d * (1 - t))⁻¹ := by
    have : |1 - t| = 1 - t := abs_of_pos (by linarith)
    simp only [Bparam, this]
  rw [hBp]
  have hX : 0 ≤ (g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
    have : (0 : ℝ) < 1 - t := by linarith
    positivity
  have hF : 0 ≤ ((L : ℝ) ^ d * (1 - t))⁻¹ := by
    have : (0 : ℝ) < 1 - t := by linarith
    positivity
  have hEx : 0 ≤ Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := (Real.exp_pos _).le
  have hCh0 := p5hCh_nonneg hd hCK.le hCA.le hCB.le hc'
  calc _ ≤ p5hCh d CK CA CB c'
            * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
          * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)
        + (1 + CG) * Real.exp (c * d / 2) * (((L : ℝ) ^ d * (1 - t))⁻¹)
          * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := add_le_add h1 h2
    _ ≤ C * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
          * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)
        + C * (((L : ℝ) ^ d * (1 - t))⁻¹)
          * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
        gcongr
    _ = _ := by ring

/-- **`(prop:ThfadC)`** (property 5 of `lem_propTH`) for every `d ≥ 3` and `Λ > 0`: constants
`(C, c)` depend on `(d, Λ)` only.  Reduction to real `t` (`norm_Theta_apply_le`), `t = 0`
separately, `0 < t < 1` by the Laplace representation `Θ_t(0,a) = γ⁻¹ ∫₀^∞ e^{-ετ} K_τ(a) dτ`
split at `τ = L²`; regimes `n = 0`, `ε ≥ 1`, `L⁻² ≤ ε < 1`, `ε < L⁻²`.  No unproved input. -/
theorem prop5Decay_holds (d : ℕ) (Λ : ℝ) : Prop5Decay d Λ := by
  intro hd hΛ
  obtain ⟨CK, cK, hCK, hcK, hK⟩ := kProd_le d (by omega)
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := kProd_gap d (by omega)
  obtain ⟨CB, hCB, c', hc', hB⟩ := lg_bulk d hd cK hcK
  obtain ⟨CA, hCA, hA⟩ := lg_convA d Λ hΛ
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (c' / 2) (2 / d) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact lt_min (by positivity) (by positivity)
  have hcc : c ≤ c' / 2 := by rw [hc]; exact min_le_left _ _
  have hcd : c * d ≤ 2 := by
    have : c ≤ 2 / d := by rw [hc]; exact min_le_right _ _
    calc c * d ≤ 2 / d * d := mul_le_mul_of_nonneg_right this hdpos.le
      _ = 2 := by field_simp
  have hCh0 := p5hCh_nonneg hd hCK.le hCA.le hCB.le hc'
  have hCt0 : 0 ≤ (1 + CG) * Real.exp (c * d / 2) := by positivity
  have hΛ2 : 0 < Λ ^ 2 + 1 := by positivity
  refine ⟨p5hCh d CK CA CB c' + (1 + CG) * Real.exp (c * d / 2) + (Λ ^ 2 + 1), by positivity, c,
    hc0, ?_⟩
  intro L hL g hg hgΛ t ht0 ht1 m hm σ₁ σ₂ a
  have : NeZero L := ⟨by omega⟩
  rcases ht0.eq_or_lt with h0 | h0
  · subst h0
    exact p5h_zero5 d L hg hgΛ _ a (by linarith)
  · refine le_trans (norm_Theta_apply_le hL ht0 ht1 (p5h_norm_mu m hm σ₁ σ₂) 0 a) ?_
    exact p5h_core5 d hd hCK hCG hcG.le hCB hc' hCA hK
      (fun L _ τ hτ a => (hG L τ hτ a ⟨0, by omega⟩ ⟨0, by omega⟩).1) hB hA L hL g hg hgΛ t h0 ht1 a
      hc0.le hcc hcd (by linarith) (by linarith)

/-! ### Property 8, `σ₁ ≠ σ₂` (`μ = 1`): the zero-mode-removed Laplace representation -/

/-- `Θ̊_t(0,a) = γ⁻¹ ∫₀^∞ e^{-ετ} (K_τ(a) - L^{-d}) dτ` for `0 < t < 1`
(`Theta0_apply_eq` and `∫₀^∞ e^{-ετ} = 1/ε`, `γ ε = e`). -/
private lemma p5h_theta0_eq (d L : ℕ) (hL : 3 ≤ L) (g t : ℝ) (hg : 0 < g) (ht0 : 0 < t)
    (ht1 : t < 1) (a : Zd d L) :
    haveI : NeZero L := ⟨by omega⟩
    Theta0 d L g (t : ℂ) 0 a =
      (((lgGam d g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ)
          * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹) : ℝ) : ℂ) := by
  have : NeZero L := ⟨by omega⟩
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0.le]
  have hγ := p5h_gam_pos d hg ht0
  have hε := p5h_eps_pos d hg ht0 ht1
  have he := p5h_gam_mul_eps d hg ht0
  rw [Theta0_apply_eq hL hξ, p5h_theta_eq d L hL g t hg ht0 ht1 a]
  have hE : IntegrableOn (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hint : ∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹)
      = (∫ τ in Ioi (0 : ℝ), Real.exp (-(lgEps d g t) * τ) * kProd d L τ a)
        - ((L : ℝ) ^ d)⁻¹ * (1 / lgEps d g t) := by
    have h1 : (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ) * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹))
        = fun τ : ℝ => Real.exp (-(lgEps d g t) * τ) * kProd d L τ a
          - ((L : ℝ) ^ d)⁻¹ * Real.exp (-(lgEps d g t) * τ) := by
      funext τ; ring
    rw [h1, integral_sub (p5h_F_integrable d L hε a) (hE.const_mul _), integral_const_mul,
      p5h_integral_exp hε]
  rw [hint]
  have hc : ((L : ℂ) ^ d)⁻¹ * (1 - (t : ℂ))⁻¹
      = ((((lgGam d g t)⁻¹ * (((L : ℝ) ^ d)⁻¹ * (1 / lgEps d g t)) : ℝ)) : ℂ) := by
    have h2 : (lgGam d g t)⁻¹ * (((L : ℝ) ^ d)⁻¹ * (1 / lgEps d g t))
        = ((L : ℝ) ^ d)⁻¹ * (1 - t)⁻¹ := by
      rw [← he]; field_simp
    rw [h2]; push_cast; ring
  rw [hc, ← Complex.ofReal_sub]
  congr 1
  ring

/-- `γ⁻¹ (L^{-d} Y) ≲ (g²+e)⁻¹ L^{-(d-2)}` when `Y ≤ A L²` and `Y ≤ A/ε`:
`ε < 1` uses `γ⁻¹` (`lg_convA`) and `L^{-d} L² = L^{-(d-2)}`, `ε ≥ 1` uses `γ⁻¹/ε = 1/e`. -/
private lemma p5h_Ld_piece {γ ε e g Y A Ld T W CA : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
    (he : γ * ε = e) (hA : 0 ≤ A) (hCA : 0 ≤ CA) (hLd : 0 ≤ Ld) (hLT : Ld * T = W)
    (hLdW : Ld ≤ W) (hA1 : 1 ≤ ε → 1 / e ≤ CA / (g ^ 2 + e))
    (hA2 : ε < 1 → 1 / γ ≤ CA / (g ^ 2 + e)) (hY1 : Y ≤ A * T) (hY2 : Y ≤ A / ε) :
    γ⁻¹ * (Ld * Y) ≤ CA * A * ((g ^ 2 + e)⁻¹ * W) := by
  have he0 : 0 < e := by rw [← he]; positivity
  have hX : 0 ≤ (g ^ 2 + e)⁻¹ := inv_nonneg.mpr (by positivity)
  have hγ' : 0 ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
  have hW : 0 ≤ W := le_trans hLd hLdW
  rcases lt_or_ge ε 1 with h | h
  · have h1 := hA2 h
    rw [one_div, div_eq_mul_inv] at h1
    calc γ⁻¹ * (Ld * Y) ≤ γ⁻¹ * (Ld * (A * T)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY1 hLd) hγ'
      _ = A * γ⁻¹ * W := by rw [← hLT]; ring
      _ ≤ A * (CA * (g ^ 2 + e)⁻¹) * W := by gcongr
      _ = _ := by ring
  · have h1 := hA1 h
    rw [one_div, div_eq_mul_inv] at h1
    have h2 : γ⁻¹ * (Ld * (A / ε)) = A * Ld * e⁻¹ := by
      rw [← he]; field_simp
    calc γ⁻¹ * (Ld * Y) ≤ γ⁻¹ * (Ld * (A / ε)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY2 hLd) hγ'
      _ = A * Ld * e⁻¹ := h2
      _ ≤ A * Ld * (CA * (g ^ 2 + e)⁻¹) := by gcongr
      _ ≤ A * W * (CA * (g ^ 2 + e)⁻¹) := by gcongr
      _ = _ := by ring

/-- The head `(0, L²]` of the zero-mode-removed integrand: `|∫ e^{-ετ}(K - L^{-d})| ≤ ∫ e^{-ετ} K
+ L^{-d} ∫ e^{-ετ}` (Fable F5 (d): `e^{-ετ}` is kept on the `L^{-d}` piece). -/
private lemma p5h_head0_le (d L : ℕ) [NeZero L] {ε : ℝ} (hε : 0 < ε) (a : Zd d L) :
    |∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹)|
      ≤ (∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kProd d L τ a)
        + ((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) := by
  have hF : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kProd d L τ a) (Ioc 0 ((L : ℝ) ^ 2)) :=
    (p5h_F_integrable d L hε a).mono_set Ioc_subset_Ioi_self
  have hE : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioc 0 ((L : ℝ) ^ 2)) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-ε * τ)).integrableOn_Ioc
  have h1 : (fun τ : ℝ => Real.exp (-ε * τ) * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹))
      = fun τ : ℝ => Real.exp (-ε * τ) * kProd d L τ a
        - ((L : ℝ) ^ d)⁻¹ * Real.exp (-ε * τ) := by
    funext τ; ring
  rw [h1, integral_sub hF (hE.const_mul _), integral_const_mul]
  have hx : 0 ≤ ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kProd d L τ a := by
    refine setIntegral_nonneg measurableSet_Ioc fun τ hτ => ?_
    exact mul_nonneg (Real.exp_pos _).le (p5h_kProd_nonneg_le_one d L hτ.1.le a).1
  have hy : 0 ≤ ((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) := by
    refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioc fun τ _ => ?_)
    exact (Real.exp_pos _).le
  rw [abs_le]
  constructor <;> linarith

/-- The tail `(L², ∞)` of the zero-mode-removed integrand:
`|K - L^{-d}| ≤ C_G L^{-d} e^{-cτ/L²}`. -/
private lemma p5h_tail0_le (d L : ℕ) [NeZero L] {CG cG : ℝ} (hcG : 0 < cG)
    {ε : ℝ} (hε : 0 < ε) (a : Zd d L)
    (hG : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → |kProd d L τ a - ((L : ℝ) ^ d)⁻¹|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) :
    |∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-ε * τ) * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹)|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ *
        ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-ε * τ - cG * τ / (L : ℝ) ^ 2) := by
  have hT : (0 : ℝ) < (L : ℝ) ^ 2 := by have := Nat.pos_of_neZero L; positivity
  obtain ⟨hI, -⟩ := (lg_tail ((L : ℝ) ^ 2) hT).1 ε cG hε.le hcG
  rw [← integral_const_mul]
  have := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi ((L : ℝ) ^ 2)))
    (f := fun τ : ℝ => Real.exp (-ε * τ) * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹))
    (g := fun τ : ℝ => CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-ε * τ - cG * τ / (L : ℝ) ^ 2))
    (hI.const_mul _) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h := hG τ (le_of_lt hτ)
      have hexp : Real.exp (-ε * τ - cG * τ / (L : ℝ) ^ 2)
          = Real.exp (-ε * τ) * Real.exp (-cG * τ / (L : ℝ) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]
      calc Real.exp (-ε * τ) * |kProd d L τ a - ((L : ℝ) ^ d)⁻¹|
          ≤ Real.exp (-ε * τ) * (CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = _ := by ring)
  simpa [Real.norm_eq_abs] using this

/-- **Property 8, `μ = 1`, `0 < t < 1`**: `|Θ̊_t(0,a)| ≤ C (g²+e)⁻¹ (n+1)^{-(d-2)}`; the head
`K` piece is the property-5 head at `c = 0`, the `L^{-d}` pieces keep `e^{-ετ}` (`p5h_Ld_piece`). -/
private lemma p5h_core8 (d : ℕ) (hd : 3 ≤ d) {Λ : ℝ} {CK cK CG cG CB c' CA : ℝ}
    (hCK : 0 < CK) (hCG : 0 < CG) (hcG : 0 < cG) (hCB : 0 < CB) (hc' : 0 < c') (hCA : 0 < CA)
    (hK : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
      kProd d L τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
        Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)))
    (hG : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ a : Zd d L,
      |kProd d L τ a - ((L : ℝ) ^ d)⁻¹|
        ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2))
    (hB : ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε → IntegrableOn (lgIntegrand d cK n ε) (Ioi 0) ∧
      (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ
        ≤ CB * n ^ (-((d : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
      (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ ≤ 2 / ε * Real.exp (-c' * n)))
    (hA : ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ lgEps d g t → 1 / (1 - t) ≤ CA / (g ^ 2 + (1 - t))) ∧
      (lgEps d g t < 1 → 1 / lgGam d g t ≤ CA / (g ^ 2 + (1 - t))))
    (L : ℕ) (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (hgΛ : g ≤ Λ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Zd d L) {C : ℝ}
    (hC : p5hCh d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
      + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2) ≤ C) :
    haveI : NeZero L := ⟨by omega⟩
    ‖Theta0 d L g (t : ℂ) 0 a‖
      ≤ C * (g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
  have : NeZero L := ⟨by omega⟩
  have hL1 : 1 ≤ L := by omega
  have hd2 : 2 ≤ d := by omega
  have hγ := p5h_gam_pos d hg ht0
  have hε := p5h_eps_pos d hg ht0 ht1
  have he := p5h_gam_mul_eps d hg ht0
  have hT : (0 : ℝ) < (L : ℝ) ^ 2 := by have := Nat.pos_of_neZero L; positivity
  obtain ⟨hA1, hA2⟩ := hA g t hg hgΛ ht0 ht1
  have hγ' : 0 ≤ (lgGam d g t)⁻¹ := inv_nonneg.mpr hγ.le
  have hLd0 : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  have hE : IntegrableOn (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hh : IntegrableOn (fun τ : ℝ => Real.exp (-(lgEps d g t) * τ)
      * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹)) (Ioi 0) := by
    have h1 := (p5h_F_integrable d L hε a).sub (hE.const_mul (((L : ℝ) ^ d)⁻¹))
    refine h1.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    rw [Pi.sub_apply]; ring
  rw [p5h_theta0_eq d L hL g t hg ht0 ht1 a, Complex.norm_real, Real.norm_eq_abs,
    p5h_split hT hh, abs_mul, abs_of_nonneg hγ']
  -- the three pieces
  have hHead := p5h_head0_le d L hε a
  have hTail := p5h_tail0_le d L hcG hε a (fun τ hτ => hG L τ hτ a)
  obtain ⟨hY2a, hY2b⟩ := (lg_tail ((L : ℝ) ^ 2) hT).2.2 (lgEps d g t) hε.le
  have hY2c := hY2b hε
  obtain ⟨-, hY3a⟩ := (lg_tail ((L : ℝ) ^ 2) hT).1 (lgEps d g t) cG hε.le hcG
  obtain ⟨-, hY3b⟩ := (lg_tail ((L : ℝ) ^ 2) hT).2.1 (lgEps d g t) cG hε hcG.le
  have hexpT : Real.exp (-(lgEps d g t) * (L : ℝ) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 ≤ lgEps d g t * (L : ℝ) ^ 2 := by positivity
    linarith
  have hexpT0 : 0 < Real.exp (-(lgEps d g t) * (L : ℝ) ^ 2) := Real.exp_pos _
  have hY3T : ∫ τ in Ioi ((L : ℝ) ^ 2),
      Real.exp (-(lgEps d g t) * τ - cG * τ / (L : ℝ) ^ 2) ≤ (1 + 1 / cG) * (L : ℝ) ^ 2 := by
    refine hY3a.trans ?_
    calc Real.exp (-(lgEps d g t) * (L : ℝ) ^ 2) * ((L : ℝ) ^ 2 / cG)
        ≤ 1 * ((L : ℝ) ^ 2 / cG) := mul_le_mul_of_nonneg_right hexpT (by positivity)
      _ = (1 / cG) * (L : ℝ) ^ 2 := by ring
      _ ≤ (1 + 1 / cG) * (L : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hT.le; linarith
  have hY3ε : ∫ τ in Ioi ((L : ℝ) ^ 2),
      Real.exp (-(lgEps d g t) * τ - cG * τ / (L : ℝ) ^ 2) ≤ (1 + 1 / cG) / lgEps d g t := by
    refine hY3b.trans ?_
    calc Real.exp (-(lgEps d g t) * (L : ℝ) ^ 2) / lgEps d g t ≤ 1 / lgEps d g t :=
          div_le_div_of_nonneg_right hexpT hε.le
      _ ≤ (1 + 1 / cG) / lgEps d g t := by
          apply div_le_div_of_nonneg_right _ hε.le
          have : 0 < 1 / cG := by positivity
          linarith
  -- `L^{-d} L² = L^{-(d-2)}`
  have hLd : (L : ℝ) ^ d = (L : ℝ) ^ (d - 2) * (L : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hLT : ((L : ℝ) ^ d)⁻¹ * (L : ℝ) ^ 2 = ((L : ℝ) ^ (d - 2))⁻¹ := by
    have h0 : (L : ℝ) ≠ 0 := by positivity
    rw [hLd]; field_simp
  have hLdW := p5h_Linv_d_le d L hd2
  have hW := p5h_Linv_le d L a (d - 2)
  -- (a) the head `K` piece, the property-5 head at `c = 0`
  have h5 := p5h_head5 d hd hCK hCB hc' hCA hK hB hA L hL g hg hgΛ t ht0 ht1 a (c := 0) le_rfl
    (by linarith)
  simp only [neg_zero, zero_mul, zero_div, Real.exp_zero, mul_one] at h5
  -- (b), (c) the `L^{-d}` pieces
  have h6 := p5h_Ld_piece (A := 1)
    (Y := ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ)) hγ hε he zero_le_one hCA.le
    hLd0 hLT hLdW hA1 hA2 (by rw [one_mul]; exact hY2a) hY2c
  have hA3 : (0 : ℝ) ≤ 1 + 1 / cG := by positivity
  have h7 := p5h_Ld_piece (A := 1 + 1 / cG) hγ hε he hA3 hCA.le hLd0 hLT hLdW hA1 hA2
    hY3T hY3ε
  have hX : 0 ≤ (g ^ 2 + (1 - t))⁻¹ := by
    have : (0 : ℝ) < 1 - t := by linarith
    positivity
  have hP : 0 ≤ ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hXP : 0 ≤ (g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
    mul_nonneg hX hP
  calc (lgGam d g t)⁻¹ * |(∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ)
          * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹))
        + ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ)
          * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹)|
      ≤ (lgGam d g t)⁻¹ * (|∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ)
          * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹)|
        + |∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ)
          * (kProd d L τ a - ((L : ℝ) ^ d)⁻¹)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hγ'
    _ ≤ (lgGam d g t)⁻¹ * (((∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ)
            * kProd d L τ a)
          + ((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ))
        + CG * ((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioi ((L : ℝ) ^ 2),
            Real.exp (-(lgEps d g t) * τ - cG * τ / (L : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hHead hTail) hγ'
    _ = ((lgGam d g t)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(lgEps d g t) * τ)
            * kProd d L τ a)
        + (lgGam d g t)⁻¹ * (((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2),
            Real.exp (-(lgEps d g t) * τ))
        + CG * ((lgGam d g t)⁻¹ * (((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioi ((L : ℝ) ^ 2),
            Real.exp (-(lgEps d g t) * τ - cG * τ / (L : ℝ) ^ 2))) := by ring
    _ ≤ p5hCh d CK CA CB c' * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
        + CA * 1 * ((g ^ 2 + (1 - t))⁻¹ * (((L : ℝ) ^ (d - 2))⁻¹))
        + CG * (CA * (1 + 1 / cG) * ((g ^ 2 + (1 - t))⁻¹ * (((L : ℝ) ^ (d - 2))⁻¹))) :=
        add_le_add (add_le_add h5 h6) (mul_le_mul_of_nonneg_left h7 hCG.le)
    _ ≤ p5hCh d CK CA CB c' * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
        + CA * 1 * ((g ^ 2 + (1 - t))⁻¹ * (((d : ℝ) / 2 + 1) ^ (d - 2)
            * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹))
        + CG * (CA * (1 + 1 / cG) * ((g ^ 2 + (1 - t))⁻¹ * (((d : ℝ) / 2 + 1) ^ (d - 2)
            * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹))) := by
        gcongr
    _ = (p5hCh d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
          + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2))
        * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) := by ring
    _ ≤ C * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) :=
        mul_le_mul_of_nonneg_right hC hXP
    _ = _ := by ring

/-- `t = 0`: `Θ̊_0 = 1_{a=0} - L^{-d}`, `|Θ̊_0(0,a)| ≤ (1 + P_d)(n+1)^{-(d-2)}`. -/
private lemma p5h_zero8 (d L : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) {Λ g : ℝ} (hg : 0 < g)
    (hgΛ : g ≤ Λ) (a : Zd d L) {C : ℝ} (hC : (Λ ^ 2 + 1) * (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) ≤ C) :
    ‖Theta0 d L g (((0 : ℝ) : ℂ)) 0 a‖
      ≤ C * (g ^ 2 + |1 - (0 : ℝ)|)⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
  have hd2 : 2 ≤ d := by omega
  have hξ : ‖((0 : ℝ) : ℂ)‖ < 1 := by simp
  rw [Theta0_apply_eq hL hξ, Complex.ofReal_zero]
  have hT0 : Theta d L g 0 = 1 := p5h_Theta_zero d L g
  rw [hT0]
  have hLd0 : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  have hW := p5h_Linv_le d L a (d - 2)
  have hLdW := p5h_Linv_d_le d L hd2
  have hP : 0 < ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hPd : 0 ≤ ((d : ℝ) / 2 + 1) ^ (d - 2) := by positivity
  -- the indicator is at most `P`
  have hind : ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 a‖
      ≤ ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
    by_cases ha : a = 0
    · subst ha
      simp
    · rw [Matrix.one_apply_ne (Ne.symm ha)]
      simpa using hP.le
  have hnorm : ‖((L : ℂ) ^ d)⁻¹ * (1 - 0)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by
    simp [norm_inv, norm_pow]
  have h1 : ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 a - ((L : ℂ) ^ d)⁻¹ * (1 - 0)⁻¹‖
      ≤ (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
    refine (norm_sub_le _ _).trans ?_
    rw [hnorm]
    calc ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) 0 a‖ + ((L : ℝ) ^ d)⁻¹
        ≤ ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
          + ((d : ℝ) / 2 + 1) ^ (d - 2) * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
          add_le_add hind (hLdW.trans hW)
      _ = _ := by ring
  refine h1.trans ?_
  have habs : |1 - (0 : ℝ)| = 1 := by simp
  rw [habs]
  have hg2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
  have hY : (1 : ℝ) ≤ (Λ ^ 2 + 1) * (g ^ 2 + 1)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
  have h2 : (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) ≤ C * (g ^ 2 + 1)⁻¹ := by
    have : (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) * 1
        ≤ (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) * ((Λ ^ 2 + 1) * (g ^ 2 + 1)⁻¹) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    calc (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) = (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) * 1 := by ring
      _ ≤ _ := this
      _ = ((Λ ^ 2 + 1) * (1 + ((d : ℝ) / 2 + 1) ^ (d - 2))) * (g ^ 2 + 1)⁻¹ := by ring
      _ ≤ C * (g ^ 2 + 1)⁻¹ := mul_le_mul_of_nonneg_right hC (by positivity)
  calc (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
      ≤ (C * (g ^ 2 + 1)⁻¹) * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
        mul_le_mul_of_nonneg_right h2 hP.le
    _ = _ := rfl

/-! ### Property 8, `σ₁ = σ₂`: `prop5Short_holds` and the gap `|1 - tμ| ≥ κ²` -/

/-- `|1 - xμ|² = (1-x)² + 4x (Im m)²` for `μ = m(σ)²`, `‖m‖ = 1`. -/
private theorem p5h_gap_sq (m : ℂ) (hm : ‖m‖ = 1) (σ : Bool) (x : ℝ) :
    ‖1 - (x : ℂ) * (PropSpin m σ * PropSpin m σ)‖ ^ 2 = (1 - x) ^ 2 + 4 * x * m.im ^ 2 := by
  have hm2 : m.re ^ 2 + m.im ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hm
    simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    nlinarith [h]
  rw [Complex.sq_norm, Complex.normSq_apply]
  cases σ
  · simp only [PropSpin, Bool.false_eq_true, ite_false, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_im, Complex.one_im, Complex.mul_im]
    linear_combination (-2 * x + x ^ 2 * (m.re ^ 2 + m.im ^ 2 + 1)) * hm2
  · simp only [PropSpin, ite_true, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
    linear_combination (-2 * x + x ^ 2 * (m.re ^ 2 + m.im ^ 2 + 1)) * hm2

/-- `κ² ≤ |1 - tμ|` for `μ = m(σ)²`, `κ ≤ Im m`, `0 < κ ≤ 1`, `t ∈ [0,1]`. -/
private lemma p5h_gap_lower {κ t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ht0 : 0 ≤ t)
    {m : ℂ} (hm : ‖m‖ = 1) (hκm : κ ≤ m.im) (σ : Bool) :
    κ ^ 2 ≤ ‖1 - (t : ℂ) * (PropSpin m σ * PropSpin m σ)‖ := by
  have h := p5h_gap_sq m hm σ t
  have him : κ ^ 2 ≤ m.im ^ 2 := pow_le_pow_left₀ hκ.le hκm 2
  have hu : κ ^ 2 ≤ 1 := pow_le_one₀ hκ.le hκ1
  have hu0 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have h2 : (κ ^ 2) ^ 2 ≤ (1 - t) ^ 2 + 4 * t * κ ^ 2 := by
    nlinarith [sq_nonneg (1 - t - κ ^ 2), mul_nonneg hu0 (sub_nonneg.mpr hu), mul_nonneg hu0 ht0]
  have h3 : (κ ^ 2) ^ 2 ≤ ‖1 - (t : ℂ) * (PropSpin m σ * PropSpin m σ)‖ ^ 2 := by
    rw [h]; nlinarith [mul_nonneg ht0 (sub_nonneg.mpr him)]
  by_contra hcon
  push Not at hcon
  have := norm_nonneg (1 - (t : ℂ) * (PropSpin m σ * PropSpin m σ))
  nlinarith

/-- **Property 8, `σ₁ = σ₂`** (bulk `κ ≤ Im m`): from
`|Θ_{tμ}(0,a)| ≤ C_s (1_{a=0} + g² e^{-c_s n})` (`prop5Short_holds`), `|1 - tμ| ≥ κ²`,
`Θ̊ = Θ - L^{-d}(1 - tμ)⁻¹`. -/
private lemma p5h_sigma_eq (d L : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L)
    {Λ κ g t cs Cs : ℝ} (hκ : 0 < κ) (hg : 0 < g) (hgΛ : g ≤ Λ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hCs : 0 ≤ Cs) (hcs : 0 < cs) {m : ℂ} (hm : ‖m‖ = 1) (hκm : κ ≤ m.im) (σ : Bool)
    (a : Zd d L)
    (hSa : ‖Theta d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖
      ≤ Cs * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-cs * (zdistD d L a : ℝ))))
    {C : ℝ} (hC : Cs * (Λ ^ 2 + 1)
      + Cs * (Λ ^ 2 * (Λ ^ 2 + 1)) * (((d - 2).factorial : ℝ) * (1 / cs) ^ (d - 2) * Real.exp cs)
      + (κ ^ 2)⁻¹ * ((d : ℝ) / 2 + 1) ^ (d - 2) * (Λ ^ 2 + 1) ≤ C) :
    ‖Theta0 d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖
      ≤ C * (g ^ 2 + |1 - t|)⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
  have hd2 : 2 ≤ d := by omega
  have hμ := p5h_norm_mu m hm σ σ
  have hξ : ‖(t : ℂ) * (PropSpin m σ * PropSpin m σ)‖ < 1 := norm_t_mul_lt_one ht0 ht1 hμ
  rw [Theta0_apply_eq hL hξ]
  have hκ1 : κ ≤ 1 := hκm.trans ((Complex.im_le_norm m).trans hm.le)
  have hgap := p5h_gap_lower hκ hκ1 ht0 hm hκm σ
  have hκ2 : 0 < κ ^ 2 := by positivity
  set n : ℝ := (zdistD d L a : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have habs : |1 - t| = 1 - t := abs_of_pos (by linarith)
  rw [habs]
  have he0 : 0 < 1 - t := by linarith
  have hY0 : 0 < (g ^ 2 + (1 - t))⁻¹ := by positivity
  have hP0 : 0 < ((n + 1) ^ (d - 2))⁻¹ := by positivity
  have hg2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
  have hsum : g ^ 2 + (1 - t) ≤ Λ ^ 2 + 1 := by linarith
  have hspos : 0 < g ^ 2 + (1 - t) := by positivity
  -- `1 ≤ (Λ²+1) Y` and `g² ≤ Λ²(Λ²+1) Y`
  have hY1 : (1 : ℝ) ≤ (Λ ^ 2 + 1) * (g ^ 2 + (1 - t))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hspos]; linarith
  have hY2 : g ^ 2 ≤ Λ ^ 2 * (Λ ^ 2 + 1) * (g ^ 2 + (1 - t))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hspos]
    nlinarith [sq_nonneg g, sq_nonneg Λ]
  -- the three pieces
  have hind : (if a = 0 then (1 : ℝ) else 0) ≤ ((n + 1) ^ (d - 2))⁻¹ := by
    by_cases ha : a = 0
    · subst ha; simp [hn]
    · simpa [ha] using hP0.le
  have hexp : Real.exp (-cs * n) ≤ (((d - 2).factorial : ℝ) * (1 / cs) ^ (d - 2) * Real.exp cs)
      * ((n + 1) ^ (d - 2))⁻¹ := by
    have hpoly := p5h_poly_exp_le hcs (d - 2) hn0
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hpoly
  have hLdW := p5h_Linv_d_le d L hd2
  have hW := p5h_Linv_le d L a (d - 2)
  set Ms : ℝ := ((d - 2).factorial : ℝ) * (1 / cs) ^ (d - 2) * Real.exp cs with hMs
  have hMs0 : 0 ≤ Ms := by positivity
  set Pd : ℝ := ((d : ℝ) / 2 + 1) ^ (d - 2) with hPd
  have hPd0 : 0 ≤ Pd := by positivity
  set P : ℝ := ((n + 1) ^ (d - 2))⁻¹ with hP
  set Y : ℝ := (g ^ 2 + (1 - t))⁻¹ with hY
  have hnorm : ‖((L : ℂ) ^ d)⁻¹ * (1 - (t : ℂ) * (PropSpin m σ * PropSpin m σ))⁻¹‖
      ≤ (κ ^ 2)⁻¹ * (Pd * P) := by
    rw [norm_mul, norm_inv, norm_inv, norm_pow, Complex.norm_natCast]
    have h1 : ((L : ℝ) ^ d)⁻¹ ≤ Pd * P := hLdW.trans hW
    have h2 : ‖1 - (t : ℂ) * (PropSpin m σ * PropSpin m σ)‖⁻¹ ≤ (κ ^ 2)⁻¹ :=
      inv_anti₀ hκ2 hgap
    calc ((L : ℝ) ^ d)⁻¹ * ‖1 - (t : ℂ) * (PropSpin m σ * PropSpin m σ)‖⁻¹
        ≤ (Pd * P) * (κ ^ 2)⁻¹ := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  refine (norm_sub_le _ _).trans ?_
  have hA1 : ‖Theta d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖
      ≤ Cs * ((Λ ^ 2 + 1) * Y * P) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * Y * (Ms * P)) := by
    refine hSa.trans ?_
    have h3 : g ^ 2 * Real.exp (-cs * n) ≤ (Λ ^ 2 * (Λ ^ 2 + 1) * Y) * (Ms * P) :=
      mul_le_mul hY2 hexp (Real.exp_pos _).le (by positivity)
    have h4 : (if a = 0 then (1 : ℝ) else 0) ≤ (Λ ^ 2 + 1) * Y * P := by
      refine hind.trans ?_
      calc P = 1 * P := (one_mul _).symm
        _ ≤ ((Λ ^ 2 + 1) * Y) * P := mul_le_mul_of_nonneg_right hY1 hP0.le
    calc Cs * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-cs * n))
        ≤ Cs * ((Λ ^ 2 + 1) * Y * P + (Λ ^ 2 * (Λ ^ 2 + 1) * Y) * (Ms * P)) :=
          mul_le_mul_of_nonneg_left (add_le_add h4 h3) hCs
      _ = _ := by ring
  have hA2 : (κ ^ 2)⁻¹ * (Pd * P) ≤ (κ ^ 2)⁻¹ * (Pd * ((Λ ^ 2 + 1) * Y * P)) := by
    have : Pd * P ≤ Pd * ((Λ ^ 2 + 1) * Y * P) := by
      apply mul_le_mul_of_nonneg_left _ hPd0
      calc P = 1 * P := (one_mul _).symm
        _ ≤ ((Λ ^ 2 + 1) * Y) * P := mul_le_mul_of_nonneg_right hY1 hP0.le
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hXP : 0 ≤ Y * P := by positivity
  calc _ ≤ Cs * ((Λ ^ 2 + 1) * Y * P) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * Y * (Ms * P))
        + (κ ^ 2)⁻¹ * (Pd * ((Λ ^ 2 + 1) * Y * P)) := add_le_add hA1 (hnorm.trans hA2)
    _ = (Cs * (Λ ^ 2 + 1) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1)) * Ms + (κ ^ 2)⁻¹ * Pd * (Λ ^ 2 + 1))
          * (Y * P) := by ring
    _ ≤ C * (Y * P) := mul_le_mul_of_nonneg_right hC hXP
    _ = _ := by ring

/-- `PropSpin m σ₁ · PropSpin m σ₂ = |m|² = 1` for opposite signs. -/
private lemma p5h_mu_one (m : ℂ) (hm : ‖m‖ = 1) {σ₁ σ₂ : Bool} (h : σ₁ ≠ σ₂) :
    PropSpin m σ₁ * PropSpin m σ₂ = 1 := by
  cases σ₁ <;> cases σ₂
  · exact absurd rfl h
  · simp only [PropSpin, Bool.false_eq_true, ite_false, ite_true]
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]; simp
  · simp only [PropSpin, Bool.false_eq_true, ite_false, ite_true]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]; simp
  · exact absurd rfl h

/-- **`(prop:ThfadC0)`** (property 8 of `lem_propTH`) for every `d ≥ 3`, `Λ > 0`, `κ > 0`:
`|Θ̊_t(0,a)| ≤ C (g²+|1-t|)⁻¹ (|a|+1)^{-(d-2)}`, `C` depending on `(d, Λ, κ)` only.
`σ₁ ≠ σ₂` (`μ = 1`): `t = 0` by `Θ = 1`, `0 < t < 1` by the zero-mode-removed Laplace representation
(`e^{-ετ}` kept on the `L^{-d}` piece, Fable F5 (d)); `σ₁ = σ₂` (bulk `κ ≤ Im m`):
`prop5Short_holds` and `|1 - tμ| ≥ κ²`.  No unproved input. -/
theorem prop8ZeroMode_holds (d : ℕ) (Λ κ : ℝ) : Prop8ZeroMode d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨CK, cK, hCK, hcK, hK⟩ := kProd_le d (by omega)
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := kProd_gap d (by omega)
  obtain ⟨CB, hCB, c', hc', hB⟩ := lg_bulk d hd cK hcK
  obtain ⟨CA, hCA, hA⟩ := lg_convA d Λ hΛ
  obtain ⟨Cs, hCs, cs, hcs, hS⟩ := prop5Short_holds d Λ κ hd hΛ hκ
  have hPd0 : 0 ≤ ((d : ℝ) / 2 + 1) ^ (d - 2) := by positivity
  have hCh0 := p5hCh_nonneg hd hCK.le hCA.le hCB.le hc'
  have hK1 : 0 ≤ p5hCh d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
      + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2) := by positivity
  have hK2 : 0 < (Λ ^ 2 + 1) * (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) := by positivity
  have hK3 : 0 ≤ Cs * (Λ ^ 2 + 1)
      + Cs * (Λ ^ 2 * (Λ ^ 2 + 1)) * (((d - 2).factorial : ℝ) * (1 / cs) ^ (d - 2) * Real.exp cs)
      + (κ ^ 2)⁻¹ * ((d : ℝ) / 2 + 1) ^ (d - 2) * (Λ ^ 2 + 1) := by positivity
  refine ⟨(p5hCh d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
      + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2))
    + (Λ ^ 2 + 1) * (1 + ((d : ℝ) / 2 + 1) ^ (d - 2))
    + (Cs * (Λ ^ 2 + 1)
      + Cs * (Λ ^ 2 * (Λ ^ 2 + 1)) * (((d - 2).factorial : ℝ) * (1 / cs) ^ (d - 2) * Real.exp cs)
      + (κ ^ 2)⁻¹ * ((d : ℝ) / 2 + 1) ^ (d - 2) * (Λ ^ 2 + 1)), by linarith, ?_⟩
  intro L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ a
  have : NeZero L := ⟨by omega⟩
  by_cases hσ : σ₁ = σ₂
  · subst hσ
    exact p5h_sigma_eq d L hd hL hκ hg hgΛ ht0 ht1 hCs.le hcs hm hκm σ₁ a
      (hS L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ a) (by linarith)
  · rw [p5h_mu_one m hm hσ, mul_one]
    rcases ht0.eq_or_lt with h0 | h0
    · subst h0
      exact p5h_zero8 d L hd hL hg hgΛ a (by linarith)
    · rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
      exact p5h_core8 d hd hCK hCG hcG hCB hc' hCA hK
        (fun L _ τ hτ a => (hG L τ hτ a ⟨0, by omega⟩ ⟨0, by omega⟩).1) hB hA L hL g hg hgΛ t
        h0 ht1 a (by linarith)

/-! ### The theorems are the pinned statements -/

example (d : ℕ) (Λ : ℝ) : Prop5Decay d Λ := prop5Decay_holds d Λ

example (d : ℕ) (Λ κ : ℝ) : Prop8ZeroMode d Λ κ := prop8ZeroMode_holds d Λ κ

/-! ### Compiled nonempty instances

`prop5Decay_holds 3 1` and `prop8ZeroMode_holds 3 1 (1/2)` applied at `L = 5`, `g = 1/2`,
`t = 9/10`, `m = I` (`‖I‖ = 1`, `1/2 ≤ Im I = 1`), `σ₁ = true`, `σ₂ = false` (so `μ = m m̄ = 1`), at
`a = 0` and at `a = (1, 0, 0) ≠ 0`, `|a| = 1`; P8 also at `σ₁ = σ₂ = true` (`μ = m²`, the
`prop5Short_holds` branch).  Every hypothesis is discharged (`3 ≤ d`, `0 < Λ`, `0 < κ`, `3 ≤ L`,
`0 < g ≤ Λ`, `0 ≤ t < 1`, `‖m‖ = 1`, `κ ≤ Im m`); the constants `C`, `c` stay existential, as in
the statements. -/

example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
        0 0‖
      ≤ C * Bparam 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (0 : Zd 3 5))
        * Real.exp (-c * (zdistD 3 5 (0 : Zd 3 5) : ℝ) / ellT 5 (1 / 2) (9 / 10)) := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Decay_holds 3 1 (by norm_num) (by norm_num)
  exact ⟨C, hC, c, hc, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) Complex.I Complex.norm_I true false 0⟩

example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ (![1, 0, 0] : Zd 3 5) ≠ 0 ∧
    zdistD 3 5 (![1, 0, 0] : Zd 3 5) = 1 ∧
    ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
        0 ![1, 0, 0]‖
      ≤ C * Bparam 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (![1, 0, 0] : Zd 3 5))
        * Real.exp (-c * (zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℝ) / ellT 5 (1 / 2) (9 / 10)) := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Decay_holds 3 1 (by norm_num) (by norm_num)
  exact ⟨C, hC, c, hc, by decide, by decide, H 5 (by norm_num) (1 / 2) (by norm_num)
    (by norm_num) (9 / 10) (by norm_num) (by norm_num) Complex.I Complex.norm_I true false
    ![1, 0, 0]⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖Theta0 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
        0 0‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - (9 / 10 : ℝ)|)⁻¹
        * (((zdistD 3 5 (0 : Zd 3 5) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop8ZeroMode_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false 0⟩

example : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 5) ≠ 0 ∧
    zdistD 3 5 (![1, 0, 0] : Zd 3 5) = 1 ∧
    ‖Theta0 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
        0 ![1, 0, 0]‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - (9 / 10 : ℝ)|)⁻¹
        * (((zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop8ZeroMode_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, by decide, by decide, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    (9 / 10) (by norm_num) (by norm_num) Complex.I Complex.norm_I (by norm_num) true false
    ![1, 0, 0]⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖Theta0 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
        0 ![1, 0, 0]‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - (9 / 10 : ℝ)|)⁻¹
        * (((zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop8ZeroMode_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true true ![1, 0, 0]⟩

/-- The zero-mode regime `ε < L⁻²`: `t = 999/1000` (`ε ≈ 0.01 < L⁻² = 0.04`, `ℓ_t = L`), at a point
`a = (2, 1, 0)` with `|a| = 3`; the same two theorems, no change of hypotheses. -/
example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ zdistD 3 5 (![2, 1, 0] : Zd 3 5) = 3 ∧
    ‖Theta 3 5 (1 / 2) (((999 / 1000 : ℝ) : ℂ)
        * (PropSpin Complex.I true * PropSpin Complex.I false)) 0 ![2, 1, 0]‖
      ≤ C * Bparam 3 5 (1 / 2) (999 / 1000) (zdistD 3 5 (![2, 1, 0] : Zd 3 5))
        * Real.exp (-c * (zdistD 3 5 (![2, 1, 0] : Zd 3 5) : ℝ) / ellT 5 (1 / 2) (999 / 1000)) := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Decay_holds 3 1 (by norm_num) (by norm_num)
  exact ⟨C, hC, c, hc, by decide, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    (999 / 1000) (by norm_num) (by norm_num) Complex.I Complex.norm_I true false ![2, 1, 0]⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖Theta0 3 5 (1 / 2) (((999 / 1000 : ℝ) : ℂ)
        * (PropSpin Complex.I true * PropSpin Complex.I false)) 0 ![2, 1, 0]‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - (999 / 1000 : ℝ)|)⁻¹
        * (((zdistD 3 5 (![2, 1, 0] : Zd 3 5) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop8ZeroMode_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (999 / 1000) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false ![2, 1, 0]⟩

/-- Three of the five fields of the bundle `Prop5to8` are now proved
(`Prop5Decay`, `Prop5Short`, `Prop8ZeroMode`); `Prop6Diff1`, `Prop7Diff2` stay hypotheses. -/
example (h6 : Prop6Diff1 3 1 (1 / 2) (1 / 2)) (h7 : Prop7Diff2 3 1 (1 / 2) (1 / 2)) :
    Prop5to8 3 1 (1 / 2) (1 / 2) :=
  ⟨prop5Decay_holds 3 1, prop5Short_holds 3 1 (1 / 2), h6, h7, prop8ZeroMode_holds 3 1 (1 / 2)⟩

/-- The merged consumer interfaces `ThetaDecay` and `ThetaZeroMode` follow from the proved pins. -/
example : ThetaDecay 3 (1 / 2) Complex.I := (prop5Decay_holds 3 (1 / 2)).thetaDecay Complex.I

example : ThetaZeroMode 3 (1 / 2) (PropSpin Complex.I true * PropSpin Complex.I false) :=
  (prop8ZeroMode_holds 3 1 (1 / 2)).thetaZeroMode (by norm_num) (by norm_num) (by norm_num)
    Complex.norm_I (by norm_num) true false

end RBM
