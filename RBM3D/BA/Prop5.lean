/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KHeatTail
import RBM3D.BA.FlowPins
import RBM3D.Propagator.Prop5Hold

/-!
# Properties 5 and 8 of `lem_propTH` for `Θ_BA`, mixed charges `σ₁ ≠ σ₂` (BA-P5)

Ticket T2337.  `baProp5mixed_holds` and `baProp8mixed_holds`: the pins `BAProp5` and `BAProp8`
(`BA/FlowPins.lean:171`, `:215`) restricted to `σ₁ ≠ σ₂`, by porting `Propagator/Prop5Hold.lean`
(`prop5Decay_holds :784`, `prop8ZeroMode_holds :1266`) with the substitutions
`kProd d L τ ↦ kBA d L g E m τ`, `lgGam d g t ↦ γ = t g²`, `Theta_eq_laplace_prod ↦
BATheta_eq_laplace_kBA`, `kProd_le ↦ kBA_le`, `kProd_gap ↦ kBA_gap`.

For `σ₁ ≠ σ₂` the matrix is `K = BAK` (`BAMss_pm_eq`, `BAMss_mp_eq`), real and nonnegative, so
`Θ = PropThetaQ (map K ofReal) t` is a nonnegative real kernel and the band's reduction
(property 4, `‖Θ_{tμ}‖ ≤ Re Θ_t`) is not needed.

Notation: `e = 1 - t`, `γ = t g²`, `ε = e / γ`, `n = zdistD d L a`, `ℓ = ellT L g t`, `T = L²`.

* **Representation** (`BATheta_eq_laplace_kBA`, `τ = γ s`): for `0 < t < 1`,
  `Θ_t(0,a) = γ⁻¹ ∫₀^∞ e^{-ετ} kBA(τ, a) dτ`, split at `τ = L²`.
* **Head** `(0, L²]`: `kBA_le` and `lg_bulk` (`n ≥ 1`), `lg_zero` (`n = 0`).
* **Tail** `(L², ∞)`: `kBA ≤ (1 + C) L^{-d}` (`kBA_gap`) and `∫_{L²}^∞ e^{-ετ} = e^{-εL²}/ε`.
* **Regimes by `ε`** (not by `e ≷ g²`): `ε ≥ 1`, `L⁻² ≤ ε < 1`, `ε < L⁻²`, `n = 0`; the conversions
  `baP5_convA` (`Λ` enters, `C_A = 3 + 2Λ²`), `baP5_convB`, `baP5_convC` are the band's
  `lg_convA/B/C` restated for `γ = t g²` (the band `γ = t g² / (1 + 2dg²)`).
* **Property 8**: `Θ̊_t(0,a) = Θ_t(0,a) - L^{-d} (1-t)⁻¹` (all rows of `Θ` sum to `(1-t)⁻¹`, Neumann
  series of `K`), then `Θ̊_t(0,a) = γ⁻¹ ∫ e^{-ετ} (kBA(τ,a) - L^{-d}) dτ` with `e^{-ετ}` kept on the
  `L^{-d}` piece.

Constants depend on `(d, Λ, κ)` only.  No unproved input.  The private helpers of the merged band
file `RBM3D/Propagator/Prop5Hold.lean` are copied under the prefix `baP5_` (nothing is imported from
`RBM1D` or `RBM2D`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Set

namespace RBM.BA

open RBM RBM.Gauss RBM.Heat

/-! ## 1. The pins (mixed charges) -/

/-- **Property 5, mixed charges** (`BAProp5` with `σ₁ ≠ σ₂`). -/
def BAProp5mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ a : Zd d L,
          ‖BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- **Property 8, mixed charges** (`BAProp8` with `σ₁ ≠ σ₂`). -/
def BAProp8mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ a : Zd d L,
          ‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

/-! ## 2. `γ`, `ε`, the kernel in `τ`, and the Laplace representation -/

/-- `γ = t g²`: the diffusion constant of `1 - tK` in the time `τ = γ s` (the band has
`t g² / (1 + 2dg²)`). -/
private noncomputable def baP5Gam (g t : ℝ) : ℝ := t * g ^ 2

/-- `ε = e / γ`, the parameter that decides the regime. -/
private noncomputable def baP5Eps (g t : ℝ) : ℝ := (1 - t) / baP5Gam g t

private lemma baP5_gam_pos {g t : ℝ} (hg : 0 < g) (ht : 0 < t) : 0 < baP5Gam g t := by
  unfold baP5Gam; positivity

private lemma baP5_eps_pos {g t : ℝ} (hg : 0 < g) (ht : 0 < t) (ht1 : t < 1) :
    0 < baP5Eps g t := by
  unfold baP5Eps
  exact div_pos (by linarith) (baP5_gam_pos hg ht)

private lemma baP5_gam_mul_eps {g t : ℝ} (hg : 0 < g) (ht : 0 < t) :
    baP5Gam g t * baP5Eps g t = 1 - t := by
  have := (baP5_gam_pos hg ht).ne'
  unfold baP5Eps
  field_simp

private lemma baP5_gam_le {g t : ℝ} (ht1 : t < 1) (ht : 0 < t) : baP5Gam g t ≤ g ^ 2 := by
  unfold baP5Gam
  nlinarith [sq_nonneg g]

private lemma baP5_kBA_bounds {d L : ℕ} [NeZero L] {g E : ℝ} {m : ℂ} (hg : 0 < g)
    (hS : BASelf d L g (E : ℂ) m) {τ : ℝ} (hτ : 0 ≤ τ) (a : Zd d L) :
    0 ≤ kBA d L g E m τ a ∧ kBA d L g E m τ a ≤ 1 := by
  obtain ⟨h0, -, h1, -⟩ := kBA_basic d L g E m hg hS
  exact ⟨h0 τ hτ a, h1 τ hτ a⟩

private lemma baP5_kBA_continuous {d L : ℕ} [NeZero L] {g E : ℝ} {m : ℂ} (hg : 0 < g)
    (hS : BASelf d L g (E : ℂ) m) (a : Zd d L) :
    Continuous (fun τ : ℝ => kBA d L g E m τ a) :=
  (kBA_basic d L g E m hg hS).2.2.2.2.2 a

/-- `e^{-ετ} kBA(τ, a)` is integrable on `(0, ∞)` for `ε > 0`. -/
private lemma baP5_F_integrable {d L : ℕ} [NeZero L] {g E : ℝ} {m : ℂ} (hg : 0 < g)
    (hS : BASelf d L g (E : ℂ) m) {ε : ℝ} (hε : 0 < ε) (a : Zd d L) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a) (Ioi 0) := by
  have hg' : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hc := baP5_kBA_continuous hg hS a
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a)
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a).aestronglyMeasurable
  refine Integrable.mono' hg' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hτ' : 0 ≤ τ := le_of_lt hτ
  obtain ⟨h0, h1⟩ := baP5_kBA_bounds hg hS hτ' a
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h0)]
  calc Real.exp (-ε * τ) * kBA d L g E m τ a ≤ Real.exp (-ε * τ) * 1 :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := mul_one _

/-- For `σ₁ ≠ σ₂` both mixed charges give the matrix `K` (`BAMss_pm_eq`, `BAMss_mp_eq`). -/
private lemma baP5_Theta_mixed (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ) {σ₁ σ₂ : Bool}
    (h : σ₁ ≠ σ₂) : BATheta d L g E m t σ₁ σ₂ = BATheta d L g E m t true false := by
  cases σ₁ <;> cases σ₂
  · exact absurd rfl h
  · unfold BATheta
    rw [BAMss_mp_eq, BAMss_pm_eq]
  · rfl
  · exact absurd rfl h

private lemma baP5_Theta_zero (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) :
    BATheta d L g E m 0 σ₁ σ₂ = 1 := by
  simp [BATheta, PropThetaQ]

/-- `Θ_t(0,a) = γ⁻¹ ∫₀^∞ e^{-ετ} kBA(τ,a) dτ`: `BATheta_eq_laplace_kBA` and `τ = γ s`. -/
private lemma baP5_theta_eq (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g E : ℝ) (m : ℂ) (t : ℝ)
    (hg : 0 < g) (hS : BASelf d L g (E : ℂ) m) (ht0 : 0 < t) (ht1 : t < 1) (a : Zd d L) :
    BATheta d L g E m t true false 0 a =
      (((baP5Gam g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a
        : ℝ) : ℂ) := by
  rw [BATheta_eq_laplace_kBA d L hL g E m t hg hS ht0.le ht1 a]
  congr 1
  have hγ := baP5_gam_pos hg ht0
  have key := integral_comp_mul_left_Ioi
    (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a) 0 hγ
  rw [mul_zero] at key
  simp only [smul_eq_mul] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  have h1 : -(baP5Eps g t) * (baP5Gam g t * s) = -(1 - t) * s := by
    rw [← baP5_gam_mul_eps hg ht0]; ring
  rw [h1]
  rfl

/-! ## 3. The conversions `ε`, `γ`, `ℓ` for `γ = t g²` (the band's `lg_convA/B/C` restated) -/

/-- (L3) = Fable F5 (a) for `γ = t g²`: `min(1/e, 1/γ) ≤ C_Λ/(g² + e)`, `C_Λ = 3 + 2Λ²`.  Regime
`ε ≥ 1` (`e ≥ γ`) uses `1/e`, regime `ε < 1` uses `1/γ` (and `t > (1 + Λ²)⁻¹` there). -/
private lemma baP5_convA (Λ : ℝ) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧
    ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ baP5Eps g t → 1 / (1 - t) ≤ C / (g ^ 2 + (1 - t))) ∧
      (baP5Eps g t < 1 → 1 / baP5Gam g t ≤ C / (g ^ 2 + (1 - t))) := by
  refine ⟨3 + 2 * Λ ^ 2, by positivity, ?_⟩
  intro g t hg hgΛ ht ht1
  have hγ := baP5_gam_pos hg ht
  have he : 0 < 1 - t := by linarith
  have hG : 0 < g ^ 2 := by positivity
  have hGP : g ^ 2 ≤ Λ ^ 2 := by nlinarith
  have hΛ2 : 0 ≤ Λ ^ 2 := sq_nonneg Λ
  constructor
  · intro h1
    have h2 : baP5Gam g t ≤ 1 - t := by
      unfold baP5Eps at h1
      rwa [le_div_iff₀ hγ, one_mul] at h1
    have h2' : t * g ^ 2 ≤ 1 - t := h2
    rw [div_le_div_iff₀ he (by positivity)]
    rcases le_or_gt (1 / 2) t with ht2 | ht2
    · have h3 : g ^ 2 ≤ 2 * (1 - t) := by nlinarith
      nlinarith [mul_nonneg hΛ2 he.le]
    · nlinarith [mul_nonneg hΛ2 (by linarith : (0 : ℝ) ≤ (1 - t) - 1 / 2)]
  · intro h1
    have h2 : 1 - t < baP5Gam g t := by
      unfold baP5Eps at h1
      rwa [div_lt_one hγ] at h1
    have h2' : 1 - t < t * g ^ 2 := h2
    rw [div_le_div_iff₀ hγ (by positivity)]
    have h4 : 1 < t * (1 + Λ ^ 2) := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hGP)]
    have h5 : g ^ 2 + (1 - t) < 2 * g ^ 2 := by nlinarith
    have h6 : 0 < g ^ 2 * (t * (1 + Λ ^ 2) - 1) := mul_pos hG (by linarith)
    have h7 : baP5Gam g t = t * g ^ 2 := rfl
    rw [h7]
    nlinarith [mul_pos hG ht]

/-- `ε^{-1/2} ≤ g/√e`, the common core of `convB`, `convC` and `convB`, `convC` themselves (the
band's `lg_sqrt_eps_inv_le`, `lg_ell_inv_le`, `lg_convB`, `lg_convC`; only `0 < γ ≤ g²` is used). -/
private lemma baP5_sqrt_eps_inv_le {g t : ℝ} (hg : 0 < g) (ht : 0 < t) (ht1 : t < 1) :
    1 / Real.sqrt (baP5Eps g t) ≤ g / Real.sqrt |1 - t| := by
  have hε := baP5_eps_pos hg ht ht1
  have he : 0 < 1 - t := by linarith
  have habs : |1 - t| = 1 - t := abs_of_pos he
  rw [habs]
  have hγ := baP5_gam_pos hg ht
  have hγg := baP5_gam_le (g := g) ht1 ht
  have h1 : 1 - t ≤ baP5Eps g t * g ^ 2 := by
    unfold baP5Eps
    rw [div_mul_eq_mul_div, le_div_iff₀ hγ]
    nlinarith
  have h2 : Real.sqrt (1 - t) ≤ Real.sqrt (baP5Eps g t) * g := by
    calc Real.sqrt (1 - t) ≤ Real.sqrt (baP5Eps g t * g ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (baP5Eps g t) * g := by
        rw [Real.sqrt_mul hε.le, Real.sqrt_sq hg.le]
  have hse : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr he
  have hsε : 0 < Real.sqrt (baP5Eps g t) := Real.sqrt_pos.mpr hε
  rw [div_le_div_iff₀ hsε hse]
  linarith

/-- The common core of (L3b) and (L3c). -/
private lemma baP5_ell_inv_le (L : ℕ) {g t : ℝ} (hL : 1 ≤ L) (hg : 0 < g) (ht : 0 < t)
    (ht1 : t < 1) (h : ((L : ℝ)⁻¹) ^ 2 ≤ baP5Eps g t) :
    (ellT L g t)⁻¹ ≤ Real.sqrt (baP5Eps g t) := by
  have hε := baP5_eps_pos hg ht ht1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsε : 0 < Real.sqrt (baP5Eps g t) := Real.sqrt_pos.mpr hε
  have hLs : (L : ℝ)⁻¹ ≤ Real.sqrt (baP5Eps g t) := by
    rw [Real.le_sqrt (by positivity) hε.le]; exact h
  have h1 : 1 / Real.sqrt (baP5Eps g t) ≤ ellT L g t := by
    refine le_min (le_max_of_le_left (baP5_sqrt_eps_inv_le hg ht ht1)) ?_
    rw [one_div]
    exact (inv_le_comm₀ hsε hLpos).mpr hLs
  rw [one_div] at h1
  have hpos : 0 < ellT L g t := lt_of_lt_of_le (inv_pos.mpr hsε) h1
  exact (inv_le_comm₀ hpos hsε).mpr h1

private lemma baP5_convB : ∀ (L : ℕ) (g t : ℝ), 1 ≤ L → 0 < g → 0 < t → t < 1 →
    (((L : ℝ)⁻¹) ^ 2 ≤ baP5Eps g t → (ellT L g t)⁻¹ ≤ Real.sqrt (baP5Eps g t)) ∧
    (baP5Eps g t < ((L : ℝ)⁻¹) ^ 2 → ellT L g t = (L : ℝ)) := by
  intro L g t hL hg ht ht1
  refine ⟨baP5_ell_inv_le L hL hg ht ht1, ?_⟩
  intro h
  have hε := baP5_eps_pos hg ht ht1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsε : 0 < Real.sqrt (baP5Eps g t) := Real.sqrt_pos.mpr hε
  have hLs : Real.sqrt (baP5Eps g t) < (L : ℝ)⁻¹ := by
    rw [Real.sqrt_lt' (by positivity)]; exact h
  have h1 : (L : ℝ) < 1 / Real.sqrt (baP5Eps g t) := by
    rw [one_div]
    exact (lt_inv_comm₀ hLpos hsε).mpr hLs
  have h2 : (L : ℝ) ≤ max (g / Real.sqrt |1 - t|) 1 :=
    le_max_of_le_left (h1.le.trans (baP5_sqrt_eps_inv_le hg ht ht1))
  unfold ellT
  exact min_eq_right h2

private lemma baP5_convC (d : ℕ) : ∀ (L : ℕ) (g t n : ℝ), 1 ≤ L → 0 < g → 0 < t → t < 1 → 0 ≤ n →
    n ≤ (d : ℝ) * (L : ℝ) / 2 → ((L : ℝ)⁻¹) ^ 2 ≤ baP5Eps g t →
      n / ellT L g t ≤ (d : ℝ) / 2 * (baP5Eps g t * (L : ℝ) ^ 2) := by
  intro L g t n hL hg ht ht1 hn hnd h
  have hε := baP5_eps_pos hg ht ht1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsε : 0 < Real.sqrt (baP5Eps g t) := Real.sqrt_pos.mpr hε
  have hell := baP5_ell_inv_le L hL hg ht ht1 h
  have hLs : (L : ℝ)⁻¹ ≤ Real.sqrt (baP5Eps g t) := by
    rw [Real.le_sqrt (by positivity) hε.le]; exact h
  have hx : 1 ≤ (L : ℝ) * Real.sqrt (baP5Eps g t) := by
    have := mul_le_mul_of_nonneg_left hLs hLpos.le
    rwa [mul_inv_cancel₀ hLpos.ne'] at this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc n / ellT L g t = n * (ellT L g t)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ n * Real.sqrt (baP5Eps g t) := mul_le_mul_of_nonneg_left hell hn
    _ ≤ ((d : ℝ) * L / 2) * Real.sqrt (baP5Eps g t) := mul_le_mul_of_nonneg_right hnd hsε.le
    _ = (d : ℝ) / 2 * ((L : ℝ) * Real.sqrt (baP5Eps g t)) := by ring
    _ ≤ (d : ℝ) / 2 * (((L : ℝ) * Real.sqrt (baP5Eps g t)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = (d : ℝ) / 2 * (baP5Eps g t * (L : ℝ) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hε.le]; ring
/-! ### Elementary real inequalities -/

/-- `n^{-(d-2)}` as a real power. -/
private lemma baP5_rpow_eq {d : ℕ} (hd : 2 ≤ d) {n : ℝ} (hn : 0 ≤ n) :
    n ^ (-((d : ℝ) - 2)) = (n ^ (d - 2))⁻¹ := by
  have : -((d : ℝ) - 2) = -((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd]; push_cast; ring
  rw [this, Real.rpow_neg hn, Real.rpow_natCast]

private lemma baP5_inv_pow_le {n : ℝ} (hn : 1 ≤ n) (k : ℕ) :
    (n ^ k)⁻¹ ≤ 2 ^ k * ((n + 1) ^ k)⁻¹ := by
  have h1 : (n + 1) ^ k ≤ (2 * n) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
  rw [mul_pow] at h1
  have hn0 : 0 < n ^ k := by positivity
  have hn1 : 0 < (n + 1) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hn1, inv_mul_le_iff₀ hn0]
  linarith

/-- `(n+1)^k e^{-bn} ≤ k! b^{-k} e^b`. -/
private lemma baP5_poly_exp_le {b : ℝ} (hb : 0 < b) (k : ℕ) {n : ℝ} (hn : 0 ≤ n) :
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

private lemma baP5_zdist_le (L : ℕ) [NeZero L] (u : ZMod L) : 2 * zdist L u ≤ L := by
  have := ZMod.val_lt u
  unfold zdist
  omega

/-- `|a| ≤ dL/2`: every torus `ℓ¹` distance. -/
private lemma baP5_zdistD_le (d L : ℕ) [NeZero L] (a : Zd d L) :
    (zdistD d L a : ℝ) ≤ (d : ℝ) * (L : ℝ) / 2 := by
  have h : 2 * zdistD d L a ≤ d * L := by
    unfold zdistD
    calc 2 * ∑ i, zdist L (a i) = ∑ i, 2 * zdist L (a i) := by rw [Finset.mul_sum]
      _ ≤ ∑ _i : Fin d, L := Finset.sum_le_sum fun i _ => baP5_zdist_le L (a i)
      _ = d * L := by simp
  have h' : (2 : ℝ) * (zdistD d L a : ℝ) ≤ (d : ℝ) * (L : ℝ) := by exact_mod_cast h
  linarith

/-- `L^{-k} ≤ (d/2 + 1)^k (|a| + 1)^{-k}`, since `|a| + 1 ≤ (d/2 + 1) L`. -/
private lemma baP5_Linv_le (d L : ℕ) [NeZero L] (a : Zd d L) (k : ℕ) :
    ((L : ℝ) ^ k)⁻¹ ≤ ((d : ℝ) / 2 + 1) ^ k * ((((zdistD d L a : ℝ) + 1) ^ k)⁻¹) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hn := baP5_zdistD_le d L a
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (zdistD d L a : ℝ) + 1 ≤ ((d : ℝ) / 2 + 1) * L := by nlinarith
  have h2 : ((zdistD d L a : ℝ) + 1) ^ k ≤ (((d : ℝ) / 2 + 1) * L) ^ k :=
    pow_le_pow_left₀ (by positivity) h1 k
  rw [mul_pow] at h2
  have hLk : 0 < (L : ℝ) ^ k := by positivity
  have hnk : 0 < ((zdistD d L a : ℝ) + 1) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hnk, inv_mul_le_iff₀ hLk]
  linarith

private lemma baP5_Linv_d_le (d L : ℕ) [NeZero L] (hd : 2 ≤ d) :
    ((L : ℝ) ^ d)⁻¹ ≤ ((L : ℝ) ^ (d - 2))⁻¹ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega))

/-! ### The exponential factors: regimes of `ε` against `L⁻²` -/

/-- `e^{-b n √ε} ≤ e^{bd/2} e^{-b n/ℓ}` for `0 ≤ n ≤ dL/2`: if `ε ≥ L⁻²` then `ℓ⁻¹ ≤ √ε`
(`baP5_convB`), otherwise `ℓ = L` and `n/ℓ ≤ d/2`. -/
private lemma baP5_exp_bulk (d L : ℕ) (hL : 1 ≤ L) {ε ℓ n b : ℝ} (hb : 0 ≤ b)
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
`ε ≥ L⁻²` then `n/ℓ ≤ (d/2) ε L²` (`baP5_convC`), otherwise `ℓ = L`. -/
private lemma baP5_exp_zero (d L : ℕ) (hL : 1 ≤ L) {ε ℓ n c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
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
private lemma baP5_shape_zero {γ ε e g J C₀ CA : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (he : γ * ε = e)
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
private lemma baP5_shape_big {γ ε e g J CA c' c ℓ n : ℝ} (k : ℕ) (hγ : 0 < γ) (hε : 0 < ε)
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
  have hpoly : (n + 1) ^ k * Real.exp (-(c' / 2) * n) ≤ M := baP5_poly_exp_le (by positivity) k hn
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
(`baP5_exp_bulk`), `n^{-k} ≤ 2^k (n+1)^{-k}`. -/
private lemma baP5_shape_small {γ ε e g J CA CB c' c ℓ n Ed : ℝ} (k : ℕ) (hγ : 0 < γ)
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
  have hN := baP5_inv_pow_le hn k
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
private lemma baP5_head_shape {γ ε e g J CA CB C₀ c' c ℓ Ed : ℝ} (k n : ℕ) (hγ : 0 < γ)
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
    have := baP5_shape_zero hγ hε he hC₀ hCA hA1 hA2 h1 h2
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
    · have := baP5_shape_small (c := c) k hγ hε hCA hCB hEd (by linarith) hn1 hℓ0 he0 hε1 hA2
        (hJ1 hpos hε1) (hU hpos hε1)
      refine this.trans ?_
      have h3 : CA * CB * 2 ^ k * Ed ≤ CA * (C₀ + 1 + 2 * M + CB * 2 ^ k * Ed) := by
        have : 0 ≤ CA * (C₀ + 1 + 2 * M) := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hP) hExp
    · have := baP5_shape_big k hγ hε he hCA hc' hc hcc hn0 hℓ hε1 hA1 (hJ2 hpos hε1)
      refine this.trans ?_
      have h3 : 2 * CA * M ≤ CA * (C₀ + 1 + 2 * M + CB * 2 ^ k * Ed) := by
        have : 0 ≤ CA * (C₀ + 1) := by positivity
        have : 0 ≤ CA * (CB * 2 ^ k * Ed) := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hP) hExp
private lemma baP5_lg_nonneg (m : ℕ) (c n ε : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ lgIntegrand m c n ε τ := by
  unfold lgIntegrand
  have : 0 ≤ min 1 (τ ^ (-(m : ℝ) / 2)) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  positivity

/-- Split of `∫_{(0,∞)}` at `T`. -/
private lemma baP5_split {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : IntegrableOn f (Ioi 0)) :
    ∫ τ in Ioi (0 : ℝ), f τ = (∫ τ in Ioc 0 T, f τ) + ∫ τ in Ioi T, f τ := by
  have hU : Ioc (0 : ℝ) T ∪ Ioi T = Ioi 0 := Ioc_union_Ioi_eq_Ioi hT.le
  have h1 : IntegrableOn f (Ioc 0 T) := hf.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn f (Ioi T) := hf.mono_set (Ioi_subset_Ioi hT.le)
  rw [← hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2]
/-- The head `(0, L²]`: `e^{-ετ} kBA_τ ≤ C_K · lgIntegrand` (`kBA_le`), so the head integral is
at most `C_K ∫_{(0,∞)} lgIntegrand` (`n` is `|a|`). -/
private lemma baP5_head_le (d L : ℕ) [NeZero L] {g E : ℝ} {m : ℂ} (hg : 0 < g)
    (hS : BASelf d L g (E : ℂ) m) {CK cK : ℝ} (hCK : 0 ≤ CK) {ε : ℝ} (hε : 0 < ε)
    (a : Zd d L) (n : ℕ)
    (hK : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → kBA d L g E m τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
      Real.exp (-cK * min ((n : ℝ) ^ 2 / τ) (n : ℝ)))
    (hI : IntegrableOn (lgIntegrand d cK (n : ℝ) ε) (Ioi 0)) :
    ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kBA d L g E m τ a
      ≤ CK * ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) ε τ := by
  have hF : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a) (Ioc 0 ((L : ℝ) ^ 2)) :=
    (baP5_F_integrable hg hS hε a).mono_set Ioc_subset_Ioi_self
  have hI' : IntegrableOn (lgIntegrand d cK (n : ℝ) ε) (Ioc 0 ((L : ℝ) ^ 2)) :=
    hI.mono_set Ioc_subset_Ioi_self
  calc ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kBA d L g E m τ a
      ≤ ∫ τ in Ioc 0 ((L : ℝ) ^ 2), CK * lgIntegrand d cK (n : ℝ) ε τ := by
        refine setIntegral_mono_on hF (hI'.const_mul CK) measurableSet_Ioc ?_
        intro τ hτ
        have h := hK τ hτ.1 hτ.2
        unfold lgIntegrand
        calc Real.exp (-ε * τ) * kBA d L g E m τ a
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
        exact baP5_lg_nonneg d cK _ ε hτ

/-- `kBA_τ ≤ (1 + C) L^{-d}` for `τ ≥ 0` from `|kBA_τ - L^{-d}| ≤ C L^{-d} e^{-cτ/L²}`. -/
private lemma baP5_K_le_tail {d L : ℕ} [NeZero L] {g E : ℝ} {m : ℂ} {CG cG τ : ℝ} (hCG : 0 ≤ CG) (hcG : 0 ≤ cG)
    (hτ : 0 ≤ τ) (a : Zd d L)
    (h : |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) :
    kBA d L g E m τ a ≤ (1 + CG) * ((L : ℝ) ^ d)⁻¹ := by
  have hLd : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  have he : Real.exp (-cG * τ / (L : ℝ) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ cG * τ / (L : ℝ) ^ 2 := by positivity
    have h2 : -cG * τ / (L : ℝ) ^ 2 = -(cG * τ / (L : ℝ) ^ 2) := by ring
    linarith
  have h1 : kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹ ≤ CG * ((L : ℝ) ^ d)⁻¹ := by
    refine (le_abs_self _).trans (h.trans ?_)
    calc CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)
        ≤ CG * ((L : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := mul_one _
  linarith
/-- `∫_{(0,∞)} e^{-ετ} = 1/ε`. -/
private lemma baP5_integral_exp {ε : ℝ} (hε : 0 < ε) :
    ∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) = 1 / ε := by
  have ha : -ε < 0 := by linarith
  rw [integral_exp_mul_Ioi ha 0]
  simp [neg_div]

/-- `∫_{(T,∞)} e^{-ετ} = e^{-εT}/ε`. -/
private lemma baP5_integral_exp_Ioi {ε T : ℝ} (hε : 0 < ε) :
    ∫ τ in Ioi T, Real.exp (-ε * τ) = Real.exp (-ε * T) / ε := by
  have ha : -ε < 0 := by linarith
  rw [integral_exp_mul_Ioi ha T, neg_div, div_neg, neg_neg]
/-- The tail `(L², ∞)`: `kBA_τ ≤ (1 + C) L^{-d}` gives `(1 + C) L^{-d} e^{-εL²}/ε`. -/
private lemma baP5_tail_le (d L : ℕ) [NeZero L] {g E : ℝ} {m : ℂ} (hg : 0 < g)
    (hS : BASelf d L g (E : ℂ) m) {CG : ℝ} {ε : ℝ} (hε : 0 < ε)
    (a : Zd d L)
    (hG : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → kBA d L g E m τ a ≤ (1 + CG) * ((L : ℝ) ^ d)⁻¹) :
    ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kBA d L g E m τ a
      ≤ (1 + CG) * ((L : ℝ) ^ d)⁻¹ * (Real.exp (-ε * (L : ℝ) ^ 2) / ε) := by
  have hT : (0 : ℝ) < (L : ℝ) ^ 2 := by have := Nat.pos_of_neZero L; positivity
  have hF : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a) (Ioi ((L : ℝ) ^ 2)) :=
    (baP5_F_integrable hg hS hε a).mono_set (Ioi_subset_Ioi hT.le)
  have hE : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioi ((L : ℝ) ^ 2)) :=
    integrableOn_exp_mul_Ioi (by linarith) _
  calc ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kBA d L g E m τ a
      ≤ ∫ τ in Ioi ((L : ℝ) ^ 2), (1 + CG) * ((L : ℝ) ^ d)⁻¹ * Real.exp (-ε * τ) := by
        refine setIntegral_mono_on hF (hE.const_mul _) measurableSet_Ioi ?_
        intro τ hτ
        have h := hG τ hτ.le
        calc Real.exp (-ε * τ) * kBA d L g E m τ a
            ≤ Real.exp (-ε * τ) * ((1 + CG) * ((L : ℝ) ^ d)⁻¹) :=
              mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
          _ = _ := by ring
    _ = (1 + CG) * ((L : ℝ) ^ d)⁻¹ * (Real.exp (-ε * (L : ℝ) ^ 2) / ε) := by
        rw [integral_const_mul, baP5_integral_exp_Ioi hε]
/-- The tail in the pinned shape: `γ⁻¹ (1 + C) L^{-d} e^{-εL²}/ε = (1 + C) e^{-εL²} (L^d e)⁻¹`,
and `e^{-εL²} ≤ E_z e^{-cn/ℓ}` (`baP5_exp_zero`). -/
private lemma baP5_tail_shape {γ ε e CG c ℓ n Ld L2 Ez : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
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

/-- The constant of the head in the pinned shape (`baP5_head_shape` times `C_K`). -/
private noncomputable def baP5Ch (d : ℕ) (CK CA CB c' : ℝ) : ℝ :=
  CK * (CA * ((1 + 2 / ((d : ℝ) - 2)) + 1
    + 2 * (((d - 2).factorial : ℝ) * (1 / (c' / 2)) ^ (d - 2) * Real.exp (c' / 2))
    + CB * 2 ^ (d - 2) * Real.exp (c' * d / 2)))

private lemma baP5Ch_nonneg {d : ℕ} (hd : 3 ≤ d) {CK CA CB c' : ℝ} (hCK : 0 ≤ CK) (hCA : 0 ≤ CA)
    (hCB : 0 ≤ CB) (hc' : 0 < c') : 0 ≤ baP5Ch d CK CA CB c' := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : 0 ≤ 2 / ((d : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
  have h3 : 0 ≤ (1 + 2 / ((d : ℝ) - 2)) + 1 := by linarith
  have h4 : 0 ≤ 2 * (((d - 2).factorial : ℝ) * (1 / (c' / 2)) ^ (d - 2) * Real.exp (c' / 2)) := by
    positivity
  have h5 : 0 ≤ CB * 2 ^ (d - 2) * Real.exp (c' * d / 2) := by positivity
  unfold baP5Ch
  exact mul_nonneg hCK (mul_nonneg hCA (by linarith))
/-- **The head in the pinned shape** (`0 < t < 1`): `γ⁻¹ ∫_{(0,L²]} e^{-ετ} kBA_τ(a) dτ
≤ Ch (g² + e)⁻¹ (n+1)^{-(d-2)} e^{-c n/ℓ_t}` for `0 ≤ c ≤ c'/2`; `kBA_le`, `lg_bulk`, `lg_zero`,
`baP5_convA`, `baP5_convB`, in the regimes `n = 0`, `ε ≥ 1`, `ε < 1`. -/
private lemma baP5_head5 (d : ℕ) (hd : 3 ≤ d) {Λ : ℝ} {CK cK CB c' CA : ℝ}
    (hCK : 0 < CK) (hCB : 0 < CB) (hc' : 0 < c') (hCA : 0 < CA)
    (hB : ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε → IntegrableOn (lgIntegrand d cK n ε) (Ioi 0) ∧
      (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ
        ≤ CB * n ^ (-((d : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
      (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ ≤ 2 / ε * Real.exp (-c' * n)))
    (hA : ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ baP5Eps g t → 1 / (1 - t) ≤ CA / (g ^ 2 + (1 - t))) ∧
      (baP5Eps g t < 1 → 1 / baP5Gam g t ≤ CA / (g ^ 2 + (1 - t))))
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (g E : ℝ) (m : ℂ) (hg : 0 < g) (hS : BASelf d L g (E : ℂ) m)
    (hgΛ : g ≤ Λ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (a : Zd d L)
    (hK : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → kBA d L g E m τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
      Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)))
    {c : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c' / 2) :
    (baP5Gam g t)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a
      ≤ baP5Ch d CK CA CB c' * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
        * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
  have hL1 : 1 ≤ L := by omega
  have hγ := baP5_gam_pos hg ht0
  have hε := baP5_eps_pos hg ht0 ht1
  have he := baP5_gam_mul_eps hg ht0
  have hnL := baP5_zdistD_le d L a
  have hKa := hK
  generalize zdistD d L a = n at hKa hnL ⊢
  have hcn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT (by exact_mod_cast hL1)
  have hℓ0 : 0 < ellT L g t := lt_of_lt_of_le one_pos hℓ1
  obtain ⟨hB1, hB2⟩ := baP5_convB L g t hL1 hg ht0 ht1
  obtain ⟨hA1, hA2⟩ := hA g t hg hgΛ ht0 ht1
  have hd2 : 2 ≤ d := by omega
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hI : IntegrableOn (lgIntegrand d cK (n : ℝ) (baP5Eps g t)) (Ioi 0) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simpa using (lg_zero d hd cK (baP5Eps g t) hε.le).1
    · exact (hB n (baP5Eps g t) (by exact_mod_cast hpos) hε.le).1
  have hhead := baP5_head_le d L hg hS hCK.le hε a n hKa hI
  have hJ0 : n = 0 → (∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (baP5Eps g t) τ)
      ≤ 1 + 2 / ((d : ℝ) - 2) ∧
      (∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (baP5Eps g t) τ) ≤ 1 / baP5Eps g t := by
    intro h0
    subst h0
    obtain ⟨-, h1, h2⟩ := lg_zero d hd cK (baP5Eps g t) hε.le
    exact ⟨by simpa using h1, by simpa using h2 hε⟩
  have hJ1 : 1 ≤ n → baP5Eps g t < 1 →
      (∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (baP5Eps g t) τ)
      ≤ CB * ((n : ℝ) ^ (d - 2))⁻¹ * Real.exp (-c' * n * Real.sqrt (baP5Eps g t)) := by
    intro h1 h2
    have := (hB n (baP5Eps g t) (by exact_mod_cast h1) hε.le).2.1 h2.le
    rwa [baP5_rpow_eq hd2 hcn] at this
  have hJ2 : 1 ≤ n → 1 ≤ baP5Eps g t →
      (∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (baP5Eps g t) τ)
      ≤ 2 / baP5Eps g t * Real.exp (-c' * n) := by
    intro h1 h2
    exact (hB n (baP5Eps g t) (by exact_mod_cast h1) hε.le).2.2 h2
  have hU : 1 ≤ n → baP5Eps g t < 1 →
      Real.exp (-c' * n * Real.sqrt (baP5Eps g t))
        ≤ Real.exp (c' * d / 2) * Real.exp (-c' * n / ellT L g t) := fun _ _ =>
    baP5_exp_bulk d L hL1 hc'.le hcn hnL hB1 hB2
  have hC₀ : (0 : ℝ) ≤ 1 + 2 / ((d : ℝ) - 2) := by
    have : 0 ≤ 2 / ((d : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
    linarith
  have hshape := baP5_head_shape (d - 2) n hγ hε he hCA.le hCB.le hC₀ (Real.exp_pos _).le hc' hc
    hcc hℓ1 hA1 hA2 hJ0 hJ1 hJ2 hU
  calc (baP5Gam g t)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a
      ≤ (baP5Gam g t)⁻¹ * (CK * ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (baP5Eps g t) τ) :=
        mul_le_mul_of_nonneg_left hhead (inv_nonneg.mpr hγ.le)
    _ = CK * ((baP5Gam g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK (n : ℝ) (baP5Eps g t) τ) := by
        ring
    _ ≤ CK * (CA * ((1 + 2 / ((d : ℝ) - 2)) + 1
          + 2 * (((d - 2).factorial : ℝ) * (1 / (c' / 2)) ^ (d - 2) * Real.exp (c' / 2))
          + CB * 2 ^ (d - 2) * Real.exp (c' * d / 2)) *
          ((g ^ 2 + (1 - t))⁻¹ * (((n : ℝ) + 1) ^ (d - 2))⁻¹) * Real.exp (-c * n / ellT L g t)) :=
        mul_le_mul_of_nonneg_left hshape hCK.le
    _ = _ := by unfold baP5Ch; ring

/-- **The tail in the pinned shape** (`0 < t < 1`): `γ⁻¹ ∫_{(L²,∞)} e^{-ετ} kBA_τ(a) dτ
≤ (1 + C_G) e^{cd/2} (L^d e)⁻¹ e^{-c n/ℓ_t}` for `0 ≤ c`, `c d ≤ 2` (zero mode, Fable F5 (c)). -/
private lemma baP5_tail5 (d : ℕ) {CG cG : ℝ} (hCG : 0 < CG) (hcG : 0 ≤ cG)
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (g E : ℝ) (m : ℂ) (hg : 0 < g) (hS : BASelf d L g (E : ℂ) m)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (a : Zd d L)
    (hG : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2))
    {c : ℝ} (hc : 0 ≤ c) (hcd : c * d ≤ 2) :
    (baP5Gam g t)⁻¹ * ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a
      ≤ (1 + CG) * Real.exp (c * d / 2) * (((L : ℝ) ^ d * (1 - t))⁻¹)
        * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
  have hL1 : 1 ≤ L := by omega
  have hγ := baP5_gam_pos hg ht0
  have hε := baP5_eps_pos hg ht0 ht1
  have he := baP5_gam_mul_eps hg ht0
  have hGa : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → kBA d L g E m τ a ≤ (1 + CG) * ((L : ℝ) ^ d)⁻¹ := fun τ hτ =>
    baP5_K_le_tail hCG.le hcG (le_trans (by positivity) hτ) a (hG τ hτ)
  have htail := baP5_tail_le d L hg hS hε a hGa
  have hnL := baP5_zdistD_le d L a
  generalize zdistD d L a = n at hnL ⊢
  have hcn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT (by exact_mod_cast hL1)
  have hℓ0 : 0 < ellT L g t := lt_of_lt_of_le one_pos hℓ1
  obtain ⟨-, hB2⟩ := baP5_convB L g t hL1 hg ht0 ht1
  have hC := baP5_convC d L g t n hL1 hg ht0 ht1 hcn hnL
  have hZ := baP5_exp_zero d L hL1 hε hc hcd hnL hB2 hC
  have hLd : 0 < (L : ℝ) ^ d := by positivity
  calc (baP5Gam g t)⁻¹ * ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a
      ≤ (baP5Gam g t)⁻¹ * ((1 + CG) * ((L : ℝ) ^ d)⁻¹
          * (Real.exp (-(baP5Eps g t) * (L : ℝ) ^ 2) / baP5Eps g t)) :=
        mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hγ.le)
    _ ≤ _ := baP5_tail_shape hγ hε he hCG.le hLd hZ
/-- `t = 0`: `Θ = 1`, `B_{0,0} ≥ (Λ²+1)⁻¹`. -/
private lemma baP5_zero5 (d L : ℕ) [NeZero L] {Λ g : ℝ} (E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool)
    (hg : 0 < g) (hgΛ : g ≤ Λ) (a : Zd d L) {c C : ℝ} (hC : Λ ^ 2 + 1 ≤ C) :
    ‖BATheta d L g E m 0 σ₁ σ₂ 0 a‖
      ≤ C * Bparam d L g 0 (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g 0) := by
  rw [baP5_Theta_zero]
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
/-- **Property 5 for `t ∈ (0,1)`**: `Θ_t(0,a) ≤ C B_{t,|a|} e^{-c|a|/ℓ_t}` (`Θ_t(0,a)` is a nonnegative real). -/
private lemma baP5_core5 (d : ℕ) (hd : 3 ≤ d) {Λ : ℝ} {CK cK CG cG CB c' CA : ℝ}
    (hCK : 0 < CK) (hCG : 0 < CG) (hcG : 0 ≤ cG) (hCB : 0 < CB) (hc' : 0 < c') (hCA : 0 < CA)
    (hB : ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε → IntegrableOn (lgIntegrand d cK n ε) (Ioi 0) ∧
      (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ
        ≤ CB * n ^ (-((d : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
      (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ ≤ 2 / ε * Real.exp (-c' * n)))
    (hA : ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ baP5Eps g t → 1 / (1 - t) ≤ CA / (g ^ 2 + (1 - t))) ∧
      (baP5Eps g t < 1 → 1 / baP5Gam g t ≤ CA / (g ^ 2 + (1 - t))))
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (g E : ℝ) (m : ℂ) (hg : 0 < g) (hS : BASelf d L g (E : ℂ) m)
    (hgΛ : g ≤ Λ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (a : Zd d L)
    (hK : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → kBA d L g E m τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
      Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)))
    (hG : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2))
    {c : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c' / 2) (hcd : c * d ≤ 2) {C : ℝ}
    (hC1 : baP5Ch d CK CA CB c' ≤ C) (hC2 : (1 + CG) * Real.exp (c * d / 2) ≤ C) :
    ‖BATheta d L g E m t true false 0 a‖
      ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
  have hγ := baP5_gam_pos hg ht0
  have hε := baP5_eps_pos hg ht0 ht1
  have hT : (0 : ℝ) < (L : ℝ) ^ 2 := by have := Nat.pos_of_neZero L; positivity
  have hx : 0 ≤ (baP5Gam g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a :=
    mul_nonneg (inv_nonneg.mpr hγ.le) (setIntegral_nonneg measurableSet_Ioi fun τ hτ =>
      mul_nonneg (Real.exp_pos _).le (baP5_kBA_bounds hg hS (le_of_lt hτ) a).1)
  rw [baP5_theta_eq d L hL g E m t hg hS ht0 ht1 a, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx, baP5_split hT (baP5_F_integrable hg hS hε a), mul_add]
  have h1 := baP5_head5 d hd hCK hCB hc' hCA hB hA L hL g E m hg hS hgΛ t ht0 ht1 a hK hc hcc
  have h2 := baP5_tail5 d hCG hcG L hL g E m hg hS t ht0 ht1 a hG hc hcd
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
  have hCh0 := baP5Ch_nonneg hd hCK.le hCA.le hCB.le hc'
  calc _ ≤ baP5Ch d CK CA CB c'
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

/-! ## 4. Property 5, mixed charges -/

/-- **`(prop:ThfadC)`** (property 5 of `lem_propTH`) for the block Anderson propagator, mixed charges
`σ₁ ≠ σ₂`, for every `d ≥ 3`, `Λ > 0`, `κ > 0`: constants `(C, c)` depend on `(d, Λ, κ)` only.
`t = 0` separately (`Θ = 1`), `0 < t < 1` by the Laplace representation
`Θ_t(0,a) = γ⁻¹ ∫₀^∞ e^{-ετ} kBA(τ,a) dτ`, `γ = t g²`, split at `τ = L²`; regimes `n = 0`,
`ε ≥ 1`, `L⁻² ≤ ε < 1`, `ε < L⁻²`.  Special case `σ₁ ≠ σ₂` of `BAProp5`, not the general pin. -/
theorem baProp5mixed_holds (d : ℕ) (Λ κ : ℝ) : BAProp5mixed d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨CK, cK, hCK, hcK, hK⟩ := kBA_le d (by omega) Λ κ hΛ hκ
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := kBA_gap d (by omega) Λ κ hΛ hκ
  obtain ⟨CB, hCB, c', hc', hB⟩ := lg_bulk d hd cK hcK
  obtain ⟨CA, hCA, hA⟩ := baP5_convA Λ hΛ
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (c' / 2) (2 / d) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact lt_min (by positivity) (by positivity)
  have hcc : c ≤ c' / 2 := by rw [hc]; exact min_le_left _ _
  have hcd : c * d ≤ 2 := by
    have : c ≤ 2 / d := by rw [hc]; exact min_le_right _ _
    calc c * d ≤ 2 / d * d := mul_le_mul_of_nonneg_right this hdpos.le
      _ = 2 := by field_simp
  have hCh0 := baP5Ch_nonneg hd hCK.le hCA.le hCB.le hc'
  have hCt0 : 0 ≤ (1 + CG) * Real.exp (c * d / 2) := by positivity
  have hΛ2 : 0 < Λ ^ 2 + 1 := by positivity
  refine ⟨baP5Ch d CK CA CB c' + (1 + CG) * Real.exp (c * d / 2) + (Λ ^ 2 + 1), by positivity, c,
    hc0, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ hσ a
  have : NeZero L := ⟨by omega⟩
  rw [baP5_Theta_mixed d L g E m t hσ]
  rcases ht0.eq_or_lt with h0 | h0
  · subst h0
    exact baP5_zero5 d L E m true false hg hgΛ a (by linarith)
  · exact baP5_core5 d hd hCK hCG hcG.le hCB hc' hCA hB hA L hL g E m hg hr.1 hgΛ t h0 ht1 a
      (fun τ hτ hτL => hK L hL g E m hg hgΛ hr τ hτ hτL a)
      (fun τ hτ => (hG L hL g E m hg hgΛ hr τ hτ a ⟨0, by omega⟩ ⟨0, by omega⟩).1)
      hc0.le hcc hcd (by linarith) (by linarith)

example (d : ℕ) (Λ κ : ℝ) : BAProp5mixed d Λ κ := baProp5mixed_holds d Λ κ

/-! ## 5. Property 8: the rows of `Θ` sum to `(1 - t)⁻¹`, and `Θ̊ = Θ - L^{-d}(1-t)⁻¹`

The Neumann series `Θ = Σ tⁿ Kⁿ` of `BA/KHeat.lean` (private there: `baP5_pow_le_one`,
`baP5_summable_t`, `baP5_neumann`, `baP5_Theta_eq`; copied here under `baP5_`). -/

section Series

variable (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)

private theorem baP5_pow_le_one (h : BASelf d L g (E : ℂ) m) (n : ℕ) (a b : Zd d L) :
    (BAK d L g E m ^ n) a b ≤ 1 := by
  calc (BAK d L g E m ^ n) a b ≤ ∑ c, (BAK d L g E m ^ n) a c :=
        Finset.single_le_sum (f := fun c => (BAK d L g E m ^ n) a c)
          (fun c _ => BAK_pow_nonneg d L g E m n a c) (Finset.mem_univ b)
    _ = 1 := BAK_pow_row_sum d L g E m h n a

private theorem baP5_summable_t (h : BASelf d L g (E : ℂ) m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) : Summable (fun n : ℕ => t ^ n * (BAK d L g E m ^ n) a b) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg ht0 n) (BAK_pow_nonneg d L g E m n a b)) (fun n => ?_)
    (summable_geometric_of_lt_one ht0 ht1)
  calc t ^ n * (BAK d L g E m ^ n) a b ≤ t ^ n * 1 :=
        mul_le_mul_of_nonneg_left (baP5_pow_le_one d L g E m h n a b) (pow_nonneg ht0 n)
    _ = t ^ n := mul_one _

/-- The Neumann series solves `B - t K B = 1` entrywise. -/
private theorem baP5_neumann (h : BASelf d L g (E : ℂ) m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) :
    (∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) a b)
      - t * ∑ c, BAK d L g E m a c * ∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b
      = if a = b then 1 else 0 := by
  have hsum := fun c => baP5_summable_t d L g E m h ht0 ht1 c b
  have h1 : ∑ c, BAK d L g E m a c * ∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b
      = ∑' n : ℕ, t ^ n * (BAK d L g E m ^ (n + 1)) a b := by
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun c _ => (hsum c).mul_left _)]
    refine tsum_congr fun n => ?_
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [h1, (hsum a).tsum_eq_zero_add]
  have h2 : ∑' n : ℕ, t ^ (n + 1) * (BAK d L g E m ^ (n + 1)) a b
      = t * ∑' n : ℕ, t ^ n * (BAK d L g E m ^ (n + 1)) a b := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    ring
  rw [h2]
  simp [Matrix.one_apply]

/-- `Θ^{(+,-)}_t = Σ tⁿ Kⁿ` for `0 ≤ t < 1` (Neumann series; `Ring.inverse (1 - tK)`). -/
private theorem baP5_Theta_eq (h : BASelf d L g (E : ℂ) m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    BATheta d L g E m t true false
      = Matrix.of fun a b => (((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) a b : ℝ)) : ℂ) := by
  rw [BATheta_pm_eq]
  unfold PropThetaQ
  set B : Matrix (Zd d L) (Zd d L) ℂ :=
    Matrix.of fun a b => (((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) a b : ℝ)) : ℂ) with hB
  have hXB : (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal) * B = 1 := by
    ext a b
    have h1 := congrArg (fun r : ℝ => (r : ℂ)) (baP5_neumann d L g E m h ht0 ht1 a b)
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, hB,
      Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, smul_eq_mul]
    have h2 : ∑ c, (if a = c then (1 : ℂ) else 0) * ((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b : ℝ) : ℂ)
        = ((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) a b : ℝ) : ℂ) := by
      simp
    have h3 : ∑ c, (t : ℂ) * (BAK d L g E m a c : ℂ) * ((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b : ℝ) : ℂ)
        = (t : ℂ) * ∑ c, (BAK d L g E m a c : ℂ) * ((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [h2, h3]
    push_cast at h1 ⊢
    rw [h1]
    split_ifs <;> simp
  have hBX : B * (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal) = 1 :=
    mul_eq_one_comm.mp hXB
  have hu : IsUnit (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal) :=
    ⟨⟨_, B, hXB, hBX⟩, rfl⟩
  calc Ring.inverse (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal)
      = Ring.inverse (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal)
          * ((1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal) * B) := by rw [hXB, mul_one]
    _ = B := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

end Series

private lemma baP5_card (d L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

/-- Every row of `Θ^{(+,-)}_t` sums to `(1 - t)⁻¹` (`Kⁿ` has unit row sums, `BAK_pow_row_sum`). -/
private lemma baP5_Theta_row_sum (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Zd d L) :
    ∑ b, BATheta d L g E m t true false a b = (((1 - t)⁻¹ : ℝ) : ℂ) := by
  rw [baP5_Theta_eq d L g E m h ht0 ht1]
  simp only [Matrix.of_apply]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [← Summable.tsum_finsetSum (fun b _ => baP5_summable_t d L g E m h ht0 ht1 a b)]
  have h1 : ∀ n : ℕ, ∑ b, t ^ n * (BAK d L g E m ^ n) a b = t ^ n := fun n => by
    rw [← Finset.mul_sum, BAK_pow_row_sum d L g E m h n a, mul_one]
  simp_rw [h1]
  exact tsum_geometric_of_lt_one ht0 ht1

/-- `Θ̊_t(0,a) = Θ_t(0,a) - L^{-d} (1-t)⁻¹` for `σ₁ ≠ σ₂` (all `L^d` rows of `Θ` sum to `(1-t)⁻¹`). -/
private lemma baP5_Theta0_apply_eq (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)
    (h : BASelf d L g (E : ℂ) m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {σ₁ σ₂ : Bool}
    (hσ : σ₁ ≠ σ₂) (a : Zd d L) :
    BATheta0 d L g E m t σ₁ σ₂ 0 a
      = BATheta d L g E m t true false 0 a - ((L : ℂ) ^ d)⁻¹ * (1 - (t : ℂ))⁻¹ := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hdouble : ∑ a' : Zd d L, ∑ b' : Zd d L, BATheta d L g E m t true false a' b'
      = (L : ℂ) ^ d * (1 - (t : ℂ))⁻¹ := by
    have hrow : ∀ a' : Zd d L, ∑ b' : Zd d L, BATheta d L g E m t true false a' b'
        = (1 - (t : ℂ))⁻¹ := fun a' => by
      rw [baP5_Theta_row_sum d L g E m h ht0 ht1 a']; push_cast; rfl
    rw [Finset.sum_congr rfl fun a' _ => hrow a', Finset.sum_const, Finset.card_univ,
      baP5_card, nsmul_eq_mul, Nat.cast_pow]
  unfold BATheta0
  simp only [Matrix.of_apply]
  rw [baP5_Theta_mixed d L g E m t hσ, hdouble]
  congr 1
  rw [two_mul, pow_add]
  field_simp

/-- `Θ̊_t(0,a) = γ⁻¹ ∫₀^∞ e^{-ετ} (kBA_τ(a) - L^{-d}) dτ` for `0 < t < 1`
(`baP5_Theta0_apply_eq` and `∫₀^∞ e^{-ετ} = 1/ε`, `γ ε = e`). -/
private lemma baP5_theta0_eq (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g E : ℝ) (m : ℂ) (t : ℝ)
    (hg : 0 < g) (hS : BASelf d L g (E : ℂ) m) (ht0 : 0 < t) (ht1 : t < 1) {σ₁ σ₂ : Bool}
    (hσ : σ₁ ≠ σ₂) (a : Zd d L) :
    BATheta0 d L g E m t σ₁ σ₂ 0 a =
      (((baP5Gam g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ)
          * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹) : ℝ) : ℂ) := by
  have hγ := baP5_gam_pos hg ht0
  have hε := baP5_eps_pos hg ht0 ht1
  have he := baP5_gam_mul_eps hg ht0
  rw [baP5_Theta0_apply_eq d L g E m hS ht0.le ht1 hσ a, baP5_theta_eq d L hL g E m t hg hS ht0 ht1 a]
  have hE : IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hint : ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹)
      = (∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a)
        - ((L : ℝ) ^ d)⁻¹ * (1 / baP5Eps g t) := by
    have h1 : (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ) * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹))
        = fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ) * kBA d L g E m τ a
          - ((L : ℝ) ^ d)⁻¹ * Real.exp (-(baP5Eps g t) * τ) := by
      funext τ; ring
    rw [h1, integral_sub (baP5_F_integrable hg hS hε a) (hE.const_mul _), integral_const_mul,
      baP5_integral_exp hε]
  rw [hint]
  have hc : ((L : ℂ) ^ d)⁻¹ * (1 - (t : ℂ))⁻¹
      = ((((baP5Gam g t)⁻¹ * (((L : ℝ) ^ d)⁻¹ * (1 / baP5Eps g t)) : ℝ)) : ℂ) := by
    have h2 : (baP5Gam g t)⁻¹ * (((L : ℝ) ^ d)⁻¹ * (1 / baP5Eps g t))
        = ((L : ℝ) ^ d)⁻¹ * (1 - t)⁻¹ := by
      rw [← he]; field_simp
    rw [h2]; push_cast; ring
  rw [hc, ← Complex.ofReal_sub]
  congr 1
  ring
/-- `γ⁻¹ (L^{-d} Y) ≲ (g²+e)⁻¹ L^{-(d-2)}` when `Y ≤ A L²` and `Y ≤ A/ε`:
`ε < 1` uses `γ⁻¹` (`baP5_convA`) and `L^{-d} L² = L^{-(d-2)}`, `ε ≥ 1` uses `γ⁻¹/ε = 1/e`. -/
private lemma baP5_Ld_piece {γ ε e g Y A Ld T W CA : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
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
private lemma baP5_head0_le (d L : ℕ) [NeZero L] {g E : ℝ} {m : ℂ} (hg : 0 < g)
    (hS : BASelf d L g (E : ℂ) m) {ε : ℝ} (hε : 0 < ε) (a : Zd d L) :
    |∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹)|
      ≤ (∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kBA d L g E m τ a)
        + ((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) := by
  have hF : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a) (Ioc 0 ((L : ℝ) ^ 2)) :=
    (baP5_F_integrable hg hS hε a).mono_set Ioc_subset_Ioi_self
  have hE : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioc 0 ((L : ℝ) ^ 2)) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-ε * τ)).integrableOn_Ioc
  have h1 : (fun τ : ℝ => Real.exp (-ε * τ) * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹))
      = fun τ : ℝ => Real.exp (-ε * τ) * kBA d L g E m τ a
        - ((L : ℝ) ^ d)⁻¹ * Real.exp (-ε * τ) := by
    funext τ; ring
  rw [h1, integral_sub hF (hE.const_mul _), integral_const_mul]
  have hx : 0 ≤ ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) * kBA d L g E m τ a := by
    refine setIntegral_nonneg measurableSet_Ioc fun τ hτ => ?_
    exact mul_nonneg (Real.exp_pos _).le (baP5_kBA_bounds hg hS hτ.1.le a).1
  have hy : 0 ≤ ((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-ε * τ) := by
    refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioc fun τ _ => ?_)
    exact (Real.exp_pos _).le
  rw [abs_le]
  constructor <;> linarith

/-- The tail `(L², ∞)` of the zero-mode-removed integrand:
`|K - L^{-d}| ≤ C_G L^{-d} e^{-cτ/L²}`. -/
private lemma baP5_tail0_le (d L : ℕ) [NeZero L] {g E : ℝ} {m : ℂ} {CG cG : ℝ} (hcG : 0 < cG)
    {ε : ℝ} (hε : 0 < ε) (a : Zd d L)
    (hG : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) :
    |∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-ε * τ) * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹)|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ *
        ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-ε * τ - cG * τ / (L : ℝ) ^ 2) := by
  have hT : (0 : ℝ) < (L : ℝ) ^ 2 := by have := Nat.pos_of_neZero L; positivity
  obtain ⟨hI, -⟩ := (lg_tail ((L : ℝ) ^ 2) hT).1 ε cG hε.le hcG
  rw [← integral_const_mul]
  have := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi ((L : ℝ) ^ 2)))
    (f := fun τ : ℝ => Real.exp (-ε * τ) * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹))
    (g := fun τ : ℝ => CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-ε * τ - cG * τ / (L : ℝ) ^ 2))
    (hI.const_mul _) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h := hG τ (le_of_lt hτ)
      have hexp : Real.exp (-ε * τ - cG * τ / (L : ℝ) ^ 2)
          = Real.exp (-ε * τ) * Real.exp (-cG * τ / (L : ℝ) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]
      calc Real.exp (-ε * τ) * |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹|
          ≤ Real.exp (-ε * τ) * (CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = _ := by ring)
  simpa [Real.norm_eq_abs] using this
/-- **Property 8, mixed charges, `0 < t < 1`**: `|Θ̊_t(0,a)| ≤ C (g²+e)⁻¹ (n+1)^{-(d-2)}`; the head
`K` piece is the property-5 head at `c = 0`, the `L^{-d}` pieces keep `e^{-ετ}` (`baP5_Ld_piece`). -/
private lemma baP5_core8 (d : ℕ) (hd : 3 ≤ d) {Λ : ℝ} {CK cK CG cG CB c' CA : ℝ}
    (hCK : 0 < CK) (hCG : 0 < CG) (hcG : 0 < cG) (hCB : 0 < CB) (hc' : 0 < c') (hCA : 0 < CA)
    (hB : ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε → IntegrableOn (lgIntegrand d cK n ε) (Ioi 0) ∧
      (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ
        ≤ CB * n ^ (-((d : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
      (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand d cK n ε τ ≤ 2 / ε * Real.exp (-c' * n)))
    (hA : ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ baP5Eps g t → 1 / (1 - t) ≤ CA / (g ^ 2 + (1 - t))) ∧
      (baP5Eps g t < 1 → 1 / baP5Gam g t ≤ CA / (g ^ 2 + (1 - t))))
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (g E : ℝ) (m : ℂ) (hg : 0 < g) (hS : BASelf d L g (E : ℂ) m)
    (hgΛ : g ≤ Λ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) {σ₁ σ₂ : Bool} (hσ : σ₁ ≠ σ₂) (a : Zd d L)
    (hK : ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → kBA d L g E m τ a ≤ CK * min 1 (τ ^ (-(d : ℝ) / 2)) *
      Real.exp (-cK * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)))
    (hG : ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹|
      ≤ CG * ((L : ℝ) ^ d)⁻¹ * Real.exp (-cG * τ / (L : ℝ) ^ 2)) {C : ℝ}
    (hC : baP5Ch d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
      + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2) ≤ C) :
    ‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖
      ≤ C * (g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
  have hL1 : 1 ≤ L := by omega
  have hd2 : 2 ≤ d := by omega
  have hγ := baP5_gam_pos hg ht0
  have hε := baP5_eps_pos hg ht0 ht1
  have he := baP5_gam_mul_eps hg ht0
  have hT : (0 : ℝ) < (L : ℝ) ^ 2 := by have := Nat.pos_of_neZero L; positivity
  obtain ⟨hA1, hA2⟩ := hA g t hg hgΛ ht0 ht1
  have hγ' : 0 ≤ (baP5Gam g t)⁻¹ := inv_nonneg.mpr hγ.le
  have hLd0 : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  have hE : IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hh : IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ)
      * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹)) (Ioi 0) := by
    have h1 := (baP5_F_integrable hg hS hε a).sub (hE.const_mul (((L : ℝ) ^ d)⁻¹))
    refine h1.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    rw [Pi.sub_apply]; ring
  rw [baP5_theta0_eq d L hL g E m t hg hS ht0 ht1 hσ a, Complex.norm_real, Real.norm_eq_abs,
    baP5_split hT hh, abs_mul, abs_of_nonneg hγ']
  -- the three pieces
  have hHead := baP5_head0_le d L hg hS hε a
  have hTail := baP5_tail0_le d L hcG hε a hG
  obtain ⟨hY2a, hY2b⟩ := (lg_tail ((L : ℝ) ^ 2) hT).2.2 (baP5Eps g t) hε.le
  have hY2c := hY2b hε
  obtain ⟨-, hY3a⟩ := (lg_tail ((L : ℝ) ^ 2) hT).1 (baP5Eps g t) cG hε.le hcG
  obtain ⟨-, hY3b⟩ := (lg_tail ((L : ℝ) ^ 2) hT).2.1 (baP5Eps g t) cG hε hcG.le
  have hexpT : Real.exp (-(baP5Eps g t) * (L : ℝ) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 ≤ baP5Eps g t * (L : ℝ) ^ 2 := by positivity
    linarith
  have hexpT0 : 0 < Real.exp (-(baP5Eps g t) * (L : ℝ) ^ 2) := Real.exp_pos _
  have hY3T : ∫ τ in Ioi ((L : ℝ) ^ 2),
      Real.exp (-(baP5Eps g t) * τ - cG * τ / (L : ℝ) ^ 2) ≤ (1 + 1 / cG) * (L : ℝ) ^ 2 := by
    refine hY3a.trans ?_
    calc Real.exp (-(baP5Eps g t) * (L : ℝ) ^ 2) * ((L : ℝ) ^ 2 / cG)
        ≤ 1 * ((L : ℝ) ^ 2 / cG) := mul_le_mul_of_nonneg_right hexpT (by positivity)
      _ = (1 / cG) * (L : ℝ) ^ 2 := by ring
      _ ≤ (1 + 1 / cG) * (L : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hT.le; linarith
  have hY3ε : ∫ τ in Ioi ((L : ℝ) ^ 2),
      Real.exp (-(baP5Eps g t) * τ - cG * τ / (L : ℝ) ^ 2) ≤ (1 + 1 / cG) / baP5Eps g t := by
    refine hY3b.trans ?_
    calc Real.exp (-(baP5Eps g t) * (L : ℝ) ^ 2) / baP5Eps g t ≤ 1 / baP5Eps g t :=
          div_le_div_of_nonneg_right hexpT hε.le
      _ ≤ (1 + 1 / cG) / baP5Eps g t := by
          apply div_le_div_of_nonneg_right _ hε.le
          have : 0 < 1 / cG := by positivity
          linarith
  -- `L^{-d} L² = L^{-(d-2)}`
  have hLd : (L : ℝ) ^ d = (L : ℝ) ^ (d - 2) * (L : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hLT : ((L : ℝ) ^ d)⁻¹ * (L : ℝ) ^ 2 = ((L : ℝ) ^ (d - 2))⁻¹ := by
    have h0 : (L : ℝ) ≠ 0 := by positivity
    rw [hLd]; field_simp
  have hLdW := baP5_Linv_d_le d L hd2
  have hW := baP5_Linv_le d L a (d - 2)
  -- (a) the head `K` piece, the property-5 head at `c = 0`
  have h5 := baP5_head5 d hd hCK hCB hc' hCA hB hA L hL g E m hg hS hgΛ t ht0 ht1 a hK (c := 0) le_rfl
    (by linarith)
  simp only [neg_zero, zero_mul, zero_div, Real.exp_zero, mul_one] at h5
  -- (b), (c) the `L^{-d}` pieces
  have h6 := baP5_Ld_piece (A := 1)
    (Y := ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ)) hγ hε he zero_le_one hCA.le
    hLd0 hLT hLdW hA1 hA2 (by rw [one_mul]; exact hY2a) hY2c
  have hA3 : (0 : ℝ) ≤ 1 + 1 / cG := by positivity
  have h7 := baP5_Ld_piece (A := 1 + 1 / cG) hγ hε he hA3 hCA.le hLd0 hLT hLdW hA1 hA2
    hY3T hY3ε
  have hX : 0 ≤ (g ^ 2 + (1 - t))⁻¹ := by
    have : (0 : ℝ) < 1 - t := by linarith
    positivity
  have hP : 0 ≤ ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hXP : 0 ≤ (g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
    mul_nonneg hX hP
  calc (baP5Gam g t)⁻¹ * |(∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ)
          * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹))
        + ∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ)
          * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹)|
      ≤ (baP5Gam g t)⁻¹ * (|∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ)
          * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹)|
        + |∫ τ in Ioi ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ)
          * (kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hγ'
    _ ≤ (baP5Gam g t)⁻¹ * (((∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ)
            * kBA d L g E m τ a)
          + ((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ))
        + CG * ((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioi ((L : ℝ) ^ 2),
            Real.exp (-(baP5Eps g t) * τ - cG * τ / (L : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hHead hTail) hγ'
    _ = ((baP5Gam g t)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2), Real.exp (-(baP5Eps g t) * τ)
            * kBA d L g E m τ a)
        + (baP5Gam g t)⁻¹ * (((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioc 0 ((L : ℝ) ^ 2),
            Real.exp (-(baP5Eps g t) * τ))
        + CG * ((baP5Gam g t)⁻¹ * (((L : ℝ) ^ d)⁻¹ * ∫ τ in Ioi ((L : ℝ) ^ 2),
            Real.exp (-(baP5Eps g t) * τ - cG * τ / (L : ℝ) ^ 2))) := by ring
    _ ≤ baP5Ch d CK CA CB c' * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
        + CA * 1 * ((g ^ 2 + (1 - t))⁻¹ * (((L : ℝ) ^ (d - 2))⁻¹))
        + CG * (CA * (1 + 1 / cG) * ((g ^ 2 + (1 - t))⁻¹ * (((L : ℝ) ^ (d - 2))⁻¹))) :=
        add_le_add (add_le_add h5 h6) (mul_le_mul_of_nonneg_left h7 hCG.le)
    _ ≤ baP5Ch d CK CA CB c' * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
        + CA * 1 * ((g ^ 2 + (1 - t))⁻¹ * (((d : ℝ) / 2 + 1) ^ (d - 2)
            * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹))
        + CG * (CA * (1 + 1 / cG) * ((g ^ 2 + (1 - t))⁻¹ * (((d : ℝ) / 2 + 1) ^ (d - 2)
            * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹))) := by
        gcongr
    _ = (baP5Ch d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
          + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2))
        * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) := by ring
    _ ≤ C * ((g ^ 2 + (1 - t))⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) :=
        mul_le_mul_of_nonneg_right hC hXP
    _ = _ := by ring
/-- `t = 0`: `Θ̊_0 = 1_{a=0} - L^{-d}`, `|Θ̊_0(0,a)| ≤ (1 + P_d)(n+1)^{-(d-2)}`. -/
private lemma baP5_zero8 (d L : ℕ) [NeZero L] (hd : 3 ≤ d) {Λ g : ℝ} (E : ℝ) (m : ℂ)
    (hS : BASelf d L g (E : ℂ) m) {σ₁ σ₂ : Bool} (hσ : σ₁ ≠ σ₂) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (a : Zd d L) {C : ℝ} (hC : (Λ ^ 2 + 1) * (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) ≤ C) :
    ‖BATheta0 d L g E m (0 : ℝ) σ₁ σ₂ 0 a‖
      ≤ C * (g ^ 2 + |1 - (0 : ℝ)|)⁻¹ * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
  have hd2 : 2 ≤ d := by omega
  rw [baP5_Theta0_apply_eq d L g E m hS le_rfl zero_lt_one hσ a, Complex.ofReal_zero,
    baP5_Theta_zero d L g E m true false]
  have hLd0 : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  have hW := baP5_Linv_le d L a (d - 2)
  have hLdW := baP5_Linv_d_le d L hd2
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

/-! ## 6. Property 8, mixed charges -/

/-- **`(prop:ThfadC0)`** (property 8 of `lem_propTH`) for the block Anderson propagator, mixed charges
`σ₁ ≠ σ₂`, for every `d ≥ 3`, `Λ > 0`, `κ > 0`: `|Θ̊_t(0,a)| ≤ C (g²+|1-t|)⁻¹ (|a|+1)^{-(d-2)}`,
`C` depending on `(d, Λ, κ)` only.  `t = 0` by `Θ = 1`, `0 < t < 1` by the zero-mode-removed Laplace
representation (`e^{-ετ}` kept on the `L^{-d}` piece).  Special case `σ₁ ≠ σ₂` of `BAProp8`, not the
general pin (`σ₁ = σ₂` is the `BAProp5s` branch, a later ticket). -/
theorem baProp8mixed_holds (d : ℕ) (Λ κ : ℝ) : BAProp8mixed d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨CK, cK, hCK, hcK, hK⟩ := kBA_le d (by omega) Λ κ hΛ hκ
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := kBA_gap d (by omega) Λ κ hΛ hκ
  obtain ⟨CB, hCB, c', hc', hB⟩ := lg_bulk d hd cK hcK
  obtain ⟨CA, hCA, hA⟩ := baP5_convA Λ hΛ
  have hPd0 : 0 ≤ ((d : ℝ) / 2 + 1) ^ (d - 2) := by positivity
  have hCh0 := baP5Ch_nonneg hd hCK.le hCA.le hCB.le hc'
  have hK1 : 0 ≤ baP5Ch d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
      + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2) := by positivity
  have hK2 : 0 < (Λ ^ 2 + 1) * (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)) := by positivity
  refine ⟨(baP5Ch d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
      + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2))
    + (Λ ^ 2 + 1) * (1 + ((d : ℝ) / 2 + 1) ^ (d - 2)), by linarith, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ hσ a
  have : NeZero L := ⟨by omega⟩
  rcases ht0.eq_or_lt with h0 | h0
  · subst h0
    exact baP5_zero8 d L hd E m hr.1 hσ hg hgΛ a (by linarith)
  · rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
    exact baP5_core8 d hd hCK hCG hcG hCB hc' hCA hB hA L hL g E m hg hr.1 hgΛ t h0 ht1 hσ a
      (fun τ hτ hτL => hK L hL g E m hg hgΛ hr τ hτ hτL a)
      (fun τ hτ => (hG L hL g E m hg hgΛ hr τ hτ a ⟨0, by omega⟩ ⟨0, by omega⟩).1)
      (by linarith)

example (d : ℕ) (Λ κ : ℝ) : BAProp8mixed d Λ κ := baProp8mixed_holds d Λ κ

/-! ## 7. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, flow point `P`)

Both targets at the `KKernel` instance data (`BAReal 3 4 g₀ (Im m₀) E m₀`, `g₀ ≈ 4.67 ≤ 10`), with
every deterministic hypothesis discharged (`3 ≤ d`, `0 < Λ`, `0 < κ`, `3 ≤ L`, `0 < g ≤ Λ`,
`BAReal`, `0 ≤ t < 1`, `σ₁ ≠ σ₂`); the constants `C`, `c` stay existential, as in the statements. -/

namespace Prop5Inst

open RBM.BA.MFixedPointInst

/-- `baProp5mixed_holds` at `t = 1/2`, `σ = (+,-)`, `a = (1, 0, 0) ≠ 0`, `|a| = 1`
(`ε ≈ 0.046 < L⁻² = 0.0625`: the zero-mode regime `ℓ_t = L`). -/
theorem inst_prop5 : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
    zdistD 3 4 (![1, 0, 0] : Zd 3 4) = 1 ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![1, 0, 0]‖
      ≤ C * Bparam 3 4 P.g0 (1 / 2) (zdistD 3 4 (![1, 0, 0] : Zd 3 4))
        * Real.exp (-c * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) / ellT 4 P.g0 (1 / 2)) := by
  obtain ⟨C, hC, c, hc, H⟩ :=
    baProp5mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, c, hc, by decide, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      true false (by decide) ![1, 0, 0]⟩

/-- `baProp5mixed_holds` at the other mixed charge `σ = (-,+)`, `t = 1/100` (`ε ≈ 4.5 ≥ 1`), `a = (2, 1, 0)`,
`|a| = 3`. -/
theorem inst_prop5_large_eps : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ zdistD 3 4 (![2, 1, 0] : Zd 3 4) = 3 ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 100) false true 0 ![2, 1, 0]‖
      ≤ C * Bparam 3 4 P.g0 (1 / 100) (zdistD 3 4 (![2, 1, 0] : Zd 3 4))
        * Real.exp (-c * (zdistD 3 4 (![2, 1, 0] : Zd 3 4) : ℝ) / ellT 4 P.g0 (1 / 100)) := by
  obtain ⟨C, hC, c, hc, H⟩ :=
    baProp5mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, c, hc, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 100) (by norm_num) (by norm_num)
      false true (by decide) ![2, 1, 0]⟩

/-- `baProp8mixed_holds` at `t = 1/2`, `σ = (+,-)`, `a = (1, 0, 0)`. -/
theorem inst_prop8 : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
    zdistD 3 4 (![1, 0, 0] : Zd 3 4) = 1 ∧
    ‖BATheta0 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![1, 0, 0]‖
      ≤ C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baProp8mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, by decide, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      true false (by decide) ![1, 0, 0]⟩

/-- `baProp8mixed_holds` at `σ = (-,+)`, `t = 1/100`, `a = (2, 1, 0)`. -/
theorem inst_prop8_large_eps : ∃ C : ℝ, 0 < C ∧
    ‖BATheta0 3 4 P.g0 P.E P.m0 (1 / 100) false true 0 ![2, 1, 0]‖
      ≤ C * (P.g0 ^ 2 + |1 - (1 / 100 : ℝ)|)⁻¹ * (((zdistD 3 4 (![2, 1, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baProp8mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 100) (by norm_num)
    (by norm_num) false true (by decide) ![2, 1, 0]⟩

/-- `baProp8mixed_holds` at `t = 0` (`Θ̊_0 = 1 - L^{-d}` on the diagonal), `a = 0`. -/
theorem inst_prop8_zero : ∃ C : ℝ, 0 < C ∧
    ‖BATheta0 3 4 P.g0 P.E P.m0 0 true false 0 0‖
      ≤ C * (P.g0 ^ 2 + |1 - (0 : ℝ)|)⁻¹ * (((zdistD 3 4 (0 : Zd 3 4) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baProp8mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real 0 le_rfl (by norm_num)
    true false (by decide) 0⟩

end Prop5Inst

end RBM.BA
