/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import RBM3D.Defs.Params

/-!
# The Θ-free Laplace–Gauss integrals (route H, step S5)

The one-variable integrals that turn the heat-kernel representation of the propagator into the
decay `B_{t,|a|} e^{-c|a|/ℓ_t}` of `lem:propTH` (Fable review F5, `docs/claude-team/fable/
2026-10-02-routeH.md` §2 S5): the AM–GM + Gamma key lemma (`lg_key`), the bulk and large-`ε`
bounds for `n ≥ 1` (`lg_bulk`), the `n = 0` bound (`lg_zero`), the tail and head integrals
(`lg_tail`), and the conversions between `ε = e/γ`, `ℓ_t` and `L` (`lg_convA/B/C`).
Nothing here mentions the propagator `Θ`; only Mathlib and `RBM.ellT` are used.
-/

open MeasureTheory Set

namespace RBM.Heat

/-- The Laplace–Gauss integrand `e^{-ετ} min(1, τ^{-m/2}) e^{-c min(n²/τ, n)}` (route H, step S5;
Fable review §2 S5 (L1)).  Only `τ > 0` is ever used. -/
noncomputable def lgIntegrand (m : ℕ) (c n ε τ : ℝ) : ℝ :=
  Real.exp (-ε * τ) * min 1 (τ ^ (-(m : ℝ) / 2)) * Real.exp (-c * min (n ^ 2 / τ) n)

/-- `γ = t s₀ g²`, `s₀ = (1 + 2dg²)⁻¹`: the diffusion constant of `1 − tS = e + γ Σ_j Δ_j`
(route H, step S1; Fable F1).  `e = 1 − t`. -/
noncomputable def lgGam (d : ℕ) (g t : ℝ) : ℝ := t * g ^ 2 / (1 + 2 * (d : ℝ) * g ^ 2)

/-- `ε = e / γ`, the parameter that decides the regime (Fable F5: regimes by `ε`, not by `e ≷ g²`). -/
noncomputable def lgEps (d : ℕ) (g t : ℝ) : ℝ := (1 - t) / lgGam d g t

/-! ### Pinned statements -/

/-- Target 1, key lemma (Fable F5): AM–GM `ετ + (c/2)n²/τ ≥ √(cε) n`, then the Gamma integral
`∫₀^∞ τ^{-m/2} e^{-A/τ} dτ = Γ(m/2 − 1) A^{-(m-2)/2}`; converges because `m ≥ 3`. -/
def LGKey : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ c n ε : ℝ, 0 < c → 0 < n → 0 ≤ ε →
    IntegrableOn (fun τ : ℝ => τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)
      ≤ Real.Gamma ((m : ℝ) / 2 - 1) * (c / 2 * n ^ 2) ^ (-((m : ℝ) - 2) / 2)
          * Real.exp (-Real.sqrt (c * ε) * n)

/-- Target 2, (L1) for `n ≥ 1`: the bulk bound for `ε ≤ 1` and the large-`ε` bound for `ε ≥ 1`
(Fable §2 S5 (L1), split at `ε = 1`: for large `ε` only the second form holds).  Constants
after `(m, c)`, before `n, ε`. -/
def LGBulk : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 0 < C ∧ ∃ c' : ℝ, 0 < c' ∧
      ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε →
        IntegrableOn (lgIntegrand m c n ε) (Ioi 0) ∧
        (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c n ε τ
            ≤ C * n ^ (-((m : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
        (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c n ε τ ≤ 2 / ε * Real.exp (-c' * n))

/-- Target 3, (L1) for `n = 0`: `≤ 1 + 2/(m − 2)` always, `≤ 1/ε` for `ε > 0`. -/
def LGZero : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ c ε : ℝ, 0 ≤ ε →
    IntegrableOn (lgIntegrand m c 0 ε) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), lgIntegrand m c 0 ε τ ≤ 1 + 2 / ((m : ℝ) - 2) ∧
    (0 < ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c 0 ε τ ≤ 1 / ε)

/-- Target 4, (L2): the tail beyond `T = L²` (with the torus gap `κτ/T`, Fable F3/F4, or without it)
and the head `(0, T]`; the factor `e^{-ετ}` is kept on the `L^{-d}` pieces (Fable F5 (d)). -/
def LGTail : Prop :=
  ∀ T : ℝ, 0 < T →
    (∀ ε κ : ℝ, 0 ≤ ε → 0 < κ →
      IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ - κ * τ / T)) (Ioi T) ∧
      ∫ τ in Ioi T, Real.exp (-ε * τ - κ * τ / T) ≤ Real.exp (-ε * T) * (T / κ)) ∧
    (∀ ε κ : ℝ, 0 < ε → 0 ≤ κ →
      IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ - κ * τ / T)) (Ioi T) ∧
      ∫ τ in Ioi T, Real.exp (-ε * τ - κ * τ / T) ≤ Real.exp (-ε * T) / ε) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ T ∧
      (0 < ε → ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ 1 / ε))

/-- Target 5, (L3) = Fable F5 (a): `min(1/e, 1/γ) ≤ C_{d,Λ}/(g² + e)`, the step where `Λ` enters
P5–P8.  Regime `ε ≥ 1` (i.e. `e ≥ γ`) uses `1/e`, regime `ε < 1` uses `1/γ`. -/
def LGConvA : Prop :=
  ∀ (d : ℕ) (Λ : ℝ), 0 < Λ → ∃ C : ℝ, 0 < C ∧
    ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ lgEps d g t → 1 / (1 - t) ≤ C / (g ^ 2 + (1 - t))) ∧
      (lgEps d g t < 1 → 1 / lgGam d g t ≤ C / (g ^ 2 + (1 - t)))

/-- Target 6, (L3) = Fable F5 (b): `ℓ_t ≥ ε^{-1/2}` when `ε ≥ L^{-2}`, and `ℓ_t = L` when
`ε < L^{-2}` (`ellT` of `(eq:ellt)`, merged `RBM3D/Defs/Params.lean`). -/
def LGConvB : Prop :=
  ∀ (d L : ℕ) (g t : ℝ), 1 ≤ L → 0 < g → 0 < t → t < 1 →
    (((L : ℝ)⁻¹) ^ 2 ≤ lgEps d g t → (ellT L g t)⁻¹ ≤ Real.sqrt (lgEps d g t)) ∧
    (lgEps d g t < ((L : ℝ)⁻¹) ^ 2 → ellT L g t = (L : ℝ))

/-- Target 7, (L3) = Fable F5 (c): for `ε ≥ L^{-2}` and `n ≤ dL/2` (every torus `ℓ¹` distance),
`n/ℓ_t ≤ (d/2) εL²`, so the zero-mode factor `e^{-εL²}` pays for `e^{-(2/d) n/ℓ_t}`. -/
def LGConvC : Prop :=
  ∀ (d L : ℕ) (g t n : ℝ), 1 ≤ L → 0 < g → 0 < t → t < 1 → 0 ≤ n →
    n ≤ (d : ℝ) * (L : ℝ) / 2 → ((L : ℝ)⁻¹) ^ 2 ≤ lgEps d g t →
      n / ellT L g t ≤ (d : ℝ) / 2 * (lgEps d g t * (L : ℝ) ^ 2)

/-! ### (L3): conversions -/

private lemma lg_gam_pos (d : ℕ) {g t : ℝ} (hg : 0 < g) (ht : 0 < t) : 0 < lgGam d g t := by
  unfold lgGam; positivity

private lemma lg_eps_pos (d : ℕ) {g t : ℝ} (hg : 0 < g) (ht : 0 < t) (ht1 : t < 1) :
    0 < lgEps d g t := by
  unfold lgEps
  exact div_pos (by linarith) (lg_gam_pos d hg ht)

private lemma lg_gam_le (d : ℕ) {g t : ℝ} (hg : 0 < g) (ht : 0 < t) (ht1 : t < 1) :
    lgGam d g t ≤ g ^ 2 := by
  unfold lgGam
  have hs : 1 ≤ 1 + 2 * (d : ℝ) * g ^ 2 := by
    have : 0 ≤ 2 * (d : ℝ) * g ^ 2 := by positivity
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg g]

/-- `ε^{-1/2} ≤ g/√e`. -/
private lemma lg_sqrt_eps_inv_le (d : ℕ) {g t : ℝ} (hg : 0 < g) (ht : 0 < t) (ht1 : t < 1) :
    1 / Real.sqrt (lgEps d g t) ≤ g / Real.sqrt |1 - t| := by
  have hε := lg_eps_pos d hg ht ht1
  have he : 0 < 1 - t := by linarith
  have habs : |1 - t| = 1 - t := abs_of_pos he
  rw [habs]
  have hγ := lg_gam_pos d hg ht
  have hγg := lg_gam_le d hg ht ht1
  have h1 : 1 - t ≤ lgEps d g t * g ^ 2 := by
    unfold lgEps
    rw [div_mul_eq_mul_div, le_div_iff₀ hγ]
    nlinarith
  have h2 : Real.sqrt (1 - t) ≤ Real.sqrt (lgEps d g t) * g := by
    calc Real.sqrt (1 - t) ≤ Real.sqrt (lgEps d g t * g ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (lgEps d g t) * g := by
        rw [Real.sqrt_mul hε.le, Real.sqrt_sq hg.le]
  have hse : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr he
  have hsε : 0 < Real.sqrt (lgEps d g t) := Real.sqrt_pos.mpr hε
  rw [div_le_div_iff₀ hsε hse]
  linarith

/-- The common core of (L3b) and (L3c). -/
private lemma lg_ell_inv_le (d L : ℕ) {g t : ℝ} (hL : 1 ≤ L) (hg : 0 < g) (ht : 0 < t)
    (ht1 : t < 1) (h : ((L : ℝ)⁻¹) ^ 2 ≤ lgEps d g t) :
    (ellT L g t)⁻¹ ≤ Real.sqrt (lgEps d g t) := by
  have hε := lg_eps_pos d hg ht ht1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsε : 0 < Real.sqrt (lgEps d g t) := Real.sqrt_pos.mpr hε
  have hLs : (L : ℝ)⁻¹ ≤ Real.sqrt (lgEps d g t) := by
    rw [Real.le_sqrt (by positivity) hε.le]; exact h
  have h1 : 1 / Real.sqrt (lgEps d g t) ≤ ellT L g t := by
    refine le_min (le_max_of_le_left (lg_sqrt_eps_inv_le d hg ht ht1)) ?_
    rw [one_div]
    exact (inv_le_comm₀ hsε hLpos).mpr hLs
  rw [one_div] at h1
  have hpos : 0 < ellT L g t := lt_of_lt_of_le (inv_pos.mpr hsε) h1
  exact (inv_le_comm₀ hpos hsε).mpr h1

theorem lg_convB : ∀ (d L : ℕ) (g t : ℝ), 1 ≤ L → 0 < g → 0 < t → t < 1 →
    (((L : ℝ)⁻¹) ^ 2 ≤ lgEps d g t → (ellT L g t)⁻¹ ≤ Real.sqrt (lgEps d g t)) ∧
    (lgEps d g t < ((L : ℝ)⁻¹) ^ 2 → ellT L g t = (L : ℝ)) := by
  intro d L g t hL hg ht ht1
  refine ⟨lg_ell_inv_le d L hL hg ht ht1, ?_⟩
  intro h
  have hε := lg_eps_pos d hg ht ht1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsε : 0 < Real.sqrt (lgEps d g t) := Real.sqrt_pos.mpr hε
  have hLs : Real.sqrt (lgEps d g t) < (L : ℝ)⁻¹ := by
    rw [Real.sqrt_lt' (by positivity)]; exact h
  have h1 : (L : ℝ) < 1 / Real.sqrt (lgEps d g t) := by
    rw [one_div]
    exact (lt_inv_comm₀ hLpos hsε).mpr hLs
  have h2 : (L : ℝ) ≤ max (g / Real.sqrt |1 - t|) 1 :=
    le_max_of_le_left (h1.le.trans (lg_sqrt_eps_inv_le d hg ht ht1))
  unfold ellT
  exact min_eq_right h2

theorem lg_convC : ∀ (d L : ℕ) (g t n : ℝ), 1 ≤ L → 0 < g → 0 < t → t < 1 → 0 ≤ n →
    n ≤ (d : ℝ) * (L : ℝ) / 2 → ((L : ℝ)⁻¹) ^ 2 ≤ lgEps d g t →
      n / ellT L g t ≤ (d : ℝ) / 2 * (lgEps d g t * (L : ℝ) ^ 2) := by
  intro d L g t n hL hg ht ht1 hn hnd h
  have hε := lg_eps_pos d hg ht ht1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsε : 0 < Real.sqrt (lgEps d g t) := Real.sqrt_pos.mpr hε
  have hell := lg_ell_inv_le d L hL hg ht ht1 h
  have hLs : (L : ℝ)⁻¹ ≤ Real.sqrt (lgEps d g t) := by
    rw [Real.le_sqrt (by positivity) hε.le]; exact h
  have hx : 1 ≤ (L : ℝ) * Real.sqrt (lgEps d g t) := by
    have := mul_le_mul_of_nonneg_left hLs hLpos.le
    rwa [mul_inv_cancel₀ hLpos.ne'] at this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc n / ellT L g t = n * (ellT L g t)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ n * Real.sqrt (lgEps d g t) := mul_le_mul_of_nonneg_left hell hn
    _ ≤ ((d : ℝ) * L / 2) * Real.sqrt (lgEps d g t) := mul_le_mul_of_nonneg_right hnd hsε.le
    _ = (d : ℝ) / 2 * ((L : ℝ) * Real.sqrt (lgEps d g t)) := by ring
    _ ≤ (d : ℝ) / 2 * (((L : ℝ) * Real.sqrt (lgEps d g t)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = (d : ℝ) / 2 * (lgEps d g t * (L : ℝ) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hε.le]; ring

theorem lg_convA : ∀ (d : ℕ) (Λ : ℝ), 0 < Λ → ∃ C : ℝ, 0 < C ∧
    ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
      (1 ≤ lgEps d g t → 1 / (1 - t) ≤ C / (g ^ 2 + (1 - t))) ∧
      (lgEps d g t < 1 → 1 / lgGam d g t ≤ C / (g ^ 2 + (1 - t))) := by
  intro d Λ hΛ
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hP : 0 < Λ ^ 2 := by positivity
  refine ⟨3 + 4 * d * Λ ^ 2 + 2 * Λ ^ 2, by positivity, ?_⟩
  intro g t hg hgΛ ht ht1
  have hγ := lg_gam_pos d hg ht
  have he : 0 < 1 - t := by linarith
  have hG : 0 < g ^ 2 := by positivity
  have hGP : g ^ 2 ≤ Λ ^ 2 := by nlinarith
  set s : ℝ := 1 + 2 * (d : ℝ) * g ^ 2 with hs
  have hs1 : 1 ≤ s := by
    have : 0 ≤ 2 * (d : ℝ) * g ^ 2 := by positivity
    linarith
  have hsP : s ≤ 1 + 2 * d * Λ ^ 2 := by
    have : (d : ℝ) * g ^ 2 ≤ d * Λ ^ 2 := mul_le_mul_of_nonneg_left hGP hd
    rw [hs]; linarith
  have hspos : 0 < s := by linarith
  have hγeq : lgGam d g t = t * g ^ 2 / s := rfl
  constructor
  · intro h1
    have h2 : lgGam d g t ≤ 1 - t := by
      unfold lgEps at h1
      rwa [le_div_iff₀ hγ, one_mul] at h1
    rw [hγeq, div_le_iff₀ hspos] at h2
    rw [div_le_div_iff₀ he (by positivity)]
    rcases le_or_gt (1 / 2) t with ht2 | ht2
    · have h3 : g ^ 2 ≤ 2 * s * (1 - t) := by nlinarith
      have h4 : 2 * s * (1 - t) ≤ 2 * (1 + 2 * d * Λ ^ 2) * (1 - t) := by nlinarith
      nlinarith [mul_nonneg hd hP.le, mul_nonneg (mul_nonneg hd hP.le) he.le]
    · nlinarith
  · intro h1
    have h2 : 1 - t < lgGam d g t := by
      unfold lgEps at h1
      rwa [div_lt_one hγ] at h1
    rw [hγeq, lt_div_iff₀ hspos] at h2
    rw [hγeq, one_div, inv_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : s * g ^ 2 < t * g ^ 2 * (s + g ^ 2) := by nlinarith
    nlinarith [mul_nonneg hd hP.le, mul_pos ht hG]

/-! ### (L2): tail and head -/

private lemma lg_exp_form (ε κ T : ℝ) (hT : 0 < T) :
    (fun τ : ℝ => Real.exp (-ε * τ - κ * τ / T)) = fun τ : ℝ => Real.exp (-(ε + κ / T) * τ) := by
  funext τ
  congr 1
  field_simp
  ring

private lemma lg_tail_exact {T ε κ : ℝ} (hT : 0 < T) (h : 0 < ε + κ / T) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ - κ * τ / T)) (Ioi T) ∧
    ∫ τ in Ioi T, Real.exp (-ε * τ - κ * τ / T)
      = Real.exp (-ε * T) * Real.exp (-κ) / (ε + κ / T) := by
  rw [lg_exp_form ε κ T hT]
  have ha : -(ε + κ / T) < 0 := by linarith
  refine ⟨integrableOn_exp_mul_Ioi ha T, ?_⟩
  have e1 : -(ε + κ / T) * T = -ε * T + -κ := by field_simp; ring
  rw [integral_exp_mul_Ioi ha T, e1, Real.exp_add, neg_div, div_neg, neg_neg]

private lemma lg_head_le_Ioc {T ε : ℝ} (hT : 0 < T) (hε : 0 ≤ ε) :
    ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ T := by
  have hint : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioc 0 T) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-ε * τ)).integrableOn_Ioc
  calc ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ ∫ _τ in Ioc 0 T, (1 : ℝ) := by
        refine setIntegral_mono_on hint (integrableOn_const (by simp)) measurableSet_Ioc ?_
        intro τ hτ
        rw [Real.exp_le_one_iff]
        have := hτ.1
        nlinarith
    _ = T := by simp [Measure.real, hT.le]

private lemma lg_integral_exp_Ioi {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ)) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), Real.exp (-ε * τ) = 1 / ε := by
  have ha : -ε < 0 := by linarith
  refine ⟨integrableOn_exp_mul_Ioi ha 0, ?_⟩
  rw [integral_exp_mul_Ioi ha 0]
  simp [neg_div]

private lemma lg_head_le_inv {T ε : ℝ} (hε : 0 < ε) :
    ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ 1 / ε := by
  obtain ⟨hI, hv⟩ := lg_integral_exp_Ioi hε
  rw [← hv]
  refine setIntegral_mono_set hI (Filter.Eventually.of_forall fun τ => (Real.exp_pos _).le) ?_
  exact Filter.Eventually.of_forall (Ioc_subset_Ioi_self)

theorem lg_tail : ∀ T : ℝ, 0 < T →
    (∀ ε κ : ℝ, 0 ≤ ε → 0 < κ →
      IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ - κ * τ / T)) (Ioi T) ∧
      ∫ τ in Ioi T, Real.exp (-ε * τ - κ * τ / T) ≤ Real.exp (-ε * T) * (T / κ)) ∧
    (∀ ε κ : ℝ, 0 < ε → 0 ≤ κ →
      IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ - κ * τ / T)) (Ioi T) ∧
      ∫ τ in Ioi T, Real.exp (-ε * τ - κ * τ / T) ≤ Real.exp (-ε * T) / ε) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ T ∧
      (0 < ε → ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ 1 / ε)) := by
  intro T hT
  refine ⟨?_, ?_, ?_⟩
  · intro ε κ hε hκ
    have hκT : 0 < κ / T := div_pos hκ hT
    have hpos : 0 < ε + κ / T := by linarith
    obtain ⟨hI, hv⟩ := lg_tail_exact (ε := ε) hT hpos
    refine ⟨hI, ?_⟩
    rw [hv]
    have h1 : Real.exp (-κ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 1 / (ε + κ / T) ≤ T / κ := by
      rw [div_le_div_iff₀ hpos hκ]
      have : T * (κ / T) = κ := by field_simp
      nlinarith [mul_nonneg hT.le hε]
    have h3 : 0 < Real.exp (-ε * T) := Real.exp_pos _
    calc Real.exp (-ε * T) * Real.exp (-κ) / (ε + κ / T)
        = (Real.exp (-ε * T) * Real.exp (-κ)) * (1 / (ε + κ / T)) := by ring
      _ ≤ Real.exp (-ε * T) * 1 * (T / κ) := by
          apply mul_le_mul _ h2 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left h1 h3.le
      _ = Real.exp (-ε * T) * (T / κ) := by ring
  · intro ε κ hε hκ
    have hκT : 0 ≤ κ / T := div_nonneg hκ hT.le
    have hpos : 0 < ε + κ / T := by linarith
    obtain ⟨hI, hv⟩ := lg_tail_exact (ε := ε) hT hpos
    refine ⟨hI, ?_⟩
    rw [hv]
    have h1 : Real.exp (-κ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 1 / (ε + κ / T) ≤ 1 / ε := one_div_le_one_div_of_le hε (by linarith)
    have h3 : 0 < Real.exp (-ε * T) := Real.exp_pos _
    calc Real.exp (-ε * T) * Real.exp (-κ) / (ε + κ / T)
        = (Real.exp (-ε * T) * Real.exp (-κ)) * (1 / (ε + κ / T)) := by ring
      _ ≤ Real.exp (-ε * T) * 1 * (1 / ε) := by
          apply mul_le_mul _ h2 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left h1 h3.le
      _ = Real.exp (-ε * T) / ε := by ring
  · intro ε hε
    exact ⟨lg_head_le_Ioc hT hε, fun h => lg_head_le_inv h⟩

/-! ### The key lemma -/

/-- The substitution `u = 1/τ`: `∫₀^∞ τ^{-a} e^{-A/τ} dτ = Γ(a-1) A^{-(a-1)}`
for `a > 1`, `A > 0`. -/
private lemma lg_inv_gamma {a A : ℝ} (ha : 1 < a) (hA : 0 < A) :
    IntegrableOn (fun τ : ℝ => τ ^ (-a) * Real.exp (-A / τ)) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), τ ^ (-a) * Real.exp (-A / τ)
      = Real.Gamma (a - 1) * A ^ (-(a - 1)) := by
  have hgi : IntegrableOn (fun y : ℝ => y ^ (a - 2) * Real.exp (-A * y)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 2) (b := A)
      (by linarith) one_pos hA
    simpa only [Real.rpow_one] using this
  have hcongr : ∀ x ∈ Ioi (0 : ℝ),
      (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
        ((fun y : ℝ => y ^ (a - 2) * Real.exp (-A * y)) (x ^ (-1 : ℝ)))
        = x ^ (-a) * Real.exp (-A / x) := by
    intro x hx
    have hx' : 0 < x := hx
    simp only [smul_eq_mul, abs_neg, abs_one, one_mul]
    rw [Real.rpow_neg_one, Real.inv_rpow hx'.le, ← Real.rpow_neg hx'.le]
    rw [show -A * x⁻¹ = -A / x by ring, ← mul_assoc, ← Real.rpow_add hx']
    congr 3
    ring
  constructor
  · have h1 := (integrableOn_Ioi_comp_rpow_iff
      (fun y : ℝ => y ^ (a - 2) * Real.exp (-A * y)) (p := -1) (by norm_num)).mpr hgi
    exact h1.congr_fun hcongr measurableSet_Ioi
  · have h2 := integral_comp_rpow_Ioi (fun y : ℝ => y ^ (a - 2) * Real.exp (-A * y))
      (p := -1) (by norm_num)
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr] at h2
    rw [h2]
    have h3 := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := a - 2) (b := A)
      one_pos (by linarith) hA
    simp only [Real.rpow_one, div_one, mul_one] at h3
    rw [h3]
    ring_nf

/-- AM–GM: `√(cε) n ≤ ετ + (c/2) n²/τ`. -/
private lemma lg_amgm {c n ε τ : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (hτ : 0 < τ) :
    Real.sqrt (c * ε) * n ≤ ε * τ + c / 2 * n ^ 2 / τ := by
  have hp := Real.sq_sqrt hε
  have hq := Real.sq_sqrt hc
  have hp0 := Real.sqrt_nonneg ε
  have hq0 := Real.sqrt_nonneg c
  rw [Real.sqrt_mul hc]
  set p := Real.sqrt ε
  set q := Real.sqrt c
  have key : ε * τ + c / 2 * n ^ 2 / τ - q * p * n
      = ((p * τ) ^ 2 + (p * τ - q * n) ^ 2) / (2 * τ) := by
    rw [← hp, ← hq]
    field_simp
    ring
  have : 0 ≤ ((p * τ) ^ 2 + (p * τ - q * n) ^ 2) / (2 * τ) := by positivity
  linarith

theorem lg_key : ∀ m : ℕ, 3 ≤ m → ∀ c n ε : ℝ, 0 < c → 0 < n → 0 ≤ ε →
    IntegrableOn (fun τ : ℝ => τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)
      ≤ Real.Gamma ((m : ℝ) / 2 - 1) * (c / 2 * n ^ 2) ^ (-((m : ℝ) - 2) / 2)
          * Real.exp (-Real.sqrt (c * ε) * n) := by
  intro m hm c n ε hc hn hε
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 1 < (m : ℝ) / 2 := by linarith
  have hA : 0 < c / 2 * n ^ 2 := by positivity
  obtain ⟨hI, hv⟩ := lg_inv_gamma ha hA
  set B : ℝ → ℝ := fun τ => Real.exp (-Real.sqrt (c * ε) * n) *
    (τ ^ (-((m : ℝ) / 2)) * Real.exp (-(c / 2 * n ^ 2) / τ)) with hB
  have hBi : IntegrableOn B (Ioi 0) := hI.const_mul _
  have hle : ∀ τ ∈ Ioi (0 : ℝ),
      τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ) ≤ B τ := by
    intro τ hτ
    have hτ' : 0 < τ := hτ
    have h1 := lg_amgm (c := c) (n := n) hc.le hε hτ'
    have h2 : Real.exp (-ε * τ - c * n ^ 2 / τ)
        ≤ Real.exp (-Real.sqrt (c * ε) * n) * Real.exp (-(c / 2 * n ^ 2) / τ) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : -(c / 2 * n ^ 2) / τ = -(c / 2 * n ^ 2 / τ) := neg_div _ _
      have e2 : c * n ^ 2 / τ = c / 2 * n ^ 2 / τ + c / 2 * n ^ 2 / τ := by ring
      rw [this, e2]
      nlinarith
    have h3 : (-(m : ℝ) / 2) = -((m : ℝ) / 2) := by ring
    rw [h3, hB]
    change _ ≤ Real.exp (-Real.sqrt (c * ε) * n) *
      (τ ^ (-((m : ℝ) / 2)) * Real.exp (-(c / 2 * n ^ 2) / τ))
    have hpos : 0 ≤ τ ^ (-((m : ℝ) / 2)) := Real.rpow_nonneg hτ'.le _
    calc τ ^ (-((m : ℝ) / 2)) * Real.exp (-ε * τ - c * n ^ 2 / τ)
        ≤ τ ^ (-((m : ℝ) / 2)) * (Real.exp (-Real.sqrt (c * ε) * n) *
            Real.exp (-(c / 2 * n ^ 2) / τ)) := mul_le_mul_of_nonneg_left h2 hpos
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable
      (fun τ : ℝ => τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ))
      (volume.restrict (Ioi 0)) := by
    have : Measurable (fun τ : ℝ => τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)) := by
      fun_prop
    exact this.aestronglyMeasurable
  have hfi : IntegrableOn
      (fun τ : ℝ => τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)) (Ioi 0) := by
    refine Integrable.mono' hBi hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hτ' : 0 < τ := hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle τ hτ
  refine ⟨hfi, ?_⟩
  calc ∫ τ in Ioi (0 : ℝ), τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)
      ≤ ∫ τ in Ioi (0 : ℝ), B τ := setIntegral_mono_on hfi hBi measurableSet_Ioi hle
    _ = Real.exp (-Real.sqrt (c * ε) * n) *
          (Real.Gamma ((m : ℝ) / 2 - 1) * (c / 2 * n ^ 2) ^ (-((m : ℝ) / 2 - 1))) := by
        rw [hB, integral_const_mul, hv]
    _ = _ := by
        have : -((m : ℝ) - 2) / 2 = -((m : ℝ) / 2 - 1) := by ring
        rw [this]; ring

/-! ### (L1): the `n = 0` bound and the bulk bound -/

/-- `∫₀^∞ min(1, τ^{-m/2}) dτ = 1 + 2/(m-2)`. -/
private lemma lg_min_int {m : ℕ} (hm : 3 ≤ m) :
    IntegrableOn (fun τ : ℝ => min 1 (τ ^ (-(m : ℝ) / 2))) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), min 1 (τ ^ (-(m : ℝ) / 2)) = 1 + 2 / ((m : ℝ) - 2) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlt : -(m : ℝ) / 2 < -1 := by linarith
  have h1 : ∀ τ ∈ Ioc (0 : ℝ) 1, min 1 (τ ^ (-(m : ℝ) / 2)) = 1 := by
    intro τ hτ
    apply min_eq_left
    have : (1 : ℝ) = τ ^ (0 : ℝ) := (Real.rpow_zero τ).symm
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_ge hτ.1 hτ.2 (by linarith)
  have h2 : ∀ τ ∈ Ioi (1 : ℝ), min 1 (τ ^ (-(m : ℝ) / 2)) = τ ^ (-(m : ℝ) / 2) := by
    intro τ hτ
    apply min_eq_right
    have hτ1 : (1 : ℝ) ≤ τ := le_of_lt hτ
    calc τ ^ (-(m : ℝ) / 2) ≤ τ ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
      _ = 1 := Real.rpow_zero τ
  have hI1 : IntegrableOn (fun τ : ℝ => min 1 (τ ^ (-(m : ℝ) / 2))) (Ioc 0 1) := by
    refine (integrableOn_const (by simp)).congr_fun (fun τ hτ => (h1 τ hτ).symm)
      measurableSet_Ioc
  have hI2 : IntegrableOn (fun τ : ℝ => min 1 (τ ^ (-(m : ℝ) / 2))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hlt one_pos).congr_fun (fun τ hτ => (h2 τ hτ).symm)
      measurableSet_Ioi
  have hU : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  refine ⟨?_, ?_⟩
  · rw [← hU]; exact hI1.union hI2
  · rw [← hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hI1 hI2,
      setIntegral_congr_fun measurableSet_Ioc h1, setIntegral_congr_fun measurableSet_Ioi h2,
      integral_Ioi_rpow_of_lt hlt one_pos]
    have h3 : -(m : ℝ) / 2 + 1 ≠ 0 := by linarith
    simp only [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, mul_one, Real.one_rpow]
    simp only [sub_zero, zero_le_one, sup_of_le_left, add_right_inj]
    have h4 : (m : ℝ) - 2 ≠ 0 := by linarith
    rw [div_eq_div_iff h3 h4]
    ring

private lemma lg_integrand_nonneg (m : ℕ) (c n ε : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ lgIntegrand m c n ε τ := by
  unfold lgIntegrand
  have : 0 ≤ min 1 (τ ^ (-(m : ℝ) / 2)) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  positivity

private lemma lg_integrand_le_min (m : ℕ) {c n ε τ : ℝ} (hc : 0 ≤ c) (hn : 0 ≤ n) (hε : 0 ≤ ε)
    (hτ : 0 < τ) : lgIntegrand m c n ε τ ≤ min 1 (τ ^ (-(m : ℝ) / 2)) := by
  unfold lgIntegrand
  have h0 : 0 ≤ min 1 (τ ^ (-(m : ℝ) / 2)) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  have h1 : Real.exp (-ε * τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 : Real.exp (-c * min (n ^ 2 / τ) n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ min (n ^ 2 / τ) n := le_min (by positivity) hn
    nlinarith
  calc Real.exp (-ε * τ) * min 1 (τ ^ (-(m : ℝ) / 2)) * Real.exp (-c * min (n ^ 2 / τ) n)
      ≤ 1 * min 1 (τ ^ (-(m : ℝ) / 2)) * 1 := by gcongr
    _ = _ := by ring

private lemma lg_integrand_le_exp (m : ℕ) {c n ε τ : ℝ} (hc : 0 ≤ c) (hn : 0 ≤ n)
    (hτ : 0 < τ) : lgIntegrand m c n ε τ ≤ Real.exp (-ε * τ) := by
  unfold lgIntegrand
  have h0 : 0 ≤ min 1 (τ ^ (-(m : ℝ) / 2)) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  have h1 : min 1 (τ ^ (-(m : ℝ) / 2)) ≤ 1 := min_le_left _ _
  have h2 : Real.exp (-c * min (n ^ 2 / τ) n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ min (n ^ 2 / τ) n := le_min (by positivity) hn
    nlinarith
  calc Real.exp (-ε * τ) * min 1 (τ ^ (-(m : ℝ) / 2)) * Real.exp (-c * min (n ^ 2 / τ) n)
      ≤ Real.exp (-ε * τ) * 1 * 1 := by gcongr
    _ = _ := by ring

private lemma lg_integrand_meas (m : ℕ) (c n ε : ℝ) :
    AEStronglyMeasurable (lgIntegrand m c n ε) (volume.restrict (Ioi 0)) := by
  have : Measurable (lgIntegrand m c n ε) := by unfold lgIntegrand; fun_prop
  exact this.aestronglyMeasurable

private lemma lg_integrand_int {m : ℕ} (hm : 3 ≤ m) {c n ε : ℝ} (hc : 0 ≤ c) (hn : 0 ≤ n)
    (hε : 0 ≤ ε) : IntegrableOn (lgIntegrand m c n ε) (Ioi 0) := by
  refine Integrable.mono' (lg_min_int hm).1 (lg_integrand_meas m c n ε) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hτ' : 0 < τ := hτ
  rw [Real.norm_eq_abs, abs_of_nonneg (lg_integrand_nonneg m c n ε hτ')]
  exact lg_integrand_le_min m hc hn hε hτ'

theorem lg_zero : ∀ m : ℕ, 3 ≤ m → ∀ c ε : ℝ, 0 ≤ ε →
    IntegrableOn (lgIntegrand m c 0 ε) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), lgIntegrand m c 0 ε τ ≤ 1 + 2 / ((m : ℝ) - 2) ∧
    (0 < ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c 0 ε τ ≤ 1 / ε) := by
  intro m hm c ε hε
  have hc0 : lgIntegrand m c 0 ε = lgIntegrand m 0 0 ε := by
    funext τ; simp [lgIntegrand]
  rw [hc0]
  have hz : ∀ τ : ℝ, lgIntegrand m 0 0 ε τ
      = Real.exp (-ε * τ) * min 1 (τ ^ (-(m : ℝ) / 2)) := by
    intro τ
    simp [lgIntegrand]
  have hI : IntegrableOn (lgIntegrand m 0 0 ε) (Ioi 0) := by
    refine Integrable.mono' (lg_min_int hm).1 (lg_integrand_meas m 0 0 ε) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hτ' : 0 < τ := hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (lg_integrand_nonneg m 0 0 ε hτ'), hz]
    have h0 : 0 ≤ min 1 (τ ^ (-(m : ℝ) / 2)) := le_min zero_le_one (Real.rpow_nonneg hτ'.le _)
    have h1 : Real.exp (-ε * τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith
  refine ⟨hI, ?_, ?_⟩
  · rw [← (lg_min_int hm).2]
    refine setIntegral_mono_on hI (lg_min_int hm).1 measurableSet_Ioi ?_
    intro τ hτ
    exact lg_integrand_le_min m le_rfl le_rfl hε hτ
  · intro hε'
    obtain ⟨hE, hv⟩ := lg_integral_exp_Ioi hε'
    rw [← hv]
    refine setIntegral_mono_on hI hE measurableSet_Ioi ?_
    intro τ hτ
    exact lg_integrand_le_exp m (c := 0) le_rfl le_rfl hτ

/-- `n^k e^{-(c/2) n} ≤ k! (2/c)^k`. -/
private lemma lg_pow_exp_le {c : ℝ} (hc : 0 < c) (k : ℕ) {n : ℝ} (hn : 0 ≤ n) :
    n ^ k * Real.exp (-(c / 2) * n) ≤ (k.factorial : ℝ) * (2 / c) ^ k := by
  have h := Real.pow_div_factorial_le_exp ((c / 2) * n) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  have h2 : ((c / 2) * n) ^ k * (2 / c) ^ k = n ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have h3 : Real.exp ((c / 2) * n) * Real.exp (-(c / 2) * n) = 1 := by
    rw [← Real.exp_add]; simp
  calc n ^ k * Real.exp (-(c / 2) * n)
      = ((c / 2) * n) ^ k * (2 / c) ^ k * Real.exp (-(c / 2) * n) := by rw [h2]
    _ ≤ (Real.exp ((c / 2) * n) * k.factorial) * (2 / c) ^ k * Real.exp (-(c / 2) * n) := by
        gcongr
    _ = (Real.exp ((c / 2) * n) * Real.exp (-(c / 2) * n)) * (k.factorial * (2 / c) ^ k) := by
        ring
    _ = _ := by rw [h3, one_mul]

/-- Splitting at `τ = n`. -/
private lemma lg_bulk_split {m : ℕ} (hm : 3 ≤ m) {c n ε : ℝ} (hc : 0 ≤ c) (hn : 0 < n)
    (hε : 0 ≤ ε) :
    IntegrableOn (lgIntegrand m c n ε) (Ioc 0 n) ∧ IntegrableOn (lgIntegrand m c n ε) (Ioi n) ∧
    ∫ τ in Ioi (0 : ℝ), lgIntegrand m c n ε τ
      = (∫ τ in Ioc 0 n, lgIntegrand m c n ε τ) + ∫ τ in Ioi n, lgIntegrand m c n ε τ := by
  have hI := lg_integrand_int hm hc hn.le hε
  have hU : Ioc (0 : ℝ) n ∪ Ioi n = Ioi 0 := Ioc_union_Ioi_eq_Ioi hn.le
  have h1 : IntegrableOn (lgIntegrand m c n ε) (Ioc 0 n) :=
    hI.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn (lgIntegrand m c n ε) (Ioi n) :=
    hI.mono_set (Ioi_subset_Ioi hn.le)
  refine ⟨h1, h2, ?_⟩
  rw [← hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2]

/-- The head `(0, n]`: `min(n²/τ, n) = n`. -/
private lemma lg_bulk_head {m : ℕ} (hm : 3 ≤ m) {c n ε : ℝ} (hc : 0 ≤ c) (hn : 0 < n)
    (hε : 0 ≤ ε) :
    ∫ τ in Ioc 0 n, lgIntegrand m c n ε τ
      ≤ Real.exp (-c * n) * ∫ τ in Ioc 0 n, Real.exp (-ε * τ) := by
  obtain ⟨h1, -, -⟩ := lg_bulk_split hm hc hn hε
  have hg : IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ) * Real.exp (-c * n)) (Ioc 0 n) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-ε * τ) * Real.exp (-c * n)).integrableOn_Ioc
  calc ∫ τ in Ioc 0 n, lgIntegrand m c n ε τ
      ≤ ∫ τ in Ioc 0 n, Real.exp (-ε * τ) * Real.exp (-c * n) := by
        refine setIntegral_mono_on h1 hg measurableSet_Ioc ?_
        intro τ hτ
        have hτ0 : 0 < τ := hτ.1
        have hmin : min (n ^ 2 / τ) n = n := by
          apply min_eq_right
          rw [le_div_iff₀ hτ0]
          nlinarith [hτ.2]
        have h0 : 0 ≤ min 1 (τ ^ (-(m : ℝ) / 2)) :=
          le_min zero_le_one (Real.rpow_nonneg hτ0.le _)
        have h1' : min 1 (τ ^ (-(m : ℝ) / 2)) ≤ 1 := min_le_left _ _
        unfold lgIntegrand
        rw [hmin]
        have := Real.exp_pos (-ε * τ)
        have := Real.exp_pos (-c * n)
        calc Real.exp (-ε * τ) * min 1 (τ ^ (-(m : ℝ) / 2)) * Real.exp (-c * n)
            ≤ Real.exp (-ε * τ) * 1 * Real.exp (-c * n) := by gcongr
          _ = _ := by ring
    _ = Real.exp (-c * n) * ∫ τ in Ioc 0 n, Real.exp (-ε * τ) := by
        rw [integral_mul_const, mul_comm]

/-- The tail `(n, ∞)` through the key lemma. -/
private lemma lg_bulk_tail_key {m : ℕ} (hm : 3 ≤ m) {c n ε : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hε : 0 ≤ ε) :
    ∫ τ in Ioi n, lgIntegrand m c n ε τ
      ≤ Real.Gamma ((m : ℝ) / 2 - 1) * (c / 2 * n ^ 2) ^ (-((m : ℝ) - 2) / 2)
          * Real.exp (-Real.sqrt (c * ε) * n) := by
  obtain ⟨-, h2, -⟩ := lg_bulk_split hm hc.le hn hε
  obtain ⟨hKi, hKv⟩ := lg_key m hm c n ε hc hn hε
  have hKi' : IntegrableOn
      (fun τ : ℝ => τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)) (Ioi n) :=
    hKi.mono_set (Ioi_subset_Ioi hn.le)
  refine le_trans ?_ hKv
  calc ∫ τ in Ioi n, lgIntegrand m c n ε τ
      ≤ ∫ τ in Ioi n, τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ) := by
        refine setIntegral_mono_on h2 hKi' measurableSet_Ioi ?_
        intro τ hτ
        have hτn : n < τ := hτ
        have hτ0 : 0 < τ := lt_trans hn hτn
        have hmin : min (n ^ 2 / τ) n = n ^ 2 / τ := by
          apply min_eq_left
          rw [div_le_iff₀ hτ0]
          nlinarith
        have hr : 0 ≤ τ ^ (-(m : ℝ) / 2) := Real.rpow_nonneg hτ0.le _
        have h1' : min 1 (τ ^ (-(m : ℝ) / 2)) ≤ τ ^ (-(m : ℝ) / 2) := min_le_right _ _
        have e1 : Real.exp (-ε * τ - c * n ^ 2 / τ)
            = Real.exp (-ε * τ) * Real.exp (-c * (n ^ 2 / τ)) := by
          rw [← Real.exp_add]; congr 1; ring
        unfold lgIntegrand
        rw [hmin, e1]
        have := Real.exp_pos (-ε * τ)
        have := Real.exp_pos (-c * (n ^ 2 / τ))
        calc Real.exp (-ε * τ) * min 1 (τ ^ (-(m : ℝ) / 2)) * Real.exp (-c * (n ^ 2 / τ))
            ≤ Real.exp (-ε * τ) * τ ^ (-(m : ℝ) / 2) * Real.exp (-c * (n ^ 2 / τ)) := by
              gcongr
          _ = _ := by ring
    _ ≤ ∫ τ in Ioi (0 : ℝ), τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ) := by
        refine setIntegral_mono_set hKi ?_ (Filter.Eventually.of_forall (Ioi_subset_Ioi hn.le))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
        have hτ0 : 0 < τ := hτ
        have := Real.rpow_nonneg hτ0.le (-(m : ℝ) / 2)
        simp only [Pi.zero_apply]
        positivity

/-- The tail `(n, ∞)` for large `ε`. -/
private lemma lg_bulk_tail_exp {m : ℕ} (hm : 3 ≤ m) {c n ε : ℝ} (hc : 0 ≤ c) (hn : 0 < n)
    (hε : 0 < ε) :
    ∫ τ in Ioi n, lgIntegrand m c n ε τ ≤ Real.exp (-ε * n) / ε := by
  obtain ⟨-, h2, -⟩ := lg_bulk_split hm hc hn hε.le
  obtain ⟨hTi, hTv⟩ := (lg_tail n hn).2.1 ε 0 hε le_rfl
  refine le_trans ?_ hTv
  refine setIntegral_mono_on h2 hTi measurableSet_Ioi ?_
  intro τ hτ
  have hτ0 : 0 < τ := lt_trans hn hτ
  have := lg_integrand_le_exp m hc hn.le hτ0 (ε := ε)
  simpa using this

theorem lg_bulk : ∀ m : ℕ, 3 ≤ m → ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 0 < C ∧ ∃ c' : ℝ, 0 < c' ∧
      ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε →
        IntegrableOn (lgIntegrand m c n ε) (Ioi 0) ∧
        (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c n ε τ
            ≤ C * n ^ (-((m : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
        (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c n ε τ ≤ 2 / ε * Real.exp (-c' * n)) := by
  intro m hm c hc
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + 2 := ⟨m - 2, by omega⟩
  have hmk : (m : ℝ) = (k : ℝ) + 2 := by rw [hk]; push_cast; ring
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have ha : 0 < (m : ℝ) / 2 - 1 := by linarith
  set c' : ℝ := min (c / 2) 1 with hc'
  have hc'pos : 0 < c' := lt_min (by positivity) one_pos
  have hc'1 : c' ≤ c / 2 := min_le_left _ _
  have hc'2 : c' ≤ 1 := min_le_right _ _
  have hc'c : c' ≤ Real.sqrt c := by
    rw [Real.le_sqrt hc'pos.le hc.le]
    nlinarith
  set C1 : ℝ := ((k + 1).factorial : ℝ) * (2 / c) ^ (k + 1) with hC1
  set C2 : ℝ := Real.Gamma ((m : ℝ) / 2 - 1) * (c / 2) ^ (-((m : ℝ) - 2) / 2) with hC2
  have hC1pos : 0 < C1 := by
    have : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hC2pos : 0 < C2 :=
    mul_pos (Real.Gamma_pos_of_pos ha) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨C1 + C2, by positivity, c', hc'pos, ?_⟩
  intro n ε hn hε
  have hn0 : 0 < n := by linarith
  have hI := lg_integrand_int hm hc.le hn0.le hε
  refine ⟨hI, ?_, ?_⟩
  · -- the regime `ε ≤ 1`
    intro hε1
    obtain ⟨-, -, hsplit⟩ := lg_bulk_split hm hc.le hn0 hε
    have hhead := lg_bulk_head hm hc.le hn0 hε
    have htail := lg_bulk_tail_key hm hc hn0 hε
    have hhead2 : ∫ τ in Ioc 0 n, Real.exp (-ε * τ) ≤ n := lg_head_le_Ioc hn0 hε
    -- the powers of `n`
    have hnk : 0 < n ^ k := pow_pos hn0 k
    have hNn : n ^ (-((m : ℝ) - 2)) = (n ^ k)⁻¹ := by
      rw [show -((m : ℝ) - 2) = -(k : ℝ) by rw [hmk]; ring, Real.rpow_neg hn0.le,
        Real.rpow_natCast]
    have hNn2 : (c / 2 * n ^ 2) ^ (-((m : ℝ) - 2) / 2) = (c / 2) ^ (-((m : ℝ) - 2) / 2) *
        n ^ (-((m : ℝ) - 2)) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      push_cast
      ring
    set N : ℝ := n ^ (-((m : ℝ) - 2)) with hN
    have hNpos : 0 < N := by rw [hN]; exact Real.rpow_pos_of_pos hn0 _
    have hsq : Real.sqrt ε ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hε1
    have hsε : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
    set E : ℝ := Real.exp (-c' * n * Real.sqrt ε) with hE
    -- the Gauss part
    have hgauss : Real.exp (-Real.sqrt (c * ε) * n) ≤ E := by
      rw [hE]
      apply Real.exp_le_exp.mpr
      rw [Real.sqrt_mul hc.le]
      have : c' * Real.sqrt ε ≤ Real.sqrt c * Real.sqrt ε := mul_le_mul_of_nonneg_right hc'c hsε
      nlinarith
    have hkey : Real.Gamma ((m : ℝ) / 2 - 1) * (c / 2 * n ^ 2) ^ (-((m : ℝ) - 2) / 2)
          * Real.exp (-Real.sqrt (c * ε) * n) ≤ C2 * N * E := by
      rw [hNn2]
      have h0 : 0 ≤ C2 * N := by positivity
      calc Real.Gamma ((m : ℝ) / 2 - 1) * ((c / 2) ^ (-((m : ℝ) - 2) / 2) * N)
            * Real.exp (-Real.sqrt (c * ε) * n) = C2 * N * Real.exp (-Real.sqrt (c * ε) * n) := by
              rw [hC2]; ring
        _ ≤ C2 * N * E := mul_le_mul_of_nonneg_left hgauss h0
    -- the head part
    have hheadb : Real.exp (-c * n) * ∫ τ in Ioc 0 n, Real.exp (-ε * τ) ≤ C1 * N * E := by
      have hp := lg_pow_exp_le hc (k + 1) hn0.le
      have hexp : Real.exp (-c * n) = Real.exp (-(c / 2) * n) * Real.exp (-(c / 2) * n) := by
        rw [← Real.exp_add]; congr 1; ring
      have hexpE : Real.exp (-(c / 2) * n) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        have : c' * Real.sqrt ε ≤ c / 2 := by nlinarith
        nlinarith
      have h1 : Real.exp (-c * n) * ∫ τ in Ioc 0 n, Real.exp (-ε * τ)
          ≤ Real.exp (-c * n) * n :=
        mul_le_mul_of_nonneg_left hhead2 (Real.exp_pos _).le
      have h2 : Real.exp (-c * n) * n ≤ C1 * N * Real.exp (-(c / 2) * n) := by
        rw [hexp, hNn]
        have hpow : n ^ (k + 1) * (n ^ k)⁻¹ = n := by
          rw [pow_succ]; field_simp
        calc Real.exp (-(c / 2) * n) * Real.exp (-(c / 2) * n) * n
            = Real.exp (-(c / 2) * n) * Real.exp (-(c / 2) * n) * (n ^ (k + 1) * (n ^ k)⁻¹) := by
              rw [hpow]
          _ = (n ^ (k + 1) * Real.exp (-(c / 2) * n)) * (n ^ k)⁻¹ * Real.exp (-(c / 2) * n) := by
              ring
          _ ≤ C1 * (n ^ k)⁻¹ * Real.exp (-(c / 2) * n) := by
              gcongr
          _ = _ := by ring
      calc Real.exp (-c * n) * ∫ τ in Ioc 0 n, Real.exp (-ε * τ)
          ≤ Real.exp (-c * n) * n := h1
        _ ≤ C1 * N * Real.exp (-(c / 2) * n) := h2
        _ ≤ C1 * N * E := mul_le_mul_of_nonneg_left hexpE (by positivity)
    rw [hsplit]
    calc (∫ τ in Ioc 0 n, lgIntegrand m c n ε τ) + ∫ τ in Ioi n, lgIntegrand m c n ε τ
        ≤ C1 * N * E + C2 * N * E := add_le_add (hhead.trans hheadb) (htail.trans hkey)
      _ = (C1 + C2) * N * E := by ring
  · -- the regime `ε ≥ 1`
    intro hε1
    have hεpos : 0 < ε := by linarith
    obtain ⟨-, -, hsplit⟩ := lg_bulk_split hm hc.le hn0 hε
    have hhead := lg_bulk_head hm hc.le hn0 hε
    have htail := lg_bulk_tail_exp hm hc.le hn0 hεpos
    have hhead2 : ∫ τ in Ioc 0 n, Real.exp (-ε * τ) ≤ 1 / ε := lg_head_le_inv hεpos
    have h1 : Real.exp (-c * n) ≤ Real.exp (-c' * n) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have h2 : Real.exp (-ε * n) ≤ Real.exp (-c' * n) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [hsplit]
    calc (∫ τ in Ioc 0 n, lgIntegrand m c n ε τ) + ∫ τ in Ioi n, lgIntegrand m c n ε τ
        ≤ Real.exp (-c * n) * (1 / ε) + Real.exp (-ε * n) / ε :=
          add_le_add (hhead.trans (mul_le_mul_of_nonneg_left hhead2 (Real.exp_pos _).le)) htail
      _ ≤ Real.exp (-c' * n) * (1 / ε) + Real.exp (-c' * n) / ε := by
          gcongr
      _ = 2 / ε * Real.exp (-c' * n) := by ring

/-! ### The theorems are the pinned statements -/

example : LGKey := lg_key
example : LGBulk := lg_bulk
example : LGZero := lg_zero
example : LGTail := lg_tail
example : LGConvA := lg_convA
example : LGConvB := lg_convB
example : LGConvC := lg_convC

/-! ### Compiled nonempty instances (concrete, nondegenerate data) -/

/-- `lg_key` at `m = 3`, `c = 1`, `n = 1`, `ε = 1/2`. -/
example := lg_key 3 (by norm_num) 1 1 (1 / 2) one_pos one_pos (by norm_num)

/-- `lg_key` at `m = 5`, `c = 0.18`, `n = 5`, `ε = 0` (no `ε`-decay). -/
example := lg_key 5 (by norm_num) 0.18 5 0 (by norm_num) (by norm_num) le_rfl

/-- `lg_bulk` at `m = 3`, `c = 0.18`: the bulk bound at `n = 5`, `ε = 1/2` and the large-`ε` bound
at `n = 2`, `ε = 2`; the constants `C`, `c'` are fixed before `n`, `ε`. -/
example : ∃ C : ℝ, 0 < C ∧ ∃ c' : ℝ, 0 < c' ∧
    IntegrableOn (lgIntegrand 3 0.18 5 (1 / 2)) (Ioi 0) ∧
    (∫ τ in Ioi (0 : ℝ), lgIntegrand 3 0.18 5 (1 / 2) τ
      ≤ C * (5 : ℝ) ^ (-(((3 : ℕ) : ℝ) - 2)) * Real.exp (-c' * 5 * Real.sqrt (1 / 2))) ∧
    (∫ τ in Ioi (0 : ℝ), lgIntegrand 3 0.18 2 2 τ ≤ 2 / 2 * Real.exp (-c' * 2)) := by
  obtain ⟨C, hC, c', hc', h⟩ := lg_bulk 3 (by norm_num) 0.18 (by norm_num)
  obtain ⟨h1, h2, -⟩ := h 5 (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨-, -, h3⟩ := h 2 2 (by norm_num) (by norm_num)
  exact ⟨C, hC, c', hc', h1, h2 (by norm_num), h3 (by norm_num)⟩

/-- `lg_zero` at `m = 3`, `c = 1`: `ε = 0` (the integral is `≤ 1 + 2/(3-2) = 3`) and `ε = 1`. -/
example := lg_zero 3 (by norm_num) 1 0 le_rfl

example : ∫ τ in Ioi (0 : ℝ), lgIntegrand 3 1 0 1 τ ≤ 1 / 1 :=
  (lg_zero 3 (by norm_num) 1 1 zero_le_one).2.2 one_pos

/-- `lg_tail` at `T = 9`: all three clauses. -/
example : (IntegrableOn (fun τ : ℝ => Real.exp (-(1 / 2 : ℝ) * τ - 16 * τ / 9)) (Ioi 9) ∧
      ∫ τ in Ioi (9 : ℝ), Real.exp (-(1 / 2 : ℝ) * τ - 16 * τ / 9)
        ≤ Real.exp (-(1 / 2 : ℝ) * 9) * (9 / 16)) ∧
    (IntegrableOn (fun τ : ℝ => Real.exp (-(1 / 2 : ℝ) * τ - (1 / 2) * τ / 9)) (Ioi 9) ∧
      ∫ τ in Ioi (9 : ℝ), Real.exp (-(1 / 2 : ℝ) * τ - (1 / 2) * τ / 9)
        ≤ Real.exp (-(1 / 2 : ℝ) * 9) / (1 / 2)) ∧
    (∫ τ in Ioc (0 : ℝ) 9, Real.exp (-(1 / 2 : ℝ) * τ) ≤ 9 ∧
      ∫ τ in Ioc (0 : ℝ) 9, Real.exp (-(1 / 2 : ℝ) * τ) ≤ 1 / (1 / 2)) := by
  obtain ⟨h1, h2, h3⟩ := lg_tail 9 (by norm_num)
  exact ⟨h1 (1 / 2) 16 (by norm_num) (by norm_num), h2 (1 / 2) (1 / 2) (by norm_num) (by norm_num),
    (h3 (1 / 2) (by norm_num)).1, (h3 (1 / 2) (by norm_num)).2 (by norm_num)⟩

/-- `lg_convA` at `d = 3`, `Λ = 1`: at `g = 1/2`, `t = 1/2` (`ε = 10 ≥ 1`) and at `g = 1/2`,
`t = 0.999` (`ε ≈ 0.01 < 1`). -/
example : ∃ C : ℝ, 0 < C ∧
    1 / (1 - (1 / 2 : ℝ)) ≤ C / ((1 / 2 : ℝ) ^ 2 + (1 - 1 / 2)) ∧
    1 / lgGam 3 (1 / 2) 0.999 ≤ C / ((1 / 2 : ℝ) ^ 2 + (1 - 0.999)) := by
  obtain ⟨C, hC, h⟩ := lg_convA 3 1 one_pos
  refine ⟨C, hC, ?_, ?_⟩
  · exact (h (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
      (by norm_num [lgEps, lgGam])
  · exact (h (1 / 2) 0.999 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
      (by norm_num [lgEps, lgGam])

/-- `lg_convB` at `d = 3`, `L = 5`, `g = 1/2`, `t = 1/2` (`ε = 10 ≥ L⁻²`, clause (a)) and at
`t = 0.999` (`ε ≈ 0.01 < L⁻² = 0.04`, clause (b), `ℓ_t = L`). -/
example : (ellT 5 (1 / 2) (1 / 2))⁻¹ ≤ Real.sqrt (lgEps 3 (1 / 2) (1 / 2)) :=
  (lg_convB 3 5 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
    (by norm_num [lgEps, lgGam])

example : ellT 5 (1 / 2) 0.999 = (5 : ℕ) :=
  (lg_convB 3 5 (1 / 2) 0.999 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num [lgEps, lgGam])

/-- `lg_convC` at `d = 3`, `L = 5`, `g = 1/2`, `t = 1/2`, `n = 7 ≤ dL/2 = 7.5`. -/
example : (7 : ℝ) / ellT 5 (1 / 2) (1 / 2)
    ≤ ((3 : ℕ) : ℝ) / 2 * (lgEps 3 (1 / 2) (1 / 2) * ((5 : ℕ) : ℝ) ^ 2) :=
  lg_convC 3 5 (1 / 2) (1 / 2) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [lgEps, lgGam])

end RBM.Heat
