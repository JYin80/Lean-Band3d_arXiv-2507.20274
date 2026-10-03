/-
Release check for T2010 (dispatcher V1, Sat Oct  3 00:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §14).
Pinned definitions and `Prop` statements of PT-E (route H step S5, Θ-free; Fable review §1 F5, §2 S5 (L1)–(L3)).
Namespace `RBM.Heat.T2010Check` here becomes `RBM.Heat` in the ticket.
Definitions and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2010-check.lean`.
-/
import RBM3D
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma

open MeasureTheory Set

#check @Real.Gamma_eq_integral
#check @integral_rpow_mul_exp_neg_mul_rpow
#check @integral_exp_mul_Ioi
#check @integrableOn_Ioi_rpow_of_lt
#check @integral_Ioi_rpow_of_lt
#check @integral_comp_rpow_Ioi
#check @MeasureTheory.setIntegral_mono_on
#check @RBM.ellT

namespace RBM.Heat.T2010Check

/-- The Laplace–Gauss integrand `e^{-ετ} min(1, τ^{-m/2}) e^{-c min(n²/τ, n)}` (route H, step S5;
Fable review §2 S5 (L1)).  Only `τ > 0` is ever used. -/
noncomputable def lgIntegrand (m : ℕ) (c n ε τ : ℝ) : ℝ :=
  Real.exp (-ε * τ) * min 1 (τ ^ (-(m : ℝ) / 2)) * Real.exp (-c * min (n ^ 2 / τ) n)

/-- `γ = t s₀ g²`, `s₀ = (1 + 2dg²)⁻¹`: the diffusion constant of `1 − tS = e + γ Σ_j Δ_j`
(route H, step S1; Fable F1).  `e = 1 − t`. -/
noncomputable def lgGam (d : ℕ) (g t : ℝ) : ℝ := t * g ^ 2 / (1 + 2 * (d : ℝ) * g ^ 2)

/-- `ε = e / γ`, the parameter that decides the regime (Fable F5: regimes by `ε`, not by `e ≷ g²`). -/
noncomputable def lgEps (d : ℕ) (g t : ℝ) : ℝ := (1 - t) / lgGam d g t

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

end RBM.Heat.T2010Check
