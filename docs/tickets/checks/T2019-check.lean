/-
Release check for T2019 (dispatcher V1, Sat Oct  3 03:21 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §14).
Pinned definition and `Prop` statements of PT-D (route H: the exact Laplace–product representation of `Θ_t`
and the bounds of the product kernel; Fable review §1 F1, F4, §2 S4).
Namespace `RBM.Heat.T2019Check` here becomes `RBM.Heat` in the ticket.
Definitions and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2019-check.lean`.
-/
import RBM3D

#check @RBM.Theta
#check @RBM.SB
#check @RBM.eq_Theta_of_mul
#check @RBM.Theta0_apply_eq
#check @RBM.zdistD
#check @RBM.Heat.hkT
#check @RBM.Heat.hkT_mass
#check @RBM.Heat.lgGam
#check @RBM.Heat.hkT_le
#check @RBM.Heat.hkT_diff1_le
#check @RBM.Heat.hkT_diff2_le
#check @RBM.Heat.hkT_gap

namespace RBM.Heat.T2019Check

open RBM RBM.Heat MeasureTheory Set

/-- The product kernel `K_τ(a) = ∏_j hk(τ, a_j)` on `ℤ_L^d` (route H, step S4). -/
noncomputable def kProd (d L : ℕ) [NeZero L] (τ : ℝ) (a : Zd d L) : ℝ := ∏ j, hkT L τ (a j)

/-- Target 1 (F1, exact): `Θ_t(0, a) = ∫₀^∞ e^{-(1-t)s} K_{γs}(a) ds`, `γ = t g²/(1 + 2dg²)`, for real
`t ∈ [0, 1)` (the sign pairs with `m(σ₁)m(σ₂) = 1`). -/
def LaplaceProd : Prop :=
  ∀ (d L : ℕ) (hL : 3 ≤ L) (g t : ℝ), 0 < g → 0 ≤ t → t < 1 → ∀ a : Zd d L,
    haveI : NeZero L := ⟨by omega⟩
    Theta d L g (t : ℂ) 0 a =
      ((∫ s in Ioi (0 : ℝ), Real.exp (-(1 - t) * s) * kProd d L (lgGam d g t * s) a : ℝ) : ℂ)

/-- Target 2 (F4, the `1/d` lemma; the version without `1/d` is false, `x = (1, 50, 0)`, `τ = 10`). -/
def SumMin : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ τ : ℝ, 0 < τ → ∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j) →
    (d : ℝ)⁻¹ * min ((∑ j, x j) ^ 2 / τ) (∑ j, x j) ≤ ∑ j, min (x j ^ 2 / τ) (x j)

/-- Target 3 (`τ ≤ L²`): `K_τ(a) ≤ C min(1, τ^{-d/2}) e^{-c min(|a|²/τ, |a|)}`, `|a|` the torus `ℓ¹` norm. -/
def KProdBound : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
      kProd d L τ a ≤ C * min 1 (τ ^ (-(d : ℝ) / 2))
        * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ))

/-- Target 4 (`τ ≤ L²`): unit first differences, `min(1, τ^{-(d+1)/2})`. -/
def KProdDiff1 : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (j : Fin d),
      |kProd d L τ (a + Pi.single j 1) - kProd d L τ a| ≤ C * min 1 (τ ^ (-((d : ℝ) + 1) / 2))
        * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ))

/-- Target 5 (`τ ≤ L²`): unit second differences, mixed (`i ≠ j`) and same-direction (`i = j`),
`min(1, τ^{-(d+2)/2})` (Fable F7: both are needed). -/
def KProdDiff2 : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (i j : Fin d),
      |kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
          - kProd d L τ (a + Pi.single j 1) + kProd d L τ a|
        ≤ C * min 1 (τ ^ (-((d : ℝ) + 2) / 2))
          * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ))

/-- Target 6 (`τ ≥ L²`): the zero mode `L^{-d}` and the gap, for the kernel and its unit differences. -/
def KProdGap : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ (a : Zd d L) (i j : Fin d),
      |kProd d L τ a - ((L : ℝ) ^ d)⁻¹| ≤ C * ((L : ℝ) ^ d)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
      |kProd d L τ (a + Pi.single j 1) - kProd d L τ a|
        ≤ C * ((L : ℝ) ^ (d + 1))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
      |kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
          - kProd d L τ (a + Pi.single j 1) + kProd d L τ a|
        ≤ C * ((L : ℝ) ^ (d + 2))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2)

end RBM.Heat.T2019Check
