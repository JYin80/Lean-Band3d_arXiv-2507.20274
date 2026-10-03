/-
Release check for T2011 (dispatcher V1, Sat Oct  3 00:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §14).
Pinned `Prop` statements of PT-B2 (route H pilot part 2: bounds on `ℤ`; Fable review §1 F2, §2 S3-Z (a)–(c)).
Namespace `RBM.Heat.T2011Check` here; the theorems go to `RBM.Heat`.
Statements and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2011-check.lean`.
-/
import RBM3D

#check @RBM.Heat.hkZ
#check @RBM.Heat.hkZ_nonneg
#check @RBM.Heat.hkZ_mass
#check @RBM.Heat.hkZ_neg
#check @RBM.Heat.hkZ_tilt
#check @RBM.Heat.hkZ_hasSum_mgf
#check @Real.cosh_le_exp_half_sq
#check @Real.mul_le_sin
#check @integral_gaussian

namespace RBM.Heat.T2011Check

open RBM.Heat

/-- Target 1, (a): `h_τ(n) ≤ C min(1, τ^{-1/2}) e^{-c min(n²/τ, |n|)}` (Fable: `C = 1` with
`min(1, (√π/4) τ^{-1/2})`, `c = 0.18`, or `0.14` via `Real.cosh_le_exp_half_sq`). -/
def Bound : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    hkZ τ n ≤ C * min 1 (τ ^ (-(1 / 2 : ℝ))) * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|)

/-- Target 2, (b): first difference, `min(1, τ^{-1})`. -/
def Diff1 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    |hkZ τ (n + 1) - hkZ τ n| ≤ C * min 1 τ⁻¹ * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|)

/-- Target 3, (c): second difference, `min(1, τ^{-3/2})`. -/
def Diff2 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    |hkZ τ (n + 1) + hkZ τ (n - 1) - 2 * hkZ τ n|
      ≤ C * min 1 (τ ^ (-(3 / 2 : ℝ))) * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|)

end RBM.Heat.T2011Check
