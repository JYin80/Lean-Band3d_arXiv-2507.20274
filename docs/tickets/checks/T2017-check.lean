/-
Release check for T2017 (dispatcher V1, Sat Oct  3 02:04 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §14).
Pinned `Prop` statements of PT-C (route H: the torus kernel; Fable review §1 F3, §2 S3-L).
Namespace `RBM.Heat.T2017Check` here; the theorems go to `RBM.Heat`.
Statements and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2017-check.lean`.
-/
import RBM3D

#check @RBM.zdist
#check @RBM.Heat.hkT
#check @RBM.Heat.hkT_hasSum_images
#check @RBM.Heat.hkT_mass
#check @RBM.Heat.hkZ_le
#check @RBM.Heat.hkZ_diff1_le
#check @RBM.Heat.hkZ_diff2_le

namespace RBM.Heat.T2017Check

open RBM.Heat

/-- Target 1 (`τ ≤ L²`, (a)): `hk(τ, x) ≤ C min(1, τ^{-1/2}) e^{-c min(|x|_L²/τ, |x|_L)}`. -/
def TorusBound : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
    ∀ x : ZMod L,
      hkT L τ x ≤ C * min 1 (τ ^ (-(1 / 2 : ℝ)))
        * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ))

/-- Target 2 (`τ ≤ L²`, (b)): first difference. -/
def TorusDiff1 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
    ∀ x : ZMod L,
      |hkT L τ (x + 1) - hkT L τ x| ≤ C * min 1 τ⁻¹
        * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ))

/-- Target 3 (`τ ≤ L²`, (c)): second difference. -/
def TorusDiff2 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
    ∀ x : ZMod L,
      |hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x| ≤ C * min 1 (τ ^ (-(3 / 2 : ℝ)))
        * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ))

/-- Target 4 (`τ ≥ L²`): the zero mode and the spectral gap,
`|hk − 1/L| ≤ (C/L) e^{-cτ/L²}`, `|Δ₁ hk| ≤ (C/L²) e^{-cτ/L²}`, `|Δ₂ hk| ≤ (C/L³) e^{-cτ/L²}`. -/
def TorusGap : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ x : ZMod L,
    |hkT L τ x - (L : ℝ)⁻¹| ≤ C * (L : ℝ)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
    |hkT L τ (x + 1) - hkT L τ x| ≤ C * ((L : ℝ) ^ 2)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
    |hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x|
      ≤ C * ((L : ℝ) ^ 3)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2)

end RBM.Heat.T2017Check
