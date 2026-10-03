/-
Release check for T2026 (dispatcher V1, Sat Oct  3 04:39 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §18).
Pinned `Prop` statements of EK-2: the decay of the one-index kernel `Ξ = (t−s)μ S Θ_{tμ}` (`(eq:decayXi)`),
its ball sums, and the same-sign row bound (`(eq:samecolor)`), uniform in `g ∈ (0, Λ]`, on the PT pins.
They are the conclusions of the probe lemmas `ek_norm_XiKer_apply_le`, `ek_sum_ball_norm_XiKer_le`
(`c961e62:RBM3D/Probe/T2016Pins.lean` lines 211–372) with the decay hypothesis supplied by `Prop5Decay`,
and of the merged `exists_norm_uKer_same_le` (`RBM3D/Kernel/Evolution.lean:445`) with `Prop5Short` (proved) for the
old `ThetaDecayShort`.  Namespace `RBM.T2026Check` here becomes `RBM` in the ticket.
Statements and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2026-check.lean`.
-/
import RBM3D

#check @RBM.XiKer
#check @RBM.uKer
#check @RBM.PropSpin
#check @RBM.Prop5Decay
#check @RBM.prop5Short_holds
#check @RBM.norm_Theta_apply_le
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.exists_norm_uKer_same_le
#check @RBM.sum_ball_norm_XiKer_le
#check @RBM.norm_XiKer_apply_le

namespace RBM.T2026Check

open RBM
open scoped Matrix.Norms.Operator

/-- `(eq:decayXi)`, uniform in `g ∈ (0, Λ]` and in the unit `μ`, from pin 5 (`Prop5Decay`). -/
def EKXiDecay (d : ℕ) (Λ : ℝ) : Prop :=
  Prop5Decay d Λ → 3 ≤ d → 0 < Λ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ μ : ℂ, ‖μ‖ = 1 →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
          haveI : NeZero L := ⟨by omega⟩
          ∀ a b : Zd d L,
            ‖XiKer d L g μ s t a b‖
              ≤ C * (1 - s) * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L (a - b) : ℝ) + 1) ^ (d - 2))⁻¹
                * Real.exp (-(c * (zdistD d L (a - b) : ℝ)) / ellT L g t)

/-- Ball sums of `Ξ` over any set within distance `R ≤ Λ' ℓ_s` of a centre (pin 5 again). -/
def EKXiBall (d : ℕ) (Λ : ℝ) : Prop :=
  Prop5Decay d Λ → 3 ≤ d → 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ μ : ℂ, ‖μ‖ = 1 →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
          ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
          haveI : NeZero L := ⟨by omega⟩
          ∀ (a ctr : Zd d L) (D : Finset (Zd d L)), (∀ b ∈ D, (zdistD d L (ctr - b) : ℝ) ≤ R) →
            ∑ b ∈ D, ‖XiKer d L g μ s t a b‖ ≤ C * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))

/-- `(eq:samecolor)`: at a same-sign index the one-index factor `(1 − sμS)Θ_{tμ}`, `μ = m(σ)²`, is bounded in
the `∞ → ∞` norm, uniformly in `L, g ≤ Λ, s, t`; bulk `κ ≤ Im m`. -/
def EKSameRow (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im →
        ∀ σ : Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
          haveI : NeZero L := ⟨by omega⟩
          ‖uKer d L g (PropSpin m σ * PropSpin m σ) s t‖ ≤ C

end RBM.T2026Check
