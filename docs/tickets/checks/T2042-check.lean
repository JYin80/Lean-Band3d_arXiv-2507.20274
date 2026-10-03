/-
Release check for T2042 (dispatcher V1, Sat Oct  3 06:26 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §18).
EK-4 proves the pin `EKSumDecay2` (`(sum_res_2)` under `(sumAzero)`), merged in `RBM3D/Evolution/Pins.lean` (EK-1).
Nothing is restated: this file checks that the pin, the EK-2 / EK-3 inputs and the PT property 6 exist.
Statements and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2042-check.lean`.
-/
import RBM3D

#check (RBM.EKSumDecay2 : ℕ → ℕ → ℝ → ℝ → Prop)
#print RBM.EKSumDecay2
#check @RBM.EKSumZero
#check @RBM.EKFastDecay
#check @RBM.XiKer
#check @RBM.ekXiDecay_holds
#check @RBM.ekXiBall_holds
#check @RBM.ekSumDecay1_holds
#check @RBM.ek_core_bound
#check @RBM.ek_anchor_sum_le
#check @RBM.ek_UN_anchor_bound
#check (RBM.Prop6Diff1 : ℕ → ℝ → ℝ → ℝ → Prop)
#check @RBM.prop6Diff1_holds
#check @RBM.prop5Decay_holds
#check @RBM.prop5Short_holds

-- Amend 1 (dispatcher V1, Sat Oct  3 08:13 UTC 2026; DECISIONS §21): the amended pin.  The merged `RBM.EKSumDecay2` above is the
-- old text (false: T2042 preflight); T2042 replaces its body in `RBM3D/Evolution/Pins.lean` by the one below.
namespace RBM.T2042Check

open RBM

/-- `(sumAzero) ⟹ (sum_res_2)` with `L^d ≤ W^K` (candidate `T2042a`, DECISIONS §21); `C` depends on `K`. -/
def EKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop :=
  Prop5Decay d Λ → Prop5Short d Λ κ → Prop6Diff1 d Λ κ (1 / 2) →
    3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
    ∀ K : ℝ, 0 < K →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
        (L : ℝ) ^ d ≤ W ^ K →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          EKFastDecay g s W ε D A → EKSumZero A →
          ‖UN d L g (EKsgn m σ) s t A‖ ≤
            W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)

end RBM.T2042Check

example : Prop := ∀ (d n : ℕ) (Λ κ : ℝ), RBM.T2042Check.EKSumDecay2 d n Λ κ
