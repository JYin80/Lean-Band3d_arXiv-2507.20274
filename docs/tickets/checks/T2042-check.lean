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

example : Prop := ∀ (d n : ℕ) (Λ κ : ℝ), RBM.EKSumDecay2 d n Λ κ
