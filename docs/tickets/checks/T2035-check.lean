/-
Release check for T2035 (dispatcher V1, Sat Oct  3 05:28 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §18).
EK-5 proves the pin `EKSumDecayNonzero` (`lem:sum_decay_nonzero`, loss-free, both charges) already merged in
`RBM3D/Evolution/Pins.lean` (EK-1).  Nothing is restated here: this file only checks that the pin, the EK-2
theorem, the proved PT properties and the merged zero-mode machinery the ticket names exist.
Statements and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2035-check.lean`.
-/
import RBM3D

-- the target (pin of EK-1)
#check (RBM.EKSumDecayNonzero : ℕ → ℕ → ℝ → ℝ → Prop)
#print RBM.EKSumDecayNonzero

-- vocabulary and the merged machinery to copy-adapt
#check @RBM.EKsgn
#check @RBM.UN
#check @RBM.zeroModeSet
#check @RBM.projMat
#check @RBM.tensorKer
#check @RBM.zeroModeSet_tensorKer
#check @RBM.norm_tensorKer_le
#check @RBM.norm_zeroModeSet_UN_le
#check @RBM.Theta0
#check @RBM.cycProd

-- inputs named by the ticket
#check @RBM.ekSameRow_holds
#check @RBM.prop5Short_holds
#check @RBM.prop8ZeroMode_holds
#check (RBM.Prop8ZeroMode : ℕ → ℝ → ℝ → Prop)

-- the target type the prover must produce
example : Prop := ∀ (d n : ℕ) (Λ κ : ℝ), RBM.EKSumDecayNonzero d n Λ κ
