/-
Release check for T2034 (dispatcher V1, Sat Oct  3 05:28 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §18).
EK-3 proves two pins already merged in `RBM3D/Evolution/Pins.lean` (EK-1): `EKSumDecay1` = `(sum_res_1)` and
`EKSumDecayNAL` = `(sum_res_2_NAL)` of `lem:sum_decay`, for every `n`.  Nothing is restated here: this file only
checks that the pins, the EK-2 theorems and the merged ingredients the ticket names exist with the expected types.
Statements and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2034-check.lean`.
-/
import RBM3D

-- the two targets (pins of EK-1)
#check (RBM.EKSumDecay1 : ℕ → ℕ → ℝ → Prop)
#check (RBM.EKSumDecayNAL : ℕ → ℕ → ℝ → ℝ → Prop)
#print RBM.EKSumDecay1
#print RBM.EKSumDecayNAL

-- vocabulary
#check @RBM.EKsgn
#check @RBM.EKFastDecay
#check @RBM.UN
#check @RBM.uKer
#check @RBM.XiKer
#check @RBM.cycProd
#check @RBM.ellT

-- inputs named by the ticket
#check @RBM.ekXiDecay_holds
#check @RBM.ekXiBall_holds
#check @RBM.ekSameRow_holds
#check @RBM.ekSumNdecay_holds
#check @RBM.UN_apply_eq_sum_powerset
#check @RBM.prop5Decay_holds
#check @RBM.prop5Short_holds

-- the target types the prover must produce
example : Prop := ∀ (d n : ℕ) (Λ : ℝ), RBM.EKSumDecay1 d n Λ
example : Prop := ∀ (d n : ℕ) (Λ κ : ℝ), RBM.EKSumDecayNAL d n Λ κ
