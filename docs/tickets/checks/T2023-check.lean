/-
Release check for T2023 (dispatcher V1, Sat Oct  3 04:09 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §13, §14).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
PT-F1 proves the merged pins `RBM.Prop5Decay` and `RBM.Prop8ZeroMode` (T2007, `RBM3D/Propagator/Pins.lean`);
this file checks that the pins and every merged route lemma exist on `main`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2023-check.lean`.
-/
import RBM3D

#check @RBM.Prop5Decay
#check @RBM.Prop8ZeroMode
#check @RBM.prop5Short_holds
#check @RBM.PropSpin
#check @RBM.Theta
#check @RBM.Theta0
#check @RBM.Theta0_apply_eq
#check @RBM.norm_Theta_apply_le
#check @RBM.Theta_real_nonneg
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.Heat.Theta_eq_laplace_prod
#check @RBM.Heat.kProd
#check @RBM.Heat.kProd_le
#check @RBM.Heat.kProd_gap
#check @RBM.Heat.lgGam
#check @RBM.Heat.lgEps
#check @RBM.Heat.lg_bulk
#check @RBM.Heat.lg_zero
#check @RBM.Heat.lg_tail
#check @RBM.Heat.lg_convA
#check @RBM.Heat.lg_convB
#check @RBM.Heat.lg_convC
