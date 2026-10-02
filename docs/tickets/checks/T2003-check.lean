/-
Release check for T2003 (dispatcher V1, Fri Oct  2 17:26 UTC 2026; CLAUDE.md §4 step 0, DECISIONS §3–§7).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2003-check.lean`.
-/
import RBM3D

-- definitions the pins are written with
#check @RBM.SB
#check @RBM.sbKernel
#check @RBM.SBR
#check @RBM.Theta
#check @RBM.Theta0
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.BparamR
-- properties 1-4 (merged theorems)
#check @RBM.Theta_transpose_of_three_le
#check @RBM.Theta_apply_add_right_of_three_le
#check @RBM.Theta_commute_of_three_le
#check @RBM.sum_norm_Theta_row_le
#check @RBM.norm_Theta_apply_le
#check @RBM.hasDerivAt_Theta_apply
-- the old-mode shapes of properties 5-8 (Props, constants after `g`, `m`) and the fixed-`L` results
#check @RBM.ThetaDecay
#check @RBM.ThetaDecayShort
#check @RBM.ThetaDiffOne
#check @RBM.ThetaDiffTwo
#check @RBM.ThetaZeroMode
#check @RBM.PropTH
#check @RBM.exists_norm_Theta0_le
#check @RBM.exists_norm_Theta_sub_le
#check @RBM.Test.thetaDecay_fixedL
#check @RBM.Test.propTH_fixedL
