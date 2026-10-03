/-
Release check for T2027 (dispatcher V1, Sat Oct  3 05:11 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §13, §14, §16).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
PT-G proves the merged pins `RBM.Prop6Diff1`, `RBM.Prop7Diff2` and the bundle `RBM.Prop5to8`, and the old
interface forms `ThetaDecay`, `ThetaDecayShort`, `ThetaZeroMode` through the merged bridges; this file checks
that every declaration the route uses exists on `main`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2027-check.lean`.
-/
import RBM3D

#check @RBM.Prop6Diff1
#check @RBM.Prop7Diff2
#check @RBM.Prop5to8
#check @RBM.prop5Decay_holds
#check @RBM.prop8ZeroMode_holds
#check @RBM.prop5Short_holds
#check @RBM.propUnit1_holds
#check @RBM.propUnit2_holds
#check @RBM.PropUnit1
#check @RBM.PropUnit2
#check @RBM.exists_step
#check @RBM.zdistD_add_le
#check @RBM.zdistD_neg
#check @RBM.ThetaDecay
#check @RBM.ThetaDecayShort
#check @RBM.ThetaZeroMode
#check @RBM.Prop5Decay.thetaDecay
#check @RBM.Prop5Short.thetaDecayShort
#check @RBM.Prop8ZeroMode.thetaZeroMode
