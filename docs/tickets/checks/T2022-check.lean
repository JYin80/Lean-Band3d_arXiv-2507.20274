/-
Release check for T2022 (dispatcher V1, Sat Oct  3 04:07 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §18).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
The pinned text is the compiled probe `c961e62:RBM3D/Probe/T2016Pins.lean` lines 44–198 (vocabulary, pins,
bridges); this file checks that every merged declaration those lines use exists on `main`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2022-check.lean`.
-/
import RBM3D

#check @RBM.PropSpin
#check @RBM.UN
#check @RBM.norm_UN_le
#check @RBM.zeroModeSet
#check @RBM.propT
#check @RBM.tailT
#check @RBM.sfT
#check @RBM.PsiT
#check @RBM.key_T_reduce_absorbed
#check @RBM.ellT
#check @RBM.zdistD
#check @RBM.Prop5Decay
#check @RBM.Prop5Short
#check @RBM.Prop6Diff1
#check @RBM.Prop8ZeroMode
