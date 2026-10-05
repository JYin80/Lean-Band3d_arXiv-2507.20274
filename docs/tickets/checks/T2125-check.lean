/-
Release check for T2125 (dispatcher V1, Sun Oct  4 08:20 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
KL14a: composes the KL bounds with the PT proofs; `STKbound`, `STKward`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2125-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLPT
#check @RBM.prop5to8_holds
#check @RBM.Prop5to8
#check @RBM.Loop.KLShort_holds
#check @RBM.Loop.KLboundPin_holds
#check @RBM.Loop.KLwardIneqPin_holds
#check @RBM.Loop.KLBoundAt
#check @RBM.Loop.KLoopBound
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STKI
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.mE_im_pos
