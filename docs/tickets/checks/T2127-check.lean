/-
Release check for T2127 (dispatcher V1, Sun Oct  4 10:18 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
KL14b: deletes the old pins, makes the K-loop privates public, updates the registry; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2127-check.lean`.
-/
import RBM3D

#check @RBM.ThetaDiffOne
#check @RBM.ThetaDiffTwo
#check @RBM.PropTH
#check @RBM.ThetaDecay
#check @RBM.ThetaZeroMode
#check @RBM.Loop.KTreeRep
#check @RBM.Loop.TwoLoopBounded
#check @RBM.Loop.KLoopBound
#check @RBM.Loop.KLoopBound_KLK
#check @RBM.Loop.KLretire_twoLoopBounded
#check @RBM.Loop.KLretire_kTwoFormula
#check @RBM.Loop.KLretire_kThree
#check @RBM.Gauss.Sizes.STNewKLKAt
#check @RBM.Gauss.Sizes.stNewKLK_holds
#check @RBM.Gauss.Sizes.ST_good_engine
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKward_of_flow
#check @RBM.Green.gijOmegaSeq
