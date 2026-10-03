/-
Release check for T2043 (dispatcher V1, Sat Oct  3 07:57 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15).
KL7a ports RBM2D `Loop/SumZero.lean` onto the merged KL layer; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2043-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLK
#check @RBM.Loop.KLKpi
#check @RBM.Loop.KLSigmaPi
#check @RBM.Loop.TSP
#check @RBM.Loop.thetaEdge
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.KLK_ward
#check @RBM.Loop.KLK_rotate
#check @RBM.Loop.KLK_translate
#check @RBM.Loop.KLK_isKLoop
#check @RBM.Gauss.etaT
#check @RBM.mSigma
