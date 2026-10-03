/-
Release check for T2048 (dispatcher V1, Sat Oct  3 09:12 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15, §23).
KL7b ports RBM2D `Loop/SumAll.lean` onto the merged KL layer; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2048-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLK
#check @RBM.Loop.KLK_ward
#check @RBM.Loop.KLK_rotate
#check @RBM.Loop.KLK_translate
#check @RBM.Loop.KLKpi
#check @RBM.Loop.gapK
#check @RBM.Loop.gapK_le_norm
#check @RBM.Loop.Alayer
#check @RBM.Loop.Qlayer
#check @RBM.Loop.sum_Kpi_closed
#check @RBM.Loop.TSP
#check @RBM.Gauss.etaT
#check @RBM.mSigma
