/-
Release check for T2056 (dispatcher V1, Sat Oct  3 13:08 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15, §23).
KL7c ports RBM2D `Loop/SumZeroWard.lean` onto the merged KL layer; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2056-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLK_sumAll_le
#check @RBM.Loop.SigmaPi_alt_sumZero_le_of_Qlayer_one
#check @RBM.Loop.SumZero_sum_slice_alt
#check @RBM.Loop.Alayer
#check @RBM.Loop.Qlayer
#check @RBM.Loop.KLsigAlt
#check @RBM.Loop.KLSigmaPi
#check @RBM.Loop.KLsum_cut
#check @RBM.Loop.KLK_ward
#check @RBM.Loop.gapK
#check @RBM.Loop.TSP
#check @RBM.mSigma
#check @RBM.Gauss.etaT
