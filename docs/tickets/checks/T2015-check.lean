/-
Release check for T2015 (dispatcher V1, Sat Oct  3 01:19 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
ST-D1 is report-only (design of Step 1); this file checks that the merged declarations its pins build on
exist on `main` (MD-1 = T2006 merged 0a873f1; KL1 = T2008 merged 710acd2; PT-A = T2007 merged b20c658).
Run from the main worktree: `lake env lean docs/tickets/checks/T2015-check.lean`.
-/
import RBM3D

#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.zt
#check @RBM.mSigma
#check @RBM.msc
#check @RBM.StochDom
#check @RBM.HighProb
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.W_rpow_le
#check @RBM.Gauss.Sizes.size_rpow_le_W_rpow
#check @RBM.Gauss.Eblk
#check @RBM.Gauss.etaT
#check @RBM.Loop.KLK
#check @RBM.Loop.KLK_two
#check @RBM.Prop5to8
