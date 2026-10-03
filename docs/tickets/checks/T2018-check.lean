/-
Release check for T2018 (dispatcher V1, Sat Oct  3 02:19 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
The pinned text is the compiled probe `5d2a4a8:RBM3D/Probe/T2002Vocab.lean` section 8 (lines 937–1035);
this file checks that every merged declaration those lines use exists on `main`
(MD-1 = T2006 0a873f1, MD-2 = T2012 9e2b00f, MD-3 = T2013 868b3b4).
Run from the main worktree: `lake env lean docs/tickets/checks/T2018-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqXmat_isHermitian
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.one_le_size
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.StochDomAt
#check @RBM.badSetAt
#check @RBM.Path.PerTimeDomAt
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Idx
