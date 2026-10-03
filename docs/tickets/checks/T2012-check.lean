/-
Release check for T2012 (dispatcher V1, Sat Oct  3 00:50 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
The pinned text is the compiled probe `5d2a4a8:RBM3D/Probe/T2002Vocab.lean` section 7 (lines 795–935,
without `LocalLawPT`, lines 882–889); this file checks that every merged declaration those lines use
(including MD-1, T2006 merged 0a873f1) exists on `main`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2012-check.lean`.
-/
import RBM3D

#check @RBM.StochDom
#check @RBM.HighProb
#check @RBM.UnifDetDom
#check @RBM.NormStochDom
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.W_pos
#check @RBM.Gauss.Idx
