/-
Release check for T2013 (dispatcher V1, Sat Oct  3 00:50 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
The pinned text is the compiled probe `5d2a4a8:RBM3D/Probe/T2002Vocab.lean` sections 5–6 (lines 448–791,
including the `LoopZero` sanity block); this file checks that every merged declaration those lines use
(including MD-1, T2006 merged 0a873f1) exists on `main`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2013-check.lean`.
-/
import RBM3D

#check @RBM.Adj
#check @RBM.zdistD_neg
#check @RBM.zt
#check @RBM.eq_inv_sqrt_mul_zt
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.lemT_pos
#check @RBM.mE_mul
#check @RBM.mSigma
#check @RBM.msc
#check @RBM.msc_mul
#check @RBM.isUnit_sub_smul_of_isHermitian
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.Omega
#check @RBM.Gauss.Hmat
#check @RBM.Gauss.Eblk
#check @RBM.Gauss.etaT
#check @RBM.Gauss.Gsig
#check @RBM.Gauss.gloop
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.cutGlueL
#check @RBM.Loop.LoopIdx.cutGlueR
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.splitEquiv
#check @RBM.Gauss.Idx
