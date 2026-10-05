/-
Release check for T2155 (dispatcher V1, Sun Oct  4 18:49 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-22a: translation and reflection invariance of `𝔼𝓛^{(2)}`, the pin `STExpInv`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2155-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STExpInv
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.slice
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.PF
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Xentry
#check @RBM.Gauss.idxKey
#check @RBM.Gauss.gvarF
#check @RBM.SB
#check @RBM.SB_apply
#check @RBM.sbKernel_neg
#check @RBM.Theta
