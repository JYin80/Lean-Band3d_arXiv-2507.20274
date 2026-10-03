/-
Release check for T2059 (dispatcher V1, Sat Oct  3 13:52 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §21, §25).
S3-05 proves the merged pin `STQopNorm` (`lem_+Q`) and the decay clause on the merged `Step34Pins` / `QopAlgebra`
vocabulary; this file checks that the names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2059-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.stMollifierEx_holds
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_Qop
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_of_sumZero
#check @RBM.EKFastDecay
#check @RBM.ellT
#check @RBM.zdistD
