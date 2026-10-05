/-
Release check for T2109 (dispatcher V1, Sun Oct  4 03:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-10: third estimate of `lem: EMn2_N`, part 1 (pin `STEMn2Exp`); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2109-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STEMn2Exp
#check @RBM.Gauss.Sizes.STEMn2Poly
#check @RBM.Gauss.Sizes.stEMn2Poly_holds
#check @RBM.Gauss.Sizes.emn2Poly_contractPt_partner
#check @RBM.Gauss.Sizes.emn2Poly_norm_loop3_le
#check @RBM.Gauss.Sizes.stContractPt_holds
#check @RBM.Gauss.Sizes.STJhat
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.STLWassmExp
#check @RBM.Gauss.Sizes.STEEk
