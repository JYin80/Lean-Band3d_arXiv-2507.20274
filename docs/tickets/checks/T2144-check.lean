/-
Release check for T2144 (dispatcher V1, Sun Oct  4 17:02 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-18: port of CltResolvent + CltPath with parametrised scales; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2144-check.lean`.
-/
import RBM3D

#check @RBM.Evol.cltSwap
#check @RBM.Evol.cltHyb
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.coordinateMatrix
#check @RBM.Gauss.Xmat_update
#check @RBM.Gauss.Hflow
#check @RBM.Gauss.Gres
#check @RBM.zt
#check @RBM.Gauss.zdistInf
#check @RBM.SB
#check @RBM.ellT
#check @RBM.Gauss.Sizes.STCltIsoConcl
#check @RBM.Gauss.Sizes.STcltB
#check @RBM.Gauss.Step5Inst.szCL
