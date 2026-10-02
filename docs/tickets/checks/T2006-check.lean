/-
Release check for T2006 (dispatcher V1, Fri Oct  2 23:15 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
The pinned text is the compiled probe `5d2a4a8:RBM3D/Probe/T2002Vocab.lean` lines 39–446; this file
checks that every merged declaration those lines use still exists on `main`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2006-check.lean`.
-/
import RBM3D

#check @RBM.Zd
#check @RBM.zdist
#check @RBM.zdistD
#check @RBM.SB
#check @RBM.SBR
#check @RBM.sbKernelR
#check @RBM.sbKernelR_neg
#check @RBM.sbKernelR_nonneg
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.svar
#check @RBM.Gauss.gvar
#check @RBM.Gauss.Coord
#check @RBM.Gauss.P
#check @RBM.StochDom
#check @RBM.msc_eq_integral
