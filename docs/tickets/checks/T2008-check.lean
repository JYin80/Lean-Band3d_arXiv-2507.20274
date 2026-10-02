/-
Release check for T2008 (dispatcher V1, Fri Oct  2 23:46 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
The pinned text is the compiled probe `64b58eb:RBM3D/Probe/T2004Pins.lean` lines 41–501; this file
checks that every merged declaration those lines use, and the three to be generalised, exist on `main`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2008-check.lean`.
-/
import RBM3D

#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.Theta
#check @RBM.Theta0
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.mE
#check @RBM.mE_im_pos
#check @RBM.norm_mE
#check @RBM.mSigma
#check @RBM.norm_Theta_apply_le
#check @RBM.sum_Theta_row_of_three_le
#check @RBM.Gauss.etaT
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.length
#check @RBM.Loop.TSP
#check @RBM.Loop.TSP_three
#check @RBM.Loop.diagonals
#check @RBM.Loop.thetaEdge
#check @RBM.Loop.kTwo
#check @RBM.Loop.kThree
#check @RBM.Loop.kTwoFormula_of_isKLoop
-- the merged definitions item 3 generalises (unchanged; primed/kernel-generic successors are added)
#check @RBM.Loop.treeEqRhs
#check @RBM.Loop.MLoop
#check @RBM.Loop.IsKLoop
