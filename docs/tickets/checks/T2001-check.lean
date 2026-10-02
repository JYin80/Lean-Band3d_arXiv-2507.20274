/-
Release check for T2001 (dispatcher V1, Fri Oct  2 17:26 UTC 2026; CLAUDE.md §4 step 0, DECISIONS §3–§7).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2001-check.lean`.
-/
import RBM3D

-- deterministic vocabulary on `main` that the endpoint table and the pins refer to
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.SB
#check @RBM.Theta
#check @RBM.Theta0
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.msc
#check @RBM.mE
#check @RBM.zt
#check @RBM.lemE
#check @RBM.lemT
-- probability notions and the Gaussian model at one size
#check @RBM.StochDom
#check @RBM.HighProb
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.svar
#check @RBM.Gauss.P
#check @RBM.Gauss.Hmat
#check @RBM.Gauss.Eblk
#check @RBM.Gauss.Gsig
#check @RBM.Gauss.gloop
-- the old-mode `Prop` hypotheses whose status item 4 classifies
#check @RBM.PropTH
#check @RBM.ThetaDecay
#check @RBM.Loop.IsKLoop
#check @RBM.Loop.KTreeRep
#check @RBM.Loop.KLoopBound
