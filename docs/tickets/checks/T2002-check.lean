/-
Release check for T2002 (dispatcher V1, Fri Oct  2 17:26 UTC 2026; CLAUDE.md §4 step 0, DECISIONS §3–§7).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2002-check.lean`.
-/
import RBM3D

-- the RBM3D model vocabulary on `main` (item 1 (i)); keep / port / bridge is decided per object
#check @RBM.Zd
#check @RBM.SB
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.svar
#check @RBM.Gauss.Coord
#check @RBM.Gauss.Omega
#check @RBM.Gauss.gvar
#check @RBM.Gauss.P
#check @RBM.Gauss.Hmat
#check @RBM.Gauss.MomentDom
#check @RBM.StochDom
#check @RBM.NormStochDom
#check @RBM.HighProb
#check @RBM.HighProbIn
#check @RBM.badSet
#check @RBM.mE
#check @RBM.mSigma
#check @RBM.msc
#check @RBM.zt
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.Gauss.Eblk
#check @RBM.Gauss.etaT
#check @RBM.Gauss.Gsig
#check @RBM.Gauss.gloop
#check @RBM.Gauss.loopMax
