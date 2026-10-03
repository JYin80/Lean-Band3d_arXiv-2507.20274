/-
Release check for T2028 (dispatcher V1, Sat Oct  3 05:12 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-07 promotes the T2015 probe (`752e027:RBM3D/Probe/T2015Pins.lean`, sections 1, 1b, 2, lines 161–501) and ports
RBM2D `Green/Pins.lean`; this file checks that the merged declarations the pins use (T2015 portmap P.8.5) exist.
Run from the main worktree: `lake env lean docs/tickets/checks/T2028-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Idx
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.Whp
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.etaT
#check @RBM.Loop.KLK
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.mE
#check @RBM.lemE
#check @RBM.lemT
