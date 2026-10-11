/-
Release check for T2409 (dispatcher V2, Sun Oct 11 04:34 UTC 2026; DECISIONS §222).  BA-L2c2a: the GG expansion (B.20) with the D402 coefficient
(new `Graph/BAGGExp.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2409-check.lean
-/
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.LWGGExp

#check @RBM.Graph.baLanlw_holds
#check @RBM.Graph.baLweight_holds
#check @RBM.Graph.BAlweight
#check @RBM.Graph.BAlwData
#check @RBM.Graph.baW_mul
#check @RBM.Graph.baW_isUnit
#check @RBM.Graph.BAlwW
#check @RBM.Graph.BAlwGc
#check @RBM.Graph.BAlwf
#check @RBM.Graph.BAlwdf
#check @RBM.Graph.oe2x_integral
