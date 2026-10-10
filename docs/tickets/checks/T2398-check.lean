/-
Release check for T2398 (dispatcher V2, Sat Oct 10 22:26 UTC 2026; DECISIONS §210).  BA LW-14 design gate: G6 and lever C
(supervisor 2149 L3, L4 (c)), report only.  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2398-check.lean
-/
import RBM3D.Graph.LWExpTerm4
import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.LWExpCertBS1
import RBM3D.Graph.BAExpandWOrd

#check @RBM.Gauss.Sizes.LWExpI1K
#check @RBM.Gauss.Sizes.LWExpI23K
#check @RBM.Gauss.Sizes.LWExpI41K
#check @RBM.Gauss.Sizes.RCand
#check @RBM.Gauss.Sizes.LWG5Identity
#check @RBM.Gauss.Sizes.lwExpandIdentity_holds
#check @RBM.Graph.LWCert.cert_all'
#check @RBM.Graph.LWCert.belowOf'
#check @RBM.Graph.BAlweight
