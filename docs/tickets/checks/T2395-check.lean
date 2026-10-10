/-
Release check for T2395 (dispatcher V2, Sat Oct 10 21:57 UTC 2026; DECISIONS §208).  BA-L3a3 design gate: G1 and the S test
(supervisor 2149 L1, L4 (a)), report only.  Merged names the design starts from.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2395-check.lean
-/
import RBM3D.Graph.BAExpandWOrd
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LWSymm
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.LocalRegular

#check @RBM.Graph.BAGraph
#check @RBM.Graph.BALData
#check @RBM.Graph.BAlanlw
#check @RBM.Graph.BAlweight
#check @RBM.Graph.baLanlw_holds
#check @RBM.Graph.lanlw_val
#check @RBM.Graph.lvl1Cutoff
#check @RBM.Graph.baLweight_holds
#check @RBM.Graph.lvl1_lemma
#check @RBM.Graph.Lvl1Ident
#check @RBM.Graph.lvl1_step_good
#check @RBM.Graph.lwSymmTwistG
