/-
Release check for T2420 (dispatcher V2, Sun Oct 11 10:01 UTC 2026; DECISIONS §232).  BA-L L3c1 `BAAtom`: atoms, the
auxiliary graph, (G_by_auxG_BA) (supervisor 0951 Q4; design gate G3, G4).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2420-check.lean
-/
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.BASizeClaim2
import RBM3D.BA.GreenSchur

#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAGraph.atom
#check @RBM.Graph.BAGraph.exists_forest
#check @RBM.Graph.BAGraph.counters_le
#check @RBM.BA.BAMfine_eq
#check @RBM.Graph.LWGtoAG
#check @RBM.Graph.lwGtoAG_holds
#check @RBM.Graph.baClaimSize
#check @RBM.Graph.baClaimSizeG
#check @RBM.Graph.baClaimSize_E
#check @RBM.Graph.baSp_eq
#check @RBM.Graph.baSpDecay
#check @RBM.Graph.baKBound_E
#check @RBM.Graph.BASizeClaim_forest_sum_le
