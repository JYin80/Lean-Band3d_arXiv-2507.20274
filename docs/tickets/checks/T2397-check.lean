/-
Release check for T2397 (dispatcher V2, Sat Oct 10 22:26 UTC 2026; DECISIONS §210).  BA-L3b3 design gate: G2, property (6) of
`lem:localregular` at BA (supervisor 2149 L4 (b)), report only.  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2397-check.lean
-/
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.BAVocab

#check @RBM.Graph.lw_localregular
#check @RBM.Graph.BAGraph
#check @RBM.Graph.BALData
