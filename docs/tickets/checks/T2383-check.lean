/-
Release check for T2383 (dispatcher V2, Sat Oct 10 12:00 UTC 2026; DECISIONS §195).  BA-T T5s1: route G in place on
`Induction/LoopGenN.lean`, `Induction/HierarchyN.lean` (the tripwire block; supervisor 1155 C6).
G1: the band statements below must stay unchanged; the auditor adds `example : <statement> := <name>` for each.
No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2383-check.lean
-/
import RBM3D.Induction.LoopGenN
import RBM3D.Induction.HierarchyN

#check @RBM.Ind.loopGenN
#check @RBM.Ind.stLoopGenNForm_holds
#check @RBM.Ind.hierarchyN_holds
#check @RBM.Ind.STLoopGenNForm
#check @RBM.Ind.HierarchyN
