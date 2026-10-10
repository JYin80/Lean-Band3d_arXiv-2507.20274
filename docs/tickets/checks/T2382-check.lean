/-
Release check for T2382 (dispatcher V2, Sat Oct 10 12:00 UTC 2026; DECISIONS §195).  BA-T row 0: move the carrier `FlowFM` and the generic
estimate-level predicates from `BA/FlowPins.lean` to the new `Chain/Carrier.lean` (supervisor 1155 TUV Q2; T2379 L1).
Part 1: the names that move (they keep their full names in `RBM.BA`).  Part 2 (G1): statements that must stay unchanged.
No proofs beyond `example … := <name>`; no sorry.  Run: lake env lean docs/tickets/checks/T2382-check.lean
-/
import RBM3D.BA.FlowPins

open RBM RBM.BA

/-! ## Part 1: names that move -/
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.STLKgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLocalMaxgL
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STInitialGT2gL

/-! ## Part 2: names that stay in `BA/FlowPins.lean` (G1: the auditor adds `example : <statement> := <name>` for each) -/
#check @RBM.BA.bandFM
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.STMainIndG
#check @RBM.BA.STMainInd_iff
#check @RBM.BA.bandFM_STLK
#check @RBM.BA.bandFM_STKbound
