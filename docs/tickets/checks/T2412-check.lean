/-
Release check for T2412 (dispatcher V2, Sun Oct 11 07:44 UTC 2026; DECISIONS §224).  BA-L3c2: claim:size at BA (new `Graph/BASizeClaim*.lean`).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2412-check.lean
-/
import RBM3D.Graph.LWSizeClaim
import RBM3D.Graph.BAExpandW
import RBM3D.BA.GreenSchur
import RBM3D.BA.Prop5Short

#check @RBM.Graph.lwClaimSize
#check @RBM.Graph.lwSpOf_decay
#check @RBM.Graph.lwTail_log32
#check @RBM.Graph.baSplitSolid
#check @RBM.Graph.BAGraph.val_eq_partition
#check @RBM.Graph.BAGraph.scalingOrder
#check @RBM.Graph.baW_mul
#check @RBM.Graph.baW_isUnit
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAMfine_decay
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.baProp5s_holds
