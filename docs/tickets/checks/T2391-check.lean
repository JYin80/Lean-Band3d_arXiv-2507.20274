/-
Release check for T2391 (dispatcher V2, Sat Oct 10 21:19 UTC 2026; DECISIONS §205).  BA-K08b: the absolute weighted clause of
the BA molecule weight and the K-b predicate `SigSumZeroAbs … (BASig …)` (new `BA/KSumZeroB.lean`).  Merged names only.
No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2391-check.lean
-/
import RBM3D.BA.KSumZeroA
import RBM3D.BA.KPure
import RBM3D.BA.KMolecule
import RBM3D.Loop.KLIndStepB

#check @RBM.BA.BASig
#check @RBM.BA.baSig_transl
#check @RBM.BA.baSig_decay
#check @RBM.BA.baSig_signed_sum
#check @RBM.BA.baSigmaPi_slice
#check @RBM.BA.baSigmaPi_total_le
#check @RBM.BA.baSigmaTree_bound
#check @RBM.BA.baSlot_path_le
#check @RBM.BA.BAnextSlot_orbit
#check @RBM.BA.BAK_off_le
#check @RBM.BA.baProp5s_of_real
#check @RBM.Loop.SigSumZeroAbs
#check @RBM.Loop.sigSumZeroAbs_band
#check @RBM.Loop.KLsumZero_weighted
