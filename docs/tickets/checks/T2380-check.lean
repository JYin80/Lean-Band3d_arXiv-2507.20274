/-
Release check for T2380 (dispatcher V2, Sat Oct 10 10:25 UTC 2026; DECISIONS §192).  BA-K07: `BA/KPure.lean`, pure BA loops and
`(eq:molecule-decay)` for `BASig`.  No new pin: the 1a fixes the statements (design gate).  Merged names only.
No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2380-check.lean
-/
import RBM3D.BA.KMolecule
import RBM3D.BA.CombesThomas
import RBM3D.BA.Prop5Short
import RBM3D.BA.KKernel
import RBM3D.Loop.PureLoop
import RBM3D.Loop.KLIndStepA

#check @RBM.BA.BASig
#check @RBM.BA.BASigmaTree
#check @RBM.BA.BASigmaPi
#check @RBM.BA.baSig_transl
#check @RBM.BA.baSigmaPi_cut
#check @RBM.BA.baPropM_holds
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.BAK_off_le
#check @RBM.Loop.SigDecayAbs
#check @RBM.Loop.SigSumZeroAbs
