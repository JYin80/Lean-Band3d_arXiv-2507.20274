/-
Release check for T2394 (dispatcher V2, Sat Oct 10 21:56 UTC 2026; DECISIONS §208).  BA-L0: the generic LW pins over the
carrier (new `Chain/LWGen.lean`, `BA/LWPinsBA.lean`), rebuilt on the merged `Chain/Step2Gen` (supervisor 2149 L2).
Merged names only (the six `Step2Gen` names L0 must not redefine, and the band pins it bridges to).  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2394-check.lean
-/
import RBM3D.Chain.Step2Gen
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWTermHolds
import RBM3D.Graph.LWExpTerm6
import RBM3D.BA.FlowPins

#check @RBM.BA.STLWassmExpgL
#check @RBM.BA.STEGtg
#check @RBM.BA.STLWassmgL
#check @RBM.BA.STLWBgL
#check @RBM.BA.STLWTgL
#check @RBM.BA.STEMn2ExpgL
#check @RBM.BA.STmsigg
#check @RBM.BA.bandFM
#check @RBM.BA.FlowFM
#check @RBM.Gauss.Sizes.LWterm
#check @RBM.Gauss.Sizes.LWtermExp
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.Sizes.LWAssm
#check @RBM.Gauss.Sizes.LWcut
#check @RBM.Gauss.Sizes.LWAvgLaw
#check @RBM.Gauss.Sizes.lwterm_holds
#check @RBM.Gauss.Sizes.lwtermExp_holds
#check @RBM.Gauss.Sizes.lwTermEXP_holds
