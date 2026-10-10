/-
Release check for T2387 (dispatcher V2, Sat Oct 10 12:39 UTC 2026; DECISIONS §198).  BA-DL: design of stage L (the BA graph layer),
report only (supervisor 1155 R1).  Merged names the design starts from.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2387-check.lean
-/
import RBM3D.Graph.BAExpandWOrd
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWExpCertBS1
import RBM3D.Graph.LWLvl1
import RBM3D.BA.KKernel
import RBM3D.Chain.Carrier
import RBM3D.Induction.Step2Defs

#check @RBM.Graph.BAlanlw
#check @RBM.Graph.BAlweight
#check @RBM.Gauss.Sizes.LWtermExp
#check @RBM.Gauss.Sizes.LWAssm
#check @RBM.Gauss.Sizes.LWcut
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.Sizes.LWAvgLaw
#check @RBM.Gauss.Sizes.STLWB
#check @RBM.Gauss.Sizes.STLWT
#check @RBM.Gauss.Sizes.STEMn2Exp
#check @RBM.Graph.lvl1Cutoff
#check @RBM.Graph.LWCert.cert_all'
#check @RBM.Graph.LWCert.belowOf'
#check @RBM.BA.BAK_adj_sum_ge
#check @RBM.BA.FlowFM
