/-
Release check for T2389 (dispatcher V2, Sat Oct 10 12:48 UTC 2026; DECISIONS §200).  BA-G2: the G segments of `Green/LDE`,
`Green/RowIndep`, `Green/IBPPoly` restated in place over a deterministic shift `D`; the BA large-deviation inputs `BALDEin`
in the new `BA/GreenLDE.lean`.  Part 1: the BA objects.  Part 2 (G1): band statements that must stay unchanged; the auditor adds
`example : <statement> := <name>` for each of the 28 names.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2389-check.lean
-/
import RBM3D.Green.LDE
import RBM3D.Green.RowIndep
import RBM3D.Green.IBPPoly
import RBM3D.Green.EntryCore
import RBM3D.BA.GreenSchur
import RBM3D.BA.FlowPins

/-! ## Part 1: BA objects -/
#check @RBM.BA.BAGt
#check @RBM.BA.BAFlow
#check @RBM.BA.green_diag_split
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Green.ldeRowLHS
#check @RBM.Green.stochDom_rowSum_general

/-! ## Part 2 (G1): names used outside the three files -/
#check @RBM.Green.measurable_green_apply
#check @RBM.Green.norm_green_apply_le_etaT
#check @RBM.Green.im_green_diag
#check @RBM.Green.green_diag_ne_zero
#check @RBM.Green.stochDom_ldeRow
#check @RBM.Green.stochDom_ldeCol
#check @RBM.Green.stochDom_normSq_Hflow_diag
#check @RBM.Green.minorCol
#check @RBM.Green.minorRowConj
#check @RBM.Green.hwConst
#check @RBM.Green.hwConst_pos
#check @RBM.Green.stochDom_ldeQuad
