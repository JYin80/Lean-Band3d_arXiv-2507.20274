/-
Release check for T2449 (dispatcher V3, Mon Oct 12 11:23 UTC 2026; DECISIONS §262).  BA-DMN: design of stage M/N (the BA endpoints of
Thm 2.7, `MR:decol_BA`), report only.  Merged names the design starts from, plus two `Prop` shapes.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2449-check.lean
-/
import RBM3D.Main.BandTerminal
import RBM3D.BA.UNPins
import RBM3D.BA.TwistChain
import RBM3D.Induction.MainIndOut
import RBM3D.Universality.GUEPhase.RandomLayerB
import RBM3D.Universality.OUInterfaceK
import RBM3D.Universality.QUEFlow
import RBM3D.Universality.EMCTE2
import RBM3D.Universality.Uyw
import RBM3D.Universality.GreenCorr
import RBM3D.Universality.UnivMain
import RBM3D.BA.CouplingWindow
import RBM3D.BA.MReg
import RBM3D.BA.KTreeRep
import RBM3D.BA.Boundary
import RBM3D.BA.ImmLower

/-! ## The band endpoints and the band assembly (MA-01 … MA-06a, UN-52b): the twins of M1–M3, N2 -/
#check @RBM.Endpoints.decol
#check @RBM.Endpoints.locSC
#check @RBM.Endpoints.QUE
#check @RBM.Endpoints.QDiff
#check @RBM.Endpoints.BUniv
#check @RBM.Endpoints.band_terminal
#check @RBM.Endpoints.locSC_holds
#check @RBM.Endpoints.QDiff_holds
#check @RBM.Endpoints.QUE_holds
#check @RBM.Endpoints.decol_holds
#check @RBM.Endpoints.unBUniv_of_L32
#check @RBM.Endpoints.locSCFixed_of_ML
#check @RBM.Endpoints.QDiffFixed_of_ML
#check @RBM.Endpoints.netLoc
#check @RBM.Endpoints.netQD
#check @RBM.Endpoints.QUE_of_QDiff
#check @RBM.Endpoints.decol_of_locSC
#check @RBM.Endpoints.locSC_to_UNLocAvgBand
#check @RBM.Endpoints.QUE_to_UNQueBand
#check @RBM.Endpoints.explicit_of_stochDomAt
#check @RBM.Endpoints.prec_of_explicit
#check @RBM.Endpoints.det_of_prec
#check @RBM.Endpoints.bUniv_holds
#check @RBM.Endpoints.unOURow
#check @RBM.Endpoints.unClaimRowBA_holds

/-! ## The merged BA end pins, the BUniv assembly and its inputs (`BA/UNPins.lean`) -/
#check @RBM.BA.BAEnd_QUEL
#check @RBM.BA.BAEnd_BUnivL
#check @RBM.BA.BAqueConclL
#check @RBM.Univ.baBUniv_of_rows
#check @RBM.Univ.UNQueBA_of_BAEnd_QUEL
#check @RBM.Univ.un_claimAll_of_rowsBA
#check @RBM.Univ.UNKind.ba
#check @RBM.Univ.UNModelC.ba
#check @RBM.Univ.UNMLOutBA
#check @RBM.Univ.UNLocAvgBA
#check @RBM.Univ.UNQueBA
#check @RBM.Univ.UNOURowBA
#check @RBM.Univ.UNClaimRowBA
#check @RBM.Univ.UNDensBARow'
#check @RBM.Univ.unDensBARow'_holds
#check @RBM.Univ.UNTrLocalBARow
#check @RBM.Univ.UNTrLocalInitBARow'
#check @RBM.Univ.UNNormBARow
#check @RBM.Univ.lamHat
#check @RBM.Univ.admissible_lamHat
#check @RBM.Univ.UNL32
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.un_gueLocal_of_tail
#check @RBM.Univ.gueSchurTail

/-! ## The V interface (BA-V interface list (iii): V3 and BA-M1 take `BAMLOutTL`) -/
#check @RBM.BA.BAMLOutTL
#check @RBM.BA.BAMainIndTL
#check @RBM.BA.BAChainTL
#check @RBM.BA.baChainTL_holds
#check @RBM.BA.baTwistLoopBase_holds
#check @RBM.BA.STMainIndG
#check @RBM.BA.STHorizonG
#check @RBM.BA.STBaseG
#check @RBM.BA.STG0M
#check @RBM.Univ.unMLOutBA_of_pins

/-- The shape of V3 as a projection (MN2): `BAMLOutTL` drops its sixth conjunct to `UNMLOutBA`. -/
example (d : ℕ) : Prop := RBM.BA.BAMLOutTL d → RBM.Univ.UNMLOutBA d

/-! ## The BA flow, the bulk and the domain bridge -/
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowLam0
#check @RBM.BA.baFMz
#check @RBM.BA.BAt0
#check @RBM.BA.BAflowE
#check @RBM.BA.BAm
#check @RBM.BA.BArho
#check @RBM.BA.BAbulk
#check @RBM.BA.BAdom
#check @RBM.BA.BAWinBulk_of_dom_holds
#check @RBM.BA.baImmLower_holds
#check @RBM.BA.baMBoundary_holds
#check @RBM.BA.baMUniqReal_holds
#check @RBM.BA.baKsolve

/-! ## BA-C5 / E5: the UN-51 window conditions (`etaT`, `|fE| ≤ 2 - κ`) and the UN-side producers -/
#check @RBM.Gauss.etaT
#check @RBM.mE
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.Univ.GUEPhase.RandomLayerB_Flow
#check @RBM.Univ.GUEPhase.RandomLayerB_MLout
#check @RBM.Univ.GUEPhase.RandomLayerB_Prod
#check @RBM.Univ.GUEPhase.RandomLayerB_LL
#check @RBM.Univ.GUEPhase.RandomLayerB_Que
#check @RBM.Univ.GUEPhase.g1Rowk_of_inputs
#check @RBM.Univ.GUEPhase.g1Rowk_band
#check @RBM.Univ.GUEPhase.RandomLayer_lem28
#check @RBM.Univ.UNG1Rowk
#check @RBM.Univ.UNOUProfRowk
#check @RBM.Univ.UNOULLk
#check @RBM.Univ.UNOUEq747k
#check @RBM.Univ.ouRowk_of_pins
#check @RBM.Univ.g2bRowk

/-- The question of MN0 (a): T1 of `g1Rowk_of_inputs` at the block Anderson kind with the BA flow maps
(`fE z = BAflowE z m`, `fT z = BAt0 z m`, `m = m(z, λ_n)`), the readings of `BAflowEs`, `BAflowT0`. -/
example (d : ℕ) : Prop :=
  RBM.Univ.GUEPhase.RandomLayerB_Flow (RBM.Univ.UNKind.ba d)
    (fun sz n w => RBM.BA.BAflowE w (RBM.BA.BAm d (sz.L n) (sz.lam n) w))
    (fun sz n w => RBM.BA.BAt0 w (RBM.BA.BAm d (sz.L n) (sz.lam n) w))

/-! ## BA-N3: E1–E4 (owed, owner BA-N3), the transfer identities and the band producers -/
#check @RBM.Univ.UNEMCTE2RowBA
#check @RBM.Univ.UNJakUywRowBA
#check @RBM.Univ.UNEMCTE2k
#check @RBM.Univ.UNEMCTE2Rowk
#check @RBM.Univ.UNJakk
#check @RBM.Univ.UNUywk
#check @RBM.Univ.UNJakUywRowk
#check @RBM.Univ.UNCoreC''
#check @RBM.Univ.UNGreenCorrC
#check @RBM.Univ.UNGreenCorrAllC
#check @RBM.Univ.UNGreenCorrAllC.toAll
#check @RBM.Univ.ouMatC_ba_eq_band_add
#check @RBM.Univ.ouP_ba_eq_band
#check @RBM.Univ.unEMCTE2Rowk_band
#check @RBM.Univ.jakUywRow
#check @RBM.Univ.unCore'_holds
#check @RBM.Univ.greenCorrAll
#check @RBM.Univ.unClaimRowk
