Prover model: claude-sonnet-5-5

# T2522 dead-code report (core closure of the RBM3D library; tool `docs/claude-team/tools/DeadDecls.lean`, branch `t/T2522`)

Command (main worktree `/Users/junyin/Lean_proof/RBM3D`, at `main` 316653b9, tool file from branch `t/T2522` commit 0aea2069): 
`lake env lean /Users/junyin/Lean_proof/RBM3D-wt/T2522/docs/claude-team/tools/DeadDecls.lean`; exit 0, started Fri Oct 16 20:29:27 UTC 2026, ended Fri Oct 16 20:30:06 UTC 2026.
The sections (a)-(g) below are the tool output, verbatim, in report-format order (`(a)` also carries the group roots and the sanity checks); the summary and group tables follow at the end.

Roots added by hand under the `open`s of `RBM3D/Main/FinalShape.lean` (the five core `example`s are not constants): `UNL32`, `Inst.inst_decol/_locSC/_QUE/_BUniv/_QDiff`, the private `FinalShape_hg`, `BAInst.S0`, `S0_adm`, `S0_bulk`, `UNPinsInst.clsκ`, `clsκ_pos`, `fp`, `UNInst.bump`, `bump_testFun` (lines tagged "added by hand" in (a)).

```text
DeadDecls report: modules 6783, in scope 673, constants in scope 56575, counted declarations 32992

## (a) roots actually used
- RBM.Endpoints.final_shape  (core: ticket root)
- RBM.Endpoints.Thm27  (core: ticket root)
- RBM.Endpoints.Thm27_of_L32  (core: ticket root)
- RBM.Endpoints.band_terminal  (core: ticket root)
- RBM.Univ.UNL32  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_decol  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_locSC  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_QUE  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_BUniv  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_QDiff  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- private RBM.Endpoints.FinalShape_hg  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Univ.BAInst.S0  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Univ.BAInst.S0_adm  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.BA.UNPinsInst.clsκ  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.BA.UNPinsInst.clsκ_pos  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.BA.UNPinsInst.fp  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Univ.BAInst.S0_bulk  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Univ.UNInst.bump  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Univ.UNInst.bump_testFun  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Audit.Fixture.FakePremise  (core: namespace RBM.Audit)
- RBM.Audit.Fixture.uses_fake  (core: namespace RBM.Audit)
- RBM.Audit.allowedAxioms  (core: namespace RBM.Audit)
- RBM.Audit.borrowedProps  (core: namespace RBM.Audit)
- RBM.Audit.certificates  (core: namespace RBM.Audit)
- RBM.Audit.interfaceAxioms  (core: namespace RBM.Audit)
- RBM.Audit.interfaceProps  (core: namespace RBM.Audit)
- RBM.Audit.isHandwritten  (core: namespace RBM.Audit)
- RBM.Audit.isHandwritten._sparseCasesOn_1  (core: namespace RBM.Audit)
- RBM.Audit.isHandwritten.match_1  (core: namespace RBM.Audit)
- RBM.Audit.owedProps  (core: namespace RBM.Audit)
- RBM.Audit.refutedProps  (core: namespace RBM.Audit)
- RBM.Audit.scanPremises  (core: namespace RBM.Audit)
- RBM.Audit.scanPremises._sparseCasesOn_1  (core: namespace RBM.Audit)
- RBM.Audit.scanPremises._sparseCasesOn_6  (core: namespace RBM.Audit)
- RBM.Audit.scanPremises.match_1  (core: namespace RBM.Audit)
- RBM.Audit.scanPremises.match_4  (core: namespace RBM.Audit)
- RBM.Audit.scanPremises.match_6  (core: namespace RBM.Audit)
- RBM.Audit.scanPremises.match_9  (core: namespace RBM.Audit)
- RBM.Audit.structuralProps  (core: namespace RBM.Audit)
- RBM.Audit.supersededProps  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_audit_detects__1»  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1»  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1»._sparseCasesOn_1  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1»._sparseCasesOn_11  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1»._sparseCasesOn_6  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1».match_1  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1».match_11  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1».match_14  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1».match_16  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1».match_4  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1».match_6  (core: namespace RBM.Audit)
- RBM.Audit.«_aux_RBM3D_Test_Axioms___elabRules_RBM_Audit_command#assert_rbm_axioms_1».match_9  (core: namespace RBM.Audit)
- RBM.Audit.«command#assert_rbm_audit_detects_»  (core: namespace RBM.Audit)
- RBM.Audit.«command#assert_rbm_axioms»  (core: namespace RBM.Audit)
- (35 constants in RBM.Audit and its sub-namespaces; 34795 in-scope constants reached in the core)
- G1 (constants of the `example`s in Main/BandTerminal.lean §Instances; optional, not part of the core closure): 20 roots
  - G1: RBM.Endpoints.Inst.inst_decol
  - G1: RBM.Endpoints.Inst.inst_locSC
  - G1: RBM.Endpoints.Inst.inst_QUE
  - G1: RBM.Endpoints.Inst.inst_BUniv
  - G1: RBM.Endpoints.Inst.inst_QDiff
  - G1: RBM.Endpoints.Inst.inst_bridge_loc
  - G1: RBM.Endpoints.Inst.inst_bridge_que
  - G1: RBM.Endpoints.band_terminal
  - G1: RBM.Endpoints.unBUniv_of_L32
  - G1: RBM.Endpoints.decol_holds
  - G1: RBM.Endpoints.locSC_holds
  - G1: RBM.Endpoints.QUE_holds
  - G1: RBM.Endpoints.QDiff_holds
  - G1: RBM.Endpoints.unOUClaims_holds
  - G1: RBM.Endpoints.unOUQUE_holds
  - G1: RBM.Univ.UNOUQUE
  - G1: RBM.Univ.UNOUDiag
  - G1: RBM.Gauss.SizesInst.sz0
  - G1: RBM.Gauss.SizesInst.sz0_admissible
  - G1: RBM.Univ.UNL32
- G2 (constants of the `example`s in BA/MAPins.lean; optional, not part of the core closure): 31 roots
  - G2: RBM.Univ.BAInst.S0
  - G2: RBM.Univ.BAInst.S0_adm
  - G2: RBM.BA.UNPinsInst.clsκ
  - G2: RBM.BA.UNPinsInst.clsκ_pos
  - G2: RBM.BA.UNPinsInst.fp
  - G2: RBM.Univ.BAInst.S0_bulk
  - G2: RBM.Univ.UNInst.bump
  - G2: RBM.Univ.UNInst.bump_testFun
  - G2: private RBM.BA.MAPins_hg
  - G2: RBM.BA.BAThm27L
  - G2: RBM.BA.BAlocSCFixed
  - G2: RBM.BA.BAQDiffFixed
  - G2: RBM.BA.BAMANetLoc
  - G2: RBM.BA.BAMADecol
  - G2: RBM.BA.BAMANetQD
  - G2: RBM.BA.BAMAQUE
  - G2: RBM.BA.BAMAFixed
  - G2: RBM.Univ.UNMLOutBA
  - G2: RBM.Univ.BAInst.inst_locAvg_domain
  - G2: RBM.BA.BAendDom
  - G2: RBM.BA.BAbulk
  - G2: RBM.BA.BAbulk_window
  - G2: RBM.BA.UNLocAvgBAAt
  - G2: RBM.BA.UNTrLocalBAAt
  - G2: RBM.BA.UNTrLocalInitBAAt'
  - G2: RBM.Univ.UNLocAvgBA
  - G2: RBM.Univ.UNTrLocalBARow
  - G2: RBM.Univ.UNTrLocalInitBARow'
  - G2: RBM.BA.UNLocAvgBA_iff_at
  - G2: RBM.BA.UNTrLocalBARow_iff_at
  - G2: RBM.BA.UNTrLocalInitBARow'_iff_at
- G3 (the general-`d` BA forms; optional, not part of the core closure): 3 roots
  - G3: RBM.BA.baThm27L_any
  - G3: RBM.BA.baThm27L_of_ML
  - G3: RBM.BA.baEnd_BUnivL_of_ML
- G4 (`bUniv_holds` and the constants of the `example`s in Main/BUnivHolds.lean; optional, not part of the core closure): 16 roots
  - G4: RBM.Endpoints.bUniv_holds
  - G4: RBM.Univ.kPoint
  - G4: RBM.Gauss.Sizes.seqXmat_isHermitian
  - G4: RBM.Gauss.Xmat_isHermitian
  - G4: RBM.Gauss.Sizes.seqP
  - G4: RBM.Univ.gueP
  - G4: RBM.Univ.UNInst.bump
  - G4: RBM.Univ.UNInst.bump_testFun
  - G4: RBM.Gauss.SizesInst.sz0
  - G4: RBM.Gauss.SizesInst.sz0_admissible
  - G4: RBM.Univ.UNNormBandRow
  - G4: RBM.Univ.UNL32
  - G4: RBM.Univ.UNMLOut
  - G4: RBM.Univ.UNLocAvgBand
  - G4: RBM.Univ.UNQueBand
  - G4: RBM.Univ.UNGUESchurTail

## sanity checks (core closure)
- every core root reached: true
- RBM.BA.baThm27L_three: reached in the core
  reached via (first discovered path, from the name up to a root): RBM.BA.baThm27L_three <- RBM.Endpoints.Thm27_of_L32
- RBM.BA.unMLOutBA_three: reached in the core
  reached via (first discovered path, from the name up to a root): RBM.BA.unMLOutBA_three <- RBM.BA.baThm27L_three <- RBM.Endpoints.Thm27_of_L32
- RBM.Endpoints.bUniv_holds: reached in the core
  reached via (first discovered path, from the name up to a root): RBM.Endpoints.bUniv_holds <- RBM.Endpoints.unBUniv_of_L32 <- RBM.Endpoints.BUniv_of_L32 <- RBM.Endpoints.band_terminal

## (b) per module: declarations total (non-meta), reached, unreached; unreached as `name  start-end` sorted by line

| module | total | reached | unreached |
|---|---|---|---|
| RBM3D.Analysis.Resolvent | 8 | 7 | 1 |
| RBM3D.BA.B45BA | 29 | 14 | 15 |
| RBM3D.BA.Boundary | 13 | 2 | 11 |
| RBM3D.BA.CltFlowBA | 32 | 25 | 7 |
| RBM3D.BA.CombesThomas | 36 | 21 | 15 |
| RBM3D.BA.ConArg | 69 | 57 | 12 |
| RBM3D.BA.CouplingWindow | 33 | 18 | 15 |
| RBM3D.BA.DecayLoopBA | 8 | 2 | 6 |
| RBM3D.BA.EKGenBA | 36 | 17 | 19 |
| RBM3D.BA.EKNonzero | 21 | 11 | 10 |
| RBM3D.BA.EKPins | 60 | 27 | 33 |
| RBM3D.BA.EKSum | 36 | 32 | 4 |
| RBM3D.BA.EMCTE2BA | 41 | 18 | 23 |
| RBM3D.BA.EMn2BA | 41 | 30 | 11 |
| RBM3D.BA.FlowPins | 110 | 34 | 76 |
| RBM3D.BA.GUEDuhamelBA | 60 | 29 | 31 |
| RBM3D.BA.GUEDuhamelBA2 | 13 | 11 | 2 |
| RBM3D.BA.GUEEntry | 59 | 59 | 0 |
| RBM3D.BA.GUEEntry2 | 48 | 24 | 24 |
| RBM3D.BA.GUEEntryGridBA | 17 | 15 | 2 |
| RBM3D.BA.GUEEq729BA | 52 | 26 | 26 |
| RBM3D.BA.GUEHyp | 75 | 29 | 46 |
| RBM3D.BA.GUEHypABA | 45 | 8 | 37 |
| RBM3D.BA.GUEHypBBA | 46 | 26 | 20 |
| RBM3D.BA.GUEKPrim | 45 | 39 | 6 |
| RBM3D.BA.GUELLBA | 15 | 14 | 1 |
| RBM3D.BA.GUEOneLoop | 31 | 23 | 8 |
| RBM3D.BA.GUEPathBoundsBA | 14 | 9 | 5 |
| RBM3D.BA.GUEProcBA | 28 | 26 | 2 |
| RBM3D.BA.GUETwistBA | 103 | 102 | 1 |
| RBM3D.BA.GUETwistBA2 | 38 | 15 | 23 |
| RBM3D.BA.GbEXPav | 2 | 2 | 0 |
| RBM3D.BA.GreenCond | 136 | 124 | 12 |
| RBM3D.BA.GreenCond2 | 62 | 62 | 0 |
| RBM3D.BA.GreenCore | 132 | 92 | 40 |
| RBM3D.BA.GreenLDE | 13 | 8 | 5 |
| RBM3D.BA.GreenLocal | 44 | 31 | 13 |
| RBM3D.BA.GreenMinor | 35 | 19 | 16 |
| RBM3D.BA.GreenMinor2 | 45 | 11 | 34 |
| RBM3D.BA.GreenMinor3 | 60 | 53 | 7 |
| RBM3D.BA.GreenOff | 88 | 61 | 27 |
| RBM3D.BA.GreenSchur | 49 | 10 | 39 |
| RBM3D.BA.GreenStab | 29 | 10 | 19 |
| RBM3D.BA.GridDriftBA | 28 | 22 | 6 |
| RBM3D.BA.GridGoodBA | 53 | 3 | 50 |
| RBM3D.BA.GridMartBA | 40 | 37 | 3 |
| RBM3D.BA.GridRepTailBA | 83 | 70 | 13 |
| RBM3D.BA.ImmLower | 26 | 24 | 2 |
| RBM3D.BA.KBase | 34 | 27 | 7 |
| RBM3D.BA.KBound | 16 | 14 | 2 |
| RBM3D.BA.KCactus | 105 | 51 | 54 |
| RBM3D.BA.KCactusCut | 85 | 84 | 1 |
| RBM3D.BA.KDecayBA | 29 | 23 | 6 |
| RBM3D.BA.KHeat | 75 | 60 | 15 |
| RBM3D.BA.KHeatDiff | 71 | 66 | 5 |
| RBM3D.BA.KHeatTail | 32 | 29 | 3 |
| RBM3D.BA.KInduct | 35 | 29 | 6 |
| RBM3D.BA.KKernel | 54 | 24 | 30 |
| RBM3D.BA.KLipBA | 7 | 7 | 0 |
| RBM3D.BA.KMolecule | 21 | 20 | 1 |
| RBM3D.BA.KPure | 39 | 31 | 8 |
| RBM3D.BA.KSolve | 47 | 11 | 36 |
| RBM3D.BA.KStep | 20 | 18 | 2 |
| RBM3D.BA.KSumZeroA | 39 | 39 | 0 |
| RBM3D.BA.KSumZeroB | 21 | 18 | 3 |
| RBM3D.BA.KSymbol | 49 | 35 | 14 |
| RBM3D.BA.KTreeDeriv | 29 | 27 | 2 |
| RBM3D.BA.KTreeRep | 100 | 99 | 1 |
| RBM3D.BA.KWard | 13 | 12 | 1 |
| RBM3D.BA.KWardIneq | 34 | 34 | 0 |
| RBM3D.BA.LWPinsBA | 14 | 3 | 11 |
| RBM3D.BA.MADecolQUE | 20 | 15 | 5 |
| RBM3D.BA.MALocal | 34 | 30 | 4 |
| RBM3D.BA.MAPins | 26 | 21 | 5 |
| RBM3D.BA.MAQDiff | 29 | 25 | 4 |
| RBM3D.BA.MATrLocalBA | 11 | 6 | 5 |
| RBM3D.BA.MFixedPoint | 62 | 54 | 8 |
| RBM3D.BA.MReg | 16 | 12 | 4 |
| RBM3D.BA.MainIndFamTL | 13 | 10 | 3 |
| RBM3D.BA.MainIndGlue | 19 | 16 | 3 |
| RBM3D.BA.MainIndOutBA | 22 | 19 | 3 |
| RBM3D.BA.MainIndRegBA | 5 | 5 | 0 |
| RBM3D.BA.MainIndTermBA | 4 | 2 | 2 |
| RBM3D.BA.NetLiftBA | 15 | 15 | 0 |
| RBM3D.BA.NewKLKBA | 21 | 10 | 11 |
| RBM3D.BA.Prop5 | 66 | 61 | 5 |
| RBM3D.BA.Prop5Short | 40 | 24 | 16 |
| RBM3D.BA.Prop6Path | 46 | 37 | 9 |
| RBM3D.BA.PropUnit | 47 | 39 | 8 |
| RBM3D.BA.RandomLayerBGBA | 12 | 11 | 1 |
| RBM3D.BA.SEforLnBA | 20 | 12 | 8 |
| RBM3D.BA.Step1 | 28 | 9 | 19 |
| RBM3D.BA.Step1Boot | 49 | 32 | 17 |
| RBM3D.BA.Step1Fam | 66 | 41 | 25 |
| RBM3D.BA.Step1Prime | 35 | 22 | 13 |
| RBM3D.BA.Step1Setup | 47 | 28 | 19 |
| RBM3D.BA.Step1Trivial | 10 | 10 | 0 |
| RBM3D.BA.Step2BA | 18 | 7 | 11 |
| RBM3D.BA.Step2CloseBA | 5 | 5 | 0 |
| RBM3D.BA.Step2IterBA | 14 | 14 | 0 |
| RBM3D.BA.Step34BA | 28 | 14 | 14 |
| RBM3D.BA.Step5CasesBA | 40 | 16 | 24 |
| RBM3D.BA.Step5IIIEdet | 72 | 61 | 11 |
| RBM3D.BA.Step5IIIEdet2 | 42 | 37 | 5 |
| RBM3D.BA.Step5IIIGood | 24 | 21 | 3 |
| RBM3D.BA.Step5IIIGood2 | 6 | 1 | 5 |
| RBM3D.BA.Step5IIIKer | 31 | 28 | 3 |
| RBM3D.BA.Step5IIIKer2 | 13 | 9 | 4 |
| RBM3D.BA.Step5IIITargets | 6 | 3 | 3 |
| RBM3D.BA.Step5IIIWalk | 57 | 49 | 8 |
| RBM3D.BA.Step5IIIWalk2 | 14 | 11 | 3 |
| RBM3D.BA.Step5KerBA | 19 | 14 | 5 |
| RBM3D.BA.Step6BA | 10 | 10 | 0 |
| RBM3D.BA.Step6BridgeBA | 13 | 12 | 1 |
| RBM3D.BA.Step6PinsBA | 37 | 17 | 20 |
| RBM3D.BA.TwistAvgA | 84 | 80 | 4 |
| RBM3D.BA.TwistAvgA2 | 52 | 51 | 1 |
| RBM3D.BA.TwistAvgB | 14 | 14 | 0 |
| RBM3D.BA.TwistChain | 16 | 14 | 2 |
| RBM3D.BA.TwistFold2 | 37 | 28 | 9 |
| RBM3D.BA.TwistFold2B | 45 | 41 | 4 |
| RBM3D.BA.TwistGrid | 65 | 58 | 7 |
| RBM3D.BA.TwistGrid2 | 21 | 16 | 5 |
| RBM3D.BA.TwistGridRem | 46 | 46 | 0 |
| RBM3D.BA.TwistGridRem2 | 22 | 21 | 1 |
| RBM3D.BA.TwistGridTail | 73 | 73 | 0 |
| RBM3D.BA.TwistGridTail2 | 4 | 3 | 1 |
| RBM3D.BA.TwistGridWTail | 95 | 94 | 1 |
| RBM3D.BA.TwistGridWTail2 | 53 | 53 | 0 |
| RBM3D.BA.TwistKer | 70 | 68 | 2 |
| RBM3D.BA.TwistKer2 | 43 | 42 | 1 |
| RBM3D.BA.TwistLoop | 30 | 27 | 3 |
| RBM3D.BA.TwistPins | 76 | 70 | 6 |
| RBM3D.BA.TwistQV | 64 | 62 | 2 |
| RBM3D.BA.TwistStep | 59 | 59 | 0 |
| RBM3D.BA.TwistStep2 | 58 | 51 | 7 |
| RBM3D.BA.UNBUniv | 36 | 18 | 18 |
| RBM3D.BA.UNPins | 100 | 39 | 61 |
| RBM3D.BA.Ward | 21 | 14 | 7 |
| RBM3D.BA.ZeroModeBA | 27 | 3 | 24 |
| RBM3D.Chain.AzumaProxyGen | 33 | 12 | 21 |
| RBM3D.Chain.B45Gen | 29 | 10 | 19 |
| RBM3D.Chain.Carrier | 19 | 19 | 0 |
| RBM3D.Chain.CltFarUGen | 20 | 16 | 4 |
| RBM3D.Chain.CltGen | 26 | 21 | 5 |
| RBM3D.Chain.DecayGen | 25 | 15 | 10 |
| RBM3D.Chain.DecayGenTw | 1 | 1 | 0 |
| RBM3D.Chain.ExpAvgGen | 76 | 66 | 10 |
| RBM3D.Chain.ExpDuhamelGen | 25 | 19 | 6 |
| RBM3D.Chain.ExpEtermsAGen | 13 | 11 | 2 |
| RBM3D.Chain.ExpEtermsBGen | 24 | 20 | 4 |
| RBM3D.Chain.ExpHierGen | 38 | 35 | 3 |
| RBM3D.Chain.ExpIniIGen | 18 | 13 | 5 |
| RBM3D.Chain.ExpIntEasyGen | 14 | 11 | 3 |
| RBM3D.Chain.ExpIntIGen | 15 | 8 | 7 |
| RBM3D.Chain.ExpIntIIGen | 7 | 6 | 1 |
| RBM3D.Chain.ExpIntIQGen | 20 | 13 | 7 |
| RBM3D.Chain.ExpWardIGen | 21 | 16 | 5 |
| RBM3D.Chain.ExpWardIIGen | 15 | 11 | 4 |
| RBM3D.Chain.GridAssemblyGen | 51 | 25 | 26 |
| RBM3D.Chain.GridDuhamelGen | 37 | 13 | 24 |
| RBM3D.Chain.GridEnvelopeGen | 14 | 6 | 8 |
| RBM3D.Chain.GridGoodGen | 59 | 33 | 26 |
| RBM3D.Chain.GridRepTailGen | 36 | 36 | 0 |
| RBM3D.Chain.GridRepTailGen2 | 14 | 6 | 8 |
| RBM3D.Chain.HierDriftGen | 73 | 36 | 37 |
| RBM3D.Chain.IniTermIGen | 20 | 20 | 0 |
| RBM3D.Chain.IniTermIGen2 | 10 | 9 | 1 |
| RBM3D.Chain.IniTermIIGen | 24 | 23 | 1 |
| RBM3D.Chain.IterationsGen | 30 | 23 | 7 |
| RBM3D.Chain.IterationsGen2 | 25 | 17 | 8 |
| RBM3D.Chain.KDecayGen | 10 | 4 | 6 |
| RBM3D.Chain.LWGen | 21 | 10 | 11 |
| RBM3D.Chain.NQBudgetGen | 25 | 11 | 14 |
| RBM3D.Chain.NQEndFlowGen | 36 | 20 | 16 |
| RBM3D.Chain.NQEndLinGen | 26 | 17 | 9 |
| RBM3D.Chain.NQGood1Gen | 41 | 22 | 19 |
| RBM3D.Chain.NQGood2Gen | 45 | 18 | 27 |
| RBM3D.Chain.NQLinGen | 42 | 19 | 23 |
| RBM3D.Chain.NewKLKGen | 17 | 4 | 13 |
| RBM3D.Chain.NewKLKLGen | 6 | 1 | 5 |
| RBM3D.Chain.OptL2Gen | 29 | 24 | 5 |
| RBM3D.Chain.QEndB1Gen | 20 | 14 | 6 |
| RBM3D.Chain.QEndGridGen | 11 | 8 | 3 |
| RBM3D.Chain.QGridGen | 52 | 27 | 25 |
| RBM3D.Chain.QGridGen2 | 9 | 2 | 7 |
| RBM3D.Chain.QopDecayGen | 11 | 4 | 7 |
| RBM3D.Chain.QtBootGen | 14 | 10 | 4 |
| RBM3D.Chain.QtNonzeroBootGen | 16 | 8 | 8 |
| RBM3D.Chain.QtNonzeroEndGen | 7 | 5 | 2 |
| RBM3D.Chain.QtNonzeroFlowGen | 27 | 15 | 12 |
| RBM3D.Chain.QtNonzeroGen | 20 | 12 | 8 |
| RBM3D.Chain.QtXiRoundLiftGen | 18 | 11 | 7 |
| RBM3D.Chain.SEforLnGen | 65 | 61 | 4 |
| RBM3D.Chain.SEforLnGen2 | 29 | 28 | 1 |
| RBM3D.Chain.Step2CloseGen | 30 | 23 | 7 |
| RBM3D.Chain.Step2EventsGen | 54 | 48 | 6 |
| RBM3D.Chain.Step2EventsGenTw | 7 | 4 | 3 |
| RBM3D.Chain.Step2Gen | 144 | 87 | 57 |
| RBM3D.Chain.Step2IterGen | 17 | 12 | 5 |
| RBM3D.Chain.Step2IterGen2 | 12 | 7 | 5 |
| RBM3D.Chain.Step2Kern | 7 | 5 | 2 |
| RBM3D.Chain.Step34Gen | 123 | 46 | 77 |
| RBM3D.Chain.Step34RGen | 25 | 12 | 13 |
| RBM3D.Chain.Step5CasesGen | 19 | 17 | 2 |
| RBM3D.Chain.Step5Gen | 57 | 29 | 28 |
| RBM3D.Chain.Step5KerGen | 16 | 12 | 4 |
| RBM3D.Chain.Step6Gen | 94 | 35 | 59 |
| RBM3D.Chain.Step6KitGen | 37 | 23 | 14 |
| RBM3D.Chain.StepDecompGen | 100 | 60 | 40 |
| RBM3D.Chain.ZeroModeGen | 48 | 23 | 25 |
| RBM3D.Defs.Block | 20 | 20 | 0 |
| RBM3D.Defs.Convolution | 10 | 10 | 0 |
| RBM3D.Defs.Domination | 27 | 5 | 22 |
| RBM3D.Defs.Lattice | 15 | 13 | 2 |
| RBM3D.Defs.Neighbours | 15 | 15 | 0 |
| RBM3D.Defs.Params | 8 | 8 | 0 |
| RBM3D.Defs.RadialSum | 25 | 25 | 0 |
| RBM3D.Defs.Semicircle | 37 | 36 | 1 |
| RBM3D.Defs.SemicircleIntegral | 7 | 0 | 7 |
| RBM3D.Defs.Shells | 7 | 7 | 0 |
| RBM3D.Defs.Sizes | 47 | 37 | 10 |
| RBM3D.Defs.StochDom | 23 | 2 | 21 |
| RBM3D.Defs.StochDomAt | 84 | 38 | 46 |
| RBM3D.Defs.Tail | 18 | 18 | 0 |
| RBM3D.Endpoints | 78 | 49 | 29 |
| RBM3D.Evolution.CltFar | 77 | 73 | 4 |
| RBM3D.Evolution.CltFarG | 24 | 18 | 6 |
| RBM3D.Evolution.CltGood | 38 | 22 | 16 |
| RBM3D.Evolution.CltMoments1 | 92 | 70 | 22 |
| RBM3D.Evolution.CltMoments2 | 98 | 62 | 36 |
| RBM3D.Evolution.CltMoments2G | 28 | 24 | 4 |
| RBM3D.Evolution.CltPath | 60 | 16 | 44 |
| RBM3D.Evolution.CltResolvent | 98 | 47 | 51 |
| RBM3D.Evolution.CltStep | 54 | 41 | 13 |
| RBM3D.Evolution.CltSwap | 24 | 24 | 0 |
| RBM3D.Evolution.ExpInv | 42 | 39 | 3 |
| RBM3D.Evolution.FarEntry | 51 | 39 | 12 |
| RBM3D.Evolution.MeanFar | 64 | 54 | 10 |
| RBM3D.Evolution.MeanFarG | 19 | 14 | 5 |
| RBM3D.Evolution.Nonzero | 7 | 6 | 1 |
| RBM3D.Evolution.Pins | 36 | 10 | 26 |
| RBM3D.Evolution.Prec | 27 | 12 | 15 |
| RBM3D.Evolution.PropTInf | 26 | 17 | 9 |
| RBM3D.Evolution.SumDecay | 15 | 6 | 9 |
| RBM3D.Evolution.SumDecayZero | 45 | 22 | 23 |
| RBM3D.Evolution.XiPins | 12 | 9 | 3 |
| RBM3D.Gauss.BlockAnderson | 21 | 9 | 12 |
| RBM3D.Gauss.Domination | 13 | 8 | 5 |
| RBM3D.Gauss.DominationAt | 33 | 12 | 21 |
| RBM3D.Gauss.Envelope | 3 | 0 | 3 |
| RBM3D.Gauss.FineModel | 64 | 58 | 6 |
| RBM3D.Gauss.FlowCalculus | 62 | 47 | 15 |
| RBM3D.Gauss.LinearForm | 19 | 14 | 5 |
| RBM3D.Gauss.LoopCoordinate | 45 | 35 | 10 |
| RBM3D.Gauss.LoopFlowStein | 44 | 37 | 7 |
| RBM3D.Gauss.LoopGenerator | 56 | 36 | 20 |
| RBM3D.Gauss.Model | 15 | 4 | 11 |
| RBM3D.Gauss.Stein | 11 | 11 | 0 |
| RBM3D.Gauss.SteinMatrix | 6 | 6 | 0 |
| RBM3D.Graph.AnpKey | 59 | 44 | 15 |
| RBM3D.Graph.AnpKey2 | 167 | 11 | 156 |
| RBM3D.Graph.AnpKey3 | 25 | 1 | 24 |
| RBM3D.Graph.AnpKey4 | 30 | 0 | 30 |
| RBM3D.Graph.AnpKey5 | 112 | 98 | 14 |
| RBM3D.Graph.AnpKey6 | 54 | 35 | 19 |
| RBM3D.Graph.AuxGraph | 97 | 78 | 19 |
| RBM3D.Graph.AuxGraph2 | 62 | 50 | 12 |
| RBM3D.Graph.AuxGraphRooted | 12 | 9 | 3 |
| RBM3D.Graph.BAAnpLift | 9 | 8 | 1 |
| RBM3D.Graph.BAAtom | 50 | 37 | 13 |
| RBM3D.Graph.BAAtom2 | 20 | 14 | 6 |
| RBM3D.Graph.BAAtomic | 99 | 71 | 28 |
| RBM3D.Graph.BAAtomic2 | 18 | 8 | 10 |
| RBM3D.Graph.BAAuxGraph2 | 52 | 44 | 8 |
| RBM3D.Graph.BAAuxGraph2B | 31 | 19 | 12 |
| RBM3D.Graph.BAEngine | 33 | 29 | 4 |
| RBM3D.Graph.BAExp14a | 68 | 67 | 1 |
| RBM3D.Graph.BAExp14a2 | 25 | 23 | 2 |
| RBM3D.Graph.BAExp14aB | 103 | 102 | 1 |
| RBM3D.Graph.BAExp14b | 77 | 71 | 6 |
| RBM3D.Graph.BAExp14b2 | 59 | 57 | 2 |
| RBM3D.Graph.BAExp14b2B | 40 | 39 | 1 |
| RBM3D.Graph.BAExp14bB | 74 | 73 | 1 |
| RBM3D.Graph.BAExp14c | 45 | 41 | 4 |
| RBM3D.Graph.BAExp14cB | 36 | 24 | 12 |
| RBM3D.Graph.BAExp14d | 23 | 12 | 11 |
| RBM3D.Graph.BAExp14dB | 21 | 21 | 0 |
| RBM3D.Graph.BAExp14e | 9 | 7 | 2 |
| RBM3D.Graph.BAExpand | 54 | 46 | 8 |
| RBM3D.Graph.BAExpandId | 70 | 44 | 26 |
| RBM3D.Graph.BAExpandW | 45 | 42 | 3 |
| RBM3D.Graph.BAExpandWOrd | 46 | 39 | 7 |
| RBM3D.Graph.BAG5Leaf | 69 | 58 | 11 |
| RBM3D.Graph.BAGGExp | 27 | 24 | 3 |
| RBM3D.Graph.BAGGOp | 116 | 91 | 25 |
| RBM3D.Graph.BALWOut | 3 | 1 | 2 |
| RBM3D.Graph.BALocReg1 | 55 | 38 | 17 |
| RBM3D.Graph.BALocReg1B | 65 | 13 | 52 |
| RBM3D.Graph.BALocReg2 | 41 | 32 | 9 |
| RBM3D.Graph.BALocReg2B | 24 | 15 | 9 |
| RBM3D.Graph.BALvl1A | 46 | 34 | 12 |
| RBM3D.Graph.BALvl1B | 37 | 30 | 7 |
| RBM3D.Graph.BALvl1B2 | 10 | 10 | 0 |
| RBM3D.Graph.BALvl1C | 35 | 35 | 0 |
| RBM3D.Graph.BAMomentExpGen | 37 | 23 | 14 |
| RBM3D.Graph.BAMomentExpGenB | 29 | 27 | 2 |
| RBM3D.Graph.BAMomentGen | 49 | 44 | 5 |
| RBM3D.Graph.BAMomentGenB | 38 | 13 | 25 |
| RBM3D.Graph.BAProv | 68 | 50 | 18 |
| RBM3D.Graph.BAProvB | 75 | 71 | 4 |
| RBM3D.Graph.BAS3Close | 151 | 143 | 8 |
| RBM3D.Graph.BAS3CloseB | 105 | 104 | 1 |
| RBM3D.Graph.BAS3CloseC | 124 | 93 | 31 |
| RBM3D.Graph.BAScost | 110 | 83 | 27 |
| RBM3D.Graph.BAScost2 | 17 | 5 | 12 |
| RBM3D.Graph.BAShapeO2 | 49 | 48 | 1 |
| RBM3D.Graph.BAShapeO2B | 16 | 15 | 1 |
| RBM3D.Graph.BASim | 144 | 132 | 12 |
| RBM3D.Graph.BASim2 | 138 | 134 | 4 |
| RBM3D.Graph.BASim3 | 111 | 94 | 17 |
| RBM3D.Graph.BASizeClaim | 46 | 43 | 3 |
| RBM3D.Graph.BASizeClaim2 | 31 | 18 | 13 |
| RBM3D.Graph.BAStepS | 39 | 33 | 6 |
| RBM3D.Graph.BASymm1 | 35 | 29 | 6 |
| RBM3D.Graph.BASymm2 | 36 | 6 | 30 |
| RBM3D.Graph.BATermHolds | 23 | 23 | 0 |
| RBM3D.Graph.BATermHoldsB | 22 | 16 | 6 |
| RBM3D.Graph.BAVocab | 144 | 107 | 37 |
| RBM3D.Graph.BAWeightOp | 90 | 80 | 10 |
| RBM3D.Graph.BAZetaExp | 21 | 13 | 8 |
| RBM3D.Graph.Expansions | 3 | 2 | 1 |
| RBM3D.Graph.LWEdgeExp | 61 | 32 | 29 |
| RBM3D.Graph.LWEngine | 82 | 70 | 12 |
| RBM3D.Graph.LWExpCert | 32 | 17 | 15 |
| RBM3D.Graph.LWExpCertB | 25 | 13 | 12 |
| RBM3D.Graph.LWExpCertBS0 | 363 | 363 | 0 |
| RBM3D.Graph.LWExpCertBS1 | 383 | 383 | 0 |
| RBM3D.Graph.LWExpCertS0 | 96 | 0 | 96 |
| RBM3D.Graph.LWExpCertS1 | 97 | 0 | 97 |
| RBM3D.Graph.LWExpSim | 85 | 73 | 12 |
| RBM3D.Graph.LWExpSound | 108 | 95 | 13 |
| RBM3D.Graph.LWExpTerm | 59 | 14 | 45 |
| RBM3D.Graph.LWExpTerm2 | 150 | 134 | 16 |
| RBM3D.Graph.LWExpTerm3 | 84 | 65 | 19 |
| RBM3D.Graph.LWExpTerm4 | 83 | 72 | 11 |
| RBM3D.Graph.LWExpTerm5 | 49 | 39 | 10 |
| RBM3D.Graph.LWExpTerm6 | 25 | 12 | 13 |
| RBM3D.Graph.LWGGExp | 57 | 36 | 21 |
| RBM3D.Graph.LWLvl1 | 218 | 168 | 50 |
| RBM3D.Graph.LWMomExp | 66 | 40 | 26 |
| RBM3D.Graph.LWMomExpD | 1 | 1 | 0 |
| RBM3D.Graph.LWMomExpFar | 31 | 24 | 7 |
| RBM3D.Graph.LWMomExpInf | 31 | 27 | 4 |
| RBM3D.Graph.LWMoment | 69 | 67 | 2 |
| RBM3D.Graph.LWMomentExp | 62 | 61 | 1 |
| RBM3D.Graph.LWMomentExpA | 14 | 13 | 1 |
| RBM3D.Graph.LWPins | 86 | 33 | 53 |
| RBM3D.Graph.LWProv | 121 | 110 | 11 |
| RBM3D.Graph.LWPsi | 72 | 30 | 42 |
| RBM3D.Graph.LWSizeClaim | 68 | 51 | 17 |
| RBM3D.Graph.LWStein | 134 | 77 | 57 |
| RBM3D.Graph.LWSymm | 186 | 141 | 45 |
| RBM3D.Graph.LWTermExpN | 18 | 17 | 1 |
| RBM3D.Graph.LWTermHolds | 54 | 46 | 8 |
| RBM3D.Graph.LWVocab | 256 | 161 | 95 |
| RBM3D.Graph.LWWeightExp | 87 | 48 | 39 |
| RBM3D.Graph.LWXiExp | 32 | 28 | 4 |
| RBM3D.Graph.LocalRegular | 163 | 80 | 83 |
| RBM3D.Graph.LocalRegular2 | 103 | 91 | 12 |
| RBM3D.Graph.LocalRegular6a | 105 | 71 | 34 |
| RBM3D.Graph.LocalRegular6b | 154 | 118 | 36 |
| RBM3D.Graph.LocalRegular6c | 100 | 80 | 20 |
| RBM3D.Graph.LocalRegular6d | 117 | 69 | 48 |
| RBM3D.Graph.Model | 32 | 0 | 32 |
| RBM3D.Graph.ScalingOrder | 9 | 2 | 7 |
| RBM3D.Green.CondDom | 75 | 25 | 50 |
| RBM3D.Green.EntryCore | 100 | 61 | 39 |
| RBM3D.Green.EntryDom | 84 | 62 | 22 |
| RBM3D.Green.FlucIter | 90 | 69 | 21 |
| RBM3D.Green.FlucIterGain | 62 | 19 | 43 |
| RBM3D.Green.FlucThreshold | 75 | 44 | 31 |
| RBM3D.Green.FlucVanish | 130 | 94 | 36 |
| RBM3D.Green.GbEXP | 47 | 28 | 19 |
| RBM3D.Green.IBP | 68 | 47 | 21 |
| RBM3D.Green.IBPPoly | 67 | 58 | 9 |
| RBM3D.Green.IBPRem | 47 | 17 | 30 |
| RBM3D.Green.LDE | 118 | 64 | 54 |
| RBM3D.Green.LDEQuad | 89 | 75 | 14 |
| RBM3D.Green.LDEQuadMom | 52 | 37 | 15 |
| RBM3D.Green.LDEQuadT | 73 | 60 | 13 |
| RBM3D.Green.LocalLaw | 65 | 50 | 15 |
| RBM3D.Green.MinorDiff | 129 | 54 | 75 |
| RBM3D.Green.MinorDiffCond | 95 | 37 | 58 |
| RBM3D.Green.MinorGoodLe | 103 | 62 | 41 |
| RBM3D.Green.Pins | 115 | 72 | 43 |
| RBM3D.Green.RowIndep | 110 | 85 | 25 |
| RBM3D.Green.Stability | 18 | 16 | 2 |
| RBM3D.Hierarchy.ContractionBasic | 45 | 39 | 6 |
| RBM3D.Hierarchy.ContractionSecondLoop | 71 | 50 | 21 |
| RBM3D.Induction.AzumaProxyN | 91 | 21 | 70 |
| RBM3D.Induction.AzumaProxyN2 | 92 | 42 | 50 |
| RBM3D.Induction.B45 | 83 | 40 | 43 |
| RBM3D.Induction.ConArg | 24 | 22 | 2 |
| RBM3D.Induction.ConArgDet | 85 | 65 | 20 |
| RBM3D.Induction.Continuity | 21 | 19 | 2 |
| RBM3D.Induction.ContinuityNet | 48 | 40 | 8 |
| RBM3D.Induction.Contract | 62 | 62 | 0 |
| RBM3D.Induction.ContractPt | 43 | 35 | 8 |
| RBM3D.Induction.DecayLoopA | 31 | 1 | 30 |
| RBM3D.Induction.DecayLoopB | 107 | 80 | 27 |
| RBM3D.Induction.Defs | 72 | 31 | 41 |
| RBM3D.Induction.DuhamelI | 35 | 35 | 0 |
| RBM3D.Induction.DuhamelI2 | 45 | 43 | 2 |
| RBM3D.Induction.DuhamelII | 18 | 16 | 2 |
| RBM3D.Induction.EMn2Exp1 | 86 | 61 | 25 |
| RBM3D.Induction.EMn2Exp2 | 45 | 28 | 17 |
| RBM3D.Induction.EMn2Poly | 45 | 40 | 5 |
| RBM3D.Induction.EtermsMid | 10 | 10 | 0 |
| RBM3D.Induction.EtermsMid2 | 66 | 56 | 10 |
| RBM3D.Induction.ExpAvg | 55 | 37 | 18 |
| RBM3D.Induction.ExpDuhamel | 39 | 27 | 12 |
| RBM3D.Induction.ExpEtermsA | 24 | 13 | 11 |
| RBM3D.Induction.ExpEtermsB | 51 | 37 | 14 |
| RBM3D.Induction.ExpHier | 51 | 45 | 6 |
| RBM3D.Induction.ExpIniI | 36 | 25 | 11 |
| RBM3D.Induction.ExpIntEasy | 30 | 21 | 9 |
| RBM3D.Induction.ExpIntI | 27 | 16 | 11 |
| RBM3D.Induction.ExpIntII | 24 | 15 | 9 |
| RBM3D.Induction.ExpIntIQ | 47 | 36 | 11 |
| RBM3D.Induction.ExpWardI | 29 | 21 | 8 |
| RBM3D.Induction.ExpWardII | 29 | 21 | 8 |
| RBM3D.Induction.GridAssemblyN | 91 | 49 | 42 |
| RBM3D.Induction.GridDriftN | 53 | 44 | 9 |
| RBM3D.Induction.GridDuhamelN | 44 | 16 | 28 |
| RBM3D.Induction.GridEnvelopeN | 32 | 19 | 13 |
| RBM3D.Induction.GridGoodN | 66 | 46 | 20 |
| RBM3D.Induction.HierAlgebra | 48 | 39 | 9 |
| RBM3D.Induction.HierarchyN | 16 | 3 | 13 |
| RBM3D.Induction.IniTermI | 120 | 111 | 9 |
| RBM3D.Induction.IniTermII | 64 | 56 | 8 |
| RBM3D.Induction.IterationsA | 77 | 43 | 34 |
| RBM3D.Induction.IterationsB | 35 | 29 | 6 |
| RBM3D.Induction.KDecay | 52 | 34 | 18 |
| RBM3D.Induction.LemDecCalELip | 75 | 55 | 20 |
| RBM3D.Induction.LemDecCalEPrec | 56 | 45 | 11 |
| RBM3D.Induction.LocalAvg1 | 23 | 16 | 7 |
| RBM3D.Induction.LocalAvg2 | 16 | 10 | 6 |
| RBM3D.Induction.LoopC2N | 29 | 24 | 5 |
| RBM3D.Induction.LoopGenN | 47 | 36 | 11 |
| RBM3D.Induction.MainIndBase | 14 | 14 | 0 |
| RBM3D.Induction.MainIndChain | 9 | 9 | 0 |
| RBM3D.Induction.MainIndHolds | 6 | 1 | 5 |
| RBM3D.Induction.MainIndOut | 12 | 11 | 1 |
| RBM3D.Induction.MainIndRegimes | 70 | 35 | 35 |
| RBM3D.Induction.NQBudget | 81 | 17 | 64 |
| RBM3D.Induction.NQEndFlow | 46 | 37 | 9 |
| RBM3D.Induction.NQEndFlowLift | 28 | 6 | 22 |
| RBM3D.Induction.NQEndLin | 77 | 36 | 41 |
| RBM3D.Induction.NQGood1 | 102 | 34 | 68 |
| RBM3D.Induction.NQGood2 | 86 | 23 | 63 |
| RBM3D.Induction.NQLin | 107 | 46 | 61 |
| RBM3D.Induction.NewKLK | 40 | 35 | 5 |
| RBM3D.Induction.NewKLKL | 34 | 30 | 4 |
| RBM3D.Induction.NewPQ | 38 | 38 | 0 |
| RBM3D.Induction.OptL2a | 39 | 38 | 1 |
| RBM3D.Induction.OptL2b | 8 | 8 | 0 |
| RBM3D.Induction.PerTimeCalc | 74 | 35 | 39 |
| RBM3D.Induction.PfStep5 | 80 | 68 | 12 |
| RBM3D.Induction.PfStep5Alg | 42 | 21 | 21 |
| RBM3D.Induction.PfStep5Grid | 66 | 45 | 21 |
| RBM3D.Induction.QBudgetA | 93 | 32 | 61 |
| RBM3D.Induction.QBudgetB | 81 | 27 | 54 |
| RBM3D.Induction.QDriftA | 117 | 34 | 83 |
| RBM3D.Induction.QDriftB | 59 | 18 | 41 |
| RBM3D.Induction.QEndA | 61 | 56 | 5 |
| RBM3D.Induction.QEndA2 | 102 | 0 | 102 |
| RBM3D.Induction.QEndB1 | 48 | 40 | 8 |
| RBM3D.Induction.QEndGrid | 92 | 51 | 41 |
| RBM3D.Induction.QGridA | 122 | 115 | 7 |
| RBM3D.Induction.QGridB | 21 | 17 | 4 |
| RBM3D.Induction.QLevelsA | 49 | 15 | 34 |
| RBM3D.Induction.QLevelsB | 48 | 2 | 46 |
| RBM3D.Induction.QProxy | 64 | 59 | 5 |
| RBM3D.Induction.QProxy2 | 74 | 0 | 74 |
| RBM3D.Induction.QVN | 55 | 51 | 4 |
| RBM3D.Induction.QopAlgebra | 58 | 49 | 9 |
| RBM3D.Induction.QopDecay | 47 | 39 | 8 |
| RBM3D.Induction.QopNorm | 14 | 10 | 4 |
| RBM3D.Induction.QtNonzero | 75 | 26 | 49 |
| RBM3D.Induction.QtNonzeroBoot | 35 | 29 | 6 |
| RBM3D.Induction.QtNonzeroEnd | 79 | 30 | 49 |
| RBM3D.Induction.QtNonzeroFlow | 34 | 33 | 1 |
| RBM3D.Induction.QtNonzeroFlowLift | 26 | 25 | 1 |
| RBM3D.Induction.QtXiRoundLift | 27 | 24 | 3 |
| RBM3D.Induction.SEforLn1 | 38 | 37 | 1 |
| RBM3D.Induction.SEforLn2 | 59 | 59 | 0 |
| RBM3D.Induction.ScaleFacts | 31 | 10 | 21 |
| RBM3D.Induction.ScaleFacts3 | 27 | 20 | 7 |
| RBM3D.Induction.SizesComp | 85 | 32 | 53 |
| RBM3D.Induction.Split | 78 | 58 | 20 |
| RBM3D.Induction.Step1 | 20 | 15 | 5 |
| RBM3D.Induction.Step1Setup | 74 | 57 | 17 |
| RBM3D.Induction.Step2Core | 57 | 29 | 28 |
| RBM3D.Induction.Step2Defs | 87 | 64 | 23 |
| RBM3D.Induction.Step2Events | 80 | 54 | 26 |
| RBM3D.Induction.Step2Iterate | 77 | 53 | 24 |
| RBM3D.Induction.Step2K2 | 6 | 6 | 0 |
| RBM3D.Induction.Step2Scale | 24 | 24 | 0 |
| RBM3D.Induction.Step3 | 15 | 11 | 4 |
| RBM3D.Induction.Step34Pins | 125 | 58 | 67 |
| RBM3D.Induction.Step34PinsP | 6 | 0 | 6 |
| RBM3D.Induction.Step4 | 14 | 6 | 8 |
| RBM3D.Induction.Step5Cases | 16 | 14 | 2 |
| RBM3D.Induction.Step5Kernel | 45 | 10 | 35 |
| RBM3D.Induction.Step5Kit | 27 | 19 | 8 |
| RBM3D.Induction.Step5Pins | 106 | 44 | 62 |
| RBM3D.Induction.Step6Kit | 81 | 42 | 39 |
| RBM3D.Induction.Step6Pins | 76 | 39 | 37 |
| RBM3D.Induction.StepDecompN | 101 | 71 | 30 |
| RBM3D.Induction.TailtoTail | 23 | 21 | 2 |
| RBM3D.Induction.TailtoTailSq | 33 | 31 | 2 |
| RBM3D.Induction.WardII | 17 | 16 | 1 |
| RBM3D.Induction.ZeroModeCalc | 58 | 42 | 16 |
| RBM3D.Kernel.Evolution | 35 | 30 | 5 |
| RBM3D.Kernel.PropT | 43 | 26 | 17 |
| RBM3D.Kernel.SumDecay | 13 | 8 | 5 |
| RBM3D.Loop.GLoop | 13 | 6 | 7 |
| RBM3D.Loop.GLoopFlow | 61 | 42 | 19 |
| RBM3D.Loop.KBound | 3 | 1 | 2 |
| RBM3D.Loop.KLCut | 121 | 88 | 33 |
| RBM3D.Loop.KLFinal | 25 | 19 | 6 |
| RBM3D.Loop.KLIndStepA | 61 | 49 | 12 |
| RBM3D.Loop.KLIndStepB | 28 | 27 | 1 |
| RBM3D.Loop.KLInduct | 31 | 26 | 5 |
| RBM3D.Loop.KLMolecule | 39 | 29 | 10 |
| RBM3D.Loop.KLSumAll | 38 | 30 | 8 |
| RBM3D.Loop.KLSumZero | 77 | 43 | 34 |
| RBM3D.Loop.KLSumZeroWard | 50 | 40 | 10 |
| RBM3D.Loop.KLTree | 102 | 81 | 21 |
| RBM3D.Loop.KLTreeDeriv | 50 | 40 | 10 |
| RBM3D.Loop.KLUnique | 49 | 30 | 19 |
| RBM3D.Loop.KLWard | 74 | 64 | 10 |
| RBM3D.Loop.KLWardIneq | 24 | 24 | 0 |
| RBM3D.Loop.Partition | 35 | 14 | 21 |
| RBM3D.Loop.Primitive | 11 | 5 | 6 |
| RBM3D.Loop.PureLoop | 6 | 1 | 5 |
| RBM3D.Loop.TreeFour | 8 | 0 | 8 |
| RBM3D.Loop.TreeRep | 18 | 18 | 0 |
| RBM3D.Loop.TreeThree | 15 | 0 | 15 |
| RBM3D.Loop.Unique | 24 | 17 | 7 |
| RBM3D.Main.BUniv | 2 | 2 | 0 |
| RBM3D.Main.BUnivHolds | 8 | 8 | 0 |
| RBM3D.Main.BandTerminal | 12 | 9 | 3 |
| RBM3D.Main.FinalShape | 4 | 4 | 0 |
| RBM3D.Main.FixedZ | 26 | 20 | 6 |
| RBM3D.Main.QUECore | 57 | 54 | 3 |
| RBM3D.Main.QUEFromQDiff | 23 | 14 | 9 |
| RBM3D.Main.ZNet | 54 | 49 | 5 |
| RBM3D.Main.ZTransfer | 31 | 25 | 6 |
| RBM3D.Path.Azuma | 8 | 5 | 3 |
| RBM3D.Path.DifREP1 | 74 | 63 | 11 |
| RBM3D.Path.DifREP2 | 101 | 68 | 33 |
| RBM3D.Path.DifREP3 | 99 | 91 | 8 |
| RBM3D.Path.DriftAlgebra | 34 | 0 | 34 |
| RBM3D.Path.DuhamelTail | 36 | 0 | 36 |
| RBM3D.Path.Expansion | 93 | 0 | 93 |
| RBM3D.Path.KellStar | 16 | 6 | 10 |
| RBM3D.Path.Kernel | 19 | 4 | 15 |
| RBM3D.Path.LemDecCalE | 60 | 45 | 15 |
| RBM3D.Path.LemDecCalEdif | 70 | 54 | 16 |
| RBM3D.Path.LemDecCalEdif2 | 30 | 25 | 5 |
| RBM3D.Path.LemDecCalEwG | 85 | 72 | 13 |
| RBM3D.Path.LoopStep | 22 | 15 | 7 |
| RBM3D.Path.Markov | 47 | 35 | 12 |
| RBM3D.Path.NetLift1 | 26 | 26 | 0 |
| RBM3D.Path.NetLift2 | 22 | 22 | 0 |
| RBM3D.Path.OneStep | 134 | 108 | 26 |
| RBM3D.Path.QVIdentity | 59 | 17 | 42 |
| RBM3D.Path.StepDecomp | 90 | 29 | 61 |
| RBM3D.Path.StepDecompLoop | 49 | 14 | 35 |
| RBM3D.Path.Stop | 15 | 9 | 6 |
| RBM3D.Path.UBounds | 47 | 1 | 46 |
| RBM3D.Path.UTransport | 17 | 0 | 17 |
| RBM3D.Path.Walk | 72 | 51 | 21 |
| RBM3D.Propagator.Basic | 17 | 16 | 1 |
| RBM3D.Propagator.Deriv | 5 | 5 | 0 |
| RBM3D.Propagator.Gap | 23 | 5 | 18 |
| RBM3D.Propagator.HeatBounds1D | 43 | 41 | 2 |
| RBM3D.Propagator.HeatKernel1D | 17 | 14 | 3 |
| RBM3D.Propagator.HeatProduct | 52 | 52 | 0 |
| RBM3D.Propagator.HeatTorus1D | 23 | 23 | 0 |
| RBM3D.Propagator.Interface | 3 | 0 | 3 |
| RBM3D.Propagator.LaplaceGauss | 40 | 33 | 7 |
| RBM3D.Propagator.Pins | 16 | 8 | 8 |
| RBM3D.Propagator.Prop5Hold | 50 | 50 | 0 |
| RBM3D.Propagator.Prop5Short | 21 | 21 | 0 |
| RBM3D.Propagator.Prop6Hold | 24 | 15 | 9 |
| RBM3D.Propagator.PropUnit | 32 | 32 | 0 |
| RBM3D.Propagator.Props4 | 28 | 26 | 2 |
| RBM3D.Test.AuditNegative | 2 | 2 | 0 |
| RBM3D.Test.Axioms | 9 | 9 | 0 |
| RBM3D.Test.InterfaceShape | 7 | 0 | 7 |
| RBM3D.Universality.Apriori | 12 | 5 | 7 |
| RBM3D.Universality.EMCTE2 | 41 | 34 | 7 |
| RBM3D.Universality.EigenInterlacing | 31 | 27 | 4 |
| RBM3D.Universality.EigenMeasurable | 41 | 26 | 15 |
| RBM3D.Universality.FreeConv | 23 | 14 | 9 |
| RBM3D.Universality.FreeConvRegular | 54 | 43 | 11 |
| RBM3D.Universality.FreeConvStability | 34 | 34 | 0 |
| RBM3D.Universality.GUEInvariance | 104 | 95 | 9 |
| RBM3D.Universality.GUELocalBootstrap | 67 | 54 | 13 |
| RBM3D.Universality.GUELocalSchur | 31 | 16 | 15 |
| RBM3D.Universality.GUEPhase.AuxCarrier | 110 | 87 | 23 |
| RBM3D.Universality.GUEPhase.Bootstrap | 64 | 31 | 33 |
| RBM3D.Universality.GUEPhase.BootstrapAt | 61 | 11 | 50 |
| RBM3D.Universality.GUEPhase.BoundsA | 40 | 29 | 11 |
| RBM3D.Universality.GUEPhase.Drift | 79 | 64 | 15 |
| RBM3D.Universality.GUEPhase.DuhamelA1 | 80 | 65 | 15 |
| RBM3D.Universality.GUEPhase.DuhamelA2 | 85 | 57 | 28 |
| RBM3D.Universality.GUEPhase.DuhamelB | 67 | 43 | 24 |
| RBM3D.Universality.GUEPhase.DuhamelC | 47 | 40 | 7 |
| RBM3D.Universality.GUEPhase.EntryDet | 90 | 33 | 57 |
| RBM3D.Universality.GUEPhase.EntryGrid | 31 | 28 | 3 |
| RBM3D.Universality.GUEPhase.EntryTail | 112 | 49 | 63 |
| RBM3D.Universality.GUEPhase.EntryTailMain | 37 | 18 | 19 |
| RBM3D.Universality.GUEPhase.Eq729A | 79 | 43 | 36 |
| RBM3D.Universality.GUEPhase.Eq729B | 103 | 42 | 61 |
| RBM3D.Universality.GUEPhase.Generator | 70 | 63 | 7 |
| RBM3D.Universality.GUEPhase.Grid | 55 | 52 | 3 |
| RBM3D.Universality.GUEPhase.HypA | 92 | 40 | 52 |
| RBM3D.Universality.GUEPhase.HypB | 83 | 26 | 57 |
| RBM3D.Universality.GUEPhase.KPrim | 30 | 28 | 2 |
| RBM3D.Universality.GUEPhase.LLTransfer | 24 | 22 | 2 |
| RBM3D.Universality.GUEPhase.Markov | 53 | 37 | 16 |
| RBM3D.Universality.GUEPhase.OneLoop | 55 | 46 | 9 |
| RBM3D.Universality.GUEPhase.PathBounds | 46 | 16 | 30 |
| RBM3D.Universality.GUEPhase.Proc | 62 | 49 | 13 |
| RBM3D.Universality.GUEPhase.ProcK | 49 | 23 | 26 |
| RBM3D.Universality.GUEPhase.RandomLayerA | 23 | 13 | 10 |
| RBM3D.Universality.GUEPhase.RandomLayerB | 29 | 26 | 3 |
| RBM3D.Universality.GUEPhase.RandomLayerBG | 24 | 14 | 10 |
| RBM3D.Universality.GUEPhase.RandomLayerBGD | 8 | 4 | 4 |
| RBM3D.Universality.GUETranslation | 47 | 35 | 12 |
| RBM3D.Universality.GreenCorr | 50 | 35 | 15 |
| RBM3D.Universality.InjSum | 33 | 29 | 4 |
| RBM3D.Universality.Jak | 22 | 17 | 5 |
| RBM3D.Universality.JakKernel | 47 | 36 | 11 |
| RBM3D.Universality.JakSpectral | 39 | 29 | 10 |
| RBM3D.Universality.NormBand | 12 | 7 | 5 |
| RBM3D.Universality.OU | 15 | 11 | 4 |
| RBM3D.Universality.OUContraction | 40 | 31 | 9 |
| RBM3D.Universality.OUGenerator | 89 | 81 | 8 |
| RBM3D.Universality.OUHessian | 71 | 61 | 10 |
| RBM3D.Universality.OUInterfaceK | 30 | 18 | 12 |
| RBM3D.Universality.Pins | 141 | 82 | 59 |
| RBM3D.Universality.PinsC2 | 74 | 40 | 34 |
| RBM3D.Universality.PinsDens | 41 | 10 | 31 |
| RBM3D.Universality.PinsK | 75 | 39 | 36 |
| RBM3D.Universality.PinsKD | 18 | 8 | 10 |
| RBM3D.Universality.PoissonSmoothing | 34 | 30 | 4 |
| RBM3D.Universality.QUEFlow | 51 | 48 | 3 |
| RBM3D.Universality.Step1Band | 63 | 48 | 15 |
| RBM3D.Universality.Step1Cond | 39 | 27 | 12 |
| RBM3D.Universality.Step1Good | 33 | 29 | 4 |
| RBM3D.Universality.Step1RegularityGUE | 50 | 37 | 13 |
| RBM3D.Universality.UnivMain | 52 | 36 | 16 |
| RBM3D.Universality.Uyw | 23 | 18 | 5 |
| RBM3D.Universality.UywKernel | 63 | 47 | 16 |
| RBM3D.Universality.ZeroModeProfile | 55 | 35 | 20 |

### unreached declarations
### RBM3D.Analysis.Resolvent  (1 unreached of 8)
RBM.norm_le_of_isHermitian  116-122
### RBM3D.BA.B45BA  (15 unreached of 29)
RBM.BA.baWardTypePgL_of  222-236
RBM.BA.baB45gL_of  238-250
RBM.BA.BAWardTypePPin  258-262
RBM.BA.BAB45Pin  264-268
RBM.BA.baWardTypePPin_holds  270-279
RBM.BA.baB45Pin_holds  281-289
private RBM.BA.B45BAInst.B45BAInst_inv_size  304-311
RBM.BA.B45BAInst.inst_kerSums  313-315
RBM.BA.B45BAInst.inst_b45Facts  327-335
RBM.BA.B45BAInst.inst_wardTypePgL  337-344
RBM.BA.B45BAInst.inst_b45gL  346-352
RBM.BA.B45BAInst.inst_baWardTypePPin  354-357
RBM.BA.B45BAInst.inst_baB45Pin  359-362
RBM.BA.B45BAInst.inst_wardTypePPin_applied  364-377
RBM.BA.B45BAInst.inst_b45Pin_applied  379-390
### RBM3D.BA.Boundary  (11 unreached of 13)
private RBM.BA.Boundary_F  53-55
private RBM.BA.Boundary_self_iff_F  67-82
private RBM.BA.Boundary_F_hasStrictDerivAt  84-108
private RBM.BA.Boundary_gap_ne_zero  110-121
private RBM.BA.Boundary_norm_le_inv_im  123-152
private RBM.BA.Boundary_BAm_of_none  154-158
RBM.BA.BAm_tendsto_of_self  188-238
RBM.BA.BAm_im_tendsto_zero  242-277
RBM.BA.BArho_tendsto  281-302
RBM.BA.baMBoundary_holds  304-308
private RBM.BA.BoundaryInst.Boundary_none_10_63  324-327
### RBM3D.BA.CltFlowBA  (7 unreached of 32)
private RBM.BA.CltFlowBA_szI  597-602
private RBM.BA.CltFlowBA_wI  604-604
private RBM.BA.CltFlowBA_mI  605-605
private RBM.BA.CltFlowBA_zI  606-606
private RBM.BA.CltFlowBA_flowI  608-680
private RBM.BA.CltFlowBA_regI  682-683
private RBM.BA.CltFlowBA_tI  685-686
### RBM3D.BA.CombesThomas  (15 unreached of 36)
private RBM.BA.CombesThomasInst.CT_zSmS  586-586
private RBM.BA.CombesThomasInst.CT_wI_im  588-588
RBM.BA.CombesThomasInst.gap_im  590-592
RBM.BA.CombesThomasInst.nu_pos  594-595
RBM.BA.CombesThomasInst.gap_cond  597-600
RBM.BA.CombesThomasInst.core_at_point  602-607
RBM.BA.CombesThomasInst.row_at_point  609-615
RBM.BA.CombesThomasInst.lip_at_point  617-620
RBM.BA.CombesThomasInst.decay_large_at_P  622-627
RBM.BA.CombesThomasInst.propM3_at_P  629-638
RBM.BA.CombesThomasInst.upper_small_at_P  640-643
RBM.BA.CombesThomasInst.lower_small_at_P  645-648
RBM.BA.CombesThomasInst.propM_at_P  650-662
RBM.BA.CombesThomasInst.C_pos_at  664-665
RBM.BA.CombesThomasInst.rate_pos_at  667-668
### RBM3D.BA.ConArg  (12 unreached of 69)
RBM.BA.bandFM_omegaC  78-80
private RBM.BA.ConArg_vecEntry_single  1667-1671
private RBM.BA.ConArg_ratio  1673-1695
private RBM.BA.ConArg_loop1_im  1697-1712
RBM.BA.BAimTrace_compare  1714-1817
RBM.BA.ConArgInst.inst_BAConArgHyp  1845-1850
RBM.BA.ConArgInst.inst_baConArg''  1852-1862
RBM.BA.ConArgInst.inst_baConArgLoop''  1864-1871
RBM.BA.ConArgInst.inst_baConArgVec  1873-1879
RBM.BA.ConArgInst.inst_hflow_scale  1886-1892
private RBM.BA.ConArgInst.herm_diag  1900-1903
RBM.BA.ConArgInst.inst_imTrace  1953-1978
### RBM3D.BA.CouplingWindow  (15 unreached of 33)
RBM.BA.BAzztE_inv  74-82
RBM.BA.BAzztE_inv_holds  302-307
RBM.BA.BAwindow_iter  719-774
RBM.BA.BAwindow_floor  776-790
RBM.BA.CouplingWindowInst.szP  848-854
RBM.BA.CouplingWindowInst.zP  856-857
RBM.BA.CouplingWindowInst.t0P  859-861
RBM.BA.CouplingWindowInst.EP  862-862
RBM.BA.CouplingWindowInst.m0P  863-863
RBM.BA.CouplingWindowInst.g0P  864-864
RBM.BA.CouplingWindowInst.BAm_zP  866-867
RBM.BA.CouplingWindowInst.flowP_data  869-871
RBM.BA.CouplingWindowInst.g0P_pos  874-874
RBM.BA.CouplingWindowInst.g0P_le  876-876
RBM.BA.CouplingWindowInst.flowP_real  878-882
### RBM3D.BA.DecayLoopBA  (6 unreached of 8)
RBM.BA.baFlow_sizeInv_le  70-82
private RBM.BA.DecayLoopBA_PT_of_U  84-87
RBM.BA.baDecayLoopPT_of  89-99
RBM.BA.baDecayLoopAt_holds  101-108
RBM.BA.baSTLWB_of  134-137
RBM.BA.baSTLWT_of  139-142
### RBM3D.BA.EKGenBA  (19 unreached of 36)
RBM.BA.baEKSumRes1gL_holds  339-370
private RBM.BA.EKGenBAInst.EKGenBA_precL_of_le  500-509
private RBM.BA.EKGenBAInst.EKGenBA_fastDecay_delta0  511-523
private RBM.BA.EKGenBAInst.inst_L1  525-525
private RBM.BA.EKGenBAInst.inst_Wpos  527-527
private RBM.BA.EKGenBAInst.inst_W4  529-533
private RBM.BA.EKGenBAInst.inst_kernel  535-537
private RBM.BA.EKGenBAInst.inst_window  539-540
private RBM.BA.EKGenBAInst.inst_R1  542-550
private RBM.BA.EKGenBAInst.inst_win  552-553
private RBM.BA.EKGenBAInst.inst_prec_delta0  555-557
private RBM.BA.EKGenBAInst.inst_prec_Az  559-561
private RBM.BA.EKGenBAInst.inst_low  563-564
private RBM.BA.EKGenBAInst.inst_decay_delta0  566-570
private RBM.BA.EKGenBAInst.inst_decay_Az  572-583
private RBM.BA.EKGenBAInst.inst_lam_ratio_nonneg  620-620
private RBM.BA.EKGenBAInst.inst_lam_ratio_pos  622-625
private RBM.BA.EKGenBAInst.inst_lam_ratio_le_one  627-634
private RBM.BA.EKGenBAInst.inst_thr  636-647
### RBM3D.BA.EKNonzero  (10 unreached of 21)
private RBM.BA.EKNonzero_coef  167-186
private RBM.BA.EKNonzero_norm_projMat_mul_uKer_le  188-252
RBM.BA.baEKSumDecayNonzero_holds  258-300
RBM.BA.EKNonzeroInst.window_s  312-315
RBM.BA.EKNonzeroInst.window_st  317-323
RBM.BA.EKNonzeroInst.window_t  325-328
RBM.BA.EKNonzeroInst.AI3  330-331
RBM.BA.EKNonzeroInst.AI3_zero  333-333
RBM.BA.EKNonzeroInst.inst_baEKSumDecayNonzero_n2  335-342
RBM.BA.EKNonzeroInst.inst_baEKSumDecayNonzero_n3  344-353
### RBM3D.BA.EKPins  (33 unreached of 60)
RBM.BA.BAEKSumDecayNonzero  133-139
RBM.BA.EKPinsInst.gI  642-643
RBM.BA.EKPinsInst.EI  644-644
RBM.BA.EKPinsInst.mI  645-645
RBM.BA.EKPinsInst.AI  647-648
RBM.BA.EKPinsInst.AI_zero  650-650
RBM.BA.EKPinsInst.gI_pos  652-654
RBM.BA.EKPinsInst.gI_le  656-663
RBM.BA.EKPinsInst.LI_real  665-665
RBM.BA.EKPinsInst.hrI  667-668
RBM.BA.EKPinsInst.gI_sq_le  670-676
RBM.BA.EKPinsInst.AI_fastDecay  678-687
RBM.BA.EKPinsInst.inst_baEKSumNdecay  689-693
RBM.BA.EKPinsInst.ballI  695-696
RBM.BA.EKPinsInst.zero_mem_ballI  698-698
RBM.BA.EKPinsInst.ballI_dist  700-701
RBM.BA.EKPinsInst.inst_baEKXiDecay  703-710
RBM.BA.EKPinsInst.inst_baEKXiBall  712-719
RBM.BA.EKPinsInst.inst_baEKSameRow  722-727
RBM.BA.EKPinsInst.sixteen_rpow_half  729-731
RBM.BA.EKPinsInst.half_le_one_sub  733-735
RBM.BA.EKPinsInst.inst_BAEKSumDecay1  737-745
RBM.BA.EKPinsInst.inst_BAEKSumDecayNAL  747-754
RBM.BA.EKPinsInst.inst_BAEKSumDecayNonzero  756-769
RBM.BA.EKPinsInst.eI  773-774
RBM.BA.EKPinsInst.AzI  776-778
RBM.BA.EKPinsInst.zdistD_eI  780-784
RBM.BA.EKPinsInst.zero_ne_eI  786-790
RBM.BA.EKPinsInst.AzI_vals  792-793
RBM.BA.EKPinsInst.AzI_fastDecay  795-819
RBM.BA.EKPinsInst.AzI_sumZero  821-835
RBM.BA.EKPinsInst.log_le_half  837-840
RBM.BA.EKPinsInst.inst_BAEKSumDecay2  842-850
### RBM3D.BA.EKSum  (4 unreached of 36)
RBM.BA.baEKSumDecay1_holds  198-285
RBM.BA.EKSumInst.inst_baEKSumDecay1  1906-1911
RBM.BA.EKSumInst.inst_baEKSumDecayNAL  1913-1917
RBM.BA.EKSumInst.inst_baEKSumDecay2  1919-1923
### RBM3D.BA.EMCTE2BA  (23 unreached of 41)
RBM.Univ.jakUywRowk  627-637
RBM.Univ.UNBulkWindowk_band  660-667
RBM.Univ.UNBadBoundk_band  669-673
RBM.Univ.UNBad2Boundk_band  675-679
RBM.Univ.unJakUywRowBA_holds  763-767
RBM.Univ.EMCTE2BAInst.lamPsi0  796-798
RBM.Univ.EMCTE2BAInst.lamPsi0_herm  800-800
RBM.Univ.EMCTE2BAInst.zI_pos  802-802
RBM.Univ.EMCTE2BAInst.inst_translate  804-808
RBM.Univ.EMCTE2BAInst.inst_wirtSecond_translate  810-817
RBM.Univ.EMCTE2BAInst.inst_eq225_intervalShift  819-857
RBM.Univ.EMCTE2BAInst.inst_unEMCTE2k_ba_sz0  859-861
RBM.Univ.EMCTE2BAInst.inst_unEMCTE2Rowk_ba  863-867
RBM.Univ.EMCTE2BAInst.inst_unJak_k_band  869-876
RBM.Univ.EMCTE2BAInst.inst_unUyw_k_band  878-884
RBM.Univ.EMCTE2BAInst.inst_unJak_unUyw_band_recover  886-895
RBM.Univ.EMCTE2BAInst.inst_jakUywRowk_band  897-906
RBM.Univ.EMCTE2BAInst.inst_unJak_k_ba  908-914
RBM.Univ.EMCTE2BAInst.inst_unUyw_k_ba  916-921
RBM.Univ.EMCTE2BAInst.inst_bulk_window_ba  923-928
RBM.Univ.EMCTE2BAInst.inst_bad_ba  930-939
RBM.Univ.EMCTE2BAInst.inst_unJakUywRowBA  941-947
RBM.Univ.EMCTE2BAInst.inst_univ_ba_rows  949-956
### RBM3D.BA.EMn2BA  (11 unreached of 41)
RBM.BA.BAEMn2ExpJ  757-770
RBM.BA.baSTEMn2ExpJ  772-774
RBM.BA.BAContractAt  790-805
RBM.BA.EMn2BA_contract_iff  807-810
RBM.BA.baSTContractM  812-819
RBM.BA.baSTContractM_flow  821-829
private RBM.BA.EMn2BAInst.EMn2BAInst_ellT_le  906-921
private RBM.BA.EMn2BAInst.EMn2BAInst_far_ev  923-949
private RBM.BA.EMn2BAInst.EMn2BAInst_zdistInf  951-964
private RBM.BA.EMn2BAInst.EMn2BAInst_logW  1000-1012
private RBM.BA.EMn2BAInst.EMn2BAInst_ell_range  1014-1020
### RBM3D.BA.FlowPins  (76 unreached of 110)
RBM.BA.BASelfFine  57-60
RBM.BA.BAfine_trace  114-137
RBM.BA.BASelf_iff_fine  139-153
RBM.BA.BAGM  303-306
RBM.BA.bandFM_STLK  331-334
RBM.BA.bandFM_STLmax  335-336
RBM.BA.bandFM_STDecay  337-338
RBM.BA.bandFM_STDecayStrong  339-340
RBM.BA.bandFM_STLocalMax  341-342
RBM.BA.bandFM_STLocalEntry  343-344
RBM.BA.bandFM_STExp2  345-346
RBM.BA.bandFM_STInitialGT2  347-348
RBM.BA.bandFM_STStep1Loop  351-352
RBM.BA.bandFM_STStep1Weak  353-354
RBM.BA.bandFM_STLWassmExp  355-356
RBM.BA.bandFM_STEEk  357-360
RBM.BA.BAConArgLoop  446-455
RBM.BA.BAConArg'  472-484
RBM.BA.STStep1_iff  490-501
RBM.BA.BArho_eq_zero_of_gt  741-746
private RBM.BA.FlowPins_BAmF_flow  760-766
private RBM.BA.FlowPins_BAmF_flow_im  768-772
private RBM.BA.FlowPins_BAmF_flow_im_pos  774-779
private RBM.BA.FlowPins_zim_pos  781-788
RBM.BA.BAConArg'_premise_diag  790-808
private RBM.BA.BAConArg  824-832
private RBM.BA.FlowPins_Gres_false  834-842
private RBM.BA.FlowPins_Gii_im_pos  844-856
private RBM.BA.FlowPins_trace_GDGD  858-870
private RBM.BA.FlowPins_loop2_pos  872-922
private RBM.BA.FlowPins_seqHflowBA_herm  924-931
RBM.BA.not_BAConArg_of_data  933-979
RBM.BA.FlowPinsInst.im_I_add_m  996-1000
RBM.BA.FlowPinsInst.inst_kron  1002-1006
RBM.BA.FlowPinsInst.inst_apply  1008-1013
RBM.BA.FlowPinsInst.inst_apply_concrete  1015-1029
RBM.BA.FlowPinsInst.inst_trace  1031-1035
RBM.BA.FlowPinsInst.inst_selfFine  1037-1039
RBM.BA.FlowPinsInst.inst_selfFine_real  1041-1043
RBM.BA.FlowPinsInst.inst_kron_real  1045-1049
RBM.BA.FlowPinsInst.zd_a  1057-1058
RBM.BA.FlowPinsInst.zd_r  1059-1060
RBM.BA.FlowPinsInst.inst_BAProp5  1062-1068
RBM.BA.FlowPinsInst.inst_BAProp5s  1070-1076
RBM.BA.FlowPinsInst.inst_BAProp6  1078-1087
RBM.BA.FlowPinsInst.inst_BAProp7  1089-1099
RBM.BA.FlowPinsInst.inst_BAProp8  1101-1106
private RBM.BA.FlowPinsInst.FlowPins_wI_im  1117-1117
private RBM.BA.FlowPinsInst.FlowPins_mS_im_lower  1119-1121
private RBM.BA.FlowPinsInst.FlowPins_mS_im_upper  1123-1124
private RBM.BA.FlowPinsInst.FlowPins_zS_add_mS_im  1126-1128
RBM.BA.FlowPinsInst.sz0_lam_L  1130-1143
RBM.BA.FlowPinsInst.mS_im_half  1145-1150
RBM.BA.FlowPinsInst.size_ge  1152-1165
RBM.BA.FlowPinsInst.size_rpow_le  1167-1178
RBM.BA.FlowPinsInst.zSeq  1180-1181
RBM.BA.FlowPinsInst.sz0_lam_pos  1183-1186
RBM.BA.FlowPinsInst.BAm_zSeq  1188-1194
RBM.BA.FlowPinsInst.zSeq_im_le  1196-1202
RBM.BA.FlowPinsInst.zSeq_im_ge  1204-1211
RBM.BA.FlowPinsInst.flow_sz0  1213-1223
RBM.BA.FlowPinsInst.t0_sz0  1225-1236
RBM.BA.FlowPinsInst.inst_BAConArg'  1244-1251
RBM.BA.FlowPinsInst.half_lt_t0  1253-1256
RBM.BA.FlowPinsInst.zSeq_im_pos  1260-1261
RBM.BA.FlowPinsInst.BAmF_sz0_eq  1263-1267
RBM.BA.FlowPinsInst.BAmF_sz0_im_pos  1269-1271
RBM.BA.FlowPinsInst.BAMfine_sz0_kron  1273-1284
RBM.BA.FlowPinsInst.inst_premise_diag  1287-1290
RBM.BA.FlowPinsInst.inst_none_pos  1296-1297
RBM.BA.FlowPinsInst.inst_none_neg  1299-1300
RBM.BA.FlowPinsInst.inst_BAm_zero  1302-1302
RBM.BA.FlowPinsInst.inst_BArho_zero  1304-1304
RBM.BA.FlowPinsInst.inst_flowPt_inside  1306-1309
RBM.BA.FlowPinsInst.svarF_ne_zero_profile  1371-1393
RBM.BA.FlowPinsInst.seqGvar_ne_withLam_zero  1395-1425
### RBM3D.BA.GUEDuhamelBA  (31 unreached of 60)
RBM.BA.GUEDuhamelBA_Phi  620-625
RBM.BA.GUEDuhamelBA_Zinc  627-631
RBM.BA.GUEDuhamelBA_Yst  633-643
RBM.BA.GUEDuhamelBA_r  645-655
RBM.BA.Duhamel_step_decompBA  657-674
RBM.BA.GUEDuhamelBA_Vp  765-771
RBM.BA.GUEDuhamelBA_Zst  773-779
RBM.BA.Duhamel_azuma_ZBA  781-791
RBM.BA.Duhamel_azuma_YBA  793-806
RBM.BA.GUEDuhamelBAInst.gI  826-827
RBM.BA.GUEDuhamelBAInst.EI  828-828
RBM.BA.GUEDuhamelBAInst.mI  829-829
RBM.BA.GUEDuhamelBAInst.t1I  830-830
RBM.BA.GUEDuhamelBAInst.t0I  831-831
RBM.BA.GUEDuhamelBAInst.KI  832-832
RBM.BA.GUEDuhamelBAInst.real_I  834-835
RBM.BA.GUEDuhamelBAInst.im_pos_I  837-837
RBM.BA.GUEDuhamelBAInst.norm_le_I  839-840
RBM.BA.GUEDuhamelBAInst.loop2  842-843
RBM.BA.GUEDuhamelBAInst.loop2_wf  845-845
RBM.BA.GUEDuhamelBAInst.Duhamel_step_decompBA_check  847-864
RBM.BA.GUEDuhamelBAInst.Duhamel_drift_remainder_aeBA_check  866-882
RBM.BA.GUEDuhamelBAInst.KI1  884-885
RBM.BA.GUEDuhamelBAInst.hv_I  887-889
RBM.BA.GUEDuhamelBAInst.hv_I1  891-893
RBM.BA.GUEDuhamelBAInst.Duhamel_azuma_ZBA_check  895-902
RBM.BA.GUEDuhamelBAInst.bI  904-909
RBM.BA.GUEDuhamelBAInst.eta_pos_I1  911-915
RBM.BA.GUEDuhamelBAInst.bI_nonneg  917-922
RBM.BA.GUEDuhamelBAInst.hb_I  924-934
RBM.BA.GUEDuhamelBAInst.Duhamel_azuma_YBA_check  936-944
### RBM3D.BA.GUEDuhamelBA2  (2 unreached of 13)
RBM.BA.GUEDuhamelBAInst.hscale_I  1003-1029
RBM.BA.GUEDuhamelBAInst.gueGrid_loop_duhamelBA_check  1031-1054
### RBM3D.BA.GUEEntry2  (24 unreached of 48)
RBM.BA.GUEEntry_mixMatBA_isHermitian  459-464
RBM.BA.gueEntryMixBA  910-918
private RBM.BA.GUEEntryInst_h310  942-942
private RBM.BA.GUEEntryInst_BAMB_le_one  944-952
private RBM.BA.GUEEntryInst_c0  1026-1032
private RBM.BA.GUEEntryInst_dlt  1034-1038
private RBM.BA.GUEEntryInst_cs  1040-1043
private RBM.BA.n₁  1048-1048
private RBM.BA.g₁  1049-1049
private RBM.BA.E₁  1050-1050
private RBM.BA.m₁  1051-1051
private RBM.BA.GUEEntryInst_real  1053-1054
private RBM.BA.GUEEntryInst_g  1056-1062
private RBM.BA.GUEEntryInst_wd  1064-1065
private RBM.BA.H₁  1067-1069
private RBM.BA.z₁  1070-1070
private RBM.BA.S₁  1071-1072
private RBM.BA.GUEEntryInst_expC_ge_one  1245-1252
private RBM.BA.GUEEntryInst_consts  1254-1286
private RBM.BA.GUEEntryInst_core  1290-1441
private RBM.BA.GUEEntryInst_prof  1443-1458
private RBM.BA.GUEEntryInst_SBR_le  1460-1462
private RBM.BA.GUEEntryInst_zero_obstr  1464-1527
private RBM.BA.GUEEntryInst_zero_obstr_vtx  1529-1582
### RBM3D.BA.GUEEntryGridBA  (2 unreached of 17)
RBM.BA.gueGrid_entry_boundBA  379-402
private RBM.BA.GUEEntryGridBAInst.GUEEntryGridBAInst_data  416-427
### RBM3D.BA.GUEEq729BA  (26 unreached of 52)
private RBM.BA.GUEEq729BA_hdrift_int  714-728
private RBM.BA.GUEEq729BAInst.gI  1120-1120
private RBM.BA.GUEEq729BAInst.EI  1121-1121
private RBM.BA.GUEEq729BAInst.mI  1122-1122
private RBM.BA.GUEEq729BAInst.t1I  1123-1123
private RBM.BA.GUEEq729BAInst.t0I  1124-1124
private RBM.BA.GUEEq729BAInst.KI  1125-1125
private RBM.BA.GUEEq729BAInst.im_ge  1127-1127
private RBM.BA.GUEEq729BAInst.im_pos  1129-1129
private RBM.BA.GUEEq729BAInst.norm_le  1131-1131
private RBM.BA.GUEEq729BAInst.im_le  1133-1133
private RBM.BA.GUEEq729BAInst.grid_lt  1135-1137
private RBM.BA.GUEEq729BAInst.loop2  1139-1140
private RBM.BA.GUEEq729BAInst.loop2_wf  1142-1142
RBM.BA.GUEEq729BAInst.oneStepEnvelopeGUEOf_check  1144-1162
RBM.BA.GUEEq729BAInst.condExp_loop_step_gueBA_check  1164-1176
RBM.BA.GUEEq729BAInst.condExp_loop_drift_gueBA_check  1178-1193
RBM.BA.GUEEq729BAInst.eq729_eG2BA_check  1195-1212
RBM.BA.GUEEq729BAInst.eq729_duhamelBA_check  1214-1232
private RBM.BA.GUEEq729BAInst.size0  1234-1236
private RBM.BA.GUEEq729BAInst.ΛI  1238-1239
private RBM.BA.GUEEq729BAInst.eta_t0  1241-1242
private RBM.BA.GUEEq729BAInst.Λ_le_one  1244-1246
private RBM.BA.GUEEq729BAInst.Λ_ge  1248-1253
private RBM.BA.GUEEq729BAInst.hBk_inst  1255-1281
RBM.BA.GUEEq729BAInst.eq729_one_stepBA_check  1283-1306
### RBM3D.BA.GUEHyp  (46 unreached of 75)
RBM.BA.baEq729_Kdisc  978-994
private RBM.BA.GUEHyp_kTwo_le  996-1042
private RBM.BA.GUEHypInst.hg  1076-1076
private RBM.BA.GUEHypInst.E0  1078-1078
private RBM.BA.GUEHypInst.g0  1079-1079
private RBM.BA.GUEHypInst.g0_pos  1081-1081
private RBM.BA.GUEHypInst.g0_le  1082-1082
private RBM.BA.GUEHypInst.flowS0  1084-1091
private RBM.BA.GUEHypInst.κI  1093-1093
private RBM.BA.GUEHypInst.cI  1094-1094
private RBM.BA.GUEHypInst.cTI  1095-1095
private RBM.BA.GUEHypInst.flowS0_spec  1097-1099
private RBM.BA.GUEHypInst.GUEHyp_scale_ev  1101-1116
private RBM.BA.GUEHypInst.etaI  1118-1119
private RBM.BA.GUEHypInst.etaI_pos  1121-1122
private RBM.BA.GUEHypInst.etaI_le  1124-1128
private RBM.BA.GUEHypInst.g0sq_le  1130-1130
private RBM.BA.GUEHypInst.etaI_le_one  1132-1132
private RBM.BA.GUEHypInst.zI  1134-1135
private RBM.BA.GUEHypInst.fI  1137-1138
private RBM.BA.GUEHypInst.fI_eq  1140-1140
private RBM.BA.GUEHypInst.zI_im  1142-1142
private RBM.BA.GUEHypInst.fI_facts  1144-1149
private RBM.BA.GUEHypInst.fI_pos  1151-1151
private RBM.BA.GUEHypInst.sqrt_fI_le  1153-1153
private RBM.BA.GUEHypInst.t1I  1155-1156
private RBM.BA.GUEHypInst.Nsz_S0_one  1158-1158
private RBM.BA.GUEHypInst.off_bounds  1160-1169
private RBM.BA.GUEHypInst.t1I_nonneg  1171-1173
private RBM.BA.GUEHypInst.t1I_le  1175-1177
private RBM.BA.GUEHypInst.hellI  1179-1182
private RBM.BA.GUEHypInst.hell1I  1184-1185
private RBM.BA.GUEHypInst.tauU_pos  1214-1214
private RBM.BA.GUEHypInst.zQ  1216-1216
private RBM.BA.GUEHypInst.tQ  1218-1218
private RBM.BA.GUEHypInst.tQ_ok  1220-1221
private RBM.BA.GUEHypInst.zQ_im  1223-1228
private RBM.BA.GUEHypInst.zQ_ev  1230-1233
private RBM.BA.GUEHypInst.hgoodQ  1235-1242
private RBM.BA.GUEHypInst.xI  1291-1291
private RBM.BA.GUEHypInst.t0S  1292-1292
private RBM.BA.GUEHypInst.t1S  1293-1293
private RBM.BA.GUEHypInst.xI_pos  1295-1295
private RBM.BA.GUEHypInst.xI_le  1296-1296
private RBM.BA.GUEHypInst.t1S_bounds  1298-1310
private RBM.BA.GUEHypInst.etaOf_S  1312-1313
### RBM3D.BA.GUEHypABA  (37 unreached of 45)
private RBM.BA.GUEHypABAInst.ig  657-657
private RBM.BA.GUEHypABAInst.iE  658-658
private RBM.BA.GUEHypABAInst.im  659-659
private RBM.BA.GUEHypABAInst.iN  660-660
private RBM.BA.GUEHypABAInst.ix  661-661
private RBM.BA.GUEHypABAInst.it0  662-662
private RBM.BA.GUEHypABAInst.it1  663-663
private RBM.BA.GUEHypABAInst.GUEHypABAInst_real  665-666
private RBM.BA.GUEHypABAInst.GUEHypABAInst_L  668-671
private RBM.BA.GUEHypABAInst.GUEHypABAInst_N  673-674
private RBM.BA.GUEHypABAInst.GUEHypABAInst_x_pos  676-679
private RBM.BA.GUEHypABAInst.GUEHypABAInst_x_le  681-690
private RBM.BA.GUEHypABAInst.GUEHypABAInst_t0  692-698
private RBM.BA.GUEHypABAInst.GUEHypABAInst_t1_nonneg  700-706
private RBM.BA.GUEHypABAInst.GUEHypABAInst_t10  708-712
private RBM.BA.GUEHypABAInst.GUEHypABAInst_t0_lt  714-715
private RBM.BA.GUEHypABAInst.GUEHypABAInst_g_pos  717-720
private RBM.BA.GUEHypABAInst.GUEHypABAInst_hell  722-740
private RBM.BA.GUEHypABAInst.GUEHypABAInst_h730  742-756
private RBM.BA.GUEHypABAInst.GUEHypABAInst_K  758-771
private RBM.BA.GUEHypABAInst.X2  810-810
private RBM.BA.GUEHypABAInst.uj  811-811
private RBM.BA.GUEHypABAInst.Hj  812-812
private RBM.BA.GUEHypABAInst.Lj  813-814
private RBM.BA.GUEHypABAInst.scj  815-815
private RBM.BA.GUEHypABAInst.AMj  816-818
private RBM.BA.GUEHypABAInst.AFj  819-821
private RBM.BA.GUEHypABAInst.AEj  822-823
private RBM.BA.GUEHypABAInst.ADj  824-826
private RBM.BA.GUEHypABAInst.Qj  827-829
private RBM.BA.GUEHypABAInst.GUEHypABAInst_dsum  831-836
private RBM.BA.GUEHypABAInst.GUEHypABAInst_scj_pos  838-842
private RBM.BA.GUEHypABAInst.S0  844-845
private RBM.BA.GUEHypABAInst.c0  846-847
private RBM.BA.GUEHypABAInst.GUEHypABAInst_AMsc_nonneg  849-850
private RBM.BA.GUEHypABAInst.GUEHypABAInst_S0_nonneg  852-853
private RBM.BA.GUEHypABAInst.GUEHypABAInst_c0_nonneg  855-858
### RBM3D.BA.GUEHypBBA  (20 unreached of 46)
private RBM.BA.HypBBA_Gres_true  90-93
private RBM.BA.GUEHypBBAInst.jg  1233-1233
private RBM.BA.GUEHypBBAInst.jE  1234-1234
private RBM.BA.GUEHypBBAInst.jm  1235-1235
private RBM.BA.GUEHypBBAInst.jt0  1236-1236
private RBM.BA.GUEHypBBAInst.jt1  1237-1237
private RBM.BA.GUEHypBBAInst.jreal  1239-1240
private RBM.BA.GUEHypBBAInst.jim  1242-1242
private RBM.BA.GUEHypBBAInst.jnorm  1244-1245
private RBM.BA.GUEHypBBAInst.jN  1247-1247
private RBM.BA.GUEHypBBAInst.j_le_rpow  1249-1257
private RBM.BA.GUEHypBBAInst.j_eta  1259-1261
private RBM.BA.GUEHypBBAInst.j_scale  1263-1264
private RBM.BA.GUEHypBBAInst.j_hscN  1266-1277
private RBM.BA.GUEHypBBAInst.j_h730  1279-1289
private RBM.BA.GUEHypBBAInst.j_hellN  1291-1292
private RBM.BA.GUEHypBBAInst.j_hsmallN  1294-1299
private RBM.BA.GUEHypBBAInst.j_h4N  1301-1306
private RBM.BA.GUEHypBBAInst.j_hbig  1308-1314
private RBM.BA.GUEHypBBAInst.j_delta  1316-1323
### RBM3D.BA.GUEKPrim  (6 unreached of 45)
RBM.BA.baThetaTilde_osc  536-558
RBM.Univ.UNOUProfile.ba_zero  607-625
private RBM.BA.GUEKPrimInst.hg  1132-1132
RBM.BA.GUEKPrimInst.zS0  1134-1135
private RBM.BA.GUEKPrimInst.S0_win  1137-1142
private RBM.BA.GUEKPrimInst.fp_im_pos  1144-1144
### RBM3D.BA.GUELLBA  (1 unreached of 15)
private RBM.BA.GUELLBAInst.hg  368-368
### RBM3D.BA.GUEOneLoop  (8 unreached of 31)
RBM.BA.gueGrid_expect_oneLoopBA  1272-1308
private RBM.BA.GUEOneLoopInst.GUEOneLoopInst_window  1322-1329
private RBM.BA.GUEOneLoopInst.GUEOneLoopInst_σ  1348-1349
private RBM.BA.GUEOneLoopInst.GUEOneLoopInst_c0  1351-1351
private RBM.BA.GUEOneLoopInst.GUEOneLoopInst_hL  1353-1354
private RBM.BA.GUEOneLoopInst.GUEOneLoopInst_hσ  1356-1360
private RBM.BA.GUEOneLoopInst.GUEOneLoopInst_hu  1362-1366
private RBM.BA.GUEOneLoopInst.GUEOneLoopInst_nonneg  1368-1374
### RBM3D.BA.GUEPathBoundsBA  (5 unreached of 14)
private RBM.BA.GUEPathBoundsBAInst.j_Nx  655-667
private RBM.BA.GUEPathBoundsBAInst.j_hell  669-680
private RBM.BA.GUEPathBoundsBAInst.j_hell1  682-691
private RBM.BA.GUEPathBoundsBAInst.j_hscale  693-724
private RBM.BA.GUEPathBoundsBAInst.j_data  726-733
### RBM3D.BA.GUEProcBA  (2 unreached of 28)
private RBM.BA.GUEProcBAInst.GUEProcBAInst_flow  532-537
private RBM.BA.GUEProcBAInst.GUEProcBAInst_real  569-572
### RBM3D.BA.GUETwistBA  (1 unreached of 103)
RBM.BA.GUETwistBA_Pi_apply  66-67
### RBM3D.BA.GUETwistBA2  (23 unreached of 38)
RBM.BA.GUETwistBA_Kt_one  992-1014
RBM.BA.GUETwistBAInst.gI  1022-1024
RBM.BA.GUETwistBAInst.EI  1025-1025
RBM.BA.GUETwistBAInst.mI  1026-1026
private RBM.BA.GUETwistBAInst.NI  1027-1027
private RBM.BA.GUETwistBAInst.xI  1028-1028
RBM.BA.GUETwistBAInst.t0I  1029-1029
RBM.BA.GUETwistBAInst.t1I  1030-1030
RBM.BA.GUETwistBAInst.real_I  1032-1033
private RBM.BA.GUETwistBAInst.GUETwistBAInst_L  1035-1038
private RBM.BA.GUETwistBAInst.GUETwistBAInst_N  1040-1041
private RBM.BA.GUETwistBAInst.GUETwistBAInst_x_pos  1043-1046
private RBM.BA.GUETwistBAInst.GUETwistBAInst_x_le  1048-1057
private RBM.BA.GUETwistBAInst.GUETwistBAInst_t0  1059-1065
private RBM.BA.GUETwistBAInst.GUETwistBAInst_t1_nonneg  1067-1073
private RBM.BA.GUETwistBAInst.GUETwistBAInst_t10  1075-1079
private RBM.BA.GUETwistBAInst.GUETwistBAInst_t0_lt  1081-1082
private RBM.BA.GUETwistBAInst.GUETwistBAInst_g_pos  1084-1088
private RBM.BA.GUETwistBAInst.GUETwistBAInst_hell  1090-1111
private RBM.BA.GUETwistBAInst.GUETwistBAInst_h730  1113-1131
RBM.BA.GUETwistBAInst.KtI  1133-1136
private RBM.BA.GUETwistBAInst.GUETwistBAInst_KtI_spec  1138-1146
RBM.BA.GUETwistBAInst.twist_sz0  1148-1172
### RBM3D.BA.GreenCond  (12 unreached of 136)
RBM.BA.GreenCond_famA_eq  325-326
RBM.BA.GreenCond_famX_eq  328-329
RBM.BA.GreenCond_Env_nonneg  362-364
RBM.BA.GreenCond_sz0_eq  1236-1236
RBM.BA.GreenCond_Xc_rowSplit_off  1263-1279
RBM.BA.GreenCond_QX_nonneg  1807-1808
private RBM.BA.GreenCondInst_g0  1918-1919
private RBM.BA.GreenCondInst_Env  1935-1935
private RBM.BA.GreenCondInst_cM  1936-1936
private RBM.BA.GreenCondInst_δ  1937-1937
private RBM.BA.GreenCondInst_ε  1938-1938
private RBM.BA.GreenCondInst_G0  1940-1947
### RBM3D.BA.GreenCore  (40 unreached of 132)
private RBM.BA.GreenCoreInst.g₀  1687-1687
private RBM.BA.GreenCoreInst.E₀  1688-1688
private RBM.BA.GreenCoreInst.m₀  1689-1689
private RBM.BA.GreenCoreInst.Mb₀  1690-1690
private RBM.BA.GreenCoreInst.t₁  1691-1691
private RBM.BA.GreenCoreInst.ω₀  1692-1692
private RBM.BA.GreenCoreInst.G₁  1693-1693
private RBM.BA.GreenCoreInst.X₁  1694-1694
private RBM.BA.GreenCoreInst.M₁  1695-1695
private RBM.BA.GreenCoreInst.D₁  1696-1696
private RBM.BA.GreenCoreInst.s₀  1697-1697
private RBM.BA.GreenCoreInst.hreal  1698-1698
private RBM.BA.GreenCoreInst.hT0  1699-1699
private RBM.BA.GreenCoreInst.hg  1700-1705
private RBM.BA.GreenCoreInst.kern  1707-1726
private RBM.BA.GreenCoreInst.X0  1728-1733
private RBM.BA.GreenCoreInst.card4096  1734-1734
private RBM.BA.GreenCoreInst.cnt  1735-1736
private RBM.BA.GreenCoreInst.c0_lb  1737-1742
private RBM.BA.GreenCoreInst.Gbd  1743-1754
private RBM.BA.GreenCoreInst.iC  1756-1757
private RBM.BA.GreenCoreInst.iCh  1758-1758
private RBM.BA.GreenCoreInst.iC1  1759-1759
private RBM.BA.GreenCoreInst.lde_zero  1761-1791
private RBM.BA.GreenCoreInst.om_gen  1793-1813
private RBM.BA.GreenCoreInst.Om  1814-1817
private RBM.BA.GreenCoreInst.hW  1818-1818
private RBM.BA.GreenCoreInst.iwd  1819-1819
private RBM.BA.GreenCoreInst.iLDE  1820-1826
private RBM.BA.GreenCoreInst.icr  1828-1831
private RBM.BA.GreenCoreInst.loop_le  1833-1837
private RBM.BA.GreenCoreInst.stab_small  1839-1855
private RBM.BA.GreenCoreInst.istab  1856-1859
private RBM.BA.GreenCoreInst.istabBA  1861-1862
private RBM.BA.GreenCoreInst.iC1n  1863-1874
private RBM.BA.GreenCoreInst.c0pos  1875-1875
private RBM.BA.GreenCoreInst.iρ  1876-1876
private RBM.BA.GreenCoreInst.iS  1877-1879
private RBM.BA.GreenCoreInst.K_gen  1881-1900
private RBM.BA.GreenCoreInst.iΔ  1902-1912
### RBM3D.BA.GreenLDE  (5 unreached of 13)
private RBM.BA.GreenLDE_ae_coord_zero  129-138
private RBM.BA.GreenLDE_svarF_zero_off_block  140-144
private RBM.BA.GreenLDE_gvar_off_block  146-154
private RBM.BA.GreenLDE_Xentry_zero  156-164
RBM.BA.GreenLDE_BAX_ae_block_support  166-184
### RBM3D.BA.GreenLocal  (13 unreached of 44)
RBM.BA.GreenLocal_LocalLaw  53-63
private RBM.BA.GreenLocal_prec_of_whp  155-166
private RBM.BA.GreenLocal_le_of_sq_le  168-171
private RBM.BA.GreenLocal_sqrt_rpow  173-175
private RBM.BA.GreenLocal_ev_incl  202-215
RBM.BA.greenLocal_omega  231-240
RBM.BA.greenLocal_localLaw  548-577
RBM.BA.greenLocal_floor  579-607
RBM.BA.greenLocal_gii_of_le  757-763
RBM.BA.GreenLocal_IBPPrem  765-778
RBM.BA.greenLocal_ibp_premises  780-784
private RBM.BA.GreenLocalInst.Ψ0  810-811
private RBM.BA.GreenLocalInst.δ0  812-813
### RBM3D.BA.GreenMinor  (16 unreached of 35)
RBM.BA.GreenMinor_removal  84-93
RBM.BA.GreenMinor_removal_crossL  101-111
RBM.BA.GreenMinor_removal_crossR  113-124
RBM.BA.GreenMinor_removal_cross  126-138
RBM.BA.GreenMinorInst.HV  342-342
RBM.BA.GreenMinorInst.hp  343-344
RBM.BA.GreenMinorInst.hq  345-346
RBM.BA.GreenMinorInst.hm  347-348
RBM.BA.GreenMinorInst.hε  349-350
RBM.BA.GreenMinorInst.hMb  351-352
RBM.BA.GreenMinorInst.hM  353-353
RBM.BA.GreenMinorInst.hΔ  354-354
RBM.BA.GreenMinorInst.hG  355-356
RBM.BA.GreenMinorInst.hD  357-358
RBM.BA.GreenMinorInst.hy  359-360
RBM.BA.GreenMinorInst.hΔ_herm  362-369
### RBM3D.BA.GreenMinor2  (34 unreached of 45)
RBM.BA.GreenMinor_split_A  261-271
RBM.BA.GreenMinor_split_X  273-285
RBM.BA.GreenMinorInst.hpq  385-385
RBM.BA.GreenMinorInst.hqp  386-386
RBM.BA.GreenMinorInst.hm0  387-387
RBM.BA.GreenMinorInst.hc  389-390
RBM.BA.GreenMinorInst.hc_ne  392-396
RBM.BA.GreenMinorInst.hMe  398-401
RBM.BA.GreenMinorInst.hΔb  403-408
RBM.BA.GreenMinorInst.hgS  410-414
RBM.BA.GreenMinorInst.hGs  416-416
RBM.BA.GreenMinorInst.hTower  418-479
RBM.BA.GreenMinorInst.hpy  490-490
RBM.BA.GreenMinorInst.hqy  491-491
RBM.BA.GreenMinorInst.hC  493-494
RBM.BA.GreenMinorInst.hC_card  496-500
RBM.BA.GreenMinorInst.hJ  502-503
RBM.BA.GreenMinorInst.hJJ  505-512
RBM.BA.GreenMinorInst.hH  514-515
RBM.BA.GreenMinorInst.hcc  517-518
RBM.BA.GreenMinorInst.hGex  520-521
RBM.BA.GreenMinorInst.hH_herm  523-530
RBM.BA.GreenMinorInst.hden  532-535
RBM.BA.GreenMinorInst.hcc_eq  537-540
RBM.BA.GreenMinorInst.hGex_mul  542-550
RBM.BA.GreenMinorInst.green_hH  552-554
RBM.BA.GreenMinorInst.hGex_sub  556-559
RBM.BA.GreenMinorInst.hcc_norm  561-571
RBM.BA.GreenMinorInst.hcc_ne  573-575
RBM.BA.GreenMinorInst.hGΔ  577-581
private RBM.BA.c_g₀  650-650
private RBM.BA.c_E₀  651-651
private RBM.BA.c_m₀  652-652
private RBM.BA.c_s₀  653-653
### RBM3D.BA.GreenMinor3  (7 unreached of 60)
RBM.BA.GreenMinor_avg_const  66-71
RBM.BA.GreenMinor_avgK_eq  82-105
RBM.BA.GreenMinor_a_zero  222-222
RBM.BA.GreenMinor_lev_union  330-332
private RBM.BA.c_g₀  883-883
private RBM.BA.c_E₀  884-884
private RBM.BA.c_m₀  885-885
### RBM3D.BA.GreenOff  (27 unreached of 88)
private RBM.BA.GreenOffInst.W₁  1376-1376
private RBM.BA.GreenOffInst.instNeZeroNatW₁  1377-1377
private RBM.BA.GreenOffInst.W₁_ge  1378-1378
private RBM.BA.GreenOffInst.δ₁  1379-1379
private RBM.BA.GreenOffInst.Mb₁  1380-1380
private RBM.BA.GreenOffInst.M₁  1381-1381
private RBM.BA.GreenOffInst.Δ₁  1382-1382
private RBM.BA.GreenOffInst.𝔛₁  1383-1383
private RBM.BA.GreenOffInst.D₁  1384-1384
private RBM.BA.GreenOffInst.Θ₁  1385-1385
private RBM.BA.GreenOffInst.Mb₁_apply  1387-1387
private RBM.BA.GreenOffInst.hΔ₁  1389-1391
private RBM.BA.GreenOffInst.hM₁  1393-1394
private RBM.BA.GreenOffInst.hT₁  1396-1406
private RBM.BA.GreenOffInst.hX₁  1408-1425
private RBM.BA.GreenOffInst.hXi₁  1427-1444
private RBM.BA.GreenOffInst.hdec₁  1446-1450
private RBM.BA.GreenOffInst.hS₁  1452-1455
private RBM.BA.GreenOffInst.hvb₁  1457-1460
private RBM.BA.GreenOffInst.hE3₁  1462-1467
private RBM.BA.GreenOffInst.hA₁  1469-1472
private RBM.BA.GreenOffInst.hD₁  1474-1474
private RBM.BA.GreenOffInst.hD1₁  1476-1477
private RBM.BA.GreenOffInst.hDadj₁  1479-1482
private RBM.BA.GreenOffInst.hΘ₁  1484-1489
private RBM.BA.GreenOffInst.hΘw₁  1491-1495
private RBM.BA.GreenOffInst.hC2₁  1497-1511
### RBM3D.BA.GreenSchur  (39 unreached of 49)
RBM.BA.BAMfine_decay  122-135
private RBM.BA.GreenSchur_fibre_sum  159-169
RBM.BA.BAMfine_row_l1  171-190
RBM.BA.BAPsiI_inBlock  264-273
private RBM.BA.GreenSchur_sum_split2  275-288
RBM.BA.green_diag_split  290-331
RBM.BA.green_off_split  333-350
private RBM.BA.GreenSchurInst.GreenSchur_mF  364-366
private RBM.BA.GreenSchurInst.GreenSchur_hr  368-371
private RBM.BA.GreenSchurInst.GreenSchur_hm  373-375
private RBM.BA.GreenSchurInst.GreenSchur_hs  377-379
RBM.BA.GreenSchurInst.inst_row_l1  381-386
RBM.BA.GreenSchurInst.inst_Mfine_eq  388-395
RBM.BA.GreenSchurInst.inst_Mfine_norm  397-399
RBM.BA.GreenSchurInst.inst_Mfine_decay  401-406
RBM.BA.GreenSchurInst.inst_Mfine_row_l1  408-413
RBM.BA.GreenSchurInst.inst_Gt_sub_Mfine  415-424
RBM.BA.GreenSchurInst.inst_PsiI_inBlock  426-429
private RBM.BA.GreenSchurInst.GreenSchur_D2  431-432
private RBM.BA.GreenSchurInst.GreenSchur_D2_det  434-437
private RBM.BA.GreenSchurInst.GreenSchur_D2_G00  439-442
private RBM.BA.GreenSchurInst.GreenSchur_D2_hD  444-448
private RBM.BA.GreenSchurInst.GreenSchur_D2_hU  450-453
RBM.BA.GreenSchurInst.inst_green_diag  455-477
RBM.BA.GreenSchurInst.inst_green_off  479-490
private RBM.BA.GreenSchurInst.GreenSchur_szF  494-500
private RBM.BA.GreenSchurInst.GreenSchur_wF  502-502
private RBM.BA.GreenSchurInst.GreenSchur_wF_norm  504-507
private RBM.BA.GreenSchurInst.GreenSchur_wF_im  509-509
private RBM.BA.GreenSchurInst.GreenSchur_mF0  511-512
private RBM.BA.GreenSchurInst.GreenSchur_zF  514-514
private RBM.BA.GreenSchurInst.GreenSchur_sub  516-520
private RBM.BA.GreenSchurInst.GreenSchur_mim_lo  522-527
private RBM.BA.GreenSchurInst.GreenSchur_mim_hi  529-533
private RBM.BA.GreenSchurInst.GreenSchur_Am  535-537
private RBM.BA.GreenSchurInst.GreenSchur_size  539-539
RBM.BA.GreenSchurInst.inst_BAFlow  541-599
RBM.BA.GreenSchurInst.inst_flow_real  601-606
RBM.BA.GreenSchurInst.inst_flow_window  608-611
### RBM3D.BA.GreenStab  (19 unreached of 29)
RBM.BA.baM_rhohat  145-169
private RBM.BA.GreenStab_fibre_sum  173-183
RBM.BA.baMfine_rhohat  185-213
RBM.BA.GreenStabInst.g0I  332-332
RBM.BA.GreenStabInst.E0I  333-333
RBM.BA.GreenStabInst.m0I  334-334
private RBM.BA.GreenStabInst.g0I_pos  336-339
private RBM.BA.GreenStabInst.g0I_le  341-349
RBM.BA.GreenStabInst.hr0I  351-353
RBM.BA.GreenStabInst.vI  355-356
RBM.BA.GreenStabInst.vI_zero  358-358
private RBM.BA.GreenStabInst.Q_le_one  360-367
RBM.BA.GreenStabInst.inst_baStab  369-394
RBM.BA.GreenStabInst.inst_col_l1  396-401
RBM.BA.GreenStabInst.inst_rho2  403-406
RBM.BA.GreenStabInst.inst_rhohat  408-414
RBM.BA.GreenStabInst.inst_rhohat_fine  416-424
RBM.BA.GreenStabInst.inst_theta_weighted  426-432
RBM.BA.GreenStabInst.inst_theta_shift  434-438
### RBM3D.BA.GridDriftBA  (6 unreached of 28)
RBM.BA.baStep2Mat_imLeOne  79-83
RBM.BA.baGridDrift_ev  647-668
RBM.BA.baQVPropagated  670-674
RBM.BA.GridDriftBAInst.inst_real  689-692
RBM.BA.GridDriftBAInst.inst_lam0_pos  694-696
RBM.BA.GridDriftBAInst.inst_loopForm  698-701
### RBM3D.BA.GridGoodBA  (50 unreached of 53)
RBM.BA.baGridGood_of  54-101
RBM.BA.baGridGood_holds  103-109
private RBM.BA.GridGoodBA_envelope_ev  117-192
RBM.BA.baGridDrift_envelope  194-221
RBM.BA.baAzumaSubG  231-235
RBM.BA.baYMoments  237-244
RBM.BA.baAzumaProxy_subG_goodExit  246-262
private RBM.BA.GridGoodBA_norm_prod_two  280-293
private RBM.BA.GridGoodBA_norm_prod_one  295-305
private RBM.BA.GridGoodBA_BAMLoop_eq  307-330
private RBM.BA.GridGoodBA_chain  332-358
private RBM.BA.GridGoodBA_far_edge  360-413
private RBM.BA.GridGoodBA_norm_BAMB_le_one  421-429
private RBM.BA.GridGoodBA_norm_Ms  431-436
private RBM.BA.GridGoodBA_cs  438-445
private RBM.BA.GridGoodBA_decay  447-453
private RBM.BA.GridGoodBA_edge  455-457
private RBM.BA.GridGoodBA_edge_le_one  459-464
private RBM.BA.GridGoodBA_norm_pref  466-468
private RBM.BA.GridGoodBA_BAMLoop_one  470-478
private RBM.BA.GridGoodBA_BAMLoop_two  480-489
private RBM.BA.GridGoodBA_BAMLoop_far  491-513
private RBM.BA.GridGoodBA_LIM_init  576-588
private RBM.BA.GridGoodBA_KI_init  601-617
private RBM.BA.GridGoodBA_LIM_sub_KI  619-625
private RBM.BA.GridGoodBA_ee_a_list  635-639
private RBM.BA.GridGoodBA_eeX  641-643
private RBM.BA.GridGoodBA_eeY  645-647
private RBM.BA.GridGoodBA_ee_loop_two  649-699
private RBM.BA.GridGoodBA_STeeMg_init_le  707-737
private RBM.BA.GridGoodBA_diam_pair  745-755
private RBM.BA.GridGoodBA_exp_mono  757-764
private RBM.BA.GridGoodBA_ee_level  766-796
private RBM.BA.GridGoodBA_pref_le_one  798-801
private RBM.BA.GridGoodBA_dec  803-827
private RBM.BA.GridGoodBA_ee_far  829-884
private RBM.BA.GridGoodBA_STLKIMg_zero  894-899
private RBM.BA.GridGoodBA_STLKIMg_zero_cut  901-910
private RBM.BA.GridGoodBA_STksimLKMg_zero  912-924
private RBM.BA.GridGoodBA_STelklkMg_zero  926-938
private RBM.BA.GridGoodBA_STavgErrMg_zero  940-954
private RBM.BA.GridGoodBA_STegtMg_zero  956-964
private RBM.BA.GridGoodBA_LM_sub_K_zero  966-980
private RBM.BA.GridGoodBA_pos_d  990-1001
private RBM.BA.GridGoodBA_Bctl_lower  1003-1017
private RBM.BA.GridGoodBA_goodSet_n  1019-1135
private RBM.BA.GridGoodBA_exp_ev  1143-1164
private RBM.BA.GridGoodBA_W_tendsto  1166-1171
private RBM.BA.GridGoodBA_far_ev  1173-1225
RBM.BA.baGoodSetNg_init  1227-1252
### RBM3D.BA.GridMartBA  (3 unreached of 40)
private RBM.BA.GridMartBA_Kinst  685-686
private RBM.BA.GridMartBA_Kinst_ne  688-688
private RBM.BA.GridMartBA_Kinst_ge  690-691
### RBM3D.BA.GridRepTailBA  (13 unreached of 83)
RBM.BA.gridRepTailBA_stepZCN_re  671-674
RBM.BA.gridRepTailBA_stepZCN_im  676-679
RBM.BA.baStep2_filt_withLam  1066-1067
RBM.BA.GridRepTailBAInst.sI  1259-1260
RBM.BA.GridRepTailBAInst.tI  1262-1263
RBM.BA.GridRepTailBAInst.hsI  1265-1265
RBM.BA.GridRepTailBAInst.hstI  1267-1267
RBM.BA.GridRepTailBAInst.htI  1269-1269
RBM.BA.GridRepTailBAInst.hN1I  1271-1271
RBM.BA.GridRepTailBAInst.hεnI  1273-1277
RBM.BA.GridRepTailBAInst.CmI  1279-1280
RBM.BA.GridRepTailBAInst.inst_baGridWTail2  1303-1325
RBM.BA.GridRepTailBAInst.inst_baGridRepNAt2  1344-1381
### RBM3D.BA.ImmLower  (2 unreached of 26)
private RBM.BA.ImmLower_inv_norm_le  76-78
RBM.BA.baImmLower_holds  412-420
### RBM3D.BA.KBase  (7 unreached of 34)
RBM.BA.BAMLoop_le_two  78-98
RBM.BA.BAMLoop_witM  100-104
RBM.BA.BAMLoop_witness  106-117
RBM.BA.BAMLoop_witness_old  119-136
private RBM.BA.BAKBase_conj  275-292
RBM.BA.BATheta_conj  360-368
RBM.BA.KBaseInst.witM_symm  502-508
### RBM3D.BA.KBound  (2 unreached of 16)
RBM.BA.KBound_baKsol_ward  307-321
RBM.BA.inst_BAKbound  333-337
### RBM3D.BA.KCactus  (54 unreached of 105)
RBM.BA.BAMssOf_BAMsigma  53-55
RBM.BA.BAMssOf_isSymm  57-64
RBM.BA.BAThetaOf_BAMsigma  74-77
RBM.BA.BAThetaOf_isSymm  79-86
RBM.BA.BAslotStart_leaf  125-126
RBM.BA.BAslotStart_out  128-129
RBM.BA.BAslotStart_in  131-132
RBM.BA.BAslotNode_leaf  142-143
RBM.BA.BAslotNode_out  145-146
RBM.BA.BAslotNode_in  148-149
private RBM.BA.BAKCactus_succ_injective  277-294
RBM.BA.BAnextSlot_injective  389-391
RBM.BA.BAnextSlot_bijective  393-395
RBM.BA.BAnextSlotPerm  397-399
RBM.BA.BAnextSlot_sameCycle_iff  412-422
RBM.BA.BAMcharge_def  437-438
RBM.BA.BAGamma_eq  492-494
RBM.BA.BAGamma_of_mem_TSP  496-499
private RBM.BA.BAKCactus_gval_orient  647-659
RBM.BA.BACactusVal_orient  661-674
RBM.BA.BACactusVal_three_BAMLoop  760-778
private RBM.BA.KCactusInst.BAKCactus_F02  803-804
private RBM.BA.KCactusInst.BAKCactus_F13  806-807
private RBM.BA.KCactusInst.BAKCactus_F02set  862-862
private RBM.BA.KCactusInst.BAKCactus_F02mem  864-865
private RBM.BA.KCactusInst.BAKCactus_leafPar0  867-868
private RBM.BA.KCactusInst.BAKCactus_leafPar1  870-871
private RBM.BA.KCactusInst.BAKCactus_leafPar2  873-874
private RBM.BA.KCactusInst.BAKCactus_leafPar3  876-877
private RBM.BA.KCactusInst.BAKCactus_nodePar02  879-880
private RBM.BA.KCactusInst.BAKCactus_nodeM  882-886
private RBM.BA.KCactusInst.BAKCactus_nodeM_eq  888-901
private RBM.BA.KCactusInst.BAKCactus_nextM  903-909
private RBM.BA.KCactusInst.BAKCactus_tableM  911-918
private RBM.BA.KCactusInst.BAKCactus_next_eq  920-926
private RBM.BA.KCactusInst.BAKCactus_F13set  979-979
private RBM.BA.KCactusInst.BAKCactus_F13mem  981-982
private RBM.BA.KCactusInst.BAKCactus_leafPar13_0  984-985
private RBM.BA.KCactusInst.BAKCactus_leafPar13_1  987-988
private RBM.BA.KCactusInst.BAKCactus_leafPar13_2  990-991
private RBM.BA.KCactusInst.BAKCactus_leafPar13_3  993-994
private RBM.BA.KCactusInst.BAKCactus_nodePar13  996-997
private RBM.BA.KCactusInst.BAKCactus_nodeM13  999-1002
private RBM.BA.KCactusInst.BAKCactus_nodeM13_eq  1004-1017
private RBM.BA.KCactusInst.BAKCactus_nextM13  1019-1025
private RBM.BA.KCactusInst.BAKCactus_tableM13  1027-1035
private RBM.BA.KCactusInst.BAKCactus_next13_eq  1037-1043
private RBM.BA.KCactusInst.BAKCactus_Msym  1076-1085
private RBM.BA.KCactusInst.BAKCactus_Msh  1201-1202
private RBM.BA.KCactusInst.BAKCactus_Mss_zero  1204-1214
private RBM.BA.KCactusInst.BAKCactus_Theta_one  1216-1217
private RBM.BA.KCactusInst.BAKCactus_uniqueF02  1219-1220
private RBM.BA.KCactusInst.BAKCactus_card_F02  1223-1228
private RBM.BA.KCactusInst.BAKCactus_val_F02  1230-1251
### RBM3D.BA.KCactusCut  (1 unreached of 85)
private RBM.BA.KCactusCutInst.KCactusCut_isTSP_F02  1264-1266
### RBM3D.BA.KDecayBA  (6 unreached of 29)
RBM.BA.KDecayBAInst.inst_baKcalDecay  822-824
private RBM.BA.KDecayBAInst.instA  826-828
private RBM.BA.KDecayBAInst.instA_maxDist  830-841
private RBM.BA.KDecayBAInst.inst_ellT  843-853
private RBM.BA.KDecayBAInst.inst_far  855-871
RBM.BA.KDecayBAInst.inst_baKcalDecay_far  873-879
### RBM3D.BA.KHeat  (15 unreached of 75)
RBM.BA.KHeatInst.inst_zero_delta  1317-1320
RBM.BA.KHeatInst.inst_zero_origin  1322-1324
RBM.BA.KHeatInst.inst_zero_off  1326-1329
RBM.BA.KHeatInst.inst_mass  1331-1333
RBM.BA.KHeatInst.inst_nonneg_le_one  1335-1338
RBM.BA.KHeatInst.inst_even  1340-1342
RBM.BA.KHeatInst.inst_continuous  1344-1345
RBM.BA.KHeatInst.inst_fourier  1347-1352
RBM.BA.KHeatInst.inst_semigroup  1354-1358
RBM.BA.KHeatInst.inst_shift  1360-1364
RBM.BA.KHeatInst.inst_laplace  1366-1372
RBM.BA.KHeatInst.inst_laplace_origin  1374-1380
RBM.BA.KHeatInst.inst_diag_le  1382-1387
RBM.BA.KHeatInst.inst_gap  1389-1403
RBM.BA.KHeatInst.inst_gap_diag  1405-1414
### RBM3D.BA.KHeatDiff  (5 unreached of 71)
private RBM.BA.KHeatDiff_iter_ofReal  1642-1651
RBM.BA.BAKhat_diff_le  1653-1711
RBM.BA.KHeatDiffInst.inst_diff1  1721-1728
RBM.BA.KHeatDiffInst.inst_diff2  1730-1739
RBM.BA.KHeatDiffInst.inst_symb  1741-1750
### RBM3D.BA.KHeatTail  (3 unreached of 32)
RBM.BA.KHeatTailInst.inst_zdistD  757-759
RBM.BA.KHeatTailInst.inst_kBA_le  761-772
RBM.BA.KHeatTailInst.inst_tail_le  774-780
### RBM3D.BA.KInduct  (6 unreached of 35)
RBM.BA.baKsol_three  103-114
RBM.BA.baKpi_cut_S  706-721
private RBM.BA.KInductInst.KInduct_F5_mem  886-888
private RBM.BA.KInductInst.KInduct_F5_long  890-893
private RBM.BA.KInductInst.KInduct_F5_inner02  895-902
private RBM.BA.KInductInst.KInduct_F5_inner24  904-911
### RBM3D.BA.KKernel  (30 unreached of 54)
RBM.BA.BAK_offdiag_sum  133-138
RBM.BA.BAK_diag_bounds  140-145
RBM.BA.BAK_le_small  204-212
RBM.BA.BAK_le_decay  214-224
RBM.BA.BAK_adj_ge_small  280-287
RBM.BA.KKernelInst.inst_row_sum  393-395
RBM.BA.KKernelInst.inst_col_sum  397-398
RBM.BA.KKernelInst.inst_diag  400-401
RBM.BA.KKernelInst.inst_offdiag_sum  403-405
RBM.BA.KKernelInst.inst_diag_bounds  407-409
RBM.BA.KKernelInst.inst_symm  411-413
RBM.BA.KKernelInst.inst_shift  415-418
RBM.BA.KKernelInst.inst_zero_neg  420-422
RBM.BA.KKernelInst.inst_Mss_pm  424-427
RBM.BA.KKernelInst.inst_Mss_mp  429-432
RBM.BA.KKernelInst.inst_Mss_norm  434-437
RBM.BA.KKernelInst.inst_Theta_pm  439-443
RBM.BA.KKernelInst.inst_pow_row_sum  445-447
RBM.BA.KKernelInst.inst_pow_nonneg  449-450
RBM.BA.KKernelInst.inst_pow_transpose  452-454
RBM.BA.KKernelInst.inst_pow_shift  456-459
RBM.BA.KKernelInst.inst_off_le  461-467
RBM.BA.KKernelInst.inst_le_decay  469-474
RBM.BA.KKernelInst.inst_exp_moment  476-482
RBM.BA.KKernelInst.inst_exp_moment_zero  484-490
RBM.BA.KKernelInst.inst_adj_ge_small  492-496
RBM.BA.KKernelInst.inst_le_small  498-503
RBM.BA.KKernelInst.inst_adj_sum  505-509
RBM.BA.KKernelInst.inst_adj_sum_ge  511-517
RBM.BA.KKernelInst.inst_scalar  519-524
### RBM3D.BA.KMolecule  (1 unreached of 21)
private RBM.BA.KMoleculeInst.Sig0  411-413
### RBM3D.BA.KPure  (8 unreached of 39)
private RBM.BA.KPureInst.M0  856-857
private RBM.BA.KPureInst.tP  859-859
private RBM.BA.KPureInst.δ3  861-861
private RBM.BA.KPureInst.δ4  863-863
private RBM.BA.KPureInst.F02  870-870
private RBM.BA.KPureInst.F02_tsp  872-872
private RBM.BA.KPureInst.rate_pos  874-874
private RBM.BA.KPureInst.edge_P  876-885
### RBM3D.BA.KSolve  (36 unreached of 47)
RBM.BA.IsKLoopSLe  47-54
RBM.BA.BAKsolveLe3  69-86
private RBM.BA.BAKSolve_Msigma_symm  94-100
private RBM.BA.BAKSolve_Mss_symm  102-106
private RBM.BA.BAKSolve_Mss_swap  108-113
private RBM.BA.BAKSolve_Theta_zero  115-118
private RBM.BA.BAKSolve_comm  120-131
private RBM.BA.BAKSolve_ThQ_symm  133-145
private RBM.BA.BAKSolve_wc_pow  147-151
private RBM.BA.BAKSolve_wc_BAMLoop  153-159
private RBM.BA.BAKSolve_sum_one  169-172
private RBM.BA.BAKSolve_rhs_two  174-191
private RBM.BA.BAKSolve_rhs_three  193-224
private RBM.BA.BAKSolve_tau  234-237
private RBM.BA.BAKSolve_tau_hasDerivAt  239-256
private RBM.BA.BAKSolve_tau_leg1  258-271
private RBM.BA.BAKSolve_tau_leg2  273-285
private RBM.BA.BAKSolve_tau_leg3  287-299
private RBM.BA.BAKSolve_tau_one  301-305
private RBM.BA.BAKSolve_tau_smul  307-314
private RBM.BA.BAKSolve_tau_wc  316-327
private RBM.BA.BAKSolve_K  337-347
private RBM.BA.BAKSolve_mulRight_hasDerivAt  351-356
private RBM.BA.BAKSolve_two_hasDerivAt  358-376
private RBM.BA.BAKSolve_three_hasDerivAt  378-444
private RBM.BA.BAKSolve_exists_eq_of_length_three  448-456
private RBM.BA.BAKSolve_zero  458-467
RBM.BA.baKsolveLe3_holds  474-496
RBM.BA.BAKsol_translate  627-634
private RBM.BA.KSolveInst.m0_ne  649-652
RBM.BA.KSolveInst.le3_nondeg  670-686
RBM.BA.KSolveInst.rot_witness  688-695
RBM.BA.KSolveInst.translate_BAMLoop  702-718
RBM.BA.KSolveInst.unique_inst  720-731
RBM.BA.KSolveInst.rotate_inst  733-747
RBM.BA.KSolveInst.translate_inst  749-763
### RBM3D.BA.KStep  (2 unreached of 20)
private RBM.BA.KStepInst.KStep_layer4  619-622
private RBM.BA.KStepInst.KStep_layer5  624-627
### RBM3D.BA.KSumZeroB  (3 unreached of 21)
private RBM.BA.KSumZeroBInst.KSumZeroB_nc  636-637
private RBM.BA.KSumZeroBInst.KSumZeroB_nc_nonconst  639-639
private RBM.BA.KSumZeroBInst.KSumZeroB_F02  641-643
### RBM3D.BA.KSymbol  (14 unreached of 49)
RBM.BA.BAK_dir_ge  458-466
private RBM.BA.KSymbol_phi_zero  499-500
RBM.BA.BAK_lazy  566-583
RBM.BA.BAK_second_moment  698-753
RBM.BA.KSymbolInst.inst_var_lower  763-767
RBM.BA.KSymbolInst.inst_perm  769-774
RBM.BA.KSymbolInst.inst_dir_eq  776-780
RBM.BA.KSymbolInst.inst_dir_ge  782-786
RBM.BA.KSymbolInst.inst_Khat_eq  788-793
RBM.BA.KSymbolInst.inst_thetaSq_pos  795-801
RBM.BA.KSymbolInst.inst_gap  803-807
RBM.BA.KSymbolInst.inst_lazy  809-812
RBM.BA.KSymbolInst.inst_second_moment  814-818
RBM.BA.KSymbolInst.inst_Khat_zero  820-824
### RBM3D.BA.KTreeDeriv  (2 unreached of 29)
private RBM.BA.KTreeDerivInst.BAKTreeDeriv_isTSP_empty  529-530
private RBM.BA.KTreeDerivInst.BAKTreeDeriv_isTSP_F02  532-534
### RBM3D.BA.KTreeRep  (1 unreached of 100)
private RBM.BA.KTreeRepInst.KTreeRep_isTSP_F02  1730-1732
### RBM3D.BA.KWard  (1 unreached of 13)
private RBM.BA.BAKWardInst_K2  366-371
### RBM3D.BA.LWPinsBA  (11 unreached of 14)
RBM.BA.BALWtermEXP  48-49
RBM.BA.BASTLWB  50-51
RBM.BA.BASTLWT  52-53
RBM.BA.band_LWtermG  57-57
RBM.BA.band_LWtermExpG  58-58
RBM.BA.band_LWtermEXPG  59-59
RBM.BA.band_STLWBgL  60-60
RBM.BA.band_STLWTgL  61-61
private RBM.BA.Ψ0  71-72
private RBM.BA.Ψ0_window  73-76
private RBM.BA.ell0  77-79
### RBM3D.BA.MADecolQUE  (5 unreached of 20)
RBM.BA.UNQueBA_iff_at  59-60
RBM.BA.baEnd_decolL_three  146-147
RBM.BA.baEnd_QUEL_three  362-363
RBM.BA.unQueBAAt_three  381-382
private RBM.BA.MADecolQUE_hg  392-392
### RBM3D.BA.MALocal  (4 unreached of 34)
RBM.BA.baEnd_locSCL_three  837-839
RBM.BA.UNLocAvgBA_of_BAEnd_locSCL  852-855
RBM.BA.unLocAvgBAAt_of_ML  857-859
private RBM.BA.MALocal_hg  869-869
### RBM3D.BA.MAPins  (5 unreached of 26)
RBM.BA.BAMAFixed  150-152
RBM.BA.UNLocAvgBA_iff_at  195-196
RBM.BA.UNTrLocalBARow_iff_at  198-199
RBM.BA.UNTrLocalInitBARow'_iff_at  201-203
private RBM.BA.MAPins_hg  211-211
### RBM3D.BA.MAQDiff  (4 unreached of 29)
private RBM.BA.MAQDiff_Mss_symm  178-182
RBM.BA.baEnd_QDiffL_three  1015-1016
RBM.BA.baMAFixed_holds  1018-1019
private RBM.BA.MAQDiff_hg  1033-1033
### RBM3D.BA.MATrLocalBA  (5 unreached of 11)
RBM.BA.unTrLocalBARow_holds  91-93
RBM.BA.unTrLocalInitBARow'_holds  447-449
private RBM.BA.MATrLocalBA_hg  461-461
private RBM.BA.MATrLocalBA_hδ  463-464
private RBM.BA.MATrLocalBA_hwin  466-468
### RBM3D.BA.MFixedPoint  (8 unreached of 62)
RBM.BA.BAmBoundary  547-554
RBM.BA.BAWard  556-564
RBM.BA.BAoffDiag  582-591
RBM.BA.BAImmLower  593-600
RBM.BA.baMExists_holds  793-799
RBM.BA.BAm_eq_freeConvST  814-821
RBM.BA.MFixedPointInst.wI_norm  855-858
RBM.BA.MFixedPointInst.P  892-893
### RBM3D.BA.MReg  (4 unreached of 16)
private RBM.BA.MReg_norm_real_sub  66-68
RBM.BA.BArho_lip_of_bulk  167-188
private RBM.BA.MRegInst.MReg_flow_pos  347-348
private RBM.BA.MRegInst.MReg_flow_bulk  350-354
### RBM3D.BA.MainIndFamTL  (3 unreached of 13)
private RBM.BA.MainIndFamTL_atSz0  299-306
private RBM.BA.MainIndFamTL_famData  335-340
private RBM.BA.MainIndFamTL_atDatum  342-351
### RBM3D.BA.MainIndGlue  (3 unreached of 19)
RBM.BA.baMainIndFamTL_mono  45-51
private RBM.BA.MainIndGlue_lam_sq  337-345
private RBM.BA.MainIndGlue_reg  347-351
### RBM3D.BA.MainIndOutBA  (3 unreached of 22)
private RBM.BA.MainIndOutBA_flow  343-344
private RBM.BA.MainIndOutBA_win  346-347
private RBM.BA.MainIndOutBA_mem  349-351
### RBM3D.BA.MainIndTermBA  (2 unreached of 4)
RBM.BA.baMLOutTL_three  43-44
RBM.BA.baMainIndFamTL_any  51-56
### RBM3D.BA.NewKLKBA  (11 unreached of 21)
RBM.BA.stNewKLKgL'_ba  558-561
private RBM.BA.NewKLKBA_hermitian  612-617
private RBM.BA.NewKLKBA_GMM_small  619-725
private RBM.BA.NewKLKBAInst.szI  741-742
private RBM.BA.NewKLKBAInst.cmI  744-745
private RBM.BA.NewKLKBAInst.szI_lam  747-747
private RBM.BA.NewKLKBAInst.szI_lam_pos  749-749
private RBM.BA.NewKLKBAInst.szI_lam_le  751-751
private RBM.BA.NewKLKBAInst.szI_im  753-753
private RBM.BA.NewKLKBAInst.szI_L  755-757
private RBM.BA.NewKLKBAInst.HI  787-789
### RBM3D.BA.Prop5  (5 unreached of 66)
RBM.BA.Prop5Inst.inst_prop5  1426-1437
RBM.BA.Prop5Inst.inst_prop5_large_eps  1439-1449
RBM.BA.Prop5Inst.inst_prop8  1451-1459
RBM.BA.Prop5Inst.inst_prop8_large_eps  1461-1467
RBM.BA.Prop5Inst.inst_prop8_zero  1469-1475
### RBM3D.BA.Prop5Short  (16 unreached of 40)
RBM.BA.Prop5sInst.inst_sum_exp_decay  687-690
RBM.BA.Prop5sInst.inst_ss_norm  692-696
RBM.BA.Prop5sInst.inst_ss_diag  698-701
RBM.BA.Prop5sInst.inst_norm_sigma  703-707
RBM.BA.Prop5sInst.inst_row_offdiag_sum  709-713
RBM.BA.Prop5sInst.inst_sq_off_le  715-721
RBM.BA.Prop5sInst.inst_row_weighted  723-730
private RBM.BA.Prop5sInst.BP5_hyp_row  732-738
private RBM.BA.Prop5sInst.BP5_gap  740-746
RBM.BA.Prop5sInst.inst_BApropQ_decay  748-759
RBM.BA.Prop5sInst.inst_BApropQ_offdiag  761-779
RBM.BA.Prop5sInst.inst_of_real_half  781-787
RBM.BA.Prop5sInst.inst_of_real_one  789-795
RBM.BA.Prop5sInst.inst_BAProp5s_closed  797-802
RBM.BA.Prop5sInst.inst_C_pos  804-805
RBM.BA.Prop5sInst.inst_rate_pos  807-808
### RBM3D.BA.Prop6Path  (9 unreached of 46)
RBM.BA.Prop6PathInst.inst_bundle  1064-1065
RBM.BA.Prop6PathInst.inst_prop5_eq  1076-1083
RBM.BA.Prop6PathInst.inst_prop5_eq_zero  1085-1092
RBM.BA.Prop6PathInst.inst_prop6_eq  1094-1105
RBM.BA.Prop6PathInst.inst_prop7_eq  1107-1119
RBM.BA.Prop6PathInst.inst_prop8_eq  1121-1127
RBM.BA.Prop6PathInst.inst_reduction5  1129-1142
RBM.BA.Prop6PathInst.inst_reduction6  1144-1157
RBM.BA.Prop6PathInst.inst_reduction8  1159-1174
### RBM3D.BA.PropUnit  (8 unreached of 47)
RBM.BA.baPropUnit_laplace_head  480-510
RBM.BA.PropUnitInst.inst_unit1  1024-1035
RBM.BA.PropUnitInst.inst_unit1_large_eps  1037-1047
RBM.BA.PropUnitInst.inst_unit1_zero  1049-1057
RBM.BA.PropUnitInst.inst_unit2  1059-1072
RBM.BA.PropUnitInst.inst_unit2_large_eps  1074-1087
RBM.BA.PropUnitInst.inst_unit2_zero  1089-1101
RBM.BA.PropUnitInst.inst_laplace_head  1103-1115
### RBM3D.BA.RandomLayerBGBA  (1 unreached of 12)
private RBM.BA.RandomLayerBGBA_hg  141-141
### RBM3D.BA.SEforLnBA  (8 unreached of 20)
RBM.BA.baStep2Mat_carrierFacts  141-148
RBM.BA.baSEforLnConclgL_of  195-209
RBM.BA.SEforLnBAInst.inst_wardCls  313-315
RBM.BA.SEforLnBAInst.inst_oneLoop  317-322
RBM.BA.SEforLnBAInst.inst_carrierFacts  324-330
RBM.BA.SEforLnBAInst.inst_flowFacts  332-337
RBM.BA.SEforLnBAInst.inst_seforLnConclgL  342-351
RBM.BA.SEforLnBAInst.inst_baSEforLn  353-357
### RBM3D.BA.Step1  (19 unreached of 28)
private RBM.BA.BAStep1_gmMax_nonneg  83-87
RBM.BA.baS1_wl_seq  185-290
RBM.BA.baS1_forb  300-413
RBM.BA.baS1_boot  424-464
RBM.BA.baS1_weakPT  466-498
RBM.BA.baS1_loopPT  500-559
RBM.BA.baBootstrap'_holds  569-597
private RBM.BA.Step1Inst.lamS_two_thirds'  622-627
RBM.BA.Step1Inst.inst_hcon_full  629-669
RBM.BA.Step1Inst.inst_hLI  671-682
RBM.BA.Step1Inst.inst_hGii  684-691
RBM.BA.Step1Inst.inst_hGij  693-699
RBM.BA.Step1Inst.inst_baS1_wl_seq  701-712
RBM.BA.Step1Inst.inst_baS1_forb  714-722
RBM.BA.Step1Inst.inst_baS1_boot  724-733
RBM.BA.Step1Inst.inst_baS1_weakPT  735-745
RBM.BA.Step1Inst.inst_baS1_loopPT  747-758
RBM.BA.Step1Inst.inst_baBootstrap'  760-776
RBM.BA.Step1Inst.inst_gmMax_zero  778-782
### RBM3D.BA.Step1Boot  (17 unreached of 49)
RBM.BA.bandFM_indMax  67-69
RBM.BA.bandFM_gexRHS  71-74
RBM.BA.BAGijGEX  85-93
RBM.BA.BAGbEXPij  114-120
RBM.BA.baGij_member  282-303
RBM.BA.baOmegaC_eq_one  338-354
RBM.BA.Step1BootInst.inst_baGii_member  710-716
RBM.BA.Step1BootInst.inst_baGij_member  718-723
RBM.BA.Step1BootInst.inst_baM_entry_le  725-730
RBM.BA.Step1BootInst.inst_baOmegaC_eq_one  732-737
private RBM.BA.Step1BootInst.lamS_two_thirds  739-743
RBM.BA.Step1BootInst.inst_hcon  745-783
RBM.BA.Step1BootInst.inst_baBoot_LI_a  785-797
RBM.BA.Step1BootInst.inst_baBoot_LI_b  799-810
RBM.BA.Step1BootInst.inst_BAFamZ_mono  812-815
RBM.BA.Step1BootInst.inst_BAFamZ_horizon  817-818
RBM.BA.Step1BootInst.inst_PrecL_congr  820-832
### RBM3D.BA.Step1Fam  (25 unreached of 66)
RBM.BA.baStep1_holds  692-697
private RBM.BA.Step1FamInst.BAStep1Fam_wI_im  716-716
private RBM.BA.Step1FamInst.BAStep1Fam_zS_add_mS_im  718-719
RBM.BA.Step1FamInst.mS_im_ge  721-726
RBM.BA.Step1FamInst.mS_sz0_ge  728-728
RBM.BA.Step1FamInst.sz0_lam_le  730-736
private RBM.BA.Step1FamInst.BAStep1Fam_t0_eq  738-745
RBM.BA.Step1FamInst.t0_sz0_ge  747-750
RBM.BA.Step1FamInst.t0_sz0_le  752-758
RBM.BA.Step1FamInst.sz0_T0_pos  760-760
RBM.BA.Step1FamInst.sz0_T0_lt_one  762-763
RBM.BA.Step1FamInst.sz0_win  765-800
RBM.BA.Step1FamInst.sz0_win_third  802-805
RBM.BA.Step1FamInst.sz0_win_half  807-810
RBM.BA.Step1FamInst.sz0_win_tenth  812-816
RBM.BA.Step1FamInst.inst_BAFamZ_closed  818-824
RBM.BA.Step1FamInst.zMod  883-884
RBM.BA.Step1FamInst.zMod_ev  886-887
RBM.BA.Step1FamInst.sz0_conArg_bulk  902-915
RBM.BA.Step1FamInst.inst_conArg_lt  917-942
RBM.BA.Step1FamInst.inst_BAFlowMember  950-958
RBM.BA.Step1FamInst.inst_BALmaxFromLK  960-971
RBM.BA.Step1FamInst.inst_baStep1  979-996
RBM.BA.Step1FamInst.inst_baStep1_low  998-1014
RBM.BA.Step1FamInst.inst_baBootstrap'_full  1016-1024
### RBM3D.BA.Step1Prime  (13 unreached of 35)
RBM.BA.baBootstrap'_holds'  884-887
RBM.BA.Step1PrimeInst.inst_baGij'_member  943-960
RBM.BA.Step1PrimeInst.inst_step1Prime_loopPrem  962-968
RBM.BA.Step1PrimeInst.inst_step1Prime_wl_det  970-1037
RBM.BA.Step1PrimeInst.inst_hGii'  1042-1045
RBM.BA.Step1PrimeInst.inst_baS1_wl_seq'  1047-1058
RBM.BA.Step1PrimeInst.inst_baS1_forb'  1060-1068
RBM.BA.Step1PrimeInst.inst_baS1_boot'  1070-1079
RBM.BA.Step1PrimeInst.inst_baS1_weakPT'  1081-1091
RBM.BA.Step1PrimeInst.inst_baS1_loopPT'  1093-1104
RBM.BA.Step1PrimeInst.inst_baBootstrap'_ij'  1106-1122
RBM.BA.Step1PrimeInst.inst_baStep1'  1124-1140
RBM.BA.Step1PrimeInst.inst_baStep1'_low  1142-1157
### RBM3D.BA.Step1Setup  (19 unreached of 47)
RBM.BA.flowFM_omegaC_mono  53-62
private RBM.BA.BASetup_gexRHS_le  64-107
RBM.BA.flowFM_wl_det  109-164
private RBM.BA.BASetup_maxLoop_nonneg  1059-1063
private RBM.BA.BASetup_gexRHS_nonneg  1065-1068
private RBM.BA.BASetup_omegaC_le_one  1070-1073
RBM.BA.Step1SetupInst.sI  1093-1094
RBM.BA.Step1SetupInst.tI  1096-1096
RBM.BA.Step1SetupInst.inst_im_m_ge  1098-1111
RBM.BA.Step1SetupInst.inst_norm_m_le  1113-1115
RBM.BA.Step1SetupInst.inst_baS1Std  1117-1125
RBM.BA.Step1SetupInst.inst_baG_continuousOn  1139-1144
RBM.BA.Step1SetupInst.inst_baGopbound  1146-1159
RBM.BA.Step1SetupInst.inst_rangeCond  1161-1169
RBM.BA.Step1SetupInst.inst_baNetLift  1171-1189
RBM.BA.Step1SetupInst.inst_GM_zero  1191-1194
RBM.BA.Step1SetupInst.inst_flowFM_wl_det  1196-1255
RBM.BA.Step1SetupInst.inst_flowFM_omegaC_mono  1260-1263
RBM.BA.Step1SetupInst.inst_omegaC_three  1265-1277
### RBM3D.BA.Step2BA  (11 unreached of 18)
RBM.BA.baStep2Mat_toFlowFM  74-76
RBM.BA.baStep2Mat_LM  78-81
RBM.BA.baStep2Mat_GMM  83-86
RBM.BA.baStep2Mat_KI  88-91
RBM.BA.baStep2Mat_Pp  100-102
RBM.BA.baStep2Data_toFlowFM  131-133
RBM.BA.baStep2Data_T0  135-136
RBM.BA.baStep2Data_flowOK  138-140
RBM.BA.BAStep2_iff_STStep2G  142-147
RBM.BA.baStep2Fam_K  159-161
RBM.BA.baStep2Fam_m  163-165
### RBM3D.BA.Step34BA  (14 unreached of 28)
private RBM.BA.Step34BAInst.Step34BAInst_K  262-266
private RBM.BA.Step34BAInst.Step34BAInst_con  268-271
private RBM.BA.Step34BAInst.Step34BAInst_regIII  273-281
private RBM.BA.Step34BAInst.Step34BAInst_regI  283-285
RBM.BA.Step34BAInst.inst_baQtNZGen_kerNZ  287-297
RBM.BA.Step34BAInst.inst_baOeqQtgL'  334-344
RBM.BA.Step34BAInst.inst_baOeqQtNZgL'  346-356
RBM.BA.Step34BAInst.inst_baStep3RegIII  358-369
RBM.BA.Step34BAInst.inst_baStep3RegI  371-382
RBM.BA.Step34BAInst.inst_baStep3II  384-395
RBM.BA.Step34BAInst.inst_baStep4I  397-409
RBM.BA.Step34BAInst.inst_baStep4II  411-423
RBM.BA.Step34BAInst.inst_baStep4RegIII  425-437
RBM.BA.Step34BAInst.inst_baStep4RegI  439-451
### RBM3D.BA.Step5CasesBA  (24 unreached of 40)
private RBM.BA.Step5CasesBA_sz  277-283
private RBM.BA.Step5CasesBA_w  285-285
private RBM.BA.Step5CasesBA_z  287-288
private RBM.BA.Step5CasesBA_w_norm  290-293
private RBM.BA.Step5CasesBA_flow  295-369
private RBM.BA.Step5CasesBA_conStInd  371-388
private RBM.BA.Step5CasesBA_Datum  390-393
private RBM.BA.Step5CasesBA_datum  395-404
private RBM.BA.Step5CasesBA_prem  406-412
private RBM.BA.Step5CasesBA_apply  414-423
private RBM.BA.Step5CasesBA_szI  428-428
private RBM.BA.Step5CasesBA_zI  429-429
private RBM.BA.Step5CasesBA_szII  430-430
private RBM.BA.Step5CasesBA_zII  431-431
private RBM.BA.Step5CasesBA_szIV  432-432
private RBM.BA.Step5CasesBA_zIV  433-433
private RBM.BA.Step5CasesBA_datI  435-438
private RBM.BA.Step5CasesBA_datII  440-443
private RBM.BA.Step5CasesBA_datIV  445-448
private RBM.BA.Step5CasesBA_regI  450-451
private RBM.BA.Step5CasesBA_regMidI  453-454
private RBM.BA.Step5CasesBA_regII  456-457
private RBM.BA.Step5CasesBA_regMidII  459-460
private RBM.BA.Step5CasesBA_regIV  462-463
### RBM3D.BA.Step5IIIEdet  (11 unreached of 72)
RBM.BA.baStep5IIIE_trace_mul3_le  78-84
RBM.BA.baStep5IIIE_loop_hs_list  273-286
RBM.BA.Step5IIIEdet_tau_sq_le  412-419
RBM.BA.Step5IIIEdet_tau_le  421-427
RBM.BA.Step5IIIEdet_three_le_d  429-429
RBM.BA.Step5IIIEdet_u_nonneg  430-430
RBM.BA.Step5IIIEdet_scalar_sz0_one  1406-1413
RBM.BA.Step5IIIEdet_scalar_sz0_800  1415-1421
private RBM.BA.Step5IIIEdet_C0  1423-1423
private RBM.BA.Step5IIIEdet_Hf  1425-1426
private RBM.BA.Step5IIIEdet_loop_hs_sz0  1428-1433
### RBM3D.BA.Step5IIIEdet2  (5 unreached of 42)
RBM.BA.Step5IIIEdet2_near_self  1135-1144
private RBM.BA.Step5IIIEdet2_C0  1180-1181
private RBM.BA.Step5IIIEdet2_pt  1221-1222
private RBM.BA.Step5IIIEdet2_pt_dist  1224-1227
private RBM.BA.Step5IIIEdet2_pt_far  1229-1243
### RBM3D.BA.Step5IIIGood  (3 unreached of 24)
RBM.BA.Step5IIIGood_sz0_lam_le  613-620
RBM.BA.Step5IIIGood_reg_sz0  622-627
private RBM.BA.Step5IIIGood_Mat  651-665
### RBM3D.BA.Step5IIIGood2  (5 unreached of 6)
private RBM.BA.Step5IIIGood2_Scalar  89-93
private RBM.BA.Step5IIIGood2_Matrix  95-108
private RBM.BA.Step5IIIGood2_EdetConcl  110-124
private RBM.BA.Step5IIIGood2_Edet  126-132
RBM.BA.Step5IIIGood2_sz0_floor  134-150
### RBM3D.BA.Step5IIIKer  (3 unreached of 31)
RBM.BA.baStep5III_Theta_far  492-527
RBM.BA.Step5IIIKer_sz0_lam_le  657-666
RBM.BA.Step5IIIKer_sz0_reg  668-672
### RBM3D.BA.Step5IIIKer2  (4 unreached of 13)
RBM.BA.Step5IIIKer2_Xinst  374-376
RBM.BA.Step5IIIKer2_Yinst  378-380
RBM.BA.Step5IIIKer2_Xinst_near  382-385
RBM.BA.Step5IIIKer2_Xinst_crude  387-406
### RBM3D.BA.Step5IIITargets  (3 unreached of 6)
private RBM.BA.Step5IIITargets_instPrem  67-77
private RBM.BA.Step5IIITargets_inst_pf  79-86
private RBM.BA.Step5IIITargets_inst_step5  92-99
### RBM3D.BA.Step5IIIWalk  (8 unreached of 57)
RBM.BA.baStep5III_EMatrix_level  76-84
RBM.BA.baStep5III_duhamel  672-691
private RBM.BA.Step5IIIWalk_good_nonempty  1528-1541
private RBM.BA.Step5IIIWalk_sz0_floor46  1598-1604
private RBM.BA.Step5IIIWalk_instU  1628-1629
private RBM.BA.Step5IIIWalk_instA  1631-1632
private RBM.BA.Step5IIIWalk_instF  1634-1638
private RBM.BA.Step5IIIWalk_instQ  1684-1689
### RBM3D.BA.Step5IIIWalk2  (3 unreached of 14)
private RBM.BA.Step5IIIWalk2_instRead  996-1002
private RBM.BA.Step5IIIWalk2_instPrem  1004-1014
private RBM.BA.Step5IIIWalk2_inst_walk  1025-1034
### RBM3D.BA.Step5KerBA  (5 unreached of 19)
private RBM.BA.Step5KerBA_hmn  534-538
private RBM.BA.Step5KerBA_hSr  540-546
RBM.BA.baNewKLKLgL'  548-551
private RBM.BA.Step5KerBA_inst_window  567-574
private RBM.BA.Step5KerBA_inst_herm  576-581
### RBM3D.BA.Step6BridgeBA  (1 unreached of 13)
private RBM.BA.Step6BridgeBA_tl1  351-355
### RBM3D.BA.Step6PinsBA  (20 unreached of 37)
RBM.BA.baExpWardIgL  108-114
private RBM.BA.Step6PinsBA_prem  305-310
private RBM.BA.Step6PinsBA_apply  312-322
private RBM.BA.Step6PinsBA_reg3  324-334
private RBM.BA.Step6PinsBA_con0  336-338
private RBM.BA.Step6PinsBA_tT0  340-342
private RBM.BA.Step6PinsBA_szI  350-351
private RBM.BA.Step6PinsBA_zI  352-352
private RBM.BA.Step6PinsBA_szII  353-354
private RBM.BA.Step6PinsBA_zII  355-355
private RBM.BA.Step6PinsBA_szIV  356-357
private RBM.BA.Step6PinsBA_zIV  358-358
private RBM.BA.Step6PinsBA_datI  360-364
private RBM.BA.Step6PinsBA_datII  366-370
private RBM.BA.Step6PinsBA_datIV  372-376
private RBM.BA.Step6PinsBA_regI  378-379
private RBM.BA.Step6PinsBA_regII  381-382
private RBM.BA.Step6PinsBA_regIV  384-385
private RBM.BA.Step6PinsBA_applyD  387-394
private RBM.BA.Step6PinsBA_TL  455-458
### RBM3D.BA.TwistAvgA  (4 unreached of 84)
RBM.BA.twAvgMomentAt  99-107
RBM.BA.twAvgMoment  109-112
RBM.BA.TwistAvgA_pt_split  170-172
RBM.BA.twAvgMoment_holds  1049-1051
### RBM3D.BA.TwistAvgA2  (1 unreached of 52)
RBM.BA.TwistAvgA2_G_eq  162-163
### RBM3D.BA.TwistChain  (2 unreached of 16)
private RBM.BA.TwistChain_posConcl  149-184
RBM.BA.baChainTL_holds  236-262
### RBM3D.BA.TwistFold2  (9 unreached of 37)
RBM.BA.TwistFold2_shift_shift  62-66
RBM.BA.twLoop2X_trace  119-133
RBM.BA.TwistFold2_rho0  558-561
RBM.BA.TwistFold2_card_sz0  563-565
RBM.BA.TwistFold2_inst_val  567-575
RBM.BA.TwistFold2_rho0_row  577-582
RBM.BA.TwistFold2_rho0_col  584-589
RBM.BA.TwistFold2_H2  606-607
RBM.BA.TwistFold2_H2_herm  609-610
### RBM3D.BA.TwistFold2B  (4 unreached of 45)
RBM.BA.twFold2PrecDet  916-930
RBM.BA.twFold2PrecDet_holds  987-996
RBM.BA.TwistFold2_rho2  1003-1006
RBM.BA.TwistFold2_rho2_bounds  1008-1030
### RBM3D.BA.TwistGrid  (7 unreached of 65)
RBM.BA.twL2M_eq  131-131
RBM.BA.twL3M_eq  132-133
RBM.BA.twEGM_eq  134-134
RBM.BA.twB1M_eq  135-135
RBM.BA.twB2M_eq  136-136
RBM.BA.twDerM_eq  137-137
RBM.BA.twEEM_eq  138-138
### RBM3D.BA.TwistGrid2  (5 unreached of 21)
RBM.BA.twPredInc  64-67
RBM.BA.TwistGrid2_twAk_step  88-94
RBM.BA.TwistGrid2_twAk_duhamel  96-128
RBM.BA.BATwistDuhamel  132-141
RBM.BA.BATwistDuhamel_holds  143-164
### RBM3D.BA.TwistGridRem2  (1 unreached of 22)
private RBM.BA.TwistGridRem2_m_norm  117-121
### RBM3D.BA.TwistGridTail2  (1 unreached of 4)
private RBM.BA.TwistGridTail2_Kinst  413-414
### RBM3D.BA.TwistGridWTail  (1 unreached of 95)
private RBM.BA.TwistGridWTail_cm_apply  865-866
### RBM3D.BA.TwistKer  (2 unreached of 70)
RBM.BA.baTwKerA_holds  77-82
private RBM.BA.TwistKer_Pf  538-539
### RBM3D.BA.TwistKer2  (1 unreached of 43)
private RBM.BA.TwistKer2_frame_inst  1380-1387
### RBM3D.BA.TwistLoop  (3 unreached of 30)
RBM.BA.BATwKcircBound  722-734
private RBM.BA.TwistLoop_sum_M  740-754
RBM.BA.baTwKcircBound_holds  756-823
### RBM3D.BA.TwistPins  (6 unreached of 76)
RBM.BA.BAMainIndTL  168-175
RBM.BA.BAChainTL  183-188
private RBM.BA.TwistPins_frame_inst  765-770
private RBM.BA.TwistPins_trP_diag  827-838
private RBM.BA.TwistPins_loopX_perm  874-893
private RBM.BA.TwistPins_Pf  926-928
### RBM3D.BA.TwistQV  (2 unreached of 64)
private RBM.BA.TwistQV_wd_singleton  283-283
private RBM.BA.TwistQV_frame_inst  1398-1406
### RBM3D.BA.TwistStep2  (7 unreached of 58)
RBM.BA.TwistStep2_eta_eq  631-632
RBM.BA.TwistStep2_szII  1340-1346
RBM.BA.TwistStep2_wII  1348-1348
RBM.BA.TwistStep2_mII  1349-1349
RBM.BA.TwistStep2_zII  1350-1350
RBM.BA.TwistStep2_flowII  1352-1434
RBM.BA.TwistStep2_no_caseII_sz0  1546-1558
### RBM3D.BA.UNBUniv  (18 unreached of 36)
RBM.Univ.unG1RowkBA_holds  236-243
RBM.Univ.unOURowBA_holds  245-248
RBM.BA.baEnd_BUnivL_three  274-277
RBM.BA.baThm27L_any  284-289
private RBM.Univ.BAInst.UNBUniv_hML3  304-304
private RBM.Univ.BAInst.UNBUniv_hLoc3  306-307
private RBM.Univ.BAInst.UNBUniv_hQ3  309-309
RBM.Univ.BAInst.inst_UNOURowBAD  311-315
RBM.Univ.BAInst.inst_UNEMCTE2RowBAD  317-322
RBM.Univ.BAInst.inst_UNJakUywRowBAD  324-332
RBM.Univ.BAInst.inst_claimAll_baD  334-340
RBM.Univ.BAInst.inst_univ_baD  342-352
RBM.Univ.BAInst.inst_unNormBARow  354-356
RBM.Univ.BAInst.inst_unG1RowkBAD  358-364
RBM.Univ.BAInst.inst_unG1RowkBA  366-370
RBM.Univ.BAInst.inst_unOURowBA  372-376
RBM.Univ.BAInst.inst_baEnd_BUnivL_three  378-383
RBM.Univ.BAInst.inst_baThm27L_three  385-390
### RBM3D.BA.UNPins  (61 unreached of 100)
RBM.Univ.UNModelC.ba_spec  72-76
RBM.Univ.UNModelC.ba_toUNModel  78-79
RBM.Univ.UNKind.ba_M  90-91
RBM.Univ.UNQueBA  97-99
RBM.Univ.UNLocAvgBA  101-103
RBM.Univ.UNOURowBA  121-124
RBM.Univ.UNJakUywRowBA  130-132
RBM.Univ.UNClaimRowBA  134-136
RBM.Univ.un_claimAll_of_rowsBA  138-146
RBM.Univ.UNTrLocalBARow  166-173
RBM.Univ.UNTrLocalInitBARow'  175-185
RBM.Univ.UNQueBA_of_BAEnd_QUEL  355-359
RBM.Univ.baBUniv_of_rows  361-380
RBM.Univ.ouMatC_ba_eq_ouMat  404-434
RBM.Univ.ouP_ba_withLam  436-439
RBM.Univ.ouP_ba_eq_band  465-468
RBM.Univ.ba_zero_H  530-535
RBM.Univ.ba_zero_mean  537-542
RBM.Univ.ouMatC_ba_zero  544-551
RBM.Univ.UNEMCTE2k_ba_zero  553-561
RBM.Univ.UNJakk_ba_zero  563-571
RBM.Univ.UNUywk_ba_zero  573-581
RBM.BA.BASelf_msc  591-616
RBM.Univ.BAInst.inst_UNOUQUEk  897-905
RBM.Univ.BAInst.inst_UNOUDiagk  907-916
RBM.Univ.BAInst.zpt  918-919
RBM.Univ.BAInst.inst_UNEMCTE2k  921-941
RBM.Univ.BAInst.zpt2  943-944
RBM.Univ.BAInst.inst_UNJakk  946-959
RBM.Univ.BAInst.inst_UNUywk  961-975
RBM.Univ.BAInst.inst_UNQueBA  979-987
RBM.Univ.BAInst.inst_locAvg_domain  989-998
RBM.Univ.BAInst.inst_UNLocAvgBA  1000-1010
RBM.Univ.BAInst.inst_UNMLOutBA  1012-1022
RBM.Univ.BAInst.inst_UNOURowBA  1026-1030
RBM.Univ.BAInst.inst_UNEMCTE2RowBA  1032-1037
RBM.Univ.BAInst.inst_UNJakUywRowBA  1039-1047
RBM.Univ.BAInst.inst_claimAll_ba  1049-1056
RBM.Univ.BAInst.inst_univ_ba  1058-1071
RBM.Univ.BAInst.inst_admissible_lamHat  1075-1088
RBM.Univ.BAInst.inst_ouMatC_ba_eq_ouMat  1090-1107
RBM.Univ.BAInst.inst_unMeanBound_ba  1111-1114
RBM.Univ.BAInst.inst_step1GoodC''_ba  1116-1144
RBM.Univ.BAInst.badYBA_zero  1148-1158
RBM.Univ.BAInst.inst_badYBA_subset  1160-1166
RBM.Univ.BAInst.inst_badYBA_measure  1168-1173
RBM.Univ.BAInst.PsiI_entry_one  1175-1180
RBM.Univ.BAInst.inst_ba_mean_ne_zero  1182-1190
RBM.Univ.BAInst.inst_window_sub_ba  1192-1197
RBM.Univ.BAInst.inst_UNOUQUEk_zero  1199-1209
RBM.Univ.BAInst.inst_UNModelC_ba_spec  1213-1220
RBM.Univ.BAInst.inst_BAEnd_QUEL  1222-1234
RBM.Univ.BAInst.inst_UNQueBA_of_BAEnd_QUEL  1236-1243
RBM.Univ.BAInst.inst_ouP_ba  1245-1250
RBM.Univ.BAInst.inst_ouMatC_ba_eq_band_add  1252-1258
RBM.Univ.BAInst.inst_ouInit_ba  1260-1266
RBM.Univ.BAInst.inst_ba_zero  1268-1277
RBM.Univ.BAInst.inst_ba_zero_pins  1279-1291
RBM.Univ.BAInst.inst_BASelf_msc  1293-1295
RBM.Univ.BAInst.inst_unBadY_subset'  1297-1303
RBM.Univ.BAInst.inst_SBR_zero_ne  1305-1310
### RBM3D.BA.Ward  (7 unreached of 21)
RBM.BA.baWard_holds  157-162
RBM.BA.BAMss_pp_apply  266-268
RBM.BA.BAoffDiag_row_sum  274-286
RBM.BA.BAoffDiag_of_real  288-298
RBM.BA.baOffDiag_holds  302-308
RBM.BA.WardInst.ward_scalar_inst_norm  393-399
RBM.BA.WardInst.ward_scalar_inst_im  401-403
### RBM3D.BA.ZeroModeBA  (24 unreached of 27)
private RBM.BA.ZeroModeBA_coef  45-53
RBM.BA.stNewPQgL_wardCls  55-67
RBM.BA.baSTNewPQgL  69-76
private RBM.BA.ZeroModeBA_hIm  80-83
RBM.BA.baZeroModeSet_UN  85-97
RBM.BA.baZeroModeSet_ThetaN  99-106
RBM.BA.baStep2Gen_USemigroup  110-115
private RBM.BA.ZeroModeBAInst.σ3  158-159
private RBM.BA.ZeroModeBAInst.σ3_idiff  161-162
RBM.BA.ZeroModeBAInst.inst_newPQ_ba  164-180
RBM.BA.ZeroModeBAInst.inst_usemigroup  204-206
private RBM.BA.ZeroModeBAInst.inst_carrier  208-212
private RBM.BA.ZeroModeBAInst.szI  242-247
private RBM.BA.ZeroModeBAInst.wI  249-249
private RBM.BA.ZeroModeBAInst.mI  250-250
private RBM.BA.ZeroModeBAInst.zI  251-251
private RBM.BA.ZeroModeBAInst.flowI  253-335
private RBM.BA.ZeroModeBAInst.szI_W_tendsto  338-342
private RBM.BA.ZeroModeBAInst.szI_window  344-345
private RBM.BA.ZeroModeBAInst.szI_regIterI  347-349
private RBM.BA.ZeroModeBAInst.szII_W_tendsto  351-355
private RBM.BA.ZeroModeBAInst.szII_caseII  357-360
RBM.BA.ZeroModeBAInst.inst_iterationsgL'  362-382
RBM.BA.ZeroModeBAInst.inst_iterationsIIgL'  384-405
### RBM3D.Chain.AzumaProxyGen  (21 unreached of 33)
RBM.BA.azumaProxy_Hpath_zerog  134-143
RBM.BA.azumaProxy_pos_gridExitTauNg  145-159
RBM.BA.azumaProxy_pos_goodExitTauNg  161-168
RBM.BA.azumaProxy_subG_goodExitg  227-243
RBM.BA.AzumaProxyN_c0_pos_pubg  501-503
RBM.BA.yMomentsNg_of_unif  623-628
RBM.BA.yMomentsNg  630-637
RBM.BA.bandStep2_AzumaSubGN  647-653
private RBM.BA.AzumaProxyGenCheck.Cm0  755-755
private RBM.BA.AzumaProxyGenCheck.hL0  757-757
private RBM.BA.AzumaProxyGenCheck.hW0  758-758
private RBM.BA.AzumaProxyGenCheck.hKer0  759-760
private RBM.BA.AzumaProxyGenCheck.hQV0  761-761
private RBM.BA.AzumaProxyGenCheck.hspec0  762-763
private RBM.BA.AzumaProxyGenCheck.rangeCond_vg  765-776
private RBM.BA.AzumaProxyGenCheck.Kg_ne_zero  778-778
private RBM.BA.AzumaProxyGenCheck.gridStep_pos  780-782
RBM.BA.AzumaProxyGenCheck.azumaSubGNg_instance  788-800
private RBM.BA.AzumaProxyGenCheck.h0_inst  811-817
RBM.BA.AzumaProxyGenCheck.yMomentsUnifNg_instance  865-877
RBM.BA.AzumaProxyGenCheck.yfieldsWg_instance  914-942
### RBM3D.Chain.B45Gen  (19 unreached of 29)
private RBM.BA.B45Gen_flow_im_pos  75-77
RBM.BA.b45Gen_facts_band  79-104
private RBM.BA.B45Gen_norm_le_XiLK  576-595
private RBM.BA.B45Gen_prec_assemble  597-633
private RBM.BA.B45Gen_farXi  635-640
private RBM.BA.B45Gen_key  652-821
private RBM.BA.B45Gen_pins  831-876
RBM.BA.stWardTypePgL_of  878-902
RBM.BA.stB45gL_of  904-925
private RBM.BA.B45Gen_Bctl_ge  935-956
private RBM.BA.B45Gen_invN_of_conStInd  958-980
private RBM.BA.B45Gen_pin_data  982-1012
RBM.BA.stWardTypePPingL_of  1014-1027
RBM.BA.stB45PingL_of  1029-1040
private RBM.BA.B45Gen_band_kcal  1048-1052
RBM.BA.stWardTypePPin_gen_band  1054-1059
RBM.BA.stB45Pin_gen_band  1061-1066
private RBM.BA.B45GenInst.z0_abs_le''  1086-1087
private RBM.BA.B45GenInst.inst_hN  1089-1092
### RBM3D.Chain.CltFarUGen  (4 unreached of 20)
private RBM.BA.CltFarUGen_ck_pos  76-78
RBM.BA.iniTermGen_cltFlow_band  80-108
RBM.BA.bandFM_STCltFarUConcl  140-146
RBM.BA.iniTermGen_cltFarU_band  620-628
### RBM3D.Chain.CltGen  (5 unreached of 26)
RBM.BA.bandFM_STfFarg  207-212
RBM.BA.bandFM_STCltFarConcl  214-217
RBM.BA.bandFM_STCltIsoConcl  219-221
RBM.BA.bandFM_STExpInv  223-226
private RBM.BA.cltGen_chk_E  233-238
### RBM3D.Chain.DecayGen  (10 unreached of 25)
RBM.BA.STDecayLoopPTgL  72-78
RBM.BA.bandFM_STDecayLoopU  124-127
RBM.BA.bandFM_STDecayLoopPT  129-131
RBM.BA.bandFM_STKcalDecay  133-139
RBM.BA.DecayGen_bandWardPair  159-164
private RBM.BA.DecayGen_main_at  384-437
RBM.BA.stDecayLoopAtgL_of  439-455
RBM.BA.stDecayLoopPTgL_of_step2  457-520
private RBM.BA.DecayGen_inst_hE  607-610
private RBM.BA.DecayGen_inst_hN  612-615
### RBM3D.Chain.ExpAvgGen  (10 unreached of 76)
RBM.BA.ExpAvgGen_W1iiiOfLW  113-120
private RBM.BA.ExpAvgGen_int_of_bdd  876-880
RBM.BA.stImproveExpAvergL_of  1405-1412
RBM.BA.stExpAvgUgL_of_core  1414-1431
private RBM.BA.ExpAvgGen_band_W1i  1439-1456
private RBM.BA.ExpAvgGen_band_flowE  1458-1459
RBM.BA.ExpAvgGen_band_W1fam  1461-1479
private RBM.BA.ExpAvgGen_band_collapse  1481-1502
RBM.BA.ExpAvgGen_band_W1iiiOfLW  1504-1531
RBM.BA.stImproveExpAver_of_gL  1533-1537
### RBM3D.Chain.ExpDuhamelGen  (6 unreached of 25)
RBM.BA.stExpDuhamelZ_of_gL  469-481
RBM.BA.stExpDuhamelQ_of_gL  483-494
RBM.BA.stExpDuhamelZgL_at_inst  507-508
RBM.BA.stExpDuhamelQgL_at_inst  510-511
RBM.BA.stExpDuhamelZgL_ev_inst  546-556
RBM.BA.stExpDuhamelQgL_ev_inst  558-567
### RBM3D.Chain.ExpEtermsAGen  (2 unreached of 13)
private RBM.BA.ExpEtermsAGen_band_col  535-545
RBM.BA.stExpLKLKHi_of_gL  547-555
### RBM3D.Chain.ExpEtermsBGen  (4 unreached of 24)
private RBM.BA.ExpEtermsBGen_band_K1  863-871
private RBM.BA.ExpEtermsBGen_band_decay  873-906
RBM.BA.stExpDriftLo_of_gL  908-917
RBM.BA.stExpDriftDecay_of_gL  919-928
### RBM3D.Chain.ExpHierGen  (3 unreached of 38)
RBM.BA.stExpHier_of_gL  816-829
RBM.BA.stExpHiergL_at_inst  843-848
RBM.BA.stExpHiergL_ev_inst  856-865
### RBM3D.Chain.ExpIniIGen  (5 unreached of 18)
RBM.BA.bandFM_STExpIniIConcl'  79-84
RBM.BA.STExpIniI'_iff_gL'  88-93
private RBM.BA.ExpIniIGen_Kb_band  825-831
RBM.BA.stExpIniI'_gen_band  833-839
private RBM.BA.ExpIniIGen_bandData  852-863
### RBM3D.Chain.ExpIntEasyGen  (3 unreached of 14)
private RBM.BA.ExpIntEasyGen_KerF_band  358-366
RBM.BA.stExpIntIII_gen_band  368-372
RBM.BA.stExpIntIV_gen_band  374-377
### RBM3D.Chain.ExpIntIGen  (7 unreached of 15)
RBM.BA.bandFM_STExpIntQConcl'  88-93
RBM.BA.STExpIntI'_of_gL'  97-107
RBM.BA.ST_step6_caseI_of_pinsgL''  540-586
RBM.BA.ST_step6_caseI_of_pinsgL''_core  588-609
RBM.BA.ST_step6_caseI_of_pins''_gen_band  615-635
RBM.BA.ST_step6I_of_LW_Int_gen_band  637-643
private RBM.BA.ExpIntIGen_avgU_iff  655-663
### RBM3D.Chain.ExpIntIIGen  (1 unreached of 7)
RBM.BA.stExpIntII_gen_band  337-342
### RBM3D.Chain.ExpIntIQGen  (7 unreached of 20)
private RBM.BA.ExpIntIQGen_flowE_abs  1192-1195
RBM.BA.ExpIntIQGen_stExpIntIgL'_band  1197-1210
RBM.BA.ExpIntIQGen_stExpIntI'_band  1212-1214
RBM.BA.ExpIntIQGen_stStep6I_of_LW_band  1216-1218
private RBM.BA.ExpIntIQGen_bandEnv  1231-1240
private RBM.BA.ExpIntIQGen_sz0Env  1259-1273
private RBM.BA.ExpIntIQGen_bandKer  1300-1307
### RBM3D.Chain.ExpWardIGen  (5 unreached of 21)
RBM.BA.bandFM_STExpWardIConcl'  80-85
RBM.BA.STExpWardI'_iff_gL'  89-94
RBM.BA.stExpWardI_gen_band  457-462
RBM.BA.stExpWardI'_gen_band  464-468
private RBM.BA.ExpWardIGen_bandData  480-491
### RBM3D.Chain.ExpWardIIGen  (4 unreached of 15)
private RBM.BA.ExpWardIIGen_K1_band  315-323
RBM.BA.stExpWardII_gen_band  325-332
private RBM.BA.ExpWardIIGen_L1_band  344-356
private RBM.BA.ExpWardIIGen_bandData  358-363
### RBM3D.Chain.GridAssemblyGen  (26 unreached of 51)
RBM.BA.YMomentsConclNg  109-115
RBM.BA.YMomentsNg  117-121
RBM.BA.stoppedAzumaZNg  418-429
RBM.BA.bandStep2_qvFormN  844-861
RBM.BA.bandStep2_GridAssemblyHypN  871-912
RBM.BA.stoppedAzumaZN_of_Ng  914-932
private RBM.BA.GridAssemblyGen_Cm  979-980
private RBM.BA.GridAssemblyGen_hL  982-983
private RBM.BA.GridAssemblyGen_hW  985-986
private RBM.BA.GridAssemblyGen_assembled_instance_gen  1016-1072
private RBM.BA.GridAssemblyGenCheck.E0  1142-1142
private RBM.BA.GridAssemblyGenCheck.s0  1143-1143
private RBM.BA.GridAssemblyGenCheck.t0  1144-1144
private RBM.BA.GridAssemblyGenCheck.K0  1145-1145
private RBM.BA.GridAssemblyGenCheck.Ψ0  1146-1146
private RBM.BA.GridAssemblyGenCheck.Cm0  1147-1147
private RBM.BA.GridAssemblyGenCheck.σ3  1148-1148
private RBM.BA.GridAssemblyGenCheck.b3  1149-1149
private RBM.BA.GridAssemblyGenCheck.hL0  1151-1152
private RBM.BA.GridAssemblyGenCheck.hW0  1153-1153
private RBM.BA.GridAssemblyGenCheck.U3  1155-1157
private RBM.BA.GridAssemblyGenCheck.hΔ  1159-1159
private RBM.BA.GridAssemblyGenCheck.A₀3  1161-1162
private RBM.BA.GridAssemblyGenCheck.AbCN_eq  1164-1166
private RBM.BA.GridAssemblyGenCheck.c3  1168-1169
private RBM.BA.GridAssemblyGenCheck.c3_nonneg  1171-1171
### RBM3D.Chain.GridDuhamelGen  (24 unreached of 37)
RBM.BA.AvecNg_two  210-212
RBM.BA.bandStep2_AvecN  220-221
RBM.BA.bandStep2_martIncN  223-224
RBM.BA.bandStep2_predIncN  226-231
RBM.BA.StoppedDuhamelNg  241-257
RBM.BA.stoppedDuhamelNg  283-286
private RBM.BA.GridDuhamelGen_stronglyMeasurable_martIncNg  296-311
private RBM.BA.GridDuhamelGen_stronglyMeasurable_UN_apply  313-323
RBM.BA.StoppedAzumaNg  333-359
RBM.BA.stoppedAzumaNg_at  361-406
RBM.BA.stoppedAzumaNg  408-412
private RBM.BA.GridDuhamelGen_band_measurable  422-429
private RBM.BA.GridDuhamelGen_bandPp_isProbabilityMeasure  431-433
private RBM.BA.GridDuhamelGen_instSigma  495-495
private RBM.BA.GridDuhamelGen_instSigma_nonconst  497-498
private RBM.BA.GridDuhamelGen_instE  500-500
private RBM.BA.GridDuhamelGen_instS  501-501
private RBM.BA.GridDuhamelGen_instT  502-502
private RBM.BA.GridDuhamelGen_instK  503-503
private RBM.BA.GridDuhamelGen_inst_semigroup  505-507
private RBM.BA.GridDuhamelGen_inst_s0  509-510
private RBM.BA.GridDuhamelGen_inst_st  512-513
private RBM.BA.GridDuhamelGen_inst_t1  515-516
private RBM.BA.GridDuhamelGen_inst_K  518-519
### RBM3D.Chain.GridEnvelopeGen  (8 unreached of 14)
RBM.BA.gridDriftNg_envelope  58-125
private RBM.BA.GridEnvelopeGenCheck.Cm0  284-284
private RBM.BA.GridEnvelopeGenCheck.hE0  286-286
private RBM.BA.GridEnvelopeGenCheck.hL0  287-287
private RBM.BA.GridEnvelopeGenCheck.hW0  288-288
private RBM.BA.GridEnvelopeGenCheck.hspec0  289-290
private RBM.BA.GridEnvelopeGenCheck.him1  292-299
private RBM.BA.GridEnvelopeGenCheck.hη0  301-302
### RBM3D.Chain.GridGoodGen  (26 unreached of 59)
RBM.BA.STXiLMg  74-76
RBM.BA.STmaxLMg_Hf  94-99
RBM.BA.STXiLMg_Hf  108-113
RBM.BA.bandStep2_STmaxLM  129-129
RBM.BA.bandStep2_STmaxLKM  130-130
RBM.BA.bandStep2_STXiLM  131-131
RBM.BA.bandStep2_STXiLKM  132-132
RBM.BA.bandStep2_GoodSetN  177-180
RBM.BA.goodExitTauNg  196-198
RBM.BA.GoodExitMeasNg  398-402
RBM.BA.goodExitMeasNg  404-411
RBM.BA.bandStep2_gridExitTauN  419-422
RBM.BA.bandStep2_goodExitTauN  424-426
RBM.BA.bandStep2_GoodExitMeasN  428-430
RBM.BA.bandStep2_MeasurableGoodSetN  432-437
RBM.BA.bandStep2_GridGoodNConcl  483-485
RBM.BA.bandStep2_GridGoodN  487-491
RBM.BA.gridGoodNConclg_of  805-832
private RBM.BA.GridGoodGenCheck.E1  914-914
private RBM.BA.GridGoodGenCheck.Cm1  915-915
private RBM.BA.GridGoodGenCheck.hE1  917-917
private RBM.BA.GridGoodGenCheck.hL1  918-918
private RBM.BA.GridGoodGenCheck.hW1  919-919
private RBM.BA.GridGoodGenCheck.hspec1  988-989
private RBM.BA.GridGoodGenCheck.hB1_inst  991-993
private RBM.BA.GridGoodGenCheck.flow_abs_le  995-998
### RBM3D.Chain.GridRepTailGen2  (8 unreached of 14)
RBM.BA.bandStep2_STGridWTail2  657-667
RBM.BA.gridRepTailGen_eta_band  691-704
RBM.BA.gridRepTailGen_window_band  706-716
RBM.BA.gridRepTailGen_zfields_band  725-734
RBM.BA.gridRepTailGen_yfields_band  737-794
RBM.BA.gridRepTailGen_inc_band  796-819
RBM.BA.gridRepTailGen_hyp_band  823-837
RBM.BA.GridRepTailGenInst.inst_stGridWTail2gL_band  897-925
### RBM3D.Chain.HierDriftGen  (37 unreached of 73)
RBM.BA.STllPairNg  307-311
RBM.BA.bandStep2_STllPairN  313-316
RBM.BA.hierDriftGen_kLoop_band  385-390
RBM.BA.hierDriftGen_kTwo_band  392-401
RBM.BA.hierDriftGen_band_loopDrift  403-417
RBM.BA.HierarchyNg  427-437
RBM.BA.hierarchyNg_of  439-453
RBM.BA.hierarchyN_of_Ng  455-465
RBM.BA.hierDriftGen_kLink_band  681-683
RBM.BA.gridDriftNg  940-949
RBM.BA.HierDriftGen_exists_envelope_of  957-990
RBM.BA.HierDriftGen_exists_envelope  998-1005
RBM.BA.HierDriftGen_sum_norm_uKer_sub_one  1156-1177
RBM.BA.hierDriftGen_uStep_band  1179-1193
RBM.BA.hierDriftGen_expand_band  1195-1215
RBM.BA.hierDriftGen_SB_row  1217-1223
RBM.BA.hierDriftGen_band_gridDriftN  1225-1237
RBM.BA.hierDriftGen_band_exists_envelope  1239-1247
RBM.BA.hierDriftGen_band_eta  1249-1260
RBM.BA.hierDriftGen_band_exists_norm_Kcal_le_win  1262-1272
private RBM.BA.HierDriftGenCheck.E0  1290-1290
private RBM.BA.HierDriftGenCheck.s0  1291-1291
private RBM.BA.HierDriftGenCheck.t0  1292-1292
private RBM.BA.HierDriftGenCheck.K0  1293-1293
private RBM.BA.HierDriftGenCheck.Ψ0  1294-1294
private RBM.BA.HierDriftGenCheck.Cm0  1295-1295
private RBM.BA.HierDriftGenCheck.σ3  1296-1296
private RBM.BA.HierDriftGenCheck.a3  1297-1297
private RBM.BA.HierDriftGenCheck.hE0  1299-1299
private RBM.BA.HierDriftGenCheck.hL0  1300-1300
private RBM.BA.HierDriftGenCheck.hW0  1301-1301
private RBM.BA.HierDriftGenCheck.hst0  1302-1302
private RBM.BA.HierDriftGenCheck.ht10  1303-1303
private RBM.BA.HierDriftGenCheck.hj0  1304-1304
private RBM.BA.HierDriftGenCheck.data  1306-1309
private RBM.BA.HierDriftGenCheck.env3  1338-1342
private RBM.BA.HierDriftGenCheck.env3'  1352-1356
### RBM3D.Chain.IniTermIGen2  (1 unreached of 10)
RBM.BA.iniTermIGen_band_holds  727-736
### RBM3D.Chain.IniTermIIGen  (1 unreached of 24)
RBM.BA.iniTermIIGen_band_holds  1004-1009
### RBM3D.Chain.IterationsGen  (7 unreached of 30)
RBM.BA.IterationsGen_scaleg_iff  298-310
RBM.BA.bandFM_IterationsAScale  312-316
private RBM.BA.IterationsGenInst.szB_hsize  532-532
private RBM.BA.IterationsGenInst.szB_B_pos  534-534
private RBM.BA.IterationsGenInst.zB_abs_E  536-536
private RBM.BA.IterationsGenInst.zB_loopForm  538-539
private RBM.BA.IterationsGenInst.zB_norm_m  541-542
### RBM3D.Chain.IterationsGen2  (8 unreached of 25)
RBM.BA.IterationsGen2_famBand  429-439
private RBM.BA.IterationsGen2Inst.zB_abs_E  447-447
private RBM.BA.IterationsGen2Inst.zB_loopForm  449-450
private RBM.BA.IterationsGen2Inst.zB_norm_m  452-453
private RBM.BA.IterationsGen2Inst.szB_scaleII  455-458
private RBM.BA.IterationsGen2Inst.szB_scaleI  460-463
RBM.BA.IterationsGen2Inst.inst_iterationsgL'  465-487
RBM.BA.IterationsGen2Inst.inst_iterationsIIgL'  489-509
### RBM3D.Chain.KDecayGen  (6 unreached of 10)
RBM.BA.stKbound_timeIcc_gen_band  130-140
private RBM.BA.KDecayGen_band_KI  142-149
RBM.BA.KDecayGen_band_STKwardgL  151-161
RBM.BA.stKward_timeIcc_gen_band  163-180
private RBM.BA.KDecayGenInst.z0_abs_le'  199-200
private RBM.BA.KDecayGenInst.sz0_lam_bounds'  202-205
### RBM3D.Chain.LWGen  (11 unreached of 21)
RBM.BA.LWtermEXPG  107-119
RBM.BA.bandPin  129-131
RBM.BA.band_LWE  133-134
RBM.BA.band_LWAvgLaw  135-136
RBM.BA.band_LWAssm  137-139
RBM.BA.band_LWAssmExp  140-141
RBM.BA.LWterm_iff  142-142
RBM.BA.LWtermExp_iff  143-143
RBM.BA.LWtermEXP_iff  144-144
RBM.BA.STLWB_bandPin  145-146
RBM.BA.STLWT_bandPin  147-147
### RBM3D.Chain.NQBudgetGen  (14 unreached of 25)
RBM.BA.assembledRHSNonAltNg  50-67
RBM.BA.assembledRHSNonAltNg_band  80-84
RBM.BA.NQBudgetGen_kapFar_band  86-87
RBM.BA.NQBudgetGen_qvFar_band  89-90
RBM.BA.tbDriftNonAltNg  305-369
RBM.BA.budgetNonAltNg  441-719
private RBM.BA.NQBudgetGen_Cm0  775-775
private RBM.BA.NQBudgetGen_C  777-777
private RBM.BA.NQBudgetGen_hL0  779-779
private RBM.BA.NQBudgetGen_hm0  781-781
private RBM.BA.NQBudgetGen_eta_pos  783-784
private RBM.BA.NQBudgetGen_Cm00  941-941
private RBM.BA.NQBudgetGen_hspec00  943-944
private RBM.BA.NQBudgetGen_him00  946-953
### RBM3D.Chain.NQEndFlowGen  (16 unreached of 36)
RBM.BA.STOeqNQgL''  97-101
RBM.BA.bandFM_STXiBoot'  156-156
RBM.BA.bandFM_STNQConcl''  157-157
RBM.BA.bandFM_STNQConclPT''  158-158
RBM.BA.bandFM_STOeqNQ''  164-167
RBM.BA.bandFM_STOeqNQPT''  169-172
RBM.BA.bandFM_STOeqQt'  174-177
RBM.BA.bandFM_STOeqQtNZ'  179-182
RBM.BA.bandFM_STIterR'  184-187
RBM.BA.bandFM_STIterations'  189-191
RBM.BA.bandFM_STIterationsII'  193-195
RBM.BA.nqEndFlowGen_kLip_band  220-235
private RBM.BA.NQEndFlowGenCheck.flow_abs_le  787-790
RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band  792-822
RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band3  824-827
RBM.BA.stOeqNQPT''_holds_of_gen  831-836
### RBM3D.Chain.NQEndLinGen  (9 unreached of 26)
RBM.BA.gridDriftNg_iff_at  74-77
RBM.BA.gridDriftNg_envelope_of_merged  157-174
RBM.BA.nqGridEndLinN_of_gen  827-893
private RBM.BA.NQEndLinGenCheck.Cm1  913-913
private RBM.BA.NQEndLinGenCheck.nqEndLinNg_instance  915-958
private RBM.BA.NQEndLinGenCheck.hKb1  963-964
private RBM.BA.NQEndLinGenCheck.hL1  966-966
private RBM.BA.NQEndLinGenCheck.hW1  968-968
private RBM.BA.NQEndLinGenCheck.hm1  970-970
### RBM3D.Chain.NQGood1Gen  (19 unreached of 41)
RBM.BA.nqGoodGen_kerNAL_band_at  77-89
private RBM.BA.NQGood1Gen_flow_im  91-93
private RBM.BA.NQGood1Gen_flow_E  95-97
RBM.BA.nqGoodGen_kerNAL_band  99-110
RBM.BA.driftTensorNg_norm_le_of_goodSetNg  129-152
RBM.BA.qvFormNg_le_of_goodSetNg  393-412
RBM.BA.etaT_inv_shiftNg_le  458-484
RBM.BA.loopFine_shiftNg_le  486-511
private RBM.BA.NQGood1Gen_STmaxLMg_shift_le  513-522
private RBM.BA.NQGood1Gen_STmaxLMg_nonneg  524-526
RBM.BA.STXiLMg_shiftNg_le  528-546
RBM.BA.goodSetNg_dec_shiftNg  548-578
private RBM.BA.NQGood1Gen_Cm0  722-722
private RBM.BA.NQGood1Gen_hL0  724-724
private RBM.BA.NQGood1Gen_hm0  726-726
private RBM.BA.NQGood1Gen_goodSet0  728-730
private RBM.BA.NQGood1Gen_kerNAL0  732-735
private RBM.BA.NQGood1Gen_H0  786-786
private RBM.BA.NQGood1Gen_hS0  788-789
### RBM3D.Chain.NQGood2Gen  (27 unreached of 45)
RBM.BA.dDriftNonAltNg  61-63
RBM.BA.kappaNonAltNg_band  79-81
RBM.BA.epsNonAltNg_band  83-84
RBM.BA.dDriftNonAltNg_band  86-87
RBM.BA.qvBdNonAltNg_band  89-90
RBM.BA.cQVNonAltNg_band  92-95
RBM.BA.nonAlt_hdriftNg  189-196
RBM.BA.nonAlt_hdDrift0Ng  231-245
RBM.BA.subGaussStop_nonAltNg  378-399
RBM.BA.hQ_nonAltN_of_Ng  425-462
private RBM.BA.NQGood2Gen_Cm0  482-482
private RBM.BA.NQGood2Gen_C  484-484
private RBM.BA.NQGood2Gen_tau0  486-486
private RBM.BA.NQGood2Gen_hL0  488-488
private RBM.BA.NQGood2Gen_hWalk0  490-490
private RBM.BA.NQGood2Gen_hRow0  492-492
private RBM.BA.NQGood2Gen_hQV0  494-494
private RBM.BA.NQGood2Gen_hm0  496-496
private RBM.BA.NQGood2Gen_hS0  498-499
private RBM.BA.NQGood2Gen_kerNAL0  501-503
private RBM.BA.NQGood2Gen_R1  505-506
private RBM.BA.NQGood2Gen_hdW  508-509
private RBM.BA.NQGood2Gen_goodSet0  511-514
private RBM.BA.NQGood2Gen_tau0_mem  516-518
private RBM.BA.NQGood2Gen_tau0_pos  520-523
private RBM.BA.NQGood2Gen_hker_field  560-570
private RBM.BA.NQGood2Gen_hQ_instance  639-648
### RBM3D.Chain.NQLinGen  (23 unreached of 42)
RBM.BA.bandStep2_GoodLinN  102-104
RBM.BA.bandStep2_NQLinConcl  106-108
RBM.BA.bandStep2_NQLinGood  110-114
RBM.BA.goodSetNg_subset_goodLinNg  142-153
RBM.BA.nqLinGood_holds_of_gen  385-396
RBM.BA.dDriftNonAltNg_eq_lin  419-424
private RBM.BA.NQLinGen_Cm0  895-895
private RBM.BA.NQLinGen_C  897-897
private RBM.BA.NQLinGen_hL0  899-899
private RBM.BA.NQLinGen_hWalk0  901-901
private RBM.BA.NQLinGen_hRow0  903-903
private RBM.BA.NQLinGen_hQV0  905-905
private RBM.BA.NQLinGen_hm0  907-907
private RBM.BA.NQLinGen_hS0  909-910
private RBM.BA.NQLinGen_kerNAL0  912-914
private RBM.BA.NQLinGen_R1  916-917
private RBM.BA.NQLinGen_hdW  919-920
private RBM.BA.NQLinGen_goodSet0  922-924
private RBM.BA.NQLinGen_goodLin0  928-934
private RBM.BA.NQLinGen_tau0  975-976
private RBM.BA.NQLinGen_mem0  978-989
private RBM.BA.NQLinGen_tau0_pos  991-995
private RBM.BA.NQLinGen_drift_instance  1004-1009
### RBM3D.Chain.NewKLKGen  (13 unreached of 17)
RBM.BA.STNewKLKAtgL'  56-69
RBM.BA.STNewKLKgL'  71-73
RBM.BA.stNewKLKAtgL'_of  413-606
RBM.BA.stNewKLKAtgL'_holds  608-613
RBM.BA.stNewKLKgL'_of  615-622
RBM.BA.stNewKLKAtgL_of_primed  626-633
RBM.BA.stNewKLKgL_of_primed  635-643
RBM.BA.stK2decaygL_of_primed  645-655
RBM.BA.newKLKGenHyp_band  665-744
RBM.BA.stK2decaygL'_band  746-757
private RBM.BA.NewKLKGen_cm0  806-807
private RBM.BA.NewKLKGen_H0  810-811
private RBM.BA.NewKLKGen_baMk  838-847
### RBM3D.Chain.NewKLKLGen  (5 unreached of 6)
RBM.BA.stNewKLKLAtgL'_of  186-296
RBM.BA.stNewKLKLgL'_of  298-305
RBM.BA.stNewKLKLgL'_holds_band  311-314
private RBM.BA.NewKLKLGen_cm0  345-346
private RBM.BA.NewKLKLGen_H0  348-349
### RBM3D.Chain.OptL2Gen  (5 unreached of 29)
RBM.BA.optL2Gen_bandStep2_OptL2aJ  63-66
private RBM.BA.OptL2Gen_bandSpec  1260-1265
private RBM.BA.OptL2Gen_bdata_band  1267-1270
private RBM.BA.OptL2Gen_hcon  1272-1274
RBM.BA.optL2Gen_stOptL2_of_pins_band  1362-1372
### RBM3D.Chain.QEndB1Gen  (6 unreached of 20)
RBM.BA.bandFM_STXiRoundPT''  91-92
RBM.BA.bandFM_STOeqQtRoundPT''  96-100
private RBM.BA.QEndB1GenCheck.flow_abs_le  1028-1031
RBM.BA.QEndB1GenCheck.stOeqQtRoundPTgL''_band  1033-1069
RBM.BA.QEndB1GenCheck.stOeqQtRoundPTgL''_band3  1071-1074
RBM.BA.stOeqQtRoundPT''_holds_of_gen  1078-1083
### RBM3D.Chain.QEndGridGen  (3 unreached of 11)
private RBM.BA.QEndGridGenCheck.Cm1  1074-1074
private RBM.BA.QEndGridGenCheck.b45_band_rowcol  1076-1093
RBM.BA.QEndGridGenCheck.altGridEndQNg_instance  1095-1151
### RBM3D.Chain.QGridGen  (25 unreached of 52)
RBM.BA.QGridGen_bandStep2_aTrueQN  846-848
RBM.BA.QGridGen_bandStep2_dGridQN  850-860
private RBM.BA.QGridGenCheck.E0  880-880
private RBM.BA.QGridGenCheck.s0  881-881
private RBM.BA.QGridGenCheck.t0  882-882
private RBM.BA.QGridGenCheck.K0  883-883
private RBM.BA.QGridGenCheck.Ψ0  884-884
private RBM.BA.QGridGenCheck.Cm0  885-885
RBM.BA.QGridGenCheck.QGridGen_sigma4  887-888
RBM.BA.QGridGenCheck.QGridGen_sigma4_alternating  890-893
private RBM.BA.QGridGenCheck.moll  895-897
private RBM.BA.QGridGenCheck.lam_pos  899-899
private RBM.BA.QGridGenCheck.hE0  901-901
private RBM.BA.QGridGenCheck.hL0  902-902
private RBM.BA.QGridGenCheck.hW0  903-903
private RBM.BA.QGridGenCheck.hm0  904-904
private RBM.BA.QGridGenCheck.hs0  905-905
private RBM.BA.QGridGenCheck.hst0  906-906
private RBM.BA.QGridGenCheck.ht10  907-907
private RBM.BA.QGridGenCheck.hK0  908-908
private RBM.BA.QGridGenCheck.hj0  909-909
private RBM.BA.QGridGenCheck.data  911-914
private RBM.BA.QGridGenCheck.env4  916-919
RBM.BA.QGridGenCheck.QGridGen_gridDriftQNg_instance  921-939
RBM.BA.QGridGenCheck.QGridGen_stoppedDuhamelQNg_instance  941-955
### RBM3D.Chain.QGridGen2  (7 unreached of 9)
private RBM.BA.QGridGen2Check.Cm0  100-100
private RBM.BA.QGridGen2Check.hspec0  102-103
private RBM.BA.QGridGen2Check.him1  105-112
RBM.BA.QGridGen2Check.QGridGen2_Kc31  114-115
private RBM.BA.QGridGen2Check.Kc31_ne_zero  117-122
private RBM.BA.QGridGen2Check.rpow_31_le_Kc31  124-128
RBM.BA.QGridGen2Check.QGridGen2_sum_weighted_qErrQNg_instance  130-148
### RBM3D.Chain.QopDecayGen  (7 unreached of 11)
RBM.BA.QopDecayGen_STthetaOp_fastDecay_band  238-258
private RBM.BA.QopDecayGen_sz0_lam  270-275
private RBM.BA.QopDecayGen_sz0_W  277-280
private RBM.BA.QopDecayGen_ellT_le_one  282-290
private RBM.BA.QopDecayGen_sz0_far  292-318
private RBM.BA.QopDecayGen_sz0_nontriv  320-334
private RBM.BA.QopDecayGen_inst_data  336-388
### RBM3D.Chain.QtBootGen  (4 unreached of 14)
RBM.BA.bandFM_STXiRound'  72-73
private RBM.BA.QtBootGen_flow_abs_le  435-438
RBM.BA.qtBootGen_flowModFam_band  440-445
RBM.BA.qtBootGen_hyp_band  447-459
### RBM3D.Chain.QtNonzeroBootGen  (8 unreached of 16)
RBM.BA.QtNonzeroBootGenCheck.stXiRoundNZgL_band  588-620
RBM.BA.QtNonzeroBootGenCheck.stOeqQtNZgL'_band  622-653
RBM.BA.QtNonzeroBootGenCheck.stOeqQtNZgL'_band3  655-658
RBM.BA.QtNonzeroBootGenCheck.stXiRoundNZgL_band3  660-664
RBM.BA.QtNonzeroBootGenCheck.stXiRoundNZ_holds_of_gen  666-671
RBM.BA.stOeqQtNZ'_holds_of_gen  675-680
RBM.BA.QtNonzeroBootGenCheck.inst_XiRoundNZgL  697-708
RBM.BA.QtNonzeroBootGenCheck.inst_OeqQtNZgL'  710-720
### RBM3D.Chain.QtNonzeroEndGen  (2 unreached of 7)
RBM.BA.nzGridEndN_of_gen  550-617
RBM.BA.qtNZEndGen_instance  637-673
### RBM3D.Chain.QtNonzeroFlowGen  (12 unreached of 27)
RBM.BA.bandFM_STNZConclPT''  121-121
RBM.BA.bandFM_STNZConcl''  122-122
RBM.BA.bandFM_STOeqNZPT''  128-131
RBM.BA.bandFM_STOeqNZ''  133-136
RBM.BA.QtNonzeroFlowGenCheck.stOeqNZPTgL''_band  935-965
RBM.BA.QtNonzeroFlowGenCheck.stOeqNZgL''_band  967-998
RBM.BA.QtNonzeroFlowGenCheck.stOeqNZPTgL''_band3  1000-1003
RBM.BA.QtNonzeroFlowGenCheck.stOeqNZgL''_band3  1005-1008
RBM.BA.stOeqNZPT''_holds_of_gen  1012-1017
RBM.BA.stOeqNZ''_holds_of_gen  1019-1023
RBM.BA.QtNonzeroFlowGenCheck.inst_OeqNZPTgL''  1040-1052
RBM.BA.QtNonzeroFlowGenCheck.inst_OeqNZgL''  1054-1064
### RBM3D.Chain.QtNonzeroGen  (8 unreached of 20)
RBM.BA.qtNZGen_bandC  70-72
RBM.BA.qtNZGen_bandC_pos  74-77
RBM.BA.qtNZGen_kerNZ_band_at  79-97
RBM.BA.qtNZGen_kerNZ_band  99-114
private RBM.BA.QtNZGen_D1_szB  769-773
private RBM.BA.QtNZGen_drift_instance  825-832
private RBM.BA.QtNZGen_row_coarse  852-879
RBM.BA.qtNZGen_subGaussStop_instance  881-891
### RBM3D.Chain.QtXiRoundLiftGen  (7 unreached of 18)
RBM.BA.QtXiRoundLiftGenCheck.stXiRoundQtgL_band  549-587
RBM.BA.QtXiRoundLiftGenCheck.stOeqQtgL'_band  589-625
RBM.BA.QtXiRoundLiftGenCheck.stOeqQtgL'_band3  627-630
RBM.BA.QtXiRoundLiftGenCheck.stXiRoundQtgL_band3  632-636
RBM.BA.QtXiRoundLiftGenCheck.stXiRoundQt_holds_of_gen  638-643
RBM.BA.stOeqQt'_holds_of_gen  647-652
private RBM.BA.QtXiRoundLiftGenCheck.inst_htN  669-674
### RBM3D.Chain.SEforLnGen  (4 unreached of 65)
private RBM.BA.SEforLnGen_sum_norm_SB_col  77-84
RBM.BA.seforLnGen_facts_band  86-105
private RBM.BA.SEforLnGen_flow_im  1562-1564
private RBM.BA.SEforLnGenInst.z0_abs_le''  1663-1664
### RBM3D.Chain.SEforLnGen2  (1 unreached of 29)
private RBM.BA.SEforLnGen2Inst.z0_abs_le3  941-942
### RBM3D.Chain.Step2CloseGen  (7 unreached of 30)
RBM.BA.step2IterGen_listLink_band  72-75
RBM.BA.STthetaOpg_eq_ThetaN  81-84
RBM.BA.STEEMg_eq_STeeMg  136-144
RBM.BA.STgAg_eq_STgANg  146-149
RBM.BA.STgDriftg_eq_STgDriftNg  151-162
RBM.BA.step2CloseGen_stLocalAvgOfL2_band  807-822
RBM.BA.step2CloseGen_step2_of_pinsLW'  828-839
### RBM3D.Chain.Step2EventsGen  (6 unreached of 54)
RBM.BA.Step2EventsGen_STEEMg_measurable  398-401
RBM.BA.bandFM_STScaleInv  441-443
RBM.BA.Step2EventsGen_bandFlow  1115-1118
RBM.BA.Step2EventsGen_bandRot3  1120-1122
RBM.BA.Step2EventsGen_bandGoodAt  1137-1164
private RBM.BA.Step2EventsGen_inst_hE  1180-1181
### RBM3D.Chain.Step2EventsGenTw  (3 unreached of 7)
RBM.BA.Step2EventsGenTw_toFlowFM  80-82
RBM.BA.Step2EventsGenTw_band_STLWBgL  156-161
RBM.BA.Step2EventsGenTw_band_STLWTgL  163-167
### RBM3D.Chain.Step2Gen  (57 unreached of 144)
RBM.BA.Step2Kern_ThetaN_band  315-324
RBM.BA.bandStep2_STmsig  414-414
RBM.BA.bandStep2_STLM  415-416
RBM.BA.bandStep2_STLKM  417-418
RBM.BA.bandStep2_STJhatM  419-420
RBM.BA.bandStep2_STavgM  421-422
RBM.BA.bandStep2_STEGtM  423-424
RBM.BA.bandStep2_STELKLKM  425-426
RBM.BA.bandStep2_STEEkM  441-442
RBM.BA.bandStep2_STEEM  443-444
RBM.BA.bandStep2_STGMM  445-446
RBM.BA.bandFM_STJhat  474-475
RBM.BA.bandFM_STEGt  476-477
RBM.BA.bandFM_STLWassm  478-479
RBM.BA.bandFM_STAvgU  564-564
RBM.BA.bandFM_STLocalEntryU  565-566
RBM.BA.bandFM_STGdecayW  567-568
RBM.BA.bandFM_STStep2Concl  569-570
RBM.BA.bandFM_STStep2Local  571-571
RBM.BA.bandFM_STStep2Avg  572-572
RBM.BA.bandFM_STStep2Decay  573-574
RBM.BA.bandFM_STStep2LocalPT  575-576
RBM.BA.bandFM_STStep2AvgPT  577-577
RBM.BA.bandFM_STStep2DecayPT  578-579
RBM.BA.bandFM_STL2decayPT  580-580
RBM.BA.STStep2_iff  705-707
RBM.BA.bandFM_STNetLift2  708-710
RBM.BA.bandFM_STLocalAvgOfL2  711-713
RBM.BA.bandFM_STOptL2  714-716
RBM.BA.bandFM_STScaleExists  717-718
RBM.BA.bandFM_STLWB  719-721
RBM.BA.bandFM_STindMax  784-785
RBM.BA.bandFM_STgexRHS  786-787
RBM.BA.bandFM_STGiiGEX  788-788
RBM.BA.bandFM_STGavLGEX  789-789
RBM.BA.bandStep2_STgA  890-891
RBM.BA.bandStep2_STstopIdx  898-899
RBM.BA.STGridRepNgL  1030-1033
RBM.BA.bandStep2_STLIM  1040-1040
RBM.BA.bandStep2_STLKIM  1041-1042
RBM.BA.bandStep2_STksimLKM  1043-1044
RBM.BA.bandStep2_STelklkM  1045-1046
RBM.BA.bandStep2_STavgErrM  1047-1048
RBM.BA.bandStep2_STegtM  1049-1050
RBM.BA.bandStep2_STeeM  1051-1052
RBM.BA.bandStep2_STgAN  1053-1054
RBM.BA.bandStep2_STgDriftN  1055-1062
RBM.BA.bandStep2_STeeUM  1063-1069
RBM.BA.bandStep2_STGridRepNAt  1070-1078
RBM.BA.bandStep2_STGridRepN  1079-1083
RBM.BA.STNewKLKAtgL  1089-1102
RBM.BA.STNewKLKgL  1104-1106
RBM.BA.STK2decaygL  1108-1113
RBM.BA.bandStep2_STNewKLKAt  1128-1137
RBM.BA.bandStep2_STNewKLK  1138-1140
RBM.BA.bandStep2_STK2decay  1141-1141
private RBM.BA.Step2GenInst.Step2Gen_Bm0  1235-1236
### RBM3D.Chain.Step2IterGen  (5 unreached of 17)
private RBM.BA.Step2IterGen_flow_data  92-99
RBM.BA.step2IterGen_newKLKAtN_band  101-111
RBM.BA.step2IterGen_newKLK_band  113-121
RBM.BA.step2IterGen_oneLoop_band  128-133
RBM.BA.bandFM_STSelfImp  455-457
### RBM3D.Chain.Step2IterGen2  (5 unreached of 12)
RBM.BA.ST_step2_of_pinsg  292-371
RBM.BA.stBdatagL_band  375-379
RBM.BA.stScaleExistsgL_band  381-385
RBM.BA.step2IterGen_step2_of_pins_band  387-407
private RBM.BA.Step2IterGen2_inst_step2  465-482
### RBM3D.Chain.Step2Kern  (2 unreached of 7)
RBM.BA.Step2Kern_BAKsolve_form  102-109
private RBM.BA.Step2Kern_BI  145-146
### RBM3D.Chain.Step34Gen  (77 unreached of 123)
RBM.BA.bandFM_STLmaxU  88-88
RBM.BA.bandFM_STLKU  89-89
RBM.BA.STsupXiLKg  115-116
RBM.BA.bandStep34_STmaxL  128-128
RBM.BA.bandStep34_STmaxLK  129-129
RBM.BA.bandStep34_STXiL  130-130
RBM.BA.bandStep34_STXiLK  131-131
RBM.BA.bandStep34_STsupXiLK  132-132
RBM.BA.bandStep34_STLKtensor  133-134
RBM.BA.bandStep34_STLI  177-178
RBM.BA.bandStep34_STKI  179-179
RBM.BA.bandStep34_STLKI  180-181
RBM.BA.bandStep34_STksimLK  182-183
RBM.BA.bandStep34_STelklk  184-185
RBM.BA.bandStep34_STavgErr  186-187
RBM.BA.bandStep34_STegt  188-189
RBM.BA.bandStep34_STee  190-191
RBM.BA.bandStep34_LCompat  193-196
RBM.BA.bandStep34_KCompat  197-197
RBM.BA.STXiBootgL  239-248
RBM.BA.STNQConclgL  250-262
RBM.BA.STNQConclgL'  264-276
RBM.BA.STWardTypePgL  283-291
RBM.BA.STB45gL  293-307
RBM.BA.bandStep34_ThetaN  315-319
RBM.BA.bandStep34_UN  321-324
RBM.BA.bandFM_STSEforLnConcl  326-327
RBM.BA.bandFM_STXiBoot  328-328
RBM.BA.bandFM_STNQConcl  329-329
RBM.BA.bandFM_STNQConcl'  330-330
RBM.BA.bandFM_STIterHyp  331-332
RBM.BA.bandFM_STWardTypeP  333-333
RBM.BA.bandFM_STB45  334-338
RBM.BA.STIterRgL  385-400
RBM.BA.STOeqNQgL  412-416
RBM.BA.STWardTypePPingL  418-422
RBM.BA.STB45PingL  424-428
RBM.BA.bandFM_STStep3R  432-438
RBM.BA.bandFM_STStep4R  440-445
RBM.BA.bandFM_STIngR  447-453
RBM.BA.bandFM_STIterR  455-458
RBM.BA.bandFM_STSEforLn  460-463
RBM.BA.bandFM_STOeqNQ  465-468
RBM.BA.bandFM_STWardTypePPin  470-473
private RBM.BA.step34Gen_ingR_congr  475-482
RBM.BA.bandFM_STB45Pin  484-489
RBM.BA.STEKSumRes1gL  539-549
RBM.BA.STEKBandKer  586-588
RBM.BA.bandFM_STEKWin  596-596
RBM.BA.bandFM_STEKDecay  598-599
RBM.BA.bandFM_STEKLow  601-602
RBM.BA.stek_sumNdecaygL_band  615-621
RBM.BA.stek_sumRes1gL_band  623-627
RBM.BA.stek_sumRes2NALgL_band  629-634
RBM.BA.stek_sumRes2gL_band  636-641
RBM.BA.stek_nonzerogL_band  643-655
private RBM.BA.step34Gen_ellT_le_pt  723-738
RBM.BA.step34Gen_ellT_le  778-782
RBM.BA.STNewPQgL  821-835
RBM.BA.stNewPQgL_band  837-843
private RBM.BA.step34Gen_lam0_nonneg  855-857
private RBM.BA.step34Gen_mE_zero_im  859-860
private RBM.BA.step34Gen_norm_delta0_le  1036-1039
private RBM.BA.step34Gen_prec_delta0  1041-1043
private RBM.BA.step34Gen_decay_delta0  1045-1061
private RBM.BA.step34Gen_low_one  1063-1064
private RBM.BA.step34Gen_win_sz0  1066-1074
private RBM.BA.step34Gen_Az  1076-1078
private RBM.BA.step34Gen_norm_Az_le  1080-1083
private RBM.BA.step34Gen_Az_sumZero  1085-1099
private RBM.BA.step34Gen_Az_decay  1101-1124
private RBM.BA.step34Gen_decay_Az  1126-1139
private RBM.BA.step34Gen_prec_Az  1141-1143
private RBM.BA.step34Gen_ker0  1160-1161
private RBM.BA.step34Gen_cmp_band  1209-1210
private RBM.BA.step34Gen_cmp_half  1212-1215
private RBM.BA.step34Gen_cmp_neg  1217-1223
### RBM3D.Chain.Step34RGen  (13 unreached of 25)
RBM.BA.Step34RGenCheck.stStep3RegIII_holds_of_gen  541-546
RBM.BA.Step34RGenCheck.stStep3RegI_holds_of_gen  548-558
RBM.BA.Step34RGenCheck.stStep3II_holds_of_gen  560-570
RBM.BA.Step34RGenCheck.stStep4I_holds_of_gen  572-579
RBM.BA.Step34RGenCheck.stStep4II_holds_of_gen  581-588
private RBM.BA.Step34RGenCheck.Step34RGen_band_Kbound  606-608
private RBM.BA.Step34RGenCheck.Step34RGen_band_Kward  610-612
private RBM.BA.Step34RGenCheck.Step34RGen_fam3  614-618
RBM.BA.Step34RGenCheck.inst_step3RegIIIgL  620-634
RBM.BA.Step34RGenCheck.inst_step3RegIgL  636-654
RBM.BA.Step34RGenCheck.inst_step3IIgL  656-673
RBM.BA.Step34RGenCheck.inst_step4RgL  675-690
RBM.BA.Step34RGenCheck.inst_step34Mono  692-709
### RBM3D.Chain.Step5CasesGen  (2 unreached of 19)
RBM.BA.step5CasesGen_wardIdent_band  196-201
private RBM.BA.Step5CasesGen_wardIIgL_band  728-737
### RBM3D.Chain.Step5Gen  (28 unreached of 57)
RBM.BA.STNewKLKLAtgL'  148-161
RBM.BA.STNewKLKLgL'  163-165
RBM.BA.STTailtoTailgL'  176-182
RBM.BA.STStep5gL  230-230
RBM.BA.bandFM_STDecayStrongU  263-264
RBM.BA.bandFM_STStep5Concl  266-267
RBM.BA.bandFM_STLK2  269-270
RBM.BA.bandFM_STELKLK  272-273
RBM.BA.bandFM_STWardIIConcl  278-279
RBM.BA.bandFM_STPfConcl  281-282
RBM.BA.bandFM_STIniTermConcl  284-289
private RBM.BA.Step5Gen_abs_le_of_im  302-314
RBM.BA.stNewKLKLgL'_band  316-326
RBM.BA.stTailtoTailgL'_band  328-347
RBM.BA.STIngR5_iff_gL  374-382
RBM.BA.STStep5R_iff_gL  386-391
RBM.BA.STStep5I_iff_gL  393-396
RBM.BA.STStep5II_iff_gL  398-401
RBM.BA.STStep5III_iff_gL  403-406
RBM.BA.STStep5IV_iff_gL  408-411
RBM.BA.STStep5_iff_gL  413-416
RBM.BA.STIniTermI_iff_gL  434-438
RBM.BA.STIniTermII_iff_gL  450-456
RBM.BA.STWardII_iff_gL  458-462
RBM.BA.STPfStep5_iff_gL  464-468
private RBM.BA.Step5Gen_cm0  606-607
private RBM.BA.Step5Gen_H0  609-609
private RBM.BA.Step5Gen_im_zero  611-618
### RBM3D.Chain.Step5KerGen  (4 unreached of 16)
RBM.BA.stTailtoTailgL'_holds_band  396-399
private RBM.BA.Step5KerGen_thDecay_sz0  452-456
private RBM.BA.Step5KerGen_szH  477-483
private RBM.BA.Step5KerGen_carrierH  485-494
### RBM3D.Chain.Step6Gen  (59 unreached of 94)
RBM.BA.STExp2UgL_iff  78-82
RBM.BA.STStep6RgL  114-118
RBM.BA.STStep6IgL  126-127
RBM.BA.STStep6IIgL  128-128
RBM.BA.STStep6IIIgL  129-129
RBM.BA.STStep6IVgL  130-130
RBM.BA.STStep6gL  131-131
RBM.BA.ST_step6R_of_anygL  135-142
RBM.BA.STExpIntQConclgL  279-291
RBM.BA.STExpIniIConclgL  293-303
RBM.BA.STImproveExpAvergL  315-320
RBM.BA.STExpIntIgL  374-379
RBM.BA.STExpIniIgL  381-383
private RBM.BA.Step6Gen_STthetaOp_eq  393-404
RBM.BA.bandFM_STExpErr  406-407
RBM.BA.bandFM_STExpELKLK  409-410
RBM.BA.bandFM_STExpEGt  412-413
RBM.BA.bandFM_STExpDrift  415-416
RBM.BA.bandFM_STExpQsrc  418-423
RBM.BA.bandFM_STExp2U  425-425
RBM.BA.bandFM_STStep2Core  427-427
RBM.BA.bandFM_STStep6Concl  429-429
RBM.BA.bandFM_STExpAvgAt  431-431
RBM.BA.bandFM_STExpAvgU  433-433
RBM.BA.bandFM_STExpLKLKHiConcl  435-436
RBM.BA.bandFM_STExpEGtHiConcl  438-439
RBM.BA.bandFM_STExpDriftHiConcl  441-442
RBM.BA.bandFM_STExpDriftLoConcl  444-445
RBM.BA.bandFM_STExpDriftDecayConcl  447-448
RBM.BA.bandFM_STExpWardIIConcl  450-451
RBM.BA.bandFM_STExpWardIConcl  453-457
RBM.BA.bandFM_STExpIntConcl  459-464
RBM.BA.bandFM_STExpIniIConcl  466-470
RBM.BA.bandFM_STExpDuhEq_to_gL  472-478
RBM.BA.bandFM_STExpDuhEqQ  480-485
RBM.BA.bandFM_STExpIntQConcl  487-491
RBM.BA.Step6Gen_ingR6_iff_congr  503-519
RBM.BA.Step6Gen_ingR6_of_gL  521-529
RBM.BA.STIngR6_iff_gL  531-537
RBM.BA.STStep6R_iff_gL  539-544
RBM.BA.STStep6I_iff_gL  546-548
RBM.BA.STStep6II_iff_gL  550-552
RBM.BA.STStep6III_iff_gL  554-556
RBM.BA.STStep6IV_iff_gL  558-560
RBM.BA.STStep6_iff_gL  562-564
RBM.BA.STImproveExpAver_iff_gL  574-577
RBM.BA.STExpLKLKHi_iff_gL  579-583
RBM.BA.STExpDriftLo_iff_gL  585-589
RBM.BA.STExpDriftDecay_iff_gL  591-595
RBM.BA.STExpWardI_iff_gL  597-601
RBM.BA.STExpWardII_iff_gL  603-607
RBM.BA.STExpIniI_iff_gL  609-613
RBM.BA.STExpIntIII_of_gL  618-624
RBM.BA.STExpIntIV_of_gL  626-632
RBM.BA.STExpIntII_of_gL  634-643
RBM.BA.STExpIntI_of_gL  645-654
private RBM.BA.Step6Gen_flowE_lt_two  656-663
RBM.BA.STExpDuhamelZ_to_gL  665-674
RBM.BA.STExpDuhamelQ_to_gL  676-684
### RBM3D.Chain.Step6KitGen  (14 unreached of 37)
RBM.BA.LWAvgLawgL_of_STAvgUgL_at  138-148
RBM.BA.st6_expAvgU_of_ping  337-352
RBM.BA.st6_caseI_coreg  598-658
RBM.BA.ST_step6_caseIII_of_pinsgL  674-711
RBM.BA.ST_step6_caseIV_of_pinsgL  713-743
RBM.BA.ST_step6_caseII_of_pinsgL  745-791
RBM.BA.ST_step6_caseI_of_pinsgL  793-839
RBM.BA.st6_GdecayW_of_zerog  849-879
RBM.BA.ST_step6R_monogL  883-891
private RBM.BA.Step6KitGen_K1_band  908-911
private RBM.BA.Step6KitGen_Ker_band  913-918
private RBM.BA.Step6KitGen_hg_band  1057-1060
private RBM.BA.Step6KitGen_KerF_band  1062-1068
private RBM.BA.Step6KitGen_KerFR1_band  1070-1076
### RBM3D.Chain.StepDecompGen  (40 unreached of 100)
RBM.BA.hermTestFunLoopN_of_Of  119-124
private RBM.BA.StepDecompGen_wd_nil  184-186
RBM.BA.qvPropagatedN_of_Ng  517-525
RBM.BA.bandStep2_ZfamN  614-621
RBM.BA.bandStep2_SubGaussFormN  653-655
RBM.BA.UN_stepZCNg  810-821
RBM.BA.UN_stepYCNg  900-926
RBM.BA.subGaussStopNg_zvecNg  938-983
RBM.BA.stepDecompGen_band_loopFam  993-999
RBM.BA.stepDecompGen_band_ZvecN_eq_stepZCN  1001-1011
RBM.BA.stepDecompGen_band_kernel  1013-1022
RBM.BA.stepDecompGen_band_Ugen_stepZCN  1024-1039
RBM.BA.stepDecompGen_band_martIncN_eq_stepXiCN  1041-1052
RBM.BA.stepDecompGen_band_YvecN_eq_stepYCN  1054-1066
RBM.BA.stepDecompGen_band_Ugen_stepYCN  1068-1084
RBM.BA.stepDecompGen_band_subGaussStopN_zvecN  1086-1117
private RBM.BA.StepDecompGenCheck.E0  1134-1134
private RBM.BA.StepDecompGenCheck.s0  1135-1135
private RBM.BA.StepDecompGenCheck.t0  1136-1136
private RBM.BA.StepDecompGenCheck.K0  1137-1137
private RBM.BA.StepDecompGenCheck.Ψ0  1138-1138
private RBM.BA.StepDecompGenCheck.Cm0  1139-1139
private RBM.BA.StepDecompGenCheck.σ3  1140-1140
private RBM.BA.StepDecompGenCheck.b3  1141-1141
private RBM.BA.StepDecompGenCheck.hE0  1143-1143
private RBM.BA.StepDecompGenCheck.hL0  1144-1144
private RBM.BA.StepDecompGenCheck.hW0  1145-1145
private RBM.BA.StepDecompGenCheck.hst0  1146-1146
private RBM.BA.StepDecompGenCheck.ht10  1147-1147
private RBM.BA.StepDecompGenCheck.hj0  1148-1148
private RBM.BA.StepDecompGenCheck.hj1  1149-1149
private RBM.BA.StepDecompGenCheck.data  1151-1155
RBM.BA.StepDecompGenCheck.hermTestFunLoopNOf_instance  1157-1172
private RBM.BA.StepDecompGenCheck.U3  1206-1209
private RBM.BA.StepDecompGenCheck.hΔ  1211-1211
private RBM.BA.StepDecompGenCheck.pathH_zero  1213-1215
private RBM.BA.StepDecompGenCheck.A₀3  1217-1218
private RBM.BA.StepDecompGenCheck.AbCN_eq  1220-1222
private RBM.BA.StepDecompGenCheck.c3  1224-1226
private RBM.BA.StepDecompGenCheck.c3_nonneg  1228-1228
### RBM3D.Chain.ZeroModeGen  (25 unreached of 48)
RBM.BA.zeroModeGen_X_band  59-63
RBM.BA.zeroModeGen_rowSum_band  65-72
RBM.BA.zeroModeGen_colSum_band  74-81
RBM.BA.zeroModeGen_kerSums_band  83-89
RBM.BA.zeroModeGen_isUnit_band  91-97
RBM.BA.zeroModeGen_projMat_comm_thetaKer  133-141
private RBM.BA.ZeroModeGen_ThetaN_eq  151-157
RBM.BA.zeroModeOp_ThetaNg  169-176
RBM.BA.zeroModeSet_ThetaNg  178-184
RBM.BA.zeroModeGen_wardCls_band  297-315
RBM.BA.QopAlgebra_col_sum_uKerg  426-432
private RBM.BA.ZeroModeGen_uKer_colConst  447-457
RBM.BA.QopAlgebra_UN_sumZerog  484-519
RBM.BA.QopAlgebra_commutator_UNg  549-561
private RBM.BA.ZeroModeGenInst.zmgSigma  672-673
private RBM.BA.ZeroModeGenInst.zmgE  675-675
private RBM.BA.ZeroModeGenInst.zmgS  676-676
private RBM.BA.ZeroModeGenInst.zmgT  677-677
private RBM.BA.ZeroModeGenInst.zmgK  678-678
private RBM.BA.ZeroModeGenInst.zmgDelta  680-681
private RBM.BA.ZeroModeGenInst.zmgDelta_ne  683-685
private RBM.BA.ZeroModeGenInst.zmgIdiff_card  687-687
private RBM.BA.ZeroModeGenInst.zmgVartheta  825-827
private RBM.BA.ZeroModeGenInst.zmgA0  829-831
private RBM.BA.ZeroModeGenInst.zmgA0_sum  833-834
### RBM3D.Defs.Domination  (22 unreached of 27)
RBM.detDom_iff  62-65
RBM.UnifDetDom.of_eventually_le_const_mul  76-81
RBM.UnifDetDom.of_le  83-84
RBM.UnifDetDom.refl  86-88
RBM.UnifDetDom.mono_left  90-94
RBM.UnifDetDom.mono_right  96-101
RBM.UnifDetDom.trans  108-117
RBM.UnifDetDom.add  119-125
RBM.UnifDetDom.mul  127-141
RBM.UnifDetDom.const_mul  143-149
RBM.UnifDetDom.const_mul_left  151-154
RBM.UnifDetDom.const_mul_right  156-161
RBM.UnifDetDom.add_left  163-167
RBM.DetDom.of_eventually_le_const_mul  175-177
RBM.DetDom.refl  179-180
RBM.DetDom.trans  182-183
RBM.DetDom.add  185-186
RBM.DetDom.mul  188-190
RBM.DetDom.const_mul_left  192-194
RBM.DetDom.const_mul_right  196-198
RBM.DetDom.smul_left  200-202
RBM.DetDom.add_left  204-205
### RBM3D.Defs.Lattice  (2 unreached of 15)
RBM.torusDiam  73-75
RBM.zdistD_le_torusDiam  77-78
### RBM3D.Defs.Semicircle  (1 unreached of 37)
RBM.lemT_eq  255-261
### RBM3D.Defs.SemicircleIntegral  (7 unreached of 7)
private RBM.semicircleIntegral_sub_ne  31-36
private RBM.semicircleIntegral_k  38-40
private RBM.semicircleIntegral_k_continuous  42-45
private RBM.semicircleIntegral_subst  47-95
private RBM.semicircleIntegral_fold  97-113
private RBM.semicircleIntegral_contour  115-184
RBM.msc_eq_integral  186-217
### RBM3D.Defs.Sizes  (10 unreached of 47)
RBM.Gauss.SizesInst.sz0_values  267-270
RBM.Gauss.SizesInst.sz0_lam_sq  334-338
RBM.Gauss.SizesInst.scales_sz0  340-352
RBM.Gauss.SizesInst.sz0_lam_tendsto  354-360
RBM.Gauss.SizesInst.card_Iblk_sz0  363-365
RBM.Gauss.SizesInst.card_Idx_sz0  367-369
RBM.Gauss.SizesInst.zdistInf_inst  371-375
RBM.Gauss.SizesInst.W_le_size_sz0  379-382
RBM.Gauss.SizesInst.size_le_W_sz0  384-387
RBM.Gauss.SizesInst.sz0_locDomain  403-415
### RBM3D.Defs.StochDom  (21 unreached of 23)
RBM.badSet  75-77
RBM.StochDom  79-82
RBM.NormStochDom  84-86
RBM.HighProb  88-90
RBM.HighProbIn  92-94
RBM.StochDom.of_subset  102-109
RBM.StochDom.of_subset_union  111-126
RBM.StochDom.of_eventually_empty  128-133
RBM.StochDom.of_unifDetDom  135-142
RBM.StochDom.refl  144-152
RBM.StochDom.trans  154-165
RBM.StochDom.add  167-175
RBM.StochDom.mul  177-193
RBM.StochDom.const_mul_left  195-209
RBM.StochDom.const_mul_right  211-227
RBM.StochDom.of_forall_le  229-267
RBM.StochDom.highProb  269-276
RBM.HighProb.mono  284-289
RBM.HighProb.inter  291-303
RBM.HighProb.biInter  305-322
RBM.HighProb.highProbIn  324-329
### RBM3D.Defs.StochDomAt  (46 unreached of 84)
RBM.stochDom_iff_at_id  65-68
RBM.Gauss.highProb_iff_at_id  85-87
RBM.Gauss.Sizes.precPT_of_le  150-162
RBM.StochDomAt.of_unifDetDom  383-397
RBM.NormStochDomAt  545-550
RBM.normStochDom_iff_at_id  552-555
RBM.StochDomAt.of_add_le  665-687
RBM.Gauss.StochDomAtInst.obs  744-746
RBM.Gauss.StochDomAtInst.obs_nonneg  748-748
RBM.Gauss.StochDomAtInst.obs_le_one  750-751
RBM.Gauss.StochDomAtInst.obs_nonconst  753-756
RBM.Gauss.StochDomAtInst.tendsto_sz0_size  758-758
RBM.Gauss.StochDomAtInst.Xi  760-762
RBM.Gauss.StochDomAtInst.Ze  763-763
RBM.Gauss.StochDomAtInst.Ch  764-764
RBM.Gauss.StochDomAtInst.Ze_nonneg  766-767
RBM.Gauss.StochDomAtInst.Ch_nonneg  769-770
RBM.Gauss.StochDomAtInst.Xi_nonneg  772-772
RBM.Gauss.StochDomAtInst.prec_Xi_Ze  774-777
RBM.Gauss.StochDomAtInst.prec_Ze_Ch  779-780
RBM.Gauss.StochDomAtInst.stochDomAt_Xi_Ch  782-785
RBM.Gauss.StochDomAtInst.stochDomAt_id_Ze  787-791
RBM.Gauss.StochDomAtInst.stochDom_Ze  793-795
RBM.Gauss.StochDomAtInst.highProbAt_id_Ze  797-801
RBM.Gauss.StochDomAtInst.whp_Xi  803-807
RBM.Gauss.StochDomAtInst.precPT_Xi_Ze  809-813
RBM.Gauss.StochDomAtInst.stochDomAt_Fin2  815-823
RBM.Gauss.StochDomAtInst.sz0_self_le_size  846-852
RBM.Gauss.StochDomAtInst.stochDomAt_add  857-858
RBM.Gauss.StochDomAtInst.stochDomAt_mul  860-861
RBM.Gauss.StochDomAtInst.stochDomAt_const_mul_left  863-865
RBM.Gauss.StochDomAtInst.stochDomAt_const_mul_right  867-869
RBM.Gauss.StochDomAtInst.stochDomAt_of_subset  871-872
RBM.Gauss.StochDomAtInst.stochDomAt_precomp  874-876
RBM.Gauss.StochDomAtInst.stochDomAt_of_le_left  878-881
RBM.Gauss.StochDomAtInst.stochDomAt_zero_empty  883-889
RBM.Gauss.StochDomAtInst.stochDomAt_of_unifDetDom  891-897
RBM.Gauss.StochDomAtInst.highProbAt_good  899-901
RBM.Gauss.StochDomAtInst.highProbAt_inter  903-906
RBM.Gauss.StochDomAtInst.highProbAt_mono  908-909
RBM.Gauss.StochDomAtInst.highProbAt_univ_ev  911-913
RBM.Gauss.StochDomAtInst.highProbAt_biInter  915-922
RBM.Gauss.StochDomAtInst.highProbAt_nonempty  940-942
RBM.Gauss.StochDomAtInst.stochDomAt_of_add_le  944-952
RBM.Gauss.StochDomAtInst.stochDomAt_of_highProb_add  954-965
RBM.Gauss.StochDomAtInst.stochDomAt_section  989-995
### RBM3D.Endpoints  (29 unreached of 78)
RBM.Endpoints.calB_antitone  274-290
RBM.Endpoints.calB_dist_compare  299-340
RBM.Endpoints.calB_distB_compare  342-361
RBM.Endpoints.prec_of_explicit  399-417
RBM.Endpoints.Inst.zI  549-550
RBM.Endpoints.Inst.zI_dom  552-552
RBM.Endpoints.Inst.zI_im_pos  554-554
RBM.Endpoints.Inst.zI_im_le  556-556
RBM.Endpoints.Inst.zI_re_le  558-558
RBM.Endpoints.Inst.inst_bridge_loc  607-615
RBM.Endpoints.Inst.inst_bridge_que  617-623
RBM.Endpoints.Inst.szE  628-634
RBM.Endpoints.Inst.szLo  636-637
RBM.Endpoints.Inst.szUp  639-640
RBM.Endpoints.Inst.szE_size_le  642-650
RBM.Endpoints.Inst.szE_bandwidth  652-659
RBM.Endpoints.Inst.szE_tendsto  661-668
RBM.Endpoints.Inst.szLo_admissible  670-677
RBM.Endpoints.Inst.szUp_admissible  679-684
RBM.Endpoints.Inst.inst_locSC_lo  686-692
RBM.Endpoints.Inst.inst_locSC_up  694-700
RBM.Endpoints.Inst.inst_QUE_up  702-711
RBM.Endpoints.Inst.domain_extreme  716-725
RBM.Endpoints.Inst.locBad1_empty_kappa  727-730
RBM.Endpoints.Inst.im_mE_edge  732-735
RBM.Endpoints.Inst.que2BadMat_univ  738-766
RBM.Endpoints.Inst.que2BadMat_empty_zero  768-777
RBM.Endpoints.Inst.inst_calB  780-785
RBM.Endpoints.Inst.inst_distB_compare  787-794
### RBM3D.Evolution.CltFar  (4 unreached of 77)
private RBM.Gauss.Sizes.cltFar_zCL_im  1869-1872
private RBM.Gauss.Sizes.cltFar_zCL_E  1874-1876
private RBM.Gauss.Sizes.cltFar_tCL_lt  1878-1883
private RBM.Gauss.Sizes.cltFar_sCL_lt  1885-1886
### RBM3D.Evolution.CltFarG  (6 unreached of 24)
RBM.BA.bandFM_STThPropsg  907-913
RBM.BA.bandFM_STKpropsg  915-920
RBM.BA.stCltFar_of_gL  922-948
private RBM.BA.cltFarG_chk_s1  965-966
private RBM.BA.cltFarG_chk_Th  968-970
private RBM.BA.cltFarG_chk_K  972-975
### RBM3D.Evolution.CltGood  (16 unreached of 38)
RBM.Evol.HClt  61-67
RBM.Evol.CltGmaxConcl  82-88
RBM.Evol.CltGmaxWhp  90-94
RBM.Evol.CltFarEntryConcl  96-106
RBM.Evol.CltFarEntryWhp  108-114
RBM.Evol.CltGoodConcl  116-122
RBM.Evol.CltGoodWhp  124-130
private RBM.Evol.cltGood_gEntry_meas  138-144
private RBM.Evol.cltGood_norm_gEntry_false  171-180
private RBM.Evol.cltGood_exists_true  182-191
private RBM.Evol.cltGood_STWB_le  411-418
RBM.Evol.cltGmax_whp  420-488
RBM.Evol.cltFarEntry_whp  496-558
RBM.Evol.cltGood_whp  566-619
RBM.Gauss.Step5Inst.cltGood_hclt_szCL  961-965
RBM.Gauss.Step5Inst.cltGood_hCltOf_szCL  998-1034
### RBM3D.Evolution.CltMoments1  (22 unreached of 92)
private RBM.Evol.cltMom1_sum_sub  222-225
RBM.Evol.cltMom1_clusterSum_nonneg  838-842
RBM.Evol.cltMom1_clusters  846-880
RBM.Evol.cltMom1_iso_hyp_iff  891-899
RBM.Evol.cltMom1_scale_ell_le  1165-1168
RBM.Evol.cltMom1_cluster_sum  1243-1293
RBM.Evol.cltMom1_cluster_sum_C4  1338-1349
RBM.Evol.cltMom1_simplecalculus_ell  1619-1652
RBM.Evol.cltMom1_exponent_identity  1662-1665
RBM.Evol.cltMom1_exponent_count_eq  1708-1727
RBM.Evol.cltMom1_prod_exponent_exact  1729-1757
private RBM.Evol.cltMom1_a₂  1946-1950
private RBM.Evol.cltMom1_b  1952-1953
private RBM.Evol.cltMom1_b_dist  1955-1957
RBM.Evol.cltMom1_cluster_inst  1959-1964
RBM.Evol.cltMom1_b_paired  1966-1976
private RBM.Evol.cltMom1_xi  1996-1998
private RBM.Evol.cltMom1_c  2078-2083
private RBM.Evol.cltMom1_c_pos  2085-2091
private RBM.Evol.cltMom1_z  2094-2095
private RBM.Evol.cltMom1_z_nonneg  2097-2102
private RBM.Evol.cltMom1_z_hzu  2104-2120
### RBM3D.Evolution.CltMoments2  (36 unreached of 98)
private RBM.Evol.cltMom2_stcltX_false'  1136-1139
private RBM.Evol.cltMom2_unifBool  1215-1217
private RBM.Evol.instIsProbabilityMeasureBoolCltMom2_unifBool  1219-1220
private RBM.Evol.cltMom2_signY  1222-1223
private RBM.Evol.cltMom2_signY_norm  1225-1226
private RBM.Evol.cltMom2_signY_int  1228-1233
private RBM.Evol.cltMom2_a₂  1235-1236
private RBM.Evol.cltMom2_β0  1238-1238
private RBM.Evol.cltMom2_β0_win  1240-1240
private RBM.Evol.cltMom2_c  1242-1246
private RBM.Evol.cltMom2_c_pos  1248-1253
private RBM.Evol.cltMom2_Z0  1256-1258
private RBM.Evol.cltMom2_Z0_prof  1261-1271
private RBM.Evol.cltMom2_toy_hZ  1273-1280
private RBM.Evol.cltMom2_toy_hzu  1282-1301
private RBM.Evol.cltMom2_toy_hdom  1303-1314
private RBM.Evol.cltMom2_toy_hiso  1316-1329
private RBM.Evol.cltMom2_β1  1354-1355
private RBM.Evol.cltMom2_c40  1357-1359
private RBM.Evol.cltMom2_c40_pos  1361-1366
private RBM.Evol.cltMom2_z40  1369-1372
private RBM.Evol.cltMom2_z40_nonneg  1374-1379
private RBM.Evol.cltMom2_z40_bound  1381-1401
private RBM.Evol.cltMom2_domHyp_zero  1422-1444
private RBM.Evol.cltMom2_isoHyp_envelope  1446-1477
private RBM.Evol.cltMom2_sCL_lt  1479-1480
private RBM.Evol.cltMom2_lam_pos  1482-1483
private RBM.Evol.cltMom2_lam_le  1485-1486
private RBM.Evol.cltMom2_tCL_nonneg  1488-1492
private RBM.Evol.cltMom2_tCL_lt  1494-1499
private RBM.Evol.cltMom2_log_W_ge  1501-1506
private RBM.Evol.cltMom2_log_W_ge40  1508-1513
private RBM.Evol.cltMom2_mE0  1515-1520
private RBM.Evol.cltMom2_zCL_im  1578-1581
private RBM.Evol.cltMom2_zCL_E  1583-1585
private RBM.Evol.cltMom2_zCL_mE  1587-1597
### RBM3D.Evolution.CltMoments2G  (4 unreached of 28)
private RBM.BA.cltMom2G_chk_H  583-587
private RBM.BA.cltMom2G_chk_Th  589-630
private RBM.BA.cltMom2G_chk_E  632-637
private RBM.BA.cltMom2G_chk_Th0  639-641
### RBM3D.Evolution.CltPath  (44 unreached of 60)
RBM.Evol.cltYo  63-65
RBM.Evol.cltYoOf  72-75
RBM.Evol.cltCoefSum  83-85
RBM.Evol.CltPathBound  125-136
RBM.Evol.CltPathBoundOf  151-161
private RBM.Evol.cltpath_gEntry_le  204-209
RBM.Evol.cltPath_boundOf  341-345
private RBM.Evol.cltpath_evalAt_zero  347-349
private RBM.Evol.cltpath_good_zero  351-353
RBM.Evol.cltPathMulti_bound  355-360
RBM.Evol.cltPath_bound  362-366
private RBM.Evol.cltpath_blk_zero  386-389
private RBM.Evol.cltpath_zdistInf_zero  391-392
private RBM.Evol.cltpath_Hflow_zero  394-397
private RBM.Evol.cltpath_gEntry_diag  399-416
private RBM.Evol.cltpath_gEntry_zero  418-424
private RBM.Evol.cltpath_chk_z_ne  426-428
private RBM.Evol.cltpath_chkForm  430-435
private RBM.Evol.cltpath_chk_local  437-460
private RBM.Evol.cltpath_chk_sum  462-472
private RBM.Evol.cltpath_chk_L  477-477
private RBM.Evol.cltpath_chk_W  478-478
private RBM.Evol.cpw  480-482
private RBM.Evol.cpw_eq  484-485
private RBM.Evol.cpw_ge  487-488
private RBM.Evol.cpw_le  490-495
private RBM.Evol.cpS  497-498
private RBM.Evol.cpS_pos  500-500
private RBM.Evol.cltpath_chk_step  502-505
private RBM.Evol.cpx  507-509
private RBM.Evol.cpx_far  511-529
private RBM.Evol.cltpath_chk_good  532-549
private RBM.Evol.cpc  551-552
private RBM.Evol.cltpath_chk_szCL  554-575
private RBM.Evol.cltpath_chk_szCL_multi  578-599
private RBM.Evol.cpm  603-603
private RBM.Evol.cpm_im  605-606
private RBM.Evol.cpm_ne  608-608
private RBM.Evol.cpH  610-612
private RBM.Evol.cpH_herm  614-617
private RBM.Evol.cltpath_chk_goodOf  619-637
private RBM.Evol.cltpath_chk_szCLOf  639-660
private RBM.Evol.cltpath_chk_szCLOf_multi  662-682
private RBM.Evol.cltpath_chk_nondeg  684-692
### RBM3D.Evolution.CltResolvent  (51 unreached of 98)
RBM.Evol.cltY  105-109
RBM.Evol.cltYOf  111-114
RBM.Evol.CltDerivEvalMulti  160-176
RBM.Evol.CltDerivEval  178-190
RBM.Evol.CltDerivEvalOf  207-219
RBM.Evol.CltEtaLower  224-230
RBM.Evol.CltEvalDetLeMulti  239-250
RBM.Evol.CltEvalDetLe  252-260
RBM.Evol.CltEvalDetLeOf  272-280
RBM.Evol.cltDeriv_eval_leOf  646-649
RBM.Evol.cltDeriv_evalMulti_le  651-655
RBM.Evol.cltDeriv_eval_le  657-661
RBM.Evol.cltEta_lower  714-718
RBM.Evol.cltEval_det_leOf  800-803
RBM.Evol.cltEval_detMulti_le  805-810
RBM.Evol.cltEval_det_le  812-816
private RBM.Evol.cltres_chk_z_im  941-943
private RBM.Evol.cltres_chk_z_ne  945-946
private RBM.Evol.cltres_chk_dir  948-952
private RBM.Evol.cltres_chk_g  954-961
private RBM.Evol.cltres_chk_gr  963-967
private RBM.Evol.cltres_chk_herm  969-971
private RBM.Evol.cltres_chk_entry  973-977
private RBM.Evol.cltres_chk_gvar  979-992
private RBM.Evol.cltres_chk_offdiag  994-1016
private RBM.Evol.cltres_chk_M1  1018-1023
private RBM.Evol.cltres_chk_M2  1025-1037
private RBM.Evol.cltres_chkG  1039-1041
private RBM.Evol.cltres_chk_M3  1043-1051
private RBM.Evol.cltres_chkForm  1053-1058
private RBM.Evol.cltres_chkForm_ne  1060-1062
private RBM.Evol.cltres_chkForm_le  1064-1068
private RBM.Evol.cltres_chk_M4  1070-1081
private RBM.Evol.cltres_chk_M4Multi  1083-1093
private RBM.Evol.cltres_chk_R  1095-1102
private RBM.Evol.cltres_chk_E4  1104-1107
private RBM.Evol.cltres_chk_M5  1109-1117
private RBM.Evol.cltres_chk_M5Multi  1119-1126
private RBM.Evol.cltres_chkm  1131-1131
private RBM.Evol.cltres_chkm_im  1133-1134
private RBM.Evol.cltres_chk_gOf  1136-1141
private RBM.Evol.cltres_chk_E4Of  1143-1147
private RBM.Evol.cltres_chk_M4Of  1149-1158
private RBM.Evol.cltres_chk_M4MultiOf  1160-1169
private RBM.Evol.cltres_chk_M5Of  1171-1179
private RBM.Evol.cltres_chk_M5MultiOf  1181-1188
private RBM.Evol.cltres_chk_ckfacts  1190-1192
private RBM.Evol.cltres_chk_half  1194-1218
private RBM.Evol.cltres_chk_near  1220-1229
private RBM.Evol.cltres_chk_adj  1231-1238
private RBM.Evol.cltres_chk_witness  1240-1258
### RBM3D.Evolution.CltStep  (13 unreached of 54)
RBM.Evol.cltStep_Xo  68-74
RBM.Evol.cltStep_Gamma  76-79
private RBM.Evol.cltStep_gEntry_meas  100-104
private RBM.Evol.cltStep_eval_meas  106-111
private RBM.Evol.cltStep_ck_pos  712-718
RBM.Evol.cltStep  931-984
RBM.Evol.cltStep_pairForm_eval  1071-1079
RBM.Evol.cltStep_loopForm_eval  1226-1232
RBM.Evol.cltStep_loopForm_stcltB  1333-1345
RBM.Gauss.Step5Inst.cltStep_yCL  1591-1592
RBM.Gauss.Step5Inst.cltStep_zdistInf_yCL  1594-1610
RBM.Gauss.Step5Inst.cltStep_szCL_witness  1612-1687
RBM.Gauss.Step5Inst.cltStep_szCL_coef  1730-1735
### RBM3D.Evolution.ExpInv  (3 unreached of 42)
RBM.BA.stExpInvgL_band  569-571
private RBM.Gauss.SizesInst.expInv_chkC  597-608
private RBM.Gauss.SizesInst.expInv_chkC_inv  610-620
### RBM3D.Evolution.FarEntry  (12 unreached of 51)
RBM.Gauss.Sizes.prec_timeIcc_section  60-69
private RBM.Gauss.Sizes.farEntry_zdistInf_tri  141-151
private RBM.Gauss.Sizes.farEntry_norm_Gt_false  173-180
private RBM.Gauss.Sizes.farEntry_neighbour  523-587
private RBM.Gauss.Sizes.farEntry_gexRHS_le  589-635
RBM.Gauss.Sizes.STFarEntryAtLog  702-714
private RBM.Gauss.Sizes.farEntry_core  716-861
RBM.Gauss.Sizes.stFarEntryAtLog  864-890
RBM.Gauss.Sizes.farEntry_FarNonempty  892-897
RBM.Gauss.Sizes.farEntry_farNonempty_of  899-916
RBM.Gauss.Step5Inst.farEntry_szCL_far_nonempty  1780-1797
RBM.Gauss.Step5Inst.farEntry_szCL_stFarEntryAtLog  1799-1808
### RBM3D.Evolution.MeanFar  (10 unreached of 64)
private RBM.Gauss.Sizes.meanFar_zdistInf_zero  87-88
RBM.Gauss.Sizes.STMeanFarConcl  2084-2097
RBM.Gauss.Sizes.STMeanFar  2099-2100
RBM.Gauss.Sizes.stMeanFar  2102-2134
private RBM.Gauss.Sizes.meanFar_Tinst  2142-2145
private RBM.Gauss.Sizes.meanFar_Binst  2147-2151
private RBM.Gauss.Sizes.meanFar_Binst_tr  2153-2155
private RBM.Gauss.Sizes.meanFar_Binst_sym  2157-2159
private RBM.Gauss.Sizes.meanFar_Binst_zero  2161-2164
private RBM.Gauss.Sizes.meanFar_inst_T  2166-2188
### RBM3D.Evolution.MeanFarG  (5 unreached of 19)
private RBM.BA.meanFarG_chk_Th  720-760
private RBM.BA.meanFarG_chk_K  762-810
private RBM.BA.meanFarG_chk_m  812-822
private RBM.BA.meanFarG_chk_t1  824-828
private RBM.BA.meanFarG_chk_E  830-835
### RBM3D.Evolution.Nonzero  (1 unreached of 7)
RBM.ekDelta0  191-192
### RBM3D.Evolution.Pins  (26 unreached of 36)
RBM.EKPropT  139-149
RBM.EKTTk  151-167
RBM.ekPropT_holds  176-180
RBM.ekTTk_holds  182-196
RBM.ek_sum_fin_two  199-206
private RBM.ekE  222-222
private RBM.ekA0  224-224
private RBM.ekAz  226-227
private RBM.ek_zdistD_E  229-233
private RBM.ekA0_zero  235-235
private RBM.ek_zero_ne_E  237-241
private RBM.ekAz_vals  243-244
private RBM.ek_sqrt25  246-248
private RBM.ek_ellT_s  250-263
private RBM.ek_zdistD_far  265-268
private RBM.ek_far_point_exists  270-277
private RBM.ek_fastDecay_A0  279-289
private RBM.ek_fastDecay_Az  291-317
private RBM.ek_sumZero_Az  319-333
private RBM.ek_log5  335-340
private RBM.ekInstNdecay  342-346
private RBM.ekInstNAL  348-359
private RBM.ekInstDecay2  361-374
private RBM.ekInstNonzero  376-388
private RBM.ekInstPropT  390-397
private RBM.ekInstTTk  399-412
### RBM3D.Evolution.Prec  (15 unreached of 27)
RBM.Gauss.Sizes.stek_sumRes1_holds  356-387
private RBM.Gauss.PrecInst.norm_delta0_le  458-461
private RBM.Gauss.PrecInst.prec_delta0  463-465
private RBM.Gauss.PrecInst.decay_delta0  467-483
private RBM.Gauss.PrecInst.low_one  485-486
private RBM.Gauss.PrecInst.Az  488-490
private RBM.Gauss.PrecInst.Az_zero  492-498
private RBM.Gauss.PrecInst.norm_Az_le  500-503
private RBM.Gauss.PrecInst.prec_Az  505-507
private RBM.Gauss.PrecInst.Az_sumZero  509-523
private RBM.Gauss.PrecInst.Az_decay  525-549
private RBM.Gauss.PrecInst.decay_Az  551-562
private RBM.Gauss.PrecInst.win_sz0  564-573
private RBM.Gauss.PrecInst.win_szB_I  575-582
private RBM.Gauss.PrecInst.I_im  584-584
### RBM3D.Evolution.PropTInf  (9 unreached of 26)
private RBM.ptiB  580-580
private RBM.pti_inst_dist  582-584
private RBM.ptiInst_i  586-593
private RBM.ptiInst_ii  595-603
private RBM.ptiInst_bdry_t  605-612
private RBM.ptiInst_bdry_ut  614-621
private RBM.ptiInst_bdry_u  623-631
private RBM.ptiInst_gL  633-640
private RBM.ptiInst_uniform  642-658
### RBM3D.Evolution.SumDecay  (9 unreached of 15)
RBM.ek_ellT_sq_ge  41-64
RBM.ek_ratio_le  66-94
RBM.ek_arith_res1  210-229
RBM.ekSumDecay1_holds  321-412
private RBM.ekSDdelta0  530-532
private RBM.ekSD_sqrt25  534-536
private RBM.ekSD_fastDecay  538-551
private RBM.ekSD_ellT_s  553-566
private RBM.ekSD_zdistD_far  568-571
### RBM3D.Evolution.SumDecayZero  (23 unreached of 45)
private RBM.ekSZe  1534-1534
private RBM.ekSZprod  1536-1538
private RBM.ekSZd0  1540-1541
private RBM.ekSZde  1543-1544
private RBM.ekSZAz2  1546-1547
private RBM.ekSZAz3  1549-1550
private RBM.ekSZ_zdistD_E  1552-1557
private RBM.ekSZ_zero_ne_E  1559-1563
private RBM.ekSZ_sqrt25  1565-1567
private RBM.ekSZ_ellT_s  1569-1582
private RBM.ekSZ_zdistD_far  1584-1587
private RBM.ekSZ_log5  1589-1593
private RBM.ekSZ_dist_le_one  1595-1602
private RBM.ekSZ_support  1604-1612
private RBM.ekSZ_d0_supp  1614-1618
private RBM.ekSZ_de_supp  1620-1624
private RBM.ekSZ_prod_sumzero  1626-1647
private RBM.ekSZ_de_sum  1649-1651
private RBM.ekSZ_fastDecay  1653-1665
private RBM.ekSZ_fastDecay2  1667-1672
private RBM.ekSZ_fastDecay3  1674-1680
private RBM.ekSZ_sumZero2  1682-1686
private RBM.ekSZ_sumZero3  1688-1692
### RBM3D.Evolution.XiPins  (3 unreached of 12)
private RBM.xpBall  435-436
private RBM.xp_zero_mem  438-439
private RBM.xp_ball_dist  441-442
### RBM3D.Gauss.BlockAnderson  (12 unreached of 21)
RBM.Gauss.BlockAndersonInst.t0  169-170
RBM.Gauss.BlockAndersonInst.E0  172-173
RBM.Gauss.BlockAndersonInst.lam0  175-176
RBM.Gauss.BlockAndersonInst.m0  178-180
RBM.Gauss.BlockAndersonInst.sqrt_t0  182-184
RBM.Gauss.BlockAndersonInst.t0_pos  186-186
RBM.Gauss.BlockAndersonInst.m0_im_pos  188-192
RBM.Gauss.BlockAndersonInst.hlam0  194-196
RBM.Gauss.BlockAndersonInst.hzt0  198-205
RBM.Gauss.BlockAndersonInst.Gt_BA_sz0  207-212
RBM.Gauss.BlockAndersonInst.norm_loop_BA_sz0  228-235
RBM.Gauss.BlockAndersonInst.norm_loop_BA_sharp_sz0  237-244
### RBM3D.Gauss.Domination  (5 unreached of 13)
RBM.Gauss.MomentDom  65-72
RBM.Gauss.stochDom_of_momentDom  76-116
RBM.Gauss.stochDom_one_of_momentDom  118-131
RBM.Gauss.stochDom_Icc_of_holder  219-329
RBM.Gauss.stochDom_Icc_of_lipschitz  331-344
### RBM3D.Gauss.DominationAt  (21 unreached of 33)
RBM.Gauss.stochDomAt_Icc_of_holder_on_good  165-289
RBM.Gauss.momentDomAt_constant_one_example  293-305
RBM.Gauss.momentDomAt_of_normStochDomAt  463-477
RBM.Gauss.Sizes.seqP_eq_law  661-663
RBM.Gauss.DominationAtInst.measurable_obs  673-678
RBM.Gauss.DominationAtInst.integral_le_one  680-684
RBM.Gauss.DominationAtInst.integrable_pow_obs  686-698
RBM.Gauss.DominationAtInst.moment_obs_le  700-708
RBM.Gauss.DominationAtInst.momentDomAt_obs  710-722
RBM.Gauss.DominationAtInst.stochDomAt_obs_of_moment  724-729
RBM.Gauss.DominationAtInst.momentDomAt_obs_of_dom  731-741
RBM.Gauss.DominationAtInst.momentDomAt_obs_of_nonneg  743-750
RBM.Gauss.DominationAtInst.momentDomAt_obs_of_norm  752-763
RBM.Gauss.DominationAtInst.Yt  765-766
RBM.Gauss.DominationAtInst.stochDomAt_Icc_Yt  768-791
RBM.Gauss.DominationAtInst.integrable_abs_obs  793-797
RBM.Gauss.DominationAtInst.c0  802-804
RBM.Gauss.DominationAtInst.law_pi_c0  806-812
RBM.Gauss.DominationAtInst.gvar_c0_pos  814-820
RBM.Gauss.DominationAtInst.map_update_seqP  822-826
RBM.Gauss.DominationAtInst.stein_sin_seqP  828-847
### RBM3D.Gauss.Envelope  (3 unreached of 3)
RBM.Gauss.momentDom_of_stochDom  50-174
RBM.Gauss.momentDom_of_stochDom_of_nonneg  176-195
RBM.Gauss.momentDom_of_normStochDom  197-211
### RBM3D.Gauss.FineModel  (6 unreached of 64)
private RBM.Gauss.fineModel_Xmat_apply  264-266
RBM.Gauss.P_map_restrict  275-279
private RBM.Gauss.fineModel_Hflow_apply  440-442
RBM.Gauss.norm_Hflow_sub  498-503
RBM.Gauss.Sizes.seqP_map_restrict  520-523
RBM.Gauss.Sizes.integral_normSq_seqXmat  541-553
### RBM3D.Gauss.FlowCalculus  (15 unreached of 62)
RBM.Gauss.spectralM_im  44-45
RBM.Gauss.spectralZ_window_gap_of_bulk  66-76
RBM.Gauss.spectralM_sqrt_sq  78-81
RBM.Gauss.hasDerivAt_spectralZ_im  111-116
RBM.Gauss.continuous_Hflow_entry_time  133-137
RBM.Gauss.continuous_green_Hflow_time  202-207
RBM.Gauss.continuous_gloop_Hflow_time  290-298
RBM.Gauss.spectralMSign_eq_mSigma  461-461
RBM.Gauss.norm_gloop_HflowBlock_le_crude_on_Icc  730-741
private RBM.Gauss.flowCalculus_continuousOn_integral_abs_pow_of_envelope  751-772
private RBM.Gauss.flowCalculus_continuousOn_gloop_HflowBlock_window  776-800
private RBM.Gauss.flowCalculus_continuousOn_integral_norm_gloop_pow  802-837
RBM.Gauss.continuousOn_integral_norm_gloop_pow_spectralZ  839-853
private RBM.Gauss.flowCalculusLoop  861-864
private RBM.Gauss.flowCalculusLoop_wf  866-866
### RBM3D.Gauss.LinearForm  (5 unreached of 19)
RBM.Gauss.LinearForm.hasLaw_const_mul_coord  53-63
RBM.Gauss.LinearForm.iIndepFun_const_mul_coord  111-114
RBM.Gauss.LinearForm.eq_glue_of_congr  234-239
private RBM.Gauss.LinearForm.checkSizes  245-251
private RBM.Gauss.LinearForm.check_map_sum_const_mul_coord  253-270
### RBM3D.Gauss.LoopCoordinate  (10 unreached of 45)
RBM.Gauss.hasDerivAt_deriv_green_HflowBlock_update  222-255
RBM.Gauss.hasDerivAt_deriv_coordinateWord  337-368
RBM.Gauss.hasDerivAt_deriv_gloopProd_update  370-379
RBM.Gauss.deriv_gloop_coordinate_eq  767-774
RBM.Gauss.deriv_deriv_gloop_coordinate_eq  776-784
RBM.Gauss.measurable_integrable_actual_gloop_coordinate_derivatives  786-815
private RBM.Gauss.loopCoordinateLoop  823-826
private RBM.Gauss.loopCoordinateLoop_wf  828-828
private RBM.Gauss.loopCoordinateOff  830-832
private RBM.Gauss.loopCoordinateDiag  834-835
### RBM3D.Gauss.LoopFlowStein  (7 unreached of 44)
RBM.Gauss.wordDirectionMap_nil  89-92
RBM.Gauss.wordDirectionMap_cons  94-101
RBM.Gauss.loop_flow_derivative_actual_coordinate_chain  237-261
RBM.Gauss.flowWindow_mem  617-621
private RBM.Gauss.loopFlowSteinLoop  899-901
private RBM.Gauss.loopFlowSteinLoop_wf  903-903
private RBM.Gauss.loopFlowSteinCoord  905-906
### RBM3D.Gauss.LoopGenerator  (20 unreached of 56)
RBM.Gauss.length_spectralEdgeSplits  53-58
RBM.Gauss.HflowBlock_zero  364-370
RBM.Gauss.gloop_HflowBlock_zero  386-392
RBM.Gauss.integral_gloop_HflowBlock_zero  394-402
RBM.Gauss.trace_Eblk_mul_Eblk  475-482
RBM.Gauss.initialLoopValue_two_edges  484-500
RBM.Gauss.adjacentBlockWeight_three  587-594
RBM.Gauss.initialLoopValue_zero_of_adjacentMismatch  642-650
RBM.Gauss.initialLoopValue_all_same  652-663
RBM.Gauss.cutResolventEnvelope  676-681
RBM.Gauss.continuousOn_integral_gloop_product_window  742-797
RBM.Gauss.continuousOn_integral_gloop_product_spectralZ  799-816
RBM.Gauss.continuousOn_integral_gloop_window  818-851
RBM.Gauss.continuousOn_integral_gloop_spectralZ  853-868
private RBM.Gauss.genLoop  880-882
private RBM.Gauss.genLoop_wf  884-884
private RBM.Gauss.genLoop3  886-888
private RBM.Gauss.genLoop3_wf  890-890
private RBM.Gauss.gen_hE  892-892
private RBM.Gauss.gen_hzim  894-897
### RBM3D.Gauss.Model  (11 unreached of 15)
RBM.Gauss.vkey  77-79
RBM.Gauss.vkey_injective  81-82
RBM.Gauss.Coord  84-87
RBM.Gauss.Omega  89-90
RBM.Gauss.gvar  92-98
RBM.Gauss.P  100-102
RBM.Gauss.isProbabilityMeasure_P  104-105
RBM.Gauss.Hmat  109-117
RBM.Gauss.Hmat_isHermitian  119-128
RBM.Gauss.preimage_upd_univ_pi  142-158
RBM.Gauss.P_map_update  160-178
### RBM3D.Graph.AnpKey  (15 unreached of 59)
RBM.Graph.AnpDetGhZero  58-62
RBM.Graph.AnpDetGhStep  64-70
private RBM.Graph.anpKey_zero_prod  213-332
RBM.Graph.anpDetGh_zero  335-359
RBM.Graph.anpDetGh_of_step  647-656
RBM.Graph.anpKey_oneEdge  842-845
RBM.Graph.anpKey_oneEdge_nested  847-849
RBM.Graph.anpKey_oneEdge_ghostOK  851-853
private RBM.Graph.anpKey_zdist_three_le  855-857
private RBM.Graph.anpKey_zdistInf_three_le  859-860
RBM.Graph.anpKey_inst_zero  862-889
RBM.Graph.anpKey_inst_anp  892-903
RBM.Graph.anpKey_inst_figAux  905-909
RBM.Graph.anpKey_inst_figAux_step  911-913
RBM.Graph.anpKey_inst_ghostify  915-941
### RBM3D.Graph.AnpKey2  (156 unreached of 167)
RBM.Graph.NGraph.EndAt  59-63
RBM.Graph.NGraph.IsA1  65-69
RBM.Graph.NGraph.IsA2  71-74
RBM.Graph.NGraph.IsB1  76-79
RBM.Graph.NGraph.IsB2  81-84
RBM.Graph.NGraph.NoA2  86-88
RBM.Graph.NGraph.degS  90-92
RBM.Graph.NGraph.anpKey2_decEndAt  94-95
RBM.Graph.NGraph.anpKey2_decIsA1  97-98
RBM.Graph.NGraph.anpKey2_decIsA2  100-101
RBM.Graph.NGraph.anpKey2_decIsB1  103-104
RBM.Graph.NGraph.anpKey2_decIsB2  106-107
RBM.Graph.NGraph.anpKey2_decNoA2  109-110
RBM.Graph.anpKey2_val_eq_valOn  114-116
RBM.Graph.anpKey2_region  118-123
RBM.Graph.anpKey2_regionOne  125-129
RBM.Graph.anpKey2_fixLab  131-134
RBM.Graph.AnpDetGhRegAt  136-147
RBM.Graph.AnpIH  149-152
RBM.Graph.AnpDetGhRegStep  154-158
RBM.Graph.AnpCaseI  160-163
RBM.Graph.AnpCaseIII  165-168
RBM.Graph.AnpDetGhCaseI  170-174
RBM.Graph.AnpDetGhCaseIII  176-180
RBM.Graph.AnpDetGhCaseIV  182-186
RBM.Graph.anpDetGh_of_reg  190-256
RBM.Graph.anpKey2_half  260-266
RBM.Graph.anpKey2_reg_half  268-285
RBM.Graph.anpKey2_endTypes  287-299
RBM.Graph.anpKey2_noGhost_iff  301-306
RBM.Graph.anpKey2_ghostStep  308-315
RBM.Graph.anpKey2_caseI_ne  317-339
RBM.Graph.anpKey2_chain_append  396-404
RBM.Graph.anpKey2_chain_snoc  406-410
RBM.Graph.anpKey2_chain_end  412-415
RBM.Graph.anpKey2_endAt_ends  435-458
private RBM.Graph.anpKey2_xi_le  512-521
RBM.Graph.anpKey2_A2_factor  523-543
RBM.Graph.anpKey2_A2_val  545-561
RBM.Graph.anpDetGhReg_of_noA2  565-651
RBM.Graph.anpKey2_seg  666-671
RBM.Graph.anpKey2_seg_nil  673-673
RBM.Graph.anpKey2_seg_zero  675-676
RBM.Graph.anpKey2_seg_succ  678-679
RBM.Graph.anpKey2_seg_zero_pos  681-682
RBM.Graph.anpKey2_seg_zero_neg  684-685
RBM.Graph.anpKey2_seg_succ_pos  687-688
RBM.Graph.anpKey2_seg_succ_neg  690-691
RBM.Graph.anpKey2_seg_sublist  693-704
RBM.Graph.anpKey2_seg_nil_of_gt  706-718
RBM.Graph.anpKey2_seg_cover  720-738
RBM.Graph.anpKey2_seg_unique  740-772
RBM.Graph.anpKey2_seg_shape  774-797
RBM.Graph.anpKey2_seg_last  799-816
RBM.Graph.anpKey2_seg_snoc  818-840
RBM.Graph.anpKey2_seg_head  842-846
RBM.Graph.anpKey2_isA  854-855
RBM.Graph.anpKey2_isA_eq  857-858
RBM.Graph.anpKey2_seg_chain  860-895
RBM.Graph.anpKey2_K  903-904
RBM.Graph.anpKey2_Seg  906-907
RBM.Graph.anpKey2_P  909-910
RBM.Graph.anpKey2_ee  912-913
RBM.Graph.anpKey2_steps  915-917
RBM.Graph.anpKey2_ea  919-922
RBM.Graph.anpKey2_eb  924-927
RBM.Graph.anpKey2_own  929-930
RBM.Graph.anpKey2_pred  932-934
RBM.Graph.anpKey2_succAbove_pred  936-937
RBM.Graph.anpKey2_pred_succAbove  939-940
RBM.Graph.anpKey2_rel0  942-946
RBM.Graph.anpKey2_tgt  948-958
RBM.Graph.anpKey2_edge  960-963
RBM.Graph.anpKey2_es  965-967
RBM.Graph.anpKey2_es_length  969-970
RBM.Graph.anpKey2_fixV  972-976
RBM.Graph.anpKey2_em  978-980
RBM.Graph.anpKey2_steps_sublist  984-985
RBM.Graph.anpKey2_steps_mem_path  987-989
RBM.Graph.anpKey2_cover  991-994
RBM.Graph.anpKey2_edge_unique  996-1012
RBM.Graph.anpKey2_steps_chain  1014-1018
RBM.Graph.anpKey2_steps_shape  1020-1032
RBM.Graph.anpKey2_steps_ne_nil  1034-1045
RBM.Graph.anpKey2_noneV  1049-1053
RBM.Graph.anpKey2_tgt_none  1055-1062
RBM.Graph.anpKey2_tgt_first  1064-1075
private RBM.Graph.anpKey2_single  1077-1092
RBM.Graph.anpKey2_tgt_last  1094-1120
RBM.Graph.anpKey2_rel0_self  1124-1125
RBM.Graph.anpKey2_rel0_succAbove  1127-1131
RBM.Graph.anpKey2_rel0_ne  1133-1139
RBM.Graph.anpKey2_noneV_ne_a  1141-1148
RBM.Graph.anpKey2_noneV_ne_b  1150-1157
RBM.Graph.anpKey2_noneV_ne_inr  1159-1162
RBM.Graph.anpKey2_rel0_inj  1164-1197
RBM.Graph.anpKey2_es_get  1199-1201
RBM.Graph.anpKey2_ee_symm_snd  1203-1205
RBM.Graph.anpKey2_ee_symm_fst  1207-1209
RBM.Graph.anpKey2_ea_ee  1211-1213
RBM.Graph.anpKey2_eb_ee  1215-1218
RBM.Graph.anpKey2_lab  1220-1238
RBM.Graph.anpKey2_chain_new  1240-1284
RBM.Graph.anpKey2_seg_eq_zero  1286-1290
RBM.Graph.anpKey2_seg_eq_last  1292-1297
RBM.Graph.anpKey2_fixV_path  1299-1305
RBM.Graph.anpKey2_fixV_edge  1307-1313
RBM.Graph.anpKey2_steps_dropLast  1315-1323
RBM.Graph.anpKey2_steps_arrival  1325-1339
RBM.Graph.anpKey2_fixV_walk  1341-1372
RBM.Graph.anpKey2_fixV_visits  1374-1388
RBM.Graph.anpKey2_fixV_nested  1390-1441
RBM.Graph.anpKey2_ghost_unique  1443-1458
RBM.Graph.anpKey2_steps_first  1460-1466
RBM.Graph.anpKey2_steps_last  1468-1484
RBM.Graph.anpKey2_fixV_ghost  1486-1489
RBM.Graph.anpKey2_fixV_ghostOK  1491-1528
RBM.Graph.anpKey2_prod_eq  1532-1535
RBM.Graph.anpKey2_ep_eq  1537-1547
RBM.Graph.anpKey2_fixV_value  1549-1595
RBM.Graph.anpKey2_fixV_steps  1599-1622
RBM.Graph.anpKey2_fixV_noGhost1  1624-1634
RBM.Graph.anpKey2_fixV_noGhost2  1636-1672
RBM.Graph.anpKey2_filter_len  1674-1682
RBM.Graph.anpKey2_nSolid_sum  1684-1689
RBM.Graph.anpKey2_fixV_nSolid  1691-1694
RBM.Graph.anpKey2_seg_end_nil  1696-1702
RBM.Graph.anpKey2_fixV_end  1704-1771
RBM.Graph.anpKey2_exists_s₀  1773-1782
RBM.Graph.anpKey2_ea_unique  1784-1798
RBM.Graph.anpKey2_eb_unique  1800-1814
RBM.Graph.anpKey2_fix  1816-1878
RBM.Graph.anpDetGhStep_of_reg  1884-1888
RBM.Graph.anpDetGhRegStep_of_cases  1890-1898
RBM.Graph.anpKey2_decGhostOK  1904-1904
RBM.Graph.anpKey2_decCaseI  1906-1908
RBM.Graph.anpKey2_decCaseIII  1910-1912
RBM.Graph.anpKey2_figAuxGh  1914-1920
RBM.Graph.anpKey2_figAuxGh_ghostOK  1922-1924
RBM.Graph.anpKey2_figAuxGh_nested  1926-1928
RBM.Graph.anpKey2_figAux_ghostOK  1930-1930
RBM.Graph.anpKey2_inst_figAuxGh  1932-1939
RBM.Graph.anpKey2_eAux  1941-1942
RBM.Graph.anpKey2_eGh  1944-1945
RBM.Graph.anpKey2_inst_figAux_a2  1947-1954
RBM.Graph.anpKey2_inst_figAux_reg  1956-1960
RBM.Graph.anpKey2_inst_cover  1962-1964
RBM.Graph.anpKey2_inst_chain  1966-1970
RBM.Graph.anpKey2_inst_figAux_det  1972-1975
RBM.Graph.anpKey2_inst_half  1977-1984
RBM.Graph.anpKey2_pt  1986-1987
RBM.Graph.anpKey2_inst_reg_half  1990-2011
RBM.Graph.anpKey2_inst_endTypes  2013-2021
RBM.Graph.anpKey2_inst_caseI_ne  2023-2028
RBM.Graph.anpKey2_inst_fix  2030-2048
RBM.Graph.anpKey2_inst_fixP  2050-2053
### RBM3D.Graph.AnpKey3  (24 unreached of 25)
RBM.Graph.anpKey3_endAt_mem  61-72
RBM.Graph.anpKey3_end_solid  74-81
RBM.Graph.anpKey3_endAt_of  83-86
RBM.Graph.anpKey3_noGhost_single  88-95
RBM.Graph.anpKey3_gh2  105-107
RBM.Graph.anpKey3_gh2_props  109-163
RBM.Graph.anpKey3_endFactor  171-189
RBM.Graph.anpKey3_far_end  199-264
RBM.Graph.anpKey3_far_gen  266-313
RBM.Graph.anpKey3_far  315-341
RBM.Graph.anpKey3_prod  349-396
RBM.Graph.anpDetGhCaseI_holds  425-563
RBM.Graph.anpKey3_pi  569-570
RBM.Graph.anpKey3_figAuxMix  572-578
RBM.Graph.anpKey3_inst_figAuxGh_hyp  580-585
RBM.Graph.anpKey3_inst_figAuxGh  587-593
RBM.Graph.anpKey3_inst_figAux_hyp  595-599
RBM.Graph.anpKey3_inst_figAux  601-606
RBM.Graph.anpKey3_inst_figAuxMix  608-617
RBM.Graph.anpKey3_inst_chain  619-621
RBM.Graph.anpKey3_inst_types  623-633
RBM.Graph.anpKey3_fixV_ng_iff  635-649
RBM.Graph.anpKey3_figAuxGh_seg  651-656
RBM.Graph.anpKey3_inst_gh2  658-710
### RBM3D.Graph.AnpKey4  (30 unreached of 30)
RBM.Graph.anpKey4_ng_false  56-64
RBM.Graph.anpKey4_caseIII_ne  66-90
RBM.Graph.anpKey4_head_shape  92-118
RBM.Graph.anpKey4_last_shape  120-147
RBM.Graph.anpKey4_side  149-199
RBM.Graph.anpKey4_degS_eq  201-222
RBM.Graph.anpKey4_solid  224-265
RBM.Graph.anpKey4_gh2_props  273-338
RBM.Graph.anpKey4_gh2_edges  340-364
RBM.Graph.anpKey4_pos_false  374-397
RBM.Graph.anpKey4_pos_true  399-411
RBM.Graph.anpKey4_seg  413-467
RBM.Graph.anpKey4_lab_indep  475-485
RBM.Graph.anpKey4_factor  487-508
RBM.Graph.anpKey4_indep  510-522
RBM.Graph.anpKey4_ep_congr  524-534
RBM.Graph.anpKey4_F2  536-552
RBM.Graph.anpKey4_reduce  558-691
RBM.Graph.anpKey4_of_reduce  695-776
RBM.Graph.anpDetGhCaseIII_holds  778-785
RBM.Graph.anpKey4_figLoop  791-799
RBM.Graph.anpKey4_piLoop  801-802
RBM.Graph.anpKey4_eL  804-805
RBM.Graph.anpKey4_inst_hyp  807-817
RBM.Graph.anpKey4_inst_figLoop  819-824
RBM.Graph.anpKey4_inst_figAuxGh  826-832
RBM.Graph.anpKey4_inst_chain  834-836
RBM.Graph.anpKey4_inst_reduce  838-845
RBM.Graph.anpKey4_inst_ne_solid  847-859
RBM.Graph.anpKey4_inst_gh2  861-874
### RBM3D.Graph.AnpKey5  (14 unreached of 112)
RBM.Graph.anpKey5_decSumOrder  110-112
RBM.Graph.anpKey5_decPerPath  114-116
RBM.Graph.anpKey5_one_le_countP  158-161
RBM.Graph.anpKey5_inS_inl  228-228
RBM.Graph.anpKey5_decIsNested  1347-1348
RBM.Graph.anpKey5_figIVext  1350-1358
RBM.Graph.anpKey5_piIV  1360-1361
RBM.Graph.anpKey5_resAux  1363-1364
RBM.Graph.anpKey5_inst_figIVext  1366-1373
RBM.Graph.anpKey5_perm_two  1375-1379
RBM.Graph.anpKey5_inst_resAux  1381-1392
RBM.Graph.anpKey5_inst_figAuxGh  1394-1398
RBM.Graph.anpKey5_inst_figIVext_cert  1400-1407
RBM.Graph.anpKey5_inst_cross_inside  1409-1423
### RBM3D.Graph.AnpKey6  (19 unreached of 54)
RBM.Graph.anpKey6_order  479-494
RBM.Graph.anpKey6_valOn_le  909-920
RBM.Graph.anpDetGhCaseIV_holds  922-929
RBM.Graph.anpDetGhStep_holds  931-933
RBM.Graph.anpIH_holds  935-937
RBM.Graph.anpDetGhRegStep_holds  939-943
private RBM.Graph.anpKey6_zdist_three_le  960-962
private RBM.Graph.anpKey6_zdistInf_three_le  964-965
RBM.Graph.anpKey6_inst_data  967-988
RBM.Graph.anpKey6_inst_eval  990-1003
RBM.Graph.anpKey6_inst_det  1005-1009
RBM.Graph.anpKey6_inst_det_eval  1011-1033
RBM.Graph.anpKey6_inst_lw  1035-1038
RBM.Graph.anpKey6_inst_anp  1041-1057
RBM.Graph.anpKey6_inst_cases  1059-1067
RBM.Graph.anpKey6_inst_apply  1069-1082
RBM.Graph.anpKey6_inst_sum  1084-1096
RBM.Graph.anpKey6_inst_order  1098-1110
RBM.Graph.anpKey6_inst_union  1112-1132
### RBM3D.Graph.AuxGraph  (19 unreached of 97)
RBM.Graph.auxGraph_molSolid_length  1647-1656
RBM.Graph.auxGraph_auxVal_const  1658-1666
RBM.Graph.auxGraph_instD  1668-1674
RBM.Graph.auxGraph_instD_hM  1676-1676
RBM.Graph.auxGraph_instD_hG  1678-1680
RBM.Graph.auxGraph_instD_hGd  1682-1684
RBM.Graph.auxGraph_inst_window  1686-1692
RBM.Graph.auxGraph_figGraph_molSolid  1698-1699
RBM.Graph.auxGraph_inst_Q_molSolid  1701-1702
RBM.Graph.auxGraph_inst_Q_counters  1704-1706
RBM.Graph.auxGraph_figGraph_hext  1729-1732
RBM.Graph.auxGraph_figGraph_auxVal  1734-1738
RBM.Graph.auxGraph_instXY  1764-1770
RBM.Graph.auxGraph_instXY_normal  1772-1772
RBM.Graph.auxGraph_instXY_mol  1774-1775
RBM.Graph.auxGraph_instEll  1777-1778
RBM.Graph.auxGraph_instEll_dist  1780-1781
RBM.Graph.auxGraph_inst_Q_hxy  1803-1810
RBM.Graph.auxGraph_inst_Q_auxOrd  1812-1814
### RBM3D.Graph.AuxGraph2  (12 unreached of 62)
private RBM.Graph.auxGraph2_zdistInf_zero  88-90
RBM.Graph.lwXiSq_ge_W  174-187
private RBM.Graph.auxGraph2_entry_le_sum  1288-1295
private RBM.Graph.auxGraph2_R0  1308-1309
private RBM.Graph.auxGraph2_ρ0  1311-1313
private RBM.Graph.auxGraph2_R0_nonneg  1315-1316
private RBM.Graph.auxGraph2_ρ0_nonneg  1318-1322
private RBM.Graph.auxGraph2_ρ0_ge  1324-1324
private RBM.Graph.auxGraph2_ρ0_rad  1326-1329
private RBM.Graph.auxGraph2_Entry  1331-1335
private RBM.Graph.auxGraph2_exists_ne  1337-1345
private RBM.Graph.auxGraph2_Ugb  1414-1419
### RBM3D.Graph.AuxGraphRooted  (3 unreached of 12)
RBM.Graph.lwAuxRoot_auxValOn_const  31-38
RBM.Graph.lwAuxRoot_exists_rep  496-506
private RBM.Graph.lwAuxRoot_Dm_card  507-507
### RBM3D.Graph.BAAnpLift  (1 unreached of 9)
private RBM.Graph.BAAnpLift_zeta0  285-294
### RBM3D.Graph.BAAtom  (13 unreached of 50)
RBM.Graph.BAAtom_shadow_ext  128-134
private RBM.Graph.BAAtom_atomAdj_cases  263-280
RBM.Graph.baAtom_dist  282-319
RBM.Graph.baAtom_wedge  338-362
RBM.Graph.BAAtomInst.Gstar  964-972
RBM.Graph.BAAtomInst.Gstar_normal  974-974
RBM.Graph.BAAtomInst.Gstar_ext  976-976
RBM.Graph.BAAtomInst.xiInst  978-979
RBM.Graph.BAAtomInst.D1  1000-1007
RBM.Graph.BAAtomInst.D1_hoff  1009-1011
RBM.Graph.BAAtomInst.ell1  1013-1016
RBM.Graph.BAAtomInst.D1_term  1018-1021
RBM.Graph.BAAtomInst.ellI1  1074-1075
### RBM3D.Graph.BAAtom2  (6 unreached of 20)
RBM.Graph.BAGtoAG  387-412
RBM.Graph.baGtoAG_holds  414-526
RBM.Graph.baGtoAG_E  602-636
RBM.Graph.BAAnpAux  673-689
RBM.Graph.baAnpAux_holds  691-708
RBM.Graph.BAAtomInst2.baPQ  768-770
### RBM3D.Graph.BAAtomic  (28 unreached of 99)
RBM.Graph.BAGraph.BAAtomic_img_g  254-254
RBM.Graph.BAGraph.BAAtomic_img_ext  256-256
RBM.Graph.BAGraph.BAAtomic_img_coeff  279-279
RBM.Graph.BAImgNormal  335-337
RBM.Graph.BAImgMol  427-431
private RBM.Graph.BAAtomic_merge_dotted  562-564
RBM.Graph.BAImgNormal_holds  709-709
RBM.Graph.BAImgMol_holds  711-711
private RBM.Graph.BAAtomic_dot95  719-721
RBM.Graph.BAGraph.img95  723-730
private RBM.Graph.BAAtomic_dot95_eqRel_iff  732-745
private RBM.Graph.BAAtomic_dot95_eqSetoid  747-752
private RBM.Graph.BAAtomic_eC  754-756
private RBM.Graph.BAAtomic_eC_cls  758-758
private RBM.Graph.BAAtomic_isExt_iff  760-766
private RBM.Graph.BAAtomic_eE  768-769
private RBM.Graph.BAAtomic_eI  771-772
private RBM.Graph.BAAtomic_vmap95  774-783
private RBM.Graph.BAAtomic_vmap95_eq_iff  785-790
private RBM.Graph.BAAtomic_merge95_solid  792-793
private RBM.Graph.BAAtomic_lgraph_ext  795-797
RBM.Graph.BAGraph.img95_equiv_gen  799-861
RBM.Graph.BAGraph.img95_equiv  863-877
private RBM.Graph.BAAtomic_G0  885-894
private RBM.Graph.BAAtomic_G1  896-904
private RBM.Graph.BAAtomic_G2  906-910
private RBM.Graph.BAAtomic_G0_normal  912-912
private RBM.Graph.BAAtomic_G1_normal  913-913
### RBM3D.Graph.BAAtomic2  (10 unreached of 18)
RBM.Graph.liftG  36-37
RBM.Graph.liftC  39-45
RBM.Graph.liftC_normal  47-48
RBM.Graph.BAAtomic_vmapEquiv_apply  90-91
RBM.Graph.BAAtomic_cendsMS_liftG  185-188
RBM.Graph.BAAtomic_pathFam_liftG  190-194
RBM.Graph.BAPathLift  196-199
RBM.Graph.BAPathLift_holds  201-205
RBM.Graph.BAAtomic_counters_liftC  207-215
private RBM.Graph.BAAtomic_p2_normal  223-225
### RBM3D.Graph.BAAuxGraph2  (8 unreached of 52)
RBM.Graph.BAAuxGraph2_zdistInf_zero  92-94
RBM.Graph.BAAuxGraph2_zdistInf_le_of_zdistD  117-122
RBM.Graph.baZetaSq_ge_W  191-204
RBM.Graph.LWXigL_bandFM  1042-1046
private RBM.Graph.BAAuxGraph2_one_le_W  1057-1057
private RBM.Graph.BAAuxGraph2_ρ0  1059-1060
private RBM.Graph.BAAuxGraph2_ρ0_nonneg  1062-1062
private RBM.Graph.BAAuxGraph2_entry_le_sum  1064-1070
### RBM3D.Graph.BAAuxGraph2B  (12 unreached of 31)
RBM.Graph.baGbyZeta_hxi  765-782
private RBM.Graph.BAAuxGraph2B_one_le_W  893-893
private RBM.Graph.BAAuxGraph2B_one_le_log  895-897
private RBM.Graph.BAAuxGraph2B_Φ0  899-900
private RBM.Graph.BAAuxGraph2B_R0  901-902
private RBM.Graph.BAAuxGraph2B_ρ0  903-905
private RBM.Graph.BAAuxGraph2B_psiAll  907-919
private RBM.Graph.BAAuxGraph2B_R0_nonneg  921-922
private RBM.Graph.BAAuxGraph2B_ρ0_nonneg  924-927
private RBM.Graph.BAAuxGraph2B_ρ0_rad  929-935
private RBM.Graph.BAAuxGraph2B_sep  937-961
private RBM.Graph.BAAuxGraph2B_exists_data  1011-1015
### RBM3D.Graph.BAEngine  (4 unreached of 33)
private RBM.Graph.BAEngine_col_transpose  60-60
private RBM.Graph.BAEngine_start_not_locStd  390-402
RBM.Graph.BAEngine_pL  404-408
RBM.Graph.BAEngine_pL_locStd  410-413
### RBM3D.Graph.BAExp14a  (1 unreached of 68)
RBM.BA.BAExp14a_J_MM_le  625-632
### RBM3D.Graph.BAExp14a2  (2 unreached of 25)
RBM.BA.LWCutExp_iff  72-73
RBM.BA.band_LWCutExpG  75-77
### RBM3D.Graph.BAExp14aB  (1 unreached of 103)
RBM.BA.BAExp14a_X_le_a  418-419
### RBM3D.Graph.BAExp14b  (6 unreached of 77)
RBM.BA.BAExp14b_twTie  551-580
RBM.BA.BAExp14b_twTie_ba  582-588
RBM.BA.BAExp14b_Wk_blk  596-609
RBM.BA.BAExp14bS2Fam_block  892-901
RBM.BA.BAExp14b_twLoopX_twL2'  903-906
private RBM.BA.BAExp14b_hr0  918-921
### RBM3D.Graph.BAExp14b2  (2 unreached of 59)
private RBM.BA.BAExp14b2_hr0  1677-1680
private RBM.BA.BAExp14b2_MB0  1754-1763
### RBM3D.Graph.BAExp14b2B  (1 unreached of 40)
private RBM.BA.BAExp14b2B_U0  1097-1111
### RBM3D.Graph.BAExp14bB  (1 unreached of 74)
private RBM.BA.BAExp14b_outerDt_eq_fr  538-541
### RBM3D.Graph.BAExp14c  (4 unreached of 45)
private RBM.BA.BAExp14c_D_G  178-179
private RBM.BA.BAExp14c_D_S'  181-182
private RBM.BA.BAExp14c_blk  184-185
RBM.BA.baFoldLeafT_fold  800-817
### RBM3D.Graph.BAExp14cB  (12 unreached of 36)
RBM.BA.BAExp14cInst.rootT0_leaf  941-945
RBM.BA.BAExp14cInst.rootT0_partition_ne  947-948
RBM.BA.BAExp14cInst.rootT0_inst  950-957
RBM.BA.BAExp14cInst.rootT0_inst_identity  959-966
RBM.BA.BAExp14cInst.anchor_nW  977-978
RBM.BA.BAExp14cInst.foldT_rho0  1004-1025
RBM.BA.BAExp14cInst.foldT_anchor  1027-1030
private RBM.BA.BAExp14cInst.foldT_occurs  1032-1060
RBM.BA.BAExp14cInst.closeT_inst  1062-1065
RBM.BA.BAExp14cInst.tiedGraph  1074-1080
RBM.BA.BAExp14cInst.tiedGraph_atom  1082-1083
RBM.BA.BAExp14cInst.offsets_exist  1085-1092
### RBM3D.Graph.BAExp14d  (11 unreached of 23)
RBM.BA.BAExp14d_dataT_eq  67-75
RBM.BA.BAExp14dInst.leaf1  483-487
RBM.BA.BAExp14dInst.leaf1P  489-491
RBM.BA.BAExp14dInst.leaf1_props  493-508
private RBM.BA.BAExp14dInst.hr0  510-513
RBM.BA.BAExp14dInst.D0  515-518
RBM.BA.BAExp14dInst.Ψ0  520-521
private RBM.BA.BAExp14dInst.g0_bounds  542-552
private RBM.BA.BAExp14dInst.data_bounds  554-566
private RBM.BA.BAExp14dInst.Ψ0_pos  568-573
private RBM.BA.BAExp14dInst.ones_row  575-578
### RBM3D.Graph.BAExp14e  (2 unreached of 9)
RBM.BA.BAExp14eInst.leafPrecInst  363-370
RBM.BA.BAExp14eInst.baAllMP_counters  372-382
### RBM3D.Graph.BAExpand  (8 unreached of 54)
RBM.Graph.stein_baPoly  353-359
RBM.Graph.BAExpand_Hm_eq  372-375
RBM.Graph.baWx_baG  377-380
RBM.Graph.BAExpandInst.baS_diag  788-790
RBM.Graph.BAExpandInst.baS_row_sum  792-796
RBM.Graph.BAExpandInst.baLanlw_t0  798-811
RBM.Graph.BAExpandInst.baInstSz  813-814
RBM.Graph.BAExpandInst.baSelf_zero  864-875
### RBM3D.Graph.BAExpandId  (26 unreached of 70)
RBM.Graph.baG5Graph  72-83
RBM.Graph.BAG5Identity  85-93
RBM.Graph.BAexpandRoot  378-380
RBM.Graph.BAselClassical  382-384
RBM.Graph.baRCand_nonempty_iff  386-394
RBM.Graph.baSelClassical_isSome  396-398
RBM.Graph.baExpandIdentity_holds  584-606
RBM.Graph.BAExpandIdInst.baG5Circ  621-630
RBM.Graph.BAExpandIdInst.baG5Circ_normal  632-632
RBM.Graph.BAExpandIdInst.instP  634-636
RBM.Graph.BAExpandIdInst.instCand  638-655
RBM.Graph.BAExpandIdInst.instCand_sizes  657-661
RBM.Graph.BAExpandIdInst.instP_selected  663-663
RBM.Graph.BAExpandIdInst.baG5CircRed  665-675
RBM.Graph.BAExpandIdInst.baG5CircRed_normal  677-677
RBM.Graph.BAExpandIdInst.instPRed  679-681
RBM.Graph.BAExpandIdInst.instCandRed  683-700
RBM.Graph.BAExpandIdInst.instCandRed_sizes  702-705
RBM.Graph.BAExpandIdInst.instPRed_selected  707-707
RBM.Graph.BAExpandIdInst.baG5Graph_partition_length  709-712
RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_identity  714-720
RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_normal  722-723
RBM.Graph.BAExpandIdInst.baExpandId_inst_gg_red  725-734
RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_identity_red  736-741
RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_normal_red  743-744
RBM.Graph.BAExpandIdInst.baExpandId_inst_identity  746-753
### RBM3D.Graph.BAExpandW  (3 unreached of 45)
RBM.Graph.baGcxy  970-977
RBM.Graph.baGcxx  979-986
RBM.Graph.BAExpandWInst.baLweight_t0  990-1003
### RBM3D.Graph.BAExpandWOrd  (7 unreached of 46)
private RBM.Graph.BAExpandWOrd_β  307-307
RBM.Graph.lanlw_ord  780-795
private RBM.Graph.BAExpandWOrd_foldr_min_le  840-848
private RBM.Graph.BAExpandWOrd_scalingOrderG_le  850-862
RBM.Graph.BAExpandWOrdInst.T2315_I3  870-893
RBM.Graph.BAExpandWOrdInst.T2315_I4  895-918
RBM.Graph.BAExpandWOrdInst.T2315_D  935-981
### RBM3D.Graph.BAG5Leaf  (11 unreached of 69)
RBM.Graph.BAG5Expand  88-89
RBM.Graph.BAG5LeafInst.instCtx  1008-1011
RBM.Graph.BAG5LeafInst.instP_ord  1013-1016
RBM.Graph.BAG5LeafInst.baG5CtxLemma_inst  1018-1034
RBM.Graph.BAG5LeafInst.baG5CtxKids_inst  1036-1048
RBM.Graph.BAG5LeafInst.baAllM  1050-1054
RBM.Graph.BAG5LeafInst.baAllMP  1056-1058
RBM.Graph.BAG5LeafInst.baAllM_leaf  1060-1080
RBM.Graph.BAG5LeafInst.baG5Ctx_H3_needed  1082-1105
RBM.Graph.BAG5LeafInst.baG5Attached_inst  1107-1114
RBM.Graph.BAG5LeafInst.baselStar_inst  1116-1132
### RBM3D.Graph.BAGGExp  (3 unreached of 27)
RBM.Graph.ba_W_sub_one  50-57
RBM.Graph.BAGGExpInst.e0  479-480
RBM.Graph.BAGGExpInst.e1  482-483
### RBM3D.Graph.BAGGOp  (25 unreached of 116)
private RBM.Graph.BAGGOp_rho2_u  1134-1134
private RBM.Graph.BAGGOp_rho2_b  1136-1136
RBM.Graph.BAGGOpInst.baGG3  1743-1750
RBM.Graph.BAGGOpInst.baGG4  1752-1759
RBM.Graph.BAGGOpInst.p0  1761-1761
RBM.Graph.BAGGOpInst.q0  1762-1762
RBM.Graph.BAGGOpInst.p3  1763-1764
RBM.Graph.BAGGOpInst.q3  1765-1765
RBM.Graph.BAGGOpInst.p4  1766-1766
RBM.Graph.BAGGOpInst.q4  1767-1767
RBM.Graph.BAGGOpInst.hp0  1769-1769
RBM.Graph.BAGGOpInst.hq0  1770-1770
RBM.Graph.BAGGOpInst.hp3  1771-1771
RBM.Graph.BAGGOpInst.hq3  1772-1772
RBM.Graph.BAGGOpInst.hp4  1773-1773
RBM.Graph.BAGGOpInst.hq4  1774-1774
RBM.Graph.BAGGOpInst.hN0  1775-1775
RBM.Graph.BAGGOpInst.hN3  1776-1776
RBM.Graph.BAGGOpInst.hN4  1777-1777
RBM.Graph.BAGGOpInst.Cnt  1779-1781
RBM.Graph.BAGGOpInst.instDecidableCnt  1783-1784
RBM.Graph.BAGGOpInst.lists_baGGLhs  1786-1793
RBM.Graph.BAGGOpInst.lists_baGG3  1795-1800
RBM.Graph.BAGGOpInst.A1_keeps  1811-1816
RBM.Graph.BAGGOpInst.A1_gains  1818-1823
### RBM3D.Graph.BALWOut  (2 unreached of 3)
RBM.BA.baLWCutExpTw_holds  45-49
private RBM.BA.BALWOut_reg  73-85
### RBM3D.Graph.BALocReg1  (17 unreached of 55)
RBM.Graph.BALocReg1_flip_false_ms  72-74
RBM.Graph.BALocReg1_img_pathInv2_iff  155-156
RBM.Graph.BALocReg1Inst.LEr  657-657
RBM.Graph.BALocReg1Inst.LEr_pathFam  659-725
RBM.Graph.BALocReg1Inst.baPEr  727-727
RBM.Graph.BALocReg1Inst.pEr  728-728
RBM.Graph.BALocReg1Inst.pathInv2_Er  730-733
RBM.Graph.BALocReg1Inst.outsEr  735-736
RBM.Graph.BALocReg1Inst.hStepEr  738-739
RBM.Graph.BALocReg1Inst.normalEr  741-741
RBM.Graph.BALocReg1Inst.tags_Er  743-744
private RBM.Graph.BALocReg1Inst.outsErT  756-756
private RBM.Graph.BALocReg1Inst.stepErT  758-759
private RBM.Graph.BALocReg1Inst.pathInv2_ErT  761-761
RBM.Graph.BALocReg1Inst.LCr  774-777
RBM.Graph.BALocReg1Inst.LCr_pathFam  779-851
RBM.Graph.BALocReg1Inst.pathInv2_C  853-871
### RBM3D.Graph.BALocReg1B  (52 unreached of 65)
RBM.Graph.BALocReg1_molMap_mk  168-168
RBM.Graph.BALocReg1B_partition_ne  321-327
private RBM.Graph.BALocReg1B_twist_ff  343-348
RBM.Graph.BALocReg1B_baSplitSolid_ne  350-357
RBM.Graph.BALocReg1B_start_step  359-400
RBM.Graph.BALocReg1B_mapG  424-427
RBM.Graph.BALocReg1B_mapG_comp  429-432
RBM.Graph.BALocReg1B_mapG_twist  434-445
RBM.Graph.BALocReg1B_atomAdj_map  455-456
RBM.Graph.BALocReg1B_atomAdj_map_range  458-461
RBM.Graph.BALocReg1B_mem_atom_map  463-476
RBM.Graph.BALocReg1B_sameAtom_map  478-482
RBM.Graph.BALocReg1B_intAtom_map  484-490
RBM.Graph.BALocReg1B_atEdges_map  492-499
RBM.Graph.BALocReg1B_atCharge_map  501-508
RBM.Graph.BALocReg1B_normal_map  511-512
RBM.Graph.BALocReg1B_locStd_map  514-542
RBM.Graph.BALocReg1B_adj_map  553-557
RBM.Graph.BALocReg1B_adj_map_range  559-565
RBM.Graph.BALocReg1B_mem_mol_map  567-580
RBM.Graph.BALocReg1B_nM_map  582-612
RBM.Graph.BALocReg1B_pmap  620-622
RBM.Graph.BALocReg1B_lwSplit_map  624-628
RBM.Graph.BALocReg1B_baSplitSolid_map  630-638
RBM.Graph.BALocReg1B_splitG_map  640-647
RBM.Graph.BALocReg1B_extMap  649-653
RBM.Graph.BALocReg1B_extMap_owxEmb  655-657
RBM.Graph.BALocReg1B_extMap_new  659-660
RBM.Graph.BALocReg1B_extMap_injective  662-672
RBM.Graph.BALocReg1B_extMap_isRight  674-682
RBM.Graph.BALocReg1B_extMap_surj  684-689
RBM.Graph.BALocReg1B_lanlwD_map  691-712
RBM.Graph.BALocReg1B_cls_eq_iff  720-734
RBM.Graph.BALocReg1B_merge_map  736-755
RBM.Graph.BALocReg1B_Good  763-765
RBM.Graph.BALocReg1B_Good.comp  767-772
RBM.Graph.BALocReg1B_Good.ext  774-775
RBM.Graph.BALocReg1B_Good.locStd  777-780
RBM.Graph.BALocReg1B_Good.nM  782-785
RBM.Graph.BALocReg1B_weight_out  789-828
RBM.Graph.BALocReg1B_D0  830-831
RBM.Graph.BALocReg1B_p1  832-833
RBM.Graph.BALocReg1B_q1  834-834
RBM.Graph.BALocReg1B_T1  835-836
RBM.Graph.BALocReg1B_G1  837-838
RBM.Graph.BALocReg1B_p2  839-839
RBM.Graph.BALocReg1B_q2  840-840
RBM.Graph.BALocReg1B_T2  841-841
RBM.Graph.BALocReg1B_G2  842-843
RBM.Graph.BALocReg1B_data  845-850
RBM.Graph.BALocReg1B_reach_locStd  852-888
private RBM.Graph.BALocReg1B_liftQ_locStd  899-901
### RBM3D.Graph.BALocReg2  (9 unreached of 41)
RBM.Graph.BALocReg2_cends_bpS  185-185
RBM.Graph.BALocReg2_bpS_σ  187-187
RBM.Graph.BALocReg2_bpS_src  189-189
RBM.Graph.BALocReg2_bpS_dst  191-191
RBM.Graph.BALocReg2Inst.pathInv2_A  784-800
RBM.Graph.BALocReg2Inst.pathInv2_B  802-827
RBM.Graph.BALocReg2Inst.baPL  829-831
RBM.Graph.BALocReg2Inst.pL  833-834
RBM.Graph.BALocReg2Inst.pathInv2_L  836-857
### RBM3D.Graph.BALocReg2B  (9 unreached of 24)
RBM.Graph.baPathStep_closed  348-349
RBM.Graph.baShapeLLBinder_holds  356-362
RBM.Graph.ba_localregular_upto5  379-387
private RBM.Graph.BALocReg2B_extraB_map  402-413
private RBM.Graph.BALocReg2B_weight_out_e2  415-450
private RBM.Graph.BALocReg2B_start_weight_e2  452-465
RBM.Graph.BALocReg2BInst.outsErT  532-533
RBM.Graph.BALocReg2BInst.stepErT  535-536
RBM.Graph.BALocReg2BInst.pathInv2_ErT  538-538
### RBM3D.Graph.BALvl1A  (12 unreached of 46)
RBM.Graph.BALvl1AInst.hFA  562-564
RBM.Graph.BALvl1AInst.hFB  565-566
RBM.Graph.BALvl1AInst.hFC  567-569
RBM.Graph.BALvl1AInst.hFW  570-571
RBM.Graph.BALvl1AInst.hFE  572-574
RBM.Graph.BALvl1AInst.ℓ1  576-577
RBM.Graph.BALvl1AInst.P2  622-623
RBM.Graph.BALvl1AInst.ℓ0_not_factor  625-633
RBM.Graph.BALvl1AInst.locStepB  640-643
RBM.Graph.BALvl1AInst.locStepC  645-647
RBM.Graph.BALvl1AInst.normalB  649-649
RBM.Graph.BALvl1AInst.normalC  650-650
### RBM3D.Graph.BALvl1B  (7 unreached of 37)
RBM.Graph.instDecidableBALvl1Good  75-75
RBM.Graph.instDecidableBALvl1GoodLit  76-76
RBM.Graph.BALvl1BInst.tW  454-455
RBM.Graph.BALvl1BInst.d1C  462-465
RBM.Graph.BALvl1BInst.normalPC  467-467
RBM.Graph.BALvl1BInst.outsW  476-477
RBM.Graph.BALvl1BInst.outsE  478-478
### RBM3D.Graph.BAMomentExpGen  (14 unreached of 37)
RBM.BA.LWfgD_bandFM  72-88
RBM.BA.LWMomentExp_iff_bandPin  174-179
private RBM.BA.BAMomentExpGen_Φ0  910-911
private RBM.BA.BAMomentExpGen_Ψ0  913-913
private RBM.BA.BAMomentExpGen_Ψ0_window  915-918
private RBM.BA.BAMomentExpGen_ell0  920-923
private RBM.BA.BAMomentExpGen_psiAll0  925-938
private RBM.BA.BAMomentExpGen_Df  1006-1007
private RBM.BA.BAMomentExpGen_Ψ  1009-1011
private RBM.BA.BAMomentExpGen_Ψ_one  1013-1017
private RBM.BA.BAMomentExpGen_Ψ_le  1019-1029
private RBM.BA.BAMomentExpGen_ℓ0_dist  1031-1043
private RBM.BA.BAMomentExpGen_start  1045-1054
private RBM.BA.BAMomentExpGen_wt_vals  1056-1071
### RBM3D.Graph.BAMomentExpGenB  (2 unreached of 29)
private RBM.BA.BAMomentExpGenB_assmExp0  1224-1228
private RBM.BA.BAMomentExpGenB_strict  1230-1241
### RBM3D.Graph.BAMomentGen  (5 unreached of 49)
RBM.BA.LWfg_bandFM  75-89
RBM.BA.LWMoment_iff_bandPin  139-143
RBM.BA.BAMomentGen_D_G  339-340
RBM.BA.BAMomentGen_D_M  342-343
RBM.BA.BAMomentGen_D_GM  345-346
### RBM3D.Graph.BAMomentGenB  (25 unreached of 38)
private RBM.BA.BAMomentGen_Φ0  442-443
private RBM.BA.BAMomentGen_Ψ0  445-446
private RBM.BA.BAMomentGen_Ψ0_window  448-451
private RBM.BA.BAMomentGen_psiAll0  453-466
RBM.BA.BAMomentGen_pt  496-498
RBM.BA.BAMomentGen_P  500-502
RBM.BA.BAMomentGen_pt_Xmat  504-518
RBM.BA.BAMomentGen_P_mul  520-527
RBM.BA.BAMomentGen_resolvent  530-550
RBM.BA.BAMomentGen_M0  553-560
RBM.BA.BAMomentGen_pt_G  562-574
RBM.BA.BAMomentGen_S_sum  577-587
RBM.BA.BAMomentGen_pt_fxy  589-631
RBM.BA.BAMomentGen_PF_pos  634-653
RBM.BA.BAMomentGen_sigma  656-658
RBM.BA.BAMomentGen_sigma_sigma  660-662
RBM.BA.BAMomentGen_sigma_ne  664-674
RBM.BA.BAMomentGen_sigma_blk  676-681
RBM.BA.BAMomentGen_pt_var  684-704
RBM.BA.BAMomentGen_selfI  706-720
RBM.BA.BAMomentGen_fxyPow_pt  723-737
RBM.BA.BAMomentGen_sqrt_quarter  740-742
RBM.BA.BAMomentGen_num_z  744-749
RBM.BA.BAMomentGen_num_F  751-765
RBM.BA.BAMomentGen_lists_nonempty  770-832
### RBM3D.Graph.BAProv  (18 unreached of 68)
RBM.Graph.BAWExp.comp  155-163
RBM.Graph.BAProv_outsOf_exists  401-408
RBM.Graph.BAProv_exists_append  412-418
RBM.Graph.BAProvPos  420-422
RBM.Graph.BAProv_weight_pos  426-429
RBM.Graph.BAProv_edge_pos  431-434
RBM.Graph.BAProv_gg_pos  436-439
RBM.Graph.BAProv_within_pos  441-453
RBM.Graph.BAProv_ggSplit_pos  455-471
RBM.Graph.BAProv_frameStep_pos  473-480
RBM.Graph.BAProv_twist_pos  498-507
RBM.Graph.BAProv_locStep_pos  509-514
RBM.Graph.BAProv_start  518-549
RBM.Graph.fxyValD_univ  681-684
RBM.Graph.fxyValD_union  686-698
RBM.Graph.BAProv_w  802-803
RBM.Graph.BAProv_baPW2  833-834
RBM.Graph.BAProv_pW2  835-835
### RBM3D.Graph.BAProvB  (4 unreached of 75)
RBM.Graph.baProv_exists  937-942
RBM.Graph.BAProv_LocRegXClosed  1109-1112
RBM.Graph.baEngineProv_imp_localregularX  1114-1120
RBM.Graph.BAProv_wt  1201-1202
### RBM3D.Graph.BAS3Close  (8 unreached of 151)
private RBM.Graph.BAS3Close_iso_refl  270-272
private RBM.Graph.BAS3Close_lift_bpv  440-441
private RBM.Graph.BAS3Close_CtxG_dec  599-602
private RBM.Graph.BAS3Close_M_pk  1696-1696
private RBM.Graph.BAS3Close_LeafC_dec  1701-1703
private RBM.Graph.BAS3Close_InvC_dec  1711-1713
private RBM.Graph.BAS3Close_CandC_dec  1735-1738
private RBM.Graph.BAS3Close_CtxExD_dec  1744-1746
### RBM3D.Graph.BAS3CloseB  (1 unreached of 105)
private RBM.Graph.BAS3Close_iso_pk_eq  349-352
### RBM3D.Graph.BAS3CloseC  (31 unreached of 124)
private RBM.Graph.BAS3Close_D_M  99-100
RBM.Graph.baFoldLeaf_congr  984-992
private RBM.Graph.BAS3Close_fold_gen  1036-1038
private RBM.Graph.BAS3Close_fold00  1055-1057
private RBM.Graph.BAS3Close_fold01  1071-1073
private RBM.Graph.BAS3Close_fold02  1087-1089
private RBM.Graph.BAS3Close_fold03  1103-1105
private RBM.Graph.BAS3Close_fold04  1119-1121
private RBM.Graph.BAS3Close_fold05  1135-1137
private RBM.Graph.BAS3Close_fold06  1151-1153
private RBM.Graph.BAS3Close_fold10  1167-1169
private RBM.Graph.BAS3Close_fold11  1183-1185
private RBM.Graph.BAS3Close_fold12  1199-1201
private RBM.Graph.BAS3Close_fold13  1215-1217
private RBM.Graph.BAS3Close_fold14  1231-1233
private RBM.Graph.BAS3Close_fold15  1247-1249
private RBM.Graph.BAS3Close_fold16  1263-1265
RBM.Graph.baS3Fold_holds  1424-1444
RBM.Graph.baS3Stuck0_val  1446-1478
RBM.Graph.BAS3Close  1481-1484
RBM.Graph.baS3Close_holds  1486-1490
RBM.Graph.BAS3Expand'  1492-1495
RBM.Graph.baS3Expand'_holds  1497-1498
RBM.Graph.BAS3CloseInst.baS3_inst_identity  1506-1519
RBM.Graph.BAS3CloseInst.baS3_inst_fold  1522-1523
RBM.Graph.BAS3CloseInst.baS3_inst_congr  1525-1526
RBM.Graph.BAS3CloseInst.baS3_inst_rho0  1549-1569
RBM.Graph.BAS3CloseInst.baS3_inst_expand'  1583-1584
private RBM.Graph.BAS3CloseInst.BAS3Close_inst_leaf  1587-1603
private RBM.Graph.BAS3CloseInst.BAS3Close_inst_fold  1606-1634
RBM.Graph.BAS3CloseInst.baS3_inst_close  1636-1654
### RBM3D.Graph.BAScost  (27 unreached of 110)
RBM.Graph.locStdA  70-74
RBM.Graph.BAFinal  122-129
RBM.Graph.BAScostLL_E1  1297-1301
RBM.Graph.BAScostLL_E2  1303-1307
RBM.Graph.BAScost_sIntCls_card_le  1321-1332
RBM.Graph.BAScost_scostA_ge_crude  1334-1344
RBM.Graph.BAScost_locCostGeA_crude  1346-1349
RBM.Graph.BAScostInst.gs  1357-1365
RBM.Graph.BAScostInst.ps  1367-1369
RBM.Graph.BAScostInst.qs  1371-1372
RBM.Graph.BAScostInst.ps_mem  1374-1374
RBM.Graph.BAScostInst.qs_mem  1376-1376
RBM.Graph.BAScostInst.gs_wf1  1378-1378
RBM.Graph.BAScostInst.gs_wf2  1380-1380
RBM.Graph.BAScostInst.gw  1382-1390
RBM.Graph.BAScostInst.pw  1392-1393
RBM.Graph.BAScostInst.pw_mem  1395-1395
RBM.Graph.BAScostInst.gw_same  1397-1397
RBM.Graph.BAScostInst.gc  1399-1406
RBM.Graph.BAScostInst.pc  1408-1410
RBM.Graph.BAScostInst.qc  1412-1414
RBM.Graph.BAScostInst.pc_mem  1416-1416
RBM.Graph.BAScostInst.qc_mem  1418-1418
RBM.Graph.BAScostInst.gc_same  1420-1420
RBM.Graph.BAScostInst.gc_wf1  1422-1422
RBM.Graph.BAScostInst.gc_wf2  1424-1424
RBM.Graph.BAScostInst.g2  1461-1469
### RBM3D.Graph.BAScost2  (12 unreached of 17)
RBM.Graph.baShapeLL_s1  68-78
RBM.Graph.baShapeLL_macroA  99-108
RBM.Graph.BAScost2Inst.ts1  134-136
RBM.Graph.BAScost2Inst.ts1_shape  138-143
RBM.Graph.BAScost2Inst.te1  153-155
RBM.Graph.BAScost2Inst.te1_shape  157-161
RBM.Graph.BAScost2Inst.te2  166-169
RBM.Graph.BAScost2Inst.te2_shape  171-175
RBM.Graph.BAScost2Inst.tma  180-183
RBM.Graph.BAScost2Inst.tma_shape  185-191
RBM.Graph.BAScost2Inst.tmb  202-205
RBM.Graph.BAScost2Inst.tmb_shape  207-213
### RBM3D.Graph.BAShapeO2  (1 unreached of 49)
RBM.Graph.BAShapeO2_rho2_zero  274-274
### RBM3D.Graph.BAShapeO2B  (1 unreached of 16)
RBM.Graph.baLocReg6_holds  348-359
### RBM3D.Graph.BASim  (12 unreached of 144)
RBM.Graph.WEdge.BASim_sameRev_refl  170-170
RBM.Graph.DEdge.BASim_sameU_refl  173-173
RBM.Graph.PGraph.BASim_BAEquiv_refl  183-195
RBM.Graph.BAsim  208-213
RBM.Graph.BAPGraph.BASim_outsOf_append  262-264
RBM.Graph.BAPGraph.BASim_outsT_append  266-269
RBM.Graph.BASim_T'  938-940
RBM.Graph.BASimInst.Ed  1962-1962
RBM.Graph.BASimInst.baPA  1963-1965
RBM.Graph.BASimInst.pA  1966-1966
RBM.Graph.BASimInst.qA  1967-1967
RBM.Graph.BASimInst.ggF  1968-1969
### RBM3D.Graph.BASim2  (4 unreached of 138)
RBM.Graph.BASim_baSplit_cons_unc'  355-361
RBM.Graph.BASim_lanlwT1_eq  508-509
RBM.Graph.BASim_twistS_ff  967-967
RBM.Graph.BASim_owxEmb2_inr  1443-1443
### RBM3D.Graph.BASim3  (17 unreached of 111)
RBM.Graph.BASimInst.baPB  1878-1880
RBM.Graph.BASimInst.pB  1881-1881
RBM.Graph.BASimInst.baPC  1882-1884
RBM.Graph.BASimInst.pC  1885-1885
RBM.Graph.BASimInst.qC  1886-1886
RBM.Graph.BASimInst.baPW  1887-1888
RBM.Graph.BASimInst.pW  1889-1889
RBM.Graph.BASimInst.baPE  1890-1891
RBM.Graph.BASimInst.pE  1892-1892
RBM.Graph.BASimInst.ggFT  1893-1894
RBM.Graph.BASimInst.hTA  1895-1896
RBM.Graph.BASimInst.hTB  1897-1897
RBM.Graph.BASimInst.hTC  1898-1900
RBM.Graph.BASimInst.hTW  1901-1902
RBM.Graph.BASimInst.hTE  1903-1906
RBM.Graph.BASimInst.tag_exists  1907-1908
RBM.Graph.BASimInst.inst_match_extra  1926-1935
### RBM3D.Graph.BASizeClaim  (3 unreached of 46)
RBM.Graph.BASizeClaimInst.fInst  1130-1133
RBM.Graph.BASizeClaimInst.uInst  1135-1135
RBM.Graph.BASizeClaimInst.vInst  1137-1137
### RBM3D.Graph.BASizeClaim2  (13 unreached of 31)
private RBM.Graph.BASizeClaim_sizeG_le_iff  496-505
private RBM.Graph.BASizeClaim_norm_sum_le_of_le  507-517
private RBM.Graph.BASizeClaim_val_of_factor  519-526
private RBM.Graph.BASizeClaim_val_of_not  528-531
RBM.Graph.baClaimSizeG  533-553
RBM.Graph.baClaimSize_E  561-583
RBM.Graph.baClaimSizeG_E  585-606
RBM.Graph.baSpTail_E  612-629
RBM.Graph.baMTail_E  631-697
RBM.Graph.baTail_log  699-734
RBM.Graph.BASizeClaimInst2.D0  749-755
RBM.Graph.BASizeClaimInst2.D0_hG  757-759
RBM.Graph.BASizeClaimInst2.ellInst  761-762
### RBM3D.Graph.BAStepS  (6 unreached of 39)
RBM.Graph.baUntag_locStepT_intro  136-138
private RBM.Graph.BAStepS_LTB  433-434
private RBM.Graph.BAStepS_LTC  435-436
private RBM.Graph.BAStepS_stepB  438-439
private RBM.Graph.BAStepS_stepC  440-441
private RBM.Graph.BAStepS_pL  492-495
### RBM3D.Graph.BASymm1  (6 unreached of 35)
RBM.Graph.BAtwistIntegral  397-403
RBM.Graph.baTwistIntegral_holds  405-420
RBM.Graph.BASymm1Inst.G0  426-436
RBM.Graph.BASymm1Inst.G0_normal  438-438
RBM.Graph.BASymm1Inst.G0_counts  440-442
RBM.Graph.BASymm1Inst.ℓ0  444-445
### RBM3D.Graph.BASymm2  (30 unreached of 36)
RBM.Graph.baSum_twist  85-93
RBM.Graph.BAtwistSum  116-125
RBM.Graph.baTwistSum_holds  127-139
private RBM.Graph.BASymm2_baSum_nil  166-168
private RBM.Graph.BASymm2_back  176-189
private RBM.Graph.BASymm2_back1  191-201
RBM.Graph.BAtwistFormE  205-231
RBM.Graph.baTwistFormE_holds  233-248
private RBM.Graph.BASymm2_circ_twist  264-270
private RBM.Graph.BASymm2_circ_twist_ord  272-275
private RBM.Graph.BASymm2_mono  277-301
RBM.Graph.baTwist_lanlw_ord  309-317
RBM.Graph.baTwist_lanlw_scalingOrderG  319-326
RBM.Graph.baTwist_lw_raw  328-339
RBM.Graph.baTwist_lw_mono  341-357
RBM.Graph.baTwist_lw_scalingOrderG  359-366
RBM.Graph.baTwist_gg_raw  368-388
RBM.Graph.baTwist_gg_mono  390-416
RBM.Graph.baTwist_gg_scalingOrderG  418-425
RBM.Graph.BASymm2Inst.G1  435-446
RBM.Graph.BASymm2Inst.G1_normal  448-448
RBM.Graph.BASymm2Inst.G1_counts  450-451
RBM.Graph.BASymm2Inst.Pa  453-456
RBM.Graph.BASymm2Inst.Pb  458-461
RBM.Graph.BASymm2Inst.Qc  463-465
RBM.Graph.BASymm2Inst.Pa_mem  467-468
RBM.Graph.BASymm2Inst.Pb_mem  469-469
RBM.Graph.BASymm2Inst.Qc_mem  470-470
RBM.Graph.BASymm2Inst.A0  472-473
RBM.Graph.BASymm2Inst.B0  474-474
### RBM3D.Graph.BATermHoldsB  (6 unreached of 22)
RBM.BA.baStep2_closed  876-879
private RBM.BA.BATermHoldsB_ℓ0  898-899
private RBM.BA.BATermHoldsB_ℓ0_ge  901-902
private RBM.BA.BATermHoldsB_ℓ0_le  904-915
private RBM.BA.BATermHoldsB_reg_small  917-930
private RBM.BA.BATermHoldsB_t0_le  932-942
### RBM3D.Graph.BAVocab  (37 unreached of 144)
RBM.Graph.BAPGraph.scalingSize  205-206
RBM.Graph.BAGraph.scalingSizeG  238-241
RBM.Graph.BAGraph.term_addM  253-258
RBM.Graph.BAGraph.nA_le_card  434-458
RBM.Graph.BAGraph.scalingSize_eq  489-496
RBM.Graph.BAGraph.scalingOrder_ofLGraph  561-568
RBM.Graph.BAVocabInst.baGGLhs  1180-1187
RBM.Graph.BAVocabInst.baGGT1  1189-1197
RBM.Graph.BAVocabInst.baLWT1  1199-1207
RBM.Graph.BAVocabInst.baGedge  1209-1216
RBM.Graph.BAVocabInst.baEqGraph  1218-1226
RBM.Graph.BAVocabInst.baD  1228-1234
RBM.Graph.BAVocabInst.baGGLhs_counters  1237-1239
RBM.Graph.BAVocabInst.baGGLhs_ord  1241-1242
RBM.Graph.BAVocabInst.baGGT1_counters  1245-1247
RBM.Graph.BAVocabInst.baGGT1_ord  1249-1250
RBM.Graph.BAVocabInst.baLWT1_counters  1253-1255
RBM.Graph.BAVocabInst.baLWT1_ord  1257-1258
RBM.Graph.BAVocabInst.baGedge_ord  1261-1263
RBM.Graph.BAVocabInst.baGedge_splitG_length  1265-1265
RBM.Graph.BAVocabInst.baGedge_not_normal  1267-1270
RBM.Graph.BAVocabInst.baGedge_splitG_circ  1272-1273
RBM.Graph.BAVocabInst.p2Graph_ba_ord  1276-1278
RBM.Graph.BAVocabInst.figGraph_ba_ord  1280-1282
RBM.Graph.BAVocabInst.baGedge1  1284-1291
RBM.Graph.BAVocabInst.baGedge2  1293-1299
RBM.Graph.BAVocabInst.baGedge_splitG  1301-1301
RBM.Graph.BAVocabInst.baGedge1_normal  1303-1303
RBM.Graph.BAVocabInst.baGedge2_normal  1305-1305
RBM.Graph.BAVocabInst.baGedge_ordG  1308-1326
private RBM.Graph.BAVocabInst.BAVocab_val_fin_one  1328-1336
RBM.Graph.BAVocabInst.baGedge_val  1340-1343
RBM.Graph.BAVocabInst.baGedge1_val  1345-1348
RBM.Graph.BAVocabInst.baGedge2_val  1350-1353
RBM.Graph.BAVocabInst.baGGLhs_size  1355-1361
RBM.Graph.BAVocabInst.baGedge_split_sum  1363-1368
RBM.Graph.BAVocabInst.baGedge_partition_val  1370-1371
### RBM3D.Graph.BAWeightOp  (10 unreached of 90)
RBM.Graph.BAWeightOpInst.baGwx  1845-1852
RBM.Graph.BAWeightOpInst.p0  1854-1855
RBM.Graph.BAWeightOpInst.p1  1857-1858
RBM.Graph.BAWeightOpInst.hp0  1860-1860
RBM.Graph.BAWeightOpInst.hp1  1862-1862
RBM.Graph.BAWeightOpInst.hN0  1864-1864
RBM.Graph.BAWeightOpInst.hN1  1866-1866
RBM.Graph.BAWeightOpInst.lists_baGcxx  1868-1873
RBM.Graph.BAWeightOpInst.lists_baGwx  1875-1878
RBM.Graph.BAWeightOpInst.frameE1  1923-1931
### RBM3D.Graph.BAZetaExp  (8 unreached of 21)
RBM.Graph.LWXiEgL_bandFM  72-76
private RBM.Graph.BAZetaExp_ρ0  513-514
private RBM.Graph.BAZetaExp_ρ0_nonneg  516-517
private RBM.Graph.BAZetaExp_ρ0_rad  519-534
private RBM.Graph.BAZetaExp_Ψ0  536-537
private RBM.Graph.BAZetaExp_Ψ0_window  539-542
private RBM.Graph.BAZetaExp_ell0  544-547
private RBM.Graph.BAZetaExp_strict  549-561
### RBM3D.Graph.Expansions  (1 unreached of 3)
RBM.Graph.hasDerivAt_inverse_sub_apply  87-92
### RBM3D.Graph.LWEdgeExp  (29 unreached of 61)
RBM.Graph.oe1x_rhs_tame  96-107
RBM.Graph.oe1x_tame1_finprod  211-220
RBM.Graph.oe1x_dh_finprod  222-242
RBM.Graph.oe1xR  248-256
RBM.Graph.oe1xR_tame1  260-269
RBM.Graph.oe1x_dh_R  271-351
RBM.Graph.oe1x_pointwise  356-430
RBM.Graph.oe1x_lwG_zero  450-465
RBM.Graph.oe1x_rest_eq  468-474
RBM.Graph.oe1x_pin_pos  476-558
RBM.Graph.lwEdgeExp_holds  560-569
RBM.Graph.oe1xT1_ord  1043-1049
RBM.Graph.oe1xD_ord  1072-1078
RBM.Graph.oe1xT1loop  1320-1323
RBM.Graph.oe1xT1d_val_loop  1325-1332
RBM.Graph.oe1xT1loop_counters  1334-1340
RBM.Graph.oe1x_graph_E_loop  1342-1362
RBM.Graph.oe1xInstGraph  1394-1403
RBM.Graph.oe1xInstP  1405-1409
RBM.Graph.oe1xInst_mem  1411-1412
RBM.Graph.oe1xInst_hv  1414-1414
RBM.Graph.oe1xInstQr  1433-1437
RBM.Graph.oe1xInstQb  1439-1443
RBM.Graph.oe1xInstQf  1445-1449
RBM.Graph.oe1xInst_memr  1451-1452
RBM.Graph.oe1xInst_memb  1454-1455
RBM.Graph.oe1xInst_memf  1457-1458
RBM.Graph.oe1xInstGraphL  1509-1516
RBM.Graph.oe1xInstL_mem  1518-1521
### RBM3D.Graph.LWEngine  (12 unreached of 82)
RBM.Graph.lwEngine_evX_eq  83-83
RBM.Graph.lwEngine_dotChoices_sc  137-137
RBM.Graph.LocStepX.eval_one  446-451
RBM.Graph.lwEngine_col_transpose  478-478
RBM.Graph.LWEngineInst.lwEngineInst_mE_zero  799-801
RBM.Graph.LWEngineInst.lwEngine_inst_lwEvX  803-815
RBM.Graph.LWEngineInst.lwEngine_inst_stepX  817-821
RBM.Graph.LWEngineInst.lwEngine_inst_two_m  823-832
RBM.Graph.LWEngineInst.lwEngine_inst_stepX_edge_gg  834-860
RBM.Graph.LWEngineInst.lwEngine_inst_nWS_ge  862-874
RBM.Graph.LWEngineInst.lwEngine_inst_step1_identity  876-887
RBM.Graph.LWEngineInst.lwEngine_inst_localregularX  889-932
### RBM3D.Graph.LWExpCert  (15 unreached of 32)
RBM.Graph.LWCert.cPartition  99-104
RBM.Graph.LWCert.belowOf  152-189
RBM.Graph.LWCert.childrenB  191-193
RBM.Graph.LWCert.goodB  195-200
RBM.Graph.LWCert.rootInfo  202-204
RBM.Graph.LWCert.rootAt  206-206
RBM.Graph.LWCert.kids  208-210
RBM.Graph.LWCert.kidsOk  212-213
RBM.Graph.LWCert.kid  215-215
RBM.Graph.LWCert.goodB_succ_of  225-254
RBM.Graph.LWCert.inner_node_one  259-264
RBM.Graph.LWCert.root_FF_shape  266-267
RBM.Graph.LWCert.root_FT_shape  268-268
RBM.Graph.LWCert.lwCert_root0_nonleaf  270-276
RBM.Graph.LWCert.lwCert_roots_below  278-282
### RBM3D.Graph.LWExpCertB  (12 unreached of 25)
RBM.Graph.LWCert.inner_node_one'  134-139
RBM.Graph.LWCert.root_FF_shape'  141-142
RBM.Graph.LWCert.root_FT_shape'  143-143
RBM.Graph.LWCert.lwCert_root0_nonleaf'  145-151
RBM.Graph.LWCert.lwCert_roots_below'  153-157
RBM.Graph.LWCert.lostOf  187-199
RBM.Graph.LWCert.lostAt  201-205
RBM.Graph.LWCert.lwCertB_cex  207-208
RBM.Graph.LWCert.lwCertB_lost_R2  210-212
RBM.Graph.LWCert.lwCertB_lost_R8  213-213
RBM.Graph.LWCert.lwCertB_cex_bites  215-220
RBM.Graph.LWCert.lwCertB_root_eq  222-227
### RBM3D.Graph.LWExpCertS0  (96 unreached of 96)
RBM.Graph.LWCert.root_FF_0  29-34
RBM.Graph.LWCert.root_FF_1  35-40
RBM.Graph.LWCert.root_FF_2  41-46
RBM.Graph.LWCert.root_FF_3  47-52
RBM.Graph.LWCert.root_FF_4  53-58
RBM.Graph.LWCert.root_FF_5  59-64
RBM.Graph.LWCert.root_FF_6  65-70
RBM.Graph.LWCert.root_FF_7  71-76
RBM.Graph.LWCert.root_FF_8  77-82
RBM.Graph.LWCert.ch_FF_9_0_0  83-83
RBM.Graph.LWCert.ch_FF_9_0_1  84-84
RBM.Graph.LWCert.ch_FF_9_0_2  85-85
RBM.Graph.LWCert.ch_FF_9_0_3  86-86
RBM.Graph.LWCert.ch_FF_9_0_4  87-87
RBM.Graph.LWCert.ch_FF_9_0_5  88-88
RBM.Graph.LWCert.ch_FF_9_0_6  89-89
RBM.Graph.LWCert.ch_FF_9_0_7  90-90
RBM.Graph.LWCert.ch_FF_9_0_8  91-91
RBM.Graph.LWCert.ch_FF_9_0_9  92-92
RBM.Graph.LWCert.ch_FF_9_0_10  93-93
RBM.Graph.LWCert.ch_FF_9_0_11  94-94
RBM.Graph.LWCert.chs_FF_9_0  95-109
RBM.Graph.LWCert.ch_FF_9_1_0  110-110
RBM.Graph.LWCert.ch_FF_9_1_1  111-111
RBM.Graph.LWCert.ch_FF_9_1_2  112-112
RBM.Graph.LWCert.ch_FF_9_1_3  113-113
RBM.Graph.LWCert.ch_FF_9_1_4  114-114
RBM.Graph.LWCert.ch_FF_9_1_5  115-115
RBM.Graph.LWCert.ch_FF_9_1_6  116-116
RBM.Graph.LWCert.ch_FF_9_1_7  117-117
RBM.Graph.LWCert.ch_FF_9_1_8  118-118
RBM.Graph.LWCert.ch_FF_9_1_9  119-119
RBM.Graph.LWCert.ch_FF_9_1_10  120-120
RBM.Graph.LWCert.ch_FF_9_1_11  121-121
RBM.Graph.LWCert.chs_FF_9_1  122-136
RBM.Graph.LWCert.ch_FF_9_2_0  137-137
RBM.Graph.LWCert.ch_FF_9_2_1  138-138
RBM.Graph.LWCert.ch_FF_9_2_2  139-139
RBM.Graph.LWCert.ch_FF_9_2_3  140-140
RBM.Graph.LWCert.ch_FF_9_2_4  141-141
RBM.Graph.LWCert.ch_FF_9_2_5  142-142
RBM.Graph.LWCert.ch_FF_9_2_6  143-143
RBM.Graph.LWCert.ch_FF_9_2_7  144-144
RBM.Graph.LWCert.ch_FF_9_2_8  145-145
RBM.Graph.LWCert.ch_FF_9_2_9  146-146
RBM.Graph.LWCert.ch_FF_9_2_10  147-147
RBM.Graph.LWCert.ch_FF_9_2_11  148-148
RBM.Graph.LWCert.chs_FF_9_2  149-163
RBM.Graph.LWCert.root_FF_9  164-173
RBM.Graph.LWCert.ch_FF_10_0_0  174-174
RBM.Graph.LWCert.ch_FF_10_0_1  175-175
RBM.Graph.LWCert.ch_FF_10_0_2  176-176
RBM.Graph.LWCert.ch_FF_10_0_3  177-177
RBM.Graph.LWCert.ch_FF_10_0_4  178-178
RBM.Graph.LWCert.ch_FF_10_0_5  179-179
RBM.Graph.LWCert.ch_FF_10_0_6  180-180
RBM.Graph.LWCert.ch_FF_10_0_7  181-181
RBM.Graph.LWCert.ch_FF_10_0_8  182-182
RBM.Graph.LWCert.ch_FF_10_0_9  183-183
RBM.Graph.LWCert.ch_FF_10_0_10  184-184
RBM.Graph.LWCert.ch_FF_10_0_11  185-185
RBM.Graph.LWCert.ch_FF_10_0_12  186-186
RBM.Graph.LWCert.ch_FF_10_0_13  187-187
RBM.Graph.LWCert.chs_FF_10_0  188-204
RBM.Graph.LWCert.ch_FF_10_1_0  205-205
RBM.Graph.LWCert.ch_FF_10_1_1  206-206
RBM.Graph.LWCert.ch_FF_10_1_2  207-207
RBM.Graph.LWCert.ch_FF_10_1_3  208-208
RBM.Graph.LWCert.ch_FF_10_1_4  209-209
RBM.Graph.LWCert.ch_FF_10_1_5  210-210
RBM.Graph.LWCert.ch_FF_10_1_6  211-211
RBM.Graph.LWCert.ch_FF_10_1_7  212-212
RBM.Graph.LWCert.ch_FF_10_1_8  213-213
RBM.Graph.LWCert.ch_FF_10_1_9  214-214
RBM.Graph.LWCert.ch_FF_10_1_10  215-215
RBM.Graph.LWCert.ch_FF_10_1_11  216-216
RBM.Graph.LWCert.ch_FF_10_1_12  217-217
RBM.Graph.LWCert.ch_FF_10_1_13  218-218
RBM.Graph.LWCert.chs_FF_10_1  219-235
RBM.Graph.LWCert.ch_FF_10_2_0  236-236
RBM.Graph.LWCert.ch_FF_10_2_1  237-237
RBM.Graph.LWCert.ch_FF_10_2_2  238-238
RBM.Graph.LWCert.ch_FF_10_2_3  239-239
RBM.Graph.LWCert.ch_FF_10_2_4  240-240
RBM.Graph.LWCert.ch_FF_10_2_5  241-241
RBM.Graph.LWCert.ch_FF_10_2_6  242-242
RBM.Graph.LWCert.ch_FF_10_2_7  243-243
RBM.Graph.LWCert.ch_FF_10_2_8  244-244
RBM.Graph.LWCert.ch_FF_10_2_9  245-245
RBM.Graph.LWCert.ch_FF_10_2_10  246-246
RBM.Graph.LWCert.ch_FF_10_2_11  247-247
RBM.Graph.LWCert.ch_FF_10_2_12  248-248
RBM.Graph.LWCert.ch_FF_10_2_13  249-249
RBM.Graph.LWCert.chs_FF_10_2  250-266
RBM.Graph.LWCert.root_FF_10  267-276
RBM.Graph.LWCert.cert_FF  277-292
### RBM3D.Graph.LWExpCertS1  (97 unreached of 97)
RBM.Graph.LWCert.root_FT_0  29-34
RBM.Graph.LWCert.root_FT_1  35-40
RBM.Graph.LWCert.root_FT_2  41-46
RBM.Graph.LWCert.root_FT_3  47-52
RBM.Graph.LWCert.root_FT_4  53-58
RBM.Graph.LWCert.root_FT_5  59-64
RBM.Graph.LWCert.root_FT_6  65-70
RBM.Graph.LWCert.root_FT_7  71-76
RBM.Graph.LWCert.root_FT_8  77-82
RBM.Graph.LWCert.ch_FT_9_0_0  83-83
RBM.Graph.LWCert.ch_FT_9_0_1  84-84
RBM.Graph.LWCert.ch_FT_9_0_2  85-85
RBM.Graph.LWCert.ch_FT_9_0_3  86-86
RBM.Graph.LWCert.ch_FT_9_0_4  87-87
RBM.Graph.LWCert.ch_FT_9_0_5  88-88
RBM.Graph.LWCert.ch_FT_9_0_6  89-89
RBM.Graph.LWCert.ch_FT_9_0_7  90-90
RBM.Graph.LWCert.ch_FT_9_0_8  91-91
RBM.Graph.LWCert.ch_FT_9_0_9  92-92
RBM.Graph.LWCert.ch_FT_9_0_10  93-93
RBM.Graph.LWCert.ch_FT_9_0_11  94-94
RBM.Graph.LWCert.chs_FT_9_0  95-109
RBM.Graph.LWCert.ch_FT_9_1_0  110-110
RBM.Graph.LWCert.ch_FT_9_1_1  111-111
RBM.Graph.LWCert.ch_FT_9_1_2  112-112
RBM.Graph.LWCert.ch_FT_9_1_3  113-113
RBM.Graph.LWCert.ch_FT_9_1_4  114-114
RBM.Graph.LWCert.ch_FT_9_1_5  115-115
RBM.Graph.LWCert.ch_FT_9_1_6  116-116
RBM.Graph.LWCert.ch_FT_9_1_7  117-117
RBM.Graph.LWCert.ch_FT_9_1_8  118-118
RBM.Graph.LWCert.ch_FT_9_1_9  119-119
RBM.Graph.LWCert.ch_FT_9_1_10  120-120
RBM.Graph.LWCert.ch_FT_9_1_11  121-121
RBM.Graph.LWCert.chs_FT_9_1  122-136
RBM.Graph.LWCert.ch_FT_9_2_0  137-137
RBM.Graph.LWCert.ch_FT_9_2_1  138-138
RBM.Graph.LWCert.ch_FT_9_2_2  139-139
RBM.Graph.LWCert.ch_FT_9_2_3  140-140
RBM.Graph.LWCert.ch_FT_9_2_4  141-141
RBM.Graph.LWCert.ch_FT_9_2_5  142-142
RBM.Graph.LWCert.ch_FT_9_2_6  143-143
RBM.Graph.LWCert.ch_FT_9_2_7  144-144
RBM.Graph.LWCert.ch_FT_9_2_8  145-145
RBM.Graph.LWCert.ch_FT_9_2_9  146-146
RBM.Graph.LWCert.ch_FT_9_2_10  147-147
RBM.Graph.LWCert.ch_FT_9_2_11  148-148
RBM.Graph.LWCert.chs_FT_9_2  149-163
RBM.Graph.LWCert.root_FT_9  164-173
RBM.Graph.LWCert.ch_FT_10_0_0  174-174
RBM.Graph.LWCert.ch_FT_10_0_1  175-175
RBM.Graph.LWCert.ch_FT_10_0_2  176-176
RBM.Graph.LWCert.ch_FT_10_0_3  177-177
RBM.Graph.LWCert.ch_FT_10_0_4  178-178
RBM.Graph.LWCert.ch_FT_10_0_5  179-179
RBM.Graph.LWCert.ch_FT_10_0_6  180-180
RBM.Graph.LWCert.ch_FT_10_0_7  181-181
RBM.Graph.LWCert.ch_FT_10_0_8  182-182
RBM.Graph.LWCert.ch_FT_10_0_9  183-183
RBM.Graph.LWCert.ch_FT_10_0_10  184-184
RBM.Graph.LWCert.ch_FT_10_0_11  185-185
RBM.Graph.LWCert.ch_FT_10_0_12  186-186
RBM.Graph.LWCert.ch_FT_10_0_13  187-187
RBM.Graph.LWCert.chs_FT_10_0  188-204
RBM.Graph.LWCert.ch_FT_10_1_0  205-205
RBM.Graph.LWCert.ch_FT_10_1_1  206-206
RBM.Graph.LWCert.ch_FT_10_1_2  207-207
RBM.Graph.LWCert.ch_FT_10_1_3  208-208
RBM.Graph.LWCert.ch_FT_10_1_4  209-209
RBM.Graph.LWCert.ch_FT_10_1_5  210-210
RBM.Graph.LWCert.ch_FT_10_1_6  211-211
RBM.Graph.LWCert.ch_FT_10_1_7  212-212
RBM.Graph.LWCert.ch_FT_10_1_8  213-213
RBM.Graph.LWCert.ch_FT_10_1_9  214-214
RBM.Graph.LWCert.ch_FT_10_1_10  215-215
RBM.Graph.LWCert.ch_FT_10_1_11  216-216
RBM.Graph.LWCert.ch_FT_10_1_12  217-217
RBM.Graph.LWCert.ch_FT_10_1_13  218-218
RBM.Graph.LWCert.chs_FT_10_1  219-235
RBM.Graph.LWCert.ch_FT_10_2_0  236-236
RBM.Graph.LWCert.ch_FT_10_2_1  237-237
RBM.Graph.LWCert.ch_FT_10_2_2  238-238
RBM.Graph.LWCert.ch_FT_10_2_3  239-239
RBM.Graph.LWCert.ch_FT_10_2_4  240-240
RBM.Graph.LWCert.ch_FT_10_2_5  241-241
RBM.Graph.LWCert.ch_FT_10_2_6  242-242
RBM.Graph.LWCert.ch_FT_10_2_7  243-243
RBM.Graph.LWCert.ch_FT_10_2_8  244-244
RBM.Graph.LWCert.ch_FT_10_2_9  245-245
RBM.Graph.LWCert.ch_FT_10_2_10  246-246
RBM.Graph.LWCert.ch_FT_10_2_11  247-247
RBM.Graph.LWCert.ch_FT_10_2_12  248-248
RBM.Graph.LWCert.ch_FT_10_2_13  249-249
RBM.Graph.LWCert.chs_FT_10_2  250-266
RBM.Graph.LWCert.root_FT_10  267-276
RBM.Graph.LWCert.cert_FT  277-292
RBM.Graph.LWCert.cert_all  295-306
### RBM3D.Graph.LWExpSim  (12 unreached of 85)
RBM.Graph.LWCert.Cand.toR  107-110
RBM.Gauss.Sizes.lwG5Cand_of_cands  166-174
RBM.Gauss.Sizes.ChildrenSim  206-211
private RBM.Gauss.Sizes.lwExpSim_block  1120-1131
private RBM.Gauss.Sizes.lwExpSim_block_id  1133-1140
RBM.Gauss.Sizes.childrenSim  1142-1153
RBM.Gauss.Sizes.rel_self  1156-1166
private RBM.Gauss.Sizes.lwExpSim_rootN  1170-1171
private RBM.Gauss.Sizes.lwExpSim_rootN_surj  1173-1173
private RBM.Gauss.Sizes.lwExpSim_instN  1189-1191
private RBM.Gauss.Sizes.lwExpSim_instN_surj  1193-1193
private RBM.Gauss.Sizes.lwExpSim_instC  1195-1196
### RBM3D.Graph.LWExpSound  (13 unreached of 108)
RBM.Gauss.Sizes.LWG5ExpandSplit  49-52
RBM.Gauss.Sizes.SoundStep  86-92
RBM.Gauss.Sizes.soundStep  1252-1257
RBM.Gauss.Sizes.lwG5ExpandSplit_iff  1402-1402
RBM.Gauss.Sizes.lwG5LeafProps_iff  1403-1404
private RBM.Gauss.Sizes.lwExpSound_N  1416-1416
private RBM.Gauss.Sizes.lwExpSound_N_surj  1417-1417
private RBM.Gauss.Sizes.lwExpSound_c  1418-1418
private RBM.Gauss.Sizes.lwExpSound_f  1419-1420
RBM.Gauss.Sizes.lwExpSound_inst_relKids  1435-1442
RBM.Gauss.Sizes.lwExpSound_inst_belowOfSound_R2  1452-1458
RBM.Gauss.Sizes.lwExpSound_inst_leafOK_R2  1460-1462
RBM.Gauss.Sizes.lwExpSound_inst_leafProps  1478-1485
### RBM3D.Graph.LWExpTerm  (45 unreached of 59)
RBM.Gauss.Sizes.LWExpI1  63-75
RBM.Gauss.Sizes.LWExpI41  77-91
RBM.Gauss.Sizes.LWExpG5  93-108
private RBM.Gauss.Sizes.lwExpTerm_prec_congr  195-202
private RBM.Gauss.Sizes.lwExpTerm_vec1  336-339
private RBM.Gauss.Sizes.lwExpTerm_Kloop_one  341-345
private RBM.Gauss.Sizes.lwExpTerm_facts  347-370
private RBM.Gauss.Sizes.lwExpTerm_env_X  372-381
private RBM.Gauss.Sizes.lwExpTerm_env_L2  383-389
private RBM.Gauss.Sizes.lwExpTerm_env_D  391-398
private RBM.Gauss.Sizes.lwExpTerm_floor3  400-405
private RBM.Gauss.Sizes.lwExpTerm_XD  407-456
private RBM.Gauss.Sizes.lwExpTerm_sum_norm_SB_col  458-464
private RBM.Gauss.Sizes.lwExpTerm_int_X  466-473
private RBM.Gauss.Sizes.lwExpTerm_int_XL  475-494
private RBM.Gauss.Sizes.lwExpTerm_I1_n  496-524
RBM.Gauss.Sizes.lwExpI1_holds  530-568
private RBM.Gauss.Sizes.lwExpTerm_loopL_rot  576-580
private RBM.Gauss.Sizes.lwExpTerm_loopL_conj  582-585
private RBM.Gauss.Sizes.lwExpTerm_loopL_one  587-589
private RBM.Gauss.Sizes.lwExpTerm_ward_loop  591-607
private RBM.Gauss.Sizes.lwExpTerm_green_conj  609-614
private RBM.Gauss.Sizes.lwExpTerm_loop2_nonneg  616-657
private RBM.Gauss.Sizes.lwExpTerm_Lloop_eq2  665-671
private RBM.Gauss.Sizes.lwExpTerm_Lloop_eq1  673-678
private RBM.Gauss.Sizes.lwExpTerm_ward_two  680-693
private RBM.Gauss.Sizes.lwExpTerm_ward_sum_le  695-739
private RBM.Gauss.Sizes.lwExpTerm_wsum2  750-759
private RBM.Gauss.Sizes.lwExpTerm_wsum3  762-774
private RBM.Gauss.Sizes.lwExpTerm_norm_sum3_le  776-779
private RBM.Gauss.Sizes.lwExpTerm_norm_Wd  787-788
private RBM.Gauss.Sizes.lwExpTerm_Ta_n  790-815
private RBM.Gauss.Sizes.lwExpTerm_Tb_n  817-839
private RBM.Gauss.Sizes.lwExpTerm_int_split3  849-866
private RBM.Gauss.Sizes.lwExpTerm_int_sum3  868-882
private RBM.Gauss.Sizes.lwExpTerm_I41_split  884-903
private RBM.Gauss.Sizes.lwExpTerm_Ra  913-918
private RBM.Gauss.Sizes.lwExpTerm_Ra_prec  920-993
private RBM.Gauss.Sizes.lwExpTerm_eta_le_one  995-1003
private RBM.Gauss.Sizes.lwExpTerm_Ta_det  1005-1072
private RBM.Gauss.Sizes.lwExpTerm_Kward  1074-1106
RBM.Gauss.Sizes.lwExpI41_holds  1112-1208
RBM.Gauss.LWInst.lwExpTerm_inst_cut  1221-1230
RBM.Gauss.LWInst.lwExpTerm_inst_I1  1232-1240
RBM.Gauss.LWInst.lwExpTerm_inst_I41  1242-1253
### RBM3D.Graph.LWExpTerm2  (16 unreached of 150)
RBM.Gauss.Sizes.lwExpTerm2_trace_prod5  598-600
RBM.Gauss.Sizes.lwExpTerm2_BM_LWcut  1153-1160
RBM.Gauss.Sizes.lwExpTerm2_ker_SB  1740-1756
RBM.Gauss.Sizes.lwExpG5_of_G5'  2026-2034
RBM.Gauss.Sizes.lwExpI1_of_K  2036-2040
RBM.Gauss.Sizes.lwExpI41_of_K  2042-2051
RBM.Gauss.LWInst.lwExpTerm2_inst_cut  2064-2072
RBM.Gauss.LWInst.lwExpTerm2_inst_ker_SB  2074-2075
RBM.Gauss.LWInst.lwExpTerm2_inst_ker_Kp  2077-2079
RBM.Gauss.LWInst.lwExpTerm2_inst_ker_KK  2081-2083
RBM.Gauss.LWInst.lwExpTerm2_inst_expand  2085-2098
RBM.Gauss.LWInst.lwExpTerm2_inst_conj  2100-2103
RBM.Gauss.LWInst.lwExpTerm2_inst_Kp_split  2105-2110
RBM.Gauss.LWInst.lwExpTerm2_inst_G5  2112-2112
RBM.Gauss.LWInst.lwExpTerm2_inst_I1  2113-2113
RBM.Gauss.LWInst.lwExpTerm2_inst_I41  2114-2114
### RBM3D.Graph.LWExpTerm3  (19 unreached of 84)
RBM.Gauss.Sizes.LWG5Expand  1781-1790
RBM.Gauss.Sizes.lwExpTerm3_T4pos  1857-1953
RBM.Gauss.Sizes.LwExpG5'OfExpand  2028-2029
RBM.Gauss.Sizes.lwExpG5'_of_expand  2031-2171
RBM.Gauss.Sizes.LwCutExpOfExpand  2177-2178
RBM.Gauss.Sizes.LwTermEXPOfExpand  2180-2181
RBM.Gauss.Sizes.lwCutExp_of_expand  2183-2184
RBM.Gauss.Sizes.lwTermEXP_of_expand  2186-2187
RBM.Gauss.Sizes.lwExpTerm3_instGraph  2189-2198
RBM.Gauss.Sizes.lwExpTerm3_instGraph_nM  2207-2208
RBM.Gauss.Sizes.lwExpTerm3_instGraph_normal  2210-2210
RBM.Gauss.Sizes.lwExpTerm3_instGraph_attached  2212-2214
RBM.Gauss.Sizes.lwExpTerm3_instGraph_ext  2216-2222
RBM.Gauss.LWInst.lwExpTerm3_inst_prec1  2230-2239
RBM.Gauss.LWInst.lwExpTerm3_inst_graph_order  2242-2244
RBM.Gauss.LWInst.lwExpTerm3_inst_bridge  2246-2259
RBM.Gauss.LWInst.lwExpTerm3_inst_G5  2261-2275
RBM.Gauss.LWInst.lwExpTerm3_inst_cut  2277-2288
RBM.Gauss.LWInst.lwExpTerm3_inst_term  2290-2299
### RBM3D.Graph.LWExpTerm4  (11 unreached of 83)
private RBM.Gauss.Sizes.lwExpTerm4_Gt_entry_le  576-595
RBM.Gauss.LWInst.lwExpTerm4_inst_cut  1731-1740
RBM.Gauss.LWInst.lwExpTerm4_inst_I1K  1742-1751
RBM.Gauss.LWInst.lwExpTerm4_inst_I23K  1753-1768
RBM.Gauss.LWInst.lwExpTerm4_inst_I41K  1770-1782
RBM.Gauss.LWInst.lwExpTerm4_inst_kerSum  1784-1789
RBM.Gauss.LWInst.lwExpTerm4_inst_ward2  1791-1799
RBM.Gauss.LWInst.lwExpTerm4_inst_L3  1801-1810
RBM.Gauss.LWInst.lwExpTerm4_inst_L3_full  1812-1820
RBM.Gauss.LWInst.lwExpTerm4_inst_kward  1822-1829
RBM.Gauss.LWInst.lwExpTerm4_inst_diag  1831-1836
### RBM3D.Graph.LWExpTerm5  (10 unreached of 49)
RBM.Gauss.Sizes.LWG5Progress  70-73
RBM.Gauss.Sizes.PartitionXSpec  112-115
RBM.Gauss.Sizes.partitionX_spec  310-314
RBM.Gauss.LWInst.lwExpTerm5_inst_identity  634-643
private RBM.Gauss.LWInst.lwExpTerm5_instP  646-648
private RBM.Gauss.LWInst.lwExpTerm5_instCand  650-671
RBM.Gauss.LWInst.lwExpTerm5_inst_kids_identity  673-681
RBM.Gauss.LWInst.lwExpTerm5_inst_kids_normal  683-685
RBM.Gauss.LWInst.lwExpTerm5_inst_R1_val_zero  687-692
RBM.Gauss.LWInst.lwExpTerm5_inst_val_eq_partitionX  694-699
### RBM3D.Graph.LWExpTerm6  (13 unreached of 25)
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_instGraph  641-650
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_instGraph_normal  652-652
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_instGraph_nM  654-654
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_instGraph_joined  656-660
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_instGraph_counters  662-667
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_join  669-678
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_expand  680-695
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_G5  697-711
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_cut  713-722
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_term  724-732
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_step6I  734-738
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_step6II  740-743
RBM.Gauss.Sizes.LWExpTerm6Inst.lwExpTerm6_inst_step6III  745-748
### RBM3D.Graph.LWGGExp  (21 unreached of 57)
RBM.Graph.oe2x_lwG_zero  414-429
RBM.Graph.lwGGExp_holds  431-460
RBM.Graph.oe2x_nM_add_edge  687-787
RBM.Graph.oe2xR2_adj  991-1013
RBM.Graph.oe2xR1d_adj  1015-1034
RBM.Graph.oe2x_adj_relabel_inv  1036-1057
RBM.Graph.oe2xR2_nM_ge  1059-1064
RBM.Graph.oe2xR1_nM_ge  1066-1103
RBM.Graph.oe2xR1_ord  1105-1111
RBM.Graph.oe2xR2_ord  1113-1118
RBM.Graph.oe2xR4_ord  1120-1126
RBM.Graph.oe2xR5_ord  1128-1134
RBM.Graph.oe2xR6_ord  1136-1142
RBM.Graph.oe2xR7_ord  1144-1151
RBM.Graph.oe2xR8_ord  1153-1160
RBM.Graph.oe2xInstGraph  1641-1648
RBM.Graph.oe2xInstP  1650-1653
RBM.Graph.oe2xInstQ  1655-1658
RBM.Graph.oe2xInst_hp  1660-1661
RBM.Graph.oe2xInst_hq  1663-1664
RBM.Graph.oe2xInst_hy  1666-1666
### RBM3D.Graph.LWLvl1  (50 unreached of 218)
RBM.Graph.lvl1_col_twist  968-971
RBM.Graph.lvl1Outs  3132-3135
RBM.Graph.instDecidableLocStd_1  3217-3218
RBM.Graph.lvl1_exists_aux  3837-3878
RBM.Graph.lvl1_lemma  3902-3935
RBM.Graph.lvl1_lemma_induction  3937-3956
RBM.Graph.lvl1_lemma_size  4043-4068
RBM.Graph.lvl1ExStd  4090-4099
RBM.Graph.lvl1ExNotNormal  4101-4102
RBM.Graph.lvl1ExLoop  4104-4106
RBM.Graph.lvl1ExLoopExt  4108-4110
RBM.Graph.lvl1ExDeg1  4112-4117
RBM.Graph.lvl1ExDeg3  4119-4124
RBM.Graph.lvl1ExSame  4126-4131
RBM.Graph.lvl1ExCharge  4133-4138
RBM.Graph.lvl1_locStd_iff  4140-4143
RBM.Graph.lvl1_inst_locStd  4145-4147
RBM.Graph.lvl1_inst_locStd_pack  4149-4149
RBM.Graph.lvl1_inst_std_counts  4151-4154
RBM.Graph.lvl1_inst_fail_normal  4156-4158
RBM.Graph.lvl1_inst_fail_loop  4160-4162
RBM.Graph.lvl1_inst_fail_loopExt  4164-4166
RBM.Graph.lvl1_inst_fail_deg1  4168-4170
RBM.Graph.lvl1_inst_fail_deg3  4172-4174
RBM.Graph.lvl1_inst_fail_same  4176-4178
RBM.Graph.lvl1_inst_fail_charge  4180-4183
RBM.Graph.lvl1_inst_not_locStd  4185-4187
RBM.Graph.lvl1ExP2p  4195-4198
RBM.Graph.lvl1_inst_locStep_weight  4200-4204
RBM.Graph.lvl1_inst_step1  4206-4217
RBM.Graph.lvl1ExLoopExtp  4227-4230
RBM.Graph.lvl1_inst_locStep_weightExt  4232-4236
RBM.Graph.lvl1_inst_step1Ext  4238-4248
RBM.Graph.lvl1ExDeg1p  4250-4251
RBM.Graph.lvl1_inst_locStep_edge  4253-4258
RBM.Graph.lvl1_inst_step2  4260-4270
RBM.Graph.lvl1ExSamep  4272-4274
RBM.Graph.lvl1ExSameq  4276-4276
RBM.Graph.lvl1_inst_locStep_gg  4278-4285
RBM.Graph.lvl1_inst_step3  4287-4299
RBM.Graph.lvl1Counts4  4301-4303
RBM.Graph.lvl1_inst_step1_terms  4305-4322
RBM.Graph.lvl1_inst_step2_terms  4324-4330
RBM.Graph.lvl1_inst_step3_terms  4332-4346
RBM.Graph.lvl1_inst_cutoff  4354-4363
RBM.Graph.lvl1_inst_size_le  4365-4379
RBM.Graph.lvl1_inst_lemma  4381-4399
RBM.Graph.lvl1_inst_lemma_size  4401-4422
RBM.Graph.lvl1_inst_induction  4428-4437
RBM.Graph.lvl1_inst_lemma_induction  4439-4456
### RBM3D.Graph.LWMomExp  (26 unreached of 66)
RBM.Graph.lwMomExp_tau  520-522
RBM.Graph.lwMomExp_nearD  530-534
private RBM.Graph.lwMomExp_tau_nonneg  540-541
private RBM.Graph.lwMomExp_tau_symm  543-546
private RBM.Graph.lwMomExp_tau_self  548-551
private RBM.Graph.lwMomExp_sfT_le_zero  553-561
private RBM.Graph.lwMomExp_tau_le  563-565
private RBM.Graph.lwMomExp_psi_pos  567-579
private RBM.Graph.lwMomExp_TTkBody  583-593
private RBM.Graph.lwMomExp_TTkBody_mono  595-613
private RBM.Graph.lwMomExp_exists_K  615-630
private RBM.Graph.lwMomExp_hstep  634-653
RBM.Graph.lwMomExp_near_step'  655-679
private RBM.Graph.lwMomExp_sys_near  681-699
RBM.Graph.AnpDetNearAt  897-909
RBM.Graph.AnpDetNear  911-912
private RBM.Graph.lwMomExp_nSolid  918-922
private RBM.Graph.lwMomExp_ordN  924-929
RBM.Graph.lwMomExp_near_graph  931-1019
RBM.Graph.lwMomExp_near  1021-1024
RBM.Graph.lwMomExp_inst_near  1035-1037
private RBM.Graph.lwMomExp_inst_ell  1039-1041
private RBM.Graph.lwMomExp_inst_mem  1043-1050
RBM.Graph.lwMomExp_inst_near_pt  1052-1064
private RBM.Graph.lwMomExp_sysOf_figAux  1066-1068
RBM.Graph.lwMomExp_inst_step  1070-1084
### RBM3D.Graph.LWMomExpFar  (7 unreached of 31)
RBM.Graph.lwMomExpFar_ownExt_dec  52-53
RBM.Graph.LWAuxNestedOwn  94-102
RBM.Graph.lwMomExpFar_auxOwn  372-408
RBM.Graph.lwMomExpFar_inst_figAux  416-418
RBM.Graph.lwMomExpFar_inst_oneEdge  420-424
RBM.Graph.lwMomExpFar_inst_head  426-428
RBM.Graph.lwMomExpFar_inst_aux  430-436
### RBM3D.Graph.LWMomExpInf  (4 unreached of 31)
private RBM.Graph.LWMomExpInfInst.lwMEI_zdistInf_le  563-566
RBM.Graph.LWMomExpInfInst.inst_ekTTkInf  574-586
RBM.Graph.LWMomExpInfInst.inst_near  588-590
RBM.Graph.LWMomExpInfInst.inst_near_pt  592-609
### RBM3D.Graph.LWMoment  (2 unreached of 69)
RBM.Gauss.LWInst.lwMoment_inst_moment  1847-1858
RBM.Gauss.LWInst.lwMoment_inst_moment_endT  1860-1868
### RBM3D.Graph.LWMomentExp  (1 unreached of 62)
RBM.Graph.lwMomentExp_inst_nonempty  1446-1473
### RBM3D.Graph.LWMomentExpA  (1 unreached of 14)
private RBM.Graph.lwMEA_zdistInf_zero  93-95
### RBM3D.Graph.LWPins  (53 unreached of 86)
RBM.Graph.LWPins_lwGb  80-80
RBM.Graph.LWPins_lwGcb  82-82
RBM.Graph.LWPins_oe1xRest  118-125
RBM.Graph.LWedgeExp  127-160
RBM.Graph.LWggExp  162-181
RBM.Gauss.Sizes.LWtermB  251-270
RBM.Gauss.LWInst.one_le_W  518-518
RBM.Gauss.LWInst.Φ0  520-521
RBM.Gauss.LWInst.Ψ0  522-522
RBM.Gauss.LWInst.W_rpow_inv_le  524-526
RBM.Gauss.LWInst.W_inv_le_rpow  528-530
RBM.Gauss.LWInst.window0  532-535
RBM.Gauss.LWInst.class0  537-540
RBM.Gauss.LWInst.psiRel0  542-550
RBM.Gauss.LWInst.psiAll0  552-552
RBM.Gauss.LWInst.tInst_range  554-556
RBM.Gauss.LWInst.assm_of  558-563
RBM.Gauss.LWInst.inst_LWterm  565-574
RBM.Gauss.LWInst.ℓT  582-584
RBM.Gauss.LWInst.ℓT_one_le  586-587
RBM.Gauss.LWInst.ℓT_window  589-598
RBM.Gauss.LWInst.assmExpT_of  600-603
RBM.Gauss.LWInst.assmExp_of  605-608
RBM.Gauss.LWInst.strict_all  610-623
RBM.Gauss.LWInst.inst_LWtermExp  625-634
RBM.Gauss.LWInst.inst_LWMoment  636-647
RBM.Gauss.LWInst.inst_LWMomentExp  649-662
RBM.Gauss.LWInst.inst_LWtermEXP  664-674
RBM.Gauss.LWInst.inst_AnpKey  682-696
RBM.Gauss.LWInst.inst_Anp  698-709
RBM.Gauss.LWInst.figAux_ghostOK  711-714
RBM.Graph.LWInstFixed.P01  725-728
RBM.Graph.LWInstFixed.inst_ssl  730-733
RBM.Graph.LWInstFixed.inst_edge  735-738
RBM.Graph.LWInstFixed.inst_gg  740-742
RBM.Gauss.LWInst.tEnd_range  757-759
RBM.Gauss.LWInst.inst_LWterm_endT  761-769
RBM.Gauss.LWInst.inst_LWtermExp_endT  771-779
RBM.Gauss.LWInst.inst_LWtermExpN  781-792
RBM.Gauss.LWInst.inst_LWMoment_endT  794-804
RBM.Gauss.LWInst.inst_AnpKey_endT  806-816
RBM.Gauss.LWInst.inst_LWtermEXP_endT  818-826
RBM.Gauss.LWInst.lam_le  834-838
RBM.Gauss.LWInst.lam_nonneg  840-841
RBM.Gauss.LWInst.ΦB  843-846
RBM.Gauss.LWInst.Bparam_bounds  848-876
RBM.Gauss.LWInst.classB  878-913
RBM.Gauss.LWInst.inst_LWtermB  915-929
RBM.Gauss.LWInst.inst_LWtermExpS  937-948
RBM.Gauss.LWInst.inst_AnpKeyGh  950-963
RBM.Gauss.LWInst.inst_shift  965-968
RBM.Gauss.LWInst.inst_LWReduceB  970-983
RBM.Gauss.LWInst.inst_LWReduceT  985-1004
### RBM3D.Graph.LWProv  (11 unreached of 121)
RBM.Graph.valW_one  54-56
RBM.Graph.pvalW_one  58-61
RBM.Graph.WExp.comp  107-116
RBM.Graph.stepOuts  163-165
RBM.Graph.lwEngineProv_imp_localregularX  176-187
RBM.Graph.lwProv_EW_zero  985-989
RBM.Graph.lwProv_pvalW_comp_not  1215-1220
RBM.Graph.LWProvInst.ProvOut.molecular_id  1712-1713
RBM.Graph.lwProv_LocStepXProvPos  1789-1795
RBM.Graph.lwProv_locStepXProvPos_holds  1797-1797
RBM.Graph.lwProv_wildGraph  1802-1807
### RBM3D.Graph.LWPsi  (42 unreached of 72)
RBM.Gauss.Sizes.LWPhiB_psiRel_three  240-253
RBM.Gauss.Sizes.LWPhiB_shift  309-317
RBM.Gauss.Sizes.LWPsiMax_asymp  352-361
RBM.tailW_regime2_bounds  512-520
RBM.Gauss.LWPsiInst.tW  537-538
RBM.Gauss.LWPsiInst.W_pos'  540-540
RBM.Gauss.LWPsiInst.lam_pos  542-543
RBM.Gauss.LWPsiInst.two_le_x  545-546
RBM.Gauss.LWPsiInst.lam_le_64  548-554
RBM.Gauss.LWPsiInst.lam_le_Winv  556-561
RBM.Gauss.LWPsiInst.L_ge_4  563-565
RBM.Gauss.LWPsiInst.Winv_sq_le  567-571
RBM.Gauss.LWPsiInst.tInst_ok  573-578
RBM.Gauss.LWPsiInst.tW_ok  580-586
RBM.Gauss.LWPsiInst.B0_le  588-596
RBM.Gauss.LWPsiInst.upper_core  598-625
RBM.Gauss.LWPsiInst.Bctl_eq  627-631
RBM.Gauss.LWPsiInst.hgt_tInst  633-638
RBM.Gauss.LWPsiInst.hgt_tW  640-648
RBM.Gauss.LWPsiInst.inst_psiRel  652-655
RBM.Gauss.LWPsiInst.inst_psiRel_tInst  657-659
RBM.Gauss.LWPsiInst.inst_psiRel_tW  661-663
RBM.Gauss.LWPsiInst.inst_psiRel_three_tInst  665-667
RBM.Gauss.LWPsiInst.inst_psiRel_three_tW  669-671
RBM.Gauss.LWPsiInst.inst_shift_tInst  673-682
RBM.Gauss.LWPsiInst.inst_shift_tW  684-688
RBM.Gauss.LWPsiInst.inst_window_tInst  692-695
RBM.Gauss.LWPsiInst.inst_window_tW  697-700
RBM.Gauss.LWPsiInst.inst_class_tInst  702-707
RBM.Gauss.LWPsiInst.inst_class_tW  709-714
RBM.Gauss.LWPsiInst.inst_psiAll_tInst  716-721
RBM.Gauss.LWPsiInst.inst_psiAll_tW  723-728
RBM.Gauss.LWPsiInst.inst_shift_all_tInst  730-734
RBM.Gauss.LWPsiInst.inst_shift_all_tW  736-739
RBM.Gauss.LWPsiInst.inst_asymp_tInst  741-746
RBM.Gauss.LWPsiInst.inst_asymp_tW  748-753
RBM.Gauss.LWPsiInst.inst_tail1_tInst  757-763
RBM.Gauss.LWPsiInst.inst_tail1_tW  765-773
RBM.Gauss.LWPsiInst.inst_tailW1_tInst  775-781
RBM.Gauss.LWPsiInst.inst_tailW1_tW  783-790
RBM.Gauss.LWPsiInst.inst_tail2  792-800
RBM.Gauss.LWPsiInst.inst_tailW2  802-811
### RBM3D.Graph.LWSizeClaim  (17 unreached of 68)
RBM.Graph.LWPins_lwSp_eq  146-152
RBM.Graph.lwKBound_E  473-487
private RBM.Graph.lwWVal_eq  833-834
RBM.Graph.LGraph.sizeConstG  1142-1145
private RBM.Graph.lwNorm_sum_le_of_le  1147-1157
RBM.Graph.lwClaimSizeG  1159-1181
RBM.Graph.lwClaimSize_E  1189-1209
RBM.Graph.lwClaimSizeG_E  1211-1226
RBM.Graph.LGraph.scalingSize_mul  1228-1235
RBM.Graph.lwKernel_tail  1246-1282
RBM.Graph.lwSpOf_tail_E  1314-1331
RBM.Graph.LWPins_lwSp_decay  1340-1349
RBM.Graph.lwSizeD0  1384-1391
private RBM.Graph.lwSizeD0_hG  1393-1395
private RBM.Graph.lwSizeD0_hGd  1397-1399
RBM.Graph.lwSizeEll  1423-1424
private RBM.Graph.lwSizeD0_hM  1426-1426
### RBM3D.Graph.LWStein  (57 unreached of 134)
RBM.Graph.owxG0  203-209
RBM.Graph.owxG1  211-217
RBM.Graph.owxG2  219-225
RBM.Graph.owx_ord  227-231
RBM.Graph.owx_smallest  233-246
RBM.Graph.owxH0  248-254
RBM.Graph.owxH1  256-263
RBM.Graph.owxH2  265-269
RBM.Graph.owxH3  271-275
RBM.Graph.owxH4  277-281
RBM.Graph.owx_ord_H  283-287
RBM.Graph.owx_second  289-321
RBM.Graph.owx_smallest_E  323-348
RBM.Graph.dhSample_lwG_eq_deriv  624-637
RBM.Graph.Tame1.neg  784-787
RBM.Graph.Tame1.pow  822-827
RBM.Graph.stein_lwPoly  1107-1113
RBM.Graph.lwEmb  1367-1368
RBM.Graph.lwDEdges  1370-1376
RBM.Graph.LGraph.dTerm  1378-1386
RBM.Graph.LGraph.dTerms  1388-1391
RBM.Graph.lwSplit_length  1393-1397
RBM.Graph.lwStein_dTerm_term  1477-1497
RBM.Graph.lwStein_dh_term  1522-1547
RBM.Graph.dhSample_graphVal  1556-1581
RBM.Graph.lwStein_nM_empty  1606-1614
RBM.Graph.LGraph.dTerm_counters  1616-1648
RBM.Graph.LGraph.dTerms_length  1651-1652
RBM.Graph.LGraph.dTerm_ord  1654-1661
RBM.Graph.LGraph.dTerms_counters  1663-1668
RBM.Graph.lwSzT  1679-1686
RBM.Graph.lwZ  1688-1689
RBM.Graph.lwZ_im  1691-1692
RBM.Graph.lwOmega  1704-1705
RBM.Graph.lwPoly_X_true  1714-1718
RBM.Graph.lwM0  1720-1721
RBM.Graph.lwZ0  1723-1723
RBM.Graph.lwZ0_im  1725-1726
RBM.Graph.lwM0_ne  1728-1729
RBM.Graph.lwM0_hzm  1731-1737
RBM.Graph.lwM0_norm  1739-1742
RBM.Graph.lwTwoEdge  1820-1826
RBM.Graph.lwTwoEdge_counters  1828-1830
RBM.Graph.lwStein_owxG1_counters  1832-1838
RBM.Graph.LWInstOwx.S0  1906-1907
RBM.Graph.LWInstOwx.Sp0  1909-1910
RBM.Graph.LWInstOwx.G0  1912-1913
RBM.Graph.LWInstOwx.D0  1915-1916
RBM.Graph.LWInstOwx.hS0  1918-1920
RBM.Graph.LWInstOwx.hSp0  1922-1924
RBM.Graph.LWInstOwx.hzm0  1926-1926
RBM.Graph.LWInstOwx.hM0  1928-1930
RBM.Graph.LWInstOwx.inst_owx_smallest  1932-1937
RBM.Graph.LWInstOwx.inst_owx_second  1939-1945
RBM.Graph.LWInstOwx.inst_owx_smallest_E  1947-1962
RBM.Graph.LWInstOwx.owxDefect_M0  1964-1967
RBM.Graph.LWInstOwx.inst_owx_smallest_E_unit  1969-1981
### RBM3D.Graph.LWSymm  (45 unreached of 186)
RBM.Graph.lwSymmTwistG_coeff  196-198
RBM.Graph.lwSymmTwistG_counters_eq  340-343
RBM.Graph.lwSymmTwistG_ord  345-348
RBM.Graph.lwSymm_slice_flip  409-410
RBM.Graph.lwSymmFlipLitF  479-480
RBM.Graph.lwSymm_Xentry_flipLit  482-495
RBM.Graph.lwSymm_flipLit_ne  497-504
RBM.Graph.lwSymmDataConj  506-507
RBM.Graph.lwSymm_conj_literal_false  509-518
RBM.Graph.lwSymm_conj_integral  540-549
RBM.Graph.owxET1_inr  621-622
RBM.Graph.owxET2_inr  624-625
RBM.Graph.owxET3_inr  627-628
RBM.Graph.owxET4_inr  630-631
RBM.Graph.owxET1_ord  822-827
RBM.Graph.owxET2_ord  829-834
RBM.Graph.owxET3_ord  836-842
RBM.Graph.owxET4_ord  844-850
RBM.Graph.lwSymmFrame_counters  1498-1503
RBM.Graph.lwSymmFrame2_counters  1505-1510
RBM.Graph.lwSymm_inst_hM0  2044-2045
RBM.Graph.lwSymm_inst_hMs  2047-2047
RBM.Graph.lwSymm_inst_hSpT  2049-2050
RBM.Graph.lwSymmInstL  2052-2053
RBM.Graph.lwSymmInstGraph  2057-2065
RBM.Graph.lwSymmInstD  2067-2072
RBM.Graph.lwSymmInstD_hS  2074-2075
RBM.Graph.lwSymmInstExtGraph  2129-2135
RBM.Graph.lwSymmInstExt_mem  2137-2140
RBM.Graph.lwSymmInstRedGraph  2188-2193
RBM.Graph.lwSymmInstRedIntGraph  2202-2207
RBM.Graph.lwSymmInstEdgeGraph  2222-2230
RBM.Graph.lwSymmInstEdgeP  2232-2236
RBM.Graph.lwSymmInstEdge_mem  2238-2239
RBM.Graph.lwSymmInstEdge_hv  2241-2241
RBM.Graph.lwSymmInstPairP  2269-2273
RBM.Graph.lwSymmInstPairQ  2275-2276
RBM.Graph.lwSymmInstPair_hp  2278-2279
RBM.Graph.lwSymmInstPair_hq  2281-2282
RBM.Graph.lwSymmInstPair_hy  2284-2284
RBM.Graph.lwSymmInstRedPairGraph  2296-2302
RBM.Graph.lwSymmInstRedPairP  2304-2305
RBM.Graph.lwSymmInstRedPairQ  2307-2308
RBM.Graph.lwSymmInstRedPair_hp  2310-2311
RBM.Graph.lwSymmInstRedPair_hq  2313-2314
### RBM3D.Graph.LWTermExpN  (1 unreached of 18)
RBM.Gauss.LWTermExpNInst.inst_lwtermExpN_of_LWterm  534-544
### RBM3D.Graph.LWTermHolds  (8 unreached of 54)
RBM.Gauss.Sizes.lwtermB_holds  687-718
RBM.Gauss.LWTermHoldsInst.LWTermHolds_flow_facts  1630-1634
RBM.Gauss.LWTermHoldsInst.LWTermHolds_sz0_size_real  1712-1716
RBM.Gauss.LWTermHoldsInst.LWTermHolds_sz0_ratio  1718-1723
RBM.Gauss.LWTermHoldsInst.LWTermHolds_sz0_eta_le  1725-1749
RBM.Gauss.LWTermHoldsInst.LWTermHolds_N_regime_tEnd  1751-1771
RBM.Gauss.LWTermHoldsInst.LWTermHolds_tMix  1773-1774
RBM.Gauss.LWTermHoldsInst.LWTermHolds_tMix_range  1776-1783
### RBM3D.Graph.LWVocab  (95 unreached of 256)
RBM.Graph.p2Graph  188-197
RBM.Graph.p2Graph_val  201-214
RBM.Graph.p2Graph_val_eq  220-236
RBM.Graph.p2Graph_counters  238-241
RBM.Graph.p2Graph_ord  243-246
RBM.Graph.figGraph  248-262
RBM.Graph.figGraph_counters  264-267
RBM.Graph.figGraph_ord  269-272
RBM.Graph.figGraph_val  274-290
RBM.Graph.NGraph.instDecidableWalkOK  332-332
RBM.Graph.figAux  375-382
RBM.Graph.instDecidableIsNestedFigAux  384-384
RBM.Graph.instDecidableNoGhostFigAux  386-386
RBM.Graph.figAux_nested  388-389
RBM.Graph.figAux_ord  391-394
RBM.Graph.SEdge.IsWeight  420-422
RBM.Graph.SEdge.IsLightWeight  424-425
RBM.Graph.SEdge.charge  427-428
RBM.Graph.IntEnds  430-432
RBM.Graph.LGraph.DotWF  434-438
RBM.Graph.instDecidableDotWFOfDecidableEq  440-441
private RBM.Graph.SEdge.val_map  449-450
private RBM.Graph.WEdge.val_map  452-453
private RBM.Graph.DEdge.val_map  455-456
RBM.Graph.LGraph.mem_iterate_iff  559-564
RBM.Graph.Counters.scalingSize_le  1640-1650
RBM.Graph.LGraph.scalingSizeG  1674-1677
RBM.Graph.LGraph.scalingOrderG  1679-1682
RBM.Graph.LGraph.le_scalingOrderG_iff  1684-1694
RBM.Graph.LGraph.scalingSizeG_le_iff  1696-1707
RBM.Graph.LGraph.val_of_isEmpty  1719-1728
RBM.Graph.LGraph.val_of_isEmpty_prod  1730-1737
RBM.Graph.LGraph.val_relabel_equiv  1739-1749
RBM.Graph.LData.map  1751-1756
private RBM.Graph.LGraph.term_map  1758-1765
RBM.Graph.LGraph.val_map_equiv  1767-1777
RBM.Graph.lwUnionV₁  1792-1793
RBM.Graph.lwUnionV₂  1795-1796
private RBM.Graph.lwUnionV₁_injective  1798-1799
private RBM.Graph.lwUnionV₂_injective  1801-1802
RBM.Graph.LGraph.disjUnion  1804-1810
private RBM.Graph.LGraph.term_disjUnion  1812-1823
RBM.Graph.LGraph.val_disjUnion  1825-1837
RBM.Graph.LGraph.nS_disjUnion  1839-1842
RBM.Graph.LGraph.nW_disjUnion  1844-1847
RBM.Graph.LGraph.nV_disjUnion  1849-1852
private RBM.Graph.lwUnionV_cases  1854-1860
private RBM.Graph.lwUnionV₁_ne_unionV₂  1862-1864
private RBM.Graph.lwUnionV₁_eq_unionV₂  1872-1874
private RBM.Graph.lwUnionV₂_eq_unionV₁  1876-1878
private RBM.Graph.lwUnionV₁_eq_iff  1880-1881
private RBM.Graph.lwUnionV₂_eq_iff  1883-1884
private RBM.Graph.lwAdj_union₁  1886-1890
private RBM.Graph.lwAdj_union₂  1892-1896
private RBM.Graph.lwAdj_union₁₂  1898-1904
private RBM.Graph.lwAdj_union₂₁  1906-1909
private RBM.Graph.lwStep_union₁  1911-1932
private RBM.Graph.lwStep_union₂  1934-1955
private RBM.Graph.lwIterate_union₁  1957-1964
private RBM.Graph.lwIterate_union₂  1966-1973
private RBM.Graph.lwMol_union₁  1975-1982
private RBM.Graph.lwMol_union₂  1984-1991
private RBM.Graph.lwIsRight_unionV₁  1993-1995
private RBM.Graph.lwIsRight_unionV₂  1997-1999
private RBM.Graph.lwSelf_mem_mol  2001-2003
RBM.Graph.LGraph.nM_disjUnion  2005-2056
RBM.Graph.LGraph.ord_disjUnion  2058-2064
private RBM.Graph.lwNormal_aPairs  2161-2170
private RBM.Graph.lwNormal_bEdges  2172-2179
private RBM.Graph.lwNormal_dotChoices  2181-2184
private RBM.Graph.lwNormal_dotBase  2186-2197
private RBM.Graph.lwNormal_withDots  2199-2203
private RBM.Graph.lwNormal_consistent  2222-2223
private RBM.Graph.lwVmapC_injective  2225-2230
private RBM.Graph.lwVmap_injective  2232-2235
private RBM.Graph.lwVmap_surjective  2237-2242
private RBM.Graph.lwSplitLoops_of_circ  2254-2264
RBM.Graph.LGraph.partition_of_normal  2266-2303
RBM.Graph.LGraph.scalingOrderG_of_normal  2305-2311
RBM.Graph.LGraph.scalingSizeG_of_normal  2313-2327
RBM.Graph.lwD  2335-2340
private RBM.Graph.lwD_S_real  2342-2344
private RBM.Graph.lwD_M_diag  2346-2348
private RBM.Graph.lwFxyVal  2350-2353
private RBM.Graph.lwP2Graph_val  2355-2359
RBM.Graph.lwNwGraph  2364-2372
RBM.Graph.lwSwGraph  2374-2380
RBM.Graph.lwSumGG  2382-2387
RBM.Graph.lwEqGraph  2389-2394
RBM.Graph.lwEdgeGraph  2396-2401
private RBM.Graph.lwSumGG_val  2431-2436
private RBM.Graph.lwEqGraph_val  2445-2449
private RBM.Graph.lwEdgeGraph_val  2454-2457
RBM.Graph.lwLoopGraph  2508-2513
private RBM.Graph.lwLoopGraph_val  2518-2520
### RBM3D.Graph.LWWeightExp  (39 unreached of 87)
RBM.Graph.lwWx_lwG  69-72
RBM.Graph.lwWx_lwS  74-77
RBM.Graph.lwWx_lwSp  79-83
RBM.Graph.lwWx_hSp  105-112
RBM.Graph.lwWx_lwPoly_eval  161-177
RBM.Graph.lwWx_lwPoly  179-184
RBM.Graph.lwWx_dh_var  186-211
RBM.Graph.lwWx_hasDerivAt  213-263
RBM.Graph.lwWx_dh  265-271
RBM.Graph.lwWx_lwdf  273-278
RBM.Graph.lwWx_lwGc  285-289
RBM.Graph.lwWx_gc_zero  373-392
RBM.Graph.lwWx_lwS_zero  394-395
RBM.Graph.lwWx_lwSp_zero  397-402
RBM.Graph.lwWeightExp_holds  404-429
RBM.Graph.owxT2  662-671
RBM.Graph.owxT3  673-683
RBM.Graph.owxT4  685-695
RBM.Graph.owxT2_counters  752-768
RBM.Graph.owxT3_counters  770-788
RBM.Graph.owxT4_counters  790-808
RBM.Graph.owxT1_ord  811-816
RBM.Graph.owxT2_ord  818-823
RBM.Graph.owxT3_ord  825-831
RBM.Graph.owxT4_ord  833-839
RBM.Graph.owxT2_term  860-873
RBM.Graph.owxT3_term  875-896
RBM.Graph.owxT4_term  898-920
RBM.Graph.owx_term_integral  1056-1267
RBM.Graph.owx_graph_E  1309-1367
RBM.Graph.lwWxInstSz  1381-1382
RBM.Graph.lwWx_inst_hE  1384-1384
RBM.Graph.lwWx_inst_im  1386-1386
RBM.Graph.lwWx_inst_norm  1388-1389
RBM.Graph.lwWxInstSp  1449-1451
RBM.Graph.lwWxInstM  1453-1455
RBM.Graph.lwWx_inst_hSp  1457-1460
RBM.Graph.lwWx_inst_hM  1462-1463
RBM.Graph.lwWxInstGraph  1474-1480
### RBM3D.Graph.LWXiExp  (4 unreached of 32)
private RBM.Graph.lwXE_ρ0  730-731
private RBM.Graph.lwXE_ρ0_nonneg  733-734
private RBM.Graph.lwXE_ρ0_rad  736-751
private RBM.Graph.lwXE_Entry  753-757
### RBM3D.Graph.LocalRegular  (83 unreached of 163)
RBM.Graph.localReg_StepWalk.single  159-159
RBM.Graph.localReg_stepMS  186-187
RBM.Graph.localReg_offDiag_le  195-195
RBM.Graph.localReg_offDiag_mono  197-198
RBM.Graph.localReg_offDiag_of_diag  200-201
RBM.Graph.localReg_offDiag_eq_self  203-204
RBM.Graph.localReg_offDiag_le_of_le_add_diag  213-225
RBM.Graph.localReg_Fam  227-233
RBM.Graph.localReg_Fam.mono  235-239
RBM.Graph.localReg_Fam.of_add_diag  241-245
RBM.Graph.localReg_stepEdges_nil  248-248
RBM.Graph.localReg_stepMS_map  265-270
RBM.Graph.localReg_Fam.map  272-313
RBM.Graph.localReg_exists_through  315-329
RBM.Graph.localReg_Fam.thr  331-418
RBM.Graph.localReg_Fam.strict  470-488
RBM.Graph.localReg_FamRepl  490-492
RBM.Graph.localReg_FamRepl.of_le  494-496
RBM.Graph.localReg_FamRepl.of_diag  498-500
RBM.Graph.localReg_FamRepl.trans  502-504
RBM.Graph.localReg_FamRepl.add  506-515
RBM.Graph.localReg_FamRepl.thr  517-519
RBM.Graph.localReg_FamRepl.refl  521-522
RBM.Graph.localReg_FamRepl.thr'  524-529
RBM.Graph.localReg_FamRepl.thr3  531-536
RBM.Graph.localReg_FamRepl.same  538-543
RBM.Graph.SEdge.localReg_ends_map  558-559
RBM.Graph.LGraph.localReg_PathFam  570-573
RBM.Graph.LGraph.localReg_pathFam_map  589-625
RBM.Graph.localReg_lvl1Split_ends  627-651
RBM.Graph.LGraph.localReg_pathFam_partition  653-702
RBM.Graph.LGraph.localReg_pathFam_stage1  704-718
RBM.Graph.SEdge.localReg_ends_twist  720-722
RBM.Graph.localReg_ends_list_twist  724-728
RBM.Graph.LGraph.localReg_endsMS_of_perm  735-738
RBM.Graph.localReg_endsMS_twistOwx  740-751
RBM.Graph.localReg_VRepl  753-755
RBM.Graph.localReg_pathFam_term  757-803
RBM.Graph.localReg_owxDE_ends_mol  805-812
RBM.Graph.localReg_VRepl.deriv  814-827
RBM.Graph.localReg_VRepl.same  829-839
RBM.Graph.SEdge.localReg_ends_mk  841-842
RBM.Graph.localReg_owxEmb_inr_eq  848-849
RBM.Graph.localReg_pathFam_owxT3  865-889
RBM.Graph.localReg_pathFam_owxT1  891-904
RBM.Graph.localReg_pathFam_owxT2  906-928
RBM.Graph.localReg_pathFam_owxT4  930-957
RBM.Graph.localReg_lwSymmFrame_endsMS  967-974
RBM.Graph.localReg_lwSymmFrame2_endsMS  976-984
RBM.Graph.localReg_pathFam_oe1xOwx  986-998
RBM.Graph.localReg_pathFam_oe1xD  1005-1027
RBM.Graph.localReg_pathFam_oe1xP5  1029-1055
RBM.Graph.localReg_pathFam_oe1xP3  1057-1083
RBM.Graph.localReg_pathFam_oe1xP6  1085-1111
RBM.Graph.localReg_pathFam_oe1xP4  1113-1139
RBM.Graph.localReg_pathFam_oe2xR2  1156-1177
RBM.Graph.localReg_pathFam_oe2xR3  1179-1192
RBM.Graph.localReg_pathFam_oe2xR4  1194-1219
RBM.Graph.localReg_pathFam_oe2xR5  1221-1246
RBM.Graph.localReg_pathFam_oe2xR6  1248-1273
RBM.Graph.localReg_pathFam_oe2xR7  1275-1302
RBM.Graph.localReg_pathFam_oe2xR8  1304-1333
RBM.Graph.fxyPowGraph_two  1360-1362
RBM.Graph.localReg_fxyPowGraph_pathFam  1593-1618
RBM.Graph.localReg_pathFam_oe1xDs  1827-1852
RBM.Graph.PGraph.PathInv  1854-1857
RBM.Graph.pathInv_locStep  1859-1896
RBM.Graph.PGraph.LocReg35  1952-1953
RBM.Graph.PGraph.PathInv.exists_walks  1961-1973
RBM.Graph.fxyPowGraph_ord  1982-1987
RBM.Graph.fxyPowGraph_pathInv  1989-1990
RBM.Graph.lw_localregular_expansion  1999-2032
RBM.Graph.lw_fxyPow_integral_eq  2034-2049
RBM.Graph.localReg_inst_lwD_S_real  2060-2063
RBM.Graph.localReg_inst_lwFxyVal  2065-2068
RBM.Graph.localReg_inst_val2  2070-2073
RBM.Graph.localReg_inst_val4  2075-2078
RBM.Graph.localReg_inst_step1  2106-2110
RBM.Graph.localReg_Fam.not_of_isolated  2132-2169
RBM.Graph.LGraph.localReg_molOf_isolated  2171-2181
RBM.Graph.localReg_inst_noX  2184-2189
RBM.Graph.localReg_inst_noX_not  2191-2217
RBM.Graph.localReg_inst_expansion  2219-2243
### RBM3D.Graph.LocalRegular2  (12 unreached of 103)
RBM.Graph.SEdge.localReg2_cends_mk  573-574
RBM.Graph.localReg2_owxEmb_inr_eq  1187-1188
RBM.Graph.lw_localregular_upto5  1852-1884
RBM.Graph.localReg2_inst_step1  1900-1904
RBM.Graph.localReg2_inst_expansion  1906-1929
RBM.Graph.localReg2_inst_Q  1931-1939
RBM.Graph.localReg2_inst_Q_locStd  1941-1941
RBM.Graph.localReg2_inst_Q_pathInv2  1943-2032
RBM.Graph.localReg2_inst_Q_locReg345  2034-2037
RBM.Graph.localReg2_inst_R  2039-2045
RBM.Graph.localReg2_inst_R_locStd  2047-2047
RBM.Graph.localReg2_inst_R_not_pathInv2  2049-2063
### RBM3D.Graph.LocalRegular6a  (34 unreached of 105)
RBM.Graph.localReg6a_mem_skept  279-281
RBM.Graph.localReg6a_inst_perm  965-969
RBM.Graph.localReg6a_inst_relabel  971-976
RBM.Graph.localReg6a_inst_consLoop  978-982
RBM.Graph.localReg6a_instSplit0  984-989
RBM.Graph.localReg6a_instSplit1  991-996
RBM.Graph.localReg6a_inst_splitCirc  998-1002
RBM.Graph.localReg6a_inst_splitDrop  1004-1008
RBM.Graph.localReg6a_inst_partition  1010-1016
RBM.Graph.localReg6a_inst_nElem2  1018-1019
RBM.Graph.localReg6a_inst_nElem3  1021-1022
RBM.Graph.localReg6a_inst_bot2  1024-1028
RBM.Graph.localReg6a_inst_bot3  1030-1034
RBM.Graph.localReg6a_inst_nElemLocStd  1036-1037
RBM.Graph.localReg6a_inst_cost2  1039-1044
RBM.Graph.localReg6a_inst_cost3  1046-1051
RBM.Graph.localReg6a_inst_inv2  1053-1054
RBM.Graph.localReg6a_inst_inv3  1056-1057
RBM.Graph.localReg6a_instXY  1059-1066
RBM.Graph.localReg6a_instXY_locStd  1068-1068
RBM.Graph.localReg6a_instXY_ord  1070-1070
RBM.Graph.localReg6a_instXY_sIntCls  1073-1078
RBM.Graph.localReg6a_instXY_sElemCls  1081-1082
RBM.Graph.localReg6a_instXY_far  1084-1094
RBM.Graph.localReg6a_instXY_all  1096-1108
RBM.Graph.localReg6a_instXY_far_ord  1110-1112
RBM.Graph.localReg6a_instXY_all_ord  1114-1116
RBM.Graph.localReg6a_instQ_int_card  1123-1143
RBM.Graph.localReg6a_instQ_kept  1146-1151
RBM.Graph.localReg6a_instQ_all  1154-1167
RBM.Graph.localReg6a_instQ_locStd  1169-1170
RBM.Graph.localReg6a_instQ_ord  1172-1173
RBM.Graph.localReg6a_instQ_all_ord  1175-1177
RBM.Graph.localReg6a_instQ_far_ord  1179-1182
### RBM3D.Graph.LocalRegular6b  (36 unreached of 154)
RBM.Graph.scostLL_refl  85-88
private RBM.Graph.scostLL_el_eq_one  155-156
RBM.Graph.scostLL_elem_E3  236-237
RBM.Graph.scostLL_elem_ne_zero  251-255
RBM.Graph.scostLL_split_inl  1587-1595
RBM.Graph.localReg6b_inst_loop  1939-1942
RBM.Graph.localReg6b_inst_addLoop  1950-1953
RBM.Graph.localReg6b_inst_moveLoopPerm  1955-1958
RBM.Graph.localReg6b_inst_moveLoop  1960-1963
RBM.Graph.localReg6b_instCyc  1965-1970
RBM.Graph.localReg6b_inst_contract  1972-1976
RBM.Graph.localReg6b_instCyc_bot  1979-1987
RBM.Graph.localReg6b_instCyc_contract_bot  1990-2002
RBM.Graph.localReg6b_instCyc_L_bot  2005-2014
RBM.Graph.localReg6b_inst_repair  2016-2022
RBM.Graph.localReg6b_instCyc_repair_forced  2024-2028
RBM.Graph.localReg6b_inst_trans  2043-2049
RBM.Graph.localReg6b_phi  2051-2054
RBM.Graph.localReg6b_phi_surj  2056-2059
RBM.Graph.localReg6b_inst_T2  2061-2071
RBM.Graph.localReg6b_inst_T2_all  2073-2085
RBM.Graph.localReg6b_inst_transfer  2087-2096
RBM.Graph.localReg6b_inst_loop_placement  2187-2191
RBM.Graph.localReg6b_inst_moveLoop_placement  2193-2199
RBM.Graph.localReg6b_inst_patterns  2201-2236
RBM.Graph.localReg6b_inst_refl  2238-2239
RBM.Graph.localReg6b_inst_scost_eq  2242-2247
RBM.Graph.localReg6b_inst_fresh_classes  2250-2260
RBM.Graph.localReg6b_instS  2262-2268
RBM.Graph.localReg6b_inst_moveSC_Gamma2  2270-2283
RBM.Graph.localReg6b_inst_surgery  2286-2303
RBM.Graph.localReg6b_inst_localise  2306-2325
RBM.Graph.localReg6b_inst_contractPerm  2327-2340
RBM.Graph.localReg6b_inst_contractGamma2  2342-2346
RBM.Graph.localReg6b_inst_s55  2348-2356
RBM.Graph.localReg6b_inst_s55_prims  2358-2376
### RBM3D.Graph.LocalRegular6c  (20 unreached of 100)
private RBM.Graph.localReg6c_row_sc_k2_raw  695-699
private RBM.Graph.localReg6c_row_sc_k2  959-963
private RBM.Graph.localReg6c_card_image_ker  1448-1459
private RBM.Graph.localReg6c_scost_ker  1462-1494
RBM.Graph.localReg6c_mapXYA  1504-1507
RBM.Graph.localReg6c_mapCyc  1509-1512
RBM.Graph.localReg6c_mapInj  1514-1516
RBM.Graph.localReg6c_inst_moveSC  1518-1524
RBM.Graph.localReg6c_inst_moveSC_values  1526-1552
RBM.Graph.localReg6c_inst_moveSC_cyc  1554-1557
RBM.Graph.localReg6c_inst_moveSC_cyc_values  1559-1575
RBM.Graph.localReg6c_inst_moveOutPerm  1577-1589
RBM.Graph.localReg6c_inst_moveOut  1591-1596
RBM.Graph.localReg6c_inst_dmovePerm  1598-1606
RBM.Graph.localReg6c_inst_dmove  1608-1613
RBM.Graph.localReg6c_inst_dmove_cyc  1615-1619
RBM.Graph.localReg6c_inst_dmove_cyc_values  1621-1639
RBM.Graph.localReg6c_inst_T3  1667-1673
RBM.Graph.localReg6c_inst_s55  1683-1711
RBM.Graph.localReg6c_inst_alone_values  1741-1753
### RBM3D.Graph.LocalRegular6d  (48 unreached of 117)
private RBM.Graph.localReg6d_phi_a  250-251
private RBM.Graph.localReg6d_phi_b  253-254
private RBM.Graph.localReg6d_map_mk  290-292
RBM.Graph.lw_localregular  1101-1133
RBM.Graph.localReg6d_scost_ge  1142-1160
RBM.Graph.localReg6d_inst_twist  1162-1166
RBM.Graph.localReg6d_inst_T2  1168-1171
RBM.Graph.localReg6d_inst_step1  1173-1178
RBM.Graph.localReg6d_inst_circ_loopExt  1180-1183
RBM.Graph.localReg6d_inst_circ_deg1  1185-1188
RBM.Graph.localReg6d_inst_circ_same  1190-1193
RBM.Graph.localReg6d_inst_weightExt  1195-1203
RBM.Graph.localReg6d_inst_edge  1205-1212
RBM.Graph.localReg6d_inst_gg  1214-1222
RBM.Graph.localReg6d_inst_weightExt_conc  1224-1235
RBM.Graph.localReg6d_inst_edge_conc  1237-1246
RBM.Graph.localReg6d_inst_gg_conc  1248-1258
RBM.Graph.localReg6d_inst_T1  1260-1262
RBM.Graph.localReg6d_inst_T4  1264-1269
RBM.Graph.localReg6d_inst_P6  1271-1276
RBM.Graph.localReg6d_inst_R4  1278-1283
RBM.Graph.localReg6d_inst_R5  1285-1291
RBM.Graph.localReg6d_inst_R6  1293-1298
RBM.Graph.localReg6d_inst_R7  1300-1304
RBM.Graph.localReg6d_inst_R8  1306-1311
RBM.Graph.localReg6d_instG  1313-1318
RBM.Graph.localReg6d_inst_P5  1320-1323
RBM.Graph.localReg6d_inst_ll_twist  1325-1328
RBM.Graph.localReg6d_inst_ll_perm  1330-1333
RBM.Graph.localReg6d_inst_ll_frame  1335-1340
RBM.Graph.localReg6d_inst_ll_frame2  1342-1351
RBM.Graph.localReg6d_instEdgeG  1353-1362
RBM.Graph.localReg6d_instEdgep  1364-1367
RBM.Graph.localReg6d_inst_locStep_edge3  1369-1375
RBM.Graph.localReg6d_inst_edge3_normal  1377-1378
RBM.Graph.localReg6d_inst_edge3_circ  1380-1383
RBM.Graph.localReg6d_instGGG  1385-1392
RBM.Graph.localReg6d_instGGp  1394-1397
RBM.Graph.localReg6d_instGGq  1399-1401
RBM.Graph.localReg6d_inst_locStep_gg3  1403-1410
RBM.Graph.localReg6d_inst_gg3_normal  1412-1413
RBM.Graph.localReg6d_inst_gg3_circ  1415-1418
RBM.Graph.localReg6d_inst_edge3_terms  1420-1424
RBM.Graph.localReg6d_inst_gg3_terms  1426-1427
RBM.Graph.localReg6d_inst_edge3  1429-1443
RBM.Graph.localReg6d_inst_gg3  1445-1458
RBM.Graph.localReg6d_inst_expansion  1465-1493
RBM.Graph.localReg6d_inst_last  1495-1502
### RBM3D.Graph.Model  (32 unreached of 32)
RBM.Graph.Case  52-66
RBM.Graph.instDecidableEqCase  66-66
RBM.Graph.Pattern  68-79
RBM.Graph.instDecidableEqPattern  79-79
RBM.Graph.instDecidableEqPattern.decEq  79-79
RBM.Graph.Pattern.of  85-87
RBM.Graph.Pattern.Realizable  89-93
RBM.Graph.Pattern.instDecidableRealizable  95-96
RBM.Graph.Pattern.of_realizable  98-102
RBM.Graph.Pattern.all  104-107
RBM.Graph.Pattern.mem_all  109-110
RBM.Graph.Pattern.card_realizable  112-114
RBM.Graph.Pattern.classify  116-138
RBM.Graph.Pattern.classify_eq_i_iff  147-150
RBM.Graph.Pattern.classify_eq_ii_iff  152-155
RBM.Graph.Pattern.classify_eq_iii_iff  157-160
RBM.Graph.Pattern.classify_eq_iv_iff  162-165
RBM.Graph.Pattern.classify_eq_v_iff  167-170
RBM.Graph.Pattern.classify_eq_vi_iff  172-175
RBM.Graph.classify  183-185
RBM.Graph.classify_eq_i_iff  193-196
RBM.Graph.classify_eq_ii_iff  198-201
RBM.Graph.classify_eq_iii_iff  203-206
RBM.Graph.classify_eq_iv_iff  208-211
RBM.Graph.classify_eq_v_iff  213-216
RBM.Graph.classify_eq_vi_iff  218-223
RBM.Graph.classify_vi_occurs  225-226
RBM.Graph.Case.Rel  234-242
RBM.Graph.Case.gain  244-251
RBM.Graph.Case.one_le_gain  253-254
RBM.Graph.Case.ord_ge  256-263
RBM.Graph.ord_weight_step  267-273
### RBM3D.Graph.ScalingOrder  (7 unreached of 9)
RBM.Graph.ord_ge_of_counters  67-73
RBM.Graph.ord_case_ii  75-79
RBM.Graph.ord_case_iii  81-85
RBM.Graph.ord_case_iv  87-91
RBM.Graph.ord_case_v  93-97
RBM.Graph.ord_case_vi  99-109
RBM.Graph.ord_case_v_eq_ii  111-116
### RBM3D.Green.CondDom  (50 unreached of 75)
RBM.Green.W_le_self  292-299
RBM.Green.inv_etaT_le_inv_etaT  470-476
private RBM.Green.condDomCkI  822-822
private RBM.Green.condDomCk0  824-825
private RBM.Green.condDomCkC  827-828
private RBM.Green.condDomCkSet  830-831
private RBM.Green.condDomCkSet_meas  833-834
private RBM.Green.condDom_etaT_half  885-891
private RBM.Green.condDom_norm_ibpRem_le  893-937
private RBM.Green.condDom_inst_offdiag  939-957
private RBM.Green.condDomCkY  967-969
private RBM.Green.condDomCkY_meas  971-973
private RBM.Green.condDomCkY_abs_pow_le  975-979
private RBM.Green.condDomCkY_int  981-987
private RBM.Green.condDomCkY_moment  989-1005
private RBM.Green.condDom_inst_moment  1007-1013
private RBM.Green.condDomCkS  1015-1021
private RBM.Green.condDom_no_hsize  1023-1064
private RBM.Green.condStableK  1072-1073
private RBM.Green.condStableX  1075-1077
private RBM.Green.condStableX_meas  1079-1081
private RBM.Green.condStableX_norm_le  1083-1086
private RBM.Green.condStableX_sub_norm_le  1088-1092
private RBM.Green.condStable_three_le  1094-1096
private RBM.Green.condStable_inst_envelope  1098-1126
private RBM.Green.condStable_inst_subself  1128-1162
private RBM.Green.condStable_inst_le_left_on  1164-1173
private RBM.Green.condStable_inst_of_highProb  1175-1182
private RBM.Green.condStable_inst_const  1184-1191
private RBM.Green.condStable_inst_inv_etaT  1193-1195
private RBM.Green.condStableΩ  1210-1212
private RBM.Green.condStable_seqXmat  1214-1257
private RBM.Green.blk_BB  1263-1266
private RBM.Green.blk_BP  1268-1271
private RBM.Green.blk_alg  1273-1280
private RBM.Green.blk_green  1282-1290
private RBM.Green.condStable_mE_zero  1294-1299
private RBM.Green.condStable_hflow  1301-1307
private RBM.Green.condStable_zt  1309-1312
private RBM.Green.condStable_green  1314-1334
private RBM.Green.condStable_norm_realMul_I  1336-1337
private RBM.Green.condStable_goodEvent_nd  1340-1380
private RBM.Green.condStable_green_ki  1382-1386
private RBM.Green.condStable_green_ik  1388-1392
private RBM.Green.condStable_inst_minor_nd  1394-1407
private RBM.Green.condDomCk1  1411-1412
private RBM.Green.condDomCk01  1414-1419
private RBM.Green.EntryGauss_chk_gij  1434-1437
private RBM.Green.EntryGauss_chk_gii  1440-1443
private RBM.Green.EntryGauss_chk_adapters  1446-1452
### RBM3D.Green.EntryCore  (39 unreached of 100)
RBM.Green.minorMat_apply  63-64
RBM.Green.minorGreen_apply  67-68
RBM.Green.isUnit_det_minorMat  124-127
RBM.Green.sum_minorGreen_row  129-143
RBM.Green.green_off_diag_eq  145-150
RBM.Green.green_off_diag_paper  240-252
private RBM.Green.minor_check_fin2  1086-1118
private RBM.Green.chkH  1135-1135
private RBM.Green.chkG  1136-1137
private RBM.Green.chkS  1138-1138
private RBM.Green.chk_hGM  1141-1145
private RBM.Green.chk_hMG  1147-1148
private RBM.Green.chk_herm  1150-1152
private RBM.Green.chk_erase  1154-1158
private RBM.Green.chk_minor  1160-1166
private RBM.Green.chk_norm_diag  1168-1170
private RBM.Green.chk_norm_G00  1172-1173
private RBM.Green.chk_norm_G01  1175-1176
private RBM.Green.chk_norm_G10  1178-1179
private RBM.Green.chk_norm_G11  1181-1182
private RBM.Green.chk_good  1184-1187
private RBM.Green.chk_minor01  1189-1189
private RBM.Green.chk_minor10  1191-1191
private RBM.Green.chk_erase0  1193-1193
private RBM.Green.chk_erase1  1195-1195
private RBM.Green.chk_row  1197-1201
private RBM.Green.chk_col  1203-1207
private RBM.Green.chk_quad  1209-1213
private RBM.Green.chk_diag_H  1215-1217
private RBM.Green.chk_Lam1  1219-1223
private RBM.Green.chk_stable  1225-1227
private RBM.Green.entry_core_check_fin2  1229-1249
private RBM.Green.chk_green  1258-1260
private RBM.Green.chk_unit  1262-1267
private RBM.Green.zS  1301-1302
private RBM.Green.zsumc  1304-1305
private RBM.Green.zsumr  1307-1308
private RBM.Green.zsum  1310-1312
private RBM.Green.zstable  1314-1331
### RBM3D.Green.EntryDom  (22 unreached of 84)
RBM.Green.abs_blkCoef2_le  487-491
RBM.Green.sum_blkCoef2  506-512
RBM.Green.avgErr_eq_sum_blkCoef2  534-540
private RBM.Green.entryDom_card_Zd  730-731
private RBM.Green.entryDom_Zd_le_size  740-742
private RBM.Green.entryDom_card_Zd_le  744-746
private RBM.Green.entryDom_card_Zd_sq_le  748-751
private RBM.Green.entryDom_maxLoop_dom_of_loopDet  1162-1181
RBM.Green.avg_bound_stochDom  1183-1275
private RBM.Green.entryDom_mE_zero  1295-1298
private RBM.Green.entryDom_gres_zero  1300-1304
private RBM.Green.entryDom_inst_green  1306-1318
private RBM.Green.entryDom_inst_diag  1320-1324
private RBM.Green.entryDom_inst_sum_svar  1326-1329
private RBM.Green.entryDom_inst_sum_blk  1331-1333
private RBM.Green.entryDom_inst_avgErr  1335-1340
private RBM.Green.entryDom_seqHflow_zero  1378-1381
private RBM.Green.entryDom_norm_loopPM_zero  1383-1410
private RBM.Green.entryDom_loopDet_zero  1412-1421
private RBM.Green.entryDom_lde_zero  1517-1537
private RBM.Green.entryDom_goodEvent_zero  1539-1545
private RBM.Green.entryDom_lde_blockMat_zero  1574-1576
### RBM3D.Green.FlucIter  (21 unreached of 90)
RBM.Green.applyOps_nil  342-343
RBM.Green.numQ_nil  356-357
private RBM.Green.FlucIterInst.szT  820-826
private RBM.Green.FlucIterInst.site  828-831
private RBM.Green.FlucIterInst.site_inj  833-834
private RBM.Green.FlucIterInst.hE0  836-836
private RBM.Green.FlucIterInst.ht0  837-837
private RBM.Green.FlucIterInst.G  839-841
private RBM.Green.FlucIterInst.Z  843-845
RBM.Green.FlucIterInst.bddMeas_greenDiagCentered_szT  847-849
RBM.Green.FlucIterInst.bddMeas_flucDiag_szT  851-853
RBM.Green.FlucIterInst.finDep_greenDiagCentered_szT  855-857
private RBM.Green.FlucIterInst.fZ  859-860
private RBM.Green.FlucIterInst.bG  862-862
private RBM.Green.FlucIterInst.bZ  863-863
private RBM.Green.FlucIterInst.fG  864-864
private RBM.Green.FlucIterInst.w1  866-867
private RBM.Green.FlucIterInst.S12  978-979
private RBM.Green.FlucIterInst.l2  1013-1014
private RBM.Green.FlucIterInst.l2_ok  1016-1019
private RBM.Green.FlucIterInst.Lw  1035-1036
### RBM3D.Green.FlucIterGain  (43 unreached of 62)
RBM.Green.card_filter_card_image_le  162-194
private RBM.Green.flucIter_integral_prod_norm_applyOps_le_crude  908-929
private RBM.Green.flucIter_flucGainUpTo'_of_crude  931-942
private RBM.Green.FlucIterGainInst.szG  976-982
private RBM.Green.FlucIterGainInst.eta_eq  984-989
private RBM.Green.FlucIterGainInst.hE0  991-991
private RBM.Green.FlucIterGainInst.ht0  992-992
private RBM.Green.FlucIterGainInst.flucGainUpTo'_szG_half  994-1002
private RBM.Green.FlucIterGainInst.flucGainUpTo'_szG_one  1004-1011
RBM.Green.FlucIterGainInst.flucGainUpTo'_szG_projections  1013-1015
private RBM.Green.FlucIterGainInst.siteA  1017-1018
private RBM.Green.FlucIterGainInst.siteB  1019-1019
private RBM.Green.FlucIterGainInst.siteB_ne_siteA  1021-1021
private RBM.Green.FlucIterGainInst.rowK  1023-1024
RBM.Green.FlucIterGainInst.flucGainUpTo'_szG_gain  1026-1040
private RBM.Green.FlucIterGainInst.vCount  1044-1046
RBM.Green.FlucIterGainInst.counting_values  1048-1051
RBM.Green.FlucIterGainInst.counting_two_mul  1053-1056
RBM.Green.FlucIterGainInst.counting_image_lone  1058-1063
RBM.Green.FlucIterGainInst.counting_mem_lone  1065-1067
RBM.Green.FlucIterGainInst.counting_card_filter  1069-1075
private RBM.Green.FlucIterGainInst.rowW  1079-1081
private RBM.Green.FlucIterGainInst.rowA  1083-1087
private RBM.Green.FlucIterGainInst.rowW_bounded  1089-1091
RBM.Green.FlucIterGainInst.rowA_card  1093-1097
RBM.Green.FlucIterGainInst.sum_prod_abs_card_image_row  1099-1107
RBM.Green.FlucIterGainInst.sum_weighted_row  1109-1119
RBM.Green.FlucIterGainInst.moment_row_p1  1123-1133
RBM.Green.FlucIterGainInst.moment_row_p2  1135-1144
private RBM.Green.FlucIterGainInst.blockW  1146-1148
private RBM.Green.FlucIterGainInst.blockA  1150-1153
private RBM.Green.FlucIterGainInst.blockW_bounded  1155-1157
RBM.Green.FlucIterGainInst.blockA_card  1159-1162
RBM.Green.FlucIterGainInst.moment_block_p1  1164-1173
RBM.Green.FlucIterGainInst.bddMeas_epsHom_flucDiag_szG  1177-1180
private RBM.Green.FlucIterGainInst.slotV  1182-1185
RBM.Green.FlucIterGainInst.iter_epsHom_budget  1187-1199
private RBM.Green.FlucIterGainInst.hgain_graded  1201-1219
private RBM.Green.FlucIterGainInst.opsOkOut_one  1221-1227
RBM.Green.FlucIterGainInst.opsOkOut_length_le_szG  1229-1234
RBM.Green.FlucIterGainInst.iter_graded  1236-1255
RBM.Green.FlucIterGainInst.iter_qRow  1257-1272
RBM.Green.FlucIterGainInst.iter_comm  1274-1282
### RBM3D.Green.FlucThreshold  (31 unreached of 75)
RBM.Green.detFlucControl_pos  458-461
RBM.Green.detFlucControl_floor  466-468
private RBM.Green.flucThreshold_control_eq_psi  729-755
private RBM.Green.flucThreshold_check_consumer  890-919
private RBM.Green.flucThresholdPsi  944-945
private RBM.Green.flucThreshold_inst_floor  947-949
private RBM.Green.flucThreshold_inst_ceiling  951-971
private RBM.Green.flucThreshold_inst_mE_zero  973-977
private RBM.Green.flucThreshold_inst_etaT_zero  979-981
private RBM.Green.flucThreshold_inst_etaT_half  983-985
private RBM.Green.flucThreshold_inst_eta_half  987-993
private RBM.Green.flucThreshold_inst_eta_zero  995-999
private RBM.Green.flucThreshold_inst_theta  1001-1005
private RBM.Green.flucThreshold_inst_hE  1007-1007
private RBM.Green.flucThreshold_inst_ll_zero  1009-1013
private RBM.Green.flucThreshold_inst_polyLo  1015-1019
private RBM.Green.flucThreshold_inst_polyHi_half  1021-1024
private RBM.Green.flucThreshold_inst_bounds  1026-1052
private RBM.Green.flucThreshold_inst_highProb_half  1054-1065
private RBM.Green.flucThreshold_inst_highProb_zero  1067-1076
private RBM.Green.flucThreshold_inst_measureReal  1078-1089
private RBM.Green.flucThreshold_inst_hsmall_half  1091-1111
private RBM.Green.flucThreshold_inst_hsmall_zero  1113-1132
private RBM.Green.flucThreshold_inst_flucGain_half  1134-1150
private RBM.Green.flucThreshold_inst_flucGain_zero  1152-1166
private RBM.Green.flucThreshold_inst_poly  1168-1195
private RBM.Green.flucThreshold_neg_aux  1197-1213
private RBM.Green.flucThreshold_delta3_le  1215-1248
private RBM.Green.flucThreshold_psi3_le  1250-1255
private RBM.Green.flucThreshold_literal_false  1257-1275
private RBM.Green.flucThreshold_inst_slice3  1277-1291
### RBM3D.Green.FlucVanish  (36 unreached of 130)
RBM.Green.GreenDeriv_crd_injective  364-367
RBM.Green.GreenDeriv_slice_apply  369-371
RBM.Green.epsHom_inl  979-979
RBM.Green.epsHom_inr  981-982
RBM.Green.not_uniformWeight_svarF  1191-1241
private RBM.Green.flucVanish_isUnit_det  1282-1284
private RBM.Green.flucVanish_im_green_diag  1286-1311
private RBM.Green.flucVanish_green_diag_ne_zero  1313-1337
private RBM.Green.FlucVanishInst.zI  1354-1355
private RBM.Green.FlucVanishInst.zI_im  1357-1358
RBM.Green.FlucVanishInst.greenMinorMat_eq_minorGreen_sz0  1362-1371
RBM.Green.FlucVanishInst.condRow_greenMinorMat_apply_sz0  1373-1380
private RBM.Green.FlucVanishInst.szS  1390-1396
private RBM.Green.FlucVanishInst.c0  1398-1400
private RBM.Green.FlucVanishInst.X0  1402-1403
private RBM.Green.FlucVanishInst.X0_measurable  1405-1407
private RBM.Green.FlucVanishInst.X0_norm  1409-1410
private RBM.Green.FlucVanishInst.c0_isRowCoord  1412-1414
RBM.Green.FlucVanishInst.X0_not_finDepOffRow_szS  1416-1430
RBM.Green.FlucVanishInst.condRow_sub_condRow_szS  1432-1435
RBM.Green.FlucVanishInst.integral_condRow_szS  1437-1442
private RBM.Green.FlucVanishInst.condRow_X0  1444-1453
RBM.Green.FlucVanishInst.integral_mul_prod_eq_zero_szS  1455-1483
RBM.Green.FlucVanishInst.norm_flucDiag_le_sz0  1485-1491
RBM.Green.FlucVanishInst.continuous_green_comp_sz0_time  1495-1501
RBM.Green.FlucVanishInst.continuous_green_comp_sz0_sample  1503-1508
RBM.Green.FlucVanishInst.Xmat_eq_sum_sz0  1510-1513
RBM.Green.FlucVanishInst.hasFDerivAt_resH_sz0  1515-1523
RBM.Green.FlucVanishInst.finDep_of_Hflow_sz0  1525-1529
RBM.Green.FlucVanishInst.flucVanish_blockAvg2_eq_blkCoef2_sz0  1533-1539
RBM.Green.FlucVanishInst.flucVanish_blockAvg2_nondegenerate_sz0  1541-1555
RBM.Green.FlucVanishInst.uniformWeight_blockAvg2_sz0  1557-1565
RBM.Green.FlucVanishInst.boundedWeight_blockAvg2_sz0  1567-1576
RBM.Green.FlucVanishInst.boundedWeight_svarF_sz0  1578-1589
RBM.Green.FlucVanishInst.boundedWeight_svarF_card_sz0  1591-1597
RBM.Green.FlucVanishInst.not_uniformWeight_svarF_sz0  1599-1609
### RBM3D.Green.GbEXP  (19 unreached of 47)
private RBM.Green.gbEXPPsi  844-845
private RBM.Green.gbEXPPsi_nonneg  847-848
private RBM.Green.gbEXPPsi_ceiling  850-869
private RBM.Green.gbEXP_W_inv_not_le_psi  871-882
private RBM.Green.gbEXP_rangeCond_zero  884-889
private RBM.Green.gbEXP_inst_fixedTimeFA  891-903
private RBM.Green.gbEXP_inst_ibpDet  905-912
private RBM.Green.gbEXP_inst_fixedTimeFA_zero  914-924
private RBM.Green.gbEXP_inst_ibpDet_zero  926-935
private RBM.Green.gbEXP_inst_gbEXPV3_ij_ii  937-945
private RBM.Green.gbEXP_inst_gbEXPV3_avg  947-959
private RBM.Green.gbEXP_inst_stGbEXP  961-966
private RBM.Green.gbEXP_inst_stStep1  968-978
private RBM.Green.gbEXP_inst_eta  982-989
private RBM.Green.gbEXP_inst_weighted_block  991-1018
private RBM.Green.gbEXP_inst_weighted_row  1020-1045
private RBM.Green.gbEXP_inst_ibp_inputs  1047-1060
private RBM.Green.gbEXP_inst_weighted_of_rem  1062-1079
private RBM.Green.gbEXP_inst_bridge  1081-1118
### RBM3D.Green.IBP  (21 unreached of 68)
private RBM.Green.entryCLM_apply  310-311
RBM.Green.integral_coord_mul_green_apply  362-382
private RBM.Green.integral_const_matrix_mul_apply  704-719
RBM.Green.integral_coord_mul_Bmat_mul_green_diag  751-794
private RBM.Green.ckS  1396-1401
private RBM.Green.ckI  1403-1403
private RBM.Green.ckx0  1405-1405
private RBM.Green.ckx1  1406-1406
private RBM.Green.ckx2  1407-1407
private RBM.Green.ckp0  1409-1410
private RBM.Green.ckp1  1411-1411
private RBM.Green.ck_hE  1413-1413
private RBM.Green.ck_hE2  1414-1414
private RBM.Green.ck_ht  1415-1415
private RBM.Green.ck_ht0  1416-1416
private RBM.Green.ckp0_used  1418-1420
private RBM.Green.ckp1_used  1422-1424
private RBM.Green.ck_x01  1426-1432
private RBM.Green.ck_x20  1434-1439
private RBM.Green.ck_x21  1441-1446
private RBM.Green.ck_offDiag  1448-1459
### RBM3D.Green.IBPPoly  (9 unreached of 67)
RBM.Green.modelChaos_B  519-520
private RBM.Green.IBPInst.c0  1126-1127
private RBM.Green.IBPInst.c1  1129-1130
RBM.Green.IBPInst.gaussIBP_sz0_polyInt  1132-1137
RBM.Green.IBPInst.seqGvar_sz0_c0  1139-1149
RBM.Green.IBPInst.seqGvar_sz0_c0_pos  1151-1153
RBM.Green.IBPInst.gaussIBP_sz0_stein_cubic  1155-1163
RBM.Green.IBPInst.stochDom_ldeQuad_sz0  1165-1175
RBM.Green.IBPInst.hwConst_two  1193-1196
### RBM3D.Green.IBPRem  (30 unreached of 47)
private RBM.Green.IBPRemCkE  557-558
private RBM.Green.IBPRemCkT  560-561
private RBM.Green.IBPRemCkPsi  563-564
private RBM.Green.IBPRemCkDelta  566-567
private RBM.Green.IBPRemCkGood  569-573
private RBM.Green.IBPRemCk_W_ge  575-579
private RBM.Green.IBPRemCk_W3_le_size  581-588
private RBM.Green.IBPRemCk_hE  590-591
private RBM.Green.IBPRemCk_ht1  593-594
private RBM.Green.IBPRemCk_hΨ0  596-597
private RBM.Green.IBPRemCk_Psi_mul  599-605
private RBM.Green.IBPRemCk_hΨ1  607-611
private RBM.Green.IBPRemCk_hΨlow  613-619
private RBM.Green.IBPRemCk_etaT  621-627
private RBM.Green.IBPRemCk_hEnv  629-639
private RBM.Green.IBPRemCk_hδ1  641-642
private RBM.Green.IBPRemCk_offPair_nonempty  644-652
private RBM.Green.IBPRemCk_hll  661-664
private RBM.Green.IBPRemCk_hΩ  666-684
private RBM.Green.IBPRem_inst_green_diag_sub  691-698
private RBM.Green.IBPRem_inst_green_offdiag  700-707
private RBM.Green.IBPRem_inst_prod_green_diag_sub  709-718
private RBM.Green.IBPRem_inst_condRow_prod_green_diag  720-731
private RBM.Green.IBPRem_inst_greenDiagCentered_sub_minor  733-743
private RBM.Green.IBPRem_inst_condRow_greenDiagCentered_sub_self  745-758
private RBM.Green.IBPRem_inst_ibpRem_offdiag  760-767
private RBM.Green.IBPRem_inst_greenDiagCentered_one  769-777
private RBM.Green.IBPRem_inst_condExpDiag_one  779-787
private RBM.Green.IBPRem_inst_ibpRem_diag  789-797
private RBM.Green.IBPRem_inst_ibpRem  799-810
### RBM3D.Green.LDE  (54 unreached of 118)
RBM.Green.LDE_norm_flucAvg_le_of_boundedWeight  360-376
RBM.Green.flucAvg_card_Z2_le_size  438-446
RBM.Green.LDE_greenMinorMatD  476-485
RBM.Green.LDE_greenDiagCenteredD  487-491
RBM.Green.LDE_greenMinorDiagCenteredD  493-498
RBM.Green.LDE_flucDiagD  500-504
RBM.Green.LDE_flucDiagMinorD  506-512
RBM.Green.LDE_flucAvgD  514-518
RBM.Green.LDE_condExpDiagD  520-524
RBM.Green.LDE_shift_zero  526-548
RBM.Green.LDE_measurable_HflowD_sub  552-558
RBM.Green.LDE_measurable_green_applyD  560-563
RBM.Green.LDE_measurable_greenMinorMat_applyD  565-577
RBM.Green.LDE_measurable_greenDiagCenteredD  579-581
RBM.Green.LDE_measurable_greenMinorDiagCenteredD  583-586
RBM.Green.LDE_measurable_flucDiagD  588-592
RBM.Green.LDE_measurable_flucAvgD  594-597
RBM.Green.LDE_norm_green_apply_leD  603-610
RBM.Green.LDE_norm_greenMinorMat_apply_leD  612-621
RBM.Green.LDE_norm_greenDiagCentered_le_envD  623-627
RBM.Green.LDE_norm_greenMinorDiagCentered_le_envD  629-632
RBM.Green.LDE_FlucBoundD  636-651
RBM.Green.LDE_norm_flucDiag_sub_flucDiagMinor_leD  653-694
RBM.Green.LDE_flucBound_envD  696-717
RBM.Green.LDE_norm_flucAvg_leD  719-729
RBM.Green.LDE_norm_flucAvg_le_of_boundedWeightD  731-742
RBM.Green.LDE_integrable_norm_flucAvg_powD  744-759
RBM.Green.minorRowConj_eq_greenMinor  854-865
RBM.Green.ldeColLHS_eq  867-886
RBM.Green.rowVarSum_minorRowConj_eq  888-905
private RBM.Green.LDEInst.inst_zt_im_ne_zero  1506-1507
RBM.Green.LDEInst.tendsto_W_sz0  1511-1513
RBM.Green.LDEInst.eventually_le_W_sz0  1515-1518
RBM.Green.LDEInst.eventually_le_W_sz0_million  1520-1522
RBM.Green.LDEInst.stochDom_normSq_Hflow_diag_sz0  1526-1534
RBM.Green.LDEInst.diag_variance_sz0  1536-1548
private RBM.Green.LDEInst.szT  1550-1557
RBM.Green.LDEInst.integral_norm_Hflow_diag_pow_szT  1559-1570
RBM.Green.LDEInst.stochDom_ldeRow_sz0  1574-1583
RBM.Green.LDEInst.stochDom_ldeCol_sz0  1585-1594
RBM.Green.LDEInst.LDE_shiftD_sz0  1596-1600
RBM.Green.LDEInst.LDE_shiftD_sz0_isHermitian  1602-1603
RBM.Green.LDEInst.green_diag_ne_zero_sz0  1711-1718
RBM.Green.LDEInst.ldeColLHS_eq_sz0  1720-1727
RBM.Green.LDEInst.rowVarSum_minorRowConj_eq_sz0  1729-1736
RBM.Green.LDEInst.minorRowConj_eq_greenMinor_sz0  1738-1744
private RBM.Green.LDEInst.inst_zt_zero_im  1748-1754
RBM.Green.LDEInst.flucBound_env_sz0  1756-1761
RBM.Green.LDEInst.norm_green_apply_le_etaT_sz0  1763-1767
RBM.Green.LDEInst.norm_flucAvg_le_boundedWeight_sz0  1769-1778
RBM.Green.LDEInst.norm_flucAvg_le_sz0  1780-1787
RBM.Green.LDEInst.card_blockAvg_support_sz0  1791-1798
RBM.Green.LDEInst.card_Sblk_support_sz0  1800-1808
RBM.Green.LDEInst.flucAvg_card_sz0  1810-1819
### RBM3D.Green.LDEQuad  (14 unreached of 89)
private RBM.Green.chkX  915-916
private RBM.Green.chkY  918-921
private RBM.Green.chkCo  923-924
private RBM.Green.chkMat  926-931
private RBM.Green.chkY_injective  933-935
private RBM.Green.chkCo_injective  937-941
private RBM.Green.chkChaos  943-958
private RBM.Green.chk_gvarF_offDiag  960-965
private RBM.Green.chk_svarF_false  967-977
private RBM.Green.chk_svarF_true  979-992
private RBM.Green.chk_w  994-1001
private RBM.Green.chk_sg  1003-1008
private RBM.Green.chk_tame_coord  1010-1013
private RBM.Green.chk_euler  1015-1020
### RBM3D.Green.LDEQuadMom  (15 unreached of 52)
private RBM.Green.chkMPos  802-805
private RBM.Green.chkMPos_injective  807-810
private RBM.Green.chkMCo  812-814
private RBM.Green.chkMG  816-817
private RBM.Green.chkM_green  819-820
private RBM.Green.chkMCo_injective  822-827
private RBM.Green.chkMChaos  829-843
private RBM.Green.chkMS  845-847
private RBM.Green.chkM_gvarF_offDiag  849-854
private RBM.Green.chkM_svarF_one  856-866
private RBM.Green.chkM_svarF_two  868-881
private RBM.Green.chkM_sg  883-892
private RBM.Green.chkM_sg'  894-897
private RBM.Green.chkM_sg_pos  899-909
private RBM.Green.chkMH  961-964
### RBM3D.Green.LDEQuadT  (13 unreached of 73)
private RBM.Green.chkTPos  1038-1041
private RBM.Green.chkTPos_injective  1043-1046
private RBM.Green.chkTCo  1048-1050
private RBM.Green.chkTG  1052-1053
private RBM.Green.chkT_green  1055-1056
private RBM.Green.chkTCo_injective  1058-1063
private RBM.Green.chkTChaos  1065-1079
private RBM.Green.chkT_gvarF_offDiag  1081-1086
private RBM.Green.chkT_svarF_one  1088-1098
private RBM.Green.chkT_svarF_two  1100-1113
private RBM.Green.chkT_sg  1115-1123
private RBM.Green.chkT_sg_pos  1125-1134
private RBM.Green.chkT_Vq_pos  1136-1157
### RBM3D.Green.LocalLaw  (15 unreached of 65)
RBM.Green.asGMcSeq_iff  148-152
private RBM.Green.localLaw_seqHflow_zero  315-317
RBM.Green.localLawDetSeq_time_zero  862-869
RBM.Green.condDiagBlk_time_zero  871-876
RBM.Green.fixedTimeFASeq_time_zero  878-890
RBM.Green.ibpDetSeq_time_zero  892-899
RBM.Green.not_sizeTendsto_bandwidth_of_W_one  901-912
private RBM.Green.localLaw_inst_hE  971-972
private RBM.Green.localLaw_inst_W_inv_le  974-981
private RBM.Green.localLaw_inst_floor  983-986
private RBM.Green.localLaw_inst_rangeCond_zero  988-993
private RBM.Green.localLaw_norm_loopPM_zero  995-1023
private RBM.Green.localLaw_inst_loopDet_zero  1025-1032
private RBM.Green.localLaw_inst_gavL  1094-1102
RBM.Green.LocalLaw_loopFloor_literal_false  1201-1251
### RBM3D.Green.MinorDiff  (75 unreached of 129)
RBM.Green.deltaFam_apply  113-114
RBM.Green.iterDeltaFam_nil  119-119
RBM.Green.gFam_apply  435-436
RBM.Green.gInvFam_apply  438-439
private RBM.Green.MinorDiffInst.szM  935-941
private RBM.Green.MinorDiffInst.siteA  943-944
private RBM.Green.MinorDiffInst.siteB  945-945
private RBM.Green.MinorDiffInst.siteC  946-946
private RBM.Green.MinorDiffInst.siteD  947-947
private RBM.Green.MinorDiffInst.siteE  948-948
private RBM.Green.MinorDiffInst.hE0  950-950
private RBM.Green.MinorDiffInst.hBA  952-952
private RBM.Green.MinorDiffInst.hCA  953-953
private RBM.Green.MinorDiffInst.hDA  954-954
private RBM.Green.MinorDiffInst.hCB  955-955
private RBM.Green.MinorDiffInst.hDB  956-956
private RBM.Green.MinorDiffInst.hDC  957-957
private RBM.Green.MinorDiffInst.hAB  958-958
private RBM.Green.MinorDiffInst.hAD  959-959
private RBM.Green.MinorDiffInst.hBC  960-960
private RBM.Green.MinorDiffInst.hBD  961-961
private RBM.Green.MinorDiffInst.hCD  962-962
private RBM.Green.MinorDiffInst.seqHflow_zero_omega  966-972
private RBM.Green.MinorDiffInst.sqrt_four  974-975
private RBM.Green.MinorDiffInst.mE_zero  977-979
private RBM.Green.MinorDiffInst.zt_u  981-985
private RBM.Green.MinorDiffInst.green_zero  987-992
private RBM.Green.MinorDiffInst.inv_neg_zt  994-999
private RBM.Green.MinorDiffInst.zt_ne_zero  1001-1003
private RBM.Green.MinorDiffInst.norm_diag_sub  1005-1010
private RBM.Green.MinorDiffInst.goodEvent_omega_zero  1012-1023
private RBM.Green.MinorDiffInst.zt_im_ne  1025-1027
private RBM.Green.MinorDiffInst.check_hg  1029-1036
RBM.Green.MinorDiffInst.inst_gEnt_nonconst  1038-1052
RBM.Green.MinorDiffInst.inst_constants  1054-1057
RBM.Green.MinorDiffInst.inst_endpoint  1061-1069
RBM.Green.MinorDiffInst.inst_endpoint_num  1071-1079
RBM.Green.MinorDiffInst.inst_diag  1081-1085
RBM.Green.MinorDiffInst.inst_diag_removed  1087-1091
RBM.Green.MinorDiffInst.inst_atom  1093-1104
RBM.Green.MinorDiffInst.inst_atom_entry  1106-1113
RBM.Green.MinorDiffInst.inst_atom_inv  1115-1121
RBM.Green.MinorDiffInst.inst_gFam  1123-1130
RBM.Green.MinorDiffInst.inst_gInvFam  1132-1140
RBM.Green.MinorDiffInst.inst_first_diff  1142-1150
RBM.Green.MinorDiffInst.inst_eq_iter  1152-1160
private RBM.Green.MinorDiffInst.word3  1164-1166
RBM.Green.MinorDiffInst.inst_bddMeas  1168-1176
RBM.Green.MinorDiffInst.inst_qList  1178-1179
RBM.Green.MinorDiffInst.inst_qList_nodup  1181-1183
RBM.Green.MinorDiffInst.inst_mem_qList_ne  1185-1188
RBM.Green.MinorDiffInst.inst_bddMeas_minorDiff  1190-1195
RBM.Green.MinorDiffInst.inst_qRow  1197-1206
RBM.Green.MinorDiffInst.inst_flucDiagSet_eq  1208-1216
private RBM.Green.MinorDiffInst.toyPow  1224-1226
private RBM.Green.MinorDiffInst.toyHalf  1228-1228
private RBM.Green.MinorDiffInst.toy_half_delta  1230-1232
private RBM.Green.MinorDiffInst.toy_quarter_delta  1234-1236
private RBM.Green.MinorDiffInst.toy_diffBd_pow  1238-1263
private RBM.Green.MinorDiffInst.toy_diffBd_half  1265-1268
RBM.Green.MinorDiffInst.inst_mul  1270-1277
RBM.Green.MinorDiffInst.inst_mul_use  1279-1283
RBM.Green.MinorDiffInst.inst_inv  1285-1289
RBM.Green.MinorDiffInst.inst_leibniz  1291-1297
RBM.Green.MinorDiffInst.inst_calculus  1299-1314
RBM.Green.MinorDiffInst.inst_monotone  1316-1323
RBM.Green.MinorDiffInst.inst_congr  1325-1330
RBM.Green.MinorDiffInst.inst_le_self  1332-1335
RBM.Green.MinorDiffInst.inst_zero  1337-1338
RBM.Green.MinorDiffInst.inst_mono  1340-1344
RBM.Green.MinorDiffInst.inst_neg  1346-1348
RBM.Green.MinorDiffInst.inst_congrBd  1350-1353
RBM.Green.MinorDiffInst.inst_delta  1355-1357
RBM.Green.MinorDiffInst.inst_mono_p  1359-1361
RBM.Green.MinorDiffInst.inst_shift  1363-1365
### RBM3D.Green.MinorDiffCond  (58 unreached of 95)
RBM.Green.badTower_zero  141-142
RBM.Green.minorDiffCond_meas_badStep_le_size  259-266
private RBM.Green.MinorDiffCondInst.szC  956-962
private RBM.Green.MinorDiffCondInst.siteA  964-965
private RBM.Green.MinorDiffCondInst.siteB  966-966
private RBM.Green.MinorDiffCondInst.siteC  967-967
private RBM.Green.MinorDiffCondInst.siteB_ne_siteA  969-969
private RBM.Green.MinorDiffCondInst.siteC_ne_siteA  970-970
private RBM.Green.MinorDiffCondInst.siteB_ne_siteC  971-971
RBM.Green.MinorDiffCondInst.inst_size  973-975
private RBM.Green.MinorDiffCondInst.hE0  977-977
private RBM.Green.MinorDiffCondInst.sqrt_four  979-980
private RBM.Green.MinorDiffCondInst.mE_zero  982-984
private RBM.Green.MinorDiffCondInst.zt_zero  986-988
private RBM.Green.MinorDiffCondInst.etaT_zero  990-992
private RBM.Green.MinorDiffCondInst.seqHflow_zero_time  994-997
private RBM.Green.MinorDiffCondInst.green_zero_I  999-1004
private RBM.Green.MinorDiffCondInst.goodEvent_I  1006-1012
private RBM.Green.MinorDiffCondInst.llErr_zero  1014-1022
RBM.Green.MinorDiffCondInst.inst_badBase_null  1024-1031
RBM.Green.MinorDiffCondInst.inst_condEnv  1033-1037
RBM.Green.MinorDiffCondInst.inst_minorDiffC_one  1039-1042
RBM.Green.MinorDiffCondInst.inst_condEps  1044-1048
RBM.Green.MinorDiffCondInst.inst_condCost  1050-1054
private RBM.Green.MinorDiffCondInst.inst_hε  1056-1057
private RBM.Green.MinorDiffCondInst.inst_hB1  1059-1063
private RBM.Green.MinorDiffCondInst.inst_B  1065-1070
private RBM.Green.MinorDiffCondInst.inst_badTower_null  1072-1084
private RBM.Green.MinorDiffCondInst.inst_hsmall  1086-1096
RBM.Green.MinorDiffCondInst.inst_minorDiffGain  1098-1109
RBM.Green.MinorDiffCondInst.inst_flucGain  1111-1120
private RBM.Green.MinorDiffCondInst.halfS  1124-1127
private RBM.Green.MinorDiffCondInst.measurableSet_halfS  1129-1130
RBM.Green.MinorDiffCondInst.inst_meas_badStep  1132-1137
RBM.Green.MinorDiffCondInst.inst_meas_badTower  1139-1144
RBM.Green.MinorDiffCondInst.inst_meas_badTower_size  1146-1151
RBM.Green.MinorDiffCondInst.inst_badFamily  1153-1158
private RBM.Green.MinorDiffCondInst.notMem_badStep_one  1160-1167
private RBM.Green.MinorDiffCondInst.zero_notMem_tower  1169-1173
private RBM.Green.MinorDiffCondInst.hEnv_flucDiagSet  1175-1182
RBM.Green.MinorDiffCondInst.inst_norm_applyOps_le_badFamily  1184-1197
RBM.Green.MinorDiffCondInst.inst_envelope  1199-1209
RBM.Green.MinorDiffCondInst.inst_condEnv_two  1211-1215
RBM.Green.MinorDiffCondInst.inst_gain_applied  1234-1243
private RBM.Green.MinorDiffCondInst.zt_half_im  1248-1250
private RBM.Green.MinorDiffCondInst.etaT_half  1252-1254
RBM.Green.MinorDiffCondInst.inst_condEnv_half  1256-1260
RBM.Green.MinorDiffCondInst.inst_envelope_half  1262-1273
private RBM.Green.MinorDiffCondInst.hEnv_flucDiagSet_half  1275-1281
RBM.Green.MinorDiffCondInst.inst_norm_applyOps_le_badFamily_half  1283-1298
RBM.Green.MinorDiffCondInst.inst_integral_prod_half  1300-1328
RBM.Green.MinorDiffCondInst.inst_minorDiffC_zero  1333-1336
private RBM.Green.MinorDiffCondInst.inst_pos_cost  1338-1341
private RBM.Green.MinorDiffCondInst.inst_pos_hB1  1343-1347
private RBM.Green.MinorDiffCondInst.inst_pos_B  1349-1353
RBM.Green.MinorDiffCondInst.inst_minorDiffGain_pos  1355-1374
RBM.Green.MinorDiffCondInst.inst_flucGain_pos  1376-1393
RBM.Green.MinorDiffCondInst.inst_gain_applied_pos  1395-1412
### RBM3D.Green.MinorGoodLe  (41 unreached of 103)
private RBM.Green.flucIterHigh_slice_apply  96-98
private RBM.Green.flucIterHigh_seqHflow_apply  100-104
RBM.Green.minorDiff_nil  360-362
private RBM.Green.MinorGoodLeInst.szH  1054-1060
private RBM.Green.MinorGoodLeInst.siteA  1062-1063
private RBM.Green.MinorGoodLeInst.siteB  1064-1064
private RBM.Green.MinorGoodLeInst.siteC  1065-1065
private RBM.Green.MinorGoodLeInst.siteD  1066-1066
private RBM.Green.MinorGoodLeInst.siteB_ne_siteA  1068-1068
private RBM.Green.MinorGoodLeInst.siteC_ne_siteA  1069-1069
private RBM.Green.MinorGoodLeInst.siteB_ne_siteC  1070-1070
private RBM.Green.MinorGoodLeInst.siteD_ne_siteA  1071-1071
private RBM.Green.MinorGoodLeInst.hE0  1073-1073
private RBM.Green.MinorGoodLeInst.eta_zero  1075-1078
private RBM.Green.MinorGoodLeInst.integral_prod_le  1080-1097
private RBM.Green.MinorGoodLeInst.minorDiffGainUpTo'_of_crude  1099-1120
private RBM.Green.MinorGoodLeInst.minorDiffGain_szH  1122-1129
private RBM.Green.MinorGoodLeInst.slotK  1138-1139
private RBM.Green.MinorGoodLeInst.slotWord  1141-1144
RBM.Green.MinorGoodLeInst.inst_flucGain_word  1146-1162
private RBM.Green.MinorGoodLeInst.word3  1164-1166
RBM.Green.MinorGoodLeInst.inst_annihilation  1168-1180
RBM.Green.MinorGoodLeInst.inst_qList  1182-1184
RBM.Green.MinorGoodLeInst.inst_finDepOffRows  1186-1191
private RBM.Green.MinorGoodLeInst.seqHflow_zero_omega  1195-1202
private RBM.Green.MinorGoodLeInst.sqrt_four  1204-1205
private RBM.Green.MinorGoodLeInst.mE_zero  1207-1209
private RBM.Green.MinorGoodLeInst.zt_sixteenth  1211-1215
private RBM.Green.MinorGoodLeInst.green_zero  1217-1222
private RBM.Green.MinorGoodLeInst.inv_neg_zt  1224-1229
private RBM.Green.MinorGoodLeInst.zt_ne_zero  1231-1233
private RBM.Green.MinorGoodLeInst.norm_diag_sub  1235-1240
private RBM.Green.MinorGoodLeInst.goodEvent_omega_zero  1242-1254
private RBM.Green.MinorGoodLeInst.zt_im_ne  1256-1259
RBM.Green.MinorGoodLeInst.inst_minorGoodLe_flow  1261-1267
RBM.Green.MinorGoodLeInst.inst_minorGoodLe_general  1269-1275
RBM.Green.MinorGoodLeInst.inst_isUnit_det  1277-1285
RBM.Green.MinorGoodLeInst.inst_norm_gEnt  1287-1297
RBM.Green.MinorGoodLeInst.inst_gEnt_insert  1299-1307
RBM.Green.MinorGoodLeInst.inst_level_one  1309-1313
RBM.Green.MinorGoodLeInst.inst_gEnt_empty  1315-1320
### RBM3D.Green.Pins  (43 unreached of 115)
RBM.Green.GavLRandSeq  184-189
RBM.Green.GavLGEXRandHyp  227-232
RBM.Green.asGMcPT_iff_forall_prec  764-785
RBM.Green.giiOmegaSeq_of_stGiiGEX  830-844
RBM.Green.prec_maxLoop2_of_loopDetSeq  1010-1041
RBM.Green.perTimeDomAt_of_nonpos  1161-1175
private RBM.Green.gres_zero_true  1179-1194
RBM.Green.greenBlk_time_zero  1196-1200
RBM.Green.gexRHS_swap_eq  1213-1226
RBM.Green.offSq_time_zero  1228-1234
RBM.Green.diagSq_time_zero  1236-1240
RBM.Green.llErrMat_time_zero  1242-1248
RBM.Green.avgErr_time_zero  1250-1254
RBM.Green.diag_entry_sq_time_zero  1256-1261
private RBM.Green.zdistInf_zero  1303-1305
private RBM.Green.norm_loopPM_le_gexRHS  1307-1331
RBM.Green.offSq_le_gexRHS_swap_W1  1333-1363
private RBM.Green.seqHflow_zero'  1371-1372
RBM.Green.conclusions_time_zero  1374-1398
RBM.Green.asGMcSeq_time_zero  1400-1405
RBM.Green.Instance.premises  1423-1433
RBM.Green.Instance.rangeCond_sInst  1435-1437
RBM.Green.Instance.inst_gijGEXPTSwap  1439-1448
RBM.Green.Instance.inst_perTime_timeIcc  1450-1467
RBM.Green.Instance.inst_perSeq  1469-1479
RBM.Green.Instance.inst_asGMcSeq_iff  1481-1487
RBM.Green.Instance.inst_stGijGEX  1489-1492
RBM.Green.Instance.inst_giiOmegaSeq  1494-1497
RBM.Green.Instance.inst_stGiiGEX  1499-1505
RBM.Green.Instance.inst_gavLDetSeq_iff  1507-1514
RBM.Green.Instance.inst_loopDetSeq  1516-1523
RBM.Green.Instance.inst_hyp  1525-1528
RBM.Green.Instance.inst_stGavLGEX  1530-1536
RBM.Green.Instance.inst_stGbEXP_of_v3  1538-1543
RBM.Green.Instance.inst_conclusions_time_zero  1545-1551
RBM.Green.Instance.inst_norm_loopPM_eq  1553-1560
RBM.Green.Instance.inst_time_zero_checks  1562-1572
RBM.Green.Instance.inst_gexRHS_checks  1574-1584
RBM.Green.Instance.inst_offSq_W1  1586-1592
RBM.Green.Instance.inst_perTimeDomAt_of_nonpos  1594-1599
RBM.Green.Instance.inst_bridges_time_zero  1601-1621
RBM.Green.Instance.inst_asGMcPT_iff  1623-1630
RBM.Green.Instance.inst_prec_maxLoop2  1632-1639
### RBM3D.Green.RowIndep  (25 unreached of 110)
private RBM.Green.slice_apply  296-298
RBM.Green.minorCol  885-895
RBM.Green.minorCol_congr  897-904
RBM.Green.measurable_minorCol  906-918
RBM.Green.minorCol_eq_greenMinor  926-936
RBM.Green.ldeRowLHS_eq  938-951
RBM.Green.rowVarSum_eq  953-967
RBM.Green.stochDom_rowSum_general  1239-1254
RBM.Green.minorRowConj  1258-1269
RBM.Green.minorRowConj_congr  1271-1277
RBM.Green.measurable_minorRowConj  1279-1291
RBM.Green.RowIndep_minorColD_zero  1497-1502
RBM.Green.RowIndep_minorRowConjD_zero  1504-1509
RBM.Green.highProb_norm_rowSum_sq_le  1596-1687
private RBM.Green.RowIndepInst.sz0_size_tendsto  1706-1708
RBM.Green.RowIndepInst.LdeIdx_nonempty_sz0  1710-1717
RBM.Green.RowIndepInst.highProb_norm_rowSum_sq_le_sz0  1719-1730
RBM.Green.RowIndepInst.stochDom_rowSum_general_sz0  1732-1742
RBM.Green.RowIndepInst.stochDom_rowSum_generalTime_sz0  1744-1755
private RBM.Green.RowIndepInst.shiftD  1757-1760
RBM.Green.RowIndepInst.RowIndep_stochDom_rowSum_generalTime_shift_sz0  1762-1774
private RBM.Green.RowIndepInst.sum_svarF_row  1789-1805
RBM.Green.RowIndepInst.integral_norm_row_sum_pow_le_sz0  1807-1829
private RBM.Green.RowIndepInst.exists_agreeOffRow_ne  1831-1855
RBM.Green.RowIndepInst.exists_agreeOffRow_ne_sz0  1857-1864
### RBM3D.Green.Stability  (2 unreached of 18)
RBM.Green.stable_svar  171-178
RBM.Green.eventually_stable_svar_bulk  379-391
### RBM3D.Hierarchy.ContractionBasic  (6 unreached of 45)
private RBM.Gauss.contraction_coordinateMatrix_apply  115-117
RBM.Gauss.weighted_trace_coordinate_offDiag_blocks  284-302
RBM.Gauss.blockRelabel_eq_blockMat  463-464
private RBM.Gauss.contraction_loopL_eq  764-766
private RBM.Gauss.contraction_gloopProd_cons  768-771
private RBM.Gauss.ContractionInst.lab  886-887
### RBM3D.Hierarchy.ContractionSecondLoop  (21 unreached of 71)
RBM.Gauss.trace_gsigCoordinateSecondDeriv_Eblk  252-274
RBM.Gauss.sum_gsigCoordinateSecondDeriv_Eblk  276-306
private RBM.Gauss.secondLoop_gloopProd_nil  404-404
RBM.Gauss.edgeSplits_unique_position  535-549
RBM.Gauss.pairSplits_positions_valid  596-608
private RBM.Gauss.edgeSplits_injective_position  610-616
private RBM.Gauss.pairSplits_injective_positions  618-628
RBM.Gauss.pairSplits_unique_positions  630-654
RBM.Gauss.edgeSplit_segment_products  948-961
RBM.Gauss.pairSplit_segment_products  963-982
RBM.Gauss.sum_coordinateSameEdgeTerm_cutLoops_of_mem  1023-1044
RBM.Gauss.sum_coordinatePairTerm_cutLoops_of_mem  1091-1117
RBM.Gauss.segmentLoopIdx_zip_eq  1194-1203
RBM.Gauss.sum_gloopSecondWordDeriv_allCuts  1205-1222
private RBM.Gauss.SecondLoopInst.lab  1238-1239
private RBM.Gauss.SecondLoopInst.γ0  1241-1242
private RBM.Gauss.SecondLoopInst.word3  1244-1245
private RBM.Gauss.SecondLoopInst.e1  1247-1248
private RBM.Gauss.SecondLoopInst.e1_mem  1250-1251
private RBM.Gauss.SecondLoopInst.p13  1253-1255
private RBM.Gauss.SecondLoopInst.p13_mem  1257-1258
### RBM3D.Induction.AzumaProxyN  (70 unreached of 91)
RBM.Ind.testFun_const_smul  90-96
private RBM.Ind.azumaProxy_testFun_sum  98-106
RBM.Ind.testFun_linComb  108-112
private RBM.Ind.azumaProxy_norm_adjacentBlockWeight_le  412-432
private RBM.Ind.azumaProxy_norm_prod_le_one  434-443
private RBM.Ind.azumaProxy_norm_loopL_zero_le  457-473
private RBM.Ind.azumaProxy_loopL_zero_of_ne  475-487
private RBM.Ind.azumaProxy_STLKIM_zero  538-545
private RBM.Ind.azumaProxy_STavgErrM_zero  547-556
private RBM.Ind.azumaProxy_STksimLKM_zero  558-574
private RBM.Ind.azumaProxy_STelklkM_zero  576-587
private RBM.Ind.azumaProxy_STegtM_zero  589-594
private RBM.Ind.azumaProxy_STXiLKM_zero  608-620
private RBM.Ind.azumaProxy_zdistInf_zero  622-625
private RBM.Ind.azumaProxy_exists_ne  627-638
private RBM.Ind.azumaProxy_far_exists_ne  640-648
private RBM.Ind.azumaProxy_mem_eeLoop  650-659
private RBM.Ind.azumaProxy_norm_SB_self  661-666
private RBM.Ind.azumaProxy_STeeM_zero_of_far  668-684
private RBM.Ind.azumaProxy_norm_STeeM_zero_le  686-775
private RBM.Ind.azumaProxy_Bctl_nonneg  777-780
RBM.Ind.zero_mem_goodSetN  782-879
RBM.Ind.azumaProxy_hee_of_levels  881-920
RBM.Ind.zero_mem_goodSetN_of_levels  922-929
RBM.Ind.azumaProxy_pathH_zero_of_s_zero  968-972
RBM.Ind.azumaProxy_subG_goodExit  1005-1022
RBM.Ind.azumaProxy_pos_gridExitTauN  1024-1039
private RBM.Ind.azumaProxy_blockMat_scalar  1052-1056
private RBM.Ind.azumaProxy_Gres_scalar_true  1058-1063
private RBM.Ind.azumaProxy_Gres_scalar_false  1065-1070
RBM.Ind.azumaProxy_loop3_scalar  1072-1091
RBM.Ind.azumaProxy_xmu  1093-1095
RBM.Ind.azumaProxy_xmu_Xmat  1097-1105
RBM.Ind.AzumaProxyNInst.Einst  1124-1125
RBM.Ind.AzumaProxyNInst.sig3  1127-1128
RBM.Ind.AzumaProxyNInst.Einst_abs_lt  1130-1130
RBM.Ind.AzumaProxyNInst.sInst_nonneg  1132-1132
RBM.Ind.AzumaProxyNInst.sInst_le_vg  1134-1134
RBM.Ind.AzumaProxyNInst.vg_lt_one  1136-1136
RBM.Ind.AzumaProxyNInst.phi3  1138-1141
RBM.Ind.AzumaProxyNInst.kap3  1143-1146
RBM.Ind.AzumaProxyNInst.qProxy3  1148-1153
RBM.Ind.AzumaProxyNInst.phi3_hermTestFun  1155-1160
RBM.Ind.AzumaProxyNInst.azumaSubGN_instance  1162-1178
RBM.Ind.AzumaProxyNInst.Γ4  1180-1181
RBM.Ind.AzumaProxyNInst.Λ3  1182-1182
RBM.Ind.AzumaProxyNInst.Φ1  1183-1183
RBM.Ind.AzumaProxyNInst.zero_mem_goodSetN_instance  1185-1196
RBM.Ind.AzumaProxyNInst.zero_mem_goodSetN_of_levels_instance  1198-1207
RBM.Ind.AzumaProxyNInst.zero_mem_goodSetN_instance_grid  1209-1214
RBM.Ind.AzumaProxyNInst.azumaSubGN_goodExit_zero_instance  1216-1234
RBM.Ind.AzumaProxyNInst.goodExitTauN_pos_instance  1236-1244
RBM.Ind.AzumaProxyNInst.azumaSubGN_goodExit_instance  1246-1260
RBM.Ind.AzumaProxyNInst.testFun_linComb_instance  1262-1266
RBM.Ind.AzumaProxyNInst.testFun_const_smul_instance  1268-1271
RBM.Ind.AzumaProxyNInst.b0  1282-1283
RBM.Ind.AzumaProxyNInst.z1  1285-1286
RBM.Ind.AzumaProxyNInst.z1_im_pos  1288-1292
RBM.Ind.AzumaProxyNInst.z1_ne_zero  1294-1297
RBM.Ind.AzumaProxyNInst.z1_sub_ne  1299-1304
RBM.Ind.AzumaProxyNInst.z1_sub_conj_ne  1306-1311
RBM.Ind.AzumaProxyNInst.fsc  1313-1315
RBM.Ind.AzumaProxyNInst.phi3_scalar  1317-1325
RBM.Ind.AzumaProxyNInst.fsc_hasDerivAt  1327-1351
RBM.Ind.AzumaProxyNInst.fsc_deriv_ne  1353-1364
RBM.Ind.AzumaProxyNInst.fderiv_one_ne  1366-1382
RBM.Ind.AzumaProxyNInst.exists_coord_deriv_ne  1384-1420
RBM.Ind.AzumaProxyNInst.kap3_one_sum  1422-1430
RBM.Ind.AzumaProxyNInst.sum_pos_aux  1432-1437
RBM.Ind.AzumaProxyNInst.qProxy3_pos  1439-1456
### RBM3D.Induction.AzumaProxyN2  (50 unreached of 92)
RBM.Ind.yMomentsN_of_unif  978-984
RBM.Ind.yMomentsN  986-993
RBM.Ind.AzumaProxyN_c0_pos_pub  1229-1233
RBM.Ind.AzumaProxyN_etaT_inv_le_pub  1241-1246
RBM.Ind.AzumaProxyN_rowsum_Ugen_pub  1256-1264
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_rangeCond_vg  1285-1296
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Kg_ne_zero  1298-1298
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_gridStep_pos  1300-1302
RBM.Ind.AzumaProxyN2Inst.normPow8_instance  1304-1310
RBM.Ind.AzumaProxyN2Inst.yMomentsUnifN_instance  1312-1324
RBM.Ind.AzumaProxyN2Inst.yMomentsN_of_unif_instance  1326-1339
RBM.Ind.AzumaProxyN2Inst.yMomentsN_instance  1341-1367
RBM.Ind.AzumaProxyN2Inst.yfieldsW_instance  1369-1405
private RBM.Ind.azumaProxy2_hasDerivAt_dir  1470-1483
private RBM.Ind.azumaProxy2_dirDerivN_eq  1485-1489
private RBM.Ind.azumaProxy2_gvarF_diag_pos  1491-1500
private RBM.Ind.azumaProxy2_PF_ball_pos  1502-1528
private RBM.Ind.azumaProxy2_eq_of_ae_eq_of_ball_pos  1530-1541
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_gridTime_one  1551-1552
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_phiN  1554-1557
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_phiN_hermTestFun  1559-1563
RBM.Ind.AzumaProxyN2Inst.b0n  1565-1566
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_z1n  1568-1569
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_z1n_im_pos  1571-1575
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_z1n_ne_zero  1577-1580
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_z1n_sub_ne  1582-1587
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_z1n_sub_conj_ne  1589-1594
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_fscn  1596-1599
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_phiN_scalar  1601-1610
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Φ0n  1612-1614
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Φ0n_scalar  1616-1618
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Φ0n_measurable  1620-1622
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Tfun  1624-1628
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Kc0  1630-1632
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_psi0  1634-1635
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_psi0_measurable  1637-1643
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_pathH_one  1645-1649
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_avecN_one  1651-1656
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_condExp_avecN_one  1658-1671
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_yvecN_ae_eq  1673-1695
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Φ0n_differentiableAt  1697-1699
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Tfun_eq  1701-1706
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Tfun_measurable  1708-1722
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Tfun_continuousAt  1724-1752
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_fscn_zero_ne  1754-1758
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_inv_sub_tendsto  1760-1771
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_fscn_tendsto  1773-1778
private RBM.Ind.AzumaProxyN2Inst.azumaProxy2_Tfun_xmu  1780-1795
RBM.Ind.AzumaProxyN2Inst.yvecN_not_ae_zero  1797-1853
RBM.Ind.AzumaProxyN2Inst.yMomentsUnifN_instance_nonzero  1855-1868
### RBM3D.Induction.B45  (43 unreached of 83)
RBM.Gauss.Sizes.B45_STKloop_eq  195-196
RBM.Gauss.Sizes.B45_Psum_LK_le  411-447
private RBM.Gauss.Sizes.B45_zdistInf_add_le  904-912
private RBM.Gauss.Sizes.B45_zdistInf_neg  914-916
private RBM.Gauss.Sizes.B45_zdistInf_zero  919-921
private RBM.Gauss.Sizes.B45_zdistInf_comm  923-925
private RBM.Gauss.Sizes.B45_zdistInf_tri  927-930
private RBM.Gauss.Sizes.B45_two_mul_zdistInf_le  932-939
private RBM.Gauss.Sizes.B45_two_mul_diam_le  941-949
private RBM.Gauss.Sizes.B45_diam_le_KLmaxDist  951-957
private RBM.Gauss.Sizes.B45_diam_one  959-965
private RBM.Gauss.Sizes.B45_adjacent  967-1021
private RBM.Gauss.Sizes.B45_loopL_eq_prod  1029-1041
private RBM.Gauss.Sizes.B45_loopL_rotate  1043-1052
private RBM.Gauss.Sizes.B45_loopL_rotate_iter  1054-1074
private RBM.Gauss.Sizes.B45_cut  1078-1147
private RBM.Gauss.Sizes.B45_loopL_two_sign  1149-1158
private RBM.Gauss.Sizes.B45_pair  1160-1196
private RBM.Gauss.Sizes.B45_one_sub_u  1217-1255
private RBM.Gauss.Sizes.B45_STWB_le  1257-1296
private RBM.Gauss.Sizes.B45_STWB_nonneg  1298-1302
private RBM.Gauss.Sizes.B45_alg  1304-1405
private RBM.Gauss.Sizes.B45_exp_small  1407-1438
private RBM.Gauss.Sizes.B45_real_geom  1440-1466
private RBM.Gauss.Sizes.B45_zdistD_le_KLmaxDist_two  1468-1473
RBM.Gauss.Sizes.B45_far_main  1487-1746
RBM.Gauss.Sizes.B45_far  1760-1791
private RBM.Gauss.Sizes.B45_ellT_eq_one  1983-1988
RBM.Gauss.Sizes.B45_vth_sup  2110-2230
RBM.Gauss.Sizes.B45_det  2341-2438
RBM.Gauss.Sizes.B45_prec_assemble  2452-2490
RBM.Gauss.Sizes.B45_norm_le_XiLK  2504-2524
RBM.Gauss.Sizes.B45_alt_last  2526-2532
RBM.Gauss.Sizes.B45_W_pow_neg_le  2534-2544
RBM.Gauss.Sizes.B45_window_pow_le  2546-2560
RBM.Gauss.Sizes.B45_det2  2574-2635
RBM.Gauss.Sizes.B45_log_le  2647-2662
RBM.Gauss.Sizes.B45_farXi  2676-2682
RBM.Gauss.Sizes.B45_key  2686-2865
RBM.Gauss.Sizes.B45_pins  2868-2924
RBM.Gauss.Sizes.stWardTypePPin_holds  2934-2940
RBM.Gauss.Sizes.stB45Pin_holds  2942-2948
RBM.Gauss.B45Inst.B45_sz0_lam_pos  2967-2969
### RBM3D.Induction.ConArg  (2 unreached of 24)
RBM.Gauss.Sizes.stConArg_holds  799-818
private RBM.Ind.ConArgInst.bulk_z0  836-839
### RBM3D.Induction.ConArgDet  (20 unreached of 85)
RBM.Ind.zSig_true  363-363
RBM.Ind.zSig_false  365-365
RBM.Ind.list_prod_add_eq  447-480
RBM.Ind.gloop_symm_eq_trace  589-602
RBM.Ind.transpose_blockSel_mul  1103-1106
private RBM.Ind.cad_Hd  1364-1365
private RBM.Ind.cad_Hd_herm  1367-1369
private RBM.Ind.cad_mE_zero  1371-1375
private RBM.Ind.cad_im_z  1377-1380
private RBM.Ind.cad_im_w'  1382-1389
private RBM.Ind.cad_im_w  1391-1393
private RBM.Ind.cad_z_pos  1395-1396
private RBM.Ind.cad_conj_im_ne  1398-1399
private RBM.Ind.cad_green_zero  1535-1540
private RBM.Ind.cad_green_zero_I  1542-1546
private RBM.Ind.cad_green_zero_conj_I  1548-1552
private RBM.Ind.cad_loop_one_true  1554-1559
private RBM.Ind.cad_loop_one_false  1561-1566
private RBM.Ind.cad_ward_div_value  1568-1588
private RBM.Ind.cad_check_ward_row  1590-1607
### RBM3D.Induction.Continuity  (2 unreached of 21)
private RBM.Ind.perTime_of_sections  743-759
RBM.Gauss.Sizes.stNetLift_holds  769-787
### RBM3D.Induction.ContinuityNet  (8 unreached of 48)
RBM.Ind.ContinuityNet.cont_im_m_le_one  610-614
RBM.Ind.ContinuityNet.cont_spectralM_im_nonneg  632-634
private RBM.Ind.ContinuityNet.contInst_hsize  824-824
private RBM.Ind.ContinuityNet.contInst_one_le  826-827
private RBM.Ind.ContinuityNet.contInstω  829-830
private RBM.Ind.ContinuityNet.contInstω_good  832-833
private RBM.Ind.ContinuityNet.contInst_eta_pos  922-922
private RBM.Ind.ContinuityNet.contInst_herm  924-925
### RBM3D.Induction.ContractPt  (8 unreached of 43)
private RBM.Gauss.Sizes.ptH  579-580
private RBM.Gauss.Sizes.ptH_herm  582-585
private RBM.Gauss.Sizes.ptZ  587-587
private RBM.Gauss.Sizes.ptZ_im  589-591
private RBM.Gauss.Sizes.ptB  593-593
private RBM.Gauss.Sizes.ptM  595-596
private RBM.Gauss.Sizes.ptM_nonneg  598-599
private RBM.Gauss.Sizes.ptM_bound  601-605
### RBM3D.Induction.DecayLoopA  (30 unreached of 31)
RBM.Gauss.Sizes.STDecayLoopAt  76-102
RBM.Gauss.Sizes.STDecayLoopPT  104-114
private RBM.Gauss.Sizes.DecayLoopA_zdistInf_add_le  130-138
private RBM.Gauss.Sizes.DecayLoopA_zdistInf_neg  140-142
private RBM.Gauss.Sizes.DecayLoopA_zdistInf_zero  145-147
private RBM.Gauss.Sizes.DecayLoopA_zdistInf_comm  149-151
private RBM.Gauss.Sizes.DecayLoopA_zdistInf_tri  153-156
private RBM.Gauss.Sizes.DecayLoopA_two_mul_zdistInf_le  158-165
private RBM.Gauss.Sizes.DecayLoopA_two_mul_diam_le  167-175
RBM.Gauss.Sizes.DecayLoopA_diam_le_KLmaxDist  177-183
private RBM.Gauss.Sizes.DecayLoopA_diam_one  185-191
private RBM.Gauss.Sizes.DecayLoopA_adjacent  193-247
private RBM.Gauss.Sizes.DecayLoopA_loopL_eq_prod  255-267
private RBM.Gauss.Sizes.DecayLoopA_loopL_rotate  269-278
private RBM.Gauss.Sizes.DecayLoopA_loopL_rotate_iter  280-300
private RBM.Gauss.Sizes.DecayLoopA_cut  304-373
private RBM.Gauss.Sizes.DecayLoopA_loopL_two_sign  375-384
private RBM.Gauss.Sizes.DecayLoopA_pair  386-422
private RBM.Gauss.Sizes.DecayLoopA_mE_im_ge  430-441
private RBM.Gauss.Sizes.DecayLoopA_one_sub_u  443-481
private RBM.Gauss.Sizes.DecayLoopA_STWB_le  483-522
private RBM.Gauss.Sizes.DecayLoopA_STWB_nonneg  524-528
private RBM.Gauss.Sizes.DecayLoopA_alg  530-631
private RBM.Gauss.Sizes.DecayLoopA_exp_small  633-664
private RBM.Gauss.Sizes.DecayLoopA_real_geom  666-692
private RBM.Gauss.Sizes.DecayLoopA_zdistD_le_KLmaxDist_two  694-699
private RBM.Gauss.Sizes.DecayLoopA_main  709-922
RBM.Gauss.Sizes.stDecayLoopAt_holds  932-960
RBM.Gauss.Sizes.stDecayLoopPT_of_step2  962-1082
RBM.Gauss.DecayLoopAInst.sz0_far_nonempty  1103-1168
### RBM3D.Induction.DecayLoopB  (27 unreached of 107)
RBM.Ind.LoopDecay.sub  66-70
RBM.Ind.mem_cutGlue  86-87
RBM.Ind.exists_anchor_cutGlueL  95-102
RBM.Ind.exists_anchor_cutGlueR  104-111
private RBM.Ind.DecayLoopB_zdistInf_tri  167-170
RBM.Ind.norm_sum_SB_le_left  299-343
RBM.Ind.norm_sum_SB_le_right  345-357
RBM.Ind.glueTerm  367-371
RBM.Ind.norm_glueTerm_le_of_far  434-449
private RBM.Gauss.DecayLoopBInst.DecayLoopB_I3  2254-2255
private RBM.Gauss.DecayLoopBInst.DecayLoopB_I3_WF  2257-2257
private RBM.Gauss.DecayLoopBInst.DecayLoopB_I3_length  2258-2258
private RBM.Gauss.DecayLoopBInst.DecayLoopB_I3_mem0  2259-2259
private RBM.Gauss.DecayLoopBInst.DecayLoopB_I3_mem1  2260-2260
private RBM.Gauss.DecayLoopBInst.DecayLoopB_I3_far  2261-2263
private RBM.Gauss.DecayLoopBInst.DecayLoopB_F3  2266-2267
private RBM.Gauss.DecayLoopBInst.DecayLoopB_F3_decay  2269-2278
private RBM.Gauss.DecayLoopBInst.DecayLoopB_F3_bound  2280-2281
private RBM.Gauss.DecayLoopBInst.DecayLoopB_eeσ  2299-2299
private RBM.Gauss.DecayLoopBInst.DecayLoopB_eea  2300-2300
private RBM.Gauss.DecayLoopBInst.DecayLoopB_eea'  2301-2301
private RBM.Gauss.DecayLoopBInst.sz0_zdistInf  2317-2329
private RBM.Gauss.DecayLoopBInst.sz0_ell_zero  2331-2344
private RBM.Gauss.DecayLoopBInst.sz0_W_rpow  2346-2356
RBM.Gauss.DecayLoopBInst.DecayLoopB_sz0_far_nonempty_U  2358-2386
private RBM.Gauss.DecayLoopBInst.inst_hE  2389-2394
RBM.Gauss.DecayLoopBInst.DecayLoopB_sz0_far_nonempty_EK  2457-2481
### RBM3D.Induction.Defs  (41 unreached of 72)
RBM.Gauss.Sizes.STForbidden  260-267
RBM.Gauss.Sizes.STConArg  331-344
RBM.Gauss.Sizes.STBootstrap  359-370
RBM.Gauss.Sizes.STNetLift  372-386
RBM.Gauss.InductionDefsInst.one_le_size_sz0  407-410
RBM.Gauss.InductionDefsInst.z0  412-413
RBM.Gauss.InductionDefsInst.z0_locDomain  415-421
RBM.Gauss.InductionDefsInst.z0_im_pos  423-424
RBM.Gauss.InductionDefsInst.z0_im_le_one  426-426
RBM.Gauss.InductionDefsInst.sixteenth_le_lemT  428-431
RBM.Gauss.InductionDefsInst.zero_le_lemT  433-433
RBM.Gauss.InductionDefsInst.flow_z0  435-436
RBM.Gauss.InductionDefsInst.sInst  438-439
RBM.Gauss.InductionDefsInst.tInst  440-440
RBM.Gauss.InductionDefsInst.W_ge_32  442-447
RBM.Gauss.InductionDefsInst.Bctl_const_le_gen  449-470
RBM.Gauss.InductionDefsInst.Bctl_const_le  472-473
RBM.Gauss.InductionDefsInst.Bctl_tInst_tendsto_gen  475-490
RBM.Gauss.InductionDefsInst.conStInd_gen  492-503
RBM.Gauss.InductionDefsInst.W_tendsto_sz0  505-511
RBM.Gauss.InductionDefsInst.Bctl_tInst_tendsto  513-514
RBM.Gauss.InductionDefsInst.conStInd_inst  516-517
RBM.Gauss.InductionDefsInst.inst_mainInd  519-534
RBM.Gauss.InductionDefsInst.inst_gbEXP  536-548
RBM.Gauss.InductionDefsInst.inst_gbEXP_av  550-567
RBM.Gauss.InductionDefsInst.inst_conArg  569-581
RBM.Gauss.InductionDefsInst.inst_step1  583-592
RBM.Gauss.InductionDefsInst.inst_bootstrap  594-604
RBM.Gauss.InductionDefsInst.inst_netLift  606-616
RBM.Gauss.InductionDefsInst.tEnd  625-626
RBM.Gauss.InductionDefsInst.tEnd_lt_one  628-628
RBM.Gauss.InductionDefsInst.inst_gbEXP_endT  630-639
RBM.Gauss.InductionDefsInst.inst_conArg_endT  641-653
RBM.Gauss.InductionDefsInst.sz1  662-663
RBM.Gauss.InductionDefsInst.sz1_admissible  665-675
RBM.Gauss.InductionDefsInst.flow_z1  677-678
RBM.Gauss.InductionDefsInst.W_tendsto_sz1  680-680
RBM.Gauss.InductionDefsInst.inst_mainInd_lowg  682-696
RBM.Gauss.InductionDefsInst.inst_gbEXP_lowg  698-710
RBM.Gauss.InductionDefsInst.inst_conArg_lowg  712-723
RBM.Gauss.InductionDefsInst.inst_step1_lowg  725-733
### RBM3D.Induction.DuhamelI2  (2 unreached of 45)
RBM.Gauss.Sizes.stDuhamelConcl_engine  1554-1588
RBM.Gauss.Step5Inst.inst_duhamelI_proved  1607-1611
### RBM3D.Induction.DuhamelII  (2 unreached of 18)
RBM.Gauss.Sizes.stDuhamelConcl_engineQ1  871-905
RBM.Gauss.Step5Inst.inst_duhamelII_proved  922-927
### RBM3D.Induction.EMn2Exp1  (25 unreached of 86)
RBM.Gauss.Sizes.emn2Exp_near  1433-1453
RBM.Gauss.Sizes.emn2ExpS1M  1468-1473
RBM.Gauss.Sizes.emn2ExpS2M  1475-1479
RBM.Gauss.Sizes.emn2ExpS3M  1481-1485
private RBM.Gauss.Sizes.emn2Exp_STEEkM_zero_eq  1502-1509
private RBM.Gauss.Sizes.emn2Exp_STEEkM_one_eq  1511-1515
RBM.Gauss.Sizes.emn2Exp_EEk_cover  1517-1533
RBM.Gauss.Sizes.emn2Exp_far12  1720-1741
RBM.Gauss.Sizes.emn2ExpEllStar_eq  1751-1755
RBM.Gauss.Sizes.emn2Exp_trunc_cmp  1772-1805
RBM.Gauss.Sizes.emn2Exp_EEk_split  1807-1825
RBM.Gauss.Sizes.emn2Exp_of_far3  1903-1965
private RBM.Gauss.EMn2Exp1Inst.exH  1996-1998
private RBM.Gauss.EMn2Exp1Inst.exH_herm  2000-2003
private RBM.Gauss.EMn2Exp1Inst.exZ  2005-2005
private RBM.Gauss.EMn2Exp1Inst.exZ_im  2007-2009
private RBM.Gauss.EMn2Exp1Inst.exB  2011-2011
private RBM.Gauss.EMn2Exp1Inst.szA  2059-2066
private RBM.Gauss.EMn2Exp1Inst.szA_logW  2068-2073
private RBM.Gauss.EMn2Exp1Inst.szA_Lg4  2075-2082
private RBM.Gauss.EMn2Exp1Inst.sz0_logW  2103-2114
private RBM.Gauss.EMn2Exp1Inst.sz0_Bdata  2138-2145
private RBM.Gauss.EMn2Exp1Inst.ℓ_range_inst  2180-2185
private RBM.Gauss.EMn2Exp1Inst.sz0_rangeCond  2251-2256
private RBM.Gauss.EMn2Exp1Inst.sz0_lam_ev  2258-2262
### RBM3D.Induction.EMn2Exp2  (17 unreached of 45)
private RBM.Gauss.Sizes.emn2Exp2_STLKM_le  741-750
RBM.Gauss.Sizes.emn2Exp2_loop2_far_le  752-794
RBM.Gauss.Sizes.emn2Exp_far3  1179-1205
private RBM.Gauss.EMn2Exp2Inst.exH  1302-1304
private RBM.Gauss.EMn2Exp2Inst.exH_herm  1306-1309
private RBM.Gauss.EMn2Exp2Inst.exZ  1311-1311
private RBM.Gauss.EMn2Exp2Inst.exZ_im  1313-1315
private RBM.Gauss.EMn2Exp2Inst.exB  1317-1317
private RBM.Gauss.EMn2Exp2Inst.exC  1319-1319
private RBM.Gauss.EMn2Exp2Inst.exC'  1321-1321
private RBM.Gauss.EMn2Exp2Inst.exPf  1332-1334
private RBM.Gauss.EMn2Exp2Inst.exPf_ge  1336-1345
private RBM.Gauss.EMn2Exp2Inst.ex_two_loop  1347-1361
private RBM.Gauss.EMn2Exp2Inst.sz0_logW  1388-1399
private RBM.Gauss.EMn2Exp2Inst.ℓ_range_inst  1401-1406
private RBM.Gauss.EMn2Exp2Inst.baHf  1516-1517
private RBM.Gauss.EMn2Exp2Inst.baZf  1519-1520
### RBM3D.Induction.EMn2Poly  (5 unreached of 45)
private RBM.Gauss.EMn2PolyInst.emH  1038-1040
private RBM.Gauss.EMn2PolyInst.emH_herm  1042-1045
private RBM.Gauss.EMn2PolyInst.emZ  1047-1047
private RBM.Gauss.EMn2PolyInst.emZ_im  1049-1051
private RBM.Gauss.EMn2PolyInst.emB  1053-1053
### RBM3D.Induction.EtermsMid2  (10 unreached of 66)
private RBM.Gauss.Sizes.etermsMid_Kf_le_L  219-220
RBM.Gauss.Sizes.LemDecCalELip_ELKLKgL  1439-1460
RBM.Gauss.Sizes.LemDecCalELip_eegL  1480-1495
private RBM.Gauss.Sizes.etermsMid_inst_Cm  1508-1509
private RBM.Gauss.Sizes.etermsMid_inst_L  1511-1512
private RBM.Gauss.Sizes.etermsMid_inst_m  1514-1515
private RBM.Gauss.Sizes.etermsMid_inst_S  1517-1518
private RBM.Gauss.Sizes.etermsMid_inst_Q  1520-1523
private RBM.Gauss.Sizes.etermsMid_inst_Kn  1525-1528
private RBM.Gauss.Sizes.etermsMid_inst_Ks  1530-1536
### RBM3D.Induction.ExpAvg  (18 unreached of 55)
RBM.Gauss.Sizes.expAvg_u_zero  775-787
RBM.Gauss.Step6Inst.inst_expAvgAt_holds  893-898
RBM.Gauss.Step6Inst.inst_improveExpAver_holds  900-903
RBM.Gauss.Step6Inst.inst_expAvgU_holds  905-908
RBM.Gauss.Step6Inst.inst_skeleton6I_avg  910-915
RBM.Gauss.Step6Inst.inst_skeleton6II_avg  917-921
RBM.Gauss.Step6Inst.inst_skeleton6IV_avg  923-926
RBM.Gauss.Step6Inst.inst_eta_inv_le  928-931
RBM.Gauss.Step6Inst.inst_expAvg_u_zero  933-936
private RBM.Gauss.Step6Inst.instLoop  941-943
private RBM.Gauss.Step6Inst.inst_E_lt  945-946
RBM.Gauss.Step6Inst.inst_expAvg_stein  948-955
RBM.Gauss.Step6Inst.inst_expAvg_selfcons  957-964
RBM.Gauss.Step6Inst.inst_expAvg_norm_solve  966-983
RBM.Gauss.Step6Inst.inst_expAvg_expErr_le  985-997
RBM.Gauss.Step6Inst.inst_expAvg_Bctl_ge  999-1001
RBM.Gauss.Step6Inst.inst_expAvg_moment  1003-1010
RBM.Gauss.Step6Inst.inst_expAvg_integral_conj  1012-1017
### RBM3D.Induction.ExpDuhamel  (12 unreached of 39)
private RBM.Gauss.Sizes.expDuh_zeroModeCLM_apply  345-346
RBM.Gauss.Sizes.expDuh_plain  366-380
RBM.Gauss.Step6Inst.inst_duhamelZ_holds  598-608
RBM.Gauss.Step6Inst.inst_duhamelQ_holds  610-618
RBM.Gauss.Step6Inst.inst_duhEq_holds  620-622
RBM.Gauss.Step6Inst.inst_expDuh_plain  624-632
RBM.Gauss.Step6Inst.inst_expDuh_single  634-645
private RBM.Gauss.Step6Inst.expDuh_inst_hier  655-661
private RBM.Gauss.Step6Inst.expDuh_inst_Icc  663-664
private RBM.Gauss.Step6Inst.expDuh_inst_cont_err  666-668
private RBM.Gauss.Step6Inst.expDuh_inst_cont_drift  670-672
private RBM.Gauss.Step6Inst.expDuh_inst_mollifier  674-682
### RBM3D.Induction.ExpEtermsA  (11 unreached of 24)
RBM.Gauss.Step6Inst.inst_expLKLK_I_holds  622-625
RBM.Gauss.Step6Inst.inst_expLKLK_II_holds  627-630
RBM.Gauss.Step6Inst.inst_expLKLK_III_holds  632-635
RBM.Gauss.Step6Inst.inst_skeleton6III_LK  637-641
RBM.Gauss.Step6Inst.inst_expLK_latticeSum  643-650
RBM.Gauss.Step6Inst.inst_expLK_env  652-659
RBM.Gauss.Step6Inst.inst_expLK_window  661-671
RBM.Gauss.Step6Inst.inst_expLK_env_poly  673-677
RBM.Gauss.Step6Inst.inst_expLK_prec  679-687
RBM.Gauss.Step6Inst.inst_expLK_expect  689-696
RBM.Gauss.Step6Inst.inst_expLKLK_of_LKU  698-703
### RBM3D.Induction.ExpEtermsB  (14 unreached of 51)
RBM.Gauss.Step6Inst.inst_expDriftLo_holds  1069-1073
RBM.Gauss.Step6Inst.inst_expDriftDecay_holds  1075-1078
RBM.Gauss.Step6Inst.inst_skeleton6IV_Lo  1080-1084
RBM.Gauss.Step6Inst.inst_skeleton6I_Dec  1086-1093
RBM.Gauss.Step6Inst.inst_expDr_Bctl_le_IV  1095-1098
RBM.Gauss.Step6Inst.inst_expDr_envEGt  1100-1107
RBM.Gauss.Step6Inst.inst_expDr_EGt_split  1109-1115
RBM.Gauss.Step6Inst.inst_expDr_env_poly  1117-1125
RBM.Gauss.Step6Inst.inst_expDr_expect  1127-1139
RBM.Gauss.Step6Inst.inst_expDr_LK_prec  1141-1146
RBM.Gauss.Step6Inst.inst_expDr_EGtLK_prec  1148-1153
RBM.Gauss.Step6Inst.inst_expDr_EGtK_prec  1155-1161
RBM.Gauss.Step6Inst.inst_STExpDriftLoConcl_of_LKU  1163-1168
RBM.Gauss.Step6Inst.inst_STExpDriftDecayConcl_of_GdecayW  1170-1175
### RBM3D.Induction.ExpHier  (6 unreached of 51)
RBM.Gauss.Sizes.stExpHier_holds  768-773
RBM.Gauss.Step6Inst.inst_expHier_holds  789-796
RBM.Gauss.Step6Inst.inst_expHier_pp  798-806
RBM.Gauss.Step6Inst.inst_expHier_half  808-814
RBM.Gauss.Step6Inst.inst_expHier_Kloop  816-823
RBM.Gauss.Step6Inst.inst_expHier_hierarchy_two  825-839
### RBM3D.Induction.ExpIniI  (11 unreached of 36)
RBM.Gauss.Sizes.expIniI_props_shift  1011-1075
RBM.Gauss.Sizes.ST_step6_caseI_of_pins'  1119-1208
RBM.Gauss.Step6Inst.inst_expIniI'  1224-1227
RBM.Gauss.Step6Inst.inst_skeleton6I'  1229-1233
RBM.Gauss.Step6Inst.inst_expIniI_fastDecay  1235-1241
RBM.Gauss.Step6Inst.inst_expIniI_fastDecay_mono  1243-1259
RBM.Gauss.Step6Inst.inst_expIniI_same  1261-1271
RBM.Gauss.Step6Inst.inst_expIniI_Qop  1273-1289
RBM.Gauss.Step6Inst.inst_expIniI_mixed  1291-1305
RBM.Gauss.Step6Inst.inst_expIniI_props_shift  1307-1312
RBM.Gauss.Step6Inst.inst_expIniI_props_shift_ex  1314-1322
### RBM3D.Induction.ExpIntEasy  (9 unreached of 30)
RBM.Gauss.Step6Inst.inst_expIntIII_holds  638-642
RBM.Gauss.Step6Inst.inst_expIntIV_holds  644-648
RBM.Gauss.Step6Inst.inst_skeleton6III_Int  650-653
RBM.Gauss.Step6Inst.inst_skeleton6IV_Int  655-658
RBM.Gauss.Step6Inst.inst_expIntIII_concl  660-665
RBM.Gauss.Step6Inst.inst_expIntIV_concl  667-675
RBM.Gauss.Step6Inst.inst_expIntEasy_integral_rpow  677-680
RBM.Gauss.Step6Inst.inst_expIntIII_rates_le_target  682-688
RBM.Gauss.Step6Inst.inst_expIntIV_rate_le_target  690-693
### RBM3D.Induction.ExpIntI  (11 unreached of 27)
RBM.Gauss.Step6Inst.inst_skeleton6I''  678-682
RBM.Gauss.Step6Inst.inst_expIntI_same  684-697
RBM.Gauss.Step6Inst.inst_expIntI_log_ratio  699-704
RBM.Gauss.Step6Inst.inst_expIntI_ratio_le  706-710
private RBM.Gauss.Step6Inst.inst_expIntI_diag_decay  712-730
RBM.Gauss.Step6Inst.inst_expIntI_kernel_unif  732-755
private RBM.Gauss.Step6Inst.inst_expIntI_sumZero  757-783
private RBM.Gauss.Step6Inst.inst_expIntI_dipole_decay  786-832
RBM.Gauss.Step6Inst.inst_expIntI_kernel_unif_sumzero  835-868
RBM.Gauss.Step6Inst.inst_expIntI_tensors_ne_zero  870-879
RBM.Gauss.Step6Inst.inst_expIntI_concl_of_kernel  881-897
### RBM3D.Induction.ExpIntII  (9 unreached of 24)
RBM.Gauss.Step6Inst.inst_expIntII_holds  568-574
RBM.Gauss.Step6Inst.inst_skeleton6II_Int  576-581
RBM.Gauss.Step6Inst.inst_expIntII_concl  583-592
RBM.Gauss.Step6Inst.inst_expIntII_log_ratio  594-599
RBM.Gauss.Step6Inst.inst_expIntII_Bctl_le  601-604
RBM.Gauss.Step6Inst.inst_expIntII_rates_le_target  606-609
RBM.Gauss.Step6Inst.inst_expIntII_log_eventually  611-615
RBM.Gauss.Step6Inst.inst_expIntII_kernel_unif  617-630
RBM.Gauss.Step6Inst.inst_expIntII_drift_integral_le  632-649
### RBM3D.Induction.ExpIntIQ  (11 unreached of 47)
RBM.Gauss.Step6Inst.inst_expIntI'  1380-1385
RBM.Gauss.Step6Inst.inst_expIntIQ_star_props  1387-1391
RBM.Gauss.Step6Inst.inst_expIntI'_mixed  1393-1423
RBM.Gauss.Step6Inst.inst_stStep6I_of_LW  1425-1429
RBM.Gauss.Step6Inst.inst_expIntIQ_Qop_sub  1432-1441
RBM.Gauss.Step6Inst.inst_expIntIQ_diff_sumZero  1443-1455
RBM.Gauss.Step6Inst.inst_expIntIQ_src_sumZero  1457-1462
RBM.Gauss.Step6Inst.inst_expIntIQ_src_decay  1464-1474
RBM.Gauss.Step6Inst.inst_expIntIQ_ini  1476-1499
RBM.Gauss.Step6Inst.inst_expIntIQ_star_bound  1501-1520
RBM.Gauss.Step6Inst.inst_expIntIQ_back  1522-1541
### RBM3D.Induction.ExpWardI  (8 unreached of 29)
RBM.Gauss.Sizes.expWI_core'  432-437
RBM.Gauss.Step6Inst.inst_expWardI'  468-472
RBM.Gauss.Step6Inst.inst_expWardI_holds  474-479
RBM.Gauss.Step6Inst.inst_expWardI'_mixed  481-508
RBM.Gauss.Step6Inst.inst_expWI_Psum_eq  510-519
RBM.Gauss.Step6Inst.inst_expWI_Psum_prec  521-529
RBM.Gauss.Step6Inst.inst_expWI_window  531-534
RBM.Gauss.Step6Inst.inst_expWI_vth_le  536-548
### RBM3D.Induction.ExpWardII  (8 unreached of 29)
RBM.Gauss.Step6Inst.inst_expWardII_holds  437-442
RBM.Gauss.Step6Inst.inst_skeleton6II_Wd  444-449
RBM.Gauss.Step6Inst.inst_expWII_concl  451-457
RBM.Gauss.Step6Inst.inst_expWII_inv_Neta_le  459-463
RBM.Gauss.Step6Inst.inst_expWII_slot0  465-472
RBM.Gauss.Step6Inst.inst_expWII_slot1  474-481
RBM.Gauss.Step6Inst.inst_expWII_det_bound  483-502
RBM.Gauss.Step6Inst.inst_expWII_two_slot_bound  504-513
### RBM3D.Induction.GridAssemblyN  (42 unreached of 91)
RBM.Ind.YMomentsConclN  157-166
RBM.Ind.YMomentsN  168-176
private RBM.Ind.gridAsm_gridStep_nonneg  987-990
private RBM.Ind.gridAsm_gridTime_nonneg  992-995
private RBM.Ind.gridAsm_gridTime_le  997-1004
RBM.Ind.stoppedAzumaZN  1006-1017
RBM.Ind.GridAssemblyNInst.gridAsm_E  1655-1656
RBM.Ind.GridAssemblyNInst.gridAsm_E_abs_lt  1658-1661
RBM.Ind.GridAssemblyNInst.gridAsm_stoppedAzumaZN_instance  1665-1684
RBM.Ind.GridAssemblyNInst.gridAsm_stoppedAzumaZN_bound_lt_one  1686-1705
RBM.Ind.GridAssemblyNInst.gridAsm_stoppedAzumaZN_instance_concrete  1707-1734
RBM.Ind.GridAssemblyNInst.gridAsm_K  1738-1739
RBM.Ind.GridAssemblyNInst.gridAsm_size_pos  1741-1743
RBM.Ind.GridAssemblyNInst.gridAsm_K_pos  1745-1745
RBM.Ind.GridAssemblyNInst.gridAsm_K_ne  1747-1747
RBM.Ind.GridAssemblyNInst.gridAsm_sInst_le_tInst  1749-1749
RBM.Ind.GridAssemblyNInst.gridAsm_tInst_lt_one  1751-1751
RBM.Ind.GridAssemblyNInst.gridAsm_step  1753-1758
RBM.Ind.GridAssemblyNInst.gridAsm_step_pos  1760-1763
RBM.Ind.GridAssemblyNInst.gridAsm_grid_data  1765-1781
RBM.Ind.GridAssemblyNInst.gridAsm_gridTime_bounds  1783-1790
RBM.Ind.GridAssemblyNInst.gridAsm_witZ  1804-1809
RBM.Ind.GridAssemblyNInst.gridAsm_witZvec  1811-1813
RBM.Ind.GridAssemblyNInst.gridAsm_measurable_witZ  1816-1827
RBM.Ind.GridAssemblyNInst.gridAsm_stronglyMeasurable_witZvec  1829-1833
RBM.Ind.GridAssemblyNInst.gridAsm_witC0  1835-1840
RBM.Ind.GridAssemblyNInst.gridAsm_witProxy  1842-1843
RBM.Ind.GridAssemblyNInst.gridAsm_witProxy_pos  1845-1847
RBM.Ind.GridAssemblyNInst.gridAsm_witZ_subG  1849-1867
private RBM.Ind.GridAssemblyNInst.gridAsm_hasCondSubG_mono  1869-1881
private RBM.Ind.GridAssemblyNInst.gridAsm_hasCondSubG_const_mul  1883-1899
private RBM.Ind.GridAssemblyNInst.gridAsm_Ugen_const  1901-1907
RBM.Ind.GridAssemblyNInst.gridAsm_witSubGaussStop  1909-1981
RBM.Ind.GridAssemblyNInst.gridAsm_witAzuma  1983-1999
RBM.Ind.GridAssemblyNInst.gridAsm_bundle  2004-2064
RBM.Ind.GridAssemblyNInst.gridAsm_assembledN_instance_gen  2069-2128
RBM.Ind.GridAssemblyNInst.gridAsm_assembledN_instance_random  2130-2153
private RBM.Ind.GridAssemblyNInst.gridAsm_linTr_one_single  2155-2181
RBM.Ind.GridAssemblyNInst.gridAsm_witZ_ne_zero  2183-2193
RBM.Ind.GridAssemblyNInst.gridAsm_witZ_zero  2195-2205
RBM.Ind.GridAssemblyNInst.gridAsm_witA_ne  2207-2238
RBM.Ind.GridAssemblyNInst.gridAsm_assembledN_instance_zvec  2240-2264
### RBM3D.Induction.GridDriftN  (9 unreached of 53)
RBM.Ind.GridDriftN_exists_envelope  944-981
RBM.Ind.GridDriftNCheck.E0  1187-1188
RBM.Ind.GridDriftNCheck.s0  1189-1190
RBM.Ind.GridDriftNCheck.t0  1191-1192
RBM.Ind.GridDriftNCheck.K0  1193-1194
RBM.Ind.GridDriftNCheck.data  1196-1199
RBM.Ind.GridDriftNCheck.gridDriftN_instance  1201-1222
RBM.Ind.GridDriftNCheck.envelope_instance  1224-1231
RBM.Ind.GridDriftNCheck.exists_norm_Kcal_le_win_instance  1233-1242
### RBM3D.Induction.GridDuhamelN  (28 unreached of 44)
private RBM.Ind.GridDuhamelN_uKer_eq  69-71
RBM.Ind.Ugen_two_eq_Uop  202-229
RBM.Ind.StoppedDuhamelN  290-303
RBM.Ind.stoppedDuhamelN  333-337
RBM.Ind.AvecN_two  347-349
RBM.Ind.martIncN_two  351-354
RBM.Ind.predIncN_two  356-361
RBM.Ind.stoppedDuhamel105_of_stoppedDuhamelN  363-382
private RBM.Ind.GridDuhamelN_measurable_AvecN  392-399
private RBM.Ind.GridDuhamelN_stronglyMeasurable_martIncN  401-411
private RBM.Ind.GridDuhamelN_stronglyMeasurable_Ugen_apply  413-421
private RBM.Ind.GridDuhamelN_prependZero  432-434
private RBM.Ind.GridDuhamelN_sum_range_succ_prependZero  436-440
private RBM.Ind.GridDuhamelN_azuma_step  442-519
RBM.Ind.StoppedAzumaN  529-549
RBM.Ind.stoppedAzumaN_at  551-594
RBM.Ind.stoppedAzumaN  596-601
private RBM.Ind.GridDuhamelN_instSigma  618-618
private RBM.Ind.GridDuhamelN_instSigma_nonconst  620-621
private RBM.Ind.GridDuhamelN_instE  623-623
private RBM.Ind.GridDuhamelN_instS  624-624
private RBM.Ind.GridDuhamelN_instT  625-625
private RBM.Ind.GridDuhamelN_instK  626-626
private RBM.Ind.GridDuhamelN_inst_E  628-629
private RBM.Ind.GridDuhamelN_inst_s0  631-632
private RBM.Ind.GridDuhamelN_inst_st  634-635
private RBM.Ind.GridDuhamelN_inst_t1  637-638
private RBM.Ind.GridDuhamelN_inst_K  640-641
### RBM3D.Induction.GridEnvelopeN  (13 unreached of 32)
RBM.Ind.GridEnvelopeNCheck.four_le_size  665-673
RBM.Ind.GridEnvelopeNCheck.E1  675-676
RBM.Ind.GridEnvelopeNCheck.Kc  678-679
RBM.Ind.GridEnvelopeNCheck.Kc_ne_zero  681-686
RBM.Ind.GridEnvelopeNCheck.rpow_21_le_Kc  688-692
RBM.Ind.GridEnvelopeNCheck.rangeCond_half  694-701
RBM.Ind.GridEnvelopeNCheck.sum_weighted_stepErrN_instance  703-722
RBM.Ind.GridEnvelopeNCheck.tBd  724-725
RBM.Ind.GridEnvelopeNCheck.tBd_lt_one  727-731
RBM.Ind.GridEnvelopeNCheck.zero_le_tBd  733-737
RBM.Ind.GridEnvelopeNCheck.rangeCond_tBd  739-740
RBM.Ind.GridEnvelopeNCheck.sum_gridStep_instance  742-751
RBM.Ind.GridEnvelopeNCheck.gridDriftN_envelope_instance  753-778
### RBM3D.Induction.GridGoodN  (20 unreached of 66)
RBM.Gauss.Sizes.STXiLM  74-78
RBM.Gauss.Sizes.gridGood_STmaxLM_seqHflow  86-87
RBM.Gauss.Sizes.gridGood_STmaxLKM_seqHflow  89-90
RBM.Gauss.Sizes.gridGood_STXiLM_seqHflow  92-93
RBM.Path.goodExitTauN  175-179
private RBM.Gauss.Sizes.gridGood_meas_STmaxLM  272-284
RBM.Path.GoodExitMeasN  409-413
private RBM.Path.goodExitMeasN_of_measurable  415-419
RBM.Path.goodExitMeasN  421-424
private RBM.Gauss.Sizes.gridGood_prec_of_whp  976-985
private RBM.Gauss.Sizes.gridGood_one_add_le  987-987
private RBM.Gauss.Sizes.gridGood_prec_XiL_one  989-1014
private RBM.Gauss.Sizes.gridGood_prec_XiLK_one  1016-1041
private RBM.Gauss.Sizes.gridGood_prec_Q_one  1043-1095
RBM.Gauss.GridGoodNInst.vg  1122-1123
RBM.Gauss.GridGoodNInst.Kg  1125-1126
RBM.Gauss.GridGoodNInst.grid_data  1128-1131
RBM.Gauss.GridGoodNInst.tInst_lt_one  1168-1168
RBM.Gauss.GridGoodNInst.gridGood_instance  1170-1200
RBM.Gauss.GridGoodNInst.gridGood_instance_nonempty  1202-1214
### RBM3D.Induction.HierAlgebra  (9 unreached of 48)
private RBM.Ind.HierAlgebra_I0  780-781
private RBM.Ind.HierAlgebra_I0_wf  783-783
private RBM.Ind.HierAlgebra_I0_length  785-785
RBM.Ind.HierAlgebra_check_norm_primBil_le  787-796
RBM.Ind.HierAlgebra_check_primBil_value  798-811
RBM.Ind.HierAlgebra_check_primRhs_split  813-819
RBM.Ind.HierAlgebra_check_couplingLen_two  821-829
RBM.Ind.HierAlgebra_check_algebra  831-857
RBM.Ind.HierAlgebra_check_loopDrift_sz0  860-885
### RBM3D.Induction.HierarchyN  (13 unreached of 16)
private RBM.Ind.HierarchyN_STLIM_loopOf  81-84
private RBM.Ind.HierarchyN_STLKIM_loopOf  86-91
private RBM.Ind.HierarchyN_ThetaN_two  93-102
private RBM.Ind.HierarchyN_length_two  104-107
private RBM.Ind.HierarchyN_STelklkM_two  109-118
private RBM.Ind.HierarchyN_STegtM_two  120-129
private RBM.Ind.HierarchyN_SB_symm  131-133
private RBM.Ind.HierarchyN_STllPairN_two  135-153
RBM.Ind.hierarchyN_two  157-167
RBM.Ind.loopGenNForm_two_of_loopGenN2  169-180
RBM.Ind.HierarchyN_check_sz0  195-212
RBM.Ind.HierarchyN_check_two_sz0  214-227
RBM.Ind.HierarchyN_check_loopGenNForm_two_sz0  229-239
### RBM3D.Induction.IniTermI  (9 unreached of 120)
private RBM.Gauss.Step5Inst.iniTermI_inst_im  3739-3744
private RBM.Gauss.Step5Inst.iniTermI_inst_X  3746-3753
RBM.Gauss.Step5Inst.iniTermI_core_same_inst  3755-3766
RBM.Gauss.Step5Inst.iniTermI_core_mixed_inst  3768-3782
RBM.Gauss.Step5Inst.iniTermI_restrict_inst  3784-3797
RBM.Gauss.Step5Inst.inst_cltFarU_proved  3799-3802
RBM.Gauss.Step5Inst.inst_cltFarU_CL  3804-3809
RBM.Gauss.Step5Inst.iniTermI_cltFarU_index_nonempty  3811-3816
RBM.Gauss.Step5Inst.inst_iniTermI_proved  3818-3821
### RBM3D.Induction.IniTermII  (8 unreached of 64)
private RBM.Gauss.Sizes.iniTermII_PI_pos  77-78
private RBM.Gauss.Sizes.iniTermII_PI_le_one  80-82
private RBM.Gauss.Sizes.iniTermII_PI_sub_comm  127-129
private RBM.Gauss.Step5Inst.iniTermII_inst_im  1742-1747
RBM.Gauss.Step5Inst.iniTermII_core_inst  1749-1768
RBM.Gauss.Step5Inst.iniTermII_core_same_inst  1770-1788
RBM.Gauss.Step5Inst.iniTermII_concl_inst  1790-1796
RBM.Gauss.Step5Inst.inst_iniTermII_proved  1798-1802
### RBM3D.Induction.IterationsA  (34 unreached of 77)
RBM.Gauss.Sizes.iterationsA_STPsi_mono_n  504-508
private RBM.Gauss.Sizes.iterationsA_XLv  894-900
private RBM.Gauss.Sizes.iterationsA_XLKv  902-904
private RBM.Gauss.Sizes.iterationsA_XLv_ge_one  906-925
private RBM.Gauss.Sizes.iterationsA_XLv_le_pred  927-944
private RBM.Gauss.Sizes.iterationsA_XLv_le  946-958
private RBM.Gauss.Sizes.iterationsA_XLv_le_chain  960-993
private RBM.Gauss.Sizes.iterationsA_XLv_four_p  995-999
private RBM.Gauss.Sizes.iterationsA_XLKv_ge_one  1001-1004
private RBM.Gauss.Sizes.iterationsA_XLKv_le  1006-1010
private RBM.Gauss.Sizes.iterationsA_XLv_le_Z  1013-1025
private RBM.Gauss.Sizes.iterationsA_prec_XL_of  1027-1046
private RBM.Gauss.Sizes.iterationsA_rho  1072-1074
private RBM.Gauss.Sizes.iterationsA_XL  1076-1078
private RBM.Gauss.Sizes.iterationsA_XLK  1080-1082
private RBM.Gauss.Sizes.iterationsA_rho_ge_one  1084-1085
private RBM.Gauss.Sizes.iterationsA_rho_eq  1087-1088
private RBM.Gauss.Sizes.iterationsA_obl_short  1090-1140
private RBM.Gauss.Sizes.iterationsA_prec_chain_abs  1142-1165
private RBM.Gauss.Sizes.iterationsA_sqrt_prod_le  1167-1176
private RBM.Gauss.Sizes.iterationsA_obl_chain  1178-1236
private RBM.Gauss.Sizes.iterationsA_obl_four_p  1239-1253
private RBM.Gauss.Sizes.iterationsA_obl_K  1255-1275
RBM.Gauss.Sizes.iterationsA_step  1277-1340
private RBM.Gauss.IterationsAInst.r256_18  1787-1789
private RBM.Gauss.IterationsAInst.r256_34  1791-1793
private RBM.Gauss.IterationsAInst.r256_78  1795-1797
private RBM.Gauss.IterationsAInst.szB_hsize  1883-1883
private RBM.Gauss.IterationsAInst.szB_B_pos  1885-1885
private RBM.Gauss.IterationsAInst.zB_abs_E  1922-1922
private RBM.Gauss.IterationsAInst.szB_conI  1924-1926
private RBM.Gauss.IterationsAInst.szB_conII  1928-1930
private RBM.Gauss.IterationsAInst.szB_scaleI  1932-1936
private RBM.Gauss.IterationsAInst.szB_scaleII  1938-1942
### RBM3D.Induction.IterationsB  (6 unreached of 35)
private RBM.Gauss.Sizes.iterationsB_one_le_ratio  67-69
RBM.Gauss.IterationsBInst.inst_iterations'  603-624
RBM.Gauss.IterationsBInst.inst_iterationsII'  626-645
private RBM.Gauss.IterationsBInst.iterationsB_zB_abs_E  664-664
private RBM.Gauss.IterationsBInst.iterationsB_szB_scaleII  666-671
private RBM.Gauss.IterationsBInst.iterationsB_szB_scaleI  673-678
### RBM3D.Induction.KDecay  (18 unreached of 52)
private RBM.Gauss.KDecayInst.instA  899-901
private RBM.Gauss.KDecayInst.inst_ellT  903-913
private RBM.Gauss.KDecayInst.le_maxDist  915-917
private RBM.Gauss.KDecayInst.instA_maxDist  919-929
private RBM.Gauss.KDecayInst.instA_far  931-935
RBM.Gauss.KDecayInst.inst_stKcalDecay  937-971
RBM.Gauss.Sizes.stSumTwoLoop  1255-1334
RBM.Gauss.Sizes.stSumTwoLoop_exists  1336-1354
private RBM.Gauss.KDecayInst.z0_abs_le  1370-1371
private RBM.Gauss.KDecayInst.z0_abs_lt  1373-1373
private RBM.Gauss.KDecayInst.sz0_lam_bounds  1375-1378
private RBM.Gauss.KDecayInst.sInst_nonneg  1380-1380
private RBM.Gauss.KDecayInst.tInst_lt  1381-1381
RBM.Gauss.KDecayInst.inst_stKbound_timeIcc  1383-1390
RBM.Gauss.KDecayInst.inst_stKward_timeIcc  1392-1401
RBM.Gauss.KDecayInst.inst_KDecay_sum_tailT_le  1403-1406
RBM.Gauss.KDecayInst.inst_stSumTwoLoop  1408-1418
RBM.Gauss.KDecayInst.inst_stSumTwoLoop_exists  1421-1433
### RBM3D.Induction.LemDecCalELip  (20 unreached of 75)
private RBM.Gauss.Sizes.lemDecCalELip_word_trace_norm  141-150
RBM.Gauss.Sizes.LemDecCalELip_STLI_norm  220-231
RBM.Gauss.Sizes.LemDecCalELip_Lloop_norm  279-286
RBM.Gauss.Sizes.LemDecCalELip_LK_normg  684-694
RBM.Gauss.Sizes.LemDecCalELip_ELKLK_subg  696-736
private RBM.Gauss.Sizes.lemDecCalELip_STeeLoop_len  829-837
RBM.Gauss.Sizes.LemDecCalELip_ee_subg  839-880
private RBM.Gauss.Sizes.lemDecCalELip_bandIn_Ln  894-899
private RBM.Gauss.Sizes.lemDecCalELip_bandIn_Kn  901-904
RBM.Gauss.Sizes.LemDecCalELip_LK_norm  950-954
RBM.Gauss.Sizes.LemDecCalELip_ELKLK_sub  956-964
RBM.Gauss.Sizes.LemDecCalELip_EGt_sub  967-973
RBM.Gauss.Sizes.LemDecCalELip_ee_sub  976-986
RBM.Gauss.Sizes.LemDecCalELip_ELKLK  1058-1071
RBM.Gauss.Sizes.LemDecCalELip_EGt  1073-1086
RBM.Gauss.Sizes.LemDecCalELip_ee  1088-1101
RBM.BA.STLemDecCalEConclgL  1614-1644
RBM.BA.STLemDecCalEgL  1646-1652
RBM.BA.STLemDecCalE_iff_gL  1654-1660
private RBM.Gauss.Sizes.lemDecCalELip_inst_tN  1684-1698
### RBM3D.Induction.LemDecCalEPrec  (11 unreached of 56)
RBM.Gauss.Sizes.lemDecCalEPrec_perTime_bounds  1010-1051
RBM.Gauss.Sizes.lemDecCalEPrec_V3  1053-1058
RBM.Gauss.Sizes.lemDecCalEPrec_precPT  1060-1117
RBM.Gauss.Sizes.lemDecCalEPrec_card_V3  1184-1202
RBM.Gauss.Sizes.lemDecCalEPrec_combine  1292-1354
RBM.Gauss.Sizes.lemDecCalEPrec_floor  1373-1424
RBM.Gauss.Sizes.lemDecCalEPrec_rel  1426-1503
RBM.Gauss.Sizes.lemDecCalEPrec_R0_nonneg  1505-1517
RBM.Gauss.Sizes.stLemDecCalE_holds  1544-1656
RBM.Gauss.Sizes.lemDecCalEPrec_inst_floor  1670-1680
RBM.Gauss.Sizes.lemDecCalEPrec_inst_Jst  1682-1688
### RBM3D.Induction.LocalAvg1  (7 unreached of 23)
RBM.Gauss.Sizes.localAvg1_whp_L2  339-347
RBM.Gauss.Sizes.localAvg1_whp_omega  349-358
RBM.Gauss.Sizes.localAvg1_maxLoop2_le  360-366
RBM.Gauss.Sizes.stInitialGT2_of_L2decay  433-455
RBM.Gauss.Sizes.stStep2AvgPT_of_L2decay  498-512
RBM.Gauss.LocalAvg1Inst.localAvg1_inst_hdat  553-559
RBM.Gauss.LocalAvg1Inst.localAvg1_inst_hL  578-593
### RBM3D.Induction.LocalAvg2  (6 unreached of 16)
private RBM.Gauss.Sizes.la2_loopFine_mp_eq_pm  105-112
private RBM.Gauss.Sizes.la2_loop_pm  120-125
RBM.Gauss.Sizes.localAvg2_rhs_le  316-324
private RBM.Gauss.Sizes.la2_stGM_ne  326-329
RBM.Gauss.Sizes.localAvg2_entry_le  331-354
RBM.Gauss.Sizes.stStep2LocalPT_of_L2decay  437-458
### RBM3D.Induction.LoopC2N  (5 unreached of 29)
private RBM.Ind.LoopC2N_trCLM_apply  133-134
RBM.Ind.LoopC2NCheck.instance_data  506-508
RBM.Ind.LoopC2NCheck.hermTestFunLoopN_k3_instance  510-525
RBM.Ind.LoopC2NCheck.hermTestFunLoopN_k3_same_instance  527-544
RBM.Ind.LoopC2NCheck.hermTestFunLoopN_k1_instance  546-561
### RBM3D.Induction.LoopGenN  (11 unreached of 47)
private RBM.Ind.LoopGenN_loopL_eq  389-391
private RBM.Ind.LoopGenN_gloopProd_nil  393-394
private RBM.Ind.LoopGenN_gloopProd_cons  396-399
RBM.Ind.genMat_eq_genMatOf  561-563
RBM.Ind.recovers_loopGenN  664-667
private RBM.Ind.LoopGenN_M0  681-685
private RBM.Ind.LoopGenN_M0_isHermitian  687-688
private RBM.Ind.LoopGenN_M0_apply  690-699
private RBM.Ind.LoopGenN_check_loopGenN  701-723
RBM.Ind.LoopGenN_check_stLoopGenNForm_sz0  725-735
RBM.Ind.LoopGenN_check_hierarchyN_sz0  737-755
### RBM3D.Induction.MainIndHolds  (5 unreached of 6)
RBM.Gauss.Sizes.stMainInd_holds  31-34
RBM.Gauss.Sizes.stStep2_holds  36-40
RBM.Gauss.Sizes.stEtermsMid_holds  42-45
RBM.Gauss.Sizes.stStep5I_holds  47-49
RBM.Gauss.Sizes.stStep5II_holds  51-53
### RBM3D.Induction.MainIndOut  (1 unreached of 12)
RBM.Univ.unMLOutBA_of_pins  142-148
### RBM3D.Induction.MainIndRegimes  (35 unreached of 70)
RBM.Gauss.Sizes.ST_mainInd_iff_any  91-101
RBM.Gauss.Sizes.STMainIndR_mono  103-111
RBM.Gauss.Sizes.ST_mainIndR_III_of_steps  216-219
RBM.Gauss.Sizes.ST_mainIndR_I_of_steps  221-224
RBM.Gauss.Sizes.ST_mainIndR_seq  287-295
RBM.Gauss.Sizes.STRegChain_succ  459-461
RBM.Gauss.Sizes.ST_mainInd_of_pins  670-683
RBM.Gauss.MainIndRegimesInst.inst_caseI_III  701-702
RBM.Gauss.MainIndRegimesInst.inst_caseI_I  704-706
RBM.Gauss.MainIndRegimesInst.inst_caseII_II  708-710
RBM.Gauss.MainIndRegimesInst.inst_caseII_IV  712-714
RBM.Gauss.MainIndRegimesInst.inst_regSeq_szB  716-720
RBM.Gauss.MainIndRegimesInst.inst_localMax_sz0  722-726
RBM.Gauss.MainIndRegimesInst.inst_regimes3  728-732
RBM.Gauss.MainIndRegimesInst.inst_mainInd3  734-738
RBM.Gauss.MainIndRegimesInst.inst_pattern_szB  742-752
RBM.Gauss.MainIndRegimesInst.inst_chain_szB  754-760
RBM.Gauss.MainIndRegimesInst.parity_strictMono  762-764
RBM.Gauss.MainIndRegimesInst.parity_cover  766-770
RBM.Gauss.MainIndRegimesInst.inst_STLK_iff  772-777
RBM.Gauss.MainIndRegimesInst.inst_STLmax_iff  779-784
RBM.Gauss.MainIndRegimesInst.inst_STDecay_iff  786-791
RBM.Gauss.MainIndRegimesInst.inst_STDecayStrong_iff  793-799
RBM.Gauss.MainIndRegimesInst.inst_STLocalMax_iff  801-807
RBM.Gauss.MainIndRegimesInst.inst_STLocalEntry_iff  809-815
RBM.Gauss.MainIndRegimesInst.inst_STExp2_iff  817-822
RBM.Gauss.MainIndRegimesInst.inst_mono_I  824-826
RBM.Gauss.MainIndRegimesInst.InstMainIndRConcl  828-836
RBM.Gauss.MainIndRegimesInst.inst_mainIndR  838-847
RBM.Gauss.MainIndRegimesInst.inst_mainIndR_seq  849-856
RBM.Gauss.MainIndRegimesInst.inst_steps_III  858-863
RBM.Gauss.MainIndRegimesInst.inst_steps_I  865-871
RBM.Gauss.MainIndRegimesInst.inst_steps_II  873-879
RBM.Gauss.MainIndRegimesInst.inst_steps_IV  881-888
RBM.Gauss.MainIndRegimesInst.inst_mainInd3_data  890-899
### RBM3D.Induction.NQBudget  (64 unreached of 81)
RBM.Ind.assembledRHSNonAltN  73-91
private RBM.Ind.nqBudget_absorb  325-331
private RBM.Ind.nqBudget_K_mul_step  345-350
RBM.Ind.tbDriftNonAltN  387-452
private RBM.Ind.nqBudget_final  523-539
RBM.Ind.budgetNonAltN  541-822
private RBM.Ind.NQBudgetInst.W0  877-877
private RBM.Ind.NQBudgetInst.lam0  879-879
private RBM.Ind.NQBudgetInst.N0  881-881
private RBM.Ind.NQBudgetInst.abs_half  883-883
private RBM.Ind.NQBudgetInst.im_ge  885-889
private RBM.Ind.NQBudgetInst.im_le  891-891
private RBM.Ind.NQBudgetInst.u_le  893-896
private RBM.Ind.NQBudgetInst.u_nonneg  898-899
private RBM.Ind.NQBudgetInst.u_lt_one  901-902
private RBM.Ind.NQBudgetInst.u_mono  904-908
private RBM.Ind.NQBudgetInst.eta_inv_le  910-920
private RBM.Ind.NQBudgetInst.eta_inv_le_N  922-927
private RBM.Ind.NQBudgetInst.Bseq  929-930
private RBM.Ind.NQBudgetInst.Bseq_pos  932-933
private RBM.Ind.NQBudgetInst.Bseq_mono  935-936
private RBM.Ind.NQBudgetInst.eta_pos'  938-939
RBM.Ind.NQBudgetInst.tbInitN_instance  944-951
RBM.Ind.NQBudgetInst.tbDriftN_instance  953-970
RBM.Ind.NQBudgetInst.tbQvN_instance  972-986
private RBM.Ind.NQBudgetInst.Kg0  1084-1084
private RBM.Ind.NQBudgetInst.u4  1086-1087
private RBM.Ind.NQBudgetInst.step0  1089-1089
private RBM.Ind.NQBudgetInst.two_pow_rpow  1091-1092
private RBM.Ind.NQBudgetInst.two_rpow_nat_mul  1094-1095
private RBM.Ind.NQBudgetInst.W_rpow  1097-1099
private RBM.Ind.NQBudgetInst.N_rpow  1101-1103
private RBM.Ind.NQBudgetInst.W_eps  1105-1106
private RBM.Ind.NQBudgetInst.W_C  1108-1109
private RBM.Ind.NQBudgetInst.N_eps0  1111-1114
private RBM.Ind.NQBudgetInst.N_eps1  1116-1117
private RBM.Ind.NQBudgetInst.N_tauK  1119-1120
private RBM.Ind.NQBudgetInst.N_one  1122-1123
private RBM.Ind.NQBudgetInst.N_negone  1125-1126
private RBM.Ind.NQBudgetInst.N_five  1128-1129
private RBM.Ind.NQBudgetInst.W_neg  1131-1132
private RBM.Ind.NQBudgetInst.log_N  1134-1135
private RBM.Ind.NQBudgetInst.Ls_bounds  1137-1150
private RBM.Ind.NQBudgetInst.rpow_three_halves  1155-1161
private RBM.Ind.NQBudgetInst.uStepC_le_one  1163-1179
private RBM.Ind.NQBudgetInst.kStepC_le  1181-1184
private RBM.Ind.NQBudgetInst.stepErr_le  1187-1237
RBM.Ind.NQBudgetInst.hR_instance  1239-1263
private RBM.Ind.NQBudgetInst.eta_inv_le_v  1267-1268
RBM.Ind.NQBudgetInst.hlog_instance  1270-1287
private RBM.Ind.NQBudgetInst.le_P0  1289-1295
private RBM.Ind.NQBudgetInst.ha1_inst  1297-1304
private RBM.Ind.NQBudgetInst.ha2_inst  1306-1318
private RBM.Ind.NQBudgetInst.ha3_inst  1320-1335
private RBM.Ind.NQBudgetInst.W_neg6  1337-1338
private RBM.Ind.NQBudgetInst.W_neg5  1340-1341
private RBM.Ind.NQBudgetInst.he1_inst  1343-1352
private RBM.Ind.NQBudgetInst.he3_inst  1354-1364
private RBM.Ind.NQBudgetInst.he4_inst  1366-1372
private RBM.Ind.NQBudgetInst.he2_inst  1374-1401
private RBM.Ind.NQBudgetInst.Cpos  1403-1404
RBM.Ind.NQBudgetInst.budgetNonAltN_instance  1406-1425
RBM.Ind.NQBudgetInst.nqBudget_merged_inputs_instance  1433-1457
RBM.Ind.NQBudgetInst.nqBudget_merged_inputs_exists  1459-1476
### RBM3D.Induction.NQEndFlow  (9 unreached of 46)
RBM.Gauss.Sizes.STOeqNQ''  123-124
private RBM.Gauss.Sizes.nqFlow_bootRHS_anti  187-203
private RBM.Gauss.Sizes.stNQConcl''_of_stNQConcl'  213-232
RBM.Gauss.Sizes.stXiBoot'_of_stXiBoot  234-245
private RBM.Gauss.Sizes.nqFlow_ingR_mono  247-263
RBM.Gauss.Sizes.stOeqNQ''_of_stOeqNQ'  265-268
RBM.Gauss.Sizes.stOeqQt'_of_stOeqQt  270-273
RBM.Gauss.Sizes.stOeqQtNZ'_of_stOeqQtNZ  275-278
RBM.Ind.NQEndFlowInst.inst_OeqNQPT''  970-977
### RBM3D.Induction.NQEndFlowLift  (22 unreached of 28)
private RBM.Ind.nqLift_sharp_one_le  73-76
private RBM.Ind.nqLift_sharp_le  78-87
private RBM.Ind.nqLift_sharp_mono  89-97
private RBM.Ind.nqLift_sharp_prec  99-124
private RBM.Ind.nqLift_bootRHS_mono  132-164
private RBM.Ind.nqLift_bootRHS_one_le  166-183
private RBM.Ind.nqLift_zeta_mono  185-211
private RBM.Ind.nqLift_zeta_le  213-230
private RBM.Ind.nqLift_zeta_one_le  232-248
private RBM.Ind.nqLift_stochDomAt_of_subset  267-293
private RBM.Ind.nqLift_time  295-297
private RBM.Ind.nqLift_time_mem  299-304
private RBM.Ind.nqLift_netPt_floor  306-325
private RBM.Ind.nqLift_core_below  327-416
private RBM.Ind.nqLift_arith  703-750
private RBM.Ind.nqLift_xi_close  752-827
private RBM.Ind.nqLift_card_V  829-847
private RBM.Ind.nqLift_prec_of_le_right  849-856
private RBM.Ind.nqLift_flowLam  858-863
private RBM.Ind.nqLift_lift  865-926
RBM.Ind.stOeqNQ''_holds  932-955
RBM.Ind.NQEndFlowLiftInst.inst_OeqNQ''  970-976
### RBM3D.Induction.NQEndLin  (41 unreached of 77)
private RBM.Ind.nqEnd_one_le_W  130-131
RBM.Ind.NQEndLinInst.κi  1297-1298
RBM.Ind.NQEndLinInst.Ci  1300-1301
RBM.Ind.NQEndLinInst.Ci_pos  1303-1303
RBM.Ind.NQEndLinInst.e0i  1305-1306
RBM.Ind.NQEndLinInst.epsi  1307-1307
RBM.Ind.NQEndLinInst.Ddi  1308-1308
private RBM.Ind.NQEndLinInst.arith_i  1310-1311
RBM.Ind.NQEndLinInst.hE_i  1313-1313
RBM.Ind.NQEndLinInst.hκm_i  1315-1316
RBM.Ind.NQEndLinInst.hlam_i  1318-1321
RBM.Ind.NQEndLinInst.rangeCond_tInst  1323-1324
RBM.Ind.NQEndLinInst.rangeCond_vg  1326-1327
RBM.Ind.NQEndLinInst.vg_le_tInst  1329-1329
RBM.Ind.NQEndLinInst.sInst_le_tInst  1331-1331
RBM.Ind.NQEndLinInst.WtInst  1333-1339
RBM.Ind.NQEndLinInst.hσ3_i  1341-1341
RBM.Ind.NQEndLinInst.KC  1345-1346
RBM.Ind.NQEndLinInst.KC_ne_zero  1348-1350
RBM.Ind.NQEndLinInst.KC_low  1352-1355
RBM.Ind.NQEndLinInst.KC_up  1357-1361
RBM.Ind.NQEndLinInst.window_nondegenerate  1363-1369
RBM.Ind.NQEndLinInst.asymp_instance  1373-1380
RBM.Ind.NQEndLinInst.union_instance  1387-1389
RBM.Ind.NQEndLinInst.rangeCond_mono_instance  1391-1392
RBM.Ind.NQEndLinInst.ha1_instance  1394-1397
RBM.Ind.NQEndLinInst.ha2_instance  1399-1404
RBM.Ind.NQEndLinInst.ha3_instance  1406-1411
RBM.Ind.NQEndLinInst.he1_instance  1413-1416
RBM.Ind.NQEndLinInst.he2_instance  1418-1423
RBM.Ind.NQEndLinInst.he34_instance  1425-1428
RBM.Ind.NQEndLinInst.hη_instance  1430-1433
RBM.Ind.NQEndLinInst.hδ_instance  1435-1444
RBM.Ind.NQEndLinInst.hΔη_instance  1446-1456
RBM.Ind.NQEndLinInst.hwL_i  1462-1465
RBM.Ind.NQEndLinInst.hWt_vg  1467-1472
RBM.Ind.NQEndLinInst.hW1_i  1474-1475
RBM.Ind.NQEndLinInst.hWε_i  1477-1479
RBM.Ind.NQEndLinInst.hdW_i  1481-1490
RBM.Ind.NQEndLinInst.assembly_instance  1492-1542
RBM.Ind.NQEndLinInst.nqEndLin_instance  1546-1577
### RBM3D.Induction.NQGood1  (68 unreached of 102)
RBM.Ind.driftTensorN_norm_le_of_goodSet  101-128
RBM.Ind.qvFormN_le_of_goodSetN  547-574
RBM.Ind.loopMax_zshiftN_le  695-715
RBM.Ind.etaT_inv_shiftN_le  748-777
RBM.Ind.loopFine_shiftN_le  779-800
RBM.Ind.nqGood1_STmaxLM_shiftN_le  822-833
RBM.Ind.nqGood1_STmaxLM_nonneg  835-839
RBM.Ind.STXiLM_shiftN_le  841-865
private RBM.Ind.nqGood1_STdiamInf_one  867-873
RBM.Ind.goodSetN_dec_shiftN  875-912
private RBM.Ind.NQGood1Inst.W0  1071-1071
private RBM.Ind.NQGood1Inst.lam0  1073-1073
private RBM.Ind.NQGood1Inst.L0  1075-1075
private RBM.Ind.NQGood1Inst.L0r  1077-1077
private RBM.Ind.NQGood1Inst.rpow32_fifth  1079-1082
private RBM.Ind.NQGood1Inst.rpow32_four_fifth  1084-1088
private RBM.Ind.NQGood1Inst.rpow32_neg  1090-1091
private RBM.Ind.NQGood1Inst.ell0  1093-1095
private RBM.Ind.NQGood1Inst.im_mE_half  1097-1099
private RBM.Ind.NQGood1Inst.abs_half  1101-1101
RBM.Ind.NQGood1Inst.aFar  1103-1104
private RBM.Ind.NQGood1Inst.zdistInf_two  1106-1107
RBM.Ind.NQGood1Inst.diam_aFar  1109-1115
RBM.Ind.NQGood1Inst.zero_mem_goodSetN_inst  1117-1125
RBM.Ind.NQGood1Inst.zero_mem_goodSetN_inst_grid  1127-1132
RBM.Ind.NQGood1Inst.drift_norm_instance  1136-1142
RBM.Ind.NQGood1Inst.drift_far_instance  1144-1152
RBM.Ind.NQGood1Inst.Xinst  1156-1159
RBM.Ind.NQGood1Inst.Xinst_zero  1161-1166
RBM.Ind.NQGood1Inst.Xinst_norm_le  1168-1169
RBM.Ind.NQGood1Inst.Xinst_far  1171-1178
private RBM.Ind.NQGood1Inst.hW_inst  1180-1180
private RBM.Ind.NQGood1Inst.hWε_inst  1182-1183
private RBM.Ind.NQGood1Inst.hdW_inst  1185-1187
private RBM.Ind.NQGood1Inst.hWt_inst  1189-1190
private RBM.Ind.NQGood1Inst.hwL_inst  1192-1193
private RBM.Ind.NQGood1Inst.hσ_inst  1195-1195
RBM.Ind.NQGood1Inst.hker_instance  1197-1210
RBM.Ind.NQGood1Inst.nqGood1C_pos_instance  1212-1214
RBM.Ind.NQGood1Inst.mE_im_ge_instance  1216-1218
RBM.Ind.NQGood1Inst.qvFormN_instance  1222-1239
RBM.Ind.NQGood1Inst.ugenPairN_instance  1241-1262
RBM.Ind.NQGood1Inst.qvFormN_eq_re_instance  1264-1271
RBM.Ind.NQGood1Inst.ugenPairN_eq_instance  1274-1283
private RBM.Ind.NQGood1Inst.hη_inst  1287-1287
private RBM.Ind.NQGood1Inst.hz_inst  1289-1291
private RBM.Ind.NQGood1Inst.hz'_inst  1293-1294
private RBM.Ind.NQGood1Inst.im_mE_nine  1296-1301
private RBM.Ind.NQGood1Inst.etaInv_inst  1303-1310
RBM.Ind.NQGood1Inst.etaT_inv_shift_instance  1312-1319
RBM.Ind.NQGood1Inst.H0v  1321-1322
RBM.Ind.NQGood1Inst.loopL_shift_instance  1324-1333
RBM.Ind.NQGood1Inst.loopMax_shift_instance  1335-1341
RBM.Ind.NQGood1Inst.loopShiftErrN_nonneg_instance  1343-1346
RBM.Ind.NQGood1Inst.loopFine_shift_instance  1348-1356
RBM.Ind.NQGood1Inst.ellT_mono_instance  1358-1363
RBM.Ind.NQGood1Inst.STmaxLM_shift_instance  1365-1373
RBM.Ind.NQGood1Inst.STmaxLM_nonneg_instance  1375-1379
RBM.Ind.NQGood1Inst.STXiLM_shift_instance  1381-1390
private RBM.Ind.NQGood1Inst.hδ_inst  1392-1416
RBM.Ind.NQGood1Inst.dec_shift_instance  1418-1428
RBM.Ind.NQGood1Inst.loopFine_crude_instance  1430-1435
RBM.Ind.NQGood1Inst.MKinst  1437-1440
RBM.Ind.NQGood1Inst.MKinst_spec  1442-1445
RBM.Ind.NQGood1Inst.STmaxLKM_crude_instance  1447-1452
private RBM.Ind.NQGood1Inst.Bctl0_le  1454-1458
RBM.Ind.NQGood1Inst.STXiLKM_crude_instance  1460-1466
RBM.Ind.NQGood1Inst.STeeM_shift_instance  1468-1476
### RBM3D.Induction.NQGood2  (63 unreached of 86)
RBM.Ind.dDriftNonAltN  94-97
RBM.Ind.nonAlt_hdriftN  312-322
RBM.Ind.nonAlt_hdDrift0N  372-389
RBM.Ind.subGaussStop_nonAltN  558-584
private RBM.Ind.NQGood2Inst.W0  628-628
private RBM.Ind.NQGood2Inst.lam0  630-630
private RBM.Ind.NQGood2Inst.L0  632-632
private RBM.Ind.NQGood2Inst.L0r  634-634
private RBM.Ind.NQGood2Inst.rpow32_fifth  636-639
private RBM.Ind.NQGood2Inst.rpow32_four_fifth  641-645
private RBM.Ind.NQGood2Inst.rpow32_neg  647-648
private RBM.Ind.NQGood2Inst.abs_half  650-650
private RBM.Ind.NQGood2Inst.im_mE_half  652-654
private RBM.Ind.NQGood2Inst.im_mE_nine  656-661
private RBM.Ind.NQGood2Inst.hσ3  663-663
private RBM.Ind.NQGood2Inst.hW1  665-665
private RBM.Ind.NQGood2Inst.hW1'  667-667
private RBM.Ind.NQGood2Inst.hW0  669-669
private RBM.Ind.NQGood2Inst.hWε  671-672
private RBM.Ind.NQGood2Inst.hdW  674-676
RBM.Ind.NQGood2Inst.gridTime_inst  678-682
private RBM.Ind.NQGood2Inst.u_le_of_le  684-687
private RBM.Ind.NQGood2Inst.u_nonneg  689-690
private RBM.Ind.NQGood2Inst.u_lt_one  692-693
private RBM.Ind.NQGood2Inst.u_mono  695-699
private RBM.Ind.NQGood2Inst.hwL  701-703
private RBM.Ind.NQGood2Inst.hvL  705-707
private RBM.Ind.NQGood2Inst.hWt  709-711
RBM.Ind.NQGood2Inst.ratio_instance  715-722
RBM.Ind.NQGood2Inst.kappa_Bctl_instance  724-731
RBM.Ind.NQGood2Inst.kappa_succ_instance  733-740
private RBM.Ind.NQGood2Inst.ell_u0  744-746
private RBM.Ind.NQGood2Inst.ell_u1  748-756
RBM.Ind.NQGood2Inst.hker_field_instance  758-776
RBM.Ind.NQGood2Inst.Xinst_cls  778-783
RBM.Ind.NQGood2Inst.hker_applied  785-794
RBM.Ind.NQGood2Inst.tau0  796-797
RBM.Ind.NQGood2Inst.tau0_mem  799-803
RBM.Ind.NQGood2Inst.tau0_pos  805-810
RBM.Ind.NQGood2Inst.A0cls_instance  812-819
RBM.Ind.NQGood2Inst.driftCls_instance  821-829
RBM.Ind.NQGood2Inst.hA0cls_instance  831-837
RBM.Ind.NQGood2Inst.hA0cls_far_instance  839-846
RBM.Ind.NQGood2Inst.hdrift_instance  848-854
RBM.Ind.NQGood2Inst.hDcls_instance  856-865
RBM.Ind.NQGood2Inst.hDcls_far_instance  867-875
RBM.Ind.NQGood2Inst.hκ0_instance  877-881
RBM.Ind.NQGood2Inst.hε0_instance  883-885
RBM.Ind.NQGood2Inst.hdDrift0_instance  887-892
private RBM.Ind.NQGood2Inst.etaT_ge  897-901
RBM.Ind.NQGood2Inst.eeShiftErrN_inst_le  903-931
RBM.Ind.NQGood2Inst.delta_shift_ok  933-954
RBM.Ind.NQGood2Inst.qvBd_pos_instance  956-961
RBM.Ind.NQGood2Inst.qvFormN_shift_instance  963-981
RBM.Ind.NQGood2Inst.hQ_instance  983-994
RBM.Ind.NQGood2Inst.hQ_instance_zero  996-1002
RBM.Ind.NQGood2Inst.subGaussStop_instance  1004-1017
RBM.Ind.NQGood2Inst.hc_pos_instance  1019-1026
RBM.Ind.NQGood2Inst.Dr0  1031-1033
RBM.Ind.NQGood2Inst.A0f  1035-1037
RBM.Ind.NQGood2Inst.Af  1039-1047
RBM.Ind.NQGood2Inst.gridAssemblyHyp_instance  1050-1099
RBM.Ind.NQGood2Inst.bundle_fields_instance  1101-1120
### RBM3D.Induction.NQLin  (61 unreached of 107)
RBM.Gauss.Sizes.goodSetN_subset_goodLinN  210-222
private RBM.Gauss.Sizes.nqLin_prec_of_whp  618-627
private RBM.Gauss.Sizes.nqLin_one_add_le  629-629
private RBM.Gauss.Sizes.nqLin_prec_XiL_one  631-656
private RBM.Gauss.Sizes.nqLin_prec_XiLK_one  658-683
private RBM.Gauss.Sizes.nqLin_LmaxU_restrict  685-690
private RBM.Gauss.Sizes.nqLin_LKU_restrict  692-697
RBM.Ind.dDriftNonAltN_eq_lin  722-727
private RBM.Ind.NQLinInst.W0  1262-1262
private RBM.Ind.NQLinInst.lam0  1264-1264
private RBM.Ind.NQLinInst.L0  1266-1266
private RBM.Ind.NQLinInst.L0r  1268-1268
private RBM.Ind.NQLinInst.N0  1270-1270
private RBM.Ind.NQLinInst.rpow32_fifth  1272-1275
private RBM.Ind.NQLinInst.rpow32_four_fifth  1277-1281
private RBM.Ind.NQLinInst.abs_half  1283-1283
private RBM.Ind.NQLinInst.im_ge  1285-1289
private RBM.Ind.NQLinInst.im_mE_half  1291-1293
private RBM.Ind.NQLinInst.hσ3  1295-1295
private RBM.Ind.NQLinInst.hW1  1297-1297
private RBM.Ind.NQLinInst.hWε  1299-1300
private RBM.Ind.NQLinInst.hdW  1302-1304
private RBM.Ind.NQLinInst.hvL  1306-1308
RBM.Ind.NQLinInst.nqLinExitTauN_eq_tau0  1312-1328
RBM.Ind.NQLinInst.nqLinExitTauN_pos  1330-1334
RBM.Ind.NQLinInst.zero_mem_goodLinN_inst  1336-1344
RBM.Ind.NQLinInst.drift_lin_instance  1359-1364
RBM.Ind.NQLinInst.dDriftLinN_inst_pos  1366-1372
RBM.Ind.NQLinInst.hdrift_lin_instance  1374-1384
RBM.Ind.NQLinInst.subGaussStop_lin_instance  1400-1414
RBM.Ind.NQLinInst.nqLinGood_instance  1425-1450
RBM.Ind.NQLinInst.nqLinGood_instance_nonempty  1452-1463
private RBM.Ind.NQLinInst.eta_inv_le  1500-1508
private RBM.Ind.NQLinInst.eta_inv_le_N  1510-1515
private RBM.Ind.NQLinInst.eta_inv_le_v  1517-1518
private RBM.Ind.NQLinInst.step0  1520-1520
private RBM.Ind.NQLinInst.two_pow_rpow  1522-1523
private RBM.Ind.NQLinInst.two_rpow_nat_mul  1525-1526
private RBM.Ind.NQLinInst.W_rpow  1528-1530
private RBM.Ind.NQLinInst.N_rpow  1532-1534
private RBM.Ind.NQLinInst.W_eps  1536-1537
private RBM.Ind.NQLinInst.W_C  1539-1540
private RBM.Ind.NQLinInst.N_eps0  1542-1545
private RBM.Ind.NQLinInst.N_eps1  1547-1548
private RBM.Ind.NQLinInst.N_one  1550-1551
private RBM.Ind.NQLinInst.N_negone  1553-1554
private RBM.Ind.NQLinInst.N_five  1556-1557
private RBM.Ind.NQLinInst.W_neg  1559-1560
private RBM.Ind.NQLinInst.log_N  1562-1563
private RBM.Ind.NQLinInst.Ls_bounds  1565-1578
private RBM.Ind.NQLinInst.le_P0  1580-1586
private RBM.Ind.NQLinInst.ha1_inst  1588-1595
private RBM.Ind.NQLinInst.ha2_inst  1597-1611
private RBM.Ind.NQLinInst.ha3_inst  1613-1628
private RBM.Ind.NQLinInst.W_neg6  1630-1631
private RBM.Ind.NQLinInst.W_neg5  1633-1634
private RBM.Ind.NQLinInst.he1_inst  1636-1645
private RBM.Ind.NQLinInst.he3_inst  1647-1657
private RBM.Ind.NQLinInst.he4_inst  1659-1665
private RBM.Ind.NQLinInst.he2_inst  1667-1694
RBM.Ind.NQLinInst.budgetNonAltLinN_instance  1718-1738
### RBM3D.Induction.NewKLK  (5 unreached of 40)
private RBM.Gauss.Sizes.nkl_STmsig_eq  987-987
private RBM.Gauss.Sizes.nkl_mE_zero  1211-1215
private RBM.Gauss.Sizes.nkl_diag0  1217-1228
private RBM.Gauss.Sizes.nkl_STGMM_zero  1230-1251
RBM.Gauss.Sizes.stNewKLKAt_holds  1318-1324
### RBM3D.Induction.NewKLKL  (4 unreached of 34)
private RBM.Gauss.Sizes.newKLKL_mE_zero  847-851
private RBM.Gauss.Sizes.newKLKL_diag0  853-864
private RBM.Gauss.Sizes.newKLKL_STGMM_zero  866-887
private RBM.Gauss.Sizes.newKLKLsz31  919-925
### RBM3D.Induction.OptL2a  (1 unreached of 39)
private RBM.Gauss.OptL2aInst.OptL2a_hcon  1436-1438
### RBM3D.Induction.PerTimeCalc  (39 unreached of 74)
private RBM.Ind.PerTimeCalc.imp_min  275-283
RBM.Ind.PerTimeCalc.PerTime.stochDom_min  500-505
RBM.Ind.PerTimeCalc.PerTime.quad_le_one  507-522
RBM.Ind.PerTimeCalc.Unif.perTimeCalc_of_imp  540-552
RBM.Ind.PerTimeCalc.Unif.perTimeCalc_of_imp_union  554-570
RBM.Ind.PerTimeCalc.Unif.perTimeCalc_refl  572-586
RBM.Ind.PerTimeCalc.Unif.perTimeCalc_add  588-594
RBM.Ind.PerTimeCalc.Unif.perTimeCalc_mul  596-603
RBM.Ind.PerTimeCalc.Unif.perTimeCalc_mono  605-611
RBM.Ind.PerTimeCalc.Unif.mono_right_eventually  615-619
RBM.Ind.PerTimeCalc.Unif.rpow_of_le_one  621-627
RBM.Ind.PerTimeCalc.Unif.sqrt_of  629-635
RBM.Ind.PerTimeCalc.Unif.of_forall_rpow_mul  637-647
RBM.Ind.PerTimeCalc.Unif.of_le_add_sqrt_mul  649-655
RBM.Ind.PerTimeCalc.Unif.finset_sum_of  657-671
RBM.Ind.PerTimeCalc.Unif.stochDom_of_forall_or  727-735
RBM.Ind.PerTimeCalc.Unif.stochDom_of_le_const_mul  737-743
RBM.Ind.PerTimeCalc.Unif.stochDom_of_le_left_eventually  745-750
RBM.Ind.PerTimeCalc.Unif.stochDom_of_highProb  752-764
RBM.Ind.PerTimeCalc.Unif.stochDom_min  768-773
RBM.Ind.PerTimeCalc.Unif.quad_le_one  775-790
RBM.Ind.PerTimeCalcInst.s0  851-852
RBM.Ind.PerTimeCalcInst.t0  854-855
RBM.Ind.PerTimeCalcInst.s0_lt_t0  857-857
private RBM.Ind.PerTimeCalcInst.one_le_size  859-860
RBM.Ind.PerTimeCalcInst.xF  862-864
RBM.Ind.PerTimeCalcInst.fF  866-867
RBM.Ind.PerTimeCalcInst.xF_nonneg  869-870
RBM.Ind.PerTimeCalcInst.xF_le_fF  872-877
RBM.Ind.PerTimeCalcInst.fF_nonneg  879-880
RBM.Ind.PerTimeCalcInst.xF_nonconst  882-888
RBM.Ind.PerTimeCalcInst.forbidden_region_sz0  890-910
RBM.Ind.PerTimeCalcInst.stepOneBootstrap_sz0  912-933
RBM.Ind.PerTimeCalcInst.pt_Xi_Ze  942-944
RBM.Ind.PerTimeCalcInst.pt_Ze_Ch  946-948
private RBM.Ind.PerTimeCalcInst.Xi_le_Ze  950-951
private RBM.Ind.PerTimeCalcInst.Ze_le_Ch  953-954
private RBM.Ind.PerTimeCalcInst.pt_Xi_one  1036-1039
private RBM.Ind.PerTimeCalcInst.prec_Xi_one  1041-1044
### RBM3D.Induction.PfStep5  (12 unreached of 80)
RBM.Gauss.PfStep5Inst.pfStep5_inst_realize  2494-2500
RBM.Gauss.PfStep5Inst.pfStep5_inst_realize_one  2502-2507
RBM.Gauss.PfStep5Inst.pfStep5_inst_goodMeas  2509-2515
RBM.Gauss.PfStep5Inst.pfStep5_inst_farAbsorb  2517-2523
RBM.Gauss.PfStep5Inst.pfStep5_inst_walk  2525-2530
RBM.Gauss.PfStep5Inst.pfStep5_inst_PT  2532-2538
RBM.Gauss.PfStep5Inst.pfStep5_inst_lift  2540-2545
RBM.Gauss.PfStep5Inst.pfStep5_inst_Prec  2547-2550
RBM.Gauss.PfStep5Inst.pfStep5_inst_PT_of_premises  2552-2559
RBM.Gauss.PfStep5Inst.pfStep5_inst_Prec_of_premises  2561-2567
RBM.Gauss.PfStep5Inst.pfStep5_inst_pf  2569-2573
RBM.Gauss.PfStep5Inst.pfStep5_inst_step5III  2575-2579
### RBM3D.Induction.PfStep5Alg  (21 unreached of 42)
RBM.Gauss.Sizes.PfStep5Alg_goodStop_pin  106-115
RBM.Gauss.Sizes.pfStep5Alg_ugenSum  264-270
RBM.Gauss.Sizes.pfStep5Alg_goodStop  404-407
private RBM.Gauss.Sizes.pfStep5Alg_instA  533-534
RBM.Gauss.Sizes.pfStep5Alg_instA_dist  536-538
RBM.Gauss.Sizes.pfStep5Alg_inst_tailAnti  540-542
RBM.Gauss.Sizes.pfStep5Alg_inst_tailAnti_strict  544-550
private RBM.Gauss.Sizes.pfStep5Alg_instU  552-554
private RBM.Gauss.Sizes.pfStep5Alg_instU_mono  556-559
RBM.Gauss.Sizes.pfStep5Alg_inst_ugenSum'_zero  561-578
RBM.Gauss.Sizes.pfStep5Alg_inst_ugenSum'_extremal  580-599
RBM.Gauss.Sizes.pfStep5Alg_inst_ugenSum_zero  601-618
RBM.Gauss.Sizes.pfStep5Alg_inst_riemann  620-635
RBM.Gauss.Sizes.pfStep5Alg_inst_riemann_sum  637-640
RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop'  642-650
RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop  652-659
RBM.Gauss.Sizes.pfStep5Alg_inst_goodProb  661-671
RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop'_nonvac  673-746
RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop_nonvac_one  748-758
RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop'_nonvac_55  760-770
RBM.Gauss.Sizes.pfStep5Alg_inst_closure  772-781
### RBM3D.Induction.PfStep5Grid  (21 unreached of 66)
RBM.Gauss.Sizes.PfStep5Grid_stopIdx  82-91
RBM.Gauss.Sizes.PfStep5Grid_stop_pin  110-114
RBM.Gauss.Sizes.PfStep5Grid_below_pin  116-123
private RBM.Gauss.Sizes.pfStep5Grid_JsharpM_measurable  196-210
RBM.Gauss.Sizes.pfStep5Grid_stop  212-219
RBM.Gauss.Sizes.pfStep5Grid_below  221-229
private RBM.Gauss.Sizes.pfStep5Grid_gres_zero_true  997-1012
private RBM.Gauss.Sizes.pfStep5Grid_gres_zero  1014-1022
private RBM.Gauss.Sizes.pfStep5Grid_sum_block_indicator  1024-1036
private RBM.Gauss.Sizes.pfStep5Grid_trace_Eblk_mul  1038-1060
private RBM.Gauss.Sizes.pfStep5Grid_STKloop_zero  1062-1075
private RBM.Gauss.Sizes.pfStep5Grid_STLM_zero  1077-1090
private RBM.Gauss.Sizes.pfStep5Grid_STLKM_zero  1092-1097
private RBM.Gauss.Sizes.pfStep5Grid_JsharpM_zero  1099-1105
private RBM.Gauss.Sizes.pfStep5Grid_firstHit_pos  1107-1117
RBM.Gauss.Sizes.pfStep5Grid_inst_level  1134-1146
RBM.Gauss.Sizes.pfStep5Grid_inst_Jsharp  1148-1153
RBM.Gauss.Sizes.pfStep5Grid_inst_stop  1155-1164
RBM.Gauss.Sizes.pfStep5Grid_inst_below_flow  1166-1179
RBM.Gauss.Sizes.pfStep5Grid_inst_duhamel  1181-1204
RBM.Gauss.Sizes.pfStep5Grid_inst_below  1206-1238
### RBM3D.Induction.QBudgetA  (61 unreached of 93)
RBM.Ind.altBudget_kapFarg_band  245-246
RBM.Ind.altBudget_qvFarg_band  248-249
RBM.Ind.qvBdAltQNg_band  251-253
RBM.Ind.cQVAltQNg_band  255-258
RBM.Ind.dDriftAltLinQNg_band  260-262
RBM.Ind.assembledRHSAltQNg_band  264-267
RBM.Ind.dDriftAltQN_le_shape  943-1007
private RBM.Ind.QBudgetAInst.W0  1027-1027
private RBM.Ind.QBudgetAInst.lam0  1029-1029
private RBM.Ind.QBudgetAInst.N0  1031-1031
private RBM.Ind.QBudgetAInst.abs_half  1033-1033
private RBM.Ind.QBudgetAInst.im_ge  1035-1039
private RBM.Ind.QBudgetAInst.eta_inv_le  1041-1049
private RBM.Ind.QBudgetAInst.eta_inv_le_N  1051-1056
private RBM.Ind.QBudgetAInst.eta_inv_le_v  1058-1059
private RBM.Ind.QBudgetAInst.step0  1061-1061
private RBM.Ind.QBudgetAInst.two_pow_rpow  1063-1064
private RBM.Ind.QBudgetAInst.two_rpow_nat_mul  1066-1067
private RBM.Ind.QBudgetAInst.W_rpow  1069-1071
private RBM.Ind.QBudgetAInst.N_rpow  1073-1075
private RBM.Ind.QBudgetAInst.W_eps  1077-1079
private RBM.Ind.QBudgetAInst.W_fifth  1081-1083
private RBM.Ind.QBudgetAInst.W_C  1085-1086
private RBM.Ind.QBudgetAInst.N_eps0  1088-1094
private RBM.Ind.QBudgetAInst.N_eps1  1096-1097
private RBM.Ind.QBudgetAInst.N_one  1099-1100
private RBM.Ind.QBudgetAInst.N_negone  1102-1103
private RBM.Ind.QBudgetAInst.N_five  1105-1106
private RBM.Ind.QBudgetAInst.W_neg  1108-1109
private RBM.Ind.QBudgetAInst.W_neg6  1111-1112
private RBM.Ind.QBudgetAInst.W_neg5  1114-1115
private RBM.Ind.QBudgetAInst.W_neg6_add  1117-1120
private RBM.Ind.QBudgetAInst.log_N  1122-1123
private RBM.Ind.QBudgetAInst.Ls_bounds  1125-1138
private RBM.Ind.QBudgetAInst.le_P  1140-1149
private RBM.Ind.QBudgetAInst.ha1_inst  1154-1163
private RBM.Ind.QBudgetAInst.ha2_inst  1165-1184
private RBM.Ind.QBudgetAInst.ha3_inst  1186-1206
private RBM.Ind.QBudgetAInst.he0_inst  1208-1220
private RBM.Ind.QBudgetAInst.he1_inst  1222-1245
private RBM.Ind.QBudgetAInst.he2_inst  1247-1281
private RBM.Ind.QBudgetAInst.he3_inst  1283-1293
private RBM.Ind.QBudgetAInst.he4_inst  1295-1307
private RBM.Ind.QBudgetAInst.C4₀_pos  1314-1315
private RBM.Ind.QBudgetAInst.Cn₀_pos  1317-1318
private RBM.Ind.QBudgetAInst.s0  1320-1320
private RBM.Ind.QBudgetAInst.sv  1322-1322
private RBM.Ind.QBudgetAInst.v1  1324-1324
private RBM.Ind.QBudgetAInst.K0  1326-1326
private RBM.Ind.QBudgetAInst.u_nonneg  1328-1329
private RBM.Ind.QBudgetAInst.u_lt  1331-1332
private RBM.Ind.QBudgetAInst.u_mono  1334-1335
private RBM.Ind.QBudgetAInst.u_zero  1337-1337
private RBM.Ind.QBudgetAInst.u_last  1339-1339
private RBM.Ind.QBudgetAInst.inv_one_sub_le  1341-1342
private RBM.Ind.QBudgetAInst.Pa_nonneg  1344-1347
private RBM.Ind.QBudgetAInst.hdd_inst  1349-1361
private RBM.Ind.QBudgetAInst.hL0  1363-1364
private RBM.Ind.QBudgetAInst.hm0  1366-1366
RBM.Ind.QBudgetAInst.budgetAltQN_instance  1426-1455
RBM.Ind.QBudgetAInst.budgetAltQNg_instance  1461-1491
### RBM3D.Induction.QBudgetB  (54 unreached of 81)
RBM.Ind.altBudgetNumQNg_band  156-158
RBM.Ind.dDriftAltQN_eq_lin  328-336
private RBM.Ind.QBudgetBInst.rpow_pow5  1083-1084
private RBM.Ind.QBudgetBInst.sz0_facts  1086-1092
private RBM.Ind.QBudgetBInst.lam_pos_n  1094-1096
private RBM.Ind.QBudgetBInst.lam_le_one  1098-1102
private RBM.Ind.QBudgetBInst.numeric  1104-1130
private RBM.Ind.QBudgetBInst.Cmol3  1132-1133
private RBM.Ind.QBudgetBInst.zero_mem_inst  1135-1147
private RBM.Ind.QBudgetBInst.H0  1149-1149
private RBM.Ind.QBudgetBInst.hx4  1151-1151
private RBM.Ind.QBudgetBInst.W4  1153-1154
private RBM.Ind.QBudgetBInst.N4  1156-1158
private RBM.Ind.QBudgetBInst.W10_4  1160-1163
private RBM.Ind.QBudgetBInst.sqrt10_pow6  1165-1167
private RBM.Ind.QBudgetBInst.σalt  1169-1170
private RBM.Ind.QBudgetBInst.σalt_last  1172-1172
private RBM.Ind.QBudgetBInst.hFv4  1174-1177
private RBM.Ind.QBudgetBInst.hMΛ4  1179-1182
private RBM.Ind.QBudgetBInst.hNu4  1184-1185
private RBM.Ind.QBudgetBInst.zero_mem_lin  1187-1191
private RBM.Ind.QBudgetBInst.hY4  1193-1201
RBM.Ind.QBudgetBInst.dFlowQN_levelLin_instance  1203-1219
RBM.Ind.QBudgetBInst.alt_hdriftLinQN_instance  1221-1259
RBM.Ind.QBudgetBInst.dDriftAltLinQN_nonneg_instance  1261-1266
RBM.Ind.QBudgetBInst.dDriftAltQN_eq_lin_instance  1268-1273
private RBM.Ind.QBudgetBInst.Ez  1282-1282
private RBM.Ind.QBudgetBInst.Ez_lt  1284-1284
private RBM.Ind.QBudgetBInst.mE_im_one  1286-1290
private RBM.Ind.QBudgetBInst.hm_Ez  1292-1292
private RBM.Ind.QBudgetBInst.hY4g  1294-1299
private RBM.Ind.QBudgetBInst.thetaKer_rows  1301-1309
private RBM.Ind.QBudgetBInst.thetaKer_cols  1311-1320
RBM.Ind.QBudgetBInst.dFlowQNg_levelLin_instance  1323-1342
RBM.Ind.QBudgetBInst.alt_hdriftLinQNg_instance  1345-1394
RBM.Ind.QBudgetBInst.dDriftAltLinQNg_nonneg_instance  1396-1402
private RBM.Ind.QBudgetBInst.im_ge  1406-1410
private RBM.Ind.QBudgetBInst.C4i  1412-1412
private RBM.Ind.QBudgetBInst.Cni  1413-1413
private RBM.Ind.QBudgetBInst.εi  1414-1414
private RBM.Ind.QBudgetBInst.ε'i  1415-1415
private RBM.Ind.QBudgetBInst.D'i  1416-1416
private RBM.Ind.QBudgetBInst.D''i  1417-1417
private RBM.Ind.QBudgetBInst.C4i_pos  1419-1420
private RBM.Ind.QBudgetBInst.Cni_pos  1422-1423
private RBM.Ind.QBudgetBInst.εi_pos  1425-1425
private RBM.Ind.QBudgetBInst.εi_le  1427-1427
private RBM.Ind.QBudgetBInst.C4εi_le  1429-1436
private RBM.Ind.QBudgetBInst.Cnεi_le  1438-1445
private RBM.Ind.QBudgetBInst.ε'i_nonneg  1447-1447
private RBM.Ind.QBudgetBInst.Cnε'i_le  1449-1454
RBM.Ind.QBudgetBInst.altBudgetExpQN_of_choice_instance  1456-1467
RBM.Ind.QBudgetBInst.altBudgetNumQN_eventually_instance  1469-1478
RBM.Ind.QBudgetBInst.altBudgetNumQNg_eventually_instance  1481-1490
### RBM3D.Induction.QDriftA  (83 unreached of 117)
RBM.Ind.qDriftA_kappaAltQNg_band  158-159
RBM.Ind.qDriftA_epsAltQNg_band  161-162
RBM.Ind.aTrueQN_sumZero  314-323
private RBM.Ind.QDriftA_meas_STLIM  810-814
private RBM.Ind.QDriftA_meas_STLKIM  816-819
private RBM.Ind.QDriftA_meas_loopFine  821-825
private RBM.Ind.QDriftA_meas_STLKM  827-830
private RBM.Ind.QDriftA_meas_STksimLKM  832-842
private RBM.Ind.QDriftA_meas_STelklkM  844-850
private RBM.Ind.QDriftA_meas_STavgErrM  852-856
private RBM.Ind.QDriftA_meas_STegtM  858-864
private RBM.Ind.QDriftA_meas_Psum  866-870
private RBM.Ind.QDriftA_meas_Qop  872-876
private RBM.Ind.QDriftA_meas_ThetaN  878-883
RBM.Ind.measurable_altB4N  885-903
RBM.Ind.measurable_altB5N  905-913
RBM.Ind.measurable_STQopDriftN  915-927
RBM.Ind.measurable_dFlowQN  929-937
RBM.Ind.QDriftAInst.ω0  955-956
RBM.Ind.QDriftAInst.H1  958-959
RBM.Ind.QDriftAInst.H1_hermitian  961-961
RBM.Ind.QDriftAInst.H1_ne_zero  963-965
RBM.Ind.QDriftAInst.dGridQN_eq_dFlowQN_instance  967-971
RBM.Ind.QDriftAInst.dFlowQN_sumZero_instance  973-990
RBM.Ind.QDriftAInst.aTrueQN_sumZero_instance  992-995
RBM.Ind.QDriftAInst.measurable_instance  997-1010
private RBM.Ind.QDriftAInst.rpow_pow5  1017-1018
private RBM.Ind.QDriftAInst.mE_zero_im  1020-1024
private RBM.Ind.QDriftAInst.mE_zero_im_ge  1026-1027
private RBM.Ind.QDriftAInst.etaT_zero_zero  1029-1032
private RBM.Ind.QDriftAInst.etaT_zero_half  1034-1037
private RBM.Ind.QDriftAInst.sz0_facts  1039-1045
private RBM.Ind.QDriftAInst.lam_pos_n  1047-1049
private RBM.Ind.QDriftAInst.lam_le_one  1051-1055
private RBM.Ind.QDriftAInst.L_ge_four  1057-1060
private RBM.Ind.QDriftAInst.numeric  1062-1099
private RBM.Ind.QDriftAInst.ellT_zero_eq  1101-1105
private RBM.Ind.QDriftAInst.ellT_sz0  1107-1108
private RBM.Ind.QDriftAInst.zdist_far  1110-1119
private RBM.Ind.QDriftAInst.farv  1121-1122
private RBM.Ind.QDriftAInst.zdistD_farv  1124-1126
private RBM.Ind.QDriftAInst.zdistInf_farv  1128-1131
private RBM.Ind.QDriftAInst.farb  1133-1134
private RBM.Ind.QDriftAInst.window_l1  1136-1145
private RBM.Ind.QDriftAInst.window_linf  1147-1159
private RBM.Ind.QDriftAInst.diam_zero  1161-1164
private RBM.Ind.QDriftAInst.W_rpow_fifth  1166-1170
RBM.Ind.QDriftAInst.deltaVec  1172-1173
RBM.Ind.QDriftAInst.deltaVec_ne  1175-1178
private RBM.Ind.QDriftAInst.deltaVec_norm  1180-1182
private RBM.Ind.QDriftAInst.deltaVec_zero_of_window  1184-1191
private RBM.Ind.QDriftAInst.Cmol3  1193-1194
RBM.Ind.QDriftAInst.Qop_fastDecay_instance  1196-1241
RBM.Ind.QDriftAInst.fastDecay_of_diamInf_instance  1243-1268
private RBM.Ind.QDriftAInst.ev  1272-1273
private RBM.Ind.QDriftAInst.zdist_one  1275-1282
private RBM.Ind.QDriftAInst.ev_ne  1284-1291
private RBM.Ind.QDriftAInst.zdistInf_ev_le  1293-1294
private RBM.Ind.QDriftAInst.zdistInf_neg_ev_le  1296-1299
private RBM.Ind.QDriftAInst.b2  1301-1302
private RBM.Ind.QDriftAInst.b2_ne  1304-1308
private RBM.Ind.QDriftAInst.b2_zero  1310-1310
private RBM.Ind.QDriftAInst.diam_b2_le  1312-1318
RBM.Ind.QDriftAInst.Xsz  1320-1323
RBM.Ind.QDriftAInst.Xsz_sumZero  1325-1331
RBM.Ind.QDriftAInst.Xsz_ne  1333-1337
private RBM.Ind.QDriftAInst.Xsz_norm  1339-1346
private RBM.Ind.QDriftAInst.Xsz_small  1348-1354
private RBM.Ind.QDriftAInst.Xsz_cls  1356-1369
RBM.Ind.QDriftAInst.hker_altQN_instance  1371-1407
RBM.Ind.QDriftAInst.alt_hkerQN_instance  1409-1439
RBM.Ind.QDriftAInst.sigma_alt_and_nonalt  1441-1446
private RBM.Ind.QDriftAInst.zero_mem_inst  1452-1464
private RBM.Ind.QDriftAInst.crude_sup  1466-1511
RBM.Ind.QDriftAInst.goodSetN_A0clsQN_instance  1513-1571
RBM.Ind.QDriftAInst.alt_hA0clsQN_instance  1573-1637
RBM.Ind.QDriftAInst.dGridQNg_eq_dFlowQNg_instance  1644-1648
RBM.Ind.QDriftAInst.dFlowQNg_sumZero_instance  1650-1665
RBM.Ind.QDriftAInst.fastDecay_of_diamInfg_instance  1667-1690
RBM.Ind.QDriftAInst.hker_altQNg_instance  1692-1728
RBM.Ind.QDriftAInst.alt_hkerQNg_instance  1730-1760
RBM.Ind.QDriftAInst.goodSetNg_A0clsQNg_instance  1762-1819
RBM.Ind.QDriftAInst.alt_hA0clsQNg_instance  1821-1887
### RBM3D.Induction.QDriftB  (41 unreached of 59)
RBM.Ind.qDriftB_thDecay_band_concl  789-793
private RBM.Ind.QDriftBInst.rpow_pow5  974-975
private RBM.Ind.QDriftBInst.mE_zero_im  977-981
private RBM.Ind.QDriftBInst.etaT_zero_zero  983-986
private RBM.Ind.QDriftBInst.etaT_zero_half  988-991
private RBM.Ind.QDriftBInst.sz0_facts  993-999
private RBM.Ind.QDriftBInst.lam_pos_n  1001-1003
private RBM.Ind.QDriftBInst.lam_le_one  1005-1009
private RBM.Ind.QDriftBInst.L_ge_four  1011-1014
private RBM.Ind.QDriftBInst.numeric  1016-1053
private RBM.Ind.QDriftBInst.ellT_zero_eq  1055-1059
private RBM.Ind.QDriftBInst.ellT_sz0  1061-1062
private RBM.Ind.QDriftBInst.zdist_far  1064-1073
private RBM.Ind.QDriftBInst.farv  1075-1076
private RBM.Ind.QDriftBInst.zdistD_farv  1078-1080
private RBM.Ind.QDriftBInst.zdistInf_farv  1082-1085
private RBM.Ind.QDriftBInst.farb  1087-1088
private RBM.Ind.QDriftBInst.window_l1  1090-1099
private RBM.Ind.QDriftBInst.window_linf  1101-1113
private RBM.Ind.QDriftBInst.W_rpow_fifth  1115-1119
private RBM.Ind.QDriftBInst.Cmol3  1122-1123
private RBM.Ind.QDriftBInst.zero_mem_inst  1125-1137
private RBM.Ind.QDriftBInst.crude_sup  1139-1184
private RBM.Ind.QDriftBInst.ellT_eq_one  1186-1198
private RBM.Ind.QDriftBInst.crude_block  1200-1239
private RBM.Ind.QDriftBInst.inst_data  1241-1258
private RBM.Ind.QDriftBInst.x_le_W  1260-1264
private RBM.Ind.QDriftBInst.hDD_inst  1266-1276
RBM.Ind.QDriftBInst.drift13_fastDecay_instance  1280-1299
RBM.Ind.QDriftBInst.altB4N_fastDecay_instance  1301-1324
RBM.Ind.QDriftBInst.altB5N_fastDecay_moll_instance  1326-1344
RBM.Ind.QDriftBInst.dFlowQN_clsQN_instance  1346-1394
RBM.Ind.QDriftBInst.alt_hDclsQN_instance  1396-1468
private RBM.Ind.QDriftBInst.hcmp_inst  1475-1476
private RBM.Ind.QDriftBInst.zero_memg_inst  1478-1481
RBM.Ind.QDriftBInst.drift13_fastDecayg_instance  1483-1501
RBM.Ind.QDriftBInst.altB4Ng_fastDecay_instance  1503-1526
RBM.Ind.QDriftBInst.altB5Ng_fastDecay_moll_instance  1528-1546
RBM.Ind.QDriftBInst.dFlowQNg_clsQNg_instance  1548-1595
RBM.Ind.QDriftBInst.alt_hDclsQNg_instance  1597-1668
RBM.Ind.QDriftBInst.qDriftB_thDecay_band_concl_instance  1670-1673
### RBM3D.Induction.QEndA  (5 unreached of 61)
RBM.Ind.gridDriftQN_envelope  252-317
RBM.Ind.altEnd_crudeSup  841-856
RBM.Ind.altEnd_yMomentsMax  997-1022
RBM.Ind.altYSetNg_band  1048-1049
RBM.Ind.altExitTauNg_band  1051-1053
### RBM3D.Induction.QEndA2  (102 unreached of 102)
private RBM.Ind.altEnd_gridStep_nonneg  31-33
private RBM.Ind.altEnd_gridTime_nonneg  35-40
private RBM.Ind.altEnd_gridTime_le  42-45
private RBM.Ind.QEndAInst.rpow_pow5  60-61
private RBM.Ind.QEndAInst.mE_zero_im  63-67
private RBM.Ind.QEndAInst.etaT_zero_half  69-72
private RBM.Ind.QEndAInst.sz0_facts  74-80
private RBM.Ind.QEndAInst.lam_pos_n  82-84
private RBM.Ind.QEndAInst.lam_le_one  86-90
private RBM.Ind.QEndAInst.L_ge_four  92-95
private RBM.Ind.QEndAInst.numeric  97-134
private RBM.Ind.QEndAInst.Cmol3  136-137
private RBM.Ind.QEndAInst.zero_mem_inst  139-151
private RBM.Ind.QEndAInst.x_le_W  153-157
private RBM.Ind.QEndAInst.hDD_inst  159-169
private RBM.Ind.QEndAInst.inst_data2  171-186
private RBM.Ind.QEndAInst.crude_u  188-236
private RBM.Ind.QEndAInst.zero_lt_exitTau  238-250
private RBM.Ind.QEndAInst.H0  254-254
private RBM.Ind.QEndAInst.hx4  256-256
private RBM.Ind.QEndAInst.W4  258-259
private RBM.Ind.QEndAInst.N4  261-263
private RBM.Ind.QEndAInst.W10_4  265-268
private RBM.Ind.QEndAInst.sqrt10_pow6  270-272
private RBM.Ind.QEndAInst.σalt  274-275
private RBM.Ind.QEndAInst.σalt_last  277-277
private RBM.Ind.QEndAInst.hFv4  279-282
private RBM.Ind.QEndAInst.hMΛ4  284-287
private RBM.Ind.QEndAInst.hNu4  289-290
private RBM.Ind.QEndAInst.zero_mem_lin  292-296
private RBM.Ind.QEndAInst.Φ2v  298-299
private RBM.Ind.QEndAInst.zero_mem_G0  301-310
private RBM.Ind.QEndAInst.hY4  312-320
private RBM.Ind.QEndAInst.altEnd_one_le_size  331-332
private RBM.Ind.QEndAInst.altEnd_size_cast  335-341
private RBM.Ind.QEndAInst.altEnd_W_le_size  343-350
private RBM.Ind.QEndAInst.altEnd_step_le  352-366
private RBM.Ind.QEndAInst.altEnd_gridTime_succ_sub  368-371
private RBM.Ind.QEndAInst.altEnd_eeShiftErrN_le  373-393
private RBM.Ind.QEndAInst.altEnd_shift_fixed  396-484
RBM.Ind.QEndAInst.altYSetN_instance  490-496
RBM.Ind.QEndAInst.altYGridN_instance  498-518
private RBM.Ind.QEndAInst.T2294_altYGridN  520-530
private RBM.Ind.QEndAInst.sg0  537-537
private RBM.Ind.QEndAInst.vg2  539-539
RBM.Ind.QEndAInst.gridDriftQN_envelope_instance  541-557
private RBM.Ind.QEndAInst.σalt0  559-560
RBM.Ind.QEndAInst.gridDriftQN_envelope'_instance  562-578
private RBM.Ind.QEndAInst.kapI  580-582
private RBM.Ind.QEndAInst.epsI  584-586
RBM.Ind.QEndAInst.assembledRHSAltQN_qErr_le_instance  588-612
private RBM.Ind.QEndAInst.Cm2  616-617
private RBM.Ind.QEndAInst.Bctl_le_four  619-643
private RBM.Ind.QEndAInst.etaT_zero  645-647
private RBM.Ind.QEndAInst.hwL_gen  649-658
private RBM.Ind.QEndAInst.hWt_gen  660-664
RBM.Ind.QEndAInst.hQ_altQN_subGaussStop_altQN_instance  666-795
RBM.Ind.QEndAInst.alt_hkerGridQN_instance  799-818
RBM.Ind.QEndAInst.alt_hdriftGridQN_instance  820-845
RBM.Ind.QEndAInst.alt_hA0clsGridQN_instance  847-883
RBM.Ind.QEndAInst.alt_hDclsGridQN_instance  885-959
RBM.Ind.QEndAInst.altExitMeasN_instance  963-968
RBM.Ind.QEndAInst.altEnd_hexp_instance  970-993
RBM.Ind.QEndAInst.altEnd_stronglyMeasurable_zVecQN_instance  995-999
RBM.Ind.QEndAInst.altEnd_aFroz_eq_aTrue_instance  1001-1009
RBM.Ind.QEndAInst.altEnd_unQ_instance  1011-1025
RBM.Ind.QEndAInst.altEnd_yMomentsMax_instance  1027-1042
private RBM.Ind.QEndAInst.Ez  1052-1052
private RBM.Ind.QEndAInst.CmZ  1054-1054
private RBM.Ind.QEndAInst.Ez_lt  1056-1056
private RBM.Ind.QEndAInst.hLZ  1058-1058
private RBM.Ind.QEndAInst.hWZ  1060-1060
private RBM.Ind.QEndAInst.hmZ  1062-1062
private RBM.Ind.QEndAInst.hSZ  1064-1065
private RBM.Ind.QEndAInst.hRowZ  1067-1067
private RBM.Ind.QEndAInst.hQVZ  1069-1069
private RBM.Ind.QEndAInst.hR1Z  1071-1072
private RBM.Ind.QEndAInst.hηZ  1074-1075
private RBM.Ind.QEndAInst.mE_im_one  1077-1081
private RBM.Ind.QEndAInst.hY4g  1083-1087
RBM.Ind.QEndAInst.altYSetNg_instance  1089-1094
RBM.Ind.QEndAInst.altYGridNg_instance  1096-1114
RBM.Ind.QEndAInst.gridDriftQNg_envelope_ev_instance  1116-1129
private RBM.Ind.QEndAInst.kapZ  1131-1134
private RBM.Ind.QEndAInst.epsZ  1136-1138
RBM.Ind.QEndAInst.assembledRHSAltQNg_qErr_le_instance  1140-1170
RBM.Ind.QEndAInst.hQ_altQNg_subGaussStop_altQNg_instance  1173-1313
private RBM.Ind.QEndAInst.thetaKerZ_cols  1317-1327
private RBM.Ind.QEndAInst.thetaKerZ_rows  1329-1338
private RBM.Ind.QEndAInst.hκmZ  1340-1343
private RBM.Ind.QEndAInst.zero_mem_GZ  1345-1352
private RBM.Ind.QEndAInst.crude_uZ  1354-1364
RBM.Ind.QEndAInst.alt_hkerGridQNg_instance  1366-1387
RBM.Ind.QEndAInst.alt_hdriftGridQNg_instance  1391-1423
RBM.Ind.QEndAInst.alt_hA0clsGridQNg_instance  1425-1466
RBM.Ind.QEndAInst.alt_hDclsGridQNg_instance  1469-1550
RBM.Ind.QEndAInst.altExitMeasNg_instance  1552-1557
RBM.Ind.QEndAInst.altEnd_hexpg_instance  1559-1580
RBM.Ind.QEndAInst.altEnd_stronglyMeasurable_zVecQNg_instance  1582-1586
RBM.Ind.QEndAInst.altEnd_aFroz_eq_aTrueg_instance  1588-1595
RBM.Ind.QEndAInst.altEnd_unQg_instance  1598-1614
RBM.Ind.QEndAInst.altEnd_driftSupg_instance  1616-1635
### RBM3D.Induction.QEndB1  (8 unreached of 48)
RBM.Gauss.Sizes.STOeqQtRoundPT'  116-118
private RBM.Ind.altQFlow_Ylow_le_bootRHS  445-460
private RBM.Ind.altQFlow_initQ  532-711
private RBM.Ind.altQFlow_core  725-910
private RBM.Ind.altQFlow_section  1003-1191
RBM.Ind.stOeqQtRoundPT'_holds  1780-1835
RBM.Ind.QEndB1Inst.inst_OeqQtRoundPT'  1901-1908
RBM.Ind.QEndB1Inst.inst_OeqQtRoundPT''  1971-1978
### RBM3D.Induction.QEndGrid  (41 unreached of 92)
private RBM.Ind.altGrid_assembly  825-1106
private RBM.Ind.altGrid_arith  1510-1591
RBM.Ind.altGridEndQN  1700-2170
RBM.Ind.QEndGridInst.agE  2664-2665
RBM.Ind.QEndGridInst.agS  2666-2667
RBM.Ind.QEndGridInst.agT  2668-2669
RBM.Ind.QEndGridInst.agV  2670-2671
RBM.Ind.QEndGridInst.agC  2672-2673
RBM.Ind.QEndGridInst.agOne  2674-2675
private RBM.Ind.QEndGridInst.sz0_facts  2677-2682
private RBM.Ind.QEndGridInst.sz0_lam_pos  2684-2686
private RBM.Ind.QEndGridInst.sz0_lam_le_one  2688-2691
private RBM.Ind.QEndGridInst.sz0_L_ge_four  2693-2695
RBM.Ind.QEndGridInst.agCaseI  2697-2706
RBM.Ind.QEndGridInst.agE_abs  2708-2708
RBM.Ind.QEndGridInst.agWt  2710-2716
RBM.Ind.QEndGridInst.agS_nonneg  2718-2718
RBM.Ind.QEndGridInst.agS_le_agT  2719-2719
RBM.Ind.QEndGridInst.agT_lt_one  2720-2720
RBM.Ind.QEndGridInst.agS_le_agV  2721-2721
RBM.Ind.QEndGridInst.agV_le_agT  2722-2722
RBM.Ind.QEndGridInst.agS_le_agC  2723-2723
RBM.Ind.QEndGridInst.agC_le_agT  2724-2724
RBM.Ind.QEndGridInst.agK  2726-2727
RBM.Ind.QEndGridInst.agK_ne_zero  2729-2731
RBM.Ind.QEndGridInst.agK_low  2733-2736
RBM.Ind.QEndGridInst.agK_up  2738-2742
RBM.Ind.QEndGridInst.window_nondegenerate  2744-2749
RBM.Ind.QEndGridInst.window_collapsed  2751-2755
private RBM.Ind.QEndGridInst.T2302_altGridEndQN  2759-2794
RBM.Ind.QEndGridInst.altGrid_instance  2802-2839
RBM.Ind.QEndGridInst.altGrid_instance'  2841-2876
RBM.Ind.QEndGridInst.altGrid_instance_collapsed  2886-2919
RBM.Ind.QEndGridInst.lam_patch_instance  2936-2942
RBM.Ind.QEndGridInst.lam_patch_values  2944-2964
private RBM.Ind.QEndGridInst.N4  2968-2970
private RBM.Ind.QEndGridInst.mE_zero_im  2972-2976
private RBM.Ind.QEndGridInst.etaT_zero_half  2978-2981
RBM.Ind.QEndGridInst.levels_small_instance  2983-3006
RBM.Ind.QEndGridInst.levels_big_instance  3008-3014
RBM.Ind.QEndGridInst.levels_crude_instance  3016-3033
### RBM3D.Induction.QGridA  (7 unreached of 122)
RBM.Ind.QGridACheck.sigma4  2234-2235
RBM.Ind.QGridACheck.sigma4_alternating  2237-2240
RBM.Ind.QGridACheck.moll  2242-2244
RBM.Ind.QGridACheck.lam_pos  2246-2246
RBM.Ind.QGridACheck.gridDriftQN_instance  2248-2268
RBM.Ind.QGridACheck.stoppedDuhamelQN_instance  2270-2284
RBM.Ind.QGridACheck.taylor2_instance  2286-2289
### RBM3D.Induction.QGridB  (4 unreached of 21)
RBM.Ind.QGridBCheck.Kc31  697-698
RBM.Ind.QGridBCheck.Kc31_ne_zero  700-705
RBM.Ind.QGridBCheck.rpow_31_le_Kc31  707-711
RBM.Ind.QGridBCheck.sum_weighted_qErrQN_instance  713-733
### RBM3D.Induction.QLevelsA  (34 unreached of 49)
RBM.Ind.crudeLKM_of_level  600-609
private RBM.Ind.QLevelsAInst.H0  625-626
private RBM.Ind.QLevelsAInst.W0  628-628
private RBM.Ind.QLevelsAInst.N0  629-629
private RBM.Ind.QLevelsAInst.lam0  630-630
private RBM.Ind.QLevelsAInst.L0r  631-631
private RBM.Ind.QLevelsAInst.lam_pos0  633-633
private RBM.Ind.QLevelsAInst.ellT0  635-638
private RBM.Ind.QLevelsAInst.W15  640-642
private RBM.Ind.QLevelsAInst.Wneg36  644-645
private RBM.Ind.QLevelsAInst.Bctl0  647-654
private RBM.Ind.QLevelsAInst.zero_mem0  656-662
private RBM.Ind.QLevelsAInst.norm_STLKM_le_of_XiLKM  664-677
private RBM.Ind.QLevelsAInst.farv  679-680
private RBM.Ind.QLevelsAInst.zdist_far0  682-688
private RBM.Ind.QLevelsAInst.window0  690-709
private RBM.Ind.QLevelsAInst.hY0  711-720
private RBM.Ind.QLevelsAInst.hF0  722-731
private RBM.Ind.QLevelsAInst.hYtop0  733-735
private RBM.Ind.QLevelsAInst.moll_sup  737-755
private RBM.Ind.QLevelsAInst.moll_deriv  757-761
private RBM.Ind.QLevelsAInst.hNu0  763-764
private RBM.Ind.QLevelsAInst.hMΛ0  766-769
private RBM.Ind.QLevelsAInst.hFv0'  771-773
RBM.Ind.QLevelsAInst.altB45N_levelM_instance  775-792
RBM.Ind.QLevelsAInst.startLevelQN_instance  794-807
RBM.Ind.QLevelsAInst.crudeLKM_of_level_instance  809-822
private RBM.Ind.QLevelsAInst.Ez  829-829
private RBM.Ind.QLevelsAInst.Ez_lt  831-831
private RBM.Ind.QLevelsAInst.mE_im_one  833-837
private RBM.Ind.QLevelsAInst.thetaKer_rows  839-847
private RBM.Ind.QLevelsAInst.thetaKer_cols  849-858
RBM.Ind.QLevelsAInst.altB45Ng_levelM_instance  861-886
RBM.Ind.QLevelsAInst.startLevelQNg_instance  889-908
### RBM3D.Induction.QLevelsB  (46 unreached of 48)
RBM.Ind.dDriftAltQN  54-60
private RBM.Ind.QLevelsB_norm_STLKM_le_of_XiLKM  64-78
private RBM.Ind.QLevelsB_STmaxLKM_nonneg  80-86
RBM.Ind.goodSetN_LKM_le  88-108
RBM.Ind.qopB13N_levelM  142-182
RBM.Ind.dFlowQN_levelM  186-255
RBM.Ind.alt_hdriftQN  259-300
RBM.Ind.dDriftAltQN_nonneg  304-323
private RBM.Ind.QLevelsBInst.rpow_pow5  341-342
private RBM.Ind.QLevelsBInst.sz0_facts  344-350
private RBM.Ind.QLevelsBInst.lam_pos_n  352-354
private RBM.Ind.QLevelsBInst.lam_le_one  356-360
private RBM.Ind.QLevelsBInst.numeric  362-388
private RBM.Ind.QLevelsBInst.W_rpow_fifth  390-393
private RBM.Ind.QLevelsBInst.ellT_zero_eq  395-399
private RBM.Ind.QLevelsBInst.ellT_sz0  401-402
private RBM.Ind.QLevelsBInst.zdist_far  404-413
private RBM.Ind.QLevelsBInst.farv  415-415
private RBM.Ind.QLevelsBInst.zdistInf_farv  417-420
private RBM.Ind.QLevelsBInst.farb  422-422
private RBM.Ind.QLevelsBInst.window_linf  424-436
private RBM.Ind.QLevelsBInst.Cmol3  438-439
private RBM.Ind.QLevelsBInst.zero_mem_inst  441-453
private RBM.Ind.QLevelsBInst.H0  455-455
private RBM.Ind.QLevelsBInst.hx4  457-457
private RBM.Ind.QLevelsBInst.W4  459-460
private RBM.Ind.QLevelsBInst.L4  462-463
private RBM.Ind.QLevelsBInst.N4  465-467
private RBM.Ind.QLevelsBInst.W5_4  469-470
private RBM.Ind.QLevelsBInst.W10_4  472-475
private RBM.Ind.QLevelsBInst.sqrt10_pow6  477-479
private RBM.Ind.QLevelsBInst.sqrt10_le  481-482
private RBM.Ind.QLevelsBInst.lam4  484-485
private RBM.Ind.QLevelsBInst.window4  487-492
private RBM.Ind.QLevelsBInst.σalt  494-495
private RBM.Ind.QLevelsBInst.σalt_last  497-497
RBM.Ind.QLevelsBInst.goodSetN_LKM_le_instance  499-504
RBM.Ind.QLevelsBInst.goodSetN_LKM_far_instance  506-516
RBM.Ind.QLevelsBInst.goodSetNg_LKM_far_instance  518-529
RBM.Ind.QLevelsBInst.qopB13N_levelM_instance  532-547
private RBM.Ind.QLevelsBInst.hFv4  549-552
private RBM.Ind.QLevelsBInst.hMΛ4  554-557
private RBM.Ind.QLevelsBInst.hNu4  559-560
RBM.Ind.QLevelsBInst.dFlowQN_levelM_instance  562-576
RBM.Ind.QLevelsBInst.alt_hdriftQN_instance  578-605
RBM.Ind.QLevelsBInst.dDriftAltQN_nonneg_instance  607-612
### RBM3D.Induction.QProxy  (5 unreached of 64)
private RBM.Ind.qProxy4C_spec  657-674
private RBM.Ind.QProxyG_flow_im  710-712
private RBM.Ind.QProxyG_flow_E  714-716
RBM.Ind.qProxyG_kerEK4_band  718-727
RBM.Ind.qvFormQN_le_of_goodSetN  1296-1334
### RBM3D.Induction.QProxy2  (74 unreached of 74)
RBM.Ind.QProxyInst.qProxyG_kerEK4_band_instance  42-47
RBM.Ind.QProxyInst.martIncQNg_ae_eq_instance  49-55
RBM.Ind.QProxyInst.martIncQN_ae_eq_instance  59-62
RBM.Ind.QProxyInst.Mx  66-69
RBM.Ind.QProxyInst.qv_at_propagatorQg_instance  71-83
RBM.Ind.QProxyInst.deltaTensor  88-90
RBM.Ind.QProxyInst.Adelta  92-93
RBM.Ind.QProxyInst.Adelta_ne  95-98
RBM.Ind.QProxyInst.Adelta_not_sumZero  100-105
RBM.Ind.QProxyInst.qqTensorN_sumZero_instance  107-111
private RBM.Ind.QProxyInst.hL_Ei  113-114
private RBM.Ind.QProxyInst.hW_Ei  116-117
private RBM.Ind.QProxyInst.hQV_Ei  119-120
private RBM.Ind.QProxyInst.hKer_Ei  122-123
RBM.Ind.QProxyInst.azumaSubGQ_ugenNg_instance  127-144
RBM.Ind.QProxyInst.azumaSubGQ_gridExitNg_instance_zero  146-160
RBM.Ind.QProxyInst.azumaSubGQ_gridExitN_instance  162-176
RBM.Ind.QProxyInst.azumaSubGQ_gridExitN_instance_zero  178-193
private RBM.Ind.QProxyInst.rangeCond_vg  197-209
private RBM.Ind.QProxyInst.Kg_ne_zero  211-211
private RBM.Ind.QProxyInst.gridStep_pos  213-215
private RBM.Ind.QProxyInst.lam_pos_n  217-219
RBM.Ind.QProxyInst.yMomentsQUnifNg_instance_pos  220-237
RBM.Ind.QProxyInst.yMomentsQUnifN_instance  241-256
private RBM.Ind.QProxyInst.rpow_pow5  262-263
private RBM.Ind.QProxyInst.mE_zero_im  265-269
private RBM.Ind.QProxyInst.mE_zero_im_ge  271-272
private RBM.Ind.QProxyInst.etaT_zero_zero  274-277
private RBM.Ind.QProxyInst.diam_append_zero  279-288
private RBM.Ind.QProxyInst.e5  292-293
RBM.Ind.QProxyInst.w5  295-297
private RBM.Ind.QProxyInst.zero_ne_e5  299-303
private RBM.Ind.QProxyInst.b1_ne_b2  305-307
private RBM.Ind.QProxyInst.zdistD_e5  309-313
RBM.Ind.QProxyInst.w5_sumZero  315-321
private RBM.Ind.QProxyInst.w5_b1  323-325
RBM.Ind.QProxyInst.w5_ne  327-331
private RBM.Ind.QProxyInst.w5_norm  333-343
private RBM.Ind.QProxyInst.w5_small  345-363
RBM.Ind.QProxyInst.T5  365-366
RBM.Ind.QProxyInst.T5_ne  368-372
private RBM.Ind.QProxyInst.rpow25  374-376
private RBM.Ind.QProxyInst.ellT_five_le  378-383
private RBM.Ind.QProxyInst.zdistD_222  385-389
private RBM.Ind.QProxyInst.window_five  391-401
RBM.Ind.QProxyInst.szQP  402-408
RBM.Ind.QProxyInst.ugenPairQNg_le_of_bounds_instance  410-475
private RBM.Ind.QProxyInst.sz0_facts  484-490
private RBM.Ind.QProxyInst.lam_le_one  492-496
private RBM.Ind.QProxyInst.ellT_zero_eq  498-502
private RBM.Ind.QProxyInst.ellT_sz0  504-505
private RBM.Ind.QProxyInst.zdist_far  507-516
private RBM.Ind.QProxyInst.farv  518-519
private RBM.Ind.QProxyInst.zdistD_farv  521-523
private RBM.Ind.QProxyInst.zdistInf_farv  525-528
private RBM.Ind.QProxyInst.farb  530-531
private RBM.Ind.QProxyInst.window_l1  533-542
private RBM.Ind.QProxyInst.window_linf  544-560
private RBM.Ind.QProxyInst.Bctl_zero_le  562-579
private RBM.Ind.QProxyInst.Cmol3  581-582
private RBM.Ind.QProxyInst.Cn3  584-585
private RBM.Ind.QProxyInst.CQ3  586-586
private RBM.Ind.QProxyInst.Dq  588-589
private RBM.Ind.QProxyInst.R0  591-592
private RBM.Ind.QProxyInst.sz0_numeric  594-649
private RBM.Ind.QProxyInst.bdQ  651-661
private RBM.Ind.QProxyInst.hD_inst  663-666
private RBM.Ind.QProxyInst.zero_mem_inst  668-679
private RBM.Ind.QProxyInst.exists_big_n  681-684
private RBM.Ind.QProxyInst.W_rpow_le_x  686-699
RBM.Ind.QProxyInst.qvFormQNg_le_of_bounds_instance  700-724
RBM.Ind.QProxyInst.qvFormQN_le_of_goodSetN_instance  727-749
RBM.Ind.QProxyInst.qvFormQN_le_of_bounds_instance  751-772
RBM.Ind.QProxyInst.qqTensorBoundsN_instance  774-833
### RBM3D.Induction.QVN  (4 unreached of 55)
private RBM.Ind.QVN_cm_apply  116-117
private RBM.Ind.QVN_wd_nil  383-385
RBM.Ind.QVN_check_sz0_one  829-842
RBM.Ind.QVN_check_sz0_two  844-865
### RBM3D.Induction.QopAlgebra  (9 unreached of 58)
RBM.Gauss.Sizes.QopAlgebra_Psum_mollifier  623-626
RBM.Gauss.Sizes.QopAlgebra_Qop_hasDerivAt_const  657-665
private RBM.Gauss.Sizes.qa_col_sum_Theta  687-694
RBM.Gauss.Sizes.QopAlgebra_col_sum_uKer  703-709
private RBM.Gauss.Sizes.qa_sum_fiber0  807-817
RBM.Gauss.Sizes.QopAlgebra_UN_sumZero  819-856
RBM.Gauss.Sizes.QopAlgebra_commutator_UN  883-894
private RBM.Gauss.Sizes.qaTheta  924-925
private RBM.Gauss.Sizes.qaTheta_sum  927-929
### RBM3D.Induction.QopDecay  (8 unreached of 47)
private RBM.Gauss.Sizes.qdec_mollifier_eq  383-385
private RBM.Gauss.Sizes.qdecA  901-902
private RBM.Gauss.Sizes.qdecA_ne  904-907
private RBM.Gauss.Sizes.qdecA_norm_le  909-912
private RBM.Gauss.Sizes.qdecA_fastDecay  914-929
private RBM.Gauss.Sizes.qdec_ellT_le  931-939
private RBM.Gauss.Sizes.qdec_window  941-970
private RBM.Gauss.Sizes.qdecSz  1034-1040
### RBM3D.Induction.QopNorm  (4 unreached of 14)
private RBM.Gauss.Sizes.qnA  467-468
private RBM.Gauss.Sizes.qnA_ne  470-473
private RBM.Gauss.Sizes.qnA_norm_le  475-478
private RBM.Gauss.Sizes.qnA_fastDecay  480-494
### RBM3D.Induction.QtNonzero  (49 unreached of 75)
private RBM.Ind.qtNZ_row_coarse  273-291
private RBM.Ind.qtNZ_scalar  659-684
private RBM.Ind.QtNonzeroInst.qnDelta  1156-1157
private RBM.Ind.QtNonzeroInst.qnDelta_ne  1159-1161
private RBM.Ind.QtNonzeroInst.qnIdiff  1163-1164
private RBM.Ind.QtNonzeroInst.qn_Q_delta_zero'  1166-1179
private RBM.Ind.QtNonzeroInst.qn_Q_delta_zero  1181-1187
RBM.Ind.QtNonzeroInst.idem_instance  1191-1205
private RBM.Ind.QtNonzeroInst.qn_mE0_im  1209-1211
RBM.Ind.QtNonzeroInst.nzUgen_instance  1213-1229
private RBM.Ind.QtNonzeroInst.qnU  1233-1234
private RBM.Ind.QtNonzeroInst.qnU_nonneg  1236-1239
private RBM.Ind.QtNonzeroInst.qnU_lt_one  1241-1244
private RBM.Ind.QtNonzeroInst.qnU_ge  1246-1249
private RBM.Ind.QtNonzeroInst.qnU_mono  1251-1254
RBM.Ind.QtNonzeroInst.nz_hker_instance  1256-1282
RBM.Ind.QtNonzeroInst.nz_hdrift_instance  1286-1299
RBM.Ind.QtNonzeroInst.nz_hdrift_level_pos  1318-1326
private RBM.Ind.QtNonzeroInst.qn_gridTime_nonneg  1330-1333
private RBM.Ind.QtNonzeroInst.qn_gridTime_le  1335-1338
RBM.Ind.QtNonzeroInst.subGaussStop_nz_instance  1340-1368
RBM.Ind.QtNonzeroInst.cQVNZN_inst_pos  1370-1383
private RBM.Ind.QtNonzeroInst.qn_yMoment_zero  1388-1406
RBM.Ind.QtNonzeroInst.yMoment_zero_instance  1408-1420
private RBM.Ind.QtNonzeroInst.qnZ  1430-1431
private RBM.Ind.QtNonzeroInst.qnG  1433-1437
private RBM.Ind.QtNonzeroInst.qnZ_eq  1439-1439
private RBM.Ind.QtNonzeroInst.qnG_meas  1441-1442
private RBM.Ind.QtNonzeroInst.qnG_memLp  1444-1452
private RBM.Ind.QtNonzeroInst.qnZ_memLp  1454-1458
private RBM.Ind.QtNonzeroInst.qnZ_int4  1460-1465
private RBM.Ind.QtNonzeroInst.qnG_integral  1467-1469
private RBM.Ind.QtNonzeroInst.qnZ_integral  1471-1476
private RBM.Ind.QtNonzeroInst.qnZ_condExp  1478-1488
private RBM.Ind.QtNonzeroInst.qnδ  1490-1491
private RBM.Ind.QtNonzeroInst.qnY  1493-1495
private RBM.Ind.QtNonzeroInst.qnY_meas  1497-1500
private RBM.Ind.QtNonzeroInst.qn_Ugen_smul  1502-1508
RBM.Ind.QtNonzeroInst.yMoment_random_instance  1510-1604
private RBM.Ind.QtNonzeroInst.qn_W0  1608-1608
private RBM.Ind.QtNonzeroInst.qn_N0  1610-1610
private RBM.Ind.QtNonzeroInst.qn_two_pow_rpow  1612-1613
private RBM.Ind.QtNonzeroInst.qn_N_rpow  1615-1618
private RBM.Ind.QtNonzeroInst.qn_N_eps1  1620-1623
private RBM.Ind.QtNonzeroInst.qn_N_nine  1625-1626
private RBM.Ind.QtNonzeroInst.qn_im_ge  1628-1632
private RBM.Ind.QtNonzeroInst.qn_Ls_le  1634-1647
private RBM.Ind.QtNonzeroInst.qn_Ls_nonneg  1649-1652
RBM.Ind.QtNonzeroInst.budgetNZN_instance  1654-1700
### RBM3D.Induction.QtNonzeroBoot  (6 unreached of 35)
RBM.Ind.QtNonzeroBootInst.inst_OeqQtNZ'  1089-1097
RBM.Ind.QtNonzeroBootInst.inst_RoundNZ  1099-1105
private RBM.Ind.QtNonzeroBootInst.obsB  1171-1174
private RBM.Ind.QtNonzeroBootInst.obsB_nonneg  1176-1176
private RBM.Ind.QtNonzeroBootInst.obsB_le_one  1178-1179
private RBM.Ind.QtNonzeroBootInst.obsB_nonconst  1181-1184
### RBM3D.Induction.QtNonzeroEnd  (49 unreached of 79)
RBM.Ind.QtNonzeroEndInst.sB  1203-1204
RBM.Ind.QtNonzeroEndInst.tB  1206-1207
RBM.Ind.QtNonzeroEndInst.vB  1209-1210
RBM.Ind.QtNonzeroEndInst.vC  1212-1213
RBM.Ind.QtNonzeroEndInst.oneL  1215-1216
RBM.Ind.QtNonzeroEndInst.κz  1218-1219
RBM.Ind.QtNonzeroEndInst.κz_pos  1221-1221
RBM.Ind.QtNonzeroEndInst.Cz_ex  1223-1232
RBM.Ind.QtNonzeroEndInst.Cz  1234-1235
RBM.Ind.QtNonzeroEndInst.Cz_pos  1237-1237
RBM.Ind.QtNonzeroEndInst.Ddz  1239-1240
RBM.Ind.QtNonzeroEndInst.Ddz_eq  1242-1242
RBM.Ind.QtNonzeroEndInst.hE_B  1244-1244
RBM.Ind.QtNonzeroEndInst.hκm_B  1246-1246
RBM.Ind.QtNonzeroEndInst.hlam_B  1248-1249
RBM.Ind.QtNonzeroEndInst.sB_nonneg  1251-1251
RBM.Ind.QtNonzeroEndInst.sB_le_tB  1253-1253
RBM.Ind.QtNonzeroEndInst.tB_lt_one  1255-1255
RBM.Ind.QtNonzeroEndInst.sB_le_vB  1257-1257
RBM.Ind.QtNonzeroEndInst.vB_le_tB  1259-1259
RBM.Ind.QtNonzeroEndInst.vB_lt_one  1261-1261
RBM.Ind.QtNonzeroEndInst.sB_le_vC  1263-1263
RBM.Ind.QtNonzeroEndInst.vC_le_tB  1265-1265
RBM.Ind.QtNonzeroEndInst.vC_lt_one  1267-1267
RBM.Ind.QtNonzeroEndInst.rangeCond_tB  1269-1283
RBM.Ind.QtNonzeroEndInst.σ3_idiff  1285-1285
RBM.Ind.QtNonzeroEndInst.KB  1289-1291
RBM.Ind.QtNonzeroEndInst.KB_ne_zero  1293-1295
RBM.Ind.QtNonzeroEndInst.KB_low  1297-1300
RBM.Ind.QtNonzeroEndInst.KB_up  1302-1306
RBM.Ind.QtNonzeroEndInst.window_nondegenerate  1308-1314
RBM.Ind.QtNonzeroEndInst.window_collapsed  1316-1320
RBM.Ind.QtNonzeroEndInst.asymp_instance  1324-1331
RBM.Ind.QtNonzeroEndInst.H1_instance  1338-1341
RBM.Ind.QtNonzeroEndInst.H2_instance  1343-1349
RBM.Ind.QtNonzeroEndInst.H3_instance  1351-1357
RBM.Ind.QtNonzeroEndInst.H4_instance  1359-1364
RBM.Ind.QtNonzeroEndInst.H5_instance  1366-1370
RBM.Ind.QtNonzeroEndInst.H6_instance  1372-1376
RBM.Ind.QtNonzeroEndInst.union_instance  1378-1381
RBM.Ind.QtNonzeroEndInst.rangeCond_mono_instance  1383-1386
RBM.Ind.QtNonzeroEndInst.hη_instance  1388-1390
RBM.Ind.QtNonzeroEndInst.hδ_instance  1392-1402
RBM.Ind.QtNonzeroEndInst.grid_instance  1404-1408
RBM.Ind.QtNonzeroEndInst.hop_instance  1410-1427
RBM.Ind.QtNonzeroEndInst.Γz  1436-1437
RBM.Ind.QtNonzeroEndInst.assembly_instance  1439-1484
RBM.Ind.QtNonzeroEndInst.nzEnd_instance  1494-1532
RBM.Ind.QtNonzeroEndInst.nzEnd_instance_collapsed  1534-1567
### RBM3D.Induction.QtNonzeroFlow  (1 unreached of 34)
RBM.Ind.QtNonzeroFlowInst.inst_OeqNZPT''  878-887
### RBM3D.Induction.QtNonzeroFlowLift  (1 unreached of 26)
RBM.Ind.QtNonzeroFlowLiftInst.inst_OeqNZ''  795-804
### RBM3D.Induction.QtXiRoundLift  (3 unreached of 27)
RBM.Ind.QtXiRoundLiftInst.inst_OeqQt'  752-758
RBM.Ind.QtXiRoundLiftInst.inst_RoundQt  760-763
private RBM.Ind.QtXiRoundLiftInst.inst_htN  817-822
### RBM3D.Induction.SEforLn1  (1 unreached of 38)
private RBM.Gauss.Sizes.SEforLn1_norm_ite  494-496
### RBM3D.Induction.ScaleFacts  (21 unreached of 31)
RBM.Ind.closure_sq_le  169-173
RBM.Ind.scaleFacts_ellT_mono_ratio  296-325
RBM.Ind.scaleFacts_ellT_ratio  327-338
RBM.Ind.scaleFacts_ellT_pow_four  346-363
RBM.Ind.ScaleFactsInst.R1_sz0  381-398
RBM.Ind.ScaleFactsInst.R1_sz0_lt_one  400-420
RBM.Ind.ScaleFactsInst.R2_sz0  422-427
RBM.Ind.ScaleFactsInst.R2_pt_sz0  429-435
RBM.Ind.ScaleFactsInst.closure_sz0  437-448
RBM.Ind.ScaleFactsInst.ell_values  450-469
RBM.Ind.ScaleFactsInst.ratio_sz0  471-481
RBM.Ind.ScaleFactsInst.ratio_sz0_sharp  483-489
RBM.Ind.ScaleFactsInst.Bctl_facts_sz0  491-514
RBM.Ind.ScaleFactsInst.xB  526-528
RBM.Ind.ScaleFactsInst.xB_le_fB  530-537
RBM.Ind.ScaleFactsInst.Bctl_eighth_le  539-569
RBM.Ind.ScaleFactsInst.forbidden_region_Bctl_sz0  571-598
RBM.Ind.ScaleFactsNeg.szNoWO  612-618
RBM.Ind.ScaleFactsNeg.szNoWO_size  620-623
RBM.Ind.ScaleFactsNeg.tNoWO  625-626
RBM.Ind.ScaleFactsNeg.scaleFacts_R1_needs_WO  628-697
### RBM3D.Induction.ScaleFacts3  (7 unreached of 27)
RBM.Gauss.Sizes.st_EKWin  464-471
RBM.Gauss.Sizes.st_split_I  496-509
RBM.Gauss.Sizes.st_split_II  511-523
private RBM.Gauss.ScaleFacts3Inst.zB_abs_E  540-540
private RBM.Gauss.ScaleFacts3Inst.szB_conI  542-544
private RBM.Gauss.ScaleFacts3Inst.szB_conII  546-548
private RBM.Gauss.ScaleFacts3Inst.szB_con_wide  617-618
### RBM3D.Induction.SizesComp  (53 unreached of 85)
RBM.Gauss.Sizes.comp_L  62-62
RBM.Gauss.Sizes.comp_W  64-64
RBM.Gauss.Sizes.comp_lam  66-66
RBM.Gauss.Sizes.comp_size  68-68
RBM.Gauss.Sizes.withLam_comp  70-71
RBM.Gauss.Sizes.comp_locDomain  73-74
RBM.Gauss.Sizes.reindex_eq  225-225
RBM.Gauss.Sizes.slice_reindex  273-274
RBM.Gauss.Sizes.seqXmat_reindex  276-277
RBM.Gauss.Sizes.seqHflow_reindex  279-280
RBM.Gauss.Sizes.Gt_reindex  282-283
RBM.Gauss.Sizes.STGM_reindex  289-291
RBM.Gauss.Sizes.STKloop_comp  293-295
RBM.Gauss.Sizes.Bctl_comp  297-297
RBM.Gauss.Sizes.STWB_comp  299-300
RBM.Gauss.Sizes.STblk_comp  302-303
RBM.Gauss.Sizes.ellT_comp  305-307
RBM.Gauss.Sizes.STflowE_comp  309-310
RBM.StochDomAt.of_map  364-376
RBM.Path.PerTimeDomAt.map_iff  404-414
RBM.Path.PerTimeDomAt.subseq  416-421
RBM.Path.PerTimeDomAt.iff_cover  423-431
RBM.Gauss.HighProbAt.map_iff  437-445
RBM.Gauss.HighProbAt.subseq  447-452
RBM.Gauss.HighProbAt.iff_cover  454-461
RBM.Gauss.Sizes.PrecPT_comp_iff  502-508
RBM.Gauss.Sizes.Whp_comp_iff  510-514
RBM.Gauss.Sizes.perTimeDomAt_iff_comp_cover  556-576
RBM.Gauss.Sizes.highProbAt_iff_comp_cover  578-592
RBM.Gauss.Sizes.PrecPT_iff_comp_cover  605-613
RBM.Gauss.Sizes.Whp_iff_comp_cover  615-621
RBM.Gauss.SizesCompInst.two_mul_strictMono  636-638
RBM.Gauss.SizesCompInst.two_mul_tendsto  640-641
RBM.Gauss.SizesCompInst.inst_comp_values  643-649
RBM.Gauss.SizesCompInst.inst_comp_admissible  651-652
RBM.Gauss.SizesCompInst.inst_flow_comp  654-656
RBM.Gauss.SizesCompInst.inst_conStInd_comp  658-661
RBM.Gauss.SizesCompInst.inst_reindex_mp  663-665
RBM.Gauss.SizesCompInst.inst_reindex_BA  667-671
RBM.Gauss.SizesCompInst.inst_STLK_comp  673-679
private RBM.Gauss.SizesCompInst.sizesComp_STExp2_comp  681-687
RBM.Gauss.SizesCompInst.inst_STExp2_comp  689-693
RBM.Gauss.SizesCompInst.parity_infinite  695-697
RBM.Gauss.SizesCompInst.inst_STLK_parity  699-714
private RBM.Gauss.SizesCompInst.badSetAt_zero  725-730
private RBM.Gauss.SizesCompInst.stochDomAt_zero  732-734
private RBM.Gauss.SizesCompInst.perTimeDomAt_zero  736-746
RBM.Gauss.SizesCompInst.inst_Prec_comp_iff  750-757
RBM.Gauss.SizesCompInst.inst_PrecPT_Whp_comp_iff  759-763
RBM.Gauss.SizesCompInst.inst_of_map  765-772
RBM.Gauss.SizesCompInst.inst_subseq  774-786
RBM.Gauss.SizesCompInst.inst_nth_cover  788-792
RBM.Gauss.SizesCompInst.inst_parity_PrecPT_Whp  794-810
### RBM3D.Induction.Split  (20 unreached of 78)
private RBM.Ind.gloopProd_nil  272-272
RBM.Ind.gchain_nil  314-315
RBM.Ind.gchain_single  317-317
RBM.Ind.loopMax_two_mul_add_two_le  587-594
private RBM.Ind.Gres_zero_I  914-930
private RBM.Ind.Eblk_mul_self  933-939
private RBM.Ind.gloopProd_zero_I  942-963
private RBM.Ind.norm_loopL_zero_I  965-976
private RBM.Ind.loopMax_zero_I  978-994
private RBM.Ind.check_loopMax_formula  998-1002
private RBM.Ind.check_odd_sq_le  1004-1010
private RBM.Ind.check_odd_sq_le_values  1012-1019
private RBM.Ind.check_trace_mul_Eblk_le  1021-1025
private RBM.Ind.check_trace_mul_Eblk_ne_zero  1027-1031
private RBM.Ind.check_gloop_le_of_le_abs_im  1033-1039
private RBM.Ind.check_gloop_attained  1041-1051
private RBM.Ind.check_symIdx_split_le  1053-1063
private RBM.Ind.check_symIdx_split_values  1065-1078
private RBM.Ind.check_loopMax_two_mul_add_le  1080-1086
private RBM.Ind.check_loopXi_le  1088-1092
### RBM3D.Induction.Step1  (5 unreached of 20)
private RBM.Ind.Step1Inst.sz2  587-589
private RBM.Ind.Step1Inst.sz2_admissible  591-600
private RBM.Ind.Step1Inst.flow_z2  602-603
private RBM.Ind.Step1Inst.gbexp_ii_window  636-641
private RBM.Ind.Step1Inst.gbexp_ij_window  643-648
### RBM3D.Induction.Step1Setup  (17 unreached of 74)
RBM.StochDomAt.of_subset_whp  103-121
RBM.StochDomAt.of_subset_compl  123-131
RBM.Ind.stStep1_of_target  152-154
RBM.Ind.s1_size_eq  179-182
RBM.Ind.s1_one_le_L  184-185
RBM.Ind.s1_W_pow_le_size  192-197
private RBM.Ind.s1_pt_of_le  549-561
RBM.Ind.s1xM_nonneg  926-929
RBM.Ind.Step1SetupInst.s1Std_sz0  1140-1146
RBM.Ind.Step1SetupInst.s1Setup_conStInd_const  1224-1241
RBM.Ind.Step1SetupInst.bulk_z0'  1243-1246
RBM.Ind.Step1SetupInst.s1Std_sz0_const  1248-1261
RBM.Ind.Step1SetupInst.seqHflow_zero_sz0  1339-1340
RBM.Ind.Step1SetupInst.hE_half  1342-1343
RBM.Ind.Step1SetupInst.s1xM_time_zero_sz0  1345-1350
private RBM.Ind.Step1SetupInst.maxLoop2_nonneg  1390-1392
private RBM.Ind.Step1SetupInst.gexRHS_nonneg  1394-1399
### RBM3D.Induction.Step2Core  (28 unreached of 57)
RBM.Gauss.Sizes.ST_model_of_whp_grid  461-494
private RBM.Gauss.Sizes.sI  1314-1314
private RBM.Gauss.Sizes.tI  1315-1315
private RBM.Gauss.Sizes.KI  1316-1316
private RBM.Gauss.Sizes.lam_pos  1318-1320
private RBM.Gauss.Sizes.L100_real  1322-1324
private RBM.Gauss.Sizes.one_le_L100  1326-1326
private RBM.Gauss.Sizes.W100_real  1328-1330
private RBM.Gauss.Sizes.tailT_le_one  1416-1437
private RBM.Gauss.Sizes.meas_S  1449-1450
private RBM.Gauss.Sizes.VI  1456-1456
private RBM.Gauss.Sizes.sI_nonneg  1458-1458
private RBM.Gauss.Sizes.sI_le  1459-1459
private RBM.Gauss.Sizes.KI_ne  1460-1460
private RBM.Gauss.Sizes.size_ge_17  1462-1474
private RBM.Gauss.Sizes.tenth_rpow  1520-1524
private RBM.Gauss.Sizes.c30  1526-1528
private RBM.Gauss.Sizes.c5  1530-1532
private RBM.Gauss.Sizes.c6  1534-1536
private RBM.Gauss.Sizes.core_small  1538-1567
private RBM.Gauss.Sizes.r_bounds  1569-1578
private RBM.Gauss.Sizes.one_sub_pos  1580-1582
private RBM.Gauss.Sizes.mE_zero_im  1694-1697
private RBM.Gauss.Sizes.gt_eq  1699-1700
private RBM.Gauss.Sizes.gt_le  1702-1705
private RBM.Gauss.Sizes.Bctl_small  1707-1716
private RBM.Gauss.Sizes.a0  1718-1718
private RBM.Gauss.Sizes.a0_nonneg  1720-1721
### RBM3D.Induction.Step2Defs  (23 unreached of 87)
RBM.Gauss.Sizes.STLM_seqHflow  64-65
RBM.Gauss.Sizes.STGMM_seqHflow  150-151
RBM.Gauss.Sizes.STEEM_measurable  215-218
RBM.Gauss.Sizes.STstopIdx_isStoppingTime  550-558
RBM.Gauss.Step2DefsInst.inst_step2  877-890
RBM.Gauss.Step2DefsInst.inst_step2_lowg  892-903
RBM.Gauss.Step2DefsInst.STGMM_zero  905-926
RBM.Gauss.Step2DefsInst.inst_newKLK  928-954
RBM.Gauss.Step2DefsInst.inst_contractPt  956-979
RBM.Gauss.Step2DefsInst.Ψ0  981-982
RBM.Gauss.Step2DefsInst.W_ge_one  984-984
RBM.Gauss.Step2DefsInst.Ψ0_class  986-1004
RBM.Gauss.Step2DefsInst.inst_LWB  1006-1018
RBM.Gauss.Step2DefsInst.inst_EMn2Poly  1020-1030
RBM.Gauss.Step2DefsInst.Ψ1_window  1032-1036
RBM.Gauss.Step2DefsInst.ℓ0_range  1038-1040
RBM.Gauss.Step2DefsInst.inst_LWT  1042-1053
RBM.Gauss.Step2DefsInst.inst_EMn2Exp  1055-1067
RBM.Gauss.Step2DefsInst.inst_stop  1093-1099
RBM.Gauss.Step2DefsInst.inst_K2decay  1101-1112
RBM.Gauss.Step2DefsInst.inst_scaleExists  1126-1130
RBM.Gauss.Step2DefsInst.inst_optL2  1132-1146
RBM.Gauss.Step2DefsInst.inst_gridRepN  1156-1180
### RBM3D.Induction.Step2Events  (26 unreached of 80)
private RBM.Gauss.Sizes.KI  1468-1468
private RBM.Gauss.Sizes.VI  1469-1469
private RBM.Gauss.Sizes.lam_pos  1471-1473
private RBM.Gauss.Sizes.lam_le_one  1475-1477
private RBM.Gauss.Sizes.sI_nonneg  1479-1479
private RBM.Gauss.Sizes.sI_le  1480-1480
private RBM.Gauss.Sizes.KI_ne  1481-1481
private RBM.Gauss.Sizes.size_ge_17  1483-1491
private RBM.Gauss.Sizes.size_le_W6  1493-1497
private RBM.Gauss.Sizes.size_le_W6'  1499-1500
private RBM.Gauss.Sizes.Bctl_ge_half  1502-1510
private RBM.Gauss.Sizes.Bctl_le_three  1512-1519
private RBM.Gauss.Sizes.cardVI_le  1538-1542
private RBM.Gauss.Sizes.measF  1575-1578
private RBM.Gauss.Sizes.W_neg_le_N_neg  1677-1686
private RBM.Gauss.Sizes.hBd_sz0  1688-1713
private RBM.Gauss.Sizes.small_sz0  1715-1747
private RBM.Gauss.Sizes.hN_sz0  1799-1808
private RBM.Gauss.Sizes.hW_sz0  1810-1816
private RBM.Gauss.Sizes.seventeen_mul  1824-1830
private RBM.Gauss.Sizes.cast17  1832-1833
private RBM.Gauss.Sizes.hcard_idx  1835-1841
private RBM.Gauss.Sizes.hcard_lab  1843-1848
private RBM.Gauss.Sizes.hcard_fin2lab  1850-1856
private RBM.Gauss.Sizes.hKcap_sz0  1858-1861
private RBM.Gauss.Sizes.hsmall_sz0  1863-1866
### RBM3D.Induction.Step2Iterate  (24 unreached of 77)
RBM.Gauss.Sizes.STStep2Parts  1487-1498
RBM.Gauss.Sizes.ST_step2_concl  1500-1515
RBM.Gauss.Sizes.STLIM_seqHflow  1542-1543
RBM.Gauss.Sizes.STLKIM_seqHflow  1545-1546
RBM.Gauss.Sizes.STksimLKM_seqHflow  1548-1549
RBM.Gauss.Sizes.STeeM_seqHflow  1557-1559
RBM.Gauss.Sizes.ST_step2_of_pins'  1776-1782
RBM.Gauss.Step2IterateInst.hs0  1867-1867
RBM.Gauss.Step2IterateInst.hst  1869-1869
RBM.Gauss.Step2IterateInst.tInst_nonneg  1871-1871
RBM.Gauss.Step2IterateInst.ht1  1873-1873
RBM.Gauss.Step2IterateInst.htT  1875-1875
RBM.Gauss.Step2IterateInst.bdata_sz0  1877-1886
RBM.Gauss.Step2IterateInst.bdata_cB  1888-1888
RBM.Gauss.Step2IterateInst.bdata_c  1889-1889
RBM.Gauss.Step2IterateInst.bdata_spec  1891-1894
RBM.Gauss.Step2IterateInst.k2_sz0  1896-1901
RBM.Gauss.Step2IterateInst.CK0  1903-1903
RBM.Gauss.Step2IterateInst.CK0_pos  1904-1904
RBM.Gauss.Step2IterateInst.hK2_sz0  1905-1909
RBM.Gauss.Step2IterateInst.hq_sz0  1911-1918
RBM.Gauss.Step2IterateInst.scale_sz0  1920-1923
RBM.Gauss.Step2IterateInst.Kseq0  1925-1925
RBM.Gauss.Step2IterateInst.Kseq0_adm  1926-1926
### RBM3D.Induction.Step3  (4 unreached of 15)
RBM.Ind.Step3Inst.sz0_regIII  472-485
RBM.Ind.Step3Inst.inst_regIII  487-497
RBM.Ind.Step3Inst.inst_regI  499-511
RBM.Ind.Step3Inst.inst_II  513-525
### RBM3D.Induction.Step34Pins  (67 unreached of 125)
RBM.Gauss.Sizes.STStep3  274-275
RBM.Gauss.Sizes.STStep4  276-276
RBM.Gauss.Sizes.STStep3I  277-277
RBM.Gauss.Sizes.STsupXiLK  393-395
RBM.Gauss.Sizes.STXiBoot  408-422
RBM.Gauss.Sizes.STNQConcl  424-440
RBM.Gauss.Sizes.STOeqNQ  458-459
RBM.Gauss.Sizes.STOeqQt  461-462
RBM.Gauss.Sizes.STOeqQtNZ  464-465
RBM.Gauss.Sizes.STIterR  473-490
RBM.Gauss.Sizes.STIterations  496-497
RBM.Gauss.Sizes.STIterationsII  499-500
RBM.Gauss.Sizes.STAlternating  542-543
RBM.Gauss.Sizes.STWardTypeP  545-556
RBM.Gauss.Sizes.STB45  558-574
RBM.Gauss.Sizes.STWardTypePPin  576-577
RBM.Gauss.Sizes.STB45Pin  579-580
RBM.Gauss.Sizes.STEKSumRes1  624-634
RBM.Gauss.Step34Inst.szB  709-715
RBM.Gauss.Step34Inst.szB_W_tendsto  717-720
RBM.Gauss.Step34Inst.szB_size  722-723
RBM.Gauss.Step34Inst.szB_size_ge  725-728
RBM.Gauss.Step34Inst.szB_tendsto  730-736
RBM.Gauss.Step34Inst.szB_bandwidth  738-752
RBM.Gauss.Step34Inst.szB_WO  754-759
RBM.Gauss.Step34Inst.szB_admissible  761-762
RBM.Gauss.Step34Inst.zB  764-765
RBM.Gauss.Step34Inst.zB_locDomain  767-783
RBM.Gauss.Step34Inst.flow_zB  785-785
RBM.Gauss.Step34Inst.lemT_zB  787-811
RBM.Gauss.Step34Inst.Bctl_tendsto_const  813-822
RBM.Gauss.Step34Inst.conStInd_const  824-832
RBM.Gauss.Step34Inst.szB_caseI  834-835
RBM.Gauss.Step34Inst.szB_caseII  837-838
RBM.Gauss.Step34Inst.szB_regIterI  840-841
RBM.Gauss.Step34Inst.sz0_caseI  843-859
RBM.Gauss.Step34Inst.InstIngConcl  861-867
RBM.Gauss.Step34Inst.InstStep3Concl  869-873
RBM.Gauss.Step34Inst.InstStep4Concl  875-880
RBM.Gauss.Step34Inst.InstIterConcl  882-891
RBM.Gauss.Step34Inst.inst_ing  893-903
RBM.Gauss.Step34Inst.inst_iter  905-914
RBM.Gauss.Step34Inst.inst_step3R  916-925
RBM.Gauss.Step34Inst.inst_step4R  927-936
RBM.Gauss.Step34Inst.sz0_hs0  941-941
RBM.Gauss.Step34Inst.sz0_hst  942-942
RBM.Gauss.Step34Inst.sz0_ht  943-943
RBM.Gauss.Step34Inst.sz0_con  944-944
RBM.Gauss.Step34Inst.szB_flow_ht  946-946
RBM.Gauss.Step34Inst.inst_step3  948-951
RBM.Gauss.Step34Inst.inst_step3I  953-956
RBM.Gauss.Step34Inst.inst_step3II  958-963
RBM.Gauss.Step34Inst.inst_step4  965-967
RBM.Gauss.Step34Inst.inst_step4I  969-971
RBM.Gauss.Step34Inst.inst_step4II  973-977
RBM.Gauss.Step34Inst.inst_SEforLn  987-991
RBM.Gauss.Step34Inst.inst_OeqNQ  993-997
RBM.Gauss.Step34Inst.inst_OeqQt  999-1003
RBM.Gauss.Step34Inst.inst_OeqQtNZ  1005-1010
RBM.Gauss.Step34Inst.inst_WardTypeP  1012-1016
RBM.Gauss.Step34Inst.inst_B45  1018-1022
RBM.Gauss.Step34Inst.inst_iterations  1024-1029
RBM.Gauss.Step34Inst.inst_iterationsII  1031-1036
RBM.Gauss.Step34Inst.inst_contract  1040-1059
RBM.Gauss.Step34Inst.inst_newPQ  1061-1072
RBM.Gauss.Step34Inst.inst_mollifier  1074-1079
RBM.Gauss.Step34Inst.inst_qopNorm  1081-1089
### RBM3D.Induction.Step34PinsP  (6 unreached of 6)
RBM.Gauss.Sizes.STNQConcl'  48-65
RBM.Gauss.Sizes.STOeqNQ'  69-70
private RBM.Gauss.Sizes.stP_bootRHS_nonneg  78-87
private RBM.Gauss.Sizes.stNQConcl'_of_stNQConcl  89-146
RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ  153-166
RBM.Gauss.Step34PInst.inst_OeqNQ'  183-187
### RBM3D.Induction.Step4  (8 unreached of 14)
RBM.Ind.Step4Inst.Step4Concl  241-246
RBM.Ind.Step4Inst.inst_step4R_dis  248-259
RBM.Ind.Step4Inst.inst_stStep4I  261-264
RBM.Ind.Step4Inst.inst_stStep4II  266-270
RBM.Ind.Step4Inst.inst_stStep4I'  272-273
RBM.Ind.Step4Inst.inst_stStep4II'  275-277
RBM.Ind.Step4Inst.inst_mainInd3'_data  279-289
RBM.Ind.Step4Inst.inst_mainInd3'_sz0  291-297
### RBM3D.Induction.Step5Cases  (2 unreached of 16)
RBM.Gauss.Step5Inst.inst_skeletonII  706-710
RBM.Gauss.Step5Inst.inst_skeletonIII  712-715
### RBM3D.Induction.Step5Kernel  (35 unreached of 45)
RBM.step5Kernel_profile_holds  277-310
private RBM.step5Ker_tailT_mono  313-334
private RBM.step5Ker_tailW_mono_time  337-341
private RBM.step5Ker_tailW_sub  344-350
RBM.step5Kernel_profile_not_unconditional  352-440
RBM.Gauss.Sizes.step5Kernel_Th  454-457
RBM.Gauss.Sizes.step5Kernel_calA  459-469
private RBM.Gauss.Sizes.step5Ker_tw  471-474
private RBM.Gauss.Sizes.step5Ker_STprof_eq  476-478
private RBM.Gauss.Sizes.step5Ker_tw_pos  480-482
private RBM.Gauss.Sizes.step5Ker_tw_comm  484-487
private RBM.Gauss.Sizes.step5Ker_tw_mono_time  489-493
private RBM.Gauss.Sizes.step5Ker_tw_sub  495-498
private RBM.Gauss.Sizes.step5Ker_Th_eq_norm  500-503
private RBM.Gauss.Sizes.step5Ker_Th_nonneg  505-508
private RBM.Gauss.Sizes.step5Ker_Th_symm  510-517
private RBM.Gauss.Sizes.step5Ker_STprof_symm  519-521
RBM.Gauss.Sizes.step5Kernel_calA_holds  523-699
private RBM.Gauss.Sizes.step5Ker_tT  701-703
private RBM.Gauss.Sizes.step5Ker_tT_nonneg  705-707
private RBM.Gauss.Sizes.step5Ker_tT_comm  709-712
private RBM.Gauss.Sizes.step5Ker_tT_mono_time  714-718
private RBM.Gauss.Sizes.step5Ker_tw_le_add  720-726
private RBM.Gauss.Sizes.step5Ker_tT_le_tw  728-732
RBM.Gauss.Sizes.step5Kernel_calA_explicit_holds  734-938
RBM.Gauss.Sizes.step5Kernel_calA_sup_holds  940-957
RBM.step5Kernel_instSz  971-977
RBM.step5Kernel_decompU_inst  979-985
RBM.step5Kernel_UN_decompU_inst  987-997
RBM.step5Kernel_row_sum_inst  1000-1009
RBM.step5Kernel_profile_inst  1011-1023
RBM.step5Kernel_profile_explicit_inst  1025-1036
RBM.step5Kernel_calA_inst  1038-1049
RBM.step5Kernel_calA_explicit_inst  1051-1065
RBM.step5Kernel_calA_sup_inst  1067-1079
### RBM3D.Induction.Step5Kit  (8 unreached of 27)
RBM.Gauss.Step5Inst.inst_step5I  597-600
RBM.Gauss.Step5Inst.inst_step5II  602-605
RBM.Gauss.Step5Inst.inst_step5III  607-610
RBM.Gauss.Step5Inst.inst_step5IV  612-615
RBM.Gauss.Step5Inst.inst_step5IV_proved  617-620
RBM.Gauss.Step5Inst.inst_step5  622-625
RBM.Gauss.Step5Inst.inst_assembly  627-630
RBM.Gauss.Step5Inst.inst_skeletonI  634-638
### RBM3D.Induction.Step5Pins  (62 unreached of 106)
RBM.Gauss.Sizes.STLemDecCalE  190-193
RBM.Gauss.Sizes.STStep5  461-463
RBM.Gauss.Step5Inst.szG  496-497
RBM.Gauss.Step5Inst.szG_WO  499-504
RBM.Gauss.Step5Inst.szG_admissible  506-507
RBM.Gauss.Step5Inst.szG_W_tendsto  509-509
RBM.Gauss.Step5Inst.flow_zG  511-511
RBM.Gauss.Step5Inst.szG_reg4  513-514
RBM.Gauss.Step5Inst.szB_reg5I  516-517
RBM.Gauss.Step5Inst.szB_reg5II  519-520
RBM.Gauss.Step5Inst.sz0_reg5III  522-535
RBM.Gauss.Step5Inst.InstIng5Concl  537-544
RBM.Gauss.Step5Inst.inst_ing5  546-556
RBM.Gauss.Step5Inst.inst_ing5_I  558-565
RBM.Gauss.Step5Inst.inst_ing5_II  567-574
RBM.Gauss.Step5Inst.inst_ing5_III  576-581
RBM.Gauss.Step5Inst.inst_ing5_IV  583-590
RBM.Gauss.Step5Inst.inst_lemDecCalE  595-598
RBM.Gauss.Step5Inst.inst_pfStep5  600-603
RBM.Gauss.Step5Inst.inst_etermsMid  605-608
RBM.Gauss.Step5Inst.inst_duhamelI  610-614
RBM.Gauss.Step5Inst.inst_iniTermI  616-619
RBM.Gauss.Step5Inst.szCL_pow_le  630-640
RBM.Gauss.Step5Inst.szCL  642-649
RBM.Gauss.Step5Inst.szCL_L_le_W  651-651
RBM.Gauss.Step5Inst.szCL_L_real  653-655
RBM.Gauss.Step5Inst.szCL_W_real  657-659
RBM.Gauss.Step5Inst.szCL_log_W  661-662
RBM.Gauss.Step5Inst.szCL_log_W_le  664-668
RBM.Gauss.Step5Inst.szCL_one_le_log_W  670-674
RBM.Gauss.Step5Inst.szCL_size_le  676-680
RBM.Gauss.Step5Inst.szCL_bandwidth  682-691
RBM.Gauss.Step5Inst.szCL_n_le_size  693-700
RBM.Gauss.Step5Inst.szCL_tendsto  702-704
RBM.Gauss.Step5Inst.szCL_WO  706-710
RBM.Gauss.Step5Inst.szCL_admissible  712-713
RBM.Gauss.Step5Inst.sCL  715-715
RBM.Gauss.Step5Inst.tCL  717-717
RBM.Gauss.Step5Inst.zCL  719-719
RBM.Gauss.Step5Inst.szCL_two_le_L  721-725
RBM.Gauss.Step5Inst.zCL_locDomain  727-752
RBM.Gauss.Step5Inst.flow_zCL  754-754
RBM.Gauss.Step5Inst.lemT_zCL  756-782
RBM.Gauss.Step5Inst.szCL_hst  784-788
RBM.Gauss.Step5Inst.szCL_one_sub_t  790-791
RBM.Gauss.Step5Inst.szCL_reg5I  793-799
RBM.Gauss.Step5Inst.szCL_ellT_s  801-807
RBM.Gauss.Step5Inst.szCL_ellT_t  809-815
RBM.Gauss.Step5Inst.szCL_Bctl_le  817-846
RBM.Gauss.Step5Inst.szCL_con  848-875
RBM.Gauss.Step5Inst.xCL  877-878
RBM.Gauss.Step5Inst.zdistInf_xCL  880-895
RBM.Gauss.Step5Inst.szCL_cltFar_index_nonempty  897-925
RBM.Gauss.Step5Inst.szCL_cltIso_witness  927-960
RBM.Gauss.Step5Inst.inst_cltFar  962-966
RBM.Gauss.Step5Inst.inst_cltIso  968-972
RBM.Gauss.Step5Inst.inst_duhamelII  974-979
RBM.Gauss.Step5Inst.inst_iniTermII  981-985
RBM.Gauss.Step5Inst.inst_wardII  987-990
RBM.Gauss.Step5Inst.inst_tailtoTail  995-1011
RBM.Gauss.Step5Inst.inst_newKLKL  1013-1033
RBM.Gauss.Step5Inst.inst_expInv  1035-1042
### RBM3D.Induction.Step6Kit  (39 unreached of 81)
RBM.Gauss.Sizes.st6_G_pos  65-69
RBM.Gauss.Sizes.st6_target_lam_zero  71-77
RBM.Gauss.Sizes.st6_F1_window_vs_reg5II  725-731
RBM.Gauss.Sizes.ST_step6_caseI_of_pins  943-1028
RBM.Gauss.Sizes.st6_GdecayW_of_zero  1044-1075
RBM.Gauss.Sizes.ST_step6R_mono  1077-1082
RBM.Gauss.Step6Inst.inst_hiI  1093-1093
RBM.Gauss.Step6Inst.inst_hiII  1094-1094
RBM.Gauss.Step6Inst.inst_hiIII  1095-1095
RBM.Gauss.Step6Inst.inst_expLKLK_I  1097-1100
RBM.Gauss.Step6Inst.inst_expLKLK_II  1101-1103
RBM.Gauss.Step6Inst.inst_expLKLK_III  1104-1106
RBM.Gauss.Step6Inst.inst_skeleton6I  1110-1114
RBM.Gauss.Step6Inst.inst_skeleton6II  1116-1119
RBM.Gauss.Step6Inst.inst_skeleton6III  1121-1124
RBM.Gauss.Step6Inst.inst_skeleton6IV  1126-1129
RBM.Gauss.Step6Inst.inst_precU  1138-1146
RBM.Gauss.Step6Inst.inst_GdecayW_of_zero  1148-1150
RBM.Gauss.Step6Inst.inst_F1  1152-1155
RBM.Gauss.Step6Inst.inst_step6R_mono  1157-1160
RBM.Gauss.Step6Inst.inst_bridges  1162-1178
RBM.Gauss.Step6Inst.inst_endpoints  1180-1183
RBM.Gauss.Step6Inst.inst_expAvgU  1185-1189
RBM.Gauss.Step6Inst.inst_EGtHi  1191-1197
RBM.Gauss.Step6Inst.inst_duhEq  1199-1201
RBM.Gauss.Step6Inst.inst_G_pos_sz0  1203-1206
RBM.Gauss.Step6Inst.inst_G_pos_szB  1208-1209
RBM.Gauss.Step6Inst.inst_G_pos_szG  1211-1212
RBM.Gauss.Step6Inst.st6_target_pos  1214-1220
RBM.Gauss.Step6Inst.inst_target_pos_sz0  1222-1223
RBM.Gauss.Step6Inst.inst_target_pos_szB  1225-1226
RBM.Gauss.Step6Inst.inst_target_pos_szG  1228-1229
RBM.Gauss.Step6Inst.inst_lam_pos  1231-1232
RBM.Gauss.Step6Inst.inst_target_lam_zero  1234-1237
RBM.Gauss.Step6Inst.inst_cmp_III  1239-1248
RBM.Gauss.Step6Inst.inst_cmp_IV  1250-1259
RBM.Gauss.Step6Inst.inst_ini_sumNdecay  1261-1268
RBM.Gauss.Step6Inst.inst_ini_nonzero  1270-1280
RBM.Gauss.Step6Inst.inst_mollifier_family  1282-1286
### RBM3D.Induction.Step6Pins  (37 unreached of 76)
RBM.Gauss.Sizes.STExp2U_iff  78-83
RBM.Gauss.Sizes.ST_step6R_of_any  147-153
RBM.Gauss.Sizes.STExpIntQConcl  406-420
RBM.Gauss.Sizes.STExpIntI  446-452
RBM.Gauss.Sizes.STExpIniIConcl  454-468
RBM.Gauss.Sizes.STExpIniI  470-471
RBM.Gauss.Step6Inst.InstIng6Concl  503-510
RBM.Gauss.Step6Inst.inst_ing6  512-522
RBM.Gauss.Step6Inst.inst_ing6_I  524-531
RBM.Gauss.Step6Inst.inst_ing6_II  533-540
RBM.Gauss.Step6Inst.inst_ing6_III  542-547
RBM.Gauss.Step6Inst.inst_ing6_IV  549-556
RBM.Gauss.Step6Inst.inst_step6I  560-562
RBM.Gauss.Step6Inst.inst_step6II  564-566
RBM.Gauss.Step6Inst.inst_step6III  568-570
RBM.Gauss.Step6Inst.inst_step6IV  572-574
RBM.Gauss.Step6Inst.inst_step6  576-579
RBM.Gauss.Step6Inst.inst_step6_atI  581-584
RBM.Gauss.Step6Inst.inst_expDriftLo  595-599
RBM.Gauss.Step6Inst.inst_expDriftDecay  601-604
RBM.Gauss.Step6Inst.inst_expWardI  606-610
RBM.Gauss.Step6Inst.inst_expWardII  612-616
RBM.Gauss.Step6Inst.inst_expIniI  618-621
RBM.Gauss.Step6Inst.inst_expIntI  623-628
RBM.Gauss.Step6Inst.inst_expIntII  629-633
RBM.Gauss.Step6Inst.inst_expIntIII  634-637
RBM.Gauss.Step6Inst.inst_expIntIV  638-641
RBM.Gauss.Step6Inst.inst_improveExpAver  652-656
RBM.Gauss.Step6Inst.inst_expHier  658-665
RBM.Gauss.Step6Inst.inst_duhamelZ  667-678
RBM.Gauss.Step6Inst.inst_duhamelQ  680-695
RBM.Gauss.Step6Inst.inst_A_value  699-700
RBM.Gauss.Step6Inst.st6_idx2_nonempty  702-705
RBM.Gauss.Step6Inst.st6_idxSame_nonempty  707-709
RBM.Gauss.Step6Inst.st6_idxMixed_nonempty  711-713
RBM.Gauss.Step6Inst.inst_normQA2  715-720
RBM.Gauss.Step6Inst.inst_step6R_of_any  729-732
### RBM3D.Induction.StepDecompN  (30 unreached of 101)
private RBM.Ind.StepDecompN_loopFam_hC₂  1066-1079
RBM.Ind.Ugen_stepZCN  1158-1171
RBM.Ind.StepDecompN_subGaussStopN_zvecN  1312-1358
private RBM.Ind.StepDecompNCheck.E0  1379-1379
private RBM.Ind.StepDecompNCheck.s0  1380-1380
private RBM.Ind.StepDecompNCheck.t0  1381-1381
private RBM.Ind.StepDecompNCheck.K0  1382-1382
private RBM.Ind.StepDecompNCheck.σ3  1384-1385
private RBM.Ind.StepDecompNCheck.b3  1387-1388
private RBM.Ind.StepDecompNCheck.δ3  1390-1392
private RBM.Ind.StepDecompNCheck.U3  1394-1398
private RBM.Ind.StepDecompNCheck.hE0  1400-1400
private RBM.Ind.StepDecompNCheck.hs00  1401-1401
private RBM.Ind.StepDecompNCheck.hst0  1402-1402
private RBM.Ind.StepDecompNCheck.ht10  1403-1403
private RBM.Ind.StepDecompNCheck.hj0  1404-1404
private RBM.Ind.StepDecompNCheck.hj1  1405-1405
private RBM.Ind.StepDecompNCheck.hΔ  1407-1407
private RBM.Ind.StepDecompNCheck.data  1409-1412
private RBM.Ind.StepDecompNCheck.hΦ3  1414-1417
private RBM.Ind.StepDecompNCheck.C₂3  1419-1422
private RBM.Ind.StepDecompNCheck.hC₂3  1424-1428
private RBM.Ind.StepDecompNCheck.C₂3_pos  1430-1437
private RBM.Ind.StepDecompNCheck.pathH_zero  1475-1478
private RBM.Ind.StepDecompNCheck.A₀3  1480-1482
private RBM.Ind.StepDecompNCheck.AbCN_eq  1484-1486
private RBM.Ind.StepDecompNCheck.c3  1488-1491
private RBM.Ind.StepDecompNCheck.c3_nonneg  1493-1494
private RBM.Ind.StepDecompNCheck.boundRe3  1496-1499
private RBM.Ind.StepDecompNCheck.boundIm3  1501-1504
### RBM3D.Induction.TailtoTail  (2 unreached of 23)
RBM.Gauss.Sizes.inst_tailtoTail_zero  595-609
RBM.Gauss.Sizes.inst_tailtoTail_extremal  611-626
### RBM3D.Induction.TailtoTailSq  (2 unreached of 33)
private RBM.Gauss.Sizes.tailtoTailSq_four_le_log64  891-896
RBM.Gauss.Sizes.inst_tailtoTailSq_c  960-1011
### RBM3D.Induction.WardII  (1 unreached of 17)
private RBM.Gauss.Sizes.wardII_szI  330-336
### RBM3D.Induction.ZeroModeCalc  (16 unreached of 58)
RBM.zeroModeSet_zero  107-108
RBM.zeroModeOp_UN  338-343
RBM.sameSignOutside_of_STIdiff_subset  416-424
RBM.sameSignOutside_union_STIdiff  426-430
RBM.Ind.Ugen_eq_UN_EKsgn  442-446
RBM.Ind.zeroModeOp_Ugen  455-459
private RBM.ZeroModeCalcInst.zmcSigma  627-628
private RBM.ZeroModeCalcInst.zmcDelta  630-631
private RBM.ZeroModeCalcInst.zmcDelta_ne  633-635
private RBM.ZeroModeCalcInst.zmcIdiff_card  637-637
private RBM.ZeroModeCalcInst.zmcSigma_nonconst  639-639
private RBM.ZeroModeCalcInst.zmc_slot_lt_one  671-675
private RBM.ZeroModeCalcInst.zmcE  734-734
private RBM.ZeroModeCalcInst.zmcS  735-735
private RBM.ZeroModeCalcInst.zmcT  736-736
private RBM.ZeroModeCalcInst.zmcK  737-737
### RBM3D.Kernel.Evolution  (5 unreached of 35)
RBM.sum_one_complex  213-214
RBM.exists_norm_uKer_same_le  443-509
RBM.exists_norm_projMat_mul_uKer_le  518-610
RBM.SameSignOutside  616-619
RBM.norm_zeroModeSet_UN_le  621-682
### RBM3D.Kernel.PropT  (17 unreached of 43)
RBM.propT_ii  125-294
RBM.zmC  298-299
RBM.zmC_nonneg  301-301
RBM.constI  303-304
RBM.tailT_le_decay  306-330
RBM.propT_i  332-401
RBM.propT  405-441
RBM.min_le_add_min  622-638
RBM.sfT_TtTt  642-668
RBM.sfT_KtKt  671-680
RBM.sfT_pair_cases  682-714
RBM.wfac_antitone  769-771
RBM.sfT_pair_le  785-836
RBM.prod_sfT_pair_le  838-880
RBM.keyC  896-897
RBM.key_T_reduce  899-1003
RBM.key_T_reduce_absorbed  1048-1076
### RBM3D.Kernel.SumDecay  (5 unreached of 13)
RBM.UN_apply_eq_sum_powerset  347-367
RBM.norm_XiKer_apply_le  369-512
RBM.sum_ball_norm_XiKer_le  534-631
RBM.sum_prod_le_pow  647-657
RBM.sum_prod_norm_XiKer_le  659-706
### RBM3D.Loop.GLoop  (7 unreached of 13)
RBM.Gauss.Gsig  90-94
RBM.Gauss.gloop  96-99
RBM.Gauss.loopMax  101-103
RBM.Gauss.gsigEblk_apply  117-125
RBM.Gauss.norm_Gsig_entry_le  127-147
RBM.Gauss.norm_prod_entry_le  149-241
RBM.Gauss.norm_gloop_le  243-294
### RBM3D.Loop.GLoopFlow  (19 unreached of 61)
RBM.Gauss.zt_eq_ztOf  60-60
RBM.Gauss.etaT_eq_etaOf  62-62
RBM.Gauss.Gsig_eq_Gres  86-87
RBM.Gauss.gloop_eq_loopM  96-98
RBM.Gauss.Mres_zero_msc  218-229
private RBM.Gauss.gloopProd_nil  390-391
private RBM.Gauss.gloopProd_cons  393-397
RBM.Gauss.GLoopFlowInst.z0  929-930
RBM.Gauss.GLoopFlowInst.sz0_size_pos  932-933
RBM.Gauss.GLoopFlowInst.z0_im_pos  935-936
RBM.Gauss.GLoopFlowInst.z0_mem  938-939
RBM.Gauss.GLoopFlowInst.z0_zztE  941-951
RBM.Gauss.GLoopFlowInst.z0_Gt  953-957
RBM.Gauss.GLoopFlowInst.loopL_sz0  959-965
RBM.Gauss.GLoopFlowInst.Mres_sz0  967-972
RBM.Gauss.GLoopFlowInst.Lloop_sz0  974-979
RBM.Gauss.GLoopFlowInst.norm_loop_sz0  1041-1049
RBM.Gauss.GLoopFlowInst.norm_Lloop_sz0  1051-1057
RBM.Gauss.GLoopFlowInst.norm_gloop_sharp_sz0  1059-1070
### RBM3D.Loop.KBound  (2 unreached of 3)
RBM.Loop.KLoopBound  62-78
RBM.Loop.not_inv_pow_pair_le_single  143-152
### RBM3D.Loop.KLCut  (33 unreached of 121)
private RBM.Loop.sum_perm4'  101-111
RBM.Loop.KLCutInst_sum_cut  1336-1342
RBM.Loop.KLCutInst_sum_cut_count  1344-1348
RBM.Loop.KLCutInst_sum_cut_card  1350-1359
RBM.Loop.KLCutInst_vertex_maps  1361-1369
RBM.Loop.KLCutInst_F5  1371-1372
RBM.Loop.KLCutInst_F5_mem  1374-1374
RBM.Loop.KLCutInst_J5_mem  1376-1376
RBM.Loop.KLCutInst_J5_isDiag  1378-1379
RBM.Loop.KLCutInst_pieces  1381-1385
RBM.Loop.KLCutInst_FIn_mem  1387-1391
RBM.Loop.KLCutInst_FOut_mem  1393-1398
RBM.Loop.KLCutInst_glueF_mem  1400-1406
RBM.Loop.KLCutInst_glueF_cut  1408-1413
RBM.Loop.KLCutInst_FIn_glueF  1415-1421
RBM.Loop.KLCutInst_FOut_glueF  1423-1429
RBM.Loop.KLCutInst_F4  1433-1434
RBM.Loop.KLCutInst_F4_mem  1436-1436
RBM.Loop.KLCutInst_J4_mem  1438-1438
RBM.Loop.KLCutInst_σ4  1440-1441
RBM.Loop.KLCutInst_a4  1443-1444
RBM.Loop.KLCutInst_M4  1446-1448
RBM.Loop.KLCutInst_E4  1450-1452
RBM.Loop.KLCutInst_P4  1454-1456
RBM.Loop.KLCutInst_treeValW_cut  1458-1484
RBM.Loop.KLCutInst_pieces4  1486-1490
RBM.Loop.KLCutInst_gval_in  1492-1525
RBM.Loop.KLCutInst_gval_out  1527-1565
RBM.Loop.KLCutInst_eq_gval  1569-1579
RBM.Loop.KLCutInst_gval_congr  1581-1599
RBM.Loop.KLCutInst_gval_split  1601-1625
private RBM.Loop.KLCutInst_hasDerivAt_ofReal_mul  1627-1629
RBM.Loop.KLCutInst_hasDerivAt  1631-1644
### RBM3D.Loop.KLFinal  (6 unreached of 25)
RBM.Loop.KLoopBound_KLK  164-180
RBM.Gauss.Sizes.KLFinal_szConst  321-326
RBM.Gauss.Sizes.KLFinal_szConst_size  328-329
private RBM.Gauss.Sizes.KLFinal_mSigma_mul  331-336
private RBM.Gauss.Sizes.KLFinal_Theta_zero  338-339
RBM.Gauss.Sizes.KLFinal_not_stKbound  341-381
### RBM3D.Loop.KLIndStepA  (12 unreached of 61)
RBM.Loop.KLf2_neg  75-77
RBM.Loop.KLf0_bound  347-355
RBM.Loop.KLf_crude_bound  357-375
RBM.Loop.KLf12_bound  377-412
RBM.Loop.KLlat_pow_sub_two  442-447
RBM.Loop.KLlat_pow_sub_one  449-474
RBM.Loop.KLlat_log_le_logL  605-616
RBM.Loop.KLlat_pow_dim_logL  618-625
RBM.Loop.KLlat_pair_logL  627-635
RBM.Loop.KLslice_f1_vanish  705-712
RBM.Loop.KLindStep_nonAlt_noloss  1364-1376
RBM.Loop.KLindStep_nonAlt  1378-1401
### RBM3D.Loop.KLIndStepB  (1 unreached of 28)
RBM.Loop.KLindStep_alt  853-866
### RBM3D.Loop.KLInduct  (5 unreached of 31)
RBM.Loop.KLKpiBoundPin  111-113
RBM.Loop.KLKpiBoundPin_holds  1145-1148
RBM.Loop.KLInduct_instσ  1207-1209
RBM.Loop.KLInduct_insta  1211-1212
RBM.Loop.KLInduct_instJ  1290-1292
### RBM3D.Loop.KLMolecule  (10 unreached of 39)
private RBM.Loop.KLMolecule_mE_zero  885-889
private RBM.Loop.KLMolecule_mSigma_sq  891-892
private RBM.Loop.KLMolecule_TSPlong_four  894-897
private RBM.Loop.KLMolecule_Qlayer_four  899-909
private RBM.Loop.KLMolecule_TSPlong_three  911-913
RBM.Loop.KLMolecule_inst_molecule_norm  915-924
RBM.Loop.KLMolecule_inst_molecule  926-940
RBM.Loop.KLMolecule_inst_signed_val  942-953
RBM.Loop.KLMolecule_inst_sumZero  955-973
private RBM.Loop.KLMolecule_parEdge  975-989
### RBM3D.Loop.KLSumAll  (8 unreached of 38)
private RBM.Loop.KLSumAll_gapK_one  759-761
private RBM.Loop.KLSumAll_etaT_half  763-768
RBM.Loop.KLSumAll_inst_four  770-777
RBM.Loop.KLSumAll_inst_four_val  779-786
RBM.Loop.KLSumAll_inst_two  788-795
RBM.Loop.KLSumAll_inst_three  797-804
private RBM.Loop.KLSumAll_mSigma_zero  806-810
RBM.Loop.KLSumAll_inst_two_val  812-838
### RBM3D.Loop.KLSumZero  (34 unreached of 77)
RBM.Loop.sum_Theta_sub_one_row  288-294
private RBM.Loop.chk_mE_zero  845-849
private RBM.Loop.chk_m_true  851-852
private RBM.Loop.chk_m_false  854-855
private RBM.Loop.chk_mSigma_sq  857-858
private RBM.Loop.chk_hm  860-862
private RBM.Loop.chk_TSPlong_four  864-866
private RBM.Loop.chk_Qlayer  868-877
RBM.Loop.KLSumZero_inst_Qlayer_one  879-883
private RBM.Loop.chk_prod_m  885-887
RBM.Loop.KLSumZero_inst_slice_alt  889-896
RBM.Loop.KLSumZero_inst_bound  898-906
RBM.Loop.KLSumZero_inst_slice  908-915
RBM.Loop.KLSumZero_inst_sum_SigmaPi  917-921
RBM.Loop.KLSumZero_inst_Kpi_eq  923-929
RBM.Loop.KLSumZero_inst_Kpi_closed  931-937
private RBM.Loop.chk_Alayer  939-951
RBM.Loop.KLSumZero_inst_Kpi_closed_val  953-958
private RBM.Loop.chk_TSPlong_three  960-962
private RBM.Loop.chk_Qlayer_pure  964-966
RBM.Loop.KLSumZero_inst_Kpi_closed_pure  968-982
RBM.Loop.KLSumZero_neg_Kpi_closed_2Dform  984-998
RBM.Loop.KLSumZero_inst_add_const  1000-1004
RBM.Loop.KLSumZero_instF  1006-1007
RBM.Loop.KLSumZero_instF_mem  1009-1009
RBM.Loop.KLSumZero_instE  1011-1013
RBM.Loop.KLSumZero_instr  1015-1017
RBM.Loop.KLSumZero_inst_col  1019-1023
RBM.Loop.KLSumZero_inst_treeZ_peel  1025-1033
RBM.Loop.KLSumZero_inst_treeZ_eq  1035-1040
RBM.Loop.KLSumZero_inst_sum_selfW  1042-1046
RBM.Loop.KLSumZero_inst_Theta_sums  1048-1058
RBM.Loop.KLSumZero_inst_gap  1060-1064
RBM.Loop.KLSumZero_inst_sum_out  1066-1076
### RBM3D.Loop.KLSumZeroWard  (10 unreached of 50)
RBM.Loop.KLSumZeroWard_Qlayer_zero  1183-1194
RBM.Loop.KLSumZeroWard_inst_Q_four  1196-1200
RBM.Loop.KLSumZeroWard_inst_Q_six  1202-1206
RBM.Loop.KLSumZeroWard_inst_Q_four_nondeg  1208-1212
RBM.Loop.KLSumZeroWard_inst_Q_six_nondeg  1214-1218
RBM.Loop.KLSumZeroWard_inst_card  1221-1226
RBM.Loop.KLSumZeroWard_inst_bound  1228-1236
RBM.Loop.KLSumZeroWard_inst_bound_zero  1238-1244
RBM.Loop.KLSumZeroWard_inst_bound_lhs  1246-1251
RBM.Loop.KLSumZeroWard_inst_bound_six  1253-1261
### RBM3D.Loop.KLTree  (21 unreached of 102)
RBM.Loop.KLSigmaPi_empty_symm  773-792
RBM.Loop.MLoopM  815-820
RBM.Loop.KLallEq  822-824
RBM.Loop.treeEqRhs_eq_treeEqRhsS  837-839
RBM.Loop.KLMLoop_eq_MLoopM  841-843
RBM.Loop.IsKLoop_iff_IsKLoopS  845-848
RBM.Loop.KLinstPar  855-869
RBM.Loop.KLinstσ  871-872
RBM.Loop.KLinsta  874-874
RBM.Loop.KLinst_scales  876-887
RBM.Loop.KLinst_two  889-894
RBM.Loop.KLinst_three  896-904
RBM.Loop.KLinst_ward_two  906-912
RBM.Loop.KLinst_Kpi  914-920
RBM.Loop.KLinst_Kpi_SigmaPi  922-929
RBM.Loop.KLinst_SigmaPi_symm  931-937
RBM.Loop.KLinst_treeEqRhsS  939-945
RBM.Loop.KLinst_MLoopM  947-951
RBM.Loop.KLinst_IsKLoopS  953-959
RBM.Loop.KLinst_one_two_kTwo  961-966
RBM.Loop.KLinst_gen_loopOf  968-972
### RBM3D.Loop.KLTreeDeriv  (10 unreached of 50)
private RBM.Loop.Kgen_one  506-508
private RBM.Loop.mE_zero_eq  1072-1077
RBM.Loop.KLTreeDerivInst_isKLoop  1079-1082
RBM.Loop.KLTreeDerivInst_ode_two  1084-1089
RBM.Loop.KLTreeDerivInst_ode_three  1091-1097
RBM.Loop.KLTreeDerivInst_ode_four  1099-1107
RBM.Loop.KLTreeDerivInst_ode_zero  1109-1115
RBM.Loop.KLTreeDerivInst_init_const  1117-1126
RBM.Loop.KLTreeDerivInst_init_nonconst  1128-1141
RBM.Loop.KLTreeDerivInst_one  1143-1149
### RBM3D.Loop.KLUnique  (19 unreached of 49)
RBM.Loop.KLK_unique  115-140
private RBM.Loop.KLUnique_isKLoop_shift  221-227
RBM.Loop.KLUniqueInst_unique_one  742-748
RBM.Loop.KLUniqueInst_unique_two  750-756
RBM.Loop.KLUniqueInst_unique_three  758-764
RBM.Loop.KLUniqueInst_unique_shifted  766-782
RBM.Loop.KLUniqueInst_rotate_three  784-789
RBM.Loop.KLUniqueInst_rotate_four  791-797
RBM.Loop.KLUniqueInst_translate_three  799-809
RBM.Loop.KLUniqueInst_retire_twoLoopBounded  811-816
RBM.Loop.KLUniqueInst_kTwoFormula  818-823
RBM.Loop.KLUniqueInst_kThree  825-831
private RBM.Loop.KLUnique_inst_im  833-835
RBM.Loop.KLUniqueInst_pureLoop_two  837-848
RBM.Loop.KLUniqueInst_pureLoop_three  850-861
RBM.Loop.kernel_SB_rot_transl  875-881
RBM.Loop.KLUniqueInst_uniqS_shifted  883-906
RBM.Loop.KLUniqueInst_rotS  908-917
RBM.Loop.KLUniqueInst_translS  919-931
### RBM3D.Loop.KLWard  (10 unreached of 74)
private RBM.Loop.KLWard_flipIdx_length  1037-1039
RBM.Loop.KLWard_flip  1331-1339
RBM.Loop.KLWardInst_ward_true  1354-1361
RBM.Loop.KLWardInst_ward_false  1363-1370
RBM.Loop.KLWardInst_ward_two_false  1372-1379
RBM.Loop.KLWardInst_ward_four_false  1381-1389
RBM.Loop.KLWardInst_flip  1391-1396
RBM.Loop.KLWardInst_kernelFacts_one  1398-1399
RBM.Loop.KLWardInst_kernelFacts_SB  1401-1402
RBM.Loop.KLWardInst_wardS  1404-1420
### RBM3D.Loop.Partition  (21 unreached of 35)
RBM.Loop.crossing_comm  94-95
RBM.Loop.TSP_four  110-112
RBM.Loop.card_TSP_five  114-116
RBM.Loop.noncrossing_split  118-126
RBM.Loop.isDiag_split_lt  128-134
RBM.Loop.reindexR  136-140
RBM.Loop.leftPairs  142-144
RBM.Loop.rightPairs  146-148
RBM.Loop.length_leftPairs_le  150-153
RBM.Loop.length_rightPairs_le  155-158
RBM.Loop.starGamma  174-178
RBM.Loop.polyVal  180-213
RBM.Loop.bdList  215-220
RBM.Loop.treeVal  222-227
RBM.Loop.diagList  229-232
RBM.Loop.treeSum  234-236
RBM.Loop.GammaN  238-242
RBM.Loop.GammaSum  244-248
RBM.Loop.treeVal_nil_eq_polyVal  252-256
RBM.Loop.treeVal_four_nil  258-274
RBM.Loop.GammaSum_eq_sum  276-279
### RBM3D.Loop.Primitive  (6 unreached of 11)
RBM.Loop.norm_mul_lt_one  54-61
RBM.Loop.kTwoLoop  96-100
RBM.Loop.hasDerivAt_kTwoLoop  104-111
RBM.Loop.kTwoLoop_zero  113-116
RBM.Loop.kTwoFormula_kTwoLoop  118-123
RBM.Loop.pureLoop_two_kTwoLoop  147-157
### RBM3D.Loop.PureLoop  (5 unreached of 6)
RBM.Loop.norm_Theta_same_le_exp  55-87
RBM.Loop.sum_exp_decay_conv  91-130
RBM.Loop.norm_sum_prod_le  149-236
RBM.Loop.KTwoFormula  242-248
RBM.Loop.pureLoop_two  252-288
### RBM3D.Loop.TreeFour  (8 unreached of 8)
RBM.Loop.treeEqRhs_four  38-78
RBM.Loop.treeVal_four_diag02  87-107
RBM.Loop.treeVal_four_diag13  109-129
RBM.Loop.treeSum_four  131-148
RBM.Loop.hasDerivAt_thetaEdge_sub_one  165-179
RBM.Loop.hasDerivAt_starFour  181-212
RBM.Loop.treeVal_four_diag02_as_star  227-239
RBM.Loop.treeVal_four_diag13_as_star  241-249
### RBM3D.Loop.TreeThree  (15 unreached of 15)
RBM.Loop.treeEqRhs_three  48-69
RBM.Loop.treeVal_three_nil  73-88
RBM.Loop.treeSum_three  90-97
RBM.Loop.kThree  101-104
RBM.Loop.kThree_zero  108-135
RBM.Loop.sum_sum_mul_SB  140-148
RBM.Loop.sum_SB_starLeft  150-177
RBM.Loop.sum_SB_starLeft.sum_SB_starLeft_aux  173-177
RBM.Loop.sum_SB_starRight  179-198
RBM.Loop.hasDerivAt_starThree  200-221
RBM.Loop.hasDerivAt_kThree  223-317
RBM.Loop.kLoop3  323-329
RBM.Loop.exists_eq_of_length_three  334-342
RBM.Loop.kThree_eq_of_isKLoop  344-399
RBM.Loop.pureLoop_three  403-469
### RBM3D.Loop.Unique  (7 unreached of 24)
RBM.Loop.eq_on_level  268-283
RBM.Loop.isKLoop_unique  309-319
RBM.Loop.KLretire_twoLoopBounded  359-366
RBM.Loop.kTwoFormula_of_isKLoop  368-418
RBM.Loop.pureLoop_two_of_isKLoop  420-431
RBM.Loop.UniqueInst_retireS  439-444
RBM.Loop.UniqueInst_uniqS  446-457
### RBM3D.Main.BandTerminal  (3 unreached of 12)
RBM.Endpoints.unOUClaims_holds  73-74
RBM.Endpoints.unOUQUE_holds  76-84
RBM.Endpoints.unClaimRowBA_holds  86-88
### RBM3D.Main.FixedZ  (6 unreached of 26)
RBM.Endpoints.MAFixed  70-73
RBM.Endpoints.fixed_of_ML  537-538
RBM.Endpoints.Inst.inst_decol_of_locSC  812-817
RBM.Endpoints.Inst.inst_locSCFixed  819-826
RBM.Endpoints.Inst.inst_QDiffFixed  828-840
RBM.Endpoints.Inst.inst_decol_scalars  842-847
### RBM3D.Main.QUECore  (3 unreached of 57)
RBM.Endpoints.Inst.inst_thetaDiff  1111-1117
private RBM.Endpoints.Inst.queCore_inst_window  1119-1142
RBM.Endpoints.Inst.inst_queBad_sub  1144-1152
### RBM3D.Main.QUEFromQDiff  (9 unreached of 23)
RBM.Endpoints.Inst.queDomain_edge  545-552
RBM.Endpoints.Inst.inst_queDomain  554-558
RBM.Endpoints.Inst.inst_BetaK  560-566
RBM.Endpoints.Inst.inst_three_terms  568-572
private RBM.Endpoints.Inst.queFromQDiff_inst_etaQ  576-597
RBM.Endpoints.Inst.inst_queRowDiff  599-606
RBM.Endpoints.Inst.inst_queChain  608-617
RBM.Endpoints.Inst.inst_queFixed  619-648
RBM.Endpoints.Inst.inst_QUE_of_QDiff  650-658
### RBM3D.Main.ZNet  (5 unreached of 54)
RBM.Endpoints.Inst.inst_netLoc  1063-1069
RBM.Endpoints.Inst.inst_netQD  1071-1082
RBM.Endpoints.Inst.inst_zNet  1084-1089
private RBM.Endpoints.Inst.znet_inst_h32  1103-1106
private RBM.Endpoints.Inst.znet_inst_h5  1108-1110
### RBM3D.Main.ZTransfer  (6 unreached of 31)
RBM.Endpoints.Inst.inst_zRange  537-541
RBM.Endpoints.Inst.inst_btBt  543-548
RBM.Endpoints.Inst.inst_zLocal  550-553
RBM.Endpoints.Inst.inst_zAve  555-559
RBM.Endpoints.Inst.inst_zTrace  561-567
RBM.Endpoints.Inst.inst_zProfile  569-573
### RBM3D.Path.Azuma  (3 unreached of 8)
RBM.Path.stopped_martingale  307-332
private RBM.Path.azumaInstY  350-354
private RBM.Path.azumaInstY_adapted  356-369
### RBM3D.Path.DifREP1  (11 unreached of 74)
RBM.Ind.DifREP1Inst.hs0  1325-1325
RBM.Ind.DifREP1Inst.hst  1327-1327
RBM.Ind.DifREP1Inst.htT  1329-1329
RBM.Ind.DifREP1Inst.gridStep_inst  1331-1333
RBM.Ind.DifREP1Inst.σ3  1335-1336
RBM.Ind.DifREP1Inst.ω0  1338-1339
RBM.Ind.DifREP1Inst.inst_difRep_identity  1341-1351
RBM.Ind.DifREP1Inst.inst_difRepMartN_succ_sub  1353-1358
RBM.Ind.DifREP1Inst.inst_difRep_Ugen_step_le  1364-1372
RBM.Ind.DifREP1Inst.inst_difRep_flow_bounds  1374-1380
RBM.Ind.DifREP1Inst.inst_gridRepRemN  1382-1406
### RBM3D.Path.DifREP2  (33 unreached of 101)
RBM.Ind.difRep2_peel_N  750-794
private RBM.Ind.difRepTail_measurable_linTr_left  1099-1108
private RBM.Ind.difRepTail_linTrVar_eq_sum  1110-1116
private RBM.Ind.difRepTail_measurable_linTrVar  1118-1127
private RBM.Ind.difRepTail_vSeq_le_crude  1719-1735
RBM.Ind.stGridMartAt_holds  2286-2293
RBM.Ind.DifREP2Inst.hs0  2309-2309
RBM.Ind.DifREP2Inst.hst  2311-2311
RBM.Ind.DifREP2Inst.htT  2313-2313
RBM.Ind.DifREP2Inst.gridStep_inst  2315-2317
RBM.Ind.DifREP2Inst.E12  2319-2320
RBM.Ind.DifREP2Inst.σ3  2322-2323
RBM.Ind.DifREP2Inst.a0  2325-2326
RBM.Ind.DifREP2Inst.κ0  2328-2329
RBM.Ind.DifREP2Inst.hE12  2331-2334
RBM.Ind.DifREP2Inst.ht0  2336-2336
RBM.Ind.DifREP2Inst.N0_pos  2338-2339
RBM.Ind.DifREP2Inst.eta12  2341-2351
RBM.Ind.DifREP2Inst.gridTime_inst_le  2353-2357
RBM.Ind.DifREP2Inst.eta_ge  2359-2365
RBM.Ind.DifREP2Inst.eta_inst  2367-2370
RBM.Ind.DifREP2Inst.herm0  2379-2381
RBM.Ind.DifREP2Inst.B3  2400-2402
RBM.Ind.DifREP2Inst.B3_pos  2404-2408
RBM.Ind.DifREP2Inst.inst_azumaRandProxy_max  2410-2438
RBM.Ind.DifREP2Inst.δ3  2442-2443
RBM.Ind.DifREP2Inst.δ3_pos  2445-2450
RBM.Ind.DifREP2Inst.Lmax3  2452-2454
RBM.Ind.DifREP2Inst.inst_peel  2456-2499
RBM.Ind.DifREP2Inst.aN  2503-2505
RBM.Ind.DifREP2Inst.LmaxN  2507-2508
RBM.Ind.DifREP2Inst.inst_peel_N  2510-2570
RBM.Ind.DifREP2Inst.inst_gridRepTailN  2574-2597
### RBM3D.Path.DifREP3  (8 unreached of 99)
RBM.Ind.DifREP3Inst.hs0  2400-2400
RBM.Ind.DifREP3Inst.hst  2402-2402
RBM.Ind.DifREP3Inst.htT  2404-2404
RBM.Ind.DifREP3Inst.gridStep_inst  2406-2408
RBM.Ind.DifREP3Inst.σ3  2410-2411
RBM.Ind.DifREP3Inst.a0  2413-2414
RBM.Ind.DifREP3Inst.inst_gridRepWTailQN  2485-2512
RBM.Ind.DifREP3Inst.inst_gridRepWTailN  2521-2546
### RBM3D.Path.DriftAlgebra  (34 unreached of 34)
RBM.Path.KpmODE  48-57
RBM.Path.LoopGenN2  59-70
RBM.Path.HierarchyN2  72-83
private RBM.Path.DriftAlgebra_mSigma_mul  91-96
private RBM.Path.DriftAlgebra_STKloop_eq  98-106
RBM.Path.kpmODE  110-122
private RBM.Path.DriftAlgebra_hasDerivAt_trace  132-141
private RBM.Path.DriftAlgebra_hasDerivAt_Gres  143-158
private RBM.Path.DriftAlgebra_hasDerivAt_line  161-166
private RBM.Path.DriftAlgebra_isHermitian_add_realSmul  169-174
private RBM.Path.DriftAlgebra_hasDerivAt_word1  178-186
private RBM.Path.DriftAlgebra_hasDerivAt_word2  188-205
private RBM.Path.DriftAlgebra_loopL_pm  217-222
private RBM.Path.DriftAlgebra_loopFine_pm  224-230
private RBM.Path.DriftAlgebra_loopFine_three  232-238
private RBM.Path.DriftAlgebra_loopFine_one  240-245
private RBM.Path.DriftAlgebra_blockMat_add_smul  247-251
private RBM.Path.DriftAlgebra_deriv2_line  253-283
private RBM.Path.DriftAlgebra_deriv_spec  285-312
private RBM.Path.DriftAlgebra_cov  314-341
private RBM.Path.DriftAlgebra_sum_Eblk  351-360
private RBM.Path.DriftAlgebra_trace_insert  362-371
private RBM.Path.DriftAlgebra_sum_SB_col  373-378
private RBM.Path.DriftAlgebra_sum_algebra  380-418
private RBM.Path.DriftAlgebra_rot  422-425
private RBM.Path.DriftAlgebra_loopGen_core  427-573
RBM.Path.loopGenN2  575-578
private RBM.Path.DriftAlgebra_matrix_identity  586-603
private RBM.Path.DriftAlgebra_TST_apply  605-610
RBM.Path.hierarchyN2  614-693
RBM.Path.DriftAlgebra_check_labels_sz0  706-710
RBM.Path.DriftAlgebra_check_kpmODE_sz0  712-719
RBM.Path.DriftAlgebra_check_loopGenN2_sz0  721-737
RBM.Path.DriftAlgebra_check_hierarchyN2_sz0  739-756
### RBM3D.Path.DuhamelTail  (36 unreached of 36)
private RBM.Path.DuhamelTail_prependZero  55-59
private RBM.Path.DuhamelTail_prependZero_succ  61-62
private RBM.Path.DuhamelTail_sum_range_succ_prependZero  64-68
private RBM.Path.DuhamelTail_memLp_finset_sum  70-79
private RBM.Path.DuhamelTail_norm_real_mul_lt_one  81-91
private RBM.Path.DuhamelTail_back_factor_apply  93-102
private RBM.Path.DuhamelTail_back_factor_sum_apply  104-132
private RBM.Path.DuhamelTail_exists_label_of_back_bound  134-151
private RBM.Path.DuhamelTail_card_label  153-158
RBM.Path.stoppedEdge  168-175
RBM.Path.stoppedEdge_apply  177-182
private RBM.Path.DuhamelTail_stronglyMeasurable_Uop_apply  184-196
private RBM.Path.DuhamelTail_stronglyMeasurable_stoppedEdge  198-209
private RBM.Path.DuhamelTail_stronglyMeasurable_stoppedEdge_re  211-217
private RBM.Path.DuhamelTail_stronglyMeasurable_stoppedEdge_im  219-225
private RBM.Path.DuhamelTail_stopped_sum_apply_eq  227-236
private RBM.Path.DuhamelTail_inner_sum_apply_eq  238-246
private RBM.Path.DuhamelTail_azuma_stoppedEdge  257-342
RBM.Path.stopped_duhamel_azuma_tail_fixed  344-374
RBM.Path.stopped_duhamel_azuma_union  376-429
RBM.Path.stopped_duhamel_cheb_tail  440-648
RBM.Path.stopped_duhamel_det_bound  659-699
RBM.Path.StoppedAzuma108  709-734
private RBM.Path.DuhamelTail_measurable_Avec  740-747
private RBM.Path.DuhamelTail_stronglyMeasurable_martInc  749-759
private RBM.Path.DuhamelTail_Z  761-764
RBM.Path.stoppedAzuma108_at  768-802
RBM.Path.stoppedAzuma108  804-809
private RBM.Path.DuhamelTail_instS  827-827
private RBM.Path.DuhamelTail_instT  828-828
private RBM.Path.DuhamelTail_instK  829-829
private RBM.Path.DuhamelTail_inst_s0  831-832
private RBM.Path.DuhamelTail_inst_st  834-835
private RBM.Path.DuhamelTail_inst_t1  837-838
private RBM.Path.DuhamelTail_inst_K  840-841
private RBM.Path.DuhamelTail_instU  908-908
### RBM3D.Path.Expansion  (93 unreached of 93)
RBM.Path.Avec  53-56
RBM.Path.martInc  58-63
RBM.Path.predInc  65-70
RBM.Path.StoppedDuhamel105  72-83
private RBM.Path.Expansion_gridStep_nonneg  91-92
private RBM.Path.Expansion_gridTime_succ  94-96
private RBM.Path.Expansion_gridTime_zero  98-99
private RBM.Path.Expansion_gridTime_mono  101-106
private RBM.Path.Expansion_gridTime_nonneg  108-112
private RBM.Path.Expansion_gridTime_lt_one  114-118
private RBM.Path.Expansion_normSq_mE  124-127
RBM.Path.stoppedDuhamel105_at  129-156
RBM.Path.stoppedDuhamel105  158-162
private RBM.Path.Expansion_herm  170-172
private RBM.Path.Expansion_herm_isHermitian  174-176
private RBM.Path.Expansion_herm_of_isHermitian  178-182
private RBM.Path.Expansion_continuous_herm  184-188
private RBM.Path.Expansion_continuous_comp  190-196
private RBM.Path.Expansion_measurable_phi  200-210
private RBM.Path.Expansion_integrable_phi  212-220
private RBM.Path.Expansion_mSigma_mul  231-235
private RBM.Path.Expansion_STKloop_eq  237-247
private RBM.Path.Expansion_norm_Theta_real  249-252
private RBM.Path.Expansion_norm_entry_le  254-257
private RBM.Path.Expansion_norm_ofReal_lt_one  259-262
private RBM.Path.Expansion_norm_mul5  264-277
private RBM.Path.Expansion_K_step  279-337
private RBM.Path.Expansion_thetaGenMat  350-353
private RBM.Path.Expansion_thetaGen  355-360
private RBM.Path.Expansion_RealNonneg  362-364
private RBM.Path.Expansion_RN_zero  366-366
private RBM.Path.Expansion_RN_one  368-368
private RBM.Path.Expansion_RN_add  370-374
private RBM.Path.Expansion_RN_mul  376-380
private RBM.Path.Expansion_RN_sum  382-385
private RBM.Path.Expansion_SB_RN  387-389
private RBM.Path.Expansion_Theta_RN  391-394
private RBM.Path.Expansion_ukerMat_eq  396-405
private RBM.Path.Expansion_ukerNonneg  407-436
private RBM.Path.Expansion_norm_sum_mul_le  438-449
private RBM.Path.Expansion_sum_prod_eq_iter  451-459
private RBM.Path.Expansion_row_thetaGenMat  461-474
private RBM.Path.Expansion_row_thetaGenMat_diff  476-524
private RBM.Path.Expansion_uopOneStep  526-610
RBM.Path.Dgrid  616-623
RBM.Path.Rgrid  625-629
RBM.Path.Expansion_predInc_eq_Dgrid_add_Rgrid  631-636
private RBM.Path.Expansion_Avec_eq  638-645
private RBM.Path.Expansion_loopPM_eq  647-652
private RBM.Path.Expansion_norm_Avec_le  655-694
private RBM.Path.Expansion_arith  696-731
private RBM.Path.Expansion_STthetaOp_eq  733-750
RBM.Path.condExp_A_succ  752-932
RBM.Path.Expansion_condExp_A_succ_of_lt_one  934-949
RBM.Path.Expansion_condExp_A_succ_rpow  951-975
RBM.Path.grid_expansion_all_at  980-999
RBM.Path.grid_expansion_all  1001-1014
RBM.Path.grid_expansion_at  1016-1031
RBM.Path.grid_expansion  1033-1046
RBM.Path.gridDelta  1059-1061
RBM.Path.Expansion_loopObs  1063-1067
private RBM.Path.Expansion_linTr_Ab  1071-1088
private RBM.Path.Expansion_stepZ_gridDelta  1090-1105
RBM.Path.stepZ_eq_sum_gridDelta  1107-1121
private RBM.Path.Expansion_ukerMat_mul_eq  1123-1138
RBM.Path.stepZ_ukerMat_eq_Uker  1140-1156
private RBM.Path.Expansion_stepXi_delta  1158-1176
RBM.Path.stepXi_eq_sum_gridDelta_ae  1178-1210
RBM.Path.stepY_eq_sum_gridDelta_ae  1212-1225
RBM.Path.stepY_ukerMat_eq_Uker_ae  1227-1246
RBM.Path.Zvec  1254-1260
RBM.Path.Yvec  1262-1267
RBM.Path.Zvec_succ  1269-1273
RBM.Path.Yvec_succ  1275-1279
RBM.Path.Expansion_martInc_eq_Zvec_add_Yvec  1281-1314
RBM.Path.Expansion_uop_martInc_eq  1316-1344
RBM.Path.Expansion_uop_martInc_eq_all  1346-1376
RBM.Path.grid_expansion'_at  1378-1442
RBM.Path.grid_expansion'  1444-1465
RBM.Path.grid_expansion_all'_at  1467-1492
RBM.Path.grid_expansion_all'  1494-1515
private RBM.Path.Expansion_instS  1531-1531
private RBM.Path.Expansion_instT  1532-1532
private RBM.Path.Expansion_instK  1533-1533
private RBM.Path.Expansion_inst_gridStep  1535-1537
private RBM.Path.Expansion_inst_gridTime  1539-1543
private RBM.Path.Expansion_inst_lt_one  1545-1549
private RBM.Path.Expansion_inst_s0  1551-1552
private RBM.Path.Expansion_inst_st  1554-1555
private RBM.Path.Expansion_inst_t1  1557-1558
private RBM.Path.Expansion_inst_K  1560-1561
private RBM.Path.Expansion_inst_E  1563-1563
private RBM.Path.Expansion_inst_herm  1647-1650
### RBM3D.Path.KellStar  (10 unreached of 16)
private RBM.Path.ks_size_ge  294-299
private RBM.Path.ks_rangeCond  301-311
private RBM.Path.ks_lam_pos  313-315
private RBM.Path.ks_lam_le  317-324
private RBM.Path.ks_lam_ev  326-327
private RBM.Path.ks_ellT_le  329-342
private RBM.Path.ks_logW  344-374
private RBM.Path.ks_zdistInf  376-388
private RBM.Path.ks_far  390-403
RBM.Path.kellStarEv_instance  405-428
### RBM3D.Path.Kernel  (15 unreached of 19)
RBM.Path.Uop  49-52
RBM.Path.UopSemigroup  54-59
private RBM.Path.Kernel_norm_ofReal_mul_lt_one  67-73
RBM.Path.Uop_add  107-112
RBM.Path.Uop_smul  114-120
RBM.Path.Uop_self  122-130
RBM.Path.Uop_comp  132-160
RBM.Path.UopHom  162-165
RBM.Path.UopHom_apply  167-168
RBM.Path.uopSemigroup  172-182
RBM.Path.duhamel_telescope_stopped  234-243
RBM.Path.Uop_grid_semigroup  251-273
RBM.Path.Uop_factor  275-287
RBM.Path.Uop_duhamel_telescope  289-307
RBM.Path.Uop_duhamel_telescope_stopped  309-318
### RBM3D.Path.LemDecCalE  (15 unreached of 60)
RBM.Path.LemDecCalE_e1_rpow  493-502
RBM.Path.LemDecCalE_tailT_mono_scale  562-576
RBM.Path.LemDecCalE_lk_le  926-931
private RBM.Path.lemDecCalE_gres_zero_true  1206-1221
private RBM.Path.lemDecCalE_gres_zero  1223-1231
private RBM.Path.lemDecCalE_blockMat_zero  1233-1235
private RBM.Path.lemDecCalE_sum_block_indicator  1237-1249
private RBM.Path.lemDecCalE_trace_Eblk_mul  1251-1273
private RBM.Path.lemDecCalE_STKloop_two  1275-1284
private RBM.Path.lemDecCalE_STKloop_zero_time  1286-1295
private RBM.Path.lemDecCalE_STLM_zero_time  1297-1310
private RBM.Path.lemDecCalE_STLKM_zero_time  1312-1317
RBM.Path.LemDecCalE_e2Hyp_zero  1319-1395
private RBM.Path.lemDecCalE_inst_values  1405-1408
RBM.Path.LemDecCalE_inst  1410-1439
### RBM3D.Path.LemDecCalEdif  (16 unreached of 70)
private RBM.Path.lemDecCalEdif_gres_zero_true  1194-1209
private RBM.Path.lemDecCalEdif_gres_zero  1211-1219
private RBM.Path.lemDecCalEdif_blockMat_zero  1221-1223
private RBM.Path.lemDecCalEdif_prod_diag  1225-1245
private RBM.Path.lemDecCalEdif_norm_trace_diag  1247-1281
private RBM.Path.lemDecCalEdif_STLM_zero_time  1283-1299
private RBM.Path.lemDecCalEdif_sum_block_indicator  1301-1313
private RBM.Path.lemDecCalEdif_STLM_zero_const  1315-1349
RBM.Path.LemDecCalEdif_hyp_zero  1351-1398
private RBM.Path.lemDecCalEdif_inst_values  1408-1411
RBM.Path.LemDecCalEdif_inst_a  1413-1441
RBM.Path.LemDecCalEdif_inst_b  1443-1466
private RBM.Path.lemDecCalEdif_inst_dist  1559-1563
private RBM.Path.lemDecCalEdif_inst_dist'  1565-1568
private RBM.Path.lemDecCalEdif_inst_dist''  1570-1573
private RBM.Path.lemDecCalEdif_inst_ell  1575-1592
### RBM3D.Path.LemDecCalEdif2  (5 unreached of 30)
private RBM.Path.lemDecCalEdif2_R_pos  869-900
private RBM.Path.lemDecCalEdif2_inst_dist_a  902-906
private RBM.Path.lemDecCalEdif2_inst_dist  908-913
private RBM.Path.lemDecCalEdif2_inst_dist'  915-919
private RBM.Path.lemDecCalEdif2_inst_ell  921-939
### RBM3D.Path.LemDecCalEwG  (13 unreached of 85)
private RBM.Path.lemDecCalEwG_zdistInf_zero  101-103
private RBM.Path.lemDecCalEwG_gres_zero_true  2127-2142
private RBM.Path.lemDecCalEwG_gres_zero  2144-2152
private RBM.Path.lemDecCalEwG_blockMat_zero  2154-2156
private RBM.Path.lemDecCalEwG_sum_block_indicator  2158-2171
private RBM.Path.lemDecCalEwG_trace_three_Eblk  2173-2209
private RBM.Path.lemDecCalEwG_STLM_zero_three  2211-2228
RBM.Path.LemDecCalEwG_hyp_zero  2230-2263
private RBM.Path.lemDecCalEwG_inst_values  2274-2277
RBM.Path.LemDecCalEwG_inst  2279-2308
RBM.Path.LemDecCalEwG_inst_CL  2310-2331
private RBM.Path.lemDecCalEwG_rhs_pos  2333-2382
private RBM.Path.lemDecCalEwG_zdistInf_single  2432-2438
### RBM3D.Path.LoopStep  (7 unreached of 22)
private RBM.Path.LoopStep_instLoop  351-353
private RBM.Path.LoopStep_instLoop_wf  355-356
RBM.Path.LoopStep_check_labels_sz0  358-362
private RBM.Path.LoopStep_inst_gridTime  364-366
private RBM.Path.LoopStep_inst_gridTime_lt  368-370
RBM.Path.LoopStep_check_step_sz0  372-390
RBM.Path.LoopStep_check_drift_sz0  392-414
### RBM3D.Path.Markov  (12 unreached of 47)
RBM.Path.markov_linTrVar_one_pos  691-735
RBM.Path.markov_instOne  741-742
private RBM.Path.instGridStep  744-747
RBM.Path.markov_hasCondSubgaussianMGF_linear_sz0  749-762
RBM.Path.markov_instance_c_pos  764-768
private RBM.Path.linTr_smul_left  771-776
private RBM.Path.linTrVar_smul  778-785
RBM.Path.markov_instScale  787-789
RBM.Path.markov_instA  791-794
RBM.Path.markov_instA_bound  796-808
RBM.Path.markov_cond_subgaussian_unit_sz0  810-823
RBM.Path.markov_measurable_linTr_seqXmat_sz0  825-830
### RBM3D.Path.OneStep  (26 unreached of 134)
private RBM.Path.DriftLip_reindexHom  160-170
private RBM.Path.DriftLip_norm_blockMat  172-184
private RBM.Path.DriftLip_isHermitian_blockMat  186-189
private RBM.Path.DriftLip_blockMat_sub  191-193
private RBM.Path.OneStep_sum_norm_SB_row  274-285
private RBM.Path.DriftLip_sum_sub_le  287-304
private RBM.Path.OneStep_length_cutGlue  317-322
private RBM.Path.OneStep_wf_cutGlue  324-329
private RBM.Path.DriftLip_word_le  337-356
private RBM.Path.DriftLip_word_sub_le  358-413
private RBM.Path.DriftLip_card_real  416-419
private RBM.Path.DriftLip_norm_gloop_le  421-436
private RBM.Path.DriftLip_norm_gloop_sub_le  438-461
private RBM.Path.DriftLip_norm_trace_le  463-483
private RBM.Path.DriftLip_norm_trace_sub_le  485-508
RBM.Path.DriftLip_eGterm  516-529
RBM.Path.loopDrift  533-539
RBM.Path.loopDrift_eq  541-544
RBM.Path.driftLip  547-553
private RBM.Path.DriftLip_eGterm_sub_le  558-604
private RBM.Path.DriftLip_primRhs_sub_le  607-640
private RBM.Path.DriftLip_norm_mul_sub_mul_le  642-652
private RBM.Path.DriftLip_block_sub_le  654-791
RBM.Path.norm_loopDrift_sub_le  794-805
private RBM.Path.OneStep_instLoop  2367-2368
private RBM.Path.OneStep_instLoop_wf  2370-2370
### RBM3D.Path.QVIdentity  (42 unreached of 59)
RBM.Path.vB_nonneg_diag  99-101
private RBM.Path.QVForm_linTr_sum_smul  103-117
RBM.Path.v_sum_eq  119-167
RBM.Path.abs_vB_le  169-225
private RBM.Path.QVForm_fderiv_im_eq_zero  236-261
private RBM.Path.QVForm_seqXmat_single  263-278
RBM.Path.v_gradMat_eq_quadVar  280-312
private RBM.Path.QVForm_g  316-321
private RBM.Path.QVForm_check_differentiable  323-332
RBM.Path.QVForm_check_v_gradMat_eq_quadVar  334-346
RBM.Path.loop6  361-364
RBM.Path.EE  366-371
RBM.Path.cutDeriv1  373-377
RBM.Path.cutDeriv2  379-383
RBM.Path.loopDeriv  385-388
RBM.Path.EECutIdentity  394-405
RBM.Path.QVPropagated  407-416
RBM.Path.EEShift  418-426
private RBM.Path.QVIdentity_cm_apply  434-435
private RBM.Path.QVIdentity_trace_blockMat_mul  587-597
private RBM.Path.QVIdentity_svar_sum  630-686
private RBM.Path.QVIdentity_Gres_conjTranspose  696-713
private RBM.Path.QVIdentity_loop6_eq  715-724
private RBM.Path.QVIdentity_cut1_eq  726-744
private RBM.Path.QVIdentity_cut2_eq  746-763
private RBM.Path.QVIdentity_cut_pair  765-775
private RBM.Path.QVIdentity_greenBlk_conjTranspose  777-780
private RBM.Path.QVIdentity_SB_swap  782-788
RBM.Path.eeCutIdentity  792-823
private RBM.Path.QVIdentity_hasDerivAt_trace  832-841
private RBM.Path.QVIdentity_hasDerivAt_line  845-852
private RBM.Path.QVIdentity_loopDeriv_eq  854-900
private RBM.Path.QVIdentity_norm_add_sq_le  902-907
private RBM.Path.QVIdentity_mul_conj  909-911
RBM.Path.qvPropagated  915-962
private RBM.Path.QVIdentity_norm_foldr_le  970-984
private RBM.Path.QVIdentity_norm_foldr_sub_le  986-1033
private RBM.Path.QVIdentity_sum_norm_SB  1035-1037
private RBM.Path.QVIdentity_norm_zt_sub  1039-1045
private RBM.Path.QVIdentity_Gres_shift  1047-1086
private RBM.Path.QVIdentity_loop6_shift  1088-1109
RBM.Path.eeShift  1111-1219
### RBM3D.Path.StepDecomp  (61 unreached of 90)
private RBM.Path.StepDecomp_hermCLM  195-208
private RBM.Path.StepDecomp_hermCLM_apply  210-211
private RBM.Path.StepDecomp_isHermitian_hermCLM  213-218
private RBM.Path.StepDecomp_hermCLM_of_isHermitian  220-223
private RBM.Path.StepDecomp_isHermitian_single_diag  226-228
private RBM.Path.StepDecomp_isHermitian_S  231-233
private RBM.Path.StepDecomp_isHermitian_T  236-241
private RBM.Path.StepDecomp_contDiff_comp  243-248
private RBM.Path.StepDecomp_fderiv_comp  250-261
private RBM.Path.StepDecomp_gradMat_comp  263-272
private RBM.Path.StepDecomp_continuous_gradMat  274-282
private RBM.Path.StepDecomp_hasDerivAt_add_smul  292-295
private RBM.Path.StepDecomp_isHermitian_add_smul  297-301
private RBM.Path.StepDecomp_hasFDerivAt_fderiv_apply  303-308
private RBM.Path.StepDecomp_taylor  310-368
RBM.Path.Ab  724-731
RBM.Path.stepZ  733-740
RBM.Path.stepXi  742-751
RBM.Path.stepY  753-758
RBM.Path.lin_eq_fderiv  760-766
private RBM.Path.StepDecomp_measurable_pathH  768-771
private RBM.Path.StepDecomp_measurable_seqXmat  773-776
private RBM.Path.StepDecomp_pathH_succ  778-788
private RBM.Path.StepDecomp_measurable_phi_filt  791-802
private RBM.Path.StepDecomp_integrable_phi  804-813
private RBM.Path.StepDecomp_fderiv_im_eq_zero  815-834
private RBM.Path.StepDecomp_measurable_Ab  836-852
private RBM.Path.StepDecomp_Rlabel  854-860
private RBM.Path.StepDecomp_norm_Rlabel_le  862-875
private RBM.Path.StepDecomp_measurable_Rlabel  877-900
private RBM.Path.StepDecomp_norm_Rlabel_sum_le  902-927
private RBM.Path.StepDecomp_integrable_Rlabel_sum  929-947
private RBM.Path.StepDecomp_lin_Ab_eq_sum  949-966
private RBM.Path.StepDecomp_sum_fderiv_eq_stepZ  968-999
private RBM.Path.StepDecomp_condExp_stepZ_eq_zero  1001-1023
private RBM.Path.StepDecomp_g_eq_pointwise  1025-1050
private RBM.Path.StepDecomp_measurable_h0  1052-1060
private RBM.Path.StepDecomp_integrable_h0  1062-1070
private RBM.Path.StepDecomp_integrable_stepZ_complex  1072-1078
private RBM.Path.StepDecomp_stepXi_eq_ae  1080-1124
private RBM.Path.StepDecomp_stepY_eq_ae  1126-1144
private RBM.Path.StepDecomp_stepY_norm_le_ae  1146-1178
RBM.Path.stepDecomp  1180-1228
RBM.Path.stepDecomp_Y_sq  1230-1292
RBM.Path.stepDecomp_Z_subG  1294-1307
RBM.Path.stepDecomp_integrable_stepZ  1309-1333
private RBM.Path.StepDecomp_g  1348-1353
private RBM.Path.StepDecomp_g_apply  1355-1356
private RBM.Path.StepDecomp_check_hasFDerivAt  1358-1361
private RBM.Path.StepDecomp_check_fderiv  1363-1367
private RBM.Path.StepDecomp_check_fderiv_apply  1369-1373
private RBM.Path.StepDecomp_check_fderiv2  1375-1385
private RBM.Path.StepDecomp_check_gradMat  1388-1398
private RBM.Path.StepDecomp_checkΦ  1404-1407
private RBM.Path.StepDecomp_diag  1409-1411
private RBM.Path.StepDecomp_check_class  1413-1420
private RBM.Path.StepDecomp_check_hC₂  1422-1440
RBM.Path.StepDecomp_check_stepDecomp  1442-1474
private RBM.Path.StepDecomp_linTrVar_smul  1477-1486
RBM.Path.StepDecomp_check_Z_subG  1488-1517
RBM.Path.StepDecomp_check_trace_not_hermTestFun  1580-1598
### RBM3D.Path.StepDecompLoop  (35 unreached of 49)
private RBM.Path.StepDecompLoop_blockMat_add_smul  72-75
private RBM.Path.StepDecompLoop_blockCLM_apply  85-86
private RBM.Path.StepDecompLoop_reindexHom  88-98
private RBM.Path.StepDecompLoop_norm_blockMat  100-112
private RBM.Path.StepDecompLoop_isHermitian_blockMat  114-116
private RBM.Path.StepDecompLoop_obs  118-124
private RBM.Path.StepDecompLoop_loopPM_eq  126-128
private RBM.Path.StepDecompLoop_trCLM_apply  143-144
private RBM.Path.StepDecompLoop_contDiffAt_Gres  335-356
private RBM.Path.StepDecompLoop_contDiffAt_obs  358-382
private RBM.Path.StepDecompLoop_line_jets  384-436
private RBM.Path.StepDecompLoop_second_deriv_bound  438-452
private RBM.Path.StepDecompLoop_first_deriv_bound  454-470
private RBM.Path.StepDecompLoop_RealNonneg  480-483
private RBM.Path.StepDecompLoop_RN_zero  485-485
private RBM.Path.StepDecompLoop_RN_one  487-487
private RBM.Path.StepDecompLoop_RN_add  489-493
private RBM.Path.StepDecompLoop_RN_mul  495-499
private RBM.Path.StepDecompLoop_RN_sum  501-504
private RBM.Path.StepDecompLoop_SB_RN  506-509
private RBM.Path.StepDecompLoop_Theta_RN  511-514
private RBM.Path.StepDecompLoop_ukerMat_eq  516-526
private RBM.Path.StepDecompLoop_ukerNonneg  528-558
private RBM.Path.StepDecompLoop_weight_nonneg  566-580
RBM.Path.hermTestFun_loopPM  598-658
RBM.Path.loopPM_real_of_herm  660-684
RBM.Path.stepDecomp_loopPM  686-782
RBM.Path.stepDecomp_Z_subG_loopPM  784-807
private RBM.Path.StepDecompLoop_sizes  823-829
private RBM.Path.StepDecompLoop_Phi  831-835
private RBM.Path.StepDecompLoop_Uw  837-841
private RBM.Path.StepDecompLoop_linTr_sum  843-849
private RBM.Path.StepDecompLoop_linTrVar_eq_sum  851-857
private RBM.Path.StepDecompLoop_exists_variance_bound  859-916
private RBM.Path.StepDecompLoop_check_Z_subG  936-954
### RBM3D.Path.Stop  (6 unreached of 15)
RBM.Path.isStoppingTime_min_firstHit  88-101
RBM.Path.lt_min_firstHit_measurableSet  103-120
RBM.Path.lt_min_firstHit_imp  122-128
RBM.Path.isStoppingTime_firstHit_grid  173-181
RBM.Path.isStoppingTime_min_firstHit_grid  193-203
RBM.Path.lt_min_firstHit_grid_measurableSet  205-215
### RBM3D.Path.UBounds  (46 unreached of 47)
RBM.Path.thetaGen  56-59
RBM.Path.UopOneStep  63-69
RBM.Path.NormSqSpectralMOne  71-74
RBM.Path.UkerNonneg  76-81
RBM.Path.UkerRowSum  83-86
RBM.Path.SumNdecay  88-92
RBM.Path.SumNdecayEta  94-99
RBM.Path.UopBack  101-106
private RBM.Path.RealNonneg  114-116
private RBM.Path.RealNonneg.ofNonneg  118-118
private RBM.Path.realNonneg_zero  120-120
private RBM.Path.realNonneg_one  122-122
private RBM.Path.RealNonneg.add  124-128
private RBM.Path.RealNonneg.mul  130-134
private RBM.Path.RealNonneg.sum  136-138
private RBM.Path.SB_realNonneg  141-146
private RBM.Path.Theta_real_realNonneg  148-152
private RBM.Path.SB_mul_Theta_real_realNonneg  154-158
private RBM.Path.norm_ofReal_mul_eq  164-166
private RBM.Path.norm_ofReal_mul_lt  168-174
private RBM.Path.norm_eq_re_of  176-180
private RBM.Path.arith_gen  182-190
private RBM.Path.arith_inv  192-197
private RBM.Path.ukerMat_eq  205-213
private RBM.Path.ukerMat_apply_eq  215-221
private RBM.Path.thetaGenMat_realNonneg  223-230
private RBM.Path.sum_norm_row_le_opNorm  240-248
private RBM.Path.norm_Theta_le_of_lt  250-266
private RBM.Path.sum_norm_thetaGenMat_row_le  268-282
private RBM.Path.sum_norm_thetaGenMat_diff_row_le  284-328
private RBM.Path.norm_sum_mul_le  336-347
private RBM.Path.sum_prod_eq_iter  349-357
private RBM.Path.norm_sum_prod_le  359-364
private RBM.Path.norm_Uop_le_of_rows  366-372
RBM.Path.normSqSpectralMOne  378-382
RBM.Path.ukerNonneg  384-405
RBM.Path.ukerRowSum  407-427
private RBM.Path.ukerMat_row_norm_eq  429-440
RBM.Path.sumNdecay  442-448
private RBM.Path.etaT_div_etaT'  450-453
RBM.Path.sumNdecayEta  455-462
private RBM.Path.sum_norm_ukerMat_back_row_le  464-509
RBM.Path.uopBack  511-518
RBM.Path.uopOneStep  520-622
private RBM.Path.instA  633-634
private RBM.Path.instA_le  636-638
### RBM3D.Path.UTransport  (17 unreached of 17)
RBM.Path.UkerFar  42-45
RBM.Path.UopLocalMax  47-56
RBM.Path.UopPairLocalMax  58-70
private RBM.Path.uT_norm_eq_re_of  78-82
private RBM.Path.uT_row_sum  84-99
private RBM.Path.uTF  101-103
private RBM.Path.uTF_nonneg  106-107
private RBM.Path.uTF_eq_one  110-112
private RBM.Path.uTF_eq_zero  115-117
private RBM.Path.uT_far_sum_le  119-132
private RBM.Path.uT_sum2  134-137
private RBM.Path.uT_sum4  139-146
RBM.Path.uopLocalMax  152-215
RBM.Path.uopPairLocalMax  217-312
private RBM.Path.uT_zdistInf_eq_zero  324-329
private RBM.Path.uT_eq_of_lt_one  331-335
private RBM.Path.uT_inst_far  337-346
### RBM3D.Path.Walk  (21 unreached of 72)
RBM.Path.IndepIncr  88-92
RBM.Gauss.Sizes.PrecGrid  119-124
RBM.Gauss.Sizes.precGrid_of_le  126-139
RBM.Path.indepIncr  269-270
RBM.Path.GridTransferPT  657-673
private RBM.Path.transfer_measurable_pathH  675-677
private RBM.Path.transfer_measurable_seqHflow  679-681
RBM.Path.gridTransferPT  683-705
RBM.Path.WalkInst.gridTime_sz0  839-842
RBM.Path.WalkInst.gridTime_last_sz0  844-847
RBM.Path.WalkInst.transferLaw_sz0  849-857
RBM.Path.WalkInst.transferLaw_pin_sz0  859-860
RBM.Path.WalkInst.indepIncr_sz0  862-866
RBM.Path.WalkInst.indepIncr_pin_sz0  868-869
RBM.Path.WalkInst.map_incr_sz0  871-873
RBM.Path.WalkInst.gridRes_prec  875-891
RBM.Path.WalkInst.Fres  893-897
RBM.Path.WalkInst.Zres  899-900
RBM.Path.WalkInst.Fres_measurable  902-903
RBM.Path.WalkInst.gridTime_le_half  905-912
RBM.Path.WalkInst.gridTransferPT_sz0  914-945
### RBM3D.Propagator.Basic  (1 unreached of 17)
RBM.Theta_isSymm  114-116
### RBM3D.Propagator.Gap  (18 unreached of 23)
RBM.sbKernelR_pos  116-130
RBM.SBR_pow_pos  132-178
RBM.exists_doeblin  180-199
RBM.sum_SBR_pow_row  210-227
RBM.SBR_isSymm  234-236
RBM.SBR_pow_comm  238-240
RBM.sum_SBR_pow_col  242-245
RBM.osc  249-251
RBM.le_sup_osc  253-255
RBM.inf_osc_le  257-259
RBM.osc_nonneg  261-264
RBM.osc_mulVec_le  266-318
RBM.osc_mulVec_pow_le  320-336
RBM.exists_mixing  338-448
RBM.sum_range_pow_div  456-471
RBM.summable_pow_div  473-495
RBM.exists_norm_Theta0_le  498-548
RBM.exists_norm_Theta_sub_le  557-602
### RBM3D.Propagator.HeatBounds1D  (2 unreached of 43)
private RBM.Heat.rpow_hundred_neg_half  804-808
private RBM.Heat.rpow_hundred_neg_three_halves  810-814
### RBM3D.Propagator.HeatKernel1D  (3 unreached of 17)
private RBM.Heat.walkCount_neg  56-77
RBM.Heat.hkZ_neg  144-147
RBM.Heat.hkZ_mass  220-230
### RBM3D.Propagator.Interface  (3 unreached of 3)
RBM.ThetaDecay  62-77
RBM.ThetaDecayShort  79-101
RBM.ThetaZeroMode  103-115
### RBM3D.Propagator.LaplaceGauss  (7 unreached of 40)
RBM.Heat.LGKey  41-48
RBM.Heat.LGBulk  50-60
RBM.Heat.LGZero  62-67
RBM.Heat.LGTail  69-81
RBM.Heat.LGConvA  83-89
RBM.Heat.LGConvB  91-96
RBM.Heat.LGConvC  98-103
### RBM3D.Propagator.Pins  (8 unreached of 16)
RBM.Prop5_needs_Lambda  115-149
private RBM.pins_exists_sq  160-168
RBM.Prop5Short.thetaDecayShort  170-177
RBM.Prop5Decay.thetaDecay  179-186
RBM.Prop8ZeroMode.thetaZeroMode  188-203
RBM.PropThetaQ_Theta_eq  218-221
RBM.Prop5DecayQ  224-232
RBM.Prop5Decay.toQ  234-241
### RBM3D.Propagator.Prop6Hold  (9 unreached of 24)
RBM.thetaDecay_holds  437-439
RBM.thetaDecayShort_holds  441-444
RBM.thetaZeroMode_holds  446-451
private RBM.p6h_exists_sq  453-461
private RBM.p6h_exists_spin  463-485
RBM.thetaZeroMode_unit_holds  487-494
private RBM.p6h_inst_a  502-502
private RBM.p6h_inst_r  504-504
private RBM.p6h_inst_hr  506-510
### RBM3D.Propagator.Props4  (2 unreached of 28)
RBM.sum_Theta0_row  260-271
RBM.sum_Theta_shift  273-277
### RBM3D.Test.InterfaceShape  (7 unreached of 7)
RBM.Test.not_decayShort_at_one  46-109
RBM.Test.not_zeroMode_without_removal  111-183
RBM.Test.thetaDecay_fixedL  223-280
RBM.Test.exists_norm_Theta_ge  282-304
RBM.Test.not_exists_uniform_entry_bound  306-344
RBM.Test.sum_Theta_diff_row  346-352
RBM.Test.thetaZeroMode_fixedL  354-418
### RBM3D.Universality.Apriori  (7 unreached of 12)
RBM.Univ.unApriori_band_of_rows  335-342
RBM.Univ.AprioriInst.inst_unApriori_band_zero  353-359
RBM.Univ.AprioriInst.inst_unApriori_band_one  361-366
RBM.Univ.AprioriInst.inst_im_le_of_near  368-376
RBM.Univ.AprioriInst.inst_bctl_le  378-389
RBM.Univ.AprioriInst.inst_im_bounds  391-396
RBM.Univ.AprioriInst.inst_ouMat_zero_integral  398-403
### RBM3D.Universality.EMCTE2  (7 unreached of 41)
private RBM.Univ.EMCTE2_BM_hsum  273-284
private RBM.Univ.EMCTE2_hsum_bdd  288-299
RBM.Univ.unEMCTE2Rowk_band  688-694
RBM.Univ.EMCTE2Inst.inst_eq225_interval  710-747
RBM.Univ.EMCTE2Inst.inst_unEMCTE2_sz0  749-750
RBM.Univ.EMCTE2Inst.inst_unEMCTE2Row_sz0  752-755
RBM.Univ.EMCTE2Inst.inst_unEMCTE2Rowk_band_sz0  757-763
### RBM3D.Universality.EigenInterlacing  (4 unreached of 31)
RBM.Univ.EigenInterlacingInst.A3  641-642
RBM.Univ.EigenInterlacingInst.A3_isHermitian  644-646
RBM.Univ.EigenInterlacingInst.A3_minor  648-651
RBM.Univ.EigenInterlacingInst.A3_eigenpairs  654-675
### RBM3D.Universality.EigenMeasurable  (15 unreached of 41)
private RBM.Univ.EigenMeasurable.corrSumVal_eq  402-407
RBM.Univ.EigenMeasurableCheck.A3  489-490
RBM.Univ.EigenMeasurableCheck.B3  492-493
RBM.Univ.EigenMeasurableCheck.A3_herm  495-496
RBM.Univ.EigenMeasurableCheck.B3_herm  498-499
RBM.Univ.EigenMeasurableCheck.A3_ne_B3  501-504
private RBM.Univ.EigenMeasurableCheck.O2_cont  512-514
RBM.Univ.EigenMeasurableCheck.Hw  516-517
RBM.Univ.EigenMeasurableCheck.Hw_herm  519-520
RBM.Univ.EigenMeasurableCheck.measurable_Hw  522-524
private RBM.Univ.EigenMeasurableCheck.measurable_Hband  553-554
RBM.Univ.EigenMeasurableCheck.T3aStmt  567-572
RBM.Univ.EigenMeasurableCheck.T3bStmt  574-581
RBM.Univ.EigenMeasurableCheck.T3aStmt_holds  583-583
RBM.Univ.EigenMeasurableCheck.T3bStmt_holds  585-585
### RBM3D.Universality.FreeConv  (9 unreached of 23)
private RBM.Univ.freeConv_card_ne_zero  53-55
RBM.Univ.exists_isFreeConv32  669-673
RBM.Univ.isFreeConv32_unique  675-679
RBM.Univ.FreeConvCheck.v3  688-689
RBM.Univ.FreeConvCheck.z0  691-692
RBM.Univ.FreeConvCheck.z0_im  694-694
RBM.Univ.FreeConvCheck.v0  720-721
RBM.Univ.FreeConvCheck.z1  723-724
RBM.Univ.FreeConvCheck.z1_im  726-726
### RBM3D.Universality.FreeConvRegular  (11 unreached of 54)
RBM.Univ.freeConvST_norm_sq_le  308-318
private RBM.Univ.FreeConvRegular_norm_horiz  357-360
private RBM.Univ.FreeConvRegular_lip_one  362-371
private RBM.Univ.FreeConvRegular_norm_le_one  373-380
RBM.Univ.unDens_freeConvST  384-462
RBM.Univ.unDens_not_eta_determined  466-504
RBM.Univ.freeConv_stable_freeConvST  1258-1289
RBM.Univ.FreeConvRegularInst.uI  1347-1348
RBM.Univ.FreeConvRegularInst.uI_lower  1350-1376
RBM.Univ.FreeConvRegularInst.stable_lip_msc  1388-1421
RBM.Univ.FreeConvRegularInst.stable_freeConvST_uI  1438-1458
### RBM3D.Universality.GUEInvariance  (9 unreached of 104)
private RBM.Univ.GUE_real_smul  217-217
private RBM.Univ.GUE_Tpp_eucl_apply  780-783
private RBM.Univ.GUE_Xmat_apply  827-828
RBM.Univ.GUEInvarianceCheck.phaseU  1014-1016
RBM.Univ.GUEInvarianceCheck.phaseU_mem  1018-1028
RBM.Univ.GUEInvarianceCheck.phaseU_not_scalar  1030-1053
RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_one  1056-1059
RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_phase  1063-1066
RBM.Univ.GUEInvarianceCheck.isProbabilityMeasure_map_Xmat  1069-1071
### RBM3D.Universality.GUELocalBootstrap  (13 unreached of 67)
RBM.Univ.GUELocalBootstrapInst.inst_schurTail  1011-1024
RBM.Univ.GUELocalBootstrapInst.inst_Nsz_zero  1026-1030
RBM.Univ.GUELocalBootstrapInst.inst_grid_nonempty  1032-1034
RBM.Univ.GUELocalBootstrapInst.inst_grid_nonempty_sz0  1036-1038
RBM.Univ.GUELocalBootstrapInst.inst_glSmall  1040-1043
RBM.Univ.GUELocalBootstrapInst.inst_gueLocal  1045-1053
RBM.Univ.GUELocalBootstrapInst.inst_glSmall_witness  1055-1087
private RBM.Univ.GUELocalBootstrapInst.GUELocalBootstrap_green_zero_unit  1130-1137
private RBM.Univ.GUELocalBootstrapInst.GUELocalBootstrap_stieltjesN_zero_unit  1139-1144
private RBM.Univ.GUELocalBootstrapInst.GUELocalBootstrap_schurErr_zero_unit  1146-1150
private RBM.Univ.GUELocalBootstrapInst.GUELocalBootstrap_norm_schurErr_zero_unit  1152-1158
private RBM.Univ.GUELocalBootstrapInst.GUELocalBootstrap_near_zero_unit  1166-1173
private RBM.Univ.GUELocalBootstrapInst.GUELocalBootstrap_cGap_two  1188-1191
### RBM3D.Universality.GUELocalSchur  (15 unreached of 31)
RBM.Univ.gueLocal  589-591
RBM.Univ.GUELocalSchurInst.H3  608-609
RBM.Univ.GUELocalSchurInst.H3_isHermitian  611-613
RBM.Univ.GUELocalSchurInst.green_diagonal  615-630
RBM.Univ.GUELocalSchurInst.H3_ne_I  632-633
RBM.Univ.GUELocalSchurInst.H3_minor  635-638
RBM.Univ.GUELocalSchurInst.H3_minor_green  640-644
RBM.Univ.GUELocalSchurInst.H3_Q  646-654
RBM.Univ.GUELocalSchurInst.H3_trace  656-670
RBM.Univ.GUELocalSchurInst.H3_hmim  672-677
RBM.Univ.GUELocalSchurInst.H3_hdiag  679-684
RBM.Univ.GUELocalSchurInst.H3_hquad  686-706
RBM.Univ.GUELocalSchurInst.one_le_Nsz  729-735
RBM.Univ.GUELocalSchurInst.schurBud_sz0_zero  737-760
RBM.Univ.GUELocalSchurInst.final_arith_h2  770-783
### RBM3D.Universality.GUEPhase.AuxCarrier  (23 unreached of 110)
RBM.Univ.auxHG_law  245-253
RBM.Univ.exists_seqP_map_eq_gaussLaw  257-262
RBM.Univ.PF_eq_gaussLaw  277-277
RBM.Univ.mixVar_exp_eq_ouVar  290-291
RBM.Univ.mixVar_zero_right  318-320
RBM.Univ.mixVar_zero_left  322-324
RBM.Univ.gvarF_tagFree  332-332
RBM.Univ.kind_quad_tail  979-991
RBM.Univ.AuxCarrierCheck.inst_svarF_pos_of_block_eq  1216-1222
RBM.Univ.AuxCarrierCheck.inst_aux_pos  1224-1229
RBM.Univ.AuxCarrierCheck.inst_auxT_law  1231-1235
RBM.Univ.AuxCarrierCheck.inst_auxHG_law  1237-1241
RBM.Univ.AuxCarrierCheck.inst_exists_seqP_map_eq_gaussLaw  1243-1247
RBM.Univ.AuxCarrierCheck.inst_chaos_tail  1249-1259
RBM.Univ.AuxCarrierCheck.inst_gue_quad_tail  1261-1275
RBM.Univ.AuxCarrierCheck.inst_band_quad_tail  1277-1286
RBM.Univ.AuxCarrierCheck.inst_shift_quad_tail  1288-1297
RBM.Univ.AuxCarrierCheck.inst_kind_quad_tail_band  1299-1316
RBM.Univ.AuxCarrierCheck.inst_kind_quad_tail_band_size  1318-1322
RBM.Univ.AuxCarrierCheck.inst_aux_lin_tail  1324-1340
RBM.Univ.AuxCarrierCheck.inst_sum_Smix_row  1342-1347
RBM.Univ.AuxCarrierCheck.inst_mixVar_exp_eq_ouVar  1349-1352
RBM.Univ.AuxCarrierCheck.inst_bounds  1354-1360
### RBM3D.Universality.GUEPhase.Bootstrap  (33 unreached of 64)
RBM.Univ.GUEPhase.sum_SBgue_row  67-72
RBM.Univ.GUEPhase.ellT_eq_L  144-159
RBM.Univ.GUEPhase.BootstrapCheck.loopThree  616-618
RBM.Univ.GUEPhase.BootstrapCheck.loopThree_WF  620-620
RBM.Univ.GUEPhase.BootstrapCheck.loopThree_length  622-622
RBM.Univ.GUEPhase.BootstrapCheck.primBilGUE_zero_left  624-626
RBM.Univ.GUEPhase.BootstrapCheck.primRhsGUE_zero  628-630
RBM.Univ.GUEPhase.BootstrapCheck.inst_sum_SBgue_col  632-634
RBM.Univ.GUEPhase.BootstrapCheck.inst_sum_SBgue_row  636-638
RBM.Univ.GUEPhase.BootstrapCheck.inst_continuity_argument  640-646
RBM.Univ.GUEPhase.BootstrapCheck.inst_K_bootstrap  648-668
RBM.Univ.GUEPhase.BootstrapCheck.inst_norm_primBilGUE_le_zero  670-679
RBM.Univ.GUEPhase.BootstrapCheck.inst_norm_primBilGUE_le_one  681-690
RBM.Univ.GUEPhase.BootstrapCheck.inst_norm_primRhsGUE_le  692-699
RBM.Univ.GUEPhase.BootstrapCheck.inst_eq736  701-721
RBM.Univ.GUEPhase.BootstrapCheck.inst_ellT_eq_L  723-727
RBM.Univ.GUEPhase.BootstrapCheck.inst_finite_loopIdx  729-733
RBM.Univ.GUEPhase.BootstrapCheck.inst_eventually_small  735-739
RBM.Univ.GUEPhase.BootstrapCheck.inst_eventually_rpow_le_of_neg  741-743
RBM.Univ.GUEPhase.BootstrapCheck.inst_sum_pow_mul_pow  745-749
RBM.Univ.GUEPhase.BootstrapCheck.inst_supOn_le  751-753
RBM.Univ.GUEPhase.BootstrapCheck.inst_supOn_nonneg  755-757
RBM.Univ.GUEPhase.BootstrapCheck.inst_inv_mul_pow  759-761
RBM.Univ.GUEPhase.BootstrapCheck.inst_mul_le_of_eq730  763-767
RBM.Univ.GUEPhase.BootstrapCheck.inst_sqrt_mul_sqrt_le  769-774
RBM.Univ.GUEPhase.BootstrapCheck.inst_supOn_line1_le  776-788
RBM.Univ.GUEPhase.BootstrapCheck.inst_bounds  790-797
RBM.Univ.GUEPhase.BootstrapCheck.kTight  799-801
RBM.Univ.GUEPhase.BootstrapCheck.kTight_hasDerivAt  803-812
RBM.Univ.GUEPhase.BootstrapCheck.primRhsGUE_const_len_two  814-822
RBM.Univ.GUEPhase.BootstrapCheck.kTight_zero  824-824
RBM.Univ.GUEPhase.BootstrapCheck.kTight_one  826-827
RBM.Univ.GUEPhase.BootstrapCheck.inst_eq736_tight  829-857
### RBM3D.Universality.GUEPhase.BootstrapAt  (50 unreached of 61)
RBM.Univ.GUEPhase.unifDetDom_iff_at_id  538-541
RBM.Univ.GUEPhase.eq736_detDomAt  570-614
RBM.Univ.GUEPhase.BootstrapAtCheck.sizeD  765-766
RBM.Univ.GUEPhase.BootstrapAtCheck.sizeD_tendsto  768-769
RBM.Univ.GUEPhase.BootstrapAtCheck.sizeD_pos  771-772
RBM.Univ.GUEPhase.BootstrapAtCheck.sizeD_one_le  774-775
RBM.Univ.GUEPhase.BootstrapAtCheck.zero_stochDomAt  777-787
RBM.Univ.GUEPhase.BootstrapAtCheck.NfD  789-792
RBM.Univ.GUEPhase.BootstrapAtCheck.etaD  794-794
RBM.Univ.GUEPhase.BootstrapAtCheck.t1D  796-796
RBM.Univ.GUEPhase.BootstrapAtCheck.t0D  798-798
RBM.Univ.GUEPhase.BootstrapAtCheck.NfD_pos  800-800
RBM.Univ.GUEPhase.BootstrapAtCheck.t10D  802-802
RBM.Univ.GUEPhase.BootstrapAtCheck.t0D_le_one  804-807
RBM.Univ.GUEPhase.BootstrapAtCheck.lamD  809-810
RBM.Univ.GUEPhase.BootstrapAtCheck.rhs746G_zero_nonneg  812-815
RBM.Univ.GUEPhase.BootstrapAtCheck.rhs745G_zero_nonneg  817-820
RBM.Univ.GUEPhase.BootstrapAtCheck.ctrlD_nonneg  822-823
RBM.Univ.GUEPhase.BootstrapAtCheck.h730At  825-830
RBM.Univ.GUEPhase.BootstrapAtCheck.hscaleAt  832-835
RBM.Univ.GUEPhase.BootstrapAtCheck.ctrlAt_nonneg  837-839
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_unifDetDom_iff_at_id  841-847
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_eventually_size_rpow_le_of_neg  849-852
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_stochDomAt_of_forall_highProbAt  854-862
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_eq736_detDomAt_zero  864-893
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_eq736_detDomAt_tight  895-934
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_bounds  936-954
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_eq728GAt_zero  956-969
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_eq727GEAt_zero  971-984
RBM.Univ.GUEPhase.BootstrapAtCheck.xD  991-992
RBM.Univ.GUEPhase.BootstrapAtCheck.xD_eq  994-995
RBM.Univ.GUEPhase.BootstrapAtCheck.xD_nonneg  997-998
RBM.Univ.GUEPhase.BootstrapAtCheck.xD_pos  1000-1001
RBM.Univ.GUEPhase.BootstrapAtCheck.xD_le_one  1003-1004
RBM.Univ.GUEPhase.BootstrapAtCheck.LmD  1006-1006
RBM.Univ.GUEPhase.BootstrapAtCheck.DmD  1008-1008
RBM.Univ.GUEPhase.BootstrapAtCheck.KmD  1010-1010
RBM.Univ.GUEPhase.BootstrapAtCheck.LmD_nonneg  1012-1013
RBM.Univ.GUEPhase.BootstrapAtCheck.DmD_nonneg  1015-1016
RBM.Univ.GUEPhase.BootstrapAtCheck.LmD_cont  1018-1019
RBM.Univ.GUEPhase.BootstrapAtCheck.DmD_cont  1021-1022
RBM.Univ.GUEPhase.BootstrapAtCheck.KmD_le  1024-1025
RBM.Univ.GUEPhase.BootstrapAtCheck.DmD_le_LmD_add_KmD  1027-1034
RBM.Univ.GUEPhase.BootstrapAtCheck.LmD_odd  1036-1042
RBM.Univ.GUEPhase.BootstrapAtCheck.DmD_le_rhs745G  1044-1064
RBM.Univ.GUEPhase.BootstrapAtCheck.DmD_le_rhs746G  1066-1086
RBM.Univ.GUEPhase.BootstrapAtCheck.rhs745G_nonneg  1088-1091
RBM.Univ.GUEPhase.BootstrapAtCheck.rhs746G_nonneg  1093-1096
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_eq727GEAt_pos  1098-1121
RBM.Univ.GUEPhase.BootstrapAtCheck.inst_eq728GAt_chain  1123-1136
### RBM3D.Universality.GUEPhase.BoundsA  (11 unreached of 40)
private RBM.Univ.GUEPhase.BoundsAInst.Inst_size_real  771-773
private RBM.Univ.GUEPhase.BoundsAInst.Inst_le_rpow  775-784
private RBM.Univ.GUEPhase.BoundsAInst.E0  786-788
private RBM.Univ.GUEPhase.BoundsAInst.t1c  789-789
private RBM.Univ.GUEPhase.BoundsAInst.t0c  790-790
private RBM.Univ.GUEPhase.BoundsAInst.Inst_im  792-797
private RBM.Univ.GUEPhase.BoundsAInst.Inst_hscN  799-821
private RBM.Univ.GUEPhase.BoundsAInst.Inst_hsmallN  823-831
private RBM.Univ.GUEPhase.BoundsAInst.Inst_h4N  833-841
private RBM.Univ.GUEPhase.BoundsAInst.Inst_hellN  843-845
RBM.Univ.GUEPhase.BoundsAInst.highProbAt_hF_sz0  873-878
### RBM3D.Universality.GUEPhase.Drift  (15 unreached of 79)
private RBM.Univ.GUEPhase.DriftInst.DriftInst_loop1  1365-1366
private RBM.Univ.GUEPhase.DriftInst.DriftInst_loop1_wf  1368-1368
RBM.Univ.GUEPhase.DriftInst.oneStepEnvelopeGUE_check  1370-1381
private RBM.Univ.GUEPhase.DriftInst.DriftInst_loop2  1383-1385
private RBM.Univ.GUEPhase.DriftInst.DriftInst_loop2_wf  1387-1388
RBM.Univ.GUEPhase.DriftInst.labels_sz0  1390-1394
private RBM.Univ.GUEPhase.DriftInst.DriftInst_t1  1396-1397
private RBM.Univ.GUEPhase.DriftInst.DriftInst_t0  1399-1399
private RBM.Univ.GUEPhase.DriftInst.DriftInst_K  1401-1401
private RBM.Univ.GUEPhase.DriftInst.DriftInst_t1_nonneg  1403-1406
private RBM.Univ.GUEPhase.DriftInst.DriftInst_t1_le_t0  1408-1411
private RBM.Univ.GUEPhase.DriftInst.DriftInst_gridTime_lt  1413-1419
RBM.Univ.GUEPhase.DriftInst.gueH_succ_check  1421-1427
RBM.Univ.GUEPhase.DriftInst.condExp_loop_step_gue_check  1429-1446
RBM.Univ.GUEPhase.DriftInst.condExp_loop_drift_gue_check  1448-1470
### RBM3D.Universality.GUEPhase.DuhamelA1  (15 unreached of 80)
private RBM.Univ.GUEPhase.Duhamel_coordinateMatrix_apply  76-79
private RBM.Univ.GUEPhase.Duhamel_gloopProd_eq  330-331
private RBM.Univ.GUEPhase.DuhamelA1Inst.DuhamelA1Inst_loop1  1132-1133
private RBM.Univ.GUEPhase.DuhamelA1Inst.DuhamelA1Inst_loop1_wf  1135-1135
private RBM.Univ.GUEPhase.DuhamelA1Inst.DuhamelA1Inst_Idx0  1137-1138
RBM.Univ.GUEPhase.DuhamelA1Inst.frobSq_one_sz0  1140-1149
RBM.Univ.GUEPhase.DuhamelA1Inst.vGue_le_inst  1151-1155
RBM.Univ.GUEPhase.DuhamelA1Inst.vGue_le_inst_value  1157-1160
RBM.Univ.GUEPhase.DuhamelA1Inst.loopMax_le_crude_inst  1162-1167
RBM.Univ.GUEPhase.DuhamelA1Inst.loopMax_zero_eq  1169-1189
RBM.Univ.GUEPhase.DuhamelA1Inst.loopMax_shift_le_inst  1191-1207
RBM.Univ.GUEPhase.DuhamelA1Inst.loopCut_loop1  1209-1215
RBM.Univ.GUEPhase.DuhamelA1Inst.frobSq_loopCut_le_inst  1217-1225
RBM.Univ.GUEPhase.DuhamelA1Inst.vGue_gradMat_le_inst  1227-1240
RBM.Univ.GUEPhase.DuhamelA1Inst.contDiffAt_loop_inst  1242-1246
### RBM3D.Universality.GUEPhase.DuhamelA2  (28 unreached of 85)
RBM.Univ.GUEPhase.DuhamelA2Inst.zero_mem_good  1114-1120
RBM.Univ.GUEPhase.DuhamelA2Inst.exists_not_mem_good  1122-1133
RBM.Univ.GUEPhase.DuhamelA2Inst.measurableSet_good_check  1135-1140
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_loop2  1144-1146
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_loop2_wf  1148-1149
RBM.Univ.GUEPhase.DuhamelA2Inst.labels_sz0  1151-1152
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_t1  1154-1154
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_t0  1156-1156
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_K  1158-1158
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_t1_nonneg  1160-1163
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_t1_le_t0  1165-1168
RBM.Univ.GUEPhase.DuhamelA2Inst.drift_remainder_ae_check  1170-1195
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_g  1203-1208
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_Φ  1210-1212
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_continuous_Φ  1214-1216
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_hasFDerivAt  1218-1221
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_fderiv  1223-1227
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_fderiv2  1229-1239
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_hC₂  1241-1254
private RBM.Univ.GUEPhase.DuhamelA2Inst.DuhamelA2Inst_class  1256-1264
RBM.Univ.GUEPhase.DuhamelA2Inst.Z_re_im_check  1268-1277
RBM.Univ.GUEPhase.DuhamelA2Inst.measurable_R_check  1279-1285
RBM.Univ.GUEPhase.DuhamelA2Inst.integral_step_check  1287-1296
RBM.Univ.GUEPhase.DuhamelA2Inst.norm_T_le_check  1298-1305
RBM.Univ.GUEPhase.DuhamelA2Inst.norm_B_le_check  1307-1314
RBM.Univ.GUEPhase.DuhamelA2Inst.measurable_loop_check  1316-1320
RBM.Univ.GUEPhase.DuhamelA2Inst.measurable_coord_check  1322-1324
RBM.Univ.GUEPhase.DuhamelA2Inst.gueH_measurable_filt_check  1326-1330
### RBM3D.Universality.GUEPhase.DuhamelB  (24 unreached of 67)
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_t1  1052-1052
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_t0  1053-1053
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_K  1054-1054
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_loop  1055-1055
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_t1_nonneg  1057-1060
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_t1_le_t0  1062-1065
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_Δ  1067-1067
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_z  1069-1070
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_mE_im  1072-1075
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_eta  1077-1080
RBM.Univ.GUEPhase.DuhamelBInst.grid_facts_check  1082-1094
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_Δ_le  1096-1101
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_Δ_nonneg  1103-1103
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_im_ge  1105-1106
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_v_nonneg  1108-1110
RBM.Univ.GUEPhase.DuhamelBInst.bddC2C_Phi_check  1114-1127
RBM.Univ.GUEPhase.DuhamelBInst.step_decomp_check  1129-1149
RBM.Univ.GUEPhase.DuhamelBInst.Vp_le_check  1153-1173
RBM.Univ.GUEPhase.DuhamelBInst.qv_le_crude_check  1175-1182
RBM.Univ.GUEPhase.DuhamelBInst.exists_level_check  1186-1194
RBM.Univ.GUEPhase.DuhamelBInst.azuma_Z_check  1198-1206
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_b  1208-1212
private RBM.Univ.GUEPhase.DuhamelBInst.DuhamelBInst_hb  1214-1254
RBM.Univ.GUEPhase.DuhamelBInst.azuma_Y_check  1256-1267
### RBM3D.Universality.GUEPhase.DuhamelC  (7 unreached of 47)
private RBM.Univ.GUEPhase.DuhamelCInst.DuhamelCInst_t1  1527-1527
private RBM.Univ.GUEPhase.DuhamelCInst.DuhamelCInst_t0  1528-1528
private RBM.Univ.GUEPhase.DuhamelCInst.DuhamelCInst_t1_le_t0  1530-1534
private RBM.Univ.GUEPhase.DuhamelCInst.DuhamelCInst_mE_im  1536-1539
private RBM.Univ.GUEPhase.DuhamelCInst.DuhamelCInst_eta  1541-1544
RBM.Univ.GUEPhase.DuhamelCInst.hscale_check  1546-1564
RBM.Univ.GUEPhase.DuhamelCInst.gueGrid_loop_duhamel_check  1566-1598
### RBM3D.Universality.GUEPhase.EntryDet  (57 unreached of 90)
RBM.Univ.Snorm_symm  222-224
RBM.Univ.Snorm_zero_right  254-259
RBM.Univ.Snorm_zero_left  261-266
RBM.Univ.mix_offdiag_det  268-283
RBM.Univ.mix_diag_det  285-309
private RBM.Univ.EntryDetCheck.check_mE_zero  917-920
private RBM.Univ.EntryDetCheck.check_zt_zero  922-923
private RBM.Univ.EntryDetCheck.check_green_zero  925-931
private RBM.Univ.EntryDetCheck.check_blockMat_zero  933-935
private RBM.Univ.EntryDetCheck.check_greenBlk_zero  937-955
private RBM.Univ.EntryDetCheck.check_goodEvent_zero  957-965
RBM.Univ.EntryDetCheck.stable_mix_inst  967-975
RBM.Univ.EntryDetCheck.inv_N_le_maxLoopPM_inst  977-989
RBM.Univ.EntryDetCheck.ward_col_inst  991-995
RBM.Univ.EntryDetCheck.ward_row_inst  997-1000
RBM.Univ.EntryDetCheck.green_transpose_inst  1002-1006
RBM.Univ.EntryDetCheck.sum_Snorm_le_inst  1008-1021
RBM.Univ.EntryDetCheck.svarF_le_inst  1025-1028
RBM.Univ.EntryDetCheck.Snorm_le_inst  1030-1033
RBM.Univ.EntryDetCheck.Snorm_nonneg_inst  1035-1036
RBM.Univ.EntryDetCheck.sum_Snorm_row_inst  1038-1039
RBM.Univ.EntryDetCheck.sum_Snorm_col_inst  1041-1042
RBM.Univ.EntryDetCheck.Snorm_symm_inst  1044-1046
RBM.Univ.EntryDetCheck.Snorm_zero_right_inst  1048-1050
RBM.Univ.EntryDetCheck.Snorm_zero_left_inst  1052-1054
RBM.Univ.EntryDetCheck.im_diag_le_inst  1056-1064
RBM.Univ.EntryDetCheck.mixC_pos_inst  1066-1068
RBM.Univ.EntryDetCheck.mixK_one_le_inst  1070-1070
RBM.Univ.EntryDetCheck.mixDelta_pos_inst  1072-1072
RBM.Univ.EntryDetCheck.mixCdet_nonneg_inst  1074-1074
RBM.Univ.EntryDetCheck.ldeRowRHS_smul_inst  1076-1082
RBM.Univ.EntryDetCheck.ldeColRHS_smul_inst  1084-1089
RBM.Univ.EntryDetCheck.ldeQuadRHS_smul_inst  1091-1096
RBM.Univ.EntryDetCheck.ldeQuadLHS_smul_inst  1098-1105
private RBM.Univ.EntryDetCheck.check_lde_zero  1115-1130
private RBM.Univ.EntryDetCheck.check_ldeQuad_scalar  1132-1196
private RBM.Univ.EntryDetCheck.check_neg_inv  1198-1207
private RBM.Univ.EntryDetCheck.check_norm_sub  1209-1217
private RBM.Univ.EntryDetCheck.check_norm_c  1219-1226
private RBM.Univ.EntryDetCheck.check_scalar_goodEvent  1228-1233
private RBM.Univ.EntryDetCheck.check_sum_le  1235-1256
private RBM.Univ.EntryDetCheck.check_zt_im_ne  1258-1262
private RBM.Univ.EntryDetCheck.check_dI  1264-1265
private RBM.Univ.EntryDetCheck.check_dI_pos  1267-1268
private RBM.Univ.EntryDetCheck.check_dI_le_thou  1270-1270
private RBM.Univ.EntryDetCheck.check_dI_le_mixDelta  1272-1272
private RBM.Univ.EntryDetCheck.check_t  1274-1275
private RBM.Univ.EntryDetCheck.check_t_pos  1277-1277
private RBM.Univ.EntryDetCheck.check_t_add_le  1279-1280
private RBM.Univ.EntryDetCheck.check_t_two_le  1282-1283
private RBM.Univ.EntryDetCheck.check_dI_mixK  1285-1290
private RBM.Univ.EntryDetCheck.check_card_idx  1292-1293
private RBM.Univ.EntryDetCheck.check_card_vtx  1295-1296
RBM.Univ.EntryDetCheck.mix_offdiag_det_inst  1298-1336
RBM.Univ.EntryDetCheck.mix_diag_det_inst  1338-1386
RBM.Univ.EntryDetCheck.mix_det_inst  1388-1424
RBM.Univ.EntryDetCheck.mix_det_inst_vars  1426-1453
### RBM3D.Universality.GUEPhase.EntryGrid  (3 unreached of 31)
private RBM.Univ.GUEPhase.EntryGridInst.t1_le  623-627
private RBM.Univ.GUEPhase.EntryGridInst.measurableSet_diag_le  669-679
RBM.Univ.GUEPhase.EntryGridInst.gueGrid_entry_bound_sz0  698-722
### RBM3D.Universality.GUEPhase.EntryTail  (63 unreached of 112)
RBM.Univ.mixMat_isHermitian  58-61
RBM.Univ.mixMat_zero_right  71-75
RBM.Univ.mixMat_zero_left  77-81
RBM.Univ.EntryTailCheck.inst_zt_im  924-930
RBM.Univ.EntryTailCheck.inst_zt_im_ne  932-934
RBM.Univ.EntryTailCheck.inst_x1_ne  936-940
RBM.Univ.EntryTailCheck.inst_mixMat_isHermitian  942-945
RBM.Univ.EntryTailCheck.inst_ouMat_eq_mixMat  947-949
RBM.Univ.EntryTailCheck.inst_mixMat_zero_right  951-953
RBM.Univ.EntryTailCheck.inst_mixMat_zero_left  955-957
RBM.Univ.EntryTailCheck.inst_mixMat_eq_Xmat_mixSample  959-961
RBM.Univ.EntryTailCheck.inst_measurable_mixMat  963-964
RBM.Univ.EntryTailCheck.inst_mixSample_law  966-971
RBM.Univ.EntryTailCheck.inst_ouP_mixSample_preimage  973-977
RBM.Univ.EntryTailCheck.inst_mixEntry_mixVar_coe  979-982
RBM.Univ.EntryTailCheck.inst_mixEntry_sigRow_gvarF  984-987
RBM.Univ.EntryTailCheck.inst_mixEntry_sigRow_mixVar  989-992
RBM.Univ.EntryTailCheck.inst_mixEntry_mixVar_diag  994-996
RBM.Univ.EntryTailCheck.inst_mixEntry_Smix_diag_pos  998-999
RBM.Univ.EntryTailCheck.inst_mixProfOK  1001-1003
RBM.Univ.EntryTailCheck.inst_mixEntry_quad_tail  1005-1014
RBM.Univ.EntryTailCheck.inst_mixEntry_row_tail  1016-1024
RBM.Univ.EntryTailCheck.inst_mixEntry_col_tail  1026-1034
RBM.Univ.EntryTailCheck.inst_mixEntry_diag_tail  1036-1041
RBM.Univ.EntryTailCheck.inst_mixEntry_quad_tail_sharp  1043-1052
RBM.Univ.EntryTailCheck.inst_mixEntry_row_tail_sharp  1054-1062
RBM.Univ.EntryTailCheck.inst_mixEntry_col_tail_sharp  1064-1072
RBM.Univ.EntryTailCheck.inst_mixEntry_greenBlk_eq  1074-1079
RBM.Univ.EntryTailCheck.inst_mixEntry_det  1081-1103
RBM.Univ.EntryTailCheck.inst_measurable_mixSample  1107-1108
RBM.Univ.EntryTailCheck.inst_mixEntry_minor_eq  1110-1114
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_Xmat  1116-1118
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_green  1120-1123
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_greenMinor  1125-1128
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_ldeRowLHS  1130-1133
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_ldeRowRHS  1135-1138
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_ldeColLHS  1140-1143
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_ldeColRHS  1145-1148
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_ldeQuadLHS  1150-1153
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_ldeQuadRHS  1155-1158
RBM.Univ.EntryTailCheck.inst_mixEntry_meas_diag  1160-1162
RBM.Univ.EntryTailCheck.inst_mixEntry_relabel_ldeRowLHS  1164-1171
RBM.Univ.EntryTailCheck.inst_mixEntry_relabel_ldeRowRHS  1173-1180
RBM.Univ.EntryTailCheck.inst_mixEntry_relabel_ldeColLHS  1182-1189
RBM.Univ.EntryTailCheck.inst_mixEntry_relabel_ldeColRHS  1191-1198
RBM.Univ.EntryTailCheck.inst_mixEntry_relabel_ldeQuadLHS  1200-1209
RBM.Univ.EntryTailCheck.inst_mixEntry_relabel_ldeQuadRHS  1211-1218
RBM.Univ.EntryTailCheck.inst_green_zero  1231-1236
RBM.Univ.EntryTailCheck.inst_greenMinor_zero  1238-1241
RBM.Univ.EntryTailCheck.inst_ldeRowLHS_zero  1243-1245
RBM.Univ.EntryTailCheck.inst_ldeColLHS_zero  1247-1249
RBM.Univ.EntryTailCheck.inst_ldeQuadLHS_zero  1251-1266
RBM.Univ.EntryTailCheck.inst_ldeQuadRHS_zero  1268-1285
RBM.Univ.EntryTailCheck.inst_quad_zero  1287-1302
RBM.Univ.EntryTailCheck.inst_mE_zero  1306-1312
RBM.Univ.EntryTailCheck.inst_zt_zero  1314-1315
RBM.Univ.EntryTailCheck.inst_zt_zero_ne  1317-1320
RBM.Univ.EntryTailCheck.inst_llErr_zero  1322-1342
RBM.Univ.EntryTailCheck.inst_det_zero  1344-1381
RBM.Univ.EntryTailCheck.instDelta  1383-1384
RBM.Univ.EntryTailCheck.instDelta_pos  1386-1387
RBM.Univ.EntryTailCheck.instU  1389-1389
RBM.Univ.EntryTailCheck.inst_mixEntry_det_full  1391-1413
### RBM3D.Universality.GUEPhase.EntryTailMain  (19 unreached of 37)
RBM.Univ.EntryTailMainCheck.inst_mixCq_pos  622-622
RBM.Univ.EntryTailMainCheck.mixCq_one  624-626
RBM.Univ.EntryTailMainCheck.inst_mixBad_tail  628-634
RBM.Univ.EntryTailMainCheck.inst_mixBad_tail_small  636-643
RBM.Univ.EntryTailMainCheck.inst_lam_window  645-654
RBM.Univ.EntryTailMainCheck.delta0  656-657
RBM.Univ.EntryTailMainCheck.delta0_nonneg  659-660
RBM.Univ.EntryTailMainCheck.delta0_le  662-662
RBM.Univ.EntryTailMainCheck.delta0_36  664-665
RBM.Univ.EntryTailMainCheck.zeta3  667-668
RBM.Univ.EntryTailMainCheck.aMix  670-670
RBM.Univ.EntryTailMainCheck.bMix  672-672
RBM.Univ.EntryTailMainCheck.mix_params_ok  674-679
RBM.Univ.EntryTailMainCheck.mix_params_values  681-685
RBM.Univ.EntryTailMainCheck.inst_mixEntry_event_subset  687-704
RBM.Univ.EntryTailMainCheck.inst_mixEntry_union  706-723
RBM.Univ.EntryTailMainCheck.sz0_size_ge_two  725-733
RBM.Univ.EntryTailMainCheck.inst_entryMix  735-752
RBM.Univ.EntryTailMainCheck.inst_entryMix_quarter  754-771
### RBM3D.Universality.GUEPhase.Eq729A  (36 unreached of 79)
RBM.Univ.GUEPhase.eq729_primRhs_one  140-146
private RBM.Univ.GUEPhase.Eq729A_hdrift_int  693-708
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_t1  1094-1094
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_t0  1095-1095
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_K  1096-1096
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_E  1097-1097
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_Nnat  1099-1103
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_N  1105-1106
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_c  1108-1110
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_Kt  1112-1114
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_den  1116-1118
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_c_nonneg  1120-1122
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_c_le  1124-1128
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_Kt_two  1130-1132
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_Kt_three  1134-1136
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_primBil_const  1138-1149
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_primRhs  1151-1159
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_hasDerivAt  1161-1180
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_hKb  1182-1187
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_hKd  1189-1197
RBM.Univ.GUEPhase.Eq729AInst.eq729_Kdisc_check  1199-1210
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_hK0  1212-1215
RBM.Univ.GUEPhase.Eq729AInst.eq729_norm_primBil2_le_check  1217-1223
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_mE_im  1225-1229
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_eta  1231-1233
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_gridTime_zero  1235-1237
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_hz0  1239-1242
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_hBk  1244-1270
private RBM.Univ.GUEPhase.Eq729AInst.Eq729AInst_hΛ  1272-1274
RBM.Univ.GUEPhase.Eq729AInst.eq729_one_step_check  1276-1311
RBM.Univ.GUEPhase.Eq729AInst.eq729_primBil2_check  1328-1336
RBM.Univ.GUEPhase.Eq729AInst.eq729_primRhs_one_check  1338-1340
RBM.Univ.GUEPhase.Eq729AInst.eq729_norm_primRhs2_le_check  1342-1348
RBM.Univ.GUEPhase.Eq729AInst.eq729_eG2_check  1350-1367
RBM.Univ.GUEPhase.Eq729AInst.eq729_duhamel_check  1369-1389
RBM.Univ.GUEPhase.Eq729AInst.eq729_grid_facts_check  1391-1407
### RBM3D.Universality.GUEPhase.Eq729B  (61 unreached of 103)
RBM.Univ.GUEPhase.Eq729B_ueq747_iff  125-128
RBM.Univ.GUEPhase.Eq729B_STExp2_congr  1249-1254
RBM.Univ.GUEPhase.Eq729B_flowData_formulas  1256-1262
RBM.Univ.GUEPhase.Eq729B_FlowData.ev_eq  1264-1269
RBM.Univ.GUEPhase.Eq729B_goodFlow_aux  1271-1302
RBM.Univ.GUEPhase.Eq729B_goodFlow  1304-1311
RBM.Univ.GUEPhase.Eq729B_bridge  1313-1322
private RBM.Univ.GUEPhase.Eq729BInst.Ei  1345-1345
private RBM.Univ.GUEPhase.Eq729BInst.xx  1346-1346
private RBM.Univ.GUEPhase.Eq729BInst.Nn  1347-1347
private RBM.Univ.GUEPhase.Eq729BInst.yy  1348-1348
private RBM.Univ.GUEPhase.Eq729BInst.tw0  1349-1349
private RBM.Univ.GUEPhase.Eq729BInst.tw1  1350-1350
private RBM.Univ.GUEPhase.Eq729BInst.xx_ge  1352-1352
private RBM.Univ.GUEPhase.Eq729BInst.lam_eq  1353-1353
private RBM.Univ.GUEPhase.Eq729BInst.W_eq  1354-1354
private RBM.Univ.GUEPhase.Eq729BInst.L_eq  1355-1355
private RBM.Univ.GUEPhase.Eq729BInst.Nn_eq  1356-1357
private RBM.Univ.GUEPhase.Eq729BInst.yy_eq  1358-1360
private RBM.Univ.GUEPhase.Eq729BInst.yy_pos  1361-1363
private RBM.Univ.GUEPhase.Eq729BInst.yy_le_half  1364-1369
private RBM.Univ.GUEPhase.Eq729BInst.Nn_ge_one  1370-1372
private RBM.Univ.GUEPhase.Eq729BInst.Nn_mul_yy  1373-1375
private RBM.Univ.GUEPhase.Eq729BInst.tw1_nonneg  1377-1381
private RBM.Univ.GUEPhase.Eq729BInst.tw1_le_tw0  1382-1384
private RBM.Univ.GUEPhase.Eq729BInst.tw0_lt_one  1385-1385
private RBM.Univ.GUEPhase.Eq729BInst.mE_zero_im  1386-1387
private RBM.Univ.GUEPhase.Eq729BInst.etaT_tw0  1389-1390
private RBM.Univ.GUEPhase.Eq729BInst.h730_at  1392-1403
private RBM.Univ.GUEPhase.Eq729BInst.hscale_at  1405-1427
private RBM.Univ.GUEPhase.Eq729BInst.hell_at  1429-1441
private RBM.Univ.GUEPhase.Eq729BInst.hlam1  1444-1448
private RBM.Univ.GUEPhase.Eq729BInst.hE0  1450-1450
private RBM.Univ.GUEPhase.Eq729BInst.hKb0  1452-1455
private RBM.Univ.GUEPhase.Eq729BInst.exists_Kt  1457-1470
RBM.Univ.GUEPhase.Eq729BInst.inst_gueGrid_eq729  1472-1484
private RBM.Univ.GUEPhase.Eq729BInst.two_pow_rpow  1486-1487
private RBM.Univ.GUEPhase.Eq729BInst.W7  1489-1489
private RBM.Univ.GUEPhase.Eq729BInst.lam7  1490-1490
private RBM.Univ.GUEPhase.Eq729BInst.N7  1491-1492
private RBM.Univ.GUEPhase.Eq729BInst.h4_7  1494-1497
private RBM.Univ.GUEPhase.Eq729BInst.hlo_7  1499-1502
private RBM.Univ.GUEPhase.Eq729BInst.etaQ7_pos  1505-1508
private RBM.Univ.GUEPhase.Eq729BInst.hc4_7  1510-1513
private RBM.Univ.GUEPhase.Eq729BInst.hN_7  1515-1525
RBM.Univ.GUEPhase.Eq729BInst.inst_claimA  1527-1531
RBM.Univ.GUEPhase.Eq729BInst.inst_hell_of_scales  1533-1540
RBM.Univ.GUEPhase.Eq729BInst.inst_assembly_747  1542-1548
private RBM.Univ.GUEPhase.Eq729BInst.hτUi  1553-1553
private RBM.Univ.GUEPhase.Eq729BInst.tU  1555-1556
private RBM.Univ.GUEPhase.Eq729BInst.tU_ok  1558-1559
RBM.Univ.GUEPhase.Eq729BInst.inst_goodFlow  1561-1565
private RBM.Univ.GUEPhase.Eq729BInst.Ec  1567-1569
private RBM.Univ.GUEPhase.Eq729BInst.T0c  1570-1570
private RBM.Univ.GUEPhase.Eq729BInst.T1c  1571-1571
private RBM.Univ.GUEPhase.Eq729BInst.fdc  1573-1573
RBM.Univ.GUEPhase.Eq729BInst.inst_derived  1575-1580
RBM.Univ.GUEPhase.Eq729BInst.inst_bridge  1582-1585
RBM.Univ.GUEPhase.Eq729BInst.inst_eq747_of_eq729  1587-1592
RBM.Univ.GUEPhase.Eq729BInst.inst_eq747_of_inputs  1594-1611
RBM.Univ.GUEPhase.Eq729BInst.inst_bctl_le_two_calB  1616-1618
### RBM3D.Universality.GUEPhase.Generator  (7 unreached of 70)
private RBM.Univ.GUEPhase.Generator_loopL_eq  988-990
private RBM.Univ.GUEPhase.Generator_gloopProd_nil  992-993
private RBM.Univ.GUEPhase.Generator_gloopProd_cons  995-998
private RBM.Univ.GUEPhase.GeneratorCheck.Generator_diag_isHermitian  1269-1272
private RBM.Univ.GUEPhase.GeneratorCheck.Generator_M0  1274-1278
private RBM.Univ.GUEPhase.GeneratorCheck.Generator_M0_isHermitian  1280-1281
private RBM.Univ.GUEPhase.GeneratorCheck.Generator_M0_apply  1283-1292
### RBM3D.Universality.GUEPhase.Grid  (3 unreached of 55)
private RBM.Univ.GUEPhase.GUEPhaseGrid_mixedStepMeasure_isProbabilityMeasure  250-253
RBM.Univ.GUEPhase.GridCheck.t1_pos  799-803
RBM.Univ.GUEPhase.GridCheck.gueGridK_size_le  866-870
### RBM3D.Universality.GUEPhase.HypA  (52 unreached of 92)
private RBM.Univ.GUEPhase.HypAInst.tA  1139-1139
private RBM.Univ.GUEPhase.HypAInst.tB  1140-1140
private RBM.Univ.GUEPhase.HypAInst.K64  1141-1141
private RBM.Univ.GUEPhase.HypAInst.tAB  1143-1143
private RBM.Univ.GUEPhase.HypAInst.sqrt_four  1178-1179
private RBM.Univ.GUEPhase.HypAInst.mE_zero  1181-1182
private RBM.Univ.GUEPhase.HypAInst.mE_zero_im  1184-1184
private RBM.Univ.GUEPhase.HypAInst.green_zero  1186-1192
private RBM.Univ.GUEPhase.HypAInst.eps_hc  1194-1207
private RBM.Univ.GUEPhase.HypAInst.Ei  1214-1214
private RBM.Univ.GUEPhase.HypAInst.Nn  1215-1215
private RBM.Univ.GUEPhase.HypAInst.yy  1216-1216
private RBM.Univ.GUEPhase.HypAInst.tw1  1217-1217
private RBM.Univ.GUEPhase.HypAInst.tw0  1218-1218
private RBM.Univ.GUEPhase.HypAInst.Nn_ge_one  1220-1227
private RBM.Univ.GUEPhase.HypAInst.yy_pos  1229-1234
private RBM.Univ.GUEPhase.HypAInst.yy_le_one  1236-1250
private RBM.Univ.GUEPhase.HypAInst.tw1_nonneg  1252-1252
private RBM.Univ.GUEPhase.HypAInst.tw_frac  1254-1256
private RBM.Univ.GUEPhase.HypAInst.tw1_le_tw0  1258-1262
private RBM.Univ.GUEPhase.HypAInst.tw0_lt_one  1264-1268
private RBM.Univ.GUEPhase.HypAInst.etaT_tw0  1270-1271
private RBM.Univ.GUEPhase.HypAInst.h730_at  1273-1289
private RBM.Univ.GUEPhase.HypAInst.hell_at  1291-1297
private RBM.Univ.GUEPhase.HypAInst.toyK  1301-1303
private RBM.Univ.GUEPhase.HypAInst.toyK_primRhs  1305-1315
private RBM.Univ.GUEPhase.HypAInst.Kt0  1317-1318
private RBM.Univ.GUEPhase.HypAInst.Kt0_hK  1320-1327
private RBM.Univ.GUEPhase.HypAInst.exists_Kt  1329-1341
private RBM.Univ.GUEPhase.HypAInst.hKb0  1343-1350
private RBM.Univ.GUEPhase.HypAInst.Kt0_hbd  1373-1375
private RBM.Univ.GUEPhase.HypAInst.hsmall_at  1377-1390
private RBM.Univ.GUEPhase.HypAInst.loop2_ok  1392-1397
private RBM.Univ.GUEPhase.HypAInst.ω0  1404-1405
private RBM.Univ.GUEPhase.HypAInst.δ0  1406-1406
private RBM.Univ.GUEPhase.HypAInst.stop0  1408-1415
private RBM.Univ.GUEPhase.HypAInst.X2  1417-1417
private RBM.Univ.GUEPhase.HypAInst.uj  1418-1418
private RBM.Univ.GUEPhase.HypAInst.Hj  1419-1419
private RBM.Univ.GUEPhase.HypAInst.Lj  1420-1421
private RBM.Univ.GUEPhase.HypAInst.scj  1422-1422
private RBM.Univ.GUEPhase.HypAInst.AMj  1423-1424
private RBM.Univ.GUEPhase.HypAInst.AFj  1425-1427
private RBM.Univ.GUEPhase.HypAInst.AEj  1428-1429
private RBM.Univ.GUEPhase.HypAInst.Qj  1430-1431
private RBM.Univ.GUEPhase.HypAInst.le_dsum  1433-1438
private RBM.Univ.GUEPhase.HypAInst.S0  1440-1441
private RBM.Univ.GUEPhase.HypAInst.c0  1442-1442
private RBM.Univ.GUEPhase.HypAInst.S0_nonneg  1443-1443
private RBM.Univ.GUEPhase.HypAInst.AMsc_nonneg  1444-1445
private RBM.Univ.GUEPhase.HypAInst.c0_nonneg  1446-1447
private RBM.Univ.GUEPhase.HypAInst.scj_pos  1449-1454
### RBM3D.Universality.GUEPhase.HypB  (57 unreached of 83)
private RBM.Univ.GUEPhase.HypBInst.szT  1098-1098
private RBM.Univ.GUEPhase.HypBInst.E0  1099-1099
private RBM.Univ.GUEPhase.HypBInst.tA  1100-1100
private RBM.Univ.GUEPhase.HypBInst.tB  1101-1101
private RBM.Univ.GUEPhase.HypBInst.τT  1102-1102
private RBM.Univ.GUEPhase.HypBInst.ω0  1103-1103
private RBM.Univ.GUEPhase.HypBInst.sqrt_four  1105-1106
private RBM.Univ.GUEPhase.HypBInst.mE_zero  1108-1109
private RBM.Univ.GUEPhase.HypBInst.mE_zero_im  1111-1111
private RBM.Univ.GUEPhase.HypBInst.size_val  1113-1114
private RBM.Univ.GUEPhase.HypBInst.gueDelta_val  1116-1121
private RBM.Univ.GUEPhase.HypBInst.seqXmat_zero  1123-1126
private RBM.Univ.GUEPhase.HypBInst.gueH_zero  1128-1132
private RBM.Univ.GUEPhase.HypBInst.green_zero  1134-1140
private RBM.Univ.GUEPhase.HypBInst.entry_aux  1142-1173
private RBM.Univ.GUEPhase.HypBInst.dev_le  1175-1182
private RBM.Univ.GUEPhase.HypBInst.stop_eq  1184-1195
private RBM.Univ.GUEPhase.HypBInst.one_lt_K  1197-1200
private RBM.Univ.GUEPhase.HypBInst.Kg  1202-1202
private RBM.Univ.GUEPhase.HypBInst.uj  1203-1203
private RBM.Univ.GUEPhase.HypBInst.Hj  1204-1204
private RBM.Univ.GUEPhase.HypBInst.Lm  1205-1206
private RBM.Univ.GUEPhase.HypBInst.Gm  1207-1208
private RBM.Univ.GUEPhase.HypBInst.entry_at  1212-1240
private RBM.Univ.GUEPhase.HypBInst.hszT  1251-1251
private RBM.Univ.GUEPhase.HypBInst.exists_Kt  1255-1266
private RBM.Univ.GUEPhase.HypBInst.half_le  1291-1295
private RBM.Univ.GUEPhase.HypBInst.etaT_tB  1297-1299
private RBM.Univ.GUEPhase.HypBInst.h730_at  1301-1305
private RBM.Univ.GUEPhase.HypBInst.step_at  1307-1309
private RBM.Univ.GUEPhase.HypBInst.toyK  1314-1316
private RBM.Univ.GUEPhase.HypBInst.toyK_primRhs  1318-1328
private RBM.Univ.GUEPhase.HypBInst.Kt0  1330-1331
private RBM.Univ.GUEPhase.HypBInst.Kt0_hK  1333-1340
private RBM.Univ.GUEPhase.HypBInst.Kt0_zero  1342-1344
private RBM.Univ.GUEPhase.HypBInst.scale_pos  1346-1347
private RBM.Univ.GUEPhase.HypBInst.exists_tau  1375-1385
private RBM.Univ.GUEPhase.HypBInst.X2  1387-1387
private RBM.Univ.GUEPhase.HypBInst.Lj  1388-1389
private RBM.Univ.GUEPhase.HypBInst.scj  1390-1390
private RBM.Univ.GUEPhase.HypBInst.AMj  1391-1392
private RBM.Univ.GUEPhase.HypBInst.AEj  1393-1394
private RBM.Univ.GUEPhase.HypBInst.Qj  1395-1396
private RBM.Univ.GUEPhase.HypBInst.X2_ne  1398-1398
private RBM.Univ.GUEPhase.HypBInst.rg_ne  1400-1400
private RBM.Univ.GUEPhase.HypBInst.Cm  1402-1405
private RBM.Univ.GUEPhase.HypBInst.g3v  1407-1408
private RBM.Univ.GUEPhase.HypBInst.g4v  1409-1409
private RBM.Univ.GUEPhase.HypBInst.x00  1411-1411
private RBM.Univ.GUEPhase.HypBInst.uj_le  1413-1414
private RBM.Univ.GUEPhase.HypBInst.scj_pos  1416-1417
private RBM.Univ.GUEPhase.HypBInst.Cm_nonneg  1419-1420
private RBM.Univ.GUEPhase.HypBInst.g3v_nonneg  1422-1423
private RBM.Univ.GUEPhase.HypBInst.g4v_nonneg  1425-1426
private RBM.Univ.GUEPhase.HypBInst.AM_le_Cm  1428-1431
private RBM.Univ.GUEPhase.HypBInst.L0_le_Cm  1433-1435
private RBM.Univ.GUEPhase.HypBInst.lt_K  1437-1440
### RBM3D.Universality.GUEPhase.KPrim  (2 unreached of 30)
private RBM.Univ.GUEPhase.KPrimCheck.KPrim_ne_one_of_norm_lt  790-793
private RBM.Univ.GUEPhase.KPrimCheck.KPrim_norm_lt0  795-798
### RBM3D.Universality.GUEPhase.LLTransfer  (2 unreached of 24)
private RBM.Univ.GUEPhase.LLTransferInst.zq  484-484
private RBM.Univ.GUEPhase.LLTransferInst.tq  485-485
### RBM3D.Universality.GUEPhase.Markov  (16 unreached of 53)
private RBM.Univ.GUEPhase.Markov_hasSubgaussianMGF_lin  936-941
private RBM.Univ.GUEPhase.Markov_measurable_eval_filt  943-952
private RBM.Univ.GUEPhase.Markov_vGue_one_pos  954-994
RBM.Univ.GUEPhase.MarkovInst.markovInstOne  1016-1017
RBM.Univ.GUEPhase.MarkovInst.markovInstCoord  1019-1020
RBM.Univ.GUEPhase.MarkovInst.markovInstF  1022-1024
RBM.Univ.GUEPhase.MarkovInst.vGue_one_pos_sz0  1026-1029
RBM.Univ.GUEPhase.MarkovInst.gueMap_lin_Xmat_sz0  1031-1038
private RBM.Univ.GUEPhase.MarkovInst.markovInstF_measurable  1040-1043
private RBM.Univ.GUEPhase.MarkovInst.markovInst_integrable  1045-1060
RBM.Univ.GUEPhase.MarkovInst.gueCondExp_freeze_sz0  1062-1069
private RBM.Univ.GUEPhase.MarkovInst.markovInstF_subgaussian  1071-1093
RBM.Univ.GUEPhase.MarkovInst.gueHasCondSubgaussianMGF_of_frozen_sz0  1095-1104
RBM.Univ.GUEPhase.MarkovInst.gueHasCondSubgaussianMGF_linear_sz0  1106-1118
RBM.Univ.GUEPhase.MarkovInst.sz0_size_tendsto_nat  1120-1123
RBM.Univ.GUEPhase.MarkovInst.gue_highProb_incr_le_sz0  1125-1131
### RBM3D.Universality.GUEPhase.OneLoop  (9 unreached of 55)
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_t1  1383-1384
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_t0  1385-1385
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_K  1386-1386
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_E  1387-1387
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_ouZeta_nonneg  1389-1392
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_t1_nonneg  1394-1400
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_t1_le_t0  1402-1404
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_lam_window  1470-1478
private RBM.Univ.GUEPhase.OneLoopInst.OneLoopInst_main  1480-1504
### RBM3D.Universality.GUEPhase.PathBounds  (30 unreached of 46)
private RBM.Univ.GUEPhase.PathBoundsInst.Ei  687-687
private RBM.Univ.GUEPhase.PathBoundsInst.Nn  688-688
private RBM.Univ.GUEPhase.PathBoundsInst.yy  689-689
private RBM.Univ.GUEPhase.PathBoundsInst.tw1  690-690
private RBM.Univ.GUEPhase.PathBoundsInst.tw0  691-691
private RBM.Univ.GUEPhase.PathBoundsInst.sqrt_four  693-694
private RBM.Univ.GUEPhase.PathBoundsInst.mE_zero_im  696-698
private RBM.Univ.GUEPhase.PathBoundsInst.Nn_ge_one  700-707
private RBM.Univ.GUEPhase.PathBoundsInst.lam_eq  709-709
private RBM.Univ.GUEPhase.PathBoundsInst.lam_nonneg  711-711
private RBM.Univ.GUEPhase.PathBoundsInst.lam_le_one  713-715
private RBM.Univ.GUEPhase.PathBoundsInst.yy_pos  717-721
private RBM.Univ.GUEPhase.PathBoundsInst.yy_le_one  723-729
private RBM.Univ.GUEPhase.PathBoundsInst.tw1_nonneg  731-731
private RBM.Univ.GUEPhase.PathBoundsInst.tw_frac  733-735
private RBM.Univ.GUEPhase.PathBoundsInst.tw1_le_tw0  737-741
private RBM.Univ.GUEPhase.PathBoundsInst.tw0_lt_one  743-747
private RBM.Univ.GUEPhase.PathBoundsInst.etaT_tw0  749-750
private RBM.Univ.GUEPhase.PathBoundsInst.h730_at  752-768
private RBM.Univ.GUEPhase.PathBoundsInst.hell_at  770-776
private RBM.Univ.GUEPhase.PathBoundsInst.hell1_at  778-780
private RBM.Univ.GUEPhase.PathBoundsInst.Nn_yy  782-791
private RBM.Univ.GUEPhase.PathBoundsInst.Nn_le  793-806
private RBM.Univ.GUEPhase.PathBoundsInst.hscale_at  808-837
private RBM.Univ.GUEPhase.PathBoundsInst.hE_at  839-839
private RBM.Univ.GUEPhase.PathBoundsInst.exists_Kt  841-854
private RBM.Univ.GUEPhase.PathBoundsInst.Kt0  856-856
private RBM.Univ.GUEPhase.PathBoundsInst.Kt0_init  858-859
private RBM.Univ.GUEPhase.PathBoundsInst.Kt0_deriv  861-864
private RBM.Univ.GUEPhase.PathBoundsInst.hKb0  866-873
### RBM3D.Universality.GUEPhase.Proc  (13 unreached of 62)
private RBM.Univ.GUEPhase.ProcInst.t1c  926-926
private RBM.Univ.GUEPhase.ProcInst.t0c  927-927
private RBM.Univ.GUEPhase.ProcInst.Kc  928-928
private RBM.Univ.GUEPhase.ProcInst.Ec  929-929
private RBM.Univ.GUEPhase.ProcInst.Ktc  930-930
private RBM.Univ.GUEPhase.ProcInst.t1c_le  932-935
private RBM.Univ.GUEPhase.ProcInst.mE_zero_im  937-941
private RBM.Univ.GUEPhase.ProcInst.zt_half_im  1071-1072
private RBM.Univ.GUEPhase.ProcInst.norm_mSigma_zero  1074-1074
private RBM.Univ.GUEPhase.ProcInst.egt_norm_G  1076-1083
private RBM.Univ.GUEPhase.ProcInst.egt_hε  1085-1097
private RBM.Univ.GUEPhase.ProcInst.I2  1099-1100
private RBM.Univ.GUEPhase.ProcInst.egt_hB  1102-1116
### RBM3D.Universality.GUEPhase.ProcK  (26 unreached of 49)
private RBM.Univ.GUEPhase.ProcKInst.mE_zero_im  746-751
RBM.Univ.GUEPhase.ProcKInst.szToy  759-765
RBM.Univ.GUEPhase.ProcKInst.szToy_Bctl  767-769
RBM.Univ.GUEPhase.ProcKInst.szToy_scale  771-774
RBM.Univ.GUEPhase.ProcKInst.szToy_conv  776-779
private RBM.Univ.GUEPhase.ProcKInst.Nn  787-787
private RBM.Univ.GUEPhase.ProcKInst.size_eq  789-792
private RBM.Univ.GUEPhase.ProcKInst.Nn_eq  794-798
private RBM.Univ.GUEPhase.ProcKInst.Nn_pos  800-800
private RBM.Univ.GUEPhase.ProcKInst.Nn_ge_one  802-805
private RBM.Univ.GUEPhase.ProcKInst.Nn_rpow_le  807-822
private RBM.Univ.GUEPhase.ProcKInst.x0  824-825
private RBM.Univ.GUEPhase.ProcKInst.t0  827-827
private RBM.Univ.GUEPhase.ProcKInst.t1  829-830
private RBM.Univ.GUEPhase.ProcKInst.x0_pos  832-834
private RBM.Univ.GUEPhase.ProcKInst.x0_le  836-846
private RBM.Univ.GUEPhase.ProcKInst.Npow_le_one  848-849
private RBM.Univ.GUEPhase.ProcKInst.Npow_nonneg  851-852
private RBM.Univ.GUEPhase.ProcKInst.x0_small  854-859
private RBM.Univ.GUEPhase.ProcKInst.t0_lt_one  862-862
private RBM.Univ.GUEPhase.ProcKInst.etaT_t0  864-867
private RBM.Univ.GUEPhase.ProcKInst.t1_nonneg  869-875
private RBM.Univ.GUEPhase.ProcKInst.t1_le_t0  877-879
private RBM.Univ.GUEPhase.ProcKInst.h730_at  881-885
private RBM.Univ.GUEPhase.ProcKInst.hscale_at  887-897
private RBM.Univ.GUEPhase.ProcKInst.hell_at  899-923
### RBM3D.Universality.GUEPhase.RandomLayerA  (10 unreached of 23)
RBM.Univ.GUEPhase.RandomLayer_rows  146-172
private RBM.Univ.GUEPhase.RandomLayerInst.tau_eq  516-517
private RBM.Univ.GUEPhase.RandomLayerInst.tau_pos  519-519
private RBM.Univ.GUEPhase.RandomLayerInst.zLL  521-522
private RBM.Univ.GUEPhase.RandomLayerInst.hc0  524-525
RBM.Univ.GUEPhase.RandomLayerInst.inst_lem28  527-534
RBM.Univ.GUEPhase.RandomLayerInst.inst_rowsLL  536-547
RBM.Univ.GUEPhase.RandomLayerInst.inst_rowsQ  549-558
RBM.Univ.GUEPhase.RandomLayerInst.inst_etaLL  569-572
RBM.Univ.GUEPhase.RandomLayerInst.inst_etaQ  574-576
### RBM3D.Universality.GUEPhase.RandomLayerB  (3 unreached of 29)
RBM.Univ.GUEPhase.RandomLayerBInst.inst_g1Row  483-486
RBM.Univ.GUEPhase.RandomLayerBInst.inst_g1Rowk  488-493
RBM.Univ.GUEPhase.RandomLayerBInst.inst_g1Rowk_of_inputs  495-508
### RBM3D.Universality.GUEPhase.RandomLayerBG  (10 unreached of 24)
RBM.Univ.GUEPhase.g1Rowk_of_inputsG  393-427
RBM.Univ.GUEPhase.RandomLayerBG_bandEd  439-442
RBM.Univ.GUEPhase.RandomLayerBG_flowG_of_band_id  444-452
RBM.Univ.GUEPhase.flowG_of_band  454-458
RBM.Univ.GUEPhase.RandomLayerBG_dom_band  460-462
RBM.Univ.GUEPhase.RandomLayerBG_profComp_band  464-466
RBM.Univ.GUEPhase.RandomLayerBG_comp_band  468-472
RBM.Univ.GUEPhase.RandomLayerBG_prod_band  474-481
RBM.Univ.GUEPhase.RandomLayerBG_Que_band  483-493
RBM.Univ.GUEPhase.RandomLayerBGInst.inst_g1Rowk_of_inputsG  509-520
### RBM3D.Universality.GUEPhase.RandomLayerBGD  (4 unreached of 8)
RBM.Univ.RandomLayerBGDInst.inst_unClaimRowkD_band_zero  120-135
RBM.Univ.RandomLayerBGDInst.inst_un_claimAll_of_rowskD  137-149
RBM.Univ.RandomLayerBGDInst.inst_ouRowk_of_pinsD  151-161
RBM.Univ.RandomLayerBGDInst.inst_g1Rowk_of_inputsGD  163-177
### RBM3D.Universality.GUETranslation  (12 unreached of 47)
RBM.Univ.un_core'_of_univMainRow  789-791
RBM.Univ.GUETranslationInst.inst_dilation_ne_one  807-811
RBM.Univ.GUETranslationInst.inst_guetranslation_sz0  813-823
RBM.Univ.GUETranslationInst.inst_guetranslationRow_sz0  825-836
RBM.Univ.GUETranslationInst.inst_guetranslation_integral_gue_sz0  838-846
RBM.Univ.GUETranslationInst.inst_good_nonempty_sz0  848-857
RBM.Univ.GUETranslationInst.inst_guetranslation_core_sz0  859-877
RBM.Univ.GUETranslationInst.inst_guetranslation_uniform_sz0  879-891
RBM.Univ.GUETranslationInst.inst_un_infty1Row'_of_translation_band_zero  893-905
RBM.Univ.GUETranslationInst.inst_un_infty1Row'_band_zero  907-921
RBM.Univ.GUETranslationInst.inst_un_infty1Row'_band_one  923-936
RBM.Univ.GUETranslationInst.inst_un_core'_band_zero  938-951
### RBM3D.Universality.GreenCorr  (15 unreached of 50)
RBM.Univ.GreenCorrCheck.sz0_size_tendsto  967-969
RBM.Univ.GreenCorrCheck.instance_band  971-996
RBM.Univ.GreenCorrCheck.instance_ba  998-1024
RBM.Univ.GreenCorrCheck.instance_greenCorrAll  1026-1045
RBM.Univ.GreenCorrCheck.instance_greenCorrAll_tauU  1047-1074
private RBM.Univ.GreenCorrCheck.GreenCorr_blk0  1078-1078
private RBM.Univ.GreenCorrCheck.GreenCorr_blk32  1080-1080
private RBM.Univ.GreenCorrCheck.GreenCorr_ofs_eq  1082-1082
private RBM.Univ.GreenCorrCheck.GreenCorr_psiI_entry  1084-1099
private RBM.Univ.GreenCorrCheck.GreenCorr_baC  1101-1110
private RBM.Univ.GreenCorrCheck.GreenCorr_baC_mean_ne  1112-1121
RBM.Univ.GreenCorrCheck.instance_unGreenCorrC_band  1123-1145
RBM.Univ.GreenCorrCheck.instance_unGreenCorrC_baC  1147-1172
RBM.Univ.GreenCorrCheck.instance_greenCorrAllC_band  1174-1194
RBM.Univ.GreenCorrCheck.instance_greenCorrAllC_baC  1196-1218
### RBM3D.Universality.InjSum  (4 unreached of 33)
private RBM.Univ.InjSumCheck.bump  585-586
private RBM.Univ.InjSumCheck.bump_isTestFun  588-589
private RBM.Univ.InjSumCheck.diag123  591-593
private RBM.Univ.InjSumCheck.diag123_herm  595-597
### RBM3D.Universality.Jak  (5 unreached of 22)
RBM.Univ.jakRow  940-954
RBM.Univ.JakInst.inst_row  968-974
RBM.Univ.JakInst.inst_window  976-993
RBM.Univ.JakInst.inst_unJak  995-1001
RBM.Univ.JakInst.inst_cd_le_half  1003-1005
### RBM3D.Universality.JakKernel  (11 unreached of 47)
RBM.Univ.JakKernelInst.H1  975-976
RBM.Univ.JakKernelInst.y0  978-978
RBM.Univ.JakKernelInst.H1_herm  980-980
RBM.Univ.JakKernelInst.im_Gres_le_inv  982-1001
RBM.Univ.JakKernelInst.gridGood_one  1003-1008
RBM.Univ.JakKernelInst.blockM_le_432  1010-1021
RBM.Univ.JakKernelInst.inst_window  1023-1030
RBM.Univ.JakKernelInst.inst_good  1032-1046
RBM.Univ.JakKernelInst.H2  1048-1050
RBM.Univ.JakKernelInst.H2_herm  1052-1053
RBM.Univ.JakKernelInst.inst_crude  1068-1076
### RBM3D.Universality.JakSpectral  (10 unreached of 39)
RBM.Univ.JakSpectralInst.H1  575-576
RBM.Univ.JakSpectralInst.y0  578-578
RBM.Univ.JakSpectralInst.a0  580-580
private RBM.Univ.JakSpectralInst.I_im_ne  582-582
private RBM.Univ.JakSpectralInst.I_im_pos  584-584
RBM.Univ.JakSpectralInst.inst_spectral  586-604
RBM.Univ.JakSpectralInst.inst_block  606-614
RBM.Univ.JakSpectralInst.inst_identity  616-634
RBM.Univ.JakSpectralInst.inst_mass  636-640
RBM.Univ.JakSpectralInst.inst_bad  642-653
### RBM3D.Universality.NormBand  (5 unreached of 12)
RBM.Univ.NormBandInst.H2  230-231
RBM.Univ.NormBandInst.H2_isHermitian  233-235
RBM.Univ.NormBandInst.H2_entry_le  237-252
RBM.Univ.NormBandInst.Nsz_sz0_zero  267-269
RBM.Univ.NormBandInst.exp_ge  271-276
### RBM3D.Universality.OU  (4 unreached of 15)
RBM.Univ.ouMat_zero_map  230-240
RBM.Univ.seqXmat_map_eq_ouMat_zero  242-246
RBM.Univ.OUCheck.ouVar_zero  277-280
RBM.Univ.OUCheck.ouVar_one_gue_weight_pos  282-285
### RBM3D.Universality.OUContraction  (9 unreached of 40)
RBM.Univ.OUContractionInst.diagH  1101-1103
RBM.Univ.OUContractionInst.diagH_herm  1105-1107
RBM.Univ.OUContractionInst.diagH_nonscalar  1109-1116
RBM.Univ.OUContractionInst.inst_single  1118-1125
RBM.Univ.OUContractionInst.inst_single_diag  1127-1133
RBM.Univ.OUContractionInst.inst_wirtFirst_product  1135-1147
RBM.Univ.OUContractionInst.inst_contraction  1149-1171
RBM.Univ.OUContractionInst.inst_kernel_bound  1173-1191
RBM.Univ.OUContractionInst.inst_kernel_bound_Lt  1193-1211
### RBM3D.Universality.OUGenerator  (8 unreached of 89)
RBM.Univ.ouMat_band_eq_ouPairMat  1001-1007
RBM.Univ.OUGeneratorInst.Phi2  1304-1306
RBM.Univ.OUGeneratorInst.zIm_pos  1308-1310
RBM.Univ.OUGeneratorInst.phi2_testFunH  1312-1314
RBM.Univ.OUGeneratorInst.inst_testFunH  1316-1317
RBM.Univ.OUGeneratorInst.inst_pair_sub_eq  1319-1326
RBM.Univ.OUGeneratorInst.inst_band_hasDerivAt  1328-1337
RBM.Univ.OUGeneratorInst.inst_band_sub_eq  1339-1350
### RBM3D.Universality.OUHessian  (10 unreached of 71)
RBM.Univ.OUHessianInst.x0  1175-1176
RBM.Univ.OUHessianInst.x1  1178-1179
RBM.Univ.OUHessianInst.x0_ne_x1  1181-1185
RBM.Univ.OUHessianInst.inst_directions  1187-1196
RBM.Univ.OUHessianInst.inst_entry  1198-1212
RBM.Univ.OUHessianInst.inst_product  1214-1232
RBM.Univ.OUHessianInst.inst_wirtFirst  1234-1242
RBM.Univ.OUHessianInst.inst_kernels  1244-1259
RBM.Univ.OUHessianInst.inst_green_line  1261-1274
RBM.Univ.OUHessianInst.inst_stieltjes_line  1276-1290
### RBM3D.Universality.OUInterfaceK  (12 unreached of 30)
RBM.Univ.ouRowk_of_pins  289-298
RBM.Univ.ouRow_of_pinsk_band  410-417
RBM.Univ.OUInterfaceK_UNOULL_of_k  419-423
RBM.Univ.OUInterfaceK_UNG1Row_of_k  425-430
RBM.Univ.OUInterfaceKInst.inst_profRow_band  438-440
RBM.Univ.OUInterfaceKInst.inst_ouDiagk_band  442-445
RBM.Univ.OUInterfaceKInst.inst_ouLLk_band  447-448
RBM.Univ.OUInterfaceKInst.inst_Eq747k_band  450-453
RBM.Univ.OUInterfaceKInst.inst_g1k_band  455-465
RBM.Univ.OUInterfaceKInst.inst_g2b_of_k  467-469
RBM.Univ.OUInterfaceKInst.inst_ouRowk_band  471-477
RBM.Univ.OUInterfaceKInst.inst_ouRow_band  479-484
### RBM3D.Universality.Pins  (59 unreached of 141)
RBM.Univ.UNInfty1Row  727-740
RBM.Univ.UNCore  753-767
RBM.Univ.un_core_of_rows  769-780
RBM.Univ.un_bUniv_of_rows  862-881
RBM.Univ.un_que_params  898-902
RBM.Univ.un_cprime  936-943
RBM.Univ.un_claim_exponent  945-955
RBM.Univ.un_d_lt_half  1027-1040
RBM.Univ.un_window_N_scale  1042-1061
RBM.Univ.un_rhoSC_lower  1063-1071
RBM.Univ.un_rhoSC_edge  1073-1074
RBM.Univ.un_rhoSC_lip  1076-1121
RBM.Univ.un_const_absorb  1344-1353
private RBM.Univ.un_msc_eqs  1366-1374
RBM.Univ.un_msc_im_ge  1376-1392
RBM.Univ.un_msc_lip  1394-1429
RBM.Univ.un_msc_imag_axis  1431-1450
RBM.Univ.un_dens_msc_zero  1452-1486
RBM.Univ.UNInst.bump_nondegenerate  1507-1513
RBM.Univ.UNInst.sz0_adm  1517-1518
RBM.Univ.UNInst.inst_dc_lt_one  1520-1530
RBM.Univ.UNInst.inst_d_lt_half  1532-1543
RBM.Univ.UNInst.two_le_rpow_quarter  1547-1553
RBM.Univ.UNInst.inst_L32_arith_half  1555-1569
RBM.Univ.UNInst.inst_L32_arith_sharp  1571-1586
RBM.Univ.UNInst.inst_que_exponent  1590-1592
RBM.Univ.UNInst.inst_que_params  1594-1596
RBM.Univ.UNInst.inst_cprime  1598-1600
RBM.Univ.UNInst.inst_claim_exponent  1602-1604
RBM.Univ.UNInst.pow32  1606-1613
RBM.Univ.UNInst.inst_window_sub_lower_edge  1615-1617
RBM.Univ.UNInst.inst_window_sub_inst  1619-1621
RBM.Univ.UNInst.inst_window_sub_upper_edge  1623-1626
RBM.Univ.UNInst.inst_W_neg_le  1628-1636
RBM.Univ.UNInst.inst_step1_floor  1638-1649
RBM.Univ.UNInst.inst_window_N_scale  1651-1662
RBM.Univ.UNInst.inst_Bctl_le  1664-1671
RBM.Univ.UNInst.inst_const_absorb  1673-1681
RBM.Univ.UNInst.inst_rhoSC_lower  1685-1686
RBM.Univ.UNInst.inst_rhoSC_edge  1688-1690
RBM.Univ.UNInst.inst_rhoSC_lip  1692-1693
RBM.Univ.UNInst.inst_dens_msc  1695-1696
RBM.Univ.UNInst.unMy_single_self  1700-1710
RBM.Univ.UNInst.isOrthoEigenbasis_zero  1712-1717
RBM.Univ.UNInst.badY_zero  1719-1728
RBM.Univ.UNInst.inst_badY_subset  1730-1735
RBM.Univ.UNInst.inst_badY_measure  1737-1744
RBM.Univ.UNInst.inst_badY_card  1746-1748
RBM.Univ.UNInst.inst_bUniv_band  1753-1768
RBM.Univ.UNInst.inst_core_band  1770-1779
RBM.Univ.UNInst.inst_core_ba  1781-1793
RBM.Univ.UNInst.inst_claimAll_band  1795-1801
RBM.Univ.UNInst.kPoint_zero  1805-1811
RBM.Univ.UNInst.kPoint_eq_zero_of_card_lt  1813-1819
RBM.Univ.UNInst.unUnivDilAt_zero  1821-1831
RBM.Univ.UNInst.un_claim417_zero  1842-1848
RBM.Univ.UNInst.un_uyw_one  1850-1854
RBM.Univ.UNInst.un_not_emcte2_zero_noB  1857-1883
RBM.Univ.UNInst.inst_core_of_rows  1886-1895
### RBM3D.Universality.PinsC2  (34 unreached of 74)
private RBM.Univ.PinsC2_quarter_le  162-168
private RBM.Univ.PinsC2_Bctl_anti  199-217
RBM.Univ.un_exists_eigenvalues_eq_diagonal  366-384
RBM.Univ.stieltjesN_diagonal  387-412
RBM.Univ.mV_vOUC  481-486
RBM.Univ.stieltjesN_ouInit_toC  506-518
RBM.Univ.UNDens'.mono  524-536
RBM.Univ.UNTrLocal.mono  538-545
RBM.Univ.unMeanBound_toC  547-554
private RBM.Univ.PinsC2_aux3  569-573
RBM.Univ.unTrLocalInit'_of_unTrLocal  583-786
RBM.Univ.unTrLocalInit'_band_zero  789-803
private RBM.Univ.PinsC2_eig_eq  807-810
private RBM.Univ.PinsC2_diag_herm  812-815
private RBM.Univ.PinsC2_mV_single  817-837
private RBM.Univ.PinsC2_univ_not_le  839-845
private RBM.Univ.PinsC2_shift  847-851
RBM.Univ.not_UNStep1GoodC'_of_diag  853-998
RBM.Univ.PinsC2Inst.diagModel  1526-1534
RBM.Univ.PinsC2Inst.inst_diag_model  1536-1543
RBM.Univ.PinsC2Inst.inst_not_UNStep1GoodC'_diag  1545-1556
RBM.Univ.PinsC2Inst.inst_unTrLocalInit'_band  1558-1566
RBM.Univ.PinsC2Inst.inst_step1GoodC''_band  1568-1588
RBM.Univ.PinsC2Inst.inst_step1GoodC''_det_band  1590-1606
RBM.Univ.PinsC2Inst.inst_coreC_band''  1608-1624
private RBM.Univ.PinsC2Inst.PinsC2_eig_diag_entry  1628-1647
private RBM.Univ.PinsC2Inst.PinsC2_eig_diag_abs  1649-1654
private RBM.Univ.PinsC2Inst.PinsC2_diag_convex  1656-1663
RBM.Univ.PinsC2Inst.inst_un_eigenvalues_abs_le_convex  1665-1674
RBM.Univ.PinsC2Inst.inst_un_exists_eigenvalues_eq_diagonal  1676-1679
RBM.Univ.PinsC2Inst.inst_stieltjesN_diagonal  1681-1685
RBM.Univ.PinsC2Inst.inst_stieltjesN_vert_le  1687-1691
RBM.Univ.PinsC2Inst.inst_mV_vOUC  1693-1697
RBM.Univ.PinsC2Inst.inst_stieltjesN_ouInit_toC  1699-1705
### RBM3D.Universality.PinsDens  (31 unreached of 41)
RBM.Univ.UNDensBandRow'  108-112
RBM.Univ.UNStep1GoodC'  114-127
RBM.Univ.UNCoreC'  129-138
private RBM.Univ.PinsDens_norm_vert  146-150
private RBM.Univ.PinsDens_norm_le_one  164-171
RBM.Univ.unDensBandRow'_of_row  192-196
RBM.Univ.unDens'_freeConvST  198-214
RBM.Univ.unDensShift_of_le  253-256
RBM.Univ.unDens_shift  258-290
private RBM.Univ.PinsDens_one_le_Nsz  292-299
private RBM.Univ.PinsDens_Nsz_pos  301-302
private RBM.Univ.PinsDens_rpow_two_le  304-307
RBM.Univ.unTrLocal_shift  309-319
RBM.Univ.unTrLocalInit_shift  321-331
RBM.Univ.not_unDens'_unDensShift  333-383
private RBM.Univ.PinsDens_exists_not_mem  385-404
private RBM.Univ.PinsDens_rho_eq  406-427
private RBM.Univ.PinsDens_refute  429-467
RBM.Univ.not_UNStep1Good  469-500
RBM.Univ.not_UNStep1GoodC  502-529
RBM.Univ.un_msc_box_zero  533-549
RBM.Univ.un_dens'_msc_zero  551-558
private RBM.Univ.UNDensInst.PinsDens_rpow_two_le_one  572-575
RBM.Univ.UNDensInst.inst_core_band'  577-584
RBM.Univ.UNDensInst.inst_core_of_rows'  586-594
RBM.Univ.UNDensInst.inst_bUniv_band'  596-609
RBM.Univ.UNDensInst.inst_bUniv_band_k'  611-627
RBM.Univ.UNDensInst.inst_coreC_band'  629-637
RBM.Univ.UNDensInst.inst_dens'_uI  639-648
RBM.Univ.UNDensInst.inst_T2190a_family  650-665
RBM.Univ.UNDensInst.not_UNStep1Good_band  667-676
### RBM3D.Universality.PinsK  (36 unreached of 75)
RBM.Univ.unPinsK_toC_toUNModel  109-110
RBM.Univ.ouInit_toC  123-126
private RBM.Univ.unPinsK_eigenvalues_congr  162-166
private RBM.Univ.unPinsK_eig_toC  168-171
RBM.Univ.UNGreenCorrC_toC  231-234
RBM.Univ.UNInfty1C_toC  236-240
RBM.Univ.UNUnivMainC_toC  242-246
RBM.Univ.UNGreenCorrAllC.toAll  250-252
RBM.Univ.UNCoreC  288-299
RBM.Univ.UNQuek  397-403
RBM.Univ.UNLocAvgk  405-414
RBM.Univ.UNOURowk  425-426
RBM.Univ.un_claimAll_of_rowsk  451-466
RBM.Univ.ouP_cylinder  482-489
RBM.Univ.UNOUQUEk_zero_of_UNQuek  491-507
RBM.Univ.unPinsK_band_bulk  517-518
RBM.Univ.UNOUDiagk_band  528-532
RBM.Univ.UNQuek_band  552-552
RBM.Univ.UNLocAvgk_band  554-554
RBM.Univ.UNOUClaimsk_band  556-558
RBM.Univ.UNOURowk_band  560-563
RBM.Univ.UNEMCTE2Rowk_band  565-567
RBM.Univ.UNJakUywRowk_band  569-571
RBM.Univ.un_claimAll_of_rowsk_band  578-590
RBM.Univ.UNKInst.inWindow_nonempty  606-626
RBM.Univ.UNKInst.inst_claimAllC_band  628-637
RBM.Univ.UNKInst.inst_claimAll_band_k  639-647
RBM.Univ.UNKInst.inst_bUniv_band_k  649-667
RBM.Univ.UNKInst.inst_coreC_band  669-680
RBM.Univ.UNKInst.inst_OUQUEk_zero_band  682-691
private RBM.Univ.UNKInst.unPinsK_blk0  693-693
private RBM.Univ.UNKInst.unPinsK_blk32  695-695
private RBM.Univ.UNKInst.unPinsK_ofs_eq  697-697
private RBM.Univ.UNKInst.unPinsK_psiI_entry  699-713
private RBM.Univ.UNKInst.unPinsK_baC  715-723
RBM.Univ.UNKInst.inst_ouMatC_ne_ouMat  725-748
### RBM3D.Universality.PinsKD  (10 unreached of 18)
RBM.Univ.UNQuekD_true  99-101
RBM.Univ.UNLocAvgkD_true  103-105
RBM.Univ.UNOUClaimskD_true  107-109
RBM.Univ.UNOURowkD_true  111-114
RBM.Univ.UNEMCTE2RowkD_true  116-118
RBM.Univ.UNJakUywRowkD_true  120-124
RBM.Univ.UNClaimRowkD_true  126-128
RBM.Univ.UNG1RowkD_true  130-133
RBM.Univ.band_locAvg  135-137
RBM.Univ.band_ouRow  139-142
### RBM3D.Universality.PoissonSmoothing  (4 unreached of 34)
private RBM.Univ.PoissonSmoothingCheck.bump  1038-1039
private RBM.Univ.PoissonSmoothingCheck.bump_isTestFun  1041-1042
private RBM.Univ.PoissonSmoothingCheck.diag123  1044-1046
private RBM.Univ.PoissonSmoothingCheck.diag123_herm  1048-1050
### RBM3D.Universality.QUEFlow  (3 unreached of 51)
RBM.Univ.QUEFlowInst.inst_ouEtaQ  980-983
RBM.Univ.QUEFlowInst.inst_exponent  985-990
RBM.Univ.QUEFlowInst.inst_queBound  992-997
### RBM3D.Universality.Step1Band  (15 unreached of 63)
private RBM.Univ.Step1Band_zeta_le  96-97
private RBM.Univ.Step1Band_zeta_nonneg  99-101
RBM.Univ.Step1BandInst.inst_step1Band_band  1382-1394
RBM.Univ.Step1BandInst.inst_step1Band_band_one  1396-1409
RBM.Univ.Step1BandInst.inst_rhoSC_one_lt_zero  1411-1415
RBM.Univ.Step1BandInst.inst_step1Band_row_band  1417-1428
RBM.Univ.Step1BandInst.inst_step1Band_abs_integral_kPoint_le  1430-1436
RBM.Univ.Step1BandInst.inst_step1Band_kPoint_shift  1438-1442
RBM.Univ.Step1BandInst.inst_step1Band_eventually_forall  1444-1450
RBM.Univ.Step1BandInst.inst_step1Band_gue_count  1452-1458
RBM.Univ.Step1BandInst.inst_step1Band_integral_ouP  1460-1470
RBM.Univ.Step1BandInst.inst_step1Band_integral_ouPC  1472-1488
RBM.Univ.Step1BandInst.inst_step1Band_integral_ouPC_band  1490-1499
RBM.Univ.Step1BandInst.inst_step1BandC''_band  1501-1514
RBM.Univ.Step1BandInst.inst_step1Band_rowC''_band  1516-1527
### RBM3D.Universality.Step1Cond  (12 unreached of 39)
RBM.Univ.Step1CondCheck.step1Cond_szC  841-847
RBM.Univ.Step1CondCheck.step1Cond_hat  849-850
RBM.Univ.Step1CondCheck.step1Cond_hat_cont  852-854
RBM.Univ.Step1CondCheck.step1Cond_hat_nonneg  856-856
RBM.Univ.Step1CondCheck.step1Cond_hat_le_one  858-860
RBM.Univ.Step1CondCheck.step1Cond_hat_eq_zero_of_one_lt  862-864
RBM.Univ.Step1CondCheck.step1Cond_hat_cpt  866-878
RBM.Univ.Step1CondCheck.step1Cond_hat_le_indicator  880-896
RBM.Univ.Step1CondCheck.step1Cond_bump  898-899
RBM.Univ.Step1CondCheck.step1Cond_bump_testFun  901-904
RBM.Univ.Step1CondCheck.step1Cond_card_Idx331  906-908
RBM.Univ.Step1CondCheck.step1Cond_measurable_Xmat_331  910-912
### RBM3D.Universality.Step1Good  (4 unreached of 33)
RBM.Univ.mV_vOU  131-139
RBM.Univ.Step1GoodInst.inst_step1Good'_band  811-831
RBM.Univ.Step1GoodInst.inst_step1Good'_det_band  833-849
RBM.Univ.Step1GoodInst.inst_admissible_sz0  851-856
### RBM3D.Universality.Step1RegularityGUE  (13 unreached of 50)
RBM.Univ.gue_window  97-103
RBM.Univ.gue_window_sharp  105-109
RBM.Univ.gue_l32_exponents  111-123
RBM.Univ.Step1RegularityGUEInst.inst_sz0_size_tendsto  946-948
RBM.Univ.Step1RegularityGUEInst.inst_guelocalEvent_sz0  950-956
RBM.Univ.Step1RegularityGUEInst.inst_event_nonempty_sz0  958-974
RBM.Univ.Step1RegularityGUEInst.inst_guedetHalf_sz0  976-981
RBM.Univ.Step1RegularityGUEInst.inst_gueGood_sz0  983-989
RBM.Univ.Step1RegularityGUEInst.inst_gueGoodHighProb_of_sz0  991-997
RBM.Univ.Step1RegularityGUEInst.inst_size_zero_sz0  999-1003
RBM.Univ.Step1RegularityGUEInst.inst_gueGood_nonempty_sz0  1005-1020
RBM.Univ.Step1RegularityGUEInst.inst_exponents_sz0  1022-1033
RBM.Univ.Step1RegularityGUEInst.inst_gue_err_pow_sz0  1035-1047
### RBM3D.Universality.UnivMain  (16 unreached of 52)
RBM.Univ.unCore'_holds  559-562
RBM.Univ.UnivMainInst.inst_nondegenerate  680-685
RBM.Univ.UnivMainInst.inst_univMain_band_zero  687-699
RBM.Univ.UnivMainInst.inst_claim417_core  701-714
RBM.Univ.UnivMainInst.inst_claimAll_band_zero  716-728
RBM.Univ.UnivMainInst.inst_rho_bounds_zero  730-733
RBM.Univ.UnivMainInst.inst_transfer_band_zero  735-741
RBM.Univ.UnivMainInst.inst_unClaimRowk_band_zero  743-759
RBM.Univ.UnivMainInst.inst_core'_band_zero  761-773
RBM.Univ.UnivMainInst.inst_un_infty1RowC''_band_zero  784-795
RBM.Univ.UnivMainInst.inst_un_infty1RowC''_band_one  797-809
RBM.Univ.UnivMainInst.inst_univMain_transferC_band  811-817
RBM.Univ.UnivMainInst.inst_univMain_transferC_nonzero_mean  819-830
RBM.Univ.UnivMainInst.inst_univMainRowC_band_zero  832-841
RBM.Univ.UnivMainInst.inst_univMainRowC_nonzero_mean  843-857
RBM.Univ.UnivMainInst.inst_unCoreC''_holds_band_zero  859-874
### RBM3D.Universality.Uyw  (5 unreached of 23)
RBM.Univ.uywRow  880-893
RBM.Univ.UywInst.inst_row  918-925
RBM.Univ.UywInst.inst_uywRow  927-933
RBM.Univ.UywInst.inst_unUyw  935-943
RBM.Univ.UywInst.inst_window  945-972
### RBM3D.Universality.UywKernel  (16 unreached of 63)
RBM.Univ.blockM2_self  807-811
private RBM.Univ.UywKernel_norm_eigvec_le_one  1303-1311
RBM.Univ.UywKernelInst.H1  1315-1316
RBM.Univ.UywKernelInst.y0  1318-1318
RBM.Univ.UywKernelInst.y1  1320-1320
RBM.Univ.UywKernelInst.H1_herm  1322-1322
private RBM.Univ.UywKernelInst.I_im_pos  1324-1324
RBM.Univ.UywKernelInst.blockM2_le_432  1326-1351
RBM.Univ.UywKernelInst.inst_self  1353-1357
RBM.Univ.UywKernelInst.inst_eq  1359-1365
RBM.Univ.UywKernelInst.inst_identity2  1367-1379
RBM.Univ.UywKernelInst.inst_bad2  1381-1394
RBM.Univ.UywKernelInst.inst_good  1396-1411
RBM.Univ.UywKernelInst.inst_crude  1413-1424
RBM.Univ.UywKernelInst.H2  1426-1428
RBM.Univ.UywKernelInst.H2_herm  1430-1431
### RBM3D.Universality.ZeroModeProfile  (20 unreached of 55)
RBM.Univ.Stilde  57-59
RBM.Univ.ZeroModeProfile_ouZeta_zero  138-138
RBM.Univ.Stilde_zero  158-160
RBM.Univ.sum_Stilde_row  162-171
RBM.Univ.ouVar_eq_Stilde  173-194
RBM.Univ.Stilde_eq_SBtilde_mul  196-212
private RBM.Univ.ZeroModeProfile_SBtilde_zero  220-221
RBM.Univ.ThetaTilde_zero  223-225
RBM.Univ.profPMTilde_zero  521-526
RBM.Univ.ZeroModeProfileInst.inst_sum_Stilde_row  731-733
RBM.Univ.ZeroModeProfileInst.inst_ouVar_eq_Stilde  735-739
RBM.Univ.ZeroModeProfileInst.inst_ThetaTilde_eq  741-750
RBM.Univ.ZeroModeProfileInst.inst_norm_ThetaTilde_sub_le  752-761
RBM.Univ.ZeroModeProfileInst.inst_profTilde_rowDiff  763-772
RBM.Univ.ZeroModeProfileInst.inst_profPMTilde_zero  774-777
RBM.Univ.ZeroModeProfileInst.inst_ouTauMax  779-782
RBM.Univ.ZeroModeProfileInst.inst_ouTauMax_slack  784-788
RBM.Univ.ZeroModeProfileInst.inst_ouDiag  790-792
RBM.Univ.ZeroModeProfileInst.inst_g1  794-798
RBM.Univ.ZeroModeProfileInst.inst_ouRow  800-802

## (c) modules with no reached declaration (whole module dead), and the modules that import them
- RBM3D.Defs.SemicircleIntegral  (7 declarations plus 0 meta, last one ends at line 217); imported by: RBM3D.Universality.Pins, RBM3D
- RBM3D.Gauss.Envelope  (3 declarations plus 0 meta, last one ends at line 211); imported by: RBM3D
- RBM3D.Graph.AnpKey4  (30 declarations plus 0 meta, last one ends at line 874); imported by: RBM3D.Graph.AnpKey6, RBM3D
- RBM3D.Graph.LWExpCertS0  (96 declarations plus 0 meta, last one ends at line 292); imported by: RBM3D.Graph.LWExpCertS1, RBM3D
- RBM3D.Graph.LWExpCertS1  (97 declarations plus 0 meta, last one ends at line 306); imported by: RBM3D
- RBM3D.Graph.Model  (32 declarations plus 0 meta, last one ends at line 273); imported by: RBM3D
- RBM3D.Induction.QEndA2  (102 declarations plus 0 meta, last one ends at line 1635); imported by: RBM3D
- RBM3D.Induction.QProxy2  (74 declarations plus 0 meta, last one ends at line 833); imported by: RBM3D
- RBM3D.Induction.Step34PinsP  (6 declarations plus 0 meta, last one ends at line 187); imported by: RBM3D.Chain.Step34Gen, RBM3D.Induction.NQEndFlow, RBM3D
- RBM3D.Loop.TreeFour  (8 declarations plus 0 meta, last one ends at line 249); imported by: RBM3D
- RBM3D.Loop.TreeThree  (15 declarations plus 0 meta, last one ends at line 469); imported by: RBM3D.Loop.TreeFour, RBM3D.Loop.KBound, RBM3D.Loop.KLUnique, RBM3D
- RBM3D.Path.DriftAlgebra  (34 declarations plus 0 meta, last one ends at line 756); imported by: RBM3D.Induction.HierAlgebra, RBM3D.Path.Expansion, RBM3D.Induction.ExpHier, RBM3D
- RBM3D.Path.DuhamelTail  (36 declarations plus 0 meta, last one ends at line 908); imported by: RBM3D
- RBM3D.Path.Expansion  (93 declarations plus 0 meta, last one ends at line 1650); imported by: RBM3D.Path.DuhamelTail, RBM3D.Induction.GridDuhamelN, RBM3D
- RBM3D.Path.UTransport  (17 declarations plus 0 meta, last one ends at line 346); imported by: RBM3D
- RBM3D.Propagator.Interface  (3 declarations plus 0 meta, last one ends at line 115); imported by: RBM3D.Kernel.Evolution, RBM3D.Loop.PureLoop, RBM3D.Test.InterfaceShape, RBM3D.Propagator.Pins, RBM3D
- RBM3D.Test.InterfaceShape  (7 declarations plus 0 meta, last one ends at line 418); imported by: RBM3D

## (d) meta list (not candidates for deletion): unreached syntax/macro/elab/parser/tactic-like declarations
### RBM3D.BA.DecayLoopBA: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (2 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_DecayLoopBA___macroRules__private_RBM3D_BA_DecayLoopBA_0_RBM_BA_termμ0_1  154-154
  private RBM.BA._aux_RBM3D_BA_DecayLoopBA___unexpand_RBM_Gauss_Sizes_seqP_1  154-154
  private RBM.BA.termμ0  154-154
### RBM3D.BA.LWPinsBA: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (3 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_LWPinsBA___macroRules__private_RBM3D_BA_LWPinsBA_0_RBM_BA_termμ0_1  81-81
  private RBM.BA._aux_RBM3D_BA_LWPinsBA___unexpand_RBM_Gauss_Sizes_seqP_1  81-81
  private RBM.BA.termμ0  81-81
### RBM3D.BA.MainIndFamTL: 10 unreached meta declaration(s) of 10; file contains reached declarations: yes (10 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_MainIndFamTL___macroRules__private_RBM3D_BA_MainIndFamTL_0_RBM_BA_termμ0_1  278-278
  private RBM.BA._aux_RBM3D_BA_MainIndFamTL___unexpand_RBM_Gauss_Sizes_seqP_1  278-278
  private RBM.BA.termμ0  278-278
  private RBM.BA._aux_RBM3D_BA_MainIndFamTL___macroRules__private_RBM3D_BA_MainIndFamTL_0_RBM_BA_termMem0_1  279-279
  private RBM.BA._aux_RBM3D_BA_MainIndFamTL___unexpand_RBM_BA_BAzSrc_1  279-279
  private RBM.BA.termMem0  279-279
  private RBM.BA.«_aux_RBM3D_BA_MainIndFamTL___macroRules__private_RBM3D_BA_MainIndFamTL_0_RBM_BA_termFam6(_,_,_)_1»  280-281
  private RBM.BA.«termFam6(_,_,_)»  280-281
  private RBM.BA.«_aux_RBM3D_BA_MainIndFamTL___macroRules__private_RBM3D_BA_MainIndFamTL_0_RBM_BA_termFam7(_,_,_)_1»  282-283
  private RBM.BA.«termFam7(_,_,_)»  282-283
### RBM3D.BA.MainIndGlue: 4 unreached meta declaration(s) of 4; file contains reached declarations: yes (16 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_MainIndGlue___macroRules__private_RBM3D_BA_MainIndGlue_0_RBM_BA_termHyp6_1  355-358
  private RBM.BA.termHyp6  355-358
  private RBM.BA._aux_RBM3D_BA_MainIndGlue___macroRules__private_RBM3D_BA_MainIndGlue_0_RBM_BA_termConcl7_1  362-365
  private RBM.BA.termConcl7  362-365
### RBM3D.BA.MainIndOutBA: 6 unreached meta declaration(s) of 6; file contains reached declarations: yes (19 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_MainIndOutBA___macroRules__private_RBM3D_BA_MainIndOutBA_0_RBM_BA_termμ0_1  340-340
  private RBM.BA._aux_RBM3D_BA_MainIndOutBA___unexpand_RBM_Gauss_Sizes_seqP_1  340-340
  private RBM.BA.termμ0  340-340
  private RBM.BA._aux_RBM3D_BA_MainIndOutBA___macroRules__private_RBM3D_BA_MainIndOutBA_0_RBM_BA_termMem0_1  341-341
  private RBM.BA._aux_RBM3D_BA_MainIndOutBA___unexpand_RBM_BA_BAzSrc_1  341-341
  private RBM.BA.termMem0  341-341
### RBM3D.BA.MainIndRegBA: 10 unreached meta declaration(s) of 10; file contains reached declarations: yes (5 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_MainIndRegBA___macroRules__private_RBM3D_BA_MainIndRegBA_0_RBM_BA_termμ0_1  68-68
  private RBM.BA._aux_RBM3D_BA_MainIndRegBA___unexpand_RBM_Gauss_Sizes_seqP_1  68-68
  private RBM.BA.termμ0  68-68
  private RBM.BA._aux_RBM3D_BA_MainIndRegBA___macroRules__private_RBM3D_BA_MainIndRegBA_0_RBM_BA_termMem0_1  69-69
  private RBM.BA._aux_RBM3D_BA_MainIndRegBA___unexpand_RBM_BA_BAzSrc_1  69-69
  private RBM.BA.termMem0  69-69
  private RBM.BA.«_aux_RBM3D_BA_MainIndRegBA___macroRules__private_RBM3D_BA_MainIndRegBA_0_RBM_BA_termFam6(_,_,_)_1»  70-71
  private RBM.BA.«termFam6(_,_,_)»  70-71
  private RBM.BA.«_aux_RBM3D_BA_MainIndRegBA___macroRules__private_RBM3D_BA_MainIndRegBA_0_RBM_BA_termFam7(_,_,_)_1»  72-73
  private RBM.BA.«termFam7(_,_,_)»  72-73
### RBM3D.BA.MainIndTermBA: 10 unreached meta declaration(s) of 10; file contains reached declarations: yes (2 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_MainIndTermBA___macroRules__private_RBM3D_BA_MainIndTermBA_0_RBM_BA_termμ0_1  69-69
  private RBM.BA._aux_RBM3D_BA_MainIndTermBA___unexpand_RBM_Gauss_Sizes_seqP_1  69-69
  private RBM.BA.termμ0  69-69
  private RBM.BA._aux_RBM3D_BA_MainIndTermBA___macroRules__private_RBM3D_BA_MainIndTermBA_0_RBM_BA_termMem0_1  70-70
  private RBM.BA._aux_RBM3D_BA_MainIndTermBA___unexpand_RBM_BA_BAzSrc_1  70-70
  private RBM.BA.termMem0  70-70
  private RBM.BA.«_aux_RBM3D_BA_MainIndTermBA___macroRules__private_RBM3D_BA_MainIndTermBA_0_RBM_BA_termFam6(_,_,_)_1»  71-72
  private RBM.BA.«termFam6(_,_,_)»  71-72
  private RBM.BA.«_aux_RBM3D_BA_MainIndTermBA___macroRules__private_RBM3D_BA_MainIndTermBA_0_RBM_BA_termFam7(_,_,_)_1»  73-74
  private RBM.BA.«termFam7(_,_,_)»  73-74
### RBM3D.BA.Step2CloseBA: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (5 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_Step2CloseBA___macroRules__private_RBM3D_BA_Step2CloseBA_0_RBM_BA_termμ0_1  208-208
  private RBM.BA._aux_RBM3D_BA_Step2CloseBA___unexpand_RBM_Gauss_Sizes_seqP_1  208-208
  private RBM.BA.termμ0  208-208
### RBM3D.BA.Step6BA: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (10 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_Step6BA___macroRules__private_RBM3D_BA_Step6BA_0_RBM_BA_termμ0_1  173-173
  private RBM.BA._aux_RBM3D_BA_Step6BA___unexpand_RBM_Gauss_Sizes_seqP_1  173-173
  private RBM.BA.termμ0  173-173
### RBM3D.BA.Step6BridgeBA: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (12 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_Step6BridgeBA___macroRules__private_RBM3D_BA_Step6BridgeBA_0_RBM_BA_termμ0_1  349-349
  private RBM.BA._aux_RBM3D_BA_Step6BridgeBA___unexpand_RBM_Gauss_Sizes_seqP_1  349-349
  private RBM.BA.termμ0  349-349
### RBM3D.BA.Step6PinsBA: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (17 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_Step6PinsBA___macroRules__private_RBM3D_BA_Step6PinsBA_0_RBM_BA_termμ0_1  303-303
  private RBM.BA._aux_RBM3D_BA_Step6PinsBA___unexpand_RBM_Gauss_Sizes_seqP_1  303-303
  private RBM.BA.termμ0  303-303
### RBM3D.BA.TwistAvgA2: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (51 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistAvgA2___macroRules__private_RBM3D_BA_TwistAvgA2_0_RBM_BA_termμ0_1  1164-1164
  private RBM.BA._aux_RBM3D_BA_TwistAvgA2___unexpand_RBM_Gauss_Sizes_seqP_1  1164-1164
  private RBM.BA.termμ0  1164-1164
### RBM3D.BA.TwistAvgB: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (14 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistAvgB___macroRules__private_RBM3D_BA_TwistAvgB_0_RBM_BA_termμ0_1  461-461
  private RBM.BA._aux_RBM3D_BA_TwistAvgB___unexpand_RBM_Gauss_Sizes_seqP_1  461-461
  private RBM.BA.termμ0  461-461
### RBM3D.BA.TwistChain: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (14 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistChain___macroRules__private_RBM3D_BA_TwistChain_0_RBM_BA_termμ0_1  271-271
  private RBM.BA._aux_RBM3D_BA_TwistChain___unexpand_RBM_Gauss_Sizes_seqP_1  271-271
  private RBM.BA.termμ0  271-271
### RBM3D.BA.TwistGrid: 6 unreached meta declaration(s) of 6; file contains reached declarations: yes (58 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistGrid___macroRules__private_RBM3D_BA_TwistGrid_0_RBM_BA_termLam₀_1  909-909
  private RBM.BA._aux_RBM3D_BA_TwistGrid___unexpand_RBM_BA_BAflowLam0_1  909-909
  private RBM.BA.termLam₀  909-909
  private RBM.BA._aux_RBM3D_BA_TwistGrid___macroRules__private_RBM3D_BA_TwistGrid_0_RBM_BA_termE₀_1  910-910
  private RBM.BA._aux_RBM3D_BA_TwistGrid___unexpand_RBM_BA_BAflowEs_1  910-910
  private RBM.BA.termE₀  910-910
### RBM3D.BA.TwistKer2: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (42 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistKer2___macroRules__private_RBM3D_BA_TwistKer2_0_RBM_BA_termμ0_1  1378-1378
  private RBM.BA._aux_RBM3D_BA_TwistKer2___unexpand_RBM_Gauss_Sizes_seqP_1  1378-1378
  private RBM.BA.termμ0  1378-1378
### RBM3D.BA.TwistLoop: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (27 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistLoop___macroRules__private_RBM3D_BA_TwistLoop_0_RBM_BA_termμ0_1  838-838
  private RBM.BA._aux_RBM3D_BA_TwistLoop___unexpand_RBM_Gauss_Sizes_seqP_1  838-838
  private RBM.BA.termμ0  838-838
### RBM3D.BA.TwistPins: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (70 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistPins___macroRules__private_RBM3D_BA_TwistPins_0_RBM_BA_termμ0_1  763-763
  private RBM.BA._aux_RBM3D_BA_TwistPins___unexpand_RBM_Gauss_Sizes_seqP_1  763-763
  private RBM.BA.termμ0  763-763
### RBM3D.BA.TwistQV: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (62 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistQV___macroRules__private_RBM3D_BA_TwistQV_0_RBM_BA_termμ0_1  1396-1396
  private RBM.BA._aux_RBM3D_BA_TwistQV___unexpand_RBM_Gauss_Sizes_seqP_1  1396-1396
  private RBM.BA.termμ0  1396-1396
### RBM3D.BA.TwistStep2: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (51 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_BA_TwistStep2___macroRules__private_RBM3D_BA_TwistStep2_0_RBM_BA_termμ0_1  1438-1438
  private RBM.BA._aux_RBM3D_BA_TwistStep2___unexpand_RBM_Gauss_Sizes_seqP_1  1438-1438
  private RBM.BA.termμ0  1438-1438
### RBM3D.Defs.Domination: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (5 non-meta, 0 meta)
  RBM._aux_RBM3D_Defs_Domination___unexpand_RBM_DetDom_1  60-60
  RBM.«_aux_RBM3D_Defs_Domination___macroRules_RBM_term_≺__1»  60-60
  RBM.«term_≺_»  60-60
### RBM3D.Graph.BAAnpLift: 15 unreached meta declaration(s) of 15; file contains reached declarations: yes (8 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BAAnpLift___macroRules__private_RBM3D_Graph_BAAnpLift_0_RBM_Graph_termμ0_1  277-277
  private RBM.Graph._aux_RBM3D_Graph_BAAnpLift___unexpand_RBM_Gauss_Sizes_seqP_1  277-277
  private RBM.Graph.termμ0  277-277
  private RBM.Graph._aux_RBM3D_Graph_BAAnpLift___macroRules__private_RBM3D_Graph_BAAnpLift_0_RBM_Graph_termΦb_1  282-282
  private RBM.Graph._aux_RBM3D_Graph_BAAnpLift___unexpand__private_RBM3D_Graph_BAAuxGraph2B_0_RBM_Graph_BAAuxGraph2B_Φ0_1  282-282
  private RBM.Graph.termΦb  282-282
  private RBM.Graph._aux_RBM3D_Graph_BAAnpLift___macroRules__private_RBM3D_Graph_BAAnpLift_0_RBM_Graph_termζ0_1  283-283
  private RBM.Graph._aux_RBM3D_Graph_BAAnpLift___unexpand_RBM_Graph_baZetaVar_1  283-283
  private RBM.Graph.termζ0  283-283
  private RBM.BA._aux_RBM3D_Graph_BAAnpLift___macroRules__private_RBM3D_Graph_BAAnpLift_0_RBM_BA_termμ0_1  355-355
  private RBM.BA._aux_RBM3D_Graph_BAAnpLift___unexpand_RBM_Gauss_Sizes_seqP_1  355-355
  private RBM.BA.termμ0  355-355
  private RBM.BA._aux_RBM3D_Graph_BAAnpLift___macroRules__private_RBM3D_Graph_BAAnpLift_0_RBM_BA_termℓh_1  356-356
  private RBM.BA._aux_RBM3D_Graph_BAAnpLift___unexpand_RBM_Gauss_LWInst_ℓT_1  356-356
  private RBM.BA.termℓh  356-356
### RBM3D.Graph.BAAuxGraph2B: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (19 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BAAuxGraph2B___macroRules__private_RBM3D_Graph_BAAuxGraph2B_0_RBM_Graph_termμ0_1  891-891
  private RBM.Graph._aux_RBM3D_Graph_BAAuxGraph2B___unexpand_RBM_Gauss_Sizes_seqP_1  891-891
  private RBM.Graph.termμ0  891-891
### RBM3D.Graph.BAExp14a2: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (23 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAExp14a2___macroRules__private_RBM3D_Graph_BAExp14a2_0_RBM_BA_termμ0_1  339-339
  private RBM.BA._aux_RBM3D_Graph_BAExp14a2___unexpand_RBM_Gauss_Sizes_seqP_1  339-339
  private RBM.BA.termμ0  339-339
### RBM3D.Graph.BAExp14aB: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (102 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAExp14aB___macroRules__private_RBM3D_Graph_BAExp14aB_0_RBM_BA_termμ0_1  1736-1736
  private RBM.BA._aux_RBM3D_Graph_BAExp14aB___unexpand_RBM_Gauss_Sizes_seqP_1  1736-1736
  private RBM.BA.termμ0  1736-1736
### RBM3D.Graph.BAExp14b: 9 unreached meta declaration(s) of 9; file contains reached declarations: yes (71 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAExp14b___macroRules__private_RBM3D_Graph_BAExp14b_0_RBM_BA_tacticBf_elim_1  660-663
  private RBM.BA.tacticBf_elim  660-663
  private RBM.BA._aux_RBM3D_Graph_BAExp14b___macroRules__private_RBM3D_Graph_BAExp14b_0_RBM_BA_tacticBf_flat_1  666-666
  private RBM.BA.tacticBf_flat  666-666
  private RBM.BA._aux_RBM3D_Graph_BAExp14b___macroRules__private_RBM3D_Graph_BAExp14b_0_RBM_BA_tacticBf_fin_1  669-669
  private RBM.BA.tacticBf_fin  669-669
  private RBM.BA._aux_RBM3D_Graph_BAExp14b___macroRules__private_RBM3D_Graph_BAExp14b_0_RBM_BA_termμ0_1  916-916
  private RBM.BA._aux_RBM3D_Graph_BAExp14b___unexpand_RBM_Gauss_Sizes_seqP_1  916-916
  private RBM.BA.termμ0  916-916
### RBM3D.Graph.BAExp14b2: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (57 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAExp14b2___macroRules__private_RBM3D_Graph_BAExp14b2_0_RBM_BA_termμ0_1  1675-1675
  private RBM.BA._aux_RBM3D_Graph_BAExp14b2___unexpand_RBM_BA_BAExp14a_μ_1  1675-1675
  private RBM.BA.termμ0  1675-1675
### RBM3D.Graph.BAExp14b2B: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (39 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAExp14b2B___macroRules__private_RBM3D_Graph_BAExp14b2B_0_RBM_BA_termμ0_1  1095-1095
  private RBM.BA._aux_RBM3D_Graph_BAExp14b2B___unexpand_RBM_BA_BAExp14a_μ_1  1095-1095
  private RBM.BA.termμ0  1095-1095
### RBM3D.Graph.BAExp14bB: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (73 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAExp14bB___macroRules__private_RBM3D_Graph_BAExp14bB_0_RBM_BA_tacticBm_tac_1  483-497
  private RBM.BA.tacticBm_tac  483-497
### RBM3D.Graph.BAExp14c: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (41 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAExp14c___macroRules__private_RBM3D_Graph_BAExp14c_0_RBM_BA_tacticBAExp14c_peel_1  108-108
  private RBM.BA.tacticBAExp14c_peel  108-108
### RBM3D.Graph.BAExp14dB: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (21 non-meta, 0 meta)
  private RBM.BA.BAExp14dInst._aux_RBM3D_Graph_BAExp14dB___macroRules__private_RBM3D_Graph_BAExp14dB_0_RBM_BA_BAExp14dInst_termμ0_1  860-860
  private RBM.BA.BAExp14dInst._aux_RBM3D_Graph_BAExp14dB___unexpand_RBM_Gauss_Sizes_seqP_1  860-860
  private RBM.BA.BAExp14dInst.termμ0  860-860
### RBM3D.Graph.BAExp14e: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (7 non-meta, 0 meta)
  private RBM.BA.BAExp14eInst._aux_RBM3D_Graph_BAExp14e___macroRules__private_RBM3D_Graph_BAExp14e_0_RBM_BA_BAExp14eInst_termμ0_1  361-361
  private RBM.BA.BAExp14eInst._aux_RBM3D_Graph_BAExp14e___unexpand_RBM_Gauss_Sizes_seqP_1  361-361
  private RBM.BA.BAExp14eInst.termμ0  361-361
### RBM3D.Graph.BAExpand: 4 unreached meta declaration(s) of 4; file contains reached declarations: yes (46 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BAExpand___macroRules__private_RBM3D_Graph_BAExpand_0_RBM_Graph_tacticBa_tame_1  586-597
  private RBM.Graph.tacticBa_tame  586-597
  private RBM.Graph._aux_RBM3D_Graph_BAExpand___macroRules__private_RBM3D_Graph_BAExpand_0_RBM_Graph_tacticBa_tame_1_1  708-719
  private RBM.Graph.tacticBa_tame_1  708-719
### RBM3D.Graph.BAExpandW: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (42 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BAExpandW___macroRules__private_RBM3D_Graph_BAExpandW_0_RBM_Graph_tacticBaw_tame_1  281-292
  private RBM.Graph.tacticBaw_tame  281-292
### RBM3D.Graph.BAGGExp: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (24 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BAGGExp___macroRules__private_RBM3D_Graph_BAGGExp_0_RBM_Graph_tacticBagg_tl_1  342-352
  private RBM.Graph.tacticBagg_tl  342-352
### RBM3D.Graph.BAGGOp: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (91 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BAGGOp___macroRules__private_RBM3D_Graph_BAGGOp_0_RBM_Graph_tacticBgo_tame_1  504-515
  private RBM.Graph.tacticBgo_tame  504-515
### RBM3D.Graph.BALWOut: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (1 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BALWOut___macroRules__private_RBM3D_Graph_BALWOut_0_RBM_BA_termμ0_1  71-71
  private RBM.BA._aux_RBM3D_Graph_BALWOut___unexpand_RBM_Gauss_Sizes_seqP_1  71-71
  private RBM.BA.termμ0  71-71
### RBM3D.Graph.BALocReg2: 4 unreached meta declaration(s) of 4; file contains reached declarations: yes (32 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BALocReg2___macroRules__private_RBM3D_Graph_BALocReg2_0_RBM_Graph_tacticBALocReg2_simp0_1  260-262
  private RBM.Graph.tacticBALocReg2_simp0  260-262
  private RBM.Graph._aux_RBM3D_Graph_BALocReg2___macroRules__private_RBM3D_Graph_BALocReg2_0_RBM_Graph_tacticBALocReg2_msnorm_1  264-264
  private RBM.Graph.tacticBALocReg2_msnorm  264-264
### RBM3D.Graph.BALocReg2B: 4 unreached meta declaration(s) of 4; file contains reached declarations: yes (15 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BALocReg2B___macroRules__private_RBM3D_Graph_BALocReg2B_0_RBM_Graph_tacticBALocReg2B_simp0_1  51-53
  private RBM.Graph.tacticBALocReg2B_simp0  51-53
  private RBM.Graph._aux_RBM3D_Graph_BALocReg2B___macroRules__private_RBM3D_Graph_BALocReg2B_0_RBM_Graph_tacticBALocReg2B_msnorm_1  55-55
  private RBM.Graph.tacticBALocReg2B_msnorm  55-55
### RBM3D.Graph.BAMomentExpGen: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (23 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAMomentExpGen___macroRules__private_RBM3D_Graph_BAMomentExpGen_0_RBM_BA_termμ0_1  908-908
  private RBM.BA._aux_RBM3D_Graph_BAMomentExpGen___unexpand_RBM_Gauss_Sizes_seqP_1  908-908
  private RBM.BA.termμ0  908-908
### RBM3D.Graph.BAMomentExpGenB: 6 unreached meta declaration(s) of 6; file contains reached declarations: yes (27 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAMomentExpGenB___macroRules__private_RBM3D_Graph_BAMomentExpGenB_0_RBM_BA_termμ0_1  1221-1221
  private RBM.BA._aux_RBM3D_Graph_BAMomentExpGenB___unexpand_RBM_Gauss_Sizes_seqP_1  1221-1221
  private RBM.BA.termμ0  1221-1221
  private RBM.BA._aux_RBM3D_Graph_BAMomentExpGenB___macroRules__private_RBM3D_Graph_BAMomentExpGenB_0_RBM_BA_termℓh_1  1222-1222
  private RBM.BA._aux_RBM3D_Graph_BAMomentExpGenB___unexpand_RBM_Gauss_LWInst_ℓT_1  1222-1222
  private RBM.BA.termℓh  1222-1222
### RBM3D.Graph.BAMomentGenB: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (13 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BAMomentGenB___macroRules__private_RBM3D_Graph_BAMomentGenB_0_RBM_BA_termμ0_1  440-440
  private RBM.BA._aux_RBM3D_Graph_BAMomentGenB___unexpand_RBM_Gauss_Sizes_seqP_1  440-440
  private RBM.BA.termμ0  440-440
### RBM3D.Graph.BAS3CloseC: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (93 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BAS3CloseC___macroRules__private_RBM3D_Graph_BAS3CloseC_0_RBM_Graph_tacticBAS3Close_peel_1  506-506
  private RBM.Graph.tacticBAS3Close_peel  506-506
### RBM3D.Graph.BATermHolds: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (23 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BATermHolds___macroRules__private_RBM3D_Graph_BATermHolds_0_RBM_BA_termμ0_1  877-877
  private RBM.BA._aux_RBM3D_Graph_BATermHolds___unexpand_RBM_Gauss_Sizes_seqP_1  877-877
  private RBM.BA.termμ0  877-877
### RBM3D.Graph.BATermHoldsB: 3 unreached meta declaration(s) of 3; file contains reached declarations: yes (16 non-meta, 0 meta)
  private RBM.BA._aux_RBM3D_Graph_BATermHoldsB___macroRules__private_RBM3D_Graph_BATermHoldsB_0_RBM_BA_termμ0_1  893-893
  private RBM.BA._aux_RBM3D_Graph_BATermHoldsB___unexpand_RBM_Gauss_Sizes_seqP_1  893-893
  private RBM.BA.termμ0  893-893
### RBM3D.Graph.BAWeightOp: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (80 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_BAWeightOp___macroRules__private_RBM3D_Graph_BAWeightOp_0_RBM_Graph_tacticBwo_tame_1  380-391
  private RBM.Graph.tacticBwo_tame  380-391
### RBM3D.Graph.LWEdgeExp: 4 unreached meta declaration(s) of 4; file contains reached declarations: yes (32 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_LWEdgeExp___macroRules__private_RBM3D_Graph_LWEdgeExp_0_RBM_Graph_tacticOe1x_tame_1  66-76
  private RBM.Graph.tacticOe1x_tame  66-76
  private RBM.Graph._aux_RBM3D_Graph_LWEdgeExp___macroRules__private_RBM3D_Graph_LWEdgeExp_0_RBM_Graph_tacticOe1x_tame_1_1  438-448
  private RBM.Graph.tacticOe1x_tame_1  438-448
### RBM3D.Graph.LWEngine: 4 unreached meta declaration(s) of 4; file contains reached declarations: yes (70 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_LWEngine___macroRules__private_RBM3D_Graph_LWEngine_0_RBM_Graph_tacticLwEngine_gen_1  203-209
  private RBM.Graph.tacticLwEngine_gen  203-209
  private RBM.Graph._aux_RBM3D_Graph_LWEngine___macroRules__private_RBM3D_Graph_LWEngine_0_RBM_Graph_tacticLwEngine_nws_1  484-491
  private RBM.Graph.tacticLwEngine_nws  484-491
### RBM3D.Graph.LWGGExp: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (36 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_LWGGExp___macroRules__private_RBM3D_Graph_LWGGExp_0_RBM_Graph_tacticOe2x_tame_1  62-72
  private RBM.Graph.tacticOe2x_tame  62-72
### RBM3D.Graph.LWStein: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (77 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_LWStein___macroRules__private_RBM3D_Graph_LWStein_0_RBM_Graph_tacticLw_tame_1  1223-1233
  private RBM.Graph.tacticLw_tame  1223-1233
### RBM3D.Graph.LWWeightExp: 2 unreached meta declaration(s) of 2; file contains reached declarations: yes (48 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_LWWeightExp___macroRules__private_RBM3D_Graph_LWWeightExp_0_RBM_Graph_tacticLwx_tame_1  354-364
  private RBM.Graph.tacticLwx_tame  354-364
### RBM3D.Graph.LocalRegular: 4 unreached meta declaration(s) of 4; file contains reached declarations: yes (80 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_LocalRegular___macroRules__private_RBM3D_Graph_LocalRegular_0_RBM_Graph_tacticLocalReg_msnorm_1  844-846
  private RBM.Graph.tacticLocalReg_msnorm  844-846
  private RBM.Graph._aux_RBM3D_Graph_LocalRegular___macroRules__private_RBM3D_Graph_LocalRegular_0_RBM_Graph_tacticLocalReg_msnormx_1  851-853
  private RBM.Graph.tacticLocalReg_msnormx  851-853
### RBM3D.Graph.LocalRegular2: 6 unreached meta declaration(s) of 6; file contains reached declarations: yes (91 non-meta, 0 meta)
  private RBM.Graph._aux_RBM3D_Graph_LocalRegular2___macroRules__private_RBM3D_Graph_LocalRegular2_0_RBM_Graph_tacticLocalReg2_simp0_1  908-908
  private RBM.Graph.tacticLocalReg2_simp0  908-908
  private RBM.Graph._aux_RBM3D_Graph_LocalRegular2___macroRules__private_RBM3D_Graph_LocalRegular2_0_RBM_Graph_tacticLocalReg2_msnorm_1  910-910
  private RBM.Graph.tacticLocalReg2_msnorm  910-910
  private RBM.Graph._aux_RBM3D_Graph_LocalRegular2___macroRules__private_RBM3D_Graph_LocalRegular2_0_RBM_Graph_tacticLocalReg2_msnormx_1  1190-1190
  private RBM.Graph.tacticLocalReg2_msnormx  1190-1190
### RBM3D.Induction.QBudgetA: 6 unreached meta declaration(s) of 6; file contains reached declarations: yes (32 non-meta, 0 meta)
  private RBM.Ind.QBudgetAInst._aux_RBM3D_Induction_QBudgetA___macroRules__private_RBM3D_Induction_QBudgetA_0_RBM_Ind_QBudgetAInst_termC4₀_1  1311-1311
  private RBM.Ind.QBudgetAInst._aux_RBM3D_Induction_QBudgetA___unexpand_RBM_Ind_qProxy4C_1  1311-1311
  private RBM.Ind.QBudgetAInst.termC4₀  1311-1311
  private RBM.Ind.QBudgetAInst._aux_RBM3D_Induction_QBudgetA___macroRules__private_RBM3D_Induction_QBudgetA_0_RBM_Ind_QBudgetAInst_termCn₀_1  1312-1312
  private RBM.Ind.QBudgetAInst._aux_RBM3D_Induction_QBudgetA___unexpand_RBM_Ind_qProxyCn_1  1312-1312
  private RBM.Ind.QBudgetAInst.termCn₀  1312-1312

## (e) totals
- modules in scope: 673; with counted declarations: 670
- declarations (non-meta units): 32770; meta declarations: 222 (unreached meta: 213)
- unreached (non-meta): 10243
- sum of unreached line spans (end-start+1 per declaration): 100272
- unreached lines counted once (union of the intervals per module): 100264
- modules with no reached declaration: 17

## (f) optional groups: declarations and lines kept alive beyond the core closure

### G1: constants of the `example`s in Main/BandTerminal.lean §Instances
- roots: 20; already reached in the core: 16; not reached in the core: 4 (RBM.Endpoints.Inst.inst_bridge_loc, RBM.Endpoints.Inst.inst_bridge_que, RBM.Endpoints.unOUClaims_holds, RBM.Endpoints.unOUQUE_holds)
- extra over the core: 4 declarations (non-meta), 0 meta declarations; sum of line spans 27; lines counted once (union per module) 27; modules touched 2
- five largest modules it keeps alive (module: declarations, line spans):
  - RBM3D.Endpoints: 2 declarations, 16 lines
  - RBM3D.Main.BandTerminal: 2 declarations, 11 lines

### G2: constants of the `example`s in BA/MAPins.lean
- roots: 31; already reached in the core: 22; not reached in the core: 9 (private RBM.BA.MAPins_hg, RBM.BA.BAMAFixed, RBM.Univ.BAInst.inst_locAvg_domain, RBM.Univ.UNLocAvgBA, RBM.Univ.UNTrLocalBARow, RBM.Univ.UNTrLocalInitBARow', RBM.BA.UNLocAvgBA_iff_at, RBM.BA.UNTrLocalBARow_iff_at, RBM.BA.UNTrLocalInitBARow'_iff_at)
- extra over the core: 10 declarations (non-meta), 0 meta declarations; sum of line spans 53; lines counted once (union per module) 53; modules touched 3
- five largest modules it keeps alive (module: declarations, line spans):
  - RBM3D.BA.MAPins: 5 declarations, 11 lines
  - RBM3D.BA.UNPins: 4 declarations, 32 lines
  - RBM3D.Universality.PinsK: 1 declarations, 10 lines

### G3: the general-`d` BA forms
- roots: 3; already reached in the core: 2; not reached in the core: 1 (RBM.BA.baThm27L_any)
- extra over the core: 2 declarations (non-meta), 0 meta declarations; sum of line spans 12; lines counted once (union per module) 12; modules touched 2
- five largest modules it keeps alive (module: declarations, line spans):
  - RBM3D.BA.MainIndTermBA: 1 declarations, 6 lines
  - RBM3D.BA.UNBUniv: 1 declarations, 6 lines

### G4: `bUniv_holds` and the constants of the `example`s in Main/BUnivHolds.lean
- roots: 16; already reached in the core: 16; not reached in the core: 0
- extra over the core: 0 declarations (non-meta), 0 meta declarations; sum of line spans 0; lines counted once (union per module) 0; modules touched 0
- five largest modules it keeps alive (module: declarations, line spans):
  (none: the group is inside the core)

## (g) name lists of the Audit registry (`RBM3D/Test/Axioms.lean`): names unreached in the core
- source file read: 667 lines
### RBM.Audit.allowedAxioms  (lines 59-60): 3 names, 0 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.borrowedProps  (lines 84-93): 2 names, 2 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.certificates  (lines 440-453): 0 names, 0 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.interfaceAxioms  (lines 62-67): 0 names, 0 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.interfaceProps  (lines 437-438): 0 names, 0 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.owedProps  (lines 95-232): 111 names, 111 in scope, 11 unreached in the core, 0 not constants
  RBM.Gauss.Sizes.STBootstrap  line 109
  RBM.Gauss.Sizes.STForbidden  line 110
  RBM.Gauss.Sizes.STIterR  line 117
  RBM.Gauss.Sizes.STOeqNQ  line 118
  RBM.Gauss.Sizes.STXiBoot  line 119
  RBM.Gauss.Sizes.STStep2Parts  line 164
  RBM.BA.STImproveExpAvergL  line 217
  RBM.BA.ExpAvgGen_W1iiiOfLW  line 220
  RBM.BA.STExpIniIgL  line 226
  RBM.BA.STExpIntIgL  line 227
  RBM.BA.LWtermEXPG  line 231
### RBM.Audit.refutedProps  (lines 391-406): 7 names, 7 in scope, 4 unreached in the core, 0 not constants
  RBM.Univ.UNInfty1Row  line 401
  RBM.Univ.UNCoreC  line 403
  RBM.Univ.UNStep1GoodC'  line 405
  RBM.Univ.UNCoreC'  line 406
### RBM.Audit.structuralProps  (lines 234-389): 148 names, 148 in scope, 23 unreached in the core, 0 not constants
  RBM.SameSignOutside  line 242
  RBM.Graph.Case.Rel  line 243
  RBM.NormStochDom  line 244
  RBM.NormStochDomAt  line 245
  RBM.Graph.LGraph.DotWF  line 265
  RBM.Graph.NGraph.EndAt  line 274
  RBM.Graph.NGraph.IsA1  line 275
  RBM.Graph.NGraph.IsA2  line 276
  RBM.Graph.NGraph.IsB1  line 277
  RBM.Graph.NGraph.IsB2  line 278
  RBM.Graph.AnpCaseIII  line 279
  RBM.Graph.NGraph.NoA2  line 280
  RBM.Graph.lvl1Split.below  line 290
  RBM.Graph.Lvl1Reach.below  line 291
  RBM.Graph.BAReach.below  line 292
  RBM.Path.UkerFar  line 294
  RBM.Gauss.Sizes.STExpIntQConcl  line 336
  RBM.Gauss.Sizes.STExpIniIConcl  line 337
  RBM.BA.STStep6RgL  line 346
  RBM.BA.STExpIntQConclgL  line 356
  RBM.BA.STExpIniIConclgL  line 357
  RBM.Univ.UNQuek  line 381
  RBM.Univ.UNLocAvgk  line 382
### RBM.Audit.supersededProps  (lines 408-435): 19 names, 19 in scope, 16 unreached in the core, 0 not constants
  RBM.Gauss.Sizes.STStep3  line 417
  RBM.BA.BAConArg'  line 418
  RBM.Gauss.Sizes.STStep3I  line 419
  RBM.Gauss.Sizes.STStep4  line 420
  RBM.Gauss.Sizes.STStep5  line 421
  RBM.Gauss.Sizes.STStep6  line 422
  RBM.BA.STStep6gL  line 423
  RBM.Gauss.Sizes.STExpIniI  line 424
  RBM.Gauss.Sizes.STExpIntI  line 425
  RBM.Gauss.Sizes.STOeqNQ'  line 426
  RBM.Gauss.Sizes.STOeqQt  line 427
  RBM.Gauss.Sizes.STOeqQtNZ  line 428
  RBM.Gauss.Sizes.STIterations  line 429
  RBM.Gauss.Sizes.STIterationsII  line 430
  RBM.Gauss.Sizes.LWG5Expand  line 431
  RBM.BA.BAGbEXPij  line 435
- totals over 9 name lists: 290 names, 287 in scope, 54 unreached in the core
```

## Summary table (core; copied by script from section (e) above)

| quantity | value |
|---|---|
| modules in scope / with counted declarations | 673 / 670 |
| declarations (non-meta units) | 32770 |
| meta declarations (unreached meta) | 222 (213) |
| unreached declarations (non-meta) | 10243 |
| sum of unreached line spans | 100272 |
| unreached lines counted once (union per module) | 100264 |
| modules with no reached declaration | 17 |

## Group table (optional groups beyond the core; copied by script from section (f) above)

| group | roots (in core / not) | extra declarations | extra meta | line spans | lines once | modules | five largest modules kept alive |
|---|---|---|---|---|---|---|---|
| G1 | 20 (16 / 4) | 4 | 0 | 27 | 27 | 2 | RBM3D.Endpoints (2 decl, 16 lines); RBM3D.Main.BandTerminal (2 decl, 11 lines) |
| G2 | 31 (22 / 9) | 10 | 0 | 53 | 53 | 3 | RBM3D.BA.MAPins (5 decl, 11 lines); RBM3D.BA.UNPins (4 decl, 32 lines); RBM3D.Universality.PinsK (1 decl, 10 lines) |
| G3 | 3 (2 / 1) | 2 | 0 | 12 | 12 | 2 | RBM3D.BA.MainIndTermBA (1 decl, 6 lines); RBM3D.BA.UNBUniv (1 decl, 6 lines) |
| G4 | 16 (16 / 0) | 0 | 0 | 0 | 0 | 0 | (none: inside the core) |
