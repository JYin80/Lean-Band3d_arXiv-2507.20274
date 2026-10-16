/-
Release check for T2519 (dispatcher V5, 2026-10-16 10:34 UTC; DECISIONS §348; supervisor 2026-10-15-1044 Q1-Q4,
C5S-C1-C4; drafted by dispatcher V4's helper 2026-10-15, DECISIONS §343-§344). BA stage M/N row C5 (T2449 §5 `:136`;
T2173 pm `:277`, `:288`): the BA §7.2 random layer on the GUE-phase grid and the BA producers of `RBG_Prod`,
`RandomLayerB_LL`, `RBG_Que` at `UNKind.ba`.
Part 1: merged names (`file:line` as of `main` 13b68cea). Part 3: the names of C4 a (ff7bd277), C4 b (26561542) and
C3 b (fde07256), now merged. Every full name was checked against `main` fde07256 with `docs/claude-team/tools/nsof.sh`.
The proposals `T2519_*` (not binding until the 1a-audit) are in `docs/tickets/checks/T2519-pins.lean`, compiled for
information only; this file is the release gate.
Statements only; no proofs.
Run: lake env lean docs/tickets/checks/T2519-check.lean
-/
import RBM3D.BA.GUEKPrim
import RBM3D.BA.KBound
import RBM3D.BA.KCactus
import RBM3D.BA.GreenStab
import RBM3D.BA.GUEOneLoop
import RBM3D.BA.GUEEq729BA
import RBM3D.BA.GUEEntry2

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 1: merged names -/

-- C5g (T2475): the generic successors and the BA vocabulary; the N2 reading is `BA/RandomLayerBGBA:199-212`
#check @RBM.Univ.GUEPhase.RBG_Prod                  -- Universality/GUEPhase/RandomLayerBG:72 (target of `ba_prodG`)

#check @RBM.Univ.GUEPhase.RBG_Que                   -- RandomLayerBG:87 (target of `ba_QueG`)

#check @RBM.Univ.GUEPhase.RandomLayerB_LL           -- Universality/GUEPhase/RandomLayerB:151 (target of `ba_LLG`, unprimed)

#check @RBM.Univ.GUEPhase.RBG_Flow                  -- RandomLayerBG:59

#check @RBM.Univ.GUEPhase.RBG_Dom                   -- RandomLayerBG:65

#check @RBM.Univ.GUEPhase.RBG_Comp                  -- RandomLayerBG:115

#check @RBM.Univ.GUEPhase.RBG_ProfComp              -- RandomLayerBG:123

#check @RBM.Univ.GUEPhase.g1Rowk_of_inputsG         -- RandomLayerBG:399 (N2 instantiates it at `UNKind.ba`)

#check @RBM.Univ.GUEPhase.RandomLayerB_MLout        -- RandomLayerB:123

#check @RBM.Univ.GUEPhase.RandomLayerB_LLAt         -- RandomLayerB:76

#check @RBM.Univ.GUEPhase.RandomLayerB_QueAt        -- RandomLayerB:83

#check @RBM.Univ.GUEPhase.RandomLayerB_KFam         -- RandomLayerB:63 (band twin of `BAKFam`)

#check @RBM.Univ.GUEPhase.RandomLayerB_PBband       -- RandomLayerB:346 (band twin of `BAPB`)

#check @RBM.Univ.GUEPhase.RandomLayerB_prod_band    -- RandomLayerB:400 (band twin of `ba_prodG`)

#check @RBM.Univ.GUEPhase.RandomLayerB_LL_band      -- RandomLayerB:427 (band twin of `ba_LLG`)

#check @RBM.Univ.GUEPhase.RandomLayerB_Que_band     -- RandomLayerB:439 (band twin of `ba_QueG`)

#check @RBM.BA.BAfT                                 -- BA/RandomLayerBGBA:49

#check @RBM.BA.BAfE                                 -- RandomLayerBGBA:52

#check @RBM.BA.BAEd                                 -- RandomLayerBGBA:56

#check @RBM.BA.BAMO                                 -- RandomLayerBGBA:61

#check @RBM.BA.ba_dom_of_bulk                       -- RandomLayerBGBA:69

#check @RBM.BA.ba_Ed_of_im                          -- RandomLayerBGBA:87

#check @RBM.BA.ba_flowG                             -- RandomLayerBGBA:92 (`RBG_Flow` at BA)

#check @RBM.BA.ba_domG                              -- RandomLayerBGBA:103 (`RBG_Dom` at BA)

#check @RBM.BA.ba_mlout                             -- RandomLayerBGBA:115

#check @RBM.BA.RandomLayerBGBA_comp                 -- RandomLayerBGBA:126

-- C3 row a (T2515, merged 13b68cea `BA/GUEKPrim`)
#check @RBM.Univ.UNOUProfile.ba                     -- BA/GUEKPrim:77

#check @RBM.BA.baProfComp                           -- GUEKPrim:604

#check @RBM.BA.baOUProfRowk_holds                   -- GUEKPrim:584

#check @RBM.BA.baT0Cmp                              -- GUEKPrim:135 (UBA-C1 comparison)

#check @RBM.BA.kTwoGUEBA                            -- GUEKPrim:634

#check @RBM.BA.kTwoGUELoopBA                        -- GUEKPrim:639

#check @RBM.BA.kTwoGUEBA_self                       -- GUEKPrim:646

#check @RBM.BA.kTwoGUEBA_eq_ThetaTilde              -- GUEKPrim:659

#check @RBM.BA.hasDerivAt_kTwoGUELoopBA             -- GUEKPrim:776 (`hKd` of target 8)

#check @RBM.BA.gueK_existsBA                        -- GUEKPrim:1015 (the `Kt` of `BAKFam`; needs `0 < g`)

#check @RBM.BA.kTwoGUEBA_bridge                     -- GUEKPrim:1071

#check @RBM.BA.kTwoGUEBA_bridge_pm                  -- GUEKPrim:1101 (`t₀ K = P.pm` for `RBG_Que`)

#check @RBM.BA.kTwoGUEBA_bridge_pp                  -- GUEKPrim:1111

-- the band twins (census of the ticket)
#check @RBM.Univ.GUEPhase.GUEPathBounds             -- Universality/GUEPhase/Grid:89 (registry `Test/Axioms:383`, structural)

#check @RBM.Univ.GUEPhase.gueGridK                  -- Grid:106

#check @RBM.Univ.GUEPhase.gueH                      -- Grid:77 (BA: at `sz.withLam 0` inside `gueHBA` only)

#check @RBM.Univ.GUEPhase.Pgue                      -- Grid:61 (BA: at `sz.withLam 0`)

#check @RBM.Univ.GUEPhase.gueDev                    -- Proc:83 (reads `mE (E n) • 1`)

#check @RBM.Univ.GUEPhase.gueStop                   -- Proc:89

#check @RBM.Univ.GUEPhase.gueLmax                   -- Proc:93

#check @RBM.Univ.GUEPhase.gueDmax                   -- Proc:98

#check @RBM.Univ.GUEPhase.gueLproc                  -- Proc:112

#check @RBM.Univ.GUEPhase.gueDproc                  -- Proc:116

#check @RBM.Univ.GUEPhase.gueKproc                  -- Proc:122 (no band token; read by name)

#check @RBM.Univ.GUEPhase.norm_egtNGUE_le           -- Proc:596

#check @RBM.Univ.GUEPhase.gueDev_succ_le            -- Proc:771

#check @RBM.Univ.GUEPhase.gueKproc_detDom           -- ProcK:553

#check @RBM.Univ.GUEPhase.Hyp_Kt_detDom             -- HypA:690

#check @RBM.Univ.GUEPhase.Hyp_Kt_one                -- HypA:712

#check @RBM.Univ.GUEPhase.Hyp_Kt_disc               -- HypA:864

#check @RBM.Univ.GUEPhase.Hyp_grid                  -- HypA:981

#check @RBM.Univ.GUEPhase.map_gueH_eq_mixMat        -- EntryGrid:118

#check @RBM.Univ.GUEPhase.gueGrid_entry_bound       -- EntryGrid:518 (UN-43; owner of the BA twin: C5, T2515 Decision (5))

#check @RBM.Univ.GUEPhase.Duhamel_drift_remainder_ae  -- DuhamelA2:1008 (reads `condExp_loop_drift_gue`)

#check @RBM.Univ.GUEPhase.Duhamel_step_decomp       -- DuhamelB:739

#check @RBM.Univ.GUEPhase.gueGrid_loop_duhamel      -- DuhamelC:1485

#check @RBM.Univ.GUEPhase.HypB_entry_le             -- HypB:131 (`‖G - m‖_max`: BA `‖G - M‖_max`)

#check @RBM.Univ.GUEPhase.HypB_fixed                -- HypB:783

#check @RBM.Univ.GUEPhase.Bounds_path               -- BoundsA:503

#check @RBM.Univ.GUEPhase.BoundsACheck.pathBounds_of_forall_highProbAt  -- BoundsA:751

#check @RBM.Univ.GUEPhase.gueBds_h745E              -- PathBounds:330

#check @RBM.Univ.GUEPhase.gueBds_h746               -- PathBounds:433

#check @RBM.Univ.GUEPhase.gueGrid_pathBounds        -- PathBounds:550

#check @RBM.Univ.GUEPhase.oull_of_pathBounds        -- LLTransfer:443

#check @RBM.Univ.GUEPhase.gueGrid_eq729             -- Eq729B:622 (`h1` from `hP.lk 1` :663-690; Lemma 5.15 :676)

#check @RBM.Univ.GUEPhase.Eq729B_eq747_of_eq729     -- Eq729B:1077

#check @RBM.Univ.GUEPhase.Eq729B_derived            -- Eq729B:1125

#check @RBM.Univ.GUEPhase.Eq729B_eq747_of_inputs    -- Eq729B:1221

#check @RBM.Univ.GUEPhase.Eq729B_Concl              -- Eq729B:104

#check @RBM.Univ.GUEPhase.eq729_Kdisc               -- Eq729A:562 (target 8 instantiates it)

#check @RBM.Univ.GUEPhase.gue_highProb_incr_le      -- Markov:863 (read at `sz.withLam 0`)

#check @RBM.Univ.GUEPhase.gueK_exists               -- KPrim:749 (band twin of `gueK_existsBA`)

#check @RBM.Univ.GUEPhase.primRhsGUE                -- Bootstrap:178

-- the generic `Of` layer and the BA flow data (all merged; none is a V output)
#check @RBM.Gauss.ztOf                              -- Loop/GLoopFlow:55

#check @RBM.Gauss.etaOf                             -- GLoopFlow:58

#check @RBM.Gauss.Mres                              -- GLoopFlow:81 (`M = M^{(B)} ⊗ 1` of the local law)

#check @RBM.Univ.GUEPhase.mSigOf                    -- Universality/GUEPhase/Generator:62

#check @RBM.Univ.GUEPhase.genMatGUEOf               -- Generator:68

#check @RBM.Univ.GUEPhase.egtNGUEOf                 -- Generator:79

#check @RBM.Univ.GUEPhase.loopGenGUEOf              -- Generator:1168

#check @RBM.Gauss.PsiI                              -- Gauss/BlockAnderson:52

#check @RBM.Gauss.Sizes.withLam                     -- Defs/Sizes:182

#check @RBM.BA.BAm                                  -- BA/MFixedPoint:379

#check @RBM.BA.BAm_spec                             -- MFixedPoint:441

#check @RBM.BA.BAReal                               -- MFixedPoint:432

#check @RBM.BA.BAMB                                 -- MFixedPoint:190

#check @RBM.BA.BAMss                                -- MFixedPoint:511

#check @RBM.BA.BAMsigma                             -- MFixedPoint:507

#check @RBM.BA.BAzztE_data                          -- MFixedPoint:297 (`etaOf` identity of the flow point)

#check @RBM.BA.BAdom_real                           -- MFixedPoint:479

#check @RBM.BA.BAmF                                 -- BA/FlowPins:252

#check @RBM.BA.BAflowLam0                           -- FlowPins:386

#check @RBM.BA.BAFlow                               -- FlowPins:389

#check @RBM.BA.baFMz                                -- FlowPins:393

#check @RBM.BA.BAKsol                               -- FlowPins:283

#check @RBM.BA.baKsol_two                           -- BA/KInduct:88

#check @RBM.BA.BAKbound                             -- BA/KBound:196 (under `BAFlow`: coverage row 12)

#check @RBM.BA.baKbound_holds                       -- KBound:245

#check @RBM.BA.BAGamma                              -- BA/KCactus:488

#check @RBM.BA.STKboundgL                           -- Chain/Carrier:147 (registry `Test/Axioms:134`)

#check @RBM.BA.STLKgL                               -- Carrier:80

#check @RBM.BA.STLocalEntrygL                       -- Carrier:121

#check @RBM.BA.STExp2gL                             -- Carrier:127

#check @RBM.BA.baTheta_weighted_l1                  -- BA/GreenStab:251 (`‖K̃₂‖ ≤ 1`, target 8)

#check @RBM.BA.baM_row_l1                           -- GreenStab:116 (row `ℓ¹` of `M`, D1 (i))

#check @RBM.BA.BAm_norm_le_one                      -- BA/Ward:136

#check @RBM.Univ.ouP_ba_eq_band                     -- BA/UNPins:467

#check @RBM.Univ.ouMatC_ba_eq_band_add              -- UNPins:445

#check @RBM.Univ.UNMLOutBA                          -- UNPins:110 (instances: a hypothesis, no V name)

-- registry Props C5 contributes to (owner comments only)
#check @RBM.Univ.UNOULLk                            -- Universality/OUInterfaceK:69 (registry `Test/Axioms:168`)

#check @RBM.Univ.UNG1Rowk                           -- OUInterfaceK:101 (registry `Test/Axioms:169`)

#check @RBM.Univ.UNOUQUEk                           -- Universality/PinsK:326 (registry `Test/Axioms:387`)

#check @RBM.Univ.UNOUProfRowk                       -- OUInterfaceK:56 (registry `Test/Axioms:386`, untouched)

/-! ## Part 3: names of C4 a, C4 b, C3 b (merged) -/

-- C4 row a, merged ff7bd277: `BA/GUEOneLoop` (`gueHBA` :58, `gueHBA_succ` :72, `ol_gueHBA_eq` :85, `gueGrid_expect_oneLoopBA` :1196 = `T2517_OneLoopBA`)
#check @RBM.BA.gueHBA
#check @RBM.BA.gueHBA_succ
#check @RBM.BA.ol_gueHBA_eq
#check @RBM.BA.gueGrid_expect_oneLoopBA

-- C4 row b, merged 26561542: `BA/GUEEq729BA` (`oneStepEnvelopeGUEOf` :171, `condExp_loop_drift_gueBA` :488, `eq729FBA` :531, `eq729eBA` :538, `eq729_one_stepBA` :743)
#check @RBM.BA.oneStepEnvelopeGUEOf
#check @RBM.BA.condExp_loop_drift_gueBA
#check @RBM.BA.eq729FBA
#check @RBM.BA.eq729eBA
#check @RBM.BA.eq729_one_stepBA

-- C3 row b, merged fde07256: `BA/GUEEntry2` (`GUEEntry_llErr` :48, `GUEEntry_maxLoop` :55, `mixMatBA` :448, `GUEEntryMixBA` :738, `gueEntryMixBA` :785), `BA/GUEEntry` (`stable_mixBA` :68)
#check @RBM.BA.mixMatBA
#check @RBM.BA.GUEEntry_llErr
#check @RBM.BA.GUEEntryMixBA
#check @RBM.BA.gueEntryMixBA
#check @RBM.BA.stable_mixBA
