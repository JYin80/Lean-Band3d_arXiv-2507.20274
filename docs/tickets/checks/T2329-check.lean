/-
Release check for T2329 (dispatcher V1, Thu Oct  8 10:17 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §145, §40).
S5-16 (ST-4, Step 5, case (i)): `RBM3D/Induction/IniTermI.lean`, the pin `STIniTermI` (owed) proved.
Section 1: merged names (exact namespaces; `main` e654e53).  Section 2: the target statement as a `Prop`.
`#check` and a `Prop` only.  Never imported or merged.  Run: `lake env lean docs/tickets/checks/T2329-check.lean`.
-/
import RBM3D.Induction.IniTermII
import RBM3D.Evolution.CltFar
import RBM3D.Induction.B45

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.STIniTermI                    -- Step5Pins.lean:322 (owed; the target)
#check @RBM.Gauss.Sizes.STIniTermConcl                -- Step5Pins.lean:280
#check @RBM.Gauss.Sizes.STIngR5                       -- Step5Pins.lean:82
#check @RBM.Gauss.Sizes.STReg5I                       -- Step5Pins.lean:44
#check @RBM.Gauss.Sizes.STSigAll                      -- Step5Pins.lean:313
#check @RBM.Gauss.Sizes.STIdx2P                       -- Step5Pins.lean:224
#check @RBM.Gauss.Sizes.STCltFar                      -- Step5Pins.lean:398
#check @RBM.Gauss.Sizes.STCltFarConcl                 -- Step5Pins.lean:387
#check @RBM.Gauss.Sizes.STfFar                        -- Step5Pins.lean:364
#check @RBM.Gauss.Sizes.stCltFar_holds                -- CltFar.lean:1757 (S5-25)
#check @RBM.Gauss.Sizes.STIniTermII                   -- Step5Pins.lean:333 (the twin, proved)
#check @RBM.Gauss.Sizes.stIniTermII_holds             -- IniTermII.lean:1718 (S5-27)
#check @RBM.Gauss.Sizes.iniTermII_core_same           -- IniTermII.lean:1378
#check @RBM.Gauss.Sizes.iniTermII_concl               -- IniTermII.lean:1664
#check @RBM.prop5Short_holds                          -- Prop5Short.lean:400 (prop:ThfadC_short)
#check @RBM.prop5Decay_holds                          -- Prop5Hold.lean:784 (prop:ThfadC)
#check @RBM.step5Kernel_UN_decompU                    -- Step5Kernel.lean:74 (eq:decompU)
#check @RBM.step5Kernel_profile_explicit_holds        -- Step5Kernel.lean:199 (uwp2-92kj)
#check @RBM.step5Kernel_theta_decay                   -- Step5Kernel.lean:135
#check @RBM.ekPropTInf_holds                          -- PropTInf.lean:534 (TTT2)
#check @RBM.Gauss.Sizes.B45_ward_fin                  -- B45.lean:200 (WI_calL, last label)
#check @RBM.Gauss.Sizes.B45_Lloop_eq                  -- B45.lean:189
#check @RBM.Gauss.Sizes.STLKtensor                    -- Step34Pins.lean:538
#check @RBM.Gauss.Sizes.STLKM                         -- Step2Defs.lean:68
#check @RBM.Gauss.Sizes.STAvgU                        -- Step34Pins.lean:192 (Gt_avgbound_flow)
#check @RBM.Gauss.Sizes.STStep2Concl                  -- Step34Pins.lean:221
#check @RBM.Gauss.Sizes.STDecay                       -- Defs.lean:121 (Eq:Gdecay+IND at s)
#check @RBM.Gauss.Sizes.STConStInd                    -- Defs.lean:168
#check @RBM.Gauss.Sizes.STBctl_mono                   -- ScaleFacts.lean:74
#check @RBM.Gauss.Sizes.st5_zeroModeSet_empty         -- Step5Kit.lean:96
#check @RBM.Gauss.Sizes.ST_step5_caseI_of_pins        -- Step5Kit.lean:292 (consumer)
#check @RBM.Gauss.Step5Inst.inst_iniTermI             -- Step5Pins.lean:617
#check @RBM.Ind.Ugen                                  -- GridDuhamelN.lean:65
#check @RBM.zeroModeSet                               -- Kernel/Evolution.lean:199
#check @RBM.Theta                                     -- Propagator/Basic.lean:70
#check @RBM.tailT                                     -- Defs/Tail.lean:48
#check @RBM.ellT                                      -- Defs/Params.lean:32

/-! ## 2. Target statement -/

namespace RBM.Gauss.Sizes.T2329Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- `(iksjuwjx0)` (`3_5:2072`), case (i), all signs, uniformly in `u ∈ [s,t]`. -/
def T2329_stIniTermI_holds : Prop := ∀ d : ℕ, STIniTermI d

example : Prop := T2329_stIniTermI_holds

end RBM.Gauss.Sizes.T2329Check
