/-
Release check for T2333 (dispatcher V1, Thu Oct  8 11:52 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §147, §145, §40).
S5-15 (ST-4, Step 5, case (i)): `RBM3D/Induction/DuhamelI.lean`, the integrated hierarchy at `n = 2` conditional on the initial
term and on the three error terms: the pin `STDuhamelI` (owed) proved.
Section 1: merged names (exact namespaces; `main` 7b9fefe).  Section 2: the target statement as a `Prop`.
`#check` and a `Prop` only.  Never imported or merged.  Run: `lake env lean docs/tickets/checks/T2333-check.lean`.
-/
import RBM3D.Induction.EtermsMid
import RBM3D.Induction.Step5Kernel
import RBM3D.Induction.Step5Kit
import RBM3D.Path.DifREP3

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.STDuhamelI                     -- Step5Pins.lean:317 (owed; the target)
#check @RBM.Gauss.Sizes.STDuhamelConcl                 -- Step5Pins.lean:297
#check @RBM.Gauss.Sizes.STEtermsMidConcl               -- Step5Pins.lean:259 (hypothesis of the pin)
#check @RBM.Gauss.Sizes.stEtermsMid_of_LWT             -- EtermsMid.lean (T2328, S5-13)
#check @RBM.Gauss.Sizes.STIngR5                        -- Step5Pins.lean:82
#check @RBM.Gauss.Sizes.STReg5I                        -- Step5Pins.lean:44
#check @RBM.Gauss.Sizes.STSigAll                       -- Step5Pins.lean:313
#check @RBM.Gauss.Sizes.STIdx2P                        -- Step5Pins.lean:224
#check @RBM.Gauss.Sizes.STELKLK                        -- Step5Pins.lean:147
#check @RBM.Gauss.Sizes.STEGt                          -- Step2Defs.lean:312
#check @RBM.Gauss.Sizes.STEEk                          -- Step2Defs.lean:316
#check @RBM.Gauss.Sizes.STGridRepN                     -- Step2Defs.lean:854
#check @RBM.Gauss.Sizes.STGridRepNAt                   -- Step2Defs.lean:817 (last conjunct: the 𝒰-weighted martingale)
#check @RBM.Gauss.Sizes.STGridMartAt                   -- Step2Defs.lean:513
#check @RBM.Gauss.Sizes.STeeUM                         -- Step2Defs.lean:797
#check @RBM.Gauss.Sizes.STgAN                          -- Step2Defs.lean:777
#check @RBM.Gauss.Sizes.STgDriftN                      -- Step2Defs.lean:784
#check @RBM.Ind.stGridRepN_holds                       -- Path/DifREP3.lean:2381
#check @RBM.Ind.stGridMart_holds                       -- Path/DifREP2.lean:2283
#check @RBM.Ind.Ugen                                   -- GridDuhamelN.lean:65
#check @RBM.Ind.GridDuhamelN_Ugen_duhamel_telescope    -- GridDuhamelN.lean:161
#check @RBM.Ind.StoppedAzumaN                          -- GridDuhamelN.lean:531
#check @RBM.step5Kernel_UN_decompU                     -- Step5Kernel.lean:74 (eq:decompU)
#check @RBM.step5Kernel_profile_explicit_holds         -- Step5Kernel.lean:199 (uwp2-92kj)
#check @RBM.norm_Theta_le                              -- Propagator/Props4.lean:218
#check @RBM.Gauss.Sizes.ST_good_engine                 -- Step2Core.lean:997 (the Step-2 Duhamel/bootstrap engine)
#check @RBM.Gauss.Sizes.ST_good_prob                   -- Step2Events.lean:853 (grid → model transfer at Step 2)
#check @RBM.Gauss.Sizes.ST_step5_caseI_of_pins         -- Step5Kit.lean:292 (consumer)
#check @RBM.Gauss.Step5Inst.inst_duhamelI              -- Step5Pins.lean (instance pattern)

/-! ## 2. Target statement -/

namespace RBM.Gauss.Sizes.T2333Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- `(iois-mtx)`..`(iois-mtx2)` (`3_5:2046-2069`), case (i), all signs, no `Q`, uniformly in `u ∈ [s,t]`. -/
def T2333_stDuhamelI_holds : Prop := ∀ d : ℕ, STDuhamelI d

example : Prop := T2333_stDuhamelI_holds

end RBM.Gauss.Sizes.T2333Check
