/-
Release check for T2328 (dispatcher V1, Thu Oct  8 10:17 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §145, §40).
S5-13 (ST-4, Step 5): `RBM3D/Induction/EtermsMid.lean`, `STEtermsMid` from the LW pin `STLWT`.
Section 1: merged names (exact namespaces; `main` e654e53).  Section 2: the target statement as a `Prop`.
`#check` and a `Prop` only.  Never imported or merged.  Run: `lake env lean docs/tickets/checks/T2328-check.lean`.
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.EMn2Exp2
import RBM3D.Induction.Step2K2
import RBM3D.Induction.NewKLKL

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.STEtermsMid            -- Step5Pins.lean:275 (owed; the target)
#check @RBM.Gauss.Sizes.STEtermsMidConcl       -- Step5Pins.lean:259
#check @RBM.Gauss.Sizes.STIngR5                -- Step5Pins.lean:82
#check @RBM.Gauss.Sizes.STReg5Mid              -- Step5Pins.lean:54
#check @RBM.Gauss.Sizes.STIdx2                 -- Step5Pins.lean:139
#check @RBM.Gauss.Sizes.STNewKLKL              -- Step5Pins.lean:247
#check @RBM.Gauss.Sizes.STNewKLKLAt            -- Step5Pins.lean:235
#check @RBM.Gauss.Sizes.stNewKLKL_holds        -- NewKLKL.lean:836 (S5-12)
#check @RBM.Gauss.Sizes.STLWT                  -- Step2Defs.lean:421 (owed, LW gate)
#check @RBM.Gauss.Sizes.STLWT_of_LWtermExp     -- Step2Events.lean:1427
#check @RBM.Gauss.Sizes.STEMn2Exp              -- Step2Defs.lean:456
#check @RBM.Gauss.Sizes.stEMn2Exp_holds        -- EMn2Exp2.lean:1090
#check @RBM.Gauss.Sizes.STK2decay              -- Step2Defs.lean:568
#check @RBM.Gauss.Sizes.stK2decay_holds        -- Step2K2.lean:132
#check @RBM.Gauss.Sizes.STGdecayW              -- Step34Pins.lean:208
#check @RBM.Gauss.Sizes.STLocalEntryU          -- Step34Pins.lean:199
#check @RBM.Gauss.Sizes.STAvgU                 -- Step34Pins.lean:192
#check @RBM.Gauss.Sizes.STELKLK                -- Step5Pins.lean:147
#check @RBM.Gauss.Sizes.STELKLKM               -- Step2Defs.lean:110
#check @RBM.Gauss.Sizes.STEGt                  -- Step2Defs.lean:312
#check @RBM.Gauss.Sizes.STEEk                  -- Step2Defs.lean:316
#check @RBM.Gauss.Sizes.STJhatM                -- Step2Defs.lean:81
#check @RBM.Gauss.Sizes.STGMM                  -- Step2Defs.lean:146
#check @RBM.Gauss.Sizes.STprof                 -- Step2Defs.lean:75
#check @RBM.Gauss.Sizes.STAI                   -- Step34Pins.lean:79
#check @RBM.Gauss.Sizes.ST_selfImprove_section -- Step2Iterate.lean:284 (the Step-2 twin)

/-! ## 2. Target statement -/

namespace RBM.Gauss.Sizes.T2328Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- `(S5WG+M000)`, `(S5WG+M)` (`3_5:1961-1979`) from the LW pin `STLWT` (owed, LW gate). -/
def T2328_stEtermsMid_of_LWT : Prop := ∀ d : ℕ, STLWT d → STEtermsMid d

example : Prop := T2328_stEtermsMid_of_LWT

end RBM.Gauss.Sizes.T2328Check
