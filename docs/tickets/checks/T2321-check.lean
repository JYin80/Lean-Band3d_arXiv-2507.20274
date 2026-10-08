/-
Release check for T2321 (dispatcher V1, Thu Oct  8 03:15 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §133, §132, §68 (9), §80).
S3-26 (ST-3, Step 4 of `lem:main_ind`, `1_2:1370-1374`, proof `3_5:1602-1614`): `RBM3D/Induction/Step4.lean`,
`STStep4I`, `STStep4II` (the owed pins) and the primed assembly `ST_mainInd_of_pins'` that takes the Step-3 pins at
the consumed regimes (T2320) instead of `STStep3I`.
Section 1: merged names (exact namespaces; file:line on `main` 8f90d6d).
Section 2: the target statements as `Prop`s (T2321 proves them with these texts).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2321-check.lean`.
-/
import RBM3D.Induction.QtXiRoundLift
import RBM3D.Induction.QtNonzeroBoot
import RBM3D.Induction.IterationsA
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.MainIndRegimes

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- pins (`Induction/Step34Pins.lean`, `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.STStep4R          -- :261
#check @RBM.Gauss.Sizes.STStep4I          -- :279 (owed; target 1)
#check @RBM.Gauss.Sizes.STStep4II         -- :280 (owed; target 2)
#check @RBM.Gauss.Sizes.STStep3R          -- :250
#check @RBM.Gauss.Sizes.STStep3I          -- :277 (owed → superseded here, DECISIONS §133 (3))
#check @RBM.Gauss.Sizes.STStep3II         -- :278
#check @RBM.Gauss.Sizes.STLKU             -- :184 (the conclusion `(Eq:L-KGt-flow)`)
#check @RBM.Gauss.Sizes.STLmaxU           -- :176 (Step 3's conclusion, a hypothesis of `STStep4R`)
#check @RBM.Gauss.Sizes.STAvgU            -- :192
#check @RBM.Gauss.Sizes.STStep2Concl      -- :221
#check @RBM.Gauss.Sizes.STbootRHS         -- :402
#check @RBM.Gauss.Sizes.STlenL            -- :391
#check @RBM.Gauss.Sizes.STXiL             -- :63
#check @RBM.Gauss.Sizes.STXiLK            -- :68
#check @RBM.Gauss.Sizes.STPair            -- :48
#check @RBM.Gauss.Sizes.STCaseI           -- :237
#check @RBM.Gauss.Sizes.STCaseII          -- :241
#check @RBM.Gauss.Sizes.STIngR            -- :445
-- R2* bootstrap (`NQEndFlow.lean`; theorems in `RBM.Ind`)
#check @RBM.Gauss.Sizes.STXiBoot'         -- :95
#check @RBM.Ind.stOeqQt'_holds            -- QtXiRoundLift.lean:736 (T2314)
#check @RBM.Ind.stOeqQtNZ'_holds          -- QtNonzeroBoot.lean:1074 (T2304)
-- helpers (`IterationsA.lean`, `ScaleFacts3.lean`, `ScaleFacts.lean`; `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.st_prec_one_add_sup        -- IterationsA.lean:103
#check @RBM.Gauss.Sizes.st_prec_of_xi              -- :129
#check @RBM.Gauss.Sizes.iterationsA_avg_of_STAvgU  -- :1359 (k = 1)
#check @RBM.Gauss.Sizes.st_Bctl_ge                 -- ScaleFacts3.lean:56
#check @RBM.Gauss.Sizes.st_bootRHS_one             -- :97
#check @RBM.Gauss.Sizes.STBctl_pos                 -- ScaleFacts.lean:64
-- the setting (`Induction/Defs.lean`)
#check @RBM.Gauss.Sizes.STFlow            -- :286
#check @RBM.Gauss.Sizes.STflowE           -- :283
#check @RBM.Gauss.Sizes.STMainInd         -- :294
#check @RBM.Gauss.Sizes.STStep1           -- :349
#check @RBM.Gauss.Sizes.STStep2           -- Step2Defs.lean:599
-- the regimes and the assembly (T2245, `MainIndRegimes.lean`; `Step5Pins.lean`, `Step6Pins.lean`)
#check @RBM.Gauss.Sizes.STReg5I           -- Step5Pins.lean:44
#check @RBM.Gauss.Sizes.STReg5II          -- :48
#check @RBM.Gauss.Sizes.STReg5III         -- :58
#check @RBM.Gauss.Sizes.STReg5IV          -- :63
#check @RBM.Gauss.Sizes.STStep5I          -- :453
#check @RBM.Gauss.Sizes.STStep5II         -- :456
#check @RBM.Gauss.Sizes.STStep5III        -- :458
#check @RBM.Gauss.Sizes.STStep6I          -- Step6Pins.lean:131
#check @RBM.Gauss.Sizes.STStep6II         -- :134
#check @RBM.Gauss.Sizes.STStep6III        -- :137
#check @RBM.Gauss.Sizes.STMainIndR        -- MainIndRegimes.lean:64
#check @RBM.Gauss.Sizes.ST_mainIndR_of_steps      -- :165
#check @RBM.Gauss.Sizes.ST_mainIndR_III_of_steps  -- :217
#check @RBM.Gauss.Sizes.ST_mainIndR_I_of_steps    -- :222
#check @RBM.Gauss.Sizes.st_caseI_of_reg5III       -- :125
#check @RBM.Gauss.Sizes.st_caseI_of_reg5I         -- :137
#check @RBM.Gauss.Sizes.st_caseII_of_reg5II       -- :141
#check @RBM.Gauss.Sizes.st_caseII_of_reg5IV       -- :145
#check @RBM.Gauss.Sizes.ST_mainInd_of_regimes     -- :616
#check @RBM.Gauss.Sizes.ST_mainInd_of_pins        -- :674 (the unprimed consumer; kept)
#check @RBM.Gauss.Sizes.stStep5III_holds          -- PfStep5.lean:2473
#check @RBM.Gauss.Sizes.stStep5IV_holds           -- Step5Kit.lean:549
#check @RBM.Gauss.Sizes.stStep6IV_holds           -- ExpIntEasy.lean:626
#check @RBM.Green.stStep1_holds                   -- Green/GbEXP.lean:816

/-! ## 2. Target statements (T2321 proves them with these texts) -/

namespace RBM.Ind.T2321Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- Target 1: Step 4, case (i) (`3_5:1602-1613`, with `lem:STOeq_Qt`). -/
def T2321_stStep4I : Prop := ∀ d : ℕ, STStep4I d

/-- Target 2: Step 4, case (ii) (with `lem:STOeq_Qt_nonzero`). -/
def T2321_stStep4II : Prop := ∀ d : ℕ, STStep4II d

/-- Target 3: `lem:main_ind` from the step pins still owed, with Step 3 at the consumed regimes (T2320) in place of
`STStep3I`, and Step 4 proved here (primed successor of `ST_mainInd_of_pins`, `MainIndRegimes.lean:674`). -/
def T2321_mainInd_of_pins' : Prop :=
  ∀ d : ℕ, STStep2 d → STStep3R d STReg5III → STStep3R d STReg5I → STStep3II d →
    STStep5I d → STStep5II d → STStep6I d → STStep6II d → STStep6III d → STMainInd d

example : Prop := T2321_stStep4I ∧ T2321_stStep4II ∧ T2321_mainInd_of_pins'

end RBM.Ind.T2321Check
