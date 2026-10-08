/-
Release check for T2320 (dispatcher V1, Thu Oct  8 03:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §132, §68 (9), §80, §85).
S3-25 (ST-3, Step 3 of `lem:main_ind`, `1_2:1359-1366`, proof `3_5:1366-1601`): `RBM3D/Induction/Step3.lean`,
the Step-3 pins at the regimes the main-induction assembly consumes: `STStep3R d STReg5III` (`3_5:1384`, from `(lRB1)`),
`STStep3R d STReg5I` (`3_5:1407-1431`, `lem:iterations` case (i)) and `STStep3II d` (`3_5:1575-1595`, case (ii)).
Section 1: merged names (exact namespaces from the enclosing `namespace … end` blocks; file:line on `main` 8f90d6d).
Section 2: the target statements as `Prop`s (T2320 proves them with these texts).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2320-check.lean`.
-/
import RBM3D.Induction.QtXiRoundLift
import RBM3D.Induction.QtNonzeroBoot
import RBM3D.Induction.IterationsB
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.MainIndRegimes
import RBM3D.Loop.KLFinal

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- the pins (`Induction/Step34Pins.lean`, namespace `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.STStep3R          -- :250
#check @RBM.Gauss.Sizes.STStep3I          -- :277 (owed; not a target, DECISIONS §132 (2))
#check @RBM.Gauss.Sizes.STStep3II         -- :278 (owed; target 3)
#check @RBM.Gauss.Sizes.STLmaxU           -- :176
#check @RBM.Gauss.Sizes.STIterHyp         -- :469
#check @RBM.Gauss.Sizes.STPsi             -- :76
#check @RBM.Gauss.Sizes.STAI              -- :79
#check @RBM.Gauss.Sizes.STAII             -- :82
#check @RBM.Gauss.Sizes.STRegIterI        -- :493
#check @RBM.Gauss.Sizes.STCaseI           -- :237
#check @RBM.Gauss.Sizes.STCaseII          -- :241
#check @RBM.Gauss.Sizes.STIngR            -- :445
#check @RBM.Gauss.Sizes.STXiL             -- :63
#check @RBM.Gauss.Sizes.STXiLK            -- :68
#check @RBM.Gauss.Sizes.STPair            -- :48
#check @RBM.Gauss.Sizes.STStep2Concl      -- :221
#check @RBM.Gauss.Sizes.STKward           -- :229
-- `Induction/Defs.lean` (namespace `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.STStep1Loop       -- :234 (lRB1)
#check @RBM.Gauss.Sizes.STConStInd        -- :168
#check @RBM.Gauss.Sizes.STKbound          -- :174
#check @RBM.Gauss.Sizes.STLK              -- :104
#check @RBM.Gauss.Sizes.STFlow            -- :286
#check @RBM.Gauss.Sizes.STflowE           -- :283
#check @RBM.Gauss.Sizes.STKloop           -- :64
#check @RBM.lemT                          -- Defs/Semicircle.lean:193
#check @RBM.Gauss.Sizes.Lloop             -- Loop/GLoopFlow.lean:158
#check @RBM.Path.TimeIcc                  -- Defs/StochDomAt.lean:100
-- the regimes (`Induction/Step5Pins.lean`, `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.STReg5I           -- :44
#check @RBM.Gauss.Sizes.STReg5III         -- :58
-- R2* bootstrap inputs (`NQEndFlow.lean`, `RBM.Gauss.Sizes`; theorems in `RBM.Ind`)
#check @RBM.Gauss.Sizes.STXiBoot'         -- NQEndFlow.lean:95
#check @RBM.Gauss.Sizes.STOeqQt'          -- :127
#check @RBM.Gauss.Sizes.STOeqQtNZ'        -- :130
#check @RBM.Gauss.Sizes.STIterations'     -- :149
#check @RBM.Gauss.Sizes.STIterationsII'   -- :152
#check @RBM.Ind.stOeqQt'_holds            -- QtXiRoundLift.lean:736 (T2314, c8e166a)
#check @RBM.Ind.stOeqQtNZ'_holds          -- QtNonzeroBoot.lean:1074 (T2304)
-- `lem:iterations` (T2087 S3-24a, T2259 S3-24b; namespace `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.stIterations'_holds     -- IterationsB.lean:570
#check @RBM.Gauss.Sizes.stIterationsII'_holds   -- IterationsB.lean:581
#check @RBM.Gauss.Sizes.iterationsB_step        -- IterationsB.lean:454
#check @RBM.Gauss.Sizes.iterationsA_apriori_of_lRB1  -- IterationsA.lean:1385 (sef8w483r324)
#check @RBM.Gauss.Sizes.iterationsA_rela_of_K        -- :1454 (rela_XILXILK)
#check @RBM.Gauss.Sizes.iterationsA_avg_of_STAvgU    -- :1359 (k = 1)
#check @RBM.Gauss.Sizes.iterationsA_scale_I          -- :1631
#check @RBM.Gauss.Sizes.iterationsA_scale_II         -- :1704
#check @RBM.Gauss.Sizes.st_prec_of_xi                -- :129
#check @RBM.Gauss.Sizes.st_one_le_XiL                -- :151
#check @RBM.Gauss.Sizes.st_one_le_XiLK               -- :160
-- the deterministic scale facts (T2058 S3-23, `ScaleFacts3.lean`, `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.st_iterate        -- :106
#check @RBM.Gauss.Sizes.st_kmin           -- :126
#check @RBM.Gauss.Sizes.st_hscale_I'      -- :303
#check @RBM.Gauss.Sizes.st_hscale_II'     -- :310
#check @RBM.Gauss.Sizes.st_hBA_I          -- :323
#check @RBM.Gauss.Sizes.st_hBA_II         -- :380
#check @RBM.Gauss.Sizes.st_conStInd_sub   -- :478
-- `Bctl` facts (`ScaleFacts.lean`, `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.STBctl_pos        -- :64
#check @RBM.Gauss.Sizes.STBctl_mono       -- :74
#check @RBM.Gauss.Sizes.STBctl_xmono      -- :93
#check @RBM.Gauss.Sizes.Bctl              -- Defs/Sizes.lean:214
-- consumer and the regime monotonicity (T2245, `MainIndRegimes.lean`; `Step5Kit.lean`)
#check @RBM.Gauss.Sizes.ST_mainIndR_of_steps  -- MainIndRegimes.lean:165
#check @RBM.Gauss.Sizes.st_caseI_of_reg5III   -- :125
#check @RBM.Gauss.Sizes.st_caseI_of_reg5I     -- :137
#check @RBM.Gauss.Sizes.st5_conStInd_mono     -- Step5Kit.lean:101
#check @RBM.Gauss.Sizes.stKbound_of_flow      -- Loop/KLFinal.lean:302
#check @RBM.Gauss.Sizes.stKward_of_flow       -- Loop/KLFinal.lean:308

/-! ## 2. Target statements (T2320 proves them with these texts) -/

namespace RBM.Ind.T2320Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- Target 1: Step 3 at regime (iii) `ilambda² ≤ 1 - t` (`3_5:1384`: `(Eq:LGxb)` from `(lRB1)`). -/
def T2320_stStep3RegIII : Prop := ∀ d : ℕ, STStep3R d STReg5III

/-- Target 2: Step 3 at regime (i) `ilambda²/L² ≤ 1 - t`, `1 - s ≤ ilambda²` (`3_5:1407-1431`, `lem:iterations`). -/
def T2320_stStep3RegI : Prop := ∀ d : ℕ, STStep3R d STReg5I

/-- Target 3: Step 3, case (ii) `1 - s ≤ ilambda²/L²` (`3_5:1575-1595`). -/
def T2320_stStep3II : Prop := ∀ d : ℕ, STStep3II d

example : Prop := T2320_stStep3RegIII ∧ T2320_stStep3RegI ∧ T2320_stStep3II

end RBM.Ind.T2320Check
