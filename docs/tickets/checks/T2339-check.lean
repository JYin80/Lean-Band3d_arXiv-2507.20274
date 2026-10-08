/-
Release check for T2339 (dispatcher V1, Thu Oct  8 14:52 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §150, §145, §40).
S5-26 (ST-4, Step 5, case (ii), last row of ST-4): `RBM3D/Induction/DuhamelII.lean`, the pin `STDuhamelII` (owed) proved:
`Q^{(1)} = zeroModeSet {0}` for mixed signs, `Q = ∅` for equal signs.
Section 1: merged names (`main` dea6588).  Section 2: the target as a `Prop`.  `#check` and a `Prop` only.
Run: `lake env lean docs/tickets/checks/T2339-check.lean`.
-/
import RBM3D.Induction.DuhamelI
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.WardII
import RBM3D.Induction.IniTermII

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.STDuhamelII                       -- Step5Pins.lean:327 (owed; the target)
#check @RBM.Gauss.Sizes.STDuhamelConcl                    -- Step5Pins.lean:297
#check @RBM.Gauss.Sizes.STSigMixed                        -- Step5Pins.lean:312
#check @RBM.Gauss.Sizes.STSigSame                         -- Step5Pins.lean:311
#check @RBM.Gauss.Sizes.STReg5II                          -- Step5Pins.lean:48
#check @RBM.Gauss.Sizes.STReg5Mid                         -- Step5Pins.lean:54
#check @RBM.Gauss.Sizes.stDuhamelConcl_engine             -- DuhamelI.lean:1884 (Q = ∅, any sign class)
#check @RBM.Gauss.Sizes.stDuhamelI_holds                  -- DuhamelI.lean:1943
#check @RBM.Gauss.Sizes.duhamelI_Phi                      -- DuhamelI.lean:156 (public API)
#check @RBM.Gauss.Sizes.duhamelI_Phi_STprof               -- DuhamelI.lean:516
#check @RBM.Gauss.Sizes.duhamelI_Ugen_le                  -- DuhamelI.lean:594
#check @RBM.Gauss.Sizes.duhamelI_mart_Ugen                -- DuhamelI.lean:615
#check @RBM.ZeroModeCalc_zeroModeOp_tensorKer_comm        -- ZeroModeCalc.lean:263 (Q^{(1)} through the tensor kernel)
#check @RBM.norm_zeroModeSet_le                           -- ZeroModeCalc.lean:163
#check @RBM.zeroModeSet                                   -- Kernel/Evolution.lean:199
#check @RBM.Theta0                                        -- Propagator/Basic.lean:225
#check @RBM.prop8ZeroMode_holds                           -- Propagator/Prop5Hold.lean:1266 (prop:ThfadC0)
#check @RBM.Gauss.Sizes.stWardII_holds                    -- WardII.lean:269 ((zYU1))
#check @RBM.Gauss.Sizes.stIniTermII_holds                 -- IniTermII.lean:1718
#check @RBM.Gauss.Sizes.ST_step5_caseII_of_pins           -- Step5Cases.lean:542 (consumer)
#check @RBM.Gauss.Step5Inst.inst_duhamelII                -- Step5Pins.lean:975

/-! ## 2. Target statement -/

namespace RBM.Gauss.Sizes.T2339Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- `(zYU2)` (`3_5:2263-2277`), case (ii): `Q^{(1)}` for `σ₁ ≠ σ₂`, `Q = ∅` for `σ₁ = σ₂`. -/
def T2339_stDuhamelII_holds : Prop := ∀ d : ℕ, STDuhamelII d

example : Prop := T2339_stDuhamelII_holds

end RBM.Gauss.Sizes.T2339Check
