/-
Release check for T2338 (dispatcher V1, Thu Oct  8 13:50 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §149, §68 (7), §12).
ST-D6 (ST-6 design, report only): from `lem:main_ind` (`STMainInd`, one induction step `s → t` under `(con_st_ind)`) to the
outputs consumed by UN and MA (`UNMLOut`: `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` at every time sequence `t ≤ lemT z`), the
base case `t = 0` (`G_0 = M`, `𝓛 = 𝒦`), the finite chain of times, and the route-G (carrier-generic) form for BA.
Section 1: merged names (`main` 8a62117).  Section 2: the candidate target as a `Prop` (the design confirms or corrects it).
`#check` and a `Prop` only.  Never imported or merged.  Run: `lake env lean docs/tickets/checks/T2338-check.lean`.
-/
import RBM3D.Induction.Step4
import RBM3D.Universality.Pins
import RBM3D.BA.FlowPins
import RBM3D.Main.FixedZ
import RBM3D.BA.UNPins

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.STMainInd               -- Induction/Defs.lean:294 (the one-step induction)
#check @RBM.Gauss.Sizes.ST_mainInd_of_pins'     -- Induction/Step4.lean:209 (`STMainInd` from the step pins still owed)
#check @RBM.Gauss.Sizes.ST_mainInd_of_regimes   -- Induction/MainIndRegimes.lean:616
#check @RBM.Gauss.Sizes.ST_mainIndR_of_steps    -- Induction/MainIndRegimes.lean:165
#check @RBM.Gauss.Sizes.STMainIndR              -- Induction/MainIndRegimes.lean:64
#check @RBM.Gauss.Sizes.STRegChain              -- Induction/MainIndRegimes.lean:453
#check @RBM.Gauss.Sizes.STLK                    -- Induction/Defs.lean:104
#check @RBM.Gauss.Sizes.STLmax                  -- Induction/Defs.lean:112
#check @RBM.Gauss.Sizes.STDecay                 -- Induction/Defs.lean:121
#check @RBM.Gauss.Sizes.STDecayStrong           -- Induction/Defs.lean:134
#check @RBM.Gauss.Sizes.STLocalMax              -- Induction/Defs.lean:144
#check @RBM.Gauss.Sizes.STLocalEntry            -- Induction/Defs.lean:151
#check @RBM.Gauss.Sizes.STExp2                  -- Induction/Defs.lean:159
#check @RBM.Gauss.Sizes.STConStInd              -- Induction/Defs.lean:168
#check @RBM.Gauss.Sizes.STFlow                  -- Induction/Defs.lean:287
#check @RBM.lemT                                -- Defs/Semicircle.lean:193
#check @RBM.Univ.UNMLOut                        -- Universality/Pins.lean:432 (owed; consumer UN, MA)
#check @RBM.Univ.UNMLOutBA                      -- BA/UNPins.lean:110 (owed; BA twin, owner BA-V3)
#check @RBM.BA.STMainIndG                       -- BA/FlowPins.lean:565 (carrier-generic `lem:main_ind`)
#check @RBM.Endpoints.MAFixed                   -- Main/FixedZ.lean:73 (MA consumer of `UNMLOut`)

/-! ## 2. Candidate target -/

namespace RBM.Gauss.Sizes.T2338Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- The ST-6 assembly in its simplest form: `lem:main_ind` gives the flow outputs at every time sequence. -/
def T2338_mlOut_of_mainInd : Prop := ∀ d : ℕ, STMainInd d → RBM.Univ.UNMLOut d

example : Prop := T2338_mlOut_of_mainInd

end RBM.Gauss.Sizes.T2338Check
