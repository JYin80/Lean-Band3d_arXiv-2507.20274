/-
Release check for T2344 (dispatcher V1, Thu Oct 8 19:55 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §154, §147, §123, §126).
LW-13b-2: `lem:LW_moment_exp` (`LWMomentExp`, `7_8:78-83`, proof `7_8:1600-1791`) from the merged LW-02
(`lwMoment_holds`, T2297), LW-13b-1 (`lwMomExp_valOnD_eq_valOn`, T2312), the near bound (`lwMomExp_near`, T2281),
the far bound (`lwMomExpFar_and`, T2289) and the engine (`lw_localregularX`, T2332).
Section 1: merged names (`main` 1546ef7).  Section 2: the target as a `Prop`.  `#check` and a `Prop` only.
Run: `lake env lean docs/tickets/checks/T2344-check.lean`.
-/
import RBM3D.Graph.LWMoment
import RBM3D.Graph.LWMomExp
import RBM3D.Graph.LWMomExpD
import RBM3D.Graph.LWMomExpFar
import RBM3D.Graph.LWEngine

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.LWMomentExp           -- Graph/LWPins.lean:341 (owed; the target)
#check @RBM.Gauss.Sizes.LWMoment              -- Graph/LWPins.lean:325
#check @RBM.Gauss.Sizes.lwMoment_holds        -- Graph/LWMoment.lean:1785 (T2297)
#check @RBM.Gauss.Sizes.lwMoment_prec_far     -- Graph/LWMoment.lean:1303 (the far-pair expansion of LW-02)
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral -- Graph/LWExpTerm.lean:143 (the `≺ → 𝔼` upgrade)
#check @RBM.Gauss.Sizes.LWf                   -- Graph/LWPins.lean:199
#check @RBM.Gauss.Sizes.LWAssmExp             -- Graph/LWPins.lean:283
#check @RBM.Gauss.Sizes.LWLoopExp             -- Graph/LWPins.lean:274 (`zdistInf`)
#check @RBM.Gauss.Sizes.LWPhiB_psiAll         -- Graph/LWPsi.lean:417 (B class, as T2342)
#check @RBM.tailT_regime1_bounds              -- Graph/LWPsi.lean:459
#check @RBM.tailW_regime1_bounds              -- Graph/LWPsi.lean:475
#check @RBM.sfT                               -- Kernel/PropT.lean:469
#check @RBM.EKTTk                             -- Evolution/Pins.lean:156
#check @RBM.Graph.lw_localregularX            -- Graph/LWEngine.lean:771 (T2332)
#check @RBM.Graph.lwMomExp_valOnD             -- Graph/LWMomExp.lean:526
#check @RBM.Graph.lwMomExp_valOnD_eq_valOn    -- Graph/LWMomExpD.lean:18 (T2312)
#check @RBM.Graph.AnpDetNearAt                -- Graph/LWMomExp.lean:900 (`zdistD` edges)
#check @RBM.Graph.lwMomExp_near               -- Graph/LWMomExp.lean:1023 (T2281)
#check @RBM.Graph.AnpFarAndAt                 -- Graph/LWMomExpFar.lean:80 (`zdistInf` edges, "and" domain)
#check @RBM.Graph.lwMomExpFar_and             -- Graph/LWMomExpFar.lean:338 (T2289)

namespace RBM.Gauss.Sizes.T2344Check

/-! ## 2. The target -/

/-- LW-13b-2: `lem:LW_moment_exp` for every `d`. -/
def T2344_lwMomentExp_holds : Prop := ∀ d : ℕ, LWMomentExp d

end RBM.Gauss.Sizes.T2344Check
