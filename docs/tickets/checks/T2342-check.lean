/-
Release check for T2342 (dispatcher V1, Thu Oct 8 18:50 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §152, §147, §145).
LW-16: `lem: EWGn2_N` in the regime `1 - t ≤ ĝ²/L²` (`LWtermExpN`) from `lem:LWterm` (`LWterm`), applied to the
merged B class `LWPhiB` (c₀ = d, K = ⌊ℓ⌋ ∧ L), compared with `tailW` in the regime (supervisor 0838 O3, answered in §152 (3)).
Section 1: merged names (`main` 7154d50).  Section 2: the target as a `Prop`.  `#check` and a `Prop` only.
Run: `lake env lean docs/tickets/checks/T2342-check.lean`.
-/
import RBM3D.Graph.LWPins

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.LWtermExpN            -- Graph/LWPins.lean:462 (owed; LW-16 proves it from `LWterm`)
#check @RBM.Gauss.Sizes.LWterm                -- Graph/LWPins.lean:240 (owed; LW-01)
#check @RBM.Gauss.Sizes.LWtermB               -- Graph/LWPins.lean:255 (owed; the B class "in particular")
#check @RBM.Gauss.Sizes.LWAssm                -- Graph/LWPins.lean:234
#check @RBM.Gauss.Sizes.LWAssmExp             -- Graph/LWPins.lean:283
#check @RBM.Gauss.Sizes.LWLoopExp             -- Graph/LWPins.lean:274
#check @RBM.Gauss.Sizes.LWLoop2               -- Graph/LWPins.lean:228
#check @RBM.Gauss.Sizes.LWE                   -- Graph/LWPins.lean:218
#check @RBM.Gauss.Sizes.Prec                  -- Defs/StochDomAt.lean:121
#check @RBM.Gauss.Sizes.LWPhiB_psiAll         -- Graph/LWPsi.lean:417 (`(eq:Psi)` for the B class, T2051)
#check @RBM.Gauss.Sizes.LWClass_B             -- Graph/LWPsi.lean:366
#check @RBM.Gauss.Sizes.LWPhiB_psiRel          -- Graph/LWPsi.lean:220
#check @RBM.Gauss.Sizes.LWWindow_max_Bctl     -- Graph/LWPsi.lean:344
#check @RBM.tailT_regime2_bounds              -- Graph/LWPsi.lean:500 (`e⁻¹ B ≤ 𝒯 ≤ B` for `r ≤ L` in the regime)
#check @RBM.tailW_regime2_bounds              -- Graph/LWPsi.lean:514
#check @RBM.ellT_eq_of_le                     -- Defs/Tail.lean:143
#check @RBM.exp_tail_ge                       -- Defs/Tail.lean:158
#check @RBM.BparamR_natCast                   -- Defs/Tail.lean:57
#check @RBM.Gauss.etaT                        -- Loop/GLoop.lean:75

namespace RBM.Gauss.Sizes.T2342Check

/-! ## 2. The target -/

/-- LW-16: the second regime of `lem: EWGn2_N` from `lem:LWterm`. -/
def T2342_lwtermExpN_of_LWterm : Prop := ∀ d : ℕ, LWterm d → LWtermExpN d

end RBM.Gauss.Sizes.T2342Check
