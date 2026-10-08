/-
Release check for T2334 (dispatcher V1, Thu Oct  8 12:52 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §148, §147 (C6), §84 (1)).
LW-14f (LW gate, last row of LW-14): `RBM3D/Graph/LWExpTerm6.lean`: the joined-graph bound `LwGraphPrecJoin`, the consumer
`lwExpG5'_of_expand'`, then unconditional `LWExpG5'`, `LWCutExp`, `LWtermEXP` and the Step 6 closures `STStep6I/II/III`.
**Compiles only after T2318 is merged** (imports `RBM3D.Graph.LWExpSound`, `LWG5Expand'`, `lwG5Expand'_holds`).
Section 1: merged names.  Section 2: `LwGraphPrecJoin` (T2265 check section 3 draft, `LWJoinedPin ↦ LWJoined`; copied
verbatim into `RBM.Gauss.Sizes`) and the targets.  Statements and `#check` only.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2334-check.lean`.
-/
import RBM3D.Graph.LWExpSound
import RBM3D.Graph.LWExpTerm4
import RBM3D.Induction.ExpIntIQ
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpDuhamel
import RBM3D.Induction.ExpIntII
import RBM3D.Induction.ExpWardII
import RBM3D.Induction.ExpIntEasy

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.LWG5Expand'              -- Graph/LWExpSound.lean:55 (T2318)
#check @RBM.Gauss.Sizes.lwG5Expand'_holds        -- Graph/LWExpSound.lean:1408 (T2318)
#check @RBM.Gauss.Sizes.LWJoined                 -- Graph/LWExpTerm5.lean:58
#check @RBM.Gauss.Sizes.LwGraphPrec1             -- Graph/LWExpTerm3.lean:1430 (the twin for distinct molecules)
#check @RBM.Gauss.Sizes.lwGraphPrec1             -- Graph/LWExpTerm3.lean:1442
#check @RBM.Gauss.Sizes.lwExpTerm3_T4pos         -- Graph/LWExpTerm3.lean:1859 (to copy)
#check @RBM.Gauss.Sizes.LwExpG5'OfExpand         -- Graph/LWExpTerm3.lean:2029
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand       -- Graph/LWExpTerm3.lean:2031 (to copy)
#check @RBM.Gauss.Sizes.LWExpG5'                 -- Graph/LWExpTerm2.lean:132 (owed)
#check @RBM.Gauss.Sizes.LWCutExp                 -- Graph/LWExpTerm.lean:52 (owed)
#check @RBM.Gauss.Sizes.LWtermEXP                -- Graph/LWPins.lean:311 (owed)
#check @RBM.Gauss.Sizes.lwCutExp_of_G5'          -- Graph/LWExpTerm4.lean:1717
#check @RBM.Gauss.Sizes.lwTermEXP_of_cut         -- Graph/LWExpTerm.lean:286
#check @RBM.Gauss.Sizes.STLocalEntry             -- Induction/Defs.lean:151
#check @RBM.Gauss.Sizes.STBctl_ge                -- Induction/ScaleFacts.lean:126
#check @RBM.Gauss.Sizes.STStep6I                 -- Induction/Step6Pins.lean:131 (owed)
#check @RBM.Gauss.Sizes.STStep6II                -- Induction/Step6Pins.lean:134 (owed)
#check @RBM.Gauss.Sizes.STStep6III               -- Induction/Step6Pins.lean:137 (owed)
#check @RBM.Gauss.Sizes.stStep6I_of_LW           -- Induction/ExpIntIQ.lean:1362
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins  -- Induction/Step6Kit.lean:865
#check @RBM.Gauss.Sizes.ST_step6_caseIII_of_pins -- Induction/Step6Kit.lean:737
#check @RBM.Gauss.Sizes.stExpLKLKHi_holds        -- Induction/ExpEtermsA.lean:607
#check @RBM.Gauss.Sizes.stImproveExpAver_holds   -- Induction/ExpAvg.lean:879
#check @RBM.Gauss.Sizes.stExpDuhamelZ_holds      -- Induction/ExpDuhamel.lean:385
#check @RBM.Gauss.Sizes.stExpIntII_holds         -- Induction/ExpIntII.lean:553
#check @RBM.Gauss.Sizes.stExpWardII_holds        -- Induction/ExpWardII.lean:419
#check @RBM.Gauss.Sizes.stExpIntIII_holds        -- Induction/ExpIntEasy.lean:610

noncomputable section

namespace RBM.Gauss.Sizes.T2334Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 2. The pin (copied verbatim into `RBM.Gauss.Sizes`) and the targets -/

/-- **`(Gammamuxy)` for a joined graph** (`q = 0`, one molecule containing both external vertices): the analogue of
`LwGraphPrec1` without `ξ` (pathwise: waved spanning tree, `W^{-d} ≤ (𝔡⁻² + 1) B` by `STBctl_ge`). -/
def LwGraphPrecJoin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t →
        ∀ P : PGraph (Fin 2), P.g.Normal → LWJoined P →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p _ => ‖∫ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![p.1, p.2] ∂(sz.seqP)‖)
            (fun n _ _ => (t n) ^ P.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
              (sz.Bctl n (t n)) ^ ((P.g.scalingOrder : ℝ) / 2))

def T2334_lwGraphPrecJoin_holds : Prop := ∀ d : ℕ, LwGraphPrecJoin d
def T2334_lwExpG5'_of_expand' : Prop := ∀ d : ℕ, LWG5Expand' d → LwGraphPrecJoin d → LWExpG5' d
def T2334_lwExpG5'_holds : Prop := ∀ d : ℕ, LWExpG5' d
def T2334_lwCutExp_holds : Prop := ∀ d : ℕ, LWCutExp d
def T2334_lwTermEXP_holds : Prop := ∀ d : ℕ, LWtermEXP d
def T2334_stStep6I_holds : Prop := ∀ d : ℕ, STStep6I d
def T2334_stStep6II_holds : Prop := ∀ d : ℕ, STStep6II d
def T2334_stStep6III_holds : Prop := ∀ d : ℕ, STStep6III d

example : Prop := T2334_lwTermEXP_holds

end RBM.Gauss.Sizes.T2334Check

end
