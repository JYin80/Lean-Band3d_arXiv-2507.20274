/-
Release check for T2310 (dispatcher V1, Wed Oct  7 08:xx UTC 2026; CLAUDE.md §4 step 0; DECISIONS §116).
Gate S3-18b1: `RBM3D/Induction/QEndB1.lean` (new file), proving
  `stOeqQtRoundPT'_holds : ∀ d, STOeqQtRoundPT' d` (per-time alternating round endpoint;
  assembled to `STXiBoot'` by S3-18b2; closes ST-3 at 46/46).
Section 1: merged names the proofs use, with exact namespaces.
Section 2: the two new pin definitions (verbatim from T2310.md §1, redesigned per DECISIONS §120)
  in the temporary namespace `RBM.Gauss.Sizes.T2310Check`; T2310 defines them in `RBM.Gauss.Sizes`
  / `RBM.Ind` (QEndB1.lean).
Section 3: the public theorem shape as a `_pin : Prop`.
Section 4: Prop-valued example.
Statements and `#check` only: no proof, no tactic block. Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2310-check.lean`.
-/
import RBM3D.Induction.QEndGrid
import RBM3D.Induction.QEndA
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.QLevelsA
import RBM3D.Induction.NQLin
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.NQBudget
import RBM3D.Loop.KLFinal

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Merged names -/

-- QEndGrid (T2302, `RBM3D/Induction/QEndGrid.lean`), namespace `RBM.Ind` (`:53`)
#check @RBM.Ind.altGridEndQN
-- QEndA (T2294, `RBM3D/Induction/QEndA.lean`), namespace `RBM.Ind` (`:46`)
#check @RBM.Ind.altYGridN
-- QLevelsA (`RBM3D/Induction/QLevelsA.lean`), namespace `RBM.Ind` (`:42`)
#check @RBM.Ind.startLevelQN
-- NQEndFlow (`RBM3D/Induction/NQEndFlow.lean`), namespace `RBM.Gauss.Sizes` (`:68`)
#check @RBM.Gauss.Sizes.STOeqQt'
#check @RBM.Gauss.Sizes.STXiBoot'
-- NQLin (`RBM3D/Induction/NQLin.lean`), namespace `RBM.Gauss.Sizes` (`:54`)
#check @RBM.Gauss.Sizes.NQLinGood
-- GridGoodN (`RBM3D/Induction/GridGoodN.lean`), namespace `RBM.Gauss.Sizes` (`:51`)
#check @RBM.Gauss.Sizes.STmaxLM
-- Step34Pins (transitively imported), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STOeqNQ
-- StochDomAt (transitively imported), namespace `RBM.Gauss.Sizes`
#check @RBM.Path.perTimeDomAt_iff_forall_section
-- KLFinal (`RBM3D/Loop/KLFinal.lean`), namespace `RBM.Loop` (`:49`)
#check @RBM.Loop.KLbound_holds

noncomputable section

namespace RBM.Gauss.Sizes.T2310Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d)

/-! ## 2. New pin definitions (verbatim from T2310.md §1) -/

/-- Per-time round: `STXiRound'` with `Prec` ↦ `PrecPT` in the conclusion and `3 ≤ n_`.
    Target of `stOeqQtRoundPT'_holds`; assembled to `STXiBoot'`/`STOeqQt'` by S3-18b2
    via `stXiBootR_of_round` (QtNonzeroBoot.lean:581). -/
def STXiRoundPT' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 3 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2)
          (sz.Bctl n (s n)) n_ p)

/-- Per-time round ingredient: `STXiRoundPT'` packed into the `STIngR` shape. -/
def STOeqQtRoundPT' (d : ℕ) : Prop :=
  STIngR d STCaseI (fun sz E s t => STXiRoundPT' sz E s t)

/-! ## 3. Public theorem shape -/

/-- `stOeqQtRoundPT'_holds` — closes ST-3 at 46/46 (after S3-18b2 assembly). -/
def stOeqQtRoundPT'_holds_pin : Prop := ∀ d : ℕ, STOeqQtRoundPT' d

/-! ## 4. Statement shape -/

example : Prop := stOeqQtRoundPT'_holds_pin

end RBM.Gauss.Sizes.T2310Check

end
