/-
Release check for T2313 (dispatcher V1, Wed Oct  8 01:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §127).
Gate S3-18b2a (induction ST-3): primed successors in QEndGrid/QEndA/QEndB1, theorem `stOeqQtRoundPT''_holds`.
Section 1: merged names the proof uses, with exact namespaces.
Section 2: new constants (pins) in the temporary namespace `RBM.Gauss.Sizes.T2313Check`.
Section 3: public theorem shape.
Section 4: Prop-valued example.
Statements and `#check` only: no proof, no tactic block. Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2313-check.lean`.
-/
import RBM3D.Induction.QEndB1

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- T2302 (S3-18a2): `RBM3D/Induction/QEndGrid.lean`, namespace `RBM.Ind` (line 1326)
#check @RBM.Ind.altGridEndQN
-- T2294 (S3-18a1): `RBM3D/Induction/QEndA.lean`, namespace `RBM.Ind`
#check @RBM.Ind.gridDriftQN_envelope
-- T2310 (S3-18b1): `RBM3D/Induction/QEndB1.lean`, namespace `RBM.Gauss.Sizes` (line 84)
#check @RBM.Gauss.Sizes.STXiRoundPT'
-- T2310 (S3-18b1): `RBM3D/Induction/QEndB1.lean`, namespace `RBM.Gauss.Sizes` (line 101)
#check @RBM.Gauss.Sizes.STOeqQtRoundPT'
-- T2310 (S3-18b1): `RBM3D/Induction/QEndB1.lean`, namespace `RBM.Ind` (line 1187)
#check @RBM.Ind.stOeqQtRoundPT'_holds

noncomputable section

namespace RBM.Gauss.Sizes.T2313Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d)

/-! ## 2. New constants: primed-successor pins -/

/-- **Per-time round at n_ ≥ 2** (T2313 target): primed successor of `STXiRoundPT'`
    (T2310, QEndB1.lean:84) lowering the threshold from `3 ≤ n_` to `2 ≤ n_`.
    Uses `altGridEndQN'` (τ' = e₂/(40·d·(m+1))) via `gridDriftQN_envelope'`. -/
def STXiRoundPT''_pin (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
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

/-- `STXiRoundPT''` packed into the `STIngR` shape. -/
def STOeqQtRoundPT''_pin (d' : ℕ) : Prop :=
  STIngR d' STCaseI (fun sz' E s t => STXiRoundPT''_pin sz' E s t)

/-! ## 3. Public theorem shape -/

def stOeqQtRoundPT''_holds_pin : Prop := ∀ d', STOeqQtRoundPT''_pin d'

/-! ## 4. Prop-valued example -/

example : Prop := stOeqQtRoundPT''_holds_pin

end RBM.Gauss.Sizes.T2313Check

end
