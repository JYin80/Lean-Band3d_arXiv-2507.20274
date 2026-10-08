/-
Release check for T2341 (dispatcher V1, Thu Oct 8 18:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §152, §146, §144).
BA-P6 (BA stage P, row 5 of 6): the unit first and second differences of `Θ_BA` for mixed charges `σ₁ ≠ σ₂`
(twin of `Propagator/PropUnit.lean`), from the P4c bounds (T2336) by a polynomial-decay Laplace lemma
(supervisor `docs/supervisor/2026-10-08-1048.md` Q3, C4).
Section 1: merged names (`main` 7154d50).  Section 2: the two pins, verbatim.  Section 3: the targets as `Prop`s.
Run: `lake env lean docs/tickets/checks/T2341-check.lean`.
-/
import RBM3D.BA.KHeatDiff
import RBM3D.BA.Prop5
import RBM3D.Propagator.PropUnit

/-! ## 1. Merged names -/

#check @RBM.BA.kBA_diff1_le              -- BA/KHeatDiff.lean:1573 (T2336; `τ ≤ L²`, `M = ⌊d/2⌋+1`, `max τ 1`)
#check @RBM.BA.kBA_diff2_le              -- BA/KHeatDiff.lean:1599
#check @RBM.BA.kBA_gap                   -- BA/KHeat.lean:989 (regime (ii), unit differences included)
#check @RBM.BA.kBA_le                    -- BA/KHeatTail.lean:631
#check @RBM.BA.kBA_basic                 -- BA/KHeat.lean:387
#check @RBM.BA.BATheta_eq_laplace_kBA    -- BA/KHeat.lean:540
#check @RBM.BA.BAReal                    -- BA/MFixedPoint.lean:432
#check @RBM.BA.BATheta                   -- BA/MFixedPoint.lean:515
#check @RBM.BA.BAProp5mixed              -- BA/Prop5.lean:56 (T2337)
#check @RBM.BA.baProp5mixed_holds        -- BA/Prop5.lean:928
#check @RBM.BA.BAProp6                   -- BA/FlowPins.lean:192 (owed; P8)
#check @RBM.BA.BAProp7                   -- BA/FlowPins.lean:203 (owed; P8)
#check @RBM.PropUnit1                    -- Propagator/PropUnit.lean:39 (the band twin)
#check @RBM.PropUnit2
#check @RBM.propUnit1_holds              -- Propagator/PropUnit.lean:747
#check @RBM.propUnit2_holds              -- Propagator/PropUnit.lean:826
#check @RBM.Heat.lg_tail                 -- Propagator/LaplaceGauss.lean:295
#check @RBM.Heat.lg_zero                 -- Propagator/LaplaceGauss.lean:541
#check @RBM.Heat.lg_bulk                 -- Propagator/LaplaceGauss.lean:692 (exponential; the new lemma is its polynomial twin)

namespace RBM.BA.T2341Check

open RBM RBM.Gauss RBM.Heat

/-! ## 2. The pins (namespace `RBM.BA` in the ticket, names without `T2341_`) -/

/-- **Unit pin 1, mixed charges**: `|Θ_t(0, a + e_j) − Θ_t(0, a)| ≤ C (g² + |1−t|)⁻¹ (|a| + 1)^{-(d−1)}`, `σ₁ ≠ σ₂`. -/
def T2341_BAPropUnit1mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ (a : Zd d L) (j : Fin d),
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single j 1) - BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Unit pin 2, mixed charges**: unit second differences (`i ≠ j` and `i = j`), `(|a| + 1)^{-d}`, `σ₁ ≠ σ₂`. -/
def T2341_BAPropUnit2mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ (a : Zd d L) (i j : Fin d),
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single i 1 + Pi.single j 1)
              - BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single i 1)
              - BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single j 1) + BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-! ## 3. The targets -/

def T2341_baPropUnit1mixed_holds : Prop := ∀ (d : ℕ) (Λ κ : ℝ), T2341_BAPropUnit1mixed d Λ κ
def T2341_baPropUnit2mixed_holds : Prop := ∀ (d : ℕ) (Λ κ : ℝ), T2341_BAPropUnit2mixed d Λ κ

end RBM.BA.T2341Check
