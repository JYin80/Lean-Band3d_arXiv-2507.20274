/-
Release check for T2337 (dispatcher V1, Thu Oct  8 13:50 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §149, §146 (supervisor 1048 C1, C2, Q2)).
BA-P5 (BA stage P, row 4 of 6): `RBM3D/BA/Prop5.lean`: properties 5 and 8 of `lem_propTH` for the block Anderson propagator,
mixed charges `σ₁ ≠ σ₂` (the old P7 merged here), by porting `Propagator/Prop5Hold.lean` with `kProd ↦ kBA`, `lgGam ↦ t g²`.
Section 1: merged names (`main` 8a62117).  Section 2: the two pins (the texts of `BAProp5`/`BAProp8`, `BA/FlowPins.lean:171/:215`,
with the extra hypothesis `σ₁ ≠ σ₂`; copied verbatim into `RBM.BA`) and the targets.  Statements and `#check` only.
Run from the main worktree: `lake env lean docs/tickets/checks/T2337-check.lean`.
-/
import RBM3D.BA.KHeatTail
import RBM3D.BA.FlowPins
import RBM3D.Propagator.Prop5Hold

/-! ## 1. Merged names -/

#check @RBM.BA.BAProp5                   -- BA/FlowPins.lean:171 (owed; all charges)
#check @RBM.BA.BAProp8                   -- BA/FlowPins.lean:215 (owed; all charges)
#check @RBM.BA.BATheta                   -- BA/MFixedPoint.lean:515
#check @RBM.BA.BATheta0                  -- BA/MFixedPoint.lean:519
#check @RBM.BA.BAMss_pm_eq               -- BA/KKernel.lean:84
#check @RBM.BA.BAMss_mp_eq               -- BA/KKernel.lean:93
#check @RBM.BA.BATheta_pm_eq             -- BA/KKernel.lean:107
#check @RBM.BA.kBA                       -- BA/KHeat.lean:54
#check @RBM.BA.BATheta_eq_laplace_kBA    -- BA/KHeat.lean:540 (Laplace identity, τ = t g² u)
#check @RBM.BA.kBA_basic                 -- BA/KHeat.lean:387
#check @RBM.BA.kBA_gap                   -- BA/KHeat.lean:989 (regime (ii), τ ≥ L²)
#check @RBM.BA.kBA_le                    -- BA/KHeatTail.lean:631 (regime (i), τ ≤ L²)
#check @RBM.prop5Decay_holds             -- Propagator/Prop5Hold.lean:784 (the band proof to port)
#check @RBM.prop8ZeroMode_holds          -- Propagator/Prop5Hold.lean:1266
#check @RBM.Heat.lg_bulk                 -- Propagator/LaplaceGauss.lean:692 (Θ-free)
#check @RBM.Heat.lg_zero                 -- Propagator/LaplaceGauss.lean:541
#check @RBM.Heat.lg_tail                 -- Propagator/LaplaceGauss.lean:295
#check @RBM.Heat.lg_convA                -- Propagator/LaplaceGauss.lean:206 (stated with `lgGam`; restate for `γ = t g²`)
#check @RBM.Heat.lg_convB                -- Propagator/LaplaceGauss.lean:163
#check @RBM.Heat.lg_convC                -- Propagator/LaplaceGauss.lean:182
#check @RBM.Bparam                       -- Defs/Params.lean:36
#check @RBM.ellT                         -- Defs/Params.lean:32

namespace RBM.BA.T2337Check

open RBM RBM.Gauss

/-! ## 2. The pins (copied verbatim into `RBM.BA`) and the targets -/

/-- **Property 5, mixed charges** (`BAProp5` with `σ₁ ≠ σ₂`). -/
def BAProp5mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ a : Zd d L,
          ‖BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- **Property 8, mixed charges** (`BAProp8` with `σ₁ ≠ σ₂`). -/
def BAProp8mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ a : Zd d L,
          ‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

def T2337_baProp5mixed_holds : Prop := ∀ (d : ℕ) (Λ κ : ℝ), BAProp5mixed d Λ κ
def T2337_baProp8mixed_holds : Prop := ∀ (d : ℕ) (Λ κ : ℝ), BAProp8mixed d Λ κ

example : Prop := T2337_baProp5mixed_holds

end RBM.BA.T2337Check
