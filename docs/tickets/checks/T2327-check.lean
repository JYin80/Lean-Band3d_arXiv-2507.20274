/-
Release check for T2327 (dispatcher V1, Thu Oct  8 10:00 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §143, §54, §91 (1)).
UN-32 (bulk universality, GUE phase): `RBM3D/Universality/GUEPhase/Markov.lean`, port of RBM2D
`Universality/GUEPhase/Markov.lean` (912 lines): the `Pgue` freezing / conditional sub-Gaussianity toolkit.
Section 1: merged names (exact namespaces; `main` f38bffa).  Section 2: the definition `vGue` (copied verbatim) and the five
target statements (renaming of `GUEPhase/Grid.lean`, T2316: `d : Sizes` ↦ `sz : Sizes d`, `Idx (d.L n) (d.W n)` ↦
`Idx d (sz.L n) (sz.W n)`).  Statements, definitions and `#check` only.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2327-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Grid
import RBM3D.Path.Markov
import Mathlib.Probability.Moments.SubGaussian

/-! ## 1. Merged names -/

#check @RBM.Univ.GUEPhase.Pgue                      -- Grid.lean:61
#check @RBM.Univ.GUEPhase.gueUnit                   -- Grid.lean:52
#check @RBM.Univ.GUEPhase.gueUnitVar                -- Grid.lean:49
#check @RBM.Univ.GUEPhase.gueStepMeasure            -- Grid.lean:56
#check @RBM.Univ.GUEPhase.gueGridK                  -- Grid.lean:106
#check @RBM.Path.PathΩ                              -- Path/Walk.lean:54
#check @RBM.Path.filt                               -- Path/Walk.lean:62
#check @RBM.Path.linTr                              -- Path/Markov.lean:134
#check @RBM.Path.coordFinset                        -- Path/Markov.lean:139
#check @RBM.Path.linTr_seqXmat_eq_sum               -- Path/Markov.lean:224
#check @RBM.Gauss.LinearForm.linVar                 -- Gauss/LinearForm.lean:130
#check @RBM.Gauss.LinearForm.map_sum_const_mul_of_indep  -- :74
#check @RBM.Gauss.LinearForm.lintegral_indep_pair   -- :181
#check @RBM.Gauss.HighProbAt                        -- Defs/StochDomAt.lean:82
#check @RBM.Path.highProbAt_iInter                  -- Defs/StochDomAt.lean:279
#check @RBM.Gauss.Sizes.seqXmat                     -- Gauss/FineModel.lean:218
#check @RBM.Gauss.Sizes.SeqΩ                        -- Gauss/FineModel.lean:160
#check @RBM.Gauss.Sizes.SeqCoord                    -- Gauss/FineModel.lean:156
#check @RBM.Gauss.Xentry                            -- Gauss/FineModel.lean:105
#check @RBM.Gauss.measurable_Xentry                 -- Gauss/FineModel.lean:282

noncomputable section

namespace RBM.Univ.GUEPhase.T2327Check

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path RBM.Univ.GUEPhase
open scoped NNReal ENNReal MeasureTheory

variable {d : ℕ} (sz : Sizes d)

/-! ## 2. Definition (copied verbatim into `RBM.Univ.GUEPhase`) and target statements -/

/-- The variance of `y ↦ Re tr (A · seqXmat sz n y)` under `gueUnit sz` (RBM2D `Markov.lean:274`). -/
def vGue (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ≥0 :=
  linVar (gueUnitVar sz)
    (fun c => linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) (coordFinset n)

/-- `gueCondExp_freeze` (RBM2D `:92`). -/
def T2327_gueCondExp_freeze : Prop :=
  ∀ {β : Type} [MeasurableSpace β] [StandardBorelSpace β] (k : ℕ) {Y : PathΩ sz → β},
    Measurable[filt sz k] Y → ∀ {F : β → Sizes.SeqΩ sz → ℝ},
    Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2) →
    Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue sz) →
    (Pgue sz)[fun ω => F (Y ω) (ω (k + 1)) | filt sz k]
      =ᵐ[Pgue sz] fun ω => ∫ x, F (Y ω) x ∂(gueUnit sz)

/-- `gueHasCondSubgaussianMGF_of_frozen` (RBM2D `:167`). -/
def T2327_gueHasCondSubgaussianMGF_of_frozen : Prop :=
  ∀ {β : Type} [MeasurableSpace β] [StandardBorelSpace β] (k : ℕ) {Y : PathΩ sz → β},
    Measurable[filt sz k] Y → ∀ {F : β → Sizes.SeqΩ sz → ℝ},
    Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2) → ∀ {c : ℝ≥0},
    (∀ y, HasSubgaussianMGF (F y) c (gueUnit sz)) →
    HasCondSubgaussianMGF (filt sz k) ((filt sz).le k)
      (fun ω => F (Y ω) (ω (k + 1))) c (Pgue sz)

/-- `gueMap_lin_Xmat` (RBM2D `:281`). -/
def T2327_gueMap_lin_Xmat : Prop :=
  ∀ (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    (gueUnit sz).map (fun y => linTr n A (Sizes.seqXmat sz n y)) = gaussianReal 0 (vGue sz n A)

/-- `gueHasCondSubgaussianMGF_linear` (RBM2D `:598`). -/
def T2327_gueHasCondSubgaussianMGF_linear : Prop :=
  ∀ (n k : ℕ) (s : ℝ) {A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ},
    Measurable[filt sz k] A → ∀ (E : Set (PathΩ sz)), MeasurableSet[filt sz k] E → ∀ (c : ℝ≥0),
    (∀ ω ∈ E, s ^ 2 * (vGue sz n (A ω) : ℝ) ≤ c) →
    HasCondSubgaussianMGF (filt sz k) ((filt sz).le k)
      (fun ω => E.indicator (fun ω => s * linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))) ω)
      c (Pgue sz)

/-- `gue_highProb_incr_le` (RBM2D `:843`). -/
def T2327_gue_highProb_incr_le : Prop :=
  ∀ (n0 : ℕ), Tendsto (fun n => sz.size n) atTop atTop →
    HighProbAt (Pgue sz) sz.size (fun n => {ω | ∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n →
      ∀ i j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)})

example : Prop := T2327_gueCondExp_freeze sz ∧ T2327_gueHasCondSubgaussianMGF_of_frozen sz ∧
  T2327_gueMap_lin_Xmat sz ∧ T2327_gueHasCondSubgaussianMGF_linear sz ∧ T2327_gue_highProb_incr_le sz

end RBM.Univ.GUEPhase.T2327Check

end
