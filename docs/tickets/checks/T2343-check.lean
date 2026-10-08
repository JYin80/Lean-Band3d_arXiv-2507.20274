/-
Release check for T2343 (dispatcher V1, Thu Oct 8 18:54 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §153, §145, §91 (1)).
UN-34 (+ UN-35, merged into one row, §153 (1)): `RBM3D/Universality/GUEPhase/Drift.lean`, port of RBM2D
`Universality/GUEPhase/Drift.lean` (2067 lines at RBM2D HEAD 9e0f275) with §1–§3 (jets, loop functional, their bounds)
**reused** from the merged `RBM3D/Path/OneStep.lean` §1–§4 (keyword `private` deleted there) instead of copied.
Section 1: merged names (exact namespaces; `main` 7154d50).  Section 2: the four target statements (renaming as T2330:
`d : Sizes` ↦ `sz : Sizes d`, `Idx (d.L n) (d.W n)` ↦ `Idx d (sz.L n) (sz.W n)`, `Z2` ↦ `Zd d`, `spectralZ` ↦ `zt`,
`gloop L W (blockMat M)` ↦ `loopL d L W (blockMat d L W M)`, `RBM.Endpoints.gueP L W` ↦ `gueP d L W`; the band twins
`RBM.Path.OneStepEnvelope`, `RBM.Path.pathH_succ`, `condExp_loop_step`, `condExp_loop_drift` fix the shapes).
Statements and `#check` only.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2343-check.lean`.
-/
import RBM3D.Path.LoopStep
import RBM3D.Universality.GUEPhase.Generator
import RBM3D.Universality.GUEPhase.Markov

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ RBM.Loop
open scoped NNReal ENNReal

/-! ## 1. Merged names -/

#check @RBM.Path.OneStepEnvelope              -- Path/OneStep.lean:85 (band twin of the first target)
#check @RBM.Path.oneStepEnvelope              -- Path/OneStep.lean:2205
#check @RBM.Path.envConst                     -- Path/OneStep.lean:78
#check @RBM.Path.pathH_succ                   -- Path/LoopStep.lean:48 (band twin)
#check @RBM.Path.condExp_loop_step            -- Path/LoopStep.lean:206 (band twin)
#check @RBM.Path.condExp_loop_drift           -- Path/LoopStep.lean:310 (band twin)
#check @RBM.Univ.GUEPhase.genMatGUE           -- GUEPhase/Generator.lean:89 (T2305)
#check @RBM.Univ.gueP                         -- Universality/Pins.lean:67
#check @RBM.Univ.gueVar                       -- Universality/Pins.lean:61
#check @RBM.Univ.GUEPhase.Pgue                -- GUEPhase/Grid.lean:61 (T2316)
#check @RBM.Univ.GUEPhase.gueH                -- GUEPhase/Grid.lean:77
#check @RBM.Univ.GUEPhase.gueUnit             -- GUEPhase/Grid.lean:52
#check @RBM.Univ.GUEPhase.gueCondExp_freeze   -- GUEPhase/Markov.lean:109
#check @RBM.Path.filt                         -- Path/Walk.lean:62
#check @RBM.Path.gridTime                     -- Path/Walk.lean:70
#check @RBM.Path.gridStep                     -- Path/Walk.lean:67
#check @RBM.Gauss.loopL                       -- Loop/GLoopFlow.lean:123
#check @RBM.Gauss.blockMat                    -- Loop/GLoopFlow.lean:105
#check @RBM.Gauss.Xmat                        -- Gauss/FineModel.lean:113
#check @RBM.Gauss.Sizes.seqXmat               -- Gauss/FineModel.lean:218
#check @RBM.zt                                -- Defs/Semicircle.lean:179

namespace RBM.Univ.GUEPhase.T2343Check

/-! ## 2. The targets (namespace `RBM.Univ.GUEPhase`, names without `T2343_`) -/

/-- `oneStepEnvelopeGUE`: `OneStepEnvelope` with `PF d L W g ↦ gueP d L W`, `genMat ↦ genMatGUE`, the band `envConst`. -/
def T2343_oneStepEnvelopeGUE : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), |E| < 2 → ∀ (I : Loop.LoopIdx (Zd d L)),
    I.WF → ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
      ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
        ‖(∫ ω', loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω'))
              (zt E (u + Δ)) I ∂(gueP d L W)) -
            loopL d L W (blockMat d L W M) (zt E u) I - (Δ : ℂ) * GUEPhase.genMatGUE d L W E u M I‖ ≤
          envConst d L W E I.length (u + Δ) * Δ ^ ((3 : ℝ) / 2)

/-- `gueH_succ`: the one-step recursion `H_{k+1} = H_k + √(Δ/N) X_{k+1}`. -/
def T2343_gueH_succ : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
    GUEPhase.gueH sz t1 t0 K n (k + 1) ω
      = GUEPhase.gueH sz t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ) • Sizes.seqXmat sz n (ω (k + 1))

/-- `condExp_loop_step_gue`: the conditional step given `filt sz k`, one GUE increment `√Δ X`, `X ~ gueP`. -/
def T2343_condExp_loop_step_gue : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ), |E| < 2 →
    ∀ {I : Loop.LoopIdx (Zd d (sz.L n))}, I.WF → gridTime t1 t0 K n (k + 1) < 1 →
    (GUEPhase.Pgue sz)[fun ω : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEPhase.gueH sz t1 t0 K n (k + 1) ω))
          (zt E (gridTime t1 t0 K n (k + 1))) I | filt sz k]
      =ᵐ[GUEPhase.Pgue sz] fun ω =>
        ∫ x, loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (GUEPhase.gueH sz t1 t0 K n k ω
            + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) x))
          (zt E (gridTime t1 t0 K n (k + 1))) I ∂(gueP d (sz.L n) (sz.W n))

/-- `condExp_loop_drift_gue`: the conditional drift along the GUE-phase grid, bounded by the envelope. -/
def T2343_condExp_loop_drift_gue : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ), |E| < 2 →
    ∀ {I : Loop.LoopIdx (Zd d (sz.L n))}, I.WF → 0 ≤ t1 n → t1 n ≤ t0 n → K n ≠ 0 → k < K n →
    gridTime t1 t0 K n (k + 1) < 1 →
    ∀ᵐ ω ∂(GUEPhase.Pgue sz),
      ‖(GUEPhase.Pgue sz)[fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEPhase.gueH sz t1 t0 K n (k + 1) ω'))
              (zt E (gridTime t1 t0 K n (k + 1))) I | filt sz k] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEPhase.gueH sz t1 t0 K n k ω))
              (zt E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * GUEPhase.genMatGUE d (sz.L n) (sz.W n) E (gridTime t1 t0 K n k)
              (GUEPhase.gueH sz t1 t0 K n k ω) I‖
        ≤ envConst d (sz.L n) (sz.W n) E I.length (gridTime t1 t0 K n (k + 1))
            * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)

end RBM.Univ.GUEPhase.T2343Check
