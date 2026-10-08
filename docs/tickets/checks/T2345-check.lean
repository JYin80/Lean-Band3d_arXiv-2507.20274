/-
Release check for T2345 (dispatcher V1, Thu Oct 8 20:54 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §155, §145, §91 (1)).
UN-36: `RBM3D/Universality/GUEPhase/DuhamelA1.lean`, port of RBM2D `Universality/GUEPhase/DuhamelA.lean` §1–§4
(lines 1–1040 at RBM2D HEAD 9e0f275): the unit-GUE variance bound, the Ward bound of the quadratic variation, the
conditional variance of the linear part, crude and shift bounds on `loopMax`.  Section 1: merged names (`main` after T2343).
Section 2: three target statements (renaming as T2330/T2343; the one `d`-line `card (Vtx d L W) = (L W)^d`).
Run (after T2343 is merged): `lake env lean docs/tickets/checks/T2345-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Drift
import RBM3D.Path.StepDecomp
import RBM3D.Induction.Split
import RBM3D.Induction.LoopC2N

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path RBM.Univ RBM.Loop
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. Merged names -/

#check @RBM.Univ.GUEPhase.oneStepEnvelopeGUE     -- GUEPhase/Drift.lean (T2343)
#check @RBM.Univ.GUEPhase.condExp_loop_drift_gue  -- GUEPhase/Drift.lean (T2343)
#check @RBM.Univ.GUEPhase.gueH_succ               -- GUEPhase/Drift.lean (T2343)
#check @RBM.Univ.GUEPhase.vGue                    -- GUEPhase/Markov.lean:291
#check @RBM.Univ.GUEPhase.gueUnitVar              -- GUEPhase/Grid.lean:49
#check @RBM.Univ.GUEPhase.gueH                    -- GUEPhase/Grid.lean:77
#check @RBM.Univ.GUEPhase.Pgue                    -- GUEPhase/Grid.lean:61
#check @RBM.Path.linTr                            -- Path/Markov.lean:134
#check @RBM.Path.gradMat                          -- Path/StepDecomp.lean:80
#check @RBM.Path.fderiv_eq_trace_gradMat          -- Path/StepDecomp.lean:123
#check @RBM.Path.HermTestFun                      -- Path/StepDecomp.lean:186
#check @RBM.Ind.loopMax                           -- Induction/Split.lean:515
#check @RBM.Ind.loopMax_le                        -- Induction/Split.lean:533
#check @RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero -- Induction/ConArgDet.lean:380
#check @RBM.green_sub_green                       -- Induction/ConArgDet.lean:73
#check @RBM.green                                 -- Green/EntryCore.lean:34
#check @RBM.Gauss.loopL                           -- Loop/GLoopFlow.lean:123
#check @RBM.Gauss.blockMat                        -- Loop/GLoopFlow.lean:105
#check @RBM.Gauss.gloopProd                       -- Loop/GLoopFlow.lean:384
#check @RBM.Gauss.Gres                            -- Loop/GLoopFlow.lean:74
#check @RBM.Gauss.Eblk                            -- Loop/GLoop.lean:55
#check @RBM.Gauss.Vtx                             -- Gauss/Model.lean:60
#check @RBM.Gauss.coordinateMatrix                -- Gauss/FineModel.lean:384
#check @RBM.Gauss.Sizes.seqXmat                   -- Gauss/FineModel.lean:218
#check @RBM.Gauss.Sizes.seqHflow                  -- Gauss/FineModel.lean:225
#check @RBM.Gauss.LinearForm.linVar               -- Gauss/LinearForm.lean:130

namespace RBM.Univ.GUEPhase.T2345Check

/-! ## 2. Targets (namespace `RBM.Univ.GUEPhase`, names without `T2345_`) -/

/-- `vGue A ≤ 8 ‖A‖_F²`. -/
def T2345_Duhamel_vGue_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    (GUEPhase.vGue sz n A : ℝ) ≤ 8 * ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- `L^{(m)} ≤ (L W)^d |Im z|^{-m}` (the `d`-line: `card (Vtx d L W) = (L W)^d`). -/
def T2345_Duhamel_loopMax_le_crude : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}, M.IsHermitian →
    ∀ {z : ℂ}, z.im ≠ 0 → ∀ m : ℕ,
      RBM.Ind.loopMax d L W M z m ≤ ((L : ℝ) * (W : ℝ)) ^ d * (|z.im|⁻¹) ^ m

/-- `max(vGue(∇Φ), vGue(-i∇Φ)) ≤ 8 n² |Im z|⁻² L^{(2n)}`, `Φ M = 𝓛(blockMat M, z, I)`, `n = |I|`. -/
def T2345_Duhamel_vGue_gradMat_le : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ}, z.im ≠ 0 → ∀ {I : Loop.LoopIdx (Zd d (sz.L n))}, I.WF →
    ∀ {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}, M.IsHermitian →
      max (GUEPhase.vGue sz n (gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z I) M) : ℝ)
          (GUEPhase.vGue sz n (-Complex.I • gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z I) M) : ℝ)
        ≤ 8 * ((I.length : ℝ) ^ 2 * (|z.im|⁻¹) ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z (2 * I.length))

end RBM.Univ.GUEPhase.T2345Check
