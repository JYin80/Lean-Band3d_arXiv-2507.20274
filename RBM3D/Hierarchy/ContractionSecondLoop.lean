/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Hierarchy.ContractionBasic
import RBM3D.Gauss.LoopCoordinate

/-!
# The second-derivative contraction of loops (S1-04)

Ticket T2065.  Port of the thirteen files `RBM2D/Hierarchy/Contraction{SecondLoop,
SecondLoopSameEdge, SecondLoopSameEdgeWord, SecondLoopSameEdgeCut, EdgeSplits, PairSplits,
FirstDerivativePositionSum, SecondDerivativePositionSum, SecondDerivativeTraceSum,
PositionLoopBridge, SameEdgePositionCut, PairPositionCut, SecondLoopAllCuts}.lean` at commit
`c9a24cf`, with the renaming rules of `docs/tickets/ST1-COMMON.md` item 2: `Z2 L` becomes
`Zd d L`, `BlockIndex L W` becomes `Vtx d L W`, `Coord`, `gvar` become `CoordF`, `gvarF`, `Gsig`
becomes `Gres`, `gloop` becomes `loopL`, and the contraction coefficient `W^2` becomes `W^d`.

Everything is a finite-matrix identity at a fixed sample `(u, ω, z)`: no probability, no
expectation, no estimate.  The combinatorial lists `edgeSplits`, `pairSplits` are
dimension-free.  The coefficient `W^d` is the one of `sum_allCoords_trace_blocks`
(`W^d · (W^{-d})² = W^{-d}`).  `RBM2D/Hierarchy/ContractionSecondLoopReverse.lean` (imported by
the first RBM2D file but not among the thirteen) has no consumer and is not ported.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace RBM.Gauss

open Matrix

/-! ## 1. A two-edge cross term in the second loop derivative
(`ContractionSecondLoop`) -/

section Sec1

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

private theorem trace_blockRelabel (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix.trace (blockRelabel d L W M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, blockRelabel]
  exact (Equiv.sum_comp (splitEquiv d L W).symm (fun i => M i i))

private theorem blockRelabel_mul
    (M N : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockRelabel d L W (M * N) =
      blockRelabel d L W M * blockRelabel d L W N := by
  exact (Matrix.submatrix_mul_equiv M N
    (splitEquiv d L W).symm (splitEquiv d L W).symm (splitEquiv d L W).symm).symm

private theorem trace_coordinateBlock_pair
    (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (γ : CoordF d L W) :
    Matrix.trace (A * coordinateBlock d L W γ * C *
      coordinateBlock d L W γ) =
    Matrix.trace (A.submatrix (split d L W) (split d L W) *
      coordinateMatrix d L W γ * C.submatrix (split d L W) (split d L W) *
      coordinateMatrix d L W γ) := by
  let P := A.submatrix (split d L W) (split d L W)
  let Q := C.submatrix (split d L W) (split d L W)
  have hA : blockRelabel d L W P = A := blockRelabel_submatrix_split d L W A
  have hC : blockRelabel d L W Q = C := blockRelabel_submatrix_split d L W C
  change Matrix.trace (A * blockRelabel d L W (coordinateMatrix d L W γ) *
    C * blockRelabel d L W (coordinateMatrix d L W γ)) =
    Matrix.trace (P * coordinateMatrix d L W γ * Q * coordinateMatrix d L W γ)
  rw [← hA, ← hC, ← blockRelabel_mul d L W,
    ← blockRelabel_mul d L W, ← blockRelabel_mul d L W]
  exact trace_blockRelabel d L W _

omit [NeZero W] in
/-- The ordered mixed term obtained by differentiating two distinct Green
factors once is the cut-chain trace, before covariance summation.
`RBM2D/Hierarchy/ContractionSecondLoop.lean:53`. -/
theorem trace_twoEdge_mixed_eq_cutChains
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (B : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    let Gs := Gres H z s
    let Gt := Gres H z t
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let M := gloopProd d L W H z ⟨σ₂, a₂⟩
    let T := gloopProd d L W H z ⟨σ₃, a₃⟩
    Matrix.trace (P * (Gs * B * Gs * Eblk d L W a) * M *
      (Gt * B * Gt * Eblk d L W c) * T) =
    Matrix.trace (cutLeftChain d L W H z σ₁ σ₃ a₁ a₃ s t c * B *
      cutRightChain d L W H z σ₂ a₂ s t a * B) := by
  let P := gloopProd d L W H z ⟨σ₁, a₁⟩
  let M := gloopProd d L W H z ⟨σ₂, a₂⟩
  let T := gloopProd d L W H z ⟨σ₃, a₃⟩
  let Gs := Gres H z s
  let Gt := Gres H z t
  let Ea := Eblk d L W a
  let Ec := Eblk d L W c
  simpa only [cutLeftChain, cutRightChain, Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (P * Gs * B * Gs * Ea * M * Gt * B) (Gt * Ec * T))

/-- Covariance summation of one ordered, unscaled two-edge cross term.
`RBM2D/Hierarchy/ContractionSecondLoop.lean:78`. -/
theorem sum_twoEdge_mixed_cutChains
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (cutLeftChain d L W H z σ₁ σ₃ a₁ a₃ s t c *
          coordinateBlock d L W γ *
          cutRightChain d L W H z σ₂ a₂ s t a *
          coordinateBlock d L W γ)) =
    (W : ℂ) ^ d * ∑ u : Zd d L, ∑ v : Zd d L,
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) u) *
        SB d L g u v *
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) v) := by
  simp_rw [trace_coordinateBlock_pair d L W]
  exact sum_coordinate_cutChains d L W g H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂

omit [NeZero W] in
private theorem trace_two_smul (u : ℝ) (hu : 0 ≤ u)
    (A B C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (A * (Real.sqrt u • B) * C * (Real.sqrt u • B)) =
      (u : ℂ) * Matrix.trace (A * B * C * B) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_smul]
  rw [Real.mul_self_sqrt hu]
  rfl

private theorem trace_twoEdge_deriv_signs
    (u : ℝ) (ω : Ω d L W) (γ : CoordF d L W) (z : ℂ)
    (P M T : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (s t : Bool) (a c : Zd d L) :
    let H := HflowBlock d L W u ω
    let B := Real.sqrt u • coordinateBlock d L W γ
    Matrix.trace (P * (gsigCoordinateDeriv d L W u ω γ z s * Eblk d L W a) * M *
      (gsigCoordinateDeriv d L W u ω γ z t * Eblk d L W c) * T) =
    Matrix.trace (P * (Gres H z s * B * Gres H z s * Eblk d L W a) * M *
      (Gres H z t * B * Gres H z t * Eblk d L W c) * T) := by
  simp only [gsigCoordinateDeriv, neg_mul, mul_neg, neg_neg]

/-- One ordered cross term in the finite second product rule, after the
Gaussian coordinate weights are summed. The other ordering and terms where
both derivatives hit one edge are separate. `RBM2D/Hierarchy/ContractionSecondLoop.lean:126`. -/
theorem sum_twoEdge_mixed_coordinate
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock d L W u ω
    let Gs := Gres H z s
    let Gt := Gres H z t
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let M := gloopProd d L W H z ⟨σ₂, a₂⟩
    let T := gloopProd d L W H z ⟨σ₃, a₃⟩
    (∑ γ : CoordF d L W,
      let B := Real.sqrt u • coordinateBlock d L W γ
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (P * (Gs * B * Gs * Eblk d L W a) * M *
          (Gt * B * Gt * Eblk d L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SB d L g p q *
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
  dsimp only
  simp_rw [trace_twoEdge_mixed_eq_cutChains d L W]
  simp_rw [trace_two_smul d L W u hu]
  calc
    _ = (u : ℂ) * ∑ γ : CoordF d L W,
          (((gvarF d L W g γ : ℝ) : ℂ) *
            Matrix.trace (cutLeftChain d L W (HflowBlock d L W u ω) z
              σ₁ σ₃ a₁ a₃ s t c * coordinateBlock d L W γ *
              cutRightChain d L W (HflowBlock d L W u ω) z
                σ₂ a₂ s t a * coordinateBlock d L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [sum_twoEdge_mixed_cutChains d L W g (HflowBlock d L W u ω) z
        σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂]
      ring

/-- The same contraction written with the two actual first derivatives of
the signed Green factors in `coordinateSecondWordDeriv`.
`RBM2D/Hierarchy/ContractionSecondLoop.lean:172`. -/
theorem sum_twoEdge_mixed_deriv
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock d L W u ω
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let M := gloopProd d L W H z ⟨σ₂, a₂⟩
    let T := gloopProd d L W H z ⟨σ₃, a₃⟩
    (∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (P *
          (gsigCoordinateDeriv d L W u ω γ z s * Eblk d L W a) * M *
          (gsigCoordinateDeriv d L W u ω γ z t * Eblk d L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SB d L g p q *
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
  dsimp only
  simp_rw [trace_twoEdge_deriv_signs d L W u ω]
  exact sum_twoEdge_mixed_coordinate d L W g u hu ω z
    σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂

end Sec1

/-! ## 2. A single-edge term of the second loop derivative
(`ContractionSecondLoopSameEdge`) -/

section Sec2

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- Coordinate contraction in block notation, with the physical-site
Gaussian covariance and its exact `W^d` normalization.
`RBM2D/Hierarchy/ContractionSecondLoopSameEdge.lean:52`. -/
theorem sum_coordinateBlock_trace_pair
    (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (A * coordinateBlock d L W γ * C *
          coordinateBlock d L W γ)) =
    (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
      Matrix.trace (A * Eblk d L W p) * SB d L g p q *
        Matrix.trace (C * Eblk d L W q) := by
  simp_rw [trace_coordinateBlock_pair d L W]
  rw [sum_allCoords_trace_blocks]
  rw [blockRelabel_submatrix_split, blockRelabel_submatrix_split]

/-- One actual second Green derivative produces a twice-weighted same-edge
`A B C B` contraction. The trace rotation puts the fixed block projector
inside `A = G Eₐ G`. `RBM2D/Hierarchy/ContractionSecondLoopSameEdge.lean:77`. -/
theorem trace_gsigCoordinateSecondDeriv_Eblk
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (s : Bool) (a : Zd d L) :
    let G := Gres (HflowBlock d L W u ω) z s
    Matrix.trace (gsigCoordinateSecondDeriv d L W u ω γ z s * Eblk d L W a) =
      (2 : ℂ) * (u : ℂ) *
        Matrix.trace ((G * Eblk d L W a * G) * coordinateBlock d L W γ * G *
          coordinateBlock d L W γ) := by
  let G := Gres (HflowBlock d L W u ω) z s
  let E := Eblk d L W a
  let D := coordinateBlock d L W γ
  let B := Real.sqrt u • D
  have hcyc : Matrix.trace (G * B * G * B * G * E) =
      Matrix.trace ((G * E * G) * B * G * B) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (G * B * G * B) (G * E)
  change Matrix.trace (((2 : ℝ) • (G * B * G * B * G)) * E) =
    (2 : ℂ) * (u : ℂ) * Matrix.trace ((G * E * G) * D * G * D)
  rw [smul_mul_assoc, Matrix.trace_smul, hcyc, trace_two_smul d L W u hu]
  simp only [two_smul, two_mul]
  ring

/-- Gaussian variance contraction of the actual second derivative at one
Green edge. The first trace contains the two-edge loop `G Eₐ G Eₚ`, and the
second trace is the one-edge loop `G E_q`.
`RBM2D/Hierarchy/ContractionSecondLoopSameEdge.lean:101`. -/
theorem sum_gsigCoordinateSecondDeriv_Eblk
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W)
    (z : ℂ) (s : Bool) (a : Zd d L) :
    let G := Gres (HflowBlock d L W u ω) z s
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (gsigCoordinateSecondDeriv d L W u ω γ z s * Eblk d L W a)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ∑ p : Zd d L, ∑ q : Zd d L,
        Matrix.trace ((G * Eblk d L W a * G) * Eblk d L W p) * SB d L g p q *
          Matrix.trace (G * Eblk d L W q) := by
  dsimp only
  simp_rw [trace_gsigCoordinateSecondDeriv_Eblk d L W u hu ω]
  calc
    _ = ((2 : ℂ) * (u : ℂ)) * ∑ γ : CoordF d L W,
          (((gvarF d L W g γ : ℝ) : ℂ) *
            Matrix.trace ((Gres (HflowBlock d L W u ω) z s * Eblk d L W a *
              Gres (HflowBlock d L W u ω) z s) *
              coordinateBlock d L W γ *
              Gres (HflowBlock d L W u ω) z s *
              coordinateBlock d L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [sum_coordinateBlock_trace_pair d L W g]
      ring

end Sec2

/-! ## 3. A same-edge second derivative inside a finite matrix word
(`ContractionSecondLoopSameEdgeWord`) -/

section Sec3

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- A single second Green derivative at an arbitrary edge of a matrix word.
The surrounding prefix and suffix remain explicit matrices.
`RBM2D/Hierarchy/ContractionSecondLoopSameEdgeWord.lean:29`. -/
theorem trace_gsigCoordinateSecondDeriv_word
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (s : Bool) (a : Zd d L)
    (P T : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    let G := Gres (HflowBlock d L W u ω) z s
    Matrix.trace (P * (gsigCoordinateSecondDeriv d L W u ω γ z s * Eblk d L W a) * T) =
      (2 : ℂ) * (u : ℂ) *
        Matrix.trace (((G * Eblk d L W a * T * P) * G) *
          coordinateBlock d L W γ * G * coordinateBlock d L W γ) := by
  let G := Gres (HflowBlock d L W u ω) z s
  let E := Eblk d L W a
  let D := coordinateBlock d L W γ
  let B := Real.sqrt u • D
  have hcyc : Matrix.trace (P * ((G * B * G * B * G) * E) * T) =
      Matrix.trace (((G * E * T * P) * G) * B * G * B) := by
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm (P * G * B * G * B) (G * E * T)
  change Matrix.trace (P * (((2 : ℝ) • (G * B * G * B * G)) * E) * T) =
    (2 : ℂ) * (u : ℂ) * Matrix.trace (((G * E * T * P) * G) * D * G * D)
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, Matrix.trace_smul, hcyc,
    trace_two_smul d L W u hu]
  simp only [two_smul, two_mul]
  ring

/-- The weighted same-edge term at one chosen position of a finite word.
The covariance is exactly `SB d L g p q`, with the surrounding word absorbed
into the first block trace. `RBM2D/Hierarchy/ContractionSecondLoopSameEdgeWord.lean:56`. -/
theorem sum_gsigCoordinateSecondDeriv_word
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W)
    (z : ℂ) (s : Bool) (a : Zd d L)
    (P T : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    let G := Gres (HflowBlock d L W u ω) z s
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (P * (gsigCoordinateSecondDeriv d L W u ω γ z s *
          Eblk d L W a) * T)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ∑ p : Zd d L, ∑ q : Zd d L,
        Matrix.trace ((((G * Eblk d L W a * T * P) * G) * Eblk d L W p)) *
          SB d L g p q * Matrix.trace (G * Eblk d L W q) := by
  dsimp only
  simp_rw [trace_gsigCoordinateSecondDeriv_word d L W u hu ω]
  calc
    _ = ((2 : ℂ) * (u : ℂ)) * ∑ γ : CoordF d L W,
          (((gvarF d L W g γ : ℝ) : ℂ) *
            Matrix.trace (((Gres (HflowBlock d L W u ω) z s * Eblk d L W a *
              T * P) * Gres (HflowBlock d L W u ω) z s) *
              coordinateBlock d L W γ *
              Gres (HflowBlock d L W u ω) z s *
              coordinateBlock d L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [sum_coordinateBlock_trace_pair d L W g]
      ring

end Sec3

/-! ## 4. A same-edge contraction at a specified edge of a finite loop
(`ContractionSecondLoopSameEdgeCut`) -/

section Sec4

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

section Sec4Aux

variable {d L W} {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}

omit [NeZero W] in
/-- The merged `gloopProd_cons` is private (`RBM3D/Loop/GLoopFlow.lean:394`); `rfl`.
`RBM2D/Hierarchy/Loops.lean:102`. -/
private theorem secondLoop_gloopProd_cons (s : Bool) (b : Zd d L)
    (σ : List Bool) (a : List (Zd d L)) :
    gloopProd d L W H z ⟨s :: σ, b :: a⟩ =
      Gres H z s * Eblk d L W b * gloopProd d L W H z ⟨σ, a⟩ := rfl

omit [NeZero W] in
/-- `loopL` is the trace of `gloopProd` (by `rfl`).  `RBM2D/Hierarchy/Loops.lean:92` (`gloop`). -/
private theorem secondLoop_loopL_eq (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W H z I = Matrix.trace (gloopProd d L W H z I) := rfl

omit [NeZero W] in
private theorem secondLoop_gloopProd_nil : gloopProd d L W H z ⟨[], []⟩ = 1 := rfl

omit [NeZero W] in
/-- The merged `gloopProd_append` is private (`RBM3D/Loop/GLoopFlow.lean:401`).
`RBM2D/Hierarchy/Loops.lean:117`. -/
private theorem secondLoop_gloopProd_append {σ₁ : List Bool} {a₁ : List (Zd d L)}
    (h₁ : σ₁.length = a₁.length)
    (σ₂ : List Bool) (a₂ : List (Zd d L)) :
    gloopProd d L W H z ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩ =
      gloopProd d L W H z ⟨σ₁, a₁⟩ * gloopProd d L W H z ⟨σ₂, a₂⟩ := by
  induction σ₁ generalizing a₁ with
  | nil =>
    obtain rfl : a₁ = [] := List.eq_nil_of_length_eq_zero h₁.symm
    simp [gloopProd]
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a, a₁ = b :: a := by
      cases a₁ with
      | nil => simp at h₁
      | cons b a => exact ⟨b, a, rfl⟩
    have h : σ.length = a.length := by simpa using h₁
    simp only [List.cons_append, secondLoop_gloopProd_cons, ih h, Matrix.mul_assoc]

end Sec4Aux

omit [NeZero W] in
/-- The first block trace closes into the loop formed by the suffix,
prefix, and a repeated copy of the differentiated signed Green edge.
`RBM2D/Hierarchy/ContractionSecondLoopSameEdgeCut.lean:21`. -/
theorem trace_sameEdge_cutLoop
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a p : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let G := Gres H z s
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let T := gloopProd d L W H z ⟨σ₂, a₂⟩
    Matrix.trace (((G * Eblk d L W a * T * P) * G) * Eblk d L W p) =
      loopL d L W H z
        ⟨s :: (σ₂ ++ (σ₁ ++ [s])), a :: (a₂ ++ (a₁ ++ [p]))⟩ := by
  rw [secondLoop_loopL_eq, secondLoop_gloopProd_cons, secondLoop_gloopProd_append h₂,
    secondLoop_gloopProd_append h₁]
  simp only [secondLoop_gloopProd_cons, secondLoop_gloopProd_nil, Matrix.mul_one,
    Matrix.mul_assoc]

omit [NeZero W] in
/-- The second block trace is the one-edge loop.
`RBM2D/Hierarchy/ContractionSecondLoopSameEdgeCut.lean:38`. -/
theorem trace_sameEdge_oneLoop
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (z : ℂ) (s : Bool) (q : Zd d L) :
    Matrix.trace (Gres H z s * Eblk d L W q) =
      loopL d L W H z ⟨[s], [q]⟩ := by
  simp only [secondLoop_loopL_eq, secondLoop_gloopProd_cons, secondLoop_gloopProd_nil,
    Matrix.mul_one]

/-- The same-edge variance contraction at the specified split of a finite
loop word. No sum over edge positions or expectation is taken.
`RBM2D/Hierarchy/ContractionSecondLoopSameEdgeCut.lean:47`. -/
theorem sum_sameEdge_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock d L W u ω
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let T := gloopProd d L W H z ⟨σ₂, a₂⟩
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (P * (gsigCoordinateSecondDeriv d L W u ω γ z s *
          Eblk d L W a) * T)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ∑ p : Zd d L, ∑ q : Zd d L,
        loopL d L W H z
          ⟨s :: (σ₂ ++ (σ₁ ++ [s])), a :: (a₂ ++ (a₁ ++ [p]))⟩ *
          SB d L g p q * loopL d L W H z ⟨[s], [q]⟩ := by
  dsimp only
  rw [sum_gsigCoordinateSecondDeriv_word d L W g u hu ω z s a
    (gloopProd d L W (HflowBlock d L W u ω) z ⟨σ₁, a₁⟩)
    (gloopProd d L W (HflowBlock d L W u ω) z ⟨σ₂, a₂⟩)]
  simp_rw [trace_sameEdge_cutLoop d L W (HflowBlock d L W u ω) z
    σ₁ σ₂ a₁ a₂ s a _ h₁ h₂,
    trace_sameEdge_oneLoop d L W (HflowBlock d L W u ω) z s]

end Sec4

/-! ## 5. Enumerating one selected edge of a finite word
(`ContractionEdgeSplits`) -/

section Sec5

/-- A chosen edge, with the word before and after it.
`RBM2D/Hierarchy/ContractionEdgeSplits.lean:15`. -/
structure EdgeSplit (α : Type*) where
  before : List α
  selected : α
  after : List α

/-- Enumerate the edge at every position from left to right.
`RBM2D/Hierarchy/ContractionEdgeSplits.lean:21`. -/
def edgeSplits {α : Type*} : List α → List (EdgeSplit α)
  | [] => []
  | x :: xs =>
      ⟨[], x, xs⟩ :: (edgeSplits xs).map
        (fun e => ⟨x :: e.before, e.selected, e.after⟩)

/-- Every enumerated split reconstructs the original word.
`RBM2D/Hierarchy/ContractionEdgeSplits.lean:28`. -/
theorem edgeSplits_reconstruct {α : Type*} (l : List α)
    (e : EdgeSplit α) (he : e ∈ edgeSplits l) :
    e.before ++ e.selected :: e.after = l := by
  induction l generalizing e with
  | nil => simp [edgeSplits] at he
  | cons x xs ih =>
      simp only [edgeSplits, List.mem_cons, List.mem_map] at he
      rcases he with rfl | ⟨d, hd, rfl⟩
      · rfl
      · simpa only [List.cons_append] using congrArg (List.cons x) (ih d hd)

/-- The prefix lengths occur in exactly the order `0, ..., length - 1`.
`RBM2D/Hierarchy/ContractionEdgeSplits.lean:40`. -/
theorem edgeSplits_prefix_lengths {α : Type*} (l : List α) :
    (edgeSplits l).map (fun e => e.before.length) = List.range l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [edgeSplits, List.map_cons, List.map_map, List.length_nil,
        List.length_cons, List.range_succ_eq_map]
      congr 1
      rw [← ih, List.map_map]
      rfl

/-- Each valid position occurs exactly once in the edge-split enumeration.
`RBM2D/Hierarchy/ContractionEdgeSplits.lean:52`. -/
theorem edgeSplits_unique_position {α : Type*} (l : List α)
    (i : ℕ) (hi : i < l.length) :
    ∃! e : EdgeSplit α, e ∈ edgeSplits l ∧ e.before.length = i := by
  have hmap : ((edgeSplits l).map (fun e => e.before.length)).Nodup := by
    rw [edgeSplits_prefix_lengths]
    exact List.nodup_range
  have himem : i ∈ (edgeSplits l).map (fun e => e.before.length) := by
    rw [edgeSplits_prefix_lengths]
    exact List.mem_range.mpr hi
  obtain ⟨e, he, heq⟩ := List.mem_map.mp himem
  refine ⟨e, ⟨he, heq⟩, ?_⟩
  intro d ⟨hd, hdeq⟩
  exact (List.inj_on_of_nodup_map hmap he hd (heq.trans hdeq.symm)).symm

end Sec5

/-! ## 6. Enumerating two ordered edges of a finite word
(`ContractionPairSplits`) -/

section Sec6

/-- Two selected edges with the three intervening word segments.
`RBM2D/Hierarchy/ContractionPairSplits.lean:15`. -/
structure PairSplit (α : Type*) where
  before : List α
  first : α
  middle : List α
  second : α
  after : List α

/-- Choose the first edge, then choose the second edge in its suffix.
`RBM2D/Hierarchy/ContractionPairSplits.lean:23`. -/
def pairSplits {α : Type*} (l : List α) : List (PairSplit α) :=
  (edgeSplits l).flatMap fun e =>
    (edgeSplits e.after).map fun f =>
      ⟨e.before, e.selected, f.before, f.selected, f.after⟩

private theorem mem_pairSplits_iff {α : Type*} (l : List α) (p : PairSplit α) :
    p ∈ pairSplits l ↔
      ∃ e ∈ edgeSplits l, ∃ f ∈ edgeSplits e.after,
        p = ⟨e.before, e.selected, f.before, f.selected, f.after⟩ := by
  simp only [pairSplits, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨e, he, f, hf, hfp⟩
    exact ⟨e, he, f, hf, hfp.symm⟩
  · rintro ⟨e, he, f, hf, rfl⟩
    exact ⟨e, he, f, hf, rfl⟩

/-- Every enumerated pair reconstructs the original word.
`RBM2D/Hierarchy/ContractionPairSplits.lean:40`. -/
theorem pairSplits_reconstruct {α : Type*} (l : List α)
    (p : PairSplit α) (hp : p ∈ pairSplits l) :
    p.before ++ p.first :: p.middle ++ p.second :: p.after = l := by
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_pairSplits_iff l p).mp hp
  have houter := edgeSplits_reconstruct l e he
  have hinner := edgeSplits_reconstruct e.after f hf
  simpa only [List.append_assoc, List.cons_append] using
    (hinner ▸ houter)

/-- An enumerated pair always consists of two valid increasing positions.
`RBM2D/Hierarchy/ContractionPairSplits.lean:50`. -/
theorem pairSplits_positions_valid {α : Type*} (l : List α)
    (p : PairSplit α) (hp : p ∈ pairSplits l) :
    p.before.length < p.before.length + 1 + p.middle.length ∧
      p.before.length + 1 + p.middle.length < l.length := by
  have h := pairSplits_reconstruct l p hp
  have hlen : l.length =
      p.before.length + 1 + p.middle.length + 1 + p.after.length := by
    rw [← h, List.length_append, List.length_cons, List.length_append,
      List.length_cons]
    omega
  omega

private theorem edgeSplits_injective_position {α : Type*} (l : List α)
    (e d : EdgeSplit α) (he : e ∈ edgeSplits l) (hd : d ∈ edgeSplits l)
    (h : e.before.length = d.before.length) : e = d := by
  have hnodup : ((edgeSplits l).map (fun x => x.before.length)).Nodup := by
    rw [edgeSplits_prefix_lengths]
    exact List.nodup_range
  exact List.inj_on_of_nodup_map hnodup he hd h

private theorem pairSplits_injective_positions {α : Type*} (l : List α)
    (p q : PairSplit α) (hp : p ∈ pairSplits l) (hq : q ∈ pairSplits l)
    (hfirst : p.before.length = q.before.length)
    (hsecond : p.middle.length = q.middle.length) : p = q := by
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_pairSplits_iff l p).mp hp
  obtain ⟨d, hd, g, hg, rfl⟩ := (mem_pairSplits_iff l q).mp hq
  have hed : e = d := edgeSplits_injective_position l e d he hd hfirst
  subst d
  have hfg : f = g := edgeSplits_injective_position e.after f g hf hg hsecond
  subst g
  rfl

/-- Every ordered pair of distinct positions occurs exactly once.
`RBM2D/Hierarchy/ContractionPairSplits.lean:83`. -/
theorem pairSplits_unique_positions {α : Type*} (l : List α)
    (i j : ℕ) (hij : i < j) (hj : j < l.length) :
    ∃! p : PairSplit α,
      p ∈ pairSplits l ∧ p.before.length = i ∧
        p.before.length + 1 + p.middle.length = j := by
  obtain ⟨e, ⟨he, hei⟩, _⟩ := edgeSplits_unique_position l i (lt_trans hij hj)
  have hlen : l.length = e.before.length + 1 + e.after.length := by
    have h := edgeSplits_reconstruct l e he
    rw [← h, List.length_append, List.length_cons]
    omega
  have hk : j - (i + 1) < e.after.length := by omega
  obtain ⟨f, ⟨hf, hfk⟩, _⟩ :=
    edgeSplits_unique_position e.after (j - (i + 1)) hk
  let p : PairSplit α := ⟨e.before, e.selected, f.before, f.selected, f.after⟩
  have hp : p ∈ pairSplits l := (mem_pairSplits_iff l p).mpr ⟨e, he, f, hf, rfl⟩
  refine ⟨p, ⟨hp, hei, ?_⟩, ?_⟩
  · dsimp [p]
    omega
  · intro q ⟨hq, hqi, hqj⟩
    apply pairSplits_injective_positions l q p hq hp
    · exact hqi.trans hei.symm
    · dsimp [p] at hqj ⊢
      omega

end Sec6

/-! ## 7. The first coordinate derivative as a sum over edge positions
(`ContractionFirstDerivativePositionSum`) -/

section Sec7

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The undifferentiated matrix word on a list of signed block edges.
`RBM2D/Hierarchy/ContractionFirstDerivativePositionSum.lean:19`. -/
noncomputable def coordinateWordProduct (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2 * M) 1

/-- Differentiate precisely the chosen edge of a split word.
`RBM2D/Hierarchy/ContractionFirstDerivativePositionSum.lean:24`. -/
noncomputable def coordinateEdgeTerm (u : ℝ) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (e : EdgeSplit (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  coordinateWordProduct d L W u ω z e.before *
    (gsigCoordinateDeriv d L W u ω γ z e.selected.1 * Eblk d L W e.selected.2) *
    coordinateWordProduct d L W u ω z e.after

omit [NeZero W] in
private theorem sum_map_mul_left
    (A : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (ms : List (Matrix (Vtx d L W) (Vtx d L W) ℂ)) :
    (ms.map (fun M => A * M)).sum = A * ms.sum := by
  induction ms with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
  | cons M ms ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- The recursive first product rule is exactly the finite sum over all
selected edges. Prefix and suffix matrix factors remain in word order.
`RBM2D/Hierarchy/ContractionFirstDerivativePositionSum.lean:43`. -/
theorem coordinateWordDeriv_eq_edgeSplits_sum
    (u : ℝ) (ω : Ω d L W) (γ : CoordF d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    coordinateWordDeriv d L W u ω γ z l =
      ((edgeSplits l).map (coordinateEdgeTerm d L W u ω γ z)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      let A := Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2
      let D := gsigCoordinateDeriv d L W u ω γ z p.1 * Eblk d L W p.2
      have hshift (e : EdgeSplit (Bool × Zd d L)) :
          coordinateEdgeTerm d L W u ω γ z
              ⟨p :: e.before, e.selected, e.after⟩ =
            A * coordinateEdgeTerm d L W u ω γ z e := by
        dsimp [A, coordinateEdgeTerm, coordinateWordProduct]
        simp only [Matrix.mul_assoc]
      have hhead : coordinateEdgeTerm d L W u ω γ z
          ⟨[], p, l⟩ = D * coordinateWordProduct d L W u ω z l := by
        dsimp [D, coordinateEdgeTerm, coordinateWordProduct]
        simp only [one_mul]
      simp only [coordinateWordDeriv, edgeSplits, List.map_cons, List.sum_cons]
      rw [ih]
      rw [hhead]
      rw [List.map_map]
      change D * coordinateWordProduct d L W u ω z l +
          A * ((edgeSplits l).map (coordinateEdgeTerm d L W u ω γ z)).sum =
        D * coordinateWordProduct d L W u ω z l +
          ((edgeSplits l).map (fun e => coordinateEdgeTerm d L W u ω γ z
            ⟨p :: e.before, e.selected, e.after⟩)).sum
      simp_rw [hshift]
      rw [← sum_map_mul_left d L W A
        ((edgeSplits l).map (coordinateEdgeTerm d L W u ω γ z)), List.map_map]
      rfl

end Sec7

/-! ## 8. The second coordinate derivative as finite position sums
(`ContractionSecondDerivativePositionSum`) -/

section Sec8

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The second derivative applied twice to the selected Green edge.
`RBM2D/Hierarchy/ContractionSecondDerivativePositionSum.lean:19`. -/
noncomputable def coordinateSameEdgeTerm (u : ℝ) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (e : EdgeSplit (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  coordinateWordProduct d L W u ω z e.before *
    (gsigCoordinateSecondDeriv d L W u ω γ z e.selected.1 * Eblk d L W e.selected.2) *
    coordinateWordProduct d L W u ω z e.after

/-- First derivatives applied once to each of two ordered selected edges.
`RBM2D/Hierarchy/ContractionSecondDerivativePositionSum.lean:27`. -/
noncomputable def coordinatePairTerm (u : ℝ) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (p : PairSplit (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  coordinateWordProduct d L W u ω z p.before *
    (gsigCoordinateDeriv d L W u ω γ z p.first.1 * Eblk d L W p.first.2) *
    coordinateWordProduct d L W u ω z p.middle *
    (gsigCoordinateDeriv d L W u ω γ z p.second.1 * Eblk d L W p.second.2) *
    coordinateWordProduct d L W u ω z p.after

private theorem pairSplits_cons {α : Type*} (x : α) (xs : List α) :
    pairSplits (x :: xs) =
      (edgeSplits xs).map (fun e : EdgeSplit α =>
        (⟨[], x, e.before, e.selected, e.after⟩ : PairSplit α)) ++
      (pairSplits xs).map (fun p : PairSplit α =>
        ⟨x :: p.before, p.first, p.middle, p.second, p.after⟩) := by
  simp [pairSplits, edgeSplits, List.flatMap_cons, List.flatMap_map,
    List.map_flatMap, List.map_map]
  rfl

/-- Sum of all same-edge second-derivative terms.
`RBM2D/Hierarchy/ContractionSecondDerivativePositionSum.lean:57`. -/
noncomputable def coordinateSameEdgeSum (u : ℝ) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (l : List (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  ((edgeSplits l).map (coordinateSameEdgeTerm d L W u ω γ z)).sum

/-- Sum over each unordered pair of distinct positions, keeping the
original left-to-right matrix order.
`RBM2D/Hierarchy/ContractionSecondDerivativePositionSum.lean:64`. -/
noncomputable def coordinatePairSum (u : ℝ) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (l : List (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  ((pairSplits l).map (coordinatePairTerm d L W u ω γ z)).sum

private theorem coordinateSameEdgeSum_cons
    (u : ℝ) (ω : Ω d L W) (γ : CoordF d L W) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    coordinateSameEdgeSum d L W u ω γ z (p :: l) =
      (gsigCoordinateSecondDeriv d L W u ω γ z p.1 * Eblk d L W p.2) *
        coordinateWordProduct d L W u ω z l +
      (Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2) *
        coordinateSameEdgeSum d L W u ω γ z l := by
  let A := Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2
  let S := gsigCoordinateSecondDeriv d L W u ω γ z p.1 * Eblk d L W p.2
  have hhead : coordinateSameEdgeTerm d L W u ω γ z ⟨[], p, l⟩ =
      S * coordinateWordProduct d L W u ω z l := by
    dsimp [S, coordinateSameEdgeTerm, coordinateWordProduct]
    simp only [one_mul]
  have hshift (e : EdgeSplit (Bool × Zd d L)) :
      coordinateSameEdgeTerm d L W u ω γ z ⟨p :: e.before, e.selected, e.after⟩ =
        A * coordinateSameEdgeTerm d L W u ω γ z e := by
    dsimp [A, coordinateSameEdgeTerm, coordinateWordProduct]
    simp only [Matrix.mul_assoc]
  simp only [coordinateSameEdgeSum, edgeSplits, List.map_cons, List.sum_cons]
  rw [hhead, List.map_map]
  simp only [Function.comp_def]
  simp_rw [hshift]
  rw [← sum_map_mul_left d L W A
    ((edgeSplits l).map (coordinateSameEdgeTerm d L W u ω γ z)), List.map_map]
  rfl

private theorem coordinatePairSum_cons
    (u : ℝ) (ω : Ω d L W) (γ : CoordF d L W) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    coordinatePairSum d L W u ω γ z (p :: l) =
      (gsigCoordinateDeriv d L W u ω γ z p.1 * Eblk d L W p.2) *
        ((edgeSplits l).map (coordinateEdgeTerm d L W u ω γ z)).sum +
      (Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2) *
        coordinatePairSum d L W u ω γ z l := by
  let A := Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2
  let D := gsigCoordinateDeriv d L W u ω γ z p.1 * Eblk d L W p.2
  have hhead (e : EdgeSplit (Bool × Zd d L)) :
      coordinatePairTerm d L W u ω γ z
          ⟨[], p, e.before, e.selected, e.after⟩ =
        D * coordinateEdgeTerm d L W u ω γ z e := by
    dsimp [D, coordinatePairTerm, coordinateEdgeTerm, coordinateWordProduct]
    simp only [one_mul, Matrix.mul_assoc]
  have hshift (q : PairSplit (Bool × Zd d L)) :
      coordinatePairTerm d L W u ω γ z
          ⟨p :: q.before, q.first, q.middle, q.second, q.after⟩ =
        A * coordinatePairTerm d L W u ω γ z q := by
    dsimp [A, coordinatePairTerm, coordinateWordProduct]
    simp only [Matrix.mul_assoc]
  simp only [coordinatePairSum, pairSplits_cons, List.map_append,
    List.sum_append, List.map_map, Function.comp_def]
  simp_rw [hhead, hshift]
  rw [← sum_map_mul_left d L W D
    ((edgeSplits l).map (coordinateEdgeTerm d L W u ω γ z)),
    ← sum_map_mul_left d L W A
      ((pairSplits l).map (coordinatePairTerm d L W u ω γ z))]
  simp only [List.map_map, Function.comp_def]

/-- For every finite signed word, the second coordinate derivative is the
sum over all same-edge insertions plus twice the sum over all pairs of
distinct edges. The `PairSplit` enumerator lists each pair only once.
`RBM2D/Hierarchy/ContractionSecondDerivativePositionSum.lean:130`. -/
theorem coordinateSecondWordDeriv_eq_position_sums
    (u : ℝ) (ω : Ω d L W) (γ : CoordF d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    coordinateSecondWordDeriv d L W u ω γ z l =
      coordinateSameEdgeSum d L W u ω γ z l +
        (2 : ℕ) • coordinatePairSum d L W u ω γ z l := by
  induction l with
  | nil =>
      simp only [coordinateSecondWordDeriv, coordinateSameEdgeSum,
        coordinatePairSum, edgeSplits, pairSplits, List.flatMap_nil,
        List.map_nil, List.sum_nil,
        smul_zero, add_zero]
  | cons p l ih =>
      rw [coordinateSecondWordDeriv,
        coordinateSameEdgeSum_cons d L W u ω γ z p l,
        coordinatePairSum_cons d L W u ω γ z p l,
        coordinateWordDeriv_eq_edgeSplits_sum d L W u ω γ z l, ih]
      simp only [coordinateWordProduct, nsmul_eq_mul, Nat.cast_ofNat,
        two_mul, mul_add]
      abel

end Sec8

/-! ## 9. Finite trace and Gaussian-coordinate sums of the second word derivative
(`ContractionSecondDerivativeTraceSum`) -/

section Sec9

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

private theorem sum_weighted_trace_list {α : Type*}
    (es : List α) (w : CoordF d L W → ℂ)
    (T : CoordF d L W → α → Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ γ : CoordF d L W, w γ * Matrix.trace ((es.map (T γ)).sum) =
      (es.map (fun e => ∑ γ : CoordF d L W, w γ * Matrix.trace (T γ e))).sum := by
  induction es with
  | nil =>
      simp only [List.map_nil, List.sum_nil, Matrix.trace_zero, mul_zero,
        Finset.sum_const_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.trace_add, mul_add,
        Finset.sum_add_distrib, ih]

/-- Exact finite exchange of coordinate and edge-position sums in the
traced second product rule. No loop-cut or expectation identity is used.
`RBM2D/Hierarchy/ContractionSecondDerivativeTraceSum.lean:33`. -/
theorem sum_coordinateSecondWordDeriv_trace_positions
    (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv d L W u ω γ z l)) =
    ((edgeSplits l).map (fun e => ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSameEdgeTerm d L W u ω γ z e)))).sum +
    (2 : ℂ) * ((pairSplits l).map (fun p => ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (coordinatePairTerm d L W u ω γ z p)))).sum := by
  simp_rw [coordinateSecondWordDeriv_eq_position_sums d L W]
  simp only [two_nsmul, Matrix.trace_add, mul_add, Finset.sum_add_distrib,
    coordinateSameEdgeSum, coordinatePairSum]
  rw [sum_weighted_trace_list d L W (edgeSplits l),
    sum_weighted_trace_list d L W (pairSplits l)]
  ring

end Sec9

/-! ## 10. Matching position-split word segments with loop products
(`ContractionPositionLoopBridge`) -/

section Sec10

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The sign and block-label projections of a signed word segment.
`RBM2D/Hierarchy/ContractionPositionLoopBridge.lean:19`. -/
def segmentLoopIdx (l : List (Bool × Zd d L)) : Loop.LoopIdx (Zd d L) :=
  ⟨l.map Prod.fst, l.map Prod.snd⟩

omit [NeZero L] [NeZero W] in
/-- A projected word segment always has matching sign and block lengths.
`RBM2D/Hierarchy/ContractionPositionLoopBridge.lean:24`. -/
theorem segmentLoopIdx_WF (l : List (Bool × Zd d L)) :
    (segmentLoopIdx d L l).WF := by
  simp only [segmentLoopIdx, Loop.LoopIdx.WF, List.length_map]

omit [NeZero L] [NeZero W] in
private theorem zip_segment_projections (l : List (Bool × Zd d L)) :
    (l.map Prod.fst).zip (l.map Prod.snd) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      cases p
      simp only [List.map_cons, List.zip_cons_cons, ih]

/-- The finite matrix word on a segment equals its loop-index product.
`RBM2D/Hierarchy/ContractionPositionLoopBridge.lean:38`. -/
theorem coordinateWordProduct_eq_gloopProd
    (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    coordinateWordProduct d L W u ω z l =
      gloopProd d L W (HflowBlock d L W u ω) z (segmentLoopIdx d L l) := by
  unfold coordinateWordProduct gloopProd segmentLoopIdx
  rw [zip_segment_projections d L l]

/-- Both segments of a one-edge split have genuine, well-formed loop words.
`RBM2D/Hierarchy/ContractionPositionLoopBridge.lean:47`. -/
theorem edgeSplit_segment_products
    (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (e : EdgeSplit (Bool × Zd d L)) :
    (segmentLoopIdx d L e.before).WF ∧
      (segmentLoopIdx d L e.after).WF ∧
      coordinateWordProduct d L W u ω z e.before =
        gloopProd d L W (HflowBlock d L W u ω) z (segmentLoopIdx d L e.before) ∧
      coordinateWordProduct d L W u ω z e.after =
        gloopProd d L W (HflowBlock d L W u ω) z (segmentLoopIdx d L e.after) := by
  exact ⟨segmentLoopIdx_WF d L e.before, segmentLoopIdx_WF d L e.after,
    coordinateWordProduct_eq_gloopProd d L W u ω z e.before,
    coordinateWordProduct_eq_gloopProd d L W u ω z e.after⟩

/-- All three segments of a two-edge split have genuine, well-formed loop
words, and their products agree with the coordinate-derivative convention.
`RBM2D/Hierarchy/ContractionPositionLoopBridge.lean:62`. -/
theorem pairSplit_segment_products
    (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (p : PairSplit (Bool × Zd d L)) :
    (segmentLoopIdx d L p.before).WF ∧
      (segmentLoopIdx d L p.middle).WF ∧
      (segmentLoopIdx d L p.after).WF ∧
      coordinateWordProduct d L W u ω z p.before =
        gloopProd d L W (HflowBlock d L W u ω) z (segmentLoopIdx d L p.before) ∧
      coordinateWordProduct d L W u ω z p.middle =
        gloopProd d L W (HflowBlock d L W u ω) z (segmentLoopIdx d L p.middle) ∧
      coordinateWordProduct d L W u ω z p.after =
        gloopProd d L W (HflowBlock d L W u ω) z (segmentLoopIdx d L p.after) := by
  exact ⟨segmentLoopIdx_WF d L p.before, segmentLoopIdx_WF d L p.middle,
    segmentLoopIdx_WF d L p.after,
    coordinateWordProduct_eq_gloopProd d L W u ω z p.before,
    coordinateWordProduct_eq_gloopProd d L W u ω z p.middle,
    coordinateWordProduct_eq_gloopProd d L W u ω z p.after⟩

end Sec10

/-! ## 11. The same-edge cut formula at one enumerated loop position
(`ContractionSameEdgePositionCut`) -/

section Sec11

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- At any chosen edge, the weighted second-coordinate insertion is the
same-edge cut-loop double sum. The two projected segments are well formed.
`RBM2D/Hierarchy/ContractionSameEdgePositionCut.lean:20`. -/
theorem sum_coordinateSameEdgeTerm_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (e : EdgeSplit (Bool × Zd d L)) :
    let H := HflowBlock d L W u ω
    let I₁ := segmentLoopIdx d L e.before
    let I₂ := segmentLoopIdx d L e.after
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSameEdgeTerm d L W u ω γ z e)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ∑ p : Zd d L, ∑ q : Zd d L,
        loopL d L W H z
          ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
            e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
          SB d L g p q * loopL d L W H z ⟨[e.selected.1], [q]⟩ := by
  have h₁ : (e.before.map Prod.fst).length =
      (e.before.map Prod.snd).length := segmentLoopIdx_WF d L e.before
  have h₂ : (e.after.map Prod.fst).length =
      (e.after.map Prod.snd).length := segmentLoopIdx_WF d L e.after
  dsimp only [coordinateSameEdgeTerm, segmentLoopIdx]
  rw [coordinateWordProduct_eq_gloopProd d L W u ω z e.before,
    coordinateWordProduct_eq_gloopProd d L W u ω z e.after]
  exact sum_sameEdge_cutLoops d L W g u hu ω z
    (e.before.map Prod.fst) (e.after.map Prod.fst)
    (e.before.map Prod.snd) (e.after.map Prod.snd)
    e.selected.1 e.selected.2 h₁ h₂

/-- Membership in the position enumerator supplies the literal split of the
original word, together with its cut-loop contraction.
`RBM2D/Hierarchy/ContractionSameEdgePositionCut.lean:49`. -/
theorem sum_coordinateSameEdgeTerm_cutLoops_of_mem
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) (e : EdgeSplit (Bool × Zd d L))
    (he : e ∈ edgeSplits l) :
    e.before ++ e.selected :: e.after = l ∧
      (let H := HflowBlock d L W u ω
       let I₁ := segmentLoopIdx d L e.before
       let I₂ := segmentLoopIdx d L e.after
       ∑ γ : CoordF d L W,
         (((gvarF d L W g γ : ℝ) : ℂ) *
           Matrix.trace (coordinateSameEdgeTerm d L W u ω γ z e)) =
       (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
         ∑ p : Zd d L, ∑ q : Zd d L,
           loopL d L W H z
             ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
               e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
             SB d L g p q * loopL d L W H z ⟨[e.selected.1], [q]⟩) := by
  exact ⟨edgeSplits_reconstruct l e he,
    sum_coordinateSameEdgeTerm_cutLoops d L W g u hu ω z e⟩

end Sec11

/-! ## 12. The two-edge cut formula at one enumerated pair of loop positions
(`ContractionPairPositionCut`) -/

section Sec12

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- At any chosen ordered pair of edges, the Gaussian variance contraction
is the corresponding left/right cut-loop double sum.
`RBM2D/Hierarchy/ContractionPairPositionCut.lean:20`. -/
theorem sum_coordinatePairTerm_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (p : PairSplit (Bool × Zd d L)) :
    let H := HflowBlock d L W u ω
    let I₁ := segmentLoopIdx d L p.before
    let I₂ := segmentLoopIdx d L p.middle
    let I₃ := segmentLoopIdx d L p.after
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (coordinatePairTerm d L W u ω γ z p)) =
    (u : ℂ) * (W : ℂ) ^ d * ∑ v : Zd d L, ∑ w : Zd d L,
      loopL d L W H z
        ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
            I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
          (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
        SB d L g v w *
      loopL d L W H z
        ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
            I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
          (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w) := by
  have h₁ : (p.before.map Prod.fst).length =
      (p.before.map Prod.snd).length := segmentLoopIdx_WF d L p.before
  have h₂ : (p.middle.map Prod.fst).length =
      (p.middle.map Prod.snd).length := segmentLoopIdx_WF d L p.middle
  dsimp only [coordinatePairTerm, segmentLoopIdx]
  rw [coordinateWordProduct_eq_gloopProd d L W u ω z p.before,
    coordinateWordProduct_eq_gloopProd d L W u ω z p.middle,
    coordinateWordProduct_eq_gloopProd d L W u ω z p.after]
  exact sum_twoEdge_mixed_deriv d L W g u hu ω z
    (p.before.map Prod.fst) (p.middle.map Prod.fst) (p.after.map Prod.fst)
    (p.before.map Prod.snd) (p.middle.map Prod.snd) (p.after.map Prod.snd)
    p.first.1 p.second.1 p.first.2 p.second.2 h₁ h₂

/-- Pair membership supplies the literal five-part split of the original
word, alongside the fixed-position variance contraction.
`RBM2D/Hierarchy/ContractionPairPositionCut.lean:55`. -/
theorem sum_coordinatePairTerm_cutLoops_of_mem
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) (p : PairSplit (Bool × Zd d L))
    (hp : p ∈ pairSplits l) :
    p.before ++ p.first :: p.middle ++ p.second :: p.after = l ∧
      (let H := HflowBlock d L W u ω
       let I₁ := segmentLoopIdx d L p.before
       let I₂ := segmentLoopIdx d L p.middle
       let I₃ := segmentLoopIdx d L p.after
       ∑ γ : CoordF d L W,
         (((gvarF d L W g γ : ℝ) : ℂ) *
           Matrix.trace (coordinatePairTerm d L W u ω γ z p)) =
       (u : ℂ) * (W : ℂ) ^ d * ∑ v : Zd d L, ∑ w : Zd d L,
         loopL d L W H z
           ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
               I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
             (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
           SB d L g v w *
         loopL d L W H z
           ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
               I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
             (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w)) := by
  exact ⟨pairSplits_reconstruct l p hp,
    sum_coordinatePairTerm_cutLoops d L W g u hu ω z p⟩

end Sec12

/-! ## 13. All finite cut terms in the variance-weighted second loop derivative
(`ContractionSecondLoopAllCuts`) -/

section Sec13

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The cut-loop product attached to one same-edge position, without its
common coefficient `2uW^d`. `RBM2D/Hierarchy/ContractionSecondLoopAllCuts.lean:20`. -/
noncomputable def sameEdgeCutValue (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (e : EdgeSplit (Bool × Zd d L)) : ℂ :=
  let H := HflowBlock d L W u ω
  let I₁ := segmentLoopIdx d L e.before
  let I₂ := segmentLoopIdx d L e.after
  ∑ p : Zd d L, ∑ q : Zd d L,
    loopL d L W H z
      ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
        e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
      SB d L g p q * loopL d L W H z ⟨[e.selected.1], [q]⟩

/-- The left/right cut-loop product attached to one pair of distinct edges,
without its common coefficient `2uW^d` from the two derivative orders.
`RBM2D/Hierarchy/ContractionSecondLoopAllCuts.lean:33`. -/
noncomputable def pairCutValue (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (p : PairSplit (Bool × Zd d L)) : ℂ :=
  let H := HflowBlock d L W u ω
  let I₁ := segmentLoopIdx d L p.before
  let I₂ := segmentLoopIdx d L p.middle
  let I₃ := segmentLoopIdx d L p.after
  ∑ v : Zd d L, ∑ w : Zd d L,
    loopL d L W H z
      ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
          I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
        (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
      SB d L g v w *
    loopL d L W H z
      ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
          I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
        (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w)

omit [NeZero L] [NeZero W] in
private theorem list_sum_map_mul_left {α : Type*} (c : ℂ)
    (es : List α) (f : α → ℂ) :
    (es.map (fun e => c * f e)).sum = c * (es.map f).sum := by
  induction es with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- The full finite samplewise cut formula for any actual signed word.
Both same-edge and distinct-edge families have coefficient `2uW^d`.
`RBM2D/Hierarchy/ContractionSecondLoopAllCuts.lean:61`. -/
theorem sum_coordinateSecondWordDeriv_allCuts
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv d L W u ω γ z l)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ((edgeSplits l).map (sameEdgeCutValue d L W g u ω z)).sum +
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ((pairSplits l).map (pairCutValue d L W g u ω z)).sum := by
  rw [sum_coordinateSecondWordDeriv_trace_positions d L W g u ω z l]
  simp_rw [sum_coordinateSameEdgeTerm_cutLoops d L W g u hu ω z]
  simp_rw [sum_coordinatePairTerm_cutLoops d L W g u hu ω z]
  change ((edgeSplits l).map (fun e =>
      ((2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d) * sameEdgeCutValue d L W g u ω z e)).sum +
    (2 : ℂ) * ((pairSplits l).map (fun p =>
      ((u : ℂ) * (W : ℂ) ^ d) * pairCutValue d L W g u ω z p)).sum = _
  rw [list_sum_map_mul_left, list_sum_map_mul_left]
  ring

omit [NeZero L] [NeZero W] in
/-- Zipping a well-formed loop and projecting it back preserves its literal
sign and block-label lists. `RBM2D/Hierarchy/ContractionSecondLoopAllCuts.lean:84`. -/
theorem segmentLoopIdx_zip_eq (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    segmentLoopIdx d L (I.σ.zip I.a) = I := by
  cases I with
  | mk σ a =>
      change σ.length = a.length at hwf
      change (⟨(σ.zip a).map Prod.fst, (σ.zip a).map Prod.snd⟩ :
        Loop.LoopIdx (Zd d L)) = ⟨σ, a⟩
      rw [List.map_fst_zip hwf.le, List.map_snd_zip hwf.ge]

/-- The full samplewise cut formula for a well-formed finite loop. The first
conclusion certifies that the signed word used by the derivative is exactly
the supplied loop, without truncation by `List.zip`.
`RBM2D/Hierarchy/ContractionSecondLoopAllCuts.lean:96`. -/
theorem sum_gloopSecondWordDeriv_allCuts
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    let l := I.σ.zip I.a
    segmentLoopIdx d L l = I ∧
      (∑ γ : CoordF d L W,
        (((gvarF d L W g γ : ℝ) : ℂ) *
          Matrix.trace (coordinateSecondWordDeriv d L W u ω γ z l)) =
       (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
         ((edgeSplits l).map (sameEdgeCutValue d L W g u ω z)).sum +
       (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
         ((pairSplits l).map (pairCutValue d L W g u ω z)).sum) := by
  exact ⟨segmentLoopIdx_zip_eq d L I hwf,
    sum_coordinateSecondWordDeriv_allCuts d L W g u hu ω z (I.σ.zip I.a)⟩

end Sec13

/-! ## 14. Compiled nonempty instances

Every target is applied at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `u = 1/2`, `z = i`: the fine
lattice `Z_6^3` has `(W L)^d = 216` points, the block-product index `Z_3^3 × Fin 8` also, and
there are `27` blocks.  The statements are unconditional identities at an arbitrary sample `ω`
(the flow matrix `HflowBlock 3 3 2 (1/2) ω`, a variable of the examples); the hypotheses
`0 ≤ u` and the length conditions are discharged by `norm_num` and `rfl`.  The chain data have
the two cut positions `σ₁ = [+, -]`, `σ₂ = [-, +]`, `σ₃ = [+]` (loop length `7`, cuts
`k = 3`, `l = 6`); the word of the position sums has three edges. -/

namespace SecondLoopInst

/-- A block label of `Z_3^3`. -/
private def lab (n : ℕ) : Zd 3 3 := fun i => ((n + i.val : ℕ) : ZMod 3)

/-- A coordinate: the off-diagonal real coordinate `(0, (1,0,0), true)` of `Z_6^3`. -/
private def γ0 : CoordF 3 3 2 := (![0, 0, 0], ![1, 0, 0], true)

/-- A signed word of three edges. -/
private def word3 : List (Bool × Zd 3 3) := [(true, lab 1), (false, lab 2), (true, lab 3)]

/-- The split at the middle edge. -/
private def e1 : EdgeSplit (Bool × Zd 3 3) := ⟨[(true, lab 1)], (false, lab 2), [(true, lab 3)]⟩

private theorem e1_mem : e1 ∈ edgeSplits word3 := by
  simp [edgeSplits, word3, e1]

/-- The pair of the first and the last edge. -/
private def p13 : PairSplit (Bool × Zd 3 3) :=
  ⟨[], (true, lab 1), [(false, lab 2)], (true, lab 3), []⟩

private theorem p13_mem : p13 ∈ pairSplits word3 := by
  simp [pairSplits, edgeSplits, word3, p13]

/-- `trace_twoEdge_mixed_eq_cutChains`. -/
example (ω : Ω 3 3 2) :=
  trace_twoEdge_mixed_eq_cutChains 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) Complex.I
    [true, false] [false, true] [true] [lab 4, lab 17] [lab 9, lab 22] [lab 0]
    true false (lab 5) (lab 2) (coordinateBlock 3 3 2 γ0)

/-- `sum_twoEdge_mixed_cutChains`. -/
example (ω : Ω 3 3 2) :=
  sum_twoEdge_mixed_cutChains 3 3 2 (1 / 2) (HflowBlock 3 3 2 (1 / 2) ω) Complex.I
    [true, false] [false, true] [true] [lab 4, lab 17] [lab 9, lab 22] [lab 0]
    true false (lab 5) (lab 2) rfl rfl

/-- `sum_twoEdge_mixed_coordinate`. -/
example (ω : Ω 3 3 2) :=
  sum_twoEdge_mixed_coordinate 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I
    [true, false] [false, true] [true] [lab 4, lab 17] [lab 9, lab 22] [lab 0]
    true false (lab 5) (lab 2) rfl rfl

/-- `sum_twoEdge_mixed_deriv`. -/
example (ω : Ω 3 3 2) :=
  sum_twoEdge_mixed_deriv 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I
    [true, false] [false, true] [true] [lab 4, lab 17] [lab 9, lab 22] [lab 0]
    true false (lab 5) (lab 2) rfl rfl

/-- `sum_coordinateBlock_trace_pair`. -/
example (ω : Ω 3 3 2) :=
  sum_coordinateBlock_trace_pair 3 3 2 (1 / 2) (HflowBlock 3 3 2 (1 / 2) ω)
    (HflowBlock 3 3 2 (1 / 2) ω)

/-- `trace_gsigCoordinateSecondDeriv_Eblk`. -/
example (ω : Ω 3 3 2) :=
  trace_gsigCoordinateSecondDeriv_Eblk 3 3 2 (1 / 2) (by norm_num) ω γ0 Complex.I true (lab 5)

/-- `sum_gsigCoordinateSecondDeriv_Eblk`. -/
example (ω : Ω 3 3 2) :=
  sum_gsigCoordinateSecondDeriv_Eblk 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I true (lab 5)

/-- `trace_gsigCoordinateSecondDeriv_word`. -/
example (ω : Ω 3 3 2) :=
  trace_gsigCoordinateSecondDeriv_word 3 3 2 (1 / 2) (by norm_num) ω γ0 Complex.I true (lab 5)
    (HflowBlock 3 3 2 (1 / 2) ω) (HflowBlock 3 3 2 (1 / 2) ω)

/-- `sum_gsigCoordinateSecondDeriv_word`. -/
example (ω : Ω 3 3 2) :=
  sum_gsigCoordinateSecondDeriv_word 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I true
    (lab 5) (HflowBlock 3 3 2 (1 / 2) ω) (HflowBlock 3 3 2 (1 / 2) ω)

/-- `trace_sameEdge_cutLoop`. -/
example (ω : Ω 3 3 2) :=
  trace_sameEdge_cutLoop 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) Complex.I
    [true, false] [false, true] [lab 4, lab 17] [lab 9, lab 22] true (lab 5) (lab 6) rfl rfl

/-- `trace_sameEdge_oneLoop`. -/
example (ω : Ω 3 3 2) :=
  trace_sameEdge_oneLoop 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) Complex.I true (lab 6)

/-- `sum_sameEdge_cutLoops`. -/
example (ω : Ω 3 3 2) :=
  sum_sameEdge_cutLoops 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I
    [true, false] [false, true] [lab 4, lab 17] [lab 9, lab 22] true (lab 5) rfl rfl

/-- `edgeSplits_reconstruct`, `edgeSplits_prefix_lengths`, `edgeSplits_unique_position`. -/
example : e1.before ++ e1.selected :: e1.after = word3 ∧
    (edgeSplits word3).map (fun e => e.before.length) = List.range word3.length ∧
    ∃! e : EdgeSplit (Bool × Zd 3 3), e ∈ edgeSplits word3 ∧ e.before.length = 1 :=
  ⟨edgeSplits_reconstruct word3 e1 e1_mem, edgeSplits_prefix_lengths word3,
    edgeSplits_unique_position word3 1 (by simp [word3])⟩

/-- `pairSplits_reconstruct`, `pairSplits_positions_valid`, `pairSplits_unique_positions`. -/
example : p13.before ++ p13.first :: p13.middle ++ p13.second :: p13.after = word3 ∧
    (p13.before.length < p13.before.length + 1 + p13.middle.length ∧
      p13.before.length + 1 + p13.middle.length < word3.length) ∧
    ∃! p : PairSplit (Bool × Zd 3 3), p ∈ pairSplits word3 ∧ p.before.length = 0 ∧
      p.before.length + 1 + p.middle.length = 2 :=
  ⟨pairSplits_reconstruct word3 p13 p13_mem, pairSplits_positions_valid word3 p13 p13_mem,
    pairSplits_unique_positions word3 0 2 (by norm_num) (by simp [word3])⟩

/-- `coordinateWordDeriv_eq_edgeSplits_sum`. -/
example (ω : Ω 3 3 2) :=
  coordinateWordDeriv_eq_edgeSplits_sum 3 3 2 (1 / 2) ω γ0 Complex.I word3

/-- `coordinateSecondWordDeriv_eq_position_sums`. -/
example (ω : Ω 3 3 2) :=
  coordinateSecondWordDeriv_eq_position_sums 3 3 2 (1 / 2) ω γ0 Complex.I word3

/-- `sum_coordinateSecondWordDeriv_trace_positions`. -/
example (ω : Ω 3 3 2) :=
  sum_coordinateSecondWordDeriv_trace_positions 3 3 2 (1 / 2) (1 / 2) ω Complex.I word3

/-- `segmentLoopIdx_WF`, `coordinateWordProduct_eq_gloopProd`. -/
example (ω : Ω 3 3 2) :=
  And.intro (segmentLoopIdx_WF 3 3 word3)
    (coordinateWordProduct_eq_gloopProd 3 3 2 (1 / 2) ω Complex.I word3)

/-- `edgeSplit_segment_products`. -/
example (ω : Ω 3 3 2) :=
  edgeSplit_segment_products 3 3 2 (1 / 2) ω Complex.I e1

/-- `pairSplit_segment_products`. -/
example (ω : Ω 3 3 2) :=
  pairSplit_segment_products 3 3 2 (1 / 2) ω Complex.I p13

/-- `sum_coordinateSameEdgeTerm_cutLoops` and `_of_mem`. -/
example (ω : Ω 3 3 2) :=
  And.intro
    (sum_coordinateSameEdgeTerm_cutLoops 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I e1)
    (sum_coordinateSameEdgeTerm_cutLoops_of_mem 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I
      word3 e1 e1_mem)

/-- `sum_coordinatePairTerm_cutLoops` and `_of_mem`. -/
example (ω : Ω 3 3 2) :=
  And.intro
    (sum_coordinatePairTerm_cutLoops 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I p13)
    (sum_coordinatePairTerm_cutLoops_of_mem 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I
      word3 p13 p13_mem)

/-- `sum_coordinateSecondWordDeriv_allCuts`. -/
example (ω : Ω 3 3 2) :=
  sum_coordinateSecondWordDeriv_allCuts 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I word3

/-- `segmentLoopIdx_zip_eq`, `sum_gloopSecondWordDeriv_allCuts`, for the loop `(+,-,+)`. -/
example (ω : Ω 3 3 2) :=
  And.intro
    (segmentLoopIdx_zip_eq 3 3
      (⟨[true, false, true], [lab 1, lab 2, lab 3]⟩ : Loop.LoopIdx (Zd 3 3)) rfl)
    (sum_gloopSecondWordDeriv_allCuts 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I
      ⟨[true, false, true], [lab 1, lab 2, lab 3]⟩ rfl)

end SecondLoopInst

end RBM.Gauss
