/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Hierarchy.ContractionBasic
import RBM3D.Gauss.LoopCoordinate

/-!
# The second-derivative contraction of loops

Everything is a finite-matrix identity at a fixed sample `(u, ω, z)`: no probability, no
expectation, no estimate.  The combinatorial lists `edgeSplits`, `pairSplits` are
dimension-free.  The coefficient `W^d` is the one of `sum_allCoords_trace_blocks`
(`W^d · (W^{-d})² = W^{-d}`).

The final statement is `sum_coordinateSecondWordDeriv_allCuts`: for every signed word, the
variance-weighted trace of the second coordinate derivative of the word is the sum over all
same-edge cuts and all pairs of distinct edges of cut-loop products, each family with
coefficient `2uW^d`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace RBM.Gauss

open Matrix

/-! ## 1. A two-edge cross term in the second loop derivative -/

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
factors once is the cut-chain trace, before covariance summation. -/
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

/-- Covariance summation of one ordered, unscaled two-edge cross term. -/
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
both derivatives hit one edge are separate. -/
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
the signed Green factors in `coordinateSecondWordDeriv`. -/
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

/-! ## 2. A single-edge term of the second loop derivative -/

section Sec2

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- Coordinate contraction in block notation, with the physical-site
Gaussian covariance and its exact `W^d` normalization. -/
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

end Sec2

/-! ## 3. A same-edge second derivative inside a finite matrix word -/

section Sec3

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- A single second Green derivative at an arbitrary edge of a matrix word.
The surrounding prefix and suffix remain explicit matrices. -/
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
into the first block trace. -/
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

/-! ## 4. A same-edge contraction at a specified edge of a finite loop -/

section Sec4

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

section Sec4Aux

variable {d L W} {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}

omit [NeZero W] in
/-- `gloopProd` of a nonempty word is `G_s E_b` times the `gloopProd` of the rest (`rfl`). -/
private theorem secondLoop_gloopProd_cons (s : Bool) (b : Zd d L)
    (σ : List Bool) (a : List (Zd d L)) :
    gloopProd d L W H z ⟨s :: σ, b :: a⟩ =
      Gres H z s * Eblk d L W b * gloopProd d L W H z ⟨σ, a⟩ := rfl

omit [NeZero W] in
/-- `loopL` is the trace of `gloopProd` (by `rfl`). -/
private theorem secondLoop_loopL_eq (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W H z I = Matrix.trace (gloopProd d L W H z I) := rfl

omit [NeZero W] in
private theorem secondLoop_gloopProd_nil : gloopProd d L W H z ⟨[], []⟩ = 1 := rfl

omit [NeZero W] in
/-- `gloopProd` of a concatenation is the product of the two `gloopProd`s, for a first part
with matching lengths. -/
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
prefix, and a repeated copy of the differentiated signed Green edge. -/
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
/-- The second block trace is the one-edge loop. -/
theorem trace_sameEdge_oneLoop
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (z : ℂ) (s : Bool) (q : Zd d L) :
    Matrix.trace (Gres H z s * Eblk d L W q) =
      loopL d L W H z ⟨[s], [q]⟩ := by
  simp only [secondLoop_loopL_eq, secondLoop_gloopProd_cons, secondLoop_gloopProd_nil,
    Matrix.mul_one]

/-- The same-edge variance contraction at the specified split of a finite
loop word. No sum over edge positions or expectation is taken. -/
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

/-! ## 5. Enumerating one selected edge of a finite word -/

section Sec5

/-- A chosen edge, with the word before and after it. -/
structure EdgeSplit (α : Type*) where
  before : List α
  selected : α
  after : List α

/-- Enumerate the edge at every position from left to right. -/
def edgeSplits {α : Type*} : List α → List (EdgeSplit α)
  | [] => []
  | x :: xs =>
      ⟨[], x, xs⟩ :: (edgeSplits xs).map
        (fun e => ⟨x :: e.before, e.selected, e.after⟩)

/-- Every enumerated split reconstructs the original word. -/
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

/-- The prefix lengths occur in exactly the order `0, ..., length - 1`. -/
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

end Sec5

/-! ## 6. Enumerating two ordered edges of a finite word -/

section Sec6

/-- Two selected edges with the three intervening word segments. -/
structure PairSplit (α : Type*) where
  before : List α
  first : α
  middle : List α
  second : α
  after : List α

/-- Choose the first edge, then choose the second edge in its suffix. -/
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

/-- Every enumerated pair reconstructs the original word. -/
theorem pairSplits_reconstruct {α : Type*} (l : List α)
    (p : PairSplit α) (hp : p ∈ pairSplits l) :
    p.before ++ p.first :: p.middle ++ p.second :: p.after = l := by
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_pairSplits_iff l p).mp hp
  have houter := edgeSplits_reconstruct l e he
  have hinner := edgeSplits_reconstruct e.after f hf
  simpa only [List.append_assoc, List.cons_append] using
    (hinner ▸ houter)

end Sec6

/-! ## 7. The first coordinate derivative as a sum over edge positions -/

section Sec7

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The undifferentiated matrix word on a list of signed block edges. -/
noncomputable def coordinateWordProduct (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2 * M) 1

/-- Differentiate precisely the chosen edge of a split word. -/
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
selected edges. Prefix and suffix matrix factors remain in word order. -/
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

/-! ## 8. The second coordinate derivative as finite position sums -/

section Sec8

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The second derivative applied twice to the selected Green edge. -/
noncomputable def coordinateSameEdgeTerm (u : ℝ) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (e : EdgeSplit (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  coordinateWordProduct d L W u ω z e.before *
    (gsigCoordinateSecondDeriv d L W u ω γ z e.selected.1 * Eblk d L W e.selected.2) *
    coordinateWordProduct d L W u ω z e.after

/-- First derivatives applied once to each of two ordered selected edges. -/
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

/-- Sum of all same-edge second-derivative terms. -/
noncomputable def coordinateSameEdgeSum (u : ℝ) (ω : Ω d L W)
    (γ : CoordF d L W) (z : ℂ) (l : List (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  ((edgeSplits l).map (coordinateSameEdgeTerm d L W u ω γ z)).sum

/-- Sum over each unordered pair of distinct positions, keeping the
original left-to-right matrix order. -/
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
distinct edges. The `PairSplit` enumerator lists each pair only once. -/
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

/-! ## 9. Finite trace and Gaussian-coordinate sums of the second word derivative -/

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
traced second product rule. No loop-cut or expectation identity is used. -/
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

/-! ## 10. Matching position-split word segments with loop products -/

section Sec10

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The sign and block-label projections of a signed word segment. -/
def segmentLoopIdx (l : List (Bool × Zd d L)) : Loop.LoopIdx (Zd d L) :=
  ⟨l.map Prod.fst, l.map Prod.snd⟩

omit [NeZero L] [NeZero W] in
/-- A projected word segment always has matching sign and block lengths. -/
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

/-- The finite matrix word on a segment equals its loop-index product. -/
theorem coordinateWordProduct_eq_gloopProd
    (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    coordinateWordProduct d L W u ω z l =
      gloopProd d L W (HflowBlock d L W u ω) z (segmentLoopIdx d L l) := by
  unfold coordinateWordProduct gloopProd segmentLoopIdx
  rw [zip_segment_projections d L l]

end Sec10

/-! ## 11. The same-edge cut formula at one enumerated loop position -/

section Sec11

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- At any chosen edge, the weighted second-coordinate insertion is the
same-edge cut-loop double sum. The two projected segments are well formed. -/
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

end Sec11

/-! ## 12. The two-edge cut formula at one enumerated pair of loop positions -/

section Sec12

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- At any chosen ordered pair of edges, the Gaussian variance contraction
is the corresponding left/right cut-loop double sum. -/
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

end Sec12

/-! ## 13. All finite cut terms in the variance-weighted second loop derivative -/

section Sec13

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The cut-loop product attached to one same-edge position, without its
common coefficient `2uW^d`. -/
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
without its common coefficient `2uW^d` from the two derivative orders. -/
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
Both same-edge and distinct-edge families have coefficient `2uW^d`. -/
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

end Sec13

end RBM.Gauss
