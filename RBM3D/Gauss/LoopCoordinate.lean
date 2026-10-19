/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.FlowCalculus

/-!
# One-coordinate derivatives of the `G`-loops

In the vocabulary of `RBM3D.Gauss.FineModel` and `RBM3D.Gauss.FlowCalculus`: `Gres H z σ` is the
resolvent of either sign, `loopL` the loop, `Vtx d L W` the block-product index, `CoordF d L W`
the coordinates and `PF d L W g` the one-size law, which carries the real parameter `g` of
`svarF` (so the integrability statement takes `g` as an argument).

Everything is deterministic at a fixed sample: changing one real Gaussian coordinate `ω c` to `t`
moves the block matrix affinely, `H(ω[c := t]) = H(ω) + √u (t - ω c) B_c`, hence
`d/dt G = -G B G`, `d²/dt² G = 2 G B G B G`, and the loop derivatives are the finite Leibniz sums.
The only dimension-dependent statements are the bound
`‖tr D_k‖ ≤ (L W)^d · (word bound with `W^{-d}` per edge)` and the index types.
-/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace RBM.Gauss

section Coordinate

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- A Gaussian coordinate direction in block coordinates. -/
noncomputable def coordinateBlock (c : CoordF d L W) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  blockMat d L W (coordinateMatrix d L W c)

/-- Exact affine dependence of the reindexed matrix on one sample coordinate. -/
theorem HflowBlock_update (u : ℝ) (ω : Ω d L W) (c : CoordF d L W) (t : ℝ) :
    HflowBlock d L W u (Function.update ω c t) =
      HflowBlock d L W u ω + (Real.sqrt u * (t - ω c)) • coordinateBlock d L W c := by
  ext i j
  simp only [HflowBlock, blockMat, coordinateBlock, Hflow_eq_realSmul, Xmat_update,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, smul_add, smul_smul]

/-- The sample-coordinate derivative of the reindexed matrix. -/
theorem hasDerivAt_HflowBlock_update (u : ℝ) (ω : Ω d L W) (c : CoordF d L W) :
    HasDerivAt (fun t : ℝ => HflowBlock d L W u (Function.update ω c t))
      (Real.sqrt u • coordinateBlock d L W c) (ω c) := by
  have hscalar : HasDerivAt (fun t : ℝ => Real.sqrt u * (t - ω c))
      (Real.sqrt u) (ω c) := by
    simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul (Real.sqrt u)
  have hline := (hscalar.smul_const (coordinateBlock d L W c)).const_add
    (HflowBlock d L W u ω)
  exact hline.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => HflowBlock_update d L W u ω c t)

/-- The exact directional resolvent derivative for one real Gaussian coordinate. -/
theorem hasDerivAt_green_HflowBlock_update (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt
      (fun t : ℝ => Gres (HflowBlock d L W u (Function.update ω c t)) z true)
      (let G := Gres (HflowBlock d L W u ω) z true;
       -(G * (Real.sqrt u • coordinateBlock d L W c) * G)) (ω c) := by
  have h := hasDerivAt_green_moving
    (hasDerivAt_HflowBlock_update d L W u ω c)
    (hasDerivAt_const (ω c) z)
    (by simpa only [Function.update_eq_self] using HflowBlock_isHermitian d L W u ω)
    hz
  simpa only [Function.update_eq_self, zero_smul, sub_zero] using h

/-- The derivative of either signed Green factor in one coordinate. -/
noncomputable def gsigCoordinateDeriv (u : ℝ) (ω : Ω d L W) (c : CoordF d L W)
    (z : ℂ) (σ : Bool) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  let G := Gres (HflowBlock d L W u ω) z σ;
  -(G * (Real.sqrt u • coordinateBlock d L W c) * G)

/-- The derivative of one signed Green factor with respect to the coordinate `ω c`. -/
theorem hasDerivAt_Gsig_HflowBlock_update (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    HasDerivAt
      (fun t : ℝ => Gres (HflowBlock d L W u (Function.update ω c t)) z σ)
      (gsigCoordinateDeriv d L W u ω c z σ) (ω c) := by
  cases σ with
  | true =>
      simpa only [gsigCoordinateDeriv] using
        hasDerivAt_green_HflowBlock_update d L W u ω c hz
  | false =>
      have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
      have hGf : ∀ H : Matrix (Vtx d L W) (Vtx d L W) ℂ,
          Gres H z false = Gres H ((starRingEnd ℂ) z) true := fun H => by simp [Gres]
      simpa only [gsigCoordinateDeriv, hGf] using
        hasDerivAt_green_HflowBlock_update d L W u ω c hz'

/-- Recursive product rule for the finite signed word. -/
noncomputable def coordinateWordDeriv (u : ℝ) (ω : Ω d L W) (c : CoordF d L W)
    (z : ℂ) : List (Bool × Zd d L) → Matrix (Vtx d L W) (Vtx d L W) ℂ
  | [] => 0
  | p :: l =>
      (gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2) *
        l.foldr (fun q M => Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1 +
      (Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2) *
        coordinateWordDeriv u ω c z l

/-- The derivative of a finite signed Green and block-insertion word with respect to one real
coordinate (the recursive Leibniz derivative `coordinateWordDeriv`). -/
theorem hasDerivAt_coordinateWord (u : ℝ) (ω : Ω d L W) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Zd d L)) :
    HasDerivAt
      (fun t : ℝ => l.foldr (fun p M =>
        Gres (HflowBlock d L W u (Function.update ω c t)) z p.1 * Eblk d L W p.2 * M) 1)
      (coordinateWordDeriv d L W u ω c z l) (ω c) := by
  induction l with
  | nil =>
      simpa only [List.foldr_nil, coordinateWordDeriv] using
        hasDerivAt_const (ω c) (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have hhead := (hasDerivAt_Gsig_HflowBlock_update d L W u ω c hz p.1).mul_const
        (Eblk d L W p.2)
      have h := hhead.mul ih
      have hfun :
          (fun t : ℝ => Gres (HflowBlock d L W u (Function.update ω c t)) z p.1 *
            Eblk d L W p.2) *
            (fun t : ℝ => l.foldr (fun q M =>
              Gres (HflowBlock d L W u (Function.update ω c t)) z q.1 * Eblk d L W q.2 * M) 1) =
          (fun t : ℝ => Gres (HflowBlock d L W u (Function.update ω c t)) z p.1 *
            Eblk d L W p.2 * l.foldr (fun q M =>
              Gres (HflowBlock d L W u (Function.update ω c t)) z q.1 * Eblk d L W q.2 * M)
              1) := by
        funext t
        rfl
      rw [hfun] at h
      have hgoalFun :
          (fun t : ℝ => (p :: l).foldr (fun q M =>
            Gres (HflowBlock d L W u (Function.update ω c t)) z q.1 *
              Eblk d L W q.2 * M) 1) =
          (fun t : ℝ => Gres (HflowBlock d L W u (Function.update ω c t)) z p.1 *
            Eblk d L W p.2 * l.foldr (fun q M =>
              Gres (HflowBlock d L W u (Function.update ω c t)) z q.1 *
                Eblk d L W q.2 * M) 1) := by
        funext t
        rfl
      rw [hgoalFun]
      rw [coordinateWordDeriv]
      simp only [Function.update_eq_self] at h
      exact h

/-- Coordinate derivative of the finite loop matrix product. -/
theorem hasDerivAt_gloopProd_update (u : ℝ) (ω : Ω d L W) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (_hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => gloopProd d L W (HflowBlock d L W u (Function.update ω c t)) z I)
      (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a)) (ω c) :=
  hasDerivAt_coordinateWord d L W u ω c hz (I.σ.zip I.a)

/-- Coordinate derivative of the complete finite loop. -/
theorem hasDerivAt_gloop_update (u : ℝ) (ω : Ω d L W) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => loopL d L W (HflowBlock d L W u (Function.update ω c t)) z I)
      (Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))) (ω c) := by
  set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt (ω c)
    (hasDerivAt_gloopProd_update d L W u ω c hz I hwf)
  simpa only [hT, Function.comp_def, loopL, gloopProd] using h

/-! ## 2. The second derivative of the Green matrix and of the loops -/

/-- The derivative of the first-coordinate derivative `-G B G`. -/
theorem hasDerivAt_greenCoordinateDerivative (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt
      (fun t : ℝ =>
        let G := Gres (HflowBlock d L W u (Function.update ω c t)) z true;
        let B := Real.sqrt u • coordinateBlock d L W c;
        -(G * B * G))
      (let G := Gres (HflowBlock d L W u ω) z true;
       let B := Real.sqrt u • coordinateBlock d L W c;
       (2 : ℝ) • (G * B * G * B * G)) (ω c) := by
  let B : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    Real.sqrt u • coordinateBlock d L W c
  let G : ℝ → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun t => Gres (HflowBlock d L W u (Function.update ω c t)) z true
  have hbase : G (ω c) = Gres (HflowBlock d L W u ω) z true := by
    simp [G]
  have hG : HasDerivAt G (-(G (ω c) * B * G (ω c))) (ω c) := by
    simpa only [G, B, hbase] using
      hasDerivAt_green_HflowBlock_update d L W u ω c hz
  have hprod := ((hG.mul_const B).mul hG).neg
  have hval :
      -((-(G (ω c) * B * G (ω c)) * B) * G (ω c) +
        (G (ω c) * B) * (-(G (ω c) * B * G (ω c)))) =
      (2 : ℝ) • (G (ω c) * B * G (ω c) * B * G (ω c)) := by
    rw [two_smul]
    noncomm_ring
  rw [hval] at hprod
  have hfun :
      -((fun t : ℝ => G t * B) * G) =
        (fun t : ℝ => -(G t * B * G t)) := by
    funext t
    rfl
  rw [hfun] at hprod
  simpa only [G, B, hbase] using hprod

/-- Second derivative of one signed Green factor in a real Gaussian coordinate. -/
noncomputable def gsigCoordinateSecondDeriv (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) (z : ℂ) (σ : Bool) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  let G := Gres (HflowBlock d L W u ω) z σ
  let B := Real.sqrt u • coordinateBlock d L W c
  (2 : ℝ) • (G * B * G * B * G)

/-- The derivative along the coordinate of the coordinate derivative of one signed Green factor
is `gsigCoordinateSecondDeriv`. -/
theorem hasDerivAt_gsigCoordinateDeriv_update (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    HasDerivAt
      (fun t : ℝ => gsigCoordinateDeriv d L W u (Function.update ω c t) c z σ)
      (gsigCoordinateSecondDeriv d L W u ω c z σ) (ω c) := by
  cases σ with
  | true =>
      simpa only [gsigCoordinateDeriv, gsigCoordinateSecondDeriv] using
        hasDerivAt_greenCoordinateDerivative d L W u ω c hz
  | false =>
      have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
      have hGf : ∀ H : Matrix (Vtx d L W) (Vtx d L W) ℂ,
          Gres H z false = Gres H ((starRingEnd ℂ) z) true := fun H => by simp [Gres]
      simpa only [gsigCoordinateDeriv, gsigCoordinateSecondDeriv, hGf] using
        hasDerivAt_greenCoordinateDerivative d L W u ω c hz'

/-- Recursive second product rule, including both mixed terms. -/
noncomputable def coordinateSecondWordDeriv (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) (z : ℂ) : List (Bool × Zd d L) →
      Matrix (Vtx d L W) (Vtx d L W) ℂ
  | [] => 0
  | p :: l =>
      ((gsigCoordinateSecondDeriv d L W u ω c z p.1 * Eblk d L W p.2) *
          l.foldr (fun q M => Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1 +
        (gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2) *
          coordinateWordDeriv d L W u ω c z l) +
      ((gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2) *
          coordinateWordDeriv d L W u ω c z l +
        (Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2) *
          coordinateSecondWordDeriv u ω c z l)

/-- The same for a word: the derivative along the coordinate of `coordinateWordDeriv` is
`coordinateSecondWordDeriv`. -/
theorem hasDerivAt_coordinateWordDeriv (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × Zd d L)) :
    HasDerivAt
      (fun t : ℝ => coordinateWordDeriv d L W u (Function.update ω c t) c z l)
      (coordinateSecondWordDeriv d L W u ω c z l) (ω c) := by
  induction l with
  | nil =>
      simpa only [coordinateWordDeriv, coordinateSecondWordDeriv] using
        hasDerivAt_const (ω c) (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have hDhead :=
        (hasDerivAt_gsigCoordinateDeriv_update d L W u ω c hz p.1).mul_const
          (Eblk d L W p.2)
      have hHead :=
        (hasDerivAt_Gsig_HflowBlock_update d L W u ω c hz p.1).mul_const
          (Eblk d L W p.2)
      have hTail := hasDerivAt_coordinateWord d L W u ω c hz l
      have h := (hDhead.mul hTail).add (hHead.mul ih)
      have hfun :
          (fun t : ℝ => gsigCoordinateDeriv d L W u (Function.update ω c t) c z p.1 *
            Eblk d L W p.2) *
              (fun t : ℝ => l.foldr (fun q M =>
                Gres (HflowBlock d L W u (Function.update ω c t)) z q.1 *
                  Eblk d L W q.2 * M) 1) +
          (fun t : ℝ => Gres (HflowBlock d L W u (Function.update ω c t)) z p.1 *
            Eblk d L W p.2) *
              (fun t : ℝ => coordinateWordDeriv d L W u (Function.update ω c t) c z l) =
          (fun t : ℝ => coordinateWordDeriv d L W u (Function.update ω c t) c z (p :: l)) := by
        funext t
        rfl
      rw [hfun] at h
      simp only [Function.update_eq_self] at h
      rw [coordinateSecondWordDeriv]
      exact h

/-- The second coordinate derivative of the traced finite loop. -/
theorem hasDerivAt_deriv_gloop_update (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ =>
        loopL d L W (HflowBlock d L W u (Function.update ω c s)) z I) t)
      (Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a)))
      (ω c) := by
  let f : ℝ → ℂ := fun s =>
    loopL d L W (HflowBlock d L W u (Function.update ω c s)) z I
  have hfirst (t : ℝ) :
      HasDerivAt f
        (Matrix.trace (coordinateWordDeriv d L W u (Function.update ω c t) c z
          (I.σ.zip I.a))) t := by
    have h := hasDerivAt_gloop_update d L W u (Function.update ω c t) c hz I hwf
    have hpoint : (Function.update ω c t) c = t := by simp
    rw [hpoint] at h
    have hpath : (fun s : ℝ => loopL d L W
        (HflowBlock d L W u (Function.update (Function.update ω c t) c s)) z I) = f := by
      funext s
      simp [f, Function.update_idem]
    rw [hpath] at h
    exact h
  have hderiv : (fun t : ℝ => deriv f t) =
      (fun t : ℝ => Matrix.trace
        (coordinateWordDeriv d L W u (Function.update ω c t) c z (I.σ.zip I.a))) := by
    funext t
    exact (hfirst t).deriv
  set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt (ω c)
    (hasDerivAt_coordinateWordDeriv d L W u ω c hz (I.σ.zip I.a))
  change HasDerivAt (fun t : ℝ => deriv f t) _ (ω c)
  rw [hderiv]
  simpa only [hT, Function.comp_def] using h

/-! ## 3. Sample-uniform bounds for the coordinate derivatives -/

/-- `η⁻¹ W^{-d}`, the bound of one `G E` block. -/
private noncomputable def coordA (η : ℝ) : ℝ :=
  η⁻¹ * ((W : ℝ) ^ d)⁻¹

/-- `η⁻¹ ‖√u B_c‖ η⁻¹ W^{-d}`, the bound of one first-derivative factor `G (√u B_c) G E`. -/
private noncomputable def coordD (u η : ℝ) (c : CoordF d L W) : ℝ :=
  (η⁻¹ * ‖Real.sqrt u • coordinateBlock d L W c‖ * η⁻¹) *
    ((W : ℝ) ^ d)⁻¹

/-- `2 η⁻¹ ‖√u B_c‖ η⁻¹ ‖√u B_c‖ η⁻¹ W^{-d}`, the bound of one second-derivative factor. -/
private noncomputable def coordS (u η : ℝ) (c : CoordF d L W) : ℝ :=
  2 * ((η⁻¹ * ‖Real.sqrt u • coordinateBlock d L W c‖ * η⁻¹ *
      ‖Real.sqrt u • coordinateBlock d L W c‖ * η⁻¹) *
    ((W : ℝ) ^ d)⁻¹)

/-- Explicit finite-recursion majorant for the first derivative of a word. -/
noncomputable def coordinateFirstWordBound (u η : ℝ) (c : CoordF d L W) : ℕ → ℝ
  | 0 => 0
  | n + 1 => coordD d L W u η c * (coordA d W η) ^ n +
      coordA d W η * coordinateFirstWordBound u η c n

/-- Explicit finite-recursion majorant for the second derivative of a word. -/
noncomputable def coordinateSecondWordBound (u η : ℝ) (c : CoordF d L W) : ℕ → ℝ
  | 0 => 0
  | n + 1 => coordS d L W u η c * (coordA d W η) ^ n +
      2 * coordD d L W u η c * coordinateFirstWordBound d L W u η c n +
      coordA d W η * coordinateSecondWordBound u η c n

omit [NeZero L] [NeZero W] in
private theorem coordA_nonneg {η : ℝ} (hη : 0 < η) :
    0 ≤ coordA d W η := by unfold coordA; positivity

private theorem coordD_nonneg {η u : ℝ} (hη : 0 < η) (c : CoordF d L W) :
    0 ≤ coordD d L W u η c := by unfold coordD; positivity

private theorem coordS_nonneg {η u : ℝ} (hη : 0 < η) (c : CoordF d L W) :
    0 ≤ coordS d L W u η c := by unfold coordS; positivity

private theorem firstBound_nonneg {η u : ℝ} (hη : 0 < η) (c : CoordF d L W)
    (n : ℕ) : 0 ≤ coordinateFirstWordBound d L W u η c n := by
  induction n with
  | zero => simp [coordinateFirstWordBound]
  | succ n ih =>
      rw [coordinateFirstWordBound]
      exact add_nonneg
        (mul_nonneg (coordD_nonneg d L W hη c) (pow_nonneg (coordA_nonneg d W hη) _))
        (mul_nonneg (coordA_nonneg d W hη) ih)

private theorem secondBound_nonneg {η u : ℝ} (hη : 0 < η) (c : CoordF d L W)
    (n : ℕ) : 0 ≤ coordinateSecondWordBound d L W u η c n := by
  induction n with
  | zero => simp [coordinateSecondWordBound]
  | succ n ih =>
      rw [coordinateSecondWordBound]
      exact add_nonneg
        (add_nonneg
          (mul_nonneg (coordS_nonneg d L W hη c) (pow_nonneg (coordA_nonneg d W hη) _))
          (mul_nonneg (mul_nonneg (by norm_num) (coordD_nonneg d L W hη c))
            (firstBound_nonneg d L W hη c n)))
        (mul_nonneg (coordA_nonneg d W hη) ih)

private theorem norm_coordinate_head_le {η u : ℝ} (hη : 0 < η)
    (ω : Ω d L W) (c : CoordF d L W) {z : ℂ} (hz : η ≤ |z.im|)
    (p : Bool × Zd d L) :
    ‖Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2‖ ≤ coordA d W η ∧
    ‖gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2‖ ≤
      coordD d L W u η c ∧
    ‖gsigCoordinateSecondDeriv d L W u ω c z p.1 * Eblk d L W p.2‖ ≤
      coordS d L W u η c := by
  let G := Gres (HflowBlock d L W u ω) z p.1
  let B := Real.sqrt u • coordinateBlock d L W c
  let E := Eblk d L W p.2
  have hG : ‖G‖ ≤ η⁻¹ :=
    norm_Gsig_le_inv_eta (HflowBlock_isHermitian d L W u ω) hη hz p.1
  have hE : ‖E‖ ≤ ((W : ℝ) ^ d)⁻¹ := norm_Eblk_le_inv_W_sq d L W p.2
  have hq : 0 ≤ η⁻¹ := by positivity
  have he : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  constructor
  · calc
      ‖G * E‖ ≤ ‖G‖ * ‖E‖ := norm_mul_le _ _
      _ ≤ η⁻¹ * (((W : ℝ) ^ d)⁻¹) := by gcongr
      _ = coordA d W η := rfl
  constructor
  · change ‖-(G * B * G) * E‖ ≤ coordD d L W u η c
    calc
      ‖-(G * B * G) * E‖ ≤ ‖-(G * B * G)‖ * ‖E‖ := norm_mul_le _ _
      _ = ‖G * B * G‖ * ‖E‖ := by rw [norm_neg]
      _ ≤ (‖G‖ * ‖B‖ * ‖G‖) * ‖E‖ := by
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ (η⁻¹ * ‖B‖ * η⁻¹) * (((W : ℝ) ^ d)⁻¹) := by gcongr
      _ = coordD d L W u η c := rfl
  · change ‖((2 : ℝ) • (G * B * G * B * G)) * E‖ ≤ coordS d L W u η c
    calc
      ‖((2 : ℝ) • (G * B * G * B * G)) * E‖
          ≤ ‖(2 : ℝ) • (G * B * G * B * G)‖ * ‖E‖ := norm_mul_le _ _
      _ = 2 * ‖G * B * G * B * G‖ * ‖E‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (‖G‖ * ‖B‖ * ‖G‖ * ‖B‖ * ‖G‖) * ‖E‖ := by
        gcongr
        exact (norm_mul_le _ _).trans (by
          gcongr
          exact (norm_mul_le _ _).trans (by
            gcongr
            exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)))
      _ ≤ 2 * (η⁻¹ * ‖B‖ * η⁻¹ * ‖B‖ * η⁻¹) *
            (((W : ℝ) ^ d)⁻¹) := by gcongr
      _ = coordS d L W u η c := by unfold coordS; ring

/-- Uniform first and second derivative bounds for every Gaussian sample. -/
theorem norm_coordinateWordDeriv_le {η u : ℝ} (hη : 0 < η)
    (c : CoordF d L W) {z : ℂ} (hz : η ≤ |z.im|)
    (l : List (Bool × Zd d L)) (ω : Ω d L W) :
    ‖coordinateWordDeriv d L W u ω c z l‖ ≤
        coordinateFirstWordBound d L W u η c l.length ∧
    ‖coordinateSecondWordDeriv d L W u ω c z l‖ ≤
        coordinateSecondWordBound d L W u η c l.length := by
  induction l with
  | nil => simp [coordinateWordDeriv, coordinateSecondWordDeriv,
      coordinateFirstWordBound, coordinateSecondWordBound]
  | cons p l ih =>
      obtain ⟨hA, hD, hS⟩ := norm_coordinate_head_le d L W (u := u) hη ω c hz p
      obtain ⟨hF, hT⟩ := ih
      have hword := norm_foldr_Gsig_Eblk_le d L W
        (HflowBlock_isHermitian d L W u ω) hη hz l
      have hword' :
          ‖l.foldr (fun q M => Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1‖ ≤
            coordA d W η ^ l.length := by
        simpa only [coordA] using hword
      have hA0 := coordA_nonneg d W hη
      have hD0 := coordD_nonneg d L W (u := u) hη c
      have hS0 := coordS_nonneg d L W (u := u) hη c
      have hF0 := firstBound_nonneg d L W (u := u) hη c l.length
      have hT0 := secondBound_nonneg d L W (u := u) hη c l.length
      have hp0 : 0 ≤ (coordA d W η) ^ l.length := pow_nonneg hA0 _
      constructor
      · rw [coordinateWordDeriv, List.length_cons, coordinateFirstWordBound]
        calc
          ‖_ + _‖ ≤ ‖gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2 *
              l.foldr (fun q M => Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1‖ +
              ‖(Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2) *
                coordinateWordDeriv d L W u ω c z l‖ := norm_add_le _ _
          _ ≤ ‖gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2‖ *
                ‖l.foldr (fun q M =>
                  Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1‖ +
              ‖Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2‖ *
                ‖coordinateWordDeriv d L W u ω c z l‖ :=
                  add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ coordD d L W u η c * coordA d W η ^ l.length +
              coordA d W η * coordinateFirstWordBound d L W u η c l.length := by gcongr
      · rw [coordinateSecondWordDeriv, List.length_cons, coordinateSecondWordBound]
        have hSterm :
            ‖gsigCoordinateSecondDeriv d L W u ω c z p.1 * Eblk d L W p.2 *
                l.foldr (fun q M =>
                  Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1‖ ≤
              coordS d L W u η c * coordA d W η ^ l.length := by
          calc
            _ ≤ ‖gsigCoordinateSecondDeriv d L W u ω c z p.1 * Eblk d L W p.2‖ *
                ‖l.foldr (fun q M =>
                  Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1‖ :=
                  norm_mul_le _ _
            _ ≤ _ := by gcongr
        have hDterm :
            ‖(gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2) *
                coordinateWordDeriv d L W u ω c z l‖ ≤
              coordD d L W u η c * coordinateFirstWordBound d L W u η c l.length := by
          calc
            _ ≤ ‖gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2‖ *
                ‖coordinateWordDeriv d L W u ω c z l‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr
        have hAterm :
            ‖(Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2) *
                coordinateSecondWordDeriv d L W u ω c z l‖ ≤
              coordA d W η * coordinateSecondWordBound d L W u η c l.length := by
          calc
            _ ≤ ‖Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2‖ *
                ‖coordinateSecondWordDeriv d L W u ω c z l‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr
        calc
          ‖(_ + _) + (_ + _)‖ ≤
              (‖gsigCoordinateSecondDeriv d L W u ω c z p.1 * Eblk d L W p.2 *
                  l.foldr (fun q M =>
                    Gres (HflowBlock d L W u ω) z q.1 * Eblk d L W q.2 * M) 1‖ +
                ‖(gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2) *
                  coordinateWordDeriv d L W u ω c z l‖) +
              (‖(gsigCoordinateDeriv d L W u ω c z p.1 * Eblk d L W p.2) *
                  coordinateWordDeriv d L W u ω c z l‖ +
                ‖(Gres (HflowBlock d L W u ω) z p.1 * Eblk d L W p.2) *
                  coordinateSecondWordDeriv d L W u ω c z l‖) := by
                    apply (norm_add_le _ _).trans
                    exact add_le_add (norm_add_le _ _) (norm_add_le _ _)
          _ ≤ (coordS d L W u η c * coordA d W η ^ l.length +
                coordD d L W u η c * coordinateFirstWordBound d L W u η c l.length) +
              (coordD d L W u η c * coordinateFirstWordBound d L W u η c l.length +
                coordA d W η * coordinateSecondWordBound d L W u η c l.length) := by
                  exact add_le_add (add_le_add hSterm hDterm)
                    (add_le_add hDterm hAterm)
          _ = coordS d L W u η c * coordA d W η ^ l.length +
              2 * coordD d L W u η c * coordinateFirstWordBound d L W u η c l.length +
              coordA d W η * coordinateSecondWordBound d L W u η c l.length := by ring

/-- A sample-independent envelope for the two derivatives of a traced loop: the trace costs the
volume factor `(L W)^d`, each edge `W^{-d}` (inside the word bounds). -/
theorem norm_gloop_coordinate_derivatives_le {η u : ℝ} (hη : 0 < η)
    (c : CoordF d L W) {z : ℂ} (hz : η ≤ |z.im|)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) (ω : Ω d L W) :
    ‖Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))‖ ≤
        (((L * W) ^ d : ℕ) : ℝ) *
          coordinateFirstWordBound d L W u η c I.a.length ∧
    ‖Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))‖ ≤
        (((L * W) ^ d : ℕ) : ℝ) *
          coordinateSecondWordBound d L W u η c I.a.length := by
  obtain ⟨hF, hS⟩ := norm_coordinateWordDeriv_le d L W hη c hz (I.σ.zip I.a) ω
  have hlen : (I.σ.zip I.a).length = I.a.length := by
    rw [List.length_zip]
    simp only [Loop.LoopIdx.WF] at hwf
    rw [hwf, min_self]
  constructor
  · calc
      ‖Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))‖ ≤
          (Fintype.card (Vtx d L W) : ℝ) *
            ‖coordinateWordDeriv d L W u ω c z (I.σ.zip I.a)‖ :=
              norm_matrix_trace_le_card_mul _
      _ ≤ (Fintype.card (Vtx d L W) : ℝ) *
          coordinateFirstWordBound d L W u η c (I.σ.zip I.a).length := by
            exact mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)
      _ = _ := by rw [card_BlockIndex, hlen]
  · calc
      ‖Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))‖ ≤
          (Fintype.card (Vtx d L W) : ℝ) *
            ‖coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a)‖ :=
              norm_matrix_trace_le_card_mul _
      _ ≤ (Fintype.card (Vtx d L W) : ℝ) *
          coordinateSecondWordBound d L W u η c (I.σ.zip I.a).length := by
            exact mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
      _ = _ := by rw [card_BlockIndex, hlen]

/-! ## 4. Measurability and integrability of the coordinate derivatives -/

/-- The first signed-factor coordinate derivative is sample-continuous. -/
theorem continuous_gsigCoordinateDeriv_sample (u : ℝ) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun ω : Ω d L W => gsigCoordinateDeriv d L W u ω c z σ := by
  have hG := continuous_Gsig_HflowBlock_sample d L W u hz σ
  change Continuous fun ω : Ω d L W =>
    -(Gres (HflowBlock d L W u ω) z σ *
      (Real.sqrt u • coordinateBlock d L W c) *
        Gres (HflowBlock d L W u ω) z σ)
  exact ((hG.mul continuous_const).mul hG).neg

/-- The second signed-factor coordinate derivative is sample-continuous. -/
theorem continuous_gsigCoordinateSecondDeriv_sample (u : ℝ) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun ω : Ω d L W => gsigCoordinateSecondDeriv d L W u ω c z σ := by
  have hG := continuous_Gsig_HflowBlock_sample d L W u hz σ
  change Continuous fun ω : Ω d L W =>
    (2 : ℝ) • (Gres (HflowBlock d L W u ω) z σ *
      (Real.sqrt u • coordinateBlock d L W c) *
      Gres (HflowBlock d L W u ω) z σ *
      (Real.sqrt u • coordinateBlock d L W c) *
      Gres (HflowBlock d L W u ω) z σ)
  exact (continuous_const : Continuous fun _ : Ω d L W => (2 : ℝ)).smul
    ((((hG.mul continuous_const).mul hG).mul continuous_const).mul hG)

/-- The recursive first word derivative is sample-continuous. -/
theorem continuous_coordinateWordDeriv_sample (u : ℝ) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Zd d L)) :
    Continuous fun ω : Ω d L W => coordinateWordDeriv d L W u ω c z l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact (((continuous_gsigCoordinateDeriv_sample d L W u c hz p.1).mul
        continuous_const).mul (continuous_foldr_HflowBlock_sample d L W u hz l)).add
        (((continuous_Gsig_HflowBlock_sample d L W u hz p.1).mul
          continuous_const).mul ih)

/-- The recursive second word derivative is sample-continuous. -/
theorem continuous_coordinateSecondWordDeriv_sample (u : ℝ) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Zd d L)) :
    Continuous fun ω : Ω d L W => coordinateSecondWordDeriv d L W u ω c z l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      have hD := continuous_coordinateWordDeriv_sample d L W u c hz l
      have hG := continuous_Gsig_HflowBlock_sample d L W u hz p.1
      have hDsig := continuous_gsigCoordinateDeriv_sample d L W u c hz p.1
      have hSsig := continuous_gsigCoordinateSecondDeriv_sample d L W u c hz p.1
      exact (((hSsig.mul continuous_const).mul
        (continuous_foldr_HflowBlock_sample d L W u hz l)).add
        ((hDsig.mul continuous_const).mul hD)).add
        (((hDsig.mul continuous_const).mul hD).add
        ((hG.mul continuous_const).mul ih))

/-- Both traced coordinate-derivative observables are measurable. -/
theorem measurable_gloop_coordinate_derivatives_sample (u : ℝ) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    Measurable (fun ω : Ω d L W =>
      Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))) ∧
    Measurable (fun ω : Ω d L W =>
      Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))) := by
  constructor
  · exact ((continuous_matrixTrace d L W).comp
      (continuous_coordinateWordDeriv_sample d L W u c hz _)).measurable
  · exact ((continuous_matrixTrace d L W).comp
      (continuous_coordinateSecondWordDeriv_sample d L W u c hz _)).measurable

/-- Both traced derivatives are integrable under the Gaussian product law `PF d L W g`; `g` is an
argument because the one-size law carries the parameter `g`. -/
theorem integrable_gloop_coordinate_derivatives (g u : ℝ) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    Integrable (fun ω : Ω d L W =>
      Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))) (PF d L W g) ∧
    Integrable (fun ω : Ω d L W =>
      Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a)))
      (PF d L W g) := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hm := measurable_gloop_coordinate_derivatives_sample d L W u c hz I
  constructor
  · exact Integrable.of_bound hm.1.aestronglyMeasurable
      ((((L * W) ^ d : ℕ) : ℝ) *
        coordinateFirstWordBound d L W u |z.im| c I.a.length)
      (Filter.Eventually.of_forall fun ω =>
        (norm_gloop_coordinate_derivatives_le d L W hη c le_rfl I hwf ω).1)
  · exact Integrable.of_bound hm.2.aestronglyMeasurable
      ((((L * W) ^ d : ℕ) : ℝ) *
        coordinateSecondWordBound d L W u |z.im| c I.a.length)
      (Filter.Eventually.of_forall fun ω =>
        (norm_gloop_coordinate_derivatives_le d L W hη c le_rfl I hwf ω).2)

end Coordinate

end RBM.Gauss
