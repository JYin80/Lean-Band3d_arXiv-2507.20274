/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.LoopGenN
import RBM3D.Path.DriftAlgebra
import RBM3D.Loop.KLTree
import RBM3D.Gauss.LoopGenerator

/-!
# S6-04 (T2218): the expected hierarchy at `n = 2` (the pin `STExpHier`)

Port of RBM2D `Evolution/MLExpHier.lean` at commit `c9a24cf` (cited `MLExpHier:<line>`; 731 lines
there) to `d ≥ 3`, onto the merged vocabulary (renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`).
Paper: arXiv:2507.20274, `(eq_L-Keee)` `paper/tex/3_5_Loop_Hierarchy.tex:73` at `n = 2` after taking
expectations, and `paper/tex/6_Step6_two_loop.tex:90`.

**Target** `stExpHier_holds d : STExpHier d` (the pin of `Induction/Step6Pins.lean:213`, unchanged).

## Route (as in RBM2D, `MLExpHier:11-30`)

1. Fixed size `(L, W, g)`.  A regularity class `expHier_Good b F` (continuous in the sample,
   continuous in the time on `[0, b]`, `b < 1`, uniformly bounded) is closed under sums, products and
   deterministic continuous coefficients, contains `𝓛_u(J)` at the flow sample, and gives
   integrability and continuity of `u ↦ 𝔼 F u` (dominated convergence).  Continuity on `[0,1)`
   *including* `u = 0` follows (`expHier_continuousOn_integral_loopL`); the drift identity holds on
   the open window only.
2. Samplewise bridge (`0 < u < 1`): the second Gaussian derivative of the flow sample in the coordinate
   `ω_c` carries the factor `u⁻¹` (`H_u = √u X`), so the one-step generator `genMat` at `H_u` is the
   merged samplewise cut expression (`expHier_genMat_eq_cuts`).
3. The `𝒦` ODE at `n = 2` for **every** sign pair `σ` (`expHier_Kloop_hasDerivAt`, from the merged
   `hasDerivAt_kTwo`; the merged `KpmODE` is `σ = (+,-)` only) and the matrix hierarchy at `k = 2` for
   every `σ` (`expHier_hierarchy_two`, from `hierarchyN_holds` and the private `k = 2` reductions of
   `Induction/HierarchyN.lean:81-140`, copied with the prefix `expHier_`).
4. Fixed-size expected hierarchy (`expHier_hasDerivAt_fixed`) and transfer from the one-size law
   `PF d L W g` to the common space `sz.seqP` (`seqP_map_slice`); the drift is the two integrals of
   `STExpDrift`.

Not needed: RBM2D's first conjunct `f_0 = 0` (`expErrT_zero`), which is not in the merged pin.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Gauss.Sizes

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Ind
open scoped NNReal ENNReal

/-! ## 1. The regularity class `expHier_Good` (`MLExpHier:55-160`) -/

section Good

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- A family `F u ω` is regular on `[0, b]`: continuous in the sample, continuous in the time, and
uniformly bounded (`MLExpHier:63`). -/
private structure expHier_Good (d L W : ℕ) [NeZero L] [NeZero W] (b : ℝ)
    (F : ℝ → Ω d L W → ℂ) : Prop where
  cont_ω : ∀ u ∈ Set.Icc (0 : ℝ) b, Continuous (F u)
  cont_u : ∀ ω : Ω d L W, ContinuousOn (fun u => F u ω) (Set.Icc 0 b)
  bdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc (0 : ℝ) b, ∀ ω : Ω d L W, ‖F u ω‖ ≤ B

private theorem expHier_Good_add {b : ℝ} {F G : ℝ → Ω d L W → ℂ}
    (hF : expHier_Good d L W b F) (hG : expHier_Good d L W b G) :
    expHier_Good d L W b (fun u ω => F u ω + G u ω) := by
  obtain ⟨B₁, hB₁, h₁⟩ := hF.bdd
  obtain ⟨B₂, hB₂, h₂⟩ := hG.bdd
  refine ⟨fun u hu => (hF.cont_ω u hu).add (hG.cont_ω u hu),
    fun ω => (hF.cont_u ω).add (hG.cont_u ω), B₁ + B₂, by positivity, fun u hu ω => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (h₁ u hu ω) (h₂ u hu ω))

private theorem expHier_Good_sub {b : ℝ} {F G : ℝ → Ω d L W → ℂ}
    (hF : expHier_Good d L W b F) (hG : expHier_Good d L W b G) :
    expHier_Good d L W b (fun u ω => F u ω - G u ω) := by
  obtain ⟨B₁, hB₁, h₁⟩ := hF.bdd
  obtain ⟨B₂, hB₂, h₂⟩ := hG.bdd
  refine ⟨fun u hu => (hF.cont_ω u hu).sub (hG.cont_ω u hu),
    fun ω => (hF.cont_u ω).sub (hG.cont_u ω), B₁ + B₂, by positivity, fun u hu ω => ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add (h₁ u hu ω) (h₂ u hu ω))

private theorem expHier_Good_mul {b : ℝ} {F G : ℝ → Ω d L W → ℂ}
    (hF : expHier_Good d L W b F) (hG : expHier_Good d L W b G) :
    expHier_Good d L W b (fun u ω => F u ω * G u ω) := by
  obtain ⟨B₁, hB₁, h₁⟩ := hF.bdd
  obtain ⟨B₂, hB₂, h₂⟩ := hG.bdd
  refine ⟨fun u hu => (hF.cont_ω u hu).mul (hG.cont_ω u hu),
    fun ω => (hF.cont_u ω).mul (hG.cont_u ω), B₁ * B₂, by positivity, fun u hu ω => ?_⟩
  exact (norm_mul_le _ _).trans
    (mul_le_mul (h₁ u hu ω) (h₂ u hu ω) (norm_nonneg _) hB₁)

/-- A deterministic coefficient continuous on the window. -/
private theorem expHier_Good_coef {b : ℝ} (c : ℝ → ℂ) (hc : ContinuousOn c (Set.Icc 0 b)) :
    expHier_Good d L W b (fun u _ => c u) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨fun u _ => continuous_const, fun _ => hc, max C 0, le_max_right _ _,
    fun u hu _ => (hC u hu).trans (le_max_left _ _)⟩

private theorem expHier_Good_const {b : ℝ} {c : ℂ} :
    expHier_Good d L W b (fun _ _ => c) :=
  expHier_Good_coef (fun _ => c) continuousOn_const

private theorem expHier_Good_sum {ι : Type*} {b : ℝ} (s : Finset ι)
    (F : ι → ℝ → Ω d L W → ℂ) (h : ∀ i ∈ s, expHier_Good d L W b (F i)) :
    expHier_Good d L W b (fun u ω => ∑ i ∈ s, F i u ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expHier_Good_const (d := d) (L := L) (W := W) (b := b) (c := 0)
  | insert i s hi ih =>
      have h1 := h i (Finset.mem_insert_self i s)
      have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using expHier_Good_add h1 h2

/-- The loop value along the spectral path is regular on `[0, b]`, `b < 1`
(`MLExpHier:Good_gloop`; bound `card (Vtx) (η⁻¹ W^{-d})^k`). -/
private theorem expHier_Good_loopL {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1)
    (I : LoopIdx (Zd d L)) :
    expHier_Good d L W b (fun u ω => loopL d L W (HflowBlock d L W u ω) (zt E u) I) := by
  have hη : 0 < (1 - b) * (mE E).im := mul_pos (by linarith) (spectralM_im_pos hE)
  have hlow : ∀ u ∈ Set.Icc (0 : ℝ) b, (1 - b) * (mE E).im ≤ |(zt E u).im| :=
    fun u hu => spectralZ_im_gap hE hb hu
  have hzim : ∀ u ∈ Set.Icc (0 : ℝ) b, (zt E u).im ≠ 0 := fun u hu =>
    abs_pos.mp (hη.trans_le (hlow u hu))
  refine ⟨fun u hu => (continuous_matrixTrace d L W).comp
      (continuous_gloopProd_HflowBlock_sample d L W u (hzim u hu) I),
    fun ω => continuousOn_gloop_any_window d L W hb0 ω (continuous_spectralZ E) hzim I,
    (Fintype.card (Vtx d L W) : ℝ) *
      (((1 - b) * (mE E).im)⁻¹ * (((W : ℝ) ^ d)⁻¹)) ^ (I.σ.zip I.a).length,
    by positivity, fun u hu ω => ?_⟩
  exact norm_gloop_any_window_le d L W hη hlow I hu ω

/-- Regularity gives integrability at every time of the window. -/
private theorem expHier_Good_integrable (g : ℝ) {b : ℝ} {F : ℝ → Ω d L W → ℂ}
    (hF : expHier_Good d L W b F) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) b) :
    Integrable (F u) (PF d L W g) := by
  obtain ⟨B, hB, h⟩ := hF.bdd
  exact Integrable.of_bound (hF.cont_ω u hu).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => h u hu ω)

/-- Regularity gives continuity of the expectation on the window. -/
private theorem expHier_Good_continuousOn_integral (g : ℝ) {b : ℝ} {F : ℝ → Ω d L W → ℂ}
    (hF : expHier_Good d L W b F) :
    ContinuousOn (fun u => ∫ ω, F u ω ∂(PF d L W g)) (Set.Icc 0 b) := by
  obtain ⟨B, hB, h⟩ := hF.bdd
  exact MeasureTheory.continuousOn_of_dominated
    (fun u hu => (hF.cont_ω u hu).measurable.aestronglyMeasurable)
    (fun u hu => Filter.Eventually.of_forall fun ω => h u hu ω)
    (integrable_const B) (Filter.Eventually.of_forall fun ω => hF.cont_u ω)

/-- Transport of regularity along a pointwise equality. -/
private theorem expHier_Good_congr {b : ℝ} {F G : ℝ → Ω d L W → ℂ}
    (hF : expHier_Good d L W b F) (h : ∀ u ω, F u ω = G u ω) : expHier_Good d L W b G := by
  have : G = F := by funext u ω; exact (h u ω).symm
  rw [this]; exact hF

/-- A function continuous on every `[0,b]`, `b < 1`, is continuous on `[0,1)` (`MLExpHier:488`). -/
private theorem expHier_continuousOn_Ico {F : ℝ → ℂ}
    (h : ∀ b : ℝ, 0 ≤ b → b < 1 → ContinuousOn F (Set.Icc 0 b)) :
    ContinuousOn F (Set.Ico 0 1) := by
  intro u hu
  have hb : u < (u + 1) / 2 := by linarith [hu.2]
  have hcw := h ((u + 1) / 2) (by linarith [hu.1]) (by linarith [hu.2]) u
    ⟨hu.1, hb.le⟩
  refine hcw.mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Set.Iio ((u + 1) / 2), isOpen_Iio, hb, fun x hx => ⟨hx.2.1, hx.1.le⟩⟩

end Good

/-- **Target 1a** (`MLExpHier_continuousOn_Lexp`, `MLExpHier:499`): the expected loop is continuous on
`[0,1)`, including `u = 0`, for every loop index (no `WF` needed). -/
theorem expHier_continuousOn_integral_loopL {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)
    {E : ℝ} (hE : |E| < 2) (I : LoopIdx (Zd d L)) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) I
      ∂(PF d L W g)) (Set.Ico 0 1) :=
  expHier_continuousOn_Ico fun b hb0 hb1 =>
    expHier_Good_continuousOn_integral g (expHier_Good_loopL hE hb0 hb1 I)

/-! ## 2. The samplewise bridge: `genMat E u (H_u) = ` the merged cut expression (`u > 0`)
(`MLExpHier:298-453`) -/

section Bridge

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The line `y ↦ blockMat (H_u + y X_c)` is the coordinate line of the flow block. -/
private theorem expHier_blockMat_line (u : ℝ) (ω : Ω d L W) (c : CoordF d L W) (y : ℝ) :
    blockMat d L W (Hflow d L W u ω + (y : ℂ) • coordinateMatrix d L W c) =
      HflowBlock d L W u ω + y • coordinateBlock d L W c := by
  ext i j
  simp [blockMat, HflowBlock, coordinateBlock, Matrix.submatrix_apply, Complex.real_smul]

/-- **The factor `u⁻¹` of the second derivative** (`H_u = √u X`): the coordinate Hessian of the flow
sample at time `u` is `u` times the line Hessian of `y ↦ 𝓛(H_u + y X_c)` at `y = 0`
(`MLExpHier:313`, `MLExpHier_second_deriv`). -/
private theorem expHier_second_deriv {u : ℝ} (hu : 0 < u) (ω : Ω d L W) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Zd d L)) (hI : I.WF) :
    deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (Hflow d L W u ω + (y : ℂ) • coordinateMatrix d L W c)) z I)) 0 =
      (u : ℂ)⁻¹ * Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a)) := by
  set s : ℝ := Real.sqrt u with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu
  have hss : s * s = u := Real.mul_self_sqrt hu.le
  set g : ℝ → ℂ := fun t => loopL d L W (HflowBlock d L W u (Function.update ω c t)) z I with hg
  set f : ℝ → ℂ := fun y => loopL d L W
    (blockMat d L W (Hflow d L W u ω + (y : ℂ) • coordinateMatrix d L W c)) z I with hf
  have hfg : f = fun y => g (ω c + s⁻¹ * y) := by
    funext y
    simp only [hf, hg, expHier_blockMat_line, HflowBlock_update]
    congr 2
    rw [show ω c + s⁻¹ * y - ω c = s⁻¹ * y by ring, ← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]
  have hg1 : ∀ t, HasDerivAt g (Matrix.trace (coordinateWordDeriv d L W u
      (Function.update ω c t) c z (I.σ.zip I.a))) t := by
    intro t
    have h := hasDerivAt_gloop_update d L W u (Function.update ω c t) c hz I hI
    have hpoint : (Function.update ω c t) c = t := by simp
    rw [hpoint] at h
    have hpath : (fun s : ℝ => loopL d L W
        (HflowBlock d L W u (Function.update (Function.update ω c t) c s)) z I) = g := by
      funext s'
      simp [hg, Function.update_idem]
    rw [hpath] at h
    exact h
  have hg1' : ∀ t, HasDerivAt g (deriv g t) t := fun t => (hg1 t).differentiableAt.hasDerivAt
  have hg2 : HasDerivAt (fun t => deriv g t)
      (Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))) (ω c) :=
    hasDerivAt_deriv_gloop_update d L W u ω c hz I hI
  have hin : ∀ y : ℝ, HasDerivAt (fun y : ℝ => ω c + s⁻¹ * y) s⁻¹ y := fun y => by
    simpa using ((hasDerivAt_id y).const_mul s⁻¹).const_add (ω c)
  have h1 : ∀ y, HasDerivAt f (s⁻¹ • deriv g (ω c + s⁻¹ * y)) y := fun y => by
    rw [hfg]
    exact (hg1' (ω c + s⁻¹ * y)).scomp y (hin y)
  have hderiv : deriv f = fun y => s⁻¹ • deriv g (ω c + s⁻¹ * y) := by
    funext y; exact (h1 y).deriv
  have h2 : HasDerivAt (fun y : ℝ => deriv g (ω c + s⁻¹ * y))
      (s⁻¹ • Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))) 0 := by
    have hg2' : HasDerivAt (fun t => deriv g t)
        (Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a)))
        (ω c + s⁻¹ * (0 : ℝ)) := by simpa using hg2
    exact hg2'.scomp (0 : ℝ) (hin 0)
  have h3 : HasDerivAt (fun y : ℝ => s⁻¹ • deriv g (ω c + s⁻¹ * y))
      (s⁻¹ • s⁻¹ • Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))) 0 :=
    h2.const_smul s⁻¹
  change deriv (deriv f) 0 = _
  rw [hderiv, h3.deriv]
  have hu' : (u : ℂ) = (s : ℂ) * (s : ℂ) := by rw [← Complex.ofReal_mul, hss]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [hu']
  field_simp

open scoped Matrix.Norms.L2Operator in
/-- The spectral derivative of one signed resolvent at a fixed Hermitian matrix (copy of the
private `LoopGenN_hasDerivAt_Gsig_spec`, `Induction/LoopGenN.lean:147`; `MLExpHier:372`). -/
private theorem expHier_hasDerivAt_Gsig {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (σ : Bool) :
    HasDerivAt (fun v : ℝ => Gres H (zt E v) σ)
      (-(Gres H (zt E u) σ *
        (spectralMSign E σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        Gres H (zt E u) σ)) u := by
  have him : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  cases σ with
  | true =>
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) (hasDerivAt_spectralZ E u) hH him
      simpa only [spectralMSign, ite_true, zero_sub, neg_smul, neg_neg] using h
  | false =>
      have hz : HasDerivAt (fun v : ℝ => (starRingEnd ℂ) (zt E v))
          (-((starRingEnd ℂ) (mE E))) u := by
        simpa using (hasDerivAt_spectralZ E u).star
      have him' : ((starRingEnd ℂ) (zt E u)).im ≠ 0 := by simpa using him
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) hz hH him'
      have hfun : (fun v : ℝ => Gres H (zt E v) false) =
          fun v : ℝ => Gres H ((starRingEnd ℂ) (zt E v)) true := by
        funext v
        simp [Gres]
      rw [hfun]
      have hG : Gres H (zt E u) false = Gres H ((starRingEnd ℂ) (zt E u)) true := by
        simp [Gres]
      rw [hG]
      simpa only [spectralMSign, Bool.false_eq_true, ite_false, zero_sub, neg_smul, neg_neg] using h

open scoped Matrix.Norms.L2Operator in
/-- The spectral derivative of a signed word at the flow block `H_u` is the merged recursive
`spectralWordDeriv` (`MLExpHier:385`). -/
private theorem expHier_hasDerivAt_word (ω : Ω d L W) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (l : List (Bool × Zd d L)) :
    HasDerivAt (fun v : ℝ => l.foldr (fun q M =>
        Gres (HflowBlock d L W u ω) (zt E v) q.1 * Eblk d L W q.2 * M) 1)
      (spectralWordDeriv d L W ω E u l) u := by
  induction l with
  | nil =>
      simpa [spectralWordDeriv] using
        hasDerivAt_const u (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have h := ((expHier_hasDerivAt_Gsig (HflowBlock_isHermitian d L W u ω) hE hu
        p.1).mul_const (Eblk d L W p.2)).mul ih
      refine h.congr_deriv ?_
      simp only [spectralWordDeriv, gsigSpectralFlowDeriv]

open scoped Matrix.Norms.L2Operator in
/-- The spectral derivative of a loop at the fixed flow block `H_u` (`MLExpHier:415`). -/
private theorem expHier_deriv_spec (ω : Ω d L W) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (I : LoopIdx (Zd d L)) :
    deriv (fun v : ℝ => loopL d L W (HflowBlock d L W u ω) (zt E v) I) u =
      Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a)) := by
  set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt u (expHier_hasDerivAt_word ω hE hu (I.σ.zip I.a))
  simp only [hT, Function.comp_def] at h
  have hfun : (fun v : ℝ => loopL d L W (HflowBlock d L W u ω) (zt E v) I) =
      fun v : ℝ => Matrix.trace (((I.σ.zip I.a)).foldr (fun q M =>
        Gres (HflowBlock d L W u ω) (zt E v) q.1 * Eblk d L W q.2 * M) 1) := by
    funext v
    rfl
  rw [hfun]
  exact h.deriv

end Bridge

/-- **Target 1b** (`MLExpHier_genMat_eq_cuts`, `MLExpHier:436`; with `_second_deriv` `:313`, the factor
`u⁻¹` of `H_u = √u X`, and `_deriv_spec` `:415`): the one-step generator at the flow sample `H_u` is the
merged samplewise cut expression (`0 < u < 1`). -/
theorem expHier_genMat_eq_cuts {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {E u : ℝ}
    (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) (ω : Ω d L W) (I : LoopIdx (Zd d L)) (hI : I.WF) :
    genMat d L W g E u (Hflow d L W u ω) I = samplewiseLoopGeneratorCuts d L W g ω E u I := by
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  rw [← samplewise_loop_generator_eq_cuts d L W g ω hu hu1 I hI]
  unfold genMat
  simp only [expHier_second_deriv hu ω _ hz I hI]
  have h3 : deriv (fun v : ℝ => loopL d L W (blockMat d L W (Hflow d L W u ω)) (zt E v) I) u =
      Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a)) :=
    expHier_deriv_spec ω hE hu1 I
  rw [h3]
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  field_simp

/-! ## 3. The `𝒦` ODE at `n = 2` and the hierarchy at `k = 2`, for every `σ` -/

section Two

variable {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
  (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

private theorem expHier_loopOf_wf {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    (loopOf σ a).WF := by
  change (List.ofFn σ).length = (List.ofFn a).length
  simp

/-- `𝓛_I` of a list index `loopOf σ a` is `STLM` (copy of `HierarchyN_STLIM_loopOf`,
`Induction/HierarchyN.lean:84`). -/
private theorem expHier_STLIM_loopOf {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    sz.STLIM n E u H (loopOf σ a) = sz.STLM n E u H σ a :=
  (loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a).symm

private theorem expHier_STLKIM_loopOf {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    sz.STLKIM n E u H (loopOf σ a) = sz.STLKM n E u H σ a := by
  unfold STLKIM STLKM
  rw [expHier_STLIM_loopOf sz n E u H σ a]
  rfl

private theorem expHier_ThetaN_two (σ : Fin 2 → Bool)
    (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u A a = sz.STthetaOp n E u σ A a := by
  unfold ThetaN STthetaOp
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  have hμ : cycProd (fun i => mSigma E (σ i)) i = STmsig E (σ 0) * STmsig E (σ 1) := by
    fin_cases i
    · rfl
    · exact mul_comm _ _
  simp only [thetaKer, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, hμ]

private theorem expHier_length_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    (loopOf σ a).length = 2 := by
  change (List.ofFn a).length = 2
  simp

private theorem expHier_STelklkM_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STelklkM n E u H (loopOf σ a) = sz.STELKLKM n E u H σ a := by
  unfold STelklkM STELKLKM
  rw [expHier_length_two sz n σ a]
  have h1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  have h2 : (Finset.Ioc 1 2 : Finset ℕ) = {2} := by decide
  have h3 : (Finset.Ioc 2 2 : Finset ℕ) = ∅ := by decide
  rw [h1, Finset.sum_pair (by decide), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero]
  congr 1

private theorem expHier_STegtM_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STegtM n E u H (loopOf σ a) = sz.STEGtM n E u H σ a := by
  unfold STegtM STEGtM
  rw [expHier_length_two sz n σ a]
  have h1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by decide)]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rfl

/-- `STKloop` at a sign vector of length `2` is `kTwo` (`KLK_two_eq_kTwo`). -/
private theorem expHier_STKloop_eq (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (v : ℝ) :
    sz.STKloop n E v σ a =
      kTwo d (sz.L n) (sz.W n) (sz.lam n) (mSigma E) v (σ 0) (σ 1) (a 0) (a 1) := by
  have hI : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  unfold Sizes.STKloop
  rw [hI]
  exact KLK_two_eq_kTwo d (sz.L n) (sz.lam n) (sz.W n) E v (σ 0) (σ 1) (a 0) (a 1)

end Two

/-- **Target 1c** (new form; replaces RBM2D `isPrimitive_Kcal`, `MLExpHier:228`, `:542`): `(pro_dyncalK)`
at `n = 2` for `STKloop`, **every** `σ` (the merged `KpmODE` is `σ = (+,-)` only), on `[0,1)`. -/
theorem expHier_Kloop_hasDerivAt {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    HasDerivAt (fun v : ℝ => sz.STKloop n E v σ a)
      ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ e : Zd d (sz.L n),
        sz.STKloop n E u σ ![a 0, c] * SB d (sz.L n) (sz.lam n) c e *
          sz.STKloop n E u σ ![e, a 1]) u := by
  have hu : ‖(u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))‖ < 1 :=
    norm_mul_mSigma_lt_one hE.le hu0 hu1 (σ 0) (σ 1)
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne (sz.W n)))
  have h := hasDerivAt_kTwo (norm_SB d (sz.L n) (sz.lam n) (sz.three_le_L n)) hW (mSigma E)
    (σ 0) (σ 1) hu (a 0) (a 1)
  have hfun : (fun v : ℝ => sz.STKloop n E v σ a) =
      fun v : ℝ => kTwo d (sz.L n) (sz.W n) (sz.lam n) (mSigma E) v (σ 0) (σ 1) (a 0) (a 1) :=
    funext fun v => expHier_STKloop_eq sz n E σ a v
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [expHier_STKloop_eq sz n E σ _ u, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Target 1d** (copy of `hierarchyN_two`, `Induction/HierarchyN.lean:159`, with `σ` general, and the
private reductions `:81-140`; RBM2D `hierarchyN_two`, `MLExpVocab:239`): the matrix-level hierarchy
at `n = 2` for **every** `σ`, from `hierarchyN_holds` at `k = 2` (`Σ_{l ∈ Icc 3 2}` is empty). -/
theorem expHier_hierarchy_two {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) -
        deriv (fun v : ℝ => sz.STKloop n E v σ a) u =
      sz.STthetaOp n E u σ (sz.STLKM n E u M σ) a + sz.STELKLKM n E u M σ a +
        sz.STEGtM n E u M σ a := by
  have h2 := hierarchyN_holds d sz n E hE u hu0 hu1 M hM 2 le_rfl σ a
  have hfun : (fun b : Fin 2 → Zd d (sz.L n) => sz.STLKIM n E u M (loopOf σ b))
      = sz.STLKM n E u M σ :=
    funext fun b => expHier_STLKIM_loopOf sz n E u M σ b
  rw [expHier_ThetaN_two, hfun, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, add_zero,
    expHier_STelklkM_two, expHier_STegtM_two] at h2
  exact h2

/-! ## 4. The expected hierarchy at a fixed size (`MLExpHier:457-592`) -/

section FixedSize

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem expHier_STLM_eq (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    sz.STLM n E u H σ a =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (zt E u) (loopOf σ a) :=
  loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a

/-- `STLM` at the flow sample is regular on `[0,b]`. -/
private theorem expHier_Good_STLM {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b
      (fun u ω => sz.STLM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a) :=
  expHier_Good_congr (expHier_Good_loopL hE hb0 hb (loopOf σ a))
    fun u ω => (expHier_STLM_eq sz n E u _ σ a).symm

/-- `𝒦` at length `2` is continuous on `[0,1)` (from the `𝒦` ODE, target 1c). -/
private theorem expHier_continuousOn_Kloop {E : ℝ} (hE : |E| < 2) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun u : ℝ => sz.STKloop n E u σ a) (Set.Ico 0 1) :=
  fun t ht => (expHier_Kloop_hasDerivAt sz n hE t ht.1 ht.2 σ a).continuousAt.continuousWithinAt

private theorem expHier_Good_STLKM {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b
      (fun u ω => sz.STLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a) :=
  expHier_Good_sub (expHier_Good_STLM sz n hE hb0 hb σ a)
    (expHier_Good_coef _ ((expHier_continuousOn_Kloop sz n hE σ a).mono
      (fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hb⟩)))

private theorem expHier_Good_STELKLKM {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b
      (fun u ω => sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a) := by
  have hlk : ∀ a' : Fin 2 → Zd d (sz.L n), expHier_Good d (sz.L n) (sz.W n) b
      (fun u ω => sz.STLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a') := fun a' =>
    expHier_Good_STLKM sz n hE hb0 hb σ a'
  exact expHier_Good_mul expHier_Good_const
    (expHier_Good_sum _ _ fun x _ => expHier_Good_sum _ _ fun y _ =>
      expHier_Good_mul (expHier_Good_mul (hlk _) expHier_Good_const) (hlk _))

private theorem expHier_Good_STavgM {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1)
    (s : Bool) (x : Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b
      (fun u ω => sz.STavgM n E u (Hflow d (sz.L n) (sz.W n) u ω) s x) :=
  expHier_Good_sub (expHier_Good_STLM sz n hE hb0 hb (fun _ : Fin 1 => s) (fun _ => x))
    expHier_Good_const

private theorem expHier_Good_STEGtM {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b
      (fun u ω => sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a) := by
  exact expHier_Good_mul expHier_Good_const
    (expHier_Good_sum _ _ fun x _ => expHier_Good_sum _ _ fun y _ =>
      expHier_Good_add
        (expHier_Good_mul (expHier_Good_mul (expHier_Good_STavgM sz n hE hb0 hb _ _)
          expHier_Good_const) (expHier_Good_STLM sz n hE hb0 hb _ _))
        (expHier_Good_mul (expHier_Good_mul (expHier_Good_STavgM sz n hE hb0 hb _ _)
          expHier_Good_const) (expHier_Good_STLM sz n hE hb0 hb _ _)))

/-- The expectation of `Θ^{(2)}_{u,σ}` of a family of integrable tensors is `Θ^{(2)}_{u,σ}` of the
expectation (`MLExpHier_integral_thetaSig`, `MLExpHier:476`). -/
private theorem expHier_integral_thetaOp (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (Φ : Ω d (sz.L n) (sz.W n) → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hΦ : ∀ b, Integrable (fun ω => Φ ω b) (PF d (sz.L n) (sz.W n) (sz.lam n))) :
    ∫ ω, sz.STthetaOp n E u σ (Φ ω) a ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) =
      sz.STthetaOp n E u σ (fun b => ∫ ω, Φ ω b ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) a := by
  unfold STthetaOp
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun b _ => (hΦ _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun b _ => (hΦ _).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

/-- **Target 1e** (`MLExpHier_hasDerivAt`, `MLExpHier:515`, with `_integral_LKf` `:464`): the expected
hierarchy at one size, on `(0,1)`, over the one-size law `PF d L W g` at
`(L, W, g) = (sz.L n, sz.W n, sz.lam n)`; the drift as the two integrals of `STExpDrift`. -/
theorem expHier_hasDerivAt_fixed {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    HasDerivAt (fun v : ℝ =>
        (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) v ω) (zt E v) (loopOf σ a)
          ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E v σ a)
      (sz.STthetaOp n E u σ (fun b =>
          (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) u ω) (zt E u) (loopOf σ b)
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E u σ b) a +
        ((∫ ω, sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) +
          ∫ ω, sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n)))) u := by
  have hI : (loopOf σ a).WF := expHier_loopOf_wf sz n σ a
  -- the expected loop
  have hL1 := hasDerivAt_integral_gloop_HflowBlock_spectralZ d (sz.L n) (sz.W n) (sz.lam n) hE hu0
    hu1 (loopOf σ a) hI
  have hL2 : HasDerivAt (fun v : ℝ => ∫ ω : Ω d (sz.L n) (sz.W n),
      loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) v ω) (zt E v) (loopOf σ a)
        ∂(PF d (sz.L n) (sz.W n) (sz.lam n)))
      (∫ ω : Ω d (sz.L n) (sz.W n), genMat d (sz.L n) (sz.W n) (sz.lam n) E u
        (Hflow d (sz.L n) (sz.W n) u ω) (loopOf σ a) ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) u := by
    have h0 := hL1.differentiableAt.hasDerivAt
    rw [deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts d (sz.L n) (sz.W n)
      (sz.lam n) hE hu0 hu1 (loopOf σ a) hI] at h0
    have hcuts : (∫ ω : Ω d (sz.L n) (sz.W n), genMat d (sz.L n) (sz.W n) (sz.lam n) E u
        (Hflow d (sz.L n) (sz.W n) u ω) (loopOf σ a) ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) =
        ∫ ω : Ω d (sz.L n) (sz.W n), samplewiseLoopGeneratorCuts d (sz.L n) (sz.W n) (sz.lam n) ω
          E u (loopOf σ a) ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        expHier_genMat_eq_cuts (sz.L n) (sz.W n) (sz.lam n) hE hu0 hu1 ω (loopOf σ a) hI)
    rw [hcuts]
    exact h0
  -- the deterministic `𝒦`
  have hK2 := (expHier_Kloop_hasDerivAt sz n hE u hu0.le hu1 σ a).differentiableAt.hasDerivAt
  refine (hL2.sub hK2).congr_deriv ?_
  -- integrability
  have hgen : Integrable (fun ω : Ω d (sz.L n) (sz.W n) => genMat d (sz.L n) (sz.W n) (sz.lam n) E u
      (Hflow d (sz.L n) (sz.W n) u ω) (loopOf σ a)) (PF d (sz.L n) (sz.W n) (sz.lam n)) := by
    have := integrable_samplewiseLoopGeneratorCuts d (sz.L n) (sz.W n) (sz.lam n) hE hu0 hu1
      (loopOf σ a) hI
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (expHier_genMat_eq_cuts (sz.L n) (sz.W n) (sz.lam n) hE hu0 hu1 ω (loopOf σ a) hI).symm
  have hlkI : ∀ b : Fin 2 → Zd d (sz.L n), Integrable
      (fun ω => sz.STLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ b)
      (PF d (sz.L n) (sz.W n) (sz.lam n)) := fun b =>
    expHier_Good_integrable (sz.lam n) (expHier_Good_STLKM sz n hE hu0.le hu1 σ b)
      (u := u) ⟨hu0.le, le_rfl⟩
  have hXi : Integrable (fun ω : Ω d (sz.L n) (sz.W n) =>
      sz.STthetaOp n E u σ (sz.STLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ) a)
      (PF d (sz.L n) (sz.W n) (sz.lam n)) := by
    unfold STthetaOp
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun b _ =>
      (hlkI _).const_mul _
  have hD1 : Integrable (fun ω : Ω d (sz.L n) (sz.W n) =>
      sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a)
      (PF d (sz.L n) (sz.W n) (sz.lam n)) :=
    expHier_Good_integrable (sz.lam n) (expHier_Good_STELKLKM sz n hE hu0.le hu1 σ a)
      (u := u) ⟨hu0.le, le_rfl⟩
  have hD2 : Integrable (fun ω : Ω d (sz.L n) (sz.W n) =>
      sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a)
      (PF d (sz.L n) (sz.W n) (sz.lam n)) :=
    expHier_Good_integrable (sz.lam n) (expHier_Good_STEGtM sz n hE hu0.le hu1 σ a)
      (u := u) ⟨hu0.le, le_rfl⟩
  -- the pointwise hierarchy identity
  have hpt : ∀ ω : Ω d (sz.L n) (sz.W n), genMat d (sz.L n) (sz.W n) (sz.lam n) E u
      (Hflow d (sz.L n) (sz.W n) u ω) (loopOf σ a) -
      deriv (fun v : ℝ => sz.STKloop n E v σ a) u =
        sz.STthetaOp n E u σ (sz.STLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ) a +
          sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a +
          sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a := fun ω =>
    expHier_hierarchy_two sz n hE u hu0.le hu1 (Hflow d (sz.L n) (sz.W n) u ω)
      (Hflow_isHermitian d (sz.L n) (sz.W n) u ω) σ a
  have hint : (∫ ω : Ω d (sz.L n) (sz.W n), genMat d (sz.L n) (sz.W n) (sz.lam n) E u
        (Hflow d (sz.L n) (sz.W n) u ω) (loopOf σ a) ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) -
      deriv (fun v : ℝ => sz.STKloop n E v σ a) u =
      (∫ ω : Ω d (sz.L n) (sz.W n),
        sz.STthetaOp n E u σ (sz.STLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ) a
          ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) +
        ((∫ ω : Ω d (sz.L n) (sz.W n), sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) +
          ∫ ω : Ω d (sz.L n) (sz.W n), sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) := by
    have hD12 : Integrable (fun ω : Ω d (sz.L n) (sz.W n) =>
        sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a +
          sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a)
        (PF d (sz.L n) (sz.W n) (sz.lam n)) := hD1.add hD2
    have hpt' : ∀ ω : Ω d (sz.L n) (sz.W n), sz.STthetaOp n E u σ
        (sz.STLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ) a +
          (sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a +
          sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a) =
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u
          (Hflow d (sz.L n) (sz.W n) u ω) (loopOf σ a) -
        deriv (fun v : ℝ => sz.STKloop n E v σ a) u := fun ω => by
      rw [hpt ω]; ring
    have h3 := integral_congr_ae (μ := PF d (sz.L n) (sz.W n) (sz.lam n))
      (Filter.Eventually.of_forall hpt')
    rw [integral_sub hgen (integrable_const _)] at h3
    rw [← integral_add hD1 hD2, ← integral_add hXi hD12, h3]
    simp
  rw [hint]
  congr 1
  refine (expHier_integral_thetaOp sz n E u σ a
    (fun ω b => sz.STLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ b) hlkI).trans ?_
  congr 1
  funext b
  have hg := expHier_Good_integrable (sz.lam n)
    (expHier_Good_loopL (d := d) (L := sz.L n) (W := sz.W n) hE hu0.le hu1 (loopOf σ b))
    (u := u) ⟨hu0.le, le_rfl⟩
  change ∫ ω, (sz.STLM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ b - sz.STKloop n E u σ b)
    ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) = _
  rw [integral_sub (hg.congr (Filter.Eventually.of_forall fun ω =>
      (expHier_STLM_eq sz n E u _ σ b).symm)) (integrable_const _)]
  rw [integral_const, probReal_univ, one_smul]
  congr 1

end FixedSize

/-! ## 5. Transfer to the common probability space, and the pin `STExpHier` (`MLExpHier:594-667`) -/

section Target

variable {d : ℕ} (sz : Sizes d)

/-- Integrals over the common space of a function of the size-`n` slice are integrals over `PF`
(`MLExpHier_integral_slice`, `MLExpHier:601`). -/
private theorem expHier_integral_slice (n : ℕ) (G : Ω d (sz.L n) (sz.W n) → ℂ)
    (hG : AEStronglyMeasurable G (PF d (sz.L n) (sz.W n) (sz.lam n))) :
    ∫ ω, G (sz.slice n ω) ∂(sz.seqP) = ∫ ω, G ω ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
  have hf : AEMeasurable (sz.slice n) (sz.seqP) := (sz.measurable_slice n).aemeasurable
  have hg : AEStronglyMeasurable G ((sz.seqP).map (sz.slice n)) := by
    rw [sz.seqP_map_slice]; exact hG
  rw [← integral_map hf hg, sz.seqP_map_slice]

/-- `STExpErr` is `𝔼𝓛 - 𝒦` over the size-`n` law, for `u < 1`. -/
private theorem expHier_expErr_eq (n : ℕ) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu1 : u < 1)
    (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) :
    sz.STExpErr n E u σ b =
      (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) u ω) (zt E u) (loopOf σ b)
          ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E u σ b := by
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  unfold STExpErr
  congr 1
  rw [← expHier_integral_slice sz n
    (fun ω' => loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) u ω') (zt E u)
      (loopOf σ b))
    ((continuous_gloop_HflowBlock_sample d (sz.L n) (sz.W n) u hz (loopOf σ b)
      (expHier_loopOf_wf sz n σ b)).aestronglyMeasurable)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ b)

/-- `STExpELKLK` is the integral over the size-`n` law, for `0 ≤ u < 1`. -/
private theorem expHier_expELKLK_eq (n : ℕ) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpELKLK n E u σ a =
      ∫ ω, sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a
        ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
  unfold STExpELKLK
  exact expHier_integral_slice sz n
    (fun ω' => sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω') σ a)
    (((expHier_Good_STELKLKM sz n hE hu0 hu1 σ a).cont_ω u ⟨hu0, le_rfl⟩).aestronglyMeasurable)

/-- `STExpEGt` is the integral over the size-`n` law, for `0 ≤ u < 1`. -/
private theorem expHier_expEGt_eq (n : ℕ) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpEGt n E u σ a =
      ∫ ω, sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a
        ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
  unfold STExpEGt
  exact expHier_integral_slice sz n
    (fun ω' => sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω') σ a)
    (((expHier_Good_STEGtM sz n hE hu0 hu1 σ a).cont_ω u ⟨hu0, le_rfl⟩).aestronglyMeasurable)

/-- **Target 2a** (`MLExpHier:649-651`): `f = 𝔼(𝓛 - 𝒦)` is continuous on `[0,1)`. -/
theorem expHier_continuousOn_err {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun u => sz.STExpErr n E u σ a) (Set.Ico 0 1) := by
  have h1 := (expHier_continuousOn_integral_loopL (d := d) (sz.L n) (sz.W n) (sz.lam n) hE
    (loopOf σ a)).sub (expHier_continuousOn_Kloop sz n hE σ a)
  exact h1.congr fun v hv => expHier_expErr_eq sz n hE hv.2 σ a

/-- **Target 2b** (`MLExpHier:652-653`, `_Good_drift` `:262` split): the drift
`D = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}` is continuous on `[0,1)`. -/
theorem expHier_continuousOn_drift {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun u => sz.STExpDrift n E u σ a) (Set.Ico 0 1) := by
  have h1 : ContinuousOn (fun u : ℝ => ∫ ω, sz.STELKLKM n E u
      (Hflow d (sz.L n) (sz.W n) u ω) σ a ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) (Set.Ico 0 1) :=
    expHier_continuousOn_Ico fun b hb0 hb1 =>
      expHier_Good_continuousOn_integral (sz.lam n) (expHier_Good_STELKLKM sz n hE hb0 hb1 σ a)
  have h2 : ContinuousOn (fun u : ℝ => ∫ ω, sz.STEGtM n E u
      (Hflow d (sz.L n) (sz.W n) u ω) σ a ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) (Set.Ico 0 1) :=
    expHier_continuousOn_Ico fun b hb0 hb1 =>
      expHier_Good_continuousOn_integral (sz.lam n) (expHier_Good_STEGtM sz n hE hb0 hb1 σ a)
  exact (h1.add h2).congr fun v hv => by
    unfold STExpDrift
    rw [expHier_expELKLK_eq sz n hE hv.1 hv.2 σ a, expHier_expEGt_eq sz n hE hv.1 hv.2 σ a]
    rfl

/-- **Target 2c** (`MLExpHier:654-664`): `∂_u f = Θ^{(2)}_{u,σ} f + D` on `(0,1)`. -/
theorem expHier_hasDerivAt {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz.STExpErr n E v σ a)
      (sz.STthetaOp n E u σ (fun b => sz.STExpErr n E u σ b) a + sz.STExpDrift n E u σ a) u := by
  intro u hu
  have h1 := expHier_hasDerivAt_fixed sz n hE u hu.1 hu.2 σ a
  have hev : (fun v => sz.STExpErr n E v σ a) =ᶠ[nhds u] (fun v : ℝ =>
      (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) v ω) (zt E v)
        (loopOf σ a) ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E v σ a) := by
    filter_upwards [Iio_mem_nhds hu.2] with v hv
    exact expHier_expErr_eq sz n hE hv σ a
  refine (h1.congr_of_eventuallyEq hev).congr_deriv ?_
  have hθ : (fun b => sz.STExpErr n E u σ b) = fun b =>
      (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) u ω) (zt E u)
        (loopOf σ b) ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E u σ b :=
    funext fun b => expHier_expErr_eq sz n hE hu.2 σ b
  rw [hθ]
  unfold STExpDrift
  rw [expHier_expELKLK_eq sz n hE hu.1.le hu.2 σ a, expHier_expEGt_eq sz n hE hu.1.le hu.2 σ a]

/-- **Target 3: the pin `STExpHier`** (`expHierPin`, `MLExpHier:643`), proved for every `d` (the premise
`3 ≤ d` is not used).  Without RBM2D's first conjunct `f_0 = 0`, which the merged pin does not state. -/
theorem stExpHier_holds (d : ℕ) : STExpHier d :=
  fun _ sz n E hE σ a =>
    ⟨expHier_continuousOn_err sz n hE σ a, expHier_continuousOn_drift sz n hE σ a,
      expHier_hasDerivAt sz n hE σ a⟩

end Target

end RBM.Gauss.Sizes

/-! ## 6. Compiled nonempty instances

At `d = 3`, the merged admissible sequence `sz0` (`RBM.Gauss.SizesInst.sz0`: `L_0 = 4`, `W_0 = 32`,
`lam_0 = 1/64`), `n = 0`, `E = 1/2` (`|E| < 2`), loop label `a = (0, e₁)`.  Every hypothesis is
discharged (`|1/2| < 2`, `0 < 1/2 < 1`, `M = 1` Hermitian); nothing is left as a hypothesis. -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Path RBM.Loop Filter MeasureTheory

/-- `stExpHier_holds 3` through the merged `inst_expHier`, `σ = (+,-)`. -/
theorem inst_expHier_holds :
    ContinuousOn (fun u => sz0.STExpErr 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => sz0.STExpDrift 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz0.STExpErr 0 (1 / 2) v ![true, false] ![0, Pi.single 0 1])
      (sz0.STthetaOp 0 (1 / 2) u ![true, false] (fun b => sz0.STExpErr 0 (1 / 2) u ![true, false] b)
          ![0, Pi.single 0 1] + sz0.STExpDrift 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) u :=
  inst_expHier (stExpHier_holds 3)

/-- The repeated sign `σ = (+,+)`, outside `HierarchyN2`/`KpmODE`. -/
theorem inst_expHier_pp :
    ContinuousOn (fun u => sz0.STExpErr 0 (1 / 2) u ![true, true] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => sz0.STExpDrift 0 (1 / 2) u ![true, true] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz0.STExpErr 0 (1 / 2) v ![true, true] ![0, Pi.single 0 1])
      (sz0.STthetaOp 0 (1 / 2) u ![true, true] (fun b => sz0.STExpErr 0 (1 / 2) u ![true, true] b)
          ![0, Pi.single 0 1] + sz0.STExpDrift 0 (1 / 2) u ![true, true] ![0, Pi.single 0 1]) u :=
  stExpHier_holds 3 (by norm_num) sz0 0 (1 / 2) (by norm_num [abs_of_pos]) ![true, true]
    ![0, Pi.single 0 1]

/-- The drift identity at the interior time `u = 1/2`, `σ = (-,-)`. -/
theorem inst_expHier_half :
    HasDerivAt (fun v => sz0.STExpErr 0 (1 / 2) v ![false, false] ![0, Pi.single 0 1])
      (sz0.STthetaOp 0 (1 / 2) (1 / 2) ![false, false] (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![false, false] b)
        ![0, Pi.single 0 1] + sz0.STExpDrift 0 (1 / 2) (1 / 2) ![false, false] ![0, Pi.single 0 1]) (1 / 2) :=
  (stExpHier_holds 3 (by norm_num) sz0 0 (1 / 2) (by norm_num [abs_of_pos]) ![false, false]
    ![0, Pi.single 0 1]).2.2 (1 / 2) ⟨by norm_num, by norm_num⟩

/-- Target 1c at `sz0`, `n = 0`, `E = u = 1/2`, `σ = (+,+)`. -/
theorem inst_expHier_Kloop :
    HasDerivAt (fun v : ℝ => sz0.STKloop 0 (1 / 2) v ![true, true] ![0, Pi.single 0 1])
      ((((sz0.W 0 : ℕ) : ℂ) ^ 3) * ∑ c : Zd 3 (sz0.L 0), ∑ e : Zd 3 (sz0.L 0),
        sz0.STKloop 0 (1 / 2) (1 / 2) ![true, true] ![0, c] * SB 3 (sz0.L 0) (sz0.lam 0) c e *
          sz0.STKloop 0 (1 / 2) (1 / 2) ![true, true] ![e, Pi.single 0 1]) (1 / 2) :=
  expHier_Kloop_hasDerivAt sz0 0 (by norm_num [abs_of_pos]) (1 / 2) (by norm_num) (by norm_num)
    ![true, true] ![0, Pi.single 0 1]

/-- Target 1d at `sz0`, `n = 0`, `E = u = 1/2`, `M = 1`, `σ = (-,-)`, `a = (0, 0)`. -/
theorem inst_expHier_hierarchy_two :
    genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 2) (1 / 2)
        (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        (loopOf ![false, false] ![(0 : Zd 3 (sz0.L 0)), 0]) -
      deriv (fun v : ℝ => sz0.STKloop 0 (1 / 2) v ![false, false] ![(0 : Zd 3 (sz0.L 0)), 0]) (1 / 2) =
    sz0.STthetaOp 0 (1 / 2) (1 / 2) ![false, false]
        (sz0.STLKM 0 (1 / 2) (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          ![false, false]) ![0, 0] +
      sz0.STELKLKM 0 (1 / 2) (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        ![false, false] ![0, 0] +
      sz0.STEGtM 0 (1 / 2) (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        ![false, false] ![0, 0] :=
  expHier_hierarchy_two sz0 0 (by norm_num [abs_of_pos]) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one ![false, false] ![0, 0]

/-- Target 1a at `(L, W, g) = (4, 32, 1/64)`, `E = 1/2`, the loop `((+,-), (0, e₁))`. -/
example :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω 3 (sz0.L 0) (sz0.W 0),
      loopL 3 (sz0.L 0) (sz0.W 0) (HflowBlock 3 (sz0.L 0) (sz0.W 0) u ω) (zt (1 / 2) u)
        (loopOf ![true, false] ![(0 : Zd 3 (sz0.L 0)), Pi.single 0 1])
      ∂(PF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0))) (Set.Ico 0 1) :=
  expHier_continuousOn_integral_loopL (sz0.L 0) (sz0.W 0) (sz0.lam 0) (by norm_num [abs_of_pos]) _

/-- Target 1b at the nonzero sample `ω ≡ 1`, `E = u = 1/2`, the loop `((+,-), (0, e₁))`. -/
example :
    genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 2) (1 / 2)
        (Hflow 3 (sz0.L 0) (sz0.W 0) (1 / 2) (fun _ => 1))
        (loopOf ![true, false] ![(0 : Zd 3 (sz0.L 0)), Pi.single 0 1]) =
      samplewiseLoopGeneratorCuts 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (fun _ => 1) (1 / 2) (1 / 2)
        (loopOf ![true, false] ![(0 : Zd 3 (sz0.L 0)), Pi.single 0 1]) :=
  expHier_genMat_eq_cuts (sz0.L 0) (sz0.W 0) (sz0.lam 0) (by norm_num [abs_of_pos]) (by norm_num)
    (by norm_num) (fun _ => 1) _ (by simp [LoopIdx.WF, loopOf])

/-- Target 1e at `sz0`, `n = 0`, `E = u = 1/2`, `σ = (+,-)`. -/
example :=
  expHier_hasDerivAt_fixed sz0 0 (E := 1 / 2) (by norm_num [abs_of_pos]) (1 / 2) (by norm_num)
    (by norm_num) ![true, false] ![0, Pi.single 0 1]

/-- Target 2a at `sz0`, `n = 0`, `E = 1/2`, `σ = (+,-)`. -/
example :=
  expHier_continuousOn_err sz0 0 (E := 1 / 2) (by norm_num [abs_of_pos]) ![true, false]
    ![0, Pi.single 0 1]

/-- Target 2b at `sz0`, `n = 0`, `E = 1/2`, `σ = (+,-)`. -/
example :=
  expHier_continuousOn_drift sz0 0 (E := 1 / 2) (by norm_num [abs_of_pos]) ![true, false]
    ![0, Pi.single 0 1]

end RBM.Gauss.Step6Inst

end

#print axioms RBM.Gauss.Sizes.expHier_continuousOn_integral_loopL
#print axioms RBM.Gauss.Sizes.expHier_genMat_eq_cuts
#print axioms RBM.Gauss.Sizes.expHier_Kloop_hasDerivAt
#print axioms RBM.Gauss.Sizes.expHier_hierarchy_two
#print axioms RBM.Gauss.Sizes.expHier_hasDerivAt_fixed
#print axioms RBM.Gauss.Sizes.expHier_continuousOn_err
#print axioms RBM.Gauss.Sizes.expHier_continuousOn_drift
#print axioms RBM.Gauss.Sizes.expHier_hasDerivAt
#print axioms RBM.Gauss.Sizes.stExpHier_holds
#print axioms RBM.Gauss.Step6Inst.inst_expHier_holds
#print axioms RBM.Gauss.Step6Inst.inst_expHier_pp
#print axioms RBM.Gauss.Step6Inst.inst_expHier_half
#print axioms RBM.Gauss.Step6Inst.inst_expHier_Kloop
#print axioms RBM.Gauss.Step6Inst.inst_expHier_hierarchy_two
