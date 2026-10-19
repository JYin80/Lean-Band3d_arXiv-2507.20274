/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.LoopFlowStein
import RBM3D.Hierarchy.ContractionSecondLoop

/-!
# The loop generator: cut expansion, expectation, initial values

In the vocabulary of `RBM3D.Gauss.FlowCalculus`, `RBM3D.Gauss.LoopCoordinate` and
`RBM3D.Gauss.LoopFlowStein`: `Zd d L` is the block lattice, `Vtx d L W` the block-product index,
`Gres` the resolvent of either sign, `loopL` the loop, `zt` the spectral path, `mE` the bulk
value, `CoordF`, `gvarF`, `PF d L W g` the coordinates, their variances and the one-size law, and
`SB d L g` the block variance profile; the block size enters as `W^d` (and `W^{-d}`).

Contents: the spectral drift as a finite sum of single-edge cuts, the samplewise and the expected
finite-loop cut expressions, the initial value of a finite Gaussian resolvent loop (scalar
values, projector words, support), and the time continuity and bound of finite expected loops.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace RBM.Gauss

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

variable (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)

/-! ## 1. Spectral drift as a finite sum of single-edge cuts -/

/-- A split at one signed edge of a paired loop word. -/
structure SpectralEdgeSplit (d L : ℕ) where
  pre : List (Bool × Zd d L)
  edge : Bool × Zd d L
  post : List (Bool × Zd d L)

/-- One split per signed edge, in its original list order. -/
def spectralEdgeSplits : List (Bool × Zd d L) → List (SpectralEdgeSplit d L)
  | [] => []
  | p :: l => ⟨[], p, l⟩ ::
      (spectralEdgeSplits l).map fun s => ⟨p :: s.pre, s.edge, s.post⟩

omit [NeZero L] [NeZero W] in
/-- Every generated split reconstructs its original paired word. -/
theorem spectralEdgeSplits_reconstruct (l : List (Bool × Zd d L))
    (s : SpectralEdgeSplit d L) (hs : s ∈ spectralEdgeSplits d L l) :
    s.pre ++ s.edge :: s.post = l := by
  induction l generalizing s with
  | nil => simp [spectralEdgeSplits] at hs
  | cons p l ih =>
      simp only [spectralEdgeSplits, List.mem_cons, List.mem_map] at hs
      rcases hs with rfl | ⟨s', hs', rfl⟩
      · rfl
      · simpa only [List.cons_append] using congrArg (List.cons p) (ih s' hs')

private theorem pairedWord_eq_gloopProd
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1 =
      gloopProd d L W H z ⟨l.map Prod.fst, l.map Prod.snd⟩ := by
  have hzip : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with
    | nil => rfl
    | cons p l ih => simp [ih]
  rw [gloopProd, hzip]

/-- The matrix insertion at a selected signed edge. -/
noncomputable def spectralEdgeTerm (ω : Ω d L W) (E u : ℝ)
    (s : SpectralEdgeSplit d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  let H := HflowBlock d L W u ω;
  let z := zt E u;
  let G := Gres H z s.edge.1;
  let M := spectralMSign E s.edge.1 •
    (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ);
  -((s.pre.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1) *
    (G * M * (G * Eblk d L W s.edge.2 *
      (s.post.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1))))

private theorem spectralEdgeTerm_head (ω : Ω d L W) (E u : ℝ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    spectralEdgeTerm d L W ω E u ⟨[], p, l⟩ =
      (gsigSpectralFlowDeriv d L W ω E u p.1 * Eblk d L W p.2) *
        l.foldr (fun q M => Gres (HflowBlock d L W u ω) (zt E u) q.1 *
          Eblk d L W q.2 * M) 1 := by
  simp only [spectralEdgeTerm, List.foldr_nil, one_mul, gsigSpectralFlowDeriv]
  noncomm_ring

private theorem spectralEdgeTerm_cons_prefix (ω : Ω d L W) (E u : ℝ)
    (p : Bool × Zd d L) (s : SpectralEdgeSplit d L) :
    spectralEdgeTerm d L W ω E u ⟨p :: s.pre, s.edge, s.post⟩ =
      (Gres (HflowBlock d L W u ω) (zt E u) p.1 * Eblk d L W p.2) *
        spectralEdgeTerm d L W ω E u s := by
  simp only [spectralEdgeTerm, List.foldr_cons]
  noncomm_ring

/-- The recursive spectral derivative is the finite sum of all signed-edge insertions. -/
theorem spectralWordDeriv_eq_sum_edgeTerms (ω : Ω d L W) (E u : ℝ)
    (l : List (Bool × Zd d L)) :
    spectralWordDeriv d L W ω E u l =
      ((spectralEdgeSplits d L l).map (spectralEdgeTerm d L W ω E u)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      have htail :
          ((spectralEdgeSplits d L l).map fun s => spectralEdgeTerm d L W ω E u
            ⟨p :: s.pre, s.edge, s.post⟩).sum =
          (Gres (HflowBlock d L W u ω) (zt E u) p.1 * Eblk d L W p.2) *
            ((spectralEdgeSplits d L l).map (spectralEdgeTerm d L W ω E u)).sum := by
        simp_rw [spectralEdgeTerm_cons_prefix]
        exact List.sum_map_mul_left _ _ _
      rw [spectralWordDeriv]
      simp only [spectralEdgeSplits, List.map_cons, List.sum_cons, List.map_map,
        Function.comp_def, spectralEdgeTerm_head]
      rw [htail]
      rw [← ih]

/-- A single signed-edge insertion is the existing cut-and-glue loop sum; the coefficient is
`-(m_σ W^d)`. -/
theorem trace_spectralEdgeTerm_eq_cutGlue (ω : Ω d L W) (E u : ℝ)
    (s : SpectralEdgeSplit d L) :
    Matrix.trace (spectralEdgeTerm d L W ω E u s) =
      -(spectralMSign E s.edge.1 * (W : ℂ) ^ d) *
        ∑ b : Zd d L,
          loopL d L W (HflowBlock d L W u ω) (zt E u)
            ((⟨s.pre.map Prod.fst ++ s.edge.1 :: s.post.map Prod.fst,
                s.pre.map Prod.snd ++ s.edge.2 :: s.post.map Prod.snd⟩ :
              Loop.LoopIdx (Zd d L)).cutGlue (s.pre.length + 1) b) := by
  have hpre : (s.pre.map Prod.fst).length = (s.pre.map Prod.snd).length := by simp
  have h := neg_trace_scalarDrift_cutGlue_split d L W
    (HflowBlock d L W u ω) (zt E u)
    (s.pre.map Prod.fst) (s.post.map Prod.fst)
    (s.pre.map Prod.snd) (s.post.map Prod.snd)
    s.edge.1 s.edge.2 (spectralMSign E s.edge.1) hpre
  simpa only [spectralEdgeTerm, Matrix.trace_neg, pairedWord_eq_gloopProd,
    List.length_map] using h

/-- The traced spectral drift is the finite sum of the single-edge cut-loop sums. -/
theorem trace_spectralWordDeriv_eq_sum_cuts (ω : Ω d L W) (E u : ℝ)
    (l : List (Bool × Zd d L)) :
    Matrix.trace (spectralWordDeriv d L W ω E u l) =
      ((spectralEdgeSplits d L l).map fun s =>
        -(spectralMSign E s.edge.1 * (W : ℂ) ^ d) *
          ∑ b : Zd d L,
            loopL d L W (HflowBlock d L W u ω) (zt E u)
              ((⟨s.pre.map Prod.fst ++ s.edge.1 :: s.post.map Prod.fst,
                  s.pre.map Prod.snd ++ s.edge.2 :: s.post.map Prod.snd⟩ :
                Loop.LoopIdx (Zd d L)).cutGlue (s.pre.length + 1) b)).sum := by
  rw [spectralWordDeriv_eq_sum_edgeTerms, Matrix.trace_list_sum]
  simp only [List.map_map, Function.comp_def, trace_spectralEdgeTerm_eq_cutGlue]

omit [NeZero L] [NeZero W] in
private theorem map_zip_fst_snd (σ : List Bool) (a : List (Zd d L))
    (h : σ.length = a.length) :
    (σ.zip a).map Prod.fst = σ ∧ (σ.zip a).map Prod.snd = a := by
  induction σ generalizing a with
  | nil =>
      have ha : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst a
      simp
  | cons s σ ih =>
      cases a with
      | nil => simp at h
      | cons b a =>
          have ht : σ.length = a.length := by simpa using h
          obtain ⟨hσ, ha⟩ := ih a ht
          simp [hσ, ha]

omit [NeZero L] [NeZero W] in
/-- A selected edge cut in a well-formed loop acts on that original loop. -/
theorem spectralEdgeSplit_cutGlue_eq (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (s : SpectralEdgeSplit d L)
    (hs : s ∈ spectralEdgeSplits d L (I.σ.zip I.a)) (b : Zd d L) :
    (⟨s.pre.map Prod.fst ++ s.edge.1 :: s.post.map Prod.fst,
       s.pre.map Prod.snd ++ s.edge.2 :: s.post.map Prod.snd⟩ :
       Loop.LoopIdx (Zd d L)).cutGlue (s.pre.length + 1) b =
      I.cutGlue (s.pre.length + 1) b := by
  have hrec := spectralEdgeSplits_reconstruct d L (I.σ.zip I.a) s hs
  have hσ := congrArg (List.map Prod.fst) hrec
  have ha := congrArg (List.map Prod.snd) hrec
  obtain ⟨hzσ, hza⟩ := map_zip_fst_snd d L I.σ I.a hI
  simp only [List.map_append, List.map_cons] at hσ ha
  rw [hzσ] at hσ
  rw [hza] at ha
  cases I with
  | mk σ a =>
      simp only at hσ ha ⊢
      rw [hσ, ha]

/-- The spectral drift of a well-formed loop is a sum of cuts of that loop. -/
theorem trace_spectralWordDeriv_eq_sum_original_cuts
    (ω : Ω d L W) (E u : ℝ) (I : Loop.LoopIdx (Zd d L)) (hI : I.WF) :
    Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a)) =
      ((spectralEdgeSplits d L (I.σ.zip I.a)).map fun s =>
        -(spectralMSign E s.edge.1 * (W : ℂ) ^ d) *
          ∑ b : Zd d L,
            loopL d L W (HflowBlock d L W u ω) (zt E u)
              (I.cutGlue (s.pre.length + 1) b)).sum := by
  rw [trace_spectralWordDeriv_eq_sum_cuts]
  congr 1
  apply List.map_congr_left
  intro s hs
  simp only [spectralEdgeSplit_cutGlue_eq d L I hI s hs]

/-! ## 2. The samplewise finite-loop cut expression -/

/-- The finite cut-loop expression at one sample, with exact second-coordinate and signed
spectral-drift coefficients; the Hessian cut coefficient is `W^d`.  The variance
parameter `g` of `SB d L g` is an extra argument. -/
noncomputable def samplewiseLoopGeneratorCuts (ω : Ω d L W) (E u : ℝ)
    (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  let l := I.σ.zip I.a
  let z := zt E u
  (W : ℂ) ^ d *
    (((edgeSplits l).map (sameEdgeCutValue d L W g u ω z)).sum +
      ((pairSplits l).map (pairCutValue d L W g u ω z)).sum) +
  ((spectralEdgeSplits d L l).map fun s =>
    -(spectralMSign E s.edge.1 * (W : ℂ) ^ d) *
      ∑ b : Zd d L,
        loopL d L W (HflowBlock d L W u ω) z
          (I.cutGlue (s.pre.length + 1) b)).sum

/-- The flow Hessian and spectral drift equal the corresponding finite cut sums.  A samplewise
algebraic statement; it does not interchange expectation and differentiation.
`g` is an extra argument (the one-size law carries the parameter `g`). -/
theorem samplewise_loop_generator_eq_cuts
    (ω : Ω d L W) {E u : ℝ} (hu : 0 < u) (_hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hI : I.WF) :
    (1 / (2 * (u : ℂ))) *
        ∑ γ : CoordF d L W,
          (((gvarF d L W g γ : ℝ) : ℂ) *
            Matrix.trace (coordinateSecondWordDeriv d L W u ω γ
              (zt E u) (I.σ.zip I.a))) +
      Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a)) =
        samplewiseLoopGeneratorCuts d L W g ω E u I := by
  have hsecond := sum_coordinateSecondWordDeriv_allCuts d L W g u hu.le ω
    (zt E u) (I.σ.zip I.a)
  have hdrift := trace_spectralWordDeriv_eq_sum_original_cuts d L W ω E u I hI
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  rw [hsecond, hdrift]
  unfold samplewiseLoopGeneratorCuts
  field_simp

/-! ## 3. The expected finite-loop cut expression -/

/-- The samplewise finite cut expression is integrable under the product Gaussian law. -/
theorem integrable_samplewiseLoopGeneratorCuts
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hI : I.WF) :
    Integrable (fun ω : Ω d L W => samplewiseLoopGeneratorCuts d L W g ω E u I)
      (PF d L W g) := by
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hη : 0 < |(zt E u).im| := abs_pos.mpr hz
  have hcoord : Integrable (fun ω : Ω d L W =>
      ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
        Matrix.trace (coordinateSecondWordDeriv d L W u ω c
          (zt E u) (I.σ.zip I.a))) (PF d L W g) := by
    apply integrable_finsetSum univ
    intro c _
    exact ((integrable_gloop_coordinate_derivatives d L W g u c hz I hI).2).smul
      (gvarF d L W g c : ℝ)
  have hspec : Integrable (fun ω : Ω d L W =>
      Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))) (PF d L W g) :=
    integrable_trace_spectralWordDeriv d L W g E u hE hu1 (I.σ.zip I.a)
  have hsum := (hcoord.smul (1 / (2 * u))).add hspec
  have hscale : ((1 / (2 * u) : ℝ) : ℂ) = 1 / (2 * (u : ℂ)) := by norm_cast
  have hfun : (fun ω : Ω d L W => samplewiseLoopGeneratorCuts d L W g ω E u I) =
      (fun ω : Ω d L W => (1 / (2 * u)) •
        (∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv d L W u ω c
            (zt E u) (I.σ.zip I.a))) +
        Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))) := by
    funext ω
    have h := samplewise_loop_generator_eq_cuts d L W g ω (E := E) hu hu1 I hI
    simpa only [Complex.real_smul, hscale] using h.symm
  rw [hfun]
  exact hsum

/-- Derivative of the expected loop as one expectation of its finite cut expression. -/
theorem deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hI : I.WF) :
    deriv (fun v : ℝ => ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W v ω) (zt E v) I ∂(PF d L W g)) u =
      ∫ ω : Ω d L W, samplewiseLoopGeneratorCuts d L W g ω E u I ∂(PF d L W g) := by
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hcoord : Integrable (fun ω : Ω d L W =>
      ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
        Matrix.trace (coordinateSecondWordDeriv d L W u ω c
          (zt E u) (I.σ.zip I.a))) (PF d L W g) := by
    apply integrable_finsetSum univ
    intro c _
    exact ((integrable_gloop_coordinate_derivatives d L W g u c hz I hI).2).smul
      (gvarF d L W g c : ℝ)
  have hspec : Integrable (fun ω : Ω d L W =>
      Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))) (PF d L W g) :=
    integrable_trace_spectralWordDeriv d L W g E u hE hu1 (I.σ.zip I.a)
  have hscaled : Integrable (fun ω : Ω d L W => (1 / (2 * u)) •
      ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
        Matrix.trace (coordinateSecondWordDeriv d L W u ω c
          (zt E u) (I.σ.zip I.a))) (PF d L W g) :=
    hcoord.smul (1 / (2 * u))
  have hscale : ((1 / (2 * u) : ℝ) : ℂ) = 1 / (2 * (u : ℂ)) := by norm_cast
  calc
    _ = (1 / (2 * u)) • ∫ ω : Ω d L W,
          ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
            Matrix.trace (coordinateSecondWordDeriv d L W u ω c
              (zt E u) (I.σ.zip I.a)) ∂(PF d L W g) +
        ∫ ω : Ω d L W,
          Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))
            ∂(PF d L W g) :=
      deriv_integral_gloop_HflowBlock_spectralZ d L W g hE hu hu1 I hI
    _ = ∫ ω : Ω d L W,
          (1 / (2 * u)) •
            (∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
              Matrix.trace (coordinateSecondWordDeriv d L W u ω c
                (zt E u) (I.σ.zip I.a))) +
          Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))
            ∂(PF d L W g) := by
      rw [integral_add hscaled hspec, integral_smul]
    _ = _ := by
      congr 1
      funext ω
      have h := samplewise_loop_generator_eq_cuts d L W g ω (E := E) hu hu1 I hI
      simpa only [Complex.real_smul, hscale] using h

/-! ## 4. The initial value of a finite Gaussian resolvent loop -/

/-- The exact deterministic initial loop value, retaining the normalized block insertions
`E_a` (entries `W^{-d}`) in `loopL`. -/
noncomputable def initialLoopValue (E : ℝ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  loopL d L W 0 ((E : ℂ) + mE E) I

/-- Explicit finite matrix product for the initial value. -/
theorem initialLoopValue_eq_trace_product (E : ℝ) (I : Loop.LoopIdx (Zd d L)) :
    initialLoopValue d L W E I =
      Matrix.trace ((I.σ.zip I.a).foldr
        (fun p M => Gres (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
          ((E : ℂ) + mE E) p.1 * Eblk d L W p.2 * M) 1) := rfl

/-! ## 5. Scalar initial values of short loops -/

omit [NeZero W] in
/-- The signed zero-matrix Green function is a scalar matrix when `z ≠ 0`. -/
theorem Gres_zero_eq_scalar (z : ℂ) (hz : z ≠ 0) (σ : Bool) :
    Gres (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ) z σ =
      (-(if σ then z else (starRingEnd ℂ) z))⁻¹ •
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  have hne : -(if σ then z else (starRingEnd ℂ) z) ≠ 0 := by
    cases σ with
    | true => simpa using hz
    | false =>
        intro hc
        have hc' := congrArg (starRingEnd ℂ) hc
        exact hz (by simpa using hc')
  have h : (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ) -
      (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (-(if σ then z else (starRingEnd ℂ) z)) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
    rw [zero_sub, neg_smul]
  unfold Gres
  rw [h, ring_inverse_smul_one hne]

/-- Each normalized block projector has trace one. -/
theorem trace_Eblk_eq_one (a : Zd d L) :
    Matrix.trace (Eblk d L W a) = 1 := trace_Eblk d L W a

/-- Scalar contributed by a signed Green factor at the initial spectral point. -/
noncomputable def initialGreenScalar (E : ℝ) (σ : Bool) : ℂ :=
  (-(if σ then (E : ℂ) + mE E
      else (starRingEnd ℂ) ((E : ℂ) + mE E)))⁻¹

private theorem initial_spectral_ne_zero {E : ℝ} (hE : |E| < 2) :
    (E : ℂ) + mE E ≠ 0 := by
  intro hz
  have hi := congrArg Complex.im hz
  have hp := spectralM_im_pos hE
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at hi
  exact (ne_of_gt hp) hi

/-- Exact one-edge initial value, including the `W^{-d}` block normalization. -/
theorem initialLoopValue_one_edge {E : ℝ} (hE : |E| < 2)
    (σ : Bool) (a : Zd d L) :
    initialLoopValue d L W E ⟨[σ], [a]⟩ = initialGreenScalar E σ := by
  rw [initialLoopValue_eq_trace_product]
  change Matrix.trace
    (Gres (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
      ((E : ℂ) + mE E) σ * Eblk d L W a * 1) = _
  rw [mul_one]
  rw [Gres_zero_eq_scalar d L W _ (initial_spectral_ne_zero hE) σ]
  simp [initialGreenScalar, trace_Eblk_eq_one]

omit [NeZero W] in
private theorem Eblk_mul_Eblk (a b : Zd d L) :
    Eblk d L W a * Eblk d L W b =
      if a = b then (((W : ℂ) ^ d)⁻¹) • Eblk d L W a else 0 := by
  unfold Eblk
  rw [diagonal_mul_diagonal]
  ext p q
  by_cases hab : a = b
  · subst hab
    simp only [ite_true, diagonal_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp_all
  · simp only [hab, ite_false, diagonal_apply, Matrix.zero_apply]
    split_ifs <;> simp_all

/-! ## 6. Arbitrary products of normalized block projectors -/

/-- Product of the normalized block projectors in a list. -/
noncomputable def blockProjectorWord (as : List (Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  as.foldr (fun a M => Eblk d L W a * M) 1

/-- The explicit product of adjacent equality indicators and `W^{-d}` factors.
The empty and singleton lists have coefficient one. -/
noncomputable def adjacentBlockWeight : List (Zd d L) → ℂ
  | [] => 1
  | [_] => 1
  | a :: b :: as =>
      (if a = b then (W : ℂ)⁻¹ ^ d else 0) *
        adjacentBlockWeight (b :: as)

/-- A nonempty block projector word is a scalar multiple of its first projector. -/
theorem blockProjectorWord_cons (a : Zd d L) (as : List (Zd d L)) :
    blockProjectorWord d L W (a :: as) =
      adjacentBlockWeight d L W (a :: as) • Eblk d L W a := by
  induction as generalizing a with
  | nil => simp [blockProjectorWord, adjacentBlockWeight]
  | cons b bs ih =>
      change Eblk d L W a * blockProjectorWord d L W (b :: bs) = _
      rw [ih b, mul_smul_comm, Eblk_mul_Eblk d L W a b]
      by_cases hab : a = b
      · simp [adjacentBlockWeight, hab, smul_smul, mul_comm, inv_pow]
      · simp [adjacentBlockWeight, hab]

/-- Trace of an arbitrary nonempty projector word, with all normalization and
equality-indicator factors explicit in `adjacentBlockWeight`. -/
theorem trace_blockProjectorWord_cons (a : Zd d L) (as : List (Zd d L)) :
    Matrix.trace (blockProjectorWord d L W (a :: as)) =
      adjacentBlockWeight d L W (a :: as) := by
  rw [blockProjectorWord_cons, Matrix.trace_smul, trace_Eblk_eq_one]
  simp

/-- At time zero, every signed Green factor can be pulled out of the matrix word. -/
theorem initial_green_word_eq_scalar_projectors {E : ℝ} (hE : |E| < 2)
    (l : List (Bool × Zd d L)) :
    l.foldr (fun p M =>
      Gres (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
        ((E : ℂ) + mE E) p.1 * Eblk d L W p.2 * M) 1 =
      (l.map fun p => initialGreenScalar E p.1).prod •
        blockProjectorWord d L W (l.map Prod.snd) := by
  induction l with
  | nil => simp [blockProjectorWord]
  | cons p l ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [Gres_zero_eq_scalar d L W _ (initial_spectral_ne_zero hE) p.1, ih]
      change ((initialGreenScalar E p.1 •
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Eblk d L W p.2) *
          ((l.map fun p => initialGreenScalar E p.1).prod •
            blockProjectorWord d L W (l.map Prod.snd)) =
        (initialGreenScalar E p.1 *
          (l.map fun p => initialGreenScalar E p.1).prod) •
            (Eblk d L W p.2 * blockProjectorWord d L W (l.map Prod.snd))
      simp only [smul_mul_assoc, one_mul, mul_smul_comm, smul_smul]
      rw [mul_comm]

/-- General nonempty initial-loop formula: the signed Green scalars multiply, and each adjacent
block-label match contributes exactly one `W^{-d}` factor. -/
theorem initialLoopValue_nonempty {E : ℝ} (hE : |E| < 2)
    (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (a : Zd d L) (as : List (Zd d L)) (ha : I.a = a :: as) :
    initialLoopValue d L W E I =
      ((I.σ.zip I.a).map fun p => initialGreenScalar E p.1).prod *
        adjacentBlockWeight d L W (a :: as) := by
  rw [initialLoopValue_eq_trace_product,
    initial_green_word_eq_scalar_projectors d L W hE,
    Matrix.trace_smul]
  have hlabels : (I.σ.zip I.a).map Prod.snd = I.a :=
    List.map_snd_zip hI.ge
  rw [hlabels, ha, trace_blockProjectorWord_cons]
  rfl

/-! ## 7. Support and normalization of the initial-loop value -/

/-- A finite block-label word contains an unequal adjacent pair. -/
def AdjacentMismatch : List (Zd d L) → Prop
  | [] => False
  | [_] => False
  | a :: b :: as => a ≠ b ∨ AdjacentMismatch (b :: as)

omit [NeZero L] [NeZero W] in
/-- A mismatched adjacent pair makes the adjacent block weight vanish. -/
theorem adjacentBlockWeight_zero_of_mismatch (as : List (Zd d L))
    (hm : AdjacentMismatch d L as) : adjacentBlockWeight d L W as = 0 := by
  induction as with
  | nil => simp [AdjacentMismatch] at hm
  | cons a as ih =>
      cases as with
      | nil => simp [AdjacentMismatch] at hm
      | cons b bs =>
          change a ≠ b ∨ AdjacentMismatch d L (b :: bs) at hm
          rcases hm with hab | htail
          · simp [adjacentBlockWeight, hab]
          · have ht := ih htail
            simp [adjacentBlockWeight, ht]

omit [NeZero L] [NeZero W] in
/-- When all labels agree, each additional projector supplies one `W^{-d}`. -/
theorem adjacentBlockWeight_all_same (a : Zd d L) (as : List (Zd d L))
    (hsame : ∀ b ∈ as, b = a) :
    adjacentBlockWeight d L W (a :: as) =
      ((W : ℂ)⁻¹ ^ d) ^ as.length := by
  induction as generalizing a with
  | nil => simp [adjacentBlockWeight]
  | cons b bs ih =>
      have hab : b = a := hsame b (by simp)
      subst b
      have hbs : ∀ c ∈ bs, c = a := by
        intro c hc
        exact hsame c (by simp [hc])
      simp only [adjacentBlockWeight, List.length_cons, pow_succ]
      rw [ih a hbs]
      simp only [ite_true]
      ring

/-! ## 8. Time continuity of finite expected loops

Continuity on a time window of any finite loop, and its bound. -/

/-- Time continuity of any finite loop, including a loop index not separately certified well
formed.  Its product uses the paired list `σ.zip a`. -/
theorem continuousOn_gloop_any_window {s t : ℝ} (hst : s ≤ t)
    (ω : Ω d L W) {z : ℝ → ℂ} (hzcont : Continuous z)
    (hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) :
    ContinuousOn (fun u : ℝ => loopL d L W (HflowBlock d L W u ω) (z u) I)
      (Set.Icc s t) := by
  let clamp : ℝ → ℝ := fun u => max s (min t u)
  have hclamp_cont : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem : ∀ u, clamp u ∈ Set.Icc s t := by
    intro u
    exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩
  have hclamp_eq : ∀ u ∈ Set.Icc s t, clamp u = u := by
    intro u hu
    simp [clamp, min_eq_right hu.2, max_eq_right hu.1]
  have hglobal : Continuous (fun u : ℝ =>
      loopL d L W (HflowBlock d L W u ω) (z (clamp u)) I) :=
    (continuous_matrixTrace d L W).comp
      (continuous_gloopProd_Hflow_time d L W ω
        (hzcont.comp hclamp_cont)
        (fun u => hzim (clamp u) (hclamp_mem u)) I)
  exact hglobal.continuousOn.congr (fun u hu => by
    change loopL d L W (HflowBlock d L W u ω) (z u) I =
      loopL d L W (HflowBlock d L W u ω) (z (clamp u)) I
    rw [hclamp_eq u hu])

/-- A uniform deterministic bound for any finite loop on a spectral window; the per-edge factor
is `η^{-1} W^{-d}`, the trace constant `card (Vtx d L W) = (W L)^d`. -/
theorem norm_gloop_any_window_le {s t η : ℝ} (hη : 0 < η)
    {z : ℝ → ℂ} (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : Loop.LoopIdx (Zd d L)) {u : ℝ} (hu : u ∈ Set.Icc s t)
    (ω : Ω d L W) :
    ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) *
        (η⁻¹ * (((W : ℝ) ^ d)⁻¹)) ^ (I.σ.zip I.a).length := by
  have ht := norm_matrix_trace_le_card_mul
    (gloopProd d L W (HflowBlock d L W u ω) (z u) I)
  have hw := norm_foldr_Gsig_Eblk_le d L W
    (HflowBlock_isHermitian d L W u ω) hη (hzlow u hu) (I.σ.zip I.a)
  calc
    ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖ ≤
        (Fintype.card (Vtx d L W) : ℝ) *
          ‖gloopProd d L W (HflowBlock d L W u ω) (z u) I‖ := ht
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end RBM.Gauss
