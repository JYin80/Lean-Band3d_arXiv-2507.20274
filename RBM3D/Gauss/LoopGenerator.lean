/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.LoopFlowStein
import RBM3D.Hierarchy.ContractionSecondLoop

/-!
# The loop generator: cut expansion, expectation, initial values (ST-1, ticket S1-06 = T2077)

Port of nine files of `RBM2D` at commit `c9a24cf` (cited `RBM2D/<File>.lean:<line>`), in the order
`Gauss/{LoopSpectralDriftCuts, LoopGeneratorSamplewise, LoopGeneratorExpectation,
LoopInitialValue, LoopInitialValueScalar, LoopInitialValueProjectionWords,
LoopInitialValueSupport}`, `Hierarchy/{LoopHierarchyCutBlockSumBound, LoopHierarchyCutContinuity}`
(only the parts that do not use the dead-code files of RBM2D, see the report), onto the merged MD
layer and S1-03/04/05.  Renaming (`docs/tickets/ST1-COMMON.md` item 2): `Z2 L` is `Zd d L`,
`BlockIndex L W` is `Vtx d L W`, `Gsig` is `Gres`, `gloop` is `loopL`, `spectralZ` is `zt`,
`spectralM` is `mE`, `Coord`/`gvar`/`P` are `CoordF`/`gvarF g`/`PF d L W g`, `LoopIdx (Z2 L)` is
`Loop.LoopIdx (Zd d L)`, `SB L` is `SB d L g`, and the exponents `W^2` become `W^d`
(`W^{-2}` becomes `W^{-d}`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace RBM.Gauss

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

variable (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)

/-! ## 1. Spectral drift as a finite sum of single-edge cuts
(`RBM2D/Gauss/LoopSpectralDriftCuts.lean`) -/

/-- A split at one signed edge of a paired loop word.
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:23` (`SpectralEdgeSplit`). -/
structure SpectralEdgeSplit (d L : ℕ) where
  pre : List (Bool × Zd d L)
  edge : Bool × Zd d L
  post : List (Bool × Zd d L)

/-- One split per signed edge, in its original list order.
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:29` (`spectralEdgeSplits`). -/
def spectralEdgeSplits : List (Bool × Zd d L) → List (SpectralEdgeSplit d L)
  | [] => []
  | p :: l => ⟨[], p, l⟩ ::
      (spectralEdgeSplits l).map fun s => ⟨p :: s.pre, s.edge, s.post⟩

omit [NeZero L] [NeZero W] in
/-- `RBM2D/Gauss/LoopSpectralDriftCuts.lean:35` (`length_spectralEdgeSplits`). -/
theorem length_spectralEdgeSplits (l : List (Bool × Zd d L)) :
    (spectralEdgeSplits d L l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [spectralEdgeSplits, ih]

omit [NeZero L] [NeZero W] in
/-- Every generated split reconstructs its original paired word.
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:42` (`spectralEdgeSplits_reconstruct`). -/
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

/-- The matrix insertion at a selected signed edge.
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:68` (`spectralEdgeTerm`). -/
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

/-- The recursive spectral derivative is the finite sum of all signed-edge insertions.
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:99` (`spectralWordDeriv_eq_sum_edgeTerms`). -/
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
`-(m_σ W^d)` (RBM2D: `-(m_σ W^2)`).
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:123` (`trace_spectralEdgeTerm_eq_cutGlue`). -/
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

/-- The traced spectral drift is the finite sum of the single-edge cut-loop sums.
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:140` (`trace_spectralWordDeriv_eq_sum_cuts`). -/
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
/-- A selected edge cut in a well-formed loop acts on that original loop.
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:170` (`spectralEdgeSplit_cutGlue_eq`). -/
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

/-- The spectral drift of a well-formed loop is a sum of cuts of that loop.
`RBM2D/Gauss/LoopSpectralDriftCuts.lean:196` (`trace_spectralWordDeriv_eq_sum_original_cuts`). -/
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

/-! ## 2. The samplewise finite-loop cut expression
(`RBM2D/Gauss/LoopGeneratorSamplewise.lean`) -/

/-- The finite cut-loop expression at one sample, with exact second-coordinate and signed
spectral-drift coefficients; the Hessian cut coefficient is `W^d` (RBM2D: `W^2`).  The variance
parameter `g` of `SB d L g` is an extra argument (paper-delta candidate `T2077a`).
`RBM2D/Gauss/LoopGeneratorSamplewise.lean:24` (`samplewiseLoopGeneratorCuts`). -/
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
`RBM2D/Gauss/LoopGeneratorSamplewise.lean:40` (`samplewise_loop_generator_eq_cuts`); `g` is an
extra argument (paper-delta candidate `T2077a`). -/
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

/-! ## 3. The expected finite-loop cut expression
(`RBM2D/Gauss/LoopGeneratorExpectation.lean`) -/

/-- The samplewise finite cut expression is integrable under the product Gaussian law.
`RBM2D/Gauss/LoopGeneratorExpectation.lean:23` (`integrable_samplewiseLoopGeneratorCuts`). -/
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

/-- Derivative of the expected loop as one expectation of its finite cut expression.
`RBM2D/Gauss/LoopGeneratorExpectation.lean:57`
(`deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts`). -/
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

/-! ## 4. The initial value of a finite Gaussian resolvent loop
(`RBM2D/Gauss/LoopInitialValue.lean`) -/

/-- At time zero the flow vanishes at every sample.
`RBM2D/Gauss/LoopInitialValue.lean:17` (`HflowBlock_zero`). -/
@[simp] theorem HflowBlock_zero (ω : Ω d L W) :
    HflowBlock d L W 0 ω = 0 := by
  rw [HflowBlock, Hflow_eq_realSmul]
  simp only [Real.sqrt_zero, zero_smul]
  exact blockMat_zero d L W

/-- The exact deterministic initial loop value, retaining the normalized block insertions
`E_a` (entries `W^{-d}`) in `loopL`.
`RBM2D/Gauss/LoopInitialValue.lean:22` (`initialLoopValue`). -/
noncomputable def initialLoopValue (E : ℝ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  loopL d L W 0 ((E : ℂ) + mE E) I

/-- Explicit finite matrix product for the initial value.
`RBM2D/Gauss/LoopInitialValue.lean:29` (`initialLoopValue_eq_trace_product`). -/
theorem initialLoopValue_eq_trace_product (E : ℝ) (I : Loop.LoopIdx (Zd d L)) :
    initialLoopValue d L W E I =
      Matrix.trace ((I.σ.zip I.a).foldr
        (fun p M => Gres (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
          ((E : ℂ) + mE E) p.1 * Eblk d L W p.2 * M) 1) := rfl

/-- Each sample has the same initial loop value.
`RBM2D/Gauss/LoopInitialValue.lean:38` (`gloop_HflowBlock_zero`). -/
theorem gloop_HflowBlock_zero (ω : Ω d L W) (E : ℝ)
    (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W (HflowBlock d L W 0 ω) (zt E 0) I =
      initialLoopValue d L W E I := by
  simp [initialLoopValue, zt]

/-- The expected finite loop starts at the deterministic zero-matrix value.
`RBM2D/Gauss/LoopInitialValue.lean:47` (`integral_gloop_HflowBlock_zero`); `g` is an extra
argument (paper-delta candidate `T2077a`). -/
theorem integral_gloop_HflowBlock_zero (E : ℝ) (I : Loop.LoopIdx (Zd d L)) :
    ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W 0 ω) (zt E 0) I ∂(PF d L W g) =
        initialLoopValue d L W E I := by
  simp only [gloop_HflowBlock_zero]
  simp

/-! ## 5. Scalar initial values of short loops
(`RBM2D/Gauss/LoopInitialValueScalar.lean`) -/

omit [NeZero W] in
/-- The signed zero-matrix Green function is a scalar matrix when `z ≠ 0`; the merged `Gres`
replaces RBM2D's `Gsig` (`RBM2D/Gauss/LoopInitialValueScalar.lean:34`, `Gsig_zero_eq_scalar`; its
`green`-form `green_zero_eq_scalar:21` is not ported, the merged loops use `Gres`). -/
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

/-- Each normalized block projector has trace one.
`RBM2D/Gauss/LoopInitialValueScalar.lean:50` (`trace_Eblk_eq_one`); the merged `trace_Eblk`. -/
theorem trace_Eblk_eq_one (a : Zd d L) :
    Matrix.trace (Eblk d L W a) = 1 := trace_Eblk d L W a

/-- Scalar contributed by a signed Green factor at the initial spectral point.
`RBM2D/Gauss/LoopInitialValueScalar.lean:63` (`initialGreenScalar`). -/
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

/-- Exact one-edge initial value, including the `W^{-d}` block normalization.
`RBM2D/Gauss/LoopInitialValueScalar.lean:76` (`initialLoopValue_one_edge`). -/
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

/-- Two block projectors have nonzero trace exactly when their labels agree; the value is
`W^{-d}` (RBM2D: `W^{-2}`).
`RBM2D/Gauss/LoopInitialValueScalar.lean:88` (`trace_Eblk_mul_Eblk`). -/
theorem trace_Eblk_mul_Eblk (a b : Zd d L) :
    Matrix.trace (Eblk d L W a * Eblk d L W b) =
      if a = b then (W : ℂ)⁻¹ ^ d else 0 := by
  rw [Eblk_mul_Eblk d L W a b]
  split_ifs <;> simp [trace_Eblk_eq_one, inv_pow]

/-- Exact two-edge initial value, with the block-label equality indicator and the weight
`W^{-d}` (RBM2D: `W^{-2}`).  No variance profile enters: the value is `s_1 s_2 1(a = b) W^{-d}`.
`RBM2D/Gauss/LoopInitialValueScalar.lean:95` (`initialLoopValue_two_edges`). -/
theorem initialLoopValue_two_edges {E : ℝ} (hE : |E| < 2)
    (σ₁ σ₂ : Bool) (a b : Zd d L) :
    initialLoopValue d L W E ⟨[σ₁, σ₂], [a, b]⟩ =
      initialGreenScalar E σ₁ * initialGreenScalar E σ₂ *
        (if a = b then (W : ℂ)⁻¹ ^ d else 0) := by
  rw [initialLoopValue_eq_trace_product]
  change Matrix.trace
    (Gres (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
      ((E : ℂ) + mE E) σ₁ * Eblk d L W a *
      (Gres 0 ((E : ℂ) + mE E) σ₂ * Eblk d L W b * 1)) = _
  rw [mul_one, Gres_zero_eq_scalar d L W _ (initial_spectral_ne_zero hE) σ₁,
    Gres_zero_eq_scalar d L W _ (initial_spectral_ne_zero hE) σ₂]
  simp [initialGreenScalar, trace_Eblk_mul_Eblk, mul_assoc]
  split_ifs <;> ring

/-! ## 6. Arbitrary products of normalized block projectors
(`RBM2D/Gauss/LoopInitialValueProjectionWords.lean`) -/

/-- Product of the normalized block projectors in a list.
`RBM2D/Gauss/LoopInitialValueProjectionWords.lean:20` (`blockProjectorWord`). -/
noncomputable def blockProjectorWord (as : List (Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  as.foldr (fun a M => Eblk d L W a * M) 1

/-- The explicit product of adjacent equality indicators and `W^{-d}` factors (RBM2D: `W^{-2}`).
The empty and singleton lists have coefficient one.
`RBM2D/Gauss/LoopInitialValueProjectionWords.lean:28` (`adjacentBlockWeight`). -/
noncomputable def adjacentBlockWeight : List (Zd d L) → ℂ
  | [] => 1
  | [_] => 1
  | a :: b :: as =>
      (if a = b then (W : ℂ)⁻¹ ^ d else 0) *
        adjacentBlockWeight (b :: as)

/-- A nonempty block projector word is a scalar multiple of its first projector.
`RBM2D/Gauss/LoopInitialValueProjectionWords.lean:38` (`blockProjectorWord_cons`). -/
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
equality-indicator factors explicit in `adjacentBlockWeight`.
`RBM2D/Gauss/LoopInitialValueProjectionWords.lean:50` (`trace_blockProjectorWord_cons`). -/
theorem trace_blockProjectorWord_cons (a : Zd d L) (as : List (Zd d L)) :
    Matrix.trace (blockProjectorWord d L W (a :: as)) =
      adjacentBlockWeight d L W (a :: as) := by
  rw [blockProjectorWord_cons, Matrix.trace_smul, trace_Eblk_eq_one]
  simp

/-- At time zero, every signed Green factor can be pulled out of the matrix word.
`RBM2D/Gauss/LoopInitialValueProjectionWords.lean:66`
(`initial_green_word_eq_scalar_projectors`). -/
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
block-label match contributes exactly one `W^{-d}` factor.
`RBM2D/Gauss/LoopInitialValueProjectionWords.lean:91` (`initialLoopValue_nonempty`). -/
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

omit [NeZero L] [NeZero W] in
/-- Three edges give the equality indicator for all three labels and `(W^{-d})^2 = W^{-2d}`
(RBM2D: `W^{-4}`: the two matching adjacent pairs each carry `W^{-d}`).
`RBM2D/Gauss/LoopInitialValueProjectionWords.lean:107` (`adjacentBlockWeight_three`). -/
theorem adjacentBlockWeight_three (a b c : Zd d L) :
    adjacentBlockWeight d L W [a, b, c] =
      if a = b ∧ b = c then ((W : ℂ)⁻¹ ^ d) ^ 2 else 0 := by
  by_cases hab : a = b <;> by_cases hbc : b = c <;>
    simp [adjacentBlockWeight, hab, hbc, pow_two]

/-! ## 7. Support and normalization of the initial-loop value
(`RBM2D/Gauss/LoopInitialValueSupport.lean`) -/

/-- A finite block-label word contains an unequal adjacent pair.
`RBM2D/Gauss/LoopInitialValueSupport.lean:18` (`AdjacentMismatch`). -/
def AdjacentMismatch : List (Zd d L) → Prop
  | [] => False
  | [_] => False
  | a :: b :: as => a ≠ b ∨ AdjacentMismatch (b :: as)

omit [NeZero L] [NeZero W] in
/-- `RBM2D/Gauss/LoopInitialValueSupport.lean:24` (`adjacentBlockWeight_zero_of_mismatch`). -/
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
/-- When all labels agree, each additional projector supplies one `W^{-d}`.
`RBM2D/Gauss/LoopInitialValueSupport.lean:41` (`adjacentBlockWeight_all_same`). -/
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

/-- The initial value vanishes as soon as two consecutive block labels differ.
`RBM2D/Gauss/LoopInitialValueSupport.lean:57` (`initialLoopValue_zero_of_adjacentMismatch`). -/
theorem initialLoopValue_zero_of_adjacentMismatch {E : ℝ} (hE : |E| < 2)
    (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (a : Zd d L) (as : List (Zd d L)) (ha : I.a = a :: as)
    (hm : AdjacentMismatch d L (a :: as)) :
    initialLoopValue d L W E I = 0 := by
  rw [initialLoopValue_nonempty d L W hE I hI a as ha,
    adjacentBlockWeight_zero_of_mismatch d L W (a :: as) hm, mul_zero]

/-- With constant block label, a length `n` loop carries `W^{-d(n-1)}` (RBM2D: `W^{-2(n-1)}`).
`RBM2D/Gauss/LoopInitialValueSupport.lean:70` (`initialLoopValue_all_same`). -/
theorem initialLoopValue_all_same {E : ℝ} (hE : |E| < 2)
    (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (a : Zd d L) (as : List (Zd d L)) (ha : I.a = a :: as)
    (hsame : ∀ b ∈ as, b = a) :
    initialLoopValue d L W E I =
      ((I.σ.zip I.a).map fun p => initialGreenScalar E p.1).prod *
        (W : ℂ)⁻¹ ^ (d * as.length) := by
  rw [initialLoopValue_nonempty d L W hE I hI a as ha,
    adjacentBlockWeight_all_same d L W a as hsame]
  rw [← pow_mul]

/-! ## 8. Block-label sums of finite cut-loop bounds
(`RBM2D/Hierarchy/LoopHierarchyCutBlockSumBound.lean`)

Ported: the envelope.  `sum_norm_SB_row` (RBM2D `:30`) is the merged
`RBM.sum_norm_SB_row d L g hL a`
(`Defs/Block.lean:118`, same statement, namespace `RBM`) and is not restated, to avoid a second
name `RBM.Gauss.sum_norm_SB_row` that would make `sum_norm_SB_row` ambiguous in `namespace
RBM.Gauss`.  The two double-sum bounds (`:38`, `:78`) are stated through
`sameEdgeCutIntegrand`/`pairCutIntegrand`, defined in the dead-code RBM2D file
`Hierarchy/ContractionSecondLoopExpectedCuts` (portmap class d), and are not ported. -/

/-- The exact crude resolvent-loop envelope: one dimension factor and one normalized projector
factor `W^{-d}` per Green edge.
`RBM2D/Hierarchy/LoopHierarchyCutBlockSumBound.lean:25` (`cutResolventEnvelope`). -/
noncomputable def cutResolventEnvelope (η : ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (Vtx d L W) : ℝ) *
    (η⁻¹ * (((W : ℝ) ^ d)⁻¹)) ^ n

/-! ## 9. Time continuity of finite expected loops
(`RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean`)

Ported: the two lemmas on a single loop and the four dominated-continuity theorems that use only
them.  The theorems on `sameEdgeCutIntegrand`, `pairCutIntegrand`, `expectedSameEdgeCuts`,
`expectedPairCuts`, `expectedSpectralCuts`, `expectedLoopCutRHS` and
`expected_gloop_hierarchy_integral_unconditional` (RBM2D `:142`-`:228` and `:277`-`:321`) use
the definitions of the dead-code files `Hierarchy/{ContractionSecondLoopExpectedCuts,
LoopHierarchyGenerator, LoopHierarchyIntegral}` and are not ported. -/

/-- Time continuity of any finite loop, including a loop index not separately certified well
formed.  Its product uses the paired list `σ.zip a`.
`RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean:26` (`continuousOn_gloop_any_window`). -/
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
is `η^{-1} W^{-d}` (RBM2D: `η^{-1} W^{-2}`), the trace constant `card (Vtx d L W) = (W L)^d`.
`RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean:53` (`norm_gloop_any_window_le`). -/
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

/-- Dominated continuity for the expectation of a product of two finite loops.
`RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean:71` (`continuousOn_integral_gloop_product_window`);
`g` is an extra argument (paper-delta candidate `T2077a`). -/
theorem continuousOn_integral_gloop_product_window {s t η : ℝ}
    (hst : s ≤ t) (hη : 0 < η) {z : ℝ → ℂ}
    (hzcont : Continuous z)
    (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I J : Loop.LoopIdx (Zd d L)) (k : ℂ) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W u ω) (z u) I * k *
        loopL d L W (HflowBlock d L W u ω) (z u) J ∂(PF d L W g))
      (Set.Icc s t) := by
  let C (K : Loop.LoopIdx (Zd d L)) : ℝ :=
    (Fintype.card (Vtx d L W) : ℝ) *
      (η⁻¹ * (((W : ℝ) ^ d)⁻¹)) ^ (K.σ.zip K.a).length
  let B : ℝ := C I * ‖k‖ * C J
  have hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0 := by
    intro u hu
    exact abs_pos.mp (hη.trans_le (hzlow u hu))
  have hmeas : ∀ u ∈ Set.Icc s t,
      AEStronglyMeasurable (fun ω : Ω d L W =>
        loopL d L W (HflowBlock d L W u ω) (z u) I * k *
          loopL d L W (HflowBlock d L W u ω) (z u) J) (PF d L W g) := by
    intro u hu
    have hK (K : Loop.LoopIdx (Zd d L)) :
        Continuous (fun ω : Ω d L W =>
          loopL d L W (HflowBlock d L W u ω) (z u) K) :=
      (continuous_matrixTrace d L W).comp
        (continuous_gloopProd_HflowBlock_sample d L W u (hzim u hu) K)
    exact (((hK I).mul continuous_const).mul (hK J)).measurable.aestronglyMeasurable
  have hbound : ∀ u ∈ Set.Icc s t, ∀ᵐ ω ∂(PF d L W g),
      ‖loopL d L W (HflowBlock d L W u ω) (z u) I * k *
        loopL d L W (HflowBlock d L W u ω) (z u) J‖ ≤ B := by
    intro u hu
    exact Filter.Eventually.of_forall fun ω => by
      have hI := norm_gloop_any_window_le d L W hη hzlow I hu ω
      have hJ := norm_gloop_any_window_le d L W hη hzlow J hu ω
      calc
        ‖loopL d L W (HflowBlock d L W u ω) (z u) I * k *
            loopL d L W (HflowBlock d L W u ω) (z u) J‖ ≤
            ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖ * ‖k‖ *
              ‖loopL d L W (HflowBlock d L W u ω) (z u) J‖ := by
                exact (norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ B := by
          dsimp [B]
          gcongr
  have hcont : ∀ᵐ ω ∂(PF d L W g), ContinuousOn (fun u : ℝ =>
      loopL d L W (HflowBlock d L W u ω) (z u) I * k *
        loopL d L W (HflowBlock d L W u ω) (z u) J) (Set.Icc s t) :=
    Filter.Eventually.of_forall fun ω =>
      ((continuousOn_gloop_any_window d L W hst ω hzcont hzim I).mul
        continuousOn_const).mul
        (continuousOn_gloop_any_window d L W hst ω hzcont hzim J)
  exact MeasureTheory.continuousOn_of_dominated hmeas hbound
    (integrable_const B) hcont

/-- Specialization to the spectral path on a compact interior time window.
`RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean:126`
(`continuousOn_integral_gloop_product_spectralZ`);
`g` is an extra argument (paper-delta candidate `T2077a`). -/
theorem continuousOn_integral_gloop_product_spectralZ
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I J : Loop.LoopIdx (Zd d L)) (k : ℂ) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W u ω) (zt E u) I * k *
        loopL d L W (HflowBlock d L W u ω) (zt E u) J ∂(PF d L W g))
      (Set.Icc a b) := by
  let η : ℝ := (1 - b) * (mE E).im
  have hη : 0 < η := mul_pos (by linarith) (spectralM_im_pos hE)
  have hlow : ∀ u ∈ Set.Icc a b, η ≤ |(zt E u).im| := by
    intro u hu
    exact spectralZ_im_gap hE hb hu
  exact continuousOn_integral_gloop_product_window d L W g hab hη
    (continuous_spectralZ E) hlow I J k

/-- Dominated continuity for a single expected finite loop.
`RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean:229` (`continuousOn_integral_gloop_window`);
`g` is an extra argument (paper-delta candidate `T2077a`). -/
theorem continuousOn_integral_gloop_window {s t η : ℝ}
    (hst : s ≤ t) (hη : 0 < η) {z : ℝ → ℂ}
    (hzcont : Continuous z)
    (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : Loop.LoopIdx (Zd d L)) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W u ω) (z u) I ∂(PF d L W g))
      (Set.Icc s t) := by
  let B : ℝ := (Fintype.card (Vtx d L W) : ℝ) *
    (η⁻¹ * (((W : ℝ) ^ d)⁻¹)) ^ (I.σ.zip I.a).length
  have hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0 := by
    intro u hu
    exact abs_pos.mp (hη.trans_le (hzlow u hu))
  have hmeas : ∀ u ∈ Set.Icc s t,
      AEStronglyMeasurable (fun ω : Ω d L W =>
        loopL d L W (HflowBlock d L W u ω) (z u) I) (PF d L W g) := by
    intro u hu
    exact ((continuous_matrixTrace d L W).comp
      (continuous_gloopProd_HflowBlock_sample d L W u (hzim u hu) I)).measurable
      |>.aestronglyMeasurable
  have hbound : ∀ u ∈ Set.Icc s t, ∀ᵐ ω ∂(PF d L W g),
      ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖ ≤ B := by
    intro u hu
    exact Filter.Eventually.of_forall fun ω =>
      norm_gloop_any_window_le d L W hη hzlow I hu ω
  have hcont : ∀ᵐ ω ∂(PF d L W g), ContinuousOn (fun u : ℝ =>
      loopL d L W (HflowBlock d L W u ω) (z u) I) (Set.Icc s t) :=
    Filter.Eventually.of_forall fun ω =>
      continuousOn_gloop_any_window d L W hst ω hzcont hzim I
  exact MeasureTheory.continuousOn_of_dominated hmeas hbound
    (integrable_const B) hcont

/-- Continuity of the expectation of any fixed cut loop along the spectral path.
`RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean:261` (`continuousOn_integral_gloop_spectralZ`);
`g` is an extra argument (paper-delta candidate `T2077a`). -/
theorem continuousOn_integral_gloop_spectralZ
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I : Loop.LoopIdx (Zd d L)) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W u ω) (zt E u) I ∂(PF d L W g))
      (Set.Icc a b) := by
  let η : ℝ := (1 - b) * (mE E).im
  have hη : 0 < η := mul_pos (by linarith) (spectralM_im_pos hE)
  have hlow : ∀ u ∈ Set.Icc a b, η ≤ |(zt E u).im| := by
    intro u hu
    exact spectralZ_im_gap hE hb hu
  exact continuousOn_integral_gloop_window d L W g hab hη
    (continuous_spectralZ E) hlow I

/-! ## 10. Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `N = (W L)^d = 216`)

Every deterministic hypothesis is discharged at `E = 3/10` (`|E| < 2`), `u = 1/2` (`0 < u < 1`),
the window `[1/4, 3/4]` (`0 < 1/4 ≤ 3/4 < 1`), `g = 1` and the well-formed 2-loop with charges
`(+, -)` and distinct block labels `(0,0,0)`, `(1,2,0)` of `Z_3^3` (27 blocks of `W^d = 8` sites,
216 vertices, 46656 real coordinates); the initial-value theorems at labels `(0,0,0)` (equal) and a
3-loop with three equal labels. -/

section Instances

/-- A 2-loop with charges `(+, -)` and two distinct block labels of `Z_3^3`. -/
private def genLoop : Loop.LoopIdx (Zd 3 3) :=
  ⟨[true, false], [![0, 0, 0], ![1, 2, 0]]⟩

private theorem genLoop_wf : genLoop.WF := rfl

/-- A 3-loop with charges `(+, -, +)` and three equal block labels. -/
private def genLoop3 : Loop.LoopIdx (Zd 3 3) :=
  ⟨[true, false, true], [![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]⟩

private theorem genLoop3_wf : genLoop3.WF := rfl

private theorem gen_hE : |(3 / 10 : ℝ)| < 2 := by norm_num [abs_lt]

private theorem gen_hzim (u : ℝ) (hu : u ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)) :
    (zt (3 / 10) u).im ≠ 0 := by
  rw [spectralZ_im]
  exact ne_of_gt (mul_pos (by linarith [hu.2]) (spectralM_im_pos gen_hE))

/-- **Instance of `trace_spectralWordDeriv_eq_sum_original_cuts`** at every sample. -/
example (ω : Ω 3 3 2) :
    Matrix.trace (spectralWordDeriv 3 3 2 ω (3 / 10) (1 / 2) (genLoop.σ.zip genLoop.a)) =
      ((spectralEdgeSplits 3 3 (genLoop.σ.zip genLoop.a)).map fun s =>
        -(spectralMSign (3 / 10) s.edge.1 * (2 : ℂ) ^ 3) *
          ∑ b : Zd 3 3,
            loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) (zt (3 / 10) (1 / 2))
              (genLoop.cutGlue (s.pre.length + 1) b)).sum := by
  simpa using trace_spectralWordDeriv_eq_sum_original_cuts 3 3 2 ω (3 / 10) (1 / 2)
    genLoop genLoop_wf

/-- **Instance of `samplewise_loop_generator_eq_cuts`** at every sample, `g = 1`. -/
example (ω : Ω 3 3 2) :
    (1 / (2 * ((1 / 2 : ℝ) : ℂ))) *
        ∑ γ : CoordF 3 3 2,
          (((gvarF 3 3 2 1 γ : ℝ) : ℂ) *
            Matrix.trace (coordinateSecondWordDeriv 3 3 2 (1 / 2) ω γ
              (zt (3 / 10) (1 / 2)) (genLoop.σ.zip genLoop.a))) +
      Matrix.trace (spectralWordDeriv 3 3 2 ω (3 / 10) (1 / 2) (genLoop.σ.zip genLoop.a)) =
        samplewiseLoopGeneratorCuts 3 3 2 1 ω (3 / 10) (1 / 2) genLoop :=
  samplewise_loop_generator_eq_cuts 3 3 2 1 ω (E := 3 / 10) (u := 1 / 2) (by norm_num)
    (by norm_num) genLoop genLoop_wf

/-- **Instance of `integrable_samplewiseLoopGeneratorCuts`** under `PF 3 3 2 1`. -/
example : Integrable (fun ω : Ω 3 3 2 => samplewiseLoopGeneratorCuts 3 3 2 1 ω (3 / 10) (1 / 2)
    genLoop) (PF 3 3 2 1) :=
  integrable_samplewiseLoopGeneratorCuts 3 3 2 1 gen_hE (by norm_num) (by norm_num) genLoop
    genLoop_wf

/-- **Instance of `deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts`**:
`d/du E 𝓛_u |_{u = 1/2}` under `PF 3 3 2 1`. -/
example :
    deriv (fun v : ℝ => ∫ ω : Ω 3 3 2,
      loopL 3 3 2 (HflowBlock 3 3 2 v ω) (zt (3 / 10) v) genLoop ∂(PF 3 3 2 1)) (1 / 2) =
      ∫ ω : Ω 3 3 2, samplewiseLoopGeneratorCuts 3 3 2 1 ω (3 / 10) (1 / 2) genLoop
        ∂(PF 3 3 2 1) :=
  deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts 3 3 2 1 gen_hE (by norm_num)
    (by norm_num) genLoop genLoop_wf

/-- **Instance of `integral_gloop_HflowBlock_zero`** under `PF 3 3 2 1`. -/
example :
    ∫ ω : Ω 3 3 2, loopL 3 3 2 (HflowBlock 3 3 2 0 ω) (zt (3 / 10) 0) genLoop ∂(PF 3 3 2 1) =
      initialLoopValue 3 3 2 (3 / 10) genLoop :=
  integral_gloop_HflowBlock_zero 3 3 2 1 (3 / 10) genLoop

/-- **Instance of `initialLoopValue_two_edges`** at equal labels: the value is
`s_+ s_- W^{-d}` with `W^{-d} = (1/2)^3`, a nonzero number. -/
example :
    initialLoopValue 3 3 2 (3 / 10) ⟨[true, false], [![0, 0, 0], ![0, 0, 0]]⟩ =
      initialGreenScalar (3 / 10) true * initialGreenScalar (3 / 10) false *
        ((2 : ℂ)⁻¹) ^ 3 := by
  rw [initialLoopValue_two_edges 3 3 2 gen_hE]
  simp

/-- **Instance of `initialLoopValue_two_edges`** at distinct labels: the value is zero. -/
example : initialLoopValue 3 3 2 (3 / 10) genLoop = 0 := by
  have h := initialLoopValue_two_edges 3 3 2 (E := 3 / 10) gen_hE true false ![0, 0, 0] ![1, 2, 0]
  rw [show genLoop = ⟨[true, false], [![0, 0, 0], ![1, 2, 0]]⟩ from rfl, h]
  have hne : (![0, 0, 0] : Zd 3 3) ≠ ![1, 2, 0] := by
    intro hc
    have := congrFun hc 0
    simp at this
  simp [hne]

/-- **Instance of `adjacentBlockWeight_three`** at three equal labels: `(W^{-d})^2 = (1/2)^6`. -/
example : adjacentBlockWeight 3 3 2 [(![0, 0, 0] : Zd 3 3), ![0, 0, 0], ![0, 0, 0]] =
    (((2 : ℂ)⁻¹) ^ 3) ^ 2 := by
  rw [adjacentBlockWeight_three 3 3 2]
  simp

/-- **Instance of `initialLoopValue_all_same`**: a 3-loop with three equal labels carries
`W^{-d(n-1)} = (1/2)^6`. -/
example :
    initialLoopValue 3 3 2 (3 / 10) genLoop3 =
      ((genLoop3.σ.zip genLoop3.a).map fun p => initialGreenScalar (3 / 10) p.1).prod *
        (2 : ℂ)⁻¹ ^ (3 * 2) := by
  have h := initialLoopValue_all_same 3 3 2 (E := 3 / 10) gen_hE genLoop3 genLoop3_wf
    ![0, 0, 0] [![0, 0, 0], ![0, 0, 0]] rfl (by simp)
  simpa using h

/-- **Instance of `continuousOn_gloop_any_window`**: at every sample, on `[1/4, 3/4]`. -/
example (ω : Ω 3 3 2) :
    ContinuousOn (fun u : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (3 / 10) u) genLoop)
      (Set.Icc (1 / 4) (3 / 4)) :=
  continuousOn_gloop_any_window 3 3 2 (by norm_num) ω (continuous_spectralZ (3 / 10))
    gen_hzim genLoop

/-- **Instance of `norm_gloop_any_window_le`** at `u = 1/2` in the window `[1/4, 3/4]`, with the
gap `η = (1 - 3/4) Im m(3/10) > 0`. -/
example (ω : Ω 3 3 2) :
    ‖loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) (zt (3 / 10) (1 / 2)) genLoop‖ ≤
      (Fintype.card (Vtx 3 3 2) : ℝ) *
        (((1 - 3 / 4) * (mE (3 / 10)).im)⁻¹ * (((2 : ℝ) ^ 3)⁻¹)) ^
          (genLoop.σ.zip genLoop.a).length :=
  norm_gloop_any_window_le 3 3 2 (s := 1 / 4) (t := 3 / 4)
    (mul_pos (by norm_num) (spectralM_im_pos gen_hE)) (z := zt (3 / 10))
    (fun _ hu => spectralZ_im_gap gen_hE (by norm_num) hu) genLoop
    (u := 1 / 2) (by norm_num [Set.mem_Icc]) ω

/-- **Instance of `continuousOn_integral_gloop_product_spectralZ`** (`k = 1`), under
`PF 3 3 2 1`. -/
example :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω 3 3 2,
      loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (3 / 10) u) genLoop * 1 *
        loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (3 / 10) u) genLoop3 ∂(PF 3 3 2 1))
      (Set.Icc (1 / 4) (3 / 4)) :=
  continuousOn_integral_gloop_product_spectralZ 3 3 2 1 gen_hE (by norm_num) (by norm_num)
    genLoop genLoop3 1

/-- **Instance of `continuousOn_integral_gloop_spectralZ`** under `PF 3 3 2 1`. -/
example :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω 3 3 2,
      loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (3 / 10) u) genLoop ∂(PF 3 3 2 1))
      (Set.Icc (1 / 4) (3 / 4)) :=
  continuousOn_integral_gloop_spectralZ 3 3 2 1 gen_hE (by norm_num) (by norm_num) genLoop

end Instances

end RBM.Gauss
