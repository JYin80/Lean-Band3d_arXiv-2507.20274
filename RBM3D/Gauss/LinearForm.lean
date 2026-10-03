/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.FineModel
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw

/-!
# Linear forms in the Gaussian coordinates of the sequence-level sample

Ticket T2006 (MD-1).  The coordinates of `Sizes.seqP sz` are independent centred Gaussians
(`seqP` is an infinite product), so a finite real linear combination of them is again a centred
Gaussian, with variance the weighted sum of the coordinate variances.

Port of `RBM2D/Gauss/LinearForm.lean` (RBM2D commit `c9a24cf`, lines 1-282; the whole file, the
`#print axioms` lines removed), with the renaming rule R1: `Sizes.SeqCoord d` becomes
`Sizes.SeqCoord sz` for `sz : Sizes d`.  The checks in `section AtSz0` (applications at the
admissible `d = 3` sequence `SizesInst.sz0`) are new.  The RBM2D file is itself a port of
`RBM1D/Gauss/LinearForm.lean` (its own header: RBM1D commit `86573b9`, lines 1-137 and 210-303,
without the three moment lemmas `integrable_pow_lin`, `integral_pow_lin`,
`integral_sq_add_sq_pow_le`).  The lemmas are generic: no exponent and no dimension enters.

## Main statements

* `RBM.Gauss.LinearForm.iIndepFun_coord` : the coordinates are independent
* `RBM.Gauss.LinearForm.hasLaw_coord` : each coordinate is `N(0, seqGvar c)`
* `RBM.Gauss.LinearForm.hasLaw_const_mul_coord` : `a · ω c` is `N(0, a² seqGvar c)`
* `RBM.Gauss.LinearForm.map_sum_const_mul_coord` : a finite linear form is a centred Gaussian
-/

namespace RBM.Gauss.LinearForm

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-- **The coordinates are independent.**  `seqP` is an infinite product measure. -/
theorem iIndepFun_coord :
    iIndepFun (fun (c : Sizes.SeqCoord sz) (ω : Sizes.SeqΩ sz) => ω c) (Sizes.seqP sz) := by
  have := iIndepFun_infinitePi
    (P := fun c : Sizes.SeqCoord sz => gaussianReal 0 (Sizes.seqGvar sz c))
    (X := fun _ x => x) (fun _ => measurable_id)
  simpa [Sizes.seqP] using this

/-- Each coordinate is a centred Gaussian of variance `seqGvar sz c`. -/
theorem hasLaw_coord (c : Sizes.SeqCoord sz) :
    HasLaw (fun ω : Sizes.SeqΩ sz => ω c) (gaussianReal 0 (Sizes.seqGvar sz c)) (Sizes.seqP sz) :=
  ⟨measurable_pi_apply c |>.aemeasurable, Sizes.seqP_map_eval sz c⟩

/-- A scaled coordinate is a centred Gaussian of variance `a² seqGvar sz c`. -/
theorem hasLaw_const_mul_coord (a : ℝ) (c : Sizes.SeqCoord sz) :
    HasLaw (fun ω : Sizes.SeqΩ sz => a * ω c)
      (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg _) * Sizes.seqGvar sz c)) (Sizes.seqP sz) := by
  refine ⟨((measurable_const.mul (measurable_pi_apply c)).aemeasurable), ?_⟩
  have h : (Sizes.seqP sz).map (fun ω : Sizes.SeqΩ sz => a * ω c)
      = ((Sizes.seqP sz).map (fun ω : Sizes.SeqΩ sz => ω c)).map (fun x : ℝ => a * x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h, Sizes.seqP_map_eval sz c, gaussianReal_map_const_mul a]
  simp

section General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [DecidableEq ι]

set_option linter.unusedDecidableInType false in
/-- **A finite real linear form in an independent Gaussian family is a centred Gaussian**, with
variance `∑ a_i² v_i`.  Induction on the finite set: a scaled variable is independent of the sum
of the others, and Gaussians convolve. -/
theorem map_sum_const_mul_of_indep {X : ι → Ω → ℝ} {v : ι → ℝ≥0} (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P) (a : ι → ℝ)
    (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω)
      = gaussianReal 0 (∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
  classical
  have hmul : ∀ i, Measurable (fun ω => a i * X i ω) := fun i => (hmeas i).const_mul _
  have hindep' : iIndepFun (fun i ω => a i * X i ω) P :=
    hindep.comp (fun i => fun x : ℝ => a i * x) fun _ => by fun_prop
  have hlaw' : ∀ i, P.map (fun ω => a i * X i ω)
      = gaussianReal 0 (NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
    intro i
    have h : P.map (fun ω => a i * X i ω) = (P.map (X i)).map (fun x : ℝ => a i * x) := by
      rw [Measure.map_map (by fun_prop) (hmeas i)]
      rfl
    rw [h, hlaw i, gaussianReal_map_const_mul (a i)]
    simp
  induction s using Finset.induction with
  | empty => simp [Measure.map_const]
  | insert i₀ s hi₀ ih =>
    have hsum : Measurable (fun ω => ∑ i ∈ s, a i * X i ω) :=
      Finset.measurable_sum _ fun i _ => hmul i
    have hindep0 := hindep'.indepFun_finsetSum_of_notMem (fun i => hmul i) hi₀
    have hfun : (∑ j ∈ s, fun ω => a j * X j ω) = fun ω => ∑ i ∈ s, a i * X i ω := by
      funext ω
      simp [Finset.sum_apply]
    rw [hfun] at hindep0
    have hadd : (fun ω => ∑ i ∈ insert i₀ s, a i * X i ω)
        = (fun ω => a i₀ * X i₀ ω) + (fun ω => ∑ i ∈ s, a i * X i ω) := by
      funext ω
      simp [Finset.sum_insert hi₀]
    rw [hadd, (hindep0.symm).map_add_eq_map_conv_map (hmul i₀) hsum, ih, hlaw' i₀,
      gaussianReal_conv_gaussianReal, Finset.sum_insert hi₀]
    simp

end General

/-- The family of scaled coordinates is independent. -/
theorem iIndepFun_const_mul_coord (a : Sizes.SeqCoord sz → ℝ) :
    iIndepFun (fun (c : Sizes.SeqCoord sz) (ω : Sizes.SeqΩ sz) => a c * ω c) (Sizes.seqP sz) :=
  (iIndepFun_coord sz).comp (fun c => fun x : ℝ => a c * x) fun _ => by fun_prop

/-- **A finite real linear form in the coordinates is a centred Gaussian**, with variance the
weighted sum `∑ a_c² v_c`. -/
theorem map_sum_const_mul_coord (a : Sizes.SeqCoord sz → ℝ) (s : Finset (Sizes.SeqCoord sz)) :
    (Sizes.seqP sz).map (fun ω : Sizes.SeqΩ sz => ∑ c ∈ s, a c * ω c)
      = gaussianReal 0 (∑ c ∈ s, NNReal.mk (a c ^ 2) (sq_nonneg _) * Sizes.seqGvar sz c) :=
  map_sum_const_mul_of_indep (fun c => measurable_pi_apply c) (fun c => Sizes.seqP_map_eval sz c)
    (iIndepFun_coord sz) a s

section MomentBound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [DecidableEq ι] {X : ι → Ω → ℝ} {v : ι → ℝ≥0}

/-- The variance of the linear form `∑ a_i X_i`. -/
noncomputable def linVar (v : ι → ℝ≥0) (a : ι → ℝ) (s : Finset ι) : ℝ≥0 :=
  ∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i

variable (hmeas : ∀ i, Measurable (X i)) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
  (hindep : iIndepFun X P)
include hmeas hlaw hindep

omit [IsProbabilityMeasure P] [DecidableEq ι] hlaw hindep in
theorem measurable_lin (a : ι → ℝ) (s : Finset ι) :
    Measurable fun ω => ∑ i ∈ s, a i * X i ω :=
  Finset.measurable_sum _ fun i _ => (hmeas i).const_mul _

set_option linter.unusedDecidableInType false in
/-- The law of the linear form, in terms of `linVar`. -/
theorem map_lin (a : ι → ℝ) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω) = gaussianReal 0 (linVar v a s) :=
  map_sum_const_mul_of_indep hmeas hlaw hindep a s

end MomentBound

section Block

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Conditioning on an independent block.**  If `U` and `V` are independent, an integral of
`F(U, V)` is the iterated integral against their laws: the outer variable `V` may be frozen and
the inner integral computed against the law of `U` alone. -/
theorem integral_indep_pair {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ} (hF : Integrable F ((P.map U).prod (P.map V))) :
    ∫ ω, F (U ω, V ω) ∂P = ∫ y, (∫ x, F (x, y) ∂(P.map U)) ∂(P.map V) := by
  have hpair : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 h
  have hmap := integral_map (μ := P) (φ := fun ω => (U ω, V ω)) (f := F)
    (hU.prodMk hV).aemeasurable (by rw [hpair]; exact hF.aestronglyMeasurable)
  rw [hpair] at hmap
  rw [← hmap, integral_prod_symm F hF]

/-- The same, as an upper bound: a uniform bound on the inner (conditional) integral gives a
bound on the whole integral. -/
theorem integral_indep_pair_le {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ} (hF : Integrable F ((P.map U).prod (P.map V)))
    {g : β → ℝ} (hg : Integrable g (P.map V))
    (hbound : ∀ᵐ y ∂(P.map V), (∫ x, F (x, y) ∂(P.map U)) ≤ g y) :
    ∫ ω, F (U ω, V ω) ∂P ≤ ∫ y, g y ∂(P.map V) := by
  rw [integral_indep_pair hU hV h hF]
  exact integral_mono_ae hF.integral_prod_right hg hbound

/-- **Tonelli across an independent pair.**  For a nonnegative measurable `F`, no integrability
is needed: the integral of `F(U, V)` is the iterated integral against the two laws.  This is what
lets the conditional bound be proved without assuming integrability first. -/
theorem lintegral_indep_pair {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (U ω, V ω) ∂P = ∫⁻ y, (∫⁻ x, F (x, y) ∂(P.map U)) ∂(P.map V) := by
  have hpair : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 h
  rw [← lintegral_map hF (hU.prodMk hV), hpair, lintegral_prod_symm' F hF]

set_option linter.unusedSectionVars false in
set_option linter.overlappingInstances false in
/-- The same, as an upper bound from a bound on the inner (conditional) integral. -/
theorem lintegral_indep_pair_le {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ≥0∞} (hF : Measurable F) {c : ℝ≥0∞}
    (hbound : ∀ y, (∫⁻ x, F (x, y) ∂(P.map U)) ≤ c) [IsProbabilityMeasure P] :
    ∫⁻ ω, F (U ω, V ω) ∂P ≤ c := by
  rw [lintegral_indep_pair hU hV h hF]
  calc ∫⁻ y, (∫⁻ x, F (x, y) ∂(P.map U)) ∂(P.map V)
      ≤ ∫⁻ _y, c ∂(P.map V) := lintegral_mono hbound
    _ = c := by
        rw [lintegral_const]
        simp

end Block

section Glue

variable {ι : Type*} [DecidableEq ι]

/-- Glue two coordinate blocks into a full sample point, filling the rest with `0`. -/
def glue (S T : Finset ι) (p : (S → ℝ) × (T → ℝ)) : ι → ℝ := fun c =>
  if h : c ∈ S then p.1 ⟨c, h⟩ else if h' : c ∈ T then p.2 ⟨c, h'⟩ else 0

theorem measurable_glue (S T : Finset ι) : Measurable (glue S T) := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ S
  · simpa [glue, h] using (measurable_fst.eval : Measurable fun p : (S → ℝ) × (T → ℝ) => p.1 _)
  · by_cases h' : c ∈ T
    · simpa [glue, h, h'] using
        (measurable_snd.eval : Measurable fun p : (S → ℝ) × (T → ℝ) => p.2 _)
    · simp only [glue, h, h', ↓reduceDIte]
      exact measurable_const

/-- Gluing the two blocks of `ω` back together reproduces `ω` on `S ∪ T`. -/
theorem glue_agree (S T : Finset ι) (ω : ι → ℝ) {c : ι} (hc : c ∈ S ∪ T) :
    glue S T ((fun c : S => ω c), (fun c : T => ω c)) c = ω c := by
  simp only [glue]
  by_cases h : c ∈ S
  · simp [h]
  · have h' : c ∈ T := by
      rcases Finset.mem_union.1 hc with h'' | h''
      · exact absurd h'' h
      · exact h''
    simp [h, h']

/-- **A quantity that reads only `S ∪ T` is a function of the two blocks.**  This is the shape
required by `integral_indep_pair`. -/
theorem eq_glue_of_congr {V : Type*} (S T : Finset ι) (g : (ι → ℝ) → V)
    (hg : ∀ ω ω' : ι → ℝ, (∀ c ∈ S ∪ T, ω c = ω' c) → g ω = g ω') (ω : ι → ℝ) :
    g ω = (fun p => g (glue S T p)) ((fun c : S => ω c), (fun c : T => ω c)) :=
  hg _ _ fun _ hc => (glue_agree S T ω hc).symm

end Glue

section Checks

/-- Concrete sizes at `d = 3`: `L n = W n = n + 3` and the coupling `lam n = 1/2`. -/
private noncomputable def checkSizes : Sizes 3 where
  L n := n + 3
  W n := n + 3
  lam _ := 1 / 2
  three_le_L n := by omega
  W_pos n := by omega

/-- `map_sum_const_mul_coord` at the concrete sizes `checkSizes`, with two diagonal coordinates at
sizes `n = 0` and `n = 1` (so `c₀ ≠ c₁`) and weights `1`, `2`. -/
private theorem check_map_sum_const_mul_coord :
    ∃ (c₀ c₁ : Sizes.SeqCoord checkSizes) (a : Sizes.SeqCoord checkSizes → ℝ),
      c₀ ≠ c₁ ∧ a c₀ = 1 ∧ a c₁ = 2 ∧
      (Sizes.seqP checkSizes).map
          (fun ω : Sizes.SeqΩ checkSizes => ∑ c ∈ ({c₀, c₁} : Finset _), a c * ω c)
        = gaussianReal 0 (∑ c ∈ ({c₀, c₁} : Finset _),
            NNReal.mk (a c ^ 2) (sq_nonneg _) * Sizes.seqGvar checkSizes c) := by
  classical
  let c₀ : Sizes.SeqCoord checkSizes := ⟨0, (0, 0, true)⟩
  let c₁ : Sizes.SeqCoord checkSizes := ⟨1, (0, 0, true)⟩
  have h01 : c₀ ≠ c₁ := fun h => by
    have := congrArg Sigma.fst h
    simp [c₀, c₁] at this
  refine ⟨c₀, c₁, fun c => if c = c₀ then 1 else if c = c₁ then 2 else 0, h01, by simp, ?_, ?_⟩
  · simp [h01.symm]
  · exact map_sum_const_mul_coord checkSizes _ _

/-- The main statements at the admissible `d = 3` sequence `SizesInst.sz0`: the coordinates are
independent, each is a centred Gaussian of variance `seqGvar`, a scaled coordinate has variance
`a² seqGvar`, the scaled coordinates are independent, and a finite real linear form is a centred
Gaussian with the weighted variance. -/
example (a : ℝ) (c : Sizes.SeqCoord SizesInst.sz0) (b : Sizes.SeqCoord SizesInst.sz0 → ℝ)
    (s : Finset (Sizes.SeqCoord SizesInst.sz0)) :
    iIndepFun (fun (c : Sizes.SeqCoord SizesInst.sz0) (ω : Sizes.SeqΩ SizesInst.sz0) => ω c)
        (Sizes.seqP SizesInst.sz0) ∧
      HasLaw (fun ω : Sizes.SeqΩ SizesInst.sz0 => ω c)
        (gaussianReal 0 (Sizes.seqGvar SizesInst.sz0 c)) (Sizes.seqP SizesInst.sz0) ∧
      HasLaw (fun ω : Sizes.SeqΩ SizesInst.sz0 => a * ω c)
        (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg _) * Sizes.seqGvar SizesInst.sz0 c))
        (Sizes.seqP SizesInst.sz0) ∧
      iIndepFun (fun (c : Sizes.SeqCoord SizesInst.sz0) (ω : Sizes.SeqΩ SizesInst.sz0) => b c * ω c)
        (Sizes.seqP SizesInst.sz0) ∧
      (Sizes.seqP SizesInst.sz0).map (fun ω : Sizes.SeqΩ SizesInst.sz0 => ∑ c ∈ s, b c * ω c)
        = gaussianReal 0
          (∑ c ∈ s, NNReal.mk (b c ^ 2) (sq_nonneg _) * Sizes.seqGvar SizesInst.sz0 c) :=
  ⟨iIndepFun_coord _, hasLaw_coord _ c, hasLaw_const_mul_coord _ a c,
    iIndepFun_const_mul_coord _ b, map_sum_const_mul_coord _ b s⟩

section AtSz0

open SizesInst

/-- `map_lin` and `measurable_lin` at `sz0`: the law of a finite linear form in the coordinates,
written with `linVar`. -/
example (a : Sizes.SeqCoord sz0 → ℝ) (s : Finset (Sizes.SeqCoord sz0)) :
    Measurable (fun ω : Sizes.SeqΩ sz0 => ∑ c ∈ s, a c * ω c) ∧
      (Sizes.seqP sz0).map (fun ω : Sizes.SeqΩ sz0 => ∑ c ∈ s, a c * ω c) =
        gaussianReal 0 (linVar (Sizes.seqGvar sz0) a s) :=
  ⟨measurable_lin (fun c => measurable_pi_apply c) a s,
    map_lin (fun c => measurable_pi_apply c) (fun c => Sizes.seqP_map_eval sz0 c)
      (iIndepFun_coord sz0) a s⟩

/-- `lintegral_indep_pair` at `sz0`: two coordinates of different sizes are independent, and the
integral of a function of the pair is the iterated integral against their laws. -/
example (c₀ c₁ : Sizes.SeqCoord sz0) (h01 : c₀ ≠ c₁) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(ω c₀) ^ 2 - (ω c₁) ^ 2)) ∂(Sizes.seqP sz0) =
      ∫⁻ y, (∫⁻ x, ENNReal.ofReal (Real.exp (-x ^ 2 - y ^ 2))
        ∂((Sizes.seqP sz0).map fun ω => ω c₀)) ∂((Sizes.seqP sz0).map fun ω => ω c₁) := by
  have h : IndepFun (fun ω : Sizes.SeqΩ sz0 => ω c₀) (fun ω => ω c₁) (Sizes.seqP sz0) :=
    (iIndepFun_coord sz0).indepFun h01
  exact lintegral_indep_pair (U := fun ω : Sizes.SeqΩ sz0 => ω c₀) (V := fun ω => ω c₁)
    (measurable_pi_apply c₀) (measurable_pi_apply c₁) h
    (F := fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2 - p.2 ^ 2))) (by fun_prop)

/-- `integral_indep_pair` at `sz0`: for two coordinates of different sizes (independent), the
integral of the bounded function `exp(-x² - y²)` of the pair is the iterated integral against their
laws. -/
example (c₀ c₁ : Sizes.SeqCoord sz0) (h01 : c₀ ≠ c₁) :
    ∫ ω, Real.exp (-(ω c₀) ^ 2 - (ω c₁) ^ 2) ∂(Sizes.seqP sz0) =
      ∫ y, (∫ x, Real.exp (-x ^ 2 - y ^ 2) ∂((Sizes.seqP sz0).map fun ω => ω c₀))
        ∂((Sizes.seqP sz0).map fun ω => ω c₁) := by
  have h : IndepFun (fun ω : Sizes.SeqΩ sz0 => ω c₀) (fun ω => ω c₁) (Sizes.seqP sz0) :=
    (iIndepFun_coord sz0).indepFun h01
  have hF : Integrable (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2 - p.2 ^ 2))
      (((Sizes.seqP sz0).map fun ω : Sizes.SeqΩ sz0 => ω c₀).prod
        ((Sizes.seqP sz0).map fun ω : Sizes.SeqΩ sz0 => ω c₁)) := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])
  exact integral_indep_pair (U := fun ω : Sizes.SeqΩ sz0 => ω c₀) (V := fun ω => ω c₁)
    (measurable_pi_apply c₀) (measurable_pi_apply c₁) h hF

/-- `integral_indep_pair_le` and `lintegral_indep_pair_le` at `sz0`: the iterated integral of the
bounded function `exp(-x² - y²)` against two independent Gaussian coordinates is at most `1`. -/
example (c₀ c₁ : Sizes.SeqCoord sz0) (h01 : c₀ ≠ c₁) :
    (∫ ω, Real.exp (-(ω c₀) ^ 2 - (ω c₁) ^ 2) ∂(Sizes.seqP sz0) ≤ 1) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(ω c₀) ^ 2 - (ω c₁) ^ 2)) ∂(Sizes.seqP sz0) ≤ 1 := by
  have h : IndepFun (fun ω : Sizes.SeqΩ sz0 => ω c₀) (fun ω => ω c₁) (Sizes.seqP sz0) :=
    (iIndepFun_coord sz0).indepFun h01
  have hle : ∀ x y : ℝ, Real.exp (-x ^ 2 - y ^ 2) ≤ 1 := fun x y =>
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x, sq_nonneg y])
  have hF : Integrable (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2 - p.2 ^ 2))
      (((Sizes.seqP sz0).map fun ω : Sizes.SeqΩ sz0 => ω c₀).prod
        ((Sizes.seqP sz0).map fun ω : Sizes.SeqΩ sz0 => ω c₁)) :=
    Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hle p.1 p.2)
  have hU : Measurable (fun ω : Sizes.SeqΩ sz0 => ω c₀) := measurable_pi_apply c₀
  have hV : Measurable (fun ω : Sizes.SeqΩ sz0 => ω c₁) := measurable_pi_apply c₁
  constructor
  · have hb : ∀ᵐ y ∂((Sizes.seqP sz0).map fun ω : Sizes.SeqΩ sz0 => ω c₁),
        ∫ x, Real.exp (-x ^ 2 - y ^ 2) ∂((Sizes.seqP sz0).map fun ω : Sizes.SeqΩ sz0 => ω c₀)
          ≤ (fun _ : ℝ => (1 : ℝ)) y := by
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Sizes.seqP_map_eval]
      calc ∫ x, Real.exp (-x ^ 2 - y ^ 2) ∂(gaussianReal 0 (Sizes.seqGvar sz0 c₀))
          ≤ ∫ _x, (1 : ℝ) ∂(gaussianReal 0 (Sizes.seqGvar sz0 c₀)) :=
            integral_mono (Integrable.of_bound (by fun_prop) 1
              (Filter.Eventually.of_forall fun x => by
                rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hle x y))
              (integrable_const 1) fun x => hle x y
        _ = 1 := by simp
    have := integral_indep_pair_le hU hV h hF (g := fun _ => (1 : ℝ)) (integrable_const 1) hb
    simpa using this
  · have hb : ∀ y : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (-x ^ 2 - y ^ 2))
        ∂((Sizes.seqP sz0).map fun ω : Sizes.SeqΩ sz0 => ω c₀) ≤ 1 := by
      intro y
      rw [Sizes.seqP_map_eval]
      calc ∫⁻ x, ENNReal.ofReal (Real.exp (-x ^ 2 - y ^ 2)) ∂(gaussianReal 0 (Sizes.seqGvar sz0 c₀))
          ≤ ∫⁻ _x, 1 ∂(gaussianReal 0 (Sizes.seqGvar sz0 c₀)) :=
            lintegral_mono fun x => by
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hle x y)
        _ = 1 := by simp
    exact lintegral_indep_pair_le hU hV h
      (F := fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2 - p.2 ^ 2))) (by fun_prop) hb

/-- `glue` and its three lemmas at two disjoint coordinate blocks `{c₀}`, `{c₁}` of `sz0`: a
quantity that reads only `c₀, c₁` is a function of the two blocks. -/
example (c₀ c₁ : Sizes.SeqCoord sz0) (ω : Sizes.SeqΩ sz0) :
    Measurable (glue ({c₀} : Finset (Sizes.SeqCoord sz0)) {c₁}) ∧
      glue ({c₀} : Finset (Sizes.SeqCoord sz0)) {c₁}
        ((fun c : ({c₀} : Finset (Sizes.SeqCoord sz0)) => ω c),
          (fun c : ({c₁} : Finset (Sizes.SeqCoord sz0)) => ω c)) c₀ = ω c₀ ∧
      ω c₀ + ω c₁ =
        (fun p => (fun ω' : Sizes.SeqCoord sz0 → ℝ => ω' c₀ + ω' c₁)
          (glue ({c₀} : Finset (Sizes.SeqCoord sz0)) {c₁} p))
          ((fun c : ({c₀} : Finset (Sizes.SeqCoord sz0)) => ω c),
            (fun c : ({c₁} : Finset (Sizes.SeqCoord sz0)) => ω c)) :=
  ⟨measurable_glue _ _, glue_agree _ _ ω (by simp),
    eq_glue_of_congr ({c₀} : Finset (Sizes.SeqCoord sz0)) {c₁}
      (fun ω' : Sizes.SeqCoord sz0 → ℝ => ω' c₀ + ω' c₁)
      (fun ω' ω'' h => by
        simp only [Finset.mem_union, Finset.mem_singleton] at h
        rw [h c₀ (Or.inl rfl), h c₁ (Or.inr rfl)]) ω⟩

end AtSz0

end Checks


end RBM.Gauss.LinearForm
