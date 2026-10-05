/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Pins
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# The OU carrier facts (T2177, UN-02a)

Port of `RBM2D/Universality/OU.lean` at `c9a24cf` (`ouSample` `:42`, `ouVar` `:46`,
`ouMat_eq_Xmat_ouSample` `:50`, `measurable_ouSample` `:60`, `measurable_ouMat` `:71`,
`ouSample_law` `:105`, `ouMat_zero_map` `:176`, `seqXmat_map_eq_ouMat_zero` `:188`) to
`d` dimensions and to the abstract model `UNModel` of `RBM3D/Universality/Pins.lean`.

The matrix OU marginal `𝐇_t = e^{-t/2} H + √(1 - e^{-t}) H'` of `ouMat` is, for the band model
`UNModel.band sz`, the Hermitian matrix `Xmat` of the interpolated coordinates `ouSample`; under
`ouP` its coordinates are independent centred Gaussians with variance
`e^{-t} S_c + (1 - e^{-t}) N⁻¹_c` (`ouSample_law`).  At `t = 0` the law of `𝐇_0` is that of the
model (`ouMat_zero_map`, for every `UNModel`).

Statement shapes that differ from RBM2D (paper-delta candidates, see the prove report):
`ouP M n` lives on `SeqΩ sz × Ω d (L n) (W n)`, so `ouSample` is built from `slice sz n`, `ouVar`
carries the coupling `g = sz.lam n`, and the Gaussian law is stated for the band model only (it
is Gaussian only there); `ouMat_zero_map`, `measurable_ouMat` hold for every `UNModel`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal

section U0

variable {d : ℕ} {sz : Sizes d}

instance isProbabilityMeasure_ouP (M : UNModel sz) (n : ℕ) : IsProbabilityMeasure (ouP M n) := by
  unfold ouP
  infer_instance

/-- The interpolated real coordinates `e^{-t/2} (slice ω₁) + √(1 - e^{-t}) ω₂` at size `n`
(`RBM2D/Universality/OU.lean:42`, `ouSample`; the first coordinate is read through `slice sz n`). -/
def ouSample (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Ω d (sz.L n) (sz.W n) :=
  fun c => Real.exp (-t / 2) * slice sz n ω.1 c + Real.sqrt (1 - Real.exp (-t)) * ω.2 c

/-- The coordinate variance of `𝐇_t`: `e^{-t} S_c + (1 - e^{-t}) N⁻¹_c` (RBM2D paper `1-2:334-337`);
`S_c = gvarF d L W g c` carries the coupling `g` (`RBM2D/Universality/OU.lean:46`, `ouVar`). -/
def ouVar (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (t : ℝ) (c : CoordF d L W) : ℝ≥0 :=
  (Real.exp (-t)).toNNReal * gvarF d L W g c + (1 - Real.exp (-t)).toNNReal * gueVar d L W c

/-- `𝐇_t` of the band model is `Xmat` of the interpolated coordinates
(`RBM2D/Universality/OU.lean:50`, `ouMat_eq_Xmat_ouSample`; `Xmat_add`, `Xmat_smul`). -/
theorem ouMat_eq_Xmat_ouSample (sz : Sizes d) (n : ℕ) (t : ℝ)
    (ω : SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat (UNModel.band sz) n t ω = Xmat d (sz.L n) (sz.W n) (ouSample sz n t ω) := by
  have h : ouSample sz n t ω =
      Real.exp (-t / 2) • slice sz n ω.1 + Real.sqrt (1 - Real.exp (-t)) • ω.2 := by
    funext c
    simp [ouSample]
  rw [h, Xmat_add, Xmat_smul, Xmat_smul]
  rfl

theorem measurable_ouSample (sz : Sizes d) (n : ℕ) (t : ℝ) : Measurable (ouSample sz n t) := by
  refine measurable_pi_iff.2 fun c => ?_
  have h1 : Measurable fun ω : SeqΩ sz × Ω d (sz.L n) (sz.W n) => slice sz n ω.1 c :=
    ((measurable_pi_apply c).comp (measurable_slice sz n)).comp measurable_fst
  have h2 : Measurable fun ω : SeqΩ sz × Ω d (sz.L n) (sz.W n) => ω.2 c :=
    (measurable_pi_apply c).comp measurable_snd
  exact (h1.const_mul _).add (h2.const_mul _)

/-- `𝐇_t` is measurable for every `UNModel` (`RBM2D/Universality/OU.lean:71`, `measurable_ouMat`). -/
theorem measurable_ouMat (M : UNModel sz) (n : ℕ) (t : ℝ) : Measurable (ouMat M n t) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have h1 : Measurable fun ω : SeqΩ sz × Ω d (sz.L n) (sz.W n) => M.H n ω.1 i j :=
    (M.meas n i j).comp measurable_fst
  have h2 : Measurable fun ω : SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      Xentry d (sz.L n) (sz.W n) ω.2 i j :=
    (measurable_Xentry d (sz.L n) (sz.W n) i j).comp measurable_snd
  have h3 : (fun ω : SeqΩ sz × Ω d (sz.L n) (sz.W n) => ouMat M n t ω i j) = fun ω =>
      (Real.exp (-t / 2) : ℂ) * M.H n ω.1 i j +
        (Real.sqrt (1 - Real.exp (-t)) : ℂ) * Xentry d (sz.L n) (sz.W n) ω.2 i j := by
    funext ω
    simp [ouMat, Xmat]
  rw [h3]
  exact (h1.const_mul _).add (h2.const_mul _)

end U0

/-- The law of `a X + b Y` for independent centred Gaussians `X`, `Y`. -/
private theorem ou_pair_map (a b : ℝ) (v₁ v₂ : ℝ≥0) :
    ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)).map
        (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      gaussianReal 0
        (NNReal.mk (a ^ 2) (sq_nonneg a) * v₁ + NNReal.mk (b ^ 2) (sq_nonneg b) * v₂) := by
  have h : (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      (fun q : ℝ × ℝ => q.1 + q.2) ∘ Prod.map (fun x : ℝ => a * x) (fun y : ℝ => b * y) := by
    funext p
    rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  have := gaussianReal_conv_gaussianReal (m₁ := a * 0) (m₂ := b * 0)
    (v₁ := NNReal.mk (a ^ 2) (sq_nonneg a) * v₁) (v₂ := NNReal.mk (b ^ 2) (sq_nonneg b) * v₂)
  rw [mul_zero] at this
  simpa [Measure.conv] using this

section U0Law

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The interpolation on the pair space `Ω × Ω` (the source form of `ouSample`; helper). -/
private def ouSamplePair (t : ℝ) (ω : Ω d L W × Ω d L W) : Ω d L W :=
  fun c => Real.exp (-t / 2) * ω.1 c + Real.sqrt (1 - Real.exp (-t)) * ω.2 c

private theorem measurable_ouSamplePair (t : ℝ) : Measurable (ouSamplePair d L W t) := by
  refine measurable_pi_iff.2 fun c => ?_
  have h1 : Measurable fun ω : Ω d L W × Ω d L W => ω.1 c :=
    (measurable_pi_apply c).comp measurable_fst
  have h2 : Measurable fun ω : Ω d L W × Ω d L W => ω.2 c :=
    (measurable_pi_apply c).comp measurable_snd
  exact (h1.const_mul _).add (h2.const_mul _)

/-- The one-time Gaussian law on the pair space `PF × gueP` (the body of the source proof of
`RBM2D/Universality/OU.lean:105`, with `P` replaced by `PF d L W g`). -/
private theorem ouSamplePair_law {t : ℝ} (ht : 0 ≤ t) :
    ((PF d L W g).prod (gueP d L W)).map (ouSamplePair d L W t) =
      Measure.infinitePi (fun c => gaussianReal 0 (ouVar d L W g t c)) := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hA : NNReal.mk (Real.exp (-t / 2) ^ 2) (sq_nonneg _) = (Real.exp (-t)).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mk, Real.coe_toNNReal _ (Real.exp_pos _).le, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hB : NNReal.mk (Real.sqrt (1 - Real.exp (-t)) ^ 2) (sq_nonneg _) =
      (1 - Real.exp (-t)).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mk, Real.coe_toNNReal _ (sub_nonneg.2 he)]
    exact Real.sq_sqrt (sub_nonneg.2 he)
  refine IsProjectiveLimit.unique ?_
    (Measure.isProjectiveLimit_infinitePi (fun c => gaussianReal 0 (ouVar d L W g t c)))
  intro I
  set a : ℝ := Real.exp (-t / 2) with ha
  set b : ℝ := Real.sqrt (1 - Real.exp (-t)) with hb
  let f : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
  have hf : Measurable f := by fun_prop
  let R : (Ω d L W × Ω d L W) → (I → ℝ) × (I → ℝ) := Prod.map I.restrict I.restrict
  let g' : (I → ℝ) × (I → ℝ) → (I → ℝ) := fun q i => a * q.1 i + b * q.2 i
  have hR : Measurable R := (Finset.measurable_restrict I).prodMap (Finset.measurable_restrict I)
  have hg : Measurable g' := by
    refine measurable_pi_iff.2 fun i => ?_
    have h1 : Measurable fun q : (I → ℝ) × (I → ℝ) => q.1 i :=
      (measurable_pi_apply i).comp measurable_fst
    have h2 : Measurable fun q : (I → ℝ) × (I → ℝ) => q.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    exact (h1.const_mul _).add (h2.const_mul _)
  have hcomp : (fun ω : Ω d L W => I.restrict ω) ∘ ouSamplePair d L W t = g' ∘ R := by
    funext ω
    rfl
  have hR_map : ((PF d L W g).prod (gueP d L W)).map R =
      (Measure.pi fun i : I => gaussianReal 0 (gvarF d L W g i)).prod
        (Measure.pi fun i : I => gaussianReal 0 (gueVar d L W i)) := by
    have h1 : (PF d L W g).map I.restrict =
        Measure.pi fun i : I => gaussianReal 0 (gvarF d L W g i) :=
      Measure.infinitePi_map_restrict _
    have h2 : (gueP d L W).map I.restrict =
        Measure.pi fun i : I => gaussianReal 0 (gueVar d L W i) :=
      Measure.infinitePi_map_restrict _
    rw [← h1, ← h2, Measure.map_prod_map _ _ (Finset.measurable_restrict I)
      (Finset.measurable_restrict I)]
  have he_map := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I
    (fun i : I => gaussianReal 0 (gvarF d L W g i))
    (fun i : I => gaussianReal 0 (gueVar d L W i))).map_eq
  have hge : g' ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I) = fun x i => f (x i) := by
    funext x i
    rfl
  have : ∀ i : I, SigmaFinite
      (((gaussianReal 0 (gvarF d L W g i)).prod (gaussianReal 0 (gueVar d L W i))).map f) :=
    fun i => by
    rw [ou_pair_map]
    infer_instance
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_ouSamplePair d L W t), hcomp,
    ← Measure.map_map hg hR, hR_map, ← he_map, Measure.map_map hg
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I).measurable, hge,
    Measure.pi_map_pi (fun i => hf.aemeasurable)]
  congr 1
  funext i
  rw [ou_pair_map, hA, hB]
  rfl

end U0Law

section U0Band

variable {d : ℕ}

/-- **The one-time Gaussian law** (RBM2D `ouSample_law`, `OU.lean:105`; paper `1-2:334-337`):
for the band model under `ouP` the coordinates of `𝐇_t` are independent centred Gaussians with
variance `e^{-t} S_c + (1 - e^{-t}) N⁻¹_c`, `S_c = gvarF d (L n) (W n) (sz.lam n) c`.  The statement
is for `UNModel.band sz` (the law is Gaussian only there); not for an abstract `M`. -/
theorem ouSample_law (sz : Sizes d) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (ouP (UNModel.band sz) n).map (ouSample sz n t) =
      Measure.infinitePi (fun c => gaussianReal 0 (ouVar d (sz.L n) (sz.W n) (sz.lam n) t c)) := by
  have h : ouSample sz n t = ouSamplePair d (sz.L n) (sz.W n) t ∘ Prod.map (slice sz n) id := rfl
  have hm : Measurable (Prod.map (slice sz n) (id : Ω d (sz.L n) (sz.W n) → _)) :=
    (measurable_slice sz n).prodMap measurable_id
  rw [h, ← Measure.map_map (measurable_ouSamplePair _ _ _ t) hm]
  have : (ouP (UNModel.band sz) n).map (Prod.map (slice sz n) id) =
      (PF d (sz.L n) (sz.W n) (sz.lam n)).prod (gueP d (sz.L n) (sz.W n)) := by
    unfold ouP
    rw [← Measure.map_prod_map _ _ (measurable_slice sz n) measurable_id, Measure.map_id]
    change ((seqP sz).map (slice sz n)).prod _ = _
    rw [seqP_map_slice]
  rw [this]
  exact ouSamplePair_law d (sz.L n) (sz.W n) (sz.lam n) ht

end U0Band

section U0Zero

variable {d : ℕ} {sz : Sizes d}

/-- **Law transfer at `t = 0`** (RBM2D paper `1-2:339`; `RBM2D/Universality/OU.lean:176`): `𝐇_0 = H`
under `ouP` has the law of the model matrix `M.H n` under `M.μ` (first marginal of `ouP`,
`ouMat_zero`). -/
theorem ouMat_zero_map (M : UNModel sz) (n : ℕ) :
    (ouP M n).map (ouMat M n 0) = M.μ.map (M.H n) := by
  have hH : Measurable (M.H n) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => M.meas n i j
  have h : ouMat M n 0 = M.H n ∘ Prod.fst := funext (ouMat_zero M n)
  rw [h, ← Measure.map_map hH measurable_fst]
  unfold ouP
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- **Law transfer from the frozen carrier**: the band matrix `seqXmat sz n` on `seqP sz` and `𝐇_0`
on `ouP` have the same law (`RBM2D/Universality/OU.lean:188`, `seqXmat_map_eq_ouMat_zero`). -/
theorem seqXmat_map_eq_ouMat_zero (sz : Sizes d) (n : ℕ) :
    (seqP sz).map (seqXmat sz n) = (ouP (UNModel.band sz) n).map (ouMat (UNModel.band sz) n 0) :=
  (ouMat_zero_map (UNModel.band sz) n).symm

end U0Zero

end RBM.Univ

/-! ## Compiled nonempty instances (band model `UNModel.band sz0`, `d = 3`, `n = 0`: `L = 4`,
`W = 32`, `lam = 1/64`, `N = 2097152`) -/

namespace RBM.Univ.OUCheck

open MeasureTheory ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst
open scoped NNReal

/-- `ouSample_law` at `UNModel.band sz0`, `n = 0`, `t = 1`. -/
example : (ouP (UNModel.band sz0) 0).map (ouSample sz0 0 1) =
    Measure.infinitePi (fun c => gaussianReal 0 (ouVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 1 c)) :=
  ouSample_law sz0 0 zero_le_one

/-- `ouSample_law` at `t = 1/2` and `t = 0` (the limit `t = 0` has `ouVar = gvarF`). -/
example : (ouP (UNModel.band sz0) 0).map (ouSample sz0 0 (1 / 2)) =
    Measure.infinitePi (fun c => gaussianReal 0
      (ouVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 2) c)) :=
  ouSample_law sz0 0 (by norm_num)

example : (ouP (UNModel.band sz0) 0).map (ouSample sz0 0 0) =
    Measure.infinitePi (fun c => gaussianReal 0
      (ouVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 c)) :=
  ouSample_law sz0 0 le_rfl

/-- At `t = 0` the OU variance is the band variance (`ouVar = gvarF`). -/
theorem ouVar_zero (c : CoordF 3 (sz0.L 0) (sz0.W 0)) :
    ouVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 c = gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c := by
  simp [ouVar]

/-- At `t = 1` the weights `e^{-1}`, `1 - e^{-1}` are both positive: the GUE part is nonzero. -/
theorem ouVar_one_gue_weight_pos : 0 < (1 - Real.exp (-1)).toNNReal := by
  rw [Real.toNNReal_pos, sub_pos]
  exact Real.exp_lt_one_iff.2 (by norm_num)

/-- `ouMat_zero_map` at `UNModel.band sz0`, `n = 0`. -/
example : (ouP (UNModel.band sz0) 0).map (ouMat (UNModel.band sz0) 0 0) =
    (UNModel.band sz0).μ.map ((UNModel.band sz0).H 0) :=
  ouMat_zero_map (UNModel.band sz0) 0

example : (seqP sz0).map (seqXmat sz0 0) =
    (ouP (UNModel.band sz0) 0).map (ouMat (UNModel.band sz0) 0 0) :=
  seqXmat_map_eq_ouMat_zero sz0 0

example : Measurable (ouMat (UNModel.band sz0) 0 1) := measurable_ouMat _ 0 1
example : Measurable (ouSample sz0 0 1) := measurable_ouSample sz0 0 1
example (ω : SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0)) :
    ouMat (UNModel.band sz0) 0 1 ω = Xmat 3 (sz0.L 0) (sz0.W 0) (ouSample sz0 0 1 ω) :=
  ouMat_eq_Xmat_ouSample sz0 0 1 ω

#print axioms RBM.Univ.isProbabilityMeasure_ouP
#print axioms RBM.Univ.ouMat_eq_Xmat_ouSample
#print axioms RBM.Univ.measurable_ouSample
#print axioms RBM.Univ.measurable_ouMat
#print axioms RBM.Univ.ouSample_law
#print axioms RBM.Univ.ouMat_zero_map
#print axioms RBM.Univ.seqXmat_map_eq_ouMat_zero

end RBM.Univ.OUCheck

end
