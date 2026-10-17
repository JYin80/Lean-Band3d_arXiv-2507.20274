/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWVocab
import RBM3D.Graph.LWWeightExp
import RBM3D.Gauss.FineModel
import RBM3D.Green.IBPPoly
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# LW-07: the `GG` expansion `(Oe2x)` (T2120)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:334-349` (`7_8:334-349`, lemma `T eq0`,
cited from `[yang2021]` Lemma 3.14, no proof in the paper).  Design: T2040 (split row LW-07); the
twin of the weight expansion `(Owx)` of `Graph/LWWeightExp` (T2107).

## Contents (namespace `RBM.Graph`)

1. **The pathwise identity** `oe2x_defect_identity` (`(Oe2x)` is the Stein identity plus linear
   algebra: the difference of the two sides is `-m Σ_w (δ_{xw} + m² S⁺_{xw}) Z_w` with the Stein
   defect `Z_w = oe2xDefect` of the row `w`), the twin of `owx_defect_identity`.
2. **Stein on the sequence space**: `oe2x_resolvent_id` (`Σ_α H_{wα} G_{αy} = δ_{wy} + z G_{wy}`,
   the off-diagonal case of `lwStein_resolvent_id`), `integral_oe2xDefect` (`E Z_w = 0`, from
   `stein_sample` applied to `G_{αy} G_{y'w} f`), `oe2x_integral` (`(Oe2x)` in expectation for
   every resolvent polynomial `f`).
3. **The pin on the one-size law**: `lwGGExp_holds : ∀ d, LWggExp d` (the pin of
   `Graph/LWPins.lean:164`, with `S⁺ = LWPins_lwSp d L W g E t` as fixed by DECISIONS §34), for
   every `d`, from `oe2x_integral` through the bridge `lwWx_*` of `Graph/LWWeightExp` for
   `0 < t < 1`, and `t = 0` separately (`oe2x_lwG_zero`).
4. **`(Oe2x)` as a graph operation**: the eight terms as graphs `oe2xR1` (`x` merged into `y`;
   `oe2xR1d` is the same with an `=`-dotted edge), `oe2xR2`, `owxT1` (= `R3`), `oe2xR4`, `oe2xR5`,
   `oe2xR6`, and `oe2xR7 q'`, `oe2xR8 q'` (one graph for each solid edge `q'.1` of `f`);
   `oe2x_term_integral` (one labelling), `oe2x_graph_E` (the identity of expectations of values),
   `oe2xR*_counters` (`Δ(n_S, n_W, n_V, n_M)`) and `oe2xR*_ord` (`Δord = +1` in each term;
   `n_M` is unchanged except in `R1`, `R2`, where a merge or an added waved edge lowers it by at
   most one: `oe2xR1_counters`, `oe2xR1_nM_ge`, `oe2xR2_counters`, `oe2xR2_nM_ge`).
5. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green

/-- Closure of `Tame` under the operations that occur in the expansion (copy of the local macro of
`Graph/LWStein.lean`, which is not exported). -/
local macro "oe2x_tame" : tactic =>
  `(tactic| repeat' first
    | exact Tame.const _
    | assumption
    | (apply lwStein_tame_lwG; assumption)
    | (apply lwStein_tame_dhSample; assumption)
    | apply Tame.mul
    | apply Tame.add
    | apply Tame.sub
    | apply Tame.neg
    | (apply Tame.sum; intros; skip))

/-! ## 1. The pathwise identity -/

section Oe2xAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Stein defect at row `w` of the `GG` expansion `(Oe2x)` (`7_8:334-349`) for `G_{xy} G_{y'x} f(G)`:
`Z_w = (Σ_α H_{wα} G_{αy}) G_{y'w} f - Σ_α S_{wα} ∂_{h_{αw}}(G_{αy} G_{y'w} f)` with the resolvent identity
`Σ_α H_{wα} G_{αy} = δ_{wy} + z G_{wy}`, `∂_{h_{αw}} G_{αy} = -G_{αα} G_{wy}` and
`∂_{h_{αw}} G_{y'w} = -G_{y'α} G_{ww}` inserted; `f` and `df α w = ∂_{h_{αw}} f` are data. -/
def oe2xDefect (z : ℂ) (G S : Matrix ι ι ℂ) (f : ℂ) (df : ι → ι → ℂ) (y y' w : ι) : ℂ :=
  ((if w = y then 1 else 0) + z * G w y) * (G y' w * f) + (∑ α, S w α * G α α) * (G w y * G y' w * f) +
    ∑ α, S w α * (G α y * G y' α * G w w * f) - ∑ α, S w α * (G α y * G y' w * df α w)

/-- **`(Oe2x)` is the Stein identity plus linear algebra**: for every `f`, `df`, the difference of the two
sides of `(Oe2x)` is, pathwise and exactly, `-m Σ_w (δ_{xw} + m² S⁺_{xw}) Z_w`.  Hypotheses: `m ≠ 0`, the rows of
`S` sum to `s`, `z + s m = -m⁻¹` and `S⁺ (1 - m² S) = S`. -/
theorem oe2x_defect_identity (z m s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (G S Sp : Matrix ι ι ℂ) (hS : ∀ i, ∑ j, S i j = s)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * S w j = S i j) (f : ℂ) (df : ι → ι → ℂ) (x y y' : ι) :
    G x y * G y' x * f -
      (m * (if x = y then 1 else 0) * G y' x * f +
        m ^ 3 * Sp x y * G y' y * f +
        m * (∑ α, S x α * (G α α - m)) * (G x y * G y' x * f) +
        m ^ 3 * ∑ α, ∑ β, Sp x α * S α β * (G β β - m) * G α y * G y' α * f +
        m * (G x x - m) * ∑ α, S x α * G α y * G y' α * f +
        m ^ 3 * ∑ α, ∑ β, Sp x α * S α β * (G α α - m) * G β y * G y' β * f -
        m * ∑ α, S x α * G α y * G y' x * df α x -
        m ^ 3 * ∑ α, ∑ β, Sp x α * S α β * G β y * G y' α * df β α) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) * oe2xDefect z G S f df y y' w := by
  set u : ι → ℂ := fun i => G i i - m with hu
  set Su : ι → ℂ := fun w => ∑ α, S w α * u α with hSu
  have hrow : ∀ w, ∑ α, S w α * G α α = s * m + Su w := by
    intro w
    have h1 : ∑ α, S w α * G α α = ∑ α, S w α * m + ∑ α, S w α * u α := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [hu]; ring
    rw [h1, ← Finset.sum_mul, hS]
  set a : ι → ℂ := fun w => G w y * G y' w * f with ha
  set b : ι → ℂ := fun w => ∑ α, S w α * a α with hb
  set c : ι → ℂ := fun w => ∑ α, S w α * (G α y * G y' w * df α w) with hc
  set r : ι → ℂ := fun w => m * ((if w = y then 1 else 0) * (G y' w * f)) + m * Su w * a w +
    m * u w * b w - m * c w with hr
  have hD : ∀ w, -m * oe2xDefect z G S f df y y' w = a w - m ^ 2 * b w - r w := by
    intro w
    unfold oe2xDefect
    rw [hrow w]
    have hzm' : z = -m⁻¹ - s * m := by linear_combination hzm
    have hGw : G w w = m + u w := by simp only [hu]; ring
    have hbw : ∑ α, S w α * (G α y * G y' α * G w w * f) = G w w * b w := by
      simp only [hb, ha, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hbw, hzm', hGw]
    simp only [hr, ha, hc]
    field_simp
    ring
  have hvec : ∀ v : ι → ℂ, m ^ 2 * ∑ w, Sp x w * v w - m ^ 4 * ∑ w, Sp x w * ∑ α, S w α * v α =
      m ^ 2 * ∑ α, S x α * v α := by
    intro v
    have h1 : ∑ α, S x α * v α = ∑ α, (Sp x α - m ^ 2 * ∑ w, Sp x w * S w α) * v α :=
      Finset.sum_congr rfl fun α _ => by rw [hSp x α]
    have h2 : ∑ α, (Sp x α - m ^ 2 * ∑ w, Sp x w * S w α) * v α =
        ∑ α, Sp x α * v α - m ^ 2 * ∑ w, Sp x w * ∑ α, S w α * v α := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun α _ => by ring
    rw [h1, h2]
    ring
  have hR : -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) * oe2xDefect z G S f df y y' w =
      ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) * (a w - m ^ 2 * b w - r w) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← hD w]; ring
  rw [hR]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have hf1 := hvec a
  have hsplit : ∑ w, m ^ 2 * Sp x w * (a w - m ^ 2 * b w - r w) =
      m ^ 2 * ∑ w, Sp x w * a w - m ^ 4 * ∑ w, Sp x w * b w - m ^ 2 * ∑ w, Sp x w * r w := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [hsplit]
  have hxx : ∑ α, S x α * (G α α - m) = Su x := rfl
  have h2 : ∑ α, ∑ β, Sp x α * S α β * (G β β - m) * G α y * G y' α * f =
      ∑ α, Sp x α * (Su α * a α) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hSu, hu, ha, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have h3 : ∑ α, ∑ β, Sp x α * S α β * (G α α - m) * G β y * G y' β * f =
      ∑ α, Sp x α * (u α * b α) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hb, hu, ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have h4 : ∑ α, ∑ β, Sp x α * S α β * G β y * G y' α * df β α = ∑ α, Sp x α * c α := by
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have h5 : ∑ α, S x α * G α y * G y' α * f = b x := by
    simp only [hb, ha]
    exact Finset.sum_congr rfl fun α _ => by ring
  have h6 : ∑ α, S x α * G α y * G y' x * df α x = c x := by
    simp only [hc]
    exact Finset.sum_congr rfl fun α _ => by ring
  have hrsum : ∑ w, Sp x w * r w = m * (Sp x y * (G y' y * f)) + m * ∑ α, Sp x α * (Su α * a α) +
      m * ∑ α, Sp x α * (u α * b α) - m * ∑ α, Sp x α * c α := by
    have hpt : ∀ w, Sp x w * r w = m * (Sp x w * ((if w = y then 1 else 0) * (G y' w * f))) +
        m * (Sp x w * (Su w * a w)) + m * (Sp x w * (u w * b w)) - m * (Sp x w * c w) := fun w => by
      simp only [hr]; ring
    have hy : ∑ w, Sp x w * ((if w = y then 1 else 0) * (G y' w * f)) = Sp x y * (G y' y * f) := by
      simp [ite_mul, mul_ite, Finset.sum_ite_eq']
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hy]
  have hrx : r x = m * ((if x = y then 1 else 0) * (G y' x * f)) + m * Su x * a x + m * u x * b x - m * c x := rfl
  rw [h2, h3, h4, h5, h6, hxx]
  have hax : a x = G x y * G y' x * f := rfl
  have hux : G x x - m = u x := rfl
  have hf1' : m ^ 2 * ∑ w, Sp x w * a w - m ^ 4 * ∑ w, Sp x w * b w = m ^ 2 * b x := hf1
  rw [hrx, hrsum, hax, hux]
  linear_combination (-1 : ℂ) * hf1'

end Oe2xAlg

/-! ## 2. Stein on the sequence space: `E Z_w = 0` and `(Oe2x)` in expectation -/

section Oe2xStein

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- The resolvent identity `Σ_α H_{wα} G_{αy} = δ_{wy} + z G_{wy}` (the off-diagonal case of the merged
`lwStein_resolvent_id`). -/
theorem oe2x_resolvent_id {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (w y : Idx d (sz.L n) (sz.W n)) :
    ∑ α, sz.seqHflow n u ω w α * lwG sz n z u α y ω =
      (if w = y then 1 else 0) + z * lwG sz n z u w y ω := by
  have hU : IsUnit (sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    isUnit_sub_smul_of_isHermitian (Sizes.seqHflow_isHermitian sz n u ω) hz
  have h : ((sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
      Ring.inverse (sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))) w y =
      (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) w y := by
    rw [Ring.mul_inverse_cancel _ hU]
  simp only [lwG, lwGm, Gres, ite_true]
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at h
  linear_combination h

/-- **`E Z_w = 0`** (`(Oe2x)`, `7_8:334-349`): for a resolvent polynomial `f`, `df α w = ∂_{h_{αw}} f`, the Stein
defect `Z_w` of the row `w` (`oe2xDefect`, with `S = u · svarF`) has mean zero.  From the complex Stein identity
(`stein_sample`, applied to `G_{αy} G_{y'w} f`) and the resolvent identity `oe2x_resolvent_id`. -/
theorem integral_oe2xDefect (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (y y' w : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, oe2xDefect z (lwGm sz n z u ω) (lwS sz n u) (lwPoly sz n z u P ω)
      (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) y y' w ∂(Sizes.seqP sz) = 0 := by
  classical
  have hf : Tame1 sz n (lwPoly sz n z u P) := lwPoly_tame1 hz u P
  have hF : Tame1 sz n (fun ω => lwG sz n z u y' w ω * lwPoly sz n z u P ω) :=
    (lwG_tame1 hz u y' w).mul hf
  have hQ : ∀ α : Idx d (sz.L n) (sz.W n),
      Tame1 sz n (fun ω => lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω)) :=
    fun α => (lwG_tame1 hz u α y).mul hF
  have hdF : ∀ (α : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
      dhSample sz n u α w (fun ω => lwG sz n z u y' w ω * lwPoly sz n z u P ω) ω =
        -(lwG sz n z u y' α ω * lwG sz n z u w w ω) * lwPoly sz n z u P ω +
          lwG sz n z u y' w ω * dhSample sz n u α w (lwPoly sz n z u P) ω := by
    intro α ω
    rw [lwStein_dh_mul (lwG_tame1 hz u y' w) hf, dhSample_lwG sz n hz hu]
  have hdQ : ∀ (α : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
      dhSample sz n u α w (fun ω => lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω)) ω =
        -(lwG sz n z u α α ω * lwG sz n z u w y ω) * (lwG sz n z u y' w ω * lwPoly sz n z u P ω) +
          lwG sz n z u α y ω * (-(lwG sz n z u y' α ω * lwG sz n z u w w ω) * lwPoly sz n z u P ω +
            lwG sz n z u y' w ω * dhSample sz n u α w (lwPoly sz n z u P) ω) := by
    intro α ω
    rw [lwStein_dh_mul (lwG_tame1 hz u α y) hF, dhSample_lwG sz n hz hu, hdF]
  have hpt : ∀ ω : Sizes.SeqΩ sz,
      oe2xDefect z (lwGm sz n z u ω) (lwS sz n u) (lwPoly sz n z u P ω)
        (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) y y' w =
      ∑ α, sz.seqHflow n u ω w α *
          (lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω)) -
        ∑ α, lwS sz n u w α *
          dhSample sz n u α w (fun ω => lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω)) ω := by
    intro ω
    have hres := oe2x_resolvent_id (sz := sz) (n := n) hz.ne' u ω w y
    have h1 : ∑ α, sz.seqHflow n u ω w α *
        (lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω)) =
        ((if w = y then 1 else 0) + z * lwG sz n z u w y ω) *
          (lwG sz n z u y' w ω * lwPoly sz n z u P ω) := by
      rw [← hres, Finset.sum_mul]
      exact Finset.sum_congr rfl fun α _ => by ring
    have h2 : ∑ α, lwS sz n u w α *
          dhSample sz n u α w (fun ω => lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω)) ω =
        -((∑ α, lwS sz n u w α * lwGm sz n z u ω α α) *
            (lwG sz n z u w y ω * lwG sz n z u y' w ω * lwPoly sz n z u P ω)) -
          ∑ α, lwS sz n u w α * (lwG sz n z u α y ω * lwG sz n z u y' α ω * lwG sz n z u w w ω *
            lwPoly sz n z u P ω) +
          ∑ α, lwS sz n u w α * (lwG sz n z u α y ω * lwG sz n z u y' w ω *
            dhSample sz n u α w (lwPoly sz n z u P) ω) := by
      have hterm : ∀ α : Idx d (sz.L n) (sz.W n), lwS sz n u w α *
          dhSample sz n u α w (fun ω => lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω)) ω =
          -(lwS sz n u w α * lwGm sz n z u ω α α *
            (lwG sz n z u w y ω * lwG sz n z u y' w ω * lwPoly sz n z u P ω)) -
          lwS sz n u w α * (lwG sz n z u α y ω * lwG sz n z u y' α ω * lwG sz n z u w w ω *
            lwPoly sz n z u P ω) +
          lwS sz n u w α * (lwG sz n z u α y ω * lwG sz n z u y' w ω *
            dhSample sz n u α w (lwPoly sz n z u P) ω) := by
        intro α
        rw [hdQ α ω]
        simp only [lwG]
        ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
    rw [h1, h2]
    unfold oe2xDefect
    simp only [lwG]
    ring
  simp_rw [hpt]
  have iA : ∀ α : Idx d (sz.L n) (sz.W n), Integrable (fun ω => sz.seqHflow n u ω w α *
      (lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω))) (Sizes.seqP sz) := fun α =>
    Tame.integrable hG ((lwStein_tame_hflow sz n u w α).mul (hQ α).tame)
  have iB : ∀ α : Idx d (sz.L n) (sz.W n), Integrable (fun ω => lwS sz n u w α *
      dhSample sz n u α w (fun ω => lwG sz n z u α y ω * (lwG sz n z u y' w ω * lwPoly sz n z u P ω)) ω)
      (Sizes.seqP sz) := fun α =>
    Tame.integrable hG ((Tame.const _).mul (lwStein_tame_dhSample (hQ α) u α w))
  rw [integral_sub (integrable_finsetSum _ fun α _ => iA α) (integrable_finsetSum _ fun α _ => iB α),
    integral_finsetSum _ fun α _ => iA α, integral_finsetSum _ fun α _ => iB α,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [integral_const_mul]
  have := stein_sample hG (hQ α) hu.le α w
  rw [this]
  simp [lwS]

/-- **`(Oe2x)` in expectation, for every resolvent polynomial** (`7_8:334-349`, `T eq0`): the sequence-space
form of the pin `LWggExp`.  Hypotheses: `GaussIBP sz` (proved: `gaussIBP sz`); `m ≠ 0`, `z + u m = -m⁻¹`; and
`S⁺ = Sp` with `S⁺ (1 - m² S) = S` for `S = u · svarF`.  `df α x = ∂_{h_{αx}} f` (`dhSample`). -/
theorem oe2x_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (x y y' : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, lwG sz n z u x y ω * lwG sz n z u y' x ω * lwPoly sz n z u P ω ∂(Sizes.seqP sz) =
      ∫ ω, (m * (if x = y then 1 else 0) * lwG sz n z u y' x ω * lwPoly sz n z u P ω +
          m ^ 3 * Sp x y * lwG sz n z u y' y ω * lwPoly sz n z u P ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * lwG sz n z u y' x ω * lwPoly sz n z u P ω) +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u β β ω - m) * lwG sz n z u α y ω *
            lwG sz n z u y' α ω * lwPoly sz n z u P ω +
          m * (lwG sz n z u x x ω - m) * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * lwG sz n z u y' α ω *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) * lwG sz n z u β y ω *
            lwG sz n z u y' β ω * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * lwG sz n z u y' x ω *
            dhSample sz n u α x (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β y ω * lwG sz n z u y' α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω) ∂(Sizes.seqP sz) := by
  classical
  have hz' : z.im ≠ 0 := hz.ne'
  have hf : Tame1 sz n (lwPoly sz n z u P) := lwPoly_tame1 hz u P
  have tf : Tame sz (lwPoly sz n z u P) := hf.tame
  have tD : ∀ α β : Idx d (sz.L n) (sz.W n), Tame sz (dhSample sz n u α β (lwPoly sz n z u P)) :=
    fun α β => lwStein_tame_dhSample hf u α β
  have hpt : ∀ ω : Sizes.SeqΩ sz,
      (lwG sz n z u x y ω * lwG sz n z u y' x ω * lwPoly sz n z u P ω -
        (m * (if x = y then 1 else 0) * lwG sz n z u y' x ω * lwPoly sz n z u P ω +
          m ^ 3 * Sp x y * lwG sz n z u y' y ω * lwPoly sz n z u P ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * lwG sz n z u y' x ω * lwPoly sz n z u P ω) +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u β β ω - m) * lwG sz n z u α y ω *
            lwG sz n z u y' α ω * lwPoly sz n z u P ω +
          m * (lwG sz n z u x x ω - m) * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * lwG sz n z u y' α ω *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) * lwG sz n z u β y ω *
            lwG sz n z u y' β ω * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * lwG sz n z u y' x ω *
            dhSample sz n u α x (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β y ω * lwG sz n z u y' α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω)) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) *
        oe2xDefect z (lwGm sz n z u ω) (lwS sz n u) (lwPoly sz n z u P ω)
          (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) y y' w :=
    fun ω => oe2x_defect_identity z m (u : ℂ) hm0 hzm (lwGm sz n z u ω) (lwS sz n u) Sp
      (lwS_row_sum u) hSp (lwPoly sz n z u P ω) (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) x y y'
  have iZ : ∀ w : Idx d (sz.L n) (sz.W n), Integrable (fun ω => oe2xDefect z (lwGm sz n z u ω)
      (lwS sz n u) (lwPoly sz n z u P ω) (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) y y' w)
      (Sizes.seqP sz) := by
    intro w
    refine Tame.integrable hG ?_
    unfold oe2xDefect
    oe2x_tame
  have hzero : ∫ ω, (lwG sz n z u x y ω * lwG sz n z u y' x ω * lwPoly sz n z u P ω -
        (m * (if x = y then 1 else 0) * lwG sz n z u y' x ω * lwPoly sz n z u P ω +
          m ^ 3 * Sp x y * lwG sz n z u y' y ω * lwPoly sz n z u P ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * lwG sz n z u y' x ω * lwPoly sz n z u P ω) +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u β β ω - m) * lwG sz n z u α y ω *
            lwG sz n z u y' α ω * lwPoly sz n z u P ω +
          m * (lwG sz n z u x x ω - m) * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * lwG sz n z u y' α ω *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) * lwG sz n z u β y ω *
            lwG sz n z u y' β ω * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * lwG sz n z u y' x ω *
            dhSample sz n u α x (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β y ω * lwG sz n z u y' α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω)) ∂(Sizes.seqP sz) = 0 := by
    simp_rw [hpt]
    rw [integral_const_mul, integral_finsetSum _ fun w _ => (iZ w).const_mul _]
    simp [integral_const_mul, integral_oe2xDefect hG hz hu P y y']
  have iL : Integrable (fun ω => lwG sz n z u x y ω * lwG sz n z u y' x ω * lwPoly sz n z u P ω)
      (Sizes.seqP sz) := by
    refine Tame.integrable hG ?_
    oe2x_tame
  have iR : Integrable (fun ω => (m * (if x = y then 1 else 0) * lwG sz n z u y' x ω * lwPoly sz n z u P ω +
          m ^ 3 * Sp x y * lwG sz n z u y' y ω * lwPoly sz n z u P ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * lwG sz n z u y' x ω * lwPoly sz n z u P ω) +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u β β ω - m) * lwG sz n z u α y ω *
            lwG sz n z u y' α ω * lwPoly sz n z u P ω +
          m * (lwG sz n z u x x ω - m) * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * lwG sz n z u y' α ω *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) * lwG sz n z u β y ω *
            lwG sz n z u y' β ω * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * lwG sz n z u y' x ω *
            dhSample sz n u α x (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β y ω * lwG sz n z u y' α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω)) (Sizes.seqP sz) := by
    refine Tame.integrable hG ?_
    oe2x_tame
  rw [integral_sub iL iR] at hzero
  linear_combination hzero

end Oe2xStein

/-! ## 3. The pin `LWggExp` on the one-size law -/

/-! ## 4. `(Oe2x)` as a graph operation

For a graph `Γ` with the factors `G_{xy} G_{y'x}` at the internal vertex `x` (`y, y'` vertices of `Γ`; the two
edges are `p.1` and `q.1` for `p ∈ lwSplit Γ.solid`, `q ∈ lwSplit p.2`, so `q.2` are the edges of `f`), the eight
terms of `(Oe2x)` (`7_8:337-339`) are graphs:

* `oe2xR1` (`m δ_{xy} G_{y'x} f`, needs `y ≠ x`): `x` is merged into `y`, `G_{xy}` is dropped
  (a graph on the internal vertices other than `x`; `oe2xR1d` is the unmerged form with the `=`-dotted edge);
* `oe2xR2` (`m³ S⁺_{xy} G_{y'y} f`): both edges dropped, `G_{y'y}` and the blue `S⁺_{xy}` added;
* `owxT1` (`m Σ_α S_{xα} Ǧ_{αα} 𝒢`, the merged term `T1` of `(Owx)`): `R3`;
* `oe2xR4` (`m³ Σ S⁺_{xα} S_{αβ} Ǧ_{ββ} G_{αy} G_{y'α} f`), `oe2xR5` (`m Ǧ_{xx} Σ S_{xα} G_{αy} G_{y'α} f`),
  `oe2xR6` (`m³ Σ S⁺_{xα} S_{αβ} Ǧ_{αα} G_{βy} G_{y'β} f`);
* `oe2xR7 q'`, `oe2xR8 q'` for each `q' ∈ lwSplit q.2` (one graph for each solid edge of `f`): the two derivative
  terms, `-m Σ S_{xα} G_{αy} G_{y'x} ∂_{h_{αx}} f` and `-m³ Σ S⁺_{xα} S_{αβ} G_{βy} G_{y'α} ∂_{h_{βα}} f`
  (the sign of the derivative is in `owxDE`, as for `owxT3`, `owxT4`). -/

section Oe2xGraph

variable {E I : Type*}

/-- `R2`: `m³ S⁺_{xy} G_{y'y} f`. -/
def oe2xR2 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I) :
    LGraph E I :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt id (m ^ 3)
    [⟨true, false, y', y⟩] [⟨true, true, Sum.inr x, y⟩]

/-- `R4`: `m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{ββ} G_{αy} G_{y'α} f`. -/
def oe2xR4 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I) :
    LGraph E (I ⊕ Fin 2) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 2) (m ^ 3)
    [⟨true, false, Sum.inr (Sum.inr 0), owxEmb 2 y⟩, ⟨true, false, owxEmb 2 y', Sum.inr (Sum.inr 0)⟩,
      ⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩]
    [⟨true, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩,
      ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]

/-- `R5`: `m Ǧ_{xx} Σ_α S_{xα} G_{αy} G_{y'α} f`. -/
def oe2xR5 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) m
    [⟨true, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inl x)⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 y⟩, ⟨true, false, owxEmb 1 y', Sum.inr (Sum.inr 0)⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

/-- `R6`: `m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{αα} G_{βy} G_{y'β} f`. -/
def oe2xR6 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I) :
    LGraph E (I ⊕ Fin 2) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 2) (m ^ 3)
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩,
      ⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 y⟩, ⟨true, false, owxEmb 2 y', Sum.inr (Sum.inr 1)⟩]
    [⟨true, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩,
      ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]

/-- `R7` for the solid edge `q'.1` of `f` (`q' ∈ lwSplit q.2`, `q'.2` the others):
`-m Σ_α S_{xα} G_{αy} G_{y'x} ∂_{h_{αx}}` applied to `q'.1`. -/
def oe2xR7 (m : ℂ) (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q'.2 } : LGraph E I).owxExt (owxEmb 1) m
    [⟨true, false, owxEmb 1 y', Sum.inr (Sum.inl x)⟩,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q'.1)).1,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q'.1)).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 y⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

/-- `R8` for the solid edge `q'.1` of `f`: `-m³ Σ_{α,β} S⁺_{xα} S_{αβ} G_{βy} G_{y'α} ∂_{h_{βα}}` applied to
`q'.1`. -/
def oe2xR8 (m : ℂ) (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 2) :=
  ({ Γ with solid := q'.2 } : LGraph E I).owxExt (owxEmb 2) (m ^ 3)
    [⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 y⟩, ⟨true, false, owxEmb 2 y', Sum.inr (Sum.inr 0)⟩,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q'.1)).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q'.1)).2]
    [⟨true, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩,
      ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]

/-- `R1d`: `m δ_{xy} G_{y'x} f` with the `=`-dotted edge `x = y` (the vertex `x` is kept). -/
def oe2xR1d (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y : E ⊕ I) :
    LGraph E I where
  solid := p.2
  waved := Γ.waved
  dotted := ⟨true, Sum.inr x, y⟩ :: Γ.dotted
  coeff := m * Γ.coeff

end Oe2xGraph

/-! ### `R1`: the merge `x ↦ y` -/

section Oe2xMerge

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- A vertex other than the internal vertex `x`, as a vertex of the graph without `x`. -/
def oe2xRet (x : I) : (v : E ⊕ I) → v ≠ Sum.inr x → E ⊕ {i : I // i ≠ x}
  | Sum.inl a, _ => Sum.inl a
  | Sum.inr i, h => Sum.inr ⟨i, fun e => h (congrArg Sum.inr e)⟩

/-- The vertex map of the merge: `x ↦ y`, every other vertex to itself. -/
def oe2xPhi (x : I) (y : E ⊕ I) (hy : y ≠ Sum.inr x) (v : E ⊕ I) : E ⊕ {i : I // i ≠ x} :=
  if h : v = Sum.inr x then oe2xRet x y hy else oe2xRet x v h

/-- **`R1`**: `m δ_{xy} G_{y'x} f`: `G_{xy}` (`p.1`) is dropped and the internal vertex `x` is merged into
`y ≠ x` (a graph on the internal vertices other than `x`). -/
def oe2xR1 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y : E ⊕ I)
    (hy : y ≠ Sum.inr x) : LGraph E {i : I // i ≠ x} :=
  ({ Γ with solid := p.2, coeff := m * Γ.coeff } : LGraph E I).relabel (oe2xPhi x y hy)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A labelling of `I` is a label of `x` and a labelling of the other vertices. -/
def oe2xSplit (x : I) (ι : Type*) : ι × ({i : I // i ≠ x} → ι) ≃ (I → ι) where
  toFun a := fun i => if h : i = x then a.1 else a.2 ⟨i, h⟩
  invFun ℓ := (ℓ x, fun j => ℓ j.1)
  left_inv a := by
    refine Prod.ext (by simp) (funext fun j => ?_)
    simp [j.2]
  right_inv ℓ := by
    funext i
    by_cases h : i = x
    · subst h; simp
    · simp [h]

theorem oe2xSplit_apply_x (x : I) (a : ι) (ℓ' : {i : I // i ≠ x} → ι) : oe2xSplit x ι (a, ℓ') x = a := by
  simp [oe2xSplit]

theorem oe2xSplit_apply_ne (x : I) (a : ι) (ℓ' : {i : I // i ≠ x} → ι) (i : I) (h : i ≠ x) :
    oe2xSplit x ι (a, ℓ') i = ℓ' ⟨i, h⟩ := by
  simp [oe2xSplit, h]

/-- **The merged graph has the value of the graph with the dotted edge `x = y`.** -/
theorem oe2xR1_val (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y : E ⊕ I)
    (hy : y ≠ Sum.inr x) (D : LData ι) (ℓe : E → ι) :
    (oe2xR1 m Γ p x y hy).val D ℓe = (oe2xR1d m Γ p x y).val D ℓe := by
  classical
  set Γ₁ : LGraph E I := { Γ with solid := p.2, coeff := m * Γ.coeff } with hΓ₁
  have hterm : ∀ ℓ : E ⊕ I → ι, (oe2xR1d m Γ p x y).term D ℓ =
      Γ₁.term D ℓ * (if ℓ (Sum.inr x) = ℓ y then 1 else 0) := by
    intro ℓ
    simp only [LGraph.term, oe2xR1d, hΓ₁, List.map_cons, List.prod_cons, DEdge.val, iff_true]
    ring
  have hret : ∀ (ℓ' : {i : I // i ≠ x} → ι) (a : ι),
      Sum.elim ℓe (oe2xSplit x ι (a, ℓ')) y = Sum.elim ℓe ℓ' (oe2xRet x y hy) := by
    intro ℓ' a
    rcases y with b | j
    · rfl
    · have hj : j ≠ x := fun e => hy (by rw [e])
      simp [oe2xRet, oe2xSplit_apply_ne x a ℓ' j hj]
  have hφ : ∀ (ℓ' : {i : I // i ≠ x} → ι), Sum.elim ℓe ℓ' ∘ oe2xPhi x y hy =
      Sum.elim ℓe (oe2xSplit x ι (Sum.elim ℓe ℓ' (oe2xRet x y hy), ℓ')) := by
    intro ℓ'
    funext v
    rcases v with a | i
    · simp [oe2xPhi, oe2xRet]
    · by_cases h : i = x
      · subst h
        simp [oe2xPhi, oe2xSplit_apply_x]
      · simp [oe2xPhi, h, oe2xRet, oe2xSplit_apply_ne x _ ℓ' i h]
  unfold LGraph.val
  simp only [oe2xR1, LGraph.term_relabel, hterm]
  rw [← (oe2xSplit x ι).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  have h2 : ∀ a : ι, Γ₁.term D (Sum.elim ℓe (oe2xSplit x ι (a, ℓ'))) *
      (if Sum.elim ℓe (oe2xSplit x ι (a, ℓ')) (Sum.inr x) = Sum.elim ℓe (oe2xSplit x ι (a, ℓ')) y then 1 else 0) =
      if a = Sum.elim ℓe ℓ' (oe2xRet x y hy) then Γ₁.term D (Sum.elim ℓe (oe2xSplit x ι (a, ℓ'))) else 0 := by
    intro a
    rw [hret ℓ' a]
    have : Sum.elim ℓe (oe2xSplit x ι (a, ℓ')) (Sum.inr x) = a := oe2xSplit_apply_x x a ℓ'
    rw [this]
    split_ifs <;> simp
  simp_rw [h2]
  rw [Finset.sum_ite_eq' Finset.univ (Sum.elim ℓe ℓ' (oe2xRet x y hy))
    (fun a => Γ₁.term D (Sum.elim ℓe (oe2xSplit x ι (a, ℓ'))))]
  simp only [Finset.mem_univ, ite_true]
  rw [hφ]

end Oe2xMerge

/-! ### The counters of the eight terms -/

section Oe2xCounters

variable {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']

/-- **A vertex map that carries molecules into molecules and meets every molecule of `Γ'` cannot increase
`n_M`**: if every vertex of `Γ'` is in the molecule of some `φ v`, `φ` fixes the external vertices, and every
waved or `=`-dotted edge `u v` of `Γ` is sent to vertices `φ u`, `φ v` of the same molecule of `Γ'`, then `Γ'` has at
most as many internal molecules as `Γ`. -/
theorem oe2x_nM_le (Γ : LGraph E I) (Γ' : LGraph E I') (φ : E ⊕ I → E ⊕ I')
    (hφ : ∀ v', ∃ v, Γ'.molGraph.Reachable v' (φ v))
    (hl : ∀ a : E, φ (Sum.inl a) = Sum.inl a)
    (hadj : ∀ u v, Γ.adj u v = true → Γ'.molGraph.Reachable (φ u) (φ v)) : Γ'.nM ≤ Γ.nM := by
  classical
  rw [Γ'.nM_eq_card, Γ.nM_eq_card]
  have hwalk : ∀ {v w : E ⊕ I} (p : Γ.molGraph.Walk v w), Γ'.molGraph.Reachable (φ v) (φ w) := by
    intro v w p
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih =>
      exact (hadj _ _ ((owx_molGraph_adj Γ _ _).1 h).2).trans ih
  let ψ : Γ.Mol → Γ'.Mol :=
    SimpleGraph.ConnectedComponent.lift (fun v => Γ'.molOf (φ v))
      (fun _ _ p _ => SimpleGraph.ConnectedComponent.eq.2 (hwalk p))
  have hψmk : ∀ v, ψ (Γ.molOf v) = Γ'.molOf (φ v) := fun v => rfl
  have hψ : Function.Surjective ψ := by
    intro c'
    induction c' using SimpleGraph.ConnectedComponent.ind with | h v' => ?_
    obtain ⟨v, hv⟩ := hφ v'
    exact ⟨Γ.molOf v, (SimpleGraph.ConnectedComponent.eq.2 hv).symm⟩
  have hint : ∀ c' : Γ'.Mol, ¬ Γ'.IsExtMol c' → ¬ Γ.IsExtMol (Function.surjInv hψ c') := by
    rintro c' hc' ⟨a, ha⟩
    apply hc'
    refine ⟨a, ?_⟩
    have h1 : ψ (Γ.molOf (Sum.inl a)) = c' := by
      rw [ha]; exact Function.surjInv_eq hψ c'
    rw [hψmk, hl] at h1
    exact h1
  let g : {c' : Γ'.Mol // ¬ Γ'.IsExtMol c'} → {c : Γ.Mol // ¬ Γ.IsExtMol c} :=
    fun c' => ⟨Function.surjInv hψ c'.1, hint c'.1 c'.2⟩
  have hg : Function.Injective g := by
    intro c₁ c₂ h
    apply Subtype.ext
    have := congrArg (fun c : {c : Γ.Mol // ¬ Γ.IsExtMol c} => ψ c.1) h
    simpa [g, Function.surjInv_eq hψ] using this
  exact Nat.card_le_card_of_injective g hg

/-- A relabelled graph joins the images of the vertices that a waved or `=`-dotted edge joins. -/
theorem oe2x_adj_relabel {I'' : Type} [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (φ : E ⊕ I → E ⊕ I'') (u v : E ⊕ I)
    (h : Γ.adj u v = true) : (Γ.relabel φ).adj (φ u) (φ v) = true := by
  simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
    Bool.and_eq_true] at h ⊢
  rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
  · left
    refine ⟨WEdge.map φ e, ?_, ?_⟩
    · exact List.mem_map_of_mem he
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; simp [WEdge.map, h1, h2]
      · right; simp [WEdge.map, h1, h2]
  · right
    refine ⟨DEdge.map φ e, ?_, ?_, ?_⟩
    · exact List.mem_map_of_mem he
    · simpa [DEdge.map] using h1
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; simp [DEdge.map, h1, h2]
      · right; simp [DEdge.map, h1, h2]

/-- `Γ.owxExt` joins the images of the vertices that `Γ` joins. -/
theorem oe2x_adj_owxExt {I'' : Type} [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (emb : E ⊕ I → E ⊕ I'') (c : ℂ)
    (s : List (SEdge (E ⊕ I''))) (w : List (WEdge (E ⊕ I''))) (u v : E ⊕ I) (h : Γ.adj u v = true) :
    (Γ.owxExt emb c s w).adj (emb u) (emb v) = true := by
  simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
    Bool.and_eq_true] at h ⊢
  rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
  · left
    refine ⟨WEdge.map emb e, ?_, ?_⟩
    · exact List.mem_append_left _ (List.mem_map_of_mem he)
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; simp [WEdge.map, h1, h2]
      · right; simp [WEdge.map, h1, h2]
  · right
    refine ⟨DEdge.map emb e, ?_, ?_, ?_⟩
    · exact List.mem_map_of_mem he
    · simpa [DEdge.map] using h1
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; simp [DEdge.map, h1, h2]
      · right; simp [DEdge.map, h1, h2]

theorem oe2xPhi_surjective (x : I) (y : E ⊕ I) (hy : y ≠ Sum.inr x) :
    Function.Surjective (oe2xPhi x y hy) := by
  intro v'
  rcases v' with a | ⟨i, hi⟩
  · exact ⟨Sum.inl a, by simp [oe2xPhi, oe2xRet]⟩
  · refine ⟨Sum.inr i, ?_⟩
    have : (Sum.inr i : E ⊕ I) ≠ Sum.inr x := fun e => hi (Sum.inr_injective e)
    simp [oe2xPhi, this, oe2xRet]

theorem oe2x_card_subtype (x : I) : Fintype.card {i : I // i ≠ x} + 1 = Fintype.card I := by
  have h : Fintype.card {i : I // i ≠ x} = Fintype.card I - Fintype.card {i : I // i = x} :=
    Fintype.card_subtype_compl (fun i : I => i = x)
  have h1 : Fintype.card {i : I // i = x} = 1 := Fintype.card_subtype_eq x
  have h2 : 0 < Fintype.card I := Fintype.card_pos_iff.2 ⟨x⟩
  omega

/-- **`R1` counters**: `n_S` one less, `n_W` the same, `n_V` one less (`x` is merged into `y`), `n_M` not larger;
so `ord` rises by one. -/
theorem oe2xR1_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (y : E ⊕ I) (hy : y ≠ Sum.inr x) :
    (oe2xR1 m Γ p x y hy).nS + 1 = Γ.nS ∧ (oe2xR1 m Γ p x y hy).nW = Γ.nW ∧
      (oe2xR1 m Γ p x y hy).nV + 1 = Γ.nV ∧ (oe2xR1 m Γ p x y hy).nM ≤ Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  refine ⟨?_, by simp [oe2xR1, LGraph.relabel, LGraph.nW], oe2x_card_subtype x, ?_⟩
  · simp only [oe2xR1, LGraph.relabel, LGraph.nS, List.length_map]
    omega
  · set Γ₁ : LGraph E I := { Γ with solid := p.2, coeff := m * Γ.coeff } with hΓ₁
    have h1 : Γ₁.nM = Γ.nM := lwStein_nM_congr _ _ rfl rfl
    rw [← h1]
    refine oe2x_nM_le Γ₁ (oe2xR1 m Γ p x y hy) (oe2xPhi x y hy)
      (fun v' => by
        obtain ⟨v, hv⟩ := oe2xPhi_surjective x y hy v'
        exact ⟨v, by rw [hv]⟩)
      (fun a => by simp [oe2xPhi, oe2xRet]) fun u v h => ?_
    by_cases huv : oe2xPhi x y hy u = oe2xPhi x y hy v
    · rw [huv]
    · exact SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨huv, oe2x_adj_relabel Γ₁ _ u v h⟩)

theorem oe2xR2_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) :
    (oe2xR2 m Γ q x y y').nS + 1 = Γ.nS ∧ (oe2xR2 m Γ q x y y').nW = Γ.nW + 1 ∧
      (oe2xR2 m Γ q x y y').nV = Γ.nV ∧ (oe2xR2 m Γ q x y y').nM ≤ Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [oe2xR2, LGraph.owxExt, LGraph.nW], rfl, ?_⟩
  · simp only [oe2xR2, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · set Γ₁ : LGraph E I := { Γ with solid := q.2 } with hΓ₁
    have h1 : Γ₁.nM = Γ.nM := lwStein_nM_congr _ _ rfl rfl
    rw [← h1]
    refine oe2x_nM_le Γ₁ (oe2xR2 m Γ q x y y') id (fun v' => ⟨v', SimpleGraph.Reachable.refl _⟩) (fun a => rfl)
      fun u v h => ?_
    by_cases huv : u = v
    · rw [huv]
    · exact SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2
        ⟨huv, oe2x_adj_owxExt Γ₁ id (m ^ 3) _ _ u v h⟩)

theorem oe2xR4_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) :
    (oe2xR4 m Γ q x y y').nS = Γ.nS + 1 ∧ (oe2xR4 m Γ q x y y').nW = Γ.nW + 2 ∧
      (oe2xR4 m Γ q x y y').nV = Γ.nV + 2 ∧ (oe2xR4 m Γ q x y y').nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [oe2xR4, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [oe2xR4, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (oe2xR4 m Γ q x y y').nM = ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 2 x (m ^ 3) _ _ ?_
        (owxExt_reach2 _ x (m ^ 3) _ _ true true false true (by simp) (by simp))
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem oe2xR5_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) :
    (oe2xR5 m Γ q x y y').nS = Γ.nS + 1 ∧ (oe2xR5 m Γ q x y y').nW = Γ.nW + 1 ∧
      (oe2xR5 m Γ q x y y').nV = Γ.nV + 1 ∧ (oe2xR5 m Γ q x y y').nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [oe2xR5, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [oe2xR5, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (oe2xR5 m Γ q x y y').nM = ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 1 x m _ _ ?_ (owxExt_reach1 _ x m _ _ false true (by simp))
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem oe2xR6_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) :
    (oe2xR6 m Γ q x y y').nS = Γ.nS + 1 ∧ (oe2xR6 m Γ q x y y').nW = Γ.nW + 2 ∧
      (oe2xR6 m Γ q x y y').nV = Γ.nV + 2 ∧ (oe2xR6 m Γ q x y y').nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [oe2xR6, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [oe2xR6, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (oe2xR6 m Γ q x y y').nM = ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 2 x (m ^ 3) _ _ ?_
        (owxExt_reach2 _ x (m ^ 3) _ _ true true false true (by simp) (by simp))
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem oe2xR7_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2) :
    (oe2xR7 m Γ x y y' q').nS = Γ.nS + 1 ∧ (oe2xR7 m Γ x y y' q').nW = Γ.nW + 1 ∧
      (oe2xR7 m Γ x y y' q').nV = Γ.nV + 1 ∧ (oe2xR7 m Γ x y y' q').nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hl'' := lwSplit_snd_length q.2 q' hq'
  refine ⟨?_, by simp [oe2xR7, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [oe2xR7, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (oe2xR7 m Γ x y y' q').nM = ({ Γ with solid := q'.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 1 x m _ _ ?_ (owxExt_reach1 _ x m _ _ false true (by simp))
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem oe2xR8_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2) :
    (oe2xR8 m Γ x y y' q').nS = Γ.nS + 1 ∧ (oe2xR8 m Γ x y y' q').nW = Γ.nW + 2 ∧
      (oe2xR8 m Γ x y y' q').nV = Γ.nV + 2 ∧ (oe2xR8 m Γ x y y' q').nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hl'' := lwSplit_snd_length q.2 q' hq'
  refine ⟨?_, by simp [oe2xR8, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [oe2xR8, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (oe2xR8 m Γ x y y' q').nM = ({ Γ with solid := q'.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 2 x (m ^ 3) _ _ ?_
        (owxExt_reach2 _ x (m ^ 3) _ _ true true false true (by simp) (by simp))
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

end Oe2xCounters

/-! ### The values of the terms -/

section Oe2xTermVal

variable {E I : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

/-- The value of a term of `oe2xR7` at a labelling `ℓ'` extending `ℓ` (`ℓ' ∘ owxEmb 1 = ℓ`). -/
theorem oe2xR7_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : I) (y y' : E ⊕ I)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 1) → ι)
    (hℓ : ℓ' ∘ owxEmb 1 = ℓ) :
    (oe2xR7 m Γ x y y' q').term D ℓ' = m * ({ Γ with solid := q'.2 } : LGraph E I).term D ℓ *
      (D.G (ℓ y') (ℓ (Sum.inr x)) *
        ((if q'.1.σ then D.G (ℓ q'.1.src) (ℓ' (Sum.inr (Sum.inr 0))) * D.G (ℓ (Sum.inr x)) (ℓ q'.1.dst)
          else star (D.G (ℓ q'.1.src) (ℓ (Sum.inr x))) * star (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q'.1.dst))) *
          D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ y))) *
      D.S (ℓ (Sum.inr x)) (ℓ' (Sum.inr (Sum.inr 0))) := by
  have hx : ℓ' (Sum.inr (Sum.inl x)) = ℓ (Sum.inr x) := by
    rw [← hℓ]; rfl
  have hq : ∀ v, ℓ' (owxEmb 1 v) = ℓ v := fun v => by rw [← hℓ]; rfl
  have h : SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q'.1)).1 *
      SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q'.1)).2 =
      if q'.1.σ then D.G (ℓ q'.1.src) (ℓ' (Sum.inr (Sum.inr 0))) * D.G (ℓ (Sum.inr x)) (ℓ q'.1.dst)
      else star (D.G (ℓ q'.1.src) (ℓ (Sum.inr x))) * star (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q'.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq, hx]
  rw [oe2xR7, LGraph.term_owxExt, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← h]
  simp [SEdge.val, WEdge.val, hx, hq]
  ring_nf

/-- The value of a term of `oe2xR8` at a labelling `ℓ'` extending `ℓ` (`ℓ' ∘ owxEmb 2 = ℓ`). -/
theorem oe2xR8_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : I) (y y' : E ⊕ I)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι)
    (hℓ : ℓ' ∘ owxEmb 2 = ℓ) :
    (oe2xR8 m Γ x y y' q').term D ℓ' = m ^ 3 * ({ Γ with solid := q'.2 } : LGraph E I).term D ℓ *
      (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ y) * D.G (ℓ y') (ℓ' (Sum.inr (Sum.inr 0))) *
        (if q'.1.σ then D.G (ℓ q'.1.src) (ℓ' (Sum.inr (Sum.inr 1))) * D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q'.1.dst)
          else star (D.G (ℓ q'.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) * star (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ q'.1.dst)))) *
      (D.Sp (ℓ (Sum.inr x)) (ℓ' (Sum.inr (Sum.inr 0))) *
        D.S (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 1)))) := by
  have hx : ℓ' (Sum.inr (Sum.inl x)) = ℓ (Sum.inr x) := by
    rw [← hℓ]; rfl
  have hq : ∀ v, ℓ' (owxEmb 2 v) = ℓ v := fun v => by rw [← hℓ]; rfl
  have h : SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q'.1)).1 *
      SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q'.1)).2 =
      if q'.1.σ then D.G (ℓ q'.1.src) (ℓ' (Sum.inr (Sum.inr 1))) * D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q'.1.dst)
      else star (D.G (ℓ q'.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) * star (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ q'.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq]
  rw [oe2xR8, LGraph.term_owxExt, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← h]
  simp [SEdge.val, WEdge.val, hx, hq]
  ring_nf

/-- The value of the term `R1d`: that of the graph without `G_{xy}` times the `=`-dotted factor. -/
theorem oe2xR1d_term (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y : E ⊕ I) (D : LData ι) (ℓ : E ⊕ I → ι) :
    (oe2xR1d m Γ p x y).term D ℓ =
      ({ Γ with solid := p.2, coeff := m * Γ.coeff } : LGraph E I).term D ℓ *
        (if ℓ (Sum.inr x) = ℓ y then 1 else 0) := by
  simp only [LGraph.term, oe2xR1d, List.map_cons, List.prod_cons, DEdge.val, iff_true]
  ring

end Oe2xTermVal

/-! ### `(Oe2x)` at one labelling of the vertices of `Γ` -/

section Oe2xIdentity

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`(Oe2x)` for one labelling of the vertices of `Γ`** (expectations of terms): `Γ` has the factors
`G_{xy}` (`p.1`) and `G_{y'x}` (`q.1`) at the internal vertex `x`, `q.2` the other solid edges (`f`); `E Γ.term(ℓ)` is
the sum of the expectations of the terms of `oe2xR1d` (the vertex `x` kept, with the dotted factor `δ_{xy}`),
`oe2xR2`, `owxT1` (`R3`), `oe2xR4`, `oe2xR5`, `oe2xR6` and, for each solid edge `q'.1` of `f`, of `oe2xR7 q'`,
`oe2xR8 q'`, summed over the labels of the new vertices.  Hypotheses: `GaussIBP` (proved: `gaussIBP sz`),
`Im z > 0`, `u > 0`, `m ≠ 0`, `z + u m = -m⁻¹`, `S⁺ (1 - m² S) = S`, `M_{aa} = m`. -/
theorem oe2x_term_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (x : I) (y y' : E ⊕ I)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hq1 : q.1 = ⟨true, false, y', Sum.inr x⟩)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) (ℓi : I → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) =
      ∫ ω, (oe2xR1d m Γ p x y).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR2 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) +
      ∑ α, ∫ ω, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) +
      ∑ α, ∑ β, ∫ ω, (oe2xR4 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) +
      ∑ α, ∫ ω, (oe2xR5 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) +
      ∑ α, ∑ β, ∫ ω, (oe2xR6 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) +
      ∑ α, ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR7 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum +
      ∑ α, ∑ β, ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR8 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
  classical
  have hz' : z.im ≠ 0 := hz.ne'
  set ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n) := Sum.elim ℓe ℓi with hℓ
  set xl : Idx d (sz.L n) (sz.W n) := ℓi x with hxl
  set yl : Idx d (sz.L n) (sz.W n) := ℓ y with hyl
  set y'l : Idx d (sz.L n) (sz.W n) := ℓ y' with hy'l
  set K : ℂ := lwK Γ M (lwS sz n u) Sp ℓ with hK
  set P := (q.2.map (owxEdgePoly sz n M ℓ)).prod with hPdef
  have hf : ∀ ω, lwPoly sz n z u P ω =
      (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod :=
    fun ω => lwPoly_owxEdgePoly_prod z u M (lwS sz n u) Sp ℓ q.2 ω
  have hℓx : ℓ (Sum.inr x) = xl := rfl
  have hv1 : ∀ ω, SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ p.1 = lwG sz n z u xl yl ω := by
    intro ω
    rw [hp1]
    simp [SEdge.val, lwSampleData, lwG, hℓx, ← hyl]
  have hv2 : ∀ ω, SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ q.1 = lwG sz n z u y'l xl ω := by
    intro ω
    rw [hq1]
    simp [SEdge.val, lwSampleData, lwG, hℓx, ← hy'l]
  have hΓ : ∀ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
      K * (lwG sz n z u xl yl ω * (lwG sz n z u y'l xl ω * lwPoly sz n z u P ω)) := by
    intro ω
    rw [lwStein_term_eq, lwSplit_prod Γ.solid _ p hp, lwSplit_prod p.2 _ q hq, hv1 ω, hv2 ω, hf ω]
  have hK' : ∀ s : List (SEdge (E ⊕ I)),
      lwK ({ Γ with solid := s } : LGraph E I) M (lwS sz n u) Sp ℓ = K := fun s => rfl
  have hbase : ∀ (s : List (SEdge (E ⊕ I))) ω, ({ Γ with solid := s } : LGraph E I).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
      K * (s.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod := by
    intro s ω
    rw [lwStein_term_eq, hK']
  have hT1 : ∀ ω, (oe2xR1d m Γ p x y).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
      m * K * (if xl = yl then 1 else 0) * (lwG sz n z u y'l xl ω * lwPoly sz n z u P ω) := by
    intro ω
    rw [oe2xR1d_term, lwStein_term_eq, lwSplit_prod p.2 _ q hq, hv2 ω, hf ω]
    have : lwK ({ Γ with solid := p.2, coeff := m * Γ.coeff } : LGraph E I) M (lwS sz n u) Sp ℓ = m * K := by
      simp only [lwK, hK]
      ring
    rw [this, hℓx]
    ring
  have hT2 : ∀ ω, (oe2xR2 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
      m ^ 3 * (K * lwPoly sz n z u P ω) * lwG sz n z u y'l yl ω * Sp xl yl := by
    intro ω
    rw [oe2xR2, LGraph.term_owxExt, Function.comp_id, hbase q.2 ω, ← hf ω]
    simp [SEdge.val, WEdge.val, lwSampleData, lwG, hℓx]
    ring
  have hT3 : ∀ α ω, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * (lwG sz n z u xl yl ω * (lwG sz n z u y'l xl ω * lwPoly sz n z u P ω))) *
        (lwG sz n z u α α ω - m) * lwS sz n u xl α := by
    intro α ω
    rw [owxT1_term _ m Γ x ℓ _ (owxLab1_emb ℓe ℓi α), hΓ ω]
    simp [owxLab1, lwSampleData, lwG, hM, hℓx]
  have hT4 : ∀ α β ω, (oe2xR4 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) =
      m ^ 3 * (K * lwPoly sz n z u P ω) *
        (lwG sz n z u α yl ω * lwG sz n z u y'l α ω * (lwG sz n z u β β ω - m)) *
        (Sp xl α * lwS sz n u α β) := by
    intro α β ω
    have hq2 : ∀ v, owxLab2 ℓe ℓi α β (owxEmb 2 v) = ℓ v := fun v => by
      rcases v with a | b <;> rfl
    have ha0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
    have hb1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
    have hx2 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inl x)) = xl := rfl
    rw [oe2xR4, LGraph.term_owxExt, owxLab2_emb, hbase q.2 ω, ← hf ω]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val,
      lwSampleData, lwG, hM, hq2, ha0, hb1, hx2, ← hyl, ← hy'l, ↓reduceIte, Bool.false_eq_true, sub_zero]
    ring
  have hT5 : ∀ α ω, (oe2xR5 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * lwPoly sz n z u P ω) *
        ((lwG sz n z u xl xl ω - m) * lwG sz n z u α yl ω * lwG sz n z u y'l α ω) * lwS sz n u xl α := by
    intro α ω
    have hq2 : ∀ v, owxLab1 ℓe ℓi α (owxEmb 1 v) = ℓ v := fun v => by
      rcases v with a | b <;> rfl
    have ha0 : owxLab1 ℓe ℓi α (Sum.inr (Sum.inr 0)) = α := rfl
    have hx2 : owxLab1 ℓe ℓi α (Sum.inr (Sum.inl x)) = xl := rfl
    rw [oe2xR5, LGraph.term_owxExt, owxLab1_emb, hbase q.2 ω, ← hf ω]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val,
      lwSampleData, lwG, hM, hq2, ha0, hx2, ← hyl, ← hy'l, ↓reduceIte, Bool.false_eq_true, sub_zero]
    ring
  have hT6 : ∀ α β ω, (oe2xR6 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) =
      m ^ 3 * (K * lwPoly sz n z u P ω) *
        ((lwG sz n z u α α ω - m) * lwG sz n z u β yl ω * lwG sz n z u y'l β ω) *
        (Sp xl α * lwS sz n u α β) := by
    intro α β ω
    have hq2 : ∀ v, owxLab2 ℓe ℓi α β (owxEmb 2 v) = ℓ v := fun v => by
      rcases v with a | b <;> rfl
    have ha0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
    have hb1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
    have hx2 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inl x)) = xl := rfl
    rw [oe2xR6, LGraph.term_owxExt, owxLab2_emb, hbase q.2 ω, ← hf ω]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val,
      lwSampleData, lwG, hM, hq2, ha0, hb1, hx2, ← hyl, ← hy'l, ↓reduceIte, Bool.false_eq_true, sub_zero]
    ring
  have hT7 : ∀ (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) α ω,
      (oe2xR7 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * (q'.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod) *
        (lwG sz n z u y'l xl ω * ((if q'.1.σ then lwG sz n z u (ℓ q'.1.src) α ω * lwG sz n z u xl (ℓ q'.1.dst) ω
          else star (lwG sz n z u (ℓ q'.1.src) xl ω) * star (lwG sz n z u α (ℓ q'.1.dst) ω)) *
          lwG sz n z u α yl ω)) * lwS sz n u xl α := by
    intro q' α ω
    have ha0 : owxLab1 ℓe ℓi α (Sum.inr (Sum.inr 0)) = α := rfl
    rw [oe2xR7_term _ m Γ x y y' q' ℓ _ (owxLab1_emb ℓe ℓi α), hbase q'.2 ω]
    simp only [lwSampleData, lwG, ha0, hℓx, ← hyl, ← hy'l]
  have hT8 : ∀ (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) α β ω,
      (oe2xR8 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) =
      m ^ 3 * (K * (q'.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod) *
        (lwG sz n z u β yl ω * lwG sz n z u y'l α ω *
          (if q'.1.σ then lwG sz n z u (ℓ q'.1.src) β ω * lwG sz n z u α (ℓ q'.1.dst) ω
          else star (lwG sz n z u (ℓ q'.1.src) α ω) * star (lwG sz n z u β (ℓ q'.1.dst) ω))) *
        (Sp xl α * lwS sz n u α β) := by
    intro q' α β ω
    have ha0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
    have hb1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
    rw [oe2xR8_term _ m Γ x y y' q' ℓ _ (owxLab2_emb ℓe ℓi α β), hbase q'.2 ω]
    simp only [lwSampleData, lwG, ha0, hb1, hℓx, ← hyl, ← hy'l]
  have hdh : ∀ (α w : Idx d (sz.L n) (sz.W n)) ω, dhSample sz n u α w (lwPoly sz n z u P) ω =
      ((lwSplit q.2).map fun q' =>
        (if q'.1.σ then -(lwG sz n z u (ℓ q'.1.src) α ω * lwG sz n z u w (ℓ q'.1.dst) ω)
          else -(star (lwG sz n z u (ℓ q'.1.src) w ω) * star (lwG sz n z u α (ℓ q'.1.dst) ω))) *
        (q'.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod).sum := by
    intro α w ω
    have hfun : lwPoly sz n z u P = fun ω => (q.2.map fun a =>
        SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ a).prod := funext hf
    rw [hfun, lwStein_dh_listProd q.2 (fun e _ => lwStein_sedge_val_tame1 hz e ℓ)]
    congr 1
    refine List.map_congr_left fun q' _ => ?_
    rw [lwStein_dh_sedge_val hz hu q'.1 α w ℓ ω]
  have hS7 : ∀ α ω, ((lwSplit q.2).map fun q' => (oe2xR7 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum =
      -(K * (m * (lwS sz n u xl α * lwG sz n z u α yl ω * lwG sz n z u y'l xl ω)) *
        dhSample sz n u α xl (lwPoly sz n z u P) ω) := by
    intro α ω
    rw [hdh α xl ω]
    refine owx_list_aux _ _ _ _ fun q' _ => ?_
    rw [hT7 q' α ω]
    by_cases hσ : q'.1.σ <;> simp [hσ] <;> ring
  have hS8 : ∀ α β ω, ((lwSplit q.2).map fun q' => (oe2xR8 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum =
      -(K * (m ^ 3 * (Sp xl α * lwS sz n u α β * lwG sz n z u β yl ω * lwG sz n z u y'l α ω)) *
        dhSample sz n u β α (lwPoly sz n z u P) ω) := by
    intro α β ω
    rw [hdh β α ω]
    refine owx_list_aux _ _ _ _ fun q' _ => ?_
    rw [hT8 q' α β ω]
    by_cases hσ : q'.1.σ <;> simp [hσ] <;> ring
  have hpath : ∀ ω, K * (m * (if xl = yl then 1 else 0) * lwG sz n z u y'l xl ω * lwPoly sz n z u P ω +
          m ^ 3 * Sp xl yl * lwG sz n z u y'l yl ω * lwPoly sz n z u P ω +
          m * (∑ α, lwS sz n u xl α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u xl yl ω * lwG sz n z u y'l xl ω * lwPoly sz n z u P ω) +
          m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * (lwG sz n z u β β ω - m) * lwG sz n z u α yl ω *
            lwG sz n z u y'l α ω * lwPoly sz n z u P ω +
          m * (lwG sz n z u xl xl ω - m) * ∑ α, lwS sz n u xl α * lwG sz n z u α yl ω * lwG sz n z u y'l α ω *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * (lwG sz n z u α α ω - m) * lwG sz n z u β yl ω *
            lwG sz n z u y'l β ω * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u xl α * lwG sz n z u α yl ω * lwG sz n z u y'l xl ω *
            dhSample sz n u α xl (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * lwG sz n z u β yl ω * lwG sz n z u y'l α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω) =
      (oe2xR1d m Γ p x y).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ + (oe2xR2 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ +
      ∑ α, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) +
      ∑ α, ∑ β, (oe2xR4 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) +
      ∑ α, (oe2xR5 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) +
      ∑ α, ∑ β, (oe2xR6 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) +
      ∑ α, ((lwSplit q.2).map fun q' => (oe2xR7 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum +
      ∑ α, ∑ β, ((lwSplit q.2).map fun q' => (oe2xR8 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum := by
    intro ω
    simp only [hT1, hT2, hT3, hT4, hT5, hT6, hS7, hS8]
    have hA3 : ∑ a, m * (K * (lwG sz n z u xl yl ω * (lwG sz n z u y'l xl ω * lwPoly sz n z u P ω))) *
        (lwG sz n z u a a ω - m) * lwS sz n u xl a =
        K * (m * (∑ α, lwS sz n u xl α * (lwG sz n z u α α ω - m)) *
          (lwG sz n z u xl yl ω * lwG sz n z u y'l xl ω * lwPoly sz n z u P ω)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hA4 : ∑ a, ∑ b, m ^ 3 * (K * lwPoly sz n z u P ω) *
        (lwG sz n z u a yl ω * lwG sz n z u y'l a ω * (lwG sz n z u b b ω - m)) * (Sp xl a * lwS sz n u a b) =
        K * (m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * (lwG sz n z u β β ω - m) * lwG sz n z u α yl ω *
          lwG sz n z u y'l α ω * lwPoly sz n z u P ω) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
    have hA5 : ∑ a, m * (K * lwPoly sz n z u P ω) *
        ((lwG sz n z u xl xl ω - m) * lwG sz n z u a yl ω * lwG sz n z u y'l a ω) * lwS sz n u xl a =
        K * (m * (lwG sz n z u xl xl ω - m) * ∑ α, lwS sz n u xl α * lwG sz n z u α yl ω *
          lwG sz n z u y'l α ω * lwPoly sz n z u P ω) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hA6 : ∑ a, ∑ b, m ^ 3 * (K * lwPoly sz n z u P ω) *
        ((lwG sz n z u a a ω - m) * lwG sz n z u b yl ω * lwG sz n z u y'l b ω) * (Sp xl a * lwS sz n u a b) =
        K * (m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * (lwG sz n z u α α ω - m) * lwG sz n z u β yl ω *
          lwG sz n z u y'l β ω * lwPoly sz n z u P ω) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
    have hA7 : ∑ a, -(K * (m * (lwS sz n u xl a * lwG sz n z u a yl ω * lwG sz n z u y'l xl ω)) *
        dhSample sz n u a xl (lwPoly sz n z u P) ω) =
        -(K * (m * ∑ α, lwS sz n u xl α * lwG sz n z u α yl ω * lwG sz n z u y'l xl ω *
          dhSample sz n u α xl (lwPoly sz n z u P) ω)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hA8 : ∑ a, ∑ b, -(K * (m ^ 3 * (Sp xl a * lwS sz n u a b * lwG sz n z u b yl ω *
          lwG sz n z u y'l a ω)) * dhSample sz n u b a (lwPoly sz n z u P) ω) =
        -(K * (m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * lwG sz n z u β yl ω * lwG sz n z u y'l α ω *
          dhSample sz n u β α (lwPoly sz n z u P) ω)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [hA3, hA4, hA5, hA6, hA7, hA8]
    ring
  have key := oe2x_integral hG hz hu hm0 hzm Sp hSp P xl yl y'l
  have hint : ∀ {E' I' : Type} (T : LGraph E' I') (ℓ' : E' ⊕ I' → Idx d (sz.L n) (sz.W n)),
      Integrable (fun ω => T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') (Sizes.seqP sz) :=
    fun T ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have e1 : ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ ∂(Sizes.seqP sz) =
      K * ∫ ω, lwG sz n z u xl yl ω * lwG sz n z u y'l xl ω * lwPoly sz n z u P ω ∂(Sizes.seqP sz) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [hΓ ω]
    ring
  rw [e1, key, ← integral_const_mul]
  simp_rw [hpath]
  set S1 : Sizes.SeqΩ sz → ℂ := fun ω => (oe2xR1d m Γ p x y).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ with hS1
  set S2 : Sizes.SeqΩ sz → ℂ := fun ω => (oe2xR2 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ with hS2
  set S3 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) with hS3
  set S4 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, (oe2xR4 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) with hS4
  set S5 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, (oe2xR5 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) with hS5
  set S6 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, (oe2xR6 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) with hS6
  set S7 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ((lwSplit q.2).map fun q' =>
    (oe2xR7 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum with hS7'
  set S8 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, ((lwSplit q.2).map fun q' =>
    (oe2xR8 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum with hS8'
  have hi1 : Integrable S1 (Sizes.seqP sz) := hint _ _
  have hi2 : Integrable S2 (Sizes.seqP sz) := hint _ _
  have hi3 : Integrable S3 (Sizes.seqP sz) := integrable_finsetSum _ fun α _ => hint _ _
  have hi4 : Integrable S4 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _
  have hi5 : Integrable S5 (Sizes.seqP sz) := integrable_finsetSum _ fun α _ => hint _ _
  have hi6 : Integrable S6 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _
  have hi7 : Integrable S7 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => owx_integrable_list_sum _ _ fun q _ => hint _ _
  have hi8 : Integrable S8 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      owx_integrable_list_sum _ _ fun q _ => hint _ _
  have hi12 : Integrable (fun ω => S1 ω + S2 ω) (Sizes.seqP sz) := hi1.add hi2
  have hi123 : Integrable (fun ω => S1 ω + S2 ω + S3 ω) (Sizes.seqP sz) := hi12.add hi3
  have hi1234 : Integrable (fun ω => S1 ω + S2 ω + S3 ω + S4 ω) (Sizes.seqP sz) := hi123.add hi4
  have hi12345 : Integrable (fun ω => S1 ω + S2 ω + S3 ω + S4 ω + S5 ω) (Sizes.seqP sz) := hi1234.add hi5
  have hi123456 : Integrable (fun ω => S1 ω + S2 ω + S3 ω + S4 ω + S5 ω + S6 ω) (Sizes.seqP sz) := hi12345.add hi6
  have hi1234567 : Integrable (fun ω => S1 ω + S2 ω + S3 ω + S4 ω + S5 ω + S6 ω + S7 ω) (Sizes.seqP sz) :=
    hi123456.add hi7
  change ∫ ω, (S1 ω + S2 ω + S3 ω + S4 ω + S5 ω + S6 ω + S7 ω + S8 ω) ∂(Sizes.seqP sz) = _
  rw [integral_add hi1234567 hi8, integral_add hi123456 hi7, integral_add hi12345 hi6,
    integral_add hi1234 hi5, integral_add hi123 hi4, integral_add hi12 hi3, integral_add hi1 hi2]
  have e3' : ∫ ω, S3 ω ∂(Sizes.seqP sz) = ∑ α, ∫ ω, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
    integral_finsetSum _ fun α _ => hint _ _
  have e4' : ∫ ω, S4 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ∫ ω, (oe2xR4 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
    rw [hS4, integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact integral_finsetSum _ fun β _ => hint _ _
  have e5' : ∫ ω, S5 ω ∂(Sizes.seqP sz) = ∑ α, ∫ ω, (oe2xR5 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
    integral_finsetSum _ fun α _ => hint _ _
  have e6' : ∫ ω, S6 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ∫ ω, (oe2xR6 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
    rw [hS6, integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact integral_finsetSum _ fun β _ => hint _ _
  have e7' : ∫ ω, S7 ω ∂(Sizes.seqP sz) = ∑ α, ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR7 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
      (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
    rw [hS7', integral_finsetSum _ fun α _ => owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact owx_integral_list_sum _ _ _ fun q _ => hint _ _
  have e8' : ∫ ω, S8 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR8 m Γ x y y' q').term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
      (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
    rw [hS8', integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun β _ => owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun β _ => ?_
    exact owx_integral_list_sum _ _ _ fun q _ => hint _ _
  rw [e3', e4', e5', e6', e7', e8']

/-- **`(Oe2x)` as a graph operation: the identity of expectations of values** (`7_8:334-349`, `T eq0`; T2120,
design row LW-07).  For a graph `Γ` with the factors `G_{xy}` (`p.1`, `p ∈ lwSplit Γ.solid`) and `G_{y'x}`
(`q.1`, `q ∈ lwSplit p.2`) at the internal vertex `x`, `y ≠ x`, and `q.2` the other solid edges (`Γ.val = E[G_{xy}
G_{y'x} f]` with the monomial `f`):
`E Γ.val = E R1.val + E R2.val + E R3.val + E R4.val + E R5.val + E R6.val + Σ_{q'} E R7_{q'}.val +
Σ_{q'} E R8_{q'}.val`, with `R1 = oe2xR1`, `R2 = oe2xR2`, `R3 = owxT1`, `R4 = oe2xR4`, `R5 = oe2xR5`,
`R6 = oe2xR6`, `q'` running over `lwSplit q.2` (one graph for each solid edge of `f`) for `R7 = oe2xR7`,
`R8 = oe2xR8`.  The counters of the eight families: `oe2xR1_counters` ... `oe2xR8_ord` (each `ord Γ + 1`).
Data: the resolvent `G = (H_u - z)⁻¹` of the flow of size `n`, deterministic `M` (`M_{aa} = m`), `S = lwS sz n u`,
`S⁺ = Sp` with `S⁺ (1 - m² S) = S`. -/
theorem oe2x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (hy : y ≠ Sum.inr x)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hq1 : q.1 = ⟨true, false, y', Sum.inr x⟩)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (oe2xR1 m Γ p x y hy).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR2 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxT1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR4 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR5 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR6 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR7 m Γ x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
      ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR8 m Γ x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  classical
  have hint : ∀ {E' I' : Type} (T : LGraph E' I') (ℓ' : E' ⊕ I' → Idx d (sz.L n) (sz.W n)),
      Integrable (fun ω => T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') (Sizes.seqP sz) :=
    fun T ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have hL : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) := by
    unfold LGraph.val
    exact integral_finsetSum _ fun ℓi _ => hint _ _
  have hR1 : ∫ ω, (oe2xR1 m Γ p x y hy).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, (oe2xR1d m Γ p x y).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) := by
    simp_rw [oe2xR1_val]
    unfold LGraph.val
    exact integral_finsetSum _ fun ℓi _ => hint _ _
  have hR2 : ∫ ω, (oe2xR2 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, (oe2xR2 m Γ q x y y').term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) := by
    unfold LGraph.val
    exact integral_finsetSum _ fun ℓi _ => hint _ _
  have hR3 := owx_integral_val1 (u := u) hG hz M (lwS sz n u) Sp (owxT1 m Γ x) ℓe
  have hR4 := owx_integral_val2 (u := u) hG hz M (lwS sz n u) Sp (oe2xR4 m Γ q x y y') ℓe
  have hR5 := owx_integral_val1 (u := u) hG hz M (lwS sz n u) Sp (oe2xR5 m Γ q x y y') ℓe
  have hR6 := owx_integral_val2 (u := u) hG hz M (lwS sz n u) Sp (oe2xR6 m Γ q x y y') ℓe
  have hR7 : ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR7 m Γ x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR7 m Γ x y y' q').term
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
    have e : ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR7 m Γ x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
        (lwSplit q.2).map fun q' => ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∫ ω, (oe2xR7 m Γ x y y' q').term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
      List.map_congr_left fun q' _ => owx_integral_val1 hG hz M _ Sp _ ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
  have hR8 : ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR8 m Γ x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR8 m Γ x y y' q').term
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
    have e : ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR8 m Γ x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
        (lwSplit q.2).map fun q' => ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ∫ ω, (oe2xR8 m Γ x y y' q').term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) :=
      List.map_congr_left fun q' _ => owx_integral_val2 hG hz M _ Sp _ ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
  rw [hL, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8]
  simp_rw [oe2x_term_integral hG hz hu hm0 hzm Sp M hSp hM Γ x y y' p hp hp1 q hq hq1 ℓe]
  simp only [Finset.sum_add_distrib]

end Oe2xIdentity


/-! ## 5. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`

(`N = (W L)^d = 27`; `m(0) = i`, `z_{1/2} = i/2`.)  Every deterministic hypothesis is discharged; `gaussIBP` is the
merged proof. -/

end RBM.Graph
