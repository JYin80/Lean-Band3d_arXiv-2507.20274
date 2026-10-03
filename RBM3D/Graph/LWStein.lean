/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWVocab
import RBM3D.Graph.Expansions
import RBM3D.Green.LDEQuad
import RBM3D.Gauss.FineModel
import RBM3D.Gauss.FlowCalculus
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# LW-04: the Stein bridge of the expansions `(Owx)`, `(Oe1x)`, `(Oe2x)` (T2060)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:294-349` (cited `7_8:line`; the paper
cites Lemmas 3.5, 3.10, 3.14 of `[yang2021]` and gives no proof).  Design: T2040 (the probe
`eeda441:RBM3D/Probe/T2040Graphs.lean`, DECISIONS §24); vocabulary: the merged
`Graph/LWVocab.lean` (T2050); the model: the merged `Gauss/FineModel.lean`.

## Contents (namespace `RBM.Graph`)

* **Item 1, section 4 of the probe, copied verbatim** (probe lines 433-697 and `end OwxSmallest`):
  `owxDefect`, `owx_defect_identity` (`(Owx)` is the Stein identity plus linear algebra: pathwise,
  with the Stein defect `Z_w` of the row `w`), `owxG0..2`, `owx_smallest`, `owxH0..4`,
  `owx_second`, `owx_smallest_E`.  The merged `LWVocab` names force no change.  Its instances are
  the section `RBM.Graph.LWInstOwx` at the end (probe lines 2033-2112).
* **Item 2, the derivative** `dhSample` (`∂_{h_{αw}}` on functions of the sample), through the
  real coordinates of the entry `(α, w)` of the model: the Wirtinger derivative that treats
  `h_{αw}` and `h_{wα} = \bar h_{αw}` as independent, the real derivative on the diagonal
  (convention T2060a, numbering D65 = T2040i; the docstring of `dhSample` fixes it).  Closed forms
  `dhSample_lwG : ∂_{h_{αw}} G_{ij} = -G_{iα} G_{wj}` and `dhSample_lwG_star : ∂_{h_{αw}} \bar
  G_{ij} = -\overline{G_{iw} G_{αj}}` for `G = (H_u - z)⁻¹`, `Im z > 0`, `u > 0` (the
  real-direction derivative of the inverse, `lwStein_hasDerivAt_inv`, is proved here from
  `hasFDerivAt_ringInverse`; the merged `hasDerivAt_inverse_apply` is the complex direction
  `E_{αw}` and is matched in `dhSample_lwG_eq_deriv`).
* **Item 3, complex Stein on the model**: the class `Tame1` of `C¹`-tame functions of the sample,
  resolvent polynomials `lwPoly` (T2040d: `MvPolynomial` in `G_{ij}`, `\bar G_{ij}`) and
  `lwPoly_tame1` (bounded by `(Im z)⁻¹` per entry, continuous, finitely dependent, with tame
  derivatives), the Leibniz rule `lwStein_dh_mul`, and `stein_sample` / `stein_lwPoly`:
  `E[(H_u)_{wα} F] = u S_{wα} E[∂_{h_{αw}} F]`, `S = svarF`, for every `w, α` including `w = α`
  (case analysis on the orientation of the entry by `idxKey`, two applications of
  `GaussIBP.stein`, the variances of `CoordF`: `S_{wα}/2` off the diagonal, `S_{ww}` on it).
* **Item 4**: `integral_owxDefect` (`E Z_w = 0` for every resolvent polynomial `f`, `df α w =
  ∂_{h_{αw}} f`, from item 3 and the resolvent identity `Σ_α H_{wα} G_{αw} = 1 + z G_{ww}`) and
  `owx_integral` (`(Owx)` in expectation for every resolvent polynomial: the general form of
  `owx_smallest_E`), with `S⁺ = lwSplus`, `lwS_isUnit`, `lwSplus_spec`, `lwS_row_sum` (the rows of
  `S^{(u)} = u · svarF` sum to `u`).
* **Item 5, the graph derivative**: `LGraph.dTerms` (one derivative graph for each solid edge,
  weights and light-weights included, over `E ⊕ Fin 2`: the two new vertices `α, w` are external),
  `dhSample_graphVal` (`∂_{h_{αw}}` of `LGraph.val` is the sum of the values of `dTerms`), and
  `LGraph.dTerm_counters` (`n_S + 1`, `n_W`, `n_V`, `n_M` unchanged), `LGraph.dTerm_ord` (`ord +
  1`).
* The compiled instances: section `Instances` (items 2-5 at `d = 3`) and `RBM.Graph.LWInstOwx`
  (item 1).

## Hypotheses carried

`GaussIBP sz` (`RBM3D/Green/LDEQuad.lean:302`, registered owed, proved by S1-19) is the only
hypothesis of the probabilistic statements (`stein_sample`, `stein_lwPoly`, `integral_owxDefect`,
`owx_integral`); it is never proved here.  The closed forms, the Leibniz calculus, the graph
derivative and its counters are deterministic.

## Imports beyond the ticket's list

`RBM3D.Gauss.FlowCalculus` (merged: `Gres`, the sample continuity of the resolvent, and through it
the envelope `‖(H - z)⁻¹_{ij}‖ ≤ |Im z|⁻¹` of `RBM3D/Analysis/Resolvent.lean`) and
`Mathlib.LinearAlgebra.Matrix.Gershgorin` (strict diagonal dominance, for `1 - m² S` invertible).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

/-! ## 4. The weight expansion on the vocabulary

`(Owx)` (`7_8:294-306`): `Ǧ_{xx} f(G) =_𝔼 m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f + m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{αα}
Ǧ_{ββ} f - m Σ_α S_{xα} G_{αx} ∂_{h_{αx}} f - m³ Σ_{α,β} S⁺_{xα} S_{αβ} G_{βα} ∂_{h_{βα}} f`.
Pathwise it is an identity with the Stein defect `Z_w` of each row (`owx_defect_identity`);
`E Z_w = 0` is the Stein identity.  Section 4.2 applies it to the smallest graph. -/

section OwxAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- The Stein defect at row `w` of the weight expansion `(Owx)` (`7_8:298`) for `Ǧ_{xx} f(G)`:
`Z_w = (Σ_α H_{wα} G_{αw}) f - Σ_α S_{wα} ∂_{h_{αw}}(G_{αw} f)` with the resolvent identity
`Σ_α H_{wα} G_{αw} = 1 + z G_{ww}` and `∂_{h_{αw}} G_{αw} = -G_{αα} G_{ww}` inserted; `f` and the array
`df α w = ∂_{h_{αw}} f` are data.  `E Z_w = 0` is Gaussian integration by parts (merged `GaussIBP.stein`). -/
def owxDefect (z : ℂ) (G S : Matrix ι ι ℂ) (f : ℂ) (df : ι → ι → ℂ) (w : ι) : ℂ :=
  (1 + z * G w w) * f + (∑ α, S w α * G α α) * G w w * f - ∑ α, S w α * G α w * df α w

/-- **`(Owx)` is the Stein identity plus linear algebra**: for every `f`, `df`, the difference of the two
sides of `(Owx)` is, pathwise and exactly, `-m Σ_w (δ_{xw} + m² S⁺_{xw}) Z_w` (the weight `Ǧ_{αα} = G_{αα} - m`).
Hypotheses: `m ≠ 0`, the rows of `S` sum to `s`, `z + s m = -m⁻¹` and `S⁺ (1 - m² S) = S`.  The flow is
`s = t`, `S = t S^{(B)}`, `z = z_t = E + (1 - t) m` (`z_t + t m = -m⁻¹`); `s = 1` is the static case. -/
theorem owx_defect_identity (z m s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (G S Sp : Matrix ι ι ℂ) (hS : ∀ i, ∑ j, S i j = s)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * S w j = S i j) (f : ℂ) (df : ι → ι → ℂ) (x : ι) :
    (G x x - m) * f -
      (m * ∑ α, S x α * (G x x - m) * (G α α - m) * f +
        m ^ 3 * ∑ α, ∑ β, Sp x α * S α β * (G α α - m) * (G β β - m) * f -
        m * ∑ α, S x α * G α x * df α x -
        m ^ 3 * ∑ α, ∑ β, Sp x α * S α β * G β α * df β α) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) * owxDefect z G S f df w := by
  set u : ι → ℂ := fun i => G i i - m with hu
  -- `(S u)_w`
  set Su : ι → ℂ := fun w => ∑ α, S w α * u α with hSu
  have hrow : ∀ w, ∑ α, S w α * G α α = s * m + Su w := by
    intro w
    have h1 : ∑ α, S w α * G α α = ∑ α, S w α * m + ∑ α, S w α * u α := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [hu]; ring
    rw [h1, ← Finset.sum_mul, hS]
  -- `r w`
  set r : ι → ℂ := fun w => m * u w * Su w * f - m * ∑ α, S w α * G α w * df α w with hr
  have hD : ∀ w, -m * owxDefect z G S f df w = f * u w - m ^ 2 * f * Su w - r w := by
    intro w
    unfold owxDefect
    rw [hrow w]
    have hzm' : z = -m⁻¹ - s * m := by linear_combination hzm
    have hGw : G w w = m + u w := by simp only [hu]; ring
    rw [hzm', hGw]
    simp only [hr]
    field_simp
    ring
  -- `Sp (1 - m² S) = S` on vectors
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
  -- the right side as a sum over `w` of `c_w (f u_w - m² f Su_w - r_w)`
  have hR : -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) * owxDefect z G S f df w =
      ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) * (f * u w - m ^ 2 * f * Su w - r w) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← hD w]; ring
  rw [hR]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have hf1 := hvec (fun w => f * u w)
  have hSf : ∀ w, ∑ α, S w α * (f * u α) = f * Su w := by
    intro w
    simp only [hSu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring
  have hsplit : ∑ w, m ^ 2 * Sp x w * (f * u w - m ^ 2 * f * Su w - r w) =
      m ^ 2 * ∑ w, Sp x w * (f * u w) - m ^ 4 * ∑ w, Sp x w * ∑ α, S w α * (f * u α) -
        m ^ 2 * ∑ w, Sp x w * r w := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, hSf]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [hsplit]
  have hxx : ∑ α, S x α * (G x x - m) * (G α α - m) * f = u x * Su x * f := by
    simp only [hSu, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by simp only [hu]; ring
  have h2 : ∑ α, ∑ β, Sp x α * S α β * (G α α - m) * (G β β - m) * f =
      ∑ α, Sp x α * (u α * Su α * f) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hSu, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by simp only [hu]; ring
  have h3 : ∑ α, ∑ β, Sp x α * S α β * G β α * df β α =
      ∑ α, Sp x α * ∑ β, S α β * G β α * df β α := by
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have hrsum : ∑ w, Sp x w * r w = m * ∑ α, Sp x α * (u α * Su α * f) -
      m * ∑ α, Sp x α * ∑ β, S α β * G β α * df β α := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [hr]
    ring
  have hux : G x x - m = u x := rfl
  rw [hux, hxx, h2, h3]
  have hrx : r x = m * u x * Su x * f - m * ∑ α, S x α * G α x * df α x := rfl
  have hSf' := hSf x
  linear_combination (-1 : ℂ) * hf1 + (-m ^ 2) * hSf' + m ^ 2 * hrsum + hrx

end OwxAlg

section OwxSmallest

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The smallest nontrivial graph: the single light-weight `Ǧ_{xx}` at an external vertex
(`n_S = 1`, `n_W = n_V = 0`, `ord = 1`). -/
def owxG0 : LGraph Unit (Fin 0) where
  solid := [⟨true, true, .inl (), .inl ()⟩]
  waved := []
  dotted := []
  coeff := 1

/-- The first graph of `(Owx)`: `m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα}` (one new internal vertex `α = inr 0`, a
waved edge and a second light-weight; `ord = 2`). -/
def owxG1 (m : ℂ) : LGraph Unit (Fin 1) where
  solid := [⟨true, true, .inl (), .inl ()⟩, ⟨true, true, .inr 0, .inr 0⟩]
  waved := [⟨false, true, .inl (), .inr 0⟩]
  dotted := []
  coeff := m

/-- The second graph of `(Owx)`: `m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{αα} Ǧ_{ββ}` (the original weight is
removed; a blue waved edge `S⁺`, a black waved edge `S`; `ord = 2`). -/
def owxG2 (m : ℂ) : LGraph Unit (Fin 2) where
  solid := [⟨true, true, .inr 0, .inr 0⟩, ⟨true, true, .inr 1, .inr 1⟩]
  waved := [⟨true, true, .inl (), .inr 0⟩, ⟨false, true, .inr 0, .inr 1⟩]
  dotted := []
  coeff := m ^ 3

/-- The counters: `ord` rises from `1` to `2` in both terms (the preflight table, `(a)(i)`). -/
theorem owx_ord (m : ℂ) :
    ord owxG0.counters = 1 ∧ ord (owxG1 m).counters = 2 ∧ ord (owxG2 m).counters = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [LGraph.counters, ord, LGraph.nS, LGraph.nW, LGraph.nV,
    owxG0, owxG1, owxG2]

/-- **`(Owx)` for the smallest graph, on the vocabulary**: with `f = 1` (so `∂f = 0`) the values of
`owxG0`, `owxG1`, `owxG2` satisfy `val G₀ - (val G₁ + val G₂) = -m Σ_w (δ_{xw} + m² S⁺_{xw}) Z_w`
exactly (the Stein defect `Z_w = 1 + z G_{ww} + G_{ww} Σ_α S_{wα} G_{αα}`). -/
theorem owx_smallest (D : LData ι) (m z s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (hM : ∀ i j, D.M i j = if i = j then m else 0) (hS : ∀ i, ∑ j, D.S i j = s)
    (hSp : ∀ i j, D.Sp i j - m ^ 2 * ∑ w, D.Sp i w * D.S w j = D.S i j) (x : ι) :
    owxG0.val D (fun _ => x) - ((owxG1 m).val D (fun _ => x) + (owxG2 m).val D (fun _ => x)) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * D.Sp x w) *
        owxDefect z D.G D.S 1 (fun _ _ => 0) w := by
  have h := owx_defect_identity z m s hm0 hzm D.G D.S D.Sp hS hSp 1 (fun _ _ => 0) x
  unfold LGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero]
  simp [owxG0, owxG1, owxG2, LGraph.term, SEdge.val, WEdge.val, hM]
  simpa [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum] using h

/-- The next graph, with a derivative term: `Ǧ_{xx} G_{xy}` (external `x = inl 0`, `y = inl 1`;
`f = G_{xy}`, `∂_{h_{αw}} G_{xy} = -G_{xα} G_{wy}`). -/
def owxH0 : LGraph (Fin 2) (Fin 0) where
  solid := [⟨true, true, .inl 0, .inl 0⟩, ⟨true, false, .inl 0, .inl 1⟩]
  waved := []
  dotted := []
  coeff := 1

/-- The four graphs of `(Owx)` for `owxH0`: the first two keep `f`, the last two carry the derivative:
`G_{xy} ↦ -G_{xα} G_{wy}` replaces the edge by two edges (`w = x` in the third, `w = α` in the
fourth); `ord` of each is `ord(owxH0) + 1`. -/
def owxH1 (m : ℂ) : LGraph (Fin 2) (Fin 1) where
  solid := [⟨true, true, .inl 0, .inl 0⟩, ⟨true, false, .inl 0, .inl 1⟩, ⟨true, true, .inr 0, .inr 0⟩]
  waved := [⟨false, true, .inl 0, .inr 0⟩]
  dotted := []
  coeff := m

def owxH2 (m : ℂ) : LGraph (Fin 2) (Fin 2) where
  solid := [⟨true, false, .inl 0, .inl 1⟩, ⟨true, true, .inr 0, .inr 0⟩, ⟨true, true, .inr 1, .inr 1⟩]
  waved := [⟨true, true, .inl 0, .inr 0⟩, ⟨false, true, .inr 0, .inr 1⟩]
  dotted := []
  coeff := m ^ 3

def owxH3 (m : ℂ) : LGraph (Fin 2) (Fin 1) where
  solid := [⟨true, false, .inr 0, .inl 0⟩, ⟨true, false, .inl 0, .inr 0⟩, ⟨true, false, .inl 0, .inl 1⟩]
  waved := [⟨false, true, .inl 0, .inr 0⟩]
  dotted := []
  coeff := m

def owxH4 (m : ℂ) : LGraph (Fin 2) (Fin 2) where
  solid := [⟨true, false, .inr 1, .inr 0⟩, ⟨true, false, .inl 0, .inr 1⟩, ⟨true, false, .inr 0, .inl 1⟩]
  waved := [⟨true, true, .inl 0, .inr 0⟩, ⟨false, true, .inr 0, .inr 1⟩]
  dotted := []
  coeff := m ^ 3

theorem owx_ord_H (m : ℂ) :
    ord owxH0.counters = 2 ∧ ord (owxH1 m).counters = 3 ∧ ord (owxH2 m).counters = 3 ∧
      ord (owxH3 m).counters = 3 ∧ ord (owxH4 m).counters = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [LGraph.counters, ord, LGraph.nS, LGraph.nW, LGraph.nV,
    owxH0, owxH1, owxH2, owxH3, owxH4]

/-- **`(Owx)` for `Ǧ_{xx} G_{xy}`**, all four terms, on the vocabulary: the pathwise identity with the
Stein defect of `f = G_{xy}`, `∂_{h_{αw}} f = -G_{xα} G_{wy}`. -/
theorem owx_second (D : LData ι) (m z s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (hM : ∀ i j, D.M i j = if i = j then m else 0) (hS : ∀ i, ∑ j, D.S i j = s)
    (hSp : ∀ i j, D.Sp i j - m ^ 2 * ∑ w, D.Sp i w * D.S w j = D.S i j) (x y : ι) :
    owxH0.val D ![x, y] - ((owxH1 m).val D ![x, y] + (owxH2 m).val D ![x, y] +
        (owxH3 m).val D ![x, y] + (owxH4 m).val D ![x, y]) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * D.Sp x w) *
        owxDefect z D.G D.S (D.G x y) (fun α w => -(D.G x α * D.G w y)) w := by
  have h := owx_defect_identity z m s hm0 hzm D.G D.S D.Sp hS hSp (D.G x y)
    (fun α w => -(D.G x α * D.G w y)) x
  unfold LGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero]
  simp [owxH0, owxH1, owxH2, owxH3, owxH4, LGraph.term, SEdge.val, WEdge.val, hM]
  have e1 : ∑ a, m * ((D.G x x - m) * (D.G x y * (D.G a a - m))) * D.S x a =
      m * ∑ α, D.S x α * (D.G x x - m) * (D.G α α - m) * D.G x y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ a, ∑ b, m ^ 3 * (D.G x y * ((D.G a a - m) * (D.G b b - m))) * (D.Sp x a * D.S a b) =
      m ^ 3 * ∑ α, ∑ β, D.Sp x α * D.S α β * (D.G α α - m) * (D.G β β - m) * D.G x y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ a, m * (D.G a x * (D.G x a * D.G x y)) * D.S x a =
      -(m * ∑ α, D.S x α * D.G α x * -(D.G x α * D.G x y)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e4 : ∑ a, ∑ b, m ^ 3 * (D.G b a * (D.G x b * D.G a y)) * (D.Sp x a * D.S a b) =
      -(m ^ 3 * ∑ α, ∑ β, D.Sp x α * D.S α β * D.G β α * -(D.G x β * D.G α y)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3, e4]
  linear_combination h

/-- **`(Owx)` in expectation for the smallest graph.**  If the Stein defect of every row is
integrable with mean zero (Gaussian integration by parts: merged `GaussIBP.stein` for the tame
functions `ω ↦ Σ_α H_{wα} G_{αw}`; the data of the model has the deterministic `S`, `S⁺`), and the
three values are integrable, then `E val G₀ = E val G₁ + E val G₂`: the identity of values. -/
theorem owx_smallest_E {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Dω : Ω → LData ι) (m z s : ℂ)
    (Sp₀ : Matrix ι ι ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (hM : ∀ ω i j, (Dω ω).M i j = if i = j then m else 0) (hS : ∀ ω i, ∑ j, (Dω ω).S i j = s)
    (hSp : ∀ ω i j, (Dω ω).Sp i j - m ^ 2 * ∑ w, (Dω ω).Sp i w * (Dω ω).S w j = (Dω ω).S i j)
    (hSp0 : ∀ ω, (Dω ω).Sp = Sp₀) (x : ι)
    (hZint : ∀ w, Integrable (fun ω => owxDefect z (Dω ω).G (Dω ω).S 1 (fun _ _ => 0) w) P)
    (hZ : ∀ w, ∫ ω, owxDefect z (Dω ω).G (Dω ω).S 1 (fun _ _ => 0) w ∂P = 0)
    (h0 : Integrable (fun ω => owxG0.val (Dω ω) (fun _ => x)) P)
    (h1 : Integrable (fun ω => (owxG1 m).val (Dω ω) (fun _ => x)) P)
    (h2 : Integrable (fun ω => (owxG2 m).val (Dω ω) (fun _ => x)) P) :
    ∫ ω, owxG0.val (Dω ω) (fun _ => x) ∂P =
      ∫ ω, (owxG1 m).val (Dω ω) (fun _ => x) ∂P + ∫ ω, (owxG2 m).val (Dω ω) (fun _ => x) ∂P := by
  have hpt := fun ω => owx_smallest (Dω ω) m z s hm0 hzm (hM ω) (hS ω) (hSp ω) x
  have hs : Integrable (fun ω => (owxG1 m).val (Dω ω) (fun _ => x) +
      (owxG2 m).val (Dω ω) (fun _ => x)) P := h1.add h2
  have hint : ∫ ω, (owxG0.val (Dω ω) (fun _ => x) - ((owxG1 m).val (Dω ω) (fun _ => x) +
      (owxG2 m).val (Dω ω) (fun _ => x))) ∂P = 0 := by
    simp_rw [hpt, hSp0]
    rw [integral_const_mul, integral_finsetSum _ (fun w _ => (hZint w).const_mul _)]
    simp [integral_const_mul, hZ]
  rw [integral_sub h0 hs, integral_add h1 h2] at hint
  linear_combination hint
end OwxSmallest

open RBM RBM.Gauss RBM.Green

section CoordMat
variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The matrix direction of the real part of the entry `(a, b)`, `key a < key b`: `E_{ab} + E_{ba}`. -/
theorem lwStein_coordMat_true_lt (a b : Idx d L W) (h : idxKey d L W a < idxKey d L W b) :
    coordinateMatrix d L W (a, b, true) = single a b (1 : ℂ) + single b a (1 : ℂ) := by
  ext i j
  have hab : a ≠ b := fun e => absurd (e ▸ h) (lt_irrefl _)
  simp only [coordinateMatrix, Xmat, Xentry, Matrix.of_apply, Matrix.add_apply, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  rcases idxKey_lt_or_eq_or_lt d L W i j with hij | rfl | hij
  · have h2 : ¬ idxKey d L W j < idxKey d L W i := not_lt.mpr hij.le
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hij, hab]
    · by_cases h3 : b = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := h3; omega
      · simp [hij, h1, h3, eq_comm]
  · have e1 : ¬ (i = a ∧ i = b) := fun ⟨h1, h2⟩ => hab (h1.symm.trans h2)
    have e2 : ¬ (a = i ∧ b = i) := fun ⟨h1, h2⟩ => hab (h1.trans h2.symm)
    have e3 : ¬ (b = i ∧ a = i) := fun ⟨h1, h2⟩ => hab (h2.trans h1.symm)
    simp [e1, e2, e3]
  · have h2 : ¬ idxKey d L W i < idxKey d L W j := not_lt.mpr hij.le
    by_cases h3 : b = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h3
      simp [hij, hab, h2, eq_comm]
    · by_cases h1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h1; omega
      · have h3' : ¬ (a = j ∧ b = i) := fun ⟨x, y⟩ => h3 ⟨y, x⟩
        simp [hij, h2, h1, h3]
        intro ha hb
        exact h3' ⟨ha.symm, hb.symm⟩

/-- The matrix direction of the imaginary part of the entry `(a, b)`, `key a < key b`: `i E_{ab} - i E_{ba}`. -/
theorem lwStein_coordMat_false_lt (a b : Idx d L W) (h : idxKey d L W a < idxKey d L W b) :
    coordinateMatrix d L W (a, b, false) = single a b Complex.I + single b a (-Complex.I) := by
  ext i j
  have hab : a ≠ b := fun e => absurd (e ▸ h) (lt_irrefl _)
  simp only [coordinateMatrix, Xmat, Xentry, Matrix.of_apply, Matrix.add_apply, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  rcases idxKey_lt_or_eq_or_lt d L W i j with hij | rfl | hij
  · have h2 : ¬ idxKey d L W j < idxKey d L W i := not_lt.mpr hij.le
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hij, hab]
    · by_cases h3 : b = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := h3; omega
      · simp [hij, h1, h3, eq_comm]
  · have e2 : ¬ (a = i ∧ b = i) := fun ⟨h1, h2⟩ => hab (h1.trans h2.symm)
    have e3 : ¬ (b = i ∧ a = i) := fun ⟨h1, h2⟩ => hab (h2.trans h1.symm)
    simp [e2, e3]
  · have h2 : ¬ idxKey d L W i < idxKey d L W j := not_lt.mpr hij.le
    by_cases h3 : b = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h3
      simp [hij, hab, h2, eq_comm]
    · by_cases h1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h1; omega
      · have h3' : ¬ (a = j ∧ b = i) := fun ⟨x, y⟩ => h3 ⟨y, x⟩
        simp [hij, h2, h1, h3]
        intro ha hb
        exact h3' ⟨ha.symm, hb.symm⟩

/-- The matrix direction of the diagonal coordinate `(a, a, true)`: `E_{aa}`. -/
theorem lwStein_coordMat_diag (a : Idx d L W) :
    coordinateMatrix d L W (a, a, true) = single a a (1 : ℂ) := by
  ext i j
  simp only [coordinateMatrix, Xmat, Xentry, Matrix.of_apply, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  rcases idxKey_lt_or_eq_or_lt d L W i j with hij | rfl | hij
  · have h2 : ¬ idxKey d L W j < idxKey d L W i := not_lt.mpr hij.le
    by_cases h1 : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h1; omega
    · have h1' : ¬ (i = a ∧ j = a) := fun ⟨x, y⟩ => h1 ⟨x.symm, y.symm⟩
      simp [hij, h1, h1']
  · by_cases h : a = i
    · subst h; simp
    · simp [h, Ne.symm h]
  · have h2 : ¬ idxKey d L W i < idxKey d L W j := not_lt.mpr hij.le
    by_cases h1 : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h1; omega
    · have h1' : ¬ (j = a ∧ i = a) := fun ⟨x, y⟩ => h1 ⟨y.symm, x.symm⟩
      simp [hij, h2, h1, h1']
end CoordMat

section RealDeriv
open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative of the entries of the inverse along a real line: `d/dt (A + (t - t₀) B)⁻¹ |_{t=t₀} =
-A⁻¹ B A⁻¹`. -/
theorem lwStein_hasDerivAt_inv {A B : Matrix ι ι ℂ} (hA : IsUnit A) (t₀ : ℝ) (i j : ι) :
    HasDerivAt (fun t : ℝ => Ring.inverse (A + (t - t₀) • B) i j)
      (-(Ring.inverse A * B * Ring.inverse A) i j) t₀ := by
  obtain ⟨u, rfl⟩ := hA
  have hpath : HasDerivAt (fun t : ℝ => (u : Matrix ι ι ℂ) + (t - t₀) • B) B t₀ := by
    have h := (((hasDerivAt_id t₀).sub_const t₀).smul_const B).const_add (u : Matrix ι ι ℂ)
    simp only [id, one_smul] at h
    exact h
  set D := -ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ) ↑u⁻¹ ↑u⁻¹ with hD
  have hinv : HasFDerivAt Ring.inverse D ((u : Matrix ι ι ℂ) + (t₀ - t₀) • B) := by
    rw [sub_self, zero_smul, add_zero]
    exact hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hcomp := hinv.comp_hasDerivAt t₀ hpath
  let ent : Matrix ι ι ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (entryLinearMap ℝ ℂ i j)
  have hent := ent.hasFDerivAt.comp_hasDerivAt t₀ hcomp
  have hval : ent (D B) = -(Ring.inverse (u : Matrix ι ι ℂ) * B * Ring.inverse (u : Matrix ι ι ℂ)) i j := by
    simp only [D, Ring.inverse_unit]
    simp [ent]
  exact hent.congr_deriv hval

end RealDeriv

section Sample

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- The resolvent matrix `G = (H_u - z)⁻¹` of the flow `H_u = √u X` at size `n`, as a function of the
sample (the merged `Gres`). -/
def lwGm (z : ℂ) (u : ℝ) (ω : Sizes.SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres (sz.seqHflow n u ω) z true

/-- The entry `G_{ij}` of the resolvent of the flow. -/
def lwG (z : ℂ) (u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) : ℂ :=
  lwGm sz n z u ω i j

/-- Moving one real coordinate `c` of the sample moves `H_u = √u X` by `(t - ω c) √u D_c`. -/
theorem lwStein_seqHflow_update (u : ℝ) (ω : Sizes.SeqΩ sz) (c : CoordF d (sz.L n) (sz.W n)) (t : ℝ) :
    sz.seqHflow n u (Function.update ω ⟨n, c⟩ t) = sz.seqHflow n u ω +
      (t - ω ⟨n, c⟩) • ((Real.sqrt u : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c) := by
  unfold Sizes.seqHflow
  rw [Sizes.seqXmat_update, smul_add, smul_comm (Real.sqrt u : ℂ) (t - ω ⟨n, c⟩)]

/-- **The derivative of `G_{ij}` along one real coordinate** of the sample: moving the coordinate `c`
moves `H_u` by `√u · D_c` (`Xmat_update`, `D_c = coordinateMatrix c`), so
`∂_c G_{ij} = -√u (G D_c G)_{ij}`. -/
theorem lwStein_hasDerivAt_lwG {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (c : CoordF d (sz.L n) (sz.W n)) (i j : Idx d (sz.L n) (sz.W n)) :
    HasDerivAt (fun t : ℝ => lwG sz n z u i j (Function.update ω ⟨n, c⟩ t))
      (-((Real.sqrt u : ℂ) * (lwGm sz n z u ω * coordinateMatrix d (sz.L n) (sz.W n) c *
        lwGm sz n z u ω) i j)) (ω ⟨n, c⟩) := by
  have hU : IsUnit (sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    isUnit_sub_smul_of_isHermitian (Sizes.seqHflow_isHermitian sz n u ω) hz
  have h := lwStein_hasDerivAt_inv hU (ω ⟨n, c⟩) i j
    (B := (Real.sqrt u : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c)
  have hfun : (fun t : ℝ => lwG sz n z u i j (Function.update ω ⟨n, c⟩ t)) = fun t : ℝ =>
      Ring.inverse ((sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) +
        (t - ω ⟨n, c⟩) • ((Real.sqrt u : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c)) i j := by
    funext t
    simp only [lwG, lwGm, Gres, ite_true, lwStein_seqHflow_update]
    rw [add_sub_right_comm]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [lwGm, Gres, ite_true, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]


/-- The real partial derivative `∂/∂ω_c` at size `n` of a function of the sample: the derivative at
`ω c` of `t ↦ F (ω with the coordinate `c` replaced by `t`)`. -/
def lwPartial (c : CoordF d (sz.L n) (sz.W n)) (F : Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz) : ℂ :=
  deriv (fun t : ℝ => F (Function.update ω ⟨n, c⟩ t)) (ω ⟨n, c⟩)

/-- **`∂_{h_{αw}}` on functions of the sample** (T2040i, T2060a): `h_{αw} = (H_u)_{αw} = √u X_{αw}`,
where the entry `X_{αw}` of the model (`Xentry`) is oriented by `idxKey`, and `h_{αw}`, `h_{wα} =
\bar h_{αw}` are treated as independent (Wirtinger).  In the real coordinates `a = ω(·,·,true)`,
`b = ω(·,·,false)` of the entry:
* `key α < key w`: `X_{αw} = a + i b`, `∂_{h_{αw}} = (2√u)⁻¹ (∂_a - i ∂_b)` on `(α, w, ·)`;
* `key w < key α`: `X_{αw} = a - i b`, `∂_{h_{αw}} = (2√u)⁻¹ (∂_a + i ∂_b)` on `(w, α, ·)`;
* `α = w`: `X_{αα} = a` real, `∂_{h_{αα}} = u^{-1/2} ∂_a` on `(α, α, true)` (the real derivative).
So `∂_{h_{αw}} h_{αw} = 1`, `∂_{h_{αw}} h_{wα} = 0`.  It is `0` at `u = 0` (Lean's `0⁻¹ = 0`); every theorem
below that needs the closed forms takes `0 < u`. -/
def dhSample (u : ℝ) (α w : Idx d (sz.L n) (sz.W n)) (F : Sizes.SeqΩ sz → ℂ)
    (ω : Sizes.SeqΩ sz) : ℂ :=
  if idxKey d (sz.L n) (sz.W n) α < idxKey d (sz.L n) (sz.W n) w then
    (2 * (Real.sqrt u : ℂ))⁻¹ *
      (lwPartial sz n (α, w, true) F ω - Complex.I * lwPartial sz n (α, w, false) F ω)
  else if idxKey d (sz.L n) (sz.W n) w < idxKey d (sz.L n) (sz.W n) α then
    (2 * (Real.sqrt u : ℂ))⁻¹ *
      (lwPartial sz n (w, α, true) F ω + Complex.I * lwPartial sz n (w, α, false) F ω)
  else (Real.sqrt u : ℂ)⁻¹ * lwPartial sz n (α, α, true) F ω

/-- `lwPartial` of `G_{ij}` along `c`: `-√u (G D_c G)_{ij}`. -/
theorem lwStein_partial_lwG {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (c : CoordF d (sz.L n) (sz.W n)) (i j : Idx d (sz.L n) (sz.W n)) :
    lwPartial sz n c (lwG sz n z u i j) ω =
      -((Real.sqrt u : ℂ) * (lwGm sz n z u ω * coordinateMatrix d (sz.L n) (sz.W n) c *
        lwGm sz n z u ω) i j) :=
  (lwStein_hasDerivAt_lwG sz n hz u ω c i j).deriv

/-- `(P (c E_{ab}) Q)_{ij} = c P_{ia} Q_{bj}`. -/
theorem lwStein_mul_single_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℂ)
    (a b : ι) (c : ℂ) (i j : ι) : (P * single a b c * Q) i j = c * (P i a * Q b j) := by
  have : single a b c = c • single a b (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [mul_single_mul_apply]


/-- `√u ≠ 0` for `u > 0`, as a complex number. -/
theorem lwStein_sqrt_ne {u : ℝ} (hu : 0 < u) : (Real.sqrt u : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 hu).ne'

/-- The real partial derivative commutes with complex conjugation. -/
theorem lwStein_partial_star (c : CoordF d (sz.L n) (sz.W n)) (F : Sizes.SeqΩ sz → ℂ)
    (ω : Sizes.SeqΩ sz) :
    lwPartial sz n c (fun ω => star (F ω)) ω = star (lwPartial sz n c F ω) := by
  unfold lwPartial
  exact deriv.star

/-- **`∂_{h_{αw}} G_{ij} = -G_{iα} G_{wj}`** (`(Owx)`, `7_8:298`; T2060a convention of `dhSample`):
for `0 < u` and `Im z > 0`, the resolvent `G = (H_u - z)⁻¹` of the flow `H_u = √u X`. -/
theorem dhSample_lwG {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) (α w i j : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (lwG sz n z u i j) ω = -(lwG sz n z u i α ω * lwG sz n z u w j ω) := by
  have hz' : z.im ≠ 0 := hz.ne'
  have hs := lwStein_sqrt_ne hu
  have h2s : (2 * (Real.sqrt u : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hs
  unfold dhSample
  rcases idxKey_lt_or_eq_or_lt d (sz.L n) (sz.W n) α w with h | rfl | h
  · rw [ite_eq_left h, lwStein_partial_lwG sz n hz', lwStein_partial_lwG sz n hz',
      lwStein_coordMat_true_lt _ _ _ _ _ h, lwStein_coordMat_false_lt _ _ _ _ _ h]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, lwStein_mul_single_mul_apply]
    simp only [lwG]
    rw [inv_mul_eq_iff_eq_mul₀ h2s]
    linear_combination ((Real.sqrt u : ℂ) * (lwGm sz n z u ω i α * lwGm sz n z u ω w j
      - lwGm sz n z u ω i w * lwGm sz n z u ω α j)) * Complex.I_sq
  · rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), lwStein_partial_lwG sz n hz',
      lwStein_coordMat_diag]
    simp only [lwStein_mul_single_mul_apply, lwG]
    field_simp
  · rw [ite_eq_right h.not_gt, ite_eq_left h, lwStein_partial_lwG sz n hz', lwStein_partial_lwG sz n hz',
      lwStein_coordMat_true_lt _ _ _ _ _ h, lwStein_coordMat_false_lt _ _ _ _ _ h]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, lwStein_mul_single_mul_apply]
    simp only [lwG]
    rw [inv_mul_eq_iff_eq_mul₀ h2s]
    linear_combination ((Real.sqrt u : ℂ) * (lwGm sz n z u ω i α * lwGm sz n z u ω w j
      - lwGm sz n z u ω i w * lwGm sz n z u ω α j)) * Complex.I_sq


/-- **`∂_{h_{αw}} \bar G_{ij} = -\overline{G_{iw} G_{αj}}`** (the conjugate rule: the derivative in the
independent variable `h_{αw}` of `\bar G = conj G` is the conjugate of the derivative of `G` in `h_{wα}`). -/
theorem dhSample_lwG_star {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u)
    (α w i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => star (lwG sz n z u i j ω)) ω =
      -star (lwG sz n z u i w ω * lwG sz n z u α j ω) := by
  have hz' : z.im ≠ 0 := hz.ne'
  have hs := lwStein_sqrt_ne hu
  have h2s : (2 * (Real.sqrt u : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hs
  unfold dhSample
  simp only [lwStein_partial_star]
  rcases idxKey_lt_or_eq_or_lt d (sz.L n) (sz.W n) α w with h | rfl | h
  · rw [ite_eq_left h, lwStein_partial_lwG sz n hz', lwStein_partial_lwG sz n hz',
      lwStein_coordMat_true_lt _ _ _ _ _ h, lwStein_coordMat_false_lt _ _ _ _ _ h]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, lwStein_mul_single_mul_apply]
    simp only [lwG, star_neg, star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      one_mul]
    rw [inv_mul_eq_iff_eq_mul₀ h2s]
    linear_combination ((Real.sqrt u : ℂ) * ((starRingEnd ℂ) (lwGm sz n z u ω i w) * (starRingEnd ℂ) (lwGm sz n z u ω α j)
      - (starRingEnd ℂ) (lwGm sz n z u ω i α) * (starRingEnd ℂ) (lwGm sz n z u ω w j))) * Complex.I_sq
  · rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), lwStein_partial_lwG sz n hz',
      lwStein_coordMat_diag]
    simp only [lwStein_mul_single_mul_apply, lwG, star_neg, star_mul', Complex.star_def,
      Complex.conj_ofReal, one_mul]
    field_simp
  · rw [ite_eq_right h.not_gt, ite_eq_left h, lwStein_partial_lwG sz n hz', lwStein_partial_lwG sz n hz',
      lwStein_coordMat_true_lt _ _ _ _ _ h, lwStein_coordMat_false_lt _ _ _ _ _ h]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, lwStein_mul_single_mul_apply]
    simp only [lwG, star_neg, star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      one_mul]
    rw [inv_mul_eq_iff_eq_mul₀ h2s]
    linear_combination ((Real.sqrt u : ℂ) * ((starRingEnd ℂ) (lwGm sz n z u ω i w) * (starRingEnd ℂ) (lwGm sz n z u ω α j)
      - (starRingEnd ℂ) (lwGm sz n z u ω i α) * (starRingEnd ℂ) (lwGm sz n z u ω w j))) * Complex.I_sq


/-- **The convention of `dhSample` is the complex derivative along the matrix unit `E_{αw}`** (T2040i, the
probe's `dH`): for `G_{ij}`, `∂_{h_{αw}} G_{ij} = d/ds ((H_u - z) + s E_{αw})⁻¹_{ij} |_{s = 0}`, the merged
`hasDerivAt_inverse_apply` (`Graph/Expansions.lean:63`), with `h_{wα}` held fixed. -/
theorem dhSample_lwG_eq_deriv {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u)
    (α w i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (lwG sz n z u i j) ω =
      deriv (fun s : ℂ => Ring.inverse ((sz.seqHflow n u ω -
        z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) +
          s • single α w (1 : ℂ)) i j) 0 := by
  have hU : IsUnit (sz.seqHflow n u ω -
      z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    isUnit_sub_smul_of_isHermitian (Sizes.seqHflow_isHermitian sz n u ω) hz.ne'
  rw [dhSample_lwG sz n hz hu, (hasDerivAt_inverse_apply hU α w i j).deriv]
  rfl

/-! ### Tameness of the resolvent entries -/

open Classical in
theorem lwStein_finDep_of_slice {V : Type*} (F : Sizes.SeqΩ sz → V)
    (h : ∀ ω ω' : Sizes.SeqΩ sz, Sizes.slice sz n ω = Sizes.slice sz n ω' → F ω = F ω') :
    FinDep sz F :=
  ⟨Finset.univ.image (fun c : CoordF d (sz.L n) (sz.W n) => (⟨n, c⟩ : Sizes.SeqCoord sz)),
    fun ω ω' hh => h ω ω' (funext fun c =>
      hh ⟨n, c⟩ (Finset.mem_image_of_mem _ (Finset.mem_univ c)))⟩

/-- The size projection of the common sample space is continuous. -/
theorem lwStein_continuous_slice : Continuous (Sizes.slice sz n) :=
  continuous_pi fun c => continuous_apply (⟨n, c⟩ : Sizes.SeqCoord sz)

/-- The flow `H_u` is a continuous function of the sample. -/
theorem lwStein_continuous_seqHflow (u : ℝ) : Continuous (sz.seqHflow n u) := by
  have h : sz.seqHflow n u = fun ω => (Real.sqrt u : ℂ) • Xmat d (sz.L n) (sz.W n) (Sizes.slice sz n ω) :=
    rfl
  rw [h]
  exact ((continuous_Xmat d (sz.L n) (sz.W n)).comp (lwStein_continuous_slice sz n)).const_smul (Real.sqrt u : ℂ)

/-- The resolvent of the flow is a continuous function of the sample (`Im z ≠ 0`). -/
theorem lwStein_continuous_lwGm {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) : Continuous (lwGm sz n z u) :=
  continuous_green_of_isHermitian (lwStein_continuous_seqHflow sz n u)
    (fun ω => Sizes.seqHflow_isHermitian sz n u ω) hz

/-- The entries of the resolvent obey the envelope `|G_{ij}| ≤ |Im z|⁻¹` at every sample. -/
theorem lwStein_norm_lwG_le {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) (i j : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) : ‖lwG sz n z u i j ω‖ ≤ |z.im|⁻¹ := by
  simpa [lwG, lwGm, Gres] using
    norm_inverse_entry_le (Sizes.seqHflow_isHermitian sz n u ω) hz i j

/-- A resolvent entry is tame: continuous, finitely dependent, bounded by `|Im z|⁻¹`. -/
theorem lwStein_tame_lwG {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) :
    Tame sz (lwG sz n z u i j) :=
  Tame.ofBdd (((continuous_apply j).comp ((continuous_apply i).comp (lwStein_continuous_lwGm sz n hz u))))
    (lwStein_finDep_of_slice sz n _ fun ω ω' h => by
      have : sz.seqHflow n u ω = sz.seqHflow n u ω' := by
        unfold Sizes.seqHflow Sizes.seqXmat; rw [h]
      simp only [lwG, lwGm, this])
    (lwStein_norm_lwG_le sz n hz u i j)

/-- An entry of `H_u` is tame (a polynomial of degree one in at most two coordinates). -/
theorem lwStein_tame_hflow (u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => sz.seqHflow n u ω i j) := by
  have h : (fun ω : Sizes.SeqΩ sz => sz.seqHflow n u ω i j) = fun ω =>
      (Real.sqrt u : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) i j := rfl
  rw [h]
  refine Tame.mul (Tame.const _) ?_
  unfold Xentry
  split_ifs
  · exact (Tame.coord (⟨n, (i, j, true)⟩ : Sizes.SeqCoord sz)).add
      ((Tame.const Complex.I).mul (Tame.coord (⟨n, (i, j, false)⟩ : Sizes.SeqCoord sz)))
  · exact (Tame.coord (⟨n, (j, i, true)⟩ : Sizes.SeqCoord sz)).sub
      ((Tame.const Complex.I).mul (Tame.coord (⟨n, (j, i, false)⟩ : Sizes.SeqCoord sz)))
  · exact Tame.coord (⟨n, (i, j, true)⟩ : Sizes.SeqCoord sz)


/-! ### `C¹`-tame functions and the calculus of `∂_{h_{αw}}` -/

/-- **`F` is `C¹`-tame at size `n`**: tame (continuous, finitely dependent, polynomially bounded), differentiable
along every real coordinate of size `n` (at every sample), with tame partial derivatives.  This is the
class on which the Stein identity of `GaussIBP` applies to `F` and to its derivatives (the first
condition is `RBM.Green.Tame`, `Green/LDEQuad.lean:165`). -/
structure Tame1 (sz : Sizes d) (n : ℕ) (F : Sizes.SeqΩ sz → ℂ) : Prop where
  /-- `F` is tame. -/
  tame : Tame sz F
  /-- `F` is differentiable along each real coordinate of size `n`. -/
  diff : ∀ (c : CoordF d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
    DifferentiableAt ℝ (fun t : ℝ => F (Function.update ω ⟨n, c⟩ t)) (ω ⟨n, c⟩)
  /-- The partial derivatives along the coordinates of size `n` are tame. -/
  tame_partial : ∀ c : CoordF d (sz.L n) (sz.W n), Tame sz (lwPartial sz n c F)

variable {sz n}

theorem lwStein_partial_add {F G : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) (hG : Tame1 sz n G)
    (c : CoordF d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    lwPartial sz n c (fun ω => F ω + G ω) ω = lwPartial sz n c F ω + lwPartial sz n c G ω :=
  deriv_add (hF.diff c ω) (hG.diff c ω)

/-- `lwPartial` of a difference. -/
theorem lwStein_partial_sub {F G : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) (hG : Tame1 sz n G)
    (c : CoordF d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    lwPartial sz n c (fun ω => F ω - G ω) ω = lwPartial sz n c F ω - lwPartial sz n c G ω :=
  deriv_sub (hF.diff c ω) (hG.diff c ω)

/-- `lwPartial` of a product (Leibniz). -/
theorem lwStein_partial_mul {F G : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) (hG : Tame1 sz n G)
    (c : CoordF d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    lwPartial sz n c (fun ω => F ω * G ω) ω =
      lwPartial sz n c F ω * G ω + F ω * lwPartial sz n c G ω := by
  have h := deriv_mul (hF.diff c ω) (hG.diff c ω)
  simp only [Function.update_eq_self] at h
  exact h

/-- `lwPartial` of a constant is `0`. -/
theorem lwStein_partial_const (a : ℂ) (c : CoordF d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    lwPartial sz n c (fun _ => a) ω = 0 := by
  simp [lwPartial]

/-- A constant is `C¹`-tame. -/
theorem Tame1.const (a : ℂ) : Tame1 sz n (fun _ => a) where
  tame := Tame.const a
  diff := fun _ _ => differentiableAt_const _
  tame_partial := fun c => by
    have : lwPartial sz n c (fun _ => a) = fun _ => 0 := funext (lwStein_partial_const a c)
    rw [this]
    exact Tame.const 0

/-- `C¹`-tame functions are closed under sums. -/
theorem Tame1.add {F G : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) (hG : Tame1 sz n G) :
    Tame1 sz n (fun ω => F ω + G ω) where
  tame := hF.tame.add hG.tame
  diff := fun c ω => (hF.diff c ω).add (hG.diff c ω)
  tame_partial := fun c => by
    have : lwPartial sz n c (fun ω => F ω + G ω) =
        fun ω => lwPartial sz n c F ω + lwPartial sz n c G ω :=
      funext (lwStein_partial_add hF hG c)
    rw [this]
    exact (hF.tame_partial c).add (hG.tame_partial c)

/-- `C¹`-tame functions are closed under differences. -/
theorem Tame1.sub {F G : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) (hG : Tame1 sz n G) :
    Tame1 sz n (fun ω => F ω - G ω) where
  tame := hF.tame.sub hG.tame
  diff := fun c ω => (hF.diff c ω).sub (hG.diff c ω)
  tame_partial := fun c => by
    have : lwPartial sz n c (fun ω => F ω - G ω) =
        fun ω => lwPartial sz n c F ω - lwPartial sz n c G ω :=
      funext (lwStein_partial_sub hF hG c)
    rw [this]
    exact (hF.tame_partial c).sub (hG.tame_partial c)

/-- `C¹`-tame functions are closed under products. -/
theorem Tame1.mul {F G : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) (hG : Tame1 sz n G) :
    Tame1 sz n (fun ω => F ω * G ω) where
  tame := hF.tame.mul hG.tame
  diff := fun c ω => (hF.diff c ω).mul (hG.diff c ω)
  tame_partial := fun c => by
    have : lwPartial sz n c (fun ω => F ω * G ω) =
        fun ω => lwPartial sz n c F ω * G ω + F ω * lwPartial sz n c G ω :=
      funext (lwStein_partial_mul hF hG c)
    rw [this]
    exact ((hF.tame_partial c).mul hG.tame).add (hF.tame.mul (hG.tame_partial c))

/-- `C¹`-tame functions are closed under negation. -/
theorem Tame1.neg {F : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) : Tame1 sz n (fun ω => -F ω) := by
  have h := (Tame1.const (sz := sz) (n := n) 0).sub hF
  simpa using h

/-- `C¹`-tame functions are closed under complex conjugation (`star`). -/
theorem Tame1.conj {F : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) :
    Tame1 sz n (fun ω => star (F ω)) where
  tame := by simpa [Complex.star_def] using hF.tame.conj
  diff := fun c ω => (hF.diff c ω).star
  tame_partial := fun c => by
    have : lwPartial sz n c (fun ω => star (F ω)) =
        fun ω => star (lwPartial sz n c F ω) :=
      funext (lwStein_partial_star sz n c F)
    rw [this]
    simpa [Complex.star_def] using (hF.tame_partial c).conj

/-- `C¹`-tame functions are closed under finite sums. -/
theorem Tame1.sum {κ : Type*} (s : Finset κ) {F : κ → Sizes.SeqΩ sz → ℂ}
    (h : ∀ i ∈ s, Tame1 sz n (F i)) : Tame1 sz n (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Tame1.const (sz := sz) (n := n) 0
  | insert i₀ s hi₀ ih =>
    have h₀ := h i₀ (Finset.mem_insert_self _ _)
    have hs := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert hi₀] using h₀.add hs

/-- `C¹`-tame functions are closed under products over a list. -/
theorem Tame1.listProd {κ : Type*} (l : List κ) {F : κ → Sizes.SeqΩ sz → ℂ}
    (h : ∀ a ∈ l, Tame1 sz n (F a)) : Tame1 sz n (fun ω => (l.map fun a => F a ω).prod) := by
  induction l with
  | nil => simpa using Tame1.const (sz := sz) (n := n) 1
  | cons a l ih =>
    have h₀ := h a (List.mem_cons_self ..)
    have hs := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simpa using h₀.mul hs

/-- `C¹`-tame functions are closed under powers. -/
theorem Tame1.pow {F : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) (k : ℕ) :
    Tame1 sz n (fun ω => F ω ^ k) := by
  induction k with
  | zero => simpa using Tame1.const (sz := sz) (n := n) 1
  | succ k ih => simpa [_root_.pow_succ] using ih.mul hF

/-- `∂_{h_{αw}}` is determined by the real partials of its argument: if the partials of `H` at `ω` are
`a` times those of `F` plus `b` times those of `G`, so is `dhSample`. -/
theorem lwStein_dh_of_partial {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} {H F G : Sizes.SeqΩ sz → ℂ}
    {ω : Sizes.SeqΩ sz} (a b : ℂ)
    (h : ∀ c, lwPartial sz n c H ω = a * lwPartial sz n c F ω + b * lwPartial sz n c G ω) :
    dhSample sz n u α w H ω = a * dhSample sz n u α w F ω + b * dhSample sz n u α w G ω := by
  unfold dhSample
  split_ifs <;> simp only [h] <;> ring

/-- `∂_{h_{αw}}` is additive on `C¹`-tame functions. -/
theorem lwStein_dh_add {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} {F G : Sizes.SeqΩ sz → ℂ}
    (hF : Tame1 sz n F) (hG : Tame1 sz n G) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => F ω + G ω) ω = dhSample sz n u α w F ω + dhSample sz n u α w G ω := by
  have := lwStein_dh_of_partial (u := u) (α := α) (w := w) (ω := ω) (H := fun ω => F ω + G ω)
    (F := F) (G := G) 1 1 (fun c => by rw [lwStein_partial_add hF hG]; ring)
  simpa using this

/-- `∂_{h_{αw}}` of a difference. -/
theorem lwStein_dh_sub {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} {F G : Sizes.SeqΩ sz → ℂ}
    (hF : Tame1 sz n F) (hG : Tame1 sz n G) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => F ω - G ω) ω = dhSample sz n u α w F ω - dhSample sz n u α w G ω := by
  have := lwStein_dh_of_partial (u := u) (α := α) (w := w) (ω := ω) (H := fun ω => F ω - G ω)
    (F := F) (G := G) 1 (-1) (fun c => by rw [lwStein_partial_sub hF hG]; ring)
  simpa [sub_eq_add_neg] using this

/-- **The Leibniz rule for `∂_{h_{αw}}`.** -/
theorem lwStein_dh_mul {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} {F G : Sizes.SeqΩ sz → ℂ}
    (hF : Tame1 sz n F) (hG : Tame1 sz n G) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => F ω * G ω) ω =
      dhSample sz n u α w F ω * G ω + F ω * dhSample sz n u α w G ω := by
  have := lwStein_dh_of_partial (u := u) (α := α) (w := w) (ω := ω) (H := fun ω => F ω * G ω)
    (F := F) (G := G) (G ω) (F ω) (fun c => by rw [lwStein_partial_mul hF hG]; ring)
  rw [this]; ring

/-- `∂_{h_{αw}}` of a constant is `0`. -/
theorem lwStein_dh_const (a : ℂ) {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun _ => a) ω = 0 := by
  unfold dhSample
  split_ifs <;> simp [lwStein_partial_const]

/-- `∂_{h_{αw}}` commutes with multiplication by a constant. -/
theorem lwStein_dh_const_mul (a : ℂ) {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} {F : Sizes.SeqΩ sz → ℂ}
    (hF : Tame1 sz n F) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => a * F ω) ω = a * dhSample sz n u α w F ω := by
  rw [lwStein_dh_mul (Tame1.const a) hF, lwStein_dh_const]; ring

/-- `∂_{h_{αw}}` of a finite sum. -/
theorem lwStein_dh_sum {κ : Type*} (s : Finset κ) {F : κ → Sizes.SeqΩ sz → ℂ}
    (h : ∀ i ∈ s, Tame1 sz n (F i)) {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => ∑ i ∈ s, F i ω) ω = ∑ i ∈ s, dhSample sz n u α w (F i) ω := by
  classical
  induction s using Finset.induction with
  | empty => simpa using lwStein_dh_const (sz := sz) (n := n) (u := u) (α := α) (w := w) 0 ω
  | insert i₀ s hi₀ ih =>
    have h₀ := h i₀ (Finset.mem_insert_self _ _)
    have hs := Tame1.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)
    have := lwStein_dh_add (u := u) (α := α) (w := w) h₀ hs ω
    simp only [Finset.sum_insert hi₀]
    rw [this, ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- The Leibniz rule for a product over a list: the sum over the positions of the list of the
derivative of one factor times the product of the others (`splitEdges`). -/
def lwSplit {κ : Type*} : List κ → List (κ × List κ)
  | [] => []
  | a :: l => (a, l) :: (lwSplit l).map fun p => (p.1, a :: p.2)

/-- `∂_{h_{αw}}` of a product over a list (`lwSplit`): the sum over the positions of the derivative of one factor times the product of the others. -/
theorem lwStein_dh_listProd {κ : Type*} (l : List κ) {F : κ → Sizes.SeqΩ sz → ℂ}
    (h : ∀ a ∈ l, Tame1 sz n (F a)) {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => (l.map fun a => F a ω).prod) ω =
      ((lwSplit l).map fun p => dhSample sz n u α w (F p.1) ω * (p.2.map fun a => F a ω).prod).sum := by
  induction l with
  | nil => simpa [lwSplit] using lwStein_dh_const (sz := sz) (n := n) (u := u) (α := α) (w := w) 1 ω
  | cons a l ih =>
    have h₀ := h a (List.mem_cons_self ..)
    have hs := Tame1.listProd l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.prod_cons]
    rw [lwStein_dh_mul h₀ hs, ih']
    simp only [lwSplit, List.map_cons, List.sum_cons, List.map_map, Function.comp_def, List.prod_cons,
      ]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun x _ => by ring


variable (sz n) in
theorem lwStein_tame_GDG {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (i j : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => (lwGm sz n z u ω * D * lwGm sz n z u ω) i j) := by
  have h : (fun ω => (lwGm sz n z u ω * D * lwGm sz n z u ω) i j) = fun ω =>
      ∑ k, (∑ l, lwG sz n z u i l ω * D l k) * lwG sz n z u k j ω := by
    funext ω
    simp [Matrix.mul_apply, lwG]
  rw [h]
  exact Tame.sum _ fun k _ => (Tame.sum _ fun l _ =>
    (lwStein_tame_lwG sz n hz u i l).mul (Tame.const _)).mul (lwStein_tame_lwG sz n hz u k j)

/-- A resolvent entry `G_{ij}` is `C¹`-tame (`Im z > 0`). -/
theorem lwG_tame1 {z : ℂ} (hz : 0 < z.im) (u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) :
    Tame1 sz n (lwG sz n z u i j) where
  tame := lwStein_tame_lwG sz n hz.ne' u i j
  diff := fun c ω => (lwStein_hasDerivAt_lwG sz n hz.ne' u ω c i j).differentiableAt
  tame_partial := fun c => by
    have : lwPartial sz n c (lwG sz n z u i j) = fun ω =>
        -((Real.sqrt u : ℂ) * (lwGm sz n z u ω * coordinateMatrix d (sz.L n) (sz.W n) c *
          lwGm sz n z u ω) i j) := funext (lwStein_partial_lwG sz n hz.ne' u · c i j)
    rw [this]
    exact ((Tame.const _).mul (lwStein_tame_GDG sz n hz.ne' u _ i j)).neg

variable (sz n) in
/-- **A resolvent polynomial** (T2040d): a polynomial in the entries `G_{ij}` (variable `(i, j, true)`)
and `\bar G_{ij}` (variable `(i, j, false)`) of the resolvent `G = (H_u - z)⁻¹` of the flow, evaluated at the
sample.  The paper's "differentiable function of `G`" (`7_8:295, 310, 335`) is read as this class. -/
def lwVar (z : ℂ) (u : ℝ) (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool)
    (ω : Sizes.SeqΩ sz) : ℂ :=
  if v.2.2 then lwG sz n z u v.1 v.2.1 ω else star (lwG sz n z u v.1 v.2.1 ω)

variable (sz n) in
def lwPoly (z : ℂ) (u : ℝ)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (ω : Sizes.SeqΩ sz) : ℂ :=
  MvPolynomial.eval (fun v => lwVar sz n z u v ω) P

/-- A variable of a resolvent polynomial (`G_{ij}` or `\bar G_{ij}`) is `C¹`-tame. -/
theorem lwVar_tame1 {z : ℂ} (hz : 0 < z.im) (u : ℝ)
    (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) :
    Tame1 sz n (lwVar sz n z u v) := by
  unfold lwVar
  cases h : v.2.2
  · simpa using (lwG_tame1 (sz := sz) (n := n) hz u v.1 v.2.1).conj
  · simpa using lwG_tame1 (sz := sz) (n := n) hz u v.1 v.2.1

/-- **A resolvent polynomial is `C¹`-tame**: bounded (`‖G_{ij}‖ ≤ (Im z)⁻¹`), continuous, finitely
dependent, with tame derivatives along every coordinate. -/
theorem lwPoly_tame1 {z : ℂ} (hz : 0 < z.im) (u : ℝ)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ) :
    Tame1 sz n (lwPoly sz n z u P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    convert Tame1.const (sz := sz) (n := n) a using 1
    funext ω; simp [lwPoly]
  | add p q hp hq =>
    convert hp.add hq using 1
    funext ω; simp [lwPoly, map_add]
  | mul_X p v hp =>
    convert hp.mul (lwVar_tame1 hz u v) using 1
    funext ω; simp [lwPoly, map_mul, MvPolynomial.eval_X]


/-! ### The complex Stein identity on the model -/

theorem lwStein_gvar_off (i j : Idx d (sz.L n) (sz.W n)) (b : Bool) (hij : i ≠ j) :
    ((Sizes.seqGvar sz ⟨n, (i, j, b)⟩ : ℝ≥0) : ℝ) = svarF d (sz.L n) (sz.W n) (sz.lam n) i j / 2 := by
  change (if i = j then svarF d (sz.L n) (sz.W n) (sz.lam n) i j
    else svarF d (sz.L n) (sz.W n) (sz.lam n) i j / 2) = _
  simp [hij]

/-- The variance of a diagonal coordinate is `S_{ii}`. -/
theorem lwStein_gvar_diag (i : Idx d (sz.L n) (sz.W n)) (b : Bool) :
    ((Sizes.seqGvar sz ⟨n, (i, i, b)⟩ : ℝ≥0) : ℝ) = svarF d (sz.L n) (sz.W n) (sz.lam n) i i := by
  change (if i = i then svarF d (sz.L n) (sz.W n) (sz.lam n) i i
    else svarF d (sz.L n) (sz.W n) (sz.lam n) i i / 2) = _
  simp

variable (sz n) in
/-- The variance matrix `S^{(u)} = u · svarF` of the flow `H_u = √u X` (`E|(H_u)_{ij}|² = S^{(u)}_{ij}`,
`integral_normSq_seqHflow`). -/
def lwS (u : ℝ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Matrix.of fun i j => ((u * svarF d (sz.L n) (sz.W n) (sz.lam n) i j : ℝ) : ℂ)

/-- The one-coordinate Stein identity for a `C¹`-tame function (from `GaussIBP`). -/
theorem lwStein_coord (hG : GaussIBP sz) {F : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F)
    (c : CoordF d (sz.L n) (sz.W n)) :
    ∫ ω, ((ω ⟨n, c⟩ : ℝ) : ℂ) * F ω ∂(Sizes.seqP sz) =
      ((Sizes.seqGvar sz ⟨n, c⟩ : ℝ≥0) : ℝ) * ∫ ω, lwPartial sz n c F ω ∂(Sizes.seqP sz) :=
  hG.stein ⟨n, c⟩ F (lwPartial sz n c F) hF.tame (hF.tame_partial c)
    (fun ω => (hF.diff c ω).hasDerivAt)

/-- **The complex Stein identity on the model** (`7_8:298`; Stein's identity for the Hermitian Gaussian
matrix `H_u = √u X`, the entry `(H_u)_{wα}` against the Wirtinger derivative in `h_{αw}`): for a `C¹`-tame `F`,
`E[(H_u)_{wα} F] = u S_{wα} E[∂_{h_{αw}} F]` with `S = svarF`, for every `w, α`, including `w = α`.
Hypothesis: the merged `GaussIBP sz` (owed, S1-19). -/
theorem stein_sample (hG : GaussIBP sz) {F : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) {u : ℝ}
    (hu : 0 ≤ u) (α w : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, sz.seqHflow n u ω w α * F ω ∂(Sizes.seqP sz) =
      lwS sz n u w α * ∫ ω, dhSample sz n u α w F ω ∂(Sizes.seqP sz) := by
  have hSw : lwS sz n u w α = ((u * svarF d (sz.L n) (sz.W n) (sz.lam n) w α : ℝ) : ℂ) := rfl
  rw [hSw]
  rcases hu.eq_or_lt with rfl | hu
  · simp [Sizes.seqHflow]
  have hs := lwStein_sqrt_ne hu
  have h2s : (2 * (Real.sqrt u : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hs
  have hsq : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]
  have iF : ∀ c : CoordF d (sz.L n) (sz.W n),
      Integrable (fun ω => ((ω ⟨n, c⟩ : ℝ) : ℂ) * F ω) (Sizes.seqP sz) := fun c =>
    Tame.integrable hG ((Tame.coord (⟨n, c⟩ : Sizes.SeqCoord sz)).mul hF.tame)
  have iD : ∀ c : CoordF d (sz.L n) (sz.W n),
      Integrable (fun ω => lwPartial sz n c F ω) (Sizes.seqP sz) := fun c =>
    Tame.integrable hG (hF.tame_partial c)
  rcases idxKey_lt_or_eq_or_lt d (sz.L n) (sz.W n) w α with h | rfl | h
  · -- `key w < key α`: `X_{wα} = a + i b` on `(w, α, ·)`
    have hwα : w ≠ α := fun e => absurd (e ▸ h) (lt_irrefl _)
    have e : ∀ ω : Sizes.SeqΩ sz, sz.seqHflow n u ω w α * F ω =
        (Real.sqrt u : ℂ) * (((ω ⟨n, (w, α, true)⟩ : ℝ) : ℂ) * F ω) +
          ((Real.sqrt u : ℂ) * Complex.I) * (((ω ⟨n, (w, α, false)⟩ : ℝ) : ℂ) * F ω) := by
      intro ω
      change (Real.sqrt u : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) w α * F ω = _
      rw [Xentry, ite_eq_left h]
      simp only [Sizes.slice]
      ring
    have hdh : ∀ ω : Sizes.SeqΩ sz, dhSample sz n u α w F ω = (2 * (Real.sqrt u : ℂ))⁻¹ *
        (lwPartial sz n (w, α, true) F ω + Complex.I * lwPartial sz n (w, α, false) F ω) := by
      intro ω
      unfold dhSample
      rw [ite_eq_right h.not_gt, ite_eq_left h]
    simp_rw [e, hdh]
    rw [integral_add ((iF _).const_mul _) ((iF _).const_mul _), integral_const_mul, integral_const_mul,
      lwStein_coord hG hF, lwStein_coord hG hF, integral_const_mul,
      integral_add (iD _) ((iD _).const_mul _), integral_const_mul,
      lwStein_gvar_off w α true hwα, lwStein_gvar_off w α false hwα]
    push_cast
    rw [← hsq]
    field_simp
  · -- `w = α`: `X_{ww} = a` is real
    have e : ∀ ω : Sizes.SeqΩ sz, sz.seqHflow n u ω w w * F ω =
        (Real.sqrt u : ℂ) * (((ω ⟨n, (w, w, true)⟩ : ℝ) : ℂ) * F ω) := by
      intro ω
      change (Real.sqrt u : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) w w * F ω = _
      rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
      simp only [Sizes.slice]
      ring
    have hdh : ∀ ω : Sizes.SeqΩ sz, dhSample sz n u w w F ω =
        (Real.sqrt u : ℂ)⁻¹ * lwPartial sz n (w, w, true) F ω := by
      intro ω
      unfold dhSample
      rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
    simp_rw [e, hdh]
    rw [integral_const_mul, lwStein_coord hG hF, integral_const_mul, lwStein_gvar_diag w true]
    push_cast
    rw [← hsq]
    field_simp
  · -- `key α < key w`: `X_{wα} = a - i b` on `(α, w, ·)`
    have hαw : α ≠ w := fun e => absurd (e ▸ h) (lt_irrefl _)
    have e : ∀ ω : Sizes.SeqΩ sz, sz.seqHflow n u ω w α * F ω =
        (Real.sqrt u : ℂ) * (((ω ⟨n, (α, w, true)⟩ : ℝ) : ℂ) * F ω) -
          ((Real.sqrt u : ℂ) * Complex.I) * (((ω ⟨n, (α, w, false)⟩ : ℝ) : ℂ) * F ω) := by
      intro ω
      change (Real.sqrt u : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) w α * F ω = _
      rw [Xentry, ite_eq_right h.not_gt, ite_eq_left h]
      simp only [Sizes.slice]
      ring
    have hdh : ∀ ω : Sizes.SeqΩ sz, dhSample sz n u α w F ω = (2 * (Real.sqrt u : ℂ))⁻¹ *
        (lwPartial sz n (α, w, true) F ω - Complex.I * lwPartial sz n (α, w, false) F ω) := by
      intro ω
      unfold dhSample
      rw [ite_eq_left h]
    simp_rw [e, hdh]
    rw [integral_sub ((iF _).const_mul _) ((iF _).const_mul _), integral_const_mul, integral_const_mul,
      lwStein_coord hG hF, lwStein_coord hG hF, integral_const_mul,
      integral_sub (iD _) ((iD _).const_mul _), integral_const_mul,
      lwStein_gvar_off α w true hαw, lwStein_gvar_off α w false hαw]
    push_cast
    rw [← hsq, svarF_comm d (sz.L n) (sz.W n) (sz.lam n) w α]
    field_simp


/-- `∂_{h_{αw}}` of a `C¹`-tame function is tame. -/
theorem lwStein_tame_dhSample {F : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) (u : ℝ) (α w : Idx d (sz.L n) (sz.W n)) :
    Tame sz (dhSample sz n u α w F) := by
  unfold dhSample
  split_ifs
  · exact (Tame.const _).mul ((hF.tame_partial _).sub ((Tame.const _).mul (hF.tame_partial _)))
  · exact (Tame.const _).mul ((hF.tame_partial _).add ((Tame.const _).mul (hF.tame_partial _)))
  · exact (Tame.const _).mul (hF.tame_partial _)

/-- **Stein for resolvent polynomials**: no tameness hypothesis is left; `GaussIBP sz` is the only input. -/
theorem stein_lwPoly (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 ≤ u)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (α w : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, sz.seqHflow n u ω w α * lwPoly sz n z u P ω ∂(Sizes.seqP sz) =
      lwS sz n u w α * ∫ ω, dhSample sz n u α w (lwPoly sz n z u P) ω ∂(Sizes.seqP sz) :=
  stein_sample hG (lwPoly_tame1 hz u P) hu α w

/-- The resolvent identity `Σ_α H_{wα} G_{αw} = 1 + z G_{ww}`. -/
theorem lwStein_resolvent_id {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (w : Idx d (sz.L n) (sz.W n)) :
    ∑ α, sz.seqHflow n u ω w α * lwG sz n z u α w ω = 1 + z * lwG sz n z u w w ω := by
  have hU : IsUnit (sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    isUnit_sub_smul_of_isHermitian (Sizes.seqHflow_isHermitian sz n u ω) hz
  have h : ((sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
      Ring.inverse (sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))) w w =
      (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) w w := by
    rw [Ring.mul_inverse_cancel _ hU]
  simp only [lwG, lwGm, Gres, ite_true]
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at h
  linear_combination h


/-- **`E Z_w = 0`** (`(Owx)`, `7_8:298`): for a resolvent polynomial `f`, `df α w = ∂_{h_{αw}} f`, the
Stein defect `Z_w` of the row `w` (`owxDefect`, with `S = S^{(u)} = u · svarF`) has mean zero.  From
the complex Stein identity (`stein_lwPoly`, applied to `G_{αw} f`) and the resolvent identity
`Σ_α H_{wα} G_{αw} = 1 + z G_{ww}`. -/
theorem integral_owxDefect (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (w : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, owxDefect z (lwGm sz n z u ω) (lwS sz n u) (lwPoly sz n z u P ω)
      (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) w ∂(Sizes.seqP sz) = 0 := by
  classical
  have hf : Tame1 sz n (lwPoly sz n z u P) := lwPoly_tame1 hz u P
  have hQ : ∀ α : Idx d (sz.L n) (sz.W n),
      Tame1 sz n (fun ω => lwG sz n z u α w ω * lwPoly sz n z u P ω) :=
    fun α => (lwG_tame1 hz u α w).mul hf
  have hdQ : ∀ (α : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
      dhSample sz n u α w (fun ω => lwG sz n z u α w ω * lwPoly sz n z u P ω) ω =
        -(lwG sz n z u α α ω * lwG sz n z u w w ω) * lwPoly sz n z u P ω +
          lwG sz n z u α w ω * dhSample sz n u α w (lwPoly sz n z u P) ω := by
    intro α ω
    rw [lwStein_dh_mul (lwG_tame1 hz u α w) hf, dhSample_lwG sz n hz hu]
  have hpt : ∀ ω : Sizes.SeqΩ sz,
      owxDefect z (lwGm sz n z u ω) (lwS sz n u) (lwPoly sz n z u P ω)
        (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) w =
      ∑ α, sz.seqHflow n u ω w α * (lwG sz n z u α w ω * lwPoly sz n z u P ω) -
        ∑ α, lwS sz n u w α *
          dhSample sz n u α w (fun ω => lwG sz n z u α w ω * lwPoly sz n z u P ω) ω := by
    intro ω
    have hres := lwStein_resolvent_id (sz := sz) (n := n) hz.ne' u ω w
    have h1 : ∑ α, sz.seqHflow n u ω w α * (lwG sz n z u α w ω * lwPoly sz n z u P ω) =
        (1 + z * lwG sz n z u w w ω) * lwPoly sz n z u P ω := by
      rw [← hres, Finset.sum_mul]
      exact Finset.sum_congr rfl fun α _ => by ring
    have h2 : ∑ α, lwS sz n u w α *
          dhSample sz n u α w (fun ω => lwG sz n z u α w ω * lwPoly sz n z u P ω) ω =
        -((∑ α, lwS sz n u w α * lwGm sz n z u ω α α) * lwG sz n z u w w ω * lwPoly sz n z u P ω) +
          ∑ α, lwS sz n u w α * lwGm sz n z u ω α w *
            dhSample sz n u α w (lwPoly sz n z u P) ω := by
      simp only [hdQ, mul_add, Finset.sum_add_distrib, Finset.sum_mul, ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun α _ => by simp only [lwG]; ring
      · exact Finset.sum_congr rfl fun α _ => by simp only [lwG]; ring
    rw [h1, h2]
    unfold owxDefect
    simp only [lwG]
    ring
  simp_rw [hpt]
  have iA : ∀ α : Idx d (sz.L n) (sz.W n), Integrable (fun ω => sz.seqHflow n u ω w α *
      (lwG sz n z u α w ω * lwPoly sz n z u P ω)) (Sizes.seqP sz) := fun α =>
    Tame.integrable hG ((lwStein_tame_hflow sz n u w α).mul (hQ α).tame)
  have iB : ∀ α : Idx d (sz.L n) (sz.W n), Integrable (fun ω => lwS sz n u w α *
      dhSample sz n u α w (fun ω => lwG sz n z u α w ω * lwPoly sz n z u P ω) ω) (Sizes.seqP sz) := fun α =>
    Tame.integrable hG ((Tame.const _).mul (lwStein_tame_dhSample (hQ α) u α w))
  rw [integral_sub (integrable_finsetSum _ fun α _ => iA α) (integrable_finsetSum _ fun α _ => iB α),
    integral_finsetSum _ fun α _ => iA α, integral_finsetSum _ fun α _ => iB α,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [integral_const_mul]
  have := stein_sample hG (hQ α) hu.le α w
  rw [this]
  simp [lwS]


/-- The rows of the fine-lattice variance profile sum to `1` (copy of the `example` at
`RBM3D/Gauss/FineModel.lean:643`, `sum_sbKernelR`, `3 ≤ L`). -/
private theorem lwStein_sum_svarF_row (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g : ℝ)
    (i : Idx d L W) : ∑ j, svarF d L W g i j = 1 := by
  classical
  have h1 : ∑ j : Idx d L W, svarF d L W g i j =
      ∑ p : Vtx d L W, ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 p.1 :=
    Fintype.sum_equiv (splitEquiv d L W) _ _ fun j => rfl
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  have h2 : ∑ x : Zd d L, SBR d L g (split d L W i).1 x = 1 := by
    simp only [SBR, Matrix.of_apply]
    rw [← sum_sbKernelR d L g hL]
    exact Fintype.sum_equiv (Equiv.subLeft (split d L W i).1) _ _ fun x => rfl
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← h2]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  field_simp

/-- The rows of `S^{(u)} = u · svarF` sum to `u`. -/
theorem lwS_row_sum (u : ℝ) (i : Idx d (sz.L n) (sz.W n)) : ∑ j, lwS sz n u i j = (u : ℂ) := by
  have h := lwStein_sum_svarF_row (d := d) (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) i
  simp only [lwS, Matrix.of_apply]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum, h, mul_one]


/-- Closure of `Tame` under the operations that occur in the expansions (finite sums, products,
differences, constants), with the resolvent entries and the derivatives as leaves. -/
local macro "lw_tame" : tactic =>
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

/-- **`(Owx)` in expectation, for every resolvent polynomial** (`7_8:294-306`, `ssl`): the general form of the
probe's `owx_smallest_E`.  Hypotheses: `GaussIBP sz` (owed, S1-19); `m ≠ 0`, `z + u m = -m⁻¹` (`z_u + u m = -1/m`,
the flow of `(self_m)`), and `S⁺ = Sp` with `S⁺ (1 - m² S) = S` for `S = S^{(u)} = u · svarF` (`(eq:def-Spm)`;
the rows of `S^{(u)}` sum to `u`, proved here).  `df α x = ∂_{h_{αx}} f` (`dhSample`).  With `Ǧ = G - m`. -/
theorem owx_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (x : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (lwG sz n z u x x ω - m) * lwPoly sz n z u P ω ∂(Sizes.seqP sz) =
      ∫ ω, (m * ∑ α, lwS sz n u x α * (lwG sz n z u x x ω - m) * (lwG sz n z u α α ω - m) *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
            (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α x ω * dhSample sz n u α x (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω) ∂(Sizes.seqP sz) := by
  classical
  have hz' : z.im ≠ 0 := hz.ne'
  have hf : Tame1 sz n (lwPoly sz n z u P) := lwPoly_tame1 hz u P
  have tf : Tame sz (lwPoly sz n z u P) := hf.tame
  have tD : ∀ α β : Idx d (sz.L n) (sz.W n), Tame sz (dhSample sz n u α β (lwPoly sz n z u P)) :=
    fun α β => lwStein_tame_dhSample hf u α β
  have hpt : ∀ ω : Sizes.SeqΩ sz,
      ((lwG sz n z u x x ω - m) * lwPoly sz n z u P ω -
        (m * ∑ α, lwS sz n u x α * (lwG sz n z u x x ω - m) * (lwG sz n z u α α ω - m) *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
            (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α x ω * dhSample sz n u α x (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω)) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) *
        owxDefect z (lwGm sz n z u ω) (lwS sz n u) (lwPoly sz n z u P ω)
          (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) w :=
    fun ω => owx_defect_identity z m (u : ℂ) hm0 hzm (lwGm sz n z u ω) (lwS sz n u) Sp
      (lwS_row_sum u) hSp (lwPoly sz n z u P ω) (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) x
  have iZ : ∀ w : Idx d (sz.L n) (sz.W n), Integrable (fun ω => owxDefect z (lwGm sz n z u ω)
      (lwS sz n u) (lwPoly sz n z u P ω) (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) w)
      (Sizes.seqP sz) := by
    intro w
    refine Tame.integrable hG ?_
    unfold owxDefect
    lw_tame
  have hzero : ∫ ω, ((lwG sz n z u x x ω - m) * lwPoly sz n z u P ω -
        (m * ∑ α, lwS sz n u x α * (lwG sz n z u x x ω - m) * (lwG sz n z u α α ω - m) *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
            (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α x ω * dhSample sz n u α x (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω)) ∂(Sizes.seqP sz) = 0 := by
    simp_rw [hpt]
    rw [integral_const_mul, integral_finsetSum _ fun w _ => (iZ w).const_mul _]
    simp [integral_const_mul, integral_owxDefect hG hz hu P]
  have iL : Integrable (fun ω => (lwG sz n z u x x ω - m) * lwPoly sz n z u P ω) (Sizes.seqP sz) := by
    refine Tame.integrable hG ?_
    lw_tame
  have iR : Integrable (fun ω => (m * ∑ α, lwS sz n u x α * (lwG sz n z u x x ω - m) * (lwG sz n z u α α ω - m) *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
            (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α x ω * dhSample sz n u α x (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω)) (Sizes.seqP sz) := by
    refine Tame.integrable hG ?_
    lw_tame
  rw [integral_sub iL iR] at hzero
  linear_combination hzero

variable (sz n) in
/-- **`S⁺ = S (1 - m² S)⁻¹`** (`(eq:def-Spm)`) for `S = S^{(u)} = u · svarF`. -/
def lwSplus (u : ℝ) (m : ℂ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  lwS sz n u * Ring.inverse (1 - m ^ 2 • lwS sz n u)

/-- `1 - m² S^{(u)}` is invertible when `|m|² u < 1` (strict diagonal dominance: the rows of `S^{(u)}` are
non-negative and sum to `u`). -/
theorem lwS_isUnit {u : ℝ} (hu : 0 ≤ u) {m : ℂ} (hm : ‖m‖ ^ 2 * u < 1) :
    IsUnit (1 - m ^ 2 • lwS sz n u) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  set s : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℝ := svarF d (sz.L n) (sz.W n) (sz.lam n)
    with hs
  have hs0 : ∀ i j, 0 ≤ s i j := svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n)
  have hrow : ∑ j, s k j = 1 := lwStein_sum_svarF_row (d := d) (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) k
  have hoff : ∀ j ∈ Finset.univ.erase k, ‖(1 - m ^ 2 • lwS sz n u) k j‖ = ‖m‖ ^ 2 * (u * s k j) := by
    intro j hj
    have hjk : k ≠ j := fun e => (Finset.ne_of_mem_erase hj) e.symm
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hjk, lwS, Matrix.of_apply,
      smul_eq_mul, zero_sub, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hu, abs_of_nonneg (svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) k j)]
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum : ∑ j ∈ Finset.univ.erase k, s k j = 1 - s k k := by
    rw [← hrow, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    ring
  have hdiag : 1 - ‖m‖ ^ 2 * (u * s k k) ≤ ‖(1 - m ^ 2 • lwS sz n u) k k‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (m ^ 2 * (lwS sz n u k k))
    have e : (1 - m ^ 2 • lwS sz n u) k k = 1 - m ^ 2 * lwS sz n u k k := by simp
    rw [e]
    have e2 : ‖m ^ 2 * lwS sz n u k k‖ = ‖m‖ ^ 2 * (u * s k k) := by
      simp only [lwS, Matrix.of_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg hu, abs_of_nonneg (svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) k k)]
    rw [e2] at h
    simpa using h
  rw [hsum]
  have : 0 ≤ ‖m‖ ^ 2 * u := by positivity
  nlinarith [hs0 k k, mul_nonneg this (hs0 k k)]

/-- `S⁺ (1 - m² S) = S` entrywise: `S⁺_{ij} - m² Σ_w S⁺_{iw} S_{wj} = S_{ij}` for `S = S^{(u)}`, `|m|² u < 1`. -/
theorem lwSplus_spec {u : ℝ} (hu : 0 ≤ u) {m : ℂ} (hm : ‖m‖ ^ 2 * u < 1) (i j : Idx d (sz.L n) (sz.W n)) :
    lwSplus sz n u m i j - m ^ 2 * ∑ w, lwSplus sz n u m i w * lwS sz n u w j = lwS sz n u i j := by
  have hU := lwS_isUnit (sz := sz) (n := n) hu hm
  have h : lwSplus sz n u m * (1 - m ^ 2 • lwS sz n u) = lwS sz n u := by
    unfold lwSplus
    rw [Matrix.mul_assoc, Ring.inverse_mul_cancel _ hU, Matrix.mul_one]
  have := congrFun (congrFun h i) j
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul] at this
  simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply] using this

end Sample

/-! ## The derivative of a graph value (item 5)

The vertices of the derivative graphs are those of `Γ` (`inl a ↦ inl (inl a)`, `inr i ↦ inr i`) and two
*new external* vertices `α = inl (inr 0)`, `w = inl (inr 1)`, with the labels `α, w` of `∂_{h_{αw}}`. -/

section GraphDeriv

variable {E I : Type*}

/-- The embedding of the vertices of `Γ` into those of its derivative graphs (two new external vertices). -/
def lwEmb : E ⊕ I → (E ⊕ Fin 2) ⊕ I := Sum.map Sum.inl id

/-- **The two edges replacing a solid edge `e` in its derivative** (`∂_{h_{αw}} G_{ab} = -G_{aα} G_{wb}`,
`∂_{h_{αw}} \bar G_{ab} = -\bar G_{aw} \bar G_{αb}`; the circle is dropped, `M` is constant): the blue edge
`a → b` becomes `a → α` and `w → b`, the red edge becomes `a → w` and `α → b`; `α = inl (inr 0)`,
`w = inl (inr 1)`. -/
def lwDEdges (e : SEdge (E ⊕ I)) : SEdge ((E ⊕ Fin 2) ⊕ I) × SEdge ((E ⊕ Fin 2) ⊕ I) :=
  if e.σ then (⟨true, false, lwEmb e.src, Sum.inl (Sum.inr 0)⟩, ⟨true, false, Sum.inl (Sum.inr 1), lwEmb e.dst⟩)
  else (⟨false, false, lwEmb e.src, Sum.inl (Sum.inr 1)⟩, ⟨false, false, Sum.inl (Sum.inr 0), lwEmb e.dst⟩)

/-- **The derivative graph of the solid edge `p.1`** (with the other solid edges `p.2`): the edge `p.1` is
replaced by the two edges of `lwDEdges`, the coefficient changes sign, the waved and dotted edges stay;
`n_S + 1` solid edges, the two new vertices `α, w` are external. -/
def LGraph.dTerm (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph (E ⊕ Fin 2) I where
  solid := p.2.map (SEdge.map lwEmb) ++ [(lwDEdges p.1).1, (lwDEdges p.1).2]
  waved := Γ.waved.map (WEdge.map lwEmb)
  dotted := Γ.dotted.map (DEdge.map lwEmb)
  coeff := -Γ.coeff

/-- **The derivative of a graph**: one term for each solid edge of `Γ`, light-weights and weights included
(`lwSplit`). -/
def LGraph.dTerms (Γ : LGraph E I) : List (LGraph (E ⊕ Fin 2) I) :=
  (lwSplit Γ.solid).map Γ.dTerm

/-- `lwSplit` has one entry for each element of the list. -/
theorem lwSplit_length {κ : Type*} (l : List κ) : (lwSplit l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [lwSplit, ih]

/-- Each entry of `lwSplit l` leaves one element out of `l`. -/
theorem lwSplit_snd_length {κ : Type*} (l : List κ) :
    ∀ p ∈ lwSplit l, p.2.length + 1 = l.length := by
  induction l with
  | nil => simp [lwSplit]
  | cons a l ih =>
    intro p hp
    simp only [lwSplit, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · simp
    · simpa using ih q hq


end GraphDeriv

section GraphDerivVal

variable {d : ℕ} (sz : Sizes d) (n : ℕ) {E I : Type*}

/-- The graph data at the sample `ω`: the resolvent `G` of the flow (the only random matrix), and the
deterministic `M`, `S`, `S⁺`. -/
def lwSampleData (z : ℂ) (u : ℝ) (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ω : Sizes.SeqΩ sz) : LData (Idx d (sz.L n) (sz.W n)) :=
  ⟨lwGm sz n z u ω, M, S, Sp⟩

variable {sz n}
variable {z : ℂ} {u : ℝ} {M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

theorem lwStein_sedge_val_blue {V : Type*} (e : SEdge V) (hσ : e.σ = true) (ℓ : V → Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) :
    SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ e =
      lwG sz n z u (ℓ e.src) (ℓ e.dst) ω - (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0) := by
  simp [SEdge.val, hσ, lwSampleData, lwG]

/-- The factor of a red solid edge: `\overline{G_{ab}} - \overline{M_{ab}}` (or without `M`). -/
theorem lwStein_sedge_val_red {V : Type*} (e : SEdge V) (hσ : e.σ = false) (ℓ : V → Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) :
    SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ e =
      star (lwG sz n z u (ℓ e.src) (ℓ e.dst) ω) - star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0) := by
  simp [SEdge.val, hσ, lwSampleData, lwG, star_sub]

/-- The factor of a solid edge is `C¹`-tame as a function of the sample. -/
theorem lwStein_sedge_val_tame1 (hz : 0 < z.im) {V : Type*} (e : SEdge V)
    (ℓ : V → Idx d (sz.L n) (sz.W n)) :
    Tame1 sz n (fun ω => SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ e) := by
  have hG := lwG_tame1 (sz := sz) (n := n) hz u (ℓ e.src) (ℓ e.dst)
  cases hσ : e.σ
  · have h := hG.conj.sub (Tame1.const (n := n) (sz := sz) (star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0)))
    convert h using 1
    funext ω
    exact lwStein_sedge_val_red e hσ ℓ ω
  · have h := hG.sub (Tame1.const (n := n) (sz := sz) (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0))
    convert h using 1
    funext ω
    exact lwStein_sedge_val_blue e hσ ℓ ω

/-- **The derivative of one edge factor** (`7_8:298`): `∂_{h_{αw}} (G-M)_{ab} = -G_{aα} G_{wb}`
(blue, with or without circle), `∂_{h_{αw}} \overline{(G-M)_{ab}} = -\bar G_{aw} \bar G_{αb}` (red): the factor
is replaced by the product of the two factors of `lwDEdges`. -/
theorem lwStein_dh_sedge_val (hz : 0 < z.im) (hu : 0 < u) {V : Type*} (e : SEdge V) (α w : Idx d (sz.L n) (sz.W n))
    (ℓ : V → Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ e) ω =
      if e.σ then -(lwG sz n z u (ℓ e.src) α ω * lwG sz n z u w (ℓ e.dst) ω)
      else -(star (lwG sz n z u (ℓ e.src) w ω) * star (lwG sz n z u α (ℓ e.dst) ω)) := by
  cases hσ : e.σ
  · have hfun : (fun ω => SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ e) = fun ω =>
        star (lwG sz n z u (ℓ e.src) (ℓ e.dst) ω) - star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0) :=
      funext (lwStein_sedge_val_red e hσ ℓ)
    rw [hfun, lwStein_dh_sub (lwG_tame1 hz u _ _).conj (Tame1.const _), lwStein_dh_const,
      dhSample_lwG_star sz n hz hu]
    simp [star_mul']
  · have hfun : (fun ω => SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ e) = fun ω =>
        lwG sz n z u (ℓ e.src) (ℓ e.dst) ω - (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0) :=
      funext (lwStein_sedge_val_blue e hσ ℓ)
    rw [hfun, lwStein_dh_sub (lwG_tame1 hz u _ _) (Tame1.const _), lwStein_dh_const, dhSample_lwG sz n hz hu]
    simp


/-- The product of the edge factors of the derivative graph of the edge `p.1`: the factors of the two new
edges are the two factors of the derivative of `p.1`, with the sign of the coefficient. -/
theorem lwStein_dTerm_term (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (α w : Idx d (sz.L n) (sz.W n)) (ℓ' : (E ⊕ Fin 2) ⊕ I → Idx d (sz.L n) (sz.W n))
    (hα : ℓ' (Sum.inl (Sum.inr 0)) = α) (hw : ℓ' (Sum.inl (Sum.inr 1)) = w) (ω : Sizes.SeqΩ sz) :
    (Γ.dTerm p).term (lwSampleData sz n z u M S Sp ω) ℓ' =
      (-Γ.coeff) * ((p.2.map (SEdge.val (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb))).prod *
        (if p.1.σ then lwG sz n z u (ℓ' (lwEmb p.1.src)) α ω * lwG sz n z u w (ℓ' (lwEmb p.1.dst)) ω
          else star (lwG sz n z u (ℓ' (lwEmb p.1.src)) w ω) * star (lwG sz n z u α (ℓ' (lwEmb p.1.dst)) ω))) *
        (Γ.waved.map (WEdge.val (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb))).prod *
        (Γ.dotted.map (DEdge.val (ℓ' ∘ lwEmb))).prod := by
  have hS : (SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ') ∘ (SEdge.map lwEmb) =
      SEdge.val (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb) := funext fun e => rfl
  have hW : (WEdge.val (lwSampleData sz n z u M S Sp ω) ℓ') ∘ (WEdge.map lwEmb) =
      WEdge.val (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb) := funext fun e => rfl
  have hD : (DEdge.val ℓ') ∘ (DEdge.map lwEmb) = DEdge.val (ℓ' ∘ lwEmb) := funext fun e => rfl
  simp only [LGraph.term, LGraph.dTerm, List.map_append, List.prod_append, List.map_map, hS, hW, hD,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  by_cases hσ : p.1.σ = true
  · simp [lwDEdges, hσ, SEdge.val, lwSampleData, lwG, hα, hw]
  · simp [lwDEdges, hσ, SEdge.val, lwSampleData, lwG, hα, hw]


/-- The part of the value of a term that does not depend on the sample: coefficient, waved and dotted
factors. -/
def lwK {ι : Type*} [DecidableEq ι] (Γ : LGraph E I) (M S Sp : Matrix ι ι ℂ) (ℓ : E ⊕ I → ι) : ℂ :=
  Γ.coeff * (Γ.waved.map (WEdge.val (⟨0, M, S, Sp⟩ : LData ι) ℓ)).prod * (Γ.dotted.map (DEdge.val ℓ)).prod

/-- The term of a graph is the sample-independent part times the product of the solid edge factors. -/
theorem lwStein_term_eq (Γ : LGraph E I) (ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    Γ.term (lwSampleData sz n z u M S Sp ω) ℓ =
      lwK Γ M S Sp ℓ * (Γ.solid.map (SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ)).prod := by
  have hW : WEdge.val (lwSampleData sz n z u M S Sp ω) ℓ = WEdge.val (⟨0, M, S, Sp⟩ : LData _) ℓ := rfl
  simp only [LGraph.term, lwK, hW]
  ring

/-- The term of a graph is `C¹`-tame as a function of the sample. -/
theorem lwStein_term_tame1 (hz : 0 < z.im) (Γ : LGraph E I) (ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n)) :
    Tame1 sz n (fun ω => Γ.term (lwSampleData sz n z u M S Sp ω) ℓ) := by
  have hfun : (fun ω => Γ.term (lwSampleData sz n z u M S Sp ω) ℓ) = fun ω =>
      lwK Γ M S Sp ℓ * (Γ.solid.map (SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ)).prod :=
    funext (lwStein_term_eq Γ ℓ)
  rw [hfun]
  exact (Tame1.const _).mul (Tame1.listProd _ fun e _ => lwStein_sedge_val_tame1 hz e ℓ)

/-- **The derivative of the term of a graph at a labelling**: the sum over the solid edges (`lwSplit`) of
the term of the derivative graph `Γ.dTerm`, at the labelling that extends `ℓ'` by `α, w` on the two new
external vertices. -/
theorem lwStein_dh_term (hz : 0 < z.im) (hu : 0 < u) (Γ : LGraph E I) (α w : Idx d (sz.L n) (sz.W n))
    (ℓ' : (E ⊕ Fin 2) ⊕ I → Idx d (sz.L n) (sz.W n))
    (hα : ℓ' (Sum.inl (Sum.inr 0)) = α) (hw : ℓ' (Sum.inl (Sum.inr 1)) = w) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => Γ.term (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb)) ω =
      (Γ.dTerms.map fun Γ' => Γ'.term (lwSampleData sz n z u M S Sp ω) ℓ').sum := by
  have hfun : (fun ω => Γ.term (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb)) = fun ω =>
      lwK Γ M S Sp (ℓ' ∘ lwEmb) *
        (Γ.solid.map (SEdge.val (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb))).prod :=
    funext (lwStein_term_eq Γ _)
  have hT : ∀ e ∈ Γ.solid, Tame1 sz n (fun ω => SEdge.val (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb) e) :=
    fun e _ => lwStein_sedge_val_tame1 hz e _
  rw [hfun, lwStein_dh_const_mul _ (Tame1.listProd _ hT), lwStein_dh_listProd _ hT]
  simp only [LGraph.dTerms, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  simp only [Function.comp_apply]
  rw [lwStein_dTerm_term Γ p α w ℓ' hα hw ω, lwStein_dh_sedge_val hz hu p.1 α w (ℓ' ∘ lwEmb) ω]
  have hW : WEdge.val (lwSampleData sz n z u M S Sp ω) (ℓ' ∘ lwEmb) =
      WEdge.val (⟨0, M, S, Sp⟩ : LData _) (ℓ' ∘ lwEmb) := rfl
  unfold lwK
  rw [hW]
  by_cases hσ : p.1.σ = true <;> simp [hσ] <;> ring

/-- A finite sum of list sums is the list of the finite sums. -/
theorem lwStein_sum_list {β κ : Type*} [Fintype β] (L : List κ) (f : κ → β → ℂ) :
    ∑ b, (L.map fun x => f x b).sum = (L.map fun x => ∑ b, f x b).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Finset.sum_add_distrib, ih]

/-- **The graph derivative** (item 5; `(Owx)` third and fourth terms, `7_8:298`): for a graph `Γ` with
external labels `ℓe`, `∂_{h_{αw}}` of its value `Γ.val` (a function of the sample through `G = (H_u - z)⁻¹`;
`M`, `S`, `S⁺` deterministic) is the sum over the solid edges of `Γ` -- weights and light-weights included, the
light-weight `Ǧ = G - M` has the derivative of `G` -- of the values of the derivative graphs `Γ.dTerm`
(`Γ.dTerms`), at the external labels `ℓe` extended by `α, w`.  The counters of each term:
`LGraph.dTerm_counters`. -/
theorem dhSample_graphVal [Fintype I] [DecidableEq I] (hz : 0 < z.im) (hu : 0 < u) (Γ : LGraph E I)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) (α w : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => Γ.val (lwSampleData sz n z u M S Sp ω) ℓe) ω =
      (Γ.dTerms.map fun Γ' => Γ'.val (lwSampleData sz n z u M S Sp ω) (Sum.elim ℓe ![α, w])).sum := by
  classical
  unfold LGraph.val
  rw [lwStein_dh_sum Finset.univ fun ℓi _ => lwStein_term_tame1 hz Γ _]
  have hterm : ∀ ℓi : I → Idx d (sz.L n) (sz.W n),
      dhSample sz n u α w (fun ω => Γ.term (lwSampleData sz n z u M S Sp ω) (Sum.elim ℓe ℓi)) ω =
        (Γ.dTerms.map fun Γ' => Γ'.term (lwSampleData sz n z u M S Sp ω)
          (Sum.elim (Sum.elim ℓe ![α, w]) ℓi)).sum := by
    intro ℓi
    have hcomp : (Sum.elim (Sum.elim ℓe ![α, w]) ℓi) ∘ lwEmb = Sum.elim ℓe ℓi := by
      funext v
      rcases v with a | b <;> simp [lwEmb]
    have := lwStein_dh_term (M := M) (S := S) (Sp := Sp) hz hu Γ α w (Sum.elim (Sum.elim ℓe ![α, w]) ℓi)
      (by simp) (by simp) ω
    rwa [hcomp] at this
  simp_rw [hterm]
  rw [lwStein_sum_list]

end GraphDerivVal


/-! ### The counters of the derivative graphs -/

section DCounters

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The molecule counter only reads the waved and the `=`-dotted edges. -/
theorem lwStein_nM_congr (Γ₁ Γ₂ : LGraph E I) (hW : Γ₁.waved = Γ₂.waved) (hD : Γ₁.dotted = Γ₂.dotted) :
    Γ₁.nM = Γ₂.nM := by
  have hadj : Γ₁.adj = Γ₂.adj := by
    funext u v
    simp only [LGraph.adj, hW, hD]
  have hstep : Γ₁.step = Γ₂.step := by
    funext s
    simp only [LGraph.step, hadj]
  have hmol : Γ₁.mol = Γ₂.mol := by
    funext v
    simp only [LGraph.mol, hstep]
  simp only [LGraph.nM, hmol]

/-- The graph with two vertices (external) and no edge has no internal molecule. -/
theorem lwStein_nM_empty (Z : LGraph (Fin 2) (Fin 0)) : Z.nM = 0 := by
  unfold LGraph.nM
  rw [Finset.card_eq_zero, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro v _ h
  rcases v with a | b
  · have := h (Sum.inl a) ((Z.mem_mol_iff _ _).2 (SimpleGraph.Reachable.refl _))
    simp at this
  · exact b.elim0

/-- **The counters of the derivative graphs** (item 5): replacing a solid edge by its two edges through the
new external vertices `α, w` adds one solid edge and nothing else: `n_S + 1`, `n_W`, `n_V` (the new
vertices are external) and `n_M` (no waved or dotted edge is touched) are those of `Γ`, plus one in `n_S`. -/
theorem LGraph.dTerm_counters (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) :
    (Γ.dTerm p).nS = Γ.nS + 1 ∧ (Γ.dTerm p).nW = Γ.nW ∧ (Γ.dTerm p).nV = Γ.nV ∧
      (Γ.dTerm p).nM = Γ.nM := by
  refine ⟨?_, by simp [LGraph.nW, LGraph.dTerm], rfl, ?_⟩
  · have := lwSplit_snd_length Γ.solid p hp
    simp only [LGraph.nS, LGraph.dTerm, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · let Z : LGraph (Fin 2) (Fin 0) := ⟨[], [], [], 1⟩
    let φ : (E ⊕ Fin 2) ⊕ (I ⊕ Fin 0) ≃ (E ⊕ Fin 2) ⊕ I :=
      Equiv.sumCongr (Equiv.refl _) (Equiv.sumEmpty I (Fin 0))
    have hφ : ∀ v, (φ v).isRight = v.isRight := by
      intro v
      rcases v with x | y <;> simp [φ]
    have hc := (Γ.disjUnion Z).counters_relabel_equiv φ hφ
    have hcomp : ∀ v : E ⊕ I, φ (lwUnionV₁ (E₂ := Fin 2) (I₂ := Fin 0) v) = lwEmb v := by
      intro v
      rcases v with a | b <;> simp [φ, lwUnionV₁, lwEmb]
    have hW : (Γ.dTerm p).waved = ((Γ.disjUnion Z).relabel φ).waved := by
      simp only [LGraph.dTerm, LGraph.relabel, LGraph.disjUnion, Z, List.map_nil, List.append_nil,
        List.map_map]
      refine List.map_congr_left fun e _ => ?_
      simp only [Function.comp_apply, WEdge.map, hcomp]
    have hD : (Γ.dTerm p).dotted = ((Γ.disjUnion Z).relabel φ).dotted := by
      simp only [LGraph.dTerm, LGraph.relabel, LGraph.disjUnion, Z, List.map_nil, List.append_nil,
        List.map_map]
      refine List.map_congr_left fun e _ => ?_
      simp only [Function.comp_apply, DEdge.map, hcomp]
    rw [lwStein_nM_congr _ _ hW hD, hc.2.2.2, LGraph.nM_disjUnion, lwStein_nM_empty, add_zero]

omit [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] in
theorem LGraph.dTerms_length (Γ : LGraph E I) : Γ.dTerms.length = Γ.nS := by
  simp [LGraph.dTerms, lwSplit_length, LGraph.nS]

/-- **The scaling order of each derivative graph is that of `Γ` plus one** (`n_S + 1`, `n_W`, `n_V` as
above): the derivative terms of `(Owx)` have `ord = ord(Γ) + 1`. -/
theorem LGraph.dTerm_ord (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) : ord (Γ.dTerm p).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := Γ.dTerm_counters p hp
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

/-- Every derivative graph has one solid edge more and the other counters of `Γ`. -/
theorem LGraph.dTerms_counters (Γ : LGraph E I) :
    ∀ Γ' ∈ Γ.dTerms, Γ'.nS = Γ.nS + 1 ∧ Γ'.nW = Γ.nW ∧ Γ'.nV = Γ.nV ∧ Γ'.nM = Γ.nM := by
  intro Γ' hΓ'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hΓ'
  exact Γ.dTerm_counters p hp

end DCounters


/-! ## Compiled instances -/

section Instances

open RBM.Gauss.SizesInst

/-- The small admissible-shape size sequence of the preflight (`d = 3`, `L = 3`, `W = 2`, `N = 216`, coupling `1/2`),
constant in `n`. -/
def lwSzT : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_refl 3
  W_pos := fun _ => by norm_num

/-- The spectral parameter `z = 0.3 + 0.05 i` of the preflight. -/
def lwZ : ℂ := (3 / 10 : ℝ) + (1 / 20 : ℝ) * Complex.I

/-- `Im z > 0` at `z = 0.3 + 0.05 i`. -/
theorem lwZ_im : 0 < lwZ.im := by simp [lwZ]

/-- **Item 2 at `d = 3`, `L = 3`, `W = 2`** (`N = 216`), `z = 0.3 + 0.05 i`, `u = 7/10`, at every sample `ω`
(in particular at the sample below) and every `α, w, i, j`: both closed forms. -/
example (ω : Sizes.SeqΩ lwSzT) (α w i j : Idx 3 (lwSzT.L 0) (lwSzT.W 0)) :
    dhSample lwSzT 0 (7 / 10) α w (lwG lwSzT 0 lwZ (7 / 10) i j) ω =
        -(lwG lwSzT 0 lwZ (7 / 10) i α ω * lwG lwSzT 0 lwZ (7 / 10) w j ω) ∧
      dhSample lwSzT 0 (7 / 10) α w (fun ω => star (lwG lwSzT 0 lwZ (7 / 10) i j ω)) ω =
        -star (lwG lwSzT 0 lwZ (7 / 10) i w ω * lwG lwSzT 0 lwZ (7 / 10) α j ω) :=
  ⟨dhSample_lwG lwSzT 0 lwZ_im (by norm_num) α w i j ω,
    dhSample_lwG_star lwSzT 0 lwZ_im (by norm_num) α w i j ω⟩

/-- A fixed non-trivial sample: real part `1/2`, imaginary part `-1/3` in every coordinate. -/
def lwOmega : Sizes.SeqΩ lwSzT := fun c => if c.2.2.2 then 1 / 2 else -(1 / 3)

/-- **Item 2 at a fixed sample and fixed vertices** (`0` and `(1, 0, 0)` in `Z_6^3`). -/
example :
    dhSample lwSzT 0 (7 / 10) (0 : Idx 3 (lwSzT.L 0) (lwSzT.W 0)) ![1, 0, 0]
        (lwG lwSzT 0 lwZ (7 / 10) 0 ![1, 0, 0]) lwOmega =
      -(lwG lwSzT 0 lwZ (7 / 10) 0 0 lwOmega * lwG lwSzT 0 lwZ (7 / 10) ![1, 0, 0] ![1, 0, 0] lwOmega) :=
  dhSample_lwG lwSzT 0 lwZ_im (by norm_num) _ _ _ _ _

/-- The resolvent polynomial `X (i, j, true)` is the entry `G_{ij}`. -/
theorem lwPoly_X_true {d : ℕ} (sz : Sizes d) (n : ℕ) {z : ℂ} (u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) :
    lwPoly sz n z u (MvPolynomial.X (i, j, true)) = lwG sz n z u i j := by
  funext ω
  simp [lwPoly, lwVar]

/-- `m = i/2`, `z = 7 i / 4`, `u = 1/2`: `z + u m = -1/m` (`2 i = 2 i`), `|m|² u = 1/8 < 1`, `Im z > 0`. -/
def lwM0 : ℂ := Complex.I / 2

def lwZ0 : ℂ := 7 * Complex.I / 4

/-- `Im z > 0` at `z = 7i/4`. -/
theorem lwZ0_im : 0 < lwZ0.im := by simp [lwZ0]

/-- `m = i/2 ≠ 0`. -/
theorem lwM0_ne : lwM0 ≠ 0 := by simp [lwM0]

/-- `z + u m = -m⁻¹` at `u = 1/2`. -/
theorem lwM0_hzm : lwZ0 + (((1 / 2 : ℝ)) : ℂ) * lwM0 = -lwM0⁻¹ := by
  simp only [lwZ0, lwM0]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- `|m|² u = 1/8 < 1` at `u = 1/2`. -/
theorem lwM0_norm : ‖lwM0‖ ^ 2 * (1 / 2 : ℝ) < 1 := by
  simp [lwM0]
  norm_num

/-- **Tameness of a resolvent polynomial** at `d = 3`, `L = 3`, `W = 2`: `|G_{00}|² + 2`
(`G_{00} \bar G_{00} + 2`), `u = 7/10`, `z = 0.3 + 0.05 i`; the bound `|G_{ij}| ≤ 20 = (Im z)⁻¹` of the envelope. -/
example : Tame1 lwSzT 0 (lwPoly lwSzT 0 lwZ (7 / 10)
    (MvPolynomial.X (0, 0, true) * MvPolynomial.X (0, 0, false) + MvPolynomial.C 2)) :=
  lwPoly_tame1 lwZ_im _ _

example (ω : Sizes.SeqΩ lwSzT) (i j : Idx 3 (lwSzT.L 0) (lwSzT.W 0)) :
    ‖lwG lwSzT 0 lwZ (7 / 10) i j ω‖ ≤ 20 := by
  have h := lwStein_norm_lwG_le lwSzT 0 lwZ_im.ne' (7 / 10) i j ω
  have e : |lwZ.im|⁻¹ = (20 : ℝ) := by simp [lwZ]
  rwa [e] at h

/-- **The convention of `dhSample` against the matrix-level complex derivative along `E_{αw}`**, at `d = 3`,
`L = 3`, `W = 2` and the fixed sample `lwOmega`. -/
example (α w i j : Idx 3 (lwSzT.L 0) (lwSzT.W 0)) :
    dhSample lwSzT 0 (7 / 10) α w (lwG lwSzT 0 lwZ (7 / 10) i j) lwOmega =
      deriv (fun s : ℂ => Ring.inverse ((lwSzT.seqHflow 0 (7 / 10) lwOmega -
        lwZ • (1 : Matrix (Idx 3 (lwSzT.L 0) (lwSzT.W 0)) (Idx 3 (lwSzT.L 0) (lwSzT.W 0)) ℂ)) +
          s • single α w (1 : ℂ)) i j) 0 :=
  dhSample_lwG_eq_deriv lwSzT 0 lwZ_im (by norm_num) α w i j lwOmega

/-- **Item 3 at `sz0` (`d = 3`, `L = 4`, `W = 32`, `n = 0`)**, `F = G_{xx}`, `u = 1/2`: the complex Stein
identity `E[(H_u)_{wα} G_{xx}] = u S_{wα} E[-G_{xα} G_{wx}]` for every `w, α, x`, with `GaussIBP sz0` the only
hypothesis (another gate's pin, S1-19). -/
example (hG : GaussIBP sz0) (x w α : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ∫ ω, sz0.seqHflow 0 (1 / 2) ω w α * lwG sz0 0 lwZ0 (1 / 2) x x ω ∂(Sizes.seqP sz0) =
      lwS sz0 0 (1 / 2) w α *
        ∫ ω, -(lwG sz0 0 lwZ0 (1 / 2) x α ω * lwG sz0 0 lwZ0 (1 / 2) w x ω) ∂(Sizes.seqP sz0) := by
  have h := stein_sample hG (lwG_tame1 (sz := sz0) (n := 0) lwZ0_im (1 / 2) x x) (u := 1 / 2)
    (by norm_num) α w
  simpa only [dhSample_lwG sz0 0 lwZ0_im (by norm_num : (0 : ℝ) < 1 / 2) α w x x] using h

/-- **Item 3 at a concrete off-diagonal pair**: `w = 0`, `α = (32, 0, 0)` (the pair of the `FineModel` check of
`E|X_{wα}|²`), `x = 0`. -/
example (hG : GaussIBP sz0) :
    ∫ ω, sz0.seqHflow 0 (1 / 2) ω 0 ![32, 0, 0] * lwG sz0 0 lwZ0 (1 / 2) 0 0 ω ∂(Sizes.seqP sz0) =
      lwS sz0 0 (1 / 2) 0 ![32, 0, 0] *
        ∫ ω, -(lwG sz0 0 lwZ0 (1 / 2) 0 ![32, 0, 0] ω * lwG sz0 0 lwZ0 (1 / 2) 0 0 ω) ∂(Sizes.seqP sz0) := by
  have h := stein_sample hG (lwG_tame1 (sz := sz0) (n := 0) lwZ0_im (1 / 2) 0 0) (u := 1 / 2)
    (by norm_num) ![32, 0, 0] 0
  simpa only [dhSample_lwG sz0 0 lwZ0_im (by norm_num : (0 : ℝ) < 1 / 2) ![32, 0, 0] 0 0 0] using h

/-- **Item 3 for a resolvent polynomial with a red factor** at `sz0`: `F = |G_{xy}|² = G_{xy} \bar G_{xy}` with
`x = 0`, `y = (32, 0, 0)`, at the pair `(w, α) = (0, 0)`; no tameness hypothesis, `GaussIBP sz0` only. -/
example (hG : GaussIBP sz0) :=
  stein_lwPoly (n := 0) hG lwZ0_im (u := 1 / 2) (by norm_num)
    (MvPolynomial.X (0, ![32, 0, 0], true) * MvPolynomial.X (0, ![32, 0, 0], false)) 0 0

/-- **Item 4 at `sz0`**, `f = G_{xx}`, `df α w = -G_{xα} G_{wx}`: `E Z_w = 0` for the Stein defect of the row `w`. -/
example (hG : GaussIBP sz0) (x w : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ∫ ω, owxDefect lwZ0 (lwGm sz0 0 lwZ0 (1 / 2) ω) (lwS sz0 0 (1 / 2)) (lwG sz0 0 lwZ0 (1 / 2) x x ω)
      (fun α w' => -(lwG sz0 0 lwZ0 (1 / 2) x α ω * lwG sz0 0 lwZ0 (1 / 2) w' x ω)) w ∂(Sizes.seqP sz0) = 0 := by
  have h := integral_owxDefect hG lwZ0_im (u := 1 / 2) (by norm_num)
    (MvPolynomial.X (x, x, true)) w
  simpa only [lwPoly_X_true, dhSample_lwG sz0 0 lwZ0_im (by norm_num : (0 : ℝ) < 1 / 2)] using h

/-- **Item 4, `(Owx)` in expectation, at `sz0`**: `f = G_{xx}`, `u = 1/2`, `m = i/2`, `z = 7i/4`,
`S⁺ = S (1 - m² S)⁻¹`; every deterministic hypothesis is discharged (`m ≠ 0`, `z + u m = -1/m`,
`S⁺ (1 - m² S) = S` from `|m|² u = 1/8 < 1`), `GaussIBP sz0` is the only hypothesis. -/
example (hG : GaussIBP sz0) (x : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ∫ ω, (lwG sz0 0 lwZ0 (1 / 2) x x ω - lwM0) * lwG sz0 0 lwZ0 (1 / 2) x x ω ∂(Sizes.seqP sz0) =
      ∫ ω, (lwM0 * ∑ α, lwS sz0 0 (1 / 2) x α * (lwG sz0 0 lwZ0 (1 / 2) x x ω - lwM0) *
            (lwG sz0 0 lwZ0 (1 / 2) α α ω - lwM0) * lwG sz0 0 lwZ0 (1 / 2) x x ω +
          lwM0 ^ 3 * ∑ α, ∑ β, lwSplus sz0 0 (1 / 2) lwM0 x α * lwS sz0 0 (1 / 2) α β *
            (lwG sz0 0 lwZ0 (1 / 2) α α ω - lwM0) * (lwG sz0 0 lwZ0 (1 / 2) β β ω - lwM0) *
            lwG sz0 0 lwZ0 (1 / 2) x x ω -
          lwM0 * ∑ α, lwS sz0 0 (1 / 2) x α * lwG sz0 0 lwZ0 (1 / 2) α x ω *
            -(lwG sz0 0 lwZ0 (1 / 2) x α ω * lwG sz0 0 lwZ0 (1 / 2) x x ω) -
          lwM0 ^ 3 * ∑ α, ∑ β, lwSplus sz0 0 (1 / 2) lwM0 x α * lwS sz0 0 (1 / 2) α β *
            lwG sz0 0 lwZ0 (1 / 2) β α ω * -(lwG sz0 0 lwZ0 (1 / 2) x β ω * lwG sz0 0 lwZ0 (1 / 2) α x ω))
        ∂(Sizes.seqP sz0) := by
  have h := owx_integral hG lwZ0_im (u := 1 / 2) (by norm_num) lwM0_ne lwM0_hzm
    (lwSplus sz0 0 (1 / 2) lwM0) (lwSplus_spec (by norm_num) lwM0_norm)
    (MvPolynomial.X (x, x, true)) x
  simpa only [lwPoly_X_true, dhSample_lwG sz0 0 lwZ0_im (by norm_num : (0 : ℝ) < 1 / 2)] using h

/-- A two-edge graph: `S_{xa} G_{xa} \bar G_{ay}` (external `x, y`, internal `a`; `n_S = 2`, `n_W = 1`,
`n_V = 1`, the waved edge joins `x` and `a`, so `n_M = 0`). -/
def lwTwoEdge : LGraph (Fin 2) (Fin 1) where
  solid := [⟨true, false, .inl 0, .inr 0⟩, ⟨false, false, .inr 0, .inl 1⟩]
  waved := [⟨false, true, .inl 0, .inr 0⟩]
  dotted := []
  coeff := 1

/-- The counters of `lwTwoEdge`. -/
theorem lwTwoEdge_counters :
    lwTwoEdge.nS = 2 ∧ lwTwoEdge.nW = 1 ∧ lwTwoEdge.nV = 1 ∧ lwTwoEdge.nM = 0 := by decide

/-- The counters of `owxG1`: `n_S = 2`, `n_W = 1`, `n_V = 1`, `n_M = 0`. -/
theorem lwStein_owxG1_counters (m : ℂ) :
    (owxG1 m).nS = 2 ∧ (owxG1 m).nW = 1 ∧ (owxG1 m).nV = 1 ∧ (owxG1 m).nM = 0 := by
  refine ⟨rfl, rfl, by simp [LGraph.nV], ?_⟩
  have : (owxG1 m).nM = (owxG1 0).nM := lwStein_nM_congr _ _ rfl rfl
  rw [this]
  decide

/-- **Item 5 on `owxG1`** (`m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα}`, `d = 3`, `L = 4`, `W = 32`): the derivative of the value
is the sum of the two derivative graphs, each with `n_S = 3`, `n_W = 1`, `n_V = 1`, `n_M = 0`; all hypotheses
discharged (`u = 1/2`, `z = 7i/4`, `M = (i/2) I`, `S = S^{(u)}`, `S⁺`). -/
example (x α w : Idx 3 (sz0.L 0) (sz0.W 0)) (ω : Sizes.SeqΩ sz0) :
    dhSample sz0 0 (1 / 2) α w (fun ω => (owxG1 lwM0).val
        (lwSampleData sz0 0 lwZ0 (1 / 2) (lwM0 • 1) (lwS sz0 0 (1 / 2)) (lwSplus sz0 0 (1 / 2) lwM0) ω)
        (fun _ => x)) ω =
      ((owxG1 lwM0).dTerms.map fun Γ' => Γ'.val
        (lwSampleData sz0 0 lwZ0 (1 / 2) (lwM0 • 1) (lwS sz0 0 (1 / 2)) (lwSplus sz0 0 (1 / 2) lwM0) ω)
        (Sum.elim (fun _ => x) ![α, w])).sum ∧
      (owxG1 lwM0).dTerms.length = 2 ∧
      ∀ Γ' ∈ (owxG1 lwM0).dTerms, Γ'.nS = 3 ∧ Γ'.nW = 1 ∧ Γ'.nV = 1 ∧ Γ'.nM = 0 := by
  refine ⟨dhSample_graphVal lwZ0_im (by norm_num) (owxG1 lwM0) (fun _ => x) α w ω, ?_, ?_⟩
  · rw [LGraph.dTerms_length]; exact (lwStein_owxG1_counters lwM0).1
  · intro Γ' hΓ'
    obtain ⟨h1, h2, h3, h4⟩ := (owxG1 lwM0).dTerms_counters Γ' hΓ'
    obtain ⟨c1, c2, c3, c4⟩ := lwStein_owxG1_counters lwM0
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- **Item 5 on a two-edge graph** `S_{xa} G_{xa} \bar G_{ay}` (here with `d = 3`, `L = 3`, `W = 2`). -/
example (x y α w : Idx 3 (lwSzT.L 0) (lwSzT.W 0)) (ω : Sizes.SeqΩ lwSzT) :
    dhSample lwSzT 0 (7 / 10) α w (fun ω => lwTwoEdge.val
        (lwSampleData lwSzT 0 lwZ (7 / 10) 0 (lwS lwSzT 0 (7 / 10)) 0 ω) ![x, y]) ω =
      (lwTwoEdge.dTerms.map fun Γ' => Γ'.val
        (lwSampleData lwSzT 0 lwZ (7 / 10) 0 (lwS lwSzT 0 (7 / 10)) 0 ω)
        (Sum.elim ![x, y] ![α, w])).sum ∧
      lwTwoEdge.dTerms.length = 2 ∧
      ∀ Γ' ∈ lwTwoEdge.dTerms, Γ'.nS = 3 ∧ Γ'.nW = 1 ∧ Γ'.nV = 1 ∧ Γ'.nM = 0 := by
  refine ⟨dhSample_graphVal lwZ_im (by norm_num) lwTwoEdge ![x, y] α w ω, ?_, ?_⟩
  · rw [LGraph.dTerms_length]; exact lwTwoEdge_counters.1
  · intro Γ' hΓ'
    obtain ⟨h1, h2, h3, h4⟩ := lwTwoEdge.dTerms_counters Γ' hΓ'
    obtain ⟨c1, c2, c3, c4⟩ := lwTwoEdge_counters
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- **Item 5 on the merged `figGraph`** (the left graph of `fig:p=2expansion`, `n_S = 8`, `n_W = 4`, `n_V = 6`,
`n_M = 2`; `d = 3`, `L = 3`, `W = 2`): eight derivative graphs, each with `n_S = 9` and the other counters unchanged. -/
example (x y α w : Idx 3 (lwSzT.L 0) (lwSzT.W 0)) (ω : Sizes.SeqΩ lwSzT) :
    dhSample lwSzT 0 (7 / 10) α w (fun ω => figGraph.val
        (lwSampleData lwSzT 0 lwZ (7 / 10) 0 (lwS lwSzT 0 (7 / 10)) 0 ω) ![x, y]) ω =
      (figGraph.dTerms.map fun Γ' => Γ'.val
        (lwSampleData lwSzT 0 lwZ (7 / 10) 0 (lwS lwSzT 0 (7 / 10)) 0 ω)
        (Sum.elim ![x, y] ![α, w])).sum ∧
      figGraph.dTerms.length = 8 ∧
      ∀ Γ' ∈ figGraph.dTerms, Γ'.nS = 9 ∧ Γ'.nW = 4 ∧ Γ'.nV = 6 ∧ Γ'.nM = 2 := by
  refine ⟨dhSample_graphVal lwZ_im (by norm_num) figGraph ![x, y] α w ω, ?_, ?_⟩
  · rw [LGraph.dTerms_length]; exact figGraph_counters.1
  · intro Γ' hΓ'
    obtain ⟨h1, h2, h3, h4⟩ := figGraph.dTerms_counters Γ' hΓ'
    obtain ⟨c1, c2, c3, c4⟩ := figGraph_counters
    exact ⟨by omega, by omega, by omega, by omega⟩

end Instances

end RBM.Graph

/-! ## Instances of item 1 (probe lines 2033-2112)

The proved weight expansion at `m = i`, `z = 0`, `s = 1`, `S = J/2`, `S⁺ = J/4`, `M = m I`, `G` arbitrary on two
vertices: every deterministic hypothesis is discharged; in `inst_owx_smallest_E` the Stein identity stays a hypothesis
(`GaussIBP`, S1-19), in `inst_owx_smallest_E_unit` it is discharged on the point mass. -/

namespace RBM.Graph.LWInstOwx

open Matrix Complex

/-- `S = J/2`: the rows sum to `1`. -/
def S0 : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- `S⁺ = S (1 - m² S)⁻¹ = J/4` for `m = i` (`m² = -1`). -/
def Sp0 : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 4, 1 / 4; 1 / 4, 1 / 4]

/-- An arbitrary resolvent-like matrix (the identity is algebraic: it holds for every `G`). -/
def G0 : Matrix (Fin 2) (Fin 2) ℂ := !![1 + I, 2; 3 - I, 4]

/-- The data `D₀ = (G₀, M = i·1, S₀, S₀⁺)`. -/
def D0 : LData (Fin 2) := ⟨G0, Matrix.diagonal fun _ => I, S0, Sp0⟩

theorem hS0 : ∀ i, ∑ j, S0 i j = 1 := by
  intro i
  fin_cases i <;> simp [S0, Fin.sum_univ_two] <;> norm_num

theorem hSp0 : ∀ i j, Sp0 i j - I ^ 2 * ∑ w, Sp0 i w * S0 w j = S0 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Sp0, S0, Fin.sum_univ_two] <;> norm_num

theorem hzm0 : (0 : ℂ) + 1 * I = -I⁻¹ := by simp

theorem hM0 : ∀ i j, D0.M i j = if i = j then I else 0 := by
  intro i j
  simp [D0, Matrix.diagonal_apply]

/-- **`(Owx)` for `Ǧ_{xx}`, instantiated** (two vertices, `m = i`, `z = 0`, `s = 1`). -/
theorem inst_owx_smallest (x : Fin 2) :
    owxG0.val D0 (fun _ => x) - ((owxG1 I).val D0 (fun _ => x) + (owxG2 I).val D0 (fun _ => x)) =
      -I * ∑ w, ((if x = w then 1 else 0) + I ^ 2 * D0.Sp x w) *
        owxDefect 0 D0.G D0.S 1 (fun _ _ => 0) w :=
  owx_smallest D0 I 0 1 I_ne_zero hzm0 hM0 hS0 hSp0 x

/-- **`(Owx)` for `Ǧ_{xx} G_{xy}`, instantiated** (four terms, `x = 0`, `y = 1`). -/
theorem inst_owx_second :
    owxH0.val D0 ![0, 1] - ((owxH1 I).val D0 ![0, 1] + (owxH2 I).val D0 ![0, 1] +
        (owxH3 I).val D0 ![0, 1] + (owxH4 I).val D0 ![0, 1]) =
      -I * ∑ w, ((if (0 : Fin 2) = w then 1 else 0) + I ^ 2 * D0.Sp 0 w) *
        owxDefect 0 D0.G D0.S (D0.G 0 1) (fun α w => -(D0.G 0 α * D0.G w 1)) w :=
  owx_second D0 I 0 1 I_ne_zero hzm0 hM0 hS0 hSp0 0 1

/-- **`(Owx)` in expectation, instantiated** on an arbitrary probability space with a random `G`
(any measurable family): the Stein identity `E Z_w = 0` (Gaussian integration by parts, merged
`GaussIBP`, another gate's pin) and the integrability stay hypotheses. -/
theorem inst_owx_smallest_E {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (Gω : Ω → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2)
    (hZint : ∀ w, MeasureTheory.Integrable
      (fun ω => owxDefect 0 (Gω ω) S0 1 (fun _ _ => 0) w) P)
    (hZ : ∀ w, ∫ ω, owxDefect 0 (Gω ω) S0 1 (fun _ _ => 0) w ∂P = 0)
    (h0 : MeasureTheory.Integrable (fun ω => owxG0.val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x)) P)
    (h1 : MeasureTheory.Integrable (fun ω => (owxG1 I).val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x)) P)
    (h2 : MeasureTheory.Integrable (fun ω => (owxG2 I).val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x)) P) :
    ∫ ω, owxG0.val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x) ∂P =
      ∫ ω, (owxG1 I).val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x) ∂P +
        ∫ ω, (owxG2 I).val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x) ∂P :=
  owx_smallest_E P (fun ω => ⟨Gω ω, D0.M, S0, Sp0⟩) I 0 1 Sp0 I_ne_zero hzm0
    (fun _ => hM0) (fun _ => hS0) (fun _ => hSp0) (fun _ => rfl) x hZint hZ h0 h1 h2

/-- At `G = M = i·1` the Stein defect of every row vanishes. -/
theorem owxDefect_M0 (w : Fin 2) :
    owxDefect 0 (Matrix.diagonal fun _ => I) S0 1 (fun _ _ => 0) w = 0 := by
  fin_cases w <;> simp [owxDefect, S0, Fin.sum_univ_two, Matrix.diagonal_apply] <;> ring_nf <;> simp

/-- **`(Owx)` in expectation at a fully concrete point** (`Ω = Unit` with the point mass, `G = M`):
every hypothesis, the Stein identity included, is discharged. -/
theorem inst_owx_smallest_E_unit (x : Fin 2) :
    ∫ _ : Unit, owxG0.val ⟨Matrix.diagonal fun _ => I, D0.M, S0, Sp0⟩ (fun _ => x)
        ∂(MeasureTheory.Measure.dirac ()) =
      ∫ _ : Unit, (owxG1 I).val ⟨Matrix.diagonal fun _ => I, D0.M, S0, Sp0⟩ (fun _ => x)
          ∂(MeasureTheory.Measure.dirac ()) +
        ∫ _ : Unit, (owxG2 I).val ⟨Matrix.diagonal fun _ => I, D0.M, S0, Sp0⟩ (fun _ => x)
          ∂(MeasureTheory.Measure.dirac ()) :=
  inst_owx_smallest_E (MeasureTheory.Measure.dirac ()) (fun _ => Matrix.diagonal fun _ => I) x
    (fun w => MeasureTheory.integrable_const _) (fun w => by simp [owxDefect_M0])
    (MeasureTheory.integrable_const _) (MeasureTheory.integrable_const _)
    (MeasureTheory.integrable_const _)

end RBM.Graph.LWInstOwx
