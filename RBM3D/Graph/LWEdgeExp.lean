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
# LW-06: the edge expansion `(Oe1x)` (T2119)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:309-330` (`7_8:309-330`, lemma `Oe14`,
cited from `[yang2021]` Lemma 3.10).  Design: T2040 (split row LW-06).

## Contents (namespace `RBM.Graph`)

1. **The Stein step for `G_{xy} f`** (`oe1x_integral`, on the sequence space): for every
   `C¹`-tame `f` (resolvent polynomials, products of edge factors),
   `E[G_{xy} f] = E[m δ_{xy} f + m (Σ_α S_{xα} Ǧ_{αα}) G_{xy} f - m Σ_α S_{xα} G_{αy} ∂_{h_{αx}} f]`
   (no `S⁺`: the term `t m² G_{xy} f` of the resolvent identity cancels against
   `m² Σ_α S_{xα} G_{xy} f` from the derivative of `G_{αy}`).
   `oe1x_resolvent_id`: `Σ_α H_{xα} G_{αy} = δ_{xy} + z G_{xy}`.
2. **The derivative of the rest** `𝒢/(G_{xy₁} f)` (`oe1xR`, `oe1x_dh_R`) and **the pin**
   `lwEdgeExp_holds : ∀ d, LWedgeExp d` (`Graph/LWPins.lean:131`): the nine terms of `(Oe1x)`, from
   `oe1x_integral` with `f := rest · f` through the bridge of T2107 (`lwWx_*`); `t = 0` separately.
3. **`(Oe1x)` as a graph operation**: for a graph `Γ` with a blue solid edge `e₀ = G_{xy₁}` out of
   the internal vertex `x` (`p ∈ lwSplit Γ.solid`, `p.1 = e₀`, `p.2` the other solid edges: the rest
   and `f`): `oe1xT1` (`m 1_{x = y₁}`, `x` merged into `y₁`), `owxT1` (T2107:
   `m Σ_α S_{xα} Ǧ_{αα} Γ`), and for every solid edge `q` of `p.2` the derivative graph `oe1xD`
   (`-m Σ_α S_{xα} G_{αy₁} ∂_{h_{αx}}` on `q`), refined for the red out-edges and the blue in-edges
   of `x` into `oe1xP5`, `oe1xP3` and `oe1xP6`, `oe1xP4` (`Ḡ_{xx} = Ǧ_{xx} + m̄`,
   `G_{xx} = Ǧ_{xx} + m`; the list `oe1xDs`).  `oe1x_graph_E`: the identity of expectations
   of values; `oe1x*_counters`, `oe1x*_ord`: the changes of `n_S, n_W, n_V, n_M` and of `ord`.
4. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`.
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

/-! ## 1. The Stein step for `G_{xy} f` -/

section OeInt

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- Closure of `Tame` under the operations of the expansion (copy of the local macro of
`Graph/LWStein.lean`, which is not exported). -/
local macro "oe1x_tame" : tactic =>
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

/-- The resolvent identity `Σ_α H_{xα} G_{αy} = δ_{xy} + z G_{xy}` (the diagonal case is
`lwStein_resolvent_id`). -/
theorem oe1x_resolvent_id {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ∑ α, sz.seqHflow n u ω x α * lwG sz n z u α y ω =
      (if x = y then 1 else 0) + z * lwG sz n z u x y ω := by
  have hU : IsUnit (sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    isUnit_sub_smul_of_isHermitian (Sizes.seqHflow_isHermitian sz n u ω) hz
  have h : ((sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
      Ring.inverse (sz.seqHflow n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))) x y =
      (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) x y := by
    rw [Ring.mul_inverse_cancel _ hU]
  simp only [lwG, lwGm, Gres, ite_true]
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at h
  linear_combination h

/-- The integrand of `oe1x_integral` is tame (continuous), for a `C¹`-tame `f`. -/
theorem oe1x_rhs_tame {z : ℂ} (hz : 0 < z.im) {u : ℝ} (m : ℂ)
    {f : Sizes.SeqΩ sz → ℂ} (hf : Tame1 sz n f) (x y : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => m * (if x = y then 1 else 0) * f ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * f ω) -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * dhSample sz n u α x f ω) := by
  have hz' : z.im ≠ 0 := hz.ne'
  have tf : Tame sz f := hf.tame
  have tD : ∀ α β : Idx d (sz.L n) (sz.W n), Tame sz (dhSample sz n u α β f) :=
    fun α β => lwStein_tame_dhSample hf u α β
  oe1x_tame

/-- **`(Oe1x)` for a general resolvent polynomial `f`** (`7_8:309-330`): the Stein step for `G_{xy} f`.
`E[G_{xy} f] = E[m δ_{xy} f + m (Σ_α S_{xα} Ǧ_{αα}) G_{xy} f - m Σ_α S_{xα} G_{αy} ∂_{h_{αx}} f]`,
`Ǧ = G - m`, `S = u · svarF`, for every `C¹`-tame `f` (resolvent polynomials, products of edge factors).  Hypotheses: `GaussIBP sz` (proved: `gaussIBP sz`), `Im z > 0`, `u > 0`,
`m ≠ 0`, `z + u m = -m⁻¹`.  No `S⁺`. -/
theorem oe1x_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    {f : Sizes.SeqΩ sz → ℂ} (hf : Tame1 sz n f)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, lwG sz n z u x y ω * f ω ∂(Sizes.seqP sz) =
      ∫ ω, (m * (if x = y then 1 else 0) * f ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * f ω) -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * dhSample sz n u α x f ω)
        ∂(Sizes.seqP sz) := by
  classical
  have hz' : z.im ≠ 0 := hz.ne'
  have tf : Tame sz f := hf.tame
  have tD : ∀ α β : Idx d (sz.L n) (sz.W n), Tame sz (dhSample sz n u α β f) :=
    fun α β => lwStein_tame_dhSample hf u α β
  have hF : ∀ α : Idx d (sz.L n) (sz.W n),
      Tame1 sz n (fun ω => lwG sz n z u α y ω * f ω) :=
    fun α => (lwG_tame1 hz u α y).mul hf
  have hdF : ∀ (α : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
      dhSample sz n u α x (fun ω => lwG sz n z u α y ω * f ω) ω =
        -(lwG sz n z u α α ω * lwG sz n z u x y ω) * f ω +
          lwG sz n z u α y ω * dhSample sz n u α x f ω := by
    intro α ω
    rw [lwStein_dh_mul (lwG_tame1 hz u α y) hf, dhSample_lwG sz n hz hu]
  -- the Stein defect `Z = Σ_α (H_{xα} F_α - S_{xα} ∂_{h_{αx}} F_α)`
  have iA : ∀ α : Idx d (sz.L n) (sz.W n), Integrable (fun ω => sz.seqHflow n u ω x α *
      (lwG sz n z u α y ω * f ω)) (Sizes.seqP sz) := fun α =>
    Tame.integrable hG ((lwStein_tame_hflow sz n u x α).mul (hF α).tame)
  have iB : ∀ α : Idx d (sz.L n) (sz.W n), Integrable (fun ω => lwS sz n u x α *
      dhSample sz n u α x (fun ω => lwG sz n z u α y ω * f ω) ω) (Sizes.seqP sz) :=
    fun α => Tame.integrable hG ((Tame.const _).mul (lwStein_tame_dhSample (hF α) u α x))
  have hZ : ∫ ω, (∑ α, sz.seqHflow n u ω x α * (lwG sz n z u α y ω * f ω) -
      ∑ α, lwS sz n u x α *
        dhSample sz n u α x (fun ω => lwG sz n z u α y ω * f ω) ω) ∂(Sizes.seqP sz) = 0 := by
    rw [integral_sub (integrable_finsetSum _ fun α _ => iA α) (integrable_finsetSum _ fun α _ => iB α),
      integral_finsetSum _ fun α _ => iA α, integral_finsetSum _ fun α _ => iB α,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [integral_const_mul]
    have := stein_sample hG (hF α) hu.le α x
    rw [this]
    simp [lwS]
  have hpt : ∀ ω : Sizes.SeqΩ sz,
      lwG sz n z u x y ω * f ω -
        (m * (if x = y then 1 else 0) * f ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * f ω) -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * dhSample sz n u α x f ω) =
      -m * (∑ α, sz.seqHflow n u ω x α * (lwG sz n z u α y ω * f ω) -
        ∑ α, lwS sz n u x α *
          dhSample sz n u α x (fun ω => lwG sz n z u α y ω * f ω) ω) := by
    intro ω
    have hres := oe1x_resolvent_id (sz := sz) (n := n) hz' u ω x y
    have h1 : ∑ α, sz.seqHflow n u ω x α * (lwG sz n z u α y ω * f ω) =
        ((if x = y then 1 else 0) + z * lwG sz n z u x y ω) * f ω := by
      rw [← hres, Finset.sum_mul]
      exact Finset.sum_congr rfl fun α _ => by ring
    have h2 : ∑ α, lwS sz n u x α *
          dhSample sz n u α x (fun ω => lwG sz n z u α y ω * f ω) ω =
        -((∑ α, lwS sz n u x α * lwG sz n z u α α ω) * lwG sz n z u x y ω * f ω) +
          ∑ α, lwS sz n u x α * lwG sz n z u α y ω * dhSample sz n u α x f ω := by
      simp only [hdF, mul_add, Finset.sum_add_distrib, Finset.sum_mul, ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun α _ => by ring
      · exact Finset.sum_congr rfl fun α _ => by ring
    have hS : ∑ α, lwS sz n u x α = (u : ℂ) := lwS_row_sum u x
    have hsplit : ∑ α, lwS sz n u x α * lwG sz n z u α α ω =
        (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) + (u : ℂ) * m := by
      rw [← hS, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hz2 : z = -m⁻¹ - u * m := by linear_combination hzm
    rw [h1, h2, hsplit, hz2]
    field_simp
    ring
  have iL : Integrable (fun ω => lwG sz n z u x y ω * f ω) (Sizes.seqP sz) := by
    refine Tame.integrable hG ?_
    oe1x_tame
  have iR : Integrable (fun ω => (m * (if x = y then 1 else 0) * f ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * f ω) -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * dhSample sz n u α x f ω))
      (Sizes.seqP sz) := by
    refine Tame.integrable hG ?_
    oe1x_tame
  have hzero : ∫ ω, (lwG sz n z u x y ω * f ω -
        (m * (if x = y then 1 else 0) * f ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * f ω) -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * dhSample sz n u α x f ω))
      ∂(Sizes.seqP sz) = 0 := by
    simp_rw [hpt]
    rw [integral_const_mul, hZ, mul_zero]
  rw [integral_sub iL iR] at hzero
  linear_combination hzero


/-! ### Finite products: tameness and the Leibniz rule -/

/-- A finite product of `C¹`-tame functions is `C¹`-tame. -/
theorem oe1x_tame1_finprod {κ : Type*} (s : Finset κ) {F : κ → Sizes.SeqΩ sz → ℂ}
    (h : ∀ i ∈ s, Tame1 sz n (F i)) : Tame1 sz n (fun ω => ∏ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Tame1.const (sz := sz) (n := n) 1
  | insert i₀ s hi₀ ih =>
    have h₀ := h i₀ (Finset.mem_insert_self _ _)
    have hs := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.prod_insert hi₀] using h₀.mul hs

/-- **The Leibniz rule for `∂_{h_{αw}}` on a finite product**: the sum over the factors of the derivative
of one factor times the product of the others. -/
theorem oe1x_dh_finprod {κ : Type*} [DecidableEq κ] (s : Finset κ) {F : κ → Sizes.SeqΩ sz → ℂ}
    (h : ∀ i ∈ s, Tame1 sz n (F i)) {u : ℝ} {α w : Idx d (sz.L n) (sz.W n)} (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => ∏ i ∈ s, F i ω) ω =
      ∑ i ∈ s, dhSample sz n u α w (F i) ω * ∏ j ∈ s.erase i, F j ω := by
  induction s using Finset.induction with
  | empty => simpa using lwStein_dh_const (sz := sz) (n := n) (u := u) (α := α) (w := w) 1 ω
  | insert i₀ s hi₀ ih =>
    have h₀ := h i₀ (Finset.mem_insert_self _ _)
    have hs := oe1x_tame1_finprod s fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ih' := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have e : (fun ω => ∏ i ∈ insert i₀ s, F i ω) = fun ω => F i₀ ω * ∏ i ∈ s, F i ω := by
      funext ω'; rw [Finset.prod_insert hi₀]
    rw [e, lwStein_dh_mul h₀ hs, ih', Finset.sum_insert hi₀, Finset.erase_insert hi₀]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i ≠ i₀ := fun e' => hi₀ (e' ▸ hi)
    rw [Finset.erase_insert_of_ne (Ne.symm hne), Finset.prod_insert (fun hm => hi₀ (Finset.mem_of_mem_erase hm))]
    ring

/-! ### The rest `𝒢 / (G_{xy₁} f)` of `(Oe1x)` and its derivative -/

variable (z : ℂ) (u : ℝ) {k₁ k₂ k₃ k₄ : ℕ}

/-- The product `𝒢 / (G_{xy₁} f)` of `(Oe1x)` (`7_8:312`) at the sample (the sequence-space form of
`LWPins_oe1xRest`): `k₁` further blue out-edges `G_{xy_i}`, the red out-edges `Ḡ_{xy'_i}` for `i ∈ s₂`, the blue
in-edges `G_{w_i x}` for `i ∈ s₃`, all `k₄` red in-edges `Ḡ_{w'_i x}`. -/
def oe1xR (x : Idx d (sz.L n) (sz.W n)) (y : Fin (k₁ + 1) → Idx d (sz.L n) (sz.W n))
    (y' : Fin k₂ → Idx d (sz.L n) (sz.W n)) (w : Fin k₃ → Idx d (sz.L n) (sz.W n))
    (w' : Fin k₄ → Idx d (sz.L n) (sz.W n)) (s₂ : Finset (Fin k₂)) (s₃ : Finset (Fin k₃))
    (ω : Sizes.SeqΩ sz) : ℂ :=
  (∏ i : Fin k₁, lwG sz n z u x (y i.succ) ω) * (∏ i ∈ s₂, star (lwG sz n z u x (y' i) ω)) *
    (∏ i ∈ s₃, lwG sz n z u (w i) x ω) * (∏ i : Fin k₄, star (lwG sz n z u (w' i) x ω))

variable {z u}

/-- The rest is `C¹`-tame. -/
theorem oe1xR_tame1 (hz : 0 < z.im) (x : Idx d (sz.L n) (sz.W n)) (y : Fin (k₁ + 1) → Idx d (sz.L n) (sz.W n))
    (y' : Fin k₂ → Idx d (sz.L n) (sz.W n)) (w : Fin k₃ → Idx d (sz.L n) (sz.W n))
    (w' : Fin k₄ → Idx d (sz.L n) (sz.W n)) (s₂ : Finset (Fin k₂)) (s₃ : Finset (Fin k₃)) :
    Tame1 sz n (oe1xR (sz := sz) (n := n) z u x y y' w w' s₂ s₃) := by
  unfold oe1xR
  refine (((oe1x_tame1_finprod _ fun i _ => lwG_tame1 hz u x (y i.succ)).mul
    (oe1x_tame1_finprod _ fun i _ => (lwG_tame1 hz u x (y' i)).conj)).mul
    (oe1x_tame1_finprod _ fun i _ => lwG_tame1 hz u (w i) x)).mul
    (oe1x_tame1_finprod _ fun i _ => (lwG_tame1 hz u (w' i) x).conj)

/-- **The derivative of the rest** (`∂_{h_{αx}}`, `7_8:313-319`): `∂_{h_{αx}} G_{xy_i} = -G_{xα} G_{xy_i}`,
`∂ Ḡ_{xy'_i} = -Ḡ_{xx} Ḡ_{αy'_i}`, `∂ G_{w_i x} = -G_{w_i α} G_{xx}`, `∂ Ḡ_{w'_i x} = -Ḡ_{αx} Ḡ_{w'_i x}`:
the factors that are not differentiated stay, so the first and the last group give `k₁`, `k₄` times the rest. -/
theorem oe1x_dh_R [DecidableEq (Idx d (sz.L n) (sz.W n))] (hz : 0 < z.im) (hu : 0 < u)
    (x : Idx d (sz.L n) (sz.W n)) (y : Fin (k₁ + 1) → Idx d (sz.L n) (sz.W n))
    (y' : Fin k₂ → Idx d (sz.L n) (sz.W n)) (w : Fin k₃ → Idx d (sz.L n) (sz.W n))
    (w' : Fin k₄ → Idx d (sz.L n) (sz.W n)) (s₂ : Finset (Fin k₂)) (s₃ : Finset (Fin k₃))
    (α : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α x (oe1xR (sz := sz) (n := n) z u x y y' w w' s₂ s₃) ω =
      -((k₁ : ℂ) * lwG sz n z u x α ω * oe1xR z u x y y' w w' s₂ s₃ ω) -
        ∑ i ∈ s₂, star (lwG sz n z u x x ω) * star (lwG sz n z u α (y' i) ω) *
          oe1xR z u x y y' w w' (s₂.erase i) s₃ ω -
        ∑ i ∈ s₃, lwG sz n z u (w i) α ω * lwG sz n z u x x ω *
          oe1xR z u x y y' w w' s₂ (s₃.erase i) ω -
        (k₄ : ℂ) * star (lwG sz n z u α x ω) * oe1xR z u x y y' w w' s₂ s₃ ω := by
  set A : Sizes.SeqΩ sz → ℂ := fun ω => ∏ i : Fin k₁, lwG sz n z u x (y i.succ) ω with hA
  set B : Finset (Fin k₂) → Sizes.SeqΩ sz → ℂ := fun s ω => ∏ i ∈ s, star (lwG sz n z u x (y' i) ω) with hB
  set C : Finset (Fin k₃) → Sizes.SeqΩ sz → ℂ := fun s ω => ∏ i ∈ s, lwG sz n z u (w i) x ω with hC
  set D : Sizes.SeqΩ sz → ℂ := fun ω => ∏ i : Fin k₄, star (lwG sz n z u (w' i) x ω) with hD
  have tA : Tame1 sz n A := oe1x_tame1_finprod _ fun i _ => lwG_tame1 hz u x (y i.succ)
  have tB : Tame1 sz n (B s₂) := oe1x_tame1_finprod _ fun i _ => (lwG_tame1 hz u x (y' i)).conj
  have tC : Tame1 sz n (C s₃) := oe1x_tame1_finprod _ fun i _ => lwG_tame1 hz u (w i) x
  have tD : Tame1 sz n D := oe1x_tame1_finprod _ fun i _ => (lwG_tame1 hz u (w' i) x).conj
  have hR : oe1xR (sz := sz) (n := n) z u x y y' w w' s₂ s₃ =
      fun ω => A ω * B s₂ ω * C s₃ ω * D ω := rfl
  -- the four group derivatives
  have dA : dhSample sz n u α x A ω = -((k₁ : ℂ) * lwG sz n z u x α ω * A ω) := by
    rw [hA, oe1x_dh_finprod _ fun i _ => lwG_tame1 hz u x (y i.succ)]
    simp only [dhSample_lwG sz n hz hu]
    have : ∀ i : Fin k₁, -(lwG sz n z u x α ω * lwG sz n z u x (y i.succ) ω) *
        ∏ j ∈ Finset.univ.erase i, lwG sz n z u x (y j.succ) ω =
        -(lwG sz n z u x α ω * ∏ j : Fin k₁, lwG sz n z u x (y j.succ) ω) := by
      intro i
      rw [← Finset.mul_prod_erase Finset.univ (fun j => lwG sz n z u x (y j.succ) ω) (Finset.mem_univ i)]
      ring
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have dB : dhSample sz n u α x (B s₂) ω =
      -∑ i ∈ s₂, star (lwG sz n z u x x ω) * star (lwG sz n z u α (y' i) ω) * B (s₂.erase i) ω := by
    rw [hB, oe1x_dh_finprod _ fun i _ => (lwG_tame1 hz u x (y' i)).conj, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dhSample_lwG_star sz n hz hu, star_mul']
    ring
  have dC : dhSample sz n u α x (C s₃) ω =
      -∑ i ∈ s₃, lwG sz n z u (w i) α ω * lwG sz n z u x x ω * C (s₃.erase i) ω := by
    rw [hC, oe1x_dh_finprod _ fun i _ => lwG_tame1 hz u (w i) x, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dhSample_lwG sz n hz hu]
    ring
  have dD : dhSample sz n u α x D ω = -((k₄ : ℂ) * star (lwG sz n z u α x ω) * D ω) := by
    rw [hD, oe1x_dh_finprod _ fun i _ => (lwG_tame1 hz u (w' i) x).conj]
    simp only [dhSample_lwG_star sz n hz hu, star_mul']
    have : ∀ i : Fin k₄, -(star (lwG sz n z u (w' i) x ω) * star (lwG sz n z u α x ω)) *
        ∏ j ∈ Finset.univ.erase i, star (lwG sz n z u (w' j) x ω) =
        -(star (lwG sz n z u α x ω) * ∏ j : Fin k₄, star (lwG sz n z u (w' j) x ω)) := by
      intro i
      rw [← Finset.mul_prod_erase Finset.univ (fun j => star (lwG sz n z u (w' j) x ω)) (Finset.mem_univ i)]
      ring
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hABC : Tame1 sz n (fun ω => A ω * B s₂ ω * C s₃ ω) := (tA.mul tB).mul tC
  have hAB : Tame1 sz n (fun ω => A ω * B s₂ ω) := tA.mul tB
  have hRω : ∀ (s₂' : Finset (Fin k₂)) (s₃' : Finset (Fin k₃)),
      oe1xR (sz := sz) (n := n) z u x y y' w w' s₂' s₃' ω = A ω * B s₂' ω * C s₃' ω * D ω := fun _ _ => rfl
  have e2 : A ω * (∑ i ∈ s₂, star (lwG sz n z u x x ω) * star (lwG sz n z u α (y' i) ω) * B (s₂.erase i) ω) *
      C s₃ ω * D ω = ∑ i ∈ s₂, star (lwG sz n z u x x ω) * star (lwG sz n z u α (y' i) ω) *
        oe1xR (sz := sz) (n := n) z u x y y' w w' (s₂.erase i) s₃ ω := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hRω]
    ring
  have e3 : A ω * B s₂ ω * (∑ i ∈ s₃, lwG sz n z u (w i) α ω * lwG sz n z u x x ω * C (s₃.erase i) ω) *
      D ω = ∑ i ∈ s₃, lwG sz n z u (w i) α ω * lwG sz n z u x x ω *
        oe1xR (sz := sz) (n := n) z u x y y' w w' s₂ (s₃.erase i) ω := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hRω]
    ring
  change dhSample sz n u α x (fun ω => A ω * B s₂ ω * C s₃ ω * D ω) ω = _
  rw [lwStein_dh_mul hABC tD, lwStein_dh_mul hAB tC, lwStein_dh_mul tA tB, dA, dB, dC, dD, hRω s₂ s₃]
  linear_combination (-1 : ℂ) * e2 + (-1 : ℂ) * e3


/-! ### The nine terms: the algebra of the pointwise identity -/

/-- **The nine terms of `(Oe1x)`, pointwise** (pure algebra): the Stein step `oe1x_integral` for `f := rest · f`,
with the derivative of the rest of `oe1x_dh_R` inserted (`Ḡ_{xx} = Ǧ̄_{xx} + m̄`, `G_{xx} = Ǧ_{xx} + m`), is the sum
of the nine terms of the pin `LWedgeExp` (`7_8:316-319`).  `Sx α = S_{xα}`, `Gxy0 = G_{xy₁}`, `Gαy0 α = G_{αy₁}`,
`R, R2 i, R3 i` the rest and the rests with the `i`-th red out-edge (blue in-edge) removed. -/
theorem oe1x_pointwise {ι : Type*} [Fintype ι] {k₁ k₂ k₃ k₄ : ℕ} (m δ Gxy0 Gxx R f : ℂ)
    (Sx Gaa Gay0 Gxa Gax : ι → ℂ) (Gay' : ι → Fin k₂ → ℂ) (Gwa : Fin k₃ → ι → ℂ)
    (R2 : Fin k₂ → ℂ) (R3 : Fin k₃ → ℂ) (df : ι → ℂ) :
    m * δ * (R * f) + m * (∑ α, Sx α * (Gaa α - m)) * (Gxy0 * (R * f)) -
        m * ∑ α, Sx α * Gay0 α *
          ((-((k₁ : ℂ) * Gxa α * R) - ∑ i, star Gxx * star (Gay' α i) * R2 i -
              ∑ i, Gwa i α * Gxx * R3 i - (k₄ : ℂ) * star (Gax α) * R) * f + R * df α) =
      m * δ * (R * f) + m * (∑ α, Sx α * (Gaa α - m)) * (Gxy0 * (R * f)) +
        ∑ i, (m * star m) * (∑ α, Sx α * Gay0 α * star (Gay' α i)) * (R2 i * f) +
        ∑ i, m ^ 2 * (∑ α, Sx α * Gay0 α * Gwa i α) * (R3 i * f) +
        ∑ i, m * star (Gxx - m) * (∑ α, Sx α * Gay0 α * star (Gay' α i)) * (R2 i * f) +
        ∑ i, m * (Gxx - m) * (∑ α, Sx α * Gay0 α * Gwa i α) * (R3 i * f) +
        (k₁ : ℂ) * m * (∑ α, Sx α * Gxa α * Gay0 α) * (R * f) +
        (k₄ : ℂ) * m * (∑ α, Sx α * star (Gax α) * Gay0 α) * (R * f) -
        m * ∑ α, Sx α * R * Gay0 α * df α := by
  have h1 : ∑ α, Sx α * Gay0 α * (-((k₁ : ℂ) * Gxa α * R) * f) =
      -((k₁ : ℂ) * (∑ α, Sx α * Gxa α * Gay0 α) * (R * f)) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun α _ => by ring
  have h4 : ∑ α, Sx α * Gay0 α * (-((k₄ : ℂ) * star (Gax α) * R) * f) =
      -((k₄ : ℂ) * (∑ α, Sx α * star (Gax α) * Gay0 α) * (R * f)) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun α _ => by ring
  have h2 : ∑ α, Sx α * Gay0 α * (-(∑ i, star Gxx * star (Gay' α i) * R2 i) * f) =
      -(star Gxx * ∑ i, (∑ α, Sx α * Gay0 α * star (Gay' α i)) * (R2 i * f)) := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring
  have h3 : ∑ α, Sx α * Gay0 α * (-(∑ i, Gwa i α * Gxx * R3 i) * f) =
      -(Gxx * ∑ i, (∑ α, Sx α * Gay0 α * Gwa i α) * (R3 i * f)) := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring
  have h5 : ∑ α, Sx α * Gay0 α * (R * df α) = ∑ α, Sx α * R * Gay0 α * df α :=
    Finset.sum_congr rfl fun α _ => by ring
  have hsum : ∀ α, Sx α * Gay0 α * ((-((k₁ : ℂ) * Gxa α * R) - ∑ i, star Gxx * star (Gay' α i) * R2 i -
      ∑ i, Gwa i α * Gxx * R3 i - (k₄ : ℂ) * star (Gax α) * R) * f + R * df α) =
      Sx α * Gay0 α * (-((k₁ : ℂ) * Gxa α * R) * f) -
        Sx α * Gay0 α * ((∑ i, star Gxx * star (Gay' α i) * R2 i) * f) -
        Sx α * Gay0 α * ((∑ i, Gwa i α * Gxx * R3 i) * f) +
        Sx α * Gay0 α * (-((k₄ : ℂ) * star (Gax α) * R) * f) + Sx α * Gay0 α * (R * df α) := by
    intro α; ring
  have h2' : ∑ α, Sx α * Gay0 α * ((∑ i, star Gxx * star (Gay' α i) * R2 i) * f) =
      star Gxx * ∑ i, (∑ α, Sx α * Gay0 α * star (Gay' α i)) * (R2 i * f) := by
    have := h2
    rw [show ∑ α, Sx α * Gay0 α * (-(∑ i, star Gxx * star (Gay' α i) * R2 i) * f) =
      -∑ α, Sx α * Gay0 α * ((∑ i, star Gxx * star (Gay' α i) * R2 i) * f) from by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun α _ => by ring] at this
    linear_combination -this
  have h3' : ∑ α, Sx α * Gay0 α * ((∑ i, Gwa i α * Gxx * R3 i) * f) =
      Gxx * ∑ i, (∑ α, Sx α * Gay0 α * Gwa i α) * (R3 i * f) := by
    have := h3
    rw [show ∑ α, Sx α * Gay0 α * (-(∑ i, Gwa i α * Gxx * R3 i) * f) =
      -∑ α, Sx α * Gay0 α * ((∑ i, Gwa i α * Gxx * R3 i) * f) from by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun α _ => by ring] at this
    linear_combination -this
  simp only [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h4, h2', h3', h5]
  have e1 : ∑ i, (m * star m) * (∑ α, Sx α * Gay0 α * star (Gay' α i)) * (R2 i * f) +
        ∑ i, m * star (Gxx - m) * (∑ α, Sx α * Gay0 α * star (Gay' α i)) * (R2 i * f) =
      m * star Gxx * ∑ i, (∑ α, Sx α * Gay0 α * star (Gay' α i)) * (R2 i * f) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sub]; ring
  have e2 : ∑ i, m ^ 2 * (∑ α, Sx α * Gay0 α * Gwa i α) * (R3 i * f) +
        ∑ i, m * (Gxx - m) * (∑ α, Sx α * Gay0 α * Gwa i α) * (R3 i * f) =
      m * Gxx * ∑ i, (∑ α, Sx α * Gay0 α * Gwa i α) * (R3 i * f) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  linear_combination (-1 : ℂ) * e1 + (-1 : ℂ) * e2

end OeInt

/-! ## 2. The pin `LWedgeExp` on `PF d L W g` -/

section PinProof

local macro "oe1x_tame" : tactic =>
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

/-- **`t = 0`**: `H_0 = 0`, `z_0 = E + m = -m⁻¹`, `G = m I`: `G_{ab} = m δ_{ab}`. -/
theorem oe1x_lwG_zero {E : ℝ} (hE : |E| < 2) {d L W : ℕ} [NeZero L] [NeZero W] (ω : Ω d L W)
    (a b : Idx d L W) : LWPins_lwG d L W E 0 ω a b = if a = b then mE E else 0 := by
  have hm0 : mE E ≠ 0 := lwWx_mE_ne E hE
  have hz : zt E 0 = -(mE E)⁻¹ := by
    have hm := mE_mul hE.le
    simp only [zt, Complex.ofReal_zero, sub_zero, one_mul]
    field_simp
    linear_combination hm
  have hH : Hflow d L W 0 ω = 0 := by
    simp [Hflow]
  have hz0 : zt E 0 ≠ 0 := by
    rw [hz]; exact neg_ne_zero.2 (inv_ne_zero hm0)
  have hG : Gres (Hflow d L W 0 ω) (zt E 0) true = mE E • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
    rw [hH, lwWx_gres_zero hz0, hz, neg_neg, inv_inv]
  simp [LWPins_lwG, hG, Matrix.one_apply]


/-- The rest of the pin at a sample of the one-size law is `oe1xR` at the sample of the sequence space. -/
theorem oe1x_rest_eq {d L W : ℕ} [NeZero L] [NeZero W] {g : ℝ} (hL : 3 ≤ L) (E t : ℝ)
    (ω' : Sizes.SeqΩ (lwWxSizes d L W g hL)) {k₁ k₂ k₃ k₄ : ℕ} (x : Idx d L W)
    (y : Fin (k₁ + 1) → Idx d L W) (y' : Fin k₂ → Idx d L W) (w : Fin k₃ → Idx d L W)
    (w' : Fin k₄ → Idx d L W) (s₂ : Finset (Fin k₂)) (s₃ : Finset (Fin k₃)) :
    LWPins_oe1xRest d L W E t (Sizes.slice (lwWxSizes d L W g hL) 0 ω') x y y' w w' s₂ s₃ =
      oe1xR (sz := lwWxSizes d L W g hL) (n := 0) (zt E t) t x y y' w w' s₂ s₃ ω' := rfl

/-- **`(Oe1x)` for `0 < t < 1`**: the pin `LWedgeExp` (every `d`, `g`, `L ≥ 3`, `W ≥ 1`, `|E| < 2`), through the
bridge of T2107 and `oe1x_integral` with `f := rest · f`. -/
theorem oe1x_pin_pos {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (g E t : ℝ) (hE : |E| < 2) (ht : 0 < t)
    (ht1 : t < 1) (k₁ k₂ k₃ k₄ : ℕ) (x : Idx d L W) (y : Fin (k₁ + 1) → Idx d L W) (y' : Fin k₂ → Idx d L W)
    (w : Fin k₃ → Idx d L W) (w' : Fin k₄ → Idx d L W) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    ∫ ω, LWPins_lwG d L W E t ω x (y 0) * (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
          LWPins_lwf d L W E t P ω) ∂(PF d L W g) =
        ∫ ω, (mE E * (if x = y 0 then 1 else 0) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * LWPins_lwf d L W E t P ω) +
          mE E * (∑ α, LWPins_lwS d L W g t x α * LWPins_lwGc d L W E t ω α α) *
            (LWPins_lwG d L W E t ω x (y 0) * (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
              LWPins_lwf d L W E t P ω)) +
          ∑ i : Fin k₂, (mE E * star (mE E)) *
            (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α (y 0) * LWPins_lwGb d L W E t ω α (y' i)) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' (Finset.univ.erase i) Finset.univ * LWPins_lwf d L W E t P ω) +
          ∑ i : Fin k₃, mE E ^ 2 *
            (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α (y 0) * LWPins_lwG d L W E t ω (w i) α) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ (Finset.univ.erase i) * LWPins_lwf d L W E t P ω) +
          ∑ i : Fin k₂, mE E * LWPins_lwGcb d L W E t ω x x *
            (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α (y 0) * LWPins_lwGb d L W E t ω α (y' i)) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' (Finset.univ.erase i) Finset.univ * LWPins_lwf d L W E t P ω) +
          ∑ i : Fin k₃, mE E * LWPins_lwGc d L W E t ω x x *
            (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α (y 0) * LWPins_lwG d L W E t ω (w i) α) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ (Finset.univ.erase i) * LWPins_lwf d L W E t P ω) +
          (k₁ : ℂ) * mE E * (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω x α * LWPins_lwG d L W E t ω α (y 0)) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * LWPins_lwf d L W E t P ω) +
          (k₄ : ℂ) * mE E * (∑ α, LWPins_lwS d L W g t x α * LWPins_lwGb d L W E t ω α x * LWPins_lwG d L W E t ω α (y 0)) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * LWPins_lwf d L W E t P ω) -
          mE E * ∑ α, LWPins_lwS d L W g t x α * LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
            LWPins_lwG d L W E t ω α (y 0) * LWPins_lwdf d L W E t P ω α x) ∂(PF d L W g) := by
  classical
  set sz := lwWxSizes d L W g hL with hsz
  have hz : 0 < (zt E t).im := lwWx_im_pos E t hE ht1
  have hz' : (zt E t).im ≠ 0 := hz.ne'
  have hf : Tame1 sz 0 (lwPoly sz 0 (zt E t) t (lwWxRename d L W P)) :=
    lwPoly_tame1 (sz := sz) (n := 0) hz t (lwWxRename d L W P)
  have hR : ∀ (s₂ : Finset (Fin k₂)) (s₃ : Finset (Fin k₃)),
      Tame1 sz 0 (oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' s₂ s₃) :=
    fun s₂ s₃ => oe1xR_tame1 (sz := sz) (n := 0) (z := zt E t) (u := t) hz x y y' w w' s₂ s₃
  have hRf : Tame1 sz 0 (fun ω => oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' Finset.univ Finset.univ ω *
      lwPoly sz 0 (zt E t) t (lwWxRename d L W P) ω) := (hR _ _).mul hf
  have key := oe1x_integral (sz := sz) (n := 0) (z := zt E t) (u := t) (m := mE E) (gaussIBP sz) hz ht
    (lwWx_mE_ne E hE) (lwWx_flow E t hE) hRf x (y 0)
  have tRf := hRf.tame
  have hrhs := oe1x_rhs_tame (sz := sz) (n := 0) (z := zt E t) (u := t) hz (mE E) hRf x (y 0)
  refine (lwWx_integral hL ?_ ?_).trans (key.trans (lwWx_integral hL ?_ ?_).symm)
  · exact ((lwStein_tame_lwG sz 0 hz' t x (y 0)).mul tRf).cont
  · intro ω'
    have h1 := lwWx_lwPoly hL E t ω' P
    change LWPins_lwG d L W E t (Sizes.slice sz 0 ω') x (y 0) * (LWPins_oe1xRest d L W E t (Sizes.slice sz 0 ω') x y y' w w' Finset.univ Finset.univ * LWPins_lwf d L W E t P (Sizes.slice sz 0 ω')) = _
    rw [← h1]
    rfl
  · exact hrhs.cont
  · intro ω'
    have hdh : ∀ α : Idx d L W, dhSample sz 0 t α x (fun ω => oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' Finset.univ
          Finset.univ ω * lwPoly sz 0 (zt E t) t (lwWxRename d L W P) ω) ω' =
        (-((k₁ : ℂ) * lwG sz 0 (zt E t) t x α ω' * oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' Finset.univ Finset.univ ω') -
          ∑ i : Fin k₂, star (lwG sz 0 (zt E t) t x x ω') * star (lwG sz 0 (zt E t) t α (y' i) ω') *
            oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' (Finset.univ.erase i) Finset.univ ω' -
          ∑ i : Fin k₃, lwG sz 0 (zt E t) t (w i) α ω' * lwG sz 0 (zt E t) t x x ω' *
            oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' Finset.univ (Finset.univ.erase i) ω' -
          (k₄ : ℂ) * star (lwG sz 0 (zt E t) t α x ω') *
            oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' Finset.univ Finset.univ ω') *
          lwPoly sz 0 (zt E t) t (lwWxRename d L W P) ω' +
        oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' Finset.univ Finset.univ ω' *
          dhSample sz 0 t α x (lwPoly sz 0 (zt E t) t (lwWxRename d L W P)) ω' := by
      intro α
      rw [lwStein_dh_mul (hR _ _) hf, oe1x_dh_R hz ht]
    simp only [hdh]
    refine Eq.trans ?_ (oe1x_pointwise (k₁ := k₁) (k₂ := k₂) (k₃ := k₃) (k₄ := k₄) (mE E)
      (if x = y 0 then 1 else 0) (lwG sz 0 (zt E t) t x (y 0) ω') (lwG sz 0 (zt E t) t x x ω')
      (oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' Finset.univ Finset.univ ω')
      (lwPoly sz 0 (zt E t) t (lwWxRename d L W P) ω')
      (fun α => lwS sz 0 t x α) (fun α => lwG sz 0 (zt E t) t α α ω')
      (fun α => lwG sz 0 (zt E t) t α (y 0) ω') (fun α => lwG sz 0 (zt E t) t x α ω')
      (fun α => lwG sz 0 (zt E t) t α x ω') (fun α i => lwG sz 0 (zt E t) t α (y' i) ω')
      (fun i α => lwG sz 0 (zt E t) t (w i) α ω')
      (fun i => oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' (Finset.univ.erase i) Finset.univ ω')
      (fun i => oe1xR (sz := sz) (n := 0) (zt E t) t x y y' w w' Finset.univ (Finset.univ.erase i) ω')
      (fun α => dhSample sz 0 t α x (lwPoly sz 0 (zt E t) t (lwWxRename d L W P)) ω')).symm
    simp only [lwWx_lwGc hL E t ω', ← lwWx_lwPoly hL E t ω' P, lwWx_lwdf hL E t hz ht _ _ ω' P,
      ← lwWx_lwS_apply hL t, LWPins_lwGb, LWPins_lwGcb, oe1x_rest_eq hL E t ω', ← lwWx_lwG hL E t ω']
    rfl

/-- **`(Oe1x)` on the one-size law** (`7_8:309-330`, lemma `Oe14`; cited from `[yang2021]` Lemma 3.10): the pin
`LWedgeExp` for every `d`, every `g : ℝ`, `L ≥ 3`, `W ≥ 1`, `|E| < 2`, `0 ≤ t < 1` and every `k₁ … k₄ ≥ 0`.  For
`0 < t < 1`: `oe1x_integral` with `f := rest · f` through the bridge of T2107 (`oe1x_pin_pos`); for `t = 0`,
`G = m I` and `S = 0`: both integrands are `m δ_{x y₁} (rest · f)`.  The paper's `k₁` is the pin's `k₁ + 1`. -/
theorem lwEdgeExp_holds (d : ℕ) : LWedgeExp d := by
  intro L W _ _ hL g E t hE ht0 ht1 k₁ k₂ k₃ k₄ x y y' w w' P
  rcases ht0.eq_or_lt with rfl | ht
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [oe1x_lwG_zero hE, lwWx_lwS_zero]
  · exact oe1x_pin_pos hL g E t hE ht ht1 k₁ k₂ k₃ k₄ x y y' w w' P

end PinProof

/-! ## 3. `(Oe1x)` as a graph operation (T2060d, design row LW-06)

Let `Γ` be a graph with a blue solid edge `e₀ = G_{xy₁}` out of the internal vertex `x` (`p ∈ lwSplit Γ.solid`,
`p.1 = ⟨true, false, inr x, v⟩`, `v = y₁ : E ⊕ I` any vertex; `p.2` the other solid edges: the rest `𝒢/(G_{xy₁} f)`
and `f`).  The terms of `(Oe1x)` as graphs:

* `oe1xT1d`: `m 1_{x = y₁} · rest` -- `e₀` dropped, the dotted `=` edge `x = y₁` added (the paper's form before
  merging); `oe1xT1`: the same with `x` merged into `y₁` (`relabel` onto the internal vertices `{i // i ≠ x}`);
* `owxT1` (T2107): `m Σ_α S_{xα} Ǧ_{αα} · Γ` -- `Γ` kept, a leaf `α` joined to `x` by `S_{xα}` with the light-weight
  `Ǧ_{αα}`; this is the second term of `(Oe1x)` (no `S⁺`);
* `oe1xD q`, one graph for each solid edge `q.1` of `p.2` (`q ∈ lwSplit p.2`): `-m Σ_α S_{xα} G_{αy₁} ∂_{h_{αx}}`
  applied to the factor `q.1`: `e₀` and `q.1` dropped, a leaf `α`, the edge `G_{αy₁}`, and `q.1` replaced by the two
  edges of its derivative (`owxDE`).  Among them: `k₁` terms for the blue out-edges of `x`, `k₄` for the red
  in-edges, `k₂`, `k₃` for the red out-edges and the blue in-edges (the derivative creates the loop `Ḡ_{xx}`,
  resp. `G_{xx}`), and one for each edge of `f`; the loops are split by `oe1xP5`, `oe1xP3` (red out) and
  `oe1xP6`, `oe1xP4` (blue in).
-/

section Oe1xGraph

variable {E I : Type}

/-- **Term 1 of `(Oe1x)`, before merging** (`m 1_{x = y₁}`): `e₀` dropped, the dotted edge `x = y₁` added. -/
def oe1xT1d (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I) :
    LGraph E I where
  solid := p.2
  waved := Γ.waved
  dotted := ⟨true, Sum.inr x, v⟩ :: Γ.dotted
  coeff := m * Γ.coeff

/-- **The derivative term of `(Oe1x)` for the solid edge `q.1` of the rest** (`q ∈ lwSplit p.2`):
`-m Σ_α S_{xα} G_{αy₁} ∂_{h_{αx}}` on `q.1`.  `e₀` and `q.1` are dropped; the new leaf `α = inr (inr 0)`; the
coefficient is `m` (the sign of the derivative is in `owxDE`). -/
def oe1xD (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) m
    [(owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q.1)).1,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q.1)).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

section OeTermVal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

/-- The value of a term of `oe1xD`. -/
theorem oe1xD_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 1) → ι)
    (hℓ : ℓ' ∘ owxEmb 1 = ℓ) :
    (oe1xD m Γ x v q).term D ℓ' = m * ({ Γ with solid := q.2 } : LGraph E I).term D ℓ *
      ((if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0))) * D.G (ℓ (Sum.inr x)) (ℓ q.1.dst)
        else star (D.G (ℓ q.1.src) (ℓ (Sum.inr x))) * star (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst))) *
        D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ v)) *
      D.S (ℓ (Sum.inr x)) (ℓ' (Sum.inr (Sum.inr 0))) := by
  have hx : ℓ' (Sum.inr (Sum.inl x)) = ℓ (Sum.inr x) := by
    rw [← hℓ]; rfl
  have hq : ∀ u, ℓ' (owxEmb 1 u) = ℓ u := fun u => by rw [← hℓ]; rfl
  have h : SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q.1)).1 *
      SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q.1)).2 =
      if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0))) * D.G (ℓ (Sum.inr x)) (ℓ q.1.dst)
      else star (D.G (ℓ q.1.src) (ℓ (Sum.inr x))) * star (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq, hx]
  rw [oe1xD, LGraph.term_owxExt, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc ((SEdge.val D ℓ' _)), h]
  simp [SEdge.val, WEdge.val, hx, hq]

end OeTermVal

end Oe1xGraph

section Oe1xIdentity

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`(Oe1x)` for one labelling of the vertices of `Γ`** (expectations of terms): `Γ` has the blue edge
`e₀ = p.1 = G_{xy₁}` (`p ∈ lwSplit Γ.solid`) out of the internal vertex `x`; `E Γ.term(ℓ)` is the expectation of the
term of `oe1xT1d`, plus the sum over the new label `α` of the expectations of the terms of `owxT1` and, for each
solid edge `q.1` of `p.2`, of `oe1xD q`.  Hypotheses: `GaussIBP` (proved: `gaussIBP sz`), `Im z > 0`, `u > 0`,
`m ≠ 0`, `z + u m = -m⁻¹`, `M_{aa} = m`; `S⁺` is not used. -/
theorem oe1x_term_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (v : E ⊕ I) (hx : p.1 = ⟨true, false, Sum.inr x, v⟩)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) (ℓi : I → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) =
      ∫ ω, (oe1xT1d m Γ p x v).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi)
          ∂(Sizes.seqP sz) +
      ∑ α, ∫ ω, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)
          ∂(Sizes.seqP sz) +
      ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (oe1xD m Γ x v q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
  classical
  have hz' : z.im ≠ 0 := hz.ne'
  set ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n) := Sum.elim ℓe ℓi with hℓ
  set xl : Idx d (sz.L n) (sz.W n) := ℓi x with hxl
  set yl : Idx d (sz.L n) (sz.W n) := ℓ v with hyl
  set K : ℂ := lwK Γ M (lwS sz n u) Sp ℓ with hK
  set P := (p.2.map (owxEdgePoly sz n M ℓ)).prod with hPdef
  have hf : ∀ ω, lwPoly sz n z u P ω =
      (p.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod :=
    fun ω => lwPoly_owxEdgePoly_prod z u M (lwS sz n u) Sp ℓ p.2 ω
  have hP1 : Tame1 sz n (lwPoly sz n z u P) := lwPoly_tame1 hz u P
  have hw : ∀ ω, SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ p.1 =
      lwG sz n z u xl yl ω := by
    intro ω
    rw [hx]
    simp [SEdge.val, lwSampleData, lwG, hℓ, hxl, hyl]
  have hΓ : ∀ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
      K * (lwG sz n z u xl yl ω * lwPoly sz n z u P ω) := by
    intro ω
    rw [lwStein_term_eq, lwSplit_prod Γ.solid _ p hp, hw ω, hf ω]
  have hℓx : ℓ (Sum.inr x) = xl := rfl
  have hK' : ∀ s : List (SEdge (E ⊕ I)),
      lwK ({ Γ with solid := s } : LGraph E I) M (lwS sz n u) Sp ℓ = K := fun s => rfl
  have hT1 : ∀ ω, (oe1xT1d m Γ p x v).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
      m * K * (if xl = yl then 1 else 0) * lwPoly sz n z u P ω := by
    intro ω
    rw [lwStein_term_eq, hf ω]
    simp only [lwK, oe1xT1d, hK, List.map_cons, List.prod_cons, DEdge.val]
    have : (ℓ (Sum.inr x) = ℓ v) = (xl = yl) := rfl
    simp only [this, iff_true]
    ring
  have hT2 : ∀ α ω, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * (lwG sz n z u xl yl ω * lwPoly sz n z u P ω)) * (lwG sz n z u α α ω - m) *
        lwS sz n u xl α := by
    intro α ω
    rw [owxT1_term _ m Γ x ℓ _ (owxLab1_emb ℓe ℓi α), hΓ ω]
    simp [owxLab1, lwSampleData, lwG, hM, hℓx]
  have hT3 : ∀ (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) α ω,
      (oe1xD m Γ x v q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod) *
        ((if q.1.σ then lwG sz n z u (ℓ q.1.src) α ω * lwG sz n z u xl (ℓ q.1.dst) ω
          else star (lwG sz n z u (ℓ q.1.src) xl ω) * star (lwG sz n z u α (ℓ q.1.dst) ω)) *
          lwG sz n z u α yl ω) * lwS sz n u xl α := by
    intro q α ω
    rw [oe1xD_term _ m Γ x v q ℓ _ (owxLab1_emb ℓe ℓi α)]
    have : ({ Γ with solid := q.2 } : LGraph E I).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
        K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod := by
      rw [lwStein_term_eq, hK']
    rw [this]
    simp [owxLab1, lwSampleData, lwG, hℓx, hyl]
  have hdh : ∀ (α w : Idx d (sz.L n) (sz.W n)) ω, dhSample sz n u α w (lwPoly sz n z u P) ω =
      ((lwSplit p.2).map fun q =>
        (if q.1.σ then -(lwG sz n z u (ℓ q.1.src) α ω * lwG sz n z u w (ℓ q.1.dst) ω)
          else -(star (lwG sz n z u (ℓ q.1.src) w ω) * star (lwG sz n z u α (ℓ q.1.dst) ω))) *
        (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod).sum := by
    intro α w ω
    have hfun : lwPoly sz n z u P = fun ω => (p.2.map fun a =>
        SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ a).prod := funext hf
    rw [hfun, lwStein_dh_listProd p.2 (fun e _ => lwStein_sedge_val_tame1 hz e ℓ)]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [lwStein_dh_sedge_val hz hu q.1 α w ℓ ω]
  have hS3 : ∀ α ω, ((lwSplit p.2).map fun q => (oe1xD m Γ x v q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum =
      -(K * (m * (lwS sz n u xl α * lwG sz n z u α yl ω)) *
        dhSample sz n u α xl (lwPoly sz n z u P) ω) := by
    intro α ω
    rw [hdh α xl ω]
    refine owx_list_aux _ _ _ _ fun q _ => ?_
    rw [hT3 q α ω]
    by_cases hσ : q.1.σ <;> simp [hσ] <;> ring
  have hpath : ∀ ω, K * (m * (if xl = yl then 1 else 0) * lwPoly sz n z u P ω +
          m * (∑ α, lwS sz n u xl α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u xl yl ω * lwPoly sz n z u P ω) -
          m * ∑ α, lwS sz n u xl α * lwG sz n z u α yl ω * dhSample sz n u α xl (lwPoly sz n z u P) ω) =
      (oe1xT1d m Γ p x v).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ +
      ∑ α, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) +
      ∑ α, ((lwSplit p.2).map fun q => (oe1xD m Γ x v q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (owxLab1 ℓe ℓi α)).sum := by
    intro ω
    simp only [hT1, hT2, hS3]
    have hB : ∑ x, m * (K * (lwG sz n z u xl yl ω * lwPoly sz n z u P ω)) *
        (lwG sz n z u x x ω - m) * lwS sz n u xl x =
        K * (m * (∑ α, lwS sz n u xl α * (lwG sz n z u α α ω - m)) *
          (lwG sz n z u xl yl ω * lwPoly sz n z u P ω)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hC : ∑ x, -(K * (m * (lwS sz n u xl x * lwG sz n z u x yl ω)) *
        dhSample sz n u x xl (lwPoly sz n z u P) ω) =
        -(K * (m * ∑ α, lwS sz n u xl α * lwG sz n z u α yl ω *
          dhSample sz n u α xl (lwPoly sz n z u P) ω)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hB, hC]
    ring
  have key := oe1x_integral hG hz hu hm0 hzm hP1 xl yl
  have hint : ∀ {E' I' : Type} (T : LGraph E' I') (ℓ' : E' ⊕ I' → Idx d (sz.L n) (sz.W n)),
      Integrable (fun ω => T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') (Sizes.seqP sz) :=
    fun T ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have e1 : ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ ∂(Sizes.seqP sz) =
      K * ∫ ω, lwG sz n z u xl yl ω * lwPoly sz n z u P ω ∂(Sizes.seqP sz) := by
    simp_rw [hΓ]
    rw [integral_const_mul]
  rw [e1, key, ← integral_const_mul]
  simp_rw [hpath]
  set S1 : Sizes.SeqΩ sz → ℂ := fun ω => (oe1xT1d m Γ p x v).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ with hS1
  set S2 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, (owxT1 m Γ x).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) with hS2
  set S3 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ((lwSplit p.2).map fun q => (oe1xD m Γ x v q).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum with hS3'
  have hi1 : Integrable S1 (Sizes.seqP sz) := hint _ _
  have hi2 : Integrable S2 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => hint _ _
  have hi3 : Integrable S3 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => owx_integrable_list_sum _ _ fun q _ => hint _ _
  change ∫ ω, (S1 ω + S2 ω + S3 ω) ∂(Sizes.seqP sz) = _
  have hi12 : Integrable (fun ω => S1 ω + S2 ω) (Sizes.seqP sz) := hi1.add hi2
  rw [integral_add hi12 hi3, integral_add hi1 hi2]
  have e2' : ∫ ω, S2 ω ∂(Sizes.seqP sz) = ∑ α, ∫ ω, (owxT1 m Γ x).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
    integral_finsetSum _ fun α _ => hint _ _
  have e3' : ∫ ω, S3 ω ∂(Sizes.seqP sz) = ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (oe1xD m Γ x v q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
    rw [hS3', integral_finsetSum _ fun α _ => owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact owx_integral_list_sum _ _ _ fun q _ => hint _ _
  rw [e2', e3']

/-- **`(Oe1x)` as a graph operation: the identity of expectations of values** (`7_8:309-330`, `Oe14`; T2060d, design row
LW-06).  For a graph `Γ` with the blue edge `e₀ = p.1 = G_{xy₁}` out of the internal vertex `x` (`p ∈ lwSplit Γ.solid`,
`p.2` the other solid edges, i.e. `Γ.val = E[G_{xy₁} · rest · f]`):
`E Γ.val = E (oe1xT1d m Γ p x v).val + E (owxT1 m Γ x).val + Σ_q E (oe1xD m Γ x v q).val`,
`q` running over `lwSplit p.2` (one graph for each solid edge of the rest and of `f`).  The counters:
`oe1xT1d_counters`, `owxT1_counters`, `oe1xD_counters`.  Data: the resolvent `G = (H_u - z)⁻¹` of the flow of
size `n`, deterministic `M` (`M_{aa} = m`), `S = lwS sz n u`, and any `Sp` (`S⁺` does not occur). -/
theorem oe1x_graph_Ed (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (v : E ⊕ I) (hx : p.1 = ⟨true, false, Sum.inr x, v⟩) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (oe1xT1d m Γ p x v).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxT1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ∫ ω, (oe1xD m Γ x v q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  classical
  have hint : ∀ {E' I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph E' I')
      (ℓ' : E' ⊕ I' → Idx d (sz.L n) (sz.W n)),
      Integrable (fun ω => T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') (Sizes.seqP sz) :=
    fun T ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have hval : ∀ (T : LGraph E I),
      ∫ ω, T.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) := by
    intro T
    unfold LGraph.val
    exact integral_finsetSum _ fun ℓi _ => hint _ _
  rw [hval Γ, hval (oe1xT1d m Γ p x v), owx_integral_val1 hG hz M _ Sp (owxT1 m Γ x) ℓe]
  simp_rw [oe1x_term_integral hG hz hu hm0 hzm Sp M hM Γ p hp x v hx ℓe]
  simp only [Finset.sum_add_distrib]
  have h3 : ((lwSplit p.2).map fun q => ∫ ω, (oe1xD m Γ x v q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (oe1xD m Γ x v q).term
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
    have e : ((lwSplit p.2).map fun q => ∫ ω, (oe1xD m Γ x v q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
        (lwSplit p.2).map fun q => ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∫ ω, (oe1xD m Γ x v q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
      List.map_congr_left fun q _ => owx_integral_val1 hG hz M _ Sp _ ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
  rw [h3]

end Oe1xIdentity

/-! ### Term 1 with `x` merged into `y₁` -/

section Oe1xMerge

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- A vertex other than `inr x`, as a vertex of the graph without the internal vertex `x`. -/
def oe1xSub (x : I) : (u : E ⊕ I) → u ≠ Sum.inr x → E ⊕ {i : I // i ≠ x}
  | Sum.inl a, _ => Sum.inl a
  | Sum.inr i, h => Sum.inr ⟨i, fun e => h (by rw [e])⟩

/-- The merge of `x` into `v ≠ inr x`: `x ↦ v`, every other vertex stays. -/
def oe1xPhi (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) (u : E ⊕ I) : E ⊕ {i : I // i ≠ x} :=
  if h : u = Sum.inr x then oe1xSub x v hv else oe1xSub x u h

/-- **Term 1 of `(Oe1x)`** (`m 1_{x = y₁}`, `x ≠ y₁`): `e₀` dropped and the vertex `x` merged into `y₁`: the graph
on the internal vertices `{i // i ≠ x}`. -/
def oe1xT1 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) : LGraph E {i : I // i ≠ x} :=
  ({ Γ with solid := p.2, coeff := m * Γ.coeff } : LGraph E I).relabel (oe1xPhi x v hv)

theorem oe1xPhi_inl (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) (a : E) :
    oe1xPhi x v hv (Sum.inl a) = Sum.inl a := by
  simp [oe1xPhi, oe1xSub]

theorem oe1xPhi_x (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) :
    oe1xPhi x v hv (Sum.inr x) = oe1xSub x v hv := by
  simp [oe1xPhi]

theorem oe1xPhi_ne (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) (i : I) (h : i ≠ x) :
    oe1xPhi x v hv (Sum.inr i) = Sum.inr ⟨i, h⟩ := by
  simp [oe1xPhi, oe1xSub, h]

/-- The retraction: `Φ` is surjective. -/
theorem oe1xPhi_surj (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) : Function.Surjective (oe1xPhi x v hv) := by
  intro w
  rcases w with a | ⟨i, hi⟩
  · exact ⟨Sum.inl a, oe1xPhi_inl x v hv a⟩
  · exact ⟨Sum.inr i, oe1xPhi_ne x v hv i hi⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The value of term 1 with `x` merged into `y₁` is that of the graph with the dotted edge `x = y₁`**
(`dot-def`, `7_8:222`): for every `D`, `ℓe`. -/
theorem oe1xT1_val (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) (D : LData ι) (ℓe : E → ι) :
    (oe1xT1 m Γ p x v hv).val D ℓe = (oe1xT1d m Γ p x v).val D ℓe := by
  classical
  set Δ : LGraph E I := { Γ with solid := p.2, coeff := m * Γ.coeff } with hΔ
  -- the extension of a labelling of `{i // i ≠ x}` by the label of `y₁`
  let ext : ({i : I // i ≠ x} → ι) → (I → ι) := fun ℓi' i =>
    if h : i = x then (Sum.elim ℓe ℓi') (oe1xSub x v hv) else ℓi' ⟨i, h⟩
  have hext : ∀ ℓi', Sum.elim ℓe ℓi' ∘ oe1xPhi x v hv = Sum.elim ℓe (ext ℓi') := by
    intro ℓi'
    funext u
    rcases u with a | i
    · simp [oe1xPhi_inl]
    · by_cases h : i = x
      · subst h
        simp [oe1xPhi_x, ext]
      · simp [oe1xPhi_ne x v hv i h, ext, h]
  have hinj : Function.Injective ext := by
    intro f g hfg
    funext ⟨i, hi⟩
    have := congrFun hfg i
    simpa [ext, hi] using this
  have hv' : oe1xPhi x v hv v = oe1xSub x v hv := by
    simp [oe1xPhi, hv]
  have hdot : ∀ ℓi', (ext ℓi') x = (Sum.elim ℓe (ext ℓi')) v := by
    intro ℓi'
    have h1 := congrFun (hext ℓi') v
    rw [Function.comp_apply, hv'] at h1
    rw [← h1]
    simp [ext]
  have hsub : ∀ ℓi : I → ι, (Sum.elim ℓe (ℓi ∘ Subtype.val)) (oe1xSub x v hv) = (Sum.elim ℓe ℓi) v := by
    intro ℓi
    rcases v with a | j <;> simp [oe1xSub]
  have hT1d : ∀ ℓi, (oe1xT1d m Γ p x v).term D (Sum.elim ℓe ℓi) =
      (if ℓi x = (Sum.elim ℓe ℓi) v then 1 else 0) * Δ.term D (Sum.elim ℓe ℓi) := by
    intro ℓi
    simp only [LGraph.term, oe1xT1d, hΔ, List.map_cons, List.prod_cons, DEdge.val]
    simp only [Sum.elim_inr, iff_true]
    split_ifs <;> ring
  have hrel : ∀ ℓi', (oe1xT1 m Γ p x v hv).term D (Sum.elim ℓe ℓi') = Δ.term D (Sum.elim ℓe (ext ℓi')) := by
    intro ℓi'
    rw [oe1xT1, LGraph.term_relabel, hext]
  set F : (I → ι) → ℂ := fun ℓi => (if ℓi x = (Sum.elim ℓe ℓi) v then (1 : ℂ) else 0) *
    Δ.term D (Sum.elim ℓe ℓi) with hFdef
  have hF : ∀ ℓi', F (ext ℓi') = Δ.term D (Sum.elim ℓe (ext ℓi')) := by
    intro ℓi'
    simp only [hFdef, hdot ℓi', ↓reduceIte, one_mul]
  have hsupp : ∀ ℓi : I → ι, ℓi ∉ Finset.univ.image ext → F ℓi = 0 := by
    intro ℓi hni
    have hne : ¬ ℓi x = (Sum.elim ℓe ℓi) v := by
      intro hxv
      apply hni
      refine Finset.mem_image.2 ⟨ℓi ∘ Subtype.val, Finset.mem_univ _, ?_⟩
      funext i
      by_cases h : i = x
      · subst h
        simp only [ext, dite_true]
        rw [hsub, hxv]
      · simp [ext, h]
    simp [hFdef, hne]
  unfold LGraph.val
  simp_rw [hT1d, hrel]
  calc ∑ ℓi', Δ.term D (Sum.elim ℓe (ext ℓi')) = ∑ ℓi', F (ext ℓi') :=
        Finset.sum_congr rfl fun ℓi' _ => (hF ℓi').symm
    _ = ∑ ℓi ∈ Finset.univ.image ext, F ℓi := (Finset.sum_image fun a _ b _ h => hinj h).symm
    _ = ∑ ℓi, F ℓi := Finset.sum_subset (Finset.subset_univ _) fun ℓi _ hni => hsupp ℓi hni

/-- A relabelled graph keeps the adjacency (waved or `=`-dotted edge) of the images. -/
theorem oe1x_adj_relabel {I' : Type} [Fintype I'] [DecidableEq I'] (Γ : LGraph E I) (φ : E ⊕ I → E ⊕ I')
    (u v : E ⊕ I) (h : Γ.adj u v = true) : (Γ.relabel φ).adj (φ u) (φ v) = true := by
  simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
    Bool.and_eq_true] at h ⊢
  rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
  · left
    refine ⟨WEdge.map φ e, ?_, ?_⟩
    · simp only [LGraph.relabel, List.mem_map]
      exact ⟨e, he, rfl⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; simp [WEdge.map, h1, h2]
      · right; simp [WEdge.map, h1, h2]
  · right
    refine ⟨DEdge.map φ e, ?_, by simpa [DEdge.map] using h1, ?_⟩
    · simp only [LGraph.relabel, List.mem_map]
      exact ⟨e, he, rfl⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; simp [DEdge.map, h1, h2]
      · right; simp [DEdge.map, h1, h2]

/-- **Merging vertices does not increase `n_M`**: if `φ` is onto and fixes the external vertices, the relabelled graph
has at most as many internal molecules (the molecules of `Γ` map onto those of the relabelled graph; the preimage
of an internal molecule is internal). -/
theorem oe1x_nM_relabel_le {I' : Type} [Fintype I'] [DecidableEq I'] (Γ : LGraph E I) (φ : E ⊕ I → E ⊕ I')
    (hφ : ∀ a, φ (Sum.inl a) = Sum.inl a) (hsurj : Function.Surjective φ) :
    (Γ.relabel φ).nM ≤ Γ.nM := by
  classical
  have hreach : ∀ {u v : E ⊕ I}, Γ.molGraph.Reachable u v → (Γ.relabel φ).molGraph.Reachable (φ u) (φ v) := by
    intro u v h
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hadj _ ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      by_cases hab : φ a = φ b
      · rw [hab]
      · exact SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨hab,
          oe1x_adj_relabel Γ φ a b ((owx_molGraph_adj Γ a b).1 hadj).2⟩)
  let Φ : Γ.Mol → (Γ.relabel φ).Mol :=
    SimpleGraph.ConnectedComponent.lift (fun v => (Γ.relabel φ).molOf (φ v))
      (fun u v p _ => SimpleGraph.ConnectedComponent.eq.2 (hreach (SimpleGraph.Walk.reachable p)))
  have hΦ : ∀ v, Φ (Γ.molOf v) = (Γ.relabel φ).molOf (φ v) := fun v => rfl
  have hΦsurj : Function.Surjective Φ := by
    intro c'
    induction c' using SimpleGraph.ConnectedComponent.ind with | h w' => ?_
    obtain ⟨w, rfl⟩ := hsurj w'
    exact ⟨Γ.molOf w, rfl⟩
  have hext : ∀ c, Γ.IsExtMol c → (Γ.relabel φ).IsExtMol (Φ c) := by
    rintro c ⟨a, rfl⟩
    exact ⟨a, by rw [hΦ, hφ]⟩
  set σ : (Γ.relabel φ).Mol → Γ.Mol := Function.surjInv hΦsurj with hσ
  have hσinj : Function.Injective σ := Function.injective_surjInv hΦsurj
  have hΦσ : ∀ c', Φ (σ c') = c' := Function.surjInv_eq hΦsurj
  rw [LGraph.nM_eq_card, LGraph.nM_eq_card]
  refine Nat.card_le_card_of_injective
    (fun c : {c : (Γ.relabel φ).Mol // ¬ (Γ.relabel φ).IsExtMol c} =>
      (⟨σ c.1, fun h => c.2 (by have := hext _ h; rwa [hΦσ] at this)⟩ :
        {c : Γ.Mol // ¬ Γ.IsExtMol c})) ?_
  intro c c' h
  exact Subtype.ext (hσinj (congrArg Subtype.val h))

/-- **The counters of term 1** (`x` merged into `y₁ ≠ x`): the solid edge `e₀` and the vertex `x` disappear, `n_W`
stays, `n_M` does not grow (`oe1x_nM_relabel_le`).  The table of T2040 (a)(i) lists `Δ n_M = 0`; here only `Δ n_M ≤ 0`
is proved (candidate `T2119a`). -/
theorem oe1xT1_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) :
    (oe1xT1 m Γ p x v hv).nS + 1 = Γ.nS ∧ (oe1xT1 m Γ p x v hv).nW = Γ.nW ∧
      (oe1xT1 m Γ p x v hv).nV + 1 = Γ.nV ∧ (oe1xT1 m Γ p x v hv).nM ≤ Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  refine ⟨?_, by simp [oe1xT1, LGraph.relabel, LGraph.nW], ?_, ?_⟩
  · simp only [oe1xT1, LGraph.relabel, LGraph.nS, List.length_map]
    omega
  · unfold LGraph.nV
    have h1 : Fintype.card {i : I // i ≠ x} = Fintype.card I - Fintype.card {i : I // i = x} :=
      Fintype.card_subtype_compl (fun i : I => i = x)
    have h2 : Fintype.card {i : I // i = x} = 1 := Fintype.card_subtype_eq x
    have h3 : 0 < Fintype.card I := Fintype.card_pos_iff.2 ⟨x⟩
    omega
  · have h := oe1x_nM_relabel_le ({ Γ with solid := p.2, coeff := m * Γ.coeff } : LGraph E I)
      (oe1xPhi x v hv) (oe1xPhi_inl x v hv) (oe1xPhi_surj x v hv)
    have h' : ({ Γ with solid := p.2, coeff := m * Γ.coeff } : LGraph E I).nM = Γ.nM :=
      lwStein_nM_congr _ _ rfl rfl
    rw [oe1xT1]
    omega

/-- **`ord` of term 1**: `ord Γ + 1` (`Δ(n_S, n_W, n_V) = (-1, 0, -1)`). -/
theorem oe1xT1_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) :
    ord (oe1xT1 m Γ p x v hv).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, -⟩ := oe1xT1_counters m Γ p hp x v hv
  simp only [LGraph.counters, ord, h2]
  omega

/-- **The counters of the derivative terms**: `Δ(n_S, n_W, n_V, n_M) = (1, 1, 1, 0)`. -/
theorem oe1xD_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    (oe1xD m Γ x v q).nS = Γ.nS + 1 ∧ (oe1xD m Γ x v q).nW = Γ.nW + 1 ∧
      (oe1xD m Γ x v q).nV = Γ.nV + 1 ∧ (oe1xD m Γ x v q).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [oe1xD, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [oe1xD, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (oe1xD m Γ x v q).nM = ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 1 x m _ _ ?_ (owxExt_reach1 _ x m _ _ false true (by simp))
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem oe1xD_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) : ord (oe1xD m Γ x v q).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := oe1xD_counters m Γ p hp x v q hq
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

/-! ### The loops at `x` of the derivative terms (`Ḡ_{xx} = Ǧ_{xx} + m̄`, `G_{xx} = Ǧ_{xx} + m`) -/

/-- **Terms 3 and 5 of `(Oe1x)`** for a red out-edge `q.1 = Ḡ_{x d}` of `x` (`k₂` sum): the derivative
`-Ḡ_{xx} Ḡ_{αd}` with the loop circled: `m Ǧ̄_{xx} Σ_α S_{xα} G_{αy₁} Ḡ_{αd}`. -/
def oe1xP5 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) m
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inl x)⟩,
      ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 q.1.dst⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

/-- **Term 3**: the loop `Ḡ_{xx}` replaced by the constant `m̄`: `|m|² Σ_α S_{xα} G_{αy₁} Ḡ_{αd}`. -/
def oe1xP3 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) (m * star m)
    [⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 q.1.dst⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

/-- **Terms 4 and 6 of `(Oe1x)`** for a blue in-edge `q.1 = G_{s x}` of `x` (`k₃` sum): the derivative
`-G_{sα} G_{xx}` with the loop circled: `m Ǧ_{xx} Σ_α S_{xα} G_{αy₁} G_{sα}`. -/
def oe1xP6 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) m
    [⟨true, false, owxEmb 1 q.1.src, Sum.inr (Sum.inr 0)⟩,
      ⟨true, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inl x)⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

/-- **Term 4**: the loop `G_{xx}` replaced by the constant `m`: `m² Σ_α S_{xα} G_{αy₁} G_{sα}`. -/
def oe1xP4 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) (m * m)
    [⟨true, false, owxEmb 1 q.1.src, Sum.inr (Sum.inr 0)⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

section OeSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The term of the derivative graph of a red out-edge of `x` is the sum of those of `oe1xP5` and `oe1xP3`. -/
theorem oe1xD_red_term (D : LData ι) (m : ℂ) (hM : ∀ a, D.M a a = m) (Γ : LGraph E I) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hσ : q.1.σ = false) (hs : q.1.src = Sum.inr x)
    (ℓ' : E ⊕ (I ⊕ Fin 1) → ι) :
    (oe1xD m Γ x v q).term D ℓ' = (oe1xP5 m Γ x v q).term D ℓ' + (oe1xP3 m Γ x v q).term D ℓ' := by
  simp only [oe1xD, oe1xP5, oe1xP3, LGraph.term_owxExt]
  simp [owxDE, hσ, SEdge.map, hs, owxEmb, SEdge.val, WEdge.val, hM, star_sub]
  ring

/-- The term of the derivative graph of a blue in-edge of `x` is the sum of those of `oe1xP6` and `oe1xP4`. -/
theorem oe1xD_blue_term (D : LData ι) (m : ℂ) (hM : ∀ a, D.M a a = m) (Γ : LGraph E I) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hσ : q.1.σ = true) (hd : q.1.dst = Sum.inr x)
    (ℓ' : E ⊕ (I ⊕ Fin 1) → ι) :
    (oe1xD m Γ x v q).term D ℓ' = (oe1xP6 m Γ x v q).term D ℓ' + (oe1xP4 m Γ x v q).term D ℓ' := by
  simp only [oe1xD, oe1xP6, oe1xP4, LGraph.term_owxExt]
  simp [owxDE, hσ, SEdge.map, hd, owxEmb, SEdge.val, WEdge.val, hM]
  ring

end OeSplit

/-- Counters of the four graphs `oe1xP5`, `oe1xP3`, `oe1xP6`, `oe1xP4`: one new vertex `α`, one new waved edge `S_{xα}`,
no change of the molecules; `n_S + 1` with the circled loop (`oe1xP5`, `oe1xP6`), `n_S + 0` with the constant
(`oe1xP3`, `oe1xP4`). -/
theorem oe1xP_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    ((oe1xP5 m Γ x v q).nS = Γ.nS + 1 ∧ (oe1xP5 m Γ x v q).nW = Γ.nW + 1 ∧
      (oe1xP5 m Γ x v q).nV = Γ.nV + 1 ∧ (oe1xP5 m Γ x v q).nM = Γ.nM) ∧
    ((oe1xP3 m Γ x v q).nS = Γ.nS ∧ (oe1xP3 m Γ x v q).nW = Γ.nW + 1 ∧
      (oe1xP3 m Γ x v q).nV = Γ.nV + 1 ∧ (oe1xP3 m Γ x v q).nM = Γ.nM) ∧
    ((oe1xP6 m Γ x v q).nS = Γ.nS + 1 ∧ (oe1xP6 m Γ x v q).nW = Γ.nW + 1 ∧
      (oe1xP6 m Γ x v q).nV = Γ.nV + 1 ∧ (oe1xP6 m Γ x v q).nM = Γ.nM) ∧
    ((oe1xP4 m Γ x v q).nS = Γ.nS ∧ (oe1xP4 m Γ x v q).nW = Γ.nW + 1 ∧
      (oe1xP4 m Γ x v q).nV = Γ.nV + 1 ∧ (oe1xP4 m Γ x v q).nM = Γ.nM) := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hM : ∀ (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 1)))),
      (({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) c s
        [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]).nM = Γ.nM := by
    intro c s
    have h : (({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) c s
        [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]).nM =
        ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 1 x c _ _ ?_ (owxExt_reach1 _ x c _ _ false true (by simp))
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl
  refine ⟨⟨?_, by simp [oe1xP5, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], hM _ _⟩,
    ⟨?_, by simp [oe1xP3, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], hM _ _⟩,
    ⟨?_, by simp [oe1xP6, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], hM _ _⟩,
    ⟨?_, by simp [oe1xP4, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], hM _ _⟩⟩
  · simp only [oe1xP5, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · simp only [oe1xP3, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · simp only [oe1xP6, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · simp only [oe1xP4, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega

/-- **The derivative terms with the loops at `x` split** (`q ∈ lwSplit p.2`): for a red out-edge of `x` the two graphs
`oe1xP5` (loop circled) and `oe1xP3` (loop replaced by `m̄`); for a blue in-edge of `x` the two graphs `oe1xP6`, `oe1xP4`;
for every other solid edge the one graph `oe1xD`.  These are terms 3-9 of `(Oe1x)` (`7_8:316-319`). -/
def oe1xDs (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List (LGraph E (I ⊕ Fin 1)) :=
  if q.1.σ = false ∧ q.1.src = Sum.inr x then [oe1xP5 m Γ x v q, oe1xP3 m Γ x v q]
  else if q.1.σ = true ∧ q.1.dst = Sum.inr x then [oe1xP6 m Γ x v q, oe1xP4 m Γ x v q]
  else [oe1xD m Γ x v q]

/-- **The counters of the derivative terms** (`oe1xDs`): `n_W + 1`, `n_V + 1`, `n_M` unchanged, `n_S + 1` except for the
two graphs with the loop replaced by a constant (`oe1xP3`, `oe1xP4`), which have `n_S`. -/
theorem oe1xDs_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ oe1xDs m Γ x v q, T.nW = Γ.nW + 1 ∧ T.nV = Γ.nV + 1 ∧ T.nM = Γ.nM ∧
      (T.nS = Γ.nS + 1 ∨ (T.nS = Γ.nS ∧ ((q.1.σ = false ∧ q.1.src = Sum.inr x) ∨
        (q.1.σ = true ∧ q.1.dst = Sum.inr x)))) := by
  intro T hT
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩, ⟨e1, e2, e3, e4⟩⟩ :=
    oe1xP_counters m Γ p hp x v q hq
  obtain ⟨d1, d2, d3, d4⟩ := oe1xD_counters m Γ p hp x v q hq
  unfold oe1xDs at hT
  split_ifs at hT with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact ⟨a2, a3, a4, Or.inl a1⟩
    · exact ⟨b2, b3, b4, Or.inr ⟨b1, Or.inl h1⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact ⟨c2, c3, c4, Or.inl c1⟩
    · exact ⟨e2, e3, e4, Or.inr ⟨e1, Or.inr h2⟩⟩
  · simp only [List.mem_singleton] at hT
    subst hT
    exact ⟨d2, d3, d4, Or.inl d1⟩

/-- **The scaling order of the derivative terms**: `ord Γ + 1`, except `ord Γ` for the two graphs with the loop replaced
by a constant (`Δ(n_S, n_W, n_V) = (0, 1, 1)`: the pull of `G_{αy₁} Ḡ_{αd}` resp. `G_{αy₁} G_{sα}`), as in the table of
T2040 (a)(i).  In particular `ord T ≥ ord Γ` for every term. -/
theorem oe1xDs_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ oe1xDs m Γ x v q, ord T.counters = ord Γ.counters + 1 ∨
      (ord T.counters = ord Γ.counters ∧ ((q.1.σ = false ∧ q.1.src = Sum.inr x) ∨
        (q.1.σ = true ∧ q.1.dst = Sum.inr x))) := by
  intro T hT
  obtain ⟨h1, h2, h3, h4⟩ := oe1xDs_counters m Γ p hp x v q hq T hT
  simp only [LGraph.counters, ord, h1, h2, h3]
  rcases h4 with h | ⟨h, hc⟩
  · left; rw [h]; push_cast; ring
  · right; refine ⟨?_, hc⟩; rw [h]; push_cast; ring

end Oe1xMerge

/-! ### The identity of expectations with the merged term 1 and the split derivative terms -/

section Oe1xGraphE

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The value of a graph at the sample is integrable (`GaussIBP`). -/
theorem oe1x_val_integrable (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ}
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {E' I' : Type}
    [Fintype I'] [DecidableEq I'] (T : LGraph E' I') (ℓe : E' → Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => T.val (lwSampleData sz n z u M S Sp ω) ℓe) (Sizes.seqP sz) := by
  unfold LGraph.val
  exact integrable_finsetSum _ fun ℓi _ => Tame.integrable hG (lwStein_term_tame1 hz T _).tame

/-- **The split of the derivative term** (`oe1xDs`): `E (oe1xD q).val` is the sum of the `E T.val` over the graphs `T` of
`oe1xDs q` (the loops `Ḡ_{xx}`, `G_{xx}` created at `x` are split into the light-weight and the constant `m̄`, `m`). -/
theorem oe1xDs_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} {m : ℂ}
    (S Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (oe1xD m Γ x v q).val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
      ((oe1xDs m Γ x v q).map fun T => ∫ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe
        ∂(Sizes.seqP sz)).sum := by
  classical
  have hMd : ∀ ω, ∀ a, (lwSampleData sz n z u M S Sp ω).M a a = m := fun ω a => hM a
  have hint := fun (T : LGraph E (I ⊕ Fin 1)) =>
    oe1x_val_integrable (sz := sz) (n := n) hG hz (u := u) M S Sp T ℓe
  have hsplit : ∀ (A B : LGraph E (I ⊕ Fin 1)),
      (∀ ℓ' : E ⊕ (I ⊕ Fin 1) → Idx d (sz.L n) (sz.W n), ∀ ω,
        (oe1xD m Γ x v q).term (lwSampleData sz n z u M S Sp ω) ℓ' =
          A.term (lwSampleData sz n z u M S Sp ω) ℓ' + B.term (lwSampleData sz n z u M S Sp ω) ℓ') →
      ∫ ω, (oe1xD m Γ x v q).val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
        ∫ ω, A.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) +
          ∫ ω, B.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) := by
    intro A B h
    rw [← integral_add (hint A) (hint B)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [LGraph.val, ← Finset.sum_add_distrib, h]
  unfold oe1xDs
  split_ifs with h1 h2
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact hsplit _ _ fun ℓ' ω => oe1xD_red_term _ m (hMd ω) Γ x v q h1.1 h1.2 ℓ'
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact hsplit _ _ fun ℓ' ω => oe1xD_blue_term _ m (hMd ω) Γ x v q h2.1 h2.2 ℓ'
  · simp

/-- **`(Oe1x)` as a graph operation (the form `lvl1` consumes)**, `7_8:309-330` (lemma `Oe14`); T2060d, design row LW-06.
Let `Γ` be a graph with the blue solid edge `e₀ = p.1 = G_{xy₁}` out of the internal vertex `x` (`p ∈ lwSplit Γ.solid`,
`p.1 = ⟨true, false, inr x, v⟩`, `v = y₁ ≠ x`; `p.2` are the other solid edges: the rest `𝒢/(G_{xy₁} f)` and `f`).  Then
`E Γ.val = E (oe1xT1 m Γ p x v hv).val + E (owxT1 m Γ x).val + Σ_{q ∈ lwSplit p.2} Σ_{T ∈ oe1xDs m Γ x v q} E T.val`.
The nine terms: `oe1xT1` is `m 1_{x = y₁}` (`x` merged into `y₁`); `owxT1` is `m Σ_α S_{xα} Ǧ_{αα} 𝒢`; for each
solid edge `q.1` of `p.2`: a blue out-edge of `x` gives one graph (term 7, `k₁` of them), a red in-edge of `x` one graph
(term 8, `k₄`), a red out-edge of `x` the pair `oe1xP5`, `oe1xP3` (terms 5, 3), a blue in-edge of `x` the pair `oe1xP6`,
`oe1xP4` (terms 6, 4), every other edge one graph (term 9, `-m Σ_α S_{xα} G_{αy₁} ∂_{h_{αx}} f`).  The counter changes:
`oe1xT1_counters`/`oe1xT1_ord` (`ord + 1`), `owxT1_counters`/`owxT1_ord` (`ord + 1`), `oe1xDs_counters`/`oe1xDs_ord`
(`ord + 1`, except `ord + 0` for `oe1xP3`, `oe1xP4`).  `S⁺` does not occur (`Sp` is arbitrary). -/
theorem oe1x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (v : E ⊕ I) (hx : p.1 = ⟨true, false, Sum.inr x, v⟩) (hv : v ≠ Sum.inr x)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (oe1xT1 m Γ p x v hv).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxT1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ((oe1xDs m Γ x v q).map fun T => ∫ ω, T.val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum).sum := by
  have e1 : ∫ ω, (oe1xT1d m Γ p x v).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (oe1xT1 m Γ p x v hv).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => (oe1xT1_val m Γ p x v hv _ ℓe).symm)
  have e2 : ((lwSplit p.2).map fun q => ∫ ω, (oe1xD m Γ x v q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
      ((lwSplit p.2).map fun q => ((oe1xDs m Γ x v q).map fun T => ∫ ω, T.val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) :=
    List.map_congr_left fun q _ => oe1xDs_integral hG hz (lwS sz n u) Sp M hM Γ x v q ℓe
  rw [oe1x_graph_Ed hG hz hu hm0 hzm Sp M hM Γ p hp x v hx ℓe, e1, e2]

/-- **The case `y₁ = x`** (`e₀` a weight `G_{xx}`): term 1 is `m · rest` on the same vertices: `e₀` dropped, the coefficient
`m`. -/
def oe1xT1loop (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E I :=
  { Γ with solid := p.2, coeff := m * Γ.coeff }

/-- For `y₁ = x` the dotted edge `x = x` of `oe1xT1d` is always satisfied: `oe1xT1d` and `oe1xT1loop` have the same value. -/
theorem oe1xT1d_val_loop {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℂ) (Γ : LGraph E I)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (D : LData ι) (ℓe : E → ι) :
    (oe1xT1d m Γ p x (Sum.inr x)).val D ℓe = (oe1xT1loop m Γ p).val D ℓe := by
  unfold LGraph.val
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  simp only [LGraph.term, oe1xT1d, oe1xT1loop, List.map_cons, List.prod_cons, DEdge.val, Sum.elim_inr]
  simp

/-- The counters of `oe1xT1loop`: `Δ(n_S, n_W, n_V, n_M) = (-1, 0, 0, 0)`, `ord Γ - 1` (no vertex is lost). -/
theorem oe1xT1loop_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) :
    (oe1xT1loop m Γ p).nS + 1 = Γ.nS ∧ (oe1xT1loop m Γ p).nW = Γ.nW ∧ (oe1xT1loop m Γ p).nV = Γ.nV ∧
      (oe1xT1loop m Γ p).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  exact ⟨by simp only [oe1xT1loop, LGraph.nS]; omega, rfl, rfl, lwStein_nM_congr _ _ rfl rfl⟩

/-- `(Oe1x)` as a graph operation for `y₁ = x` (the dotted edge `x = x` is trivial: term 1 is `oe1xT1loop`). -/
theorem oe1x_graph_E_loop (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (hx : p.1 = ⟨true, false, Sum.inr x, Sum.inr x⟩) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (oe1xT1loop m Γ p).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxT1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ((oe1xDs m Γ x (Sum.inr x) q).map fun T => ∫ ω, T.val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum).sum := by
  have e1 : ∫ ω, (oe1xT1d m Γ p x (Sum.inr x)).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (oe1xT1loop m Γ p).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => oe1xT1d_val_loop m Γ p x _ ℓe)
  have e2 : ((lwSplit p.2).map fun q => ∫ ω, (oe1xD m Γ x (Sum.inr x) q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
      ((lwSplit p.2).map fun q => ((oe1xDs m Γ x (Sum.inr x) q).map fun T => ∫ ω, T.val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) :=
    List.map_congr_left fun q _ => oe1xDs_integral hG hz (lwS sz n u) Sp M hM Γ x (Sum.inr x) q ℓe
  rw [oe1x_graph_Ed hG hz hu hm0 hzm Sp M hM Γ p hp x (Sum.inr x) hx ℓe, e1, e2]

end Oe1xGraphE

/-! ## 4. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`

(`N = (W L)^d = 27`; `m(0) = i`, `z_{1/2} = i/2`; `H_{1/2} = X / √2` on `27 × 27`.)  The merged instance data of T2107
(`lwWxInstSz`, `lwWxInstSp`, `lwWxInstM`, `lwWx_inst_*`); every deterministic hypothesis is discharged. -/

section Instances

/-- **Target 1 at the instance** (`P = 1`, `x = 0`, `(k₁, k₂, k₃, k₄) = (0, 1, 1, 0)`: one blue out-edge `G_{xy₁}`, one
red out-edge `Ḡ_{xy'₀}`, one blue in-edge `G_{w₀x}`, no red in-edge; `y₁ = y'₀ = (1,0,0) ≠ x`, `w₀ = x`): `(Oe1x)` on
`PF 3 3 1 (1/2)`, the pin `LWedgeExp 3` at `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`. -/
example := lwEdgeExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  0 1 1 0 (0 : Idx 3 3 1) ![Pi.single 0 1] ![Pi.single 0 1] ![0] ![] 1

/-- Target 1 at the instance with `y₁ = x` (the term `m 1_{x = y₁}` is present), all four counts positive
`(k₁, k₂, k₃, k₄) = (1, 1, 1, 1)`, and `f = Ḡ_{xx}` (a non-constant resolvent polynomial). -/
example := lwEdgeExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  1 1 1 1 (0 : Idx 3 3 1) ![0, Pi.single 0 1] ![Pi.single 0 1] ![Pi.single 1 1] ![Pi.single 2 1]
  (MvPolynomial.X (false, (0 : Idx 3 3 1), 0))

/-- Target 1 at `t = 0` (`G = m I`, `S = 0`). -/
example := lwEdgeExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 0 lwWx_inst_hE (le_refl 0) (by norm_num)
  0 1 1 0 (0 : Idx 3 3 1) ![Pi.single 0 1] ![Pi.single 0 1] ![0] ![] 1

/-- Target 1 at the merged instance of the pin (`Graph/LWPins.lean`, `inst_ssl`-style: `d = 3`, `L = 3`, `W = 2`,
`N = 216`, `g = 1`, `E = 0`, `t = 1/2`), for `(k₁, k₂, k₃, k₄) = (0, 1, 1, 0)`. -/
example := lwEdgeExp_holds 3 3 2 (le_refl 3) 1 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  0 1 1 0 (0 : Idx 3 3 2) ![Pi.single 0 1] ![Pi.single 0 1] ![0] ![] 1

/-- The graph `Γ` of the instance of target 2 (`E = Fin 4` external vertices `a, b, c, e`, `I = Fin 2` internal vertices
`x = 0`, `u = 1`): the solid edges `G_{xa}` (`e₀`, `y₁ = a`), `G_{xu}` (a blue out-edge), `Ḡ_{xb}` (a red out-edge),
`G_{cx}` (a blue in-edge), `Ḡ_{ex}` (a red in-edge), `Ḡ_{ua}` (an edge of `f`), the waved edge `S_{xu}`. -/
def oe1xInstGraph (m : ℂ) : LGraph (Fin 4) (Fin 2) where
  solid := [⟨true, false, Sum.inr 0, Sum.inl 0⟩, ⟨true, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨false, false, Sum.inr 0, Sum.inl 1⟩, ⟨true, false, Sum.inl 2, Sum.inr 0⟩,
    ⟨false, false, Sum.inl 3, Sum.inr 0⟩, ⟨false, false, Sum.inr 1, Sum.inl 0⟩]
  waved := [⟨false, true, Sum.inr 0, Sum.inr 1⟩]
  dotted := []
  coeff := m

/-- The pair `p = (e₀, other solid edges)` of the instance. -/
def oe1xInstP : SEdge (Fin 4 ⊕ Fin 2) × List (SEdge (Fin 4 ⊕ Fin 2)) :=
  (⟨true, false, Sum.inr 0, Sum.inl 0⟩, [⟨true, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨false, false, Sum.inr 0, Sum.inl 1⟩, ⟨true, false, Sum.inl 2, Sum.inr 0⟩,
    ⟨false, false, Sum.inl 3, Sum.inr 0⟩, ⟨false, false, Sum.inr 1, Sum.inl 0⟩])

theorem oe1xInst_mem : oe1xInstP ∈ lwSplit (oe1xInstGraph (mE 0)).solid := by
  simp [oe1xInstP, oe1xInstGraph, lwSplit]

theorem oe1xInst_hv : (Sum.inl 0 : Fin 4 ⊕ Fin 2) ≠ Sum.inr 0 := by simp

/-- **Target 2 at the instance** (identity of expectations of values, `x = 0`, `y₁ = a = inl 0`; `gaussIBP` proved, every
other hypothesis deterministic: `M = m I`, `Im z_t > 0`, `z_t + t m = -m⁻¹`, `m ≠ 0`; `Sp := lwWxInstSp` is not used). -/
example := oe1x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hM (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) rfl
  oe1xInst_hv (fun _ => 0)

/-- Target 2 with the dotted form of term 1 (`oe1x_graph_Ed`, valid also for `y₁ = x`): the same graph, `v = inr 1` (an
internal vertex `u ≠ x`). -/
example := oe1x_graph_Ed (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hM (oe1xInstGraph (mE 0))
  (⟨true, false, Sum.inr 0, Sum.inr 1⟩, [⟨true, false, Sum.inr 0, Sum.inl 0⟩,
    ⟨false, false, Sum.inr 0, Sum.inl 1⟩, ⟨true, false, Sum.inl 2, Sum.inr 0⟩,
    ⟨false, false, Sum.inl 3, Sum.inr 0⟩, ⟨false, false, Sum.inr 1, Sum.inl 0⟩])
  (by simp [oe1xInstGraph, lwSplit]) 0 (Sum.inr 1) rfl (fun _ => 0)

/-- The red out-edge `Ḡ_{xb}` of the instance, as an element of `lwSplit p.2` (`k₂`-term). -/
def oe1xInstQr : SEdge (Fin 4 ⊕ Fin 2) × List (SEdge (Fin 4 ⊕ Fin 2)) :=
  (⟨false, false, Sum.inr 0, Sum.inl 1⟩, [⟨true, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨true, false, Sum.inl 2, Sum.inr 0⟩, ⟨false, false, Sum.inl 3, Sum.inr 0⟩,
    ⟨false, false, Sum.inr 1, Sum.inl 0⟩])

/-- The blue in-edge `G_{cx}` of the instance (`k₃`-term). -/
def oe1xInstQb : SEdge (Fin 4 ⊕ Fin 2) × List (SEdge (Fin 4 ⊕ Fin 2)) :=
  (⟨true, false, Sum.inl 2, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨false, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, false, Sum.inl 3, Sum.inr 0⟩,
    ⟨false, false, Sum.inr 1, Sum.inl 0⟩])

/-- The edge `Ḡ_{ua}` of `f` (term 9). -/
def oe1xInstQf : SEdge (Fin 4 ⊕ Fin 2) × List (SEdge (Fin 4 ⊕ Fin 2)) :=
  (⟨false, false, Sum.inr 1, Sum.inl 0⟩, [⟨true, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨false, false, Sum.inr 0, Sum.inl 1⟩, ⟨true, false, Sum.inl 2, Sum.inr 0⟩,
    ⟨false, false, Sum.inl 3, Sum.inr 0⟩])

theorem oe1xInst_memr : oe1xInstQr ∈ lwSplit oe1xInstP.2 := by
  simp [oe1xInstQr, oe1xInstP, lwSplit]

theorem oe1xInst_memb : oe1xInstQb ∈ lwSplit oe1xInstP.2 := by
  simp [oe1xInstQb, oe1xInstP, lwSplit]

theorem oe1xInst_memf : oe1xInstQf ∈ lwSplit oe1xInstP.2 := by
  simp [oe1xInstQf, oe1xInstP, lwSplit]

/-- The counters of the instance graph `Γ` and of its terms, computed (`(n_S, n_W, n_V, n_M)`): `Γ = (6, 1, 2, 1)`;
term 1 (`oe1xT1`, `y₁ = a` external): `(5, 1, 1, 1)`; term 2 (`owxT1`): `(7, 2, 3, 1)`; the red out-edge `Ḡ_{xb}`:
`oe1xP5 = (7, 2, 3, 1)`, `oe1xP3 = (6, 2, 3, 1)`; the blue in-edge `G_{cx}`: `oe1xP6 = (7, 2, 3, 1)`,
`oe1xP4 = (6, 2, 3, 1)`; the edge `Ḡ_{ua}` of `f`: `oe1xD = (7, 2, 3, 1)`. -/
example :
    let Γ := oe1xInstGraph 1
    (Γ.nS, Γ.nW, Γ.nV, Γ.nM) = (6, 1, 2, 1) ∧
    ((oe1xT1 1 Γ oe1xInstP 0 (Sum.inl 0) oe1xInst_hv).nS, (oe1xT1 1 Γ oe1xInstP 0 (Sum.inl 0) oe1xInst_hv).nW,
      (oe1xT1 1 Γ oe1xInstP 0 (Sum.inl 0) oe1xInst_hv).nV) = (5, 1, 1) ∧
    ((owxT1 1 Γ 0).nS, (owxT1 1 Γ 0).nW, (owxT1 1 Γ 0).nV, (owxT1 1 Γ 0).nM) = (7, 2, 3, 1) ∧
    ((oe1xP5 1 Γ 0 (Sum.inl 0) oe1xInstQr).nS, (oe1xP5 1 Γ 0 (Sum.inl 0) oe1xInstQr).nW,
      (oe1xP5 1 Γ 0 (Sum.inl 0) oe1xInstQr).nV, (oe1xP5 1 Γ 0 (Sum.inl 0) oe1xInstQr).nM) = (7, 2, 3, 1) ∧
    ((oe1xP3 1 Γ 0 (Sum.inl 0) oe1xInstQr).nS, (oe1xP3 1 Γ 0 (Sum.inl 0) oe1xInstQr).nW,
      (oe1xP3 1 Γ 0 (Sum.inl 0) oe1xInstQr).nV, (oe1xP3 1 Γ 0 (Sum.inl 0) oe1xInstQr).nM) = (6, 2, 3, 1) ∧
    ((oe1xP6 1 Γ 0 (Sum.inl 0) oe1xInstQb).nS, (oe1xP6 1 Γ 0 (Sum.inl 0) oe1xInstQb).nW,
      (oe1xP6 1 Γ 0 (Sum.inl 0) oe1xInstQb).nV, (oe1xP6 1 Γ 0 (Sum.inl 0) oe1xInstQb).nM) = (7, 2, 3, 1) ∧
    ((oe1xP4 1 Γ 0 (Sum.inl 0) oe1xInstQb).nS, (oe1xP4 1 Γ 0 (Sum.inl 0) oe1xInstQb).nW,
      (oe1xP4 1 Γ 0 (Sum.inl 0) oe1xInstQb).nV, (oe1xP4 1 Γ 0 (Sum.inl 0) oe1xInstQb).nM) = (6, 2, 3, 1) ∧
    ((oe1xD 1 Γ 0 (Sum.inl 0) oe1xInstQf).nS, (oe1xD 1 Γ 0 (Sum.inl 0) oe1xInstQf).nW,
      (oe1xD 1 Γ 0 (Sum.inl 0) oe1xInstQf).nV, (oe1xD 1 Γ 0 (Sum.inl 0) oe1xInstQf).nM) = (7, 2, 3, 1) := by
  decide

/-- The counter theorems applied at the instance (every hypothesis discharged): term 1, and the derivative terms of the
red out-edge, the blue in-edge and the edge of `f`. -/
example := oe1xT1_counters (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInst_hv
example := oe1xT1_ord (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInst_hv
example := owxT1_counters (mE 0) (oe1xInstGraph (mE 0)) 0
example := owxT1_ord (mE 0) (oe1xInstGraph (mE 0)) 0
example := oe1xDs_counters (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQr oe1xInst_memr
example := oe1xDs_ord (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQr oe1xInst_memr
example := oe1xDs_counters (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQb oe1xInst_memb
example := oe1xDs_ord (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQb oe1xInst_memb
example := oe1xDs_counters (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQf oe1xInst_memf
example := oe1xDs_ord (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQf oe1xInst_memf

/-- The classification of `oe1xDs` at the instance (computed): the red out-edge gives the pair `[oe1xP5, oe1xP3]`, the blue
in-edge the pair `[oe1xP6, oe1xP4]`, the edge of `f` the single graph `oe1xD`. -/
example : (oe1xDs 1 (oe1xInstGraph 1) 0 (Sum.inl 0) oe1xInstQr).length = 2 ∧
    (oe1xDs 1 (oe1xInstGraph 1) 0 (Sum.inl 0) oe1xInstQb).length = 2 ∧
    (oe1xDs 1 (oe1xInstGraph 1) 0 (Sum.inl 0) oe1xInstQf).length = 1 := by
  decide

/-- **The Stein step at the instance** (`oe1x_integral`, `f = G_{00}`, `x = y = 0`): `E[G_{xy} f]` is the expectation of the
three-term integrand; `gaussIBP` proved, `f = G_{00}` a non-constant resolvent polynomial. -/
example := oe1x_integral (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  (lwPoly_tame1 (sz := lwWxInstSz) (n := 0) lwWx_inst_im (1 / 2)
    (MvPolynomial.X ((0 : Idx 3 3 1), 0, true))) (0 : Idx 3 3 1) 0

/-- A graph with `e₀ = G_{xx}` a weight (`y₁ = x`): `E = Fin 1`, `I = Fin 1`, the solid edges `G_{xx}` (`e₀`), `G_{xa}`,
`Ḡ_{ax}`. -/
def oe1xInstGraphL (m : ℂ) : LGraph (Fin 1) (Fin 1) where
  solid := [⟨true, false, Sum.inr 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 0⟩,
    ⟨false, false, Sum.inl 0, Sum.inr 0⟩]
  waved := []
  dotted := []
  coeff := m

theorem oe1xInstL_mem : ((⟨true, false, Sum.inr 0, Sum.inr 0⟩ : SEdge (Fin 1 ⊕ Fin 1)),
    [(⟨true, false, Sum.inr 0, Sum.inl 0⟩ : SEdge (Fin 1 ⊕ Fin 1)), ⟨false, false, Sum.inl 0, Sum.inr 0⟩]) ∈
    lwSplit (oe1xInstGraphL (mE 0)).solid := by
  simp [oe1xInstGraphL, lwSplit]

/-- **Target 2 for `y₁ = x`** (`oe1x_graph_E_loop`) at the instance, and the counters of `oe1xT1loop` (computed and by
`oe1xT1loop_counters`). -/
example := oe1x_graph_E_loop (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hM (oe1xInstGraphL (mE 0))
  (⟨true, false, Sum.inr 0, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inl 0⟩, ⟨false, false, Sum.inl 0, Sum.inr 0⟩])
  oe1xInstL_mem 0 rfl (fun _ => 0)

example := oe1xT1loop_counters (mE 0) (oe1xInstGraphL (mE 0))
  (⟨true, false, Sum.inr 0, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inl 0⟩, ⟨false, false, Sum.inl 0, Sum.inr 0⟩])
  oe1xInstL_mem

example :
    let Γ := oe1xInstGraphL 1
    let p : SEdge (Fin 1 ⊕ Fin 1) × List (SEdge (Fin 1 ⊕ Fin 1)) :=
      (⟨true, false, Sum.inr 0, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inl 0⟩, ⟨false, false, Sum.inl 0, Sum.inr 0⟩])
    (Γ.nS, Γ.nW, Γ.nV, Γ.nM) = (3, 0, 1, 1) ∧
    ((oe1xT1loop 1 Γ p).nS, (oe1xT1loop 1 Γ p).nW, (oe1xT1loop 1 Γ p).nV, (oe1xT1loop 1 Γ p).nM) = (2, 0, 1, 1) := by
  decide

end Instances

end RBM.Graph
