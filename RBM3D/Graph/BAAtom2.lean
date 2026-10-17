/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAAtom
import RBM3D.Graph.LWPins
import RBM3D.Graph.AnpKey6

/-!
# Atoms and the auxiliary graph at block Anderson (part 2): the tail, the main sum, the nested form

Paper: Subappendix B.3, proof of Lemma B.7 (`lem_lweight`): (B.25) `G_by_auxG_BA` ("by repeating
the argument of `GtoAG`", proof of Lemma 7.21), and the bound of the auxiliary graph by `Anp`
(Lemma 7.22).  Part 1 is `Graph/BAAtom` (the vocabulary, `scaleatom`, the pointwise bound on a
confined labelling, the roots of the molecular forest); this file imports it.  It is the BA
counterpart of `Graph/AuxGraph` (Sections 8-12).

## Contents (namespace `RBM.Graph`, private prefix `BAAtom_`)

1. **The tail on a non-confined labelling** (as `AuxGraph` Section 8): the weights
   `f_j e^{(c/2) d_B}` of the four kernels `S`, `S⁺`, `M`, `g Ψ` (`M`, `g Ψ` offset-diagonal),
   the pointwise tail bound `BAAtom_term_tail`, the tail sum `BAAtom_tail_sum`.
2. **(B.25) `G_by_auxG_BA`**: the main sum `BAAtom_main_sum`.
3. **The constants of the BA model**: `BAAtom_decay_E` (constants of `(d, Λ, κ)` only).
4. **The nested form** `baAuxNested_holds` (the walks of Lemma 7.17 (`lem:localregular`) (3)-(5)
   of the shadow).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss

/-! ## 1. The tail on a non-confined labelling (as `AuxGraph` Section 8) -/

section Tail

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The weights of the tail: `f_j · e^{(c/2) d_B}` (the weighted kernels `S`, `S⁺`, `M`, `g Ψ`, cf. (7.18) `eq:estSpm-W`). -/
def BAAtom_fJw (Γ : BAGraph E I) (D : BALData (Idx d L W)) (c : ℝ) : Γ.Jx → Idx d L W → Idx d L W → ℝ :=
  fun j x y => BAAtom_fJ Γ D j x y * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ))

theorem BAAtom_fJw_nonneg (Γ : BAGraph E I) (D : BALData (Idx d L W)) (c : ℝ) (j : Γ.Jx) (x y : Idx d L W) :
    0 ≤ BAAtom_fJw Γ D c j x y :=
  mul_nonneg (BAAtom_nonneg_fJ Γ D j x y) (Real.exp_pos _).le

/-- A product of exponentials of non-negative numbers, one of which exceeds `r`, is at least `e^{t r}` (over a `Fintype`). -/
private theorem BAAtom_prod_exp_ge {α : Type*} [Fintype α] (g : α → ℝ) {t r : ℝ} (ht : 0 ≤ t)
    (hg : ∀ x, 0 ≤ g x) (hex : ∃ x, r ≤ g x) :
    Real.exp (t * r) ≤ ∏ x, Real.exp (t * g x) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.2
  obtain ⟨x0, hx0⟩ := hex
  have h1 : g x0 ≤ ∑ x, g x := Finset.single_le_sum (f := g) (fun x _ => hg x) (Finset.mem_univ x0)
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hx0.trans h1) ht

/-- **The pointwise tail bound**: if some `J`-edge has block distance `> r`, then
`|term ℓ| ≤ |coeff| Ψ^{n_S} e^{-cr/2} ∏_J f_j e^{(c/2) d_B}` (the product over the weighted kernels). -/
theorem BAAtom_term_tail (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ c r : ℝ}
    (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hc : 0 < c) (ℓ : E ⊕ I → Idx d L W)
    (hbad : ∃ j : Γ.Jx, r < (lwBdist d L W (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) : ℝ)) :
    ‖Γ.term D ℓ‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
      ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2)) := by
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG (fun _ => 0) (fun _ => 0))
  have h1 := BAAtom_term_le0 Γ D ℓ
  have h2 := BAAtom_solid_prod_le Γ hN D hG ℓ
  set P : ℝ := ∏ j : Γ.Jx, BAAtom_fJ Γ D j (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => BAAtom_nonneg_fJ _ _ _ _ _
  have hw : ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) =
      P * ∏ j : Γ.Jx, Real.exp ((c / 2) * (lwBdist d L W (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) : ℝ)) := by
    unfold BAAtom_fJw
    rw [Finset.prod_mul_distrib]
  have hexp := BAAtom_prod_exp_ge (fun j : Γ.Jx => (lwBdist d L W (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) : ℝ))
    (t := c / 2) (r := r) (by linarith) (fun j => Nat.cast_nonneg _) (by
      obtain ⟨j, hj⟩ := hbad
      exact ⟨j, hj.le⟩)
  set Q := ∏ j : Γ.Jx, Real.exp ((c / 2) * (lwBdist d L W (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) : ℝ)) with hQ
  have h3 : 1 ≤ Real.exp (-(c * r / 2)) * Q := by
    calc (1 : ℝ) = Real.exp (-(c * r / 2)) * Real.exp (c / 2 * r) := by
          rw [← Real.exp_add]; ring_nf; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
  rw [hw]
  have hcn : 0 ≤ ‖Γ.coeff‖ := norm_nonneg _
  calc ‖Γ.term D ℓ‖ ≤ ‖Γ.coeff‖ * (Γ.solid.map fun e => ‖SEdge.val D.toLData ℓ e‖).prod * P := h1
    _ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * P := by gcongr
    _ = ‖Γ.coeff‖ * Ψ ^ Γ.nS * (P * 1) := by rw [mul_one]
    _ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (P * (Real.exp (-(c * r / 2)) * Q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hP0) (mul_nonneg hcn (pow_nonneg hΨ _))
    _ = _ := by ring

/-- The row sums of a kernel supported on one offset with the entry decay `C e^{-c' d_B}`: `Σ_y ≤ C expC(d-2, c')`
(one `y` per block in the fibre, `Σ_b e^{-c'|[x] - b|} ≤ expC`). -/
private theorem BAAtom_fibre_row (hd : 3 ≤ d) {C c' : ℝ} (hC : 0 ≤ C) (hc : 0 < c') (x : Idx d L W) :
    ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then
      C * Real.exp (-(c' * (lwBdist d L W x y : ℝ))) else 0) ≤ C * expC (d - 2) c' := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have h1 := BASizeClaim_fibre_sum x
    (fun b : Zd (k + 2) L => C * Real.exp (-(c' * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))))
  have h2 : ∑ b : Zd (k + 2) L, Real.exp (-(c' * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))) ≤
      expC k c' := by
    refine le_trans (le_of_eq ?_) (sum_radial_exp_decay_le (L := L) k hc)
    exact Fintype.sum_equiv (Equiv.subLeft _) _ _ fun b => rfl
  simp only [lwBdist]
  rw [h1, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h2 hC

/-- **The `LWKBound` of an offset-diagonal kernel** with the entry decay `C e^{-c' d_B}` (the kernels `M`, `g Ψ`, weighted):
entries `≤ C`, row and column sums `≤ C expC(d-2, c')`. -/
theorem BAAtom_offdiag_kbound (hd : 3 ≤ d) {C c' : ℝ} (hC : 0 ≤ C) (hc : 0 < c')
    {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → K x y = 0)
    (h : ∀ x y, ‖K x y‖ ≤ C * Real.exp (-(c' * (lwBdist d L W x y : ℝ)))) :
    LWKBound K C (C * expC (d - 2) c') := by
  have hpt : ∀ x y, ‖K x y‖ ≤ (if (split d L W x).2 = (split d L W y).2 then
      C * Real.exp (-(c' * (lwBdist d L W x y : ℝ))) else 0) := by
    intro x y
    by_cases ho : (split d L W x).2 = (split d L W y).2
    · simp only [ho, ↓reduceIte]
      exact h x y
    · simp only [ho, ↓reduceIte, hoff x y ho, norm_zero]
      exact le_rfl
  refine ⟨fun x y => (h x y).trans ?_, fun x => ?_, fun y => ?_⟩
  · have : Real.exp (-(c' * (lwBdist d L W x y : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have : 0 ≤ c' * (lwBdist d L W x y : ℝ) := by positivity
      linarith
    nlinarith [Real.exp_pos (-(c' * (lwBdist d L W x y : ℝ)))]
  · exact (Finset.sum_le_sum fun y _ => hpt x y).trans (BAAtom_fibre_row hd hC hc x)
  · refine (Finset.sum_le_sum fun x _ => ?_).trans (BAAtom_fibre_row hd hC hc y)
    have := hpt x y
    have h2 : (if (split d L W x).2 = (split d L W y).2 then
        C * Real.exp (-(c' * (lwBdist d L W x y : ℝ))) else 0) =
        (if (split d L W y).2 = (split d L W x).2 then
          C * Real.exp (-(c' * (lwBdist d L W y x : ℝ))) else 0) := by
      rw [lwBdist_comm d L W y x]
      simp only [eq_comm]
    rw [h2] at this
    exact this

/-- A waved-edge weight is bounded by the common bound of `S` and `S⁺` (symmetric in the two labels). -/
theorem BAAtom_wval_decay {D : LData (Idx d L W)} {B : Idx d L W → Idx d L W → ℝ}
    (hB : ∀ x y, B x y = B y x) (hS : ∀ x y, ‖D.S x y‖ ≤ B x y) (hSp : ∀ x y, ‖D.Sp x y‖ ≤ B x y)
    (e : WEdge (E ⊕ I)) (x y : Idx d L W) : ‖lwWVal D e x y‖ ≤ B x y := by
  unfold lwWVal
  by_cases hc : e.col = true
  · by_cases hσ : e.σ = true
    · simp only [hc, hσ, ite_true]; exact hSp x y
    · have hσ' : e.σ = false := by simpa using hσ
      simp only [hc, hσ', ite_true, Bool.false_eq_true, ite_false, norm_star]
      rw [hB x y]
      exact hSp y x
  · have hc' : e.col = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]; exact hS x y

private theorem BAAtom_kbound_of_real {ι : Type} [Fintype ι] {g : ι → ι → ℝ} (hg : ∀ x y, 0 ≤ g x y) {a K₁ : ℝ}
    (h : LWKBound (Matrix.of fun x y => ((g x y : ℝ) : ℂ)) a K₁) :
    (∀ x y, g x y ≤ a) ∧ (∀ x, ∑ y, g x y ≤ K₁) ∧ (∀ y, ∑ x, g x y ≤ K₁) := by
  have hn : ∀ x y, ‖((g x y : ℝ) : ℂ)‖ = g x y := fun x y => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hg x y)]
  refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
  · have := h.1 x y
    simp only [Matrix.of_apply, hn] at this
    exact this
  · have := h.2.1 x
    simp only [Matrix.of_apply, hn] at this
    exact this
  · have := h.2.2 y
    simp only [Matrix.of_apply, hn] at this
    exact this

/-- **The weighted weights satisfy the bounds of the peeling sum** (`BAAtom_sum_J` for `f_j e^{(c/2) d_B}`): the waved edges have
entries `≤ C W^{-d}` and row and column sums `≤ C expC(d-2, c/2)`, the `M`- and `Ψ`-dotted edges entries and sums
`≤ C (1 + expC(d-2, c/2))`. -/
theorem BAAtom_fJw_bounds (hd : 3 ≤ d) (Γ : BAGraph E I) (D : BALData (Idx d L W)) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSp : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hMP : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) :
    (∀ (j : Fin Γ.waved.length) x y, BAAtom_fJw Γ D c (Sum.inl j) x y ≤ C * ((W : ℝ) ^ d)⁻¹) ∧
    (∀ (j : Fin Γ.waved.length) x, ∑ y, BAAtom_fJw Γ D c (Sum.inl j) x y ≤ C * expC (d - 2) (c / 2)) ∧
    (∀ (j : Fin Γ.waved.length) y, ∑ x, BAAtom_fJw Γ D c (Sum.inl j) x y ≤ C * expC (d - 2) (c / 2)) ∧
    (∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) x y, BAAtom_fJw Γ D c (Sum.inr j) x y ≤ C * (1 + expC (d - 2) (c / 2))) ∧
    (∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) x, ∑ y, BAAtom_fJw Γ D c (Sum.inr j) x y ≤ C * (1 + expC (d - 2) (c / 2))) ∧
    (∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) y, ∑ x, BAAtom_fJw Γ D c (Sum.inr j) x y ≤ C * (1 + expC (d - 2) (c / 2))) := by
  have hc2 : 0 < c / 2 := by linarith
  have hE : 0 < expC (d - 2) (c / 2) := by unfold expC; positivity
  have hexp : ∀ x y : Idx d L W, Real.exp (-(c * (lwBdist d L W x y : ℝ))) * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) =
      Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ))) := fun x y => by
    rw [← Real.exp_add]; congr 1; ring
  have hB : ∀ x y : Idx d L W, C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) =
      C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W y x : ℝ))) := fun x y => by rw [lwBdist_comm d L W x y]
  have hwav : ∀ j : Fin Γ.waved.length, LWKBound (Matrix.of fun x y => ((BAAtom_fJw Γ D c (Sum.inl j) x y : ℝ) : ℂ))
      (C * ((W : ℝ) ^ d)⁻¹) (C * expC (d - 2) (c / 2)) := by
    intro j
    refine lwKBound_of_decay hd hC hc2 (fun x y => ?_)
    simp only [Matrix.of_apply, Complex.norm_real, Real.norm_of_nonneg (BAAtom_fJw_nonneg Γ D c _ x y)]
    unfold BAAtom_fJw BAAtom_fJ
    have h1 := BAAtom_wval_decay (D := D.toLData) hB hS hSp (Γ.waved.get j) x y
    calc ‖lwWVal D.toLData (Γ.waved.get j) x y‖ * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ))
        ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, hexp x y]
  have hdot : ∀ j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length,
      LWKBound (Matrix.of fun x y => ((BAAtom_fJw Γ D c (Sum.inr j) x y : ℝ) : ℂ)) C (C * expC (d - 2) (c / 2)) := by
    intro j
    refine BAAtom_offdiag_kbound hd hC hc2 (fun x y ho => ?_) (fun x y => ?_)
    · rcases j with j | j
      · simp only [Matrix.of_apply, BAAtom_fJw, BAAtom_fJ, (hoff x y ho).1, norm_zero, zero_mul, Complex.ofReal_zero]
      · simp only [Matrix.of_apply, BAAtom_fJw, BAAtom_fJ, (hoff x y ho).2, norm_zero, zero_mul, Complex.ofReal_zero]
    · simp only [Matrix.of_apply, Complex.norm_real, Real.norm_of_nonneg (BAAtom_fJw_nonneg Γ D c _ x y)]
      unfold BAAtom_fJw BAAtom_fJ
      rcases j with j | j
      · calc ‖D.M x y‖ * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ))
            ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) :=
              mul_le_mul_of_nonneg_right (hMP x y).1 (Real.exp_pos _).le
          _ = _ := by rw [mul_assoc, hexp x y]
      · calc ‖D.gPsi x y‖ * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ))
            ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) :=
              mul_le_mul_of_nonneg_right (hMP x y).2 (Real.exp_pos _).le
          _ = _ := by rw [mul_assoc, hexp x y]
  have hCE : C * expC (d - 2) (c / 2) ≤ C * (1 + expC (d - 2) (c / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have hC1 : C ≤ C * (1 + expC (d - 2) (c / 2)) := by nlinarith
  refine ⟨fun j x y => (BAAtom_kbound_of_real (fun x y => BAAtom_fJw_nonneg Γ D c _ x y) (hwav j)).1 x y,
    fun j x => (BAAtom_kbound_of_real (fun x y => BAAtom_fJw_nonneg Γ D c _ x y) (hwav j)).2.1 x,
    fun j y => (BAAtom_kbound_of_real (fun x y => BAAtom_fJw_nonneg Γ D c _ x y) (hwav j)).2.2 y,
    fun j x y => ((BAAtom_kbound_of_real (fun x y => BAAtom_fJw_nonneg Γ D c _ x y) (hdot j)).1 x y).trans hC1,
    fun j x => ((BAAtom_kbound_of_real (fun x y => BAAtom_fJw_nonneg Γ D c _ x y) (hdot j)).2.1 x).trans hCE,
    fun j y => ((BAAtom_kbound_of_real (fun x y => BAAtom_fJw_nonneg Γ D c _ x y) (hdot j)).2.2 y).trans hCE⟩

/-- The size identity `N^{n_M} (K₀ W^{-d})^{n_W-(n_A-n_M)} = K₀^{n_W-(n_A-n_M)} (L^d)^{n_M} W^{-d(n_W-n_A)}` (`N = (W L)^d`; as
the private `BASizeClaim_size_alg` of `Graph/BASizeClaim2.lean`). -/
private theorem BAAtom_size_alg (W d L nM nV nW : ℕ) (hW : (W : ℝ) ≠ 0) (h1 : nM ≤ nV) (h2 : nV - nM ≤ nW) (K₀ : ℝ) :
    ((((W * L) ^ d : ℕ) : ℝ)) ^ nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (nW - (nV - nM)) =
      K₀ ^ (nW - (nV - nM)) * (((L : ℝ) ^ d) ^ nM * (W : ℝ) ^ (-(d : ℤ) * ((nW : ℤ) - nV))) := by
  obtain ⟨t, ht⟩ : ∃ t, nW = (nV - nM) + t := ⟨nW - (nV - nM), by omega⟩
  have htt : nW - (nV - nM) = t := by omega
  have hexp : -(d : ℤ) * ((nW : ℤ) - nV) = ((d * nM : ℕ) : ℤ) - ((d * t : ℕ) : ℤ) := by
    have : (nW : ℤ) - nV = (t : ℤ) - nM := by omega
    rw [this]; push_cast; ring
  rw [htt, hexp, zpow_sub₀ hW, zpow_natCast, zpow_natCast]
  push_cast
  rw [mul_pow, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  field_simp
  rw [pow_mul (W : ℝ) d t]

/-- **The tail sum**: the sum over all labellings of the internal vertices of the weighted bound is
`≤ e^{-cr/2} C'_Γ size(Γ)`, `C'_Γ = Γ.sizeConst C (C expC(d-2, c/2)) (C (1 + expC(d-2, c/2)))` (the peeling sum `BAAtom_sum_J` on the
weighted kernels, with `Φ = 1`). -/
theorem BAAtom_tail_sum (hd : 3 ≤ d) (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ C c r : ℝ}
    (hΨ : 0 ≤ Ψ) (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSp : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hMP : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0)
    (ℓe : E → Idx d L W) :
    ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) ≤
      Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
        Γ.scalingSize Ψ W d L := by
  classical
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have : Fintype (LGraph.AuxIMol Γ.shadow) := Fintype.ofFinite _
  obtain ⟨hwa, hwr, hwc, hda, hdr, hdc⟩ := BAAtom_fJw_bounds hd Γ D hC hc hS hSp hMP hoff
  obtain ⟨root, -, -, hsum⟩ := BAAtom_sum_J Γ hN.1 (BAAtom_fJw Γ D c) (a := C * ((W : ℝ) ^ d)⁻¹)
    (K₁ := C * expC (d - 2) (c / 2)) (Kd := C * (1 + expC (d - 2) (c / 2)))
    (fun j x y => BAAtom_fJw_nonneg Γ D c j x y) hwa hwr hwc hda hdr hdc ℓe
  have h1 := hsum (fun _ => 1) (fun _ => zero_le_one)
  simp only [one_mul] at h1
  have hcardsum : ∑ x : LGraph.AuxIMol Γ.shadow → Idx d L W, (1 : ℝ) = (Fintype.card (Idx d L W) : ℝ) ^ Γ.nM := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul, mul_one, Nat.cast_pow]
    rw [auxGraph_card_aux, BAGraph.shadow_nM]
  rw [hcardsum] at h1
  have hcard : (Fintype.card (Idx d L W) : ℝ) = ((((W * L) ^ d : ℕ)) : ℝ) := by rw [card_Idx]
  rw [hcard] at h1
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  obtain ⟨hn1, hn2⟩ := Γ.counters_le hN.1
  have hal := BAAtom_size_alg W d L Γ.nM Γ.nA Γ.nW hW hn1 hn2 C
  have hE0 : 0 ≤ Real.exp (-(c * r / 2)) := (Real.exp_pos _).le
  have hA0 : 0 ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * Real.exp (-(c * r / 2)) := by positivity
  calc ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))
      = (‖Γ.coeff‖ * Ψ ^ Γ.nS * Real.exp (-(c * r / 2))) * ∑ ℓi : I → Idx d L W,
          ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓi _ => ?_
        ring
    _ ≤ (‖Γ.coeff‖ * Ψ ^ Γ.nS * Real.exp (-(c * r / 2))) *
          (((((W * L) ^ d : ℕ)) : ℝ) ^ Γ.nM * ((C * expC (d - 2) (c / 2)) ^ (Γ.nA - Γ.nM) *
            (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) *
            (C * (1 + expC (d - 2) (c / 2))) ^ (Γ.mdot.length + Γ.psi.length))) :=
        mul_le_mul_of_nonneg_left h1 hA0
    _ = (‖Γ.coeff‖ * Ψ ^ Γ.nS * Real.exp (-(c * r / 2))) * (C * expC (d - 2) (c / 2)) ^ (Γ.nA - Γ.nM) *
          (C * (1 + expC (d - 2) (c / 2))) ^ (Γ.mdot.length + Γ.psi.length) *
          (((((W * L) ^ d : ℕ)) : ℝ) ^ Γ.nM * (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM))) := by ring
    _ = _ := by
        rw [hal]
        unfold BAGraph.sizeConst BAGraph.scalingSize Counters.scalingSize
        simp only [BAGraph.counters]
        ring

end Tail

/-! ## 2. (B.25) `G_by_auxG_BA`: the main sum -/

section Main

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The main sum** (proof of Lemma 7.21): the sum over the labels of the internal vertices of the confined bound is
`≤ (W^d)^{n_M} Γ^aux_{[ℓe]} K₁^{n_A - n_M} a^{n_W - (n_A - n_M)} Kd^{#M + #Ψ}`, for one choice `root` of the roots of the
molecular forest (the same `root` as in the pointwise bound). -/
theorem BAAtom_main_sum (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {a K₁ Kd : ℝ}
    {ξ : Zd d L → Zd d L → ℝ} (hξ0 : ∀ a b, 0 ≤ ξ a b)
    (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁) (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd)
    (ℓe : E → Idx d L W) :
    ∃ root : LGraph.AuxIMol Γ.shadow → I, Function.Injective root ∧
      (∀ c, Γ.shadow.molOf (Sum.inr (root c)) = c.1) ∧
      ∑ ℓi : I → Idx d L W,
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) ≤
        ((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) *
          (K₁ ^ (Γ.nA - Γ.nM) * a ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)) := by
  classical
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have : Fintype (LGraph.AuxIMol Γ.shadow) := Fintype.ofFinite _
  obtain ⟨root, hrootinj, hroot, hsum⟩ := BAAtom_sum_J Γ hN.1 (BAAtom_fJ Γ D)
    (fun j x y => BAAtom_nonneg_fJ Γ D j x y)
    (fun j x y => (auxGraph_wval_bound hS hSp (Γ.waved.get j)).1 x y)
    (fun j x => (auxGraph_wval_bound hS hSp (Γ.waved.get j)).2.1 x)
    (fun j y => (auxGraph_wval_bound hS hSp (Γ.waved.get j)).2.2 y)
    (fun j x y => by rcases j with j | j; exacts [hM.1 x y, hP.1 x y])
    (fun j x => by rcases j with j | j; exacts [hM.2.1 x, hP.2.1 x])
    (fun j y => by rcases j with j | j; exacts [hM.2.2 y, hP.2.2 y]) ℓe
  refine ⟨root, hrootinj, hroot, ?_⟩
  set Φ : (LGraph.AuxIMol Γ.shadow → Idx d L W) → ℝ := fun x =>
    (Γ.shadow.molSolid.map fun e => ξ
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (x c)).1) e.src)
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (x c)).1) e.dst)).prod with hΦ
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x => List.prod_nonneg fun y hy => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
    exact hξ0 _ _
  have hmain := hsum Φ hΦ0
  have hblocks := auxGraph_sum_blocks (d := d) (L := L) (W := W) (Rt := LGraph.AuxIMol Γ.shadow)
    (fun b => (Γ.shadow.molSolid.map fun e => ξ
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) b e.src)
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) b e.dst)).prod)
  rw [auxGraph_card_aux, BAGraph.shadow_nM] at hblocks
  have hav := auxGraph_auxVal_eq Γ.shadow ξ (fun a => (split d L W (ℓe a)).1)
  have hΦsum : ∑ x : LGraph.AuxIMol Γ.shadow → Idx d L W, Φ x =
      ((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) := by
    unfold BAGraph.auxVal
    rw [hav]
    exact hblocks
  rw [hΦsum] at hmain
  exact hmain

end Main

/-! ## 3. The constants of the BA model  -/

section Model

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **The decay and the offset structure of the four kernels of the BA model**: one decay `(C, c)` depending on `(d, Λ, κ)` only of
`S`, `S⁺ = S W` (`baSpDecay`), `M` (`BAMB_decay_large`, through the fibre) and `g₀ Ψ` (nearest-neighbour entries `g₀ ≤ Λ`); `M` and
`g₀ Ψ` vanish between different offsets (`BAMres_fine_apply`, `PsiI`). -/
theorem BAAtom_decay_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
      RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
      (∀ x y : Idx d L W, ‖Matrix.of (BAlwS d L W t) x y‖ ≤
        C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
      (∀ x y : Idx d L W, ‖(Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) x y‖ ≤
        C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
      (∀ x y : Idx d L W, ‖BAlwM d L W g0 E m x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
        ‖((g0 : ℂ) • PsiI d L W) x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
      (∀ x y : Idx d L W, (split d L W x).2 ≠ (split d L W y).2 →
        BAlwM d L W g0 E m x y = 0 ∧ ((g0 : ℂ) • PsiI d L W) x y = 0) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hdec⟩ := baSpDecay d hd Λ κ hΛ hκ
  have hd0 : 0 < d := by omega
  have hc₂ := RBM.BA.BAct_rate_pos d Λ κ hd0 hΛ hκ
  set c₂ := RBM.BA.BAct_rate d Λ κ with hc₂def
  set C : ℝ := max (max C₁ c₂⁻¹) (Λ * Real.exp 1) with hCdef
  set c : ℝ := min (min c₁ c₂) 1 with hcdef
  have hC0 : 0 ≤ C := le_max_of_le_left (le_max_of_le_left hC₁.le)
  have hc0 : 0 < c := lt_min (lt_min hc₁ hc₂) one_pos
  have hmono : ∀ (v w u C' c' : ℝ), 0 ≤ w → 0 ≤ u → C' ≤ C → c ≤ c' → v ≤ C' * w * Real.exp (-(c' * u)) →
      v ≤ C * w * Real.exp (-(c * u)) := by
    intro v w u C' c' hw hu hC hc hv
    refine hv.trans (mul_le_mul (mul_le_mul_of_nonneg_right hC hw) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (mul_nonneg hC0 hw))
    nlinarith
  refine ⟨C, c, hC0, hc0, fun L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 => ?_⟩
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using hr.1.1.ne'
  obtain ⟨hdS, hdSp⟩ := hdec L W hL g0 E t m hg hgΛ hr ht0 ht1
  have hMapp : ∀ x y : Idx d L W, BAlwM d L W g0 E m x y = if (split d L W x).2 = (split d L W y).2 then
      RBM.BA.BAMB d L g0 (E : ℂ) m (split d L W x).1 (split d L W y).1 else 0 :=
    fun x y => RBM.BA.BAMres_fine_apply d L W g0 (E : ℂ) m hw x y
  have hPsi : ∀ x y : Idx d L W, ((g0 : ℂ) • PsiI d L W) x y = if (split d L W x).2 = (split d L W y).2 then
      (if Adj d L (split d L W x).1 (split d L W y).1 then (g0 : ℂ) else 0) else 0 := by
    intro x y
    rw [Matrix.smul_apply, smul_eq_mul, BAAtom_PsiI_apply]
    split_ifs <;> simp
  refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ⟨?_, ?_⟩, fun x y ho => ⟨?_, ?_⟩⟩
  · exact hmono _ _ _ C₁ c₁ (by positivity) (Nat.cast_nonneg _) (le_max_of_le_left (le_max_left _ _))
      ((min_le_left _ _).trans (min_le_left _ _)) (hdS x y)
  · exact hmono _ _ _ C₁ c₁ (by positivity) (Nat.cast_nonneg _) (le_max_of_le_left (le_max_left _ _))
      ((min_le_left _ _).trans (min_le_left _ _)) (hdSp x y)
  · rw [hMapp]
    split_ifs with ho
    · have := RBM.BA.BAMB_decay_large d L hL hd0 Λ g0 κ E m hΛ hg hgΛ hκ hr (split d L W x).1 (split d L W y).1
      have h1 := hmono _ 1 (lwBdist d L W x y : ℝ) c₂⁻¹ c₂ one_pos.le (Nat.cast_nonneg _)
        (le_max_of_le_left (le_max_right _ _)) ((min_le_left _ _).trans (min_le_right _ _))
        (by simpa [neg_mul, lwBdist] using this)
      simpa using h1
    · rw [norm_zero]; positivity
  · rw [hPsi]
    split_ifs with ho ha
    · have hd1 : (lwBdist d L W x y : ℝ) = 1 := by
        simp only [lwBdist]
        exact_mod_cast ha
      rw [hd1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg, mul_one]
      have h1 : Λ * Real.exp 1 ≤ C := le_max_right _ _
      have h2 : 1 ≤ Real.exp (-c) * Real.exp 1 := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith [min_le_right (min c₁ c₂) 1])
      have h3 : g0 * Real.exp 1 ≤ Λ * Real.exp 1 := mul_le_mul_of_nonneg_right hgΛ (Real.exp_pos 1).le
      nlinarith [Real.exp_pos (-c), Real.exp_pos 1]
    all_goals simp only [norm_zero]; positivity
  · rw [hMapp]; simp [ho]
  · rw [hPsi]; simp [ho]

end Model

/-! ## 4. The nested form of `Γ^aux` -/

/-- **The nested form of `Γ^aux`** (the BA counterpart of `lwAuxNested_holds` in `Graph/AuxGraph.lean`): the walks of `lem:localregular` (3)-(5)
of the shadow, the molecules `𝓜_x ≠ 𝓜_y`; an `NGraph` with `p` paths and `n_M` internal vertices, no ghost edge, of order
`ord Γ^aux`, whose value is the value of the aux graph for every symmetric `ξ`.  The aux graph of a BA graph at the molecule
centres is the band's on `BAGraph.shadow`, so this is `lwAuxNested_holds` on the shadow (no sum over non-centre atoms
remains in `Γ^aux`). -/
theorem baAuxNested_holds : ∀ (p : ℕ) (P : BAPGraph (Fin 2)), 0 < p → (BAShadowPG P).LocReg345 p →
    P.g.mol (Sum.inl (P.ext 0)) ≠ P.g.mol (Sum.inl (P.ext 1)) →
    ∃ Γa : NGraph p P.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = P.g.auxOrd ∧
      ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : P.E' → κ,
        Γa.val ξ (fun _ => be (P.ext 0)) (fun _ => be (P.ext 1)) = P.g.auxVal ξ be := by
  intro p P hp hLR hxy
  have hxy' : (BAShadowPG P).g.molOf (Sum.inl ((BAShadowPG P).ext 0)) ≠
      (BAShadowPG P).g.molOf (Sum.inl ((BAShadowPG P).ext 1)) := fun h =>
    hxy (BAAtom_mol_eq_of_mem P.g ((BAAtom_shadow_molOf_eq_iff P.g _ _).1 h)).symm
  obtain ⟨Γa, h1, h2, h3, h4⟩ := lwAuxNested_holds p (BAShadowPG P) hp hLR hxy'
  have key : ∀ (q : ℕ) (hq : q = P.g.nM) (Γa : NGraph p q), Γa.NoGhost → Γa.IsNested → Γa.ordN = P.g.auxOrd →
      (∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : P.E' → κ,
        Γa.val ξ (fun _ => be (P.ext 0)) (fun _ => be (P.ext 1)) = P.g.auxVal ξ be) →
      ∃ Γa : NGraph p P.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = P.g.auxOrd ∧
        ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : P.E' → κ,
          Γa.val ξ (fun _ => be (P.ext 0)) (fun _ => be (P.ext 1)) = P.g.auxVal ξ be := by
    intro q hq
    subst hq
    intro Γa h1 h2 h3 h4
    exact ⟨Γa, h1, h2, h3, h4⟩
  exact key _ (BAGraph.shadow_nM P.g) Γa h1 h2 h3 h4

end RBM.Graph

end
