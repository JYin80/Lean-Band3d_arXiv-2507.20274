/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAAtom
import RBM3D.Graph.LWPins

/-!
# BA-L3c1 (T2420), part 2: the tail, `(G_by_auxG_BA)`, the nested form, the G4 pin

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex` (`B:line`), `paper/tex/7_8_light_weight.tex` (`7_8:line`):
`(G_by_auxG_BA)` (`B:486-490`, "by repeating the argument of `GtoAG`", `7_8:907-928`), the bound of the auxiliary graph by
`Anp` (`B:491-497`).  Part 1 is `Graph/BAAtom` (the vocabulary, `scaleatom`, the pointwise bound on a confined labelling, the
roots of the molecular forest); this file imports it.  The BA twin of `Graph/AuxGraph` §§8-12.

## Contents (namespace `RBM.Graph`, private prefix `BAAtom_`)

6. **The tail on a non-confined labelling** (twin of `AuxGraph` §8, `7_8:255-258`): the weights `f_j e^{(c/2) d_B}` of the four kernels
   `S`, `S⁺`, `M`, `g Ψ` (`M`, `g Ψ` offset-diagonal), the pointwise tail bound, the tail sum.
7. **G3, `(G_by_auxG_BA)`** (`B:486-490`): `BAGtoAG`, `baGtoAG_holds` (deterministic form: `‖G - M‖ ≤ Ψ` entrywise, no `hM : M = m I`,
   window `W^{-d} ≤ A Ψ²`), and `baGtoAG_E` with the constants of the BA model depending on `(d, Λ, κ)` only.
8. **The nested form** `baAuxNested_holds` (the walks of `lem:localregular` (3)-(5) of the shadow) and **G4** `BAAnpAux` (`B:491-497`,
   the pin of L3d1).
9. Compiled instances at `d = 3`, `L = 4`, `W = 2`.

Paper-delta candidates (report (d)): `T2420a` the auxiliary graph at the molecule centres (retained atoms folded in; same order),
`T2420b` the window `W^{-d} ≤ A Ψ²`, `A = g² + 1`, `T2420c` the exponent identity `ord Γ - ord Γ^aux = n_S^{within} + 2 (n_W - n_A + n_M)`.
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

/-! ## 6. The tail on a non-confined labelling (twin of `AuxGraph` §8, `7_8:255-258`) -/

section Tail

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The weights of the tail: `f_j · e^{(c/2) d_B}` (the weighted kernels `S`, `S⁺`, `M`, `g Ψ` of `7_8:255-258`). -/
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

/-- **The pointwise tail bound** (`7_8:255-258`): if some `J`-edge has block distance `> r`, then
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

/-- The size identity `N^{n_M} (K₀ W^{-d})^{n_W-(n_A-n_M)} = K₀^{n_W-(n_A-n_M)} (L^d)^{n_M} W^{-d(n_W-n_A)}` (`N = (W L)^d`; a copy
of the private `BASizeClaim_size_alg`, `BASizeClaim2.lean:446`). -/
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

/-- **The tail sum** (`7_8:255-258`): the sum over all labellings of the internal vertices of the weighted bound is
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

/-! ## 7. G3: `(G_by_auxG_BA)` (`B:486-490`), the main sum and the assembly -/

section Main

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The main sum** (`7_8:922-926`): the sum over the labels of the internal vertices of the confined bound is
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

/-- **G3, `(G_by_auxG_BA)`** (`B:486-490`, the BA twin of `LWGtoAG`, `AuxGraph.lean:979`), deterministic form: a normal BA graph whose
distinct external vertices lie in distinct molecules, data with `‖G - M‖ ≤ Ψ` entrywise (no `hM : M = m I`), the window
`W^{-d} ≤ A Ψ²`, the `LWKBound`s of `S`, `S⁺`, `M`, `g Ψ`, one decay `(C, c)` of the four kernels (`M`, `g Ψ` offset-diagonal),
and `ξ ≥ 0` dominating `‖G - M‖` on the `R`-balls, `R ≥ |E ⊕ I| r`:
`|Γ| ≤ C_Γ(K₀ A, K₁, Kd) Ψ^{ord Γ - ord Γ^aux} (W^d)^{n_M} Γ^aux_{[ℓe]} + e^{-cr/2} C'_Γ size(Γ)`. -/
def BAGtoAG (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I), Γ.Normal → (∀ a b : E, Γ.mol (Sum.inl a) = Γ.mol (Sum.inl b) → a = b) →
    ∀ (D : BALData (Idx d L W)) (Ψ A K₀ K₁ Kd C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
      (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A → ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2 →
      LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ → LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ →
      LWKBound D.M Kd Kd → LWKBound D.gPsi Kd Kd → 0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
        ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) →
      0 ≤ r → (Fintype.card (E ⊕ I) : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
      (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
        (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
      ∀ ℓe : E → Idx d L W,
        ‖Γ.val D ℓe‖ ≤
          Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
              (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) +
            Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
              Γ.scalingSize Ψ W d L

/-- **G3, deterministic form** (`B:486-490`): the argument of `lwGtoAG_holds` on the shadow with the atomic forest (per-edge
constants: a tree waved edge costs `K₁`, a non-tree one `K₀ W^{-d} ≤ K₀ A Ψ²`, a dotted edge `Kd`), the `‖G - M‖ ≤ Ψ` bound on
every circled solid edge, and the weighted kernels `S`, `S⁺`, `M`, `g Ψ` for the tail.  `hext` is not used (as for the band,
paper-delta candidate `T2170f`). -/
theorem baGtoAG_holds (d : ℕ) : BAGtoAG d := by
  intro hd L W _ _ E I _ _ _ _ Γ hN hext D Ψ A K₀ K₁ Kd C c r R ξ hG hA hwin hS hSp hM hP hC hc hSd hSpd hMPd hoff hr hRr hξ0 hξ ℓe
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG (fun _ => 0) (fun _ => 0))
  have hWpos : (0 : ℝ) < ((W : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hWpos d
  have hK₀' : 0 ≤ K₀ * ((W : ℝ) ^ d)⁻¹ := (norm_nonneg _).trans (hS.1 (fun _ => 0) (fun _ => 0))
  have hK₀ : 0 ≤ K₀ := by
    by_contra h
    push Not at h
    have : K₀ * ((W : ℝ) ^ d)⁻¹ < 0 := mul_neg_of_neg_of_pos h (inv_pos.2 hWd)
    linarith
  have : Fintype (LGraph.AuxIMol Γ.shadow) := Fintype.ofFinite _
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hmS := Γ.molSolid_length_le
  obtain ⟨root, hrootinj, hroot, hmain⟩ := BAAtom_main_sum Γ hN D hξ0 hS hSp hM hP ℓe
  have htail := BAAtom_tail_sum (r := r) hd Γ hN D hΨ hC hc hSd hSpd hMPd hoff ℓe
  have ha : K₀ * ((W : ℝ) ^ d)⁻¹ ≤ K₀ * (A * Ψ ^ 2) := mul_le_mul_of_nonneg_left hwin hK₀
  have hapow : (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) ≤
      (K₀ * A) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nA - Γ.nM))) := by
    calc (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) ≤ (K₀ * (A * Ψ ^ 2)) ^ (Γ.nW - (Γ.nA - Γ.nM)) :=
          pow_le_pow_left₀ hK₀' ha _
      _ = _ := by rw [← mul_assoc, mul_pow, ← pow_mul, mul_comm 2]
  have hexp : Γ.scalingOrder - Γ.auxOrd =
      (((Γ.nS - Γ.shadow.molSolid.length) + 2 * (Γ.nW - (Γ.nA - Γ.nM)) : ℕ) : ℤ) := by
    rw [Γ.scalingOrder_sub_auxOrd]
    unfold BAGraph.nS BAGraph.nW at *
    omega
  rw [hexp, zpow_natCast]
  have hav0 := Γ.auxVal_nonneg ξ hξ0 (fun a => (split d L W (ℓe a)).1)
  have hK₁ : 0 ≤ K₁ := (Finset.sum_nonneg fun y _ => norm_nonneg _).trans (hS.2.1 (fun _ => 0))
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hM.1 (fun _ => 0) (fun _ => 0))
  have hmain' : ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) ≤
      Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ ((Γ.nS - Γ.shadow.molSolid.length) + 2 * (Γ.nW - (Γ.nA - Γ.nM))) *
        (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) := by
    rw [← Finset.mul_sum]
    have hcn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) := by positivity
    calc ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) * ∑ ℓi : I → Idx d L W,
          ((Γ.shadow.molSolid.map fun e => ξ
              (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
              (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
            ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))
        ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) *
            (K₁ ^ (Γ.nA - Γ.nM) * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) *
              Kd ^ (Γ.mdot.length + Γ.psi.length))) :=
          mul_le_mul_of_nonneg_left hmain hcn
      _ ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) *
            (K₁ ^ (Γ.nA - Γ.nM) * ((K₀ * A) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nA - Γ.nM)))) *
              Kd ^ (Γ.mdot.length + Γ.psi.length))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcn
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hav0)
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hapow (by positivity)
      _ = _ := by
          unfold BAGraph.sizeConst
          rw [pow_add]
          ring
  have hpt : ∀ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤
      ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
    intro ℓi
    have hMn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
      have h1 : 0 ≤ (Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod :=
        List.prod_nonneg fun y hy => by
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
          exact hξ0 _ _
      have h2 : 0 ≤ ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) :=
        Finset.prod_nonneg fun j _ => BAAtom_nonneg_fJ _ _ _ _ _
      positivity
    have hTl : 0 ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
      have h2 : 0 ≤ ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) :=
        Finset.prod_nonneg fun j _ => BAAtom_fJw_nonneg _ _ _ _ _ _
      positivity
    by_cases hconf : ∀ j : Γ.Jx, (lwBdist d L W (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) : ℝ) ≤ r
    · exact (BAAtom_term_conf Γ hN D hG hξ hr hRr ℓe ℓi root hroot hconf).trans (le_add_of_nonneg_right hTl)
    · push Not at hconf
      exact (BAAtom_term_tail Γ hN D hG hc _ hconf).trans (le_add_of_nonneg_left hMn)
  unfold BAGraph.val
  calc ‖∑ ℓi : I → Idx d L W, Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ∑ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ℓi : I → Idx d L W, (‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))) :=
        Finset.sum_le_sum fun ℓi _ => hpt ℓi
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hmain' htail

end RBM.Graph

end
