/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.BASizeClaim2
import RBM3D.BA.GreenSchur

/-!
# BA-L3c1 (T2420), part 1: atoms and the auxiliary graph at BA

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex` (`B:line`) and
`paper/tex/7_8_light_weight.tex` (`7_8:line`): `scaleatom` (`B:317-318`), `Gyiyjatom`,
`Gyiyjatom2` (`B:424`, `B:432`), the auxiliary graph of a BA graph (`B:436-449`,
`(eq:ordGaux_BAM)`, `B:486`), `(G_by_auxG_BA)` (`B:486-490`, "by repeating the argument of
`GtoAG`").  Part 2 is `Graph/BAAtom2` (it imports this file).  This file is the BA twin of
`Graph/AuxGraph` §§1-2, §3, §5-7; there is nothing to port from RBM1D/RBM2D.

## Contents (namespace `RBM.Graph`, private prefix `BAAtom_`)

1. **Vocabulary.**  `BAGraph.shadow` (every `M`- and `Ψ`-dotted edge also a waved edge: the
   molecules, `n_M`, `IsExtMol`, `molSolid` are those of the band graph `shadow`),
   `BAGraph.auxVal`, `BAGraph.auxOrd`, `BAShadowPG`.
2. **The order comparison** `BAGraph.scalingOrder_sub_auxOrd`, `BAGraph.auxOrd_le_scalingOrder`
   (twin of `AuxGraph` §2).
3. **`scaleatom`, `Gyiyjatom`, `Gyiyjatom2`**: `baAtom_offset`, `baAtom_dist`,
   `baAtom_sedge_xi`, `baAtom_wedge`; `BAAtom_offdiag_E` (`M`, `g₀ Ψ` offset-diagonal).
4. **The pointwise bound on a confined labelling** `BAAtom_term_conf` (twin of `AuxGraph` §5
   with `‖G - M‖ ≤ Ψ` entrywise, no `hM : M = m I`).
5. **The roots of the molecular forest and the sum over the children** `BAAtom_exists_roots`,
   `BAAtom_forest_roots`, `BAAtom_sum_J` (twin of `AuxGraph` §6-7 with per-edge constants).
6. Compiled instances at `d = 3`, `L = 4`, `W = 2`.

The centre-level auxiliary graph is the band's on `BAGraph.shadow`: the retained atoms
`x_{i,j}` of `B:448` are folded into the molecule centre (paper-delta candidate `T2420a`); the
orders agree (report (a), E2).
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

/-! ## 1. The vocabulary of the auxiliary graph at BA -/

section Vocab

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `Γ` with every `M`-dotted and every `Ψ`-dotted edge also a waved edge: the molecules of `Γ` (`BAGraph.adj`: waved,
`=`-dotted, `Ψ`-dotted and `M`-dotted edges join) are the molecules of the shadow. -/
def BAGraph.shadow (Γ : BAGraph E I) : LGraph E I where
  solid := Γ.solid
  waved := Γ.waved ++ Γ.mdot.map (fun e => (⟨false, true, e.x, e.y⟩ : WEdge (E ⊕ I))) ++
    Γ.psi.map (fun e => (⟨false, true, e.x, e.y⟩ : WEdge (E ⊕ I)))
  dotted := Γ.dotted
  coeff := Γ.coeff

/-- The value of the auxiliary graph at the molecule centres (the construction of `B:436-449`, retained atoms folded in). -/
def BAGraph.auxVal {κ : Type} [Fintype κ] (Γ : BAGraph E I) (ξ : κ → κ → ℝ) (be : E → κ) : ℝ :=
  Γ.shadow.auxVal ξ be

/-- `ord(Γ^aux)` at the centre level: `#molecular solid edges - 2 n_M`. -/
def BAGraph.auxOrd (Γ : BAGraph E I) : ℤ := Γ.shadow.auxOrd

/-- The shadow has the adjacency of `Γ`: waved, `=`-dotted, `Ψ`-dotted and `M`-dotted edges join. -/
theorem BAAtom_shadow_adj (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.shadow.adj u v = Γ.adj u v := by
  simp only [BAGraph.adj, LGraph.adj, BAGraph.atomAdj, BAGraph.shadow, List.any_append, List.any_map,
    Function.comp_def]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true]
  tauto

/-- The molecules of `Γ` and of its shadow agree. -/
theorem BAGraph.shadow_mol (Γ : BAGraph E I) (v : E ⊕ I) : Γ.shadow.mol v = Γ.mol v := by
  have h : Γ.shadow.step = Γ.step := by
    funext s
    simp only [LGraph.step, BAGraph.step, BAAtom_shadow_adj]
  unfold LGraph.mol BAGraph.mol
  rw [h]

/-- `n_M` of the shadow is `n_M` of `Γ`. -/
theorem BAGraph.shadow_nM (Γ : BAGraph E I) : Γ.shadow.nM = Γ.nM := by
  have h : Γ.shadow.mol = Γ.mol := funext (BAGraph.shadow_mol Γ)
  unfold LGraph.nM BAGraph.nM
  rw [h]

/-- Two vertices are in one molecule of the shadow iff one is in the molecule of the other. -/
theorem BAAtom_shadow_molOf_eq_iff (Γ : BAGraph E I) (u v : E ⊕ I) :
    Γ.shadow.molOf u = Γ.shadow.molOf v ↔ v ∈ Γ.mol u := by
  rw [Γ.shadow.molOf_eq_iff, BAGraph.shadow_mol]

/-- The auxiliary graph has a non-negative value for non-negative edge variables. -/
theorem BAGraph.auxVal_nonneg {κ : Type} [Fintype κ] (Γ : BAGraph E I) (ξ : κ → κ → ℝ)
    (hξ : ∀ u v, 0 ≤ ξ u v) (be : E → κ) : 0 ≤ Γ.auxVal ξ be :=
  Γ.shadow.auxVal_nonneg ξ hξ be

/-- The molecule closure is an equivalence: a vertex of the molecule of `v` has the molecule of `v`. -/
theorem BAAtom_mol_eq_of_mem (Γ : BAGraph E I) {v w : E ⊕ I} (h : w ∈ Γ.mol v) : Γ.mol w = Γ.mol v := by
  rw [BAGraph.mem_mol_iff] at h
  have hs : ∀ x y, Γ.adj x y = true → Γ.adj y x = true := fun x y hxy => by
    have : Γ.adj x y = Γ.adj y x := by
      simp only [BAGraph.adj, RBM.Graph.LGraph.adj, BAGraph.atomAdj, or_comm]
    rwa [this] at hxy
  have hsymm : ∀ {x y : E ⊕ I}, Relation.ReflTransGen (fun a b => Γ.adj a b = true) x y →
      Relation.ReflTransGen (fun a b => Γ.adj a b = true) y x := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hs _ _ hbc) ih
  ext w'
  rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx; exact (hsymm h).trans hx

end Vocab

/-- The packed graph of the shadow (the input of the band's nested form `lwAuxNested_holds`). -/
def BAShadowPG (P : BAPGraph (Fin 2)) : PGraph (Fin 2) := ⟨P.E', P.I', P.ext, P.ext_surj, P.g.shadow⟩

/-! ## 2. The order comparison (twin of `AuxGraph` §2, `7_8:926`, `B:486`) -/

section Order

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `(eq:ordG_BA)` against the aux order: `ord Γ - ord Γ^aux = (n_S - |𝒢_ℳ|) + 2 (n_W - n_A + n_M)`. -/
theorem BAGraph.scalingOrder_sub_auxOrd (Γ : BAGraph E I) :
    Γ.scalingOrder - Γ.auxOrd =
      ((Γ.nS : ℤ) - (Γ.shadow.molSolid.length : ℤ)) + 2 * ((Γ.nW : ℤ) - (Γ.nA : ℤ) + (Γ.nM : ℤ)) := by
  simp only [BAGraph.scalingOrder, BAGraph.auxOrd, LGraph.auxOrd, BAGraph.counters, ord, BAGraph.shadow_nM]
  ring

/-- `|𝒢_ℳ| ≤ n_S`. -/
theorem BAGraph.molSolid_length_le (Γ : BAGraph E I) : Γ.shadow.molSolid.length ≤ Γ.nS :=
  Γ.shadow.molSolid_length_le

/-- `ord Γ^aux ≤ ord Γ` for a normal graph (`BAGraph.counters_le`). -/
theorem BAGraph.auxOrd_le_scalingOrder (Γ : BAGraph E I) (hN : Γ.Normal) : Γ.auxOrd ≤ Γ.scalingOrder := by
  have h1 := Γ.scalingOrder_sub_auxOrd
  have h2 := Γ.molSolid_length_le
  obtain ⟨h3, h4⟩ := Γ.counters_le hN.1
  omega

end Order

/-! ## 3. `scaleatom`, `Gyiyjatom`, `Gyiyjatom2` (`B:317-318`, `B:424`, `B:432`) -/

section Atoms

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- A non-zero term has non-zero `Ψ`-dotted, `M`-dotted and `=`/`×`-dotted factors. -/
private theorem BAAtom_factors_ne_zero (Γ : BAGraph E I) (D : BALData (Idx d L W)) (ℓ : E ⊕ I → Idx d L W)
    (h : Γ.term D ℓ ≠ 0) :
    (∀ e ∈ Γ.psi, BAPsiEdge.val D ℓ e ≠ 0) ∧ (∀ e ∈ Γ.mdot, BAMEdge.val D ℓ e ≠ 0) ∧
      (∀ e ∈ Γ.dotted, DEdge.val ℓ e ≠ 0) := by
  unfold BAGraph.term RBM.Graph.LGraph.term at h
  obtain ⟨h1, hM⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h2, hP⟩ := mul_ne_zero_iff.1 h1
  obtain ⟨h3, hD⟩ := mul_ne_zero_iff.1 h2
  refine ⟨fun e he hz => hP (List.prod_eq_zero (List.mem_map.2 ⟨e, he, hz⟩)),
    fun e he hz => hM (List.prod_eq_zero (List.mem_map.2 ⟨e, he, hz⟩)),
    fun e he hz => hD (List.prod_eq_zero (List.mem_map.2 ⟨e, he, hz⟩))⟩

/-- **`scaleatom`, first half** (`B:317-318`): atom-mates share one offset (`M`, `g Ψ` are offset-diagonal; the `=`-dotted
factors force equal labels). -/
theorem baAtom_offset (Γ : BAGraph E I) (D : BALData (Idx d L W))
    (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0)
    (ℓ : E ⊕ I → Idx d L W) (h : Γ.term D ℓ ≠ 0) (u v : E ⊕ I) (hv : v ∈ Γ.atom u) :
    (split d L W (ℓ u)).2 = (split d L W (ℓ v)).2 := by
  obtain ⟨hP, hM, hD⟩ := BAAtom_factors_ne_zero Γ D ℓ h
  have hstep : ∀ b c : E ⊕ I, Γ.atomAdj b c = true → (split d L W (ℓ b)).2 = (split d L W (ℓ c)).2 := by
    intro b c hbc
    unfold BAGraph.atomAdj at hbc
    rw [Bool.or_eq_true, Bool.or_eq_true] at hbc
    rcases hbc with (hd | hp) | hm
    · rw [List.any_eq_true] at hd
      obtain ⟨e, he, hde⟩ := hd
      rw [Bool.and_eq_true] at hde
      obtain ⟨hq, hde⟩ := hde
      have hz := hD e he
      unfold DEdge.val at hz
      have hxy : ℓ e.x = ℓ e.y := by
        by_contra hne
        apply hz
        have : ¬ ((ℓ e.x = ℓ e.y) ↔ (e.eq = true)) := fun hh => hne (hh.2 hq)
        simp [this]
      rcases of_decide_eq_true hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hxy]
      · rw [← h1, ← h2, hxy]
    · rw [List.any_eq_true] at hp
      obtain ⟨e, he, hde⟩ := hp
      have hz := hP e he
      have hne : D.gPsi (ℓ e.x) (ℓ e.y) ≠ 0 := hz
      have hso : (split d L W (ℓ e.x)).2 = (split d L W (ℓ e.y)).2 := by
        by_contra hh
        exact hne (hoff _ _ hh).2
      rcases of_decide_eq_true hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hso
      · rw [← h1, ← h2]; exact hso.symm
    · rw [List.any_eq_true] at hm
      obtain ⟨e, he, hde⟩ := hm
      have hz := hM e he
      have hne : D.M (ℓ e.x) (ℓ e.y) ≠ 0 := by
        intro h0
        apply hz
        unfold BAMEdge.val
        split_ifs <;> simp [h0]
      have hso : (split d L W (ℓ e.x)).2 = (split d L W (ℓ e.y)).2 := by
        by_contra hh
        exact hne (hoff _ _ hh).1
      rcases of_decide_eq_true hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hso
      · rw [← h1, ← h2]; exact hso.symm
  rw [BAGraph.mem_atom_iff] at hv
  induction hv with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hstep _ _ hbc)

/-- The entries of `Ψ = Ψ^{(B)} ⊗ I` (`PsiI`) in the block-offset form (a copy of the private `BASizeClaim_PsiI_apply`). -/
theorem BAAtom_PsiI_apply (x y : Idx d L W) :
    PsiI d L W x y = if (split d L W x).2 = (split d L W y).2 then
      (if Adj d L (split d L W x).1 (split d L W y).1 then (1 : ℂ) else 0) else 0 := by
  simp only [PsiI, PsiV, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, PsiB,
    Matrix.of_apply]
  have h1 : splitEquiv d L W x = split d L W x := rfl
  have h2 : splitEquiv d L W y = split d L W y := rfl
  rw [h1, h2]
  by_cases h : (split d L W x).2 = (split d L W y).2 <;> simp [h]

/-- **`M` and `g₀ Ψ` of the BA model are offset-diagonal** (the premise of `baAtom_offset`, `BAAtom_tail_sum`, `baGtoAG_holds`):
`BAMres_fine_apply` and the form of `PsiI`. -/
theorem BAAtom_offdiag_E (g0 E : ℝ) (m : ℂ) (hw : ((E : ℂ) + m).im ≠ 0) (x y : Idx d L W)
    (ho : (split d L W x).2 ≠ (split d L W y).2) :
    BAlwM d L W g0 E m x y = 0 ∧ ((g0 : ℂ) • PsiI d L W) x y = 0 := by
  refine ⟨?_, ?_⟩
  · rw [show BAlwM d L W g0 E m x y = _ from RBM.BA.BAMres_fine_apply d L W g0 (E : ℂ) m hw x y]
    simp [ho]
  · rw [Matrix.smul_apply, BAAtom_PsiI_apply]
    simp [ho]

/-- **`Gyiyjatom`** (`B:424`), deterministic: if every label is within `R` of its centre block `lab`, a circled solid edge is
`≤ ξ` of the centre blocks of its ends (the `hξ`-domination on `R`-balls). -/
theorem baAtom_sedge_xi {V : Type} (D : BALData (Idx d L W)) (ξ : Zd d L → Zd d L → ℝ) (R : ℝ)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b)
    (ℓ : V → Idx d L W) (lab : V → Zd d L) (hlab : ∀ v, (zdistD d L ((split d L W (ℓ v)).1 - lab v) : ℝ) ≤ R)
    (e : SEdge V) (he : e.circ = true) : ‖SEdge.val D.toLData ℓ e‖ ≤ ξ (lab e.src) (lab e.dst) := by
  have h := hξ (ℓ e.src) (ℓ e.dst) (lab e.src) (lab e.dst) (hlab _) (hlab _)
  unfold SEdge.val
  dsimp only
  simp only [he, ite_true]
  cases e.σ
  · simp only [Bool.false_eq_true, ite_false, norm_star]
    exact h
  · simp only [ite_true]
    exact h

end Atoms

/-! ## 4. The pointwise bounds (twin of `AuxGraph` §5, `7_8:914-921`): `‖G - M‖ ≤ Ψ` entrywise, no `hM : M = m I` -/

section Pointwise

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAAtom_norm_list_prod (l : List ℂ) : ‖l.prod‖ = (l.map fun z => ‖z‖).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem BAAtom_list_prod_le_pow (l : List ℝ) (Ψ : ℝ) (h0 : ∀ x ∈ l, 0 ≤ x) (h : ∀ x ∈ l, x ≤ Ψ) :
    l.prod ≤ Ψ ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons, List.length_cons, pow_succ]
    have hx0 := h0 x (List.mem_cons_self ..)
    have hx := h x (List.mem_cons_self ..)
    have hl0 : 0 ≤ l.prod := List.prod_nonneg fun y hy => h0 y (List.mem_cons_of_mem _ hy)
    have ih' := ih (fun y hy => h0 y (List.mem_cons_of_mem _ hy)) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have : 0 ≤ Ψ := hx0.trans hx
    calc x * l.prod ≤ Ψ * Ψ ^ l.length := mul_le_mul hx ih' hl0 this
      _ = _ := by ring

private theorem BAAtom_list_prod_fin {α : Type*} (l : List α) (g : α → ℝ) :
    (l.map g).prod = ∏ j : Fin l.length, g (l.get j) := by
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

/-- The weight of an edge of `J = waved ⊕ mdot ⊕ psi` at the labels `(x, y)` of its ends: the norm of its factor
(`S`, `S⁺` or `S⁻` for a waved edge, `M` for an `M`-dotted edge, `g Ψ` for a `Ψ`-dotted edge). -/
def BAAtom_fJ {ι : Type} (Γ : BAGraph E I) (D : BALData ι) : Γ.Jx → ι → ι → ℝ
  | Sum.inl j, x, y => ‖lwWVal D.toLData (Γ.waved.get j) x y‖
  | Sum.inr (Sum.inl _), x, y => ‖D.M x y‖
  | Sum.inr (Sum.inr _), x, y => ‖D.gPsi x y‖

private theorem BAAtom_mdot_norm {ι V : Type*} (D : BALData ι) (ℓ : V → ι) (e : BAMEdge V) :
    ‖BAMEdge.val D ℓ e‖ = ‖D.M (ℓ e.x) (ℓ e.y)‖ := by
  unfold BAMEdge.val
  split_ifs <;> simp

theorem BAAtom_nonneg_fJ {ι : Type} (Γ : BAGraph E I) (D : BALData ι) (j : Γ.Jx) (x y : ι) :
    0 ≤ BAAtom_fJ Γ D j x y := by
  rcases j with j | j | j <;> exact norm_nonneg _

/-- The product of the weights of the waved, `Ψ`-dotted and `M`-dotted factors is the product over `J`. -/
theorem BAAtom_prod_J {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : BAGraph E I) (D : BALData ι) (ℓ : E ⊕ I → ι) :
    (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod * (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod *
        (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod =
      ∏ j : Γ.Jx, BAAtom_fJ Γ D j (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, BAAtom_list_prod_fin, BAAtom_list_prod_fin,
    BAAtom_list_prod_fin]
  simp only [BAAtom_fJ, BAGraph.edgeEnds, BAAtom_mdot_norm]
  have hw : ∏ j : Fin Γ.waved.length, ‖WEdge.val D.toLData ℓ (Γ.waved.get j)‖ =
      ∏ j : Fin Γ.waved.length, ‖lwWVal D.toLData (Γ.waved.get j) (ℓ (Γ.waved.get j).x) (ℓ (Γ.waved.get j).y)‖ :=
    rfl
  have hp : ∏ j : Fin Γ.psi.length, ‖BAPsiEdge.val D ℓ (Γ.psi.get j)‖ =
      ∏ j : Fin Γ.psi.length, ‖D.gPsi (ℓ (Γ.psi.get j).x) (ℓ (Γ.psi.get j).y)‖ := rfl
  rw [hw, hp]
  ring

/-- A circled solid edge has the factor `(G - M)_{xy}` or its conjugate, `≤ Ψ` by the entry bound. -/
theorem BAAtom_sedge_le {ι V : Type*} (D : BALData ι) {Ψ : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ)
    (ℓ : V → ι) (e : SEdge V) (hc : e.circ = true) : ‖SEdge.val D.toLData ℓ e‖ ≤ Ψ := by
  unfold SEdge.val
  dsimp only
  simp only [hc, ite_true]
  cases e.σ
  · simp only [Bool.false_eq_true, ite_false, norm_star]
    exact hG _ _
  · simp only [ite_true]
    exact hG _ _

/-- **The norm of a term against its solid and its `J`-edge factors**: `|term| ≤ |coeff| ∏_{solid} |·| ∏_{J} f_j`
(the `=`/`×`-dotted factors are `0` or `1`). -/
theorem BAAtom_term_le0 {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : BAGraph E I) (D : BALData ι) (ℓ : E ⊕ I → ι) :
    ‖Γ.term D ℓ‖ ≤ ‖Γ.coeff‖ * (Γ.solid.map fun e => ‖SEdge.val D.toLData ℓ e‖).prod *
      ∏ j : Γ.Jx, BAAtom_fJ Γ D j (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) := by
  unfold BAGraph.term RBM.Graph.LGraph.term
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, BAAtom_norm_list_prod, BAAtom_norm_list_prod,
    BAAtom_norm_list_prod, BAAtom_norm_list_prod, BAAtom_norm_list_prod]
  simp only [List.map_map]
  have h3 : (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod ≤ 1 := by
    have := BAAtom_list_prod_le_pow (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)) 1 (by
        intro x hx
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _) (by
        intro x hx
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        simp only [Function.comp, DEdge.val]
        split_ifs <;> simp)
    simpa using this
  have h0s : 0 ≤ (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D.toLData ℓ)).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hw' : (Γ.waved.map ((fun z : ℂ => ‖z‖) ∘ WEdge.val D.toLData ℓ)).prod =
      (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod := rfl
  have hp' : (Γ.psi.map ((fun z : ℂ => ‖z‖) ∘ BAPsiEdge.val D ℓ)).prod =
      (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod := rfl
  have hm' : (Γ.mdot.map ((fun z : ℂ => ‖z‖) ∘ BAMEdge.val D ℓ)).prod =
      (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod := rfl
  have hs' : (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D.toLData ℓ)).prod =
      (Γ.solid.map fun e => ‖SEdge.val D.toLData ℓ e‖).prod := rfl
  rw [hw', hp', hm', hs', ← BAAtom_prod_J]
  have hwn : 0 ≤ (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hpn : 0 ≤ (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hmn : 0 ≤ (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have h0d : 0 ≤ (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hs0 := h0s
  rw [hs'] at hs0
  calc ‖Γ.coeff‖ * (Γ.solid.map fun e => ‖SEdge.val D.toLData ℓ e‖).prod *
        (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod *
        (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod *
        (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod * (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod
      ≤ ‖Γ.coeff‖ * (Γ.solid.map fun e => ‖SEdge.val D.toLData ℓ e‖).prod *
        (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod * 1 *
        (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod * (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod := by
        gcongr
    _ = _ := by ring

/-- The solid edges of a normal BA graph are each `≤ Ψ`. -/
theorem BAAtom_solid_prod_le {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : BAGraph E I) (hN : Γ.Normal)
    (D : BALData ι) {Ψ : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (ℓ : E ⊕ I → ι) :
    (Γ.solid.map fun e => ‖SEdge.val D.toLData ℓ e‖).prod ≤ Ψ ^ Γ.nS := by
  have := BAAtom_list_prod_le_pow (Γ.solid.map fun e => ‖SEdge.val D.toLData ℓ e‖) Ψ (by
      intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _) (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      exact BAAtom_sedge_le D hG ℓ e (hN.2 e he))
  simpa [BAGraph.nS] using this

/-- Every `J`-edge within block distance `r` puts every shadow waved edge within `r`. -/
theorem BAAtom_shadow_conf (Γ : BAGraph E I) (ℓ : E ⊕ I → Idx d L W) (r : ℝ)
    (hconf : ∀ j : Γ.Jx, (lwBdist d L W (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) : ℝ) ≤ r) :
    ∀ e ∈ Γ.shadow.waved, (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ) ≤ r := by
  intro e he
  simp only [BAGraph.shadow, List.mem_append, List.mem_map] at he
  rcases he with (he | ⟨e', he', rfl⟩) | ⟨e', he', rfl⟩
  · obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
    exact hconf (Sum.inl j)
  · obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he'
    exact hconf (Sum.inr (Sum.inl j))
  · obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he'
    exact hconf (Sum.inr (Sum.inr j))

/-- **The solid edges on a confined labelling** (`7_8:914-921`, `B:424`): the solid edges inside a molecule cost `Ψ`, the solid
edges between two molecules cost `ξ` of the blocks of the molecules (`hξ` and the confinement). -/
theorem BAAtom_solid_prod_conf (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ R r : ℝ}
    {ξ : Zd d L → Zd d L → ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b)
    (hr : 0 ≤ r) (hR : (Fintype.card (E ⊕ I) : ℝ) * r ≤ R)
    (ℓe : E → Idx d L W) (ℓi : I → Idx d L W) (root : LGraph.AuxIMol Γ.shadow → I)
    (hroot : ∀ c, Γ.shadow.molOf (Sum.inr (root c)) = c.1)
    (hconf : ∀ e ∈ Γ.shadow.waved, (lwBdist d L W (Sum.elim ℓe ℓi e.x) (Sum.elim ℓe ℓi e.y) : ℝ) ≤ r) :
    (Γ.solid.map fun e => ‖SEdge.val D.toLData (Sum.elim ℓe ℓi) e‖).prod ≤ Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
      (Γ.shadow.molSolid.map fun e => ξ
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod := by
  classical
  set ℓ : E ⊕ I → Idx d L W := Sum.elim ℓe ℓi with hℓ
  set Lab : Γ.shadow.Mol → Zd d L :=
    LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) with hLab
  set Pn : SEdge (E ⊕ I) → Bool := fun e => decide (¬ Γ.shadow.InsideMol e.src e.dst) with hPn
  have hms : Γ.shadow.molSolid = (Γ.solid.filter Pn).map (SEdge.map Γ.shadow.molOf) := rfl
  set X : SEdge (E ⊕ I) → ℝ := fun e => ξ (Lab (Γ.shadow.molOf e.src)) (Lab (Γ.shadow.molOf e.dst)) with hX
  have hmsmap : (Γ.shadow.molSolid.map fun e => ξ (Lab e.src) (Lab e.dst)) = (Γ.solid.filter Pn).map X := by
    rw [hms, List.map_map]; rfl
  have hmslen : Γ.shadow.molSolid.length = (Γ.solid.filter Pn).length := by rw [hms, List.length_map]
  rw [hmsmap, hmslen]
  have hB : (Γ.solid.map fun e => ‖SEdge.val D.toLData ℓ e‖).prod ≤
      (Γ.solid.map fun e => if Pn e = true then X e else Ψ).prod := by
    refine auxGraph_list_prod_le _ _ _ (fun e he => norm_nonneg _) (fun e he => ?_)
    have hc := hN.2 e he
    by_cases hin : Γ.shadow.InsideMol e.src e.dst
    · have : Pn e = false := by simp [hPn, hin]
      simp only [this, Bool.false_eq_true, ite_false]
      exact BAAtom_sedge_le D hG ℓ e hc
    · have : Pn e = true := by simp [hPn, hin]
      simp only [this, ite_true]
      exact baAtom_sedge_xi D ξ R hξ ℓ (fun v => Lab (Γ.shadow.molOf v))
        (fun v => auxGraph_lab_close Γ.shadow hN.1 ℓe ℓi root hroot hr hR hconf v) e hc
  rw [auxGraph_prod_filter] at hB
  have hlen : Γ.solid.length = Γ.nS := rfl
  rw [hlen] at hB
  rw [mul_comm]
  exact hB

/-- **The pointwise bound on a confined labelling** (`7_8:914-921`): every `J`-edge within block distance `r`:
`|term ℓ| ≤ |coeff| Ψ^{n_S - |𝒢_ℳ|} ∏_{𝒢_ℳ} ξ ∏_J f_j`, the blocks of the internal molecules being those of the roots. -/
theorem BAAtom_term_conf (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ R r : ℝ}
    {ξ : Zd d L → Zd d L → ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b)
    (hr : 0 ≤ r) (hR : (Fintype.card (E ⊕ I) : ℝ) * r ≤ R)
    (ℓe : E → Idx d L W) (ℓi : I → Idx d L W) (root : LGraph.AuxIMol Γ.shadow → I)
    (hroot : ∀ c, Γ.shadow.molOf (Sum.inr (root c)) = c.1)
    (hconf : ∀ j : Γ.Jx, (lwBdist d L W (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) : ℝ) ≤ r) :
    ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
      ((Γ.shadow.molSolid.map fun e => ξ
          (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
        ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
  have h1 := BAAtom_term_le0 Γ D (Sum.elim ℓe ℓi)
  have h2 := BAAtom_solid_prod_conf Γ hN D hG hξ hr hR ℓe ℓi root hroot (BAAtom_shadow_conf Γ _ r hconf)
  have hP : 0 ≤ ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) :=
    Finset.prod_nonneg fun j _ => BAAtom_nonneg_fJ _ _ _ _ _
  calc ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.coeff‖ * (Γ.solid.map fun e => ‖SEdge.val D.toLData (Sum.elim ℓe ℓi) e‖).prod *
        ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) := h1
    _ ≤ ‖Γ.coeff‖ * (Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
      (Γ.shadow.molSolid.map fun e => ξ
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod) *
        ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) := by
        gcongr
    _ = _ := by ring

end Pointwise

/-! ## 5. The roots of the molecular forest, the sum over the children (twin of `AuxGraph` §6-7, per-edge constants) -/

section Roots

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Two vertices joined by an edge of the shadow lie in one molecule of the shadow. -/
private theorem BAAtom_molOf_eq_of_adj (Γ : LGraph E I) {u v : E ⊕ I} (h : Γ.adj u v = true) :
    Γ.molOf u = Γ.molOf v := by
  by_cases huv : u = v
  · rw [huv]
  · exact SimpleGraph.ConnectedComponent.eq.2
      (SimpleGraph.Adj.reachable ((owx_molGraph_adj Γ u v).2 ⟨huv, h⟩))

/-- The two ends of every `J`-edge lie in one molecule of the shadow. -/
private theorem BAAtom_molOf_ends (Γ : BAGraph E I) (j : Γ.Jx) :
    Γ.shadow.molOf (Γ.edgeEnds j).1 = Γ.shadow.molOf (Γ.edgeEnds j).2 := by
  refine BAAtom_molOf_eq_of_adj Γ.shadow ?_
  unfold LGraph.adj
  rw [Bool.or_eq_true]
  left
  rw [List.any_eq_true]
  rcases j with j | j | j
  · refine ⟨Γ.waved.get j, ?_, ?_⟩
    · simp only [BAGraph.shadow, List.mem_append]
      exact Or.inl (Or.inl (List.get_mem _ j))
    · simp [BAGraph.edgeEnds]
  · refine ⟨⟨false, true, (Γ.mdot.get j).x, (Γ.mdot.get j).y⟩, ?_, ?_⟩
    · simp only [BAGraph.shadow, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨Γ.mdot.get j, List.get_mem _ j, rfl⟩)
    · simp [BAGraph.edgeEnds]
  · refine ⟨⟨false, true, (Γ.psi.get j).x, (Γ.psi.get j).y⟩, ?_, ?_⟩
    · simp only [BAGraph.shadow, List.mem_append, List.mem_map]
      exact Or.inr ⟨Γ.psi.get j, List.get_mem _ j, rfl⟩
    · simp [BAGraph.edgeEnds]

/-- **The roots of the molecular forest** (`BAGraph.exists_forest` with the root map): in the molecular forest of a graph without
`=`-dotted edges the children are exactly the internal vertices outside the range of an injective map `root` that picks one
vertex in every internal molecule of the shadow (`n_M` roots: `|C| + n_M = |I|`). -/
theorem BAAtom_exists_roots (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) :
    ∃ (root : LGraph.AuxIMol Γ.shadow → I) (C : Finset I) (par : I → E ⊕ I) (edge : I → Option Γ.Jx) (ρ : I → ℕ),
      Function.Injective root ∧ (∀ c, Γ.shadow.molOf (Sum.inr (root c)) = c.1) ∧
      (∀ i, i ∈ C ↔ i ∉ Set.range root) ∧ C.card + Γ.nM = Fintype.card I ∧
      (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card + Γ.nM = Γ.nA ∧
      (∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) ∧
      (∀ c ∈ C, ∃ j, edge c = some j ∧
        (((Γ.edgeEnds j).1 = Sum.inr c ∧ (Γ.edgeEnds j).2 = par c) ∨
         ((Γ.edgeEnds j).2 = Sum.inr c ∧ (Γ.edgeEnds j).1 = par c))) ∧
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, edge c₁ = edge c₂ → c₁ = c₂) := by
  classical
  obtain ⟨C, par, edge, ρ, hcard, hgcard, hrank, hedge, hinj⟩ := Γ.exists_forest hD
  have hmolpar : ∀ c ∈ C, Γ.shadow.molOf (par c) = Γ.shadow.molOf (Sum.inr c) := by
    intro c hc
    obtain ⟨j, hj, hends⟩ := hedge c hc
    have := BAAtom_molOf_ends Γ j
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at this; exact this.symm
    · rw [h1, h2] at this; exact this
  have hreach : ∀ n : ℕ, ∀ v : I, ρ v = n →
      ((∃ a : E, Γ.shadow.molOf (Sum.inl a) = Γ.shadow.molOf (Sum.inr v)) ∨
        ∃ w : I, w ∉ C ∧ Γ.shadow.molOf (Sum.inr w) = Γ.shadow.molOf (Sum.inr v)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      by_cases hvC : v ∈ C
      · rcases hpar : par v with a | w
        · left
          refine ⟨a, ?_⟩
          rw [← hmolpar v hvC, hpar]
        · have hlt := hrank v hvC w hpar
          have hmw : Γ.shadow.molOf (Sum.inr w) = Γ.shadow.molOf (Sum.inr v) := by
            rw [← hpar]; exact hmolpar v hvC
          rcases ih (ρ w) (hv ▸ hlt) w rfl with ⟨a, ha⟩ | ⟨w', hw'C, hw'⟩
          · left; exact ⟨a, ha.trans hmw⟩
          · right; exact ⟨w', hw'C, hw'.trans hmw⟩
      · right; exact ⟨v, hvC, rfl⟩
  have hMi : ∀ c : LGraph.AuxIMol Γ.shadow, ∃ w : I, w ∉ C ∧ Γ.shadow.molOf (Sum.inr w) = c.1 := by
    rintro ⟨c, hc⟩
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    rcases v with a | i
    · exact absurd ⟨a, rfl⟩ hc
    · rcases hreach _ i rfl with ⟨a, ha⟩ | ⟨w, hwC, hw⟩
      · exact absurd ⟨a, ha⟩ hc
      · exact ⟨w, hwC, hw⟩
  choose root hrootC hrootmol using hMi
  have hinjroot : Function.Injective root := by
    intro c c' h
    apply Subtype.ext
    rw [← hrootmol c, ← hrootmol c', h]
  refine ⟨root, C, par, edge, ρ, hinjroot, hrootmol, ?_, hcard, hgcard, hrank, hedge, hinj⟩
  have : Fintype (LGraph.AuxIMol Γ.shadow) := Fintype.ofFinite _
  have hsub : (Finset.univ.image root) ⊆ Cᶜ := by
    intro w hw
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hw
    exact Finset.mem_compl.2 (hrootC c)
  have hAuxCard : Fintype.card (LGraph.AuxIMol Γ.shadow) = Γ.nM := by
    rw [auxGraph_card_aux, BAGraph.shadow_nM]
  have hc1 : (Finset.univ.image root).card = Γ.nM := by
    rw [Finset.card_image_of_injective _ hinjroot, Finset.card_univ, hAuxCard]
  have hc2 : Cᶜ.card = Γ.nM := by
    rw [Finset.card_compl]; omega
  have heq : Finset.univ.image root = Cᶜ := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro i
  constructor
  · intro hi ⟨c, hc⟩
    exact hrootC c (hc ▸ hi)
  · intro hi
    by_contra hnC
    have : i ∈ Cᶜ := Finset.mem_compl.2 hnC
    rw [← heq] at this
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 this
    exact hi ⟨c, hc⟩

end Roots

section ForestSum

/-- **The sum over the children with the roots as external labels, per-edge constants** (the BA twin of
`auxGraph_forest_roots`, `AuxGraph.lean:551`, from `BASizeClaim_forest_sum_le` in place of `lwForest_sum_le`). -/
theorem BAAtom_forest_roots {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {E I Rt J : Type}
    [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype Rt] [DecidableEq Rt] [Fintype J] [DecidableEq J]
    (ℓe : E → ι) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (a K : J → ℝ)
    (hf0 : ∀ j x y, 0 ≤ f j x y) (hfa : ∀ j x y, f j x y ≤ a j)
    (hrow : ∀ j x, ∑ y, f j x y ≤ K j) (hcol : ∀ j y, ∑ x, f j x y ≤ K j)
    (root : Rt → I) (hroot : Function.Injective root) (C : Finset I) (hC : ∀ i, i ∈ C ↔ i ∉ Set.range root)
    (par : I → E ⊕ I) (edge : C → J) (ρ : I → ℕ) (hinj : Function.Injective edge)
    (hedge : ∀ c : C, (u (edge c) = Sum.inr c.1 ∧ v (edge c) = par c.1) ∨
      (v (edge c) = Sum.inr c.1 ∧ u (edge c) = par c.1))
    (hrank : ∀ c : C, ∀ w, par c.1 = Sum.inr w → ρ w < ρ c.1)
    (Φ : (Rt → ι) → ℝ) (hΦ : ∀ x, 0 ≤ Φ x) :
    ∑ ℓ : I → ι, Φ (fun t => ℓ (root t)) * ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) ≤
      (∑ x : Rt → ι, Φ x) * ((∏ c : C, K (edge c)) * ∏ j ∈ (Finset.univ.image edge)ᶜ, a j) := by
  classical
  let eI : Rt ⊕ C ≃ I :=
    (Equiv.sumCongr (Equiv.ofInjective root hroot) (Equiv.subtypeEquivRight hC)).trans
      (Equiv.sumCompl (· ∈ Set.range root))
  have heIl : ∀ t, eI (Sum.inl t) = root t := fun t => rfl
  have heIr : ∀ c : C, eI (Sum.inr c) = c.1 := fun c => rfl
  let e1 : (I → ι) ≃ (Rt → ι) × (C → ι) :=
    (Equiv.arrowCongr eI.symm (Equiv.refl ι)).trans (Equiv.sumArrowEquivProdArrow Rt C ι)
  have hsymm : ∀ (x : Rt → ι) (y : C → ι) (i : I), e1.symm (x, y) i = Sum.elim x y (eI.symm i) := fun _ _ _ => rfl
  have hcardI : Fintype.card Rt + Fintype.card C = Fintype.card I := by
    rw [← Fintype.card_sum]; exact Fintype.card_congr eI
  -- the relabelling of the vertices
  let φ : E ⊕ I → (E ⊕ Rt) ⊕ C := fun x => match x with
    | Sum.inl a => Sum.inl (Sum.inl a)
    | Sum.inr i => Sum.elim (fun m => Sum.inl (Sum.inr m)) Sum.inr (eI.symm i)
  have hφ : ∀ (x : Rt → ι) (y : C → ι) (z : E ⊕ I),
      Sum.elim (Sum.elim ℓe x) y (φ z) = Sum.elim ℓe (e1.symm (x, y)) z := by
    intro x y z
    rcases z with a | i
    · rfl
    · rw [Sum.elim_inr, hsymm]
      change Sum.elim (Sum.elim ℓe x) y (Sum.elim (fun m => Sum.inl (Sum.inr m)) Sum.inr (eI.symm i)) = _
      rcases eI.symm i with m | c <;> rfl
  have hroots : ∀ (x : Rt → ι) (y : C → ι) (t : Rt), e1.symm (x, y) (root t) = x t := by
    intro x y t
    rw [hsymm]
    have : eI.symm (root t) = Sum.inl t := by rw [Equiv.symm_apply_eq]; rfl
    rw [this]; rfl
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  -- the bound for fixed roots
  have hfix : ∀ x : Rt → ι, ∑ y : C → ι,
      ∏ j, f j (Sum.elim ℓe (e1.symm (x, y)) (u j)) (Sum.elim ℓe (e1.symm (x, y)) (v j)) ≤
        (∏ c : C, K (edge c)) * ∏ j ∈ (Finset.univ.image edge)ᶜ, a j := by
    intro x
    have hmain := BASizeClaim_forest_sum_le (ι := ι) (E := E ⊕ Rt) (I := C) (J := J) (Sum.elim ℓe x)
      (fun j => φ (u j)) (fun j => φ (v j)) f a K hf0 hfa hrow hcol (Finset.univ : Finset C)
      (fun c => φ (par c.1)) edge (fun c => ρ c.1)
      (fun c₁ _ c₂ _ h => hinj h)
      (fun c _ => by
        have hc : eI.symm c.1 = Sum.inr c := by rw [Equiv.symm_apply_eq]; rfl
        have hφc : φ (Sum.inr c.1) = Sum.inr c := by
          change Sum.elim (fun m => Sum.inl (Sum.inr m)) Sum.inr (eI.symm c.1) = _
          rw [hc]; rfl
        rcases hedge c with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by rw [h1, hφc], by rw [h2]⟩
        · exact Or.inr ⟨by rw [h1, hφc], by rw [h2]⟩)
      (fun c _ w hw => by
        rcases hpc : par c.1 with a' | i
        · rw [hpc] at hw
          exact absurd hw (by simp [φ])
        · rw [hpc] at hw
          change Sum.elim (fun m => Sum.inl (Sum.inr m)) Sum.inr (eI.symm i) = Sum.inr w at hw
          rcases hi : eI.symm i with m | c'
          · rw [hi] at hw; exact absurd hw (by simp)
          · rw [hi] at hw
            have hcw : c' = w := Sum.inr_injective hw
            have hi' : i = c'.1 := by rw [← heIr c', ← hi]; simp
            have := hrank c w.1 (by rw [hpc, hi', hcw])
            exact this)
    have h' : ∀ y : C → ι, ∏ j, f j (Sum.elim ℓe (e1.symm (x, y)) (u j)) (Sum.elim ℓe (e1.symm (x, y)) (v j)) =
        ∏ j, f j (Sum.elim (Sum.elim ℓe x) y (φ (u j))) (Sum.elim (Sum.elim ℓe x) y (φ (v j))) := by
      intro y; simp only [hφ]
    simp only [h', Finset.card_univ] at hmain ⊢
    have hpos : 0 < (Fintype.card ι : ℝ) ^ Fintype.card C := pow_pos hN _
    refine le_of_mul_le_mul_left ?_ hpos
    calc (Fintype.card ι : ℝ) ^ Fintype.card C * ∑ y : C → ι,
          ∏ j, f j (Sum.elim (Sum.elim ℓe x) y (φ (u j))) (Sum.elim (Sum.elim ℓe x) y (φ (v j)))
        ≤ (Fintype.card ι : ℝ) ^ Fintype.card C * (∏ c ∈ (Finset.univ : Finset C), K (edge c)) *
          ∏ j ∈ (Finset.univ.image edge)ᶜ, a j := hmain
      _ = _ := by ring
  -- the sum over the roots
  calc ∑ ℓ : I → ι, Φ (fun t => ℓ (root t)) * ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j))
      = ∑ q : (Rt → ι) × (C → ι), Φ (fun t => e1.symm q (root t)) *
          ∏ j, f j (Sum.elim ℓe (e1.symm q) (u j)) (Sum.elim ℓe (e1.symm q) (v j)) :=
        (Equiv.sum_comp e1.symm (fun ℓ : I → ι => Φ (fun t => ℓ (root t)) *
          ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)))).symm
    _ = ∑ x : Rt → ι, ∑ y : C → ι, Φ x *
          ∏ j, f j (Sum.elim ℓe (e1.symm (x, y)) (u j)) (Sum.elim ℓe (e1.symm (x, y)) (v j)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        simp only [hroots]
    _ = ∑ x : Rt → ι, Φ x * ∑ y : C → ι,
          ∏ j, f j (Sum.elim ℓe (e1.symm (x, y)) (u j)) (Sum.elim ℓe (e1.symm (x, y)) (v j)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ x : Rt → ι, Φ x * ((∏ c : C, K (edge c)) * ∏ j ∈ (Finset.univ.image edge)ᶜ, a j) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfix x) (hΦ x)
    _ = _ := by rw [Finset.sum_mul]

end ForestSum

section SumJ

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The algebra of the forest bound: a tree edge costs `K_j`, every other edge `a_j`; the dotted edges cost `Kd` in both
cases, the waved edges `K₁` or `a` (a copy of the private `BASizeClaim_alg_prod`, `BASizeClaim2.lean:193`). -/
private theorem BAAtom_alg_prod {I : Type} [Fintype I] [DecidableEq I] {p q r : ℕ} (a K₁ Kd : ℝ)
    (KJ aJ : Fin p ⊕ Fin q ⊕ Fin r → ℝ) (hK1 : ∀ jw, KJ (Sum.inl jw) = K₁) (hK2 : ∀ j', KJ (Sum.inr j') = Kd)
    (ha1 : ∀ jw, aJ (Sum.inl jw) = a) (ha2 : ∀ j', aJ (Sum.inr j') = Kd)
    (C : Finset I) (edgeT : I → Fin p ⊕ Fin q ⊕ Fin r) (hinj : Set.InjOn edgeT C) :
    (∏ c ∈ C, KJ (edgeT c)) * ∏ j ∈ (C.image edgeT)ᶜ, aJ j =
      K₁ ^ (C.filter fun c => ∃ jw, edgeT c = Sum.inl jw).card *
        a ^ (p - (C.filter fun c => ∃ jw, edgeT c = Sum.inl jw).card) * Kd ^ (q + r) := by
  classical
  set S := C.image edgeT with hS
  set TW := C.filter fun c => ∃ jw, edgeT c = Sum.inl jw with hTW
  have h1 : (∏ c ∈ C, KJ (edgeT c)) = ∏ j ∈ S, KJ j := (Finset.prod_image hinj).symm
  set g : Fin p ⊕ Fin q ⊕ Fin r → ℝ := fun j => if j ∈ S then KJ j else aJ j with hg
  have h2 : (∏ j ∈ S, KJ j) * ∏ j ∈ Sᶜ, aJ j = ∏ j, g j := by
    rw [← Finset.prod_mul_prod_compl S g]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by simp [hg, hj]
    · exact Finset.prod_congr rfl fun j hj => by simp [hg, (Finset.mem_compl.1 hj)]
  rw [h1, h2, Fintype.prod_sum_type, Fintype.prod_sum_type]
  have h3 : ∀ j', g (Sum.inr j') = Kd := fun j' => by
    simp only [hg]
    split_ifs
    · exact hK2 j'
    · exact ha2 j'
  simp only [h3, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_add]
  set U := Finset.univ.filter (fun jw : Fin p => Sum.inl jw ∈ S) with hU
  have h4 : ∏ jw : Fin p, g (Sum.inl jw) = K₁ ^ U.card * a ^ (p - U.card) := by
    have : ∀ jw : Fin p, g (Sum.inl jw) = if Sum.inl jw ∈ S then K₁ else a := fun jw => by
      simp only [hg]
      split_ifs
      · exact hK1 jw
      · exact ha1 jw
    simp only [this]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hUc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p)))
      (fun jw => Sum.inl jw ∈ S)
    rw [Finset.card_univ, Fintype.card_fin] at hUc
    have e1 : (Finset.univ.filter fun jw : Fin p => ¬ Sum.inl jw ∈ S).card = p - U.card := by
      simp only [hU]
      omega
    rw [e1]
  have h5 : U.card = TW.card := by
    symm
    refine Finset.card_bij (fun c hc => (Finset.mem_filter.1 hc).2.choose) (fun c hc => ?_)
      (fun c₁ h₁ c₂ h₂ h => ?_) (fun jw hjw => ?_)
    · have hc' := Finset.mem_filter.1 hc
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and, hS]
      rw [← hc'.2.choose_spec]
      exact Finset.mem_image_of_mem _ hc'.1
    · have h₁' := Finset.mem_filter.1 h₁
      have h₂' := Finset.mem_filter.1 h₂
      refine hinj h₁'.1 h₂'.1 ?_
      rw [h₁'.2.choose_spec, h₂'.2.choose_spec, h]
    · have hjw' : Sum.inl jw ∈ S := by simpa [hU] using hjw
      obtain ⟨c, hcC, hc⟩ := Finset.mem_image.1 hjw'
      have hcT : c ∈ TW := Finset.mem_filter.2 ⟨hcC, jw, hc⟩
      refine ⟨c, hcT, ?_⟩
      have h6 := (Finset.mem_filter.1 hcT).2.choose_spec
      exact Sum.inl_injective (h6.symm.trans hc)
  rw [h4, h5]

/-- **The sum over the internal labels with the roots as free labels, per-edge constants** (the BA twin of `auxGraph_main_sum`'s
use of `auxGraph_forest_roots`; `BASizeClaim_sum_le`, `BASizeClaim2.lean:317`, with a weight `Φ` of the labels of the roots):
for weights `f_j` (waved: entries `≤ a`, row and column sums `≤ K₁`; `M`- and `Ψ`-dotted: entries, row and column sums `≤ Kd`),
`Σ_{ℓ_I} Φ(ℓ ∘ root) ∏_J f_j ≤ (Σ_x Φ x) K₁^{n_A - n_M} a^{n_W - (n_A - n_M)} Kd^{#M + #Ψ}`. -/
theorem BAAtom_sum_J {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Γ : BAGraph E I)
    (hD : ∀ e ∈ Γ.dotted, e.eq = false) (f : Γ.Jx → ι → ι → ℝ) {a K₁ Kd : ℝ}
    (hf0 : ∀ j x y, 0 ≤ f j x y)
    (hwa : ∀ (j : Fin Γ.waved.length) x y, f (Sum.inl j) x y ≤ a)
    (hwr : ∀ (j : Fin Γ.waved.length) x, ∑ y, f (Sum.inl j) x y ≤ K₁)
    (hwc : ∀ (j : Fin Γ.waved.length) y, ∑ x, f (Sum.inl j) x y ≤ K₁)
    (hda : ∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) x y, f (Sum.inr j) x y ≤ Kd)
    (hdr : ∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) x, ∑ y, f (Sum.inr j) x y ≤ Kd)
    (hdc : ∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) y, ∑ x, f (Sum.inr j) x y ≤ Kd)
    [Fintype (LGraph.AuxIMol Γ.shadow)] [DecidableEq (LGraph.AuxIMol Γ.shadow)] (ℓe : E → ι) :
    ∃ root : LGraph.AuxIMol Γ.shadow → I, Function.Injective root ∧
      (∀ c, Γ.shadow.molOf (Sum.inr (root c)) = c.1) ∧
      ∀ Φ : (LGraph.AuxIMol Γ.shadow → ι) → ℝ, (∀ x, 0 ≤ Φ x) →
        ∑ ℓi : I → ι, Φ (fun t => ℓi (root t)) *
            ∏ j : Γ.Jx, f j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) ≤
          (∑ x : LGraph.AuxIMol Γ.shadow → ι, Φ x) *
            (K₁ ^ (Γ.nA - Γ.nM) * a ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)) := by
  classical
  obtain ⟨root, C, par, edge, ρ, hroot, hrootmol, hC, -, hgcard, hrank, hedge, hinj⟩ := BAAtom_exists_roots Γ hD
  refine ⟨root, hroot, hrootmol, fun Φ hΦ => ?_⟩
  choose edgeJ hedgeJ using fun c : C => hedge c.1 c.2
  have hinjJ : Function.Injective edgeJ := fun c₁ c₂ h =>
    Subtype.ext (hinj c₁.1 c₁.2 c₂.1 c₂.2 (by rw [(hedgeJ c₁).1, (hedgeJ c₂).1, h]))
  let aJ : Γ.Jx → ℝ := fun j => match j with
    | Sum.inl _ => a
    | Sum.inr _ => Kd
  let KJ : Γ.Jx → ℝ := fun j => match j with
    | Sum.inl _ => K₁
    | Sum.inr _ => Kd
  have hmain := BAAtom_forest_roots (ι := ι) (E := E) (I := I) (Rt := LGraph.AuxIMol Γ.shadow) (J := Γ.Jx) ℓe
    (fun j => (Γ.edgeEnds j).1) (fun j => (Γ.edgeEnds j).2) f aJ KJ hf0
    (by rintro (j | j) x y; exacts [hwa j x y, hda j x y])
    (by rintro (j | j) x; exacts [hwr j x, hdr j x])
    (by rintro (j | j) y; exacts [hwc j y, hdc j y])
    root hroot C hC par edgeJ ρ hinjJ (fun c => (hedgeJ c).2) (fun c => hrank c.1 c.2) Φ hΦ
  have halg := BAAtom_alg_prod (I := C) (p := Γ.waved.length) (q := Γ.mdot.length) (r := Γ.psi.length)
    a K₁ Kd KJ aJ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Finset.univ : Finset C) edgeJ
    hinjJ.injOn
  have hw : (Finset.univ.filter fun c : C => ∃ jw, edgeJ c = Sum.inl jw).card = Γ.nA - Γ.nM := by
    have h1 : (Finset.univ.filter fun c : C => ∃ jw, edgeJ c = Sum.inl jw).card =
        (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card := by
      refine Finset.card_bij (fun c _ => c.1) (fun c hc => ?_) (fun c₁ _ c₂ _ h => Subtype.ext h) (fun c hc => ?_)
      · obtain ⟨jw, hjw⟩ := (Finset.mem_filter.1 hc).2
        exact Finset.mem_filter.2 ⟨c.2, jw, by rw [(hedgeJ c).1, hjw]⟩
      · obtain ⟨hcC, jw, hjw⟩ := Finset.mem_filter.1 hc
        refine ⟨⟨c, hcC⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, jw, ?_⟩, rfl⟩
        have := (hedgeJ ⟨c, hcC⟩).1
        rw [hjw] at this
        exact (Option.some.inj this).symm
    omega
  rw [halg, hw] at hmain
  exact hmain

end SumJ

/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 4`, `W = 2`, the flow point `P : FlowPt 4 10`, `t = 1/2`)

The BA data are those of `BASizeClaimInst2`: `D0` (`M = BAlwM`, `S`, `S⁺ = S W`, `g₀ Ψ` at `P`, `G = M + 1/100`, so
`|Ǧ_{xy}| = 1/100` for all `x, y`, the diagonal included), `ellInst` the labels of the two external vertices.  The graph `G*`
(normal, every solid edge circled, no `=`-dotted edge): externals `a = inl 0`, `b = inl 1`, internals `u₁ .. u₅ = inr 0 .. inr 4`;
solid `a → u₁`, `u₅ → b` (red), `u₃ → u₂`, `u₁ → u₄`; waved `S(a, u₃)`, `S⁺(u₂, u₄)`, `S(u₁, u₅)`; `M̄`-dotted `u₁ u₂`, `Ψ`-dotted `u₄ u₅`.
Atoms `{a}, {b}, {u₁, u₂}, {u₃}, {u₄, u₅}`, molecules `{a, u₃}`, `{b}`, `{u₁, u₂, u₄, u₅}`; `(n_S, n_W, n_A, n_M) = (4, 3, 3, 1)`,
`|𝒢_ℳ| = 3`, `ord Γ = 4`, `ord Γ^aux = 1`. -/

end RBM.Graph

end
