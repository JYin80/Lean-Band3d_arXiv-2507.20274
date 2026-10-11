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

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex` (cited `B:line`) and `paper/tex/7_8_light_weight.tex`
(`7_8:line`): `scaleatom` (`B:317-318`), `Gyiyjatom`, `Gyiyjatom2` (`B:424`, `B:432`), the auxiliary graph of a BA graph
(`B:436-449`, `(eq:ordGaux_BAM)`, `B:486`), `(G_by_auxG_BA)` (`B:486-490`, "by repeating the argument of `GtoAG`").
Part 2 is `Graph/BAAtom2` (it imports this file).  The BA twin of `Graph/AuxGraph` §§1-2, §3, §5-7.

## Contents (namespace `RBM.Graph`, private prefix `BAAtom_`)

1. **Vocabulary.**  `BAGraph.shadow` (every `M`- and `Ψ`-dotted edge also a waved edge: the molecules, `n_M`, `IsExtMol`, `molSolid` are
   those of the band graph `shadow`), `BAGraph.auxVal`, `BAGraph.auxOrd`, `BAShadowPG`; the order comparison
   `BAGraph.scalingOrder_sub_auxOrd`, `BAGraph.auxOrd_le_scalingOrder` (twin of `AuxGraph` §2).
2. **`scaleatom`, `Gyiyjatom`, `Gyiyjatom2`** (the four `baAtom_*` statements).
3. **The pointwise bound on a confined labelling** (twin of `AuxGraph` §5 with `‖G - M‖ ≤ Ψ` entrywise, no `hM : M = m I`).
4. **The roots of the molecular forest and the sum over the children** (twin of `AuxGraph` §6-7, per-edge constants).

The centre-level auxiliary graph is the band's on `BAGraph.shadow`: the retained atoms `x_{i,j}` of `B:448` are folded into the
molecule centre (paper-delta candidate `T2420a`); the orders agree (`T2420`, report (a) E2).
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
theorem BAGraph.shadow_adj (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.shadow.adj u v = Γ.adj u v := by
  simp only [BAGraph.adj, LGraph.adj, BAGraph.atomAdj, BAGraph.shadow, List.any_append, List.any_map,
    Function.comp_def]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true]
  tauto

/-- The molecules of `Γ` and of its shadow agree. -/
theorem BAGraph.shadow_mol (Γ : BAGraph E I) (v : E ⊕ I) : Γ.shadow.mol v = Γ.mol v := by
  have h : Γ.shadow.step = Γ.step := by
    funext s
    simp only [LGraph.step, BAGraph.step, BAGraph.shadow_adj]
  unfold LGraph.mol BAGraph.mol
  rw [h]

/-- `n_M` of the shadow is `n_M` of `Γ`. -/
theorem BAGraph.shadow_nM (Γ : BAGraph E I) : Γ.shadow.nM = Γ.nM := by
  have h : Γ.shadow.mol = Γ.mol := funext (BAGraph.shadow_mol Γ)
  unfold LGraph.nM BAGraph.nM
  rw [h]

/-- Two vertices are in one molecule of the shadow iff one is in the molecule of the other. -/
theorem BAGraph.shadow_molOf_eq_iff (Γ : BAGraph E I) (u v : E ⊕ I) :
    Γ.shadow.molOf u = Γ.shadow.molOf v ↔ v ∈ Γ.mol u := by
  rw [Γ.shadow.molOf_eq_iff, BAGraph.shadow_mol]

/-- The shadow has the same dotted edges: no `=`-dotted edge if `Γ` is normal. -/
theorem BAGraph.shadow_dotted (Γ : BAGraph E I) : Γ.shadow.dotted = Γ.dotted := rfl

/-- The auxiliary graph has a non-negative value for non-negative edge variables. -/
theorem BAGraph.auxVal_nonneg {κ : Type} [Fintype κ] (Γ : BAGraph E I) (ξ : κ → κ → ℝ)
    (hξ : ∀ u v, 0 ≤ ξ u v) (be : E → κ) : 0 ≤ Γ.auxVal ξ be :=
  Γ.shadow.auxVal_nonneg ξ hξ be

/-- If distinct external vertices lie in distinct molecules of `Γ`, they lie in distinct molecules of the shadow. -/
theorem BAGraph.shadow_ext (Γ : BAGraph E I)
    (hext : ∀ a b : E, Γ.mol (Sum.inl a) = Γ.mol (Sum.inl b) → a = b) :
    ∀ a b : E, Γ.shadow.molOf (Sum.inl a) = Γ.shadow.molOf (Sum.inl b) → a = b := by
  intro a b h
  rw [BAGraph.shadow_molOf_eq_iff] at h
  refine hext a b ?_
  rw [BAGraph.mem_mol_iff] at h
  ext w
  rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
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
  constructor
  · intro hx; exact (hsymm h).trans hx
  · intro hx; exact h.trans hx

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

/-- A dotted edge of a graph without `=`-dotted edges is a `Ψ`-dotted or an `M`-dotted edge: `atomAdj` of the ends. -/
private theorem BAAtom_atomAdj_cases (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) {u v : E ⊕ I}
    (h : Γ.atomAdj u v = true) :
    (∃ e ∈ Γ.mdot, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) ∨
      ∃ e ∈ Γ.psi, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u) := by
  unfold BAGraph.atomAdj at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hd⟩ := h
    have := hD e he
    simp [this] at hd
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hd⟩ := h
    exact Or.inr ⟨e, he, of_decide_eq_true hd⟩
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hd⟩ := h
    exact Or.inl ⟨e, he, of_decide_eq_true hd⟩

/-- **`scaleatom`, second half** (`B:317-318`): atom-mates are within `|E ⊕ I| r` in block distance when every `M`- and
`Ψ`-dotted edge is within `r` (no `=`-dotted edge: the part (ii) of `BAGraph.Normal`). -/
theorem baAtom_dist (Γ : BAGraph E I) (ℓ : E ⊕ I → Idx d L W) (r : ℝ) (hr : 0 ≤ r)
    (hD : ∀ e ∈ Γ.dotted, e.eq = false)
    (hm : ∀ e ∈ Γ.mdot, (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ) ≤ r)
    (hp : ∀ e ∈ Γ.psi, (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ) ≤ r)
    (u v : E ⊕ I) (hv : v ∈ Γ.atom u) :
    (lwBdist d L W (ℓ u) (ℓ v) : ℝ) ≤ (Fintype.card (E ⊕ I) : ℝ) * r := by
  have hstep : ∀ b c : E ⊕ I, Γ.atomAdj b c = true → (lwBdist d L W (ℓ b) (ℓ c) : ℝ) ≤ r := by
    intro b c hbc
    rcases BAAtom_atomAdj_cases Γ hD hbc with ⟨e, he, h1 | h1⟩ | ⟨e, he, h1 | h1⟩
    · rw [← h1.1, ← h1.2]; exact hm e he
    · rw [← h1.1, ← h1.2, lwBdist_comm]; exact hm e he
    · rw [← h1.1, ← h1.2]; exact hp e he
    · rw [← h1.1, ← h1.2, lwBdist_comm]; exact hp e he
  have key : ∀ n : ℕ, ∀ w ∈ (Γ.atomStep)^[n] {u}, (lwBdist d L W (ℓ u) (ℓ w) : ℝ) ≤ (n : ℝ) * r := by
    intro n
    induction n with
    | zero =>
      intro w hw
      simp only [Function.iterate_zero, id, Finset.mem_singleton] at hw
      subst hw
      simp [auxGraph_bdist_self]
    | succ n ih =>
      intro w hw
      rw [Function.iterate_succ_apply'] at hw
      simp only [BAGraph.atomStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rcases hw with hw | ⟨v', hv', hadj⟩
      · refine (ih w hw).trans ?_
        push_cast
        nlinarith
      · have h1 := ih v' hv'
        have h2 := hstep v' w hadj
        have h3 : (lwBdist d L W (ℓ u) (ℓ w) : ℝ) ≤ lwBdist d L W (ℓ u) (ℓ v') + lwBdist d L W (ℓ v') (ℓ w) := by
          exact_mod_cast auxGraph_bdist_triangle (ℓ u) (ℓ v') (ℓ w)
        push_cast
        nlinarith
  exact key _ v hv

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

/-- **`Gyiyjatom2`** (`B:432`), deterministic: the decay of `S`, `S⁺` gives the indicator of `d_B ≤ r` plus the tail. -/
theorem baAtom_wedge (K : Matrix (Idx d L W) (Idx d L W) ℂ) (C c r : ℝ) (hc : 0 ≤ c)
    (hK : ∀ x y, ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) (x y : Idx d L W) :
    ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * ((if (lwBdist d L W x y : ℝ) ≤ r then 1 else 0) + Real.exp (-(c * r))) := by
  have h0 := hK x y
  have he := Real.exp_pos (-(c * (lwBdist d L W x y : ℝ)))
  have ha : 0 ≤ C * ((W : ℝ) ^ d)⁻¹ :=
    (mul_nonneg_iff_of_pos_right he).1 ((norm_nonneg _).trans h0)
  by_cases hd : (lwBdist d L W x y : ℝ) ≤ r
  · simp only [hd, ↓reduceIte]
    have h1 : Real.exp (-(c * (lwBdist d L W x y : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have : 0 ≤ c * (lwBdist d L W x y : ℝ) := by positivity
      linarith
    have h2 := Real.exp_pos (-(c * r))
    calc ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := h0
      _ ≤ C * ((W : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 ha
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) ha
  · simp only [hd, ↓reduceIte]
    have h1 : Real.exp (-(c * (lwBdist d L W x y : ℝ))) ≤ Real.exp (-(c * r)) := by
      apply Real.exp_le_exp.2
      nlinarith [not_le.1 hd]
    calc ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := h0
      _ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * r)) := mul_le_mul_of_nonneg_left h1 ha
      _ = _ := by ring

end Atoms

end RBM.Graph

end
