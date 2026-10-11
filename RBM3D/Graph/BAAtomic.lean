/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAVocab
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LocalRegular6a

/-!
# BA-L R0: the atomic image of a block Anderson graph (T2417)

Under the strategy S' (T2395 design, supervisor `2026-10-11-0951` L4-C2) every BA step is
compared with a band `LocStep` on the atomic image of the BA graph
(`paper/tex/B_graphical_lemmas.tex:308-313`, cited `B:line`).  This file defines the atom-level
vocabulary (`BAGraph.sameAtom` ... `BAGraph.LocStd`, the statements of the probe
`t/T2395:RBM3D/Probe/T2395Pins.lean:27-63`) and **one** image map `BAGraph.img` (the order of the
probe `t/T2397:RBM3D/Probe/T2397Pins.lean:29-48`: `promoteC` recolours the edges first, then the
merged `LGraph.mergeP` merges the atoms), and proves the pins both designs wrote against it:
`BAimg` (T2395:230), the map properties `BAImgNormal` (m0), `BAImgCounters` (m1), `BAImgMol` (m2)
(T2397:108-118) and, in `BAAtomic2.lean`, `BAPathLift` (T2397:355).

Proved here: `BAGraph.img95_equiv_gen`, `BAGraph.img95_equiv`: the construction of
T2395:222-227 (merge first, then rebuild the solid edges) gives the same packed graph up to a
relabelling of the vertices (for a normal graph; for every graph up to the circles of the solid
edges).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Graph

/-! ## 1. The atom-level vocabulary (T2395 probe 27-41, 56-66; statements copied verbatim) -/

section Vocab

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `u`, `v` lie in one atom. -/
def BAGraph.sameAtom (Γ : BAGraph E I) (u v : E ⊕ I) : Bool := decide (v ∈ Γ.atom u)
/-- the atom of `v` has no external vertex. -/
def BAGraph.intAtom (Γ : BAGraph E I) (v : E ⊕ I) : Bool := decide (∀ w ∈ Γ.atom v, w.isRight = true)
/-- atom-level loops: solid edges (self-loops included) with both ends in one atom (`B:312` read as: they stay, T2395 D§1). -/
def BAGraph.nLoops (Γ : BAGraph E I) : ℕ := Γ.solid.countP fun e => Γ.sameAtom e.src e.dst
/-- the number of atoms with an external vertex. -/
def BAGraph.nExt (Γ : BAGraph E I) : ℕ := ((Finset.univ.filter fun v : E ⊕ I => v.isLeft = true).image Γ.atom).card
/-- `lvl1Share` (`LWLvl1.lean:80`) on atoms: the common internal ends of two edges that are not atom-level loops. -/
def BAGraph.nShare (Γ : BAGraph E I) (e e' : SEdge (E ⊕ I)) : ℕ :=
  if Γ.sameAtom e.src e.dst = true ∨ Γ.sameAtom e'.src e'.dst = true then 0 else
    ([e.src, e.dst].map fun u => ([e'.src, e'.dst].filter fun w => Γ.sameAtom u w = true ∧ Γ.intAtom u = true).length).sum
def BAGraph.pairsAux (Γ : BAGraph E I) : List (SEdge (E ⊕ I)) → ℕ
  | [] => 0
  | e :: es => Γ.pairsAux es + (es.map (Γ.nShare e)).sum
def BAGraph.nPairs (Γ : BAGraph E I) : ℕ := Γ.pairsAux Γ.solid
/-- the non-loop solid edges at the atom of `v` and the charge of the atom (`LWLvl1.lean:1529-1546` on atoms). -/
def BAGraph.atEdges (Γ : BAGraph E I) (v : E ⊕ I) : List (SEdge (E ⊕ I)) :=
  Γ.solid.filter fun e => Γ.sameAtom v e.src != Γ.sameAtom v e.dst
def BAGraph.atCharge (Γ : BAGraph E I) (v : E ⊕ I) : ℤ :=
  ((Γ.atEdges v).map fun e => if Γ.sameAtom v e.src = true then (if e.σ then -1 else 1) else (if e.σ then 1 else -1)).sum
/-- **locally standard at the atom level** (`deflvl1`, `7_8:367-386`, on the atomic image): normal, no solid edge inside an atom, every
internal atom has no edge or two edges of opposite colours and charge `0`. -/
def BAGraph.LocStd (Γ : BAGraph E I) : Prop :=
  Γ.Normal ∧ (∀ e ∈ Γ.solid, Γ.sameAtom e.src e.dst = false) ∧ ∀ i : I, Γ.intAtom (Sum.inr i) = true →
    Γ.atEdges (Sum.inr i) = [] ∨ (((Γ.atEdges (Sum.inr i)).map SEdge.σ = [true, false] ∨
      (Γ.atEdges (Sum.inr i)).map SEdge.σ = [false, true]) ∧ Γ.atCharge (Sum.inr i) = 0)

instance (Γ : BAGraph E I) : Decidable Γ.Normal := by
  unfold BAGraph.Normal; infer_instance
instance (Γ : BAGraph E I) : Decidable Γ.LocStd := by
  unfold BAGraph.LocStd; infer_instance

/-- a graph is a packed graph (no merging) -/
def baPG (Γ : BAGraph E I) : BAPGraph E :=
  ⟨E, I, id, Function.surjective_id, Γ⟩

end Vocab

/-! ## 2. The atoms as a setoid, `promoteC`, the one image map -/

section Image

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The atoms of a BA graph (`def_atom`, `B:302-304`) as a setoid on its vertices (T2397 probe 29). -/
def atomSetoid (Γ : BAGraph E I) : Setoid (E ⊕ I) := Setoid.ker Γ.atom
open Classical in
/-- **The atomic image of a BA graph as a graph of the band** (`B:308-313`, with two deliberate differences, paper-delta `T2397a`): the `=`-, `Ψ`- and `M`-dotted edges are promoted to `=`-dotted edges (so that `LGraph.merge` merges the atoms); a solid edge inside an atom is kept as a circled loop (the paper discards it, `ord` counts it: `B:353`); a solid edge between two atoms loses its circle (the band's `CircIffLoop`) and gets the `×`-dotted edge; the `×`-dotted edges of the BA graph are dropped. (T2397 probe 31-39.) -/
def promoteC (Γ : BAGraph E I) : LGraph E I where
  solid := Γ.solid.map fun e => { e with circ := e.circ && decide (atomSetoid Γ e.src e.dst) }
  waved := Γ.waved
  dotted := (Γ.dotted.filter fun d => d.eq) ++ Γ.psi.map (fun e => ⟨true, e.x, e.y⟩) ++ Γ.mdot.map (fun e => ⟨true, e.x, e.y⟩) ++
    (Γ.solid.filter fun e => !decide (atomSetoid Γ e.src e.dst)).map (fun e => ⟨false, e.src, e.dst⟩)
  coeff := Γ.coeff

/-- **The one image map** (L4-C2): the atomic image of a BA graph, as a packed graph of the band over the external vertices `E` of `Γ`:
`promoteC` first, then the merged `LGraph.mergeP` (T2397's order; `BAGraph.img95` is the construction of T2395, proved equivalent). -/
def BAGraph.img (Γ : BAGraph E I) : PGraph E := (promoteC Γ).mergeP

/-- The atomic image of a packed BA graph (T2395 probe 228; T2397 probe 46 for `E = Fin 2`): `lvl1Comp` of the image of the graph. -/
def BAPGraph.img {E : Type} (P : BAPGraph E) : PGraph E := PGraph.lvl1Comp P.g.img P.ext P.ext_surj

end Image

/-! ## 3. The classes of `promoteC`: one class is one atom -/

section Key

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAAtomic_atomAdj_comm (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.atomAdj u v = Γ.atomAdj v u := by
  simp only [BAGraph.atomAdj, or_comm]

private theorem BAAtomic_rtg_symm (Γ : BAGraph E I) {v w : E ⊕ I}
    (h : Relation.ReflTransGen (fun a b => Γ.atomAdj a b = true) v w) :
    Relation.ReflTransGen (fun a b => Γ.atomAdj a b = true) w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (by rw [BAAtomic_atomAdj_comm]; exact hbc) ih

/-- Two vertices are equivalent for `atomSetoid` iff the second lies in the atom of the first. -/
theorem atomSetoid_iff (Γ : BAGraph E I) (u v : E ⊕ I) : atomSetoid Γ u v ↔ v ∈ Γ.atom u := by
  rw [atomSetoid, Setoid.ker_def]
  constructor
  · intro h
    rw [h]
    exact (Γ.mem_atom_iff v v).2 Relation.ReflTransGen.refl
  · intro h
    ext x
    rw [Γ.mem_atom_iff, Γ.mem_atom_iff]
    rw [Γ.mem_atom_iff] at h
    constructor
    · intro hx; exact (BAAtomic_rtg_symm Γ h).trans hx
    · intro hx; exact h.trans hx

theorem BAGraph.sameAtom_iff (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.sameAtom u v = true ↔ v ∈ Γ.atom u := by
  simp [BAGraph.sameAtom]

theorem BAGraph.sameAtom_comm (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.sameAtom u v = Γ.sameAtom v u := by
  rw [Bool.eq_iff_iff, Γ.sameAtom_iff, Γ.sameAtom_iff, ← atomSetoid_iff, ← atomSetoid_iff]
  exact ⟨fun h => (atomSetoid Γ).symm h, fun h => (atomSetoid Γ).symm h⟩

theorem BAGraph.sameAtom_iff_atom_eq (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.sameAtom u v = true ↔ Γ.atom u = Γ.atom v := by
  rw [Γ.sameAtom_iff, ← atomSetoid_iff, atomSetoid, Setoid.ker_def]

theorem BAGraph.intAtom_iff (Γ : BAGraph E I) (v : E ⊕ I) : Γ.intAtom v = true ↔ ∀ w ∈ Γ.atom v, w.isRight = true := by
  simp [BAGraph.intAtom]

/-- The equivalence relation of `promoteC` is the atom adjacency. -/
theorem promoteC_eqRel_iff (Γ : BAGraph E I) (u v : E ⊕ I) : (promoteC Γ).EqRel u v ↔ Γ.atomAdj u v = true := by
  classical
  unfold LGraph.EqRel
  simp only [promoteC, BAGraph.atomAdj, List.mem_append, List.mem_filter, List.mem_map, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨e, (((⟨he, h1⟩ | ⟨e', he', rfl⟩) | ⟨e', he', rfl⟩) | ⟨e', ⟨he', _⟩, rfl⟩), h2, h3⟩
    · exact Or.inl (Or.inl ⟨e, he, h1, h3⟩)
    · exact Or.inl (Or.inr ⟨e', he', h3⟩)
    · exact Or.inr ⟨e', he', h3⟩
    · exact absurd h2 (by simp)
  · rintro ((⟨e, he, h1, h3⟩ | ⟨e', he', h3⟩) | ⟨e', he', h3⟩)
    · exact ⟨e, Or.inl (Or.inl (Or.inl ⟨he, h1⟩)), h1, h3⟩
    · exact ⟨_, Or.inl (Or.inl (Or.inr ⟨e', he', rfl⟩)), rfl, h3⟩
    · exact ⟨_, Or.inl (Or.inr ⟨e', he', rfl⟩), rfl, h3⟩

/-- **The key fact**: two vertices lie in the same class of `promoteC Γ` iff they lie in the same atom of `Γ`. -/
theorem promoteC_cls_eq_iff (Γ : BAGraph E I) (u v : E ⊕ I) : (promoteC Γ).cls u = (promoteC Γ).cls v ↔ v ∈ Γ.atom u := by
  rw [Quotient.eq (r := (promoteC Γ).eqSetoid), Γ.mem_atom_iff]
  change Relation.EqvGen _ u v ↔ _
  constructor
  · intro h
    induction h with
    | rel a b hab => exact Relation.ReflTransGen.single ((promoteC_eqRel_iff Γ a b).1 hab)
    | refl => exact Relation.ReflTransGen.refl
    | symm a b _ ih => exact BAAtomic_rtg_symm Γ ih
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl _
    | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ ((promoteC_eqRel_iff Γ _ _).2 hbc))

theorem BAAtomic_vmapC_injective (Γ : LGraph E I) : Function.Injective Γ.vmapC := by
  intro q q' h
  unfold LGraph.vmapC at h
  by_cases hq : Γ.IsExtCls q <;> by_cases hq' : Γ.IsExtCls q' <;> simp [hq, hq'] at h
  · exact h
  · exact h

theorem BAAtomic_vmap_eq_iff (Γ : LGraph E I) (u v : E ⊕ I) : Γ.vmap u = Γ.vmap v ↔ Γ.cls u = Γ.cls v :=
  ⟨fun h => BAAtomic_vmapC_injective Γ h, fun h => congrArg Γ.vmapC h⟩

theorem BAAtomic_vmap_inl (Γ : LGraph E I) (a : E) : Γ.vmap (Sum.inl a) = Sum.inl (Γ.extMap a) := by
  have h : Γ.IsExtCls (Γ.cls (Sum.inl a)) := ⟨a, rfl⟩
  simp [LGraph.vmap, LGraph.vmapC, LGraph.extMap, h]

theorem BAAtomic_vmap_surjective (Γ : LGraph E I) : Function.Surjective Γ.vmap := by
  rintro (⟨q, hq⟩ | ⟨q, hq⟩)
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [LGraph.vmap, LGraph.vmapC, hq]⟩
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [LGraph.vmap, LGraph.vmapC, hq]⟩

theorem BAAtomic_vmap_isRight_iff (Γ : LGraph E I) (v : E ⊕ I) :
    (Γ.vmap v).isRight = true ↔ ¬ Γ.IsExtCls (Γ.cls v) := by
  unfold LGraph.vmap LGraph.vmapC
  by_cases h : Γ.IsExtCls (Γ.cls v) <;> simp [h]

/-- Every internal class has an internal vertex. -/
theorem BAAtomic_exists_inr (Γ : LGraph E I) (q : Γ.IntCls) : ∃ b : I, Γ.cls (Sum.inr b) = q.1 := by
  obtain ⟨v, hv⟩ := Quotient.exists_rep q.1
  rcases v with a | b
  · exact absurd ⟨a, hv⟩ q.2
  · exact ⟨b, hv⟩

/-- **`vmap` identifies exactly the vertices of one atom.** -/
theorem promoteC_vmap_eq_iff (Γ : BAGraph E I) (u v : E ⊕ I) : (promoteC Γ).vmap u = (promoteC Γ).vmap v ↔ v ∈ Γ.atom u := by
  rw [BAAtomic_vmap_eq_iff, promoteC_cls_eq_iff]

theorem promoteC_vmap_eq_iff' (Γ : BAGraph E I) (u v : E ⊕ I) :
    (promoteC Γ).vmap u = (promoteC Γ).vmap v ↔ Γ.sameAtom u v = true := by
  rw [promoteC_vmap_eq_iff, Γ.sameAtom_iff]

/-- An atom has no external vertex iff its image vertex is internal. -/
theorem promoteC_vmap_isRight_iff (Γ : BAGraph E I) (v : E ⊕ I) :
    ((promoteC Γ).vmap v).isRight = true ↔ Γ.intAtom v = true := by
  rw [BAAtomic_vmap_isRight_iff, Γ.intAtom_iff]
  constructor
  · intro h w hw
    rcases w with a | b
    · exact absurd ⟨a, (promoteC_cls_eq_iff Γ v (Sum.inl a)).2 hw |>.symm⟩ h
    · rfl
  · intro h ⟨a, ha⟩
    have := h (Sum.inl a) ((promoteC_cls_eq_iff Γ v (Sum.inl a)).1 ha.symm)
    simp at this

end Key

/-! ## 4. The image explicitly, (m0) -/

section ImgDesc

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem BAGraph.img_g (Γ : BAGraph E I) : Γ.img.g = (promoteC Γ).merge := rfl

theorem BAGraph.img_ext (Γ : BAGraph E I) : Γ.img.ext = (promoteC Γ).extMap := rfl

private theorem BAAtomic_decide_atomSetoid (Γ : BAGraph E I) (u v : E ⊕ I) :
    @decide (atomSetoid Γ u v) (Classical.propDecidable _) = Γ.sameAtom u v := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Γ.sameAtom_iff, atomSetoid_iff]

theorem promoteC_solid (Γ : BAGraph E I) :
    (promoteC Γ).solid = Γ.solid.map fun e => ⟨e.σ, e.circ && Γ.sameAtom e.src e.dst, e.src, e.dst⟩ := by
  unfold promoteC
  simp only [BAAtomic_decide_atomSetoid]

/-- The solid edges of the image: those of `Γ`, relabelled; an edge keeps its circle iff its ends lie in one atom. -/
theorem BAGraph.img_solid (Γ : BAGraph E I) :
    Γ.img.g.solid = Γ.solid.map fun e =>
      ⟨e.σ, e.circ && Γ.sameAtom e.src e.dst, (promoteC Γ).vmap e.src, (promoteC Γ).vmap e.dst⟩ := by
  change (promoteC Γ).solid.map (SEdge.map (promoteC Γ).vmap) = _
  rw [promoteC_solid, List.map_map]
  rfl

/-- The waved edges of the image: those of `Γ`, relabelled. -/
theorem BAGraph.img_waved (Γ : BAGraph E I) : Γ.img.g.waved = Γ.waved.map (WEdge.map (promoteC Γ).vmap) := rfl

theorem BAGraph.img_coeff (Γ : BAGraph E I) : Γ.img.g.coeff = Γ.coeff := rfl

/-- The `×`-dotted edges of the image: one for every solid edge of `Γ` between two atoms; there is no `=`-dotted edge. -/
theorem BAGraph.img_dotted (Γ : BAGraph E I) :
    Γ.img.g.dotted = (Γ.solid.filter fun e => !Γ.sameAtom e.src e.dst).map fun e =>
      ⟨false, (promoteC Γ).vmap e.src, (promoteC Γ).vmap e.dst⟩ := by
  change ((promoteC Γ).dotted.filter fun e => !e.eq).map (DEdge.map (promoteC Γ).vmap) = _
  have h : (promoteC Γ).dotted.filter (fun e => !e.eq) =
      (Γ.solid.filter fun e => !Γ.sameAtom e.src e.dst).map fun e => (⟨false, e.src, e.dst⟩ : DEdge (E ⊕ I)) := by
    unfold promoteC
    simp only [BAAtomic_decide_atomSetoid, List.filter_append, List.filter_map]
    simp [List.filter_filter, Function.comp_def]
  rw [h, List.map_map]
  rfl

theorem BAGraph.img_dotted_eq (Γ : BAGraph E I) : ∀ e ∈ Γ.img.g.dotted, e.eq = false := by
  intro e he
  rw [BAGraph.img_dotted] at he
  obtain ⟨e0, _, rfl⟩ := List.mem_map.1 he
  rfl

/-- The circle of an edge of the image is the circle of the edge of `Γ` if the ends lie in one atom. -/
private theorem BAAtomic_img_loop_iff (Γ : BAGraph E I) {e : SEdge (E ⊕ I)} :
    (promoteC Γ).vmap e.src = (promoteC Γ).vmap e.dst ↔ Γ.sameAtom e.src e.dst = true :=
  promoteC_vmap_eq_iff' Γ _ _

/-- **(m0), the graph form**: the atomic image of a BA-normal graph is a normal graph of the band (`LGraph.Normal`: no `=`-dotted edge;
`×`-dotted iff solid between distinct atoms, by `promoteC`; every loop circled) in which a solid edge is circled iff it is a loop
(`CircIffLoop`, `LocalRegular6a.lean:162`). -/
theorem BAGraph.img_normal (Γ : BAGraph E I) (hN : Γ.Normal) : Γ.img.g.Normal ∧ LGraph.CircIffLoop Γ.img.g := by
  have hC : ∀ e ∈ Γ.img.g.solid, (e.src = e.dst ↔ e.circ = true) := by
    intro e he
    rw [BAGraph.img_solid] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    have h1 := hN.2 e0 he0
    simp only [h1, Bool.true_and]
    exact BAAtomic_img_loop_iff Γ
  refine ⟨⟨Γ.img_dotted_eq, ?_, fun e he h => ((hC e he).1 h)⟩, hC⟩
  intro u v huv
  unfold LGraph.XBetween LGraph.SBetween
  rw [BAGraph.img_dotted, BAGraph.img_solid]
  constructor
  · rintro ⟨e, he, _, h⟩
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    obtain ⟨he0, hs⟩ := List.mem_filter.1 he0
    refine ⟨_, List.mem_map.2 ⟨e0, he0, rfl⟩, ?_, h⟩
    intro hh
    have := (BAAtomic_img_loop_iff Γ).1 hh
    simp [this] at hs
  · rintro ⟨e, he, hne, h⟩
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    refine ⟨_, List.mem_map.2 ⟨e0, List.mem_filter.2 ⟨he0, ?_⟩, rfl⟩, rfl, h⟩
    rw [Bool.not_eq_true']
    by_contra hh
    exact hne ((BAAtomic_img_loop_iff Γ).2 (by simpa using hh))

/-- **Map property (m0)** (T2397 probe 108): the atomic image of a BA-normal graph is normal and a solid edge is circled iff it is a loop. -/
def BAImgNormal : Prop :=
  ∀ P : BAPGraph (Fin 2), P.g.Normal → (BAPGraph.img P).g.Normal ∧ LGraph.CircIffLoop (BAPGraph.img P).g

theorem baImgNormal : BAImgNormal := fun P hN => P.g.img_normal hN

end ImgDesc

/-! ## 5. (m2): the molecules of the image are the molecules of the BA graph -/

section Mol

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem BAAtomic_ladj_comm {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (Γ : LGraph E' I') (u v : E' ⊕ I') : Γ.adj u v = Γ.adj v u := by
  simp only [LGraph.adj, or_comm]

theorem BAAtomic_merge_adj_iff (Γ : BAGraph E I) (a b : (promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls) :
    (promoteC Γ).merge.adj a b = true ↔ ∃ e0 ∈ Γ.waved,
      (((promoteC Γ).vmap e0.x = a ∧ (promoteC Γ).vmap e0.y = b) ∨ ((promoteC Γ).vmap e0.x = b ∧ (promoteC Γ).vmap e0.y = a)) := by
  unfold LGraph.adj
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨e, he, h⟩ | ⟨e, he, h1, _⟩)
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact ⟨e0, he0, h⟩
    · exact absurd h1 (by simp [Γ.img_dotted_eq e he])
  · rintro ⟨e0, he0, h⟩
    exact Or.inl ⟨WEdge.map (promoteC Γ).vmap e0, List.mem_map.2 ⟨e0, he0, rfl⟩, h⟩

private theorem BAAtomic_ba_adj_iff (Γ : BAGraph E I) (a b : E ⊕ I) :
    Γ.adj a b = true ↔ (∃ e0 ∈ Γ.waved, ((e0.x = a ∧ e0.y = b) ∨ (e0.x = b ∧ e0.y = a))) ∨ Γ.atomAdj a b = true := by
  unfold BAGraph.adj LGraph.adj
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((⟨e, he, h⟩ | ⟨e, he, h1, h2⟩) | h)
    · exact Or.inl ⟨e, he, h⟩
    · refine Or.inr ?_
      unfold BAGraph.atomAdj
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl (Or.inl ⟨e, he, h1, h2⟩)
    · exact Or.inr h
  · rintro (⟨e, he, h⟩ | h)
    · exact Or.inl (Or.inl ⟨e, he, h⟩)
    · exact Or.inr h

private theorem BAAtomic_adj_of_atom (Γ : BAGraph E I) {u w : E ⊕ I} (h : w ∈ Γ.atom u) :
    Relation.ReflTransGen (fun a b => Γ.adj a b = true) u w := by
  rw [Γ.mem_atom_iff] at h
  refine Relation.ReflTransGen.mono ?_ u w h
  intro a b hab
  exact (BAAtomic_ba_adj_iff Γ a b).2 (Or.inr hab)

/-- **The molecules of the image are those of the BA graph** (the graph form of (m2)). -/
theorem BAGraph.img_molOf_eq_iff (Γ : BAGraph E I) (u v : E ⊕ I) :
    (promoteC Γ).merge.molOf ((promoteC Γ).vmap u) = (promoteC Γ).merge.molOf ((promoteC Γ).vmap v) ↔ v ∈ Γ.mol u := by
  rw [LGraph.molOf_eq_iff, LGraph.mem_mol_iff, Γ.mem_mol_iff, SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    have key : ∀ b, Relation.ReflTransGen (promoteC Γ).merge.molGraph.Adj ((promoteC Γ).vmap u) b →
        ∃ w, (promoteC Γ).vmap w = b ∧ Relation.ReflTransGen (fun a b => Γ.adj a b = true) u w := by
      intro b hb
      induction hb with
      | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
      | @tail b' c _ hbc ih =>
        obtain ⟨w, hw, huw⟩ := ih
        have hadj : (promoteC Γ).merge.adj b' c = true := by
          rcases ((SimpleGraph.fromRel_adj _ b' c).1 hbc).2 with h | h
          · exact h
          · rw [BAAtomic_ladj_comm]; exact h
        obtain ⟨e0, he0, h0 | h0⟩ := (BAAtomic_merge_adj_iff Γ b' c).1 hadj
        · refine ⟨e0.y, h0.2, huw.trans ((BAAtomic_adj_of_atom Γ ((promoteC_vmap_eq_iff Γ w e0.x).1 (hw.trans h0.1.symm))).trans
            (Relation.ReflTransGen.single ((BAAtomic_ba_adj_iff Γ _ _).2 (Or.inl ⟨e0, he0, Or.inl ⟨rfl, rfl⟩⟩))))⟩
        · refine ⟨e0.x, h0.1, huw.trans ((BAAtomic_adj_of_atom Γ ((promoteC_vmap_eq_iff Γ w e0.y).1 (hw.trans h0.2.symm))).trans
            (Relation.ReflTransGen.single ((BAAtomic_ba_adj_iff Γ _ _).2 (Or.inl ⟨e0, he0, Or.inr ⟨rfl, rfl⟩⟩))))⟩
    obtain ⟨w, hw, huw⟩ := key _ h
    exact huw.trans (BAAtomic_adj_of_atom Γ ((promoteC_vmap_eq_iff Γ w v).1 hw))
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      rcases (BAAtomic_ba_adj_iff Γ b c).1 hbc with ⟨e0, he0, h0⟩ | hat
      · by_cases hbc' : (promoteC Γ).vmap b = (promoteC Γ).vmap c
        · rw [← hbc']; exact ih
        · refine ih.tail ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hbc', Or.inl ?_⟩)
          refine (BAAtomic_merge_adj_iff Γ _ _).2 ⟨e0, he0, ?_⟩
          rcases h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
          · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
      · have : (promoteC Γ).vmap b = (promoteC Γ).vmap c :=
          (promoteC_vmap_eq_iff Γ b c).2 ((Γ.mem_atom_iff b c).2 (Relation.ReflTransGen.single hat))
        rw [← this]; exact ih

/-- **Map property (m2)** (T2397 probe 118): the molecules of the image are the molecules of the BA graph (`def_poly`, `B:299`;
`BAGraph.mol`, `BAVocab.lean:125`). -/
def BAImgMol : Prop :=
  ∀ (Q : BAPGraph (Fin 2)) (u v : Q.E' ⊕ Q.I'),
    (promoteC Q.g).merge.molOf ((promoteC Q.g).vmap u) = (promoteC Q.g).merge.molOf ((promoteC Q.g).vmap v) ↔ v ∈ Q.g.mol u

theorem baImgMol : BAImgMol := fun Q u v => Q.g.img_molOf_eq_iff u v

end Mol

/-! ## 6. (m1): the counters, and the number of external atoms -/

section Counters

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Counting classes: if `f u` is the class of `u` and `φ` separates the classes, the classes of a set are counted by `φ`. -/
private theorem BAAtomic_card_image_class {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β]
    (f : α → Finset α) (φ : α → β) (h : ∀ u v, v ∈ f u ↔ φ u = φ v) (S : Finset α) :
    (S.image f).card = (S.image φ).card := by
  classical
  have hf : f = fun u => Finset.univ.filter (fun v => φ u = φ v) := by
    funext u; ext v; simp [h]
  have himg : S.image f = (S.image φ).image (fun b => Finset.univ.filter (fun v => b = φ v)) := by
    rw [Finset.image_image, hf]; rfl
  rw [himg]
  apply Finset.card_image_of_injOn
  intro b hb b' hb' hbb
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hb
  obtain ⟨v', _, rfl⟩ := Finset.mem_image.1 hb'
  have hv : v ∈ Finset.univ.filter (fun x => φ v = φ x) := by simp
  simp only at hbb
  rw [hbb] at hv
  exact (Finset.mem_filter.1 hv).2.symm

theorem BAGraph.card_intCls (Γ : BAGraph E I) : Fintype.card (promoteC Γ).IntCls = Γ.nA := by
  classical
  unfold BAGraph.nA
  rw [BAAtomic_card_image_class Γ.atom (promoteC Γ).cls (fun u v => (promoteC_cls_eq_iff Γ u v).symm)]
  have himg : (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.atom v, w.isRight = true)).image (promoteC Γ).cls =
      Finset.univ.filter (fun q : (promoteC Γ).Cls => ¬ (promoteC Γ).IsExtCls q) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩ ⟨a, ha⟩
      have := hv (Sum.inl a) ((promoteC_cls_eq_iff Γ v (Sum.inl a)).1 ha.symm)
      simp at this
    · intro hq
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      refine ⟨v, fun w hw => ?_, rfl⟩
      rcases w with a | b
      · exact absurd ⟨a, ((promoteC_cls_eq_iff Γ v (Sum.inl a)).2 hw).symm⟩ hq
      · rfl
  rw [himg]
  exact Fintype.card_of_subtype _ (by simp)

/-- The classes with an external vertex are counted by the atoms with an external vertex. -/
theorem BAGraph.card_extCls (Γ : BAGraph E I) : Fintype.card (promoteC Γ).ExtCls = Γ.nExt := by
  classical
  unfold BAGraph.nExt
  rw [BAAtomic_card_image_class Γ.atom (promoteC Γ).cls (fun u v => (promoteC_cls_eq_iff Γ u v).symm)]
  have himg : (Finset.univ.filter (fun v : E ⊕ I => v.isLeft = true)).image (promoteC Γ).cls =
      Finset.univ.filter (fun q : (promoteC Γ).Cls => (promoteC Γ).IsExtCls q) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases v with a | b
      · exact ⟨a, rfl⟩
      · simp at hv
    · rintro ⟨a, rfl⟩
      exact ⟨Sum.inl a, rfl, rfl⟩
  rw [himg]
  exact Fintype.card_of_subtype _ (by simp)

/-- A vertex has an all-internal molecule iff its image has one. -/
private theorem BAAtomic_mol_int_iff (Γ : BAGraph E I) (v : E ⊕ I) :
    (∀ w ∈ Γ.mol v, w.isRight = true) ↔ ∀ w' ∈ (promoteC Γ).merge.mol ((promoteC Γ).vmap v), w'.isRight = true := by
  constructor
  · intro h w' hw'
    obtain ⟨w, rfl⟩ := BAAtomic_vmap_surjective (promoteC Γ) w'
    have hm : w ∈ Γ.mol v := (Γ.img_molOf_eq_iff v w).1 ((LGraph.molOf_eq_iff _ _ _).2 hw')
    rw [promoteC_vmap_isRight_iff, BAGraph.intAtom_iff]
    intro x hx
    apply h
    rw [BAGraph.mem_mol_iff] at hm ⊢
    exact hm.trans ((Γ.mem_mol_iff w x).1 (Γ.atom_subset_mol w hx))
  · intro h w hw
    rcases w with a | b
    · exfalso
      have := h _ ((LGraph.molOf_eq_iff _ _ _).1 ((Γ.img_molOf_eq_iff v (Sum.inl a)).2 hw))
      rw [BAAtomic_vmap_inl] at this
      simp at this
    · rfl

theorem BAGraph.nM_merge (Γ : BAGraph E I) : (promoteC Γ).merge.nM = Γ.nM := by
  classical
  unfold LGraph.nM BAGraph.nM
  rw [BAAtomic_card_image_class (promoteC Γ).merge.mol (fun v' => (promoteC Γ).merge.molOf v')
      (fun u v => (LGraph.molOf_eq_iff _ u v).symm),
    BAAtomic_card_image_class Γ.mol (fun v => (promoteC Γ).merge.molOf ((promoteC Γ).vmap v))
      (fun u v => (Γ.img_molOf_eq_iff u v).symm)]
  congr 1
  ext c
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v', hv', rfl⟩
    obtain ⟨v, rfl⟩ := BAAtomic_vmap_surjective (promoteC Γ) v'
    exact ⟨v, (BAAtomic_mol_int_iff Γ v).2 hv', rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨(promoteC Γ).vmap v, (BAAtomic_mol_int_iff Γ v).1 hv, rfl⟩

/-- **Map property (m1), the graph form**: the counters of the image are the BA counters (`n_V ↔ n_A`). -/
theorem BAGraph.img_counters (Γ : BAGraph E I) : Γ.img.g.counters = Γ.counters := by
  change (promoteC Γ).merge.counters = Γ.counters
  unfold LGraph.counters BAGraph.counters
  congr 1
  · simp [LGraph.nS, BAGraph.nS, LGraph.merge, promoteC]
  · simp [LGraph.nW, BAGraph.nW, LGraph.merge, promoteC]
  · exact Γ.card_intCls
  · exact Γ.nM_merge

/-- **Map property (m1)** (T2397 probe 115): the counters of the image are the BA counters. -/
def BAImgCounters : Prop := ∀ Q : BAPGraph (Fin 2), (BAPGraph.img Q).g.counters = Q.g.counters

theorem baImgCounters : BAImgCounters := fun Q => Q.g.img_counters

end Counters

/-! ## 7. `BAimg`: loops, pairs, external atoms -/

section LoopsPairs

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- An edge of the image: the end vertices are merged, the circle stays iff the ends lie in one atom. -/
private def BAAtomic_fm (Γ : BAGraph E I) (e : SEdge (E ⊕ I)) : SEdge ((promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls) :=
  ⟨e.σ, e.circ && Γ.sameAtom e.src e.dst, (promoteC Γ).vmap e.src, (promoteC Γ).vmap e.dst⟩

private theorem BAAtomic_merge_dotted (Γ : BAGraph E I) : (promoteC Γ).merge.dotted =
    (Γ.solid.filter fun e => !Γ.sameAtom e.src e.dst).map fun e =>
      ⟨false, (promoteC Γ).vmap e.src, (promoteC Γ).vmap e.dst⟩ := Γ.img_dotted

theorem BAAtomic_merge_solid (Γ : BAGraph E I) : (promoteC Γ).merge.solid = Γ.solid.map (BAAtomic_fm Γ) := Γ.img_solid

/-- The atom-level loops of `Γ` are the loops of the image. -/
theorem BAGraph.img_nLoops (Γ : BAGraph E I) : Γ.img.g.lvl1NLoops = Γ.nLoops := by
  change lvl1Loops (promoteC Γ).merge.solid = _
  unfold BAGraph.nLoops lvl1Loops
  rw [BAAtomic_merge_solid, List.countP_map]
  apply List.countP_congr
  intro e _
  exact decide_eq_true_iff.trans (promoteC_vmap_eq_iff' Γ _ _)

private theorem BAAtomic_share_eq (Γ : BAGraph E I) (e e' : SEdge (E ⊕ I)) :
    lvl1Share Sum.isRight (BAAtomic_fm Γ e) (BAAtomic_fm Γ e') = Γ.nShare e e' := by
  unfold lvl1Share BAGraph.nShare
  simp only [BAAtomic_fm, promoteC_vmap_eq_iff', promoteC_vmap_isRight_iff, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.filter_cons, List.filter_nil, decide_eq_true_eq]
  split_ifs <;> simp_all

private theorem BAAtomic_pairs_eq (Γ : BAGraph E I) :
    ∀ es : List (SEdge (E ⊕ I)), lvl1Pairs Sum.isRight (es.map (BAAtomic_fm Γ)) = Γ.pairsAux es
  | [] => rfl
  | e :: es => by
    simp only [List.map_cons, lvl1Pairs, BAGraph.pairsAux, BAAtomic_pairs_eq Γ es, List.map_map, Function.comp_def]
    simp only [BAAtomic_share_eq]

/-- The atom-level pairs of `Γ` are the pairs of the image. -/
theorem BAGraph.img_nPairs (Γ : BAGraph E I) : Γ.img.g.lvl1NPairs = Γ.nPairs := by
  change lvl1Pairs Sum.isRight (promoteC Γ).merge.solid = _
  unfold BAGraph.nPairs
  rw [BAAtomic_merge_solid]
  exact BAAtomic_pairs_eq Γ _

end LoopsPairs

/-! ## 8. `BAimg`: local standardness at the atom level -/

section LocStdImg

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAAtomic_inc_logic {α : Type*} [DecidableEq α] (x s t : α) :
    decide (s ≠ t ∧ (s = x ∨ t = x)) = (decide (x = s) != decide (x = t)) := by
  by_cases h1 : x = s <;> by_cases h2 : x = t
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2]
  · subst h2; simp [h1, Ne.symm h1]
  · simp [h1, h2, Ne.symm h1, Ne.symm h2]

private theorem BAAtomic_sameAtom_decide (Γ : BAGraph E I) (u v : E ⊕ I) :
    Γ.sameAtom u v = decide ((promoteC Γ).vmap u = (promoteC Γ).vmap v) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact (promoteC_vmap_eq_iff' Γ u v).symm

private theorem BAAtomic_incAt (Γ : BAGraph E I) (v : E ⊕ I) (e : SEdge (E ⊕ I)) :
    (BAAtomic_fm Γ e).lvl1IncAt ((promoteC Γ).vmap v) = (Γ.sameAtom v e.src != Γ.sameAtom v e.dst) := by
  rw [BAAtomic_sameAtom_decide, BAAtomic_sameAtom_decide]
  exact BAAtomic_inc_logic ((promoteC Γ).vmap v) _ _

private theorem BAAtomic_solidAt (Γ : BAGraph E I) (v : E ⊕ I) :
    (promoteC Γ).merge.lvl1SolidAt ((promoteC Γ).vmap v) = (Γ.atEdges v).map (BAAtomic_fm Γ) := by
  unfold LGraph.lvl1SolidAt BAGraph.atEdges
  rw [BAAtomic_merge_solid, List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  exact BAAtomic_incAt Γ v e

private theorem BAAtomic_charge (Γ : BAGraph E I) (v : E ⊕ I) :
    (promoteC Γ).merge.lvl1ChargeAt ((promoteC Γ).vmap v) = Γ.atCharge v := by
  unfold LGraph.lvl1ChargeAt BAGraph.atCharge
  rw [BAAtomic_solidAt, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, SEdge.lvl1ChargeAt, BAAtomic_fm]
  refine if_congr ?_ rfl rfl
  exact eq_comm.trans (promoteC_vmap_eq_iff' Γ v e.src)

private theorem BAAtomic_std_iff (Γ : BAGraph E I) (v : E ⊕ I) :
    ((promoteC Γ).merge.StdNeutral ((promoteC Γ).vmap v) ∨ (promoteC Γ).merge.lvl1DegAt ((promoteC Γ).vmap v) = 0) ↔
    (Γ.atEdges v = [] ∨ (((Γ.atEdges v).map SEdge.σ = [true, false] ∨ (Γ.atEdges v).map SEdge.σ = [false, true]) ∧
      Γ.atCharge v = 0)) := by
  unfold LGraph.StdNeutral LGraph.lvl1DegAt
  rw [BAAtomic_solidAt, BAAtomic_charge, List.map_map, List.length_map, List.length_eq_zero_iff, or_comm]
  rfl

private theorem BAAtomic_exists_inr_vmap (Γ : BAGraph E I) (q : (promoteC Γ).IntCls) :
    ∃ b : I, (promoteC Γ).vmap (Sum.inr b) = Sum.inr q := by
  obtain ⟨b, hb⟩ := BAAtomic_exists_inr (promoteC Γ) q
  refine ⟨b, ?_⟩
  unfold LGraph.vmap LGraph.vmapC
  rw [hb]
  simp [q.2]

/-- **`BAimg`, local standardness**: for a normal graph, atom-level local standardness of `Γ` is local standardness of its image. -/
theorem BAGraph.img_locStd_iff (Γ : BAGraph E I) (hN : Γ.Normal) : Γ.LocStd ↔ Γ.img.g.LocStd := by
  unfold BAGraph.LocStd LGraph.LocStd
  constructor
  · rintro ⟨_, hloop, hint⟩
    refine ⟨(Γ.img_normal hN).1, ?_, ?_⟩
    · intro e he
      rw [BAGraph.img_solid] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      intro hh
      have := (promoteC_vmap_eq_iff' Γ e0.src e0.dst).1 hh
      rw [hloop e0 he0] at this
      exact absurd this (by simp)
    · intro i
      obtain ⟨b, hb⟩ := BAAtomic_exists_inr_vmap Γ i
      have hia : Γ.intAtom (Sum.inr b) = true := by
        rw [← promoteC_vmap_isRight_iff, hb]; rfl
      have := (BAAtomic_std_iff Γ (Sum.inr b)).2 (hint b hia)
      rw [hb] at this
      exact this
  · rintro ⟨_, hloop, hint⟩
    refine ⟨hN, ?_, ?_⟩
    · intro e he
      by_contra hh
      have hs : Γ.sameAtom e.src e.dst = true := by simpa using hh
      have hmem : BAAtomic_fm Γ e ∈ Γ.img.g.solid := by
        rw [BAGraph.img_solid]
        exact List.mem_map.2 ⟨e, he, rfl⟩
      exact hloop _ hmem ((promoteC_vmap_eq_iff' Γ e.src e.dst).2 hs)
    · intro i hi
      have hr : ((promoteC Γ).vmap (Sum.inr i)).isRight = true := (promoteC_vmap_isRight_iff Γ _).2 hi
      rcases hv : (promoteC Γ).vmap (Sum.inr i) with a | i'
      · rw [hv] at hr; simp at hr
      · have h2 : (promoteC Γ).merge.StdNeutral ((promoteC Γ).vmap (Sum.inr i)) ∨
            (promoteC Γ).merge.lvl1DegAt ((promoteC Γ).vmap (Sum.inr i)) = 0 := by
          rw [hv]; exact hint i'
        exact (BAAtomic_std_iff Γ (Sum.inr i)).1 h2

end LocStdImg

/-- **`BAimg`** (T2395 probe 230): the image keeps the counters, the atom-level loops and pairs, the number of external atoms; it is normal;
it is locally standard iff `Γ` is. -/
def BAimg : Prop := ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
  Γ.img.g.counters = Γ.counters ∧ Γ.img.g.lvl1NLoops = Γ.nLoops ∧ Γ.img.g.lvl1NPairs = Γ.nPairs ∧ Fintype.card Γ.img.E' = Γ.nExt ∧
    (Γ.Normal → Γ.img.g.Normal) ∧ (Γ.Normal → (Γ.LocStd ↔ Γ.img.g.LocStd))

theorem BAimg_holds : BAimg := fun Γ =>
  ⟨Γ.img_counters, Γ.img_nLoops, Γ.img_nPairs, Γ.card_extCls, fun hN => (Γ.img_normal hN).1, fun hN => Γ.img_locStd_iff hN⟩

theorem BAImgNormal_holds : BAImgNormal := fun P hN => P.g.img_normal hN
theorem BAImgCounters_holds : BAImgCounters := fun Q => Q.g.img_counters
theorem BAImgMol_holds : BAImgMol := fun Q u v => Q.g.img_molOf_eq_iff u v

/-! ## 9. The other construction (T2395 probe 222-227) is the same map -/

section Img95

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `Γ` with the `Ψ`- and `M`-dotted edges promoted to `=`-dotted edges (T2395 probe 223-224). -/
private def BAAtomic_dot95 (Γ : BAGraph E I) : LGraph E I :=
  { Γ.toLGraph with dotted := Γ.dotted ++ (Γ.psi.map (fun e => ⟨true, e.x, e.y⟩) ++ Γ.mdot.map (fun e => ⟨true, e.x, e.y⟩)) }

/-- **The construction of T2395** (probe 222-227): merge the `Ψ`-, `M`-, `=`-dotted edges by the merged `LGraph.mergeP` first, then rebuild
the solid edges (circled iff a loop) and put a `×`-dotted edge on every non-loop solid edge.  `BAGraph.img95_equiv` shows that this is the
map `BAGraph.img` up to relabelling the vertices. -/
def BAGraph.img95 (Γ : BAGraph E I) : PGraph E :=
  let P := (BAAtomic_dot95 Γ).mergeP
  let xs : List (DEdge (P.E' ⊕ P.I')) := (P.g.solid.filter (fun e => e.src ≠ e.dst)).map (fun e => ⟨false, e.src, e.dst⟩)
  let sol : List (SEdge (P.E' ⊕ P.I')) := P.g.solid.map (fun e => ⟨e.σ, decide (e.src = e.dst), e.src, e.dst⟩)
  { P with g := ⟨sol, P.g.waved, xs, P.g.coeff⟩ }

private theorem BAAtomic_dot95_eqRel_iff (Γ : BAGraph E I) (u v : E ⊕ I) :
    (BAAtomic_dot95 Γ).EqRel u v ↔ Γ.atomAdj u v = true := by
  unfold LGraph.EqRel
  simp only [BAAtomic_dot95, BAGraph.atomAdj, List.mem_append, List.mem_map, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨e, (he | ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩), h2, h3⟩
    · exact Or.inl (Or.inl ⟨e, he, h2, h3⟩)
    · exact Or.inl (Or.inr ⟨e', he', h3⟩)
    · exact Or.inr ⟨e', he', h3⟩
  · rintro ((⟨e, he, h1, h3⟩ | ⟨e', he', h3⟩) | ⟨e', he', h3⟩)
    · exact ⟨e, Or.inl he, h1, h3⟩
    · exact ⟨⟨true, e'.x, e'.y⟩, Or.inr (Or.inl ⟨e', he', rfl⟩), rfl, h3⟩
    · exact ⟨⟨true, e'.x, e'.y⟩, Or.inr (Or.inr ⟨e', he', rfl⟩), rfl, h3⟩

private theorem BAAtomic_dot95_eqSetoid (Γ : BAGraph E I) : (BAAtomic_dot95 Γ).eqSetoid = (promoteC Γ).eqSetoid := by
  have h : (BAAtomic_dot95 Γ).EqRel = (promoteC Γ).EqRel := by
    funext u v
    exact propext ((BAAtomic_dot95_eqRel_iff Γ u v).trans (promoteC_eqRel_iff Γ u v).symm)
  unfold LGraph.eqSetoid
  rw [h]

/-- The classes of the two constructions correspond. -/
private def BAAtomic_eC (Γ : BAGraph E I) : (BAAtomic_dot95 Γ).Cls ≃ (promoteC Γ).Cls :=
  Quotient.congr (Equiv.refl _) (fun a b => by rw [BAAtomic_dot95_eqSetoid Γ]; exact Iff.rfl)

private theorem BAAtomic_eC_cls (Γ : BAGraph E I) (v : E ⊕ I) : BAAtomic_eC Γ ((BAAtomic_dot95 Γ).cls v) = (promoteC Γ).cls v := rfl

private theorem BAAtomic_isExt_iff (Γ : BAGraph E I) (q : (BAAtomic_dot95 Γ).Cls) :
    (BAAtomic_dot95 Γ).IsExtCls q ↔ (promoteC Γ).IsExtCls (BAAtomic_eC Γ q) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (BAAtomic_eC Γ).injective ha⟩

private def BAAtomic_eE (Γ : BAGraph E I) : (BAAtomic_dot95 Γ).ExtCls ≃ (promoteC Γ).ExtCls :=
  Equiv.subtypeEquiv (BAAtomic_eC Γ) (BAAtomic_isExt_iff Γ)

private def BAAtomic_eI (Γ : BAGraph E I) : (BAAtomic_dot95 Γ).IntCls ≃ (promoteC Γ).IntCls :=
  Equiv.subtypeEquiv (BAAtomic_eC Γ) (fun q => not_congr (BAAtomic_isExt_iff Γ q))

private theorem BAAtomic_vmap95 (Γ : BAGraph E I) (v : E ⊕ I) :
    Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ) ((BAAtomic_dot95 Γ).vmap v) = (promoteC Γ).vmap v := by
  unfold LGraph.vmap LGraph.vmapC
  by_cases h : (BAAtomic_dot95 Γ).IsExtCls ((BAAtomic_dot95 Γ).cls v)
  · have h' : (promoteC Γ).IsExtCls ((promoteC Γ).cls v) := (BAAtomic_isExt_iff Γ _).1 h
    simp only [h, h', ↓reduceDIte]
    rfl
  · have h' : ¬ (promoteC Γ).IsExtCls ((promoteC Γ).cls v) := fun hh => h ((BAAtomic_isExt_iff Γ _).2 hh)
    simp only [h, h', ↓reduceDIte]
    rfl

private theorem BAAtomic_vmap95_eq_iff (Γ : BAGraph E I) (u v : E ⊕ I) :
    (BAAtomic_dot95 Γ).vmap u = (BAAtomic_dot95 Γ).vmap v ↔ Γ.sameAtom u v = true := by
  have hinj : Function.Injective (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ)) :=
    Sum.map_injective.2 ⟨(BAAtomic_eE Γ).injective, (BAAtomic_eI Γ).injective⟩
  rw [← promoteC_vmap_eq_iff', ← BAAtomic_vmap95 Γ u, ← BAAtomic_vmap95 Γ v]
  exact hinj.eq_iff.symm

private theorem BAAtomic_merge95_solid (Γ : BAGraph E I) :
    (BAAtomic_dot95 Γ).merge.solid = Γ.solid.map (SEdge.map (BAAtomic_dot95 Γ).vmap) := rfl

private theorem BAAtomic_lgraph_ext {E' I' : Type} {G H : LGraph E' I'} (h1 : G.solid = H.solid) (h2 : G.waved = H.waved)
    (h3 : G.dotted = H.dotted) (h4 : G.coeff = H.coeff) : G = H := by
  cases G; cases H; simp_all

/-- **The two constructions give the same graph up to relabelling and the circles** (L4-C2; T2417 target 2), for every BA graph: there are
bijections of the external and of the internal vertices of T2395's `img95` and of the one map `img`, compatible with the maps of the external
vertices, under which the waved edges, the `×`-dotted edges and the coefficient agree (as lists, in the same order) and the solid edges of
`img95` are those of `img` with the circle of every edge set to "it is a loop" (T2395 circles every loop; `img` keeps the circle of `Γ` on a loop).
The packed graphs themselves cannot be equal: their vertex types are quotients of `E ⊕ I` by two relations that agree only propositionally
(T2397 audit D1). -/
theorem BAGraph.img95_equiv_gen (Γ : BAGraph E I) :
    ∃ (eE : Γ.img95.E' ≃ Γ.img.E') (eI : Γ.img95.I' ≃ Γ.img.I'),
      (∀ a, Γ.img.ext a = eE (Γ.img95.ext a)) ∧
      Γ.img.g.waved = (Γ.img95.g.relabel (Sum.map eE eI)).waved ∧
      Γ.img.g.dotted = (Γ.img95.g.relabel (Sum.map eE eI)).dotted ∧
      Γ.img.g.coeff = (Γ.img95.g.relabel (Sum.map eE eI)).coeff ∧
      (Γ.img95.g.relabel (Sum.map eE eI)).solid = Γ.img.g.solid.map fun e => { e with circ := decide (e.src = e.dst) } := by
  refine ⟨BAAtomic_eE Γ, BAAtomic_eI Γ, fun a => rfl, ?_, ?_, rfl, ?_⟩
  · change (promoteC Γ).merge.waved = (LGraph.relabel
      ⟨(BAAtomic_dot95 Γ).merge.solid.map (fun e => ⟨e.σ, decide (e.src = e.dst), e.src, e.dst⟩), (BAAtomic_dot95 Γ).merge.waved,
        ((BAAtomic_dot95 Γ).merge.solid.filter (fun e => e.src ≠ e.dst)).map (fun e => ⟨false, e.src, e.dst⟩), (BAAtomic_dot95 Γ).merge.coeff⟩
      (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ))).waved
    dsimp only [LGraph.relabel]
    change Γ.waved.map (WEdge.map (promoteC Γ).vmap) = ((Γ.waved.map (WEdge.map (BAAtomic_dot95 Γ).vmap)).map _)
    rw [List.map_map]
    apply List.map_congr_left
    intro e _
    change WEdge.mk e.col e.σ ((promoteC Γ).vmap e.x) ((promoteC Γ).vmap e.y) =
      WEdge.mk e.col e.σ (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ) ((BAAtomic_dot95 Γ).vmap e.x))
        (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ) ((BAAtomic_dot95 Γ).vmap e.y))
    rw [BAAtomic_vmap95, BAAtomic_vmap95]
  · change (promoteC Γ).merge.dotted = (LGraph.relabel
      ⟨(BAAtomic_dot95 Γ).merge.solid.map (fun e => ⟨e.σ, decide (e.src = e.dst), e.src, e.dst⟩), (BAAtomic_dot95 Γ).merge.waved,
        ((BAAtomic_dot95 Γ).merge.solid.filter (fun e => e.src ≠ e.dst)).map (fun e => ⟨false, e.src, e.dst⟩), (BAAtomic_dot95 Γ).merge.coeff⟩
      (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ))).dotted
    dsimp only [LGraph.relabel]
    rw [BAAtomic_merge_dotted, BAAtomic_merge95_solid, List.filter_map, List.map_map, List.map_map]
    have hf : ∀ e ∈ Γ.solid, (!Γ.sameAtom e.src e.dst) =
        decide ((SEdge.map (BAAtomic_dot95 Γ).vmap e).src ≠ (SEdge.map (BAAtomic_dot95 Γ).vmap e).dst) := by
      intro e _
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      change _ ↔ (BAAtomic_dot95 Γ).vmap e.src ≠ (BAAtomic_dot95 Γ).vmap e.dst
      rw [ne_eq, BAAtomic_vmap95_eq_iff, Bool.not_eq_true']
      simp
    rw [List.filter_congr hf]
    apply List.map_congr_left
    intro e _
    change DEdge.mk false ((promoteC Γ).vmap e.src) ((promoteC Γ).vmap e.dst) =
      DEdge.mk false (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ) ((BAAtomic_dot95 Γ).vmap e.src))
        (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ) ((BAAtomic_dot95 Γ).vmap e.dst))
    rw [BAAtomic_vmap95, BAAtomic_vmap95]
  · change (LGraph.relabel
      ⟨(BAAtomic_dot95 Γ).merge.solid.map (fun e => ⟨e.σ, decide (e.src = e.dst), e.src, e.dst⟩), (BAAtomic_dot95 Γ).merge.waved,
        ((BAAtomic_dot95 Γ).merge.solid.filter (fun e => e.src ≠ e.dst)).map (fun e => ⟨false, e.src, e.dst⟩), (BAAtomic_dot95 Γ).merge.coeff⟩
      (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ))).solid = (promoteC Γ).merge.solid.map fun e => { e with circ := decide (e.src = e.dst) }
    dsimp only [LGraph.relabel]
    rw [BAAtomic_merge_solid, BAAtomic_merge95_solid, List.map_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro e he
    have h2 : decide ((BAAtomic_dot95 Γ).vmap e.src = (BAAtomic_dot95 Γ).vmap e.dst) =
        decide ((promoteC Γ).vmap e.src = (promoteC Γ).vmap e.dst) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, BAAtomic_vmap95_eq_iff, promoteC_vmap_eq_iff']
    change SEdge.mk e.σ (decide ((BAAtomic_dot95 Γ).vmap e.src = (BAAtomic_dot95 Γ).vmap e.dst))
        (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ) ((BAAtomic_dot95 Γ).vmap e.src))
        (Sum.map (BAAtomic_eE Γ) (BAAtomic_eI Γ) ((BAAtomic_dot95 Γ).vmap e.dst)) =
      SEdge.mk e.σ (decide ((promoteC Γ).vmap e.src = (promoteC Γ).vmap e.dst)) ((promoteC Γ).vmap e.src) ((promoteC Γ).vmap e.dst)
    rw [h2, BAAtomic_vmap95, BAAtomic_vmap95]

/-- **The two constructions give the same graph up to relabelling** (L4-C2; T2417 target 2), for a BA-normal graph: there are bijections of
the external and of the internal vertices of T2395's `img95` and of the one map `img`, compatible with the maps of the external vertices,
that carry the graph of `img95` onto the graph of `img` (record equality: the lists of solid, waved and `×`-dotted edges, in the same order,
with the same circles, and the coefficient). -/
theorem BAGraph.img95_equiv (Γ : BAGraph E I) (hN : Γ.Normal) :
    ∃ (eE : Γ.img95.E' ≃ Γ.img.E') (eI : Γ.img95.I' ≃ Γ.img.I'),
      (∀ a, Γ.img.ext a = eE (Γ.img95.ext a)) ∧ Γ.img.g = Γ.img95.g.relabel (Sum.map eE eI) := by
  obtain ⟨eE, eI, hext, hw, hd, hc, hs⟩ := Γ.img95_equiv_gen
  refine ⟨eE, eI, hext, BAAtomic_lgraph_ext ?_ hw hd hc⟩
  rw [hs]
  conv_lhs => rw [← List.map_id Γ.img.g.solid]
  refine List.map_congr_left fun e he => ?_
  have h := (Γ.img_normal hN).2 e he
  obtain ⟨σ, c, a, b⟩ := e
  cases c <;> simp_all

end Img95

/-! ## 10. Compiled instances: the K1 case (an `M`-edge inside an atom, one between atoms) -/

section Instances

/-- A concrete BA graph (`E = Fin 2`, `I = Fin 3`; external `x = inl 0`, `y = inl 1`, internal `α, β, γ = inr 0, inr 1, inr 2`): solid
`blue α→β` (inside the atom `{α, β}`, K1), `blue x→α` (between atoms), `red γ→y` (between atoms), `blue γ→γ` (a self-loop), all circled; waved
`β — γ`; the original `×`-dot `x — α`; the `M`-dotted edge `M_{αβ}`.  Atoms `{x}, {y}, {α, β}, {γ}`. -/
private def BAAtomic_G0 : BAGraph (Fin 2) (Fin 3) where
  solid := [⟨true, true, .inr 0, .inr 1⟩, ⟨true, true, .inl 0, .inr 0⟩, ⟨false, true, .inr 2, .inl 1⟩, ⟨true, true, .inr 2, .inr 2⟩]
  waved := [⟨false, true, .inr 1, .inr 2⟩]
  dotted := [⟨false, .inl 0, .inr 0⟩]
  coeff := 1
  psi := []
  mdot := [⟨true, .inr 0, .inr 1⟩]

/-- A concrete locally standard BA graph (`E = Fin 2`, `I = Fin 2`): solid `blue x→α`, `red y→β`, `M_{αβ}`; the internal atom `{α, β}` has the
two edges `[blue, red]` of charge `+1 - 1 = 0`. -/
private def BAAtomic_G1 : BAGraph (Fin 2) (Fin 2) where
  solid := [⟨true, true, .inl 0, .inr 0⟩, ⟨false, true, .inl 1, .inr 1⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := [⟨true, .inr 0, .inr 1⟩]

private theorem BAAtomic_G0_normal : BAAtomic_G0.Normal := by decide
private theorem BAAtomic_G1_normal : BAAtomic_G1.Normal := by decide

/-- The data are nondegenerate: `n_S = 4`, `n_W = 1`, `n_A = 2`, `n_M = 1`, two atom-level loops (the self-loop and the K1 edge), two
external atoms; `M_{αβ}` is inside the atom `{α, β}` and the atom of `α` contains `β` but not `γ`. -/
example : BAAtomic_G0.nS = 4 ∧ BAAtomic_G0.nW = 1 ∧ BAAtomic_G0.nA = 2 ∧ BAAtomic_G0.nM = 1 ∧ BAAtomic_G0.nLoops = 2 ∧
    BAAtomic_G0.nExt = 2 ∧ BAAtomic_G0.nPairs = 0 ∧ Sum.inr 1 ∈ BAAtomic_G0.atom (Sum.inr 0) ∧
    Sum.inr 2 ∉ BAAtomic_G0.atom (Sum.inr 0) ∧ Sum.inr 2 ∈ BAAtomic_G0.mol (Sum.inr 0) := by decide

/-- **`BAimg` at `G0`** (every deterministic hypothesis discharged: `Γ.Normal`; `G0` is not locally standard). -/
example : BAAtomic_G0.img.g.counters = BAAtomic_G0.counters ∧ BAAtomic_G0.img.g.lvl1NLoops = BAAtomic_G0.nLoops ∧
    BAAtomic_G0.img.g.lvl1NPairs = BAAtomic_G0.nPairs ∧ Fintype.card BAAtomic_G0.img.E' = BAAtomic_G0.nExt ∧
    (BAAtomic_G0.Normal → BAAtomic_G0.img.g.Normal) ∧ (BAAtomic_G0.Normal → (BAAtomic_G0.LocStd ↔ BAAtomic_G0.img.g.LocStd)) :=
  BAimg_holds BAAtomic_G0

/-- `G1` is locally standard (so is its image), and the image has two external vertices. -/
example : BAAtomic_G1.LocStd ∧ BAAtomic_G1.img.g.LocStd ∧ Fintype.card BAAtomic_G1.img.E' = 2 ∧ BAAtomic_G1.nPairs = 1 := by
  have h : BAAtomic_G1.LocStd := by decide
  refine ⟨h, (BAimg_holds BAAtomic_G1).2.2.2.2.2 BAAtomic_G1_normal |>.1 h, ?_, by decide⟩
  rw [(BAimg_holds BAAtomic_G1).2.2.2.1]
  decide

example : ¬ BAAtomic_G0.LocStd ∧ ¬ BAAtomic_G0.img.g.LocStd :=
  ⟨by decide, fun h => by
    have : BAAtomic_G0.LocStd := ((BAimg_holds BAAtomic_G0).2.2.2.2.2 BAAtomic_G0_normal).2 h
    exact absurd this (by decide)⟩

/-- **(m0), (m1), (m2) at the packed graph `baPG G0`.** -/
example : (BAPGraph.img (baPG BAAtomic_G0)).g.Normal ∧ LGraph.CircIffLoop (BAPGraph.img (baPG BAAtomic_G0)).g :=
  BAImgNormal_holds (baPG BAAtomic_G0) BAAtomic_G0_normal

example : (BAPGraph.img (baPG BAAtomic_G0)).g.counters = (baPG BAAtomic_G0).g.counters :=
  BAImgCounters_holds (baPG BAAtomic_G0)

example (u v : (baPG BAAtomic_G0).E' ⊕ (baPG BAAtomic_G0).I') :
    (promoteC (baPG BAAtomic_G0).g).merge.molOf ((promoteC (baPG BAAtomic_G0).g).vmap u) =
      (promoteC (baPG BAAtomic_G0).g).merge.molOf ((promoteC (baPG BAAtomic_G0).g).vmap v) ↔ v ∈ (baPG BAAtomic_G0).g.mol u :=
  BAImgMol_holds (baPG BAAtomic_G0) u v

/-- (m2) at `G0`, `u = α`, `v = γ`: the molecule of the image vertex of `α` contains the image vertex of `γ` (they are joined through the
waved edge `β — γ` and the atom `{α, β}`). -/
example : (promoteC BAAtomic_G0).merge.molOf ((promoteC BAAtomic_G0).vmap (Sum.inr 0)) =
    (promoteC BAAtomic_G0).merge.molOf ((promoteC BAAtomic_G0).vmap (Sum.inr 2)) :=
  (BAAtomic_G0.img_molOf_eq_iff _ _).2 (by decide)

/-- Target 2 at `G0`: the two constructions agree up to relabelling. -/
example : ∃ (eE : BAAtomic_G0.img95.E' ≃ BAAtomic_G0.img.E') (eI : BAAtomic_G0.img95.I' ≃ BAAtomic_G0.img.I'),
    (∀ a, BAAtomic_G0.img.ext a = eE (BAAtomic_G0.img95.ext a)) ∧
      BAAtomic_G0.img.g = BAAtomic_G0.img95.g.relabel (Sum.map eE eI) :=
  BAAtomic_G0.img95_equiv BAAtomic_G0_normal

end Instances

end RBM.Graph
