/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim2
import RBM3D.Graph.BASim3
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAExpandWOrd
import RBM3D.Graph.BAScost
import RBM3D.Graph.LWLvl1

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# BA-L L3a4 (T2442), part 1: the BA measure predicates, the partition structure and the counter half of Lemma S

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:353-409` (`lanlw`, `lem_lweight`, `GGGamma`, `lvl1 lemma`).  Design: `docs/reports/T2395-design.md` §6
(row L3a4), §3 Step 3; probe `t/T2395:RBM3D/Probe/T2395Pins.lean:44-55, 259-272, 289-337`.  The BA twin of `Graph/LWLvl1.lean` §1 (`:64-997`) and of `lvl1_step_good`
(`:3290`), with the band's `×`-dot partition counters replaced by R1's simulation `BAsim'` (`Graph/BASim3`, `baSim'_holds`).

## Contents (namespace `RBM.Graph`; private prefix `BALvl1B_`, `RBM.Graph.BALvl1B_*` public helpers used by `Graph/BALvl1B2`)

1. **The measure predicates** (probe, verbatim): `BALvl1Good`, `BALvl1GoodLit`, `BAlvl1StepGood`, `BAstepMono`, `ba_good_of_lit`.
2. **The reduction for `BAsim'`** `ba_lvl1StepGood_of_sim'` (probe 323-337 with `BAsim' m` for `BAsim m`), and `BALvl1B_lit_of_band` (probe 311 on the `baInv` equalities).
3. **Coarsening and the partition structure** (target 3): `BALvl1B_coarse`, `BALvl1B_adj_mono`, `BALvl1B_part_struct`.
4. **The counters at the terms**, the assembly `BALvl1B_outs_mono`, and the cases `weight`, `edge`, `gg` of `BAstepMono`.
5. Compiled instances.

The cases `within`, `ggSplit` (macro claims), `baStepMono_holds`, `baLvl1StepGood_holds` are in `Graph/BALvl1B2`.
-/

noncomputable section

namespace RBM.Graph

open RBM

/-! ## 1. The measure predicates (the probe, verbatim) -/

section Measure

variable {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁] [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]

/-- **`Lvl1Good` of the band on atoms, with `#external atoms` after `ord`** (D§2, correction K3): the order does not fall, `n_M` and
`n_A - n_W` do not grow, the external atoms do not multiply, and either the order rises or it stays and `(nExt, loops, n_S, pairs)` falls. -/
def BALvl1Good (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Prop :=
  Γ.scalingOrder ≤ Q.scalingOrder ∧ Q.nM ≤ Γ.nM ∧ ((Q.nA : ℤ) - Q.nW ≤ (Γ.nA : ℤ) - Γ.nW) ∧ Q.nExt ≤ Γ.nExt ∧
    (Γ.scalingOrder < Q.scalingOrder ∨ (Q.scalingOrder = Γ.scalingOrder ∧
      (Q.nExt < Γ.nExt ∨ (Q.nExt = Γ.nExt ∧ (Q.nLoops < Γ.nLoops ∨ (Q.nLoops = Γ.nLoops ∧
        (Q.nS < Γ.nS ∨ (Q.nS = Γ.nS ∧ Q.nPairs < Γ.nPairs))))))))

/-- the band-literal measure `(loops, n_S, pairs)` of `Lvl1Good` (`LWLvl1.lean:989-992`) read on atoms, without `nExt`. -/
def BALvl1GoodLit (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Prop :=
  Γ.scalingOrder ≤ Q.scalingOrder ∧ Q.nM ≤ Γ.nM ∧ ((Q.nA : ℤ) - Q.nW ≤ (Γ.nA : ℤ) - Γ.nW) ∧
    (Γ.scalingOrder < Q.scalingOrder ∨ (Q.scalingOrder = Γ.scalingOrder ∧
      (Q.nLoops < Γ.nLoops ∨ (Q.nLoops = Γ.nLoops ∧ (Q.nS < Γ.nS ∨ (Q.nS = Γ.nS ∧ Q.nPairs < Γ.nPairs))))))

instance (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Decidable (BALvl1Good Γ Q) := by unfold BALvl1Good; infer_instance
instance (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Decidable (BALvl1GoodLit Γ Q) := by unfold BALvl1GoodLit; infer_instance

/-- the transport lemma (D§2): the band-literal measure and `nExt ≤` give `BALvl1Good`. -/
theorem ba_good_of_lit {Γ : BAGraph E₁ I₁} {Q : BAGraph E₂ I₂} (h : BALvl1GoodLit Γ Q) (hx : Q.nExt ≤ Γ.nExt) : BALvl1Good Γ Q := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, hx, ?_⟩
  rcases h4 with h | ⟨h, h'⟩
  · exact Or.inl h
  · rcases hx.lt_or_eq with hl | he
    · exact Or.inr ⟨h, Or.inl hl⟩
    · exact Or.inr ⟨h, Or.inr ⟨he, h'⟩⟩

end Measure

/-- L3a4: every output of a step is normal and good (the BA `lvl1_step_good`, `LWLvl1.lean:3290`). -/
def BAlvl1StepGood : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs → P.g.Normal →
  ∀ Q ∈ outs, Q.g.Normal ∧ BALvl1Good P.g Q.g

/-- **L3a4, the counter half of Lemma S** (D§3 Step 3 (a), (c)): every output of a frame step at a normal graph is normal, its order does
not fall, `n_M`, `n_A - n_W` and the number of external atoms do not grow. -/
def BAstepMono : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal → ∀ Q ∈ outs, Q.g.Normal ∧
  P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧ ((Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧ Q.g.nExt ≤ P.g.nExt

/-! ## 2. The reduction for `BAsim'` (probe 301-337) -/

section Reduction

variable {E₁ I₁ E₂ I₂ E₃ I₃ E₄ I₄ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁] [Fintype E₂] [DecidableEq E₂]
  [Fintype I₂] [DecidableEq I₂] [Fintype E₃] [DecidableEq E₃] [Fintype I₃] [DecidableEq I₃] [Fintype E₄] [DecidableEq E₄] [Fintype I₄] [DecidableEq I₄]

/-- `BALvl1Good` reads only the counters, `nExt`, loops and pairs of both graphs. -/
private theorem BALvl1B_good_congr {Γ : BAGraph E₁ I₁} {Q : BAGraph E₂ I₂} {Γ' : BAGraph E₃ I₃} {Q' : BAGraph E₄ I₄}
    (hΓ : Γ'.counters = Γ.counters ∧ Γ'.nExt = Γ.nExt ∧ Γ'.nLoops = Γ.nLoops ∧ Γ'.nPairs = Γ.nPairs)
    (hQ : Q'.counters = Q.counters ∧ Q'.nExt = Q.nExt ∧ Q'.nLoops = Q.nLoops ∧ Q'.nPairs = Q.nPairs) (h : BALvl1Good Γ Q) :
    BALvl1Good Γ' Q' := by
  obtain ⟨hc, he, hl, hp⟩ := hΓ; obtain ⟨hc', he', hl', hp'⟩ := hQ
  unfold BALvl1Good BAGraph.scalingOrder at *
  simp only [BAGraph.counters, Counters.mk.injEq] at hc hc'
  obtain ⟨a1, a2, a3, a4, -⟩ := hc; obtain ⟨b1, b2, b3, b4, -⟩ := hc'
  simp only [BAGraph.counters, a1, a2, a3, a4, b1, b2, b3, b4, he, he', hl, hl', hp, hp'] at h ⊢; exact h

/-- **The band's `Lvl1Good` at a packed band graph with the invariants of `P`, for an output with the invariants of `Q`, is `BALvl1GoodLit P Q`**
(probe 311, restated on the invariant tuples `PGraph.baInv`, `BAPGraph.baInv` of R1: the tuples read the order, `n_M`, `n_A - n_W`, loops, `n_S`, pairs, `nExt`). -/
theorem BALvl1B_lit_of_band {E : Type} {P Q : BAPGraph E} {G Q0 : PGraph E} (hG : G.baInv = P.baInv) (hQ : Q0.baInv = Q.baInv)
    (h : Lvl1Good G.g Q0.g) : BALvl1GoodLit P.g Q.g := by
  simp only [PGraph.baInv, BAPGraph.baInv, Prod.mk.injEq] at hG hQ
  obtain ⟨g1, g2, g3, g4, g5, g6, -⟩ := hG
  obtain ⟨q1, q2, q3, q4, q5, q6, -⟩ := hQ
  unfold BALvl1GoodLit; unfold Lvl1Good at h
  rw [← g1, ← g2, ← g3, ← g4, ← g5, ← g6, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6]
  exact h

end Reduction

/-- **The reduction of S′ for R1's `BAsim'`** (D§2; probe 323-337 with `BAsim' m` in place of `BAsim m`): the BA `lvl1_step_good` (L3a4) from the image (R0), the simulation (R1,
`BAsim'`, `baSim'_holds`), the counter half of Lemma S (`BAstepMono`, `baStepMono_holds` in `Graph/BALvl1B2`), the twist invariance (L3a1) and the band's `lvl1_step_good`
(`LWLvl1.lean:3290`) at the atomic image `T.img` of the BA graph `T` that `BAsim'` provides. -/
theorem ba_lvl1StepGood_of_sim' : ∀ m : ℂ, BAimg → BAsim' m → BAstepMono → BAtwistInv → BAlvl1StepGood := by
  intro m hi hs hm ht E P outs hst hP Q hQ
  obtain ⟨c, t, F, hF, rfl⟩ := hst
  obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hQ
  have hPt : (P.twist c t).g.Normal := (ht c t P.g).1 hP
  obtain ⟨hN, ho, hnM, hAW, hx⟩ := hm _ _ hF hPt Q' hQ'
  have hg : BALvl1Good (P.twist c t).g Q'.g := by
    rcases hs _ _ hF hPt Q' hQ' with ⟨T, L', hTN, hTinv, hstT, Q0, hQ0, hQ0inv⟩ | h | h
    · have hNimg : T.img.g.Normal := (hi T.g).2.2.2.2.1 hTN
      exact ba_good_of_lit (BALvl1B_lit_of_band ((BASim_img_baInv T).trans hTinv) hQ0inv (lvl1_step_good hstT hNimg Q0 hQ0).2) hx
    · exact ⟨ho, hnM, hAW, hx, Or.inl h⟩
    · rcases ho.lt_or_eq with h' | h'
      · exact ⟨ho, hnM, hAW, hx, Or.inl h'⟩
      · exact ⟨ho, hnM, hAW, hx, Or.inr ⟨h'.symm, Or.inl h⟩⟩
  obtain ⟨-, e, l, p⟩ := ht c t P.g; obtain ⟨-, e', l', p'⟩ := ht c t Q'.g
  exact ⟨(ht c t Q'.g).1 hN, BALvl1B_good_congr ⟨(ba_twist_counters c t P.g).symm, e.symm, l.symm, p.symm⟩ ⟨ba_twist_counters c t Q'.g, e', l', p'⟩ hg⟩

/-! ## 3. Coarsening and the partition structure (target 3; twin of `LWLvl1` §1 `lvl1_nM_le`, `lvl1_part_nM`, `:531-602`) -/

section Coarse

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the number of classes consisting of vertices that satisfy `i` can only drop when the classes are coarsened (the injection of `BAWeightOp_nA_le`, via `BASim_card_image_le`) -/
theorem BALvl1B_cnt_le {V : Type} [Fintype V] [DecidableEq V] (i : V → Bool) (cl cl' : V → Finset V)
    (hself : ∀ v, v ∈ cl v) (hsub : ∀ a b, b ∈ cl a → b ∈ cl' a) (hsym : ∀ v w, w ∈ cl' v → cl' w = cl' v) :
    ((Finset.univ.filter fun v => ∀ w ∈ cl' v, i w = true).image cl').card ≤
      ((Finset.univ.filter fun v => ∀ w ∈ cl v, i w = true).image cl).card := by
  classical
  have hS : (Finset.univ.filter fun v => ∀ w ∈ cl' v, i w = true) ⊆ (Finset.univ.filter fun v => ∀ w ∈ cl v, i w = true) := fun v hv => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact fun w hw => hv w (hsub _ _ hw)
  refine ((BASim_card_image_le (Finset.univ.filter fun v => ∀ w ∈ cl' v, i w = true) cl cl' (fun u _ v _ h => ?_)).1).trans
    (Finset.card_le_card (Finset.image_subset_image hS))
  have hv : v ∈ cl' u := hsub u v (by rw [h]; exact hself v)
  exact (hsym u v hv).symm

/-- the atoms of a graph: `w ∈ atom v` makes the atoms equal -/
theorem BALvl1B_atom_eq_of_mem (G : BAGraph E I) {v w : E ⊕ I} (h : w ∈ G.atom v) : G.atom w = G.atom v :=
  ((BAGraph.BAAtomic_sameAtom_iff_atom_eq G v w).1 (by simpa [BAGraph.sameAtom] using h)).symm

/-- the molecules of a graph: `w ∈ mol v` makes the molecules equal -/
theorem BALvl1B_mol_eq_of_mem (G : BAGraph E I) {v w : E ⊕ I} (h : w ∈ G.mol v) : G.mol w = G.mol v := by
  rw [BAGraph.mem_mol_iff] at h
  have hs : ∀ x y, G.adj x y = true → G.adj y x = true := fun x y hxy => by
    have : G.adj x y = G.adj y x := by
      simp only [BAGraph.adj, RBM.Graph.LGraph.adj, BAGraph.atomAdj, or_comm]
    rwa [this] at hxy
  have hsymm : ∀ {x y : E ⊕ I}, Relation.ReflTransGen (fun a b => G.adj a b = true) x y →
      Relation.ReflTransGen (fun a b => G.adj a b = true) y x := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hs _ _ hbc) ih
  ext w'
  rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx; exact (hsymm h).trans hx

/-- more `M`-, `Ψ`-, `=`-dotted and waved edges: the atoms and the molecules coarsen -/
theorem BALvl1B_adj_mono (G₁ G₂ : BAGraph E I) (hw : G₁.waved = G₂.waved) (hd : G₁.dotted = G₂.dotted) (hp : G₁.psi = G₂.psi)
    (hm : ∀ e ∈ G₁.mdot, e ∈ G₂.mdot) :
    (∀ u v, G₁.atomAdj u v = true → G₂.atomAdj u v = true) ∧ (∀ u v, G₁.adj u v = true → G₂.adj u v = true) := by
  have hA : ∀ u v, G₁.atomAdj u v = true → G₂.atomAdj u v = true := by
    intro u v h
    simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with (⟨e, he, h1, h2⟩ | ⟨e, he, h2⟩) | ⟨e, he, h2⟩
    · exact Or.inl (Or.inl ⟨e, hd ▸ he, h1, h2⟩)
    · exact Or.inl (Or.inr ⟨e, hp ▸ he, h2⟩)
    · exact Or.inr ⟨e, hm e he, h2⟩
  refine ⟨hA, fun u v h => ?_⟩
  simp only [BAGraph.adj, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · left
    have : G₁.toLGraph.adj u v = G₂.toLGraph.adj u v := by simp only [LGraph.adj, hw, hd]
    rwa [← this]
  · exact Or.inr (hA u v h)

/-- **Coarsening** (twin of `lvl1_nM_le`, `LWLvl1:531`; the injection of `BAWeightOp_nA_le`): if every atom edge and every molecule edge of `G₁` is one of `G₂`, then `G₂` has no more internal atoms,
no more internal molecules and no more atoms with an external vertex. -/
theorem BALvl1B_coarse (G₁ G₂ : BAGraph E I) (hA : ∀ u v, G₁.atomAdj u v = true → G₂.atomAdj u v = true)
    (hM : ∀ u v, G₁.adj u v = true → G₂.adj u v = true) : G₂.nA ≤ G₁.nA ∧ G₂.nM ≤ G₁.nM ∧ G₂.nExt ≤ G₁.nExt := by
  classical
  have hsa : ∀ a b, b ∈ G₁.atom a → b ∈ G₂.atom a := fun a b h => by
    rw [BAGraph.mem_atom_iff] at h ⊢
    exact Relation.ReflTransGen.mono (fun x y hxy => hA x y hxy) a b h
  have hsm : ∀ a b, b ∈ G₁.mol a → b ∈ G₂.mol a := fun a b h => by
    rw [BAGraph.mem_mol_iff] at h ⊢
    exact Relation.ReflTransGen.mono (fun x y hxy => hM x y hxy) a b h
  have sa : ∀ v, v ∈ G₁.atom v := fun v => (BAGraph.mem_atom_iff G₁ v v).2 Relation.ReflTransGen.refl
  have sm : ∀ v, v ∈ G₁.mol v := fun v => (BAGraph.mem_mol_iff G₁ v v).2 Relation.ReflTransGen.refl
  refine ⟨?_, ?_, ?_⟩
  · exact BALvl1B_cnt_le Sum.isRight G₁.atom G₂.atom sa hsa (fun v w h => BALvl1B_atom_eq_of_mem G₂ h)
  · exact BALvl1B_cnt_le Sum.isRight G₁.mol G₂.mol sm hsm (fun v w h => BALvl1B_mol_eq_of_mem G₂ h)
  · unfold BAGraph.nExt
    refine (BASim_card_image_le (Finset.univ.filter fun v : E ⊕ I => v.isLeft = true) G₁.atom G₂.atom (fun u _ v _ h => ?_)).1
    have hv : v ∈ G₂.atom u := hsa u v (by rw [h]; exact sa v)
    exact (BALvl1B_atom_eq_of_mem G₂ hv).symm

/-- the terms of the `M`-split of `T` have the waved, dotted and `Ψ`-dotted edges of `T°` and more `M`-dotted ones -/
theorem BALvl1B_splitG_struct (T : BAGraph E I) : ∀ Δ ∈ T.splitG, Δ.waved = (BAWeightOp_circ T).waved ∧ Δ.dotted = (BAWeightOp_circ T).dotted ∧
    Δ.psi = (BAWeightOp_circ T).psi ∧ ∀ e ∈ (BAWeightOp_circ T).mdot, e ∈ Δ.mdot := by
  intro Δ hΔ
  simp only [BAGraph.splitG, List.mem_map] at hΔ
  obtain ⟨r, hr, rfl⟩ := hΔ
  exact ⟨rfl, rfl, rfl, fun e he => List.mem_append_right _ he⟩

end Coarse

section PartStruct

variable {E0 : Type}

/-- **Target 3, the partition structure and the merge budget** (`T2395` design §3 Step 3 (a); twin of `lvl1_part_nM`, `LWLvl1:602`): for a term `T` that extends a normal graph `G` (`BASim_Ext`) and a term `Δ` of its
`M`-split, `Δ` is normal, the packed output of `Δ` has the invariants of `Δ` (`BASim_outOf_baInv`), and against `T°` (every solid edge circled) the number of waved edges is equal and the numbers of internal atoms,
internal molecules and atoms with an external vertex are not larger (an `M`-split only joins atoms and molecules); `Δ` has no more atoms with an external vertex than `G`. -/
theorem BALvl1B_part_struct (P : BAPGraph E0) {I0 : Type} [Fintype I0] [DecidableEq I0] (G : BAGraph P.E' I0) {k : ℕ}
    {T : BAGraph P.E' (I0 ⊕ Fin k)} (hExt : BASim_Ext G k T) (hG : G.Normal) :
    ∀ Δ ∈ T.splitG, Δ.Normal ∧ (P.BASim_outOf Δ).baInv = BASim_inv Δ ∧ Δ.nW = (BAWeightOp_circ T).nW ∧ Δ.nA ≤ (BAWeightOp_circ T).nA ∧
      Δ.nM ≤ (BAWeightOp_circ T).nM ∧ Δ.nExt ≤ (BAWeightOp_circ T).nExt ∧ Δ.nExt ≤ G.nExt := by
  intro Δ hΔ
  have hN := BASim_splitG_normal hExt hG Δ hΔ
  obtain ⟨hw, hd, hp, hm⟩ := BALvl1B_splitG_struct T Δ hΔ
  obtain ⟨hA, hAdj⟩ := BALvl1B_adj_mono (BAWeightOp_circ T) Δ hw.symm hd.symm hp.symm hm
  obtain ⟨c1, c2, c3⟩ := BALvl1B_coarse _ Δ hA hAdj
  refine ⟨hN, BASim_outOf_baInv P Δ hN, (BAGraph.splitG_edges T Δ hΔ).1, c1, c2, c3, ?_⟩
  exact (BASim_nExt_le G Δ (fun u v h => BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj (BASim_Ext_split hExt Δ hΔ) u v h))).1

end PartStruct

/-! ## 4. The counters at the terms and the assembly of `BAstepMono` for one list of terms -/

section Terms

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `T°` has the counters of `T` (copy of the private `BAWeightOp_circ_counters`) -/
theorem BALvl1B_circ_counters (T : BAGraph E I) : (BAWeightOp_circ T).counters = T.counters := by
  have hS : (BAWeightOp_circ T).nS = T.nS := by simp [BAGraph.nS, BAWeightOp_circ]
  simp only [BAGraph.counters, hS]
  rfl

/-- a generic extension of a normal graph with circled new solid edges is normal (copy of the private `BAWeightOp_ext_normal`) -/
theorem BALvl1B_ext_normal (k : ℕ) (Γ : BAGraph E I) (hN : Γ.Normal) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (hrest : ∀ e ∈ rest, e.circ = true) (hs : ∀ e ∈ s, e.circ = true) : (BAGraph.ext k Γ rest s w md).Normal := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact hN.1 e0 he0
  · rcases List.mem_append.1 he with he | he
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact hrest e0 he0
    · exact hs e he

/-- the counters at `T°` of a term whose counters are those of the parent with `d` more waved edges and `d` more internal atoms: `n_M` and `n_A - n_W` do not grow -/
theorem BALvl1B_mono_of_counters {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] {T : BAGraph E' I'} {Γ : BAGraph E I} {s d : ℕ}
    (c : T.counters = ⟨s, Γ.nW + d, Γ.nA + d, Γ.nM, 0, 0⟩) :
    (BAWeightOp_circ T).nM ≤ Γ.nM ∧ ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW ≤ (Γ.nA : ℤ) - Γ.nW := by
  have c' := (BALvl1B_circ_counters T).trans c
  have hnM : (BAWeightOp_circ T).nM = Γ.nM := congrArg Counters.nM c'
  have hnA : (BAWeightOp_circ T).nA = Γ.nA + d := congrArg Counters.nV c'
  have hnW : (BAWeightOp_circ T).nW = Γ.nW + d := congrArg Counters.nW c'
  refine ⟨hnM.le, ?_⟩
  rw [hnA, hnW]; push_cast; omega

/-- the counters of an extension of `Γ` by two new vertices, a waved edge `α β` and the `M`-edge `x α`: `n_W + 1`, `n_A + 1`, `n_M` (`BASim_counters_tr2` at `y = x`; the extra `M`-edge `α x` changes no atom) -/
theorem BALvl1B_ext1 (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) :
    (BAGraph.ext 2 Γ rest s [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 x) (bpv 0)]).counters =
      ⟨rest.length + s.length, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩ := by
  have hT0 : BASim_ExtraDot (BAGraph.ext 2 Γ rest s [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 x) (bpv 0)])
      (BASim_tr2 Γ rest s [bpW false (bpv 0) (bpv 1)] x x) (bpM (bpv 0) (owxEmb 2 x)) :=
    ⟨rfl, rfl, fun z => by simp [BASim_tr2, BAGraph.ext, bpM]; aesop⟩
  have hd : (BAGraph.ext 2 Γ rest s [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 x) (bpv 0)]).sameAtom (bpM (bpv 0) (owxEmb 2 x)).x
      (bpM (bpv 0) (owxEmb 2 x)).y = true := by
    have h1 : atomSetoid (BAGraph.ext 2 Γ rest s [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 x) (bpv 0)]) (owxEmb 2 x) (bpv 0) :=
      BAScost_atomSetoid_ext_md Γ rest s [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 x) (bpv 0)] (bpM (owxEmb 2 x) (bpv 0)) (by simp)
    rw [BASim_sameAtom_iff]
    exact (atomSetoid _).symm h1
  obtain ⟨h12, h21⟩ := BASim_extraDot_atomAdj hT0 hd
  have := (BASim_counters_congr hT0.1 h12 h21).1
  rw [← this]
  exact BASim_counters_tr2 Γ rest s x x (BAScost_sameAtom_self Γ x)

/-- **A term with the waved, dotted and `Ψ`-dotted edges of a reference graph `B` and more `M`-dotted edges** (`B` as in `BALvl1B_ext1`: `n_W + d`, `n_A + d`, `n_M` of the parent): at `T°` the
numbers `n_M` and `n_A - n_W` do not grow (coarsening) -/
theorem BALvl1B_mono_of_ref {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] {Γ : BAGraph E I} {B T : BAGraph E' I'} {d : ℕ}
    (hw : B.waved = T.waved) (hd : B.dotted = T.dotted) (hp : B.psi = T.psi) (hm : ∀ e ∈ B.mdot, e ∈ T.mdot)
    (hB : B.nW = Γ.nW + d ∧ B.nA = Γ.nA + d ∧ B.nM = Γ.nM) :
    (BAWeightOp_circ T).nM ≤ Γ.nM ∧ ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW ≤ (Γ.nA : ℤ) - Γ.nW := by
  obtain ⟨hA, hAdj⟩ := BALvl1B_adj_mono B (BAWeightOp_circ T) hw hd hp hm
  obtain ⟨c1, c2, -⟩ := BALvl1B_coarse B _ hA hAdj
  have hW : (BAWeightOp_circ T).nW = B.nW := (congrArg List.length hw).symm
  refine ⟨c2.trans hB.2.2.le, ?_⟩
  rw [hW, hB.1]
  have := hB.2.1
  have c1' : ((BAWeightOp_circ T).nA : ℤ) ≤ B.nA := by exact_mod_cast c1
  rw [this] at c1'
  push_cast at c1' ⊢
  omega

/-- the terms of `lanlw`: `n_M`, `n_A - n_W` at `T°` do not grow (`lanlwT1_counters`, `lanlwD_counters`) -/
theorem BALvl1B_lanlw_mono (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (h1 : p.1.σ = true) (h2 : p.1.circ = true) :
    ∀ T ∈ BAGraph.lanlwTerms Γ p, (BAWeightOp_circ T).nM ≤ Γ.nM ∧ ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW ≤ (Γ.nA : ℤ) - Γ.nW := by
  intro T hT
  simp only [BAGraph.lanlwTerms, List.mem_cons, List.mem_map] at hT
  rcases hT with rfl | ⟨q, hq, rfl⟩
  · exact BALvl1B_mono_of_counters (lanlwT1_counters Γ p hp h1 h2)
  · exact BALvl1B_mono_of_counters (lanlwD_counters Γ p hp h1 h2 q hq)

end Terms

section Assembly

variable {E0 : Type}

/-- the five conclusions of `BAstepMono` for an output `Q` of a step at `P` -/
def BALvl1B_Mono (P Q : BAPGraph E0) : Prop :=
  Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧ ((Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧ Q.g.nExt ≤ P.g.nExt

/-- an output of a list of terms is the packed output of a term of the `M`-split of one of the terms -/
theorem BALvl1B_mem_outsOf (P : BAPGraph E0) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')) {Q : BAPGraph E0}
    (h : Q ∈ P.outsOf Ts) : ∃ T ∈ Ts, ∃ Δ ∈ T.splitG, P.BASim_outOf Δ = Q := by
  unfold BAPGraph.outsOf at h
  obtain ⟨T, hT, h⟩ := List.mem_flatMap.1 h
  obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 h
  obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 (show Q' ∈ T.splitG.map BAGraph.packMerge from hQ')
  exact ⟨T, hT, Δ, hΔ, rfl⟩

/-- **The assembly of `BAstepMono` for one list of terms `Ts` over a base graph `G` with the invariants of `P`** (T2395 design §3 Step 3 (a)): if every term extends the normal graph `G`, has
`ord G ≤ ordG T`, and has at `T°` no more internal molecules and no larger `n_A - n_W` than `G`, then every output of `P.outsOf Ts` is normal, its order does not fall, `n_M`, `n_A - n_W` and `nExt` do not grow
(target 3 `BALvl1B_part_struct` for the `M`-split and the packing). -/
theorem BALvl1B_outs_mono (P : BAPGraph E0) {I0 : Type} [Fintype I0] [DecidableEq I0] (G : BAGraph P.E' I0) {k : ℕ}
    (Ts : List (BAGraph P.E' (I0 ⊕ Fin k))) (hG : G.Normal)
    (hinv : G.scalingOrder = P.g.scalingOrder ∧ G.nM = P.g.nM ∧ (G.nA : ℤ) - G.nW = (P.g.nA : ℤ) - P.g.nW ∧ G.nExt = P.g.nExt)
    (hExt : ∀ T ∈ Ts, BASim_Ext G k T) (hord : ∀ T ∈ Ts, ((G.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG)
    (hM : ∀ T ∈ Ts, (BAWeightOp_circ T).nM ≤ G.nM)
    (hAW : ∀ T ∈ Ts, ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW ≤ (G.nA : ℤ) - G.nW) :
    ∀ Q ∈ P.outsOf Ts, BALvl1B_Mono P Q := by
  intro Q hQ
  obtain ⟨T, hT, Δ, hΔ, rfl⟩ := BALvl1B_mem_outsOf P Ts hQ
  obtain ⟨hN, hbi, hW, hA, hMo, -, hX⟩ := BALvl1B_part_struct P G (hExt T hT) hG Δ hΔ
  obtain ⟨i1, i2, i3, i7⟩ := hinv
  simp only [BAPGraph.baInv, BASim_inv, Prod.mk.injEq] at hbi
  obtain ⟨b1, b2, b3, -, -, -, b7⟩ := hbi
  have hmem : Δ.packMerge ∈ T.partition := show Δ.packMerge ∈ T.splitG.map BAGraph.packMerge from List.mem_map_of_mem hΔ
  have hord' := ((BAGraph.le_scalingOrderG_iff T G.scalingOrder).1 (hord T hT)) _ hmem
  have hMT := hM T hT
  have hAT := hAW T hT
  refine ⟨BAGraph.partition_normal T _ hmem, ?_, ?_, ?_, ?_⟩
  · rw [← i1]
    exact hord'
  · rw [b2, ← i2]
    exact hMo.trans hMT
  · rw [b3, ← i3, ← i2] at *
    have : (Δ.nA : ℤ) ≤ (BAWeightOp_circ T).nA := by exact_mod_cast hA
    rw [hW]
    omega
  · rw [b7, ← i7]
    exact hX

/-- **`BALvl1B_outs_mono` for a family of terms** (`BASim_Fam`: the terms extend the graph and have `ord ≤ ordG`) -/
theorem BALvl1B_outs_fam (P : BAPGraph E0) {I0 : Type} [Fintype I0] [DecidableEq I0] (G : BAGraph P.E' I0) {k : ℕ}
    {F : BAGraph P.E' I0 → List (BAGraph P.E' (I0 ⊕ Fin k))} (hFam : BASim_Fam G k F) (Ts : List (BAGraph P.E' (I0 ⊕ Fin k))) (hTs : ∀ T ∈ Ts, T ∈ F G)
    (hG : G.Normal)
    (hinv : G.scalingOrder = P.g.scalingOrder ∧ G.nM = P.g.nM ∧ (G.nA : ℤ) - G.nW = (P.g.nA : ℤ) - P.g.nW ∧ G.nExt = P.g.nExt)
    (hM : ∀ T ∈ Ts, (BAWeightOp_circ T).nM ≤ G.nM)
    (hAW : ∀ T ∈ Ts, ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW ≤ (G.nA : ℤ) - G.nW) :
    ∀ Q ∈ P.outsOf Ts, BALvl1B_Mono P Q :=
  BALvl1B_outs_mono P G Ts hG hinv (fun T hT => hFam.hExt G T (hTs T hT)) (fun T hT => hFam.hmono G hG rfl T (hTs T hT)) hM hAW

/-! ### The cases `weight`, `edge`, `gg` of `BAstepMono` -/

/-- **`BAstepMono` at the weight step**: the terms of `lw2` and `lw4` (`lw_mono`, `BASim_fam_lw2`, `BASim_fam_lw4`) -/
theorem BALvl1B_weight (P : BAPGraph E0) (hN : P.g.Normal) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (h1 : p.1.σ = true) (h2 : p.1.circ = true) : ∀ Q ∈ P.outsOf (P.g.lw2 p) ++ P.outsOf (P.g.lw4 p), BALvl1B_Mono P Q := by
  intro Q hQ
  obtain ⟨m2, m4⟩ := lw_mono P.g p hp h1 h2
  rcases List.mem_append.1 hQ with hQ | hQ
  · exact BALvl1B_outs_fam P P.g (BASim_fam_lw2 P.g p hp h1 h2) (P.g.lw2 p) (fun T hT => hT) hN ⟨rfl, rfl, rfl, rfl⟩ (fun T hT => (m2 T hT).1.le)
      (fun T hT => (m2 T hT).2.1.le) Q hQ
  · exact BALvl1B_outs_fam P P.g (BASim_fam_lw4 P.g p hp h1 h2) (P.g.lw4 p) (fun T hT => hT) hN ⟨rfl, rfl, rfl, rfl⟩ (fun T hT => (m4 T hT).1.le)
      (fun T hT => (m4 T hT).2.1.le) Q hQ

/-- **`BAstepMono` at the edge step**: the terms of `lanlw` (`lanlwT1_counters`, `lanlwD_counters`, `BASim_fam_lanlw`) -/
theorem BALvl1B_edge (P : BAPGraph E0) (hN : P.g.Normal) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (h1 : p.1.σ = true) (h2 : p.1.circ = true) : ∀ Q ∈ P.outsOf (BAGraph.lanlwTerms P.g p), BALvl1B_Mono P Q :=
  BALvl1B_outs_fam P P.g (BASim_fam_lanlw P.g p hp h1 h2) (BAGraph.lanlwTerms P.g p) (fun T hT => hT) hN ⟨rfl, rfl, rfl, rfl⟩
    (fun T hT => (BALvl1B_lanlw_mono P.g p hp h1 h2 T hT).1) (fun T hT => (BALvl1B_lanlw_mono P.g p hp h1 h2 T hT).2)

/-- **`BAstepMono` at the `gg` step**: the terms of `gg2` and `gg4` (`gg_mono`, `BASim_fam_gg2`, `BASim_fam_gg4`) -/
theorem BALvl1B_gg (P : BAPGraph E0) (hN : P.g.Normal) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) : ∀ Q ∈ P.outsOf (P.g.gg2 p q) ++ P.outsOf (P.g.gg4 p q), BALvl1B_Mono P Q := by
  intro Q hQ
  obtain ⟨m2, m4⟩ := gg_mono P.g p q hp hq
  rcases List.mem_append.1 hQ with hQ | hQ
  · exact BALvl1B_outs_fam P P.g (BASim_fam_gg2 P.g p q hp hq) (P.g.gg2 p q) (fun T hT => hT) hN ⟨rfl, rfl, rfl, rfl⟩ (fun T hT => (m2 T hT).1)
      (fun T hT => (m2 T hT).2.1) Q hQ
  · exact BALvl1B_outs_fam P P.g (BASim_fam_gg4 P.g p q hp hq) (P.g.gg4 p q) (fun T hT => hT) hN ⟨rfl, rfl, rfl, rfl⟩ (fun T hT => (m4 T hT).1)
      (fun T hT => (m4 T hT).2.1) Q hQ

end Assembly

end RBM.Graph

end
