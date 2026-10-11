/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp

/-!
# BA-L L3b3' `BAScostS'`: the cost vocabulary at atoms, BA Lemma B, the initial values (T2426)

Property (6) of `lem:localregular` at the block Anderson model is one cost invariant on the atomic image of the BA graph
(`paper/tex/B_graphical_lemmas.tex:302-313`, cited `B:line`; design `docs/reports/T2397-design.md`, gate G2).  This file
writes the cost vocabulary at atoms (verbatim from `t/T2397:RBM3D/Probe/T2397Pins.lean:40-94, 123-136`, over R0's
`atomSetoid`, `promoteC`), the engine of the local lemma at atoms, **BA Lemma B** (`G = Ǧ + M`: merge-and-drop, the
circled edge by Lemma A; the `M`-splits that join two atoms joined by a kept edge are the extra outputs `E2`), `BAInit`,
and the reduction of `BAScostLL` to the band local lemma `LGraph.ScostLL` on the atomic image.  The five BA-only shape
lemmas and their packed forms are in `Graph/BAScost2.lean`.

## Contents (namespace `RBM.Graph`, private helpers carry the stem `BAScost_`)

1. The vocabulary: `scostA`, `locStdA`, `locCostGeA`, `locReg6InvA`, `BReach`, `BAInit`, `BAFinal`, `BAStep`, `BANormal`,
   `BAScostLL` with `BAScostLL.trans`, `BAShape`, `BTStep`, `untag`, `BAShapeLL`.
2. The cost engine (`BAScost_Up`: the solid list `l'` is `l` with edges circled and circled in-class edges added; such a list
   never costs less: Lemma A for a circled edge inside a class, `LGraph.scost_cons_loop_ge` `LocalRegular6a.lean:434`).
3. **BA Lemma B** (`BAScost_splitG_le`, `BAScostLL_splitG`): every term of `G = Ǧ + M` costs at least the graph.
4. The merge of the `=`-dotted classes is a relabelling: `BAScost_scostA_merge`; **`BAInit`** (`baInit_holds`).
5. The reduction to the band: `BAScostLL_of_band`.
6. The packed term lemma `baScost_locCostGeA_term` (the BA twin of `localReg6d_locCostGe_term`, `LocalRegular6d.lean:955`).
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

/-! ## 1. The cost vocabulary at atoms (verbatim from the T2397 probe) -/

section Vocab

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The cost of a merge at atoms** (`B:302-313`): the band cost `LGraph.scost` (`LocalRegular6a.lean:157`) of the atomic image
`promoteC Γ` at a merge `s` of the vertices that contains the atoms.  An edge is kept iff it is circled (inside an atom) or joins
two classes of `s`. -/
def scostA (Γ : BAGraph E I) (s : Setoid (E ⊕ I)) : ℤ := (promoteC Γ).scost s

/-- Vertex-level local standardness of a BA graph (`deflvl1`, `7_8:367-386`, read at the vertices as the paper writes it):
BA-normal, no weight, every internal vertex standard neutral or without solid edge. -/
def locStdA (Γ : BAGraph E I) : Prop :=
  Γ.Normal ∧ (∀ e ∈ Γ.solid, e.src ≠ e.dst) ∧
    ∀ i : I, Γ.toLGraph.StdNeutral (Sum.inr i) ∨ Γ.toLGraph.lvl1DegAt (Sum.inr i) = 0

end Vocab

/-- `PGraph.LocCostGe` (`LocalRegular6a.lean:177`) at BA: every merge of the vertices that contains the atoms (and, if `far`, keeps
the atoms of `x = P.ext 0` and `y = P.ext 1` apart) costs at least `k`. -/
def locCostGeA (far : Bool) (k : ℤ) (P : BAPGraph (Fin 2)) : Prop :=
  ∀ s : Setoid (P.E' ⊕ P.I'), atomSetoid P.g ≤ s →
    (far = true → ¬ s (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1))) → k ≤ scostA P.g s

/-- `PGraph.LocReg6Inv` (`LocalRegular6a.lean:182`) at BA. -/
def locReg6InvA (p : ℕ) (Q : BAPGraph (Fin 2)) : Prop :=
  Q.g.Normal ∧ locCostGeA false (2 * (p : ℤ)) Q ∧ locCostGeA true (3 * (p : ℤ)) Q

/-- Reachability along an abstract step relation (the BA twin of `Lvl1Reach`, `LWLvl1.lean:3277`; rows L3a). -/
inductive BReach (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) (P0 : BAPGraph (Fin 2)) :
    BAPGraph (Fin 2) → Prop
  | refl : BReach BStep P0 P0
  | step {Q R : BAPGraph (Fin 2)} {L : List (BAPGraph (Fin 2))} :
      BReach BStep P0 Q → BStep Q L → R ∈ L → BReach BStep P0 R

/-- **Pin L3b3, initial values** (`fxyPowGraph_locCostGe`, `LocalRegular6a.lean:927`, at BA): every BA term of `G = Ǧ + M` on the
starting graph `Γ_p` (`B:339-341`; `2^{2p}` terms, `baSplitSolid`) satisfies `Φ^all ≥ 2p` and, for atoms of `x`, `y` apart,
`Φ^far ≥ 3p`. -/
def BAInit (p : ℕ) : Prop :=
  ∀ P ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, locReg6InvA p P

/-- **Pin L3b3, final step** (`locReg6_of_locCostGe`, `locReg6far_of_locCostGe`, `LocalRegular6a.lean:645-653`, at BA): at a locally
standard BA graph the trivial merge (the atoms) costs `ord` (no elementary atom: every atom with a solid edge carries both
colours).  `R` restricts to the reachable graphs.  (Copied from the T2397 probe; row L3b4' restates it at `BAGraph.LocStd`,
supervisor `2026-10-11-0951` L4-C3.) -/
def BAFinal (R : BAPGraph (Fin 2) → Prop) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (k : ℤ), R P → locStdA P.g →
    (locCostGeA false k P → k ≤ P.scalingOrder) ∧
      (¬ atomSetoid P.g (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) → locCostGeA true k P → k ≤ P.scalingOrder)

/-- **Pin L3b4-L3b6, the step lemma** (`locCostGe_locStep`, `LocalRegular6d.lean:1077`, at BA): `Φ(Q) ≥ Φ(P)` for every output `Q`
of a BA step (`lanlw`, `lweight`, `GGGamma` followed by `G = Ǧ + M`), for `Φ^all` and `Φ^far`. -/
def BAStep (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), BStep P L → ∀ (far : Bool) (k : ℤ),
    locCostGeA far k P → ∀ Q ∈ L, locCostGeA far k Q

/-- The outputs of a BA step are BA-normal (`lvl1_step_good`, `LWLvl1.lean:3290`, first conjunct). -/
def BANormal (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop :=
  ∀ P L, BStep P L → ∀ Q ∈ L, Q.g.Normal

/-- **Pin L3b4-L3b5, the local lemma at BA** (`LGraph.ScostLL`, `LocalRegular6a.lean:168`): every merge `s` of a term `T`
(containing the atoms of `T`) is matched by a merge `s₀` of `Γ` (containing the atoms of `Γ`) that keeps apart every pair of
external vertices that `s` keeps apart, at no higher cost. -/
def BAScostLL {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (Γ : BAGraph E I) (T : BAGraph E I') : Prop :=
  ∀ s : Setoid (E ⊕ I'), atomSetoid T ≤ s → ∃ s₀ : Setoid (E ⊕ I), atomSetoid Γ ≤ s₀ ∧
    (∀ a b : E, ¬ s (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧ scostA Γ s₀ ≤ scostA T s

/-- The local lemma composes (`LGraph.ScostLL.trans`, `LocalRegular6b.lean:92`). -/
theorem BAScostLL.trans {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I']
    [DecidableEq I'] [Fintype I''] [DecidableEq I''] {Γ : BAGraph E I} {T : BAGraph E I'} {U : BAGraph E I''}
    (h1 : BAScostLL Γ T) (h2 : BAScostLL T U) : BAScostLL Γ U := by
  intro s hs
  obtain ⟨s₁, hs₁, hsep₁, hc₁⟩ := h2 s hs
  obtain ⟨s₀, hs₀, hsep₀, hc₀⟩ := h1 s₁ hs₁
  exact ⟨s₀, hs₀, fun a b h => hsep₀ a b (hsep₁ a b h), hc₀.trans hc₁⟩

/-- The output classes of a step of T2395's strategy `BALocStep` (lever S', `t/T2395` probe 207: K1-K4, at atoms): `band` =
matched, up to relabelling, with an output of a band `LocStep`; the BA-only shapes `s1` (first sum of `GGGamma`, `y`, `y'` in two
atoms), `e1` (`M_{αy}` of `lanlw` joining `[x]`, `[y]`), `e2` (an `M`-split joining two atoms joined by a parent solid edge),
`macroA`, `macroB` (the outputs of the macro steps K2(a), K2(b) that are not `band`; new lemma at their transfer intermediates).
(`deriving DecidableEq`: the case `sh = band` of `baStep_of_simC`.) -/
inductive BAShape | band | s1 | e1 | e2 | macroA | macroB
  deriving DecidableEq

/-- A step relation with tagged outputs; `untag` forgets the tags. -/
abbrev BTStep : Type 1 := BAPGraph (Fin 2) → List (BAShape × BAPGraph (Fin 2)) → Prop

def untag (T : BTStep) (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))) : Prop :=
  ∃ LT, T P LT ∧ L = LT.map Prod.snd

/-- **Pin L3b3' (S'): the `ScostLL` lemma of a BA-only shape**, in packed form (as `localReg6d_locCostGe_term`, 6d:955, packs
`LGraph.ScostLL`). -/
def BAShapeLL (sh : BAShape) (T : BTStep) : Prop :=
  ∀ P LT, T P LT → ∀ Q, (sh, Q) ∈ LT → ∀ far k, locCostGeA far k P → locCostGeA far k Q


/-! ## 2. The cost engine: circling edges and adding circled in-class edges never lowers the cost -/

section Engine

variable {V : Type}

/-- the edge with its circle set (the cost reads `σ`, `src`, `dst` of the kept edges only) -/
def BAScost_fe (e : SEdge V) : SEdge V := ⟨e.σ, true, e.src, e.dst⟩

theorem BAScost_halfPat_fe (es : List (SEdge V)) (K : V → Prop) [DecidablePred K] :
    lwHalfPat (es.map BAScost_fe) K = lwHalfPat es K := by
  simp only [lwHalfPat, List.countP_map]
  rfl

/-- the pattern of a list with one more edge that lies outside the class (both ends) is unchanged -/
theorem BAScost_halfPat_cons_out (e : SEdge V) (es : List (SEdge V)) (K : V → Prop) [DecidablePred K]
    (hK : ¬ K e.src) (h2 : ¬ K e.dst) : lwHalfPat (e :: es) K = lwHalfPat es K := by
  simp [lwHalfPat, hK, h2]

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the cost reads the kept edges up to order and circles, and the number of waved edges -/
theorem BAScost_scost_congr (Λ Λ' : LGraph E I) (s : Setoid (E ⊕ I))
    (h : ((Λ.skept s).map BAScost_fe).Perm ((Λ'.skept s).map BAScost_fe))
    (hW : Λ.waved.length = Λ'.waved.length) : Λ.scost s = Λ'.scost s := by
  classical
  have hp : ∀ (K : E ⊕ I → Prop) [DecidablePred K], lwHalfPat (Λ.skept s) K = lwHalfPat (Λ'.skept s) K := by
    intro K _
    rw [← BAScost_halfPat_fe (Λ.skept s), ← BAScost_halfPat_fe (Λ'.skept s)]
    exact localReg6a_halfPat_perm h K
  have hE : Λ.sElemCls s = Λ'.sElemCls s := by
    ext c
    rw [localReg6a_mem_sElemCls, localReg6a_mem_sElemCls]
    refine exists_congr fun v => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [hp]
  have hl : (Λ.skept s).length = (Λ'.skept s).length := by
    simpa using h.length_eq
  unfold LGraph.scost
  rw [hl, hW, hE]
  rfl

open Classical in
/-- **Lemma A for a circled edge inside a class** (`LGraph.scost_cons_loop_ge`, `LocalRegular6a.lean:434`, whose proof reads only
that the two ends of the added edge lie in one class): adding a circled edge whose ends are merged never lowers the cost. -/
theorem BAScost_cons_inclass_ge (Γ : LGraph E I) (e : SEdge (E ⊕ I)) (hc : e.circ = true) (s : Setoid (E ⊕ I))
    (he : s e.src e.dst) :
    Γ.scost s ≤ ({ Γ with solid := e :: Γ.solid } : LGraph E I).scost s := by
  set Γ' : LGraph E I := { Γ with solid := e :: Γ.solid } with hΓ'
  have hk : Γ'.skept s = e :: Γ.skept s := by
    simp [LGraph.skept, hΓ', hc]
  have hsub : (Γ.sElemCls s).erase (Quotient.mk s e.src) ⊆ Γ'.sElemCls s := by
    intro c hc'
    rw [Finset.mem_erase] at hc'
    obtain ⟨hne, hc'⟩ := hc'
    obtain ⟨v, hv, hel, rfl⟩ := (localReg6a_mem_sElemCls Γ s c).1 hc'
    refine (localReg6a_mem_sElemCls Γ' s _).2 ⟨v, hv, ?_, rfl⟩
    have h1 : ¬ s e.src v := fun h => hne (Quotient.sound (s.symm h))
    have h2 : ¬ s e.dst v := fun h => h1 (s.trans he h)
    rw [hk, BAScost_halfPat_cons_out e _ (fun w => s w v) h1 h2]
    exact hel
  have hcard := Finset.pred_card_le_card_erase (s := Γ.sElemCls s) (a := Quotient.mk s e.src)
  have h2 := Finset.card_le_card hsub
  have hI : Γ'.sIntCls s = Γ.sIntCls s := rfl
  unfold LGraph.scost
  rw [hk, hI]
  have hW : Γ'.waved.length = Γ.waved.length := rfl
  rw [hW]
  simp only [List.length_cons]
  push_cast
  omega

/-- circled in-class edges added to the kept list never lower the cost -/
theorem BAScost_scost_le_extra (Λ Λ' : LGraph E I) (s : Setoid (E ⊕ I)) (Y : List (SEdge (E ⊕ I)))
    (hY : ∀ y ∈ Y, y.circ = true ∧ s y.src y.dst)
    (h : ((Λ'.skept s).map BAScost_fe).Perm ((Λ.skept s).map BAScost_fe ++ Y.map BAScost_fe))
    (hW : Λ.waved.length = Λ'.waved.length) : Λ.scost s ≤ Λ'.scost s := by
  classical
  have key : ∀ Y : List (SEdge (E ⊕ I)), (∀ y ∈ Y, y.circ = true ∧ s y.src y.dst) →
      Λ.scost s ≤ ({ Λ with solid := Y ++ Λ.solid } : LGraph E I).scost s := by
    intro Y
    induction Y with
    | nil => intro _; exact le_rfl
    | cons y Y ih =>
      intro hY
      refine (ih (fun z hz => hY z (List.mem_cons_of_mem _ hz))).trans ?_
      exact BAScost_cons_inclass_ge ({ Λ with solid := Y ++ Λ.solid } : LGraph E I) y (hY y List.mem_cons_self).1 s
        (hY y List.mem_cons_self).2
  refine (key Y hY).trans (le_of_eq ?_)
  refine BAScost_scost_congr _ _ s ?_ (by simpa using hW)
  have hk : (({ Λ with solid := Y ++ Λ.solid } : LGraph E I).skept s) = Y ++ Λ.skept s := by
    simp only [LGraph.skept, List.filter_append]
    congr 1
    rw [List.filter_eq_self]
    intro y hy
    simp [(hY y hy).1]
  rw [hk, List.map_append]
  exact List.perm_append_comm.trans h.symm


/-! ### The relation `Up` between solid lists -/

section Up

variable {V : Type}

theorem BAScost_kept_cons_of (s : Setoid V) (e : SEdge V) (l : List (SEdge V)) (h : e.circ = true ∨ ¬ s e.src e.dst) :
    scostLL_kept (e :: l) s = e :: scostLL_kept l s := by
  classical
  simp only [scostLL_kept, List.filter_cons]
  rcases h with h | h <;> simp [h]

theorem BAScost_kept_cons_not (s : Setoid V) (e : SEdge V) (l : List (SEdge V)) (h : ¬ (e.circ = true ∨ ¬ s e.src e.dst)) :
    scostLL_kept (e :: l) s = scostLL_kept l s := by
  classical
  simp only [scostLL_kept, List.filter_cons]
  push Not at h
  simp [h.1, h.2]

/-- **`l'` is `l` at the merge `s`, with edges circled and circled edges inside classes added**: the kept edges of `l'` are those of
`l` (read up to the circle) and circled edges `Y` whose ends lie in one class. -/
def BAScost_Up (s : Setoid V) (l l' : List (SEdge V)) : Prop :=
  ∃ Y : List (SEdge V), (∀ y ∈ Y, y.circ = true ∧ s y.src y.dst) ∧
    ((scostLL_kept l' s).map BAScost_fe).Perm ((scostLL_kept l s).map BAScost_fe ++ Y.map BAScost_fe)

theorem BAScost_Up.refl (s : Setoid V) (l : List (SEdge V)) : BAScost_Up s l l := ⟨[], by simp, by simp⟩

/-- the same edge, circled if it was: the head of a list -/
theorem BAScost_Up.cons (s : Setoid V) {l l' : List (SEdge V)} (e e' : SEdge V) (h : BAScost_Up s l l')
    (hσ : e'.σ = e.σ) (hsrc : e'.src = e.src) (hdst : e'.dst = e.dst) (hc : e.circ = true → e'.circ = true) :
    BAScost_Up s (e :: l) (e' :: l') := by
  obtain ⟨Y, hY, hp⟩ := h
  have hfe : BAScost_fe e' = BAScost_fe e := by simp [BAScost_fe, hσ, hsrc, hdst]
  have hs' : s e'.src e'.dst ↔ s e.src e.dst := by rw [hsrc, hdst]
  by_cases h1 : e.circ = true ∨ ¬ s e.src e.dst <;> by_cases h2 : e'.circ = true ∨ ¬ s e'.src e'.dst
  · refine ⟨Y, hY, ?_⟩
    rw [BAScost_kept_cons_of s e l h1, BAScost_kept_cons_of s e' l' h2]
    simp only [List.map_cons, hfe]
    exact hp.cons _
  · exfalso
    apply h2
    rcases h1 with h1 | h1
    · exact Or.inl (hc h1)
    · exact Or.inr (fun h => h1 (hs'.1 h))
  · have h1' := h1
    push Not at h1'
    have hse : s e.src e.dst := h1'.2
    have hc' : e'.circ = true := by
      rcases h2 with h | h
      · exact h
      · exact absurd (hs'.2 hse) h
    refine ⟨e' :: Y, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨hc', hs'.2 hse⟩
      · exact hY y hy
    · rw [BAScost_kept_cons_not s e l h1, BAScost_kept_cons_of s e' l' h2]
      simp only [List.map_cons, hfe]
      exact (hp.cons _).trans List.perm_middle.symm
  · refine ⟨Y, hY, ?_⟩
    rw [BAScost_kept_cons_not s e l h1, BAScost_kept_cons_not s e' l' h2]
    exact hp


/-- an uncircled edge inside a class is not kept: it can be dropped -/
theorem BAScost_Up.drop (s : Setoid V) {l l' : List (SEdge V)} (e : SEdge V) (h : BAScost_Up s l l')
    (hc : e.circ = false) (hs : s e.src e.dst) : BAScost_Up s (e :: l) l' := by
  obtain ⟨Y, hY, hp⟩ := h
  refine ⟨Y, hY, ?_⟩
  rw [BAScost_kept_cons_not s e l (by simp [hc, hs])]
  exact hp

theorem BAScost_Up.append (s : Setoid V) {l₁ l₁' l₂ l₂' : List (SEdge V)} (h₁ : BAScost_Up s l₁ l₁')
    (h₂ : BAScost_Up s l₂ l₂') : BAScost_Up s (l₁ ++ l₂) (l₁' ++ l₂') := by
  obtain ⟨Y₁, hY₁, hp₁⟩ := h₁
  obtain ⟨Y₂, hY₂, hp₂⟩ := h₂
  refine ⟨Y₁ ++ Y₂, ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.1 hy with h | h
    exacts [hY₁ y h, hY₂ y h]
  · rw [scostLL_kept_append, scostLL_kept_append]
    simp only [List.map_append]
    refine (hp₁.append hp₂).trans ?_
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

theorem BAScost_Up.perm_left (s : Setoid V) {l₀ l l' : List (SEdge V)} (hp : l₀.Perm l) (h : BAScost_Up s l l') :
    BAScost_Up s l₀ l' := by
  obtain ⟨Y, hY, hq⟩ := h
  exact ⟨Y, hY, hq.trans (((scostLL_kept_perm hp s).map BAScost_fe).symm.append_right _)⟩

theorem BAScost_Up.perm_right (s : Setoid V) {l l' l'' : List (SEdge V)} (hp : l'.Perm l'') (h : BAScost_Up s l l') :
    BAScost_Up s l l'' := by
  obtain ⟨Y, hY, hq⟩ := h
  exact ⟨Y, hY, (((scostLL_kept_perm hp s).map BAScost_fe).symm).trans hq⟩

/-- two lists of edges indexed by the same list, the second with larger circles -/
theorem BAScost_Up_map {W : Type} (s : Setoid V) (rest : List W) (f f' : W → SEdge V)
    (h : ∀ e ∈ rest, (f' e).σ = (f e).σ ∧ (f' e).src = (f e).src ∧ (f' e).dst = (f e).dst ∧
      ((f e).circ = true → (f' e).circ = true)) :
    BAScost_Up s (rest.map f) (rest.map f') := by
  induction rest with
  | nil => exact BAScost_Up.refl s []
  | cons e rest ih =>
    obtain ⟨h1, h2, h3, h4⟩ := h e List.mem_cons_self
    exact BAScost_Up.cons s (f e) (f' e) (ih fun e he => h e (List.mem_cons_of_mem _ he)) h1 h2 h3 h4

end Up

section UpCost

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The cost comparison of two graphs on one vertex type**: if the solid list of `Λ'` is that of `Λ` with edges circled and circled
in-class edges added at the merge `s`, and the numbers of waved edges agree, then `Λ'` costs at least `Λ` at `s`. -/
theorem BAScost_scost_le_of_Up (Λ Λ' : LGraph E I) (s : Setoid (E ⊕ I)) (h : BAScost_Up s Λ.solid Λ'.solid)
    (hW : Λ.waved.length = Λ'.waved.length) : Λ.scost s ≤ Λ'.scost s := by
  obtain ⟨Y, hY, hp⟩ := h
  exact BAScost_scost_le_extra Λ Λ' s Y hY hp hW

end UpCost

end Engine


/-! ## 3. BA Lemma B: the terms of `G = Ǧ + M` -/

section LemmaB

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- an `M`-dotted edge joins two vertices of one atom -/
theorem BAScost_atomSetoid_of_mdot (Γ : BAGraph E I) (m : BAMEdge (E ⊕ I)) (hm : m ∈ Γ.mdot) :
    atomSetoid Γ m.x m.y := by
  rw [BAAtomic_atomSetoid_iff, Γ.mem_atom_iff]
  refine Relation.ReflTransGen.single ?_
  simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨m, hm, Or.inl ⟨rfl, rfl⟩⟩

/-- the term of `G = Ǧ + M` with the split `r` of the solid edges -/
theorem BAScost_atomSetoid_le_split (T : BAGraph E I) (r : List (SEdge (E ⊕ I)) × List (BAMEdge (E ⊕ I))) :
    atomSetoid T ≤ atomSetoid (BAGraph.mk (LGraph.mk r.1 T.waved T.dotted T.coeff) T.psi (r.2 ++ T.mdot) : BAGraph E I) := by
  intro u v h
  rw [BAAtomic_atomSetoid_iff] at h ⊢
  rw [BAGraph.mem_atom_iff] at h ⊢
  refine Relation.ReflTransGen.mono (fun a b hab => ?_) u v h
  simp only [BAGraph.atomAdj, List.any_append, Bool.or_eq_true] at hab ⊢
  tauto


/-- **The split of the solid edges** (`baSplitSolid`, `B:339-340`): the circled copies and the dropped edges of a term of
`G = Ǧ + M`, read through any edge maps `fT`, `fQ` that circle at least as much for `Q` as for `T`. -/
theorem BAScost_split_Up {V : Type} (s : Setoid V) (fT fQ : SEdge V → SEdge V)
    (hT : ∀ e, (fT e).σ = e.σ ∧ (fT e).src = e.src ∧ (fT e).dst = e.dst)
    (hQ : ∀ e, (fQ e).σ = e.σ ∧ (fQ e).src = e.src ∧ (fQ e).dst = e.dst)
    (hTc : ∀ e, e.circ = false → (fT e).circ = false)
    (hmono : ∀ e, (fT e).circ = true → (fQ e).circ = true) :
    ∀ (es : List (SEdge V)) (r : List (SEdge V) × List (BAMEdge V)), r ∈ baSplitSolid es →
      (∀ m ∈ r.2, s m.x m.y) → BAScost_Up s (es.map fT) (r.1.map fQ) := by
  intro es
  induction es with
  | nil =>
    intro r hr _
    simp only [baSplitSolid, List.mem_singleton] at hr
    subst hr
    exact BAScost_Up.refl s []
  | cons e es ih =>
    intro r hr hm
    simp only [baSplitSolid, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    by_cases hc : e.circ = true
    · simp only [hc, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      exact BAScost_Up.cons s (fT e) (fQ e) (ih r' hr' hm) (by rw [(hQ e).1, (hT e).1]) (by rw [(hQ e).2.1, (hT e).2.1])
        (by rw [(hQ e).2.2, (hT e).2.2]) (hmono e)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hcf : e.circ = false := by simpa using hc
      rcases hr with rfl | rfl
      · refine BAScost_Up.cons s (fT e) (fQ ⟨e.σ, true, e.src, e.dst⟩) (ih r' hr' hm)
          (by rw [(hQ _).1, (hT e).1]) (by rw [(hQ _).2.1, (hT e).2.1]) (by rw [(hQ _).2.2, (hT e).2.2])
          (fun h => by rw [hTc e hcf] at h; exact absurd h (by simp))
      · refine BAScost_Up.drop s (fT e) (ih r' hr' (fun m hm' => hm m (List.mem_cons_of_mem _ hm'))) (hTc e hcf) ?_
        rw [(hT e).2.1, (hT e).2.2]
        exact hm ⟨e.σ, e.src, e.dst⟩ List.mem_cons_self

/-- **BA Lemma B, pointwise** (`B:339-341`; the band: `LGraph.scost_partition_ge`, `LocalRegular6a.lean:503`): every term `Q` of
`G = Ǧ + M` on `T` costs at least `T` at every merge `s` that contains the atoms of `Q`.  A split joins two atoms of `T`, and
if the two are joined by a kept edge of `T` the edge becomes a circled edge inside a class (the outputs `E2`): Lemma A. -/
theorem BAScost_splitG_le (T : BAGraph E I) {Q : BAGraph E I} (hQ : Q ∈ T.splitG) (s : Setoid (E ⊕ I))
    (hs : atomSetoid Q ≤ s) : scostA T s ≤ scostA Q s := by
  simp only [BAGraph.splitG, List.mem_map] at hQ
  obtain ⟨r, hr, rfl⟩ := hQ
  set Q : BAGraph E I := BAGraph.mk (LGraph.mk r.1 T.waved T.dotted T.coeff) T.psi (r.2 ++ T.mdot) with hQdef
  have hle : atomSetoid T ≤ atomSetoid Q := BAScost_atomSetoid_le_split T r
  have hm : ∀ m ∈ r.2, s m.x m.y := fun m hm =>
    hs (BAScost_atomSetoid_of_mdot Q m (by simp [hQdef, hm]))
  unfold scostA
  refine BAScost_scost_le_of_Up (promoteC T) (promoteC Q) s ?_ rfl
  rw [BAAtomic_promoteC_solid, BAAtomic_promoteC_solid]
  refine BAScost_split_Up s (fun e => ⟨e.σ, e.circ && T.sameAtom e.src e.dst, e.src, e.dst⟩)
    (fun e => ⟨e.σ, e.circ && Q.sameAtom e.src e.dst, e.src, e.dst⟩) (fun e => ⟨rfl, rfl, rfl⟩) (fun e => ⟨rfl, rfl, rfl⟩)
    (fun e he => by simp [he]) (fun e he => ?_) T.solid r hr hm
  simp only [Bool.and_eq_true] at he ⊢
  refine ⟨he.1, ?_⟩
  rw [T.BAAtomic_sameAtom_iff] at he
  rw [Q.BAAtomic_sameAtom_iff]
  exact (BAAtomic_atomSetoid_iff Q _ _).1 (hle ((BAAtomic_atomSetoid_iff T _ _).2 he.2))

/-- **BA Lemma B** (`G = Ǧ + M`, `B:339-341`; includes the extra outputs `E2`: an `M`-split joining two atoms joined by a kept edge):
`BAScostLL T Q` for every term `Q` of the expansion, with `s₀ = s`. -/
theorem BAScostLL_splitG (T : BAGraph E I) {Q : BAGraph E I} (hQ : Q ∈ T.splitG) : BAScostLL T Q := by
  intro s hs
  have hle : atomSetoid T ≤ atomSetoid Q := by
    simp only [BAGraph.splitG, List.mem_map] at hQ
    obtain ⟨r, hr, rfl⟩ := hQ
    exact BAScost_atomSetoid_le_split T r
  exact ⟨s, hle.trans hs, fun _ _ h => h, BAScost_splitG_le T hQ s hs⟩

end LemmaB


/-! ## 4. The merge of the `=`-dotted classes is a relabelling; the initial values -/

section Merge

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the vertex map of the merge of the `=`-dotted classes sends the atoms of `Q` into the atoms of the merged graph -/
theorem BAScost_atomSetoid_merge (Q : BAGraph E I) {u v : E ⊕ I} (h : atomSetoid Q u v) :
    atomSetoid Q.merge (Q.toLGraph.vmap u) (Q.toLGraph.vmap v) := by
  rw [BAAtomic_atomSetoid_iff] at h ⊢
  rw [BAGraph.mem_atom_iff] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine ih.trans ?_
    simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hbc
    rcases hbc with (⟨e, he, he1, he2⟩ | ⟨e, he, he2⟩) | ⟨e, he, he2⟩
    · have hrel : Q.toLGraph.EqRel b c := by
        rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨e, he, he1, Or.inl ⟨h1, h2⟩⟩
        · exact ⟨e, he, he1, Or.inr ⟨h1, h2⟩⟩
      have hv : Q.toLGraph.vmap b = Q.toLGraph.vmap c :=
        congrArg Q.toLGraph.vmapC (Quotient.sound (Relation.EqvGen.rel _ _ hrel))
      rw [hv]
    · refine Relation.ReflTransGen.single ?_
      simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      refine Or.inl (Or.inr ⟨BAPsiEdge.map Q.toLGraph.vmap e, List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩)
      rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simp [BAPsiEdge.map, h1], by simp [BAPsiEdge.map, h2]⟩
      · exact Or.inr ⟨by simp [BAPsiEdge.map, h1], by simp [BAPsiEdge.map, h2]⟩
    · refine Relation.ReflTransGen.single ?_
      simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      refine Or.inr ⟨BAMEdge.map Q.toLGraph.vmap e, List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩
      rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simp [BAMEdge.map, h1], by simp [BAMEdge.map, h2]⟩
      · exact Or.inr ⟨by simp [BAMEdge.map, h1], by simp [BAMEdge.map, h2]⟩

/-- **The merge of the `=`-dotted classes never costs less than the graph at the pulled-back merge** (`B:340`): the relabelled atomic
image has the same edges as the atomic image of the merged graph, with circles at least as large. -/
theorem BAScost_scostA_le_merge (Q : BAGraph E I) (s : Setoid (Q.toLGraph.ExtCls ⊕ Q.toLGraph.IntCls)) :
    scostA Q (Setoid.comap Q.toLGraph.vmap s) ≤ scostA Q.merge s := by
  unfold scostA
  rw [← LGraph.scost_relabel (promoteC Q) Q.toLGraph.extMap Q.toLGraph.extMap_surj Q.toLGraph.vmap
    (BAAtomic_vmap_surjective Q.toLGraph) (BAAtomic_vmap_inl Q.toLGraph) s]
  refine BAScost_scost_le_of_Up _ _ s ?_ (by simp [LGraph.relabel, promoteC, BAGraph.merge, LGraph.merge])
  have h1 : ((promoteC Q).relabel Q.toLGraph.vmap).solid = Q.solid.map (fun e =>
      (⟨e.σ, e.circ && Q.sameAtom e.src e.dst, Q.toLGraph.vmap e.src, Q.toLGraph.vmap e.dst⟩ :
        SEdge (Q.toLGraph.ExtCls ⊕ Q.toLGraph.IntCls))) := by
    simp only [LGraph.relabel, BAAtomic_promoteC_solid, List.map_map]
    rfl
  have h2 : (promoteC Q.merge).solid = Q.solid.map (fun e =>
      (⟨e.σ, e.circ && Q.merge.sameAtom (Q.toLGraph.vmap e.src) (Q.toLGraph.vmap e.dst), Q.toLGraph.vmap e.src,
        Q.toLGraph.vmap e.dst⟩ : SEdge (Q.toLGraph.ExtCls ⊕ Q.toLGraph.IntCls))) := by
    rw [BAAtomic_promoteC_solid]
    simp only [BAGraph.merge, LGraph.merge, List.map_map]
    rfl
  rw [h1, h2]
  refine BAScost_Up_map s Q.solid _ _ (fun e he => ⟨rfl, rfl, rfl, fun h => ?_⟩)
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [Q.BAAtomic_sameAtom_iff, ← BAAtomic_atomSetoid_iff] at h
  rw [Q.merge.BAAtomic_sameAtom_iff, ← BAAtomic_atomSetoid_iff]
  exact BAScost_atomSetoid_merge Q h.2

/-- the band cost of a graph with `CircIffLoop` is at most the cost of its atomic image as a BA graph without dotted edges -/
theorem BAScost_scost_le_scostA_ofLGraph (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (s : Setoid (E ⊕ I)) :
    Γ.scost s ≤ scostA (BAGraph.ofLGraph Γ) s := by
  unfold scostA
  refine BAScost_scost_le_of_Up Γ _ s ?_ rfl
  have key := BAScost_Up_map s Γ.solid (fun e => e)
    (fun e => (⟨e.σ, e.circ && (BAGraph.ofLGraph Γ).sameAtom e.src e.dst, e.src, e.dst⟩ : SEdge (E ⊕ I)))
    (fun e he => ⟨rfl, rfl, rfl, fun h => ?_⟩)
  · rw [List.map_id'] at key
    show BAScost_Up s Γ.solid (promoteC (BAGraph.ofLGraph Γ)).solid
    rw [BAAtomic_promoteC_solid]
    exact key
  · have hl : e.src = e.dst := (hC e he).2 h
    have h' : e.circ = true := h
    show (e.circ && (BAGraph.ofLGraph Γ).sameAtom e.src e.dst) = true
    rw [h', Bool.true_and, (BAGraph.ofLGraph Γ).BAAtomic_sameAtom_iff, ← BAAtomic_atomSetoid_iff, hl]

/-- **`BAInit`, the initial values** (`fxyPowGraph_locCostGe`, `LocalRegular6a.lean:927`, at BA): every BA term of `G = Ǧ + M` on
the starting graph `Γ_p` satisfies the invariant of (6): Lemma B (`BAScost_splitG_le`), the merge of the `=`-dotted classes
(`BAScost_scostA_le_merge`), and the band bound. -/
theorem baInit_holds (p : ℕ) : BAInit p := by
  intro P hP
  have hN := BAGraph.partition_normal _ P hP
  simp only [BAGraph.partition, List.mem_map] at hP
  obtain ⟨Q, hQ, rfl⟩ := hP
  have key : ∀ s : Setoid (Q.toLGraph.ExtCls ⊕ Q.toLGraph.IntCls), atomSetoid Q.merge ≤ s →
      (fxyPowGraph p).scost (Setoid.comap Q.toLGraph.vmap s) ≤ scostA Q.merge s := by
    intro s hs
    have hatom : atomSetoid Q ≤ Setoid.comap Q.toLGraph.vmap s := fun u v h => hs (BAScost_atomSetoid_merge Q h)
    exact (BAScost_scost_le_scostA_ofLGraph _ (localReg6a_fxy_circIffLoop p) _).trans
      ((BAScost_splitG_le _ hQ _ hatom).trans (BAScost_scostA_le_merge Q s))
  refine ⟨hN, fun s hs _ => ?_, fun s hs hfar => ?_⟩
  · exact ((fxyPowGraph_locCostGe p).1 _ (fun h => by cases h)).trans (key s hs)
  · have hf : ¬ Setoid.comap Q.toLGraph.vmap s (Sum.inl 0) (Sum.inl 1) := by
      intro h
      apply hfar rfl
      have h' : s (Q.toLGraph.vmap (Sum.inl 0)) (Q.toLGraph.vmap (Sum.inl 1)) := h
      rw [BAAtomic_vmap_inl, BAAtomic_vmap_inl] at h'
      exact h'
    exact ((fxyPowGraph_locCostGe p).2 _ (fun _ => hf)).trans (key s hs)

end Merge

end RBM.Graph
