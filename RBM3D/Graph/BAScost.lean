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
# The cost vocabulary at atoms, BA Lemma B, `BAInit`, five shapes

Property (6) of Lemma 7.17 (`lem:localregular`) at the block Anderson model is one cost invariant
on the atomic image of the BA graph (Definition B.3 `def_atom`).  This file writes the cost
vocabulary at atoms (over `atomSetoid`, `promoteC`), the engine of the local lemma at atoms,
**BA Lemma B** (`G = Ǧ + M`, Definition B.4 `defn_normalBA`: merge-and-drop, the circled edge by
Lemma A; the `M`-splits that join two atoms joined by a kept edge are the extra outputs `E2`),
`BAInit`, the reduction of `BAScostLL` to the band local lemma `LGraph.ScostLL` on the atomic
image, and the five BA-only shape lemmas `BAScostLL Γ T`.  The packed forms `BAShapeLL sh T` are in
`Graph/BAScost2.lean`.

## Contents (namespace `RBM.Graph`, private helpers carry the stem `BAScost_`)

1. The vocabulary: `scostA`, `locCostGeA`, `locReg6InvA`, `BReach`, `BAInit`,
   `BAStep`, `BANormal`, `BAScostLL` with `BAScostLL.trans`, `BAShape`, `BTStep`, `untag`,
   `BAShapeLL`.
2. The cost engine: `BAScost_Up` (the solid list `l'` is `l` with edges circled and circled edges
   inside classes added) never costs less (Lemma A for a circled edge inside a class, the loop
   hypothesis of `LGraph.scost_cons_loop_ge`, `Graph/LocalRegular6a.lean`, replaced by "the ends
   lie in one class").
3. **BA Lemma B** (`BAScost_splitG_le`, `BAScostLL_splitG`; the extra outputs `E2` are included in
   `BAScostLL_splitG`).
4. The merge of the `=`-dotted classes is a relabelling; **`BAInit`** (`baInit_holds`).
5. The reduction to the band (`BAScostLL_of_band`: the band local lemmas apply on the atom quotient
   `(promoteC Γ).merge`, where every setoid pulls back to a merge that contains the atoms) and the
   packed term lemma `BAScost_locCostGeA_term` (the BA counterpart of `localReg6d_locCostGe_term`,
   `Graph/LocalRegular6d.lean`).
6. The shapes: **S1** (`BAScostLL_S1`, `scostLL_contract`), **E1** and the raw first term of `lanlw`
   (`BAScostLL_lanlwT1`; `scostLL_loop`, `scostLL_moveLoop`), **macroA**
   (`BAScostLL_macroA`; `scostLL_moveLoop`, `scostLL_loop`), **macroB** (`BAScostLL_macroB`;
   `scostLL_moveSC`), **E2** (the extra outputs of `BAScostLL_splitG`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false

noncomputable section

namespace RBM.Graph

/-! ## 1. The cost vocabulary at atoms -/

section Vocab

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The cost of a merge at atoms** (Definition B.3 `def_atom`): the band cost `LGraph.scost` (`Graph/LocalRegular6a.lean`) of the atomic image
`promoteC Γ` at a merge `s` of the vertices that contains the atoms.  An edge is kept iff it is circled (inside an atom) or joins
two classes of `s`. -/
def scostA (Γ : BAGraph E I) (s : Setoid (E ⊕ I)) : ℤ := (promoteC Γ).scost s

end Vocab

/-- `PGraph.LocCostGe` (`Graph/LocalRegular6a.lean`) at BA: every merge of the vertices that contains the atoms (and, if `far`, keeps
the atoms of `x = P.ext 0` and `y = P.ext 1` apart) costs at least `k`. -/
def locCostGeA (far : Bool) (k : ℤ) (P : BAPGraph (Fin 2)) : Prop :=
  ∀ s : Setoid (P.E' ⊕ P.I'), atomSetoid P.g ≤ s →
    (far = true → ¬ s (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1))) → k ≤ scostA P.g s

/-- `PGraph.LocReg6Inv` (`Graph/LocalRegular6a.lean`) at BA. -/
def locReg6InvA (p : ℕ) (Q : BAPGraph (Fin 2)) : Prop :=
  Q.g.Normal ∧ locCostGeA false (2 * (p : ℤ)) Q ∧ locCostGeA true (3 * (p : ℤ)) Q

/-- Reachability along an abstract step relation (the BA counterpart of `Lvl1Reach` in `Graph/LWLvl1.lean`): `BReach.refl` and
`BReach.step` are the two constructors of an inductive predicate, and `BReach.ind` its induction principle (`induction hQ with
| refl | step hQ' hst hmem ih`).  A definition by `Relation.ReflTransGen`, not an inductive predicate. -/
def BReach (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) (P0 : BAPGraph (Fin 2)) :
    BAPGraph (Fin 2) → Prop :=
  Relation.ReflTransGen (fun Q R => ∃ L, BStep Q L ∧ R ∈ L) P0

theorem BReach.refl {BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop} {P0 : BAPGraph (Fin 2)} :
    BReach BStep P0 P0 := Relation.ReflTransGen.refl

theorem BReach.step {BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop} {P0 Q R : BAPGraph (Fin 2)}
    {L : List (BAPGraph (Fin 2))} (h : BReach BStep P0 Q) (hs : BStep Q L) (hm : R ∈ L) : BReach BStep P0 R :=
  Relation.ReflTransGen.tail h ⟨L, hs, hm⟩

/-- the induction principle of `BReach` -/
@[elab_as_elim, induction_eliminator]
theorem BReach.ind {BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop} {P0 : BAPGraph (Fin 2)}
    {motive : ∀ Q, BReach BStep P0 Q → Prop} (refl : motive P0 BReach.refl)
    (step : ∀ {Q R L} (h : BReach BStep P0 Q) (hs : BStep Q L) (hm : R ∈ L), motive Q h → motive R (BReach.step h hs hm))
    {Q : BAPGraph (Fin 2)} (h : BReach BStep P0 Q) : motive Q h := by
  have h' : Relation.ReflTransGen (fun Q R => ∃ L, BStep Q L ∧ R ∈ L) P0 Q := h
  induction h' with
  | refl => exact refl
  | tail hPQ hQR ih =>
    obtain ⟨L, hs, hm⟩ := hQR
    exact step hPQ hs hm (ih hPQ)

/-- **Initial values** (`fxyPowGraph_locCostGe` in `Graph/LocalRegular6a.lean`, at BA): every BA term of `G = Ǧ + M` on the
starting graph `Γ_p` (Definition B.4; `2^{2p}` terms, `baSplitSolid`) satisfies `Φ^all ≥ 2p` and, for atoms of `x`, `y` apart,
`Φ^far ≥ 3p`. -/
def BAInit (p : ℕ) : Prop :=
  ∀ P ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, locReg6InvA p P

/-- **The step lemma** (`locCostGe_locStep` in `Graph/LocalRegular6d.lean`, at BA): `Φ(Q) ≥ Φ(P)` for every output `Q`
of a BA step (`lanlw`, `lweight`, `GGGamma` followed by `G = Ǧ + M`), for `Φ^all` and `Φ^far`. -/
def BAStep (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), BStep P L → ∀ (far : Bool) (k : ℤ),
    locCostGeA far k P → ∀ Q ∈ L, locCostGeA far k Q

/-- The outputs of a BA step are BA-normal (`lvl1_step_good` in `Graph/LWLvl1.lean`, first conjunct). -/
def BANormal (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop :=
  ∀ P L, BStep P L → ∀ Q ∈ L, Q.g.Normal

/-- **The local lemma at BA** (`LGraph.ScostLL` in `Graph/LocalRegular6a.lean`): every merge `s` of a term `T`
(containing the atoms of `T`) is matched by a merge `s₀` of `Γ` (containing the atoms of `Γ`) that keeps apart every pair of
external vertices that `s` keeps apart, at no higher cost. -/
def BAScostLL {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (Γ : BAGraph E I) (T : BAGraph E I') : Prop :=
  ∀ s : Setoid (E ⊕ I'), atomSetoid T ≤ s → ∃ s₀ : Setoid (E ⊕ I), atomSetoid Γ ≤ s₀ ∧
    (∀ a b : E, ¬ s (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧ scostA Γ s₀ ≤ scostA T s

/-- The local lemma composes (`LGraph.ScostLL.trans` in `Graph/LocalRegular6b.lean`). -/
theorem BAScostLL.trans {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I']
    [DecidableEq I'] [Fintype I''] [DecidableEq I''] {Γ : BAGraph E I} {T : BAGraph E I'} {U : BAGraph E I''}
    (h1 : BAScostLL Γ T) (h2 : BAScostLL T U) : BAScostLL Γ U := by
  intro s hs
  obtain ⟨s₁, hs₁, hsep₁, hc₁⟩ := h2 s hs
  obtain ⟨s₀, hs₀, hsep₀, hc₀⟩ := h1 s₁ hs₁
  exact ⟨s₀, hs₀, fun a b h => hsep₀ a b (hsep₁ a b h), hc₀.trans hc₁⟩

/-- The output classes of a step of the strategy `BALocStep` (at atoms): `band` =
matched, up to relabelling, with an output of a band `LocStep`; the BA-only shapes `s1` (first sum of `GGGamma`, `y`, `y'` in two
atoms), `e1` (`M_{αy}` of `lanlw` joining `[x]`, `[y]`), `e2` (an `M`-split joining two atoms joined by a parent solid edge),
`macroA`, `macroB` (the outputs of the macro steps that are not `band`; a lemma at their transfer intermediates).
(`deriving DecidableEq`: the case `sh = band` of `baStep_of_simC'`.) -/
inductive BAShape | band | s1 | e1 | e2 | macroA | macroB
  deriving DecidableEq

/-- A step relation with tagged outputs; `untag` forgets the tags. -/
abbrev BTStep : Type 1 := BAPGraph (Fin 2) → List (BAShape × BAPGraph (Fin 2)) → Prop

def untag (T : BTStep) (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))) : Prop :=
  ∃ LT, T P LT ∧ L = LT.map Prod.snd

/-- **The `ScostLL` lemma of a BA-only shape**, in packed form (as `localReg6d_locCostGe_term` in `Graph/LocalRegular6d.lean` packs
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
/-- **Lemma A for a circled edge inside a class** (`LGraph.scost_cons_loop_ge` in `Graph/LocalRegular6a.lean`, whose proof reads only
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


/-- **The split of the solid edges** (`baSplitSolid`, Definition B.4 `defn_normalBA`): the circled copies and the dropped edges of a term of
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

/-- **BA Lemma B, pointwise** (Definition B.4; the band: `LGraph.scost_partition_ge` in `Graph/LocalRegular6a.lean`): every term `Q` of
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

/-- **BA Lemma B** (`G = Ǧ + M`, Definition B.4; includes the extra outputs `E2`: an `M`-split joining two atoms joined by a kept edge):
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

/-- **The merge of the `=`-dotted classes never costs less than the graph at the pulled-back merge**: the relabelled atomic
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

/-- **`BAInit`, the initial values** (`fxyPowGraph_locCostGe` in `Graph/LocalRegular6a.lean`, at BA): every BA term of `G = Ǧ + M` on
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


/-! ## 5. The reduction of `BAScostLL` to the band local lemma on the atomic image -/

section Reduction

variable {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']

/-- **The reduction to the band** (`LGraph.ScostLL` in `Graph/LocalRegular6a.lean`): the band local lemmas quantify over all setoids and
return an arbitrary `s₀`, so they apply to the atom quotient `(promoteC Γ).merge` (the atomic image `Γ.img.g`), where every setoid
pulls back to a merge that contains the atoms.  A map `ψ` of the vertices of `T` onto those of a band graph `Λ` over the image of `Γ`
(external vertices to the images of the external vertices, `ker ψ` inside the atoms of `T`) transports the merges of `T`, and
`hcost` compares the costs there (typically `BAScost_scost_le_of_Up`). -/
theorem BAScostLL_of_band (Γ : BAGraph E I) (T : BAGraph E I') {J : Type} [Fintype J] [DecidableEq J]
    (Λ : LGraph (promoteC Γ).ExtCls J) (hLL : LGraph.ScostLL (promoteC Γ).merge Λ)
    (ψ : E ⊕ I' → (promoteC Γ).ExtCls ⊕ J) (hψ : Function.Surjective ψ)
    (hψl : ∀ a : E, ψ (Sum.inl a) = Sum.inl ((promoteC Γ).extMap a))
    (hker : ∀ u v, ψ u = ψ v → atomSetoid T u v)
    (hcost : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ J), (∀ u v, atomSetoid T u v → s'' (ψ u) (ψ v)) →
      Λ.scost s'' ≤ ((promoteC T).relabel ψ).scost s'') : BAScostLL Γ T := by
  classical
  intro s hs
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : (promoteC Γ).ExtCls ⊕ J → E ⊕ I', ∀ w, ψ (ψ' w) = w :=
    ⟨Function.surjInv hψ, Function.surjInv_eq hψ⟩
  have hback : ∀ a, s (ψ' (ψ a)) a := fun a => hs (hker _ _ (hψ' (ψ a)))
  set s'' : Setoid ((promoteC Γ).ExtCls ⊕ J) := Setoid.comap ψ' s with hs''
  have hcomap : ∀ a b, s'' (ψ a) (ψ b) ↔ s a b := by
    intro a b
    show s (ψ' (ψ a)) (ψ' (ψ b)) ↔ s a b
    exact ⟨fun h => s.trans (s.symm (hback a)) (s.trans h (hback b)),
      fun h => s.trans (hback a) (s.trans h (s.symm (hback b)))⟩
  have hadm : ∀ u v, atomSetoid T u v → s'' (ψ u) (ψ v) := fun u v h => (hcomap u v).2 (hs h)
  obtain ⟨s_0, hsep, hc0⟩ := hLL s''
  refine ⟨Setoid.comap (promoteC Γ).vmap s_0, ?_, ?_, ?_⟩
  · intro u v h
    show s_0 ((promoteC Γ).vmap u) ((promoteC Γ).vmap v)
    rw [(BAAtomic_promoteC_vmap_eq_atom Γ u v).2 ((BAAtomic_atomSetoid_iff Γ u v).1 h)]
  · intro a b hab hc
    have hc' : s_0 (Sum.inl ((promoteC Γ).extMap a)) (Sum.inl ((promoteC Γ).extMap b)) := by
      have h0 : s_0 ((promoteC Γ).vmap (Sum.inl a)) ((promoteC Γ).vmap (Sum.inl b)) := hc
      rwa [BAAtomic_vmap_inl, BAAtomic_vmap_inl] at h0
    refine hsep _ _ (fun h => hab ?_) hc'
    have h1 : s'' (ψ (Sum.inl a)) (ψ (Sum.inl b)) := by rw [hψl, hψl]; exact h
    exact (hcomap _ _).1 h1
  · show scostA Γ (Setoid.comap (promoteC Γ).vmap s_0) ≤ scostA T s
    have e1 : scostA Γ (Setoid.comap (promoteC Γ).vmap s_0) = (promoteC Γ).merge.scost s_0 := by
      unfold scostA
      rw [← LGraph.scost_relabel (promoteC Γ) (promoteC Γ).extMap (promoteC Γ).extMap_surj (promoteC Γ).vmap
        (BAAtomic_vmap_surjective _) (BAAtomic_vmap_inl _) s_0]
      exact localReg6a_scost_congr _ _ s_0 rfl rfl
    have e2 : ((promoteC T).relabel ψ).scost s'' = scostA T s := by
      unfold scostA
      rw [LGraph.scost_relabel (promoteC T) (promoteC Γ).extMap (promoteC Γ).extMap_surj ψ hψ hψl s'']
      congr 1
      exact Setoid.ext hcomap
    rw [e1]
    exact hc0.trans ((hcost s'' hadm).trans (le_of_eq e2))

end Reduction

/-! ## 6. The packed term lemma (the BA counterpart of `localReg6d_locCostGe_term`) -/

section Pack

/-- The packed output of a term of `P`: the partition term `Q0` of a term over the vertices of `P`, with the external vertices of `P`
read through `Q0.ext` (the packing of `localReg6d_locCostGe_term`, `Q0.lvl1Comp P.ext P.ext_surj`). -/
def BAScost_pack (P : BAPGraph (Fin 2)) (Q0 : BAPGraph P.E') : BAPGraph (Fin 2) where
  E' := Q0.E'
  I' := Q0.I'
  ext := Q0.ext ∘ P.ext
  ext_surj := Q0.ext_surj.comp P.ext_surj
  g := Q0.g

/-- **The step from a term to the packed outputs of its partition** (the BA counterpart of `localReg6d_locCostGe_term` in
`Graph/LocalRegular6d.lean`: Lemma B and the local lemma): if `BAScostLL P.g T` and `P` satisfies the bound, every term of the
partition of `T` does. -/
theorem BAScost_locCostGeA_term (P : BAPGraph (Fin 2)) {I'' : Type} [Fintype I''] [DecidableEq I''] (T : BAGraph P.E' I'')
    (far : Bool) (k : ℤ) (hLL : BAScostLL P.g T) (hk : locCostGeA far k P) :
    ∀ Q0 ∈ T.partition, locCostGeA far k (BAScost_pack P Q0) := by
  intro Q0 hQ0
  simp only [BAGraph.partition, List.mem_map] at hQ0
  obtain ⟨Q, hQ, rfl⟩ := hQ0
  intro s hs hfar
  set sQ : Setoid (P.E' ⊕ I'') := Setoid.comap Q.toLGraph.vmap s with hsQ
  have hatom : atomSetoid Q ≤ sQ := fun u v h => hs (BAScost_atomSetoid_merge Q h)
  obtain ⟨sT, hsT, hsepT, hcT⟩ := BAScostLL_splitG T hQ sQ hatom
  obtain ⟨sP, hsP, hsepP, hcP⟩ := hLL sT hsT
  have hf : far = true → ¬ sP (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) := by
    intro hfr hc
    have hQn : ¬ sQ (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) := by
      intro h
      apply hfar hfr
      have h' : s (Q.toLGraph.vmap (Sum.inl (P.ext 0))) (Q.toLGraph.vmap (Sum.inl (P.ext 1))) := h
      rw [BAAtomic_vmap_inl, BAAtomic_vmap_inl] at h'
      exact h'
    exact hsepP _ _ (hsepT _ _ hQn) hc
  have hk' := hk sP hsP hf
  exact hk'.trans (hcP.trans (hcT.trans (BAScost_scostA_le_merge Q s)))

end Pack


/-! ## 7. Tools for the shapes: extensions by new vertices -/

section ShapeTools

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open private BAWeightOp_ext_atomAdj from RBM3D.Graph.BAWeightOp

/-- the atoms of an extension contain the atoms of the graph (renamed) -/
theorem BAScost_atomSetoid_ext {k : ℕ} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    {u v : E ⊕ I} (h : atomSetoid Γ u v) :
    atomSetoid (BAGraph.ext k Γ rest S W md) (owxEmb k u) (owxEmb k v) := by
  rw [BAAtomic_atomSetoid_iff] at h ⊢
  rw [BAGraph.mem_atom_iff] at h ⊢
  exact Relation.ReflTransGen.lift (p := fun a b => (BAGraph.ext k Γ rest S W md).atomAdj a b = true) (owxEmb k)
    (fun a b hab => (BAWeightOp_ext_atomAdj k Γ rest S W md (owxEmb k a) (owxEmb k b)).2 (Or.inl ⟨a, b, rfl, rfl, hab⟩)) u v h

/-- the new `M`-dotted edges of an extension join vertices of one atom -/
theorem BAScost_atomSetoid_ext_md {k : ℕ} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (m : BAMEdge (E ⊕ (I ⊕ Fin k))) (hm : m ∈ md) :
    atomSetoid (BAGraph.ext k Γ rest S W md) m.x m.y :=
  BAScost_atomSetoid_of_mdot _ m (by simp [BAGraph.ext, hm])

/-- the solid edges of the atomic image of an extension -/
theorem BAScost_ext_promoteC_solid {k : ℕ} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) :
    (promoteC (BAGraph.ext k Γ rest S W md)).solid =
      (rest.map (SEdge.map (owxEmb k)) ++ S).map (fun e =>
        (⟨e.σ, e.circ && (BAGraph.ext k Γ rest S W md).sameAtom e.src e.dst, e.src, e.dst⟩ : SEdge (E ⊕ (I ⊕ Fin k)))) := by
  rw [BAAtomic_promoteC_solid]
  rfl

/-- **The old edges**: at a merge, the old solid edges of an extension, read at a vertex map `ψ` that agrees with a map `kap` of the
atom classes on the old vertices, are the old solid edges of `Γ` at the atomic image with larger circles (an old edge between two
atoms of `Γ` that the new `M`-dotted edges join becomes a circled edge inside an atom). -/
theorem BAScost_Up_old {k : ℕ} {W' : Type} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (ψ : E ⊕ (I ⊕ Fin k) → W') (kap : (promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls → W')
    (hψkap : ∀ v, ψ (owxEmb k v) = kap ((promoteC Γ).vmap v)) (s : Setoid W') :
    BAScost_Up s
      (rest.map (fun e => (⟨e.σ, e.circ && Γ.sameAtom e.src e.dst, kap ((promoteC Γ).vmap e.src), kap ((promoteC Γ).vmap e.dst)⟩ :
        SEdge W')))
      (rest.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext k Γ rest S W md).sameAtom (owxEmb k e.src) (owxEmb k e.dst),
        ψ (owxEmb k e.src), ψ (owxEmb k e.dst)⟩ : SEdge W'))) := by
  refine BAScost_Up_map s rest _ _ (fun e he => ⟨rfl, ?_, ?_, fun h => ?_⟩)
  · exact hψkap e.src
  · exact hψkap e.dst
  · simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    rw [Γ.BAAtomic_sameAtom_iff, ← BAAtomic_atomSetoid_iff] at h
    rw [(BAGraph.ext k Γ rest S W md).BAAtomic_sameAtom_iff, ← BAAtomic_atomSetoid_iff]
    exact BAScost_atomSetoid_ext Γ rest S W md h.2

/-- the kernel of a retraction onto the old vertices: if every new vertex lies in the atom of its image, a map that factors through
the atom classes of the old vertices has its kernel inside the atoms -/
theorem BAScost_ker_ext {k : ℕ} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (rt : E ⊕ (I ⊕ Fin k) → E ⊕ I) (hrt : ∀ w, atomSetoid (BAGraph.ext k Γ rest S W md) w (owxEmb k (rt w)))
    (u v : E ⊕ (I ⊕ Fin k)) (h : (promoteC Γ).vmap (rt u) = (promoteC Γ).vmap (rt v)) :
    atomSetoid (BAGraph.ext k Γ rest S W md) u v := by
  have h1 : atomSetoid Γ (rt u) (rt v) :=
    (BAAtomic_atomSetoid_iff Γ _ _).2 ((BAAtomic_promoteC_vmap_eq_atom Γ _ _).1 h)
  have h2 := BAScost_atomSetoid_ext Γ rest S W md h1
  exact (atomSetoid _).trans ((atomSetoid _).trans (hrt u) h2) ((atomSetoid _).symm (hrt v))


/-- the solid edges of the relabelled atomic image of an extension: the old edges and the new edges -/
theorem BAScost_ext_relabel_solid {k : ℕ} {E' I' : Type} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (ψ : E ⊕ (I ⊕ Fin k) → E' ⊕ I') :
    ((promoteC (BAGraph.ext k Γ rest S W md)).relabel ψ).solid =
      rest.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext k Γ rest S W md).sameAtom (owxEmb k e.src) (owxEmb k e.dst),
        ψ (owxEmb k e.src), ψ (owxEmb k e.dst)⟩ : SEdge (E' ⊕ I'))) ++
      S.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext k Γ rest S W md).sameAtom e.src e.dst, ψ e.src, ψ e.dst⟩ :
        SEdge (E' ⊕ I'))) := by
  simp only [LGraph.relabel, BAScost_ext_promoteC_solid, List.map_append, List.map_map]
  rfl

/-- the number of waved edges of the relabelled atomic image of an extension -/
theorem BAScost_ext_relabel_waved_length {k : ℕ} {E' I' : Type} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (ψ : E ⊕ (I ⊕ Fin k) → E' ⊕ I') :
    ((promoteC (BAGraph.ext k Γ rest S W md)).relabel ψ).waved.length = Γ.waved.length + W.length := by
  simp [LGraph.relabel, promoteC, BAGraph.ext, LGraph.owxExt]

/-- the image of a solid edge of `Γ` in the atomic image (`BAGraph.BAAtomic_img_solid`) -/
def BAScost_imgE (Γ : BAGraph E I) (e : SEdge (E ⊕ I)) : SEdge ((promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls) :=
  ⟨e.σ, e.circ && Γ.sameAtom e.src e.dst, (promoteC Γ).vmap e.src, (promoteC Γ).vmap e.dst⟩

theorem BAScost_img_solid (Γ : BAGraph E I) : (promoteC Γ).merge.solid = Γ.solid.map (BAScost_imgE Γ) :=
  Γ.BAAtomic_img_solid

/-- the waved edges of the atomic image are those of `Γ` -/
theorem BAScost_img_waved_length (Γ : BAGraph E I) : (promoteC Γ).merge.waved.length = Γ.waved.length := by
  simp [LGraph.merge, promoteC]

/-- the retraction of `E ⊕ (I ⊕ Fin 2)` onto `E ⊕ I`: the new vertices `bpv 0`, `bpv 1` go to `x`, `y` -/
def BAScost_rho2 (x y : E ⊕ I) : E ⊕ (I ⊕ Fin 2) → E ⊕ I
  | Sum.inl e => Sum.inl e
  | Sum.inr (Sum.inl i) => Sum.inr i
  | Sum.inr (Sum.inr j) => if j = 0 then x else y

theorem BAScost_rho2_emb (x y v : E ⊕ I) : BAScost_rho2 x y (owxEmb 2 v) = v := by
  rcases v with a | i <;> rfl

theorem BAScost_sameAtom_self (Γ : BAGraph E I) (u : E ⊕ I) : Γ.sameAtom u u = true := by
  rw [Γ.BAAtomic_sameAtom_iff, ← BAAtomic_atomSetoid_iff]

theorem BAScost_vmap_ne_of_sameAtom (Γ : BAGraph E I) {u v : E ⊕ I} (h : Γ.sameAtom u v = false) :
    (promoteC Γ).vmap u ≠ (promoteC Γ).vmap v := fun h' => by
  rw [BAAtomic_promoteC_vmap_eq_sameAtom] at h'
  rw [h] at h'
  exact Bool.false_ne_true h'

end ShapeTools


/-! ## 8. The shape S1: `GGGamma`, the first sum -/

section ShapeS1

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`S1`** ((B.20) `GGGamma`, the first sum; `BAGGOp_A1` is the first term of `gg2`): `Σ_{u,β} M_{xu} M_{ux} S⁺_{uβ} M_{βy} M_{y'β} f`
at a pair `Ǧ_{xy}`, `Ǧ_{y'x}` of blue circled edges that are not atom-level loops (`[x] ≠ [y]`, `[y'] ≠ [x]`; `[y]`, `[y']` may or may not be
equal).  The pair is contracted to a waved edge `[x] - [y]` and `[y]`, `[y']` are merged (through `β`): the atomic image of the term is the band's
`Contract(z = [x]; u = [y'], v = [y])` (`lwPrimContract` in `Graph/LocalRegular6a.lean`) with the contracted edge `u → v` dropped (`[u] = [v]` at every merge of
the term), and the local lemma is `scostLL_contract` (`Graph/LocalRegular6b.lean`) on the atomic image `(promoteC Γ).merge`. -/
theorem BAScostLL_S1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    BAScostLL Γ (BAGGOp_A1 Γ p q) := by
  classical
  have hA1 : BAGGOp_A1 Γ p q = BAGraph.ext 2 Γ q.2 [] [bpW true (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst),
        bpM (owxEmb 2 q.1.src) (bpv 1)] := rfl
  rw [hA1]
  have hwf2' : Γ.sameAtom q.1.src p.1.src = false := hxy ▸ hwf2
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.src⟩ :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h3 : Γ.solid.Perm (p.1 :: q.1 :: q.2) :=
      (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)
    have h4 := h3.map (BAScost_imgE Γ)
    have e1 : BAScost_imgE Γ p.1 = ⟨true, false, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.dst⟩ := by
      simp [BAScost_imgE, hp1.1, hp1.2, hwf1]
    have e2 : BAScost_imgE Γ q.1 = ⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.src⟩ := by
      simp [BAScost_imgE, hq1.1, hq1.2, hwf2', hxy]
    rw [List.map_cons, List.map_cons, e1, e2] at h4
    exact h4
  have hLL := scostLL_contract (promoteC Γ).merge (q.2.map (BAScost_imgE Γ)) ((promoteC Γ).vmap p.1.src)
    ((promoteC Γ).vmap q.1.src) ((promoteC Γ).vmap p.1.dst)
    (BAScost_vmap_ne_of_sameAtom Γ hwf2') (BAScost_vmap_ne_of_sameAtom Γ hwf1) hperm
  have hmd : ∀ m ∈ [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst),
        bpM (owxEmb 2 q.1.src) (bpv 1)], atomSetoid (BAGraph.ext 2 Γ q.2 [] [bpW true (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst),
        bpM (owxEmb 2 q.1.src) (bpv 1)]) m.x m.y := fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  have hrt : ∀ w, atomSetoid (BAGraph.ext 2 Γ q.2 [] [bpW true (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst),
        bpM (owxEmb 2 q.1.src) (bpv 1)]) w (owxEmb 2 (BAScost_rho2 p.1.src p.1.dst w)) := by
    intro w
    rcases w with e | i | j
    · exact (atomSetoid _).refl' _
    · exact (atomSetoid _).refl' _
    · fin_cases j
      · exact (atomSetoid _).symm (hmd (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp))
      · exact hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp)
  refine BAScostLL_of_band Γ _ _ hLL ((promoteC Γ).vmap ∘ BAScost_rho2 (p.1.src) (p.1.dst)) ?_ ?_ ?_ ?_
  · exact (BAAtomic_vmap_surjective _).comp (fun v => ⟨owxEmb 2 v, BAScost_rho2_emb _ _ v⟩)
  · intro a
    exact BAAtomic_vmap_inl (promoteC Γ) a
  · intro u v h
    exact BAScost_ker_ext Γ q.2 [] _ _ (BAScost_rho2 p.1.src p.1.dst) hrt u v h
  · intro s'' hadm
    have hψ : ∀ v, ((promoteC Γ).vmap ∘ BAScost_rho2 p.1.src p.1.dst) (owxEmb 2 v) = (promoteC Γ).vmap v := fun v => by
      simp [BAScost_rho2_emb]
    have hu : s'' ((promoteC Γ).vmap q.1.src) ((promoteC Γ).vmap p.1.dst) := by
      have h1 : atomSetoid (BAGraph.ext 2 Γ q.2 [] [bpW true (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst),
            bpM (owxEmb 2 q.1.src) (bpv 1)]) (owxEmb 2 q.1.src) (owxEmb 2 p.1.dst) :=
        (atomSetoid _).trans (hmd (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp)) (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp))
      have h2 := hadm _ _ h1
      rwa [hψ, hψ] at h2
    refine BAScost_scost_le_of_Up _ _ s'' ?_ ?_
    · rw [BAScost_ext_relabel_solid, List.map_nil, List.append_nil]
      show BAScost_Up s'' (⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.dst⟩ :: q.2.map (BAScost_imgE Γ)) _
      refine BAScost_Up.drop s'' _ ?_ rfl hu
      have := BAScost_Up_old (k := 2) Γ q.2 [] [bpW true (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst),
          bpM (owxEmb 2 q.1.src) (bpv 1)] ((promoteC Γ).vmap ∘ BAScost_rho2 p.1.src p.1.dst) (fun w => w) hψ s''
      exact this
    · rw [BAScost_ext_relabel_waved_length]
      simp [lwPrimContract, BAScost_img_waved_length]

end ShapeS1

/-! ## 9. The vertex map of the shapes with one fresh vertex -/

section ShapePsi1

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem BAScost_owxEmb_inj {E' I' : Type} (k : ℕ) : Function.Injective (owxEmb (E := E') (I := I') k) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp [owxEmb] at h <;> simp [h]

/-- **The vertex map of an extension by `α = bpv 0`, `β = bpv 1`** onto the band vertices of the atomic image of `Γ` plus one fresh vertex:
the old vertices go to their atoms, `α` to the atom of the old vertex `a` (it carries an `M`-dotted edge to `a`), `β` to the fresh vertex. -/
def BAScost_psi1 (Γ : BAGraph E I) (a : E ⊕ I) :
    E ⊕ (I ⊕ Fin 2) → (promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 1)
  | Sum.inl e => Sum.inl ((promoteC Γ).extMap e)
  | Sum.inr (Sum.inl i) => owxEmb 1 ((promoteC Γ).vmap (Sum.inr i))
  | Sum.inr (Sum.inr j) => if j = 0 then owxEmb 1 ((promoteC Γ).vmap a) else Sum.inr (Sum.inr 0)

theorem BAScost_psi1_emb (Γ : BAGraph E I) (a v : E ⊕ I) :
    BAScost_psi1 Γ a (owxEmb 2 v) = owxEmb 1 ((promoteC Γ).vmap v) := by
  rcases v with e | i
  · simp [BAScost_psi1, owxEmb, BAAtomic_vmap_inl]
  · rfl

theorem BAScost_psi1_alpha (Γ : BAGraph E I) (a : E ⊕ I) :
    BAScost_psi1 Γ a (bpv 0) = owxEmb 1 ((promoteC Γ).vmap a) := by
  simp [BAScost_psi1]

theorem BAScost_psi1_beta (Γ : BAGraph E I) (a : E ⊕ I) :
    BAScost_psi1 Γ a (bpv 1) = Sum.inr (Sum.inr 0) := by
  simp [BAScost_psi1]

theorem BAScost_psi1_surj (Γ : BAGraph E I) (a : E ⊕ I) : Function.Surjective (BAScost_psi1 Γ a) := by
  intro w
  rcases scostLL_emb_cases w with ⟨v, rfl⟩ | rfl
  · obtain ⟨v₀, rfl⟩ := BAAtomic_vmap_surjective (promoteC Γ) v
    exact ⟨owxEmb 2 v₀, BAScost_psi1_emb Γ a v₀⟩
  · exact ⟨bpv 1, BAScost_psi1_beta Γ a⟩

theorem BAScost_psi1_inl (Γ : BAGraph E I) (a : E ⊕ I) (e : E) :
    BAScost_psi1 Γ a (Sum.inl e) = Sum.inl ((promoteC Γ).extMap e) := rfl

/-- the kernel of `BAScost_psi1` lies inside the atoms of the extension, if `α` lies in the atom of `a` -/
theorem BAScost_ker_psi1 (Γ : BAGraph E I) (a : E ⊕ I) (T : BAGraph E (I ⊕ Fin 2))
    (hα : atomSetoid T (bpv 0) (owxEmb 2 a))
    (hmono : ∀ u v, atomSetoid Γ u v → atomSetoid T (owxEmb 2 u) (owxEmb 2 v))
    (u v : E ⊕ (I ⊕ Fin 2)) (h : BAScost_psi1 Γ a u = BAScost_psi1 Γ a v) : atomSetoid T u v := by
  -- retract `α` to `a`
  let rt : E ⊕ (I ⊕ Fin 2) → E ⊕ (I ⊕ Fin 2) := fun w =>
    match w with
    | Sum.inr (Sum.inr j) => if j = 0 then owxEmb 2 a else w
    | _ => w
  have hrt : ∀ w, atomSetoid T w (rt w) := by
    intro w
    rcases w with e | i | j
    · exact (atomSetoid _).refl' _
    · exact (atomSetoid _).refl' _
    · fin_cases j
      · exact hα
      · exact (atomSetoid _).refl' _
  have hψrt : ∀ w, BAScost_psi1 Γ a (rt w) = BAScost_psi1 Γ a w := by
    intro w
    rcases w with e | i | j
    · rfl
    · rfl
    · fin_cases j
      · show BAScost_psi1 Γ a (owxEmb 2 a) = BAScost_psi1 Γ a (bpv 0)
        rw [BAScost_psi1_emb, BAScost_psi1_alpha]
      · rfl
  have hold : ∀ w, (∃ v₀, rt w = owxEmb 2 v₀) ∨ rt w = bpv 1 := by
    intro w
    rcases w with e | i | j
    · exact Or.inl ⟨Sum.inl e, rfl⟩
    · exact Or.inl ⟨Sum.inr i, rfl⟩
    · fin_cases j
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr rfl
  have h' : BAScost_psi1 Γ a (rt u) = BAScost_psi1 Γ a (rt v) := by rw [hψrt, hψrt]; exact h
  refine (atomSetoid _).trans (hrt u) ((atomSetoid _).trans ?_ ((atomSetoid _).symm (hrt v)))
  rcases hold u with ⟨u₀, hu⟩ | hu <;> rcases hold v with ⟨v₀, hv⟩ | hv
  · rw [hu, hv] at h' ⊢
    rw [BAScost_psi1_emb, BAScost_psi1_emb] at h'
    have := BAScost_owxEmb_inj 1 h'
    exact hmono _ _ ((BAAtomic_atomSetoid_iff Γ _ _).2 ((BAAtomic_promoteC_vmap_eq_atom Γ _ _).1 this))
  · rw [hu, hv] at h'
    rw [BAScost_psi1_emb, BAScost_psi1_beta] at h'
    exact absurd h' (scostLL_emb_ne_alpha _)
  · rw [hu, hv] at h'
    rw [BAScost_psi1_emb, BAScost_psi1_beta] at h'
    exact absurd h'.symm (scostLL_emb_ne_alpha _)
  · rw [hu, hv]

end ShapePsi1

theorem BAScost_perm_snoc2 {α : Type*} (A : List α) (a b : α) : (A ++ [b, a]).Perm (a :: (A ++ [b])) := by
  simpa using List.perm_append_singleton a (A ++ [b])

/-- an uncircled edge inside a class on the right does not count -/
theorem BAScost_Up.drop_right {V : Type} (s : Setoid V) {l l' : List (SEdge V)} (e : SEdge V) (h : BAScost_Up s l l')
    (hc : e.circ = false) (hs : s e.src e.dst) : BAScost_Up s l (e :: l') := by
  obtain ⟨Y, hY, hp⟩ := h
  refine ⟨Y, hY, ?_⟩
  rw [BAScost_kept_cons_not s e l' (by simp [hc, hs])]
  exact hp

/-! ## 10. The band primitives with a fresh vertex: their solid and waved edges -/

section PrimShape

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem BAScost_lwPrimLoop_solid (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) :
    (lwPrimLoop Γ z col).solid = Γ.solid.map (SEdge.map (owxEmb 1)) ++
      [(⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1)))] := rfl

theorem BAScost_lwPrimLoop_waved_length (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) :
    (lwPrimLoop Γ z col).waved.length = Γ.waved.length + 1 := by simp [lwPrimLoop, LGraph.owxExt]

theorem BAScost_lwPrimMoveLoop_solid (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z : E ⊕ I) (col : Bool) :
    (lwPrimMoveLoop Γ rest z col).solid = rest.map (SEdge.map (owxEmb 1)) ++
      [(⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1)))] := rfl

theorem BAScost_lwPrimMoveLoop_waved_length (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z : E ⊕ I) (col : Bool) :
    (lwPrimMoveLoop Γ rest z col).waved.length = Γ.waved.length + 1 := by simp [lwPrimMoveLoop, LGraph.owxExt]

theorem BAScost_lwPrimMoveSC_solid (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) :
    (lwPrimMoveSC Γ rest z u v).solid = rest.map (SEdge.map (owxEmb 1)) ++
      [(⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1))),
        ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] := rfl

theorem BAScost_lwPrimMoveSC_waved_length (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) :
    (lwPrimMoveSC Γ rest z u v).waved.length = Γ.waved.length + 1 := by simp [lwPrimMoveSC, LGraph.owxExt]

end PrimShape

/-! ## 11. The shapes `E1` and `macroA`: `lanlw`, term `T1` -/

section ShapeLoop

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The transfer graph of macro step (a)**: the `M`-split of the first term `T1` of `lanlw`
(`BAGraph.lanlwT1`, `M_{αy}`) at the blue circled edge `Ǧ_{xy}`: `Σ_{α,β} M_{xα} M_{αy} S_{αβ} Ǧ_{ββ} f`. -/
def BAGraph.BAScost_trA (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]

/-- **The macro (a) intermediate** (`BAGraph.BAScost_trA` has the solid and waved edges of the `M`-branch `M_{αy}` of `lanlwT1`, Lemma B.6; its `M`-dotted list is `[M_{xα}, M_{αy}]`): `Σ_{α,β} M_{xα} M_{αy} S_{αβ} Ǧ_{ββ} f` at a blue circled edge `Ǧ_{xy}`.  Local lemma in both regimes, no atom hypothesis: if `[x] = [y]`
(a within-atom edge; the macro step) the edge is a circled loop of the atomic image and the image of `tr` is the band's `MoveLoop(z = [x])`
(`scostLL_moveLoop` in `Graph/LocalRegular6b.lean`); if `[x] ≠ [y]` (`E1`, the extra output of `lanlw`: the band's `×`-dot forbids it) the image is
`Loop(z = [x])` (`scostLL_loop` in `Graph/LocalRegular6b.lean`) with the edge `[x] → [y]` dropped (`[x]`, `[y]` are in one class at every merge of `tr`). -/
theorem BAScostLL_macroA (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) : BAScostLL Γ (Γ.BAScost_trA p) := by
  classical
  unfold BAGraph.BAScost_trA
  have hmdx : atomSetoid (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]) (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ p.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  have hmdy : atomSetoid (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]) (bpv 0) (owxEmb 2 p.1.dst) :=
    BAScost_atomSetoid_ext_md Γ p.2 _ _ _ (bpM (bpv 0) (owxEmb 2 p.1.dst)) (by simp)
  have hperm0 : Γ.solid.Perm (p.1 :: p.2) := lwSplit_perm Γ.solid p hp
  have hker := fun u v h => BAScost_ker_psi1 Γ p.1.src _ ((atomSetoid _).symm hmdx)
    (fun u v h => BAScost_atomSetoid_ext Γ p.2 _ _ _ h) u v h
  have hold : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 1)),
      BAScost_Up s'' (p.2.map (fun e => SEdge.map (owxEmb 1) (BAScost_imgE Γ e)))
        (p.2.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]).sameAtom (owxEmb 2 e.src) (owxEmb 2 e.dst),
          BAScost_psi1 Γ p.1.src (owxEmb 2 e.src), BAScost_psi1 Γ p.1.src (owxEmb 2 e.dst)⟩ : SEdge _))) := fun s'' =>
    BAScost_Up_old (k := 2) Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)] (BAScost_psi1 Γ p.1.src) (owxEmb 1)
      (BAScost_psi1_emb Γ p.1.src) s''
  have hloop : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 1)),
      BAScost_Up s'' [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge _)]
        ([bpS true (bpv 1) (bpv 1)].map (fun e => (⟨e.σ, e.circ && (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)]
          [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]).sameAtom e.src e.dst,
          BAScost_psi1 Γ p.1.src e.src, BAScost_psi1 Γ p.1.src e.dst⟩ : SEdge _))) := by
    intro s''
    refine BAScost_Up.cons s'' _ _ (BAScost_Up.refl s'' []) rfl ?_ ?_ (fun _ => ?_)
    · simp [BAScost_psi1_beta, bpS, bpv]
    · simp [BAScost_psi1_beta, bpS, bpv]
    · simp [bpS, BAScost_sameAtom_self]
  by_cases hxy : Γ.sameAtom p.1.src p.1.dst = true
  · -- `[x] = [y]`: `MoveLoop`
    have hvv : (promoteC Γ).vmap p.1.src = (promoteC Γ).vmap p.1.dst :=
      (BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hxy
    have e1 : BAScost_imgE Γ p.1 = ⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ := by
      simp [BAScost_imgE, hp1.1, hp1.2, hxy, hvv]
    have hperm : (promoteC Γ).merge.solid.Perm (⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ ::
        p.2.map (BAScost_imgE Γ)) := by
      rw [BAScost_img_solid]
      have h4 := hperm0.map (BAScost_imgE Γ)
      rw [List.map_cons, e1] at h4
      exact h4
    refine BAScostLL_of_band Γ _ _ (scostLL_moveLoop (promoteC Γ).merge (p.2.map (BAScost_imgE Γ))
      ((promoteC Γ).vmap p.1.src) true hperm) (BAScost_psi1 Γ p.1.src) (BAScost_psi1_surj Γ _)
      (fun a => BAScost_psi1_inl Γ _ a) hker ?_
    intro s'' hadm
    refine BAScost_scost_le_of_Up _ _ s'' ?_ ?_
    · rw [BAScost_ext_relabel_solid, BAScost_lwPrimMoveLoop_solid, List.map_map]
      exact BAScost_Up.append s'' (hold s'') (hloop s'')
    · rw [BAScost_ext_relabel_waved_length, BAScost_lwPrimMoveLoop_waved_length, BAScost_img_waved_length]
      rfl
  · -- `[x] ≠ [y]`: `Loop`
    have hxy' : Γ.sameAtom p.1.src p.1.dst = false := by simpa using hxy
    refine BAScostLL_of_band Γ _ _ (scostLL_loop (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) true)
      (BAScost_psi1 Γ p.1.src) (BAScost_psi1_surj Γ _) (fun a => BAScost_psi1_inl Γ _ a) hker ?_
    intro s'' hadm
    have hs : s'' (owxEmb 1 ((promoteC Γ).vmap p.1.src)) (owxEmb 1 ((promoteC Γ).vmap p.1.dst)) := by
      have h := hadm (owxEmb 2 p.1.src) (owxEmb 2 p.1.dst) ((atomSetoid _).trans hmdx hmdy)
      rwa [BAScost_psi1_emb, BAScost_psi1_emb] at h
    refine BAScost_scost_le_of_Up _ _ s'' ?_ ?_
    · rw [BAScost_ext_relabel_solid, BAScost_lwPrimLoop_solid, BAScost_img_solid, List.map_map]
      have hP : (List.map (SEdge.map (owxEmb 1) ∘ BAScost_imgE Γ) Γ.solid ++
          [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge _)]).Perm
          (SEdge.map (owxEmb 1) (BAScost_imgE Γ p.1) ::
            (p.2.map (fun e => SEdge.map (owxEmb 1) (BAScost_imgE Γ e)) ++
              [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge _)])) :=
        (hperm0.map (SEdge.map (owxEmb 1) ∘ BAScost_imgE Γ)).append_right _
      refine BAScost_Up.perm_left s'' hP ?_
      refine BAScost_Up.drop s'' _ (BAScost_Up.append s'' (hold s'') (hloop s'')) ?_ hs
      simp [BAScost_imgE, SEdge.map, hp1.2, hxy']
    · rw [BAScost_ext_relabel_waved_length, BAScost_lwPrimLoop_waved_length, BAScost_img_waved_length]
      rfl


/-- `lanlwT1` as an extension (`BAGraph.lanlwExt` with the coefficient `1` is `BAGraph.ext 2`) -/
theorem BAScost_lanlwT1_eq (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGraph.lanlwT1 Γ p = BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)]
      [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] := rfl

/-- **The first term of `lanlw`** (Lemma B.6, `BAGraph.lanlwT1`): `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} f` has the local lemma in both regimes (`[x] ≠ [y]`:
the image is `Loop`, the edge `G_{αy}` is the edge `x → y`; `[x] = [y]`: `MoveLoop`, the uncircled edge `G_{αy}` inside the atom is not kept).  With Lemma B
(`BAScostLL_splitG`) every term of `G = Ǧ + M` on it, among them the `M`-split `M_{αy}` (`E1`), has the local lemma. -/
theorem BAScostLL_lanlwT1 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) : BAScostLL Γ (BAGraph.lanlwT1 Γ p) := by
  classical
  rw [BAScost_lanlwT1_eq]
  have hmdx : atomSetoid (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)]
      [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]) (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ p.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  have hperm0 : Γ.solid.Perm (p.1 :: p.2) := lwSplit_perm Γ.solid p hp
  have hker := fun u v h => BAScost_ker_psi1 Γ p.1.src _ ((atomSetoid _).symm hmdx)
    (fun u v h => BAScost_atomSetoid_ext Γ p.2 _ _ _ h) u v h
  have hold : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 1)),
      BAScost_Up s'' (p.2.map (fun e => SEdge.map (owxEmb 1) (BAScost_imgE Γ e)))
        (p.2.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)]
          [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]).sameAtom (owxEmb 2 e.src) (owxEmb 2 e.dst),
          BAScost_psi1 Γ p.1.src (owxEmb 2 e.src), BAScost_psi1 Γ p.1.src (owxEmb 2 e.dst)⟩ : SEdge _))) := fun s'' =>
    BAScost_Up_old (k := 2) Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)]
      [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] (BAScost_psi1 Γ p.1.src) (owxEmb 1)
      (BAScost_psi1_emb Γ p.1.src) s''
  have hloopT : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 1)),
      BAScost_Up s'' [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge _)]
        ([(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge _)]) := fun s'' => BAScost_Up.refl s'' _
  have hS : ∀ (S : List (SEdge (E ⊕ (I ⊕ Fin 2)))), S = [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)] →
      ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 1)),
        S.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)]
          [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]).sameAtom e.src e.dst,
          BAScost_psi1 Γ p.1.src e.src, BAScost_psi1 Γ p.1.src e.dst⟩ : SEdge _)) =
          [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge _),
            ⟨true, false, owxEmb 1 ((promoteC Γ).vmap p.1.src), owxEmb 1 ((promoteC Γ).vmap p.1.dst)⟩] := by
    intro S hS s''
    subst hS
    simp [bpS, BAScost_sameAtom_self, BAScost_psi1_beta, BAScost_psi1_alpha, BAScost_psi1_emb, bpv]
  by_cases hxy : Γ.sameAtom p.1.src p.1.dst = true
  · -- `[x] = [y]`: `MoveLoop`
    have hvv : (promoteC Γ).vmap p.1.src = (promoteC Γ).vmap p.1.dst :=
      (BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hxy
    have e1 : BAScost_imgE Γ p.1 = ⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ := by
      simp [BAScost_imgE, hp1.1, hp1.2, hxy, hvv]
    have hperm : (promoteC Γ).merge.solid.Perm (⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ ::
        p.2.map (BAScost_imgE Γ)) := by
      rw [BAScost_img_solid]
      have h4 := hperm0.map (BAScost_imgE Γ)
      rw [List.map_cons, e1] at h4
      exact h4
    refine BAScostLL_of_band Γ _ _ (scostLL_moveLoop (promoteC Γ).merge (p.2.map (BAScost_imgE Γ))
      ((promoteC Γ).vmap p.1.src) true hperm) (BAScost_psi1 Γ p.1.src) (BAScost_psi1_surj Γ _)
      (fun a => BAScost_psi1_inl Γ _ a) hker ?_
    intro s'' hadm
    refine BAScost_scost_le_of_Up _ _ s'' ?_ ?_
    · rw [BAScost_ext_relabel_solid, BAScost_lwPrimMoveLoop_solid, List.map_map,
        hS _ rfl s'']
      refine BAScost_Up.append s'' (hold s'') ?_
      refine BAScost_Up.cons s'' _ _ ?_ rfl rfl rfl (fun h => h)
      refine BAScost_Up.drop_right s'' _ (BAScost_Up.refl s'' []) rfl ?_
      show s'' (owxEmb 1 ((promoteC Γ).vmap p.1.src)) (owxEmb 1 ((promoteC Γ).vmap p.1.dst))
      rw [hvv]
    · rw [BAScost_ext_relabel_waved_length, BAScost_lwPrimMoveLoop_waved_length, BAScost_img_waved_length]
      rfl
  · -- `[x] ≠ [y]`: `Loop`
    have hxy' : Γ.sameAtom p.1.src p.1.dst = false := by simpa using hxy
    refine BAScostLL_of_band Γ _ _ (scostLL_loop (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) true)
      (BAScost_psi1 Γ p.1.src) (BAScost_psi1_surj Γ _) (fun a => BAScost_psi1_inl Γ _ a) hker ?_
    intro s'' hadm
    refine BAScost_scost_le_of_Up _ _ s'' ?_ ?_
    · rw [BAScost_ext_relabel_solid, BAScost_lwPrimLoop_solid, BAScost_img_solid, List.map_map, hS _ rfl s'']
      have hP : (List.map (SEdge.map (owxEmb 1) ∘ BAScost_imgE Γ) Γ.solid ++
          [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge _)]).Perm
          (SEdge.map (owxEmb 1) (BAScost_imgE Γ p.1) ::
            (p.2.map (fun e => SEdge.map (owxEmb 1) (BAScost_imgE Γ e)) ++
              [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge _)])) :=
        (hperm0.map (SEdge.map (owxEmb 1) ∘ BAScost_imgE Γ)).append_right _
      refine BAScost_Up.perm_left s'' hP ?_
      refine BAScost_Up.perm_right s'' (BAScost_perm_snoc2 _ _ _).symm ?_
      refine BAScost_Up.cons s'' _ _ (BAScost_Up.append s'' (hold s'') (hloopT s'')) ?_ rfl rfl (fun h => ?_)
      · simp [BAScost_imgE, SEdge.map, hp1.1]
      · simp [BAScost_imgE, SEdge.map, hp1.2, hxy'] at h
    · rw [BAScost_ext_relabel_waved_length, BAScost_lwPrimLoop_waved_length, BAScost_img_waved_length]
      rfl

end ShapeLoop

/-! ## 12. The shape `macroB`: `lanlw`, then `GGGamma` at the transferred pair -/

section ShapeMoveSC

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The transfer graph of macro step (b)** (the graph `tr`): `lanlw` at `Ǧ_{ay}` (`p`), the
derivative on the partner edge `Ǧ_{y'a'}` (`q`, `a`, `a'` in one atom), its three solid edges split so that `Ǧ_{y'β}`, `Ǧ_{βy}` are circled and
`G_{αa'}` is the `M`-edge `M_{αa'}`: `Σ_{α,β} M_{aα} M_{αa'} S_{αβ} Ǧ_{y'β} Ǧ_{βy} f`. -/
def BAGraph.BAScost_trB (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)]
    [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst)]

/-- **The macro (b) intermediate** ((B.20) `GGGamma` at the transferred pair): at the pair `Ǧ_{ay}`, `Ǧ_{y'a'}` of one atom
(`[a] = [a'] =: z`, the ends `[y]`, `[y']` and `z` apart) the image of the transfer graph is the band's `MoveSC(z; u = [y'], v = [y])`
(`lwPrimMoveSC` in `Graph/LocalRegular6a.lean`: the edges `z → v`, `u → z` replaced by `u → β → v` with a waved edge `z - β`), and the
local lemma is `scostLL_moveSC` (`Graph/LocalRegular6c.lean`) on the atomic image.  No new primitive of the size of `Dmove` is needed. -/
theorem BAScostLL_macroB (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    BAScostLL Γ (Γ.BAScost_trB p q) := by
  classical
  unfold BAGraph.BAScost_trB
  have hvv : (promoteC Γ).vmap q.1.dst = (promoteC Γ).vmap p.1.src :=
    ((BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hsame).symm
  have hu : (promoteC Γ).vmap q.1.src ≠ (promoteC Γ).vmap p.1.src := by
    rw [← hvv]
    exact BAScost_vmap_ne_of_sameAtom Γ hwf2
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.src⟩ :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h3 : Γ.solid.Perm (p.1 :: q.1 :: q.2) :=
      (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)
    have h4 := h3.map (BAScost_imgE Γ)
    have e1 : BAScost_imgE Γ p.1 = ⟨true, false, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.dst⟩ := by
      simp [BAScost_imgE, hp1.1, hp1.2, hwf1]
    have e2 : BAScost_imgE Γ q.1 = ⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.src⟩ := by
      simp [BAScost_imgE, hq1.1, hq1.2, hwf2, hvv]
    rw [List.map_cons, List.map_cons, e1, e2] at h4
    exact h4
  have hLL := scostLL_moveSC (promoteC Γ).merge (q.2.map (BAScost_imgE Γ)) ((promoteC Γ).vmap p.1.src)
    ((promoteC Γ).vmap q.1.src) ((promoteC Γ).vmap p.1.dst) hu (BAScost_vmap_ne_of_sameAtom Γ hwf1) hperm
  have hmdx : atomSetoid (BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)]
      [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst)])
      (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  have hker := fun u v h => BAScost_ker_psi1 Γ p.1.src _ ((atomSetoid _).symm hmdx)
    (fun u v h => BAScost_atomSetoid_ext Γ q.2 _ _ _ h) u v h
  refine BAScostLL_of_band Γ _ _ hLL (BAScost_psi1 Γ p.1.src) (BAScost_psi1_surj Γ _)
    (fun a => BAScost_psi1_inl Γ _ a) hker ?_
  intro s'' hadm
  refine BAScost_scost_le_of_Up _ _ s'' ?_ ?_
  · rw [BAScost_ext_relabel_solid, BAScost_lwPrimMoveSC_solid, List.map_map]
    refine BAScost_Up.append s'' (BAScost_Up_old (k := 2) Γ q.2 _ [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst)] (BAScost_psi1 Γ p.1.src) (owxEmb 1)
      (BAScost_psi1_emb Γ p.1.src) s'') ?_
    refine BAScost_Up.cons s'' _ _ (BAScost_Up.cons s'' _ _ (BAScost_Up.refl s'' []) rfl ?_ ?_ (fun h => ?_)) rfl ?_ ?_
      (fun h => ?_)
    · simp [BAScost_psi1_beta, bpS, bpv]
    · simp [bpS, bpv, BAScost_psi1_emb]
    · simp at h
    · simp [bpS, bpv, BAScost_psi1_emb]
    · simp [BAScost_psi1_beta, bpS, bpv]
    · simp at h
  · rw [BAScost_ext_relabel_waved_length, BAScost_lwPrimMoveSC_waved_length, BAScost_img_waved_length]
    rfl

end ShapeMoveSC

/-! ## 13. `E1` and `E2` as corollaries -/

end RBM.Graph
