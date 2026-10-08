/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExpandW

/-!
# BA-L2b2: the order bookkeeping of `lanlw` as a graph operation (T2315)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:353-372` (cited `B:line`; `(eq:ordG_BA)`
at `B:353`, `lanlw` = `(eq:BE)` at `B:361-363`).  Second cut of BA-L2b (DECISIONS §129 (1)): the
vocabulary `lanlwT1`, `lanlwD`, `lanlwTerms` is `Graph/BAExpandW` (T2303); this file is target 3(c)
of its draft.

## Contents (namespace `RBM.Graph`, private prefix `BAExpandWOrd_`)

1. Generic closure lemmas (classes of a symmetric relation under a pendant extension, the count of
   internal classes) and the monotonicity of `n_A` under added `M`-dotted edges.
2. **Targets 1, 2**: `lanlwT1_counters`, `lanlwD_counters` (raw counters
   `⟨n_S+1, n_W+1, n_A+1, n_M, 0, 0⟩`, for every graph, normal or not) and `lanlw_ord` (`ord` goes
   up by one).
3. **Target 3**: `lanlw_scalingOrderG` (`ord Γ ≤ ordG Δ` for every term `Δ` of `lanlw`, `Γ` normal;
   tight).
4. Compiled instances (`RBM.Graph.BAExpandWOrdInst`): (I3) `lanlwT1 baGcxy`, (I4) `lanlwT1 baGcxx`,
   the tight derivative term `T2315_D` (on `Ǧ_{y'x} Ǧ_{xy}`, `ordG = ord Γ`), and one application of
   each of the targets at `baGcxy` and at `baGGLhs`.

Counting the atoms and molecules of the extension (`BAExpandWOrd_ext`: `Γ` renamed by `owxEmb 2`,
the waved edge `S_{αβ}` and the `M`-dotted edge `M_{xα}` added) is done by one generic
classification of the classes of a relation under a pendant extension (`BAExpandWOrd_rtg_ext`,
`BAExpandWOrd_cnt_ext`); the monotonicity of `n_A` under added `M`-dotted edges
(`BAExpandWOrd_nA_le`, `BAExpandWOrd_nA_lt`, injections of internal atoms) gives `κ ≥ 0`, and
`κ ≥ 1` when the singleton atom `{β}` is merged.
The private closure lemmas of `BAVocab` are re-proved locally (DECISIONS §57 (1)).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Graph

/-! ## 1. Generic closure lemmas -/

section Generic

private theorem BAExpandWOrd_rtg_symm {α : Type*} (r : α → α → Bool) (hs : ∀ u v, r u v = r v u) {v w : α}
    (h : Relation.ReflTransGen (fun a b => r a b = true) v w) :
    Relation.ReflTransGen (fun a b => r a b = true) w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (by rw [hs]; exact hbc) ih

/-- The classes of a relation `r'` that extends `r` by pendant vertices (`ρ` retracts the new vertices onto old
ones; the vertices with `¬ P` are isolated): `v ~ w` iff `v = w` or both are `P` and `ρ v ~ ρ w` in `r`. -/
private theorem BAExpandWOrd_rtg_ext {V V' : Type*} (r : V → V → Bool) (r' : V' → V' → Bool)
    (hs' : ∀ u v, r' u v = r' v u) (emb : V → V') (ρ : V' → V) (P : V' → Prop)
    (e1 : ∀ u w, r u w = true → r' (emb u) (emb w) = true)
    (e2 : ∀ b c, r' b c = true → P b ∧ P c ∧ (ρ b = ρ c ∨ r (ρ b) (ρ c) = true))
    (e3 : ∀ w, P w → Relation.ReflTransGen (fun a b => r' a b = true) w (emb (ρ w))) (v w : V') :
    Relation.ReflTransGen (fun a b => r' a b = true) v w ↔
      v = w ∨ (P v ∧ P w ∧ Relation.ReflTransGen (fun a b => r a b = true) (ρ v) (ρ w)) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      obtain ⟨hPb, hPc, hbc'⟩ := e2 b c hbc
      rcases ih with rfl | ⟨hPv, _, hrt⟩
      · right
        refine ⟨hPb, hPc, ?_⟩
        rcases hbc' with h | h
        · rw [h]
        · exact Relation.ReflTransGen.single h
      · right
        refine ⟨hPv, hPc, ?_⟩
        rcases hbc' with h | h
        · rw [← h]; exact hrt
        · exact hrt.tail h
  · rintro (rfl | ⟨hPv, hPw, h⟩)
    · exact Relation.ReflTransGen.refl
    · have h1 : Relation.ReflTransGen (fun a b => r' a b = true) (emb (ρ v)) (emb (ρ w)) :=
        Relation.ReflTransGen.lift emb (fun a b hab => e1 a b hab) _ _ h
      exact (e3 v hPv).trans (h1.trans (BAExpandWOrd_rtg_symm r' hs' (e3 w hPw)))

/-- The number of classes without a "bad" element (the shape of `BAGraph.nA`, `BAGraph.nM`). -/
private def BAExpandWOrd_cnt {V : Type*} [Fintype V] [DecidableEq V] (i : V → Bool) (cl : V → Finset V) : ℕ :=
  ((Finset.univ.filter (fun v : V => ∀ w ∈ cl v, i w = true)).image cl).card

/-- The count of internal classes of a pendant extension: the classes of `cl'` are the `G`-images of the classes
of `cl` and the singletons of the isolated vertices. -/
private theorem BAExpandWOrd_cnt_ext {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (i : V → Bool) (i' : V' → Bool) (cl : V → Finset V) (cl' : V' → Finset V') (emb : V → V') (ρ : V' → V)
    (P : V' → Prop) [DecidablePred P] (hρ : ∀ a, ρ (emb a) = a) (hi1 : ∀ a, i' (emb a) = i a)
    (hi2 : ∀ w, i (ρ w) = true → i' w = true) (hP1 : ∀ a, P (emb a)) (hP2 : ∀ w, ¬ P w → i' w = true)
    (hself : ∀ v, v ∈ cl v)
    (hcl : ∀ v w, w ∈ cl' v ↔ w = v ∨ (P v ∧ P w ∧ ρ w ∈ cl (ρ v))) :
    BAExpandWOrd_cnt i' cl' = BAExpandWOrd_cnt i cl + (Finset.univ.filter (fun w => ¬ P w)).card := by
  classical
  unfold BAExpandWOrd_cnt
  set G : Finset V → Finset V' := fun A => Finset.univ.filter (fun w => P w ∧ ρ w ∈ A) with hG
  have h1 : ∀ v, ¬ P v → cl' v = {v} := by
    intro v hv
    ext w
    rw [hcl]
    simp [hv]
  have h2 : ∀ v, P v → cl' v = G (cl (ρ v)) := by
    intro v hv
    ext w
    rw [hcl]
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨_, hw, h⟩)
      · exact ⟨hv, hself _⟩
      · exact ⟨hw, h⟩
    · rintro ⟨hw, h⟩
      exact Or.inr ⟨hv, hw, h⟩
  have hGinj : Function.Injective G := by
    intro A A' h
    have hA : ∀ B : Finset V, B = (G B).image ρ := by
      intro B
      ext a
      simp only [hG, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ha
        exact ⟨emb a, ⟨hP1 a, by rw [hρ]; exact ha⟩, hρ a⟩
      · rintro ⟨w, ⟨_, hw⟩, rfl⟩
        exact hw
    rw [hA A, hA A', h]
  have himg : (Finset.univ.filter (fun v : V' => ∀ w ∈ cl' v, i' w = true)).image cl' =
      ((Finset.univ.filter (fun v : V => ∀ w ∈ cl v, i w = true)).image cl).image G ∪
        ((Finset.univ.filter (fun w => ¬ P w)).image fun v => ({v} : Finset V')) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨v, hv, rfl⟩
      by_cases hPv : P v
      · left
        refine ⟨cl (ρ v), ⟨ρ v, ?_, rfl⟩, (h2 v hPv).symm⟩
        intro a ha
        have : emb a ∈ cl' v := by
          rw [h2 v hPv]
          simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hP1 a, by rw [hρ]; exact ha⟩
        have := hv _ this
        rwa [hi1] at this
      · right
        exact ⟨v, hPv, (h1 v hPv).symm⟩
    · rintro (⟨_, ⟨u, hu, rfl⟩, rfl⟩ | ⟨v, hv, rfl⟩)
      · refine ⟨emb u, ?_, ?_⟩
        · intro w hw
          rw [h2 _ (hP1 u), hρ] at hw
          simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          exact hi2 w (hu _ hw.2)
        · rw [h2 _ (hP1 u), hρ]
      · refine ⟨v, ?_, h1 v hv⟩
        intro w hw
        rw [h1 v hv] at hw
        rw [Finset.mem_singleton.1 hw]
        exact hP2 v hv
  rw [himg, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ hGinj,
    Finset.card_image_of_injective _ Finset.singleton_injective]
  rw [Finset.disjoint_left]
  intro T hT1 hT2
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.1 hT1
  obtain ⟨v, hv, hvT⟩ := Finset.mem_image.1 hT2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have : v ∈ G A := by rw [← hvT]; exact Finset.mem_singleton_self v
  simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact hv this.1

end Generic

section AtomMono

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAExpandWOrd_atomAdj_comm (Γ : BAGraph E I) (u v : E ⊕ I) :
    Γ.atomAdj u v = Γ.atomAdj v u := by
  simp only [BAGraph.atomAdj, or_comm]

private theorem BAExpandWOrd_adj_comm (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.adj u v = Γ.adj v u := by
  simp only [BAGraph.adj, BAExpandWOrd_atomAdj_comm Γ u v, LGraph.adj, or_comm]

private theorem BAExpandWOrd_self_mem_atom (Γ : BAGraph E I) (v : E ⊕ I) : v ∈ Γ.atom v := by
  rw [BAGraph.mem_atom_iff]

private theorem BAExpandWOrd_atom_eq_of_mem (Γ : BAGraph E I) {v w : E ⊕ I} (h : w ∈ Γ.atom v) :
    Γ.atom w = Γ.atom v := by
  rw [BAGraph.mem_atom_iff] at h
  ext x
  rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx
    exact (BAExpandWOrd_rtg_symm (fun a b => Γ.atomAdj a b) (BAExpandWOrd_atomAdj_comm Γ) h).trans hx

/-- Adding atom edges makes the atoms bigger. -/
private theorem BAExpandWOrd_atom_subset (Γ₁ Γ₂ : BAGraph E I)
    (h : ∀ u v, Γ₁.atomAdj u v = true → Γ₂.atomAdj u v = true) (v : E ⊕ I) : Γ₁.atom v ⊆ Γ₂.atom v := by
  intro w hw
  rw [BAGraph.mem_atom_iff] at hw ⊢
  exact Relation.ReflTransGen.mono (fun a b hab => h a b hab) _ _ hw

/-- **Adding `=`-, `Ψ`- or `M`-dotted edges never increases `n_A`** (merging two atoms never creates an internal
one). -/
private theorem BAExpandWOrd_nA_le (Γ₁ Γ₂ : BAGraph E I)
    (h : ∀ u v, Γ₁.atomAdj u v = true → Γ₂.atomAdj u v = true) : Γ₂.nA ≤ Γ₁.nA := by
  classical
  unfold BAGraph.nA
  set F : Finset (E ⊕ I) → Finset (E ⊕ I) := fun A =>
    if hA : A.Nonempty then Γ₂.atom hA.choose else ∅ with hF
  have hsub : (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₂.atom v, w.isRight = true)).image Γ₂.atom ⊆
      ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₁.atom v, w.isRight = true)).image Γ₁.atom).image F := by
    intro T hT
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine Finset.mem_image.2 ⟨Γ₁.atom v, Finset.mem_image.2 ⟨v, ?_, rfl⟩, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun w hw => hv w (BAExpandWOrd_atom_subset Γ₁ Γ₂ h v hw)
    · have hne : (Γ₁.atom v).Nonempty := ⟨v, BAExpandWOrd_self_mem_atom Γ₁ v⟩
      simp only [hF, hne, ↓reduceDIte]
      exact BAExpandWOrd_atom_eq_of_mem Γ₂ (BAExpandWOrd_atom_subset Γ₁ Γ₂ h v hne.choose_spec)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- **A singleton internal atom `{b}` that is joined to another vertex loses one internal atom.** -/
private theorem BAExpandWOrd_nA_lt (Γ₁ Γ₂ : BAGraph E I)
    (h : ∀ u v, Γ₁.atomAdj u v = true → Γ₂.atomAdj u v = true) (b : E ⊕ I) (hb : b.isRight = true)
    (hiso : ∀ w, Γ₁.atomAdj b w = false) (u : E ⊕ I) (hu : u ≠ b) (hbu : Γ₂.atomAdj b u = true) :
    Γ₂.nA + 1 ≤ Γ₁.nA := by
  classical
  have hb1 : Γ₁.atom b = {b} := by
    ext w
    rw [BAGraph.mem_atom_iff, Finset.mem_singleton]
    constructor
    · intro hw
      induction hw with
      | refl => rfl
      | @tail b' c _ hbc ih =>
        subst ih
        rw [hiso c] at hbc
        exact absurd hbc (by simp)
    · rintro rfl; exact Relation.ReflTransGen.refl
  unfold BAGraph.nA
  set IA₁ := (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₁.atom v, w.isRight = true)).image Γ₁.atom with hIA₁
  have hbmem : ({b} : Finset (E ⊕ I)) ∈ IA₁ := by
    rw [hIA₁, Finset.mem_image]
    refine ⟨b, ?_, hb1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro w hw
    rw [hb1, Finset.mem_singleton] at hw
    rw [hw]; exact hb
  set F : Finset (E ⊕ I) → Finset (E ⊕ I) := fun A =>
    if hA : A.Nonempty then Γ₂.atom hA.choose else ∅ with hF
  have hsub : (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₂.atom v, w.isRight = true)).image Γ₂.atom ⊆
      (IA₁.erase {b}).image F := by
    intro T hT
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    set a : E ⊕ I := if v = b then u else v with ha
    have haT : a ∈ Γ₂.atom v := by
      by_cases hvb : v = b
      · subst hvb
        simp only [ha, ↓reduceIte]
        rw [BAGraph.mem_atom_iff]
        exact Relation.ReflTransGen.single hbu
      · simp only [ha, hvb, ↓reduceIte]; exact BAExpandWOrd_self_mem_atom Γ₂ v
    have hab : a ≠ b := by
      by_cases hvb : v = b
      · simp only [ha, hvb, ↓reduceIte]; exact hu
      · simp only [ha, hvb, ↓reduceIte]; exact hvb
    have hsubT : Γ₁.atom a ⊆ Γ₂.atom v := by
      intro w hw
      have := BAExpandWOrd_atom_subset Γ₁ Γ₂ h a hw
      rwa [BAExpandWOrd_atom_eq_of_mem Γ₂ haT] at this
    refine Finset.mem_image.2 ⟨Γ₁.atom a, Finset.mem_erase.2 ⟨?_, Finset.mem_image.2 ⟨a, ?_, rfl⟩⟩, ?_⟩
    · intro hAb
      have := BAExpandWOrd_self_mem_atom Γ₁ a
      rw [hAb, Finset.mem_singleton] at this
      exact hab this
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun w hw => hv w (hsubT hw)
    · have hne : (Γ₁.atom a).Nonempty := ⟨a, BAExpandWOrd_self_mem_atom Γ₁ a⟩
      simp only [hF, hne, ↓reduceDIte]
      exact BAExpandWOrd_atom_eq_of_mem Γ₂ (hsubT hne.choose_spec)
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 := Finset.card_erase_of_mem hbmem
  have h3 : 0 < IA₁.card := Finset.card_pos.2 ⟨_, hbmem⟩
  omega

end AtomMono

/-! ## 2. The extension graph of `lanlw` -/

section ExtGraph

variable {E I : Type}

/-- `α = inr (inr 0)`, `β = inr (inr 1)`. -/
private abbrev BAExpandWOrd_α : E ⊕ (I ⊕ Fin 2) := Sum.inr (Sum.inr 0)
private abbrev BAExpandWOrd_β : E ⊕ (I ⊕ Fin 2) := Sum.inr (Sum.inr 1)

/-- The shape common to term 1 and every derivative term of `lanlw`: `Γ` renamed by `owxEmb 2`, its solid edges
replaced by `rest`, the solid edges `s`, the waved edge `S_{αβ}` and the `M`-dotted edge `M_{xα}` appended. -/
private def BAExpandWOrd_ext (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.lanlwExt Γ rest 1 s [⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]
    [⟨true, owxEmb 2 x, Sum.inr (Sum.inr 0)⟩]

private theorem BAExpandWOrd_lanlwT1_eq (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGraph.lanlwT1 Γ p = BAExpandWOrd_ext Γ p.2
      [⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩,
        ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 2 p.1.dst⟩] p.1.src := rfl

private theorem BAExpandWOrd_lanlwD_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGraph.lanlwD Γ p q = BAExpandWOrd_ext Γ q.2
      [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).1,
        (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).2,
        ⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 p.1.dst⟩] p.1.src := rfl

/-- The retraction of the vertices of the extension: `α`, `β` go to `x`. -/
private def BAExpandWOrd_rho (x : E ⊕ I) : E ⊕ (I ⊕ Fin 2) → E ⊕ I
  | Sum.inl e => Sum.inl e
  | Sum.inr (Sum.inl i) => Sum.inr i
  | Sum.inr (Sum.inr _) => x

private theorem BAExpandWOrd_rho_emb (x : E ⊕ I) (a : E ⊕ I) : BAExpandWOrd_rho x (owxEmb 2 a) = a := by
  rcases a with a | a <;> rfl

variable [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The atom edges of the extension: those of `Γ` (renamed) and `M_{xα}`. -/
private theorem BAExpandWOrd_ext_atomAdj (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) (u v : E ⊕ (I ⊕ Fin 2)) :
    (BAExpandWOrd_ext Γ rest s x).atomAdj u v = true ↔
      (∃ a b, u = owxEmb 2 a ∧ v = owxEmb 2 b ∧ Γ.atomAdj a b = true) ∨
        (u = owxEmb 2 x ∧ v = Sum.inr (Sum.inr 0)) ∨ (u = Sum.inr (Sum.inr 0) ∧ v = owxEmb 2 x) := by
  simp only [BAGraph.atomAdj, BAExpandWOrd_ext, BAGraph.lanlwExt, LGraph.owxExt, Bool.or_eq_true,
    List.any_eq_true, List.mem_map, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro (((⟨_, ⟨a, ha, rfl⟩, h1, h2⟩ | ⟨_, ⟨a, ha, rfl⟩, h2⟩) | ⟨e, h1 | ⟨a, ha, rfl⟩, h2⟩))
    · left
      simp only [DEdge.map] at h1 h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inl (Or.inl ⟨a, ha, h1, Or.inl ⟨rfl, rfl⟩⟩)⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inl (Or.inl ⟨a, ha, h1, Or.inr ⟨rfl, rfl⟩⟩)⟩
    · left
      simp only [BAPsiEdge.map] at h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inl (Or.inr ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩)⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inl (Or.inr ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩)⟩
    · subst h1
      right
      rcases h2 with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact Or.inl ⟨h2.symm, h3.symm⟩
      · exact Or.inr ⟨h3.symm, h2.symm⟩
    · left
      simp only [BAMEdge.map] at h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inr ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inr ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro (⟨a, b, rfl, rfl, ((⟨e, he, h1, h2⟩ | ⟨e, he, h2⟩) | ⟨e, he, h2⟩)⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · left; left
      refine ⟨DEdge.map (owxEmb 2) e, ⟨e, he, rfl⟩, h1, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · left; right
      refine ⟨BAPsiEdge.map (owxEmb 2) e, ⟨e, he, rfl⟩, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · right
      refine ⟨BAMEdge.map (owxEmb 2) e, Or.inr ⟨e, he, rfl⟩, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · right
      exact ⟨_, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
    · right
      exact ⟨_, Or.inl rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- The waved and `=`-dotted edges of the extension: those of `Γ` (renamed) and `S_{αβ}`. -/
private theorem BAExpandWOrd_ext_ladj (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) (u v : E ⊕ (I ⊕ Fin 2)) :
    (BAExpandWOrd_ext Γ rest s x).toLGraph.adj u v = true ↔
      (∃ a b, u = owxEmb 2 a ∧ v = owxEmb 2 b ∧ Γ.toLGraph.adj a b = true) ∨
        (u = Sum.inr (Sum.inr 0) ∧ v = Sum.inr (Sum.inr 1)) ∨ (u = Sum.inr (Sum.inr 1) ∧ v = Sum.inr (Sum.inr 0)) := by
  simp only [LGraph.adj, BAExpandWOrd_ext, BAGraph.lanlwExt, LGraph.owxExt, Bool.or_eq_true,
    List.any_eq_true, List.mem_map, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ((⟨e, ⟨a, ha, rfl⟩ | h1, h2⟩) | ⟨_, ⟨a, ha, rfl⟩, h1, h2⟩)
    · left
      simp only [WEdge.map] at h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inl ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inl ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩⟩
    · subst h1
      right
      rcases h2 with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact Or.inl ⟨h2.symm, h3.symm⟩
      · exact Or.inr ⟨h3.symm, h2.symm⟩
    · left
      simp only [DEdge.map] at h1 h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inr ⟨a, ha, h1, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inr ⟨a, ha, h1, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro (⟨a, b, rfl, rfl, (⟨e, he, h2⟩ | ⟨e, he, h1, h2⟩)⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · left
      refine ⟨WEdge.map (owxEmb 2) e, Or.inl ⟨e, he, rfl⟩, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · right
      refine ⟨DEdge.map (owxEmb 2) e, ⟨e, he, rfl⟩, h1, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · left
      exact ⟨_, Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩
    · left
      exact ⟨_, Or.inr rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- The molecule edges of the extension: those of `Γ` (renamed), `S_{αβ}` and `M_{xα}`. -/
private theorem BAExpandWOrd_ext_adj (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) (u v : E ⊕ (I ⊕ Fin 2)) :
    (BAExpandWOrd_ext Γ rest s x).adj u v = true ↔
      (∃ a b, u = owxEmb 2 a ∧ v = owxEmb 2 b ∧ Γ.adj a b = true) ∨
        (u = Sum.inr (Sum.inr 0) ∧ v = Sum.inr (Sum.inr 1)) ∨ (u = Sum.inr (Sum.inr 1) ∧ v = Sum.inr (Sum.inr 0)) ∨
        (u = owxEmb 2 x ∧ v = Sum.inr (Sum.inr 0)) ∨ (u = Sum.inr (Sum.inr 0) ∧ v = owxEmb 2 x) := by
  simp only [BAGraph.adj, Bool.or_eq_true, BAExpandWOrd_ext_ladj, BAExpandWOrd_ext_atomAdj]
  constructor
  · rintro ((⟨a, b, h1, h2, h3⟩ | h) | (⟨a, b, h1, h2, h3⟩ | h))
    · exact Or.inl ⟨a, b, h1, h2, Or.inl h3⟩
    · rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl ⟨a, b, h1, h2, Or.inr h3⟩
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (⟨a, b, h1, h2, h3 | h3⟩ | h)
    · exact Or.inl (Or.inl ⟨a, b, h1, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨a, b, h1, h2, h3⟩)
    · rcases h with h | h | h
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr h)

private theorem BAExpandWOrd_isRight_emb (a : E ⊕ I) : (owxEmb 2 a : E ⊕ (I ⊕ Fin 2)).isRight = a.isRight := by
  rcases a with a | a <;> rfl

private theorem BAExpandWOrd_isRight_rho (x : E ⊕ I) (w : E ⊕ (I ⊕ Fin 2))
    (h : (BAExpandWOrd_rho x w).isRight = true) : w.isRight = true := by
  rcases w with e | i | j
  · simp [BAExpandWOrd_rho] at h
  · rfl
  · rfl

private theorem BAExpandWOrd_emb_ne_β (a : E ⊕ I) :
    (owxEmb 2 a : E ⊕ (I ⊕ Fin 2)) ≠ Sum.inr (Sum.inr 1) := by
  rcases a with a | a <;> simp [owxEmb]

/-- **`n_A` of the extension is `n_A Γ + 1`**: `β` is a new singleton internal atom, `α` joins the atom of `x`. -/
private theorem BAExpandWOrd_ext_nA (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) :
    (BAExpandWOrd_ext Γ rest s x).nA = Γ.nA + 1 := by
  have key := BAExpandWOrd_cnt_ext (fun w : E ⊕ I => w.isRight) (fun w : E ⊕ (I ⊕ Fin 2) => w.isRight) Γ.atom
    (BAExpandWOrd_ext Γ rest s x).atom (owxEmb 2) (BAExpandWOrd_rho x)
    (fun w => w ≠ Sum.inr (Sum.inr 1)) (BAExpandWOrd_rho_emb x) BAExpandWOrd_isRight_emb
    (BAExpandWOrd_isRight_rho x) BAExpandWOrd_emb_ne_β (fun w hw => by
      have : w = Sum.inr (Sum.inr 1) := not_not.1 hw
      subst this; rfl) (BAExpandWOrd_self_mem_atom Γ) (fun v w => by
      rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
      rw [BAExpandWOrd_rtg_ext (fun a b => Γ.atomAdj a b) (fun a b => (BAExpandWOrd_ext Γ rest s x).atomAdj a b)
        (BAExpandWOrd_atomAdj_comm _) (owxEmb 2) (BAExpandWOrd_rho x) (fun w => w ≠ Sum.inr (Sum.inr 1))
        (fun u w h => (BAExpandWOrd_ext_atomAdj Γ rest s x _ _).2 (Or.inl ⟨u, w, rfl, rfl, h⟩))
        ?_ ?_ v w]
      · rw [eq_comm]
      · intro b c h
        rcases (BAExpandWOrd_ext_atomAdj Γ rest s x _ _).1 h with ⟨a, a', rfl, rfl, h'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨BAExpandWOrd_emb_ne_β a, BAExpandWOrd_emb_ne_β a', Or.inr (by
            rw [BAExpandWOrd_rho_emb, BAExpandWOrd_rho_emb]; exact h')⟩
        · exact ⟨BAExpandWOrd_emb_ne_β x, by simp, Or.inl (by rw [BAExpandWOrd_rho_emb]; rfl)⟩
        · exact ⟨by simp, BAExpandWOrd_emb_ne_β x, Or.inl (by rw [BAExpandWOrd_rho_emb]; rfl)⟩
      · intro w hw
        rcases w with e | i | j
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.refl
        · have hj : j = 0 := by
            fin_cases j
            · rfl
            · exact absurd rfl hw
          subst hj
          refine Relation.ReflTransGen.single ((BAExpandWOrd_ext_atomAdj Γ rest s x _ _).2
            (Or.inr (Or.inr ⟨rfl, ?_⟩)))
          rfl)
  have hc : (Finset.univ.filter fun w : E ⊕ (I ⊕ Fin 2) => ¬ w ≠ Sum.inr (Sum.inr 1)) =
      {Sum.inr (Sum.inr 1)} := by
    ext w; simp
  rw [hc, Finset.card_singleton] at key
  exact key

/-- **`n_M` of the extension is `n_M Γ`**: `α` and `β` join the molecule of `x`. -/
private theorem BAExpandWOrd_ext_nM (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) :
    (BAExpandWOrd_ext Γ rest s x).nM = Γ.nM := by
  have key := BAExpandWOrd_cnt_ext (fun w : E ⊕ I => w.isRight) (fun w : E ⊕ (I ⊕ Fin 2) => w.isRight) Γ.mol
    (BAExpandWOrd_ext Γ rest s x).mol (owxEmb 2) (BAExpandWOrd_rho x)
    (fun _ => True) (BAExpandWOrd_rho_emb x) BAExpandWOrd_isRight_emb
    (BAExpandWOrd_isRight_rho x) (fun _ => trivial) (fun w hw => absurd trivial hw)
    (fun v => by rw [BAGraph.mem_mol_iff]) (fun v w => by
      rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
      rw [BAExpandWOrd_rtg_ext (fun a b => Γ.adj a b) (fun a b => (BAExpandWOrd_ext Γ rest s x).adj a b)
        (BAExpandWOrd_adj_comm _) (owxEmb 2) (BAExpandWOrd_rho x) (fun _ => True)
        (fun u w h => (BAExpandWOrd_ext_adj Γ rest s x _ _).2 (Or.inl ⟨u, w, rfl, rfl, h⟩))
        ?_ ?_ v w]
      · rw [eq_comm]
      · intro b c h
        refine ⟨trivial, trivial, ?_⟩
        rcases (BAExpandWOrd_ext_adj Γ rest s x _ _).1 h with ⟨a, a', rfl, rfl, h'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (by rw [BAExpandWOrd_rho_emb, BAExpandWOrd_rho_emb]; exact h')
        · exact Or.inl rfl
        · exact Or.inl rfl
        · exact Or.inl (by rw [BAExpandWOrd_rho_emb]; rfl)
        · exact Or.inl (by rw [BAExpandWOrd_rho_emb]; rfl)
      · intro w _
        have hα : Relation.ReflTransGen (fun a b => (BAExpandWOrd_ext Γ rest s x).adj a b = true)
            (Sum.inr (Sum.inr 0)) (owxEmb 2 x) :=
          Relation.ReflTransGen.single ((BAExpandWOrd_ext_adj Γ rest s x _ _).2
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
        rcases w with e | i | j
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.refl
        · fin_cases j
          · exact hα
          · exact Relation.ReflTransGen.head ((BAExpandWOrd_ext_adj Γ rest s x _ _).2
              (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hα)
  have hc : (Finset.univ.filter fun w : E ⊕ (I ⊕ Fin 2) => ¬ True) = ∅ := by
    ext w; simp
  rw [hc, Finset.card_empty, Nat.add_zero] at key
  exact key

private theorem BAExpandWOrd_ext_nS (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) :
    (BAExpandWOrd_ext Γ rest s x).nS = rest.length + s.length := by
  simp [BAGraph.nS, BAExpandWOrd_ext, BAGraph.lanlwExt, LGraph.owxExt]

private theorem BAExpandWOrd_ext_nW (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) :
    (BAExpandWOrd_ext Γ rest s x).nW = Γ.nW + 1 := by
  simp [BAGraph.nW, BAExpandWOrd_ext, BAGraph.lanlwExt, LGraph.owxExt]

/-- The raw counters of the extension. -/
private theorem BAExpandWOrd_ext_counters (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) :
    (BAExpandWOrd_ext Γ rest s x).counters = ⟨rest.length + s.length, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩ := by
  simp only [BAGraph.counters, BAExpandWOrd_ext_nS, BAExpandWOrd_ext_nW, BAExpandWOrd_ext_nA,
    BAExpandWOrd_ext_nM]

/-- Term-by-term bookkeeping of `G = Ǧ + M`: if the split of the extension `Δ` has `ms` as its new `M`-dotted
edges (`r1` its solid edges, `|r1| + |ms| = n_S(Δ)`), then `ord ≥ ord Γ` as soon as `|ms| ≤ 1`, or `|ms| ≤ 3` and one
of the new `M`-edges joins `β` (a singleton internal atom of `Δ`) to another vertex.  (`ord Δ_s = ord Γ + 1 - |ms| + 2κ`,
`κ = n_A(Δ) - n_A(Δ_s) ≥ 0`, and `κ ≥ 1` in the second case; T2295-prove (a) rows 14-15.) -/
private theorem BAExpandWOrd_core (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) (r1 : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (ms : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) (hS : rest.length + s.length = Γ.nS + 1)
    (hlen : r1.length + ms.length = rest.length + s.length)
    (hms : ms.length ≤ 1 ∨ (ms.length ≤ 3 ∧ ∃ m ∈ ms, (m.x = Sum.inr (Sum.inr 1) ∧ m.y ≠ Sum.inr (Sum.inr 1)) ∨
        (m.y = Sum.inr (Sum.inr 1) ∧ m.x ≠ Sum.inr (Sum.inr 1)))) :
    ord Γ.counters ≤ ord (BAGraph.mk (LGraph.mk r1 (BAExpandWOrd_ext Γ rest s x).waved
      (BAExpandWOrd_ext Γ rest s x).dotted (BAExpandWOrd_ext Γ rest s x).coeff)
      (BAExpandWOrd_ext Γ rest s x).psi (ms ++ (BAExpandWOrd_ext Γ rest s x).mdot)).counters := by
  set Δ := BAExpandWOrd_ext Γ rest s x with hΔ
  set Δs : BAGraph E (I ⊕ Fin 2) := BAGraph.mk (LGraph.mk r1 Δ.waved Δ.dotted Δ.coeff) Δ.psi
    (ms ++ Δ.mdot) with hΔs
  have hrefine : ∀ u v, Δ.atomAdj u v = true → Δs.atomAdj u v = true := by
    intro u v h
    simp only [hΔs, BAGraph.atomAdj, List.any_append] at h ⊢
    revert h
    simp only [Bool.or_eq_true]
    tauto
  have hle : Δs.nA ≤ Δ.nA := BAExpandWOrd_nA_le Δ Δs hrefine
  have hnA : Δ.nA = Γ.nA + 1 := BAExpandWOrd_ext_nA Γ rest s x
  have hnW : Δ.nW = Γ.nW + 1 := BAExpandWOrd_ext_nW Γ rest s x
  have hκ : ms.length ≤ 1 ∨ Δs.nA + 1 ≤ Δ.nA := by
    rcases hms with h | ⟨_, m, hm, h⟩
    · exact Or.inl h
    · right
      have hiso : ∀ w, Δ.atomAdj (Sum.inr (Sum.inr 1)) w = false := by
        intro w
        by_contra h'
        have h'' : Δ.atomAdj (Sum.inr (Sum.inr 1)) w = true := by simpa using h'
        rcases (BAExpandWOrd_ext_atomAdj Γ rest s x _ _).1 h'' with ⟨a, b, h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact BAExpandWOrd_emb_ne_β a h1.symm
        · exact BAExpandWOrd_emb_ne_β x h1.symm
        · simp at h1
      have hmem : ∀ u v, ((m.x = u ∧ m.y = v) ∨ (m.x = v ∧ m.y = u)) → Δs.atomAdj u v = true := by
        intro u v h
        simp only [hΔs, BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, List.mem_append]
        right
        exact ⟨m, Or.inl hm, by simpa using h⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact BAExpandWOrd_nA_lt Δ Δs hrefine _ rfl hiso m.y h2 (hmem _ _ (Or.inl ⟨h1, rfl⟩))
      · exact BAExpandWOrd_nA_lt Δ Δs hrefine _ rfl hiso m.x h2 (hmem _ _ (Or.inr ⟨rfl, h1⟩))
  have hc : Δs.counters = ⟨r1.length, Δ.nW, Δs.nA, Δs.nM, 0, 0⟩ := rfl
  rw [hc]
  simp only [ord, BAGraph.counters]
  rcases hκ with h | h <;> omega

/-- Splitting `G = Ǧ + M` after circled edges: only the later edges are split (the BA twin of the private
`BAVocab_baSplitSolid_circ`). -/
private theorem BAExpandWOrd_split_append {V : Type*} (l t : List (SEdge V)) (hl : ∀ e ∈ l, e.circ = true) :
    baSplitSolid (l ++ t) = (baSplitSolid t).map fun r => (l ++ r.1, r.2) := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have he := hl e List.mem_cons_self
    have := ih (fun e' h => hl e' (List.mem_cons_of_mem _ h))
    simp [baSplitSolid, this, he, List.flatMap_map]
    exact List.map_eq_flatMap.symm

/-- A graph with only circled solid edges is its own `splitG`. -/
private theorem BAExpandWOrd_splitG_of_circ {E' I' : Type} (Δ : BAGraph E' I') (h : ∀ e ∈ Δ.solid, e.circ = true) :
    Δ.splitG = [Δ] := by
  have key : ∀ es : List (SEdge (E' ⊕ I')), (∀ e ∈ es, e.circ = true) → baSplitSolid es = [(es, [])] := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons e es ih =>
      intro hh
      simp [baSplitSolid, ih fun e' he' => hh e' (List.mem_cons_of_mem _ he'), hh e List.mem_cons_self]
  unfold BAGraph.splitG
  rw [key Δ.solid h]
  obtain ⟨⟨s, w, d, c⟩, p, m⟩ := Δ
  rfl

/-- The packed merge of a normal graph has its counters. -/
private theorem BAExpandWOrd_packMerge_counters {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I']
    [DecidableEq I'] (Δ : BAGraph E' I') (hN : Δ.Normal) : Δ.packMerge.counters = Δ.counters := by
  obtain ⟨P', hP', hc⟩ := Δ.partition_of_normal hN
  have h1 : Δ.partition = [Δ.packMerge] := by
    unfold BAGraph.partition
    rw [BAExpandWOrd_splitG_of_circ Δ hN.2]
    rfl
  rw [h1] at hP'
  rw [List.singleton_inj.1 hP']
  exact hc

/-- The `M`-splits of a circled and a non-circled edge: at most one `M`-edge. -/
private theorem BAExpandWOrd_split2 {V : Type*} (a b : SEdge V) (ha : a.circ = true) (hb : b.circ = false) :
    ∀ r ∈ baSplitSolid [a, b], r.2.length ≤ 1 := by
  intro r hr
  simp only [baSplitSolid, ha, hb, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.mem_nil_iff, or_false, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append] at hr
  rcases hr with rfl | rfl <;> simp

/-- The `M`-splits of three non-circled edges: at most one `M`-edge, or at most three, one of which joins `b` to another
vertex (when `e3` and one of `e1`, `e2` have an end at `b`). -/
private theorem BAExpandWOrd_split3 {V : Type*} (e1 e2 e3 : SEdge V) (h1 : e1.circ = false) (h2 : e2.circ = false)
    (h3 : e3.circ = false) (b : V) (hb : (e3.src = b ∧ e3.dst ≠ b) ∨ (e3.dst = b ∧ e3.src ≠ b))
    (hb' : ((e1.src = b ∧ e1.dst ≠ b) ∨ (e1.dst = b ∧ e1.src ≠ b)) ∨
      ((e2.src = b ∧ e2.dst ≠ b) ∨ (e2.dst = b ∧ e2.src ≠ b))) :
    ∀ r ∈ baSplitSolid [e1, e2, e3], r.2.length ≤ 1 ∨
      (r.2.length ≤ 3 ∧ ∃ m ∈ r.2, (m.x = b ∧ m.y ≠ b) ∨ (m.y = b ∧ m.x ≠ b)) := by
  intro r hr
  simp only [baSplitSolid, h1, h2, h3, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.mem_nil_iff, or_false, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; simp
  · left; simp
  · left; simp
  · right
    refine ⟨by simp, ?_⟩
    rcases hb' with h | h
    · exact ⟨_, List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
  · left; simp
  · right; exact ⟨by simp, _, List.mem_cons_of_mem _ List.mem_cons_self, hb⟩
  · right; exact ⟨by simp, _, List.mem_cons_of_mem _ List.mem_cons_self, hb⟩
  · right; exact ⟨by simp, _, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hb⟩

/-- Every term of `G = Ǧ + M` on the extension of a normal graph is normal and has `ord ≥ ord Γ`, given the three
facts: the old solid edges `rest` carry circles, the solid counts match, and the `M`-splits of the new solid edges `s`
are as in `BAExpandWOrd_core`. -/
private theorem BAExpandWOrd_ext_ge (Γ : BAGraph E I) (hN : Γ.Normal) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) (hrest : ∀ e ∈ rest, e.circ = true)
    (hS : rest.length + s.length = Γ.nS + 1)
    (hsplit : ∀ r ∈ baSplitSolid s, r.2.length ≤ 1 ∨ (r.2.length ≤ 3 ∧ ∃ m ∈ r.2,
      (m.x = Sum.inr (Sum.inr 1) ∧ m.y ≠ Sum.inr (Sum.inr 1)) ∨ (m.y = Sum.inr (Sum.inr 1) ∧ m.x ≠ Sum.inr (Sum.inr 1)))) :
    ∀ Δs ∈ (BAExpandWOrd_ext Γ rest s x).splitG, Δs.Normal ∧ ord Γ.counters ≤ ord Δs.counters := by
  intro Δs hΔs
  set Δ := BAExpandWOrd_ext Γ rest s x with hΔ
  have hedges := BAGraph.splitG_edges Δ Δs hΔs
  refine ⟨⟨?_, BAGraph.splitG_circ Δ Δs hΔs⟩, ?_⟩
  · rw [hedges.2.1]
    intro e he
    simp only [hΔ, BAExpandWOrd_ext, BAGraph.lanlwExt, LGraph.owxExt, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact hN.1 e0 he0
  · have hnS : Δ.nS = rest.length + s.length := BAExpandWOrd_ext_nS Γ rest s x
    simp only [BAGraph.splitG, List.mem_map] at hΔs
    obtain ⟨r, hr, rfl⟩ := hΔs
    have hsol : Δ.solid = rest.map (SEdge.map (owxEmb 2)) ++ s := rfl
    rw [hsol, BAExpandWOrd_split_append _ _ (fun e he => by
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact hrest e0 he0)] at hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    have hlen : (rest.map (SEdge.map (owxEmb 2)) ++ r'.1).length + r'.2.length = rest.length + s.length := by
      have := hedges.2.2.2
      simp only [BAGraph.nS, List.length_append, List.length_map] at this hnS ⊢
      omega
    exact BAExpandWOrd_core Γ rest s x _ r'.2 hS hlen (hsplit r' hr')


/-- The `M`-splits of the three new solid edges of a derivative term. -/
private theorem BAExpandWOrd_D_split (q : SEdge (E ⊕ I)) (y : E ⊕ I) :
    ∀ r ∈ baSplitSolid [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q)).1,
        (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q)).2,
        (⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 y⟩ : SEdge (E ⊕ (I ⊕ Fin 2)))],
      r.2.length ≤ 1 ∨ (r.2.length ≤ 3 ∧ ∃ m ∈ r.2,
        (m.x = Sum.inr (Sum.inr 1) ∧ m.y ≠ Sum.inr (Sum.inr 1)) ∨
          (m.y = Sum.inr (Sum.inr 1) ∧ m.x ≠ (Sum.inr (Sum.inr 1) : E ⊕ (I ⊕ Fin 2)))) := by
  by_cases hσ : q.σ = true
  · have h : owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q) =
        (⟨true, false, owxEmb 2 q.src, Sum.inr (Sum.inr 1)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 2 q.dst⟩) := by
      simp [owxDE, SEdge.map, hσ]
    rw [h]
    exact BAExpandWOrd_split3 _ _ _ rfl rfl rfl _ (Or.inl ⟨rfl, BAExpandWOrd_emb_ne_β _⟩)
      (Or.inl (Or.inr ⟨rfl, BAExpandWOrd_emb_ne_β _⟩))
  · have hσ' : q.σ = false := by simpa using hσ
    have h : owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q) =
        (⟨false, false, owxEmb 2 q.src, Sum.inr (Sum.inr 0)⟩, ⟨false, false, Sum.inr (Sum.inr 1), owxEmb 2 q.dst⟩) := by
      simp [owxDE, SEdge.map, hσ']
    rw [h]
    exact BAExpandWOrd_split3 _ _ _ rfl rfl rfl _ (Or.inl ⟨rfl, BAExpandWOrd_emb_ne_β _⟩)
      (Or.inr (Or.inl ⟨rfl, BAExpandWOrd_emb_ne_β _⟩))

end ExtGraph

/-! ## 3. Targets 1 and 2: the raw counters and the raw order -/

/-- **Target 1, term 1** (`B:361-363`; T2295-prove (a) row 8): the raw counters of term 1 of `lanlw` are
`⟨n_S + 1, n_W + 1, n_A + 1, n_M, 0, 0⟩`, for every graph (normal or not): one solid edge more, one waved edge
`S_{αβ}`, `β` a new singleton internal atom, `α` joins the atom of `x` through `M_{xα}`, both join its molecule. -/
theorem lanlwT1_counters :
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      (BAGraph.lanlwT1 Γ p).counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩ := by
  intro Ex Ix _ _ _ _ Γ p hp _ _
  have hl := lwSplit_snd_length Γ.solid p hp
  rw [BAExpandWOrd_lanlwT1_eq, BAExpandWOrd_ext_counters]
  have : p.2.length + 2 = Γ.nS + 1 := by simp only [BAGraph.nS]; omega
  simp only [List.length_cons, List.length_nil, this]

/-- **Target 1, derivative terms** (`B:361-363`; row 8): the raw counters of every derivative term of `lanlw`:
`p.1` and `q.1` removed, the two `owxDE` edges and `G_{βy}` added. -/
theorem lanlwD_counters :
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      ∀ q ∈ lwSplit p.2, (BAGraph.lanlwD Γ p q).counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩ := by
  intro Ex Ix _ _ _ _ Γ p hp _ _ q hq
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  rw [BAExpandWOrd_lanlwD_eq, BAExpandWOrd_ext_counters]
  have : q.2.length + 3 = Γ.nS + 1 := by simp only [BAGraph.nS]; omega
  simp only [List.length_cons, List.length_nil, this]

/-- **Target 2** (`B:361-363`; row 8): every term of `lanlw` has raw order `ord Γ + 1`. -/
theorem lanlw_ord :
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      ∀ Δ ∈ BAGraph.lanlwTerms Γ p, Δ.scalingOrder = Γ.scalingOrder + 1 := by
  intro Ex Ix _ _ _ _ Γ p hp h1 h2 Δ hΔ
  have key : Δ.counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩ := by
    simp only [BAGraph.lanlwTerms, List.mem_cons, List.mem_map] at hΔ
    rcases hΔ with rfl | ⟨q, hq, rfl⟩
    · exact lanlwT1_counters Γ p hp h1 h2
    · exact lanlwD_counters Γ p hp h1 h2 q hq
  unfold BAGraph.scalingOrder
  rw [key]
  simp only [BAGraph.counters, ord]
  push_cast
  ring

/-! ## 4. Target 3: `lanlw_scalingOrderG` -/

/-- **Target 3: `lanlw_scalingOrderG`** (`B:354-372`; T2295-prove (a) row 9, tight: minimum `0`, 13228 equality
cases): for a normal `Γ`, every graph of the partition of every term of `lanlw` has `ord ≥ ord Γ`.  A member with
`j` `M`-splits has `ord - ord Γ = 1 - j + 2κ`, `κ ≥ 0` the internal atoms lost; `j ≤ 1` for term 1, and `j ≥ 2`
for a derivative term splits an edge at `β`, merging `β`'s singleton atom (`κ ≥ 1`). -/
theorem lanlw_scalingOrderG :
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      Γ.Normal → ∀ Δ ∈ BAGraph.lanlwTerms Γ p, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ Δ.scalingOrderG := by
  intro Ex Ix _ _ _ _ Γ p hp _ _ hN Δ hΔ
  have hl := lwSplit_snd_length Γ.solid p hp
  have hcirc : ∀ e ∈ p.2, e.circ = true := fun e he =>
    hN.2 e ((lwSplit_perm Γ.solid p hp).mem_iff.2 (List.mem_cons_of_mem _ he))
  have key : ∀ Δs ∈ Δ.splitG, Δs.Normal ∧ ord Γ.counters ≤ ord Δs.counters := by
    simp only [BAGraph.lanlwTerms, List.mem_cons, List.mem_map] at hΔ
    rcases hΔ with rfl | ⟨q, hq, rfl⟩
    · rw [BAExpandWOrd_lanlwT1_eq]
      refine BAExpandWOrd_ext_ge Γ hN p.2 _ p.1.src hcirc (by simp only [BAGraph.nS]; simp; omega) ?_
      intro r hr
      exact Or.inl (BAExpandWOrd_split2 _ _ rfl rfl r hr)
    · have hl' := lwSplit_snd_length p.2 q hq
      have hcirc' : ∀ e ∈ q.2, e.circ = true := fun e he =>
        hcirc e ((lwSplit_perm p.2 q hq).mem_iff.2 (List.mem_cons_of_mem _ he))
      rw [BAExpandWOrd_lanlwD_eq]
      exact BAExpandWOrd_ext_ge Γ hN q.2 _ p.1.src hcirc' (by simp only [BAGraph.nS]; simp; omega)
        (BAExpandWOrd_D_split q.1 p.1.dst)
  rw [BAGraph.le_scalingOrderG_iff]
  intro P hP
  simp only [BAGraph.partition, List.mem_map] at hP
  obtain ⟨Δs, hΔs, rfl⟩ := hP
  obtain ⟨hNs, hge⟩ := key Δs hΔs
  change ord Γ.counters ≤ ord Δs.packMerge.counters
  rw [BAExpandWOrd_packMerge_counters Δs hNs]
  exact hge


/-! ## 5. Instances (namespace `RBM.Graph.BAExpandWOrdInst`) -/

section InstLemmas

variable {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

private theorem BAExpandWOrd_foldr_min_le (L : List (WithTop ℤ)) (a : WithTop ℤ) (h : a ∈ L) :
    L.foldr min ⊤ ≤ a := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

/-- A normal term of `G = Ǧ + M` bounds `ord` of a general graph from above (the minimum of `B:354-355`). -/
private theorem BAExpandWOrd_scalingOrderG_le (Δ Δs : BAGraph E' I') (hΔs : Δs ∈ Δ.splitG) (hN : Δs.Normal) :
    Δ.scalingOrderG ≤ ((ord Δs.counters : ℤ) : WithTop ℤ) := by
  have hmem : (((Δs.packMerge).scalingOrder : ℤ) : WithTop ℤ) ∈
      Δ.partition.map (fun P => ((P.scalingOrder : ℤ) : WithTop ℤ)) :=
    List.mem_map_of_mem (f := fun P : BAPGraph E' => ((P.scalingOrder : ℤ) : WithTop ℤ))
      (List.mem_map_of_mem (f := BAGraph.packMerge) hΔs)
  have h2 : Δs.packMerge.scalingOrder = ord Δs.counters := by
    change ord Δs.packMerge.counters = _
    rw [BAExpandWOrd_packMerge_counters Δs hN]
  have h1 := BAExpandWOrd_foldr_min_le _ _ hmem
  rw [h2] at h1
  exact h1

end InstLemmas

namespace BAExpandWOrdInst

set_option maxRecDepth 100000

/-- (I3) as stated (T2295-prove (a) Command D: counters `2 1 1 0`, raw 2, `ordG` 1). -/
theorem T2315_I3 :
    (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).counters = ⟨2, 1, 1, 0, 0, 0⟩ ∧
    (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).scalingOrder = 2 ∧
    (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).scalingOrderG = (((1 : ℤ)) : WithTop ℤ) := by
  refine ⟨?_, by decide, ?_⟩
  · have : (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).nS = 2 ∧
        (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).nW = 1 ∧
        (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).nA = 1 ∧
        (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).nM = 0 := by decide
    simp only [BAGraph.counters, this.1, this.2.1, this.2.2.1, this.2.2.2]
  · have hp : ((⟨true, true, .inl 0, .inl 1⟩ : SEdge (Fin 2 ⊕ Fin 0)), ([] : List (SEdge (Fin 2 ⊕ Fin 0)))) ∈
        lwSplit baGcxy.solid := by simp [baGcxy, lwSplit]
    have hN : baGcxy.Normal := by simp [BAGraph.Normal, baGcxy]
    have hge := lanlw_scalingOrderG baGcxy _ hp rfl rfl hN _ (List.mem_cons_self ..)
    have hΓ : baGcxy.scalingOrder = 1 := by decide
    rw [hΓ] at hge
    refine le_antisymm ?_ hge
    obtain ⟨Δs, hmem, hNs, hord⟩ : ∃ Δs ∈ (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).splitG,
        ((∀ e ∈ Δs.dotted, e.eq = false) ∧ (∀ e ∈ Δs.solid, e.circ = true)) ∧ ord Δs.counters = 1 := by
      decide
    have := BAExpandWOrd_scalingOrderG_le _ Δs hmem hNs
    rw [hord] at this
    exact this

/-- (I4) as stated (Command D: counters `2 1 2 1`, raw 0, `ordG` -1). -/
theorem T2315_I4 :
    (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).counters = ⟨2, 1, 2, 1, 0, 0⟩ ∧
    (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).scalingOrder = 0 ∧
    (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).scalingOrderG = (((-1 : ℤ)) : WithTop ℤ) := by
  refine ⟨?_, by decide, ?_⟩
  · have : (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).nS = 2 ∧
        (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).nW = 1 ∧
        (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).nA = 2 ∧
        (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).nM = 1 := by decide
    simp only [BAGraph.counters, this.1, this.2.1, this.2.2.1, this.2.2.2]
  · have hp : ((⟨true, true, .inr 0, .inr 0⟩ : SEdge (Fin 0 ⊕ Fin 1)), ([] : List (SEdge (Fin 0 ⊕ Fin 1)))) ∈
        lwSplit baGcxx.solid := by simp [baGcxx, lwSplit]
    have hN : baGcxx.Normal := by simp [BAGraph.Normal, baGcxx]
    have hge := lanlw_scalingOrderG baGcxx _ hp rfl rfl hN _ (List.mem_cons_self ..)
    have hΓ : baGcxx.scalingOrder = -1 := by decide
    rw [hΓ] at hge
    refine le_antisymm ?_ hge
    obtain ⟨Δs, hmem, hNs, hord⟩ : ∃ Δs ∈ (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).splitG,
        ((∀ e ∈ Δs.dotted, e.eq = false) ∧ (∀ e ∈ Δs.solid, e.circ = true)) ∧ ord Δs.counters = -1 := by
      decide
    have := BAExpandWOrd_scalingOrderG_le _ Δs hmem hNs
    rw [hord] at this
    exact this

/-- **Target 1 at `baGcxy`**: the raw counters of term 1 (`n_S = 1`, `n_W = 0`, `n_A = 0`, `n_M = 0` before). -/
example : (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).counters =
    ⟨baGcxy.nS + 1, baGcxy.nW + 1, baGcxy.nA + 1, baGcxy.nM, 0, 0⟩ :=
  lanlwT1_counters baGcxy _ (by simp [baGcxy, lwSplit]) rfl rfl

/-- **Target 2 at `baGcxy`**: every term of `lanlw` has raw order `ord Γ + 1`. -/
example : ∀ Δ ∈ BAGraph.lanlwTerms baGcxy (⟨true, true, .inl 0, .inl 1⟩, []),
    Δ.scalingOrder = baGcxy.scalingOrder + 1 :=
  lanlw_ord baGcxy _ (by simp [baGcxy, lwSplit]) rfl rfl

/-- **Target 3 at `baGcxy`** (`baGcxy` is normal: no `=`-dotted edge, the one solid edge is circled). -/
example : ∀ Δ ∈ BAGraph.lanlwTerms baGcxy (⟨true, true, .inl 0, .inl 1⟩, []),
    ((baGcxy.scalingOrder : ℤ) : WithTop ℤ) ≤ Δ.scalingOrderG :=
  lanlw_scalingOrderG baGcxy _ (by simp [baGcxy, lwSplit]) rfl rfl (by simp [BAGraph.Normal, baGcxy])

/-- A derivative term: `Ǧ_{y'x} Ǧ_{xy}` (`BAVocabInst.baGGLhs`, `y', y = inl 0, inl 1`, `x = inr 0`), the edge
`p.1 = Ǧ_{y'x}` is expanded (`x = y'`, `y = inr 0`) and `q.1 = Ǧ_{xy}` is differentiated: the derivative term has
`ord = ord Γ + 1 = 1`, the counters `⟨3, 1, 2, 1, 0, 0⟩` (`n_A = 2`: the atom `{x}` and `{β}`), and `ordG = 0` (tight). -/
theorem T2315_D :
    (BAGraph.lanlwD BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩])
      (⟨true, true, .inr 0, .inl 1⟩, [])).counters = ⟨3, 1, 2, 1, 0, 0⟩ ∧
    (BAGraph.lanlwD BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩])
      (⟨true, true, .inr 0, .inl 1⟩, [])).scalingOrder = 1 ∧
    (BAGraph.lanlwD BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩])
      (⟨true, true, .inr 0, .inl 1⟩, [])).scalingOrderG = (((0 : ℤ)) : WithTop ℤ) := by
  have hp : ((⟨true, true, .inl 0, .inr 0⟩ : SEdge (Fin 2 ⊕ Fin 1)),
      [(⟨true, true, .inr 0, .inl 1⟩ : SEdge (Fin 2 ⊕ Fin 1))]) ∈ lwSplit BAVocabInst.baGGLhs.solid :=
    List.mem_cons_self ..
  have hq : ((⟨true, true, .inr 0, .inl 1⟩ : SEdge (Fin 2 ⊕ Fin 1)), ([] : List (SEdge (Fin 2 ⊕ Fin 1)))) ∈
      lwSplit [(⟨true, true, .inr 0, .inl 1⟩ : SEdge (Fin 2 ⊕ Fin 1))] := List.mem_cons_self ..
  have hN : BAVocabInst.baGGLhs.Normal := by simp [BAGraph.Normal, BAVocabInst.baGGLhs]
  refine ⟨?_, by decide, ?_⟩
  · have : (BAGraph.lanlwD BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩])
      (⟨true, true, .inr 0, .inl 1⟩, [])).nS = 3 ∧
      (BAGraph.lanlwD BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩])
      (⟨true, true, .inr 0, .inl 1⟩, [])).nW = 1 ∧
      (BAGraph.lanlwD BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩])
      (⟨true, true, .inr 0, .inl 1⟩, [])).nA = 2 ∧
      (BAGraph.lanlwD BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩])
      (⟨true, true, .inr 0, .inl 1⟩, [])).nM = 1 := by decide
    simp only [BAGraph.counters, this.1, this.2.1, this.2.2.1, this.2.2.2]
  · have hge := lanlw_scalingOrderG BAVocabInst.baGGLhs _ hp rfl rfl hN
      (BAGraph.lanlwD BAVocabInst.baGGLhs
        (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩]) (⟨true, true, .inr 0, .inl 1⟩, []))
      (List.mem_cons_of_mem _ (List.mem_map_of_mem hq))
    have hΓ : BAVocabInst.baGGLhs.scalingOrder = 0 := by decide
    rw [hΓ] at hge
    refine le_antisymm ?_ hge
    obtain ⟨Δs, hmem, hNs, hord⟩ : ∃ Δs ∈ (BAGraph.lanlwD BAVocabInst.baGGLhs
        (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩]) (⟨true, true, .inr 0, .inl 1⟩, [])).splitG,
        ((∀ e ∈ Δs.dotted, e.eq = false) ∧ (∀ e ∈ Δs.solid, e.circ = true)) ∧ ord Δs.counters = 0 := by
      decide
    have := BAExpandWOrd_scalingOrderG_le _ Δs hmem hNs
    rw [hord] at this
    exact this

/-- **Targets 1-3 at `baGGLhs`, the derivative term** (`q ∈ lwSplit p.2` is the one other edge). -/
example : (BAGraph.lanlwD BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩])
      (⟨true, true, .inr 0, .inl 1⟩, [])).counters =
    ⟨BAVocabInst.baGGLhs.nS + 1, BAVocabInst.baGGLhs.nW + 1, BAVocabInst.baGGLhs.nA + 1,
      BAVocabInst.baGGLhs.nM, 0, 0⟩ :=
  lanlwD_counters BAVocabInst.baGGLhs _ List.mem_cons_self rfl rfl _ List.mem_cons_self

example : ∀ Δ ∈ BAGraph.lanlwTerms BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩]),
    Δ.scalingOrder = BAVocabInst.baGGLhs.scalingOrder + 1 :=
  lanlw_ord BAVocabInst.baGGLhs _ List.mem_cons_self rfl rfl

example : ∀ Δ ∈ BAGraph.lanlwTerms BAVocabInst.baGGLhs
      (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inr 0, .inl 1⟩]),
    ((BAVocabInst.baGGLhs.scalingOrder : ℤ) : WithTop ℤ) ≤ Δ.scalingOrderG :=
  lanlw_scalingOrderG BAVocabInst.baGGLhs _ List.mem_cons_self rfl rfl (by simp [BAGraph.Normal, BAVocabInst.baGGLhs])

end BAExpandWOrdInst

end RBM.Graph

end
