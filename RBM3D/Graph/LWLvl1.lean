/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWSymm
import RBM3D.Graph.LWVocab
import RBM3D.Graph.ScalingOrder
import RBM3D.Graph.LWWeightExp

/-!
# LW-08: locally standard graphs, `strat_local`, the `lvl1 lemma` (T2128)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:353-399` (cited `7_8:line`): the three bullets that make every local
expansion progress (`7_8:353-362`), `deflvl1` (`7_8:367-386`, `(eq:neutralcharge)`), the `lvl1 lemma` (`7_8:392-399`, [yang2021]
Lemma 3.22, proved here, DECISIONS §5); `paper/tex/B_graphical_lemmas.tex:135-157` (`strat_local`, cited `B:line`).  Design: T2040
(split row LW-08), the preflight `docs/reports/T2128-prove.md` (a), the expansions in the uniform shape of T2131 (`Graph/LWSymm`).

## Contents (namespace `RBM.Graph`)

1. **`deflvl1`** (target 1, §10): the degree `LGraph.lvl1DegAt` and the charge `LGraph.lvl1ChargeAt` of a vertex (§5, solid self-loops not
   counted), `LGraph.StdNeutral`, `LGraph.LocStd`, `PGraph.LocStd` (decidable; `lvl1_locStd_iff` spells out the three clauses).
2. **`strat_local` as a one-step relation** (target 2, §10, §11): `LocStep m P outs` with the constructors `weight`, `edge`, `gg`
   (Steps 1, 2, 3 of `B:135-157`; a later step applies only when the earlier ones are null).  The outputs are the terms of the
   expansions of T2131 (`lwSymmOwxT*`, `lwSymmOe1x*`, `lwSymmOe2xR*`, for the selector `(c, t)` that makes the selected edge the blue
   out-edge), each followed by `LGraph.partition m` and packed over the external vertices of the input (`lvl1Pack`).
   `lvl1_step_identity`: `E[Γ] = Σ_{Γ' ∈ outs} E[Γ']`.
3. **The termination argument** (§1-§9, §12, §13): the measure `Lvl1Mu K` = (order deficit `(K - ord)⁺`, `n_loops`, `n_S`, `n_pairs`),
   lexicographic (`Lvl1Lt`, `lvl1Lt_wf`); `lvl1_step_good`: every output of every `LocStep` at a normal graph is normal, `ord`, `n_M`
   and `n_V - n_W` do not get worse, and either `ord` rises or the measure falls (`Lvl1Good`, proved term by term, `lvl1_good_*`);
   `lvl1_exists_step`: a normal graph that is not locally standard admits a step.
4. **The `lvl1 lemma`** (target 3, §13, §14): `lvl1_lemma` (for the order cutoff `K`) and `lvl1_lemma_size` (the paper's form: `size ≤
   W^{-D}` for the error graphs), by well-founded induction on the measure (`lvl1_exists_aux`).
5. **The induction principle** (target 4, §13, §14): `Lvl1Reach m K P Q` (`Q` is reached from `P` by steps applied below the cutoff to
   graphs that are not locally standard) and `lvl1_induction`; `lvl1_lemma` states `Lvl1Reach` for every graph of both lists, and
   `lvl1_lemma_induction` gives, for the same lists, every predicate that holds at `Γ` and is passed along every `LocStep`.
6. **The cutoff** (target 5, §15): (a) `ord ≥ K` (combinatorial, independent of `n`); `lvl1Cutoff` and `lvl1_size_le`: above it
   `size ≤ W^{-D}` in the regime `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`.
7. **Compiled instances** (§16, `lvl1_inst_*`): `deflvl1` on records (one locally standard, each clause failing alone), one `LocStep` of each
   kind and its identity, `lvl1_lemma` and `lvl1_lemma_size` on `p2Graph`, `lvl1_induction` on one invariant, at the merged instance data
   of `Graph/LWWeightExp.lean` (`d = 3`, `L = 3`, `W = 1`, `E = 0`, `t = 1/2`) and, for the size, at `W = 27`, `L = 3`.

## Hypotheses of the expectation identity

Those of the merged `owx_graph_E`, `oe1x_graph_E`, `oe2x_graph_E` (`GaussIBP sz`, `0 < Im z`, `0 < u`, `m ≠ 0`, `z + u m = -m⁻¹`, the
`S⁺` resummation, `M a a = m`) plus `M a b = 0` for `a ≠ b` (ticket Amend 1, C4) and `S⁺ᵀ = S⁺` (the hypothesis of the symmetric forms of
T2131; `lwSymm_lwSplus_symm` proves it for `S⁺ = lwSplus`).  `GaussIBP` is the proved `gaussIBP`; no stochastic input enters.

## Differences from the paper and the ticket (delta candidates)

* `T2128a`: the data hypothesis `S⁺ᵀ = S⁺` (above); the paper's `S⁺` is symmetric.
* `T2128b`: the cutoff is (a) `ord ≥ K` instead of the paper's `size ≤ W^{-D}` (`(eq:smallsize)`, `B:140`); `lvl1_size_le` turns it into
  `size ≤ W^{-D}`.  The list `errs` holds every graph the strategy stops at because of the cutoff, locally standard or not.
* `T2128c`: the terms `m 1_{x = y₁}` of `(Oe1x)` and `R1 = m δ_{xy} G_{y' x}` of `(Oe2x)` are not listed in the outputs of `LocStep`: they
  vanish on normal graphs (`lvl1_oe1xT1_zero`, `lvl1_oe2xR1_zero`).
* `T2128d`: the termination measure is `(K - ord, n_loops, n_S, n_pairs)`, with `n_pairs` the number of pairs of solid non-loop edges
  with a common internal end, not the preflight's `(…, w, Φ, n_S)` (an internal choice, no statement changes).
* `T2128e`: the `lvl1 lemma` is stated for normal packed graphs (the paper: "an arbitrary graph with `O(1)` vertices and edges";
  `dot-def` reduces to normal graphs).
-/

set_option linter.style.longLine false

/-! ## 1. Counters of a term of the dotted edge partition; the measure pieces `LGraph.lvl1NLoops`, `LGraph.lvl1NPairs`, `Lvl1Good` -/

section Lvl1PartA
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Defs
variable {V : Type*} [DecidableEq V]

/-- loops in a list of solid edges -/
def lvl1Loops (es : List (SEdge V)) : ℕ := es.countP fun e => decide (e.src = e.dst)

/-- the number of internal common endpoints of two non-loop edges -/
def lvl1Share (int : V → Bool) (e e' : SEdge V) : ℕ :=
  if e.src = e.dst ∨ e'.src = e'.dst then 0 else
    (if e.src = e'.src ∧ int e.src = true then 1 else 0) + (if e.src = e'.dst ∧ int e.src = true then 1 else 0) +
    (if e.dst = e'.src ∧ int e.dst = true then 1 else 0) + (if e.dst = e'.dst ∧ int e.dst = true then 1 else 0)

def lvl1Pairs (int : V → Bool) : List (SEdge V) → ℕ
  | [] => 0
  | e :: es => lvl1Pairs int es + (es.map (lvl1Share int e)).sum

private theorem lvl1_ite_swap (int : V → Bool) (a b : V) :
    (if a = b ∧ int a = true then 1 else 0) = (if b = a ∧ int b = true then 1 else 0) := by
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem lvl1Share_comm (int : V → Bool) (e e' : SEdge V) : lvl1Share int e e' = lvl1Share int e' e := by
  unfold lvl1Share
  by_cases h : e.src = e.dst ∨ e'.src = e'.dst
  · have h' : e'.src = e'.dst ∨ e.src = e.dst := h.symm
    simp [h, h']
  · have h' : ¬ (e'.src = e'.dst ∨ e.src = e.dst) := fun h2 => h h2.symm
    simp only [h, h', ite_false]
    rw [lvl1_ite_swap int e.src e'.src, lvl1_ite_swap int e.src e'.dst, lvl1_ite_swap int e.dst e'.src,
      lvl1_ite_swap int e.dst e'.dst]
    omega

theorem lvl1Pairs_append (int : V → Bool) (l₁ l₂ : List (SEdge V)) :
    lvl1Pairs int (l₁ ++ l₂) = lvl1Pairs int l₁ + lvl1Pairs int l₂ +
      (l₁.map fun e => (l₂.map (lvl1Share int e)).sum).sum := by
  induction l₁ with
  | nil => simp [lvl1Pairs]
  | cons e l ih =>
    simp only [List.cons_append, lvl1Pairs, ih, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    omega

theorem lvl1Pairs_perm (int : V → Bool) {l₁ l₂ : List (SEdge V)} (h : l₁.Perm l₂) :
    lvl1Pairs int l₁ = lvl1Pairs int l₂ := by
  induction h with
  | nil => rfl
  | @cons e l₁ l₂ hperm ih =>
    simp only [lvl1Pairs, ih]
    congr 1
    exact (hperm.map (lvl1Share int e)).sum_eq
  | swap x y l =>
    simp only [lvl1Pairs, List.map_cons, List.sum_cons]
    rw [lvl1Share_comm int x y]
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2


/-- how the weight split changes a list of solid edges: `d` weights are dropped, the others kept or circled -/
inductive lvl1Split : List (SEdge V) → List (SEdge V) → ℕ → Prop
  | nil : lvl1Split [] [] 0
  | keep (e : SEdge V) {es es' : List (SEdge V)} {d : ℕ} (h : ¬ (e.src = e.dst ∧ e.circ = false)) :
      lvl1Split es es' d → lvl1Split (e :: es) (e :: es') d
  | circ (e : SEdge V) {es es' : List (SEdge V)} {d : ℕ} (h1 : e.src = e.dst) (h2 : e.circ = false) :
      lvl1Split es es' d → lvl1Split (e :: es) ({ e with circ := true } :: es') d
  | drop (e : SEdge V) {es es' : List (SEdge V)} {d : ℕ} (h1 : e.src = e.dst) (h2 : e.circ = false) :
      lvl1Split es es' d → lvl1Split (e :: es) es' (d + 1)

private theorem lvl1Split_of_mem (m : ℂ) :
    ∀ (es : List (SEdge V)) (r : ℂ × List (SEdge V)), r ∈ lwSplitLoops m es → ∃ d, lvl1Split es r.2 d
  | [], r, h => by
    simp only [lwSplitLoops, List.mem_singleton] at h
    subst h
    exact ⟨0, .nil⟩
  | e :: es, r, h => by
    simp only [lwSplitLoops, List.mem_flatMap] at h
    obtain ⟨r', hr', h⟩ := h
    obtain ⟨d, hd⟩ := lvl1Split_of_mem m es r' hr'
    by_cases hw : e.src = e.dst ∧ e.circ = false
    · rw [if_pos hw] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact ⟨d, .circ e hw.1 hw.2 hd⟩
      · exact ⟨d + 1, .drop e hw.1 hw.2 hd⟩
    · simp only [hw, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact ⟨d, .keep e hw hd⟩

private theorem lvl1Split.length_add {es es' : List (SEdge V)} {d : ℕ} (h : lvl1Split es es' d) :
    es'.length + d = es.length := by
  induction h with
  | nil => rfl
  | keep e _ _ ih => simp only [List.length_cons]; omega
  | circ e _ _ _ ih => simp only [List.length_cons]; omega
  | drop e _ _ _ ih => simp only [List.length_cons]; omega

private theorem lvl1Split.loops_add {es es' : List (SEdge V)} {d : ℕ} (h : lvl1Split es es' d) :
    lvl1Loops es' + d = lvl1Loops es := by
  induction h with
  | nil => rfl
  | keep e hne _ ih => simp only [lvl1Loops, List.countP_cons] at ih ⊢; omega
  | circ e h1 h2 _ ih => simp [lvl1Loops, List.countP_cons, h1] at ih ⊢; omega
  | drop e h1 h2 _ ih => simp [lvl1Loops, List.countP_cons, h1] at ih ⊢; omega

/-- a weight: a loop without circle -/
def lvl1IsW (e : SEdge V) : Bool := decide (e.src = e.dst) && !e.circ

private theorem lvl1Split.d_le {es es' : List (SEdge V)} {d : ℕ} (h : lvl1Split es es' d) :
    d ≤ es.countP lvl1IsW := by
  induction h with
  | nil => simp
  | keep e hne _ ih =>
    have : lvl1IsW e = false := by
      simp only [lvl1IsW, Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_false']
      by_contra hc
      push Not at hc
      exact hne ⟨hc.1, by simpa using hc.2⟩
    rw [List.countP_cons_of_neg (by simp [this])]; exact ih
  | circ e h1 h2 _ ih =>
    have : lvl1IsW e = true := by simp [lvl1IsW, h1, h2]
    rw [List.countP_cons_of_pos (by simp [this])]; exact le_trans ih (Nat.le_succ _)
  | drop e h1 h2 _ ih =>
    have : lvl1IsW e = true := by simp [lvl1IsW, h1, h2]
    rw [List.countP_cons_of_pos (by simp [this])]; omega

private theorem lvl1Pairs_cons_loop (int : V → Bool) (e : SEdge V) (he : e.src = e.dst) (es : List (SEdge V)) :
    lvl1Pairs int (e :: es) = lvl1Pairs int es := by
  have : (es.map (lvl1Share int e)).sum = 0 := by
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy
    simp [lvl1Share, he]
  simp [lvl1Pairs, this]

private theorem lvl1Split.pairs_eq (int : V → Bool) {es es' : List (SEdge V)} {d : ℕ} (h : lvl1Split es es' d) :
    lvl1Pairs int es' = lvl1Pairs int es := by
  have key : ∀ (e : SEdge V) {es es' : List (SEdge V)} {d : ℕ}, lvl1Split es es' d →
      (es'.map (lvl1Share int e)).sum = (es.map (lvl1Share int e)).sum := by
    intro e es es' d h
    induction h with
    | nil => rfl
    | keep x _ _ ih => simp only [List.map_cons, List.sum_cons, ih]
    | circ x h1 h2 _ ih => simp [lvl1Share, h1] at ih ⊢; omega
    | drop x h1 h2 _ ih => simp [lvl1Share, h1] at ih ⊢; omega
  induction h with
  | nil => rfl
  | keep e _ h ih => simp only [lvl1Pairs, ih, key e h]
  | circ e h1 h2 h ih =>
    rw [lvl1Pairs_cons_loop int _ (by simpa using h1), lvl1Pairs_cons_loop int _ h1, ih]
  | drop e h1 h2 h ih => rw [lvl1Pairs_cons_loop int _ h1, ih]

end Defs

section PartStruct
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem lvl1_vmapC_injective (Γ : LGraph E I) : Function.Injective Γ.vmapC := by
  intro q q' h
  unfold LGraph.vmapC at h
  by_cases hq : Γ.IsExtCls q <;> by_cases hq' : Γ.IsExtCls q' <;> simp [hq, hq'] at h
  · exact h
  · exact h

private theorem lvl1_vmap_inl (Γ : LGraph E I) (a : E) : Γ.vmap (Sum.inl a) = Sum.inl (Γ.extMap a) := by
  have hq : Γ.IsExtCls (Γ.cls (Sum.inl a)) := ⟨a, rfl⟩
  simp [LGraph.vmap, LGraph.vmapC, hq, LGraph.extMap]

private theorem lvl1_vmap_surj (Γ : LGraph E I) : Function.Surjective Γ.vmap := by
  rintro (⟨q, hq⟩ | ⟨q, hq⟩)
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [LGraph.vmap, LGraph.vmapC, hq]⟩
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [LGraph.vmap, LGraph.vmapC, hq]⟩

/-- **The structure of a term of the dotted edge partition**: the vertex map `vm` onto the vertices of the term, the
weights it drops, the unchanged waved edges, and the separation of the ends of the `×`-dotted edges that stay
(`dot-def`, `7_8:214-225`). -/
theorem lvl1_part_struct (m : ℂ) (Δ : LGraph E I) (P : PGraph E) (hP : P ∈ Δ.partition m) :
    ∃ (vm : E ⊕ I → P.E' ⊕ P.I') (d : ℕ),
      Function.Surjective vm ∧ (∀ a : E, vm (Sum.inl a) = Sum.inl (P.ext a)) ∧
      (∀ e ∈ Δ.dotted, e.eq = false → Δ.SBetween e.x e.y → vm e.x ≠ vm e.y) ∧
      (∀ e ∈ Δ.dotted, e.eq = true → vm e.x = vm e.y) ∧
      P.g.waved = Δ.waved.map (WEdge.map vm) ∧
      lvl1Split (Δ.solid.map (SEdge.map vm)) P.g.solid d := by
  classical
  unfold LGraph.partition at hP
  obtain ⟨Δ', hΔ', hP'⟩ := List.mem_flatMap.1 hP
  unfold LGraph.mergeSplitP at hP'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hP'
  unfold LGraph.splitWeights at hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
  unfold LGraph.partitionTerms at hΔ'
  obtain ⟨hmem, hcons⟩ := List.mem_filter.1 hΔ'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hmem
  have hcons' : (Δ.withDots c).Consistent := by simpa using hcons
  obtain ⟨d, hd⟩ := lvl1Split_of_mem m _ r hr
  refine ⟨(Δ.withDots c).vmap, d, lvl1_vmap_surj _, fun a => lvl1_vmap_inl _ a, ?_, ?_, rfl, hd⟩
  · intro e he heq hsb hvm
    have hB : Δ.isB e = false := by simp [LGraph.isB, hsb]
    have hmemB : e ∈ Δ.dotBase := by simp [LGraph.dotBase, he, hB]
    have hin : e ∈ (Δ.withDots c).dotted := by simp [LGraph.withDots, hmemB]
    exact hcons' e hin heq (by
      have := lvl1_vmapC_injective (Δ.withDots c) hvm
      exact this)
  · intro e he heq
    have hB : Δ.isB e = false := by simp [LGraph.isB, heq]
    have hmemB : e ∈ Δ.dotBase := by simp [LGraph.dotBase, he, hB]
    have hin : e ∈ (Δ.withDots c).dotted := by simp [LGraph.withDots, hmemB]
    have hrel : (Δ.withDots c).EqRel e.x e.y := ⟨e, hin, heq, Or.inl ⟨rfl, rfl⟩⟩
    exact congrArg (Δ.withDots c).vmapC (Quotient.sound (Relation.EqvGen.rel _ _ hrel))


/-- **Dominated vertices are lost** (`n_V` of a merged graph): if `S` is a set of internal vertices each of which has the
same image as a vertex outside `S`, the merged graph has at least `|S|` fewer internal vertices. -/
theorem lvl1_card_le {E' I' : Type} [Fintype I'] [DecidableEq I']
    (vm : E ⊕ I → E' ⊕ I') (hsurj : Function.Surjective vm) (hl : ∀ a : E, ∃ a' : E', vm (Sum.inl a) = Sum.inl a')
    (S : Finset I) (hS : ∀ i ∈ S, ∃ b : E ⊕ I, (∀ j ∈ S, b ≠ Sum.inr j) ∧ vm (Sum.inr i) = vm b) :
    Fintype.card I' + S.card ≤ Fintype.card I := by
  classical
  let T : Type := {i : I // i ∉ S ∧ ∃ q : I', vm (Sum.inr i) = Sum.inr q}
  let f : T → I' := fun i => Classical.choose i.2.2
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨v, hv⟩ := hsurj (Sum.inr q)
    rcases v with a | i
    · obtain ⟨a', ha'⟩ := hl a
      rw [ha'] at hv
      exact absurd hv (by simp)
    · by_cases hi : i ∈ S
      · obtain ⟨b, hb, hvb⟩ := hS i hi
        rcases b with a | j
        · obtain ⟨a', ha'⟩ := hl a
          rw [hv] at hvb
          rw [ha'] at hvb
          exact absurd hvb (by simp)
        · have hj : j ∉ S := fun hj => hb j hj rfl
          refine ⟨⟨j, hj, q, ?_⟩, ?_⟩
          · rw [← hvb, hv]
          · have := Classical.choose_spec (show ∃ q' : I', vm (Sum.inr j) = Sum.inr q' from ⟨q, by rw [← hvb, hv]⟩)
            have h2 : vm (Sum.inr j) = Sum.inr q := by rw [← hvb, hv]
            exact Sum.inr_injective (this.symm.trans h2)
      · refine ⟨⟨i, hi, q, hv⟩, ?_⟩
        have := Classical.choose_spec (show ∃ q' : I', vm (Sum.inr i) = Sum.inr q' from ⟨q, hv⟩)
        exact Sum.inr_injective (this.symm.trans hv)
  have h1 : Fintype.card I' ≤ Fintype.card T := Fintype.card_le_of_surjective f hf
  have h2 : Fintype.card T ≤ Fintype.card {i : I // i ∉ S} :=
    Fintype.card_le_of_injective (fun i : T => (⟨i.1, i.2.1⟩ : {i : I // i ∉ S})) (fun a b h => Subtype.ext (congrArg (Subtype.val : {i : I // i ∉ S} → I) h))
  have h3 : Fintype.card {i : I // i ∉ S} = Fintype.card I - S.card := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun i : I => i ∉ S) = Finset.univ \ S by
      ext i; simp, Finset.card_univ_diff]
  have h4 : S.card ≤ Fintype.card I := Finset.card_le_univ S
  omega


section NoMerge

variable {E' I' : Type}

/-- **Without lost vertices the pairs are those of the graph**: if no internal vertex shares its image with another
vertex, the number of pairs of edges with a common internal end is unchanged by the merge. -/
theorem lvl1_pairs_nomerge (vm : E ⊕ I → E' ⊕ I')
    (h8 : ∀ (i : I) (b : E ⊕ I), vm (Sum.inr i) = vm b → b = Sum.inr i)
    (hint : ∀ i : I, (vm (Sum.inr i)).isRight = true) (hext : ∀ a : E, (vm (Sum.inl a)).isRight = false)
    [DecidableEq E'] [DecidableEq I'] (l : List (SEdge (E ⊕ I))) :
    lvl1Pairs Sum.isRight (l.map (SEdge.map vm)) = lvl1Pairs Sum.isRight l := by
  have hterm : ∀ a b : E ⊕ I, (if vm a = vm b ∧ Sum.isRight (vm a) = true then 1 else 0) =
      (if a = b ∧ Sum.isRight a = true then 1 else 0) := by
    intro a b
    rcases a with a | i
    · simp [hext a]
    · by_cases hb : b = Sum.inr i
      · subst hb; simp [hint i]
      · have : vm (Sum.inr i) ≠ vm b := fun h => hb (h8 i b h)
        simp [this, Ne.symm hb]
  have hcol : ∀ e : SEdge (E ⊕ I), vm e.src = vm e.dst → e.src = e.dst ∨ (e.src.isRight = false ∧ e.dst.isRight = false) := by
    intro e h
    rcases hs : e.src with a | i
    · rcases hd : e.dst with b | j
      · right; simp
      · exfalso
        have := h8 j (Sum.inl a) (by rw [hs, hd] at h; exact h.symm)
        simp at this
    · left
      rw [hs] at h
      have := h8 i e.dst h
      rw [this]
  have hshare : ∀ e e' : SEdge (E ⊕ I), lvl1Share Sum.isRight (SEdge.map vm e) (SEdge.map vm e') = lvl1Share Sum.isRight e e' := by
    intro e e'
    unfold lvl1Share
    simp only [SEdge.map]
    by_cases h1 : e.src = e.dst
    · simp [h1]
    by_cases h2 : e'.src = e'.dst
    · simp [h2]
    have hnot : ¬ (e.src = e.dst ∨ e'.src = e'.dst) := by tauto
    simp only [hnot, ↓reduceIte]
    by_cases hc : vm e.src = vm e.dst ∨ vm e'.src = vm e'.dst
    · simp only [hc, ↓reduceIte]
      rcases hc with hc | hc
      · rcases hcol e hc with h | ⟨hs, hd⟩
        · exact absurd h h1
        · simp [hs, hd]
      · rcases hcol e' hc with h | ⟨hs, hd⟩
        · exact absurd h h2
        · have h3 : ∀ x : E ⊕ I, x = e'.src ∨ x = e'.dst → Sum.isRight x = false := by
            rintro x (rfl | rfl) <;> assumption
          have a1 : ¬ (e.src = e'.src ∧ e.src.isRight = true) := fun h => by
            have := h3 e.src (Or.inl h.1); simp [this] at h
          have a2 : ¬ (e.src = e'.dst ∧ e.src.isRight = true) := fun h => by
            have := h3 e.src (Or.inr h.1); simp [this] at h
          have a3 : ¬ (e.dst = e'.src ∧ e.dst.isRight = true) := fun h => by
            have := h3 e.dst (Or.inl h.1); simp [this] at h
          have a4 : ¬ (e.dst = e'.dst ∧ e.dst.isRight = true) := fun h => by
            have := h3 e.dst (Or.inr h.1); simp [this] at h
          simp [a1, a2, a3, a4]
    · simp only [hc, ↓reduceIte]
      exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (hterm e.src e'.src) (hterm e.src e'.dst))
        (hterm e.dst e'.src)) (hterm e.dst e'.dst)
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.map_cons, lvl1Pairs, ih]
    congr 1
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun e' _ => ?_)
    exact hshare e e'

end NoMerge

section Master
variable {I₀ : Type} [Fintype I₀] [DecidableEq I₀]

/-- **The master counting lemma for a term of the dotted edge partition of an expansion output** `Δ`, whose solid edges
are the images `R.map emb` of edges of the normal graph `Γ` (possibly some of them removed) together with the new
edges `N`: nothing of `R` collapses, `n_S` loses exactly the dropped weights, `n_V` loses at least the dominated vertices,
and the loops, weights and pairs of the term are read off the lists. -/
theorem lvl1_master (m : ℂ) (Γ : LGraph E I₀) (emb : E ⊕ I₀ → E ⊕ I) (hemb : Function.Injective emb)
    (R : List (SEdge (E ⊕ I₀))) (N : List (SEdge (E ⊕ I)))
    (hR : ∀ e ∈ R, (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true))
    (Δ : LGraph E I) (hsol : Δ.solid.Perm (R.map (SEdge.map emb) ++ N))
    (hdot : Δ.dotted = Γ.dotted.map (DEdge.map emb))
    (P : PGraph E) (hP : P ∈ Δ.partition m) :
    ∃ (vm : E ⊕ I → P.E' ⊕ P.I') (d : ℕ),
      Function.Surjective vm ∧ (∀ a : E, vm (Sum.inl a) = Sum.inl (P.ext a)) ∧
      P.g.nS + d = Δ.nS ∧ P.g.nW = Δ.nW ∧
      (∀ S : Finset I, (∀ i ∈ S, ∃ b : E ⊕ I, (∀ j ∈ S, b ≠ Sum.inr j) ∧ vm (Sum.inr i) = vm b) →
          P.g.nV + S.card ≤ Δ.nV) ∧
      lvl1Loops P.g.solid + d = lvl1Loops R + N.countP (fun e => decide (vm e.src = vm e.dst)) ∧
      d ≤ N.countP (fun e => decide (vm e.src = vm e.dst) && !e.circ) ∧
      (P.g.nV = Δ.nV → lvl1Pairs Sum.isRight P.g.solid = lvl1Pairs Sum.isRight Δ.solid) := by
  classical
  obtain ⟨vm, d, hsurj, hl, hsep, hdoteq, hwav, hsplit⟩ := lvl1_part_struct m Δ P hP
  have hperm : (Δ.solid.map (SEdge.map vm)).Perm (R.map (SEdge.map (vm ∘ emb)) ++ N.map (SEdge.map vm)) := by
    have h0 := hsol.map (SEdge.map vm)
    rw [List.map_append, List.map_map] at h0
    have hfun : (SEdge.map vm ∘ SEdge.map emb) = (SEdge.map (vm ∘ emb) : SEdge (E ⊕ I₀) → SEdge _) := by
      funext e; rfl
    rw [hfun] at h0
    exact h0
  -- the edges of `R` do not collapse
  have hold : ∀ e ∈ R, (vm (emb e.src) = vm (emb e.dst) ↔ e.src = e.dst) := by
    intro e he
    refine ⟨fun hvm => ?_, fun h => by rw [h]⟩
    by_contra hne
    obtain ⟨⟨d₀, hd₀, hd₀e, hd₀xy⟩⟩ : Nonempty (∃ d₀ ∈ Γ.dotted, d₀.eq = false ∧
        ((d₀.x = e.src ∧ d₀.y = e.dst) ∨ (d₀.x = e.dst ∧ d₀.y = e.src))) := ⟨(hR e he).1 hne⟩
    have hmem : SEdge.map emb e ∈ Δ.solid :=
      hsol.mem_iff.2 (List.mem_append_left _ (List.mem_map_of_mem he))
    have hne' : emb e.src ≠ emb e.dst := fun h => hne (hemb h)
    have hd₀' : DEdge.map emb d₀ ∈ Δ.dotted := by rw [hdot]; exact List.mem_map_of_mem hd₀
    have hsb : ∀ u v : E ⊕ I, ((u = emb e.src ∧ v = emb e.dst) ∨ (u = emb e.dst ∧ v = emb e.src)) → Δ.SBetween u v := by
      intro u v huv
      refine ⟨SEdge.map emb e, hmem, hne', ?_⟩
      rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    rcases hd₀xy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine hsep _ hd₀' hd₀e (hsb _ _ (Or.inl ⟨by simp [DEdge.map, h1], by simp [DEdge.map, h2]⟩)) ?_
      simpa [DEdge.map, h1, h2] using hvm
    · refine hsep _ hd₀' hd₀e (hsb _ _ (Or.inr ⟨by simp [DEdge.map, h1], by simp [DEdge.map, h2]⟩)) ?_
      simpa [DEdge.map, h1, h2] using hvm.symm
  have hlR : lvl1Loops (R.map (SEdge.map (vm ∘ emb))) = lvl1Loops R := by
    unfold lvl1Loops
    rw [List.countP_map]
    refine List.countP_congr fun e he => ?_
    show decide (vm (emb e.src) = vm (emb e.dst)) = true ↔ decide (e.src = e.dst) = true
    rw [decide_eq_true_iff, decide_eq_true_iff]
    exact hold e he
  have hwR : (R.map (SEdge.map (vm ∘ emb))).countP lvl1IsW = 0 := by
    rw [List.countP_eq_zero]
    intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    have h1 := hold e he
    have hc := (hR e he).2
    intro h
    have h' : vm (emb e.src) = vm (emb e.dst) ∧ e.circ = false := by
      unfold lvl1IsW at h
      simp only [SEdge.map, Function.comp_apply, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact ⟨of_decide_eq_true h.1, h.2⟩
    exact absurd (hc (h1.1 h'.1)) (by simp [h'.2])
  have hloops := hsplit.loops_add
  have hlen := hsplit.length_add
  have hdle := hsplit.d_le
  have hpairs := hsplit.pairs_eq Sum.isRight
  refine ⟨vm, d, hsurj, hl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [LGraph.nS, List.length_map] at hlen ⊢
    omega
  · simp [LGraph.nW, hwav]
  · intro S hS
    have := lvl1_card_le vm hsurj (fun a => ⟨_, hl a⟩) S hS
    simpa [LGraph.nV] using this
  · have h1 : lvl1Loops (Δ.solid.map (SEdge.map vm)) =
        lvl1Loops R + N.countP (fun e => decide (vm e.src = vm e.dst)) := by
      have e1 := hperm.countP_eq (fun e : SEdge (P.E' ⊕ P.I') => decide (e.src = e.dst))
      rw [List.countP_append] at e1
      have e2 : (N.map (SEdge.map vm)).countP (fun e : SEdge (P.E' ⊕ P.I') => decide (e.src = e.dst)) =
          N.countP (fun e => decide (vm e.src = vm e.dst)) := by
        rw [List.countP_map]; rfl
      unfold lvl1Loops at hlR ⊢
      rw [e1, e2, hlR]
    omega
  · have h1 : (Δ.solid.map (SEdge.map vm)).countP lvl1IsW =
        N.countP (fun e => decide (vm e.src = vm e.dst) && !e.circ) := by
      rw [hperm.countP_eq, List.countP_append, hwR, List.countP_map, zero_add]
      rfl
    omega
  · intro hnv
    have hnv' : Fintype.card P.I' = Fintype.card I := hnv
    have h8 : ∀ (i : I) (b : E ⊕ I), vm (Sum.inr i) = vm b → b = Sum.inr i := by
      intro i b hib
      by_contra hne
      have := lvl1_card_le vm hsurj (fun a => ⟨_, hl a⟩) {i} (by
        intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨b, by simpa using hne, hib⟩)
      simp only [Finset.card_singleton] at this
      omega
    have hint : ∀ i : I, (vm (Sum.inr i)).isRight = true := by
      intro i
      rcases hv : vm (Sum.inr i) with a' | q
      · exfalso
        obtain ⟨a, ha⟩ := P.ext_surj a'
        have := h8 i (Sum.inl a) (by rw [hv, hl a, ha])
        exact absurd this (by simp)
      · rfl
    have hext : ∀ a : E, (vm (Sum.inl a)).isRight = false := fun a => by rw [hl a]; rfl
    rw [hpairs]
    exact lvl1_pairs_nomerge vm h8 hint hext Δ.solid


end Master

section NM

variable {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁]
  [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]

/-- **A vertex map that carries molecules into molecules and meets every molecule of `Γ'` cannot increase `n_M`**
(`oe2x_nM_le` for graphs with different external vertex types). -/
theorem lvl1_nM_le (Γ : LGraph E₁ I₁) (Γ' : LGraph E₂ I₂) (φ : E₁ ⊕ I₁ → E₂ ⊕ I₂)
    (hφ : ∀ v', ∃ v, Γ'.molGraph.Reachable v' (φ v))
    (hl : ∀ a : E₁, ∃ a' : E₂, φ (Sum.inl a) = Sum.inl a')
    (hadj : ∀ u v, Γ.adj u v = true → Γ'.molGraph.Reachable (φ u) (φ v)) : Γ'.nM ≤ Γ.nM := by
  classical
  rw [Γ'.nM_eq_card, Γ.nM_eq_card]
  have hwalk : ∀ {v w : E₁ ⊕ I₁} (p : Γ.molGraph.Walk v w), Γ'.molGraph.Reachable (φ v) (φ w) := by
    intro v w p
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih =>
      exact (hadj _ _ ((owx_molGraph_adj Γ _ _).1 h).2).trans ih
  let ψ : Γ.Mol → Γ'.Mol :=
    SimpleGraph.ConnectedComponent.lift (fun v => Γ'.molOf (φ v))
      (fun _ _ p _ => SimpleGraph.ConnectedComponent.eq.2 (hwalk p))
  have hψmk : ∀ v, ψ (Γ.molOf v) = Γ'.molOf (φ v) := fun v => rfl
  have hψ : Function.Surjective ψ := by
    intro c'
    induction c' using SimpleGraph.ConnectedComponent.ind with | h v' => ?_
    obtain ⟨v, hv⟩ := hφ v'
    exact ⟨Γ.molOf v, (SimpleGraph.ConnectedComponent.eq.2 hv).symm⟩
  have hint : ∀ c' : Γ'.Mol, ¬ Γ'.IsExtMol c' → ¬ Γ.IsExtMol (Function.surjInv hψ c') := by
    rintro c' hc' ⟨a, ha⟩
    apply hc'
    obtain ⟨a', ha'⟩ := hl a
    refine ⟨a', ?_⟩
    have h1 : ψ (Γ.molOf (Sum.inl a)) = c' := by
      rw [ha]; exact Function.surjInv_eq hψ c'
    rw [hψmk, ha'] at h1
    exact h1
  let g : {c' : Γ'.Mol // ¬ Γ'.IsExtMol c'} → {c : Γ.Mol // ¬ Γ.IsExtMol c} :=
    fun c' => ⟨Function.surjInv hψ c'.1, hint c'.1 c'.2⟩
  have hg : Function.Injective g := by
    intro c₁ c₂ h
    apply Subtype.ext
    have := congrArg (fun c : {c : Γ.Mol // ¬ Γ.IsExtMol c} => ψ c.1) h
    simpa [g, Function.surjInv_eq hψ] using this
  exact Nat.card_le_card_of_injective g hg

/-- **A term of the dotted edge partition has at most as many internal molecules as the graph** (the molecules of the
graph map onto those of the merged graph; the waved edges stay, the `=`-dotted ones are merged). -/
theorem lvl1_part_nM (m : ℂ) (Δ : LGraph E₁ I₁) (P : PGraph E₁) (hP : P ∈ Δ.partition m) : P.g.nM ≤ Δ.nM := by
  classical
  obtain ⟨vm, d, hsurj, hl, hsep, hdoteq, hwav, hsplit⟩ := lvl1_part_struct m Δ P hP
  refine lvl1_nM_le Δ P.g vm (fun v' => ?_) (fun a => ⟨_, hl a⟩) (fun u v h => ?_)
  · obtain ⟨v, hv⟩ := hsurj v'
    exact ⟨v, by rw [hv]⟩
  · by_cases huv : vm u = vm v
    · rw [huv]
    · refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨huv, ?_⟩)
      simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h ⊢
      rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
      · left
        refine ⟨WEdge.map vm e, ?_, ?_⟩
        · rw [hwav]; exact List.mem_map_of_mem he
        · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; simp [WEdge.map, h1, h2]
          · right; simp [WEdge.map, h1, h2]
      · exfalso
        apply huv
        have := hdoteq e he h1
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; exact this
        · rw [← h1, ← h2]; exact this.symm

end NM
end PartStruct

section K1
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- loops of a graph (the weights and light-weights of `Γ`) -/
def LGraph.lvl1NLoops {E I : Type*} (Γ : LGraph E I) [DecidableEq E] [DecidableEq I] : ℕ := lvl1Loops Γ.solid

/-- the number of pairs of solid edges with a common internal end -/
def LGraph.lvl1NPairs {E I : Type*} (Γ : LGraph E I) [DecidableEq E] [DecidableEq I] : ℕ := lvl1Pairs Sum.isRight Γ.solid

/-- the edge has an end at `a₀` -/
def lvl1IncA {V : Type*} [DecidableEq V] (a₀ : V) (e : SEdge V) : Bool := decide (e.src = a₀) || decide (e.dst = a₀)

/-- the edge is collapsed by the vertex map -/
def lvl1Col {V W : Type*} [DecidableEq W] (vm : V → W) (e : SEdge V) : Bool := decide (vm e.src = vm e.dst) && !e.circ

private theorem lvl1_loops_split_col {V W : Type*} [DecidableEq W] (vm : V → W) (N : List (SEdge V))
    (hc : ∀ e ∈ N, e.circ = true → vm e.src = vm e.dst) :
    N.countP (fun e => decide (vm e.src = vm e.dst)) =
      N.countP (fun e => e.circ) + N.countP (lvl1Col vm) := by
  induction N with
  | nil => rfl
  | cons e N ih =>
    have ih' := ih (fun e' he' => hc e' (List.mem_cons_of_mem _ he'))
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih']
    by_cases h : e.circ = true
    · have hl := hc e List.mem_cons_self h
      have : lvl1Col vm e = false := by simp [lvl1Col, h]
      rw [this]
      simp [h, hl]
      omega
    · have h' : e.circ = false := by simpa using h
      have : lvl1Col vm e = decide (vm e.src = vm e.dst) := by simp [lvl1Col, h']
      rw [this]
      simp [h']
      omega

open Classical in
private theorem lvl1_col_bound {V W : Type*} [DecidableEq V] [DecidableEq W] (vm : V → W) (a₀ : V) (N : List (SEdge V))
    (hα : ∀ e ∈ N, e.circ = false → (e.src = a₀ ∨ e.dst = a₀) → e.src ≠ e.dst) :
    N.countP (lvl1Col vm) ≤
      (if ∃ b, b ≠ a₀ ∧ vm b = vm a₀ then N.countP (fun e => !e.circ && lvl1IncA a₀ e) else 0) +
      N.countP (fun e => !e.circ && !lvl1IncA a₀ e) := by
  by_cases hμ : ∃ b, b ≠ a₀ ∧ vm b = vm a₀
  · simp only [hμ, if_true]
    induction N with
    | nil => simp
    | cons e N ih =>
      have ih' := ih (fun e' he' => hα e' (List.mem_cons_of_mem _ he'))
      rw [List.countP_cons, List.countP_cons, List.countP_cons]
      by_cases hc : e.circ = false
      · by_cases hi : lvl1IncA a₀ e = true
        · simp only [lvl1Col, hc, hi, Bool.not_false, Bool.and_true, Bool.true_and, Bool.not_true, Bool.and_false,
            decide_eq_true_eq, ite_true]
          split_ifs <;> omega
        · have hi' : lvl1IncA a₀ e = false := by simpa using hi
          simp only [lvl1Col, hc, hi', Bool.not_false, Bool.and_true, Bool.true_and, Bool.not_true, Bool.and_false,
            decide_eq_true_eq, ite_true, Bool.false_and]
          split_ifs <;> omega
      · have hc' : e.circ = true := by simpa using hc
        simp only [lvl1Col, hc', Bool.not_true, Bool.and_false, Bool.false_and]
        simp only [Bool.false_eq_true, ite_false]
        omega
  · simp only [hμ, if_false, zero_add]
    induction N with
    | nil => simp
    | cons e N ih =>
      have ih' := ih (fun e' he' => hα e' (List.mem_cons_of_mem _ he'))
      rw [List.countP_cons, List.countP_cons]
      by_cases hc : e.circ = false
      · by_cases hi : lvl1IncA a₀ e = true
        · have hi2 : e.src = a₀ ∨ e.dst = a₀ := by simpa [lvl1IncA] using hi
          have hne := hα e List.mem_cons_self hc hi2
          have hnc : ¬ (vm e.src = vm e.dst) := by
            intro hv
            apply hμ
            rcases hi2 with hi2 | hi2
            · exact ⟨e.dst, fun h => hne (hi2.trans h.symm), by rw [← hv, hi2]⟩
            · exact ⟨e.src, fun h => hne (h.trans hi2.symm), by rw [hv, hi2]⟩
          have : lvl1Col vm e = false := by simp [lvl1Col, hnc]
          rw [this]
          simp only [hc, hi, Bool.not_false, Bool.true_and, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
          omega
        · have hi' : lvl1IncA a₀ e = false := by simpa using hi
          simp only [lvl1Col, hc, hi', Bool.not_false, Bool.true_and, Bool.not_true, Bool.and_true, Bool.and_false]
          split_ifs <;> omega
      · have hc' : e.circ = true := by simpa using hc
        simp only [lvl1Col, hc', Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false]
        omega


variable {I₀ : Type} [Fintype I₀] [DecidableEq I₀]

/-- **The counting facts for a term of the dotted edge partition with one special new vertex `a`**: `N` are the new
edges, each light-weight (circled edge) a loop; the new edges at `a` are non-loops.  `L` vertices are lost, `d` weights
are dropped, `cnc` edges of `N` collapse; the edges at `a` collapse only if `a` is merged, which loses `a`. -/
theorem lvl1_k1 (m : ℂ) (Γ : LGraph E I₀) (emb : E ⊕ I₀ → E ⊕ I) (hemb : Function.Injective emb)
    (R : List (SEdge (E ⊕ I₀))) (N : List (SEdge (E ⊕ I)))
    (hR : ∀ e ∈ R, (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true))
    (Δ : LGraph E I) (hsol : Δ.solid.Perm (R.map (SEdge.map emb) ++ N))
    (hdot : Δ.dotted = Γ.dotted.map (DEdge.map emb)) (a : I)
    (hcirc : ∀ e ∈ N, e.circ = true → e.src = e.dst)
    (hα : ∀ e ∈ N, e.circ = false → (e.src = Sum.inr a ∨ e.dst = Sum.inr a) → e.src ≠ e.dst)
    (P : PGraph E) (hP : P ∈ Δ.partition m) :
    ∃ L d cnc : ℕ, P.g.nS + d = Δ.nS ∧ P.g.nW = Δ.nW ∧ P.g.nV + L = Δ.nV ∧
      P.g.lvl1NLoops + d = lvl1Loops R + N.countP (fun e => e.circ) + cnc ∧ d ≤ cnc ∧
      cnc ≤ N.countP (fun e => !e.circ && lvl1IncA (Sum.inr a) e) +
        N.countP (fun e => !e.circ && !lvl1IncA (Sum.inr a) e) ∧
      (L = 0 → cnc ≤ N.countP (fun e => !e.circ && !lvl1IncA (Sum.inr a) e)) ∧
      ((∀ e ∈ N, e.circ = false → lvl1IncA (Sum.inr a) e = false →
          e.src ≠ e.dst ∧ (e.src.isRight = true ∨ e.dst.isRight = true)) → L = 0 → cnc = 0) ∧
      (L = 0 → P.g.lvl1NPairs = Δ.lvl1NPairs) ∧ P.g.nM ≤ Δ.nM := by
  classical
  obtain ⟨vm, d, hsurj, hl, hnS, hnW, hnV, hloops, hd, hpairs⟩ := lvl1_master m Γ emb hemb R N hR Δ hsol hdot P hP
  have hnV0 : P.g.nV ≤ Δ.nV := by simpa using hnV ∅ (by simp)
  refine ⟨Δ.nV - P.g.nV, d, N.countP (lvl1Col vm), hnS, hnW, by omega, ?_, hd, ?_, ?_, ?_, ?_, lvl1_part_nM m Δ P hP⟩
  · have hc' : ∀ e ∈ N, e.circ = true → vm e.src = vm e.dst := fun e he h => by rw [hcirc e he h]
    have := lvl1_loops_split_col vm N hc'
    unfold LGraph.lvl1NLoops
    omega
  · have h1 := lvl1_col_bound vm (Sum.inr a) N hα
    split_ifs at h1 <;> omega
  · intro hL
    have h1 := lvl1_col_bound vm (Sum.inr a) N hα
    have hnμ : ¬ ∃ b, b ≠ Sum.inr a ∧ vm b = vm (Sum.inr a) := by
      rintro ⟨b, hb, hvb⟩
      have := hnV {a} (by
        intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨b, by simpa using hb, hvb.symm⟩)
      simp only [Finset.card_singleton] at this
      omega
    simp only [hnμ, if_false, zero_add] at h1
    exact h1
  · intro hoo hL
    have hdom : ∀ (i : I) (b : E ⊕ I), b ≠ Sum.inr i → vm (Sum.inr i) = vm b → False := by
      intro i b hb hvb
      have := hnV {i} (by
        intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨b, by simpa using hb, hvb⟩)
      simp only [Finset.card_singleton] at this
      omega
    rw [List.countP_eq_zero]
    intro e he hcol
    simp only [lvl1Col, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcol
    obtain ⟨hv, hc⟩ := hcol
    by_cases hi : lvl1IncA (Sum.inr a) e = true
    · have hi2 : e.src = Sum.inr a ∨ e.dst = Sum.inr a := by simpa [lvl1IncA] using hi
      have hne := hα e he hc hi2
      rcases hi2 with hi2 | hi2
      · exact hdom a e.dst (fun h => hne (hi2.trans h.symm)) (by rw [← hi2]; exact hv)
      · exact hdom a e.src (fun h => hne (h.trans hi2.symm)) (by rw [← hi2]; exact hv.symm)
    · have hi' : lvl1IncA (Sum.inr a) e = false := by simpa using hi
      obtain ⟨hne, hint⟩ := hoo e he hc hi'
      rcases hint with h | h
      · rcases hs : e.src with b | j
        · rw [hs] at h; simp at h
        · exact hdom j e.dst (fun h2 => hne (by rw [hs, h2])) (by rw [← hs]; exact hv)
      · rcases hs : e.dst with b | j
        · rw [hs] at h; simp at h
        · exact hdom j e.src (fun h2 => hne (by rw [hs, ← h2])) (by rw [← hs]; exact hv.symm)
  · intro hL
    have := hpairs (by omega)
    exact this


section K2

/-- the edge joins `a₀` to a vertex outside `{a₀, b₀}` -/
def lvl1OldA {V : Type*} [DecidableEq V] (a₀ b₀ : V) (e : SEdge V) : Bool :=
  decide ((e.src = a₀ ∧ e.dst ≠ a₀ ∧ e.dst ≠ b₀) ∨ (e.dst = a₀ ∧ e.src ≠ a₀ ∧ e.src ≠ b₀))

/-- the edge joins `a₀` and `b₀` -/
def lvl1AB {V : Type*} [DecidableEq V] (a₀ b₀ : V) (e : SEdge V) : Bool :=
  decide ((e.src = a₀ ∧ e.dst = b₀) ∨ (e.src = b₀ ∧ e.dst = a₀))

private theorem lvl1_col_split3 {V W : Type*} [DecidableEq V] [DecidableEq W] (vm : V → W) (a₀ b₀ : V)
    (hab : a₀ ≠ b₀) (N : List (SEdge V))
    (hnc : ∀ e ∈ N, e.circ = false → e.src ≠ e.dst ∧ (e.src = a₀ ∨ e.dst = a₀ ∨ e.src = b₀ ∨ e.dst = b₀)) :
    N.countP (lvl1Col vm) = N.countP (fun e => lvl1Col vm e && lvl1OldA a₀ b₀ e) +
      N.countP (fun e => lvl1Col vm e && lvl1OldA b₀ a₀ e) + N.countP (fun e => lvl1Col vm e && lvl1AB a₀ b₀ e) := by
  induction N with
  | nil => rfl
  | cons e N ih =>
    have ih' := ih (fun e' he' => hnc e' (List.mem_cons_of_mem _ he'))
    rw [List.countP_cons, List.countP_cons, List.countP_cons, List.countP_cons, ih']
    by_cases hc : e.circ = false
    · obtain ⟨hne, hT⟩ := hnc e List.mem_cons_self hc
      have key : (lvl1OldA a₀ b₀ e = true ∧ lvl1OldA b₀ a₀ e = false ∧ lvl1AB a₀ b₀ e = false) ∨
          (lvl1OldA a₀ b₀ e = false ∧ lvl1OldA b₀ a₀ e = true ∧ lvl1AB a₀ b₀ e = false) ∨
          (lvl1OldA a₀ b₀ e = false ∧ lvl1OldA b₀ a₀ e = false ∧ lvl1AB a₀ b₀ e = true) := by
        by_cases h1 : e.src = a₀ <;> by_cases h2 : e.dst = a₀ <;> by_cases h3 : e.src = b₀ <;>
          by_cases h4 : e.dst = b₀ <;> simp_all [lvl1OldA, lvl1AB]
      rcases key with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ <;> rw [k1, k2, k3] <;>
        simp only [Bool.and_true, Bool.and_false, Bool.false_eq_true, ite_false] <;> split_ifs <;> omega
    · have hc' : e.circ = true := by simpa using hc
      have : lvl1Col vm e = false := by simp [lvl1Col, hc']
      rw [this]
      simp


/-- **The counting facts for a term with two special new vertices `a ≠ b`** (`T4`, `R8`): every new edge that is not a
light-weight joins `a` or `b` to another vertex; with at most two new edges at `a`, at most two at `b`, at most four
in all, the dropped weights number at most twice the lost vertices. -/
theorem lvl1_k2 (m : ℂ) (Γ : LGraph E I₀) (emb : E ⊕ I₀ → E ⊕ I) (hemb : Function.Injective emb)
    (R : List (SEdge (E ⊕ I₀))) (N : List (SEdge (E ⊕ I)))
    (hR : ∀ e ∈ R, (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true))
    (Δ : LGraph E I) (hsol : Δ.solid.Perm (R.map (SEdge.map emb) ++ N))
    (hdot : Δ.dotted = Γ.dotted.map (DEdge.map emb)) (a b : I) (hab : a ≠ b)
    (hnc : ∀ e ∈ N, e.circ = false → e.src ≠ e.dst ∧
      (e.src = Sum.inr a ∨ e.dst = Sum.inr a ∨ e.src = Sum.inr b ∨ e.dst = Sum.inr b))
    (hA : N.countP (fun e => !e.circ && lvl1OldA (Sum.inr a) (Sum.inr b) e) ≤ 2)
    (hB : N.countP (fun e => !e.circ && lvl1OldA (Sum.inr b) (Sum.inr a) e) ≤ 2)
    (hAB : N.countP (fun e => !e.circ && lvl1AB (Sum.inr a) (Sum.inr b) e) ≤ 2)
    (hsum : N.countP (fun e => !e.circ && lvl1OldA (Sum.inr a) (Sum.inr b) e) +
      N.countP (fun e => !e.circ && lvl1OldA (Sum.inr b) (Sum.inr a) e) +
      N.countP (fun e => !e.circ && lvl1AB (Sum.inr a) (Sum.inr b) e) ≤ 4)
    (P : PGraph E) (hP : P ∈ Δ.partition m) :
    ∃ L d : ℕ, P.g.nS + d = Δ.nS ∧ P.g.nW = Δ.nW ∧ P.g.nV + L = Δ.nV ∧ d ≤ 2 * L ∧ P.g.nM ≤ Δ.nM := by
  classical
  obtain ⟨vm, d, hsurj, hl, hnS, hnW, hnV, hloops, hd, hpairs⟩ := lvl1_master m Γ emb hemb R N hR Δ hsol hdot P hP
  have hnV0 : P.g.nV ≤ Δ.nV := by simpa using hnV ∅ (by simp)
  refine ⟨Δ.nV - P.g.nV, d, hnS, hnW, by omega, ?_, lvl1_part_nM m Δ P hP⟩
  have hnab : Sum.inr a ≠ (Sum.inr b : E ⊕ I) := fun h => hab (Sum.inr_injective h)
  have hsplit := lvl1_col_split3 vm (Sum.inr a) (Sum.inr b) hnab N hnc
  have hmono : ∀ (p q : SEdge (E ⊕ I) → Bool), (∀ e, p e = true → q e = true) → N.countP p ≤ N.countP q :=
    fun p q h => List.countP_mono_left fun e _ he => h e he
  have hCa : N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr a) (Sum.inr b) e) ≤ 2 :=
    le_trans (hmono _ _ fun e he => by simp only [lvl1Col, Bool.and_eq_true] at he ⊢; simp_all) hA
  have hCb : N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr b) (Sum.inr a) e) ≤ 2 :=
    le_trans (hmono _ _ fun e he => by simp only [lvl1Col, Bool.and_eq_true] at he ⊢; simp_all) hB
  have hCab : N.countP (fun e => lvl1Col vm e && lvl1AB (Sum.inr a) (Sum.inr b) e) ≤ 2 :=
    le_trans (hmono _ _ fun e he => by simp only [lvl1Col, Bool.and_eq_true] at he ⊢; simp_all) hAB
  have hCsum : N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr a) (Sum.inr b) e) +
      N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr b) (Sum.inr a) e) +
      N.countP (fun e => lvl1Col vm e && lvl1AB (Sum.inr a) (Sum.inr b) e) ≤ 4 := by
    have h1 := hmono (fun e => lvl1Col vm e && lvl1OldA (Sum.inr a) (Sum.inr b) e)
      (fun e => !e.circ && lvl1OldA (Sum.inr a) (Sum.inr b) e) fun e he => by
        simp only [lvl1Col, Bool.and_eq_true] at he ⊢; simp_all
    have h2 := hmono (fun e => lvl1Col vm e && lvl1OldA (Sum.inr b) (Sum.inr a) e)
      (fun e => !e.circ && lvl1OldA (Sum.inr b) (Sum.inr a) e) fun e he => by
        simp only [lvl1Col, Bool.and_eq_true] at he ⊢; simp_all
    have h3 := hmono (fun e => lvl1Col vm e && lvl1AB (Sum.inr a) (Sum.inr b) e)
      (fun e => !e.circ && lvl1AB (Sum.inr a) (Sum.inr b) e) fun e he => by
        simp only [lvl1Col, Bool.and_eq_true] at he ⊢; simp_all
    omega
  -- merging facts
  have hFa : 0 < N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr a) (Sum.inr b) e) →
      ∃ x, x ≠ Sum.inr a ∧ x ≠ Sum.inr b ∧ vm x = vm (Sum.inr a) := by
    intro h
    obtain ⟨e, he, h1⟩ := List.countP_pos_iff.1 h
    simp only [lvl1Col, lvl1OldA, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    obtain ⟨⟨hv, hc⟩, ho⟩ := h1
    rcases ho with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨e.dst, h2, h3, by rw [← hv, h1]⟩
    · exact ⟨e.src, h2, h3, by rw [hv, h1]⟩
  have hFb : 0 < N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr b) (Sum.inr a) e) →
      ∃ x, x ≠ Sum.inr a ∧ x ≠ Sum.inr b ∧ vm x = vm (Sum.inr b) := by
    intro h
    obtain ⟨e, he, h1⟩ := List.countP_pos_iff.1 h
    simp only [lvl1Col, lvl1OldA, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    obtain ⟨⟨hv, hc⟩, ho⟩ := h1
    rcases ho with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨e.dst, h3, h2, by rw [← hv, h1]⟩
    · exact ⟨e.src, h3, h2, by rw [hv, h1]⟩
  have hFab : 0 < N.countP (fun e => lvl1Col vm e && lvl1AB (Sum.inr a) (Sum.inr b) e) →
      vm (Sum.inr a) = vm (Sum.inr b) := by
    intro h
    obtain ⟨e, he, h1⟩ := List.countP_pos_iff.1 h
    simp only [lvl1Col, lvl1AB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    obtain ⟨⟨hv, hc⟩, ho⟩ := h1
    rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hv
    · rw [← h1, ← h2]; exact hv.symm
  -- the lost vertices
  have hL1 : ∀ (i : I) (z : E ⊕ I), z ≠ Sum.inr i → vm (Sum.inr i) = vm z → Δ.nV ≥ P.g.nV + 1 := by
    intro i z hz hvz
    have := hnV {i} (by
      intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      exact ⟨z, by simpa using hz, hvz⟩)
    simpa using this
  have hL2 : ∀ x y : E ⊕ I, x ≠ Sum.inr a → x ≠ Sum.inr b → y ≠ Sum.inr a → y ≠ Sum.inr b →
      vm x = vm (Sum.inr a) → vm y = vm (Sum.inr b) → Δ.nV ≥ P.g.nV + 2 := by
    intro x y hx1 hx2 hy1 hy2 hxv hyv
    have := hnV {a, b} (by
      intro j hj
      rw [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact ⟨x, by intro j hj; rw [Finset.mem_insert, Finset.mem_singleton] at hj
                     rcases hj with rfl | rfl <;> simp_all, hxv.symm⟩
      · exact ⟨y, by intro j hj; rw [Finset.mem_insert, Finset.mem_singleton] at hj
                     rcases hj with rfl | rfl <;> simp_all, hyv.symm⟩)
    rw [Finset.card_pair hab] at this
    omega
  have e1 : 0 < N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr a) (Sum.inr b) e) → Δ.nV ≥ P.g.nV + 1 :=
    fun h => by
      obtain ⟨x, hx1, hx2, hxv⟩ := hFa h
      exact hL1 a x hx1 hxv.symm
  have e2 : 0 < N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr b) (Sum.inr a) e) → Δ.nV ≥ P.g.nV + 1 :=
    fun h => by
      obtain ⟨x, hx1, hx2, hxv⟩ := hFb h
      exact hL1 b x hx2 hxv.symm
  have e3 : 0 < N.countP (fun e => lvl1Col vm e && lvl1AB (Sum.inr a) (Sum.inr b) e) → Δ.nV ≥ P.g.nV + 1 :=
    fun h => hL1 a (Sum.inr b) (fun h' => hab (Sum.inr_injective h'.symm)) (hFab h)
  have e12 : 0 < N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr a) (Sum.inr b) e) →
      0 < N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr b) (Sum.inr a) e) → Δ.nV ≥ P.g.nV + 2 :=
    fun h h' => by
      obtain ⟨x, hx1, hx2, hxv⟩ := hFa h
      obtain ⟨y, hy1, hy2, hyv⟩ := hFb h'
      exact hL2 x y hx1 hx2 hy1 hy2 hxv hyv
  have e13 : 0 < N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr a) (Sum.inr b) e) →
      0 < N.countP (fun e => lvl1Col vm e && lvl1AB (Sum.inr a) (Sum.inr b) e) → Δ.nV ≥ P.g.nV + 2 :=
    fun h h' => by
      obtain ⟨x, hx1, hx2, hxv⟩ := hFa h
      have hab' := hFab h'
      exact hL2 x x hx1 hx2 hx1 hx2 hxv (by rw [hxv, hab'])
  have e23 : 0 < N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr b) (Sum.inr a) e) →
      0 < N.countP (fun e => lvl1Col vm e && lvl1AB (Sum.inr a) (Sum.inr b) e) → Δ.nV ≥ P.g.nV + 2 :=
    fun h h' => by
      obtain ⟨y, hy1, hy2, hyv⟩ := hFb h
      have hab' := hFab h'
      exact hL2 y y hy1 hy2 hy1 hy2 (by rw [hyv, hab']) hyv
  have hcnc : N.countP (lvl1Col vm) = N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr a) (Sum.inr b) e) +
      N.countP (fun e => lvl1Col vm e && lvl1OldA (Sum.inr b) (Sum.inr a) e) +
      N.countP (fun e => lvl1Col vm e && lvl1AB (Sum.inr a) (Sum.inr b) e) := hsplit
  have hd' : d ≤ N.countP (lvl1Col vm) := hd
  omega

end K2
end K1

section TwistHelpers

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lvl1_twistS_map (c t : Bool) {V W : Type*} (f : V → W) (e : SEdge V) :
    lwSymmTwistS c t (SEdge.map f e) = SEdge.map f (lwSymmTwistS c t e) := by
  cases c <;> cases t <;> rfl

theorem lvl1_twist_owxExt_solid (c t : Bool) {I' : Type*} (Γ' : LGraph E I) (emb : E ⊕ I → E ⊕ I') (cc : ℂ)
    (N : List (SEdge (E ⊕ I'))) (W : List (WEdge (E ⊕ I'))) :
    (lwSymmTwistG c t (Γ'.owxExt emb cc N W)).solid =
      (Γ'.solid.map (lwSymmTwistS c t)).map (SEdge.map emb) ++ N.map (lwSymmTwistS c t) := by
  rw [lwSymmTwistG_solid]
  simp only [LGraph.owxExt, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact lvl1_twistS_map c t emb e

theorem lvl1_twist_owxExt_dotted (c t : Bool) {I' : Type*} (Γ' : LGraph E I) (emb : E ⊕ I → E ⊕ I') (cc : ℂ)
    (N : List (SEdge (E ⊕ I'))) (W : List (WEdge (E ⊕ I'))) :
    (lwSymmTwistG c t (Γ'.owxExt emb cc N W)).dotted = Γ'.dotted.map (DEdge.map emb) := by
  rw [lwSymmTwistG_dotted]; rfl

theorem lvl1_twist_twist_list {V : Type*} (c t : Bool) (l : List (SEdge V)) :
    (l.map (lwSymmTwistS c t)).map (lwSymmTwistS c t) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun e _ => lwSymmTwistS_invol c t e

theorem lvl1_incA_twist {V : Type*} [DecidableEq V] (c t : Bool) (a₀ : V) (e : SEdge V) :
    lvl1IncA a₀ (lwSymmTwistS c t e) = lvl1IncA a₀ e := by
  rw [lwSymmTwistS_eq]
  cases t <;> simp [lvl1IncA, Bool.or_comm]

theorem lvl1_col_twist {V W : Type*} [DecidableEq W] (c t : Bool) (vm : V → W) (e : SEdge V) :
    lvl1Col vm (lwSymmTwistS c t e) = lvl1Col vm e := by
  rw [lwSymmTwistS_eq]
  cases t <;> simp [lvl1Col, eq_comm]

theorem lvl1_countP_twist {V : Type*} (c t : Bool) (p : SEdge V → Bool)
    (hp : ∀ e, p (lwSymmTwistS c t e) = p e) (N : List (SEdge V)) :
    (N.map (lwSymmTwistS c t)).countP p = N.countP p := by
  rw [List.countP_map]
  exact List.countP_congr fun e _ => by simp [Function.comp_apply, hp e]

end TwistHelpers

section Good

variable {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁]
  [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]

/-- **`Q` is a good output for the input `Γ`** (the one-step claims of `strat_local`): the scaling order does not fall,
`n_M` and `n_V - n_W` do not grow, and either the order rises or it stays and the measure
`(n_loops, n_S, n_pairs)` falls lexicographically. -/
def Lvl1Good (Γ : LGraph E₁ I₁) (Q : LGraph E₂ I₂) : Prop :=
  ord Γ.counters ≤ ord Q.counters ∧ Q.nM ≤ Γ.nM ∧ ((Q.nV : ℤ) - Q.nW ≤ (Γ.nV : ℤ) - Γ.nW) ∧
    (ord Γ.counters < ord Q.counters ∨ (ord Q.counters = ord Γ.counters ∧
      (Q.lvl1NLoops < Γ.lvl1NLoops ∨ (Q.lvl1NLoops = Γ.lvl1NLoops ∧ (Q.nS < Γ.nS ∨ (Q.nS = Γ.nS ∧ Q.lvl1NPairs < Γ.lvl1NPairs))))))

end Good
end RBM.Graph
end Lvl1PartA

/-! ## 2. Support conditions and edges of the terms of the three expansions -/

section Lvl1PartB
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Terms

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the edges of a normal graph satisfy the support conditions of the master lemma -/
theorem lvl1_hR_of_normal (Γ : LGraph E I) (hN : Γ.Normal) (R : List (SEdge (E ⊕ I)))
    (hR : ∀ e ∈ R, e ∈ Γ.solid) :
    ∀ e ∈ R, (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true) := by
  intro e he
  refine ⟨fun hne => ?_, hN.2.2 e (hR e he)⟩
  exact (hN.2.1 _ _ hne).2 ⟨e, hR e he, hne, Or.inl ⟨rfl, rfl⟩⟩

theorem lvl1_mem_split {κ : Type*} (l : List κ) (p : κ × List κ) (hp : p ∈ lwSplit l) :
    ∀ e ∈ p.2, e ∈ l := fun e he =>
  (lwSplit_perm l p hp).mem_iff.2 (List.mem_cons_of_mem _ he)

theorem lvl1_mem_split_fst {κ : Type*} (l : List κ) (p : κ × List κ) (hp : p ∈ lwSplit l) : p.1 ∈ l :=
  (lwSplit_perm l p hp).mem_iff.2 List.mem_cons_self

theorem lvl1_owxEmb_ne (v : E ⊕ I) (j : Fin 1) :
    owxEmb 1 v ≠ (Sum.inr (Sum.inr j) : E ⊕ (I ⊕ Fin 1)) := fun h => lwSymm_emb_ne v 1 j h.symm

theorem lvl1_owxEmb_inj (k : ℕ) : Function.Injective (owxEmb k : E ⊕ I → E ⊕ (I ⊕ Fin k)) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp [owxEmb] at h ⊢ <;> exact h


/-- **The three edges of a derivative term** (`T3`, `oe1xD`, `R7`): the two edges of `∂_{h_{αw}}` of the old edge `e0`
and the edge `G_{αz}`: all non-circled, the edges at `α` are non-loops, two of them are at `α` and one is not. -/
theorem lvl1_derivNf {V : Type*} [DecidableEq V] (α w z : V) (e0 : SEdge V)
    (h1 : e0.src ≠ α) (h2 : e0.dst ≠ α) (hw : w ≠ α) (hz : z ≠ α) :
    (∀ e ∈ [(owxDE α w e0).1, (owxDE α w e0).2, (⟨true, false, α, z⟩ : SEdge V)], e.circ = false) ∧
    (∀ e ∈ [(owxDE α w e0).1, (owxDE α w e0).2, (⟨true, false, α, z⟩ : SEdge V)],
      (e.src = α ∨ e.dst = α) → e.src ≠ e.dst) ∧
    ([(owxDE α w e0).1, (owxDE α w e0).2, (⟨true, false, α, z⟩ : SEdge V)].countP
        (fun e => !e.circ && lvl1IncA α e) = 2) ∧
    ([(owxDE α w e0).1, (owxDE α w e0).2, (⟨true, false, α, z⟩ : SEdge V)].countP
        (fun e => !e.circ && !lvl1IncA α e) = 1) := by
  have hα1 : ¬ (α = e0.src) := fun h => h1 h.symm
  have hα2 : ¬ (α = e0.dst) := fun h => h2 h.symm
  have hα3 : ¬ (α = w) := fun h => hw h.symm
  have hα4 : ¬ (α = z) := fun h => hz h.symm
  cases hσ : e0.σ <;> simp [owxDE, hσ, lvl1IncA, h1, h2, hw, hz, hα1, hα2, hα3, hα4, List.countP_cons]


theorem lvl1_loops_perm {V : Type*} [DecidableEq V] {l₁ l₂ : List (SEdge V)} (h : l₁.Perm l₂) :
    lvl1Loops l₁ = lvl1Loops l₂ := h.countP_eq _

theorem lvl1_loops_cons {V : Type*} [DecidableEq V] (e : SEdge V) (l : List (SEdge V)) :
    lvl1Loops (e :: l) = lvl1Loops l + (if e.src = e.dst then 1 else 0) := by
  simp [lvl1Loops, List.countP_cons]

/-- the loops of a normal graph with a weight `p.1` and an edge `q.1` removed -/
theorem lvl1_loops_split (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    Γ.lvl1NLoops = lvl1Loops q.2 + (if p.1.src = p.1.dst then 1 else 0) + (if q.1.src = q.1.dst then 1 else 0) := by
  unfold LGraph.lvl1NLoops
  rw [lvl1_loops_perm (lwSplit_perm Γ.solid p hp), lvl1_loops_cons,
    lvl1_loops_perm (lwSplit_perm p.2 q hq), lvl1_loops_cons]
  omega


theorem lvl1_oldA_twist {V : Type*} [DecidableEq V] (c t : Bool) (a₀ b₀ : V) (e : SEdge V) :
    lvl1OldA a₀ b₀ (lwSymmTwistS c t e) = lvl1OldA a₀ b₀ e := by
  rw [lwSymmTwistS_eq]
  cases t <;> simp [lvl1OldA, or_comm]

theorem lvl1_ab_twist {V : Type*} [DecidableEq V] (c t : Bool) (a₀ b₀ : V) (e : SEdge V) :
    lvl1AB a₀ b₀ (lwSymmTwistS c t e) = lvl1AB a₀ b₀ e := by
  rw [lwSymmTwistS_eq]
  unfold lvl1AB
  cases t
  · rfl
  · exact decide_eq_decide.2 (by simp only [ite_true]; tauto)

/-- **The three edges of a `T4` term**: the derivative pair with `(a, w) = (β, α)` and `G_{βα}`. -/
theorem lvl1_derivNf2 {V : Type*} [DecidableEq V] (α β : V) (hαβ : α ≠ β) (e0 : SEdge V)
    (h1 : e0.src ≠ α) (h2 : e0.dst ≠ α) (h3 : e0.src ≠ β) (h4 : e0.dst ≠ β) :
    (∀ e ∈ [(owxDE β α e0).1, (owxDE β α e0).2, (⟨true, false, β, α⟩ : SEdge V)], e.circ = false) ∧
    (∀ e ∈ [(owxDE β α e0).1, (owxDE β α e0).2, (⟨true, false, β, α⟩ : SEdge V)],
      e.src ≠ e.dst ∧ (e.src = α ∨ e.dst = α ∨ e.src = β ∨ e.dst = β)) ∧
    ([(owxDE β α e0).1, (owxDE β α e0).2, (⟨true, false, β, α⟩ : SEdge V)].countP
        (fun e => !e.circ && lvl1OldA α β e) = 1) ∧
    ([(owxDE β α e0).1, (owxDE β α e0).2, (⟨true, false, β, α⟩ : SEdge V)].countP
        (fun e => !e.circ && lvl1OldA β α e) = 1) ∧
    ([(owxDE β α e0).1, (owxDE β α e0).2, (⟨true, false, β, α⟩ : SEdge V)].countP
        (fun e => !e.circ && lvl1AB α β e) = 1) := by
  have hα1 : ¬ (α = e0.src) := fun h => h1 h.symm
  have hα2 : ¬ (α = e0.dst) := fun h => h2 h.symm
  have hβ1 : ¬ (β = e0.src) := fun h => h3 h.symm
  have hβ2 : ¬ (β = e0.dst) := fun h => h4 h.symm
  have hβα : ¬ (β = α) := fun h => hαβ h.symm
  cases hσ : e0.σ <;> simp [owxDE, hσ, lvl1OldA, lvl1AB, h1, h2, h3, h4, hα1, hα2, hβ1, hβ2, hαβ, hβα,
    List.countP_cons]

/-- **The four edges of an `R8` term**: `G_{βy}`, `G_{y'α}` and the derivative pair with `(a, w) = (β, α)`. -/
theorem lvl1_R8Nf {V : Type*} [DecidableEq V] (α β y y' : V) (hαβ : α ≠ β) (e0 : SEdge V)
    (h1 : e0.src ≠ α) (h2 : e0.dst ≠ α) (h3 : e0.src ≠ β) (h4 : e0.dst ≠ β)
    (hy1 : y ≠ α) (hy2 : y ≠ β) (hy'1 : y' ≠ α) (hy'2 : y' ≠ β) :
    (∀ e ∈ [(⟨true, false, β, y⟩ : SEdge V), ⟨true, false, y', α⟩, (owxDE β α e0).1, (owxDE β α e0).2],
      e.circ = false) ∧
    (∀ e ∈ [(⟨true, false, β, y⟩ : SEdge V), ⟨true, false, y', α⟩, (owxDE β α e0).1, (owxDE β α e0).2],
      e.src ≠ e.dst ∧ (e.src = α ∨ e.dst = α ∨ e.src = β ∨ e.dst = β)) ∧
    ([(⟨true, false, β, y⟩ : SEdge V), ⟨true, false, y', α⟩, (owxDE β α e0).1, (owxDE β α e0).2].countP
        (fun e => !e.circ && lvl1OldA α β e) = 2) ∧
    ([(⟨true, false, β, y⟩ : SEdge V), ⟨true, false, y', α⟩, (owxDE β α e0).1, (owxDE β α e0).2].countP
        (fun e => !e.circ && lvl1OldA β α e) = 2) ∧
    ([(⟨true, false, β, y⟩ : SEdge V), ⟨true, false, y', α⟩, (owxDE β α e0).1, (owxDE β α e0).2].countP
        (fun e => !e.circ && lvl1AB α β e) = 0) := by
  have hα1 : ¬ (α = e0.src) := fun h => h1 h.symm
  have hα2 : ¬ (α = e0.dst) := fun h => h2 h.symm
  have hβ1 : ¬ (β = e0.src) := fun h => h3 h.symm
  have hβ2 : ¬ (β = e0.dst) := fun h => h4 h.symm
  have hβα : ¬ (β = α) := fun h => hαβ h.symm
  have hyy1 : ¬ (α = y) := fun h => hy1 h.symm
  have hyy2 : ¬ (β = y) := fun h => hy2 h.symm
  have hyy3 : ¬ (α = y') := fun h => hy'1 h.symm
  have hyy4 : ¬ (β = y') := fun h => hy'2 h.symm
  cases hσ : e0.σ <;> simp [owxDE, hσ, lvl1OldA, lvl1AB, h1, h2, h3, h4, hα1, hα2, hβ1, hβ2, hαβ, hβα,
    hy1, hy2, hy'1, hy'2, hyy1, hyy2, hyy3, hyy4, List.countP_cons]


theorem lvl1_touch_twist {V : Type*} (c t : Bool) (e : SEdge V) (a b : V) :
    ((lwSymmTwistS c t e).src = a ∨ (lwSymmTwistS c t e).dst = a ∨ (lwSymmTwistS c t e).src = b ∨
        (lwSymmTwistS c t e).dst = b) ↔ (e.src = a ∨ e.dst = a ∨ e.src = b ∨ e.dst = b) := by
  rw [lwSymmTwistS_eq]
  cases t <;> simp <;> tauto


theorem lvl1_nS_of_sol {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (Δ : LGraph E' I') {V : Type*} (f : V → SEdge (E' ⊕ I')) (R : List V) (N : List (SEdge (E' ⊕ I')))
    (h : Δ.solid = R.map f ++ N) : Δ.nS = R.length + N.length := by
  simp [LGraph.nS, h]

theorem lvl1_frame_dotted (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame c t Γ p).dotted = Γ.dotted := by
  unfold lwSymmFrame
  rw [lwSymmTwistG_dotted]
  rfl

theorem lvl1_frame2_dotted (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame2 c t Γ p q).dotted = Γ.dotted := by
  unfold lwSymmFrame2
  rw [lwSymmTwistG_dotted]
  rfl

theorem lvl1_frame_solid_twist (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame c t Γ p).solid.map (lwSymmTwistS c t) = { p.1 with circ := false } :: p.2 := by
  unfold lwSymmFrame
  rw [lwSymmTwistG_solid, lvl1_twist_twist_list]
  rfl

theorem lvl1_frame2_solid_twist (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame2 c t Γ p q).solid.map (lwSymmTwistS c t) =
      { p.1 with circ := false } :: { q.1 with circ := false } :: q.2 := by
  unfold lwSymmFrame2
  rw [lwSymmTwistG_solid, lvl1_twist_twist_list]
  rfl

/-- the support conditions for `{p.1 with circ := false} :: p.2` (`p.1` a non-loop edge of a normal graph) -/
theorem lvl1_hR_uncirc (Γ : LGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hne : p.1.src ≠ p.1.dst) :
    ∀ e ∈ ({ p.1 with circ := false } :: p.2 : List (SEdge (E ⊕ I))),
      (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨fun _ => (hN.2.1 _ _ hne).2 ⟨p.1, lvl1_mem_split_fst _ p hp, hne, Or.inl ⟨rfl, rfl⟩⟩,
      fun h => absurd h hne⟩
  · exact lvl1_hR_of_normal Γ hN p.2 (lvl1_mem_split _ p hp) e he


theorem lvl1_isRight_twist {V W : Type*} (c t : Bool) (e : SEdge (V ⊕ W)) :
    ((lwSymmTwistS c t e).src.isRight = true ∨ (lwSymmTwistS c t e).dst.isRight = true) ↔
      (e.src.isRight = true ∨ e.dst.isRight = true) := by
  rw [lwSymmTwistS_eq]
  cases t <;> simp [or_comm]

/-- **The side condition `hoo` for a derivative term**: the old-old new edge is a non-loop with an internal end. -/
theorem lvl1_derivNf_hoo {E' I' : Type*} [DecidableEq E'] [DecidableEq I'] (α w z : E' ⊕ I') (e0 : SEdge (E' ⊕ I'))
    (h1 : e0.src ≠ α) (h2 : e0.dst ≠ α) (hwα : w ≠ α) (hzα : z ≠ α) (hwi : w.isRight = true)
    (hnb : (e0.σ = true → e0.dst ≠ w) ∧ (e0.σ = false → e0.src ≠ w)) :
    ∀ e ∈ [(owxDE α w e0).1, (owxDE α w e0).2, (⟨true, false, α, z⟩ : SEdge (E' ⊕ I'))],
      e.circ = false → lvl1IncA α e = false → e.src ≠ e.dst ∧ (e.src.isRight = true ∨ e.dst.isRight = true) := by
  have hα1 : ¬ (α = e0.src) := fun h => h1 h.symm
  have hα2 : ¬ (α = e0.dst) := fun h => h2 h.symm
  obtain ⟨hb1, hb2⟩ := hnb
  intro e he hc hi
  cases hσ : e0.σ
  · have hb := hb2 hσ
    simp only [owxDE, hσ, List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [Bool.false_eq_true, ↓reduceIte] at he
    rcases he with rfl | rfl | rfl
    · simp [lvl1IncA, h1, hb, hwi, hα1, hα2] at hi ⊢
    · simp [lvl1IncA, hα1] at hi
    · simp [lvl1IncA] at hi
  · have hb := hb1 hσ
    simp only [owxDE, hσ, List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [↓reduceIte] at he
    rcases he with rfl | rfl | rfl
    · simp [lvl1IncA] at hi
    · simp [lvl1IncA, h2, hb, hwi, hwα, hα2] at hi ⊢
      exact fun h => hb h.symm
    · simp [lvl1IncA] at hi

end Terms
end RBM.Graph
end Lvl1PartB

/-! ## 3. Good outputs of the generic shapes of a term -/

section Lvl1PartG
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Generic

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  {I₀ : Type} [Fintype I₀] [DecidableEq I₀]

/-- **Good outputs of a term with one special vertex, no old-old new edge, order raised by one** (`T1`, `T2`, `R3`,
`oe1x` `Owx`, `oe1xP5`, `oe1xP6`, `R4`, `R5`, `R6`). -/
theorem lvl1_good_k1a (m : ℂ) (Γ : LGraph E I₀) (emb : E ⊕ I₀ → E ⊕ I) (hemb : Function.Injective emb)
    (R : List (SEdge (E ⊕ I₀))) (N : List (SEdge (E ⊕ I)))
    (hR : ∀ e ∈ R, (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true))
    (Δ : LGraph E I) (hsol : Δ.solid.Perm (R.map (SEdge.map emb) ++ N))
    (hdot : Δ.dotted = Γ.dotted.map (DEdge.map emb)) (a : I)
    (hcirc : ∀ e ∈ N, e.circ = true → e.src = e.dst)
    (hα : ∀ e ∈ N, e.circ = false → (e.src = Sum.inr a ∨ e.dst = Sum.inr a) → e.src ≠ e.dst)
    (hA : N.countP (fun e => !e.circ && lvl1IncA (Sum.inr a) e) ≤ 2)
    (hO : N.countP (fun e => !e.circ && !lvl1IncA (Sum.inr a) e) = 0)
    (hord : ord Γ.counters + 1 ≤ ord Δ.counters) (hnM : Δ.nM ≤ Γ.nM)
    (hVW : (Δ.nV : ℤ) - Δ.nW ≤ (Γ.nV : ℤ) - Γ.nW)
    (P : PGraph E) (hP : P ∈ Δ.partition m) : Lvl1Good Γ P.g := by
  obtain ⟨L, d, cnc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    lvl1_k1 m Γ emb hemb R N hR Δ hsol hdot a hcirc hα P hP
  unfold Lvl1Good
  simp only [ord, LGraph.counters] at hord ⊢
  omega

/-- **Good outputs of a term with one special vertex and one old-old new edge, order raised by one** (`T3`, `oe1xD`,
`R7`, `R2`): the ties are those where the old-old edge collapses. -/
theorem lvl1_good_k1b (m : ℂ) (Γ : LGraph E I₀) (emb : E ⊕ I₀ → E ⊕ I) (hemb : Function.Injective emb)
    (R : List (SEdge (E ⊕ I₀))) (N : List (SEdge (E ⊕ I)))
    (hR : ∀ e ∈ R, (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true))
    (Δ : LGraph E I) (hsol : Δ.solid.Perm (R.map (SEdge.map emb) ++ N))
    (hdot : Δ.dotted = Γ.dotted.map (DEdge.map emb)) (a : I)
    (hcirc : ∀ e ∈ N, e.circ = true → e.src = e.dst)
    (hα : ∀ e ∈ N, e.circ = false → (e.src = Sum.inr a ∨ e.dst = Sum.inr a) → e.src ≠ e.dst)
    (hA : N.countP (fun e => !e.circ && lvl1IncA (Sum.inr a) e) ≤ 2)
    (hO : N.countP (fun e => !e.circ && !lvl1IncA (Sum.inr a) e) ≤ 1)
    (hC : N.countP (fun e => e.circ) = 0)
    (hord : ord Γ.counters + 1 ≤ ord Δ.counters) (hnM : Δ.nM ≤ Γ.nM)
    (hVW : (Δ.nV : ℤ) - Δ.nW ≤ (Γ.nV : ℤ) - Γ.nW)
    (hS : (Δ.nS : ℤ) ≤ Γ.nS + 1) (hw : lvl1Loops R ≤ Γ.lvl1NLoops)
    (htie : lvl1Loops R + 1 ≤ Γ.lvl1NLoops ∨ (Δ.nS : ℤ) ≤ Γ.nS ∨
      (∀ e ∈ N, e.circ = false → lvl1IncA (Sum.inr a) e = false →
        e.src ≠ e.dst ∧ (e.src.isRight = true ∨ e.dst.isRight = true)))
    (P : PGraph E) (hP : P ∈ Δ.partition m) : Lvl1Good Γ P.g := by
  obtain ⟨L, d, cnc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    lvl1_k1 m Γ emb hemb R N hR Δ hsol hdot a hcirc hα P hP
  rw [hC] at h4
  unfold Lvl1Good
  simp only [ord, LGraph.counters] at hord ⊢
  rcases htie with ht | ht | ht
  · omega
  · omega
  · have := h8 ht
    omega

/-- **Good outputs of a term with one special vertex whose order stays** (`oe1xP3`, `oe1xP4`): with no merge the term
is the graph itself, so the pairs decide. -/
theorem lvl1_good_k1c (m : ℂ) (Γ : LGraph E I₀) (emb : E ⊕ I₀ → E ⊕ I) (hemb : Function.Injective emb)
    (R : List (SEdge (E ⊕ I₀))) (N : List (SEdge (E ⊕ I)))
    (hR : ∀ e ∈ R, (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true))
    (Δ : LGraph E I) (hsol : Δ.solid.Perm (R.map (SEdge.map emb) ++ N))
    (hdot : Δ.dotted = Γ.dotted.map (DEdge.map emb)) (a : I)
    (hcirc : ∀ e ∈ N, e.circ = true → e.src = e.dst)
    (hα : ∀ e ∈ N, e.circ = false → (e.src = Sum.inr a ∨ e.dst = Sum.inr a) → e.src ≠ e.dst)
    (hA : N.countP (fun e => !e.circ && lvl1IncA (Sum.inr a) e) ≤ 2)
    (hO : N.countP (fun e => !e.circ && !lvl1IncA (Sum.inr a) e) = 0)
    (hC : N.countP (fun e => e.circ) = 0)
    (hord : ord Γ.counters ≤ ord Δ.counters) (hnM : Δ.nM ≤ Γ.nM)
    (hVW : (Δ.nV : ℤ) - Δ.nW ≤ (Γ.nV : ℤ) - Γ.nW)
    (hS : Δ.nS = Γ.nS) (hw : lvl1Loops R ≤ Γ.lvl1NLoops) (hpairs : Δ.lvl1NPairs < Γ.lvl1NPairs)
    (P : PGraph E) (hP : P ∈ Δ.partition m) : Lvl1Good Γ P.g := by
  obtain ⟨L, d, cnc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    lvl1_k1 m Γ emb hemb R N hR Δ hsol hdot a hcirc hα P hP
  rw [hC] at h4
  unfold Lvl1Good
  simp only [ord, LGraph.counters] at hord ⊢
  omega

/-- **Good outputs of a term with two special vertices, order raised by one** (`T4`, `R8`). -/
theorem lvl1_good_k2 (m : ℂ) (Γ : LGraph E I₀) (emb : E ⊕ I₀ → E ⊕ I) (hemb : Function.Injective emb)
    (R : List (SEdge (E ⊕ I₀))) (N : List (SEdge (E ⊕ I)))
    (hR : ∀ e ∈ R, (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true))
    (Δ : LGraph E I) (hsol : Δ.solid.Perm (R.map (SEdge.map emb) ++ N))
    (hdot : Δ.dotted = Γ.dotted.map (DEdge.map emb)) (a b : I) (hab : a ≠ b)
    (hnc : ∀ e ∈ N, e.circ = false → e.src ≠ e.dst ∧
      (e.src = Sum.inr a ∨ e.dst = Sum.inr a ∨ e.src = Sum.inr b ∨ e.dst = Sum.inr b))
    (hA : N.countP (fun e => !e.circ && lvl1OldA (Sum.inr a) (Sum.inr b) e) ≤ 2)
    (hB : N.countP (fun e => !e.circ && lvl1OldA (Sum.inr b) (Sum.inr a) e) ≤ 2)
    (hAB : N.countP (fun e => !e.circ && lvl1AB (Sum.inr a) (Sum.inr b) e) ≤ 2)
    (hsum : N.countP (fun e => !e.circ && lvl1OldA (Sum.inr a) (Sum.inr b) e) +
      N.countP (fun e => !e.circ && lvl1OldA (Sum.inr b) (Sum.inr a) e) +
      N.countP (fun e => !e.circ && lvl1AB (Sum.inr a) (Sum.inr b) e) ≤ 4)
    (hord : ord Γ.counters + 1 ≤ ord Δ.counters) (hnM : Δ.nM ≤ Γ.nM)
    (hVW : (Δ.nV : ℤ) - Δ.nW ≤ (Γ.nV : ℤ) - Γ.nW)
    (P : PGraph E) (hP : P ∈ Δ.partition m) : Lvl1Good Γ P.g := by
  obtain ⟨L, d, h1, h2, h3, h4, h5⟩ := lvl1_k2 m Γ emb hemb R N hR Δ hsol hdot a b hab hnc hA hB hAB hsum P hP
  unfold Lvl1Good
  simp only [ord, LGraph.counters] at hord ⊢
  omega

end Generic
end RBM.Graph
end Lvl1PartG

/-! ## 4. Pairs of solid edges with a common internal end under a pull -/

section Lvl1PartP
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Pairs

variable {V V' : Type*} [DecidableEq V] [DecidableEq V']

/-- the number of ends of the non-loop edge `e` at the vertex `u` -/
def lvl1Cnt (u : V) (e : SEdge V) : ℕ :=
  if e.src = e.dst then 0 else (if e.src = u then 1 else 0) + (if e.dst = u then 1 else 0)

/-- `1` for an internal vertex -/
def lvl1Iota (int : V → Bool) (u : V) : ℕ := if int u = true then 1 else 0

/-- the non-loop edges of `R` at `u` -/
def lvl1Deg (u : V) (R : List (SEdge V)) : ℕ := (R.map (lvl1Cnt u)).sum

theorem lvl1Share_cnt (int : V → Bool) (a e : SEdge V) (ha : a.src ≠ a.dst) :
    lvl1Share int a e = lvl1Iota int a.src * lvl1Cnt a.src e + lvl1Iota int a.dst * lvl1Cnt a.dst e := by
  unfold lvl1Share lvl1Cnt lvl1Iota
  by_cases he : e.src = e.dst
  · simp [he, ha]
  · simp only [ha, he, or_self, ite_false, mul_zero, zero_add]
    by_cases h1 : int a.src = true <;> by_cases h2 : int a.dst = true <;> simp [h1, h2, eq_comm]
    all_goals omega


theorem lvl1Share_ends (int : V → Bool) (a e : SEdge V) (u1 u2 : V) (ha : a.src ≠ a.dst)
    (hab : (a.src = u1 ∧ a.dst = u2) ∨ (a.src = u2 ∧ a.dst = u1)) :
    lvl1Share int a e = lvl1Iota int u1 * lvl1Cnt u1 e + lvl1Iota int u2 * lvl1Cnt u2 e := by
  rw [lvl1Share_cnt int a e ha]
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; ring

theorem lvl1Deg_cons (u : V) (e : SEdge V) (R : List (SEdge V)) : lvl1Deg u (e :: R) = lvl1Cnt u e + lvl1Deg u R := by
  simp [lvl1Deg]

theorem lvl1_sum_share (int : V → Bool) (a : SEdge V) (u1 u2 : V) (ha : a.src ≠ a.dst)
    (hab : (a.src = u1 ∧ a.dst = u2) ∨ (a.src = u2 ∧ a.dst = u1)) (R : List (SEdge V)) :
    (R.map (lvl1Share int a)).sum = lvl1Iota int u1 * lvl1Deg u1 R + lvl1Iota int u2 * lvl1Deg u2 R := by
  induction R with
  | nil => simp [lvl1Deg]
  | cons e R ih =>
    simp only [List.map_cons, List.sum_cons, ih, lvl1Deg_cons, lvl1Share_ends int a e u1 u2 ha hab]
    ring

variable (emb : V → V') (hemb : Function.Injective emb) (int : V → Bool) (int' : V' → Bool)
  (hint : ∀ u, int' (emb u) = int u)

include hemb

theorem lvl1_cnt_emb (u : V) (e : SEdge V) : lvl1Cnt (emb u) (SEdge.map emb e) = lvl1Cnt u e := by
  unfold lvl1Cnt
  simp only [SEdge.map, hemb.eq_iff]

theorem lvl1_deg_emb (u : V) (R : List (SEdge V)) : lvl1Deg (emb u) (R.map (SEdge.map emb)) = lvl1Deg u R := by
  induction R with
  | nil => rfl
  | cons e R ih => simp only [List.map_cons, lvl1Deg_cons, ih, lvl1_cnt_emb emb hemb]

include hint

theorem lvl1_share_emb (e e' : SEdge V) :
    lvl1Share int' (SEdge.map emb e) (SEdge.map emb e') = lvl1Share int e e' := by
  unfold lvl1Share
  simp only [SEdge.map, hemb.eq_iff, hint]

theorem lvl1_pairs_emb (l : List (SEdge V)) :
    lvl1Pairs int' (l.map (SEdge.map emb)) = lvl1Pairs int l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.map_cons, lvl1Pairs, ih, List.map_map]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun e' _ => ?_)
    exact lvl1_share_emb emb hemb int int' hint e e'


end Pairs

section PairsMain

variable {V V' : Type*} [DecidableEq V] [DecidableEq V']

theorem lvl1Cnt_end {u1 u2 : V} (e : SEdge V) (he : e.src ≠ e.dst)
    (hab : (e.src = u1 ∧ e.dst = u2) ∨ (e.src = u2 ∧ e.dst = u1)) : lvl1Cnt u1 e = 1 := by
  unfold lvl1Cnt
  rw [if_neg he]
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : e.dst ≠ u1 := fun h => he (h1.trans h.symm)
    rw [if_pos h1, if_neg h3]
  · have h3 : e.src ≠ u1 := fun h => he (h.trans h2.symm)
    rw [if_neg h3, if_pos h2]

theorem lvl1Cnt_other {u u1 u2 : V} (e : SEdge V) (he : e.src ≠ e.dst)
    (hab : (e.src = u1 ∧ e.dst = u2) ∨ (e.src = u2 ∧ e.dst = u1)) (h1 : u ≠ u1) (h2 : u ≠ u2) : lvl1Cnt u e = 0 := by
  unfold lvl1Cnt
  rw [if_neg he]
  rcases hab with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [if_neg (by rw [h3]; exact fun h => h1 h.symm), if_neg (by rw [h4]; exact fun h => h2 h.symm)]
  · rw [if_neg (by rw [h3]; exact fun h => h2 h.symm), if_neg (by rw [h4]; exact fun h => h1 h.symm)]


/-- **The pairs of a pulled term**: replacing the two edges `a`, `b` at `X` by the two edges `n1`, `n2` at a new internal
vertex `α` (the pull of `G_{Xv}` and an edge `b` at `X` with the far end `d`) lowers the number of pairs of edges
with a common internal end by twice the number of the other edges at `X`. -/
theorem lvl1_pairs_pull (emb : V → V') (hemb : Function.Injective emb) (int : V → Bool) (int' : V' → Bool)
    (hint : ∀ u, int' (emb u) = int u) (α : V') (hα : int' α = true) (hαe : ∀ u, emb u ≠ α)
    (X v d : V) (hX : int X = true) (hXv : X ≠ v) (hXd : X ≠ d)
    (a b : SEdge V) (ha : a.src ≠ a.dst) (hab : (a.src = X ∧ a.dst = v) ∨ (a.src = v ∧ a.dst = X))
    (hb : b.src ≠ b.dst) (hbb : (b.src = X ∧ b.dst = d) ∨ (b.src = d ∧ b.dst = X))
    (n1 n2 : SEdge V') (hn1 : n1.src ≠ n1.dst) (hn1e : (n1.src = α ∧ n1.dst = emb d) ∨ (n1.src = emb d ∧ n1.dst = α))
    (hn2 : n2.src ≠ n2.dst) (hn2e : (n2.src = α ∧ n2.dst = emb v) ∨ (n2.src = emb v ∧ n2.dst = α))
    (R : List (SEdge V)) :
    lvl1Pairs int' (R.map (SEdge.map emb) ++ [n1, n2]) + 2 * lvl1Deg X R = lvl1Pairs int (a :: b :: R) := by
  -- the degree of `α` in the embedded edges vanishes
  have hdeg0 : lvl1Deg α (R.map (SEdge.map emb)) = 0 := by
    induction R with
    | nil => rfl
    | cons e R ih =>
      simp only [List.map_cons, lvl1Deg_cons, ih, add_zero]
      unfold lvl1Cnt
      simp [SEdge.map, hαe]
  have hiα : lvl1Iota int' α = 1 := by simp [lvl1Iota, hα]
  have hX1 : lvl1Iota int X = 1 := by simp [lvl1Iota, hX]
  have hid : lvl1Iota int' (emb d) = lvl1Iota int d := by simp [lvl1Iota, hint]
  have hiv : lvl1Iota int' (emb v) = lvl1Iota int v := by simp [lvl1Iota, hint]
  -- the new edges against the embedded edges
  have s1 : ((R.map (SEdge.map emb)).map (lvl1Share int' n1)).sum = lvl1Iota int d * lvl1Deg d R := by
    rw [lvl1_sum_share int' n1 α (emb d) hn1 hn1e, hdeg0, lvl1_deg_emb emb hemb, hid]
    ring
  have s2 : ((R.map (SEdge.map emb)).map (lvl1Share int' n2)).sum = lvl1Iota int v * lvl1Deg v R := by
    rw [lvl1_sum_share int' n2 α (emb v) hn2 hn2e, hdeg0, lvl1_deg_emb emb hemb, hiv]
    ring
  -- append formula
  rw [lvl1Pairs_append, lvl1_pairs_emb emb hemb int int' hint]
  have hcross : (((R.map (SEdge.map emb)).map fun e => ([n1, n2].map (lvl1Share int' e)).sum)).sum =
      lvl1Iota int d * lvl1Deg d R + lvl1Iota int v * lvl1Deg v R := by
    have : ∀ e : SEdge V', ([n1, n2].map (lvl1Share int' e)).sum = lvl1Share int' n1 e + lvl1Share int' n2 e := by
      intro e
      simp [lvl1Share_comm int' e n1, lvl1Share_comm int' e n2]
    simp only [this, List.sum_map_add, ← s1, ← s2]
  have hn12 : lvl1Pairs int' [n1, n2] = lvl1Share int' n1 n2 := by simp [lvl1Pairs]
  have hs12 : lvl1Share int' n1 n2 = 1 + lvl1Iota int d * (if d = v then 1 else 0) := by
    rw [lvl1Share_ends int' n1 n2 α (emb d) hn1 hn1e, hiα, hid]
    have c1 : lvl1Cnt α n2 = 1 := lvl1Cnt_end n2 hn2 hn2e
    have c2 : lvl1Cnt (emb d) n2 = if d = v then 1 else 0 := by
      by_cases hdv : d = v
      · subst hdv
        rw [if_pos rfl]
        exact lvl1Cnt_end n2 hn2 (by rcases hn2e with h | h <;> [exact Or.inr h; exact Or.inl h])
      · rw [if_neg hdv]
        exact lvl1Cnt_other n2 hn2 hn2e (hαe d) (fun h => hdv (hemb h))
    rw [c1, c2]
  -- the original side
  have e1 : lvl1Pairs int (a :: b :: R) =
      lvl1Pairs int R + (R.map (lvl1Share int b)).sum + (lvl1Share int a b + (R.map (lvl1Share int a)).sum) := by
    simp only [lvl1Pairs, List.map_cons, List.sum_cons]
  have e2 := lvl1_sum_share int a X v ha hab R
  have e3 := lvl1_sum_share int b X d hb (by rcases hbb with h | h <;> [exact Or.inl h; exact Or.inr h]) R
  have e4 : lvl1Share int a b = 1 + lvl1Iota int v * (if v = d then 1 else 0) := by
    rw [lvl1Share_ends int a b X v ha hab, hX1]
    have c1 : lvl1Cnt X b = 1 := lvl1Cnt_end b hb hbb
    have c2 : lvl1Cnt v b = if v = d then 1 else 0 := by
      by_cases hvd : v = d
      · subst hvd
        rw [if_pos rfl]
        exact lvl1Cnt_end b hb (by rcases hbb with h | h <;> [exact Or.inr h; exact Or.inl h])
      · rw [if_neg hvd]
        exact lvl1Cnt_other b hb hbb (fun h => hXv h.symm) hvd
    rw [c1, c2]
  have hdv : lvl1Iota int d * (if d = v then 1 else 0) = lvl1Iota int v * (if v = d then 1 else 0) := by
    by_cases h : d = v
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [e1, e2, e3, e4, hX1, hcross, hn12, hs12]
  nlinarith [hdv]

end PairsMain
end RBM.Graph
end Lvl1PartP

/-! ## 5. Degree and charge of a vertex (`(eq:neutralcharge)`) -/

section Lvl1PartD
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Deg

/-- the non-loop edge `e` has an end at `v` -/
def SEdge.lvl1IncAt {V : Type*} [DecidableEq V] (e : SEdge V) (v : V) : Bool :=
  decide (e.src ≠ e.dst ∧ (e.src = v ∨ e.dst = v))

/-- the charge of a solid edge at one of its ends (`(eq:neutralcharge)`): `+1` for an incoming blue or an outgoing red
edge, `-1` for an outgoing blue or an incoming red edge -/
def SEdge.lvl1ChargeAt {V : Type*} [DecidableEq V] (e : SEdge V) (v : V) : ℤ :=
  if e.src = v then (if e.σ then -1 else 1) else (if e.σ then 1 else -1)

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the non-loop solid edges at the vertex `v` -/
def LGraph.lvl1SolidAt (Γ : LGraph E I) (v : E ⊕ I) : List (SEdge (E ⊕ I)) := Γ.solid.filter fun e => e.lvl1IncAt v

/-- the degree of `v`: the number of solid edges at `v`, self-loops not counted (`B:128`) -/
def LGraph.lvl1DegAt (Γ : LGraph E I) (v : E ⊕ I) : ℕ := (Γ.lvl1SolidAt v).length

/-- the charge of `v` (`(eq:neutralcharge)`): `#{incoming + or outgoing −} - #{outgoing + or incoming −}` -/
def LGraph.lvl1ChargeAt (Γ : LGraph E I) (v : E ⊕ I) : ℤ := ((Γ.lvl1SolidAt v).map fun e => e.lvl1ChargeAt v).sum

theorem lvl1_incAt_iff {V : Type*} [DecidableEq V] (e : SEdge V) (v : V) :
    e.lvl1IncAt v = true ↔ e.src ≠ e.dst ∧ (e.src = v ∨ e.dst = v) := by
  simp [SEdge.lvl1IncAt]

theorem lvl1Cnt_eq_zero_iff {V : Type*} [DecidableEq V] (e : SEdge V) (v : V) :
    lvl1Cnt v e = 0 ↔ e.lvl1IncAt v = false := by
  unfold lvl1Cnt SEdge.lvl1IncAt
  by_cases h : e.src = e.dst
  · simp [h]
  · by_cases h1 : e.src = v <;> by_cases h2 : e.dst = v <;> simp [h, h1, h2]

theorem lvl1_charge_twist {V : Type*} [DecidableEq V] (c t : Bool) (e : SEdge V) (v : V)
    (h : e.lvl1IncAt v = true) : (lwSymmTwistS c t e).lvl1ChargeAt v = (if c = t then 1 else -1) * e.lvl1ChargeAt v := by
  rw [lvl1_incAt_iff] at h
  obtain ⟨hne, hv⟩ := h
  unfold SEdge.lvl1ChargeAt
  rw [lwSymmTwistS_eq]
  have h1 : e.src = v → e.dst ≠ v := fun h h' => hne (h.trans h'.symm)
  have h2 : e.dst = v → e.src ≠ v := fun h h' => hne (h'.trans h.symm)
  rcases hv with hv | hv
  · have h3 := h1 hv
    cases c <;> cases t <;> by_cases hσ : e.σ = true <;> simp [hv, hσ, h3, hne]
  · have h3 := h2 hv
    cases c <;> cases t <;> by_cases hσ : e.σ = true <;> simp [hv, hσ, h3, hne]


/-- **A bad vertex with two opposite edges has a third edge**: if `x` has degree `≠ 0, 2` or non-neutral charge, and two of its
edges `p.1`, `q.1` have charges that cancel, the other edges `q.2` have an end at `x`. -/
theorem lvl1_deg_ge (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (X : E ⊕ I)
    (hpX : p.1.lvl1IncAt X = true) (hqX : q.1.lvl1IncAt X = true) (hch : p.1.lvl1ChargeAt X + q.1.lvl1ChargeAt X = 0)
    (hbad : Γ.lvl1DegAt X ≠ 0 ∧ (Γ.lvl1DegAt X ≠ 2 ∨ Γ.lvl1ChargeAt X ≠ 0)) : 1 ≤ lvl1Deg X q.2 := by
  by_contra h
  have h0 : lvl1Deg X q.2 = 0 := by omega
  have hnone : ∀ e ∈ q.2, e.lvl1IncAt X = false := by
    intro e he
    have : lvl1Cnt X e = 0 := by
      unfold lvl1Deg at h0
      exact (List.sum_eq_zero_iff.1 h0) _ (List.mem_map_of_mem he)
    exact (lvl1Cnt_eq_zero_iff e X).1 this
  have hfilt : q.2.filter (fun e => e.lvl1IncAt X) = [] :=
    List.filter_eq_nil_iff.2 (fun e he => by simp [hnone e he])
  have hperm : (Γ.lvl1SolidAt X).Perm [p.1, q.1] := by
    unfold LGraph.lvl1SolidAt
    have h1 := ((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)).filter
      (fun e => e.lvl1IncAt X)
    rw [List.filter_cons_of_pos (by simpa using hpX), List.filter_cons_of_pos (by simpa using hqX), hfilt] at h1
    exact h1
  have hdeg : Γ.lvl1DegAt X = 2 := by
    unfold LGraph.lvl1DegAt
    rw [hperm.length_eq]
    rfl
  have hchg : Γ.lvl1ChargeAt X = 0 := by
    unfold LGraph.lvl1ChargeAt
    rw [(hperm.map (fun e => e.lvl1ChargeAt X)).sum_eq]
    simpa using hch
  rcases hbad.2 with h | h
  · exact h hdeg
  · exact h hchg

end Deg
end RBM.Graph
end Lvl1PartD

/-! ## 6. Step 1: the one-step claims for the four terms of `(Owx)` -/

section Lvl1PartT1
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Step1

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lvl1_good_owxT3 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool)
    (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (P : PGraph E) (hP : P ∈ (lwSymmOwxT3 c t m Γ x q).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOwxT3 c t m Γ x q with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set α : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inr 0) with hα
  set xx : E ⊕ (I ⊕ Fin 1) := owxEmb 1 x with hxx
  set qf := lwSymmTwistS c t q.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) :=
    [(owxDE α xx (SEdge.map (owxEmb 1) qf)).1, (owxDE α xx (SEdge.map (owxEmb 1) qf)).2, ⟨true, false, α, xx⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOwxT3 owxET3
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hxx, hqf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lwSymmOwxT3 owxET3
    rw [lvl1_twist_owxExt_dotted]
    simp only [lwSymmTwistG_dotted]
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 1
  have hne1 : (SEdge.map (owxEmb 1) qf).src ≠ α := fun h => lvl1_owxEmb_ne qf.src 0 h
  have hne2 : (SEdge.map (owxEmb 1) qf).dst ≠ α := fun h => lvl1_owxEmb_ne qf.dst 0 h
  have hxa : xx ≠ α := fun h => lvl1_owxEmb_ne x 0 h
  obtain ⟨hc0, hnl, hcA, hcO⟩ := lvl1_derivNf α xx xx (SEdge.map (owxEmb 1) qf) hne1 hne2 hxa hxa
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ, hc0 e0 he0] at hc
    exact absurd hc (by simp)
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he _ hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    exact hnl e0 he0 hat hl
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) = 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    exact hcA
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 1 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    exact hcO
  have hcnt1 : (Nf.map (lwSymmTwistS c t)).countP (fun e => e.circ) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ])]
    rw [List.countP_eq_zero]
    intro e he
    simp [hc0 e he]
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 1 ∧ Δ.nV = Γ.nV + 1 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_weight_counters m Γ p hp x c t).2.2.1 q hq
  have hpl : p.1.src = p.1.dst := (lwSymmTwistS_loop c t p.1).1 (by rw [hx])
  have hwΓ := lvl1_loops_split Γ p hp q hq
  rw [if_pos hpl] at hwΓ
  refine lvl1_good_k1b m Γ (owxEmb 1) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0)
    hcirc hαne (by omega) (by omega) hcnt1 (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) P hP


/-- the data of a list of circled loops as the new edges of a term -/
theorem lvl1_noNC {V : Type*} [DecidableEq V] (c t : Bool) (N : List (SEdge V))
    (hN : ∀ e ∈ N, e.circ = true ∧ e.src = e.dst) (a : V) :
    (∀ e ∈ N.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst) ∧
    (∀ e ∈ N.map (lwSymmTwistS c t), e.circ = false → (e.src = a ∨ e.dst = a) → e.src ≠ e.dst) ∧
    (N.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA a e) = 0 ∧
    (N.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA a e) = 0 := by
  have hc : ∀ e ∈ N.map (lwSymmTwistS c t), e.circ = true ∧ e.src = e.dst := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    refine ⟨by rw [lwSymmTwistS_circ]; exact (hN e0 he0).1, (lwSymmTwistS_loop c t e0).2 (hN e0 he0).2⟩
  refine ⟨fun e he _ => (hc e he).2, fun e he h => absurd (hc e he).1 (by simp [h]), ?_, ?_⟩ <;>
  · rw [List.countP_eq_zero]
    intro e he
    simp [(hc e he).1]

theorem lvl1_good_owxT1 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool)
    (P : PGraph E) (hP : P ∈ (lwSymmOwxT1 c t m Γ x).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOwxT1 c t m Γ x with hΔ
  have hR := lvl1_hR_of_normal Γ hN Γ.solid (fun e he => he)
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) := [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] with hNf
  have hsol : Δ.solid = Γ.solid.map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOwxT1 owxET1
    rw [lvl1_twist_owxExt_solid, lwSymmTwistG_solid, lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lwSymmOwxT1 owxET1
    rw [lvl1_twist_owxExt_dotted]
    simp only [lwSymmTwistG_dotted]
  obtain ⟨hc1, hc2, hc3, hc4⟩ := lvl1_noNC c t Nf (by simp [hNf]) (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1))
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 1 ∧ Δ.nV = Γ.nV + 1 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_weight_counters m Γ p hp x c t).1
  refine lvl1_good_k1a m Γ (owxEmb 1) (lvl1_owxEmb_inj (E := E) (I := I) 1) Γ.solid (Nf.map (lwSymmTwistS c t)) hR Δ
    (by rw [hsol]) hdot (Sum.inr 0) hc1 hc2 (by omega) hc4 (by omega) (by omega) (by omega) P hP

theorem lvl1_good_owxT2 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool)
    (P : PGraph E) (hP : P ∈ (lwSymmOwxT2 c t m Γ p x).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOwxT2 c t m Γ p x with hΔ
  have hR := lvl1_hR_of_normal Γ hN p.2 (lvl1_mem_split _ p hp)
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 2))) := [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩,
      ⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩] with hNf
  have hsol : Δ.solid = p.2.map (SEdge.map (owxEmb 2)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOwxT2 owxET2
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 2)) := by
    rw [hΔ]
    unfold lwSymmOwxT2 owxET2
    rw [lvl1_twist_owxExt_dotted]
    simp only [lwSymmTwistG_dotted]
  obtain ⟨hc1, hc2, hc3, hc4⟩ := lvl1_noNC c t Nf (by simp [hNf]) (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 2))
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 2 ∧ Δ.nV = Γ.nV + 2 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_weight_counters m Γ p hp x c t).2.1
  refine lvl1_good_k1a m Γ (owxEmb 2) (lvl1_owxEmb_inj (E := E) (I := I) 2) p.2 (Nf.map (lwSymmTwistS c t)) hR Δ
    (by rw [hsol]) hdot (Sum.inr 0) hc1 hc2 (by omega) hc4 (by omega) (by omega) (by omega) P hP

theorem lvl1_good_owxT4 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (P : PGraph E) (hP : P ∈ (lwSymmOwxT4 c t m Γ x q).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOwxT4 c t m Γ x q with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set α : E ⊕ (I ⊕ Fin 2) := Sum.inr (Sum.inr 0) with hα
  set β : E ⊕ (I ⊕ Fin 2) := Sum.inr (Sum.inr 1) with hβ
  set qf := lwSymmTwistS c t q.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 2))) :=
    [(owxDE β α (SEdge.map (owxEmb 2) qf)).1, (owxDE β α (SEdge.map (owxEmb 2) qf)).2, ⟨true, false, β, α⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 2)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOwxT4 owxET4
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hβ, hqf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 2)) := by
    rw [hΔ]
    unfold lwSymmOwxT4 owxET4
    rw [lvl1_twist_owxExt_dotted]
    simp only [lwSymmTwistG_dotted]
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 2
  have hne : ∀ (v : E ⊕ I) (j : Fin 2), owxEmb 2 v ≠ (Sum.inr (Sum.inr j) : E ⊕ (I ⊕ Fin 2)) := by
    intro v j h
    exact lwSymm_emb_ne v 2 j h.symm
  have hαβ : α ≠ β := by simp [hα, hβ]
  obtain ⟨hc0, hnc, hOA, hOB, hAB⟩ := lvl1_derivNf2 α β hαβ (SEdge.map (owxEmb 2) qf)
    (hne _ 0) (hne _ 0) (hne _ 1) (hne _ 1)
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 2 ∧ Δ.nV = Γ.nV + 2 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_weight_counters m Γ p hp x c t).2.2.2 q hq
  have hnc' : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false → e.src ≠ e.dst ∧
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0) ∨ e.src = Sum.inr (Sum.inr 1) ∨
        e.dst = Sum.inr (Sum.inr 1)) := by
    intro e he _
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    obtain ⟨hl, hat⟩ := hnc e0 he0
    exact ⟨fun h => hl ((lwSymmTwistS_loop c t e0).1 h), (lvl1_touch_twist c t e0 α β).2 hat⟩
  have hA' : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1OldA (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) e) = 1 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_oldA_twist])]
    exact hOA
  have hB' : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1OldA (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) e) = 1 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_oldA_twist])]
    exact hOB
  have hAB' : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1AB (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) e) = 1 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_ab_twist])]
    exact hAB
  refine lvl1_good_k2 m Γ (owxEmb 2) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0) (Sum.inr 1)
    (by simp) hnc' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) P hP

end Step1
end RBM.Graph
end Lvl1PartT1

/-! ## 7. Step 2: the one-step claims for the terms of `(Oe1x)` (first part) -/

section Lvl1PartT2
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Step2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lvl1_noNC' {V : Type*} [DecidableEq V] (c t : Bool) (N : List (SEdge V))
    (hN : ∀ e ∈ N, e.circ = true ∧ e.src = e.dst) (a : V) :
    (∀ e ∈ N.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst) ∧
    (∀ e ∈ N.map (lwSymmTwistS c t), e.circ = false → (e.src = a ∨ e.dst = a) → e.src ≠ e.dst) ∧
    (N.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA a e) = 0 ∧
    (N.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA a e) = 0 := by
  have hc : ∀ e ∈ N.map (lwSymmTwistS c t), e.circ = true ∧ e.src = e.dst := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    refine ⟨by rw [lwSymmTwistS_circ]; exact (hN e0 he0).1, (lwSymmTwistS_loop c t e0).2 (hN e0 he0).2⟩
  refine ⟨fun e he _ => (hc e he).2, fun e he h => absurd (hc e he).1 (by simp [h]), ?_, ?_⟩ <;>
  · rw [List.countP_eq_zero]
    intro e he
    simp [(hc e he).1]

theorem lvl1_hpne (c t : Bool) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) :
    p.1.src ≠ p.1.dst := by
  intro h
  have := (lwSymmTwistS_loop c t p.1).2 h
  rw [hx] at this
  exact hv this.symm

theorem lvl1_good_oe1xOwx (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (P : PGraph E) (hP : P ∈ (lwSymmOe1xOwx c t m Γ p x).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOe1xOwx c t m Γ p x with hΔ
  have hR := lvl1_hR_uncirc Γ hN p hp (lvl1_hpne c t p x v hv hx)
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) := [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] with hNf
  have hsol : Δ.solid = ({ p.1 with circ := false } :: p.2).map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOe1xOwx owxT1
    rw [lvl1_twist_owxExt_solid, lvl1_frame_solid_twist]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lwSymmOe1xOwx owxT1
    rw [lvl1_twist_owxExt_dotted, lvl1_frame_dotted]
  obtain ⟨hc1, hc2, hc3, hc4⟩ := lvl1_noNC' c t Nf (by simp [hNf]) (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1))
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 1 ∧ Δ.nV = Γ.nV + 1 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_oe1x_counters m Γ p hp x v hv c t).2.1
  exact lvl1_good_k1a m Γ (owxEmb 1) (lvl1_owxEmb_inj (E := E) (I := I) 1) _ (Nf.map (lwSymmTwistS c t)) hR Δ
    (by rw [hsol]) hdot (Sum.inr 0) hc1 hc2 (by omega) hc4 (by omega) (by omega) (by omega) P hP


/-- the five derivative graphs of `(Oe1x)`, twisted back -/
def lvl1P5 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (oe1xP5 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))
def lvl1P3 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (oe1xP3 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))
def lvl1P6 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (oe1xP6 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))
def lvl1P4 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (oe1xP4 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))
def lvl1D (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (oe1xD m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))

theorem lvl1_good_oe1xD (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) (c t : Bool)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hn1 : ¬ ((lwSymmTwistS c t q.1).σ = false ∧ (lwSymmTwistS c t q.1).src = Sum.inr x))
    (hn2 : ¬ ((lwSymmTwistS c t q.1).σ = true ∧ (lwSymmTwistS c t q.1).dst = Sum.inr x))
    (hW : (lvl1D c t m Γ p x v q).nW = Γ.nW + 1) (hV : (lvl1D c t m Γ p x v q).nV = Γ.nV + 1)
    (hM : (lvl1D c t m Γ p x v q).nM = Γ.nM)
    (P : PGraph E) (hP : P ∈ (lvl1D c t m Γ p x v q).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lvl1D c t m Γ p x v q with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set α : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inr 0) with hα
  set xx : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inl x) with hxx
  set qf := lwSymmTwistS c t q.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) :=
    [(owxDE α xx (SEdge.map (owxEmb 1) qf)).1, (owxDE α xx (SEdge.map (owxEmb 1) qf)).2,
      ⟨true, false, α, owxEmb 1 v⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lvl1D oe1xD
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hxx, hqf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lvl1D oe1xD
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 1))) (lvl1_frame_dotted c t Γ p)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 1
  have hne1 : (SEdge.map (owxEmb 1) qf).src ≠ α := fun h => lvl1_owxEmb_ne qf.src 0 h
  have hne2 : (SEdge.map (owxEmb 1) qf).dst ≠ α := fun h => lvl1_owxEmb_ne qf.dst 0 h
  have hxa : xx ≠ α := by simp [hxx, hα]
  have hza : owxEmb 1 v ≠ α := fun h => lvl1_owxEmb_ne v 0 h
  obtain ⟨hc0, hnl, hcA, hcO⟩ := lvl1_derivNf α xx (owxEmb 1 v) (SEdge.map (owxEmb 1) qf) hne1 hne2 hxa hza
  have hhoo := lvl1_derivNf_hoo α xx (owxEmb 1 v) (SEdge.map (owxEmb 1) qf) hne1 hne2 hxa hza (by simp [hxx])
    ⟨fun h => by
        intro hh
        apply hn2
        refine ⟨h, ?_⟩
        have := lvl1_owxEmb_inj (E := E) (I := I) 1 (show owxEmb 1 qf.dst = owxEmb 1 (Sum.inr x) from hh)
        exact this,
     fun h => by
        intro hh
        apply hn1
        refine ⟨h, ?_⟩
        have := lvl1_owxEmb_inj (E := E) (I := I) 1 (show owxEmb 1 qf.src = owxEmb 1 (Sum.inr x) from hh)
        exact this⟩
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ, hc0 e0 he0] at hc
    exact absurd hc (by simp)
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he _ hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    exact hnl e0 he0 hat hl
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) = 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    exact hcA
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 1 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    exact hcO
  have hcnt1 : (Nf.map (lwSymmTwistS c t)).countP (fun e => e.circ) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ])]
    rw [List.countP_eq_zero]
    intro e he
    simp [hc0 e he]
  have hhoo' : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false → lvl1IncA (Sum.inr (Sum.inr 0)) e = false →
      e.src ≠ e.dst ∧ (e.src.isRight = true ∨ e.dst.isRight = true) := by
    intro e he hc hi
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lvl1_incA_twist] at hi
    obtain ⟨h1, h2⟩ := hhoo e0 he0 hc hi
    exact ⟨fun h => h1 ((lwSymmTwistS_loop c t e0).1 h), (lvl1_isRight_twist c t e0).2 h2⟩
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 1)) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hwΓ := lvl1_loops_split Γ p hp q hq
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 3 := by simp [hNf]
  refine lvl1_good_k1b m Γ (owxEmb 1) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0)
    hcirc hαne (by omega) (by omega) hcnt1 ?_ (by omega) ?_ ?_ ?_ (Or.inr (Or.inr hhoo')) P hP
  · simp only [ord, LGraph.counters, LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · simp only [LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · simp only [LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · omega


theorem lvl1_good_oe1xP5 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (c t : Bool)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hW : (lvl1P5 c t m Γ p x v q).nW = Γ.nW + 1) (hV : (lvl1P5 c t m Γ p x v q).nV = Γ.nV + 1)
    (hM : (lvl1P5 c t m Γ p x v q).nM = Γ.nM)
    (P : PGraph E) (hP : P ∈ (lvl1P5 c t m Γ p x v q).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lvl1P5 c t m Γ p x v q with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set α : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inr 0) with hα
  set xx : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inl x) with hxx
  set qf := lwSymmTwistS c t q.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) :=
    [⟨false, true, xx, xx⟩, ⟨false, false, α, owxEmb 1 qf.dst⟩, ⟨true, false, α, owxEmb 1 v⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lvl1P5 oe1xP5
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hxx, hqf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lvl1P5 oe1xP5
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 1))) (lvl1_frame_dotted c t Γ p)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 1
  have hd : owxEmb 1 qf.dst ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lvl1_owxEmb_ne qf.dst 0 h
  have hv' : owxEmb 1 v ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lvl1_owxEmb_ne v 0 h
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_loop]
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl <;> simp_all
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he hc hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl
    · simp at hc
    · simp_all
    · simp_all
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) ≤ 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    split_ifs <;> simp_all
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    simp [lvl1IncA, hd, hv', hα]
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 1)) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 3 := by simp [hNf]
  refine lvl1_good_k1a m Γ (owxEmb 1) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0)
    hcirc hαne hcnt2 hcnt3 ?_ (by omega) ?_ P hP
  · simp only [ord, LGraph.counters, LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · simp only [LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega

theorem lvl1_good_oe1xP6 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (c t : Bool)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hW : (lvl1P6 c t m Γ p x v q).nW = Γ.nW + 1) (hV : (lvl1P6 c t m Γ p x v q).nV = Γ.nV + 1)
    (hM : (lvl1P6 c t m Γ p x v q).nM = Γ.nM)
    (P : PGraph E) (hP : P ∈ (lvl1P6 c t m Γ p x v q).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lvl1P6 c t m Γ p x v q with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set α : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inr 0) with hα
  set xx : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inl x) with hxx
  set qf := lwSymmTwistS c t q.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) :=
    [⟨true, false, owxEmb 1 qf.src, α⟩, ⟨true, true, xx, xx⟩, ⟨true, false, α, owxEmb 1 v⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lvl1P6 oe1xP6
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hxx, hqf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lvl1P6 oe1xP6
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 1))) (lvl1_frame_dotted c t Γ p)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 1
  have hd : owxEmb 1 qf.src ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lvl1_owxEmb_ne qf.src 0 h
  have hv' : owxEmb 1 v ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lvl1_owxEmb_ne v 0 h
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_loop]
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl <;> simp_all
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he hc hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl
    · simp_all
    · simp at hc
    · simp_all
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) ≤ 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    split_ifs <;> simp_all
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    simp [lvl1IncA, hd, hv', hα]
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 1)) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 3 := by simp [hNf]
  refine lvl1_good_k1a m Γ (owxEmb 1) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0)
    hcirc hαne hcnt2 hcnt3 ?_ (by omega) ?_ P hP
  · simp only [ord, LGraph.counters, LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · simp only [LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega

end Step2
end RBM.Graph
end Lvl1PartT2

/-! ## 7. Step 2 (continued) -/

section Lvl1PartT3b
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Step2b

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lvl1_ends_twist {V : Type*} (c t : Bool) (e : SEdge V) :
    ((lwSymmTwistS c t e).src = e.src ∧ (lwSymmTwistS c t e).dst = e.dst) ∨
      ((lwSymmTwistS c t e).src = e.dst ∧ (lwSymmTwistS c t e).dst = e.src) := by
  rw [lwSymmTwistS_eq]
  cases t <;> simp

theorem lvl1_ends_of_twist {V : Type*} (c t : Bool) (e : SEdge V) (a b : V)
    (h : (lwSymmTwistS c t e).src = a ∧ (lwSymmTwistS c t e).dst = b) :
    (e.src = a ∧ e.dst = b) ∨ (e.src = b ∧ e.dst = a) := by
  rcases lvl1_ends_twist c t e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1.symm.trans h.1, h2.symm.trans h.2⟩
  · right; exact ⟨h2.symm.trans h.2, h1.symm.trans h.1⟩

theorem lvl1_isRight_owxEmb (k : ℕ) (u : E ⊕ I) : (owxEmb k u).isRight = u.isRight := by
  rcases u with a | b <;> rfl


theorem lvl1_good_oe1xP3 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hq1 : (lwSymmTwistS c t q.1).σ = false ∧ (lwSymmTwistS c t q.1).src = Sum.inr x)
    (hqne : q.1.src ≠ q.1.dst) (hdeg : 1 ≤ lvl1Deg (Sum.inr x : E ⊕ I) q.2)
    (hW : (lvl1P3 c t m Γ p x v q).nW = Γ.nW + 1) (hV : (lvl1P3 c t m Γ p x v q).nV = Γ.nV + 1)
    (hM : (lvl1P3 c t m Γ p x v q).nM = Γ.nM)
    (P : PGraph E) (hP : P ∈ (lvl1P3 c t m Γ p x v q).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lvl1P3 c t m Γ p x v q with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set α : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inr 0) with hα
  set qf := lwSymmTwistS c t q.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) :=
    [⟨false, false, α, owxEmb 1 qf.dst⟩, ⟨true, false, α, owxEmb 1 v⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lvl1P3 oe1xP3
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hqf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lvl1P3 oe1xP3
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 1))) (lvl1_frame_dotted c t Γ p)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 1
  have hd : owxEmb 1 qf.dst ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lvl1_owxEmb_ne qf.dst 0 h
  have hv' : owxEmb 1 v ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lvl1_owxEmb_ne v 0 h
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl <;> simp at hc
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he hc hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl
    · exact hd (by simpa [hα] using hl.symm)
    · exact hv' (by simpa [hα] using hl.symm)
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) ≤ 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    split_ifs <;> simp_all
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    simp [lvl1IncA, hd, hv', hα]
  have hcnt1 : (Nf.map (lwSymmTwistS c t)).countP (fun e => e.circ) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ])]
    simp [hNf]
  -- the pairs
  have hpne := lvl1_hpne c t p x v hv hx
  have hab := lvl1_ends_of_twist c t p.1 (Sum.inr x) v (by rw [hx]; exact ⟨rfl, rfl⟩)
  have hbb := lvl1_ends_of_twist c t q.1 (Sum.inr x) qf.dst ⟨hq1.2, rfl⟩
  have hXd : (Sum.inr x : E ⊕ I) ≠ qf.dst := by
    intro h
    rcases hbb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hqne (h1.trans (h ▸ h2.symm))
    · exact hqne (h1.trans (h ▸ h2.symm)) |> fun x => x
  have hn1 : (lwSymmTwistS c t ⟨false, false, α, owxEmb 1 qf.dst⟩).src ≠
      (lwSymmTwistS c t ⟨false, false, α, owxEmb 1 qf.dst⟩).dst := by
    rw [Ne, lwSymmTwistS_loop]; exact fun h => hd (by simpa [hα] using h.symm)
  have hn2 : (lwSymmTwistS c t ⟨true, false, α, owxEmb 1 v⟩).src ≠
      (lwSymmTwistS c t ⟨true, false, α, owxEmb 1 v⟩).dst := by
    rw [Ne, lwSymmTwistS_loop]; exact fun h => hv' (by simpa [hα] using h.symm)
  have hpairs := lvl1_pairs_pull (owxEmb 1) hemb Sum.isRight Sum.isRight (lvl1_isRight_owxEmb 1) α (by simp [hα])
    (fun u => fun h => lvl1_owxEmb_ne u 0 h) (Sum.inr x) v qf.dst (by simp) (Ne.symm hv) hXd p.1 q.1 hpne hab hqne
    (by rcases hbb with h | h <;> [exact Or.inl h; exact Or.inr h])
    (lwSymmTwistS c t ⟨false, false, α, owxEmb 1 qf.dst⟩) (lwSymmTwistS c t ⟨true, false, α, owxEmb 1 v⟩) hn1
    (lvl1_ends_twist c t _ |>.imp (fun h => by simpa using h) (fun h => by simpa using h)) hn2
    (lvl1_ends_twist c t _ |>.imp (fun h => by simpa using h) (fun h => by simpa using h)) q.2
  have hΓp : Γ.lvl1NPairs = lvl1Pairs Sum.isRight (p.1 :: q.1 :: q.2) := by
    unfold LGraph.lvl1NPairs
    exact lvl1Pairs_perm Sum.isRight ((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1))
  have hΔp : Δ.lvl1NPairs = lvl1Pairs Sum.isRight (q.2.map (SEdge.map (owxEmb 1)) ++ [lwSymmTwistS c t ⟨false, false, α, owxEmb 1 qf.dst⟩, lwSymmTwistS c t ⟨true, false, α, owxEmb 1 v⟩]) := by
    unfold LGraph.lvl1NPairs
    rw [hsol]
    simp [hNf]
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 1)) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hwΓ := lvl1_loops_split Γ p hp q hq
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 2 := by simp [hNf]
  refine lvl1_good_k1c m Γ (owxEmb 1) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0)
    hcirc hαne hcnt2 hcnt3 hcnt1 ?_ ?_ ?_ ?_ (by omega) ?_ P hP
  · simp only [ord, LGraph.counters, LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · omega
  · simp only [LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · simp only [LGraph.nS] at *
    omega
  · omega


theorem lvl1_good_oe1xP4 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hq1 : (lwSymmTwistS c t q.1).σ = true ∧ (lwSymmTwistS c t q.1).dst = Sum.inr x)
    (hqne : q.1.src ≠ q.1.dst) (hdeg : 1 ≤ lvl1Deg (Sum.inr x : E ⊕ I) q.2)
    (hW : (lvl1P4 c t m Γ p x v q).nW = Γ.nW + 1) (hV : (lvl1P4 c t m Γ p x v q).nV = Γ.nV + 1)
    (hM : (lvl1P4 c t m Γ p x v q).nM = Γ.nM)
    (P : PGraph E) (hP : P ∈ (lvl1P4 c t m Γ p x v q).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lvl1P4 c t m Γ p x v q with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set α : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inr 0) with hα
  set qf := lwSymmTwistS c t q.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) :=
    [⟨true, false, owxEmb 1 qf.src, α⟩, ⟨true, false, α, owxEmb 1 v⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lvl1P4 oe1xP4
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hqf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lvl1P4 oe1xP4
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 1))) (lvl1_frame_dotted c t Γ p)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 1
  have hd : owxEmb 1 qf.src ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lvl1_owxEmb_ne qf.src 0 h
  have hv' : owxEmb 1 v ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lvl1_owxEmb_ne v 0 h
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl <;> simp at hc
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he hc hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl
    · exact hd (by simpa [hα] using hl)
    · exact hv' (by simpa [hα] using hl.symm)
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) ≤ 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    split_ifs <;> simp_all
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    simp [lvl1IncA, hd, hv', hα]
  have hcnt1 : (Nf.map (lwSymmTwistS c t)).countP (fun e => e.circ) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ])]
    simp [hNf]
  -- the pairs
  have hpne := lvl1_hpne c t p x v hv hx
  have hab := lvl1_ends_of_twist c t p.1 (Sum.inr x) v (by rw [hx]; exact ⟨rfl, rfl⟩)
  have hbb0 := lvl1_ends_of_twist c t q.1 qf.src (Sum.inr x) ⟨rfl, hq1.2⟩
  have hbb : (q.1.src = Sum.inr x ∧ q.1.dst = qf.src) ∨ (q.1.src = qf.src ∧ q.1.dst = Sum.inr x) := hbb0.symm
  have hXd : (Sum.inr x : E ⊕ I) ≠ qf.src := by
    intro h
    rcases hbb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hqne (h1.trans (h ▸ h2.symm))
    · exact hqne (h1.trans (h ▸ h2.symm))
  have hn1 : (lwSymmTwistS c t ⟨true, false, owxEmb 1 qf.src, α⟩).src ≠
      (lwSymmTwistS c t ⟨true, false, owxEmb 1 qf.src, α⟩).dst := by
    rw [Ne, lwSymmTwistS_loop]; exact fun h => hd (by simpa [hα] using h)
  have hn2 : (lwSymmTwistS c t ⟨true, false, α, owxEmb 1 v⟩).src ≠
      (lwSymmTwistS c t ⟨true, false, α, owxEmb 1 v⟩).dst := by
    rw [Ne, lwSymmTwistS_loop]; exact fun h => hv' (by simpa [hα] using h.symm)
  have hpairs := lvl1_pairs_pull (owxEmb 1) hemb Sum.isRight Sum.isRight (lvl1_isRight_owxEmb 1) α (by simp [hα])
    (fun u => fun h => lvl1_owxEmb_ne u 0 h) (Sum.inr x) v qf.src (by simp) (Ne.symm hv) hXd p.1 q.1 hpne hab hqne
    (by rcases hbb with h | h <;> [exact Or.inl h; exact Or.inr h])
    (lwSymmTwistS c t ⟨true, false, owxEmb 1 qf.src, α⟩) (lwSymmTwistS c t ⟨true, false, α, owxEmb 1 v⟩) hn1
    (lvl1_ends_twist c t _ |>.symm |>.imp (fun h => by simpa using h) (fun h => by simpa using h)) hn2
    (lvl1_ends_twist c t _ |>.imp (fun h => by simpa using h) (fun h => by simpa using h)) q.2
  have hΓp : Γ.lvl1NPairs = lvl1Pairs Sum.isRight (p.1 :: q.1 :: q.2) := by
    unfold LGraph.lvl1NPairs
    exact lvl1Pairs_perm Sum.isRight ((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1))
  have hΔp : Δ.lvl1NPairs = lvl1Pairs Sum.isRight (q.2.map (SEdge.map (owxEmb 1)) ++ [lwSymmTwistS c t ⟨true, false, owxEmb 1 qf.src, α⟩, lwSymmTwistS c t ⟨true, false, α, owxEmb 1 v⟩]) := by
    unfold LGraph.lvl1NPairs
    rw [hsol]
    simp [hNf]
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 1)) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hwΓ := lvl1_loops_split Γ p hp q hq
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 2 := by simp [hNf]
  refine lvl1_good_k1c m Γ (owxEmb 1) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0)
    hcirc hαne hcnt2 hcnt3 hcnt1 ?_ ?_ ?_ ?_ (by omega) ?_ P hP
  · simp only [ord, LGraph.counters, LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · omega
  · simp only [LGraph.nS, LGraph.nW, LGraph.nV] at *
    omega
  · simp only [LGraph.nS] at *
    omega
  · omega

end Step2b
end RBM.Graph
end Lvl1PartT3b

/-! ## 7. Step 2 (the derivative terms) -/

section Lvl1PartT3c
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Step2c

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lvl1_eps_cases (c t : Bool) : (if c = t then (1 : ℤ) else -1) = 1 ∨ (if c = t then (1 : ℤ) else -1) = -1 := by
  by_cases h : c = t <;> simp [h]

/-- **The one-step claims for the derivative terms of `(Oe1x)`**. -/
theorem lvl1_good_oe1xDs (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (hbad : Γ.lvl1DegAt (Sum.inr x) ≠ 0 ∧ (Γ.lvl1DegAt (Sum.inr x) ≠ 2 ∨ Γ.lvl1ChargeAt (Sum.inr x) ≠ 0))
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ lwSymmOe1xDs c t m Γ p x v q, ∀ P ∈ T.partition m, Lvl1Good Γ P.g := by
  intro T hT0 P hP
  have hcnt := (lwSymm_oe1x_counters m Γ p hp x v hv c t).2.2 q hq T hT0
  obtain ⟨hW, hV, hM, -, -⟩ := hcnt
  have hqΓ : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hqne : q.1.src ≠ q.1.dst := hwf q.1 hqΓ
  have hpne := lvl1_hpne c t p x v hv hx
  have hpX : p.1.lvl1IncAt (Sum.inr x) = true := by
    rw [lvl1_incAt_iff]
    refine ⟨hpne, ?_⟩
    rcases lvl1_ends_of_twist c t p.1 (Sum.inr x) v (by rw [hx]; exact ⟨rfl, rfl⟩) with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2
  have hpch : (lwSymmTwistS c t p.1).lvl1ChargeAt (Sum.inr x) = -1 := by
    rw [hx]; simp [SEdge.lvl1ChargeAt]
  have hpch' := lvl1_charge_twist c t p.1 (Sum.inr x) hpX
  simp only [lwSymmOe1xDs, List.mem_map] at hT0
  obtain ⟨T0, hT0', rfl⟩ := hT0
  unfold oe1xDs at hT0'
  split_ifs at hT0' with h1 h2
  · -- red out-edge of `x` in the frame: `oe1xP5`, `oe1xP3`
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT0'
    rcases hT0' with rfl | rfl
    · exact lvl1_good_oe1xP5 m Γ hN p hp x v c t q hq hW hV hM P hP
    · have hq1 : (lwSymmTwistS c t q.1).σ = false ∧ (lwSymmTwistS c t q.1).src = Sum.inr x := h1
      have hqX : q.1.lvl1IncAt (Sum.inr x) = true := by
        rw [lvl1_incAt_iff]
        refine ⟨hqne, ?_⟩
        rcases lvl1_ends_of_twist c t q.1 (Sum.inr x) (lwSymmTwistS c t q.1).dst ⟨hq1.2, rfl⟩ with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inl h1
        · exact Or.inr h2
      have hqch : (lwSymmTwistS c t q.1).lvl1ChargeAt (Sum.inr x) = 1 := by
        unfold SEdge.lvl1ChargeAt; rw [hq1.2, hq1.1]; simp
      have hqch' := lvl1_charge_twist c t q.1 (Sum.inr x) hqX
      have hch : p.1.lvl1ChargeAt (Sum.inr x) + q.1.lvl1ChargeAt (Sum.inr x) = 0 := by
        rcases lvl1_eps_cases c t with h | h <;> rw [h] at hpch' hqch' <;> omega
      exact lvl1_good_oe1xP3 m Γ hN p hp x v hv c t hx q hq hq1 hqne
        (lvl1_deg_ge Γ p hp q hq (Sum.inr x) hpX hqX hch hbad) hW hV hM P hP
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT0'
    rcases hT0' with rfl | rfl
    · exact lvl1_good_oe1xP6 m Γ hN p hp x v c t q hq hW hV hM P hP
    · have hq1 : (lwSymmTwistS c t q.1).σ = true ∧ (lwSymmTwistS c t q.1).dst = Sum.inr x := h2
      have hqX : q.1.lvl1IncAt (Sum.inr x) = true := by
        rw [lvl1_incAt_iff]
        refine ⟨hqne, ?_⟩
        rcases lvl1_ends_of_twist c t q.1 (lwSymmTwistS c t q.1).src (Sum.inr x) ⟨rfl, hq1.2⟩ with ⟨_, h1⟩ | ⟨h1, _⟩
        · exact Or.inr h1
        · exact Or.inl h1
      have hqch : (lwSymmTwistS c t q.1).lvl1ChargeAt (Sum.inr x) = 1 := by
        unfold SEdge.lvl1ChargeAt
        have hne' : (lwSymmTwistS c t q.1).src ≠ Sum.inr x := by
          intro h
          apply hqne
          rw [← lwSymmTwistS_loop c t q.1]
          rw [h, hq1.2]
        rw [if_neg hne', hq1.1]; simp
      have hqch' := lvl1_charge_twist c t q.1 (Sum.inr x) hqX
      have hch : p.1.lvl1ChargeAt (Sum.inr x) + q.1.lvl1ChargeAt (Sum.inr x) = 0 := by
        rcases lvl1_eps_cases c t with h | h <;> rw [h] at hpch' hqch' <;> omega
      exact lvl1_good_oe1xP4 m Γ hN p hp x v hv c t hx q hq hq1 hqne
        (lvl1_deg_ge Γ p hp q hq (Sum.inr x) hpX hqX hch hbad) hW hV hM P hP
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT0'
    subst hT0'
    exact lvl1_good_oe1xD m Γ hN p hp x v hv c t q hq h1 h2 hW hV hM P hP

end Step2c
end RBM.Graph
end Lvl1PartT3c

/-! ## 8. Step 3: the one-step claims for the terms of `(Oe2x)` -/

section Lvl1PartT4
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Step3

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the support conditions for `{p.1 with circ := false} :: {q.1 with circ := false} :: q.2` -/
theorem lvl1_hR_uncirc2 (Γ : LGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hpne : p.1.src ≠ p.1.dst) (hqne : q.1.src ≠ q.1.dst) :
    ∀ e ∈ ({ p.1 with circ := false } :: { q.1 with circ := false } :: q.2 : List (SEdge (E ⊕ I))),
      (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨fun _ => (hN.2.1 _ _ hpne).2 ⟨p.1, lvl1_mem_split_fst _ p hp, hpne, Or.inl ⟨rfl, rfl⟩⟩,
      fun h => absurd h hpne⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨fun _ => (hN.2.1 _ _ hqne).2 ⟨q.1, lvl1_mem_split _ p hp _ (lvl1_mem_split_fst _ q hq), hqne,
      Or.inl ⟨rfl, rfl⟩⟩, fun h => absurd h hqne⟩
  · exact lvl1_hR_of_normal Γ hN q.2 (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) e he

theorem lvl1_good_R3 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hy' : y' ≠ Sum.inr x)
    (P : PGraph E) (hP : P ∈ (lwSymmOe2xR3 c t m Γ p q x).partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOe2xR3 c t m Γ p q x with hΔ
  have hpne := lvl1_hpne c t p x y hy hp1
  have hqne : q.1.src ≠ q.1.dst := by
    intro h
    have := (lwSymmTwistS_loop c t q.1).2 h
    rw [hq1] at this
    exact hy' this
  have hR := lvl1_hR_uncirc2 Γ hN p hp q hq hpne hqne
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) := [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] with hNf
  have hsol : Δ.solid = ({ p.1 with circ := false } :: { q.1 with circ := false } :: q.2).map (SEdge.map (owxEmb 1)) ++
      Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOe2xR3 owxT1
    rw [lvl1_twist_owxExt_solid, lvl1_frame2_solid_twist]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lwSymmOe2xR3 owxT1
    rw [lvl1_twist_owxExt_dotted, lvl1_frame2_dotted]
  obtain ⟨hc1, hc2, hc3, hc4⟩ := lvl1_noNC' c t Nf (by simp [hNf]) (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1))
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 1 ∧ Δ.nV = Γ.nV + 1 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_oe2x_counters m Γ p q hp hq x y y' hy c t).2.2.1
  exact lvl1_good_k1a m Γ (owxEmb 1) (lvl1_owxEmb_inj (E := E) (I := I) 1) _ (Nf.map (lwSymmTwistS c t)) hR Δ
    (by rw [hsol]) hdot (Sum.inr 0) hc1 hc2 (by omega) hc4 (by omega) (by omega) (by omega) P hP


theorem lvl1_qne (c t : Bool) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y' : E ⊕ I)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hy' : y' ≠ Sum.inr x) :
    q.1.src ≠ q.1.dst := by
  intro h
  have := (lwSymmTwistS_loop c t q.1).2 h
  rw [hq1] at this
  exact hy' this

theorem lvl1_good_R2 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hy' : y' ≠ Sum.inr x)
    (P : PGraph E) (hP : P ∈ (lwSymmOe2xR2 c t m Γ p q x y y').partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOe2xR2 c t m Γ p q x y y' with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set Nf : List (SEdge (E ⊕ I)) := [⟨true, false, y', y⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (id : E ⊕ I → E ⊕ I)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOe2xR2 oe2xR2
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmFrame2Q, hNf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (id : E ⊕ I → E ⊕ I)) := by
    rw [hΔ]
    unfold lwSymmOe2xR2 oe2xR2
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map id)) (lvl1_frame2_dotted c t Γ p q)
  have hnc0 : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    simp only [hNf, List.mem_singleton] at he0
    subst he0
    simp [lwSymmTwistS_circ]
  have hI : ∀ e ∈ Nf.map (lwSymmTwistS c t), lvl1IncA (Sum.inr x) e = false := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    simp only [hNf, List.mem_singleton] at he0
    subst he0
    rw [lvl1_incA_twist]
    simp [lvl1IncA, Ne.symm hy, Ne.symm hy', hy, hy']
  have hlen := lvl1_nS_of_sol Δ (SEdge.map id) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hwΓ : lvl1Loops q.2 ≤ Γ.lvl1NLoops := by
    have := lvl1_loops_split Γ p hp q hq
    omega
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS + 1 = Γ.nS ∧ Δ.nW = Γ.nW + 1 ∧ Δ.nV = Γ.nV ∧ Δ.nM ≤ Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_oe2x_counters m Γ p q hp hq x y y' hy c t).2.1
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := fun e he hc => by
    rw [hnc0 e he] at hc; exact absurd hc (by simp)
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr x ∨ e.dst = Sum.inr x) → e.src ≠ e.dst := by
    intro e he _ hat
    exfalso
    have hh := hI e he
    simp only [lvl1IncA, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hh
    rcases hat with h | h
    · exact hh.1 h
    · exact hh.2 h
  have hA : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr x) e) ≤ 2 := by
    have : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr x) e) = 0 :=
      List.countP_eq_zero.2 (fun e he => by simp [hI e he])
    omega
  have hO : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr x) e) ≤ 1 := by
    calc _ ≤ (Nf.map (lwSymmTwistS c t)).length := List.countP_le_length
      _ = 1 := by simp [hNf]
  have hC : (Nf.map (lwSymmTwistS c t)).countP (fun e => e.circ) = 0 :=
    List.countP_eq_zero.2 (fun e he => by simp [hnc0 e he])
  have hord : ord Γ.counters + 1 ≤ ord Δ.counters := by omega
  have hVW : (Δ.nV : ℤ) - Δ.nW ≤ (Γ.nV : ℤ) - Γ.nW := by omega
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 1 := by simp [hNf]
  exact lvl1_good_k1b m Γ id Function.injective_id q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot x
    hcirc hαne hA hO hC hord c4 hVW (by omega) hwΓ (Or.inr (Or.inl (by omega))) P hP


theorem lvl1_good_R4 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool)
    (P : PGraph E) (hP : P ∈ (lwSymmOe2xR4 c t m Γ p q x y y').partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOe2xR4 c t m Γ p q x y y' with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 2))) :=
    [⟨true, false, Sum.inr (Sum.inr 0), owxEmb 2 y⟩, ⟨true, false, owxEmb 2 y', Sum.inr (Sum.inr 0)⟩,
      ⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 2)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOe2xR4 oe2xR4
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmFrame2Q, hNf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 2)) := by
    rw [hΔ]
    unfold lwSymmOe2xR4 oe2xR4
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 2))) (lvl1_frame2_dotted c t Γ p q)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 2
  have hy1 : owxEmb 2 y ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 2)) := fun h => lwSymm_emb_ne y 2 0 h.symm
  have hy2 : owxEmb 2 y' ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 2)) := fun h => lwSymm_emb_ne y' 2 0 h.symm
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_loop]
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl <;> simp_all
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he hc hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl
    all_goals first | (simp at hc; done) | simp_all
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) ≤ 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    split_ifs <;> simp_all
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    simp [lvl1IncA, hy1, hy2]
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 2)) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 3 := by simp [hNf]
  have hy0 : y ≠ Sum.inr x := hy
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 2 ∧ Δ.nV = Γ.nV + 2 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_oe2x_counters m Γ p q hp hq x y y' hy c t).2.2.2.1
  exact lvl1_good_k1a m Γ (owxEmb 2) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0)
    hcirc hαne hcnt2 hcnt3 (by omega) (by omega) (by omega) P hP

theorem lvl1_good_R5 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool)
    (P : PGraph E) (hP : P ∈ (lwSymmOe2xR5 c t m Γ p q x y y').partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOe2xR5 c t m Γ p q x y y' with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) :=
    [⟨true, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inl x)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 y⟩,
      ⟨true, false, owxEmb 1 y', Sum.inr (Sum.inr 0)⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOe2xR5 oe2xR5
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmFrame2Q, hNf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lwSymmOe2xR5 oe2xR5
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 1))) (lvl1_frame2_dotted c t Γ p q)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 1
  have hy1 : owxEmb 1 y ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lwSymm_emb_ne y 1 0 h.symm
  have hy2 : owxEmb 1 y' ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := fun h => lwSymm_emb_ne y' 1 0 h.symm
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_loop]
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl <;> simp_all
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he hc hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl
    all_goals first | (simp at hc; done) | simp_all
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) ≤ 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    split_ifs <;> simp_all
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    simp [lvl1IncA, hy1, hy2]
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 1)) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 3 := by simp [hNf]
  have hy0 : y ≠ Sum.inr x := hy
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 1 ∧ Δ.nV = Γ.nV + 1 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_oe2x_counters m Γ p q hp hq x y y' hy c t).2.2.2.2.1
  exact lvl1_good_k1a m Γ (owxEmb 1) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0)
    hcirc hαne hcnt2 hcnt3 (by omega) (by omega) (by omega) P hP

theorem lvl1_good_R6 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool)
    (P : PGraph E) (hP : P ∈ (lwSymmOe2xR6 c t m Γ p q x y y').partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOe2xR6 c t m Γ p q x y y' with hΔ
  have hsubΓ : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hR := lvl1_hR_of_normal Γ hN q.2 hsubΓ
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 2))) :=
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 y⟩,
      ⟨true, false, owxEmb 2 y', Sum.inr (Sum.inr 1)⟩] with hNf
  have hsol : Δ.solid = q.2.map (SEdge.map (owxEmb 2)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOe2xR6 oe2xR6
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmFrame2Q, hNf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 2)) := by
    rw [hΔ]
    unfold lwSymmOe2xR6 oe2xR6
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 2))) (lvl1_frame2_dotted c t Γ p q)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 2
  have hy1 : owxEmb 2 y ≠ (Sum.inr (Sum.inr 1) : E ⊕ (I ⊕ Fin 2)) := fun h => lwSymm_emb_ne y 2 1 h.symm
  have hy2 : owxEmb 2 y' ≠ (Sum.inr (Sum.inr 1) : E ⊕ (I ⊕ Fin 2)) := fun h => lwSymm_emb_ne y' 2 1 h.symm
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_loop]
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl <;> simp_all
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 1) ∨ e.dst = Sum.inr (Sum.inr 1)) → e.src ≠ e.dst := by
    intro e he hc hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    simp only [hNf, List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl
    all_goals first | (simp at hc; done) | simp_all
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 1)) e) ≤ 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    split_ifs <;> simp_all
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 1)) e) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    simp only [hNf, List.countP_cons, List.countP_nil]
    simp [lvl1IncA, hy1, hy2]
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 2)) q.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 3 := by simp [hNf]
  have hy0 : y ≠ Sum.inr x := hy
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 2 ∧ Δ.nV = Γ.nV + 2 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_oe2x_counters m Γ p q hp hq x y y' hy c t).2.2.2.2.2.1
  exact lvl1_good_k1a m Γ (owxEmb 2) hemb q.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 1)
    hcirc hαne hcnt2 hcnt3 (by omega) (by omega) (by omega) P hP

theorem lvl1_good_R8 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2)
    (P : PGraph E) (hP : P ∈ (lwSymmOe2xR8 c t m Γ p q x y y' q').partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOe2xR8 c t m Γ p q x y y' q' with hΔ
  have hsubΓ : ∀ e ∈ q'.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e (lvl1_mem_split _ q' hq' e he))
  have hR := lvl1_hR_of_normal Γ hN q'.2 hsubΓ
  set α : E ⊕ (I ⊕ Fin 2) := Sum.inr (Sum.inr 0) with hα
  set β : E ⊕ (I ⊕ Fin 2) := Sum.inr (Sum.inr 1) with hβ
  set qf := lwSymmTwistS c t q'.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 2))) :=
    [⟨true, false, β, owxEmb 2 y⟩, ⟨true, false, owxEmb 2 y', α⟩, (owxDE β α (SEdge.map (owxEmb 2) qf)).1,
      (owxDE β α (SEdge.map (owxEmb 2) qf)).2] with hNf
  have hsol : Δ.solid = q'.2.map (SEdge.map (owxEmb 2)) ++ Nf.map (lwSymmTwistS c t) := by
    rw [hΔ]
    unfold lwSymmOe2xR8 oe2xR8
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hβ, hqf]
    rw [lvl1_twist_twist_list]
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 2)) := by
    rw [hΔ]
    unfold lwSymmOe2xR8 oe2xR8
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 2))) (lvl1_frame2_dotted c t Γ p q)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 2
  have hne : ∀ (v : E ⊕ I) (j : Fin 2), owxEmb 2 v ≠ (Sum.inr (Sum.inr j) : E ⊕ (I ⊕ Fin 2)) := by
    intro v j h
    exact lwSymm_emb_ne v 2 j h.symm
  have hαβ : α ≠ β := by simp [hα, hβ]
  obtain ⟨hc0, hnc, hOA, hOB, hAB⟩ := lvl1_R8Nf α β (owxEmb 2 y) (owxEmb 2 y') hαβ (SEdge.map (owxEmb 2) qf)
    (hne _ 0) (hne _ 0) (hne _ 1) (hne _ 1) (hne _ 0) (hne _ 1) (hne _ 0) (hne _ 1)
  have hnc' : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false → e.src ≠ e.dst ∧
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0) ∨ e.src = Sum.inr (Sum.inr 1) ∨
        e.dst = Sum.inr (Sum.inr 1)) := by
    intro e he _
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    obtain ⟨hl, hat⟩ := hnc e0 he0
    exact ⟨fun h => hl ((lwSymmTwistS_loop c t e0).1 h), (lvl1_touch_twist c t e0 α β).2 hat⟩
  have hA' : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1OldA (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) e) = 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_oldA_twist])]
    exact hOA
  have hB' : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1OldA (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) e) = 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_oldA_twist])]
    exact hOB
  have hAB' : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1AB (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) e) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_ab_twist])]
    exact hAB
  have hlen := lvl1_nS_of_sol Δ (SEdge.map (owxEmb 2)) q'.2 _ hsol
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hsl'' := lwSplit_snd_length q.2 q' hq'
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 4 := by simp [hNf]
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 2 ∧ Δ.nV = Γ.nV + 2 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_oe2x_counters m Γ p q hp hq x y y' hy c t).2.2.2.2.2.2.2 q' hq'
  refine lvl1_good_k2 m Γ (owxEmb 2) hemb q'.2 (Nf.map (lwSymmTwistS c t)) hR Δ (by rw [hsol]) hdot (Sum.inr 0) (Sum.inr 1)
    (by simp) hnc' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) P hP

theorem lvl1_good_R7 (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hy' : y' ≠ Sum.inr x)
    (hx2 : ∀ e ∈ q.2, e.src ≠ Sum.inr x ∧ e.dst ≠ Sum.inr x)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2)
    (P : PGraph E) (hP : P ∈ (lwSymmOe2xR7 c t m Γ p q x y y' q').partition m) : Lvl1Good Γ P.g := by
  classical
  set Δ := lwSymmOe2xR7 c t m Γ p q x y y' q' with hΔ
  have hqne := lvl1_qne c t q x y' hq1 hy'
  have hqΓ : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hsubΓ : ∀ e ∈ q'.2, e ∈ Γ.solid := fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e (lvl1_mem_split _ q' hq' e he))
  have hR : ∀ e ∈ ({ q.1 with circ := false } :: q'.2 : List (SEdge (E ⊕ I))),
      (e.src ≠ e.dst → Γ.XBetween e.src e.dst) ∧ (e.src = e.dst → e.circ = true) := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨fun _ => (hN.2.1 _ _ hqne).2 ⟨q.1, hqΓ, hqne, Or.inl ⟨rfl, rfl⟩⟩, fun h => absurd h hqne⟩
    · exact lvl1_hR_of_normal Γ hN q'.2 hsubΓ e he
  set α : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inr 0) with hα
  set xx : E ⊕ (I ⊕ Fin 1) := Sum.inr (Sum.inl x) with hxx
  set qf := lwSymmTwistS c t q'.1 with hqf
  set Nf : List (SEdge (E ⊕ (I ⊕ Fin 1))) :=
    [(owxDE α xx (SEdge.map (owxEmb 1) qf)).1, (owxDE α xx (SEdge.map (owxEmb 1) qf)).2,
      ⟨true, false, α, owxEmb 1 y⟩] with hNf
  -- the re-added edge is the (uncircled) edge `q.1`
  have hg0 : lwSymmTwistS c t (⟨true, false, owxEmb 1 y', xx⟩ : SEdge (E ⊕ (I ⊕ Fin 1))) =
      SEdge.map (owxEmb 1) { q.1 with circ := false } := by
    have h1 : lwSymmTwistS c t { q.1 with circ := false } = ⟨true, false, y', Sum.inr x⟩ := by
      rw [lwSymmTwistS_with_circ, hq1]
    have h2 : ({ q.1 with circ := false } : SEdge (E ⊕ I)) = lwSymmTwistS c t ⟨true, false, y', Sum.inr x⟩ := by
      rw [← h1, lwSymmTwistS_invol]
    rw [h2]
    have : (⟨true, false, owxEmb 1 y', xx⟩ : SEdge (E ⊕ (I ⊕ Fin 1))) =
        SEdge.map (owxEmb 1) ⟨true, false, y', Sum.inr x⟩ := rfl
    rw [this, lvl1_twistS_map]
  have hsol0 : Δ.solid = q'.2.map (SEdge.map (owxEmb 1)) ++
      (SEdge.map (owxEmb 1) { q.1 with circ := false } :: Nf.map (lwSymmTwistS c t)) := by
    rw [hΔ]
    unfold lwSymmOe2xR7 oe2xR7
    rw [lvl1_twist_owxExt_solid]
    simp only [lwSymmTwistP, hNf, hα, hxx, hqf, List.map_cons]
    rw [lvl1_twist_twist_list]
    simp only [List.map_nil]
    rw [hg0]
  have hsol : Δ.solid.Perm (({ q.1 with circ := false } :: q'.2).map (SEdge.map (owxEmb 1)) ++ Nf.map (lwSymmTwistS c t)) := by
    rw [hsol0]
    simp only [List.map_cons]
    exact List.perm_middle
  have hdot : Δ.dotted = Γ.dotted.map (DEdge.map (owxEmb 1)) := by
    rw [hΔ]
    unfold lwSymmOe2xR7 oe2xR7
    rw [lvl1_twist_owxExt_dotted]
    exact congrArg (List.map (DEdge.map (owxEmb 1))) (lvl1_frame2_dotted c t Γ p q)
  have hemb := lvl1_owxEmb_inj (E := E) (I := I) 1
  have hne1 : (SEdge.map (owxEmb 1) qf).src ≠ α := fun h => lvl1_owxEmb_ne qf.src 0 h
  have hne2 : (SEdge.map (owxEmb 1) qf).dst ≠ α := fun h => lvl1_owxEmb_ne qf.dst 0 h
  have hxa : xx ≠ α := by simp [hxx, hα]
  have hza : owxEmb 1 y ≠ α := fun h => lvl1_owxEmb_ne y 0 h
  obtain ⟨hc0, hnl, hcA, hcO⟩ := lvl1_derivNf α xx (owxEmb 1 y) (SEdge.map (owxEmb 1) qf) hne1 hne2 hxa hza
  -- the old-old edge is not at `x`
  have hq'x : q'.1.src ≠ Sum.inr x ∧ q'.1.dst ≠ Sum.inr x := hx2 q'.1 (lvl1_mem_split_fst _ q' hq')
  have hqfx : qf.src ≠ Sum.inr x ∧ qf.dst ≠ Sum.inr x := by
    rcases lvl1_ends_twist c t q'.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hqf]; rw [h1, h2]; exact hq'x
    · rw [hqf]; rw [h1, h2]; exact ⟨hq'x.2, hq'x.1⟩
  have hhoo := lvl1_derivNf_hoo α xx (owxEmb 1 y) (SEdge.map (owxEmb 1) qf) hne1 hne2 hxa hza (by simp [hxx])
    ⟨fun _ hh => hqfx.2 (lvl1_owxEmb_inj (E := E) (I := I) 1 (show owxEmb 1 qf.dst = owxEmb 1 (Sum.inr x) from hh)),
     fun _ hh => hqfx.1 (lvl1_owxEmb_inj (E := E) (I := I) 1 (show owxEmb 1 qf.src = owxEmb 1 (Sum.inr x) from hh))⟩
  have hcirc : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ, hc0 e0 he0] at hc
    exact absurd hc (by simp)
  have hαne : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false →
      (e.src = Sum.inr (Sum.inr 0) ∨ e.dst = Sum.inr (Sum.inr 0)) → e.src ≠ e.dst := by
    intro e he _ hat
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_at] at hat
    intro hl
    rw [lwSymmTwistS_loop] at hl
    exact hnl e0 he0 hat hl
  have hcnt2 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && lvl1IncA (Sum.inr (Sum.inr 0)) e) = 2 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    exact hcA
  have hcnt3 : (Nf.map (lwSymmTwistS c t)).countP (fun e => !e.circ && !lvl1IncA (Sum.inr (Sum.inr 0)) e) = 1 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ, lvl1_incA_twist])]
    exact hcO
  have hcnt1 : (Nf.map (lwSymmTwistS c t)).countP (fun e => e.circ) = 0 := by
    rw [lvl1_countP_twist c t _ (fun e => by simp [lwSymmTwistS_circ])]
    rw [List.countP_eq_zero]
    intro e he
    simp [hc0 e he]
  have hhoo' : ∀ e ∈ Nf.map (lwSymmTwistS c t), e.circ = false → lvl1IncA (Sum.inr (Sum.inr 0)) e = false →
      e.src ≠ e.dst ∧ (e.src.isRight = true ∨ e.dst.isRight = true) := by
    intro e he hc hi
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [lwSymmTwistS_circ] at hc
    rw [lvl1_incA_twist] at hi
    obtain ⟨h1, h2⟩ := hhoo e0 he0 hc hi
    exact ⟨fun h => h1 ((lwSymmTwistS_loop c t e0).1 h), (lvl1_isRight_twist c t e0).2 h2⟩
  have hlen : Δ.nS = q'.2.length + 4 := by simp [LGraph.nS, hsol0, hNf]
  have hsl := lwSplit_snd_length Γ.solid p hp
  have hsl' := lwSplit_snd_length p.2 q hq
  have hsl'' := lwSplit_snd_length q.2 q' hq'
  have hNlen : (Nf.map (lwSymmTwistS c t)).length = 3 := by simp [hNf]
  have hwΓ : lvl1Loops ({ q.1 with circ := false } :: q'.2) ≤ Γ.lvl1NLoops := by
    have h1 := lvl1_loops_split Γ p hp q hq
    have h2 := lvl1_loops_perm (lwSplit_perm q.2 q' hq')
    rw [lvl1_loops_cons] at h2
    rw [lvl1_loops_cons]
    have h3 : ¬ (({ q.1 with circ := false } : SEdge (E ⊕ I)).src = ({ q.1 with circ := false } : SEdge (E ⊕ I)).dst) := hqne
    rw [if_neg h3]
    omega
  obtain ⟨c1, c2, c3, c4, c5⟩ : Δ.nS = Γ.nS + 1 ∧ Δ.nW = Γ.nW + 1 ∧ Δ.nV = Γ.nV + 1 ∧ Δ.nM = Γ.nM ∧
      ord Δ.counters = ord Γ.counters + 1 := (lwSymm_oe2x_counters m Γ p q hp hq x y y' hy c t).2.2.2.2.2.2.1 q' hq'
  exact lvl1_good_k1b m Γ (owxEmb 1) hemb ({ q.1 with circ := false } :: q'.2) (Nf.map (lwSymmTwistS c t)) hR Δ hsol hdot
    (Sum.inr 0) hcirc hαne (by omega) (by omega) hcnt1 (by omega) (by omega) (by omega) (by omega) hwΓ
    (Or.inr (Or.inr hhoo')) P hP

end Step3
end RBM.Graph
end Lvl1PartT4

/-! ## 8. Step 3 (all terms) -/

section Lvl1PartT5
open RBM.Graph

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Step3d

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **A vertex of degree two has no other edges**: the edges `q.2` other than `p.1`, `q.1` at `X` are absent. -/
theorem lvl1_isolated (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (X : E ⊕ I)
    (hpX : p.1.lvl1IncAt X = true) (hqX : q.1.lvl1IncAt X = true) (hdeg : Γ.lvl1DegAt X = 2) :
    ∀ e ∈ q.2, e.lvl1IncAt X = false := by
  intro e he
  by_contra hne
  have hperm : (Γ.lvl1SolidAt X).Perm (p.1 :: q.1 :: q.2.filter (fun e => e.lvl1IncAt X)) := by
    unfold LGraph.lvl1SolidAt
    have h1 := ((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)).filter
      (fun e => e.lvl1IncAt X)
    rw [List.filter_cons_of_pos (by simpa using hpX), List.filter_cons_of_pos (by simpa using hqX)] at h1
    exact h1
  have hlen := hperm.length_eq
  unfold LGraph.lvl1DegAt at hdeg
  rw [hdeg] at hlen
  simp only [List.length_cons] at hlen
  have hpos : 0 < (q.2.filter (fun e => e.lvl1IncAt X)).length :=
    List.length_pos_of_mem (List.mem_filter.2 ⟨he, by simpa using hne⟩)
  omega

theorem lvl1_incAt_of_twist (c t : Bool) (e : SEdge (E ⊕ I)) (X a : E ⊕ I) (hne : a ≠ X)
    (h : lwSymmTwistS c t e = ⟨true, e.circ, X, a⟩) : e.lvl1IncAt X = true := by
  rw [lvl1_incAt_iff]
  have hloop : e.src ≠ e.dst := by
    intro hl
    have := (lwSymmTwistS_loop c t e).2 hl
    rw [h] at this
    exact hne this.symm
  refine ⟨hloop, ?_⟩
  rcases lvl1_ends_of_twist c t e X a (by rw [h]; exact ⟨rfl, rfl⟩) with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2

theorem lvl1_incAt_of_twist' (c t : Bool) (e : SEdge (E ⊕ I)) (X a : E ⊕ I) (hne : a ≠ X)
    (h : lwSymmTwistS c t e = ⟨true, e.circ, a, X⟩) : e.lvl1IncAt X = true := by
  rw [lvl1_incAt_iff]
  have hloop : e.src ≠ e.dst := by
    intro hl
    have := (lwSymmTwistS_loop c t e).2 hl
    rw [h] at this
    exact hne this
  refine ⟨hloop, ?_⟩
  rcases lvl1_ends_of_twist c t e a X (by rw [h]; exact ⟨rfl, rfl⟩) with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact Or.inr h2
  · exact Or.inl h1


/-- **The one-step claims for the terms of `(Oe2x)` other than `R1`** (`R1` has value zero). -/
theorem lvl1_good_gg (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩)
    (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst) (hdeg : Γ.lvl1DegAt (Sum.inr x) = 2) :
    (∀ P ∈ (lwSymmOe2xR2 c t m Γ p q x y y').partition m, Lvl1Good Γ P.g) ∧
    (∀ P ∈ (lwSymmOe2xR3 c t m Γ p q x).partition m, Lvl1Good Γ P.g) ∧
    (∀ P ∈ (lwSymmOe2xR4 c t m Γ p q x y y').partition m, Lvl1Good Γ P.g) ∧
    (∀ P ∈ (lwSymmOe2xR5 c t m Γ p q x y y').partition m, Lvl1Good Γ P.g) ∧
    (∀ P ∈ (lwSymmOe2xR6 c t m Γ p q x y y').partition m, Lvl1Good Γ P.g) ∧
    (∀ q' ∈ lwSplit q.2, ∀ P ∈ (lwSymmOe2xR7 c t m Γ p q x y y' q').partition m, Lvl1Good Γ P.g) ∧
    (∀ q' ∈ lwSplit q.2, ∀ P ∈ (lwSymmOe2xR8 c t m Γ p q x y y' q').partition m, Lvl1Good Γ P.g) := by
  have hqΓ : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hqne : q.1.src ≠ q.1.dst := hwf q.1 hqΓ
  have hy' : y' ≠ Sum.inr x := by
    intro h
    apply hqne
    rw [← lwSymmTwistS_loop c t q.1, hq1]
    exact h
  have hpX := lvl1_incAt_of_twist c t p.1 (Sum.inr x) y hy hp1
  have hqX := lvl1_incAt_of_twist' c t q.1 (Sum.inr x) y' hy' hq1
  have hiso := lvl1_isolated Γ p hp q hq (Sum.inr x) hpX hqX hdeg
  have hx2 : ∀ e ∈ q.2, e.src ≠ Sum.inr x ∧ e.dst ≠ Sum.inr x := by
    intro e he
    have h1 := hiso e he
    have h2 := hwf e (lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
    rw [← Bool.not_eq_true, lvl1_incAt_iff] at h1
    push Not at h1
    exact ⟨fun h => by simpa using h1 h2 |>.1 h |> fun x => x, fun h => by simpa using (h1 h2).2 h⟩
  exact ⟨fun P hP => lvl1_good_R2 m Γ hN p q hp hq x y y' hy c t hp1 hq1 hy' P hP,
    fun P hP => lvl1_good_R3 m Γ hN p q hp hq x y y' hy c t hp1 hq1 hy' P hP,
    fun P hP => lvl1_good_R4 m Γ hN p q hp hq x y y' hy c t P hP,
    fun P hP => lvl1_good_R5 m Γ hN p q hp hq x y y' hy c t P hP,
    fun P hP => lvl1_good_R6 m Γ hN p q hp hq x y y' hy c t P hP,
    fun q' hq' P hP => lvl1_good_R7 m Γ hN p q hp hq x y y' hy c t hp1 hq1 hy' hx2 q' hq' P hP,
    fun q' hq' P hP => lvl1_good_R8 m Γ hN p q hp hq x y y' hy c t q' hq' P hP⟩

end Step3d
end RBM.Graph
end Lvl1PartT5

/-! ## 9. Packed outputs and the integral of a term -/

section Lvl1PartV
open MeasureTheory ProbabilityTheory
open RBM RBM.Gauss RBM.Green RBM.Graph

noncomputable section

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Comp

variable {E E' : Type}

/-- **A packed graph read through a surjection of the external vertices**: the graphs of a step are packed over the external
vertices of the input, which are themselves the image of the original ones. -/
def PGraph.lvl1Comp (Q : PGraph E') (f : E → E') (hf : Function.Surjective f) : PGraph E where
  E' := Q.E'
  I' := Q.I'
  ext := Q.ext ∘ f
  ext_surj := Q.ext_surj.comp hf
  g := Q.g

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
theorem PGraph.lvl1Comp_val (Q : PGraph E') (f : E → E') (hf : Function.Surjective f) (D : LData ι) (ℓe : E → ι) :
    (Q.lvl1Comp f hf).val D ℓe = if h : ∃ ℓ' : E' → ι, ℓe = ℓ' ∘ f then Q.val D h.choose else 0 := by
  classical
  by_cases h : ∃ ℓ' : E' → ι, ℓe = ℓ' ∘ f
  · rw [dif_pos h]
    have hc : ℓe = h.choose ∘ f := h.choose_spec
    by_cases h3 : ∃ ℓ'' : Q.E' → ι, h.choose = ℓ'' ∘ Q.ext
    · obtain ⟨ℓ'', hℓ''⟩ := h3
      rw [PGraph.val_of_factor Q D hℓ'']
      refine PGraph.val_of_factor (Q.lvl1Comp f hf) D (ℓ' := ℓ'') ?_
      rw [hc, hℓ'']
      rfl
    · rw [PGraph.val_of_not Q D h3]
      refine PGraph.val_of_not (Q.lvl1Comp f hf) D ?_
      rintro ⟨ℓ'', hℓ''⟩
      apply h3
      refine ⟨ℓ'', ?_⟩
      have : h.choose ∘ f = (ℓ'' ∘ Q.ext) ∘ f := by rw [← hc, hℓ'']; rfl
      exact hf.injective_comp_right this
  · rw [dif_neg h]
    refine PGraph.val_of_not (Q.lvl1Comp f hf) D ?_
    rintro ⟨ℓ'', hℓ''⟩
    exact h ⟨ℓ'' ∘ Q.ext, hℓ''⟩


variable {E : Type}

/-- the graphs of the dotted edge partition of a term `T` of a step, packed over the external vertices of the input -/
def lvl1Outs (P : PGraph E) (m : ℂ) {I'' : Type} [Fintype I''] [DecidableEq I''] (T : LGraph P.E' I'') :
    List (PGraph E) :=
  (T.partition m).map fun Q => Q.lvl1Comp P.ext P.ext_surj

end Comp

section Integral

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
  (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- the value of a packed graph at the sample is integrable -/
theorem lvl1_pval_integrable (hG : GaussIBP sz) (hz : 0 < z.im) {E' : Type} [Fintype E'] [DecidableEq E']
    (Q : PGraph E') (ℓ' : E' → Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => Q.val (lwSampleData sz n z u M S Sp ω) ℓ') (Sizes.seqP sz) := by
  classical
  by_cases h : ∃ ℓ'' : Q.E' → Idx d (sz.L n) (sz.W n), ℓ' = ℓ'' ∘ Q.ext
  · obtain ⟨ℓ'', hℓ''⟩ := h
    have : (fun ω => Q.val (lwSampleData sz n z u M S Sp ω) ℓ') =
        fun ω => Q.g.val (lwSampleData sz n z u M S Sp ω) ℓ'' := by
      funext ω
      exact PGraph.val_of_factor Q _ hℓ''
    rw [this]
    exact oe1x_val_integrable (sz := sz) (n := n) hG hz (u := u) M S Sp Q.g ℓ''
  · have : (fun ω => Q.val (lwSampleData sz n z u M S Sp ω) ℓ') = fun _ => 0 := by
      funext ω
      exact PGraph.val_of_not Q _ h
    rw [this]
    exact integrable_zero _ _ _

/-- **The integral of a term is the sum of the integrals of the terms of its dotted edge partition** (`val_eq_partition`). -/
theorem lvl1_term_integral (hG : GaussIBP sz) (hz : 0 < z.im) {m : ℂ} (hM : ∀ a, M a a = m)
    {E' I'' : Type} [Fintype E'] [DecidableEq E'] [Fintype I''] [DecidableEq I''] (T : LGraph E' I'')
    (ℓ' : E' → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓ' ∂(Sizes.seqP sz) =
      ((T.partition m).map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M S Sp ω) ℓ' ∂(Sizes.seqP sz)).sum := by
  have h1 : ∀ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓ' =
      ((T.partition m).map fun Q => Q.val (lwSampleData sz n z u M S Sp ω) ℓ').sum := fun ω =>
    T.val_eq_partition m (lwSampleData sz n z u M S Sp ω) (fun a => hM a) ℓ'
  simp_rw [h1]
  exact owx_integral_list_sum (Sizes.seqP sz) (T.partition m)
    (fun Q ω => Q.val (lwSampleData sz n z u M S Sp ω) ℓ') fun Q _ => lvl1_pval_integrable M S Sp hG hz Q ℓ'

end Integral
end RBM.Graph
end
end Lvl1PartV

/-! ## 10. `deflvl1` (`LGraph.LocStd`), `strat_local` as a one-step relation (`LocStep`), reachability, `lvl1_step_good` -/

section Lvl1PartS
open MeasureTheory ProbabilityTheory
open RBM RBM.Gauss RBM.Green RBM.Graph

noncomputable section

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section LocStdDef

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **A standard neutral vertex** (`deflvl1`, `7_8:376-385`): exactly two solid edges, of opposite colours (`opposite charges`:
one `G`, one `Ḡ`), and neutral charge `(eq:neutralcharge)`. -/
def LGraph.StdNeutral (Γ : LGraph E I) (v : E ⊕ I) : Prop :=
  ((Γ.lvl1SolidAt v).map SEdge.σ = [true, false] ∨ (Γ.lvl1SolidAt v).map SEdge.σ = [false, true]) ∧ Γ.lvl1ChargeAt v = 0

/-- **Locally standard graphs** (`deflvl1`, `7_8:367-386`): (i) normal; (ii) no self-loops (no weight, no light-weight);
(iii) every internal vertex is standard neutral or not incident to any solid edge. -/
def LGraph.LocStd (Γ : LGraph E I) : Prop :=
  Γ.Normal ∧ (∀ e ∈ Γ.solid, e.src ≠ e.dst) ∧
    ∀ i : I, Γ.StdNeutral (Sum.inr i) ∨ Γ.lvl1DegAt (Sum.inr i) = 0

instance (Γ : LGraph E I) (v : E ⊕ I) : Decidable (Γ.StdNeutral v) := by
  unfold LGraph.StdNeutral; infer_instance

instance (Γ : LGraph E I) : Decidable Γ.LocStd := by
  unfold LGraph.LocStd; infer_instance

/-- locally standard packed graphs -/
def PGraph.LocStd {E : Type} (P : PGraph E) : Prop := P.g.LocStd

instance {E : Type} (P : PGraph E) : Decidable P.LocStd := by
  unfold PGraph.LocStd; infer_instance

end LocStdDef

section LocStepDef

variable {E : Type}

/-- **Step 1 of `strat_local`** (`B:138-145`): the four terms of `(Owx)` at the light-weight `p.1` at `x`, each followed by the dotted
edge partition. -/
def lvl1WeightOuts0 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : E' ⊕ I') (c t : Bool) : List (PGraph E') :=
  (lwSymmOwxT1 c t m Γ x).partition m ++ (lwSymmOwxT2 c t m Γ p x).partition m ++
    (lwSplit p.2).flatMap (fun q => (lwSymmOwxT3 c t m Γ x q).partition m) ++
    (lwSplit p.2).flatMap (fun q => (lwSymmOwxT4 c t m Γ x q).partition m)

/-- **Step 2 of `strat_local`** (`B:146-149`): the terms of `(Oe1x)` at the edge `p.1` at the internal vertex `x`, each followed by the
dotted edge partition; the term `m 1_{x = y₁}` is `0` on a normal graph (the `×`-dotted edge `x ≠ y₁`) and is not listed. -/
def lvl1EdgeOuts0 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (v : E' ⊕ I') (c t : Bool) : List (PGraph E') :=
  (lwSymmOe1xOwx c t m Γ p x).partition m ++
    (lwSplit p.2).flatMap (fun q => (lwSymmOe1xDs c t m Γ p x v q).flatMap (fun T => T.partition m))

/-- **Step 3 of `strat_local`** (`B:150-156`): the terms of `(Oe2x)` at the pair `p.1`, `q.1` at the internal vertex `x`, each followed
by the dotted edge partition; the term `R1` is `0` on a normal graph and is not listed. -/
def lvl1GGOuts0 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
    (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (y y' : E' ⊕ I') (c t : Bool) : List (PGraph E') :=
  (lwSymmOe2xR2 c t m Γ p q x y y').partition m ++ (lwSymmOe2xR3 c t m Γ p q x).partition m ++
    (lwSymmOe2xR4 c t m Γ p q x y y').partition m ++ (lwSymmOe2xR5 c t m Γ p q x y y').partition m ++
    (lwSymmOe2xR6 c t m Γ p q x y y').partition m ++
    (lwSplit q.2).flatMap (fun q' => (lwSymmOe2xR7 c t m Γ p q x y y' q').partition m) ++
    (lwSplit q.2).flatMap (fun q' => (lwSymmOe2xR8 c t m Γ p q x y y' q').partition m)

/-- the outputs of a step, packed over the external vertices of the input -/
def lvl1Pack (P : PGraph E) (L : List (PGraph P.E')) : List (PGraph E) :=
  L.map fun Q => Q.lvl1Comp P.ext P.ext_surj

/-- **One step of the local expansion strategy `strat_local`** (`B:135-157`) on packed graphs: `LocStep m P outs` says that `outs` is the list
of graphs produced from `P` by the first step that is not null: Step 1 at a (light-)weight; else Step 2 at an internal vertex of
degree `∉ {0, 2}` or non-neutral charge; else Step 3 at an internal vertex with two solid edges of the same charge.  The
selectors `(c, t)` make the selected edge the blue out-edge (`lwSymmTwistS`); each output is followed by the dotted edge
partition. -/
inductive LocStep (m : ℂ) : PGraph E → List (PGraph E) → Prop
  | weight (P : PGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (x : P.E' ⊕ P.I') (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) :
      LocStep m P (lvl1Pack P (lvl1WeightOuts0 m P.g p x c t))
  | edge (P : PGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (x : P.I') (v : P.E' ⊕ P.I') (hv : v ≠ Sum.inr x) (c t : Bool)
      (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) (hwf : ∀ e ∈ P.g.solid, e.src ≠ e.dst)
      (hbad : P.g.lvl1DegAt (Sum.inr x) ≠ 0 ∧ (P.g.lvl1DegAt (Sum.inr x) ≠ 2 ∨ P.g.lvl1ChargeAt (Sum.inr x) ≠ 0)) :
      LocStep m P (lvl1Pack P (lvl1EdgeOuts0 m P.g p x v c t))
  | gg (P : PGraph E) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (hq : q ∈ lwSplit p.2) (x : P.I') (y y' : P.E' ⊕ P.I') (hy : y ≠ Sum.inr x) (c t : Bool)
      (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
      (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hwf : ∀ e ∈ P.g.solid, e.src ≠ e.dst)
      (hnb : ∀ i : P.I', P.g.lvl1DegAt (Sum.inr i) = 0 ∨ (P.g.lvl1DegAt (Sum.inr i) = 2 ∧ P.g.lvl1ChargeAt (Sum.inr i) = 0)) :
      LocStep m P (lvl1Pack P (lvl1GGOuts0 m P.g p q x y y' c t))

/-- **Reachability by the strategy**: `Q` is reached from `P` by steps applied to graphs below the cutoff `K` that are not locally standard. -/
inductive Lvl1Reach (m : ℂ) (K : ℤ) : PGraph E → PGraph E → Prop
  | refl (P : PGraph E) : Lvl1Reach m K P P
  | step (P Q R : PGraph E) (L : List (PGraph E)) : Lvl1Reach m K P Q → ord Q.g.counters < K → ¬ Q.g.LocStd →
      LocStep m Q L → R ∈ L → Lvl1Reach m K P R

end LocStepDef

section StepGood

variable {E : Type}

/-- **Every output of a step is good for its input**: normal, the order does not fall, `n_M` and `n_V - n_W` do not grow, and
either the order rises or it stays and the measure falls. -/
theorem lvl1_step_good {m : ℂ} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs) (hN : P.g.Normal) :
    ∀ Q ∈ outs, Q.g.Normal ∧ Lvl1Good P.g Q.g := by
  have key : ∀ {I'' : Type} [Fintype I''] [DecidableEq I''] (T : LGraph P.E' I'')
      (hT : ∀ Q0 ∈ T.partition m, Lvl1Good P.g Q0.g) (Q0 : PGraph P.E'), Q0 ∈ T.partition m →
      Q0.g.Normal ∧ Lvl1Good P.g Q0.g := by
    intro I'' _ _ T hT Q0 hQ0
    exact ⟨LGraph.partition_normal m T Q0 hQ0, hT Q0 hQ0⟩
  cases hst with
  | weight p hp x c t hx =>
    intro Q hQ
    unfold lvl1Pack at hQ
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hQ
    simp only [lvl1WeightOuts0, List.mem_append, List.mem_flatMap] at hQ0
    show Q0.g.Normal ∧ Lvl1Good P.g Q0.g
    rcases hQ0 with ((hQ | hQ) | ⟨q, hq, hQ⟩) | ⟨q, hq, hQ⟩
    · exact key _ (fun Q0 hQ0 => lvl1_good_owxT1 m P.g hN p hp x c t Q0 hQ0) Q0 hQ
    · exact key _ (fun Q0 hQ0 => lvl1_good_owxT2 m P.g hN p hp x c t Q0 hQ0) Q0 hQ
    · exact key _ (fun Q0 hQ0 => lvl1_good_owxT3 m P.g hN p hp x c t hx q hq Q0 hQ0) Q0 hQ
    · exact key _ (fun Q0 hQ0 => lvl1_good_owxT4 m P.g hN p hp x c t q hq Q0 hQ0) Q0 hQ
  | edge p hp x v hv c t hx hwf hbad =>
    intro Q hQ
    unfold lvl1Pack at hQ
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hQ
    simp only [lvl1EdgeOuts0, List.mem_append, List.mem_flatMap] at hQ0
    show Q0.g.Normal ∧ Lvl1Good P.g Q0.g
    rcases hQ0 with hQ | ⟨q, hq, T, hT, hQ⟩
    · exact key _ (fun Q0 hQ0 => lvl1_good_oe1xOwx m P.g hN p hp x v hv c t hx Q0 hQ0) Q0 hQ
    · exact key T (fun Q0 hQ0 => lvl1_good_oe1xDs m P.g hN p hp x v hv c t hx hwf hbad q hq T hT Q0 hQ0) Q0 hQ
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb =>
    intro Q hQ
    unfold lvl1Pack at hQ
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hQ
    have hqΓ : q.1 ∈ P.g.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
    have hqne : q.1.src ≠ q.1.dst := hwf q.1 hqΓ
    have hy' : y' ≠ Sum.inr x := by
      intro h
      apply hqne
      rw [← lwSymmTwistS_loop c t q.1, hq1]
      exact h
    have hpX := lvl1_incAt_of_twist c t p.1 (Sum.inr x) y hy hp1
    have hdeg : P.g.lvl1DegAt (Sum.inr x) = 2 := by
      rcases hnb x with h | ⟨h, _⟩
      · exfalso
        have hmem : p.1 ∈ P.g.lvl1SolidAt (Sum.inr x) :=
          List.mem_filter.2 ⟨lvl1_mem_split_fst _ p hp, hpX⟩
        have : 0 < (P.g.lvl1SolidAt (Sum.inr x)).length := List.length_pos_of_mem hmem
        unfold LGraph.lvl1DegAt at h
        omega
      · exact h
    obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := lvl1_good_gg m P.g hN p q hp hq x y y' hy c t hp1 hq1 hwf hdeg
    simp only [lvl1GGOuts0, List.mem_append, List.mem_flatMap] at hQ0
    show Q0.g.Normal ∧ Lvl1Good P.g Q0.g
    rcases hQ0 with (((((hQ | hQ) | hQ) | hQ) | hQ) | ⟨q', hq', hQ⟩) | ⟨q', hq', hQ⟩
    · exact key _ h2 Q0 hQ
    · exact key _ h3 Q0 hQ
    · exact key _ h4 Q0 hQ
    · exact key _ h5 Q0 hQ
    · exact key _ h6 Q0 hQ
    · exact key _ (h7 q' hq') Q0 hQ
    · exact key _ (h8 q' hq') Q0 hQ

end StepGood
end RBM.Graph
end
end Lvl1PartS

/-! ## 11. The expectation identity of one step (`lvl1_step_identity`) -/

section Lvl1PartV2
open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green RBM.Graph

noncomputable section

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Zero

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- a `×`-dotted edge from a vertex to itself makes the value zero -/
theorem lvl1_val_zero_of_xself {ι : Type*} [Fintype ι] [DecidableEq ι] {E' I' : Type} [Fintype I'] [DecidableEq I']
    (T : LGraph E' I') (a : E' ⊕ I') (h : (⟨false, a, a⟩ : DEdge (E' ⊕ I')) ∈ T.dotted) (D : LData ι) (ℓe : E' → ι) :
    T.val D ℓe = 0 := by
  unfold LGraph.val
  refine Finset.sum_eq_zero fun ℓi _ => ?_
  have h0 : DEdge.val (Sum.elim ℓe ℓi) (⟨false, a, a⟩ : DEdge (E' ⊕ I')) = 0 := by simp [DEdge.val]
  have hprod : (T.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨_, h, h0⟩)
  simp [LGraph.term, hprod]

theorem lvl1_xBetween_of_edge (Γ : LGraph E I) (hN : Γ.Normal) (e : SEdge (E ⊕ I)) (he : e ∈ Γ.solid)
    (hne : e.src ≠ e.dst) :
    ∃ d ∈ Γ.dotted, d.eq = false ∧ ((d.x = e.src ∧ d.y = e.dst) ∨ (d.x = e.dst ∧ d.y = e.src)) :=
  (hN.2.1 _ _ hne).2 ⟨e, he, hne, Or.inl ⟨rfl, rfl⟩⟩

/-- **The term `m 1_{x = y₁}` of `(Oe1x)` has value zero on a normal graph** (the `×`-dotted edge between `x` and `y₁`). -/
theorem lvl1_oe1xT1_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I)
    (hv : v ≠ Sum.inr x) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (D : LData ι) (ℓe : E → ι) : (lwSymmOe1xT1 c t m Γ p x v hv).val D ℓe = 0 := by
  have hpne := lvl1_hpne c t p x v hv hx
  obtain ⟨d, hd, hde, hdxy⟩ := lvl1_xBetween_of_edge Γ hN p.1 (lvl1_mem_split_fst _ p hp) hpne
  have hab := lvl1_ends_of_twist c t p.1 (Sum.inr x) v (by rw [hx]; exact ⟨rfl, rfl⟩)
  refine lvl1_val_zero_of_xself _ (oe1xSub x v hv) ?_ D ℓe
  unfold lwSymmOe1xT1 oe1xT1
  rw [lwSymmTwistG_dotted]
  simp only [LGraph.relabel, lvl1_frame_dotted, List.mem_map]
  refine ⟨d, hd, ?_⟩
  have h1 : oe1xPhi x v hv (Sum.inr x) = oe1xSub x v hv := by simp [oe1xPhi]
  have h2 : oe1xPhi x v hv v = oe1xSub x v hv := by simp [oe1xPhi, hv]
  simp only [DEdge.map, hde]
  rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases hab with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    simp_all [h1, h2]

/-- **The term `R1 = m δ_{xy} G_{y'x} f` of `(Oe2x)` has value zero on a normal graph** (the `×`-dotted edge between `x` and `y`). -/
theorem lvl1_oe2xR1_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (y : E ⊕ I)
    (hy : y ≠ Sum.inr x) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (D : LData ι) (ℓe : E → ι) : (lwSymmOe2xR1 c t m Γ p q x y hy).val D ℓe = 0 := by
  have hpne := lvl1_hpne c t p x y hy hp1
  obtain ⟨d, hd, hde, hdxy⟩ := lvl1_xBetween_of_edge Γ hN p.1 (lvl1_mem_split_fst _ p hp) hpne
  have hab := lvl1_ends_of_twist c t p.1 (Sum.inr x) y (by rw [hp1]; exact ⟨rfl, rfl⟩)
  refine lvl1_val_zero_of_xself _ (oe2xRet x y hy) ?_ D ℓe
  unfold lwSymmOe2xR1 oe2xR1
  rw [lwSymmTwistG_dotted]
  simp only [LGraph.relabel, lvl1_frame2_dotted, List.mem_map]
  refine ⟨d, hd, ?_⟩
  have h1 : oe2xPhi x y hy (Sum.inr x) = oe2xRet x y hy := by simp [oe2xPhi]
  have h2 : oe2xPhi x y hy y = oe2xRet x y hy := by simp [oe2xPhi, hy]
  simp only [DEdge.map, hde]
  rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases hab with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    simp_all [h1, h2]

end Zero


section Identity

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ} {m : ℂ} (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

theorem lvl1_sum_flatMap {α β : Type*} (L : List α) (g : α → List β) (F : β → ℂ) :
    ((L.flatMap g).map F).sum = (L.map fun a => ((g a).map F).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem lvl1_comp_val_factor {E E' : Type} {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : PGraph E') (f : E → E')
    (hf : Function.Surjective f) (D : LData ι) (ℓe : E → ι) (ℓ' : E' → ι) (hℓ : ℓe = ℓ' ∘ f) :
    (Q.lvl1Comp f hf).val D ℓe = Q.val D ℓ' := by
  classical
  have h : ∃ ℓ'' : E' → ι, ℓe = ℓ'' ∘ f := ⟨ℓ', hℓ⟩
  rw [PGraph.lvl1Comp_val, dif_pos h]
  have : h.choose = ℓ' := hf.injective_comp_right (h.choose_spec.symm.trans hℓ)
  rw [this]

/-- **The packed outputs carry the expectation of the input**: if the unpacked list `L0` does at every labelling of the external
vertices of the graph, the packed list does at every labelling of the original external vertices. -/
theorem lvl1_pack_identity {E : Type} (P : PGraph E) (L0 : List (PGraph P.E')) (ℓe : E → Idx d (sz.L n) (sz.W n))
    (hid : ∀ ℓ' : P.E' → Idx d (sz.L n) (sz.W n),
      ∫ ω, P.g.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz) =
        (L0.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz)).sum) :
    ∫ ω, P.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ((lvl1Pack P L0).map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  classical
  unfold lvl1Pack
  rw [List.map_map]
  by_cases hf : ∃ ℓ' : P.E' → Idx d (sz.L n) (sz.W n), ℓe = ℓ' ∘ P.ext
  · have hc : ℓe = hf.choose ∘ P.ext := hf.choose_spec
    have h1 : ∀ ω, P.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe =
        P.g.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) hf.choose := fun ω =>
      PGraph.val_of_factor P _ hc
    simp_rw [h1]
    rw [hid hf.choose]
    refine congrArg List.sum (List.map_congr_left fun Q _ => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact (lvl1_comp_val_factor Q P.ext P.ext_surj _ ℓe hf.choose hc).symm
  · have h1 : ∀ ω, P.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe = 0 := fun ω =>
      PGraph.val_of_not P _ hf
    simp_rw [h1]
    simp only [integral_zero]
    symm
    refine List.sum_eq_zero fun a ha => ?_
    obtain ⟨Q, _, rfl⟩ := List.mem_map.1 ha
    simp only [Function.comp_apply]
    have : ∀ ω, (Q.lvl1Comp P.ext P.ext_surj).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe = 0 := fun ω => by
      rw [PGraph.lvl1Comp_val, dif_neg hf]
    simp_rw [this]
    simp

variable (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
  (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp)
  (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)

include hG hz hu hm0 hzm hSp hSpT hM hM0

/-- **The expectation identity of Step 1** for the graph `Γ` at the external labels `ℓ'`. -/
theorem lvl1_weight0_identity {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (Γ : LGraph E' I') (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (hp : p ∈ lwSplit Γ.solid)
    (x : E' ⊕ I') (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (ℓ' : E' → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz) =
      ((lvl1WeightOuts0 m Γ p x c t).map fun Q =>
        ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz)).sum := by
  rw [lwSymm_weight_graph_E hG hz hu hm0 hzm Sp M hSp hSpT hM hM0 Γ p hp x c t hx ℓ']
  unfold lvl1WeightOuts0
  simp only [List.map_append, List.sum_append, lvl1_sum_flatMap]
  have e1 := lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOwxT1 c t m Γ x) ℓ'
  have e2 := lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOwxT2 c t m Γ p x) ℓ'
  have e3 := congrArg List.sum (List.map_congr_left (l := lwSplit p.2)
    (f := fun q => ∫ ω, (lwSymmOwxT3 c t m Γ x q).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz))
    (g := fun q => (((lwSymmOwxT3 c t m Γ x q).partition m).map fun Q =>
      ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz)).sum)
    fun q _ => lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOwxT3 c t m Γ x q) ℓ')
  have e4 := congrArg List.sum (List.map_congr_left (l := lwSplit p.2)
    (f := fun q => ∫ ω, (lwSymmOwxT4 c t m Γ x q).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz))
    (g := fun q => (((lwSymmOwxT4 c t m Γ x q).partition m).map fun Q =>
      ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz)).sum)
    fun q _ => lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOwxT4 c t m Γ x q) ℓ')
  rw [e1, e2, e3, e4]


/-- **The expectation identity of Step 2** for the normal graph `Γ` at the external labels `ℓ'`. -/
theorem lvl1_edge0_identity {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (Γ : LGraph E' I') (hN : Γ.Normal) (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (hp : p ∈ lwSplit Γ.solid)
    (x : I') (v : E' ⊕ I') (hv : v ≠ Sum.inr x) (c t : Bool)
    (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) (ℓ' : E' → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz) =
      ((lvl1EdgeOuts0 m Γ p x v c t).map fun Q =>
        ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz)).sum := by
  have hpne := lvl1_hpne c t p x v hv hx
  have hX := lwSymm_hX_of_normal Γ hN p hp hpne
  rw [lwSymm_oe1x_graph_E hG hz hu hm0 hzm Sp M hSpT hM hM0 Γ p hp x v hv c t hx hX ℓ']
  have hz0 : ∫ ω, (lwSymmOe1xT1 c t m Γ p x v hv).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ'
      ∂(Sizes.seqP sz) = 0 := by
    have : (fun ω => (lwSymmOe1xT1 c t m Γ p x v hv).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') =
        fun _ => 0 := funext fun ω => lvl1_oe1xT1_zero m Γ hN p hp x v hv c t hx _ ℓ'
    rw [this, integral_zero]
  rw [hz0, zero_add]
  unfold lvl1EdgeOuts0
  simp only [List.map_append, List.sum_append, lvl1_sum_flatMap]
  have e1 := lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOe1xOwx c t m Γ p x) ℓ'
  rw [e1]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
  refine congrArg List.sum (List.map_congr_left fun T _ => ?_)
  exact lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM T ℓ'


/-- **The expectation identity of Step 3** for the normal graph `Γ` at the external labels `ℓ'`. -/
theorem lvl1_gg0_identity {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (Γ : LGraph E' I') (hN : Γ.Normal) (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I')))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I') (y y' : E' ⊕ I') (hy : y ≠ Sum.inr x)
    (hy' : y' ≠ Sum.inr x) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (ℓ' : E' → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz) =
      ((lvl1GGOuts0 m Γ p q x y y' c t).map fun Q =>
        ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz)).sum := by
  have hpne := lvl1_hpne c t p x y hy hp1
  have hqne := lvl1_qne c t q x y' hq1 hy'
  have hqΓ : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hX1 := lwSymm_hX_of_normal Γ hN p hp hpne
  have hX2 : q.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = q.1.src ∧ d.y = q.1.dst) ∨ (d.x = q.1.dst ∧ d.y = q.1.src)) := fun _ => by
    obtain ⟨d, hd, hde, hdxy⟩ := lvl1_xBetween_of_edge Γ hN q.1 hqΓ hqne
    exact ⟨d, hd, hde, hdxy⟩
  rw [lwSymm_oe2x_graph_E hG hz hu hm0 hzm Sp M hSp hSpT hM hM0 Γ x y y' hy p hp q hq c t hp1 hq1 hX1 hX2 ℓ']
  have hz0 : ∫ ω, (lwSymmOe2xR1 c t m Γ p q x y hy).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ'
      ∂(Sizes.seqP sz) = 0 := by
    have : (fun ω => (lwSymmOe2xR1 c t m Γ p q x y hy).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') =
        fun _ => 0 := funext fun ω => lvl1_oe2xR1_zero m Γ hN p q hp x y hy c t hp1 _ ℓ'
    rw [this, integral_zero]
  rw [hz0, zero_add]
  unfold lvl1GGOuts0
  simp only [List.map_append, List.sum_append, lvl1_sum_flatMap]
  have e2 := lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOe2xR2 c t m Γ p q x y y') ℓ'
  have e3 := lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOe2xR3 c t m Γ p q x) ℓ'
  have e4 := lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOe2xR4 c t m Γ p q x y y') ℓ'
  have e5 := lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOe2xR5 c t m Γ p q x y y') ℓ'
  have e6 := lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOe2xR6 c t m Γ p q x y y') ℓ'
  have e7 := congrArg List.sum (List.map_congr_left (l := lwSplit q.2)
    (f := fun q' => ∫ ω, (lwSymmOe2xR7 c t m Γ p q x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ'
      ∂(Sizes.seqP sz))
    (g := fun q' => (((lwSymmOe2xR7 c t m Γ p q x y y' q').partition m).map fun Q =>
      ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz)).sum)
    fun q' _ => lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOe2xR7 c t m Γ p q x y y' q') ℓ')
  have e8 := congrArg List.sum (List.map_congr_left (l := lwSplit q.2)
    (f := fun q' => ∫ ω, (lwSymmOe2xR8 c t m Γ p q x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ'
      ∂(Sizes.seqP sz))
    (g := fun q' => (((lwSymmOe2xR8 c t m Γ p q x y y' q').partition m).map fun Q =>
      ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' ∂(Sizes.seqP sz)).sum)
    fun q' _ => lvl1_term_integral (u := u) M (lwS sz n u) Sp hG hz hM (lwSymmOe2xR8 c t m Γ p q x y y' q') ℓ')
  rw [e2, e3, e4, e5, e6, e7, e8]


/-- **The expectation identity of one step** (item 2 of the ticket): under the hypotheses of the three expansion theorems,
`E[Γ] = Σ_{Γ' ∈ outs} E[Γ']` for every `LocStep`, at every labelling `ℓe` of the original external vertices. -/
theorem lvl1_step_identity {E : Type} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs)
    (hN : P.g.Normal) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, P.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  cases hst with
  | weight p hp x c t hx =>
    exact lvl1_pack_identity Sp M P _ ℓe fun ℓ' => lvl1_weight0_identity Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 P.g p hp x c t hx ℓ'
  | edge p hp x v hv c t hx hwf hbad =>
    exact lvl1_pack_identity Sp M P _ ℓe fun ℓ' => lvl1_edge0_identity Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 P.g hN p hp x v hv c t hx ℓ'
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb =>
    have hqne : q.1.src ≠ q.1.dst := hwf q.1 (lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq))
    have hy' : y' ≠ Sum.inr x := by
      intro h
      apply hqne
      rw [← lwSymmTwistS_loop c t q.1, hq1]
      exact h
    exact lvl1_pack_identity Sp M P _ ℓe fun ℓ' => lvl1_gg0_identity Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 P.g hN p q hp hq x y y' hy hy' c t hp1 hq1 ℓ'

end Identity

end RBM.Graph
end
end Lvl1PartV2

/-! ## 12. A step exists at every normal graph that is not locally standard (`lvl1_exists_step`) -/

section Lvl1PartE
open RBM RBM.Gauss RBM.Green RBM.Graph

noncomputable section

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Exists

theorem lvl1_exists_split_fst {κ : Type*} (l : List κ) (a : κ) (h : a ∈ l) : ∃ p ∈ lwSplit l, p.1 = a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨(a, l), by simp [lwSplit], rfl⟩
    · obtain ⟨p, hp, hpa⟩ := ih h
      refine ⟨(p.1, b :: p.2), ?_, hpa⟩
      simp only [lwSplit, List.mem_cons, List.mem_map]
      exact Or.inr ⟨p, hp, rfl⟩

theorem lvl1_split_two {κ : Type*} (l : List κ) (f : κ → Bool) (a b : κ) (h : l.filter f = [a, b]) :
    ∃ p ∈ lwSplit l, p.1 = a ∧ ∃ q ∈ lwSplit p.2, q.1 = b := by
  have ha : a ∈ l := (List.mem_filter.1 (by rw [h]; simp)).1
  have hfa : f a = true := (List.mem_filter.1 (by rw [h]; simp : a ∈ l.filter f)).2
  obtain ⟨p, hp, hpa⟩ := lvl1_exists_split_fst l a ha
  refine ⟨p, hp, hpa, ?_⟩
  have hperm := (lwSplit_perm l p hp).filter f
  rw [h, List.filter_cons_of_pos (by rw [hpa]; exact hfa), hpa] at hperm
  have h2 : [b].Perm (p.2.filter f) := List.Perm.cons_inv hperm
  have hb : b ∈ p.2 := (List.mem_filter.1 (h2.mem_iff.1 (by simp))).1
  exact lvl1_exists_split_fst p.2 b hb


variable {E : Type}

/-- **Step selection**: a normal packed graph that is not locally standard admits a step of the strategy (a weight; else a vertex of degree
`∉ {0, 2}` or non-neutral charge; else a vertex with two solid edges of the same charge). -/
theorem lvl1_exists_step (m : ℂ) (P : PGraph E) (hN : P.g.Normal) (hn : ¬ P.g.LocStd) : ∃ outs, LocStep m P outs := by
  classical
  by_cases hA : ∀ e ∈ P.g.solid, e.src ≠ e.dst
  · by_cases hbad : ∃ j : P.I', P.g.lvl1DegAt (Sum.inr j) ≠ 0 ∧ (P.g.lvl1DegAt (Sum.inr j) ≠ 2 ∨ P.g.lvl1ChargeAt (Sum.inr j) ≠ 0)
    · obtain ⟨j, hj0, hj⟩ := hbad
      have hlen : 0 < (P.g.lvl1SolidAt (Sum.inr j)).length := Nat.pos_of_ne_zero hj0
      obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hlen
      have heS : e ∈ P.g.solid := (List.mem_filter.1 he).1
      have heI : e.lvl1IncAt (Sum.inr j) = true := (List.mem_filter.1 he).2
      rw [lvl1_incAt_iff] at heI
      obtain ⟨hne, hat⟩ := heI
      obtain ⟨c, t, v, hv, hcv⟩ := lwSymm_selector_edge e (Sum.inr j) (by
        rcases hat with h | h
        · exact Or.inl ⟨h, fun h' => hne (h.trans h'.symm)⟩
        · exact Or.inr ⟨h, fun h' => hne (h'.trans h.symm)⟩)
      obtain ⟨p, hp, hpe⟩ := lvl1_exists_split_fst P.g.solid e heS
      exact ⟨_, LocStep.edge P p hp j v hv c t (by rw [hpe]; exact hcv) hA ⟨hj0, hj⟩⟩
    · push Not at hbad
      have hex : ∃ i : P.I', ¬ (P.g.StdNeutral (Sum.inr i) ∨ P.g.lvl1DegAt (Sum.inr i) = 0) := by
        by_contra hcon
        push Not at hcon
        exact hn ⟨hN, hA, fun i => hcon i⟩
      obtain ⟨i, hi⟩ := hex
      push Not at hi
      obtain ⟨hiSN, hi0⟩ := hi
      obtain ⟨hi2, hich⟩ := hbad i hi0
      have hlen : (P.g.lvl1SolidAt (Sum.inr i)).length = 2 := hi2
      obtain ⟨e1, e2, hE⟩ := List.length_eq_two.1 hlen
      have hmem1 : e1 ∈ P.g.lvl1SolidAt (Sum.inr i) := by rw [hE]; simp
      have hmem2 : e2 ∈ P.g.lvl1SolidAt (Sum.inr i) := by rw [hE]; simp
      have hI1 : e1.lvl1IncAt (Sum.inr i) = true := (List.mem_filter.1 hmem1).2
      have hI2 : e2.lvl1IncAt (Sum.inr i) = true := (List.mem_filter.1 hmem2).2
      obtain ⟨p, hp, hp1, q, hq, hq1⟩ := lvl1_split_two P.g.solid (fun e => e.lvl1IncAt (Sum.inr i)) e1 e2 hE
      -- the two edges have the same colour
      have hσ : e1.σ = e2.σ := by
        by_contra hne
        apply hiSN
        refine ⟨?_, hich⟩
        unfold LGraph.StdNeutral at *
        rw [hE]
        cases h1 : e1.σ <;> cases h2 : e2.σ <;> simp_all
      have hchg : e1.lvl1ChargeAt (Sum.inr i) + e2.lvl1ChargeAt (Sum.inr i) = 0 := by
        have := hich
        unfold LGraph.lvl1ChargeAt at this
        rw [hE] at this
        simpa using this
      rw [lvl1_incAt_iff] at hI1 hI2
      obtain ⟨hne1, hat1⟩ := hI1
      obtain ⟨hne2, hat2⟩ := hI2
      have hsel : (e1.src = Sum.inr i ∧ e1.dst ≠ Sum.inr i ∧ e2.dst = Sum.inr i) ∨
          (e1.dst = Sum.inr i ∧ e1.src ≠ Sum.inr i ∧ e2.src = Sum.inr i) := by
        unfold SEdge.lvl1ChargeAt at hchg
        by_cases hs1 : e1.src = Sum.inr i <;> by_cases hs2 : e2.src = Sum.inr i
        · exfalso
          simp only [hs1, hs2, if_true, hσ] at hchg
          by_cases hb : e2.σ = true <;> simp [hb] at hchg
        · refine Or.inl ⟨hs1, fun h => hne1 (hs1.trans h.symm), ?_⟩
          rcases hat2 with h | h
          · exact absurd h hs2
          · exact h
        · refine Or.inr ⟨?_, hs1, hs2⟩
          rcases hat1 with h | h
          · exact absurd h hs1
          · exact h
        · exfalso
          simp only [hs1, hs2, if_false, hσ] at hchg
          by_cases hb : e2.σ = true <;> simp [hb] at hchg
      obtain ⟨c, t, y, y', hy, hcp, hcq⟩ := lwSymm_selector_pair p.1 q.1 (Sum.inr i) (by rw [hp1, hq1]; exact hσ.symm)
        (by rw [hp1, hq1]; exact hsel)
      exact ⟨_, LocStep.gg P p q hp hq i y y' hy c t hcp hcq hA (fun j => by
        by_cases hj : P.g.lvl1DegAt (Sum.inr j) = 0
        · exact Or.inl hj
        · exact Or.inr (hbad j hj))⟩
  · push Not at hA
    obtain ⟨e, he, hl⟩ := hA
    obtain ⟨p, hp, hpe⟩ := lvl1_exists_split_fst P.g.solid e he
    have hc : e.circ = true := hN.2.2 e he hl
    exact ⟨_, LocStep.weight P p hp e.src (!e.σ) false (by rw [hpe]; exact lwSymm_twist_weight e e.src rfl hl.symm hc)⟩

end Exists
end RBM.Graph
end
end Lvl1PartE

/-! ## 13. Induction principle, termination measure, existence of the lists (`lvl1_induction`, `lvl1_exists_aux`) -/

section Lvl1PartM
open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green RBM.Graph

noncomputable section

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Induction

variable {E : Type}

theorem Lvl1Reach.trans {m : ℂ} {K : ℤ} {P Q R : PGraph E} (h1 : Lvl1Reach m K P Q) (h2 : Lvl1Reach m K Q R) :
    Lvl1Reach m K P R := by
  induction h2 with
  | refl => exact h1
  | step Q1 R1 L _ hlt hn hst hmem ih => exact Lvl1Reach.step P Q1 R1 L ih hlt hn hst hmem

/-- **The induction principle of the strategy** (item 4): a predicate that holds at `P` and passes from the input of every `LocStep` to each of
its outputs holds at every graph reached from `P`, in particular at every graph of the lists `outs` and `errs` of `lvl1_lemma`. -/
theorem lvl1_induction {m : ℂ} {K : ℤ} {P Q : PGraph E} (h : Lvl1Reach m K P Q) (Pred : PGraph E → Prop) (h0 : Pred P)
    (hstep : ∀ (A : PGraph E) (L : List (PGraph E)), LocStep m A L → Pred A → ∀ B ∈ L, Pred B) : Pred Q := by
  induction h with
  | refl => exact h0
  | step Q1 R1 L _ _ _ hst hmem ih => exact hstep Q1 L hst ih R1 hmem

end Induction


section Measure

variable {E : Type}

/-- **The termination measure of the `lvl1 lemma`**: the order deficit `(K - ord)⁺`, the number of self-loops, the number of solid edges, and the
number of pairs of solid edges with a common internal end, compared lexicographically. -/
def Lvl1Mu (K : ℤ) (P : PGraph E) : ℕ × ℕ × ℕ × ℕ :=
  ((K - ord P.g.counters).toNat, P.g.lvl1NLoops, P.g.nS, P.g.lvl1NPairs)

/-- the lexicographic order on the measure -/
def Lvl1Lt (a b : ℕ × ℕ × ℕ × ℕ) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))) a b

theorem lvl1Lt_wf : WellFounded Lvl1Lt :=
  (wellFounded_lt (α := ℕ)).prod_lex ((wellFounded_lt (α := ℕ)).prod_lex
    ((wellFounded_lt (α := ℕ)).prod_lex (wellFounded_lt (α := ℕ))))

/-- **The measure falls along a good step** (below the cutoff). -/
theorem lvl1_mu_lt {K : ℤ} {Γ Q : PGraph E} (hK : ord Γ.g.counters < K) (hg : Lvl1Good Γ.g Q.g) :
    Lvl1Lt (Lvl1Mu K Q) (Lvl1Mu K Γ) := by
  obtain ⟨-, -, -, h⟩ := hg
  unfold Lvl1Lt Lvl1Mu
  simp only [Prod.lex_def]
  rcases h with h | ⟨h1, h2⟩
  · left; omega
  · right
    refine ⟨by rw [h1], ?_⟩
    rcases h2 with h2 | ⟨h2, h3⟩
    · left; exact h2
    · right
      refine ⟨h2, ?_⟩
      rcases h3 with h3 | ⟨h3, h4⟩
      · left; exact h3
      · right; exact ⟨h3, h4⟩

end Measure

section Combine

theorem lvl1_choose_list {α β : Type*} (Spec : α → List β → List β → Prop) (L : List α)
    (h : ∀ a ∈ L, ∃ o e, Spec a o e) : ∃ fo fe : α → List β, ∀ a ∈ L, Spec a (fo a) (fe a) := by
  classical
  refine ⟨fun a => if h' : ∃ o e, Spec a o e then h'.choose else [],
    fun a => if h' : ∃ o e, Spec a o e then h'.choose_spec.choose else [], fun a ha => ?_⟩
  have h' : ∃ o e, Spec a o e := h a ha
  simp only [dif_pos h']
  exact h'.choose_spec.choose_spec

end Combine

section Exists

variable {E : Type}

/-- **The expectation identity `E[Γ] = Σ outs + Σ errs`** at all admissible data and external labels (the hypotheses of the three expansion
theorems, plus `M a b = 0` and `S⁺ᵀ = S⁺`). -/
def Lvl1Ident (m : ℂ) (Γ : PGraph E) (outs errs : List (PGraph E)) : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ} (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
    (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
    (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : E → Idx d (sz.L n) (sz.W n),
      ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum

theorem lvl1_exists_aux (m : ℂ) (K : ℤ) (Γ : PGraph E) (hN : Γ.g.Normal) :
    ∃ outs errs : List (PGraph E), (∀ Q ∈ outs, Q.g.LocStd ∧ ord Q.g.counters < K) ∧
      (∀ Q ∈ errs, K ≤ ord Q.g.counters) ∧ (∀ Q ∈ outs ++ errs, Lvl1Reach m K Γ Q) ∧ Lvl1Ident m Γ outs errs := by
  classical
  induction Γ using (InvImage.wf (Lvl1Mu K) lvl1Lt_wf).induction with
  | _ Γ ih =>
    by_cases hK : K ≤ ord Γ.g.counters
    · refine ⟨[], [Γ], by simp, by simpa using hK, by simpa using Lvl1Reach.refl Γ, ?_⟩
      intro d sz n z u Sp M _ _ _ _ _ _ _ _ _ ℓe
      simp
    by_cases hL : Γ.g.LocStd
    · refine ⟨[Γ], [], by simpa using ⟨hL, by omega⟩, by simp, by simpa using Lvl1Reach.refl Γ, ?_⟩
      intro d sz n z u Sp M _ _ _ _ _ _ _ _ _ ℓe
      simp
    -- a step
    obtain ⟨L, hst⟩ := lvl1_exists_step m Γ hN hL
    have hgood := lvl1_step_good hst hN
    have hlt : ord Γ.g.counters < K := by omega
    obtain ⟨fo, fe, hfo⟩ := lvl1_choose_list
      (fun (Q : PGraph E) (o e : List (PGraph E)) => (∀ Q' ∈ o, Q'.g.LocStd ∧ ord Q'.g.counters < K) ∧
        (∀ Q' ∈ e, K ≤ ord Q'.g.counters) ∧ (∀ Q' ∈ o ++ e, Lvl1Reach m K Q Q') ∧ Lvl1Ident m Q o e) L
      (fun Q hQ => ih Q (lvl1_mu_lt hlt (hgood Q hQ).2) (hgood Q hQ).1)
    have hreach : ∀ Q ∈ L, Lvl1Reach m K Γ Q := fun Q hQ =>
      Lvl1Reach.step Γ Γ Q L (Lvl1Reach.refl Γ) hlt hL hst hQ
    refine ⟨L.flatMap fo, L.flatMap fe, ?_, ?_, ?_, ?_⟩
    · intro Q' hQ'
      obtain ⟨Q, hQ, hQ'⟩ := List.mem_flatMap.1 hQ'
      exact (hfo Q hQ).1 Q' hQ'
    · intro Q' hQ'
      obtain ⟨Q, hQ, hQ'⟩ := List.mem_flatMap.1 hQ'
      exact (hfo Q hQ).2.1 Q' hQ'
    · intro Q' hQ'
      rcases List.mem_append.1 hQ' with h | h
      · obtain ⟨Q, hQ, h⟩ := List.mem_flatMap.1 h
        exact (hreach Q hQ).trans ((hfo Q hQ).2.2.1 Q' (List.mem_append_left _ h))
      · obtain ⟨Q, hQ, h⟩ := List.mem_flatMap.1 h
        exact (hreach Q hQ).trans ((hfo Q hQ).2.2.1 Q' (List.mem_append_right _ h))
    · intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 ℓe
      rw [lvl1_step_identity Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 hst hN ℓe,
        lvl1_sum_flatMap, lvl1_sum_flatMap, ← List.sum_map_add]
      refine congrArg List.sum (List.map_congr_left fun Q hQ => ?_)
      exact (hfo Q hQ).2.2.2 Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 ℓe

end Exists

end RBM.Graph
end
end Lvl1PartM

/-! ## 14. The `lvl1 lemma` (`lvl1_lemma`) -/

section Lvl1PartF
open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green RBM.Graph

noncomputable section

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Final

variable {E : Type}

/-- **The `lvl1 lemma`** (`7_8:392-399`, [yang2021] Lemma 3.22, proved here by `strat_local`): every normal packed graph `Γ` and every cutoff `K` give finite lists
`outs`, `errs` of packed graphs, independent of the sample data and of `n`, with: every graph of `outs` is locally standard of scaling order
`≥ ord Γ` and `< K`; every graph of `errs` has order `≥ K` (cutoff (a)); all are reached from
`Γ` by `LocStep` (so `lvl1_induction` applies to them), normal, and have `n_M ≤ n_M(Γ)`, `n_V - n_W ≤ n_V(Γ) - n_W(Γ)`; and
`E[Γ] = Σ_{outs} E[·] + Σ_{errs} E[·]` at all admissible data. -/
theorem lvl1_lemma (m : ℂ) (K : ℤ) (Γ : PGraph E) (hN : Γ.g.Normal) :
    ∃ outs errs : List (PGraph E),
      (∀ Q ∈ outs, Q.g.LocStd ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧
      (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ outs ++ errs, Lvl1Reach m K Γ Q ∧ Q.g.Normal ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧
        Q.g.nM ≤ Γ.g.nM ∧ (Q.g.nV : ℤ) - Q.g.nW ≤ (Γ.g.nV : ℤ) - Γ.g.nW) ∧
      ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
        (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
        (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
        (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : E → Idx d (sz.L n) (sz.W n),
          ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
            (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
            (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  obtain ⟨outs, errs, hout, herr, hreach, hid⟩ := lvl1_exists_aux m K Γ hN
  have hinv : ∀ Q ∈ outs ++ errs, Q.g.Normal ∧ ord Γ.g.counters ≤ ord Q.g.counters ∧ Q.g.nM ≤ Γ.g.nM ∧
      (Q.g.nV : ℤ) - Q.g.nW ≤ (Γ.g.nV : ℤ) - Γ.g.nW := by
    intro Q hQ
    refine lvl1_induction (hreach Q hQ) (fun Q => Q.g.Normal ∧ ord Γ.g.counters ≤ ord Q.g.counters ∧
        Q.g.nM ≤ Γ.g.nM ∧ (Q.g.nV : ℤ) - Q.g.nW ≤ (Γ.g.nV : ℤ) - Γ.g.nW)
      ⟨hN, le_refl _, le_refl _, le_refl _⟩ ?_
    intro A L hst hA B hB
    obtain ⟨hBN, hg⟩ := lvl1_step_good hst hA.1 B hB
    obtain ⟨h1, h2, h3, -⟩ := hg
    exact ⟨hBN, le_trans hA.2.1 h1, le_trans h2 hA.2.2.1, by have := hA.2.2.2; omega⟩
  refine ⟨outs, errs, fun Q hQ => ⟨(hout Q hQ).1, (hinv Q (List.mem_append_left _ hQ)).2.1, (hout Q hQ).2⟩,
    fun Q hQ => herr Q hQ, fun Q hQ => ⟨hreach Q hQ, hinv Q hQ⟩, ?_⟩
  intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 ℓe
  exact hid Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 ℓe

/-- **The induction principle for the lists of the `lvl1 lemma`** (ticket item 4, for `LW-10`): the lists of `lvl1_lemma` can be taken so
that every predicate `Pred` that holds at `Γ` and passes from the input of every `LocStep` to each of its outputs holds at every graph of
`outs` and of `errs` (the same lists, chosen before `Pred`); no unfolding of the proof of `lvl1_lemma` is needed. -/
theorem lvl1_lemma_induction (m : ℂ) (K : ℤ) (Γ : PGraph E) (hN : Γ.g.Normal) :
    ∃ outs errs : List (PGraph E),
      (∀ Q ∈ outs, Q.g.LocStd ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧
      (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
      (∀ Pred : PGraph E → Prop, Pred Γ →
        (∀ (A : PGraph E) (L : List (PGraph E)), LocStep m A L → Pred A → ∀ B ∈ L, Pred B) →
        ∀ Q ∈ outs ++ errs, Pred Q) ∧
      ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
        (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
        (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
        (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : E → Idx d (sz.L n) (sz.W n),
          ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
            (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
            (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  obtain ⟨outs, errs, h1, h2, h3, h4⟩ := lvl1_lemma m K Γ hN
  exact ⟨outs, errs, h1, h2, fun Pred h0 hstep Q hQ => lvl1_induction (h3 Q hQ).1 Pred h0 hstep, h4⟩

end Final

end RBM.Graph
end
end Lvl1PartF

/-! ## 15. The cutoff (a) `ord ≥ K`, its size corollary, the `lvl1 lemma` in the paper's form -/

section Lvl1PartX
open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green RBM.Graph

noncomputable section

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Size

/-- **The order cutoff of the `lvl1 lemma`** (cutoff (a), `(eq:smallsize)`, `B:140`): for the constants `c` (`Ψ ≤ W^{-c}`), `K0`
(`L^d ≤ W^{K0}`), the dimension `d`, the error exponent `D` and the counters `G` of the input graph, the smallest `K` with
`c K ≥ D + K0 n_M(G) + d (n_V(G) - n_W(G))⁺`. -/
def lvl1Cutoff (c : ℝ) (K0 d : ℕ) (D : ℝ) (G : Counters) : ℕ :=
  ⌈(D + (K0 : ℝ) * G.nM + (d : ℝ) * (((G.nV : ℤ) - G.nW).toNat : ℝ)) / c⌉₊

/-- **A graph above the order cutoff has size `≤ W^{-D}`** (the corollary of cutoff (a), `7_8:274-277`): in the regime
`W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`, a graph whose counters `Q` satisfy `ord Q ≥ K`, `n_M(Q) ≤ n_M(G)` and
`n_V(Q) - n_W(Q) ≤ n_V(G) - n_W(G)` (as every graph reached from `G` by a local expansion: local expansions create no
molecule, `7_8:351`) has `size(Q) ≤ W^{-D}`.  The constant is `1`; the bound is
`(L^d)^{n_M(G)} Ψ^K (W^d Ψ²)^{(n_V(G) - n_W(G))⁺} ≤ W^{K0 n_M(G) - cK + d (n_V(G) - n_W(G))⁺}`. -/
theorem lvl1_size_le (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (G : Counters) (W L : ℕ) (Ψ : ℝ)
    (hW : 1 ≤ W) (hL : 1 ≤ L) (hLW : (L : ℝ) ^ d ≤ (W : ℝ) ^ K0)
    (hlow : (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) (hup : Ψ ≤ (W : ℝ) ^ (-c))
    (Q : Counters) (hK : (lvl1Cutoff c K0 d D G : ℤ) ≤ ord Q) (hM : Q.nM ≤ G.nM)
    (hV : (Q.nV : ℤ) - Q.nW ≤ (G.nV : ℤ) - G.nW) :
    Q.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D) := by
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hx0 : (0 : ℝ) < W := by linarith
  have hΨ0 : 0 < Ψ := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hlow
  have hΨ1 : Ψ ≤ 1 := hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith))
  have hWΨ : 1 ≤ (W : ℝ) ^ d * Ψ ^ 2 := (one_le_pow_mul_sq_iff W d hx0 hΨ0.le).1 hlow
  rw [Q.scalingSize_eq W d L hΨ0.ne']
  set δ : ℕ := ((G.nV : ℤ) - G.nW).toNat with hδ
  set K : ℕ := lvl1Cutoff c K0 d D G with hKdef
  have h1 : ((L : ℝ) ^ d) ^ Q.nM ≤ (W : ℝ) ^ ((K0 * G.nM : ℕ) : ℝ) := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
    calc ((L : ℝ) ^ d) ^ Q.nM ≤ ((L : ℝ) ^ d) ^ G.nM := pow_le_pow_right₀ hL1 hM
      _ ≤ ((W : ℝ) ^ K0) ^ G.nM := pow_le_pow_left₀ (by positivity) hLW _
      _ = (W : ℝ) ^ ((K0 * G.nM : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_mul]
  have h2 : Ψ ^ (ord Q) ≤ (W : ℝ) ^ (-c * K) := by
    calc Ψ ^ (ord Q) ≤ Ψ ^ (K : ℤ) := zpow_le_zpow_right_of_le_one₀ hΨ0 hΨ1 hK
      _ = Ψ ^ K := zpow_natCast Ψ K
      _ ≤ ((W : ℝ) ^ (-c)) ^ K := pow_le_pow_left₀ hΨ0.le hup K
      _ = (W : ℝ) ^ (-c * K) := by rw [Real.rpow_mul hx0.le, Real.rpow_natCast]
  have h3 : ((W : ℝ) ^ d * Ψ ^ 2) ^ ((Q.nV : ℤ) - Q.nW) ≤ (W : ℝ) ^ ((d * δ : ℕ) : ℝ) := by
    calc ((W : ℝ) ^ d * Ψ ^ 2) ^ ((Q.nV : ℤ) - Q.nW) ≤ ((W : ℝ) ^ d * Ψ ^ 2) ^ (δ : ℤ) :=
          zpow_le_zpow_right₀ hWΨ (hV.trans (Int.self_le_toNat _))
      _ = ((W : ℝ) ^ d * Ψ ^ 2) ^ δ := zpow_natCast _ _
      _ ≤ ((W : ℝ) ^ d) ^ δ :=
          pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hΨ1)) _
      _ = (W : ℝ) ^ ((d * δ : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_mul]
  have hnn1 : 0 ≤ ((L : ℝ) ^ d) ^ Q.nM := by positivity
  have hnn2 : 0 ≤ Ψ ^ (ord Q) := zpow_nonneg hΨ0.le _
  have hnn3 : 0 ≤ ((W : ℝ) ^ d * Ψ ^ 2) ^ ((Q.nV : ℤ) - Q.nW) := zpow_nonneg (by positivity) _
  have hprod : ((L : ℝ) ^ d) ^ Q.nM * Ψ ^ (ord Q) * ((W : ℝ) ^ d * Ψ ^ 2) ^ ((Q.nV : ℤ) - Q.nW) ≤
      (W : ℝ) ^ ((K0 * G.nM : ℕ) : ℝ) * (W : ℝ) ^ (-c * K) * (W : ℝ) ^ ((d * δ : ℕ) : ℝ) :=
    mul_le_mul (mul_le_mul h1 h2 hnn2 (by positivity)) h3 hnn3 (by positivity)
  refine hprod.trans ?_
  rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
  refine Real.rpow_le_rpow_of_exponent_le hx ?_
  have hcK : D + (K0 : ℝ) * G.nM + (d : ℝ) * δ ≤ c * K := by
    have h := (div_le_iff₀ hc).1 (Nat.le_ceil ((D + (K0 : ℝ) * G.nM + (d : ℝ) * δ) / c))
    have h' : (⌈(D + (K0 : ℝ) * G.nM + (d : ℝ) * δ) / c⌉₊ : ℝ) = K := rfl
    rw [h'] at h
    linarith
  push_cast
  linarith

end Size

section LemmaSize

variable {E : Type}

/-- **The `lvl1 lemma` in the paper's form** (`7_8:392-399`, [yang2021] Lemma 3.22, proved here by `strat_local` with the order cutoff
`K = lvl1Cutoff c K0 d D Γ.counters`): for every `D`, the normal packed graph `Γ` is `E`-equal to a sum of locally standard graphs of
order `≥ ord Γ` and a sum of graphs of scaling size `≤ W^{-D}` (in the regime `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`, for all
`W, L, Ψ`; the lists do not depend on them nor on the sample data), at all admissible data of dimension `d`. -/
theorem lvl1_lemma_size (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (Γ : PGraph E) (hN : Γ.g.Normal) :
    ∃ outs errs : List (PGraph E),
      (∀ Q ∈ outs, Q.g.LocStd ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
        (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
      (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D Γ.g.counters : ℤ) Γ Q ∧ Q.g.Normal ∧
        Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ Γ.g.nM ∧ (Q.g.nV : ℤ) - Q.g.nW ≤ (Γ.g.nV : ℤ) - Γ.g.nW) ∧
      ∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
        (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
        (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
        (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : E → Idx d (sz.L n) (sz.W n),
          ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
            (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
            (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  obtain ⟨outs, errs, hout, herr, hall, hid⟩ := lvl1_lemma m (lvl1Cutoff c K0 d D Γ.g.counters : ℤ) Γ hN
  refine ⟨outs, errs, fun Q hQ => ⟨(hout Q hQ).1, (hout Q hQ).2.1⟩, ?_, hall, ?_⟩
  · intro Q hQ W L Ψ hW hL hLW hlow hup
    obtain ⟨-, -, -, hM, hV⟩ := hall Q (List.mem_append_right _ hQ)
    exact lvl1_size_le c hc K0 d D Γ.g.counters W L Ψ hW hL hLW hlow hup Q.g.counters (herr Q hQ) hM hV
  · intro sz n z u
    exact hid

end LemmaSize

end RBM.Graph
end
end Lvl1PartX

/-! ## 16. Compiled instances (`lvl1_inst_*`) -/

section Lvl1PartY
open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green RBM.Graph

noncomputable section

namespace RBM.Graph
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section ExamplesLocStd

/-- A locally standard graph (`deflvl1`): externals `a₀ = inl 0`, `a₁ = inl 1`; internal `α₀, α₁, α₂ = inr 0, inr 1, inr 2`.
`α₀` is standard neutral with two incoming edges `G_{a₀ α₀} Ḡ_{a₁ α₀}`, `α₁` is standard neutral with two outgoing edges
`G_{α₁ a₀} Ḡ_{α₁ a₁}`, `α₂` carries no solid edge (only the waved edge `S_{α₁ α₂}`); one `×`-dotted edge for each solid edge. -/
def lvl1ExStd : LGraph (Fin 2) (Fin 3) where
  solid := [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨false, false, Sum.inl 1, Sum.inr 0⟩,
    ⟨true, false, Sum.inr 1, Sum.inl 0⟩, ⟨false, false, Sum.inr 1, Sum.inl 1⟩]
  waved := [⟨false, true, Sum.inr 1, Sum.inr 2⟩]
  dotted := [⟨false, Sum.inl 0, Sum.inr 0⟩, ⟨false, Sum.inl 1, Sum.inr 0⟩, ⟨false, Sum.inr 1, Sum.inl 0⟩,
    ⟨false, Sum.inr 1, Sum.inl 1⟩]
  coeff := 1

/-- clause (i) fails: the same solid edges without the `×`-dotted edges (not normal) -/
def lvl1ExNotNormal : LGraph (Fin 2) (Fin 3) := { lvl1ExStd with dotted := [] }

/-- clause (ii) fails: a light-weight `(G - M)_{α₂ α₂}` at the otherwise isolated vertex `α₂` (normal, every vertex of clause (iii) fine) -/
def lvl1ExLoop : LGraph (Fin 2) (Fin 3) :=
  { lvl1ExStd with solid := lvl1ExStd.solid ++ [⟨true, true, Sum.inr 2, Sum.inr 2⟩] }

/-- clause (ii) fails at an external vertex: a light-weight `(Ḡ - M̄)_{a₀ a₀}` -/
def lvl1ExLoopExt : LGraph (Fin 2) (Fin 3) :=
  { lvl1ExStd with solid := lvl1ExStd.solid ++ [⟨false, true, Sum.inl 0, Sum.inl 0⟩] }

/-- clause (iii) fails: `α₀` has degree `1` -/
def lvl1ExDeg1 : LGraph (Fin 2) (Fin 3) where
  solid := [⟨true, false, Sum.inl 0, Sum.inr 0⟩]
  waved := []
  dotted := [⟨false, Sum.inl 0, Sum.inr 0⟩]
  coeff := 1

/-- clause (iii) fails: `α₀` has degree `3` -/
def lvl1ExDeg3 : LGraph (Fin 2) (Fin 3) where
  solid := [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨false, false, Sum.inl 1, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inr 1⟩]
  waved := []
  dotted := [⟨false, Sum.inl 0, Sum.inr 0⟩, ⟨false, Sum.inl 1, Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inr 1⟩]
  coeff := 1

/-- clause (iii) fails: `α₀` has two edges of one colour, `G_{a₀ α₀} G_{α₀ a₁}` (neutral charge, not standard neutral) -/
def lvl1ExSame : LGraph (Fin 2) (Fin 3) where
  solid := [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩]
  waved := []
  dotted := [⟨false, Sum.inl 0, Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inl 1⟩]
  coeff := 1

/-- clause (iii) fails: `α₀` has two edges of opposite colours with charge `2`, `G_{a₀ α₀} Ḡ_{α₀ a₁}` -/
def lvl1ExCharge : LGraph (Fin 2) (Fin 3) where
  solid := [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨false, false, Sum.inr 0, Sum.inl 1⟩]
  waved := []
  dotted := [⟨false, Sum.inl 0, Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inl 1⟩]
  coeff := 1

/-- the three clauses of `deflvl1` on a record, as one proposition -/
theorem lvl1_locStd_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) :
    Γ.LocStd ↔ Γ.Normal ∧ (∀ e ∈ Γ.solid, e.src ≠ e.dst) ∧
      ∀ i : I, Γ.StdNeutral (Sum.inr i) ∨ Γ.lvl1DegAt (Sum.inr i) = 0 := Iff.rfl

/-- **`deflvl1` on concrete records** (compiled instance of the target `LGraph.LocStd`, `by decide`): the graph `lvl1ExStd` satisfies the
three clauses (normal, no self-loop, every internal vertex standard neutral or without solid edge), also as a packed graph. -/
theorem lvl1_inst_locStd : lvl1ExStd.LocStd := by decide

theorem lvl1_inst_locStd_pack : lvl1ExStd.pack.LocStd := by decide

/-- degrees and charges of the three internal vertices of `lvl1ExStd` -/
theorem lvl1_inst_std_counts :
    (lvl1ExStd.lvl1DegAt (Sum.inr 0), lvl1ExStd.lvl1ChargeAt (Sum.inr 0), lvl1ExStd.lvl1DegAt (Sum.inr 1),
      lvl1ExStd.lvl1ChargeAt (Sum.inr 1), lvl1ExStd.lvl1DegAt (Sum.inr 2)) = (2, 0, 2, 0, 0) := by decide

/-- clause (i) fails alone -/
theorem lvl1_inst_fail_normal : ¬ lvl1ExNotNormal.Normal ∧ (∀ e ∈ lvl1ExNotNormal.solid, e.src ≠ e.dst) ∧
    ∀ i : Fin 3, lvl1ExNotNormal.StdNeutral (Sum.inr i) ∨ lvl1ExNotNormal.lvl1DegAt (Sum.inr i) = 0 := by decide

/-- clause (ii) fails alone (a light-weight at an internal vertex) -/
theorem lvl1_inst_fail_loop : lvl1ExLoop.Normal ∧ ¬ (∀ e ∈ lvl1ExLoop.solid, e.src ≠ e.dst) ∧
    ∀ i : Fin 3, lvl1ExLoop.StdNeutral (Sum.inr i) ∨ lvl1ExLoop.lvl1DegAt (Sum.inr i) = 0 := by decide

/-- clause (ii) fails alone (a light-weight at an external vertex) -/
theorem lvl1_inst_fail_loopExt : lvl1ExLoopExt.Normal ∧ ¬ (∀ e ∈ lvl1ExLoopExt.solid, e.src ≠ e.dst) ∧
    ∀ i : Fin 3, lvl1ExLoopExt.StdNeutral (Sum.inr i) ∨ lvl1ExLoopExt.lvl1DegAt (Sum.inr i) = 0 := by decide

/-- clause (iii) fails alone (degree `1`) -/
theorem lvl1_inst_fail_deg1 : lvl1ExDeg1.Normal ∧ (∀ e ∈ lvl1ExDeg1.solid, e.src ≠ e.dst) ∧
    ¬ ∀ i : Fin 3, lvl1ExDeg1.StdNeutral (Sum.inr i) ∨ lvl1ExDeg1.lvl1DegAt (Sum.inr i) = 0 := by decide

/-- clause (iii) fails alone (degree `3`) -/
theorem lvl1_inst_fail_deg3 : lvl1ExDeg3.Normal ∧ (∀ e ∈ lvl1ExDeg3.solid, e.src ≠ e.dst) ∧
    ¬ ∀ i : Fin 3, lvl1ExDeg3.StdNeutral (Sum.inr i) ∨ lvl1ExDeg3.lvl1DegAt (Sum.inr i) = 0 := by decide

/-- clause (iii) fails alone (two edges of one colour: degree `2`, charge `0`, not standard neutral) -/
theorem lvl1_inst_fail_same : lvl1ExSame.Normal ∧ (∀ e ∈ lvl1ExSame.solid, e.src ≠ e.dst) ∧
    lvl1ExSame.lvl1DegAt (Sum.inr 0) = 2 ∧ lvl1ExSame.lvl1ChargeAt (Sum.inr 0) = 0 ∧ ¬ lvl1ExSame.StdNeutral (Sum.inr 0) := by decide

/-- clause (iii) fails alone (two edges of opposite colours with charge `2`) -/
theorem lvl1_inst_fail_charge : lvl1ExCharge.Normal ∧ (∀ e ∈ lvl1ExCharge.solid, e.src ≠ e.dst) ∧
    lvl1ExCharge.lvl1DegAt (Sum.inr 0) = 2 ∧ lvl1ExCharge.lvl1ChargeAt (Sum.inr 0) = 2 ∧
    ¬ lvl1ExCharge.StdNeutral (Sum.inr 0) := by decide

/-- none of the seven failing records is locally standard -/
theorem lvl1_inst_not_locStd : ¬ lvl1ExNotNormal.LocStd ∧ ¬ lvl1ExLoop.LocStd ∧ ¬ lvl1ExLoopExt.LocStd ∧
    ¬ lvl1ExDeg1.LocStd ∧ ¬ lvl1ExDeg3.LocStd ∧ ¬ lvl1ExSame.LocStd ∧ ¬ lvl1ExCharge.LocStd := by decide

end ExamplesLocStd

section ExamplesStep

open RBM.Gauss.SizesInst

/-- the selected light-weight `(Ǧ - M)_{β₁β₁}` of `p2Graph` (the first solid edge) with the other solid edges -/
def lvl1ExP2p : SEdge (Fin 2 ⊕ Fin 4) × List (SEdge (Fin 2 ⊕ Fin 4)) :=
  (⟨true, true, Sum.inr 1, Sum.inr 1⟩, [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩,
    ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩])

/-- **Step 1 as a `LocStep`** at the light-weight `(Ǧ - M)_{β₁β₁}` of `p2Graph`: the graph, the selected weight, the selector `(c, t) = (false, false)`;
the outputs are the four terms of `(Owx)` followed by the dotted edge partition, packed (`lvl1Pack`). -/
theorem lvl1_inst_locStep_weight : LocStep (mE 0) p2Graph.pack
    (lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false)) :=
  LocStep.weight p2Graph.pack lvl1ExP2p List.mem_cons_self (Sum.inr (1 : Fin 4) : Fin 2 ⊕ Fin 4) false false rfl

/-- **One step of `strat_local` and its expectation identity, Step 1** at the light-weight `(Ǧ - M)_{β₁β₁}` of `p2Graph`
(`(eq:p=2graph)`), at the merged instance data (`d = 3`, `L = 3`, `W = 1`, `E = 0`, `t = 1/2`, `m = i`, `M = m·1`,
`S⁺ = S (1 - m² S)⁻¹`; `GaussIBP` is the proved `gaussIBP`): every hypothesis of `lvl1_step_identity` is discharged. -/
theorem lvl1_inst_step1 :
    ∫ ω, p2Graph.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
        lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      ((lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false)).map fun Q =>
        ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum :=
  lvl1_step_identity lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num)
    (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM
    lwSymm_inst_hM0 lvl1_inst_locStep_weight (by decide) lwSymmInstL

/-- the last element of a list, with the other elements, is one of the pairs of `lwSplit` -/
theorem lvl1_split_last {κ : Type*} (l : List κ) (a : κ) : (a, l) ∈ lwSplit (l ++ [a]) := by
  induction l with
  | nil => simp [lwSplit]
  | cons b l ih =>
    simp only [List.cons_append, lwSplit, List.mem_cons, List.mem_map]
    exact Or.inr ⟨(a, l), ih, rfl⟩

/-- the selected red light-weight `(Ḡ - M̄)_{a₀ a₀}` at the external vertex `a₀` of `lvl1ExLoopExt` (its last solid edge), with the other
solid edges -/
def lvl1ExLoopExtp : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3)) :=
  (⟨false, true, Sum.inl 0, Sum.inl 0⟩, lvl1ExStd.solid)

/-- **Step 1 at an external vertex, for a red weight** (`(Owx)` at `x = a₀ ∈ E`, the selector `(c, t) = (true, false)` conjugates): a `LocStep`
of `lvl1ExLoopExt`. -/
theorem lvl1_inst_locStep_weightExt : LocStep (mE 0) lvl1ExLoopExt.pack
    (lvl1Pack lvl1ExLoopExt.pack (lvl1WeightOuts0 (mE 0) lvl1ExLoopExt lvl1ExLoopExtp (Sum.inl (0 : Fin 2)) true false)) :=
  LocStep.weight lvl1ExLoopExt.pack lvl1ExLoopExtp (lvl1_split_last _ _) (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) true false rfl

/-- the expectation identity of that step at the instance data -/
theorem lvl1_inst_step1Ext :
    ∫ ω, lvl1ExLoopExt.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
        lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      ((lvl1Pack lvl1ExLoopExt.pack (lvl1WeightOuts0 (mE 0) lvl1ExLoopExt lvl1ExLoopExtp (Sum.inl (0 : Fin 2)) true
          false)).map fun Q =>
        ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum :=
  lvl1_step_identity lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num)
    (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM
    lwSymm_inst_hM0 lvl1_inst_locStep_weightExt (by decide) lwSymmInstL

/-- the selected in-edge `G_{a₀ α₀}` of the degree-`1` vertex `α₀` of `lvl1ExDeg1` -/
def lvl1ExDeg1p : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3)) := (⟨true, false, Sum.inl 0, Sum.inr 0⟩, [])

/-- **Step 2 as a `LocStep`** at the vertex `α₀` of degree `1` of `lvl1ExDeg1`: no weight, `deg α₀ = 1 ∉ {0, 2}`; the in-edge `G_{a₀ α₀}` is
made the blue out-edge by the selector `(c, t) = (false, true)` (transposition). -/
theorem lvl1_inst_locStep_edge : LocStep (mE 0) lvl1ExDeg1.pack
    (lvl1Pack lvl1ExDeg1.pack (lvl1EdgeOuts0 (mE 0) lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true)) :=
  LocStep.edge lvl1ExDeg1.pack lvl1ExDeg1p List.mem_cons_self (0 : Fin 3) (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3)
    (by decide : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) ≠ Sum.inr (0 : Fin 3)) false true rfl (by decide) (by decide)

/-- **Step 2** at the vertex `α₀` of degree `1` of `lvl1ExDeg1` (no weight; the in-edge `G_{a₀ α₀}` is made the blue out-edge by
the selector `(c, t) = (false, true)`, the transposition): the step and its expectation identity at the instance data. -/
theorem lvl1_inst_step2 :
    ∫ ω, lvl1ExDeg1.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
        lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      ((lvl1Pack lvl1ExDeg1.pack (lvl1EdgeOuts0 (mE 0) lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true)).map fun Q =>
        ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum :=
  lvl1_step_identity lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num)
    (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM
    lwSymm_inst_hM0 lvl1_inst_locStep_edge (by decide) lwSymmInstL

/-- the selected pair `G_{a₀ α₀}`, `G_{α₀ a₁}` at the vertex `α₀` of `lvl1ExSame` -/
def lvl1ExSamep : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3)) :=
  (⟨true, false, Sum.inl 0, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inl 1⟩])

def lvl1ExSameq : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3)) := (⟨true, false, Sum.inr 0, Sum.inl 1⟩, [])

/-- **Step 3 as a `LocStep`** at the vertex `α₀` of `lvl1ExSame`: no weight, every internal vertex of degree `0` or `2` with neutral charge,
`α₀` has the two blue edges `G_{a₀ α₀} G_{α₀ a₁}`; the selector is the transposition. -/
theorem lvl1_inst_locStep_gg : LocStep (mE 0) lvl1ExSame.pack
    (lvl1Pack lvl1ExSame.pack (lvl1GGOuts0 (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2))
      (Sum.inl (1 : Fin 2)) false true)) :=
  LocStep.gg lvl1ExSame.pack lvl1ExSamep lvl1ExSameq List.mem_cons_self List.mem_cons_self (0 : Fin 3)
    (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 3)
    (by decide : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) ≠ Sum.inr (0 : Fin 3)) false true rfl rfl (by decide) (by decide)

/-- **Step 3** at the vertex `α₀` of `lvl1ExSame` (no weight, every internal vertex of degree `0` or `2` with neutral charge, `α₀`
has the two blue edges `G_{a₀ α₀} G_{α₀ a₁}`; the selector is the transposition): the step and its expectation identity at the
instance data. -/
theorem lvl1_inst_step3 :
    ∫ ω, lvl1ExSame.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
        lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      ((lvl1Pack lvl1ExSame.pack (lvl1GGOuts0 (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2))
          (Sum.inl (1 : Fin 2)) false true)).map fun Q =>
        ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum :=
  lvl1_step_identity lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num)
    (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM
    lwSymm_inst_hM0 lvl1_inst_locStep_gg (by decide) lwSymmInstL

/-- the counters `(n_S, n_W, n_V, n_M)` of a graph, as a tuple -/
def lvl1Counts4 {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (g : LGraph E I) : ℕ × ℕ × ℕ × ℕ :=
  (g.nS, g.nW, g.nV, g.nM)

/-- **The outputs of Step 1 on `p2Graph`, listed before the dotted edge partition** (`lvl1_inst_locStep_weight`): `p2Graph` has the counters
`(6, 2, 4, 2)` and order `2`; the twelve terms of `(Owx)` at `(Ǧ - M)_{β₁β₁}` (`T1`, `T2`, and `T3`, `T4` for each of the five other solid
edges) have counters `(7, 3, 5, 2)` (`T1` and the five `T3`) and `(7, 4, 6, 2)` (`T2` and the five `T4`), all of order `3 = ord p2Graph + 1`.
Each term is then followed by `LGraph.partition`, whose output lists are not computable in the kernel. -/
theorem lvl1_inst_step1_terms :
    lvl1Counts4 p2Graph = (6, 2, 4, 2) ∧ ord p2Graph.counters = 2 ∧
    lvl1Counts4 (lwSymmOwxT1 false false (mE 0) p2Graph (Sum.inr 1)) = (7, 3, 5, 2) ∧
    lvl1Counts4 (lwSymmOwxT2 false false (mE 0) p2Graph lvl1ExP2p (Sum.inr 1)) = (7, 4, 6, 2) ∧
    ((lwSplit lvl1ExP2p.2).map fun q => lvl1Counts4 (lwSymmOwxT3 false false (mE 0) p2Graph (Sum.inr 1) q)) =
      [(7, 3, 5, 2), (7, 3, 5, 2), (7, 3, 5, 2), (7, 3, 5, 2), (7, 3, 5, 2)] ∧
    ((lwSplit lvl1ExP2p.2).map fun q => lvl1Counts4 (lwSymmOwxT4 false false (mE 0) p2Graph (Sum.inr 1) q)) =
      [(7, 4, 6, 2), (7, 4, 6, 2), (7, 4, 6, 2), (7, 4, 6, 2), (7, 4, 6, 2)] ∧
    ord (lwSymmOwxT1 false false (mE 0) p2Graph (Sum.inr 1)).counters = 3 ∧
    ord (lwSymmOwxT2 false false (mE 0) p2Graph lvl1ExP2p (Sum.inr 1)).counters = 3 ∧
    ((lwSplit lvl1ExP2p.2).map fun q => ord (lwSymmOwxT3 false false (mE 0) p2Graph (Sum.inr 1) q).counters) =
      [3, 3, 3, 3, 3] ∧
    ((lwSplit lvl1ExP2p.2).map fun q => ord (lwSymmOwxT4 false false (mE 0) p2Graph (Sum.inr 1) q).counters) =
      [3, 3, 3, 3, 3] := by decide

/-- **The outputs of Step 2 on `lvl1ExDeg1`, listed before the dotted edge partition**: `lvl1ExDeg1` has the counters `(1, 0, 3, 3)`, order
`-5`; the edge `G_{a₀ α₀}` is alone (`lwSplit p.2 = []`), so the only term is the loop term `(Owx)` (`m 1_{x = y₁}` is `0`), with counters
`(2, 1, 4, 3)`, order `-4`. -/
theorem lvl1_inst_step2_terms :
    lvl1Counts4 lvl1ExDeg1 = (1, 0, 3, 3) ∧ ord lvl1ExDeg1.counters = -5 ∧ lwSplit lvl1ExDeg1p.2 = [] ∧
    lvl1Counts4 (lwSymmOe1xOwx false true (mE 0) lvl1ExDeg1 lvl1ExDeg1p 0) = (2, 1, 4, 3) ∧
    ord (lwSymmOe1xOwx false true (mE 0) lvl1ExDeg1 lvl1ExDeg1p 0).counters = -4 := by decide

/-- **The outputs of Step 3 on `lvl1ExSame`, listed before the dotted edge partition**: `lvl1ExSame` has the counters `(2, 0, 3, 3)`, order
`-4`; `q.2 = []`, so there are no terms `R7`, `R8`; the terms `R2`, `R3`, `R4`, `R5`, `R6` have the counters `(1, 1, 3, 2)`, `(3, 1, 4, 3)`,
`(3, 2, 5, 3)`, `(3, 1, 4, 3)`, `(3, 2, 5, 3)`, all of order `-3 = ord + 1` (`R1` is `0`). -/
theorem lvl1_inst_step3_terms :
    lvl1Counts4 lvl1ExSame = (2, 0, 3, 3) ∧ ord lvl1ExSame.counters = -4 ∧ lwSplit lvl1ExSameq.2 = [] ∧
    lvl1Counts4 (lwSymmOe2xR2 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0 (Sum.inl 0) (Sum.inl 1)) = (1, 1, 3, 2) ∧
    lvl1Counts4 (lwSymmOe2xR3 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0) = (3, 1, 4, 3) ∧
    lvl1Counts4 (lwSymmOe2xR4 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0 (Sum.inl 0) (Sum.inl 1)) = (3, 2, 5, 3) ∧
    lvl1Counts4 (lwSymmOe2xR5 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0 (Sum.inl 0) (Sum.inl 1)) = (3, 1, 4, 3) ∧
    lvl1Counts4 (lwSymmOe2xR6 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0 (Sum.inl 0) (Sum.inl 1)) = (3, 2, 5, 3) ∧
    ord (lwSymmOe2xR2 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0 (Sum.inl 0) (Sum.inl 1)).counters = -3 ∧
    ord (lwSymmOe2xR3 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0).counters = -3 ∧
    ord (lwSymmOe2xR4 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0 (Sum.inl 0) (Sum.inl 1)).counters = -3 ∧
    ord (lwSymmOe2xR5 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0 (Sum.inl 0) (Sum.inl 1)).counters = -3 ∧
    ord (lwSymmOe2xR6 false true (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq 0 (Sum.inl 0) (Sum.inl 1)).counters = -3 := by decide

end ExamplesStep

section ExamplesLemma

open RBM.Gauss.SizesInst

/-- the cutoff of the `p = 2` graph for `c = 1/4`, `K0 = 1`, `d = 3`, `D = 10`: `(10 + 1·2 + 3·2) / (1/4) = 72` -/
theorem lvl1_inst_cutoff : lvl1Cutoff (1 / 4) 1 3 10 p2Graph.counters = 72 := by
  have h := p2Graph_counters
  have hM : p2Graph.counters.nM = 2 := h.2.2.2
  have hV : p2Graph.counters.nV = 4 := h.2.2.1
  have hW : p2Graph.counters.nW = 2 := h.2.1
  unfold lvl1Cutoff
  rw [hM, hV, hW]
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- **`lvl1_size_le` at concrete counters** (`d = 3`, `c = 1/4`, `K0 = 1`, `D = 10`, `G = p2Graph.counters`, `W = 27`, `L = 3`,
`Ψ = 27^{-1/4}`): a graph with `n_S = 80`, `n_W = 4`, `n_V = 6`, `n_M = 1` has order `76 ≥ 72`, `n_M ≤ 2`, `n_V - n_W = 2 ≤ 2`, hence size
`≤ 27^{-10}`; `L^3 = 27 ≤ 27^1` and `27^{-3/2} ≤ Ψ ≤ 27^{-1/4}`. -/
theorem lvl1_inst_size_le :
    (⟨80, 4, 6, 1, 0, 0⟩ : Counters).scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ)) := by
  have h := p2Graph_counters
  have e1 : p2Graph.counters.nV = 4 := h.2.2.1
  have e2 : p2Graph.counters.nW = 2 := h.2.1
  have e3 : p2Graph.counters.nM = 2 := h.2.2.2
  refine lvl1_size_le (1 / 4) (by norm_num) 1 3 10 p2Graph.counters 27 3 _ (by norm_num) (by norm_num) (by norm_num) ?_
    (le_refl _) (⟨80, 4, 6, 1, 0, 0⟩ : Counters) ?_ ?_ ?_
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · rw [lvl1_inst_cutoff]; norm_num [ord]
  · rw [e3]; norm_num
  · rw [e1, e2]; norm_num

/-- **The `lvl1 lemma` on `p2Graph`** with the order cutoff `K = 72` at the merged instance data: the lists exist, every graph of `outs`
is locally standard of order in `[2, 72)`, every graph of `errs` has order `≥ 72`, and the expectation identity holds at the instance
data with every hypothesis discharged (`GaussIBP` is the proved `gaussIBP`, the rest deterministic). -/
theorem lvl1_inst_lemma :
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < 72) ∧ (∀ Q ∈ errs, 72 ≤ Q.g.scalingOrder) ∧
      ∫ ω, p2Graph.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum := by
  obtain ⟨outs, errs, h1, h2, -, hid⟩ := lvl1_lemma (mE 0) 72 p2Graph.pack (by decide)
  refine ⟨outs, errs, fun Q hQ => ?_, h2, ?_⟩
  · obtain ⟨a, b, c⟩ := h1 Q hQ
    have e : p2Graph.pack.g.scalingOrder = 2 := p2Graph_ord
    exact ⟨a, by rw [e] at b; exact b, c⟩
  · exact hid lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num) (lwWx_mE_ne 0 lwWx_inst_hE)
      (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 lwSymmInstL

/-- **The `lvl1 lemma` in the paper's form on `p2Graph`**, `d = 3`, `c = 1/4`, `K0 = 1` (`L^3 ≤ W`), `D = 10`; the regime is evaluated at
`W = 27`, `L = 3`, `Ψ = 27^{-1/4}` (`27^{-3/2} ≤ Ψ ≤ 27^{-1/4}`, `L^3 = 27 ≤ 27^1`): every graph of `errs` has scaling size `≤ 27^{-10}`;
the graphs of `outs` are locally standard of order `≥ 2 = ord p2Graph`; and the expectation identity holds at the instance data. -/
theorem lvl1_inst_lemma_size :
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, Q.g.scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧
      ∫ ω, p2Graph.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum := by
  obtain ⟨outs, errs, h1, h2, -, hid⟩ := lvl1_lemma_size (E := Fin 2) (mE 0) (1 / 4) (by norm_num) 1 3 10 p2Graph.pack (by decide)
  refine ⟨outs, errs, fun Q hQ => ?_, fun Q hQ => ?_, ?_⟩
  · obtain ⟨a, b⟩ := h1 Q hQ
    have e : p2Graph.pack.g.scalingOrder = 2 := p2Graph_ord
    exact ⟨a, by rw [e] at b; exact b⟩
  · refine h2 Q hQ 27 3 _ (by norm_num) (by norm_num) (by norm_num) ?_ (le_refl _)
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · exact hid lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num) (lwWx_mE_ne 0 lwWx_inst_hE)
      (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 lwSymmInstL

end ExamplesLemma

section ExamplesInduction

/-- **`lvl1_induction` applied to the invariant "normal, `n_M ≤ 2`"** (the molecule count of `p2Graph` does not increase) at the graphs of
the lists of `lvl1_lemma` for an arbitrary cutoff: the invariant holds at `p2Graph` and passes along every `LocStep`
(by `lvl1_step_good`), hence holds at every graph of `outs` and `errs`. -/
theorem lvl1_inst_induction (K : ℤ) : ∃ outs errs : List (PGraph (Fin 2)), ∀ Q ∈ outs ++ errs, Q.g.Normal ∧ Q.g.nM ≤ 2 := by
  obtain ⟨outs, errs, -, -, hall, -⟩ := lvl1_lemma (mE 0) K p2Graph.pack (by decide)
  refine ⟨outs, errs, fun Q hQ => ?_⟩
  refine lvl1_induction (hall Q hQ).1 (fun R : PGraph (Fin 2) => R.g.Normal ∧ R.g.nM ≤ 2) ⟨by decide, by decide⟩ ?_
  intro A L hst hA B hB
  obtain ⟨hBN, hg⟩ := lvl1_step_good hst hA.1 B hB
  exact ⟨hBN, le_trans hg.2.1 hA.2⟩

/-- **`lvl1_lemma_induction` on `p2Graph`** (the same invariant, with the predicate chosen after the lists): the lists exist with the
invariant "normal, `n_M ≤ 2`" holding at all their graphs, at the instance data of the identity with every hypothesis discharged. -/
theorem lvl1_inst_lemma_induction (K : ℤ) :
    ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs ++ errs, Q.g.Normal ∧ Q.g.nM ≤ 2) ∧
      ∫ ω, p2Graph.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum := by
  obtain ⟨outs, errs, -, -, hP, hid⟩ := lvl1_lemma_induction (mE 0) K p2Graph.pack (by decide)
  refine ⟨outs, errs, ?_, hid lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num)
    (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM
    lwSymm_inst_hM0 lwSymmInstL⟩
  refine hP (fun R : PGraph (Fin 2) => R.g.Normal ∧ R.g.nM ≤ 2) ⟨by decide, by decide⟩ ?_
  intro A L hst hA B hB
  obtain ⟨hBN, hg⟩ := lvl1_step_good hst hA.1 B hB
  exact ⟨hBN, le_trans hg.2.1 hA.2⟩

end ExamplesInduction

end RBM.Graph
end
end Lvl1PartY
