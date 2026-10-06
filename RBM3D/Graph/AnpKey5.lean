/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey3
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card

/-!
# LW-12e: `lem:Anp_key_gh`, case (IV) part 1: the nested order of summation (T2264)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): Case (IV) `:1385`,
the pigeonhole and properties (1)-(2) `:1388-1393`, the nested order `:1400-1402`, `(eq:degali)`
`:1403-1406`, the spanning tree `𝕋` and its re-rooting `:1414-1451`.  Part e of the six tickets of
`lem:Anp`.

The statements are combinatorial (no `ψ`, no `ξ`).  `anpKey5_cert`: every nested graph with one
edge removed per path (its ghost, or a reserved long edge) has a summation certificate for its
remaining solid edges: a nested order of summation (every internal vertex, in turn, has two
solid edges to external or earlier vertices), or an AM-GM split `ξ_k ξ_{k'} ≤ (ξ_k² + ξ_{k'}²)/2`
(`7_8:1428-1431`) with certificates for both branches.  The route replaces the paper's
pigeonhole (false for nested graphs whose paths pass through external vertices) by Hall:

* `anpKey5_cross_ge`: every set `S` of internal vertices has `≥ |S|` remaining edges leaving `S`;
* `anpKey5_inside_ge`: if every vertex of `S` has `≤ 1` remaining edge leaving `S`, then `S`
  carries `≥ |S|` remaining edges inside;
* `anpKey5_graph`: these two bounds (and no loops) give the certificate: greedy order from the
  external vertices; on the stuck rest, a minimal closed set `U` has a non-bridge pair `α₁ α₂`;
  AM-GM on the leaving edges of `α₁`, `α₂`; induction on the stuck rest.

* Section 1: the vocabulary.
* Section 2: counting helpers.
* Section 3: the order of summation (valid prefixes, greedy, replacement of an edge).
* Section 4: sparse sets (Forest lemma) and the non-bridge pair.
* Section 5: the AM-GM branch and `anpKey5_graph`.
* Section 6: the walks of a nested graph: `anpKey5_cross_ge`, `anpKey5_inside_ge`.
* Section 7: the target `anpKey5_cert`.
* Section 8: compiled nonempty instances.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Vocabulary -/

section Vocab

/-- The vertex `w` is an internal vertex in `S`. -/
def anpKey5_inS {p q : ℕ} (S : Finset (Fin q)) (w : NV p q) : Bool :=
  Sum.elim (fun _ : Fin p ⊕ Fin p => false) (fun i : Fin q => decide (i ∈ S)) w

/-- The number of edges of `E` with exactly one end in `S`. -/
def anpKey5_cross {p q : ℕ} (E : List (NV p q × NV p q)) (S : Finset (Fin q)) : ℕ :=
  E.countP fun e => anpKey5_inS S e.1 != anpKey5_inS S e.2

/-- The number of edges of `E` at `α_v` whose other end is not in `S`. -/
def anpKey5_crossAt {p q : ℕ} (E : List (NV p q × NV p q)) (S : Finset (Fin q)) (v : Fin q) : ℕ :=
  E.countP fun e => (decide (e.1 = Sum.inr v) && !anpKey5_inS S e.2) || (decide (e.2 = Sum.inr v) && !anpKey5_inS S e.1)

/-- The number of edges of `E` with both ends in `S`. -/
def anpKey5_inside {p q : ℕ} (E : List (NV p q × NV p q)) (S : Finset (Fin q)) : ℕ :=
  E.countP fun e => anpKey5_inS S e.1 && anpKey5_inS S e.2

/-- The vertex `w` is external or among the first `m` entries of `σ`. -/
def anpKey5_early {p q : ℕ} (σ : List (Fin q)) (m : ℕ) (w : NV p q) : Bool :=
  Sum.elim (fun _ : Fin p ⊕ Fin p => true) (fun i : Fin q => decide (i ∈ σ.take m)) w

/-- A nested order of summation (`7_8:1400-1402`) for the solid edges `E` (endpoint pairs):
`σ` lists every internal vertex once, and `σ[m]` has at least two edges whose other end is external
or an earlier `σ[m']`.  The vertices are summed in the order `σ[last], …, σ[0]`: when `σ[m]` is
summed, two of its edges go to labels still fixed (`Σ_x ξ(y₁,x) ξ(y₂,x) ≤ θ`), its other edges are
`≤ ψ(0)`. -/
def AnpSumOrder {p q : ℕ} (E : List (NV p q × NV p q)) (σ : List (Fin q)) : Prop :=
  σ.Nodup ∧ (∀ i : Fin q, i ∈ σ) ∧
    ∀ m : Fin σ.length, 2 ≤ E.countP fun e =>
      (decide (e.1 = Sum.inr (σ.get m)) && anpKey5_early σ m.1 e.2) ||
        (decide (e.2 = Sum.inr (σ.get m)) && anpKey5_early σ m.1 e.1)

/-- A summation certificate of depth `≤ n`: a nested order, or an AM-GM split
`ξ_k ξ_{k'} ≤ (ξ_k² + ξ_{k'}²)/2` (`7_8:1428-1431`): the edge `k'` replaced by a copy of `k`, and
`k` by a copy of `k'`, each with a certificate of depth `≤ n - 1`. -/
def AnpSumCert {p q : ℕ} : ℕ → List (NV p q × NV p q) → Prop
  | 0, E => ∃ σ : List (Fin q), AnpSumOrder E σ
  | n + 1, E => (∃ σ : List (Fin q), AnpSumOrder E σ) ∨
      ∃ k k' : Fin E.length, k ≠ k' ∧ AnpSumCert n (E.set k'.1 (E.get k)) ∧ AnpSumCert n (E.set k.1 (E.get k'))

/-- The solid edges of `Γ` outside `M`, as endpoint pairs (`M`: the reserved long edges of the
ghost-free paths in LW-12f's union bound; ghost edges are dropped in any case). -/
def anpKey5_rest {p q : ℕ} (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) : List (NV p q × NV p q) :=
  (List.finRange Γ.es.length).filterMap fun k =>
    if (Γ.es.get k).ghost = true ∨ k ∈ M then none else some ((Γ.es.get k).u, (Γ.es.get k).v)

/-- Every path has at most one edge that is a ghost or in `M`. -/
def anpKey5_perPath {p q : ℕ} (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) : Prop :=
  ∀ j : Fin p, ((Γ.path j).filter fun st => (Γ.es.get st.1).ghost || decide (st.1 ∈ M)).length ≤ 1

instance anpKey5_decSumOrder {p q : ℕ} (E : List (NV p q × NV p q)) (σ : List (Fin q)) :
    Decidable (AnpSumOrder E σ) := by
  unfold AnpSumOrder; infer_instance

instance anpKey5_decPerPath {p q : ℕ} (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) :
    Decidable (anpKey5_perPath Γ M) := by
  unfold anpKey5_perPath; infer_instance

end Vocab

/-! ## 2. Counting helpers -/

section Count

theorem anpKey5_ite_pos {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem anpKey5_ite_neg {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem anpKey5_countP_eq_sum {α : Type*} (P : α → Bool) (l : List α) :
    l.countP P = ∑ i : Fin l.length, if P (l.get i) = true then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons]
    change _ = ∑ i : Fin (t.length + 1), if P ((a :: t).get i) = true then 1 else 0
    rw [Fin.sum_univ_succ]
    have h0 : ((a :: t).get 0) = a := rfl
    have hs : ∀ i : Fin t.length, ((a :: t).get i.succ) = t.get i := fun i => rfl
    simp only [h0, hs]
    rw [← ih]
    omega

theorem anpKey5_countP_eq_card {α : Type*} (P : α → Bool) (l : List α) :
    l.countP P = (Finset.univ.filter fun i : Fin l.length => P (l.get i) = true).card := by
  rw [anpKey5_countP_eq_sum, Finset.card_filter]

theorem anpKey5_two_le_countP {α : Type*} (P : α → Bool) (l : List α) (i j : Fin l.length) (hij : i ≠ j)
    (hi : P (l.get i) = true) (hj : P (l.get j) = true) : 2 ≤ l.countP P := by
  rw [anpKey5_countP_eq_card]
  have : ({i, j} : Finset (Fin l.length)) ⊆ Finset.univ.filter fun i : Fin l.length => P (l.get i) = true := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa [List.get_eq_getElem] using ‹_›
  have := Finset.card_le_card this
  rwa [Finset.card_pair hij] at this

theorem anpKey5_one_le_countP {α : Type*} (P : α → Bool) (l : List α) (i : Fin l.length)
    (hi : P (l.get i) = true) : 1 ≤ l.countP P := by
  rw [anpKey5_countP_eq_card]
  exact Finset.card_pos.2 ⟨i, by simpa [List.get_eq_getElem] using hi⟩

theorem anpKey5_countP_le_sum {α β : Type*} (T : Finset β) (g : α → Bool) (h : β → α → Bool) (l : List α)
    (hl : ∀ e ∈ l, g e = true → ∃ v ∈ T, h v e = true) : l.countP g ≤ ∑ v ∈ T, l.countP (h v) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib]
    have ih' := ih fun e he => hl e (List.mem_cons_of_mem _ he)
    have : (if g a = true then 1 else 0) ≤ ∑ v ∈ T, (if h v a = true then 1 else 0) := by
      by_cases hg : g a = true
      · obtain ⟨v, hv, hh⟩ := hl a List.mem_cons_self hg
        simp only [hg, ↓reduceIte]
        calc 1 = (if h v a = true then 1 else 0) := by simp [hh]
          _ ≤ _ := Finset.single_le_sum (f := fun v => if h v a = true then 1 else 0) (fun _ _ => Nat.zero_le _) hv
      · simp [hg]
    omega

theorem anpKey5_countP_set {α : Type*} (P : α → Bool) (l : List α) (k : Fin l.length) (a : α)
    (h1 : P (l.get k) = false) (h2 : P a = false) : (l.set k.1 a).countP P = l.countP P := by
  rw [List.countP_set k.2]
  have h1' : P l[k.1] = false := by simpa [List.get_eq_getElem] using h1
  simp [h1', h2]

theorem anpKey5_rest_countP {p q : ℕ} (Γ : NGraph p q) (M : Finset (Fin Γ.es.length))
    (f : NV p q × NV p q → Bool) :
    (anpKey5_rest Γ M).countP f = ∑ k : Fin Γ.es.length,
      if ((Γ.es.get k).ghost = false ∧ k ∉ M) ∧ f ((Γ.es.get k).u, (Γ.es.get k).v) = true then 1 else 0 := by
  unfold anpKey5_rest
  rw [List.countP_filterMap, Fin.sum_univ_def]
  have key : ∀ l : List (Fin Γ.es.length), l.countP (fun a =>
      (Option.map f (if (Γ.es.get a).ghost = true ∨ a ∈ M then none else some ((Γ.es.get a).u, (Γ.es.get a).v))).getD false) =
      (l.map fun k => if ((Γ.es.get k).ghost = false ∧ k ∉ M) ∧ f ((Γ.es.get k).u, (Γ.es.get k).v) = true then 1 else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.countP_cons, ih, List.map_cons, List.sum_cons]
      by_cases hg : (Γ.es.get a).ghost = true ∨ a ∈ M
      · have h1 : (Option.map f (if (Γ.es.get a).ghost = true ∨ a ∈ M then none else
            some ((Γ.es.get a).u, (Γ.es.get a).v))).getD false = false := by simp only [hg, ↓reduceIte]; rfl
        have h2 : ¬ (((Γ.es.get a).ghost = false ∧ a ∉ M) ∧ f ((Γ.es.get a).u, (Γ.es.get a).v) = true) := by
          rintro ⟨⟨h3, h4⟩, -⟩
          rcases hg with h | h
          · rw [h3] at h; exact Bool.noConfusion h
          · exact h4 h
        rw [h1]; simp only [h2, ↓reduceIte]; simp
      · have h3 : (Γ.es.get a).ghost = false ∧ a ∉ M := by
          rw [not_or] at hg
          exact ⟨by simpa using hg.1, hg.2⟩
        have h1 : (Option.map f (if (Γ.es.get a).ghost = true ∨ a ∈ M then none else
            some ((Γ.es.get a).u, (Γ.es.get a).v))).getD false = f ((Γ.es.get a).u, (Γ.es.get a).v) := by
          simp only [hg, ↓reduceIte]; rfl
        rw [h1]
        by_cases hf : f ((Γ.es.get a).u, (Γ.es.get a).v) = true
        · rw [anpKey5_ite_pos hf, anpKey5_ite_pos ⟨h3, hf⟩]; omega
        · rw [anpKey5_ite_neg hf, anpKey5_ite_neg (fun h => hf h.2)]; omega
  exact key _

end Count

/-! ## 3. Nested orders of summation: valid prefixes, greedy extension, replacing an edge -/

section Order

variable {p q : ℕ}

theorem anpKey5_inS_inl (S : Finset (Fin q)) (x : Fin p ⊕ Fin p) : anpKey5_inS S (Sum.inl x : NV p q) = false := rfl

theorem anpKey5_inS_inr (S : Finset (Fin q)) (i : Fin q) :
    anpKey5_inS S (Sum.inr i : NV p q) = decide (i ∈ S) := rfl

theorem anpKey5_inS_mono {S T : Finset (Fin q)} (h : S ⊆ T) (w : NV p q) (hw : anpKey5_inS S w = true) :
    anpKey5_inS T w = true := by
  rcases w with x | i
  · exact absurd hw (by simp [anpKey5_inS_inl])
  · simp only [anpKey5_inS_inr, decide_eq_true_eq] at hw ⊢
    exact h hw

theorem anpKey5_inS_true {S : Finset (Fin q)} {w : NV p q} (hw : anpKey5_inS S w = true) :
    ∃ i, w = Sum.inr i ∧ i ∈ S := by
  rcases w with x | i
  · exact absurd hw (by simp [anpKey5_inS_inl])
  · exact ⟨i, rfl, by simpa [anpKey5_inS_inr] using hw⟩

/-- The internal vertices not yet listed in `σ`. -/
def anpKey5_comp (σ : List (Fin q)) : Finset (Fin q) := Finset.univ.filter fun i => i ∉ σ

theorem anpKey5_mem_comp {σ : List (Fin q)} {i : Fin q} : i ∈ anpKey5_comp σ ↔ i ∉ σ := by
  simp [anpKey5_comp]

/-- `σ` is a valid prefix of a nested order for `E`: every listed vertex has two edges to external or
earlier vertices. -/
def anpKey5_valid (E : List (NV p q × NV p q)) (σ : List (Fin q)) : Prop :=
  σ.Nodup ∧ ∀ m : Fin σ.length, 2 ≤ E.countP fun e =>
      (decide (e.1 = Sum.inr (σ.get m)) && anpKey5_early σ m.1 e.2) ||
        (decide (e.2 = Sum.inr (σ.get m)) && anpKey5_early σ m.1 e.1)

theorem anpKey5_sumOrder_of_valid {E : List (NV p q × NV p q)} {σ : List (Fin q)} (h : anpKey5_valid E σ)
    (hc : ∀ i : Fin q, i ∈ σ) : AnpSumOrder E σ := ⟨h.1, hc, h.2⟩

theorem anpKey5_valid_nil (E : List (NV p q × NV p q)) : anpKey5_valid E [] :=
  ⟨List.nodup_nil, fun m => m.elim0⟩

theorem anpKey5_early_comp (σ : List (Fin q)) (w : NV p q) :
    anpKey5_early σ σ.length w = !anpKey5_inS (anpKey5_comp σ) w := by
  rcases w with x | i
  · rfl
  · simp [anpKey5_early, anpKey5_inS, anpKey5_comp]

theorem anpKey5_valid_append {E : List (NV p q × NV p q)} {σ : List (Fin q)} {v : Fin q}
    (hv : anpKey5_valid E σ) (hnot : v ∉ σ) (h2 : 2 ≤ anpKey5_crossAt E (anpKey5_comp σ) v) :
    anpKey5_valid E (σ ++ [v]) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hv.1, List.nodup_singleton v, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact hnot ha
  · intro ⟨m, hm⟩
    by_cases hlt : m < σ.length
    · have h := hv.2 ⟨m, hlt⟩
      have e1 : (σ ++ [v]).get ⟨m, hm⟩ = σ.get ⟨m, hlt⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hlt]
      have e2 : (σ ++ [v]).take m = σ.take m := List.take_append_of_le_length (le_of_lt hlt)
      have e3 : ∀ w : NV p q, anpKey5_early (σ ++ [v]) m w = anpKey5_early σ m w := by
        intro w; simp [anpKey5_early, e2]
      simp only [e1, e3]
      exact h
    · have hm' : m = σ.length := by simp at hm; omega
      subst hm'
      have e1 : (σ ++ [v]).get ⟨σ.length, hm⟩ = v := by simp [List.get_eq_getElem]
      have e2 : (σ ++ [v]).take σ.length = σ := List.take_left
      have e3 : ∀ w : NV p q, anpKey5_early (σ ++ [v]) σ.length w = !anpKey5_inS (anpKey5_comp σ) w := by
        intro w; rw [← anpKey5_early_comp]; simp [anpKey5_early, e2]
      simp only [e1, e3]
      exact h2

theorem anpKey5_comp_append_card {σ : List (Fin q)} {v : Fin q} (hnot : v ∉ σ) :
    (anpKey5_comp (σ ++ [v])).card < (anpKey5_comp σ).card := by
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [anpKey5_mem_comp] at hi ⊢
    exact fun h => hi (List.mem_append_left _ h)
  · intro h
    have := h (anpKey5_mem_comp.2 hnot)
    rw [anpKey5_mem_comp] at this
    exact this (by simp)

/-- Greedy extension: every valid prefix extends to a valid prefix whose unlisted vertices are stuck (each has
at most one edge to external or listed vertices). -/
theorem anpKey5_greedy (E : List (NV p q × NV p q)) :
    ∀ (n : ℕ) (σ : List (Fin q)), (anpKey5_comp σ).card ≤ n → anpKey5_valid E σ →
      ∃ σ' : List (Fin q), anpKey5_valid E σ' ∧ (∀ x ∈ σ, x ∈ σ') ∧
        ∀ v ∈ anpKey5_comp σ', anpKey5_crossAt E (anpKey5_comp σ') v ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro σ hσ hv
    refine ⟨σ, hv, fun x hx => hx, fun v hv' => ?_⟩
    have : anpKey5_comp σ = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hσ)
    rw [this] at hv'
    exact absurd hv' (Finset.notMem_empty v)
  | succ n ih =>
    intro σ hσ hv
    by_cases hall : ∀ v ∈ anpKey5_comp σ, anpKey5_crossAt E (anpKey5_comp σ) v ≤ 1
    · exact ⟨σ, hv, fun x hx => hx, hall⟩
    · push Not at hall
      obtain ⟨v, hvc, hv2⟩ := hall
      have hnot : v ∉ σ := anpKey5_mem_comp.1 hvc
      have hv' := anpKey5_valid_append hv hnot hv2
      have hcard := anpKey5_comp_append_card hnot
      obtain ⟨σ', h1, h2, h3⟩ := ih (σ ++ [v]) (by omega) hv'
      exact ⟨σ', h1, fun x hx => h2 x (List.mem_append_left _ hx), h3⟩

/-- An edge with an end `inr x`, `x` not yet listed in `σ`, contributes nothing to the validity count of a listed
vertex. -/
theorem anpKey5_valid_edge {σ : List (Fin q)} (m : Fin σ.length) (e : NV p q × NV p q)
    (he : anpKey5_inS (anpKey5_comp σ) e.1 = true ∨ anpKey5_inS (anpKey5_comp σ) e.2 = true) :
    ((decide (e.1 = Sum.inr (σ.get m)) && anpKey5_early σ m.1 e.2) ||
      (decide (e.2 = Sum.inr (σ.get m)) && anpKey5_early σ m.1 e.1)) = false := by
  have hmem : σ[m.1] ∈ σ := List.getElem_mem m.2
  have hne : ∀ j, j ∉ σ → j ≠ σ[m.1] := fun j hj h => hj (h ▸ hmem)
  have hnt : ∀ j, j ∉ σ → j ∉ σ.take m.1 := fun j hj h => hj (List.mem_of_mem_take h)
  rcases e with ⟨a, b⟩
  simp only at he ⊢
  rcases a with a | i <;> rcases b with b | j
  · simp [anpKey5_inS_inl] at he
  · have hj : j ∉ σ := by simpa [anpKey5_inS_inl, anpKey5_inS_inr, anpKey5_mem_comp] using he
    simp [anpKey5_early, hne j hj, hnt j hj]
  · have hi : i ∉ σ := by simpa [anpKey5_inS_inl, anpKey5_inS_inr, anpKey5_mem_comp] using he
    simp [anpKey5_early, hne i hi, hnt i hi]
  · have he' : i ∉ σ ∨ j ∉ σ := by simpa [anpKey5_inS_inr, anpKey5_mem_comp] using he
    rcases he' with hi | hj
    · simp [anpKey5_early, hne i hi, hnt i hi]
    · simp [anpKey5_early, hne j hj, hnt j hj]

theorem anpKey5_valid_set {E : List (NV p q × NV p q)} {σ : List (Fin q)} (hv : anpKey5_valid E σ)
    (k : Fin E.length) (e' : NV p q × NV p q)
    (hk : anpKey5_inS (anpKey5_comp σ) (E.get k).1 = true ∨ anpKey5_inS (anpKey5_comp σ) (E.get k).2 = true)
    (he : anpKey5_inS (anpKey5_comp σ) e'.1 = true ∨ anpKey5_inS (anpKey5_comp σ) e'.2 = true) :
    anpKey5_valid (E.set k.1 e') σ := by
  refine ⟨hv.1, fun m => ?_⟩
  have h := hv.2 m
  rw [anpKey5_countP_set _ E k e' (anpKey5_valid_edge m _ hk) (anpKey5_valid_edge m _ he)]
  exact h

end Order

/-! ## 4. Sparse sets (the Forest lemma) and the non-bridge pair -/

section Forest

variable {p q : ℕ}

theorem anpKey5_inS_sdiff (U T : Finset (Fin q)) (w : NV p q) :
    anpKey5_inS (U \ T) w = (anpKey5_inS U w && !anpKey5_inS T w) := by
  rcases w with x | i <;> simp [anpKey5_inS]

theorem anpKey5_inS_inter (T U : Finset (Fin q)) (w : NV p q) :
    anpKey5_inS (T ∩ U) w = (anpKey5_inS T w && anpKey5_inS U w) := by
  rcases w with x | i <;> simp [anpKey5_inS]

/-- The edges of `E` between `T` and `U \ T`. -/
def anpKey5_cut (E : List (NV p q × NV p q)) (T U : Finset (Fin q)) : ℕ :=
  E.countP fun e => (anpKey5_inS T e.1 && anpKey5_inS (U \ T) e.2) ||
    (anpKey5_inS (U \ T) e.1 && anpKey5_inS T e.2)

theorem anpKey5_countP_le_add3 {α : Type*} (l : List α) (P Q R S : α → Bool)
    (h : ∀ e ∈ l, (if P e = true then 1 else 0 : ℕ) ≤
      (if Q e = true then 1 else 0) + (if R e = true then 1 else 0) + (if S e = true then 1 else 0)) :
    l.countP P ≤ l.countP Q + l.countP R + l.countP S := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih fun e he => h e (List.mem_cons_of_mem _ he)
    have ha := h a List.mem_cons_self
    simp only [List.countP_cons]
    omega

theorem anpKey5_pw_split : ∀ x1 x2 u1 u2 : Bool, (x1 = true → u1 = true) → (x2 = true → u2 = true) →
    (if (u1 && u2) = true then 1 else 0 : ℕ) ≤ (if (x1 && x2) = true then 1 else 0) +
      (if ((u1 && !x1) && (u2 && !x2)) = true then 1 else 0) +
      (if ((x1 && (u2 && !x2)) || ((u1 && !x1) && x2)) = true then 1 else 0) := by
  decide

theorem anpKey5_pw_cutmono : ∀ t1 t2 u1 u2 v1 v2 : Bool, (u1 = true → v1 = true) → (u2 = true → v2 = true) →
    ((((t1 && u1) && (u2 && !(t2 && u2))) || ((u1 && !(t1 && u1)) && (t2 && u2))) = true →
      ((t1 && (v2 && !t2)) || ((v1 && !t1) && t2)) = true) := by
  decide

/-- The Forest lemma: if every inside edge of `U` is a bridge (a set `T ⊆ U` separating its ends with a single edge
between `T` and `U \ T`), then every nonempty `U' ⊆ U` carries at most `|U'| - 1` edges. -/
theorem anpKey5_forest (E : List (NV p q × NV p q)) (U : Finset (Fin q))
    (hb : ∀ k : Fin E.length, anpKey5_inS U (E.get k).1 = true → anpKey5_inS U (E.get k).2 = true →
      ∃ T ⊆ U, (anpKey5_inS T (E.get k).1 = true ↔ anpKey5_inS T (E.get k).2 = false) ∧
        anpKey5_cut E T U ≤ 1) :
    ∀ n : ℕ, ∀ U' ⊆ U, U'.card = n → U'.Nonempty → anpKey5_inside E U' + 1 ≤ U'.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U' hU' hcard hne
    by_cases h0 : anpKey5_inside E U' = 0
    · rw [h0]; exact Finset.card_pos.2 hne
    · have hpos : 0 < E.countP fun e => anpKey5_inS U' e.1 && anpKey5_inS U' e.2 := Nat.pos_of_ne_zero h0
      obtain ⟨e, he, hpe⟩ := List.countP_pos_iff.1 hpos
      obtain ⟨k, rfl⟩ := List.mem_iff_get.1 he
      simp only [Bool.and_eq_true] at hpe
      obtain ⟨x, hx1, hxU⟩ := anpKey5_inS_true hpe.1
      obtain ⟨y, hy1, hyU⟩ := anpKey5_inS_true hpe.2
      obtain ⟨T, hTU, hiff, hcut⟩ := hb k (anpKey5_inS_mono hU' _ hpe.1) (anpKey5_inS_mono hU' _ hpe.2)
      rw [hx1, hy1] at hiff
      simp only [anpKey5_inS_inr, decide_eq_true_eq, decide_eq_false_iff_not] at hiff
      set T' := T ∩ U' with hT'
      have hT'U : T' ⊆ U' := Finset.inter_subset_right
      have hcutT : anpKey5_cut E T' U' ≤ anpKey5_cut E T U := by
        unfold anpKey5_cut
        apply List.countP_mono_left
        intro e _ he
        simp only [hT', anpKey5_inS_inter, anpKey5_inS_sdiff] at he
        simp only [anpKey5_inS_sdiff]
        exact anpKey5_pw_cutmono _ _ _ _ _ _
          (fun h => anpKey5_inS_mono hU' _ h) (fun h => anpKey5_inS_mono hU' _ h) he
      have hne1 : T'.Nonempty ∧ (U' \ T').Nonempty := by
        by_cases hx : x ∈ T
        · have hy : y ∉ T := hiff.1 hx
          exact ⟨⟨x, Finset.mem_inter.2 ⟨hx, hxU⟩⟩,
            ⟨y, Finset.mem_sdiff.2 ⟨hyU, fun h => hy (Finset.mem_inter.1 h).1⟩⟩⟩
        · have hy : y ∈ T := by
            by_contra hy; exact hx (hiff.2 hy)
          exact ⟨⟨y, Finset.mem_inter.2 ⟨hy, hyU⟩⟩,
            ⟨x, Finset.mem_sdiff.2 ⟨hxU, fun h => hx (Finset.mem_inter.1 h).1⟩⟩⟩
      have hcardsum : (U' \ T').card + T'.card = U'.card := Finset.card_sdiff_add_card_eq_card hT'U
      have hc1 : 0 < T'.card := Finset.card_pos.2 hne1.1
      have hc2 : 0 < (U' \ T').card := Finset.card_pos.2 hne1.2
      have i1 := ih T'.card (by omega) T' (hT'U.trans hU') rfl hne1.1
      have i2 := ih (U' \ T').card (by omega) (U' \ T') (Finset.sdiff_subset.trans hU') rfl hne1.2
      have hsplit : anpKey5_inside E U' ≤ anpKey5_inside E T' + anpKey5_inside E (U' \ T') +
          anpKey5_cut E T' U' := by
        unfold anpKey5_inside anpKey5_cut
        apply anpKey5_countP_le_add3
        intro e _
        simp only [anpKey5_inS_sdiff]
        exact anpKey5_pw_split _ _ _ _ (fun h => anpKey5_inS_mono hT'U _ h) (fun h => anpKey5_inS_mono hT'U _ h)
      omega

/-- The non-bridge pair: a nonempty `U` with `|U| ≤ inside(U)` (no loops) has two vertices `x ≠ y` such that every
set `T ⊆ U` separating them has at least two edges between `T` and `U \ T`. -/
theorem anpKey5_nb (E : List (NV p q × NV p q)) (hloop : ∀ e ∈ E, e.1 ≠ e.2) (U : Finset (Fin q))
    (hU : U.Nonempty) (hin : U.card ≤ anpKey5_inside E U) :
    ∃ x y : Fin q, x ∈ U ∧ y ∈ U ∧ x ≠ y ∧ ∀ T ⊆ U, (x ∈ T ↔ y ∉ T) → 2 ≤ anpKey5_cut E T U := by
  by_contra H
  push Not at H
  have hb : ∀ k : Fin E.length, anpKey5_inS U (E.get k).1 = true → anpKey5_inS U (E.get k).2 = true →
      ∃ T ⊆ U, (anpKey5_inS T (E.get k).1 = true ↔ anpKey5_inS T (E.get k).2 = false) ∧
        anpKey5_cut E T U ≤ 1 := by
    intro k h1 h2
    obtain ⟨x, hx1, hxU⟩ := anpKey5_inS_true h1
    obtain ⟨y, hy1, hyU⟩ := anpKey5_inS_true h2
    have hxy : x ≠ y := by
      intro hxy
      apply hloop (E.get k) (List.get_mem E k)
      rw [hx1, hy1, hxy]
    obtain ⟨T, hTU, hiff, hc⟩ := H x y hxU hyU hxy
    refine ⟨T, hTU, ?_, by omega⟩
    rw [hx1, hy1]
    simpa [anpKey5_inS_inr] using hiff
  have := anpKey5_forest E U hb U.card U subset_rfl rfl hU
  omega

end Forest

/-! ## 5. Pendant edges, the AM-GM branch, and `anpKey5_graph` -/

section Graph

variable {p q : ℕ}

/-- `e` is an edge at `α_v` whose other end is not in `S` (the predicate counted by `anpKey5_crossAt`). -/
def anpKey5_pend (S : Finset (Fin q)) (v : Fin q) (e : NV p q × NV p q) : Bool :=
  (decide (e.1 = Sum.inr v) && !anpKey5_inS S e.2) || (decide (e.2 = Sum.inr v) && !anpKey5_inS S e.1)

theorem anpKey5_crossAt_eq (E : List (NV p q × NV p q)) (S : Finset (Fin q)) (v : Fin q) :
    anpKey5_crossAt E S v = E.countP (anpKey5_pend S v) := rfl

theorem anpKey5_pend_inS {S : Finset (Fin q)} {v : Fin q} (hv : v ∈ S) {e : NV p q × NV p q}
    (h : anpKey5_pend S v e = true) : anpKey5_inS S e.1 = true ∨ anpKey5_inS S e.2 = true := by
  simp only [anpKey5_pend, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · left; rw [h1, anpKey5_inS_inr]; simpa using hv
  · right; rw [h1, anpKey5_inS_inr]; simpa using hv

theorem anpKey5_pend_mono {S₁ S₂ : Finset (Fin q)} (h : S₁ ⊆ S₂) {v : Fin q} {e : NV p q × NV p q}
    (he : anpKey5_pend S₂ v e = true) : anpKey5_pend S₁ v e = true := by
  have key : ∀ w : NV p q, (!anpKey5_inS S₂ w) = true → (!anpKey5_inS S₁ w) = true := by
    intro w hw
    simp only [Bool.not_eq_true'] at hw ⊢
    by_contra hc
    rw [Bool.not_eq_false] at hc
    rw [anpKey5_inS_mono h w hc] at hw
    exact Bool.noConfusion hw
  simp only [anpKey5_pend, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at he ⊢
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, key _ h2⟩
  · exact Or.inr ⟨h1, key _ h2⟩

theorem anpKey5_pend_unique {S : Finset (Fin q)} {x y : Fin q} (hy : y ∈ S)
    {e : NV p q × NV p q} (h1 : anpKey5_pend S x e = true) (h2 : anpKey5_pend S y e = true) : x = y := by
  simp only [anpKey5_pend, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1 h2
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · rw [a1] at b1; exact Sum.inr_injective b1
  · rw [b1, anpKey5_inS_inr] at a2; simp [hy] at a2
  · rw [b1, anpKey5_inS_inr] at a2; simp [hy] at a2
  · rw [a1] at b1; exact Sum.inr_injective b1

/-- A pendant edge (one end outside `R`) is no edge between two subsets of `R`. -/
theorem anpKey5_pend_not_cut {R S₁ S₂ : Finset (Fin q)} (h1 : S₁ ⊆ R) (h2 : S₂ ⊆ R) {v : Fin q}
    {e : NV p q × NV p q} (he : anpKey5_pend R v e = true) :
    ((anpKey5_inS S₁ e.1 && anpKey5_inS S₂ e.2) || (anpKey5_inS S₂ e.1 && anpKey5_inS S₁ e.2)) = false := by
  have key : ∀ w : NV p q, anpKey5_inS R w = false → anpKey5_inS S₁ w = false ∧ anpKey5_inS S₂ w = false := by
    intro w hw
    constructor
    · by_contra hc; rw [Bool.not_eq_false] at hc; rw [anpKey5_inS_mono h1 w hc] at hw; exact Bool.noConfusion hw
    · by_contra hc; rw [Bool.not_eq_false] at hc; rw [anpKey5_inS_mono h2 w hc] at hw; exact Bool.noConfusion hw
  simp only [anpKey5_pend, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at he
  rcases he with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨k1, k2⟩ := key _ h
    simp [k1, k2]
  · obtain ⟨k1, k2⟩ := key _ h
    simp [k1, k2]

/-- A pendant edge of `α_v` is not an edge at `α_v` whose other end lies in `W ⊆ R`. -/
theorem anpKey5_pend_conflict {R W : Finset (Fin q)} (hW : W ⊆ R) {v : Fin q} (hv : v ∈ R)
    {e : NV p q × NV p q} (he : anpKey5_pend R v e = true)
    (h : ((decide (e.1 = Sum.inr v) && anpKey5_inS W e.2) || (decide (e.2 = Sum.inr v) && anpKey5_inS W e.1)) = true) :
    False := by
  simp only [anpKey5_pend, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at he h
  rcases he with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · rw [anpKey5_inS_mono hW _ b2] at a2; exact Bool.noConfusion a2
  · rw [b1, anpKey5_inS_inr] at a2; simp [hv] at a2
  · rw [b1, anpKey5_inS_inr] at a2; simp [hv] at a2
  · rw [anpKey5_inS_mono hW _ b2] at a2; exact Bool.noConfusion a2

theorem anpKey5_get_set_ne {α : Type*} (E : List α) (i j : Fin E.length) (a : α) (h : i ≠ j) :
    (E.set j.1 a).get (i.cast (by simp)) = E.get i := by
  have hne : j.1 ≠ i.1 := fun h' => h (Fin.ext h'.symm)
  simp [List.get_eq_getElem, List.getElem_set_ne hne]

theorem anpKey5_get_set_self {α : Type*} (E : List α) (j : Fin E.length) (a : α) :
    (E.set j.1 a).get (j.cast (by simp)) = a := by
  simp [List.get_eq_getElem]

/-- The two bounds of `AnpKey5GraphPin` at `S`. -/
def anpKey5_ok (E : List (NV p q × NV p q)) (S : Finset (Fin q)) : Prop :=
  S.card ≤ anpKey5_cross E S ∧ ((∀ v ∈ S, anpKey5_crossAt E S v ≤ 1) → S.card ≤ anpKey5_inside E S)

theorem anpKey5_untouched_pend {S : Finset (Fin q)} {v : Fin q} (hv : v ∈ S) {e : NV p q × NV p q}
    (h : anpKey5_inS S e.1 = false ∧ anpKey5_inS S e.2 = false) : anpKey5_pend S v e = false := by
  obtain ⟨h1, h2⟩ := h
  have a1 : decide (e.1 = Sum.inr v) = false := by
    simp only [decide_eq_false_iff_not]
    intro heq; rw [heq, anpKey5_inS_inr] at h1; simp [hv] at h1
  have a2 : decide (e.2 = Sum.inr v) = false := by
    simp only [decide_eq_false_iff_not]
    intro heq; rw [heq, anpKey5_inS_inr] at h2; simp [hv] at h2
  simp [anpKey5_pend, a1, a2]

theorem anpKey5_cross_pred_false {S : Finset (Fin q)} {e : NV p q × NV p q}
    (h : anpKey5_inS S e.1 = false ∧ anpKey5_inS S e.2 = false) :
    (anpKey5_inS S e.1 != anpKey5_inS S e.2) = false := by
  rw [h.1, h.2]; rfl

theorem anpKey5_inside_pred_false {S : Finset (Fin q)} {e : NV p q × NV p q}
    (h : anpKey5_inS S e.1 = false ∧ anpKey5_inS S e.2 = false) :
    (anpKey5_inS S e.1 && anpKey5_inS S e.2) = false := by
  rw [h.1, h.2]; rfl

/-- Replacing an edge that does not touch `S` by one that does not touch `S` keeps both bounds at `S`. -/
theorem anpKey5_ok_set {E : List (NV p q × NV p q)} {S : Finset (Fin q)} (k : Fin E.length)
    (e' : NV p q × NV p q) (hk : anpKey5_inS S (E.get k).1 = false ∧ anpKey5_inS S (E.get k).2 = false)
    (he : anpKey5_inS S e'.1 = false ∧ anpKey5_inS S e'.2 = false) (h : anpKey5_ok E S) :
    anpKey5_ok (E.set k.1 e') S := by
  have c1 : anpKey5_cross (E.set k.1 e') S = anpKey5_cross E S :=
    anpKey5_countP_set _ E k e' (anpKey5_cross_pred_false hk) (anpKey5_cross_pred_false he)
  have c2 : anpKey5_inside (E.set k.1 e') S = anpKey5_inside E S :=
    anpKey5_countP_set _ E k e' (anpKey5_inside_pred_false hk) (anpKey5_inside_pred_false he)
  have c3 : ∀ v ∈ S, anpKey5_crossAt (E.set k.1 e') S v = anpKey5_crossAt E S v := fun v hv =>
    anpKey5_countP_set (anpKey5_pend S v) E k e' (anpKey5_untouched_pend hv hk) (anpKey5_untouched_pend hv he)
  refine ⟨by rw [c1]; exact h.1, fun hall => ?_⟩
  rw [c2]
  exact h.2 fun v hv => by rw [← c3 v hv]; exact hall v hv

theorem anpKey5_cross_le_sum (E : List (NV p q × NV p q)) (S : Finset (Fin q)) :
    anpKey5_cross E S ≤ ∑ v ∈ S, anpKey5_crossAt E S v := by
  unfold anpKey5_cross
  simp only [anpKey5_crossAt_eq]
  apply anpKey5_countP_le_sum
  intro e _ he
  cases h1 : anpKey5_inS S e.1 <;> cases h2 : anpKey5_inS S e.2
  · simp [h1, h2] at he
  · obtain ⟨v, hv1, hv2⟩ := anpKey5_inS_true h2
    exact ⟨v, hv2, by simp [anpKey5_pend, hv1, h1]⟩
  · obtain ⟨v, hv1, hv2⟩ := anpKey5_inS_true h1
    exact ⟨v, hv2, by simp [anpKey5_pend, hv1, h2]⟩
  · simp [h1, h2] at he

/-- The AM-GM branch (`7_8:1428-1451`, the re-rooting): in the list with the pendant edge `k'` of `y` replaced by a
copy of the pendant edge `k` of `x`, the vertex `x` joins the order, and the greedy extension then reaches every vertex
of the minimal closed set `U` (a stuck part `T` of `U` has at most one edge to `U \ T`, at `y`, contradicting `hconn`
and `hsep`). -/
theorem anpKey5_branch (E : List (NV p q × NV p q)) (σ : List (Fin q)) (U : Finset (Fin q))
    (hv : anpKey5_valid E σ) (hUR : U ⊆ anpKey5_comp σ)
    (hpend : ∀ v ∈ U, ∃ i : Fin E.length, anpKey5_pend (anpKey5_comp σ) v (E.get i) = true)
    (hconn : ∀ T ⊆ U, T.Nonempty → T ≠ U → 1 ≤ anpKey5_cut E T U)
    (x y : Fin q) (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y)
    (hsep : ∀ T ⊆ U, (x ∈ T ↔ y ∉ T) → 2 ≤ anpKey5_cut E T U)
    (k k' : Fin E.length) (hk : anpKey5_pend (anpKey5_comp σ) x (E.get k) = true)
    (hk' : anpKey5_pend (anpKey5_comp σ) y (E.get k') = true) :
    ∃ σ₁ : List (Fin q), anpKey5_valid (E.set k'.1 (E.get k)) σ₁ ∧
      anpKey5_comp σ₁ ⊆ anpKey5_comp σ \ U := by
  have hkk : k ≠ k' := by
    intro h; subst h; exact hxy (anpKey5_pend_unique (hUR hy) hk hk')
  have hv₁ : anpKey5_valid (E.set k'.1 (E.get k)) σ :=
    anpKey5_valid_set hv k' (E.get k) (anpKey5_pend_inS (hUR hy) hk') (anpKey5_pend_inS (hUR hx) hk)
  have hxσ : x ∉ σ := anpKey5_mem_comp.1 (hUR hx)
  have h2 : 2 ≤ anpKey5_crossAt (E.set k'.1 (E.get k)) (anpKey5_comp σ) x := by
    rw [anpKey5_crossAt_eq]
    refine anpKey5_two_le_countP _ _ (k.cast (by simp)) (k'.cast (by simp)) ?_ ?_ ?_
    · intro h; exact hkk (Fin.cast_injective _ h)
    · rw [anpKey5_get_set_ne E k k' _ hkk]; exact hk
    · rw [anpKey5_get_set_self]; exact hk
  have hv₂ := anpKey5_valid_append hv₁ hxσ h2
  obtain ⟨σ₁, hval₁, hsub₁, hstuck₁⟩ :=
    anpKey5_greedy (E.set k'.1 (E.get k)) _ (σ ++ [x]) le_rfl hv₂
  refine ⟨σ₁, hval₁, ?_⟩
  intro z hz
  have hzσ : z ∉ σ₁ := anpKey5_mem_comp.1 hz
  have hzR : z ∈ anpKey5_comp σ :=
    anpKey5_mem_comp.2 (fun h => hzσ (hsub₁ z (List.mem_append_left _ h)))
  refine Finset.mem_sdiff.2 ⟨hzR, fun hzU => ?_⟩
  set R₁ := anpKey5_comp σ₁ with hR₁
  set T := U ∩ R₁ with hT
  have hTne : T.Nonempty := ⟨z, Finset.mem_inter.2 ⟨hzU, hz⟩⟩
  have hTU : T ⊆ U := Finset.inter_subset_left
  have hR₁R : R₁ ⊆ anpKey5_comp σ := fun i hi =>
    anpKey5_mem_comp.2 (fun h => (anpKey5_mem_comp.1 hi) (hsub₁ i (List.mem_append_left _ h)))
  have hxT : x ∉ T := fun h => (anpKey5_mem_comp.1 (Finset.mem_inter.1 h).2) (hsub₁ x (by simp))
  have hTne' : T ≠ U := fun h => hxT (by rw [h]; exact hx)
  have hWsub : U \ T ⊆ anpKey5_comp σ := Finset.sdiff_subset.trans hUR
  have hcutE : anpKey5_cut E T U = anpKey5_cut (E.set k'.1 (E.get k)) T U := by
    unfold anpKey5_cut
    exact (anpKey5_countP_set _ E k' (E.get k)
      (anpKey5_pend_not_cut (hTU.trans hUR) hWsub hk') (anpKey5_pend_not_cut (hTU.trans hUR) hWsub hk)).symm
  have hW : ∀ w : NV p q, anpKey5_inS (U \ T) w = true → anpKey5_inS R₁ w = false := by
    intro w hw
    rw [anpKey5_inS_sdiff, hT, anpKey5_inS_inter] at hw
    revert hw
    cases anpKey5_inS U w <;> cases anpKey5_inS R₁ w <;> simp
  have h_pend : ∀ (v : Fin q) (e : NV p q × NV p q),
      ((decide (e.1 = Sum.inr v) && anpKey5_inS (U \ T) e.2) ||
        (decide (e.2 = Sum.inr v) && anpKey5_inS (U \ T) e.1)) = true → anpKey5_pend R₁ v e = true := by
    intro v e he
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at he
    simp only [anpKey5_pend, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, hW _ h2⟩
    · exact Or.inr ⟨h1, hW _ h2⟩
  have hbound : anpKey5_cut (E.set k'.1 (E.get k)) T U ≤ ∑ v ∈ T, if v = y then 1 else 0 := by
    unfold anpKey5_cut
    refine le_trans (anpKey5_countP_le_sum T _ (fun v e => (decide (e.1 = Sum.inr v) &&
      anpKey5_inS (U \ T) e.2) || (decide (e.2 = Sum.inr v) && anpKey5_inS (U \ T) e.1)) _ ?_) ?_
    · intro e _ he
      simp only [Bool.or_eq_true, Bool.and_eq_true] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨v, hv1, hv2⟩ := anpKey5_inS_true h1
        exact ⟨v, hv2, by simp [hv1, h2]⟩
      · obtain ⟨v, hv1, hv2⟩ := anpKey5_inS_true h2
        exact ⟨v, hv2, by simp [hv1, h1]⟩
    · apply Finset.sum_le_sum
      intro v hvT
      have hvU : v ∈ U := hTU hvT
      have hvR₁ : v ∈ R₁ := (Finset.mem_inter.1 hvT).2
      have hle1 : (E.set k'.1 (E.get k)).countP (fun e => (decide (e.1 = Sum.inr v) &&
          anpKey5_inS (U \ T) e.2) || (decide (e.2 = Sum.inr v) && anpKey5_inS (U \ T) e.1)) ≤ 1 := by
        calc _ ≤ anpKey5_crossAt (E.set k'.1 (E.get k)) R₁ v := by
              rw [anpKey5_crossAt_eq]
              exact List.countP_mono_left fun e _ he => h_pend v e he
          _ ≤ 1 := hstuck₁ v hvR₁
      by_cases hvy : v = y
      · simp only [hvy, ↓reduceIte] at hle1 ⊢
        exact hle1
      · simp only [hvy, ↓reduceIte]
        by_contra hpos
        have hpos' := not_le.1 hpos
        obtain ⟨e, he, hpe⟩ := List.countP_pos_iff.1 hpos'
        obtain ⟨i, rfl⟩ := List.mem_iff_get.1 he
        obtain ⟨kv, hkv⟩ := hpend v hvU
        have hkvk' : kv ≠ k' := by
          intro h; subst h; exact hvy (anpKey5_pend_unique (hUR hy) hkv hk')
        have hkv1 : (E.set k'.1 (E.get k)).get (kv.cast (by simp)) = E.get kv :=
          anpKey5_get_set_ne E kv k' _ hkvk'
        have hne : i ≠ kv.cast (by simp) := by
          intro h
          rw [h, hkv1] at hpe
          exact anpKey5_pend_conflict hWsub (hUR hvU) hkv hpe
        have h2' : 2 ≤ anpKey5_crossAt (E.set k'.1 (E.get k)) R₁ v := by
          rw [anpKey5_crossAt_eq]
          refine anpKey5_two_le_countP _ _ i (kv.cast (by simp)) hne (h_pend v _ hpe) ?_
          rw [hkv1]; exact anpKey5_pend_mono hR₁R hkv
        have := hstuck₁ v hvR₁
        omega
  rw [Finset.sum_ite_eq' T y (fun _ => 1)] at hbound
  by_cases hyT : y ∈ T
  · have h3 := hsep T hTU ⟨fun h => absurd h hxT, fun h => absurd hyT h⟩
    simp only [hyT, ↓reduceIte] at hbound
    omega
  · have h3 := hconn T hTU hTne hTne'
    simp only [hyT, ↓reduceIte] at hbound
    omega

theorem anpKey5_cert_mono : ∀ (n : ℕ) (E : List (NV p q × NV p q)), AnpSumCert n E → AnpSumCert (n + 1) E := by
  intro n
  induction n with
  | zero => intro E h; exact Or.inl h
  | succ n ih =>
    intro E h
    rcases h with h | ⟨k, k', hkk, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, k', hkk, ih _ h1, ih _ h2⟩

theorem anpKey5_cert_mono_le {n m : ℕ} (hnm : n ≤ m) {E : List (NV p q × NV p q)} (h : AnpSumCert n E) :
    AnpSumCert m E := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact anpKey5_cert_mono m E ih

theorem anpKey5_countP_le_add2 {α : Type*} (l : List α) (P Q R : α → Bool)
    (h : ∀ e ∈ l, (if P e = true then 1 else 0 : ℕ) ≤ (if Q e = true then 1 else 0) + (if R e = true then 1 else 0)) :
    l.countP P ≤ l.countP Q + l.countP R := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih fun e he => h e (List.mem_cons_of_mem _ he)
    have ha := h a List.mem_cons_self
    simp only [List.countP_cons]
    omega

theorem anpKey5_pw_cuttrans : ∀ t1 t2 u1 u2 r1 r2 : Bool, (t1 = true → u1 = true) → (t2 = true → u2 = true) →
    (u1 = true → r1 = true) → (u2 = true → r2 = true) →
    (if ((t1 && (r2 && !t2)) || ((r1 && !t1) && t2)) = true then 1 else 0 : ℕ) ≤
      (if ((t1 && (u2 && !t2)) || ((u1 && !t1) && t2)) = true then 1 else 0) +
      (if ((u1 && (r2 && !u2)) || ((r1 && !u1) && u2)) = true then 1 else 0) := by
  decide

theorem anpKey5_cut_trans (E : List (NV p q × NV p q)) {T U R : Finset (Fin q)} (hTU : T ⊆ U) (hUR : U ⊆ R) :
    anpKey5_cut E T R ≤ anpKey5_cut E T U + anpKey5_cut E U R := by
  unfold anpKey5_cut
  apply anpKey5_countP_le_add2
  intro e _
  simp only [anpKey5_inS_sdiff]
  exact anpKey5_pw_cuttrans _ _ _ _ _ _ (fun h => anpKey5_inS_mono hTU _ h) (fun h => anpKey5_inS_mono hTU _ h)
    (fun h => anpKey5_inS_mono hUR _ h) (fun h => anpKey5_inS_mono hUR _ h)

theorem anpKey5_inS_empty (w : NV p q) : anpKey5_inS (∅ : Finset (Fin q)) w = false := by
  rcases w with x | i <;> simp [anpKey5_inS]

theorem anpKey5_cut_self (E : List (NV p q × NV p q)) (R : Finset (Fin q)) : anpKey5_cut E R R = 0 := by
  unfold anpKey5_cut
  apply List.countP_eq_zero.2
  intro e _
  simp [anpKey5_inS_empty]

theorem anpKey5_pw_closed : ∀ i1 i2 u1 u2 r1 r2 : Bool, (i1 = true → u1 = true) → (i2 = true → u2 = true) →
    (u1 = true → r1 = true) → (u2 = true → r2 = true) →
    ((u1 && (r2 && !u2)) || ((r1 && !u1) && u2)) = false →
    ((i1 && !u2) || (i2 && !u1)) = ((i1 && !r2) || (i2 && !r1)) := by
  decide

/-- For a closed `U ⊆ R` (no edge between `U` and `R \ U`), the edges at `v ∈ U` leaving `U` are those leaving `R`. -/
theorem anpKey5_crossAt_closed (E : List (NV p q × NV p q)) {U R : Finset (Fin q)} (hUR : U ⊆ R)
    (hcl : anpKey5_cut E U R = 0) {v : Fin q} (hv : v ∈ U) :
    anpKey5_crossAt E U v = anpKey5_crossAt E R v := by
  have hcl' := List.countP_eq_zero.1 hcl
  unfold anpKey5_crossAt
  apply List.countP_congr
  intro e he
  have hc := hcl' e he
  simp only [anpKey5_inS_sdiff, Bool.not_eq_true] at hc
  have hi1 : decide (e.1 = Sum.inr v) = true → anpKey5_inS U e.1 = true := by
    intro h; simp only [decide_eq_true_eq] at h; rw [h, anpKey5_inS_inr]; simpa using hv
  have hi2 : decide (e.2 = Sum.inr v) = true → anpKey5_inS U e.2 = true := by
    intro h; simp only [decide_eq_true_eq] at h; rw [h, anpKey5_inS_inr]; simpa using hv
  have := anpKey5_pw_closed _ _ _ _ _ _ hi1 hi2 (fun h => anpKey5_inS_mono hUR _ h)
    (fun h => anpKey5_inS_mono hUR _ h) hc
  rw [this]

theorem anpKey5_pend_untouched {R S : Finset (Fin q)} (hSR : S ⊆ R) {y : Fin q} (hy : y ∉ S)
    {e : NV p q × NV p q} (h : anpKey5_pend R y e = true) :
    anpKey5_inS S e.1 = false ∧ anpKey5_inS S e.2 = false := by
  have key : ∀ w : NV p q, anpKey5_inS R w = false → anpKey5_inS S w = false := by
    intro w hw
    by_contra hc; rw [Bool.not_eq_false] at hc; rw [anpKey5_inS_mono hSR w hc] at hw; exact Bool.noConfusion hw
  simp only [anpKey5_pend, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨?_, key _ h2⟩
    rw [h1, anpKey5_inS_inr]; simpa using hy
  · refine ⟨key _ h2, ?_⟩
    rw [h1, anpKey5_inS_inr]; simpa using hy

/-- The induction on the unlisted vertices (`7_8:1414-1451`): a valid prefix `σ` with the two bounds on every subset
of the unlisted vertices extends to a certificate. -/
theorem anpKey5_main : ∀ (n : ℕ) (E : List (NV p q × NV p q)), (∀ e ∈ E, e.1 ≠ e.2) →
    ∀ σ : List (Fin q), (anpKey5_comp σ).card = n → anpKey5_valid E σ →
      (∀ S ⊆ anpKey5_comp σ, anpKey5_ok E S) → ∃ m, AnpSumCert m E := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hloop σ hn hv hok
  obtain ⟨σ', hv', hsub', hstuck'⟩ := anpKey5_greedy E _ σ le_rfl hv
  set R := anpKey5_comp σ' with hR
  have hRσ : R ⊆ anpKey5_comp σ := fun i hi =>
    anpKey5_mem_comp.2 (fun h => (anpKey5_mem_comp.1 hi) (hsub' i h))
  by_cases hRe : R = ∅
  · refine ⟨0, σ', anpKey5_sumOrder_of_valid hv' ?_⟩
    intro i
    by_contra hi
    have : i ∈ R := anpKey5_mem_comp.2 hi
    rw [hRe] at this
    simp at this
  · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.2 hRe
    -- a minimal nonempty closed subset `U` of the stuck set
    obtain ⟨U, hUF, hUmin⟩ := Finset.exists_min_image
      (R.powerset.filter fun U => U.Nonempty ∧ anpKey5_cut E U R = 0) Finset.card
      ⟨R, by simp [hRne, anpKey5_cut_self]⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at hUF hUmin
    obtain ⟨hUR, hUne, hUcl⟩ := hUF
    have hUR' : U ⊆ anpKey5_comp σ' := hUR
    have hconn : ∀ T ⊆ U, T.Nonempty → T ≠ U → 1 ≤ anpKey5_cut E T U := by
      intro T hTU hTne hTU'
      by_contra hc
      have h0 : anpKey5_cut E T U = 0 := by omega
      have hcR : anpKey5_cut E T R = 0 := by
        have := anpKey5_cut_trans E hTU hUR
        omega
      have hmin := hUmin T ⟨hTU.trans hUR, hTne, hcR⟩
      have hlt : T.card < U.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hTU, hTU'⟩)
      omega
    have hokU := hok U (hUR.trans hRσ)
    have hcrossle : ∀ v ∈ U, anpKey5_crossAt E U v ≤ 1 := fun v hv => by
      rw [anpKey5_crossAt_closed E hUR hUcl hv]; exact hstuck' v (hUR hv)
    have hpos : ∀ v ∈ U, 1 ≤ anpKey5_crossAt E U v := by
      intro v₀ hv₀
      by_contra hlt
      have h0 : anpKey5_crossAt E U v₀ < 1 := by omega
      have hs : ∑ v ∈ U, anpKey5_crossAt E U v < ∑ v ∈ U, 1 :=
        Finset.sum_lt_sum hcrossle ⟨v₀, hv₀, h0⟩
      have h1 := hokU.1
      have h2 := anpKey5_cross_le_sum E U
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
      omega
    have hpend : ∀ v ∈ U, ∃ i : Fin E.length, anpKey5_pend R v (E.get i) = true := by
      intro v hv
      have h1 := hpos v hv
      rw [anpKey5_crossAt_closed E hUR hUcl hv, anpKey5_crossAt_eq] at h1
      obtain ⟨e, he, hpe⟩ := List.countP_pos_iff.1 (by omega : 0 < E.countP (anpKey5_pend R v))
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 he
      exact ⟨i, hpe⟩
    have hin : U.card ≤ anpKey5_inside E U := hokU.2 hcrossle
    obtain ⟨x, y, hx, hy, hxy, hsep⟩ := anpKey5_nb E hloop U hUne hin
    obtain ⟨k, hk⟩ := hpend x hx
    obtain ⟨k', hk'⟩ := hpend y hy
    have hkk : k ≠ k' := by
      intro h; subst h; exact hxy (anpKey5_pend_unique (hUR hy) hk hk')
    -- both branches
    have hbranch : ∀ (x y : Fin q), x ∈ U → y ∈ U → x ≠ y →
        (∀ T ⊆ U, (x ∈ T ↔ y ∉ T) → 2 ≤ anpKey5_cut E T U) → ∀ k k' : Fin E.length,
        anpKey5_pend R x (E.get k) = true → anpKey5_pend R y (E.get k') = true →
        ∃ m, AnpSumCert m (E.set k'.1 (E.get k)) := by
      intro x y hx hy hxy hsep k k' hk hk'
      obtain ⟨σ₁, hval₁, hsub₁⟩ := anpKey5_branch E σ' U hv' hUR' hpend hconn x y hx hy hxy hsep k k' hk hk'
      have hlt : (anpKey5_comp σ₁).card < n := by
        have h1 : (anpKey5_comp σ₁).card ≤ (R \ U).card := Finset.card_le_card hsub₁
        have h2 : (R \ U).card < R.card := Finset.card_lt_card (Finset.sdiff_ssubset hUR hUne)
        have h3 : R.card ≤ (anpKey5_comp σ).card := Finset.card_le_card hRσ
        omega
      have hloop₁ : ∀ e ∈ E.set k'.1 (E.get k), e.1 ≠ e.2 := by
        intro e he
        rcases List.mem_or_eq_of_mem_set he with h | h
        · exact hloop e h
        · rw [h]; exact hloop _ (List.get_mem E k)
      have hok₁ : ∀ S ⊆ anpKey5_comp σ₁, anpKey5_ok (E.set k'.1 (E.get k)) S := by
        intro S hS
        have hSRU : S ⊆ R \ U := hS.trans hsub₁
        have hSR : S ⊆ R := hSRU.trans Finset.sdiff_subset
        have hSU : ∀ v ∈ U, v ∉ S := fun v hv hvS => (Finset.mem_sdiff.1 (hSRU hvS)).2 hv
        exact anpKey5_ok_set k' (E.get k) (anpKey5_pend_untouched hSR (hSU y hy) hk')
          (anpKey5_pend_untouched hSR (hSU x hx) hk) (hok S (hSR.trans hRσ))
      exact ih _ hlt _ hloop₁ σ₁ rfl hval₁ hok₁
    obtain ⟨m₁, hm₁⟩ := hbranch x y hx hy hxy hsep k k' hk hk'
    obtain ⟨m₂, hm₂⟩ := hbranch y x hy hx hxy.symm
      (fun T hT h => hsep T hT (by tauto)) k' k hk' hk
    exact ⟨max m₁ m₂ + 1, Or.inr ⟨k, k', hkk, anpKey5_cert_mono_le (le_max_left _ _) hm₁,
      anpKey5_cert_mono_le (le_max_right _ _) hm₂⟩⟩

/-- `AnpKey5GraphPin` (the spanning tree and its re-rooting, `7_8:1414-1451`, as a statement on multigraphs): no
loops, the crossing bound for every `S` and the inside bound for every `S` whose vertices have at most one leaving
edge give a certificate. -/
theorem anpKey5_graph : ∀ (p q : ℕ) (E : List (NV p q × NV p q)), (∀ e ∈ E, e.1 ≠ e.2) →
    (∀ S : Finset (Fin q), S.card ≤ anpKey5_cross E S) →
    (∀ S : Finset (Fin q), (∀ v ∈ S, anpKey5_crossAt E S v ≤ 1) → S.card ≤ anpKey5_inside E S) →
    ∃ n : ℕ, AnpSumCert n E := by
  intro p q E hloop h1 h2
  exact anpKey5_main _ E hloop [] rfl (anpKey5_valid_nil E) (fun S _ => ⟨h1 S, h2 S⟩)

end Graph


/-! ## 6. Walks of a nested graph: the crossing and inside bounds -/

section Walk

variable {p q : ℕ}

theorem anpKey5_step_cross (Γ : NGraph p q) (f : NV p q → Bool) {x : NV p q}
    {st : Fin Γ.es.length × NV p q}
    (hs : ((Γ.es.get st.1).u = x ∧ (Γ.es.get st.1).v = st.2) ∨ ((Γ.es.get st.1).v = x ∧ (Γ.es.get st.1).u = st.2)) :
    (f (Γ.es.get st.1).u != f (Γ.es.get st.1).v) = (f x != f st.2) := by
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; cases f x <;> cases f st.2 <;> rfl

/-- A walk between vertices with different values of `f` has a step whose edge has different values at its ends. -/
theorem anpKey5_walk_one (Γ : NGraph p q) (f : NV p q → Bool) :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q), anpKey2_chain Γ x l y → f x ≠ f y →
      1 ≤ l.countP fun st => f (Γ.es.get st.1).u != f (Γ.es.get st.1).v := by
  intro l
  induction l with
  | nil => intro x y h hne; exact absurd (congrArg f h) hne
  | cons st t ih =>
    intro x y h hne
    obtain ⟨hs, hrest⟩ := h
    simp only [List.countP_cons, anpKey5_step_cross Γ f hs]
    by_cases hc : f x = f st.2
    · have := ih st.2 y hrest (by rw [← hc]; exact hne)
      simp only [hc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      omega
    · have : (f x != f st.2) = true := by simpa using hc
      simp [this]

/-- A walk from `x` to `y` with `f x = f y` that reaches a vertex with another value of `f` crosses twice. -/
theorem anpKey5_walk_two (Γ : NGraph p q) (f : NV p q → Bool) :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q), anpKey2_chain Γ x l y → f x = f y →
      (∃ st ∈ l, f st.2 ≠ f x) →
      2 ≤ l.countP fun st => f (Γ.es.get st.1).u != f (Γ.es.get st.1).v := by
  intro l
  induction l with
  | nil => intro x y _ _ ⟨st, hst, _⟩; simp at hst
  | cons st t ih =>
    intro x y h hxy ⟨st', hst', hne'⟩
    obtain ⟨hs, hrest⟩ := h
    simp only [List.countP_cons, anpKey5_step_cross Γ f hs]
    by_cases hc : f x = f st.2
    · have hwit : ∃ s ∈ t, f s.2 ≠ f st.2 := by
        rcases List.mem_cons.1 hst' with rfl | hmem
        · exact absurd hc.symm hne'
        · exact ⟨st', hmem, by rw [← hc]; exact hne'⟩
      have := ih st.2 y hrest (by rw [← hc]; exact hxy) hwit
      simp only [hc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      omega
    · have h1 : (f x != f st.2) = true := by simpa using hc
      have h2 := anpKey5_walk_one Γ f t st.2 y hrest (by rw [← hxy]; exact fun h => hc h.symm)
      simp only [h1, ↓reduceIte]
      omega

theorem anpKey5_path_sum {n : ℕ} {β : Type*} (L : List (Fin n × β)) (hnd : (L.map Prod.fst).Nodup)
    (g : Fin n → Bool) :
    L.countP (fun st => g st.1) = ∑ k ∈ (L.map Prod.fst).toFinset, if g k = true then 1 else 0 := by
  induction L with
  | nil => simp
  | cons st t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.countP_cons, List.map_cons, List.toFinset_cons, Finset.sum_insert (by simpa using hnd.1),
      ih hnd.2]
    omega

end Walk

section Paths

variable {p q : ℕ}

/-- The edge indices of the path `j`. -/
def anpKey5_eidx (Γ : NGraph p q) (j : Fin p) : Finset (Fin Γ.es.length) :=
  ((Γ.path j).map Prod.fst).toFinset

/-- `1` on the edges kept in `anpKey5_rest`, `0` on ghost edges and on `M`. -/
def anpKey5_gd (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (k : Fin Γ.es.length) : ℕ :=
  if (Γ.es.get k).ghost = false ∧ k ∉ M then 1 else 0

/-- `1` on the ghost edges and on `M`. -/
def anpKey5_rm (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (k : Fin Γ.es.length) : ℕ :=
  if (Γ.es.get k).ghost = true ∨ k ∈ M then 1 else 0

/-- `1` on the edges with exactly one end in `S`. -/
def anpKey5_cr (Γ : NGraph p q) (S : Finset (Fin q)) (k : Fin Γ.es.length) : ℕ :=
  if (anpKey5_inS S (Γ.es.get k).u != anpKey5_inS S (Γ.es.get k).v) = true then 1 else 0

/-- `1` on the edges with both ends in `S`. -/
def anpKey5_ins (Γ : NGraph p q) (S : Finset (Fin q)) (k : Fin Γ.es.length) : ℕ :=
  if (anpKey5_inS S (Γ.es.get k).u && anpKey5_inS S (Γ.es.get k).v) = true then 1 else 0

theorem anpKey5_gd_add_rm (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (k : Fin Γ.es.length) :
    anpKey5_gd Γ M k + anpKey5_rm Γ M k = 1 := by
  unfold anpKey5_gd anpKey5_rm
  by_cases h : (Γ.es.get k).ghost = true ∨ k ∈ M
  · have : ¬ ((Γ.es.get k).ghost = false ∧ k ∉ M) := by
      rintro ⟨h1, h2⟩
      rcases h with h | h
      · rw [h1] at h; exact Bool.noConfusion h
      · exact h2 h
    rw [anpKey5_ite_neg this, anpKey5_ite_pos h]
  · have : ((Γ.es.get k).ghost = false ∧ k ∉ M) := by
      rw [not_or] at h
      exact ⟨by simpa using h.1, h.2⟩
    rw [anpKey5_ite_pos this, anpKey5_ite_neg h]

theorem anpKey5_cr_add_ins_le (Γ : NGraph p q) (S : Finset (Fin q)) (k : Fin Γ.es.length) :
    anpKey5_cr Γ S k + anpKey5_ins Γ S k ≤ 1 := by
  unfold anpKey5_cr anpKey5_ins
  cases anpKey5_inS S (Γ.es.get k).u <;> cases anpKey5_inS S (Γ.es.get k).v <;> simp

theorem anpKey5_cr_two_ins (Γ : NGraph p q) (S : Finset (Fin q)) (k : Fin Γ.es.length) :
    anpKey5_cr Γ S k + 2 * anpKey5_ins Γ S k =
      (anpKey5_inS S (Γ.es.get k).u).toNat + (anpKey5_inS S (Γ.es.get k).v).toNat := by
  unfold anpKey5_cr anpKey5_ins
  cases anpKey5_inS S (Γ.es.get k).u <;> cases anpKey5_inS S (Γ.es.get k).v <;> simp

theorem anpKey5_ite_and (a b : Prop) [Decidable a] [Decidable b] :
    (if a ∧ b then 1 else 0 : ℕ) = (if a then 1 else 0) * (if b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem anpKey5_rest_cross (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (S : Finset (Fin q)) :
    anpKey5_cross (anpKey5_rest Γ M) S = ∑ k, anpKey5_gd Γ M k * anpKey5_cr Γ S k := by
  unfold anpKey5_cross
  rw [anpKey5_rest_countP]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold anpKey5_gd anpKey5_cr
  exact anpKey5_ite_and _ _

theorem anpKey5_rest_inside (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (S : Finset (Fin q)) :
    anpKey5_inside (anpKey5_rest Γ M) S = ∑ k, anpKey5_gd Γ M k * anpKey5_ins Γ S k := by
  unfold anpKey5_inside
  rw [anpKey5_rest_countP]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold anpKey5_gd anpKey5_ins
  exact anpKey5_ite_and _ _

theorem anpKey5_sum_eq_inS (S : Finset (Fin q)) (w : NV p q) :
    ∑ α ∈ S, (if w = Sum.inr α then 1 else 0 : ℕ) = (anpKey5_inS S w).toNat := by
  rcases w with x | i
  · simp [anpKey5_inS_inl]
  · simp only [anpKey5_inS_inr, Sum.inr.injEq, Finset.sum_ite_eq]
    by_cases h : i ∈ S <;> simp [h]

/-- A path visiting `S` has at least two edges with exactly one end in `S` (first entry, last exit). -/
theorem anpKey5_pl1 (Γ : NGraph p q) (hN : Γ.IsNested) (S : Finset (Fin q)) (j : Fin p)
    (hj : ∃ α ∈ S, Γ.Visits j (Sum.inr α)) : 2 ≤ ∑ k ∈ anpKey5_eidx Γ j, anpKey5_cr Γ S k := by
  obtain ⟨α, hα, hvis⟩ := hj
  have hchain := (anpKey2_walkOK_iff Γ j).1 (hN.2.1 j)
  have hnd := hN.2.2.1 j
  obtain ⟨st, hst, hu⟩ := anpKey2_chain_visit Γ (Sum.inr α) (Γ.path j) _ _ hchain (by simp) hvis
  have h2 := anpKey5_walk_two Γ (anpKey5_inS S) (Γ.path j) _ _ hchain (by simp [anpKey5_inS_inl])
    ⟨st, hst, by rw [hu, anpKey5_inS_inr]; simp [hα, anpKey5_inS_inl]⟩
  have key := anpKey5_path_sum (Γ.path j) hnd
    (fun k => anpKey5_inS S (Γ.es.get k).u != anpKey5_inS S (Γ.es.get k).v)
  unfold anpKey5_eidx anpKey5_cr
  rw [← key]
  exact h2

theorem anpKey5_or_le (a b : NV p q) (α : Fin q) :
    (if (decide (a = Sum.inr α) || decide (b = Sum.inr α)) = true then 1 else 0 : ℕ) ≤
      (if a = Sum.inr α then 1 else 0) + (if b = Sum.inr α then 1 else 0) := by
  by_cases h1 : a = Sum.inr α <;> by_cases h2 : b = Sum.inr α <;> simp [h1, h2]

/-- A path visiting `α ∈ S` has at least two edges at `α`: `2 ·` (the number of visited vertices of `S`) is at most
the number of edge-ends in `S` along the path (`cr + 2 · ins`). -/
theorem anpKey5_pl2 (Γ : NGraph p q) (hN : Γ.IsNested) (S : Finset (Fin q)) (j : Fin p) :
    2 * ∑ α ∈ S, (if Γ.Visits j (Sum.inr α) then 1 else 0) ≤
      ∑ k ∈ anpKey5_eidx Γ j, (anpKey5_cr Γ S k + 2 * anpKey5_ins Γ S k) := by
  have hpt : ∀ k : Fin Γ.es.length, ∑ α ∈ S, (if (decide ((Γ.es.get k).u = Sum.inr α) ||
      decide ((Γ.es.get k).v = Sum.inr α)) = true then 1 else 0 : ℕ) ≤
      anpKey5_cr Γ S k + 2 * anpKey5_ins Γ S k := by
    intro k
    rw [anpKey5_cr_two_ins, ← anpKey5_sum_eq_inS S, ← anpKey5_sum_eq_inS S, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro α _
    exact anpKey5_or_le _ _ α
  have hchain := (anpKey2_walkOK_iff Γ j).1 (hN.2.1 j)
  have hnd := hN.2.2.1 j
  calc 2 * ∑ α ∈ S, (if Γ.Visits j (Sum.inr α) then 1 else 0)
      = ∑ α ∈ S, 2 * (if Γ.Visits j (Sum.inr α) then 1 else 0) := by rw [Finset.mul_sum]
    _ ≤ ∑ α ∈ S, ∑ k ∈ anpKey5_eidx Γ j, (if (decide ((Γ.es.get k).u = Sum.inr α) ||
        decide ((Γ.es.get k).v = Sum.inr α)) = true then 1 else 0 : ℕ) := by
        apply Finset.sum_le_sum
        intro α _
        by_cases hv : Γ.Visits j (Sum.inr α)
        · have e1 : (if Γ.Visits j (Sum.inr α) then 1 else 0 : ℕ) = 1 := by simp only [hv, ↓reduceIte]
          rw [e1]
          obtain ⟨st, hst, hu⟩ := anpKey2_chain_visit Γ (Sum.inr α) (Γ.path j) _ _ hchain (by simp) hv
          have h2 := anpKey5_walk_two Γ (fun w => decide (w = Sum.inr α)) (Γ.path j) _ _ hchain (by simp)
            ⟨st, hst, by simp [hu]⟩
          have key := anpKey5_path_sum (Γ.path j) hnd
            (fun k => decide ((Γ.es.get k).u = Sum.inr α) || decide ((Γ.es.get k).v = Sum.inr α))
          unfold anpKey5_eidx
          rw [← key, Nat.mul_one]
          refine le_trans h2 (List.countP_mono_left (fun st _ h => ?_))
          simp only [bne_iff_ne, ne_eq, decide_eq_decide] at h
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          by_cases h1 : (Γ.es.get st.1).u = Sum.inr α
          · exact Or.inl h1
          · right; by_contra h3; exact h ⟨fun a => (h1 a).elim, fun a => (h3 a).elim⟩
        · simp [hv]
    _ = ∑ k ∈ anpKey5_eidx Γ j, ∑ α ∈ S, (if (decide ((Γ.es.get k).u = Sum.inr α) ||
        decide ((Γ.es.get k).v = Sum.inr α)) = true then 1 else 0 : ℕ) := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun k _ => hpt k

theorem anpKey5_pl3 (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (hN : Γ.IsNested)
    (hM : anpKey5_perPath Γ M) (j : Fin p) : ∑ k ∈ anpKey5_eidx Γ j, anpKey5_rm Γ M k ≤ 1 := by
  have h := hM j
  have key := anpKey5_path_sum (Γ.path j) (hN.2.2.1 j) (fun k => (Γ.es.get k).ghost || decide (k ∈ M))
  rw [← List.countP_eq_length_filter] at h
  rw [key] at h
  unfold anpKey5_eidx
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) h
  unfold anpKey5_rm
  by_cases h1 : (Γ.es.get k).ghost = true <;> by_cases h2 : k ∈ M <;> simp [h2]

theorem anpKey5_paths_disjoint (Γ : NGraph p q) (hN : Γ.IsNested) {i j : Fin p} (hij : i ≠ j) :
    Disjoint (anpKey5_eidx Γ i) (anpKey5_eidx Γ j) := by
  rw [Finset.disjoint_left]
  intro k hi hj
  simp only [anpKey5_eidx, List.mem_toFinset, List.mem_map] at hi hj
  obtain ⟨st, hst, rfl⟩ := hi
  obtain ⟨st', hst', h⟩ := hj
  exact hN.2.2.2.1 i j hij st hst st' hst' h.symm

theorem anpKey5_sum_paths_le (Γ : NGraph p q) (hN : Γ.IsNested) (P : Finset (Fin p))
    (h : Fin Γ.es.length → ℕ) : ∑ j ∈ P, ∑ k ∈ anpKey5_eidx Γ j, h k ≤ ∑ k, h k := by
  rw [← Finset.sum_biUnion]
  · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · intro i _ j _ hij
    exact anpKey5_paths_disjoint Γ hN hij

theorem anpKey5_gdcr (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (S : Finset (Fin q)) (j : Fin p) :
    ∑ k ∈ anpKey5_eidx Γ j, anpKey5_cr Γ S k =
      ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k +
        ∑ k ∈ anpKey5_eidx Γ j, anpKey5_rm Γ M k * anpKey5_cr Γ S k := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := anpKey5_gd_add_rm Γ M k
  calc anpKey5_cr Γ S k = (anpKey5_gd Γ M k + anpKey5_rm Γ M k) * anpKey5_cr Γ S k := by rw [this, one_mul]
    _ = _ := by ring

theorem anpKey5_gdins (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (S : Finset (Fin q)) (j : Fin p) :
    ∑ k ∈ anpKey5_eidx Γ j, anpKey5_ins Γ S k =
      ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_ins Γ S k +
        ∑ k ∈ anpKey5_eidx Γ j, anpKey5_rm Γ M k * anpKey5_ins Γ S k := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := anpKey5_gd_add_rm Γ M k
  calc anpKey5_ins Γ S k = (anpKey5_gd Γ M k + anpKey5_rm Γ M k) * anpKey5_ins Γ S k := by rw [this, one_mul]
    _ = _ := by ring

theorem anpKey5_rm_cr_ins (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (S : Finset (Fin q))
    (k : Fin Γ.es.length) :
    anpKey5_rm Γ M k * anpKey5_cr Γ S k + anpKey5_rm Γ M k * anpKey5_ins Γ S k ≤ anpKey5_rm Γ M k := by
  rw [← Nat.mul_add]
  calc anpKey5_rm Γ M k * (anpKey5_cr Γ S k + anpKey5_ins Γ S k) ≤ anpKey5_rm Γ M k * 1 :=
        Nat.mul_le_mul_left _ (anpKey5_cr_add_ins_le Γ S k)
    _ = _ := mul_one _

/-- The number of vertices of `S` that the path `j` visits. -/
def anpKey5_mj (Γ : NGraph p q) (S : Finset (Fin q)) (j : Fin p) : ℕ :=
  ∑ α ∈ S, if Γ.Visits j (Sum.inr α) then 1 else 0

/-- A path visiting `S` has at least one remaining crossing edge. -/
theorem anpKey5_pa (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (S : Finset (Fin q)) (hN : Γ.IsNested)
    (hM : anpKey5_perPath Γ M) (j : Fin p) (hj : ∃ α ∈ S, Γ.Visits j (Sum.inr α)) :
    1 ≤ ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k := by
  have h1 := anpKey5_pl1 Γ hN S j hj
  have h3 := anpKey5_pl3 Γ M hN hM j
  have hdec := anpKey5_gdcr Γ M S j
  have hrm : ∑ k ∈ anpKey5_eidx Γ j, anpKey5_rm Γ M k * anpKey5_cr Γ S k ≤
      ∑ k ∈ anpKey5_eidx Γ j, anpKey5_rm Γ M k := by
    refine Finset.sum_le_sum fun k _ => ?_
    have := anpKey5_rm_cr_ins Γ M S k
    omega
  omega

/-- If a path visiting `S` has exactly one remaining crossing edge, it visits at most `1 +` (its remaining inside
edges) vertices of `S`. -/
theorem anpKey5_path_bound (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (S : Finset (Fin q))
    (hN : Γ.IsNested) (hM : anpKey5_perPath Γ M) (j : Fin p) (hj : ∃ α ∈ S, Γ.Visits j (Sum.inr α))
    (hA : ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k = 1) :
    anpKey5_mj Γ S j ≤ 1 + ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_ins Γ S k := by
  have h1 := anpKey5_pl1 Γ hN S j hj
  have h2 := anpKey5_pl2 Γ hN S j
  have h3 := anpKey5_pl3 Γ M hN hM j
  have hcr := anpKey5_gdcr Γ M S j
  have hin := anpKey5_gdins Γ M S j
  have hrm : ∑ k ∈ anpKey5_eidx Γ j, anpKey5_rm Γ M k * anpKey5_cr Γ S k +
      ∑ k ∈ anpKey5_eidx Γ j, anpKey5_rm Γ M k * anpKey5_ins Γ S k ≤
      ∑ k ∈ anpKey5_eidx Γ j, anpKey5_rm Γ M k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => anpKey5_rm_cr_ins Γ M S k
  have hsum2 : ∑ k ∈ anpKey5_eidx Γ j, (anpKey5_cr Γ S k + 2 * anpKey5_ins Γ S k) =
      ∑ k ∈ anpKey5_eidx Γ j, anpKey5_cr Γ S k + 2 * ∑ k ∈ anpKey5_eidx Γ j, anpKey5_ins Γ S k := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold anpKey5_mj
  omega

end Paths

/-- `anpKey5_cross_ge` (`7_8:1388-1393`, the counting behind "B1 + B2", in Hall form): every set `S` of internal
vertices has at least `|S|` remaining edges with exactly one end in `S` (IsNested conjunct 6 gives `|S|` paths
visiting `S`; each crosses `∂S` at least twice with distinct edges, at most one of them removed). -/
theorem anpKey5_cross_ge : ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested →
    anpKey5_perPath Γ M → ∀ S : Finset (Fin q), S.card ≤ anpKey5_cross (anpKey5_rest Γ M) S := by
  intro p q Γ M hN hM S
  classical
  rw [anpKey5_rest_cross]
  have hHall := hN.2.2.2.2.2 S
  set P : Finset (Fin p) := Finset.univ.filter fun j => ∃ α ∈ S, Γ.Visits j (Sum.inr α) with hP
  have hmemP : ∀ j, j ∈ P ↔ ∃ α ∈ S, Γ.Visits j (Sum.inr α) := fun j => by simp [hP]
  have hA : ∀ j ∈ P, 1 ≤ ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k :=
    fun j hj => anpKey5_pa Γ M S hN hM j ((hmemP j).1 hj)
  calc S.card ≤ P.card := hHall
    _ = ∑ j ∈ P, 1 := by simp
    _ ≤ ∑ j ∈ P, ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k := Finset.sum_le_sum hA
    _ ≤ ∑ k, anpKey5_gd Γ M k * anpKey5_cr Γ S k := anpKey5_sum_paths_le Γ hN P _

/-- `anpKey5_inside_ge` (the formal `(eq:degali)`): if every vertex of `S` has at most one remaining edge leaving `S`,
then `S` carries at least `|S|` remaining edges inside (every visiting path then crosses `∂S` exactly twice and runs
inside `S` with remaining edges only; IsNested conjunct 5 gives two paths at each vertex). -/
theorem anpKey5_inside_ge : ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested →
    anpKey5_perPath Γ M → ∀ S : Finset (Fin q),
      (∀ v ∈ S, anpKey5_crossAt (anpKey5_rest Γ M) S v ≤ 1) →
        S.card ≤ anpKey5_inside (anpKey5_rest Γ M) S := by
  intro p q Γ M hN hM S hS
  classical
  have hHall := hN.2.2.2.2.2 S
  set P : Finset (Fin p) := Finset.univ.filter fun j => ∃ α ∈ S, Γ.Visits j (Sum.inr α) with hP
  have hmemP : ∀ j, j ∈ P ↔ ∃ α ∈ S, Γ.Visits j (Sum.inr α) := fun j => by simp [hP]
  have hcr : ∑ k, anpKey5_gd Γ M k * anpKey5_cr Γ S k ≤ S.card := by
    rw [← anpKey5_rest_cross]
    calc anpKey5_cross (anpKey5_rest Γ M) S ≤ ∑ v ∈ S, anpKey5_crossAt (anpKey5_rest Γ M) S v :=
          anpKey5_cross_le_sum _ _
      _ ≤ ∑ v ∈ S, 1 := Finset.sum_le_sum hS
      _ = S.card := by simp
  have hA : ∀ j ∈ P, 1 ≤ ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k :=
    fun j hj => anpKey5_pa Γ M S hN hM j ((hmemP j).1 hj)
  have hPA : ∑ j ∈ P, ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k ≤
      ∑ k, anpKey5_gd Γ M k * anpKey5_cr Γ S k := anpKey5_sum_paths_le Γ hN P _
  have hsumA : ∑ j ∈ P, 1 ≤ ∑ j ∈ P, ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k :=
    Finset.sum_le_sum hA
  have hP1 : ∑ j ∈ P, 1 = P.card := by simp
  have hPeq : ∑ j ∈ P, ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k = ∑ j ∈ P, 1 := by
    omega
  have hA1 : ∀ j ∈ P, ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_cr Γ S k = 1 :=
    fun j hj => ((Finset.sum_eq_sum_iff_of_le hA).1 hPeq.symm j hj).symm
  have hB : ∀ j ∈ P, anpKey5_mj Γ S j ≤ 1 + ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_ins Γ S k :=
    fun j hj => anpKey5_path_bound Γ M S hN hM j ((hmemP j).1 hj) (hA1 j hj)
  have hdc : 2 * S.card ≤ ∑ j ∈ P, anpKey5_mj Γ S j := by
    unfold anpKey5_mj
    rw [Finset.sum_comm]
    have key : ∀ α ∈ S, 2 ≤ ∑ j ∈ P, (if Γ.Visits j (Sum.inr α) then 1 else 0 : ℕ) := by
      intro α hα
      obtain ⟨i, i', hii, hi, hi'⟩ := hN.2.2.2.2.1 α
      have hiP : i ∈ P := (hmemP i).2 ⟨α, hα, hi⟩
      have hi'P : i' ∈ P := (hmemP i').2 ⟨α, hα, hi'⟩
      calc 2 = ∑ j ∈ ({i, i'} : Finset (Fin p)), (if Γ.Visits j (Sum.inr α) then 1 else 0 : ℕ) := by
            rw [Finset.sum_pair hii]; simp [hi, hi']
        _ ≤ _ := Finset.sum_le_sum_of_subset (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption)
    calc 2 * S.card = ∑ α ∈ S, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum key
  have hI : ∑ j ∈ P, ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_ins Γ S k ≤
      ∑ k, anpKey5_gd Γ M k * anpKey5_ins Γ S k := anpKey5_sum_paths_le Γ hN P _
  rw [anpKey5_rest_inside]
  have hsumB : ∑ j ∈ P, anpKey5_mj Γ S j ≤
      ∑ j ∈ P, (1 + ∑ k ∈ anpKey5_eidx Γ j, anpKey5_gd Γ M k * anpKey5_ins Γ S k) := Finset.sum_le_sum hB
  rw [Finset.sum_add_distrib, hP1] at hsumB
  omega

/-! ## 7. The target -/

/-- Target (`7_8:1388-1451`, combinatorial): every nested graph, with one edge per path removed (its ghost, or a
reserved edge), has a summation certificate for its remaining solid edges.  No `GhostOK` ending-edge clause, no region,
no `NoA2`, no case hypothesis.  The paper's pigeonhole (`q = p`, `7_8:1388-1393`) is replaced by Hall
(`anpKey5_cross_ge`) and `(eq:degali)` by `anpKey5_inside_ge`; the spanning tree and its re-rooting by
`anpKey5_graph`. -/
theorem anpKey5_cert : ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested →
    anpKey5_perPath Γ M → ∃ n : ℕ, AnpSumCert n (anpKey5_rest Γ M) := by
  intro p q Γ M hN hM
  refine anpKey5_graph p q (anpKey5_rest Γ M) ?_ (anpKey5_cross_ge p q Γ M hN hM)
    (anpKey5_inside_ge p q Γ M hN hM)
  intro e he
  unfold anpKey5_rest at he
  simp only [List.mem_filterMap] at he
  obtain ⟨k, -, hk⟩ := he
  by_cases h : (Γ.es.get k).ghost = true ∨ k ∈ M
  · simp only [h, ↓reduceIte] at hk
    exact absurd hk (by simp)
  · simp only [h, ↓reduceIte] at hk
    obtain rfl := Option.some.inj hk
    exact hN.1 _ (List.get_mem _ k)

/-! ## 8. Compiled nonempty instances -/

section Instances

instance anpKey5_decIsNested {p q : ℕ} (Γ : NGraph p q) : Decidable Γ.IsNested := by
  unfold NGraph.IsNested; infer_instance

/-- Formal case (IV) with `q = 1 < p = 2` (`α = inr 0`).  Path 0: `a_0 → α` (ghost, B2), `α → b_0` (solid, B1).
Path 1: `a_1 → b_0` (solid, an ending edge at an external vertex), `b_0 → α` (solid), `α → b_1` (ghost, B2).
Edge 5: `α a_0` (solid, on no path).  `deg_s(α) = 3`, `n_S = 4`, `ord = 2`, `n_ngh = 0`; without edge 5 it is
case (III).  The paper's pigeonhole `q = p` (`7_8:1388-1393`) fails here. -/
def anpKey5_figIVext : NGraph 2 1 where
  es := [⟨true, .inl (.inl 0), .inr 0⟩, ⟨false, .inr 0, .inl (.inr 0)⟩, ⟨false, .inl (.inl 1), .inl (.inr 0)⟩,
         ⟨false, .inl (.inr 0), .inr 0⟩, ⟨true, .inr 0, .inl (.inr 1)⟩, ⟨false, .inr 0, .inl (.inl 0)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (1, .inl (.inr 0))]
    else [(2, .inl (.inr 0)), (3, .inr 0), (4, .inl (.inr 1))]

/-- Any `π` works at `anpKey5_figIVext` (no path is ghost-free). -/
def anpKey5_piIV : Fin 1 → Fin 2 → Bool := fun _ _ => false

/-- The reserved set `{0, 5}` of `figAux` (the first edge of path 0, the last edge of path 1). -/
def anpKey5_resAux : Finset (Fin figAux.es.length) := Finset.univ.filter fun k => k.1 = 0 ∨ k.1 = 5

/-- Instance (1): `anpKey5_figIVext` is in case (IV), and has the nested order `[α]`. -/
theorem anpKey5_inst_figIVext :
    anpKey5_figIVext.GhostOK ∧ anpKey5_figIVext.IsNested ∧ anpKey5_figIVext.NoA2 anpKey5_piIV ∧
      ¬ AnpCaseI anpKey5_figIVext anpKey5_piIV ∧ ¬ AnpCaseIII anpKey5_figIVext anpKey5_piIV ∧
      anpKey5_figIVext.degS 0 = 3 ∧ anpKey5_figIVext.ordN = 2 ∧ anpKey5_figIVext.nngh = 0 ∧
      AnpSumOrder (anpKey5_rest anpKey5_figIVext ∅) [0] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

theorem anpKey5_perm_two (σ : List (Fin 2)) (h : σ ∈ (List.finRange 2).permutations) :
    σ = [0, 1] ∨ σ = [1, 0] := by
  rw [List.mem_permutations] at h
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 h.length_eq
  fin_cases a <;> fin_cases b <;> first | (left; rfl) | (right; rfl) | (exfalso; revert h; decide +kernel)

/-- Instance (2): the re-rooting is needed: `figAux` with `anpKey5_resAux` removed has no nested order, and a
certificate of depth 1 (AM-GM on the remaining edges `a_1 ℳ₁` (index 0) and `ℳ₂ b_0` (index 3); the two branches
have the nested orders `[0, 1]` and `[1, 0]`). -/
theorem anpKey5_inst_resAux :
    anpKey5_perPath figAux anpKey5_resAux ∧
      (∀ σ ∈ (List.finRange 2).permutations, ¬ AnpSumOrder (anpKey5_rest figAux anpKey5_resAux) σ) ∧
      AnpSumCert 1 (anpKey5_rest figAux anpKey5_resAux) := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro σ hσ
    rcases anpKey5_perm_two σ hσ with rfl | rfl <;> decide +kernel
  refine Or.inr ⟨⟨0, by decide +kernel⟩, ⟨3, by decide +kernel⟩, by decide +kernel, ⟨[0, 1], ?_⟩, ⟨[1, 0], ?_⟩⟩
  all_goals decide +kernel

/-- Instance (3): the target at the merged `anpKey2_figAuxGh` (ghosts dropped, nothing reserved). -/
theorem anpKey5_inst_figAuxGh :
    anpKey5_perPath anpKey2_figAuxGh ∅ ∧ ∃ n : ℕ, AnpSumCert n (anpKey5_rest anpKey2_figAuxGh ∅) := by
  have hp : anpKey5_perPath anpKey2_figAuxGh ∅ := by decide +kernel
  exact ⟨hp, anpKey5_cert 2 2 anpKey2_figAuxGh ∅ anpKey2_figAuxGh_nested hp⟩

/-- Instance (4): the target at `anpKey5_figIVext` (nothing reserved), and reserving edge `1` of path 0 (which
already has its ghost `0`) violates the per-path hypothesis. -/
theorem anpKey5_inst_figIVext_cert :
    anpKey5_perPath anpKey5_figIVext ∅ ∧ (∃ n : ℕ, AnpSumCert n (anpKey5_rest anpKey5_figIVext ∅)) ∧
      ¬ anpKey5_perPath anpKey5_figIVext
        (Finset.univ.filter fun k : Fin anpKey5_figIVext.es.length => k.1 = 1) := by
  have hp : anpKey5_perPath anpKey5_figIVext ∅ := by decide +kernel
  exact ⟨hp, anpKey5_cert 2 1 anpKey5_figIVext ∅ anpKey5_inst_figIVext.2.1 hp, by decide +kernel⟩

/-- Instances of the intermediate theorems at `figAux` with `anpKey5_resAux` removed (`p = q = 2`): the crossing
bound at `S = {α₀, α₁}` (`2 ≤ cross`), the inside bound there (both vertices have exactly one leaving edge:
`2 ≤ inside`), and the certificate from `anpKey5_graph` (loops excluded, both bounds checked on all four subsets). -/
theorem anpKey5_inst_cross_inside :
    (Finset.univ : Finset (Fin 2)).card ≤ anpKey5_cross (anpKey5_rest figAux anpKey5_resAux) Finset.univ ∧
      (Finset.univ : Finset (Fin 2)).card ≤ anpKey5_inside (anpKey5_rest figAux anpKey5_resAux) Finset.univ ∧
      ∃ n : ℕ, AnpSumCert n (anpKey5_rest figAux anpKey5_resAux) := by
  have hp : anpKey5_perPath figAux anpKey5_resAux := by decide +kernel
  have hN : figAux.IsNested := figAux_nested.1
  refine ⟨anpKey5_cross_ge 2 2 figAux anpKey5_resAux hN hp Finset.univ,
    anpKey5_inside_ge 2 2 figAux anpKey5_resAux hN hp Finset.univ (by decide +kernel), ?_⟩
  refine anpKey5_graph 2 2 (anpKey5_rest figAux anpKey5_resAux) ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel

end Instances

end RBM.Graph
