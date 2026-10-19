/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# `lem:Anp_key_gh`: walks and edge products for the induction step

Paper: proof of Lemma 7.24 (`lem:Anp_key_gh`), induction step: the value of a graph with the
internal labels restricted to a set (the left side of (7.42) `kwuyayw`), the replacement of an
ending edge by a ghost edge, and the paths `𝔓_j` of the graph followed step by step.

Conventions: `π i j = true` iff `α_i` is strictly closer to `b_j` than to `a_j`; an ending edge has
a side bit `s` (`false`: first step of the path, at `a_j`; `true`: last step, at `b_j`).

* `NGraph.valOn`: the value of `Γ` with the internal labels summed over a set `S`.
* `anpKey2_stepOK`, `anpKey2_chain`: walks along the edges of a graph, with the lemmas
  `anpKey2_foldl_iff`, `anpKey2_walkOK_iff`, `anpKey2_chain_visit`.
* `anpKey2_ep`, `anpKey2_ep_nonneg`, `anpKey2_ep_ghostify`: the product of the edge factors at a
  labelling; replacing an edge by a ghost edge turns one solid factor into `1`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The value with the internal labels restricted to a set -/

namespace NGraph

variable {p q : ℕ}

/-- The value of `Γ` with the internal labels restricted to `S` (the left side of (7.42)
`kwuyayw`); `Γ.val ξ a b` is the case `S = univ`. -/
def valOn (Γ : NGraph p q) {ι : Type*} (ξ : ι → ι → ℝ) (a b : Fin p → ι)
    (S : Finset (Fin q → ι)) : ℝ :=
  ∑ ℓ ∈ S, (Γ.es.map fun e =>
    if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod

end NGraph

/-! ## 2. Walks in a graph and the product of the edge factors -/

section Chain

variable {p q : ℕ}

/-- One step of a walk: the edge `st.1` joins the current vertex `c` to `st.2`. -/
def anpKey2_stepOK (Γ : NGraph p q) (c : NV p q) (st : Fin Γ.es.length × NV p q) : Prop :=
  ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨ ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2)

/-- The walk `x ⇝ y` along the steps `l`. -/
def anpKey2_chain (Γ : NGraph p q) : NV p q → List (Fin Γ.es.length × NV p q) → NV p q → Prop
  | x, [], y => x = y
  | x, st :: t, y => anpKey2_stepOK Γ x st ∧ anpKey2_chain Γ st.2 t y

private theorem anpKey2_foldl_none (Γ : NGraph p q) (l : List (Fin Γ.es.length × NV p q)) :
    (l.foldl (fun (acc : Option (NV p q)) st => acc.bind fun c =>
      if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
          ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none) none) = none := by
  induction l with
  | nil => rfl
  | cons st t ih => simpa [List.foldl_cons] using ih

theorem anpKey2_foldl_iff (Γ : NGraph p q) (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q) :
    (l.foldl (fun (acc : Option (NV p q)) st => acc.bind fun c =>
      if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
          ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none) (some x)) = some y ↔
      anpKey2_chain Γ x l y := by
  induction l generalizing x with
  | nil => simp [anpKey2_chain]
  | cons st t ih =>
    rw [List.foldl_cons, anpKey2_chain]
    by_cases hc : ((Γ.es.get st.1).u = x ∧ (Γ.es.get st.1).v = st.2) ∨
        ((Γ.es.get st.1).v = x ∧ (Γ.es.get st.1).u = st.2)
    · have : (Option.bind (some x) fun c =>
          if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
            ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none) = some st.2 := by
        rw [Option.bind_some]
        split_ifs
        rfl
      rw [this, ih]
      exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
    · have : (Option.bind (some x) fun c =>
          if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
            ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none) = none := by
        rw [Option.bind_some]
        split_ifs
        rfl
      rw [this, anpKey2_foldl_none]
      exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 hc⟩

theorem anpKey2_walkOK_iff (Γ : NGraph p q) (j : Fin p) :
    Γ.WalkOK j ↔ anpKey2_chain Γ (Sum.inl (Sum.inl j)) (Γ.path j) (Sum.inl (Sum.inr j)) :=
  anpKey2_foldl_iff Γ _ _ _

/-- A walk from `x ≠ α` that has a step with an edge at `α` has a step arriving at `α`. -/
theorem anpKey2_chain_visit (Γ : NGraph p q) (α : NV p q) :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q), anpKey2_chain Γ x l y → x ≠ α →
      (∃ st ∈ l, (Γ.es.get st.1).u = α ∨ (Γ.es.get st.1).v = α) → ∃ st ∈ l, st.2 = α := by
  intro l
  induction l with
  | nil => intro x y _ _ ⟨st, hst, _⟩; simp at hst
  | cons st t ih =>
    intro x y h hx ⟨st', hst', hα⟩
    obtain ⟨hstep, hrest⟩ := h
    by_cases h2 : st.2 = α
    · exact ⟨st, List.mem_cons_self, h2⟩
    · rcases List.mem_cons.1 hst' with rfl | hmem
      · exfalso
        rcases hstep with ⟨h1, h2'⟩ | ⟨h1, h2'⟩ <;> rcases hα with h | h <;> simp_all
      · obtain ⟨st'', hst'', h3⟩ := ih st.2 y hrest h2 ⟨st', hmem, hα⟩
        exact ⟨st'', List.mem_cons_of_mem _ hst'', h3⟩

end Chain

section A2

variable {p q : ℕ}

/-- The product of the edge factors of `Γ` at the labelling `lab`. -/
def anpKey2_ep {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (lab : NV p q → ι) : ℝ :=
  (Γ.es.map fun e => if e.ghost then (1 : ℝ) else ξ (lab e.u) (lab e.v)).prod

theorem anpKey2_ep_nonneg {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (hξ : ∀ α β, 0 ≤ ξ α β)
    (lab : NV p q → ι) : 0 ≤ anpKey2_ep Γ ξ lab := by
  unfold anpKey2_ep
  refine List.prod_nonneg fun x hx => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact zero_le_one
  · exact hξ _ _

private theorem anpKey2_prod_set {α : Type*} (f : α → ℝ) (e' : α) :
    ∀ (l : List α) (n : ℕ) (hn : n < l.length),
      (l.map f).prod * f e' = ((l.set n e').map f).prod * f l[n]
  | [], n, hn => absurd hn (by simp)
  | x :: t, 0, _ => by simp [List.set]; ring
  | x :: t, n + 1, hn => by
    have hn' : n < t.length := by simpa using hn
    have ih := anpKey2_prod_set f e' t n hn'
    simp only [List.set_cons_succ, List.map_cons, List.prod_cons, List.getElem_cons_succ]
    calc f x * (t.map f).prod * f e' = f x * ((t.map f).prod * f e') := by ring
      _ = f x * (((t.set n e').map f).prod * f t[n]) := by rw [ih]
      _ = _ := by ring

/-- The A2 replacement turns one solid factor into `1`. -/
theorem anpKey2_ep_ghostify {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (lab : NV p q → ι)
    (k : Fin Γ.es.length) (hk : (Γ.es.get k).ghost = false) :
    anpKey2_ep Γ ξ lab = ξ (lab (Γ.es.get k).u) (lab (Γ.es.get k).v) * anpKey2_ep (Γ.ghostify k) ξ lab := by
  unfold anpKey2_ep
  have h := anpKey2_prod_set (fun e : NEdge p q => if e.ghost then (1 : ℝ) else ξ (lab e.u) (lab e.v))
    { Γ.es[k.1] with ghost := true } Γ.es k.1 k.2
  have hk' : Γ.es[k.1].ghost = false := hk
  simp only [hk', Bool.false_eq_true, ite_false, ite_true, mul_one] at h
  show _ = _ * (((Γ.es.set k.1 { Γ.es[k.1] with ghost := true }).map _).prod)
  rw [h, mul_comm]
  rfl

end A2

end RBM.Graph
