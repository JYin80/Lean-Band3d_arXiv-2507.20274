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
# LW-12b: `lem:Anp_key_gh`, the setup of the induction step (T2242)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): the regions `𝐃_π`
(`:1113`) and `(kwuyayw)` (`:1118-1121`), the ending-edge types A1/A2/B1/B2 (`:1123-1141`), the A2
replacement and `(eq:noA2)` (`:1143-1148`), vertex fixing (`:1158-1172`, `:1209-1237`), the case
statements (I)-(IV) (`:1152`, `:1205`, `:1245`, `:1385`).  Part b of the six tickets of `lem:Anp`.

Conventions fixed here for LW-12c-f: `π i j = true` iff `α_i` is strictly closer to `b_j` than to
`a_j`; an ending edge has a side bit `s` (`false`: first step of the path, at `a_j`; `true`: last
step, at `b_j`); type A1 iff the path has no ghost edge and `π i j = s` (the vertex lies on the side
of its own end).

* Section 1: the vocabulary (`valOn`, the regions, `EndAt`, `IsA1`-`IsB2`, `NoA2`, `degS`, the
  pins `AnpDetGhRegAt`, `AnpIH`, `AnpDetGhRegStep`, `AnpCaseI`, `AnpCaseIII`, `AnpDetGhCase*`).
* Section 2: `anpDetGh_of_reg` (the `2^{pq}` regions cover).
* Section 3: the half-distance fact and the ending-edge types.
* Section 4: the A2 replacement on a region, `anpDetGhReg_of_noA2`.
* Section 5: vertex fixing, `anpKey2_fix`.
* Section 6: the step from the regions and the case split.
* Section 7: compiled nonempty instances.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Vocabulary (`7_8:1111-1141`) -/

namespace NGraph

variable {p q : ℕ}

/-- The value of `Γ` with the internal labels restricted to `S` (the LHS of `(kwuyayw)`, `7_8:1119`);
`Γ.val ξ a b` is the case `S = univ`. -/
def valOn (Γ : NGraph p q) {ι : Type*} (ξ : ι → ι → ℝ) (a b : Fin p → ι)
    (S : Finset (Fin q → ι)) : ℝ :=
  ∑ ℓ ∈ S, (Γ.es.map fun e =>
    if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod

end NGraph

/-! ## 2. The regions cover (`7_8:1116-1118`) -/

/-! ## 3. The half-distance fact and the ending-edge types (`7_8:1126-1141`) -/

/-! ## 4. The A2 replacement on a region (`7_8:1143-1148`) -/

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

/-! ## 5. Vertex fixing (`7_8:1158-1172`, `:1209-1237`)

The path `𝔓_j` is cut after each step that arrives at `α_{i₀}`: `K_j` arrivals give `K_j + 1` segments `(j, r)`,
`r ≤ K_j`, enumerated by `finSigmaFinEquiv` (`p' = Σ_j (K_j + 1)`).  The segment `(j, r)` starts at `a_j` (`r = 0`)
or at `α_{i₀}`, and ends at `b_j` (`r = K_j`) or at `α_{i₀}`.  The edges of the fixed graph are the edges of `Γ`,
relabelled: `a_j`, `b_j` go to the start of the first / the end of the last segment of `𝔓_j`, `α_i` to its place
among the remaining vertices (`i ≠ i₀`), and `α_{i₀}` to the start (resp. end) of the segment of which the edge is
the first (resp. last) step, else to the end of a fixed segment `s₀` that ends at `α_{i₀}`. -/

section Fix

variable {p q : ℕ} (Γ : NGraph p (q + 1)) (i₀ : Fin (q + 1))

/-! basic facts on the segments -/

/-! the image of `α_{i₀}` on an edge -/

/-! the relabelling of vertices -/

theorem anpKey2_chain_new {p q p' q' : ℕ} (Γ : NGraph p q) (Γ' : NGraph p' q')
    (em : Fin Γ.es.length → Fin Γ'.es.length) (rel : Fin Γ.es.length → NV p q → NV p' q')
    (hedge : ∀ k, (Γ'.es.get (em k)).u = rel k (Γ.es.get k).u ∧
      (Γ'.es.get (em k)).v = rel k (Γ.es.get k).v)
    (vs : NV p q → NV p' q') :
    ∀ (T : List (Fin Γ.es.length × NV p q)) (c : NV p q) (c' : NV p' q') (w : NV p q),
      anpKey2_chain Γ c T w → (∀ x ∈ T, rel x.1 x.2 = vs x.2) →
      (∀ x ∈ T.dropLast, ∀ k, rel k x.2 = vs x.2) → (∀ x, T.head? = some x → rel x.1 c = c') →
      T ≠ [] →
      anpKey2_chain Γ' c' (T.map fun x => (em x.1, vs x.2)) (vs w) := by
  intro T
  induction T with
  | nil => intro _ _ _ _ _ _ _ _; contradiction
  | cons x T' ih =>
    intro c c' w h h1 h2 h3 _
    obtain ⟨hstep, hrest⟩ := h
    have hx1 := h1 x List.mem_cons_self
    have hc := h3 x rfl
    refine ⟨?_, ?_⟩
    · obtain ⟨hu, hv⟩ := hedge x.1
      rcases hstep with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [hu, e1, hc]
        · rw [hv, e2, hx1]
      · right
        refine ⟨?_, ?_⟩
        · rw [hv, e1, hc]
        · rw [hu, e2, hx1]
    · cases T' with
      | nil =>
        have : x.2 = w := hrest
        simp [anpKey2_chain, this]
      | cons y T'' =>
        refine ih x.2 (vs x.2) w hrest (fun z hz => h1 z (List.mem_cons_of_mem _ hz)) ?_ ?_ (by simp)
        · intro z hz k
          refine h2 z ?_ k
          rw [List.dropLast_cons_of_ne_nil (by simp)]
          exact List.mem_cons_of_mem _ hz
        · intro z hz
          have hz' : z = y := by simpa using hz.symm
          subst hz'
          refine h2 x ?_ z.1
          rw [List.dropLast_cons_of_ne_nil (by simp)]
          exact List.mem_cons_self

/-! the value -/

/-! steps, ghost-free paths, ending edges, `n_S` -/

end Fix

/-! ## 6. The step from the regions and the case split -/

/-! ## 7. Compiled nonempty instances at `d = 3` -/

end RBM.Graph
