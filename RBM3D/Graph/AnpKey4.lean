/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey3
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# LW-12d: `lem:Anp_key_gh`, case (III) of the induction step (T2260)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): Case (III)
`:1245-1348`: an internal vertex `α_q` with two B2 (ghost) ending edges and `deg_s(α_q) = 2`
`:1246`, the two solid edges `(α_q, β_t)` `:1246-1247`, the new graph `:1250-1331`,
`(kwuyayw_case3)` `:1344-1347`, Cauchy-Schwarz `:1348`.  Part d of the six tickets of `lem:Anp`.

The proof, for `q = q' + 1`: fix the vertex `α_{i₀}` (`anpKey2_fixV`); the two B2 edges `k_t` become
the one-step ghost paths `r_t`, and the solid edge `m_t` next to `k_t` on `𝔓_{j_t}` is the first or
the last step of another segment `r'_t` of `𝔓_{j_t}`, which is ghost free; making `m₁`, `m₂` ghost
(`anpKey3_gh2`, in place of the paper's new ghost edges `(a_t, β_t)`, `7_8:1250-1254`) gives `Γ''`
with `q'` internal vertices and `ord Γ'' = ord Γ`.  Since `deg_s(α_{i₀}) = 2`, the label `x` of the
fixed vertex occurs only on `m₁`, `m₂`, so `Σ_x ξ(x, y₁) ξ(x, y₂) ≤ θ` closes the step; the
constants are `(C, c) ↦ (C'', c''/2)`.

* Section 1: `anpKey4_caseIII_ne` and `anpKey4_solid` (`7_8:1246-1247`).
* Section 2: the double ghostify at a first or last step of two ghost-free paths.
* Section 3: positions in the fixed graph.
* Section 4: the factor at the fixed vertex and the `x`-independence.
* Section 5: the reduction `anpKey4_reduce`.
* Section 6: the assembly `anpKey4_of_reduce` and the target `anpDetGhCaseIII_holds`.
* Section 7: compiled nonempty instances at `d = 3`.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The two B2 edges and the two solid edges at the vertex (`7_8:1246-1247`) -/

section NeSolid

variable {p q : ℕ}

/-- An ending edge of type B2 has a ghost step on its path, so the path is not ghost free. -/
theorem anpKey4_ng_false {Γ : NGraph p q} {π : Fin q → Fin p → Bool} {j : Fin p} {s : Bool}
    {k : Fin Γ.es.length} {i : Fin q} (h : Γ.IsB2 π j s k i) : Γ.noGhostPath j = false := by
  obtain ⟨v, hmem, -⟩ := anpKey3_endAt_mem h.1
  by_contra hcon
  have ht : Γ.noGhostPath j = true := by simpa using hcon
  have := (anpKey2_noGhost_iff Γ j).1 ht _ hmem
  rw [h.2] at this
  exact Bool.noConfusion this

/-- Two distinct B2 ending edges at one internal vertex lie on distinct paths (`7_8:1246`, "by definition"): the
paper's statement, from `GhostOK` (at most one ghost per path) and `IsNested` (walk, no repeated edge). -/
theorem anpKey4_caseIII_ne :
    ∀ (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool)
      (k₁ k₂ : Fin Γ.es.length),
      Γ.GhostOK → Γ.IsNested → (j₁, s₁) ≠ (j₂, s₂) →
      Γ.IsB2 π j₁ s₁ k₁ i → Γ.IsB2 π j₂ s₂ k₂ i → j₁ ≠ j₂ := by
  intro p q Γ π i j₁ j₂ s₁ s₂ k₁ k₂ hG hN hne h₁ h₂ hj
  subst hj
  have hs : s₁ ≠ s₂ := fun h => hne (by rw [h])
  obtain ⟨e₁, g₁⟩ := h₁
  obtain ⟨e₂, g₂⟩ := h₂
  obtain ⟨v₁, hm₁, -⟩ := anpKey3_endAt_mem e₁
  obtain ⟨v₂, hm₂, -⟩ := anpKey3_endAt_mem e₂
  have hk : k₁ = k₂ := congrArg Prod.fst (anpKey2_ghost_unique Γ hG hm₁ hm₂ g₁ g₂)
  subst hk
  have a₁ := anpKey2_endAt_ends (hN.2.1 j₁) e₁
  have a₂ := anpKey2_endAt_ends (hN.2.1 j₁) e₂
  cases s₁ <;> cases s₂
  · exact hs rfl
  · simp only [Bool.false_eq_true, ite_false, ite_true] at a₁ a₂
    rcases a₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases a₂ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp_all
  · simp only [Bool.false_eq_true, ite_false, ite_true] at a₁ a₂
    rcases a₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases a₂ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp_all
  · exact hs rfl

/-- The path starts with the ending edge `k` at `α_i`: the first step arrives at `α_i`, and the next step leaves
it along an edge at `α_i`. -/
theorem anpKey4_head_shape {Γ : NGraph p q} {j : Fin p} (hW : Γ.WalkOK j) {k : Fin Γ.es.length} {v : NV p q}
    {t : List (Fin Γ.es.length × NV p q)} (hp : Γ.path j = (k, v) :: t) {i : Fin q}
    (hi : (Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i) :
    v = Sum.inr i ∧ ∃ (m : Fin Γ.es.length) (w : NV p q) (rest : List (Fin Γ.es.length × NV p q)),
      t = (m, w) :: rest ∧ ((Γ.es.get m).u = Sum.inr i ∨ (Γ.es.get m).v = Sum.inr i) := by
  have hch := (anpKey2_walkOK_iff Γ j).1 hW
  rw [hp] at hch
  obtain ⟨hstep, hrest⟩ := hch
  have hv : v = Sum.inr i := by
    rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with h | h <;> simp_all
  refine ⟨hv, ?_⟩
  cases t with
  | nil =>
    exfalso
    have : v = Sum.inl (Sum.inr j) := hrest
    rw [hv] at this
    simp at this
  | cons x t' =>
    obtain ⟨m, w⟩ := x
    refine ⟨m, w, t', rfl, ?_⟩
    obtain ⟨hstep2, -⟩ := hrest
    rw [hv] at hstep2
    rcases hstep2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr h1

/-- The path ends with the ending edge `k` at `α_i`: the step before it arrives at `α_i` along an edge at `α_i`. -/
theorem anpKey4_last_shape {Γ : NGraph p q} {j : Fin p} (hW : Γ.WalkOK j) {k : Fin Γ.es.length} {v : NV p q}
    {l : List (Fin Γ.es.length × NV p q)} (hp : Γ.path j = l ++ [(k, v)]) {i : Fin q}
    (hi : (Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i) :
    v = Sum.inl (Sum.inr j) ∧ ∃ (pre : List (Fin Γ.es.length × NV p q)) (m : Fin Γ.es.length),
      l = pre ++ [(m, Sum.inr i)] ∧ ((Γ.es.get m).u = Sum.inr i ∨ (Γ.es.get m).v = Sum.inr i) := by
  have hch := (anpKey2_walkOK_iff Γ j).1 hW
  rw [hp] at hch
  obtain ⟨z, hz, hstep, hvb⟩ := (anpKey2_chain_snoc Γ l (k, v) _ _).1 hch
  simp only at hvb
  have hzα : z = Sum.inr i := by
    rcases hstep with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hi with h | h <;> simp_all
  subst hzα
  refine ⟨hvb, ?_⟩
  rcases List.eq_nil_or_concat l with h | ⟨l', y, h⟩
  · rw [h] at hz
    simp [anpKey2_chain] at hz
  · rw [List.concat_eq_append] at h
    subst h
    obtain ⟨m, w⟩ := y
    have hy2 := anpKey2_chain_end Γ l' (m, w) _ _ hz
    obtain ⟨z', -, hstep', hw⟩ := (anpKey2_chain_snoc Γ l' (m, w) _ _).1 hz
    simp only at hy2 hw
    subst hy2
    refine ⟨l', m, rfl, ?_⟩
    rcases hstep' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr e2
    · exact Or.inl e2

/-- One B2 ending edge `k` of `𝔓_j` at `α_i` and the solid edge `m` next to it on the path (`7_8:1246-1247`): the step
after `k` (`s = false`) or before `k` (`s = true`); `m` is at `α_i`, solid, and lies on the same path. -/
theorem anpKey4_side {Γ : NGraph p q} (hG : Γ.GhostOK) (hN : Γ.IsNested) {π : Fin q → Fin p → Bool}
    {j : Fin p} {s : Bool} {k : Fin Γ.es.length} {i : Fin q} (h : Γ.IsB2 π j s k i) :
    ∃ m : Fin Γ.es.length, (Γ.es.get m).ghost = false ∧
      ((Γ.es.get m).u = Sum.inr i ∨ (Γ.es.get m).v = Sum.inr i) ∧ (∃ w, (m, w) ∈ Γ.path j) ∧
      (s = false → ∃ (w : NV p q) (rest : List (Fin Γ.es.length × NV p q)),
        Γ.path j = (k, Sum.inr i) :: (m, w) :: rest) ∧
      (s = true → ∃ pre : List (Fin Γ.es.length × NV p q),
        Γ.path j = pre ++ [(m, Sum.inr i), (k, Sum.inl (Sum.inr j))]) := by
  obtain ⟨⟨⟨v, hv⟩, hi⟩, gk⟩ := h
  have hnd := hN.2.2.1 j
  cases s
  · simp only [Bool.false_eq_true, ite_false] at hv
    obtain ⟨t, ht⟩ : ∃ t, Γ.path j = (k, v) :: t := by
      cases hp : Γ.path j with
      | nil => rw [hp] at hv; simp at hv
      | cons x t => rw [hp] at hv; simp at hv; exact ⟨t, by rw [hv]⟩
    obtain ⟨hvα, m, w, rest, hrest, hm⟩ := anpKey4_head_shape (hN.2.1 j) ht hi
    subst hrest
    subst hvα
    rw [ht] at hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
    have hkm : k ≠ m := hnd.1.1
    have hmem : (m, w) ∈ Γ.path j := by rw [ht]; simp
    have hkmem : (k, Sum.inr i) ∈ Γ.path j := by rw [ht]; simp
    have gm : (Γ.es.get m).ghost = false := by
      by_contra hcon
      have hg : (Γ.es.get m).ghost = true := by simpa using hcon
      have := anpKey2_ghost_unique Γ hG hmem hkmem hg gk
      exact hkm (congrArg Prod.fst this).symm
    exact ⟨m, gm, hm, ⟨w, hmem⟩, fun _ => ⟨w, rest, ht⟩, fun h => absurd h (by simp)⟩
  · simp only [ite_true] at hv
    obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 hv
    obtain ⟨hvb, pre, m, hpre, hm⟩ := anpKey4_last_shape (hN.2.1 j) hl hi
    subst hpre
    subst hvb
    have hpath : Γ.path j = pre ++ [(m, Sum.inr i), (k, Sum.inl (Sum.inr j))] := by
      rw [hl]; simp
    rw [hl, List.map_append] at hnd
    have hmem : (m, Sum.inr i) ∈ Γ.path j := by rw [hpath]; simp
    have hkmem : (k, Sum.inl (Sum.inr j)) ∈ Γ.path j := by rw [hpath]; simp
    have hkm : m ≠ k := by
      have := (List.nodup_append.1 hnd).2.2 m (by simp) k (by simp)
      exact this
    have gm : (Γ.es.get m).ghost = false := by
      by_contra hcon
      have hg : (Γ.es.get m).ghost = true := by simpa using hcon
      have := anpKey2_ghost_unique Γ hG hmem hkmem hg gk
      exact hkm (congrArg Prod.fst this)
    exact ⟨m, gm, hm, ⟨_, hmem⟩, fun h => absurd h (by simp), fun _ => ⟨pre, hpath⟩⟩

/-- `deg_s(α_i)` counts the solid edges at `α_i` by index. -/
theorem anpKey4_degS_eq (Γ : NGraph p q) (i : Fin q) :
    Γ.degS i = (Finset.univ.filter fun k : Fin Γ.es.length =>
      (Γ.es.get k).ghost = false ∧ ((Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i)).card := by
  classical
  unfold NGraph.degS
  have h1 : ∀ (P : NEdge p q → Bool) (l : List (NEdge p q)),
      (l.filter P).length = (l.map fun e => if P e = true then 1 else 0).sum := by
    intro P l
    induction l with
    | nil => simp
    | cons a t ih =>
      by_cases ha : P a = true
      · rw [List.filter_cons_of_pos ha, List.length_cons, List.map_cons, List.sum_cons, ih]
        simp only [ha, ite_true]
        omega
      · rw [List.filter_cons_of_neg ha, List.map_cons, List.sum_cons, ih]
        simp only [ha]
        simp
  rw [h1 (fun e => !e.ghost && (decide (e.u = Sum.inr i) || decide (e.v = Sum.inr i))), ← List.ofFn_getElem_eq_map, List.sum_ofFn, Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.get_eq_getElem, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq]

/-- The two solid edges `(α, β_t)` at the vertex of case (III) (`7_8:1247`): the step after (`s_t = false`) or
before (`s_t = true`) the B2 edge `k_t` on `𝔓_{j_t}`; distinct, solid, at `α_i`, and (`deg_s(α_i) = 2`) the only
solid edges at `α_i`. -/
theorem anpKey4_solid :
    ∀ (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool)
      (k₁ k₂ : Fin Γ.es.length),
      Γ.GhostOK → Γ.IsNested → j₁ ≠ j₂ → Γ.IsB2 π j₁ s₁ k₁ i → Γ.IsB2 π j₂ s₂ k₂ i → Γ.degS i = 2 →
      ∃ m₁ m₂ : Fin Γ.es.length, m₁ ≠ m₂ ∧
        (Γ.es.get m₁).ghost = false ∧ (Γ.es.get m₂).ghost = false ∧
        ((Γ.es.get m₁).u = Sum.inr i ∨ (Γ.es.get m₁).v = Sum.inr i) ∧
        ((Γ.es.get m₂).u = Sum.inr i ∨ (Γ.es.get m₂).v = Sum.inr i) ∧
        (s₁ = false → ∃ w rest, Γ.path j₁ = (k₁, Sum.inr i) :: (m₁, w) :: rest) ∧
        (s₁ = true → ∃ pre : List (Fin Γ.es.length × NV p q),
          Γ.path j₁ = pre ++ [(m₁, Sum.inr i), (k₁, Sum.inl (Sum.inr j₁))]) ∧
        (s₂ = false → ∃ w rest, Γ.path j₂ = (k₂, Sum.inr i) :: (m₂, w) :: rest) ∧
        (s₂ = true → ∃ pre : List (Fin Γ.es.length × NV p q),
          Γ.path j₂ = pre ++ [(m₂, Sum.inr i), (k₂, Sum.inl (Sum.inr j₂))]) ∧
        ∀ k : Fin Γ.es.length, (Γ.es.get k).ghost = false →
          ((Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i) → k = m₁ ∨ k = m₂ := by
  classical
  intro p q Γ π i j₁ j₂ s₁ s₂ k₁ k₂ hG hN hj h₁ h₂ hdeg
  obtain ⟨m₁, g₁, a₁, ⟨w₁, hw₁⟩, f₁, t₁⟩ := anpKey4_side hG hN h₁
  obtain ⟨m₂, g₂, a₂, ⟨w₂, hw₂⟩, f₂, t₂⟩ := anpKey4_side hG hN h₂
  have hm : m₁ ≠ m₂ := hN.2.2.2.1 j₁ j₂ hj _ hw₁ _ hw₂
  refine ⟨m₁, m₂, hm, g₁, g₂, a₁, a₂, f₁, t₁, f₂, t₂, ?_⟩
  intro k hk hki
  by_contra hcon
  push Not at hcon
  have hsub : ({m₁, m₂, k} : Finset (Fin Γ.es.length)) ⊆ Finset.univ.filter fun k : Fin Γ.es.length =>
      (Γ.es.get k).ghost = false ∧ ((Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact ⟨g₁, a₁⟩
    · exact ⟨g₂, a₂⟩
    · exact ⟨hk, hki⟩
  have h3 : ({m₁, m₂, k} : Finset (Fin Γ.es.length)).card = 3 :=
    Finset.card_eq_three.2 ⟨m₁, m₂, k, hm, fun h => hcon.1 h.symm, fun h => hcon.2 h.symm, rfl⟩
  have := Finset.card_le_card hsub
  rw [h3, ← anpKey4_degS_eq, hdeg] at this
  omega

end NeSolid

/-! ## 2. The double A2 replacement at a first or last step of two ghost-free paths -/

section Gh2

/-- The double A2 replacement of `anpKey3_gh2` for two ending edges (first or last step) of two distinct ghost-free
paths, not necessarily one-step paths (the merged `anpKey3_gh2_props` asks for one-step paths): the ghost condition
and the nested properties are kept, two solid edges are lost, exactly the paths `r₁`, `r₂` stop being ghost free, and
the two factors split off. -/
theorem anpKey4_gh2_props :
    ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → ∀ (r₁ r₂ : Fin p), r₁ ≠ r₂ →
      ∀ st₁ st₂ : Fin Γ.es.length × NV p q,
        st₁ ∈ Γ.path r₁ → ((Γ.path r₁).head? = some st₁ ∨ (Γ.path r₁).getLast? = some st₁) →
        st₂ ∈ Γ.path r₂ → ((Γ.path r₂).head? = some st₂ ∨ (Γ.path r₂).getLast? = some st₂) →
        Γ.noGhostPath r₁ = true → Γ.noGhostPath r₂ = true →
        (anpKey3_gh2 Γ st₁.1 st₂.1).GhostOK ∧ (anpKey3_gh2 Γ st₁.1 st₂.1).IsNested ∧
          (anpKey3_gh2 Γ st₁.1 st₂.1).nSolid + 2 = Γ.nSolid ∧
          (∀ r, (anpKey3_gh2 Γ st₁.1 st₂.1).noGhostPath r = true ↔
            Γ.noGhostPath r = true ∧ r ≠ r₁ ∧ r ≠ r₂) ∧
          (∀ (ι : Type) (ξ : ι → ι → ℝ) (lab : NV p q → ι),
            anpKey2_ep Γ ξ lab = ξ (lab (Γ.es.get st₁.1).u) (lab (Γ.es.get st₁.1).v) *
              ξ (lab (Γ.es.get st₂.1).u) (lab (Γ.es.get st₂.1).v) *
                anpKey2_ep (anpKey3_gh2 Γ st₁.1 st₂.1) ξ lab) := by
  intro p q Γ hG hN r₁ r₂ hr st₁ st₂ hm₁ he₁ hm₂ he₂ hn₁ hn₂
  have g₁ : (Γ.es.get st₁.1).ghost = false := (anpKey2_noGhost_iff Γ r₁).1 hn₁ _ hm₁
  have g₂ : (Γ.es.get st₂.1).ghost = false := (anpKey2_noGhost_iff Γ r₂).1 hn₂ _ hm₂
  have hne : st₁.1 ≠ st₂.1 := fun h => hN.2.2.2.1 r₁ r₂ hr _ hm₁ _ hm₂ h
  have hG₁ : (Γ.ghostify st₁.1).GhostOK := anpKey_ghostify_ghostOK Γ hG hN hn₁ hm₁ he₁
  have hN₁ : (Γ.ghostify st₁.1).IsNested := anpKey_ghostify_nested Γ st₁.1 hN
  have hm₂' : (Γ.ghostifyIdx st₁.1 st₂.1, st₂.2) ∈ (Γ.ghostify st₁.1).path r₂ := by
    rw [anpKey_gf_path]
    exact List.mem_map.2 ⟨st₂, hm₂, rfl⟩
  have hn₂' : (Γ.ghostify st₁.1).noGhostPath r₂ = true :=
    (anpKey_gf_noGhostPath_iff Γ hN (st₀ := st₁) hm₁ r₂).2 ⟨hn₂, hr.symm⟩
  have he₂' : ((Γ.ghostify st₁.1).path r₂).head? = some (Γ.ghostifyIdx st₁.1 st₂.1, st₂.2) ∨
      ((Γ.ghostify st₁.1).path r₂).getLast? = some (Γ.ghostifyIdx st₁.1 st₂.1, st₂.2) := by
    rw [anpKey_gf_path]
    rcases he₂ with h | h
    · left; rw [List.head?_map, h]; rfl
    · right; rw [List.getLast?_map, h]; rfl
  have hG₂ : (anpKey3_gh2 Γ st₁.1 st₂.1).GhostOK :=
    anpKey_ghostify_ghostOK (Γ.ghostify st₁.1) hG₁ hN₁ (st₀ := (Γ.ghostifyIdx st₁.1 st₂.1, st₂.2)) hn₂' hm₂' he₂'
  have hN₂ : (anpKey3_gh2 Γ st₁.1 st₂.1).IsNested :=
    anpKey_ghostify_nested (Γ.ghostify st₁.1) (Γ.ghostifyIdx st₁.1 st₂.1) hN₁
  have hs₁ : (Γ.ghostify st₁.1).nSolid + 1 = Γ.nSolid :=
    anpKey_ghostify_nSolid Γ (st₀ := st₁) hn₁ hm₁
  have hs₂ : (anpKey3_gh2 Γ st₁.1 st₂.1).nSolid + 1 = (Γ.ghostify st₁.1).nSolid :=
    anpKey_ghostify_nSolid (Γ.ghostify st₁.1) (st₀ := (Γ.ghostifyIdx st₁.1 st₂.1, st₂.2)) hn₂' hm₂'
  refine ⟨hG₂, hN₂, by omega, ?_, ?_⟩
  · intro r
    have h1 := anpKey_gf_noGhostPath_iff Γ hN (st₀ := st₁) hm₁ r
    have h2 := anpKey_gf_noGhostPath_iff (Γ.ghostify st₁.1) hN₁
      (st₀ := (Γ.ghostifyIdx st₁.1 st₂.1, st₂.2)) hm₂' r
    show ((Γ.ghostify st₁.1).ghostify (Γ.ghostifyIdx st₁.1 st₂.1)).noGhostPath r = true ↔ _
    rw [h2, h1]
    tauto
  · intro ι ξ lab
    have e1 := anpKey2_ep_ghostify Γ ξ lab st₁.1 g₁
    have g₂' : ((Γ.ghostify st₁.1).es.get (Γ.ghostifyIdx st₁.1 st₂.1)).ghost = false := by
      rw [anpKey_gf_ghost']
      have h0 : decide (st₂.1 = st₁.1) = false := by simp [hne.symm]
      rw [h0, g₂]
      rfl
    have e2 := anpKey2_ep_ghostify (Γ.ghostify st₁.1) ξ lab (Γ.ghostifyIdx st₁.1 st₂.1) g₂'
    have hu : ((Γ.ghostify st₁.1).es.get (Γ.ghostifyIdx st₁.1 st₂.1)).u = (Γ.es.get st₂.1).u :=
      anpKey_gf_u Γ st₁.1 st₂.1
    have hv : ((Γ.ghostify st₁.1).es.get (Γ.ghostifyIdx st₁.1 st₂.1)).v = (Γ.es.get st₂.1).v :=
      anpKey_gf_v Γ st₁.1 st₂.1
    rw [hu, hv] at e2
    rw [e1, e2]
    ring

/-- The edges of the double A2 replacement: every solid edge has the endpoints of a solid edge `i` of `Γ`, with
`i ∉ {e₁, e₂}`. -/
theorem anpKey4_gh2_edges {p q : ℕ} (Γ : NGraph p q) (e₁ e₂ : Fin Γ.es.length) :
    ∀ e ∈ (anpKey3_gh2 Γ e₁ e₂).es, e.ghost = false →
      ∃ i : Fin Γ.es.length, e.u = (Γ.es.get i).u ∧ e.v = (Γ.es.get i).v ∧ (Γ.es.get i).ghost = false ∧
        i ≠ e₁ ∧ i ≠ e₂ := by
  intro e he hg
  obtain ⟨j'', rfl⟩ := List.mem_iff_get.1 he
  obtain ⟨j', rfl⟩ := anpKey_gf_idx_surj (Γ.ghostify e₁) (Γ.ghostifyIdx e₁ e₂) j''
  obtain ⟨i, rfl⟩ := anpKey_gf_idx_surj Γ e₁ j'
  have hu₂ := anpKey_gf_u (Γ.ghostify e₁) (Γ.ghostifyIdx e₁ e₂) (Γ.ghostifyIdx e₁ i)
  have hv₂ := anpKey_gf_v (Γ.ghostify e₁) (Γ.ghostifyIdx e₁ e₂) (Γ.ghostifyIdx e₁ i)
  have hu₁ := anpKey_gf_u Γ e₁ i
  have hv₁ := anpKey_gf_v Γ e₁ i
  have hgh := anpKey_gf_ghost' (Γ.ghostify e₁) (Γ.ghostifyIdx e₁ e₂) (Γ.ghostifyIdx e₁ i)
  have hgh₁ := anpKey_gf_ghost' Γ e₁ i
  refine ⟨i, hu₂.trans hu₁, hv₂.trans hv₁, ?_⟩
  have hg' : ((anpKey3_gh2 Γ e₁ e₂).es.get (((Γ.ghostify e₁).ghostifyIdx (Γ.ghostifyIdx e₁ e₂)) (Γ.ghostifyIdx e₁ i))).ghost = false := hg
  rw [hgh] at hg'
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hg'
  obtain ⟨hne₂, hg₁⟩ := hg'
  rw [hgh₁] at hg₁
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hg₁
  refine ⟨hg₁.2, hg₁.1, fun h => hne₂ ?_⟩
  rw [h]

end Gh2

/-! ## 3. Positions in the fixed graph -/

section Pos

variable {p q : ℕ} (Γ : NGraph p (q + 1)) (i₀ : Fin (q + 1))

/-- `s = false`: the path `𝔓_j` starts `(k, α), (m, w), …`; the segment after the arrival `(k, α)` starts with
the step `m`, so `m` is the first step of a segment `r' ≠ ⟨j, 0⟩` of `𝔓_j`. -/
theorem anpKey4_pos_false (s₀ : anpKey2_Seg Γ i₀) {j : Fin p} {k m : Fin Γ.es.length} {w : NV p (q + 1)}
    {rest : List (Fin Γ.es.length × NV p (q + 1))}
    (hp : Γ.path j = (k, Sum.inr i₀) :: (m, w) :: rest) :
    ∃ (r : Fin (anpKey2_P Γ i₀)) (v : NV (anpKey2_P Γ i₀) q), anpKey2_own Γ i₀ r = j ∧
      ((anpKey2_fixV Γ i₀ s₀).path r).head? = some (anpKey2_em Γ i₀ s₀ m, v) := by
  have hA : anpKey2_isA (Sum.inr i₀) ((k, Sum.inr i₀) : Fin Γ.es.length × NV p (q + 1)) = true :=
    (anpKey2_isA_eq _ _).2 rfl
  have hK : 1 ≤ anpKey2_K Γ i₀ j := by
    unfold anpKey2_K
    rw [hp, List.countP_cons_of_pos hA]
    omega
  refine ⟨anpKey2_ee Γ i₀ ⟨j, ⟨1, by omega⟩⟩,
    anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ ⟨j, ⟨1, by omega⟩⟩))) w, by simp [anpKey2_own], ?_⟩
  rw [anpKey2_fixV_path]
  have hst : anpKey2_steps Γ i₀ ⟨j, ⟨1, by omega⟩⟩ =
      anpKey2_seg (anpKey2_isA (Sum.inr i₀)) ((m, w) :: rest) 0 := by
    unfold anpKey2_steps
    simp only
    rw [hp, anpKey2_seg_succ_pos _ _ _ hA]
  obtain ⟨t, ht⟩ := anpKey2_seg_head (anpKey2_isA (Sum.inr i₀)) (m, w) rest
  rw [hst, ht]
  rfl

/-- `s = true`: the step `(m, α)` arrives at `α`, so it is the last step of its segment. -/
theorem anpKey4_pos_true (s₀ : anpKey2_Seg Γ i₀) {j : Fin p} {k m : Fin Γ.es.length}
    {pre : List (Fin Γ.es.length × NV p (q + 1))}
    (hp : Γ.path j = pre ++ [(m, Sum.inr i₀), (k, Sum.inl (Sum.inr j))]) :
    ∃ (r : Fin (anpKey2_P Γ i₀)) (v : NV (anpKey2_P Γ i₀) q), anpKey2_own Γ i₀ r = j ∧
      ((anpKey2_fixV Γ i₀ s₀).path r).getLast? = some (anpKey2_em Γ i₀ s₀ m, v) := by
  have hm : (m, Sum.inr i₀) ∈ Γ.path j := by rw [hp]; simp
  obtain ⟨r, hr⟩ := anpKey2_cover Γ i₀ hm
  obtain ⟨-, hlast⟩ := anpKey2_steps_arrival Γ i₀ ⟨j, r⟩ _ hr rfl
  refine ⟨anpKey2_ee Γ i₀ ⟨j, r⟩,
    anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ ⟨j, r⟩))) (Sum.inr i₀), by simp [anpKey2_own], ?_⟩
  rw [anpKey2_fixV_path, List.getLast?_map, hlast]
  rfl

/-- The segment `r'` of `𝔓_j` that carries the solid edge `m` next to the B2 edge `k` as its first (`s = false`) or
last (`s = true`) step: `r'` is ghost free in the fixed graph (`r_t = [k]` is the unique segment with the ghost). -/
theorem anpKey4_seg (hG : Γ.GhostOK) (hN : Γ.IsNested) (s₀ : anpKey2_Seg Γ i₀) {j : Fin p} {s : Bool}
    {k m : Fin Γ.es.length} (hk : Γ.EndAt j s k i₀) (gk : (Γ.es.get k).ghost = true)
    (gm : (Γ.es.get m).ghost = false)
    (hpf : s = false → ∃ (w : NV p (q + 1)) (rest : List (Fin Γ.es.length × NV p (q + 1))),
      Γ.path j = (k, Sum.inr i₀) :: (m, w) :: rest)
    (hpt : s = true → ∃ pre : List (Fin Γ.es.length × NV p (q + 1)),
      Γ.path j = pre ++ [(m, Sum.inr i₀), (k, Sum.inl (Sum.inr j))]) :
    ∃ (r : Fin (anpKey2_P Γ i₀)) (v : NV (anpKey2_P Γ i₀) q), anpKey2_own Γ i₀ r = j ∧
      (anpKey2_fixV Γ i₀ s₀).noGhostPath r = true ∧
      (anpKey2_em Γ i₀ s₀ m, v) ∈ (anpKey2_fixV Γ i₀ s₀).path r ∧
      (((anpKey2_fixV Γ i₀ s₀).path r).head? = some (anpKey2_em Γ i₀ s₀ m, v) ∨
        ((anpKey2_fixV Γ i₀ s₀).path r).getLast? = some (anpKey2_em Γ i₀ s₀ m, v)) := by
  obtain ⟨rt, hrt_own, hrt_path, -⟩ := anpKey2_fixV_end Γ i₀ hN s₀ hk
  obtain ⟨r, v, hown, hend⟩ : ∃ (r : Fin (anpKey2_P Γ i₀)) (v : NV (anpKey2_P Γ i₀) q),
      anpKey2_own Γ i₀ r = j ∧
      (((anpKey2_fixV Γ i₀ s₀).path r).head? = some (anpKey2_em Γ i₀ s₀ m, v) ∨
        ((anpKey2_fixV Γ i₀ s₀).path r).getLast? = some (anpKey2_em Γ i₀ s₀ m, v)) := by
    cases s
    · obtain ⟨w, rest, hp⟩ := hpf rfl
      obtain ⟨r, v, h1, h2⟩ := anpKey4_pos_false Γ i₀ s₀ hp
      exact ⟨r, v, h1, Or.inl h2⟩
    · obtain ⟨pre, hp⟩ := hpt rfl
      obtain ⟨r, v, h1, h2⟩ := anpKey4_pos_true Γ i₀ s₀ hp
      exact ⟨r, v, h1, Or.inr h2⟩
  have hmem : (anpKey2_em Γ i₀ s₀ m, v) ∈ (anpKey2_fixV Γ i₀ s₀).path r := by
    rcases hend with h | h
    · exact List.mem_of_mem_head? h
    · exact List.mem_of_getLast? h
  have hne : r ≠ rt := by
    intro h
    subst h
    rw [hrt_path] at hend
    have hkm : k = m := by
      rcases hend with h | h <;> simp at h <;> exact h.1
    rw [hkm] at gk
    rw [gk] at gm
    exact Bool.noConfusion gm
  have hrtf : (anpKey2_fixV Γ i₀ s₀).noGhostPath rt = false := by
    by_contra hcon
    have ht : (anpKey2_fixV Γ i₀ s₀).noGhostPath rt = true := by simpa using hcon
    have := (anpKey2_noGhost_iff _ rt).1 ht (anpKey2_em Γ i₀ s₀ k, Sum.inl (Sum.inr rt))
      (by rw [hrt_path]; simp)
    simp only [anpKey2_fixV_ghost, gk] at this
    exact Bool.noConfusion this
  have hj : Γ.noGhostPath j = false := anpKey4_ng_false (π := fun _ _ => false) ⟨hk, gk⟩
  have hng : (anpKey2_fixV Γ i₀ s₀).noGhostPath r = true := by
    by_contra hcon
    have hf : (anpKey2_fixV Γ i₀ s₀).noGhostPath r = false := by simpa using hcon
    obtain ⟨r0, -, huniq⟩ := anpKey2_fixV_noGhost2 Γ i₀ hG hN s₀ j hj
    have h1 : r = r0 := huniq r ⟨hown, hf⟩
    have h2 : rt = r0 := huniq rt ⟨hrt_own, hrtf⟩
    exact hne (h1.trans h2.symm)
  exact ⟨r, v, hown, hng, hmem, hend⟩

end Pos

/-! ## 4. The factor at the fixed vertex and the `x`-independence (`(kwuyayw_case3)`, `7_8:1344-1347`) -/

section Factor

/-- Away from `α_{i₀}` the label of a vertex of `Γ` does not depend on the label `x` of `α_{i₀}`. -/
theorem anpKey4_lab_indep {p q : ℕ} {ι : Type} (a b : Fin p → ι) (i₀ : Fin (q + 1)) (x x₀ : ι) (ℓ : Fin q → ι)
    (v : NV p (q + 1)) (hv : v ≠ Sum.inr i₀) :
    Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) v =
      Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x₀ ℓ : Fin (q + 1) → ι) v := by
  rcases v with (j | j) | i
  · rfl
  · rfl
  · have hi : i ≠ i₀ := fun h => hv (by rw [h])
    obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hi
    simp only [Sum.elim_inr, Fin.insertNth_apply_succAbove]

/-- A solid edge `m` at the fixed vertex contributes `ξ(x, y)` with `y` free of `x` (the label of its other end
`β`, `7_8:1246`): `y` depends on the labels of the other vertices only, not on `x`. -/
theorem anpKey4_factor {ι : Type} {p q p' : ℕ} (Γ : NGraph p (q + 1)) (Γ' : NGraph p' q)
    (ξ : ι → ι → ℝ) (hsym : ∀ α β, ξ α β = ξ β α) (a b : Fin p → ι) (i₀ : Fin (q + 1)) (ℓ : Fin q → ι)
    (lab : ι → NV p' q → ι) (em : Fin Γ.es.length → Fin Γ'.es.length)
    (hu : ∀ x k, lab x (Γ'.es.get (em k)).u =
      Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).u)
    (hv : ∀ x k, lab x (Γ'.es.get (em k)).v =
      Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).v)
    {m : Fin Γ.es.length} (hm : (Γ.es.get m).u = Sum.inr i₀ ∨ (Γ.es.get m).v = Sum.inr i₀)
    (hne : (Γ.es.get m).u ≠ (Γ.es.get m).v) (x₀ : ι) :
    ∃ y : ι, ∀ x : ι, ξ (lab x (Γ'.es.get (em m)).u) (lab x (Γ'.es.get (em m)).v) = ξ x y := by
  rcases hm with h | h
  · refine ⟨Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x₀ ℓ : Fin (q + 1) → ι)
      (Γ.es.get m).v, fun x => ?_⟩
    rw [hu, hv, h, anpKey4_lab_indep a b i₀ x x₀ ℓ _ (fun h' => hne (h.trans h'.symm))]
    simp only [Sum.elim_inr, Fin.insertNth_apply_same]
  · refine ⟨Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x₀ ℓ : Fin (q + 1) → ι)
      (Γ.es.get m).u, fun x => ?_⟩
    rw [hu, hv, h, anpKey4_lab_indep a b i₀ x x₀ ℓ _ (fun h' => hne (h'.trans h.symm))]
    simp only [Sum.elim_inr, Fin.insertNth_apply_same]
    exact hsym _ _

/-- An edge `k` of `Γ` not at the fixed vertex has a factor that does not depend on `x`. -/
theorem anpKey4_indep {ι : Type} {p q p' : ℕ} (Γ : NGraph p (q + 1)) (Γ' : NGraph p' q)
    (ξ : ι → ι → ℝ) (a b : Fin p → ι) (i₀ : Fin (q + 1)) (ℓ : Fin q → ι)
    (lab : ι → NV p' q → ι) (em : Fin Γ.es.length → Fin Γ'.es.length)
    (hu : ∀ x k, lab x (Γ'.es.get (em k)).u =
      Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).u)
    (hv : ∀ x k, lab x (Γ'.es.get (em k)).v =
      Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).v)
    {k : Fin Γ.es.length} (hk : (Γ.es.get k).u ≠ Sum.inr i₀ ∧ (Γ.es.get k).v ≠ Sum.inr i₀) (x x₀ : ι) :
    ξ (lab x (Γ'.es.get (em k)).u) (lab x (Γ'.es.get (em k)).v) =
      ξ (lab x₀ (Γ'.es.get (em k)).u) (lab x₀ (Γ'.es.get (em k)).v) := by
  rw [hu x k, hv x k, hu x₀ k, hv x₀ k, anpKey4_lab_indep a b i₀ x x₀ ℓ _ hk.1,
    anpKey4_lab_indep a b i₀ x x₀ ℓ _ hk.2]

/-- The product of the edge factors depends only on the labels of the solid edges. -/
theorem anpKey4_ep_congr {ι : Type*} {p q : ℕ} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (lab₁ lab₂ : NV p q → ι)
    (h : ∀ e ∈ Γ.es, e.ghost = false → ξ (lab₁ e.u) (lab₁ e.v) = ξ (lab₂ e.u) (lab₂ e.v)) :
    anpKey2_ep Γ ξ lab₁ = anpKey2_ep Γ ξ lab₂ := by
  unfold anpKey2_ep
  congr 1
  refine List.map_congr_left fun e he => ?_
  cases hg : e.ghost
  · simp only [Bool.false_eq_true, ite_false]
    exact h e he hg
  · simp

/-- (F2) for the explicit fixed graph: the labels of the endpoints of `em k` are those of `k` under
`Fin.insertNth i₀ x ℓ`. -/
theorem anpKey4_F2 {p q : ℕ} (Γ : NGraph p (q + 1)) (i₀ : Fin (q + 1)) (s₀ : anpKey2_Seg Γ i₀)
    (hs₀ : s₀.2.val ≠ anpKey2_K Γ i₀ s₀.1) {ι : Type} (a b : Fin p → ι) (ℓ : Fin q → ι) (k : Fin Γ.es.length) :
    (∀ x : ι, Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (anpKey2_ea Γ i₀ r))
        (fun r => anpKey2_fixLab a b x (anpKey2_eb Γ i₀ r))) ℓ
          ((anpKey2_fixV Γ i₀ s₀).es.get (anpKey2_em Γ i₀ s₀ k)).u =
        Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).u) ∧
    (∀ x : ι, Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (anpKey2_ea Γ i₀ r))
        (fun r => anpKey2_fixLab a b x (anpKey2_eb Γ i₀ r))) ℓ
          ((anpKey2_fixV Γ i₀ s₀).es.get (anpKey2_em Γ i₀ s₀ k)).v =
        Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).v) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [(anpKey2_fixV_edge Γ i₀ s₀ k).1]
    exact anpKey2_lab Γ i₀ a b x ℓ (anpKey2_tgt_none Γ i₀ s₀ hs₀ k) _
  · rw [(anpKey2_fixV_edge Γ i₀ s₀ k).2]
    exact anpKey2_lab Γ i₀ a b x ℓ (anpKey2_tgt_none Γ i₀ s₀ hs₀ k) _

end Factor

/-! ## 5. The reduction (`7_8:1250-1348`, existential) -/

/-- The reduction of case (III) (`7_8:1250-1348`; the construction differs from the paper's, see the report): fix
`α_{i₀}`, keep the B2 edges as one-step ghost paths, and make the solid edges `m₁`, `m₂` next to them ghost.  The new
graph `Γ''` has one internal vertex fewer, the ghost condition and the nested properties, the same `ord`, paths `r` of
old paths `own r` with ends `ea r`, `eb r` (`none`: a free external label `x₀`), ghost-free old paths stay ghost free,
and the value on `𝐃_π` is at most `θ` times the value of `Γ''` at any `x₀` (`(kwuyayw_case3)`, first steps). -/
theorem anpKey4_reduce :
    ∀ (p q : ℕ) (Γ : NGraph p (q + 1)) (π : Fin (q + 1) → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → AnpCaseIII Γ π →
      ∃ (p'' : ℕ) (Γ'' : NGraph p'' q) (ea eb : Fin p'' → Option (Fin p ⊕ Fin p)) (own : Fin p'' → Fin p),
        (Γ''.GhostOK ∧ Γ''.IsNested) ∧ Γ''.ordN = Γ.ordN ∧
        (∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none) ∧
        (∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none) ∧
        (∀ j, ∃! r, ea r = some (Sum.inl j)) ∧ (∀ j, ∃! r, eb r = some (Sum.inr j)) ∧
        (∀ r, Γ.noGhostPath (own r) = true → Γ''.noGhostPath r = true) ∧
        (∀ (d L : ℕ) [NeZero L] (ξ : Zd d L → Zd d L → ℝ) (θ : ℝ),
          (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) → (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
          ∀ (a b : Fin p → Zd d L) (x₀ : Zd d L),
            Γ.valOn ξ a b (anpKey2_region a b π) ≤
              θ * Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (ea r)) (fun r => anpKey2_fixLab a b x₀ (eb r))) := by
  intro p q Γ π hG hN hcase
  obtain ⟨i₀, j₁, j₂, s₁, s₂, k₁, k₂, hne, h₁, h₂, hdeg⟩ := hcase
  have hj := anpKey4_caseIII_ne p (q + 1) Γ π i₀ j₁ j₂ s₁ s₂ k₁ k₂ hG hN hne h₁ h₂
  obtain ⟨m₁, m₂, hm, gm₁, gm₂, am₁, am₂, f₁, t₁, f₂, t₂, hall⟩ :=
    anpKey4_solid p (q + 1) Γ π i₀ j₁ j₂ s₁ s₂ k₁ k₂ hG hN hj h₁ h₂ hdeg
  obtain ⟨s₀, hs₀⟩ := anpKey2_exists_s₀ Γ i₀ hN
  have hG' := anpKey2_fixV_ghostOK Γ i₀ hG hN s₀
  have hN' := anpKey2_fixV_nested Γ i₀ hN s₀ hs₀
  obtain ⟨r₁, v₁, hown₁, hng₁, hmem₁, hend₁⟩ := anpKey4_seg Γ i₀ hG hN s₀ h₁.1 h₁.2 gm₁ f₁ t₁
  obtain ⟨r₂, v₂, hown₂, hng₂, hmem₂, hend₂⟩ := anpKey4_seg Γ i₀ hG hN s₀ h₂.1 h₂.2 gm₂ f₂ t₂
  have hr : r₁ ≠ r₂ := fun h => hj (by rw [← hown₁, ← hown₂, h])
  obtain ⟨hG'', hN'', hS'', hng'', hep⟩ := anpKey4_gh2_props _ _ (anpKey2_fixV Γ i₀ s₀) hG' hN' r₁ r₂ hr
    (anpKey2_em Γ i₀ s₀ m₁, v₁) (anpKey2_em Γ i₀ s₀ m₂, v₂) hmem₁ hend₁ hmem₂ hend₂ hng₁ hng₂
  dsimp only at hG'' hN'' hS'' hng'' hep
  refine ⟨anpKey2_P Γ i₀, anpKey3_gh2 (anpKey2_fixV Γ i₀ s₀) (anpKey2_em Γ i₀ s₀ m₁) (anpKey2_em Γ i₀ s₀ m₂),
    anpKey2_ea Γ i₀, anpKey2_eb Γ i₀, anpKey2_own Γ i₀, ⟨hG'', hN''⟩, ?_, ?_, ?_, anpKey2_ea_unique Γ i₀,
    anpKey2_eb_unique Γ i₀, ?_, ?_⟩
  · have h : (anpKey3_gh2 (anpKey2_fixV Γ i₀ s₀) (anpKey2_em Γ i₀ s₀ m₁) (anpKey2_em Γ i₀ s₀ m₂)).nSolid + 2 =
        Γ.nSolid := by
      rw [← anpKey2_fixV_nSolid Γ i₀ s₀]
      exact hS''
    unfold NGraph.ordN
    simp only [ord]
    omega
  · intro r
    unfold anpKey2_ea anpKey2_own
    split_ifs <;> simp
  · intro r
    unfold anpKey2_eb anpKey2_own
    split_ifs <;> simp
  · intro r hr0
    refine (hng'' r).2 ⟨anpKey2_fixV_noGhost1 Γ i₀ s₀ r hr0, ?_, ?_⟩
    · intro h
      subst h
      rw [hown₁, anpKey4_ng_false h₁] at hr0
      exact Bool.noConfusion hr0
    · intro h
      subst h
      rw [hown₂, anpKey4_ng_false h₂] at hr0
      exact Bool.noConfusion hr0
  · intro d L _ ξ θ hξ hrow a b x₀
    have hnn : ∀ α β, 0 ≤ ξ α β := fun α β => (hξ α β).1
    have hsym : ∀ α β, ξ α β = ξ β α := fun α β => (hξ α β).2
    refine (anpKey2_fixV_value Γ i₀ s₀ hs₀ ξ hnn a b π).trans ?_
    set Γ' := anpKey2_fixV Γ i₀ s₀ with hΓ'
    set Γ'' := anpKey3_gh2 Γ' (anpKey2_em Γ i₀ s₀ m₁) (anpKey2_em Γ i₀ s₀ m₂) with hΓ''
    set R := anpKey2_regionOne a b (π i₀) with hR
    -- the labelling of the fixed graph with the fixed vertex labelled `x` and the internal labels `ℓ`
    let lab : Zd d L → (Fin q → Zd d L) → NV (anpKey2_P Γ i₀) q → Zd d L := fun x ℓ =>
      Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (anpKey2_ea Γ i₀ r))
        (fun r => anpKey2_fixLab a b x (anpKey2_eb Γ i₀ r))) ℓ
    have hF2 := fun ℓ k => anpKey4_F2 Γ i₀ s₀ hs₀ a b ℓ k
    have hne₁ : (Γ.es.get m₁).u ≠ (Γ.es.get m₁).v := hN.1 _ (List.get_mem _ _)
    have hne₂ : (Γ.es.get m₂).u ≠ (Γ.es.get m₂).v := hN.1 _ (List.get_mem _ _)
    -- the factors at the fixed vertex
    have hy : ∀ ℓ : Fin q → Zd d L, ∃ y₁ y₂ : Zd d L, ∀ x : Zd d L,
        ξ (lab x ℓ (Γ'.es.get (anpKey2_em Γ i₀ s₀ m₁)).u) (lab x ℓ (Γ'.es.get (anpKey2_em Γ i₀ s₀ m₁)).v) = ξ x y₁ ∧
        ξ (lab x ℓ (Γ'.es.get (anpKey2_em Γ i₀ s₀ m₂)).u) (lab x ℓ (Γ'.es.get (anpKey2_em Γ i₀ s₀ m₂)).v) = ξ x y₂ := by
      intro ℓ
      obtain ⟨y₁, hy₁⟩ := anpKey4_factor Γ Γ' ξ hsym a b i₀ ℓ (fun x => lab x ℓ) (anpKey2_em Γ i₀ s₀)
        (fun x k => (hF2 ℓ k).1 x) (fun x k => (hF2 ℓ k).2 x) am₁ hne₁ x₀
      obtain ⟨y₂, hy₂⟩ := anpKey4_factor Γ Γ' ξ hsym a b i₀ ℓ (fun x => lab x ℓ) (anpKey2_em Γ i₀ s₀)
        (fun x k => (hF2 ℓ k).1 x) (fun x k => (hF2 ℓ k).2 x) am₂ hne₂ x₀
      exact ⟨y₁, y₂, fun x => ⟨hy₁ x, hy₂ x⟩⟩
    choose y₁ y₂ hy using hy
    -- the `x`-independence of the remaining factors (`deg_s(α_{i₀}) = 2`)
    have hepind : ∀ (x : Zd d L) (ℓ : Fin q → Zd d L),
        anpKey2_ep Γ'' ξ (lab x ℓ) = anpKey2_ep Γ'' ξ (lab x₀ ℓ) := by
      intro x ℓ
      refine anpKey4_ep_congr Γ'' ξ _ _ fun e he hg => ?_
      obtain ⟨i, hu, hv, hgi, h1, h2⟩ := anpKey4_gh2_edges Γ' _ _ e he hg
      obtain ⟨k, rfl⟩ := (anpKey2_em Γ i₀ s₀).surjective i
      have hgk : (Γ.es.get k).ghost = false := by
        rw [← anpKey2_fixV_ghost Γ i₀ s₀ k]
        exact hgi
      have hk₁ : k ≠ m₁ := fun h => h1 (by rw [h])
      have hk₂ : k ≠ m₂ := fun h => h2 (by rw [h])
      have hk : (Γ.es.get k).u ≠ Sum.inr i₀ ∧ (Γ.es.get k).v ≠ Sum.inr i₀ := by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases hall k hgk (Or.inl h) with h' | h'
          · exact hk₁ h'
          · exact hk₂ h'
        · rcases hall k hgk (Or.inr h) with h' | h'
          · exact hk₁ h'
          · exact hk₂ h'
      rw [hu, hv]
      have := anpKey4_indep Γ Γ' ξ a b i₀ ℓ (fun x => lab x ℓ) (anpKey2_em Γ i₀ s₀)
        (fun x k => (hF2 ℓ k).1 x) (fun x k => (hF2 ℓ k).2 x) hk x x₀
      exact this
    have hstep : ∀ x : Zd d L,
        Γ'.val ξ (fun r => anpKey2_fixLab a b x (anpKey2_ea Γ i₀ r))
          (fun r => anpKey2_fixLab a b x (anpKey2_eb Γ i₀ r)) =
        ∑ ℓ : Fin q → Zd d L, ξ x (y₁ ℓ) * ξ x (y₂ ℓ) * anpKey2_ep Γ'' ξ (lab x₀ ℓ) := by
      intro x
      unfold NGraph.val
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      show anpKey2_ep Γ' ξ (lab x ℓ) = _
      rw [hep (Zd d L) ξ (lab x ℓ), (hy ℓ x).1, (hy ℓ x).2, hepind x ℓ]
    calc ∑ x ∈ R, Γ'.val ξ (fun r => anpKey2_fixLab a b x (anpKey2_ea Γ i₀ r))
          (fun r => anpKey2_fixLab a b x (anpKey2_eb Γ i₀ r))
        = ∑ x ∈ R, ∑ ℓ : Fin q → Zd d L, ξ x (y₁ ℓ) * ξ x (y₂ ℓ) * anpKey2_ep Γ'' ξ (lab x₀ ℓ) :=
          Finset.sum_congr rfl fun x _ => hstep x
      _ = ∑ ℓ : Fin q → Zd d L, (∑ x ∈ R, ξ (y₁ ℓ) x * ξ (y₂ ℓ) x) * anpKey2_ep Γ'' ξ (lab x₀ ℓ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hsym x (y₁ ℓ), hsym x (y₂ ℓ)]
      _ ≤ ∑ ℓ : Fin q → Zd d L, θ * anpKey2_ep Γ'' ξ (lab x₀ ℓ) :=
          Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_right
            (anpKey3_sum_xx ξ θ hnn hrow R _ _) (anpKey2_ep_nonneg Γ'' ξ hnn _)
      _ = θ * Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (anpKey2_ea Γ i₀ r))
            (fun r => anpKey2_fixLab a b x₀ (anpKey2_eb Γ i₀ r)) := by
          rw [← Finset.mul_sum]
          rfl

/-! ## 6. The assembly and the target (`7_8:1344-1348`) -/

/-- The assembly: the reduction (`anpKey4_reduce`) and the induction hypothesis give the case pin, constants
`(C, c) ↦ (C'', c''/2)` (`7_8:1347`).  Every ghost-free old path has a far segment (`anpKey3_far_gen` at the free label
`x₀`, subcase (a)) that is a ghost-free path of the new graph, the other ghost-free paths of the new graph carry the
bound `ψ(0)`, and `Σ ξ ξ ≤ θ` was used in the reduction. -/
theorem anpKey4_of_reduce
    (hred : ∀ (p q : ℕ) (Γ : NGraph p (q + 1)) (π : Fin (q + 1) → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → AnpCaseIII Γ π →
      ∃ (p'' : ℕ) (Γ'' : NGraph p'' q) (ea eb : Fin p'' → Option (Fin p ⊕ Fin p)) (own : Fin p'' → Fin p),
        (Γ''.GhostOK ∧ Γ''.IsNested) ∧ Γ''.ordN = Γ.ordN ∧
        (∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none) ∧
        (∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none) ∧
        (∀ j, ∃! r, ea r = some (Sum.inl j)) ∧ (∀ j, ∃! r, eb r = some (Sum.inr j)) ∧
        (∀ r, Γ.noGhostPath (own r) = true → Γ''.noGhostPath r = true) ∧
        (∀ (d L : ℕ) [NeZero L] (ξ : Zd d L → Zd d L → ℝ) (θ : ℝ),
          (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) → (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
          ∀ (a b : Fin p → Zd d L) (x₀ : Zd d L),
            Γ.valOn ξ a b (anpKey2_region a b π) ≤
              θ * Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (ea r)) (fun r => anpKey2_fixLab a b x₀ (eb r)))) :
    ∀ d : ℕ, AnpDetGhCaseIII d := by
  intro d q hq hIH p Γ π hG hN _ hcase
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨p'', Γ'', ea, eb, own, ⟨hG'', hN''⟩, hord, F4a, F4b, F5a, F5b, F6, hval⟩ :=
    hred p q' Γ π hG hN hcase
  obtain ⟨C, c, hC, hc, hc1, H⟩ := hIH p'' q' (Nat.lt_succ_self q') Γ'' hG'' hN''
  refine ⟨C, c / 2, hC, by positivity, by linarith, ?_⟩
  intro L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
  have hψ0 : 0 < ψ 0 := hpos 0 le_rfl
  have hc2 : 0 < c / 2 := by positivity
  have hψle : ∀ y : ℝ, 0 ≤ y → 0 ≤ ψ y ∧ ψ y ≤ ψ 0 := fun y hy =>
    ⟨(hpos y hy).le, hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy⟩
  set x₀ : Zd d L := 0 with hx₀
  set G : ℝ := ∏ i, (if Γ.noGhostPath i = true then
    ψ (c / 2 * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) with hG0
  have hGnn : 0 ≤ G := Finset.prod_nonneg fun i _ => by
    split_ifs
    · exact (hpos _ (mul_nonneg hc2.le (Nat.cast_nonneg _))).le
    · exact zero_le_one
  set K : ℝ := C * θ ^ q' * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) * G with hK0
  -- the far segment of every ghost-free path (subcase (a): the triangle inequality, `x₀` is the fixed label)
  have hfar : ∀ j, ∃ r, Γ.noGhostPath j = true → own r = j ∧ Γ''.noGhostPath r = true ∧
      ψ (c * ((zdistInf d L (anpKey2_fixLab a b x₀ (ea r) - anpKey2_fixLab a b x₀ (eb r)) : ℕ) : ℝ)) ≤
        ψ (c / 2 * ((zdistInf d L (a j - b j) : ℕ) : ℝ)) := by
    intro j
    by_cases hn : Γ.noGhostPath j = true
    · obtain ⟨r, hr0, hd⟩ := anpKey3_far_gen own ea eb F4a F4b F5a F5b a b x₀ j
      refine ⟨r, fun _ => ⟨hr0, F6 r (by rw [hr0]; exact hn), ?_⟩⟩
      refine hanti (Set.mem_Ici.2 (mul_nonneg hc2.le (Nat.cast_nonneg _)))
        (Set.mem_Ici.2 (mul_nonneg hc.le (Nat.cast_nonneg _))) ?_
      have hd' : ((zdistInf d L (a j - b j) : ℕ) : ℝ) ≤
          2 * ((zdistInf d L (anpKey2_fixLab a b x₀ (ea r) - anpKey2_fixLab a b x₀ (eb r)) : ℕ) : ℝ) := by
        exact_mod_cast hd
      have hD0 : (0 : ℝ) ≤ ((zdistInf d L (a j - b j) : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hc]
    · obtain ⟨r, -⟩ := (F5a j).exists
      exact ⟨r, fun h => absurd h hn⟩
  choose ρ hρ using hfar
  have hprod := anpKey3_prod own Γ''.noGhostPath Γ.noGhostPath
    (fun r => ψ (c * ((zdistInf d L (anpKey2_fixLab a b x₀ (ea r) - anpKey2_fixLab a b x₀ (eb r)) : ℕ) : ℝ)))
    (fun j => ψ (c / 2 * ((zdistInf d L (a j - b j) : ℕ) : ℝ))) (ψ 0) hψ0
    (fun r _ => hψle _ (mul_nonneg hc.le (Nat.cast_nonneg _))) ρ hρ
  have hIHx := H L ψ θ hanti hpos hθ ξ hξ hξψ hrow (fun r => anpKey2_fixLab a b x₀ (ea r))
    (fun r => anpKey2_fixLab a b x₀ (eb r))
  have hexp : ψ 0 ^ (Γ''.ordN - (Γ''.nngh : ℤ)) * ψ 0 ^ ((Γ''.nngh : ℤ) - (Γ.nngh : ℤ)) =
      ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) := by
    rw [← zpow_add₀ hψ0.ne', hord]
    congr 1
    ring
  have hΓ'' : Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (ea r)) (fun r => anpKey2_fixLab a b x₀ (eb r)) ≤ K := by
    calc Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (ea r)) (fun r => anpKey2_fixLab a b x₀ (eb r))
        ≤ C * θ ^ q' * ψ 0 ^ (Γ''.ordN - (Γ''.nngh : ℤ)) *
            ∏ r, (if Γ''.noGhostPath r = true then ψ (c * ((zdistInf d L (anpKey2_fixLab a b x₀ (ea r) -
              anpKey2_fixLab a b x₀ (eb r)) : ℕ) : ℝ)) else 1) := hIHx
      _ ≤ C * θ ^ q' * ψ 0 ^ (Γ''.ordN - (Γ''.nngh : ℤ)) *
            (ψ 0 ^ ((Γ''.nngh : ℤ) - (Γ.nngh : ℤ)) * G) :=
          mul_le_mul_of_nonneg_left hprod
            (mul_nonneg (mul_nonneg hC.le (pow_pos hθ q').le) (zpow_pos hψ0 _).le)
      _ = K := by rw [hK0, ← hexp]; ring
  calc Γ.valOn ξ a b (anpKey2_region a b π)
      ≤ θ * Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (ea r)) (fun r => anpKey2_fixLab a b x₀ (eb r)) :=
        hval d L ξ θ hξ hrow a b x₀
    _ ≤ θ * K := mul_le_mul_of_nonneg_left hΓ'' hθ.le
    _ = _ := by rw [hK0, hG0]; ring

/-- **Target** (`AnpKey4CaseIIIHoldsPin`): case (III) of the induction step of `lem:Anp_key_gh` (`7_8:1245-1348`), in
every dimension, for the merged case pin `AnpDetGhCaseIII` (`Graph/AnpKey2.lean:177`) unchanged: an internal vertex
`α_{i₀}` carries two B2 ending edges and `deg_s(α_{i₀}) = 2`; fix it (`anpKey2_fixV`), keep the B2 edges as one-step
ghost paths, make the two solid edges next to them ghost (`anpKey3_gh2`), apply the induction hypothesis to the graph
`Γ''` with `q - 1` internal vertices and `ord Γ'' = ord Γ`, and close with `Σ_x ξ(x, y₁) ξ(x, y₂) ≤ θ`
(`anpKey3_sum_xx`); the constants are `(C, c) ↦ (C'', c''/2)`. -/
theorem anpDetGhCaseIII_holds : ∀ d : ℕ, AnpDetGhCaseIII d :=
  anpKey4_of_reduce anpKey4_reduce

/-! ## 7. Compiled nonempty instances at `d = 3` -/

section Instances

/-- Case (III) only (no case (I)/(II)), with the self-loop configuration of T2242's note (d): `p = 2`, `q = 1`,
`α = inr 0`.  Path 0: `a_0 → α` (ghost, B2 at `α`), `α → a_0` (solid: `β_0 = a_0`, the paper's new ghost edge
`(a_0, β_0)` would be a loop), `a_0 → b_0` (solid).  Path 1: `a_1 → α` (ghost, B2), `α → b_1` (solid, B1).
`deg_s(α) = 2`, `n_S = 3`, `ord = 1`, `n_ngh = 0`. -/
def anpKey4_figLoop : NGraph 2 1 where
  es := [⟨true, .inl (.inl 0), .inr 0⟩, ⟨false, .inr 0, .inl (.inl 0)⟩, ⟨false, .inl (.inl 0), .inl (.inr 0)⟩,
         ⟨true, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (1, .inl (.inl 0)), (2, .inl (.inr 0))]
    else [(3, .inr 0), (4, .inl (.inr 1))]

/-- The region pattern of the `anpKey4_figLoop` instances (any `π` works: B2 ignores `π`, no path is ghost free). -/
def anpKey4_piLoop : Fin 1 → Fin 2 → Bool := fun _ _ => false

/-- The edge `n` of `anpKey4_figLoop` (five edges). -/
def anpKey4_eL (n : ℕ) (h : n < 5 := by decide) : Fin anpKey4_figLoop.es.length := ⟨n, h⟩

/-- Instance (1): the hypotheses at `anpKey4_figLoop`, and that case (I)/(II) does not apply. -/
theorem anpKey4_inst_hyp :
    anpKey4_figLoop.GhostOK ∧ anpKey4_figLoop.IsNested ∧ anpKey4_figLoop.NoA2 anpKey4_piLoop ∧
      ¬ AnpCaseI anpKey4_figLoop anpKey4_piLoop ∧ AnpCaseIII anpKey4_figLoop anpKey4_piLoop ∧
      anpKey4_figLoop.ordN = 1 ∧ anpKey4_figLoop.nngh = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold NGraph.GhostOK
    decide +kernel
  · unfold NGraph.IsNested
    decide +kernel
  all_goals decide +kernel

/-- Instance (2): the target at `anpKey4_figLoop` (case (III) only; the induction hypothesis `AnpIH 3 1`, discharged
by `anpDetGh_of_step` in LW-12f, is the only premise). -/
theorem anpKey4_inst_figLoop :
    AnpIH 3 1 → AnpDetGhRegAt 3 anpKey4_figLoop anpKey4_piLoop := fun hIH =>
  anpDetGhCaseIII_holds 3 1 (by norm_num) hIH 2 _ _ anpKey4_inst_hyp.1 anpKey4_inst_hyp.2.1
    anpKey4_inst_hyp.2.2.1 anpKey4_inst_hyp.2.2.2.2.1

/-- Instance (3): the target at `anpKey2_figAuxGh`, case (III) at `ℳ₂` (two B2 edges `4`, `5`, both `s = true`,
`β_0 = β_1 = ℳ₁`), through `anpDetGhCaseIII_holds` (not through case (I)). -/
theorem anpKey4_inst_figAuxGh :
    AnpCaseIII anpKey2_figAuxGh (fun _ _ => false) ∧
      (AnpIH 3 2 → AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false)) := by
  obtain ⟨hG, hN, hno, -, hIII, -⟩ := anpKey2_inst_figAuxGh
  exact ⟨hIII, fun hIH => anpDetGhCaseIII_holds 3 2 (by norm_num) hIH 2 _ _ hG hN hno hIII⟩

/-- Instance (4): the chain with cases (I) and (III) discharged. -/
theorem anpKey4_inst_chain : AnpDetGhCaseIV 3 → LWAnpKeyGh 3 :=
  anpKey3_inst_chain (anpDetGhCaseIII_holds 3)

/-- Instance (5): the reduction at `anpKey4_figLoop` (the self-loop case `β_0 = a_0`): a reduced graph with no
internal vertex, the ghost condition, the nested properties and the same `ord`. -/
theorem anpKey4_inst_reduce :
    ∃ (p'' : ℕ) (Γ'' : NGraph p'' 0), Γ''.GhostOK ∧ Γ''.IsNested ∧ Γ''.ordN = anpKey4_figLoop.ordN := by
  obtain ⟨p'', Γ'', -, -, -, ⟨hG, hN⟩, hord, -⟩ :=
    anpKey4_reduce 2 0 anpKey4_figLoop anpKey4_piLoop anpKey4_inst_hyp.1 anpKey4_inst_hyp.2.1
      anpKey4_inst_hyp.2.2.2.2.1
  exact ⟨p'', Γ'', hG, hN, hord⟩

/-- Instance (6): `anpKey4_caseIII_ne` and `anpKey4_solid` at `anpKey4_figLoop`: the two B2 edges `0`, `3` lie on the
paths `0 ≠ 1`, and two distinct solid edges at `α` exist. -/
theorem anpKey4_inst_ne_solid :
    (0 : Fin 2) ≠ 1 ∧ ∃ m₁ m₂ : Fin anpKey4_figLoop.es.length, m₁ ≠ m₂ ∧
      (anpKey4_figLoop.es.get m₁).ghost = false ∧ (anpKey4_figLoop.es.get m₂).ghost = false := by
  have b₀ : anpKey4_figLoop.IsB2 anpKey4_piLoop 0 false (anpKey4_eL 0) 0 := by decide +kernel
  have b₁ : anpKey4_figLoop.IsB2 anpKey4_piLoop 1 false (anpKey4_eL 3) 0 := by decide +kernel
  have hd : anpKey4_figLoop.degS 0 = 2 := by decide +kernel
  have hj := anpKey4_caseIII_ne 2 1 anpKey4_figLoop anpKey4_piLoop 0 0 1 false false (anpKey4_eL 0)
    (anpKey4_eL 3) anpKey4_inst_hyp.1 anpKey4_inst_hyp.2.1 (by decide) b₀ b₁
  obtain ⟨m₁, m₂, hm, g₁, g₂, -⟩ := anpKey4_solid 2 1 anpKey4_figLoop anpKey4_piLoop 0 0 1 false false
    (anpKey4_eL 0) (anpKey4_eL 3) anpKey4_inst_hyp.1 anpKey4_inst_hyp.2.1 hj b₀ b₁ hd
  exact ⟨hj, m₁, m₂, hm, g₁, g₂⟩

/-- Instance (7): `anpKey4_gh2_props` at `figAux` (no ghost edge) with the first step of path `0` and the last step of
path `1` (a three-step path, not a one-step path): the double replacement keeps the ghost condition and the nested
properties and loses two solid edges. -/
theorem anpKey4_inst_gh2 :
    (anpKey3_gh2 figAux (anpKey2_eAux 0) (anpKey2_eAux 5)).GhostOK ∧
      (anpKey3_gh2 figAux (anpKey2_eAux 0) (anpKey2_eAux 5)).IsNested ∧
      (anpKey3_gh2 figAux (anpKey2_eAux 0) (anpKey2_eAux 5)).nSolid + 2 = figAux.nSolid := by
  have e₁ : (figAux.path 0).head? = some (anpKey2_eAux 0, (Sum.inr 0 : NV 2 2)) := by decide +kernel
  have e₂ : (figAux.path 1).getLast? = some (anpKey2_eAux 5, (Sum.inl (Sum.inr 1) : NV 2 2)) := by
    decide +kernel
  have h := anpKey4_gh2_props 2 2 figAux anpKey2_figAux_ghostOK figAux_nested.1 0 1 (by decide)
    (anpKey2_eAux 0, .inr 0) (anpKey2_eAux 5, .inl (.inr 1)) (List.mem_of_mem_head? e₁) (Or.inl e₁)
    (List.mem_of_getLast? e₂) (Or.inr e₂) (by decide +kernel) (by decide +kernel)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end Instances

end RBM.Graph
