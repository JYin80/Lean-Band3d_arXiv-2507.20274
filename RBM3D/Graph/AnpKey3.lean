/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey2
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# LW-12c: `lem:Anp_key_gh`, cases (I) and (II) of the induction step (T2252)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): Case (I)
`:1152-1203` (an internal vertex `α_q` with two A1/B1 ending edges `:1154`, `(eq:induc_Ggraph)`
`:1164-1167`, `(eq:change_of_order)` `:1169`, `(eq:change_of_order2)` `:1172`, `(kwuyayw_case1)`
`:1174-1177`, Cauchy-Schwarz `:1178`), Case (II) `:1205-1244` (`(eq:jthpath)` `:1211`,
`(eq:bound_new_graph)` `:1233-1235`, the segment inequality `:1237-1239`).  Part c of the six
tickets of `lem:Anp`.

The proof, for `q = q' + 1`: fix the vertex `α_{i₀}` (`anpKey2_fix`); the two ending edges at
`α_{i₀}` are one-step paths `r₁`, `r₂` of the fixed graph `Γ'`; making both edges ghost
(`NGraph.ghostify` twice, in place of the paper's auxiliary path `(a_1 ⇒ a_2)`, `7_8:1161`,
`:1227`) gives `Γ''` with `q'` internal vertices, `ord Γ'' = ord Γ`; the factors at the fixed
vertex are `ξ(e_t, x)`, `e_t ∈ {a_{j_t}, b_{j_t}}`; the induction hypothesis on `Γ''`, the far
segment of every ghost-free old path, and Cauchy-Schwarz (`2xy ≤ x² + y²`) on the sum over `x`
close the step, with `c ↦ c/2`.

* Section 1: helpers (ending edges are solid).
* Section 2: the double A2 replacement `anpKey3_gh2`.
* Section 3: the factor at the fixed vertex.
* Section 4: the far segment of a ghost-free path.
* Section 5: the product bound.
* Section 6: `Σ_x ξ(e₁, x) ξ(e₂, x) ≤ θ`.
* Section 7: the target `anpDetGhCaseI_holds`.
* Section 8: compiled nonempty instances at `d = 3`.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Helpers -/

section Helpers

variable {p q : ℕ}

/-- An ending edge is a step of the path, and the first or the last one. -/
theorem anpKey3_endAt_mem {Γ : NGraph p q} {j : Fin p} {s : Bool} {k : Fin Γ.es.length} {i : Fin q}
    (h : Γ.EndAt j s k i) :
    ∃ v : NV p q, (k, v) ∈ Γ.path j ∧
      ((Γ.path j).head? = some (k, v) ∨ (Γ.path j).getLast? = some (k, v)) := by
  obtain ⟨⟨v, hv⟩, -⟩ := h
  refine ⟨v, ?_⟩
  cases s
  · simp only [Bool.false_eq_true, ite_false] at hv
    exact ⟨List.mem_of_mem_head? hv, Or.inl hv⟩
  · simp only [ite_true] at hv
    exact ⟨List.mem_of_getLast? hv, Or.inr hv⟩

/-- An A1 or B1 ending edge is solid (A1: the path has no ghost edge; B1: by definition). -/
theorem anpKey3_end_solid (Γ : NGraph p q) (π : Fin q → Fin p → Bool) {j : Fin p} {s : Bool}
    {k : Fin Γ.es.length} {i : Fin q} (h : Γ.IsA1 π j s k i ∨ Γ.IsB1 π j s k i) :
    (Γ.es.get k).ghost = false := by
  rcases h with ⟨he, hn, -⟩ | ⟨-, -, hg⟩
  · obtain ⟨v, hmem, -⟩ := anpKey3_endAt_mem he
    exact (anpKey2_noGhost_iff Γ j).1 hn _ hmem
  · exact hg

/-- The ending edge of an A1 or B1 type. -/
theorem anpKey3_endAt_of {Γ : NGraph p q} {π : Fin q → Fin p → Bool} {j : Fin p} {s : Bool}
    {k : Fin Γ.es.length} {i : Fin q} (h : Γ.IsA1 π j s k i ∨ Γ.IsB1 π j s k i) :
    Γ.EndAt j s k i := h.elim (fun h => h.1) (fun h => h.1)

/-- A one-step path with a solid edge has no ghost edge. -/
theorem anpKey3_noGhost_single {Γ : NGraph p q} {r : Fin p} {e : Fin Γ.es.length} {v : NV p q}
    (h : Γ.path r = [(e, v)]) (g : (Γ.es.get e).ghost = false) : Γ.noGhostPath r = true := by
  rw [anpKey2_noGhost_iff, h]
  intro st hst
  rw [List.mem_singleton] at hst
  subst hst
  exact g

end Helpers

/-! ## 2. The double A2 replacement (`7_8:1161`, `:1227`, replaced) -/

section Gh2

variable {p q : ℕ}

/-- Both ending edges `e₁`, `e₂` made ghost: `(Γ.ghostify e₁).ghostify e₂`. -/
@[reducible] def anpKey3_gh2 (Γ : NGraph p q) (e₁ e₂ : Fin Γ.es.length) : NGraph p q :=
  (Γ.ghostify e₁).ghostify (Γ.ghostifyIdx e₁ e₂)

/-- The two split-off one-step paths `r₁ ≠ r₂` of `Γ` with solid edges `e₁`, `e₂`: the double replacement keeps the
ghost condition and the nested properties, has two solid edges less, loses exactly the paths `r₁`, `r₂`, and
splits off the two factors. -/
theorem anpKey3_gh2_props (Γ : NGraph p q) (hG : Γ.GhostOK) (hN : Γ.IsNested) {r₁ r₂ : Fin p}
    (hr : r₁ ≠ r₂) {e₁ e₂ : Fin Γ.es.length} {v₁ v₂ : NV p q} (h₁ : Γ.path r₁ = [(e₁, v₁)])
    (h₂ : Γ.path r₂ = [(e₂, v₂)]) (g₁ : (Γ.es.get e₁).ghost = false) (g₂ : (Γ.es.get e₂).ghost = false) :
    (anpKey3_gh2 Γ e₁ e₂).GhostOK ∧ (anpKey3_gh2 Γ e₁ e₂).IsNested ∧
      (anpKey3_gh2 Γ e₁ e₂).nSolid + 2 = Γ.nSolid ∧
      (∀ r, (anpKey3_gh2 Γ e₁ e₂).noGhostPath r = true ↔ Γ.noGhostPath r = true ∧ r ≠ r₁ ∧ r ≠ r₂) ∧
      (∀ {ι : Type} (ξ : ι → ι → ℝ) (lab : NV p q → ι),
        anpKey2_ep Γ ξ lab = ξ (lab (Γ.es.get e₁).u) (lab (Γ.es.get e₁).v) *
          ξ (lab (Γ.es.get e₂).u) (lab (Γ.es.get e₂).v) * anpKey2_ep (anpKey3_gh2 Γ e₁ e₂) ξ lab) := by
  have hm₁ : (e₁, v₁) ∈ Γ.path r₁ := by rw [h₁]; simp
  have hm₂ : (e₂, v₂) ∈ Γ.path r₂ := by rw [h₂]; simp
  have hn₁ : Γ.noGhostPath r₁ = true := anpKey3_noGhost_single h₁ g₁
  have hn₂ : Γ.noGhostPath r₂ = true := anpKey3_noGhost_single h₂ g₂
  have hne : e₁ ≠ e₂ := fun h => hN.2.2.2.1 r₁ r₂ hr _ hm₁ _ hm₂ h
  have hG₁ : (Γ.ghostify e₁).GhostOK :=
    anpKey_ghostify_ghostOK Γ hG hN (st₀ := (e₁, v₁)) hn₁ hm₁ (Or.inl (by rw [h₁]; rfl))
  have hN₁ : (Γ.ghostify e₁).IsNested := anpKey_ghostify_nested Γ e₁ hN
  have hm₂' : (Γ.ghostifyIdx e₁ e₂, v₂) ∈ (Γ.ghostify e₁).path r₂ := by
    rw [anpKey_gf_path, h₂]; simp
  have hn₂' : (Γ.ghostify e₁).noGhostPath r₂ = true :=
    (anpKey_gf_noGhostPath_iff Γ hN (st₀ := (e₁, v₁)) hm₁ r₂).2 ⟨hn₂, hr.symm⟩
  have hG₂ : ((Γ.ghostify e₁).ghostify (Γ.ghostifyIdx e₁ e₂)).GhostOK :=
    anpKey_ghostify_ghostOK (Γ.ghostify e₁) hG₁ hN₁ (st₀ := (Γ.ghostifyIdx e₁ e₂, v₂)) hn₂' hm₂'
      (Or.inl (by rw [anpKey_gf_path, h₂]; rfl))
  have hN₂ : ((Γ.ghostify e₁).ghostify (Γ.ghostifyIdx e₁ e₂)).IsNested :=
    anpKey_ghostify_nested (Γ.ghostify e₁) (Γ.ghostifyIdx e₁ e₂) hN₁
  have hs₁ : (Γ.ghostify e₁).nSolid + 1 = Γ.nSolid :=
    anpKey_ghostify_nSolid Γ (st₀ := (e₁, v₁)) hn₁ hm₁
  have hs₂ : (anpKey3_gh2 Γ e₁ e₂).nSolid + 1 = (Γ.ghostify e₁).nSolid :=
    anpKey_ghostify_nSolid (Γ.ghostify e₁) (st₀ := (Γ.ghostifyIdx e₁ e₂, v₂)) hn₂' hm₂'
  refine ⟨hG₂, hN₂, by omega, ?_, ?_⟩
  · intro r
    have h1 := anpKey_gf_noGhostPath_iff Γ hN (st₀ := (e₁, v₁)) hm₁ r
    have h2 := anpKey_gf_noGhostPath_iff (Γ.ghostify e₁) hN₁ (st₀ := (Γ.ghostifyIdx e₁ e₂, v₂)) hm₂' r
    show ((Γ.ghostify e₁).ghostify (Γ.ghostifyIdx e₁ e₂)).noGhostPath r = true ↔ _
    rw [h2, h1]
    tauto
  · intro ι ξ lab
    have e1 := anpKey2_ep_ghostify Γ ξ lab e₁ g₁
    have g₂' : ((Γ.ghostify e₁).es.get (Γ.ghostifyIdx e₁ e₂)).ghost = false := by
      rw [anpKey_gf_ghost']
      have h0 : decide (e₂ = e₁) = false := by simp [hne.symm]
      rw [h0, g₂]
      rfl
    have e2 := anpKey2_ep_ghostify (Γ.ghostify e₁) ξ lab (Γ.ghostifyIdx e₁ e₂) g₂'
    have hu := anpKey_gf_u Γ e₁ e₂
    have hv := anpKey_gf_v Γ e₁ e₂
    have hu' : ((Γ.ghostify e₁).es.get (Γ.ghostifyIdx e₁ e₂)).u = (Γ.es.get e₂).u := hu
    have hv' : ((Γ.ghostify e₁).es.get (Γ.ghostifyIdx e₁ e₂)).v = (Γ.es.get e₂).v := hv
    rw [hu', hv'] at e2
    rw [e1, e2]
    ring

end Gh2

/-! ## 3. The factor at the fixed vertex (`(eq:induc_Ggraph)`, `7_8:1164-1167`) -/

section Factor

/-- An ending edge `k` at the fixed vertex `α_{i₀}` contributes `ξ(e, x)`, `e = a_j` (`s = false`) or `e = b_j`
(`s = true`), for every labelling of the fixed graph that agrees with `Γ` (the label equations of (F2)). -/
theorem anpKey3_endFactor {ι : Type} {p q p' : ℕ} (Γ : NGraph p (q + 1)) (Γ' : NGraph p' q)
    (hN : Γ.IsNested) (ξ : ι → ι → ℝ) (hsym : ∀ α β, ξ α β = ξ β α) (a b : Fin p → ι) (x : ι)
    (ℓ : Fin q → ι) (i₀ : Fin (q + 1)) (lab : NV p' q → ι)
    (em : Fin Γ.es.length → Fin Γ'.es.length)
    (hu : ∀ k, lab (Γ'.es.get (em k)).u =
      Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).u)
    (hv : ∀ k, lab (Γ'.es.get (em k)).v =
      Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).v)
    {j : Fin p} {s : Bool} {k : Fin Γ.es.length} (h : Γ.EndAt j s k i₀) :
    ξ (lab (Γ'.es.get (em k)).u) (lab (Γ'.es.get (em k)).v) = ξ (if s = true then b j else a j) x := by
  rw [hu, hv]
  have hx : (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) i₀ = x := Fin.insertNth_apply_same _ _ _
  rcases anpKey2_endAt_ends (hN.2.1 j) h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    cases s <;> simp
  · rw [h1, h2]
    cases s <;> simp [hsym x]

end Factor

/-! ## 4. The far segment of a ghost-free path (`(eq:change_of_order2)`, `7_8:1172`; `:1237-1239`) -/

section Far

variable {d L p p' : ℕ} [NeZero L]

/-- Subcase (b): the one-step path `r_t` of an A1 ending edge of `j = own r_t` is the first (`s = false`) or the last
(`s = true`) segment of the path `j`; the other end segment `r ≠ r_t` has its other end at the fixed vertex `x`, and
`x ∈ 𝐃_π` gives `|a_j - b_j| ≤ 2 |x - b_j|` (resp. `2 |x - a_j|`). -/
theorem anpKey3_far_end (own : Fin p' → Fin p) (ea eb : Fin p' → Option (Fin p ⊕ Fin p))
    (h4a : ∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none)
    (h4b : ∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none)
    (h5a : ∀ j, ∃! r, ea r = some (Sum.inl j)) (h5b : ∀ j, ∃! r, eb r = some (Sum.inr j))
    (a b : Fin p → Zd d L) (x : Zd d L) (π' : Fin p → Bool) (hx : x ∈ anpKey2_regionOne a b π')
    {rt : Fin p'} {s : Bool}
    (h7 : if s = true then ea rt = none ∧ eb rt = some (Sum.inr (own rt))
      else ea rt = some (Sum.inl (own rt)) ∧ eb rt = none)
    (hπ : π' (own rt) = s) :
    ∃ r, own r = own rt ∧ r ≠ rt ∧
      zdistInf d L (a (own rt) - b (own rt)) ≤
        2 * zdistInf d L (anpKey2_fixLab a b x (ea r) - anpKey2_fixLab a b x (eb r)) := by
  have hreg := (Finset.mem_filter.1 hx).2 (own rt)
  cases s
  · simp only [Bool.false_eq_true, ite_false] at h7
    obtain ⟨hea, heb⟩ := h7
    obtain ⟨rb, hrb, -⟩ := h5b (own rt)
    have hown : own rb = own rt := by
      rcases h4b rb with h | h
      · rw [hrb] at h; exact (Sum.inr_injective (Option.some_injective _ h)).symm
      · rw [hrb] at h; exact absurd h (by simp)
    have hne : rb ≠ rt := fun h => by rw [h, heb] at hrb; exact absurd hrb (by simp)
    have hearb : ea rb = none := by
      rcases h4a rb with h | h
      · exfalso
        obtain ⟨r0, -, hu⟩ := h5a (own rt)
        have h1 : rb = r0 := hu rb (by show ea rb = _; rw [h, hown])
        have h2 : rt = r0 := hu rt hea
        exact hne (h1.trans h2.symm)
      · exact h
    refine ⟨rb, hown, hne, ?_⟩
    have hle : zdistInf d L (x - a (own rt)) ≤ zdistInf d L (x - b (own rt)) := by
      have : ¬ (zdistInf d L (x - b (own rt)) < zdistInf d L (x - a (own rt))) := fun h' => by
        have := hreg.2 h'
        rw [hπ] at this
        exact Bool.false_ne_true this
      exact not_lt.1 this
    have := anpKey2_half d L (a (own rt)) (b (own rt)) x hle
    rw [hearb, hrb]
    exact this
  · simp only [ite_true] at h7
    obtain ⟨hea, heb⟩ := h7
    obtain ⟨ra, hra, -⟩ := h5a (own rt)
    have hown : own ra = own rt := by
      rcases h4a ra with h | h
      · rw [hra] at h; exact (Sum.inl_injective (Option.some_injective _ h)).symm
      · rw [hra] at h; exact absurd h (by simp)
    have hne : ra ≠ rt := fun h => by rw [h, hea] at hra; exact absurd hra (by simp)
    have hebra : eb ra = none := by
      rcases h4b ra with h | h
      · exfalso
        obtain ⟨r0, -, hu⟩ := h5b (own rt)
        have h1 : ra = r0 := hu ra (by show eb ra = _; rw [h, hown])
        have h2 : rt = r0 := hu rt heb
        exact hne (h1.trans h2.symm)
      · exact h
    refine ⟨ra, hown, hne, ?_⟩
    have hlt := hreg.1 hπ
    have := anpKey2_half d L (b (own rt)) (a (own rt)) x hlt.le
    rw [hebra, hra]
    simp only [anpKey2_fixLab, Option.elim, Sum.elim_inl]
    rw [anpKey_zdistInf_sub_comm (a (own rt)) x, anpKey_zdistInf_sub_comm (a (own rt)) (b (own rt))]
    exact this

/-- Subcase (a): any path `j`: either one segment is the whole path, or the two end segments are `a_j → x` and
`x → b_j` and the triangle inequality puts one of them at `≥ |a_j - b_j|/2`. -/
theorem anpKey3_far_gen (own : Fin p' → Fin p) (ea eb : Fin p' → Option (Fin p ⊕ Fin p))
    (h4a : ∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none)
    (h4b : ∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none)
    (h5a : ∀ j, ∃! r, ea r = some (Sum.inl j)) (h5b : ∀ j, ∃! r, eb r = some (Sum.inr j))
    (a b : Fin p → Zd d L) (x : Zd d L) (j : Fin p) :
    ∃ r, own r = j ∧
      zdistInf d L (a j - b j) ≤
        2 * zdistInf d L (anpKey2_fixLab a b x (ea r) - anpKey2_fixLab a b x (eb r)) := by
  obtain ⟨ra, hra, hua⟩ := h5a j
  obtain ⟨rb, hrb, hub⟩ := h5b j
  have howna : own ra = j := by
    rcases h4a ra with h | h
    · rw [hra] at h; exact (Sum.inl_injective (Option.some_injective _ h)).symm
    · rw [hra] at h; exact absurd h (by simp)
  have hownb : own rb = j := by
    rcases h4b rb with h | h
    · rw [hrb] at h; exact (Sum.inr_injective (Option.some_injective _ h)).symm
    · rw [hrb] at h; exact absurd h (by simp)
  by_cases hr : ra = rb
  · subst hr
    refine ⟨ra, howna, ?_⟩
    rw [hra, hrb]
    simp only [anpKey2_fixLab, Option.elim, Sum.elim_inl, Sum.elim_inr]
    omega
  · have hebra : eb ra = none := by
      rcases h4b ra with h | h
      · exfalso
        rw [howna] at h
        exact hr (hub ra h)
      · exact h
    have hearb : ea rb = none := by
      rcases h4a rb with h | h
      · exfalso
        rw [hownb] at h
        exact hr (hua rb h).symm
      · exact h
    have htri := anpKey_zdistInf_tri (a j) x (b j)
    by_cases hle : zdistInf d L (x - b j) ≤ zdistInf d L (a j - x)
    · refine ⟨ra, howna, ?_⟩
      rw [hra, hebra]
      simp only [anpKey2_fixLab, Option.elim, Sum.elim_inl]
      omega
    · refine ⟨rb, hownb, ?_⟩
      rw [hearb, hrb]
      simp only [anpKey2_fixLab, Option.elim, Sum.elim_inr]
      omega

/-- The far segment (`(eq:change_of_order2)`, `7_8:1172`; the display `7_8:1237-1239`): for every old path `j`
(with `π i₀ j = s_t` if `j = j_t`) there is a segment `r*` of `j` other than `r₁`, `r₂` with
`|a_j - b_j| ≤ 2 |a''_{r*} - b''_{r*}|`. -/
theorem anpKey3_far (own : Fin p' → Fin p) (ea eb : Fin p' → Option (Fin p ⊕ Fin p))
    (h4a : ∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none)
    (h4b : ∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none)
    (h5a : ∀ j, ∃! r, ea r = some (Sum.inl j)) (h5b : ∀ j, ∃! r, eb r = some (Sum.inr j))
    (a b : Fin p → Zd d L) (x : Zd d L) (π' : Fin p → Bool) (hx : x ∈ anpKey2_regionOne a b π')
    {r₁ r₂ : Fin p'} {s₁ s₂ : Bool} (hj : own r₁ ≠ own r₂)
    (h7₁ : if s₁ = true then ea r₁ = none ∧ eb r₁ = some (Sum.inr (own r₁))
      else ea r₁ = some (Sum.inl (own r₁)) ∧ eb r₁ = none)
    (h7₂ : if s₂ = true then ea r₂ = none ∧ eb r₂ = some (Sum.inr (own r₂))
      else ea r₂ = some (Sum.inl (own r₂)) ∧ eb r₂ = none)
    (j : Fin p) (hπ₁ : j = own r₁ → π' j = s₁) (hπ₂ : j = own r₂ → π' j = s₂) :
    ∃ r, own r = j ∧ r ≠ r₁ ∧ r ≠ r₂ ∧
      zdistInf d L (a j - b j) ≤
        2 * zdistInf d L (anpKey2_fixLab a b x (ea r) - anpKey2_fixLab a b x (eb r)) := by
  by_cases h1 : j = own r₁
  · subst h1
    obtain ⟨r, hr, hne, hd⟩ := anpKey3_far_end own ea eb h4a h4b h5a h5b a b x π' hx h7₁ (hπ₁ rfl)
    exact ⟨r, hr, hne, fun h => hj (by rw [← hr, h]), hd⟩
  · by_cases h2 : j = own r₂
    · subst h2
      obtain ⟨r, hr, hne, hd⟩ := anpKey3_far_end own ea eb h4a h4b h5a h5b a b x π' hx h7₂ (hπ₂ rfl)
      exact ⟨r, hr, fun h => hj (by rw [← hr, h]), hne, hd⟩
    · obtain ⟨r, hr, hd⟩ := anpKey3_far_gen own ea eb h4a h4b h5a h5b a b x j
      exact ⟨r, hr, fun h => h1 (by rw [← hr, h]), fun h => h2 (by rw [← hr, h]), hd⟩

end Far

/-! ## 5. The product bound (`7_8:1237-1239`) -/

section Prod

/-- Every ghost-free path `j` of the old graph has a ghost-free segment `ρ j` of the new graph with the better factor
`h'' (ρ j) ≤ h j`; all other factors are `≤ ψ(0)`.  The exponent of `ψ(0)` is the number of ghost-free paths of the
new graph minus the old one (`n_ngh(𝒢'') - n_ngh(𝒢)`, an integer `≥ 0` because `ρ` is injective). -/
theorem anpKey3_prod {p p' : ℕ} (own : Fin p' → Fin p) (g'' : Fin p' → Bool) (g : Fin p → Bool)
    (h'' : Fin p' → ℝ) (h : Fin p → ℝ) (ψ0 : ℝ) (hψ0 : 0 < ψ0)
    (hbd : ∀ r, g'' r = true → 0 ≤ h'' r ∧ h'' r ≤ ψ0) (ρ : Fin p → Fin p')
    (hρ : ∀ j, g j = true → own (ρ j) = j ∧ g'' (ρ j) = true ∧ h'' (ρ j) ≤ h j) :
    (∏ r, if g'' r = true then h'' r else 1) ≤
      ψ0 ^ (((Finset.univ.filter fun r => g'' r = true).card : ℤ) -
          ((Finset.univ.filter fun j => g j = true).card : ℕ)) *
        ∏ j, if g j = true then h j else 1 := by
  classical
  set T := Finset.univ.filter fun r : Fin p' => g'' r = true with hT
  set J := Finset.univ.filter fun j : Fin p => g j = true with hJ
  have hJmem : ∀ j, j ∈ J ↔ g j = true := fun j => by simp [hJ]
  have hTmem : ∀ r, r ∈ T ↔ g'' r = true := fun r => by simp [hT]
  have hinj : Set.InjOn ρ J := by
    intro j₁ h₁ j₂ h₂ h
    have a1 := (hρ j₁ ((hJmem _).1 h₁)).1
    have a2 := (hρ j₂ ((hJmem _).1 h₂)).1
    rw [← a1, ← a2]
    exact congrArg own h
  have hsub : J.image ρ ⊆ T := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hr
    exact (hTmem _).2 (hρ j ((hJmem _).1 hj)).2.1
  have hcard : (J.image ρ).card = J.card := Finset.card_image_of_injOn hinj
  have hL : (∏ r, if g'' r = true then h'' r else 1) = ∏ r ∈ T, h'' r :=
    (Finset.prod_filter _ _).symm
  have hR : (∏ j, if g j = true then h j else 1) = ∏ j ∈ J, h j := (Finset.prod_filter _ _).symm
  have hexp : (T.card : ℤ) - (J.card : ℕ) = (((T \ J.image ρ).card : ℕ) : ℤ) := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), hcard]
  rw [hL, hR, hexp, zpow_natCast, ← Finset.prod_sdiff hsub, Finset.prod_image hinj]
  have h1 : ∏ r ∈ T \ J.image ρ, h'' r ≤ ψ0 ^ (T \ J.image ρ).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun r hr => (hbd r ((hTmem _).1 (Finset.mem_sdiff.1 hr).1)).1)
      (fun r hr => (hbd r ((hTmem _).1 (Finset.mem_sdiff.1 hr).1)).2)
  have h2 : ∏ j ∈ J, h'' (ρ j) ≤ ∏ j ∈ J, h j :=
    Finset.prod_le_prod₀ (fun j hj => (hbd _ (hρ j ((hJmem _).1 hj)).2.1).1)
      (fun j hj => (hρ j ((hJmem _).1 hj)).2.2)
  have h3 : 0 ≤ ∏ j ∈ J, h'' (ρ j) :=
    Finset.prod_nonneg fun j hj => (hbd _ (hρ j ((hJmem _).1 hj)).2.1).1
  have h4 : 0 ≤ ∏ r ∈ T \ J.image ρ, h'' r :=
    Finset.prod_nonneg fun r hr => (hbd r ((hTmem _).1 (Finset.mem_sdiff.1 hr).1)).1
  calc (∏ r ∈ T \ J.image ρ, h'' r) * ∏ j ∈ J, h'' (ρ j)
      ≤ ψ0 ^ (T \ J.image ρ).card * ∏ j ∈ J, h j :=
        mul_le_mul h1 h2 h3 (pow_nonneg hψ0.le _)
    _ = _ := rfl

end Prod

/-! ## 6. Cauchy-Schwarz on the fixed vertex (`7_8:1178`) -/

section CS

/-- `Σ_x ξ(e₁, x) ξ(e₂, x) ≤ θ` from `2xy ≤ x² + y²` and `Σ_β ξ_{αβ}² ≤ θ` for the rows `e₁` and `e₂`. -/
theorem anpKey3_sum_xx {ι : Type*} [Fintype ι] (ξ : ι → ι → ℝ) (θ : ℝ)
    (hξ : ∀ α β, 0 ≤ ξ α β) (hrow : ∀ α, ∑ β, ξ α β ^ 2 ≤ θ) (R : Finset ι) (e₁ e₂ : ι) :
    ∑ x ∈ R, ξ e₁ x * ξ e₂ x ≤ θ := by
  have h1 : ∑ x ∈ R, ξ e₁ x * ξ e₂ x ≤ ∑ x, ξ e₁ x * ξ e₂ x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      (fun x _ _ => mul_nonneg (hξ _ _) (hξ _ _))
  have h2 : ∑ x, ξ e₁ x * ξ e₂ x ≤ ∑ x, (ξ e₁ x ^ 2 + ξ e₂ x ^ 2) / 2 :=
    Finset.sum_le_sum fun x _ => by
      have := two_mul_le_add_sq (ξ e₁ x) (ξ e₂ x)
      linarith
  have h3 : ∑ x, (ξ e₁ x ^ 2 + ξ e₂ x ^ 2) / 2 = (∑ x, ξ e₁ x ^ 2 + ∑ x, ξ e₂ x ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h4 := hrow e₁
  have h5 := hrow e₂
  linarith

end CS

/-! ## 7. The target (`7_8:1152-1244`) -/

/-- **Target** (`AnpKey3CaseIHoldsPin`): cases (I) and (II) of the induction step of `lem:Anp_key_gh`
(`7_8:1152-1244`), in every dimension, for the merged case pin `AnpDetGhCaseI` (`Graph/AnpKey2.lean:171`).
An internal vertex `α_{i₀}` carries two ending edges of type A1 or B1 (on two distinct paths); fix it
(`anpKey2_fix`), make the two one-step paths ghost, apply the induction hypothesis to the graph `Γ''` with
`q - 1` internal vertices and `ord Γ'' = ord Γ`, bound the far segment of every ghost-free path, and close with
`Σ_x ξ(e₁, x) ξ(e₂, x) ≤ θ`; the constants are `(C, c) ↦ (C'', c''/2)`. -/
theorem anpDetGhCaseI_holds : ∀ d : ℕ, AnpDetGhCaseI d := by
  intro d q hq hIH p Γ π hG hN _ hcase
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨i₀, j₁, j₂, s₁, s₂, k₁, k₂, hne, h₁, h₂⟩ := hcase
  have hj : j₁ ≠ j₂ := anpKey2_caseI_ne Γ π hG hne h₁ h₂
  have hsol₁ := anpKey3_end_solid Γ π h₁
  have hsol₂ := anpKey3_end_solid Γ π h₂
  obtain ⟨p', Γ', ea, eb, own, em, ⟨hG', hN'⟩, F2, F2', F3, F4a, F4b, F5a, F5b, -, F6a, -, F7, F8⟩ :=
    anpKey2_fix p q' Γ i₀ hG hN
  obtain ⟨r₁, hown₁, hpath₁, hf₁⟩ := F7 j₁ s₁ k₁ (anpKey3_endAt_of h₁)
  obtain ⟨r₂, hown₂, hpath₂, hf₂⟩ := F7 j₂ s₂ k₂ (anpKey3_endAt_of h₂)
  have hr : r₁ ≠ r₂ := fun h => hj (by rw [← hown₁, ← hown₂, h])
  have g₁ : (Γ'.es.get (em k₁)).ghost = false := by rw [F2]; exact hsol₁
  have g₂ : (Γ'.es.get (em k₂)).ghost = false := by rw [F2]; exact hsol₂
  obtain ⟨hG'', hN'', hS'', hng'', hep⟩ := anpKey3_gh2_props Γ' hG' hN' hr hpath₁ hpath₂ g₁ g₂
  generalize anpKey3_gh2 Γ' (em k₁) (em k₂) = Γ'' at hG'' hN'' hS'' hng'' hep
  have h7₁ : (if s₁ = true then ea r₁ = none ∧ eb r₁ = some (Sum.inr (own r₁))
      else ea r₁ = some (Sum.inl (own r₁)) ∧ eb r₁ = none) := by rw [hown₁]; exact hf₁
  have h7₂ : (if s₂ = true then ea r₂ = none ∧ eb r₂ = some (Sum.inr (own r₂))
      else ea r₂ = some (Sum.inl (own r₂)) ∧ eb r₂ = none) := by rw [hown₂]; exact hf₂
  have hj' : own r₁ ≠ own r₂ := by rw [hown₁, hown₂]; exact hj
  -- `ord Γ'' = ord Γ`
  have hordeq : Γ''.ordN = Γ.ordN := by
    have h : Γ''.nSolid + 2 = Γ.nSolid := by rw [← F8]; exact hS''
    unfold NGraph.ordN
    simp only [ord]
    omega
  obtain ⟨C, c, hC, hc, hc1, H⟩ := hIH p' q' (Nat.lt_succ_self q') Γ'' hG'' hN''
  refine ⟨C, c / 2, hC, by positivity, by linarith, ?_⟩
  intro L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
  have hnn : ∀ α β, 0 ≤ ξ α β := fun α β => (hξ α β).1
  have hsym : ∀ α β, ξ α β = ξ β α := fun α β => (hξ α β).2
  have hψ0 : 0 < ψ 0 := hpos 0 le_rfl
  have hc2 : 0 < c / 2 := by positivity
  have hψle : ∀ y : ℝ, 0 ≤ y → 0 ≤ ψ y ∧ ψ y ≤ ψ 0 := fun y hy =>
    ⟨(hpos y hy).le, hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy⟩
  -- the two factors at the fixed vertex
  set E₁ : Zd d L := if s₁ = true then b j₁ else a j₁ with hE₁
  set E₂ : Zd d L := if s₂ = true then b j₂ else a j₂ with hE₂
  set G : ℝ := ∏ i, (if Γ.noGhostPath i = true then
    ψ (c / 2 * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) with hG0
  have hGnn : 0 ≤ G := Finset.prod_nonneg fun i _ => by
    split_ifs
    · exact (hpos _ (mul_nonneg hc2.le (Nat.cast_nonneg _))).le
    · exact zero_le_one
  set K : ℝ := C * θ ^ q' * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) * G with hK0
  have hKnn : 0 ≤ K :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le (pow_pos hθ q').le) (zpow_pos hψ0 _).le) hGnn
  have hpt : ∀ x ∈ anpKey2_regionOne a b (π i₀),
      Γ'.val ξ (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r)) ≤
        ξ E₁ x * ξ E₂ x * K := by
    intro x hx
    -- step 3: the factors `ξ(e_t, x)`
    have hfac : Γ'.val ξ (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r)) =
        ξ E₁ x * ξ E₂ x * Γ''.val ξ (fun r => anpKey2_fixLab a b x (ea r))
          (fun r => anpKey2_fixLab a b x (eb r)) := by
      unfold NGraph.val
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      have h0 := hep ξ (Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (ea r))
        (fun r => anpKey2_fixLab a b x (eb r))) ℓ)
      have f₁ := anpKey3_endFactor Γ Γ' hN ξ hsym a b x ℓ i₀
        (Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (ea r))
          (fun r => anpKey2_fixLab a b x (eb r))) ℓ) em (fun k => (F2' _ a b x ℓ k).1)
        (fun k => (F2' _ a b x ℓ k).2) (anpKey3_endAt_of h₁)
      have f₂ := anpKey3_endFactor Γ Γ' hN ξ hsym a b x ℓ i₀
        (Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (ea r))
          (fun r => anpKey2_fixLab a b x (eb r))) ℓ) em (fun k => (F2' _ a b x ℓ k).1)
        (fun k => (F2' _ a b x ℓ k).2) (anpKey3_endAt_of h₂)
      show anpKey2_ep Γ' ξ _ = _ * anpKey2_ep Γ'' ξ _
      rw [h0, f₁, f₂]
    -- step 4: the far segment of every ghost-free path
    have hfar : ∀ j, ∃ r, Γ.noGhostPath j = true → own r = j ∧ Γ''.noGhostPath r = true ∧
        ψ (c * ((zdistInf d L (anpKey2_fixLab a b x (ea r) - anpKey2_fixLab a b x (eb r)) : ℕ) : ℝ)) ≤
          ψ (c / 2 * ((zdistInf d L (a j - b j) : ℕ) : ℝ)) := by
      intro j
      by_cases hn : Γ.noGhostPath j = true
      · have hπ₁ : j = own r₁ → π i₀ j = s₁ := by
          intro hjj
          rcases h₁ with ⟨-, -, hπ⟩ | ⟨-, hnb, -⟩
          · rw [hjj, hown₁]; exact hπ
          · rw [hjj, hown₁] at hn; rw [hnb] at hn; exact absurd hn (by simp)
        have hπ₂ : j = own r₂ → π i₀ j = s₂ := by
          intro hjj
          rcases h₂ with ⟨-, -, hπ⟩ | ⟨-, hnb, -⟩
          · rw [hjj, hown₂]; exact hπ
          · rw [hjj, hown₂] at hn; rw [hnb] at hn; exact absurd hn (by simp)
        obtain ⟨r, hr0, hr1, hr2, hd⟩ := anpKey3_far own ea eb F4a F4b F5a F5b a b x (π i₀) hx hj'
          h7₁ h7₂ j hπ₁ hπ₂
        refine ⟨r, fun _ => ⟨hr0, (hng'' r).2 ⟨F6a r (by rw [hr0]; exact hn), hr1, hr2⟩, ?_⟩⟩
        refine hanti (Set.mem_Ici.2 (mul_nonneg hc2.le (Nat.cast_nonneg _)))
          (Set.mem_Ici.2 (mul_nonneg hc.le (Nat.cast_nonneg _))) ?_
        have hd' : ((zdistInf d L (a j - b j) : ℕ) : ℝ) ≤
            2 * ((zdistInf d L (anpKey2_fixLab a b x (ea r) - anpKey2_fixLab a b x (eb r)) : ℕ) : ℝ) := by
          exact_mod_cast hd
        have hD0 : (0 : ℝ) ≤ ((zdistInf d L (a j - b j) : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [hc]
      · obtain ⟨r, -⟩ := (F5a j).exists
        exact ⟨r, fun h => absurd h hn⟩
    choose ρ hρ using hfar
    -- step 5: the product bound
    have hprod := anpKey3_prod own Γ''.noGhostPath Γ.noGhostPath
      (fun r => ψ (c * ((zdistInf d L (anpKey2_fixLab a b x (ea r) - anpKey2_fixLab a b x (eb r)) : ℕ) : ℝ)))
      (fun j => ψ (c / 2 * ((zdistInf d L (a j - b j) : ℕ) : ℝ))) (ψ 0) hψ0
      (fun r _ => hψle _ (mul_nonneg hc.le (Nat.cast_nonneg _))) ρ hρ
    -- step 6: the induction hypothesis
    have hIHx := H L ψ θ hanti hpos hθ ξ hξ hξψ hrow (fun r => anpKey2_fixLab a b x (ea r))
      (fun r => anpKey2_fixLab a b x (eb r))
    have hexp : ψ 0 ^ (Γ''.ordN - (Γ''.nngh : ℤ)) * ψ 0 ^ ((Γ''.nngh : ℤ) - (Γ.nngh : ℤ)) =
        ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) := by
      rw [← zpow_add₀ hψ0.ne', hordeq]
      congr 1
      ring
    have hΓ'' : Γ''.val ξ (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r)) ≤ K := by
      calc Γ''.val ξ (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r))
          ≤ C * θ ^ q' * ψ 0 ^ (Γ''.ordN - (Γ''.nngh : ℤ)) *
              ∏ r, (if Γ''.noGhostPath r = true then ψ (c * ((zdistInf d L (anpKey2_fixLab a b x (ea r) -
                anpKey2_fixLab a b x (eb r)) : ℕ) : ℝ)) else 1) := hIHx
        _ ≤ C * θ ^ q' * ψ 0 ^ (Γ''.ordN - (Γ''.nngh : ℤ)) *
              (ψ 0 ^ ((Γ''.nngh : ℤ) - (Γ.nngh : ℤ)) * G) :=
            mul_le_mul_of_nonneg_left hprod
              (mul_nonneg (mul_nonneg hC.le (pow_pos hθ q').le) (zpow_pos hψ0 _).le)
        _ = K := by rw [hK0, ← hexp]; ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hΓ'' (mul_nonneg (hnn _ _) (hnn _ _))
  calc Γ.valOn ξ a b (anpKey2_region a b π)
      ≤ ∑ x ∈ anpKey2_regionOne a b (π i₀),
          Γ'.val ξ (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r)) :=
        F3 d L ξ hnn a b π
    _ ≤ ∑ x ∈ anpKey2_regionOne a b (π i₀), ξ E₁ x * ξ E₂ x * K := Finset.sum_le_sum hpt
    _ = (∑ x ∈ anpKey2_regionOne a b (π i₀), ξ E₁ x * ξ E₂ x) * K := by rw [Finset.sum_mul]
    _ ≤ θ * K := mul_le_mul_of_nonneg_right (anpKey3_sum_xx ξ θ hnn hrow _ E₁ E₂) hKnn
    _ = _ := by rw [hK0, hG0]; ring

/-! ## 8. Compiled nonempty instances at `d = 3` -/

section Instances

/-- The region pattern of instances (2), (3): `ℳ₁` closer to the `a`-ends, `ℳ₂` strictly closer to the `b`-ends. -/
def anpKey3_pi : Fin 2 → Fin 2 → Bool := fun i _ => decide (i = 1)

/-- `figAux` with the last edge of path 0 (`ℳ₂ y`, edge 4) made ghost: on `anpKey3_pi` the ending edges at `ℳ₁` are
B1 (path 0, edge 0) and A1 (path 1, edge 1); path 1 ends with an A1 edge at `ℳ₂`; no A2. -/
def anpKey3_figAuxMix : NGraph 2 2 where
  es := [⟨false, .inl (.inl 0), .inr 0⟩, ⟨false, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inr 1⟩,
         ⟨false, .inr 0, .inr 1⟩, ⟨true, .inr 1, .inl (.inr 0)⟩, ⟨false, .inr 1, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (2, .inr 1), (4, .inl (.inr 0))]
    else [(1, .inr 0), (3, .inr 1), (5, .inl (.inr 1))]

/-- The hypotheses of instance (1): `figAuxGh` on `π ≡ false` is a legal input of Case (I) (two B1 edges at `ℳ₁`). -/
theorem anpKey3_inst_figAuxGh_hyp :
    anpKey2_figAuxGh.GhostOK ∧ anpKey2_figAuxGh.IsNested ∧ anpKey2_figAuxGh.NoA2 (fun _ _ => false) ∧
      AnpCaseI anpKey2_figAuxGh (fun _ _ => false) := by
  obtain ⟨hG, hN, hno, hcase, -⟩ := anpKey2_inst_figAuxGh
  exact ⟨hG, hN, hno, hcase⟩

/-- Instance (1): B1 + B1 at `ℳ₁` (`figAuxGh`, `π ≡ false`): the target applies at `d = 3`, `q = p = 2`, with every
deterministic hypothesis discharged (`anpKey3_inst_figAuxGh_hyp`); the induction hypothesis `AnpIH 3 2`
(discharged by `anpDetGh_of_step` in LW-12f) is the only premise. -/
theorem anpKey3_inst_figAuxGh :
    AnpIH 3 2 → AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false) := fun hIH =>
  anpDetGhCaseI_holds 3 2 (by norm_num) hIH 2 _ _ anpKey3_inst_figAuxGh_hyp.1
    anpKey3_inst_figAuxGh_hyp.2.1 anpKey3_inst_figAuxGh_hyp.2.2.1 anpKey3_inst_figAuxGh_hyp.2.2.2

/-- The hypotheses of instance (2): `figAux` on `anpKey3_pi` is a legal input of Case (I) (two A1 edges at `ℳ₁`). -/
theorem anpKey3_inst_figAux_hyp :
    figAux.GhostOK ∧ figAux.IsNested ∧ figAux.NoA2 anpKey3_pi ∧ AnpCaseI figAux anpKey3_pi := by
  refine ⟨anpKey2_figAux_ghostOK, figAux_nested.1, ?_, ?_⟩
  all_goals unfold anpKey3_pi; decide +kernel

/-- Instance (2): A1 + A1 at `ℳ₁` (`figAux`, `anpKey3_pi`). -/
theorem anpKey3_inst_figAux :
    figAux.NoA2 anpKey3_pi ∧ AnpCaseI figAux anpKey3_pi ∧ (AnpIH 3 2 → AnpDetGhRegAt 3 figAux anpKey3_pi) :=
  ⟨anpKey3_inst_figAux_hyp.2.2.1, anpKey3_inst_figAux_hyp.2.2.2, fun hIH =>
    anpDetGhCaseI_holds 3 2 (by norm_num) hIH 2 _ _ anpKey3_inst_figAux_hyp.1 anpKey3_inst_figAux_hyp.2.1
      anpKey3_inst_figAux_hyp.2.2.1 anpKey3_inst_figAux_hyp.2.2.2⟩

/-- Instance (3): A1 + B1 at `ℳ₁` (`anpKey3_figAuxMix`, `anpKey3_pi`). -/
theorem anpKey3_inst_figAuxMix :
    anpKey3_figAuxMix.GhostOK ∧ anpKey3_figAuxMix.IsNested ∧ anpKey3_figAuxMix.NoA2 anpKey3_pi ∧
      AnpCaseI anpKey3_figAuxMix anpKey3_pi ∧
      (AnpIH 3 2 → AnpDetGhRegAt 3 anpKey3_figAuxMix anpKey3_pi) := by
  have hG : anpKey3_figAuxMix.GhostOK := by unfold NGraph.GhostOK; decide +kernel
  have hN : anpKey3_figAuxMix.IsNested := by unfold NGraph.IsNested; decide +kernel
  have hno : anpKey3_figAuxMix.NoA2 anpKey3_pi := by unfold anpKey3_pi; decide +kernel
  have hcase : AnpCaseI anpKey3_figAuxMix anpKey3_pi := by unfold anpKey3_pi; decide +kernel
  exact ⟨hG, hN, hno, hcase, fun hIH => anpDetGhCaseI_holds 3 2 (by norm_num) hIH 2 _ _ hG hN hno hcase⟩

/-- Instance (4): the chain with case (I) discharged. -/
theorem anpKey3_inst_chain : AnpDetGhCaseIII 3 → AnpDetGhCaseIV 3 → LWAnpKeyGh 3 :=
  anpKey2_inst_chain (anpDetGhCaseI_holds 3)

/-- The ending-edge types of instances (1)-(3) at `ℳ₁`: B1 + B1 at `figAuxGh`, A1 + A1 at `figAux`, B1 + A1 at
`figAuxMix` (edges `0` of path `0` and `1` of path `1`, first steps). -/
theorem anpKey3_inst_types :
    (anpKey2_figAuxGh.IsB1 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∧
      anpKey2_figAuxGh.IsB1 (fun _ _ => false) 1 false (anpKey2_eGh 1) 0) ∧
    (figAux.IsA1 anpKey3_pi 0 false (anpKey2_eAux 0) 0 ∧ figAux.IsA1 anpKey3_pi 1 false (anpKey2_eAux 1) 0) ∧
    (anpKey3_figAuxMix.IsB1 anpKey3_pi 0 false ⟨0, by decide⟩ 0 ∧
      anpKey3_figAuxMix.IsA1 anpKey3_pi 1 false ⟨1, by decide⟩ 0) := by
  unfold anpKey3_pi
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

/-- `Γ'` ghost-free segments of the fixed graph: the steps of the segment are solid. -/
theorem anpKey3_fixV_ng_iff {p q : ℕ} (Γ : NGraph p (q + 1)) (i₀ : Fin (q + 1)) (s₀ : anpKey2_Seg Γ i₀)
    (s : anpKey2_Seg Γ i₀) :
    (anpKey2_fixV Γ i₀ s₀).noGhostPath (anpKey2_ee Γ i₀ s) = true ↔
      ∀ st ∈ anpKey2_steps Γ i₀ s, (Γ.es.get st.1).ghost = false := by
  rw [anpKey2_noGhost_iff, anpKey2_fixV_path]
  constructor
  · intro h st hst
    have := h _ (List.mem_map.2 ⟨st, hst, rfl⟩)
    rw [anpKey2_fixV_ghost] at this
    exact this
  · intro h st' hst'
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hst'
    rw [anpKey2_fixV_ghost]
    exact h st hst

/-- Every segment of `figAuxGh` fixed at `ℳ₁` without a ghost step contains one of the edges `0`, `1`. -/
theorem anpKey3_figAuxGh_seg :
    ∀ s : anpKey2_Seg anpKey2_figAuxGh 0, (∀ st ∈ anpKey2_steps anpKey2_figAuxGh 0 s,
        (anpKey2_figAuxGh.es.get st.1).ghost = false) →
      ∃ st ∈ anpKey2_steps anpKey2_figAuxGh 0 s, st.1.val = 0 ∨ st.1.val = 1 := by
  decide +kernel

/-- Instance (5): the double ghostify at `figAuxGh` fixed at `ℳ₁` (`i₀ = 0`): `ord` and `n_ngh` as before. -/
theorem anpKey3_inst_gh2 :
    ∃ (p' : ℕ) (Γ'' : NGraph p' 1), Γ''.GhostOK ∧ Γ''.IsNested ∧
      Γ''.ordN = anpKey2_figAuxGh.ordN ∧ Γ''.nngh = anpKey2_figAuxGh.nngh := by
  obtain ⟨s₀, hs₀⟩ := anpKey2_exists_s₀ anpKey2_figAuxGh 0 anpKey2_figAuxGh_nested
  have hG' := anpKey2_fixV_ghostOK anpKey2_figAuxGh 0 anpKey2_figAuxGh_ghostOK anpKey2_figAuxGh_nested s₀
  have hN' := anpKey2_fixV_nested anpKey2_figAuxGh 0 anpKey2_figAuxGh_nested s₀ hs₀
  have e0 : anpKey2_figAuxGh.EndAt 0 false (anpKey2_eGh 0) 0 := by decide +kernel
  have e1 : anpKey2_figAuxGh.EndAt 1 false (anpKey2_eGh 1) 0 := by decide +kernel
  obtain ⟨r₀, h0own, hp0, -⟩ := anpKey2_fixV_end anpKey2_figAuxGh 0 anpKey2_figAuxGh_nested s₀ e0
  obtain ⟨r₁, h1own, hp1, -⟩ := anpKey2_fixV_end anpKey2_figAuxGh 0 anpKey2_figAuxGh_nested s₀ e1
  have hr : r₀ ≠ r₁ := fun h => by
    have : (0 : Fin 2) = 1 := by rw [← h0own, ← h1own, h]
    exact absurd this (by decide)
  have g0 : ((anpKey2_fixV anpKey2_figAuxGh 0 s₀).es.get (anpKey2_em anpKey2_figAuxGh 0 s₀ (anpKey2_eGh 0))).ghost
      = false := by
    rw [anpKey2_fixV_ghost]; decide +kernel
  have g1 : ((anpKey2_fixV anpKey2_figAuxGh 0 s₀).es.get (anpKey2_em anpKey2_figAuxGh 0 s₀ (anpKey2_eGh 1))).ghost
      = false := by
    rw [anpKey2_fixV_ghost]; decide +kernel
  obtain ⟨hG'', hN'', hS'', hng'', -⟩ := anpKey3_gh2_props _ hG' hN' hr hp0 hp1 g0 g1
  refine ⟨_, anpKey3_gh2 (anpKey2_fixV anpKey2_figAuxGh 0 s₀) (anpKey2_em anpKey2_figAuxGh 0 s₀ (anpKey2_eGh 0))
    (anpKey2_em anpKey2_figAuxGh 0 s₀ (anpKey2_eGh 1)), hG'', hN'', ?_, ?_⟩
  · have h8 := anpKey2_fixV_nSolid anpKey2_figAuxGh 0 s₀
    have h : (anpKey3_gh2 (anpKey2_fixV anpKey2_figAuxGh 0 s₀) (anpKey2_em anpKey2_figAuxGh 0 s₀ (anpKey2_eGh 0))
      (anpKey2_em anpKey2_figAuxGh 0 s₀ (anpKey2_eGh 1))).nSolid + 2 = anpKey2_figAuxGh.nSolid := by
      rw [← h8]; exact hS''
    unfold NGraph.ordN
    simp only [ord]
    omega
  · have hz : anpKey2_figAuxGh.nngh = 0 := by decide +kernel
    rw [hz]
    unfold NGraph.nngh
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r _ hr'
    obtain ⟨s, rfl⟩ := (anpKey2_ee anpKey2_figAuxGh 0).surjective r
    obtain ⟨hng, hn0, hn1⟩ := (hng'' _).1 hr'
    obtain ⟨st, hst, hst01⟩ := anpKey3_figAuxGh_seg s
      ((anpKey3_fixV_ng_iff anpKey2_figAuxGh 0 s₀ s).1 hng)
    have hmem : (anpKey2_em anpKey2_figAuxGh 0 s₀ st.1,
        anpKey2_rel0 anpKey2_figAuxGh 0 (Sum.inl (Sum.inr (anpKey2_ee anpKey2_figAuxGh 0 s))) st.2) ∈
        (anpKey2_fixV anpKey2_figAuxGh 0 s₀).path (anpKey2_ee anpKey2_figAuxGh 0 s) := by
      rw [anpKey2_fixV_path]
      exact List.mem_map.2 ⟨st, hst, rfl⟩
    rcases hst01 with h | h
    · have hk : st.1 = anpKey2_eGh 0 := Fin.ext h
      rw [hk] at hmem
      exact hN'.2.2.2.1 _ r₀ hn0 _ hmem
        (anpKey2_em anpKey2_figAuxGh 0 s₀ (anpKey2_eGh 0), Sum.inl (Sum.inr r₀)) (by rw [hp0]; simp) rfl
    · have hk : st.1 = anpKey2_eGh 1 := Fin.ext h
      rw [hk] at hmem
      exact hN'.2.2.2.1 _ r₁ hn1 _ hmem
        (anpKey2_em anpKey2_figAuxGh 0 s₀ (anpKey2_eGh 1), Sum.inl (Sum.inr r₁)) (by rw [hp1]; simp) rfl

end Instances

end RBM.Graph
