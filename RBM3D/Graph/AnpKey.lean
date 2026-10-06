/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWPins
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# LW-12a: `lem:Anp_key_gh`, deterministic form, base case, assembly and the `≺`-lift (T2234)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `lem:Anp`
(`(eq:bddGamma_aux)` `:935`), `lem:Anp_key` (`:960`, `(eq:Gbyxi3)` `:963-966`, "easy corollary" `:1025`),
`lem:Anp_key_gh` (`:1041`, `(adsuu22)` `:1043`), the base case `q = 0` (`:1110`).  Part a of the six
tickets of `lem:Anp` (the induction step, cases (I)-(IV), is LW-12b-f).

* Section 1: the deterministic bound `AnpDetGhAt` (`(adsuu22)` with exact inequalities), `AnpDetGh`,
  `AnpDetGhZero`, `AnpDetGhStep`.
* Section 2: the base case `anpDetGh_zero` (`q = 0`; the walk along a path, the triangle inequality for
  `zdistInf`, the chosen edges).
* Section 3: the A2 replacement `NGraph.ghostify` (`7_8:1143-1148`) and its bookkeeping.
* Section 4: the assembly `anpDetGh_of_step`.
* Section 5: the `≺`-lift `lwAnpKeyGh_of_det`.
* Section 6: the merged reductions `lwAnpKey_of_gh`, `lwAnp_of_key`.
* Section 7: compiled nonempty instances at `d = 3`.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes Filter

/-! ## 1. The deterministic `(adsuu22)` -/

/-- The deterministic bound of `lem:Anp_key_gh` (`(adsuu22)`, `7_8:1043`) for one nested graph `Γ`: constants
`C, c > 0` (`c ≤ 1`) depending on `Γ` and `d` only such that, for every torus `Z_L^d`, every positive `ψ`
non-increasing on `[0, ∞)`, every `θ > 0` and every symmetric `ξ ≥ 0` with `ξ_{αβ} ≤ ψ(|α-β|)` and
`Σ_β ξ_{αβ}² ≤ θ` (the deterministic form of `(eq:Gbyxi3)`, `7_8:963-966`, with `θ = (W^d η_t)⁻¹`),
`𝒢_{ab} ≤ C θ^q ψ(0)^{ord - n_ngh} Π_i ψ(c|a_i - b_i|)^{χ(𝔓_i)}`. -/
def AnpDetGhAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          Γ.val ξ a b ≤ C * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
            ∏ i, (if Γ.noGhostPath i = true then
              ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)

/-- The deterministic `lem:Anp_key_gh` for every nested graph with the ghost condition (the `q ≤ p` of the merged
pin is implied by property (3) of `IsNested` at `A = univ` and is not assumed). -/
def AnpDetGh (d : ℕ) : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → AnpDetGhAt d Γ

/-- The base case `q = 0` of the induction (`7_8:1110`, "trivial by `(eq:Gbyxi3)`"): no internal vertex; every
path without a ghost edge is a walk through external vertices only, its longest edge has length
`≥ |a_i - b_i| / (its length)`, the paths are edge-disjoint. -/
def AnpDetGhZero (d : ℕ) : Prop :=
  ∀ (p : ℕ) (Γ : NGraph p 0), Γ.GhostOK → Γ.IsNested → AnpDetGhAt d Γ

/-- The induction step (`7_8:1110-1599`, cases (I)–(IV) after the A2 replacement `(eq:noA2)`): the bound for
every graph with fewer internal vertices, and any number of paths, gives it for `q` internal vertices.
Proved by LW-12b…f (split in the ticket); here a hypothesis. -/
def AnpDetGhStep (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q →
    (∀ (p' k : ℕ), k < q → ∀ Γ' : NGraph p' k, Γ'.GhostOK → Γ'.IsNested → AnpDetGhAt d Γ') →
    ∀ (p : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → AnpDetGhAt d Γ

/-! ## 2. The base case `q = 0` (`7_8:1110`) -/

section Lattice

variable {d L : ℕ} [NeZero L]

/-- Triangle inequality for `zdistInf` (coordinatewise `zdist_add_le`, then `Finset.sup`).  Ported from the
private `farEntry_zdistInf_add_le` (`RBM3D/Evolution/FarEntry.lean:117`). -/
theorem anpKey_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

/-- Ported from the private `farEntry_zdistInf_neg` (`RBM3D/Evolution/FarEntry.lean:127`). -/
theorem anpKey_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

/-- `|x - y|_∞ = |y - x|_∞`.  Ported from the private `farEntry_zdistInf_comm`
(`RBM3D/Evolution/FarEntry.lean:136`). -/
theorem anpKey_zdistInf_sub_comm (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub y x, anpKey_zdistInf_neg]

theorem anpKey_zdistInf_tri (x y z : Zd d L) :
    zdistInf d L (x - z) ≤ zdistInf d L (x - y) + zdistInf d L (y - z) := by
  have e : x - z = (x - y) + (y - z) := by abel
  rw [e]
  exact anpKey_zdistInf_add_le _ _

end Lattice

/-- The step of `WalkOK`. -/
private def anpKey_stepFn {p q : ℕ} (Γ : NGraph p q) (acc : Option (NV p q))
    (st : Fin Γ.es.length × NV p q) : Option (NV p q) :=
  acc.bind fun c =>
    if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
        ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none

private theorem anpKey_foldl_none {p q : ℕ} (Γ : NGraph p q) (l : List (Fin Γ.es.length × NV p q)) :
    l.foldl (anpKey_stepFn Γ) none = none := by
  induction l with
  | nil => rfl
  | cons st t ih => simpa [List.foldl_cons, anpKey_stepFn] using ih

/-- The walk lemma: a walk `x = v_0, …, v_k = y` whose steps all have `|lbl u - lbl v|_∞ ≤ M` has
`|lbl x - lbl y|_∞ ≤ k M`. -/
theorem anpKey_walk {p q : ℕ} (Γ : NGraph p q) {d L : ℕ} [NeZero L] (lbl : NV p q → Zd d L) (M : ℕ) :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q),
      l.foldl (anpKey_stepFn Γ) (some x) = some y →
      (∀ st ∈ l, zdistInf d L (lbl (Γ.es.get st.1).u - lbl (Γ.es.get st.1).v) ≤ M) →
      zdistInf d L (lbl x - lbl y) ≤ l.length * M := by
  intro l
  induction l with
  | nil =>
    intro x y h _
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    simp [zdistInf]
  | cons st t ih =>
    intro x y h hM
    rw [List.foldl_cons] at h
    by_cases hc : ((Γ.es.get st.1).u = x ∧ (Γ.es.get st.1).v = st.2) ∨
        ((Γ.es.get st.1).v = x ∧ (Γ.es.get st.1).u = st.2)
    · have hstep : anpKey_stepFn Γ (some x) st = some st.2 := by
        unfold anpKey_stepFn
        dsimp only [Option.bind]
        split_ifs
        rfl
      rw [hstep] at h
      have h1 := ih st.2 y h (fun s hs => hM s (List.mem_cons_of_mem _ hs))
      have h2 : zdistInf d L (lbl x - lbl st.2) ≤ M := by
        have hm := hM st List.mem_cons_self
        rcases hc with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · rwa [hu, hv] at hm
        · rw [hu, hv] at hm
          rwa [anpKey_zdistInf_sub_comm] at hm
      have h3 := anpKey_zdistInf_tri (lbl x) (lbl st.2) (lbl y)
      rw [List.length_cons]
      nlinarith
    · have hstep : anpKey_stepFn Γ (some x) st = none := by
        unfold anpKey_stepFn
        dsimp only [Option.bind]
        split_ifs
        rfl
      rw [hstep, anpKey_foldl_none] at h
      exact absurd h (by simp)

/-- A path `a_i → b_i` of a nested graph has a step whose edge is at least `|lbl a_i - lbl b_i|_∞ / (length)`
long, for any labelling `lbl` of the vertices. -/
theorem anpKey_long_edge {p q : ℕ} (Γ : NGraph p q) {d L : ℕ} [NeZero L] (lbl : NV p q → Zd d L)
    (i : Fin p) (hW : Γ.WalkOK i) :
    ∃ st ∈ Γ.path i, zdistInf d L (lbl (Sum.inl (Sum.inl i)) - lbl (Sum.inl (Sum.inr i))) ≤
      (Γ.path i).length *
        zdistInf d L (lbl (Γ.es.get st.1).u - lbl (Γ.es.get st.1).v) := by
  have hW' : (Γ.path i).foldl (anpKey_stepFn Γ) (some (Sum.inl (Sum.inl i))) =
      some (Sum.inl (Sum.inr i)) := hW
  have hne : (Γ.path i).toFinset.Nonempty := by
    by_contra hcon
    have h0 : Γ.path i = [] := by
      rw [Finset.not_nonempty_iff_eq_empty, List.toFinset_eq_empty_iff] at hcon
      exact hcon
    rw [h0] at hW'
    simp at hW'
  obtain ⟨st, hst, hmax⟩ := Finset.exists_max_image (Γ.path i).toFinset
    (fun st => zdistInf d L (lbl (Γ.es.get st.1).u - lbl (Γ.es.get st.1).v)) hne
  refine ⟨st, List.mem_toFinset.1 hst, ?_⟩
  exact anpKey_walk Γ lbl _ (Γ.path i) _ _ hW' (fun s hs => hmax s (List.mem_toFinset.2 hs))


/-- The list product as a product over the indices. -/
private theorem anpKey_prod_eq {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).prod = ∏ j : Fin l.length, f l[j.1] := by
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]

/-- The number of elements of a list satisfying a predicate, as a sum over the indices. -/
private theorem anpKey_filter_len {α : Type*} (l : List α) (P : α → Bool) :
    (l.filter P).length = ∑ j : Fin l.length, if P l[j.1] = true then 1 else 0 := by
  have h1 : (l.filter P).length = (l.map fun e => if P e = true then 1 else 0).sum := by
    induction l with
    | nil => simp
    | cons a t ih =>
      by_cases h : P a = true
      · simp [h, ih]
        omega
      · simp [h, ih]
  rw [h1, ← List.ofFn_getElem_eq_map, List.sum_ofFn]

/-- `n_S` as a cardinality of indices. -/
private theorem anpKey_nSolid_card {p q : ℕ} (Γ : NGraph p q) :
    Γ.nSolid = (Finset.univ.filter fun j : Fin Γ.es.length => (Γ.es[j.1]).ghost = false).card := by
  unfold NGraph.nSolid
  rw [anpKey_filter_len, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases (Γ.es[j.1]).ghost <;> simp

/-- The base-case bound for one labelling of the (absent) internal vertices: the product of the edge
factors is at most `ψ(0)^{n_S - n_ngh} Π_{i ghost-free} ψ(c |a_i - b_i|)`, `c = 1/K`, `K` bounding the
lengths of the paths. -/
private theorem anpKey_zero_prod {d L : ℕ} [NeZero L] {p : ℕ} (Γ : NGraph p 0) (hN : Γ.IsNested)
    (K : ℕ) (hK : ∀ i, (Γ.path i).length ≤ K) (ψ : ℝ → ℝ) (hanti : AntitoneOn ψ (Set.Ici 0))
    (hpos : ∀ r : ℝ, 0 ≤ r → 0 < ψ r) (ξ : Zd d L → Zd d L → ℝ) (hnn : ∀ α β, 0 ≤ ξ α β)
    (hξψ : ∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ))
    (a b : Fin p → Zd d L) (ℓ : Fin 0 → Zd d L) :
    Γ.nngh ≤ Γ.nSolid ∧
    (Γ.es.map fun e => if e.ghost then (1 : ℝ) else
        ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod ≤
      ψ 0 ^ (Γ.nSolid - Γ.nngh) *
        ∏ i, (if Γ.noGhostPath i = true then
          ψ ((1 / (max K 1 : ℕ) : ℝ) * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) := by
  classical
  set lbl : NV p 0 → Zd d L := Sum.elim (Sum.elim a b) ℓ with hlbl
  have hK1 : (1 : ℝ) ≤ ((max K 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right K 1
  have hKpos : (0 : ℝ) < ((max K 1 : ℕ) : ℝ) := lt_of_lt_of_le one_pos hK1
  -- the chosen long edge of each path
  have hlong : ∀ i, ∃ st ∈ Γ.path i,
      zdistInf d L (a i - b i) ≤ (Γ.path i).length *
        zdistInf d L (lbl (Γ.es.get st.1).u - lbl (Γ.es.get st.1).v) :=
    fun i => anpKey_long_edge Γ lbl i (hN.2.1 i)
  choose st hstmem hstle using hlong
  set ch : Fin p → Fin Γ.es.length := fun i => (st i).1 with hch
  have hinj : Function.Injective ch := by
    intro i j hij
    by_contra hne
    exact hN.2.2.2.1 i j hne (st i) (hstmem i) (st j) (hstmem j) hij
  set S : Finset (Fin p) := Finset.univ.filter fun i => Γ.noGhostPath i = true with hS
  set J : Finset (Fin Γ.es.length) := S.image ch with hJ
  set G : Finset (Fin Γ.es.length) :=
    Finset.univ.filter fun j : Fin Γ.es.length => (Γ.es[j.1]).ghost = false with hG
  have hcardJ : J.card = Γ.nngh := by
    rw [hJ, Finset.card_image_of_injective _ hinj]
    rfl
  -- chosen edges are solid
  have hsolid : ∀ i ∈ S, (Γ.es[(ch i).1]).ghost = false := by
    intro i hi
    have hi' : Γ.noGhostPath i = true := (Finset.mem_filter.1 hi).2
    unfold NGraph.noGhostPath at hi'
    rw [List.all_eq_true] at hi'
    have := hi' (st i) (hstmem i)
    simpa using this
  have hJG : J ⊆ G := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hsolid i hi⟩
  have hGcard : G.card = Γ.nSolid := (anpKey_nSolid_card Γ).symm
  refine ⟨?_, ?_⟩
  · rw [← hcardJ, ← hGcard]
    exact Finset.card_le_card hJG
  -- the factors
  set w : Fin Γ.es.length → ℝ := fun j =>
    if (Γ.es[j.1]).ghost then (1 : ℝ) else ξ (lbl (Γ.es[j.1]).u) (lbl (Γ.es[j.1]).v) with hw
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j; simp only [hw]; split_ifs
    · exact zero_le_one
    · exact hnn _ _
  set w' : Fin Γ.es.length → ℝ := fun j => if (Γ.es[j.1]).ghost then (1 : ℝ) else ψ 0 with hw'
  have hww' : ∀ j, w j ≤ w' j := by
    intro j; simp only [hw, hw']; split_ifs
    · exact le_rfl
    · refine (hξψ _ _).trans (hanti ?_ ?_ ?_)
      · exact Set.mem_Ici.2 le_rfl
      · exact Set.mem_Ici.2 (Nat.cast_nonneg _)
      · exact Nat.cast_nonneg _
  have hchosen : ∀ i ∈ S, w (ch i) ≤
      ψ ((1 / (max K 1 : ℕ) : ℝ) * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) := by
    intro i hi
    have hg := hsolid i hi
    have hwi : w (ch i) = ξ (lbl (Γ.es[(ch i).1]).u) (lbl (Γ.es[(ch i).1]).v) := by
      simp only [hw, hg]; simp
    rw [hwi]
    refine (hξψ _ _).trans (hanti ?_ ?_ ?_)
    · exact Set.mem_Ici.2 (by positivity)
    · exact Set.mem_Ici.2 (Nat.cast_nonneg _)
    · -- `c D_i ≤ E`
      have h1 := hstle i
      have h2 : ((zdistInf d L (a i - b i) : ℕ) : ℝ) ≤ ((max K 1 : ℕ) : ℝ) *
          ((zdistInf d L (lbl (Γ.es.get (st i).1).u - lbl (Γ.es.get (st i).1).v) : ℕ) : ℝ) := by
        have h3 : (Γ.path i).length ≤ max K 1 := (hK i).trans (le_max_left _ _)
        exact_mod_cast h1.trans (Nat.mul_le_mul_right _ h3)
      have : zdistInf d L (lbl (Γ.es.get (st i).1).u - lbl (Γ.es.get (st i).1).v) = zdistInf d L
          (lbl (Γ.es[(ch i).1]).u - lbl (Γ.es[(ch i).1]).v) := rfl
      rw [one_div, inv_mul_le_iff₀ hKpos]
      rw [this] at h2
      linarith
  -- the product
  rw [anpKey_prod_eq]
  have hprod : ∀ j : Fin Γ.es.length, ((fun e : NEdge p 0 => if e.ghost then (1 : ℝ) else
      ξ (lbl e.u) (lbl e.v)) Γ.es[j.1]) = w j := fun j => rfl
  simp only [hprod]
  rw [← Finset.prod_mul_prod_compl J w]
  have hJprod : ∏ j ∈ J, w j ≤ ∏ i, (if Γ.noGhostPath i = true then
      ψ ((1 / (max K 1 : ℕ) : ℝ) * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) := by
    rw [hJ, Finset.prod_image (fun i _ j _ h => hinj h)]
    rw [← Finset.prod_filter]
    exact Finset.prod_le_prod₀ (fun i _ => hw0 _) hchosen
  have hCprod : ∏ j ∈ Jᶜ, w j ≤ ψ 0 ^ (Γ.nSolid - Γ.nngh) := by
    refine (Finset.prod_le_prod₀ (fun j _ => hw0 j) (fun j _ => hww' j)).trans ?_
    simp only [hw']
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    refine le_of_eq ?_
    congr 1
    rw [← hcardJ, ← hGcard, ← Finset.card_sdiff_of_subset hJG]
    congr 1
    ext j
    simp [hG, and_comm]
  have hψ0 : 0 ≤ ψ 0 ^ (Γ.nSolid - Γ.nngh) := (pow_pos (hpos 0 le_rfl) _).le
  calc (∏ j ∈ J, w j) * ∏ j ∈ Jᶜ, w j
      ≤ (∏ i, (if Γ.noGhostPath i = true then
          ψ ((1 / (max K 1 : ℕ) : ℝ) * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)) *
          ψ 0 ^ (Γ.nSolid - Γ.nngh) :=
        mul_le_mul hJprod hCprod (Finset.prod_nonneg fun j _ => hw0 j)
          (Finset.prod_nonneg fun i _ => by
            split_ifs
            · exact (hpos _ (by positivity)).le
            · exact zero_le_one)
    _ = _ := mul_comm _ _


/-- **The base case `q = 0`** (`7_8:1110`, "trivial by `(eq:Gbyxi3)`"): `C = 1`, `c = 1 / max(1, max_i |𝔓_i|)`.
There is no internal vertex, so `𝒢_{ab} = Π_e (ghost ? 1 : ξ_e)`; each path without a ghost edge is a walk
`a_i → b_i` of solid edges, one of whose edges has length `≥ |a_i - b_i| / |𝔓_i|`; the chosen edges are
distinct (the paths are edge-disjoint) and every other solid edge is at most `ψ(0)`. -/
theorem anpDetGh_zero (d : ℕ) : AnpDetGhZero d := by
  intro p Γ _ hN
  have hK1 : (1 : ℝ) ≤ (((max (Finset.univ.sup fun i : Fin p => (Γ.path i).length) 1 : ℕ)) : ℝ) := by
    exact_mod_cast le_max_right _ 1
  refine ⟨1, 1 / (((max (Finset.univ.sup fun i : Fin p => (Γ.path i).length) 1 : ℕ)) : ℝ),
    one_pos, by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    exact hK1
  · intro L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
    have hKi : ∀ i, (Γ.path i).length ≤ Finset.univ.sup fun i : Fin p => (Γ.path i).length :=
      fun i => Finset.le_sup (f := fun i : Fin p => (Γ.path i).length) (Finset.mem_univ i)
    unfold NGraph.val
    rw [Fintype.sum_unique]
    obtain ⟨hle, hprod⟩ := anpKey_zero_prod Γ hN _ hKi ψ hanti hpos ξ (fun α β => (hξ α β).1) hξψ a b
      (@default (Fin 0 → Zd d L) Unique.instInhabited)
    have hord : Γ.ordN - (Γ.nngh : ℤ) = ((Γ.nSolid - Γ.nngh : ℕ) : ℤ) := by
      unfold NGraph.ordN
      simp only [ord]
      omega
    rw [hord, zpow_natCast, pow_zero, mul_one, one_mul]
    exact hprod


/-! ## 3. The A2 replacement `ghostify` (`7_8:1143-1148`, `(eq:noA2)`) -/

section Ghostify

variable {p q : ℕ}

/-- The edge list of `ghostify`: the edge `j` becomes a ghost edge. -/
def NGraph.ghostifyEs (Γ : NGraph p q) (j : Fin Γ.es.length) : List (NEdge p q) :=
  Γ.es.set j.1 { Γ.es[j.1] with ghost := true }

/-- The index map `Fin |es| → Fin |es'|` of `ghostify`. -/
def NGraph.ghostifyIdx (Γ : NGraph p q) (j : Fin Γ.es.length) (i : Fin Γ.es.length) :
    Fin (Γ.ghostifyEs j).length :=
  Fin.cast (List.length_set).symm i

/-- The A2 replacement (`7_8:1143-1148`): the edge `j` becomes a ghost edge; endpoints and paths unchanged. -/
@[reducible] def NGraph.ghostify (Γ : NGraph p q) (j : Fin Γ.es.length) : NGraph p q where
  es := Γ.ghostifyEs j
  path := fun i => (Γ.path i).map fun st => (Γ.ghostifyIdx j st.1, st.2)

variable (Γ : NGraph p q) (j : Fin Γ.es.length)

theorem anpKey_gf_get (i : Fin Γ.es.length) :
    (Γ.ghostifyEs j).get (Γ.ghostifyIdx j i) =
      if i = j then { Γ.es.get i with ghost := true } else Γ.es.get i := by
  simp only [NGraph.ghostifyEs, NGraph.ghostifyIdx, List.get_eq_getElem, Fin.val_cast, List.getElem_set]
  by_cases h : i = j
  · subst h; simp
  · have : ¬ (j.1 = i.1) := fun h' => h (Fin.ext h'.symm)
    simp [h, this]

theorem anpKey_gf_u (i : Fin Γ.es.length) :
    ((Γ.ghostifyEs j).get (Γ.ghostifyIdx j i)).u = (Γ.es.get i).u := by
  rw [anpKey_gf_get]; split_ifs <;> rfl

theorem anpKey_gf_v (i : Fin Γ.es.length) :
    ((Γ.ghostifyEs j).get (Γ.ghostifyIdx j i)).v = (Γ.es.get i).v := by
  rw [anpKey_gf_get]; split_ifs <;> rfl

theorem anpKey_gf_ghost (i : Fin Γ.es.length) :
    ((Γ.ghostifyEs j).get (Γ.ghostifyIdx j i)).ghost = (decide (i = j) || (Γ.es.get i).ghost) := by
  rw [anpKey_gf_get]; by_cases h : i = j <;> simp [h]

theorem anpKey_gf_idx_inj : Function.Injective (Γ.ghostifyIdx j) := by
  intro a b h
  have h' := congrArg Fin.val h
  exact Fin.ext h'

theorem anpKey_gf_idx_surj (i' : Fin (Γ.ghostify j).es.length) : ∃ i, Γ.ghostifyIdx j i = i' :=
  ⟨Fin.cast List.length_set i', Fin.ext rfl⟩


theorem anpKey_gf_path (i : Fin p) :
    (Γ.ghostify j).path i = (Γ.path i).map fun st => (Γ.ghostifyIdx j st.1, st.2) := rfl

theorem anpKey_gf_visits (i : Fin p) (v : NV p q) : (Γ.ghostify j).Visits i v ↔ Γ.Visits i v := by
  unfold NGraph.Visits
  rw [anpKey_gf_path]
  constructor
  · rintro ⟨st', hst', h⟩
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hst'
    exact ⟨st, hst, by rwa [anpKey_gf_u, anpKey_gf_v] at h⟩
  · rintro ⟨st, hst, h⟩
    exact ⟨_, List.mem_map.2 ⟨st, hst, rfl⟩, by rwa [anpKey_gf_u, anpKey_gf_v]⟩

theorem anpKey_gf_walkOK (i : Fin p) (h : Γ.WalkOK i) : (Γ.ghostify j).WalkOK i := by
  unfold NGraph.WalkOK at h ⊢
  rw [anpKey_gf_path, List.foldl_map]
  simp only [anpKey_gf_u, anpKey_gf_v]
  exact h

/-- The A2 replacement keeps the nested properties (they speak of the endpoints and the paths only). -/
theorem anpKey_ghostify_nested (h : Γ.IsNested) : (Γ.ghostify j).IsNested := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, fun i => anpKey_gf_walkOK Γ j i (h2 i), ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i', rfl⟩ := List.mem_iff_get.1 he
    obtain ⟨i, rfl⟩ := anpKey_gf_idx_surj Γ j i'
    rw [anpKey_gf_u, anpKey_gf_v]
    exact h1 _ (List.get_mem _ _)
  · intro i
    have := (h3 i).map (anpKey_gf_idx_inj Γ j)
    rw [anpKey_gf_path, List.map_map]
    simpa [Function.comp_def, List.map_map] using this
  · intro i i' hne st hst st' hst'
    rw [anpKey_gf_path] at hst hst'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hst
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hst'
    intro heq
    exact h4 i i' hne s hs s' hs' (anpKey_gf_idx_inj Γ j heq)
  · intro α
    obtain ⟨i, i', hne, hv, hv'⟩ := h5 α
    exact ⟨i, i', hne, (anpKey_gf_visits Γ j i _).2 hv, (anpKey_gf_visits Γ j i' _).2 hv'⟩
  · intro A
    refine (h6 A).trans (le_of_eq ?_)
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, anpKey_gf_visits]


theorem anpKey_gf_ghost' (i : Fin Γ.es.length) :
    ((Γ.ghostify j).es.get (Γ.ghostifyIdx j i)).ghost = (decide (i = j) || (Γ.es.get i).ghost) :=
  anpKey_gf_ghost Γ j i


/-- The edge `st₀.1` lies on one path only, at one step. -/
theorem anpKey_gf_key (hN : Γ.IsNested) {i₀ : Fin p} {st₀ : Fin Γ.es.length × NV p q}
    (hst₀ : st₀ ∈ Γ.path i₀) : ∀ i, ∀ st ∈ Γ.path i, st.1 = st₀.1 → i = i₀ ∧ st = st₀ := by
  intro i st hst h1
  by_cases hi : i = i₀
  · subst hi
    exact ⟨rfl, List.inj_on_of_nodup_map (hN.2.2.1 i) hst hst₀ h1⟩
  · exact absurd h1 (hN.2.2.2.1 i i₀ hi st hst st₀ hst₀)

/-- The A2 replacement of a solid ending edge `st₀.1` of a ghost-free path `i₀` has the ghost condition. -/
theorem anpKey_ghostify_ghostOK (hG : Γ.GhostOK) (hN : Γ.IsNested) {i₀ : Fin p}
    (hn : Γ.noGhostPath i₀ = true) {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀)
    (hend : (Γ.path i₀).head? = some st₀ ∨ (Γ.path i₀).getLast? = some st₀) :
    (Γ.ghostify st₀.1).GhostOK := by
  have hgh : ∀ st ∈ Γ.path i₀, (Γ.es.get st.1).ghost = false := by
    intro st hst
    unfold NGraph.noGhostPath at hn
    rw [List.all_eq_true] at hn
    simpa using hn st hst
  have key := anpKey_gf_key Γ hN hst₀
  intro i
  rw [anpKey_gf_path]
  refine ⟨?_, ?_⟩
  · rw [List.filter_map, List.length_map]
    by_cases hi : i = i₀
    · subst hi
      have hnd : ((Γ.path i).filter ((fun st' => ((Γ.ghostify st₀.1).es.get st'.1).ghost) ∘
          fun st => (Γ.ghostifyIdx st₀.1 st.1, st.2))).Nodup :=
        ((hN.2.2.1 i).of_map Prod.fst).filter _
      have hsub : ((Γ.path i).filter ((fun st' => ((Γ.ghostify st₀.1).es.get st'.1).ghost) ∘
          fun st => (Γ.ghostifyIdx st₀.1 st.1, st.2))) ⊆ [st₀] := by
        intro st hst
        rw [List.mem_filter] at hst
        obtain ⟨hst1, hst2⟩ := hst
        have h3 : (decide (st.1 = st₀.1) || (Γ.es.get st.1).ghost) = true := by
          have := hst2
          simp only [Function.comp_apply] at this
          rw [anpKey_gf_ghost'] at this
          exact this
        rw [hgh st hst1, Bool.or_false, decide_eq_true_eq] at h3
        exact List.mem_singleton.2 (key i st hst1 h3).2
      exact (hnd.subperm hsub).length_le
    · have : (Γ.path i).filter ((fun st' => ((Γ.ghostify st₀.1).es.get st'.1).ghost) ∘
          fun st => (Γ.ghostifyIdx st₀.1 st.1, st.2)) =
          (Γ.path i).filter fun st => (Γ.es.get st.1).ghost := by
        refine List.filter_congr fun st hst => ?_
        simp only [Function.comp_apply]
        rw [anpKey_gf_ghost']
        have : ¬ (st.1 = st₀.1) := fun h => hi (key i st hst h).1
        simp [this]
      rw [this]
      exact (hG i).1
  · intro st' hst' hg'
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hst'
    have hg'' : (decide (st.1 = st₀.1) || (Γ.es.get st.1).ghost) = true := by
      rw [← anpKey_gf_ghost']
      exact hg'
    have hinj : Function.Injective fun st : Fin Γ.es.length × NV p q =>
        (Γ.ghostifyIdx st₀.1 st.1, st.2) := by
      intro a b h
      have h1 := anpKey_gf_idx_inj Γ st₀.1 (Prod.mk.inj h).1
      exact Prod.ext h1 (Prod.mk.inj h).2
    have hmap : ∀ (c : Fin Γ.es.length × NV p q) (l : List (Fin Γ.es.length × NV p q)),
        (l.head? = some c ∨ l.getLast? = some c) →
        ((l.map fun st => (Γ.ghostifyIdx st₀.1 st.1, st.2)).head? =
            some (Γ.ghostifyIdx st₀.1 c.1, c.2) ∨
          (l.map fun st => (Γ.ghostifyIdx st₀.1 st.1, st.2)).getLast? =
            some (Γ.ghostifyIdx st₀.1 c.1, c.2)) := by
      intro c l hl
      rcases hl with hl | hl
      · left; rw [List.head?_map, hl]; rfl
      · right; rw [List.getLast?_map, hl]; rfl
    by_cases hi : i = i₀
    · subst hi
      rw [hgh st hst, Bool.or_false, decide_eq_true_eq] at hg''
      obtain ⟨-, rfl⟩ := key i st hst hg''
      exact hmap st _ hend
    · have h1 : ¬ (st.1 = st₀.1) := fun h => hi (key i st hst h).1
      simp only [h1, decide_false, Bool.false_or] at hg''
      exact hmap st _ ((hG i).2 st hst hg'')


private theorem anpKey_gf_ghostFalse {i₀ : Fin p} (hn : Γ.noGhostPath i₀ = true)
    {st : Fin Γ.es.length × NV p q} (hst : st ∈ Γ.path i₀) : (Γ.es.get st.1).ghost = false := by
  unfold NGraph.noGhostPath at hn
  rw [List.all_eq_true] at hn
  simpa using hn st hst

/-- The A2 replacement has one solid edge less. -/
theorem anpKey_ghostify_nSolid {i₀ : Fin p} (hn : Γ.noGhostPath i₀ = true)
    {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) :
    (Γ.ghostify st₀.1).nSolid + 1 = Γ.nSolid := by
  rw [anpKey_nSolid_card, anpKey_nSolid_card]
  set G : Finset (Fin Γ.es.length) :=
    Finset.univ.filter fun i : Fin Γ.es.length => (Γ.es[i.1]).ghost = false with hG
  have hjG : st₀.1 ∈ G := by
    rw [hG, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using anpKey_gf_ghostFalse Γ hn hst₀⟩
  have himg : (Finset.univ.filter fun i' : Fin (Γ.ghostify st₀.1).es.length =>
      ((Γ.ghostify st₀.1).es[i'.1]).ghost = false) = (G.erase st₀.1).image (Γ.ghostifyIdx st₀.1) := by
    ext i'
    obtain ⟨i, rfl⟩ := anpKey_gf_idx_surj Γ st₀.1 i'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase, hG]
    constructor
    · intro h
      have h0 := anpKey_gf_ghost' Γ st₀.1 i
      simp only [List.get_eq_getElem] at h0
      rw [h] at h0
      have h' := h0.symm
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h'
      exact ⟨i, ⟨h'.1, h'.2⟩, rfl⟩
    · rintro ⟨i2, ⟨h1, h2⟩, h3⟩
      obtain rfl := anpKey_gf_idx_inj Γ st₀.1 h3
      have := anpKey_gf_ghost' Γ st₀.1 i2
      simp only [List.get_eq_getElem] at this
      rw [this]
      simp [h1, h2]
  rw [himg, Finset.card_image_of_injective _ (anpKey_gf_idx_inj Γ st₀.1), Finset.card_erase_of_mem hjG]
  have : 0 < G.card := Finset.card_pos.2 ⟨_, hjG⟩
  omega


theorem anpKey_gf_noGhostPath_iff (hN : Γ.IsNested) {i₀ : Fin p}
    {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) (i : Fin p) :
    (Γ.ghostify st₀.1).noGhostPath i = true ↔ Γ.noGhostPath i = true ∧ i ≠ i₀ := by
  have key := anpKey_gf_key Γ hN hst₀
  unfold NGraph.noGhostPath
  rw [anpKey_gf_path, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h
    have h1 : ∀ st ∈ Γ.path i, (decide (st.1 = st₀.1) || (Γ.es.get st.1).ghost) = false := by
      intro st hst
      have := h _ (List.mem_map.2 ⟨st, hst, rfl⟩)
      rw [anpKey_gf_ghost'] at this
      simpa using this
    refine ⟨fun st hst => ?_, ?_⟩
    · have := h1 st hst
      simpa using (Bool.or_eq_false_iff.1 this).2
    · rintro rfl
      have := h1 st₀ hst₀
      simp at this
  · rintro ⟨h1, h2⟩ st' hst'
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hst'
    have h3 : ¬ (st.1 = st₀.1) := fun h => h2 (key i st hst h).1
    have h4 := h1 st hst
    rw [anpKey_gf_ghost']
    simp only [Bool.not_eq_true'] at h4 ⊢
    simp only [h3, decide_false, Bool.false_or, h4]

/-- The A2 replacement has one ghost-free path less. -/
theorem anpKey_ghostify_nngh (hN : Γ.IsNested) {i₀ : Fin p} (hn : Γ.noGhostPath i₀ = true)
    {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) :
    (Γ.ghostify st₀.1).nngh + 1 = Γ.nngh := by
  unfold NGraph.nngh
  have hE : (Finset.univ.filter fun i : Fin p => (Γ.ghostify st₀.1).noGhostPath i = true) =
      (Finset.univ.filter fun i : Fin p => Γ.noGhostPath i = true).erase i₀ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      anpKey_gf_noGhostPath_iff Γ hN hst₀]
    tauto
  have hmem : i₀ ∈ Finset.univ.filter fun i : Fin p => Γ.noGhostPath i = true := by simpa using hn
  rw [hE, Finset.card_erase_of_mem hmem]
  have := Finset.card_pos.2 ⟨_, hmem⟩
  omega

/-- **The A2 replacement does not change `ord - n_ngh`** (`(eq:noA2)`, `7_8:1146`): one solid edge less
and one ghost-free path less. -/
theorem anpKey_ghostify_ord (hN : Γ.IsNested) {i₀ : Fin p} (hn : Γ.noGhostPath i₀ = true)
    {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) :
    (Γ.ghostify st₀.1).ordN - ((Γ.ghostify st₀.1).nngh : ℤ) = Γ.ordN - (Γ.nngh : ℤ) := by
  have h1 := anpKey_ghostify_nSolid Γ hn hst₀
  have h2 := anpKey_ghostify_nngh Γ hN hn hst₀
  unfold NGraph.ordN
  simp only [ord]
  omega

end Ghostify

/-! ## 4. The assembly by strong induction on `q` -/

/-- **The assembly**: `AnpDetGhZero` (the base case) and `AnpDetGhStep` (the induction step) give the
deterministic `lem:Anp_key_gh` for every `q` and every `p` (strong induction on `q`). -/
theorem anpDetGh_of_step : ∀ d : ℕ, AnpDetGhZero d → AnpDetGhStep d → AnpDetGh d := by
  intro d h0 hs p q
  induction q using Nat.strong_induction_on generalizing p with
  | _ q ih =>
    intro Γ hG hN
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact h0 p Γ hG hN
    · exact hs q hq (fun p' k hk Γ' hG' hN' => ih k hk p' Γ' hG' hN') p Γ hG hN

/-! ## 5. The `≺`-lift (`7_8:1041-1077` read with `≺`) -/

/-- `Π_i (if S i then x f_i else 1) = x^{#S} Π_i (if S i then f_i else 1)`. -/
private theorem anpKey_prod_ite_mul {p : ℕ} (S : Fin p → Prop) [DecidablePred S] (x : ℝ) (f : Fin p → ℝ) :
    ∏ i, (if S i then x * f i else 1) =
      x ^ (Finset.univ.filter S).card * ∏ i, (if S i then f i else 1) := by
  have h1 : ∀ i, (if S i then x * f i else 1) = (if S i then x else 1) * (if S i then f i else 1) := by
    intro i; split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

/-- The deterministic bound at `(ψ, θ) = (x Φ, x θ_n)`, `x = N^{τ'} ≥ 1`, rewritten with the common factor
`x^{q + k + n_ngh}` taken out. -/
private theorem anpKey_rescale {p q : ℕ} (Γ : NGraph p q) (x C θ Φ0 : ℝ) (hx : 0 < x) (Φ : Fin p → ℝ) :
    C * (x * θ) ^ q * (x * Φ0) ^ (Γ.ordN - (Γ.nngh : ℤ)) *
        ∏ i, (if Γ.noGhostPath i = true then x * Φ i else 1) =
      C * x ^ ((q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ)) *
        (θ ^ q * Φ0 ^ (Γ.ordN - (Γ.nngh : ℤ)) * ∏ i, (if Γ.noGhostPath i = true then Φ i else 1)) := by
  rw [anpKey_prod_ite_mul (fun i => Γ.noGhostPath i = true) x Φ, mul_pow, mul_zpow,
    zpow_add₀ hx.ne', zpow_add₀ hx.ne', zpow_natCast, zpow_natCast]
  have : (Finset.univ.filter fun i => Γ.noGhostPath i = true).card = Γ.nngh := rfl
  rw [this]
  ring

/-- **The `≺`-lift** (`7_8:1041-1077`, "`≺` throughout"): the deterministic bound `AnpDetGh` on the event
`Ξ_n = {ξ ≤ N^{τ'} Φ_n(|α-β|) ∀ α β} ∩ {Σ_β ξ² ≤ N^{τ'} θ_n ∀ α}` (which holds w.h.p. by the two `≺`
premises of `LWXi`, `Prec.whp`, `HighProbAt.inter`), with `ψ = N^{τ'} Φ_n`, `θ = N^{τ'} θ_n`,
`θ_n = (W^d η_t)⁻¹` and `τ' = τ / (2 (q + |ord - n_ngh| + p + 1))`; the factor `C N^{τ'(q + k + n_ngh)}` is
at most `N^τ` for large `n`.  The union over the pairs `(a, b)` is inside `badSetAt`, so no union bound over
`Z_L^{2d}` is needed.  `η_t > 0` comes from `STFlow` and `t ≤ lemT z`. -/
theorem lwAnpKeyGh_of_det : ∀ d : ℕ, AnpDetGh d → LWAnpKeyGh d := by
  intro d hdet hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ hG hN ε₀ C₁ C₂ C₃ Cc
  obtain ⟨C, c, hC, hc, -, H⟩ := hdet p q Γ hG hN
  refine ⟨c, hc, ?_⟩
  intro 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ
  obtain ⟨hξnn, hξ1, hξ2⟩ := hξ
  have hsz' : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hflow.1.2.2.1
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hη : ∀ n, 0 < etaT (STflowE z n) (t n) := by
    intro n
    have hz : 0 < (z n).im :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (hN1 n)) _) (hflow.2 n).2.1
    exact etaT_pos (abs_lemE_lt_two hz) (lt_of_le_of_lt (htT n) (lemT_lt_one hz))
  have hθ : ∀ n, 0 < ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ := fun n =>
    inv_pos.2 (mul_pos (pow_pos (by exact_mod_cast sz.W_pos n) d) (hη n))
  intro τ hτ D hD
  -- the exponents
  set k : ℤ := Γ.ordN - (Γ.nngh : ℤ) with hk
  set M : ℕ := q + k.natAbs + p with hM
  set τ' : ℝ := τ / (2 * ((M : ℝ) + 1)) with hτ'
  have hτ'pos : 0 < τ' := by positivity
  have hτ'M : τ' * (M : ℝ) ≤ τ / 2 := by
    rw [hτ']
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the good event
  have hΞ := RBM.Gauss.HighProbAt.inter hsz (Sizes.Prec.whp sz hξ1 hτ'pos) (Sizes.Prec.whp sz hξ2 hτ'pos)
  have hev1 : ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → 0 < Φ n r :=
    hΦ.2.1.1.mono fun n hn r hr => (hn r hr).1
  have hev2 : ∀ᶠ n in atTop, C ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsz').eventually_ge_atTop C
  filter_upwards [hΞ D hD, hev1, hev2] with n hn hΦn hCn
  refine le_trans (MeasureTheory.measure_mono ?_) hn
  rintro ω ⟨u, hu⟩ ⟨h1, h2⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set x : ℝ := N ^ τ' with hx
  set θn : ℝ := ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ with hθn
  have hx1 : 1 ≤ x := Real.one_le_rpow (hN1 n) hτ'pos.le
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hN0 : 0 ≤ N := (zero_le_one.trans (hN1 n))
  have hψ : AntitoneOn (fun r => x * Φ n r) (Set.Ici 0) := fun a ha b hb hab =>
    mul_le_mul_of_nonneg_left (hΦ.2.2.1 n ha hb hab) hx0.le
  have hdet := H (sz.L n) (fun r => x * Φ n r) (x * θn) hψ (fun r hr => mul_pos hx0 (hΦn r hr))
    (mul_pos hx0 (hθ n)) (fun α β => ξ n α β ω) (fun α β => hξnn n α β ω) (fun α β => h1 (α, β)) h2
    u.1 u.2
  have hrs := anpKey_rescale Γ x C θn (Φ n 0) hx0
    (fun i => Φ n (c * ((zdistInf d (sz.L n) (u.1 i - u.2 i) : ℕ) : ℝ)))
  have hζ0 : 0 ≤ θn ^ q * Φ n 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
      ∏ i, (if Γ.noGhostPath i = true then
        Φ n (c * ((zdistInf d (sz.L n) (u.1 i - u.2 i) : ℕ) : ℝ)) else 1) := by
    refine mul_nonneg (mul_nonneg (pow_nonneg (hθ n).le _) (zpow_nonneg (hΦn 0 le_rfl).le _))
      (Finset.prod_nonneg fun i _ => ?_)
    split_ifs
    · exact (hΦn _ (by positivity)).le
    · exact zero_le_one
  have hexp : x ^ ((q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ)) ≤ N ^ (τ / 2) := by
    have hm : (q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ) ≤ (M : ℤ) := by
      have h1 : (Γ.ordN - (Γ.nngh : ℤ)) ≤ ((Γ.ordN - (Γ.nngh : ℤ)).natAbs : ℤ) := Int.le_natAbs
      have h2 : Γ.nngh ≤ p := by
        unfold NGraph.nngh
        exact (Finset.card_filter_le _ _).trans (by simp)
      have h2' : (Γ.nngh : ℤ) ≤ p := by exact_mod_cast h2
      have h3 : (M : ℤ) = q + ((Γ.ordN - (Γ.nngh : ℤ)).natAbs : ℤ) + p := by simp only [hM]; push_cast; ring
      rw [h3]
      linarith
    calc x ^ ((q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ)) ≤ x ^ (M : ℤ) :=
          zpow_le_zpow_right₀ hx1 hm
      _ = N ^ (τ' * (M : ℝ)) := by
          rw [zpow_natCast, hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
      _ ≤ N ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le (hN1 n) hτ'M
  have hfin : Γ.val (fun α β => ξ n α β ω) u.1 u.2 ≤ N ^ τ *
      (θn ^ q * Φ n 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
        ∏ i, (if Γ.noGhostPath i = true then
          Φ n (c * ((zdistInf d (sz.L n) (u.1 i - u.2 i) : ℕ) : ℝ)) else 1)) := by
    refine (hdet.trans (le_of_eq hrs)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hζ0
    calc C * x ^ ((q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ)) ≤ N ^ (τ / 2) * N ^ (τ / 2) :=
          mul_le_mul hCn hexp (zpow_nonneg hx0.le _) (Real.rpow_nonneg hN0 _)
      _ = N ^ τ := by rw [← Real.rpow_add (lt_of_lt_of_le one_pos (hN1 n))]; congr 1; ring
  exact absurd hu (not_lt.2 hfin)

/-! ## 6. The merged reductions `LWAnpKeyGh → LWAnpKey → LWAnp` (`7_8:1025`, `7_8:933-939`) -/

section Reductions

variable {p q : ℕ} {Γ : NGraph p q}

theorem anpKey_ghost_false (h : Γ.NoGhost) (j : Fin Γ.es.length) : (Γ.es[j.1]).ghost = false :=
  h _ (List.getElem_mem _)

/-- No ghost edge gives the ghost condition. -/
theorem anpKey_ghostOK_of_noGhost (h : Γ.NoGhost) : Γ.GhostOK := by
  intro i
  refine ⟨?_, fun st _ hg => ?_⟩
  · have : (Γ.path i).filter (fun st => (Γ.es.get st.1).ghost) = [] := by
      rw [List.filter_eq_nil_iff]
      intro st _
      simp [anpKey_ghost_false h]
    rw [this]
    simp
  · simp [anpKey_ghost_false h] at hg

theorem anpKey_noGhostPath_of_noGhost (h : Γ.NoGhost) (i : Fin p) : Γ.noGhostPath i = true := by
  unfold NGraph.noGhostPath
  rw [List.all_eq_true]
  intro st _
  simp [anpKey_ghost_false h]

theorem anpKey_nngh_of_noGhost (h : Γ.NoGhost) : Γ.nngh = p := by
  unfold NGraph.nngh
  rw [Finset.filter_true_of_mem (fun i _ => anpKey_noGhostPath_of_noGhost h i)]
  simp

end Reductions

private theorem anpKey_stochDomAt_congr {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {U : ℕ → Type*} {size : ℕ → ℕ} {ξ ζ ζ' : ∀ l, U l → Ω → ℝ}
    (h : StochDomAt P size ξ ζ) (hζ : ∀ l u ω, ζ l u ω = ζ' l u ω) : StochDomAt P size ξ ζ' := by
  have : ζ = ζ' := funext fun l => funext fun u => funext fun ω => hζ l u ω
  exact this ▸ h

/-- **`lem:Anp_key` from `lem:Anp_key_gh`** (`7_8:1025`, "an easy corollary"): no ghost edge gives `GhostOK`,
`noGhostPath i = true` for every `i`, `n_ngh = p`. -/
theorem lwAnpKey_of_gh : ∀ d : ℕ, LWAnpKeyGh d → LWAnpKey d := by
  intro d h hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ hng hnest ε₀ C₁ C₂ C₃ Cc
  obtain ⟨c, hc, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ (anpKey_ghostOK_of_noGhost hng) hnest
    ε₀ C₁ C₂ C₃ Cc
  refine ⟨c, hc, ?_⟩
  intro 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ
  exact anpKey_stochDomAt_congr (H 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ) fun n ab ω => by
    simp [anpKey_noGhostPath_of_noGhost hng, anpKey_nngh_of_noGhost hng]

/-- **`lem:Anp` from `lem:Anp_key`** (`7_8:987-989`): the special case `a_i ≡ [a]`, `b_i ≡ [b]`
(the auxiliary graph of a locally standard graph is a nested graph, `7_8:956`). -/
theorem lwAnp_of_key : ∀ d : ℕ, LWAnpKey d → LWAnp d := by
  intro d h hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ hng hnest ε₀ C₁ C₂ C₃ Cc
  obtain ⟨c, hc, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ hng hnest ε₀ C₁ C₂ C₃ Cc
  refine ⟨c, hc, ?_⟩
  intro 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ
  have h2 := StochDomAt.precomp_param (H 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ)
    (V := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (fun n ab => ((fun _ => ab.1 : Fin p → Zd d (sz.L n)), (fun _ => ab.2 : Fin p → Zd d (sz.L n))))
  refine anpKey_stochDomAt_congr h2 fun n ab ω => ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_right_comm _ _ _


/-! ## 7. Compiled nonempty instances at `d = 3` -/

section Instances

/-- Instance (1): the one-edge graph `a_0 — b_0` (`p = 1`, `q = 0`, one solid edge, one path). -/
def anpKey_oneEdge : NGraph 1 0 where
  es := [⟨false, .inl (.inl 0), .inl (.inr 0)⟩]
  path := fun _ => [(0, .inl (.inr 0))]

theorem anpKey_oneEdge_nested : anpKey_oneEdge.IsNested := by
  unfold NGraph.IsNested
  decide +kernel

theorem anpKey_oneEdge_ghostOK : anpKey_oneEdge.GhostOK := by
  unfold NGraph.GhostOK
  decide +kernel

private theorem anpKey_zdist_three_le (u : ZMod 3) : zdist 3 u ≤ 1 := by
  revert u
  decide

private theorem anpKey_zdistInf_three_le (x : Zd 3 3) : zdistInf 3 3 x ≤ 1 :=
  Finset.sup_le fun i _ => anpKey_zdist_three_le (x i)

/-- **The base case at the one-edge graph** (`d = 3`, `L = 3`, `ψ r = (1 + r)⁻¹`, `θ = 1`,
`ξ ≡ 1/6`, `a ≡ 0`, `b ≡ 1`, `|a - b| = 1`): every deterministic hypothesis of `anpDetGh_zero` is
discharged. -/
theorem anpKey_inst_zero :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      anpKey_oneEdge.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤
        C * (1 : ℝ) ^ 0 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (anpKey_oneEdge.ordN - (anpKey_oneEdge.nngh : ℤ)) *
          ∏ i, (if anpKey_oneEdge.noGhostPath i = true then
            (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ))
            else 1) := by
  obtain ⟨C, c, hC, hc, hc1, H⟩ := anpDetGh_zero 3 1 anpKey_oneEdge anpKey_oneEdge_ghostOK
    anpKey_oneEdge_nested
  refine ⟨C, c, hC, hc, hc1, H 3 (fun r : ℝ => (1 + r)⁻¹) 1 ?_ ?_ one_pos (fun _ _ => 1 / 6)
    (fun _ _ => ⟨by norm_num, rfl⟩) ?_ ?_ (fun _ => 0) (fun _ => 1)⟩
  · intro a ha b hb hab
    have ha' : (0 : ℝ) ≤ a := ha
    exact inv_anti₀ (by linarith) (by linarith)
  · intro r hr
    exact inv_pos.2 (by linarith)
  · intro α β
    have h1 : ((zdistInf 3 3 (α - β) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast anpKey_zdistInf_three_le _
    have h2 : (0 : ℝ) ≤ ((zdistInf 3 3 (α - β) : ℕ) : ℝ) := Nat.cast_nonneg _
    change (1 / 6 : ℝ) ≤ (1 + ((zdistInf 3 3 (α - β) : ℕ) : ℝ))⁻¹
    rw [← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · intro α
    simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    norm_num

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.LWInst in
/-- Instance (2): the chain `AnpDetGhStep 3 → LWAnp 3`, used as the `h` of the merged `inst_Anp` (the edge
variables `ξ` and their bounds `(eq:Gbyxi3)` stay hypotheses; the induction step is LW-12b-f). -/
theorem anpKey_inst_anp (hs : AnpDetGhStep 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
        (fun n ab ω => figAux.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 *
          Φ0 n 0 ^ (figAux.ordN - (2 : ℕ))) :=
  inst_Anp (lwAnp_of_key 3 (lwAnpKey_of_gh 3 (lwAnpKeyGh_of_det 3
    (anpDetGh_of_step 3 (anpDetGh_zero 3) hs)))) ξ hξ

/-- Instance (3): `figAux` (`q = 2`, the output of LW-11a) is a legal input of the deterministic bound:
`GhostOK` from `figAux_nested.2` and the reduction `anpKey_ghostOK_of_noGhost`; the bound at `figAux` from the
assembled lemma. -/
theorem anpKey_inst_figAux (h : AnpDetGh 3) : AnpDetGhAt 3 figAux :=
  h 2 2 figAux (anpKey_ghostOK_of_noGhost figAux_nested.2) figAux_nested.1

/-- Instance (3'): the same from the step alone (the base case is proved). -/
theorem anpKey_inst_figAux_step (hs : AnpDetGhStep 3) : AnpDetGhAt 3 figAux :=
  anpKey_inst_figAux (anpDetGh_of_step 3 (anpDetGh_zero 3) hs)

/-- Instance (4): the A2 replacement at `figAux` (`p = q = 2`, six solid edges): the first step `(0, [x]→ℳ₁)` of
the first path is made ghost; the result is still nested and has the ghost condition, with one solid edge
and one ghost-free path less (`ord - n_ngh` stays `0`). -/
theorem anpKey_inst_ghostify :
    let st₀ : Fin figAux.es.length × NV 2 2 := (⟨0, by decide⟩, Sum.inr 0)
    (figAux.ghostify st₀.1).GhostOK ∧ (figAux.ghostify st₀.1).IsNested ∧
      (figAux.ghostify st₀.1).nSolid = 5 ∧ (figAux.ghostify st₀.1).nngh = 1 ∧
      (figAux.ghostify st₀.1).ordN - ((figAux.ghostify st₀.1).nngh : ℤ) = 0 := by
  intro st₀
  have hn : figAux.noGhostPath (0 : Fin 2) = true := by decide +kernel
  have hpath : figAux.path 0 = [st₀, ((⟨2, by decide⟩ : Fin figAux.es.length), Sum.inr 1),
      ((⟨4, by decide⟩ : Fin figAux.es.length), Sum.inl (Sum.inr 0))] := by
    simp [figAux, st₀]
  have hst : st₀ ∈ figAux.path 0 := by rw [hpath]; exact List.mem_cons_self
  have hend : (figAux.path 0).head? = some st₀ ∨ (figAux.path 0).getLast? = some st₀ :=
    Or.inl (by rw [hpath]; rfl)
  have hN := figAux_nested.1
  have h1 := anpKey_ghostify_nSolid figAux hn hst
  have h2 := anpKey_ghostify_nngh figAux hN hn hst
  have h3 := anpKey_ghostify_ord figAux hN hn hst
  have hs : figAux.nSolid = 6 := by decide +kernel
  have hg : figAux.nngh = 2 := by decide +kernel
  have ho : figAux.ordN = 2 := figAux_ord
  refine ⟨anpKey_ghostify_ghostOK figAux (anpKey_ghostOK_of_noGhost figAux_nested.2) hN hn hst hend,
    anpKey_ghostify_nested figAux st₀.1 hN, by omega, by omega, ?_⟩
  rw [h3, ho, hg]
  norm_num

end Instances

end RBM.Graph
