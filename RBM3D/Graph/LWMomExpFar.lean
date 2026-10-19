/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey6
import RBM3D.Graph.AuxGraph

/-!
# The far part of `lem:LW_moment_exp`: the deterministic bound on the "and" domain

Paper: Section 7.5: the split of `f` into `f^{≤ℓ} + f^{>ℓ}`, Lemma 7.25
(`lem:LW_moment_exp_far`, (7.57)) and its proof (the domain `𝐃_{>ℓ}`, `(adsuu33)` (7.59), the
"long ending edge", `(adsuu44)` (7.60)).

The far domain is `𝐃_{>ℓ} = {c : |a_i - c|_∞ > ℓ and |b_i - c|_∞ > ℓ for all i}`, and the factor of
path `i` is `𝖳_t(|a_i - b_i|_∞ ∧ ℓ)` (a path with no internal vertex is the edge `a_i b_i`).

* Section 1: the vocabulary `lwMomExpFar_farDAnd`, `lwMomExpFar_ownExt`, `lwMomExpFar_HeadFar` and the
  statements `AnpFarHeadAt`, `AnpFarHead`, `AnpFarAndAt`, `AnpFarAnd`.
* Section 2: the head of a path of a nested graph with `ownExt`.
* Section 3: ghostify the head of every path (`NGraph.ghostify`, iterated).
* Section 4: `lwMomExpFar_head`: the far bound, from `anpDetGh_holds` with `ψ r = 𝖳_t(r ∧ ℓ)`.
* Section 5: `lwMomExpFar_and`.
* Section 6: the nested graph of an auxiliary graph has `ownExt` (`lwMomExpFar_auxGraph_ownExt`).
-/

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss

/-! ## 1. Vocabulary and statements -/

/-- The far domain `𝐃_{>ℓ}` (proof of Lemma 7.25): `|a_i - c|_∞ > ℓ` **and**
`|b_i - c|_∞ > ℓ` for every `i`. -/
def lwMomExpFar_farDAnd (d L : ℕ) [NeZero L] {p : ℕ} (a b : Fin p → Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c => ∀ i : Fin p,
    ℓ < ((zdistInf d L (a i - c) : ℕ) : ℝ) ∧ ℓ < ((zdistInf d L (b i - c) : ℕ) : ℝ)

/-- The path `𝔓_i` meets no external vertex other than its own `a_i`, `b_i` (the outputs of
`lwAuxNested_holds` have it: `auxGraph_nodeV Dt i` takes only the values `a_i`, `b_i`, internal). -/
def lwMomExpFar_ownExt {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∀ i : Fin p, ∀ st ∈ Γ.path i,
    st.2 = Sum.inl (Sum.inl i) ∨ st.2 = Sum.inl (Sum.inr i) ∨ ∃ α : Fin q, st.2 = Sum.inr α

/-- The labellings `S` put the internal vertex reached by the first step of each path at `L^∞` distance `> ℓ`
from that path's `a_i`. -/
def lwMomExpFar_HeadFar (d L : ℕ) [NeZero L] {p q : ℕ} (Γ : NGraph p q) (a : Fin p → Zd d L) (ℓ : ℝ)
    (S : Finset (Fin q → Zd d L)) : Prop :=
  ∀ lab ∈ S, ∀ (i : Fin p) (st : Fin Γ.es.length × NV p q) (α : Fin q),
    (Γ.path i).head? = some st → st.2 = Sum.inr α → ℓ < ((zdistInf d L (a i - lab α) : ℕ) : ℝ)

/-- **Far core** (`(adsuu33)` (7.59), `(adsuu44)` (7.60), deterministic): truncated edges
`ξ ≤ 𝖳_t(|α-β|_∞ ∧ ℓ)`, row sums `≤ θ`; for every set `S` of internal labellings with `lwMomExpFar_HeadFar`,
`Σ_{ℓ∈S} Π ≤ C θ^q 𝖳_t(0)^{ord - p} Π_i 𝖳_t(|a_i - b_i| ∧ ℓ)`; `C` depends on `Γ`, `d` only. -/
def AnpFarHeadAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t θ ℓ : ℝ), 0 < W → t < 1 → 0 < θ → 0 ≤ ℓ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ (a b : Fin p → Zd d L) (S : Finset (Fin q → Zd d L)), lwMomExpFar_HeadFar d L Γ a ℓ S →
          Γ.valOn ξ a b S ≤
            C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) *
              ∏ i, sfT d L W g t (min ((zdistInf d L (a i - b i) : ℕ) : ℝ) ℓ)

def AnpFarHead (d : ℕ) : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → AnpFarHeadAt d Γ

/-- **The far bound, "and" domain**: every internal label in `𝐃_{>ℓ}`. -/
def AnpFarAndAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t θ ℓ : ℝ), 0 < W → t < 1 → 0 < θ → 0 ≤ ℓ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          Γ.valOn ξ a b (Fintype.piFinset fun _ : Fin q => lwMomExpFar_farDAnd d L a b ℓ) ≤
            C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) *
              ∏ i, sfT d L W g t (min ((zdistInf d L (a i - b i) : ℕ) : ℝ) ℓ)

def AnpFarAnd (d : ℕ) : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → AnpFarAndAt d Γ

/-! ## 2. The head of a path -/

section Head

variable {p q : ℕ}

private theorem lwMomExpFar_foldl_none {α β : Type*} (f : Option α → β → Option α)
    (hf : ∀ x, f none x = none) (l : List β) : l.foldl f none = none := by
  induction l with
  | nil => rfl
  | cons x t ih => simpa [List.foldl_cons, hf] using ih

/-- Every path of a nested graph is non-empty (`WalkOK` with `a_i ≠ b_i` as vertices). -/
theorem lwMomExpFar_path_ne_nil {Γ : NGraph p q} (hN : Γ.IsNested) (i : Fin p) : Γ.path i ≠ [] := by
  intro h
  have hW := hN.2.1 i
  unfold NGraph.WalkOK at hW
  rw [h] at hW
  simp at hW

/-- The first fold step of `WalkOK`: the first step of the path `i` is an edge `{a_i, st.2}`. -/
theorem lwMomExpFar_first_step {Γ : NGraph p q} {i : Fin p} (hW : Γ.WalkOK i)
    {st : Fin Γ.es.length × NV p q} {rest : List (Fin Γ.es.length × NV p q)}
    (h : Γ.path i = st :: rest) :
    ((Γ.es.get st.1).u = Sum.inl (Sum.inl i) ∧ (Γ.es.get st.1).v = st.2) ∨
      ((Γ.es.get st.1).v = Sum.inl (Sum.inl i) ∧ (Γ.es.get st.1).u = st.2) := by
  by_contra hc
  unfold NGraph.WalkOK at hW
  rw [h, List.foldl_cons] at hW
  simp only [Option.bind_some, hc, ite_false] at hW
  rw [lwMomExpFar_foldl_none _ (fun x => rfl)] at hW
  simp at hW

/-- The head of path `i` (with `IsNested`, `ownExt`): the edge is `{a_i, st.2}` and `st.2` is `b_i` or internal. -/
theorem lwMomExpFar_head_vertex {Γ : NGraph p q} (hN : Γ.IsNested) (hO : lwMomExpFar_ownExt Γ) {i : Fin p}
    {st : Fin Γ.es.length × NV p q} (hst : (Γ.path i).head? = some st) :
    (((Γ.es.get st.1).u = Sum.inl (Sum.inl i) ∧ (Γ.es.get st.1).v = st.2) ∨
      ((Γ.es.get st.1).v = Sum.inl (Sum.inl i) ∧ (Γ.es.get st.1).u = st.2)) ∧
    (st.2 = Sum.inl (Sum.inr i) ∨ ∃ α : Fin q, st.2 = Sum.inr α) := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.1 hst
  have hstep := lwMomExpFar_first_step (hN.2.1 i) hrest
  refine ⟨hstep, ?_⟩
  have hmem : st ∈ Γ.path i := by rw [hrest]; exact List.mem_cons_self
  have hne := hN.1 (Γ.es.get st.1) (List.get_mem _ _)
  rcases hO i st hmem with h | h | h
  · exfalso
    rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hne (h1.trans (h2.trans h).symm)
    · exact hne ((h2.trans h).trans h1.symm)
  · exact Or.inl h
  · exact Or.inr h

/-- With symmetric `ξ`, the factor of the head edge of path `i` is `ξ(lab a_i, lab st.2)`. -/
theorem lwMomExpFar_head_factor {ι : Type*} {Γ : NGraph p q} (hN : Γ.IsNested) {i : Fin p}
    {st : Fin Γ.es.length × NV p q} (hst : (Γ.path i).head? = some st) (ξ : ι → ι → ℝ)
    (hξ : ∀ u v, ξ u v = ξ v u) (lab : NV p q → ι) :
    ξ (lab (Γ.es.get st.1).u) (lab (Γ.es.get st.1).v) = ξ (lab (Sum.inl (Sum.inl i))) (lab st.2) := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.1 hst
  rcases lwMomExpFar_first_step (hN.2.1 i) hrest with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact hξ _ _

end Head

/-! ## 3. Ghostify the head of every path -/

section Ghost

variable {p q : ℕ}

/-- The path `i` as the list of its steps `((u, v), next)`: endpoints of the edge and the vertex reached.
`ghostify` does not change it (`lwMomExpFar_walk_ghostify`). -/
def lwMomExpFar_walk (Γ : NGraph p q) (i : Fin p) : List ((NV p q × NV p q) × NV p q) :=
  (Γ.path i).map fun st => (((Γ.es.get st.1).u, (Γ.es.get st.1).v), st.2)

/-- The endpoints `(u, v)` of the first edge of path `i` (default `(a_i, a_i)` on an empty path). -/
def lwMomExpFar_headE (Γ : NGraph p q) (i : Fin p) : NV p q × NV p q :=
  ((lwMomExpFar_walk Γ i).headD ((Sum.inl (Sum.inl i), Sum.inl (Sum.inl i)), Sum.inl (Sum.inl i))).1

theorem lwMomExpFar_walk_ghostify (Γ : NGraph p q) (j : Fin Γ.es.length) (i : Fin p) :
    lwMomExpFar_walk (Γ.ghostify j) i = lwMomExpFar_walk Γ i := by
  unfold lwMomExpFar_walk
  rw [anpKey_gf_path, List.map_map]
  refine List.map_congr_left fun st _ => ?_
  simp only [Function.comp_apply]
  rw [anpKey_gf_u, anpKey_gf_v]

theorem lwMomExpFar_headE_eq {Γ : NGraph p q} {i : Fin p} {st : Fin Γ.es.length × NV p q}
    (hst : (Γ.path i).head? = some st) :
    lwMomExpFar_headE Γ i = ((Γ.es.get st.1).u, (Γ.es.get st.1).v) := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.1 hst
  unfold lwMomExpFar_headE lwMomExpFar_walk
  rw [hrest]
  rfl

private theorem lwMomExpFar_ghost_false {Γ : NGraph p q} {i : Fin p} (hn : Γ.noGhostPath i = true)
    {st : Fin Γ.es.length × NV p q} (hst : st ∈ Γ.path i) : (Γ.es.get st.1).ghost = false := by
  unfold NGraph.noGhostPath at hn
  rw [List.all_eq_true] at hn
  simpa using hn st hst

/-- Ghostify the first edges of the paths in `T`, one after another: the nested graph `Γ'` has `GhostOK`, the same
steps `walk`, ghost-free exactly the paths outside `T`, the same `ord - n_ngh`, and the value factor
`Π_{i ∈ T} ξ(head edge i)` split off (proof of Lemma 7.24, `(eq:noA2)` (7.43), `anpKey2_ep_ghostify`). -/
theorem lwMomExpFar_ghost_heads (Γ : NGraph p q)
    (hNG : Γ.NoGhost) (hN : Γ.IsNested) (T : Finset (Fin p)) :
    ∃ Γ' : NGraph p q, Γ'.IsNested ∧ Γ'.GhostOK ∧ (∀ i, lwMomExpFar_walk Γ' i = lwMomExpFar_walk Γ i) ∧
      (∀ i, Γ'.noGhostPath i = true ↔ i ∉ T) ∧
      Γ'.ordN - (Γ'.nngh : ℤ) = Γ.ordN - (Γ.nngh : ℤ) ∧
      ∀ {ι : Type} (ξ : ι → ι → ℝ) (lab : NV p q → ι), anpKey2_ep Γ ξ lab =
        (∏ i ∈ T, ξ (lab (lwMomExpFar_headE Γ i).1) (lab (lwMomExpFar_headE Γ i).2)) *
          anpKey2_ep Γ' ξ lab := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨Γ, hN, anpKey_ghostOK_of_noGhost hNG, fun _ => rfl, fun i => ?_, rfl, ?_⟩
    · simp [anpKey_noGhostPath_of_noGhost hNG i]
    · intro ι ξ lab; simp
  | insert i T hi ih =>
    obtain ⟨Γ₁, hN₁, hG₁, hw, hn₁, hord₁, hep₁⟩ := ih
    have hn : Γ₁.noGhostPath i = true := (hn₁ i).2 hi
    obtain ⟨st₀, rest, hrest⟩ := List.exists_cons_of_ne_nil (lwMomExpFar_path_ne_nil hN₁ i)
    have hst₀ : st₀ ∈ Γ₁.path i := by rw [hrest]; exact List.mem_cons_self
    have hhead : (Γ₁.path i).head? = some st₀ := by rw [hrest]; rfl
    have hk : (Γ₁.es.get st₀.1).ghost = false := lwMomExpFar_ghost_false hn hst₀
    have hE : lwMomExpFar_headE Γ i = ((Γ₁.es.get st₀.1).u, (Γ₁.es.get st₀.1).v) := by
      have : lwMomExpFar_headE Γ₁ i = lwMomExpFar_headE Γ i := by
        unfold lwMomExpFar_headE; rw [hw i]
      rw [← this]
      exact lwMomExpFar_headE_eq hhead
    refine ⟨Γ₁.ghostify st₀.1, anpKey_ghostify_nested Γ₁ st₀.1 hN₁,
      anpKey_ghostify_ghostOK Γ₁ hG₁ hN₁ hn hst₀ (Or.inl hhead),
      fun j => (lwMomExpFar_walk_ghostify Γ₁ st₀.1 j).trans (hw j), fun j => ?_,
      (anpKey_ghostify_ord Γ₁ hN₁ hn hst₀).trans hord₁, ?_⟩
    · rw [anpKey_gf_noGhostPath_iff Γ₁ hN₁ hst₀ j, hn₁ j, Finset.mem_insert]
      tauto
    · intro ι ξ lab
      rw [Finset.prod_insert hi, hep₁ ξ lab, anpKey2_ep_ghostify Γ₁ ξ lab st₀.1 hk, hE]
      ring

end Ghost

/-! ## 4. `lwMomExpFar_head`: the far bound from `anpDetGh_holds` -/

section Far

variable {p q : ℕ}

/-- All heads ghostified: `nngh = 0`, `ord - n_ngh = ord - p`, and the product of the head factors split off. -/
theorem lwMomExpFar_ghost_all (Γ : NGraph p q) (hNG : Γ.NoGhost) (hN : Γ.IsNested) :
    ∃ Γ' : NGraph p q, Γ'.IsNested ∧ Γ'.GhostOK ∧ (∀ i, Γ'.noGhostPath i = false) ∧
      Γ'.ordN - (Γ'.nngh : ℤ) = Γ.ordN - (p : ℤ) ∧
      ∀ {ι : Type} (ξ : ι → ι → ℝ) (lab : NV p q → ι), anpKey2_ep Γ ξ lab =
        (∏ i, ξ (lab (lwMomExpFar_headE Γ i).1) (lab (lwMomExpFar_headE Γ i).2)) *
          anpKey2_ep Γ' ξ lab := by
  obtain ⟨Γ', hN', hG', -, hn, hord, hep⟩ := lwMomExpFar_ghost_heads Γ hNG hN Finset.univ
  refine ⟨Γ', hN', hG', fun i => ?_, ?_, hep⟩
  · have := hn i
    simpa using this
  · rw [hord, anpKey_nngh_of_noGhost hNG]

private theorem lwMomExpFar_sfT_pos {d L : ℕ} [NeZero L] {W g t : ℝ} (hW : 0 < W) (ht : t < 1) {r : ℝ}
    (hr : 0 ≤ r) : 0 < sfT d L W g t r := by
  unfold sfT
  have h0 : 0 < |1 - t| := abs_pos.2 (by linarith)
  have h1 : 0 < g ^ 2 + |1 - t| := by positivity
  have h2 : 0 < r + 1 := by linarith
  positivity

/-- **The far bound, head form** (`(adsuu33)`-`(adsuu44)`): ghostify the first edge of every
path (the "long ending edge"), factor `ξ(head) ≤ 𝖳_t(|a_i - b_i| ∧ ℓ)`, then `anpDetGh_holds` with
`ψ r = 𝖳_t(r ∧ ℓ)` for the ghostified graph (`n_ngh = 0`). -/
theorem lwMomExpFar_head : ∀ d : ℕ, AnpFarHead d := by
  intro d p q Γ hNG hN hO
  obtain ⟨Γ', hN', hG', hnoG, hord, hep⟩ := lwMomExpFar_ghost_all Γ hNG hN
  obtain ⟨C, c, hC, hc, hc1, H⟩ := anpDetGh_holds d p q Γ' hG' hN'
  refine ⟨C, hC, ?_⟩
  intro L _ W g t θ ℓ hW ht hθ hℓ ξ hξ hξT hrow a b S hS
  set ψ : ℝ → ℝ := fun r => sfT d L W g t (min r ℓ) with hψ
  have hmin : ∀ r : ℝ, 0 ≤ r → 0 ≤ min r ℓ := fun r hr => le_min hr hℓ
  have hanti : AntitoneOn ψ (Set.Ici 0) := fun r₁ hr₁ r₂ _ h =>
    sfT_antitone (hmin r₁ hr₁) (min_le_min_right ℓ h)
  have hpos : ∀ r : ℝ, 0 ≤ r → 0 < ψ r := fun r hr => lwMomExpFar_sfT_pos hW ht (hmin r hr)
  have hψ0 : ψ 0 = sfT d L W g t 0 := by simp only [hψ, min_eq_left hℓ]
  have hmain := H L ψ θ hanti hpos hθ ξ hξ hξT hrow a b
  have hprod : (∏ i, if Γ'.noGhostPath i = true then
      ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) = 1 :=
    Finset.prod_eq_one fun i _ => by simp [hnoG i]
  rw [hprod, mul_one, hord, hψ0] at hmain
  set B : Fin p → ℝ := fun i => sfT d L W g t (min ((zdistInf d L (a i - b i) : ℕ) : ℝ) ℓ) with hB
  have hB0 : ∀ i, 0 ≤ B i := fun i => sfT_nonneg _
  have hpt : ∀ lab ∈ S, anpKey2_ep Γ ξ (Sum.elim (Sum.elim a b) lab) ≤
      (∏ i, B i) * anpKey2_ep Γ' ξ (Sum.elim (Sum.elim a b) lab) := by
    intro lab hlab
    rw [hep ξ]
    refine mul_le_mul_of_nonneg_right ?_ (anpKey2_ep_nonneg Γ' ξ (fun α β => (hξ α β).1) _)
    refine Finset.prod_le_prod₀ (fun i _ => (hξ _ _).1) fun i _ => ?_
    obtain ⟨st, rest, hrest⟩ := List.exists_cons_of_ne_nil (lwMomExpFar_path_ne_nil hN i)
    have hst : (Γ.path i).head? = some st := by rw [hrest]; rfl
    rw [lwMomExpFar_headE_eq hst]
    simp only
    rw [lwMomExpFar_head_factor hN hst ξ (fun u v => (hξ u v).2)]
    simp only [Sum.elim_inl]
    rcases (lwMomExpFar_head_vertex hN hO hst).2 with hb | ⟨α, hα⟩
    · rw [hb]
      simp only [Sum.elim_inl]
      exact hξT (a i) (b i)
    · rw [hα]
      simp only [Sum.elim_inr]
      have hfar := hS lab hlab i st α hst hα
      have h1 : ξ (a i) (lab α) ≤ sfT d L W g t ℓ := by
        have := hξT (a i) (lab α)
        rwa [min_eq_right hfar.le] at this
      refine h1.trans ?_
      exact sfT_antitone (hmin _ ((Nat.cast_nonneg _))) (min_le_right _ _)
  have hsum : Γ.valOn ξ a b S ≤ (∏ i, B i) * Γ'.val ξ a b := by
    calc Γ.valOn ξ a b S = ∑ lab ∈ S, anpKey2_ep Γ ξ (Sum.elim (Sum.elim a b) lab) := rfl
      _ ≤ ∑ lab ∈ S, (∏ i, B i) * anpKey2_ep Γ' ξ (Sum.elim (Sum.elim a b) lab) :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ lab, (∏ i, B i) * anpKey2_ep Γ' ξ (Sum.elim (Sum.elim a b) lab) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun lab _ _ =>
            mul_nonneg (Finset.prod_nonneg fun i _ => hB0 i)
              (anpKey2_ep_nonneg Γ' ξ (fun α β => (hξ α β).1) _)
      _ = (∏ i, B i) * Γ'.val ξ a b := by rw [← Finset.mul_sum]; rfl
  calc Γ.valOn ξ a b S ≤ (∏ i, B i) * Γ'.val ξ a b := hsum
    _ ≤ (∏ i, B i) * (C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ))) :=
        mul_le_mul_of_nonneg_left hmain (Finset.prod_nonneg fun i _ => hB0 i)
    _ = _ := by ring

end Far

/-! ## 5. `lwMomExpFar_and` -/

/-- **The far bound, "and" domain**: `piFinset (fun _ => 𝐃_{>ℓ})` satisfies `lwMomExpFar_HeadFar` (the first conjunct of
`lwMomExpFar_farDAnd` at every `i`), so `lwMomExpFar_head` applies. -/
theorem lwMomExpFar_and : ∀ d : ℕ, AnpFarAnd d := by
  intro d p q Γ hNG hN hO
  obtain ⟨C, hC, H⟩ := lwMomExpFar_head d p q Γ hNG hN hO
  refine ⟨C, hC, ?_⟩
  intro L _ W g t θ ℓ hW ht hθ hℓ ξ hξ hξT hrow a b
  refine H L W g t θ ℓ hW ht hθ hℓ ξ hξ hξT hrow a b _ ?_
  intro lab hlab i st α _ _
  have hα : lab α ∈ lwMomExpFar_farDAnd d L a b ℓ := Fintype.mem_piFinset.1 hlab α
  exact ((Finset.mem_filter.1 hα).2 i).1

/-! ## 6. The nested graph of an auxiliary graph has `ownExt` -/

section AuxOwn

/-- The vertex of a molecule on the walk `i` is `a_i`, `b_i` or internal. -/
theorem lwMomExpFar_nodeV_cases {Q : PGraph (Fin 2)} {p : ℕ} (Dt : auxGraph_Data Q p) (i : Fin p)
    (c : Q.g.Mol) :
    auxGraph_nodeV Dt i c = Sum.inl (Sum.inl i) ∨ auxGraph_nodeV Dt i c = Sum.inl (Sum.inr i) ∨
      ∃ α : Fin Q.g.nM, auxGraph_nodeV Dt i c = Sum.inr α := by
  unfold auxGraph_nodeV
  split_ifs with h1 h2 h3
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- Every step of the path `i` of `auxGraph_ngraph Dt` ends at `a_i`, `b_i` or an internal vertex
(`auxGraph_ngraph`). -/
theorem lwMomExpFar_auxGraph_ownExt {Q : PGraph (Fin 2)} {p : ℕ} (Dt : auxGraph_Data Q p) :
    lwMomExpFar_ownExt (auxGraph_ngraph Dt) := by
  intro i st hst
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hst
  exact lwMomExpFar_nodeV_cases Dt i _

end AuxOwn

end RBM.Graph

end
