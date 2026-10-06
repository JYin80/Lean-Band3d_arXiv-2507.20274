/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey6
import RBM3D.Graph.AuxGraph

/-!
# LW-13c: the far part of `lem:LW_moment_exp`, deterministic, "and" domain (T2289)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): the split of `f` into
`f^{≤ℓ} + f^{>ℓ}` `:1607-1611`, `lem:LW_moment_exp_far` `:1620-1626`, its proof `:1634-1643`
(`𝐃_{>ℓ}` `:1636`, `(adsuu33)` `:1637`, "long ending edge" `:1640`, `(adsuu44)` `:1642`).

Corrected statement (supervisor 1102 §2.2, DECISIONS §95): the far domain is
`𝐃^∧_{>ℓ} = {c : |a_i - c|_∞ > ℓ and |b_i - c|_∞ > ℓ for all i}` ("and", not "or"), and the factor of path `i` is
`𝖳_t(|a_i - b_i|_∞ ∧ ℓ)` (a path with no internal vertex is the edge `a_i b_i`), not `𝖳_t(ℓ)`.

* Section 1: the vocabulary `lwMomExpFar_farDAnd`, `lwMomExpFar_ownExt`, `lwMomExpFar_HeadFar` and the pins
  `AnpFarHeadAt`, `AnpFarHead`, `AnpFarAndAt`, `AnpFarAnd`, `LWAuxNestedOwn`.
* Section 2: the head of a path of a nested graph with `ownExt`.
* Section 3: ghostify the head of every path (`NGraph.ghostify`, iterated).
* Section 4: `lwMomExpFar_head`: the far bound, from `anpDetGh_holds` with `ψ r = 𝖳_t(r ∧ ℓ)`.
* Section 5: `lwMomExpFar_and`.
* Section 6: `lwMomExpFar_auxOwn`: the `ownExt` form of `lwAuxNested_holds`.
* Section 7: compiled nonempty instances at `d = 3`.

No port: RBM1D and RBM2D have no light-weight layer.
-/

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss

/-! ## 1. Vocabulary and pins -/

/-- `𝐃^∧_{>ℓ}` (supervisor 1102 §2.2, option (c); replaces the "or" of `7_8:1636`): `|a_i - c|_∞ > ℓ` **and**
`|b_i - c|_∞ > ℓ` for every `i`. -/
def lwMomExpFar_farDAnd (d L : ℕ) [NeZero L] {p : ℕ} (a b : Fin p → Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c => ∀ i : Fin p,
    ℓ < ((zdistInf d L (a i - c) : ℕ) : ℝ) ∧ ℓ < ((zdistInf d L (b i - c) : ℕ) : ℝ)

/-- The path `𝔓_i` meets no external vertex other than its own `a_i`, `b_i` (the outputs of
`lwAuxNested_holds` have it: `auxGraph_nodeV Dt i` takes only the values `a_i`, `b_i`, internal). -/
def lwMomExpFar_ownExt {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∀ i : Fin p, ∀ st ∈ Γ.path i,
    st.2 = Sum.inl (Sum.inl i) ∨ st.2 = Sum.inl (Sum.inr i) ∨ ∃ α : Fin q, st.2 = Sum.inr α

instance lwMomExpFar_ownExt_dec {p q : ℕ} (Γ : NGraph p q) : Decidable (lwMomExpFar_ownExt Γ) := by
  unfold lwMomExpFar_ownExt; infer_instance

/-- The labellings `S` put the internal vertex reached by the first step of each path at `L^∞` distance `> ℓ`
from that path's `a_i`. -/
def lwMomExpFar_HeadFar (d L : ℕ) [NeZero L] {p q : ℕ} (Γ : NGraph p q) (a : Fin p → Zd d L) (ℓ : ℝ)
    (S : Finset (Fin q → Zd d L)) : Prop :=
  ∀ lab ∈ S, ∀ (i : Fin p) (st : Fin Γ.es.length × NV p q) (α : Fin q),
    (Γ.path i).head? = some st → st.2 = Sum.inr α → ℓ < ((zdistInf d L (a i - lab α) : ℕ) : ℝ)

/-- **Far core** (`(adsuu33)`–`(adsuu44)` deterministic, `7_8:1637-1642`, corrected): truncated edges
`ξ ≤ 𝖳_t(|α-β|_∞ ∧ ℓ)`, row sums `≤ θ`; for every set `S` of internal labellings with `HeadFar`,
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

/-- **Far pin, "and" domain** (supervisor 1102 O4): every internal label in `𝐃^∧_{>ℓ}`. -/
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

/-- **Supply for LW-13b**: the merged `LWAuxNested` (`AuxGraph.lean:1597-1604`) verbatim with
`ownExt Γa` added. -/
def LWAuxNestedOwn : Prop :=
  ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
    Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
    ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧
      Γa.ordN = LGraph.auxOrd Q.g ∧
      ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
        Γa.val ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1)) = LGraph.auxVal Q.g ξ be

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
`Π_{i ∈ T} ξ(head edge i)` split off (`7_8:1143-1148`, `(eq:noA2)`, `anpKey2_ep_ghostify`). -/
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

/-- **The far bound, head form** (`(adsuu33)`-`(adsuu44)`, `7_8:1637-1642`, corrected): ghostify the first edge of every
path (the "long ending edge"), factor `ξ(head) ≤ 𝖳_t(|a_i - b_i| ∧ ℓ)`, then the merged `anpDetGh_holds` with
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

/-- **The far pin, "and" domain**: `piFinset (fun _ => 𝐃^∧_{>ℓ})` satisfies `HeadFar` (the first conjunct of `farDAnd`
at every `i`), so `lwMomExpFar_head` applies. -/
theorem lwMomExpFar_and : ∀ d : ℕ, AnpFarAnd d := by
  intro d p q Γ hNG hN hO
  obtain ⟨C, hC, H⟩ := lwMomExpFar_head d p q Γ hNG hN hO
  refine ⟨C, hC, ?_⟩
  intro L _ W g t θ ℓ hW ht hθ hℓ ξ hξ hξT hrow a b
  refine H L W g t θ ℓ hW ht hθ hℓ ξ hξ hξT hrow a b _ ?_
  intro lab hlab i st α _ _
  have hα : lab α ∈ lwMomExpFar_farDAnd d L a b ℓ := Fintype.mem_piFinset.1 hlab α
  exact ((Finset.mem_filter.1 hα).2 i).1

/-! ## 6. `lwMomExpFar_auxOwn`: the `ownExt` form of `lwAuxNested_holds` -/

section AuxOwn

/-- The vertex of a molecule on the walk `i` is `a_i`, `b_i` or internal (`AuxGraph.lean:1172-1175`). -/
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
(`auxGraph_ngraph`, `AuxGraph.lean:1219-1222`). -/
theorem lwMomExpFar_auxGraph_ownExt {Q : PGraph (Fin 2)} {p : ℕ} (Dt : auxGraph_Data Q p) :
    lwMomExpFar_ownExt (auxGraph_ngraph Dt) := by
  intro i st hst
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hst
  exact lwMomExpFar_nodeV_cases Dt i _

/-- **The nested form of `Γ^aux` with `ownExt`** (the proof of `lwAuxNested_holds`, `AuxGraph.lean:1606-1640`, with the
same witness `auxGraph_ngraph Dt`, plus `lwMomExpFar_auxGraph_ownExt`): the input of `lwMomExpFar_and`. -/
theorem lwMomExpFar_auxOwn : LWAuxNestedOwn := by
  classical
  rintro p Q hp ⟨W, h3, h4, h5⟩ hxy
  have : Fintype (LGraph.AuxIMol Q.g) := Fintype.ofFinite _
  let e : Fin Q.g.nM ≃ LGraph.AuxIMol Q.g := (Fintype.equivFinOfCardEq (auxGraph_card_aux Q.g)).symm
  obtain ⟨R, hR⟩ := Multiset.le_iff_exists_add.1 h3.2
  let Dt : auxGraph_Data Q p := ⟨hp, e, W, R.toList.map fun z => Quot.out z⟩
  have hout : ∀ z : Sym2 Q.g.Mol, s((Quot.out z).1, (Quot.out z).2) = z := fun z => Quot.out_eq z
  have hcover : (∑ i, localReg_stepEdges (Dt.W i)) +
      (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = Q.g.localReg_molEdgeMS := by
    have : (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = R := by
      change (↑((R.toList.map fun z => Quot.out z).map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = R
      rw [List.map_map]
      have h1 : ((fun st : Q.g.Mol × Q.g.Mol => s(st.1, st.2)) ∘ fun z : Sym2 Q.g.Mol => Quot.out z) = id := by
        funext z; exact hout z
      rw [h1, List.map_id, Multiset.coe_toList]
    rw [this]
    exact hR.symm
  have hnd : ∀ i, ∀ st ∈ Dt.W i, st.1 ≠ st.2 := by
    intro i st hst
    have h1 : s(st.1, st.2) ∈ localReg_stepEdges (W i) := localReg_mem_stepEdges.2 ⟨st, hst, rfl⟩
    have h2 : s(st.1, st.2) ∈ ∑ j, localReg_stepEdges (W j) := Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, h1⟩
    have h3' := auxGraph_molEdgeMS_nd Q.g (Multiset.mem_of_le h3.2 h2)
    rwa [Sym2.mk_isDiag_iff] at h3'
  have hndr : ∀ st ∈ Dt.rest, st.1 ≠ st.2 := by
    intro st hst
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hst
    have hzR : z ∈ R := Multiset.mem_toList.1 hz
    have hz' : z ∈ Q.g.localReg_molEdgeMS := by rw [hR]; exact Multiset.mem_add.2 (Or.inr hzR)
    have := auxGraph_molEdgeMS_nd Q.g hz'
    rw [← hout z] at this
    rwa [Sym2.mk_isDiag_iff] at this
  exact ⟨auxGraph_ngraph Dt, auxGraph_noGhost Dt, auxGraph_isNested hxy Dt h3.1 hnd hndr h4 h5,
    lwMomExpFar_auxGraph_ownExt Dt, auxGraph_ordN Dt hcover,
    fun ξ hsymm be => auxGraph_val_eq hxy Dt hcover ξ hsymm be⟩

end AuxOwn

/-! ## 7. Compiled nonempty instances at `d = 3` -/

section Instances

/-- Instance (1): `figAux` (`p = q = 2`, `ord - p = 0`, `a_0 = a_1`, `b_0 = b_1` allowed): the "and" far pin. -/
theorem lwMomExpFar_inst_figAux : AnpFarAndAt 3 figAux :=
  lwMomExpFar_and 3 2 2 figAux figAux_nested.2 figAux_nested.1 (by decide +kernel)

/-- Instance (2): the one-edge graph `a_0 — b_0` (`p = 1`, `q = 0`; the counterexample of the old pin
`𝖳_t(0)/𝖳_t(ℓ) → ∞` at `a_0 = b_0` is the equality `ξ(a, a) ≤ 𝖳_t(0 ∧ ℓ)` here). -/
theorem lwMomExpFar_inst_oneEdge : AnpFarAndAt 3 anpKey_oneEdge :=
  lwMomExpFar_and 3 1 0 anpKey_oneEdge (by unfold NGraph.NoGhost; decide +kernel) anpKey_oneEdge_nested
    (by unfold lwMomExpFar_ownExt; decide +kernel)

/-- Instance (3): the head form at `figAux`. -/
theorem lwMomExpFar_inst_head : AnpFarHeadAt 3 figAux :=
  lwMomExpFar_head 3 2 2 figAux figAux_nested.2 figAux_nested.1 (by decide +kernel)

/-- Instance (4): the output of `lwMomExpFar_auxOwn` at `localReg2_inst_Q.pack` (`p = 2`, `q = 1`) satisfies the far pin. -/
theorem lwMomExpFar_inst_aux :
    ∃ Γa : NGraph 2 localReg2_inst_Q.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧
      AnpFarAndAt 3 Γa := by
  obtain ⟨Γa, h1, h2, h3, -⟩ := lwMomExpFar_auxOwn 2 localReg2_inst_Q.pack (by norm_num)
    localReg2_inst_Q_locReg345 auxGraph_inst_Q_hxy
  exact ⟨Γa, h1, h2, h3, lwMomExpFar_and 3 _ _ Γa h1 h2 h3⟩

/-- Instance (5): `lwMomExpFar_inst_figAux` applied at concrete data, every hypothesis discharged: `d = 3`, `L = 4`,
`W = 2`, `g = t = 1/2`, `ℓ = 1`, `ξ = 𝖳_t(|α - β|_∞ ∧ ℓ)` (the extremal edge), `θ` the total mass of `ξ²` (so the
row-sum premise holds), `a_0 = a_1 = 0`, `b_0 = b_1 = e_0`; the domain `𝐃^∧_{>ℓ}` is nonempty. -/
example : ∃ (ξ : Zd 3 4 → Zd 3 4 → ℝ) (θ : ℝ) (a b : Fin 2 → Zd 3 4),
    0 < θ ∧ (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) ∧
    (∀ α β, ξ α β ≤ sfT 3 4 2 (1 / 2) (1 / 2) (min ((zdistInf 3 4 (α - β) : ℕ) : ℝ) 1)) ∧
    (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) ∧ (lwMomExpFar_farDAnd 3 4 a b 1).Nonempty ∧
    ∃ C : ℝ, 0 < C ∧
      figAux.valOn ξ a b (Fintype.piFinset fun _ : Fin 2 => lwMomExpFar_farDAnd 3 4 a b 1) ≤
        C * θ ^ 2 * sfT 3 4 2 (1 / 2) (1 / 2) 0 ^ (figAux.ordN - ((2 : ℕ) : ℤ)) *
          ∏ i, sfT 3 4 2 (1 / 2) (1 / 2) (min ((zdistInf 3 4 (a i - b i) : ℕ) : ℝ) 1) := by
  obtain ⟨C, hC, H⟩ := lwMomExpFar_inst_figAux
  set ξ : Zd 3 4 → Zd 3 4 → ℝ :=
    fun α β => sfT 3 4 2 (1 / 2) (1 / 2) (min ((zdistInf 3 4 (α - β) : ℕ) : ℝ) 1) with hξ
  have hξpos : ∀ α β, 0 < ξ α β := fun α β =>
    lwMomExpFar_sfT_pos (by norm_num) (by norm_num) (le_min (Nat.cast_nonneg _) zero_le_one)
  have hsymm : ∀ α β, ξ α β = ξ β α := fun α β => by
    simp only [hξ]; rw [anpKey_zdistInf_sub_comm]
  set θ : ℝ := ∑ α, ∑ β, ξ α β ^ 2 with hθ
  have hrow : ∀ α, ∑ β, ξ α β ^ 2 ≤ θ := fun α =>
    Finset.single_le_sum (f := fun α => ∑ β, ξ α β ^ 2)
      (fun α _ => Finset.sum_nonneg fun β _ => sq_nonneg _) (Finset.mem_univ α)
  have hθpos : 0 < θ := lt_of_lt_of_le
    (Finset.sum_pos (fun β _ => pow_pos (hξpos 0 β) 2) ⟨0, Finset.mem_univ _⟩) (hrow 0)
  have hne : (lwMomExpFar_farDAnd 3 4 (fun _ : Fin 2 => (0 : Zd 3 4)) (fun _ => Pi.single 0 1) 1).Nonempty := by
    refine ⟨Pi.single 1 2, ?_⟩
    simp only [lwMomExpFar_farDAnd, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    exact ⟨Nat.one_lt_cast.2 (by decide +kernel), Nat.one_lt_cast.2 (by decide +kernel)⟩
  exact ⟨ξ, θ, fun _ => 0, fun _ => Pi.single 0 1, hθpos, fun α β => ⟨(hξpos α β).le, hsymm α β⟩,
    fun α β => le_rfl, hrow, hne, C, hC,
    H 4 2 (1 / 2) (1 / 2) θ 1 (by norm_num) (by norm_num) hθpos (by norm_num) ξ
      (fun α β => ⟨(hξpos α β).le, hsymm α β⟩) (fun α β => le_rfl) hrow _ _⟩

end Instances

end RBM.Graph

end
