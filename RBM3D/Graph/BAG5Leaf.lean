/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExpandId

/-!
# BA-L L4e-C (T2433): the GG-with-context Lemma and the leaf pins at BA (generic half)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:66-110` (`(eq;I42inG)` at 68,
`(eq:sizeGammamu_E)` at 92, `(eq:GGraisesord)` at 99, the cases at 102-108) and `:393-405`
(`GGGamma`).  Design `docs/reports/T2398-design.md` §3; probe
`t/T2398:RBM3D/Probe/T2398Pins.lean:158-166` (the pins `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand`,
copied verbatim).  This is the generic half of the row (Amend 1 of T2433, DECISIONS §251, H234,
H235): no theorem about `baG5Graph` is proved, and no statement that a tree of the procedure ends
in leaves, for any root list.

## Contents (namespace `RBM.Graph`; private prefix `BAG5Leaf_`)

1. **The pins**: `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand` (verbatim from the probe), `BAG5Attached`
   (twin of `LWAttached`, `LWExpTerm3.lean:66`, over `BAGraph.mol`), `BAG5LeafProps` (twin of
   `LWG5LeafProps`, `LWExpSound.lean:43`, without the joined alternative).  Predicates only;
   none is claimed of a list.
2. **`BACtx`** (H1-H3 of the design §3.3, paper delta T2398b) on a `GG` candidate `BARCand`, and
   the two forms of the Lemma as `Prop`s (`BAG5CtxLemma`, `BAG5CtxKids`).
3. **The Lemma** (`(eq:GGraisesord)` with context, both charges): `baG5CtxLemma_holds` (every term
   of `BAExpandId_ggL2/4 c.σ` has `ordG ≥ ord P + 1` under `BACtx c`) and its form at the
   children, `baG5CtxKids_holds` (`∀ r ∈ c.kids, ord P + 1 ≤ ord r.2`).
4. **The selector** `BAselStar`: a leaf stops, otherwise a blue candidate with `BACtx` and
   nothing else (`baselStar_spec`, `baselStar_eq_none_iff`).
5. Compiled instances (`BAG5LeafInst`): the Lemma at the merged blue and red candidates of
   `Graph/BAExpandId.lean`, the all-`M` leaf of the probe, the selector at a non-leaf.

## The proof of the Lemma

Up to `A1`, `A2`, `A3`, a term `T` of `gg2 ++ gg4` is an extension `ext k Γ rest s w md` of the
graph `Γ` with `p`, `q` removed; its unsplit counters are those of `Γ` plus `(1, k/2, k/2)`, so
`ord T° = ord Γ + 1` (`gg_counters`).  A member of `T.splitG` with `j` `M`-splits has
`ord = ord Γ + 1 - j + 2 κ'`, `κ'` the internal atoms lost (`BAG5Leaf_core`); the `+1` needs
`κ' ≥ ⌈j/2⌉` (`BAG5Leaf_kappa`).  `κ'` is counted from atoms: an `M`-split at the singleton atom
`{β}` merges it (`BAG5Leaf_nA_lt`), and an `M`-edge from the internal atom of `α` to a vertex
outside it merges them.  For `A4`, `AD` the atom of `α` is that of `x` (H1: internal; H2: not that
of `y`; H1: no solid edge but `p.1`, `q.1` meets it, so the ends of the derivative edge lie
outside it); for `B1`, `BD` it is the pendant atom `{bpv 1, bpv 2}` (no hypothesis).  `A1` has
`ord = ord Γ + 2 κ` with `κ = 1` by H2, H3 (`gg_raw`); `A2`, `A3` have `ord = ord Γ + 1`.  The red
charge is the complex conjugate (`BAExpandId_flip`): the splits, the atoms and the counters are
conjugation invariant.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private BAExpandWOrd_ext BAExpandWOrd_ext_atomAdj BAExpandWOrd_rho BAExpandWOrd_rho_emb BAExpandWOrd_emb_ne_β
  BAExpandWOrd_isRight_rho BAExpandWOrd_ext_counters BAExpandWOrd_nA_le BAExpandWOrd_self_mem_atom
  BAExpandWOrd_atom_eq_of_mem BAExpandWOrd_atom_subset from RBM3D.Graph.BAExpandWOrd
open private BAWeightOp_ext4 BAWeightOp_ext4_atomAdj BAWeightOp_ext4_counters BAWeightOp_emb_ne BAWeightOp_ext_normal
  BAWeightOp_splitG_of_circ from RBM3D.Graph.BAWeightOp
open private BAGGOp_A4_eq BAGGOp_A5_eq BAGGOp_AD_eq BAGGOp_B1_eq BAGGOp_B2_eq BAGGOp_BD_eq BAGGOp_ordG_of_split
  BAGGOp_tail2_cnt BAGGOp_tail4_cnt from RBM3D.Graph.BAGGOp
open private BAVocab_split_props from RBM3D.Graph.BAVocab
open private BAExpandId_flipP_mem from RBM3D.Graph.BAExpandId

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.BA

/-! ## 1. The pins (probe `t/T2398:RBM3D/Probe/T2398Pins.lean:158-166`, bodies verbatim) -/

/-- **The corrected target of `(eq:sizeGammamu_E)` at BA** (`B:92`, paper delta T2398a): `ord ≥ 5` if `x`, `y` lie in different
atoms, `ord ≥ 3` if they lie in one.  (The pointwise target `4·1[x = y] + 5·1[x ≠ y]` is false at BA: the all-`M` graph has `ord 4`
and `x ~ y`.) -/
def BAG5Tgt (P : BAPGraph (Fin 2)) : Prop :=
  5 ≤ P.scalingOrder + (if P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1)) then 2 else 0)

/-- **The leaf properties**: the corrected target, `n_M ≤ 1`, `n_W ≥ 2`. -/
def BAG5Leaf (P : BAPGraph (Fin 2)) : Prop := BAG5Tgt P ∧ P.g.nM ≤ 1 ∧ 2 ≤ P.g.nW

/-- **Attachment** (twin of `LWAttached`, `LWExpTerm3.lean:66`, over `BAGraph.mol`): every internal molecule is joined to other
molecules by at least two solid edges (`B:428`, `(eq:Gbyxi2_BA)`). -/
def BAG5Attached (P : BAPGraph (Fin 2)) : Prop :=
  ∀ v : P.I', (∀ w ∈ P.g.mol (Sum.inr v), w.isRight = true) →
    2 ≤ (P.g.solid.filter fun e => decide (P.g.mol e.src ≠ P.g.mol e.dst ∧
      (P.g.mol e.src = P.g.mol (Sum.inr v) ∨ P.g.mol e.dst = P.g.mol (Sum.inr v)))).length

/-- **The leaf properties of a list of terms** (twin of `LWG5LeafProps`, `LWExpSound.lean:43`, same order of the conjuncts: `Normal`,
`n_M ≤ 1`, `2 ≤ n_W`, attachment, target; the joined alternative of the band is dropped).  A predicate; no list is claimed to satisfy it. -/
def BAG5LeafProps (Ls : Bool → Bool → List (BAPGraph (Fin 2))) : Prop :=
  ∀ k s, ∀ q ∈ Ls k s, q.g.Normal ∧ q.g.nM ≤ 1 ∧ 2 ≤ q.g.nW ∧ BAG5Attached q ∧ BAG5Tgt q

/-! ## 2. `BACtx` (H1-H3) and the two forms of the Lemma -/

/-- **H0-H3 on a candidate** `c = (σ, v, p = Ǧ_{vy}, q = Ǧ_{y'v})` of `P` (`y = p.1.dst`, `y' = q.1.src`): `P.g` normal; (H1) `atom v`
is internal and exactly two solid edges (`p.1`, `q.1`) meet it; (H2) `atom v`, `atom y'`, `atom y` are pairwise distinct; (H3) `atom y'`
or `atom y` is internal.  Then `κ = BAGGOp_kappa P.g y' y = 1` (`Graph/BAGGOp.lean:1533`). -/
def BACtx {P : BAPGraph (Fin 2)} (c : BARCand P) : Prop :=
  P.g.Normal ∧ (∀ w ∈ P.g.atom c.v, w.isRight = true) ∧
    (P.g.solid.filter fun e => decide (e.src ∈ P.g.atom c.v ∨ e.dst ∈ P.g.atom c.v)).length = 2 ∧
    P.g.atom c.v ≠ P.g.atom c.p.1.dst ∧ P.g.atom c.v ≠ P.g.atom c.q.1.src ∧ P.g.atom c.q.1.src ≠ P.g.atom c.p.1.dst ∧
    ((∀ w ∈ P.g.atom c.q.1.src, w.isRight = true) ∨ (∀ w ∈ P.g.atom c.p.1.dst, w.isRight = true))

/-- **The Lemma, graph level, both charges** (`(eq:GGraisesord)`, `B:99`, with the hypotheses H1-H3; paper delta T2398b): every term of
the `gg2` and `gg4` lists of the charge of `c` (`BAExpandId_ggL2/4`: the merged blue lists, the conjugate lists for `σ = false`) has
`ord ≥ ord P + 1` (`scalingOrderG` is the minimum over the `G = Ǧ + M` partition). -/
def BAG5CtxLemma : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (c : BARCand P), BACtx c →
    (∀ T ∈ BAExpandId_ggL2 c.σ P.g c.p c.q, ((P.scalingOrder + 1 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧
    (∀ T ∈ BAExpandId_ggL4 c.σ P.g c.p c.q, ((P.scalingOrder + 1 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG)

/-- **The Lemma at the children** (`BARCand.kids`, `Graph/BAExpandId.lean:364`): every packed child of a candidate with `BACtx` has
`ord ≥ ord P + 1`. -/
def BAG5CtxKids : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (c : BARCand P), BACtx c → ∀ r ∈ c.kids, P.scalingOrder + 1 ≤ r.2.scalingOrder

/-! ## 3. Counting internal atoms under added `M`-dotted edges -/

section AtomCount

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `Δ` with its solid edges replaced by `r1` and the `M`-dotted edges `ms` added: the shape of a term of `Δ.splitG`. -/
private def BAG5Leaf_withM (Δ : BAGraph E I) (r1 : List (SEdge (E ⊕ I))) (ms : List (BAMEdge (E ⊕ I))) : BAGraph E I :=
  BAGraph.mk (LGraph.mk r1 Δ.waved Δ.dotted Δ.coeff) Δ.psi (ms ++ Δ.mdot)

private theorem BAG5Leaf_withM_atomAdj (Δ : BAGraph E I) (r1 : List (SEdge (E ⊕ I))) (ms : List (BAMEdge (E ⊕ I)))
    (u v : E ⊕ I) :
    (BAG5Leaf_withM Δ r1 ms).atomAdj u v = true ↔
      Δ.atomAdj u v = true ∨ ∃ m ∈ ms, (m.x = u ∧ m.y = v) ∨ (m.x = v ∧ m.y = u) := by
  simp only [BAGraph.atomAdj, BAG5Leaf_withM, List.any_append, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ((h | h) | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro (((h | h) | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- **Merging an internal atom with a vertex outside it loses one internal atom** (generalizes the private `BAExpandWOrd_nA_lt`,
where the atom is a singleton): if the atom of `b` in `Γ₁` is internal, `u` is not in it, and `Γ₂ ⊇ Γ₁` joins `b` and `u`, then
`Γ₂` has fewer internal atoms. -/
private theorem BAG5Leaf_nA_lt (Γ₁ Γ₂ : BAGraph E I)
    (h : ∀ u v, Γ₁.atomAdj u v = true → Γ₂.atomAdj u v = true) (b u : E ⊕ I)
    (hb : ∀ w ∈ Γ₁.atom b, w.isRight = true) (hu : u ∉ Γ₁.atom b) (hbu : Γ₂.atomAdj b u = true) :
    Γ₂.nA + 1 ≤ Γ₁.nA := by
  classical
  unfold BAGraph.nA
  set IA₁ := (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₁.atom v, w.isRight = true)).image Γ₁.atom with hIA₁
  have hbmem : Γ₁.atom b ∈ IA₁ := by
    rw [hIA₁, Finset.mem_image]
    exact ⟨b, by simpa using hb, rfl⟩
  set F : Finset (E ⊕ I) → Finset (E ⊕ I) := fun A =>
    if hA : A.Nonempty then Γ₂.atom hA.choose else ∅ with hF
  have hsub : (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₂.atom v, w.isRight = true)).image Γ₂.atom ⊆
      (IA₁.erase (Γ₁.atom b)).image F := by
    intro T hT
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    set a : E ⊕ I := if v ∈ Γ₁.atom b then u else v with ha
    have haT : a ∈ Γ₂.atom v := by
      by_cases hvb : v ∈ Γ₁.atom b
      · simp only [ha, hvb, ↓reduceIte]
        have h1 : v ∈ Γ₂.atom b := BAExpandWOrd_atom_subset Γ₁ Γ₂ h b hvb
        have h2 : u ∈ Γ₂.atom b := by
          rw [BAGraph.mem_atom_iff]
          exact Relation.ReflTransGen.single hbu
        rw [BAExpandWOrd_atom_eq_of_mem Γ₂ h1]
        exact h2
      · simp only [ha, hvb, ↓reduceIte]
        exact BAExpandWOrd_self_mem_atom Γ₂ v
    have hab : a ∉ Γ₁.atom b := by
      by_cases hvb : v ∈ Γ₁.atom b
      · simp only [ha, hvb, ↓reduceIte]; exact hu
      · simp [ha, hvb]
    have hsubT : Γ₁.atom a ⊆ Γ₂.atom v := by
      intro w hw
      have := BAExpandWOrd_atom_subset Γ₁ Γ₂ h a hw
      rwa [BAExpandWOrd_atom_eq_of_mem Γ₂ haT] at this
    refine Finset.mem_image.2 ⟨Γ₁.atom a, Finset.mem_erase.2 ⟨?_, Finset.mem_image.2 ⟨a, ?_, rfl⟩⟩, ?_⟩
    · intro hAb
      have := BAExpandWOrd_self_mem_atom Γ₁ a
      rw [hAb] at this
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

/-- A vertex without atom edges has the singleton atom. -/
private theorem BAG5Leaf_atom_iso (Γ : BAGraph E I) (b : E ⊕ I) (hiso : ∀ w, Γ.atomAdj b w = false) :
    Γ.atom b = {b} := by
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

/-- An `M`-edge with exactly one end at `β`. -/
private def BAG5Leaf_Touch {V : Type} (β : V) (m : BAMEdge V) : Prop :=
  (m.x = β ∧ m.y ≠ β) ∨ (m.y = β ∧ m.x ≠ β)

/-- An `M`-edge from `α` to a vertex outside the atom of `α` (and different from `β`). -/
private def BAG5Leaf_Good (Δ : BAGraph E I) (α β : E ⊕ I) (m : BAMEdge (E ⊕ I)) : Prop :=
  (m.x = α ∧ m.y ∉ Δ.atom α ∧ m.y ≠ β) ∨ (m.y = α ∧ m.x ∉ Δ.atom α ∧ m.x ≠ β)

/-- **The internal atoms lost by a set of `M`-splits**: `β` has no atom edges in `Δ`, the atom of `α` is internal; if `ms` is empty, or has
at most two edges one of which touches `β` or leaves the atom of `α`, or has three edges, one touching `β` and one leaving the atom
of `α`, then `|ms| ≤ 2 (n_A Δ - n_A (Δ + ms))`. -/
private theorem BAG5Leaf_kappa (Δ : BAGraph E I) (r1 : List (SEdge (E ⊕ I))) (ms : List (BAMEdge (E ⊕ I)))
    (α β : E ⊕ I) (hαβ : α ≠ β) (hα : ∀ w ∈ Δ.atom α, w.isRight = true) (hβ : β.isRight = true)
    (hiso : ∀ w, Δ.atomAdj β w = false)
    (hms : ms.length = 0 ∨ (ms.length ≤ 2 ∧ ∃ m ∈ ms, BAG5Leaf_Touch β m ∨ BAG5Leaf_Good Δ α β m) ∨
      (ms.length ≤ 3 ∧ (∃ m ∈ ms, BAG5Leaf_Good Δ α β m) ∧ ∃ m ∈ ms, BAG5Leaf_Touch β m)) :
    ms.length + 2 * (BAG5Leaf_withM Δ r1 ms).nA ≤ 2 * Δ.nA := by
  have hadj := BAG5Leaf_withM_atomAdj Δ r1 ms
  have href : ∀ u v, Δ.atomAdj u v = true → (BAG5Leaf_withM Δ r1 ms).atomAdj u v = true :=
    fun u v h => (hadj u v).2 (Or.inl h)
  have hle : (BAG5Leaf_withM Δ r1 ms).nA ≤ Δ.nA := BAExpandWOrd_nA_le Δ _ href
  have hβ1 : Δ.atom β = {β} := BAG5Leaf_atom_iso Δ β hiso
  have ht : ∀ m ∈ ms, BAG5Leaf_Touch β m → (BAG5Leaf_withM Δ r1 ms).nA + 1 ≤ Δ.nA := by
    intro m hm h
    rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact BAG5Leaf_nA_lt Δ _ href β m.y (by rw [hβ1]; simpa using hβ) (by rw [hβ1]; simpa using hy)
        ((hadj β m.y).2 (Or.inr ⟨m, hm, Or.inl ⟨hx, rfl⟩⟩))
    · exact BAG5Leaf_nA_lt Δ _ href β m.x (by rw [hβ1]; simpa using hβ) (by rw [hβ1]; simpa using hx)
        ((hadj β m.x).2 (Or.inr ⟨m, hm, Or.inr ⟨rfl, hy⟩⟩))
  have hg : ∀ m ∈ ms, BAG5Leaf_Good Δ α β m → (BAG5Leaf_withM Δ r1 ms).nA + 1 ≤ Δ.nA := by
    intro m hm h
    rcases h with ⟨hx, hy, -⟩ | ⟨hy, hx, -⟩
    · exact BAG5Leaf_nA_lt Δ _ href α m.y hα hy ((hadj α m.y).2 (Or.inr ⟨m, hm, Or.inl ⟨hx, rfl⟩⟩))
    · exact BAG5Leaf_nA_lt Δ _ href α m.x hα hx ((hadj α m.x).2 (Or.inr ⟨m, hm, Or.inr ⟨rfl, hy⟩⟩))
  rcases hms with h0 | ⟨hl, m, hm, hmq⟩ | ⟨hl, ⟨mg, hmg, hgood⟩, ⟨mt, hmt, htouch⟩⟩
  · omega
  · have : (BAG5Leaf_withM Δ r1 ms).nA + 1 ≤ Δ.nA := by
      rcases hmq with h | h
      · exact ht m hm h
      · exact hg m hm h
    omega
  · set Δ₁ := BAG5Leaf_withM Δ Δ.solid [mg] with hΔ₁
    have hadj1 := BAG5Leaf_withM_atomAdj Δ Δ.solid [mg]
    have href1 : ∀ u v, Δ.atomAdj u v = true → Δ₁.atomAdj u v = true := fun u v h => (hadj1 u v).2 (Or.inl h)
    have s1 : Δ₁.nA + 1 ≤ Δ.nA := by
      rcases hgood with ⟨hx, hy, -⟩ | ⟨hy, hx, -⟩
      · exact BAG5Leaf_nA_lt Δ Δ₁ href1 α mg.y hα hy
          ((hadj1 α mg.y).2 (Or.inr ⟨mg, List.mem_singleton_self _, Or.inl ⟨hx, rfl⟩⟩))
      · exact BAG5Leaf_nA_lt Δ Δ₁ href1 α mg.x hα hx
          ((hadj1 α mg.x).2 (Or.inr ⟨mg, List.mem_singleton_self _, Or.inr ⟨rfl, hy⟩⟩))
    have hiso1 : ∀ w, Δ₁.atomAdj β w = false := by
      intro w
      by_contra hne
      have h' : Δ₁.atomAdj β w = true := by simpa using hne
      rcases (hadj1 β w).1 h' with h | ⟨m', hm', h⟩
      · rw [hiso w] at h
        exact absurd h (by simp)
      · rw [List.mem_singleton] at hm'
        subst hm'
        rcases hgood with ⟨hx, hy, hyb⟩ | ⟨hy, hx, hxb⟩
        · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hαβ (hx.symm.trans h1)
          · exact hyb h2
        · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hxb h1
          · exact hαβ (hy.symm.trans h2)
    have hβ2 : Δ₁.atom β = {β} := BAG5Leaf_atom_iso Δ₁ β hiso1
    have hrefs : ∀ u v, Δ₁.atomAdj u v = true → (BAG5Leaf_withM Δ r1 ms).atomAdj u v = true := by
      intro u v hh
      rcases (hadj1 u v).1 hh with h0 | ⟨m', hm', hE⟩
      · exact href u v h0
      · rw [List.mem_singleton] at hm'
        rw [hm'] at hE
        exact (hadj u v).2 (Or.inr ⟨mg, hmg, hE⟩)
    have s2 : (BAG5Leaf_withM Δ r1 ms).nA + 1 ≤ Δ₁.nA := by
      rcases htouch with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · exact BAG5Leaf_nA_lt Δ₁ _ hrefs β mt.y (by rw [hβ2]; simpa using hβ) (by rw [hβ2]; simpa using hy)
          ((hadj β mt.y).2 (Or.inr ⟨mt, hmt, Or.inl ⟨hx, rfl⟩⟩))
      · exact BAG5Leaf_nA_lt Δ₁ _ hrefs β mt.x (by rw [hβ2]; simpa using hβ) (by rw [hβ2]; simpa using hx)
          ((hadj β mt.x).2 (Or.inr ⟨mt, hmt, Or.inr ⟨rfl, hy⟩⟩))
    omega

/-- The `M`-edges that a split of the non-circled edges of `es` can produce (one `M`-edge `M_{xy}` of the charge of the edge per
non-circled edge `G_{xy}`). -/
private def BAG5Leaf_Ms {V : Type} (es : List (SEdge V)) : List (BAMEdge V) :=
  (es.filter fun e => !e.circ).map fun e => BAMEdge.mk e.σ e.src e.dst

/-- The `M`-edges of a term of `baSplitSolid es` form a sublist of `BAG5Leaf_Ms es`. -/
private theorem BAG5Leaf_split_sublist {V : Type} :
    ∀ es : List (SEdge V), ∀ r ∈ baSplitSolid es, r.2.Sublist (BAG5Leaf_Ms es)
  | [] => by
    intro r hr
    simp only [baSplitSolid, List.mem_singleton] at hr
    subst hr
    exact List.Sublist.slnil
  | e :: es => by
    intro r hr
    have ih := BAG5Leaf_split_sublist es
    simp only [baSplitSolid, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    cases hc : e.circ
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hr
      have key : BAG5Leaf_Ms (e :: es) = BAMEdge.mk e.σ e.src e.dst :: BAG5Leaf_Ms es := by
        simp [BAG5Leaf_Ms, List.filter_cons, hc]
      rw [key]
      rcases hr with rfl | rfl
      · exact (ih r' hr').cons _
      · exact (ih r' hr').cons_cons _
    · simp only [hc, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      have key : BAG5Leaf_Ms (e :: es) = BAG5Leaf_Ms es := by
        simp [BAG5Leaf_Ms, List.filter_cons, hc]
      rw [key]
      exact ih r' hr'

/-- The pattern of the `M`-splits that `BAG5Leaf_kappa` accepts, from a sublist of at most three edges. -/
private theorem BAG5Leaf_hms {V : Type} (Q Gd Tc : BAMEdge V → Prop) (L ms : List (BAMEdge V)) (hs : ms.Sublist L)
    (hL : ∀ m ∈ L, Q m) (hL3 : L.length ≤ 3) (hGT : L.length = 3 → (∃ m ∈ L, Gd m) ∧ ∃ m ∈ L, Tc m) :
    ms.length = 0 ∨ (ms.length ≤ 2 ∧ ∃ m ∈ ms, Q m) ∨ (ms.length ≤ 3 ∧ (∃ m ∈ ms, Gd m) ∧ ∃ m ∈ ms, Tc m) := by
  have hle := hs.length_le
  by_cases h0 : ms.length = 0
  · exact Or.inl h0
  · right
    by_cases h3 : ms.length = 3
    · right
      have hL' : L.length = 3 := by omega
      have heq : ms = L := hs.eq_of_length (by omega)
      subst heq
      exact ⟨by omega, hGT hL'⟩
    · left
      refine ⟨by omega, ?_⟩
      obtain ⟨m, hm⟩ := List.exists_mem_of_length_pos (by omega : 0 < ms.length)
      exact ⟨m, hm, hL m (hs.subset hm)⟩

/-- Every term of the split of `T` is normal and has `ord ≥ k`. -/
private def BAG5Leaf_SplitGe {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (k : ℤ)
    (T : BAGraph E I) : Prop :=
  ∀ Δs ∈ T.splitG, Δs.Normal ∧ k ≤ ord Δs.counters

/-- The order of a split term from the counters of the unsplit graph and the internal atoms lost by the `M`-splits. -/
private theorem BAG5Leaf_core {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (k : ℤ)
    (Δ : BAGraph E' I') (r1 : List (SEdge (E' ⊕ I'))) (ms : List (BAMEdge (E' ⊕ I')))
    (hord : k ≤ ord Δ.counters) (hlen : r1.length + ms.length = Δ.nS)
    (hκ : ms.length + 2 * (BAG5Leaf_withM Δ r1 ms).nA ≤ 2 * Δ.nA) :
    k ≤ ord (BAG5Leaf_withM Δ r1 ms).counters := by
  have hc : (BAG5Leaf_withM Δ r1 ms).counters =
      ⟨r1.length, Δ.nW, (BAG5Leaf_withM Δ r1 ms).nA, (BAG5Leaf_withM Δ r1 ms).nM, 0, 0⟩ := rfl
  have h1 : ord Δ.counters = (Δ.nS : ℤ) + 2 * ((Δ.nW : ℤ) - Δ.nA) := rfl
  rw [hc]
  rw [h1] at hord
  simp only [ord]
  omega

/-- The hypotheses of `BAG5Leaf_split_ge` on the possible `M`-edges `L`: all merge (touch `β` or leave the atom of `α`), at most three,
and with three both kinds occur. -/
private def BAG5Leaf_MsOK (Δ : BAGraph E I) (α β : E ⊕ I) (L : List (BAMEdge (E ⊕ I))) : Prop :=
  (∀ m ∈ L, BAG5Leaf_Touch β m ∨ BAG5Leaf_Good Δ α β m) ∧ L.length ≤ 3 ∧
    (L.length = 3 → (∃ m ∈ L, BAG5Leaf_Good Δ α β m) ∧ ∃ m ∈ L, BAG5Leaf_Touch β m)

/-- **The generic step**: `Δ` has solid edges `rest' ++ s` with `rest'` circled, normal dotted edges, `ord ≥ k`, a vertex `β` without atom
edges, an internal atom of `α`, and the possible `M`-splits `BAG5Leaf_Ms s` (at most three) are all merging; then every term of
`Δ.splitG` is normal with `ord ≥ k`. -/
private theorem BAG5Leaf_split_ge {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (k : ℤ)
    (Δ : BAGraph E' I') (rest' s : List (SEdge (E' ⊕ I'))) (hsol : Δ.solid = rest' ++ s)
    (hrest' : ∀ e ∈ rest', e.circ = true) (hdot : ∀ e ∈ Δ.dotted, e.eq = false) (hord : k ≤ ord Δ.counters)
    (α β : E' ⊕ I') (hαβ : α ≠ β) (hα : ∀ w ∈ Δ.atom α, w.isRight = true) (hβ : β.isRight = true)
    (hiso : ∀ w, Δ.atomAdj β w = false) (hMs : BAG5Leaf_MsOK Δ α β (BAG5Leaf_Ms s)) :
    BAG5Leaf_SplitGe k Δ := by
  intro Δs hΔs
  have hedges := BAGraph.splitG_edges Δ Δs hΔs
  have hcirc := BAGraph.splitG_circ Δ Δs hΔs
  refine ⟨⟨by rw [hedges.2.1]; exact hdot, hcirc⟩, ?_⟩
  simp only [BAGraph.splitG, List.mem_map] at hΔs
  obtain ⟨r, hr, rfl⟩ := hΔs
  have hlen := (BAVocab_split_props Δ.solid r hr).2
  have hsub := BAG5Leaf_split_sublist Δ.solid r hr
  have hMs' : BAG5Leaf_Ms Δ.solid = BAG5Leaf_Ms s := by
    rw [hsol]
    unfold BAG5Leaf_Ms
    rw [List.filter_append, List.filter_eq_nil_iff.2 (fun e he => by simp [hrest' e he]), List.nil_append]
  rw [hMs'] at hsub
  exact BAG5Leaf_core k Δ r.1 r.2 hord hlen
    (BAG5Leaf_kappa Δ r.1 r.2 α β hαβ hα hβ hiso
      (BAG5Leaf_hms (fun m => BAG5Leaf_Touch β m ∨ BAG5Leaf_Good Δ α β m) (BAG5Leaf_Good Δ α β) (BAG5Leaf_Touch β)
        _ r.2 hsub hMs.1 hMs.2.1 hMs.2.2))

end AtomCount

/-! ## 4. The shapes `BAExpandWOrd_ext` (`k = 2`) and `BAWeightOp_ext4` (`k = 4`) -/

section Shapes

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `k = 2` (`A4`, `A5`, `AD`): in `Δ = ext Γ rest s x`, a vertex reachable from `α = bpv 0` by atom edges is not `β = bpv 1`, and its
retraction (`α ↦ x`, old vertices to themselves) is reachable from `x` in `Γ`. -/
private theorem BAG5Leaf_ext2_rtg (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (x : E ⊕ I) {w : E ⊕ (I ⊕ Fin 2)}
    (h : Relation.ReflTransGen (fun a b => (BAExpandWOrd_ext Γ rest s x).atomAdj a b = true)
      (Sum.inr (Sum.inr 0)) w) :
    w ≠ Sum.inr (Sum.inr 1) ∧ Relation.ReflTransGen (fun a b => Γ.atomAdj a b = true) x (BAExpandWOrd_rho x w) := by
  induction h with
  | refl => exact ⟨by simp, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hrb⟩ := ih
    rcases (BAExpandWOrd_ext_atomAdj Γ rest s x _ _).1 hbc with ⟨a, a', rfl, rfl, h'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨BAExpandWOrd_emb_ne_β a', ?_⟩
      rw [BAExpandWOrd_rho_emb] at hrb ⊢
      exact hrb.tail h'
    · refine ⟨by simp, ?_⟩
      rw [BAExpandWOrd_rho_emb] at hrb
      exact hrb
    · exact ⟨BAExpandWOrd_emb_ne_β x, by rw [BAExpandWOrd_rho_emb]⟩

/-- `k = 2`: the atom of `α = bpv 0` is internal when that of `x` is, and contains no old vertex outside the atom of `x`; `β = bpv 1` has no
atom edge. -/
private theorem BAG5Leaf_ext2_facts (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) (hx : ∀ a ∈ Γ.atom x, a.isRight = true) :
    (∀ w ∈ (BAExpandWOrd_ext Γ rest s x).atom (Sum.inr (Sum.inr 0)), w.isRight = true) ∧
    (∀ c, c ∉ Γ.atom x → owxEmb 2 c ∉ (BAExpandWOrd_ext Γ rest s x).atom (Sum.inr (Sum.inr 0))) ∧
    (∀ w, (BAExpandWOrd_ext Γ rest s x).atomAdj (Sum.inr (Sum.inr 1)) w = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rw [BAGraph.mem_atom_iff] at hw
    obtain ⟨-, hr⟩ := BAG5Leaf_ext2_rtg Γ rest s x hw
    exact BAExpandWOrd_isRight_rho x w (hx _ ((BAGraph.mem_atom_iff Γ x _).2 hr))
  · intro c hc hmem
    rw [BAGraph.mem_atom_iff] at hmem
    obtain ⟨-, hr⟩ := BAG5Leaf_ext2_rtg Γ rest s x hmem
    rw [BAExpandWOrd_rho_emb] at hr
    exact hc ((BAGraph.mem_atom_iff Γ x c).2 hr)
  · intro w
    by_contra hne
    have h'' : (BAExpandWOrd_ext Γ rest s x).atomAdj (Sum.inr (Sum.inr 1)) w = true := by simpa using hne
    rcases (BAExpandWOrd_ext_atomAdj Γ rest s x _ _).1 h'' with ⟨a, b, h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact BAExpandWOrd_emb_ne_β a h1.symm
    · exact BAExpandWOrd_emb_ne_β x h1.symm
    · simp at h1

/-- `k = 4` (`B1`, `B2`, `BD`): in `Δ = ext4 Γ rest s x`, a vertex reachable from `α = bpv 2` by atom edges is `bpv 1` or `bpv 2`. -/
private theorem BAG5Leaf_ext4_rtg (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 4))))
    (x : E ⊕ I) {w : E ⊕ (I ⊕ Fin 4)}
    (h : Relation.ReflTransGen (fun a b => (BAWeightOp_ext4 Γ rest s x).atomAdj a b = true) (bpv 2) w) :
    w = bpv 1 ∨ w = bpv 2 := by
  induction h with
  | refl => exact Or.inr rfl
  | @tail b c _ hbc ih =>
    rcases (BAWeightOp_ext4_atomAdj Γ rest s x _ _).1 hbc with
      ⟨a, a', rfl, rfl, _⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases ih with h | h <;> exact absurd h (BAWeightOp_emb_ne _ _)
    · rcases ih with h | h <;> exact absurd h (BAWeightOp_emb_ne _ _)
    · rcases ih with h | h <;> simp at h
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- `k = 4`: the atom of `α = bpv 2` is internal and contains no old vertex; `β = bpv 3` has no atom edge. -/
private theorem BAG5Leaf_ext4_facts (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I) :
    (∀ w ∈ (BAWeightOp_ext4 Γ rest s x).atom (bpv 2), w.isRight = true) ∧
    (∀ c, owxEmb 4 c ∉ (BAWeightOp_ext4 Γ rest s x).atom (bpv 2)) ∧
    (∀ w, (BAWeightOp_ext4 Γ rest s x).atomAdj (bpv 3) w = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rw [BAGraph.mem_atom_iff] at hw
    rcases BAG5Leaf_ext4_rtg Γ rest s x hw with rfl | rfl <;> rfl
  · intro c hmem
    rw [BAGraph.mem_atom_iff] at hmem
    rcases BAG5Leaf_ext4_rtg Γ rest s x hmem with h | h <;> exact absurd h (BAWeightOp_emb_ne _ _)
  · intro w
    by_contra hne
    have h'' : (BAWeightOp_ext4 Γ rest s x).atomAdj (bpv 3) w = true := by simpa using hne
    rcases (BAWeightOp_ext4_atomAdj Γ rest s x _ _).1 h'' with ⟨a, b, h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact BAWeightOp_emb_ne a 3 h1.symm
    · exact BAWeightOp_emb_ne x 3 h1.symm
    · simp at h1
    · simp at h1
    · simp at h1

/-- The splits of the `k = 2` shape, from the splits of its new solid edges. -/
private theorem BAG5Leaf_ext2_ge (Γ : BAGraph E I) (hN : Γ.Normal) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) (hrest : ∀ e ∈ rest, e.circ = true)
    (hcnt : (BAExpandWOrd_ext Γ rest s x).counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩)
    (hx : ∀ a ∈ Γ.atom x, a.isRight = true)
    (hMs : BAG5Leaf_MsOK (BAExpandWOrd_ext Γ rest s x) (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) (BAG5Leaf_Ms s)) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAExpandWOrd_ext Γ rest s x) := by
  obtain ⟨hα, -, hiso⟩ := BAG5Leaf_ext2_facts Γ rest s x hx
  refine BAG5Leaf_split_ge _ _ (rest.map (SEdge.map (owxEmb 2))) s rfl ?_ ?_ ?_ (Sum.inr (Sum.inr 0))
    (Sum.inr (Sum.inr 1)) (by simp) hα rfl hiso hMs
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact hrest e0 he0
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact hN.1 e0 he0
  · rw [hcnt]
    simp only [ord, BAGraph.counters]
    omega

/-- The splits of the `k = 4` shape. -/
private theorem BAG5Leaf_ext4_ge (Γ : BAGraph E I) (hN : Γ.Normal) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I) (hrest : ∀ e ∈ rest, e.circ = true)
    (hcnt : (BAWeightOp_ext4 Γ rest s x).counters = ⟨Γ.nS + 1, Γ.nW + 2, Γ.nA + 2, Γ.nM, 0, 0⟩)
    (hMs : BAG5Leaf_MsOK (BAWeightOp_ext4 Γ rest s x) (bpv 2) (bpv 3) (BAG5Leaf_Ms s)) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAWeightOp_ext4 Γ rest s x) := by
  obtain ⟨hα, -, hiso⟩ := BAG5Leaf_ext4_facts Γ rest s x
  refine BAG5Leaf_split_ge _ _ (rest.map (SEdge.map (owxEmb 4))) s rfl ?_ ?_ ?_ (bpv 2) (bpv 3) (by simp) hα rfl hiso hMs
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact hrest e0 he0
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact hN.1 e0 he0
  · rw [hcnt]
    simp only [ord, BAGraph.counters]
    omega

/-- The solid edges of `Γ` other than `p.1`, `q.1` are circled. -/
private theorem BAG5Leaf_circ_tail (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) : ∀ e ∈ q.2, e.circ = true := fun e he =>
  hN.2 e ((lwSplit_perm Γ.solid p hp).mem_iff.2 (List.mem_cons_of_mem _
    ((lwSplit_perm p.2 q hq).mem_iff.2 (List.mem_cons_of_mem _ he))))

/-! ### The `M`-split patterns of the six terms -/

/-- One non-circled edge `G_{αy}` between two circled ones (`A4`, `B1`): the single possible `M`-edge `M_{αy}` leaves the atom of `α`. -/
private theorem BAG5Leaf_pat_one (Δ : BAGraph E I) (α β y : E ⊕ I) (c0 c2 : SEdge (E ⊕ I)) (h0 : c0.circ = true)
    (h2 : c2.circ = true) (hy : y ∉ Δ.atom α) (hyβ : y ≠ β) :
    BAG5Leaf_MsOK Δ α β (BAG5Leaf_Ms [c0, ⟨true, false, α, y⟩, c2]) := by
  have key : BAG5Leaf_Ms [c0, ⟨true, false, α, y⟩, c2] = [BAMEdge.mk true α y] := by
    simp [BAG5Leaf_Ms, List.filter_cons, h0, h2]
  rw [key]
  refine ⟨?_, by simp, by simp⟩
  intro m hm
  rw [List.mem_singleton] at hm
  subst hm
  exact Or.inr (Or.inl ⟨rfl, hy, hyβ⟩)

/-- Two non-circled edges `G_{βy}`, `G_{y'β}` after a circled one (`A5`, `B2`): both `M`-edges touch `β`. -/
private theorem BAG5Leaf_pat_two (Δ : BAGraph E I) (α β y y' : E ⊕ I) (c0 : SEdge (E ⊕ I)) (h0 : c0.circ = true)
    (hy : y ≠ β) (hy' : y' ≠ β) :
    BAG5Leaf_MsOK Δ α β (BAG5Leaf_Ms [c0, ⟨true, false, β, y⟩, ⟨true, false, y', β⟩]) := by
  have key : BAG5Leaf_Ms [c0, ⟨true, false, β, y⟩, ⟨true, false, y', β⟩] =
      [BAMEdge.mk true β y, BAMEdge.mk true y' β] := by
    simp [BAG5Leaf_Ms, List.filter_cons, h0]
  rw [key]
  refine ⟨?_, by simp, by simp⟩
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Or.inl (Or.inl ⟨rfl, hy⟩)
  · exact Or.inl (Or.inr ⟨rfl, hy'⟩)

/-- The `M`-edges of the split of a derivative term: `owxDE β α e` (two edges), `G_{βy}`, then a circled edge, for a blue edge `e`. -/
private theorem BAG5Leaf_Ms_Dt {V : Type} (a w : V) (e e3 c : SEdge V) (hσ : e.σ = true) (h3 : e3.circ = false)
    (hc : c.circ = true) :
    BAG5Leaf_Ms [(owxDE a w e).1, (owxDE a w e).2, e3, c] =
      [BAMEdge.mk true e.src a, BAMEdge.mk true w e.dst, BAMEdge.mk e3.σ e3.src e3.dst] := by
  unfold BAG5Leaf_Ms owxDE
  simp [hσ, List.filter_cons, h3, hc]

/-- As `BAG5Leaf_Ms_Dt` for a red edge `e`. -/
private theorem BAG5Leaf_Ms_Df {V : Type} (a w : V) (e e3 c : SEdge V) (hσ : e.σ = false) (h3 : e3.circ = false)
    (hc : c.circ = true) :
    BAG5Leaf_Ms [(owxDE a w e).1, (owxDE a w e).2, e3, c] =
      [BAMEdge.mk false e.src w, BAMEdge.mk false a e.dst, BAMEdge.mk e3.σ e3.src e3.dst] := by
  unfold BAG5Leaf_Ms owxDE
  simp [hσ, List.filter_cons, h3, hc]

/-- The derivative term `owxDE β α e`, `G_{βy}`, circled edge (`AD`, `BD`): `e = Ǧ_{ab}` with `a`, `b` outside the atom of `α`; the edge at
`α` leaves its atom and the others touch `β`. -/
private theorem BAG5Leaf_pat_D (Δ : BAGraph E I) (α β a b y : E ⊕ I) (e c : SEdge (E ⊕ I)) (hc : c.circ = true)
    (he1 : e.src = a) (he2 : e.dst = b) (haβ : a ≠ β) (hbβ : b ≠ β) (hyβ : y ≠ β) (ha : a ∉ Δ.atom α)
    (hb : b ∉ Δ.atom α) :
    BAG5Leaf_MsOK Δ α β (BAG5Leaf_Ms [(owxDE β α e).1, (owxDE β α e).2, ⟨true, false, β, y⟩, c]) := by
  rcases Bool.eq_false_or_eq_true e.σ with hσ | hσ
  · rw [BAG5Leaf_Ms_Dt β α e _ c hσ rfl hc, he1, he2]
    refine ⟨?_, by simp, fun _ => ⟨⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Or.inl ⟨rfl, hb, hbβ⟩⟩,
      ⟨_, List.mem_cons_self, Or.inr ⟨rfl, haβ⟩⟩⟩⟩
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact Or.inl (Or.inr ⟨rfl, haβ⟩)
    · exact Or.inr (Or.inl ⟨rfl, hb, hbβ⟩)
    · exact Or.inl (Or.inl ⟨rfl, hyβ⟩)
  · rw [BAG5Leaf_Ms_Df β α e _ c hσ rfl hc, he1, he2]
    refine ⟨?_, by simp, fun _ => ⟨⟨_, List.mem_cons_self, Or.inr ⟨rfl, ha, haβ⟩⟩,
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Or.inl ⟨rfl, hbβ⟩⟩⟩⟩
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨rfl, ha, haβ⟩)
    · exact Or.inl (Or.inl ⟨rfl, hbβ⟩)
    · exact Or.inl (Or.inl ⟨rfl, hyβ⟩)

/-! ### The six terms -/

/-- `A4` (`Σ M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'x} f`): the only possible `M`-split is `M_{αy}`, which merges the atom of `α` (that of `x`)
with that of `y`. -/
private theorem BAG5Leaf_A4 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hx : ∀ a ∈ Γ.atom p.1.src, a.isRight = true)
    (hy : p.1.dst ∉ Γ.atom p.1.src) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_A4 Γ p q) := by
  have hcnt := (BAGGOp_tail2_cnt Γ p q hp hq (BAGGOp_A4 Γ p q) (by simp)).1
  have hout := (BAG5Leaf_ext2_facts Γ q.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst),
    bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] p.1.src hx).2.1 _ hy
  rw [BAGGOp_A4_eq]
  exact BAG5Leaf_ext2_ge Γ hN q.2 _ p.1.src (BAG5Leaf_circ_tail Γ hN p q hp hq) hcnt hx
    (BAG5Leaf_pat_one _ _ _ _ _ _ rfl rfl hout (BAExpandWOrd_emb_ne_β _))

/-- `A5` (`Σ M_{xα} S_{αβ} Ǧ_{αx} G_{βy} G_{y'β} f`): both possible `M`-edges touch `β`. -/
private theorem BAG5Leaf_A5 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hx : ∀ a ∈ Γ.atom p.1.src, a.isRight = true) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_A5 Γ p q) := by
  have hcnt := (BAGGOp_tail2_cnt Γ p q hp hq (BAGGOp_A5 Γ p q) (by simp)).1
  rw [BAGGOp_A5_eq]
  exact BAG5Leaf_ext2_ge Γ hN q.2 _ p.1.src (BAG5Leaf_circ_tail Γ hN p q hp hq) hcnt hx
    (BAG5Leaf_pat_two _ _ _ _ _ _ rfl (BAExpandWOrd_emb_ne_β _) (BAExpandWOrd_emb_ne_β _))

/-- `AD` (the derivative term for the solid edge `r.1 = Ǧ_{ab}` of `f`): the edge at `α` leaves the atom of `α`, because no solid edge other
than `p.1`, `q.1` meets the atom of `x`; the others touch `β`. -/
private theorem BAG5Leaf_AD (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hx : ∀ a ∈ Γ.atom p.1.src, a.isRight = true)
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hr : r ∈ lwSplit q.2)
    (hra : r.1.src ∉ Γ.atom p.1.src) (hrb : r.1.dst ∉ Γ.atom p.1.src) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_AD Γ p q r) := by
  have hcirc'' : ∀ e ∈ r.2, e.circ = true := fun e he =>
    BAG5Leaf_circ_tail Γ hN p q hp hq e ((lwSplit_perm q.2 r hr).mem_iff.2 (List.mem_cons_of_mem _ he))
  have hcnt := (BAGGOp_tail2_cnt Γ p q hp hq (BAGGOp_AD Γ p q r)
    (List.mem_append_right _ (List.mem_map.2 ⟨r, hr, rfl⟩))).1
  have hout := (BAG5Leaf_ext2_facts Γ r.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1,
    (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst),
    bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] p.1.src hx).2.1
  rw [BAGGOp_AD_eq]
  exact BAG5Leaf_ext2_ge Γ hN r.2 _ p.1.src hcirc'' hcnt hx
    (BAG5Leaf_pat_D _ _ _ _ _ _ _ _ rfl rfl rfl (BAExpandWOrd_emb_ne_β _) (BAExpandWOrd_emb_ne_β _)
      (BAExpandWOrd_emb_ne_β _) (hout _ hra) (hout _ hrb))

/-- `B1` (`Σ M_{xu} M_{ux} S⁺_{uw} M_{wα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'w} f`): the only possible `M`-split `M_{αy}` leaves the atom `{w, α}`. -/
private theorem BAG5Leaf_B1 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_B1 Γ p q) := by
  have hcnt := (BAGGOp_tail4_cnt Γ p q hp hq (BAGGOp_B1 Γ p q) (by rw [BAGGOp_gg4_eq]; simp)).1
  have hout := (BAG5Leaf_ext4_facts Γ q.2 [bpS true (bpv 3) (bpv 3), bpS false (bpv 2) (owxEmb 4 p.1.dst),
    bpS true (owxEmb 4 q.1.src) (bpv 1)] p.1.src).2.1
  rw [BAGGOp_B1_eq]
  exact BAG5Leaf_ext4_ge Γ hN q.2 _ p.1.src (BAG5Leaf_circ_tail Γ hN p q hp hq) hcnt
    (BAG5Leaf_pat_one _ _ _ _ _ _ rfl rfl (hout _) (BAWeightOp_emb_ne _ 3))

/-- `B2` (`… Ǧ_{αw} G_{βy} G_{y'β} f`): both possible `M`-edges touch `β`. -/
private theorem BAG5Leaf_B2 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_B2 Γ p q) := by
  have hcnt := (BAGGOp_tail4_cnt Γ p q hp hq (BAGGOp_B2 Γ p q) (by rw [BAGGOp_gg4_eq]; simp)).1
  rw [BAGGOp_B2_eq]
  exact BAG5Leaf_ext4_ge Γ hN q.2 _ p.1.src (BAG5Leaf_circ_tail Γ hN p q hp hq) hcnt
    (BAG5Leaf_pat_two _ _ _ _ _ _ rfl (BAWeightOp_emb_ne _ 3) (BAWeightOp_emb_ne _ 3))

/-- `BD` (the derivative term of the third sum with `W - 1`). -/
private theorem BAG5Leaf_BD (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hr : r ∈ lwSplit q.2) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_BD Γ p q r) := by
  have hcirc'' : ∀ e ∈ r.2, e.circ = true := fun e he =>
    BAG5Leaf_circ_tail Γ hN p q hp hq e ((lwSplit_perm q.2 r hr).mem_iff.2 (List.mem_cons_of_mem _ he))
  have hcnt := (BAGGOp_tail4_cnt Γ p q hp hq (BAGGOp_BD Γ p q r)
    (by rw [BAGGOp_gg4_eq]; exact List.mem_append_right _ (List.mem_map.2 ⟨r, hr, rfl⟩))).1
  have hout := (BAG5Leaf_ext4_facts Γ r.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1,
    (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2, bpS false (bpv 3) (owxEmb 4 p.1.dst),
    bpS true (owxEmb 4 q.1.src) (bpv 1)] p.1.src).2.1
  rw [BAGGOp_BD_eq]
  exact BAG5Leaf_ext4_ge Γ hN r.2 _ p.1.src hcirc'' hcnt
    (BAG5Leaf_pat_D _ _ _ _ _ _ _ _ rfl rfl rfl (BAWeightOp_emb_ne _ 3) (BAWeightOp_emb_ne _ 3)
      (BAWeightOp_emb_ne _ 3) (hout _) (hout _))

/-- A normal graph is its own split: `ord ≥ k` of the graph is `SplitGe k`. -/
private theorem BAG5Leaf_splitGe_of_normal {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (k : ℤ) (T : BAGraph E' I') (hn : T.Normal) (h : k ≤ ord T.counters) : BAG5Leaf_SplitGe k T := by
  intro Δs hΔs
  rw [BAWeightOp_splitG_of_circ T hn.2, List.mem_singleton] at hΔs
  subst hΔs
  exact ⟨hn, h⟩

/-- `A1` (`Σ M_{xu} M_{ux} S⁺_{uβ} M_{βy} M_{y'β} f`, the first sum): `ord = ord Γ + 2κ` with `κ = 1` (the atoms of `y'`, `y` differ and one
is internal). -/
private theorem BAG5Leaf_A1 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (h2c : Γ.atom q.1.src ≠ Γ.atom p.1.dst)
    (h3 : (∀ w ∈ Γ.atom q.1.src, w.isRight = true) ∨ (∀ w ∈ Γ.atom p.1.dst, w.isRight = true)) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_A1 Γ p q) := by
  have hn : (BAGGOp_A1 Γ p q).Normal :=
    BAWeightOp_ext_normal 2 Γ hN _ _ _ _ (BAG5Leaf_circ_tail Γ hN p q hp hq) (by simp [BAGGOp_A1])
  have hκ : BAGGOp_kappa Γ q.1.src p.1.dst = 1 := by
    unfold BAGGOp_kappa
    split_ifs with h
    · exfalso
      rcases h with h | ⟨h1, h2⟩
      · exact h2c h
      · rcases h3 with h3 | h3
        · exact h1 h3
        · exact h2 h3
    · rfl
  have hraw := (gg_raw Γ p q hp hq).1
  rw [hκ] at hraw
  refine BAG5Leaf_splitGe_of_normal _ _ hn ?_
  have h1 : (BAGGOp_A1 Γ p q).scalingOrder = ord (BAGGOp_A1 Γ p q).counters := rfl
  have h2 : Γ.scalingOrder = ord Γ.counters := rfl
  push_cast at hraw
  omega

/-- `A2`, `A3` (the second sum): `ord = ord Γ + 1`. -/
private theorem BAG5Leaf_A23 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_A2 Γ p q) ∧ BAG5Leaf_SplitGe (ord Γ.counters + 1) (BAGGOp_A3 Γ p q) := by
  have hcirc' := BAG5Leaf_circ_tail Γ hN p q hp hq
  have hc := (gg_counters Γ p q hp hq).2.1
  refine ⟨BAG5Leaf_splitGe_of_normal _ _
    (BAWeightOp_ext_normal 2 Γ hN _ _ _ _ hcirc' (by simp [BAGGOp_A2, bpS])) ?_,
    BAG5Leaf_splitGe_of_normal _ _
    (BAWeightOp_ext_normal 2 Γ hN _ _ _ _ hcirc' (by simp [BAGGOp_A3, bpS])) ?_⟩
  · obtain ⟨e1, e2, e3, -⟩ := hc (BAGGOp_A2 Γ p q) (by simp)
    simp only [ord, BAGraph.counters]
    omega
  · obtain ⟨e1, e2, e3, -⟩ := hc (BAGGOp_A3 Γ p q) (by simp)
    simp only [ord, BAGraph.counters]
    omega

/-- Under H1, no solid edge of `q.2` meets the atom of `x = p.1.src = q.1.dst`: exactly two solid edges (`p.1`, `q.1`) do. -/
private theorem BAG5Leaf_tail_out (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hxy : p.1.src = q.1.dst)
    (h1c : (Γ.solid.filter fun e => decide (e.src ∈ Γ.atom p.1.src ∨ e.dst ∈ Γ.atom p.1.src)).length = 2) :
    ∀ e ∈ q.2, e.src ∉ Γ.atom p.1.src ∧ e.dst ∉ Γ.atom p.1.src := by
  have hperm : Γ.solid.Perm (p.1 :: q.1 :: q.2) :=
    (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)
  have hl := (hperm.filter (fun e => decide (e.src ∈ Γ.atom p.1.src ∨ e.dst ∈ Γ.atom p.1.src))).length_eq
  rw [h1c] at hl
  have hp1 : decide (p.1.src ∈ Γ.atom p.1.src ∨ p.1.dst ∈ Γ.atom p.1.src) = true := by
    simp [BAExpandWOrd_self_mem_atom Γ p.1.src]
  have hq1 : decide (q.1.src ∈ Γ.atom p.1.src ∨ q.1.dst ∈ Γ.atom p.1.src) = true := by
    simp [← hxy, BAExpandWOrd_self_mem_atom Γ p.1.src]
  simp only [List.filter_cons, hp1, hq1, ↓reduceIte, List.length_cons] at hl
  have h0 : (q.2.filter fun e => decide (e.src ∈ Γ.atom p.1.src ∨ e.dst ∈ Γ.atom p.1.src)).length = 0 := by omega
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
  intro e he
  have := h0 e he
  simpa [not_or] using this

end Shapes

/-! ## 5. The Lemma for a blue pair -/

section Blue

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The Lemma for a blue pair at the graph level**: with H1-H3 on `Γ` at `(p, q)`, every term of `gg2`, `gg4` is split into normal graphs of
`ord ≥ ord Γ + 1`. -/
private theorem BAG5Leaf_blue (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hxy : p.1.src = q.1.dst)
    (h1i : ∀ w ∈ Γ.atom p.1.src, w.isRight = true)
    (h1c : (Γ.solid.filter fun e => decide (e.src ∈ Γ.atom p.1.src ∨ e.dst ∈ Γ.atom p.1.src)).length = 2)
    (h2a : Γ.atom p.1.src ≠ Γ.atom p.1.dst) (h2c : Γ.atom q.1.src ≠ Γ.atom p.1.dst)
    (h3 : (∀ w ∈ Γ.atom q.1.src, w.isRight = true) ∨ (∀ w ∈ Γ.atom p.1.dst, w.isRight = true)) :
    (∀ T ∈ Γ.gg2 p q, BAG5Leaf_SplitGe (ord Γ.counters + 1) T) ∧
    (∀ T ∈ Γ.gg4 p q, BAG5Leaf_SplitGe (ord Γ.counters + 1) T) := by
  have hy : p.1.dst ∉ Γ.atom p.1.src := fun h => h2a (BAExpandWOrd_atom_eq_of_mem Γ h).symm
  have hout := BAG5Leaf_tail_out Γ p q hp hq hxy h1c
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · rw [BAGGOp_gg2_eq] at hT
    rcases List.mem_append.1 hT with hT | hT
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl
      · exact BAG5Leaf_A1 Γ hN p q hp hq h2c h3
      · exact (BAG5Leaf_A23 Γ hN p q hp hq).1
      · exact (BAG5Leaf_A23 Γ hN p q hp hq).2
      · exact BAG5Leaf_A4 Γ hN p q hp hq h1i hy
      · exact BAG5Leaf_A5 Γ hN p q hp hq h1i
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hT
      have hr1 : r.1 ∈ q.2 := (lwSplit_perm q.2 r hr).mem_iff.2 List.mem_cons_self
      exact BAG5Leaf_AD Γ hN p q hp hq h1i r hr (hout _ hr1).1 (hout _ hr1).2
  · rw [BAGGOp_gg4_eq] at hT
    rcases List.mem_append.1 hT with hT | hT
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl
      · exact BAG5Leaf_B1 Γ hN p q hp hq
      · exact BAG5Leaf_B2 Γ hN p q hp hq
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hT
      exact BAG5Leaf_BD Γ hN p q hp hq r hr

end Blue

/-! ## 6. The red charge: complex conjugation (`Graph/BAExpandId.lean`, `BAExpandId_flip`) -/

section Red

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Conjugation keeps the atom edges (a `Ψ`-dotted edge is reversed, an `M`-dotted edge changes its charge). -/
private theorem BAG5Leaf_flip_atomAdj (Δ : BAGraph E I) (u v : E ⊕ I) :
    (BAExpandId_flip Δ).atomAdj u v = Δ.atomAdj u v := by
  have h1 : ((Δ.psi.map BAExpandId_flipPsi).any fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) =
      Δ.psi.any fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) := by
    rw [List.any_map]
    congr 1
    funext e
    simp only [Function.comp, BAExpandId_flipPsi]
    by_cases h : e.y = u ∧ e.x = v ∨ e.y = v ∧ e.x = u
    · have h' : e.x = u ∧ e.y = v ∨ e.x = v ∧ e.y = u := by tauto
      simp [h, h']
    · have h' : ¬ (e.x = u ∧ e.y = v ∨ e.x = v ∧ e.y = u) := by tauto
      simp [h, h']
  have h2 : ((Δ.mdot.map BAExpandId_flipM).any fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) =
      Δ.mdot.any fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) := by
    rw [List.any_map]
    rfl
  simp only [BAGraph.atomAdj, BAExpandId_flip]
  rw [h1, h2]

private theorem BAG5Leaf_flip_atom (Δ : BAGraph E I) : (BAExpandId_flip Δ).atom = Δ.atom := by
  funext v
  have : (BAExpandId_flip Δ).atomStep = Δ.atomStep := by
    funext s
    simp only [BAGraph.atomStep, BAG5Leaf_flip_atomAdj]
  simp only [BAGraph.atom, this]

private theorem BAG5Leaf_flip_ord (Δ : BAGraph E I) : ord (BAExpandId_flip Δ).counters = ord Δ.counters := by
  have hA : (BAExpandId_flip Δ).nA = Δ.nA := by simp only [BAGraph.nA, BAG5Leaf_flip_atom]
  have hS : (BAExpandId_flip Δ).nS = Δ.nS := by simp [BAGraph.nS, BAExpandId_flip]
  have hW : (BAExpandId_flip Δ).nW = Δ.nW := by simp [BAGraph.nW, BAExpandId_flip]
  simp only [ord, BAGraph.counters, hS, hW, hA]

private theorem BAG5Leaf_flip_normal (Δ : BAGraph E I) (h : Δ.Normal) : (BAExpandId_flip Δ).Normal :=
  ⟨h.1, fun e he => by
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact h.2 e0 he0⟩

/-- Splitting `G = Ǧ + M` commutes with conjugation. -/
private theorem BAG5Leaf_split_flip {V : Type} :
    ∀ es : List (SEdge V), baSplitSolid (es.map BAExpandId_flipS) =
      (baSplitSolid es).map (fun r => (r.1.map BAExpandId_flipS, r.2.map BAExpandId_flipM))
  | [] => by simp [baSplitSolid]
  | e :: es => by
    simp only [List.map_cons, baSplitSolid, BAG5Leaf_split_flip es, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun r _ => ?_
    by_cases hc : e.circ = true
    · simp [hc, BAExpandId_flipS]
    · simp [hc, BAExpandId_flipS, BAExpandId_flipM]

private theorem BAG5Leaf_flip_splitG (Δ : BAGraph E I) :
    (BAExpandId_flip Δ).splitG = Δ.splitG.map BAExpandId_flip := by
  unfold BAGraph.splitG
  simp only [BAExpandId_flip, BAG5Leaf_split_flip, List.map_map, Function.comp_def, List.map_append]

private theorem BAG5Leaf_splitGe_flip (k : ℤ) (T : BAGraph E I) (h : BAG5Leaf_SplitGe k T) :
    BAG5Leaf_SplitGe k (BAExpandId_flip T) := by
  intro Δs hΔs
  rw [BAG5Leaf_flip_splitG, List.mem_map] at hΔs
  obtain ⟨Δ0, hΔ0, rfl⟩ := hΔs
  obtain ⟨hN0, hk⟩ := h Δ0 hΔ0
  exact ⟨BAG5Leaf_flip_normal Δ0 hN0, by rw [BAG5Leaf_flip_ord]; exact hk⟩

/-- **The Lemma for a red pair**: the lists `BAExpandId_gg2r`, `BAExpandId_gg4r` are the conjugates of the blue lists of the conjugate
graph at the conjugate pair, which satisfies the same hypotheses (the atoms, the counters and the edges meeting an atom are unchanged). -/
private theorem BAG5Leaf_red (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hxy : p.1.src = q.1.dst)
    (h1i : ∀ w ∈ Γ.atom p.1.src, w.isRight = true)
    (h1c : (Γ.solid.filter fun e => decide (e.src ∈ Γ.atom p.1.src ∨ e.dst ∈ Γ.atom p.1.src)).length = 2)
    (h2a : Γ.atom p.1.src ≠ Γ.atom p.1.dst) (h2c : Γ.atom q.1.src ≠ Γ.atom p.1.dst)
    (h3 : (∀ w ∈ Γ.atom q.1.src, w.isRight = true) ∨ (∀ w ∈ Γ.atom p.1.dst, w.isRight = true)) :
    (∀ T ∈ BAExpandId_gg2r Γ p q, BAG5Leaf_SplitGe (ord Γ.counters + 1) T) ∧
    (∀ T ∈ BAExpandId_gg4r Γ p q, BAG5Leaf_SplitGe (ord Γ.counters + 1) T) := by
  have hf := BAG5Leaf_blue (BAExpandId_flip Γ) (BAG5Leaf_flip_normal Γ hN) (BAExpandId_flipP p) (BAExpandId_flipP q)
    (BAExpandId_flipP_mem hp) (BAExpandId_flipP_mem hq) hxy
    (by rw [BAG5Leaf_flip_atom]; exact h1i)
    (by
      have h : ((BAExpandId_flip Γ).solid.filter fun e => decide (e.src ∈ (BAExpandId_flip Γ).atom p.1.src ∨
          e.dst ∈ (BAExpandId_flip Γ).atom p.1.src)).length = 2 := by
        rw [BAG5Leaf_flip_atom]
        change ((Γ.solid.map BAExpandId_flipS).filter _).length = 2
        rw [List.filter_map, List.length_map]
        exact h1c
      exact h)
    (by rw [BAG5Leaf_flip_atom]; exact h2a) (by rw [BAG5Leaf_flip_atom]; exact h2c)
    (by rw [BAG5Leaf_flip_atom]; exact h3)
  rw [BAG5Leaf_flip_ord] at hf
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · obtain ⟨T', hT', rfl⟩ := List.mem_map.1 (show T ∈ _ from hT)
    exact BAG5Leaf_splitGe_flip _ T' (hf.1 T' hT')
  · obtain ⟨T', hT', rfl⟩ := List.mem_map.1 (show T ∈ _ from hT)
    exact BAG5Leaf_splitGe_flip _ T' (hf.2 T' hT')

end Red

/-! ## 7. The Lemma (both charges) and its form at the children -/

/-- The split form of `ord ≥ k` gives the form of `scalingOrderG`. -/
private theorem BAG5Leaf_ordG {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (k : ℤ)
    (T : BAGraph E I) (h : BAG5Leaf_SplitGe k T) : ((k : ℤ) : WithTop ℤ) ≤ T.scalingOrderG :=
  BAGGOp_ordG_of_split T k h

/-- **The GG-with-context Lemma** (`(eq:GGraisesord)`, `B:99`, with H1-H3; paper delta T2398b), for both charges: at a candidate `c` of a packed
graph `P` with `BACtx c`, every term of the `gg2` and `gg4` lists of the charge of `c` has `ordG ≥ ord P + 1`.  Hypotheses: `BACtx c` only; no
smallness, no scalar data.  The context is needed: without H3 the conclusion is false (`BAG5LeafInst.baG5Ctx_H3_needed`: the first sum keeps
the order when `y`, `y'` are both external). -/
theorem baG5CtxLemma_holds : BAG5CtxLemma := by
  intro P c hc
  obtain ⟨hN, h1i, h1c, h2a, -, h2c, h3⟩ := hc
  have hxy : c.p.1.src = c.q.1.dst := c.hpv.trans c.hqv.symm
  rw [← c.hpv] at h1i h1c h2a
  have hP : P.scalingOrder = ord P.g.counters := rfl
  rcases Bool.eq_false_or_eq_true c.σ with hσ | hσ
  · obtain ⟨hb2, hb4⟩ := BAG5Leaf_blue P.g hN c.p c.q c.hp c.hq hxy h1i h1c h2a h2c h3
    have e2 : BAExpandId_ggL2 c.σ P.g c.p c.q = P.g.gg2 c.p c.q := by simp [BAExpandId_ggL2, hσ]
    have e4 : BAExpandId_ggL4 c.σ P.g c.p c.q = P.g.gg4 c.p c.q := by simp [BAExpandId_ggL4, hσ]
    rw [e2, e4, hP]
    exact ⟨fun T hT => BAG5Leaf_ordG _ T (hb2 T hT), fun T hT => BAG5Leaf_ordG _ T (hb4 T hT)⟩
  · obtain ⟨hr2, hr4⟩ := BAG5Leaf_red P.g hN c.p c.q c.hp c.hq hxy h1i h1c h2a h2c h3
    have e2 : BAExpandId_ggL2 c.σ P.g c.p c.q = BAExpandId_gg2r P.g c.p c.q := by simp [BAExpandId_ggL2, hσ]
    have e4 : BAExpandId_ggL4 c.σ P.g c.p c.q = BAExpandId_gg4r P.g c.p c.q := by simp [BAExpandId_ggL4, hσ]
    rw [e2, e4, hP]
    exact ⟨fun T hT => BAG5Leaf_ordG _ T (hr2 T hT), fun T hT => BAG5Leaf_ordG _ T (hr4 T hT)⟩

/-- **The Lemma at the children** (the form that the leaf half of `lem:LWterm_EXP` consumes): every packed child of a candidate with `BACtx`
has `ord ≥ ord P + 1`. -/
theorem baG5CtxKids_holds : BAG5CtxKids := by
  intro P c hc r hr
  have hL := baG5CtxLemma_holds P c hc
  have key : ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')),
      (∀ T ∈ Ts, ((P.scalingOrder + 1 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) →
        ∀ r ∈ BAExpandId_outsOf P Ts, P.scalingOrder + 1 ≤ r.2.scalingOrder := by
    intro I' _ _ Ts hTs r hr
    obtain ⟨T, hT, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hr
    exact (BAGraph.le_scalingOrderG_iff T (P.scalingOrder + 1)).1 (hTs T hT) Q hQ
  rcases List.mem_append.1 hr with hr | hr
  · exact key _ hL.1 r hr
  · exact key _ hL.2 r hr

/-! ## 8. The selector -/

/-- **The selection rule `S*`**: stop at a leaf; otherwise a blue candidate with `BACtx` (classical choice), and nothing else; `none` if there
is no such candidate.  Candidates outside `BACtx` are never selected (H234, H235 Q3-C2); that a tree ends in leaves is not claimed. -/
def BAselStar : BASel := fun P =>
  open Classical in
  if BAG5Leaf P then none else if h : ∃ c : BARCand P, c.σ = true ∧ BACtx c then some h.choose else none

/-- A selected candidate is a blue `BACtx` candidate of a non-leaf. -/
theorem baselStar_spec (P : BAPGraph (Fin 2)) (c : BARCand P) (h : BAselStar P = some c) :
    ¬ BAG5Leaf P ∧ c.σ = true ∧ BACtx c := by
  classical
  unfold BAselStar at h
  by_cases hl : BAG5Leaf P
  · simp [hl] at h
  · by_cases hex : ∃ c : BARCand P, c.σ = true ∧ BACtx c
    · simp only [hl, hex, ↓reduceIte, ↓reduceDIte, Option.some.injEq] at h
      subst h
      exact ⟨hl, hex.choose_spec⟩
    · simp [hl, hex] at h

/-- **When the selector returns `none`** (and hence, by contraposition, when it selects): at a leaf, or when there is no blue `BACtx` candidate.
(An `Iff` without a `Prop`-valued hypothesis, so that the premise scan of `#assert_rbm_axioms` does not see `BAG5Leaf` as assumed.) -/
theorem baselStar_eq_none_iff (P : BAPGraph (Fin 2)) :
    BAselStar P = none ↔ BAG5Leaf P ∨ ¬ ∃ c : BARCand P, c.σ = true ∧ BACtx c := by
  classical
  unfold BAselStar
  by_cases hl : BAG5Leaf P
  · simp [hl]
  · by_cases hex : ∃ c : BARCand P, c.σ = true ∧ BACtx c
    · simp [hl, hex]
    · simp [hl, hex]

/-! ## 9. Compiled instances (namespace `RBM.Graph.BAG5LeafInst`)

The merged parents of `Graph/BAExpandId.lean` (`BAExpandIdInst.instP`, ord `3`, 5 solid edges, 3 internal vertices, `E' = Fin 2`; its conjugate
`instPRed`) with their blue and red candidates `instCand`, `instCandRed` at `v = inr 0`, `p = Ǧ_{inr0 inr1}`, `q = Ǧ_{inl0 inr0}`: `BACtx` holds
there (H1: `atom v = {inr 0}` is internal and exactly `p.1`, `q.1` meet it; H2: the three atoms are distinct singletons; H3: `y = inr 1` is
internal), so the Lemma and its form at the children apply; the `63` children of each have `ord ≥ 4`.  The Lemma has no analytic hypothesis, so
no limit check applies. -/

end RBM.Graph
