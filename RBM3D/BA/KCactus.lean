/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KBase
import RBM3D.Loop.KLCut
import RBM3D.Loop.KLTree
import RBM3D.Loop.Partition

/-!
# Stage K, row K04: the cactus of a crossing-free diagonal set and its value `Γ_M(F)`

Ticket T2367 (design BA-DK, `docs/reports/T2360-design.md` §3 (a), §4 row K04, §5; paper deltas
D633, D634).  The band tree sum puts one label on each tree node (`KLtreeValW`,
`Loop/KLTree.lean:114`).  In the block Anderson tree sum every node is an `M`-cycle, i.e. a
polygon with one label per *slot* (`A:552-598`, `tree-representation_BA`,
`(M-graph-value-unsummed2)`).

1. The edge kernel from `M`: `BAMssOf`, `BAThetaOf` (`(eq:Msig)`, `(def_Thxi)` at `S^{(B)} = I`).
2. The slots `BAslot F = Fin n ⊕ ↥F ⊕ ↥F` of `F` with `KLIsTSP F`: one per pair (node, edge).
3. The cyclic order of the slots of a node by the first vertex `BAslotStart` of the vertex range
   of the edge; its successor `BAnextSlot` (a permutation preserving `BAslotNode`, one cycle per
   node) and the charge `BAMcharge` of the `M`-edge `s → BAnextSlot s`.
4. The value `BACactusVal`, an instance of the merged generic tree value `KLgval`
   (`Loop/KLCut.lean:58`) with the slots as nodes, and `BAGamma`, the `Γ` of the pin `BATreeRep`.
5. API: transport (`BACactusVal_congr`), the value at `F = ∅` and at `n = 3` (`(Kn3sol)`),
   orientation invariance for symmetric `M`, the `t = 0` identity with `BAMLoop`,
   compiled instances.

Hypotheses of the API lemmas: `KLIsTSP F` and `2 ≤ n` (implied by `3 ≤ n`) only.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. The edge kernel from `M` -/

section Edge

variable {d L : ℕ}

/-- `M^{(σ₁,σ₂)}_{ab} = M(σ₁)_{ba} M(σ₂)_{ab}` for a general charge-indexed `M` (`(eq:Msig)`, `1_2:1070-1071`). -/
def BAMssOf (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun a b => M σ₁ b a * M σ₂ a b

/-- Bridge: `BAMss` of the merged `BA/MFixedPoint.lean:511` is `BAMssOf` at `M(σ) = BAMsigma B σ`. -/
theorem BAMssOf_BAMsigma (B : Matrix (Zd d L) (Zd d L) ℂ) (σ₁ σ₂ : Bool) :
    BAMssOf (BAMsigma d L B) σ₁ σ₂ = BAMss d L B σ₁ σ₂ := rfl

/-- If every `M(σ)` is symmetric then so is every `M^{(σ₁,σ₂)}`. -/
theorem BAMssOf_isSymm {M : Bool → Matrix (Zd d L) (Zd d L) ℂ} (hM : ∀ σ, (M σ)ᵀ = M σ) (σ₁ σ₂ : Bool) :
    (BAMssOf M σ₁ σ₂)ᵀ = BAMssOf M σ₁ σ₂ := by
  have h1 : ∀ σ x y, M σ x y = M σ y x := fun σ x y => by
    simpa using congrFun (congrFun (hM σ) y) x
  ext a b
  simp only [Matrix.transpose_apply, BAMssOf, Matrix.of_apply]
  rw [h1 σ₁ a b, h1 σ₂ b a]

variable [NeZero L]

/-- `Θ_t^{(σ₁,σ₂)} = (1 - t M^{(σ₁,σ₂)})⁻¹` (`(def_Thxi)` at `S^{(B)} = I`, `1_2:1073-1076`) for a general
charge-indexed `M`. -/
def BAThetaOf (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ₁ σ₂ : Bool) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  PropThetaQ (BAMssOf M σ₁ σ₂) t

/-- Bridge: `BATheta` of the merged `BA/MFixedPoint.lean:515` is `BAThetaOf` at `M(σ) = BAMsigma (BAMB ..) σ`.  So
`Γ` is a function of `(Bool → Matrix, t)` only, as `BATreeRep` requires. -/
theorem BAThetaOf_BAMsigma (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) :
    BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₁ σ₂ = BATheta d L g E m t σ₁ σ₂ := rfl

/-- If every `M(σ)` is symmetric then so is every `Θ_t^{(σ₁,σ₂)}` (for every `t`: `Ring.inverse` commutes with
transposition, no invertibility is needed). -/
theorem BAThetaOf_isSymm {M : Bool → Matrix (Zd d L) (Zd d L) ℂ} (hM : ∀ σ, (M σ)ᵀ = M σ) (t : ℝ)
    (σ₁ σ₂ : Bool) : (BAThetaOf M t σ₁ σ₂)ᵀ = BAThetaOf M t σ₁ σ₂ := by
  unfold BAThetaOf PropThetaQ
  have hs : (1 - (t : ℂ) • BAMssOf M σ₁ σ₂)ᵀ = 1 - (t : ℂ) • BAMssOf M σ₁ σ₂ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, BAMssOf_isSymm hM]
  rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv, hs]

end Edge

/-! ## 2. The slots of the cactus -/

section Slots

variable {n : ℕ}

/-- The **slots** of the cactus of `F` (design §3 (a), §5): one per pair (node, incident edge) of the tree of `F`.
`Sum.inl v`: the leaf `v`, a slot in the node `KLleafPar F v`.  `Sum.inr (Sum.inl J)`: the chord `J ∈ F` seen from
its parent node `KLnodePar F J`.  `Sum.inr (Sum.inr J)`: the chord `J ∈ F` seen from the node `J` itself.
`n + 2 |F|` slots (`BAslot_card`). -/
abbrev BAslot (F : Finset (Fin n × Fin n)) : Type := Fin n ⊕ ↥F ⊕ ↥F

/-- The slot of the leaf `v`, in the node `KLleafPar F v`. -/
abbrev BAslotLeaf (F : Finset (Fin n × Fin n)) (v : Fin n) : BAslot F := Sum.inl v

/-- The slot of the chord `J`, in the node `KLnodePar F J` (the edge going down to `J`). -/
abbrev BAslotOut (F : Finset (Fin n × Fin n)) (J : ↥F) : BAslot F := Sum.inr (Sum.inl J)

/-- The slot of the chord `J`, in the node `J` (the edge going up to `KLnodePar F J`). -/
abbrev BAslotIn (F : Finset (Fin n × Fin n)) (J : ↥F) : BAslot F := Sum.inr (Sum.inr J)

/-- **`BAslot_card`**: the cactus of `F` has `n + 2 |F|` slots (no hypothesis on `F` is needed: the slot type is a
sum type). -/
theorem BAslot_card (F : Finset (Fin n × Fin n)) : Fintype.card (BAslot F) = n + 2 * F.card := by
  simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
  ring

/-- The first vertex `x` of the vertex range of the edge of the slot: the leaf `v` has the range `[v, v]`; the child
side of the chord `J = (i, j)` has the range of the arc `[i, j)`, so `x = i`; its parent side has the complementary
range `[j, i)` (cyclic), so `x = j`.  The charge of an `M`-edge is `σ_x` (D633). -/
def BAslotStart (F : Finset (Fin n × Fin n)) : BAslot F → Fin n
  | Sum.inl v => v
  | Sum.inr (Sum.inl J) => J.1.1
  | Sum.inr (Sum.inr J) => J.1.2

@[simp] theorem BAslotStart_leaf (F : Finset (Fin n × Fin n)) (v : Fin n) :
    BAslotStart F (BAslotLeaf F v) = v := rfl

@[simp] theorem BAslotStart_out (F : Finset (Fin n × Fin n)) (J : ↥F) :
    BAslotStart F (BAslotOut F J) = J.1.1 := rfl

@[simp] theorem BAslotStart_in (F : Finset (Fin n × Fin n)) (J : ↥F) :
    BAslotStart F (BAslotIn F J) = J.1.2 := rfl

variable [NeZero n]

/-- The node of a slot: the tree node (`KLnodes F`, an `M`-cycle) the slot belongs to. -/
def BAslotNode (F : Finset (Fin n × Fin n)) : BAslot F → Fin n × Fin n
  | Sum.inl v => KLleafPar F v
  | Sum.inr (Sum.inl J) => KLnodePar F J.1
  | Sum.inr (Sum.inr J) => J.1

@[simp] theorem BAslotNode_leaf (F : Finset (Fin n × Fin n)) (v : Fin n) :
    BAslotNode F (BAslotLeaf F v) = KLleafPar F v := rfl

@[simp] theorem BAslotNode_out (F : Finset (Fin n × Fin n)) (J : ↥F) :
    BAslotNode F (BAslotOut F J) = KLnodePar F J.1 := rfl

@[simp] theorem BAslotNode_in (F : Finset (Fin n × Fin n)) (J : ↥F) :
    BAslotNode F (BAslotIn F J) = J.1 := rfl

theorem BAslotNode_mem_nodes (F : Finset (Fin n × Fin n)) (s : BAslot F) : BAslotNode F s ∈ KLnodes F := by
  rcases s with v | J | J
  · exact KLleafPar_mem F v
  · exact KLnodePar_mem F J.1
  · exact KLmem_nodes_of_mem J.2

end Slots

/-! ## 3. Distinct starts inside a node -/

section Starts

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
include hF hn

private theorem BAKCactus_leaf_out (v : Fin n) (J : ↥F) (hnode : KLleafPar F v = KLnodePar F J.1)
    (hstart : v = J.1.1) : False := by
  have hlt := KLlt_of_mem_nodes hF hn (KLmem_nodes_of_mem J.2)
  have hv : KLInArc J.1 v := ⟨le_of_eq hstart.symm, hstart ▸ hlt⟩
  have h1 := KLleafPar_arcLe_of_inArc hF J.2 hv
  rw [hnode] at h1
  exact KLnot_arcLe_nodePar_self hF hn J.2 h1

private theorem BAKCactus_leaf_in (v : Fin n) (J : ↥F) (hnode : KLleafPar F v = J.1)
    (hstart : v = J.1.2) : False := by
  by_cases hv : v.val < n - 1
  · have h1 := (KLleafPar_spec hF hv).1
    rw [hnode] at h1
    exact absurd h1.2 (by rw [hstart]; exact lt_irrefl _)
  · have hroot : v.val = n - 1 := by have := v.isLt; omega
    rw [KLleafPar_root F hroot] at hnode
    exact KLwholeP_not_mem hF (hnode ▸ J.2)

private theorem BAKCactus_out_out (J K : ↥F) (hnode : KLnodePar F J.1 = KLnodePar F K.1)
    (hstart : J.1.1 = K.1.1) : J = K := by
  by_contra hne
  have hne' : J.1 ≠ K.1 := fun h => hne (Subtype.ext h)
  rcases lt_trichotomy J.1.2 K.1.2 with h | h | h
  · have hJK : KLArcLe J.1 K.1 := ⟨le_of_eq hstart.symm, le_of_lt h⟩
    have h1 := KLnodePar_arcLe hF hn K.2 J.2 hJK hne'
    rw [hnode] at h1
    exact KLnot_arcLe_nodePar_self hF hn K.2 h1
  · exact hne (Subtype.ext (Prod.ext hstart h))
  · have hKJ : KLArcLe K.1 J.1 := ⟨le_of_eq hstart, le_of_lt h⟩
    have h1 := KLnodePar_arcLe hF hn J.2 K.2 hKJ (Ne.symm hne')
    rw [← hnode] at h1
    exact KLnot_arcLe_nodePar_self hF hn J.2 h1

private theorem BAKCactus_out_in (J K : ↥F) (hnode : KLnodePar F J.1 = K.1)
    (hstart : J.1.1 = K.1.2) : False := by
  have hle := (KLnodePar_spec hF hn (KLmem_nodes_of_mem J.2) (KLne_wholeP hF J.2)).2.1
  rw [hnode] at hle
  have hlt := KLlt_of_mem_nodes hF hn (KLmem_nodes_of_mem J.2)
  exact absurd hlt (not_lt.mpr (hstart ▸ hle.2))

/-- **The starts are pairwise distinct inside a node** (laminarity: `KLleafPar_spec`, `KLnodePar_spec`,
`KLwholeP_not_mem`): two slots of the same node with the same start are equal.  Hypotheses: `KLIsTSP F`, `2 ≤ n`. -/
theorem BAslot_start_inj {s t : BAslot F} (hnode : BAslotNode F s = BAslotNode F t)
    (hstart : BAslotStart F s = BAslotStart F t) : s = t := by
  rcases s with v | J | J <;> rcases t with w | K | K <;> simp only [BAslotNode, BAslotStart] at hnode hstart
  · exact congrArg Sum.inl hstart
  · exact (BAKCactus_leaf_out hF hn v K hnode hstart).elim
  · exact (BAKCactus_leaf_in hF hn v K hnode hstart).elim
  · exact (BAKCactus_leaf_out hF hn w J hnode.symm hstart.symm).elim
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (BAKCactus_out_out hF hn J K hnode hstart)
  · exact (BAKCactus_out_in hF hn J K hnode hstart).elim
  · exact (BAKCactus_leaf_in hF hn w J hnode.symm hstart.symm).elim
  · exact (BAKCactus_out_in hF hn K J hnode.symm hstart.symm).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext hnode)

end Starts

/-! ## 4. The cyclic successor inside a node, `BAnextSlot`, and the charge `BAMcharge` -/

section Succ

variable {α β : Type*} [Finite α]

/-- `u` is the cyclic successor of `s` for the keys `key` inside the fibre of `node`: the element of the fibre of `s`
with the next larger key, or, if `s` has the largest key, the element with the smallest key. -/
private def BAKCactus_IsSucc (node : α → β) (key : α → ℕ) (s u : α) : Prop :=
  node u = node s ∧
    ((key s < key u ∧ ∀ x, node x = node s → key s < key x → key u ≤ key x) ∨
      ((∀ x, node x = node s → key x ≤ key s) ∧ ∀ x, node x = node s → key u ≤ key x))

private theorem BAKCactus_isSucc_exists (node : α → β) (key : α → ℕ) (s : α) :
    ∃ u, BAKCactus_IsSucc node key s u := by
  classical
  have := Fintype.ofFinite α
  by_cases h : ∃ x, node x = node s ∧ key s < key x
  · have hne : (Finset.univ.filter fun x => node x = node s ∧ key s < key x).Nonempty := by
      obtain ⟨x, hx⟩ := h
      exact ⟨x, by simp [hx]⟩
    obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image _ key hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hmin
    exact ⟨u, hu.1, Or.inl ⟨hu.2, fun x hx hlt => hmin x ⟨hx, hlt⟩⟩⟩
  · push Not at h
    have hne : (Finset.univ.filter fun x => node x = node s).Nonempty := ⟨s, by simp⟩
    obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image _ key hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hmin
    exact ⟨u, hu, Or.inr ⟨h, hmin⟩⟩

/-- The cyclic successor, a total function (a choice; it is determined when the keys are injective on each fibre,
`BAKCactus_IsSucc_eq`). -/
private def BAKCactus_succ (node : α → β) (key : α → ℕ) (s : α) : α :=
  Classical.choose (BAKCactus_isSucc_exists node key s)

private theorem BAKCactus_succ_spec (node : α → β) (key : α → ℕ) (s : α) :
    BAKCactus_IsSucc node key s (BAKCactus_succ node key s) :=
  Classical.choose_spec (BAKCactus_isSucc_exists node key s)

variable {node : α → β} {key : α → ℕ}

omit [Finite α] in
private theorem BAKCactus_IsSucc_eq (hinj : ∀ x y, node x = node y → key x = key y → x = y) {s u u' : α}
    (h : BAKCactus_IsSucc node key s u) (h' : BAKCactus_IsSucc node key s u') : u = u' := by
  obtain ⟨hn, hc⟩ := h
  obtain ⟨hn', hc'⟩ := h'
  have hkey : key u = key u' := by
    rcases hc with ⟨hlt, hmin⟩ | ⟨hmax, hmin⟩ <;> rcases hc' with ⟨hlt', hmin'⟩ | ⟨hmax', hmin'⟩
    · exact le_antisymm (hmin u' hn' hlt') (hmin' u hn hlt)
    · exact absurd hlt (not_lt.mpr (hmax' u hn))
    · exact absurd hlt' (not_lt.mpr (hmax u' hn'))
    · exact le_antisymm (hmin u' hn') (hmin' u hn)
  exact hinj u u' (hn.trans hn'.symm) hkey

private theorem BAKCactus_succ_injective (hinj : ∀ x y, node x = node y → key x = key y → x = y) :
    Function.Injective (BAKCactus_succ node key) := by
  intro s t hst
  have hs := BAKCactus_succ_spec node key s
  have ht := BAKCactus_succ_spec node key t
  rw [hst] at hs
  obtain ⟨hn1, hc1⟩ := hs
  obtain ⟨hn2, hc2⟩ := ht
  have hnst : node s = node t := hn1.symm.trans hn2
  rcases hc1 with ⟨hlt1, hmin1⟩ | ⟨hmax1, hmin1⟩ <;> rcases hc2 with ⟨hlt2, hmin2⟩ | ⟨hmax2, hmin2⟩
  · by_contra hne
    have hk : key s ≠ key t := fun h => hne (hinj s t hnst h)
    rcases lt_or_gt_of_ne hk with h | h
    · exact absurd (hmin1 t hnst.symm h) (not_le.mpr hlt2)
    · exact absurd (hmin2 s hnst h) (not_le.mpr hlt1)
  · exact absurd (hmin2 s hnst) (not_le.mpr hlt1)
  · exact absurd (hmin1 t hnst.symm) (not_le.mpr hlt2)
  · exact hinj s t hnst (le_antisymm (hmax2 s hnst) (hmax1 t hnst.symm))

/-- Going up inside a fibre without wrapping. -/
private theorem BAKCactus_succ_reach_up (hinj : ∀ x y, node x = node y → key x = key y → x = y) :
    ∀ (m : ℕ) (s t : α), key t - key s = m → node s = node t → key s ≤ key t →
      ∃ k, (BAKCactus_succ node key)^[k] s = t := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s t hm hnode hle
    by_cases hst : s = t
    · exact ⟨0, hst⟩
    · have hlt : key s < key t := lt_of_le_of_ne hle (fun h => hst (hinj s t hnode h))
      obtain ⟨hn1, hc1⟩ := BAKCactus_succ_spec node key s
      rcases hc1 with ⟨hlt1, hmin1⟩ | ⟨hmax1, hmin1⟩
      · have hle' : key (BAKCactus_succ node key s) ≤ key t := hmin1 t hnode.symm hlt
        obtain ⟨k, hk⟩ := ih (key t - key (BAKCactus_succ node key s)) (by omega)
          (BAKCactus_succ node key s) t rfl (hn1.trans hnode) hle'
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
      · exact absurd (hmax1 t hnode.symm) (not_le.mpr hlt)

/-- **One cycle per fibre**: any two elements of a fibre are in the same orbit of the successor. -/
private theorem BAKCactus_succ_reach (hinj : ∀ x y, node x = node y → key x = key y → x = y) {s t : α}
    (hnode : node s = node t) : ∃ k, (BAKCactus_succ node key)^[k] s = t := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨top, htop, hmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun x => node x = node s) key ⟨s, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htop hmax
  obtain ⟨k₁, hk₁⟩ := BAKCactus_succ_reach_up hinj _ s top rfl htop.symm (hmax s rfl)
  obtain ⟨hnw, hcw⟩ := BAKCactus_succ_spec node key top
  have hwmin : ∀ x, node x = node top → key (BAKCactus_succ node key top) ≤ key x := by
    rcases hcw with ⟨hlt, _⟩ | ⟨_, hmin⟩
    · exact absurd hlt (not_lt.mpr (hmax _ (hnw.trans htop)))
    · exact hmin
  have htn : node t = node top := hnode.symm.trans htop.symm
  obtain ⟨k₂, hk₂⟩ := BAKCactus_succ_reach_up hinj _ (BAKCactus_succ node key top) t rfl
    (hnw.trans (htop.trans hnode)) (hwmin t htn)
  refine ⟨k₂ + (1 + k₁), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, hk₁, Function.iterate_one]
  exact hk₂

end Succ

section NextSlot

variable {n : ℕ} [NeZero n]

/-- **`BAnextSlot F s`: the successor of the slot `s` in the cyclic order of its node** (design §3 (a)): the slot of the
same node whose edge has the next larger first vertex `BAslotStart`, or, for the slot with the largest start, the slot
with the smallest start.  A total function (a choice, determined by the characterisation lemmas
`BAnextSlot_eq_of_above`, `BAnextSlot_eq_of_wrap` when `KLIsTSP F`, `2 ≤ n`).  The paper's "counterclockwise order" of
`m-loop-tsp` item 1 is this order (`T2367a`). -/
def BAnextSlot (F : Finset (Fin n × Fin n)) (s : BAslot F) : BAslot F :=
  BAKCactus_succ (BAslotNode F) (fun x => (BAslotStart F x).val) s

/-- The successor stays in the node (no hypothesis). -/
theorem BAslotNode_nextSlot (F : Finset (Fin n × Fin n)) (s : BAslot F) :
    BAslotNode F (BAnextSlot F s) = BAslotNode F s :=
  (BAKCactus_succ_spec (BAslotNode F) (fun x => (BAslotStart F x).val) s).1

/-- The defining property of `BAnextSlot` (no hypothesis): in the node of `s`, either `s` has a larger slot and the
successor is the next larger one, or `s` is the largest and the successor is the smallest. -/
theorem BAnextSlot_spec (F : Finset (Fin n × Fin n)) (s : BAslot F) :
    (BAslotStart F s < BAslotStart F (BAnextSlot F s) ∧
        ∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F s < BAslotStart F x →
          BAslotStart F (BAnextSlot F s) ≤ BAslotStart F x) ∨
      ((∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F x ≤ BAslotStart F s) ∧
        ∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F (BAnextSlot F s) ≤ BAslotStart F x) :=
  (BAKCactus_succ_spec (BAslotNode F) (fun x => (BAslotStart F x).val) s).2

variable {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
include hF hn

private theorem BAKCactus_hinj :
    ∀ x y : BAslot F, BAslotNode F x = BAslotNode F y → (BAslotStart F x).val = (BAslotStart F y).val → x = y :=
  fun _ _ hnode hkey => BAslot_start_inj hF hn hnode (Fin.ext hkey)

/-- Characterisation of `BAnextSlot`, case "has a larger slot": `u` is the slot of the node of `s` with the least start
above `start s`. -/
theorem BAnextSlot_eq_of_above {s u : BAslot F} (hnode : BAslotNode F u = BAslotNode F s)
    (hlt : BAslotStart F s < BAslotStart F u)
    (hmin : ∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F s < BAslotStart F x →
      BAslotStart F u ≤ BAslotStart F x) : BAnextSlot F s = u :=
  BAKCactus_IsSucc_eq (BAKCactus_hinj hF hn) (BAKCactus_succ_spec (BAslotNode F) (fun x => (BAslotStart F x).val) s)
    ⟨hnode, Or.inl ⟨hlt, hmin⟩⟩

/-- Characterisation of `BAnextSlot`, case "wrap": `s` has the largest start in its node and `u` the smallest. -/
theorem BAnextSlot_eq_of_wrap {s u : BAslot F} (hnode : BAslotNode F u = BAslotNode F s)
    (hmax : ∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F x ≤ BAslotStart F s)
    (hmin : ∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F u ≤ BAslotStart F x) :
    BAnextSlot F s = u :=
  BAKCactus_IsSucc_eq (BAKCactus_hinj hF hn) (BAKCactus_succ_spec (BAslotNode F) (fun x => (BAslotStart F x).val) s)
    ⟨hnode, Or.inr ⟨hmax, hmin⟩⟩

/-- **`BAnextSlot` is injective**, hence bijective. -/
theorem BAnextSlot_injective : Function.Injective (BAnextSlot F) :=
  BAKCactus_succ_injective (BAKCactus_hinj hF hn)

/-- **`BAnextSlot` is a permutation of `BAslot F`.** -/
theorem BAnextSlot_bijective : Function.Bijective (BAnextSlot F) :=
  Finite.injective_iff_bijective.1 (BAnextSlot_injective hF hn)

/-- `BAnextSlot` as a permutation of the slots. -/
def BAnextSlotPerm : Equiv.Perm (BAslot F) :=
  Equiv.ofBijective (BAnextSlot F) (BAnextSlot_bijective hF hn)

/-- **Each node is one cycle of `BAnextSlot`**: two slots lie in the same node iff one is reached from the other by
iterating `BAnextSlot` (`⇒`: one cycle per node; `⇐`: `BAnextSlot` preserves `BAslotNode`). -/
theorem BAnextSlot_orbit (s t : BAslot F) :
    BAslotNode F s = BAslotNode F t ↔ ∃ k : ℕ, (BAnextSlot F)^[k] s = t := by
  refine ⟨fun h => BAKCactus_succ_reach (BAKCactus_hinj hF hn) h, ?_⟩
  rintro ⟨k, rfl⟩
  clear hF hn
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ← ih, BAslotNode_nextSlot]

/-- **`BAnextSlotPerm` has one cycle per node**, in Mathlib's terms: two slots are in the same cycle iff they have the
same node. -/
theorem BAnextSlot_sameCycle_iff (s t : BAslot F) :
    (BAnextSlotPerm hF hn).SameCycle s t ↔ BAslotNode F s = BAslotNode F t := by
  rw [BAnextSlot_orbit hF hn]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [← hk, ← Equiv.Perm.iterate_eq_pow]; rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow]; exact hk⟩

end NextSlot

section Charge

variable {n : ℕ} [NeZero n]

/-- **`BAMcharge F σ s`: the charge of the `M`-edge from the slot `s` to `BAnextSlot F s`** (D633, design §3 (a),
`A:571`).  The `M`-edge between consecutive edges of a node lies in the region `R_x` of the boundary edge
`(a_{x-1}, a_x)` ending at the first vertex `x` of the next edge's vertex range, so its charge is `σ_x`,
`x = BAslotStart F (BAnextSlot F s)`.  The convention is K00's (`BAMLoop_apply`): `σ_i` sits on `(a_{i-1}, a_i)`. -/
def BAMcharge (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (s : BAslot F) : Bool :=
  σ (BAslotStart F (BAnextSlot F s))

@[simp] theorem BAMcharge_def (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (s : BAslot F) :
    BAMcharge F σ s = σ (BAslotStart F (BAnextSlot F s)) := rfl

end Charge

/-! ## 5. The value `BACactusVal` and `BAGamma` -/

section Value

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- Leaf weights of the cactus: the leaf `v` carries `Θ_t^{(σ_v, σ_{v+1})}` (`(f-external2)`, `A:556`: an external
edge between the regions `R_v`, `R_{v+1}`; `(Kn3sol)`, `1_2:1176`), from the label `a v` to its slot. -/
def BACactusValLeafW (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) :
    Fin n → Matrix (Zd d L) (Zd d L) ℂ :=
  fun v => BAThetaOf M t (σ v) (σ (v + 1))

/-- The edge weights of the cactus, over the edge type `↥F ⊕ BAslot F` (chords `⊕` `M`-edges): the chord `J = (i, j)`
carries `t Θ_t^{(σ_i, σ_j)}` (`(f-internal2)` at `S^{(B)} = I`, `A:561`, D633); the `M`-edge from the slot `s`
carries `M(BAMcharge F σ s)` (`(eq:Mloop_defgen)`, `A:567`). -/
def BACactusValEdgeW (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (F : Finset (Fin n × Fin n))
    (σ : Fin n → Bool) : ↥F ⊕ BAslot F → Matrix (Zd d L) (Zd d L) ℂ :=
  Sum.elim (fun J => (t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)) (fun s => M (BAMcharge F σ s))

/-- The first end of an edge: the chord `J` starts at its slot in the node `J` (`BAslotIn`), the `M`-edge of `s` at `s`. -/
def BACactusValSrc (F : Finset (Fin n × Fin n)) : ↥F ⊕ BAslot F → BAslot F :=
  Sum.elim (fun J => BAslotIn F J) id

/-- The second end of an edge: the chord `J` ends at its slot in the node `KLnodePar F J` (`BAslotOut`), the `M`-edge of
`s` at `BAnextSlot F s`. -/
def BACactusValTgt (F : Finset (Fin n × Fin n)) : ↥F ⊕ BAslot F → BAslot F :=
  Sum.elim (fun J => BAslotOut F J) (BAnextSlot F)

variable (d L)

/-- **`BACactusVal d L M t F σ a`: the value `Γ_M(F)` of the `M`-graph of `F`** (`(M-graph-value-unsummed2)`,
`A:583`): `∑_b ∏_v Θ^{(σ_v,σ_{v+1})}(a_v, b(leaf v)) ∏_{J=(i,j)∈F} (tΘ^{(σ_i,σ_j)})(b(in J), b(out J))
∏_s M(charge s)(b s, b(next s))`, the generic tree value `KLgval` with the slots as nodes, the leaves `Fin n`
and the edges chords `⊕` `M`-edges.  The factor `W^{-d(n-1)}` of `tree-representation_BA` is not in `Γ`:
`W^{(k_i-1)d} 𝓜^{(k_i)} = ∏ M` (`(eq:Mloop_defgen)`, `BAMLoop_apply`). -/
def BACactusVal (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) : ℂ :=
  KLgval d L (Nd := BAslot F) (Lf := Fin n) a (BACactusValLeafW M t σ) (BAslotLeaf F)
    (BACactusValEdgeW M t F σ) (BACactusValSrc F) (BACactusValTgt F)

end Value

/-- **`BAGamma d L n M t F σ a`: the `Γ` of the pin `BATreeRep`** (`tree-representation_BA`, `A:592-598`, here `n ≥ 3`,
D634): `BACactusVal`, by the same formula for every `F` (junk-valued off `TSP n`, `T2367a`; `BATreeRep` sums it over
`TSP n` only, where `KLIsTSP F` holds, `KLisTSP_of_mem_TSP`).  Its type is `BAGammaType d` of the check file: a
function of the sizes, `M(σ)`, `t`, `F`, `σ`, `a` only. -/
def BAGamma (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) : ℂ :=
  BACactusVal d L M t F σ a

theorem BAGamma_eq (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    BAGamma d L n M t F σ a = BACactusVal d L M t F σ a := rfl

/-- On `F ∈ TSP n` (so `KLIsTSP F`) `BAGamma` is the cactus value. -/
theorem BAGamma_of_mem_TSP (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    {F : Finset (Fin n × Fin n)} (_hF : F ∈ TSP n) (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    BAGamma d L n M t F σ a = BACactusVal d L M t F σ a := rfl

/-! ## 6. API: transport, the value at `F = ∅` and at `n = 3`, orientation -/

section Transport

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- **Transport** (`KLgval_congr`): `BACactusVal` is the generic value of the cactus structure
(`BAslotLeaf`, `BACactusValEdgeW`, `BACactusValSrc`, `BACactusValTgt`), hence it is unchanged by any relabelling
of the slots and of the edges that carries this structure along.  Used in K05 to compare the cactus with the glued
inside and outside cacti of a cut at a chord. -/
theorem BACactusVal_congr (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (F : Finset (Fin n × Fin n))
    (σ : Fin n → Bool) (a : Fin n → Zd d L) {Nd' Ed' : Type*} [Fintype Nd'] [DecidableEq Nd'] [Fintype Ed']
    (eN : BAslot F ≃ Nd') (eE : (↥F ⊕ BAslot F) ≃ Ed') {p' : Fin n → Nd'}
    {E' : Ed' → Matrix (Zd d L) (Zd d L) ℂ} {c' q' : Ed' → Nd'}
    (hp : ∀ v, p' v = eN (BAslotLeaf F v)) (hE : ∀ e, E' (eE e) = BACactusValEdgeW M t F σ e)
    (hc : ∀ e, c' (eE e) = eN (BACactusValSrc F e)) (hq : ∀ e, q' (eE e) = eN (BACactusValTgt F e)) :
    BACactusVal d L M t F σ a = KLgval d L a (BACactusValLeafW M t σ) p' E' c' q' :=
  KLgval_congr eN (Equiv.refl (Fin n)) eE (fun _ => rfl) (fun _ => rfl) hp hE hc hq

end Transport

section Empty

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem BAKCactus_isTSP_empty : KLIsTSP (∅ : Finset (Fin n × Fin n)) :=
  ⟨fun d hd => absurd hd (Finset.notMem_empty d), fun e he => absurd he (Finset.notMem_empty e)⟩

omit [NeZero n] in
private theorem BAKCactus_slot_empty (s : BAslot (∅ : Finset (Fin n × Fin n))) : ∃ w, s = BAslotLeaf ∅ w := by
  rcases s with w | J | J
  · exact ⟨w, rfl⟩
  · exact absurd J.2 (Finset.notMem_empty _)
  · exact absurd J.2 (Finset.notMem_empty _)

private theorem BAKCactus_val_add_one (hn : 2 ≤ n) (v : Fin n) : (v + 1).val = (v.val + 1) % n := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]

/-- **The cycle at `F = ∅`**: the tree is the star, there is one node (the root) and its slots are the `n` leaves
in the order `0, 1, …, n-1`: the successor of the leaf `v` is the leaf `v + 1` (cyclically, `n - 1 ↦ 0`). -/
theorem BAnextSlot_empty (hn : 2 ≤ n) (v : Fin n) :
    BAnextSlot (∅ : Finset (Fin n × Fin n)) (BAslotLeaf ∅ v) = BAslotLeaf ∅ (v + 1) := by
  have hF := BAKCactus_isTSP_empty (n := n)
  have hnode : ∀ w : Fin n, BAslotNode (∅ : Finset (Fin n × Fin n)) (BAslotLeaf ∅ w) = KLwholeP n :=
    fun w => KLleafPar_empty w
  by_cases hv : v.val + 1 < n
  · have hv1 : (v + 1).val = v.val + 1 := by rw [BAKCactus_val_add_one hn, Nat.mod_eq_of_lt hv]
    refine BAnextSlot_eq_of_above hF hn (by rw [hnode, hnode]) ?_ ?_
    · simp only [BAslotStart_leaf, Fin.lt_def, hv1]; omega
    · intro x _ hx
      obtain ⟨w, rfl⟩ := BAKCactus_slot_empty x
      simp only [BAslotStart_leaf, Fin.lt_def, Fin.le_def, hv1] at hx ⊢
      omega
  · have hv0 : v.val + 1 = n := by have := v.isLt; omega
    have hv1 : v + 1 = 0 := Fin.ext (by rw [BAKCactus_val_add_one hn, hv0, Nat.mod_self]; rfl)
    rw [hv1]
    refine BAnextSlot_eq_of_wrap hF hn (by rw [hnode, hnode]) ?_ ?_
    · intro x _
      obtain ⟨w, rfl⟩ := BAKCactus_slot_empty x
      simp only [BAslotStart_leaf, Fin.le_def]
      have := w.isLt
      omega
    · intro x _
      obtain ⟨w, rfl⟩ := BAKCactus_slot_empty x
      simp only [BAslotStart_leaf, Fin.le_def, Fin.val_zero]
      omega

/-- **The charge at `F = ∅`**: the `M`-edge from the leaf `v` to the leaf `v + 1` has the charge `σ_{v+1}`: it lies in
the region of the side `(a_v, a_{v+1})`. -/
theorem BAMcharge_empty (hn : 2 ≤ n) (σ : Fin n → Bool) (v : Fin n) :
    BAMcharge (∅ : Finset (Fin n × Fin n)) σ (BAslotLeaf ∅ v) = σ (v + 1) := by
  simp only [BAMcharge_def, BAnextSlot_empty hn, BAslotStart_leaf]

/-- **The value at `F = ∅`** (the star, one node: the root; closed form, target 5 (b)):
`Γ_M(∅) = ∑_b ∏_v Θ^{(σ_v,σ_{v+1})}(a_v, b_v) ∏_v M(σ_{v+1})_{b_v b_{v+1}}`, `b : Fin n → Zd d L` the labels of the
`n` leaf slots, `M(σ_{v+1})` the `M`-edge from the leaf `v` to the leaf `v + 1`.  Hypothesis: `2 ≤ n`. -/
theorem BACactusVal_empty (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) :
    BACactusVal d L M t (∅ : Finset (Fin n × Fin n)) σ a =
      ∑ b : Fin n → Zd d L, (∏ v, BAThetaOf M t (σ v) (σ (v + 1)) (a v) (b v)) *
        ∏ v, M (σ (v + 1)) (b v) (b (v + 1)) := by
  let e : BAslot (∅ : Finset (Fin n × Fin n)) ≃ Fin n :=
    Equiv.sumEmpty (Fin n) (↥(∅ : Finset (Fin n × Fin n)) ⊕ ↥(∅ : Finset (Fin n × Fin n)))
  let eE : (↥(∅ : Finset (Fin n × Fin n)) ⊕ BAslot (∅ : Finset (Fin n × Fin n))) ≃ Fin n :=
    (Equiv.emptySum _ _).trans e
  refine (BACactusVal_congr M t ∅ σ a e eE (p' := fun v => v) (E' := fun v => M (σ (v + 1)))
    (c' := fun v => v) (q' := fun v => v + 1) (fun _ => rfl) ?_ ?_ ?_).trans rfl
  · intro ed
    rcases ed with J | s
    · exact absurd J.2 (Finset.notMem_empty _)
    · obtain ⟨w, rfl⟩ := BAKCactus_slot_empty s
      change M (σ (w + 1)) = M (BAMcharge ∅ σ (BAslotLeaf ∅ w))
      rw [BAMcharge_empty hn]
  · intro ed
    rcases ed with J | s
    · exact absurd J.2 (Finset.notMem_empty _)
    · rfl
  · intro ed
    rcases ed with J | s
    · exact absurd J.2 (Finset.notMem_empty _)
    · obtain ⟨w, rfl⟩ := BAKCactus_slot_empty s
      change w + 1 = e (BAnextSlot ∅ (BAslotLeaf ∅ w))
      rw [BAnextSlot_empty hn]
      rfl

end Empty

section Three

variable {d L : ℕ} [NeZero L]

private theorem BAKCactus_sum_fin_three {X : Type*} [Fintype X] (f : (Fin 3 → X) → ℂ) :
    ∑ b, f b = ∑ b₀, ∑ b₁, ∑ b₂, f ![b₀, b₁, b₂] := by
  rw [← (Fin.consEquiv (fun _ : Fin 3 => X)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b₀ _ => ?_
  rw [← (Fin.consEquiv (fun _ : Fin 2 => X)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [← (Fin.consEquiv (fun _ : Fin 1 => X)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [Fintype.sum_unique]
  rfl

/-- **`n = 3`: the one-tree formula `(Kn3sol)`** (`1_2:1176`, D634; target 5 (b)).  `TSP 3 = {∅}`, one node with the
three leaf slots in the order `0, 1, 2`:
`Γ_M(∅) = ∑_{b₀,b₁,b₂} Θ^{(σ₀,σ₁)}(a₀,b₀) Θ^{(σ₁,σ₂)}(a₁,b₁) Θ^{(σ₂,σ₀)}(a₂,b₂) · M(σ₀)_{b₂b₀} M(σ₁)_{b₀b₁} M(σ₂)_{b₁b₂}`;
the last factor is `W^{2d} 𝓜^{(3)}_{σ,b} = ∏_i M(σ_i)_{b_{i-1}b_i}` of `(eq:KMloop)` (0-indexed). -/
theorem BACactusVal_three (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin 3 → Bool)
    (a : Fin 3 → Zd d L) :
    BACactusVal d L M t (∅ : Finset (Fin 3 × Fin 3)) σ a =
      ∑ b₀, ∑ b₁, ∑ b₂,
        (BAThetaOf M t (σ 0) (σ 1) (a 0) b₀ * BAThetaOf M t (σ 1) (σ 2) (a 1) b₁ *
          BAThetaOf M t (σ 2) (σ 0) (a 2) b₂) * (M (σ 0) b₂ b₀ * M (σ 1) b₀ b₁ * M (σ 2) b₁ b₂) := by
  rw [BACactusVal_empty (by norm_num) M t σ a, BAKCactus_sum_fin_three]
  refine Finset.sum_congr rfl fun b₀ _ => Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  simp only [Fin.prod_univ_three]
  rw [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

end Three

section Orient

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

private theorem BAKCactus_gval_orient {Nd Lf Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf]
    [Fintype Ed] (a : Lf → Zd d L) (M : Lf → Matrix (Zd d L) (Zd d L) ℂ) (p : Lf → Nd)
    (E : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → Nd) (hE : ∀ e, (E e)ᵀ = E e) (o : Ed → Bool) :
    KLgval d L a M p E c q =
      KLgval d L a M p E (fun e => if o e then q e else c e) (fun e => if o e then c e else q e) := by
  unfold KLgval
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  cases h : o e
  · simp [h]
  · have := congrFun (congrFun (hE e) (b (q e))) (b (c e))
    simpa [h, Matrix.transpose_apply] using this

/-- **Orientation invariance** (target 5 (c)): if every `M(σ)` is symmetric (the block Anderson case: `BAMB_symm`,
`BATheta_isSymm`) then the value does not depend on the orientation chosen for the chords and the `M`-edges: any
set of edges (`o e = true`) may be reversed.  (For non-symmetric `M` the orientation matters; BA is symmetric.) -/
theorem BACactusVal_orient {M : Bool → Matrix (Zd d L) (Zd d L) ℂ} (hM : ∀ σ, (M σ)ᵀ = M σ) (t : ℝ)
    (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) (o : ↥F ⊕ BAslot F → Bool) :
    BACactusVal d L M t F σ a =
      KLgval d L a (BACactusValLeafW M t σ) (BAslotLeaf F) (BACactusValEdgeW M t F σ)
        (fun e => if o e then BACactusValTgt F e else BACactusValSrc F e)
        (fun e => if o e then BACactusValSrc F e else BACactusValTgt F e) := by
  refine BAKCactus_gval_orient _ _ _ _ _ _ (fun e => ?_) o
  rcases e with J | s
  · change ((t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2))ᵀ = (t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)
    rw [Matrix.transpose_smul, BAThetaOf_isSymm hM]
  · exact hM _

end Orient

section Zero

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- `Θ_0 = 1`. -/
theorem BAThetaOf_zero (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (σ₁ σ₂ : Bool) : BAThetaOf M 0 σ₁ σ₂ = 1 := by
  simp [BAThetaOf, PropThetaQ]

/-- At `t = 0` every chord carries `0 · Θ`: the value of every nonempty `F` vanishes. -/
theorem BACactusVal_zero_of_nonempty (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) {F : Finset (Fin n × Fin n)}
    (hF : F.Nonempty) (σ : Fin n → Bool) (a : Fin n → Zd d L) : BACactusVal d L M 0 F σ a = 0 := by
  unfold BACactusVal KLgval
  refine Finset.sum_eq_zero fun b _ => ?_
  obtain ⟨J, hJ⟩ := hF
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ (Sum.inl ⟨J, hJ⟩)) ?_)
  simp [BACactusValEdgeW]

/-- **The value at `F = ∅` and `t = 0`** is the `M`-loop `∏_v M(σ_{v+1})_{a_v a_{v+1}}` of `(eq:KMloop)`. -/
theorem BACactusVal_empty_zero (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) :
    BACactusVal d L M 0 (∅ : Finset (Fin n × Fin n)) σ a = ∏ v, M (σ (v + 1)) (a v) (a (v + 1)) := by
  rw [BACactusVal_empty hn]
  simp only [BAThetaOf_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    obtain ⟨v, hv⟩ := Function.ne_iff.1 hb
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [Ne.symm hv]), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- **`t = 0`: the tree sum is the `M`-loop.**  `∑_{F ∈ TSP n} Γ_M(F)|_{t=0} = ∏_v M(σ_{v+1})_{a_v a_{v+1}}`
(only `F = ∅` survives): the initial condition `𝒦_0 = 𝓜` of `tree-representation_BA`, with the charge convention of
K00 (`BAMLoop_apply`: `σ_i` on `(a_{i-1}, a_i)`). -/
theorem BACactusVal_sum_zero (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) :
    ∑ F ∈ TSP n, BACactusVal d L M 0 F σ a = ∏ v, M (σ (v + 1)) (a v) (a (v + 1)) := by
  rw [Finset.sum_eq_single (∅ : Finset (Fin n × Fin n))]
  · exact BACactusVal_empty_zero hn M σ a
  · intro F _ hF
    exact BACactusVal_zero_of_nonempty M (Finset.nonempty_iff_ne_empty.2 hF) σ a
  · intro h
    exact absurd (empty_mem_TSP n) h

end Zero

section MLoop

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem BAKCactus_getD_ofFn {α : Type*} (f : Fin n → α) (x : α) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i x = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- **`t = 0` against the K00 carrier**: `W^{-d(n-1)} ∑_{F ∈ TSP n} Γ_M(F)|_{t=0} = BAMLoop(σ, a)`, i.e. the charge
convention of the cactus (`BAMcharge`) is that of `BAMLoop_apply` (`σ_i` on `(a_{i-1}, a_i)`), checked in Lean for
every `n ≥ 2`.  This is `BATreeRep` at `t = 0` (`𝒦_0 = 𝓜`, `(eq:initial_K)`). -/
theorem BACactusVal_sum_zero_BAMLoop (hn : 2 ≤ n) (W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, BACactusVal d L M 0 F σ a =
      BAMLoop d L W M (KLloopOf d L σ a) := by
  rw [BACactusVal_sum_zero hn, BAMLoop_apply d L W M (KLloopOf d L σ a) n (by omega)
    (by simp [KLloopOf]) (by simp [KLloopOf])]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun i => M ((KLloopOf d L σ a).σ.getD i false)
    ((KLloopOf d L σ a).a.getD ((i + (n - 1)) % n) 0) ((KLloopOf d L σ a).a.getD i 0)) n]
  refine Fintype.prod_equiv (Equiv.addRight (1 : Fin n)) _ _ fun v => ?_
  have h1 : (v + 1).val = (v.val + 1) % n := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h2 : ((v + 1).val + (n - 1)) % n = v.val := by
    rw [h1]
    by_cases hv : v.val + 1 < n
    · rw [Nat.mod_eq_of_lt hv, show v.val + 1 + (n - 1) = v.val + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt v.isLt]
    · have hv0 : v.val + 1 = n := by have := v.isLt; omega
      rw [hv0, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
  simp only [Equiv.coe_addRight, KLloopOf]
  rw [h2, BAKCactus_getD_ofFn σ false _ (v + 1).isLt, BAKCactus_getD_ofFn a 0 _ (v + 1).isLt,
    BAKCactus_getD_ofFn a 0 _ v.isLt]

/-- **`(Kn3sol)` against the K00 carrier** (`1_2:1176`): `W^{-2d} Γ_M(∅) = ∑_b ∏_k Θ^{(σ_k,σ_{k+1})}(a_k, b_k) ·
𝓜^{(3)}_{σ,b}` with `𝓜^{(3)} = BAMLoop` (`(eq:KMloop)`, `BAMLoop_apply`).  Since `TSP 3 = {∅}` the left side is
`W^{-d(n-1)} ∑_{F ∈ TSP 3} Γ_M(F)` of `BATreeRep` at `n = 3`. -/
theorem BACactusVal_three_BAMLoop (W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin 3 → Bool)
    (a : Fin 3 → Zd d L) :
    (((W : ℂ) ^ d)⁻¹) ^ 2 * BACactusVal d L M t (∅ : Finset (Fin 3 × Fin 3)) σ a =
      ∑ b₀, ∑ b₁, ∑ b₂,
        BAThetaOf M t (σ 0) (σ 1) (a 0) b₀ * BAThetaOf M t (σ 1) (σ 2) (a 1) b₁ *
          BAThetaOf M t (σ 2) (σ 0) (a 2) b₂ * BAMLoop d L W M (KLloopOf d L σ ![b₀, b₁, b₂]) := by
  rw [BACactusVal_three, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₀ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [BAMLoop_apply d L W M (KLloopOf d L σ ![b₀, b₁, b₂]) 3 (by norm_num) (by simp [KLloopOf])
    (by simp [KLloopOf])]
  simp [KLloopOf, Finset.prod_range_succ, List.getD_eq_getElem?_getD, List.ofFn_succ]
  ring

end MLoop

/-! ## 7. Compiled nonempty instances

Datum of the loop part: `d = 1`, `L = 3` and `M = BAMLoop_witM` of K00 (`BA/KBase.lean:102`: symmetric `3 × 3`
matrices with distinct entries; `W = 1`), the sign vectors `σ = (+,+,-)` at `n = 3` and `σ = (+,+,-,+)` at `n = 4`, the
labels `a = (0,1,2)` resp. `(0,1,2,1)`; `n = 4` has the three trees `∅`, `{(0,2)}`, `{(1,3)}` (`TSP_four`).  At
`t = 0` the chords carry `0 · Θ`, so only `F = ∅` survives and the tree sum is the `M`-loop, `BAMLoop`.  Datum of the
symmetry part: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`), `t = 1/2`. -/

namespace KCactusInst

open RBM.BA.MFixedPointInst

/-- The slot type carries `Fintype` and `DecidableEq`. -/
example (F : Finset (Fin 4 × Fin 4)) : Fintype (BAslot F) := inferInstance

example (F : Finset (Fin 4 × Fin 4)) : DecidableEq (BAslot F) := inferInstance

/-- The slot count at `n = 4`, `F = {(0,2)}`: `4 + 2 · 1 = 6` slots. -/
example : Fintype.card (BAslot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4))) = 6 := by
  rw [BAslot_card]; rfl

private theorem BAKCactus_F02 : KLIsTSP ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) :=
  KLisTSP_of_mem_TSP (by rw [TSP_four]; simp)

private theorem BAKCactus_F13 : KLIsTSP ({((1 : Fin 4), (3 : Fin 4))} : Finset (Fin 4 × Fin 4)) :=
  KLisTSP_of_mem_TSP (by rw [TSP_four]; simp)

/-- The tree sum at `t = 0`, `n = 3`, equals `BAMLoop_witness = 15` (K00): `TSP 3 = {∅}`. -/
example : ∑ F ∈ TSP 3, BACactusVal 1 3 BAMLoop_witM 0 F ![true, true, false] ![![0], ![1], ![2]] = 15 := by
  have h := BACactusVal_sum_zero_BAMLoop (d := 1) (L := 3) (n := 3) (by norm_num) 1 BAMLoop_witM
    ![true, true, false] ![![0], ![1], ![2]]
  have hl : KLloopOf 1 3 ![true, true, false] ![![0], ![1], ![2]] =
      (⟨[true, true, false], [![0], ![1], ![2]]⟩ : LoopIdx (Zd 1 3)) := rfl
  rw [hl, BAMLoop_witness] at h
  simpa using h

/-- `n = 4`, the star `F = ∅`, `t = 0`: `Γ_M(∅) = M(+)_{01} M(-)_{12} M(+)_{21} M(+)_{10} = 1 · 5 · 2 · 1 = 10 ≠ 0`
(the `M`-loop, `BAMLoop_apply`). -/
example : BACactusVal 1 3 BAMLoop_witM 0 (∅ : Finset (Fin 4 × Fin 4)) ![true, true, false, true]
    ![![0], ![1], ![2], ![1]] = 10 := by
  rw [BACactusVal_empty_zero (by norm_num), Fin.prod_univ_four]
  have h1 : BAMLoop_witM true (![0] : Zd 1 3) ![1] = 1 := rfl
  have h2 : BAMLoop_witM false (![1] : Zd 1 3) ![2] = 5 := rfl
  have h3 : BAMLoop_witM true (![2] : Zd 1 3) ![1] = 2 := rfl
  have h4 : BAMLoop_witM true (![1] : Zd 1 3) ![0] = 1 := rfl
  change BAMLoop_witM true ![0] ![1] * BAMLoop_witM false ![1] ![2] * BAMLoop_witM true ![2] ![1] *
    BAMLoop_witM true ![1] ![0] = 10
  rw [h1, h2, h3, h4]; norm_num

/-- `n = 4`, `t = 0`: the three trees `∅`, `{(0,2)}`, `{(1,3)}` (each `KLIsTSP`); the two diagonals carry `0 · Θ`
and vanish, the star carries the whole `M`-loop `= 10` (`BAGamma` is the cactus value). -/
example : BAGamma 1 3 4 BAMLoop_witM 0 {((0 : Fin 4), (2 : Fin 4))} ![true, true, false, true]
    ![![0], ![1], ![2], ![1]] = 0 :=
  BACactusVal_zero_of_nonempty BAMLoop_witM ⟨_, Finset.mem_singleton_self _⟩ _ _

example : BAGamma 1 3 4 BAMLoop_witM 0 {((1 : Fin 4), (3 : Fin 4))} ![true, true, false, true]
    ![![0], ![1], ![2], ![1]] = 0 :=
  BACactusVal_zero_of_nonempty BAMLoop_witM ⟨_, Finset.mem_singleton_self _⟩ _ _

example : ∑ F ∈ TSP 4, BAGamma 1 3 4 BAMLoop_witM 0 F ![true, true, false, true] ![![0], ![1], ![2], ![1]] = 10 := by
  have h := BACactusVal_sum_zero_BAMLoop (d := 1) (L := 3) (n := 4) (by norm_num) 1 BAMLoop_witM
    ![true, true, false, true] ![![0], ![1], ![2], ![1]]
  have hl : KLloopOf 1 3 ![true, true, false, true] ![![0], ![1], ![2], ![1]] =
      (⟨[true, true, false, true], [![0], ![1], ![2], ![1]]⟩ : LoopIdx (Zd 1 3)) := rfl
  have hm := BAMLoop_apply 1 3 1 BAMLoop_witM ⟨[true, true, false, true], [![0], ![1], ![2], ![1]]⟩ 4
    (by norm_num) rfl rfl
  rw [hl, hm] at h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at h
  have h1 : BAMLoop_witM true (![1] : Zd 1 3) ![0] = 1 := rfl
  have h2 : BAMLoop_witM true (![0] : Zd 1 3) ![1] = 1 := rfl
  have h3 : BAMLoop_witM false (![1] : Zd 1 3) ![2] = 5 := rfl
  have h4 : BAMLoop_witM true (![2] : Zd 1 3) ![1] = 2 := rfl
  change _ = (((1 : ℕ) : ℂ) ^ 1)⁻¹ ^ (4 - 1) * (1 * BAMLoop_witM true ![1] ![0] * BAMLoop_witM true ![0] ![1] *
    BAMLoop_witM false ![1] ![2] * BAMLoop_witM true ![2] ![1]) at h
  rw [h1, h2, h3, h4] at h
  norm_num at h
  exact h

/-! ### The slots and cycles of `F = {(0,2)}`, `n = 4` (two nodes, six slots; paper figure `A:552-583`) -/

private abbrev BAKCactus_F02set : Finset (Fin 4 × Fin 4) := {((0 : Fin 4), (2 : Fin 4))}

private theorem BAKCactus_F02mem : ((0 : Fin 4), (2 : Fin 4)) ∈ BAKCactus_F02set :=
  Finset.mem_singleton_self _

private theorem BAKCactus_leafPar0 : KLleafPar BAKCactus_F02set 0 = ((0 : Fin 4), (2 : Fin 4)) :=
  KLleafPar_eq (by decide) (by decide) (by decide)

private theorem BAKCactus_leafPar1 : KLleafPar BAKCactus_F02set 1 = ((0 : Fin 4), (2 : Fin 4)) :=
  KLleafPar_eq (by decide) (by decide) (by decide)

private theorem BAKCactus_leafPar2 : KLleafPar BAKCactus_F02set 2 = KLwholeP 4 :=
  KLleafPar_eq (KLwholeP_mem_nodes _) (by decide) (by decide)

private theorem BAKCactus_leafPar3 : KLleafPar BAKCactus_F02set 3 = KLwholeP 4 :=
  KLleafPar_root _ rfl

private theorem BAKCactus_nodePar02 : KLnodePar BAKCactus_F02set ((0 : Fin 4), (2 : Fin 4)) = KLwholeP 4 :=
  KLnodePar_eq (by decide) (KLwholeP_mem_nodes _) (KLarcLe_wholeP _) (by decide) (by decide)

/-- A computable model of the node of a slot of `F = {(0,2)}`. -/
private def BAKCactus_nodeM : BAslot BAKCactus_F02set → Fin 4 × Fin 4
  | Sum.inl v => if v.val < 2 then (0, 2) else (0, 3)
  | Sum.inr (Sum.inl _) => (0, 3)
  | Sum.inr (Sum.inr _) => (0, 2)

private theorem BAKCactus_nodeM_eq : BAslotNode BAKCactus_F02set = BAKCactus_nodeM := by
  funext s
  rcases s with v | J | J
  · fin_cases v
    · exact BAKCactus_leafPar0
    · exact BAKCactus_leafPar1
    · exact BAKCactus_leafPar2
    · exact BAKCactus_leafPar3
  · obtain ⟨J, hJ⟩ := J
    obtain rfl := Finset.mem_singleton.1 hJ
    exact BAKCactus_nodePar02
  · obtain ⟨J, hJ⟩ := J
    obtain rfl := Finset.mem_singleton.1 hJ
    rfl

/-- The successor table of `F = {(0,2)}` (the cycles of the figure, `A:552-583`): the root `(0,3)` is the cycle
`out(0,2) → leaf 2 → leaf 3 → out(0,2)`, the node `(0,2)` is the cycle `leaf 0 → leaf 1 → in(0,2) → leaf 0`. -/
private def BAKCactus_nextM : BAslot BAKCactus_F02set → BAslot BAKCactus_F02set
  | Sum.inl v => if v.val = 0 then Sum.inl 1 else if v.val = 1 then Sum.inr (Sum.inr ⟨_, BAKCactus_F02mem⟩)
      else if v.val = 2 then Sum.inl 3 else Sum.inr (Sum.inl ⟨_, BAKCactus_F02mem⟩)
  | Sum.inr (Sum.inl _) => Sum.inl 2
  | Sum.inr (Sum.inr _) => Sum.inl 0

private theorem BAKCactus_tableM : ∀ s : BAslot BAKCactus_F02set,
    BAKCactus_nodeM (BAKCactus_nextM s) = BAKCactus_nodeM s ∧
      ((BAslotStart _ s < BAslotStart _ (BAKCactus_nextM s) ∧
          ∀ x, BAKCactus_nodeM x = BAKCactus_nodeM s → BAslotStart _ s < BAslotStart _ x →
            BAslotStart _ (BAKCactus_nextM s) ≤ BAslotStart _ x) ∨
        ((∀ x, BAKCactus_nodeM x = BAKCactus_nodeM s → BAslotStart _ x ≤ BAslotStart _ s) ∧
          ∀ x, BAKCactus_nodeM x = BAKCactus_nodeM s → BAslotStart _ (BAKCactus_nextM s) ≤ BAslotStart _ x)) := by
  decide

private theorem BAKCactus_next_eq (s : BAslot BAKCactus_F02set) :
    BAnextSlot BAKCactus_F02set s = BAKCactus_nextM s := by
  obtain ⟨hnode, h | h⟩ := BAKCactus_tableM s
  · rw [← BAKCactus_nodeM_eq] at hnode h
    exact BAnextSlot_eq_of_above BAKCactus_F02 (by norm_num) hnode h.1 h.2
  · rw [← BAKCactus_nodeM_eq] at hnode h
    exact BAnextSlot_eq_of_wrap BAKCactus_F02 (by norm_num) hnode h.1 h.2

/-- The two cycles of `F = {(0,2)}`, computed: the root `(0,3)` is `out(0,2) → leaf 2 → leaf 3 → out(0,2)`, the node
`(0,2)` is `leaf 0 → leaf 1 → in(0,2) → leaf 0`. -/
example :
    BAnextSlot BAKCactus_F02set (BAslotOut _ ⟨_, BAKCactus_F02mem⟩) = BAslotLeaf _ 2 ∧
    BAnextSlot BAKCactus_F02set (BAslotLeaf _ 2) = BAslotLeaf _ 3 ∧
    BAnextSlot BAKCactus_F02set (BAslotLeaf _ 3) = BAslotOut _ ⟨_, BAKCactus_F02mem⟩ ∧
    BAnextSlot BAKCactus_F02set (BAslotLeaf _ 0) = BAslotLeaf _ 1 ∧
    BAnextSlot BAKCactus_F02set (BAslotLeaf _ 1) = BAslotIn _ ⟨_, BAKCactus_F02mem⟩ ∧
    BAnextSlot BAKCactus_F02set (BAslotIn _ ⟨_, BAKCactus_F02mem⟩) = BAslotLeaf _ 0 := by
  simp only [BAKCactus_next_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The charges of the six `M`-edges of `F = {(0,2)}` (D633: `σ_x`, `x` the first vertex of the next range), as in the
figure of `A:552-583`: `M(σ_2), M(σ_3), M(σ_0)` on the root cycle, `M(σ_1), M(σ_2), M(σ_0)` on the node cycle. -/
example (σ : Fin 4 → Bool) :
    BAMcharge BAKCactus_F02set σ (BAslotOut _ ⟨_, BAKCactus_F02mem⟩) = σ 2 ∧
    BAMcharge BAKCactus_F02set σ (BAslotLeaf _ 2) = σ 3 ∧
    BAMcharge BAKCactus_F02set σ (BAslotLeaf _ 3) = σ 0 ∧
    BAMcharge BAKCactus_F02set σ (BAslotLeaf _ 0) = σ 1 ∧
    BAMcharge BAKCactus_F02set σ (BAslotLeaf _ 1) = σ 2 ∧
    BAMcharge BAKCactus_F02set σ (BAslotIn _ ⟨_, BAKCactus_F02mem⟩) = σ 0 := by
  simp only [BAMcharge_def, BAKCactus_next_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two nodes, two cycles: `leaf 0` and `in(0,2)` lie in one cycle, `leaf 0` and `leaf 2` do not
(`BAnextSlot_orbit`). -/
example : (∃ k : ℕ, (BAnextSlot BAKCactus_F02set)^[k] (BAslotLeaf _ 0) = BAslotIn _ ⟨_, BAKCactus_F02mem⟩) ∧
    ¬ ∃ k : ℕ, (BAnextSlot BAKCactus_F02set)^[k] (BAslotLeaf _ 0) = BAslotLeaf _ 2 := by
  refine ⟨(BAnextSlot_orbit BAKCactus_F02 (by norm_num) _ _).1 ?_, fun h => ?_⟩
  · rw [BAKCactus_nodeM_eq]; rfl
  · have := (BAnextSlot_orbit BAKCactus_F02 (by norm_num) _ _).2 h
    rw [BAKCactus_nodeM_eq] at this
    exact absurd this (by decide)

/-- The same in Mathlib's terms: the permutation `BAnextSlotPerm` of the six slots has exactly two cycles. -/
example : (BAnextSlotPerm BAKCactus_F02 (by norm_num : 2 ≤ 4)).SameCycle (BAslotLeaf _ 0)
      (BAslotIn _ ⟨_, BAKCactus_F02mem⟩) ∧
    ¬ (BAnextSlotPerm BAKCactus_F02 (by norm_num : 2 ≤ 4)).SameCycle (BAslotLeaf _ 0) (BAslotLeaf _ 2) := by
  refine ⟨(BAnextSlot_sameCycle_iff BAKCactus_F02 (by norm_num) _ _).2 ?_, fun h => ?_⟩
  · rw [BAKCactus_nodeM_eq]; rfl
  · have := (BAnextSlot_sameCycle_iff BAKCactus_F02 (by norm_num) _ _).1 h
    rw [BAKCactus_nodeM_eq] at this
    exact absurd this (by decide)

example : Function.Bijective (BAnextSlot BAKCactus_F02set) := BAnextSlot_bijective BAKCactus_F02 (by norm_num)

example : ∀ s t : BAslot BAKCactus_F02set, BAslotNode _ s = BAslotNode _ t → BAslotStart _ s = BAslotStart _ t →
    s = t := fun _ _ h1 h2 => BAslot_start_inj BAKCactus_F02 (by norm_num) h1 h2

/-! ### The slots and cycles of `F = {(1,3)}`, `n = 4` (the diagonal in the middle of the root cycle) -/

private abbrev BAKCactus_F13set : Finset (Fin 4 × Fin 4) := {((1 : Fin 4), (3 : Fin 4))}

private theorem BAKCactus_F13mem : ((1 : Fin 4), (3 : Fin 4)) ∈ BAKCactus_F13set :=
  Finset.mem_singleton_self _

private theorem BAKCactus_leafPar13_0 : KLleafPar BAKCactus_F13set 0 = KLwholeP 4 :=
  KLleafPar_eq (KLwholeP_mem_nodes _) (by decide) (by decide)

private theorem BAKCactus_leafPar13_1 : KLleafPar BAKCactus_F13set 1 = ((1 : Fin 4), (3 : Fin 4)) :=
  KLleafPar_eq (by decide) (by decide) (by decide)

private theorem BAKCactus_leafPar13_2 : KLleafPar BAKCactus_F13set 2 = ((1 : Fin 4), (3 : Fin 4)) :=
  KLleafPar_eq (by decide) (by decide) (by decide)

private theorem BAKCactus_leafPar13_3 : KLleafPar BAKCactus_F13set 3 = KLwholeP 4 :=
  KLleafPar_root _ rfl

private theorem BAKCactus_nodePar13 : KLnodePar BAKCactus_F13set ((1 : Fin 4), (3 : Fin 4)) = KLwholeP 4 :=
  KLnodePar_eq (by decide) (KLwholeP_mem_nodes _) (KLarcLe_wholeP _) (by decide) (by decide)

private def BAKCactus_nodeM13 : BAslot BAKCactus_F13set → Fin 4 × Fin 4
  | Sum.inl v => if v.val = 1 ∨ v.val = 2 then (1, 3) else (0, 3)
  | Sum.inr (Sum.inl _) => (0, 3)
  | Sum.inr (Sum.inr _) => (1, 3)

private theorem BAKCactus_nodeM13_eq : BAslotNode BAKCactus_F13set = BAKCactus_nodeM13 := by
  funext s
  rcases s with v | J | J
  · fin_cases v
    · exact BAKCactus_leafPar13_0
    · exact BAKCactus_leafPar13_1
    · exact BAKCactus_leafPar13_2
    · exact BAKCactus_leafPar13_3
  · obtain ⟨J, hJ⟩ := J
    obtain rfl := Finset.mem_singleton.1 hJ
    exact BAKCactus_nodePar13
  · obtain ⟨J, hJ⟩ := J
    obtain rfl := Finset.mem_singleton.1 hJ
    rfl

/-- The successor table of `F = {(1,3)}`: the root `(0,3)` is `leaf 0 → out(1,3) → leaf 3 → leaf 0`, the node `(1,3)`
is `leaf 1 → leaf 2 → in(1,3) → leaf 1`. -/
private def BAKCactus_nextM13 : BAslot BAKCactus_F13set → BAslot BAKCactus_F13set
  | Sum.inl v => if v.val = 0 then Sum.inr (Sum.inl ⟨_, BAKCactus_F13mem⟩) else if v.val = 1 then Sum.inl 2
      else if v.val = 2 then Sum.inr (Sum.inr ⟨_, BAKCactus_F13mem⟩) else Sum.inl 0
  | Sum.inr (Sum.inl _) => Sum.inl 3
  | Sum.inr (Sum.inr _) => Sum.inl 1

private theorem BAKCactus_tableM13 : ∀ s : BAslot BAKCactus_F13set,
    BAKCactus_nodeM13 (BAKCactus_nextM13 s) = BAKCactus_nodeM13 s ∧
      ((BAslotStart _ s < BAslotStart _ (BAKCactus_nextM13 s) ∧
          ∀ x, BAKCactus_nodeM13 x = BAKCactus_nodeM13 s → BAslotStart _ s < BAslotStart _ x →
            BAslotStart _ (BAKCactus_nextM13 s) ≤ BAslotStart _ x) ∨
        ((∀ x, BAKCactus_nodeM13 x = BAKCactus_nodeM13 s → BAslotStart _ x ≤ BAslotStart _ s) ∧
          ∀ x, BAKCactus_nodeM13 x = BAKCactus_nodeM13 s →
            BAslotStart _ (BAKCactus_nextM13 s) ≤ BAslotStart _ x)) := by
  decide

private theorem BAKCactus_next13_eq (s : BAslot BAKCactus_F13set) :
    BAnextSlot BAKCactus_F13set s = BAKCactus_nextM13 s := by
  obtain ⟨hnode, h | h⟩ := BAKCactus_tableM13 s
  · rw [← BAKCactus_nodeM13_eq] at hnode h
    exact BAnextSlot_eq_of_above BAKCactus_F13 (by norm_num) hnode h.1 h.2
  · rw [← BAKCactus_nodeM13_eq] at hnode h
    exact BAnextSlot_eq_of_wrap BAKCactus_F13 (by norm_num) hnode h.1 h.2

/-- The two cycles of `F = {(1,3)}` and their charges (figure of `A:552-583`, D633): the root cycle
`leaf 0 -M(σ_1)→ out(1,3) -M(σ_3)→ leaf 3 -M(σ_0)→ leaf 0`, the node cycle
`leaf 1 -M(σ_2)→ leaf 2 -M(σ_3)→ in(1,3) -M(σ_1)→ leaf 1`. -/
example (σ : Fin 4 → Bool) :
    (BAnextSlot BAKCactus_F13set (BAslotLeaf _ 0) = BAslotOut _ ⟨_, BAKCactus_F13mem⟩ ∧
      BAnextSlot BAKCactus_F13set (BAslotOut _ ⟨_, BAKCactus_F13mem⟩) = BAslotLeaf _ 3 ∧
      BAnextSlot BAKCactus_F13set (BAslotLeaf _ 3) = BAslotLeaf _ 0 ∧
      BAnextSlot BAKCactus_F13set (BAslotLeaf _ 1) = BAslotLeaf _ 2 ∧
      BAnextSlot BAKCactus_F13set (BAslotLeaf _ 2) = BAslotIn _ ⟨_, BAKCactus_F13mem⟩ ∧
      BAnextSlot BAKCactus_F13set (BAslotIn _ ⟨_, BAKCactus_F13mem⟩) = BAslotLeaf _ 1) ∧
    (BAMcharge BAKCactus_F13set σ (BAslotLeaf _ 0) = σ 1 ∧
      BAMcharge BAKCactus_F13set σ (BAslotOut _ ⟨_, BAKCactus_F13mem⟩) = σ 3 ∧
      BAMcharge BAKCactus_F13set σ (BAslotLeaf _ 3) = σ 0 ∧
      BAMcharge BAKCactus_F13set σ (BAslotLeaf _ 1) = σ 2 ∧
      BAMcharge BAKCactus_F13set σ (BAslotLeaf _ 2) = σ 3 ∧
      BAMcharge BAKCactus_F13set σ (BAslotIn _ ⟨_, BAKCactus_F13mem⟩) = σ 1) := by
  simp only [BAMcharge_def, BAKCactus_next13_eq]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

example : Function.Bijective (BAnextSlot BAKCactus_F13set) := BAnextSlot_bijective BAKCactus_F13 (by norm_num)

/-! ### The API lemmas at the data -/

/-- `BAThetaOf_BAMsigma`, `BAMssOf_BAMsigma` at the block Anderson flow point `P` of `(d, L) = (3, 4)`, `t = 1/2`:
`Γ` of `BATreeRep` is a function of `(Bool → Matrix, t)` only. -/
example : BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) true false =
    BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false := BAThetaOf_BAMsigma P.g0 P.E P.m0 (1 / 2) true false

example : BAMssOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) true false =
    BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true false := BAMssOf_BAMsigma _ true false

/-- The block Anderson `M(σ) = BAMsigma (BAMB ..) σ` is symmetric (`BAMB_symm`): the hypothesis of the symmetry
lemmas, discharged at `P`. -/
private theorem BAKCactus_Msym : ∀ σ, (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ)ᵀ =
    BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ := by
  intro σ
  ext a b
  cases σ
  · simp only [Matrix.transpose_apply, BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply,
      BAMB_symm 3 4 P.g0 (P.E : ℂ) P.m0 a b]
  · exact BAMB_symm 3 4 P.g0 (P.E : ℂ) P.m0 b a

example : (BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) true false)ᵀ =
    BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) true false :=
  BAThetaOf_isSymm BAKCactus_Msym (1 / 2) true false

example : (BAMssOf BAMLoop_witM true false)ᵀ = BAMssOf BAMLoop_witM true false :=
  BAMssOf_isSymm RBM.BA.KBaseInst.witM_symm true false

/-- `BACactusVal_orient` at the block Anderson data `P`, `t = 1/2`, `n = 4`, `F = {(0,2)}`: every edge reversed. -/
example : BACactusVal 3 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) BAKCactus_F02set
    ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] =
    KLgval 3 4 ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]
      (BACactusValLeafW (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true])
      (BAslotLeaf _)
      (BACactusValEdgeW (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) BAKCactus_F02set ![true, true, false, true])
      (fun e => BACactusValTgt _ e) (fun e => BACactusValSrc _ e) :=
  BACactusVal_orient BAKCactus_Msym (1 / 2) _ _ _ (fun _ => true)

/-- `BACactusVal_orient` at the K00 witness (symmetric), `F = {(1,3)}`: the `M`-edges are reversed, the chord is kept. -/
example : BACactusVal 1 3 BAMLoop_witM (1 / 10) BAKCactus_F13set ![true, true, false, true] ![![0], ![1], ![2], ![1]] =
    KLgval 1 3 ![![0], ![1], ![2], ![1]] (BACactusValLeafW BAMLoop_witM (1 / 10) ![true, true, false, true])
      (BAslotLeaf _) (BACactusValEdgeW BAMLoop_witM (1 / 10) BAKCactus_F13set ![true, true, false, true])
      (fun e => if e.isRight then BACactusValTgt _ e else BACactusValSrc _ e)
      (fun e => if e.isRight then BACactusValSrc _ e else BACactusValTgt _ e) :=
  BACactusVal_orient RBM.BA.KBaseInst.witM_symm (1 / 10) _ _ _ (fun e => e.isRight)

/-- `BACactusVal_congr` with a nontrivial relabelling: the six slots of `F = {(0,2)}` are numbered by `Fin 6` and its
seven edges (one chord, six `M`-edges) by `Fin 7`. -/
example :
    let eN : BAslot BAKCactus_F02set ≃ Fin 6 := Fintype.equivFinOfCardEq (by rw [BAslot_card]; rfl)
    let eE : (↥BAKCactus_F02set ⊕ BAslot BAKCactus_F02set) ≃ Fin 7 :=
      Fintype.equivFinOfCardEq (by simp [Fintype.card_sum])
    BACactusVal 1 3 BAMLoop_witM (1 / 10) BAKCactus_F02set ![true, true, false, true] ![![0], ![1], ![2], ![1]] =
      KLgval 1 3 ![![0], ![1], ![2], ![1]] (BACactusValLeafW BAMLoop_witM (1 / 10) ![true, true, false, true])
        (fun v => eN (BAslotLeaf _ v))
        (fun e => BACactusValEdgeW BAMLoop_witM (1 / 10) BAKCactus_F02set ![true, true, false, true] (eE.symm e))
        (fun e => eN (BACactusValSrc _ (eE.symm e))) (fun e => eN (BACactusValTgt _ (eE.symm e))) := by
  intro eN eE
  exact BACactusVal_congr BAMLoop_witM (1 / 10) _ _ _ eN eE (fun _ => rfl) (fun e => by simp)
    (fun e => by simp) (fun e => by simp)

/-- `BACactusVal_empty` at `n = 4` and `BACactusVal_three` (the one-tree formula `(Kn3sol)`), `t = 1/10`. -/
example : BACactusVal 1 3 BAMLoop_witM (1 / 10) (∅ : Finset (Fin 4 × Fin 4)) ![true, true, false, true]
    ![![0], ![1], ![2], ![1]] =
    ∑ b : Fin 4 → Zd 1 3, (∏ v, BAThetaOf BAMLoop_witM (1 / 10) (![true, true, false, true] v)
        (![true, true, false, true] (v + 1)) (![![0], ![1], ![2], ![1]] v) (b v)) *
      ∏ v, BAMLoop_witM (![true, true, false, true] (v + 1)) (b v) (b (v + 1)) :=
  BACactusVal_empty (by norm_num) _ _ _ _

example : BACactusVal 1 3 BAMLoop_witM (1 / 10) (∅ : Finset (Fin 3 × Fin 3)) ![true, true, false]
    ![![0], ![1], ![2]] =
    ∑ b₀, ∑ b₁, ∑ b₂,
      (BAThetaOf BAMLoop_witM (1 / 10) true true ![0] b₀ * BAThetaOf BAMLoop_witM (1 / 10) true false ![1] b₁ *
        BAThetaOf BAMLoop_witM (1 / 10) false true ![2] b₂) *
      (BAMLoop_witM true b₂ b₀ * BAMLoop_witM true b₀ b₁ * BAMLoop_witM false b₁ b₂) :=
  BACactusVal_three BAMLoop_witM (1 / 10) _ _

/-- `(Kn3sol)` against the K00 carrier at `W = 1`. -/
example : (((1 : ℕ) : ℂ) ^ 1)⁻¹ ^ 2 * BACactusVal 1 3 BAMLoop_witM (1 / 10) (∅ : Finset (Fin 3 × Fin 3))
    ![true, true, false] ![![0], ![1], ![2]] =
    ∑ b₀, ∑ b₁, ∑ b₂, BAThetaOf BAMLoop_witM (1 / 10) true true ![0] b₀ *
      BAThetaOf BAMLoop_witM (1 / 10) true false ![1] b₁ * BAThetaOf BAMLoop_witM (1 / 10) false true ![2] b₂ *
        BAMLoop 1 3 1 BAMLoop_witM (KLloopOf 1 3 ![true, true, false] ![b₀, b₁, b₂]) :=
  BACactusVal_three_BAMLoop 1 BAMLoop_witM (1 / 10) _ _

example : BAGamma 1 3 3 BAMLoop_witM (1 / 10) ∅ ![true, true, false] ![![0], ![1], ![2]] =
    BACactusVal 1 3 BAMLoop_witM (1 / 10) ∅ ![true, true, false] ![![0], ![1], ![2]] :=
  BAGamma_of_mem_TSP 1 3 3 BAMLoop_witM (1 / 10) (by rw [TSP_three]; simp) _ _

/-- The star at `n = 4` (one node, four leaf slots in the order `0, 1, 2, 3`, wrapping `3 ↦ 0`) and its charges
(`σ_{v+1}` on the `M`-edge from the leaf `v`). -/
example : BAnextSlot (∅ : Finset (Fin 4 × Fin 4)) (BAslotLeaf _ 3) = BAslotLeaf _ 0 :=
  BAnextSlot_empty (by norm_num) 3

example : BAnextSlot (∅ : Finset (Fin 4 × Fin 4)) (BAslotLeaf _ 1) = BAslotLeaf _ 2 :=
  BAnextSlot_empty (by norm_num) 1

example (σ : Fin 4 → Bool) : BAMcharge (∅ : Finset (Fin 4 × Fin 4)) σ (BAslotLeaf _ 3) = σ 0 :=
  BAMcharge_empty (by norm_num) σ 3

/-- Generic facts of `BAnextSlot` at the leaf `1` of `F = {(0,2)}`: it stays in the node, and it is the least start above
(`BAnextSlot_spec`, `BAslotNode_nextSlot`, `BAslotNode_mem_nodes`, injectivity). -/
example : BAslotNode BAKCactus_F02set (BAnextSlot BAKCactus_F02set (BAslotLeaf _ 1)) =
    KLleafPar BAKCactus_F02set 1 := BAslotNode_nextSlot _ _

example : BAslotStart _ (BAslotLeaf BAKCactus_F02set 1) <
    BAslotStart _ (BAnextSlot BAKCactus_F02set (BAslotLeaf _ 1)) := by
  rcases BAnextSlot_spec BAKCactus_F02set (BAslotLeaf _ 1) with ⟨h, -⟩ | ⟨hmax, -⟩
  · exact h
  · have := hmax (BAslotIn _ ⟨_, BAKCactus_F02mem⟩) (by rw [BAKCactus_nodeM_eq]; rfl)
    exact absurd this (by decide)

example : BAslotNode BAKCactus_F02set (BAslotLeaf _ 3) ∈ KLnodes BAKCactus_F02set := BAslotNode_mem_nodes _ _

example : Function.Injective (BAnextSlot BAKCactus_F13set) := BAnextSlot_injective BAKCactus_F13 (by norm_num)

/-- `Θ_0 = 1`, `BACactusVal_empty_zero` and `BACactusVal_zero_of_nonempty` at the witness. -/
example : BAThetaOf BAMLoop_witM 0 true false = 1 := BAThetaOf_zero _ _ _

example : BACactusVal 1 3 BAMLoop_witM 0 (∅ : Finset (Fin 3 × Fin 3)) ![true, true, false] ![![0], ![1], ![2]] = 15 := by
  rw [BACactusVal_empty_zero (by norm_num), Fin.prod_univ_three]
  have h1 : BAMLoop_witM true (![0] : Zd 1 3) ![1] = 1 := rfl
  have h2 : BAMLoop_witM false (![1] : Zd 1 3) ![2] = 5 := rfl
  have h3 : BAMLoop_witM true (![2] : Zd 1 3) ![0] = 3 := rfl
  change BAMLoop_witM true ![0] ![1] * BAMLoop_witM false ![1] ![2] * BAMLoop_witM true ![2] ![0] = 15
  rw [h1, h2, h3]; norm_num

/-! ### A chord tree with `t ≠ 0` and a nonzero value: the directed datum

`M(σ)_{xy} = 1(y = x + 1)` on `Z_3` (the directed 3-cycle, not symmetric): `M^{(σ₁σ₂)} = 0`, so `Θ_t^{(σ₁σ₂)} = 1` for
every `t` and the value of `F = {(0,2)}` at `n = 4` counts the labels `b` of the six slots with `b(leaf v) = a_v`, the
chord `b(in J) = b(out J)` (weight `t`) and every `M`-edge `s → BAnextSlot s` going from `x` to `x + 1`.  For
`a = (0,1,0,1)` the root cycle `out → leaf 2 → leaf 3 → out` reads `b_out → 0 → 1 → b_out`, the node cycle
`leaf 0 → leaf 1 → in → leaf 0` reads `0 → 1 → b_in → 0`: the only solution is `b_out = b_in = 2`, so the value is `t`. -/

private def BAKCactus_Msh (_ : Bool) : Matrix (Zd 1 3) (Zd 1 3) ℂ :=
  Matrix.of fun x y => if y 0 = x 0 + 1 then 1 else 0

private theorem BAKCactus_Mss_zero (σ₁ σ₂ : Bool) : BAMssOf BAKCactus_Msh σ₁ σ₂ = 0 := by
  ext x y
  simp only [BAMssOf, BAKCactus_Msh, Matrix.of_apply, Matrix.zero_apply]
  generalize x 0 = u
  generalize y 0 = w
  have key : ∀ u w : ZMod 3, u = w + 1 → w = u + 1 → False := by decide
  by_cases h1 : u = w + 1
  · by_cases h2 : w = u + 1
    · exact (key u w h1 h2).elim
    · simp [h2]
  · simp [h1]

private theorem BAKCactus_Theta_one (t : ℝ) (σ₁ σ₂ : Bool) : BAThetaOf BAKCactus_Msh t σ₁ σ₂ = 1 := by
  simp [BAThetaOf, PropThetaQ, BAKCactus_Mss_zero]

private instance BAKCactus_uniqueF02 : Unique ↥BAKCactus_F02set :=
  ⟨⟨⟨_, BAKCactus_F02mem⟩⟩, fun J => Subtype.ext (Finset.mem_singleton.1 J.2)⟩

set_option maxRecDepth 100000 in
private theorem BAKCactus_card_F02 :
    (Finset.univ.filter fun x : BAslot BAKCactus_F02set → Zd 1 3 =>
      (∀ ℓ : Fin 4, ![![0], ![1], ![0], ![1]] ℓ = x (BAslotLeaf BAKCactus_F02set ℓ)) ∧
        x (BAslotIn BAKCactus_F02set default) = x (BAslotOut BAKCactus_F02set default) ∧
          ∀ s, x (BAKCactus_nextM s) 0 = x s 0 + 1).card = 1 := by
  decide

/-- **A chord tree has a nonzero value at `t = 1/2`**: `Γ_M({(0,2)}) = t = 1/2` at the directed datum (the label sum is
the single term `b_out = b_in = 2`; the six `M`-edges and the chord are the ones of `BAnextSlot`, `BAKCactus_next_eq`). -/
private theorem BAKCactus_val_F02 : BACactusVal 1 3 BAKCactus_Msh (1 / 2) BAKCactus_F02set
    ![true, true, false, true] ![![0], ![1], ![0], ![1]] = 1 / 2 := by
  unfold BACactusVal KLgval
  simp only [BACactusValLeafW, BAKCactus_Theta_one, BACactusValEdgeW]
  have hsum : ∀ x : BAslot BAKCactus_F02set → Zd 1 3,
      (∏ ℓ, (1 : Matrix (Zd 1 3) (Zd 1 3) ℂ) (![![0], ![1], ![0], ![1]] ℓ) (x (BAslotLeaf BAKCactus_F02set ℓ))) *
        ∏ e, ((fun J => ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Zd 1 3) (Zd 1 3) ℂ)) ⊕ᵥ
          fun s => BAKCactus_Msh (BAMcharge BAKCactus_F02set ![true, true, false, true] s))
            e (x (BACactusValSrc BAKCactus_F02set e)) (x (BACactusValTgt BAKCactus_F02set e)) =
      if (∀ ℓ : Fin 4, ![![0], ![1], ![0], ![1]] ℓ = x (BAslotLeaf BAKCactus_F02set ℓ)) ∧
          x (BAslotIn BAKCactus_F02set default) = x (BAslotOut BAKCactus_F02set default) ∧
          ∀ s, x (BAKCactus_nextM s) 0 = x s 0 + 1 then (1 / 2 : ℂ) else 0 := by
    intro x
    rw [Fintype.prod_sum_type]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, BACactusValSrc, BACactusValTgt, BAKCactus_next_eq,
      Matrix.one_apply, BAKCactus_Msh, Matrix.of_apply, id, Matrix.smul_apply, smul_eq_mul]
    simp only [Finset.prod_boole, Finset.mem_univ, forall_true_left]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun x _ => hsum x, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    BAKCactus_card_F02, one_smul]

example : BACactusVal 1 3 BAKCactus_Msh (1 / 2) BAKCactus_F02set ![true, true, false, true]
    ![![0], ![1], ![0], ![1]] = 1 / 2 := BAKCactus_val_F02

example : BAGamma 1 3 4 BAKCactus_Msh (1 / 2) BAKCactus_F02set ![true, true, false, true]
    ![![0], ![1], ![0], ![1]] ≠ 0 := by
  rw [BAGamma_eq, BAKCactus_val_F02]
  norm_num

end KCactusInst

end RBM.BA
