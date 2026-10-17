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

variable [NeZero L]

/-- `Θ_t^{(σ₁,σ₂)} = (1 - t M^{(σ₁,σ₂)})⁻¹` (`(def_Thxi)` at `S^{(B)} = I`, `1_2:1073-1076`) for a general
charge-indexed `M`. -/
def BAThetaOf (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ₁ σ₂ : Bool) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  PropThetaQ (BAMssOf M σ₁ σ₂) t

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

variable [NeZero n]

/-- The node of a slot: the tree node (`KLnodes F`, an `M`-cycle) the slot belongs to. -/
def BAslotNode (F : Finset (Fin n × Fin n)) : BAslot F → Fin n × Fin n
  | Sum.inl v => KLleafPar F v
  | Sum.inr (Sum.inl J) => KLnodePar F J.1
  | Sum.inr (Sum.inr J) => J.1

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

end MLoop

/-! ## 7. Compiled nonempty instances

Datum of the loop part: `d = 1`, `L = 3` and `M = BAMLoop_witM` of K00 (`BA/KBase.lean:102`: symmetric `3 × 3`
matrices with distinct entries; `W = 1`), the sign vectors `σ = (+,+,-)` at `n = 3` and `σ = (+,+,-,+)` at `n = 4`, the
labels `a = (0,1,2)` resp. `(0,1,2,1)`; `n = 4` has the three trees `∅`, `{(0,2)}`, `{(1,3)}` (`TSP_four`).  At
`t = 0` the chords carry `0 · Θ`, so only `F = ∅` survives and the tree sum is the `M`-loop, `BAMLoop`.  Datum of the
symmetry part: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`), `t = 1/2`. -/

/-! ### The slots and cycles of `F = {(0,2)}`, `n = 4` (two nodes, six slots; paper figure `A:552-583`) -/

/-! ### The slots and cycles of `F = {(1,3)}`, `n = 4` (the diagonal in the middle of the root cycle) -/

/-! ### The API lemmas at the data -/

/-! ### A chord tree with `t ≠ 0` and a nonzero value: the directed datum

`M(σ)_{xy} = 1(y = x + 1)` on `Z_3` (the directed 3-cycle, not symmetric): `M^{(σ₁σ₂)} = 0`, so `Θ_t^{(σ₁σ₂)} = 1` for
every `t` and the value of `F = {(0,2)}` at `n = 4` counts the labels `b` of the six slots with `b(leaf v) = a_v`, the
chord `b(in J) = b(out J)` (weight `t`) and every `M`-edge `s → BAnextSlot s` going from `x` to `x + 1`.  For
`a = (0,1,0,1)` the root cycle `out → leaf 2 → leaf 3 → out` reads `b_out → 0 → 1 → b_out`, the node cycle
`leaf 0 → leaf 1 → in → leaf 0` reads `0 → 1 → b_in → 0`: the only solution is `b_out = b_in = 2`, so the value is `t`. -/

end RBM.BA
