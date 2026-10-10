/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KCactus
import RBM3D.Loop.KLCut
import RBM3D.Loop.KLSumZeroWard

/-!
# The cut of the cactus at a chord, for arbitrary leaf weights

Ticket T2376 (BA-K06, Amend 1, DECISIONS §190).  K05b (`BA/KTreeRep.lean`, T2374, ab54184) cuts
the cactus value `Γ_M(F)` of a tree `F ∋ J` at the chord `J = (i, j)` into the values of the outer
polygon `KLFOut F J` and the inner polygon `KLFIn F J`, but all its helpers are `private`.  This
file holds the copy of that machinery (inside/outside slots, transport of the cyclic successor,
the cut equivalences and labels), with the stem `KTreeRep_` replaced by `KCactusCut_` and the
charges of the two polygons the merged `sigmaIn`, `sigmaOut` (`Loop/KLSumZeroWard.lean:70, 75`);
the `Lists` section of K05b (`cutGlueL/R`) is not copied.  The cut theorem is generalised from
the leaf weights `Θ` and the chord weight `Θ·Θ` of K05b to arbitrary leaf weights `Lw` and an
arbitrary chord weight `P S Q`.

Public: `BAinVinv`, `BAoutVinv`, `BAdeltaIn`, `BAdeltaOut` (the vertex maps and the data of the
two polygons), `baCactus_cut` (the generic cut) and `baCactus_leafW_in/out` (for `Lw = Θ` the
polygons carry their own leaf weights).  Every other helper is `private` with the stem
`KCactusCut_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. The vertex maps of a cut and the data of its two polygons -/

section Maps

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- The vertex `i + k` of the `n`-gon for the vertex `k` of the inner polygon of the cut `J = (i, j)` (the inverse of `KLinV J` on
`[i, j]`); `sigmaIn σ J k = σ (BAinVinv J k)` by definition. -/
def BAinVinv (J : Fin n × Fin n) (k : Fin (KLwIn J + 1)) : Fin n :=
  ⟨min (J.1.val + k.val) (n - 1), by have := NeZero.pos n; omega⟩

/-- The vertex of the `n`-gon for the vertex `k` of the outer polygon of the cut `J` (the inverse of `KLoutV J` off the open arc of
`J`); `sigmaOut σ J k = σ (BAoutVinv J k)` by definition. -/
def BAoutVinv (J : Fin n × Fin n) (k : Fin (n - KLwIn J + 1)) : Fin n :=
  ⟨min (KLunCol J k.val) (n - 1), by have := NeZero.pos n; omega⟩

/-- **The data of the inner polygon of the cut `J = (i, j)`**, carried by a function `f` on the vertices of the `n`-gon (the labels
`δ` or the leaf weights): `f_i, …, f_{j-1}` on the vertices `0, …, j-i-1` and the new value `x` on the last vertex. -/
def BAdeltaIn {α : Type*} (J : Fin n × Fin n) (f : Fin n → α) (x : α) : Fin (KLwIn J + 1) → α :=
  Function.update (fun k => f (BAinVinv J k)) (Fin.last _) x

/-- **The data of the outer polygon of the cut `J = (i, j)`**: `f_0, …, f_{i-1}, x, f_j, …, f_{n-1}`, with `x` at the glue vertex
`KLglueV J`. -/
def BAdeltaOut {α : Type*} (J : Fin n × Fin n) (f : Fin n → α) (x : α) : Fin (n - KLwIn J + 1) → α :=
  Function.update (fun k => f (BAoutVinv J k)) (KLglueV J) x

private theorem KCactusCut_inVinv_val (k : Fin (KLwIn J + 1)) (hJ : J.1.val < J.2.val) :
    (BAinVinv J k).val = k.val + J.1.val := by
  have := k.isLt; have := J.2.isLt
  simp only [BAinVinv, KLwIn] at *
  omega

private theorem KCactusCut_inVinv_inV {r : Fin n} (h1 : J.1 ≤ r) (h2 : r ≤ J.2) :
    BAinVinv J (KLinV J r) = r := by
  refine Fin.ext ?_
  simp only [BAinVinv, KLinV, KLwIn, Fin.le_def] at *
  have := r.isLt
  omega

private theorem KCactusCut_inV_inVinv (k : Fin (KLwIn J + 1)) (hJ : J.1.val < J.2.val) :
    KLinV J (BAinVinv J k) = k := by
  refine Fin.ext ?_
  have := k.isLt; have := J.2.isLt
  simp only [BAinVinv, KLinV, KLwIn] at *
  omega

private theorem KCactusCut_outVinv_outV (hJ : J.1.val + 2 ≤ J.2.val) {r : Fin n}
    (h : r.val ≤ J.1.val ∨ J.2.val ≤ r.val) : BAoutVinv J (KLoutV J r) = r := by
  refine Fin.ext ?_
  have := r.isLt; have := J.2.isLt
  simp only [BAoutVinv, KLoutV, KLcol, KLunCol, KLwIn] at *
  split_ifs <;> omega

private theorem KCactusCut_outV_outVinv (hJ : J.1.val + 2 ≤ J.2.val) (k : Fin (n - KLwIn J + 1)) :
    KLoutV J (BAoutVinv J k) = k := by
  refine Fin.ext ?_
  have := k.isLt; have := J.2.isLt
  simp only [BAoutVinv, KLoutV, KLcol, KLunCol, KLwIn] at *
  split_ifs <;> omega

omit [NeZero n] in
private theorem KCactusCut_glueV_val (hJ : J.1.val + 2 ≤ J.2.val) : (KLglueV J).val = J.1.val := by
  have := J.2.isLt
  simp only [KLglueV, KLwIn]
  omega

end Maps

/-! ## 2. Transport of the cyclic successor along an order-preserving relabelling of the slots -/

section Transport

variable {n n' : ℕ} [NeZero n] [NeZero n'] {F : Finset (Fin n × Fin n)} {F' : Finset (Fin n' × Fin n')}

/-- **The cyclic successor commutes with a relabelling of the slots** `φ : BAslot F' → BAslot F` that preserves "same node"
and the order of the starts inside a node, and whose image is closed under "same node": the successor is characterised
by the nodes and the starts alone (`BAnextSlot_eq_of_above`, `BAnextSlot_eq_of_wrap`). -/
private theorem KCactusCut_next_map (hF : KLIsTSP F) (hn : 2 ≤ n) (φ : BAslot F' → BAslot F)
    (hnode : ∀ s t, BAslotNode F (φ s) = BAslotNode F (φ t) ↔ BAslotNode F' s = BAslotNode F' t)
    (hstart : ∀ s t, BAslotNode F' s = BAslotNode F' t →
      (BAslotStart F' s < BAslotStart F' t ↔ BAslotStart F (φ s) < BAslotStart F (φ t)))
    (hclosed : ∀ s x, BAslotNode F x = BAslotNode F (φ s) → ∃ t, φ t = x) (s : BAslot F') :
    φ (BAnextSlot F' s) = BAnextSlot F (φ s) := by
  have hnext : BAslotNode F' (BAnextSlot F' s) = BAslotNode F' s := BAslotNode_nextSlot F' s
  have hle : ∀ s t, BAslotNode F' s = BAslotNode F' t →
      (BAslotStart F' s ≤ BAslotStart F' t ↔ BAslotStart F (φ s) ≤ BAslotStart F (φ t)) := by
    intro s t h
    rw [← not_lt, ← not_lt (a := BAslotStart F (φ t)), hstart t s h.symm]
  symm
  rcases BAnextSlot_spec F' s with ⟨hlt, hmin⟩ | ⟨hmax, hmin⟩
  · refine BAnextSlot_eq_of_above hF hn ((hnode _ _).2 hnext) ((hstart _ _ hnext.symm).1 hlt) ?_
    intro x hx hsx
    obtain ⟨t, rfl⟩ := hclosed s x hx
    have hts : BAslotNode F' t = BAslotNode F' s := (hnode _ _).1 hx
    exact (hle _ _ (hnext.trans hts.symm)).1 (hmin t hts ((hstart _ _ hts.symm).2 hsx))
  · refine BAnextSlot_eq_of_wrap hF hn ((hnode _ _).2 hnext) ?_ ?_
    · intro x hx
      obtain ⟨t, rfl⟩ := hclosed s x hx
      exact (hle _ _ ((hnode _ _).1 hx)).1 (hmax t ((hnode _ _).1 hx))
    · intro x hx
      obtain ⟨t, rfl⟩ := hclosed s x hx
      exact (hle _ _ (hnext.trans ((hnode _ _).1 hx).symm)).1 (hmin t ((hnode _ _).1 hx))

end Transport

/-! ## 3. The inner polygon of a cut: nodes, slots -/

section InSide

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

omit [NeZero n] in
private theorem KCactusCut_shiftIn_self : KLshiftIn J J = KLwholeP (KLwIn J + 1) := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp [KLshiftIn, KLwholeP, KLwIn]

omit [NeZero n] in
private theorem KCactusCut_arcLe_shiftIn_iff {d e : Fin n × Fin n} (hd : KLArcLe d J) (hd12 : d.1 ≤ d.2)
    (he : KLArcLe e J) (he12 : e.1 ≤ e.2) :
    KLArcLe (KLshiftIn J d) (KLshiftIn J e) ↔ KLArcLe d e := by
  have h1 := KLshiftIn_val hd hd12
  have h2 := KLshiftIn_val he he12
  simp only [KLArcLe, Fin.le_def] at hd he hd12 he12 ⊢
  omega

omit [NeZero n] in
private theorem KCactusCut_inArc_shiftIn_iff {d : Fin n × Fin n} (hd : KLArcLe d J) (hd12 : d.1 ≤ d.2) {v : Fin n}
    (hv : KLInArc J v) : KLInArc (KLshiftIn J d) (KLinV J v) ↔ KLInArc d v := by
  have h1 := KLshiftIn_val hd hd12
  have h2 := KLinV_val hv
  simp only [KLArcLe, KLInArc, Fin.le_def, Fin.lt_def] at hd hv hd12 ⊢
  omega

private theorem KCactusCut_shiftIn_mem_nodes (hF : KLIsTSP F) (hJ : J ∈ F) {x : Fin n × Fin n} (hx : x ∈ KLnodes F)
    (hxJ : KLArcLe x J) : KLshiftIn J x ∈ KLnodes (KLFIn F J) := by
  by_cases h : x = J
  · subst h
    rw [KCactusCut_shiftIn_self]
    exact KLwholeP_mem_nodes _
  · have hxF : x ∈ F := by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact absurd hxJ (KLnot_arcLe_wholeP hF hJ)
      · exact hx
    exact KLmem_nodes_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hxF, hxJ, h⟩))

private theorem KCactusCut_mem_nodes_FIn (hJ : J ∈ F) {y : Fin (KLwIn J + 1) × Fin (KLwIn J + 1)}
    (hy : y ∈ KLnodes (KLFIn F J)) : ∃ x ∈ KLnodes F, KLArcLe x J ∧ KLshiftIn J x = y := by
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact ⟨J, KLmem_nodes_of_mem hJ, ⟨le_refl _, le_refl _⟩, KCactusCut_shiftIn_self⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hx' := Finset.mem_filter.1 hx
    exact ⟨x, KLmem_nodes_of_mem hx'.1, hx'.2.1, rfl⟩

/-- **The parent node of an inside leaf, in the inner polygon.** -/
private theorem KCactusCut_leafPar_in (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {v : Fin n} (hv : KLInArc J v) :
    KLleafPar (KLFIn F J) (KLinV J v) = KLshiftIn J (KLleafPar F v) := by
  have h12 : ∀ x ∈ KLnodes F, x.1 ≤ x.2 := fun x hx => le_of_lt (KLlt_of_mem_nodes hF hn hx)
  have hspec := KLleafPar_spec hF (KLlt_of_inArc hv)
  have hin := KLleafPar_arcLe_of_inArc hF hJ hv
  have hmem := KLleafPar_mem F v
  refine KLleafPar_eq (KCactusCut_shiftIn_mem_nodes hF hJ hmem hin)
    ((KCactusCut_inArc_shiftIn_iff hin (h12 _ hmem) hv).2 hspec.1) ?_
  intro e' he' hev'
  obtain ⟨x, hx, hxJ, rfl⟩ := KCactusCut_mem_nodes_FIn hJ he'
  have hxv := (KCactusCut_inArc_shiftIn_iff hxJ (h12 _ hx) hv).1 hev'
  exact (KCactusCut_arcLe_shiftIn_iff hin (h12 _ hmem) hxJ (h12 _ hx)).2 (hspec.2 x hx hxv)

/-- **The parent node of an inside chord, in the inner polygon.** -/
private theorem KCactusCut_nodePar_in (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {d : Fin n × Fin n} (hd : d ∈ F)
    (hdJ : KLArcLe d J) (hne : d ≠ J) :
    KLnodePar (KLFIn F J) (KLshiftIn J d) = KLshiftIn J (KLnodePar F d) := by
  have h12 : ∀ x ∈ KLnodes F, x.1 ≤ x.2 := fun x hx => le_of_lt (KLlt_of_mem_nodes hF hn hx)
  have hdn := KLmem_nodes_of_mem hd
  have hspec := KLnodePar_spec hF hn hdn (KLne_wholeP hF hd)
  have hin := KLnodePar_arcLe hF hn hJ hd hdJ hne
  have hpm := KLnodePar_mem F d
  have hdd := KLshiftIn_val hdJ (h12 _ hdn)
  have hlt' := KLlt_of_mem_nodes hF hn hdn
  refine KLnodePar_eq ?_ (KCactusCut_shiftIn_mem_nodes hF hJ hpm hin)
    ((KCactusCut_arcLe_shiftIn_iff hdJ (h12 _ hdn) hin (h12 _ hpm)).2 hspec.2.1) ?_ ?_
  · rw [Fin.le_def, hdd.1, hdd.2]; rw [Fin.lt_def] at hlt'; omega
  · intro h
    exact hspec.2.2.1 (KLshiftIn_injOn hin (h12 _ hpm) hdJ (h12 _ hdn) h)
  · intro e' he' hde' hne'
    obtain ⟨x, hx, hxJ, rfl⟩ := KCactusCut_mem_nodes_FIn hJ he'
    have hdx := (KCactusCut_arcLe_shiftIn_iff hdJ (h12 _ hdn) hxJ (h12 _ hx)).1 hde'
    have hxd : x ≠ d := fun h => hne' (by rw [h])
    exact (KCactusCut_arcLe_shiftIn_iff hin (h12 _ hpm) hxJ (h12 _ hx)).2 (hspec.2.2.2 x hx hdx hxd)

end InSide

section InSlots

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

/-- `KLshiftIn J` as a bijection from the chords of `F` strictly inside `J` onto the chords of the inner polygon. -/
private noncomputable def KCactusCut_eIn (hF : KLIsTSP F) (J : Fin n × Fin n) : KLEIn F J ≃ ↥(KLFIn F J) :=
  Equiv.ofBijective
    (fun d => ⟨KLshiftIn J d.1.1, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨d.1.2, d.2⟩)⟩)
    ⟨fun d e h => Subtype.ext (Subtype.ext (KLshiftIn_injOn d.2.1 (le_of_lt (hF.1 _ d.1.2).1) e.2.1
        (le_of_lt (hF.1 _ e.1.2).1) (congrArg Subtype.val h))),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 y.2
        have hx' := Finset.mem_filter.1 hx
        exact ⟨⟨⟨x, hx'.1⟩, hx'.2⟩, Subtype.ext hxy⟩⟩

omit [NeZero n] in
private theorem KCactusCut_eIn_symm (hF : KLIsTSP F) (y : ↥(KLFIn F J)) :
    KLshiftIn J ((KCactusCut_eIn hF J).symm y).1.1 = y.1 := by
  exact congrArg Subtype.val ((KCactusCut_eIn hF J).apply_symm_apply y)

/-- **The relabelling of the slots of the inner polygon**: the leaf `k < w` is the leaf `k + i`, the last leaf is the slot
`BAslotIn J` (the cycle of the node `J`), the chords are lifted by `KLshiftIn⁻¹`. -/
private noncomputable def KCactusCut_φ (hF : KLIsTSP F) (hJ : J ∈ F) : BAslot (KLFIn F J) → BAslot F
  | Sum.inl k => if k.val < KLwIn J then Sum.inl (BAinVinv J k) else BAslotIn F ⟨J, hJ⟩
  | Sum.inr (Sum.inl y) => Sum.inr (Sum.inl ((KCactusCut_eIn hF J).symm y).1)
  | Sum.inr (Sum.inr y) => Sum.inr (Sum.inr ((KCactusCut_eIn hF J).symm y).1)

private theorem KCactusCut_φ_leaf (hF : KLIsTSP F) (hJ : J ∈ F) (k : Fin (KLwIn J + 1)) (hk : k.val < KLwIn J) :
    KCactusCut_φ hF hJ (Sum.inl k) = Sum.inl (BAinVinv J k) := by
  simp only [KCactusCut_φ, hk, ↓reduceIte]

private theorem KCactusCut_φ_last (hF : KLIsTSP F) (hJ : J ∈ F) (k : Fin (KLwIn J + 1)) (hk : ¬ k.val < KLwIn J) :
    KCactusCut_φ hF hJ (Sum.inl k) = BAslotIn F ⟨J, hJ⟩ := by
  simp only [KCactusCut_φ, hk, ↓reduceIte]

omit [NeZero n] in
/-- The facts about a chord strictly inside `J` that the maps need. -/
private theorem KCactusCut_inChord (hF : KLIsTSP F) (z : KLEIn F J) :
    KLArcLe z.1.1 J ∧ z.1.1 ≠ J ∧ z.1.1.1 < z.1.1.2 := ⟨z.2.1, z.2.2, (hF.1 _ z.1.2).1⟩

omit [NeZero n] in
private theorem KCactusCut_inV_val {r : Fin n} (h1 : J.1 ≤ r) (h2 : r ≤ J.2) :
    (KLinV J r).val = r.val - J.1.val := by
  simp only [KLinV, KLwIn, Fin.le_def] at *
  omega

/-- **The nodes**: the node of `s` in the inner polygon is the `KLshiftIn`-image of the node of `φ s` in `F`, which lies
inside `J`. -/
private theorem KCactusCut_φ_node (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFIn F J)) :
    BAslotNode (KLFIn F J) s = KLshiftIn J (BAslotNode F (KCactusCut_φ hF hJ s)) ∧
      KLArcLe (BAslotNode F (KCactusCut_φ hF hJ s)) J := by
  have hJw := KLdiag_width hF hJ
  rcases s with k | y | y
  · by_cases hk : k.val < KLwIn J
    · have hv : KLInArc J (BAinVinv J k) := by
        have := KCactusCut_inVinv_val k (by omega)
        simp only [KLInArc, Fin.le_def, Fin.lt_def, this]
        simp only [KLwIn] at hk
        omega
      rw [KCactusCut_φ_leaf hF hJ k hk]
      refine ⟨?_, KLleafPar_arcLe_of_inArc hF hJ hv⟩
      have h := KCactusCut_leafPar_in hF hn hJ hv
      rw [KCactusCut_inV_inVinv k (by omega)] at h
      exact h
    · rw [KCactusCut_φ_last hF hJ k hk]
      refine ⟨?_, ⟨le_refl _, le_refl _⟩⟩
      have hkl : k.val = (KLwIn J + 1) - 1 := by have := k.isLt; omega
      change KLleafPar (KLFIn F J) k = KLshiftIn J J
      rw [KLleafPar_root _ hkl, KCactusCut_shiftIn_self]
  · set z := (KCactusCut_eIn hF J).symm y with hz
    have hy := KCactusCut_eIn_symm hF y
    obtain ⟨h1, h2, -⟩ := KCactusCut_inChord hF z
    refine ⟨?_, KLnodePar_arcLe hF hn hJ z.1.2 h1 h2⟩
    change KLnodePar (KLFIn F J) y.1 = KLshiftIn J (KLnodePar F z.1.1)
    rw [← hy]
    exact KCactusCut_nodePar_in hF hn hJ z.1.2 h1 h2
  · set z := (KCactusCut_eIn hF J).symm y with hz
    have hy := KCactusCut_eIn_symm hF y
    obtain ⟨h1, h2, -⟩ := KCactusCut_inChord hF z
    exact ⟨hy.symm, h1⟩

/-- **The starts**: the start of `s` in the inner polygon is `KLinV J` of the start of `φ s`, and the starts of the image
lie in `[i, j]`. -/
private theorem KCactusCut_φ_start (hF : KLIsTSP F) (hJ : J ∈ F) (s : BAslot (KLFIn F J)) :
    BAslotStart (KLFIn F J) s = KLinV J (BAslotStart F (KCactusCut_φ hF hJ s)) ∧
      J.1 ≤ BAslotStart F (KCactusCut_φ hF hJ s) ∧ BAslotStart F (KCactusCut_φ hF hJ s) ≤ J.2 := by
  have hJw := KLdiag_width hF hJ
  rcases s with k | y | y
  · by_cases hk : k.val < KLwIn J
    · rw [KCactusCut_φ_leaf hF hJ k hk]
      change k = KLinV J (BAinVinv J k) ∧ J.1 ≤ BAinVinv J k ∧ BAinVinv J k ≤ J.2
      have := KCactusCut_inVinv_val k (by omega)
      simp only [Fin.le_def, this]
      refine ⟨(KCactusCut_inV_inVinv k (by omega)).symm, by omega, ?_⟩
      simp only [KLwIn] at hk
      omega
    · rw [KCactusCut_φ_last hF hJ k hk]
      change k = KLinV J J.2 ∧ J.1 ≤ J.2 ∧ J.2 ≤ J.2
      simp only [Fin.le_def]
      refine ⟨Fin.ext ?_, by omega, le_refl _⟩
      have := k.isLt
      rw [KCactusCut_inV_val (by simp only [Fin.le_def]; omega) (le_refl _)]
      simp only [KLwIn] at hk this ⊢
      omega
  · set z := (KCactusCut_eIn hF J).symm y with hz
    have hy := KCactusCut_eIn_symm hF y
    obtain ⟨h1, h2, h3⟩ := KCactusCut_inChord hF z
    simp only [KCactusCut_φ, BAslotStart_out, ← hz]
    refine ⟨?_, h1.1, le_trans (le_of_lt h3) h1.2⟩
    have := congrArg Prod.fst hy
    exact this.symm
  · set z := (KCactusCut_eIn hF J).symm y with hz
    have hy := KCactusCut_eIn_symm hF y
    obtain ⟨h1, h2, h3⟩ := KCactusCut_inChord hF z
    simp only [KCactusCut_φ, BAslotStart_in, ← hz]
    refine ⟨?_, le_trans h1.1 (le_of_lt h3), h1.2⟩
    have := congrArg Prod.snd hy
    exact this.symm

/-- **The image of `φ` is closed under "same node"**: every slot of `F` whose node lies inside `J` is `φ s`. -/
private theorem KCactusCut_φ_closed (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {x : BAslot F}
    (hx : KLArcLe (BAslotNode F x) J) : ∃ s, KCactusCut_φ hF hJ s = x := by
  have hJw := KLdiag_width hF hJ
  rcases x with v | J' | J'
  · have hv : KLInArc J v := by
      by_contra h
      exact KLnot_arcLe_leafPar hF hJ h hx
    have hlt : (KLinV J v).val < KLwIn J := by
      have := KLinV_val hv
      simp only [KLInArc, Fin.lt_def] at hv
      simp only [KLwIn]
      omega
    exact ⟨Sum.inl (KLinV J v), by
      rw [KCactusCut_φ_leaf hF hJ _ hlt, KCactusCut_inVinv_inV hv.1 (le_of_lt hv.2)]⟩
  · have hx' : KLArcLe (KLnodePar F J'.1) J := hx
    have h2 : J'.1 ≠ J := fun h => by
      rw [h] at hx'
      exact KLnot_arcLe_nodePar_self hF hn hJ hx'
    have h1 : KLArcLe J'.1 J :=
      ((KLnodePar_spec hF hn (KLmem_nodes_of_mem J'.2) (KLne_wholeP hF J'.2)).2.1).trans hx'
    refine ⟨Sum.inr (Sum.inl ((KCactusCut_eIn hF J) ⟨J', h1, h2⟩)), ?_⟩
    simp only [KCactusCut_φ, Equiv.symm_apply_apply]
  · have hx' : KLArcLe J'.1 J := hx
    by_cases h2 : J'.1 = J
    · have hJ' : J' = ⟨J, hJ⟩ := Subtype.ext h2
      refine ⟨Sum.inl (Fin.last _), ?_⟩
      rw [KCactusCut_φ_last hF hJ _ (by simp), hJ']
    · refine ⟨Sum.inr (Sum.inr ((KCactusCut_eIn hF J) ⟨J', hx', h2⟩)), ?_⟩
      simp only [KCactusCut_φ, Equiv.symm_apply_apply]

/-- **`φ` commutes with the cyclic successor**: the cycle of a node of the inner polygon is the cycle of the corresponding
node of `F`. -/
private theorem KCactusCut_φ_next (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFIn F J)) :
    KCactusCut_φ hF hJ (BAnextSlot (KLFIn F J) s) = BAnextSlot F (KCactusCut_φ hF hJ s) := by
  have h12 : ∀ y : BAslot (KLFIn F J) , (BAslotNode F (KCactusCut_φ hF hJ y)).1 ≤
      (BAslotNode F (KCactusCut_φ hF hJ y)).2 := fun y =>
    le_of_lt (KLlt_of_mem_nodes hF hn (BAslotNode_mem_nodes F _))
  refine KCactusCut_next_map hF hn (KCactusCut_φ hF hJ) ?_ ?_ ?_ s
  · intro s t
    constructor
    · intro h
      rw [(KCactusCut_φ_node hF hn hJ s).1, (KCactusCut_φ_node hF hn hJ t).1, h]
    · intro h
      rw [(KCactusCut_φ_node hF hn hJ s).1, (KCactusCut_φ_node hF hn hJ t).1] at h
      exact KLshiftIn_injOn (KCactusCut_φ_node hF hn hJ s).2 (h12 s) (KCactusCut_φ_node hF hn hJ t).2 (h12 t) h
  · intro s t _
    obtain ⟨hs, hs1, hs2⟩ := KCactusCut_φ_start hF hJ s
    obtain ⟨ht, ht1, ht2⟩ := KCactusCut_φ_start hF hJ t
    rw [hs, ht, Fin.lt_def, Fin.lt_def, KCactusCut_inV_val hs1 hs2, KCactusCut_inV_val ht1 ht2]
    simp only [Fin.le_def] at hs1 hs2 ht1 ht2
    omega
  · intro s x hx
    exact KCactusCut_φ_closed hF hn hJ (by rw [hx]; exact (KCactusCut_φ_node hF hn hJ s).2)

end InSlots

/-! ## 4. The outer polygon of a cut: nodes, slots -/

section OutSide

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

omit [NeZero n] in
private theorem KCactusCut_col_le_iff {r s : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r) (hs : s ≤ J.1.val ∨ J.2.val ≤ s)
    (hJ : J.1.val + 2 ≤ J.2.val) : KLcol J r ≤ KLcol J s ↔ r ≤ s := by
  simp only [KLcol, KLwIn]
  split_ifs <;> omega

omit [NeZero n] in
private theorem KCactusCut_col_lt_of_vertex {r v : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r)
    (hv : v < J.1.val ∨ J.2.val ≤ v) (hJ : J.1.val + 2 ≤ J.2.val) :
    (KLcol J v < KLcol J r ↔ v < r) ∧ (KLcol J r ≤ KLcol J v ↔ r ≤ v) := by
  simp only [KLcol, KLwIn]
  constructor <;> split_ifs <;> omega

omit [NeZero n] in
private theorem KCactusCut_arcLe_shiftOut_iff {d e : Fin n × Fin n} (hd : KLOutEnds J d) (he : KLOutEnds J e)
    (hJ : J.1.val + 2 ≤ J.2.val) : KLArcLe (KLshiftOut J d) (KLshiftOut J e) ↔ KLArcLe d e := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have h2 := KLshiftOut_val e hJ2
  simp only [KLArcLe, Fin.le_def, h1, h2, KCactusCut_col_le_iff he.1 hd.1 hJ, KCactusCut_col_le_iff hd.2.1 he.2.1 hJ]

omit [NeZero n] in
private theorem KCactusCut_inArc_shiftOut_iff {d : Fin n × Fin n} (hd : KLOutEnds J d) {v : Fin n}
    (hv : ¬KLInArc J v) (hJ : J.1.val + 2 ≤ J.2.val) :
    KLInArc (KLshiftOut J d) (KLoutV J v) ↔ KLInArc d v := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have h2 := KLoutV_val v hJ2
  have hv' : v.val < J.1.val ∨ J.2.val ≤ v.val := by
    simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv; omega
  simp only [KLInArc, Fin.le_def, Fin.lt_def, h1, h2, (KCactusCut_col_lt_of_vertex hd.1 hv' hJ).2,
    (KCactusCut_col_lt_of_vertex hd.2.1 hv' hJ).1]

omit [NeZero n] in
private theorem KCactusCut_inArc_glue_iff {d : Fin n × Fin n} (hd : KLOutEnds J d) (hJ : J.1.val + 2 ≤ J.2.val) :
    KLInArc (KLshiftOut J d) (KLglueV J) ↔ KLArcLe J d := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have hg : (KLglueV J).val = J.1.val := KCactusCut_glueV_val hJ
  obtain ⟨e1, e2, e3⟩ := hd
  simp only [KLInArc, KLArcLe, Fin.le_def, Fin.lt_def, h1, hg]
  simp only [KLcol, KLwIn]
  split_ifs <;> omega

private theorem KCactusCut_shiftOut_whole (hF : KLIsTSP F) (hJ : J ∈ F) :
    KLshiftOut J (KLwholeP n) = KLwholeP (n - KLwIn J + 1) := by
  have hJw := KLdiag_width hF hJ
  have := J.2.isLt
  have hc : KLcol J (n - 1) = n - KLwIn J := by
    rw [KLcol_of_gt (by omega)]; simp only [KLwIn]; omega
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · simp [KLshiftOut, KLwholeP, KLcol]
  · simp only [KLshiftOut, KLwholeP, hc]; simp

private theorem KCactusCut_shiftOut_mem_nodes (hF : KLIsTSP F) (hJ : J ∈ F) {x : Fin n × Fin n} (hx : x ∈ KLnodes F)
    (hxJ : ¬KLArcLe x J) : KLshiftOut J x ∈ KLnodes (KLFOut F J) := by
  rcases Finset.mem_insert.1 hx with rfl | hx
  · rw [KCactusCut_shiftOut_whole hF hJ]; exact KLwholeP_mem_nodes _
  · exact KLmem_nodes_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hx, hxJ⟩))

private theorem KCactusCut_mem_nodes_FOut (hF : KLIsTSP F) (hJ : J ∈ F)
    {y : Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)} (hy : y ∈ KLnodes (KLFOut F J)) :
    ∃ x ∈ KLnodes F, ¬KLArcLe x J ∧ KLshiftOut J x = y := by
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact ⟨KLwholeP n, KLwholeP_mem_nodes F, KLnot_arcLe_wholeP hF hJ, KCactusCut_shiftOut_whole hF hJ⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hx' := Finset.mem_filter.1 hx
    exact ⟨x, KLmem_nodes_of_mem hx'.1, hx'.2, rfl⟩

/-- **The parent node of an outside leaf, in the outer polygon.** -/
private theorem KCactusCut_leafPar_out (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {v : Fin n} (hv : ¬KLInArc J v) :
    KLleafPar (KLFOut F J) (KLoutV J v) = KLshiftOut J (KLleafPar F v) := by
  have hJw := KLdiag_width hF hJ
  have hJ2 : J.1.val < J.2.val := by omega
  have hends : ∀ y ∈ KLnodes F, ¬KLArcLe y J → KLOutEnds J y := fun y hy hyJ => KLoutEnds_of hF hn hJ hy hyJ
  have hout := KLnot_arcLe_leafPar hF hJ hv
  have hpm := KLleafPar_mem F v
  by_cases hr : v.val < n - 1
  · have hspec := KLleafPar_spec hF hr
    refine KLleafPar_eq (KCactusCut_shiftOut_mem_nodes hF hJ hpm hout)
      ((KCactusCut_inArc_shiftOut_iff (hends _ hpm hout) hv hJw).2 hspec.1) ?_
    intro e' he' hve'
    obtain ⟨z, hz, hzJ, rfl⟩ := KCactusCut_mem_nodes_FOut hF hJ he'
    have hzv := (KCactusCut_inArc_shiftOut_iff (hends _ hz hzJ) hv hJw).1 hve'
    exact (KCactusCut_arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2 (hspec.2 z hz hzv)
  · have hroot : v.val = n - 1 := by have := v.isLt; omega
    rw [KLleafPar_root F hroot, KCactusCut_shiftOut_whole hF hJ, KLleafPar_root]
    rw [KLoutV_val _ hJ2, hroot]
    have := J.2.isLt
    rw [KLcol_of_gt (by omega)]
    simp only [KLwIn]; omega

/-- **The parent node of the glue leaf, in the outer polygon**: the parent of `J`. -/
private theorem KCactusCut_leafPar_glue (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    KLleafPar (KLFOut F J) (KLglueV J) = KLshiftOut J (KLnodePar F J) := by
  have hJw := KLdiag_width hF hJ
  have hends : ∀ y ∈ KLnodes F, ¬KLArcLe y J → KLOutEnds J y := fun y hy hyJ => KLoutEnds_of hF hn hJ hy hyJ
  have hJn := KLmem_nodes_of_mem hJ
  have hspec := KLnodePar_spec hF hn hJn (KLne_wholeP hF hJ)
  have hout := KLnot_arcLe_nodePar_self hF hn hJ
  have hpm := KLnodePar_mem F J
  refine KLleafPar_eq (KCactusCut_shiftOut_mem_nodes hF hJ hpm hout)
    ((KCactusCut_inArc_glue_iff (hends _ hpm hout) hJw).2 hspec.2.1) ?_
  intro e' he' hge'
  obtain ⟨z, hz, hzJ, rfl⟩ := KCactusCut_mem_nodes_FOut hF hJ he'
  have hJz := (KCactusCut_inArc_glue_iff (hends _ hz hzJ) hJw).1 hge'
  have hzne : z ≠ J := fun h => hzJ (h ▸ ⟨le_refl _, le_refl _⟩)
  exact (KCactusCut_arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2 (hspec.2.2.2 z hz hJz hzne)

/-- **The parent node of an outside chord, in the outer polygon.** -/
private theorem KCactusCut_nodePar_out (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {d : Fin n × Fin n} (hd : d ∈ F)
    (hdJ : ¬KLArcLe d J) :
    KLnodePar (KLFOut F J) (KLshiftOut J d) = KLshiftOut J (KLnodePar F d) := by
  have hJw := KLdiag_width hF hJ
  have hJ2 : J.1.val < J.2.val := by omega
  have hends : ∀ y ∈ KLnodes F, ¬KLArcLe y J → KLOutEnds J y := fun y hy hyJ => KLoutEnds_of hF hn hJ hy hyJ
  have hdn := KLmem_nodes_of_mem hd
  have hspec := KLnodePar_spec hF hn hdn (KLne_wholeP hF hd)
  have hout := KLnot_arcLe_nodePar hF hn hd hdJ
  have hpm := KLnodePar_mem F d
  have hdE := hends _ hdn hdJ
  have hdd := KLshiftOut_val d hJ2
  refine KLnodePar_eq ?_ (KCactusCut_shiftOut_mem_nodes hF hJ hpm hout)
    ((KCactusCut_arcLe_shiftOut_iff hdE (hends _ hpm hout) hJw).2 hspec.2.1) ?_ ?_
  · rw [Fin.le_def, hdd.1, hdd.2]
    exact (KCactusCut_col_le_iff hdE.1 hdE.2.1 hJw).2 (le_of_lt hdE.2.2)
  · intro h
    exact hspec.2.2.1 (KLshiftOut_injOn (hends _ hpm hout) hdE hJw h)
  · intro e' he' hde' hne'
    obtain ⟨z, hz, hzJ, rfl⟩ := KCactusCut_mem_nodes_FOut hF hJ he'
    have hdz := (KCactusCut_arcLe_shiftOut_iff hdE (hends _ hz hzJ) hJw).1 hde'
    have hzd : z ≠ d := fun h => hne' (by rw [h])
    exact (KCactusCut_arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2 (hspec.2.2.2 z hz hdz hzd)

end OutSide

section OutSlots

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

/-- `KLshiftOut J` as a bijection from the chords of `F` not inside `J` onto the chords of the outer polygon. -/
private noncomputable def KCactusCut_eOut (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    KLEOut F J ≃ ↥(KLFOut F J) :=
  Equiv.ofBijective
    (fun d => ⟨KLshiftOut J d.1.1, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨d.1.2, d.2⟩)⟩)
    ⟨fun d e h => Subtype.ext (Subtype.ext (KLshiftOut_injOn (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem d.1.2) d.2)
        (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem e.1.2) e.2) (KLdiag_width hF hJ) (congrArg Subtype.val h))),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 y.2
        have hx' := Finset.mem_filter.1 hx
        exact ⟨⟨⟨x, hx'.1⟩, hx'.2⟩, Subtype.ext hxy⟩⟩

private theorem KCactusCut_eOut_symm (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (y : ↥(KLFOut F J)) :
    KLshiftOut J ((KCactusCut_eOut hF hn hJ).symm y).1.1 = y.1 := by
  exact congrArg Subtype.val ((KCactusCut_eOut hF hn hJ).apply_symm_apply y)

/-- **The relabelling of the slots of the outer polygon**: the glue leaf is the slot `BAslotOut J` (the cycle of the parent
of `J`), the other leaves are lifted by `KLoutV⁻¹`, the chords by `KLshiftOut⁻¹`. -/
private noncomputable def KCactusCut_ψ (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    BAslot (KLFOut F J) → BAslot F
  | Sum.inl k => if k = KLglueV J then BAslotOut F ⟨J, hJ⟩ else Sum.inl (BAoutVinv J k)
  | Sum.inr (Sum.inl y) => Sum.inr (Sum.inl ((KCactusCut_eOut hF hn hJ).symm y).1)
  | Sum.inr (Sum.inr y) => Sum.inr (Sum.inr ((KCactusCut_eOut hF hn hJ).symm y).1)

private theorem KCactusCut_ψ_leaf (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (k : Fin (n - KLwIn J + 1))
    (hk : k ≠ KLglueV J) : KCactusCut_ψ hF hn hJ (Sum.inl k) = Sum.inl (BAoutVinv J k) := by
  simp only [KCactusCut_ψ, hk, ↓reduceIte]

private theorem KCactusCut_ψ_glue (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    KCactusCut_ψ hF hn hJ (Sum.inl (KLglueV J)) = BAslotOut F ⟨J, hJ⟩ := by
  simp only [KCactusCut_ψ, ↓reduceIte]

private theorem KCactusCut_outVinv_outer (hJ : J.1.val + 2 ≤ J.2.val) {k : Fin (n - KLwIn J + 1)}
    (hk : k ≠ KLglueV J) : ¬KLInArc J (BAoutVinv J k) := by
  have hg := KCactusCut_glueV_val hJ
  have hk' : k.val ≠ J.1.val := fun h => hk (Fin.ext (by rw [hg]; exact h))
  have := k.isLt; have := J.2.isLt
  simp only [KLInArc, Fin.le_def, Fin.lt_def, BAoutVinv, KLunCol, KLwIn, not_and, not_lt]
  split_ifs <;> omega

omit [NeZero n] in
private theorem KCactusCut_outV_ne_glue (hJ : J.1.val + 2 ≤ J.2.val) {v : Fin n} (hv : ¬KLInArc J v) :
    KLoutV J v ≠ KLglueV J := by
  intro h
  have h1 := congrArg Fin.val h
  rw [KLoutV_val v (by omega), KCactusCut_glueV_val hJ] at h1
  simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv
  simp only [KLcol, KLwIn] at h1
  split_ifs at h1 <;> omega

/-- The facts about a chord outside `J` that the maps need. -/
private theorem KCactusCut_outChord (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (z : KLEOut F J) :
    KLOutEnds J z.1.1 := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem z.1.2) z.2

/-- **The nodes**: the node of `s` in the outer polygon is the `KLshiftOut`-image of the node of `ψ s` in `F`, which is not
inside `J`. -/
private theorem KCactusCut_ψ_node (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFOut F J)) :
    BAslotNode (KLFOut F J) s = KLshiftOut J (BAslotNode F (KCactusCut_ψ hF hn hJ s)) ∧
      ¬KLArcLe (BAslotNode F (KCactusCut_ψ hF hn hJ s)) J := by
  have hJw := KLdiag_width hF hJ
  rcases s with k | y | y
  · by_cases hk : k = KLglueV J
    · subst hk
      rw [KCactusCut_ψ_glue hF hn hJ]
      exact ⟨KCactusCut_leafPar_glue hF hn hJ, KLnot_arcLe_nodePar_self hF hn hJ⟩
    · have hv := KCactusCut_outVinv_outer hJw hk
      rw [KCactusCut_ψ_leaf hF hn hJ k hk]
      refine ⟨?_, KLnot_arcLe_leafPar hF hJ hv⟩
      have h := KCactusCut_leafPar_out hF hn hJ hv
      rw [KCactusCut_outV_outVinv hJw k] at h
      exact h
  · set z := (KCactusCut_eOut hF hn hJ).symm y with hz
    have hy := KCactusCut_eOut_symm hF hn hJ y
    refine ⟨?_, KLnot_arcLe_nodePar hF hn z.1.2 z.2⟩
    change KLnodePar (KLFOut F J) y.1 = KLshiftOut J (KLnodePar F z.1.1)
    rw [← hy]
    exact KCactusCut_nodePar_out hF hn hJ z.1.2 z.2
  · set z := (KCactusCut_eOut hF hn hJ).symm y with hz
    have hy := KCactusCut_eOut_symm hF hn hJ y
    exact ⟨hy.symm, z.2⟩

/-- **The starts**: the start of `s` in the outer polygon is `KLoutV J` of the start of `ψ s`, and the starts of the image
lie outside the open arc of `J`. -/
private theorem KCactusCut_ψ_start (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFOut F J)) :
    BAslotStart (KLFOut F J) s = KLoutV J (BAslotStart F (KCactusCut_ψ hF hn hJ s)) ∧
      ((BAslotStart F (KCactusCut_ψ hF hn hJ s)).val ≤ J.1.val ∨ J.2.val ≤ (BAslotStart F (KCactusCut_ψ hF hn hJ s)).val) := by
  have hJw := KLdiag_width hF hJ
  rcases s with k | y | y
  · by_cases hk : k = KLglueV J
    · subst hk
      rw [KCactusCut_ψ_glue hF hn hJ]
      change KLglueV J = KLoutV J J.1 ∧ (J.1.val ≤ J.1.val ∨ J.2.val ≤ J.1.val)
      refine ⟨Fin.ext ?_, Or.inl le_rfl⟩
      rw [KLoutV_val _ (by omega), KCactusCut_glueV_val hJw, KLcol_of_le le_rfl]
    · have hv := KCactusCut_outVinv_outer hJw hk
      rw [KCactusCut_ψ_leaf hF hn hJ k hk]
      change k = KLoutV J (BAoutVinv J k) ∧
        ((BAoutVinv J k).val ≤ J.1.val ∨ J.2.val ≤ (BAoutVinv J k).val)
      refine ⟨(KCactusCut_outV_outVinv hJw k).symm, ?_⟩
      simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv
      omega
  · set z := (KCactusCut_eOut hF hn hJ).symm y with hz
    have hy := KCactusCut_eOut_symm hF hn hJ y
    have hE := KCactusCut_outChord hF hn hJ z
    simp only [KCactusCut_ψ, BAslotStart_out, ← hz]
    refine ⟨?_, ?_⟩
    · have := congrArg Prod.fst hy
      exact this.symm
    · rcases hE.1 with h | h
      · exact Or.inl h
      · exact Or.inr h
  · set z := (KCactusCut_eOut hF hn hJ).symm y with hz
    have hy := KCactusCut_eOut_symm hF hn hJ y
    have hE := KCactusCut_outChord hF hn hJ z
    simp only [KCactusCut_ψ, BAslotStart_in, ← hz]
    refine ⟨?_, ?_⟩
    · have := congrArg Prod.snd hy
      exact this.symm
    · rcases hE.2.1 with h | h
      · exact Or.inl h
      · exact Or.inr h

/-- **The image of `ψ` is closed under "same node"**: every slot of `F` whose node is not inside `J` is `ψ s`. -/
private theorem KCactusCut_ψ_closed (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {x : BAslot F}
    (hx : ¬KLArcLe (BAslotNode F x) J) : ∃ s, KCactusCut_ψ hF hn hJ s = x := by
  have hJw := KLdiag_width hF hJ
  rcases x with v | J' | J'
  · have hv : ¬KLInArc J v := fun h => hx (KLleafPar_arcLe_of_inArc hF hJ h)
    exact ⟨Sum.inl (KLoutV J v), by
      rw [KCactusCut_ψ_leaf hF hn hJ _ (KCactusCut_outV_ne_glue hJw hv), KCactusCut_outVinv_outV hJw (by
        simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv; omega)]⟩
  · by_cases h2 : J'.1 = J
    · have hJ' : J' = ⟨J, hJ⟩ := Subtype.ext h2
      exact ⟨Sum.inl (KLglueV J), by rw [KCactusCut_ψ_glue hF hn hJ, hJ']⟩
    · have h1 : ¬KLArcLe J'.1 J := fun h =>
        hx (KLnodePar_arcLe hF hn hJ J'.2 h h2)
      refine ⟨Sum.inr (Sum.inl ((KCactusCut_eOut hF hn hJ) ⟨J', h1⟩)), ?_⟩
      simp only [KCactusCut_ψ, Equiv.symm_apply_apply]
  · have hx' : ¬KLArcLe J'.1 J := hx
    refine ⟨Sum.inr (Sum.inr ((KCactusCut_eOut hF hn hJ) ⟨J', hx'⟩)), ?_⟩
    simp only [KCactusCut_ψ, Equiv.symm_apply_apply]

/-- **`ψ` commutes with the cyclic successor.** -/
private theorem KCactusCut_ψ_next (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFOut F J)) :
    KCactusCut_ψ hF hn hJ (BAnextSlot (KLFOut F J) s) = BAnextSlot F (KCactusCut_ψ hF hn hJ s) := by
  have hJw := KLdiag_width hF hJ
  have hends : ∀ y : BAslot (KLFOut F J), KLOutEnds J (BAslotNode F (KCactusCut_ψ hF hn hJ y)) := fun y =>
    KLoutEnds_of hF hn hJ (BAslotNode_mem_nodes F _) (KCactusCut_ψ_node hF hn hJ y).2
  refine KCactusCut_next_map hF hn (KCactusCut_ψ hF hn hJ) ?_ ?_ ?_ s
  · intro s t
    constructor
    · intro h
      rw [(KCactusCut_ψ_node hF hn hJ s).1, (KCactusCut_ψ_node hF hn hJ t).1, h]
    · intro h
      rw [(KCactusCut_ψ_node hF hn hJ s).1, (KCactusCut_ψ_node hF hn hJ t).1] at h
      exact KLshiftOut_injOn (hends s) (hends t) hJw h
  · intro s t _
    obtain ⟨hs, hs1⟩ := KCactusCut_ψ_start hF hn hJ s
    obtain ⟨ht, ht1⟩ := KCactusCut_ψ_start hF hn hJ t
    rw [hs, ht, Fin.lt_def, Fin.lt_def, KLoutV_val _ (by omega), KLoutV_val _ (by omega)]
    have := (KCactusCut_col_le_iff ht1 hs1 hJw)
    omega
  · intro s x hx
    exact KCactusCut_ψ_closed hF hn hJ (by rw [hx]; exact (KCactusCut_ψ_node hF hn hJ s).2)

end OutSlots

/-! ## 5. The cut equivalences of the cactus at a chord -/

section CutEquivs

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

omit [NeZero n] in
private theorem KCactusCut_wbounds (hF : KLIsTSP F) (hJ : J ∈ F) :
    2 ≤ KLwIn J ∧ KLwIn J + 2 ≤ n := by
  have hJd := hF.1 J hJ
  obtain ⟨h1, h2, h3⟩ := hJd
  have := J.2.isLt
  rw [Fin.lt_def] at h1
  simp only [KLwIn]
  omega

private theorem KCactusCut_ψ_injective (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Function.Injective (KCactusCut_ψ hF hn hJ) := by
  intro s t h
  have hFo := KLisTSP_of_mem_TSP (KLFOut_mem_TSP (hF.1 J hJ) hF hn hJ)
  have hb := KCactusCut_wbounds hF hJ
  refine BAslot_start_inj hFo (by omega) ?_ ?_
  · rw [(KCactusCut_ψ_node hF hn hJ s).1, (KCactusCut_ψ_node hF hn hJ t).1, h]
  · rw [(KCactusCut_ψ_start hF hn hJ s).1, (KCactusCut_ψ_start hF hn hJ t).1, h]

private theorem KCactusCut_φ_injective (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Function.Injective (KCactusCut_φ hF hJ) := by
  intro s t h
  have hFi := KLisTSP_of_mem_TSP (KLFIn_mem_TSP (J := J) hF)
  have hb := KCactusCut_wbounds hF hJ
  refine BAslot_start_inj hFi (by omega) ?_ ?_
  · rw [(KCactusCut_φ_node hF hn hJ s).1, (KCactusCut_φ_node hF hn hJ t).1, h]
  · rw [(KCactusCut_φ_start hF hJ s).1, (KCactusCut_φ_start hF hJ t).1, h]

private theorem KCactusCut_ψ_ne_φ (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFOut F J))
    (t : BAslot (KLFIn F J)) : KCactusCut_ψ hF hn hJ s ≠ KCactusCut_φ hF hJ t := fun h =>
  (KCactusCut_ψ_node hF hn hJ s).2 (h ▸ (KCactusCut_φ_node hF hn hJ t).2)

/-- **The relabelling of the slots of the cut**: `BAslot F_out ⊕ BAslot F_in ≃ BAslot F`. -/
private noncomputable def KCactusCut_eN (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    BAslot (KLFOut F J) ⊕ BAslot (KLFIn F J) ≃ BAslot F :=
  Equiv.ofBijective (Sum.elim (KCactusCut_ψ hF hn hJ) (KCactusCut_φ hF hJ))
    ⟨KCactusCut_ψ_injective hF hn hJ |>.sumElim (KCactusCut_φ_injective hF hn hJ) (KCactusCut_ψ_ne_φ hF hn hJ),
      fun x => by
        by_cases hx : KLArcLe (BAslotNode F x) J
        · obtain ⟨s, hs⟩ := KCactusCut_φ_closed hF hn hJ hx
          exact ⟨Sum.inr s, hs⟩
        · obtain ⟨s, hs⟩ := KCactusCut_ψ_closed hF hn hJ hx
          exact ⟨Sum.inl s, hs⟩⟩

/-- The vertices of `n`-gon split into those outside and inside the arc of `J`. -/
private def KCactusCut_eL (J : Fin n × Fin n) : KLLOut J ⊕ KLLIn J ≃ Fin n :=
  ((Equiv.sumCompl (fun v : Fin n => KLInArc J v)).symm.trans (Equiv.sumComm _ _)).symm

/-- The leaves of the inner polygon: the glue leaf `last` and the vertices inside the arc of `J`. -/
private noncomputable def KCactusCut_eLin (J : Fin n × Fin n) (hJ : J.1.val + 2 ≤ J.2.val) :
    Option (KLLIn J) ≃ Fin (KLwIn J + 1) :=
  Equiv.ofBijective (fun o => o.elim (Fin.last _) (fun v => KLinV J v.1))
    ⟨by
      have hlt : ∀ v : KLLIn J, (KLinV J v.1).val < KLwIn J := by
        intro v
        have h1 := KLinV_val v.2
        have h2 := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def] at h2
        simp only [KLwIn]; omega
      rintro (_ | v) (_ | v') h
      · rfl
      · have := hlt v'; simp only [Option.elim, Fin.ext_iff, Fin.val_last] at h; omega
      · have := hlt v; simp only [Option.elim, Fin.ext_iff, Fin.val_last] at h; omega
      · simp only [Option.elim, Fin.ext_iff] at h
        have h1 := KLinV_val v.2
        have h2 := KLinV_val v'.2
        have h3 := v.2
        have h4 := v'.2
        simp only [KLInArc, Fin.le_def] at h3 h4
        exact congrArg some (Subtype.ext (Fin.ext (by omega))),
      fun k => by
        by_cases hk : k.val < KLwIn J
        · have hv : KLInArc J (BAinVinv J k) := by
            have := KCactusCut_inVinv_val k (by omega)
            simp only [KLInArc, Fin.le_def, Fin.lt_def, this]
            simp only [KLwIn] at hk
            omega
          exact ⟨some ⟨_, hv⟩, KCactusCut_inV_inVinv k (by omega)⟩
        · exact ⟨none, Fin.ext (by have := k.isLt; simp only [Option.elim, Fin.val_last]; omega)⟩⟩

end CutEquivs

section CutEquivs2

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

/-- The leaves of the outer polygon: the glue leaf and the vertices outside the arc of `J`. -/
private noncomputable def KCactusCut_eLout (J : Fin n × Fin n) (hJ : J.1.val + 2 ≤ J.2.val) :
    Option (KLLOut J) ≃ Fin (n - KLwIn J + 1) :=
  Equiv.ofBijective (fun o => o.elim (KLglueV J) (fun v => KLoutV J v.1))
    ⟨by
      have hv : ∀ v : KLLOut J, v.1.val ≤ J.1.val ∨ J.2.val ≤ v.1.val := fun v => by
        have := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this
        omega
      rintro (_ | v) (_ | v') h
      · rfl
      · exact absurd h.symm (KCactusCut_outV_ne_glue hJ v'.2)
      · exact absurd h (KCactusCut_outV_ne_glue hJ v.2)
      · have h' : KLoutV J v.1 = KLoutV J v'.1 := h
        have := congrArg (BAoutVinv J) h'
        rw [KCactusCut_outVinv_outV hJ (hv v), KCactusCut_outVinv_outV hJ (hv v')] at this
        exact congrArg some (Subtype.ext this),
      fun k => by
        by_cases hk : k = KLglueV J
        · exact ⟨none, hk.symm⟩
        · exact ⟨some ⟨_, KCactusCut_outVinv_outer hJ hk⟩, KCactusCut_outV_outVinv hJ k⟩⟩

/-- The edges of the cut: the chord `J` is the new edge of the splitting, the chords and `M`-edges of `F_out` and `F_in` are
the others. -/
private noncomputable def KCactusCut_Eb (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Option ((↥(KLFOut F J) ⊕ BAslot (KLFOut F J)) ⊕ (↥(KLFIn F J) ⊕ BAslot (KLFIn F J))) → ↥F ⊕ BAslot F
  | none => Sum.inl ⟨J, hJ⟩
  | some (Sum.inl (Sum.inl y)) => Sum.inl ((KCactusCut_eOut hF hn hJ).symm y).1
  | some (Sum.inl (Sum.inr s)) => Sum.inr (KCactusCut_ψ hF hn hJ s)
  | some (Sum.inr (Sum.inl y)) => Sum.inl ((KCactusCut_eIn hF J).symm y).1
  | some (Sum.inr (Sum.inr s)) => Sum.inr (KCactusCut_φ hF hJ s)

private theorem KCactusCut_Eb_bijective (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Function.Bijective (KCactusCut_Eb hF hn hJ) := by
  have hoc : ∀ y, ¬KLArcLe ((KCactusCut_eOut hF hn hJ).symm y).1.1 J := fun y =>
    ((KCactusCut_eOut hF hn hJ).symm y).2
  have hic : ∀ y, KLArcLe ((KCactusCut_eIn hF J).symm y).1.1 J ∧ ((KCactusCut_eIn hF J).symm y).1.1 ≠ J :=
    fun y => ((KCactusCut_eIn hF J).symm y).2
  have hJa : KLArcLe J J := ⟨le_rfl, le_rfl⟩
  constructor
  · rintro (_ | ⟨(y | s) | (y | s)⟩) (_ | ⟨(y' | s') | (y' | s')⟩) h <;>
      simp only [KCactusCut_Eb, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
    · rfl
    · exact absurd (by have e := congrArg Subtype.val h; rw [← e]; exact hJa) (hoc y')
    · exact absurd (congrArg Subtype.val h).symm (hic y').2
    · exact absurd (by have e := congrArg Subtype.val h; rw [e]; exact hJa) (hoc y)
    · exact congrArg (fun z => some (Sum.inl (Sum.inl z))) ((KCactusCut_eOut hF hn hJ).symm.injective (Subtype.ext h))
    · exact absurd (congrArg Subtype.val h ▸ (hic y').1) (hoc y)
    · exact congrArg (fun z => some (Sum.inl (Sum.inr z))) (KCactusCut_ψ_injective hF hn hJ h)
    · exact absurd h (KCactusCut_ψ_ne_φ hF hn hJ _ _)
    · exact absurd (congrArg Subtype.val h) (hic y).2
    · exact absurd (congrArg Subtype.val h ▸ (hic y).1) (hoc y')
    · exact congrArg (fun z => some (Sum.inr (Sum.inl z))) ((KCactusCut_eIn hF J).symm.injective (Subtype.ext h))
    · exact absurd h.symm (KCactusCut_ψ_ne_φ hF hn hJ _ _)
    · exact congrArg (fun z => some (Sum.inr (Sum.inr z))) (KCactusCut_φ_injective hF hn hJ h)
  · rintro (J' | x)
    · by_cases h2 : J'.1 = J
      · have hJ' : J' = ⟨J, hJ⟩ := Subtype.ext h2
        exact ⟨none, by rw [hJ']; rfl⟩
      · by_cases h1 : KLArcLe J'.1 J
        · exact ⟨some (Sum.inr (Sum.inl ((KCactusCut_eIn hF J) ⟨J', h1, h2⟩))), by
            simp only [KCactusCut_Eb, Equiv.symm_apply_apply]⟩
        · exact ⟨some (Sum.inl (Sum.inl ((KCactusCut_eOut hF hn hJ) ⟨J', h1⟩))), by
            simp only [KCactusCut_Eb, Equiv.symm_apply_apply]⟩
    · obtain ⟨y, rfl⟩ := (KCactusCut_eN hF hn hJ).surjective x
      rcases y with s | s
      · exact ⟨some (Sum.inl (Sum.inr s)), rfl⟩
      · exact ⟨some (Sum.inr (Sum.inr s)), rfl⟩

/-- **The relabelling of the edges of the cut**: `Option ((↥F_out ⊕ BAslot F_out) ⊕ (↥F_in ⊕ BAslot F_in)) ≃ ↥F ⊕ BAslot F`
(`none ↦` the chord `J`). -/
private noncomputable def KCactusCut_eE (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Option ((↥(KLFOut F J) ⊕ BAslot (KLFOut F J)) ⊕ (↥(KLFIn F J) ⊕ BAslot (KLFIn F J))) ≃ ↥F ⊕ BAslot F :=
  Equiv.ofBijective (KCactusCut_Eb hF hn hJ) (KCactusCut_Eb_bijective hF hn hJ)

end CutEquivs2

section CutLabels

variable {d L : ℕ} {n : ℕ} [NeZero n] {J : Fin n × Fin n}

omit [NeZero n] in
private theorem KCactusCut_val_add_one {m : ℕ} [NeZero m] (hm : 2 ≤ m) (v : Fin m) :
    (v + 1).val = (v.val + 1) % m := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m)]

private theorem KCactusCut_σIn_inV (σ : Fin n → Bool) {r : Fin n} (h1 : J.1 ≤ r) (h2 : r ≤ J.2) :
    sigmaIn σ J (KLinV J r) = σ r := by
  change σ (BAinVinv J (KLinV J r)) = σ r
  rw [KCactusCut_inVinv_inV h1 h2]

private theorem KCactusCut_σOut_outV (hJ : J.1.val + 2 ≤ J.2.val) (σ : Fin n → Bool) {r : Fin n}
    (h : r.val ≤ J.1.val ∨ J.2.val ≤ r.val) : sigmaOut σ J (KLoutV J r) = σ r := by
  change σ (BAoutVinv J (KLoutV J r)) = σ r
  rw [KCactusCut_outVinv_outV hJ h]

private theorem KCactusCut_inVinv_succ (hJ : J.1.val < J.2.val) {v : Fin n} (hv : KLInArc J v) :
    BAinVinv J (KLinV J v + 1) = v + 1 := by
  have h1 := KLinV_val hv
  simp only [KLInArc, Fin.le_def, Fin.lt_def] at hv
  have := J.2.isLt
  have hw : 2 ≤ KLwIn J + 1 := by simp only [KLwIn]; omega
  refine Fin.ext ?_
  rw [KCactusCut_val_add_one (by omega : 2 ≤ n) v, KCactusCut_inVinv_val _ hJ, KCactusCut_val_add_one hw (KLinV J v), h1,
    Nat.mod_eq_of_lt (by simp only [KLwIn]; omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem KCactusCut_outVinv_succ (hJ : J.1.val + 2 ≤ J.2.val) {v : Fin n} (hv : ¬KLInArc J v) :
    BAoutVinv J (KLoutV J v + 1) = v + 1 := by
  have hv' : v.val < J.1.val ∨ J.2.val ≤ v.val := by
    simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv; omega
  have hv1 := v.isLt
  have := J.2.isLt
  have hp : 2 ≤ n - KLwIn J + 1 := by simp only [KLwIn]; omega
  refine Fin.ext ?_
  have hkv : (KLoutV J v + 1).val = (KLcol J v.val + 1) % (n - KLwIn J + 1) := by
    rw [KCactusCut_val_add_one hp, KLoutV_val (J := J) v (by omega)]
  change min (KLunCol J (KLoutV J v + 1).val) (n - 1) = (v + 1).val
  rw [KCactusCut_val_add_one (by omega : 2 ≤ n) v, hkv]
  rcases hv' with h1 | h1
  · have hc1 : KLcol J v.val = v.val := KLcol_of_le (by omega)
    have hm : (KLcol J v.val + 1) % (n - KLwIn J + 1) = v.val + 1 := by
      rw [hc1]; exact Nat.mod_eq_of_lt (by simp only [KLwIn]; omega)
    rw [hm, KLunCol_of_le (by omega), Nat.mod_eq_of_lt (by omega : v.val + 1 < n)]
    omega
  · have hc1 : KLcol J v.val = v.val - (KLwIn J - 1) := KLcol_of_gt (by omega)
    by_cases h2 : v.val + 1 < n
    · have hm : (KLcol J v.val + 1) % (n - KLwIn J + 1) = KLcol J v.val + 1 :=
        Nat.mod_eq_of_lt (by rw [hc1]; simp only [KLwIn]; omega)
      rw [hm, KLunCol_of_gt (by rw [hc1]; simp only [KLwIn]; omega), Nat.mod_eq_of_lt h2, hc1]
      simp only [KLwIn]; omega
    · have h3 : v.val + 1 = n := by omega
      have hm : (KLcol J v.val + 1) % (n - KLwIn J + 1) = 0 := by
        rw [hc1, show v.val - (KLwIn J - 1) + 1 = n - KLwIn J + 1 by simp only [KLwIn]; omega]
        exact Nat.mod_self _
      rw [hm, KLunCol_of_le (by omega), h3, Nat.mod_self]
      simp

omit [NeZero n] in
private theorem KCactusCut_Theta_swap {L : ℕ} [NeZero L] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (s s' : Bool) :
    BAThetaOf M t s' s = (BAThetaOf M t s s')ᵀ := by
  have hQ : BAMssOf M s' s = (BAMssOf M s s')ᵀ := by
    ext a b
    simp only [BAMssOf, Matrix.of_apply, Matrix.transpose_apply, mul_comm]
  unfold BAThetaOf PropThetaQ
  rw [hQ, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]

end CutLabels

section CutMain

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

/-- The charge of the `M`-edge of a slot of the outer polygon is the charge of the `M`-edge of its image. -/
private theorem KCactusCut_charge_out (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (σ : Fin n → Bool)
    (s : BAslot (KLFOut F J)) :
    BAMcharge F σ (KCactusCut_ψ hF hn hJ s) = BAMcharge (KLFOut F J) (sigmaOut σ J) s := by
  have hJw := KLdiag_width hF hJ
  simp only [BAMcharge_def]
  rw [← KCactusCut_ψ_next hF hn hJ s]
  obtain ⟨h1, h2⟩ := KCactusCut_ψ_start hF hn hJ (BAnextSlot (KLFOut F J) s)
  rw [h1, KCactusCut_σOut_outV hJw σ h2]

/-- The charge of the `M`-edge of a slot of the inner polygon is the charge of the `M`-edge of its image. -/
private theorem KCactusCut_charge_in (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (σ : Fin n → Bool)
    (s : BAslot (KLFIn F J)) :
    BAMcharge F σ (KCactusCut_φ hF hJ s) = BAMcharge (KLFIn F J) (sigmaIn σ J) s := by
  simp only [BAMcharge_def]
  rw [← KCactusCut_φ_next hF hn hJ s]
  obtain ⟨h1, h2, h3⟩ := KCactusCut_φ_start hF hJ (BAnextSlot (KLFIn F J) s)
  rw [h1, KCactusCut_σIn_inV σ h2 h3]

end CutMain

/-! ## 6. The pieces of the cut -/

section CutParts

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

private theorem KCactusCut_inVinv_last (hJ : J.1.val < J.2.val) : BAinVinv J (Fin.last _) = J.2 := by
  refine Fin.ext ?_
  have := J.2.isLt
  simp only [BAinVinv, Fin.val_last, KLwIn]
  omega

private theorem KCactusCut_inVinv_zero (_hJ : J.1.val < J.2.val) : BAinVinv J 0 = J.1 := by
  refine Fin.ext ?_
  have := J.1.isLt
  simp only [BAinVinv, Fin.val_zero]
  omega

private theorem KCactusCut_outVinv_glue (hJ : J.1.val + 2 ≤ J.2.val) : BAoutVinv J (KLglueV J) = J.1 := by
  refine Fin.ext ?_
  have := J.1.isLt
  simp only [BAoutVinv, KCactusCut_glueV_val hJ, KLunCol_of_le (le_refl _)]
  omega

private theorem KCactusCut_outVinv_glue_succ (hJ : J.1.val + 2 ≤ J.2.val) :
    BAoutVinv J (KLglueV J + 1) = J.2 := by
  refine Fin.ext ?_
  have h2 := J.2.isLt
  have hp : 2 ≤ n - KLwIn J + 1 := by simp only [KLwIn]; omega
  have hv : (KLglueV J + 1).val = J.1.val + 1 := by
    rw [KCactusCut_val_add_one hp, KCactusCut_glueV_val hJ]
    exact Nat.mod_eq_of_lt (by simp only [KLwIn]; omega)
  change min (KLunCol J (KLglueV J + 1).val) (n - 1) = J.2.val
  rw [hv, KLunCol_of_gt (by omega)]
  simp only [KLwIn]
  omega

/-- The charges of the ends of a chord inside `J` in the inner polygon are those of the chord in the `n`-gon. -/
private theorem KCactusCut_chord_in (hF : KLIsTSP F) (σ : Fin n → Bool) (y : ↥(KLFIn F J)) :
    sigmaIn σ J y.1.1 = σ ((KCactusCut_eIn hF J).symm y).1.1.1 ∧
      sigmaIn σ J y.1.2 = σ ((KCactusCut_eIn hF J).symm y).1.1.2 := by
  obtain ⟨h1, -, h3⟩ := KCactusCut_inChord hF ((KCactusCut_eIn hF J).symm y)
  have hy := KCactusCut_eIn_symm hF y
  have e1 : y.1.1 = KLinV J ((KCactusCut_eIn hF J).symm y).1.1.1 := (congrArg Prod.fst hy).symm
  have e2 : y.1.2 = KLinV J ((KCactusCut_eIn hF J).symm y).1.1.2 := (congrArg Prod.snd hy).symm
  rw [e1, e2]
  exact ⟨KCactusCut_σIn_inV σ h1.1 (le_trans (le_of_lt h3) h1.2), KCactusCut_σIn_inV σ (le_trans h1.1 (le_of_lt h3)) h1.2⟩

/-- The charges of the ends of a chord outside `J` in the outer polygon are those of the chord in the `n`-gon. -/
private theorem KCactusCut_chord_out (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (σ : Fin n → Bool)
    (y : ↥(KLFOut F J)) :
    sigmaOut σ J y.1.1 = σ ((KCactusCut_eOut hF hn hJ).symm y).1.1.1 ∧
      sigmaOut σ J y.1.2 = σ ((KCactusCut_eOut hF hn hJ).symm y).1.1.2 := by
  have hJw := KLdiag_width hF hJ
  have hE := KCactusCut_outChord hF hn hJ ((KCactusCut_eOut hF hn hJ).symm y)
  have hy := KCactusCut_eOut_symm hF hn hJ y
  have e1 : y.1.1 = KLoutV J ((KCactusCut_eOut hF hn hJ).symm y).1.1.1 := (congrArg Prod.fst hy).symm
  have e2 : y.1.2 = KLoutV J ((KCactusCut_eOut hF hn hJ).symm y).1.1.2 := (congrArg Prod.snd hy).symm
  rw [e1, e2]
  exact ⟨KCactusCut_σOut_outV hJw σ hE.1, KCactusCut_σOut_outV hJw σ hE.2.1⟩

/-- `BAdeltaIn` is `u` at the new leaf and `f` at the leaves of the arc (through the leaf bijection `eLin`). -/
private theorem KCactusCut_delta_in {α : Type*} (hJ : J.1.val + 2 ≤ J.2.val) (f : Fin n → α) (x : α)
    (o : Option (KLLIn J)) : BAdeltaIn J f x (KCactusCut_eLin J hJ o) = o.elim x (fun v => f v.1) := by
  rcases o with _ | v
  · change BAdeltaIn J f x (Fin.last _) = x
    simp [BAdeltaIn]
  · have hlt : (KLinV J v.1).val < KLwIn J := by
      have := KLinV_val v.2
      have h2 := v.2
      simp only [KLInArc, Fin.le_def, Fin.lt_def] at h2
      simp only [KLwIn]; omega
    change BAdeltaIn J f x (KLinV J v.1) = f v.1
    simp only [BAdeltaIn]
    rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega),
      KCactusCut_inVinv_inV v.2.1 (le_of_lt v.2.2)]

/-- `BAdeltaOut` is `x` at the glue leaf and `f` at the leaves off the arc (through the leaf bijection `eLout`). -/
private theorem KCactusCut_delta_out {α : Type*} (hJ : J.1.val + 2 ≤ J.2.val) (f : Fin n → α) (x : α)
    (o : Option (KLLOut J)) : BAdeltaOut J f x (KCactusCut_eLout J hJ o) = o.elim x (fun v => f v.1) := by
  have hv : ∀ v : KLLOut J, v.1.val ≤ J.1.val ∨ J.2.val ≤ v.1.val := fun v => by
    have := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this
    omega
  rcases o with _ | v
  · change BAdeltaOut J f x (KLglueV J) = x
    simp [BAdeltaOut]
  · change BAdeltaOut J f x (KLoutV J v.1) = f v.1
    simp only [BAdeltaOut]
    rw [Function.update_of_ne (KCactusCut_outV_ne_glue hJ v.2), KCactusCut_outVinv_outV hJ (hv v)]

/-- **The inner part of the cut is the inner polygon with the data `BAdeltaIn`** (any edge weights and ends). -/
private theorem KCactusCut_in_part {d L : ℕ} [NeZero L] (hJ : J.1.val + 2 ≤ J.2.val)
    {G : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))} {Ed : Type*} [Fintype Ed]
    (E : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → BAslot G) (a : Fin n → Zd d L)
    (Lw : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (u : Zd d L) (P : Matrix (Zd d L) (Zd d L) ℂ) :
    KLgval d L (fun o : Option (KLLIn J) => o.elim u fun v => a ↑v) (fun o => o.elim Pᵀ fun v => Lw ↑v)
        (fun o => o.elim (Sum.inl (Fin.last (KLwIn J))) fun v => Sum.inl (KLinV J ↑v)) E c q =
      KLgval d L (BAdeltaIn J a u) (BAdeltaIn J Lw Pᵀ) (BAslotLeaf G) E c q :=
  KLgval_congr (Equiv.refl _) (KCactusCut_eLin J hJ) (Equiv.refl _) (fun o => KCactusCut_delta_in hJ a u o)
    (fun o => KCactusCut_delta_in hJ Lw Pᵀ o) (fun o => by rcases o with _ | v <;> rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)

/-- **The outer part of the cut is the outer polygon with the data `BAdeltaOut`.** -/
private theorem KCactusCut_out_part {d L : ℕ} [NeZero L] (hJ : J.1.val + 2 ≤ J.2.val)
    {G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))} {Ed : Type*} [Fintype Ed]
    (E : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → BAslot G) (a : Fin n → Zd d L)
    (Lw : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (w : Zd d L) (Q : Matrix (Zd d L) (Zd d L) ℂ) :
    KLgval d L (fun o : Option (KLLOut J) => o.elim w fun v => a ↑v) (fun o => o.elim Q fun v => Lw ↑v)
        (fun o => o.elim (Sum.inl (KLglueV J)) fun v => Sum.inl (KLoutV J ↑v)) E c q =
      KLgval d L (BAdeltaOut J a w) (BAdeltaOut J Lw Q) (BAslotLeaf G) E c q :=
  KLgval_congr (Equiv.refl _) (KCactusCut_eLout J hJ) (Equiv.refl _) (fun o => KCactusCut_delta_out hJ a w o)
    (fun o => KCactusCut_delta_out hJ Lw Q o) (fun o => by rcases o with _ | v <;> rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

end CutParts

/-! ## 7. The cut theorem -/

section CutThm

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

set_option synthInstance.maxSize 512 in
/-- **The cut of the cactus of `F ∋ J` at the chord `J`, for arbitrary leaf weights `Lw` and an arbitrary chord weight `P S Q`**
(the generalisation of K05b's `KTreeRep_cut`, which is `Lw = Θ`, `P = Q = Θ`, `S = 1`): the tree value with the weight `P S Q`
at the chord is `Σ_{u,w} (inner polygon, labels `BAdeltaIn J a u`, leaf weights `BAdeltaIn J Lw Pᵀ`) `S_{uw}` (outer polygon,
labels `BAdeltaOut J a w`, leaf weights `BAdeltaOut J Lw Q`).  The charges of the polygons are `sigmaIn σ J`, `sigmaOut σ J`.
`KLgval_split` after the relabelling `BAslot F_out ⊕ BAslot F_in ≃ BAslot F` of the slots, which preserves the cycles. -/
theorem baCactus_cut (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L)
    (Lw : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (P S Q : Matrix (Zd d L) (Zd d L) ℂ) :
    KLgval d L (Nd := BAslot F) (Lf := Fin n) a Lw (BAslotLeaf F)
      (Function.update (BACactusValEdgeW M t F σ) (Sum.inl ⟨J, hJ⟩) (P * S * Q))
      (BACactusValSrc F) (BACactusValTgt F) =
    ∑ u : Zd d L, ∑ w : Zd d L,
      KLgval d L (Nd := BAslot (KLFIn F J)) (Lf := Fin (KLwIn J + 1)) (BAdeltaIn J a u) (BAdeltaIn J Lw Pᵀ)
        (BAslotLeaf (KLFIn F J)) (BACactusValEdgeW M t (KLFIn F J) (sigmaIn σ J))
        (BACactusValSrc (KLFIn F J)) (BACactusValTgt (KLFIn F J)) * S u w *
      KLgval d L (Nd := BAslot (KLFOut F J)) (Lf := Fin (n - KLwIn J + 1)) (BAdeltaOut J a w) (BAdeltaOut J Lw Q)
        (BAslotLeaf (KLFOut F J)) (BACactusValEdgeW M t (KLFOut F J) (sigmaOut σ J))
        (BACactusValSrc (KLFOut F J)) (BACactusValTgt (KLFOut F J)) := by
  have hJw := KLdiag_width hF hJ
  have hb := KCactusCut_wbounds hF hJ
  have key := KLgval_split (d := d) (L := L)
    (fun v : KLLOut J => a v.1) (fun v => Lw v.1)
    (fun v => (Sum.inl (KLoutV J v.1) : BAslot (KLFOut F J)))
    (BACactusValEdgeW M t (KLFOut F J) (sigmaOut σ J)) (BACactusValSrc (KLFOut F J))
    (BACactusValTgt (KLFOut F J))
    (fun v : KLLIn J => a v.1) (fun v => Lw v.1)
    (fun v => (Sum.inl (KLinV J v.1) : BAslot (KLFIn F J)))
    (BACactusValEdgeW M t (KLFIn F J) (sigmaIn σ J)) (BACactusValSrc (KLFIn F J))
    (BACactusValTgt (KLFIn F J)) P S Q
    (Sum.inl (Fin.last _) : BAslot (KLFIn F J)) (Sum.inl (KLglueV J) : BAslot (KLFOut F J))
  refine ((KLgval_congr (KCactusCut_eN hF hn hJ) (KCactusCut_eL J) (KCactusCut_eE hF hn hJ)
    ?_ ?_ ?_ ?_ ?_ ?_).symm.trans key).trans ?_
  · rintro (v | v) <;> rfl
  · rintro (v | v) <;> rfl
  · rintro (v | v)
    · have hv' : v.1.val ≤ J.1.val ∨ J.2.val ≤ v.1.val := by
        have := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this
        omega
      change (Sum.inl v.1 : BAslot F) = KCactusCut_ψ hF hn hJ (Sum.inl (KLoutV J v.1))
      rw [KCactusCut_ψ_leaf hF hn hJ _ (KCactusCut_outV_ne_glue hJw v.2), KCactusCut_outVinv_outV hJw hv']
    · have hlt : (KLinV J v.1).val < KLwIn J := by
        have := KLinV_val v.2
        have h2 := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def] at h2
        simp only [KLwIn]; omega
      change (Sum.inl v.1 : BAslot F) = KCactusCut_φ hF hJ (Sum.inl (KLinV J v.1))
      rw [KCactusCut_φ_leaf hF hJ _ hlt, KCactusCut_inVinv_inV v.2.1 (le_of_lt v.2.2)]
  · rintro (_ | ⟨(y | s) | (y | s)⟩)
    · change Function.update _ (Sum.inl (⟨J, hJ⟩ : ↥F)) _ (Sum.inl (⟨J, hJ⟩ : ↥F)) = _
      rw [Function.update_self]
      rfl
    · have hne : (Sum.inl ((KCactusCut_eOut hF hn hJ).symm y).1 : ↥F ⊕ BAslot F) ≠ (Sum.inl (⟨J, hJ⟩ : ↥F) : ↥F ⊕ BAslot F) :=
        fun h => ((KCactusCut_eOut hF hn hJ).symm y).2 (by
          have := congrArg Subtype.val (Sum.inl.inj h)
          simp only at this
          rw [this]; exact ⟨le_rfl, le_rfl⟩)
      change Function.update _ _ _ (Sum.inl ((KCactusCut_eOut hF hn hJ).symm y).1) = _
      rw [Function.update_of_ne hne]
      change (t : ℂ) • BAThetaOf M t (σ _) (σ _) = (t : ℂ) • BAThetaOf M t (sigmaOut σ J y.1.1) (sigmaOut σ J y.1.2)
      rw [(KCactusCut_chord_out hF hn hJ σ y).1, (KCactusCut_chord_out hF hn hJ σ y).2]
    · change Function.update _ _ _ (Sum.inr (KCactusCut_ψ hF hn hJ s)) = _
      rw [Function.update_of_ne (by simp)]
      change M (BAMcharge F σ (KCactusCut_ψ hF hn hJ s)) = M (BAMcharge (KLFOut F J) (sigmaOut σ J) s)
      rw [KCactusCut_charge_out hF hn hJ σ s]
    · have hne : (Sum.inl ((KCactusCut_eIn hF J).symm y).1 : ↥F ⊕ BAslot F) ≠ (Sum.inl (⟨J, hJ⟩ : ↥F) : ↥F ⊕ BAslot F) :=
        fun h => ((KCactusCut_eIn hF J).symm y).2.2 (congrArg Subtype.val (Sum.inl.inj h))
      change Function.update _ _ _ (Sum.inl ((KCactusCut_eIn hF J).symm y).1) = _
      rw [Function.update_of_ne hne]
      change (t : ℂ) • BAThetaOf M t (σ _) (σ _) = (t : ℂ) • BAThetaOf M t (sigmaIn σ J y.1.1) (sigmaIn σ J y.1.2)
      rw [(KCactusCut_chord_in hF σ y).1, (KCactusCut_chord_in hF σ y).2]
    · change Function.update _ _ _ (Sum.inr (KCactusCut_φ hF hJ s)) = _
      rw [Function.update_of_ne (by simp)]
      change M (BAMcharge F σ (KCactusCut_φ hF hJ s)) = M (BAMcharge (KLFIn F J) (sigmaIn σ J) s)
      rw [KCactusCut_charge_in hF hn hJ σ s]
  · rintro (_ | ⟨(y | s) | (y | s)⟩)
    · exact (KCactusCut_φ_last hF hJ _ (by simp)).symm
    all_goals rfl
  · rintro (_ | ⟨(y | s) | (y | s)⟩)
    · exact (KCactusCut_ψ_glue hF hn hJ).symm
    · rfl
    · exact (KCactusCut_ψ_next hF hn hJ s).symm
    · rfl
    · exact (KCactusCut_φ_next hF hn hJ s).symm
  · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    rw [KCactusCut_in_part hJw _ _ _ a Lw u P, KCactusCut_out_part hJw _ _ _ a Lw w Q]

end CutThm

/-! ## 8. The leaf weights of the two polygons for `Lw = Θ` (for the cut of the `K`-level values) -/

section LeafW

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **The leaf weights of the inner polygon at `Lw = Θ`**: with `P = Θ^{(σ_i,σ_j)}` the new leaf carries
`Pᵀ = Θ^{(σ_j,σ_i)}` (`KCactusCut_Theta_swap`, any `M`) and the polygon has its own leaf weights
`Θ^{(σ'_k,σ'_{k+1})}`, `σ' = sigmaIn σ J`: `baCactus_cut` at `Lw = BACactusValLeafW M t σ` is a cut into cacti. -/
theorem baCactus_leafW_in (hJ : J.1.val + 2 ≤ J.2.val) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (σ : Fin n → Bool) :
    BAdeltaIn J (BACactusValLeafW M t σ) (BAThetaOf M t (σ J.1) (σ J.2))ᵀ =
      BACactusValLeafW M t (sigmaIn σ J) := by
  have hJ2 : J.1.val < J.2.val := by omega
  funext k
  by_cases hk : k.val < KLwIn J
  · have hv : KLInArc J (BAinVinv J k) := by
      have := KCactusCut_inVinv_val k hJ2
      simp only [KLInArc, Fin.le_def, Fin.lt_def, this]
      simp only [KLwIn] at hk
      omega
    have hs : BAinVinv J (k + 1) = BAinVinv J k + 1 := by
      have := KCactusCut_inVinv_succ hJ2 hv
      rwa [KCactusCut_inV_inVinv k hJ2] at this
    simp only [BAdeltaIn]
    rw [Function.update_of_ne (fun h => by have := congrArg Fin.val h; simp at this; omega)]
    change BAThetaOf M t (σ (BAinVinv J k)) (σ (BAinVinv J k + 1)) =
      BAThetaOf M t (σ (BAinVinv J k)) (σ (BAinVinv J (k + 1)))
    rw [hs]
  · have hkl : k = Fin.last _ := Fin.ext (by have := k.isLt; simp only [Fin.val_last]; omega)
    subst hkl
    simp only [BAdeltaIn, Function.update_self, BACactusValLeafW, Fin.last_add_one]
    change _ = BAThetaOf M t (σ (BAinVinv J (Fin.last _))) (σ (BAinVinv J 0))
    rw [KCactusCut_inVinv_last hJ2, KCactusCut_inVinv_zero hJ2, ← KCactusCut_Theta_swap]

/-- **The leaf weights of the outer polygon at `Lw = Θ`**: with `Q = Θ^{(σ_i,σ_j)}` the glue leaf carries
`Θ^{(σ'_{glue},σ'_{glue+1})}`, `σ' = sigmaOut σ J`, and the other leaves keep their weights. -/
theorem baCactus_leafW_out (hJ : J.1.val + 2 ≤ J.2.val) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (σ : Fin n → Bool) :
    BAdeltaOut J (BACactusValLeafW M t σ) (BAThetaOf M t (σ J.1) (σ J.2)) =
      BACactusValLeafW M t (sigmaOut σ J) := by
  funext k
  by_cases hk : k = KLglueV J
  · subst hk
    simp only [BAdeltaOut, Function.update_self, BACactusValLeafW]
    change _ = BAThetaOf M t (σ (BAoutVinv J (KLglueV J))) (σ (BAoutVinv J (KLglueV J + 1)))
    rw [KCactusCut_outVinv_glue hJ, KCactusCut_outVinv_glue_succ hJ]
  · have hv := KCactusCut_outVinv_outer hJ hk
    have hs : BAoutVinv J (k + 1) = BAoutVinv J k + 1 := by
      have := KCactusCut_outVinv_succ hJ hv
      rwa [KCactusCut_outV_outVinv hJ k] at this
    simp only [BAdeltaOut]
    rw [Function.update_of_ne hk]
    change BAThetaOf M t (σ (BAoutVinv J k)) (σ (BAoutVinv J k + 1)) =
      BAThetaOf M t (σ (BAoutVinv J k)) (σ (BAoutVinv J (k + 1)))
    rw [hs]

end LeafW

/-! ## 9. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`), `t = 1/2`, `n = 4`
(`TSP 4 = {∅, {(0,2)}, {(1,3)}}`: the cut at `J = (0,2)` of the tree `{(0,2)}` has an inner and an outer triangle),
the charges `σ = (+,+,-,+)`, four distinct labels.  `baCactus_cut` has no hypothesis on `M`, `t`, the leaf weights or `P S Q`. -/

namespace KCactusCutInst

open RBM.BA.MFixedPointInst

private theorem KCactusCut_isTSP_F02 :
    KLIsTSP ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) :=
  KLisTSP_of_mem_TSP (by rw [TSP_four]; simp)

/-- **`baCactus_cut`** at the flow point, `F = {(0,2)}`, `J = (0,2)`, the leaf weights `Θ^{(σ_v,σ_{v+1})}`, the chord weight
`Θ · 1 · Θ` with `Θ = Θ^{(+,-)}` (the chord term of K05b), four distinct labels. -/
example :=
  baCactus_cut (d := 3) (L := 4) (F := {((0 : Fin 4), (2 : Fin 4))}) (J := ((0 : Fin 4), (2 : Fin 4)))
    KCactusCut_isTSP_F02 (by norm_num) (Finset.mem_singleton_self _)
    (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]
    (BACactusValLeafW (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true])
    (BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) true false) 1
    (BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) true false)

/-- **`baCactus_leafW_in`, `baCactus_leafW_out`** at the same cut `J = (0,2)` of the square. -/
example := baCactus_leafW_in (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num)
  (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]

example := baCactus_leafW_out (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num)
  (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]

end KCactusCutInst

end RBM.BA
