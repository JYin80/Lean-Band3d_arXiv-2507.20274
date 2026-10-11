/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAScost
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAExpandW

/-!
# BA-L R1 `BASim`: the matching of a BA step with a band `LocStep` at the atomic image (T2423), part 1

Scratch skeleton.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open private lwExists_mem_dedupPairs lwMem_of_mem_dedupPairs from RBM3D.Graph.LWVocab
open private BAVocab_vmap_injective BAVocab_vmap_surjective BAVocab_merge_atomAdj BAVocab_merge_dotted_eq from RBM3D.Graph.BAVocab

noncomputable section

namespace RBM.Graph

open RBM

/-! ## 1. The frame vocabulary (`t/T2423:RBM3D/Probe/T2423Pins.lean:19-139`; `BAShape`, `BTStep`, `untag` are those of `Graph/BAScost.lean`) -/

section Frame
variable {E : Type}
/-- the outputs of a step: the BA partition of every term, packed and read through `P.ext` (T2395 probe 154). -/
def BAPGraph.outsOf (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')) : List (BAPGraph E) :=
  Ts.flatMap fun T => T.partition.map fun Q =>
    { E' := Q.E', I' := Q.I', ext := Q.ext ∘ P.ext, ext_surj := Q.ext_surj.comp P.ext_surj, g := Q.g }
/-- macro step (a) (T2395 probe 160). -/
def BAPGraph.withinOuts (P : BAPGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) : List (BAPGraph E) :=
  let Γ := P.g; let e : SEdge (P.E' ⊕ (P.I' ⊕ Fin 2)) := bpS true (bpv 1) (bpv 1)
  let tr := BAGraph.ext 2 Γ p.2 [e] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]
  let pp := (e, p.2.map (SEdge.map (owxEmb 2)))
  P.outsOf (BAGraph.ext 2 Γ p.2 [e, bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] ::
      (lwSplit p.2).map (BAGraph.lanlwD Γ p)) ++ P.outsOf (tr.lw2 pp) ++ P.outsOf (tr.lw4 pp)
/-- macro step (b) (T2395 probe 168). -/
def BAPGraph.splitOuts (P : BAPGraph E) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (j : ℕ) : List (BAPGraph E) :=
  let Γ := P.g; let y := owxEmb 2 p.1.dst; let y' := owxEmb 2 q.1.src; let a := owxEmb 2 p.1.src; let a' := owxEmb 2 q.1.dst
  let dq (s : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin 2)))) (md : List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin 2)))) : BAGraph P.E' (P.I' ⊕ Fin 2) :=
    BAGraph.ext 2 Γ q.2 s [bpW false (bpv 0) (bpv 1)] (bpM a (bpv 0) :: md)
  let R := q.2.map (SEdge.map (owxEmb 2))
  let tr := dq [bpS true y' (bpv 1), bpS true (bpv 1) y] [bpM (bpv 0) a']
  P.outsOf (BAGraph.lanlwT1 Γ p :: ((lwSplit p.2).eraseIdx j).map (BAGraph.lanlwD Γ p)) ++
    P.outsOf [dq [bpS false y' (bpv 1), bpS true (bpv 0) a', bpS false (bpv 1) y] [],
      dq [bpS true y' (bpv 1)] [bpM (bpv 0) a', bpM (bpv 1) y], dq [bpS true (bpv 1) y] [bpM (bpv 0) a', bpM y' (bpv 1)],
      dq [] [bpM (bpv 0) a', bpM y' (bpv 1), bpM (bpv 1) y]] ++
    P.outsOf (tr.gg2 (bpS true (bpv 1) y, R ++ [bpS true y' (bpv 1)]) (bpS true y' (bpv 1), R)) ++
    P.outsOf (tr.gg4 (bpS true (bpv 1) y, R ++ [bpS true y' (bpv 1)]) (bpS true y' (bpv 1), R))
/-- **One step of the BA strategy in the frame** (T2395 probe 182): the five kinds, the selected edge blue and circled. -/
inductive BAFrameStep : BAPGraph E → List (BAPGraph E) → Prop
  | weight (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
      BAFrameStep P (P.outsOf (P.g.lw2 p) ++ P.outsOf (P.g.lw4 p))
  | within (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid)
      (h : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src ≠ p.1.dst ∧ P.g.sameAtom p.1.src p.1.dst = true) :
      BAFrameStep P (P.withinOuts p)
  | edge (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true) (x : P.I') (hx : p.1.src = Sum.inr x)
      (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false) (hv : P.g.sameAtom p.1.src p.1.dst = false)
      (hint : P.g.intAtom (Sum.inr x) = true)
      (hbad : P.g.atEdges (Sum.inr x) ≠ [] ∧ ((P.g.atEdges (Sum.inr x)).length ≠ 2 ∨ P.g.atCharge (Sum.inr x) ≠ 0)) :
      BAFrameStep P (P.outsOf (BAGraph.lanlwTerms P.g p))
  | gg (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid) (q) (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true)
      (x : P.I') (hx : p.1.src = Sum.inr x ∧ q.1.dst = Sum.inr x) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
      (hint : P.g.intAtom (Sum.inr x) = true)
      (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
        ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0)) :
      BAFrameStep P (P.outsOf (P.g.gg2 p q) ++ P.outsOf (P.g.gg4 p q))
  | ggSplit (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid) (q) (j : ℕ) (hj : (lwSplit p.2)[j]? = some q)
      (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) (a a' : P.I') (hx : p.1.src = Sum.inr a ∧ q.1.dst = Sum.inr a')
      (hne : a ≠ a') (hsame : P.g.sameAtom (Sum.inr a) (Sum.inr a') = true) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
      (hint : P.g.intAtom (Sum.inr a) = true)
      (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
        ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0)) :
      BAFrameStep P (P.splitOuts p q j)
end Frame
section Tag
variable {E : Type}
/-- **`T'` is extra for the parent `Γ`**: the `M`-splits of the term merge two atoms of `Γ` that a solid edge of `Γ` joins (`emb` embeds the vertices of `Γ`; the band's `×`-dot forbids it). -/
def BAGraph.extraB {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (Γ : BAGraph E I) (emb : E ⊕ I → E ⊕ I') (T' : BAGraph E I') : Bool :=
  Γ.solid.any fun e => !Γ.sameAtom e.src e.dst && T'.sameAtom (emb e.src) (emb e.dst)
/-- the outputs of a step as `outsOf`, each with the tag `tg T'` of the `M`-split `T'` of the term `T` it comes from. -/
def BAPGraph.outsT (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape) (Ts : List (BAGraph P.E' I')) :
    List (BAShape × BAPGraph E) :=
  Ts.flatMap fun T => T.splitG.map fun T' =>
    (tg T', let Q := T'.packMerge; { E' := Q.E', I' := Q.I', ext := Q.ext ∘ P.ext, ext_surj := Q.ext_surj.comp P.ext_surj, g := Q.g })
/-- the tag of a stage-1 output: `e2` if it is extra, else `band`; `tagT1` (the first term of `lanlw`, `M_{αy}`) tags the extra ones `e1`. -/
def BAGraph.tagStd {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (k : ℕ) (T' : BAGraph E (I ⊕ Fin k)) : BAShape :=
  if Γ.extraB (owxEmb k) T' then .e2 else .band
def BAGraph.tagT1 {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (T' : BAGraph E (I ⊕ Fin 2)) : BAShape :=
  if Γ.extraB (owxEmb 2) T' then .e1 else .band
/-- macro (a) with tags: stage 1 by extra-ness, every output of stage 2 (`lem_lweight` at the transfer loop) `macroA`. -/
def BAPGraph.withinOutsT (P : BAPGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) : List (BAShape × BAPGraph E) :=
  let Γ := P.g; let e : SEdge (P.E' ⊕ (P.I' ⊕ Fin 2)) := bpS true (bpv 1) (bpv 1)
  let tr := BAGraph.ext 2 Γ p.2 [e] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]
  let pp := (e, p.2.map (SEdge.map (owxEmb 2)))
  P.outsT (P.g.tagStd 2) (BAGraph.ext 2 Γ p.2 [e, bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] ::
      (lwSplit p.2).map (BAGraph.lanlwD Γ p)) ++ P.outsT (fun _ => .macroA) (tr.lw2 pp) ++ P.outsT (fun _ => .macroA) (tr.lw4 pp)
/-- macro (b) with tags: `lanlw` and `d1` by extra-ness, the transfer-family terms `d2, d3, d4` and every output of stage 2 (`GGGamma` at `β`) `macroB`. -/
def BAPGraph.splitOutsT (P : BAPGraph E) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (j : ℕ) : List (BAShape × BAPGraph E) :=
  let Γ := P.g; let y := owxEmb 2 p.1.dst; let y' := owxEmb 2 q.1.src; let a := owxEmb 2 p.1.src; let a' := owxEmb 2 q.1.dst
  let dq (s : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin 2)))) (md : List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin 2)))) : BAGraph P.E' (P.I' ⊕ Fin 2) :=
    BAGraph.ext 2 Γ q.2 s [bpW false (bpv 0) (bpv 1)] (bpM a (bpv 0) :: md)
  let R := q.2.map (SEdge.map (owxEmb 2))
  let tr := dq [bpS true y' (bpv 1), bpS true (bpv 1) y] [bpM (bpv 0) a']
  P.outsT P.g.tagT1 [BAGraph.lanlwT1 Γ p] ++ P.outsT (P.g.tagStd 2) (((lwSplit p.2).eraseIdx j).map (BAGraph.lanlwD Γ p)) ++
    P.outsT (P.g.tagStd 2) [dq [bpS false y' (bpv 1), bpS true (bpv 0) a', bpS false (bpv 1) y] []] ++
    P.outsT (fun _ => .macroB) [dq [bpS true y' (bpv 1)] [bpM (bpv 0) a', bpM (bpv 1) y], dq [bpS true (bpv 1) y] [bpM (bpv 0) a', bpM y' (bpv 1)],
      dq [] [bpM (bpv 0) a', bpM y' (bpv 1), bpM (bpv 1) y]] ++
    P.outsT (fun _ => .macroB) (tr.gg2 (bpS true (bpv 1) y, R ++ [bpS true y' (bpv 1)]) (bpS true y' (bpv 1), R)) ++
    P.outsT (fun _ => .macroB) (tr.gg4 (bpS true (bpv 1) y, R ++ [bpS true y' (bpv 1)]) (bpS true y' (bpv 1), R))
/-- **The tagged frame step**: the five constructors of `BAFrameStep` with the same hypotheses, the outputs tagged (`BAFrameStepT_untag` below). -/
inductive BAFrameStepT : BAPGraph E → List (BAShape × BAPGraph E) → Prop
  | weight (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
      BAFrameStepT P (P.outsT (P.g.tagStd 2) (P.g.lw2 p) ++ P.outsT (P.g.tagStd 4) (P.g.lw4 p))
  | within (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid)
      (h : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src ≠ p.1.dst ∧ P.g.sameAtom p.1.src p.1.dst = true) :
      BAFrameStepT P (P.withinOutsT p)
  | edge (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true) (x : P.I') (hx : p.1.src = Sum.inr x)
      (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false) (hv : P.g.sameAtom p.1.src p.1.dst = false)
      (hint : P.g.intAtom (Sum.inr x) = true)
      (hbad : P.g.atEdges (Sum.inr x) ≠ [] ∧ ((P.g.atEdges (Sum.inr x)).length ≠ 2 ∨ P.g.atCharge (Sum.inr x) ≠ 0)) :
      BAFrameStepT P (P.outsT P.g.tagT1 [BAGraph.lanlwT1 P.g p] ++ P.outsT (P.g.tagStd 2) ((lwSplit p.2).map (BAGraph.lanlwD P.g p)))
  | gg (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid) (q) (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true)
      (x : P.I') (hx : p.1.src = Sum.inr x ∧ q.1.dst = Sum.inr x) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
      (hint : P.g.intAtom (Sum.inr x) = true)
      (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
        ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0)) :
      BAFrameStepT P (P.outsT (P.g.tagStd 2) (P.g.gg2 p q) ++ P.outsT (P.g.tagStd 4) (P.g.gg4 p q))
  | ggSplit (P : BAPGraph E) (p) (hp : p ∈ lwSplit P.g.solid) (q) (j : ℕ) (hj : (lwSplit p.2)[j]? = some q)
      (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) (a a' : P.I') (hx : p.1.src = Sum.inr a ∧ q.1.dst = Sum.inr a')
      (hne : a ≠ a') (hsame : P.g.sameAtom (Sum.inr a) (Sum.inr a') = true) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
      (hint : P.g.intAtom (Sum.inr a) = true)
      (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
        ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0)) :
      BAFrameStepT P (P.splitOutsT p q j)
end Tag

/-! ## 2. Relabelling and the pins of R1 (probe 140-198); `BAEquivC`, `BAPGraph.twist` (Amend 1, O4) -/

section Pins
variable {E : Type}
/-- a waved edge, or its reversal (`WEdge.transpose`, `LWSymm.lean:96`). -/
def WEdge.sameRev {V : Type*} (a b : WEdge V) : Prop := a = b ∨ a.transpose = b
/-- two dotted edges with the same ends, unordered. -/
def DEdge.sameU {V : Type*} (a b : DEdge V) : Prop := a.eq = b.eq ∧ ((a.x = b.x ∧ a.y = b.y) ∨ (a.x = b.y ∧ a.y = b.x))
/-- **`R` is `S` up to relabelling** of the vertices (the external vertices keep their labels `ext`): the solid edges agree up to order, the waved edges
up to order and reversal of single edges (`LGraph.scost_perm`, `LocalRegular6a.lean:309`: `scost` sees the solid edges up to order and the number of waved edges; molecules read the symmetric `LGraph.adj`; `localReg2_cendsMS` reads `Sym2` ends), the `×`-dotted
edges as sets of unordered pairs; the coefficient is not read (it carries the powers of `m` of the band's partition). -/
def PGraph.BAEquiv (R S : PGraph E) : Prop :=
  ∃ (eE : R.E' ≃ S.E') (eI : R.I' ≃ S.I'), (∀ a, S.ext a = eE (R.ext a)) ∧
    List.Perm (R.g.relabel (Sum.map eE eI)).solid S.g.solid ∧
    (∃ l, List.Perm l (R.g.relabel (Sum.map eE eI)).waved ∧ List.Forall₂ WEdge.sameRev l S.g.waved) ∧
    (∀ d ∈ (R.g.relabel (Sum.map eE eI)).dotted, ∃ d' ∈ S.g.dotted, DEdge.sameU d d') ∧
    (∀ d ∈ S.g.dotted, ∃ d' ∈ (R.g.relabel (Sum.map eE eI)).dotted, DEdge.sameU d' d)
/-- the relation is nonempty: reflexive -/
example (R : PGraph E) : R.BAEquiv R := by
  have h : R.g.relabel (Sum.map (Equiv.refl R.E') (Equiv.refl R.I')) = R.g := by
    obtain ⟨s, w, d, c⟩ := R.g
    simp only [LGraph.relabel, Equiv.coe_refl, Sum.map_id_id, LGraph.mk.injEq, and_true]
    exact ⟨List.map_id'' (f := SEdge.map id) (fun e => by cases e; rfl) s, List.map_id'' (f := WEdge.map id) (fun e => by cases e; rfl) w,
      List.map_id'' (f := DEdge.map id) (fun e => by cases e; rfl) d⟩
  refine ⟨Equiv.refl _, Equiv.refl _, fun _ => rfl, ?_, ⟨_, ?_, List.forall₂_same.2 fun _ _ => Or.inl rfl⟩, fun d hd => ⟨d, ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩,
    fun d hd => ⟨d, ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  · rw [h]
  · rw [h]
  · rwa [h] at hd
  · rw [h]; exact hd
/-- **Item 1 (R1, L4-C1): the graph-level matching, up to relabelling.**  At a normal BA graph `P`, every `band`-tagged output `Q` of a frame step is, up to
relabelling, an output of a band `LocStep m` at the atomic image `P.img` (R0).  The band step is chosen per output: one `nat` step serves all `band` outputs of
`weight`, `within`, `edge`, `ggSplit`; at `gg` the mirror `A2` needs the swapped selector, so no single step serves all (T2423 (a) T1, T3).  Frame level: the twisted `BALocStep` is this at `P.twist c t`, a normal BA graph (L3a1, T2425). -/
def BAMatch (m : ℂ) : Prop := ∀ {E : Type} (P : BAPGraph E) (LT : List (BAShape × BAPGraph E)), BAFrameStepT P LT → P.g.Normal →
  ∀ Q, (BAShape.band, Q) ∈ LT → ∃ L' : List (PGraph E), LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img
/-- **Lemma E at graph level** (closes T2395 audit O1): an output that merges two atoms of `P` joined by a solid edge of `P` (tags `e1`, `e2`) has a higher
order, or fewer external atoms, than `P`. -/
def BAExtraGood : Prop := ∀ {E : Type} (P : BAPGraph E) (LT : List (BAShape × BAPGraph E)), BAFrameStepT P LT → P.g.Normal →
  ∀ Q, (BAShape.e1, Q) ∈ LT ∨ (BAShape.e2, Q) ∈ LT → P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt
/-- the tagged step is the step with its outputs tagged. -/
def BAFrameStepT_untag : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)),
  BAFrameStep P outs ↔ ∃ LT, BAFrameStepT P LT ∧ outs = LT.map Prod.snd
/-- **S′, the simulation** (`t/T2395:RBM3D/Probe/T2395Pins.lean:263`, verbatim): per output, the invariant tuple of an output of a band step at `P.img`, or the order
rises, or the number of external atoms falls.  True on the samples (T2423 (a): 53,624 outputs, 0 fails), but for the macro outputs not derivable from `BAMatch`. -/
def BAsim (m : ℂ) : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal →
  ∀ Q ∈ outs, (∃ outsπ : List (PGraph E), LocStep m P.img outsπ ∧ ∃ Q0 ∈ outsπ, Q.g.scalingOrder = ord Q0.g.counters ∧ Q.g.nM = Q0.g.nM ∧
      (Q.g.nA : ℤ) - Q.g.nW = (Q0.g.nV : ℤ) - Q0.g.nW ∧ Q.g.nLoops = Q0.g.lvl1NLoops ∧ Q.g.nS = Q0.g.nS ∧ Q.g.nPairs = Q0.g.lvl1NPairs ∧
      Q.g.nExt = Fintype.card Q0.E') ∨ P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt
/-- the invariants `(ord, n_M, n_A - n_W, loops, n_S, pairs, nExt)` of a BA graph and of a packed band graph (`BAimg`, R0: `P.img` has those of `P`). -/
def BAPGraph.baInv (Q : BAPGraph E) : ℤ × ℕ × ℤ × ℕ × ℕ × ℕ × ℕ :=
  (Q.g.scalingOrder, Q.g.nM, (Q.g.nA : ℤ) - Q.g.nW, Q.g.nLoops, Q.g.nS, Q.g.nPairs, Q.g.nExt)
def PGraph.baInv (Q0 : PGraph E) : ℤ × ℕ × ℤ × ℕ × ℕ × ℕ × ℕ :=
  (ord Q0.g.counters, Q0.g.nM, (Q0.g.nV : ℤ) - Q0.g.nW, Q0.g.lvl1NLoops, Q0.g.nS, Q0.g.lvl1NPairs, Fintype.card Q0.E')
/-- **`BAsim'`, the simulation at a BA graph with the invariants of `P`** (T2423 (a) T2): the band step is taken at the atomic image `T.img` (R0) of a normal BA
graph `T` with the invariants of `P` (`T = P`, or the transfer graph of a macro step); `BAsim m` is the case `T = P`.  L3a4 re-proves `ba_lvl1StepGood_of_sim` with `BAimg`
at `T` (normality and counters of `T.img`) and `lvl1_step_good` at `T.img`. -/
def BAsim' (m : ℂ) : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal →
  ∀ Q ∈ outs, (∃ (T : BAPGraph E) (L' : List (PGraph E)), T.g.Normal ∧ T.baInv = P.baInv ∧ LocStep m T.img L' ∧ ∃ Q0 ∈ L', Q0.baInv = Q.baInv) ∨
    P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt
end Pins

section Pins2
variable {E : Type}
/-- two waved edges with the same ends, unordered (the colour and the orientation of the edge are not read). -/
def WEdge.sameEnds {V : Type*} (a b : WEdge V) : Prop := (a.x = b.x ∧ a.y = b.y) ∨ (a.x = b.y ∧ a.y = b.x)
/-- **`R` is `S` up to relabelling, the colours of the waved edges not read** (`BAEquiv` with `WEdge.sameEnds` in place of `WEdge.sameRev`; Amend 1, O4: pinned
for L3b4', where the macro output `X.d4` has a waved edge `S` against the band's `S⁺`).  The consumers read `scost` (`waved.length`) and the molecules
(`LGraph.adj`, the ends of the waved edges). -/
def PGraph.BAEquivC (R S : PGraph E) : Prop :=
  ∃ (eE : R.E' ≃ S.E') (eI : R.I' ≃ S.I'), (∀ a, S.ext a = eE (R.ext a)) ∧
    List.Perm (R.g.relabel (Sum.map eE eI)).solid S.g.solid ∧
    (∃ l, List.Perm l (R.g.relabel (Sum.map eE eI)).waved ∧ List.Forall₂ WEdge.sameEnds l S.g.waved) ∧
    (∀ d ∈ (R.g.relabel (Sum.map eE eI)).dotted, ∃ d' ∈ S.g.dotted, DEdge.sameU d d') ∧
    (∀ d ∈ S.g.dotted, ∃ d' ∈ (R.g.relabel (Sum.map eE eI)).dotted, DEdge.sameU d' d)
/-- the twist of a packed BA graph (L3a1; `t/T2395:RBM3D/Probe/T2395Pins.lean:157`; pinned by Amend 1, O4) -/
def BAPGraph.twist (c t : Bool) (P : BAPGraph E) : BAPGraph E := { P with g := P.g.twist c t }
end Pins2

/-! ## 3. `BAFrameStepT_untag` -/

section Untag
variable {E : Type}

theorem BAPGraph.outsT_map_snd (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I']
    (tg : BAGraph P.E' I' → BAShape) (Ts : List (BAGraph P.E' I')) :
    (P.outsT tg Ts).map Prod.snd = P.outsOf Ts := by
  simp only [BAPGraph.outsT, BAPGraph.outsOf, BAGraph.partition, List.map_flatMap, List.map_map, Function.comp_def]

theorem BAPGraph.outsOf_append (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I']
    (A B : List (BAGraph P.E' I')) : P.outsOf (A ++ B) = P.outsOf A ++ P.outsOf B := by
  simp only [BAPGraph.outsOf, List.flatMap_append]

theorem BAPGraph.outsT_append (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I']
    (tg : BAGraph P.E' I' → BAShape) (A B : List (BAGraph P.E' I')) :
    P.outsT tg (A ++ B) = P.outsT tg A ++ P.outsT tg B := by
  simp only [BAPGraph.outsT, List.flatMap_append]

theorem BAPGraph.withinOutsT_map_snd (P : BAPGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) :
    (P.withinOutsT p).map Prod.snd = P.withinOuts p := by
  simp only [BAPGraph.withinOutsT, BAPGraph.withinOuts, List.map_append, BAPGraph.outsT_map_snd]

theorem BAPGraph.splitOutsT_map_snd (P : BAPGraph E) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (j : ℕ) :
    (P.splitOutsT p q j).map Prod.snd = P.splitOuts p q j := by
  simp only [BAPGraph.splitOutsT, BAPGraph.splitOuts, List.map_append, BAPGraph.outsT_map_snd, BAPGraph.outsOf_append]
  simp only [BAPGraph.outsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- **The tagged step is the step with its outputs tagged.** -/
theorem baFrameStepT_untag_holds : BAFrameStepT_untag := by
  intro E P outs
  constructor
  · intro h
    cases h with
    | weight p hp h' => exact ⟨_, BAFrameStepT.weight _ p hp h', by simp [List.map_append, BAPGraph.outsT_map_snd]⟩
    | within p hp h' => exact ⟨_, BAFrameStepT.within _ p hp h', (BAPGraph.withinOutsT_map_snd _ p).symm⟩
    | edge p hp h' x hx hwf hv hint hbad =>
      refine ⟨_, BAFrameStepT.edge _ p hp h' x hx hwf hv hint hbad, ?_⟩
      simp only [List.map_append, BAPGraph.outsT_map_snd, BAGraph.lanlwTerms, BAPGraph.outsOf, List.flatMap_cons]
      simp [BAPGraph.outsOf, BAPGraph.outsT_map_snd]
    | gg p hp q hq h' x hx hwf hint hnb =>
      exact ⟨_, BAFrameStepT.gg _ p hp q hq h' x hx hwf hint hnb, by simp [List.map_append, BAPGraph.outsT_map_snd]⟩
    | ggSplit p hp q j hj h' a a' hx hne hsame hwf hint hnb =>
      exact ⟨_, BAFrameStepT.ggSplit _ p hp q j hj h' a a' hx hne hsame hwf hint hnb, (BAPGraph.splitOutsT_map_snd _ p q j).symm⟩
  · rintro ⟨LT, hT, rfl⟩
    cases hT with
    | weight p hp h' => 
      have := BAFrameStep.weight _ p hp h'
      simpa [List.map_append, BAPGraph.outsT_map_snd] using this
    | within p hp h' =>
      have := BAFrameStep.within _ p hp h'
      rwa [← BAPGraph.withinOutsT_map_snd] at this
    | edge p hp h' x hx hwf hv hint hbad =>
      have := BAFrameStep.edge _ p hp h' x hx hwf hv hint hbad
      simp only [List.map_append, BAPGraph.outsT_map_snd]
      simpa [BAGraph.lanlwTerms, BAPGraph.outsOf] using this
    | gg p hp q hq h' x hx hwf hint hnb =>
      have := BAFrameStep.gg _ p hp q hq h' x hx hwf hint hnb
      simpa [List.map_append, BAPGraph.outsT_map_snd] using this
    | ggSplit p hp q j hj h' a a' hx hne hsame hwf hint hnb =>
      have := BAFrameStep.ggSplit _ p hp q j hj h' a a' hx hne hsame hwf hint hnb
      rwa [← BAPGraph.splitOutsT_map_snd] at this

end Untag

/-! ## 4. Classes of the atomic image: two merges with the same classes -/

section ClassBij
variable {E₁ I₁ E₂ I₂ W : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁]
  [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]

/-- **Two merges with the same classes** (the generalisation of `lwExpSim_equivs`, `LWExpSim.lean:691`, to two arbitrary graphs read through maps `ψ₁`, `ψ₂`
from a common vertex set `W`): if the classes of `Δ₁` at `ψ₁` and of `Δ₂` at `ψ₂` correspond (`h1`), every class is hit (`s1`, `s2`) and external classes correspond
(`e1`), there are bijections of the external and of the internal classes through which the merge maps correspond. -/
theorem BASim_classBij (Δ₁ : LGraph E₁ I₁) (Δ₂ : LGraph E₂ I₂) (ψ₁ : W → E₁ ⊕ I₁) (ψ₂ : W → E₂ ⊕ I₂)
    (h1 : ∀ u v, Δ₁.cls (ψ₁ u) = Δ₁.cls (ψ₁ v) ↔ Δ₂.cls (ψ₂ u) = Δ₂.cls (ψ₂ v))
    (s1 : ∀ q : Δ₁.Cls, ∃ u, Δ₁.cls (ψ₁ u) = q) (s2 : ∀ q : Δ₂.Cls, ∃ u, Δ₂.cls (ψ₂ u) = q)
    (e1 : ∀ u, Δ₁.IsExtCls (Δ₁.cls (ψ₁ u)) ↔ Δ₂.IsExtCls (Δ₂.cls (ψ₂ u))) :
    ∃ (eE : Δ₁.ExtCls ≃ Δ₂.ExtCls) (eI : Δ₁.IntCls ≃ Δ₂.IntCls),
      ∀ u, Δ₂.vmap (ψ₂ u) = Sum.map eE eI (Δ₁.vmap (ψ₁ u)) := by
  classical
  let ρ : Δ₁.Cls → Δ₂.Cls := fun q => Δ₂.cls (ψ₂ (Classical.choose (s1 q)))
  have hρ : ∀ u, ρ (Δ₁.cls (ψ₁ u)) = Δ₂.cls (ψ₂ u) := fun u =>
    (h1 _ _).1 (Classical.choose_spec (s1 (Δ₁.cls (ψ₁ u))))
  have hinj : Function.Injective ρ := by
    intro q q' h
    have hq := Classical.choose_spec (s1 q)
    have hq' := Classical.choose_spec (s1 q')
    rw [← hq, ← hq']
    exact (h1 _ _).2 h
  have hsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨u, rfl⟩ := s2 q
    exact ⟨Δ₁.cls (ψ₁ u), hρ u⟩
  let ρe : Δ₁.Cls ≃ Δ₂.Cls := Equiv.ofBijective ρ ⟨hinj, hsurj⟩
  have hext : ∀ q, Δ₁.IsExtCls q ↔ Δ₂.IsExtCls (ρe q) := by
    intro q
    obtain ⟨u, rfl⟩ := s1 q
    have : ρe (Δ₁.cls (ψ₁ u)) = Δ₂.cls (ψ₂ u) := hρ u
    rw [this]
    exact e1 u
  let eE : Δ₁.ExtCls ≃ Δ₂.ExtCls := Equiv.subtypeEquiv ρe hext
  let eI : Δ₁.IntCls ≃ Δ₂.IntCls := Equiv.subtypeEquiv ρe (fun q => not_congr (hext q))
  refine ⟨eE, eI, fun u => ?_⟩
  have hu : ρe (Δ₁.cls (ψ₁ u)) = Δ₂.cls (ψ₂ u) := hρ u
  unfold LGraph.vmap LGraph.vmapC
  by_cases h : Δ₁.IsExtCls (Δ₁.cls (ψ₁ u))
  · have h' : Δ₂.IsExtCls (Δ₂.cls (ψ₂ u)) := (e1 u).1 h
    simp only [h, h', ↓reduceDIte, Sum.map_inl]
    exact congrArg Sum.inl (Subtype.ext hu.symm)
  · have h' : ¬ Δ₂.IsExtCls (Δ₂.cls (ψ₂ u)) := fun hh => h ((e1 u).2 hh)
    simp only [h, h', ↓reduceDIte, Sum.map_inr]
    exact congrArg Sum.inr (Subtype.ext hu.symm)

end ClassBij

section BAside
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the atoms of the merge of a graph without `=`-dotted edges are the images of the atoms -/
theorem BASim_merge_sameAtom (T : BAGraph E I) (hT : ∀ e ∈ T.dotted, e.eq = false) (u v : E ⊕ I) :
    T.merge.sameAtom (T.toLGraph.vmap u) (T.toLGraph.vmap v) = T.sameAtom u v := by
  have hinj := BAVocab_vmap_injective T.toLGraph hT
  have hsurj := BAVocab_vmap_surjective T.toLGraph
  rw [Bool.eq_iff_iff, T.merge.BAAtomic_sameAtom_iff, T.BAAtomic_sameAtom_iff, BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
  constructor
  · intro h
    have key : ∀ b, Relation.ReflTransGen (fun a b => T.merge.atomAdj a b = true) (T.toLGraph.vmap u) b →
        ∃ w, T.toLGraph.vmap w = b ∧ Relation.ReflTransGen (fun a b => T.atomAdj a b = true) u w := by
      intro b hb
      induction hb with
      | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
      | @tail b' c _ hbc ih =>
        obtain ⟨w', hw', hrw⟩ := ih
        obtain ⟨w, rfl⟩ := hsurj c
        subst hw'
        rw [BAVocab_merge_atomAdj T hT] at hbc
        exact ⟨w, rfl, hrw.tail hbc⟩
    obtain ⟨w, hw, hrw⟩ := key _ h
    rw [hinj hw] at hrw
    exact hrw
  · intro h
    refine Relation.ReflTransGen.lift T.toLGraph.vmap (fun a b hab => ?_) _ _ h
    show T.merge.atomAdj (T.toLGraph.vmap a) (T.toLGraph.vmap b) = true
    rw [BAVocab_merge_atomAdj T hT]
    exact hab

/-- the classes of the atomic image of the merge: one class is one atom of `T` -/
theorem BASim_cls_merge_iff (T : BAGraph E I) (hT : ∀ e ∈ T.dotted, e.eq = false) (u v : E ⊕ I) :
    (promoteC T.merge).cls (T.toLGraph.vmap u) = (promoteC T.merge).cls (T.toLGraph.vmap v) ↔ T.sameAtom u v = true := by
  rw [← BASim_merge_sameAtom T hT, T.merge.BAAtomic_sameAtom_iff, BAAtomic_promoteC_cls_eq_iff]

end BAside


/-! ## 5. Flags of `G = Ǧ + M`, of the weight split; membership in the dotted edge partition; the lists of the atomic image of a packed term -/

section Flags

/-- `baSplitSolid`: the terms are the choices of keeping (circled) or dropping (as `M`) each uncircled edge: a list of flags -/
theorem BASim_baSplit_flags {V : Type*} : ∀ (es : List (SEdge V)) (r : List (SEdge V) × List (BAMEdge V)), r ∈ baSplitSolid es →
    ∃ fl : List Bool, fl.length = es.length ∧ (∀ p ∈ es.zip fl, p.2 = true → p.1.circ = false) ∧
      r.1 = (es.zip fl).filterMap (fun p => if p.2 then none else some { p.1 with circ := true }) ∧
      r.2 = (es.zip fl).filterMap (fun p => if p.2 then some (BAMEdge.mk p.1.σ p.1.src p.1.dst) else none)
  | [], r, h => by
    simp only [baSplitSolid, List.mem_singleton] at h
    subst h
    exact ⟨[], rfl, fun p hp => absurd hp (by simp), rfl, rfl⟩
  | e :: es, r, h => by
    simp only [baSplitSolid, List.mem_flatMap] at h
    obtain ⟨r', hr', h⟩ := h
    obtain ⟨fl, hl, hc, h1, h2⟩ := BASim_baSplit_flags es r' hr'
    by_cases hce : e.circ = true
    · simp only [hce, ↓reduceIte, List.mem_singleton] at h
      subst h
      refine ⟨false :: fl, by simp [hl], ?_, ?_, ?_⟩
      · intro p hp hfl
        rw [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp at hfl
        · exact hc p hp hfl
      · simp only [List.zip_cons_cons, List.filterMap_cons, Bool.false_eq_true, ↓reduceIte, h1]
        have : ({ e with circ := true } : SEdge V) = e := by cases e; simp_all
        rw [this]
      · simp [h2]
    · have hcf : e.circ = false := by simpa using hce
      simp only [hce, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · refine ⟨false :: fl, by simp [hl], ?_, ?_, ?_⟩
        · intro p hp hfl
          rw [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · simp at hfl
          · exact hc p hp hfl
        · simp [h1]
        · simp [h2]
      · refine ⟨true :: fl, by simp [hl], ?_, ?_, ?_⟩
        · intro p hp hfl
          rw [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hcf
          · exact hc p hp hfl
        · simp [h1]
        · simp [h2]

theorem BASim_perm_zip {α β : Type*} {l l' : List α} (h : l.Perm l') :
    ∀ (f : List β), f.length = l.length → ∃ f' : List β, f'.length = l'.length ∧ (l.zip f).Perm (l'.zip f') := by
  induction h with
  | nil => intro f hf; exact ⟨[], rfl, List.Perm.refl _⟩
  | cons x h ih =>
    intro f hf
    cases f with
    | nil => simp at hf
    | cons b f =>
      obtain ⟨f', hf', hp⟩ := ih f (by simpa using hf)
      exact ⟨b :: f', by simp [hf'], by simpa using hp.cons (x, b)⟩
  | swap x y l =>
    intro f hf
    cases f with
    | nil => simp at hf
    | cons b1 f =>
      cases f with
      | nil => simp at hf
      | cons b2 f =>
        refine ⟨b2 :: b1 :: f, by simpa using hf, ?_⟩
        simpa using List.Perm.swap (x, b2) (y, b1) (l.zip f)
  | trans h1 h2 ih1 ih2 =>
    intro f hf
    obtain ⟨f1, hf1, hp1⟩ := ih1 f hf
    obtain ⟨f2, hf2, hp2⟩ := ih2 f1 hf1
    exact ⟨f2, hf2, hp1.trans hp2⟩


/-- every flagged edge of a list of solid edges is a weight: the weight split can drop the flagged edges and circle the other weights -/
theorem BASim_splitLoops_flags {V : Type*} [DecidableEq V] (m : ℂ) : ∀ (es : List (SEdge V)) (fl : List Bool),
    fl.length = es.length → (∀ p ∈ es.zip fl, p.2 = true → p.1.src = p.1.dst ∧ p.1.circ = false) →
    ∃ r ∈ lwSplitLoops m es, r.2 = (es.zip fl).filterMap (fun p => if p.2 then none else
      some (if p.1.src = p.1.dst ∧ p.1.circ = false then { p.1 with circ := true } else p.1))
  | [], [], _, _ => ⟨(1, []), by simp [lwSplitLoops], rfl⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | e :: es, b :: fl, hl, hc => by
    obtain ⟨r, hr, hrr⟩ := BASim_splitLoops_flags m es fl (by simpa using hl)
      (fun p hp hfl => hc p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp) hfl)
    by_cases hw : e.src = e.dst ∧ e.circ = false
    · cases b
      · refine ⟨(r.1, { e with circ := true } :: r.2), ?_, ?_⟩
        · simp only [lwSplitLoops, List.mem_flatMap]
          exact ⟨r, hr, by simp [hw]⟩
        · simp [hw, hrr]
      · refine ⟨((if e.σ then m else star m) * r.1, r.2), ?_, ?_⟩
        · simp only [lwSplitLoops, List.mem_flatMap]
          exact ⟨r, hr, by simp [hw]⟩
        · simp [hrr]
    · cases b
      · refine ⟨(r.1, e :: r.2), ?_, ?_⟩
        · simp only [lwSplitLoops, List.mem_flatMap]
          exact ⟨r, hr, by simp [hw]⟩
        · simp [hw, hrr]
      · exact absurd (hc (e, true) (by simp) rfl) hw

/-- membership in the product of identities (`lwCombineAtoms`): one term from each factor -/
theorem BASim_combine_mem {X : Type*} : ∀ (atoms : List (List (ℤ × List X))) (ch : List (ℤ × List X)),
    List.Forall₂ (fun c a => c ∈ a) ch atoms → ((ch.map Prod.fst).prod, ch.flatMap Prod.snd) ∈ lwCombineAtoms atoms
  | [], [], _ => by simp [lwCombineAtoms]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: rest, c :: ch, h => by
    rw [List.forall₂_cons] at h
    have ih := BASim_combine_mem rest ch h.2
    simp only [lwCombineAtoms, List.mem_flatMap, List.mem_map]
    exact ⟨c, h.1, _, ih, by simp⟩

end Flags

section PartMem
variable {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

/-- the packed graph of a term `Δ` of the dotted edge partition with the weight split `r` -/
def BASim_mk (Δ : LGraph E' I') (r : ℂ × List (SEdge (Δ.ExtCls ⊕ Δ.IntCls))) : PGraph E' :=
  { E' := Δ.ExtCls, I' := Δ.IntCls, ext := Δ.extMap, ext_surj := Δ.extMap_surj,
    g := { Δ.merge with solid := r.2, coeff := r.1 * Δ.merge.coeff } }

/-- **A term of the dotted edge partition from a dot choice** (the converse of `lvl1_part_struct`, `LWLvl1.lean:248`): a dot choice `c` of `Γ` with a consistent
term `Γ.withDots c`, and a weight split `r` of its merged solid edges, give a graph of `Γ.partition m`. -/
theorem BASim_mk_mem (m : ℂ) (Γ : LGraph E' I') (c : ℤ × List (DEdge (E' ⊕ I'))) (hc : c ∈ Γ.dotChoices)
    (hcons : (Γ.withDots c).Consistent) (r : ℂ × List (SEdge ((Γ.withDots c).ExtCls ⊕ (Γ.withDots c).IntCls)))
    (hr : r ∈ lwSplitLoops m (Γ.withDots c).merge.solid) : BASim_mk (Γ.withDots c) r ∈ Γ.partition m := by
  classical
  unfold LGraph.partition
  refine List.mem_flatMap.2 ⟨Γ.withDots c, ?_, ?_⟩
  · unfold LGraph.partitionTerms
    exact List.mem_filter.2 ⟨List.mem_map.2 ⟨c, hc, rfl⟩, by simpa using hcons⟩
  · unfold LGraph.mergeSplitP LGraph.splitWeights
    exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨r, hr, rfl⟩, rfl⟩

end PartMem

section ImgLists
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the packed output of a term of `P` (an element of `P.outsT`): the `=`-classes merged, read through `P.ext` -/
def BAPGraph.outOf {E : Type} (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (T' : BAGraph P.E' I') : BAPGraph E :=
  { E' := T'.packMerge.E', I' := T'.packMerge.I', ext := T'.packMerge.ext ∘ P.ext, ext_surj := T'.packMerge.ext_surj.comp P.ext_surj,
    g := T'.packMerge.g }

/-- the vertex map of the atomic image of the merge of `T'`: the atom class of a vertex -/
def BASim_theta (T' : BAGraph E I) : E ⊕ I → (promoteC T'.merge).ExtCls ⊕ (promoteC T'.merge).IntCls :=
  fun u => (promoteC T'.merge).vmap (T'.toLGraph.vmap u)

/-- the solid edge of the band graph at a vertex map `φ`: the circle stays iff the ends have the same image -/
def BASim_phiE {V W : Type} [DecidableEq W] (φ : V → W) (e : SEdge V) : SEdge W :=
  ⟨e.σ, e.circ && decide (φ e.src = φ e.dst), φ e.src, φ e.dst⟩

theorem BASim_theta_eq_iff (T' : BAGraph E I) (hT : ∀ e ∈ T'.dotted, e.eq = false) (u v : E ⊕ I) :
    BASim_theta T' u = BASim_theta T' v ↔ T'.sameAtom u v = true := by
  unfold BASim_theta
  rw [BAAtomic_promoteC_vmap_eq_sameAtom, BASim_merge_sameAtom T' hT]

/-- the solid edges of the atomic image of the packed output: those of `T'` at the atom classes -/
theorem BASim_img_solid (T' : BAGraph E I) (hT : ∀ e ∈ T'.dotted, e.eq = false) :
    T'.merge.img.g.solid = T'.solid.map (BASim_phiE (BASim_theta T')) := by
  rw [BAGraph.BAAtomic_img_solid]
  change (T'.solid.map (SEdge.map T'.toLGraph.vmap)).map _ = _
  rw [List.map_map]
  refine List.map_congr_left fun e _ => ?_
  have h : decide (BASim_theta T' e.src = BASim_theta T' e.dst) = T'.sameAtom e.src e.dst := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact BASim_theta_eq_iff T' hT _ _
  simp only [Function.comp_apply, BASim_phiE, SEdge.map]
  rw [h, BASim_merge_sameAtom T' hT]
  rfl

theorem BASim_img_waved (T' : BAGraph E I) : T'.merge.img.g.waved = T'.waved.map (WEdge.map (BASim_theta T')) := by
  rw [BAGraph.BAAtomic_img_waved]
  change (T'.waved.map (WEdge.map T'.toLGraph.vmap)).map _ = _
  rw [List.map_map]
  rfl

theorem BASim_img_dotted (T' : BAGraph E I) (hT : ∀ e ∈ T'.dotted, e.eq = false) :
    T'.merge.img.g.dotted = (T'.solid.filter fun e => !T'.sameAtom e.src e.dst).map
      fun e => (⟨false, BASim_theta T' e.src, BASim_theta T' e.dst⟩ : DEdge _) := by
  rw [BAGraph.BAAtomic_img_dotted]
  change ((T'.solid.map (SEdge.map T'.toLGraph.vmap)).filter _).map _ = _
  rw [List.filter_map, List.map_map]
  congr 1
  · refine List.filter_congr fun e _ => ?_
    simp only [Function.comp_apply, SEdge.map]
    rw [BASim_merge_sameAtom T' hT]

end ImgLists


/-! ## 6. The matching engine: the data of one match, the classes of the partition term, `BASim_match` -/

section Master

/-- the external vertices of the atomic image of `P` (`P.img.E'`, reducibly) -/
abbrev BASimX {E : Type} (P : BAPGraph E) : Type := (promoteC P.g).ExtCls
/-- the internal vertices of the atomic image of `P` (`P.img.I'`, reducibly) -/
abbrev BASimY {E : Type} (P : BAPGraph E) : Type := (promoteC P.g).IntCls

theorem BASim_sameAtom_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (u v : E ⊕ I) :
    Γ.sameAtom u v = true ↔ atomSetoid Γ u v := by
  rw [Γ.BAAtomic_sameAtom_iff, BAAtomic_atomSetoid_iff]

theorem BASim_forall₂_map_mem {α β : Type*} (l : List α) (f : α → β) (g : α → List β) (h : ∀ a ∈ l, f a ∈ g a) :
    List.Forall₂ (fun c a => c ∈ a) (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih => exact List.Forall₂.cons (h a (by simp)) (ih fun a' ha' => h a' (by simp [ha']))

/-- the dot choice that puts `=` on the pairs satisfying `eqc` and `×` on the others (and keeps the `×`-dotted edges without a solid edge) -/
def BASim_dc {V : Type} (ps : List (V × V)) (eqc : V × V → Prop) [DecidablePred eqc] : ℤ × List (DEdge V) :=
  (1, ps.flatMap fun p => if eqc p then [⟨true, p.1, p.2⟩] else [⟨false, p.1, p.2⟩])

theorem BASim_dc_mem {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : LGraph E' I')
    (eqc : (E' ⊕ I') × (E' ⊕ I') → Prop) [DecidablePred eqc] : BASim_dc Γ.aPairs eqc ∈ Γ.dotChoices := by
  unfold LGraph.dotChoices
  have h1 := BASim_combine_mem Γ.dotAtoms
    (Γ.aPairs.map (fun p => ((1 : ℤ), if eqc p then [(⟨true, p.1, p.2⟩ : DEdge _)] else [(⟨false, p.1, p.2⟩ : DEdge _)])) ++
      Γ.bEdges.map (fun _ => ((1 : ℤ), ([] : List (DEdge (E' ⊕ I'))))))
    (by
      unfold LGraph.dotAtoms
      refine List.rel_append (BASim_forall₂_map_mem _ _ _ fun p _ => ?_) (BASim_forall₂_map_mem _ _ _ fun e _ => ?_)
      · by_cases h : eqc p <;> simp [h]
      · simp)
  have h2 : ((Γ.aPairs.map (fun p => ((1 : ℤ), if eqc p then [(⟨true, p.1, p.2⟩ : DEdge _)] else [(⟨false, p.1, p.2⟩ : DEdge _)])) ++
      Γ.bEdges.map (fun _ => ((1 : ℤ), ([] : List (DEdge (E' ⊕ I')))))).map Prod.fst).prod = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨p, _, rfl⟩ := List.mem_map.1 ha; rfl
    · obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha; rfl
  rw [h2] at h1
  have h3 : (BASim_dc Γ.aPairs eqc) = (1, List.flatMap Prod.snd (Γ.aPairs.map (fun p => ((1 : ℤ), if eqc p then [(⟨true, p.1, p.2⟩ : DEdge _)] else [(⟨false, p.1, p.2⟩ : DEdge _)])) ++
      Γ.bEdges.map (fun _ => ((1 : ℤ), ([] : List (DEdge (E' ⊕ I'))))))) := by
    simp only [BASim_dc, List.flatMap_append, List.flatMap_map, Function.comp_def, List.flatMap_nil, List.append_nil]
    simp
  rw [h3]
  exact h1


variable {E : Type}

/-- **The data of one matching** of a BA term `T` (with `k` new vertices) with a band term `H` over the atomic image of `P` (vertex set `(BASimX P) ⊕ J'`, the old vertices
embedded by `emb'`): a vertex map `φ` of the vertices of `T` onto those of `H` that sends the old vertices to their atom classes, has its fibres inside the atoms of `T`,
and under which the edges of `T` are the edges of `H` (`hHs`: the circle of a solid edge stays iff its ends have the same image; `X` are the edges of `H` that have no
edge of `T`: they are weights after the merge, `hX1`; `hHw`: waved edges up to reversal; `hHd`: the `×`-dotted edges of `H` are those of the image of `P`). -/
structure BASimData (P : BAPGraph E) (k : ℕ) (J' : Type) [Fintype J'] [DecidableEq J'] (emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J') where
  hemb : ∀ y : (BASimX P), emb' (Sum.inl y) = Sum.inl y
  T : BAGraph P.E' (P.I' ⊕ Fin k)
  H : LGraph (BASimX P) J'
  φ : P.E' ⊕ (P.I' ⊕ Fin k) → (BASimX P) ⊕ J'
  X : List (SEdge ((BASimX P) ⊕ J'))
  hT0 : ∀ d ∈ T.dotted, d.eq = false
  hφ : ∀ v, φ (owxEmb k v) = emb' ((promoteC P.g).vmap v)
  hsurj : Function.Surjective φ
  hker : ∀ u v, φ u = φ v → T.sameAtom u v = true
  hmd : ∀ m' ∈ T.mdot, φ m'.x = φ m'.y ∨ ∃ h ∈ X, (h.src = φ m'.x ∧ h.dst = φ m'.y) ∨ (h.src = φ m'.y ∧ h.dst = φ m'.x)
  hpsi : ∀ e ∈ T.psi, φ e.x = φ e.y
  hX0 : ∀ h ∈ X, h.circ = false
  hX1 : ∀ h ∈ X, ∃ u v, φ u = h.src ∧ φ v = h.dst ∧ T.sameAtom u v = true
  hHd : H.dotted = (P.g.solid.filter fun e => !P.g.sameAtom e.src e.dst).map
    (fun e => (⟨false, emb' ((promoteC P.g).vmap e.src), emb' ((promoteC P.g).vmap e.dst)⟩ : DEdge ((BASimX P) ⊕ J')))
  hHs : H.solid.Perm (T.solid.map (BASim_phiE φ) ++ X)
  hHw : List.Forall₂ (fun h w => WEdge.sameRev h (WEdge.map φ w)) H.waved T.waved

section Classes

variable {P : BAPGraph E} {k : ℕ} {J' : Type} [Fintype J'] [DecidableEq J'] {emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J'}

theorem BASim_extra_false {T' : BAGraph P.E' (P.I' ⊕ Fin k)} (hne : P.g.extraB (owxEmb k) T' = false)
    {e : SEdge (P.E' ⊕ P.I')} (he : e ∈ P.g.solid) (hns : P.g.sameAtom e.src e.dst = false) :
    T'.sameAtom (owxEmb k e.src) (owxEmb k e.dst) = false := by
  unfold BAGraph.extraB at hne
  rw [List.any_eq_false] at hne
  have := hne e he
  simpa [hns] using this

theorem BASim_sameAtom_trans {Γ : BAGraph P.E' (P.I' ⊕ Fin k)} {u v w : P.E' ⊕ (P.I' ⊕ Fin k)} (h1 : Γ.sameAtom u v = true) (h2 : Γ.sameAtom v w = true) :
    Γ.sameAtom u w = true :=
  (BASim_sameAtom_iff Γ _ _).2 ((atomSetoid Γ).trans ((BASim_sameAtom_iff Γ _ _).1 h1) ((BASim_sameAtom_iff Γ _ _).1 h2))

theorem BASim_sameAtom_symm {Γ : BAGraph P.E' (P.I' ⊕ Fin k)} {u v : P.E' ⊕ (P.I' ⊕ Fin k)} (h1 : Γ.sameAtom u v = true) :
    Γ.sameAtom v u = true :=
  (BASim_sameAtom_iff Γ _ _).2 ((atomSetoid Γ).symm ((BASim_sameAtom_iff Γ _ _).1 h1))

theorem BASim_sameAtom_refl (Γ : BAGraph P.E' (P.I' ⊕ Fin k)) (u : P.E' ⊕ (P.I' ⊕ Fin k)) : Γ.sameAtom u u = true :=
  (BASim_sameAtom_iff Γ _ _).2 ((atomSetoid Γ).refl _)

/-- **A non-extra output merges no two atoms joined by a `×`-dotted edge of the band term**: if the atoms of `T'` contain those of `T` and `T'` is not extra,
no two vertices of one atom of `T'` have images joined by a `×`-dotted edge of `H`. -/
theorem BASim_noX (D : BASimData P k J' emb') {T' : BAGraph P.E' (P.I' ⊕ Fin k)}
    (hle : ∀ u v, D.T.sameAtom u v = true → T'.sameAtom u v = true)
    (hne : P.g.extraB (owxEmb k) T' = false) (u v : P.E' ⊕ (P.I' ⊕ Fin k)) (huv : T'.sameAtom u v = true) :
    ¬ D.H.XBetween (D.φ u) (D.φ v) := by
  rintro ⟨d, hd, _, hxy⟩
  rw [D.hHd] at hd
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 hd
  obtain ⟨he0, hns⟩ := List.mem_filter.1 he0
  have hns' : P.g.sameAtom e0.src e0.dst = false := by simpa using hns
  have hF := BASim_extra_false hne he0 hns'
  have h1 : D.φ (owxEmb k e0.src) = emb' ((promoteC P.g).vmap e0.src) := D.hφ _
  have h2 : D.φ (owxEmb k e0.dst) = emb' ((promoteC P.g).vmap e0.dst) := D.hφ _
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have a1 : T'.sameAtom (owxEmb k e0.src) u = true := hle _ _ (D.hker _ _ (h1.trans hx))
    have a2 : T'.sameAtom v (owxEmb k e0.dst) = true := hle _ _ (D.hker _ _ (hy.symm.trans h2.symm))
    rw [BASim_sameAtom_trans a1 (BASim_sameAtom_trans huv a2)] at hF
    exact Bool.noConfusion hF
  · have a1 : T'.sameAtom (owxEmb k e0.src) v = true := hle _ _ (D.hker _ _ (h1.trans hx))
    have a2 : T'.sameAtom u (owxEmb k e0.dst) = true := hle _ _ (D.hker _ _ (hy.symm.trans h2.symm))
    rw [BASim_sameAtom_trans a1 (BASim_sameAtom_trans (BASim_sameAtom_symm huv) a2)] at hF
    exact Bool.noConfusion hF


open Classical in
/-- the pair of band vertices is the image of two vertices of one atom of `T'` -/
def BASim_eqc (D : BASimData P k J' emb') (T' : BAGraph P.E' (P.I' ⊕ Fin k))
    (p : ((BASimX P) ⊕ J') × ((BASimX P) ⊕ J')) : Prop :=
  ∃ u v, D.φ u = p.1 ∧ D.φ v = p.2 ∧ T'.sameAtom u v = true

open Classical in
/-- the term of the partition of `H` that merges exactly what `T'` merges -/
def BASim_Δ (D : BASimData P k J' emb') (T' : BAGraph P.E' (P.I' ⊕ Fin k)) : LGraph (BASimX P) J' :=
  D.H.withDots (BASim_dc D.H.aPairs (BASim_eqc D T'))

theorem BASim_eqRel_iff (D : BASimData P k J' emb') (T' : BAGraph P.E' (P.I' ⊕ Fin k)) (a b : (BASimX P) ⊕ J') :
    (BASim_Δ D T').EqRel a b ↔ ∃ p ∈ D.H.aPairs, BASim_eqc D T' p ∧ ((p.1 = a ∧ p.2 = b) ∨ (p.1 = b ∧ p.2 = a)) := by
  classical
  unfold LGraph.EqRel
  constructor
  · rintro ⟨d, hd, heq, hxy⟩
    simp only [BASim_Δ, LGraph.withDots, List.mem_append, BASim_dc, List.mem_flatMap] at hd
    rcases hd with hd | ⟨p, hp, hd⟩
    · exfalso
      have := (List.mem_filter.1 hd).1
      rw [D.hHd] at this
      obtain ⟨e0, _, rfl⟩ := List.mem_map.1 this
      exact absurd heq (by simp)
    · by_cases hq : BASim_eqc D T' p
      · simp only [hq, ↓reduceIte, List.mem_singleton] at hd
        subst hd
        exact ⟨p, hp, hq, hxy⟩
      · simp only [hq, ↓reduceIte, List.mem_singleton] at hd
        subst hd
        exact absurd heq (by simp)
  · rintro ⟨p, hp, hq, hxy⟩
    refine ⟨⟨true, p.1, p.2⟩, ?_, rfl, hxy⟩
    simp only [BASim_Δ, LGraph.withDots, List.mem_append, BASim_dc, List.mem_flatMap]
    exact Or.inr ⟨p, hp, by simp [hq]⟩

/-- **An `M`-dotted edge is an `=` pair of the band term**: the two ends of an `M`-dotted edge of `T'`, whose images are the ends of an edge `h` of `H`, have the same
class in the term of the partition (they have the same image, or the pair is an `=` pair: the band edge `h` joins them and no `×`-dotted edge does, by `BASim_noX`). -/
theorem BASim_drop_cls (D : BASimData P k J' emb') {T' : BAGraph P.E' (P.I' ⊕ Fin k)}
    (hle : ∀ u v, D.T.sameAtom u v = true → T'.sameAtom u v = true)
    (hne : P.g.extraB (owxEmb k) T' = false) {x y : P.E' ⊕ (P.I' ⊕ Fin k)} {h : SEdge ((BASimX P) ⊕ J')} (hh : h ∈ D.H.solid)
    (hends : (h.src = D.φ x ∧ h.dst = D.φ y) ∨ (h.src = D.φ y ∧ h.dst = D.φ x))
    (hs : T'.sameAtom x y = true) :
    (BASim_Δ D T').cls (D.φ x) = (BASim_Δ D T').cls (D.φ y) := by
  classical
  by_cases hφe : D.φ x = D.φ y
  · rw [hφe]
  have hX := BASim_noX D hle hne _ _ hs
  have hX' : ¬ D.H.XBetween h.src h.dst := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hX
    · rw [h1, h2]
      intro hb
      obtain ⟨d, hd, hde, hxy⟩ := hb
      exact hX ⟨d, hd, hde, hxy.symm⟩
  have hne' : h.src ≠ h.dst := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hφe
    · rw [h1, h2]; exact fun hh => hφe hh.symm
  have h1 : (h.src, h.dst) ∈ (D.H.solid.filter fun e => decide (e.src ≠ e.dst ∧ ¬ D.H.XBetween e.src e.dst)).map
      fun e => (e.src, e.dst) :=
    List.mem_map.2 ⟨h, List.mem_filter.2 ⟨hh, by simpa [hne'] using hX'⟩, rfl⟩
  obtain ⟨q, hq, hsame⟩ := lwExists_mem_dedupPairs h1
  simp only [lwSamePair, decide_eq_true_eq] at hsame
  have hrel : ∃ u v, D.φ u = q.1 ∧ D.φ v = q.2 ∧ T'.sameAtom u v = true := by
    rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨x, y, by rw [h1, e1], by rw [h2, e2], hs⟩
    · exact ⟨y, x, by rw [h1, e2], by rw [h2, e1], BASim_sameAtom_symm hs⟩
    · exact ⟨y, x, by rw [h1, e1], by rw [h2, e2], BASim_sameAtom_symm hs⟩
    · exact ⟨x, y, by rw [h1, e2], by rw [h2, e1], hs⟩
  have hR := (BASim_eqRel_iff D T' q.1 q.2).2 ⟨q, hq, hrel, Or.inl ⟨rfl, rfl⟩⟩
  have hc : (BASim_Δ D T').cls q.1 = (BASim_Δ D T').cls q.2 := Quotient.sound (Relation.EqvGen.rel _ _ hR)
  rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← e1, ← e2, ← h1, ← h2]; exact hc
  · rw [← e1, ← e2, ← h1, ← h2]; exact hc.symm
  · rw [← e1, ← e2, ← h1, ← h2]; exact hc.symm
  · rw [← e1, ← e2, ← h1, ← h2]; exact hc

/-- **The classes of the partition term are the atoms of `T'`** (`H1`): two vertices of `T` have the same class at `φ` in the term `BASim_Δ` iff they lie in one atom of `T'`.
`hmd`: every `M`-dotted edge of `T'` joins two vertices with the same image, or is the `M`-split of an uncircled edge of `T`. -/
theorem BASim_class (D : BASimData P k J' emb') {T' : BAGraph P.E' (P.I' ⊕ Fin k)} (hT'0 : ∀ d ∈ T'.dotted, d.eq = false)
    (hle : ∀ u v, D.T.sameAtom u v = true → T'.sameAtom u v = true)
    (hne : P.g.extraB (owxEmb k) T' = false) (hpsi : ∀ e ∈ T'.psi, D.φ e.x = D.φ e.y)
    (hmd : ∀ m' ∈ T'.mdot, D.φ m'.x = D.φ m'.y ∨ ∃ h ∈ D.H.solid, (h.src = D.φ m'.x ∧ h.dst = D.φ m'.y) ∨ (h.src = D.φ m'.y ∧ h.dst = D.φ m'.x))
    (u v : P.E' ⊕ (P.I' ⊕ Fin k)) :
    (BASim_Δ D T').cls (D.φ u) = (BASim_Δ D T').cls (D.φ v) ↔ T'.sameAtom u v = true := by
  classical
  constructor
  · intro h
    have hg : Relation.EqvGen (BASim_Δ D T').EqRel (D.φ u) (D.φ v) := Quotient.exact h
    have key : ∀ a b, Relation.EqvGen (BASim_Δ D T').EqRel a b → ∀ u v, D.φ u = a → D.φ v = b → T'.sameAtom u v = true := by
      intro a b hab
      induction hab with
      | rel a b hr =>
        intro u v hu hv
        obtain ⟨p, hp, ⟨u0, v0, h1, h2, h3⟩, hxy⟩ := (BASim_eqRel_iff D T' a b).1 hr
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact BASim_sameAtom_trans (hle _ _ (D.hker _ _ (hu.trans h1.symm)))
            (BASim_sameAtom_trans h3 (hle _ _ (D.hker _ _ (h2.trans hv.symm))))
        · exact BASim_sameAtom_trans (hle _ _ (D.hker _ _ (hu.trans h2.symm)))
            (BASim_sameAtom_trans (BASim_sameAtom_symm h3) (hle _ _ (D.hker _ _ (h1.trans hv.symm))))
      | refl a => intro u v hu hv; exact hle _ _ (D.hker _ _ (hu.trans hv.symm))
      | symm a b _ ih => intro u v hu hv; exact BASim_sameAtom_symm (ih v u hv hu)
      | trans a b c _ _ ih1 ih2 =>
        intro u v hu hv
        obtain ⟨w, hw⟩ := D.hsurj b
        exact BASim_sameAtom_trans (ih1 u w hu hw) (ih2 w v hw hv)
    exact key _ _ hg u v rfl rfl
  · intro h
    rw [BASim_sameAtom_iff, BAAtomic_atomSetoid_iff, BAGraph.mem_atom_iff] at h
    induction h with
    | refl => rfl
    | @tail b c _ hbc ih =>
      refine ih.trans ?_
      have hbc' : T'.atomAdj b c = true := hbc
      simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hbc'
      rcases hbc' with (⟨e, he, he1, he2⟩ | ⟨e, he, he2⟩) | ⟨e, he, he2⟩
      · rw [hT'0 e he] at he1
        exact absurd he1 (by simp)
      · have := hpsi e he
        rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2, this]
        · rw [← h1, ← h2, this]
      · rcases hmd e he with h0 | ⟨h0, hh0, hends⟩
        · rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2, h0]
          · rw [← h1, ← h2, h0]
        · have hs : T'.sameAtom e.x e.y = true :=
            (BASim_sameAtom_iff T' _ _).2 (BAScost_atomSetoid_of_mdot T' e he)
          have hd := BASim_drop_cls D hle hne hh0 hends hs
          rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]; exact hd
          · rw [← h1, ← h2]; exact hd.symm


section Cons
variable (D : BASimData P k J' emb') {T' : BAGraph P.E' (P.I' ⊕ Fin k)}

theorem BASim_phi_inl (b : P.E') : D.φ (Sum.inl b) = Sum.inl ((promoteC P.g).extMap b) := by
  have h := D.hφ (Sum.inl b)
  simp only [owxEmb, BAAtomic_vmap_inl, Sum.map_inl, id] at h
  rw [h]
  exact D.hemb _

/-- the term of the partition is consistent: no `×`-dotted edge joins two vertices of one class -/
theorem BASim_consistent (hT'0 : ∀ d ∈ T'.dotted, d.eq = false)
    (hle : ∀ u v, D.T.sameAtom u v = true → T'.sameAtom u v = true)
    (hne : P.g.extraB (owxEmb k) T' = false) (hpsi : ∀ e ∈ T'.psi, D.φ e.x = D.φ e.y)
    (hmd : ∀ m' ∈ T'.mdot, D.φ m'.x = D.φ m'.y ∨ ∃ h ∈ D.H.solid, (h.src = D.φ m'.x ∧ h.dst = D.φ m'.y) ∨ (h.src = D.φ m'.y ∧ h.dst = D.φ m'.x)) :
    (BASim_Δ D T').Consistent := by
  classical
  intro d hd heq hcls
  simp only [BASim_Δ, LGraph.withDots, List.mem_append, BASim_dc, List.mem_flatMap] at hd
  rcases hd with hd | ⟨p, hp, hd⟩
  · have hd' := (List.mem_filter.1 hd).1
    rw [D.hHd] at hd'
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 hd'
    obtain ⟨he0, hns⟩ := List.mem_filter.1 he0
    have hns' : P.g.sameAtom e0.src e0.dst = false := by simpa using hns
    have h1 : D.φ (owxEmb k e0.src) = emb' ((promoteC P.g).vmap e0.src) := D.hφ _
    have h2 : D.φ (owxEmb k e0.dst) = emb' ((promoteC P.g).vmap e0.dst) := D.hφ _
    have hc : (BASim_Δ D T').cls (D.φ (owxEmb k e0.src)) = (BASim_Δ D T').cls (D.φ (owxEmb k e0.dst)) := by
      rw [h1, h2]; exact hcls
    rw [BASim_class D hT'0 hle hne hpsi hmd] at hc
    rw [BASim_extra_false hne he0 hns'] at hc
    exact Bool.noConfusion hc
  · by_cases hq : BASim_eqc D T' p
    · simp only [hq, ↓reduceIte, List.mem_singleton] at hd
      subst hd
      exact absurd heq (by simp)
    · simp only [hq, ↓reduceIte, List.mem_singleton] at hd
      subst hd
      obtain ⟨u, hu⟩ := D.hsurj p.1
      obtain ⟨v, hv⟩ := D.hsurj p.2
      have hc : (BASim_Δ D T').cls (D.φ u) = (BASim_Δ D T').cls (D.φ v) := by rw [hu, hv]; exact hcls
      exact hq ⟨u, v, hu, hv, (BASim_class D hT'0 hle hne hpsi hmd u v).1 hc⟩

/-- the external classes correspond -/
theorem BASim_ext_iff (hT'0 : ∀ d ∈ T'.dotted, d.eq = false)
    (hle : ∀ u v, D.T.sameAtom u v = true → T'.sameAtom u v = true)
    (hne : P.g.extraB (owxEmb k) T' = false) (hpsi : ∀ e ∈ T'.psi, D.φ e.x = D.φ e.y)
    (hmd : ∀ m' ∈ T'.mdot, D.φ m'.x = D.φ m'.y ∨ ∃ h ∈ D.H.solid, (h.src = D.φ m'.x ∧ h.dst = D.φ m'.y) ∨ (h.src = D.φ m'.y ∧ h.dst = D.φ m'.x))
    (u : P.E' ⊕ (P.I' ⊕ Fin k)) :
    (BASim_Δ D T').IsExtCls ((BASim_Δ D T').cls (D.φ u)) ↔
      (promoteC T'.merge).IsExtCls ((promoteC T'.merge).cls (T'.toLGraph.vmap u)) := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := (promoteC P.g).extMap_surj a
    have hb : (BASim_Δ D T').cls (D.φ (Sum.inl b)) = (BASim_Δ D T').cls (D.φ u) := by
      rw [BASim_phi_inl D b]; exact ha
    have hs := (BASim_class D hT'0 hle hne hpsi hmd _ _).1 hb
    have hc := (BASim_cls_merge_iff T' (fun e he => hT'0 e he) _ _).2 hs
    refine ⟨T'.toLGraph.extMap b, ?_⟩
    rw [← hc]
    exact congrArg (promoteC T'.merge).cls (BAAtomic_vmap_inl T'.toLGraph b).symm |>.symm ▸ rfl
  · rintro ⟨a', ha'⟩
    obtain ⟨b, rfl⟩ := T'.toLGraph.extMap_surj a'
    have hc : (promoteC T'.merge).cls (T'.toLGraph.vmap (Sum.inl b)) = (promoteC T'.merge).cls (T'.toLGraph.vmap u) := by
      rw [BAAtomic_vmap_inl]; exact ha'
    have hs := (BASim_cls_merge_iff T' (fun e he => hT'0 e he) _ _).1 hc
    have hb := (BASim_class D hT'0 hle hne hpsi hmd _ _).2 hs
    rw [BASim_phi_inl D b] at hb
    exact ⟨_, hb⟩

end Cons

section Dots
variable (D : BASimData P k J' emb')

/-- the term of `G = Ǧ + M` with the split `r` of the solid edges (`BAGraph.splitG`) -/
def BASim_T' (r : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin k))) × List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin k)))) : BAGraph P.E' (P.I' ⊕ Fin k) :=
  BAGraph.mk (LGraph.mk r.1 D.T.waved D.T.dotted D.T.coeff) D.T.psi (r.2 ++ D.T.mdot)

/-- the facts about a term `T'` of `G = Ǧ + M` that the matching reads -/
structure BASimGood (T' : BAGraph P.E' (P.I' ⊕ Fin k)) : Prop where
  hT'0 : ∀ d ∈ T'.dotted, d.eq = false
  hle : ∀ u v, D.T.sameAtom u v = true → T'.sameAtom u v = true
  hne : P.g.extraB (owxEmb k) T' = false
  hpsi : ∀ e ∈ T'.psi, D.φ e.x = D.φ e.y
  hmd : ∀ m' ∈ T'.mdot, D.φ m'.x = D.φ m'.y ∨ ∃ h ∈ D.H.solid, (h.src = D.φ m'.x ∧ h.dst = D.φ m'.y) ∨ (h.src = D.φ m'.y ∧ h.dst = D.φ m'.x)

/-- the flags of the split `r` -/
structure BASimFlags (r : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin k))) × List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin k)))) (fl : List Bool) : Prop where
  hlen : fl.length = D.T.solid.length
  hcirc : ∀ p ∈ D.T.solid.zip fl, p.2 = true → p.1.circ = false
  h1 : r.1 = (D.T.solid.zip fl).filterMap (fun p => if p.2 then none else some { p.1 with circ := true })
  h2 : r.2 = (D.T.solid.zip fl).filterMap (fun p => if p.2 then some (BAMEdge.mk p.1.σ p.1.src p.1.dst) else none)

/-- **`T'` is a term of `G = Ǧ + M` with the split `r` up to the order of the `M`-dotted edges** (`T' ∈ T.splitG` gives it with the order of `BAGraph.splitG`; the order of `mdot` is not read) -/
structure BASimSplit (r : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin k))) × List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin k))))
    (T' : BAGraph P.E' (P.I' ⊕ Fin k)) : Prop where
  hsolid : T'.solid = r.1
  hwaved : T'.waved = D.T.waved
  hdotted : T'.dotted = D.T.dotted
  hpsi : T'.psi = D.T.psi
  hmdot : ∀ m', m' ∈ T'.mdot ↔ m' ∈ r.2 ++ D.T.mdot

theorem BASim_mem_zip_left {α β : Type*} : ∀ (es : List α) (fl : List β), fl.length = es.length → ∀ e ∈ es, ∃ b, (e, b) ∈ es.zip fl
  | [], _, _, e, he => by simp at he
  | a :: es, [], hl, _, _ => by simp at hl
  | a :: es, b :: fl, hl, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨b, by simp⟩
    · obtain ⟨b', hb'⟩ := BASim_mem_zip_left es fl (by simpa using hl) e he
      exact ⟨b', by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb'⟩

variable {D} {r : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin k))) × List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin k)))} {fl : List Bool}
  {T' : BAGraph P.E' (P.I' ⊕ Fin k)}

/-- the atoms of `T` are inside those of `T'` -/
theorem BASim_le_of_split (hS : BASimSplit D r T') (u v : P.E' ⊕ (P.I' ⊕ Fin k)) (h : D.T.sameAtom u v = true) :
    T'.sameAtom u v = true := by
  rw [BASim_sameAtom_iff, BAAtomic_atomSetoid_iff, BAGraph.mem_atom_iff]
  rw [BASim_sameAtom_iff, BAAtomic_atomSetoid_iff, BAGraph.mem_atom_iff] at h
  refine Relation.ReflTransGen.mono (fun a b hab => ?_) u v h
  simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab ⊢
  rcases hab with (⟨e, he, h1, h2⟩ | ⟨e, he, h2⟩) | ⟨e, he, h2⟩
  · exact Or.inl (Or.inl ⟨e, hS.hdotted ▸ he, h1, h2⟩)
  · exact Or.inl (Or.inr ⟨e, hS.hpsi ▸ he, h2⟩)
  · exact Or.inr ⟨e, (hS.hmdot e).2 (List.mem_append_right _ he), h2⟩

/-- an `M`-split edge joins two vertices of one atom of `T'` -/
theorem BASim_flag_sameAtom (hS : BASimSplit D r T') (F : BASimFlags D r fl) {e : SEdge (P.E' ⊕ (P.I' ⊕ Fin k))}
    (hb : (e, true) ∈ D.T.solid.zip fl) : T'.sameAtom e.src e.dst = true := by
  have hm : BAMEdge.mk e.σ e.src e.dst ∈ T'.mdot := by
    rw [hS.hmdot, F.h2]
    exact List.mem_append_left _ (List.mem_filterMap.2 ⟨(e, true), hb, by simp⟩)
  exact (BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_of_mdot _ _ hm)

/-- **A kept edge**: an edge of `T` whose ends are not in one atom of `T'` stays (circled) in `T'` -/
theorem BASim_kept (hS : BASimSplit D r T') (F : BASimFlags D r fl) {e : SEdge (P.E' ⊕ (P.I' ⊕ Fin k))} (he : e ∈ D.T.solid)
    (hs : T'.sameAtom e.src e.dst = false) : ({ e with circ := true } : SEdge _) ∈ r.1 := by
  obtain ⟨b, hb⟩ := BASim_mem_zip_left _ _ F.hlen e he
  cases b
  · rw [F.h1]
    exact List.mem_filterMap.2 ⟨(e, false), hb, by simp⟩
  · rw [BASim_flag_sameAtom hS F hb] at hs
    exact Bool.noConfusion hs


/-- **Every `×`-dotted edge of the term of the partition is an edge of `T'` between two atoms** -/
theorem BASim_dotA (G : BASimGood D T') {d0 : DEdge ((BASimX P) ⊕ J')}
    (hd0 : d0 ∈ (BASim_Δ D T').dotted) (heq : d0.eq = false) :
    ∃ e ∈ D.T.solid, T'.sameAtom e.src e.dst = false ∧
      ((d0.x = D.φ e.src ∧ d0.y = D.φ e.dst) ∨ (d0.x = D.φ e.dst ∧ d0.y = D.φ e.src)) := by
  classical
  simp only [BASim_Δ, LGraph.withDots, List.mem_append, BASim_dc, List.mem_flatMap] at hd0
  rcases hd0 with hd | ⟨p, hp, hd⟩
  · obtain ⟨hdH, hnb⟩ := List.mem_filter.1 hd
    have hsb : D.H.SBetween d0.x d0.y := by
      by_contra hcon
      have : D.H.isB d0 = true := by simp [LGraph.isB, heq, hcon]
      simp [this] at hnb
    obtain ⟨h0, hh0, _, hends⟩ := hsb
    rcases List.mem_append.1 (D.hHs.mem_iff.1 hh0) with hmem | hmem
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
      have hends' : (d0.x = D.φ e.src ∧ d0.y = D.φ e.dst) ∨ (d0.x = D.φ e.dst ∧ d0.y = D.φ e.src) := by
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
      refine ⟨e, he, ?_, hends'⟩
      by_contra hcon
      have hs : (T').sameAtom e.src e.dst = true := by simpa using hcon
      exact BASim_noX D G.hle G.hne _ _ hs ⟨d0, hdH, heq, hends'⟩
    · exfalso
      obtain ⟨u, v, hu, hv, huv⟩ := D.hX1 _ hmem
      have hs := G.hle _ _ huv
      refine BASim_noX D G.hle G.hne u v hs ⟨d0, hdH, heq, ?_⟩
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [← h1, hu], by rw [← h2, hv]⟩
      · exact Or.inr ⟨by rw [← h2, hv], by rw [← h1, hu]⟩
  · by_cases hq : BASim_eqc D (T') p
    · simp only [hq, ↓reduceIte, List.mem_singleton] at hd
      subst hd
      exact absurd heq (by simp)
    · simp only [hq, ↓reduceIte, List.mem_singleton] at hd
      subst hd
      unfold LGraph.aPairs at hp
      obtain ⟨hh, hhm, rfl⟩ := List.mem_map.1 (lwMem_of_mem_dedupPairs hp)
      rcases List.mem_append.1 (D.hHs.mem_iff.1 (List.mem_filter.1 hhm).1) with hmem | hmem
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
        refine ⟨e, he, ?_, Or.inl ⟨rfl, rfl⟩⟩
        by_contra hcon
        have hs : (T').sameAtom e.src e.dst = true := by simpa using hcon
        exact hq ⟨e.src, e.dst, rfl, rfl, hs⟩
      · exfalso
        obtain ⟨u, v, hu, hv, huv⟩ := D.hX1 _ hmem
        exact hq ⟨u, v, hu, hv, G.hle _ _ huv⟩

/-- **Every edge of `T'` between two atoms has a `×`-dotted edge in the term of the partition** -/
theorem BASim_dotB (G : BASimGood D T') {e : SEdge (P.E' ⊕ (P.I' ⊕ Fin k))} (he : e ∈ D.T.solid)
    (hs : T'.sameAtom e.src e.dst = false) :
    ∃ d0 ∈ (BASim_Δ D T').dotted, d0.eq = false ∧
      ((d0.x = D.φ e.src ∧ d0.y = D.φ e.dst) ∨ (d0.x = D.φ e.dst ∧ d0.y = D.φ e.src)) := by
  classical
  have hφne : D.φ e.src ≠ D.φ e.dst := fun h => by
    have := G.hle _ _ (D.hker _ _ h)
    rw [hs] at this
    exact Bool.noConfusion this
  have hmemH : BASim_phiE D.φ e ∈ D.H.solid := D.hHs.mem_iff.2 (List.mem_append_left _ (List.mem_map.2 ⟨e, he, rfl⟩))
  by_cases hX : D.H.XBetween (D.φ e.src) (D.φ e.dst)
  · obtain ⟨d, hd, hdeq, hends⟩ := hX
    refine ⟨d, ?_, hdeq, hends⟩
    simp only [BASim_Δ, LGraph.withDots, List.mem_append]
    left
    refine List.mem_filter.2 ⟨hd, ?_⟩
    have hsb : D.H.SBetween d.x d.y := by
      refine ⟨BASim_phiE D.φ e, hmemH, hφne, ?_⟩
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    simp [LGraph.isB, hsb]
  · have h1 : (D.φ e.src, D.φ e.dst) ∈ (D.H.solid.filter fun e => decide (e.src ≠ e.dst ∧ ¬ D.H.XBetween e.src e.dst)).map
        fun e => (e.src, e.dst) :=
      List.mem_map.2 ⟨BASim_phiE D.φ e, List.mem_filter.2 ⟨hmemH, by simpa [BASim_phiE, hφne] using hX⟩, rfl⟩
    obtain ⟨q, hq, hsame⟩ := lwExists_mem_dedupPairs h1
    simp only [lwSamePair, decide_eq_true_eq] at hsame
    have hnq : ¬ BASim_eqc D (T') q := by
      rintro ⟨u, v, hu, hv, huv⟩
      have hc : (BASim_Δ D (T')).cls (D.φ u) = (BASim_Δ D (T')).cls (D.φ v) :=
        (BASim_class D G.hT'0 G.hle G.hne G.hpsi G.hmd u v).2 huv
      have hc' : (BASim_Δ D (T')).cls q.1 = (BASim_Δ D (T')).cls q.2 := by rw [← hu, ← hv]; exact hc
      have hcls : (BASim_Δ D (T')).cls (D.φ e.src) = (BASim_Δ D (T')).cls (D.φ e.dst) := by
        rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at hc'; exact hc'
        · rw [h1, h2] at hc'; exact hc'.symm
      have := (BASim_class D G.hT'0 G.hle G.hne G.hpsi G.hmd _ _).1 hcls
      rw [hs] at this
      exact Bool.noConfusion this
    refine ⟨⟨false, q.1, q.2⟩, ?_, rfl, ?_⟩
    · simp only [BASim_Δ, LGraph.withDots, List.mem_append, BASim_dc, List.mem_flatMap]
      exact Or.inr ⟨q, hq, by simp [hnq]⟩
    · rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩


/-- the weight split in the form of `BASim_splitLoops_flags` -/
def BASim_fix {V : Type*} [DecidableEq V] (e : SEdge V) : SEdge V := if e.src = e.dst ∧ e.circ = false then { e with circ := true } else e

/-- the pointwise form of the solid-edge matching: an unflagged edge of `T` becomes, after the vertex map `φ`, the merge `vm` and the weight split, the edge of the
image of `T'` at the injective relabelling `f` -/
theorem BASim_edge_pt {V W X Y : Type} [DecidableEq W] [DecidableEq X] [DecidableEq Y] (φ : V → W) (vm : W → X) (f : X → Y)
    (hf : Function.Injective f) (e : SEdge V) :
    SEdge.map f (BASim_fix (SEdge.map vm (BASim_phiE φ e))) = BASim_phiE (f ∘ vm ∘ φ) { e with circ := true } := by
  by_cases h : vm (φ e.src) = vm (φ e.dst)
  · have h' : f (vm (φ e.src)) = f (vm (φ e.dst)) := congrArg f h
    by_cases h2 : φ e.src = φ e.dst <;> cases hc : e.circ <;> simp [BASim_fix, BASim_phiE, SEdge.map, h, h', h2, hc]
  · have h1 : φ e.src ≠ φ e.dst := fun hh => h (congrArg vm hh)
    have h' : ¬ f (vm (φ e.src)) = f (vm (φ e.dst)) := fun hh => h (hf hh)
    simp [BASim_fix, BASim_phiE, SEdge.map, h, h', h1]


/-- **The solid edges of the image of `T'` are those of the term of the partition** (the list form): transport of the flags along the permutation `H.solid ~ T.solid ++ X`
(the edges `xs` of `H` without an edge of `T` are all flagged: weights that the weight split drops) -/
theorem BASim_solid_perm_gen {V W X' Y : Type} [DecidableEq W] [DecidableEq X'] [DecidableEq Y]
    (ts : List (SEdge V)) (xs hs : List (SEdge W)) (φ : V → W) (vm : W → X') (f : X' → Y) (hf : Function.Injective f)
    (fl flH : List Bool) (hfl : fl.length = ts.length)
    (hperm : ((ts.map (BASim_phiE φ) ++ xs).zip (fl ++ List.replicate xs.length true)).Perm (hs.zip flH))
    (rH : List (SEdge X')) (hrH : rH = ((hs.map (SEdge.map vm)).zip flH).filterMap fun p => if p.2 then none else some (BASim_fix p.1)) :
    (rH.map (SEdge.map f)).Perm
      (((ts.zip fl).filterMap (fun p => if p.2 then none else some { p.1 with circ := true })).map (BASim_phiE (f ∘ vm ∘ φ))) := by
  subst hrH
  rw [List.zip_map_left, List.filterMap_map]
  refine ((hperm.symm.filterMap _).map _).trans (List.Perm.of_eq ?_)
  have hx : ∀ (g : SEdge W × Bool → Option (SEdge X')), (∀ p : SEdge W × Bool, p.2 = true → g p = none) →
      (xs.zip (List.replicate xs.length true)).filterMap g = [] := by
    intro g hg
    refine List.filterMap_eq_nil_iff.2 fun p hp => hg p ?_
    have := (List.of_mem_zip hp).2
    rw [List.mem_replicate] at this
    exact this.2
  rw [List.zip_append (by simp [hfl]), List.filterMap_append, List.map_append, hx _ (fun p hp => by simp [hp]), List.map_nil, List.append_nil]
  rw [List.zip_map_left, List.filterMap_map, List.map_filterMap, List.map_filterMap]
  refine List.filterMap_congr fun p _ => ?_
  obtain ⟨e, b⟩ := p
  cases b
  · simp only [Function.comp_apply, Prod.map, id, Bool.false_eq_true, ↓reduceIte, Option.map_some]
    rw [BASim_edge_pt φ vm f hf e]
  · simp

end Dots

/-- **The matching of one output with a band output** (T2423, items 1 and 4 at the level of one term): at a BA term `T` matched with a band term `H` (the data `D`), every
non-extra term `T'` of `G = Ǧ + M` on `T` has, up to relabelling, an output of the dotted edge partition of `H` (packed over the external vertices of the image of `P`). -/
theorem BASim_match' (D : BASimData P k J' emb') (m : ℂ) {T' : BAGraph P.E' (P.I' ⊕ Fin k)}
    (hT' : ∃ r ∈ baSplitSolid D.T.solid, BASimSplit D r T') (hne : P.g.extraB (owxEmb k) T' = false) :
    ∃ R ∈ lvl1Pack P.img (D.H.partition m), R.BAEquiv (P.outOf T').img := by
  classical
  obtain ⟨r, hr, hS⟩ := hT'
  obtain ⟨fl, hlen, hcirc, h1, h2⟩ := BASim_baSplit_flags _ r hr
  have F : BASimFlags D r fl := ⟨hlen, hcirc, h1, h2⟩
  have G : BASimGood D T' := by
    refine ⟨fun d hd => D.hT0 d (hS.hdotted ▸ hd), fun u v h => BASim_le_of_split hS u v h, hne,
      fun e he => D.hpsi e (hS.hpsi ▸ he), fun m' hm' => ?_⟩
    · rcases List.mem_append.1 ((hS.hmdot m').1 hm') with hm' | hm'
      · right
        rw [F.h2] at hm'
        obtain ⟨p, hp, hpm⟩ := List.mem_filterMap.1 hm'
        cases hb : p.2
        · simp [hb] at hpm
        · simp only [hb, ↓reduceIte, Option.some.injEq] at hpm
          subst hpm
          exact ⟨BASim_phiE D.φ p.1, D.hHs.mem_iff.2 (List.mem_append_left _ (List.mem_map.2 ⟨p.1, (List.of_mem_zip hp).1, rfl⟩)),
            Or.inl ⟨rfl, rfl⟩⟩
      · rcases D.hmd m' hm' with h0 | ⟨h0, hX, he⟩
        · exact Or.inl h0
        · exact Or.inr ⟨h0, D.hHs.mem_iff.2 (List.mem_append_right _ hX), he⟩
  set Δ := BASim_Δ D (T') with hΔ
  have hcons : Δ.Consistent := BASim_consistent D G.hT'0 G.hle G.hne G.hpsi G.hmd
  have hc : BASim_dc D.H.aPairs (BASim_eqc D (T')) ∈ D.H.dotChoices := BASim_dc_mem D.H _
  -- the bijections of the classes
  obtain ⟨eE, eI, hθ⟩ := BASim_classBij Δ (promoteC (T').merge) D.φ (T').toLGraph.vmap
    (fun u v => (BASim_class D G.hT'0 G.hle G.hne G.hpsi G.hmd u v).trans (BASim_cls_merge_iff _ G.hT'0 u v).symm)
    (fun q => by
      obtain ⟨w, rfl⟩ := Quotient.exists_rep q
      obtain ⟨u, hu⟩ := D.hsurj w
      exact ⟨u, by rw [hu]⟩)
    (fun q => by
      obtain ⟨w, rfl⟩ := Quotient.exists_rep q
      obtain ⟨u, hu⟩ := BAVocab_vmap_surjective (T').toLGraph w
      exact ⟨u, by rw [hu]⟩)
    (fun u => BASim_ext_iff D G.hT'0 G.hle G.hne G.hpsi G.hmd u)
  -- the flags on the band side: the edges of `H` without an edge of `T` are flagged
  have hfl' : (fl ++ List.replicate D.X.length true).length = (D.T.solid.map (BASim_phiE D.φ) ++ D.X).length := by
    simp [hlen]
  obtain ⟨flH, hflH, hperm⟩ := BASim_perm_zip D.hHs.symm (fl ++ List.replicate D.X.length true) hfl'
  have hsolid : Δ.merge.solid = D.H.solid.map (SEdge.map Δ.vmap) := rfl
  have hdrop : ∀ p ∈ Δ.merge.solid.zip flH, p.2 = true → p.1.src = p.1.dst ∧ p.1.circ = false := by
    intro p hp hfl
    rw [hsolid, List.zip_map_left] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hq' := hperm.symm.mem_iff.1 hq
    rw [List.zip_append (by simp [hlen])] at hq'
    simp only [Prod.map, id] at hfl ⊢
    rcases List.mem_append.1 hq' with hq' | hq'
    · rw [List.zip_map_left] at hq'
      obtain ⟨⟨e, b⟩, hq'', rfl⟩ := List.mem_map.1 hq'
      simp only [Prod.map, id] at hfl ⊢
      subst hfl
      have hce : e.circ = false := F.hcirc _ hq'' rfl
      have hs := BASim_flag_sameAtom hS F hq''
      have hcls := (BASim_class D G.hT'0 G.hle G.hne G.hpsi G.hmd _ _).2 hs
      refine ⟨?_, ?_⟩
      · show Δ.vmap (D.φ e.src) = Δ.vmap (D.φ e.dst)
        unfold LGraph.vmap
        rw [hcls]
      · simp [SEdge.map, BASim_phiE, hce]
    · obtain ⟨hxm, _⟩ := List.of_mem_zip hq'
      obtain ⟨u, v, hu, hv, huv⟩ := D.hX1 _ hxm
      have hcls := (BASim_class D G.hT'0 G.hle G.hne G.hpsi G.hmd u v).2 (G.hle _ _ huv)
      refine ⟨?_, ?_⟩
      · show Δ.vmap q.1.src = Δ.vmap q.1.dst
        rw [← hu, ← hv]
        unfold LGraph.vmap
        rw [hcls]
      · simp [SEdge.map, D.hX0 _ hxm]
  obtain ⟨rH, hrH, hrH2⟩ := BASim_splitLoops_flags m Δ.merge.solid flH (by rw [hsolid, List.length_map]; exact hflH) hdrop
  refine ⟨(BASim_mk Δ rH).lvl1Comp P.img.ext P.img.ext_surj, List.mem_map.2 ⟨BASim_mk Δ rH, BASim_mk_mem m D.H _ hc hcons rH hrH, rfl⟩, ?_⟩
  have hfinj : Function.Injective (Sum.map eE eI) := Sum.map_injective.2 ⟨eE.injective, eI.injective⟩
  have hθ' : BASim_theta (T') = Sum.map eE eI ∘ Δ.vmap ∘ D.φ := funext hθ
  refine ⟨eE, eI, ?_, ?_, ?_, ?_, ?_⟩
  · -- external vertices
    intro a
    have hb := hθ (Sum.inl (P.ext a))
    have hl : (promoteC (T').merge).vmap ((T').toLGraph.vmap (Sum.inl (P.ext a))) =
        Sum.inl ((P.outOf (T')).img.ext a) := by
      rw [BAAtomic_vmap_inl]
      exact BAAtomic_vmap_inl _ _
    have hr : Δ.vmap (D.φ (Sum.inl (P.ext a))) = Sum.inl (((BASim_mk Δ rH).lvl1Comp P.img.ext P.img.ext_surj).ext a) := by
      rw [BASim_phi_inl D]
      exact BAAtomic_vmap_inl Δ _
    rw [hl, hr] at hb
    exact Sum.inl.inj hb
  · -- solid edges
    have := BASim_solid_perm_gen D.T.solid D.X D.H.solid D.φ Δ.vmap (Sum.map eE eI) hfinj fl flH hlen hperm rH.2 hrH2
    rw [← F.h1] at this
    have hSS : ((P.outOf T').img).g.solid = r.1.map (BASim_phiE (BASim_theta T')) := by
      rw [← hS.hsolid]; exact BASim_img_solid T' G.hT'0
    rw [hSS, hθ']
    exact this
  · -- waved edges
    refine ⟨(((BASim_mk Δ rH).lvl1Comp P.img.ext P.img.ext_surj).g.relabel (Sum.map eE eI)).waved, List.Perm.refl _, ?_⟩
    have hSS : ((P.outOf T').img).g.waved = D.T.waved.map (WEdge.map (BASim_theta T')) := by
      rw [← hS.hwaved]; exact BASim_img_waved T'
    rw [hSS, hθ']
    change List.Forall₂ WEdge.sameRev ((D.H.waved.map (WEdge.map Δ.vmap)).map (WEdge.map (Sum.map eE eI)))
      (D.T.waved.map (WEdge.map (Sum.map eE eI ∘ Δ.vmap ∘ D.φ)))
    rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine D.hHw.imp fun h w hw => ?_
    rcases hw with hw | hw
    · exact Or.inl (by rw [hw]; rfl)
    · have hh : h = (WEdge.map D.φ w).transpose := by rw [← hw]; exact (lwSymm_wedge_tr_tr h).symm
      exact Or.inr (by rw [hh]; rfl)
  · -- `×`-dotted edges of R are those of the image
    intro d hd
    have hd' : d ∈ (Δ.merge.dotted).map (DEdge.map (Sum.map eE eI)) := hd
    obtain ⟨d1, hd1, rfl⟩ := List.mem_map.1 hd'
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd1
    obtain ⟨hd0m, hd0eq⟩ := List.mem_filter.1 hd0
    have hd0eq' : d0.eq = false := by simpa using hd0eq
    obtain ⟨e, he, hs, hends⟩ := BASim_dotA G hd0m hd0eq'
    have hk : ({ e with circ := true } : SEdge _) ∈ T'.solid := hS.hsolid ▸ BASim_kept hS F he hs
    refine ⟨⟨false, BASim_theta T' e.src, BASim_theta T' e.dst⟩, ?_, ?_⟩
    · have hSS : ((P.outOf T').img).g.dotted = (T'.solid.filter fun e => !T'.sameAtom e.src e.dst).map
          fun e => (⟨false, BASim_theta T' e.src, BASim_theta T' e.dst⟩ : DEdge _) :=
        BASim_img_dotted T' G.hT'0
      rw [hSS]
      exact List.mem_map.2 ⟨{ e with circ := true }, List.mem_filter.2 ⟨hk, by simpa using hs⟩, rfl⟩
    · refine ⟨hd0eq', ?_⟩
      rcases hends with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · left
        refine ⟨?_, ?_⟩
        · show Sum.map eE eI (Δ.vmap d0.x) = _
          rw [hx]; exact (hθ e.src).symm
        · show Sum.map eE eI (Δ.vmap d0.y) = _
          rw [hy]; exact (hθ e.dst).symm
      · right
        refine ⟨?_, ?_⟩
        · show Sum.map eE eI (Δ.vmap d0.x) = _
          rw [hx]; exact (hθ e.dst).symm
        · show Sum.map eE eI (Δ.vmap d0.y) = _
          rw [hy]; exact (hθ e.src).symm
  · -- `×`-dotted edges of the image are those of R
    intro d' hd'
    have hSS : ((P.outOf T').img).g.dotted = (T'.solid.filter fun e => !T'.sameAtom e.src e.dst).map
        fun e => (⟨false, BASim_theta T' e.src, BASim_theta T' e.dst⟩ : DEdge _) :=
      BASim_img_dotted T' G.hT'0
    rw [hSS] at hd'
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hd'
    obtain ⟨he'm, hne'⟩ := List.mem_filter.1 he'
    have h1' : e' ∈ (D.T.solid.zip fl).filterMap (fun p => if p.2 then none else some { p.1 with circ := true }) := by
      rw [← F.h1, ← hS.hsolid]; exact he'm
    obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.1 h1'
    cases hb : p.2
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hpe
      subst hpe
      have he : p.1 ∈ D.T.solid := (List.of_mem_zip hp).1
      have hs : (T').sameAtom p.1.src p.1.dst = false := by simpa using hne'
      obtain ⟨d0, hd0, hd0eq, hends⟩ := BASim_dotB G he hs
      refine ⟨DEdge.map (Sum.map eE eI) (DEdge.map Δ.vmap d0), ?_, ?_⟩
      · show _ ∈ (Δ.merge.dotted).map (DEdge.map (Sum.map eE eI))
        exact List.mem_map.2 ⟨DEdge.map Δ.vmap d0, List.mem_map.2 ⟨d0, List.mem_filter.2 ⟨hd0, by simp [hd0eq]⟩, rfl⟩, rfl⟩
      · refine ⟨hd0eq, ?_⟩
        rcases hends with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · left
          refine ⟨?_, ?_⟩
          · show Sum.map eE eI (Δ.vmap d0.x) = _
            rw [hx]; exact (hθ _).symm
          · show Sum.map eE eI (Δ.vmap d0.y) = _
            rw [hy]; exact (hθ _).symm
        · right
          refine ⟨?_, ?_⟩
          · show Sum.map eE eI (Δ.vmap d0.x) = _
            rw [hx]; exact (hθ _).symm
          · show Sum.map eE eI (Δ.vmap d0.y) = _
            rw [hy]; exact (hθ _).symm
    · simp [hb] at hpe


/-- **`BASim_match'` for a term of `T.splitG`** (the order of `BAGraph.splitG`) -/
theorem BASim_match (D : BASimData P k J' emb') (m : ℂ) {T' : BAGraph P.E' (P.I' ⊕ Fin k)} (hT' : T' ∈ D.T.splitG)
    (hne : P.g.extraB (owxEmb k) T' = false) :
    ∃ R ∈ lvl1Pack P.img (D.H.partition m), R.BAEquiv (P.outOf T').img := by
  obtain ⟨r, hr, hT'eq⟩ := List.mem_map.1 hT'
  subst hT'eq
  exact BASim_match' D m ⟨r, hr, ⟨rfl, rfl, rfl, rfl, fun _ => Iff.rfl⟩⟩ hne

end Classes

end Master


/-! ## 7. The matching of an extension: the specification `BASimExt` and its data -/

section Builder
variable {E : Type}

/-- **The vertex map of a matching of an extension**: the old vertices go to their atom classes (`emb'` embeds the old vertices of the image into those of the band term),
the new vertex `j` to the class of its anchor (an old vertex it is `M`-dotted to) or to the fresh band vertex `fresh j`. -/
def BASim_phi (P : BAPGraph E) {k : ℕ} {J' : Type} (emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J')
    (anchor : Fin k → Option (P.E' ⊕ P.I')) (fresh : Fin k → J') : P.E' ⊕ (P.I' ⊕ Fin k) → (BASimX P) ⊕ J'
  | Sum.inl a => emb' ((promoteC P.g).vmap (Sum.inl a))
  | Sum.inr (Sum.inl i) => emb' ((promoteC P.g).vmap (Sum.inr i))
  | Sum.inr (Sum.inr j) => match anchor j with
    | some a => emb' ((promoteC P.g).vmap a)
    | none => Sum.inr (fresh j)

theorem BASim_phi_emb (P : BAPGraph E) {k : ℕ} {J' : Type} (emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J')
    (anchor : Fin k → Option (P.E' ⊕ P.I')) (fresh : Fin k → J') (v : P.E' ⊕ P.I') :
    BASim_phi P emb' anchor fresh (owxEmb k v) = emb' ((promoteC P.g).vmap v) := by
  rcases v with a | i <;> rfl

theorem BASim_phi_some (P : BAPGraph E) {k : ℕ} {J' : Type} (emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J')
    (anchor : Fin k → Option (P.E' ⊕ P.I')) (fresh : Fin k → J') (j : Fin k) (a : P.E' ⊕ P.I') (h : anchor j = some a) :
    BASim_phi P emb' anchor fresh (bpv j) = emb' ((promoteC P.g).vmap a) := by
  show (match anchor j with | some a => emb' ((promoteC P.g).vmap a) | none => Sum.inr (fresh j)) = _
  rw [h]

theorem BASim_phi_none (P : BAPGraph E) {k : ℕ} {J' : Type} (emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J')
    (anchor : Fin k → Option (P.E' ⊕ P.I')) (fresh : Fin k → J') (j : Fin k) (h : anchor j = none) :
    BASim_phi P emb' anchor fresh (bpv j) = Sum.inr (fresh j) := by
  show (match anchor j with | some a => emb' ((promoteC P.g).vmap a) | none => Sum.inr (fresh j)) = _
  rw [h]

/-- an old solid edge is the image of its image edge: the circle stays iff the ends have the same image -/
theorem BASim_phiE_rest (P : BAPGraph E) (hN : P.g.Normal) {k : ℕ} {J' : Type} [DecidableEq J'] (emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J')
    (hinj : Function.Injective emb') (anchor : Fin k → Option (P.E' ⊕ P.I')) (fresh : Fin k → J') {e : SEdge (P.E' ⊕ P.I')}
    (he : e ∈ P.g.solid) :
    BASim_phiE (BASim_phi P emb' anchor fresh) (SEdge.map (owxEmb k) e) = SEdge.map emb' (BAScost_imgE P.g e) := by
  have hc : e.circ = true := hN.2 e he
  have h : decide (emb' ((promoteC P.g).vmap e.src) = emb' ((promoteC P.g).vmap e.dst)) = P.g.sameAtom e.src e.dst := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact (hinj.eq_iff (a := (promoteC P.g).vmap e.src) (b := (promoteC P.g).vmap e.dst)).trans (BAAtomic_promoteC_vmap_eq_sameAtom P.g _ _)
  simp only [BASim_phiE, SEdge.map, BAScost_imgE, BASim_phi_emb, hc, Bool.true_and, h]


/-- **The specification of the matching of an extension** `BAGraph.ext k P.g rest s w md` with the band term `owxExt emb' c sH wH` on `{img with solid := restH}`:
the anchors of the new vertices, the band edges `hd` that are not images of `rest`, the edges `X` of the band term without an edge of the extension, the small lists. -/
structure BASimExt (P : BAPGraph E) (k : ℕ) (J' : Type) [Fintype J'] [DecidableEq J'] (emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J') where
  hemb : ∀ y : (BASimX P), emb' (Sum.inl y) = Sum.inl y
  hinj : Function.Injective emb'
  anchor : Fin k → Option (P.E' ⊕ P.I')
  fresh : Fin k → J'
  rest : List (SEdge (P.E' ⊕ P.I'))
  s : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin k)))
  w : List (WEdge (P.E' ⊕ (P.I' ⊕ Fin k)))
  md : List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin k)))
  restH : List (SEdge ((BASimX P) ⊕ (BASimY P)))
  sH : List (SEdge ((BASimX P) ⊕ J'))
  wH : List (WEdge ((BASimX P) ⊕ J'))
  hd : List (SEdge ((BASimX P) ⊕ (BASimY P)))
  ex : List (SEdge ((BASimX P) ⊕ (BASimY P)))
  X : List (SEdge ((BASimX P) ⊕ J'))
  hrest : ∀ e ∈ rest, e ∈ P.g.solid
  hrestH : (restH ++ ex).Perm (hd ++ rest.map (BAScost_imgE P.g))
  hfresh : ∀ j, anchor j = none → ∀ v, emb' ((promoteC P.g).vmap v) ≠ Sum.inr (fresh j)
  hsurj : ∀ z : J', (∀ v, emb' ((promoteC P.g).vmap v) ≠ Sum.inr z) → ∃ j, anchor j = none ∧ fresh j = z
  hanch : ∀ j a, anchor j = some a → (BAGraph.ext k P.g rest s w md).sameAtom (bpv j) (owxEmb k a) = true
  hfr : ∀ j j', anchor j = none → anchor j' = none → fresh j = fresh j' → (BAGraph.ext k P.g rest s w md).sameAtom (bpv j) (bpv j') = true
  hmd : ∀ m' ∈ md, BASim_phi P emb' anchor fresh m'.x = BASim_phi P emb' anchor fresh m'.y ∨ ∃ h ∈ X,
    (h.src = BASim_phi P emb' anchor fresh m'.x ∧ h.dst = BASim_phi P emb' anchor fresh m'.y) ∨
      (h.src = BASim_phi P emb' anchor fresh m'.y ∧ h.dst = BASim_phi P emb' anchor fresh m'.x)
  hX0 : ∀ h ∈ X, h.circ = false
  hX1 : ∀ h ∈ X, ∃ u v, BASim_phi P emb' anchor fresh u = h.src ∧ BASim_phi P emb' anchor fresh v = h.dst ∧
    (BAGraph.ext k P.g rest s w md).sameAtom u v = true
  hs : (hd.map (SEdge.map emb') ++ sH).Perm (ex.map (SEdge.map emb') ++ (s.map (BASim_phiE (BASim_phi P emb' anchor fresh)) ++ X))
  hw : List.Forall₂ (fun h w => WEdge.sameRev h (WEdge.map (BASim_phi P emb' anchor fresh) w)) wH w

section ExtProofs
variable {P : BAPGraph E} {k : ℕ} {J' : Type} [Fintype J'] [DecidableEq J'] {emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J'}

/-- the vertices of `P` in one atom have the same image -/
theorem BASim_vmap_eq_of_atomAdj (Γ : BAGraph P.E' P.I') {u v : P.E' ⊕ P.I'} (h : Γ.atomAdj u v = true) :
    (promoteC Γ).vmap u = (promoteC Γ).vmap v := by
  rw [BAAtomic_promoteC_vmap_eq_atom, Γ.mem_atom_iff]
  exact Relation.ReflTransGen.single h

theorem BASim_psi_phi (B : BASimExt P k J' emb') :
    ∀ e ∈ (BAGraph.ext k P.g B.rest B.s B.w B.md).psi,
      BASim_phi P emb' B.anchor B.fresh e.x = BASim_phi P emb' B.anchor B.fresh e.y := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  have h : P.g.atomAdj e0.x e0.y = true := by
    simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inr ⟨e0, he0, Or.inl ⟨rfl, rfl⟩⟩)
  show BASim_phi P emb' B.anchor B.fresh (owxEmb k e0.x) = BASim_phi P emb' B.anchor B.fresh (owxEmb k e0.y)
  rw [BASim_phi_emb, BASim_phi_emb, BASim_vmap_eq_of_atomAdj P.g h]

theorem BASim_mdot_phi (B : BASimExt P k J' emb') :
    ∀ e ∈ P.g.mdot.map (BAMEdge.map (owxEmb k)),
      BASim_phi P emb' B.anchor B.fresh e.x = BASim_phi P emb' B.anchor B.fresh e.y := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  have h : P.g.atomAdj e0.x e0.y = true := by
    simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨e0, he0, Or.inl ⟨rfl, rfl⟩⟩
  show BASim_phi P emb' B.anchor B.fresh (owxEmb k e0.x) = BASim_phi P emb' B.anchor B.fresh (owxEmb k e0.y)
  rw [BASim_phi_emb, BASim_phi_emb, BASim_vmap_eq_of_atomAdj P.g h]


/-- the map is onto -/
theorem BASimExt.surj (B : BASimExt P k J' emb') : Function.Surjective (BASim_phi P emb' B.anchor B.fresh) := by
  intro w
  rcases w with a | z
  · obtain ⟨b, rfl⟩ := (promoteC P.g).extMap_surj a
    refine ⟨Sum.inl b, ?_⟩
    have h := BASim_phi_emb P emb' B.anchor B.fresh (Sum.inl b)
    simp only [owxEmb, BAAtomic_vmap_inl, Sum.map_inl, id] at h
    rw [h]
    exact B.hemb _
  · by_cases hz : ∀ v, emb' ((promoteC P.g).vmap v) ≠ Sum.inr z
    · obtain ⟨j, hj, hf⟩ := B.hsurj z hz
      exact ⟨bpv j, by rw [BASim_phi_none _ _ _ _ _ hj, hf]⟩
    · push Not at hz
      obtain ⟨v, hv⟩ := hz
      exact ⟨owxEmb k v, by rw [BASim_phi_emb, hv]⟩

/-- the fibres of the map are inside the atoms of the extension -/
theorem BASimExt.ker (B : BASimExt P k J' emb') (u v : P.E' ⊕ (P.I' ⊕ Fin k))
    (h : BASim_phi P emb' B.anchor B.fresh u = BASim_phi P emb' B.anchor B.fresh v) :
    (BAGraph.ext k P.g B.rest B.s B.w B.md).sameAtom u v = true := by
  set T := BAGraph.ext k P.g B.rest B.s B.w B.md with hT
  have hold : ∀ a b : P.E' ⊕ P.I', BASim_phi P emb' B.anchor B.fresh (owxEmb k a) = BASim_phi P emb' B.anchor B.fresh (owxEmb k b) →
      T.sameAtom (owxEmb k a) (owxEmb k b) = true := by
    intro a b hab
    rw [BASim_phi_emb, BASim_phi_emb] at hab
    have h1 : (promoteC P.g).vmap a = (promoteC P.g).vmap b := B.hinj hab
    have h2 : P.g.sameAtom a b = true := (BAAtomic_promoteC_vmap_eq_sameAtom P.g a b).1 h1
    exact (BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_ext P.g B.rest B.s B.w B.md ((BASim_sameAtom_iff _ _ _).1 h2))
  have hnew_old : ∀ (j : Fin k) (b : P.E' ⊕ P.I'), BASim_phi P emb' B.anchor B.fresh (bpv j) = BASim_phi P emb' B.anchor B.fresh (owxEmb k b) →
      T.sameAtom (bpv j) (owxEmb k b) = true := by
    intro j b hjb
    rcases hj : B.anchor j with _ | a
    · rw [BASim_phi_none _ _ _ _ _ hj, BASim_phi_emb] at hjb
      exact absurd hjb.symm (B.hfresh j hj b)
    · rw [BASim_phi_some _ _ _ _ _ _ hj, BASim_phi_emb] at hjb
      have := hold a b (by rw [BASim_phi_emb, BASim_phi_emb]; exact hjb)
      exact BASim_sameAtom_trans (B.hanch j a hj) this
  rcases u with a | i | j <;> rcases v with b | i' | j'
  · exact hold (Sum.inl a) (Sum.inl b) h
  · exact hold (Sum.inl a) (Sum.inr i') h
  · exact BASim_sameAtom_symm (hnew_old j' (Sum.inl a) h.symm)
  · exact hold (Sum.inr i) (Sum.inl b) h
  · exact hold (Sum.inr i) (Sum.inr i') h
  · exact BASim_sameAtom_symm (hnew_old j' (Sum.inr i) h.symm)
  · exact hnew_old j (Sum.inl b) h
  · exact hnew_old j (Sum.inr i') h
  · rcases hj : B.anchor j with _ | a <;> rcases hj' : B.anchor j' with _ | a'
    · rw [BASim_phi_none _ _ _ _ _ hj, BASim_phi_none _ _ _ _ _ hj'] at h
      exact B.hfr j j' hj hj' (Sum.inr.inj h)
    · rw [BASim_phi_none _ _ _ _ _ hj, BASim_phi_some _ _ _ _ _ _ hj'] at h
      exact absurd h (B.hfresh j hj a').symm
    · rw [BASim_phi_some _ _ _ _ _ _ hj, BASim_phi_none _ _ _ _ _ hj'] at h
      exact absurd h.symm (B.hfresh j' hj' a).symm
    · rw [BASim_phi_some _ _ _ _ _ _ hj, BASim_phi_some _ _ _ _ _ _ hj'] at h
      have := hold a a' (by rw [BASim_phi_emb, BASim_phi_emb]; exact h)
      exact BASim_sameAtom_trans (B.hanch j a hj) (BASim_sameAtom_trans this (BASim_sameAtom_symm (B.hanch j' a' hj')))


/-- the band term of the specification: the old solid edges `restH`, the new solid and waved edges, the coefficient `c` -/
def BASimExt.band (B : BASimExt P k J' emb') (c : ℂ) : LGraph (BASimX P) J' :=
  ({ P.img.g with solid := B.restH } : LGraph (BASimX P) (BASimY P)).owxExt emb' c B.sH B.wH

theorem BASimExt.hHd (B : BASimExt P k J' emb') (c : ℂ) :
    (B.band c).dotted = (P.g.solid.filter fun e => !P.g.sameAtom e.src e.dst).map
      (fun e => (⟨false, emb' ((promoteC P.g).vmap e.src), emb' ((promoteC P.g).vmap e.dst)⟩ : DEdge ((BASimX P) ⊕ J'))) := by
  change (P.g.img.g.dotted).map (DEdge.map emb') = _
  rw [BAGraph.BAAtomic_img_dotted]
  exact List.map_map

theorem BASimExt.hHs (B : BASimExt P k J' emb') (hN : P.g.Normal) (c : ℂ) :
    (B.band c).solid.Perm ((BAGraph.ext k P.g B.rest B.s B.w B.md).solid.map (BASim_phiE (BASim_phi P emb' B.anchor B.fresh)) ++ B.X) := by
  have e1 : (B.rest.map (SEdge.map (owxEmb k))).map (BASim_phiE (BASim_phi P emb' B.anchor B.fresh)) =
      B.rest.map (fun e => SEdge.map emb' (BAScost_imgE P.g e)) := by
    rw [List.map_map]
    exact List.map_congr_left fun e he => BASim_phiE_rest P hN emb' B.hinj B.anchor B.fresh (B.hrest e he)
  have e2 : (BAGraph.ext k P.g B.rest B.s B.w B.md).solid.map (BASim_phiE (BASim_phi P emb' B.anchor B.fresh)) =
      B.rest.map (fun e => SEdge.map emb' (BAScost_imgE P.g e)) ++ B.s.map (BASim_phiE (BASim_phi P emb' B.anchor B.fresh)) := by
    show (B.rest.map (SEdge.map (owxEmb k)) ++ B.s).map _ = _
    rw [List.map_append, e1]
  rw [e2]
  have e3 : (B.band c).solid = B.restH.map (SEdge.map emb') ++ B.sH := rfl
  rw [e3]
  have p1 : (B.restH.map (SEdge.map emb') ++ B.ex.map (SEdge.map emb')).Perm
      (B.hd.map (SEdge.map emb') ++ B.rest.map (fun e => SEdge.map emb' (BAScost_imgE P.g e))) := by
    have := B.hrestH.map (SEdge.map emb')
    rwa [List.map_append, List.map_append, List.map_map] at this
  classical
  rw [List.perm_iff_count]
  intro a
  have h1 := p1.count_eq a
  have h2 := B.hs.count_eq a
  simp only [List.count_append] at h1 h2 ⊢
  omega

theorem BASimExt.hHw (B : BASimExt P k J' emb') (c : ℂ) :
    List.Forall₂ (fun h w => WEdge.sameRev h (WEdge.map (BASim_phi P emb' B.anchor B.fresh) w)) (B.band c).waved
      (BAGraph.ext k P.g B.rest B.s B.w B.md).waved := by
  show List.Forall₂ _ (P.g.img.g.waved.map (WEdge.map emb') ++ B.wH) (P.g.waved.map (WEdge.map (owxEmb k)) ++ B.w)
  rw [BAGraph.BAAtomic_img_waved]
  refine List.rel_append ?_ B.hw
  rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun w0 _ => Or.inl (by cases w0; simp [WEdge.map, BASim_phi_emb])

/-- **The data of a matching from the specification of an extension** -/
def BASimExt.toData (B : BASimExt P k J' emb') (hN : P.g.Normal) (c : ℂ) : BASimData P k J' emb' where
  hemb := B.hemb
  T := BAGraph.ext k P.g B.rest B.s B.w B.md
  H := B.band c
  φ := BASim_phi P emb' B.anchor B.fresh
  X := B.X
  hT0 := fun d hd => by
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd
    exact hN.1 d0 hd0
  hφ := fun v => BASim_phi_emb P emb' B.anchor B.fresh v
  hsurj := B.surj
  hker := B.ker
  hmd := fun m' hm' => by
    rcases List.mem_append.1 hm' with hm' | hm'
    · exact B.hmd m' hm'
    · exact Or.inl (BASim_mdot_phi B m' hm')
  hpsi := BASim_psi_phi B
  hX0 := B.hX0
  hX1 := B.hX1
  hHd := B.hHd c
  hHs := B.hHs hN c
  hHw := B.hHw c

end ExtProofs
end Builder


/-! ## 8. The weight step at the image: the image of a pair, `LocStep.weight`, the specifications with one and with two fresh vertices -/

section ImageSteps
variable {E : Type}

/-- the image of a pair (an edge and the other edges) in the atomic image -/
def BASim_imgP (P : BAPGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) :
    SEdge ((BASimX P) ⊕ (BASimY P)) × List (SEdge ((BASimX P) ⊕ (BASimY P))) :=
  (BAScost_imgE P.g p.1, p.2.map (BAScost_imgE P.g))

theorem BASim_imgP_mem (P : BAPGraph E) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) :
    BASim_imgP P p ∈ lwSplit P.img.g.solid := by
  change BASim_imgP P p ∈ lwSplit (promoteC P.g).merge.solid
  rw [BAScost_img_solid, lwSymm_lwSplit_map]
  exact List.mem_map.2 ⟨p, hp, rfl⟩

theorem BASim_imgP_snd (P : BAPGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) :
    (BASim_imgP P p).2 = p.2.map (BAScost_imgE P.g) := rfl

theorem BASim_imgP_mem2 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hq : q ∈ lwSplit p.2) :
    BASim_imgP P q ∈ lwSplit (BASim_imgP P p).2 := by
  rw [BASim_imgP_snd, lwSymm_lwSplit_map]
  exact List.mem_map.2 ⟨q, hq, rfl⟩

theorem BASim_pack_mono (P : PGraph E) {L L' : List (PGraph P.E')} (h : L ⊆ L') : lvl1Pack P L ⊆ lvl1Pack P L' :=
  List.map_subset _ h

/-- **The band step at the image of a weight** (`LocStep.weight` at `(c, t) = (0, 0)`): a blue circled edge whose ends lie in one atom is a light-weight of the image -/
theorem BASim_locStep_weight (P : BAPGraph E) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true) :
    LocStep m P.img (lvl1Pack P.img (lvl1WeightOuts0 m P.img.g (BASim_imgP P p) ((promoteC P.g).vmap p.1.src) false false)) := by
  refine LocStep.weight P.img (BASim_imgP P p) (BASim_imgP_mem P hp) ((promoteC P.g).vmap p.1.src) false false ?_
  have hv : (promoteC P.g).vmap p.1.dst = (promoteC P.g).vmap p.1.src :=
    ((BAAtomic_promoteC_vmap_eq_sameAtom P.g _ _).2 h.2.2).symm
  show BAScost_imgE P.g p.1 = _
  simp only [BAScost_imgE, h.1, h.2.1, h.2.2, Bool.and_self, hv]
  rfl


/-- the anchor table of the terms with one fresh vertex: `α = bpv 0 ↦ a`, `β = bpv 1` fresh -/
def BASim_anch2 {α : Type} (a : α) : Fin 2 → Option α := fun j => if j = 0 then some a else none
theorem BASim_anch2_zero {α : Type} (a : α) : BASim_anch2 a 0 = some a := by simp [BASim_anch2]
theorem BASim_anch2_one {α : Type} (a : α) : BASim_anch2 a 1 = none := by simp [BASim_anch2]

/-- the vertex map of the terms with `k = 2` new vertices matched with band terms with one new vertex: `α ↦ ā`, `β ↦ n0` -/
abbrev BASim_phi21 (P : BAPGraph E) (a : P.E' ⊕ P.I') : P.E' ⊕ (P.I' ⊕ Fin 2) → (BASimX P) ⊕ ((BASimY P) ⊕ Fin 1) :=
  BASim_phi P (owxEmb 1) (BASim_anch2 a) (fun _ => Sum.inr 0)

theorem BASim_phi21_emb (P : BAPGraph E) (a v : P.E' ⊕ P.I') : BASim_phi21 P a (owxEmb 2 v) = owxEmb 1 ((promoteC P.g).vmap v) :=
  BASim_phi_emb _ _ _ _ v
theorem BASim_phi21_alpha (P : BAPGraph E) (a : P.E' ⊕ P.I') : BASim_phi21 P a (bpv 0) = owxEmb 1 ((promoteC P.g).vmap a) :=
  BASim_phi_some _ _ _ _ 0 a (BASim_anch2_zero a)
theorem BASim_phi21_beta (P : BAPGraph E) (a : P.E' ⊕ P.I') : BASim_phi21 P a (bpv 1) = Sum.inr (Sum.inr 0) :=
  BASim_phi_none _ _ _ _ 1 (BASim_anch2_one a)

/-- **The specification of a term with one anchored and one fresh new vertex** (`α ↦ ā`, `β ↦ n0`; the band term has one new vertex): the tables are fixed, the lists are the data.
`hma`: the `M`-dotted edges of the term are `M_{aα}`, `M_{αa}`. -/
def BASim_mk21x (P : BAPGraph E) (a : P.E' ⊕ P.I') (rest : List (SEdge (P.E' ⊕ P.I'))) (s : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin 2))))
    (w : List (WEdge (P.E' ⊕ (P.I' ⊕ Fin 2)))) (md : List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin 2))))
    (restH : List (SEdge ((BASimX P) ⊕ (BASimY P)))) (sH : List (SEdge ((BASimX P) ⊕ ((BASimY P) ⊕ Fin 1))))
    (wH : List (WEdge ((BASimX P) ⊕ ((BASimY P) ⊕ Fin 1)))) (hd ex : List (SEdge ((BASimX P) ⊕ (BASimY P))))
    (hrest : ∀ e ∈ rest, e ∈ P.g.solid) (hrestH : (restH ++ ex).Perm (hd ++ rest.map (BAScost_imgE P.g)))
    (hma : bpM (owxEmb 2 a) (bpv 0) ∈ md) (hmd : ∀ m' ∈ md, BASim_phi21 P a m'.x = BASim_phi21 P a m'.y)
    (hs : (hd.map (SEdge.map (owxEmb 1)) ++ sH).Perm (ex.map (SEdge.map (owxEmb 1)) ++ s.map (BASim_phiE (BASim_phi21 P a))))
    (hw : List.Forall₂ (fun h w => WEdge.sameRev h (WEdge.map (BASim_phi21 P a) w)) wH w) :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) where
  hemb := fun y => rfl
  hinj := lvl1_owxEmb_inj 1
  anchor := BASim_anch2 a
  fresh := fun _ => Sum.inr 0
  rest := rest
  s := s
  w := w
  md := md
  restH := restH
  sH := sH
  wH := wH
  hd := hd
  ex := ex
  X := []
  hrest := hrest
  hrestH := hrestH
  hfresh := fun j _ v => lvl1_owxEmb_ne _ 0
  hsurj := fun z hz => by
    rcases z with y | j0
    · exfalso
      obtain ⟨v, hv⟩ := BAAtomic_vmap_surjective (promoteC P.g) (Sum.inr y)
      exact hz v (by rw [hv]; rfl)
    · exact ⟨1, BASim_anch2_one _, by fin_cases j0; rfl⟩
  hanch := fun j a' ha => by
    fin_cases j
    · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, BASim_anch2_zero] at ha
      cases ha
      exact BASim_sameAtom_symm ((BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_ext_md P.g rest _ _ _ _ hma))
    · rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, BASim_anch2_one] at ha
      cases ha
  hfr := fun j j' hj hj' _ => by
    fin_cases j <;> fin_cases j'
    · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, BASim_anch2_zero] at hj
      cases hj
    · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, BASim_anch2_zero] at hj
      cases hj
    · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, BASim_anch2_zero] at hj'
      cases hj'
    · exact BASim_sameAtom_refl _ _
  hmd := fun m' hm' => Or.inl (hmd m' hm')
  hX0 := by simp
  hX1 := by simp
  hs := by simpa using hs
  hw := hw


def BASim_mk21 (P : BAPGraph E) (a : P.E' ⊕ P.I') (rest : List (SEdge (P.E' ⊕ P.I'))) (s : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin 2))))
    (w : List (WEdge (P.E' ⊕ (P.I' ⊕ Fin 2)))) (md : List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin 2))))
    (restH : List (SEdge ((BASimX P) ⊕ (BASimY P)))) (sH : List (SEdge ((BASimX P) ⊕ ((BASimY P) ⊕ Fin 1))))
    (wH : List (WEdge ((BASimX P) ⊕ ((BASimY P) ⊕ Fin 1)))) (hd : List (SEdge ((BASimX P) ⊕ (BASimY P))))
    (hrest : ∀ e ∈ rest, e ∈ P.g.solid) (hrestH : restH.Perm (hd ++ rest.map (BAScost_imgE P.g)))
    (hma : bpM (owxEmb 2 a) (bpv 0) ∈ md) (hmd : ∀ m' ∈ md, BASim_phi21 P a m'.x = BASim_phi21 P a m'.y)
    (hs : (hd.map (SEdge.map (owxEmb 1)) ++ sH).Perm (s.map (BASim_phiE (BASim_phi21 P a))))
    (hw : List.Forall₂ (fun h w => WEdge.sameRev h (WEdge.map (BASim_phi21 P a) w)) wH w) :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21x P a rest s w md restH sH wH hd [] hrest (by simpa using hrestH) hma hmd (by simpa using hs) hw

theorem BASim_phi21_anchor_dot (P : BAPGraph E) (a : P.E' ⊕ P.I') :
    BASim_phi21 P a (owxEmb 2 a) = BASim_phi21 P a (bpv 0) :=
  (BASim_phi_emb P (owxEmb 1) (BASim_anch2 a) (fun _ => Sum.inr 0) a).trans
    (BASim_phi_some P (owxEmb 1) (BASim_anch2 a) (fun _ => Sum.inr 0) 0 a (BASim_anch2_zero a)).symm


/-- the old edges of the image: the pair `p` splits `P.img.g.solid` (up to order) -/
theorem BASim_restH_perm (P : BAPGraph E) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) :
    ((promoteC P.g).merge.solid).Perm ([BAScost_imgE P.g p.1] ++ p.2.map (BAScost_imgE P.g)) := by
  rw [BAScost_img_solid]
  simpa using ((lwSplit_perm P.g.solid p hp).map (BAScost_imgE P.g))

/-- the anchor table: `bpv 0 ↦ a`, the others fresh -/
def BASim_anch4 {α : Type} (a : α) : Fin 4 → Option α := fun j => if j = 0 then some a else none
theorem BASim_anch4_zero {α : Type} (a : α) : BASim_anch4 a 0 = some a := by simp [BASim_anch4]
theorem BASim_anch4_ne {α : Type} (a : α) (j : Fin 4) (h : j ≠ 0) : BASim_anch4 a j = none := by simp [BASim_anch4, h]

/-- the fresh band vertex of a new vertex: `y2, α ↦ n0`, `β ↦ n1` -/
def BASim_fresh4 {Y : Type} : Fin 4 → Y ⊕ Fin 2 := fun j => Sum.inr (if j = 3 then 1 else 0)

abbrev BASim_phi42 (P : BAPGraph E) (a : P.E' ⊕ P.I') : P.E' ⊕ (P.I' ⊕ Fin 4) → (BASimX P) ⊕ ((BASimY P) ⊕ Fin 2) :=
  BASim_phi P (owxEmb 2) (BASim_anch4 a) BASim_fresh4

theorem BASim_phi42_one (P : BAPGraph E) (a : P.E' ⊕ P.I') :
    BASim_phi P (owxEmb 2) (BASim_anch4 a) BASim_fresh4 (bpv 1) = Sum.inr (Sum.inr 0) :=
  BASim_phi_none _ _ _ _ 1 (BASim_anch4_ne a 1 (by decide))
theorem BASim_phi42_two (P : BAPGraph E) (a : P.E' ⊕ P.I') :
    BASim_phi P (owxEmb 2) (BASim_anch4 a) BASim_fresh4 (bpv 2) = Sum.inr (Sum.inr 0) :=
  BASim_phi_none _ _ _ _ 2 (BASim_anch4_ne a 2 (by decide))
theorem BASim_phi42_three (P : BAPGraph E) (a : P.E' ⊕ P.I') :
    BASim_phi P (owxEmb 2) (BASim_anch4 a) BASim_fresh4 (bpv 3) = Sum.inr (Sum.inr 1) :=
  BASim_phi_none _ _ _ _ 3 (BASim_anch4_ne a 3 (by decide))
theorem BASim_phi42_zero (P : BAPGraph E) (a : P.E' ⊕ P.I') :
    BASim_phi P (owxEmb 2) (BASim_anch4 a) BASim_fresh4 (bpv 0) = owxEmb 2 ((promoteC P.g).vmap a) :=
  BASim_phi_some _ _ _ _ 0 a (BASim_anch4_zero a)

/-- **The specification of a term with four new vertices** (`bpv 0 ↦ ā`, `bpv 1, bpv 2 ↦ n0`, `bpv 3 ↦ n1`; the band term has two new vertices) -/
def BASim_mk42 (P : BAPGraph E) (a : P.E' ⊕ P.I') (rest : List (SEdge (P.E' ⊕ P.I'))) (s : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin 4))))
    (w : List (WEdge (P.E' ⊕ (P.I' ⊕ Fin 4)))) (md : List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin 4))))
    (restH : List (SEdge ((BASimX P) ⊕ (BASimY P)))) (sH : List (SEdge ((BASimX P) ⊕ ((BASimY P) ⊕ Fin 2))))
    (wH : List (WEdge ((BASimX P) ⊕ ((BASimY P) ⊕ Fin 2)))) (hd : List (SEdge ((BASimX P) ⊕ (BASimY P))))
    (hrest : ∀ e ∈ rest, e ∈ P.g.solid) (hrestH : restH.Perm (hd ++ rest.map (BAScost_imgE P.g)))
    (hma : bpM (owxEmb 4 a) (bpv 0) ∈ md) (hm12 : bpM (bpv 1) (bpv 2) ∈ md)
    (hmd : ∀ m' ∈ md, (m'.x = owxEmb 4 a ∧ m'.y = bpv 0) ∨ (m'.x = bpv 0 ∧ m'.y = owxEmb 4 a) ∨
      (m'.x = bpv 1 ∧ m'.y = bpv 2) ∨ (m'.x = bpv 2 ∧ m'.y = bpv 1))
    (hs : (hd.map (SEdge.map (owxEmb 2)) ++ sH).Perm (s.map (BASim_phiE (BASim_phi42 P a))))
    (hw : List.Forall₂ (fun h w => WEdge.sameRev h (WEdge.map (BASim_phi42 P a) w)) wH w) :
    BASimExt P 4 ((BASimY P) ⊕ Fin 2) (owxEmb 2) where
  hemb := fun y => rfl
  hinj := lvl1_owxEmb_inj 2
  anchor := BASim_anch4 a
  fresh := BASim_fresh4
  rest := rest
  s := s
  w := w
  md := md
  restH := restH
  sH := sH
  wH := wH
  hd := hd
  ex := []
  X := []
  hrest := hrest
  hrestH := by simpa using hrestH
  hfresh := fun j _ v => by
    intro h
    exact lwSymm_emb_ne _ 2 (if j = 3 then 1 else 0) (by simpa [BASim_fresh4] using h.symm)
  hsurj := fun z hz => by
    rcases z with y | j0
    · exfalso
      obtain ⟨v, hv⟩ := BAAtomic_vmap_surjective (promoteC P.g) (Sum.inr y)
      exact hz v (by rw [hv]; rfl)
    · fin_cases j0
      · exact ⟨1, BASim_anch4_ne _ 1 (by decide), rfl⟩
      · exact ⟨3, BASim_anch4_ne _ 3 (by decide), rfl⟩
  hanch := fun j a' ha => by
    by_cases hj : j = 0
    · subst hj
      rw [BASim_anch4_zero] at ha
      cases ha
      exact BASim_sameAtom_symm ((BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_ext_md P.g rest _ _ _ _ hma))
    · rw [BASim_anch4_ne _ j hj] at ha
      cases ha
  hfr := fun j j' hj hj' hf => by
    have h12 : (BAGraph.ext 4 P.g rest s w md).sameAtom (bpv 1) (bpv 2) = true :=
      (BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_ext_md P.g rest _ _ _ _ hm12)
    have h0 : ∀ i : Fin 4, BASim_anch4 a i = none → i ≠ 0 := fun i hi h0 => by rw [h0, BASim_anch4_zero] at hi; cases hi
    have h0j := h0 j hj
    have h0j' := h0 j' hj'
    fin_cases j <;> fin_cases j'
    all_goals first | exact absurd rfl h0j | exact absurd rfl h0j' | skip
    all_goals first | exact BASim_sameAtom_refl _ _ | exact h12 | exact BASim_sameAtom_symm h12 | skip
    all_goals simp [BASim_fresh4] at hf
  hmd := fun m' hm' => by
    left
    rcases hmd m' hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 a (BASim_anch4_zero a)]
    · rw [h1, h2, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 a (BASim_anch4_zero a)]
    · rw [h1, h2, BASim_phi42_one, BASim_phi42_two]
    · rw [h1, h2, BASim_phi42_one, BASim_phi42_two]
  hX0 := by simp
  hX1 := by simp
  hs := by simpa using hs
  hw := hw


theorem BASim_twistP_ff {V : Type} (p : SEdge V × List (SEdge V)) : lwSymmTwistP false false p = p := by
  have h : lwSymmTwistS false false = (id : SEdge V → SEdge V) := funext fun e => rfl
  simp [lwSymmTwistP, h]

/-- the outputs of the weight step at the selector `(0, 0)`: the four terms of `(Owx)` as written in `LWWeightExp` (the twist by `(0, 0)` is the identity) -/
theorem BASim_weightOuts0_ff {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : E' ⊕ I') :
    lvl1WeightOuts0 m Γ p x false false = (owxET1 m Γ x).partition m ++ (owxET2 m Γ p x).partition m ++
      (lwSplit p.2).flatMap (fun q => (owxET3 m Γ x q).partition m) ++ (lwSplit p.2).flatMap (fun q => (owxET4 m Γ x q).partition m) := by
  simp only [lvl1WeightOuts0, lwSymmOwxT1, lwSymmOwxT2, lwSymmOwxT3, lwSymmOwxT4, BASim_twistP_ff]
  rfl

/-! ### The outputs of a tagged step: membership and the tag `band` -/

theorem BASim_mem_outsT (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (t : BAShape) (Q : BAPGraph E) (h : (t, Q) ∈ P.outsT tg Ts) :
    ∃ T ∈ Ts, ∃ T' ∈ T.splitG, tg T' = t ∧ P.outOf T' = Q := by
  unfold BAPGraph.outsT at h
  obtain ⟨T, hT, h⟩ := List.mem_flatMap.1 h
  obtain ⟨T', hT', h⟩ := List.mem_map.1 h
  exact ⟨T, hT, T', hT', congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem BASim_tagStd_band {E' I : Type} [Fintype E'] [DecidableEq E'] [Fintype I] [DecidableEq I] (Γ : BAGraph E' I) (k : ℕ)
    (T' : BAGraph E' (I ⊕ Fin k)) (h : Γ.tagStd k T' = BAShape.band) : Γ.extraB (owxEmb k) T' = false := by
  by_contra hc
  have hc' : Γ.extraB (owxEmb k) T' = true := by simpa using hc
  simp [BAGraph.tagStd, hc'] at h


end ImageSteps

end RBM.Graph

end
