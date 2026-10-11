/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAGGExp
/-! # T2423 probe (never merged): the statements of R1 `BASim` (item 1, Lemma E, `BAsim m`, `BAsim'`) against merged names and R0 -/
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedVariables false
noncomputable section
namespace RBM.Graph
open RBM
/-! ## 1. The frame vocabulary (not on `main`; copied from `t/T2395:RBM3D/Probe/T2395Pins.lean:154-209`) -/
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
/-! ## 2. The tags (`BAShape`, `BTStep`, `untag`: `t/T2397:RBM3D/Probe/T2397Pins.lean:123-126`, with `deriving DecidableEq`) and the tagged frame step -/
/-- The output classes of a step: `band` = matched with an output of a band `LocStep`; the BA-only shapes (`s1` is never assigned: `A1` is the band's `R2` `(δ, m)`, T2423 (a) F1). -/
inductive BAShape | band | s1 | e1 | e2 | macroA | macroB
  deriving DecidableEq
abbrev BTStep : Type 1 := BAPGraph (Fin 2) → List (BAShape × BAPGraph (Fin 2)) → Prop
def untag (T : BTStep) (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))) : Prop := ∃ LT, T P LT ∧ L = LT.map Prod.snd
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
/-! ## 3. Relabelling and the pins of R1 -/
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
/-! ## 4. Compiled instances: the concrete nondegenerate data of T2423 (a) (ii) (external `0, 1 = inl 0, inl 1`, internal `2, 3, 4 = inr 0, 1, 2`) -/
namespace T2423Inst
abbrev Ed := SEdge (Fin 2 ⊕ Fin 3)
/-- `P_A`: blue circled solid `2→1`, `0→2`, `1→0`; waved `S_{4,3}`; `M`-dot `{2,3}`; atoms `{0}, {1}, {2,3}, {4}`; the `gg` step at `p = 2→1`, `q = 0→2`. -/
def baPA : BAGraph (Fin 2) (Fin 3) :=
  ⟨⟨[⟨true, true, .inr 0, .inl 1⟩, ⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inl 1, .inl 0⟩], [⟨false, true, .inr 2, .inr 1⟩], [], 1⟩, [], [⟨true, .inr 0, .inr 1⟩]⟩
def pA : Ed × List Ed := (⟨true, true, .inr 0, .inl 1⟩, [⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inl 1, .inl 0⟩])
def qA : Ed × List Ed := (⟨true, true, .inl 0, .inr 0⟩, [⟨true, true, .inl 1, .inl 0⟩])
/-- `P_B` (macro (a)): solid `2→3` inside the atom `{2,3}`, `0→2`, `1→4`; the `within` step at `p = 2→3`. -/
def baPB : BAGraph (Fin 2) (Fin 3) :=
  ⟨⟨[⟨true, true, .inr 0, .inr 1⟩, ⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inl 1, .inr 2⟩], [⟨false, true, .inr 2, .inr 1⟩], [], 1⟩, [], [⟨true, .inr 0, .inr 1⟩]⟩
def pB : Ed × List Ed := (⟨true, true, .inr 0, .inr 1⟩, [⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inl 1, .inr 2⟩])
/-- `P_C` (macro (b)): solid `2→1`, `0→3`, `1→0`, the pair `p = 2→1`, `q = 0→3` at the two vertices `2, 3` of one atom. -/
def baPC : BAGraph (Fin 2) (Fin 3) :=
  ⟨⟨[⟨true, true, .inr 0, .inl 1⟩, ⟨true, true, .inl 0, .inr 1⟩, ⟨true, true, .inl 1, .inl 0⟩], [⟨false, true, .inr 2, .inr 1⟩], [], 1⟩, [], [⟨true, .inr 0, .inr 1⟩]⟩
def pC : Ed × List Ed := (⟨true, true, .inr 0, .inl 1⟩, [⟨true, true, .inl 0, .inr 1⟩, ⟨true, true, .inl 1, .inl 0⟩])
def qC : Ed × List Ed := (⟨true, true, .inl 0, .inr 1⟩, [⟨true, true, .inl 1, .inl 0⟩])
/-- `P_W`: a self-loop at the internal vertex `0` and an edge `x → 1` (the `weight` step); `P_E`: the degree-3 internal vertex of `t/T2395` `baF2` (the `edge` step). -/
def baPW : BAGraph (Fin 1) (Fin 2) := ⟨⟨[⟨true, true, .inr 0, .inr 0⟩, ⟨true, true, .inl 0, .inr 1⟩], [], [], 1⟩, [], []⟩
def pW : SEdge (Fin 1 ⊕ Fin 2) × List (SEdge (Fin 1 ⊕ Fin 2)) := (⟨true, true, .inr 0, .inr 0⟩, [⟨true, true, .inl 0, .inr 1⟩])
def baPE : BAGraph (Fin 2) (Fin 1) := ⟨⟨[⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inr 0, .inl 0⟩, ⟨true, true, .inl 1, .inr 0⟩,
  ⟨false, true, .inl 0, .inl 1⟩], [], [], 1⟩, [], []⟩
def pE : SEdge (Fin 2 ⊕ Fin 1) × List (SEdge (Fin 2 ⊕ Fin 1)) := (⟨true, true, .inr 0, .inl 0⟩, [⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inl 1, .inr 0⟩, ⟨false, true, .inl 0, .inl 1⟩])
/-- the tagged outputs of the five concrete steps -/
def ggFT := (baPG baPA).outsT (baPA.tagStd 2) (baPA.gg2 pA qA) ++ (baPG baPA).outsT (baPA.tagStd 4) (baPA.gg4 pA qA)
def ggF := (baPG baPA).outsOf (baPA.gg2 pA qA) ++ (baPG baPA).outsOf (baPA.gg4 pA qA)
/-- the step relations are nonempty at the data (all hypotheses of the five constructors by `decide`), `BTStep` is the `E = Fin 2` case -/
example : BTStep := @BAFrameStepT (Fin 2)
example : BAFrameStepT (baPG baPA) ggFT :=
  BAFrameStepT.gg (baPG baPA) pA (List.mem_cons_self ..) qA (List.mem_cons_self ..) (by decide) (0 : Fin 3) (by decide) (by decide) (by decide) (by decide)
example : BAFrameStepT (baPG baPB) ((baPG baPB).withinOutsT pB) := BAFrameStepT.within (baPG baPB) pB (List.mem_cons_self ..) (by decide)
example : BAFrameStepT (baPG baPC) ((baPG baPC).splitOutsT pC qC 0) :=
  BAFrameStepT.ggSplit (baPG baPC) pC (List.mem_cons_self ..) qC 0 rfl (by decide) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide : (0 : Fin 3) ≠ 1)
    (by decide) (by decide) (by decide) (by decide)
example : BAFrameStepT (baPG baPW) ((baPG baPW).outsT (baPW.tagStd 2) (baPW.lw2 pW) ++ (baPG baPW).outsT (baPW.tagStd 4) (baPW.lw4 pW)) :=
  BAFrameStepT.weight (baPG baPW) pW (List.mem_cons_self ..) (by decide)
example : BAFrameStepT (baPG baPE) ((baPG baPE).outsT baPE.tagT1 [BAGraph.lanlwT1 baPE pE] ++
    (baPG baPE).outsT (baPE.tagStd 2) ((lwSplit pE.2).map (BAGraph.lanlwD baPE pE))) :=
  BAFrameStepT.edge (baPG baPE) pE (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, List.mem_cons_self .., rfl⟩)) (by decide) (0 : Fin 1) (by decide)
    (by decide) (by decide) (by decide) (by decide)
/-- Lemma E at the data, by kernel evaluation: every `e2`-tagged output of `gg2`, `gg4` at `P_A` has a higher order or fewer external atoms than `P_A`. -/
example : (∀ T ∈ baPA.gg2 pA qA, ∀ T' ∈ T.splitG, baPA.tagStd 2 T' = BAShape.e2 → baPA.scalingOrder < T'.scalingOrder ∨ T'.nExt < baPA.nExt) ∧
    ∀ T ∈ baPA.gg4 pA qA, ∀ T' ∈ T.splitG, baPA.tagStd 4 T' = BAShape.e2 → baPA.scalingOrder < T'.scalingOrder ∨ T'.nExt < baPA.nExt := by decide +kernel
/-- the tag census of the three concrete steps (kernel evaluation of `outsT`, `tagStd`, `tagT1`) is that of the model of T2423 (a) (ii): `P_A` 31 outputs (23 `band`, 8 `e2`), `P_B` 51 (14, 3, 34 `macroA`), `P_C` 48 (8 `band`, 1 `e1`, 5 `e2`, 34 `macroB`; the model of (a) tags the extra output of `X.L1` `e2`: a label only). -/
example : (ggFT.map Prod.fst).count BAShape.band = 23 ∧ (ggFT.map Prod.fst).count BAShape.e2 = 8 ∧ ggFT.length = 31 := by decide +kernel
example : (((baPG baPB).withinOutsT pB).map Prod.fst).count BAShape.band = 14 ∧ (((baPG baPB).withinOutsT pB).map Prod.fst).count BAShape.e2 = 3 ∧
    (((baPG baPB).withinOutsT pB).map Prod.fst).count BAShape.macroA = 34 ∧ ((baPG baPB).withinOutsT pB).length = 51 := by decide +kernel
example : (((baPG baPC).splitOutsT pC qC 0).map Prod.fst).count BAShape.band = 8 ∧ (((baPG baPC).splitOutsT pC qC 0).map Prod.fst).count BAShape.e1 = 1 ∧
    (((baPG baPC).splitOutsT pC qC 0).map Prod.fst).count BAShape.e2 = 5 ∧ (((baPG baPC).splitOutsT pC qC 0).map Prod.fst).count BAShape.macroB = 34 ∧
    ((baPG baPC).splitOutsT pC qC 0).length = 48 := by decide +kernel
/-- **The pins at the data** (the pins are other rows' targets and stay hypotheses of the examples; every deterministic hypothesis is discharged): `BAMatch` at a
`band`-tagged output and `BAExtraGood` at an `e2`-tagged output of the `gg` step at `P_A`, both of which exist. -/
example (m : ℂ) (hM : BAMatch m) (hX : BAExtraGood) :
    (∃ Q, (BAShape.band, Q) ∈ ggFT ∧ ∃ L' : List (PGraph (Fin 2)), LocStep m (baPG baPA).img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img) ∧
    ∃ Q, (BAShape.e2, Q) ∈ ggFT ∧ ((baPG baPA).g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < (baPG baPA).g.nExt) := by
  have hT : BAFrameStepT (baPG baPA) ggFT :=
    BAFrameStepT.gg (baPG baPA) pA (List.mem_cons_self ..) qA (List.mem_cons_self ..) (by decide) (0 : Fin 3) (by decide) (by decide) (by decide) (by decide)
  have key : ∀ (l : List (BAShape × BAPGraph (Fin 2))) (t : BAShape), t ∈ l.map Prod.fst → ∃ Q, (t, Q) ∈ l := fun l t h => by
    obtain ⟨⟨t', Q⟩, hm, rfl⟩ := List.mem_map.1 h; exact ⟨Q, hm⟩
  obtain ⟨Q, hQ⟩ := key ggFT .band (by decide +kernel)
  obtain ⟨Q', hQ'⟩ := key ggFT .e2 (by decide +kernel)
  exact ⟨⟨Q, hQ, hM _ _ hT (by decide) Q hQ⟩, ⟨Q', hQ', hX _ _ hT (by decide) Q' (Or.inr hQ')⟩⟩
/-- `BAsim`, `BAsim'` at the `gg`, `within`, `ggSplit` steps, `BAMatch` at the `within`, `ggSplit`, `weight`, `edge` steps, `BAFrameStepT_untag` at `gg`. -/
example (m : ℂ) (hM : BAMatch m) (hS : BAsim m) (hS' : BAsim' m) (hU : BAFrameStepT_untag) : True := by
  have hNA : (baPG baPA).g.Normal := by decide
  have hNB : (baPG baPB).g.Normal := by decide
  have hNC : (baPG baPC).g.Normal := by decide
  have hFA : BAFrameStep (baPG baPA) ggF :=
    BAFrameStep.gg (baPG baPA) pA (List.mem_cons_self ..) qA (List.mem_cons_self ..) (by decide) (0 : Fin 3) (by decide) (by decide) (by decide) (by decide)
  have hFB : BAFrameStep (baPG baPB) ((baPG baPB).withinOuts pB) := BAFrameStep.within (baPG baPB) pB (List.mem_cons_self ..) (by decide)
  have hFC : BAFrameStep (baPG baPC) ((baPG baPC).splitOuts pC qC 0) :=
    BAFrameStep.ggSplit (baPG baPC) pC (List.mem_cons_self ..) qC 0 rfl (by decide) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide : (0 : Fin 3) ≠ 1)
      (by decide) (by decide) (by decide) (by decide)
  have hTB : BAFrameStepT (baPG baPB) ((baPG baPB).withinOutsT pB) := BAFrameStepT.within (baPG baPB) pB (List.mem_cons_self ..) (by decide)
  have hTC : BAFrameStepT (baPG baPC) ((baPG baPC).splitOutsT pC qC 0) :=
    BAFrameStepT.ggSplit (baPG baPC) pC (List.mem_cons_self ..) qC 0 rfl (by decide) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide : (0 : Fin 3) ≠ 1)
      (by decide) (by decide) (by decide) (by decide)
  have hTW : BAFrameStepT (baPG baPW) ((baPG baPW).outsT (baPW.tagStd 2) (baPW.lw2 pW) ++ (baPG baPW).outsT (baPW.tagStd 4) (baPW.lw4 pW)) :=
    BAFrameStepT.weight (baPG baPW) pW (List.mem_cons_self ..) (by decide)
  have hTE : BAFrameStepT (baPG baPE) ((baPG baPE).outsT baPE.tagT1 [BAGraph.lanlwT1 baPE pE] ++
      (baPG baPE).outsT (baPE.tagStd 2) ((lwSplit pE.2).map (BAGraph.lanlwD baPE pE))) :=
    BAFrameStepT.edge (baPG baPE) pE (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, List.mem_cons_self .., rfl⟩)) (by decide) (0 : Fin 1) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have _ := hS _ _ hFA hNA
  have _ := hS' _ _ hFA hNA
  have _ := hS' _ _ hFB hNB
  have _ := hS' _ _ hFC hNC
  have _ := hM _ _ hTB hNB
  have _ := hM _ _ hTC hNC
  have _ := hM _ _ hTW (by decide)
  have _ := hM _ _ hTE (by decide)
  have _ := hU _ _ |>.1 hFA
  trivial
/-- **F1 of T2423 (a), confirmed on the band's own term**: the dotted edge partition (`LGraph.partition`, `LWVocab.lean:1303`) of the real `R2` builder `oe2xR2`
(`m³ S⁺_{xy} G_{y'y} f`, `LWGGExp.lean:485`) at two external vertices `y = 0`, `y' = 1` has an output with `ext 0 = ext 1`: the option `1_{y'=y}` of `LGraph.aPairs`
(`LWVocab.lean:1061`) merges two external vertices (`T2050b`), the band partner of the BA first sum `A1` (`BAShape.s1` is never assigned). -/
example (m : ℂ) : ∃ Q ∈ (oe2xR2 m (⟨[], [], [], 1⟩ : LGraph (Fin 2) (Fin 1)) (⟨true, true, .inl 1, .inl 0⟩, []) 0 (.inl 0) (.inl 1)).partition m,
    Q.ext 0 = Q.ext 1 := by
  classical
  set T : LGraph (Fin 2) (Fin 1) := oe2xR2 m (⟨[], [], [], 1⟩ : LGraph (Fin 2) (Fin 1)) (⟨true, true, .inl 1, .inl 0⟩, []) 0 (.inl 0) (.inl 1) with hT
  have hTs : T.solid = [⟨true, false, .inl 1, .inl 0⟩] ∧ T.dotted = [] := by simp [hT, oe2xR2, LGraph.owxExt]
  have hdc : T.dotChoices = [(1, [⟨true, .inl 1, .inl 0⟩]), (1, [⟨false, .inl 1, .inl 0⟩])] := by
    simp [LGraph.dotChoices, LGraph.dotAtoms, LGraph.aPairs, LGraph.bEdges, hTs, lwDedupPairs, LGraph.XBetween, lwCombineAtoms]
  set Δ := T.withDots (1, [⟨true, .inl 1, .inl 0⟩]) with hΔ
  have hedge : (⟨true, .inl 1, .inl 0⟩ : DEdge (Fin 2 ⊕ Fin 1)) ∈ Δ.dotted := by simp [hΔ, LGraph.withDots, LGraph.dotBase, hTs]
  have hmem : Δ ∈ T.partitionTerms := by
    unfold LGraph.partitionTerms
    refine List.mem_filter.2 ⟨?_, ?_⟩
    · rw [hdc]; simp [hΔ]
    · rw [decide_eq_true_eq]
      intro e he hf
      have : e ∈ Δ.dotted := he
      simp [hΔ, LGraph.withDots, LGraph.dotBase, hTs, LGraph.isB] at this
      subst this
      simp at hf
  have hne : ∀ {V : Type} [DecidableEq V] (es : List (SEdge V)), lwSplitLoops m es ≠ [] := by
    intro V _ es; induction es with
    | nil => simp [lwSplitLoops]
    | cons e es ih =>
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ ih
      simp only [lwSplitLoops, ne_eq, List.flatMap_eq_nil_iff, not_forall]
      refine ⟨r, hr, ?_⟩
      split_ifs <;> simp
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ (show Δ.merge.splitWeights m ≠ [] by simpa [LGraph.splitWeights] using hne Δ.merge.solid)
  exact ⟨_, List.mem_flatMap.2 ⟨Δ, hmem, List.mem_map.2 ⟨g, hg, rfl⟩⟩, Subtype.ext (Quotient.sound (Relation.EqvGen.rel _ _ ⟨_, hedge, rfl, Or.inr ⟨rfl, rfl⟩⟩))⟩
end T2423Inst
/-! ## 5. `#check` of the new statements and of the merged / R0 names they stand on -/
#check @BAFrameStep
#check @BAFrameStepT
#check @BAShape
#check @BTStep
#check @untag
#check @PGraph.BAEquiv
#check @BAMatch
#check @BAExtraGood
#check @BAFrameStepT_untag
#check @BAsim
#check @BAsim'
#check @BAPGraph.baInv
#check @PGraph.baInv
#check @BAPGraph.img
#check @BAimg
#check @BAimg_holds
#check @LocStep
#check @baPG
#print axioms BAMatch
#print axioms BAExtraGood
#print axioms BAFrameStepT_untag
#print axioms BAsim
#print axioms BAsim'
#print axioms BAFrameStepT
#print axioms PGraph.BAEquiv
end RBM.Graph
end
