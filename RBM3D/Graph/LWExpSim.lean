/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.LWExpCert

/-!
# LW-14e-3 (T2311): the simulation bridge between the computable model and the real expansion

The certificate of `LWExpCert` (T2306) lives on the computable model `MNode`
(`LGraph (Fin (a+1)) (Fin b)`, `cMerge`, `famsX`); the expansion of `LWExpTerm5` (T2307) lives
on the packed graphs `PGraph (Fin 2)` (`partitionX`, `RCand.kids`).  This file proves that the
two agree up to a renaming of the vertices: `partitionSim` (Bridge 1) and `childrenSim`
(Bridge 2), with the simulation relation `Rel`.  There is no paper content (`B:66-94` is the
procedure) and no hypothesis.

Contents (namespace `RBM.Gauss.Sizes`; `MNode.toP` and `Cand.toR` are in `RBM.Graph.LWCert`, so
that `N.toP h` is field notation):
1. the pinned definitions and lemmas, verbatim from the probe
   `t/T2288:RBM3D/Probe/T2288Cert.lean` 457-610: `MNode.toP`, `Rel`, `Rel.scalingOrder_eq`,
   `Rel.tgt_eq`, `Rel.leaf_iff`, `cands_spec`, `lwSplit_map`, `Rel.cand`, `Cand.toR`,
   `lwG5Cand_of_cands`, `cPartitionX`, `famsX`, `fams_eq_famsX`, `childrenX`, `PartitionSim`,
   `ChildrenSim`;
2. (L1) the union-find labels `labsOf` give the classes with least-vertex labels
   (`lwExpSim_labsOf_good`); the class numbers (`posOf`, `repsOf`) are ranks (`Nat.count`);
   `cMerge` is a labelling whose fibres are the classes of the `=`-dotted edges
   (`lwExpSim_cMerge_some`, `lwExpSim_cMerge_none`);
3. (L2) a labelling with the classes as fibres gives the equivalences `eE`, `eI` of `Rel`
   through which `vmap` factors (`lwExpSim_equivs`);
4. classes, the dotted terms and the dotted choices under a relabelling by an equivalence
   (`lwExpSim_cls_relabel`, `lwExpSim_terms_relabel`; L4);
5. one dotted term (`lwExpSim_term_some`), the partition of a relabelled graph against
   `partitionX` (`lwExpSim_partition_sim`; L3);
6. the bridges: `partitionSim` (no relabelling), `childrenSim` (the seven families of
   `RCand.kids`; the renumbering `renum` is the relabelling; L5), `rel_self`;
7. the compiled instances: the root `LWG5Graph false false` (163 partition terms) and the
   explicit normal graph `lwExpTerm3_instGraph` at its candidate (11 families, 550 children).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

noncomputable section

namespace RBM.Gauss.Sizes

open RBM RBM.Graph RBM.Graph.LWCert

/-! ## 1. The pinned definitions and lemmas (probe 457-610, verbatim) -/

/-- `lwSplit` commutes with `map`. -/
theorem lwSplit_map {κ μ : Type*} (f : κ → μ) (l : List κ) :
    lwSplit (l.map f) = (lwSplit l).map (fun p => (f p.1, p.2.map f)) := by
  induction l with
  | nil => simp [lwSplit]
  | cons a l ih => simp [lwSplit, ih, List.map_map, Function.comp_def]

/-- The spec of `cands`: every entry is a candidate in the shape of `LWG5Cand` / `oe2x_graph_E`. -/
theorem cands_spec {a b : ℕ} (g : LGraph (Fin (a+1)) (Fin b)) (c : Cand a b) (hc : c ∈ cands g) :
    c.p ∈ lwSplit g.solid ∧ c.q ∈ lwSplit c.p.2 ∧ c.y ≠ Sum.inr c.x ∧ c.y' ≠ Sum.inr c.x ∧
      c.p.1 = ⟨true, false, Sum.inr c.x, c.y⟩ ∧ c.q.1 = ⟨true, false, c.y', Sum.inr c.x⟩ := by
  unfold cands at hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨p, hp, hc⟩ := hc
  rcases hps : p.1.src with u | x
  · rw [hps] at hc; simp at hc
  · rw [hps] at hc
    dsimp only at hc
    split_ifs at hc with hcond
    · simp only [List.mem_filterMap] at hc
      obtain ⟨q, hq, hc⟩ := hc
      split_ifs at hc with hcq
      · cases hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcond hcq
        obtain ⟨⟨hσ, hcirc⟩, hne⟩ := hcond
        obtain ⟨⟨⟨hσ', hcirc'⟩, hdst⟩, hne'⟩ := hcq
        refine ⟨hp, hq, hne, hne', ?_, ?_⟩
        · have h1 : p.1 = ⟨p.1.σ, p.1.circ, p.1.src, p.1.dst⟩ := rfl
          rw [hσ, hcirc, hps] at h1
          exact h1
        · have h1 : q.1 = ⟨q.1.σ, q.1.circ, q.1.src, q.1.dst⟩ := rfl
          rw [hσ', hcirc', hdst] at h1
          exact h1
    · simp at hc

end RBM.Gauss.Sizes

namespace RBM.Graph.LWCert

/-- The model node as a packed graph (needs the external map onto). -/
def MNode.toP (N : MNode) (h : Function.Surjective N.ext) : PGraph (Fin 2) where
  E' := Fin (N.a + 1)
  I' := Fin N.b
  ext := N.ext
  ext_surj := h
  g := N.g

open RBM.Gauss.Sizes in
/-- The candidate of the model node as a candidate of the packed graph (in the sense of section 2). -/
def Cand.toR (N : MNode) (h : Function.Surjective N.ext) (c : Cand N.a N.b) (hc : c ∈ cands N.g) : RCand (N.toP h) :=
  ⟨c.x, c.y, c.y', c.p, c.q, (cands_spec N.g c hc).1, (cands_spec N.g c hc).2.1, (cands_spec N.g c hc).2.2.1,
    (cands_spec N.g c hc).2.2.2.1, (cands_spec N.g c hc).2.2.2.2.1, (cands_spec N.g c hc).2.2.2.2.2⟩

end RBM.Graph.LWCert

namespace RBM.Gauss.Sizes

open RBM RBM.Graph RBM.Graph.LWCert

/-- **Simulation relation**: `P` is the model node `N` with its vertices renamed by equivalences (the colours of the waved
edges are not compared: no property used depends on them; this is why `k = true` needs no separate certificate). -/
def Rel (N : MNode) (P : PGraph (Fin 2)) : Prop :=
  ∃ (eE : Fin (N.a + 1) ≃ P.E') (eI : Fin N.b ≃ P.I'),
    (∀ i, P.ext i = eE (N.ext i)) ∧
    P.g.solid = N.g.solid.map (SEdge.map (Sum.map eE eI)) ∧
    P.g.waved.map (fun e => (e.x, e.y)) = N.g.waved.map (fun e => (Sum.map eE eI e.x, Sum.map eE eI e.y)) ∧
    P.g.dotted = N.g.dotted.map (DEdge.map (Sum.map eE eI))

/-- `Rel` preserves the scaling order. -/
theorem Rel.scalingOrder_eq {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) : P.g.scalingOrder = N.g.scalingOrder := by
  obtain ⟨eE, eI, -, hs, hw, -⟩ := h
  have hS : P.g.nS = N.g.nS := by simp [LGraph.nS, hs]
  have hW : P.g.nW = N.g.nW := by
    have := congrArg List.length hw
    simpa [LGraph.nW] using this
  have hV : P.g.nV = N.g.nV := by simp only [LGraph.nV]; exact (Fintype.card_congr eI).symm
  simp only [LGraph.scalingOrder, LGraph.counters, ord, hS, hW, hV]

/-- `Rel` preserves the order target. -/
theorem Rel.tgt_eq {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) :
    (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) = tgt N := by
  obtain ⟨eE, eI, he, -⟩ := h
  simp only [tgt, he, EmbeddingLike.apply_eq_iff_eq]

/-- A leaf of the model is a leaf of every packed graph related to it. -/
theorem Rel.leaf_iff {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) :
    leaf N = true ↔ (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder := by
  rw [h.scalingOrder_eq, h.tgt_eq]
  simp [leaf]

/-- **A model candidate is a candidate of every related packed graph** (`LWG5Cand` under `relabel (Equiv.sumCongr ..)`). -/
theorem Rel.cand {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) (c : Cand N.a N.b) (hc : c ∈ cands N.g) : LWG5Cand P := by
  obtain ⟨eE, eI, -, hs, -, -⟩ := h
  obtain ⟨hp, hq, hy, hy', hp1, hq1⟩ := cands_spec N.g c hc
  set φ : Fin (N.a + 1) ⊕ Fin N.b → P.E' ⊕ P.I' := Sum.map eE eI with hφ
  have hinj : Function.Injective φ := (Equiv.sumCongr eE eI).injective
  refine ⟨eI c.x, φ c.y, φ c.y', (c.p.1.map φ, c.p.2.map (SEdge.map φ)), (c.q.1.map φ, c.q.2.map (SEdge.map φ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, lwSplit_map]
    exact List.mem_map.2 ⟨c.p, hp, rfl⟩
  · have h2 : (c.q.1.map φ, c.q.2.map (SEdge.map φ)) ∈
        (lwSplit c.p.2).map (fun p => (p.1.map φ, p.2.map (SEdge.map φ))) := List.mem_map.2 ⟨c.q, hq, rfl⟩
    rwa [← lwSplit_map] at h2
  · intro h'; exact hy (hinj (by simpa [hφ] using h'))
  · intro h'; exact hy' (hinj (by simpa [hφ] using h'))
  · simp only [hp1, SEdge.map, hφ, Sum.map_inr]
  · simp only [hq1, SEdge.map, hφ, Sum.map_inr]

/-- A model node has a candidate iff its packed graph satisfies `LWG5Cand` (one direction, from `cands_spec`). -/
theorem lwG5Cand_of_cands (N : MNode) (h : Function.Surjective N.ext) (hne : (cands N.g).isEmpty = false) :
    LWG5Cand (N.toP h) := by
  cases hc : cands N.g with
  | nil => rw [hc] at hne; simp at hne
  | cons c cs =>
    exact ⟨c.x, c.y, c.y', c.p, c.q, (cands_spec N.g c (by rw [hc]; simp)).1, (cands_spec N.g c (by rw [hc]; simp)).2.1,
      (cands_spec N.g c (by rw [hc]; simp)).2.2.1, (cands_spec N.g c (by rw [hc]; simp)).2.2.2.1,
      (cands_spec N.g c (by rw [hc]; simp)).2.2.2.2.1, (cands_spec N.g c (by rw [hc]; simp)).2.2.2.2.2⟩

/-- The model partition with the exponents of `m`, `m̄` (same order as `LGraph.partition`). -/
def cPartitionX {a b : ℕ} (Γ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)) : List ((ℕ × ℕ) × MNode) :=
  (Γ.dotChoices.map Γ.withDots).flatMap fun Δ =>
    match cMerge Δ ext with
    | none => []
    | some N => (lwSplitLoopsX N.g.solid).map fun r => (r.1, { N with g := { N.g with solid := r.2 } })

/-- The families with the exponent of `m` (`R2, R4, R6, R8`: `3`; `R3, R5, R7`: `1`). -/
def famsX {a b : ℕ} (g : LGraph (Fin (a+1)) (Fin b)) (c : Cand a b) :
    List ((ℕ × ℕ) × Σ b' : ℕ, LGraph (Fin (a+1)) (Fin b')) :=
  [((3, 0), ⟨b, oe2xR2 1 g c.q c.x c.y c.y'⟩), ((1, 0), ⟨b + 1, renum (owxT1 1 g c.x)⟩),
   ((3, 0), ⟨b + 2, renum (oe2xR4 1 g c.q c.x c.y c.y')⟩), ((1, 0), ⟨b + 1, renum (oe2xR5 1 g c.q c.x c.y c.y')⟩),
   ((3, 0), ⟨b + 2, renum (oe2xR6 1 g c.q c.x c.y c.y')⟩)] ++
  (lwSplit c.q.2).flatMap fun q' =>
    [((1, 0), ⟨b + 1, renum (oe2xR7 1 g c.x c.y c.y' q')⟩), ((3, 0), ⟨b + 2, renum (oe2xR8 1 g c.x c.y c.y' q')⟩)]

theorem fams_eq_famsX {a b : ℕ} (g : LGraph (Fin (a+1)) (Fin b)) (c : Cand a b) : fams g c = (famsX g c).map Prod.snd := by
  simp [fams, famsX, List.map_flatMap]

/-- All children of a model node at a candidate, with exponents (not only the below-target ones). -/
def childrenX (N : MNode) (c : Cand N.a N.b) : List ((ℕ × ℕ) × MNode) :=
  (famsX N.g c).flatMap fun f => (cPartitionX f.2.2 N.ext).map fun r => ((r.1.1 + f.1.1, r.1.2 + f.1.2), r.2)

/-- **Bridge 1 (the partition, exact)**: the model partition of a packed model node is, list-wise, the real
`LGraph.partition` of its graph, up to the equivalences of `Rel`, with coefficients `m^j m̄^{j'} c`. -/
def PartitionSim : Prop :=
  ∀ (N : MNode) (h : Function.Surjective N.ext) (m : ℂ),
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : PGraph (Fin 2)) => Rel r.2 Q ∧ Q.g.coeff = m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff)
      (cPartitionX N.g N.ext) ((N.g.partition m).map (pcomp (N.toP h)))

/-- **Bridge 2 (the children)**: the real children of the packed node at a candidate (`RCand.kids`) are, list-wise,
the model children up to `Rel`. -/
def ChildrenSim : Prop :=
  ∀ (N : MNode) (h : Function.Surjective N.ext) (c : Cand N.a N.b) (hc : c ∈ cands N.g),
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
      (childrenX N c) (Cand.toR N h c hc).kids

/-! ## 2. The model merge: labels, class numbers, and `cMerge` as a labelling whose fibres are the classes -/

section Labs

variable {a b : ℕ}

theorem lwExpSim_vi_lt (v : Fin (a+1) ⊕ Fin b) : vi a b v < a + 1 + b := by
  rcases v with i | j
  · have := i.isLt; simp only [vi, Sum.elim_inl]; omega
  · have := j.isLt; simp only [vi, Sum.elim_inr]; omega

theorem lwExpSim_vi_inj {u v : Fin (a+1) ⊕ Fin b} (h : vi a b u = vi a b v) : u = v := by
  rcases u with i | j <;> rcases v with i' | j' <;> simp only [vi, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · exfalso; have := i.isLt; omega
  · exfalso; have := i'.isLt; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

private theorem lwExpSim_vi_inl (i : Fin (a+1)) : vi a b (Sum.inl i) = i.val := rfl

theorem lwExpSim_vi_inr (j : Fin b) : vi a b (Sum.inr j) = a + 1 + j.val := rfl

private theorem lwExpSim_getD_map (f : ℕ → ℕ) (l : List ℕ) {i : ℕ} (h : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h)]
  simp

/-- The relation on the vertices generated by a list of dotted edges. -/
def lwExpSim_R (L : List (DEdge (Fin (a+1) ⊕ Fin b))) (u v : Fin (a+1) ⊕ Fin b) : Prop :=
  ∃ e ∈ L, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)

/-- The invariant of the label list: labels are least class vertices, and two vertices have the same label iff they are
related by the equivalence relation generated by `r`. -/
def lwExpSim_LabsGood (a b : ℕ) (labs : List ℕ) (r : Fin (a+1) ⊕ Fin b → Fin (a+1) ⊕ Fin b → Prop) : Prop :=
  labs.length = a + 1 + b ∧ (∀ i < a + 1 + b, labs.getD i 0 ≤ i) ∧
    (∀ i < a + 1 + b, labs.getD (labs.getD i 0) 0 = labs.getD i 0) ∧
    ∀ u v, labs.getD (vi a b u) 0 = labs.getD (vi a b v) 0 ↔ Relation.EqvGen r u v

private theorem lwExpSim_unite_getD {labs : List ℕ} {n : ℕ} (hlen : labs.length = n) (p q : ℕ) {i : ℕ} (hi : i < n) :
    (unite labs p q).getD i 0 =
      if labs.getD i 0 = labs.getD p 0 ∨ labs.getD i 0 = labs.getD q 0 then min (labs.getD p 0) (labs.getD q 0)
      else labs.getD i 0 := by
  unfold unite
  rw [lwExpSim_getD_map _ _ (by omega)]
  simp only [Bool.or_eq_true, beq_iff_eq]

private theorem lwExpSim_good_base : lwExpSim_LabsGood a b (List.range (a + 1 + b)) (lwExpSim_R []) := by
  have hget : ∀ i < a + 1 + b, (List.range (a + 1 + b)).getD i 0 = i := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_range]
  refine ⟨by simp, fun i hi => (hget i hi).le, fun i hi => by rw [hget i hi, hget i hi], fun u v => ?_⟩
  rw [hget _ (lwExpSim_vi_lt u), hget _ (lwExpSim_vi_lt v)]
  constructor
  · intro h
    exact lwExpSim_vi_inj h ▸ Relation.EqvGen.refl _
  · intro h
    have : ∀ u v, Relation.EqvGen (lwExpSim_R (a := a) (b := b) []) u v → u = v := by
      intro u v h
      induction h with
      | rel x y h => obtain ⟨e, he, -⟩ := h; simp at he
      | refl x => rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    rw [this u v h]


theorem lwExpSim_good_unite {labs : List ℕ} {r r' : Fin (a+1) ⊕ Fin b → Fin (a+1) ⊕ Fin b → Prop}
    (hg : lwExpSim_LabsGood a b labs r) (x y : Fin (a+1) ⊕ Fin b)
    (hr' : ∀ u v, r' u v ↔ r u v ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    lwExpSim_LabsGood a b (unite labs (vi a b x) (vi a b y)) r' := by
  obtain ⟨hlen, hle, hid, hiff⟩ := hg
  have hxn := lwExpSim_vi_lt x
  have hyn := lwExpSim_vi_lt y
  obtain ⟨lx, hlx⟩ : ∃ lx, lx = labs.getD (vi a b x) 0 := ⟨_, rfl⟩
  obtain ⟨ly, hly⟩ : ∃ ly, ly = labs.getD (vi a b y) 0 := ⟨_, rfl⟩
  have hlxn : lx ≤ vi a b x := hlx ▸ hle _ hxn
  have hlyn : ly ≤ vi a b y := hly ▸ hle _ hyn
  have hlxid : labs.getD lx 0 = lx := by rw [hlx]; exact hid _ hxn
  have hlyid : labs.getD ly 0 = ly := by rw [hly]; exact hid _ hyn
  have key : ∀ i < a + 1 + b, (unite labs (vi a b x) (vi a b y)).getD i 0 =
      if labs.getD i 0 = lx ∨ labs.getD i 0 = ly then min lx ly else labs.getD i 0 := by
    intro i hi
    rw [lwExpSim_unite_getD hlen _ _ hi, ← hlx, ← hly]
  have hmono : ∀ u v, Relation.EqvGen r u v → Relation.EqvGen r' u v := fun u v h =>
    Relation.EqvGen.mono (fun p q hpq => (hr' p q).2 (Or.inl hpq)) u v h
  have hxy : Relation.EqvGen r' x y := Relation.EqvGen.rel _ _ ((hr' x y).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have hux : ∀ u, labs.getD (vi a b u) 0 = lx → Relation.EqvGen r' u x := fun u h =>
    hmono _ _ ((hiff u x).1 (h.trans hlx))
  have huy : ∀ u, labs.getD (vi a b u) 0 = ly → Relation.EqvGen r' u y := fun u h =>
    hmono _ _ ((hiff u y).1 (h.trans hly))
  refine ⟨by simp [unite, hlen], ?_, ?_, ?_⟩
  · intro i hi
    rw [key i hi]
    split_ifs with h
    · have := hle i hi
      omega
    · exact hle i hi
  · intro i hi
    have hli : labs.getD i 0 ≤ i := hle i hi
    have hmn : min lx ly < a + 1 + b := by omega
    have hmid : labs.getD (min lx ly) 0 = min lx ly := by
      rcases min_choice lx ly with h | h <;> rw [h]
      · exact hlxid
      · exact hlyid
    rw [key i hi]
    by_cases hS : labs.getD i 0 = lx ∨ labs.getD i 0 = ly
    · simp only [hS, ↓reduceIte]
      rw [key _ hmn]
      have : labs.getD (min lx ly) 0 = lx ∨ labs.getD (min lx ly) 0 = ly := by
        rw [hmid]; exact min_choice lx ly
      simp only [this, ↓reduceIte]
    · simp only [hS, ↓reduceIte]
      have hl : labs.getD i 0 < a + 1 + b := by omega
      rw [key _ hl, hid i hi]
      have hS' : ¬ (labs.getD i 0 = lx ∨ labs.getD i 0 = ly) := hS
      simp only [hS', ↓reduceIte]
  · intro u v
    rw [key _ (lwExpSim_vi_lt u), key _ (lwExpSim_vi_lt v)]
    constructor
    · intro h
      by_cases hu : labs.getD (vi a b u) 0 = lx ∨ labs.getD (vi a b u) 0 = ly <;>
        by_cases hv : labs.getD (vi a b v) 0 = lx ∨ labs.getD (vi a b v) 0 = ly
      · simp only [hu, hv, ↓reduceIte] at h
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact (hux u hu).trans _ _ _ (hux v hv).symm
        · exact ((hux u hu).trans _ _ _ hxy).trans _ _ _ (huy v hv).symm
        · exact ((huy u hu).trans _ _ _ hxy.symm).trans _ _ _ (hux v hv).symm
        · exact (huy u hu).trans _ _ _ (huy v hv).symm
      · simp only [hu, hv, ↓reduceIte, ↓reduceIte] at h
        exfalso
        omega
      · simp only [hu, hv, ↓reduceIte, ↓reduceIte] at h
        exfalso
        omega
      · simp only [hu, hv, ↓reduceIte] at h
        exact hmono _ _ ((hiff u v).1 h)
    · intro H
      have hall : ∀ p q, Relation.EqvGen r' p q →
          (unite labs (vi a b x) (vi a b y)).getD (vi a b p) 0 = (unite labs (vi a b x) (vi a b y)).getD (vi a b q) 0 := by
        intro p q Hpq
        induction Hpq with
        | rel p q h =>
          rw [key _ (lwExpSim_vi_lt p), key _ (lwExpSim_vi_lt q)]
          rcases (hr' p q).1 h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [(hiff p q).2 (Relation.EqvGen.rel _ _ h)]
          · rw [← hlx, ← hly]
            simp
          · rw [← hlx, ← hly]
            simp
        | refl p => rfl
        | symm p q _ ih => exact ih.symm
        | trans p q s _ _ ih1 ih2 => exact ih1.trans ih2
      have := hall u v H
      rw [key _ (lwExpSim_vi_lt u), key _ (lwExpSim_vi_lt v)] at this
      exact this

theorem lwExpSim_labsOf_good (L : List (DEdge (Fin (a+1) ⊕ Fin b))) :
    lwExpSim_LabsGood a b (labsOf (a + 1 + b) (L.map (pairOf a b))) (lwExpSim_R L) := by
  unfold labsOf
  rw [List.foldl_map]
  have gen : ∀ (L L0 : List (DEdge (Fin (a+1) ⊕ Fin b))) (labs : List ℕ), lwExpSim_LabsGood a b labs (lwExpSim_R L0) →
      lwExpSim_LabsGood a b (L.foldl (fun l e => unite l (pairOf a b e).1 (pairOf a b e).2) labs)
        (lwExpSim_R (L0 ++ L)) := by
    intro L
    induction L with
    | nil => intro L0 labs h; simpa using h
    | cons e L ih =>
      intro L0 labs h
      have h1 := lwExpSim_good_unite h e.x e.y (r' := lwExpSim_R (L0 ++ [e])) (by
        intro u v
        constructor
        · rintro ⟨e', he', hh⟩
          rcases List.mem_append.1 he' with he' | he'
          · exact Or.inl ⟨e', he', hh⟩
          · rw [List.mem_singleton] at he'; subst he'; exact Or.inr hh
        · rintro (⟨e', he', hh⟩ | hh)
          · exact ⟨e', List.mem_append_left _ he', hh⟩
          · exact ⟨e, List.mem_append_right _ (List.mem_singleton_self _), hh⟩)
      have := ih (L0 ++ [e]) _ h1
      simpa [List.append_assoc, pairOf] using this
  simpa using gen L [] _ lwExpSim_good_base

/-- The label list of a model graph: the class labels of its `=`-dotted edges (as in `cMerge`). -/
def lwExpSim_labs (Δ : LGraph (Fin (a+1)) (Fin b)) : List ℕ :=
  labsOf (a + 1 + b) ((Δ.dotted.filter fun e => e.eq).map (pairOf a b))

theorem lwExpSim_labs_good (Δ : LGraph (Fin (a+1)) (Fin b)) :
    (lwExpSim_labs Δ).length = a + 1 + b ∧ (∀ i < a + 1 + b, (lwExpSim_labs Δ).getD i 0 ≤ i) ∧
    (∀ i < a + 1 + b, (lwExpSim_labs Δ).getD ((lwExpSim_labs Δ).getD i 0) 0 = (lwExpSim_labs Δ).getD i 0) ∧
    ∀ u v, (lwExpSim_labs Δ).getD (vi a b u) 0 = (lwExpSim_labs Δ).getD (vi a b v) 0 ↔ Δ.cls u = Δ.cls v := by
  obtain ⟨h1, h2, h3, h4⟩ := lwExpSim_labsOf_good (Δ.dotted.filter fun e => e.eq)
  refine ⟨h1, h2, h3, fun u v => ?_⟩
  rw [show Δ.cls u = Δ.cls v ↔ Relation.EqvGen Δ.EqRel u v from Quotient.eq]
  have hR : Δ.EqRel = lwExpSim_R (Δ.dotted.filter fun e => e.eq) := by
    funext u v
    apply propext
    simp only [LGraph.EqRel, lwExpSim_R, List.mem_filter, and_assoc]
  rw [hR]
  exact h4 u v

/-! ### The class numbers (rank of a class among the classes) -/

/-- A label list entry is its own label (a class representative). -/
private abbrev lwExpSim_P (labs : List ℕ) (i : ℕ) : Prop := labs.getD i 0 = i

private theorem lwExpSim_filter_lt (Q : ℕ → Bool) {k n : ℕ} (h : k ≤ n) :
    ((List.range n).filter Q).filter (fun i => decide (i < k)) = (List.range k).filter Q := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst this
    simp
  | succ n ih =>
    by_cases hk : k ≤ n
    · rw [List.range_succ, List.filter_append, List.filter_append, ← ih hk]
      have : (List.filter Q [n]).filter (fun i => decide (i < k)) = [] := by
        cases hq : Q n
        · simp [hq]
        · simp [hq]
          omega
      rw [this, List.append_nil]
    · have hk' : k = n + 1 := by omega
      subst hk'
      apply List.filter_eq_self.2
      intro x hx
      have := List.mem_range.1 (List.mem_filter.1 hx).1
      simpa using this

private theorem lwExpSim_repsOf_eq (labs : List ℕ) :
    repsOf labs = (List.range labs.length).filter (fun i => decide (lwExpSim_P labs i)) := by
  rfl

private theorem lwExpSim_posOf_eq (labs : List ℕ) (v : ℕ) :
    posOf labs v = Nat.count (lwExpSim_P labs) (labs.getD v 0) := by
  unfold posOf Nat.count
  rw [List.countP_eq_length_filter]
  rfl

private theorem lwExpSim_reps_length (labs : List ℕ) :
    (repsOf labs).length = Nat.count (lwExpSim_P labs) labs.length := by
  rw [lwExpSim_repsOf_eq, Nat.count, List.countP_eq_length_filter]

private theorem lwExpSim_A_eq (labs : List ℕ) {k : ℕ} (hk : k ≤ labs.length) :
    ((repsOf labs).filter (fun i => decide (i < k))).length = Nat.count (lwExpSim_P labs) k := by
  rw [lwExpSim_repsOf_eq, Nat.count, List.countP_eq_length_filter, lwExpSim_filter_lt _ hk]

private theorem lwExpSim_exists_count (P : ℕ → Prop) [DecidablePred P] :
    ∀ (n p : ℕ), p < Nat.count P n → ∃ r < n, P r ∧ Nat.count P r = p := by
  intro n
  induction n with
  | zero => intro p h; simp at h
  | succ n ih =>
    intro p h
    rw [Nat.count_succ] at h
    by_cases hn : P n
    · simp only [hn, ↓reduceIte] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · obtain ⟨r, hr, hPr, hc⟩ := ih p h
        exact ⟨r, hr.trans (Nat.lt_succ_self n), hPr, hc⟩
      · exact ⟨n, Nat.lt_succ_self n, hn, h.symm⟩
    · simp only [hn, ↓reduceIte] at h
      obtain ⟨r, hr, hPr, hc⟩ := ih p (by omega)
      exact ⟨r, hr.trans (Nat.lt_succ_self n), hPr, hc⟩

private theorem lwExpSim_mkV_lt {A B p : ℕ} (hA : 1 ≤ A) (hp : p < A) :
    mkV (A - 1) B p = Sum.inl ⟨p, by omega⟩ := by
  unfold mkV
  simp only [show p < A - 1 + 1 by omega, ↓reduceDIte]

private theorem lwExpSim_mkV_ge {A B p : ℕ} (hA : 1 ≤ A) (hp : A ≤ p) (hpB : p < A + B) :
    mkV (A - 1) B p = Sum.inr ⟨p - A, by omega⟩ := by
  unfold mkV
  simp only [show ¬ p < A - 1 + 1 by omega, ↓reduceDIte, show 0 < B by omega]
  have : (p - (A - 1 + 1)) % B = p - A := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [this]

/-! ### The model merge: `cMerge` is the labelling `φ` whose fibres are the classes -/

private def lwExpSim_A (Δ : LGraph (Fin (a+1)) (Fin b)) : ℕ :=
  ((repsOf (lwExpSim_labs Δ)).filter (fun x => decide (x < a + 1))).length

private def lwExpSim_B (Δ : LGraph (Fin (a+1)) (Fin b)) : ℕ :=
  (repsOf (lwExpSim_labs Δ)).length - lwExpSim_A Δ

private def lwExpSim_phi (Δ : LGraph (Fin (a+1)) (Fin b)) :
    Fin (a+1) ⊕ Fin b → Fin (lwExpSim_A Δ - 1 + 1) ⊕ Fin (lwExpSim_B Δ) :=
  fun v => mkV (lwExpSim_A Δ - 1) (lwExpSim_B Δ) (posOf (lwExpSim_labs Δ) (vi a b v))

theorem lwExpSim_test_iff (Δ : LGraph (Fin (a+1)) (Fin b)) :
    ((Δ.dotted.filter fun e => !e.eq).any fun e =>
        (lwExpSim_labs Δ).getD (vi a b e.x) 0 == (lwExpSim_labs Δ).getD (vi a b e.y) 0) = true ↔
      ¬ Δ.Consistent := by
  obtain ⟨-, -, -, hiff⟩ := lwExpSim_labs_good Δ
  unfold LGraph.Consistent
  rw [List.any_eq_true]
  push Not
  constructor
  · rintro ⟨e, he, h⟩
    rw [List.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    refine ⟨e, he1, by simpa using he2, ?_⟩
    exact (hiff e.x e.y).1 (by simpa using h)
  · rintro ⟨e, he, he2, hc⟩
    refine ⟨e, List.mem_filter.2 ⟨he, by simpa using he2⟩, ?_⟩
    simpa using (hiff e.x e.y).2 hc

private theorem lwExpSim_phi_spec (Δ : LGraph (Fin (a+1)) (Fin b)) :
    (∀ u v, lwExpSim_phi Δ u = lwExpSim_phi Δ v ↔ Δ.cls u = Δ.cls v) ∧
    Function.Surjective (lwExpSim_phi Δ) ∧
    ∀ v, (∃ j, lwExpSim_phi Δ v = Sum.inl j) ↔ Δ.IsExtCls (Δ.cls v) := by
  obtain ⟨hlen, hle, hid, hiff⟩ := lwExpSim_labs_good Δ
  set labs := lwExpSim_labs Δ with hlabs
  have hA : lwExpSim_A Δ = Nat.count (lwExpSim_P labs) (a + 1) := by
    unfold lwExpSim_A
    exact lwExpSim_A_eq labs (by omega)
  have hR : (repsOf labs).length = Nat.count (lwExpSim_P labs) (a + 1 + b) := by
    rw [lwExpSim_reps_length, hlen]
  have hP : ∀ v, lwExpSim_P labs (labs.getD (vi a b v) 0) := fun v => hid _ (lwExpSim_vi_lt v)
  have hlt : ∀ v, labs.getD (vi a b v) 0 < a + 1 + b := fun v =>
    lt_of_le_of_lt (hle _ (lwExpSim_vi_lt v)) (lwExpSim_vi_lt v)
  have hpos : ∀ v, posOf labs (vi a b v) = Nat.count (lwExpSim_P labs) (labs.getD (vi a b v) 0) := fun v =>
    lwExpSim_posOf_eq labs _
  have hposlt : ∀ v, posOf labs (vi a b v) < (repsOf labs).length := by
    intro v
    rw [hpos, hR]
    exact Nat.count_strict_mono (hP v) (hlt v)
  have hA1 : 1 ≤ lwExpSim_A Δ := by
    rw [hA]
    have h0 : lwExpSim_P labs 0 := by
      have := hle 0 (by omega)
      change labs.getD 0 0 = 0
      omega
    have := Nat.count_strict_mono (p := lwExpSim_P labs) h0 (show 0 < a + 1 by omega)
    rw [Nat.count_zero] at this
    omega
  have hAR : lwExpSim_A Δ ≤ (repsOf labs).length := by
    rw [hA, hR]
    exact Nat.count_monotone _ (by omega)
  have hBdef : lwExpSim_B Δ = (repsOf labs).length - lwExpSim_A Δ := rfl
  -- the class of a vertex is external iff its label is a vertex of `Fin (a+1)`
  have hext : ∀ v, Δ.IsExtCls (Δ.cls v) ↔ labs.getD (vi a b v) 0 < a + 1 := by
    intro v
    constructor
    · rintro ⟨w, hw⟩
      have h1 : labs.getD (vi a b (Sum.inl w)) 0 = labs.getD (vi a b v) 0 := (hiff _ _).2 hw
      have h2 := hle (vi a b (Sum.inl w)) (lwExpSim_vi_lt _)
      rw [lwExpSim_vi_inl] at h1 h2
      have := w.isLt
      omega
    · intro h
      refine ⟨⟨labs.getD (vi a b v) 0, h⟩, ?_⟩
      apply (hiff _ _).1
      rw [lwExpSim_vi_inl]
      exact hP v
  -- external iff the class number is below `A`
  have hlow : ∀ v, posOf labs (vi a b v) < lwExpSim_A Δ ↔ labs.getD (vi a b v) 0 < a + 1 := by
    intro v
    rw [hpos, hA]
    constructor
    · intro h
      by_contra hn
      have := Nat.count_monotone (lwExpSim_P labs) (show a + 1 ≤ labs.getD (vi a b v) 0 by omega)
      omega
    · intro h
      exact Nat.count_strict_mono (hP v) h
  have hphiL : ∀ v (hv : posOf labs (vi a b v) < lwExpSim_A Δ),
      lwExpSim_phi Δ v = Sum.inl ⟨posOf labs (vi a b v), by omega⟩ := by
    intro v hv
    exact lwExpSim_mkV_lt hA1 hv
  have hphiR : ∀ v (hv : lwExpSim_A Δ ≤ posOf labs (vi a b v)),
      lwExpSim_phi Δ v = Sum.inr ⟨posOf labs (vi a b v) - lwExpSim_A Δ, by have := hposlt v; omega⟩ := by
    intro v hv
    exact lwExpSim_mkV_ge hA1 hv (by have := hposlt v; omega)
  refine ⟨fun u v => ?_, ?_, fun v => ?_⟩
  · rw [← hiff u v]
    constructor
    · intro h
      have hp : posOf labs (vi a b u) = posOf labs (vi a b v) := by
        by_cases hu : posOf labs (vi a b u) < lwExpSim_A Δ <;> by_cases hv : posOf labs (vi a b v) < lwExpSim_A Δ
        · rw [hphiL u hu, hphiL v hv] at h
          exact congrArg Fin.val (Sum.inl.inj h)
        · rw [hphiL u hu, hphiR v (by omega)] at h
          exact absurd h (by simp)
        · rw [hphiR u (by omega), hphiL v hv] at h
          exact absurd h (by simp)
        · rw [hphiR u (by omega), hphiR v (by omega)] at h
          have := congrArg Fin.val (Sum.inr.inj h)
          simp only at this
          omega
      rw [hpos, hpos] at hp
      exact Nat.count_injective (hP u) (hP v) hp
    · intro h
      have hp : posOf labs (vi a b u) = posOf labs (vi a b v) := by rw [hpos, hpos, h]
      exact congrArg (mkV (lwExpSim_A Δ - 1) (lwExpSim_B Δ)) hp
  · rintro (j | j)
    · have hj : (j : ℕ) < lwExpSim_A Δ := by have := j.isLt; omega
      obtain ⟨r, hr, hPr, hc⟩ := lwExpSim_exists_count (lwExpSim_P labs) (a + 1) j (by rw [← hA]; exact hj)
      refine ⟨Sum.inl ⟨r, hr⟩, ?_⟩
      have hp : posOf labs (vi a b (Sum.inl ⟨r, hr⟩)) = j := by
        rw [hpos, lwExpSim_vi_inl]
        rw [show labs.getD r 0 = r from hPr, hc]
      rw [hphiL _ (by rw [hp]; exact hj)]
      congr 1
      exact Fin.ext hp
    · have hj : lwExpSim_A Δ + (j : ℕ) < (repsOf labs).length := by
        have hjB : (j : ℕ) < (repsOf labs).length - lwExpSim_A Δ := j.isLt
        omega
      obtain ⟨r, hr, hPr, hc⟩ := lwExpSim_exists_count (lwExpSim_P labs) (a + 1 + b)
        (lwExpSim_A Δ + j) (by rw [← hR]; exact hj)
      have hra : a + 1 ≤ r := by
        by_contra hn
        have := Nat.count_strict_mono (p := lwExpSim_P labs) hPr (show r < a + 1 by omega)
        rw [← hA] at this
        omega
      refine ⟨Sum.inr ⟨r - (a + 1), by omega⟩, ?_⟩
      have hp : posOf labs (vi a b (Sum.inr ⟨r - (a + 1), by omega⟩ : Fin (a+1) ⊕ Fin b)) = lwExpSim_A Δ + j := by
        rw [hpos, lwExpSim_vi_inr]
        rw [show a + 1 + (r - (a + 1)) = r by omega, show labs.getD r 0 = r from hPr, hc]
      rw [hphiR _ (by rw [hp]; omega)]
      congr 1
      apply Fin.ext
      simp only
      omega
  · rw [hext v, ← hlow v]
    constructor
    · rintro ⟨j, hj⟩
      by_contra hn
      rw [hphiR v (by omega)] at hj
      exact absurd hj (by simp)
    · intro h
      exact ⟨_, hphiL v h⟩

theorem lwExpSim_cMerge_none (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1))
    (hC : ¬ Δ.Consistent) : cMerge Δ ext = none := by
  have hc := (lwExpSim_test_iff Δ).2 hC
  unfold cMerge
  simp only []
  have hc' : ((Δ.dotted.filter fun e => !e.eq).any fun e =>
      (labsOf (a + 1 + b) ((Δ.dotted.filter fun e => e.eq).map (pairOf a b))).getD (vi a b e.x) 0 ==
        (labsOf (a + 1 + b) ((Δ.dotted.filter fun e => e.eq).map (pairOf a b))).getD (vi a b e.y) 0) = true := hc
  simp only [hc', ↓reduceIte]

theorem lwExpSim_cMerge_some (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1))
    (hC : Δ.Consistent) :
    ∃ N', cMerge Δ ext = some N' ∧ ∃ ψ : Fin (a+1) ⊕ Fin b → Fin (N'.a + 1) ⊕ Fin N'.b,
      (∀ u v, ψ u = ψ v ↔ Δ.cls u = Δ.cls v) ∧ Function.Surjective ψ ∧
      (∀ v, (∃ j, ψ v = Sum.inl j) ↔ Δ.IsExtCls (Δ.cls v)) ∧
      N'.g.solid = Δ.solid.map (SEdge.map ψ) ∧ N'.g.waved = Δ.waved.map (WEdge.map ψ) ∧
      N'.g.dotted = (Δ.dotted.filter fun e => !e.eq).map (DEdge.map ψ) ∧ N'.g.coeff = Δ.coeff ∧
      ∀ i, ψ (Sum.inl (ext i)) = Sum.inl (N'.ext i) := by
  have hc : ¬ ((Δ.dotted.filter fun e => !e.eq).any fun e =>
      (lwExpSim_labs Δ).getD (vi a b e.x) 0 == (lwExpSim_labs Δ).getD (vi a b e.y) 0) = true :=
    fun h => (lwExpSim_test_iff Δ).1 h hC
  obtain ⟨hP1, hP2, hP3⟩ := lwExpSim_phi_spec Δ
  unfold cMerge
  simp only []
  have hc' : ¬ ((Δ.dotted.filter fun e => !e.eq).any fun e =>
      (labsOf (a + 1 + b) ((Δ.dotted.filter fun e => e.eq).map (pairOf a b))).getD (vi a b e.x) 0 ==
        (labsOf (a + 1 + b) ((Δ.dotted.filter fun e => e.eq).map (pairOf a b))).getD (vi a b e.y) 0) = true := hc
  simp only [hc', Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, rfl, lwExpSim_phi Δ, hP1, hP2, hP3, rfl, rfl, rfl, rfl, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := (hP3 (Sum.inl (ext i))).2 ⟨ext i, rfl⟩
  dsimp only
  split
  · rename_i j' hj'
    exact hj'
  · rename_i j' hj'
    exact absurd (hj.symm.trans hj') (by simp)

end Labs

/-! ## 3. A labelling with the classes as fibres gives the equivalences of `Rel` -/

/-- A labelling `ψ` of the vertices with fibres the classes, onto `Fin A ⊕ Fin B`, sending exactly the external classes to
the left, gives equivalences `Fin A ≃ ExtCls`, `Fin B ≃ IntCls` through which the merge map `vmap` factors. -/
theorem lwExpSim_equivs {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Δ : LGraph E I) {A B : ℕ} (ψ : E ⊕ I → Fin A ⊕ Fin B)
    (h1 : ∀ u v, ψ u = ψ v ↔ Δ.cls u = Δ.cls v) (h2 : Function.Surjective ψ)
    (h3 : ∀ v, (∃ j, ψ v = Sum.inl j) ↔ Δ.IsExtCls (Δ.cls v)) :
    ∃ (eE : Fin A ≃ Δ.ExtCls) (eI : Fin B ≃ Δ.IntCls), ∀ v, Δ.vmap v = Sum.map eE eI (ψ v) := by
  let ρ : Δ.Cls → Fin A ⊕ Fin B := Quotient.lift ψ (fun u v h => (h1 u v).2 (Quotient.sound h))
  have hinj : Function.Injective ρ := by
    intro p q hpq
    obtain ⟨u, rfl⟩ := Quotient.exists_rep p
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact (h1 u v).1 hpq
  have hsurj : Function.Surjective ρ := fun s => by
    obtain ⟨v, rfl⟩ := h2 s
    exact ⟨Δ.cls v, rfl⟩
  let ρe : Δ.Cls ≃ Fin A ⊕ Fin B := Equiv.ofBijective ρ ⟨hinj, hsurj⟩
  have hsymm : ∀ v, ρe.symm (ψ v) = Δ.cls v := fun v => ρe.symm_apply_apply (Δ.cls v)
  have hE : ∀ j, Δ.IsExtCls (ρe.symm (Sum.inl j)) := by
    intro j
    obtain ⟨v, hv⟩ := h2 (Sum.inl j)
    rw [← hv, hsymm]
    exact (h3 v).1 ⟨j, hv⟩
  have hI : ∀ j, ¬ Δ.IsExtCls (ρe.symm (Sum.inr j)) := by
    intro j
    obtain ⟨v, hv⟩ := h2 (Sum.inr j)
    rw [← hv, hsymm, ← h3 v]
    rintro ⟨j', hj'⟩
    rw [hv] at hj'
    exact absurd hj' (by simp)
  let eE : Fin A ≃ Δ.ExtCls := Equiv.ofBijective (fun j => ⟨ρe.symm (Sum.inl j), hE j⟩) (by
    constructor
    · intro j j' h
      exact Sum.inl.inj (ρe.symm.injective (congrArg Subtype.val h))
    · rintro ⟨q, hq⟩
      obtain ⟨u, rfl⟩ := Quotient.exists_rep q
      obtain ⟨j, hj⟩ := (h3 u).2 hq
      exact ⟨j, Subtype.ext (by simp only [← hsymm u, hj])⟩)
  let eI : Fin B ≃ Δ.IntCls := Equiv.ofBijective (fun j => ⟨ρe.symm (Sum.inr j), hI j⟩) (by
    constructor
    · intro j j' h
      exact Sum.inr.inj (ρe.symm.injective (congrArg Subtype.val h))
    · rintro ⟨q, hq⟩
      obtain ⟨u, rfl⟩ := Quotient.exists_rep q
      have hu : ¬ ∃ j, ψ u = Sum.inl j := fun h => hq ((h3 u).1 h)
      obtain ⟨j, hj⟩ : ∃ j, ψ u = Sum.inr j := by
        rcases hψ : ψ u with j | j
        · exact absurd ⟨j, hψ⟩ hu
        · exact ⟨j, rfl⟩
      exact ⟨j, Subtype.ext (by simp only [← hsymm u, hj])⟩)
  refine ⟨eE, eI, fun v => ?_⟩
  rcases hψ : ψ v with j | j
  · have hex : Δ.IsExtCls (Δ.cls v) := (h3 v).1 ⟨j, hψ⟩
    simp only [LGraph.vmap, LGraph.vmapC, hex, ↓reduceDIte, Sum.map_inl]
    have hv : (eE j).1 = Δ.cls v := by
      change ρe.symm (Sum.inl j) = Δ.cls v
      rw [← hψ]
      exact hsymm v
    exact congrArg Sum.inl (Subtype.ext hv.symm)
  · have hex : ¬ Δ.IsExtCls (Δ.cls v) := fun h => by
      obtain ⟨j', hj'⟩ := (h3 v).2 h
      rw [hψ] at hj'
      exact absurd hj' (by simp)
    simp only [LGraph.vmap, LGraph.vmapC, hex, ↓reduceDIte, Sum.map_inr]
    have hv : (eI j).1 = Δ.cls v := by
      change ρe.symm (Sum.inr j) = Δ.cls v
      rw [← hψ]
      exact hsymm v
    exact congrArg Sum.inr (Subtype.ext hv.symm)


/-! ## 4. Classes under a relabelling by an equivalence -/

section Relabel

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

private theorem lwExpSim_eqvGen_equiv {α β : Type*} (f : α ≃ β) (r : α → α → Prop) (s : β → β → Prop)
    (h : ∀ a b, s (f a) (f b) ↔ r a b) (a b : α) :
    Relation.EqvGen s (f a) (f b) ↔ Relation.EqvGen r a b := by
  constructor
  · intro H
    have key : ∀ x y, Relation.EqvGen s x y → Relation.EqvGen r (f.symm x) (f.symm y) := by
      intro x y hxy
      induction hxy with
      | rel x y hxy => exact Relation.EqvGen.rel _ _ ((h _ _).1 (by simpa using hxy))
      | refl x => exact Relation.EqvGen.refl _
      | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    simpa using key _ _ H
  · intro H
    induction H with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ ((h _ _).2 hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private theorem lwExpSim_eqRel_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') (u v : E ⊕ I) :
    (Γ.relabel τ).EqRel (τ u) (τ v) ↔ Γ.EqRel u v := by
  simp only [LGraph.EqRel, LGraph.relabel, List.mem_map]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hq, hh⟩
    refine ⟨e, he, hq, ?_⟩
    simpa [DEdge.map, τ.injective.eq_iff] using hh
  · rintro ⟨e, he, hq, hh⟩
    exact ⟨DEdge.map τ e, ⟨e, he, rfl⟩, hq, by simpa [DEdge.map] using hh⟩

/-- Classes are transported by an equivalence of the vertex sets. -/
theorem lwExpSim_cls_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') (u v : E ⊕ I) :
    (Γ.relabel τ).cls (τ u) = (Γ.relabel τ).cls (τ v) ↔ Γ.cls u = Γ.cls v := by
  rw [show (Γ.relabel τ).cls (τ u) = (Γ.relabel τ).cls (τ v) ↔
      Relation.EqvGen (Γ.relabel τ).EqRel (τ u) (τ v) from Quotient.eq,
    show Γ.cls u = Γ.cls v ↔ Relation.EqvGen Γ.EqRel u v from Quotient.eq]
  exact lwExpSim_eqvGen_equiv τ _ _ (fun a b => lwExpSim_eqRel_relabel Γ τ a b) u v

theorem lwExpSim_consistent_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') :
    (Γ.relabel τ).Consistent ↔ Γ.Consistent := by
  unfold LGraph.Consistent
  simp only [LGraph.relabel, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun e he => imp_congr_right fun _ => ?_
  exact not_congr (lwExpSim_cls_relabel Γ τ e.x e.y)

end Relabel

/-! ## 5. One dotted term: the model merge against the real merge -/

section Term

theorem lwExpSim_splitLoopsX_map {V W : Type*} [DecidableEq V] [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) (es : List (SEdge V)) :
    lwSplitLoopsX (es.map (SEdge.map f)) = (lwSplitLoopsX es).map (fun r => (r.1, r.2.map (SEdge.map f))) := by
  induction es with
  | nil => simp [lwSplitLoopsX]
  | cons e es ih =>
    simp only [List.map_cons, lwSplitLoopsX, ih, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun r _ => ?_
    by_cases h : e.src = e.dst ∧ e.circ = false
    · have h' : (SEdge.map f e).src = (SEdge.map f e).dst ∧ (SEdge.map f e).circ = false := by
        simpa [SEdge.map, hf.eq_iff] using h
      simp only [h, h', and_self, ↓reduceIte]
      cases hσ : e.σ <;> simp [SEdge.map, hσ]
    · have h' : ¬ ((SEdge.map f e).src = (SEdge.map f e).dst ∧ (SEdge.map f e).circ = false) := by
        simpa [SEdge.map, hf.eq_iff] using h
      simp only [h, h', ↓reduceIte]
      simp [SEdge.map]

theorem lwExpSim_vmap_inl {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Δ : LGraph E I) (a : E) : Δ.vmap (Sum.inl a) = Sum.inl (Δ.extMap a) := by
  have hex : Δ.IsExtCls (Δ.cls (Sum.inl a)) := ⟨a, rfl⟩
  simp only [LGraph.vmap, LGraph.vmapC, hex, ↓reduceDIte]
  rfl


/-- The real terms of the partition of one dotted term `Δ`: its merge with the weights split (as in `partitionX`). -/
def lwExpSim_real {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Δ : LGraph E I) : List ((ℕ × ℕ) × PGraph E) :=
  (lwSplitLoopsX Δ.merge.solid).map fun r =>
    (r.1, { E' := Δ.ExtCls, I' := Δ.IntCls, ext := Δ.extMap, ext_surj := Δ.extMap_surj,
            g := { Δ.merge with solid := r.2 } })

/-- The model terms of the partition of one merged term `N'` (as in `cPartitionX`). -/
def lwExpSim_model (N' : MNode) : List ((ℕ × ℕ) × MNode) :=
  (lwSplitLoopsX N'.g.solid).map fun r => (r.1, { N' with g := { N'.g with solid := r.2 } })

/-- The relation of the lists of terms: exponents, `Rel` (the real term read through `N.ext`), coefficients. -/
def lwExpSim_R0 (N : MNode) (h : Function.Surjective N.ext) (r : (ℕ × ℕ) × MNode)
    (q : (ℕ × ℕ) × PGraph (Fin (N.a + 1))) : Prop :=
  Rel r.2 (pcomp (N.toP h) q.2) ∧ r.1 = q.1 ∧ q.2.g.coeff = r.2.g.coeff

private theorem lwExpSim_term_some {N : MNode} (h : Function.Surjective N.ext) {b' : ℕ} {I : Type}
    [Fintype I] [DecidableEq I] (τ : Fin (N.a + 1) ⊕ I ≃ Fin (N.a + 1) ⊕ Fin b')
    (hτ : ∀ a, τ (Sum.inl a) = Sum.inl a) (Δ : LGraph (Fin (N.a + 1)) I) (hC : Δ.Consistent) :
    ∃ N', cMerge (Δ.relabel τ) N.ext = some N' ∧
      List.Forall₂ (lwExpSim_R0 N h) (lwExpSim_model N') (lwExpSim_real Δ) := by
  obtain ⟨N', hN', ψ, hP1, hP2, hP3, hsol, hwav, hdot, hcoe, hext⟩ :=
    lwExpSim_cMerge_some (Δ.relabel τ) N.ext ((lwExpSim_consistent_relabel Δ τ).2 hC)
  obtain ⟨eE, eI, hvm⟩ := lwExpSim_equivs Δ (fun v => ψ (τ v))
    (fun u v => by rw [hP1, lwExpSim_cls_relabel])
    (hP2.comp τ.surjective)
    (fun v => by
      rw [hP3 (τ v)]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, by rw [← lwExpSim_cls_relabel Δ τ, hτ]; exact ha⟩
      · rintro ⟨a, ha⟩
        refine ⟨a, ?_⟩
        have := (lwExpSim_cls_relabel Δ τ (Sum.inl a) v).2 ha
        rwa [hτ] at this)
  refine ⟨N', hN', ?_⟩
  have hψ' : Function.Injective (Sum.map eE eI) := (Equiv.sumCongr eE eI).injective
  have hs : Δ.merge.solid = N'.g.solid.map (SEdge.map (Sum.map eE eI)) := by
    rw [hsol]
    simp only [LGraph.merge, LGraph.relabel, List.map_map]
    exact List.map_congr_left fun e _ => by simp [SEdge.map, hvm]
  have hw : Δ.merge.waved = N'.g.waved.map (WEdge.map (Sum.map eE eI)) := by
    rw [hwav]
    simp only [LGraph.merge, LGraph.relabel, List.map_map]
    exact List.map_congr_left fun e _ => by simp [WEdge.map, hvm]
  have hd : Δ.merge.dotted = N'.g.dotted.map (DEdge.map (Sum.map eE eI)) := by
    rw [hdot]
    simp only [LGraph.merge, LGraph.relabel, List.map_map, List.filter_map]
    refine List.map_congr_left fun e _ => ?_
    simp [DEdge.map, hvm]
  unfold lwExpSim_model lwExpSim_real
  rw [hs, lwExpSim_splitLoopsX_map _ hψ', List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  intro r _
  refine ⟨⟨eE, eI, fun i => ?_, rfl, ?_, ?_⟩, rfl, ?_⟩
  · have h1 := hvm (Sum.inl (N.ext i))
    rw [lwExpSim_vmap_inl] at h1
    simp only [hτ, hext, Sum.map_inl] at h1
    exact Sum.inl.inj h1
  · change List.map (fun e => (e.x, e.y)) Δ.merge.waved =
      List.map (fun e => (Sum.map eE eI e.x, Sum.map eE eI e.y)) N'.g.waved
    rw [hw, List.map_map]
    rfl
  · exact hd
  · change Δ.merge.coeff = N'.g.coeff
    rw [hcoe]
    rfl

end Term

/-! ## 6. The dotted choices under a relabelling by an equivalence -/

section Choices

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

theorem lwExpSim_sBetween_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') (u v : E ⊕ I) :
    (Γ.relabel τ).SBetween (τ u) (τ v) ↔ Γ.SBetween u v := by
  simp only [LGraph.SBetween, LGraph.relabel, List.mem_map]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hne, hh⟩
    refine ⟨e, he, fun h => hne (by simp [SEdge.map, h]), ?_⟩
    simpa [SEdge.map, τ.injective.eq_iff] using hh
  · rintro ⟨e, he, hne, hh⟩
    refine ⟨SEdge.map τ e, ⟨e, he, rfl⟩, ?_, by simpa [SEdge.map] using hh⟩
    simpa [SEdge.map, τ.injective.eq_iff] using hne

theorem lwExpSim_xBetween_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') (u v : E ⊕ I) :
    (Γ.relabel τ).XBetween (τ u) (τ v) ↔ Γ.XBetween u v := by
  simp only [LGraph.XBetween, LGraph.relabel, List.mem_map]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hq, hh⟩
    refine ⟨e, he, hq, ?_⟩
    simpa [DEdge.map, τ.injective.eq_iff] using hh
  · rintro ⟨e, he, hq, hh⟩
    exact ⟨DEdge.map τ e, ⟨e, he, rfl⟩, hq, by simpa [DEdge.map] using hh⟩

private theorem lwExpSim_dedup_map {V W : Type*} [DecidableEq V] [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) (l : List (V × V)) :
    lwDedupPairs (l.map (Prod.map f f)) = (lwDedupPairs l).map (Prod.map f f) := by
  induction l with
  | nil => simp [lwDedupPairs]
  | cons p l ih =>
    have hq : (lwSamePair (Prod.map f f p) ∘ Prod.map f f) = lwSamePair p := by
      funext q
      simp [lwSamePair, hf.eq_iff]
    simp only [List.map_cons, lwDedupPairs, ih, List.any_map, hq]
    split_ifs <;> simp

private theorem lwExpSim_relabel_solid (Γ : LGraph E I) (τ : E ⊕ I → E' ⊕ I') :
    (Γ.relabel τ).solid = Γ.solid.map (SEdge.map τ) := rfl

private theorem lwExpSim_relabel_dotted (Γ : LGraph E I) (τ : E ⊕ I → E' ⊕ I') :
    (Γ.relabel τ).dotted = Γ.dotted.map (DEdge.map τ) := rfl

private theorem lwExpSim_aPairs_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') :
    (Γ.relabel τ).aPairs = Γ.aPairs.map (Prod.map τ τ) := by
  unfold LGraph.aPairs
  rw [← lwExpSim_dedup_map τ τ.injective]
  congr 1
  rw [lwExpSim_relabel_solid, List.filter_map, List.map_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp [SEdge.map, τ.injective.eq_iff, lwExpSim_xBetween_relabel]

private theorem lwExpSim_isB_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') (e : DEdge (E ⊕ I)) :
    (Γ.relabel τ).isB (DEdge.map τ e) = Γ.isB e := by
  simp [LGraph.isB, DEdge.map, lwExpSim_sBetween_relabel]

private theorem lwExpSim_bEdges_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') :
    (Γ.relabel τ).bEdges = Γ.bEdges.map (DEdge.map τ) := by
  unfold LGraph.bEdges
  rw [lwExpSim_relabel_dotted, List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  exact lwExpSim_isB_relabel Γ τ e

theorem lwExpSim_dotBase_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') :
    (Γ.relabel τ).dotBase = Γ.dotBase.map (DEdge.map τ) := by
  unfold LGraph.dotBase
  rw [lwExpSim_relabel_dotted, List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp [lwExpSim_isB_relabel]

private theorem lwExpSim_combine_map {X Y : Type*} (f : X → Y) (atoms : List (List (ℤ × List X))) :
    lwCombineAtoms (atoms.map (List.map fun t => (t.1, t.2.map f))) =
      (lwCombineAtoms atoms).map fun t => (t.1, t.2.map f) := by
  induction atoms with
  | nil => simp [lwCombineAtoms]
  | cons a rest ih =>
    simp only [List.map_cons, lwCombineAtoms, ih, List.flatMap_map, List.map_flatMap, List.map_map]
    refine List.flatMap_congr fun o _ => ?_
    simp [Function.comp_def]

private theorem lwExpSim_dotAtoms_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') :
    (Γ.relabel τ).dotAtoms = Γ.dotAtoms.map (List.map fun t => (t.1, t.2.map (DEdge.map τ))) := by
  unfold LGraph.dotAtoms
  rw [lwExpSim_aPairs_relabel, lwExpSim_bEdges_relabel]
  simp [List.map_append, List.map_map, Function.comp_def, DEdge.map]

theorem lwExpSim_dotChoices_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') :
    (Γ.relabel τ).dotChoices = Γ.dotChoices.map fun t => (t.1, t.2.map (DEdge.map τ)) := by
  unfold LGraph.dotChoices
  rw [lwExpSim_dotAtoms_relabel, lwExpSim_combine_map]

private theorem lwExpSim_withDots_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I')
    (c : ℤ × List (DEdge (E ⊕ I))) :
    (Γ.relabel τ).withDots (c.1, c.2.map (DEdge.map τ)) = (Γ.withDots c).relabel τ := by
  unfold LGraph.withDots
  rw [lwExpSim_dotBase_relabel]
  simp only [LGraph.relabel, List.map_append]

/-- The dotted terms of the relabelled graph are the relabelled dotted terms. -/
theorem lwExpSim_terms_relabel (Γ : LGraph E I) (τ : E ⊕ I ≃ E' ⊕ I') :
    (Γ.relabel τ).dotChoices.map (Γ.relabel τ).withDots =
      (Γ.dotChoices.map Γ.withDots).map (fun Δ => Δ.relabel τ) := by
  rw [lwExpSim_dotChoices_relabel, List.map_map, List.map_map]
  exact List.map_congr_left fun c _ => lwExpSim_withDots_relabel Γ τ c

end Choices

/-! ## 7. The partition of a relabelled graph -/

theorem lwExpSim_forall₂_flatMap {α γ δ : Type*} (R : γ → δ → Prop) (l : List α) (p : α → Bool)
    (f : α → List γ) (g : α → List δ)
    (h : ∀ x ∈ l, (p x = true → List.Forall₂ R (f x) (g x)) ∧ (p x = false → f x = [])) :
    List.Forall₂ R (l.flatMap f) ((l.filter p).flatMap g) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x List.mem_cons_self
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.flatMap_cons, List.filter_cons]
    cases hp : p x
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      rw [hx.2 hp, List.nil_append]
      exact ih'
    · simp only [hp, ↓reduceIte]
      rw [List.flatMap_cons]
      exact List.rel_append (hx.1 hp) ih'

/-- **The partition of a relabelled model graph**: the model partition of `Γ.relabel τ` and the real exponent-tracking
partition `partitionX Γ` are related term by term (`τ` fixes the external vertices). -/
theorem lwExpSim_partition_sim (N : MNode) (h : Function.Surjective N.ext) {b' : ℕ} {I : Type}
    [Fintype I] [DecidableEq I] (τ : Fin (N.a + 1) ⊕ I ≃ Fin (N.a + 1) ⊕ Fin b')
    (hτ : ∀ a, τ (Sum.inl a) = Sum.inl a) (Γ : LGraph (Fin (N.a + 1)) I) :
    List.Forall₂ (lwExpSim_R0 N h) (cPartitionX (Γ.relabel τ) N.ext) (partitionX Γ) := by
  classical
  unfold cPartitionX partitionX LGraph.partitionTerms
  rw [lwExpSim_terms_relabel, List.flatMap_map]
  refine lwExpSim_forall₂_flatMap _ _ _ _ _ fun Δ _ => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨N', hN', hF⟩ := lwExpSim_term_some h τ hτ Δ (of_decide_eq_true hp)
    simp only [hN']
    exact hF
  · have hC : ¬ Δ.Consistent := of_decide_eq_false hp
    simp only [lwExpSim_cMerge_none _ _ (fun hc => hC ((lwExpSim_consistent_relabel Δ τ).1 hc))]

/-! ## 8. The two bridges -/

/-- A packed graph with its coefficient multiplied by `c` (as `T2307`'s private `lwExpTerm5_scaleP`). -/
private def lwExpSim_scaleP {E0 : Type} (c : ℂ) (P : PGraph E0) : PGraph E0 :=
  { P with g := { P.g with coeff := c * P.g.coeff } }

/-- The partition is the exponent-tracking partition with the coefficients `m^j m̄^{j'}` multiplied in. -/
private theorem lwExpSim_partition_eq {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (m : ℂ) (Γ : LGraph E I) :
    Γ.partition m = (partitionX Γ).map fun r => lwExpSim_scaleP (m ^ r.1.1 * star m ^ r.1.2) r.2 := by
  unfold LGraph.partition partitionX
  rw [List.map_flatMap]
  refine List.flatMap_congr fun Δ _ => ?_
  unfold LGraph.mergeSplitP LGraph.splitWeights
  rw [lwSplitLoopsX_spec m Δ.merge.solid]
  simp only [List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [lwExpSim_scaleP]

theorem lwExpSim_relabel_refl {E I : Type} (Γ : LGraph E I) :
    Γ.relabel ⇑(Equiv.sumCongr (Equiv.refl E) (Equiv.refl I)) = Γ := by
  have h1 : SEdge.map (id : E ⊕ I → E ⊕ I) = id := funext fun e => rfl
  have h2 : WEdge.map (id : E ⊕ I → E ⊕ I) = id := funext fun e => rfl
  have h3 : DEdge.map (id : E ⊕ I → E ⊕ I) = id := funext fun e => rfl
  cases Γ
  simp [LGraph.relabel, h1, h2, h3]

/-- **Bridge 1**: the model partition of a packed model node is the real partition, term by term. -/
theorem partitionSim : PartitionSim := by
  intro N h m
  have key := lwExpSim_partition_sim N h (Equiv.sumCongr (Equiv.refl _) (Equiv.refl (Fin N.b)))
    (fun a => rfl) N.g
  rw [lwExpSim_relabel_refl] at key
  have key2 : List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (q : (ℕ × ℕ) × PGraph (Fin (N.a + 1))) =>
      Rel r.2 (pcomp (N.toP h) (lwExpSim_scaleP (m ^ q.1.1 * star m ^ q.1.2) q.2)) ∧
        (pcomp (N.toP h) (lwExpSim_scaleP (m ^ q.1.1 * star m ^ q.1.2) q.2)).g.coeff =
          m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff)
      (cPartitionX N.g N.ext) (partitionX N.g) := by
    refine key.imp fun r q hq => ⟨hq.1, ?_⟩
    change m ^ q.1.1 * star m ^ q.1.2 * q.2.g.coeff = m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff
    rw [hq.2.2, ← hq.2.1]
  rw [lwExpSim_partition_eq]
  exact List.forall₂_map_right_iff.2 (List.forall₂_map_right_iff.2 key2)

/-! ## 9. The families -/

theorem lwExpSim_forall₂_flatMap_same {α γ δ : Type*} (R : γ → δ → Prop) (l : List α)
    (f : α → List γ) (g : α → List δ) (h : ∀ x ∈ l, List.Forall₂ R (f x) (g x)) :
    List.Forall₂ R (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- One family: the model partition of the renumbered graph against the real partition, with the shift `j` of `m`. -/
private theorem lwExpSim_block (N : MNode) (h : Function.Surjective N.ext) {b' : ℕ} {I : Type}
    [Fintype I] [DecidableEq I] (τ : Fin (N.a + 1) ⊕ I ≃ Fin (N.a + 1) ⊕ Fin b')
    (hτ : ∀ a, τ (Sum.inl a) = Sum.inl a) (Γ : LGraph (Fin (N.a + 1)) I) (j : ℕ) :
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
      ((cPartitionX (Γ.relabel τ) N.ext).map fun r => ((r.1.1 + j, r.1.2 + 0), r.2))
      ((partitionX Γ).map fun r => ((r.1.1 + j, r.1.2), pcomp (N.toP h) r.2)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine (lwExpSim_partition_sim N h τ hτ Γ).imp fun r q hq => ⟨hq.1, ?_⟩
  change (r.1.1 + j, r.1.2 + 0) = (q.1.1 + j, q.1.2)
  rw [← hq.2.1]
  rfl

/-- The same for a family that is not renumbered. -/
private theorem lwExpSim_block_id (N : MNode) (h : Function.Surjective N.ext) (Γ : LGraph (Fin (N.a + 1)) (Fin N.b))
    (j : ℕ) :
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
      ((cPartitionX Γ N.ext).map fun r => ((r.1.1 + j, r.1.2 + 0), r.2))
      ((partitionX Γ).map fun r => ((r.1.1 + j, r.1.2), pcomp (N.toP h) r.2)) := by
  have := lwExpSim_block N h (Equiv.sumCongr (Equiv.refl _) (Equiv.refl (Fin N.b))) (fun a => rfl) Γ j
  rwa [lwExpSim_relabel_refl] at this

/-- **Bridge 2**: the model children of a packed model node at a candidate are the real children, term by term. -/
theorem childrenSim : ChildrenSim := by
  intro N h c hc
  unfold childrenX famsX RCand.kids
  dsimp only [Cand.toR]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_assoc,
    List.append_assoc]
  have e1 := fun {k : ℕ} (Γ : LGraph (Fin (N.a + 1)) (Fin N.b ⊕ Fin k)) (j : ℕ) =>
    lwExpSim_block N h (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv) (fun a => rfl) Γ j
  exact List.rel_append (lwExpSim_block_id N h _ 3) (List.rel_append (e1 _ 1) (List.rel_append (e1 _ 3)
    (List.rel_append (e1 _ 1) (List.rel_append (e1 _ 3)
      (lwExpSim_forall₂_flatMap_same _ _ _ _ fun q' _ => List.rel_append (e1 _ 1) (e1 _ 3))))))


/-- **A model node is related to its own packed graph** (by the identity equivalences). -/
theorem rel_self (N : MNode) (h : Function.Surjective N.ext) : Rel N (N.toP h) := by
  have e := lwExpSim_relabel_refl N.g
  refine ⟨Equiv.refl _, Equiv.refl _, fun _ => rfl, (congrArg LGraph.solid e).symm, ?_,
    (congrArg LGraph.dotted e).symm⟩
  have hw : N.g.waved.map (WEdge.map (Sum.map (Equiv.refl (Fin (N.a + 1))) (Equiv.refl (Fin N.b)))) = N.g.waved :=
    congrArg LGraph.waved e
  change N.g.waved.map (fun e => (e.x, e.y)) = _
  conv_lhs => rw [← hw]
  rw [List.map_map]
  rfl

/-! ## 10. The compiled instances -/

/-- The root `𝒢_xy` of LW-14c (`k = s = false`) as a model node: external `x = 0`, `y = 1`, three internal vertices. -/
private def lwExpSim_rootN : MNode := ⟨1, 3, LWG5Graph false false, ![0, 1]⟩

private theorem lwExpSim_rootN_surj : Function.Surjective lwExpSim_rootN.ext := by decide

/-- **Instance of `partitionSim`** at the root graph `LWG5Graph false false` (`163` partition terms) and `m = 1/2 + i/3`
(`m ≠ m̄`): every hypothesis is discharged (`ext = ![0, 1]` is onto) and both lists are nonempty. -/
example : List.Forall₂
    (fun (r : (ℕ × ℕ) × MNode) (Q : PGraph (Fin 2)) =>
      Rel r.2 Q ∧ Q.g.coeff = (⟨1 / 2, 1 / 3⟩ : ℂ) ^ r.1.1 * star (⟨1 / 2, 1 / 3⟩ : ℂ) ^ r.1.2 * r.2.g.coeff)
    (cPartitionX lwExpSim_rootN.g lwExpSim_rootN.ext)
    ((lwExpSim_rootN.g.partition ⟨1 / 2, 1 / 3⟩).map (pcomp (lwExpSim_rootN.toP lwExpSim_rootN_surj))) :=
  partitionSim lwExpSim_rootN lwExpSim_rootN_surj ⟨1 / 2, 1 / 3⟩

example : (cPartitionX lwExpSim_rootN.g lwExpSim_rootN.ext).length = 163 := by decide +kernel

/-- **Instance of `rel_self`** at the root model node. -/
example : Rel lwExpSim_rootN (lwExpSim_rootN.toP lwExpSim_rootN_surj) := rel_self _ _

/-- The model node of the instance of `childrenSim`: the explicit normal graph `lwExpTerm3_instGraph` (external `x = 0`,
`y = 1`, internal `α`; five solid, two waved and three `×`-dotted edges). -/
private def lwExpSim_instN : MNode := ⟨1, 1, lwExpTerm3_instGraph, ![0, 1]⟩

private theorem lwExpSim_instN_surj : Function.Surjective lwExpSim_instN.ext := by decide

/-- Its candidate: `x = α`, `p = G_{αy}`, `q = G_{xα}`. -/
private def lwExpSim_instC : Cand lwExpSim_instN.a lwExpSim_instN.b := (cands lwExpSim_instN.g)[0]'(by decide)

/-- **Instance of `childrenSim`** at `lwExpTerm3_instGraph` and its candidate (all hypotheses discharged). -/
example : List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
    (childrenX lwExpSim_instN lwExpSim_instC)
    (Cand.toR lwExpSim_instN lwExpSim_instN_surj lwExpSim_instC (List.getElem_mem _)).kids :=
  childrenSim lwExpSim_instN lwExpSim_instN_surj lwExpSim_instC (List.getElem_mem _)

/-- Nondegeneracy of the instance: one candidate, eleven families, `550` children. -/
example : (cands lwExpSim_instN.g).length = 1 ∧ (famsX lwExpSim_instN.g lwExpSim_instC).length = 11 ∧
    (childrenX lwExpSim_instN lwExpSim_instC).length = 550 := by
  decide +kernel

end RBM.Gauss.Sizes

end
