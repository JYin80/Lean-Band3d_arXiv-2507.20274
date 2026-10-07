/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpTerm3
import RBM3D.Graph.LWVocab
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.ScalingOrder
import RBM3D.Defs.Semicircle
import RBM3D.Green.IBPPoly
import RBM3D.Induction.Defs

/-!
# LW-14e-2 (T2307): the expansion procedure of `𝒢_xy` and its identity in expectation

The identity half of LW-14e (`B:78-108`, `𝔼 𝒢_xy = Σ_μ 𝔼 Γ_μ`; `7_8:214-225` `dot-def`,
`7_8:334-349` `(Oe2x)`) on the real carrier `PGraph (Fin 2)`, with the exponent-tracking partition:
the procedure `expand` is generic over a selection rule `sel` and a fuel, and its list satisfies
the expectation identity for **every** rule and **every** fuel (`lwExpandIdentity_holds`).  The
leaf half (`ord ≥ tg`, molecules, `LWAttached`) is not here (LW-14e-1/3/4).

Contents (namespace `RBM.Gauss.Sizes`):
1. vocabulary `LWJoined`, `LWG5Cand`, `LWG5Progress`, `LWG5Identity`;
2. the procedure: `lwSplitLoopsX`, `partitionX`, `pcomp`, `RCand`, `RCand.kids`, `Sel`, `expand`,
   `expandRoot`, `selClassical`, `LWExpandIdentity` (texts of the probe
   `t/T2288:RBM3D/Probe/T2288Cert.lean` 55-71, 80-86, 113-207);
3. the abstract step: `expandG`, `ExpandGSum`, `expandG_sum` (induction on the fuel for any
   carrier), `lwStep`, `expand_eq_expandG`;
4. proved lemmas: `lwSplitLoopsX_spec`, `partitionX_spec`, `val_eq_partitionX`,
   `partitionX_normal`, `oe2xR1_val_zero`, `RCand.kids_normal`, `RCand.kids_identity`;
5. `lwExpandIdentity_holds`;
6. the compiled instances `RBM.Gauss.LWInst.lwExpTerm5_inst_*` (`d = 3`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Green

/-! ## 1. Vocabulary (the probe, lines 55-71, 80-86) -/

/-- Copy of T2265's `LWJoinedPin` (`docs/tickets/checks/T2265-check.lean`, section 2). -/
def LWJoined (P : PGraph (Fin 2)) : Prop :=
  P.ext 0 ≠ P.ext 1 ∧ P.g.molOf (Sum.inl (P.ext 0)) = P.g.molOf (Sum.inl (P.ext 1)) ∧
    P.g.nM = 0

/-- **Candidate** of a node: an internal vertex `x` with a blue uncircled non-loop out-edge `p.1` and a
blue uncircled non-loop in-edge `q.1`, in exactly the shape `oe2x_graph_E` (`LWGGExp.lean:1550`)
consumes (`hp`, `hp1`, `hq`, `hq1`, `hy`). -/
def LWG5Cand (P : PGraph (Fin 2)) : Prop :=
  ∃ (x : P.I') (y y' : P.E' ⊕ P.I') (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))),
    p ∈ lwSplit P.g.solid ∧ q ∈ lwSplit p.2 ∧ y ≠ Sum.inr x ∧ y' ≠ Sum.inr x ∧
      p.1 = ⟨true, false, Sum.inr x, y⟩ ∧ q.1 = ⟨true, false, y', Sum.inr x⟩

/-- **Progress** at one node (supervisor 1102 §3): below the order target there is a candidate.
`stuckG` (T2265 report (b)) shows this is not implied by Amend 1's invariants. -/
def LWG5Progress (P : PGraph (Fin 2)) : Prop :=
  P.g.scalingOrder < (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) → LWG5Cand P

/-- **Identity half** of T2265's `LWG5Expand'Pin` (T2265a): the expectation identity for a given list. -/
def LWG5Identity (d : ℕ) (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool)
    (x y : Idx d (sz.L n) (sz.W n)),
    ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
      ((Ls k s).map fun q =>
        (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
          ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum

/-! ## 2. The expansion procedure (the probe, lines 113-207) -/

section Procedure

variable {V : Type*} [DecidableEq V]

/-- `lwSplitLoops` with the exponents `(j, j')` of `m`, `m̄` in place of the coefficient. -/
def lwSplitLoopsX : List (SEdge V) → List ((ℕ × ℕ) × List (SEdge V))
  | [] => [((0, 0), [])]
  | e :: es => (lwSplitLoopsX es).flatMap fun r =>
      if e.src = e.dst ∧ e.circ = false then
        [(r.1, ⟨e.σ, true, e.src, e.dst⟩ :: r.2),
          ((if e.σ then (r.1.1 + 1, r.1.2) else (r.1.1, r.1.2 + 1)), r.2)]
      else [(r.1, e :: r.2)]

end Procedure

section Partition

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The exponent-tracking partition: `Γ.partition m` with the coefficient `m^j m̄^{j'}` split off. -/
def partitionX (Γ : LGraph E I) : List ((ℕ × ℕ) × PGraph E) :=
  Γ.partitionTerms.flatMap fun Δ =>
    (lwSplitLoopsX Δ.merge.solid).map fun r =>
      (r.1, { E' := Δ.ExtCls, I' := Δ.IntCls, ext := Δ.extMap, ext_surj := Δ.extMap_surj,
              g := { Δ.merge with solid := r.2 } })

/-- (T2265a) the exponent-tracking partition is the partition (list-wise, coefficients scaled). -/
def PartitionXSpec : Prop :=
  ∀ (m : ℂ) (Γ : LGraph E I), (Γ.partition m).map (fun P => P.g.coeff) =
    (partitionX Γ).map fun r => m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff

end Partition

/-- A packed graph read through the external map of its parent. -/
def pcomp (P : PGraph (Fin 2)) (Q : PGraph P.E') : PGraph (Fin 2) :=
  { E' := Q.E', I' := Q.I', ext := Q.ext ∘ P.ext, ext_surj := Q.ext_surj.comp P.ext_surj, g := Q.g }

/-- **A candidate** of a packed graph, as data (the data of `LWG5Cand`). -/
structure RCand (P : PGraph (Fin 2)) where
  x : P.I'
  y : P.E' ⊕ P.I'
  y' : P.E' ⊕ P.I'
  p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))
  q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))
  hp : p ∈ lwSplit P.g.solid
  hq : q ∈ lwSplit p.2
  hy : y ≠ Sum.inr x
  hy' : y' ≠ Sum.inr x
  hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩
  hq1 : q.1 = ⟨true, false, y', Sum.inr x⟩

theorem lwG5Cand_iff_nonempty (P : PGraph (Fin 2)) : LWG5Cand P ↔ Nonempty (RCand P) := by
  constructor
  · rintro ⟨x, y, y', p, q, hp, hq, hy, hy', hp1, hq1⟩
    exact ⟨⟨x, y, y', p, q, hp, hq, hy, hy', hp1, hq1⟩⟩
  · rintro ⟨⟨x, y, y', p, q, hp, hq, hy, hy', hp1, hq1⟩⟩
    exact ⟨x, y, y', p, q, hp, hq, hy, hy', hp1, hq1⟩

/-- The children of a packed graph at a candidate: the partitions of the seven `(Oe2x)` families `R2`-`R8`
(`R1` has value `0` on a normal graph: `x ≠ y` joined by a `×`-edge and the `=`-edge), with the exponents of
`m` (`R2, R4, R6, R8`: `3`; `R3, R5, R7`: `1`; `oe2xRi 1` is the family with `m = 1`). -/
def RCand.kids {P : PGraph (Fin 2)} (c : RCand P) : List ((ℕ × ℕ) × PGraph (Fin 2)) :=
  let sh : ℕ → List ((ℕ × ℕ) × PGraph P.E') → List ((ℕ × ℕ) × PGraph (Fin 2)) := fun j l =>
    l.map fun r => ((r.1.1 + j, r.1.2), pcomp P r.2)
  sh 3 (partitionX (oe2xR2 1 P.g c.q c.x c.y c.y')) ++
  sh 1 (partitionX (owxT1 1 P.g c.x)) ++
  sh 3 (partitionX (oe2xR4 1 P.g c.q c.x c.y c.y')) ++
  sh 1 (partitionX (oe2xR5 1 P.g c.q c.x c.y c.y')) ++
  sh 3 (partitionX (oe2xR6 1 P.g c.q c.x c.y c.y')) ++
  (lwSplit c.q.2).flatMap fun q' =>
    sh 1 (partitionX (oe2xR7 1 P.g c.x c.y c.y' q')) ++ sh 3 (partitionX (oe2xR8 1 P.g c.x c.y c.y' q'))

/-- A selection rule: a candidate or `none`. -/
abbrev Sel := (P : PGraph (Fin 2)) → Option (RCand P)

/-- The expansion procedure with fuel: leaf if `ord ≥ tg`, if the fuel is out, or if `sel` returns none. -/
def expand (sel : Sel) : ℕ → PGraph (Fin 2) → List ((ℕ × ℕ) × PGraph (Fin 2))
  | 0, P => [((0, 0), P)]
  | n + 1, P =>
    if (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder then [((0, 0), P)]
    else match sel P with
      | none => [((0, 0), P)]
      | some c => c.kids.flatMap fun r => (expand sel n r.2).map fun t => ((r.1.1 + t.1.1, r.1.2 + t.1.2), t.2)

/-- The list of the root: the partition of `LWG5Graph k s`, each term expanded. -/
def expandRoot (sel : Sel) (fuel : ℕ) (k s : Bool) : List ((ℕ × ℕ) × PGraph (Fin 2)) :=
  (partitionX (LWG5Graph k s)).flatMap fun r =>
    (expand sel fuel r.2).map fun t => ((r.1.1 + t.1.1, r.1.2 + t.1.2), t.2)

/-- **The identity half (T2265a)**: for every selection rule and every fuel the list of the procedure satisfies the
expectation identity.  (The leaf half is the certificate side; it picks `sel` and `fuel`.) -/
def LWExpandIdentity (sel : Sel) (fuel : ℕ) : Prop :=
  ∀ d, LWG5Identity d (expandRoot sel fuel)

/-- the selection rule of the certificate side: some candidate when there is one -/
def selClassical : Sel := fun P =>
  open Classical in if h : LWG5Cand P then some (Classical.choice ((lwG5Cand_iff_nonempty P).1 h)) else none


/-! ## 3. The abstract step (supervisor 1356 O6, DECISIONS §105 (2)) -/

/-- **The expansion along an abstract step** `st` on a carrier `X` (`none` = leaf), with fuel; the exponent
pairs add along a branch exactly as in the probe's `expand`. -/
def expandG {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) : ℕ → X → List ((ℕ × ℕ) × X)
  | 0, P => [((0, 0), P)]
  | n + 1, P =>
    match st P with
    | none => [((0, 0), P)]
    | some l => l.flatMap fun r => (expandG st n r.2).map fun t => ((r.1.1 + t.1.1, r.1.2 + t.1.2), t.2)

/-- **The induction along `expandG`**: an invariant `Inv` kept by every step and a valuation `Φ` that every step
preserves with a multiplicative weight `w` give, for every fuel, the invariant at every output and the identity
`Φ P = Σ w · Φ` over the outputs. -/
def ExpandGSum {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) (Inv : X → Prop) (Φ : X → ℂ)
    (w : ℕ × ℕ → ℂ) : Prop :=
  w (0, 0) = 1 → (∀ a b c e : ℕ, w (a + c, b + e) = w (a, b) * w (c, e)) →
    (∀ (P : X) (l : List ((ℕ × ℕ) × X)), Inv P → st P = some l →
      (∀ r ∈ l, Inv r.2) ∧ Φ P = (l.map fun r => w r.1 * Φ r.2).sum) →
    ∀ (n : ℕ) (P : X), Inv P →
      Φ P = ((expandG st n P).map fun t => w t.1 * Φ t.2).sum ∧ ∀ t ∈ expandG st n P, Inv t.2

private theorem lwExpTerm5_sum_flatMap {α β : Type*} [AddCommMonoid β] (a : List α) (g : α → List β) :
    (a.flatMap g).sum = (a.map fun x => (g x).sum).sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- The weighted sum over `l.flatMap (g · then expand)` is the weighted sum over `l`, if `Φ` is the weighted sum
over `g` at every member of `l`. -/
private theorem lwExpTerm5_flat_sum {X : Type*} (Φ : X → ℂ) (w : ℕ × ℕ → ℂ)
    (hmul : ∀ a b c e : ℕ, w (a + c, b + e) = w (a, b) * w (c, e)) (l : List ((ℕ × ℕ) × X))
    (g : X → List ((ℕ × ℕ) × X))
    (hg : ∀ r ∈ l, Φ r.2 = ((g r.2).map fun t => w t.1 * Φ t.2).sum) :
    ((l.flatMap fun r => (g r.2).map fun t => ((r.1.1 + t.1.1, r.1.2 + t.1.2), t.2)).map
      fun t => w t.1 * Φ t.2).sum = (l.map fun r => w r.1 * Φ r.2).sum := by
  rw [List.map_flatMap, lwExpTerm5_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
  rw [List.map_map]
  have : ((g r.2).map ((fun t => w t.1 * Φ t.2) ∘ fun t => ((r.1.1 + t.1.1, r.1.2 + t.1.2), t.2))) =
      (g r.2).map fun t => w r.1 * (w t.1 * Φ t.2) := by
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    rw [hmul r.1.1 r.1.2 t.1.1 t.1.2]
    ring
  rw [this, List.sum_map_mul_left, ← hg r hr]

/-- **`expandG_sum`**: the induction for every step, every invariant and every multiplicative weight (induction on
the fuel). -/
theorem expandG_sum {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) (Inv : X → Prop) (Φ : X → ℂ)
    (w : ℕ × ℕ → ℂ) : ExpandGSum st Inv Φ w := by
  intro hw0 hmul hstep n
  induction n with
  | zero =>
    intro P hP
    simp [expandG, hw0, hP]
  | succ n ih =>
    intro P hP
    cases hst : st P with
    | none => simp [expandG, hst, hw0, hP]
    | some l =>
      obtain ⟨hInv, hΦ⟩ := hstep P l hP hst
      have hexp : expandG st (n + 1) P =
          l.flatMap fun r => (expandG st n r.2).map fun t => ((r.1.1 + t.1.1, r.1.2 + t.1.2), t.2) := by
        simp [expandG, hst]
      rw [hexp]
      refine ⟨?_, ?_⟩
      · rw [hΦ, lwExpTerm5_flat_sum Φ w hmul l (fun r => expandG st n r) fun r hr => (ih r.2 (hInv r hr)).1]
      · intro t ht
        obtain ⟨r, hr, ht⟩ := List.mem_flatMap.1 ht
        obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
        exact (ih r.2 (hInv r hr)).2 t' ht'

/-- The step of the procedure (`none` = leaf). -/
noncomputable def lwStep (sel : Sel) (P : PGraph (Fin 2)) :
    Option (List ((ℕ × ℕ) × PGraph (Fin 2))) :=
  if (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder then none else (sel P).map RCand.kids

/-- `expand` is the abstract expansion along `lwStep`. -/
theorem expand_eq_expandG (sel : Sel) (n : ℕ) (P : PGraph (Fin 2)) :
    expand sel n P = expandG (lwStep sel) n P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    by_cases h : (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder
    · simp [expand, expandG, lwStep, h]
    · cases hs : sel P with
      | none => simp [expand, expandG, lwStep, h, hs]
      | some c => simp [expand, expandG, lwStep, h, hs, ih]


/-! ## 4. The proved lemmas -/

section Bridge

/-- `lwSplitLoopsX` is `lwSplitLoops` with exponents (T2265a, by induction on the list; probe 444-454). -/
theorem lwSplitLoopsX_spec {V : Type*} [DecidableEq V] (m : ℂ) (es : List (SEdge V)) :
    lwSplitLoops m es = (lwSplitLoopsX es).map fun r => (m ^ r.1.1 * star m ^ r.1.2, r.2) := by
  induction es with
  | nil => simp [lwSplitLoops, lwSplitLoopsX]
  | cons e es ih =>
    simp only [lwSplitLoops, lwSplitLoopsX, ih, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun r _ => ?_
    by_cases h : e.src = e.dst ∧ e.circ = false
    · cases hσ : e.σ <;> simp [h, hσ] <;> ring
    · simp [h]

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- A packed graph with its coefficient multiplied by `c`. -/
private def lwExpTerm5_scaleP {E0 : Type} (c : ℂ) (P : PGraph E0) : PGraph E0 :=
  { P with g := { P.g with coeff := c * P.g.coeff } }

/-- The partition is the exponent-tracking partition with the coefficients `m^j m̄^{j'}` multiplied in. -/
private theorem lwExpTerm5_partition_eq (m : ℂ) (Γ : LGraph E I) :
    Γ.partition m = (partitionX Γ).map fun r => lwExpTerm5_scaleP (m ^ r.1.1 * star m ^ r.1.2) r.2 := by
  unfold LGraph.partition partitionX
  rw [List.map_flatMap]
  refine List.flatMap_congr fun Δ _ => ?_
  unfold LGraph.mergeSplitP LGraph.splitWeights
  rw [lwSplitLoopsX_spec m Δ.merge.solid]
  simp only [List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [lwExpTerm5_scaleP]

theorem partitionX_spec : PartitionXSpec (E := E) (I := I) := by
  intro m Γ
  rw [lwExpTerm5_partition_eq, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [lwExpTerm5_scaleP]

/-- A graph with the same edges and the coefficient multiplied by `c` has the value multiplied by `c`. -/
private theorem lwExpTerm5_val_coeff {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T T' : LGraph E' I') (c : ℂ)
    (hs : T'.solid = T.solid) (hw : T'.waved = T.waved) (hd : T'.dotted = T.dotted)
    (hc : T'.coeff = c * T.coeff) (D : LData ι) (ℓ : E' → ι) : T'.val D ℓ = c * T.val D ℓ := by
  unfold LGraph.val
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  simp only [LGraph.term, hs, hw, hd, hc]
  ring

private theorem lwExpTerm5_val_scaleP {E0 : Type} {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ) (P : PGraph E0)
    (D : LData ι) (ℓe : E0 → ι) : (lwExpTerm5_scaleP c P).val D ℓe = c * P.val D ℓe := by
  by_cases h : ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := h
    rw [PGraph.val_of_factor (lwExpTerm5_scaleP c P) D hℓ, PGraph.val_of_factor P D hℓ]
    exact lwExpTerm5_val_coeff P.g (lwExpTerm5_scaleP c P).g c rfl rfl rfl rfl D ℓ'
  · rw [PGraph.val_of_not (lwExpTerm5_scaleP c P) D h, PGraph.val_of_not P D h, mul_zero]

/-- **The exponent-tracking partition has the value of the graph** (`dot-def`, `7_8:221-222`; binders as
`LGraph.val_eq_partition`). -/
theorem val_eq_partitionX {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℂ) (Γ : LGraph E I) (D : LData ι)
    (hM : ∀ x, D.M x x = m) (ℓe : E → ι) :
    Γ.val D ℓe = ((partitionX Γ).map fun r => m ^ r.1.1 * star m ^ r.1.2 * r.2.val D ℓe).sum := by
  rw [Γ.val_eq_partition m D hM ℓe]
  unfold LComb.val
  rw [lwExpTerm5_partition_eq, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  exact lwExpTerm5_val_scaleP _ r.2 D ℓe

/-- Every term of the exponent-tracking partition is a normal graph. -/
theorem partitionX_normal (Γ : LGraph E I) : ∀ r ∈ partitionX Γ, r.2.g.Normal := by
  intro r hr
  have h := LGraph.partition_normal 1 Γ (lwExpTerm5_scaleP (1 ^ r.1.1 * star 1 ^ r.1.2) r.2)
    (by rw [lwExpTerm5_partition_eq]; exact List.mem_map.2 ⟨r, hr, rfl⟩)
  exact h

end Bridge

section R1

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`R1` has value `0` on a normal graph**: `G_{xy}` (`p.1`, `x ≠ y`) is a solid edge between two different
vertices, so by `Normal` (iii) a `×`-dotted edge joins them; the `=`-dotted edge `x = y` of `oe2xR1d` kills the
product at every labelling.  Hypotheses used: `Γ.Normal`, `p ∈ lwSplit Γ.solid`, `p.1 = G_{xy}`, `y ≠ x`;
nothing about `m`, `D`, `ℓe`. -/
theorem oe2xR1_val_zero (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (y : E ⊕ I)
    (hy : y ≠ Sum.inr x) (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩) (D : LData ι) (ℓe : E → ι) :
    (oe2xR1 m Γ p x y hy).val D ℓe = 0 := by
  rw [oe2xR1_val]
  have hS : Γ.SBetween (Sum.inr x) y :=
    ⟨p.1, lvl1_mem_split_fst _ p hp, by rw [hp1]; exact fun h => hy h.symm,
      Or.inl ⟨by rw [hp1], by rw [hp1]⟩⟩
  obtain ⟨e, he, hef, hexy⟩ := (hN.2.1 (Sum.inr x) y (Ne.symm hy)).2 hS
  unfold LGraph.val
  refine Finset.sum_eq_zero fun ℓi _ => ?_
  set ℓ : E ⊕ I → ι := Sum.elim ℓe ℓi with hℓ
  by_cases hxy : ℓ (Sum.inr x) = ℓ y
  · have h0 : DEdge.val ℓ e = 0 := by
      have hee : ℓ e.x = ℓ e.y := by
        rcases hexy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hxy
        · rw [h1, h2]; exact hxy.symm
      simp [DEdge.val, hef, hee]
    have hprod : (Γ.dotted.map (DEdge.val ℓ)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.2 ⟨e, he, h0⟩)
    simp [LGraph.term, oe2xR1d, hprod]
  · simp [LGraph.term, oe2xR1d, DEdge.val, hxy]

end R1

section Kids

/-- Every child of a candidate is a normal graph read through `pcomp P` (for the support and the normality). -/
private theorem lwExpTerm5_kids_mem {P : PGraph (Fin 2)} (c : RCand P) :
    ∀ r ∈ c.kids, ∃ Q : PGraph P.E', r.2 = pcomp P Q ∧ Q.g.Normal := by
  have sh : ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (j : ℕ) (T : LGraph P.E' I')
      (r : (ℕ × ℕ) × PGraph (Fin 2)),
      r ∈ (partitionX T).map (fun r => ((r.1.1 + j, r.1.2), pcomp P r.2)) →
        ∃ Q : PGraph P.E', r.2 = pcomp P Q ∧ Q.g.Normal := by
    intro I' _ _ j T r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact ⟨r'.2, rfl, partitionX_normal T r' hr'⟩
  intro r hr
  simp only [RCand.kids, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ((((h | h) | h) | h) | h) | ⟨q', _, h | h⟩
  exacts [sh _ _ r h, sh _ _ r h, sh _ _ r h, sh _ _ r h, sh _ _ r h, sh _ _ r h, sh _ _ r h]

/-- **Every child of a candidate is a normal graph.** -/
theorem RCand.kids_normal {P : PGraph (Fin 2)} (c : RCand P) : ∀ r ∈ c.kids, r.2.g.Normal := by
  intro r hr
  obtain ⟨Q, hQ, hN⟩ := lwExpTerm5_kids_mem c r hr
  rw [hQ]
  exact hN

end Kids

section Identity

variable {d : ℕ} (sz : Sizes d) (n : ℕ) {E t : ℝ}

/-- Every graph value is integrable under the flow data (`oe2x_graph_E`'s `hint`, summed over the labellings). -/
private theorem lwExpTerm5_integrable_val (hE : |E| < 2) (ht1 : t < 1) {E' I' : Type} [Fintype E']
    [DecidableEq E'] [Fintype I'] [DecidableEq I'] (T : LGraph E' I') (ℓ' : E' → Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => T.val (LWG5Data sz n E t ω) ℓ') (sz.seqP) := by
  unfold LGraph.val
  exact integrable_finsetSum _ fun ℓi _ =>
    Tame.integrable (gaussIBP sz) (lwStein_term_tame1 (lwWx_im_pos E t hE ht1) T _).tame

/-- Every packed graph value is integrable. -/
private theorem lwExpTerm5_integrable_pval (hE : |E| < 2) (ht1 : t < 1) {E0 : Type} (Q : PGraph E0)
    (ℓe : E0 → Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => Q.val (LWG5Data sz n E t ω) ℓe) (sz.seqP) := by
  by_cases h : ∃ ℓ' : Q.E' → Idx d (sz.L n) (sz.W n), ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ⟩ := h
    simp_rw [PGraph.val_of_factor Q _ hℓ]
    exact lwExpTerm5_integrable_val sz n hE ht1 Q.g ℓ'
  · simp_rw [PGraph.val_of_not Q _ h]
    exact integrable_zero _ _ _

/-- The expectation of a graph value is the weighted sum of the expectations over its exponent-tracking partition
(`m = mE E`, `M = m I`). -/
private theorem lwExpTerm5_integral_partitionX (hE : |E| < 2) (ht1 : t < 1) {E' I' : Type} [Fintype E']
    [DecidableEq E'] [Fintype I'] [DecidableEq I'] (T : LGraph E' I') (ℓ' : E' → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, T.val (LWG5Data sz n E t ω) ℓ' ∂(sz.seqP) =
      ((partitionX T).map fun r => (mE E) ^ r.1.1 * star (mE E) ^ r.1.2 *
        ∫ ω, r.2.val (LWG5Data sz n E t ω) ℓ' ∂(sz.seqP)).sum := by
  have hM : ∀ ω, ∀ a, (LWG5Data sz n E t ω).M a a = mE E := fun ω a => by
    simp [lwExpTerm3_Data_M]
  have h1 : ∀ ω, T.val (LWG5Data sz n E t ω) ℓ' = ((partitionX T).map fun r =>
      (mE E) ^ r.1.1 * star (mE E) ^ r.1.2 * r.2.val (LWG5Data sz n E t ω) ℓ').sum :=
    fun ω => val_eq_partitionX (mE E) T _ (hM ω) ℓ'
  simp_rw [h1]
  rw [owx_integral_list_sum _ (partitionX T)
    (fun r ω => (mE E) ^ r.1.1 * star (mE E) ^ r.1.2 * r.2.val (LWG5Data sz n E t ω) ℓ')
    (fun r _ => (lwExpTerm5_integrable_pval sz n hE ht1 r.2 ℓ').const_mul _)]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  exact integral_const_mul _ _

variable {sz n}

private theorem lwExpTerm5_pcomp_val {ι : Type*} [Fintype ι] [DecidableEq ι] (P : PGraph (Fin 2))
    (Q : PGraph P.E') (D : LData ι) {ℓe : Fin 2 → ι} {ℓ' : P.E' → ι} (hℓ : ℓe = ℓ' ∘ P.ext) :
    (pcomp P Q).val D ℓe = Q.val D ℓ' := by
  have h : pcomp P Q = Q.lvl1Comp P.ext P.ext_surj := rfl
  rw [h, PGraph.lvl1Comp_val]
  have hex : ∃ ℓ'' : P.E' → ι, ℓe = ℓ'' ∘ P.ext := ⟨ℓ', hℓ⟩
  simp only [hex, ↓reduceDIte]
  congr 1
  apply P.ext_surj.injective_comp_right
  exact hex.choose_spec.symm.trans hℓ

private theorem lwExpTerm5_pcomp_val_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (P : PGraph (Fin 2))
    (Q : PGraph P.E') (D : LData ι) {ℓe : Fin 2 → ι} (hf : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) :
    (pcomp P Q).val D ℓe = 0 := by
  have h : pcomp P Q = Q.lvl1Comp P.ext P.ext_surj := rfl
  rw [h, PGraph.lvl1Comp_val]
  simp only [hf, ↓reduceDIte]

variable (sz n)

/-- One family of `(Oe2x)`: the family at `m` is `m^j` times the family at `1`, whose partition is `kids`'s block. -/
private theorem lwExpTerm5_fam (hE : |E| < 2) (ht1 : t < 1) (P : PGraph (Fin 2)) {I' : Type} [Fintype I']
    [DecidableEq I'] (j : ℕ) (T1 Tm : LGraph P.E' I') (hs : Tm.solid = T1.solid) (hw : Tm.waved = T1.waved)
    (hd : Tm.dotted = T1.dotted) (hc : Tm.coeff = mE E ^ j * T1.coeff)
    {ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)} {ℓ' : P.E' → Idx d (sz.L n) (sz.W n)} (hℓ : ℓe = ℓ' ∘ P.ext) :
    ∫ ω, Tm.val (LWG5Data sz n E t ω) ℓ' ∂(sz.seqP) =
      (((partitionX T1).map fun r => ((r.1.1 + j, r.1.2), pcomp P r.2)).map fun q =>
        (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
          ∫ ω, q.2.val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP)).sum := by
  have h1 : ∀ ω, Tm.val (LWG5Data sz n E t ω) ℓ' = mE E ^ j * T1.val (LWG5Data sz n E t ω) ℓ' :=
    fun ω => lwExpTerm5_val_coeff T1 Tm _ hs hw hd hc _ _
  simp_rw [h1]
  rw [integral_const_mul, lwExpTerm5_integral_partitionX sz n hE ht1 T1 ℓ', List.map_map,
    ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  simp only [Function.comp_apply]
  have : ∀ ω, (pcomp P r.2).val (LWG5Data sz n E t ω) ℓe = r.2.val (LWG5Data sz n E t ω) ℓ' :=
    fun ω => lwExpTerm5_pcomp_val P r.2 _ hℓ
  simp_rw [this]
  rw [pow_add]
  ring

/-- `oe2x_graph_E` at the flow data `LWG5Data` (`G = (H_t - z_t)⁻¹`, `M = m I`, `S = lwS`, `S⁺ = lwSplus`; `z = z_t`,
`u = t`, `m = mE E`, in §34 order). -/
private theorem lwExpTerm5_oe2x (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1) {E0 I0 : Type} [Fintype E0]
    [DecidableEq E0] [Fintype I0] [DecidableEq I0] (Γ : LGraph E0 I0) (x : I0) (y y' : E0 ⊕ I0)
    (hy : y ≠ Sum.inr x) (p : SEdge (E0 ⊕ I0) × List (SEdge (E0 ⊕ I0))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩) (q : SEdge (E0 ⊕ I0) × List (SEdge (E0 ⊕ I0)))
    (hq : q ∈ lwSplit p.2) (hq1 : q.1 = ⟨true, false, y', Sum.inr x⟩) (ℓe : E0 → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP) =
      ∫ ω, (oe2xR1 (mE E) Γ p x y hy).val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP) +
      ∫ ω, (oe2xR2 (mE E) Γ q x y y').val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP) +
      ∫ ω, (owxT1 (mE E) Γ x).val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP) +
      ∫ ω, (oe2xR4 (mE E) Γ q x y y').val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP) +
      ∫ ω, (oe2xR5 (mE E) Γ q x y y').val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP) +
      ∫ ω, (oe2xR6 (mE E) Γ q x y y').val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP) +
      ((lwSplit q.2).map fun q' =>
        ∫ ω, (oe2xR7 (mE E) Γ x y y' q').val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP)).sum +
      ((lwSplit q.2).map fun q' =>
        ∫ ω, (oe2xR8 (mE E) Γ x y y' q').val (LWG5Data sz n E t ω) ℓe ∂(sz.seqP)).sum :=
  oe2x_graph_E (RBM.Green.gaussIBP sz) (lwWx_im_pos E t hE ht1) ht0 (lwWx_mE_ne E hE) (lwWx_flow E t hE)
    (lwSplus sz n t (mE E)) (Matrix.diagonal fun _ => mE E)
    (lwSplus_spec ht0.le (by rw [norm_mE hE.le]; simpa using ht1)) (fun a => by simp) Γ x y y' hy p hp hp1 q hq hq1 ℓe

end Identity

section Main

/-- **One step of the expansion is an identity in expectation** (`(Oe2x)` at a candidate; `B:78-94`): for a normal
graph `P` and a candidate `c`, `𝔼 P.val = Σ_{kids} m^j m̄^{j'} 𝔼 child.val` at the data `LWG5Data` and the external
labels `![x, y]`; `R1` is dropped by value (`oe2xR1_val_zero`). -/
theorem RCand.kids_identity {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1)
    {P : PGraph (Fin 2)} (hN : P.g.Normal) (c : RCand P) (x y : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, P.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
      (c.kids.map fun r => (mE E) ^ r.1.1 * star (mE E) ^ r.1.2 *
        ∫ ω, r.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum := by
  by_cases hf : ∃ ℓ' : P.E' → Idx d (sz.L n) (sz.W n), ![x, y] = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    have hL : ∫ ω, P.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
        ∫ ω, P.g.val (LWG5Data sz n E t ω) ℓ' ∂(sz.seqP) := by
      simp_rw [PGraph.val_of_factor P _ hℓ]
    rw [hL, lwExpTerm5_oe2x sz n hE ht0 ht1 P.g c.x c.y c.y' c.hy c.p c.hp c.hp1 c.q c.hq c.hq1 ℓ']
    have hR1 : ∫ ω, (oe2xR1 (mE E) P.g c.p c.x c.y c.hy).val (LWG5Data sz n E t ω) ℓ' ∂(sz.seqP) = 0 := by
      simp_rw [oe2xR1_val_zero (mE E) P.g hN c.p c.hp c.x c.y c.hy c.hp1 _ ℓ']
      simp
    rw [hR1, zero_add]
    have e2 := lwExpTerm5_fam sz n hE ht1 P 3 (oe2xR2 1 P.g c.q c.x c.y c.y')
      (oe2xR2 (mE E) P.g c.q c.x c.y c.y') rfl rfl rfl (by simp [oe2xR2, LGraph.owxExt]) hℓ
    have e3 := lwExpTerm5_fam sz n hE ht1 P 1 (owxT1 1 P.g c.x) (owxT1 (mE E) P.g c.x)
      rfl rfl rfl (by simp [owxT1, LGraph.owxExt]) hℓ
    have e4 := lwExpTerm5_fam sz n hE ht1 P 3 (oe2xR4 1 P.g c.q c.x c.y c.y')
      (oe2xR4 (mE E) P.g c.q c.x c.y c.y') rfl rfl rfl (by simp [oe2xR4, LGraph.owxExt]) hℓ
    have e5 := lwExpTerm5_fam sz n hE ht1 P 1 (oe2xR5 1 P.g c.q c.x c.y c.y')
      (oe2xR5 (mE E) P.g c.q c.x c.y c.y') rfl rfl rfl (by simp [oe2xR5, LGraph.owxExt]) hℓ
    have e6 := lwExpTerm5_fam sz n hE ht1 P 3 (oe2xR6 1 P.g c.q c.x c.y c.y')
      (oe2xR6 (mE E) P.g c.q c.x c.y c.y') rfl rfl rfl (by simp [oe2xR6, LGraph.owxExt]) hℓ
    have e7 : ((lwSplit c.q.2).map fun q' =>
        ∫ ω, (oe2xR7 (mE E) P.g c.x c.y c.y' q').val (LWG5Data sz n E t ω) ℓ' ∂(sz.seqP)).sum =
        ((lwSplit c.q.2).map fun q' =>
          (((partitionX (oe2xR7 1 P.g c.x c.y c.y' q')).map fun r => ((r.1.1 + 1, r.1.2), pcomp P r.2)).map
            fun q => (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
              ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum).sum :=
      congrArg List.sum (List.map_congr_left fun q' _ =>
        lwExpTerm5_fam sz n hE ht1 P 1 (oe2xR7 1 P.g c.x c.y c.y' q') (oe2xR7 (mE E) P.g c.x c.y c.y' q')
          rfl rfl rfl (by simp [oe2xR7, LGraph.owxExt]) hℓ)
    have e8 : ((lwSplit c.q.2).map fun q' =>
        ∫ ω, (oe2xR8 (mE E) P.g c.x c.y c.y' q').val (LWG5Data sz n E t ω) ℓ' ∂(sz.seqP)).sum =
        ((lwSplit c.q.2).map fun q' =>
          (((partitionX (oe2xR8 1 P.g c.x c.y c.y' q')).map fun r => ((r.1.1 + 3, r.1.2), pcomp P r.2)).map
            fun q => (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
              ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum).sum :=
      congrArg List.sum (List.map_congr_left fun q' _ =>
        lwExpTerm5_fam sz n hE ht1 P 3 (oe2xR8 1 P.g c.x c.y c.y' q') (oe2xR8 (mE E) P.g c.x c.y c.y' q')
          rfl rfl rfl (by simp [oe2xR8, LGraph.owxExt]) hℓ)
    rw [e2, e3, e4, e5, e6, e7, e8]
    simp only [RCand.kids, List.map_append, List.sum_append, List.map_flatMap, lwExpTerm5_sum_flatMap,
      List.sum_map_add]
    ring
  · have h0 : ∀ ω, P.val (LWG5Data sz n E t ω) ![x, y] = 0 := fun ω => PGraph.val_of_not P _ hf
    simp_rw [h0]
    rw [integral_zero]
    symm
    refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
    obtain ⟨Q, hQ, _⟩ := lwExpTerm5_kids_mem c r hr
    have h1 : ∀ ω, r.2.val (LWG5Data sz n E t ω) ![x, y] = 0 := fun ω => by
      rw [hQ]
      exact lwExpTerm5_pcomp_val_zero P Q _ hf
    simp_rw [h1]
    simp


/-- **The identity half of LW-14e for every selection rule and every fuel** (`B:78-108`): the list of
`expandRoot sel fuel` satisfies the expectation identity `𝔼 𝒢_xy = Σ_μ m^{j_μ} m̄^{j'_μ} 𝔼 Γ_μ`. -/
theorem lwExpandIdentity_holds : ∀ (sel : Sel) (fuel : ℕ), LWExpandIdentity sel fuel := by
  intro sel fuel d sz n E t hE ht0 ht1 k s x y
  have hw0 : ((mE E) ^ (0 : ℕ) * star (mE E) ^ (0 : ℕ) : ℂ) = 1 := by simp
  have hmul : ∀ a b c e : ℕ, (mE E) ^ (a + c) * star (mE E) ^ (b + e) =
      ((mE E) ^ a * star (mE E) ^ b) * ((mE E) ^ c * star (mE E) ^ e) := by
    intro a b c e
    rw [pow_add, pow_add]
    ring
  have hexp := expandG_sum (lwStep sel) (fun P : PGraph (Fin 2) => P.g.Normal)
    (fun P => ∫ ω, P.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP))
    (fun q => (mE E) ^ q.1 * star (mE E) ^ q.2) hw0 hmul
    (by
      intro P l hP hst
      unfold lwStep at hst
      by_cases hl : (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder
      · simp only [hl, ↓reduceIte] at hst
        exact absurd hst (by simp)
      · simp only [hl, ↓reduceIte] at hst
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hst
        exact ⟨c.kids_normal, RCand.kids_identity sz n E t hE ht0 ht1 hP c x y⟩) fuel
  have hroot := lwExpTerm5_integral_partitionX sz n hE ht1 (LWG5Graph k s) ![x, y]
  rw [hroot]
  unfold expandRoot
  rw [lwExpTerm5_flat_sum (fun P : PGraph (Fin 2) => ∫ ω, P.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP))
    (fun q => (mE E) ^ q.1 * star (mE E) ^ q.2) hmul (partitionX (LWG5Graph k s))
    (fun P => expand sel fuel P) (by
      intro r hr
      simp_rw [expand_eq_expandG]
      exact (hexp r.2 (partitionX_normal _ r hr)).1)]

end Main

end RBM.Gauss.Sizes

/-! ## 6. The compiled instance (`d = 3`, `sz0`, `n = 0`, `E = STflowE z0 0`, `t = 1/16`) -/

namespace RBM.Gauss.LWInst

open RBM RBM.Loop RBM.Graph RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- **Instance of `lwExpandIdentity_holds`** at `d = 3`, `sz0`, `n = 0`, `E = STflowE z0 0`, `t = 1/16`, the rule
`selClassical`, fuel `4`, both kernels and charges, all external labels `x, y`: no hypothesis
(`|STflowE z0 0| < 2` by `abs_lemE_lt_two (z0_im_pos 0)`, `0 < 1/16 < 1`). -/
theorem lwExpTerm5_inst_identity (k s : Bool) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ∫ ω, (LWG5Graph k s).val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP) =
      ((expandRoot selClassical 4 k s).map fun q =>
        (mE (STflowE z0 0)) ^ q.1.1 * star (mE (STflowE z0 0)) ^ q.1.2 *
          ∫ ω, q.2.val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP)).sum :=
  lwExpandIdentity_holds selClassical 4 3 sz0 0 (STflowE z0 0) (1 / 16) (abs_lemE_lt_two (z0_im_pos 0))
    (by norm_num) (by norm_num) k s x y


/-- The packed instance graph `lwExpTerm3_instGraph` (external `x, y`, internal `α`; normal, `n_M = 1`), as a literal. -/
private abbrev lwExpTerm5_instP : PGraph (Fin 2) :=
  { E' := Fin 2, I' := Fin 1, ext := id, ext_surj := Function.surjective_id, g := lwExpTerm3_instGraph }

/-- A candidate of `lwExpTerm5_instP` (`x = α`, `p = G_{αy}`, `q = G_{xα}`). -/
private def lwExpTerm5_instCand : RCand lwExpTerm5_instP where
  x := (0 : Fin 1)
  y := (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 1)
  y' := (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 1)
  p := ((SEdge.mk true false (Sum.inr (0 : Fin 1)) (Sum.inl (1 : Fin 2)) : SEdge (Fin 2 ⊕ Fin 1)),
    ([SEdge.mk true false (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 1)),
      SEdge.mk false false (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)),
      SEdge.mk true true (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)),
      SEdge.mk true true (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1))] : List (SEdge (Fin 2 ⊕ Fin 1))))
  q := ((SEdge.mk true false (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 1)) : SEdge (Fin 2 ⊕ Fin 1)),
    ([SEdge.mk false false (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)),
      SEdge.mk true true (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)),
      SEdge.mk true true (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1))] : List (SEdge (Fin 2 ⊕ Fin 1))))
  hp := by
    change _ ∈ lwSplit lwExpTerm3_instGraph.solid
    simp [lwSplit, lwExpTerm3_instGraph]
  hq := by simp [lwSplit]
  hy := by simp
  hy' := by simp
  hp1 := rfl
  hq1 := rfl

/-- **Instance of `RCand.kids_identity`** (one step of the expansion) at `d = 3`, `sz0`, `n = 0`,
`E = STflowE z0 0`, `t = 1/16`, the packed normal instance graph and its candidate, all labels `x, y`: no
hypothesis. -/
theorem lwExpTerm5_inst_kids_identity (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ∫ ω, lwExpTerm5_instP.val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP) =
      (lwExpTerm5_instCand.kids.map fun r => (mE (STflowE z0 0)) ^ r.1.1 * star (mE (STflowE z0 0)) ^ r.1.2 *
        ∫ ω, r.2.val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP)).sum :=
  RCand.kids_identity sz0 0 (STflowE z0 0) (1 / 16) (abs_lemE_lt_two (z0_im_pos 0)) (by norm_num)
    (by norm_num) lwExpTerm3_instGraph_normal lwExpTerm5_instCand x y

/-- **Instance of `RCand.kids_normal`** at the same candidate. -/
theorem lwExpTerm5_inst_kids_normal : ∀ r ∈ lwExpTerm5_instCand.kids, r.2.g.Normal :=
  lwExpTerm5_instCand.kids_normal

/-- **Instance of `oe2xR1_val_zero`**: the normal instance graph, `p = G_{αy}`, `α ≠ y`, all `m`, `D`, `ℓe`. -/
theorem lwExpTerm5_inst_R1_val_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℂ) (D : LData ι)
    (ℓe : Fin 2 → ι) :
    (oe2xR1 m lwExpTerm3_instGraph lwExpTerm5_instCand.p 0 (Sum.inl 1) (by simp)).val D ℓe = 0 :=
  oe2xR1_val_zero m lwExpTerm3_instGraph lwExpTerm3_instGraph_normal lwExpTerm5_instCand.p
    lwExpTerm5_instCand.hp 0 (Sum.inl 1) (by simp) lwExpTerm5_instCand.hp1 D ℓe

/-- **Instance of `val_eq_partitionX`** at the flow data of the instance (`M = m I` by `lwExpTerm3_Data_M`). -/
theorem lwExpTerm5_inst_val_eq_partitionX (k s : Bool) (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    (LWG5Graph k s).val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] =
      ((partitionX (LWG5Graph k s)).map fun r => (mE (STflowE z0 0)) ^ r.1.1 * star (mE (STflowE z0 0)) ^ r.1.2 *
        r.2.val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y]).sum :=
  val_eq_partitionX (mE (STflowE z0 0)) (LWG5Graph k s) _ (fun a => by simp [lwExpTerm3_Data_M]) ![x, y]

/-- **Instance of `partitionX_spec`, `partitionX_normal`, `lwSplitLoopsX_spec`** on the graph `LWG5Graph k s` and an
edge list with two weights and a light edge (four terms). -/
example : PartitionXSpec (E := Fin 2) (I := Fin 3) := partitionX_spec
example (k s : Bool) : ∀ r ∈ partitionX (LWG5Graph k s), r.2.g.Normal := partitionX_normal _
example (m : ℂ) :
    lwSplitLoops m [SEdge.mk true false (0 : Fin 2) 0, SEdge.mk false false 1 1, SEdge.mk true true 0 1] =
      (lwSplitLoopsX [SEdge.mk true false (0 : Fin 2) 0, SEdge.mk false false 1 1,
        SEdge.mk true true 0 1]).map fun r => (m ^ r.1.1 * star m ^ r.1.2, r.2) :=
  lwSplitLoopsX_spec m _
example : (lwSplitLoopsX [SEdge.mk true false (0 : Fin 2) 0, SEdge.mk false false 1 1,
    SEdge.mk true true 0 1]).length = 4 := by decide

/-- **Instance of `expand_eq_expandG`** at the root graph, `selClassical` and fuel `4`. -/
example : expand selClassical 4 (LWG5Graph false false).pack =
    expandG (lwStep selClassical) 4 (LWG5Graph false false).pack := expand_eq_expandG _ _ _

/-- **Instance of `expandG_sum`**: the step `n ↦ [(1,0) · (n+1), (0,1) · (n+1)]` for `n < 2` (a leaf at `2`) on `ℕ`,
the weight `w (a, b) = (1/2)^(a+b)` and `Φ = 1`; fuel `2`, start `0` (four leaves at depth `2`). -/
example :
    (1 : ℂ) = (((expandG (fun n : ℕ => if n < 2 then some [((1, 0), n + 1), ((0, 1), n + 1)] else none) 2 0).map
      fun t => (1 / 2 : ℂ) ^ (t.1.1 + t.1.2) * 1).sum) ∧
    ∀ t ∈ expandG (fun n : ℕ => if n < 2 then some [((1, 0), n + 1), ((0, 1), n + 1)] else none) 2 0, True :=
  have h := expandG_sum (fun n : ℕ => if n < 2 then some [((1, 0), n + 1), ((0, 1), n + 1)] else none)
    (fun _ => True) (fun _ => (1 : ℂ)) (fun q => (1 / 2 : ℂ) ^ (q.1 + q.2)) (by simp)
    (fun a b c e => by
      change (1 / 2 : ℂ) ^ (a + c + (b + e)) = (1 / 2) ^ (a + b) * (1 / 2) ^ (c + e)
      rw [← pow_add]
      congr 1
      ring)
    (fun P l _ hst => by
      by_cases hP : P < 2
      · simp only [hP, ↓reduceIte, Option.some.injEq] at hst
        subst hst
        refine ⟨fun _ _ => trivial, ?_⟩
        norm_num
      · simp [hP] at hst) 2 0 trivial
  ⟨by simpa using h.1, fun t _ => trivial⟩

end RBM.Gauss.LWInst
