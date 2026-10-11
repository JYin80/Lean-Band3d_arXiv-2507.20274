/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAScost

/-!
# BA-L L3b3' `BAScostS'`, part 2: the five shapes in packed form (T2426)

`Graph/BAScost.lean` proves the vocabulary, BA Lemma B, `BAInit` and the term lemmas `BAScostLL Γ T`
of the five BA-only shapes.  This file packs them as `BAShapeLL sh T` (the BA twin of
`localReg6d_locCostGe_term`, `LocalRegular6d.lean:955`): for a tagged step relation `T` whose
`sh`-tagged outputs are the packed terms of `G = Ǧ + M` on the builder terms of
`Graph/BAExpandW.lean`, `Graph/BAGGOp.lean` (as `BAPGraph.outsT` of
`t/T2423:RBM3D/Probe/T2423Pins.lean` packs them: `BAScost_pack`).

## Contents (namespace `RBM.Graph`, private helpers carry the stem `BAScost_`)

1. `BAScost_Term`, the generic packed form `baShapeLL_of_terms`.
2. `baShapeLL_s1`, `baShapeLL_e1`, `baShapeLL_e2`, `baShapeLL_macroA`, `baShapeLL_macroB`.
3. Compiled instances at the witness graphs of `BAScost.lean` (§14): a step relation with the packed
   outputs of the builder terms, the hypothesis discharged, the statement applied.

What each packed form takes as input (all else is proved): `s1`, `e1`: nothing (the term lemmas are
`BAScostLL_S1`, `BAScostLL_lanlwT1`); `e2`: the local lemma of the builder term (the band shape of
the step; Lemma B carries it to the extra outputs); `macroA`, `macroB`: the step lemma at the
transfer graph (the band step at `img(tr)` gives `Φ(tr) ≥ k ⟹ Φ(Q) ≥ k` at a stage-2 output), while
`Φ(P) ≥ k ⟹ Φ(tr) ≥ k` is proved (`BAScostLL_macroA`, `BAScostLL_macroB`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false

noncomputable section

namespace RBM.Graph

/-! ## 1. Terms of `P` and the generic packed form -/

/-- A term over the vertices of `P` (the type of its internal vertices is bundled). -/
structure BAScost_Term (P : BAPGraph (Fin 2)) where
  I'' : Type
  [instF : Fintype I'']
  [instD : DecidableEq I'']
  X : BAGraph P.E' I''

attribute [instance] BAScost_Term.instF BAScost_Term.instD

/-- **The generic packed form** (as `localReg6d_locCostGe_term` packs `LGraph.ScostLL`): if every `sh`-tagged output of `T` is a packed term of
`G = Ǧ + M` on a term `X` with `BAScostLL P.g X`, then `BAShapeLL sh T`. -/
theorem baShapeLL_of_terms {sh : BAShape} {T : BTStep}
    (h : ∀ P LT, T P LT → ∀ Q, (sh, Q) ∈ LT →
      ∃ X : BAScost_Term P, BAScostLL P.g X.X ∧ ∃ Q0 ∈ X.X.partition, Q = BAScost_pack P Q0) :
    BAShapeLL sh T := by
  intro P LT hT Q hQ far k hk
  obtain ⟨X, hX, Q0, hQ0, rfl⟩ := h P LT hT Q hQ
  exact BAScost_locCostGeA_term P X.X far k hX hk Q0 hQ0

/-! ## 2. The five shapes -/

/-- **`BAShapeLL s1`**: the `s1` outputs are the packed terms of `G = Ǧ + M` on the first term of `GGGamma` (`BAGGOp_A1`, the first term of
`gg2`) at a pair `Ǧ_{xy}`, `Ǧ_{y'x}` whose edges are not atom-level loops (the hypotheses of the step `gg`, `hwf`).  Nothing else is assumed. -/
theorem baShapeLL_s1 {T : BTStep}
    (h : ∀ P LT, T P LT → ∀ Q, (BAShape.s1, Q) ∈ LT → ∃ p q, p ∈ lwSplit P.g.solid ∧ q ∈ lwSplit p.2 ∧
      (p.1.σ = true ∧ p.1.circ = true) ∧ (q.1.σ = true ∧ q.1.circ = true) ∧ q.1.dst = p.1.src ∧
      P.g.sameAtom p.1.src p.1.dst = false ∧ P.g.sameAtom q.1.src q.1.dst = false ∧
      ∃ Q0 ∈ (BAGGOp_A1 P.g p q).partition, Q = BAScost_pack P Q0) :
    BAShapeLL BAShape.s1 T := by
  refine baShapeLL_of_terms fun P LT hT Q hQ => ?_
  obtain ⟨p, q, hp, hq, hp1, hq1, hxy, hw1, hw2, Q0, hQ0, hQe⟩ := h P LT hT Q hQ
  exact ⟨⟨P.I' ⊕ Fin 2, BAGGOp_A1 P.g p q⟩, BAScostLL_S1 P.g p q hp hq hp1 hq1 hxy hw1 hw2, Q0, hQ0, hQe⟩

/-- **`BAShapeLL e1`**: the `e1` outputs are the packed terms of `G = Ǧ + M` on the first term `T1` of `lanlw` at a blue circled edge
(`BAGraph.lanlwT1`); the extra output `M_{αy}` (`[x]`, `[y]` merged) is among them.  Nothing else is assumed. -/
theorem baShapeLL_e1 {T : BTStep}
    (h : ∀ P LT, T P LT → ∀ Q, (BAShape.e1, Q) ∈ LT → ∃ p, p ∈ lwSplit P.g.solid ∧ (p.1.σ = true ∧ p.1.circ = true) ∧
      ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, Q = BAScost_pack P Q0) :
    BAShapeLL BAShape.e1 T := by
  refine baShapeLL_of_terms fun P LT hT Q hQ => ?_
  obtain ⟨p, hp, hp1, Q0, hQ0, hQe⟩ := h P LT hT Q hQ
  exact ⟨⟨P.I' ⊕ Fin 2, BAGraph.lanlwT1 P.g p⟩, BAScostLL_lanlwT1 P.g p hp hp1, Q0, hQ0, hQe⟩

/-- **`BAShapeLL e2`**: an `e2` output is the packed term of `G = Ǧ + M` on a builder term `X` (an `M`-split joining two atoms of `P` joined by a
solid edge of `P`); the local lemma of `X` (the band shape of the step: `BAScostLL P.g X`) carries to it by Lemma B
(`BAScostLL_splitG`, `BAScostLL_E2`).  The local lemma of `X` is the input. -/
theorem baShapeLL_e2 {T : BTStep}
    (h : ∀ P LT, T P LT → ∀ Q, (BAShape.e2, Q) ∈ LT →
      ∃ X : BAScost_Term P, BAScostLL P.g X.X ∧ ∃ Q0 ∈ X.X.partition, Q = BAScost_pack P Q0) :
    BAShapeLL BAShape.e2 T :=
  baShapeLL_of_terms h

/-- **`BAShapeLL macroA`**: a `macroA` output (stage 2 of macro step (a)) is a packed term of `G = Ǧ + M` on an output of the weight step at the
transfer graph `tr = Σ M_{xα} M_{αy} S_{αβ} Ǧ_{ββ} f` of a within-atom edge, i.e. satisfies the step lemma at the packed transfer graph:
`Φ(tr) ≥ k ⟹ Φ(Q) ≥ k` (input: the band step at `img(tr)`).  The intermediate lemma `Φ(P) ≥ k ⟹ Φ(tr) ≥ k` is `BAScostLL_macroA`. -/
theorem baShapeLL_macroA {T : BTStep}
    (h : ∀ P LT, T P LT → ∀ Q, (BAShape.macroA, Q) ∈ LT → ∃ p, p ∈ lwSplit P.g.solid ∧ (p.1.σ = true ∧ p.1.circ = true) ∧
      ∃ Q0 ∈ (P.g.BAScost_trA p).partition, ∀ far k, locCostGeA far k (BAScost_pack P Q0) → locCostGeA far k Q) :
    BAShapeLL BAShape.macroA T := by
  intro P LT hT Q hQ far k hk
  obtain ⟨p, hp, hp1, Q0, hQ0, hstep⟩ := h P LT hT Q hQ
  exact hstep far k (BAScost_locCostGeA_term P (P.g.BAScost_trA p) far k (BAScostLL_macroA P.g p hp hp1) hk Q0 hQ0)

/-- **`BAShapeLL macroB`**: a `macroB` output is either (stage 2) a packed term of `G = Ǧ + M` on an output of the `GGGamma` step at the transfer
graph `tr = Σ M_{aα} M_{αa'} S_{αβ} Ǧ_{y'β} Ǧ_{βy} f` of a split pair (`a`, `a'` in one atom), which satisfies the step lemma at the packed transfer
graph (input: the band step at `img(tr)`; the intermediate lemma `Φ(P) ≥ k ⟹ Φ(tr) ≥ k` is `BAScostLL_macroB`), or (stage 1) a packed term of a
builder term `X` with `BAScostLL P.g X` (input). -/
theorem baShapeLL_macroB {T : BTStep}
    (h : ∀ P LT, T P LT → ∀ Q, (BAShape.macroB, Q) ∈ LT →
      (∃ p q, p ∈ lwSplit P.g.solid ∧ q ∈ lwSplit p.2 ∧ (p.1.σ = true ∧ p.1.circ = true) ∧ (q.1.σ = true ∧ q.1.circ = true) ∧
        P.g.sameAtom p.1.src q.1.dst = true ∧ P.g.sameAtom p.1.src p.1.dst = false ∧ P.g.sameAtom q.1.src q.1.dst = false ∧
        ∃ Q0 ∈ (P.g.BAScost_trB p q).partition, ∀ far k, locCostGeA far k (BAScost_pack P Q0) → locCostGeA far k Q) ∨
      (∃ X : BAScost_Term P, BAScostLL P.g X.X ∧ ∃ Q0 ∈ X.X.partition, Q = BAScost_pack P Q0)) :
    BAShapeLL BAShape.macroB T := by
  intro P LT hT Q hQ far k hk
  rcases h P LT hT Q hQ with ⟨p, q, hp, hq, hp1, hq1, hs, hw1, hw2, Q0, hQ0, hstep⟩ | ⟨X, hX, Q0, hQ0, rfl⟩
  · exact hstep far k (BAScost_locCostGeA_term P (P.g.BAScost_trB p q) far k
      (BAScostLL_macroB P.g p q hp hq hp1 hq1 hs hw1 hw2) hk Q0 hQ0)
  · exact BAScost_locCostGeA_term P X.X far k hX hk Q0 hQ0


/-! ## 3. Compiled instances at the witness graphs of `BAScost.lean` §14 -/

namespace BAScost2Inst

open BAScostInst

/-- the step relation of one `s1` step at `Γ*`: the packed terms of `G = Ǧ + M` on `BAGGOp_A1`, tagged `s1` -/
def ts1 : BTStep := fun P LT => P = baPG gs ∧
  LT = (BAGGOp_A1 gs ps qs).partition.map fun Q0 => (BAShape.s1, BAScost_pack (baPG gs) Q0)

/-- **`BAShapeLL s1`** at `ts1`: every hypothesis (membership of the pair in `lwSplit`, blue, circled, `hwf`) is discharged. -/
theorem ts1_shape : BAShapeLL BAShape.s1 ts1 := by
  refine baShapeLL_s1 ?_
  rintro P LT ⟨rfl, rfl⟩ Q hQ
  obtain ⟨Q0, hQ0, hQe⟩ := List.mem_map.1 hQ
  exact ⟨ps, qs, ps_mem, qs_mem, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, gs_wf1, gs_wf2, Q0, hQ0, (Prod.mk.inj hQe).2.symm⟩

/-- the invariant passes through the `s1` step: `Φ(Γ*) ≥ 0` (crude bound `n_W - |I| = 0`) gives `Φ ≥ 0` at every output -/
example (far : Bool) : ∀ Q0 ∈ (BAGGOp_A1 gs ps qs).partition, locCostGeA far 0 (BAScost_pack (baPG gs) Q0) := fun Q0 hQ0 =>
  ts1_shape (baPG gs) _ ⟨rfl, rfl⟩ (BAScost_pack (baPG gs) Q0) (List.mem_map.2 ⟨Q0, hQ0, rfl⟩) far 0 (BAScost_locCostGeA_crude far (baPG gs))

example : ((BAGGOp_A1 gs ps qs).partition).length = 1 := by
  rw [BAGraph.partition, List.length_map]
  decide

/-- the step relation of one `e1` step at `Γ*`: the packed terms of `G = Ǧ + M` on `lanlwT1` (`[x] ≠ [y]`: the extra output among them), tagged `e1` -/
def te1 : BTStep := fun P LT => P = baPG gs ∧
  LT = (BAGraph.lanlwT1 gs ps).partition.map fun Q0 => (BAShape.e1, BAScost_pack (baPG gs) Q0)

theorem te1_shape : BAShapeLL BAShape.e1 te1 := by
  refine baShapeLL_e1 ?_
  rintro P LT ⟨rfl, rfl⟩ Q hQ
  obtain ⟨Q0, hQ0, hQe⟩ := List.mem_map.1 hQ
  exact ⟨ps, ps_mem, ⟨rfl, rfl⟩, Q0, hQ0, (Prod.mk.inj hQe).2.symm⟩

example (far : Bool) : ∀ Q0 ∈ (BAGraph.lanlwT1 gs ps).partition, locCostGeA far 0 (BAScost_pack (baPG gs) Q0) := fun Q0 hQ0 =>
  te1_shape (baPG gs) _ ⟨rfl, rfl⟩ (BAScost_pack (baPG gs) Q0) (List.mem_map.2 ⟨Q0, hQ0, rfl⟩) far 0 (BAScost_locCostGeA_crude far (baPG gs))

/-- the step relation of one `e2` step: the packed terms of `G = Ǧ + M` on `lanlwT1` tagged `e2` (the local lemma of the builder term is the
input of `baShapeLL_e2`; here it is `BAScostLL_lanlwT1`) -/
def te2 : BTStep := fun P LT => P = baPG gs ∧
  LT = (BAGraph.lanlwT1 gs ps).partition.map fun Q0 => (BAShape.e2, BAScost_pack (baPG gs) Q0)

theorem te2_shape : BAShapeLL BAShape.e2 te2 := by
  refine baShapeLL_e2 ?_
  rintro P LT ⟨rfl, rfl⟩ Q hQ
  obtain ⟨Q0, hQ0, hQe⟩ := List.mem_map.1 hQ
  exact ⟨⟨Fin 1 ⊕ Fin 2, BAGraph.lanlwT1 gs ps⟩, BAScostLL_lanlwT1 gs ps ps_mem ⟨rfl, rfl⟩, Q0, hQ0, (Prod.mk.inj hQe).2.symm⟩

example (far : Bool) : ∀ Q0 ∈ (BAGraph.lanlwT1 gs ps).partition, locCostGeA far 0 (BAScost_pack (baPG gs) Q0) := fun Q0 hQ0 =>
  te2_shape (baPG gs) _ ⟨rfl, rfl⟩ (BAScost_pack (baPG gs) Q0) (List.mem_map.2 ⟨Q0, hQ0, rfl⟩) far 0 (BAScost_locCostGeA_crude far (baPG gs))

/-- the step relation of one macro step (a) at the within-atom witness `gw`: the packed terms of `G = Ǧ + M` on the transfer graph `tr`,
tagged `macroA` (the stage-2 step is the identity here) -/
def tma : BTStep := fun P LT => P = baPG gw ∧
  LT = (gw.BAScost_trA pw).partition.map fun Q0 => (BAShape.macroA, BAScost_pack (baPG gw) Q0)

theorem tma_shape : BAShapeLL BAShape.macroA tma := by
  refine baShapeLL_macroA ?_
  rintro P LT ⟨rfl, rfl⟩ Q hQ
  obtain ⟨Q0, hQ0, hQe⟩ := List.mem_map.1 hQ
  refine ⟨pw, pw_mem, ⟨rfl, rfl⟩, Q0, hQ0, fun far k h => ?_⟩
  rw [← (Prod.mk.inj hQe).2]
  exact h

/-- `Φ(gw) ≥ 0` (crude bound `n_W - |I| = 1 - 3`: `k = -4`) gives `Φ ≥ -4` at the packed transfer graph -/
example (far : Bool) : ∀ Q0 ∈ (gw.BAScost_trA pw).partition, locCostGeA far (-4) (BAScost_pack (baPG gw) Q0) := fun Q0 hQ0 =>
  tma_shape (baPG gw) _ ⟨rfl, rfl⟩ (BAScost_pack (baPG gw) Q0) (List.mem_map.2 ⟨Q0, hQ0, rfl⟩) far (-4)
    (BAScost_locCostGeA_crude far (baPG gw))

example : ((gw.BAScost_trA pw).partition).length = 1 := by
  rw [BAGraph.partition, List.length_map]
  decide

/-- the step relation of one macro step (b) at the split-pair witness `gc`: the packed terms of `G = Ǧ + M` on the transfer graph `tr`, tagged
`macroB` -/
def tmb : BTStep := fun P LT => P = baPG gc ∧
  LT = (gc.BAScost_trB pc qc).partition.map fun Q0 => (BAShape.macroB, BAScost_pack (baPG gc) Q0)

theorem tmb_shape : BAShapeLL BAShape.macroB tmb := by
  refine baShapeLL_macroB ?_
  rintro P LT ⟨rfl, rfl⟩ Q hQ
  obtain ⟨Q0, hQ0, hQe⟩ := List.mem_map.1 hQ
  refine Or.inl ⟨pc, qc, pc_mem, qc_mem, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, gc_same, gc_wf1, gc_wf2, Q0, hQ0, fun far k h => ?_⟩
  rw [← (Prod.mk.inj hQe).2]
  exact h

example (far : Bool) : ∀ Q0 ∈ (gc.BAScost_trB pc qc).partition, locCostGeA far (-4) (BAScost_pack (baPG gc) Q0) := fun Q0 hQ0 =>
  tmb_shape (baPG gc) _ ⟨rfl, rfl⟩ (BAScost_pack (baPG gc) Q0) (List.mem_map.2 ⟨Q0, hQ0, rfl⟩) far (-4)
    (BAScost_locCostGeA_crude far (baPG gc))

example : ((gc.BAScost_trB pc qc).partition).length = 1 := by
  rw [BAGraph.partition, List.length_map]
  decide

end BAScost2Inst

end RBM.Graph
