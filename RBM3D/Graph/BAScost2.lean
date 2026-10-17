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

end RBM.Graph
