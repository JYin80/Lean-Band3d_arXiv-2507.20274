/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpTerm3
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWVocab
import RBM3D.Graph.ScalingOrder
import RBM3D.Graph.LWLvl1
import RBM3D.Defs.Semicircle
import RBM3D.Green.IBPPoly
import RBM3D.Induction.Defs

/-!
# T2307 (LW-14e-2 = T2265a) check file: merged names (section 1) and pin texts (section 2)

No proofs, no `sorry`, no `by`.  The probe definitions whose text contains a proof term (`partitionX`: field
`ext_surj := Δ.extMap_surj`; `pcomp`: field `ext_surj := Q.ext_surj.comp P.ext_surj`; `selClassical`: uses the
theorem `lwG5Cand_iff_nonempty`) are NOT here, and neither is anything depending on them (`PartitionXSpec`,
`RCand.kids`, `expand`, `expandRoot`, `LWExpandIdentity`, `lwStep`, `expand_eq_expandG`): their texts are
pinned in the ticket (`docs/tickets/T2307.md`, "Pinned texts not in the check file") as verbatim copies of
`RBM3D/Probe/T2288Cert.lean` (branch `t/T2288`) lines 128-141, 144-146, 171-207, compiled there.
-/

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## Section 1. Merged names used (`#check`, full namespaces) -/

-- `Graph/LWExpTerm3.lean` (20de014)
#check @RBM.Gauss.Sizes.LWG5Graph
#check @RBM.Gauss.Sizes.LWG5Data
#check @RBM.Gauss.Sizes.LWAttached
#check @RBM.Gauss.Sizes.LWG5Expand
#check @RBM.Gauss.Sizes.lwExpTerm3_Data_G
#check @RBM.Gauss.Sizes.lwExpTerm3_Data_M
-- `Graph/LWVocab.lean` (37db678)
#check @RBM.Graph.LGraph
#check @RBM.Graph.PGraph
#check @RBM.Graph.LGraph.val
#check @RBM.Graph.PGraph.val
#check @RBM.Graph.PGraph.val_of_factor
#check @RBM.Graph.PGraph.val_of_not
#check @RBM.Graph.LComb.val
#check @RBM.Graph.LGraph.merge
#check @RBM.Graph.LGraph.extMap
#check @RBM.Graph.LGraph.extMap_surj
#check @RBM.Graph.LGraph.mergeP
#check @RBM.Graph.LGraph.Consistent
#check @RBM.Graph.lwSplitLoops
#check @RBM.Graph.LGraph.splitWeights
#check @RBM.Graph.LGraph.val_splitWeights
#check @RBM.Graph.LGraph.mergeSplitP
#check @RBM.Graph.LGraph.partitionTerms
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.LGraph.val_eq_partition
#check @RBM.Graph.LGraph.partition_normal
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.molOf
#check @RBM.Graph.LGraph.nM
#check @RBM.Graph.LGraph.nW
#check @RBM.Graph.LGraph.scalingOrder
-- `Graph/LWGGExp.lean` (5c69cb4)
#check @RBM.Graph.oe2x_graph_E
#check @RBM.Graph.oe2xR1
#check @RBM.Graph.oe2xR1d
#check @RBM.Graph.oe2xR1_val
#check @RBM.Graph.oe2xR2
#check @RBM.Graph.oe2xR4
#check @RBM.Graph.oe2xR5
#check @RBM.Graph.oe2xR6
#check @RBM.Graph.oe2xR7
#check @RBM.Graph.oe2xR8
-- `Graph/LWWeightExp.lean` (975f4ff)
#check @RBM.Graph.owxT1
#check @RBM.Graph.lwWx_im_pos
#check @RBM.Graph.lwWx_mE_ne
#check @RBM.Graph.lwWx_flow
-- `Graph/LWStein.lean` (89f29cf)
#check @RBM.Graph.lwSplit
#check @RBM.Graph.lwSplus
#check @RBM.Graph.lwSplus_spec
-- `Graph/LWLvl1.lean` (c967b9c): `pcomp P Q` is definitionally `Q.lvl1Comp P.ext P.ext_surj`
#check @RBM.Graph.PGraph.lvl1Comp
#check @RBM.Graph.PGraph.lvl1Comp_val
-- `Green/IBPPoly.lean` (3b8c687)
#check @RBM.Green.gaussIBP
-- `Defs/Semicircle.lean` (fbc9870)
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.abs_lemE_lt_two
-- `Induction/Defs.lean` (instance (1): `|STflowE z0 0| < 2`)
#check @RBM.Gauss.InductionDefsInst.z0_im_pos

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Green

namespace T2307Check

/-! ## Section 2. Pin texts (the ticket's file states them in `namespace RBM.Gauss.Sizes`, without `Pin`) -/

/-! ### 2a. Vocabulary, verbatim from the probe (lines 55-71, 80-86) -/

/-- Copy of T2265's `LWJoinedPin` (`docs/tickets/checks/T2265-check.lean`, section 2). -/
def LWJoinedPin (P : PGraph (Fin 2)) : Prop :=
  P.ext 0 ≠ P.ext 1 ∧ P.g.molOf (Sum.inl (P.ext 0)) = P.g.molOf (Sum.inl (P.ext 1)) ∧
    P.g.nM = 0

/-- **Candidate** of a node: an internal vertex `x` with a blue uncircled non-loop out-edge `p.1` and a
blue uncircled non-loop in-edge `q.1`, in exactly the shape `oe2x_graph_E` (`LWGGExp.lean:1550`)
consumes (`hp`, `hp1`, `hq`, `hq1`, `hy`). -/
def LWG5CandPin (P : PGraph (Fin 2)) : Prop :=
  ∃ (x : P.I') (y y' : P.E' ⊕ P.I') (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))),
    p ∈ lwSplit P.g.solid ∧ q ∈ lwSplit p.2 ∧ y ≠ Sum.inr x ∧ y' ≠ Sum.inr x ∧
      p.1 = ⟨true, false, Sum.inr x, y⟩ ∧ q.1 = ⟨true, false, y', Sum.inr x⟩

/-- **Progress** at one node (supervisor 1102 §3): below the order target there is a candidate. -/
def LWG5ProgressPin (P : PGraph (Fin 2)) : Prop :=
  P.g.scalingOrder < (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) → LWG5CandPin P

/-- **Identity half** of T2265's `LWG5Expand'Pin` (T2265a): the expectation identity for a given list. -/
def LWG5IdentityPin (d : ℕ) (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool)
    (x y : Idx d (sz.L n) (sz.W n)),
    ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
      ((Ls k s).map fun q =>
        (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
          ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum

/-! ### 2b. Procedure data without proof terms, verbatim from the probe (lines 113-123, 148-160, 183) -/

section Procedure

variable {V : Type*} [DecidableEq V]

/-- `lwSplitLoops` with the exponents `(j, j')` of `m`, `m̄` in place of the coefficient. -/
def lwSplitLoopsXPin : List (SEdge V) → List ((ℕ × ℕ) × List (SEdge V))
  | [] => [((0, 0), [])]
  | e :: es => (lwSplitLoopsXPin es).flatMap fun r =>
      if e.src = e.dst ∧ e.circ = false then
        [(r.1, ⟨e.σ, true, e.src, e.dst⟩ :: r.2),
          ((if e.σ then (r.1.1 + 1, r.1.2) else (r.1.1, r.1.2 + 1)), r.2)]
      else [(r.1, e :: r.2)]

end Procedure

/-- **A candidate** of a packed graph, as data (the data of `LWG5Cand`). -/
structure RCandPin (P : PGraph (Fin 2)) where
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

/-- A selection rule: a candidate or `none`. -/
abbrev SelPin := (P : PGraph (Fin 2)) → Option (RCandPin P)

/-! ### 2c. The abstract step (new; for the LW engine, supervisor 1356 O6, DECISIONS §105 (2)) -/

/-- **The expansion along an abstract step** `st` on a carrier `X` (`none` = leaf), with fuel; the exponent
pairs add along a branch exactly as in the probe's `expand`. -/
def expandGPin {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) : ℕ → X → List ((ℕ × ℕ) × X)
  | 0, P => [((0, 0), P)]
  | n + 1, P =>
    match st P with
    | none => [((0, 0), P)]
    | some l => l.flatMap fun r => (expandGPin st n r.2).map fun t => ((r.1.1 + t.1.1, r.1.2 + t.1.2), t.2)

/-- **The induction along `expandG`**: an invariant `Inv` kept by every step and a valuation `Φ` that every step
preserves with a multiplicative weight `w` give, for every fuel, the invariant at every output and the identity
`Φ P = Σ w · Φ` over the outputs. -/
def ExpandGSumPin {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) (Inv : X → Prop) (Φ : X → ℂ)
    (w : ℕ × ℕ → ℂ) : Prop :=
  w (0, 0) = 1 → (∀ a b c e : ℕ, w (a + c, b + e) = w (a, b) * w (c, e)) →
    (∀ (P : X) (l : List ((ℕ × ℕ) × X)), Inv P → st P = some l →
      (∀ r ∈ l, Inv r.2) ∧ Φ P = (l.map fun r => w r.1 * Φ r.2).sum) →
    ∀ (n : ℕ) (P : X), Inv P →
      Φ P = ((expandGPin st n P).map fun t => w t.1 * Φ t.2).sum ∧ ∀ t ∈ expandGPin st n P, Inv t.2

end T2307Check

end RBM.Gauss.Sizes
