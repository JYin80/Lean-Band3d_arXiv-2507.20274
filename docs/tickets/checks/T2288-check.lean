/-
T2288 (LW-14e-D, design/probe for the leaf half of LW-14e) check file: merged names (section 1) and the
pin texts the probe states verbatim (section 2: the split of `LWG5Expand'` of T2265 into a leaf half
and an identity half, and the progress predicate).  No proofs, no `sorry`, no `by`.
Compiles on `main` (f3e7c74) as is.
-/
import RBM3D.Graph.LWExpTerm3
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWVocab
import RBM3D.Graph.ScalingOrder
import RBM3D.Graph.LWSymm
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.AnpKey5
import RBM3D.Defs.Semicircle

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## Section 1. Merged names (namespaces read off the enclosing `namespace … end` blocks) -/

-- `Graph/LWExpTerm3.lean` (T2255, 20de014, `namespace RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.LWG5Graph
#check @RBM.Gauss.Sizes.LWG5Data
#check @RBM.Gauss.Sizes.LWAttached
#check @RBM.Gauss.Sizes.LWG5Expand
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand
#check @RBM.Gauss.Sizes.lwExpTerm3_T4pos
-- `Graph/LWExpTerm2.lean` (T2243, d6ebc39), `Graph/LWPins.lean` (975f4ff)
#check @RBM.Gauss.Sizes.LWExpG5'
#check @RBM.Gauss.Sizes.LWtermEXP

-- `Graph/LWVocab.lean` (T2050, 37db678, `namespace RBM.Graph`): the noncomputable partition
#check @RBM.Graph.LGraph
#check @RBM.Graph.PGraph
#check @RBM.Graph.PGraph.val
#check @RBM.Graph.LGraph.relabel
#check @RBM.Graph.LGraph.val_relabel_equiv
#check @RBM.Graph.LGraph.EqRel
#check @RBM.Graph.LGraph.Cls
#check @RBM.Graph.LGraph.vmap
#check @RBM.Graph.LGraph.merge
#check @RBM.Graph.LGraph.dotChoices
#check @RBM.Graph.LGraph.withDots
#check @RBM.Graph.LGraph.Consistent
#check @RBM.Graph.LGraph.partitionTerms
#check @RBM.Graph.LGraph.mergeSplitP
#check @RBM.Graph.LGraph.splitWeights
#check @RBM.Graph.lwSplitLoops
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.LGraph.val_eq_partition
#check @RBM.Graph.LGraph.partition_normal
#check @RBM.Graph.LGraph.mol
#check @RBM.Graph.LGraph.molOf
#check @RBM.Graph.LGraph.nW
#check @RBM.Graph.LGraph.nM
#check @RBM.Graph.LGraph.counters
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.scalingOrder
-- `Graph/ScalingOrder.lean` (3c07bc8), `Graph/LWStein.lean` (T2060, 89f29cf)
#check @RBM.Graph.ord
#check @RBM.Graph.lwSplit

-- `Graph/LWGGExp.lean` (T2120, 5c69cb4), `Graph/LWWeightExp.lean` (T2107, 975f4ff): the eight families
#check @RBM.Graph.oe2x_graph_E
#check @RBM.Graph.oe2xR1
#check @RBM.Graph.oe2xR2
#check @RBM.Graph.owxT1
#check @RBM.Graph.oe2xR4
#check @RBM.Graph.oe2xR5
#check @RBM.Graph.oe2xR6
#check @RBM.Graph.oe2xR7
#check @RBM.Graph.oe2xR8
#check @RBM.Graph.oe2xR2_ord
#check @RBM.Graph.oe2xR8_ord

-- `Graph/LWSymm.lean` (T2131, a871db4): the twisted families consumed by `lvl1_good_R*`
#check @RBM.Graph.lwSymmTwistS
#check @RBM.Graph.lwSymmTwistG
#check @RBM.Graph.lwSymmUncirc2
#check @RBM.Graph.lwSymmFrame2
#check @RBM.Graph.lwSymmOe2xR2
#check @RBM.Graph.lwSymmOe2xR7

-- `Graph/LWLvl1.lean` (T2128, c967b9c): one-step facts (not lower `ord`, not higher `n_M`)
#check @RBM.Graph.Lvl1Good
#check @RBM.Graph.lvl1_part_nM
#check @RBM.Graph.lvl1_good_R3
#check @RBM.Graph.lvl1_good_R2
#check @RBM.Graph.lvl1_good_R4
#check @RBM.Graph.lvl1_good_R5
#check @RBM.Graph.lvl1_good_R6
#check @RBM.Graph.lvl1_good_R8
#check @RBM.Graph.lvl1_good_R7
#check @RBM.Graph.LGraph.LocStd
#check @RBM.Graph.LocStep
#check @RBM.Graph.lvl1_exists_step

-- `Graph/AnpKey5.lean` (T2264, 1462fdb): the LW-12e certificate precedent (generic, not kernel-evaluated)
#check @RBM.Graph.AnpSumCert
#check @RBM.Graph.anpKey5_cert

-- `Defs/Semicircle.lean` (fbc9870)
#check @RBM.mE

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Green

namespace T2288Check

/-! ## Section 2. Pin texts (the probe states them verbatim, namespace `RBM.Probe.T2288`, no `Pin`) -/

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

/-- **Progress** at one node (supervisor 1102 §3): below the order target there is a candidate.
`stuckG` (T2265 report (b)) shows this is not implied by Amend 1's invariants. -/
def LWG5ProgressPin (P : PGraph (Fin 2)) : Prop :=
  P.g.scalingOrder < (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) → LWG5CandPin P

/-- **Leaf half** of T2265's `LWG5Expand'Pin`: the six conjuncts for every member of the list. -/
def LWG5LeafPropsPin (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : Prop :=
  ∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttached q.2 ∧
    ((∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∨
      LWJoinedPin q.2) ∧
    (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder

/-- **Identity half** of T2265's `LWG5Expand'Pin` (T2265a): the expectation identity for a given list. -/
def LWG5IdentityPin (d : ℕ) (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool)
    (x y : Idx d (sz.L n) (sz.W n)),
    ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
      ((Ls k s).map fun q =>
        (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
          ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum

/-- T2265's `LWG5Expand'Pin d`, split (the probe compiles `Iff.rfl` against the T2265 text). -/
def LWG5ExpandSplitPin (d : ℕ) : Prop :=
  ∃ Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2)),
    LWG5LeafPropsPin Ls ∧ LWG5IdentityPin d Ls

end T2288Check

end RBM.Gauss.Sizes
