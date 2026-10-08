/-
Release check for T2318 (dispatcher V1, Thu Oct  8 01:40 UTC 2026; CLAUDE.md §4 step 0).
Gate LW-14e-4 (Sound): `RBM3D/Graph/LWExpSound.lean` (new file), theorems `relInvariance`, `relKids`,
`belowOfSound`, `soundStep`, `soundRoot`, `lwG5LeafProps_holds`, `lwG5Expand'_holds`.
Section 1: merged names the proofs use, with exact namespaces (file:line on `main` e5f819c).
Section 2: the pinned definitions (verbatim probe text from t/T2288:RBM3D/Probe/T2288Cert.lean, lines
  73-78, 89-92, 94-104, 210-211, 563-569, 612-616, 622-627, 629-633) in the temporary namespace
  `RBM.Gauss.Sizes.T2318Check`; T2318 defines them in `RBM.Gauss.Sizes` (LWExpSound.lean).
  The merged `MNode.toP`, `Cand.toR` are in `RBM.Graph.LWCert` (LWExpSim.lean:99, :108), so `N.toP h` is
  field notation (DECISIONS §118).
Section 3: the two new statements of this ticket (`RelKids`, `BelowOfSound`; T2288 audit §8 obs. 2).
Section 4: the public theorem shapes as `_pin : Prop` (the probe's `Iff.rfl` theorems as Prop pins).
Section 5: Prop-valued example.
Statements and `#check` only: no proof, no tactic block, no `theorem`. Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2318-check.lean`.
-/
import RBM3D.Graph.LWExpSim
import RBM3D.Graph.LWExpCertS0
import RBM3D.Graph.LWExpCertS1

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## 1. Merged names -/

-- T2306 (LW-14e-1 Cert, 8096694): `RBM3D/Graph/LWExpCert.lean`, namespace `RBM.Graph.LWCert` (`:35`)
#check @RBM.Graph.LWCert.MNode
#check @RBM.Graph.LWCert.vi
#check @RBM.Graph.LWCert.unite
#check @RBM.Graph.LWCert.labsOf
#check @RBM.Graph.LWCert.repsOf
#check @RBM.Graph.LWCert.posOf
#check @RBM.Graph.LWCert.pairOf
#check @RBM.Graph.LWCert.mkV
#check @RBM.Graph.LWCert.cMerge
#check @RBM.Graph.LWCert.cPartition
#check @RBM.Graph.LWCert.Cand
#check @RBM.Graph.LWCert.cands
#check @RBM.Graph.LWCert.renum
#check @RBM.Graph.LWCert.fams
#check @RBM.Graph.LWCert.tgt
#check @RBM.Graph.LWCert.leaf
#check @RBM.Graph.LWCert.belowOf
#check @RBM.Graph.LWCert.childrenB
#check @RBM.Graph.LWCert.goodB
#check @RBM.Graph.LWCert.rootInfo
#check @RBM.Graph.LWCert.rootAt
#check @RBM.Graph.LWCert.kids
#check @RBM.Graph.LWCert.kidsOk
#check @RBM.Graph.LWCert.goodB_succ_of
#check @RBM.Graph.LWCert.root_FF_shape
#check @RBM.Graph.LWCert.root_FT_shape
#check @RBM.Graph.LWCert.lwCert_roots_below
-- T2306: `RBM3D/Graph/LWExpCertS0.lean` (`:277`), `LWExpCertS1.lean` (`:277`, `:297`), namespace `RBM.Graph.LWCert`
#check @RBM.Graph.LWCert.cert_FF
#check @RBM.Graph.LWCert.cert_FT
#check @RBM.Graph.LWCert.cert_all
-- T2311 (LW-14e-3 Sim, 7e7b3be): `RBM3D/Graph/LWExpSim.lean`; `MNode.toP` `:99`, `Cand.toR` `:108` in `RBM.Graph.LWCert`
#check @RBM.Graph.LWCert.MNode.toP
#check @RBM.Graph.LWCert.Cand.toR
-- T2311: the rest of `LWExpSim.lean` in namespace `RBM.Gauss.Sizes` (`:53`, `:114`)
#check @RBM.Gauss.Sizes.lwSplit_map
#check @RBM.Gauss.Sizes.cands_spec
#check @RBM.Gauss.Sizes.Rel
#check @RBM.Gauss.Sizes.Rel.scalingOrder_eq
#check @RBM.Gauss.Sizes.Rel.tgt_eq
#check @RBM.Gauss.Sizes.Rel.leaf_iff
#check @RBM.Gauss.Sizes.Rel.cand
#check @RBM.Gauss.Sizes.lwG5Cand_of_cands
#check @RBM.Gauss.Sizes.cPartitionX
#check @RBM.Gauss.Sizes.famsX
#check @RBM.Gauss.Sizes.fams_eq_famsX
#check @RBM.Gauss.Sizes.childrenX
#check @RBM.Gauss.Sizes.PartitionSim
#check @RBM.Gauss.Sizes.ChildrenSim
#check @RBM.Gauss.Sizes.partitionSim
#check @RBM.Gauss.Sizes.childrenSim
#check @RBM.Gauss.Sizes.rel_self
-- T2307 (LW-14e-2, 3c11598): `RBM3D/Graph/LWExpTerm5.lean`, namespace `RBM.Gauss.Sizes` (`:51`)
#check @RBM.Gauss.Sizes.LWJoined
#check @RBM.Gauss.Sizes.LWG5Cand
#check @RBM.Gauss.Sizes.LWG5Progress
#check @RBM.Gauss.Sizes.LWG5Identity
#check @RBM.Gauss.Sizes.lwSplitLoopsX
#check @RBM.Gauss.Sizes.partitionX
#check @RBM.Gauss.Sizes.PartitionXSpec
#check @RBM.Gauss.Sizes.pcomp
#check @RBM.Gauss.Sizes.RCand
#check @RBM.Gauss.Sizes.lwG5Cand_iff_nonempty
#check @RBM.Gauss.Sizes.RCand.kids
#check @RBM.Gauss.Sizes.Sel
#check @RBM.Gauss.Sizes.expand
#check @RBM.Gauss.Sizes.expandRoot
#check @RBM.Gauss.Sizes.LWExpandIdentity
#check @RBM.Gauss.Sizes.selClassical
#check @RBM.Gauss.Sizes.expandG
#check @RBM.Gauss.Sizes.ExpandGSum
#check @RBM.Gauss.Sizes.expandG_sum
#check @RBM.Gauss.Sizes.lwStep
#check @RBM.Gauss.Sizes.expand_eq_expandG
#check @RBM.Gauss.Sizes.lwSplitLoopsX_spec
#check @RBM.Gauss.Sizes.partitionX_spec
#check @RBM.Gauss.Sizes.val_eq_partitionX
#check @RBM.Gauss.Sizes.partitionX_normal
#check @RBM.Gauss.Sizes.RCand.kids_normal
#check @RBM.Gauss.Sizes.lwExpandIdentity_holds
#check @RBM.Gauss.LWInst.lwExpTerm5_inst_identity
-- LW-14c = T2255 (20de014): `RBM3D/Graph/LWExpTerm3.lean`, namespace `RBM.Gauss.Sizes` (`:48`)
#check @RBM.Gauss.Sizes.LWG5Graph
#check @RBM.Gauss.Sizes.LWG5Data
#check @RBM.Gauss.Sizes.LWAttached
#check @RBM.Gauss.Sizes.LWG5Expand
#check @RBM.Gauss.Sizes.LwExpG5'OfExpand
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand
-- LW-03 = T2050 (37db678): `RBM3D/Graph/LWVocab.lean`, namespace `RBM.Graph` (`:67`)
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.DEdge
#check @RBM.Graph.WEdge.val
#check @RBM.Graph.WEdge.map
#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.relabel
#check @RBM.Graph.LGraph.adj
#check @RBM.Graph.LGraph.mol
#check @RBM.Graph.LGraph.mem_mol_iff
#check @RBM.Graph.LGraph.molGraph
#check @RBM.Graph.LGraph.molOf
#check @RBM.Graph.LGraph.molOf_eq_iff
#check @RBM.Graph.LGraph.nS
#check @RBM.Graph.LGraph.nW
#check @RBM.Graph.LGraph.nV
#check @RBM.Graph.LGraph.nM
#check @RBM.Graph.LGraph.nM_eq_card
#check @RBM.Graph.LGraph.counters
#check @RBM.Graph.LGraph.scalingOrder
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.EqRel
#check @RBM.Graph.LGraph.eqSetoid
#check @RBM.Graph.LGraph.cls
#check @RBM.Graph.LGraph.IsExtCls
#check @RBM.Graph.LGraph.ExtCls
#check @RBM.Graph.LGraph.IntCls
#check @RBM.Graph.LGraph.vmap
#check @RBM.Graph.LGraph.merge
#check @RBM.Graph.LGraph.extMap
#check @RBM.Graph.LGraph.extMap_surj
#check @RBM.Graph.LGraph.dotChoices
#check @RBM.Graph.LGraph.withDots
#check @RBM.Graph.LGraph.Consistent
#check @RBM.Graph.LGraph.splitWeights
#check @RBM.Graph.LGraph.partitionTerms
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.LGraph.partition_normal
#check @RBM.Graph.LGraph.counters_relabel_equiv
#check @RBM.Graph.PGraph
#check @RBM.Graph.PGraph.val
#check @RBM.Graph.lwSplitLoops
-- `RBM3D/Graph/ScalingOrder.lean` (3c07bc8), namespace `RBM.Graph` (`:44`)
#check @RBM.Graph.Counters
#check @RBM.Graph.ord
-- LW-07 = T2120 (5c69cb4): `RBM3D/Graph/LWGGExp.lean`, namespace `RBM.Graph` (`:56`)
#check @RBM.Graph.oe2xR2
#check @RBM.Graph.oe2xR4
#check @RBM.Graph.oe2xR5
#check @RBM.Graph.oe2xR6
#check @RBM.Graph.oe2xR7
#check @RBM.Graph.oe2xR8
-- LW-05 = T2107 (975f4ff): `RBM3D/Graph/LWWeightExp.lean`, namespace `RBM.Graph` (`:51`)
#check @RBM.Graph.owxEmb
#check @RBM.Graph.LGraph.owxExt
#check @RBM.Graph.owxDE
#check @RBM.Graph.owxT1
-- LW-04 = T2060 (89f29cf): `RBM3D/Graph/LWStein.lean`, namespace `RBM.Graph` (`:82`)
#check @RBM.Graph.lwSplit
-- `RBM3D/Defs/Semicircle.lean` (`RBM.mE` `:38`), `RBM3D/Defs/Sizes.lean` (`RBM.Gauss.Idx` `:46`)
#check @RBM.mE
#check @RBM.Gauss.Idx

noncomputable section

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Graph.LWCert RBM.Green

namespace T2318Check

/-! ## 2. The pinned definitions (verbatim probe text; T2318 states them in `RBM.Gauss.Sizes` without the
namespace `T2318Check`) -/

/-- **Leaf half** of T2265's `LWG5Expand'Pin`: the six conjuncts for every member of the list (probe 73-78). -/
def LWG5LeafProps (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : Prop :=
  ∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttached q.2 ∧
    ((∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∨
      LWJoined q.2) ∧
    (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder

/-- T2265's `LWG5Expand'Pin d`, split (probe 89-92). -/
def LWG5ExpandSplit (d : ℕ) : Prop :=
  ∃ Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2)),
    LWG5LeafProps Ls ∧ LWG5Identity d Ls

/-- T2265's `LWG5Expand'Pin d` (`docs/tickets/checks/T2265-check.lean:197-207`), verbatim up to names
(probe 94-104). -/
def LWG5Expand' (d : ℕ) : Prop :=
  ∃ Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2)),
    (∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttached q.2 ∧
        ((∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∨ LWJoined q.2) ∧
        (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder) ∧
    ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool)
      (x y : Idx d (sz.L n) (sz.W n)),
      ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
        ((Ls k s).map fun q =>
          (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
            ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum

/-- **The final assembly** (probe 210-211): the pin, from the identity half for `selClassical` with fuel `4`
and the leaf half for its list. -/
def LWG5ExpandOfHalves : Prop :=
  LWExpandIdentity selClassical 4 → LWG5LeafProps (expandRoot selClassical 4) → ∀ d, LWG5Expand' d

/-- **The other invariance lemmas of `Rel` that the soundness proofs need** (probe 563-569): `Normal`, `n_M`,
`LWAttached`, the molecule statement, `LWJoined`, by transport along the equivalences `eE`, `eI`. -/
def RelInvariance : Prop :=
  ∀ (N : MNode) (hs : Function.Surjective N.ext) (P : PGraph (Fin 2)), Rel N P →
    (N.g.Normal ↔ P.g.Normal) ∧ P.g.nM = N.g.nM ∧
    (LWAttached P ↔ LWAttached (N.toP hs)) ∧
    ((∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b) ↔
      (∀ a b : (N.toP hs).E', (N.toP hs).g.molOf (Sum.inl a) = (N.toP hs).g.molOf (Sum.inl b) → a = b)) ∧
    (LWJoined P ↔ LWJoined (N.toP hs))

/-- The six conjuncts of `LWG5LeafProps` for one packed graph (probe 612-616). -/
def LeafOK (P : PGraph (Fin 2)) : Prop :=
  P.g.Normal ∧ P.g.nM ≤ 1 ∧ 2 ≤ P.g.nW ∧ LWAttached P ∧
    ((∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b) ∨ LWJoined P) ∧
    (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder

/-- **Soundness of the lite classification at a node** (probe 622-627; the flag of `childrenB`): if the flag holds,
every real child of the packed node at the candidate is a leaf satisfying the leaf properties or is related to a
below-target model child. -/
def SoundStep : Prop :=
  ∀ (N : MNode) (h : Function.Surjective N.ext) (c : Cand N.a N.b) (hc : c ∈ cands N.g), (childrenB N c).1 = true →
    ∀ Q ∈ (Cand.toR N h c hc).kids,
      ((if Q.2.ext 0 = Q.2.ext 1 then (4 : ℤ) else 5) ≤ Q.2.g.scalingOrder → LeafOK Q.2) ∧
      (¬ (if Q.2.ext 0 = Q.2.ext 1 then (4 : ℤ) else 5) ≤ Q.2.g.scalingOrder → ∃ M ∈ (childrenB N c).2, Rel M Q.2)

/-- **Soundness at the root** (probe 629-633; `k` is arbitrary: `Rel` ignores the waved colours). -/
def SoundRoot : Prop :=
  ∀ (k s : Bool), (rootInfo false s).1 = true → ∀ r ∈ partitionX (LWG5Graph k s),
    ((if r.2.ext 0 = r.2.ext 1 then (4 : ℤ) else 5) ≤ r.2.g.scalingOrder → LeafOK r.2) ∧
    (¬ (if r.2.ext 0 = r.2.ext 1 then (4 : ℤ) else 5) ≤ r.2.g.scalingOrder → ∃ M ∈ (rootInfo false s).2, Rel M r.2)

/-! ## 3. The two new statements of this ticket (T2288 audit §8 observation 2: the induction along `expand`
needs the transport of candidates and children along `Rel` at every node, not only at `N.toP h`) -/

/-- **Bridge 2 along `Rel`** (engine B): the real children of any packed graph related to a model node, at any of
its candidates, are list-wise the model children at some listed model candidate (the converse of `Rel.cand` and
the naturality of `RCand.kids` under a renaming of the vertices and a recolouring of the waved edges). -/
def RelKids : Prop :=
  ∀ (N : MNode) (P : PGraph (Fin 2)), Rel N P → ∀ c' : RCand P,
    ∃ c : Cand N.a N.b, c ∈ cands N.g ∧
      List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
        (childrenX N c) c'.kids

/-- **Soundness of the lite flag of `belowOf`** (L7, model level): under the flag, every model partition term that is a
leaf has the leaf properties in every related packed graph, and every term that is not a leaf is represented in the
below-target list up to `Rel`. -/
def BelowOfSound : Prop :=
  ∀ (a b : ℕ) (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)), Function.Surjective ext →
    (belowOf Δ ext).1 = true → ∀ r ∈ cPartitionX Δ ext,
      (leaf r.2 = true → ∀ Q : PGraph (Fin 2), Rel r.2 Q → LeafOK Q) ∧
      (leaf r.2 = false → ∃ M ∈ (belowOf Δ ext).2, ∀ Q : PGraph (Fin 2), Rel r.2 Q → Rel M Q)

/-! ## 4. Public theorem shapes (the probe's `Iff.rfl` theorems `lwG5ExpandSplit_iff` 106, `lwG5LeafProps_iff` 618
and the assembly `lwG5ExpandOfHalves` 213 as Prop pins) -/

def lwG5ExpandSplit_iff_pin : Prop := ∀ d : ℕ, LWG5ExpandSplit d ↔ LWG5Expand' d
def lwG5LeafProps_iff_pin : Prop :=
  ∀ Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2)), LWG5LeafProps Ls ↔ ∀ k s, ∀ q ∈ Ls k s, LeafOK q.2
def lwG5ExpandOfHalves_pin : Prop := LWG5ExpandOfHalves
def relInvariance_pin : Prop := RelInvariance
def relKids_pin : Prop := RelKids
def belowOfSound_pin : Prop := BelowOfSound
def soundStep_pin : Prop := SoundStep
def soundRoot_pin : Prop := SoundRoot
def lwG5LeafProps_holds_pin : Prop := LWG5LeafProps (expandRoot selClassical 4)
def lwG5Expand'_holds_pin : Prop := ∀ d : ℕ, LWG5Expand' d

/-! ## 5. Statement shapes at concrete merged data (the certificate side and the instance of the identity half) -/

example : Prop := relInvariance_pin ∧ relKids_pin ∧ belowOfSound_pin ∧ soundStep_pin ∧ soundRoot_pin ∧
  lwG5LeafProps_holds_pin ∧ lwG5Expand'_holds_pin
example : Prop := (∀ s, (rootInfo false s).1 = true ∧ (rootInfo false s).2.all (goodB 3) = true) →
  LWExpandIdentity selClassical 4 → LWG5Expand' 3
example : Prop := ∀ (h : Function.Surjective (rootAt false false 9).ext),
  Rel (rootAt false false 9) (MNode.toP (rootAt false false 9) h)

end T2318Check

end RBM.Gauss.Sizes

end
