/-
Release check for T2433 (dispatcher V3, Mon Oct 12 00:33 UTC 2026; DECISIONS §243).  BA-L L4e-C `BAG5Leaf`: the leaf half of the corrected size
lemma (W3 = C), the GG-with-context Lemma (supervisor 0951 L4-C5) and the form L4g consumes (L4-C7).  Section 1: merged names.
Section 2: the probe pins `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand` (`t/T2398:RBM3D/Probe/T2398Pins.lean:158-166`, bodies verbatim,
names prefixed `T2433_`) and Prop-valued target shapes.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2433-check.lean
-/
import RBM3D.Graph.BAExpandId
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAExpandWOrd
import RBM3D.Graph.BAExpand
import RBM3D.Graph.BAVocab
import RBM3D.BA.MFixedPoint
import RBM3D.Graph.LWExpSound
import RBM3D.Graph.LWExpTerm6
import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.LWExpTerm3

-- Section 1: merged names
-- L4d (T2419, `Graph/BAExpandId`)
#check @RBM.Graph.baG5Graph
#check @RBM.Graph.BAG5Identity
#check @RBM.Graph.BARCand
#check @RBM.Graph.BARCand.kids
#check @RBM.Graph.BARCand.kids_normal
#check @RBM.Graph.BARCand.kids_identity
#check @RBM.Graph.BASel
#check @RBM.Graph.BAstep
#check @RBM.Graph.BAexpand
#check @RBM.Graph.BAexpandRoot
#check @RBM.Graph.BAselClassical
#check @RBM.Graph.baRCand_nonempty_iff
#check @RBM.Graph.baExpandIdentity_holds
#check @RBM.Graph.BAExpandId_ggL2
#check @RBM.Graph.BAExpandId_ggL4
#check @RBM.Graph.BAExpandId_gg2r
#check @RBM.Graph.BAExpandId_outsOf
#check @RBM.Graph.baExpFrame_gg_red
#check @RBM.Graph.BAExpandIdInst.instP
#check @RBM.Graph.BAExpandIdInst.instCand
#check @RBM.Graph.BAExpandIdInst.instCand_sizes
#check @RBM.Graph.BAExpandIdInst.baG5Graph_partition_length
#check @RBM.Graph.BAExpandIdInst.baExpandId_inst_identity
#check @RBM.Graph.BAExpandInst.baSelf_zero
#check @RBM.BA.BASelf
-- L2c2 (T2410, `Graph/BAGGOp`) and L2c1 (`Graph/BAWeightOp`, `Graph/BAExpandWOrd`): the counters of the Lemma
#check @RBM.Graph.BAGraph.gg2
#check @RBM.Graph.BAGraph.gg4
#check @RBM.Graph.BAGraph.ext
#check @RBM.Graph.gg_counters
#check @RBM.Graph.gg_raw
#check @RBM.Graph.gg_scalingOrderG
#check @RBM.Graph.gg_mono
#check @RBM.Graph.BAGGOp_kappa
#check @RBM.Graph.BAGGOp_Mono
#check @RBM.Graph.BAWeightOp_circ
#check @RBM.Graph.lanlw_ord
-- vocabulary (`Graph/BAVocab`)
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAPGraph.scalingOrder
#check @RBM.Graph.BAGraph.atom
#check @RBM.Graph.BAGraph.mol
#check @RBM.Graph.BAGraph.nA
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.splitG
#check @RBM.Graph.BAGraph.packMerge
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.partition_normal
#check @RBM.Graph.BAGraph.partition_of_normal
-- the band's leaf half and its consumer (twins of the targets; L4-C7)
#check @RBM.Gauss.Sizes.LWG5LeafProps
#check @RBM.Gauss.Sizes.LWG5ExpandSplit
#check @RBM.Gauss.Sizes.LWG5Expand'
#check @RBM.Gauss.Sizes.lwG5LeafProps_holds
#check @RBM.Gauss.Sizes.lwG5Expand'_holds
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand'
#check @RBM.Gauss.Sizes.LwGraphPrecJoin
#check @RBM.Gauss.Sizes.LWAttached
#check @RBM.Gauss.Sizes.LWJoined
#check @RBM.Gauss.Sizes.LWG5Progress
#check @RBM.Gauss.Sizes.expandG
#check @RBM.Gauss.Sizes.expandG_sum

-- Section 2: the probe pins (bodies verbatim from `t/T2398:RBM3D/Probe/T2398Pins.lean:158-166`) and target shapes
noncomputable section

namespace RBM.Graph.T2433Check

/-- Probe 158-159 (`BAG5Tgt`): `ord ≥ 5`, or `ord ≥ 3` if `x`, `y` lie in one atom. -/
def T2433_BAG5Tgt (P : BAPGraph (Fin 2)) : Prop :=
  5 ≤ P.scalingOrder + (if P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1)) then 2 else 0)

/-- Probe 163 (`BAG5Leaf`): corrected target, `n_M ≤ 1`, `n_W ≥ 2`. -/
def T2433_BAG5Leaf (P : BAPGraph (Fin 2)) : Prop := T2433_BAG5Tgt P ∧ P.g.nM ≤ 1 ∧ 2 ≤ P.g.nW

/-- Probe 166 (`BAG5Expand`): every graph of the lists is a leaf. -/
def T2433_BAG5Expand (Ls : Bool → Bool → List (BAPGraph (Fin 2))) : Prop := ∀ k s, ∀ q ∈ Ls k s, T2433_BAG5Leaf q

/-- Target 3, shape: the leaf half at the root list of a selector and a fuel (the row's selector `BAselStar` and fuel `F`
replace `BAselClassical` and `2`, which only type-check the shape). -/
example : Prop := T2433_BAG5Expand (BAexpandRoot BAselClassical 2)

/-- Target 4, shape: the packaged form (twin of `LWG5ExpandSplit`, `LWExpSound.lean:50`; the leaf conjunct becomes
`BAG5LeafProps` of the probe step). -/
example : Prop := ∀ d : ℕ, ∃ Ls : Bool → Bool → List (BAPGraph (Fin 2)), T2433_BAG5Expand Ls ∧ BAG5Identity d Ls

end RBM.Graph.T2433Check

end
