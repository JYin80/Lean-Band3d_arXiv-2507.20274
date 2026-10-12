/-
Release check for T2447 (dispatcher V3, Mon Oct 12 10:15 UTC 2026; DECISIONS §259).  BA-L L3b4″ `BAShapeO2`: the O2 shape inputs of `BALocReg6` (supervisor 0948
O2R-C1): `BAShapeLL` for `e2`, `macroA`, `macroB` of `BAFrameStepTN`, and the hypothesis-free (6) along `BAReach`.
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2447_`; the 1b names them `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`,
`baShapeLL_macroB_tn`, `baLocReg6_holds`; content binding), the input forms of the merged packed lemmas at `BAFrameStepTN` (route (α), not
binding), and shapes (not binding) of the file-1 builder lemmas and of the instance data.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2447-check.lean
-/
import RBM3D.Graph.BAStepS
import RBM3D.Graph.BAScost
import RBM3D.Graph.BAScost2
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim3
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpand
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAVocab
import RBM3D.Graph.LocalRegular6a
import RBM3D.Graph.LocalRegular6b
import RBM3D.Graph.LocalRegular6c
import RBM3D.Graph.LocalRegular6d

set_option linter.style.longLine false
noncomputable section
open RBM RBM.Graph

/-! ## Part 1: merged names -/
-- L3b4′ (T2443, `Graph/BAStepS`): the tagged frame step, the closed form and its binder, the closed shapes, the band step, the bridge
#check @RBM.Graph.BAFrameStepTN
#check @RBM.Graph.BALocStepT
#check @RBM.Graph.BALocReg6
#check @RBM.Graph.baLocReg6_reach
#check @RBM.Graph.baShapeLL_s1_tn
#check @RBM.Graph.baShapeLL_e1_tn
#check @RBM.Graph.baShapeLL_twist
#check @RBM.Graph.BASimC'
#check @RBM.Graph.baSimC'_holds
#check @RBM.Graph.baStep_of_simC'
#check @RBM.Graph.baBridge_holds
#check @RBM.Graph.baEquivCost_holds
#check @RBM.Graph.baCostTwist_holds
#check @RBM.Graph.baNormal_locStepT
#check @RBM.Graph.baReach_bReach
#check @RBM.Graph.baInit_locReg6InvA
-- L3b3′ (T2426, `Graph/BAScost`, `BAScost2`): the cost vocabulary, the pins, the term lemmas, the tools, the packed forms, the witness graphs
#check @RBM.Graph.BAShape
#check @RBM.Graph.BTStep
#check @RBM.Graph.untag
#check @RBM.Graph.BAShapeLL
#check @RBM.Graph.BAScostLL
#check @RBM.Graph.BAScostLL.trans
#check @RBM.Graph.scostA
#check @RBM.Graph.locCostGeA
#check @RBM.Graph.locReg6InvA
#check @RBM.Graph.BAScostLL_splitG
#check @RBM.Graph.BAScostLL_E1
#check @RBM.Graph.BAScostLL_E2
#check @RBM.Graph.BAScostLL_of_band
#check @RBM.Graph.BAScostLL_S1
#check @RBM.Graph.BAScostLL_lanlwT1
#check @RBM.Graph.BAScostLL_macroA
#check @RBM.Graph.BAScostLL_macroB
#check @RBM.Graph.BAGraph.BAScost_trA
#check @RBM.Graph.BAGraph.BAScost_trB
#check @RBM.Graph.BAScost_pack
#check @RBM.Graph.BAScost_locCostGeA_term
#check @RBM.Graph.BAScost_scost_congr
#check @RBM.Graph.BAScost_Up
#check @RBM.Graph.BAScost_scost_le_of_Up
#check @RBM.Graph.BAScost_psi1
#check @RBM.Graph.BAScost_ker_psi1
#check @RBM.Graph.BAScost_rho2
#check @RBM.Graph.BAScost_vmap_ne_of_sameAtom
#check @RBM.Graph.BAScost_locCostGeA_crude
#check @RBM.Graph.BAScost_Term
#check @RBM.Graph.baShapeLL_of_terms
#check @RBM.Graph.baShapeLL_e2
#check @RBM.Graph.baShapeLL_macroA
#check @RBM.Graph.baShapeLL_macroB
#check @RBM.Graph.BAScostInst.gc
#check @RBM.Graph.BAScostInst.pc
#check @RBM.Graph.BAScostInst.qc
#check @RBM.Graph.BAScostInst.pc_mem
#check @RBM.Graph.BAScostInst.qc_mem
#check @RBM.Graph.BAScostInst.gc_same
#check @RBM.Graph.BAScostInst.gc_wf1
#check @RBM.Graph.BAScostInst.gc_wf2
-- R1 (T2423, `Graph/BASim`, `BASim3`): the tagged frame step and its five constructors, the tagged outputs, the matching, the witness steps
#check @RBM.Graph.BAFrameStepT
#check @RBM.Graph.BAFrameStepT.weight
#check @RBM.Graph.BAFrameStepT.within
#check @RBM.Graph.BAFrameStepT.edge
#check @RBM.Graph.BAFrameStepT.gg
#check @RBM.Graph.BAFrameStepT.ggSplit
#check @RBM.Graph.BAPGraph.outsT
#check @RBM.Graph.BAPGraph.withinOutsT
#check @RBM.Graph.BAPGraph.splitOutsT
#check @RBM.Graph.BAGraph.tagStd
#check @RBM.Graph.BAGraph.tagT1
#check @RBM.Graph.BAGraph.extraB
#check @RBM.Graph.BASim_mem_outsT
#check @RBM.Graph.baMatch_holds
#check @RBM.Graph.BASimInst.baPA
#check @RBM.Graph.BASimInst.baPB
#check @RBM.Graph.BASimInst.pB
#check @RBM.Graph.BASimInst.baPC
#check @RBM.Graph.BASimInst.pC
#check @RBM.Graph.BASimInst.qC
#check @RBM.Graph.BASimInst.hTA
#check @RBM.Graph.BASimInst.hTB
#check @RBM.Graph.BASimInst.hTC
#check @RBM.Graph.BASimInst.hTW
#check @RBM.Graph.BASimInst.hTE
#check @RBM.Graph.BASimInst.tag_exists
-- L2c1, L2c2 (T2407 `Graph/BAWeightOp`, T2410 `Graph/BAGGOp`) and `Graph/BAExpandW`: the builder terms
#check @RBM.Graph.BAGraph.ext
#check @RBM.Graph.bpS
#check @RBM.Graph.bpM
#check @RBM.Graph.bpW
#check @RBM.Graph.bpv
#check @RBM.Graph.BAGraph.lw2
#check @RBM.Graph.BAGraph.lw4
#check @RBM.Graph.BAGraph.gg2
#check @RBM.Graph.BAGraph.gg4
#check @RBM.Graph.BAGGOp_A1
#check @RBM.Graph.BAGGOp_A2
#check @RBM.Graph.BAGGOp_A3
#check @RBM.Graph.BAGGOp_A4
#check @RBM.Graph.BAGGOp_A5
#check @RBM.Graph.BAGGOp_AD
#check @RBM.Graph.BAGGOp_B1
#check @RBM.Graph.BAGGOp_B2
#check @RBM.Graph.BAGGOp_BD
#check @RBM.Graph.BAGGOp_gg2_eq
#check @RBM.Graph.BAGGOp_gg4_eq
#check @RBM.Graph.BAGraph.lanlwExt
#check @RBM.Graph.BAGraph.lanlwT1
#check @RBM.Graph.BAGraph.lanlwD
#check @RBM.Graph.lwSplit
#check @RBM.Graph.owxEmb
-- packed graphs, partition, atoms, reachability (`BAVocab`, `BAAtomic`, `BALvl1A`, `LocalRegular`)
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.splitG
#check @RBM.Graph.BAGraph.packMerge
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.partition_normal
#check @RBM.Graph.BAGraph.ofLGraph
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.atomSetoid
#check @RBM.Graph.promoteC
#check @RBM.Graph.BAGraph.img_normal
#check @RBM.Graph.BAGraph.sameAtom
#check @RBM.Graph.BAGraph.intAtom
#check @RBM.Graph.BAGraph.atEdges
#check @RBM.Graph.BAGraph.atCharge
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.baPG
#check @RBM.Graph.BAPGraph.scalingOrder
#check @RBM.Graph.BAReach
#check @RBM.Graph.BALvl1A_reach_refl
-- the band (`LocalRegular6a`–`6d`): the local lemma, its composition, the primitives, the term lemmas, the step
#check @RBM.Graph.LGraph.ScostLL
#check @RBM.Graph.LGraph.ScostLL.trans
#check @RBM.Graph.LGraph.ScostLL.of_perm
#check @RBM.Graph.LGraph.ScostLL.of_relabel
#check @RBM.Graph.scostLL_loop
#check @RBM.Graph.scostLL_addLoop
#check @RBM.Graph.scostLL_moveLoop
#check @RBM.Graph.scostLL_contract
#check @RBM.Graph.scostLL_moveSC
#check @RBM.Graph.scostLL_moveOut
#check @RBM.Graph.scostLL_dmove
#check @RBM.Graph.localReg6d_ll_perm
#check @RBM.Graph.localReg6d_ll_T1
#check @RBM.Graph.localReg6d_ll_T2
#check @RBM.Graph.localReg6d_ll_T4
#check @RBM.Graph.localReg6d_ll_P5
#check @RBM.Graph.localReg6d_ll_P6
#check @RBM.Graph.localReg6d_ll_R4
#check @RBM.Graph.localReg6d_ll_R5
#check @RBM.Graph.localReg6d_ll_R6
#check @RBM.Graph.localReg6d_ll_R7
#check @RBM.Graph.localReg6d_ll_R8
#check @RBM.Graph.localReg6c_inst_ET3
#check @RBM.Graph.localReg6c_inst_P3
#check @RBM.Graph.localReg6c_inst_P4
#check @RBM.Graph.localReg6c_inst_D
#check @RBM.Graph.localReg6b_inst_T1
#check @RBM.Graph.localReg6b_inst_R2
#check @RBM.Graph.localReg6d_locCostGe_term
#check @RBM.Graph.locCostGe_locStep
#check @RBM.Graph.LocStep

/-! ## Part 2: the target statements (Prop values; no proof) -/

/-- The binder of `BALocReg6` (`BAStepS:100`), verbatim: the three shape inputs of T2426 audit O2. -/
def T2447_Binder : Prop :=
  ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN

/-- Target 1 (`baShapeLL_e2_tn`, 0948 O2R-C1): the shape `e2` of the tagged frame step with normality. -/
def T2447_E2TN : Prop := BAShapeLL BAShape.e2 BAFrameStepTN

/-- Target 2 (`baShapeLL_macroA_tn`): the shape `macroA` (stage 2 of `within`). -/
def T2447_MacroATN : Prop := BAShapeLL BAShape.macroA BAFrameStepTN

/-- Target 3 (`baShapeLL_macroB_tn`): the shape `macroB` (stage 1 `d2`–`d4` and stage 2 of `ggSplit`). -/
def T2447_MacroBTN : Prop := BAShapeLL BAShape.macroB BAFrameStepTN

/-- Target 4 (`baLocReg6_holds`): the conclusion of `BALocReg6` (`BAStepS:98-104`) without the shape binder. -/
def T2447_LocReg6Holds : Prop :=
  ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition →
    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q →
      locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧
        (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))

/-- Route (α) of target 1 (not binding): the input of `baShapeLL_e2` (`BAScost2:96-100`) at `BAFrameStepTN`; file 1 gives `BAScostLL P.g X.X`. -/
def T2447_E2Input : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q, (BAShape.e2, Q) ∈ LT →
    ∃ X : BAScost_Term P, BAScostLL P.g X.X ∧ ∃ Q0 ∈ X.X.partition, Q = BAScost_pack P Q0

/-- Route (α) of target 2 (not binding): the input of `baShapeLL_macroA` (`BAScost2:106-108`) at `BAFrameStepTN` (stage 2 at the packed transfer graph). -/
def T2447_MacroAInput : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q, (BAShape.macroA, Q) ∈ LT →
    ∃ p, p ∈ lwSplit P.g.solid ∧ (p.1.σ = true ∧ p.1.circ = true) ∧
      ∃ Q0 ∈ (P.g.BAScost_trA p).partition, ∀ far k, locCostGeA far k (BAScost_pack P Q0) → locCostGeA far k Q

/-- Route (α) of target 3 (not binding): the input of `baShapeLL_macroB` (`BAScost2:117-121`) at `BAFrameStepTN` (disjunct 1: stage 2; disjunct 2:
stage 1, `d2`–`d4`). -/
def T2447_MacroBInput : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q, (BAShape.macroB, Q) ∈ LT →
    (∃ p q, p ∈ lwSplit P.g.solid ∧ q ∈ lwSplit p.2 ∧ (p.1.σ = true ∧ p.1.circ = true) ∧ (q.1.σ = true ∧ q.1.circ = true) ∧
      P.g.sameAtom p.1.src q.1.dst = true ∧ P.g.sameAtom p.1.src p.1.dst = false ∧ P.g.sameAtom q.1.src q.1.dst = false ∧
      ∃ Q0 ∈ (P.g.BAScost_trB p q).partition, ∀ far k, locCostGeA far k (BAScost_pack P Q0) → locCostGeA far k Q) ∨
    (∃ X : BAScost_Term P, BAScostLL P.g X.X ∧ ∃ Q0 ∈ X.X.partition, Q = BAScost_pack P Q0)

/-- Statement level: targets 1–3 give the binder; the binder and the merged closed form give target 4 (`baLocReg6_reach`); the route forms give
targets 1–3 (`baShapeLL_e2`, `baShapeLL_macroA`, `baShapeLL_macroB`). -/
example : Prop := T2447_E2TN → T2447_MacroATN → T2447_MacroBTN → T2447_Binder
example : Prop := BALocReg6 → T2447_Binder → T2447_LocReg6Holds
example : Prop := (T2447_E2Input → T2447_E2TN) ∧ (T2447_MacroAInput → T2447_MacroATN) ∧ (T2447_MacroBInput → T2447_MacroBTN)

/-- File-1 shapes (target 5; not binding: the 1a's table (a) fixes names and hypotheses): `BAScostLL Γ X` at the builder terms, for a general `Γ`,
under the constructor's hypotheses and normality only (O2R-C2 (d)).  `weight` (`BASim:139`): `lw2` (head, `lanlwD` tail) and `lw4` (head, tail). -/
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))),
    Γ.Normal → p ∈ lwSplit Γ.solid → (p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) →
      (∀ X ∈ Γ.lw2 p, BAScostLL Γ X) ∧ (∀ X ∈ Γ.lw4 p, BAScostLL Γ X)

/-- `within` (`BASim:141-143`): the head of stage 1 (`BASim:122`; the solid edges of the `lw2` head in the other order). -/
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))),
    Γ.Normal → p ∈ lwSplit Γ.solid → (p.1.σ = true ∧ p.1.circ = true ∧ p.1.src ≠ p.1.dst ∧ Γ.sameAtom p.1.src p.1.dst = true) →
      BAScostLL Γ (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0)])

/-- The derivative terms `lanlwD` (the tail of `lw2`, `within`, `edge`, `ggSplit`), with no atom hypothesis (as `BAScostLL_lanlwT1`). -/
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))),
    Γ.Normal → p ∈ lwSplit Γ.solid → (p.1.σ = true ∧ p.1.circ = true) → ∀ q ∈ lwSplit p.2, BAScostLL Γ (BAGraph.lanlwD Γ p q)

/-- `gg` (`BASim:149-154`): `gg2` (heads `BAGGOp_A1`–`A5`, tail `BAGGOp_AD`; `A1` is `BAScostLL_S1`) and `gg4` (heads `BAGGOp_B1`, `B2`, tail
`BAGGOp_BD`). -/
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I),
    Γ.Normal → p ∈ lwSplit Γ.solid → q ∈ lwSplit p.2 → (p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) →
    (p.1.src = Sum.inr x ∧ q.1.dst = Sum.inr x) → (∀ e ∈ Γ.solid, Γ.sameAtom e.src e.dst = false) → Γ.intAtom (Sum.inr x) = true →
    (∀ i : I, Γ.intAtom (Sum.inr i) = true → (Γ.atEdges (Sum.inr i)).length = 0 ∨
      ((Γ.atEdges (Sum.inr i)).length = 2 ∧ Γ.atCharge (Sum.inr i) = 0)) →
      (∀ X ∈ Γ.gg2 p q, BAScostLL Γ X) ∧ (∀ X ∈ Γ.gg4 p q, BAScostLL Γ X)

/-- Target 7 (i), (ii): the R1 witnesses as `BAFrameStepTN` steps (normality by `decide`; steps `BASimInst.hTB`, `hTC`), with the tags the targets read. -/
example : Prop :=
  BAFrameStepTN (baPG BASimInst.baPB) ((baPG BASimInst.baPB).withinOutsT BASimInst.pB) ∧
    BAShape.e2 ∈ ((baPG BASimInst.baPB).withinOutsT BASimInst.pB).map Prod.fst ∧
    BAShape.macroA ∈ ((baPG BASimInst.baPB).withinOutsT BASimInst.pB).map Prod.fst
example : Prop :=
  BAFrameStepTN (baPG BASimInst.baPC) ((baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0) ∧
    BAShape.e2 ∈ ((baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0).map Prod.fst ∧
    BAShape.macroB ∈ ((baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0).map Prod.fst
/-- Target 7 (iii): the macro (b) witness `BAScostInst.gc`, `pc`, `qc` (`BAScost:1400-1415`; `a = 2 ≠ a' = 3` in one atom) against R1's `P_C`
(dispatcher reading: the same literals). -/
example : Prop := BAScostInst.gc = BASimInst.baPC ∧ BAScostInst.pc = BASimInst.pC ∧ BAScostInst.qc = BASimInst.qC
/-- Target 7 (v): target 4 at `p = 2`, with no shape hypothesis. -/
example : Prop :=
  ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q → locReg6InvA 2 Q
