/-
Release check for T2216 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §45 O2, §47,
§55).  LW-10c4: property (6) of `lem:localregular` (`7_8:815-818`, proof `B:200-278`), fourth and last of four tickets
(DECISIONS §55; Fable report `docs/claude-team/fable/2026-10-05-localreg6-locallemma.md`, cited F).
Section 1: `#check` of every merged name the ticket cites (LW-10c3 `Graph/LocalRegular6c` = T2203, ed9c0f1; LW-10c2
`Graph/LocalRegular6b` = T2195, b43cb93; LW-10c1 `Graph/LocalRegular6a` = T2184, 2a42f07; LW-10b `Graph/LocalRegular2` =
T2151, 32d895b; the merged LW files below them) and of the Mathlib / core names of the route.
Section 2: the five c4 pins, copied verbatim from `docs/tickets/checks/T2184-check.lean:379-427` (section 4 of T2184's
check file; md5 of those 49 lines `2f779e1b5b85b0a29fe0650b0db9e00e`); here they sit in `RBM.Graph.T2216Check` with
`open RBM RBM.Graph`, so `LGraph.scost`, `PGraph.LocCostGe`, `lwSymmTwistG`, `LocStep`, ... resolve to the merged
definitions.
Section 3: Prop-valued examples (no proof obligations): the twist and frame transfers, the transfer through the dotted
edge partition, the ten new term decompositions of F §3 (the other seven are merged theorems, section 1), and the shapes
of the compiled instances.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2216-check.lean`.
-/
import RBM3D.Graph.LocalRegular6c

/-! ## 1. Merged names -/

-- LW-10c1 (`Graph/LocalRegular6a`, T2184): the pinned vocabulary, the cost API, Lemma B, the final step, the initial values
#check @RBM.Graph.lwHalfPat
#check @RBM.Graph.lwElem
#check @RBM.Graph.LGraph.halfPat
#check @RBM.Graph.LGraph.skept
#check @RBM.Graph.LGraph.sIntCls
#check @RBM.Graph.LGraph.sElemCls
#check @RBM.Graph.LGraph.scost
#check @RBM.Graph.LGraph.CircIffLoop
#check @RBM.Graph.LGraph.ScostLL
#check @RBM.Graph.PGraph.LocCostGe
#check @RBM.Graph.PGraph.LocReg6Inv
#check @RBM.Graph.lwPrimLoop
#check @RBM.Graph.lwPrimAddLoop
#check @RBM.Graph.lwPrimMoveLoop
#check @RBM.Graph.lwPrimMoveSC
#check @RBM.Graph.lwPrimMoveOut
#check @RBM.Graph.lwPrimDmove
#check @RBM.Graph.lwPrimContract
#check @RBM.Graph.localReg6a_halfPat_perm
#check @RBM.Graph.localReg6a_halfPat_map
#check @RBM.Graph.localReg6a_mem_skept
#check @RBM.Graph.localReg6a_scost_congr
#check @RBM.Graph.LGraph.scost_perm
#check @RBM.Graph.LGraph.scost_relabel
#check @RBM.Graph.LGraph.scost_le_of_lvl1Split
#check @RBM.Graph.LGraph.scost_partition_ge
#check @RBM.Graph.LGraph.scost_bot
#check @RBM.Graph.LGraph.nElem_eq_zero_of_locStd
#check @RBM.Graph.locReg6_of_locCostGe
#check @RBM.Graph.locReg6far_of_locCostGe
#check @RBM.Graph.fxyPowGraph_locCostGe
#check @RBM.Graph.fxyPowGraph_locReg6Inv
#check @RBM.Graph.localReg6a_fxy_circIffLoop
#check @RBM.Graph.localReg6a_inst_bot2
#check @RBM.Graph.localReg6a_inst_cost2
-- LW-10c2 (`Graph/LocalRegular6b`, T2195): the composition API, the c2 primitives, the merged term lemmas `T1`, `R2`
#check @RBM.Graph.scostLL_refl
#check @RBM.Graph.LGraph.ScostLL.trans
#check @RBM.Graph.LGraph.ScostLL.of_perm
#check @RBM.Graph.LGraph.ScostLL.of_relabel
#check @RBM.Graph.scostLL_loop
#check @RBM.Graph.scostLL_addLoop
#check @RBM.Graph.scostLL_moveLoop
#check @RBM.Graph.scostLL_contract
#check @RBM.Graph.localReg6b_inst_T1
#check @RBM.Graph.localReg6b_inst_R2
#check @RBM.Graph.localReg6b_phi
#check @RBM.Graph.localReg6b_inst_T2_all
#check @RBM.Graph.localReg6b_inst_transfer
#check @RBM.Graph.localReg6b_inst_s55
#check @RBM.Graph.localReg6b_instCyc
-- LW-10c3 (`Graph/LocalRegular6c`, T2203): the c3 primitives, the merged term lemmas `P3`, `P4`, `D`, `T3` (also external)
#check @RBM.Graph.scostLL_moveSC
#check @RBM.Graph.scostLL_moveOut
#check @RBM.Graph.scostLL_dmove
#check @RBM.Graph.localReg6c_inst_P3
#check @RBM.Graph.localReg6c_inst_P4
#check @RBM.Graph.localReg6c_inst_D
#check @RBM.Graph.localReg6c_inst_T3
#check @RBM.Graph.localReg6c_inst_ET3
-- LW-08a (`Graph/LWSymm`): twists, frames, the external-vertex weight terms, the forms of the 17 terms
#check @RBM.Graph.SEdge.conj
#check @RBM.Graph.SEdge.transpose
#check @RBM.Graph.LGraph.conj
#check @RBM.Graph.LGraph.transpose
#check @RBM.Graph.lwSymmTwistS
#check @RBM.Graph.lwSymmTwistG
#check @RBM.Graph.lwSymmTwistP
#check @RBM.Graph.lwSymmTwistS_invol
#check @RBM.Graph.lwSymmTwistG_invol
#check @RBM.Graph.lwSymmTwistG_solid
#check @RBM.Graph.lwSymmTwistS_circ
#check @RBM.Graph.lwSymmTwistS_with_circ
#check @RBM.Graph.lwSymmTwistS_loop
#check @RBM.Graph.lwSymmTwistS_eq
#check @RBM.Graph.lwSymm_lwSplit_map
#check @RBM.Graph.lwSymmUncirc
#check @RBM.Graph.lwSymmUncirc2
#check @RBM.Graph.lwSymmFrame
#check @RBM.Graph.lwSymmFrameP
#check @RBM.Graph.lwSymmFrame2
#check @RBM.Graph.lwSymmFrame2P
#check @RBM.Graph.lwSymmFrame2Q
#check @RBM.Graph.lwSymmFrame_solid
#check @RBM.Graph.lwSymmFrame2_solid
#check @RBM.Graph.lwSymmFrameP_fst
#check @RBM.Graph.owxET1
#check @RBM.Graph.owxET2
#check @RBM.Graph.owxET3
#check @RBM.Graph.owxET4
#check @RBM.Graph.owxET1_inr
#check @RBM.Graph.owxET3_inr
#check @RBM.Graph.lwSymmOwxT1
#check @RBM.Graph.lwSymmOwxT2
#check @RBM.Graph.lwSymmOwxT3
#check @RBM.Graph.lwSymmOwxT4
#check @RBM.Graph.lwSymmOe1xOwx
#check @RBM.Graph.lwSymmOe1xDs
#check @RBM.Graph.lwSymmOe2xR2
#check @RBM.Graph.lwSymmOe2xR3
#check @RBM.Graph.lwSymmOe2xR4
#check @RBM.Graph.lwSymmOe2xR5
#check @RBM.Graph.lwSymmOe2xR6
#check @RBM.Graph.lwSymmOe2xR7
#check @RBM.Graph.lwSymmOe2xR8
-- LW-04/05/06/07 (`Graph/LWStein`, `LWWeightExp`, `LWEdgeExp`, `LWGGExp`): splits, the term builder, the 17 terms in the frame
#check @RBM.Graph.lwSplit
#check @RBM.Graph.lwSplit_perm
#check @RBM.Graph.owxEmb
#check @RBM.Graph.LGraph.owxExt
#check @RBM.Graph.owxDE
#check @RBM.Graph.owxT1
#check @RBM.Graph.owxT2
#check @RBM.Graph.owxT3
#check @RBM.Graph.owxT4
#check @RBM.Graph.oe1xD
#check @RBM.Graph.oe1xP3
#check @RBM.Graph.oe1xP4
#check @RBM.Graph.oe1xP5
#check @RBM.Graph.oe1xP6
#check @RBM.Graph.oe1xDs
#check @RBM.Graph.oe2xR2
#check @RBM.Graph.oe2xR4
#check @RBM.Graph.oe2xR5
#check @RBM.Graph.oe2xR6
#check @RBM.Graph.oe2xR7
#check @RBM.Graph.oe2xR8
-- LW-03 (`Graph/LWVocab`): records, relabelling, normal graphs, the partition, the order
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.LGraph
#check @RBM.Graph.PGraph
#check @RBM.Graph.SEdge.map
#check @RBM.Graph.LGraph.relabel
#check @RBM.Graph.LGraph.pack
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.LGraph.partition_normal
#check @RBM.Graph.LGraph.scalingOrder
#check @RBM.Graph.p2Graph
-- LW-08 (`Graph/LWLvl1`): the weight split, the partition structure, the step, reachability, induction, the merged steps
#check @RBM.Graph.lvl1Split
#check @RBM.Graph.lvl1_part_struct
#check @RBM.Graph.PGraph.lvl1Comp
#check @RBM.Graph.lvl1WeightOuts0
#check @RBM.Graph.lvl1EdgeOuts0
#check @RBM.Graph.lvl1GGOuts0
#check @RBM.Graph.lvl1Pack
#check @RBM.Graph.LocStep
#check @RBM.Graph.Lvl1Reach
#check @RBM.Graph.lvl1_step_good
#check @RBM.Graph.lvl1_induction
#check @RBM.Graph.lvl1Cutoff
#check @RBM.Graph.lvl1ExP2p
#check @RBM.Graph.lvl1ExLoopExt
#check @RBM.Graph.lvl1ExLoopExtp
#check @RBM.Graph.lvl1ExDeg1
#check @RBM.Graph.lvl1ExDeg1p
#check @RBM.Graph.lvl1ExSame
#check @RBM.Graph.lvl1ExSamep
#check @RBM.Graph.lvl1ExSameq
#check @RBM.Graph.lvl1_inst_locStep_weight
#check @RBM.Graph.lvl1_inst_locStep_weightExt
#check @RBM.Graph.lvl1_inst_locStep_edge
#check @RBM.Graph.lvl1_inst_locStep_gg
#check @RBM.Graph.lvl1_inst_fail_deg1
#check @RBM.Graph.lvl1_inst_fail_same
#check @RBM.Graph.lvl1_inst_fail_loopExt
-- LW-10a (`Graph/LocalRegular`): the starting graph, the predicates (1)-(6)
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.fxyPowGraph_normal
#check @RBM.Graph.PGraph.LocReg1
#check @RBM.Graph.PGraph.LocReg2
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.PGraph.LocReg6
-- LW-10b (`Graph/LocalRegular2`): the assembly (1)-(5) that c4 extends, its induction pattern, its instances
#check @RBM.Graph.pathInv2_locStep
#check @RBM.Graph.fxyPowGraph_pathInv2
#check @RBM.Graph.lw_localregular_upto5
#check @RBM.Graph.localReg2_inst_step1
#check @RBM.Graph.localReg2_inst_expansion
-- the parameter of the merged instance steps; the downstream consumer of (6) (`7_8:945-948`)
#check @RBM.mE
#check @RBM.Gauss.Sizes.LWMoment
-- Mathlib / core: setoids, permutations and maps of lists, the relabelling equivalences of `localReg6b_phi`
#check @Setoid.comap
#check @Setoid.comap_rel
#check @Setoid.ker
#check @List.Perm.swap
#check @List.Perm.trans
#check @List.Perm.map
#check @List.Perm.append_left
#check @List.perm_middle
#check @List.map_map
#check @List.countP_map
#check @List.filter_map
#check @Equiv.sumAssoc
#check @Equiv.sumCongr
#check @finSumFinEquiv

/-! ## 2. The c4 pins (verbatim copy of `docs/tickets/checks/T2184-check.lean:379-427`) -/

noncomputable section

namespace RBM.Graph.T2216Check

open RBM RBM.Graph

/-- c4 [`LGraph.scost_twist`]: the twists `(c, t)` leave the cost unchanged. -/
def ScostTwistPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (c t : Bool) (Γ : LGraph E I)
    (s : Setoid (E ⊕ I)), LGraph.scost (lwSymmTwistG c t Γ) s = LGraph.scost Γ s

/-- c4 [`circIffLoop_locStep`]. -/
def CircIffLoopLocStepPin : Prop :=
  ∀ {E : Type} {m : ℂ} {P : PGraph E} {outs : List (PGraph E)}, LocStep m P outs → P.g.Normal →
    LGraph.CircIffLoop P.g → ∀ Q ∈ outs, LGraph.CircIffLoop Q.g

/-- c4 [`locCostGe_locStep`], the step lemma `Φ(Q') ≥ Φ(Q)` (Fable report §2). -/
def LocCostGeLocStepPin : Prop :=
  ∀ {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))}, LocStep m P outs → P.g.Normal →
    LGraph.CircIffLoop P.g → ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k P → ∀ Q ∈ outs, PGraph.LocCostGe far k Q

/-- c4 [`locReg6Inv_locStep`]. -/
def LocReg6InvLocStepPin : Prop :=
  ∀ {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (p : ℕ), LocStep m P outs →
    PGraph.LocReg6Inv p P → ∀ Q ∈ outs, PGraph.LocReg6Inv p Q

section Assembly

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- c4 [`lw_localregular`]: `lem:localregular` in full (`7_8:786-821`): the statement of the merged
`lw_localregular_upto5` (`LocalRegular2.lean:1857`) with the last conjunct extended by (6) `2p ≤ ord` for every output
and the far corollary `3p ≤ ord` when `x ≠ y` (DECISIONS §55). -/
def LwLocalRegularPin : Prop :=
  ∀ (p : ℕ) (m : ℂ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
        (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
      (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack Q ∧
        Q.g.Normal ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧
        (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW) ∧
      (∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
        (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
        (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
        (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : Fin 2 → Idx d (sz.L n) (sz.W n),
          ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
            (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
            (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) ∧
      (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg345 p ∧ Q.LocReg6 p ∧
        (Q.ext 0 ≠ Q.ext 1 → 3 * (p : ℤ) ≤ Q.g.scalingOrder))

end Assembly

/-! ## 3. Statement shapes (Prop-valued examples, no proof obligations) -/

-- (a) target 2 (a): the twist moves from the source to the term (`LGraph.scost_twist` on both sides; F §2 last paragraph)
example : Prop :=
  ∀ {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (c t : Bool) (Γ : LGraph E I) (T : LGraph E I'),
    LGraph.ScostLL (lwSymmTwistG c t Γ) T → LGraph.ScostLL Γ (lwSymmTwistG c t T)

-- (b) target 2 (b): the source graph up to `List.Perm` of its solid edges (`LGraph.scost_perm`)
example : Prop :=
  ∀ {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (Γ Γ' : LGraph E I) (T : LGraph E I'), Γ.solid.Perm Γ'.solid → Γ.waved.length = Γ'.waved.length →
      LGraph.ScostLL Γ T → LGraph.ScostLL Γ' T

-- (c) target 2 (c): the frame of Step 2 (`lwSymmFrame`: the selected edge uncircled, then twisted)
example : Prop :=
  ∀ {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (T : LGraph E I'),
    p ∈ lwSplit Γ.solid → p.1.circ = false → LGraph.ScostLL (lwSymmFrame c t Γ p) T →
      LGraph.ScostLL Γ (lwSymmTwistG c t T)

-- (d) target 2 (d): the frame of Step 3 (`lwSymmFrame2`: both selected edges uncircled, then twisted)
example : Prop :=
  ∀ {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (T : LGraph E I'),
    p ∈ lwSplit Γ.solid → q ∈ lwSplit p.2 → p.1.circ = false → q.1.circ = false →
      LGraph.ScostLL (lwSymmFrame2 c t Γ p q) T → LGraph.ScostLL Γ (lwSymmTwistG c t T)

-- (e) target 4 (a): the step from a term to the packed outputs of its partition (Lemma B + LL; the general form of the merged
-- `localReg6b_inst_transfer`, external vertices through `P.ext`)
example : Prop :=
  ∀ {I'' : Type} [Fintype I''] [DecidableEq I''] (m : ℂ) (P : PGraph (Fin 2)) (T : LGraph P.E' I'') (far : Bool) (k : ℤ),
    LGraph.ScostLL P.g T → PGraph.LocCostGe far k P →
      ∀ Q0 ∈ T.partition m, PGraph.LocCostGe far k (Q0.lvl1Comp P.ext P.ext_surj)

-- (f) target 4 (b): `CircIffLoop` of every partition term from "circled ⇒ loop" of the term (`lvl1_part_struct`, `lvl1Split`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (T : LGraph E I) (Q0 : PGraph E),
    (∀ e ∈ T.solid, e.circ = true → e.src = e.dst) → Q0 ∈ T.partition m → LGraph.CircIffLoop Q0.g

-- (g) target 3, `T1 = Loop(x)` at an arbitrary vertex (`owxET1`, `LWSymm.lean:589`; the merged `localReg6b_inst_T1` is the
-- internal case, used for `Oe1xOwx` and `R3`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I),
    LGraph.ScostLL Γ (owxET1 m Γ x)

-- (h) target 3, `T2 = MoveLoop(x) ∘ Loop(α)`, relabelled to `I ⊕ Fin 2` (`owxET2`, `LWSymm.lean:594`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : E ⊕ I),
    Γ.solid.Perm (⟨true, true, x, x⟩ :: p.2) → LGraph.ScostLL Γ (owxET2 m Γ p x)

-- (i) target 3, `T4 = MoveLoop(x) ∘ Dmove(α; lw_α, q)`, relabelled (`owxET4`, `LWSymm.lean:612`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), (q.1.src = q.1.dst ↔ q.1.circ = true) →
    Γ.solid.Perm (⟨true, true, x, x⟩ :: q.1 :: q.2) → LGraph.ScostLL Γ (owxET4 m Γ x q)

-- (j) target 3, `P5 = MoveOut(x; v, d) ∘ AddLoop(x, red)` (`oe1xP5`, `LWEdgeExp.lean:1084`; hypotheses as the merged
-- `localReg6c_inst_P3`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), Sum.inr x ≠ v → Sum.inr x ≠ q.1.dst →
    Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨false, false, Sum.inr x, q.1.dst⟩ :: q.2) →
      LGraph.ScostLL Γ (oe1xP5 m Γ x v q)

-- (k) target 3, `P6 = MoveSC(x; s, v) ∘ AddLoop(x, blue)` (`oe1xP6`, `LWEdgeExp.lean:1102`; hypotheses as `localReg6c_inst_P4`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), q.1.src ≠ Sum.inr x → Sum.inr x ≠ v →
    Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨true, false, q.1.src, Sum.inr x⟩ :: q.2) →
      LGraph.ScostLL Γ (oe1xP6 m Γ x v q)

-- (l) target 3, `R4 = MoveSC(x; y', y) ∘ Loop(α)`, relabelled (`oe2xR4`, `LWGGExp.lean:491`; hypotheses as `localReg6b_inst_R2`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I), y' ≠ Sum.inr x → Sum.inr x ≠ y →
    Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2) →
      LGraph.ScostLL Γ (oe2xR4 m Γ q x y y')

-- (m) target 3, `R5 = MoveSC(x; y', y) ∘ AddLoop(x, blue)` (`oe2xR5`, `LWGGExp.lean:500`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I), y' ≠ Sum.inr x → Sum.inr x ≠ y →
    Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2) →
      LGraph.ScostLL Γ (oe2xR5 m Γ q x y y')

-- (n) target 3, `R6 = Loop(x) ∘ MoveSC(x; y', y)`, relabelled (`oe2xR6`, `LWGGExp.lean:508`; the waved edge `α - β` of the
-- merged term is `x - β` in the composite: only `waved.length` enters `scost`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I), y' ≠ Sum.inr x → Sum.inr x ≠ y →
    Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2) →
      LGraph.ScostLL Γ (oe2xR6 m Γ q x y y')

-- (o) target 3, `R7 = Dmove(x; x → y, q')` after cancelling the removed and re-added `G_{y'x}` (`oe2xR7`, `LWGGExp.lean:518`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), Sum.inr x ≠ y →
    (q'.1.src = q'.1.dst ↔ q'.1.circ = true) →
    Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q'.1 :: q'.2) →
      LGraph.ScostLL Γ (oe2xR7 m Γ x y y' q')

-- (p) target 3, `R8 = MoveSC(x; y', y) ∘ Dmove(α; α → y, q')`, relabelled (`oe2xR8`, `LWGGExp.lean:529`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), y' ≠ Sum.inr x → Sum.inr x ≠ y →
    (q'.1.src = q'.1.dst ↔ q'.1.circ = true) →
    Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q'.1 :: q'.2) →
      LGraph.ScostLL Γ (oe2xR8 m Γ x y y' q')

-- instance (1): the twist `(true, true)` at `Γ_2`: the cost of the trivial setoid stays `6` (merged `localReg6a_inst_bot2`)
example : Prop := (lwSymmTwistG true true (fxyPowGraph 2)).scost ⊥ = 6

-- instance (2): `T2` at `p2Graph` (`Γ_2`), the light-weight of `β_0 = inr 1` (the term of the merged Step 1)
example : Prop := LGraph.ScostLL p2Graph (owxET2 (mE 0) p2Graph lvl1ExP2p (Sum.inr 1))

-- instance (3): Step 1 at `Γ_2` (merged `lvl1_inst_locStep_weight`): every output carries the invariant `LocReg6Inv 2`
example : Prop :=
  ∀ B ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false),
    B.LocReg6Inv 2

-- instance (4): Step 1 at the external vertex `a₀` with the conjugating selector (merged `lvl1_inst_locStep_weightExt`)
example : Prop :=
  ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExLoopExt.pack →
    ∀ B ∈ lvl1Pack lvl1ExLoopExt.pack
        (lvl1WeightOuts0 (mE 0) lvl1ExLoopExt lvl1ExLoopExtp (Sum.inl (0 : Fin 2)) true false),
      PGraph.LocCostGe far k B ∧ LGraph.CircIffLoop B.g

-- instance (5): Step 2 with the transposing selector (merged `lvl1_inst_locStep_edge`)
example : Prop :=
  ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExDeg1.pack →
    ∀ B ∈ lvl1Pack lvl1ExDeg1.pack
        (lvl1EdgeOuts0 (mE 0) lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true),
      PGraph.LocCostGe far k B ∧ LGraph.CircIffLoop B.g

-- instance (6): Step 3 at the SC vertex `α₀` of `lvl1ExSame` (merged `lvl1_inst_locStep_gg`)
example : Prop :=
  ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExSame.pack →
    ∀ B ∈ lvl1Pack lvl1ExSame.pack
        (lvl1GGOuts0 (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))
          false true),
      PGraph.LocCostGe far k B ∧ LGraph.CircIffLoop B.g

-- instance (7): `lw_localregular` at `p = 2` read through its last conjunct: every output is locally standard with
-- `4 ≤ ord`, and `6 ≤ ord` when its two external vertices are distinct
example : Prop :=
  ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs ++ errs, Q.g.Normal) ∧
    ∀ Q ∈ outs, Q.LocStd ∧ Q.LocReg6 2 ∧ (Q.ext 0 ≠ Q.ext 1 → (6 : ℤ) ≤ Q.g.scalingOrder)

end RBM.Graph.T2216Check

end
