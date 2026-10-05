/-
Release check for T2203 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §45 O2, §47,
§55).  LW-10c3: property (6) of `lem:localregular` (`7_8:815-818`, proof `B:200-278`), third of four tickets (DECISIONS
§55; Fable report `docs/claude-team/fable/2026-10-05-localreg6-locallemma.md`, cited F).
Section 1: `#check` of every merged name the ticket cites (LW-10c2 `Graph/LocalRegular6b` = T2195, b43cb93; LW-10c1
`Graph/LocalRegular6a` = T2184, 2a42f07; the merged LW files below them) and of the Mathlib names of the route.
Section 2: the three c3 pins, copied verbatim from `docs/tickets/checks/T2184-check.lean:358-377` (section 4 of T2184's
check file; md5 of those 20 lines `7205e0241cb5f47d0a8efde27f93c5a5`); here they sit in `RBM.Graph.T2203Check` with
`open RBM RBM.Graph`, so `LGraph.ScostLL`, `lwPrimMoveSC`, ... resolve to the merged definitions of
`RBM3D/Graph/LocalRegular6a.lean`.
Section 3: two vocabulary maps (setoids written as `Setoid.ker` of a map, no proof) and Prop-valued examples (the statement
shapes of the compiled instances, the forced repair branches and the §55 consequence).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2203-check.lean`.
-/
import RBM3D.Graph.LocalRegular6b

/-! ## 1. Merged names -/

-- LW-10c1 (`Graph/LocalRegular6a`, T2184): the pinned vocabulary and the cost API
#check @RBM.Graph.lwHalfPat
#check @RBM.Graph.lwElem
#check @RBM.Graph.LGraph.skept
#check @RBM.Graph.LGraph.sIntCls
#check @RBM.Graph.LGraph.sElemCls
#check @RBM.Graph.LGraph.scost
#check @RBM.Graph.LGraph.CircIffLoop
#check @RBM.Graph.LGraph.ScostLL
#check @RBM.Graph.PGraph.LocCostGe
#check @RBM.Graph.lwPrimMoveSC
#check @RBM.Graph.lwPrimMoveOut
#check @RBM.Graph.lwPrimDmove
#check @RBM.Graph.lwPrimContract
#check @RBM.Graph.localReg6a_halfPat_append
#check @RBM.Graph.localReg6a_halfPat_perm
#check @RBM.Graph.localReg6a_mem_sIntCls
#check @RBM.Graph.localReg6a_qmap
#check @RBM.Graph.localReg6a_qmap_mk
#check @RBM.Graph.localReg6a_qmap_injective
#check @RBM.Graph.localReg6a_scost_drop
#check @RBM.Graph.localReg6a_sIntCls_bot_card
#check @RBM.Graph.localReg6a_sElemCls_bot_card
#check @RBM.Graph.LGraph.scost_perm
#check @RBM.Graph.LGraph.scost_relabel
#check @RBM.Graph.LGraph.scost_cons_loop_ge
#check @RBM.Graph.fxyPowGraph_locCostGe
#check @RBM.Graph.localReg6a_inst_bot2
#check @RBM.Graph.localReg6a_inst_cost2
-- LW-10c2 (`Graph/LocalRegular6b`, T2195): the composition API and the c2 primitives
#check @RBM.Graph.scostLL_refl
#check @RBM.Graph.LGraph.ScostLL.trans
#check @RBM.Graph.LGraph.ScostLL.of_perm
#check @RBM.Graph.LGraph.ScostLL.of_relabel
#check @RBM.Graph.scostLL_loop
#check @RBM.Graph.scostLL_addLoop
#check @RBM.Graph.scostLL_moveLoop
#check @RBM.Graph.scostLL_contract
-- LW-10c2: the class sum (F §4.1), the fresh vertex, the localisation
#check @RBM.Graph.scostLL_kept
#check @RBM.Graph.scostLL_clsPat
#check @RBM.Graph.scostLL_el
#check @RBM.Graph.scostLL_el_nonneg
#check @RBM.Graph.scostLL_el_le_one
#check @RBM.Graph.scostLL_el_zero
#check @RBM.Graph.scostLL_el_pair
#check @RBM.Graph.scostLL_el_pair_add
#check @RBM.Graph.scostLL_hin
#check @RBM.Graph.scostLL_hout
#check @RBM.Graph.scostLL_mem_kept
#check @RBM.Graph.scostLL_kept_append
#check @RBM.Graph.scostLL_kept_perm
#check @RBM.Graph.scostLL_kept_map
#check @RBM.Graph.scostLL_clsPat_append
#check @RBM.Graph.scostLL_clsPat_perm
#check @RBM.Graph.scostLL_clsPat_nil
#check @RBM.Graph.scostLL_clsPat_map
#check @RBM.Graph.scostLL_clsPat_map_alpha
#check @RBM.Graph.scostLL_clsPat_loop
#check @RBM.Graph.scostLL_clsPat_single_kept
#check @RBM.Graph.scostLL_clsPat_single_dropped
#check @RBM.Graph.scostLL_clsPat_zero_of_ends
#check @RBM.Graph.scostLL_halfPat_single
#check @RBM.Graph.scostLL_halfPat_zero
#check @RBM.Graph.scostLL_scost_eq
#check @RBM.Graph.scostLL_emb_cases
#check @RBM.Graph.scostLL_emb_ne_alpha
#check @RBM.Graph.scostLL_inl_ne_alpha
#check @RBM.Graph.scostLL_qmap_range
#check @RBM.Graph.scostLL_intCls_emb
#check @RBM.Graph.scostLL_sum_intCls_emb
#check @RBM.Graph.scostLL_fresh_scost
#check @RBM.Graph.scostLL_fresh_dropped
#check @RBM.Graph.scostLL_local_diff
#check @RBM.Graph.scostLL_local_diff_C
#check @RBM.Graph.scostLL_mk_mem_sIntCls
#check @RBM.Graph.scostLL_sum_single
#check @RBM.Graph.scostLL_sum_two
#check @RBM.Graph.scostLL_sum_support
-- LW-10c2: the pattern facts (F §4.2; `scostLL_elem_E3` is a tautology, T2195 audit O1: not to be cited as (E3))
#check @RBM.Graph.scostLL_elem_E0
#check @RBM.Graph.scostLL_elem_E1
#check @RBM.Graph.scostLL_elem_E5
#check @RBM.Graph.scostLL_elem_ne_zero
#check @RBM.Graph.scostLL_elem_E4col
#check @RBM.Graph.scostLL_elem_E4out
#check @RBM.Graph.scostLL_elem_E4in
#check @RBM.Graph.scostLL_elem_E6col
#check @RBM.Graph.scostLL_elem_E6out
#check @RBM.Graph.scostLL_elem_E6in
-- LW-10c2: the merge, the repair lemma (F §4.4), the split, the placement lemma (F §4.3)
#check @RBM.Graph.scostLL_merge
#check @RBM.Graph.scostLL_qmerge
#check @RBM.Graph.scostLL_qmerge_eq_iff
#check @RBM.Graph.scostLL_joined
#check @RBM.Graph.scostLL_merge_scost
#check @RBM.Graph.scostLL_repair
#check @RBM.Graph.scostLL_split
#check @RBM.Graph.scostLL_split_alone
#check @RBM.Graph.scostLL_split_of_alone
#check @RBM.Graph.scostLL_split_merge
#check @RBM.Graph.scostLL_split_comap
#check @RBM.Graph.scostLL_split_inl
#check @RBM.Graph.scostLL_placement_loop
#check @RBM.Graph.scostLL_placement_two
#check @RBM.Graph.scostLL_placement
-- LW-10c2: the c3 consumer instances (public theorems at full generality: T2195 instance (8)) and the instance data
#check @RBM.Graph.localReg6b_inst_moveSC_placement
#check @RBM.Graph.localReg6b_inst_moveOut_placement
#check @RBM.Graph.localReg6b_inst_dmoveBlue_placement
#check @RBM.Graph.localReg6b_inst_dmoveRed_placement
#check @RBM.Graph.localReg6b_inst_moveSC_k2
#check @RBM.Graph.localReg6b_inst_moveSC_Gamma2
#check @RBM.Graph.localReg6b_instS
#check @RBM.Graph.localReg6b_instCyc
#check @RBM.Graph.localReg6b_instCyc_bot
#check @RBM.Graph.localReg6b_inst_contractPerm
#check @RBM.Graph.localReg6b_inst_transfer
#check @RBM.Graph.localReg6b_inst_s55
#check @RBM.Graph.localReg6b_inst_R2
-- LW-03 (`Graph/LWVocab`): records, relabelling
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.LGraph
#check @RBM.Graph.SEdge.map
#check @RBM.Graph.LGraph.relabel
#check @RBM.Graph.LGraph.Normal
-- LW-05 (`Graph/LWWeightExp`): the vertex embedding, the term builder, the derivative edges, the weight terms `T3`, `T4`
#check @RBM.Graph.owxEmb
#check @RBM.Graph.LGraph.owxExt
#check @RBM.Graph.owxDE
#check @RBM.Graph.owxT3
#check @RBM.Graph.owxT4
-- LW-06 (`Graph/LWEdgeExp`): the edge terms `D`, `P3`-`P6` (`D`, `P3`, `P4` are single c3 primitives; `P5`, `P6` are c4's)
#check @RBM.Graph.oe1xD
#check @RBM.Graph.oe1xP3
#check @RBM.Graph.oe1xP4
#check @RBM.Graph.oe1xP5
#check @RBM.Graph.oe1xP6
-- LW-07 (`Graph/LWGGExp`): the `GG` terms `R4`-`R8` (composites; c4's)
#check @RBM.Graph.oe2xR4
#check @RBM.Graph.oe2xR5
#check @RBM.Graph.oe2xR6
#check @RBM.Graph.oe2xR7
#check @RBM.Graph.oe2xR8
-- LW-08a (`Graph/LWSymm`): the weight term `T3` at an arbitrary vertex, the twists (c4's)
#check @RBM.Graph.owxET3
#check @RBM.Graph.lwSymmTwistG
-- LW-10a (`Graph/LocalRegular`): the instance graph
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.localReg_fxyBlock
-- Mathlib / core: the setoid and quotient API, sums over classes, permutations
#check @Setoid.comap
#check @Setoid.comap_rel
#check @Setoid.ker
#check @Quotient.sound
#check @Quotient.exact
#check @Finset.sum_erase_add
#check @Finset.sum_image
#check @Finset.sum_union
#check @List.Perm.swap
#check @List.perm_middle
#check @Function.LeftInverse.surjective

/-! ## 2. The c3 pins (verbatim copy of `docs/tickets/checks/T2184-check.lean:358-377`) -/

noncomputable section

namespace RBM.Graph.T2203Check

open RBM RBM.Graph

/-- c3 [`scostLL_moveSC`]. -/
def ScostLLMoveSCPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I), u ≠ z → z ≠ v →
    Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest) →
      LGraph.ScostLL Γ (lwPrimMoveSC Γ rest z u v)

/-- c3 [`scostLL_moveOut`]. -/
def ScostLLMoveOutPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z v d : E ⊕ I), z ≠ v → z ≠ d →
    Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨false, false, z, d⟩ :: rest) →
      LGraph.ScostLL Γ (lwPrimMoveOut Γ rest z v d)

/-- c3 [`scostLL_dmove`]. -/
def ScostLLDmovePin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (cp : Bool) (q : SEdge (E ⊕ I)),
    (z = v ↔ cp = true) → (q.src = q.dst ↔ q.circ = true) →
    Γ.solid.Perm (⟨true, cp, z, v⟩ :: q :: rest) → LGraph.ScostLL Γ (lwPrimDmove Γ rest z v q)
/-! ## 3. Statement shapes (vocabulary maps; Prop-valued examples, no proof obligations) -/

/-- The setoid `{x, y, α}`, singletons otherwise, on the vertices of a `Γ_2` primitive with one fresh vertex. -/
def chkMapXYA : Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1) → ℕ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun i => i.1 + 1) (fun _ => 0))

/-- The setoid `{inr 1, α}`, singletons otherwise, on the vertices of an `instCyc` primitive (`LGraph (Fin 2) (Fin 2)`). -/
def chkMapCyc : Fin 2 ⊕ (Fin 2 ⊕ Fin 1) → ℕ :=
  Sum.elim (fun a => a.1 + 2) (Sum.elim (fun i => i.1) (fun _ => 1))

-- instance (1): `MoveSC(α_0; x, y)` at `Γ_2` (the `Perm` is the merged `localReg6b_inst_contractPerm`); `⊥`: `6 → 6`
example : Prop :=
  LGraph.ScostLL (fxyPowGraph 2)
    (lwPrimMoveSC (fxyPowGraph 2)
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1))

-- instance (1'): `k = 2` at `Γ_2` (`s' = {x, y, α}`, `U = {x, y}` external): `T.scost s' = 5`, the restriction `{x, y}` costs
-- `6` (not a witness), the merge `{x, y, α_0}` costs `5` (the repair branch is forced)
example : Prop :=
  (lwPrimMoveSC (fxyPowGraph 2)
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost (Setoid.ker chkMapXYA) = 5 ∧
    (fxyPowGraph 2).scost (Setoid.comap (owxEmb 1) (Setoid.ker chkMapXYA)) = 6 ∧
    (fxyPowGraph 2).scost (scostLL_merge (Setoid.comap (owxEmb 1) (Setoid.ker chkMapXYA)) (Sum.inl 0) (Sum.inr 0)) = 5

-- instance (2): `MoveSC(z; u, u)` at the 2-cycle `localReg6b_instCyc` (`z = inr 0`, `u = inr 1`): the collapse, forced repair
example : Prop :=
  LGraph.ScostLL localReg6b_instCyc (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1))

example : Prop :=
  (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1)).scost (Setoid.ker chkMapCyc) = -2 ∧
    ¬ localReg6b_instCyc.scost (Setoid.comap (owxEmb 1) (Setoid.ker chkMapCyc)) ≤
      (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1)).scost (Setoid.ker chkMapCyc)

-- instance (3): `MoveOut(x; α_0, α_1)` at `Γ_2` (`z = x` external; `⊥`: `6 → 6`)
example : Prop :=
  (fxyPowGraph 2).solid.Perm
      ((⟨true, false, Sum.inl 0, Sum.inr 0⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: ⟨false, false, Sum.inl 0, Sum.inr 2⟩ ::
        [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
          ⟨false, false, Sum.inr 2, Sum.inl 1⟩]) →
    LGraph.ScostLL (fxyPowGraph 2)
      (lwPrimMoveOut (fxyPowGraph 2)
        [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
          ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inl 0) (Sum.inr 0) (Sum.inr 2))

-- instance (4): `Dmove(β_0; lw_{β_0}, x → α_1)` at `Γ_2` (the `T3` shape, red `q`, `cp = true`; `⊥`: `6 → 6`)
example : Prop :=
  (fxyPowGraph 2).solid.Perm
      ((⟨true, true, Sum.inr 1, Sum.inr 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: ⟨false, false, Sum.inl 0, Sum.inr 2⟩ ::
        [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
          ⟨false, false, Sum.inr 2, Sum.inl 1⟩]) →
    LGraph.ScostLL (fxyPowGraph 2)
      (lwPrimDmove (fxyPowGraph 2)
        [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
          ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 1) (Sum.inr 1) ⟨false, false, Sum.inl 0, Sum.inr 2⟩)

-- instance (5): blue `Dmove(z; z → u, u → z)` at `localReg6b_instCyc` (`Z = B ≠ U` at `k = 2`): the collapse, forced repair;
-- the added `z → b` is the uncircled loop `inr 0 → inr 0` (F §3, the `G_{ww}` of `T3`)
example : Prop :=
  LGraph.ScostLL localReg6b_instCyc
    (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩)

example : Prop :=
  (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩).scost
      (Setoid.ker chkMapCyc) = -2 ∧
    ¬ localReg6b_instCyc.scost (Setoid.comap (owxEmb 1) (Setoid.ker chkMapCyc)) ≤
      (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩).scost
        (Setoid.ker chkMapCyc)

-- instance (6): the edge term `P3 = MoveOut(x; v, d)` (`oe1xP3`, `LWEdgeExp.lean:1093`), through `of_perm` (swap of the two
-- added edges)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), Sum.inr x ≠ v → Sum.inr x ≠ q.1.dst →
    Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨false, false, Sum.inr x, q.1.dst⟩ :: q.2) →
      LGraph.ScostLL Γ (oe1xP3 m Γ x v q)

-- instance (7): the edge term `P4 = MoveSC(x; s, v)` (`oe1xP4`, `LWEdgeExp.lean:1111`; equal solid lists)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), q.1.src ≠ Sum.inr x → Sum.inr x ≠ v →
    Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨true, false, q.1.src, Sum.inr x⟩ :: q.2) →
      LGraph.ScostLL Γ (oe1xP4 m Γ x v q)

-- instance (8): the edge term `D = Dmove(x; x → v, q)` (`oe1xD`, `LWEdgeExp.lean:606`; equal solid and waved lists)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), Sum.inr x ≠ v →
    (q.1.src = q.1.dst ↔ q.1.circ = true) → Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: q.1 :: q.2) →
      LGraph.ScostLL Γ (oe1xD m Γ x v q)

-- instance (9): the weight term `T3 = Dmove(w; lw_w, q)` (`owxT3`, `LWWeightExp.lean:677`) and its external-vertex form
-- (`owxET3`, `LWSymm.lean:603`, `x : E ⊕ I`)
example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), (q.1.src = q.1.dst ↔ q.1.circ = true) →
    Γ.solid.Perm (⟨true, true, Sum.inr x, Sum.inr x⟩ :: q.1 :: q.2) → LGraph.ScostLL Γ (owxT3 m Γ x q)

example : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))), (q.1.src = q.1.dst ↔ q.1.circ = true) →
    Γ.solid.Perm (⟨true, true, x, x⟩ :: q.1 :: q.2) → LGraph.ScostLL Γ (owxET3 m Γ x q)

-- instance (10): the §55 consequence at `Γ_2` for instance (1) (merged `localReg6b_inst_s55`): every merge costs `≥ 2p = 4`,
-- every far merge `≥ 3p = 6`
example : Prop :=
  (∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)),
      4 ≤ (lwPrimMoveSC (fxyPowGraph 2)
        [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
          ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost s) ∧
    (∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)), ¬ s (Sum.inl 0) (Sum.inl 1) →
      6 ≤ (lwPrimMoveSC (fxyPowGraph 2)
        [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
          ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost s)

end RBM.Graph.T2203Check

end
