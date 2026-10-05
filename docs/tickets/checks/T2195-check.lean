/-
Release check for T2195 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §45 O2, §47,
§55).  LW-10c2: property (6) of `lem:localregular` (`7_8:815-818`, proof `B:200-278`), second of four tickets (DECISIONS
§55; Fable report `docs/claude-team/fable/2026-10-05-localreg6-locallemma.md`, cited F).
Section 1: `#check` of every merged name the ticket cites (LW-10c1 `Graph/LocalRegular6a` = T2184, 2a42f07, and the
merged LW files below it) and of the Mathlib names of the route.
Section 2: the seven c2 pins, copied verbatim from `docs/tickets/checks/T2184-check.lean:316-357` (section 4 of T2184's
check file); here they sit in `RBM.Graph.T2195Check` with `open RBM RBM.Graph`, so `LGraph.ScostLL`, `lwPrimLoop`, ...
resolve to the merged definitions of `RBM3D/Graph/LocalRegular6a.lean` (T2184 target 1, verbatim of its section 2).
Section 3: Prop-valued examples (the statement shapes of the compiled instances and of the §55 transfer).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2195-check.lean`.
-/
import RBM3D.Graph.LocalRegular6a

/-! ## 1. Merged names -/

-- LW-10c1 (`Graph/LocalRegular6a`, T2184): the pinned vocabulary (section 2 of T2184's check file, verbatim)
#check @RBM.Graph.lwHalfPat
#check @RBM.Graph.lwElem
#check @RBM.Graph.LGraph.halfPat
#check @RBM.Graph.LGraph.nElem
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
-- LW-10c1: the pattern and class API (public helpers, reusable)
#check @RBM.Graph.localReg6a_halfPat_congr
#check @RBM.Graph.localReg6a_halfPat_append
#check @RBM.Graph.localReg6a_halfPat_perm
#check @RBM.Graph.localReg6a_halfPat_map
#check @RBM.Graph.localReg6a_halfPat_cons_loop
#check @RBM.Graph.localReg6a_mem_skept
#check @RBM.Graph.localReg6a_mem_sIntCls
#check @RBM.Graph.localReg6a_mem_sElemCls
#check @RBM.Graph.localReg6a_sElemCls_subset
#check @RBM.Graph.localReg6a_qmap
#check @RBM.Graph.localReg6a_qmap_mk
#check @RBM.Graph.localReg6a_qmap_injective
#check @RBM.Graph.localReg6a_skept_relabel
#check @RBM.Graph.localReg6a_sIntCls_relabel
#check @RBM.Graph.localReg6a_sElemCls_relabel
#check @RBM.Graph.localReg6a_sElemCls_congr
#check @RBM.Graph.localReg6a_scost_congr
#check @RBM.Graph.localReg6a_scost_drop
#check @RBM.Graph.localReg6a_two_intCls_le
#check @RBM.Graph.localReg6a_halfPat_skept_singleton
#check @RBM.Graph.localReg6a_mk_bot_injective
-- LW-10c1: the cost API, Lemma A, Lemma B, the final step, the initial values (targets 2-6 of T2184)
#check @RBM.Graph.LGraph.scost_perm
#check @RBM.Graph.LGraph.scost_relabel
#check @RBM.Graph.LGraph.scost_cons_loop_ge
#check @RBM.Graph.LGraph.scost_le_of_lvl1Split
#check @RBM.Graph.LGraph.scost_partition_ge
#check @RBM.Graph.LGraph.scost_bot
#check @RBM.Graph.locReg6_of_locCostGe
#check @RBM.Graph.locReg6far_of_locCostGe
#check @RBM.Graph.fxyPowGraph_locCostGe
#check @RBM.Graph.fxyPowGraph_locReg6Inv
#check @RBM.Graph.localReg6a_fxy_circIffLoop
#check @RBM.Graph.localReg6a_inst_bot2
#check @RBM.Graph.localReg6a_instSplit0
-- LW-03 (`Graph/LWVocab`): records, relabelling, packed graphs
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.LGraph
#check @RBM.Graph.SEdge.map
#check @RBM.Graph.LGraph.relabel
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.PGraph
#check @RBM.Graph.LGraph.pack
-- LW-05 (`Graph/LWWeightExp`): the vertex embedding and the term builder the primitives are written with
#check @RBM.Graph.owxEmb
#check @RBM.Graph.LGraph.owxExt
#check @RBM.Graph.owxDE
#check @RBM.Graph.owxT1
#check @RBM.Graph.owxT2
-- LW-07 (`Graph/LWGGExp`), LW-08a (`Graph/LWSymm`): the GG terms supplied by c2's primitives alone (`R2`, `R3`)
#check @RBM.Graph.oe2xR2
#check @RBM.Graph.lwSymmOe2xR3
#check @RBM.Graph.lwSymmOe1xOwx
-- LW-08 (`Graph/LWLvl1`): the step the local lemma feeds (c4)
#check @RBM.Graph.LocStep
#check @RBM.Graph.lvl1_part_struct
-- LW-10a (`Graph/LocalRegular`): the instance graph
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.localReg_fxyBlock
#check @RBM.Graph.localReg_fxyAlpha
#check @RBM.Graph.localReg_fxyBeta
-- Mathlib / core: the setoid and quotient API, the sums over classes, the relabelling maps
#check @Setoid.comap
#check @Setoid.comap_rel
#check @Setoid.ker
#check @Quotient.map
#check @Quotient.sound
#check @Quotient.exact
#check @Finset.sum_erase_add
#check @Finset.card_image_of_injective
#check @Function.LeftInverse.surjective
#check @Function.Surjective.sumMap
#check @Equiv.sumAssoc
#check @finSumFinEquiv

/-! ## 2. The c2 pins (verbatim copy of `docs/tickets/checks/T2184-check.lean:316-357`) -/

noncomputable section

namespace RBM.Graph.T2195Check

open RBM RBM.Graph

/-- c2 [`LGraph.ScostLL.trans`], the composition lemma (Fable report §3). -/
def ScostLLTransPin : Prop :=
  ∀ {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (T : LGraph E I') (U : LGraph E I''),
    LGraph.ScostLL Γ T → LGraph.ScostLL T U → LGraph.ScostLL Γ U

/-- c2 [`LGraph.ScostLL.of_perm`]. -/
def ScostLLPermPin : Prop :=
  ∀ {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (Γ : LGraph E I) (T T' : LGraph E I'), T.solid.Perm T'.solid → T.waved.length = T'.waved.length →
    LGraph.ScostLL Γ T → LGraph.ScostLL Γ T'

/-- c2 [`LGraph.ScostLL.of_relabel`]. -/
def ScostLLRelabelPin : Prop :=
  ∀ {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (T : LGraph E I') (φ : E ⊕ I' → E ⊕ I''),
    Function.Surjective φ → (∀ a : E, φ (Sum.inl a) = Sum.inl a) → LGraph.ScostLL Γ T →
      LGraph.ScostLL Γ (T.relabel φ)

/-- c2 [`scostLL_loop`]. -/
def ScostLLLoopPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) (z : E ⊕ I) (col : Bool),
    LGraph.ScostLL Γ (lwPrimLoop Γ z col)

/-- c2 [`scostLL_addLoop`]. -/
def ScostLLAddLoopPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) (z : E ⊕ I) (col : Bool),
    LGraph.ScostLL Γ (lwPrimAddLoop Γ z col)

/-- c2 [`scostLL_moveLoop`]. -/
def ScostLLMoveLoopPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z : E ⊕ I) (col : Bool),
    Γ.solid.Perm (⟨col, true, z, z⟩ :: rest) → LGraph.ScostLL Γ (lwPrimMoveLoop Γ rest z col)

/-- c2 [`scostLL_contract`]. -/
def ScostLLContractPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I), u ≠ z → z ≠ v →
    Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest) →
      LGraph.ScostLL Γ (lwPrimContract Γ rest z u v)

/-! ## 3. Statement shapes (Prop-valued examples; no proof obligations) -/

-- instance (1): `Loop(x)` at `Γ_2` (the terms `Oe1xOwx`, `R3` in the frame; `T1` at an internal vertex)
example : Prop := LGraph.ScostLL (fxyPowGraph 2) (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true)

-- instance (2): `AddLoop(β_0, blue)` at `Γ_2` (tight at `⊥`: `6 → 6`)
example : Prop := LGraph.ScostLL (fxyPowGraph 2) (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true)

-- instance (3): `MoveLoop(β_0)` at `Γ_2`, the blue light-weight `⟨true, true, β_0, β_0⟩` is the head of the solid list
example : Prop :=
  (fxyPowGraph 2).solid.Perm (⟨true, true, Sum.inr 1, Sum.inr 1⟩ :: (fxyPowGraph 2).solid.tail) →
    LGraph.ScostLL (fxyPowGraph 2) (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)

-- instance (4): `Contract(z; u, u)` at the 2-cycle `z → u → z` (`z = inr 0`, `u = inr 1`): the collapse, `Δc = -2`
example : Prop :=
  LGraph.ScostLL
    ({ solid := [⟨true, false, Sum.inr 0, Sum.inr 1⟩, ⟨true, false, Sum.inr 1, Sum.inr 0⟩], waved := [], dotted := [],
        coeff := 1 } : LGraph (Fin 2) (Fin 2))
    (lwPrimContract
      ({ solid := [⟨true, false, Sum.inr 0, Sum.inr 1⟩, ⟨true, false, Sum.inr 1, Sum.inr 0⟩], waved := [], dotted := [],
          coeff := 1 } : LGraph (Fin 2) (Fin 2))
      [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1))

-- instance (5): a composite of two c2 primitives (`Loop(x)`, then `AddLoop` at the fresh vertex), through `trans`
example : Prop :=
  LGraph.ScostLL (fxyPowGraph 2)
    (lwPrimAddLoop (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true) (Sum.inr (Sum.inr 0)) false)

-- instance (6): the shape of `owxT2` (`MoveLoop(w)` then `Loop(α)`, relabelled to `I ⊕ Fin 2`), through `trans` and
-- `of_relabel`
example : Prop :=
  ∀ φ : Fin 2 ⊕ ((Fin (2 * 2) ⊕ Fin 1) ⊕ Fin 1) → Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 2),
    Function.Surjective φ → (∀ a : Fin 2, φ (Sum.inl a) = Sum.inl a) →
      LGraph.ScostLL (fxyPowGraph 2)
        ((lwPrimLoop (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)
          (Sum.inr (Sum.inr 0)) true).relabel φ)

-- the §55 transfer (all and far at once): `ScostLL Γ T` carries `k ≤ scost` from the setoids of `Γ` to those of `T`,
-- with no hypothesis restricting to far setoids (c4's `locCostGe_locStep` uses it for every output)
example : Prop :=
  ∀ {I I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (Γ : LGraph (Fin 2) I)
    (T : LGraph (Fin 2) I') (far : Bool) (k : ℤ), LGraph.ScostLL Γ T →
    (∀ s₀ : Setoid (Fin 2 ⊕ I), (far = true → ¬ s₀ (Sum.inl 0) (Sum.inl 1)) → k ≤ LGraph.scost Γ s₀) →
      ∀ s : Setoid (Fin 2 ⊕ I'), (far = true → ¬ s (Sum.inl 0) (Sum.inl 1)) → k ≤ LGraph.scost T s

end RBM.Graph.T2195Check

end
