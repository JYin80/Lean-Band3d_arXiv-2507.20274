/-
Release check for T2252 (dispatcher V1, Tue Oct  6 03:42 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §74, §24, §64 (4),
§45 O2, §29, §20, §17, §16).  LW-12c: third of six tickets of `lem:Anp` (split table `docs/tickets/T2234.md:27`):
cases (I) and (II) of the induction step of `lem:Anp_key_gh` (`7_8:1152-1244`), the merged case pin
`AnpDetGhCaseI` (`Graph/AnpKey2.lean:171`).
Section 1: `#check` of every merged name the ticket cites (`Graph/AnpKey2` e362f4b, `Graph/AnpKey` e5b944a,
`Graph/LWVocab` 37db678, `Graph/ScalingOrder` 3c07bc8, `Graph/LWPins` 975f4ff, `Defs/Lattice` 51f1a17,
`Defs/Sizes` 0a873f1) and of the Mathlib names of the route.
Section 2: the target pin (namespace `RBM.Graph.T2252Check`; the prover's theorem `anpDetGhCaseI_holds` in
`RBM.Graph` is discharged by `@anpDetGhCaseI_holds`).
Section 3: the A1+B1 instance graph and the shapes of the compiled instances (Prop-valued, no proof obligations).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2252-check.lean`.
-/
import RBM3D.Graph.AnpKey2
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.GroupWithZero.Basic

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`, T2050, 37db678): nested graphs (section 3, `:296-373`)
#check @RBM.Graph.NV
#check @RBM.Graph.NEdge
#check @RBM.Graph.NGraph
#check @RBM.Graph.NGraph.WalkOK
#check @RBM.Graph.NGraph.IsNested
#check @RBM.Graph.NGraph.GhostOK
#check @RBM.Graph.NGraph.nSolid
#check @RBM.Graph.NGraph.noGhostPath
#check @RBM.Graph.NGraph.nngh
#check @RBM.Graph.NGraph.ordN
#check @RBM.Graph.NGraph.val
#check @RBM.Graph.figAux
#check @RBM.Graph.figAux_nested
-- `Graph/ScalingOrder` (3c07bc8): `ord c = nS + 2 (nW - nV)` (`:65`), the body of `ordN`
#check @RBM.Graph.ord

-- LW-12a (`Graph/AnpKey`, T2234, e5b944a): the deterministic `(adsuu22)`, the assembly, the lift
#check @RBM.Graph.AnpDetGhAt
#check @RBM.Graph.AnpDetGh
#check @RBM.Graph.AnpDetGhStep
#check @RBM.Graph.anpDetGh_zero
#check @RBM.Graph.anpDetGh_of_step
#check @RBM.Graph.lwAnpKeyGh_of_det
-- LW-12a lattice helpers (section `Lattice`)
#check @RBM.Graph.anpKey_zdistInf_sub_comm
#check @RBM.Graph.anpKey_zdistInf_tri
-- LW-12a A2 replacement (section `Ghostify`, `:364-643`): used twice on the fixed graph
#check @RBM.Graph.NGraph.ghostifyEs
#check @RBM.Graph.NGraph.ghostifyIdx
#check @RBM.Graph.NGraph.ghostify
#check @RBM.Graph.anpKey_gf_get
#check @RBM.Graph.anpKey_gf_u
#check @RBM.Graph.anpKey_gf_v
#check @RBM.Graph.anpKey_gf_ghost
#check @RBM.Graph.anpKey_gf_idx_inj
#check @RBM.Graph.anpKey_gf_path
#check @RBM.Graph.anpKey_ghostify_nested
#check @RBM.Graph.anpKey_ghostify_ghostOK
#check @RBM.Graph.anpKey_ghostify_nSolid
#check @RBM.Graph.anpKey_gf_noGhostPath_iff
#check @RBM.Graph.anpKey_ghostify_nngh
#check @RBM.Graph.anpKey_ghostOK_of_noGhost

-- LW-12b (`Graph/AnpKey2`, T2242, e362f4b): vocabulary (`:44-190`)
#check @RBM.Graph.NGraph.valOn
#check @RBM.Graph.NGraph.EndAt
#check @RBM.Graph.NGraph.IsA1
#check @RBM.Graph.NGraph.IsA2
#check @RBM.Graph.NGraph.IsB1
#check @RBM.Graph.NGraph.NoA2
#check @RBM.Graph.NGraph.anpKey2_decNoA2
#check @RBM.Graph.anpKey2_val_eq_valOn
#check @RBM.Graph.anpKey2_region
#check @RBM.Graph.anpKey2_regionOne
#check @RBM.Graph.anpKey2_fixLab
#check @RBM.Graph.AnpDetGhRegAt
#check @RBM.Graph.AnpIH
#check @RBM.Graph.AnpDetGhRegStep
#check @RBM.Graph.AnpCaseI
#check @RBM.Graph.AnpDetGhCaseI
#check @RBM.Graph.AnpDetGhCaseIII
#check @RBM.Graph.AnpDetGhCaseIV
-- LW-12b section 3 (half distance, ending edges) and the walk / edge-product lemmas (sections 4, A2)
#check @RBM.Graph.anpKey2_half
#check @RBM.Graph.anpKey2_reg_half
#check @RBM.Graph.anpKey2_noGhost_iff
#check @RBM.Graph.anpKey2_caseI_ne
#check @RBM.Graph.anpKey2_walkOK_iff
#check @RBM.Graph.anpKey2_endAt_ends
#check @RBM.Graph.anpKey2_ep
#check @RBM.Graph.anpKey2_ep_nonneg
#check @RBM.Graph.anpKey2_ep_ghostify
-- LW-12b vertex fixing (F1)-(F8) (`:1821`) and the step from the cases (`:1885`, `:1891`)
#check @RBM.Graph.anpKey2_fix
#check @RBM.Graph.anpDetGhStep_of_reg
#check @RBM.Graph.anpDetGhRegStep_of_cases
-- LW-12b instances (section 7)
#check @RBM.Graph.anpKey2_decGhostOK
#check @RBM.Graph.anpKey2_decCaseI
#check @RBM.Graph.anpKey2_figAuxGh
#check @RBM.Graph.anpKey2_figAux_ghostOK
#check @RBM.Graph.anpKey2_inst_figAuxGh
#check @RBM.Graph.anpKey2_inst_chain
#check @RBM.Graph.anpKey2_inst_fix

-- LW-P (`Graph/LWPins`, 975f4ff): the merged pin the chain ends in
#check @RBM.Gauss.Sizes.LWAnpKeyGh

-- `Defs/Lattice`, `Defs/Sizes`: the torus and its sup-distance
#check @RBM.Zd
#check @RBM.Gauss.zdistInf

-- Mathlib: the fixed vertex, fibres of `own`, products and exponents, `2xy ≤ x² + y²`
#check @Fin.insertNth
#check @Fin.insertNth_apply_same
#check @Finset.prod_fiberwise
#check @Finset.card_eq_sum_card_fiberwise
#check @Finset.mul_prod_erase
#check @Finset.prod_const
#check @Finset.prod_pow_eq_pow_sum
#check @Finset.sum_tsub_distrib
#check @Finset.prod_le_prod₀
#check @Finset.sum_le_sum_of_subset_of_nonneg
#check @Finset.sum_mul_sq_le_sq_mul_sq
#check @two_mul_le_add_sq
#check @zpow_add₀

/-! ## 2. The target of T2252 -/

namespace RBM.Graph.T2252Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- Target: cases (I)+(II) of the induction step of `lem:Anp_key_gh` (`7_8:1152-1244`), in every dimension, for the
merged case pin `AnpDetGhCaseI` (`Graph/AnpKey2.lean:171`) unchanged.  File name: `anpDetGhCaseI_holds`. -/
def AnpKey3CaseIHoldsPin : Prop := ∀ d : ℕ, AnpDetGhCaseI d

/-! ## 3. Instances (Prop-valued shapes, no proof obligations) -/

/-- `figAux` with the last edge of path 0 (`ℳ₂ y`, edge 4) made ghost: on `piMix` the ending edges at `ℳ₁` are B1
(path 0, edge 0) and A1 (path 1, edge 1); path 1 ends with an A1 edge at `ℳ₂`; no A2.  File name:
`anpKey3_figAuxMix`. -/
def figAuxMix : NGraph 2 2 where
  es := [⟨false, .inl (.inl 0), .inr 0⟩, ⟨false, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inr 1⟩,
         ⟨false, .inr 0, .inr 1⟩, ⟨true, .inr 1, .inl (.inr 0)⟩, ⟨false, .inr 1, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (2, .inr 1), (4, .inl (.inr 0))]
    else [(1, .inr 0), (3, .inr 1), (5, .inl (.inr 1))]

/-- The region pattern of instances (2), (3): `ℳ₁` closer to the `a`-ends, `ℳ₂` strictly closer to the `b`-ends. -/
def piMix : Fin 2 → Fin 2 → Bool := fun i _ => decide (i = 1)

/-- Instance (1): B1+B1 at `ℳ₁` (`figAuxGh`, `π ≡ false`). -/
example : Prop := AnpIH 3 2 → AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false)

/-- Instance (2): A1+A1 at `ℳ₁` (`figAux`, `piMix`). -/
example : Prop :=
  figAux.NoA2 piMix ∧ AnpCaseI figAux piMix ∧ (AnpIH 3 2 → AnpDetGhRegAt 3 figAux piMix)

/-- Instance (3): A1+B1 at `ℳ₁` (`figAuxMix`, `piMix`). -/
example : Prop :=
  figAuxMix.GhostOK ∧ figAuxMix.IsNested ∧ figAuxMix.NoA2 piMix ∧ AnpCaseI figAuxMix piMix ∧
    (AnpIH 3 2 → AnpDetGhRegAt 3 figAuxMix piMix)

/-- Instance (4): the chain with case (I) discharged. -/
example : Prop := AnpDetGhCaseIII 3 → AnpDetGhCaseIV 3 → LWAnpKeyGh 3

/-- Instance (5): the double ghostify at `figAuxGh` fixed at `ℳ₁` (`i₀ = 0`): `ord` and `n_ngh` as before. -/
example : Prop :=
  ∃ (p' : ℕ) (Γ'' : NGraph p' 1), Γ''.GhostOK ∧ Γ''.IsNested ∧
    Γ''.ordN = anpKey2_figAuxGh.ordN ∧ Γ''.nngh = anpKey2_figAuxGh.nngh

end RBM.Graph.T2252Check
