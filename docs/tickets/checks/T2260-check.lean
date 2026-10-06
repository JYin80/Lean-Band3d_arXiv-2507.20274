/-
Release check for T2260 (dispatcher V1, Tue Oct  6 05:16 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §74, §24, §64 (4),
§45 O2, §29, §20, §17, §16).  LW-12d: fourth of six tickets of `lem:Anp` (split table `docs/tickets/T2234.md:27`):
case (III) of the induction step of `lem:Anp_key_gh` (`7_8:1245-1348`), the merged case pin `AnpDetGhCaseIII`
(`Graph/AnpKey2.lean:177`).
Section 1: `#check` of every merged name the ticket cites (`Graph/AnpKey3` 8aa37bf, `Graph/AnpKey2` e362f4b,
`Graph/AnpKey` e5b944a, `Graph/LWVocab` 37db678, `Graph/LWPins` 975f4ff, `Defs/Lattice` 51f1a17, `Defs/Sizes`
0a873f1) and of the Mathlib names of the route; namespace of each from its enclosing `namespace … end` block.
Section 2: the target pin and the intermediate pins (namespace `RBM.Graph.T2260Check`; the prover's theorems in
`RBM.Graph`, names in the docstrings, each discharged by `@name`).
Section 3: the case-(III)-only instance graph `figLoop` (the self-loop configuration of T2242's note (d)) and the
shapes of the compiled instances (Prop-valued, no proof obligations).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2260-check.lean`.
-/
import RBM3D.Graph.AnpKey3
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Basic

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`, T2050, 37db678): nested graphs (`:296-373`)
#check @RBM.Graph.NV
#check @RBM.Graph.NEdge
#check @RBM.Graph.NGraph
#check @RBM.Graph.NGraph.WalkOK
#check @RBM.Graph.NGraph.Visits
#check @RBM.Graph.NGraph.IsNested
#check @RBM.Graph.NGraph.GhostOK
#check @RBM.Graph.NGraph.nSolid
#check @RBM.Graph.NGraph.noGhostPath
#check @RBM.Graph.NGraph.nngh
#check @RBM.Graph.NGraph.ordN
#check @RBM.Graph.NGraph.val
-- `Graph/ScalingOrder` (3c07bc8): `ord c = nS + 2 (nW - nV)`, the body of `ordN`
#check @RBM.Graph.ord

-- LW-12a (`Graph/AnpKey`, T2234, e5b944a): the deterministic `(adsuu22)`, assembly, lift (`:41`, `:649`, `:689`)
#check @RBM.Graph.AnpDetGhAt
#check @RBM.Graph.AnpDetGhStep
#check @RBM.Graph.anpDetGh_of_step
#check @RBM.Graph.lwAnpKeyGh_of_det
#check @RBM.Graph.anpKey_zdistInf_tri
-- LW-12a A2 replacement (section `Ghostify`, `:364-643`)
#check @RBM.Graph.NGraph.ghostifyIdx
#check @RBM.Graph.NGraph.ghostify
#check @RBM.Graph.anpKey_gf_u
#check @RBM.Graph.anpKey_gf_v
#check @RBM.Graph.anpKey_gf_ghost'
#check @RBM.Graph.anpKey_gf_path
#check @RBM.Graph.anpKey_ghostify_nested
#check @RBM.Graph.anpKey_ghostify_ghostOK
#check @RBM.Graph.anpKey_ghostify_nSolid
#check @RBM.Graph.anpKey_gf_noGhostPath_iff

-- LW-12b (`Graph/AnpKey2`, T2242, e362f4b): vocabulary and case pins (`:44-190`)
#check @RBM.Graph.NGraph.valOn
#check @RBM.Graph.NGraph.EndAt
#check @RBM.Graph.NGraph.IsB1
#check @RBM.Graph.NGraph.IsB2
#check @RBM.Graph.NGraph.NoA2
#check @RBM.Graph.NGraph.degS
#check @RBM.Graph.anpKey2_region
#check @RBM.Graph.anpKey2_regionOne
#check @RBM.Graph.anpKey2_fixLab
#check @RBM.Graph.AnpDetGhRegAt
#check @RBM.Graph.AnpIH
#check @RBM.Graph.AnpCaseI
#check @RBM.Graph.AnpCaseIII
#check @RBM.Graph.AnpDetGhCaseIII
#check @RBM.Graph.AnpDetGhCaseIV
-- LW-12b walk / edge-product lemmas (sections 3, Chain, A2)
#check @RBM.Graph.anpKey2_noGhost_iff
#check @RBM.Graph.anpKey2_caseI_ne
#check @RBM.Graph.anpKey2_walkOK_iff
#check @RBM.Graph.anpKey2_endAt_ends
#check @RBM.Graph.anpKey2_ep
#check @RBM.Graph.anpKey2_ep_nonneg
#check @RBM.Graph.anpKey2_ep_ghostify
-- LW-12b segments and the explicit fixed graph (sections Seg, Fix, `:662-1880`)
#check @RBM.Graph.anpKey2_seg_head
#check @RBM.Graph.anpKey2_seg_succ_pos
#check @RBM.Graph.anpKey2_seg_snoc
#check @RBM.Graph.anpKey2_K
#check @RBM.Graph.anpKey2_Seg
#check @RBM.Graph.anpKey2_P
#check @RBM.Graph.anpKey2_steps
#check @RBM.Graph.anpKey2_ea
#check @RBM.Graph.anpKey2_eb
#check @RBM.Graph.anpKey2_own
#check @RBM.Graph.anpKey2_fixV
#check @RBM.Graph.anpKey2_em
#check @RBM.Graph.anpKey2_tgt_first
#check @RBM.Graph.anpKey2_tgt_last
#check @RBM.Graph.anpKey2_lab
#check @RBM.Graph.anpKey2_fixV_path
#check @RBM.Graph.anpKey2_fixV_edge
#check @RBM.Graph.anpKey2_steps_arrival
#check @RBM.Graph.anpKey2_ghost_unique
#check @RBM.Graph.anpKey2_fixV_nested
#check @RBM.Graph.anpKey2_fixV_ghostOK
#check @RBM.Graph.anpKey2_fixV_value
#check @RBM.Graph.anpKey2_fixV_noGhost1
#check @RBM.Graph.anpKey2_fixV_noGhost2
#check @RBM.Graph.anpKey2_fixV_nSolid
#check @RBM.Graph.anpKey2_fixV_end
#check @RBM.Graph.anpKey2_exists_s₀
#check @RBM.Graph.anpKey2_ea_unique
#check @RBM.Graph.anpKey2_eb_unique
-- LW-12b (F1)-(F8) (`:1821`) and the step from the cases (`:1885`, `:1891`)
#check @RBM.Graph.anpKey2_fix
#check @RBM.Graph.anpDetGhStep_of_reg
#check @RBM.Graph.anpDetGhRegStep_of_cases
-- LW-12b instances (section 7)
#check @RBM.Graph.anpKey2_decGhostOK
#check @RBM.Graph.anpKey2_decCaseI
#check @RBM.Graph.anpKey2_decCaseIII
#check @RBM.Graph.anpKey2_figAuxGh
#check @RBM.Graph.anpKey2_figAuxGh_ghostOK
#check @RBM.Graph.anpKey2_figAuxGh_nested
#check @RBM.Graph.anpKey2_inst_chain

-- LW-12c (`Graph/AnpKey3`, T2252, 8aa37bf): helpers, double ghostify, far segment, product, `Σ ξξ ≤ θ`, target
#check @RBM.Graph.anpKey3_endAt_mem
#check @RBM.Graph.anpKey3_gh2
#check @RBM.Graph.anpKey3_gh2_props
#check @RBM.Graph.anpKey3_far_gen
#check @RBM.Graph.anpKey3_prod
#check @RBM.Graph.anpKey3_sum_xx
#check @RBM.Graph.anpKey3_fixV_ng_iff
#check @RBM.Graph.anpDetGhCaseI_holds
#check @RBM.Graph.anpKey3_inst_chain

-- LW-P (`Graph/LWPins`, 975f4ff): the merged pin the chain ends in
#check @RBM.Gauss.Sizes.LWAnpKeyGh

-- `Defs/Lattice`, `Defs/Sizes`: the torus and its sup-distance
#check @RBM.Zd
#check @RBM.Gauss.zdistInf

-- Mathlib: the fixed vertex, sums, exponents
#check @Fin.insertNth
#check @Fin.insertNth_apply_same
#check @Fin.insertNth_apply_succAbove
#check @Finset.sum_comm
#check @Finset.mul_sum
#check @Finset.sum_mul
#check @Finset.sum_le_sum
#check @zpow_add₀

/-! ## 2. The target of T2260 and the intermediate pins -/

namespace RBM.Graph.T2260Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- Target: case (III) of the induction step of `lem:Anp_key_gh` (`7_8:1245-1348`), in every dimension, for the
merged case pin `AnpDetGhCaseIII` (`Graph/AnpKey2.lean:177`) unchanged.  File name: `anpDetGhCaseIII_holds`. -/
def AnpKey4CaseIIIHoldsPin : Prop := ∀ d : ℕ, AnpDetGhCaseIII d

/-- Two distinct B2 ending edges at one internal vertex lie on distinct paths (`7_8:1246`, "by definition"): the
paper's statement, from `GhostOK` (at most one ghost per path) and `IsNested` (walk, no repeated edge).
File name: `anpKey4_caseIII_ne`. -/
def AnpKey4NePin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool)
    (k₁ k₂ : Fin Γ.es.length),
    Γ.GhostOK → Γ.IsNested → (j₁, s₁) ≠ (j₂, s₂) →
    Γ.IsB2 π j₁ s₁ k₁ i → Γ.IsB2 π j₂ s₂ k₂ i → j₁ ≠ j₂

/-- The two solid edges `(α, β_t)` at the vertex of case (III) (`7_8:1247`): the step after (`s_t = false`) or
before (`s_t = true`) the B2 edge `k_t` on `𝔓_{j_t}`; distinct, solid, at `α_i`, and (`deg_s(α_i) = 2`) the only
solid edges at `α_i`.  File name: `anpKey4_solid`. -/
def AnpKey4SolidPin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool)
    (k₁ k₂ : Fin Γ.es.length),
    Γ.GhostOK → Γ.IsNested → j₁ ≠ j₂ → Γ.IsB2 π j₁ s₁ k₁ i → Γ.IsB2 π j₂ s₂ k₂ i → Γ.degS i = 2 →
    ∃ m₁ m₂ : Fin Γ.es.length, m₁ ≠ m₂ ∧
      (Γ.es.get m₁).ghost = false ∧ (Γ.es.get m₂).ghost = false ∧
      ((Γ.es.get m₁).u = Sum.inr i ∨ (Γ.es.get m₁).v = Sum.inr i) ∧
      ((Γ.es.get m₂).u = Sum.inr i ∨ (Γ.es.get m₂).v = Sum.inr i) ∧
      (s₁ = false → ∃ w rest, Γ.path j₁ = (k₁, Sum.inr i) :: (m₁, w) :: rest) ∧
      (s₁ = true → ∃ pre : List (Fin Γ.es.length × NV p q), Γ.path j₁ = pre ++ [(m₁, Sum.inr i), (k₁, Sum.inl (Sum.inr j₁))]) ∧
      (s₂ = false → ∃ w rest, Γ.path j₂ = (k₂, Sum.inr i) :: (m₂, w) :: rest) ∧
      (s₂ = true → ∃ pre : List (Fin Γ.es.length × NV p q), Γ.path j₂ = pre ++ [(m₂, Sum.inr i), (k₂, Sum.inl (Sum.inr j₂))]) ∧
      ∀ k : Fin Γ.es.length, (Γ.es.get k).ghost = false →
        ((Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i) → k = m₁ ∨ k = m₂

/-- The double A2 replacement of `anpKey3_gh2` for two ending edges (first or last step) of two distinct ghost-free
paths, not necessarily one-step paths (the merged `anpKey3_gh2_props`, `Graph/AnpKey3.lean:112`, asks for one-step
paths).  File name: `anpKey4_gh2_props`. -/
def AnpKey4Gh2Pin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → ∀ (r₁ r₂ : Fin p), r₁ ≠ r₂ →
    ∀ st₁ st₂ : Fin Γ.es.length × NV p q,
      st₁ ∈ Γ.path r₁ → ((Γ.path r₁).head? = some st₁ ∨ (Γ.path r₁).getLast? = some st₁) →
      st₂ ∈ Γ.path r₂ → ((Γ.path r₂).head? = some st₂ ∨ (Γ.path r₂).getLast? = some st₂) →
      Γ.noGhostPath r₁ = true → Γ.noGhostPath r₂ = true →
      (anpKey3_gh2 Γ st₁.1 st₂.1).GhostOK ∧ (anpKey3_gh2 Γ st₁.1 st₂.1).IsNested ∧
        (anpKey3_gh2 Γ st₁.1 st₂.1).nSolid + 2 = Γ.nSolid ∧
        (∀ r, (anpKey3_gh2 Γ st₁.1 st₂.1).noGhostPath r = true ↔
          Γ.noGhostPath r = true ∧ r ≠ r₁ ∧ r ≠ r₂) ∧
        (∀ (ι : Type) (ξ : ι → ι → ℝ) (lab : NV p q → ι),
          anpKey2_ep Γ ξ lab = ξ (lab (Γ.es.get st₁.1).u) (lab (Γ.es.get st₁.1).v) *
            ξ (lab (Γ.es.get st₂.1).u) (lab (Γ.es.get st₂.1).v) * anpKey2_ep (anpKey3_gh2 Γ st₁.1 st₂.1) ξ lab)

/-- The reduction of case (III) (`7_8:1250-1348`; the construction is the prover's, the pin is existential): a graph
with one internal vertex fewer, the ghost condition and the nested properties, the same `ord`, paths `r` of old paths
`own r` with ends `ea r`, `eb r` (`none`: a free external label `x₀`), ghost-free old paths stay ghost-free, and the
value on `𝐃_π` is at most `θ` times the value of the new graph at any `x₀` (`(kwuyayw_case3)`, first two steps).
File name: `anpKey4_reduce`. -/
def AnpKey4ReducePin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p (q + 1)) (π : Fin (q + 1) → Fin p → Bool),
    Γ.GhostOK → Γ.IsNested → AnpCaseIII Γ π →
    ∃ (p'' : ℕ) (Γ'' : NGraph p'' q) (ea eb : Fin p'' → Option (Fin p ⊕ Fin p)) (own : Fin p'' → Fin p),
      (Γ''.GhostOK ∧ Γ''.IsNested) ∧ Γ''.ordN = Γ.ordN ∧
      (∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none) ∧
      (∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none) ∧
      (∀ j, ∃! r, ea r = some (Sum.inl j)) ∧ (∀ j, ∃! r, eb r = some (Sum.inr j)) ∧
      (∀ r, Γ.noGhostPath (own r) = true → Γ''.noGhostPath r = true) ∧
      (∀ (d L : ℕ) [NeZero L] (ξ : Zd d L → Zd d L → ℝ) (θ : ℝ),
        (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) → (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ (a b : Fin p → Zd d L) (x₀ : Zd d L),
          Γ.valOn ξ a b (anpKey2_region a b π) ≤
            θ * Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (ea r)) (fun r => anpKey2_fixLab a b x₀ (eb r)))

/-- The assembly: the reduction and the induction hypothesis give the case pin (constants `(C, c/2)` from the
`AnpDetGhAt` of the reduced graph).  File name: `anpKey4_of_reduce`. -/
def AnpKey4OfReducePin : Prop := AnpKey4ReducePin → AnpKey4CaseIIIHoldsPin

/-! ## 3. Instances (Prop-valued shapes, no proof obligations) -/

/-- Case (III) only (no case (I)/(II)), with the self-loop configuration of T2242's note (d): `p = 2`, `q = 1`,
`α = inr 0`.  Path 0: `a_0 → α` (ghost, B2 at `α`), `α → a_0` (solid: `β_0 = a_0`, the paper's new ghost edge
`(a_0, β_0)` would be a loop), `a_0 → b_0` (solid).  Path 1: `a_1 → α` (ghost, B2), `α → b_1` (solid, B1).
`deg_s(α) = 2`, `n_S = 3`, `ord = 1`, `n_ngh = 0`.  File name: `anpKey4_figLoop`. -/
def figLoop : NGraph 2 1 where
  es := [⟨true, .inl (.inl 0), .inr 0⟩, ⟨false, .inr 0, .inl (.inl 0)⟩, ⟨false, .inl (.inl 0), .inl (.inr 0)⟩,
         ⟨true, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (1, .inl (.inl 0)), (2, .inl (.inr 0))]
    else [(3, .inr 0), (4, .inl (.inr 1))]

/-- The region pattern of the `figLoop` instances (any `π` works: B2 ignores `π`, no path is ghost-free). -/
def piLoop : Fin 1 → Fin 2 → Bool := fun _ _ => false

/-- Instance (1): the hypotheses at `figLoop`, and that case (I)/(II) does not apply (by `decide +kernel`). -/
example : Prop :=
  figLoop.GhostOK ∧ figLoop.IsNested ∧ figLoop.NoA2 piLoop ∧ ¬ AnpCaseI figLoop piLoop ∧
    AnpCaseIII figLoop piLoop ∧ figLoop.ordN = 1 ∧ figLoop.nngh = 0

/-- Instance (2): the target at `figLoop`. -/
example : Prop := AnpIH 3 1 → AnpDetGhRegAt 3 figLoop piLoop

/-- Instance (3): the target at `figAuxGh`, case (III) at `ℳ₂` (two B2 edges `4`, `5`, both `s = true`,
`β_0 = β_1 = ℳ₁`), proved through `anpDetGhCaseIII_holds` (not through case (I)). -/
example : Prop :=
  AnpCaseIII anpKey2_figAuxGh (fun _ _ => false) ∧
    (AnpIH 3 2 → AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false))

/-- Instance (4): the chain with cases (I) and (III) discharged. -/
example : Prop := AnpDetGhCaseIV 3 → LWAnpKeyGh 3

/-- Instance (5): the reduction at `figLoop` (the self-loop case): a reduced graph with no internal vertex and the
same `ord`. -/
example : Prop :=
  ∃ (p'' : ℕ) (Γ'' : NGraph p'' 0), Γ''.GhostOK ∧ Γ''.IsNested ∧ Γ''.ordN = figLoop.ordN

end RBM.Graph.T2260Check
