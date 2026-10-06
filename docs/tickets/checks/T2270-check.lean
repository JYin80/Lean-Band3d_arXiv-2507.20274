/-
Release check for T2270 (dispatcher V1, Tue Oct  6 07:53 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §87 (2), §74,
§24, §64 (4), §45 O2, §29, §20, §17, §16; supervisor `docs/supervisor/2026-10-06-0752.md` §2 (REQ-0648 B: PASS)).
LW-12f: sixth and last ticket of `lem:Anp` (split table `docs/tickets/T2234.md:30`): the sums along a summation
certificate, the long-edge union bound, the deterministic `lem:Anp_key_gh` directly (`AnpDetGh d`), and from it the
merged step and case pins and the three merged `≺` pins `LWAnpKeyGh`, `LWAnpKey`, `LWAnp`.
Section 1: `#check` of every merged name the ticket cites (`Graph/AnpKey5` 1462fdb, `Graph/AnpKey4` 14c583b,
`Graph/AnpKey3` 8aa37bf, `Graph/AnpKey2` e362f4b, `Graph/AnpKey` e5b944a, `Graph/LWVocab` 37db678,
`Graph/ScalingOrder` 3c07bc8, `Graph/LWPins` 975f4ff, `Defs/Lattice` 51f1a17, `Defs/Sizes` 0a873f1) and of the
Mathlib names of the suggested route; namespace of each from its enclosing `namespace … end` block.
Section 2: the pins (namespace `RBM.Graph.T2270Check`; the prover's theorems in `RBM.Graph`, each discharged by
`@name`).  `AnpKey6SumPin`, `AnpKey6DirectPin`, `AnpKey6IVPin` restate the interface of
`docs/tickets/checks/T2264-check.lean:208-235`, with the merged `AnpSumCert` (`AnpKey5.lean:95`) in place of that
file's `sumCertPin` (equivalent, not `rfl`: `audit_sumCert_iff`, `docs/reports/T2264-audit.md` §1).
Section 3: the shapes of the compiled instances (Prop-valued, no proof obligations).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2270-check.lean`.
-/
import RBM3D.Graph.AnpKey5
import RBM3D.Graph.AnpKey4
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Logic.Equiv.Prod

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`, T2050, 37db678): nested graphs (`:296-399`)
#check @RBM.Graph.NV
#check @RBM.Graph.NEdge
#check @RBM.Graph.NGraph
#check @RBM.Graph.NGraph.WalkOK
#check @RBM.Graph.NGraph.IsNested
#check @RBM.Graph.NGraph.NoGhost
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
-- LW-P (`Graph/LWPins`, 975f4ff): the three merged `≺` pins and their premise, the merged consumers
#check @RBM.Gauss.Sizes.LWXi
#check @RBM.Gauss.Sizes.LWAnpKey
#check @RBM.Gauss.Sizes.LWAnpKeyGh
#check @RBM.Gauss.Sizes.LWAnp
#check @RBM.Gauss.LWInst.inst_AnpKey
#check @RBM.Gauss.LWInst.inst_Anp
-- `Defs/Lattice` (51f1a17), `Defs/Sizes` (0a873f1)
#check @RBM.Zd
#check @RBM.Gauss.zdistInf

-- LW-12a (`Graph/AnpKey`, T2234, e5b944a): the deterministic `(adsuu22)`, long edge, assembly, lift, reductions
#check @RBM.Graph.AnpDetGhAt
#check @RBM.Graph.AnpDetGh
#check @RBM.Graph.AnpDetGhZero
#check @RBM.Graph.AnpDetGhStep
#check @RBM.Graph.anpKey_zdistInf_tri
#check @RBM.Graph.anpKey_long_edge
#check @RBM.Graph.anpDetGh_zero
#check @RBM.Graph.anpDetGh_of_step
#check @RBM.Graph.lwAnpKeyGh_of_det
#check @RBM.Graph.anpKey_ghostOK_of_noGhost
#check @RBM.Graph.lwAnpKey_of_gh
#check @RBM.Graph.lwAnp_of_key
#check @RBM.Graph.anpKey_inst_anp
#check @RBM.Graph.anpKey_inst_figAux

-- LW-12b (`Graph/AnpKey2`, T2242, e362f4b): regions, step and case pins, the case split, instances
#check @RBM.Graph.NGraph.valOn
#check @RBM.Graph.anpKey2_val_eq_valOn
#check @RBM.Graph.anpKey2_region
#check @RBM.Graph.AnpDetGhRegAt
#check @RBM.Graph.AnpIH
#check @RBM.Graph.AnpDetGhRegStep
#check @RBM.Graph.AnpCaseI
#check @RBM.Graph.AnpCaseIII
#check @RBM.Graph.AnpDetGhCaseI
#check @RBM.Graph.AnpDetGhCaseIII
#check @RBM.Graph.AnpDetGhCaseIV
#check @RBM.Graph.anpDetGh_of_reg
#check @RBM.Graph.anpDetGhStep_of_reg
#check @RBM.Graph.anpDetGhRegStep_of_cases
#check @RBM.Graph.anpKey2_figAuxGh
#check @RBM.Graph.anpKey2_figAuxGh_ghostOK
#check @RBM.Graph.anpKey2_figAuxGh_nested
#check @RBM.Graph.anpKey2_inst_chain

-- LW-12c (`Graph/AnpKey3`, T2252, 8aa37bf): `Σ_x ξ ξ ≤ θ` (`:405`), case (I)+(II) proved, chain
#check @RBM.Graph.anpKey3_sum_xx
#check @RBM.Graph.anpDetGhCaseI_holds
#check @RBM.Graph.anpKey3_inst_chain

-- LW-12d (`Graph/AnpKey4`, T2260, 14c583b): case (III) proved (`:784`)
#check @RBM.Graph.anpDetGhCaseIII_holds

-- LW-12e (`Graph/AnpKey5`, T2264, 1462fdb): the certificate and its vocabulary, instances
#check @RBM.Graph.anpKey5_early
#check @RBM.Graph.AnpSumOrder
#check @RBM.Graph.AnpSumCert
#check @RBM.Graph.anpKey5_rest
#check @RBM.Graph.anpKey5_perPath
#check @RBM.Graph.anpKey5_decSumOrder
#check @RBM.Graph.anpKey5_decPerPath
#check @RBM.Graph.anpKey5_rest_countP
#check @RBM.Graph.anpKey5_sumOrder_of_valid
#check @RBM.Graph.anpKey5_cert_mono
#check @RBM.Graph.anpKey5_cert
#check @RBM.Graph.anpKey5_decIsNested
#check @RBM.Graph.anpKey5_figIVext
#check @RBM.Graph.anpKey5_resAux
#check @RBM.Graph.anpKey5_inst_figIVext
#check @RBM.Graph.anpKey5_inst_resAux
#check @RBM.Graph.anpKey5_inst_figAuxGh

-- Mathlib (suggested route): choice functions, splitting products, AM-GM, one coordinate out of `Fin q → X`
#check @Fintype.piFinset
#check @Fintype.mem_piFinset
#check @Fintype.card_piFinset
#check @Finset.prod_mul_prod_compl
#check @Finset.prod_le_prod₀
#check @List.prod_set
#check @two_mul_le_add_sq
#check @Equiv.piSplitAt

/-! ## 2. The pins -/

namespace RBM.Graph.T2270Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- File: `anpKey6_order`.  The sums along a nested order (`(kwuyayw_ng)`, `7_8:1397-1402`; `7_8:1420-1423`):
summing `σ[last]` first, each vertex sees two edges to labels still fixed (`Σ_x ξ(y₁,x) ξ(y₂,x) ≤ θ`,
`anpKey3_sum_xx`), its other remaining edges are `≤ ψ(0)`. -/
def AnpKey6OrderPin : Prop :=
  ∀ (d p q : ℕ) (E : List (NV p q × NV p q)) (σ : List (Fin q)), AnpSumOrder E σ →
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          ∑ ℓ : Fin q → Zd d L, (E.map fun e =>
              ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤
            θ ^ q * ψ 0 ^ ((E.length : ℤ) - 2 * (q : ℤ))

/-- File: `anpKey6_sum`.  T2264's `AnpKey6SumPin` (`T2264-check.lean:208-222`) with `AnpSumCert` for `sumCertPin`:
the sums along a certificate (`(kwuyayw_ng_tree)`, `7_8:1414-1533`; the AM-GM split `7_8:1428-1431`). -/
def AnpKey6SumPin : Prop :=
  ∀ (d p q n : ℕ) (E : List (NV p q × NV p q)), AnpSumCert n E →
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          ∑ ℓ : Fin q → Zd d L, (E.map fun e =>
              ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤
            θ ^ q * ψ 0 ^ ((E.length : ℤ) - 2 * (q : ℤ))

/-- File: `anpKey6_union`.  The long-edge union bound (base-case argument of `7_8:1110` on every ghost-free path,
`anpKey_long_edge`): a finite family `𝓜` of reserved sets (one long edge per ghost-free path; at most
`Π_j max 1 |𝔓_j|` of them), each with `perPath` and `|rest| + n_ngh = n_S`, such that for every labelling the value
is at most the sum over `M ∈ 𝓜` of the long-edge factors (`c = 1/(1 + Σ_j |𝔓_j|)`) times the sum of the rest. -/
def AnpKey6UnionPin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested →
    ∃ 𝓜 : Finset (Finset (Fin Γ.es.length)),
      (𝓜.card : ℝ) ≤ ∏ j, max (1 : ℝ) ((Γ.path j).length : ℝ) ∧
      (∀ M ∈ 𝓜, anpKey5_perPath Γ M ∧ (anpKey5_rest Γ M).length + Γ.nngh = Γ.nSolid) ∧
      ∀ (d L : ℕ) [NeZero L] (ψ : ℝ → ℝ), AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) →
        ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
          (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
          ∀ a b : Fin p → Zd d L,
            Γ.val ξ a b ≤ ∑ M ∈ 𝓜,
              (∏ i, (if Γ.noGhostPath i = true then
                ψ ((1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)) *
              ∑ ℓ : Fin q → Zd d L, ((anpKey5_rest Γ M).map fun e =>
                ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod

/-- File: `anpDetGh_holds`.  T2264's interface `AnpKey6DirectPin`, unchanged: the deterministic `lem:Anp_key_gh`
(`(adsuu22)`, `AnpKey.lean:41-58`) for every `GhostOK`, `IsNested` graph, with `C = Π_j max 1 |𝔓_j|`,
`c = 1/(1 + Σ_j |𝔓_j|)`. -/
def AnpKey6DirectPin : Prop := ∀ d : ℕ, AnpDetGh d

/-- File: `anpDetGhCaseIV_holds`.  T2264's `AnpKey6IVPin`: the merged case pin (`AnpKey2.lean:183`), unchanged
(`valOn` on a region `≤ val`, terms `≥ 0`; the case and induction hypotheses are not used). -/
def AnpKey6IVPin : Prop := ∀ d : ℕ, AnpDetGhCaseIV d

/-- File: `anpDetGhStep_holds`.  The merged step pin (`AnpKey.lean:67`): its induction hypothesis is not used. -/
def AnpKey6StepPin : Prop := ∀ d : ℕ, AnpDetGhStep d

/-- File: `anpIH_holds`.  The merged induction hypothesis (`AnpKey2.lean:151`), for every `q`; its owed registry line
(`Axioms.lean:168`) can go only once a theorem concludes it. -/
def AnpKey6IHPin : Prop := ∀ d q : ℕ, AnpIH d q

/-- File: `anpDetGhRegStep_holds`.  The merged step on regions (`AnpKey2.lean:155`), from the merged case split
`anpDetGhRegStep_of_cases` with `anpDetGhCaseI_holds`, `anpDetGhCaseIII_holds` and this ticket's case (IV). -/
def AnpKey6RegStepPin : Prop := ∀ d : ℕ, AnpDetGhRegStep d

/-- File: `lwAnpKeyGh_holds` (`lwAnpKeyGh_of_det ∘ anpDetGh_holds`). -/
def AnpKey6KeyGhPin : Prop := ∀ d : ℕ, LWAnpKeyGh d

/-- File: `lwAnpKey_holds` (`lwAnpKey_of_gh`). -/
def AnpKey6KeyPin : Prop := ∀ d : ℕ, LWAnpKey d

/-- File: `lwAnp_holds` (`lwAnp_of_key`). -/
def AnpKey6AnpPin : Prop := ∀ d : ℕ, LWAnp d

/-! ## 3. Instances (Prop-valued shapes, no proof obligations) -/

/-- Instance (1): `anpDetGh_holds` at three merged graphs: `figAux` (no ghost, `GhostOK` by
`anpKey_ghostOK_of_noGhost figAux_nested.2`), `anpKey5_figIVext` (case (IV), `q = 1 < p = 2`; `GhostOK`, `IsNested`
from `anpKey5_inst_figIVext`), `anpKey2_figAuxGh` (`anpKey2_figAuxGh_ghostOK`, `anpKey2_figAuxGh_nested`). -/
example : Prop :=
  AnpDetGhAt 3 figAux ∧ AnpDetGhAt 3 anpKey5_figIVext ∧ AnpDetGhAt 3 anpKey2_figAuxGh

/-- Instance (2): the three merged `≺` pins at `d = 3`; `LWAnp 3` is the `h` of the merged `inst_Anp`
(`LWPins.lean:699`) and `LWAnpKey 3` that of `inst_AnpKey` (`:686`). -/
example : Prop := LWAnpKeyGh 3 ∧ LWAnpKey 3 ∧ LWAnp 3

/-- Instance (3): every merged step and case pin at `d = 3` (the consumers `anpKey3_inst_chain`,
`anpKey2_inst_chain`, `anpKey_inst_anp` then close with no hypothesis left). -/
example : Prop :=
  AnpDetGhCaseI 3 ∧ AnpDetGhCaseIII 3 ∧ AnpDetGhCaseIV 3 ∧ AnpDetGhRegStep 3 ∧ AnpDetGhStep 3 ∧ AnpIH 3 2

/-- Instance (4): the sum pin at the depth-1 certificate of `figAux` minus `anpKey5_resAux` (`anpKey5_inst_resAux`:
no nested order, AM-GM needed), `d = L = 3`, `ψ r = (1 + r)⁻¹`, `θ = 1`, `ξ ≡ 1/6` (`Σ_β ξ² = 27/36 ≤ 1`,
`ξ ≤ 1/2 ≤ ψ(|α-β|)` on `Z_3^3`), `a ≡ 0`, `b ≡ 1`: `729 · 6⁻⁴ ≤ 1`. -/
example : Prop :=
  ∑ ℓ : Fin 2 → Zd 3 3, ((anpKey5_rest figAux anpKey5_resAux).map fun e : NV 2 2 × NV 2 2 =>
      (fun _ _ : Zd 3 3 => (1 / 6 : ℝ))
        (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.1)
        (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.2)).prod ≤
    (1 : ℝ) ^ 2 * (fun r : ℝ => (1 + r)⁻¹) 0 ^
      (((anpKey5_rest figAux anpKey5_resAux).length : ℤ) - 2 * (2 : ℤ))

/-- Instance (5): the union bound's family at `figAux` (two ghost-free paths of length 3: at most 9 reserved sets,
each with `perPath`). -/
example : Prop :=
  ∃ 𝓜 : Finset (Finset (Fin figAux.es.length)), (𝓜.card : ℝ) ≤ 9 ∧ ∀ M ∈ 𝓜, anpKey5_perPath figAux M

end RBM.Graph.T2270Check
