/-
Release check for T2234 (dispatcher V1, Mon Oct  5 23:58 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §24, §29,
§45 O2, §64 (4)).  LW-12a: first of six tickets of `lem:Anp` (`7_8:933-1599`; split stated in the ticket): the
deterministic form of `lem:Anp_key_gh`, its base case `q = 0`, the strong-induction assembly, the `≺`-lift to the
merged pin `LWAnpKeyGh`, and the two merged reductions `LWAnpKeyGh → LWAnpKey → LWAnp`.
Section 1: `#check` of every merged name the ticket cites (`Graph/LWVocab` 37db678, `Graph/LWPins` 975f4ff,
`Graph/LWPsi` 461ae86, `Graph/AuxGraph` 87cf70c, `Graph/AuxGraph2` fbaa460, `Defs/StochDomAt`, `Defs/Lattice`,
`Defs/Sizes`) and of the Mathlib name of the route.
Section 2: the pins of this ticket (namespace `RBM.Graph.T2234Check`; the prover's file restates them in `RBM.Graph`
with the same names minus the suffix `Pin`).
Section 3: Prop-valued examples (no proof obligations): the shapes of the compiled instances.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2234-check.lean`.
-/
import RBM3D.Graph.AuxGraph2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`, T2050, 37db678): nested graphs (section 3, `:296-399`)
#check @RBM.Graph.NV
#check @RBM.Graph.NEdge
#check @RBM.Graph.NGraph
#check @RBM.Graph.NGraph.WalkOK
#check @RBM.Graph.NGraph.Visits
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
#check @RBM.Graph.figAux_ord
-- `Graph/ScalingOrder`: the order `n_S + 2 (n_W - n_V)` behind `ordN`
#check @RBM.Graph.ord

-- LW-P (`Graph/LWPins`, T2067; pin texts fixed at 975f4ff): the three LW-12 pins and `(eq:Gbyxi3)`
#check @RBM.Gauss.Sizes.LWXi
#check @RBM.Gauss.Sizes.LWAnpKey
#check @RBM.Gauss.Sizes.LWAnpKeyGh
#check @RBM.Gauss.Sizes.LWAnp
-- the compiled consumers of the pins at `d = 3` (namespace `RBM.Gauss.LWInst`)
#check @RBM.Gauss.LWInst.inst_AnpKey
#check @RBM.Gauss.LWInst.inst_Anp
#check @RBM.Gauss.LWInst.inst_AnpKeyGh

-- LW-15 (`Graph/LWPsi`, T2051, 461ae86): the class of `Ψ_t(·)`
#check @RBM.Gauss.Sizes.LWPsiAll
#check @RBM.Gauss.Sizes.LWClass
#check @RBM.Gauss.Sizes.LWPsiRel

-- LW-11a/b (`Graph/AuxGraph` 87cf70c, `Graph/AuxGraph2` fbaa460): the producer of nested graphs and of `ξ`
#check @RBM.Graph.LWAuxNested
#check @RBM.Graph.lwAuxNested_holds
#check @RBM.Graph.LWXiClaim
#check @RBM.Graph.lwXiClaim_holds

-- `Defs/StochDomAt`: `≺`, its deterministic form, the union bound
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.Prec.whp
#check @RBM.StochDomAt.of_forall_le
#check @RBM.StochDomAt.of_le_left
#check @RBM.Gauss.HighProbAt.biInter

-- `Defs/Lattice`, `Defs/Sizes`: the torus and its sup-distance
#check @RBM.Zd
#check @RBM.zdist_add_le
#check @RBM.Gauss.zdistInf

-- Mathlib (`Mathlib.Algebra.Order.BigOperators.Ring.Finset`): Cauchy–Schwarz for finite sums
#check @Finset.sum_mul_sq_le_sq_mul_sq

/-! ## 2. Pins of T2234 -/

namespace RBM.Graph.T2234Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- The deterministic bound of `lem:Anp_key_gh` (`(adsuu22)`, `7_8:1043`) for one nested graph `Γ`: constants
`C, c > 0` (`c ≤ 1`) depending on `Γ` and `d` only such that, for every torus `Z_L^d`, every positive `ψ`
non-increasing on `[0, ∞)`, every `θ > 0` and every symmetric `ξ ≥ 0` with `ξ_{αβ} ≤ ψ(|α-β|)` and
`Σ_β ξ_{αβ}² ≤ θ` (the deterministic form of `(eq:Gbyxi3)`, `7_8:963-966`, with `θ = (W^d η_t)⁻¹`),
`𝒢_{ab} ≤ C θ^q ψ(0)^{ord - n_ngh} Π_i ψ(c|a_i - b_i|)^{χ(𝔓_i)}`. -/
def AnpDetGhAtPin (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          Γ.val ξ a b ≤ C * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
            ∏ i, (if Γ.noGhostPath i = true then
              ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)

/-- The deterministic `lem:Anp_key_gh` for every nested graph with the ghost condition (the `q ≤ p` of the merged
pin is implied by property (3) of `IsNested` at `A = univ` and is not assumed). -/
def AnpDetGhPin (d : ℕ) : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → AnpDetGhAtPin d Γ

/-- The base case `q = 0` of the induction (`7_8:1110`, "trivial by `(eq:Gbyxi3)`"): no internal vertex; every
path without a ghost edge is a walk through external vertices only, its longest edge has length
`≥ |a_i - b_i| / (its length)`, the paths are edge-disjoint. -/
def AnpDetGhZeroPin (d : ℕ) : Prop :=
  ∀ (p : ℕ) (Γ : NGraph p 0), Γ.GhostOK → Γ.IsNested → AnpDetGhAtPin d Γ

/-- The induction step (`7_8:1110-1599`, cases (I)–(IV) after the A2 replacement `(eq:noA2)`): the bound for
every graph with fewer internal vertices, and any number of paths, gives it for `q` internal vertices.
Proved by LW-12b…f (split in the ticket); here a hypothesis. -/
def AnpDetGhStepPin (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q →
    (∀ (p' k : ℕ), k < q → ∀ Γ' : NGraph p' k, Γ'.GhostOK → Γ'.IsNested → AnpDetGhAtPin d Γ') →
    ∀ (p : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → AnpDetGhAtPin d Γ

/-- The assembly by strong induction on `q`. -/
def AnpDetGhOfStepPin : Prop :=
  ∀ d : ℕ, AnpDetGhZeroPin d → AnpDetGhStepPin d → AnpDetGhPin d

/-- The `≺`-lift (`7_8:1041-1077`): the deterministic bound on the event where `(eq:Gbyxi3)` holds with `N^τ`
slack at every pair, the union bound over the `L^{2d}` pairs, gives the merged pin. -/
def LwAnpKeyGhOfDetPin : Prop :=
  ∀ d : ℕ, AnpDetGhPin d → LWAnpKeyGh d

/-- `lem:Anp_key` from `lem:Anp_key_gh` (`7_8:1025`, "an easy corollary"): no ghost edge gives `GhostOK`,
`noGhostPath i = true` for every `i`, `n_ngh = p`. -/
def LwAnpKeyOfGhPin : Prop :=
  ∀ d : ℕ, LWAnpKeyGh d → LWAnpKey d

/-- `lem:Anp` from `lem:Anp_key` (`(eq:bddGamma_aux)`, `7_8:933-939`): `a_i = [a]`, `b_i = [b]`; the product of
`p` equal factors (the probe's `lwanp_of_key`, `eeda441:RBM3D/Probe/T2040Graphs.lean`, T2040 b.5). -/
def LwAnpOfKeyPin : Prop :=
  ∀ d : ℕ, LWAnpKey d → LWAnp d

/-! ## 3. Shapes of the compiled instances (Prop-valued, no proof obligations) -/

/-- Instance (1): the base case at the one-edge graph `a_0 — b_0` (`p = 1`, `q = 0`, one solid edge, one path). -/
def oneEdge : NGraph 1 0 where
  es := [⟨false, .inl (.inl 0), .inl (.inr 0)⟩]
  path := fun _ => [(0, .inl (.inr 0))]

example : Prop := AnpDetGhAtPin 3 oneEdge

/-- Instance (2): the chain at `d = 3`, conditional on the step only: `LWAnp 3` from `AnpDetGhStepPin 3`. -/
example : Prop := AnpDetGhStepPin 3 → LWAnp 3

/-- Instance (3): the consumer of LW-11a: `figAux` (`q = 2`) is a legal input of the deterministic bound. -/
example : Prop := figAux.GhostOK → figAux.IsNested → (AnpDetGhPin 3 → AnpDetGhAtPin 3 figAux)

end RBM.Graph.T2234Check
