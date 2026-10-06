/-
Release check for T2264 (dispatcher V1, Tue Oct  6 06:06 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §74, §24, §64 (4),
§45 O2, §29, §20, §17, §16).  LW-12e: fifth of six tickets of `lem:Anp` (split table `docs/tickets/T2234.md:29`):
case (IV) part 1 of the induction step of `lem:Anp_key_gh` (`7_8:1385-1460`): the nested order of summation
(`7_8:1400-1402`, the spanning tree `𝕋` and its re-rooting `:1414-1451`), made combinatorial and general.
Section 1: `#check` of every merged name the ticket cites (`Graph/AnpKey3` 8aa37bf, `Graph/AnpKey2` e362f4b,
`Graph/AnpKey` e5b944a, `Graph/LWVocab` 37db678, `Graph/ScalingOrder` 3c07bc8, `Graph/LWPins` 975f4ff,
`Defs/Lattice` 51f1a17, `Defs/Sizes` 0a873f1) and of the Mathlib names of the suggested route; namespace of each
from its enclosing `namespace … end` block.
Section 2: the vocabulary (file names in the docstrings), the target pin and the intermediate pins (namespace
`RBM.Graph.T2264Check`; the prover's theorems in `RBM.Graph`, each discharged by `@name`), and the interface owed by
LW-12f (`AnpKey6SumPin`, `AnpKey6DirectPin`; not proved by T2264).
Section 3: the formal case-(IV) graph `figIVext` (`q = 1 < p = 2`, an ending edge at an external vertex: the
paper's properties (1)-(2) of `:1388-1393` fail) and the shapes of the compiled instances.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2264-check.lean`.
-/
import RBM3D.Graph.AnpKey3
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`, T2050, 37db678): nested graphs (`:296-388`)
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
#check @RBM.Graph.figAux
#check @RBM.Graph.figAux_nested
-- `Graph/ScalingOrder` (3c07bc8): `ord c = nS + 2 (nW - nV)`, the body of `ordN`
#check @RBM.Graph.ord
-- LW-P (`Graph/LWPins`, 975f4ff)
#check @RBM.Gauss.Sizes.LWAnpKeyGh
-- `Defs/Lattice` (51f1a17), `Defs/Sizes` (0a873f1)
#check @RBM.Zd
#check @RBM.Gauss.zdistInf

-- LW-12a (`Graph/AnpKey`, T2234, e5b944a): the deterministic `(adsuu22)`, walk and long edge, assembly, lift
#check @RBM.Graph.AnpDetGhAt
#check @RBM.Graph.AnpDetGh
#check @RBM.Graph.AnpDetGhStep
#check @RBM.Graph.anpKey_zdistInf_tri
#check @RBM.Graph.anpKey_walk
#check @RBM.Graph.anpKey_long_edge
#check @RBM.Graph.anpDetGh_zero
#check @RBM.Graph.anpDetGh_of_step
#check @RBM.Graph.lwAnpKeyGh_of_det

-- LW-12b (`Graph/AnpKey2`, T2242, e362f4b): vocabulary and case pins (`:44-190`)
#check @RBM.Graph.NGraph.valOn
#check @RBM.Graph.NGraph.EndAt
#check @RBM.Graph.NGraph.IsA1
#check @RBM.Graph.NGraph.IsB1
#check @RBM.Graph.NGraph.IsB2
#check @RBM.Graph.NGraph.NoA2
#check @RBM.Graph.NGraph.degS
#check @RBM.Graph.NGraph.anpKey2_decNoA2
#check @RBM.Graph.anpKey2_region
#check @RBM.Graph.AnpDetGhRegAt
#check @RBM.Graph.AnpIH
#check @RBM.Graph.AnpCaseI
#check @RBM.Graph.AnpCaseIII
#check @RBM.Graph.AnpDetGhCaseIV
-- LW-12b walks (section `Chain`, `:343-460`)
#check @RBM.Graph.anpKey2_stepOK
#check @RBM.Graph.anpKey2_chain
#check @RBM.Graph.anpKey2_walkOK_iff
#check @RBM.Graph.anpKey2_chain_append
#check @RBM.Graph.anpKey2_chain_visit
-- LW-12b step from the cases and instances (`:1885-1975`)
#check @RBM.Graph.anpDetGhStep_of_reg
#check @RBM.Graph.anpDetGhRegStep_of_cases
#check @RBM.Graph.anpKey2_decGhostOK
#check @RBM.Graph.anpKey2_decCaseI
#check @RBM.Graph.anpKey2_decCaseIII
#check @RBM.Graph.anpKey2_figAuxGh
#check @RBM.Graph.anpKey2_figAuxGh_ghostOK
#check @RBM.Graph.anpKey2_figAuxGh_nested
#check @RBM.Graph.anpKey2_inst_chain

-- LW-12c (`Graph/AnpKey3`, T2252, 8aa37bf): `Σ ξξ ≤ θ` (for LW-12f), target, chain
#check @RBM.Graph.anpKey3_sum_xx
#check @RBM.Graph.anpDetGhCaseI_holds
#check @RBM.Graph.anpKey3_inst_chain

-- Mathlib (suggested for section 4, optional): `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean:182`, `:298`
#check @SimpleGraph.isAcyclic_iff_forall_adj_isBridge
#check @SimpleGraph.IsTree.card_edgeFinset

/-! ## 2. Vocabulary, the target of T2264, the intermediate pins, the interface owed by LW-12f -/

namespace RBM.Graph.T2264Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- File: `anpKey5_inS`.  The vertex `w` is an internal vertex in `S`. -/
def inSPin {p q : ℕ} (S : Finset (Fin q)) (w : NV p q) : Bool :=
  Sum.elim (fun _ : Fin p ⊕ Fin p => false) (fun i : Fin q => decide (i ∈ S)) w

/-- File: `anpKey5_cross`.  The number of edges of `E` with exactly one end in `S`. -/
def crossPin {p q : ℕ} (E : List (NV p q × NV p q)) (S : Finset (Fin q)) : ℕ :=
  E.countP fun e => inSPin S e.1 != inSPin S e.2

/-- File: `anpKey5_crossAt`.  The number of edges of `E` at `α_v` whose other end is not in `S`. -/
def crossAtPin {p q : ℕ} (E : List (NV p q × NV p q)) (S : Finset (Fin q)) (v : Fin q) : ℕ :=
  E.countP fun e => (decide (e.1 = Sum.inr v) && !inSPin S e.2) || (decide (e.2 = Sum.inr v) && !inSPin S e.1)

/-- File: `anpKey5_inside`.  The number of edges of `E` with both ends in `S`. -/
def insidePin {p q : ℕ} (E : List (NV p q × NV p q)) (S : Finset (Fin q)) : ℕ :=
  E.countP fun e => inSPin S e.1 && inSPin S e.2

/-- File: `anpKey5_early`.  The vertex `w` is external or among the first `m` entries of `σ`. -/
def earlyPin {p q : ℕ} (σ : List (Fin q)) (m : ℕ) (w : NV p q) : Bool :=
  Sum.elim (fun _ : Fin p ⊕ Fin p => true) (fun i : Fin q => decide (i ∈ σ.take m)) w

/-- File: `AnpSumOrder`.  A nested order of summation (`7_8:1400-1402`) for the solid edges `E` (endpoint pairs):
`σ` lists every internal vertex once, and `σ[m]` has at least two edges whose other end is external or an earlier
`σ[m']`.  The vertices are summed in the order `σ[last], …, σ[0]`: when `σ[m]` is summed, two of its edges go to
labels still fixed (`Σ_x ξ(y₁,x) ξ(y₂,x) ≤ θ`), its other edges are `≤ ψ(0)`. -/
def sumOrderPin {p q : ℕ} (E : List (NV p q × NV p q)) (σ : List (Fin q)) : Prop :=
  σ.Nodup ∧ (∀ i : Fin q, i ∈ σ) ∧
    ∀ m : Fin σ.length, 2 ≤ E.countP fun e =>
      (decide (e.1 = Sum.inr (σ.get m)) && earlyPin σ m.1 e.2) ||
        (decide (e.2 = Sum.inr (σ.get m)) && earlyPin σ m.1 e.1)

/-- File: `AnpSumCert`.  A summation certificate of depth `≤ n`: a nested order, or an AM-GM split
`ξ_k ξ_{k'} ≤ (ξ_k² + ξ_{k'}²)/2` (`7_8:1428-1431`): the edge `k'` replaced by a copy of `k`, and `k` by a copy of
`k'`, each with a certificate of depth `≤ n - 1`. -/
def sumCertPin {p q : ℕ} : ℕ → List (NV p q × NV p q) → Prop
  | 0, E => ∃ σ : List (Fin q), sumOrderPin E σ
  | n + 1, E => (∃ σ : List (Fin q), sumOrderPin E σ) ∨
      ∃ k k' : Fin E.length, k ≠ k' ∧ sumCertPin n (E.set k'.1 (E.get k)) ∧ sumCertPin n (E.set k.1 (E.get k'))

/-- File: `anpKey5_rest`.  The solid edges of `Γ` outside `M`, as endpoint pairs (`M`: the reserved long edges of
the ghost-free paths in LW-12f's union bound; ghost edges are dropped in any case). -/
def restPin {p q : ℕ} (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) : List (NV p q × NV p q) :=
  (List.finRange Γ.es.length).filterMap fun k =>
    if (Γ.es.get k).ghost = true ∨ k ∈ M then none else some ((Γ.es.get k).u, (Γ.es.get k).v)

/-- File: `anpKey5_perPath`.  Every path has at most one edge that is a ghost or in `M`. -/
def perPathPin {p q : ℕ} (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) : Prop :=
  ∀ j : Fin p, ((Γ.path j).filter fun st => (Γ.es.get st.1).ghost || decide (st.1 ∈ M)).length ≤ 1

/-- The target, file name `anpKey5_cert`: every nested graph, with one edge per path removed (its ghost, or a
reserved edge), has a summation certificate for its remaining solid edges.  No `GhostOK` ending-edge clause, no
region, no `NoA2`, no case hypothesis. -/
def AnpKey5CertPin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested → perPathPin Γ M →
    ∃ n : ℕ, sumCertPin n (restPin Γ M)

/-- File: `anpKey5_cross_ge` (`7_8:1388-1393`, the counting behind "B1 + B2", in Hall form): every set `S` of
internal vertices has at least `|S|` remaining edges with exactly one end in `S` (IsNested conjunct 6 gives `|S|`
paths visiting `S`; each crosses `∂S` at least twice with distinct edges, at most one of them removed). -/
def AnpKey5CrossPin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested → perPathPin Γ M →
    ∀ S : Finset (Fin q), S.card ≤ crossPin (restPin Γ M) S

/-- File: `anpKey5_inside_ge` (the formal `(eq:degali)`): if every vertex of `S` has at most one remaining edge
leaving `S`, then `S` carries at least `|S|` remaining edges inside (every visiting path then crosses `∂S` exactly
twice and runs inside `S` with remaining edges only; IsNested conjunct 5 gives two paths at each vertex). -/
def AnpKey5InnerPin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested → perPathPin Γ M →
    ∀ S : Finset (Fin q), (∀ v ∈ S, crossAtPin (restPin Γ M) S v ≤ 1) → S.card ≤ insidePin (restPin Γ M) S

/-- File: `anpKey5_graph` (the spanning tree and its re-rooting, `7_8:1414-1451`, as a statement on multigraphs):
no loops, the crossing bound for every `S` and the inside bound for every `S` whose vertices have at most one
leaving edge give a certificate.  Route: greedy nested order from the external vertices; the stuck rest `R` has
exactly one leaving edge per vertex; each component of `R` has `≥ |R'|` inside edges, hence a non-bridge edge
`α₁α₂`; AM-GM on the leaving edges of `α₁`, `α₂`; induction on the number of components. -/
def AnpKey5GraphPin : Prop :=
  ∀ (p q : ℕ) (E : List (NV p q × NV p q)), (∀ e ∈ E, e.1 ≠ e.2) →
    (∀ S : Finset (Fin q), S.card ≤ crossPin E S) →
    (∀ S : Finset (Fin q), (∀ v ∈ S, crossAtPin E S v ≤ 1) → S.card ≤ insidePin E S) →
    ∃ n : ℕ, sumCertPin n E

/-- Owed by LW-12f (`AnpKey6`), not proved by T2264: the sums along a certificate (`(kwuyayw_ng_tree)`,
`7_8:1414-1533`): `Σ_ℓ Π_{e ∈ E} ξ ≤ θ^q ψ(0)^{|E| - 2q}`. -/
def AnpKey6SumPin : Prop :=
  ∀ (d p q n : ℕ) (E : List (NV p q × NV p q)), sumCertPin n E →
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          ∑ ℓ : Fin q → Zd d L, (E.map fun e =>
              ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤
            θ ^ q * ψ 0 ^ ((E.length : ℤ) - 2 * (q : ℤ))

/-- Owed by LW-12f: the deterministic `lem:Anp_key_gh` directly (union bound over the long edge of each ghost-free
path, `anpKey_long_edge`, then `AnpKey5CertPin` and `AnpKey6SumPin`); it gives `AnpDetGhCaseIV d` (`valOn ≤ val`)
and `AnpDetGhStep d` (the hypothesis is not used). -/
def AnpKey6DirectPin : Prop := ∀ d : ℕ, AnpDetGh d

/-- The merged case pin, unchanged (`Graph/AnpKey2.lean:183`); LW-12f's target. -/
def AnpKey6IVPin : Prop := ∀ d : ℕ, AnpDetGhCaseIV d

/-! ## 3. Instances (Prop-valued shapes, no proof obligations) -/

/-- Formal case (IV) with `q = 1 < p = 2` (file name `anpKey5_figIVext`): `α = inr 0`.  Path 0: `a_0 → α` (ghost,
B2), `α → b_0` (solid, B1).  Path 1: `a_1 → b_0` (solid, an ending edge at an external vertex), `b_0 → α` (solid),
`α → b_1` (ghost, B2).  Edge 5: `α a_0` (solid, on no path).  `deg_s(α) = 3`, `n_S = 4`, `ord = 2`, `n_ngh = 0`;
without edge 5 it is case (III). -/
def figIVext : NGraph 2 1 where
  es := [⟨true, .inl (.inl 0), .inr 0⟩, ⟨false, .inr 0, .inl (.inr 0)⟩, ⟨false, .inl (.inl 1), .inl (.inr 0)⟩,
         ⟨false, .inl (.inr 0), .inr 0⟩, ⟨true, .inr 0, .inl (.inr 1)⟩, ⟨false, .inr 0, .inl (.inl 0)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (1, .inl (.inr 0))]
    else [(2, .inl (.inr 0)), (3, .inr 0), (4, .inl (.inr 1))]

/-- Any `π` works at `figIVext` (no path is ghost-free). -/
def piIV : Fin 1 → Fin 2 → Bool := fun _ _ => false

/-- The reserved set `{0, 5}` of `figAux` (the first edge of path 0, the last edge of path 1). -/
def resAux : Finset (Fin figAux.es.length) := Finset.univ.filter fun k => k.1 = 0 ∨ k.1 = 5

/-- Instance (1): `figIVext` is in case (IV) (by `decide +kernel`, a local `Decidable IsNested` instance as for
`figAux`), and has the nested order `[α]`. -/
example : Prop :=
  figIVext.GhostOK ∧ figIVext.IsNested ∧ figIVext.NoA2 piIV ∧ ¬ AnpCaseI figIVext piIV ∧
    ¬ AnpCaseIII figIVext piIV ∧ figIVext.degS 0 = 3 ∧ figIVext.ordN = 2 ∧ figIVext.nngh = 0 ∧
    sumOrderPin (restPin figIVext ∅) [0]

/-- Instance (2): the re-rooting is needed: `figAux` with `resAux` removed has no nested order, and a certificate
of depth 1 (AM-GM on the remaining edges `a_1 ℳ₁` and `ℳ₂ b_0`). -/
example : Prop :=
  perPathPin figAux resAux ∧
    (∀ σ ∈ (List.finRange 2).permutations, ¬ sumOrderPin (restPin figAux resAux) σ) ∧
    sumCertPin 1 (restPin figAux resAux)

/-- Instance (3): the target at the merged `figAuxGh` (ghosts dropped, nothing reserved). -/
example : Prop := ∃ n : ℕ, sumCertPin n (restPin anpKey2_figAuxGh ∅)

/-- Instance (4): the target at `figIVext` (nothing reserved), and reserving edge `1` of path 0 (which already has
its ghost `0`) violates the per-path hypothesis. -/
example : Prop :=
  perPathPin figIVext ∅ ∧ (∃ n : ℕ, sumCertPin n (restPin figIVext ∅)) ∧
    ¬ perPathPin figIVext (Finset.univ.filter fun k : Fin figIVext.es.length => k.1 = 1)

end RBM.Graph.T2264Check
