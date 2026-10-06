/-
Release check for T2242 (dispatcher V1, Tue Oct  6 01:51 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §74, §24, §64 (4),
§45 O2, §29, §20, §17, §16).  LW-12b: second of six tickets of `lem:Anp` (split table `docs/tickets/T2234.md`):
the regions `𝐃_π` and `(kwuyayw)` (`7_8:1111-1121`), the ending-edge types A1/A2/B1/B2 (`:1126-1141`), the A2
replacement on a region (`:1143-1148`, `(eq:noA2)`), vertex fixing (`:1158-1172`, `:1209-1237`), and the case
interface of LW-12c/d/e/f (cases (I)+(II) `:1152-1244`, (III) `:1245-1384`, (IV) `:1385-1599`).
Section 1: `#check` of every merged name the ticket cites (`Graph/AnpKey` e5b944a, `Graph/LWVocab` 37db678,
`Graph/LWPins` 975f4ff, `Defs/Lattice` 51f1a17, `Defs/Sizes` 0a873f1) and of the Mathlib names of the route.
Section 2: vocabulary and pins of this ticket (namespace `RBM.Graph.T2242Check`; the prover's file restates them in
`RBM.Graph` under the names of the ticket's table: each `…Pin` is `Iff.rfl`/`rfl` with the file's definition).
Section 3: the consumer statements of LW-12c/d/e/f (§45 O2; proved there, not here).
Section 4: Prop-valued examples (no proof obligations): the shapes of the compiled instances.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2242-check.lean`.
-/
import RBM3D.Graph.AnpKey
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`, T2050, 37db678): nested graphs (section 3, `:296-399`)
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

-- LW-12a (`Graph/AnpKey`, T2234, e5b944a): the deterministic `(adsuu22)`, the step pin, the lift
#check @RBM.Graph.AnpDetGhAt
#check @RBM.Graph.AnpDetGh
#check @RBM.Graph.AnpDetGhStep
#check @RBM.Graph.anpDetGh_zero
#check @RBM.Graph.anpDetGh_of_step
#check @RBM.Graph.lwAnpKeyGh_of_det
#check @RBM.Graph.lwAnpKey_of_gh
#check @RBM.Graph.lwAnp_of_key
-- LW-12a lattice helpers (section `Lattice`, `:74-107`)
#check @RBM.Graph.anpKey_zdistInf_sub_comm
#check @RBM.Graph.anpKey_zdistInf_tri
-- LW-12a A2 replacement (section `Ghostify`, `:364-643`)
#check @RBM.Graph.NGraph.ghostifyEs
#check @RBM.Graph.NGraph.ghostifyIdx
#check @RBM.Graph.NGraph.ghostify
#check @RBM.Graph.anpKey_gf_path
#check @RBM.Graph.anpKey_ghostify_nested
#check @RBM.Graph.anpKey_ghostify_ghostOK
#check @RBM.Graph.anpKey_ghostify_nSolid
#check @RBM.Graph.anpKey_gf_noGhostPath_iff
#check @RBM.Graph.anpKey_ghostify_nngh
#check @RBM.Graph.anpKey_ghostify_ord
#check @RBM.Graph.anpKey_ghostOK_of_noGhost

-- LW-P (`Graph/LWPins`, 975f4ff): the merged pin the chain ends in
#check @RBM.Gauss.Sizes.LWAnpKeyGh

-- `Defs/Lattice`, `Defs/Sizes`: the torus and its sup-distance
#check @RBM.Zd
#check @RBM.Gauss.zdistInf

-- Mathlib: inserting the fixed vertex (`Mathlib.Data.Fin.Tuple.Basic`), Cauchy–Schwarz (`…Ring.Finset`)
#check @Fin.insertNth
#check @Fin.insertNthEquiv
#check @Finset.sum_mul_sq_le_sq_mul_sq

/-! ## 2. Vocabulary and pins of T2242 -/

namespace RBM.Graph.T2242Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- The value of `Γ` with the internal labels restricted to `S` (the LHS of `(kwuyayw)`, `7_8:1119`);
`Γ.val ξ a b` is the case `S = univ`. -/
def valOnPin {p q : ℕ} (Γ : NGraph p q) {ι : Type*} (ξ : ι → ι → ℝ) (a b : Fin p → ι)
    (S : Finset (Fin q → ι)) : ℝ :=
  ∑ ℓ ∈ S, (Γ.es.map fun e =>
    if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod

/-- The region `𝐃_π` (`7_8:1113`): `π i j = true` iff `α_i` is strictly closer to `b_j` than to `a_j`
(`π_{i,j} = 1`); `π i j = false` iff `|α_i - a_j| ≤ |α_i - b_j|` (`π_{i,j} = 0`). -/
def regionPin {d L p q : ℕ} [NeZero L] (a b : Fin p → Zd d L) (π : Fin q → Fin p → Bool) :
    Finset (Fin q → Zd d L) :=
  Finset.univ.filter fun ℓ => ∀ (i : Fin q) (j : Fin p),
    (π i j = true ↔ zdistInf d L (ℓ i - b j) < zdistInf d L (ℓ i - a j))

/-- The one-vertex region: the constraint of `𝐃_π` on a single (fixed) vertex `x`, row `π_{i,·}`. -/
def regionOnePin {d L p : ℕ} [NeZero L] (a b : Fin p → Zd d L) (π : Fin p → Bool) : Finset (Zd d L) :=
  Finset.univ.filter fun x => ∀ j : Fin p,
    (π j = true ↔ zdistInf d L (x - b j) < zdistInf d L (x - a j))

/-- The ending edge `k` of the path `𝔓_j` at the end `s` (`s = false`: at `a_j`, the first step; `s = true`: at
`b_j`, the last step) is attached to the internal vertex `α_i` (`7_8:1123-1125`). -/
def EndAtPin {p q : ℕ} (Γ : NGraph p q) (j : Fin p) (s : Bool) (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  (∃ v : NV p q, (if s = true then (Γ.path j).getLast? else (Γ.path j).head?) = some (k, v)) ∧
    ((Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i)

/-- Type A1 on `𝐃_π` (`7_8:1127`, and the `b_j` version `:1139-1141`): `𝔓_j` has no ghost edge and `α_i` is on
the side of its own end (`π i j = s`). -/
def IsA1Pin {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  EndAtPin Γ j s k i ∧ Γ.noGhostPath j = true ∧ π i j = s

/-- Type A2 on `𝐃_π` (`7_8:1130`): `𝔓_j` has no ghost edge and `α_i` is on the side of the other end. -/
def IsA2Pin {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  EndAtPin Γ j s k i ∧ Γ.noGhostPath j = true ∧ π i j = !s

/-- Type B1 (`7_8:1134`): `𝔓_j` has a ghost edge, and it is not this one. -/
def IsB1Pin {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  EndAtPin Γ j s k i ∧ Γ.noGhostPath j = false ∧ (Γ.es.get k).ghost = false

/-- Type B2 (`7_8:1136`): this ending edge is the ghost edge of `𝔓_j` (`π` unused, kept for uniformity). -/
def IsB2Pin {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  EndAtPin Γ j s k i ∧ (Γ.es.get k).ghost = true

/-- `(eq:noA2)` (`7_8:1146`) on `𝐃_π`. -/
def NoA2Pin {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Prop :=
  ∀ (j : Fin p) (s : Bool) (k : Fin Γ.es.length) (i : Fin q), ¬ IsA2Pin Γ π j s k i

/-- `deg_s(α_i)`: the number of solid edges at `α_i` (`7_8:1247`). -/
def degSPin {p q : ℕ} (Γ : NGraph p q) (i : Fin q) : ℕ :=
  (Γ.es.filter fun e => !e.ghost && (decide (e.u = Sum.inr i) || decide (e.v = Sum.inr i))).length

/-- The label of an endpoint of a path of the fixed graph: `none` is the fixed vertex (label `x`), `some o` the old
external vertex `o` (`7_8:1214-1228`: `a_{j,r}, b_{j,r} ∈ {a_j, b_j, α_q}`). -/
def fixLabPin {p : ℕ} {ι : Type*} (a b : Fin p → ι) (x : ι) (o : Option (Fin p ⊕ Fin p)) : ι :=
  o.elim x (Sum.elim a b)

/-- `(kwuyayw)` (`7_8:1118-1121`), deterministic, on the region `𝐃_π`: the right side of `AnpDetGhAt`. -/
def AnpDetGhRegAtPin (d : ℕ) {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          valOnPin Γ ξ a b (regionPin a b π) ≤ C * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
            ∏ i, (if Γ.noGhostPath i = true then
              ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)

/-- The induction hypothesis of `AnpDetGhStep` (`7_8:1107`, in the stronger form of LW-12a: every graph with fewer
internal vertices, any number of paths and edges). -/
def AnpIHPin (d q : ℕ) : Prop :=
  ∀ (p' k : ℕ), k < q → ∀ Γ' : NGraph p' k, Γ'.GhostOK → Γ'.IsNested → AnpDetGhAt d Γ'

/-- Target 2: `(kwuyayw)` for every `π` gives `(adsuu22)` (`7_8:1116-1118`: the `2^{pq}` regions cover). -/
def AnpDetGhOfRegPin : Prop :=
  ∀ (d p q : ℕ) (Γ : NGraph p q), (∀ π, AnpDetGhRegAtPin d Γ π) → AnpDetGhAt d Γ

/-- Target 3: the half-distance fact behind A1/A2 (`7_8:1128`, `:1131`). -/
def AnpKey2HalfPin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (x y z : Zd d L),
    zdistInf d L (z - x) ≤ zdistInf d L (z - y) → zdistInf d L (x - y) ≤ 2 * zdistInf d L (z - y)

/-- Target 3: on `𝐃_π`, the far end is at distance `≥ |a_j - b_j|/2` (`7_8:1128`, `:1131`). -/
def AnpKey2RegHalfPin : Prop :=
  ∀ (d L p q : ℕ) [NeZero L] (a b : Fin p → Zd d L) (π : Fin q → Fin p → Bool) (ℓ : Fin q → Zd d L),
    ℓ ∈ regionPin a b π → ∀ (i : Fin q) (j : Fin p),
      (π i j = false → zdistInf d L (a j - b j) ≤ 2 * zdistInf d L (ℓ i - b j)) ∧
      (π i j = true → zdistInf d L (a j - b j) ≤ 2 * zdistInf d L (ℓ i - a j))

/-- Target 3: every ending edge at an internal vertex has one of the four types (`7_8:1126-1141`). -/
def AnpKey2EndTypesPin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool) (k : Fin Γ.es.length)
    (i : Fin q), EndAtPin Γ j s k i →
      IsA1Pin Γ π j s k i ∨ IsA2Pin Γ π j s k i ∨ IsB1Pin Γ π j s k i ∨ IsB2Pin Γ π j s k i

/-- Target 4: the A2 replacement on a region (`7_8:1143-1148`): it suffices to prove `(kwuyayw)` under
`(eq:noA2)`, for the same `p`, `q`, `π`. -/
def AnpDetGhRegOfNoA2Pin : Prop :=
  ∀ (d p q : ℕ) (π : Fin q → Fin p → Bool),
    (∀ Γ : NGraph p q, Γ.GhostOK → Γ.IsNested → NoA2Pin Γ π → AnpDetGhRegAtPin d Γ π) →
    ∀ Γ : NGraph p q, Γ.GhostOK → Γ.IsNested → AnpDetGhRegAtPin d Γ π

/-- Target 5: vertex fixing (`7_8:1158-1172`, `:1209-1237`): the internal vertex `α_{i₀}` becomes external and every
path is split at each visit of `α_{i₀}`; new path `r` comes from old path `own r`, its ends are `ea r`, `eb r`.
(F1) hypotheses of the induction; (F2) the edges, their ghost flags and labels (`em`); (F3) the value on `𝐃_π`
(only the row `π i₀` survives); (F4) ends; (F5) steps; (F6) ghost-free paths; (F7) an ending edge at `α_{i₀}` is a
one-step path; (F8) `n_S` unchanged. -/
def AnpKey2FixPin : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p (q + 1)) (i₀ : Fin (q + 1)), Γ.GhostOK → Γ.IsNested →
    ∃ (p' : ℕ) (Γ' : NGraph p' q) (ea eb : Fin p' → Option (Fin p ⊕ Fin p)) (own : Fin p' → Fin p)
      (em : Fin Γ.es.length ≃ Fin Γ'.es.length),
      -- (F1)
      (Γ'.GhostOK ∧ Γ'.IsNested) ∧
      -- (F2)
      (∀ k, (Γ'.es.get (em k)).ghost = (Γ.es.get k).ghost) ∧
      (∀ (ι : Type) (a b : Fin p → ι) (x : ι) (ℓ : Fin q → ι) (k : Fin Γ.es.length),
        Sum.elim (Sum.elim (fun r => fixLabPin a b x (ea r)) (fun r => fixLabPin a b x (eb r))) ℓ
            (Γ'.es.get (em k)).u =
          Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).u ∧
        Sum.elim (Sum.elim (fun r => fixLabPin a b x (ea r)) (fun r => fixLabPin a b x (eb r))) ℓ
            (Γ'.es.get (em k)).v =
          Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).v) ∧
      -- (F3)
      (∀ (d L : ℕ) [NeZero L] (ξ : Zd d L → Zd d L → ℝ), (∀ α β, 0 ≤ ξ α β) →
        ∀ (a b : Fin p → Zd d L) (π : Fin (q + 1) → Fin p → Bool),
          valOnPin Γ ξ a b (regionPin a b π) ≤
            ∑ x ∈ regionOnePin a b (π i₀),
              Γ'.val ξ (fun r => fixLabPin a b x (ea r)) (fun r => fixLabPin a b x (eb r))) ∧
      -- (F4)
      (∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none) ∧
      (∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none) ∧
      (∀ j, ∃! r, ea r = some (Sum.inl j)) ∧ (∀ j, ∃! r, eb r = some (Sum.inr j)) ∧
      -- (F5)
      (∀ (j : Fin p) (k : Fin Γ.es.length), (∃ v : NV p (q + 1), (k, v) ∈ Γ.path j) ↔
        ∃ (r : Fin p') (v' : NV p' q), own r = j ∧ (em k, v') ∈ Γ'.path r) ∧
      -- (F6)
      (∀ r, Γ.noGhostPath (own r) = true → Γ'.noGhostPath r = true) ∧
      (∀ j, Γ.noGhostPath j = false → ∃! r, own r = j ∧ Γ'.noGhostPath r = false) ∧
      -- (F7)
      (∀ (j : Fin p) (s : Bool) (k : Fin Γ.es.length), EndAtPin Γ j s k i₀ →
        ∃ r, own r = j ∧ Γ'.path r = [(em k, Sum.inl (Sum.inr r))] ∧
          (if s = true then ea r = none ∧ eb r = some (Sum.inr j)
            else ea r = some (Sum.inl j) ∧ eb r = none)) ∧
      -- (F8)
      Γ'.nSolid = Γ.nSolid

/-- The step on regions (`7_8:1149-1151`): `(kwuyayw)` under `(eq:noA2)` and the induction hypothesis. -/
def AnpDetGhRegStepPin (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → AnpIHPin d q →
    ∀ (p : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → NoA2Pin Γ π → AnpDetGhRegAtPin d Γ π

/-- Target 6: the merged step pin from the step on regions (targets 2 and 4). -/
def AnpDetGhStepOfRegPin : Prop :=
  ∀ d : ℕ, AnpDetGhRegStepPin d → AnpDetGhStep d

/-! ## 3. Case interface of LW-12c/d/e/f (§45 O2) -/

/-- Cases (I)+(II) (`7_8:1152-1244`): an internal vertex with two distinct ending edges of type A1 or B1. -/
def CaseIPin {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Prop :=
  ∃ (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool) (k₁ k₂ : Fin Γ.es.length), (j₁, s₁) ≠ (j₂, s₂) ∧
    (IsA1Pin Γ π j₁ s₁ k₁ i ∨ IsB1Pin Γ π j₁ s₁ k₁ i) ∧ (IsA1Pin Γ π j₂ s₂ k₂ i ∨ IsB1Pin Γ π j₂ s₂ k₂ i)

/-- Case (III) (`7_8:1245-1384`): an internal vertex with two distinct B2 ending edges and `deg_s = 2`. -/
def CaseIIIPin {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Prop :=
  ∃ (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool) (k₁ k₂ : Fin Γ.es.length), (j₁, s₁) ≠ (j₂, s₂) ∧
    IsB2Pin Γ π j₁ s₁ k₁ i ∧ IsB2Pin Γ π j₂ s₂ k₂ i ∧ degSPin Γ i = 2

/-- LW-12c (`AnpKey3`): `(kwuyayw_case1)` and Case (II) (`7_8:1196-1244`). -/
def AnpDetGhCaseIPin (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → AnpIHPin d q →
    ∀ (p : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → NoA2Pin Γ π → CaseIPin Γ π → AnpDetGhRegAtPin d Γ π

/-- LW-12d (`AnpKey4`): `(kwuyayw_case3)` (`7_8:1376-1384`). -/
def AnpDetGhCaseIIIPin (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → AnpIHPin d q →
    ∀ (p : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → NoA2Pin Γ π → CaseIIIPin Γ π → AnpDetGhRegAtPin d Γ π

/-- LW-12e + LW-12f (`AnpKey5`, `AnpKey6`): Case (IV), `(kwuyayw_ng)`, `(kwuyayw_ng_tree)` (`7_8:1385-1599`). -/
def AnpDetGhCaseIVPin (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → AnpIHPin d q →
    ∀ (p : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → NoA2Pin Γ π → ¬ CaseIPin Γ π → ¬ CaseIIIPin Γ π → AnpDetGhRegAtPin d Γ π

/-- Target 6: the case split (proved here; LW-12f plugs the three cases in). -/
def AnpDetGhRegStepOfCasesPin : Prop :=
  ∀ d : ℕ, AnpDetGhCaseIPin d → AnpDetGhCaseIIIPin d → AnpDetGhCaseIVPin d → AnpDetGhRegStepPin d

/-! ## 4. Shapes of the compiled instances (Prop-valued, no proof obligations) -/

/-- `figAux` with its two last edges (`ℳ₂ y`) made ghost: on `π ≡ false` every ending edge is B1 (at `ℳ₁`) or B2
(at `ℳ₂`); no A2; Case (I) at `ℳ₁` and Case (III) at `ℳ₂` (`deg_s(ℳ₂) = 2`). -/
def figAuxGh : NGraph 2 2 where
  es := [⟨false, .inl (.inl 0), .inr 0⟩, ⟨false, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inr 1⟩,
         ⟨false, .inr 0, .inr 1⟩, ⟨true, .inr 1, .inl (.inr 0)⟩, ⟨true, .inr 1, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (2, .inr 1), (4, .inl (.inr 0))]
    else [(1, .inr 0), (3, .inr 1), (5, .inl (.inr 1))]

/-- Instance (1): `figAuxGh` is a legal input with no A2 edge, in Cases (I) and (III). -/
example : Prop :=
  figAuxGh.GhostOK ∧ figAuxGh.IsNested ∧ NoA2Pin figAuxGh (fun _ _ => false) ∧
    CaseIPin figAuxGh (fun _ _ => false) ∧ CaseIIIPin figAuxGh (fun _ _ => false)

/-- Instance (2): `figAux` (no ghost) on `π ≡ false` has two A2 edges (`ℳ₂ y`, at the `b`-ends). -/
example : Prop := ¬ NoA2Pin figAux (fun _ _ => false)

/-- Instance (3): the chain from the three case pins to the merged step pin and to `LWAnpKeyGh 3`. -/
example : Prop :=
  AnpDetGhCaseIPin 3 → AnpDetGhCaseIIIPin 3 → AnpDetGhCaseIVPin 3 → AnpDetGhStep 3

/-- Instance (4): the interface lemmas LW-12c consumes at `figAuxGh` (fixing `α_0 = ℳ₁`, Case (I) data). -/
example : Prop := AnpKey2FixPin ∧ AnpKey2EndTypesPin ∧ AnpKey2RegHalfPin

end RBM.Graph.T2242Check
