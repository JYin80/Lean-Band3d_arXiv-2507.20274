/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# LW-12b: `lem:Anp_key_gh`, the setup of the induction step (T2242)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): the regions `𝐃_π`
(`:1113`) and `(kwuyayw)` (`:1118-1121`), the ending-edge types A1/A2/B1/B2 (`:1123-1141`), the A2
replacement and `(eq:noA2)` (`:1143-1148`), vertex fixing (`:1158-1172`, `:1209-1237`), the case
statements (I)-(IV) (`:1152`, `:1205`, `:1245`, `:1385`).  Part b of the six tickets of `lem:Anp`.

Conventions fixed here for LW-12c-f: `π i j = true` iff `α_i` is strictly closer to `b_j` than to
`a_j`; an ending edge has a side bit `s` (`false`: first step of the path, at `a_j`; `true`: last
step, at `b_j`); type A1 iff the path has no ghost edge and `π i j = s` (the vertex lies on the side
of its own end).

* Section 1: the vocabulary (`valOn`, the regions, `EndAt`, `IsA1`-`IsB2`, `NoA2`, `degS`, the
  pins `AnpDetGhRegAt`, `AnpIH`, `AnpDetGhRegStep`, `AnpCaseI`, `AnpCaseIII`, `AnpDetGhCase*`).
* Section 2: `anpDetGh_of_reg` (the `2^{pq}` regions cover).
* Section 3: the half-distance fact and the ending-edge types.
* Section 4: the A2 replacement on a region, `anpDetGhReg_of_noA2`.
* Section 5: vertex fixing, `anpKey2_fix`.
* Section 6: the step from the regions and the case split.
* Section 7: compiled nonempty instances.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Vocabulary (`7_8:1111-1141`) -/

namespace NGraph

variable {p q : ℕ}

/-- The value of `Γ` with the internal labels restricted to `S` (the LHS of `(kwuyayw)`, `7_8:1119`);
`Γ.val ξ a b` is the case `S = univ`. -/
def valOn (Γ : NGraph p q) {ι : Type*} (ξ : ι → ι → ℝ) (a b : Fin p → ι)
    (S : Finset (Fin q → ι)) : ℝ :=
  ∑ ℓ ∈ S, (Γ.es.map fun e =>
    if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod

/-- The ending edge `k` of the path `𝔓_j` at the end `s` (`s = false`: at `a_j`, the first step; `s = true`: at
`b_j`, the last step) is attached to the internal vertex `α_i` (`7_8:1123-1125`). -/
def EndAt (Γ : NGraph p q) (j : Fin p) (s : Bool) (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  (∃ v : NV p q, (if s = true then (Γ.path j).getLast? else (Γ.path j).head?) = some (k, v)) ∧
    ((Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i)

/-- Type A1 on `𝐃_π` (`7_8:1127`, and the `b_j` version `:1139-1141`): `𝔓_j` has no ghost edge and `α_i` is on
the side of its own end (`π i j = s`). -/
def IsA1 (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  Γ.EndAt j s k i ∧ Γ.noGhostPath j = true ∧ π i j = s

/-- Type A2 on `𝐃_π` (`7_8:1130`): `𝔓_j` has no ghost edge and `α_i` is on the side of the other end. -/
def IsA2 (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  Γ.EndAt j s k i ∧ Γ.noGhostPath j = true ∧ π i j = !s

/-- Type B1 (`7_8:1134`): `𝔓_j` has a ghost edge, and it is not this one. -/
def IsB1 (Γ : NGraph p q) (_π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  Γ.EndAt j s k i ∧ Γ.noGhostPath j = false ∧ (Γ.es.get k).ghost = false

/-- Type B2 (`7_8:1136`): this ending edge is the ghost edge of `𝔓_j` (`π` unused, kept for uniformity). -/
def IsB2 (Γ : NGraph p q) (_π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Prop :=
  Γ.EndAt j s k i ∧ (Γ.es.get k).ghost = true

/-- `(eq:noA2)` (`7_8:1146`) on `𝐃_π`. -/
def NoA2 (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Prop :=
  ∀ (j : Fin p) (s : Bool) (k : Fin Γ.es.length) (i : Fin q), ¬ Γ.IsA2 π j s k i

/-- `deg_s(α_i)`: the number of solid edges at `α_i` (`7_8:1247`). -/
def degS (Γ : NGraph p q) (i : Fin q) : ℕ :=
  (Γ.es.filter fun e => !e.ghost && (decide (e.u = Sum.inr i) || decide (e.v = Sum.inr i))).length

instance anpKey2_decEndAt (Γ : NGraph p q) (j : Fin p) (s : Bool) (k : Fin Γ.es.length)
    (i : Fin q) : Decidable (Γ.EndAt j s k i) := by unfold EndAt; infer_instance

instance anpKey2_decIsA1 (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Decidable (Γ.IsA1 π j s k i) := by unfold IsA1; infer_instance

instance anpKey2_decIsA2 (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Decidable (Γ.IsA2 π j s k i) := by unfold IsA2; infer_instance

instance anpKey2_decIsB1 (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Decidable (Γ.IsB1 π j s k i) := by unfold IsB1; infer_instance

instance anpKey2_decIsB2 (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) : Decidable (Γ.IsB2 π j s k i) := by unfold IsB2; infer_instance

instance anpKey2_decNoA2 (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Decidable (Γ.NoA2 π) := by
  unfold NoA2; infer_instance

end NGraph

/-- `Γ.val ξ a b` is the case `S = univ` of `valOn`. -/
theorem anpKey2_val_eq_valOn {p q : ℕ} (Γ : NGraph p q) {ι : Type*} [Fintype ι] (ξ : ι → ι → ℝ)
    (a b : Fin p → ι) : Γ.val ξ a b = Γ.valOn ξ a b Finset.univ := rfl

/-- The region `𝐃_π` (`7_8:1113`): `π i j = true` iff `α_i` is strictly closer to `b_j` than to `a_j`
(`π_{i,j} = 1`); `π i j = false` iff `|α_i - a_j| ≤ |α_i - b_j|` (`π_{i,j} = 0`). -/
def anpKey2_region {d L p q : ℕ} [NeZero L] (a b : Fin p → Zd d L) (π : Fin q → Fin p → Bool) :
    Finset (Fin q → Zd d L) :=
  Finset.univ.filter fun ℓ => ∀ (i : Fin q) (j : Fin p),
    (π i j = true ↔ zdistInf d L (ℓ i - b j) < zdistInf d L (ℓ i - a j))

/-- The one-vertex region: the constraint of `𝐃_π` on a single (fixed) vertex `x`, row `π_{i,·}`. -/
def anpKey2_regionOne {d L p : ℕ} [NeZero L] (a b : Fin p → Zd d L) (π : Fin p → Bool) :
    Finset (Zd d L) :=
  Finset.univ.filter fun x => ∀ j : Fin p,
    (π j = true ↔ zdistInf d L (x - b j) < zdistInf d L (x - a j))

/-- The label of an endpoint of a path of the fixed graph: `none` is the fixed vertex (label `x`), `some o` the old
external vertex `o` (`7_8:1214-1228`: `a_{j,r}, b_{j,r} ∈ {a_j, b_j, α_q}`). -/
def anpKey2_fixLab {p : ℕ} {ι : Type*} (a b : Fin p → ι) (x : ι) (o : Option (Fin p ⊕ Fin p)) : ι :=
  o.elim x (Sum.elim a b)

/-- `(kwuyayw)` (`7_8:1118-1121`), deterministic, on the region `𝐃_π`: the right side of `AnpDetGhAt`. -/
def AnpDetGhRegAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          Γ.valOn ξ a b (anpKey2_region a b π) ≤ C * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
            ∏ i, (if Γ.noGhostPath i = true then
              ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)

/-- The induction hypothesis of `AnpDetGhStep` (`7_8:1107`, in the stronger form of LW-12a: every graph with fewer
internal vertices, any number of paths and edges). -/
def AnpIH (d q : ℕ) : Prop :=
  ∀ (p' k : ℕ), k < q → ∀ Γ' : NGraph p' k, Γ'.GhostOK → Γ'.IsNested → AnpDetGhAt d Γ'

/-- The step on regions (`7_8:1149-1151`): `(kwuyayw)` under `(eq:noA2)` and the induction hypothesis. -/
def AnpDetGhRegStep (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → AnpIH d q →
    ∀ (p : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → Γ.NoA2 π → AnpDetGhRegAt d Γ π

/-- Cases (I)+(II) (`7_8:1152-1244`): an internal vertex with two distinct ending edges of type A1 or B1. -/
def AnpCaseI {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Prop :=
  ∃ (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool) (k₁ k₂ : Fin Γ.es.length), (j₁, s₁) ≠ (j₂, s₂) ∧
    (Γ.IsA1 π j₁ s₁ k₁ i ∨ Γ.IsB1 π j₁ s₁ k₁ i) ∧ (Γ.IsA1 π j₂ s₂ k₂ i ∨ Γ.IsB1 π j₂ s₂ k₂ i)

/-- Case (III) (`7_8:1245-1384`): an internal vertex with two distinct B2 ending edges and `deg_s = 2`. -/
def AnpCaseIII {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) : Prop :=
  ∃ (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool) (k₁ k₂ : Fin Γ.es.length), (j₁, s₁) ≠ (j₂, s₂) ∧
    Γ.IsB2 π j₁ s₁ k₁ i ∧ Γ.IsB2 π j₂ s₂ k₂ i ∧ Γ.degS i = 2

/-- LW-12c (`AnpKey3`): `(kwuyayw_case1)` and Case (II) (`7_8:1196-1244`). -/
def AnpDetGhCaseI (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → AnpIH d q →
    ∀ (p : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → Γ.NoA2 π → AnpCaseI Γ π → AnpDetGhRegAt d Γ π

/-- LW-12d (`AnpKey4`): `(kwuyayw_case3)` (`7_8:1376-1384`). -/
def AnpDetGhCaseIII (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → AnpIH d q →
    ∀ (p : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → Γ.NoA2 π → AnpCaseIII Γ π → AnpDetGhRegAt d Γ π

/-- LW-12e + LW-12f (`AnpKey5`, `AnpKey6`): Case (IV), `(kwuyayw_ng)`, `(kwuyayw_ng_tree)` (`7_8:1385-1599`). -/
def AnpDetGhCaseIV (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → AnpIH d q →
    ∀ (p : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool),
      Γ.GhostOK → Γ.IsNested → Γ.NoA2 π → ¬ AnpCaseI Γ π → ¬ AnpCaseIII Γ π → AnpDetGhRegAt d Γ π

/-! ## 2. The regions cover (`7_8:1116-1118`) -/

/-- Target 2: `(kwuyayw)` for every `π` gives `(adsuu22)` (`7_8:1116-1118`: the `2^{pq}` regions cover). -/
theorem anpDetGh_of_reg (d p q : ℕ) (Γ : NGraph p q) (h : ∀ π, AnpDetGhRegAt d Γ π) :
    AnpDetGhAt d Γ := by
  classical
  choose C c hC hc hc1 H using h
  let π₀ : Fin q → Fin p → Bool := fun _ _ => false
  have hne : (Finset.univ : Finset (Fin q → Fin p → Bool)).Nonempty := ⟨π₀, Finset.mem_univ _⟩
  set c₀ : ℝ := Finset.univ.inf' hne c with hc₀
  have hc₀le : ∀ π, c₀ ≤ c π := fun π => Finset.inf'_le c (Finset.mem_univ π)
  have hCpos : 0 < ∑ π, C π := Finset.sum_pos (fun π _ => hC π) hne
  refine ⟨∑ π, C π, c₀, hCpos, (Finset.lt_inf'_iff hne).2 fun π _ => hc π,
    (hc₀le π₀).trans (hc1 π₀), ?_⟩
  intro L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
  -- the regions partition the torus
  have hsplit : Γ.val ξ a b = ∑ π, Γ.valOn ξ a b (anpKey2_region a b π) := by
    rw [anpKey2_val_eq_valOn]
    unfold NGraph.valOn
    let g : (Fin q → Zd d L) → (Fin q → Fin p → Bool) := fun ℓ i j =>
      decide (zdistInf d L (ℓ i - b j) < zdistInf d L (ℓ i - a j))
    rw [← Finset.sum_fiberwise Finset.univ g]
    refine Finset.sum_congr rfl fun π _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext ℓ
    simp only [anpKey2_region, Finset.mem_filter, Finset.mem_univ, true_and, g]
    constructor
    · intro h i j
      rw [← h]
      simp
    · intro h
      funext i j
      by_cases hP : zdistInf d L (ℓ i - b j) < zdistInf d L (ℓ i - a j)
      · simp [hP, (h i j).2 hP]
      · have h' : π i j ≠ true := fun h' => hP ((h i j).1 h')
        simp [hP, Bool.eq_false_iff.2 h']
  have hc₀pos : 0 < c₀ := (Finset.lt_inf'_iff hne).2 fun π _ => hc π
  have hψ0 : 0 < ψ 0 := hpos 0 le_rfl
  have hpow : 0 ≤ θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) :=
    mul_nonneg (pow_pos hθ q).le (zpow_pos hψ0 _).le
  -- the factor with `c₀` dominates the one with `c π`
  have hfac : ∀ π, ∏ i, (if Γ.noGhostPath i = true then
        ψ (c π * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) ≤
      ∏ i, (if Γ.noGhostPath i = true then
        ψ (c₀ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) := by
    intro π
    refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
    · split_ifs
      · exact (hpos _ (mul_nonneg (hc π).le (Nat.cast_nonneg _))).le
      · exact zero_le_one
    · split_ifs
      · exact hanti (Set.mem_Ici.2 (mul_nonneg hc₀pos.le (Nat.cast_nonneg _)))
          (Set.mem_Ici.2 (mul_nonneg (hc π).le (Nat.cast_nonneg _)))
          (mul_le_mul_of_nonneg_right (hc₀le π) (Nat.cast_nonneg _))
      · exact le_rfl
  have hF0 : 0 ≤ ∏ i, (if Γ.noGhostPath i = true then
        ψ (c₀ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) :=
    Finset.prod_nonneg fun i _ => by
      split_ifs
      · exact (hpos _ (mul_nonneg hc₀pos.le (Nat.cast_nonneg _))).le
      · exact zero_le_one
  calc Γ.val ξ a b = ∑ π, Γ.valOn ξ a b (anpKey2_region a b π) := hsplit
    _ ≤ ∑ π, C π * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) * ∏ i, (if Γ.noGhostPath i = true then
        ψ (c₀ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) := by
        refine Finset.sum_le_sum fun π _ => ?_
        refine (H π L ψ θ hanti hpos hθ ξ hξ hξψ hrow a b).trans ?_
        refine mul_le_mul_of_nonneg_left (hfac π) ?_
        rw [mul_assoc]
        exact mul_nonneg (hC π).le hpow
    _ = _ := by simp only [← Finset.sum_mul]

/-! ## 3. The half-distance fact and the ending-edge types (`7_8:1126-1141`) -/

/-- `|z - x| ≤ |z - y|` gives `|x - y| ≤ 2 |z - y|` (`7_8:1128`, `:1131`): the triangle inequality. -/
theorem anpKey2_half (d L : ℕ) [NeZero L] (x y z : Zd d L)
    (h : zdistInf d L (z - x) ≤ zdistInf d L (z - y)) :
    zdistInf d L (x - y) ≤ 2 * zdistInf d L (z - y) := by
  have h1 := anpKey_zdistInf_tri x z y
  rw [anpKey_zdistInf_sub_comm x z] at h1
  omega

/-- On `𝐃_π` the far end of the path is at distance `≥ |a_j - b_j|/2` (`7_8:1128`, `:1131`). -/
theorem anpKey2_reg_half (d L p q : ℕ) [NeZero L] (a b : Fin p → Zd d L) (π : Fin q → Fin p → Bool)
    (ℓ : Fin q → Zd d L) (hℓ : ℓ ∈ anpKey2_region a b π) (i : Fin q) (j : Fin p) :
    (π i j = false → zdistInf d L (a j - b j) ≤ 2 * zdistInf d L (ℓ i - b j)) ∧
    (π i j = true → zdistInf d L (a j - b j) ≤ 2 * zdistInf d L (ℓ i - a j)) := by
  have hr := (Finset.mem_filter.1 hℓ).2 i j
  constructor
  · intro h
    have h1 : ¬ (zdistInf d L (ℓ i - b j) < zdistInf d L (ℓ i - a j)) := fun h' => by
      have := hr.2 h'
      rw [h] at this
      exact Bool.false_ne_true this
    exact anpKey2_half d L (a j) (b j) (ℓ i) (not_lt.1 h1)
  · intro h
    have h' := hr.1 h
    have := anpKey2_half d L (b j) (a j) (ℓ i) h'.le
    rw [anpKey_zdistInf_sub_comm (a j) (b j)]
    exact this

/-- Every ending edge at an internal vertex has one of the four types (`7_8:1126-1141`). -/
theorem anpKey2_endTypes (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool)
    (k : Fin Γ.es.length) (i : Fin q) (h : Γ.EndAt j s k i) :
    Γ.IsA1 π j s k i ∨ Γ.IsA2 π j s k i ∨ Γ.IsB1 π j s k i ∨ Γ.IsB2 π j s k i := by
  by_cases hg : (Γ.es.get k).ghost = true
  · exact Or.inr (Or.inr (Or.inr ⟨h, hg⟩))
  · have hg' : (Γ.es.get k).ghost = false := by simpa using hg
    by_cases hn : Γ.noGhostPath j = true
    · by_cases hs : π i j = s
      · exact Or.inl ⟨h, hn, hs⟩
      · refine Or.inr (Or.inl ⟨h, hn, ?_⟩)
        cases s <;> cases hπ : π i j <;> simp_all
    · exact Or.inr (Or.inr (Or.inl ⟨h, by simpa using hn, hg'⟩))

/-- `noGhostPath` as a statement about the steps. -/
theorem anpKey2_noGhost_iff {p q : ℕ} (Γ : NGraph p q) (j : Fin p) :
    Γ.noGhostPath j = true ↔ ∀ st ∈ Γ.path j, (Γ.es.get st.1).ghost = false := by
  unfold NGraph.noGhostPath
  rw [List.all_eq_true]
  simp

theorem anpKey2_ghostStep {p q : ℕ} (Γ : NGraph p q) (j : Fin p) (h : Γ.noGhostPath j = false) :
    ∃ st ∈ Γ.path j, (Γ.es.get st.1).ghost = true := by
  by_contra hcon
  push Not at hcon
  have : Γ.noGhostPath j = true := (anpKey2_noGhost_iff Γ j).2 fun st hst => by
    simpa using hcon st hst
  rw [this] at h
  exact Bool.noConfusion h

/-- Two A1/B1 ending edges at one vertex lie on distinct paths (`7_8:1157`, "by definition"; for LW-12c). -/
theorem anpKey2_caseI_ne {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (hG : Γ.GhostOK)
    {i : Fin q} {j₁ j₂ : Fin p} {s₁ s₂ : Bool} {k₁ k₂ : Fin Γ.es.length}
    (hne : (j₁, s₁) ≠ (j₂, s₂)) (h₁ : Γ.IsA1 π j₁ s₁ k₁ i ∨ Γ.IsB1 π j₁ s₁ k₁ i)
    (h₂ : Γ.IsA1 π j₂ s₂ k₂ i ∨ Γ.IsB1 π j₂ s₂ k₂ i) : j₁ ≠ j₂ := by
  intro hj
  subst hj
  have hs : s₁ ≠ s₂ := fun h => hne (by rw [h])
  rcases h₁ with ⟨e₁, n₁, π₁⟩ | ⟨e₁, n₁, g₁⟩ <;> rcases h₂ with ⟨e₂, n₂, π₂⟩ | ⟨e₂, n₂, g₂⟩
  · exact hs (π₁.symm.trans π₂)
  · rw [n₁] at n₂; exact Bool.noConfusion n₂
  · rw [n₁] at n₂; exact Bool.noConfusion n₂
  · obtain ⟨st, hst, hgh⟩ := anpKey2_ghostStep Γ j₁ n₁
    obtain ⟨⟨v₁, hv₁⟩, -⟩ := e₁
    obtain ⟨⟨v₂, hv₂⟩, -⟩ := e₂
    have hend := (hG j₁).2 st hst hgh
    cases s₁ <;> cases s₂ <;> simp at hs hv₁ hv₂
    · rcases hend with h | h
      · rw [hv₁] at h; cases h; rw [g₁] at hgh; exact Bool.noConfusion hgh
      · rw [hv₂] at h; cases h; rw [g₂] at hgh; exact Bool.noConfusion hgh
    · rcases hend with h | h
      · rw [hv₂] at h; cases h; rw [g₂] at hgh; exact Bool.noConfusion hgh
      · rw [hv₁] at h; cases h; rw [g₁] at hgh; exact Bool.noConfusion hgh

/-! ## 4. The A2 replacement on a region (`7_8:1143-1148`) -/

section Chain

variable {p q : ℕ}

/-- One step of a walk: the edge `st.1` joins the current vertex `c` to `st.2`. -/
def anpKey2_stepOK (Γ : NGraph p q) (c : NV p q) (st : Fin Γ.es.length × NV p q) : Prop :=
  ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨ ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2)

/-- The walk `x ⇝ y` along the steps `l`. -/
def anpKey2_chain (Γ : NGraph p q) : NV p q → List (Fin Γ.es.length × NV p q) → NV p q → Prop
  | x, [], y => x = y
  | x, st :: t, y => anpKey2_stepOK Γ x st ∧ anpKey2_chain Γ st.2 t y

private theorem anpKey2_foldl_none (Γ : NGraph p q) (l : List (Fin Γ.es.length × NV p q)) :
    (l.foldl (fun (acc : Option (NV p q)) st => acc.bind fun c =>
      if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
          ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none) none) = none := by
  induction l with
  | nil => rfl
  | cons st t ih => simpa [List.foldl_cons] using ih

theorem anpKey2_foldl_iff (Γ : NGraph p q) (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q) :
    (l.foldl (fun (acc : Option (NV p q)) st => acc.bind fun c =>
      if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
          ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none) (some x)) = some y ↔
      anpKey2_chain Γ x l y := by
  induction l generalizing x with
  | nil => simp [anpKey2_chain]
  | cons st t ih =>
    rw [List.foldl_cons, anpKey2_chain]
    by_cases hc : ((Γ.es.get st.1).u = x ∧ (Γ.es.get st.1).v = st.2) ∨
        ((Γ.es.get st.1).v = x ∧ (Γ.es.get st.1).u = st.2)
    · have : (Option.bind (some x) fun c =>
          if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
            ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none) = some st.2 := by
        rw [Option.bind_some]
        split_ifs
        rfl
      rw [this, ih]
      exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
    · have : (Option.bind (some x) fun c =>
          if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
            ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none) = none := by
        rw [Option.bind_some]
        split_ifs
        rfl
      rw [this, anpKey2_foldl_none]
      exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 hc⟩

theorem anpKey2_walkOK_iff (Γ : NGraph p q) (j : Fin p) :
    Γ.WalkOK j ↔ anpKey2_chain Γ (Sum.inl (Sum.inl j)) (Γ.path j) (Sum.inl (Sum.inr j)) :=
  anpKey2_foldl_iff Γ _ _ _

theorem anpKey2_chain_append (Γ : NGraph p q) (l₁ l₂ : List (Fin Γ.es.length × NV p q)) (x y : NV p q) :
    anpKey2_chain Γ x (l₁ ++ l₂) y ↔ ∃ z, anpKey2_chain Γ x l₁ z ∧ anpKey2_chain Γ z l₂ y := by
  induction l₁ generalizing x with
  | nil => simp [anpKey2_chain]
  | cons st t ih =>
    simp only [List.cons_append, anpKey2_chain, ih]
    constructor
    · rintro ⟨h1, z, h2, h3⟩; exact ⟨z, ⟨h1, h2⟩, h3⟩
    · rintro ⟨z, ⟨h1, h2⟩, h3⟩; exact ⟨h1, z, h2, h3⟩

theorem anpKey2_chain_snoc (Γ : NGraph p q) (l : List (Fin Γ.es.length × NV p q))
    (st : Fin Γ.es.length × NV p q) (x y : NV p q) :
    anpKey2_chain Γ x (l ++ [st]) y ↔ ∃ z, anpKey2_chain Γ x l z ∧ anpKey2_stepOK Γ z st ∧ st.2 = y := by
  rw [anpKey2_chain_append]
  simp only [anpKey2_chain]

theorem anpKey2_chain_end (Γ : NGraph p q) (l : List (Fin Γ.es.length × NV p q)) (st : Fin Γ.es.length × NV p q)
    (x y : NV p q) (h : anpKey2_chain Γ x (l ++ [st]) y) : y = st.2 := by
  obtain ⟨z, -, -, h3⟩ := (anpKey2_chain_snoc Γ l st x y).1 h
  exact h3.symm

/-- A walk from `x ≠ α` that has a step with an edge at `α` has a step arriving at `α`. -/
theorem anpKey2_chain_visit (Γ : NGraph p q) (α : NV p q) :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q), anpKey2_chain Γ x l y → x ≠ α →
      (∃ st ∈ l, (Γ.es.get st.1).u = α ∨ (Γ.es.get st.1).v = α) → ∃ st ∈ l, st.2 = α := by
  intro l
  induction l with
  | nil => intro x y _ _ ⟨st, hst, _⟩; simp at hst
  | cons st t ih =>
    intro x y h hx ⟨st', hst', hα⟩
    obtain ⟨hstep, hrest⟩ := h
    by_cases h2 : st.2 = α
    · exact ⟨st, List.mem_cons_self, h2⟩
    · rcases List.mem_cons.1 hst' with rfl | hmem
      · exfalso
        rcases hstep with ⟨h1, h2'⟩ | ⟨h1, h2'⟩ <;> rcases hα with h | h <;> simp_all
      · obtain ⟨st'', hst'', h3⟩ := ih st.2 y hrest h2 ⟨st', hmem, hα⟩
        exact ⟨st'', List.mem_cons_of_mem _ hst'', h3⟩

/-- The ending edge `k` at `α_i` joins `α_i` to the external end of the path (`a_j` for `s = false`, `b_j` for
`s = true`). -/
theorem anpKey2_endAt_ends {Γ : NGraph p q} {j : Fin p} (hW : Γ.WalkOK j) {s : Bool}
    {k : Fin Γ.es.length} {i : Fin q} (h : Γ.EndAt j s k i) :
    (((Γ.es.get k).u = (if s = true then Sum.inl (Sum.inr j) else Sum.inl (Sum.inl j)) ∧
        (Γ.es.get k).v = Sum.inr i) ∨
      ((Γ.es.get k).v = (if s = true then Sum.inl (Sum.inr j) else Sum.inl (Sum.inl j)) ∧
        (Γ.es.get k).u = Sum.inr i)) := by
  obtain ⟨⟨v, hv⟩, hi⟩ := h
  have hch := (anpKey2_walkOK_iff Γ j).1 hW
  cases s
  · simp only [Bool.false_eq_true, ite_false] at hv ⊢
    obtain ⟨t, ht⟩ : ∃ t, Γ.path j = (k, v) :: t := by
      cases hp : Γ.path j with
      | nil => rw [hp] at hv; simp at hv
      | cons x t => rw [hp] at hv; simp at hv; exact ⟨t, by rw [hv]⟩
    rw [ht] at hch
    rcases hch.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with h | h <;> simp_all
  · simp only [ite_true] at hv ⊢
    obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 hv
    rw [hl] at hch
    obtain ⟨z, -, hstep, hend⟩ := (anpKey2_chain_snoc Γ l (k, v) _ _).1 hch
    simp only at hend
    rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with h | h <;> simp_all

end Chain

section A2

variable {p q : ℕ}

/-- The product of the edge factors of `Γ` at the labelling `lab`. -/
def anpKey2_ep {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (lab : NV p q → ι) : ℝ :=
  (Γ.es.map fun e => if e.ghost then (1 : ℝ) else ξ (lab e.u) (lab e.v)).prod

theorem anpKey2_ep_nonneg {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (hξ : ∀ α β, 0 ≤ ξ α β)
    (lab : NV p q → ι) : 0 ≤ anpKey2_ep Γ ξ lab := by
  unfold anpKey2_ep
  refine List.prod_nonneg fun x hx => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact zero_le_one
  · exact hξ _ _

private theorem anpKey2_prod_set {α : Type*} (f : α → ℝ) (e' : α) :
    ∀ (l : List α) (n : ℕ) (hn : n < l.length),
      (l.map f).prod * f e' = ((l.set n e').map f).prod * f l[n]
  | [], n, hn => absurd hn (by simp)
  | x :: t, 0, _ => by simp [List.set]; ring
  | x :: t, n + 1, hn => by
    have hn' : n < t.length := by simpa using hn
    have ih := anpKey2_prod_set f e' t n hn'
    simp only [List.set_cons_succ, List.map_cons, List.prod_cons, List.getElem_cons_succ]
    calc f x * (t.map f).prod * f e' = f x * ((t.map f).prod * f e') := by ring
      _ = f x * (((t.set n e').map f).prod * f t[n]) := by rw [ih]
      _ = _ := by ring

/-- The A2 replacement turns one solid factor into `1`. -/
theorem anpKey2_ep_ghostify {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (lab : NV p q → ι)
    (k : Fin Γ.es.length) (hk : (Γ.es.get k).ghost = false) :
    anpKey2_ep Γ ξ lab = ξ (lab (Γ.es.get k).u) (lab (Γ.es.get k).v) * anpKey2_ep (Γ.ghostify k) ξ lab := by
  unfold anpKey2_ep
  have h := anpKey2_prod_set (fun e : NEdge p q => if e.ghost then (1 : ℝ) else ξ (lab e.u) (lab e.v))
    { Γ.es[k.1] with ghost := true } Γ.es k.1 k.2
  have hk' : Γ.es[k.1].ghost = false := hk
  simp only [hk', Bool.false_eq_true, ite_false, ite_true, mul_one] at h
  show _ = _ * (((Γ.es.set k.1 { Γ.es[k.1] with ghost := true }).map _).prod)
  rw [h, mul_comm]
  rfl

end A2

section A2b

variable {d L p q : ℕ} [NeZero L]

omit [NeZero L] in
/-- `ξ_{xy} ≤ ψ(r/2)` once `r ≤ 2 |y - x|` (for both orders of the arguments). -/
private theorem anpKey2_xi_le (ψ : ℝ → ℝ) (hanti : AntitoneOn ψ (Set.Ici 0)) (ξ : Zd d L → Zd d L → ℝ)
    (hsym : ∀ α β, ξ α β = ξ β α) (hξψ : ∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ))
    (x y : Zd d L) (r : ℕ) (h : r ≤ 2 * zdistInf d L (y - x)) :
    ξ x y ≤ ψ ((r : ℝ) / 2) ∧ ξ y x ≤ ψ ((r : ℝ) / 2) := by
  have h1 : ξ y x ≤ ψ ((r : ℝ) / 2) := by
    refine (hξψ y x).trans (hanti (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 (Nat.cast_nonneg _)) ?_)
    have : (r : ℝ) ≤ 2 * ((zdistInf d L (y - x) : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  exact ⟨(hsym x y).symm ▸ h1, h1⟩

/-- The factor of an A2 ending edge is at most `ψ(|a_j - b_j|/2)` on `𝐃_π` (`7_8:1143-1145`). -/
theorem anpKey2_A2_factor (Γ : NGraph p q) (π : Fin q → Fin p → Bool)
    (ψ : ℝ → ℝ) (hanti : AntitoneOn ψ (Set.Ici 0)) (ξ : Zd d L → Zd d L → ℝ)
    (hsym : ∀ α β, ξ α β = ξ β α) (hξψ : ∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ))
    (a b : Fin p → Zd d L) (ℓ : Fin q → Zd d L) (hℓ : ℓ ∈ anpKey2_region a b π)
    {j : Fin p} {s : Bool} {k : Fin Γ.es.length} {i : Fin q} (hW : Γ.WalkOK j)
    (hA : Γ.IsA2 π j s k i) :
    ξ (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).u) (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).v) ≤
      ψ (((zdistInf d L (a j - b j) : ℕ) : ℝ) / 2) := by
  obtain ⟨hE, -, hπ⟩ := hA
  have hends := anpKey2_endAt_ends hW hE
  have hrh := anpKey2_reg_half d L p q a b π ℓ hℓ i j
  cases s
  · have hπ' : π i j = true := by simpa using hπ
    have key := anpKey2_xi_le ψ hanti ξ hsym hξψ (a j) (ℓ i) _ (hrh.2 hπ')
    simp only [Bool.false_eq_true, ite_false] at hends
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [key.1, key.2]
  · have hπ' : π i j = false := by simpa using hπ
    have key := anpKey2_xi_le ψ hanti ξ hsym hξψ (b j) (ℓ i) _ (hrh.1 hπ')
    simp only [ite_true] at hends
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [key.1, key.2]

/-- On `𝐃_π` an A2 edge contributes at most `ψ(|a_j - b_j|/2)`; the rest is the value of `Γ̃`
(`7_8:1143-1148`). -/
theorem anpKey2_A2_val (Γ : NGraph p q) (π : Fin q → Fin p → Bool)
    (ψ : ℝ → ℝ) (hanti : AntitoneOn ψ (Set.Ici 0)) (ξ : Zd d L → Zd d L → ℝ)
    (hnn : ∀ α β, 0 ≤ ξ α β)
    (hsym : ∀ α β, ξ α β = ξ β α) (hξψ : ∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ))
    (a b : Fin p → Zd d L) {j : Fin p} {s : Bool} {k : Fin Γ.es.length} {i : Fin q} (hW : Γ.WalkOK j)
    (hA : Γ.IsA2 π j s k i) (hk : (Γ.es.get k).ghost = false) :
    Γ.valOn ξ a b (anpKey2_region a b π) ≤
      ψ (((zdistInf d L (a j - b j) : ℕ) : ℝ) / 2) * (Γ.ghostify k).valOn ξ a b (anpKey2_region a b π) := by
  unfold NGraph.valOn
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ℓ hℓ => ?_
  show anpKey2_ep Γ ξ (Sum.elim (Sum.elim a b) ℓ) ≤ _ * anpKey2_ep (Γ.ghostify k) ξ (Sum.elim (Sum.elim a b) ℓ)
  rw [anpKey2_ep_ghostify Γ ξ _ k hk]
  exact mul_le_mul_of_nonneg_right (anpKey2_A2_factor Γ π ψ hanti ξ hsym hξψ a b ℓ hℓ hW hA)
    (anpKey2_ep_nonneg _ ξ hnn _)

end A2b

/-- Target 4: the A2 replacement on a region (`7_8:1143-1148`): it suffices to prove `(kwuyayw)` under
`(eq:noA2)`, for the same `p`, `q`, `π`.  Strong induction on `n_ngh`: each replacement of an A2 edge by a
ghost edge lowers `n_ngh` by one, keeps `ord - n_ngh`, and costs the factor `ψ(|a_j - b_j|/2) ≤ ψ(c' |a_j - b_j|)`
with `c' = min c (1/2)`. -/
theorem anpDetGhReg_of_noA2 (d p q : ℕ) (π : Fin q → Fin p → Bool)
    (h : ∀ Γ : NGraph p q, Γ.GhostOK → Γ.IsNested → Γ.NoA2 π → AnpDetGhRegAt d Γ π) :
    ∀ Γ : NGraph p q, Γ.GhostOK → Γ.IsNested → AnpDetGhRegAt d Γ π := by
  suffices H : ∀ n, ∀ Γ : NGraph p q, Γ.nngh = n → Γ.GhostOK → Γ.IsNested → AnpDetGhRegAt d Γ π from
    fun Γ hG hN => H _ Γ rfl hG hN
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ hn hG hN
    by_cases hno : Γ.NoA2 π
    · exact h Γ hG hN hno
    · simp only [NGraph.NoA2, not_forall, not_not] at hno
      obtain ⟨j, s, k, i, hA⟩ := hno
      obtain ⟨⟨⟨v, hv⟩, hedge⟩, hnj, hπ⟩ := hA
      have hmem : (k, v) ∈ Γ.path j ∧
          ((Γ.path j).head? = some (k, v) ∨ (Γ.path j).getLast? = some (k, v)) := by
        cases s
        · simp only [Bool.false_eq_true, ite_false] at hv
          exact ⟨List.mem_of_mem_head? hv, Or.inl hv⟩
        · simp only [ite_true] at hv
          exact ⟨List.mem_of_getLast? hv, Or.inr hv⟩
      have hnS : (Γ.ghostify k).nngh + 1 = Γ.nngh := anpKey_ghostify_nngh Γ hN hnj hmem.1
      have hord : (Γ.ghostify k).ordN - ((Γ.ghostify k).nngh : ℤ) = Γ.ordN - (Γ.nngh : ℤ) :=
        anpKey_ghostify_ord Γ hN hnj hmem.1
      have hG' : (Γ.ghostify k).GhostOK := anpKey_ghostify_ghostOK Γ hG hN hnj hmem.1 hmem.2
      have hN' : (Γ.ghostify k).IsNested := anpKey_ghostify_nested Γ k hN
      obtain ⟨C, c, hC, hc, hc1, hbd⟩ := ih _ (by omega) (Γ.ghostify k) rfl hG' hN'
      have hnoG := anpKey_gf_noGhostPath_iff Γ hN hmem.1
      have hA : Γ.IsA2 π j s k i := ⟨⟨⟨v, hv⟩, hedge⟩, hnj, hπ⟩
      have hk : (Γ.es.get k).ghost = false := (anpKey2_noGhost_iff Γ j).1 hnj _ hmem.1
      refine ⟨C, min c (1 / 2), hC, lt_min hc (by norm_num), (min_le_right _ _).trans (by norm_num), ?_⟩
      intro L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
      have hbd' := hbd L ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
      have hval := anpKey2_A2_val Γ π ψ hanti ξ (fun α β => (hξ α β).1) (fun α β => (hξ α β).2) hξψ a b
        (hN.2.1 j) hA hk
      set r : ℝ := ((zdistInf d L (a j - b j) : ℕ) : ℝ) with hr
      have hr0 : 0 ≤ r := Nat.cast_nonneg _
      have hψ0 : 0 < ψ 0 := hpos 0 le_rfl
      have hpow : 0 ≤ C * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) :=
        mul_nonneg (mul_nonneg hC.le (pow_pos hθ q).le) (zpow_pos hψ0 _).le
      have hcm : min c (1 / 2) ≤ c := min_le_left _ _
      have hcm2 : min c (1 / 2) ≤ 1 / 2 := min_le_right _ _
      have hcpos : 0 < min c (1 / 2) := lt_min hc (by norm_num)
      -- the product of the path factors
      have hprod : ψ (r / 2) * ∏ i, (if (Γ.ghostify k).noGhostPath i = true then
            ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) ≤
          ∏ i, (if Γ.noGhostPath i = true then
            ψ (min c (1 / 2) * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) := by
        have hg : ∏ i : Fin p, (if i = j then ψ (r / 2) else (1 : ℝ)) = ψ (r / 2) := by simp
        rw [← hg, ← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
        · refine mul_nonneg ?_ ?_
          · split_ifs
            · exact (hpos _ (by positivity)).le
            · exact zero_le_one
          · split_ifs
            · exact (hpos _ (mul_nonneg hc.le (Nat.cast_nonneg _))).le
            · exact zero_le_one
        · by_cases hij : i = j
          · subst hij
            have h1 : (Γ.ghostify k).noGhostPath i ≠ true := fun h' => ((hnoG i).1 h').2 rfl
            simp only [h1, hnj, Bool.false_eq_true, ↓reduceIte, mul_one]
            have hle : min c (1 / 2) * r ≤ r / 2 := by
              nlinarith [mul_le_mul_of_nonneg_right hcm2 hr0]
            exact hanti (Set.mem_Ici.2 (mul_nonneg hcpos.le hr0)) (Set.mem_Ici.2 (by positivity)) hle
          · simp only [hij, ↓reduceIte, one_mul]
            by_cases hni : Γ.noGhostPath i = true
            · have h1 : (Γ.ghostify k).noGhostPath i = true := (hnoG i).2 ⟨hni, hij⟩
              simp only [h1, hni, ↓reduceIte]
              exact hanti (Set.mem_Ici.2 (mul_nonneg hcpos.le (Nat.cast_nonneg _)))
                (Set.mem_Ici.2 (mul_nonneg hc.le (Nat.cast_nonneg _)))
                (mul_le_mul_of_nonneg_right hcm (Nat.cast_nonneg _))
            · have h1 : (Γ.ghostify k).noGhostPath i ≠ true := fun h' => hni ((hnoG i).1 h').1
              simp only [h1, hni, Bool.false_eq_true, ↓reduceIte, le_refl]
      rw [hord] at hbd'
      calc Γ.valOn ξ a b (anpKey2_region a b π)
          ≤ ψ (r / 2) * (Γ.ghostify k).valOn ξ a b (anpKey2_region a b π) := hval
        _ ≤ ψ (r / 2) * (C * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) * ∏ i, (if (Γ.ghostify k).noGhostPath i = true then
            ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)) :=
            mul_le_mul_of_nonneg_left hbd' (hpos _ (by positivity)).le
        _ = C * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) * (ψ (r / 2) * ∏ i, (if (Γ.ghostify k).noGhostPath i = true then
            ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod hpow

/-! ## 5. Vertex fixing (`7_8:1158-1172`, `:1209-1237`)

The path `𝔓_j` is cut after each step that arrives at `α_{i₀}`: `K_j` arrivals give `K_j + 1` segments `(j, r)`,
`r ≤ K_j`, enumerated by `finSigmaFinEquiv` (`p' = Σ_j (K_j + 1)`).  The segment `(j, r)` starts at `a_j` (`r = 0`)
or at `α_{i₀}`, and ends at `b_j` (`r = K_j`) or at `α_{i₀}`.  The edges of the fixed graph are the edges of `Γ`,
relabelled: `a_j`, `b_j` go to the start of the first / the end of the last segment of `𝔓_j`, `α_i` to its place
among the remaining vertices (`i ≠ i₀`), and `α_{i₀}` to the start (resp. end) of the segment of which the edge is
the first (resp. last) step, else to the end of a fixed segment `s₀` that ends at `α_{i₀}`. -/

section Seg

variable {α : Type*}

/-- Segments of a list cut after each `A`-element: the `r`-th piece is the run between the `r`-th and the
`(r+1)`-st `A`-element (the latter included); there are `countP A l + 1` pieces. -/
def anpKey2_seg (A : α → Bool) : List α → ℕ → List α
  | [], _ => []
  | x :: xs, 0 => if A x then [x] else x :: anpKey2_seg A xs 0
  | x :: xs, r + 1 => if A x then anpKey2_seg A xs r else anpKey2_seg A xs (r + 1)

theorem anpKey2_seg_nil (A : α → Bool) (r : ℕ) : anpKey2_seg A [] r = [] := rfl

theorem anpKey2_seg_zero (A : α → Bool) (x : α) (xs : List α) :
    anpKey2_seg A (x :: xs) 0 = if A x then [x] else x :: anpKey2_seg A xs 0 := rfl

theorem anpKey2_seg_succ (A : α → Bool) (x : α) (xs : List α) (r : ℕ) :
    anpKey2_seg A (x :: xs) (r + 1) = if A x then anpKey2_seg A xs r else anpKey2_seg A xs (r + 1) := rfl

theorem anpKey2_seg_zero_pos (A : α → Bool) {x : α} (xs : List α) (h : A x = true) :
    anpKey2_seg A (x :: xs) 0 = [x] := by simp [anpKey2_seg, h]

theorem anpKey2_seg_zero_neg (A : α → Bool) {x : α} (xs : List α) (h : A x = false) :
    anpKey2_seg A (x :: xs) 0 = x :: anpKey2_seg A xs 0 := by simp [anpKey2_seg, h]

theorem anpKey2_seg_succ_pos (A : α → Bool) {x : α} (xs : List α) (r : ℕ) (h : A x = true) :
    anpKey2_seg A (x :: xs) (r + 1) = anpKey2_seg A xs r := by simp [anpKey2_seg, h]

theorem anpKey2_seg_succ_neg (A : α → Bool) {x : α} (xs : List α) (r : ℕ) (h : A x = false) :
    anpKey2_seg A (x :: xs) (r + 1) = anpKey2_seg A xs (r + 1) := by simp [anpKey2_seg, h]

theorem anpKey2_seg_sublist (A : α → Bool) : ∀ (l : List α) (r : ℕ), (anpKey2_seg A l r).Sublist l
  | [], r => by simp [anpKey2_seg]
  | x :: xs, 0 => by
    unfold anpKey2_seg
    split_ifs
    · exact (List.nil_sublist _).cons_cons _
    · exact (anpKey2_seg_sublist A xs 0).cons_cons _
  | x :: xs, r + 1 => by
    unfold anpKey2_seg
    split_ifs
    · exact (anpKey2_seg_sublist A xs r).cons _
    · exact (anpKey2_seg_sublist A xs (r + 1)).cons _

theorem anpKey2_seg_nil_of_gt (A : α → Bool) :
    ∀ (l : List α) (r : ℕ), l.countP A < r → anpKey2_seg A l r = []
  | [], r, _ => by simp [anpKey2_seg]
  | x :: xs, 0, h => by omega
  | x :: xs, r + 1, h => by
    unfold anpKey2_seg
    by_cases hx : A x = true
    · simp only [hx, ite_true]
      refine anpKey2_seg_nil_of_gt A xs r ?_
      rw [List.countP_cons_of_pos hx] at h; omega
    · simp only [hx]
      refine anpKey2_seg_nil_of_gt A xs (r + 1) ?_
      rw [List.countP_cons_of_neg hx] at h; omega

theorem anpKey2_seg_cover (A : α → Bool) :
    ∀ (l : List α) (y : α), y ∈ l → ∃ r ≤ l.countP A, y ∈ anpKey2_seg A l r
  | [], y, h => by simp at h
  | x :: xs, y, h => by
    by_cases hx : A x = true
    · rcases List.mem_cons.1 h with rfl | hy
      · exact ⟨0, Nat.zero_le _, by simp [anpKey2_seg, hx]⟩
      · obtain ⟨r, hr, hmem⟩ := anpKey2_seg_cover A xs y hy
        refine ⟨r + 1, ?_, ?_⟩
        · rw [List.countP_cons_of_pos hx]; omega
        · simpa [anpKey2_seg, hx] using hmem
    · rcases List.mem_cons.1 h with rfl | hy
      · exact ⟨0, Nat.zero_le _, by simp [anpKey2_seg, hx]⟩
      · obtain ⟨r, hr, hmem⟩ := anpKey2_seg_cover A xs y hy
        rcases r with _ | r
        · exact ⟨0, Nat.zero_le _, by simp [anpKey2_seg, hx, hmem]⟩
        · refine ⟨r + 1, ?_, ?_⟩
          · rw [List.countP_cons_of_neg hx]; omega
          · simpa [anpKey2_seg, hx] using hmem

theorem anpKey2_seg_unique (A : α → Bool) :
    ∀ (l : List α), l.Nodup → ∀ (r r' : ℕ) (y : α), y ∈ anpKey2_seg A l r → y ∈ anpKey2_seg A l r' → r = r'
  | [], _, r, r', y, h, _ => by simp [anpKey2_seg] at h
  | x :: xs, hnd, r, r', y, h, h' => by
    have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
    have hxs : xs.Nodup := (List.nodup_cons.1 hnd).2
    have hsub : ∀ r, ∀ z ∈ anpKey2_seg A xs r, z ∈ xs := fun r z hz =>
      (anpKey2_seg_sublist A xs r).subset hz
    cases hA : A x
    · rcases r with _ | r <;> rcases r' with _ | r'
      · rfl
      · rw [anpKey2_seg_zero_neg A xs hA, List.mem_cons] at h
        rw [anpKey2_seg_succ_neg A xs _ hA] at h'
        rcases h with rfl | h
        · exact absurd (hsub _ _ h') hx
        · exact absurd (anpKey2_seg_unique A xs hxs 0 (r' + 1) y h h') (by omega)
      · rw [anpKey2_seg_succ_neg A xs _ hA] at h
        rw [anpKey2_seg_zero_neg A xs hA, List.mem_cons] at h'
        rcases h' with rfl | h'
        · exact absurd (hsub _ _ h) hx
        · exact absurd (anpKey2_seg_unique A xs hxs (r + 1) 0 y h h') (by omega)
      · rw [anpKey2_seg_succ_neg A xs _ hA] at h h'
        exact anpKey2_seg_unique A xs hxs (r + 1) (r' + 1) y h h'
    · rcases r with _ | r <;> rcases r' with _ | r'
      · rfl
      · rw [anpKey2_seg_zero_pos A xs hA, List.mem_singleton] at h
        rw [anpKey2_seg_succ_pos A xs _ hA] at h'
        subst h; exact absurd (hsub _ _ h') hx
      · rw [anpKey2_seg_succ_pos A xs _ hA] at h
        rw [anpKey2_seg_zero_pos A xs hA, List.mem_singleton] at h'
        subst h'; exact absurd (hsub _ _ h) hx
      · rw [anpKey2_seg_succ_pos A xs _ hA] at h h'
        exact congrArg (· + 1) (anpKey2_seg_unique A xs hxs r r' y h h')

/-- The shape of the pieces: below the last one a piece is a run without `A` ended by one `A`-element; the last
piece has no `A`-element. -/
theorem anpKey2_seg_shape (A : α → Bool) :
    ∀ (l : List α) (r : ℕ), r < l.countP A →
      ∃ (T₀ : List α) (z : α), anpKey2_seg A l r = T₀ ++ [z] ∧ A z = true ∧ ∀ x ∈ T₀, A x = false
  | [], r, h => by simp at h
  | x :: xs, r, h => by
    cases hA : A x
    · rw [List.countP_cons_of_neg (by simpa using hA)] at h
      rcases r with _ | r
      · obtain ⟨T₀, z, h1, h2, h3⟩ := anpKey2_seg_shape A xs 0 h
        refine ⟨x :: T₀, z, ?_, h2, ?_⟩
        · rw [anpKey2_seg_zero_neg A xs hA, h1]; rfl
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hA
          · exact h3 y hy
      · obtain ⟨T₀, z, h1, h2, h3⟩ := anpKey2_seg_shape A xs (r + 1) h
        exact ⟨T₀, z, by rw [anpKey2_seg_succ_neg A xs _ hA, h1], h2, h3⟩
    · rw [List.countP_cons_of_pos hA] at h
      rcases r with _ | r
      · exact ⟨[], x, by rw [anpKey2_seg_zero_pos A xs hA]; rfl, hA, by simp⟩
      · obtain ⟨T₀, z, h1, h2, h3⟩ := anpKey2_seg_shape A xs r (by omega)
        exact ⟨T₀, z, by rw [anpKey2_seg_succ_pos A xs _ hA, h1], h2, h3⟩

theorem anpKey2_seg_last (A : α → Bool) :
    ∀ (l : List α) (K : ℕ), l.countP A = K → ∀ x ∈ anpKey2_seg A l K, A x = false
  | [], K, _ => by simp [anpKey2_seg]
  | x :: xs, K, hK => by
    intro y hy
    cases hA : A x
    · rw [List.countP_cons_of_neg (by simpa using hA)] at hK
      rcases K with _ | K
      · rw [anpKey2_seg_zero_neg A xs hA, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hA
        · exact anpKey2_seg_last A xs 0 hK y hy
      · rw [anpKey2_seg_succ_neg A xs _ hA] at hy
        exact anpKey2_seg_last A xs (K + 1) hK y hy
    · rw [List.countP_cons_of_pos hA] at hK
      obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      rw [anpKey2_seg_succ_pos A xs _ hA] at hy
      exact anpKey2_seg_last A xs K (by omega) y hy

/-- Appending one element extends the piece `countP` by it. -/
theorem anpKey2_seg_snoc (A : α → Bool) :
    ∀ (l : List α) (x : α) (r : ℕ),
      anpKey2_seg A (l ++ [x]) r = anpKey2_seg A l r ++ (if r = l.countP A then [x] else [])
  | [], x, r => by
    rcases r with _ | r
    · cases hA : A x <;> simp [anpKey2_seg, hA]
    · cases hA : A x <;> simp [anpKey2_seg, hA]
  | y :: l, x, r => by
    rcases r with _ | r
    · cases hA : A y
      · rw [List.cons_append, anpKey2_seg_zero_neg A _ hA, anpKey2_seg_zero_neg A _ hA,
          anpKey2_seg_snoc A l x 0, List.countP_cons_of_neg (by simpa using hA)]
        simp
      · rw [List.cons_append, anpKey2_seg_zero_pos A _ hA, anpKey2_seg_zero_pos A _ hA,
          List.countP_cons_of_pos hA]
        simp
    · cases hA : A y
      · rw [List.cons_append, anpKey2_seg_succ_neg A _ _ hA, anpKey2_seg_succ_neg A _ _ hA,
          anpKey2_seg_snoc A l x (r + 1), List.countP_cons_of_neg (by simpa using hA)]
      · rw [List.cons_append, anpKey2_seg_succ_pos A _ _ hA, anpKey2_seg_succ_pos A _ _ hA,
          anpKey2_seg_snoc A l x r, List.countP_cons_of_pos hA]
        simp

theorem anpKey2_seg_head (A : α → Bool) (x : α) (xs : List α) :
    ∃ t, anpKey2_seg A (x :: xs) 0 = x :: t := by
  cases hA : A x
  · exact ⟨_, anpKey2_seg_zero_neg A xs hA⟩
  · exact ⟨[], anpKey2_seg_zero_pos A xs hA⟩

end Seg

section SegChain

variable {p q : ℕ}

/-- The arrival test: the step ends at `α`. -/
def anpKey2_isA {n : ℕ} (α : NV p q) (st : Fin n × NV p q) : Bool := decide (st.2 = α)

theorem anpKey2_isA_eq (α : NV p q) {n : ℕ} (st : Fin n × NV p q) :
    anpKey2_isA α st = true ↔ st.2 = α := by simp [anpKey2_isA]

/-- A walk splits at the visits of `α`: the `r`-th piece goes from `α` (or the start) to `α` (or the end). -/
theorem anpKey2_seg_chain (Γ : NGraph p q) (α : NV p q) :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q), anpKey2_chain Γ x l y →
      ∀ r, r ≤ l.countP (anpKey2_isA α) →
        anpKey2_chain Γ (if r = 0 then x else α) (anpKey2_seg (anpKey2_isA α) l r)
          (if r = l.countP (anpKey2_isA α) then y else α) := by
  intro l
  induction l with
  | nil =>
    intro x y h r hr
    simp only [List.countP_nil, nonpos_iff_eq_zero] at hr
    subst hr
    simpa [anpKey2_seg, anpKey2_chain] using h
  | cons st t ih =>
    intro x y h r hr
    obtain ⟨hstep, hrest⟩ := h
    cases hA : anpKey2_isA α st
    · have hA2 : ¬ st.2 = α := fun h' => by
        have := (anpKey2_isA_eq α st).2 h'; rw [hA] at this; exact Bool.noConfusion this
      rw [List.countP_cons_of_neg (by simpa using hA)] at hr ⊢
      rcases r with _ | r
      · rw [anpKey2_seg_zero_neg _ _ hA]
        have := ih st.2 y hrest 0 (Nat.zero_le _)
        simpa [anpKey2_chain, hstep] using this
      · rw [anpKey2_seg_succ_neg _ _ _ hA]
        have := ih st.2 y hrest (r + 1) hr
        simpa using this
    · have hA2 : st.2 = α := (anpKey2_isA_eq α st).1 hA
      rw [List.countP_cons_of_pos hA] at hr ⊢
      rcases r with _ | r
      · rw [anpKey2_seg_zero_pos _ _ hA]
        simp only [anpKey2_chain, ↓reduceIte, hstep, true_and]
        simpa using hA2
      · rw [anpKey2_seg_succ_pos _ _ _ hA]
        have := ih st.2 y hrest r (by omega)
        simpa [hA2] using this

end SegChain

section Fix

variable {p q : ℕ} (Γ : NGraph p (q + 1)) (i₀ : Fin (q + 1))

/-- The number of arrivals at `α_{i₀}` along the path `j`: the path is cut into `K j + 1` segments. -/
def anpKey2_K (j : Fin p) : ℕ := (Γ.path j).countP (anpKey2_isA (Sum.inr i₀))

/-- The segments: the `r`-th piece of the path `j`, `r ≤ K j`. -/
abbrev anpKey2_Seg : Type := (j : Fin p) × Fin (anpKey2_K Γ i₀ j + 1)

/-- The number of segments (`= p'`). -/
def anpKey2_P : ℕ := ∑ j : Fin p, (anpKey2_K Γ i₀ j + 1)

/-- The enumeration of the segments. -/
def anpKey2_ee : anpKey2_Seg Γ i₀ ≃ Fin (anpKey2_P Γ i₀) := finSigmaFinEquiv

/-- The steps of a segment. -/
def anpKey2_steps (s : anpKey2_Seg Γ i₀) : List (Fin Γ.es.length × NV p (q + 1)) :=
  anpKey2_seg (anpKey2_isA (Sum.inr i₀)) (Γ.path s.1) s.2.val

/-- The label of the start of a segment: `a_j` for the first segment of `𝔓_j`, `none` (the fixed vertex)
otherwise. -/
def anpKey2_ea (r : Fin (anpKey2_P Γ i₀)) : Option (Fin p ⊕ Fin p) :=
  if ((anpKey2_ee Γ i₀).symm r).2.val = 0 then some (Sum.inl ((anpKey2_ee Γ i₀).symm r).1) else none

/-- The label of the end of a segment: `b_j` for the last segment of `𝔓_j`, `none` (the fixed vertex) otherwise. -/
def anpKey2_eb (r : Fin (anpKey2_P Γ i₀)) : Option (Fin p ⊕ Fin p) :=
  if ((anpKey2_ee Γ i₀).symm r).2.val = anpKey2_K Γ i₀ ((anpKey2_ee Γ i₀).symm r).1 then
    some (Sum.inr ((anpKey2_ee Γ i₀).symm r).1) else none

/-- The old path of a segment. -/
def anpKey2_own (r : Fin (anpKey2_P Γ i₀)) : Fin p := ((anpKey2_ee Γ i₀).symm r).1

/-- The position of `i ≠ i₀` among the remaining vertices. -/
noncomputable def anpKey2_pred (i : Fin (q + 1)) (h : i ≠ i₀) : Fin q :=
  Classical.choose (Fin.exists_succAbove_eq h)

theorem anpKey2_succAbove_pred (i : Fin (q + 1)) (h : i ≠ i₀) : i₀.succAbove (anpKey2_pred i₀ i h) = i :=
  Classical.choose_spec (Fin.exists_succAbove_eq h)

theorem anpKey2_pred_succAbove (m : Fin q) (h : i₀.succAbove m ≠ i₀) : anpKey2_pred i₀ (i₀.succAbove m) h = m :=
  Fin.succAbove_right_injective (anpKey2_succAbove_pred i₀ _ h)

/-- The relabelling of the vertices: `t` is the image of `α_{i₀}`. -/
noncomputable def anpKey2_rel0 (t : NV (anpKey2_P Γ i₀) q) : NV p (q + 1) → NV (anpKey2_P Γ i₀) q
  | Sum.inl (Sum.inl j) => Sum.inl (Sum.inl (anpKey2_ee Γ i₀ ⟨j, 0⟩))
  | Sum.inl (Sum.inr j) => Sum.inl (Sum.inr (anpKey2_ee Γ i₀ ⟨j, Fin.last _⟩))
  | Sum.inr i => if h : i = i₀ then t else Sum.inr (anpKey2_pred i₀ i h)

/-- The image of `α_{i₀}` on the edge `k`: the start of the segment of which `k` is the first step (when the
segment starts at `α_{i₀}`), the end of the segment of which `k` is the last step (when it ends at `α_{i₀}`),
else the end of the default segment `s₀`. -/
noncomputable def anpKey2_tgt (s₀ : anpKey2_Seg Γ i₀) (k : Fin Γ.es.length) : NV (anpKey2_P Γ i₀) q :=
  open Classical in
  if h : ∃ s : anpKey2_Seg Γ i₀, s.2.val ≠ 0 ∧ ∃ st, (anpKey2_steps Γ i₀ s).head? = some st ∧ st.1 = k then
    Sum.inl (Sum.inl (anpKey2_ee Γ i₀ (Classical.choose h)))
  else if h' : ∃ s : anpKey2_Seg Γ i₀, s.2.val ≠ anpKey2_K Γ i₀ s.1 ∧
      ∃ st, (anpKey2_steps Γ i₀ s).getLast? = some st ∧ st.1 = k then
    Sum.inl (Sum.inr (anpKey2_ee Γ i₀ (Classical.choose h')))
  else Sum.inl (Sum.inr (anpKey2_ee Γ i₀ s₀))

/-- The edge `k` of the fixed graph. -/
noncomputable def anpKey2_edge (s₀ : anpKey2_Seg Γ i₀) (k : Fin Γ.es.length) : NEdge (anpKey2_P Γ i₀) q :=
  ⟨(Γ.es.get k).ghost, anpKey2_rel0 Γ i₀ (anpKey2_tgt Γ i₀ s₀ k) (Γ.es.get k).u,
    anpKey2_rel0 Γ i₀ (anpKey2_tgt Γ i₀ s₀ k) (Γ.es.get k).v⟩

/-- The edge list of the fixed graph: the relabelled edges of `Γ`, in the same order. -/
noncomputable def anpKey2_es (s₀ : anpKey2_Seg Γ i₀) : List (NEdge (anpKey2_P Γ i₀) q) :=
  List.ofFn (anpKey2_edge Γ i₀ s₀)

theorem anpKey2_es_length (s₀ : anpKey2_Seg Γ i₀) : (anpKey2_es Γ i₀ s₀).length = Γ.es.length :=
  List.length_ofFn

/-- The vertex fixing: the graph with `α_{i₀}` external, the paths cut at every arrival at `α_{i₀}`. -/
noncomputable def anpKey2_fixV (s₀ : anpKey2_Seg Γ i₀) : NGraph (anpKey2_P Γ i₀) q where
  es := anpKey2_es Γ i₀ s₀
  path := fun r => (anpKey2_steps Γ i₀ ((anpKey2_ee Γ i₀).symm r)).map fun st =>
    (Fin.cast (anpKey2_es_length Γ i₀ s₀).symm st.1, anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr r)) st.2)

/-- The edge correspondence. -/
noncomputable def anpKey2_em (s₀ : anpKey2_Seg Γ i₀) : Fin Γ.es.length ≃ Fin (anpKey2_fixV Γ i₀ s₀).es.length :=
  finCongr (anpKey2_es_length Γ i₀ s₀).symm

/-! basic facts on the segments -/

theorem anpKey2_steps_sublist (s : anpKey2_Seg Γ i₀) : (anpKey2_steps Γ i₀ s).Sublist (Γ.path s.1) :=
  anpKey2_seg_sublist _ _ _

theorem anpKey2_steps_mem_path {s : anpKey2_Seg Γ i₀} {x : Fin Γ.es.length × NV p (q + 1)}
    (h : x ∈ anpKey2_steps Γ i₀ s) : x ∈ Γ.path s.1 :=
  (anpKey2_steps_sublist Γ i₀ s).subset h

theorem anpKey2_cover {j : Fin p} {x : Fin Γ.es.length × NV p (q + 1)} (h : x ∈ Γ.path j) :
    ∃ r : Fin (anpKey2_K Γ i₀ j + 1), x ∈ anpKey2_steps Γ i₀ ⟨j, r⟩ := by
  obtain ⟨r, hr, hm⟩ := anpKey2_seg_cover (anpKey2_isA (Sum.inr i₀)) _ x h
  exact ⟨⟨r, Nat.lt_succ_of_le hr⟩, hm⟩

/-- An edge lies on at most one step of one segment. -/
theorem anpKey2_edge_unique (hN : Γ.IsNested) {s s' : anpKey2_Seg Γ i₀}
    {x x' : Fin Γ.es.length × NV p (q + 1)} (hx : x ∈ anpKey2_steps Γ i₀ s)
    (hx' : x' ∈ anpKey2_steps Γ i₀ s') (h : x.1 = x'.1) : s = s' ∧ x = x' := by
  by_cases hj : s.1 = s'.1
  · obtain ⟨j, r⟩ := s
    obtain ⟨j', r'⟩ := s'
    simp only at hj
    subst hj
    have hxx : x = x' := List.inj_on_of_nodup_map (hN.2.2.1 j) (anpKey2_steps_mem_path Γ i₀ hx)
      (anpKey2_steps_mem_path Γ i₀ hx') h
    subst hxx
    have := anpKey2_seg_unique (anpKey2_isA (Sum.inr i₀)) (Γ.path j) ((hN.2.2.1 j).of_map Prod.fst)
      r.val r'.val x hx hx'
    exact ⟨by rw [Fin.ext this], rfl⟩
  · exact absurd h (hN.2.2.2.1 s.1 s'.1 hj x (anpKey2_steps_mem_path Γ i₀ hx) x'
      (anpKey2_steps_mem_path Γ i₀ hx'))

theorem anpKey2_steps_chain (hN : Γ.IsNested) (s : anpKey2_Seg Γ i₀) :
    anpKey2_chain Γ (if s.2.val = 0 then Sum.inl (Sum.inl s.1) else Sum.inr i₀) (anpKey2_steps Γ i₀ s)
      (if s.2.val = anpKey2_K Γ i₀ s.1 then Sum.inl (Sum.inr s.1) else Sum.inr i₀) :=
  anpKey2_seg_chain Γ (Sum.inr i₀) (Γ.path s.1) _ _ ((anpKey2_walkOK_iff Γ s.1).1 (hN.2.1 s.1))
    s.2.val (Nat.le_of_lt_succ s.2.2)

theorem anpKey2_steps_shape (s : anpKey2_Seg Γ i₀) :
    (s.2.val < anpKey2_K Γ i₀ s.1 → ∃ (T₀ : List (Fin Γ.es.length × NV p (q + 1))) (z : Fin Γ.es.length × NV p (q + 1)),
      anpKey2_steps Γ i₀ s = T₀ ++ [z] ∧ z.2 = Sum.inr i₀ ∧ ∀ x ∈ T₀, x.2 ≠ Sum.inr i₀) ∧
    (s.2.val = anpKey2_K Γ i₀ s.1 → ∀ x ∈ anpKey2_steps Γ i₀ s, x.2 ≠ Sum.inr i₀) := by
  refine ⟨fun h => ?_, fun h x hx => ?_⟩
  · obtain ⟨T₀, z, h1, h2, h3⟩ := anpKey2_seg_shape (anpKey2_isA (Sum.inr i₀)) (Γ.path s.1) s.2.val h
    exact ⟨T₀, z, h1, (anpKey2_isA_eq _ z).1 h2, fun x hx hx' => by
      have := (anpKey2_isA_eq _ x).2 hx'; rw [h3 x hx] at this; exact Bool.noConfusion this⟩
  · intro hx'
    have := anpKey2_seg_last (anpKey2_isA (Sum.inr i₀)) (Γ.path s.1) s.2.val h.symm x hx
    have h2 := (anpKey2_isA_eq (Sum.inr i₀) x).2 hx'
    rw [this] at h2
    exact Bool.noConfusion h2

theorem anpKey2_steps_ne_nil (hN : Γ.IsNested) (s : anpKey2_Seg Γ i₀) : anpKey2_steps Γ i₀ s ≠ [] := by
  intro h
  by_cases hlt : s.2.val < anpKey2_K Γ i₀ s.1
  · obtain ⟨T₀, z, h1, -⟩ := (anpKey2_steps_shape Γ i₀ s).1 hlt
    rw [h1] at h
    simp at h
  · have hK : s.2.val = anpKey2_K Γ i₀ s.1 := by have := s.2.2; omega
    have hc := anpKey2_steps_chain Γ i₀ hN s
    rw [h, hK] at hc
    simp only [anpKey2_chain, ↓reduceIte] at hc
    split_ifs at hc
    simp_all

/-! the image of `α_{i₀}` on an edge -/

/-- The image of `α_{i₀}` carries the label `x`: it is the start (resp. end) of a segment that starts (resp.
ends) at `α_{i₀}`. -/
def anpKey2_noneV (t : NV (anpKey2_P Γ i₀) q) : Prop :=
  (∃ s : anpKey2_Seg Γ i₀, s.2.val ≠ 0 ∧ t = Sum.inl (Sum.inl (anpKey2_ee Γ i₀ s))) ∨
    (∃ s : anpKey2_Seg Γ i₀, s.2.val ≠ anpKey2_K Γ i₀ s.1 ∧ t = Sum.inl (Sum.inr (anpKey2_ee Γ i₀ s)))

theorem anpKey2_tgt_none (s₀ : anpKey2_Seg Γ i₀) (hs₀ : s₀.2.val ≠ anpKey2_K Γ i₀ s₀.1)
    (k : Fin Γ.es.length) : anpKey2_noneV Γ i₀ (anpKey2_tgt Γ i₀ s₀ k) := by
  classical
  unfold anpKey2_tgt
  split_ifs with h h'
  · exact Or.inl ⟨_, (Classical.choose_spec h).1, rfl⟩
  · exact Or.inr ⟨_, (Classical.choose_spec h').1, rfl⟩
  · exact Or.inr ⟨s₀, hs₀, rfl⟩

theorem anpKey2_tgt_first (hN : Γ.IsNested) (s₀ : anpKey2_Seg Γ i₀) {s : anpKey2_Seg Γ i₀}
    (hs : s.2.val ≠ 0) {st : Fin Γ.es.length × NV p (q + 1)} (h : (anpKey2_steps Γ i₀ s).head? = some st) :
    anpKey2_tgt Γ i₀ s₀ st.1 = Sum.inl (Sum.inl (anpKey2_ee Γ i₀ s)) := by
  classical
  have hex : ∃ s : anpKey2_Seg Γ i₀, s.2.val ≠ 0 ∧ ∃ st', (anpKey2_steps Γ i₀ s).head? = some st' ∧ st'.1 = st.1 :=
    ⟨s, hs, st, h, rfl⟩
  unfold anpKey2_tgt
  simp only [hex, ↓reduceDIte]
  obtain ⟨-, st', h1, h2⟩ := Classical.choose_spec hex
  have := (anpKey2_edge_unique Γ i₀ hN (List.mem_of_mem_head? h1) (List.mem_of_mem_head? h)
    (h2)).1
  rw [this]

private theorem anpKey2_single {α β : Type*} (l : List (α × β)) (a b : α × β) (h1 : l.head? = some a)
    (h2 : l.getLast? = some b) (hnd : (l.map Prod.fst).Nodup) (h : a.1 = b.1) : l = [a] := by
  cases l with
  | nil => simp at h1
  | cons x t =>
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    cases t with
    | nil => rfl
    | cons y t' =>
      exfalso
      have hb : b ∈ y :: t' := by
        rw [List.getLast?_cons_cons] at h2
        exact List.mem_of_getLast? h2
      have : x.1 ∈ (y :: t').map Prod.fst := List.mem_map.2 ⟨b, hb, h.symm⟩
      exact (List.nodup_cons.1 hnd).1 this

theorem anpKey2_tgt_last (hN : Γ.IsNested) (s₀ : anpKey2_Seg Γ i₀) {s : anpKey2_Seg Γ i₀}
    (hs : s.2.val ≠ anpKey2_K Γ i₀ s.1) {st : Fin Γ.es.length × NV p (q + 1)}
    (h : (anpKey2_steps Γ i₀ s).getLast? = some st) :
    anpKey2_tgt Γ i₀ s₀ st.1 = Sum.inl (Sum.inr (anpKey2_ee Γ i₀ s)) := by
  classical
  have hex : ∃ s : anpKey2_Seg Γ i₀, s.2.val ≠ anpKey2_K Γ i₀ s.1 ∧
      ∃ st', (anpKey2_steps Γ i₀ s).getLast? = some st' ∧ st'.1 = st.1 := ⟨s, hs, st, h, rfl⟩
  unfold anpKey2_tgt
  by_cases hfirst : ∃ s : anpKey2_Seg Γ i₀, s.2.val ≠ 0 ∧
      ∃ st', (anpKey2_steps Γ i₀ s).head? = some st' ∧ st'.1 = st.1
  · exfalso
    obtain ⟨s₁, hs₁, st₁, h1, h2⟩ := hfirst
    have hss := (anpKey2_edge_unique Γ i₀ hN (List.mem_of_mem_head? h1) (List.mem_of_getLast? h) h2).1
    subst hss
    have hsingle : anpKey2_steps Γ i₀ s₁ = [st₁] :=
      anpKey2_single _ st₁ st h1 h
        (List.Nodup.sublist ((anpKey2_steps_sublist Γ i₀ s₁).map Prod.fst) (hN.2.2.1 s₁.1)) h2
    have hc := anpKey2_steps_chain Γ i₀ hN s₁
    rw [hsingle] at hc
    simp only [hs₁, hs, ↓reduceIte, anpKey2_chain] at hc
    obtain ⟨hstep, hend⟩ := hc
    have hne := hN.1 (Γ.es.get st₁.1) (List.get_mem _ _)
    rcases hstep with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> exact hne (by rw [h3, h4, hend])
  · simp only [hfirst, hex, ↓reduceDIte]
    obtain ⟨-, st', h1, h2⟩ := Classical.choose_spec hex
    have := (anpKey2_edge_unique Γ i₀ hN (List.mem_of_getLast? h1) (List.mem_of_getLast? h) h2).1
    rw [this]

/-! the relabelling of vertices -/

theorem anpKey2_rel0_self (t : NV (anpKey2_P Γ i₀) q) : anpKey2_rel0 Γ i₀ t (Sum.inr i₀) = t := by
  simp [anpKey2_rel0]

theorem anpKey2_rel0_succAbove (t : NV (anpKey2_P Γ i₀) q) (m : Fin q) :
    anpKey2_rel0 Γ i₀ t (Sum.inr (i₀.succAbove m)) = Sum.inr m := by
  have h := Fin.succAbove_ne i₀ m
  simp only [anpKey2_rel0, h, ↓reduceDIte]
  rw [anpKey2_pred_succAbove i₀ m h]

theorem anpKey2_rel0_ne {t t' : NV (anpKey2_P Γ i₀) q} {v : NV p (q + 1)} (hv : v ≠ Sum.inr i₀) :
    anpKey2_rel0 Γ i₀ t v = anpKey2_rel0 Γ i₀ t' v := by
  rcases v with (j | j) | i
  · rfl
  · rfl
  · have : i ≠ i₀ := fun h => hv (by rw [h])
    simp [anpKey2_rel0, this]

theorem anpKey2_noneV_ne_a {t : NV (anpKey2_P Γ i₀) q} (ht : anpKey2_noneV Γ i₀ t) (j : Fin p) :
    t ≠ Sum.inl (Sum.inl (anpKey2_ee Γ i₀ ⟨j, 0⟩)) := by
  rintro rfl
  rcases ht with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
  · have := (anpKey2_ee Γ i₀).injective (Sum.inl.inj (Sum.inl.inj h)).symm
    subst this
    exact hs rfl
  · simp at h

theorem anpKey2_noneV_ne_b {t : NV (anpKey2_P Γ i₀) q} (ht : anpKey2_noneV Γ i₀ t) (j : Fin p) :
    t ≠ Sum.inl (Sum.inr (anpKey2_ee Γ i₀ ⟨j, Fin.last _⟩)) := by
  rintro rfl
  rcases ht with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
  · simp at h
  · have := (anpKey2_ee Γ i₀).injective (Sum.inr.inj (Sum.inl.inj h)).symm
    subst this
    exact hs (by simp)

theorem anpKey2_noneV_ne_inr {t : NV (anpKey2_P Γ i₀) q} (ht : anpKey2_noneV Γ i₀ t) (m : Fin q) :
    t ≠ Sum.inr m := by
  rintro rfl
  rcases ht with ⟨s, hs, h⟩ | ⟨s, hs, h⟩ <;> simp at h

theorem anpKey2_rel0_inj {t : NV (anpKey2_P Γ i₀) q} (ht : anpKey2_noneV Γ i₀ t) :
    Function.Injective (anpKey2_rel0 Γ i₀ t) := by
  intro u v h
  rcases u with (j | j) | i <;> rcases v with (j' | j') | i'
  · have := (anpKey2_ee Γ i₀).injective (Sum.inl.inj (Sum.inl.inj h))
    rw [(Sigma.mk.inj_iff.1 this).1]
  · simp [anpKey2_rel0] at h
  · by_cases hi : i' = i₀
    · simp only [anpKey2_rel0, hi, ↓reduceDIte] at h
      exact absurd h.symm (anpKey2_noneV_ne_a Γ i₀ ht j)
    · simp [anpKey2_rel0, hi] at h
  · simp [anpKey2_rel0] at h
  · have := (anpKey2_ee Γ i₀).injective (Sum.inr.inj (Sum.inl.inj h))
    rw [(Sigma.mk.inj_iff.1 this).1]
  · by_cases hi : i' = i₀
    · simp only [anpKey2_rel0, hi, ↓reduceDIte] at h
      exact absurd h.symm (anpKey2_noneV_ne_b Γ i₀ ht j)
    · simp [anpKey2_rel0, hi] at h
  · by_cases hi : i = i₀
    · simp only [anpKey2_rel0, hi, ↓reduceDIte] at h
      exact absurd h (anpKey2_noneV_ne_a Γ i₀ ht j')
    · simp [anpKey2_rel0, hi] at h
  · by_cases hi : i = i₀
    · simp only [anpKey2_rel0, hi, ↓reduceDIte] at h
      exact absurd h (anpKey2_noneV_ne_b Γ i₀ ht j')
    · simp [anpKey2_rel0, hi] at h
  · by_cases hi : i = i₀ <;> by_cases hi' : i' = i₀
    · rw [hi, hi']
    · simp only [anpKey2_rel0, hi, hi', ↓reduceDIte] at h
      exact absurd h (anpKey2_noneV_ne_inr Γ i₀ ht _)
    · simp only [anpKey2_rel0, hi, hi', ↓reduceDIte] at h
      exact absurd h.symm (anpKey2_noneV_ne_inr Γ i₀ ht _)
    · simp only [anpKey2_rel0, hi, hi', ↓reduceDIte, Sum.inr.injEq] at h
      rw [← anpKey2_succAbove_pred i₀ i hi, ← anpKey2_succAbove_pred i₀ i' hi', h]

theorem anpKey2_es_get (s₀ : anpKey2_Seg Γ i₀) (k : Fin Γ.es.length) :
    (anpKey2_fixV Γ i₀ s₀).es.get (anpKey2_em Γ i₀ s₀ k) = anpKey2_edge Γ i₀ s₀ k := by
  exact (List.get_ofFn (anpKey2_edge Γ i₀ s₀) (anpKey2_em Γ i₀ s₀ k)).trans (congrArg _ (Fin.ext rfl))

theorem anpKey2_ee_symm_snd (s : anpKey2_Seg Γ i₀) :
    ((anpKey2_ee Γ i₀).symm (anpKey2_ee Γ i₀ s)).2.val = s.2.val := by
  rw [Equiv.symm_apply_apply]

theorem anpKey2_ee_symm_fst (s : anpKey2_Seg Γ i₀) :
    ((anpKey2_ee Γ i₀).symm (anpKey2_ee Γ i₀ s)).1 = s.1 := by
  rw [Equiv.symm_apply_apply]

theorem anpKey2_ea_ee (s : anpKey2_Seg Γ i₀) :
    anpKey2_ea Γ i₀ (anpKey2_ee Γ i₀ s) = if s.2.val = 0 then some (Sum.inl s.1) else none := by
  simp only [anpKey2_ea, anpKey2_ee_symm_snd, anpKey2_ee_symm_fst]

theorem anpKey2_eb_ee (s : anpKey2_Seg Γ i₀) :
    anpKey2_eb Γ i₀ (anpKey2_ee Γ i₀ s) =
      if s.2.val = anpKey2_K Γ i₀ s.1 then some (Sum.inr s.1) else none := by
  simp only [anpKey2_eb, anpKey2_ee_symm_snd, anpKey2_ee_symm_fst]

/-- The labels: the relabelling of the vertices carries the labels of `Γ` (with `α_{i₀}` labelled `x`). -/
theorem anpKey2_lab {ι : Type} (a b : Fin p → ι) (x : ι) (ℓ : Fin q → ι) {t : NV (anpKey2_P Γ i₀) q}
    (ht : anpKey2_noneV Γ i₀ t) (v : NV p (q + 1)) :
    Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (anpKey2_ea Γ i₀ r))
        (fun r => anpKey2_fixLab a b x (anpKey2_eb Γ i₀ r))) ℓ (anpKey2_rel0 Γ i₀ t v) =
      Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) v := by
  rcases v with (j | j) | i
  · simp [anpKey2_rel0, anpKey2_ea_ee, anpKey2_fixLab]
  · simp [anpKey2_rel0, anpKey2_eb_ee, anpKey2_fixLab]
  · by_cases hi : i = i₀
    · subst hi
      rw [anpKey2_rel0_self]
      simp only [Sum.elim_inr, Fin.insertNth_apply_same]
      rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
      · simp [anpKey2_ea_ee, hs, anpKey2_fixLab]
      · simp [anpKey2_eb_ee, hs, anpKey2_fixLab]
    · simp only [anpKey2_rel0, hi, ↓reduceDIte, Sum.elim_inr]
      conv_rhs => rw [← anpKey2_succAbove_pred i₀ i hi]
      rw [Fin.insertNth_apply_succAbove]

theorem anpKey2_chain_new {p q p' q' : ℕ} (Γ : NGraph p q) (Γ' : NGraph p' q')
    (em : Fin Γ.es.length → Fin Γ'.es.length) (rel : Fin Γ.es.length → NV p q → NV p' q')
    (hedge : ∀ k, (Γ'.es.get (em k)).u = rel k (Γ.es.get k).u ∧
      (Γ'.es.get (em k)).v = rel k (Γ.es.get k).v)
    (vs : NV p q → NV p' q') :
    ∀ (T : List (Fin Γ.es.length × NV p q)) (c : NV p q) (c' : NV p' q') (w : NV p q),
      anpKey2_chain Γ c T w → (∀ x ∈ T, rel x.1 x.2 = vs x.2) →
      (∀ x ∈ T.dropLast, ∀ k, rel k x.2 = vs x.2) → (∀ x, T.head? = some x → rel x.1 c = c') →
      T ≠ [] →
      anpKey2_chain Γ' c' (T.map fun x => (em x.1, vs x.2)) (vs w) := by
  intro T
  induction T with
  | nil => intro _ _ _ _ _ _ _ _; contradiction
  | cons x T' ih =>
    intro c c' w h h1 h2 h3 _
    obtain ⟨hstep, hrest⟩ := h
    have hx1 := h1 x List.mem_cons_self
    have hc := h3 x rfl
    refine ⟨?_, ?_⟩
    · obtain ⟨hu, hv⟩ := hedge x.1
      rcases hstep with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [hu, e1, hc]
        · rw [hv, e2, hx1]
      · right
        refine ⟨?_, ?_⟩
        · rw [hv, e1, hc]
        · rw [hu, e2, hx1]
    · cases T' with
      | nil =>
        have : x.2 = w := hrest
        simp [anpKey2_chain, this]
      | cons y T'' =>
        refine ih x.2 (vs x.2) w hrest (fun z hz => h1 z (List.mem_cons_of_mem _ hz)) ?_ ?_ (by simp)
        · intro z hz k
          refine h2 z ?_ k
          rw [List.dropLast_cons_of_ne_nil (by simp)]
          exact List.mem_cons_of_mem _ hz
        · intro z hz
          have hz' : z = y := by simpa using hz.symm
          subst hz'
          refine h2 x ?_ z.1
          rw [List.dropLast_cons_of_ne_nil (by simp)]
          exact List.mem_cons_self

theorem anpKey2_seg_eq_zero {s : anpKey2_Seg Γ i₀} (h : s.2.val = 0) : s = ⟨s.1, 0⟩ := by
  obtain ⟨j, r⟩ := s
  have : r = 0 := Fin.ext h
  subst this
  rfl

theorem anpKey2_seg_eq_last {s : anpKey2_Seg Γ i₀} (h : s.2.val = anpKey2_K Γ i₀ s.1) :
    s = ⟨s.1, Fin.last _⟩ := by
  obtain ⟨j, r⟩ := s
  have : r = Fin.last _ := Fin.ext h
  subst this
  rfl

theorem anpKey2_fixV_path (s₀ : anpKey2_Seg Γ i₀) (s : anpKey2_Seg Γ i₀) :
    (anpKey2_fixV Γ i₀ s₀).path (anpKey2_ee Γ i₀ s) =
      (anpKey2_steps Γ i₀ s).map fun st =>
        (anpKey2_em Γ i₀ s₀ st.1, anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ s))) st.2) := by
  show ((anpKey2_steps Γ i₀ ((anpKey2_ee Γ i₀).symm (anpKey2_ee Γ i₀ s))).map _) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem anpKey2_fixV_edge (s₀ : anpKey2_Seg Γ i₀) (k : Fin Γ.es.length) :
    ((anpKey2_fixV Γ i₀ s₀).es.get (anpKey2_em Γ i₀ s₀ k)).u =
        anpKey2_rel0 Γ i₀ (anpKey2_tgt Γ i₀ s₀ k) (Γ.es.get k).u ∧
      ((anpKey2_fixV Γ i₀ s₀).es.get (anpKey2_em Γ i₀ s₀ k)).v =
        anpKey2_rel0 Γ i₀ (anpKey2_tgt Γ i₀ s₀ k) (Γ.es.get k).v := by
  rw [anpKey2_es_get]
  exact ⟨rfl, rfl⟩

theorem anpKey2_steps_dropLast (s : anpKey2_Seg Γ i₀) :
    ∀ x ∈ (anpKey2_steps Γ i₀ s).dropLast, x.2 ≠ Sum.inr i₀ := by
  intro x hx
  by_cases hlt : s.2.val < anpKey2_K Γ i₀ s.1
  · obtain ⟨T₀, z, h1, h2, h3⟩ := (anpKey2_steps_shape Γ i₀ s).1 hlt
    rw [h1, List.dropLast_concat] at hx
    exact h3 x hx
  · have hK : s.2.val = anpKey2_K Γ i₀ s.1 := by have := s.2.2; omega
    exact (anpKey2_steps_shape Γ i₀ s).2 hK x (List.mem_of_mem_dropLast hx)

theorem anpKey2_steps_arrival (s : anpKey2_Seg Γ i₀) :
    ∀ x ∈ anpKey2_steps Γ i₀ s, x.2 = Sum.inr i₀ →
      s.2.val ≠ anpKey2_K Γ i₀ s.1 ∧ (anpKey2_steps Γ i₀ s).getLast? = some x := by
  intro x hx hx2
  by_cases hlt : s.2.val < anpKey2_K Γ i₀ s.1
  · obtain ⟨T₀, z, h1, h2, h3⟩ := (anpKey2_steps_shape Γ i₀ s).1 hlt
    refine ⟨by omega, ?_⟩
    rw [h1] at hx ⊢
    rcases List.mem_append.1 hx with hx | hx
    · exact absurd hx2 (h3 x hx)
    · rw [List.mem_singleton] at hx
      subst hx
      simp
  · have hK : s.2.val = anpKey2_K Γ i₀ s.1 := by have := s.2.2; omega
    exact absurd hx2 ((anpKey2_steps_shape Γ i₀ s).2 hK x hx)

theorem anpKey2_fixV_walk (hN : Γ.IsNested) (s₀ : anpKey2_Seg Γ i₀) (s : anpKey2_Seg Γ i₀) :
    anpKey2_chain (anpKey2_fixV Γ i₀ s₀) (Sum.inl (Sum.inl (anpKey2_ee Γ i₀ s)))
      ((anpKey2_fixV Γ i₀ s₀).path (anpKey2_ee Γ i₀ s)) (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ s))) := by
  rw [anpKey2_fixV_path]
  have key := anpKey2_chain_new Γ (anpKey2_fixV Γ i₀ s₀) (anpKey2_em Γ i₀ s₀)
    (fun k => anpKey2_rel0 Γ i₀ (anpKey2_tgt Γ i₀ s₀ k)) (anpKey2_fixV_edge Γ i₀ s₀)
    (anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ s)))) (anpKey2_steps Γ i₀ s)
    (if s.2.val = 0 then Sum.inl (Sum.inl s.1) else Sum.inr i₀)
    (Sum.inl (Sum.inl (anpKey2_ee Γ i₀ s)))
    (if s.2.val = anpKey2_K Γ i₀ s.1 then Sum.inl (Sum.inr s.1) else Sum.inr i₀)
    (anpKey2_steps_chain Γ i₀ hN s)
    (by
      intro x hx
      by_cases hx2 : x.2 = Sum.inr i₀
      · obtain ⟨hne, hlast⟩ := anpKey2_steps_arrival Γ i₀ s x hx hx2
        simp only [hx2, anpKey2_rel0_self]
        exact anpKey2_tgt_last Γ i₀ hN s₀ hne hlast
      · exact anpKey2_rel0_ne Γ i₀ hx2)
    (fun x hx k => anpKey2_rel0_ne Γ i₀ (anpKey2_steps_dropLast Γ i₀ s x hx))
    (by
      intro x hx
      by_cases h0 : s.2.val = 0
      · simp only [h0, ↓reduceIte, anpKey2_rel0]
        rw [← anpKey2_seg_eq_zero Γ i₀ h0]
      · simp only [h0, ↓reduceIte, anpKey2_rel0_self]
        exact anpKey2_tgt_first Γ i₀ hN s₀ h0 hx)
    (anpKey2_steps_ne_nil Γ i₀ hN s)
  convert key using 2
  by_cases hK : s.2.val = anpKey2_K Γ i₀ s.1
  · simp only [hK, ↓reduceIte, anpKey2_rel0]
    rw [← anpKey2_seg_eq_last Γ i₀ hK]
  · simp only [hK, ↓reduceIte, anpKey2_rel0_self]

theorem anpKey2_fixV_visits (s₀ : anpKey2_Seg Γ i₀) {j : Fin p} {m : Fin q}
    (hv : Γ.Visits j (Sum.inr (i₀.succAbove m))) :
    ∃ s : anpKey2_Seg Γ i₀, s.1 = j ∧
      (anpKey2_fixV Γ i₀ s₀).Visits (anpKey2_ee Γ i₀ s) (Sum.inr m) := by
  obtain ⟨st, hst, hend⟩ := hv
  obtain ⟨r, hr⟩ := anpKey2_cover Γ i₀ hst
  refine ⟨⟨j, r⟩, rfl, ?_⟩
  refine ⟨(anpKey2_em Γ i₀ s₀ st.1,
    anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ ⟨j, r⟩))) st.2), ?_, ?_⟩
  · rw [anpKey2_fixV_path]
    exact List.mem_map.2 ⟨st, hr, rfl⟩
  · obtain ⟨hu, hv'⟩ := anpKey2_fixV_edge Γ i₀ s₀ st.1
    rcases hend with h | h
    · left; rw [hu, h, anpKey2_rel0_succAbove]
    · right; rw [hv', h, anpKey2_rel0_succAbove]

theorem anpKey2_fixV_nested (hN : Γ.IsNested) (s₀ : anpKey2_Seg Γ i₀)
    (hs₀ : s₀.2.val ≠ anpKey2_K Γ i₀ s₀.1) : (anpKey2_fixV Γ i₀ s₀).IsNested := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 he
    exact fun h => hN.1 (Γ.es.get k) (List.get_mem _ _)
      (anpKey2_rel0_inj Γ i₀ (anpKey2_tgt_none Γ i₀ s₀ hs₀ k) h)
  · intro r
    obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r
    exact (anpKey2_walkOK_iff _ _).2 (anpKey2_fixV_walk Γ i₀ hN s₀ s)
  · intro r
    obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r
    have hnd : ((anpKey2_steps Γ i₀ s).map Prod.fst).Nodup :=
      List.Nodup.sublist ((anpKey2_steps_sublist Γ i₀ s).map Prod.fst) (hN.2.2.1 s.1)
    rw [anpKey2_fixV_path, List.map_map]
    have : (Prod.fst ∘ fun st : Fin Γ.es.length × NV p (q + 1) =>
        (anpKey2_em Γ i₀ s₀ st.1, anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ s))) st.2)) =
        (anpKey2_em Γ i₀ s₀) ∘ Prod.fst := rfl
    rw [this, ← List.map_map]
    exact hnd.map (anpKey2_em Γ i₀ s₀).injective
  · intro r r' hne st hst st' hst'
    obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r
    obtain ⟨s', rfl⟩ := (anpKey2_ee Γ i₀).surjective r'
    rw [anpKey2_fixV_path] at hst hst'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hst
    obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hst'
    intro h
    have h' : x.1 = x'.1 := (anpKey2_em Γ i₀ s₀).injective h
    exact hne (by rw [(anpKey2_edge_unique Γ i₀ hN hx hx' h').1])
  · intro α
    obtain ⟨a, b, hab, ha, hb⟩ := hN.2.2.2.2.1 (i₀.succAbove α)
    obtain ⟨s, hs1, hs⟩ := anpKey2_fixV_visits Γ i₀ s₀ ha
    obtain ⟨s', hs1', hs'⟩ := anpKey2_fixV_visits Γ i₀ s₀ hb
    refine ⟨_, _, ?_, hs, hs'⟩
    intro h
    have := (anpKey2_ee Γ i₀).injective h
    exact hab (by rw [← hs1, ← hs1', this])
  · intro A
    have h6 := hN.2.2.2.2.2 (A.image i₀.succAbove)
    rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h6
    refine h6.trans ?_
    refine Finset.card_le_card_of_surjOn (fun r : Fin (anpKey2_P Γ i₀) => ((anpKey2_ee Γ i₀).symm r).1) ?_
    intro j hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
    obtain ⟨α', hα', hv⟩ := hj
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hα'
    obtain ⟨s, hs1, hs⟩ := anpKey2_fixV_visits Γ i₀ s₀ hv
    refine ⟨anpKey2_ee Γ i₀ s, ?_, ?_⟩
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      exact ⟨m, hm, hs⟩
    · simp only
      rw [anpKey2_ee_symm_fst, hs1]

/-- Two ghost steps of one path coincide (`GhostOK`: at most one ghost edge per path). -/
theorem anpKey2_ghost_unique {p' q' : ℕ} (Γ : NGraph p' q') (hG : Γ.GhostOK) {j : Fin p'}
    {x x' : Fin Γ.es.length × NV p' q'} (hx : x ∈ Γ.path j) (hx' : x' ∈ Γ.path j)
    (hg : (Γ.es.get x.1).ghost = true) (hg' : (Γ.es.get x'.1).ghost = true) : x = x' := by
  by_contra hne
  have hnd : [x, x'].Nodup := by simp [hne]
  have hsub : [x, x'] ⊆ (Γ.path j).filter fun st => (Γ.es.get st.1).ghost := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact List.mem_filter.2 ⟨hx, hg⟩
    · exact List.mem_filter.2 ⟨hx', hg'⟩
  have := (List.subperm_of_subset hnd hsub).length_le
  have h2 := (hG j).1
  simp only [List.length_cons, List.length_nil] at this
  omega

theorem anpKey2_steps_first {j : Fin p} {x : Fin Γ.es.length × NV p (q + 1)}
    {t : List (Fin Γ.es.length × NV p (q + 1))} (hp : Γ.path j = x :: t) :
    ∃ t', anpKey2_steps Γ i₀ ⟨j, 0⟩ = x :: t' := by
  unfold anpKey2_steps
  simp only [Fin.val_zero]
  rw [hp]
  exact anpKey2_seg_head _ x t

theorem anpKey2_steps_last (hN : Γ.IsNested) {j : Fin p} {l : List (Fin Γ.es.length × NV p (q + 1))}
    {x : Fin Γ.es.length × NV p (q + 1)} (hp : Γ.path j = l ++ [x]) :
    ∃ T, anpKey2_steps Γ i₀ ⟨j, Fin.last (anpKey2_K Γ i₀ j)⟩ = T ++ [x] := by
  have hch := (anpKey2_walkOK_iff Γ j).1 (hN.2.1 j)
  rw [hp] at hch
  have hend := anpKey2_chain_end Γ l x _ _ hch
  have hx : x.2 ≠ Sum.inr i₀ := by
    rw [← hend]; simp
  have hA : anpKey2_isA (Sum.inr i₀) x = false := by simpa [anpKey2_isA] using hx
  have hK : anpKey2_K Γ i₀ j = l.countP (anpKey2_isA (Sum.inr i₀)) := by
    unfold anpKey2_K
    rw [hp, List.countP_append]
    simp [hA]
  unfold anpKey2_steps
  simp only [Fin.val_last]
  rw [hp, anpKey2_seg_snoc, hK]
  exact ⟨anpKey2_seg (anpKey2_isA (Sum.inr i₀)) l (l.countP (anpKey2_isA (Sum.inr i₀))), by simp⟩

theorem anpKey2_fixV_ghost (s₀ : anpKey2_Seg Γ i₀) (k : Fin Γ.es.length) :
    ((anpKey2_fixV Γ i₀ s₀).es.get (anpKey2_em Γ i₀ s₀ k)).ghost = (Γ.es.get k).ghost := by
  rw [anpKey2_es_get]
  rfl

theorem anpKey2_fixV_ghostOK (hG : Γ.GhostOK) (hN : Γ.IsNested) (s₀ : anpKey2_Seg Γ i₀) :
    (anpKey2_fixV Γ i₀ s₀).GhostOK := by
  intro r
  obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r
  rw [anpKey2_fixV_path]
  refine ⟨?_, ?_⟩
  · rw [List.filter_map, List.length_map]
    have hfun : ((fun st' : Fin (anpKey2_fixV Γ i₀ s₀).es.length × NV (anpKey2_P Γ i₀) q =>
        ((anpKey2_fixV Γ i₀ s₀).es.get st'.1).ghost) ∘
        fun st : Fin Γ.es.length × NV p (q + 1) =>
          (anpKey2_em Γ i₀ s₀ st.1,
            anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ s))) st.2)) =
        fun st => (Γ.es.get st.1).ghost := funext fun st => anpKey2_fixV_ghost Γ i₀ s₀ st.1
    rw [hfun]
    exact (((anpKey2_steps_sublist Γ i₀ s).filter _).length_le).trans (hG s.1).1
  · intro st' hst' hg'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hst'
    have hgx : (Γ.es.get x.1).ghost = true := by
      rw [← anpKey2_fixV_ghost Γ i₀ s₀]; exact hg'
    have hxp := anpKey2_steps_mem_path Γ i₀ hx
    rcases (hG s.1).2 x hxp hgx with hh | hl
    · left
      obtain ⟨t, ht⟩ : ∃ t, Γ.path s.1 = x :: t := by
        cases hp : Γ.path s.1 with
        | nil => rw [hp] at hh; simp at hh
        | cons y t => rw [hp] at hh; simp at hh; exact ⟨t, by rw [hh]⟩
      obtain ⟨t', ht'⟩ := anpKey2_steps_first Γ i₀ ht
      have := (anpKey2_edge_unique Γ i₀ hN hx (ht' ▸ List.mem_cons_self : x ∈ anpKey2_steps Γ i₀ ⟨s.1, 0⟩) rfl).1
      rw [this, ht']
      simp
    · right
      obtain ⟨l, hl'⟩ := List.getLast?_eq_some_iff.1 hl
      obtain ⟨T, hT⟩ := anpKey2_steps_last Γ i₀ hN hl'
      have := (anpKey2_edge_unique Γ i₀ hN hx
        (hT ▸ List.mem_append_right _ (List.mem_singleton_self x) :
          x ∈ anpKey2_steps Γ i₀ ⟨s.1, Fin.last _⟩) rfl).1
      rw [this, hT]
      simp

/-! the value -/

theorem anpKey2_prod_eq {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).prod = ∏ j : Fin l.length, f (l.get j) := by
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- The product of the edge factors is invariant under a relabelling that preserves ghost flags and labels. -/
theorem anpKey2_ep_eq {p' q' : ℕ} {ι : Type*} (Γ : NGraph p q) (Γ' : NGraph p' q')
    (em : Fin Γ.es.length ≃ Fin Γ'.es.length) (ξ : ι → ι → ℝ) (lab : NV p q → ι) (lab' : NV p' q' → ι)
    (hg : ∀ k, (Γ'.es.get (em k)).ghost = (Γ.es.get k).ghost)
    (hu : ∀ k, lab' (Γ'.es.get (em k)).u = lab (Γ.es.get k).u)
    (hv : ∀ k, lab' (Γ'.es.get (em k)).v = lab (Γ.es.get k).v) :
    anpKey2_ep Γ' ξ lab' = anpKey2_ep Γ ξ lab := by
  unfold anpKey2_ep
  rw [anpKey2_prod_eq, anpKey2_prod_eq, ← Equiv.prod_comp em]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [hg, hu, hv]

theorem anpKey2_fixV_value {d L : ℕ} [NeZero L] (s₀ : anpKey2_Seg Γ i₀)
    (hs₀ : s₀.2.val ≠ anpKey2_K Γ i₀ s₀.1) (ξ : Zd d L → Zd d L → ℝ) (hnn : ∀ α β, 0 ≤ ξ α β)
    (a b : Fin p → Zd d L) (π : Fin (q + 1) → Fin p → Bool) :
    Γ.valOn ξ a b (anpKey2_region a b π) ≤
      ∑ x ∈ anpKey2_regionOne a b (π i₀),
        (anpKey2_fixV Γ i₀ s₀).val ξ (fun r => anpKey2_fixLab a b x (anpKey2_ea Γ i₀ r))
          (fun r => anpKey2_fixLab a b x (anpKey2_eb Γ i₀ r)) := by
  classical
  set R := anpKey2_regionOne a b (π i₀) with hR
  let F : (Fin (q + 1) → Zd d L) → ℝ := fun ℓ => anpKey2_ep Γ ξ (Sum.elim (Sum.elim a b) ℓ)
  have hF0 : ∀ ℓ, 0 ≤ F ℓ := fun ℓ => anpKey2_ep_nonneg Γ ξ hnn _
  have h1 : Γ.valOn ξ a b (anpKey2_region a b π) = ∑ ℓ ∈ anpKey2_region a b π, F ℓ := rfl
  have h2 : ∑ ℓ ∈ anpKey2_region a b π, F ℓ ≤ ∑ ℓ, (if ℓ i₀ ∈ R then F ℓ else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ℓ _ _ => hF0 ℓ
    · intro ℓ hℓ
      have hr := (Finset.mem_filter.1 hℓ).2 i₀
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hR, anpKey2_regionOne]
      exact hr
  have h3 : ∑ ℓ, (if ℓ i₀ ∈ R then F ℓ else 0) =
      ∑ x : Zd d L, ∑ ℓ' : Fin q → Zd d L,
        (if x ∈ R then F (Fin.insertNth (α := fun _ => Zd d L) i₀ x ℓ') else 0) := by
    rw [← (Fin.insertNthEquiv (fun _ => Zd d L) i₀).sum_comp, Fintype.sum_prod_type]
    simp [Fin.insertNthEquiv]
  have h4 : ∀ x : Zd d L, ∑ ℓ' : Fin q → Zd d L,
        (if x ∈ R then F (Fin.insertNth (α := fun _ => Zd d L) i₀ x ℓ') else 0) =
      if x ∈ R then (anpKey2_fixV Γ i₀ s₀).val ξ (fun r => anpKey2_fixLab a b x (anpKey2_ea Γ i₀ r))
          (fun r => anpKey2_fixLab a b x (anpKey2_eb Γ i₀ r)) else 0 := by
    intro x
    by_cases hx : x ∈ R
    · simp only [hx, ↓reduceIte]
      unfold NGraph.val
      refine Finset.sum_congr rfl fun ℓ' _ => ?_
      symm
      refine anpKey2_ep_eq Γ _ (anpKey2_em Γ i₀ s₀) ξ _ _ (anpKey2_fixV_ghost Γ i₀ s₀) ?_ ?_
      · intro k
        rw [(anpKey2_fixV_edge Γ i₀ s₀ k).1]
        exact anpKey2_lab Γ i₀ _ _ x ℓ' (anpKey2_tgt_none Γ i₀ s₀ hs₀ k) _
      · intro k
        rw [(anpKey2_fixV_edge Γ i₀ s₀ k).2]
        exact anpKey2_lab Γ i₀ _ _ x ℓ' (anpKey2_tgt_none Γ i₀ s₀ hs₀ k) _
    · simp [hx]
  rw [h1]
  refine h2.trans ((le_of_eq h3).trans ?_)
  refine le_of_eq ?_
  rw [Finset.sum_congr rfl fun x _ => h4 x]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-! steps, ghost-free paths, ending edges, `n_S` -/

theorem anpKey2_fixV_steps (s₀ : anpKey2_Seg Γ i₀) (j : Fin p) (k : Fin Γ.es.length) :
    (∃ v : NV p (q + 1), (k, v) ∈ Γ.path j) ↔
      ∃ (r : Fin (anpKey2_P Γ i₀)) (v' : NV (anpKey2_P Γ i₀) q), anpKey2_own Γ i₀ r = j ∧
        (anpKey2_em Γ i₀ s₀ k, v') ∈ (anpKey2_fixV Γ i₀ s₀).path r := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := anpKey2_cover Γ i₀ hv
    refine ⟨anpKey2_ee Γ i₀ ⟨j, r⟩,
      anpKey2_rel0 Γ i₀ (Sum.inl (Sum.inr (anpKey2_ee Γ i₀ ⟨j, r⟩))) v, ?_, ?_⟩
    · simp [anpKey2_own]
    · rw [anpKey2_fixV_path]
      exact List.mem_map.2 ⟨(k, v), hr, rfl⟩
  · rintro ⟨r, v', hr, hv'⟩
    obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r
    rw [anpKey2_fixV_path] at hv'
    obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hv'
    have hk : x.1 = k := (anpKey2_em Γ i₀ s₀).injective (Prod.mk.inj hxe).1
    have hs : s.1 = j := by
      simpa [anpKey2_own, anpKey2_ee_symm_fst] using hr
    refine ⟨x.2, ?_⟩
    have := anpKey2_steps_mem_path Γ i₀ hx
    rw [hs] at this
    rw [← hk]
    exact this

theorem anpKey2_fixV_noGhost1 (s₀ : anpKey2_Seg Γ i₀) (r : Fin (anpKey2_P Γ i₀))
    (h : Γ.noGhostPath (anpKey2_own Γ i₀ r) = true) : (anpKey2_fixV Γ i₀ s₀).noGhostPath r = true := by
  obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r
  have hs : anpKey2_own Γ i₀ (anpKey2_ee Γ i₀ s) = s.1 := by simp [anpKey2_own]
  rw [hs] at h
  rw [anpKey2_noGhost_iff] at h ⊢
  rw [anpKey2_fixV_path]
  intro st hst
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hst
  rw [anpKey2_fixV_ghost]
  exact h x (anpKey2_steps_mem_path Γ i₀ hx)

theorem anpKey2_fixV_noGhost2 (hG : Γ.GhostOK) (hN : Γ.IsNested) (s₀ : anpKey2_Seg Γ i₀) (j : Fin p)
    (hj : Γ.noGhostPath j = false) :
    ∃! r, anpKey2_own Γ i₀ r = j ∧ (anpKey2_fixV Γ i₀ s₀).noGhostPath r = false := by
  obtain ⟨st, hst, hgh⟩ := anpKey2_ghostStep Γ j hj
  obtain ⟨r, hr⟩ := anpKey2_cover Γ i₀ hst
  have hnot : ∀ s : anpKey2_Seg Γ i₀, st ∈ anpKey2_steps Γ i₀ s →
      (anpKey2_fixV Γ i₀ s₀).noGhostPath (anpKey2_ee Γ i₀ s) = false := by
    intro s hs
    by_contra hcon
    have hcon' : (anpKey2_fixV Γ i₀ s₀).noGhostPath (anpKey2_ee Γ i₀ s) = true := by simpa using hcon
    rw [anpKey2_noGhost_iff, anpKey2_fixV_path] at hcon'
    have := hcon' _ (List.mem_map.2 ⟨st, hs, rfl⟩)
    rw [anpKey2_fixV_ghost, hgh] at this
    exact Bool.noConfusion this
  refine ⟨anpKey2_ee Γ i₀ ⟨j, r⟩, ⟨by simp [anpKey2_own], hnot _ hr⟩, ?_⟩
  rintro r' ⟨hr1, hr2⟩
  obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r'
  have hs : s.1 = j := by simpa [anpKey2_own, anpKey2_ee_symm_fst] using hr1
  have hfalse : (anpKey2_fixV Γ i₀ s₀).noGhostPath (anpKey2_ee Γ i₀ s) = false := hr2
  have hex : ∃ x ∈ anpKey2_steps Γ i₀ s, (Γ.es.get x.1).ghost = true := by
    by_contra hcon
    push Not at hcon
    have : (anpKey2_fixV Γ i₀ s₀).noGhostPath (anpKey2_ee Γ i₀ s) = true := by
      rw [anpKey2_noGhost_iff, anpKey2_fixV_path]
      intro st' hst'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hst'
      rw [anpKey2_fixV_ghost]
      simpa using hcon x hx
    rw [hfalse] at this
    exact Bool.noConfusion this
  obtain ⟨x, hx, hgx⟩ := hex
  have hxp := anpKey2_steps_mem_path Γ i₀ hx
  rw [hs] at hxp
  have hxx := anpKey2_ghost_unique Γ hG hxp hst hgx hgh
  subst hxx
  have := (anpKey2_edge_unique Γ i₀ hN hx hr rfl).1
  rw [this]

theorem anpKey2_filter_len {p' q' : ℕ} (l : List (NEdge p' q')) :
    (l.filter fun e => !e.ghost).length = (l.map fun e => if (!e.ghost) = true then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hg : a.ghost
    · simp [hg, ih]
      omega
    · simp [hg, ih]

theorem anpKey2_nSolid_sum {p' q' : ℕ} (G : NGraph p' q') :
    G.nSolid = ∑ k : Fin G.es.length, if (G.es.get k).ghost = false then 1 else 0 := by
  unfold NGraph.nSolid
  rw [anpKey2_filter_len, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases (G.es.get k).ghost <;> simp

theorem anpKey2_fixV_nSolid (s₀ : anpKey2_Seg Γ i₀) : (anpKey2_fixV Γ i₀ s₀).nSolid = Γ.nSolid := by
  rw [anpKey2_nSolid_sum, anpKey2_nSolid_sum, ← Equiv.sum_comp (anpKey2_em Γ i₀ s₀)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [anpKey2_fixV_ghost]

theorem anpKey2_seg_end_nil (A : (Fin (Γ.es.length) × NV p (q + 1)) → Bool)
    (l : List (Fin Γ.es.length × NV p (q + 1))) (y : Fin Γ.es.length × NV p (q + 1)) (hy : A y = true) :
    anpKey2_seg A (l ++ [y]) ((l ++ [y]).countP A) = [] := by
  rw [anpKey2_seg_snoc, List.countP_append]
  simp only [List.countP_cons_of_pos hy, List.countP_nil, zero_add]
  rw [anpKey2_seg_nil_of_gt A l _ (Nat.lt_succ_self _)]
  simp

theorem anpKey2_fixV_end (hN : Γ.IsNested) (s₀ : anpKey2_Seg Γ i₀) {j : Fin p} {s : Bool}
    {k : Fin Γ.es.length} (h : Γ.EndAt j s k i₀) :
    ∃ r, anpKey2_own Γ i₀ r = j ∧
      (anpKey2_fixV Γ i₀ s₀).path r = [(anpKey2_em Γ i₀ s₀ k, Sum.inl (Sum.inr r))] ∧
      (if s = true then anpKey2_ea Γ i₀ r = none ∧ anpKey2_eb Γ i₀ r = some (Sum.inr j)
        else anpKey2_ea Γ i₀ r = some (Sum.inl j) ∧ anpKey2_eb Γ i₀ r = none) := by
  obtain ⟨⟨v, hv⟩, hi⟩ := h
  have hch := (anpKey2_walkOK_iff Γ j).1 (hN.2.1 j)
  cases s
  · simp only [Bool.false_eq_true, ite_false] at hv ⊢
    obtain ⟨t, ht⟩ : ∃ t, Γ.path j = (k, v) :: t := by
      cases hp : Γ.path j with
      | nil => rw [hp] at hv; simp at hv
      | cons x t => rw [hp] at hv; simp at hv; exact ⟨t, by rw [hv]⟩
    rw [ht] at hch
    have hvα : v = Sum.inr i₀ := by
      rcases hch.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hi with h | h <;> simp_all
    have hA : anpKey2_isA (Sum.inr i₀) (k, v) = true := (anpKey2_isA_eq _ _).2 hvα
    have hK : 1 ≤ anpKey2_K Γ i₀ j := by
      unfold anpKey2_K
      rw [ht, List.countP_cons_of_pos hA]
      omega
    have hsteps : anpKey2_steps Γ i₀ ⟨j, 0⟩ = [(k, v)] := by
      unfold anpKey2_steps
      simp only [Fin.val_zero]
      rw [ht, anpKey2_seg_zero_pos _ _ hA]
    refine ⟨anpKey2_ee Γ i₀ ⟨j, 0⟩, by simp [anpKey2_own], ?_, ?_, ?_⟩
    · rw [anpKey2_fixV_path, hsteps, hvα]
      simp [anpKey2_rel0_self]
    · rw [anpKey2_ea_ee]; simp
    · rw [anpKey2_eb_ee]
      have : ¬ (0 = anpKey2_K Γ i₀ j) := by omega
      simp only [Fin.val_zero, this, ↓reduceIte]
  · simp only [ite_true] at hv ⊢
    obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 hv
    rw [hl] at hch
    obtain ⟨z, hz, hstep, hvb⟩ := (anpKey2_chain_snoc Γ l (k, v) _ _).1 hch
    simp only at hvb
    have hzα : z = Sum.inr i₀ := by
      rcases hstep with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hi with h | h <;> simp_all
    subst hzα
    obtain ⟨l', y, rfl⟩ : ∃ l' y, l = l' ++ [y] := by
      rcases List.eq_nil_or_concat l with h | ⟨l', y, h⟩
      · rw [h] at hz; simp [anpKey2_chain] at hz
      · exact ⟨l', y, by simpa using h⟩
    have hy2 := anpKey2_chain_end Γ l' y _ _ hz
    have hA : anpKey2_isA (Sum.inr i₀) y = true := (anpKey2_isA_eq _ _).2 hy2.symm
    have hx : (k, v).2 ≠ Sum.inr i₀ := by rw [hvb]; simp
    have hAx : anpKey2_isA (Sum.inr i₀) (k, v) = false := by simpa [anpKey2_isA] using hx
    have hK : anpKey2_K Γ i₀ j = (l' ++ [y]).countP (anpKey2_isA (Sum.inr i₀)) := by
      unfold anpKey2_K
      rw [hl, List.countP_append]
      simp [hAx]
    have hK1 : 1 ≤ anpKey2_K Γ i₀ j := by
      rw [hK, List.countP_append, List.countP_cons_of_pos hA]; omega
    have hsteps : anpKey2_steps Γ i₀ ⟨j, Fin.last _⟩ = [(k, v)] := by
      unfold anpKey2_steps
      simp only [Fin.val_last]
      rw [hl, anpKey2_seg_snoc, hK, anpKey2_seg_end_nil Γ _ l' y hA]
      simp
    refine ⟨anpKey2_ee Γ i₀ ⟨j, Fin.last _⟩, by simp [anpKey2_own], ?_, ?_, ?_⟩
    · rw [anpKey2_fixV_path, hsteps]
      simp only [List.map_cons, List.map_nil, hvb]
      rw [anpKey2_rel0]
    · rw [anpKey2_ea_ee]
      have : ¬ (anpKey2_K Γ i₀ j = 0) := by omega
      simp [this]
    · rw [anpKey2_eb_ee]; simp

theorem anpKey2_exists_s₀ (hN : Γ.IsNested) :
    ∃ s₀ : anpKey2_Seg Γ i₀, s₀.2.val ≠ anpKey2_K Γ i₀ s₀.1 := by
  obtain ⟨i, j, -, hi, -⟩ := hN.2.2.2.2.1 i₀
  have hch := (anpKey2_walkOK_iff Γ i).1 (hN.2.1 i)
  obtain ⟨st, hst, h2⟩ := anpKey2_chain_visit Γ (Sum.inr i₀) (Γ.path i) _ _ hch (by simp) hi
  have hA : anpKey2_isA (Sum.inr i₀) st = true := (anpKey2_isA_eq _ _).2 h2
  refine ⟨⟨i, 0⟩, ?_⟩
  have : 0 < anpKey2_K Γ i₀ i := List.countP_pos_iff.2 ⟨st, hst, hA⟩
  simp only [Fin.val_zero]
  omega

theorem anpKey2_ea_unique (j : Fin p) : ∃! r, anpKey2_ea Γ i₀ r = some (Sum.inl j) := by
  refine ⟨anpKey2_ee Γ i₀ ⟨j, 0⟩, ?_, ?_⟩
  · show anpKey2_ea Γ i₀ _ = _
    rw [anpKey2_ea_ee]; simp
  · intro r hr
    obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r
    rw [anpKey2_ea_ee] at hr
    rcases s with ⟨j', r'⟩
    simp only at hr
    split_ifs at hr with h0
    · have : j' = j := by simpa using hr
      subst this
      have : r' = 0 := Fin.ext h0
      subst this
      rfl

theorem anpKey2_eb_unique (j : Fin p) : ∃! r, anpKey2_eb Γ i₀ r = some (Sum.inr j) := by
  refine ⟨anpKey2_ee Γ i₀ ⟨j, Fin.last _⟩, ?_, ?_⟩
  · show anpKey2_eb Γ i₀ _ = _
    rw [anpKey2_eb_ee]; simp
  · intro r hr
    obtain ⟨s, rfl⟩ := (anpKey2_ee Γ i₀).surjective r
    rw [anpKey2_eb_ee] at hr
    rcases s with ⟨j', r'⟩
    simp only at hr
    split_ifs at hr with h0
    · have : j' = j := by simpa using hr
      subst this
      have : r' = Fin.last _ := Fin.ext h0
      subst this
      rfl

/-- Target 5: vertex fixing (`7_8:1158-1172`, `:1209-1237`): the internal vertex `α_{i₀}` becomes external and every
path is split at each visit of `α_{i₀}`; new path `r` comes from old path `own r`, its ends are `ea r`, `eb r`.
(F1) hypotheses of the induction; (F2) the edges, their ghost flags and labels (`em`); (F3) the value on `𝐃_π`
(only the row `π i₀` survives); (F4) ends; (F5) steps; (F6) ghost-free paths; (F7) an ending edge at `α_{i₀}` is a
one-step path; (F8) `n_S` unchanged. -/
theorem anpKey2_fix (p q : ℕ) (Γ : NGraph p (q + 1)) (i₀ : Fin (q + 1)) (hG : Γ.GhostOK)
    (hN : Γ.IsNested) :
    ∃ (p' : ℕ) (Γ' : NGraph p' q) (ea eb : Fin p' → Option (Fin p ⊕ Fin p)) (own : Fin p' → Fin p)
      (em : Fin Γ.es.length ≃ Fin Γ'.es.length),
      -- (F1)
      (Γ'.GhostOK ∧ Γ'.IsNested) ∧
      -- (F2)
      (∀ k, (Γ'.es.get (em k)).ghost = (Γ.es.get k).ghost) ∧
      (∀ (ι : Type) (a b : Fin p → ι) (x : ι) (ℓ : Fin q → ι) (k : Fin Γ.es.length),
        Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r))) ℓ
            (Γ'.es.get (em k)).u =
          Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).u ∧
        Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r))) ℓ
            (Γ'.es.get (em k)).v =
          Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).v) ∧
      -- (F3)
      (∀ (d L : ℕ) [NeZero L] (ξ : Zd d L → Zd d L → ℝ), (∀ α β, 0 ≤ ξ α β) →
        ∀ (a b : Fin p → Zd d L) (π : Fin (q + 1) → Fin p → Bool),
          Γ.valOn ξ a b (anpKey2_region a b π) ≤
            ∑ x ∈ anpKey2_regionOne a b (π i₀),
              Γ'.val ξ (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r))) ∧
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
      (∀ (j : Fin p) (s : Bool) (k : Fin Γ.es.length), Γ.EndAt j s k i₀ →
        ∃ r, own r = j ∧ Γ'.path r = [(em k, Sum.inl (Sum.inr r))] ∧
          (if s = true then ea r = none ∧ eb r = some (Sum.inr j)
            else ea r = some (Sum.inl j) ∧ eb r = none)) ∧
      -- (F8)
      Γ'.nSolid = Γ.nSolid := by
  obtain ⟨s₀, hs₀⟩ := anpKey2_exists_s₀ Γ i₀ hN
  refine ⟨anpKey2_P Γ i₀, anpKey2_fixV Γ i₀ s₀, anpKey2_ea Γ i₀, anpKey2_eb Γ i₀, anpKey2_own Γ i₀,
    anpKey2_em Γ i₀ s₀, ⟨anpKey2_fixV_ghostOK Γ i₀ hG hN s₀, anpKey2_fixV_nested Γ i₀ hN s₀ hs₀⟩,
    anpKey2_fixV_ghost Γ i₀ s₀, ?_, ?_, ?_, ?_, anpKey2_ea_unique Γ i₀, anpKey2_eb_unique Γ i₀,
    anpKey2_fixV_steps Γ i₀ s₀, anpKey2_fixV_noGhost1 Γ i₀ s₀, anpKey2_fixV_noGhost2 Γ i₀ hG hN s₀,
    fun j s k h => anpKey2_fixV_end Γ i₀ hN s₀ h, anpKey2_fixV_nSolid Γ i₀ s₀⟩
  · intro ι a b x ℓ k
    refine ⟨?_, ?_⟩
    · rw [(anpKey2_fixV_edge Γ i₀ s₀ k).1]
      exact anpKey2_lab Γ i₀ a b x ℓ (anpKey2_tgt_none Γ i₀ s₀ hs₀ k) _
    · rw [(anpKey2_fixV_edge Γ i₀ s₀ k).2]
      exact anpKey2_lab Γ i₀ a b x ℓ (anpKey2_tgt_none Γ i₀ s₀ hs₀ k) _
  · intro d L _ ξ hnn a b π
    exact anpKey2_fixV_value Γ i₀ s₀ hs₀ ξ hnn a b π
  · intro r
    unfold anpKey2_ea anpKey2_own
    split_ifs <;> simp
  · intro r
    unfold anpKey2_eb anpKey2_own
    split_ifs <;> simp

end Fix

/-! ## 6. The step from the regions and the case split -/

/-- Target 6: the merged step pin from the step on regions (targets 2 and 4). -/
theorem anpDetGhStep_of_reg (d : ℕ) (h : AnpDetGhRegStep d) : AnpDetGhStep d := by
  intro q hq IH p Γ hG hN
  refine anpDetGh_of_reg d p q Γ fun π => ?_
  exact anpDetGhReg_of_noA2 d p q π (fun Γ' hG' hN' hno => h q hq IH p Γ' π hG' hN' hno) Γ hG hN

/-- Target 6: the case split (proved here; LW-12f plugs the three cases in). -/
theorem anpDetGhRegStep_of_cases (d : ℕ) (hI : AnpDetGhCaseI d) (hIII : AnpDetGhCaseIII d)
    (hIV : AnpDetGhCaseIV d) : AnpDetGhRegStep d := by
  intro q hq IH p Γ π hG hN hno
  by_cases h1 : AnpCaseI Γ π
  · exact hI q hq IH p Γ π hG hN hno h1
  · by_cases h3 : AnpCaseIII Γ π
    · exact hIII q hq IH p Γ π hG hN hno h3
    · exact hIV q hq IH p Γ π hG hN hno h1 h3

/-! ## 7. Compiled nonempty instances at `d = 3` -/

section Instances

instance anpKey2_decGhostOK {p q : ℕ} (Γ : NGraph p q) : Decidable Γ.GhostOK := by unfold NGraph.GhostOK; infer_instance

instance anpKey2_decCaseI {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) :
    Decidable (AnpCaseI Γ π) := by
  unfold AnpCaseI; infer_instance

instance anpKey2_decCaseIII {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) :
    Decidable (AnpCaseIII Γ π) := by
  unfold AnpCaseIII; infer_instance

/-- `figAux` (`7_8:626-647`) with its two last edges (`ℳ₂ y`) made ghost: on `π ≡ false` every ending edge
is B1 (at `ℳ₁`) or B2 (at `ℳ₂`); no A2; Case (I) at `ℳ₁` and Case (III) at `ℳ₂` (`deg_s(ℳ₂) = 2`). -/
def anpKey2_figAuxGh : NGraph 2 2 where
  es := [⟨false, .inl (.inl 0), .inr 0⟩, ⟨false, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inr 1⟩,
         ⟨false, .inr 0, .inr 1⟩, ⟨true, .inr 1, .inl (.inr 0)⟩, ⟨true, .inr 1, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (2, .inr 1), (4, .inl (.inr 0))]
    else [(1, .inr 0), (3, .inr 1), (5, .inl (.inr 1))]

theorem anpKey2_figAuxGh_ghostOK : anpKey2_figAuxGh.GhostOK := by
  unfold NGraph.GhostOK
  decide +kernel

theorem anpKey2_figAuxGh_nested : anpKey2_figAuxGh.IsNested := by
  unfold NGraph.IsNested
  decide +kernel

theorem anpKey2_figAux_ghostOK : figAux.GhostOK := anpKey_ghostOK_of_noGhost figAux_nested.2

/-- Instance (1): `figAuxGh` is a legal input with no A2 edge, in Cases (I) (at `ℳ₁`: two B1 edges) and (III)
(at `ℳ₂`: two B2 edges, `deg_s = 2`). -/
theorem anpKey2_inst_figAuxGh :
    anpKey2_figAuxGh.GhostOK ∧ anpKey2_figAuxGh.IsNested ∧ anpKey2_figAuxGh.NoA2 (fun _ _ => false) ∧
      AnpCaseI anpKey2_figAuxGh (fun _ _ => false) ∧ AnpCaseIII anpKey2_figAuxGh (fun _ _ => false) ∧
      anpKey2_figAuxGh.degS 1 = 2 := by
  refine ⟨anpKey2_figAuxGh_ghostOK, anpKey2_figAuxGh_nested, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

/-- The edge `n` of `figAux` (six edges). -/
def anpKey2_eAux (n : ℕ) (h : n < 6 := by decide) : Fin figAux.es.length := ⟨n, h⟩

/-- The edge `n` of `figAuxGh` (six edges). -/
def anpKey2_eGh (n : ℕ) (h : n < 6 := by decide) : Fin anpKey2_figAuxGh.es.length := ⟨n, h⟩

/-- Instance (2): `figAux` (no ghost) on `π ≡ false` has two A2 edges (`ℳ₂ y`, at the `b`-ends); the A2
replacement lets `anpDetGhReg_of_noA2` reduce `(kwuyayw)` at `figAux` to the graphs without A2 edge (the premise
`hreg` is the pin of LW-12c-f). -/
theorem anpKey2_inst_figAux_a2 :
    ¬ figAux.NoA2 (fun _ _ => false) ∧ figAux.IsA2 (fun _ _ => false) 0 true (anpKey2_eAux 4) 1 ∧
      figAux.IsA2 (fun _ _ => false) 1 true (anpKey2_eAux 5) 1 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals decide +kernel

theorem anpKey2_inst_figAux_reg
    (hreg : ∀ Γ : NGraph 2 2, Γ.GhostOK → Γ.IsNested → Γ.NoA2 (fun _ _ => false) →
      AnpDetGhRegAt 3 Γ (fun _ _ => false)) :
    AnpDetGhRegAt 3 figAux (fun _ _ => false) :=
  anpDetGhReg_of_noA2 3 2 2 (fun _ _ => false) hreg figAux anpKey2_figAux_ghostOK figAux_nested.1

/-- Instance (2'): the regions cover, at `figAuxGh`: `(kwuyayw)` for the 16 regions gives `(adsuu22)`. -/
theorem anpKey2_inst_cover (h : ∀ π, AnpDetGhRegAt 3 anpKey2_figAuxGh π) : AnpDetGhAt 3 anpKey2_figAuxGh :=
  anpDetGh_of_reg 3 2 2 anpKey2_figAuxGh h

/-- Instance (3): the chain from the three case pins to the merged step pin and to `LWAnpKeyGh 3`. -/
theorem anpKey2_inst_chain :
    AnpDetGhCaseI 3 → AnpDetGhCaseIII 3 → AnpDetGhCaseIV 3 → LWAnpKeyGh 3 :=
  fun hI hIII hIV => lwAnpKeyGh_of_det 3 (anpDetGh_of_step 3 (anpDetGh_zero 3)
    (anpDetGhStep_of_reg 3 (anpDetGhRegStep_of_cases 3 hI hIII hIV)))

/-- Instance (3'): the two ends of the chain at `d = 3`: the step on regions gives `AnpDetGhAt 3 figAux`. -/
theorem anpKey2_inst_figAux_det (h : AnpDetGhRegStep 3) : AnpDetGhAt 3 figAux :=
  anpDetGh_of_step 3 (anpDetGh_zero 3) (anpDetGhStep_of_reg 3 h) 2 2 figAux anpKey2_figAux_ghostOK
    figAux_nested.1

/-- Instance (3a), the half-distance fact at `d = 3`, `L = 5`: `x = 0`, `y = (2,2,2)`, `z = (1,1,1)`
(`|z - x| = |z - y| = 1`, `|x - y| = 2`: the inequality is tight). -/
theorem anpKey2_inst_half :
    let x : Zd 3 5 := fun _ => 0
    let y : Zd 3 5 := fun _ => 2
    let z : Zd 3 5 := fun _ => 1
    zdistInf 3 5 (x - y) ≤ 2 * zdistInf 3 5 (z - y) :=
  anpKey2_half 3 5 _ _ _ (by decide +kernel)

/-- The constant point `(n, n, n)` of `Z_5^3`. -/
def anpKey2_pt (n : ℕ) : Zd 3 5 := fun _ => (n : ZMod 5)

set_option maxRecDepth 4000 in
/-- Instance (3b), the region fact at `d = 3`, `L = 5`, `p = q = 1`, `a = 0`, `b = (2,2,2)`: `ℓ = (1,1,1)` lies
in `𝐃_π` for `π = false` (`|ℓ - a| = |ℓ - b| = 1`), and `ℓ' = b` for `π = true`. -/
theorem anpKey2_inst_reg_half :
    ((fun _ => anpKey2_pt 1 : Fin 1 → Zd 3 5) ∈
        anpKey2_region (fun _ => anpKey2_pt 0) (fun _ => anpKey2_pt 2) (fun _ _ => false : Fin 1 → Fin 1 → Bool) ∧
      zdistInf 3 5 (anpKey2_pt 0 - anpKey2_pt 2) ≤ 2 * zdistInf 3 5 (anpKey2_pt 1 - anpKey2_pt 2)) ∧
    ((fun _ => anpKey2_pt 2 : Fin 1 → Zd 3 5) ∈
        anpKey2_region (fun _ => anpKey2_pt 0) (fun _ => anpKey2_pt 2) (fun _ _ => true : Fin 1 → Fin 1 → Bool) ∧
      zdistInf 3 5 (anpKey2_pt 0 - anpKey2_pt 2) ≤ 2 * zdistInf 3 5 (anpKey2_pt 2 - anpKey2_pt 0)) := by
  have hm : (fun _ => anpKey2_pt 1 : Fin 1 → Zd 3 5) ∈
      anpKey2_region (fun _ => anpKey2_pt 0) (fun _ => anpKey2_pt 2) (fun _ _ => false : Fin 1 → Fin 1 → Bool) := by
    simp only [anpKey2_region, Finset.mem_filter, Finset.mem_univ, true_and]
    decide +kernel
  have hm' : (fun _ => anpKey2_pt 2 : Fin 1 → Zd 3 5) ∈
      anpKey2_region (fun _ => anpKey2_pt 0) (fun _ => anpKey2_pt 2) (fun _ _ => true : Fin 1 → Fin 1 → Bool) := by
    simp only [anpKey2_region, Finset.mem_filter, Finset.mem_univ, true_and]
    decide +kernel
  have h1 := (anpKey2_reg_half 3 5 1 1 (fun _ => anpKey2_pt 0) (fun _ => anpKey2_pt 2)
    (fun _ _ => false) (fun _ => anpKey2_pt 1) hm 0 0).1 rfl
  have h2 := (anpKey2_reg_half 3 5 1 1 (fun _ => anpKey2_pt 0) (fun _ => anpKey2_pt 2)
    (fun _ _ => true) (fun _ => anpKey2_pt 2) hm' 0 0).2 rfl
  exact ⟨⟨hm, h1⟩, ⟨hm', h2⟩⟩

/-- Instance (3c): the ending-edge types at `figAuxGh`: the first step of `𝔓_0` is a B1 edge. -/
theorem anpKey2_inst_endTypes :
    anpKey2_figAuxGh.IsB1 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∧
    (anpKey2_figAuxGh.IsA1 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∨
      anpKey2_figAuxGh.IsA2 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∨
      anpKey2_figAuxGh.IsB1 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∨
      anpKey2_figAuxGh.IsB2 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0) := by
  have h : anpKey2_figAuxGh.EndAt 0 false (anpKey2_eGh 0) 0 := by decide +kernel
  exact ⟨by decide +kernel, anpKey2_endTypes 2 2 anpKey2_figAuxGh (fun _ _ => false) 0 false _ 0 h⟩

/-- Instance (3d): two B1 ending edges at `ℳ₁` lie on distinct paths (`anpKey2_caseI_ne`). -/
theorem anpKey2_inst_caseI_ne : (0 : Fin 2) ≠ 1 :=
  anpKey2_caseI_ne anpKey2_figAuxGh (fun _ _ => false) anpKey2_figAuxGh_ghostOK
    (i := 0) (j₁ := 0) (j₂ := 1) (s₁ := false) (s₂ := false) (k₁ := anpKey2_eGh 0) (k₂ := anpKey2_eGh 1)
    (by decide)
    (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel))

/-- Instance (4): vertex fixing at `figAuxGh`, `i₀ = 0` (`ℳ₁`): the result is a legal input with the same number
of solid edges, and the ending edges `(a_0, ℳ₁)`, `(a_1, ℳ₁)` (type B1) are one-step paths with external ends. -/
theorem anpKey2_inst_fix :
    ∃ (p' : ℕ) (Γ' : NGraph p' 1) (ea eb : Fin p' → Option (Fin 2 ⊕ Fin 2)) (own : Fin p' → Fin 2)
      (em : Fin anpKey2_figAuxGh.es.length ≃ Fin Γ'.es.length),
      Γ'.GhostOK ∧ Γ'.IsNested ∧ Γ'.nSolid = 4 ∧
      (∃ r, own r = 0 ∧ Γ'.path r = [(em (anpKey2_eGh 0), Sum.inl (Sum.inr r))] ∧
        ea r = some (Sum.inl 0) ∧ eb r = none) ∧
      (∃ r, own r = 1 ∧ Γ'.path r = [(em (anpKey2_eGh 1), Sum.inl (Sum.inr r))] ∧
        ea r = some (Sum.inl 1) ∧ eb r = none) := by
  obtain ⟨p', Γ', ea, eb, own, em, ⟨hG, hN⟩, -, -, -, -, -, -, -, -, -, -, h7, h8⟩ :=
    anpKey2_fix 2 1 anpKey2_figAuxGh 0 anpKey2_figAuxGh_ghostOK anpKey2_figAuxGh_nested
  have e0 : anpKey2_figAuxGh.EndAt 0 false (anpKey2_eGh 0) 0 := by decide +kernel
  have e1 : anpKey2_figAuxGh.EndAt 1 false (anpKey2_eGh 1) 0 := by decide +kernel
  have hs : anpKey2_figAuxGh.nSolid = 4 := by decide +kernel
  obtain ⟨r0, h0, hp0, hea0, heb0⟩ := h7 0 false _ e0
  obtain ⟨r1, h1, hp1, hea1, heb1⟩ := h7 1 false _ e1
  exact ⟨p', Γ', ea, eb, own, em, hG, hN, h8.trans hs, ⟨r0, h0, hp0, hea0, heb0⟩,
    ⟨r1, h1, hp1, hea1, heb1⟩⟩

/-- Instance (4'): the number of paths after fixing `ℳ₁` in `figAuxGh`: `p' = 4 = 2 + 2` (each path visits `ℳ₁`
once and is cut in two). -/
theorem anpKey2_inst_fixP : anpKey2_P anpKey2_figAuxGh 0 = 4 := by
  decide +kernel

end Instances

end RBM.Graph
