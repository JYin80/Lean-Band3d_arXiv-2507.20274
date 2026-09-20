/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.Unique

/-!
# The tree representation at `n = 3`

`(eq_Ktree)` says `K^(n) = W^{-d(n-1)} Σ_{Γ ∈ TSP(P_a)} Γ^(n)`.  `Loop/TreeRep.lean` states
it for `n ≥ 4` and carries it as a hypothesis; this file **proves it at `n = 3`**, the first
length where the tree sum is not a single edge.

A triangle has no diagonals, so `TSP 3 = {∅}` (`RBM.Loop.TSP_three`, Q14) and the tree sum
is the single star `Σ_b Θ^(σ₀σ₁)(a₀,b) Θ^(σ₁σ₂)(a₁,b) Θ^(σ₂σ₀)(a₂,b)`.  The content is the
match between its three boundary edges and the three `(k,l)` terms of `(pro_dyncalK)`:

* `(k,l) = (1,2)` cuts off the `2`-chain `(σ₀,σ₁)` and replaces the label `a₀`;
* `(2,3)` cuts off `(σ₁,σ₂)` and replaces `a₁`;
* `(1,3)` cuts off `(σ₀,σ₂)` and replaces `a₂` -- here the `2`-chain sits on the *left* of
  `S^(B)`, which is why `RBM.Loop.sum_SB_starRight` exists alongside `sum_SB_starLeft`.

Differentiating the edge at `aᵢ` inserts `S^(B)` there (`hasDerivAt_Theta_mul_apply`, Q23),
and summing the corresponding `(k,l)` term against `S^(B)` rebuilds exactly that sandwich.

## Main results

* `RBM.Loop.treeEqRhs_three` : the three terms of `(pro_dyncalK)` at `n = 3`
* `RBM.Loop.treeSum_three`   : the tree sum is the star
* `RBM.Loop.kThree`, `RBM.Loop.hasDerivAt_kThree`, `RBM.Loop.kThree_zero` : the tree value
  solves `(pro_dyncalK)` with the `M`-loop initial value
* `RBM.Loop.kThree_eq_of_isKLoop` : **every** family of `K`-loops whose `2`-loops are
  bounded has these `3`-loops -- `(eq_Ktree)` at `n = 3`, with no hypothesis about the shape
  of the solution.  This is `eq_on_level` (Q22a) at `n = 3`, fed by
  `kTwoFormula_of_isKLoop` at length `2`.

The general `n` is `docs/QUEUE.md`, Q22b; `n = 4` is where internal edges first appear, and
the `polyVal` recursion of `Loop/Partition.lean` is what will carry them.
-/
namespace RBM.Loop

open Finset
open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ}

/-- **Index check at `n = 3`.**  The three terms of `(pro_dyncalK)`, `(k,l) = (1,2)`,
`(1,3)`, `(2,3)`: each cuts the triangle into a `2`-chain and a `3`-chain, and the three
cuts replace the labels `a₀`, `a₂`, `a₁` in turn. -/
theorem treeEqRhs_three (K : LoopIdx (Zd d L) → ℂ) (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L) :
    treeEqRhs d L W g K ⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩
      = ((W : ℂ) ^ d) *
          ((∑ x : Zd d L, ∑ y : Zd d L,
              K ⟨[σ₀, σ₁, σ₂], [x, a₁, a₂]⟩ * SB d L g x y * K ⟨[σ₀, σ₁], [a₀, y]⟩)
            + (∑ x : Zd d L, ∑ y : Zd d L,
              K ⟨[σ₀, σ₂], [x, a₂]⟩ * SB d L g x y * K ⟨[σ₀, σ₁, σ₂], [a₀, a₁, y]⟩)
            + ∑ x : Zd d L, ∑ y : Zd d L,
              K ⟨[σ₀, σ₁, σ₂], [a₀, x, a₂]⟩ * SB d L g x y * K ⟨[σ₁, σ₂], [a₁, y]⟩) := by
  have hlen : (⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩ : LoopIdx (Zd d L)).length = 3 := rfl
  have h13 : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have hIoc1 : Ioc 1 3 = ({2, 3} : Finset ℕ) := by decide
  have hIoc2 : Ioc 2 3 = ({3} : Finset ℕ) := by decide
  have hIoc3 : Ioc 3 3 = (∅ : Finset ℕ) := by decide
  rw [treeEqRhs, hlen, h13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    hIoc1, hIoc2, hIoc3, Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_singleton, Finset.sum_empty, add_zero]
  congr 1

/-! ### The tree sum at `n = 3` -/

/-- The only canonical partition of a triangle is the star, and its value is
`Σ_b Θ^(σ₀σ₁)(a₀,b) Θ^(σ₁σ₂)(a₁,b) Θ^(σ₂σ₀)(a₂,b)`. -/
theorem treeVal_three_nil (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L) :
    treeVal d L g m t [σ₀, σ₁, σ₂] [a₀, a₁, a₂] []
      = ∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b
          * thetaEdge d L g m t σ₂ σ₀ a₂ b := by
  have hbd : bdList d L g m t [σ₀, σ₁, σ₂] [a₀, a₁, a₂]
      = [(a₀, thetaEdge d L g m t σ₀ σ₁), (a₁, thetaEdge d L g m t σ₁ σ₂),
        (a₂, thetaEdge d L g m t σ₂ σ₀)] := by
    simp only [bdList, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil]
    rfl
  rw [treeVal, ite_eq_right (by simp), hbd, polyVal]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- `Σ_{Γ ∈ TSP(P_a)}` at `n = 3` is the single star term. -/
theorem treeSum_three (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L) :
    treeSum d L g m t [σ₀, σ₁, σ₂] [a₀, a₁, a₂]
      = ∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b
          * thetaEdge d L g m t σ₂ σ₀ a₂ b := by
  have hlen : ([σ₀, σ₁, σ₂] : List Bool).length = 3 := rfl
  rw [treeSum, hlen, TSP_three, Finset.sum_singleton, show diagList (∅ : Finset (Fin 3 × Fin 3))
    = [] from by simp [diagList], treeVal_three_nil]

variable (d L W g)

/-- `(eq_Ktree)` at `n = 3`: `K^(3)_{t,σ,a} = W^{-2d} m(σ₀)m(σ₁)m(σ₂) Σ_{Γ} Γ`. -/
noncomputable def kThree (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) ^ 2 * (m σ₀ * (m σ₁ * m σ₂))
    * treeSum d L g m t [σ₀, σ₁, σ₂] [a₀, a₁, a₂]

variable {d L W g}

/-- At `t = 0` the tree value is the `M`-loop value `(eq:initial_K)` at `n = 3`. -/
theorem kThree_zero (m : Bool → ℂ) (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L) :
    kThree d L W g m 0 σ₀ σ₁ σ₂ a₀ a₁ a₂ = MLoop d L W m ⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩ := by
  have hedge : ∀ s s' : Bool, thetaEdge d L g m 0 s s' = 1 := by
    intro s s'
    rw [thetaEdge, Complex.ofReal_zero, zero_mul, Theta_zero]
  have hstar : treeSum d L g m 0 [σ₀, σ₁, σ₂] [a₀, a₁, a₂]
      = if a₀ = a₁ ∧ a₁ = a₂ then 1 else 0 := by
    rw [treeSum_three]
    simp only [hedge, Matrix.one_apply]
    rw [Finset.sum_eq_single_of_mem a₀ (Finset.mem_univ _)
      (fun b _ hb => by simp [Ne.symm hb])]
    by_cases h₁ : a₁ = a₀
    · subst h₁
      by_cases h₂ : a₂ = a₁
      · subst h₂; simp
      · simp [h₂, Ne.symm h₂]
    · simp [h₁, Ne.symm h₁]
  have hall : (∀ x ∈ [a₀, a₁, a₂], ∀ y ∈ [a₀, a₁, a₂], x = y) ↔ (a₀ = a₁ ∧ a₁ = a₂) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨-, h₁, -⟩, ⟨-, -, h₂⟩, -⟩
      exact ⟨h₁, h₂⟩
    · rintro ⟨rfl, rfl⟩
      simp
  rw [kThree, hstar, MLoop]
  simp only [LoopIdx.length, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, hall]


/-! ### The tree value solves `(pro_dyncalK)` at `n = 3` -/

/-- Summing an edge against `S^(B)` on both sides: `Σ_{x,y} E_{uy} S_{xy} E_{xv}
= (E S^(B) E)_{uv}`, by the symmetry of `S^(B)`.  This is the identity that turns each
`(k,l)` term of `(pro_dyncalK)` into the derivative of one boundary edge. -/
theorem sum_sum_mul_SB (E : Matrix (Zd d L) (Zd d L) ℂ) (u v : Zd d L) :
    ∑ x : Zd d L, ∑ y : Zd d L, E u y * SB d L g x y * E x v
      = (E * SB d L g * E) u v := by
  have hsym : ∀ x y : Zd d L, SB d L g x y = SB d L g y x := fun x y =>
    congrFun (congrFun (SB_isSymm d L g) y) x
  simp only [Matrix.mul_apply, Finset.sum_mul, hsym]

/-- The `(k,l)` term with the `3`-chain on the left: summing a star against `S^(B)` and one
more edge rebuilds the sandwich `E S^(B) E` on the boundary edge. -/
theorem sum_SB_starLeft (E : Matrix (Zd d L) (Zd d L) ℂ) (u : Zd d L) (F : Zd d L → ℂ) :
    ∑ x : Zd d L, ∑ y : Zd d L, (∑ b : Zd d L, E x b * F b) * SB d L g x y * E u y
      = ∑ b : Zd d L, (E * SB d L g * E) u b * F b := by
  have expand : ∀ x y : Zd d L, (∑ b : Zd d L, E x b * F b) * SB d L g x y * E u y
      = ∑ b : Zd d L, E u y * SB d L g x y * E x b * F b := by
    intro x y
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  calc ∑ x : Zd d L, ∑ y : Zd d L, (∑ b : Zd d L, E x b * F b) * SB d L g x y * E u y
      = ∑ x : Zd d L, ∑ y : Zd d L, ∑ b : Zd d L,
          E u y * SB d L g x y * E x b * F b :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => expand x y
    _ = ∑ x : Zd d L, ∑ b : Zd d L, ∑ y : Zd d L,
          E u y * SB d L g x y * E x b * F b :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ b : Zd d L, ∑ x : Zd d L, ∑ y : Zd d L,
          E u y * SB d L g x y * E x b * F b := Finset.sum_comm
    _ = ∑ b : Zd d L, (E * SB d L g * E) u b * F b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← sum_SB_starLeft_aux E u b F]
  where
    sum_SB_starLeft_aux (E : Matrix (Zd d L) (Zd d L) ℂ) (u b : Zd d L) (F : Zd d L → ℂ) :
        (E * SB d L g * E) u b * F b
          = ∑ x : Zd d L, ∑ y : Zd d L, E u y * SB d L g x y * E x b * F b := by
      rw [← sum_sum_mul_SB E u b, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]

/-- The `(k,l)` term with the `3`-chain on the right. -/
theorem sum_SB_starRight (E : Matrix (Zd d L) (Zd d L) ℂ) (u : Zd d L) (F : Zd d L → ℂ) :
    ∑ x : Zd d L, ∑ y : Zd d L, E u x * SB d L g x y * (∑ b : Zd d L, E y b * F b)
      = ∑ b : Zd d L, (E * SB d L g * E) u b * F b := by
  have expand : ∀ x y : Zd d L, E u x * SB d L g x y * (∑ b : Zd d L, E y b * F b)
      = ∑ b : Zd d L, E u x * SB d L g x y * E y b * F b := by
    intro x y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  calc ∑ x : Zd d L, ∑ y : Zd d L, E u x * SB d L g x y * (∑ b : Zd d L, E y b * F b)
      = ∑ x : Zd d L, ∑ y : Zd d L, ∑ b : Zd d L, E u x * SB d L g x y * E y b * F b :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => expand x y
    _ = ∑ x : Zd d L, ∑ b : Zd d L, ∑ y : Zd d L, E u x * SB d L g x y * E y b * F b :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ b : Zd d L, ∑ x : Zd d L, ∑ y : Zd d L, E u x * SB d L g x y * E y b * F b :=
        Finset.sum_comm
    _ = ∑ b : Zd d L, (E * SB d L g * E) u b * F b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [Matrix.mul_apply, Finset.sum_mul]
        rw [Finset.sum_comm]

/-- The derivative of the star: one term per boundary edge. -/
theorem hasDerivAt_starThree (hS : ‖SB d L g‖ = 1) (m : Bool → ℂ) {t : ℝ}
    {σ₀ σ₁ σ₂ : Bool} (h₀₁ : ‖(t : ℂ) * (m σ₀ * m σ₁)‖ < 1)
    (h₁₂ : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h₂₀ : ‖(t : ℂ) * (m σ₂ * m σ₀)‖ < 1)
    (a₀ a₁ a₂ : Zd d L) :
    HasDerivAt
      (fun s => ∑ b : Zd d L, thetaEdge d L g m s σ₀ σ₁ a₀ b
        * thetaEdge d L g m s σ₁ σ₂ a₁ b * thetaEdge d L g m s σ₂ σ₀ a₂ b)
      (∑ b : Zd d L,
        ((m σ₀ * m σ₁) * ((thetaEdge d L g m t σ₀ σ₁ * SB d L g * thetaEdge d L g m t σ₀ σ₁)
            a₀ b) * thetaEdge d L g m t σ₁ σ₂ a₁ b * thetaEdge d L g m t σ₂ σ₀ a₂ b
        + thetaEdge d L g m t σ₀ σ₁ a₀ b
            * ((m σ₁ * m σ₂) * ((thetaEdge d L g m t σ₁ σ₂ * SB d L g
              * thetaEdge d L g m t σ₁ σ₂) a₁ b)) * thetaEdge d L g m t σ₂ σ₀ a₂ b
        + thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b
            * ((m σ₂ * m σ₀) * ((thetaEdge d L g m t σ₂ σ₀ * SB d L g
              * thetaEdge d L g m t σ₂ σ₀) a₂ b)))) t := by
  refine HasDerivAt.fun_sum fun b _ => ?_
  have e₀ := hasDerivAt_Theta_mul_apply d L g hS h₀₁ a₀ b
  have e₁ := hasDerivAt_Theta_mul_apply d L g hS h₁₂ a₁ b
  have e₂ := hasDerivAt_Theta_mul_apply d L g hS h₂₀ a₂ b
  exact ((e₀.mul e₁).mul e₂).congr_deriv (by simp only [thetaEdge, Pi.mul_apply]; ring)

/-- **`(eq_Ktree)` at `n = 3` solves `(pro_dyncalK)`.**  The three boundary edges of the
triangle match the three `(k,l)` terms one for one: differentiating the edge at `aᵢ`
inserts `S^(B)`, and that is exactly the term whose `2`-chain carries the charges of that
edge. -/
theorem hasDerivAt_kThree (hS : ‖SB d L g‖ = 1) (hW : (W : ℂ) ^ d ≠ 0) (m : Bool → ℂ)
    {t : ℝ} {σ₀ σ₁ σ₂ : Bool} (h₀₁ : ‖(t : ℂ) * (m σ₀ * m σ₁)‖ < 1)
    (h₁₂ : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h₂₀ : ‖(t : ℂ) * (m σ₂ * m σ₀)‖ < 1)
    (a₀ a₁ a₂ : Zd d L) :
    HasDerivAt (fun s => kThree d L W g m s σ₀ σ₁ σ₂ a₀ a₁ a₂)
      (((W : ℂ) ^ d) *
        ((∑ x : Zd d L, ∑ y : Zd d L, kThree d L W g m t σ₀ σ₁ σ₂ x a₁ a₂ * SB d L g x y
              * kTwo d L W g m t σ₀ σ₁ a₀ y)
          + (∑ x : Zd d L, ∑ y : Zd d L, kTwo d L W g m t σ₀ σ₂ x a₂ * SB d L g x y
              * kThree d L W g m t σ₀ σ₁ σ₂ a₀ a₁ y)
          + ∑ x : Zd d L, ∑ y : Zd d L, kThree d L W g m t σ₀ σ₁ σ₂ a₀ x a₂ * SB d L g x y
              * kTwo d L W g m t σ₁ σ₂ a₁ y)) t := by
  have hfun : (fun s => kThree d L W g m s σ₀ σ₁ σ₂ a₀ a₁ a₂)
      = fun s => ((((W : ℂ) ^ d)⁻¹) ^ 2 * (m σ₀ * (m σ₁ * m σ₂)))
        * ∑ b : Zd d L, thetaEdge d L g m s σ₀ σ₁ a₀ b * thetaEdge d L g m s σ₁ σ₂ a₁ b
            * thetaEdge d L g m s σ₂ σ₀ a₂ b := by
    funext s
    rw [kThree, treeSum_three]
  -- the `2`-loop of the term whose chain has the charges `(σ₀, σ₂)` is a `Θ^(σ₂,σ₀)` entry
  have hsym₂ : ∀ x : Zd d L, Theta d L g ((t : ℂ) * (m σ₀ * m σ₂)) x a₂
      = thetaEdge d L g m t σ₂ σ₀ a₂ x := by
    intro x
    have hc : (t : ℂ) * (m σ₀ * m σ₂) = (t : ℂ) * (m σ₂ * m σ₀) := by rw [mul_comm (m σ₀)]
    rw [hc, thetaEdge]
    exact congrFun (congrFun (Theta_transpose d L g hS h₂₀) a₂) x
  have hT1 : (∑ x : Zd d L, ∑ y : Zd d L, kThree d L W g m t σ₀ σ₁ σ₂ x a₁ a₂ * SB d L g x y
        * kTwo d L W g m t σ₀ σ₁ a₀ y)
      = ((((W : ℂ) ^ d)⁻¹) ^ 2 * (m σ₀ * (m σ₁ * m σ₂)) * (((W : ℂ) ^ d)⁻¹ * (m σ₀ * m σ₁)))
        * ∑ b : Zd d L,
          (thetaEdge d L g m t σ₀ σ₁ * SB d L g * thetaEdge d L g m t σ₀ σ₁) a₀ b
            * (thetaEdge d L g m t σ₁ σ₂ a₁ b * thetaEdge d L g m t σ₂ σ₀ a₂ b) := by
    rw [← sum_SB_starLeft (thetaEdge d L g m t σ₀ σ₁) a₀
      (fun b => thetaEdge d L g m t σ₁ σ₂ a₁ b * thetaEdge d L g m t σ₂ σ₀ a₂ b),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [kThree, kTwo, treeSum_three]
    rw [show ∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ x b
          * thetaEdge d L g m t σ₁ σ₂ a₁ b * thetaEdge d L g m t σ₂ σ₀ a₂ b
        = ∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ x b
          * (thetaEdge d L g m t σ₁ σ₂ a₁ b * thetaEdge d L g m t σ₂ σ₀ a₂ b) from
      Finset.sum_congr rfl fun b _ => by ring]
    simp only [thetaEdge]
    ring
  have hT3 : (∑ x : Zd d L, ∑ y : Zd d L, kThree d L W g m t σ₀ σ₁ σ₂ a₀ x a₂ * SB d L g x y
        * kTwo d L W g m t σ₁ σ₂ a₁ y)
      = ((((W : ℂ) ^ d)⁻¹) ^ 2 * (m σ₀ * (m σ₁ * m σ₂)) * (((W : ℂ) ^ d)⁻¹ * (m σ₁ * m σ₂)))
        * ∑ b : Zd d L,
          (thetaEdge d L g m t σ₁ σ₂ * SB d L g * thetaEdge d L g m t σ₁ σ₂) a₁ b
            * (thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₂ σ₀ a₂ b) := by
    rw [← sum_SB_starLeft (thetaEdge d L g m t σ₁ σ₂) a₁
      (fun b => thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₂ σ₀ a₂ b),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [kThree, kTwo, treeSum_three]
    rw [show ∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ a₀ b
          * thetaEdge d L g m t σ₁ σ₂ x b * thetaEdge d L g m t σ₂ σ₀ a₂ b
        = ∑ b : Zd d L, thetaEdge d L g m t σ₁ σ₂ x b
          * (thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₂ σ₀ a₂ b) from
      Finset.sum_congr rfl fun b _ => by ring]
    simp only [thetaEdge]
    ring
  have hT2 : (∑ x : Zd d L, ∑ y : Zd d L, kTwo d L W g m t σ₀ σ₂ x a₂ * SB d L g x y
        * kThree d L W g m t σ₀ σ₁ σ₂ a₀ a₁ y)
      = ((((W : ℂ) ^ d)⁻¹) ^ 2 * (m σ₀ * (m σ₁ * m σ₂)) * (((W : ℂ) ^ d)⁻¹ * (m σ₀ * m σ₂)))
        * ∑ b : Zd d L,
          (thetaEdge d L g m t σ₂ σ₀ * SB d L g * thetaEdge d L g m t σ₂ σ₀) a₂ b
            * (thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b) := by
    rw [← sum_SB_starRight (thetaEdge d L g m t σ₂ σ₀) a₂
      (fun b => thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [kThree, kTwo, treeSum_three, hsym₂ x]
    rw [show ∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b
          * thetaEdge d L g m t σ₂ σ₀ y b
        = ∑ b : Zd d L, thetaEdge d L g m t σ₂ σ₀ y b
          * (thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b) from
      Finset.sum_congr rfl fun b _ => by ring]
    simp only [thetaEdge]
    ring
  rw [hfun, hT1, hT2, hT3]
  refine ((hasDerivAt_starThree hS m h₀₁ h₁₂ h₂₀ a₀ a₁ a₂).const_mul _).congr_deriv ?_
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  field_simp
  ring

/-! ### Every family of `K`-loops has these `3`-loops -/

variable (d L W g)

/-- `(eq_Ktree)` at `n ≤ 3` as a function of the loop index: the two-loop solution at
length `2`, the tree value at length `3`, zero elsewhere. -/
noncomputable def kLoop3 (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ :=
  match I.σ, I.a with
  | [σ₀, σ₁], [a₀, a₁] => kTwo d L W g m t σ₀ σ₁ a₀ a₁
  | [σ₀, σ₁, σ₂], [a₀, a₁, a₂] => kThree d L W g m t σ₀ σ₁ σ₂ a₀ a₁ a₂
  | _, _ => 0

variable {d L W g}

omit [NeZero L] in
/-- A well-formed loop of length `3` is `⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩`. -/
theorem exists_eq_of_length_three {I : LoopIdx (Zd d L)} (hI : I.WF) (h3 : I.length = 3) :
    ∃ (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L), I = ⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩ := by
  obtain ⟨σ, a⟩ := I
  have ha : a.length = 3 := h3
  have hσ : σ.length = 3 := hI.trans ha
  obtain ⟨a₀, a₁, a₂, rfl⟩ := List.length_eq_three.mp ha
  obtain ⟨σ₀, σ₁, σ₂, rfl⟩ := List.length_eq_three.mp hσ
  exact ⟨σ₀, σ₁, σ₂, a₀, a₁, a₂, rfl⟩

/-- **`(eq_Ktree)` at `n = 3` holds of every family of `K`-loops** whose `2`-loops are
bounded on each `[0,T₀]`, `T₀ < 1`.

The proof is `eq_on_level` at `n = 3`: `K` and `kLoop3` solve the same equation at length
`3` -- linear in the `3`-loops, with the `2`-loops as coefficients -- they agree at length
`2` by `kTwoFormula_of_isKLoop`, and they agree at `t = 0` by `kThree_zero`. -/
theorem kThree_eq_of_isKLoop (hL : 3 ≤ L) (hW : (W : ℂ) ^ d ≠ 0) {m : Bool → ℂ}
    (hm : ∀ s, ‖m s‖ = 1) {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoop d L W g m (Set.Ico 0 1) K)
    (hbdd : ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc 0 T₀,
      ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L),
      K t ⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩ = kThree d L W g m t σ₀ σ₁ σ₂ a₀ a₁ a₂ := by
  intro t ht0 ht1 σ₀ σ₁ σ₂ a₀ a₁ a₂
  obtain ⟨R, hR0, hRK⟩ := hbdd t ht1
  have hS : ‖SB d L g‖ = 1 := norm_SB d L g hL
  set R' : ℝ := max R (‖((W : ℂ) ^ d)⁻¹‖ * (1 - t)⁻¹) with hR'
  have hR'0 : 0 ≤ R' := le_trans hR0 (le_max_left _ _)
  have hsub : ∀ s ∈ Set.Icc (0 : ℝ) t, s ∈ Set.Ico (0 : ℝ) 1 := fun s hs =>
    ⟨hs.1, lt_of_le_of_lt hs.2 ht1⟩
  have hnorm : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ τ₁ τ₂ : Bool,
      ‖(s : ℂ) * (m τ₁ * m τ₂)‖ < 1 := fun s hs τ₁ τ₂ =>
    norm_mul_lt_one (hm τ₁) (hm τ₂) hs.1 (lt_of_le_of_lt hs.2 ht1)
  -- the comparison family solves the equation at length `3`
  have hderiv' : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 3 →
      HasDerivAt (fun u => kLoop3 d L W g m u I)
        (treeEqRhs d L W g (kLoop3 d L W g m s) I) s := by
    intro s hs I hI h3
    obtain ⟨τ₀, τ₁, τ₂, b₀, b₁, b₂, rfl⟩ := exists_eq_of_length_three hI h3
    rw [treeEqRhs_three]
    exact hasDerivAt_kThree hS hW m (hnorm s hs τ₀ τ₁) (hnorm s hs τ₁ τ₂)
      (hnorm s hs τ₂ τ₀) b₀ b₁ b₂
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 →
      ‖K s I‖ ≤ R' ∧ ‖kLoop3 d L W g m s I‖ ≤ R' := by
    intro s hs I hI h2
    refine ⟨le_trans (hRK s hs I hI h2) (le_max_left _ _), ?_⟩
    obtain ⟨τ₀, τ₁, b₀, b₁, rfl⟩ := exists_eq_of_length_two hI h2
    have hs1 : s < 1 := lt_of_le_of_lt hs.2 ht1
    have hmono : (1 - s)⁻¹ ≤ (1 - t)⁻¹ :=
      inv_anti₀ (by linarith) (by linarith [hs.2])
    refine le_trans ?_ (le_max_right R _)
    refine le_trans (norm_kTwo_le hL (hm τ₀) (hm τ₁) hs.1 hs1 b₀ b₁) ?_
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
  have hlow : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      I.length < 3 → K s I = kLoop3 d L W g m s I := by
    intro s hs I hI h2 h3
    have hlen : I.length = 2 := by omega
    obtain ⟨τ₀, τ₁, b₀, b₁, rfl⟩ := exists_eq_of_length_two hI hlen
    rw [kTwoFormula_of_isKLoop hL hW hm hK hbdd s hs.1 (lt_of_le_of_lt hs.2 ht1) τ₀ τ₁ b₀ b₁]
    rfl
  have key := eq_on_level d L W g hL K (kLoop3 d L W g m) t R' 3 hR'0
    (fun s hs I hI h3 => hK.1 s (hsub s hs) I hI (by omega))
    hderiv' hbound hlow
    (fun I hI h3 => by
      obtain ⟨τ₀, τ₁, τ₂, b₀, b₁, b₂, rfl⟩ := exists_eq_of_length_three hI h3
      rw [hK.2.1 _ hI (by omega)]
      exact (kThree_zero m τ₀ τ₁ τ₂ b₀ b₁ b₂).symm)
  exact key t ⟨ht0, le_refl t⟩ ⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩ rfl rfl

end RBM.Loop
