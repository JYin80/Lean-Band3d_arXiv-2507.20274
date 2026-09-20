/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.TreeThree

/-!
# The tree representation at `n = 4`

`n = 4` is the first length at which a canonical partition can have an **internal edge**:
`TSP 4 = {∅, {(0,2)}, {(1,3)}}` (`RBM.Loop.TSP_four`, Q14).  It is therefore the first
place where the correspondence "edges of trees ↔ `(k,l)` terms of `(pro_dyncalK)`" is
visible in full: `4` boundary edges and `2` diagonals against the `6` pairs `k < l`.

`treeEqRhs_four` below is that count, with the chains computed: the four terms
`(1,2), (2,3), (3,4), (1,4)` each cut off a `2`-chain and replace one label -- these are
the boundary edges -- while `(1,3)` and `(2,4)` cut the square into **two `3`-chains**,
which is what an internal edge looks like from the equation's side.

## Main results

* `RBM.Loop.treeEqRhs_four` : the six terms of `(pro_dyncalK)` at `n = 4`
* `RBM.Loop.treeVal_four_diag02`, `RBM.Loop.treeVal_four_diag13` : the values of the two
  partitions with a diagonal -- two stars joined by the internal edge `Θ^(σ_i,σ_j) - I`
* `RBM.Loop.treeSum_four` : the tree sum is the star plus those two

What is not here yet is the derivative matching (`docs/QUEUE.md`, Q30 steps ③ and ④).
-/

namespace RBM.Loop

open Finset
open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ}

/-- **Index check at `n = 4`.**  The six terms of `(pro_dyncalK)`.  Four of them cut off a
`2`-chain -- the boundary edges at `a₀, a₁, a₂, a₃` -- and two cut the square into two
`3`-chains, which are the two diagonals. -/
theorem treeEqRhs_four (K : LoopIdx (Zd d L) → ℂ) (σ₀ σ₁ σ₂ σ₃ : Bool)
    (a₀ a₁ a₂ a₃ : Zd d L) :
    treeEqRhs d L W g K ⟨[σ₀, σ₁, σ₂, σ₃], [a₀, a₁, a₂, a₃]⟩
      = ((W : ℂ) ^ d) *
          (((∑ x : Zd d L, ∑ y : Zd d L,
                K ⟨[σ₀, σ₁, σ₂, σ₃], [x, a₁, a₂, a₃]⟩ * SB d L g x y
                  * K ⟨[σ₀, σ₁], [a₀, y]⟩)
            + (∑ x : Zd d L, ∑ y : Zd d L,
                K ⟨[σ₀, σ₂, σ₃], [x, a₂, a₃]⟩ * SB d L g x y
                  * K ⟨[σ₀, σ₁, σ₂], [a₀, a₁, y]⟩)
            + ∑ x : Zd d L, ∑ y : Zd d L,
                K ⟨[σ₀, σ₃], [x, a₃]⟩ * SB d L g x y
                  * K ⟨[σ₀, σ₁, σ₂, σ₃], [a₀, a₁, a₂, y]⟩)
          + ((∑ x : Zd d L, ∑ y : Zd d L,
                K ⟨[σ₀, σ₁, σ₂, σ₃], [a₀, x, a₂, a₃]⟩ * SB d L g x y
                  * K ⟨[σ₁, σ₂], [a₁, y]⟩)
            + ∑ x : Zd d L, ∑ y : Zd d L,
                K ⟨[σ₀, σ₁, σ₃], [a₀, x, a₃]⟩ * SB d L g x y
                  * K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, y]⟩)
          + ∑ x : Zd d L, ∑ y : Zd d L,
              K ⟨[σ₀, σ₁, σ₂, σ₃], [a₀, a₁, x, a₃]⟩ * SB d L g x y
                * K ⟨[σ₂, σ₃], [a₂, y]⟩) := by
  have hlen : (⟨[σ₀, σ₁, σ₂, σ₃], [a₀, a₁, a₂, a₃]⟩ : LoopIdx (Zd d L)).length = 4 := rfl
  have h14 : Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  have hIoc1 : Ioc 1 4 = ({2, 3, 4} : Finset ℕ) := by decide
  have hIoc2 : Ioc 2 4 = ({3, 4} : Finset ℕ) := by decide
  have hIoc3 : Ioc 3 4 = ({4} : Finset ℕ) := by decide
  have hIoc4 : Ioc 4 4 = (∅ : Finset ℕ) := by decide
  rw [treeEqRhs, hlen, h14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    hIoc1, hIoc2, hIoc3, hIoc4,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_empty, add_zero]
  congr 1
  norm_num [LoopIdx.cutGlueL, LoopIdx.cutGlueR]
  ring

/-! ### The two partitions with a diagonal

`polyVal` splits the square along the diagonal into two triangles, joined by a new vertex
`y` that carries `(Θ^(σ_i,σ_j) - I)ᵀ` on the left piece and `I` on the right: that product
is the internal edge `(f-internal)`.  Evaluating the recursion at `F = [(0,2)]` and
`F = [(1,3)]` gives two stars of three edges glued by `Θ - I`. -/

theorem treeVal_four_diag02 (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ σ₃ : Bool)
    (a₀ a₁ a₂ a₃ : Zd d L) :
    treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] [(0, 2)]
      = ∑ y : Zd d L,
          (∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b
            * (thetaEdge d L g m t σ₀ σ₂ - 1) b y)
          * (thetaEdge d L g m t σ₂ σ₃ a₂ y * thetaEdge d L g m t σ₃ σ₀ a₃ y) := by
  have hbd : bdList d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃]
      = [(a₀, thetaEdge d L g m t σ₀ σ₁), (a₁, thetaEdge d L g m t σ₁ σ₂),
        (a₂, thetaEdge d L g m t σ₂ σ₃), (a₃, thetaEdge d L g m t σ₃ σ₀)] := by
    simp only [bdList, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil]
    rfl
  rw [treeVal, ite_eq_right (by simp), hbd, polyVal]
  norm_num [leftPairs, rightPairs, polyVal, Matrix.one_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun b _ => by
    rcases eq_or_ne y b with rfl | h
    · simp; ring
    · simp [h, Ne.symm h]; ring

theorem treeVal_four_diag13 (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ σ₃ : Bool)
    (a₀ a₁ a₂ a₃ : Zd d L) :
    treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] [(1, 3)]
      = ∑ y : Zd d L,
          (∑ b : Zd d L, thetaEdge d L g m t σ₁ σ₂ a₁ b * thetaEdge d L g m t σ₂ σ₃ a₂ b
            * (thetaEdge d L g m t σ₁ σ₃ - 1) b y)
          * (thetaEdge d L g m t σ₃ σ₀ a₃ y * thetaEdge d L g m t σ₀ σ₁ a₀ y) := by
  have hbd : bdList d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃]
      = [(a₀, thetaEdge d L g m t σ₀ σ₁), (a₁, thetaEdge d L g m t σ₁ σ₂),
        (a₂, thetaEdge d L g m t σ₂ σ₃), (a₃, thetaEdge d L g m t σ₃ σ₀)] := by
    simp only [bdList, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil]
    rfl
  rw [treeVal, ite_eq_right (by simp), hbd, polyVal]
  norm_num [leftPairs, rightPairs, polyVal, Matrix.one_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun b _ => by
    rcases eq_or_ne y b with rfl | h
    · simp; ring
    · simp [h, Ne.symm h]; ring

/-- **`Σ_{Γ ∈ TSP(P_a)}` at `n = 4`**: the star plus the two partitions with a diagonal.
`TSP 4` has exactly these three elements because the two diagonals of a square cross, so
they cannot appear together (`RBM.Loop.TSP_four`). -/
theorem treeSum_four (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ σ₃ : Bool) (a₀ a₁ a₂ a₃ : Zd d L) :
    treeSum d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃]
      = treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] []
        + treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] [(0, 2)]
        + treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] [(1, 3)] := by
  have hlen : ([σ₀, σ₁, σ₂, σ₃] : List Bool).length = 4 := rfl
  have h0 : diagList (∅ : Finset (Fin 4 × Fin 4)) = [] := by simp [diagList]
  have h02 : diagList ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) = [(0, 2)] := by
    simp [diagList]
  have h13 : diagList ({((1 : Fin 4), (3 : Fin 4))} : Finset (Fin 4 × Fin 4)) = [(1, 3)] := by
    simp [diagList]
  rw [treeSum, hlen, TSP_four]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    h0, h02, h13]
  ring

/-! ### Differentiating the trees

Two observations before the work.

**The internal edge differentiates like a boundary edge.**  It carries `Θ^(σ_i,σ_j) - I`,
and `I` does not depend on `t`, so `∂_t(Θ - I) = ∂_t Θ = μ Θ S^(B) Θ` -- the same formula
(`RBM.hasDerivAt_Theta_mul_apply`, Q23).  That is `hasDerivAt_thetaEdge_sub_one` below.

**The summation lemmas of `n = 3` already cover `n = 4`.**  `docs/QUEUE.md`, Q35 asked for
"four-vertex versions" of `sum_SB_starLeft` / `sum_SB_starRight`; that was a mistake in the
ticket.  Those lemmas are stated for an *arbitrary* function `F` of the summation variable,
and the only difference at `n = 4` is that `F` is a product of three edges instead of two.
Nothing new is needed.
-/

/-- The internal edge `Θ^(σ,σ') - I` differentiates like a boundary edge: `I` carries no
`t`.  This is the only fact about internal edges the matching needs. -/
theorem hasDerivAt_thetaEdge_sub_one (hS : ‖SB d L g‖ = 1) (m : Bool → ℂ) {t : ℝ}
    (σ σ' : Bool) (ht : ‖(t : ℂ) * (m σ * m σ')‖ < 1) (b y : Zd d L) :
    HasDerivAt (fun s => (thetaEdge d L g m s σ σ' - 1) b y)
      ((m σ * m σ')
        * (thetaEdge d L g m t σ σ' * SB d L g * thetaEdge d L g m t σ σ') b y) t := by
  have h := hasDerivAt_Theta_mul_apply d L g hS ht b y
  have hfun : (fun s : ℝ => (thetaEdge d L g m s σ σ' - 1) b y)
      = fun s : ℝ => Theta d L g ((s : ℂ) * (m σ * m σ')) b y
        - (1 : Matrix (Zd d L) (Zd d L) ℂ) b y := by
    funext s
    simp [thetaEdge, Matrix.sub_apply]
  rw [hfun]
  simpa [thetaEdge] using h.sub_const ((1 : Matrix (Zd d L) (Zd d L) ℂ) b y)

/-- The derivative of the star at `n = 4`: one term per boundary edge, exactly as at
`n = 3`. -/
theorem hasDerivAt_starFour (hS : ‖SB d L g‖ = 1) (m : Bool → ℂ) {t : ℝ}
    {σ₀ σ₁ σ₂ σ₃ : Bool} (h₀₁ : ‖(t : ℂ) * (m σ₀ * m σ₁)‖ < 1)
    (h₁₂ : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h₂₃ : ‖(t : ℂ) * (m σ₂ * m σ₃)‖ < 1)
    (h₃₀ : ‖(t : ℂ) * (m σ₃ * m σ₀)‖ < 1) (a₀ a₁ a₂ a₃ : Zd d L) :
    HasDerivAt
      (fun s => ∑ b : Zd d L, thetaEdge d L g m s σ₀ σ₁ a₀ b
        * thetaEdge d L g m s σ₁ σ₂ a₁ b * thetaEdge d L g m s σ₂ σ₃ a₂ b
        * thetaEdge d L g m s σ₃ σ₀ a₃ b)
      (∑ b : Zd d L,
        ((m σ₀ * m σ₁) * ((thetaEdge d L g m t σ₀ σ₁ * SB d L g * thetaEdge d L g m t σ₀ σ₁)
            a₀ b) * thetaEdge d L g m t σ₁ σ₂ a₁ b * thetaEdge d L g m t σ₂ σ₃ a₂ b
            * thetaEdge d L g m t σ₃ σ₀ a₃ b
        + thetaEdge d L g m t σ₀ σ₁ a₀ b
            * ((m σ₁ * m σ₂) * ((thetaEdge d L g m t σ₁ σ₂ * SB d L g
              * thetaEdge d L g m t σ₁ σ₂) a₁ b)) * thetaEdge d L g m t σ₂ σ₃ a₂ b
            * thetaEdge d L g m t σ₃ σ₀ a₃ b
        + thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b
            * ((m σ₂ * m σ₃) * ((thetaEdge d L g m t σ₂ σ₃ * SB d L g
              * thetaEdge d L g m t σ₂ σ₃) a₂ b)) * thetaEdge d L g m t σ₃ σ₀ a₃ b
        + thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b
            * thetaEdge d L g m t σ₂ σ₃ a₂ b
            * ((m σ₃ * m σ₀) * ((thetaEdge d L g m t σ₃ σ₀ * SB d L g
              * thetaEdge d L g m t σ₃ σ₀) a₃ b)))) t := by
  refine HasDerivAt.fun_sum fun b _ => ?_
  have e₀ := hasDerivAt_Theta_mul_apply d L g hS h₀₁ a₀ b
  have e₁ := hasDerivAt_Theta_mul_apply d L g hS h₁₂ a₁ b
  have e₂ := hasDerivAt_Theta_mul_apply d L g hS h₂₃ a₂ b
  have e₃ := hasDerivAt_Theta_mul_apply d L g hS h₃₀ a₃ b
  exact (((e₀.mul e₁).mul e₂).mul e₃).congr_deriv
    (by simp only [thetaEdge, Pi.mul_apply]; ring)

/-! ### Why one summation lemma covers all three trees

The `(k,l) = (1,2)` term of `(pro_dyncalK)` replaces the label `a₀` by a summation
variable.  Seen as a function of that label, **every** canonical partition -- the star and
both diagonals -- has the same shape,

`Γ(x, a₁, a₂, a₃) = Σ_b Θ^(σ₀σ₁)(x, b) · F(b)`,

with `F` collecting whatever the rest of the tree contributes.  For the star that is
immediate; for a diagonal it needs one exchange of summations, which is the content of the
two lemmas below.  Consequently `RBM.Loop.sum_SB_starLeft` applies to each tree unchanged,
and the four boundary edges of `n = 4` are handled exactly as the three of `n = 3`. -/

theorem treeVal_four_diag02_as_star (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ σ₃ : Bool)
    (x a₁ a₂ a₃ : Zd d L) :
    treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [x, a₁, a₂, a₃] [(0, 2)]
      = ∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ x b
          * ∑ y : Zd d L, thetaEdge d L g m t σ₁ σ₂ a₁ b
              * (thetaEdge d L g m t σ₀ σ₂ - 1) b y
              * (thetaEdge d L g m t σ₂ σ₃ a₂ y * thetaEdge d L g m t σ₃ σ₀ a₃ y) := by
  rw [treeVal_four_diag02]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem treeVal_four_diag13_as_star (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ σ₃ : Bool)
    (x a₁ a₂ a₃ : Zd d L) :
    treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [x, a₁, a₂, a₃] [(1, 3)]
      = ∑ y : Zd d L, thetaEdge d L g m t σ₀ σ₁ x y
          * ((∑ b : Zd d L, thetaEdge d L g m t σ₁ σ₂ a₁ b
                * thetaEdge d L g m t σ₂ σ₃ a₂ b * (thetaEdge d L g m t σ₁ σ₃ - 1) b y)
            * thetaEdge d L g m t σ₃ σ₀ a₃ y) := by
  rw [treeVal_four_diag13]
  exact Finset.sum_congr rfl fun y _ => by ring

end RBM.Loop

