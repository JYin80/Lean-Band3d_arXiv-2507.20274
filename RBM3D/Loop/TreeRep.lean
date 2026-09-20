/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.List.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import RBM3D.Loop.Partition

/-!
# `K`-loops and the tree representation `eq_Ktree`

`\Cref{Def_Ktza}` defines the `K`-loops: `K^(1)_{t,σ,a} = m(σ)`, and for `n ≥ 2`
`K^(n)` is the unique solution of the **convolution tree equations** `(pro_dyncalK)`

  `∂_t K^(n)_{t,σ,a} = W^d Σ_{1≤k<l≤n} Σ_{a,b} (cutL^{(a)}_{k,l} ∘ K) S^(B)_{ab}
                                                  (cutR^{(b)}_{k,l} ∘ K)`

with the initial condition `K^(k)_{0,σ,a} = M^(k)_{σ,a}` of `(eq:initial_K)`, where for the
random band matrix model `M^(k)_{σ,a} = W^{-(k-1)d} ∏_i m(σ_i) 1(a_1 = … = a_k)`.
`\Cref{tree-representation}` (`[YY_25]` Lemma 3.4) then states, for `n ≥ 4`,

  `(eq_Ktree)`   `K^(n)_{t,σ,a} = W^{-d(n-1)} Σ_{Γ ∈ TSP(P_a)} Γ^(n)_{t,σ,a}`.

## What is here, and what is assumed

The cut-and-glue operators and the equations are *defined* here, so that the statement of
`(eq_Ktree)` is a statement about a concrete object: `RBM.Loop.IsKLoop` says that a family
`K` satisfies `\Cref{Def_Ktza}` verbatim.  The index layer is the one of the sister
project (`RBM1D/Loop/Index.lean`), which is already generic in the label type; only
`W ↦ W^d` changes, the `d`-dimensional weight of a block.

`(eq_Ktree)` itself is **assumed**, as `RBM.Loop.KTreeRep`, in the form the repository
uses for everything the paper cites rather than proves (`CLAUDE.md`, and `PropTH` in
`Propagator/Interface.lean`): a `Prop`, not an axiom, so that a result resting on it says
so in its own statement and the audit stays empty.

**Why assumed rather than ported.**  `RBM1D` proves it, and not by a combinatorial
bijection: it shows that the tree sum satisfies the same equations with the same initial
value, and concludes by uniqueness of solutions.  Carrying that over needs
`RBM1D/Loop/TreeRep.lean` (729 lines, `n ≤ 4`) and `TreeRepGeneral.lean` (2546 lines),
*and* a derivative layer for `Θ_t` in `t` that this project does not have yet
(`RBM1D/Propagator/Deriv.lean`).  That is a project of its own; see `docs/QUEUE.md`, Q22.
The shape here is chosen so the port can replace the hypothesis without changing a single
downstream statement.

## Main definitions

* `RBM.Loop.LoopIdx`, `cutGlueL`, `cutGlueR` : the index data and the cut-and-glue
  operators of `(calGonIND)`
* `RBM.Loop.treeEqRhs` : the right-hand side of `(pro_dyncalK)`
* `RBM.Loop.MLoop` : `(eq:initial_K)` for the random band matrix model
* `RBM.Loop.IsKLoop` : `\Cref{Def_Ktza}` as a predicate
* `RBM.Loop.KTreeRep` : `(eq_Ktree)` as a hypothesis
-/

namespace RBM.Loop

open Finset

/-! ### Index data and the cut-and-glue operators -/

/-- Index data `(σ, a)` of a loop: charges (`true` for `+`) and block labels. -/
@[ext]
structure LoopIdx (α : Type*) where
  /-- the charges `σ_1, …, σ_n` -/
  σ : List Bool
  /-- the block labels `a_1, …, a_n` -/
  a : List α
  deriving DecidableEq

namespace LoopIdx

variable {α : Type*}

/-- Well-formedness: as many charges as labels. -/
def WF (x : LoopIdx α) : Prop := x.σ.length = x.a.length

/-- The length `n` of the loop. -/
def length (x : LoopIdx α) : ℕ := x.a.length

/-- `cutL^{(b)}_{k,l}` of `(calGonIND)`, `1 ≤ k < l ≤ n`: cut the `k`-th and `l`-th edges
and close up the chain through `a_n`, inserting the label `b`. -/
def cutGlueL (k l : ℕ) (b : α) (x : LoopIdx α) : LoopIdx α where
  σ := x.σ.take k ++ x.σ.drop (l - 1)
  a := x.a.take (k - 1) ++ b :: x.a.drop (l - 1)

/-- `cutR^{(b)}_{k,l}` of `(calGonIND)`: close up the other chain, inserting `b`. -/
def cutGlueR (k l : ℕ) (b : α) (x : LoopIdx α) : LoopIdx α where
  σ := (x.σ.drop (k - 1)).take (l - k + 1)
  a := (x.a.drop (k - 1)).take (l - k) ++ [b]

variable (x : LoopIdx α) (b : α) {k l : ℕ}

theorem length_cutGlueL (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).length = k + x.length - l + 1 := by
  simp only [length, cutGlueL, List.length_append, List.length_take, List.length_cons,
    List.length_drop] at hl ⊢
  omega

theorem length_cutGlueR (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueR k l b).length = l - k + 1 := by
  simp only [length, cutGlueR, List.length_append, List.length_take, List.length_drop,
    List.length_singleton] at hl ⊢
  omega

/-- The two loops produced by cutting at `k < l` have total length `n + 2`: this is why
`(pro_dyncalK)` is quadratic. -/
theorem length_cutGlueL_add_length_cutGlueR (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).length + (x.cutGlueR k l b).length = x.length + 2 := by
  rw [length_cutGlueL x b hk hkl hl, length_cutGlueR x b hk hkl hl]
  omega

theorem length_cutGlueL_le (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).length ≤ x.length := by
  rw [length_cutGlueL x b hk hkl hl]; omega

theorem length_cutGlueR_le (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueR k l b).length ≤ x.length := by
  rw [length_cutGlueR x b hk hkl hl]; omega

theorem wf_cutGlueL (hx : x.WF) (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).WF := by
  simp only [WF, length, cutGlueL, List.length_append, List.length_take, List.length_cons,
    List.length_drop] at hx hl ⊢
  omega

theorem wf_cutGlueR (hx : x.WF) (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueR k l b).WF := by
  simp only [WF, length, cutGlueR, List.length_append, List.length_take, List.length_drop,
    List.length_singleton] at hx hl ⊢
  omega

end LoopIdx

/-! ### The convolution tree equations -/

variable (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ)

/-- The right-hand side of `(pro_dyncalK)`:
`W^d Σ_{1≤k<l≤n} Σ_{a,b} K(cutL^{(a)}_{k,l}) S^(B)_{ab} K(cutR^{(b)}_{k,l})`. -/
noncomputable def treeEqRhs (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  ((W : ℂ) ^ d) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length,
    ∑ a : Zd d L, ∑ b : Zd d L,
      K (I.cutGlueL k l a) * SB d L g a b * K (I.cutGlueR k l b)

/-- `(eq:initial_K)` for the random band matrix model:
`M^(k)_{σ,a} = W^{-(k-1)d} ∏_i m(σ_i) 1(a_1 = … = a_k)`.  The paper states the `M`-loop as
a trace at the level of the full `N × N` matrices and then records this simplification;
only the random band matrix model is formalized here (`docs/paper-deltas.md`, D6). -/
noncomputable def MLoop (m : Bool → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) ^ (I.length - 1) * (I.σ.map m).prod
    * (if ∀ x ∈ I.a, ∀ y ∈ I.a, x = y then 1 else 0)

/-- **`\Cref{Def_Ktza}`**: `K` is a family of `K`-loops on the time set `T` -- it solves
the convolution tree equations, takes the `M`-loop values at `t = 0`, and equals `m(σ)` on
loops of length `1` (for which the sum in `(pro_dyncalK)` is empty). -/
def IsKLoop (m : Bool → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ t ∈ T, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      HasDerivAt (fun s => K s I) (treeEqRhs d L W g (K t) I) t) ∧
  (∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K 0 I = MLoop d L W m I) ∧
  (∀ t ∈ T, ∀ (s : Bool) (a : Zd d L), K t ⟨[s], [a]⟩ = m s)

/-- **The a priori bound on `2`-loops.**  `K`'s two-loops stay bounded on every
`[0, T₀]` with `T₀ < 1`, with a bound that may depend on `T₀`.

This is a mathematical premise the project does not prove -- the paper obtains it along
the way, from `(prop:ThfadC)` -- so by the house rule it is a named `Prop` rather than an
anonymous clause in a signature: that is what lets the audit count the theorems resting on
it.  It is the *only* thing still assumed by `(Kn2sol)` (`kTwoFormula_of_isKLoop`) and by
`(eq_Ktree)` at `n = 3` (`kThree_eq_of_isKLoop`). -/
def TwoLoopBounded (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
    ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R

/-- **`(eq_Ktree)`**, `\Cref{tree-representation}` (`[YY_25]` Lemma 3.4): for `n ≥ 4`,
`K^(n)_{t,σ,a} = W^{-d(n-1)} Σ_{Γ ∈ TSP(P_a)} Γ^(n)_{t,σ,a}`.

Assumed, not asserted: a result that uses it takes it as a hypothesis.  `RBM1D` proves the
corresponding statement by showing that the tree sum solves the same equations with the
same initial value; porting that is `docs/QUEUE.md`, Q22. -/
def KTreeRep (m : Bool → ℂ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ (t : ℝ), 0 ≤ t → t < 1 →
    ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
      K t ⟨List.ofFn σ, List.ofFn a⟩
        = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * GammaSum d L g m t σ a

variable {d L W g}

/-- **Index check at `n = 2`.**  The general right-hand side, built from `cutGlueL` and
`cutGlueR`, is the two-loop equation `W^d Σ_{a,b} K_{σ,(a₁,a)} S^(B)_{ab} K_{σ,(b,a₂)}`.
The operators produce the two dummy indices in the opposite order; the two agree because
`S^(B)` is symmetric. -/
theorem treeEqRhs_two (K : LoopIdx (Zd d L) → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    treeEqRhs d L W g K ⟨[σ₁, σ₂], [a₁, a₂]⟩
      = ((W : ℂ) ^ d) * ∑ a : Zd d L, ∑ b : Zd d L,
          K ⟨[σ₁, σ₂], [a₁, a]⟩ * SB d L g a b * K ⟨[σ₁, σ₂], [b, a₂]⟩ := by
  have hlen : (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).length = 2 := rfl
  have hsym : ∀ x y : Zd d L, SB d L g y x = SB d L g x y := by
    intro x y
    exact congrFun (congrFun (SB_isSymm d L g) x) y
  have h12 : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hIoc1 : Ioc 1 2 = ({2} : Finset ℕ) := by decide
  have hIoc2 : Ioc 2 2 = (∅ : Finset ℕ) := by decide
  rw [treeEqRhs, hlen, h12, Finset.sum_insert (by decide), Finset.sum_singleton, hIoc1,
    hIoc2, Finset.sum_singleton, Finset.sum_empty, add_zero]
  -- the cut at `(k, l) = (1, 2)` gives the chains `(a, a₂)` and `(a₁, b)`
  have hL : ∀ a : Zd d L,
      (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).cutGlueL 1 2 a = ⟨[σ₁, σ₂], [a, a₂]⟩ := by
    intro a; simp [LoopIdx.cutGlueL]
  have hR : ∀ b : Zd d L,
      (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).cutGlueR 1 2 b = ⟨[σ₁, σ₂], [a₁, b]⟩ := by
    intro b; simp [LoopIdx.cutGlueR]
  simp only [hL, hR]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hsym b a]
  ring

end RBM.Loop
