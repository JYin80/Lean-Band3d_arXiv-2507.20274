/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.PureLoop
import RBM3D.Propagator.Deriv

/-!
# The two-loop solution `(Kn2sol)`

`K^(2)_{t,σ,a} = W^{-d} m(σ_1) m(σ_2) Θ_{t m(σ_1)m(σ_2)}(a_1, a_2)`.

The paper records this in an example and attributes it to `[YY_25]`, `[RBSO1D]`.  It does
not have to be borrowed: it is a one-line verification once the propagator can be
differentiated, and this file does it.

* `RBM.Loop.kTwo` is the right-hand side of `(Kn2sol)`;
* `RBM.Loop.hasDerivAt_kTwo` shows it **solves the convolution tree equation at `n = 2`**
  -- differentiate through `Θ` (`RBM.hasDerivAt_Theta_apply`, Q23) and compare with
  `RBM.Loop.treeEqRhs_two` (Q15);
* `RBM.Loop.kTwo_zero` shows it takes the `M`-loop value at `t = 0`;
* `RBM.Loop.kTwoFormula_kTwoLoop` records that `RBM.Loop.KTwoFormula` -- the hypothesis
  carried by `RBM.Loop.pureLoop_two` -- **is satisfiable**: the explicit solution satisfies
  it.  An unsatisfiable hypothesis would make every theorem carrying it vacuous, so this is
  worth having on the record even before the hypothesis can be discharged.

## What still stands between this and discharging `KTwoFormula`

`KTwoFormula m K` says that the `2`-loops of *an arbitrary* `K`-loop family `K` are given by
the formula.  This file proves that `kTwo` **is a** solution of the same equation with the
same initial value; to conclude that it is **the** solution, and so to rewrite an arbitrary
`K` into it, one needs uniqueness for the convolution tree equations -- a Grönwall argument
(`docs/QUEUE.md`, Q22a).  Until then the two halves are: this file (existence, and the
consistency of the hypothesis) and Q22a (uniqueness).
-/

namespace RBM.Loop

open Finset Matrix
open scoped Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ)

/-- `(Kn2sol)`: `K^(2)_{t,σ,(a₁,a₂)} = W^{-d} m₁ m₂ (Θ_{t m₁ m₂})_{a₁a₂}`, `mᵢ = m(σᵢ)`. -/
noncomputable def kTwo (m : Bool → ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) : ℂ :=
  ((W : ℂ) ^ d)⁻¹ * (m σ₁ * m σ₂) * Theta d L g ((t : ℂ) * (m σ₁ * m σ₂)) a₁ a₂

variable {d L W g}

theorem Theta_zero : Theta d L g 0 = 1 := by
  simp [Theta]

/-- The spectral parameter of `(Kn2sol)` stays in the unit ball: the paper's `m(σ)` has
`|m(σ)| = 1` (it is a point of the unit circle in the upper half plane), so
`‖t m(σ₁)m(σ₂)‖ = t < 1`. -/
theorem norm_mul_lt_one {m : Bool → ℂ} {σ₁ σ₂ : Bool} (h₁ : ‖m σ₁‖ = 1) (h₂ : ‖m σ₂‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1 := by
  rw [norm_mul, norm_mul, h₁, h₂, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht0]
  exact ht1

/-- **`(Kn2sol)` solves the convolution tree equation at `n = 2`**, wherever
`‖t m₁ m₂‖ < 1`. -/
theorem hasDerivAt_kTwo (hS : ‖SB d L g‖ = 1) (hW : (W : ℂ) ^ d ≠ 0) (m : Bool → ℂ) {t : ℝ}
    (σ₁ σ₂ : Bool) (ht : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (a₁ a₂ : Zd d L) :
    HasDerivAt (fun s => kTwo d L W g m s σ₁ σ₂ a₁ a₂)
      (((W : ℂ) ^ d) * ∑ a : Zd d L, ∑ b : Zd d L,
        kTwo d L W g m t σ₁ σ₂ a₁ a * SB d L g a b * kTwo d L W g m t σ₁ σ₂ b a₂) t := by
  set μ := m σ₁ * m σ₂ with hμ
  have h1 := hasDerivAt_Theta_mul_apply d L g hS ht a₁ a₂
  have h3 := HasDerivAt.const_mul (((W : ℂ) ^ d)⁻¹ * μ) h1
  refine h3.congr_deriv ?_
  simp only [kTwo, ← hμ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  field_simp

/-- At `t = 0`, `(Kn2sol)` is the `M`-loop value `(eq:initial_K)` for `n = 2`. -/
theorem kTwo_zero (m : Bool → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    kTwo d L W g m 0 σ₁ σ₂ a₁ a₂ = MLoop d L W m ⟨[σ₁, σ₂], [a₁, a₂]⟩ := by
  have hall : (∀ x ∈ [a₁, a₂], ∀ y ∈ [a₁, a₂], x = y) ↔ a₁ = a₂ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨-, h⟩, -⟩
      exact h
    · rintro rfl
      simp
  simp only [kTwo, MLoop, Complex.ofReal_zero, zero_mul, Theta_zero, Matrix.one_apply,
    LoopIdx.length, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, hall]
  split_ifs <;> ring

variable (d L W g)

/-- `(Kn2sol)` as a function of the loop index, zero off loops of length `2`. -/
noncomputable def kTwoLoop (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [a₁, a₂] => kTwo d L W g m t σ₁ σ₂ a₁ a₂
  | _, _ => 0

variable {d L W g}

/-- **`(Kn2sol)` satisfies `(pro_dyncalK)` at `n = 2`** in its general form, with the
right-hand side built from the cut-and-glue operators. -/
theorem hasDerivAt_kTwoLoop (hS : ‖SB d L g‖ = 1) (hW : (W : ℂ) ^ d ≠ 0) (m : Bool → ℂ)
    {t : ℝ} (σ₁ σ₂ : Bool) (ht : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (a₁ a₂ : Zd d L) :
    HasDerivAt (fun s => kTwoLoop d L W g m s ⟨[σ₁, σ₂], [a₁, a₂]⟩)
      (treeEqRhs d L W g (kTwoLoop d L W g m t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t := by
  rw [treeEqRhs_two]
  exact hasDerivAt_kTwo hS hW m σ₁ σ₂ ht a₁ a₂

/-- At `t = 0`, `(Kn2sol)` takes the `M`-loop values on every loop of length `2`. -/
theorem kTwoLoop_zero (m : Bool → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    kTwoLoop d L W g m 0 ⟨[σ₁, σ₂], [a₁, a₂]⟩ = MLoop d L W m ⟨[σ₁, σ₂], [a₁, a₂]⟩ :=
  kTwo_zero m σ₁ σ₂ a₁ a₂

/-- **`RBM.Loop.KTwoFormula` is satisfiable.**  The hypothesis carried by `pureLoop_two`
holds of the explicit solution, so the theorems that assume it are not vacuous. -/
theorem kTwoFormula_kTwoLoop (m : Bool → ℂ) :
    KTwoFormula d L W g m (kTwoLoop d L W g m) := by
  intro t _ _ σ₁ σ₂ a₁ a₂
  rfl

/-- An entrywise bound on `(Kn2sol)`: `‖K^(2)‖ ≤ W^{-d}(1-t)^{-1}`, from
`RBM.norm_Theta_apply_le` and the row sum `RBM.sum_Theta_real_row`.  This is what supplies
the `2`-loop bound that the uniqueness argument of `Loop/Unique.lean` asks for. -/
theorem norm_kTwo_le (hL : 3 ≤ L) {m : Bool → ℂ} {σ₁ σ₂ : Bool} (h₁ : ‖m σ₁‖ = 1)
    (h₂ : ‖m σ₂‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a₁ a₂ : Zd d L) :
    ‖kTwo d L W g m t σ₁ σ₂ a₁ a₂‖ ≤ ‖((W : ℂ) ^ d)⁻¹‖ * (1 - t)⁻¹ := by
  have hmm : ‖m σ₁ * m σ₂‖ = 1 := by rw [norm_mul, h₁, h₂, mul_one]
  have hentry : ‖Theta d L g ((t : ℂ) * (m σ₁ * m σ₂)) a₁ a₂‖ ≤ (1 - t)⁻¹ := by
    refine (norm_Theta_apply_le hL ht0 ht1 hmm a₁ a₂).trans ?_
    have hsingle := Finset.single_le_sum
      (f := fun b => (Theta d L g (t : ℂ) a₁ b).re)
      (fun b _ => Theta_real_nonneg (g := g) hL ht0 ht1 a₁ b) (Finset.mem_univ a₂)
    rwa [sum_Theta_real_row (g := g) hL ht0 ht1 a₁] at hsingle
  calc ‖kTwo d L W g m t σ₁ σ₂ a₁ a₂‖
      = ‖((W : ℂ) ^ d)⁻¹‖ * ‖m σ₁ * m σ₂‖
        * ‖Theta d L g ((t : ℂ) * (m σ₁ * m σ₂)) a₁ a₂‖ := by
        rw [kTwo, norm_mul, norm_mul]
    _ = ‖((W : ℂ) ^ d)⁻¹‖ * ‖Theta d L g ((t : ℂ) * (m σ₁ * m σ₂)) a₁ a₂‖ := by
        rw [hmm, mul_one]
    _ ≤ ‖((W : ℂ) ^ d)⁻¹‖ * (1 - t)⁻¹ :=
        mul_le_mul_of_nonneg_left hentry (norm_nonneg _)

/-- **`res_pureKes` at `n = 2`, with `(Kn2sol)` no longer assumed.**  Applying
`pureLoop_two` to the explicit solution discharges its `KTwoFormula` hypothesis; what is
left standing is `ThetaDecayShort`, which the paper really does borrow. -/
theorem pureLoop_two_kTwoLoop {k : ℕ} {m : Bool → ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g)
    (hL : 3 ≤ L) {σ : Bool} (hm : ‖m σ‖ = 1) (hmi : 0 < (m σ).im)
    (hshort : ThetaDecayShort (k + 2) g (m σ)) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ a₁ a₂ : Zd (k + 2) L,
      ‖kTwoLoop (k + 2) L W g m t ⟨[σ, σ], [a₁, a₂]⟩‖
        ≤ C * ‖((W : ℂ) ^ (k + 2))⁻¹‖
          * Real.exp (-(c * (zdistD (k + 2) L (a₁ - a₂) : ℝ))) :=
  pureLoop_two hd hg hL hm hmi hshort (kTwoFormula_kTwoLoop m)

end RBM.Loop
