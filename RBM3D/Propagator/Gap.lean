/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4

/-!
# Connectivity of the torus and symmetry of `S^(B)`

`S^(B)` is the transition matrix of a **lazy, irreducible** random walk on `Z_L^d`: the kernel has
the `x = 0` term (laziness) and all `2d` neighbours at `|x| = 1`.  This file contains facts about it
that do not involve the propagator.

## What is here

* `exists_zdist_step`, `exists_step` : from any `x ≠ 0` one unit step decreases
  `|x|` by exactly one.  This is the connectivity of the torus in the form an induction on the
  distance wants.
* `sum_SBR_row` : the rows of the real kernel `SBR` sum to `1`.
* `SBR_comm` : `S^(B)` is symmetric, hence so is every power.
* `norm_tsum_le_of_le` : a complex series bounded termwise by a summable real majorant has norm at
  most the sum of the majorant.
-/

namespace RBM

open Matrix

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-! ### One step towards the origin -/

/-- **One step in a single coordinate.**  For `u ≠ 0` on the cycle `ZMod L` there is a
unit `e` with `|u - e| = |u| - 1`: move towards `0` the short way round. -/
theorem exists_zdist_step (hL : 3 ≤ L) {u : ZMod L} (hu : u ≠ 0) :
    ∃ e : ZMod L, zdist L e = 1 ∧ zdist L (u - e) + 1 = zdist L u := by
  have hcast : ((u.val : ℕ) : ZMod L) = u := ZMod.natCast_rightInverse u
  have hval : u.val < L := ZMod.val_lt u
  have hval0 : u.val ≠ 0 := by
    intro h
    apply hu
    rw [← hcast, h, Nat.cast_zero]
  rcases le_total u.val (L - u.val) with hle | hle
  · -- the short way round is downwards
    refine ⟨1, zdist_one hL, ?_⟩
    have hstep : u - 1 = ((u.val - 1 : ℕ) : ZMod L) := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hval0), Nat.cast_one, hcast]
    have hvals : (u - 1).val = u.val - 1 := by
      rw [hstep, ZMod.val_cast_of_lt (by omega)]
    rw [zdist, zdist, hvals]
    omega
  · -- the short way round is upwards
    refine ⟨-1, zdist_neg_one hL, ?_⟩
    have hstep : u - (-1) = ((u.val + 1 : ℕ) : ZMod L) := by
      rw [Nat.cast_add, Nat.cast_one, hcast, sub_neg_eq_add]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hval) with heq | hlt
    · -- `u = -1`, and the step lands on `0`
      have hzero : u - (-1) = 0 := by
        have hcongr : ((u.val + 1 : ℕ) : ZMod L) = ((L : ℕ) : ZMod L) :=
          congrArg (fun n : ℕ => (n : ZMod L)) heq
        rw [hstep, hcongr, ZMod.natCast_self]
      rw [hzero, zdist, zdist]
      simp only [ZMod.val_zero, Nat.sub_zero]
      omega
    · have hvals : (u - (-1)).val = u.val + 1 := by
        rw [hstep, ZMod.val_cast_of_lt hlt]
      rw [zdist, zdist, hvals]
      omega

/-- **One step on `Z_L^d`.**  For `x ≠ 0` there is a neighbour direction `e`, `|e| = 1`,
with `|x - e| = |x| - 1`: the `ℓ¹` distance is a sum over coordinates, so a step in any
coordinate that is not yet `0` does the job. -/
theorem exists_step (hL : 3 ≤ L) {x : Zd d L} (hx : x ≠ 0) :
    ∃ e : Zd d L, zdistD d L e = 1 ∧ zdistD d L (x - e) + 1 = zdistD d L x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext fun i => hcon i)
  obtain ⟨u, hu1, hu2⟩ := exists_zdist_step (L := L) hL hi
  refine ⟨Pi.single i u, ?_, ?_⟩
  · rw [zdistD_single, hu1]
  · have hsplit : ∀ y : Zd d L, zdistD d L y
        = zdist L (y i) + ∑ j ∈ Finset.univ.erase i, zdist L (y j) := by
      intro y
      rw [zdistD]
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have herase : ∑ j ∈ Finset.univ.erase i, zdist L ((x - Pi.single i u : Zd d L) j)
        = ∑ j ∈ Finset.univ.erase i, zdist L (x j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [hji]
    have hdiag : (x - Pi.single i u : Zd d L) i = x i - u := by
      simp
    have h1 := hsplit (x - Pi.single i u)
    have h2 := hsplit x
    rw [hdiag, herase] at h1
    omega

/-! ### Stochasticity and symmetry

The rows of `SBR` sum to `1` over `ℝ`, not only over `ℂ` (`sum_SB_row`). -/

theorem sum_SBR_row (hL : 3 ≤ L) (a : Zd d L) : ∑ b, SBR d L g a b = 1 := by
  rw [← sum_sbKernelR d L g hL]
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ fun b => by simp [SBR]

/-- `S^(B)` is symmetric, hence so is every power, hence the columns sum to `1` too. -/
theorem SBR_comm (a b : Zd d L) : SBR d L g a b = SBR d L g b a := by
  simp only [SBR, Matrix.of_apply]
  rw [show b - a = -(a - b) by ring, sbKernelR_neg]

/-! ### A norm bound for series -/

/-- A complex series bounded termwise by a summable real majorant. -/
theorem norm_tsum_le_of_le {f : ℕ → ℂ} {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ k, ‖f k‖ ≤ u k) : ‖∑' k : ℕ, f k‖ ≤ ∑' k : ℕ, u k := by
  have hns : Summable fun k : ℕ => ‖f k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) h hu
  exact le_trans (norm_tsum_le_tsum_norm hns) (Summable.tsum_le_tsum h hns hu)

end RBM
