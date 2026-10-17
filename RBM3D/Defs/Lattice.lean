/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The torus `Z_L^d` and its periodic distance

The paper works on `Z_L^d` and writes `|a|` for the distance to the origin and
`|a - b|` for the distance between two points.  Section 2.1 notes that the choice of
norm is immaterial, so we fix the periodic `ℓ¹` distance: coordinatewise graph
distance on the cycle `ZMod L`, summed over the `d` coordinates.

`zdist` and its lemmas are the one-dimensional ingredients, taken from the sister
project `RBM1D`; `zdistD` is the `d`-dimensional distance built from them.
-/

namespace RBM

/-- Graph distance from `u` to `0` on the cycle `ZMod L`. -/
def zdist (L : ℕ) (u : ZMod L) : ℕ := min u.val (L - u.val)

@[simp] theorem zdist_zero (L : ℕ) : zdist L 0 = 0 := by
  simp [zdist]

theorem zdist_eq_zero_iff (L : ℕ) [NeZero L] {u : ZMod L} : zdist L u = 0 ↔ u = 0 := by
  have hu : u.val < L := ZMod.val_lt u
  constructor
  · intro h
    have : u.val = 0 := by simp only [zdist] at h; omega
    exact (ZMod.val_eq_zero u).mp this
  · rintro rfl; simp

theorem zdist_add_le (L : ℕ) [NeZero L] (u v : ZMod L) :
    zdist L (u + v) ≤ zdist L u + zdist L v := by
  have hu : u.val < L := ZMod.val_lt u
  have hv : v.val < L := ZMod.val_lt v
  have hadd : (u + v).val = (u.val + v.val) % L := ZMod.val_add u v
  rcases lt_or_ge (u.val + v.val) L with h | h
  · rw [Nat.mod_eq_of_lt h] at hadd
    simp only [zdist, hadd]
    omega
  · have hmod : (u.val + v.val) % L = u.val + v.val - L := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hadd
    simp only [zdist, hadd]
    omega

theorem zdist_neg (L : ℕ) [NeZero L] (u : ZMod L) : zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hval : (-u).val = L - u.val := by simp [ZMod.neg_val, h]
    simp only [zdist, hval]
    omega

/-- The lattice `Z_L^d` of the paper.  `abbrev` so that the `Pi` instances --
`AddCommGroup`, `Fintype`, `DecidableEq` -- are found by instance search. -/
abbrev Zd (d L : ℕ) : Type := Fin d → ZMod L

/-- The torus has `L^d` points.  The paper writes this as `|Z_L^d| = L^d` and uses it
whenever a sum over the lattice is compared with its largest term. -/
theorem card_Zd (d L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

/-- The periodic `ℓ¹` distance to the origin on `Z_L^d`, written `|x|` in the paper. -/
def zdistD (d L : ℕ) (x : Zd d L) : ℕ := ∑ i, zdist L (x i)

@[simp] theorem zdistD_zero (d L : ℕ) : zdistD d L 0 = 0 := by
  simp [zdistD]

theorem zdistD_eq_zero_iff (d L : ℕ) [NeZero L] {x : Zd d L} :
    zdistD d L x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have : zdist L (x i) = 0 := by
      by_contra hne
      have hpos : 0 < zdist L (x i) := Nat.pos_of_ne_zero hne
      have : 0 < zdistD d L x :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => zdist L (x j))
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
      omega
    simpa using (zdist_eq_zero_iff L).mp this
  · rintro rfl; simp

theorem zdistD_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistD d L (x + y) ≤ zdistD d L x + zdistD d L y := by
  simp only [zdistD, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => zdist_add_le L (x i) (y i)

theorem zdistD_neg (d L : ℕ) [NeZero L] (x : Zd d L) : zdistD d L (-x) = zdistD d L x := by
  simp only [zdistD, Pi.neg_apply]
  exact Finset.sum_congr rfl fun i _ => zdist_neg L (x i)

/-- The nearest-neighbour relation `a ∼ b` of `(eq:variancematrix)`. -/
def Adj (d L : ℕ) (x y : Zd d L) : Prop := zdistD d L (x - y) = 1

end RBM
