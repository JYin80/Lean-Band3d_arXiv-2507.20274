/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import RBM3D.Defs.Lattice

/-!
# Counting lattice points on spheres of `Z_L^d`

The lattice sums behind `lem:propT` (Appendix A.3) are radial: they are sums over
`Z_L^d` of functions of the periodic `ℓ¹` distance `|x| = zdistD d L x`.  Reducing them
to one-dimensional sums needs the sphere count

  `#{x ∈ Z_L^d : |x| = r} ≤ 2^d (r+1)^{d-1}`    (`card_sphere_le`, for `d ≥ 1`),

which is what this file proves.  The one-dimensional ingredients are that on the cycle
`ZMod L` at most two points lie at distance `r` from the origin and at most `2r+1` lie
within distance `r`; the `d`-dimensional count follows by induction on `d`, splitting
off the first coordinate with `Fin.consEquiv`.
-/

namespace RBM

open Finset

variable {L : ℕ} [NeZero L]

/-! ### One dimension -/

theorem card_zdist_eq_le (r : ℕ) :
    (univ.filter fun u : ZMod L => zdist L u = r).card ≤ 2 := by
  have hmaps : Set.MapsTo (fun u : ZMod L => u.val)
      (univ.filter fun u : ZMod L => zdist L u = r) ({r, L - r} : Finset ℕ) := by
    intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu
    have hv : u.val < L := ZMod.val_lt u
    simp only [zdist] at hu
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  calc (univ.filter fun u : ZMod L => zdist L u = r).card
      ≤ ({r, L - r} : Finset ℕ).card :=
        card_le_card_of_injOn _ hmaps (fun a _ b _ h => ZMod.val_injective L h)
    _ ≤ 2 := card_le_two

theorem card_zdist_le_le (r : ℕ) :
    (univ.filter fun u : ZMod L => zdist L u ≤ r).card ≤ 2 * r + 1 := by
  have hmaps : Set.MapsTo (fun u : ZMod L => u.val)
      (univ.filter fun u : ZMod L => zdist L u ≤ r)
      ((range (r + 1) ∪ Ico (L - r) L : Finset ℕ) : Set ℕ) := by
    intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu
    have hv : u.val < L := ZMod.val_lt u
    simp only [zdist] at hu
    simp only [coe_union, coe_range, coe_Ico, Set.mem_union, Set.mem_Iio, Set.mem_Ico]
    omega
  calc (univ.filter fun u : ZMod L => zdist L u ≤ r).card
      ≤ (range (r + 1) ∪ Ico (L - r) L).card :=
        card_le_card_of_injOn _ hmaps (fun a _ b _ h => ZMod.val_injective L h)
    _ ≤ (range (r + 1)).card + (Ico (L - r) L).card := card_union_le _ _
    _ ≤ 2 * r + 1 := by rw [card_range, Nat.card_Ico]; omega

/-! ### The sphere count -/

/-- The number of points of `Z_L^d` at distance `r` from the origin. -/
def sphereCard (d L : ℕ) [NeZero L] (r : ℕ) : ℕ :=
  (univ.filter fun x : Zd d L => zdistD d L x = r).card

omit [NeZero L] in
theorem zdistD_cons (d : ℕ) (u : ZMod L) (y : Zd d L) :
    zdistD (d + 1) L (Fin.cons u y : Zd (d + 1) L) = zdist L u + zdistD d L y := by
  simp [zdistD, Fin.sum_univ_succ]

theorem sphereCard_zero (r : ℕ) : sphereCard 0 L r = if r = 0 then 1 else 0 := by
  have h : ∀ x : Zd 0 L, zdistD 0 L x = 0 := fun x => by simp [zdistD]
  by_cases hr : r = 0
  · subst hr
    simp [sphereCard, h]
  · simp [sphereCard, h, hr, Ne.symm hr]

/-- Splitting off the first coordinate:
`#{x ∈ Z_L^{d+1} : |x| = r} = Σ_{u ∈ Z_L, |u| ≤ r} #{y ∈ Z_L^d : |y| = r - |u|}`. -/
theorem sphereCard_succ (d r : ℕ) :
    sphereCard (d + 1) L r
      = ∑ u : ZMod L, if zdist L u ≤ r then sphereCard d L (r - zdist L u) else 0 := by
  simp only [sphereCard, card_filter]
  rw [← (Fin.consEquiv fun _ : Fin (d + 1) => ZMod L).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  have hcons : ∀ y : Zd d L,
      zdistD (d + 1) L ((Fin.consEquiv fun _ : Fin (d + 1) => ZMod L) (u, y))
        = zdist L u + zdistD d L y := fun y => zdistD_cons d u y
  simp only [hcons]
  split_ifs with hu
  · exact sum_congr rfl fun y _ => by congr 1; exact propext (by omega)
  · exact sum_eq_zero fun y _ => by rw [ite_eq_right_iff]; intro h; omega

/-- **`#{x ∈ Z_L^{d+1} : |x| = r} ≤ 2^{d+1} (r+1)^d`.** -/
theorem card_sphere_le (d r : ℕ) : sphereCard (d + 1) L r ≤ 2 ^ (d + 1) * (r + 1) ^ d := by
  induction d generalizing r with
  | zero =>
    rw [sphereCard_succ]
    simp only [sphereCard_zero, pow_zero, mul_one, zero_add, pow_one]
    calc (∑ u : ZMod L, if zdist L u ≤ r then (if r - zdist L u = 0 then 1 else 0) else 0)
        = ∑ u : ZMod L, if zdist L u = r then 1 else 0 :=
          sum_congr rfl fun u _ => by split_ifs <;> omega
      _ = (univ.filter fun u : ZMod L => zdist L u = r).card := (card_filter _ _).symm
      _ ≤ 2 := card_zdist_eq_le r
  | succ d ih =>
    rw [sphereCard_succ]
    calc (∑ u : ZMod L, if zdist L u ≤ r then sphereCard (d + 1) L (r - zdist L u) else 0)
        ≤ ∑ u : ZMod L, if zdist L u ≤ r then 2 ^ (d + 1) * (r + 1) ^ d else 0 := by
          refine sum_le_sum fun u _ => ?_
          split_ifs with hu
          · exact (ih _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
          · exact le_rfl
      _ = (univ.filter fun u : ZMod L => zdist L u ≤ r).card * (2 ^ (d + 1) * (r + 1) ^ d) := by
          rw [card_filter, sum_mul]
          exact sum_congr rfl fun u _ => by split_ifs <;> simp
      _ ≤ (2 * r + 1) * (2 ^ (d + 1) * (r + 1) ^ d) :=
          Nat.mul_le_mul_right _ (card_zdist_le_le r)
      _ ≤ 2 ^ (d + 1 + 1) * (r + 1) ^ (d + 1) := by
          have : 2 * r + 1 ≤ 2 * (r + 1) := by omega
          calc (2 * r + 1) * (2 ^ (d + 1) * (r + 1) ^ d)
              ≤ 2 * (r + 1) * (2 ^ (d + 1) * (r + 1) ^ d) := Nat.mul_le_mul_right _ this
            _ = 2 ^ (d + 1 + 1) * (r + 1) ^ (d + 1) := by ring

end RBM
