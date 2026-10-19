/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import RBM3D.Defs.Lattice

/-!
# Every point of `Z_L^d` has exactly `2d` nearest neighbours

`#{x : Zd d L | |x| = 1} = 2d` as soon as `3 ≤ L`.  The unit sphere is the image of the
injection `Fin d × Bool → Zd d L`, `(i, b) ↦ ±eᵢ`: a sum of natural numbers equal to `1`
has exactly one nonzero term, and on the cycle `ZMod L` the points at distance `1` from
the origin are `±1`.

`3 ≤ L` is needed for `1 ≠ -1`.  For `L = 2` one has `1 = -1` in `ZMod 2`, the two
neighbours in each direction coincide, and the count is `d`; for `L = 1` the torus is a
point.  This is where the hypothesis `3 ≤ L` of `S^(B)(g)` being doubly stochastic comes
from.
-/

namespace RBM

section OneDim

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
theorem val_one_of_three_le (hL : 3 ≤ L) : (1 : ZMod L).val = 1 :=
  ZMod.val_one'' (by omega)

theorem val_neg_one_of_three_le (hL : 3 ≤ L) : (-1 : ZMod L).val = L - 1 := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    intro h
    have := val_one_of_three_le hL
    rw [h, ZMod.val_zero] at this
    exact absurd this (by decide)
  rw [ZMod.neg_val, val_one_of_three_le hL]
  simp [h1]

theorem one_ne_neg_one_of_three_le (hL : 3 ≤ L) : (1 : ZMod L) ≠ -1 := by
  intro h
  have := congrArg ZMod.val h
  rw [val_one_of_three_le hL, val_neg_one_of_three_le hL] at this
  omega

omit [NeZero L] in
theorem zdist_one (hL : 3 ≤ L) : zdist L 1 = 1 := by
  simp only [zdist, val_one_of_three_le hL]; omega

theorem zdist_neg_one (hL : 3 ≤ L) : zdist L (-1) = 1 := by
  rw [zdist_neg, zdist_one hL]

/-- On the cycle `ZMod L`, `L ≥ 3`, the points at distance `1` from the origin are `±1`. -/
theorem zdist_eq_one_iff (hL : 3 ≤ L) {u : ZMod L} : zdist L u = 1 ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro h
    have hu : u.val < L := ZMod.val_lt u
    simp only [zdist] at h
    rcases (show u.val = 1 ∨ u.val = L - 1 by omega) with h' | h'
    · left
      exact ZMod.val_injective L (h'.trans (val_one_of_three_le hL).symm)
    · right
      exact ZMod.val_injective L (h'.trans (val_neg_one_of_three_le hL).symm)
  · rintro (rfl | rfl)
    · exact zdist_one hL
    · exact zdist_neg_one hL

end OneDim

variable (d L : ℕ) [NeZero L]

/-- The unit vector `±eᵢ`: `true` gives `+eᵢ`, `false` gives `-eᵢ`. -/
def unitVec (p : Fin d × Bool) : Zd d L :=
  Pi.single p.1 (if p.2 then 1 else -1)

variable {d L}

omit [NeZero L] in
theorem zdistD_single (i : Fin d) (u : ZMod L) : zdistD d L (Pi.single i u) = zdist L u := by
  simp only [zdistD]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem zdistD_unitVec (hL : 3 ≤ L) (p : Fin d × Bool) : zdistD d L (unitVec d L p) = 1 := by
  rw [unitVec, zdistD_single]
  cases p.2
  · exact zdist_neg_one hL
  · exact zdist_one hL

theorem unitVec_injective (hL : 3 ≤ L) : Function.Injective (unitVec d L) := by
  have hne : ∀ b : Bool, (if b then (1 : ZMod L) else -1) ≠ 0 := by
    intro b h
    have := congrArg (zdist L) h
    cases b
    · simp [zdist_neg_one hL] at this
    · simp [zdist_one hL] at this
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  simp only [unitVec] at h
  have hij : i = j := by
    by_contra hij
    have := congrFun h i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
    exact hne b this
  subst hij
  have := congrFun h i
  simp only [Pi.single_eq_same] at this
  have h1 := one_ne_neg_one_of_three_le hL
  cases b <;> cases c <;> simp_all [eq_comm]

/-- A point at distance `1` from the origin is a unit vector `±eᵢ`. -/
theorem exists_unitVec_of_zdistD_eq_one (hL : 3 ≤ L) {x : Zd d L} (hx : zdistD d L x = 1) :
    ∃ p, unitVec d L p = x := by
  -- some coordinate is nonzero
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : x = 0 := funext h
    rw [this, zdistD_zero] at hx
    exact absurd hx (by decide)
  -- and it carries the whole sum
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => zdist L (x j)) (Finset.mem_univ i)
  simp only [zdistD] at hx
  rw [hx] at hsplit
  have hpos : 0 < zdist L (x i) :=
    Nat.pos_of_ne_zero fun h => hi ((zdist_eq_zero_iff L).mp h)
  have hi1 : zdist L (x i) = 1 := by omega
  have hrest : ∑ j ∈ Finset.univ.erase i, zdist L (x j) = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  have hx' : x = Pi.single i (x i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Pi.single_eq_of_ne hj]
      exact (zdist_eq_zero_iff L).mp (hrest j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
  rcases (zdist_eq_one_iff hL).mp hi1 with h | h
  · exact ⟨(i, true), by rw [hx', unitVec, h]; simp⟩
  · exact ⟨(i, false), by rw [hx', unitVec, h]; simp⟩

/-- The unit sphere of `Z_L^d` is the set of unit vectors `±eᵢ`. -/
theorem filter_zdistD_eq_one (hL : 3 ≤ L) :
    (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1) =
      Finset.univ.image (unitVec d L) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · exact exists_unitVec_of_zdistD_eq_one hL
  · rintro ⟨p, rfl⟩
    exact zdistD_unitVec hL p

variable (d L) in
/-- Every point of `Z_L^d` has exactly `2d` nearest neighbours, for `L ≥ 3`. -/
theorem card_nbhd (hL : 3 ≤ L) :
    (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1).card = 2 * d := by
  rw [filter_zdistD_eq_one hL, Finset.card_image_of_injective _ (unitVec_injective hL),
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]

instance (x y : Zd d L) : Decidable (Adj d L x y) :=
  inferInstanceAs (Decidable (_ = _))

variable (d L) in
/-- The same count for the neighbours of an arbitrary point `a`. -/
theorem card_adj (hL : 3 ≤ L) (a : Zd d L) :
    (Finset.univ.filter fun b : Zd d L => Adj d L a b).card = 2 * d := by
  rw [← card_nbhd d L hL]
  refine Finset.card_bij (fun b _ => a - b) ?_ ?_ ?_
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  · intro b₁ _ b₂ _ h
    simpa using h
  · intro x hx
    refine ⟨a - x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    change zdistD d L (a - (a - x)) = 1
    simpa using (Finset.mem_filter.mp hx).2

end RBM
