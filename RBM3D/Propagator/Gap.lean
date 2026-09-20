/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4

/-!
# Connectivity of `S^(B)`: every entry of a high enough power is positive

`docs/QUEUE.md`, Q51.  Q41 produced a fixed-`L` certificate for `(prop:ThfadC)` but none
for `(prop:ThfadC_short)`, `(prop:BD1)`, `(prop:BD2)`, `(prop:ThfadC0)`, and located the
obstruction precisely (`RBM.Test.not_exists_uniform_entry_bound`): at fixed `L` the
right-hand sides of those four stay bounded as `t → 1` while the entries of `Θ_t` do not,
so each of them needs a *cancellation* -- a difference of entries, or the removal of the
zero mode -- and at fixed `L` that cancellation is a statement about `S^(B)` alone.

This file is the first block of it: `S^(B)` is the transition matrix of a **lazy,
irreducible** random walk on `Z_L^d`, so all entries of `(S^(B))^n` are strictly positive
once `n` reaches the diameter of the torus.  Writing `Θ̊_t = Σ_k ξ^k (S^k - P)` with `P`
the projection on constants (`RBM.Theta0_apply_eq` is the `k`-free half of that identity),
this positivity is exactly the Doeblin condition that makes `S^k - P` decay geometrically,
uniformly in `t` -- which is what the four missing certificates need.

## What is here

* `RBM.exists_zdist_step`, `RBM.exists_step` : from any `x ≠ 0` one unit step decreases
  `|x|` by exactly one.  This is the connectivity of the torus in the form the induction
  below wants.
* `RBM.sbKernelR_pos` : the kernel is strictly positive on `{|x| ≤ 1}` -- the walk is lazy
  (`x = 0`) and has all `2d` neighbours (`|x| = 1`), for every `g > 0`.
* `RBM.SBR_pow_pos` : `0 < (S^(B))^n_{ab}` whenever `|a - b| ≤ n`.

Laziness is what makes the statement an inequality `|a - b| ≤ n` rather than a parity
condition: without the `x = 0` term the walk on `Z_L^d` with `L` even would be bipartite
and `(S^(B))^n_{ab}` would vanish for every `n` of the wrong parity.  It is also what
rules out `-1` in the spectrum, the borderline case `m² = -1` (`E = 0`) of Q41's note.
-/

namespace RBM

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

/-! ### Positivity -/

/-- The kernel of `S^(B)(g)` is strictly positive on `{|x| ≤ 1}`: the walk is lazy at
`x = 0` and has every neighbour at `|x| = 1`, for every `g > 0`. -/
theorem sbKernelR_pos (hg : 0 < g) {x : Zd d L} (hx : zdistD d L x ≤ 1) :
    0 < sbKernelR d L g x := by
  have hA : (0 : ℝ) < (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := by positivity
  unfold sbKernelR
  by_cases h0 : x = 0
  · have h1 : zdistD d L x ≠ 1 := by rw [h0, zdistD_zero]; omega
    simp only [h0, ite_true, ite_false, add_zero, zdistD_zero, Nat.zero_ne_one]
    exact hA
  · have h1 : zdistD d L x = 1 := by
      have := (zdistD_eq_zero_iff d L (x := x)).not.mpr h0
      omega
    simp only [h0, ite_false, h1, ite_true, zero_add]
    positivity

/-- **`S^(B)` connects the torus.**  Every entry of `(S^(B))^n` is strictly positive as
soon as `n` is at least the distance between the two points: there is a path of `|a - b|`
unit steps, and laziness lets the walk wait out the remaining `n - |a - b|` steps.

For `n` equal to the diameter of `Z_L^d` this says all entries of `(S^(B))^n` are
positive -- the Doeblin condition. -/
theorem SBR_pow_pos (hL : 3 ≤ L) (hg : 0 < g) :
    ∀ (n : ℕ) (a b : Zd d L), zdistD d L (a - b) ≤ n → 0 < (SBR d L g ^ n) a b := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have hab : a = b := by
      have : zdistD d L (a - b) = 0 := by omega
      have := (zdistD_eq_zero_iff d L).mp this
      exact sub_eq_zero.mp this
    rw [pow_zero, Matrix.one_apply]
    simp only [hab, ite_true]
    norm_num
  | succ n ih =>
    intro a b h
    rw [pow_succ, Matrix.mul_apply]
    have hnonneg : ∀ c : Zd d L, c ∈ Finset.univ →
        0 ≤ (SBR d L g ^ n) a c * SBR d L g c b := fun c _ =>
      mul_nonneg (SBR_pow_nonneg d L g n a c)
        (by simpa [SBR] using sbKernelR_nonneg d L g (c - b))
    refine (Finset.sum_pos_iff_of_nonneg hnonneg).mpr ?_
    by_cases hle : zdistD d L (a - b) ≤ n
    · -- stay put on the last step
      refine ⟨b, Finset.mem_univ b, mul_pos (ih a b hle) ?_⟩
      have : SBR d L g b b = sbKernelR d L g 0 := by simp [SBR]
      rw [this]
      exact sbKernelR_pos hg (by rw [zdistD_zero]; omega)
    · -- take one step towards `b`
      have hne : a - b ≠ 0 := by
        intro h0
        rw [h0, zdistD_zero] at hle
        omega
      obtain ⟨e, he1, he2⟩ := exists_step hL hne
      refine ⟨b + e, Finset.mem_univ _, mul_pos (ih a (b + e) ?_) ?_⟩
      · have : a - (b + e) = a - b - e := by rw [sub_add_eq_sub_sub]
        rw [this]
        omega
      · have : SBR d L g (b + e) b = sbKernelR d L g e := by
          simp [SBR, add_sub_cancel_left]
        rw [this]
        exact sbKernelR_pos hg (by rw [he1])

/-- **The Doeblin condition.**  All entries of `(S^(B))^{R_L}`, `R_L` the diameter of the
torus, are bounded below by one positive `ε`: any two points are within `R_L` steps of
each other, so `SBR_pow_pos` applies to every pair, and a finite set of positive numbers
has a positive minimum.

This is the form the next block wants (`docs/QUEUE.md`, Q51, block 2): a stochastic matrix
all of whose entries are `≥ ε` contracts oscillations by `1 - ε L^d` per `R_L` steps
(Dobrushin), which makes `S^k - P` decay geometrically and `Θ̊_t = Σ_k ξ^k (S^k - P)`
bounded uniformly in `t` at fixed `L`. -/
theorem exists_doeblin (hL : 3 ≤ L) (hg : 0 < g) :
    ∃ ε > (0 : ℝ), ∀ a b : Zd d L, ε ≤ (SBR d L g ^ torusDiam d L) a b := by
  classical
  have hne : (Finset.univ : Finset (Zd d L × Zd d L)).Nonempty := ⟨(0, 0), Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne fun p : Zd d L × Zd d L =>
      (SBR d L g ^ torusDiam d L) p.1 p.2, ?_, ?_⟩
  · simp only [gt_iff_lt]
    rw [Finset.lt_inf'_iff]
    intro p _
    exact SBR_pow_pos hL hg _ p.1 p.2 (zdistD_le_torusDiam d L _)
  · intro a b
    exact Finset.inf'_le _ (Finset.mem_univ (a, b))

end RBM
