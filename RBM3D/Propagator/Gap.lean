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
theorem exists_doeblin (hL : 3 ≤ L) (hg : 0 < g) {N : ℕ} (hN : torusDiam d L ≤ N) :
    ∃ ε > (0 : ℝ), ∀ a b : Zd d L, ε ≤ (SBR d L g ^ N) a b := by
  classical
  have hne : (Finset.univ : Finset (Zd d L × Zd d L)).Nonempty := ⟨(0, 0), Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne fun p : Zd d L × Zd d L => (SBR d L g ^ N) p.1 p.2, ?_, ?_⟩
  · simp only [gt_iff_lt]
    rw [Finset.lt_inf'_iff]
    intro p _
    exact SBR_pow_pos hL hg _ p.1 p.2 ((zdistD_le_torusDiam d L _).trans hN)
  · intro a b
    exact Finset.inf'_le _ (Finset.mem_univ (a, b))

/-! ### Stochasticity of the powers

The Dobrushin argument needs the rows of every power to sum to `1`, over `ℝ` and not only
over `ℂ` (`RBM.sum_SB_row`). -/

theorem sum_SBR_row (hL : 3 ≤ L) (a : Zd d L) : ∑ b, SBR d L g a b = 1 := by
  rw [← sum_sbKernelR d L g hL]
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ fun b => by simp [SBR]

theorem sum_SBR_pow_row (hL : 3 ≤ L) : ∀ (n : ℕ) (a : Zd d L), ∑ b, (SBR d L g ^ n) a b = 1 := by
  intro n
  induction n with
  | zero =>
    intro a
    simp [Matrix.one_apply]
  | succ n ih =>
    intro a
    rw [pow_succ]
    have : ∀ b, (SBR d L g ^ n * SBR d L g) a b
        = ∑ c, (SBR d L g ^ n) a c * SBR d L g c b := fun b => Matrix.mul_apply
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_comm]
    have hinner : ∀ c : Zd d L, ∑ b, (SBR d L g ^ n) a c * SBR d L g c b
        = (SBR d L g ^ n) a c := by
      intro c
      rw [← Finset.mul_sum, sum_SBR_row hL c, mul_one]
    rw [Finset.sum_congr rfl fun c _ => hinner c]
    exact ih a

/-- `S^(B)` is symmetric, hence so is every power, hence the columns sum to `1` too. -/
theorem SBR_comm (a b : Zd d L) : SBR d L g a b = SBR d L g b a := by
  simp only [SBR, Matrix.of_apply]
  rw [show b - a = -(a - b) by ring, sbKernelR_neg]

theorem SBR_isSymm : (SBR d L g).IsSymm := by
  ext a b
  exact (SBR_comm a b).symm

theorem SBR_pow_comm (n : ℕ) (a b : Zd d L) :
    (SBR d L g ^ n) a b = (SBR d L g ^ n) b a :=
  ((SBR_isSymm (d := d) (L := L) (g := g)).pow n).apply b a

theorem sum_SBR_pow_col (hL : 3 ≤ L) (n : ℕ) (b : Zd d L) :
    ∑ a, (SBR d L g ^ n) a b = 1 := by
  rw [Finset.sum_congr rfl fun a _ => SBR_pow_comm n a b]
  exact sum_SBR_pow_row hL n b

/-! ### Oscillation, and the Dobrushin contraction -/

/-- `osc f = max f - min f` on the (finite, nonempty) torus. -/
noncomputable def osc (f : Zd d L → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.inf' Finset.univ_nonempty f

theorem le_sup_osc (f : Zd d L → ℝ) (a : Zd d L) :
    f a ≤ Finset.univ.sup' Finset.univ_nonempty f :=
  Finset.le_sup' f (Finset.mem_univ a)

theorem inf_osc_le (f : Zd d L → ℝ) (a : Zd d L) :
    Finset.univ.inf' Finset.univ_nonempty f ≤ f a :=
  Finset.inf'_le f (Finset.mem_univ a)

theorem osc_nonneg (f : Zd d L → ℝ) : 0 ≤ osc f := by
  have := (inf_osc_le f 0).trans (le_sup_osc f 0)
  simp only [osc]
  linarith

/-- **Dobrushin's contraction.**  If every entry of the stochastic matrix `M` is at least
`ε`, then `M` contracts oscillations by `1 - ε L^d`.

`ε = 0` is allowed and gives the non-expansion `osc (M *ᵥ f) ≤ osc f` that a stochastic
matrix always has; the content is that a *uniformly positive* `M` contracts strictly.  The
proof is two lines of bookkeeping: subtract `ε` from every entry, so that both rows become
non-negative with the same total mass `1 - ε L^d`, and the `ε`-part cancels between the two
rows. -/
theorem osc_mulVec_le (M : Matrix (Zd d L) (Zd d L) ℝ) {ε : ℝ}
    (hM : ∀ a b, ε ≤ M a b) (hrow : ∀ a, ∑ b, M a b = 1) (f : Zd d L → ℝ) :
    osc (M *ᵥ f) ≤ (1 - ε * (L : ℝ) ^ d) * osc f := by
  classical
  set S := Finset.univ.sup' (Finset.univ_nonempty (α := Zd d L)) f with hS
  set I := Finset.univ.inf' (Finset.univ_nonempty (α := Zd d L)) f with hI
  -- the mass left after subtracting `ε` from every entry
  have hmass : ∀ a : Zd d L, ∑ b, (M a b - ε) = 1 - ε * (L : ℝ) ^ d := by
    intro a
    rw [Finset.sum_sub_distrib, hrow a, Finset.sum_const, Finset.card_univ, card_Zd,
      nsmul_eq_mul, Nat.cast_pow]
    ring
  have hq0 : 0 ≤ 1 - ε * (L : ℝ) ^ d := by
    rw [← hmass 0]
    exact Finset.sum_nonneg fun b _ => sub_nonneg.mpr (hM 0 b)
  -- the pairwise bound
  have hpair : ∀ a a' : Zd d L,
      (M *ᵥ f) a - (M *ᵥ f) a' ≤ (1 - ε * (L : ℝ) ^ d) * osc f := by
    intro a a'
    have hsplit : ∀ c : Zd d L, (M *ᵥ f) c = (∑ b, (M c b - ε) * f b) + ε * ∑ b, f b := by
      intro c
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hupper : ∑ b, (M a b - ε) * f b ≤ (1 - ε * (L : ℝ) ^ d) * S := by
      calc ∑ b, (M a b - ε) * f b
          ≤ ∑ b, (M a b - ε) * S :=
            Finset.sum_le_sum fun b _ =>
              mul_le_mul_of_nonneg_left (le_sup_osc f b) (sub_nonneg.mpr (hM a b))
        _ = (1 - ε * (L : ℝ) ^ d) * S := by rw [← Finset.sum_mul, hmass a]
    have hlower : (1 - ε * (L : ℝ) ^ d) * I ≤ ∑ b, (M a' b - ε) * f b := by
      calc (1 - ε * (L : ℝ) ^ d) * I = ∑ b, (M a' b - ε) * I := by rw [← Finset.sum_mul, hmass a']
        _ ≤ ∑ b, (M a' b - ε) * f b :=
            Finset.sum_le_sum fun b _ =>
              mul_le_mul_of_nonneg_left (inf_osc_le f b) (sub_nonneg.mpr (hM a' b))
    rw [hsplit a, hsplit a', osc]
    have : (1 - ε * (L : ℝ) ^ d) * (S - I)
        = (1 - ε * (L : ℝ) ^ d) * S - (1 - ε * (L : ℝ) ^ d) * I := by ring
    rw [← hS, ← hI, this]
    linarith
  -- the oscillation is attained
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Zd d L)) (M *ᵥ f)
  obtain ⟨a', -, ha'⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Zd d L)) (M *ᵥ f)
  rw [osc, ha, ha']
  exact hpair a a'

/-- Iterating Dobrushin: `k` applications of a uniformly positive stochastic matrix
contract the oscillation by `(1 - ε L^d)^k`. -/
theorem osc_mulVec_pow_le (M : Matrix (Zd d L) (Zd d L) ℝ) {ε : ℝ}
    (hM : ∀ a b, ε ≤ M a b) (hrow : ∀ a, ∑ b, M a b = 1) (hq0 : 0 ≤ 1 - ε * (L : ℝ) ^ d)
    (f : Zd d L → ℝ) : ∀ k : ℕ, osc ((M ^ k) *ᵥ f) ≤ (1 - ε * (L : ℝ) ^ d) ^ k * osc f := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (M ^ (k + 1)) *ᵥ f = M *ᵥ ((M ^ k) *ᵥ f) := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hstep]
    calc osc (M *ᵥ ((M ^ k) *ᵥ f))
        ≤ (1 - ε * (L : ℝ) ^ d) * osc ((M ^ k) *ᵥ f) := osc_mulVec_le M hM hrow _
      _ ≤ (1 - ε * (L : ℝ) ^ d) * ((1 - ε * (L : ℝ) ^ d) ^ k * osc f) :=
          mul_le_mul_of_nonneg_left ih hq0
      _ = (1 - ε * (L : ℝ) ^ d) ^ (k + 1) * osc f := by ring

/-- **Geometric mixing.**  `(S^(B))^n_{ab}` converges to the flat value `L^{-d}`
geometrically, at a rate that depends on `L` but not on anything else.

This is the cancellation the four uncertified premises of Q41 need, in its elementary
form: `Θ̊_t = Σ_k ξ^k ((S^(B))^k - P)` is then bounded uniformly in `t` at fixed `L`
(`docs/QUEUE.md`, Q53).  The exponent is `n / R` with `R` one more than the diameter of
the torus: oscillations contract by `q` every `R` steps and never grow in between. -/
theorem exists_mixing (hL : 3 ≤ L) (hg : 0 < g) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (n : ℕ) (a b : Zd d L),
      |(SBR d L g ^ n) a b - ((L : ℝ) ^ d)⁻¹| ≤ q ^ (n / (torusDiam d L + 1)) := by
  classical
  set R := torusDiam d L + 1 with hR
  have hR0 : 0 < R := Nat.succ_pos _
  obtain ⟨ε, hε, hεM⟩ := exists_doeblin hL hg (N := R) (Nat.le_succ _)
  set q : ℝ := 1 - ε * (L : ℝ) ^ d with hq
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by
      have : (0 : ℕ) < L := by omega
      exact_mod_cast this
    positivity
  -- the rows of every power are a probability vector
  have hrowM : ∀ a : Zd d L, ∑ b, (SBR d L g ^ R) a b = 1 := sum_SBR_pow_row hL R
  have hq0 : 0 ≤ q := by
    rw [hq, ← (by
      rw [Finset.sum_sub_distrib, hrowM 0, Finset.sum_const, Finset.card_univ, card_Zd,
        nsmul_eq_mul, Nat.cast_pow]
      ring : ∑ b : Zd d L, ((SBR d L g ^ R) 0 b - ε) = 1 - ε * (L : ℝ) ^ d)]
    exact Finset.sum_nonneg fun b _ => sub_nonneg.mpr (hεM 0 b)
  have hq1 : q < 1 := by
    rw [hq]
    nlinarith
  refine ⟨q, hq0, hq1, ?_⟩
  intro n a b
  -- the function whose oscillation controls the entry
  set h : Zd d L → ℝ := fun c => (SBR d L g ^ n) c b with hh
  have hcol : ∑ c, h c = 1 := sum_SBR_pow_col hL n b
  -- `h` is `S^n` applied to the indicator of `b`
  have hdelta : h = (SBR d L g ^ n) *ᵥ (fun c => if c = b then (1 : ℝ) else 0) := by
    funext c
    simp [hh, Matrix.mulVec, dotProduct]
  -- the flat value lies between the extremes of `h`
  have hcard : ∑ _c : Zd d L, (1 : ℝ) = (L : ℝ) ^ d := by
    rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul, Nat.cast_pow, mul_one]
  have hinf : Finset.univ.inf' Finset.univ_nonempty h ≤ ((L : ℝ) ^ d)⁻¹ := by
    by_contra hcon
    push Not at hcon
    have : (L : ℝ) ^ d * ((L : ℝ) ^ d)⁻¹ < ∑ c, h c := by
      calc (L : ℝ) ^ d * ((L : ℝ) ^ d)⁻¹
          = ∑ _c : Zd d L, ((L : ℝ) ^ d)⁻¹ := by
            rw [← hcard, Finset.sum_mul]; simp
        _ < ∑ c, h c :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ =>
              lt_of_lt_of_le hcon (inf_osc_le h c)
    rw [hcol, mul_inv_cancel₀ (ne_of_gt hLd)] at this
    exact lt_irrefl _ this
  have hsup : ((L : ℝ) ^ d)⁻¹ ≤ Finset.univ.sup' Finset.univ_nonempty h := by
    by_contra hcon
    push Not at hcon
    have : ∑ c, h c < (L : ℝ) ^ d * ((L : ℝ) ^ d)⁻¹ := by
      calc ∑ c, h c
          < ∑ _c : Zd d L, ((L : ℝ) ^ d)⁻¹ :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ =>
              lt_of_le_of_lt (le_sup_osc h c) hcon
        _ = (L : ℝ) ^ d * ((L : ℝ) ^ d)⁻¹ := by rw [← hcard, Finset.sum_mul]; simp
    rw [hcol, mul_inv_cancel₀ (ne_of_gt hLd)] at this
    exact lt_irrefl _ this
  have hentry : |h a - ((L : ℝ) ^ d)⁻¹| ≤ osc h := by
    rw [abs_le]
    constructor
    · have := inf_osc_le h a
      have := le_sup_osc h a
      simp only [osc]
      linarith
    · have := le_sup_osc h a
      have := inf_osc_le h a
      simp only [osc]
      linarith
  -- the oscillation contracts every `R` steps and never grows in between
  have hosc : osc h ≤ q ^ (n / R) := by
    set k := n / R with hk
    have hsplit : (SBR d L g ^ n) = (SBR d L g ^ (n - R * k)) * ((SBR d L g ^ R) ^ k) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      have : R * k ≤ n := Nat.mul_div_le n R
      omega
    have hdelta_osc : osc (fun c : Zd d L => if c = b then (1 : ℝ) else 0) ≤ 1 := by
      have hs : Finset.univ.sup' Finset.univ_nonempty
          (fun c : Zd d L => if c = b then (1 : ℝ) else 0) ≤ 1 := by
        refine Finset.sup'_le _ _ fun c _ => ?_
        split_ifs <;> norm_num
      have hi : (0 : ℝ) ≤ Finset.univ.inf' Finset.univ_nonempty
          (fun c : Zd d L => if c = b then (1 : ℝ) else 0) := by
        refine Finset.le_inf' _ _ fun c _ => ?_
        split_ifs <;> norm_num
      simp only [osc]
      linarith
    have hcontract : osc (((SBR d L g ^ R) ^ k) *ᵥ
        (fun c : Zd d L => if c = b then (1 : ℝ) else 0)) ≤ q ^ k := by
      refine le_trans (osc_mulVec_pow_le _ hεM hrowM hq0 _ k) ?_
      calc q ^ k * osc (fun c : Zd d L => if c = b then (1 : ℝ) else 0)
          ≤ q ^ k * 1 := mul_le_mul_of_nonneg_left hdelta_osc (by positivity)
        _ = q ^ k := by ring
    have hnonexp : osc h ≤ osc (((SBR d L g ^ R) ^ k) *ᵥ
        (fun c : Zd d L => if c = b then (1 : ℝ) else 0)) := by
      rw [hdelta, hsplit, ← Matrix.mulVec_mulVec]
      refine le_trans (osc_mulVec_le (SBR d L g ^ (n - R * k)) (ε := 0)
        (fun x y => SBR_pow_nonneg d L g _ x y) (sum_SBR_pow_row hL _) _) ?_
      simp
    exact le_trans hnonexp hcontract
  rw [hh] at hentry
  exact le_trans hentry hosc

end RBM
