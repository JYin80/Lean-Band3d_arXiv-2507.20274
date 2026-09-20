/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4
import RBM3D.Propagator.Interface
import RBM3D.Defs.RadialSum
import RBM3D.Loop.Unique
import RBM3D.Propagator.Gap

/-!
# Shape tests for the interface, in both directions

The file has two halves.  The **negative** half (the original one) refutes two statements
that the interface was once written with: they are the machine-checked record of a defect,
as house rule 13 asks.  The **positive** half (`docs/QUEUE.md`, Q41) is the other side of
the same coin: an assumption that is *false* makes every theorem carrying it vacuous, and
the axiom audit cannot see that -- it reports `0 axioms` either way.  What it can see is
whether a premise has a **certificate**: a theorem of this development witnessing that the
premise is satisfiable.

## Negative half: `(prop:ThfadC_short)` is a `σ₁ = σ₂` statement

`RBM.ThetaDecayShort` (`(prop:ThfadC_short)`, property 5' of `lem_propTH`) is stated for
the spectral parameter `m(σ)²` of the equal-sign case, with `0 < m.im`.  This file proves
that the restriction is *necessary*: the same bound at the spectral parameter `1` -- that
is, at `σ₁ ≠ σ₂`, where `m(+)m(-) = |m|² = 1` -- is **false**.

The argument is the one the paper's own structure suggests.  Summing the claimed bound
over `a` gives a constant, because `Σ_a e^{-c|a|}` is bounded uniformly in `L`
(`RBM.sum_radial_exp_decay_le`), while the row sum of the propagator is
`Σ_a Θ_{t,0a} = (1-t)⁻¹` (`RBM.sum_Theta_row_of_three_le`), which is unbounded as
`t → 1`.

This matters because an assumption that is false is not a harmless over-statement: every
theorem taking it as a hypothesis would be vacuous.  The interface was stated in that
form while properties 5–8 were axioms, where the same defect would have been an
inconsistency; `docs/paper-deltas.md` D11 records the correction.
-/

namespace RBM.Test

open Real

/-- **The equal-sign restriction in `RBM.ThetaDecayShort` is necessary.**  At the spectral
parameter `1`, which is the `σ₁ ≠ σ₂` case `m(+)m(-) = |m|² = 1`, the strong-decay bound
of `(prop:ThfadC_short)` fails. -/
theorem not_decayShort_at_one (k : ℕ) {g : ℝ} (hg : 0 < g) :
    ¬ ∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ),
        ∀ (L : ℕ) (_ : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd (k + 2) L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta (k + 2) L g ((t : ℂ) * 1) 0 a‖
            ≤ Cκ * ((if a = 0 then 1 else 0)
                + g ^ 2 * Real.exp (-cκ * (zdistD (k + 2) L a : ℝ))) := by
  rintro ⟨Cκ, hCκ, cκ, hcκ, h⟩
  have : NeZero 3 := ⟨by norm_num⟩
  -- the claimed bound sums to a constant, uniformly in `t`
  set M : ℝ := Cκ * (1 + g ^ 2 * expC k cκ) with hM
  have hM0 : 0 < M := by
    have : 0 ≤ expC k cκ := by
      unfold expC
      have : (0 : ℝ) < cκ ^ (k + 3) := by positivity
      positivity
    rw [hM]; positivity
  -- pick `t` so close to `1` that the row sum exceeds that constant
  set t : ℝ := 1 - 1 / (M + 2) with ht_def
  have hM2 : (0 : ℝ) < M + 2 := by linarith
  have ht0 : 0 ≤ t := by
    rw [ht_def]
    have : 1 / (M + 2) ≤ 1 := by
      rw [div_le_one hM2]; linarith
    linarith
  have ht1 : t < 1 := by
    rw [ht_def]
    have : 0 < 1 / (M + 2) := by positivity
    linarith
  have h1t : (1 : ℝ) - t = 1 / (M + 2) := by rw [ht_def]; ring
  -- the row sum of `Θ_t` at spectral parameter `1`
  have hξ : ‖((t : ℂ) * 1)‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]; exact ht1
  have hrow := sum_Theta_row_of_three_le (d := k + 2) (L := 3) (g := g) (by norm_num) hξ 0
  have hrow' : ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ = M + 2 := by
    rw [hrow, mul_one]
    have : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (by
      rw [h1t]; positivity)]
    rw [h1t, one_div, inv_inv]
  -- but the hypothesis bounds it by `M`
  have hsum_le : ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ ≤ M := by
    calc ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖
        ≤ ∑ b : Zd (k + 2) 3, ‖Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ := norm_sum_le _ _
      _ ≤ ∑ b : Zd (k + 2) 3, Cκ * ((if b = 0 then 1 else 0)
            + g ^ 2 * Real.exp (-cκ * (zdistD (k + 2) 3 b : ℝ))) :=
          Finset.sum_le_sum fun b _ => h 3 (by norm_num) t ht0 ht1 b
      _ = Cκ * (1 + g ^ 2 * ∑ b : Zd (k + 2) 3,
            Real.exp (-(cκ * (zdistD (k + 2) 3 b : ℝ)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 2
          · simp
          · exact congrArg _ (Finset.sum_congr rfl fun b _ => by ring_nf)
      _ ≤ M := by
          rw [hM]
          have hsum := sum_radial_exp_decay_le (L := 3) k hcκ
          have hg2 : (0 : ℝ) ≤ g ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left
            (by linarith [mul_le_mul_of_nonneg_left hsum hg2]) hCκ.le
  rw [hrow'] at hsum_le
  linarith

/-- **The zero-mode removal in `RBM.ThetaZeroMode` is essential.**  `(prop:ThfadC0)` is a
statement about `Θ̊_t`; the same bound for `Θ_t` itself is false at the spectral parameter
`1` -- the `σ₁ ≠ σ₂` case -- because the zero mode `(L^d|1-t|)⁻¹` that `Θ̊` subtracts off
is exactly what diverges as `t → 1`, while the right-hand side stays bounded. -/
theorem not_zeroMode_without_removal (k : ℕ) {g : ℝ} (hg : 0 < g) (τ : ℝ) :
    ¬ ∃ C > (0 : ℝ),
        ∀ (L : ℕ) (_ : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd (k + 2) L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta (k + 2) L g ((t : ℂ) * 1) 0 a‖
            ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
                * (((zdistD (k + 2) L a : ℝ) + 1) ^ (k + 2 - 2))⁻¹ := by
  rintro ⟨C, hC, h⟩
  have : NeZero 3 := ⟨by norm_num⟩
  have hL1 : (1 : ℝ) ≤ ((3 : ℕ) : ℝ) := by norm_num
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  set S : ℝ := Real.exp (Real.sqrt ((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1 * ((3 : ℕ) : ℝ) ^ 2)
    with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    have := radC_pos (one_pos : (0 : ℝ) < 1)
    have := Real.exp_pos (Real.sqrt ((k : ℝ) + 2))
    positivity
  set M : ℝ := C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2)⁻¹ * S with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (0 : ℝ) < ((3 : ℕ) : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set t : ℝ := 1 - 1 / (M + 2) with ht_def
  have hM2 : (0 : ℝ) < M + 2 := by linarith
  have ht0 : 0 ≤ t := by
    rw [ht_def]
    have : 1 / (M + 2) ≤ 1 := by rw [div_le_one hM2]; linarith
    linarith
  have ht1 : t < 1 := by
    rw [ht_def]
    have : 0 < 1 / (M + 2) := by positivity
    linarith
  have h1t : (1 : ℝ) - t = 1 / (M + 2) := by rw [ht_def]; ring
  have hξ : ‖((t : ℂ) * 1)‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]; exact ht1
  have hrow := sum_Theta_row_of_three_le (d := k + 2) (L := 3) (g := g) (by norm_num) hξ 0
  have hrow' : ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ = M + 2 := by
    rw [hrow, mul_one]
    have hcast : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (by
      rw [h1t]; positivity), h1t, one_div, inv_inv]
  have hsum_le : ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ ≤ M := by
    have habs : |1 - t| = 1 - t := abs_of_pos (by linarith)
    calc ‖∑ b : Zd (k + 2) 3, Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖
        ≤ ∑ b : Zd (k + 2) 3, ‖Theta (k + 2) 3 g ((t : ℂ) * 1) 0 b‖ := norm_sum_le _ _
      _ ≤ ∑ b : Zd (k + 2) 3, C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * (((zdistD (k + 2) 3 b : ℝ) + 1) ^ (k + 2 - 2))⁻¹ :=
          Finset.sum_le_sum fun b _ => h 3 (by norm_num) t ht0 ht1 b
      _ = C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * ∑ b : Zd (k + 2) 3, (((zdistD (k + 2) 3 b : ℝ) + 1) ^ k)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by norm_num
      _ ≤ C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2)⁻¹ * S := by
          have hmono : (g ^ 2 + |1 - t|)⁻¹ ≤ (g ^ 2)⁻¹ :=
            inv_anti₀ hg2 (by have := abs_nonneg (1 - t); linarith)
          have hpos : (0 : ℝ) < C * ((3 : ℕ) : ℝ) ^ τ := by
            have : (0 : ℝ) < ((3 : ℕ) : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) _
            positivity
          have hsum := sum_radial_pow_le (L := 3) k hL1
          calc C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
                * ∑ b : Zd (k + 2) 3, (((zdistD (k + 2) 3 b : ℝ) + 1) ^ k)⁻¹
              ≤ C * ((3 : ℕ) : ℝ) ^ τ * (g ^ 2)⁻¹ * S := by
                apply mul_le_mul (mul_le_mul_of_nonneg_left hmono hpos.le) hsum
                  (Finset.sum_nonneg fun b _ => by positivity)
                positivity
      _ = M := by rw [hM]
  rw [hrow'] at hsum_le
  linarith

/-! ## Positive half: certificates (`docs/QUEUE.md`, Q41)

The five components of `lem_propTH` cannot be proved here -- that is why the paper cites
them -- so a certificate has to be a weakening that is still not vacuous.  The one used
here is the ticket's:

> **fixed `L`**: replace `∃ C, ∀ L, …` by `∀ L, ∃ C, …`.

At a fixed `L` the torus is finite, so the entire content of the assumption is the
*uniformity in `L`*; a fixed-`L` proof therefore certifies the shape of the bound without
proving anything the paper borrows.  The weakening is exactly sharp enough to have caught
the defect of `docs/paper-deltas.md`, D11: the old property 5' fails already at `L = 3`
(`RBM.Test.not_decayShort_at_one` takes `L = 3`), so a fixed-`L` certificate for it could
never have been produced.

**What is certified, and what is not.**

* `ThetaDecay` -- certified (`thetaDecay_fixedL`).  Its right-hand side contains the
  zero-mode term `(L^d|1-t|)⁻¹` of `B_{t,K}`, which diverges as `t → 1` at the same rate
  as the crude bound `‖Θ_t‖_{∞→∞} ≤ (1-t)⁻¹`; that is what makes the fixed-`L` version
  provable, and `exists_norm_Theta_ge` shows the rate is attained, so the term is not
  decoration.
* `TwoLoopBounded` -- certified (`twoLoopBounded_kTwoLoop`), and not by a weakening: the
  explicit two-loop of `(Kn2sol)` satisfies it outright.
* `ThetaDecayShort`, `ThetaDiffOne`, `ThetaDiffTwo`, `ThetaZeroMode` -- **not certified.**
  Their right-hand sides stay bounded as `t → 1` at fixed `L`, while individual entries of
  `Θ_t` do not (`not_exists_uniform_entry_bound`).  A fixed-`L` proof would therefore have
  to exhibit a cancellation: the difference of two entries, or the removal of the zero
  mode.  At fixed `L` that cancellation is the statement that `1` is a *simple* eigenvalue
  of `S^(B)` -- a finite-`L` spectral gap -- which this development does not have.  This
  is a positive, self-contained work order rather than a borrowing (`docs/QUEUE.md`, Q51).

  What *is* checked here is that the refutation which killed the old property 5' cannot be
  run against these four: it went through the row sum, and the row sums of the
  zero-mode-removed propagator and of every first difference are `0`
  (`RBM.sum_Theta0_row`, `sum_Theta_diff_row` below).
* `KTreeRep` -- **not certified**, and the honest certificate is not cheap: exhibiting
  *some* `K` with `KTreeRep m K` is possible by taking the tree formula itself as the
  definition of `K`, but that witness says nothing, because the premise is only ever used
  together with `IsKLoop`.  The certificate that matters is a `K` satisfying **both**,
  which is the existence half of `(eq_Ktree)` -- Q30, Q31.
-/

open Finset

/-- **Certificate for `RBM.ThetaDecay` (`(prop:ThfadC)`), fixed `L`.**  The bound of
property 5 holds at each fixed `L`, with a constant depending on `L`; the assumption's
content is the uniformity in `L`, and this says the shape is not vacuous.

The proof is the crude row bound `‖Θ_t‖_{∞→∞} ≤ (1-t)⁻¹` against the zero-mode term
`(L^d|1-t|)⁻¹` of `B_{t,K}`: the two diverge at the same rate as `t → 1`, and the
exponential factor costs only `exp(R_L)`, since `ℓ_t ≥ 1`. -/
theorem thetaDecay_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {m : ℂ} (hm : ‖m‖ = 1) :
    ∃ Cd > (0 : ℝ), ∃ cd > (0 : ℝ),
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
        ‖Theta d L g ((t : ℂ) * m) 0 a‖
          ≤ Cd * Bparam d L g t (zdistD d L a)
              * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℕ) < L := by omega
    exact_mod_cast this
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    have : (1 : ℕ) ≤ L := by omega
    exact_mod_cast this
  refine ⟨(L : ℝ) ^ d * Real.exp (torusDiam d L), by positivity, 1, one_pos, ?_⟩
  intro t ht0 ht1 a
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hentry : ‖Theta d L g ((t : ℂ) * m) 0 a‖ ≤ (1 - t)⁻¹ := by
    refine le_trans ?_ (sum_norm_Theta_row_le (d := d) (L := L) (g := g) hL ht0 ht1 hm 0)
    exact Finset.single_le_sum (f := fun b => ‖Theta d L g ((t : ℂ) * m) 0 b‖)
      (fun b _ => norm_nonneg _) (Finset.mem_univ a)
  have hell : (1 : ℝ) ≤ ellT L g t := one_le_ellT hL1
  have hexp : Real.exp (-(torusDiam d L : ℝ))
      ≤ Real.exp (-1 * (zdistD d L a : ℝ) / ellT L g t) := by
    refine Real.exp_le_exp.mpr ?_
    have hd : (zdistD d L a : ℝ) ≤ (torusDiam d L : ℝ) := by
      exact_mod_cast zdistD_le_torusDiam d L a
    have hdiv : (zdistD d L a : ℝ) / ellT L g t ≤ (zdistD d L a : ℝ) :=
      div_le_self (by positivity) hell
    have hneg : -1 * (zdistD d L a : ℝ) / ellT L g t = -((zdistD d L a : ℝ) / ellT L g t) := by
      ring
    rw [hneg]
    linarith
  have hB : ((L : ℝ) ^ d * (1 - t))⁻¹ ≤ Bparam d L g t (zdistD d L a) := by
    have habs : |1 - t| = 1 - t := abs_of_pos h1t
    have hfirst : (0 : ℝ) ≤ (g ^ 2 + (1 - t))⁻¹
        * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    unfold Bparam
    rw [habs]
    linarith
  calc ‖Theta d L g ((t : ℂ) * m) 0 a‖
      ≤ (1 - t)⁻¹ := hentry
    _ = ((L : ℝ) ^ d * Real.exp (torusDiam d L)) * ((L : ℝ) ^ d * (1 - t))⁻¹
          * Real.exp (-(torusDiam d L : ℝ)) := by
        rw [Real.exp_neg]
        field_simp
    _ ≤ ((L : ℝ) ^ d * Real.exp (torusDiam d L)) * Bparam d L g t (zdistD d L a)
          * Real.exp (-1 * (zdistD d L a : ℝ) / ellT L g t) := by
        have h1 : (0 : ℝ) ≤ (L : ℝ) ^ d * Real.exp (torusDiam d L) := by positivity
        have hBnn : (0 : ℝ) ≤ ((L : ℝ) ^ d * (1 - t))⁻¹ := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB h1) hexp (Real.exp_pos _).le
          (mul_nonneg h1 (le_trans hBnn hB))

/-- **The divergence in `(prop:ThfadC)` is attained.**  Some entry of the row is at least
`L^{-d}(1-t)⁻¹`: the rows sum to `(1-t)⁻¹` over `L^d` points.  So the zero-mode term of
`B_{t,K}` is not slack in the certificate above -- drop it and the bound is false. -/
theorem exists_norm_Theta_ge (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ a : Zd d L, ((L : ℝ) ^ d * (1 - t))⁻¹ ≤ (Theta d L g t 0 a).re := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℕ) < L := by omega
    exact_mod_cast this
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hsum : ∑ b : Zd d L, (Theta d L g t 0 b).re = (1 - t)⁻¹ :=
    sum_Theta_real_row (d := d) (L := L) (g := g) hL ht0 ht1 0
  by_contra hcon
  push Not at hcon
  have hne : (Finset.univ : Finset (Zd d L)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hlt : ∑ b : Zd d L, (Theta d L g t 0 b).re < ∑ b : Zd d L, ((L : ℝ) ^ d * (1 - t))⁻¹ :=
    Finset.sum_lt_sum_of_nonempty hne fun b _ => hcon b
  have hconst : ∑ _b : Zd d L, ((L : ℝ) ^ d * (1 - t))⁻¹ = (1 - t)⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, RBM.card_Zd, nsmul_eq_mul, Nat.cast_pow]
    field_simp
  rw [hconst, hsum] at hlt
  exact lt_irrefl _ hlt

/-- **Why the other four have no fixed-`L` certificate yet.**  At the spectral parameter
`1` -- the `σ₁ ≠ σ₂` case -- no bound uniform in `t` holds for the entries of `Θ_t`, at any
fixed `L`.  The right-hand sides of `(prop:ThfadC_short)`, `(prop:BD1)`, `(prop:BD2)` and
`(prop:ThfadC0)` are all bounded in `t` once `L` is fixed, so each of them needs a
*cancellation*, not just a size bound. -/
theorem not_exists_uniform_entry_bound (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) :
    ¬ ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
        ‖Theta d L g ((t : ℂ) * 1) 0 a‖ ≤ C := by
  rintro ⟨C, hC⟩
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℕ) < L := by omega
    exact_mod_cast this
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hM : (0 : ℝ) < (|C| + 1) * (L : ℝ) ^ d := by positivity
  set t : ℝ := 1 - ((|C| + 1) * (L : ℝ) ^ d)⁻¹ with ht_def
  have hinv_le : ((|C| + 1) * (L : ℝ) ^ d)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hM]
    have h1 : (1 : ℝ) ≤ |C| + 1 := by have := abs_nonneg C; linarith
    have h2 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by
      have : (1 : ℕ) ≤ L := by omega
      exact_mod_cast this)
    nlinarith
  have ht0 : 0 ≤ t := by rw [ht_def]; linarith
  have ht1 : t < 1 := by
    rw [ht_def]
    have : (0 : ℝ) < ((|C| + 1) * (L : ℝ) ^ d)⁻¹ := by positivity
    linarith
  have h1t : 1 - t = ((|C| + 1) * (L : ℝ) ^ d)⁻¹ := by rw [ht_def]; ring
  obtain ⟨a, ha⟩ := exists_norm_Theta_ge d L hL g ht0 ht1
  have hval : ((L : ℝ) ^ d * (1 - t))⁻¹ = |C| + 1 := by
    rw [h1t]; field_simp
  have hre : (Theta d L g t 0 a).re ≤ ‖Theta d L g ((t : ℂ) * 1) 0 a‖ := by
    rw [mul_one]
    exact Complex.re_le_norm _
  have hCa := hC t ht0 ht1 a
  rw [hval] at ha
  have hfin : |C| + 1 ≤ C := le_trans ha (le_trans hre hCa)
  have := le_abs_self C
  linarith

/-- **The row-sum refutation cannot be run against `(prop:BD1)` or `(prop:BD2)`.**  Every
first difference of a row of `Θ` sums to zero, so the argument that refutes the old
property 5' -- compare the row sum with the sum of the claimed bound -- gives `0 ≤ …` and
no contradiction.  For `(prop:ThfadC0)` the same role is played by `RBM.sum_Theta0_row`. -/
theorem sum_Theta_diff_row (d L : ℕ) [NeZero L] {g : ℝ} {ξ : ℂ} (a r : Zd d L) :
    ∑ b : Zd d L, (Theta d L g ξ a (b + r) - Theta d L g ξ a b) = 0 := by
  rw [Finset.sum_sub_distrib, sum_Theta_shift, sub_self]

/-- **Certificate for `RBM.ThetaZeroMode` (`(prop:ThfadC0)`), fixed `L`.**  Property 8
holds at each fixed `L`, with a constant depending on `L`.

Unlike `thetaDecay_fixedL`, this one cannot come from a size bound: the right-hand side
stays bounded as `t → 1` while the entries of `Θ_t` do not
(`not_exists_uniform_entry_bound`).  What supplies it is the cancellation
`RBM.exists_norm_Theta0_le`: removing the zero mode leaves
`Θ̊_ξ = Σ_k ξ^k ((S^(B))^k - P)`, and `S^(B)` mixes geometrically at fixed `L`
(`RBM.exists_mixing`), so the series converges at a rate independent of `ξ`.  Everything
else on the right-hand side is bounded below at fixed `L`: `L^τ ≥ 1`,
`(g²+|1-t|)⁻¹ ≥ (g²+1)⁻¹`, and `(|a|+1)^{-(d-2)} ≥ (R_L+1)^{-(d-2)}`. -/
theorem thetaZeroMode_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g)
    {m : ℂ} (hm : ‖m‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
      ‖Theta0 d L g ((t : ℂ) * m) 0 a‖
        ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_Theta0_le (d := d) (L := L) (g := g) hL hg
  set D : ℝ := ((torusDiam d L : ℝ) + 1) ^ (d - 2) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  have hgpos : (0 : ℝ) < g ^ 2 + 1 := by positivity
  refine ⟨C₀ * (g ^ 2 + 1) * D + 1, by positivity, ?_⟩
  intro t ht0 ht1 a
  have hξ : ‖(t : ℂ) * m‖ < 1 := norm_t_mul_lt_one ht0 ht1 hm
  have hmain : ‖Theta0 d L g ((t : ℂ) * m) 0 a‖ ≤ C₀ := hC₀ _ hξ 0 a
  -- every factor on the right is bounded below at fixed `L`
  have hLrpow : (1 : ℝ) ≤ (L : ℝ) ^ τ := by
    refine Real.one_le_rpow ?_ hτ
    have : (1 : ℕ) ≤ L := by omega
    exact_mod_cast this
  have habs : |1 - t| ≤ 1 := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hX : (g ^ 2 + 1)⁻¹ ≤ (g ^ 2 + |1 - t|)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have hY : D⁻¹ ≤ (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    rw [hD]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (zdistD d L a : ℕ) ≤ torusDiam d L := zdistD_le_torusDiam d L a
    have : ((zdistD d L a : ℕ) : ℝ) ≤ (torusDiam d L : ℝ) := by exact_mod_cast this
    linarith
  have hsplit : (C₀ * (g ^ 2 + 1) * D + 1) * (g ^ 2 + 1)⁻¹ * D⁻¹
      = C₀ + ((g ^ 2 + 1) * D)⁻¹ := by
    field_simp
  have hlow : C₀ ≤ (C₀ * (g ^ 2 + 1) * D + 1) * (g ^ 2 + 1)⁻¹ * D⁻¹ := by
    rw [hsplit]
    have : (0 : ℝ) < ((g ^ 2 + 1) * D)⁻¹ := by positivity
    linarith
  refine le_trans hmain (le_trans hlow ?_)
  have hC1 : (0 : ℝ) ≤ C₀ * (g ^ 2 + 1) * D + 1 := by positivity
  calc (C₀ * (g ^ 2 + 1) * D + 1) * (g ^ 2 + 1)⁻¹ * D⁻¹
      ≤ (C₀ * (g ^ 2 + 1) * D + 1) * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ * D⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (C₀ * (g ^ 2 + 1) * D + 1) * (g ^ 2 + 1)⁻¹
            ≤ (C₀ * (g ^ 2 + 1) * D + 1) * (g ^ 2 + |1 - t|)⁻¹ :=
              mul_le_mul_of_nonneg_left hX hC1
          _ ≤ (C₀ * (g ^ 2 + 1) * D + 1) * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              nlinarith [hLrpow, hC1]
    _ ≤ (C₀ * (g ^ 2 + 1) * D + 1) * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
          * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by
        refine mul_le_mul_of_nonneg_left hY ?_
        have : (0 : ℝ) ≤ (L : ℝ) ^ τ := by positivity
        positivity

/-- **Certificate for `RBM.ThetaDiffOne` (`(prop:BD1)`), fixed `L`.**  Property 6 holds at
each fixed `L`, with a constant depending on `L`.

Like property 8 and unlike property 5, this needs a cancellation rather than a size bound,
and it is the same one: a difference kills the constant mode, so the geometric mixing of
`S^(B)` bounds `Θ_t(0,a+r) - Θ_t(0,a)` uniformly in `t` (`RBM.exists_norm_Theta_sub_le`).

`r = 0` is a separate case, and not a formality: there the right-hand side is `0`, because
of its factor `|r|`.  The bound still holds -- the left-hand side is `0` too -- but no
estimate can give it; only the algebra can. -/
theorem thetaDiffOne_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g)
    {m : ℂ} (hm : ‖m‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L,
      ‖Theta d L g ((t : ℂ) * m) 0 (a + r) - Theta d L g ((t : ℂ) * m) 0 a‖
        ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_Theta_sub_le (d := d) (L := L) (g := g) hL hg
  set D : ℝ := ((torusDiam d L : ℝ) + 1) ^ (d - 1) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  refine ⟨C₀ * (g ^ 2 + 1) * D + 1, by positivity, ?_⟩
  intro t ht0 ht1 a r
  have hξ : ‖(t : ℂ) * m‖ < 1 := norm_t_mul_lt_one ht0 ht1 hm
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- both sides vanish
    rw [hr0, add_zero, sub_self, norm_zero, zdistD_zero]
    simp
  · have hr1 : (1 : ℝ) ≤ (zdistD d L r : ℝ) := by
      have : zdistD d L r ≠ 0 := fun h => hr0 ((zdistD_eq_zero_iff d L).mp h)
      have : 1 ≤ zdistD d L r := by omega
      exact_mod_cast this
    have hmain : ‖Theta d L g ((t : ℂ) * m) 0 (a + r) - Theta d L g ((t : ℂ) * m) 0 a‖ ≤ C₀ :=
      hC₀ _ hξ 0 (a + r) a
    refine le_trans hmain ?_
    have hLrpow : (1 : ℝ) ≤ (L : ℝ) ^ τ := by
      refine Real.one_le_rpow ?_ hτ
      have : (1 : ℕ) ≤ L := by omega
      exact_mod_cast this
    have habs : |1 - t| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
    have hY : D⁻¹ ≤ (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      rw [hD]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have h := zdistD_le_torusDiam d L a
      have : ((zdistD d L a : ℕ) : ℝ) ≤ (torusDiam d L : ℝ) := by exact_mod_cast h
      linarith
    have hsplit : (C₀ * (g ^ 2 + 1) * D + 1) * (g ^ 2 + 1)⁻¹ * D⁻¹
        = C₀ + ((g ^ 2 + 1) * D)⁻¹ := by field_simp
    calc C₀ ≤ (C₀ * (g ^ 2 + 1) * D + 1) * 1 * (g ^ 2 + 1)⁻¹ * 1 * D⁻¹ := by
          rw [mul_one, mul_one, hsplit]
          have : (0 : ℝ) < ((g ^ 2 + 1) * D)⁻¹ := by positivity
          linarith
      _ ≤ (C₀ * (g ^ 2 + 1) * D + 1) * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by
          gcongr

/-- **Certificate for `RBM.ThetaDiffTwo` (`(prop:BD2)`), fixed `L`.**  Property 7 at fixed
`L`, from the same bound applied twice: the second difference is
`(Θ(0,a+r) - Θ(0,a)) + (Θ(0,a-r) - Θ(0,a))`. -/
theorem thetaDiffTwo_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g)
    {m : ℂ} (hm : ‖m‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L,
      ‖Theta d L g ((t : ℂ) * m) 0 (a + r) + Theta d L g ((t : ℂ) * m) 0 (a - r)
          - 2 * Theta d L g ((t : ℂ) * m) 0 a‖
        ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_Theta_sub_le (d := d) (L := L) (g := g) hL hg
  set D : ℝ := ((torusDiam d L : ℝ) + 1) ^ d with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  refine ⟨2 * C₀ * (g ^ 2 + 1) * D + 1, by positivity, ?_⟩
  intro t ht0 ht1 a r
  have hξ : ‖(t : ℂ) * m‖ < 1 := norm_t_mul_lt_one ht0 ht1 hm
  rcases eq_or_ne r 0 with hr0 | hr0
  · have hz : (zdistD d L r : ℝ) = 0 := by rw [hr0, zdistD_zero]; norm_num
    have hzero : Theta d L g ((t : ℂ) * m) 0 (a + r) + Theta d L g ((t : ℂ) * m) 0 (a - r)
        - 2 * Theta d L g ((t : ℂ) * m) 0 a = 0 := by
      rw [hr0, add_zero, sub_zero]
      ring
    rw [hzero, norm_zero, hz]
    norm_num
  · have hr1 : (1 : ℝ) ≤ (zdistD d L r : ℝ) ^ 2 := by
      have hne : zdistD d L r ≠ 0 := fun h => hr0 ((zdistD_eq_zero_iff d L).mp h)
      have h1 : 1 ≤ zdistD d L r := by omega
      have : (1 : ℝ) ≤ (zdistD d L r : ℝ) := by exact_mod_cast h1
      nlinarith
    have hmain : ‖Theta d L g ((t : ℂ) * m) 0 (a + r) + Theta d L g ((t : ℂ) * m) 0 (a - r)
        - 2 * Theta d L g ((t : ℂ) * m) 0 a‖ ≤ 2 * C₀ := by
      have hsplit : Theta d L g ((t : ℂ) * m) 0 (a + r) + Theta d L g ((t : ℂ) * m) 0 (a - r)
          - 2 * Theta d L g ((t : ℂ) * m) 0 a
          = (Theta d L g ((t : ℂ) * m) 0 (a + r) - Theta d L g ((t : ℂ) * m) 0 a)
            + (Theta d L g ((t : ℂ) * m) 0 (a - r) - Theta d L g ((t : ℂ) * m) 0 a) := by
        ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have h1 := hC₀ _ hξ 0 (a + r) a
      have h2 := hC₀ _ hξ 0 (a - r) a
      linarith
    refine le_trans hmain ?_
    have hLrpow : (1 : ℝ) ≤ (L : ℝ) ^ τ := by
      refine Real.one_le_rpow ?_ hτ
      have : (1 : ℕ) ≤ L := by omega
      exact_mod_cast this
    have habs : |1 - t| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
    have hY : D⁻¹ ≤ (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      rw [hD]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have h := zdistD_le_torusDiam d L a
      have : ((zdistD d L a : ℕ) : ℝ) ≤ (torusDiam d L : ℝ) := by exact_mod_cast h
      linarith
    have hsplit : (2 * C₀ * (g ^ 2 + 1) * D + 1) * (g ^ 2 + 1)⁻¹ * D⁻¹
        = 2 * C₀ + ((g ^ 2 + 1) * D)⁻¹ := by field_simp
    calc 2 * C₀ ≤ (2 * C₀ * (g ^ 2 + 1) * D + 1) * 1 * (g ^ 2 + 1)⁻¹ * 1 * D⁻¹ := by
          rw [mul_one, mul_one, hsplit]
          have : (0 : ℝ) < ((g ^ 2 + 1) * D)⁻¹ := by positivity
          linarith
      _ ≤ (2 * C₀ * (g ^ 2 + 1) * D + 1) * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
            * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by
          gcongr

/-- **Certificate for `RBM.PropTH`, fixed `L`.**  The bundle is the conjunction of its
four fields, so this is the conjunction of their fixed-`L` certificates and carries no
information the three theorems above do not.  It is stated because the audit asks the
question premise by premise, and `PropTH` is a premise: a bundle whose fields are
separately satisfiable is satisfiable, and saying so once is cheaper than explaining each
time why the row is empty. -/
theorem propTH_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g)
    {m : ℂ} (hm : ‖m‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (∃ Cd > (0 : ℝ), ∃ cd > (0 : ℝ),
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
          ‖Theta d L g ((t : ℂ) * m) 0 a‖
            ≤ Cd * Bparam d L g t (zdistD d L a)
                * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t))
      ∧ (∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L,
          ‖Theta d L g ((t : ℂ) * m) 0 (a + r) - Theta d L g ((t : ℂ) * m) 0 a‖
            ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
                * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹)
      ∧ (∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L,
          ‖Theta d L g ((t : ℂ) * m) 0 (a + r) + Theta d L g ((t : ℂ) * m) 0 (a - r)
              - 2 * Theta d L g ((t : ℂ) * m) 0 a‖
            ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
                * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹)
      ∧ (∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
          ‖Theta0 d L g ((t : ℂ) * m) 0 a‖
            ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
                * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) :=
  ⟨thetaDecay_fixedL d L hL g hm, thetaDiffOne_fixedL d L hL g hg hm hτ,
    thetaDiffTwo_fixedL d L hL g hg hm hτ, thetaZeroMode_fixedL d L hL g hg hm hτ⟩

/-- **Certificate for `RBM.Loop.TwoLoopBounded`**, and not by a weakening: the explicit
two-loop of `(Kn2sol)` satisfies it, with the bound `W^{-d}(1-T₀)⁻¹` of
`RBM.Loop.norm_kTwo_le`.

This is the certificate in the sense `RBM.Loop.kTwoFormula_kTwoLoop` set: the premise is
satisfied by an object this development builds, so a theorem carrying it is not vacuous.
`TwoLoopBounded` is an *owed* premise -- the paper obtains it along the way -- and what is
missing is only its a priori form, for a family of `K`-loops not yet known to be this
solution. -/
theorem twoLoopBounded_kTwoLoop {d L W : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L)
    {m : Bool → ℂ} (hm : ∀ s, ‖m s‖ = 1) :
    RBM.Loop.TwoLoopBounded d L (RBM.Loop.kTwoLoop d L W g m) := by
  intro T₀ hT₀
  refine ⟨‖((W : ℂ) ^ d)⁻¹‖ * (1 - T₀)⁻¹, by positivity, ?_⟩
  intro t ht I hI h2
  obtain ⟨σ₁, σ₂, a₁, a₂, rfl⟩ := RBM.Loop.exists_eq_of_length_two hI h2
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
  have hmono : (1 - t)⁻¹ ≤ (1 - T₀)⁻¹ :=
    inv_anti₀ (by linarith) (by linarith [ht.2])
  exact le_trans (RBM.Loop.norm_kTwo_le hL (hm σ₁) (hm σ₂) ht.1 ht1 a₁ a₂)
    (mul_le_mul_of_nonneg_left hmono (norm_nonneg _))

end RBM.Test
