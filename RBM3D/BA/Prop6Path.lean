/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Prop5
import RBM3D.BA.PropUnit
import RBM3D.BA.Prop5Short
import RBM3D.BA.FlowPins

/-!
# Properties 5-8 of `lem_propTH` for `Θ_BA`, all charge pairs, and the bundle (BA-P8)

Ticket T2357.  Targets `baProp5_holds`, `baProp6_holds`, `baProp7_holds`, `baProp8_holds`,
`baProp5to8_holds` (the pins `BAProp5`, `BAProp6`, `BAProp7`, `BAProp8`, `BAProp5to8` of
`BA/FlowPins.lean:171-236`, for every `(d, Λ, κ, c)`), from the merged inputs

* `σ₁ ≠ σ₂`: `baProp5mixed_holds`, `baProp8mixed_holds` (`BA/Prop5.lean`), and the unit differences
  `baPropUnit1mixed_holds`, `baPropUnit2mixed_holds` (`BA/PropUnit.lean`) together with the **path
  argument** of `Propagator/Prop6Hold.lean:43-350` (`Θ ↦ BATheta d L g E m t σ₁ σ₂ 0 ·`),
  whose private lemmas are copied here under the prefix `baP8_` (`p6h_tri ↦ baP8_tri`,
  `p6hQ ↦ baP8_Q`, ...; no change beyond the renaming);
* `σ₁ = σ₂`: all four properties from `baProp5s_holds` (`|Θ_t(0,a)| ≤ C (1_{a=0} + g² e^{-c'|a|})`,
  the paper's "follow directly", `A:50`):

  - (5) `1_{a=0} + g² e^{-c'|a|} ≤ C B_{t,|a|} e^{-c|a|/ℓ_t}` with `c ≤ c'/2`, `ℓ_t ≥ 1`
    (`one_le_ellT`), `g ≤ Λ`, and `B_{t,K} ≥ (g²+|1-t|)⁻¹ (K+1)^{-(d-2)}`;
  - (6), (7): `a = 0` forces `r = 0`; if `a ≠ 0`, `|a±r| ≥ (1-c)|a| > 0` (`zdistD_add_le`), so every
    value is `≤ C g² e^{-c'(1-c)|a|}`, `g² ≤ Λ²(Λ²+1)(g²+|1-t|)⁻¹`, `|r| ≥ 1` for `r ≠ 0`, and
    `e^{-x n} ≤ S (n+1)^{-m}`;
  - (8): translation invariance gives `L^{-2d} Σ Σ Θ(a',b') = L^{-d} Σ_b Θ(0,b)`, whose norm is
    `≤ L^{-d} C (1+g² Σ_b e^{-c'|b|})` (`BAsum_exp_decay_le`), `L^{-d} ≤ (d+1)^{d-2} (|a|+1)^{2-d}`
    from `|a| ≤ d L` (`zdistD_le`).  Translation invariance of `BATheta` is not merged: it is
    re-derived from `BAMB_shift` (`BA/Ward.lean:53`).

Constants depend on `(d, Λ, κ)` (`(d, Λ, κ, c)` for 6, 7) only, fixed before `L, g, E, m, t`.  No
unproved input.  Private helpers carry the prefix `baP8_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The path argument (private band lemmas of `Propagator/Prop6Hold.lean:45-350`, copied) -/

section PathLemmas

variable {d L : ℕ} [NeZero L]

/-- `|a| ≤ |z| + |z - a|`. -/
private lemma baP8_tri (a z : Zd d L) :
    zdistD d L a ≤ zdistD d L z + zdistD d L (z - a) := by
  have h := zdistD_add_le d L z (a - z)
  have e1 : z + (a - z) = a := by abel
  have e2 : zdistD d L (a - z) = zdistD d L (z - a) := by rw [← neg_sub z a, zdistD_neg]
  rw [e1, e2] at h
  exact h

/-- **The path lemma.**  If every unit step between two good points changes `G` by at most `B`,
then `G(a + r) - G(a)` is at most `|r| B` whenever every point within `|r|` of `a` is good. -/
private theorem baP8_path (hL : 3 ≤ L) (G : Zd d L → ℂ) (P : Zd d L → Prop) (B : ℝ)
    (hU : ∀ x e : Zd d L, zdistD d L e = 1 → P x → P (x + e) → ‖G (x + e) - G x‖ ≤ B) :
    ∀ (n : ℕ) (r a : Zd d L), zdistD d L r = n → (∀ z, zdistD d L (z - a) ≤ n → P z) →
      ‖G (a + r) - G a‖ ≤ n * B := by
  intro n
  induction n with
  | zero =>
    intro r a hr _
    have h0 : r = 0 := (zdistD_eq_zero_iff d L).mp hr
    subst h0
    simp
  | succ n ih =>
    intro r a hr hP
    have hr0 : r ≠ 0 := by
      intro h
      subst h
      simp at hr
    obtain ⟨e, he, hre⟩ := exists_step hL hr0
    have hr' : zdistD d L (r - e) = n := by omega
    have hih := ih (r - e) a hr' (fun z hz => hP z (by omega))
    have h1 : zdistD d L (a + (r - e) - a) = n := by
      rw [add_sub_cancel_left]
      exact hr'
    have h2 : zdistD d L (a + (r - e) + e - a) = n + 1 := by
      have : a + (r - e) + e - a = r := by abel
      rw [this, hr]
    have hstep := hU (a + (r - e)) e he (hP _ (by rw [h1]; omega)) (hP _ (by rw [h2]))
    have hsplit : G (a + r) - G a
        = (G (a + (r - e) + e) - G (a + (r - e))) + (G (a + (r - e)) - G a) := by
      have : a + (r - e) + e = a + r := by abel
      rw [this]
      ring
    rw [hsplit]
    calc ‖(G (a + (r - e) + e) - G (a + (r - e))) + (G (a + (r - e)) - G a)‖
        ≤ ‖G (a + (r - e) + e) - G (a + (r - e))‖ + ‖G (a + (r - e)) - G a‖ :=
          norm_add_le _ _
      _ ≤ B + n * B := add_le_add hstep hih
      _ = ((n + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- The unit differences of `f` (forward steps `+e_j` only) give the bound at every unit step
`±e_j`, at any lower bound `M ≤ |x|, |x + e|`. -/
private theorem baP8_unit (hL : 3 ≤ L) (f : Zd d L → ℂ) (K : ℝ) (hK : 0 ≤ K) (p : ℕ)
    (hU : ∀ (x : Zd d L) (j : Fin d),
      ‖f (x + Pi.single j 1) - f x‖ ≤ K * (((zdistD d L x : ℝ) + 1) ^ p)⁻¹)
    (M : ℝ) (hM : 0 ≤ M) (x e : Zd d L) (he : zdistD d L e = 1)
    (hx : M ≤ (zdistD d L x : ℝ)) (hxe : M ≤ (zdistD d L (x + e) : ℝ)) :
    ‖f (x + e) - f x‖ ≤ K * ((M + 1) ^ p)⁻¹ := by
  have mono : ∀ y : Zd d L, M ≤ (zdistD d L y : ℝ) →
      K * (((zdistD d L y : ℝ) + 1) ^ p)⁻¹ ≤ K * ((M + 1) ^ p)⁻¹ := by
    intro y hy
    refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hK
    exact pow_le_pow_left₀ (by linarith) (by linarith) p
  obtain ⟨⟨j, b⟩, rfl⟩ := exists_unitVec_of_zdistD_eq_one hL he
  cases b
  · have h := hU (x + unitVec d L (j, false)) j
    have hxe' : x + unitVec d L (j, false) + Pi.single j 1 = x := by
      simp [unitVec, Pi.single_neg]
    rw [hxe', norm_sub_rev] at h
    exact h.trans (mono _ hxe)
  · have hu : unitVec d L (j, true) = Pi.single j 1 := by simp [unitVec]
    rw [hu]
    exact (hU x j).trans (mono _ hx)

/-- **P6 core.**  `|f(a + r) - f(a)| ≤ |r| K ((M+1)^p)⁻¹` when `|r| + M ≤ |a|`. -/
private theorem baP8_bound (hL : 3 ≤ L) (f : Zd d L → ℂ) (K : ℝ) (hK : 0 ≤ K) (p : ℕ)
    (hU : ∀ (x : Zd d L) (j : Fin d),
      ‖f (x + Pi.single j 1) - f x‖ ≤ K * (((zdistD d L x : ℝ) + 1) ^ p)⁻¹)
    (M : ℝ) (hM : 0 ≤ M) (a r : Zd d L)
    (hr : (zdistD d L r : ℝ) + M ≤ (zdistD d L a : ℝ)) :
    ‖f (a + r) - f a‖ ≤ (zdistD d L r : ℝ) * (K * ((M + 1) ^ p)⁻¹) := by
  refine baP8_path hL f (fun z => M ≤ (zdistD d L z : ℝ)) (K * ((M + 1) ^ p)⁻¹) ?_
    (zdistD d L r) r a rfl ?_
  · intro x e he hx hxe
    exact baP8_unit hL f K hK p hU M hM x e he hx hxe
  · intro z hz
    have h : (zdistD d L a : ℝ) ≤ zdistD d L z + zdistD d L (z - a) := by
      exact_mod_cast baP8_tri a z
    have hz' : (zdistD d L (z - a) : ℝ) ≤ zdistD d L r := by exact_mod_cast hz
    change M ≤ (zdistD d L z : ℝ)
    linarith

/-! ### The second difference `Q f x u e` and the sign shifts -/

/-- `f(x+u+e) - f(x+u) - f(x+e) + f(x)`: the second difference with increments `u`, `e` at `x`. -/
private def baP8_Q (f : Zd d L → ℂ) (x u e : Zd d L) : ℂ :=
  f (x + u + e) - f (x + u) - f (x + e) + f x

omit [NeZero L] in
private lemma baP8_Q_comm (f : Zd d L → ℂ) (x u e : Zd d L) :
    baP8_Q f x u e = baP8_Q f x e u := by
  unfold baP8_Q
  rw [add_right_comm x u e]
  ring

omit [NeZero L] in
/-- `D_{-v} D_e f (x) = - D_v D_e f (x - v)`. -/
private lemma baP8_Q_neg_left (f : Zd d L → ℂ) (x v e : Zd d L) :
    baP8_Q f x (-v) e = - baP8_Q f (x - v) v e := by
  unfold baP8_Q
  have h1 : x - v + v + e = x + e := by abel
  have h2 : x - v + v = x := by abel
  have h3 : x - v + e = x + -v + e := by abel
  have h4 : x - v = x + -v := by abel
  rw [h1, h2, h3, h4]
  ring

/-- The unit second differences `Q(x, e_i, e_j)` give `Q(x, u, e)` for all units `u, e = ±e_j`
at a base point within `2` of `x`, up to sign. -/
private theorem baP8_reduce (hL : 3 ≤ L) (f : Zd d L → ℂ) (x u e : Zd d L)
    (hu : zdistD d L u = 1) (he : zdistD d L e = 1) :
    ∃ (x' : Zd d L) (i j : Fin d), zdistD d L (x' - x) ≤ 2 ∧
      ‖baP8_Q f x u e‖ = ‖baP8_Q f x' (Pi.single i 1) (Pi.single j 1)‖ := by
  obtain ⟨⟨i, bi⟩, rfl⟩ := exists_unitVec_of_zdistD_eq_one hL hu
  obtain ⟨⟨j, bj⟩, rfl⟩ := exists_unitVec_of_zdistD_eq_one hL he
  have eT : ∀ k : Fin d, unitVec d L (k, true) = Pi.single k 1 := by
    intro k; simp [unitVec]
  have eF : ∀ k : Fin d, unitVec d L (k, false) = -Pi.single k 1 := by
    intro k; simp [unitVec, Pi.single_neg]
  have hv : ∀ k : Fin d, zdistD d L (Pi.single k (1 : ZMod L)) = 1 := fun k => by
    have := zdistD_unitVec (d := d) (L := L) hL (k, true)
    rwa [eT] at this
  cases bi <;> cases bj
  · -- `u = -e_i`, `e = -e_j`
    refine ⟨x - Pi.single i 1 - Pi.single j 1, i, j, ?_, ?_⟩
    · have : x - Pi.single i 1 - Pi.single j 1 - x = -(Pi.single i 1 + Pi.single j 1) := by abel
      rw [this, zdistD_neg]
      calc zdistD d L (Pi.single i 1 + Pi.single j 1)
          ≤ zdistD d L (Pi.single i 1) + zdistD d L (Pi.single j 1) := zdistD_add_le d L _ _
        _ = 2 := by rw [hv, hv]
    · rw [eF, eF, baP8_Q_neg_left, baP8_Q_comm f (x - Pi.single i 1) (Pi.single i 1)
        (-Pi.single j 1), baP8_Q_neg_left, norm_neg, norm_neg, baP8_Q_comm]
  · -- `u = -e_i`, `e = +e_j`
    refine ⟨x - Pi.single i 1, i, j, ?_, ?_⟩
    · have : x - Pi.single i 1 - x = -Pi.single i 1 := by abel
      rw [this, zdistD_neg, hv]
      omega
    · rw [eF, eT, baP8_Q_neg_left, norm_neg]
  · -- `u = +e_i`, `e = -e_j`
    refine ⟨x - Pi.single j 1, i, j, ?_, ?_⟩
    · have : x - Pi.single j 1 - x = -Pi.single j 1 := by abel
      rw [this, zdistD_neg, hv]
      omega
    · rw [eT, eF, baP8_Q_comm, baP8_Q_neg_left, norm_neg, baP8_Q_comm]
  · refine ⟨x, i, j, ?_, ?_⟩
    · simp
    · rw [eT, eT]

/-- **Unit second difference at any units and any base with a good ball.**  The ball condition
`∀ w, |w - x| ≤ 2 → M ≤ |w|` covers the shifted base point of the sign reduction. -/
private theorem baP8_unitQ (hL : 3 ≤ L) (f : Zd d L → ℂ) (K : ℝ) (hK : 0 ≤ K) (q : ℕ)
    (hU : ∀ (x : Zd d L) (i j : Fin d),
      ‖f (x + Pi.single i 1 + Pi.single j 1) - f (x + Pi.single i 1)
          - f (x + Pi.single j 1) + f x‖ ≤ K * (((zdistD d L x : ℝ) + 1) ^ q)⁻¹)
    (M : ℝ) (hM : 0 ≤ M) (x u e : Zd d L) (hu : zdistD d L u = 1) (he : zdistD d L e = 1)
    (hball : ∀ w : Zd d L, zdistD d L (w - x) ≤ 2 → M ≤ (zdistD d L w : ℝ)) :
    ‖baP8_Q f x u e‖ ≤ K * ((M + 1) ^ q)⁻¹ := by
  obtain ⟨x', i, j, hx', hnorm⟩ := baP8_reduce hL f x u e hu he
  rw [hnorm]
  have h1 := hU x' i j
  have h2 : M ≤ (zdistD d L x' : ℝ) := hball x' hx'
  refine le_trans h1 ?_
  refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hK
  exact pow_le_pow_left₀ (by linarith) (by linarith) q

/-- **P7 core.**  With a good ball of radius `|r|` around `a` (good = unit second differences
bounded by `B` at the base point), `|f(a+r) + f(a-r) - 2 f(a)| ≤ |r|² B`. -/
private theorem baP8_second (hL : 3 ≤ L) (f : Zd d L → ℂ) (P : Zd d L → Prop) (B : ℝ)
    (hQ : ∀ x u e : Zd d L, zdistD d L u = 1 → zdistD d L e = 1 → P x →
      ‖baP8_Q f x u e‖ ≤ B) :
    ∀ (n : ℕ) (r a : Zd d L), zdistD d L r = n → (∀ z, zdistD d L (z - a) ≤ n → P z) →
      ‖f (a + r) + f (a - r) - 2 * f a‖ ≤ (n : ℝ) ^ 2 * B := by
  intro n
  induction n with
  | zero =>
    intro r a hr _
    have h0 : r = 0 := (zdistD_eq_zero_iff d L).mp hr
    subst h0
    have : f (a + 0) + f (a - 0) - 2 * f a = 0 := by
      rw [add_zero, sub_zero]
      ring
    rw [this]
    simp
  | succ n ih =>
    intro r a hr hP
    have hr0 : r ≠ 0 := by
      intro h
      subst h
      simp at hr
    obtain ⟨e, he, hre⟩ := exists_step hL hr0
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + e := ⟨r - e, by abel⟩
    have hr' : zdistD d L r' = n := by
      have : r' + e - e = r' := by abel
      rw [this] at hre
      omega
    have hih := ih r' a hr' (fun z hz => hP z (by omega))
    -- the first difference function `G = D_e f`
    obtain ⟨G, hG⟩ : ∃ G : Zd d L → ℂ, G = fun x => f (x + e) - f x := ⟨_, rfl⟩
    have hGU : ∀ x u : Zd d L, zdistD d L u = 1 → P x → P (x + u) →
        ‖G (x + u) - G x‖ ≤ B := by
      intro x u hu hx _
      have : G (x + u) - G x = baP8_Q f x u e := by
        simp only [hG, baP8_Q]
        ring
      rw [this]
      exact hQ x u e hu he hx
    have hball1 : ∀ z, zdistD d L (z - (a - e)) ≤ n → P z := by
      intro z hz
      apply hP
      have h := zdistD_add_le d L (z - (a - e)) (-e)
      have e1 : z - (a - e) + -e = z - a := by abel
      rw [e1, zdistD_neg, he] at h
      omega
    -- T2: `G(a - e + r') - G(a - e)`
    have hT2 := baP8_path hL G P B hGU n r' (a - e) hr' hball1
    -- T1: `G(a - e) - G(a - e - r')`
    have hT1 := baP8_path hL G P B hGU n (-r') (a - e) (by rw [zdistD_neg, hr']) hball1
    have e4 : a - e + -r' = a - e - r' := by abel
    rw [e4, norm_sub_rev] at hT1
    -- T3: the unit second difference at `a - e + r'`
    have hbase : P (a - e + r') := by
      apply hP
      have h := zdistD_add_le d L (-e) r'
      have e1 : a - e + r' - a = -e + r' := by abel
      rw [e1]
      rw [zdistD_neg, he, hr'] at h
      omega
    have e3 : a - e + r' + e = a + r' := by abel
    have hT3 : ‖G (a + r') - G (a - e + r')‖ ≤ B := by
      have := hGU (a - e + r') e he hbase (by
        apply hP
        have e1 : a - e + r' + e - a = r' := by abel
        rw [e1, hr']
        omega)
      rwa [e3] at this
    have hid : f (a + (r' + e)) + f (a - (r' + e)) - 2 * f a
        = (f (a + r') + f (a - r') - 2 * f a)
          + (G (a - e) - G (a - e - r'))
          + (G (a - e + r') - G (a - e))
          + (G (a + r') - G (a - e + r')) := by
      have h1 : a - e + e = a := by abel
      have h2 : a - e - r' + e = a - r' := by abel
      have h4 : a - (r' + e) = a - e - r' := by abel
      have h5 : a + (r' + e) = a + r' + e := by abel
      simp only [hG]
      rw [h1, h2, e3, h4, h5]
      ring
    rw [hid]
    have hnorm := norm_add_le (f (a + r') + f (a - r') - 2 * f a
          + (G (a - e) - G (a - e - r')) + (G (a - e + r') - G (a - e)))
        (G (a + r') - G (a - e + r'))
    have hnorm2 := norm_add_le (f (a + r') + f (a - r') - 2 * f a
          + (G (a - e) - G (a - e - r'))) (G (a - e + r') - G (a - e))
    have hnorm3 := norm_add_le (f (a + r') + f (a - r') - 2 * f a)
          (G (a - e) - G (a - e - r'))
    push_cast
    nlinarith [hnorm, hnorm2, hnorm3, hih, hT1, hT2, hT3]

end PathLemmas

/-! ### Properties 6 and 7 -/

/-- `((1-c)|a| + 1) ≥ (1-c)(|a|+1)`: the P6 conversion. -/
private lemma baP8_conv1 {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (A : ℝ) (hA : 0 ≤ A) (p : ℕ) :
    (((1 - c) * A + 1) ^ p)⁻¹ ≤ (((1 - c) ^ p)⁻¹) * ((A + 1) ^ p)⁻¹ := by
  have h1 : 0 < 1 - c := by linarith
  have h2 : (1 - c) * (A + 1) ≤ (1 - c) * A + 1 := by nlinarith
  calc (((1 - c) * A + 1) ^ p)⁻¹ ≤ (((1 - c) * (A + 1)) ^ p)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2 p)
    _ = (((1 - c) ^ p)⁻¹) * ((A + 1) ^ p)⁻¹ := by rw [mul_pow, mul_inv]

/-- The P7 conversion: `max (1, (1-c)A - 1) ≥ (1-c)(A+1)/3`, i.e. with `M = max 0 ((1-c)A - 2)`,
`(M+1)^{-p} ≤ 3^p (1-c)^{-p} (A+1)^{-p}`. -/
private lemma baP8_conv2 {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (A : ℝ) (hA : 0 ≤ A) (p : ℕ) :
    ((max 0 ((1 - c) * A - 2) + 1) ^ p)⁻¹
      ≤ (3 : ℝ) ^ p * (((1 - c) ^ p)⁻¹) * ((A + 1) ^ p)⁻¹ := by
  have h1 : 0 < 1 - c := by linarith
  have h2 : (1 - c) * (A + 1) / 3 ≤ max 0 ((1 - c) * A - 2) + 1 := by
    rcases le_total ((1 - c) * A) 2 with h | h
    · have : (1 - c) * (A + 1) / 3 ≤ 1 := by nlinarith
      have h0 : (0 : ℝ) ≤ max 0 ((1 - c) * A - 2) := le_max_left _ _
      linarith
    · have hA2 : 2 ≤ A := by nlinarith
      have h3 : (1 - c) * A - 2 ≤ max 0 ((1 - c) * A - 2) := le_max_right _ _
      nlinarith
  have h3 : 0 < (1 - c) * (A + 1) / 3 := by positivity
  calc ((max 0 ((1 - c) * A - 2) + 1) ^ p)⁻¹
      ≤ (((1 - c) * (A + 1) / 3) ^ p)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ h3.le h2 p)
    _ = (3 : ℝ) ^ p * (((1 - c) ^ p)⁻¹) * ((A + 1) ^ p)⁻¹ := by
        rw [div_pow, mul_pow, inv_div, div_eq_mul_inv, mul_inv]
        ring

/-! ## 2. Elementary inequalities (`σ₁ = σ₂` reductions) -/

/-- `S(m, x) = 2^m (1 + m!/x^m)`: `(r+1)^m e^{-x r} ≤ S(m, x)` for `r ≥ 0`, `x > 0`. -/
private noncomputable def baP8_S (m : ℕ) (x : ℝ) : ℝ :=
  2 ^ m * (1 + (Nat.factorial m : ℝ) / x ^ m)

private lemma baP8_S_pos (m : ℕ) {x : ℝ} (hx : 0 < x) : 0 < baP8_S m x := by
  unfold baP8_S
  positivity

/-- `(r+1)^m e^{-x r} ≤ 2^m (1 + m!/x^m)`, as inside `sum_radial_exp_decay_le`
(`Defs/RadialSum.lean:275-300`). -/
private lemma baP8_poly_exp (m : ℕ) {x : ℝ} (hx : 0 < x) {r : ℝ} (hr : 0 ≤ r) :
    (r + 1) ^ m * Real.exp (-(x * r)) ≤ baP8_S m x := by
  have hE : 0 < Real.exp (-(x * r)) := Real.exp_pos _
  have h1 : (r + 1) ^ m ≤ 2 ^ m * (1 + r ^ m) := by
    rcases le_total r 1 with h | h
    · calc (r + 1) ^ m ≤ (2 : ℝ) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ ≤ 2 ^ m * (1 + r ^ m) :=
            le_mul_of_one_le_right (by positivity) (by have := pow_nonneg hr m; linarith)
    · calc (r + 1) ^ m ≤ (2 * r) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 2 ^ m * r ^ m := mul_pow _ _ _
        _ ≤ 2 ^ m * (1 + r ^ m) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : r ^ m * Real.exp (-(x * r)) ≤ (Nat.factorial m : ℝ) / x ^ m :=
    pow_mul_exp_neg_le hx m hr
  have h3 : Real.exp (-(x * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc (r + 1) ^ m * Real.exp (-(x * r))
      ≤ (2 ^ m * (1 + r ^ m)) * Real.exp (-(x * r)) := mul_le_mul_of_nonneg_right h1 hE.le
    _ = 2 ^ m * (Real.exp (-(x * r)) + r ^ m * Real.exp (-(x * r))) := by ring
    _ ≤ baP8_S m x := by
        unfold baP8_S
        have : (0 : ℝ) < 2 ^ m := by positivity
        nlinarith

/-- `e^{-x n} ≤ S(m, x) (n+1)^{-m}`. -/
private lemma baP8_exp_le (m : ℕ) {x : ℝ} (hx : 0 < x) {n : ℝ} (hn : 0 ≤ n) :
    Real.exp (-(x * n)) ≤ baP8_S m x * ((n + 1) ^ m)⁻¹ := by
  have h := baP8_poly_exp m hx hn
  have hp : 0 < (n + 1) ^ m := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  calc Real.exp (-(x * n)) * (n + 1) ^ m = (n + 1) ^ m * Real.exp (-(x * n)) := mul_comm _ _
    _ ≤ baP8_S m x := h

/-- (E1) `1 ≤ (Λ²+1)(g²+|1-t|)⁻¹` for `0 < g ≤ Λ`, `0 ≤ t < 1`. -/
private lemma baP8_E1 {Λ g t : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 ≤ (Λ ^ 2 + 1) * (g ^ 2 + |1 - t|)⁻¹ := by
  have habs : |1 - t| = 1 - t := abs_of_pos (by linarith)
  have hpos : 0 < g ^ 2 + |1 - t| := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, habs]
  nlinarith [mul_self_le_mul_self hg.le hgΛ]

/-- (E2) `g² ≤ Λ²(Λ²+1)(g²+|1-t|)⁻¹`. -/
private lemma baP8_E2 {Λ g t : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    g ^ 2 ≤ Λ ^ 2 * (Λ ^ 2 + 1) * (g ^ 2 + |1 - t|)⁻¹ := by
  have h1 := baP8_E1 hg hgΛ ht0 ht1
  have h2 : g ^ 2 ≤ Λ ^ 2 := by nlinarith
  calc g ^ 2 ≤ Λ ^ 2 * 1 := by linarith
    _ ≤ Λ ^ 2 * ((Λ ^ 2 + 1) * (g ^ 2 + |1 - t|)⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Λ ^ 2 * (Λ ^ 2 + 1) * (g ^ 2 + |1 - t|)⁻¹ := by ring

/-- `g² e^{-x n} ≤ Λ²(Λ²+1) S(m, x) (g²+|1-t|)⁻¹ (n+1)^{-m}` (E2 with E3). -/
private lemma baP8_g2_exp (m : ℕ) {Λ g t x n : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hx : 0 < x) (hn : 0 ≤ n) :
    g ^ 2 * Real.exp (-(x * n))
      ≤ Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S m x * ((g ^ 2 + |1 - t|)⁻¹ * ((n + 1) ^ m)⁻¹) := by
  have h1 := baP8_E2 hg hgΛ ht0 ht1
  have h2 := baP8_exp_le m hx hn
  calc g ^ 2 * Real.exp (-(x * n))
      ≤ (Λ ^ 2 * (Λ ^ 2 + 1) * (g ^ 2 + |1 - t|)⁻¹) * (baP8_S m x * ((n + 1) ^ m)⁻¹) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S m x * ((g ^ 2 + |1 - t|)⁻¹ * ((n + 1) ^ m)⁻¹) := by ring

/-- `B_{t,K} ≥ (g²+|1-t|)⁻¹ (K+1)^{-(d-2)}` (the second summand of `Bparam` is `≥ 0`).  The merged
`KLlat_inv_le_Bparam` (`Loop/KLIndStepA.lean:109`) is at `K = 0` only and not imported. -/
private lemma baP8_Bparam_ge (d L : ℕ) (g t : ℝ) (K : ℕ) :
    (g ^ 2 + |1 - t|)⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ Bparam d L g t K := by
  unfold Bparam
  have : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  linarith

private lemma baP8_Bparam_nonneg (d L : ℕ) (g t : ℝ) (K : ℕ) : 0 ≤ Bparam d L g t K := by
  unfold Bparam
  positivity

/-- The lower bound `(1-c)|a| ≤ |a ± r|` from `|r| ≤ c |a|`. -/
private lemma baP8_lower {d L : ℕ} [NeZero L] {c : ℝ} (a r : Zd d L)
    (hr : (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ)) :
    (1 - c) * (zdistD d L a : ℝ) ≤ (zdistD d L (a + r) : ℝ) ∧
      (1 - c) * (zdistD d L a : ℝ) ≤ (zdistD d L (a - r) : ℝ) := by
  have h1 := zdistD_add_le d L (a + r) (-r)
  rw [add_neg_cancel_right, zdistD_neg] at h1
  have h2 := zdistD_add_le d L (a - r) r
  rw [sub_add_cancel] at h2
  have h1' : (zdistD d L a : ℝ) ≤ zdistD d L (a + r) + zdistD d L r := by exact_mod_cast h1
  have h2' : (zdistD d L a : ℝ) ≤ zdistD d L (a - r) + zdistD d L r := by exact_mod_cast h2
  constructor <;> linarith

/-- If `0 < n ≤ |z|` then `‖T z‖ ≤ C_s g² e^{-c' n}` (the indicator vanishes since `z ≠ 0`). -/
private lemma baP8_tail {d L : ℕ} {g Cs c' n : ℝ} (hCs : 0 < Cs) (hc' : 0 < c')
    (T : Zd d L → ℂ)
    (hT : ∀ a, ‖T a‖ ≤ Cs * ((if a = 0 then (1 : ℝ) else 0)
      + g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ))))
    (z : Zd d L) (hn : 0 < n) (hz : n ≤ (zdistD d L z : ℝ)) :
    ‖T z‖ ≤ Cs * (g ^ 2 * Real.exp (-(c' * n))) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [zdistD_zero, Nat.cast_zero] at hz
    linarith
  have h := hT z
  simp only [hz0, ite_false, zero_add] at h
  refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hCs.le)
  apply Real.exp_le_exp.mpr
  nlinarith

/-! ## 3. Translation invariance of `BAMss` and `BATheta`

No `BATheta` shift lemma is merged (`BAMB_shift`, `BA/Ward.lean:53`, and `BAK_shift`,
`BA/KKernel.lean:66`, are the only shift lemmas); the pattern of `BAMB_shift` (`Matrix.inv_submatrix_equiv`,
`Matrix.nonsing_inv_eq_ringInverse`) handles the possibly singular case. -/

section Shift

variable {d L : ℕ} [NeZero L]

private lemma baP8_BAMss_shift (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
    BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ (a + r) (b + r)
      = BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b := by
  have hM := BAMB_shift d L g (E : ℂ) m
  have hs : ∀ (σ : Bool) (x y : Zd d L),
      BAMsigma d L (BAMB d L g (E : ℂ) m) σ (x + r) (y + r)
        = BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y := by
    intro σ x y
    cases σ
    · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, hM]
    · simp only [BAMsigma, ite_true, hM]
  simp only [BAMss, Matrix.of_apply, hs]

/-- `Θ_t(a + r, b + r) = Θ_t(a, b)`, every `(σ₁, σ₂)`, unconditional (also at a singular `1 - tQ`). -/
lemma baP8_BATheta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
    BATheta d L g E m t σ₁ σ₂ (a + r) (b + r) = BATheta d L g E m t σ₁ σ₂ a b := by
  have hA : (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂).submatrix
      (Equiv.addRight r) (Equiv.addRight r)
      = 1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ := by
    ext x y
    have h1 : (x + r = y + r) ↔ (x = y) := add_left_inj r
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Equiv.coe_addRight, h1, baP8_BAMss_shift]
  have h2 := Matrix.inv_submatrix_equiv
    (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) (Equiv.addRight r) (Equiv.addRight r)
  rw [hA] at h2
  unfold BATheta PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 a) b
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- The double sum of a shift-invariant matrix: `Σ_{a'} Σ_{b'} T(a', b') = L^d Σ_b T(0, b)`. -/
private lemma baP8_sum_shift (T : Matrix (Zd d L) (Zd d L) ℂ)
    (hT : ∀ a b r : Zd d L, T (a + r) (b + r) = T a b) :
    ∑ a', ∑ b', T a' b' = ((L : ℂ) ^ d) * ∑ b, T 0 b := by
  have h1 : ∀ a' : Zd d L, ∑ b', T a' b' = ∑ b, T 0 b := by
    intro a'
    have h := fun b' : Zd d L => hT 0 (b' - a') a'
    simp only [zero_add, sub_add_cancel] at h
    rw [Finset.sum_congr rfl fun b' _ => h b']
    exact Fintype.sum_equiv (Equiv.subRight a') _ _ fun _ => rfl
  rw [Finset.sum_congr rfl fun a' _ => h1 a', Finset.sum_const, Finset.card_univ, card_Zd,
    nsmul_eq_mul, Nat.cast_pow]

end Shift

/-! ## 4. The reductions for `σ₁ = σ₂` from `|T(a)| ≤ C_s (1_{a=0} + g² e^{-c'|a|})`

Generic in the row `T = Θ(0, ·)` (`BAProp5s`, merged: `baProp5s_holds`). -/

section Equal

variable {d L : ℕ}

/-- **(5)** `σ₁ = σ₂`: `|T(a)| ≤ K B_{t,|a|} e^{-c₅|a|/ℓ_t}` with `c₅ ≤ c'/2`. -/
private lemma baP8_prop5_eq (hL : 3 ≤ L) {Λ g t Cs c' c₅ : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hCs : 0 < Cs) (hc' : 0 < c') (hc₅ : 0 < c₅)
    (hc₅' : c₅ ≤ c' / 2) (T : Zd d L → ℂ) (a : Zd d L)
    (hT : ‖T a‖ ≤ Cs * ((if a = 0 then (1 : ℝ) else 0)
      + g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ)))) :
    ‖T a‖ ≤ (Cs * max ((Λ ^ 2 + 1) * (Λ ^ 2 + 1))
        (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2)))
      * Bparam d L g t (zdistD d L a) * Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hℓ : 1 ≤ ellT L g t := one_le_ellT hLr
  have hBge := baP8_Bparam_ge d L g t (zdistD d L a)
  have hB0 := baP8_Bparam_nonneg d L g t (zdistD d L a)
  have hE := baP8_E1 hg hgΛ ht0 ht1
  have hu : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have hS := baP8_S_pos (d - 2) (by linarith : 0 < c' / 2)
  have hE0 : 0 ≤ Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t) := (Real.exp_pos _).le
  by_cases ha : a = 0
  · subst ha
    have hT' : ‖T 0‖ ≤ Cs * (1 + g ^ 2) := by simpa [zdistD_zero] using hT
    simp only [zdistD_zero, Nat.cast_zero, zero_add, one_pow, inv_one, mul_one] at hBge
    simp only [zdistD_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    have h1 : 1 + g ^ 2 ≤ (Λ ^ 2 + 1) * ((Λ ^ 2 + 1) * (g ^ 2 + |1 - t|)⁻¹) := by
      have : g ^ 2 ≤ Λ ^ 2 := by nlinarith
      nlinarith
    calc ‖T 0‖ ≤ Cs * (1 + g ^ 2) := hT'
      _ ≤ Cs * (((Λ ^ 2 + 1) * (Λ ^ 2 + 1)) * (g ^ 2 + |1 - t|)⁻¹) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hCs.le
      _ = (Cs * ((Λ ^ 2 + 1) * (Λ ^ 2 + 1))) * (g ^ 2 + |1 - t|)⁻¹ := by ring
      _ ≤ (Cs * max ((Λ ^ 2 + 1) * (Λ ^ 2 + 1))
            (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2))) * Bparam d L g t 0 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (le_max_left _ _) hCs.le) hBge hu (by positivity)
  · simp only [ha, ite_false, zero_add] at hT
    have hn0 : (0 : ℝ) ≤ zdistD d L a := Nat.cast_nonneg _
    have hexp : Real.exp (-c' * (zdistD d L a : ℝ))
        = Real.exp (-((c' / 2) * (zdistD d L a : ℝ)))
          * Real.exp (-((c' / 2) * (zdistD d L a : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp2 : Real.exp (-((c' / 2) * (zdistD d L a : ℝ)))
        ≤ Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t) := by
      apply Real.exp_le_exp.mpr
      have h1 : c₅ * (zdistD d L a : ℝ) / ellT L g t ≤ c₅ * (zdistD d L a : ℝ) :=
        div_le_self (by positivity) hℓ
      have h2 : -c₅ * (zdistD d L a : ℝ) / ellT L g t
          = -(c₅ * (zdistD d L a : ℝ) / ellT L g t) := by ring
      rw [h2]
      nlinarith
    have hg2 := baP8_g2_exp (d - 2) (Λ := Λ) (t := t) hg hgΛ ht0 ht1 (by linarith : 0 < c' / 2) hn0
    have h3 : g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ))
        ≤ (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2)) * Bparam d L g t (zdistD d L a)
          * Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t) := by
      calc g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ))
          = (g ^ 2 * Real.exp (-((c' / 2) * (zdistD d L a : ℝ))))
            * Real.exp (-((c' / 2) * (zdistD d L a : ℝ))) := by rw [hexp]; ring
        _ ≤ ((Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2))
              * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹))
            * Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t) :=
            mul_le_mul hg2 hexp2 (Real.exp_pos _).le (by positivity)
        _ ≤ (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2)) * Bparam d L g t (zdistD d L a)
            * Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hBge (by positivity)) hE0
    calc ‖T a‖ ≤ Cs * (g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ))) := hT
      _ ≤ Cs * ((Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2)) * Bparam d L g t (zdistD d L a)
          * Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t)) :=
          mul_le_mul_of_nonneg_left h3 hCs.le
      _ = (Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2))) * Bparam d L g t (zdistD d L a)
          * Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t) := by ring
      _ ≤ (Cs * max ((Λ ^ 2 + 1) * (Λ ^ 2 + 1))
            (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2)))
          * Bparam d L g t (zdistD d L a) * Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t) := by
          gcongr
          exact le_max_right _ _

/-- **(6)** `σ₁ = σ₂`. -/
private lemma baP8_prop6_eq [NeZero L] {Λ g t Cs c' c : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hCs : 0 < Cs) (hc' : 0 < c') (hc0 : 0 < c) (hc1 : c < 1)
    (T : Zd d L → ℂ)
    (hT : ∀ a, ‖T a‖ ≤ Cs * ((if a = 0 then (1 : ℝ) else 0)
      + g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ))))
    (a r : Zd d L) (hr : (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ)) :
    ‖T (a + r) - T a‖
      ≤ (2 * Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 1) (c' * (1 - c))))
        * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by
  by_cases hr0 : r = 0
  · subst hr0
    simp [zdistD_zero]
  have hr1 : (1 : ℝ) ≤ zdistD d L r := by
    have : 0 < zdistD d L r := Nat.pos_of_ne_zero fun h => hr0 ((zdistD_eq_zero_iff d L).mp h)
    exact_mod_cast this
  have ha0 : (0 : ℝ) < zdistD d L a := by
    rcases Nat.eq_zero_or_pos (zdistD d L a) with h | h
    · have h0 : (zdistD d L a : ℝ) = 0 := by exact_mod_cast h
      rw [h0] at hr
      linarith
    · exact_mod_cast h
  obtain ⟨hlo1, -⟩ := baP8_lower a r hr
  have h1c : 0 < 1 - c := by linarith
  have hn : 0 < (1 - c) * (zdistD d L a : ℝ) := mul_pos h1c ha0
  have hna : (1 - c) * (zdistD d L a : ℝ) ≤ zdistD d L a := by nlinarith
  have t1 := baP8_tail hCs hc' T hT (a + r) hn hlo1
  have t2 := baP8_tail hCs hc' T hT a hn hna
  have hS := baP8_S_pos (d - 1) (by positivity : 0 < c' * (1 - c))
  have hg2 := baP8_g2_exp (d - 1) (Λ := Λ) (t := t) hg hgΛ ht0 ht1 (by positivity : 0 < c' * (1 - c))
    (Nat.cast_nonneg (zdistD d L a))
  have hexp : Real.exp (-(c' * ((1 - c) * (zdistD d L a : ℝ))))
      = Real.exp (-((c' * (1 - c)) * (zdistD d L a : ℝ))) := by rw [mul_assoc]
  rw [hexp] at t1 t2
  have hu : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have hp : 0 ≤ (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by positivity
  calc ‖T (a + r) - T a‖ ≤ ‖T (a + r)‖ + ‖T a‖ := norm_sub_le _ _
    _ ≤ 2 * (Cs * (g ^ 2 * Real.exp (-((c' * (1 - c)) * (zdistD d L a : ℝ))))) := by linarith
    _ ≤ 2 * (Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 1) (c' * (1 - c))
          * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹))) := by
        gcongr
    _ = (2 * Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 1) (c' * (1 - c))))
          * (g ^ 2 + |1 - t|)⁻¹ * 1 * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by ring
    _ ≤ (2 * Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 1) (c' * (1 - c))))
          * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by
        gcongr

/-- **(7)** `σ₁ = σ₂`. -/
private lemma baP8_prop7_eq [NeZero L] {Λ g t Cs c' c : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hCs : 0 < Cs) (hc' : 0 < c') (hc0 : 0 < c) (hc1 : c < 1)
    (T : Zd d L → ℂ)
    (hT : ∀ a, ‖T a‖ ≤ Cs * ((if a = 0 then (1 : ℝ) else 0)
      + g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ))))
    (a r : Zd d L) (hr : (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ)) :
    ‖T (a + r) + T (a - r) - 2 * T a‖
      ≤ (4 * Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S d (c' * (1 - c))))
        * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by
  by_cases hr0 : r = 0
  · subst hr0
    have h0 : T (a + 0) + T (a - 0) - 2 * T a = 0 := by
      rw [add_zero, sub_zero]
      ring
    rw [h0]
    simp [zdistD_zero]
  have hr1 : (1 : ℝ) ≤ zdistD d L r := by
    have : 0 < zdistD d L r := Nat.pos_of_ne_zero fun h => hr0 ((zdistD_eq_zero_iff d L).mp h)
    exact_mod_cast this
  have ha0 : (0 : ℝ) < zdistD d L a := by
    rcases Nat.eq_zero_or_pos (zdistD d L a) with h | h
    · have h0 : (zdistD d L a : ℝ) = 0 := by exact_mod_cast h
      rw [h0] at hr
      linarith
    · exact_mod_cast h
  obtain ⟨hlo1, hlo2⟩ := baP8_lower a r hr
  have h1c : 0 < 1 - c := by linarith
  have hn : 0 < (1 - c) * (zdistD d L a : ℝ) := mul_pos h1c ha0
  have hna : (1 - c) * (zdistD d L a : ℝ) ≤ zdistD d L a := by nlinarith
  have t1 := baP8_tail hCs hc' T hT (a + r) hn hlo1
  have t2 := baP8_tail hCs hc' T hT (a - r) hn hlo2
  have t3 := baP8_tail hCs hc' T hT a hn hna
  have hS := baP8_S_pos d (by positivity : 0 < c' * (1 - c))
  have hg2 := baP8_g2_exp d (Λ := Λ) (t := t) hg hgΛ ht0 ht1 (by positivity : 0 < c' * (1 - c))
    (Nat.cast_nonneg (zdistD d L a))
  have hexp : Real.exp (-(c' * ((1 - c) * (zdistD d L a : ℝ))))
      = Real.exp (-((c' * (1 - c)) * (zdistD d L a : ℝ))) := by rw [mul_assoc]
  rw [hexp] at t1 t2 t3
  have hu : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have hp : 0 ≤ (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by positivity
  have hnorm : ‖T (a + r) + T (a - r) - 2 * T a‖ ≤ ‖T (a + r)‖ + ‖T (a - r)‖ + 2 * ‖T a‖ := by
    calc ‖T (a + r) + T (a - r) - 2 * T a‖ ≤ ‖T (a + r) + T (a - r)‖ + ‖2 * T a‖ :=
          norm_sub_le _ _
      _ ≤ ‖T (a + r)‖ + ‖T (a - r)‖ + ‖2 * T a‖ := by
          gcongr
          exact norm_add_le _ _
      _ = ‖T (a + r)‖ + ‖T (a - r)‖ + 2 * ‖T a‖ := by simp [norm_mul]
  calc ‖T (a + r) + T (a - r) - 2 * T a‖ ≤ ‖T (a + r)‖ + ‖T (a - r)‖ + 2 * ‖T a‖ := hnorm
    _ ≤ 4 * (Cs * (g ^ 2 * Real.exp (-((c' * (1 - c)) * (zdistD d L a : ℝ))))) := by linarith
    _ ≤ 4 * (Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S d (c' * (1 - c))
          * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹))) := by
        gcongr
    _ = (4 * Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S d (c' * (1 - c))))
          * (g ^ 2 + |1 - t|)⁻¹ * 1 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by ring
    _ ≤ (4 * Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S d (c' * (1 - c))))
          * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by
        have : (1 : ℝ) ≤ (zdistD d L r : ℝ) ^ 2 := by nlinarith
        gcongr

end Equal

section Equal8

variable {d L : ℕ} [NeZero L]

omit [NeZero L] in
/-- `L^{-d} ≤ (d+1)^{d-2} (|a|+1)^{-(d-2)}` from `|a| ≤ d L` (`zdistD_le`, `Defs/RadialSum.lean:44`). -/
private lemma baP8_Linv_le (hd : 2 ≤ d) (hL : 3 ≤ L) (a : Zd d L) :
    ((L : ℝ) ^ d)⁻¹ ≤ ((d : ℝ) + 1) ^ (d - 2) * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hLpos : (0 : ℝ) < L := by linarith
  have hn : (zdistD d L a : ℝ) ≤ d * L := by exact_mod_cast zdistD_le d a
  have h1 : (zdistD d L a : ℝ) + 1 ≤ ((d : ℝ) + 1) * L := by nlinarith
  have h2 : ((zdistD d L a : ℝ) + 1) ^ (d - 2) ≤ (((d : ℝ) + 1) * L) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have h3 : (L : ℝ) ^ (d - 2) ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hLr (by omega)
  have hP : 0 < ((zdistD d L a : ℝ) + 1) ^ (d - 2) := by positivity
  have hLd : 0 < (L : ℝ) ^ d := by positivity
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hLd hP]
  calc 1 * ((zdistD d L a : ℝ) + 1) ^ (d - 2) ≤ (((d : ℝ) + 1) * L) ^ (d - 2) := by linarith
    _ = ((d : ℝ) + 1) ^ (d - 2) * (L : ℝ) ^ (d - 2) := mul_pow _ _ _
    _ ≤ ((d : ℝ) + 1) ^ (d - 2) * (L : ℝ) ^ d := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The row sum of the short bound: `Σ_b ‖T(b)‖ ≤ C_s (1 + Λ² expC(d-2, c'))`. -/
private lemma baP8_row_sum_le (hd : 2 ≤ d) {Λ g Cs c' : ℝ} (hgΛ : g ≤ Λ) (hg : 0 < g)
    (hCs : 0 < Cs) (hc' : 0 < c') (T : Zd d L → ℂ)
    (hT : ∀ a, ‖T a‖ ≤ Cs * ((if a = 0 then (1 : ℝ) else 0)
      + g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ)))) :
    ∑ b, ‖T b‖ ≤ Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') := by
  have hind : ∑ b : Zd d L, (if b = 0 then (1 : ℝ) else 0) = 1 := by simp
  have hexp : ∑ b : Zd d L, Real.exp (-c' * (zdistD d L b : ℝ)) ≤ RBM.expC (d - 2) c' := by
    have h := BAsum_exp_decay_le d L hd c' hc' 0
    refine le_of_eq_of_le (Finset.sum_congr rfl fun b _ => ?_) h
    rw [zero_sub, zdistD_neg, neg_mul]
  have hg2 : g ^ 2 ≤ Λ ^ 2 := by nlinarith
  have hE0 : 0 ≤ RBM.expC (d - 2) c' := by unfold RBM.expC; positivity
  calc ∑ b, ‖T b‖ ≤ ∑ b : Zd d L, Cs * ((if b = 0 then (1 : ℝ) else 0)
        + g ^ 2 * Real.exp (-c' * (zdistD d L b : ℝ))) := Finset.sum_le_sum fun b _ => hT b
    _ = Cs * (1 + g ^ 2 * ∑ b : Zd d L, Real.exp (-c' * (zdistD d L b : ℝ))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hind]
    _ ≤ Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') := by
        gcongr

/-- **(8)** `σ₁ = σ₂`: `Θ̊(0,a) = Θ(0,a) - L^{-2d} Σ_{a'} Σ_{b'} Θ(a',b')` for a shift-invariant `Θ`. -/
private lemma baP8_prop8_eq (hd : 2 ≤ d) (hL : 3 ≤ L) {Λ g t Cs c' : ℝ} (hg : 0 < g)
    (hgΛ : g ≤ Λ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hCs : 0 < Cs) (hc' : 0 < c')
    (Th : Matrix (Zd d L) (Zd d L) ℂ) (hsh : ∀ a b r : Zd d L, Th (a + r) (b + r) = Th a b)
    (hT : ∀ a, ‖Th 0 a‖ ≤ Cs * ((if a = 0 then (1 : ℝ) else 0)
      + g ^ 2 * Real.exp (-c' * (zdistD d L a : ℝ))))
    (a : Zd d L) :
    ‖Th 0 a - ((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', Th a' b'‖
      ≤ (Cs * (Λ ^ 2 + 1) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) c')
          + Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2) * (Λ ^ 2 + 1))
        * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (L : ℂ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast hLpos.ne')
  have hu : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have hp : 0 ≤ (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hE := baP8_E1 hg hgΛ ht0 ht1
  have hS := baP8_S_pos (d - 2) hc'
  have hE0 : 0 ≤ RBM.expC (d - 2) c' := by unfold RBM.expC; positivity
  -- the zero-mode term
  have hR : ‖((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', Th a' b'‖
      = ((L : ℝ) ^ d)⁻¹ * ‖∑ b, Th 0 b‖ := by
    rw [baP8_sum_shift Th hsh]
    have : ((L : ℂ) ^ (2 * d))⁻¹ * ((L : ℂ) ^ d * ∑ b, Th 0 b)
        = ((L : ℂ) ^ d)⁻¹ * ∑ b, Th 0 b := by
      rw [two_mul, pow_add]
      field_simp
    rw [this, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hsum := baP8_row_sum_le hd hgΛ hg hCs hc' (fun b => Th 0 b) hT
  have hs1 : ‖∑ b, Th 0 b‖ ≤ Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') :=
    (norm_sum_le _ _).trans hsum
  have hLinv := baP8_Linv_le hd hL a
  have hR2 : ‖((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', Th a' b'‖
      ≤ (Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2) * (Λ ^ 2 + 1))
        * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by
    rw [hR]
    have hK : 0 ≤ Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') := by positivity
    calc ((L : ℝ) ^ d)⁻¹ * ‖∑ b, Th 0 b‖
        ≤ (((d : ℝ) + 1) ^ (d - 2) * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹)
          * (Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c')) :=
          mul_le_mul hLinv hs1 (norm_nonneg _) (by positivity)
      _ = (Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2))
          * (1 * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by ring
      _ ≤ (Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2) * (Λ ^ 2 + 1))
          * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by
          have h1 : 1 ≤ (Λ ^ 2 + 1) * (g ^ 2 + |1 - t|)⁻¹ := hE
          calc (Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2))
                * (1 * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹)
              ≤ (Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2))
                * (((Λ ^ 2 + 1) * (g ^ 2 + |1 - t|)⁻¹) * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by
                gcongr
            _ = _ := by ring
  -- the `Θ(0,a)` term
  have hT0 : ‖Th 0 a‖ ≤ (Cs * (Λ ^ 2 + 1) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) c'))
      * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by
    have hn0 : (0 : ℝ) ≤ zdistD d L a := Nat.cast_nonneg _
    have hg2 := baP8_g2_exp (d - 2) (Λ := Λ) (t := t) hg hgΛ ht0 ht1 hc' hn0
    have hind : (if a = 0 then (1 : ℝ) else 0)
        ≤ (Λ ^ 2 + 1) * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by
      by_cases ha : a = 0
      · subst ha
        simp only [zdistD_zero, Nat.cast_zero, zero_add, one_pow, inv_one, mul_one, ite_true]
        exact hE
      · simp only [ha, ite_false]
        positivity
    calc ‖Th 0 a‖ ≤ Cs * ((if a = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(c' * (zdistD d L a : ℝ)))) := by
          have := hT a
          rwa [neg_mul] at this
      _ ≤ Cs * ((Λ ^ 2 + 1) * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹)
          + Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) c'
            * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹)) := by
          gcongr
      _ = (Cs * (Λ ^ 2 + 1) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) c'))
          * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by ring
  calc ‖Th 0 a - ((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', Th a' b'‖
      ≤ ‖Th 0 a‖ + ‖((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', Th a' b'‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

end Equal8

/-! ## 5. The targets -/

/-- **Property 5 of `lem_propTH` for `Θ_BA`, all charge pairs** (`BAProp5`): `σ₁ ≠ σ₂` is
`baProp5mixed_holds`; `σ₁ = σ₂` is `baProp5s_holds` with `c := min (c_mixed, c'/2)`. -/
theorem baProp5_holds (d : ℕ) (Λ κ : ℝ) : BAProp5 d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨Cs, hCs, c', hc', Hs⟩ := baProp5s_holds d Λ κ hd hΛ hκ
  obtain ⟨Cm, hCm, cm, hcm, Hm⟩ := baProp5mixed_holds d Λ κ hd hΛ hκ
  have hc₅ : 0 < min cm (c' / 2) := lt_min hcm (by positivity)
  refine ⟨max Cm (Cs * max ((Λ ^ 2 + 1) * (Λ ^ 2 + 1))
      (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) (c' / 2))), lt_max_of_lt_left hCm,
    min cm (c' / 2), hc₅, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ a
  have : NeZero L := ⟨by omega⟩
  have hB0 := baP8_Bparam_nonneg d L g t (zdistD d L a)
  have hE0 : 0 ≤ Real.exp (-(min cm (c' / 2)) * (zdistD d L a : ℝ) / ellT L g t) :=
    (Real.exp_pos _).le
  by_cases hσ : σ₁ = σ₂
  · subst hσ
    have h := baP8_prop5_eq hL hg hgΛ ht0 ht1 hCs hc' hc₅ (min_le_right _ _)
      (fun x => BATheta d L g E m t σ₁ σ₁ 0 x) a (Hs L hL g hg hgΛ E m hr t ht0 ht1 σ₁ a)
    refine h.trans ?_
    gcongr
    exact le_max_right _ _
  · have h := Hm L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ hσ a
    have hℓ : 0 < ellT L g t := ellT_pos (by exact_mod_cast (by omega : 1 ≤ L))
    have hexp : Real.exp (-cm * (zdistD d L a : ℝ) / ellT L g t)
        ≤ Real.exp (-(min cm (c' / 2)) * (zdistD d L a : ℝ) / ellT L g t) := by
      apply Real.exp_le_exp.mpr
      have h1 : min cm (c' / 2) ≤ cm := min_le_left _ _
      have h2 : (0 : ℝ) ≤ zdistD d L a := Nat.cast_nonneg _
      apply div_le_div_of_nonneg_right _ hℓ.le
      nlinarith
    refine h.trans ?_
    calc Cm * Bparam d L g t (zdistD d L a) * Real.exp (-cm * (zdistD d L a : ℝ) / ellT L g t)
        ≤ Cm * Bparam d L g t (zdistD d L a)
          * Real.exp (-(min cm (c' / 2)) * (zdistD d L a : ℝ) / ellT L g t) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _

/-- **Property 6 of `lem_propTH` for `Θ_BA`, all charge pairs** (`BAProp6`): `σ₁ ≠ σ₂` by the path
argument on `baPropUnit1mixed_holds` (constant `C₁ (1-c)^{-(d-1)}`); `σ₁ = σ₂` from `baProp5s_holds`
(constant `2 C_s Λ²(Λ²+1) S(d-1, c'(1-c))`). -/
theorem baProp6_holds (d : ℕ) (Λ κ c : ℝ) : BAProp6 d Λ κ c := by
  intro hd hΛ hκ hc0 hc1
  obtain ⟨Cs, hCs, c', hc', Hs⟩ := baProp5s_holds d Λ κ hd hΛ hκ
  obtain ⟨C₁, hC₁, H1⟩ := baPropUnit1mixed_holds d Λ κ hd hΛ hκ
  have h1c : 0 < 1 - c := by linarith
  have hS := baP8_S_pos (d - 1) (by positivity : 0 < c' * (1 - c))
  refine ⟨max (C₁ * ((1 - c) ^ (d - 1))⁻¹)
      (2 * Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 1) (c' * (1 - c)))),
    lt_max_of_lt_left (by positivity), ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ a r hrc
  have : NeZero L := ⟨by omega⟩
  have he : 0 < g ^ 2 + |1 - t| := by positivity
  have hu : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have hr0 : (0 : ℝ) ≤ zdistD d L r := Nat.cast_nonneg _
  have hp : 0 ≤ (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by positivity
  by_cases hσ : σ₁ = σ₂
  · subst hσ
    have h := baP8_prop6_eq hg hgΛ ht0 ht1 hCs hc' hc0 hc1
      (fun x => BATheta d L g E m t σ₁ σ₁ 0 x)
      (fun x => Hs L hL g hg hgΛ E m hr t ht0 ht1 σ₁ x) a r hrc
    refine h.trans ?_
    gcongr
    exact le_max_right _ _
  · have hK : 0 ≤ C₁ * (g ^ 2 + |1 - t|)⁻¹ := by positivity
    set f : Zd d L → ℂ := fun x => BATheta d L g E m t σ₁ σ₂ 0 x with hf
    have hU : ∀ (x : Zd d L) (j : Fin d), ‖f (x + Pi.single j 1) - f x‖
        ≤ (C₁ * (g ^ 2 + |1 - t|)⁻¹) * (((zdistD d L x : ℝ) + 1) ^ (d - 1))⁻¹ :=
      fun x j => H1 L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ hσ x j
    have hA : (0 : ℝ) ≤ zdistD d L a := Nat.cast_nonneg _
    have hM : (0 : ℝ) ≤ (1 - c) * (zdistD d L a : ℝ) := by positivity
    have key := baP8_bound hL f (C₁ * (g ^ 2 + |1 - t|)⁻¹) hK (d - 1) hU
      ((1 - c) * (zdistD d L a : ℝ)) hM a r (by nlinarith)
    have hconv := baP8_conv1 hc0 hc1 (zdistD d L a : ℝ) hA (d - 1)
    have hfin : (zdistD d L r : ℝ) * ((C₁ * (g ^ 2 + |1 - t|)⁻¹)
          * ((((1 - c) * (zdistD d L a : ℝ)) + 1) ^ (d - 1))⁻¹)
        ≤ (zdistD d L r : ℝ) * ((C₁ * (g ^ 2 + |1 - t|)⁻¹)
          * (((1 - c) ^ (d - 1))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hconv hK) hr0
    refine key.trans (hfin.trans ?_)
    calc (zdistD d L r : ℝ) * ((C₁ * (g ^ 2 + |1 - t|)⁻¹)
          * (((1 - c) ^ (d - 1))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹))
        = (C₁ * ((1 - c) ^ (d - 1))⁻¹) * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ)
          * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by ring
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _

/-- **Property 7 of `lem_propTH` for `Θ_BA`, all charge pairs** (`BAProp7`): `σ₁ ≠ σ₂` by the
decomposition `r = r' + e` on `baPropUnit2mixed_holds` (constant `3^d C₂ (1-c)^{-d}`); `σ₁ = σ₂` from
`baProp5s_holds` (constant `4 C_s Λ²(Λ²+1) S(d, c'(1-c))`). -/
theorem baProp7_holds (d : ℕ) (Λ κ c : ℝ) : BAProp7 d Λ κ c := by
  intro hd hΛ hκ hc0 hc1
  obtain ⟨Cs, hCs, c', hc', Hs⟩ := baProp5s_holds d Λ κ hd hΛ hκ
  obtain ⟨C₂, hC₂, H2⟩ := baPropUnit2mixed_holds d Λ κ hd hΛ hκ
  have h1c : 0 < 1 - c := by linarith
  have hS := baP8_S_pos d (by positivity : 0 < c' * (1 - c))
  refine ⟨max (C₂ * (3 : ℝ) ^ d * ((1 - c) ^ d)⁻¹)
      (4 * Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S d (c' * (1 - c)))),
    lt_max_of_lt_left (by positivity), ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ a r hrc
  have : NeZero L := ⟨by omega⟩
  have he : 0 < g ^ 2 + |1 - t| := by positivity
  have hu : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have hr0 : (0 : ℝ) ≤ (zdistD d L r : ℝ) ^ 2 := by positivity
  have hp : 0 ≤ (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by positivity
  by_cases hσ : σ₁ = σ₂
  · subst hσ
    have h := baP8_prop7_eq hg hgΛ ht0 ht1 hCs hc' hc0 hc1
      (fun x => BATheta d L g E m t σ₁ σ₁ 0 x)
      (fun x => Hs L hL g hg hgΛ E m hr t ht0 ht1 σ₁ x) a r hrc
    refine h.trans ?_
    gcongr
    exact le_max_right _ _
  · have hK : 0 ≤ C₂ * (g ^ 2 + |1 - t|)⁻¹ := by positivity
    set f : Zd d L → ℂ := fun x => BATheta d L g E m t σ₁ σ₂ 0 x with hf
    have hU : ∀ (x : Zd d L) (i j : Fin d),
        ‖f (x + Pi.single i 1 + Pi.single j 1) - f (x + Pi.single i 1)
            - f (x + Pi.single j 1) + f x‖
        ≤ (C₂ * (g ^ 2 + |1 - t|)⁻¹) * (((zdistD d L x : ℝ) + 1) ^ d)⁻¹ :=
      fun x i j => H2 L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ hσ x i j
    have hA : (0 : ℝ) ≤ zdistD d L a := Nat.cast_nonneg _
    set M : ℝ := max 0 ((1 - c) * (zdistD d L a : ℝ) - 2) with hMdef
    have hM : 0 ≤ M := le_max_left _ _
    have hball : ∀ z : Zd d L, zdistD d L (z - a) ≤ zdistD d L r →
        (∀ w : Zd d L, zdistD d L (w - z) ≤ 2 → M ≤ (zdistD d L w : ℝ)) := by
      intro z hz w hw
      have h1 : zdistD d L a ≤ zdistD d L w + zdistD d L (w - a) := baP8_tri a w
      have h2 : zdistD d L (w - a) ≤ zdistD d L (w - z) + zdistD d L (z - a) := by
        have h := zdistD_add_le d L (w - z) (z - a)
        have e1 : w - z + (z - a) = w - a := by abel
        rwa [e1] at h
      have h3 : (zdistD d L a : ℝ) ≤ zdistD d L w + (zdistD d L r + 2) := by
        have : zdistD d L a ≤ zdistD d L w + (zdistD d L r + 2) := by omega
        exact_mod_cast this
      refine max_le (Nat.cast_nonneg _) ?_
      nlinarith
    have key := baP8_second hL f (fun x => ∀ w : Zd d L, zdistD d L (w - x) ≤ 2 →
        M ≤ (zdistD d L w : ℝ))
      ((C₂ * (g ^ 2 + |1 - t|)⁻¹) * ((M + 1) ^ d)⁻¹) (fun x u e hu he hx =>
        baP8_unitQ hL f (C₂ * (g ^ 2 + |1 - t|)⁻¹) hK d hU M hM x u e hu he hx)
      (zdistD d L r) r a rfl hball
    have hconv := baP8_conv2 hc0 hc1 (zdistD d L a : ℝ) hA d
    have hfin : (zdistD d L r : ℝ) ^ 2 * ((C₂ * (g ^ 2 + |1 - t|)⁻¹) * ((M + 1) ^ d)⁻¹)
        ≤ (zdistD d L r : ℝ) ^ 2 * ((C₂ * (g ^ 2 + |1 - t|)⁻¹)
          * ((3 : ℝ) ^ d * (((1 - c) ^ d)⁻¹) * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hconv hK) hr0
    refine key.trans (hfin.trans ?_)
    calc (zdistD d L r : ℝ) ^ 2 * ((C₂ * (g ^ 2 + |1 - t|)⁻¹)
          * ((3 : ℝ) ^ d * (((1 - c) ^ d)⁻¹) * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹))
        = (C₂ * (3 : ℝ) ^ d * ((1 - c) ^ d)⁻¹) * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2
          * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by ring
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _

/-- **Property 8 of `lem_propTH` for `Θ_BA`, all charge pairs** (`BAProp8`): `σ₁ ≠ σ₂` is
`baProp8mixed_holds`; `σ₁ = σ₂` from `baProp5s_holds`, the translation invariance of `BATheta`
(`baP8_BATheta_shift`) and `Σ_b e^{-c'|b|} ≤ expC (d-2) c'`. -/
theorem baProp8_holds (d : ℕ) (Λ κ : ℝ) : BAProp8 d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨Cs, hCs, c', hc', Hs⟩ := baProp5s_holds d Λ κ hd hΛ hκ
  obtain ⟨Cm, hCm, Hm⟩ := baProp8mixed_holds d Λ κ hd hΛ hκ
  have hS := baP8_S_pos (d - 2) hc'
  have hE0 : 0 ≤ RBM.expC (d - 2) c' := by unfold RBM.expC; positivity
  refine ⟨max Cm (Cs * (Λ ^ 2 + 1) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) c')
      + Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2) * (Λ ^ 2 + 1)),
    lt_max_of_lt_left hCm, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ a
  have : NeZero L := ⟨by omega⟩
  have hu : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have hp : 0 ≤ (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  by_cases hσ : σ₁ = σ₂
  · subst hσ
    have h := baP8_prop8_eq (by omega) hL hg hgΛ ht0 ht1 hCs hc'
      (BATheta d L g E m t σ₁ σ₁) (baP8_BATheta_shift g E m t σ₁ σ₁)
      (fun x => Hs L hL g hg hgΛ E m hr t ht0 ht1 σ₁ x) a
    have h' : ‖BATheta0 d L g E m t σ₁ σ₁ 0 a‖
        ≤ (Cs * (Λ ^ 2 + 1) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) c')
          + Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2) * (Λ ^ 2 + 1))
          * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by
      simpa only [BATheta0, Matrix.of_apply] using h
    refine h'.trans ?_
    calc _ = (Cs * (Λ ^ 2 + 1) + Cs * (Λ ^ 2 * (Λ ^ 2 + 1) * baP8_S (d - 2) c')
          + Cs * (1 + Λ ^ 2 * RBM.expC (d - 2) c') * ((d : ℝ) + 1) ^ (d - 2) * (Λ ^ 2 + 1))
          * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by ring
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _
  · exact Hm L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ hσ a |>.trans (by
      have : (0 : ℝ) ≤ (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
      calc Cm * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹
          = Cm * ((g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := by ring
        _ ≤ _ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) this)

/-- **Properties 5-8 of `lem_propTH` for the block Anderson model, the bundle** (`BAProp5to8`), for every
`(d, Λ, κ, c)`, all four charge pairs. -/
theorem baProp5to8_holds (d : ℕ) (Λ κ c : ℝ) : BAProp5to8 d Λ κ c :=
  ⟨baProp5_holds d Λ κ, baProp5s_holds d Λ κ, baProp6_holds d Λ κ c, baProp7_holds d Λ κ c,
    baProp8_holds d Λ κ⟩

/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, flow point `P`)

`P : FlowPt 4 10` is the merged real-axis flow point (`MFixedPoint.lean:893`): `P.g0 ∈ (0, 10]`, a real energy
`P.E`, `P.m0` solving `(self_m)` with `Im m₀ > 0` (`P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m0`), `card (Zd 3 4) = 64`.
Every deterministic hypothesis is discharged; nothing is left open.  `a = (2,0,0)`, `r = (1,0,0)`:
`|a| = 2`, `|r| = 1 ≤ (1/2) |a|` (the window of 6, 7 is not collapsed; at `a = (1,0,0)`, `c = 1/2` it would be). -/

namespace Prop6PathInst

open RBM.BA.MFixedPointInst RBM.BA.FlowPinsInst

/-- The bundle at `(d, Λ, κ, c) = (3, 10, Im m₀, 1/2)`. -/
theorem inst_bundle : BAProp5to8 3 10 P.m0.im (1 / 2) := baProp5to8_holds 3 10 P.m0.im (1 / 2)

/-- The four properties at the `FlowPins` instances (mixed charge `σ = (+,-)`, `t = 1/2`, `a = (2,0,0)`). -/
example := inst_BAProp5 (baProp5_holds 3 10 P.m0.im)

example := inst_BAProp6 (baProp6_holds 3 10 P.m0.im (1 / 2))

example := inst_BAProp7 (baProp7_holds 3 10 P.m0.im (1 / 2))

example := inst_BAProp8 (baProp8_holds 3 10 P.m0.im)

/-- Property 5 at equal charges `σ = (-,-)`, `t = 1/2`, `a = (2,0,0)`. -/
theorem inst_prop5_eq : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 ![2, 0, 0]‖ ≤
      C * Bparam 3 4 P.g0 (1 / 2) (zdistD 3 4 (![2, 0, 0] : Zd 3 4)) *
        Real.exp (-c * (zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) / ellT 4 P.g0 (1 / 2)) := by
  obtain ⟨C, hC, c, hc, H⟩ := baProp5_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, c, hC, hc, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    (by norm_num) (by norm_num) false false _⟩

/-- Property 5 at equal charges `σ = (+,+)`, `a = 0` (the indicator term of the short bound). -/
theorem inst_prop5_eq_zero : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 0‖ ≤
      C * Bparam 3 4 P.g0 (1 / 2) (zdistD 3 4 (0 : Zd 3 4)) *
        Real.exp (-c * (zdistD 3 4 (0 : Zd 3 4) : ℝ) / ellT 4 P.g0 (1 / 2)) := by
  obtain ⟨C, hC, c, hc, H⟩ := baProp5_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, c, hC, hc, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    (by norm_num) (by norm_num) true true 0⟩

/-- Property 6 at equal charges `σ = (-,-)`, `a = (2,0,0)`, `r = (1,0,0)`. -/
theorem inst_prop6_eq : ∃ C : ℝ, 0 < C ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 (![2, 0, 0] + ![1, 0, 0]) -
        BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 ![2, 0, 0]‖ ≤
      C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) *
        (((zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baProp6_holds 3 10 P.m0.im (1 / 2) (by norm_num) (by norm_num) P.real.1.1
    (by norm_num) (by norm_num)
  refine ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num) false false ![2, 0, 0] ![1, 0, 0] ?_⟩
  rw [zd_a, zd_r]
  norm_num

/-- Property 7 at equal charges `σ = (+,+)`, `a = (2,0,0)`, `r = (1,0,0)`. -/
theorem inst_prop7_eq : ∃ C : ℝ, 0 < C ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 (![2, 0, 0] + ![1, 0, 0]) +
        BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 (![2, 0, 0] - ![1, 0, 0]) -
        2 * BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 ![2, 0, 0]‖ ≤
      C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) ^ 2 *
        (((zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := baProp7_holds 3 10 P.m0.im (1 / 2) (by norm_num) (by norm_num) P.real.1.1
    (by norm_num) (by norm_num)
  refine ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num) true true ![2, 0, 0] ![1, 0, 0] ?_⟩
  rw [zd_a, zd_r]
  norm_num

/-- Property 8 at equal charges `σ = (-,-)`, `a = (1,0,0)`. -/
theorem inst_prop8_eq : ∃ C : ℝ, 0 < C ∧
    ‖BATheta0 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 ![1, 0, 0]‖ ≤
      C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baProp8_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num) false false _⟩

/-- **One `σ₁ = σ₂` reduction at concrete numbers**, (5): `d = 3`, `L = 4`, `a = (1,0,0)`, `σ = (+,+)`,
`t = 1/2`, `Λ = 10`, `c₅ = c'/2`: `|Θ(0,a)| ≤ C_s max(..) B_{t,|a|} e^{-c₅|a|/ℓ_t}` from `baProp5s_holds`. -/
theorem inst_reduction5 : ∃ Cs c' : ℝ, 0 < Cs ∧ 0 < c' ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 ![1, 0, 0]‖
      ≤ (Cs * max (((10 : ℝ) ^ 2 + 1) * ((10 : ℝ) ^ 2 + 1))
          ((10 : ℝ) ^ 2 * ((10 : ℝ) ^ 2 + 1) * baP8_S (3 - 2) (c' / 2)))
        * Bparam 3 4 P.g0 (1 / 2) (zdistD 3 4 (![1, 0, 0] : Zd 3 4))
        * Real.exp (-(c' / 2) * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) / ellT 4 P.g0 (1 / 2)) := by
  obtain ⟨Cs, hCs, c', hc', H⟩ := baProp5s_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨Cs, c', hCs, hc', baP8_prop5_eq (by norm_num) P.g0_pos P.g0_le (by norm_num)
    (by norm_num) hCs hc' (by positivity) le_rfl
    (fun x => BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 x) ![1, 0, 0]
    (H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
      (by norm_num) true _)⟩

/-- A `σ₁ = σ₂` reduction at concrete numbers, (6): `a = (2,0,0)`, `r = (1,0,0)`, `c = 1/2`, `σ = (-,-)`. -/
theorem inst_reduction6 : ∃ Cs c' : ℝ, 0 < Cs ∧ 0 < c' ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 (![2, 0, 0] + ![1, 0, 0]) -
        BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 ![2, 0, 0]‖
      ≤ (2 * Cs * ((10 : ℝ) ^ 2 * ((10 : ℝ) ^ 2 + 1) * baP8_S (3 - 1) (c' * (1 - 1 / 2))))
        * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ)
        * (((zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨Cs, hCs, c', hc', H⟩ := baProp5s_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  refine ⟨Cs, c', hCs, hc', baP8_prop6_eq P.g0_pos P.g0_le (by norm_num) (by norm_num) hCs hc'
    (by norm_num) (by norm_num) (fun x => BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 x)
    (fun x => H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
      (by norm_num) false x) ![2, 0, 0] ![1, 0, 0] ?_⟩
  rw [zd_a, zd_r]
  norm_num

/-- A `σ₁ = σ₂` reduction at concrete numbers, (8): `a = (1,0,0)`, `σ = (+,+)`; the zero mode `L^{-2d} Σ Σ Θ`
is removed by translation invariance (`baP8_BATheta_shift`). -/
theorem inst_reduction8 : ∃ Cs c' : ℝ, 0 < Cs ∧ 0 < c' ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 ![1, 0, 0]
        - (((4 : ℕ) : ℂ) ^ (2 * 3))⁻¹ * ∑ a', ∑ b', BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true a' b'‖
      ≤ (Cs * ((10 : ℝ) ^ 2 + 1) + Cs * ((10 : ℝ) ^ 2 * ((10 : ℝ) ^ 2 + 1) * baP8_S (3 - 2) c')
          + Cs * (1 + (10 : ℝ) ^ 2 * RBM.expC (3 - 2) c') * (((3 : ℕ) : ℝ) + 1) ^ (3 - 2)
            * ((10 : ℝ) ^ 2 + 1))
        * ((P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹
          * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 2))⁻¹) := by
  obtain ⟨Cs, hCs, c', hc', H⟩ := baProp5s_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨Cs, c', hCs, hc', baP8_prop8_eq (by norm_num) (by norm_num) P.g0_pos P.g0_le (by norm_num)
    (by norm_num) hCs hc' (BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true)
    (baP8_BATheta_shift P.g0 P.E P.m0 (1 / 2) true true)
    (fun x => H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
      (by norm_num) true x) ![1, 0, 0]⟩

end Prop6PathInst

end RBM.BA
