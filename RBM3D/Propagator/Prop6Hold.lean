/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.PropUnit
import RBM3D.Propagator.Gap

/-!
# Properties 6 and 7 of `lem_propTH` from the unit differences; the bundle `Prop5to8`
(route H, ticket T2027, the last ticket of gate PT; design `T2003` split row G, Fable review
`docs/claude-team/fable/2026-10-02-routeH.md` F7)

The merged `propUnit1_holds` / `propUnit2_holds` bound the unit first difference and the unit
second differences of `Θ` by `C (g² + |1-t|)⁻¹ (|a|+1)^{-(d-1)}` resp. `(|a|+1)^{-d}`.  Here the
pins `Prop6Diff1` (`(prop:BD1)`) and `Prop7Diff2` (`(prop:BD2)`) follow by a path argument on
`ℤ_L^d`, for `|r| ≤ c |a|`, `0 < c < 1`.

* **P6.**  Write `r` as `n = |r|` unit steps (`exists_step`); every point `a + s_k` of the path
  has `|a + s_k| ≥ |a| - n ≥ (1-c)|a|` and `(1-c)|a| + 1 ≥ (1-c)(|a|+1)`; the telescoping sum of
  `n` unit differences (a step `-e_j` is a forward step at the shifted base point) gives
  `C₁ (1-c)^{-(d-1)} n (g²+e)⁻¹ (|a|+1)^{-(d-1)}`.
* **P7.**  With `r = r' + e`, `|r'| = n - 1`, `|e| = 1`, and `G = D_e f`:
  `Δ²_r f(a) = Δ²_{r'} f(a) + [G(a-e) - G(a-e-r')] + [G(a-e+r') - G(a-e)] + [G(a+r') - G(a-e+r')]`,
  the two brackets in the middle being first differences of `G` along `r'` (P6 path lemma, with
  all path points within `n` of `a`) and the last one a unit second difference.  The count is
  `(n-1)² + 2(n-1) + 1 = n²`; each unit second difference is taken at a base point within
  `2` of a path point (sign shifts), so the lower bound `|·| ≥ (1-c)|a| - 2` and the elementary
  conversion `max(1, (1-c)|a| - 1) ≥ (1-c)(|a|+1)/3` give the constant `3^d C₂ (1-c)^{-d}`.

## Main results

* `RBM.prop6Diff1_holds`, `RBM.prop7Diff2_holds`: `∀ d Λ κ c, Prop6Diff1 d Λ κ c`, resp.
  `Prop7Diff2 d Λ κ c`.
* `RBM.prop5to8_holds`: `∀ d Λ κ c, Prop5to8 d Λ κ c`.
* `RBM.thetaDecay_holds`, `RBM.thetaDecayShort_holds`: the old interface forms, for all `d g m`.
* `RBM.thetaZeroMode_holds`: `ThetaZeroMode d g (PropSpin m σ₁ * PropSpin m σ₂)` with exactly the
  hypotheses of the bridge `Prop8ZeroMode.thetaZeroMode`; `RBM.thetaZeroMode_unit_holds`:
  `ThetaZeroMode d g μ` for every `d g μ` (the bridge reaches every unit `μ`).
-/

namespace RBM

section PathLemmas

variable {d L : ℕ} [NeZero L]

/-- `|a| ≤ |z| + |z - a|`. -/
private lemma p6h_tri (a z : Zd d L) :
    zdistD d L a ≤ zdistD d L z + zdistD d L (z - a) := by
  have h := zdistD_add_le d L z (a - z)
  have e1 : z + (a - z) = a := by abel
  have e2 : zdistD d L (a - z) = zdistD d L (z - a) := by rw [← neg_sub z a, zdistD_neg]
  rw [e1, e2] at h
  exact h

/-- **The path lemma.**  If every unit step between two good points changes `G` by at most `B`,
then `G(a + r) - G(a)` is at most `|r| B` whenever every point within `|r|` of `a` is good. -/
private theorem p6h_path (hL : 3 ≤ L) (G : Zd d L → ℂ) (P : Zd d L → Prop) (B : ℝ)
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
private theorem p6h_unit (hL : 3 ≤ L) (f : Zd d L → ℂ) (K : ℝ) (hK : 0 ≤ K) (p : ℕ)
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
private theorem p6h_bound (hL : 3 ≤ L) (f : Zd d L → ℂ) (K : ℝ) (hK : 0 ≤ K) (p : ℕ)
    (hU : ∀ (x : Zd d L) (j : Fin d),
      ‖f (x + Pi.single j 1) - f x‖ ≤ K * (((zdistD d L x : ℝ) + 1) ^ p)⁻¹)
    (M : ℝ) (hM : 0 ≤ M) (a r : Zd d L)
    (hr : (zdistD d L r : ℝ) + M ≤ (zdistD d L a : ℝ)) :
    ‖f (a + r) - f a‖ ≤ (zdistD d L r : ℝ) * (K * ((M + 1) ^ p)⁻¹) := by
  refine p6h_path hL f (fun z => M ≤ (zdistD d L z : ℝ)) (K * ((M + 1) ^ p)⁻¹) ?_
    (zdistD d L r) r a rfl ?_
  · intro x e he hx hxe
    exact p6h_unit hL f K hK p hU M hM x e he hx hxe
  · intro z hz
    have h : (zdistD d L a : ℝ) ≤ zdistD d L z + zdistD d L (z - a) := by
      exact_mod_cast p6h_tri a z
    have hz' : (zdistD d L (z - a) : ℝ) ≤ zdistD d L r := by exact_mod_cast hz
    change M ≤ (zdistD d L z : ℝ)
    linarith

/-! ### The second difference `Q f x u e` and the sign shifts -/

/-- `f(x+u+e) - f(x+u) - f(x+e) + f(x)`: the second difference with increments `u`, `e` at `x`. -/
private def p6hQ (f : Zd d L → ℂ) (x u e : Zd d L) : ℂ :=
  f (x + u + e) - f (x + u) - f (x + e) + f x

omit [NeZero L] in
private lemma p6hQ_comm (f : Zd d L → ℂ) (x u e : Zd d L) :
    p6hQ f x u e = p6hQ f x e u := by
  unfold p6hQ
  rw [add_right_comm x u e]
  ring

omit [NeZero L] in
/-- `D_{-v} D_e f (x) = - D_v D_e f (x - v)`. -/
private lemma p6hQ_neg_left (f : Zd d L → ℂ) (x v e : Zd d L) :
    p6hQ f x (-v) e = - p6hQ f (x - v) v e := by
  unfold p6hQ
  have h1 : x - v + v + e = x + e := by abel
  have h2 : x - v + v = x := by abel
  have h3 : x - v + e = x + -v + e := by abel
  have h4 : x - v = x + -v := by abel
  rw [h1, h2, h3, h4]
  ring

/-- The unit second differences `Q(x, e_i, e_j)` give `Q(x, u, e)` for all units `u, e = ±e_j`
at a base point within `2` of `x`, up to sign. -/
private theorem p6h_reduce (hL : 3 ≤ L) (f : Zd d L → ℂ) (x u e : Zd d L)
    (hu : zdistD d L u = 1) (he : zdistD d L e = 1) :
    ∃ (x' : Zd d L) (i j : Fin d), zdistD d L (x' - x) ≤ 2 ∧
      ‖p6hQ f x u e‖ = ‖p6hQ f x' (Pi.single i 1) (Pi.single j 1)‖ := by
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
    · rw [eF, eF, p6hQ_neg_left, p6hQ_comm f (x - Pi.single i 1) (Pi.single i 1)
        (-Pi.single j 1), p6hQ_neg_left, norm_neg, norm_neg, p6hQ_comm]
  · -- `u = -e_i`, `e = +e_j`
    refine ⟨x - Pi.single i 1, i, j, ?_, ?_⟩
    · have : x - Pi.single i 1 - x = -Pi.single i 1 := by abel
      rw [this, zdistD_neg, hv]
      omega
    · rw [eF, eT, p6hQ_neg_left, norm_neg]
  · -- `u = +e_i`, `e = -e_j`
    refine ⟨x - Pi.single j 1, i, j, ?_, ?_⟩
    · have : x - Pi.single j 1 - x = -Pi.single j 1 := by abel
      rw [this, zdistD_neg, hv]
      omega
    · rw [eT, eF, p6hQ_comm, p6hQ_neg_left, norm_neg, p6hQ_comm]
  · refine ⟨x, i, j, ?_, ?_⟩
    · simp
    · rw [eT, eT]

/-- **Unit second difference at any units and any base with a good ball.**  The ball condition
`∀ w, |w - x| ≤ 2 → M ≤ |w|` covers the shifted base point of the sign reduction. -/
private theorem p6h_unitQ (hL : 3 ≤ L) (f : Zd d L → ℂ) (K : ℝ) (hK : 0 ≤ K) (q : ℕ)
    (hU : ∀ (x : Zd d L) (i j : Fin d),
      ‖f (x + Pi.single i 1 + Pi.single j 1) - f (x + Pi.single i 1)
          - f (x + Pi.single j 1) + f x‖ ≤ K * (((zdistD d L x : ℝ) + 1) ^ q)⁻¹)
    (M : ℝ) (hM : 0 ≤ M) (x u e : Zd d L) (hu : zdistD d L u = 1) (he : zdistD d L e = 1)
    (hball : ∀ w : Zd d L, zdistD d L (w - x) ≤ 2 → M ≤ (zdistD d L w : ℝ)) :
    ‖p6hQ f x u e‖ ≤ K * ((M + 1) ^ q)⁻¹ := by
  obtain ⟨x', i, j, hx', hnorm⟩ := p6h_reduce hL f x u e hu he
  rw [hnorm]
  have h1 := hU x' i j
  have h2 : M ≤ (zdistD d L x' : ℝ) := hball x' hx'
  refine le_trans h1 ?_
  refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hK
  exact pow_le_pow_left₀ (by linarith) (by linarith) q

/-- **P7 core.**  With a good ball of radius `|r|` around `a` (good = unit second differences
bounded by `B` at the base point), `|f(a+r) + f(a-r) - 2 f(a)| ≤ |r|² B`. -/
private theorem p6h_second (hL : 3 ≤ L) (f : Zd d L → ℂ) (P : Zd d L → Prop) (B : ℝ)
    (hQ : ∀ x u e : Zd d L, zdistD d L u = 1 → zdistD d L e = 1 → P x →
      ‖p6hQ f x u e‖ ≤ B) :
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
      have : G (x + u) - G x = p6hQ f x u e := by
        simp only [hG, p6hQ]
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
    have hT2 := p6h_path hL G P B hGU n r' (a - e) hr' hball1
    -- T1: `G(a - e) - G(a - e - r')`
    have hT1 := p6h_path hL G P B hGU n (-r') (a - e) (by rw [zdistD_neg, hr']) hball1
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
private lemma p6h_conv1 {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (A : ℝ) (hA : 0 ≤ A) (p : ℕ) :
    (((1 - c) * A + 1) ^ p)⁻¹ ≤ (((1 - c) ^ p)⁻¹) * ((A + 1) ^ p)⁻¹ := by
  have h1 : 0 < 1 - c := by linarith
  have h2 : (1 - c) * (A + 1) ≤ (1 - c) * A + 1 := by nlinarith
  calc (((1 - c) * A + 1) ^ p)⁻¹ ≤ (((1 - c) * (A + 1)) ^ p)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2 p)
    _ = (((1 - c) ^ p)⁻¹) * ((A + 1) ^ p)⁻¹ := by rw [mul_pow, mul_inv]

/-- The P7 conversion: `max (1, (1-c)A - 1) ≥ (1-c)(A+1)/3`, i.e. with `M = max 0 ((1-c)A - 2)`,
`(M+1)^{-p} ≤ 3^p (1-c)^{-p} (A+1)^{-p}`. -/
private lemma p6h_conv2 {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (A : ℝ) (hA : 0 ≤ A) (p : ℕ) :
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

/-- **Property 6** (`(prop:BD1)`): `|Θ_t(0,a+r) - Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r| (|a|+1)^{-(d-1)}`
for `|r| ≤ c|a|`, `0 < c < 1`; constant `C₁ (1-c)^{-(d-1)}`, no loss. -/
theorem prop6Diff1_holds (d : ℕ) (Λ κ c : ℝ) : Prop6Diff1 d Λ κ c := by
  intro hd hΛ hκ hc0 hc1
  obtain ⟨C₁, hC₁, H1⟩ := propUnit1_holds d Λ κ hd hΛ hκ
  have h1c : 0 < 1 - c := by linarith
  refine ⟨C₁ * ((1 - c) ^ (d - 1))⁻¹, by positivity, ?_⟩
  intro L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ a r hr
  have : NeZero L := ⟨by omega⟩
  have he : 0 < g ^ 2 + |1 - t| := by positivity
  have hK : 0 ≤ C₁ * (g ^ 2 + |1 - t|)⁻¹ := by positivity
  set f : Zd d L → ℂ :=
    fun x => Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 x with hf
  have hU : ∀ (x : Zd d L) (j : Fin d), ‖f (x + Pi.single j 1) - f x‖
      ≤ (C₁ * (g ^ 2 + |1 - t|)⁻¹) * (((zdistD d L x : ℝ) + 1) ^ (d - 1))⁻¹ :=
    fun x j => H1 L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ x j
  have hA : (0 : ℝ) ≤ zdistD d L a := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (1 - c) * (zdistD d L a : ℝ) := by positivity
  have key := p6h_bound hL f (C₁ * (g ^ 2 + |1 - t|)⁻¹) hK (d - 1) hU
    ((1 - c) * (zdistD d L a : ℝ)) hM a r (by nlinarith)
  have hconv := p6h_conv1 hc0 hc1 (zdistD d L a : ℝ) hA (d - 1)
  have hr0 : (0 : ℝ) ≤ zdistD d L r := Nat.cast_nonneg _
  have hfin : (zdistD d L r : ℝ) * ((C₁ * (g ^ 2 + |1 - t|)⁻¹)
        * ((((1 - c) * (zdistD d L a : ℝ)) + 1) ^ (d - 1))⁻¹)
      ≤ (zdistD d L r : ℝ) * ((C₁ * (g ^ 2 + |1 - t|)⁻¹)
        * (((1 - c) ^ (d - 1))⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hconv hK) hr0
  refine key.trans (hfin.trans (le_of_eq ?_))
  ring

/-- **Property 7** (`(prop:BD2)`): `|Θ_t(0,a+r) + Θ_t(0,a-r) - 2Θ_t(0,a)|
≤ C (g²+|1-t|)⁻¹ |r|² (|a|+1)^{-d}` for `|r| ≤ c|a|`, `0 < c < 1`; constant
`3^d C₂ (1-c)^{-d}`, no loss. -/
theorem prop7Diff2_holds (d : ℕ) (Λ κ c : ℝ) : Prop7Diff2 d Λ κ c := by
  intro hd hΛ hκ hc0 hc1
  obtain ⟨C₂, hC₂, H2⟩ := propUnit2_holds d Λ κ hd hΛ hκ
  have h1c : 0 < 1 - c := by linarith
  refine ⟨C₂ * (3 : ℝ) ^ d * ((1 - c) ^ d)⁻¹, by positivity, ?_⟩
  intro L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ a r hr
  have : NeZero L := ⟨by omega⟩
  have he : 0 < g ^ 2 + |1 - t| := by positivity
  have hK : 0 ≤ C₂ * (g ^ 2 + |1 - t|)⁻¹ := by positivity
  set f : Zd d L → ℂ :=
    fun x => Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 x with hf
  have hU : ∀ (x : Zd d L) (i j : Fin d),
      ‖f (x + Pi.single i 1 + Pi.single j 1) - f (x + Pi.single i 1)
          - f (x + Pi.single j 1) + f x‖
      ≤ (C₂ * (g ^ 2 + |1 - t|)⁻¹) * (((zdistD d L x : ℝ) + 1) ^ d)⁻¹ :=
    fun x i j => H2 L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ x i j
  have hA : (0 : ℝ) ≤ zdistD d L a := Nat.cast_nonneg _
  set M : ℝ := max 0 ((1 - c) * (zdistD d L a : ℝ) - 2) with hMdef
  have hM : 0 ≤ M := le_max_left _ _
  have hball : ∀ z : Zd d L, zdistD d L (z - a) ≤ zdistD d L r →
      (∀ w : Zd d L, zdistD d L (w - z) ≤ 2 → M ≤ (zdistD d L w : ℝ)) := by
    intro z hz w hw
    have h1 : zdistD d L a ≤ zdistD d L w + zdistD d L (w - a) := p6h_tri a w
    have h2 : zdistD d L (w - a) ≤ zdistD d L (w - z) + zdistD d L (z - a) := by
      have h := zdistD_add_le d L (w - z) (z - a)
      have e1 : w - z + (z - a) = w - a := by abel
      rwa [e1] at h
    have h3 : (zdistD d L a : ℝ) ≤ zdistD d L w + (zdistD d L r + 2) := by
      have : zdistD d L a ≤ zdistD d L w + (zdistD d L r + 2) := by omega
      exact_mod_cast this
    refine max_le (Nat.cast_nonneg _) ?_
    nlinarith
  have key := p6h_second hL f (fun x => ∀ w : Zd d L, zdistD d L (w - x) ≤ 2 →
      M ≤ (zdistD d L w : ℝ))
    ((C₂ * (g ^ 2 + |1 - t|)⁻¹) * ((M + 1) ^ d)⁻¹) (fun x u e hu he hx =>
      p6h_unitQ hL f (C₂ * (g ^ 2 + |1 - t|)⁻¹) hK d hU M hM x u e hu he hx)
    (zdistD d L r) r a rfl hball
  have hconv := p6h_conv2 hc0 hc1 (zdistD d L a : ℝ) hA d
  have hr0 : (0 : ℝ) ≤ (zdistD d L r : ℝ) ^ 2 := by positivity
  have hfin : (zdistD d L r : ℝ) ^ 2 * ((C₂ * (g ^ 2 + |1 - t|)⁻¹) * ((M + 1) ^ d)⁻¹)
      ≤ (zdistD d L r : ℝ) ^ 2 * ((C₂ * (g ^ 2 + |1 - t|)⁻¹)
        * ((3 : ℝ) ^ d * (((1 - c) ^ d)⁻¹) * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hconv hK) hr0
  refine key.trans (hfin.trans (le_of_eq ?_))
  ring

/-! ### The bundle and the old interface forms -/

/-- **Properties 5-8 of `lem_propTH`** for every `(d, Λ, κ, c)`: the five proved pins. -/
theorem prop5to8_holds (d : ℕ) (Λ κ c : ℝ) : Prop5to8 d Λ κ c :=
  ⟨prop5Decay_holds d Λ, prop5Short_holds d Λ κ, prop6Diff1_holds d Λ κ c,
    prop7Diff2_holds d Λ κ c, prop8ZeroMode_holds d Λ κ⟩

/-- The merged interface `ThetaDecay d g m` (all `d g m`), through the bridge at `Λ = g`. -/
theorem thetaDecay_holds (d : ℕ) (g : ℝ) (m : ℂ) : ThetaDecay d g m :=
  (prop5Decay_holds d g).thetaDecay m

/-- The merged interface `ThetaDecayShort d g m` (all `d g m`), through the bridge at
`Λ = g`, `κ = Im m`. -/
theorem thetaDecayShort_holds (d : ℕ) (g : ℝ) (m : ℂ) : ThetaDecayShort d g m :=
  Prop5Short.thetaDecayShort (prop5Short_holds d g m.im)

/-- The merged interface `ThetaZeroMode d g μ`, `μ = m(σ₁) m(σ₂)`, with exactly the hypotheses
of the bridge `Prop8ZeroMode.thetaZeroMode`. -/
theorem thetaZeroMode_holds (d : ℕ) {Λ κ g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ)
    {m : ℂ} (hm : ‖m‖ = 1) (hmi : κ ≤ m.im) (σ₁ σ₂ : Bool) :
    ThetaZeroMode d g (PropSpin m σ₁ * PropSpin m σ₂) :=
  (prop8ZeroMode_holds d Λ κ).thetaZeroMode hg hgΛ hκ hm hmi σ₁ σ₂

private lemma p6h_exists_sq (μ : ℂ) (hμ : ‖μ‖ = 1) : ∃ n : ℂ, ‖n‖ = 1 ∧ n * n = μ := by
  refine ⟨Complex.exp (↑(Complex.arg μ / 2) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_add]
  have h2 : (↑(Complex.arg μ / 2) * Complex.I + ↑(Complex.arg μ / 2) * Complex.I : ℂ)
      = ↑(Complex.arg μ) * Complex.I := by push_cast; ring
  rw [h2]
  have h := Complex.norm_mul_exp_arg_mul_I μ
  rw [hμ] at h
  simpa using h

/-- Every unit `μ` is `m(σ₁) m(σ₂)` for some `m` in the bulk (`Im m > 0`, `‖m‖ = 1`): `μ = 1` is
`m = I`, `(σ₁, σ₂) = (+, -)`; otherwise `m` is a square root of `μ` with positive imaginary part
and `σ₁ = σ₂ = +`. -/
private lemma p6h_exists_spin (μ : ℂ) (hμ : ‖μ‖ = 1) :
    ∃ (m : ℂ) (σ₁ σ₂ : Bool), ‖m‖ = 1 ∧ 0 < m.im ∧ PropSpin m σ₁ * PropSpin m σ₂ = μ := by
  by_cases h1 : μ = 1
  · refine ⟨Complex.I, true, false, Complex.norm_I, by simp, ?_⟩
    simp [PropSpin, h1]
  · obtain ⟨n, hn, hnn⟩ := p6h_exists_sq μ hμ
    have him : n.im ≠ 0 := by
      intro h0
      apply h1
      have hnre : n = (n.re : ℂ) := Complex.ext (by simp) (by simp [h0])
      have hre : n.re * n.re = 1 := by
        have h := hn
        rw [hnre, Complex.norm_real, Real.norm_eq_abs] at h
        nlinarith [abs_mul_abs_self n.re, h]
      rw [← hnn, hnre]
      simpa using congrArg (fun x : ℝ => (x : ℂ)) hre
    rcases lt_or_gt_of_ne him with hneg | hpos
    · refine ⟨-n, true, true, by simpa using hn, by simpa using hneg, ?_⟩
      simp [PropSpin, ← hnn]
    · exact ⟨n, true, true, hn, hpos, by simp [PropSpin, ← hnn]⟩

/-- `ThetaZeroMode d g μ` for every `d g μ`: the bridge reaches every unit `μ`
(`p6h_exists_spin`), at `Λ = g`, `κ = Im m`. -/
theorem thetaZeroMode_unit_holds (d : ℕ) (g : ℝ) (μ : ℂ) : ThetaZeroMode d g μ := by
  intro hd hg hμ τ hτ
  obtain ⟨m, σ₁, σ₂, hm, hmi, hμm⟩ := p6h_exists_spin μ hμ
  have h := thetaZeroMode_holds d hg le_rfl hmi hm le_rfl σ₁ σ₂
  rw [hμm] at h
  exact h hd hg hμ τ hτ

/-! ### Nonempty instances

Every target is applied at `d = 3`, `L = 9`, `g = 1/2`, `t = 9/10`, `m = I`, `(σ₁, σ₂) = (+, -)`
(`μ = m m̄ = 1`, `ξ = 0.9`), `a = (4, 0, 0)`, `r = (1, 0, 0)`: `|a| = 4`, `|r| = 1 ≤ (1/2)·4`; all
deterministic hypotheses are discharged, none is another gate's pin. -/

private lemma p6h_inst_a : zdistD 3 9 (![4, 0, 0] : Zd 3 9) = 4 := by decide

private lemma p6h_inst_r : zdistD 3 9 (![1, 0, 0] : Zd 3 9) = 1 := by decide

private lemma p6h_inst_hr :
    (zdistD 3 9 (![1, 0, 0] : Zd 3 9) : ℝ)
      ≤ (1 / 2 : ℝ) * (zdistD 3 9 (![4, 0, 0] : Zd 3 9) : ℝ) := by
  rw [p6h_inst_a, p6h_inst_r]
  norm_num

example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((![4, 0, 0] : Zd 3 9) + ![1, 0, 0])
        - Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (![4, 0, 0] : Zd 3 9)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹ * (zdistD 3 9 (![1, 0, 0] : Zd 3 9) : ℝ)
        * (((zdistD 3 9 (![4, 0, 0] : Zd 3 9) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop6Diff1_holds 3 1 (1 / 2) (1 / 2) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨C, hC, H 9 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false ![4, 0, 0] ![1, 0, 0]
    p6h_inst_hr⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((![4, 0, 0] : Zd 3 9) + ![1, 0, 0])
        + Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((![4, 0, 0] : Zd 3 9) - ![1, 0, 0])
        - 2 * Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (![4, 0, 0] : Zd 3 9)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹ * (zdistD 3 9 (![1, 0, 0] : Zd 3 9) : ℝ) ^ 2
        * (((zdistD 3 9 (![4, 0, 0] : Zd 3 9) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop7Diff2_holds 3 1 (1 / 2) (1 / 2) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨C, hC, H 9 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false ![4, 0, 0] ![1, 0, 0]
    p6h_inst_hr⟩

/-- The bundle at `(d, Λ, κ, c) = (3, 1, 1/2, 1/2)`, and its `diffOne` field. -/
example : Prop5to8 3 1 (1 / 2) (1 / 2) := prop5to8_holds 3 1 (1 / 2) (1 / 2)

example : Prop6Diff1 3 1 (1 / 2) (1 / 2) := (prop5to8_holds 3 1 (1 / 2) (1 / 2)).diffOne

example : ThetaDecay 3 (1 / 2) Complex.I := thetaDecay_holds 3 (1 / 2) Complex.I

example : ThetaDecayShort 3 (1 / 2) Complex.I := thetaDecayShort_holds 3 (1 / 2) Complex.I

example : ThetaZeroMode 3 (1 / 2) (PropSpin Complex.I true * PropSpin Complex.I false) :=
  thetaZeroMode_holds 3 (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < 1 / 2) Complex.norm_I (by norm_num) true false

example : ThetaZeroMode 3 (1 / 2) (-1) := thetaZeroMode_unit_holds 3 (1 / 2) (-1)

end RBM
