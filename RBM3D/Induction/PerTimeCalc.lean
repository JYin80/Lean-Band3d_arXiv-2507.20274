/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.StochDomAt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The `≺`-calculus for the per-time predicate `PerTimeDomAt`, the forbidden region and the
continuity bootstrap (ST-1, S1-08)

Ticket T2045.  Port of `RBM2D/Induction/PerTimeCalc.lean` at `c9a24cf` (lines 67-849: the
`PerTime` and `Unif` calculus, `forbidden_region`, `stepOneBootstrap`; the toy instances, the
compiled negative statements and the axiom audit of lines 851-1434 are not copied: the instances
of this file are those of section "Instances" below, at the merged `sz0`).  The file is dimension
free: `PerTimeDomAt`, `StochDomAt`, `HighProbAt`, `TimeIcc` are the merged scale-`size` vocabulary
of `RBM3D/Defs/StochDomAt.lean` (`size = sz.size = (W L)^d`), the proofs are the RBM2D proofs.
Paper: arXiv:2507.20274, Step 1 of `lem:main_ind` (`3_5:64-66`, "the same as [YY_25 section 5.1]").

## RBM1D sources (commit `86573b9`, as cited in the RBM2D file)

* `RBM1D/Loop/ContinuityAssembly.lean`, section `StochGeneric`:
  `StochDom.mono_right_eventually` (:540), `StochDom.rpow_of_le_one` (:549),
  `StochDom.sqrt_of` (:565), `StochDom.of_forall_rpow_mul` (:572),
  `sq_le_four_mul_of_le_add_mul` (:584), `StochDom.of_le_add_sqrt_mul` (:594),
  `StochDom.finset_sum_of` (:625).
* `RBM1D/Hierarchy/Step1.lean`, section `Generic`: `rpow_mul_rpow_neg_lt_one` (:114),
  `forbidden_region` (:123), `lt_of_forall_ne_of_continuousOn` (:151), `bootstrap` (:167,
  renamed `stepOneBootstrap`), `stochDom_of_indicator` (:188), `stochDom_of_forall_or` (:218),
  `stochDom_of_le_const_mul` (:230), `stochDom_of_le_left_eventually` (:236).
* `RBM1D/Defs/StochDomHighProb.lean`: `stochDom_of_highProb` (:25).
* `RBM1D/Hierarchy/Step45.lean`: `stochDom_min` (:109), `quad_le_one` (:121).

The base layer is public with the file-stem prefix `perTimeCalc_` (the merged
`RBM.StochDomAt.*`, `RBM.Gauss.HighProbAt.*` have other names and are not renamed).

## The hypothesis `hsize`

`hsize : Tendsto size atTop atTop` is present exactly in the lemmas that need
`2 x^{-(D+1)} ≤ x^{-D}`, `1 ≤ size l` or `C ≤ (size l)^{τ'}` eventually (for `sz : Sizes d` it is
`Sizes.tendsto_size`).  The per-time variant of `forbidden_region` is not stated: its conclusion is
a `HighProbAt` event with the union over `u` inside `P`, which the per-time hypothesis does not
control (RBM2D `pt_forbidden_region_fails`, `PerTimeCalc.lean:1290`).
-/

set_option linter.style.longLine false

namespace RBM.Ind.PerTimeCalc

open MeasureTheory Filter RBM RBM.Gauss RBM.Path
open scoped ENNReal

/-! ### Pure real facts -/

/-- The elementary inequality behind the last step of §6: for `s ≥ 0`, `T ≥ 1`,
`s² ≤ T(r² + r s)` implies `s² ≤ 4T²r²`.  (RBM1D `sq_le_four_mul_of_le_add_mul`,
`ContinuityAssembly.lean:584`.) -/
theorem sq_le_four_mul_of_le_add_mul {s r T : ℝ} (hs : 0 ≤ s) (hT : 1 ≤ T)
    (h : s ^ 2 ≤ T * (r ^ 2 + r * s)) : s ^ 2 ≤ 4 * T ^ 2 * r ^ 2 := by
  rcases le_or_gt s (2 * T * r) with h1 | h1
  · have : s ^ 2 ≤ (2 * T * r) ^ 2 := pow_le_pow_left₀ hs h1 2
    nlinarith
  · have hTr : T * r * s ≤ s ^ 2 / 2 := by nlinarith
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith

/-- `N^{τ} N^{-ε} < 1` for `τ < ε`, `N ≥ 2`.  (RBM1D `rpow_mul_rpow_neg_lt_one`,
`Step1.lean:114`; here `N` is a value `size l`.) -/
theorem rpow_mul_rpow_neg_lt_one {N : ℕ} (hN : 2 ≤ N) {τ ε : ℝ} (hτε : τ < ε) :
    (N : ℝ) ^ τ * (N : ℝ) ^ (-ε) < 1 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)

/-- **The continuity argument, deterministic core.**  If `g` and `a` are continuous on
`[s, t]`, `g(s) < a(s)`, and `g(u) ≠ a(u)` for all `u ∈ [s, t]`, then `g < a` on `[s, t]`
(intermediate value theorem).  (RBM1D `lt_of_forall_ne_of_continuousOn`, `Step1.lean:151`.) -/
theorem lt_of_forall_ne_of_continuousOn {g a : ℝ → ℝ} {s t : ℝ}
    (hg : ContinuousOn g (Set.Icc s t)) (ha : ContinuousOn a (Set.Icc s t)) (h0 : g s < a s)
    (hne : ∀ u ∈ Set.Icc s t, g u ≠ a u) : ∀ u ∈ Set.Icc s t, g u < a u := by
  intro u hu
  by_contra hno
  push Not at hno
  have hsub : Set.Icc s u ⊆ Set.Icc s t := Set.Icc_subset_Icc_right hu.2
  have hc : ContinuousOn (fun v => a v - g v) (Set.Icc s u) := (ha.sub hg).mono hsub
  have h0' : (0 : ℝ) ∈ Set.Icc (a u - g u) (a s - g s) := ⟨by linarith, by linarith⟩
  obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc' hu.1 hc h0'
  exact hne v (hsub hv) (by simp only at hv0; linarith)

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- Two events with `P ≤ x^{-(D+1)}` give `P (A ∪ B) ≤ x^{-D}` once `2 x^{-(D+1)} ≤ x^{-D}`. -/
private theorem measure_union_le_of_two {A B : Set Ω} {x D : ℝ} (hx : 0 ≤ x)
    (hA : P A ≤ ENNReal.ofReal (x ^ (-(D + 1)))) (hB : P B ≤ ENNReal.ofReal (x ^ (-(D + 1))))
    (h : 2 * x ^ (-(D + 1)) ≤ x ^ (-D)) : P (A ∪ B) ≤ ENNReal.ofReal (x ^ (-D)) := by
  have hp : (0 : ℝ) ≤ x ^ (-(D + 1)) := Real.rpow_nonneg hx _
  calc P (A ∪ B) ≤ P A + P B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (x ^ (-(D + 1))) + ENNReal.ofReal (x ^ (-(D + 1))) := add_le_add hA hB
    _ = ENNReal.ofReal (2 * x ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal (x ^ (-D)) := ENNReal.ofReal_le_ofReal h

/-! ### `HighProbAt`: monotonicity and finite intersections

The `size`-indexed analogues of RBM1D `HighProb.mono` (`Defs/StochDom.lean:291`) and
`HighProb.inter` (`:298`). -/

/-- Monotonicity of `HighProbAt`. -/
theorem perTimeCalc_highProbAt_mono {Ξ Ξ' : ℕ → Set Ω} (h : HighProbAt P size Ξ)
    (hsub : ∀ᶠ l : ℕ in atTop, Ξ l ⊆ Ξ' l) : HighProbAt P size Ξ' := by
  intro D hD
  filter_upwards [h D hD, hsub] with l hN hs
  exact (measure_mono (Set.compl_subset_compl.2 hs)).trans hN

/-- Two `HighProbAt` events hold simultaneously with high probability (needs `size → ∞`). -/
theorem perTimeCalc_highProbAt_inter (hsize : Tendsto size atTop atTop) {Ξ₁ Ξ₂ : ℕ → Set Ω}
    (h₁ : HighProbAt P size Ξ₁) (h₂ : HighProbAt P size Ξ₂) :
    HighProbAt P size (fun l => Ξ₁ l ∩ Ξ₂ l) := by
  intro D hD
  filter_upwards [h₁ (D + 1) (by linarith), h₂ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l hN1 hN2 h3
  rw [Set.compl_inter]
  exact measure_union_le_of_two (Nat.cast_nonneg _) hN1 hN2 h3

/-- **`StochDomAt` gives a high-probability event**: `{∀ u, ξ ≤ (size l)^τ ζ}` holds with high
probability.  (RBM1D `StochDom.highProb`, `Defs/StochDom.lean:277`.) -/
theorem perTimeCalc_highProbAt_of_stochDomAt {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : StochDomAt P size ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with l hN
  convert hN using 2
  ext ω; simp [badSetAt]

end Generic

/-! ### Pointwise cores

The pointwise implications behind each domination lemma.  They do not mention `P`, so the same
core serves the per-time variant (`PerTime`) and the uniform variant (`Unif`). -/

section Cores

variable {Ω : Type*} {size : ℕ → ℕ} {U : ℕ → Type*}

private theorem imp_mono_right {ξ ζ ζ' : ∀ l, U l → Ω → ℝ}
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ ζ' l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ' l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ l u ω < ξ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hle] with l hl u ω hu
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hl u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) τ)) hu

private theorem imp_rpow_of_le_one {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * (ζ l u ω) ^ r < (ξ l u ω) ^ r →
        (size l : ℝ) ^ τ' * ζ l u ω < ξ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  rcases Nat.eq_zero_or_pos (size l) with h0 | h1
  · rw [h0] at hu ⊢
    simp only [Nat.cast_zero, Real.zero_rpow hτ.ne', zero_mul] at hu ⊢
    rcases (hξ l u ω).eq_or_lt with h | h
    · rw [← h, Real.zero_rpow hr0.ne'] at hu
      exact absurd hu (lt_irrefl _)
    · exact h
  · refine lt_of_not_ge fun hle => ?_
    have hN : (1 : ℝ) ≤ (size l : ℝ) ^ τ :=
      Real.one_le_rpow (by exact_mod_cast h1) hτ.le
    have h1' : (ξ l u ω) ^ r ≤ ((size l : ℝ) ^ τ * ζ l u ω) ^ r :=
      Real.rpow_le_rpow (hξ l u ω) hle hr0.le
    rw [Real.mul_rpow (by linarith) (hζ l u ω)] at h1'
    have h2 : ((size l : ℝ) ^ τ) ^ r ≤ (size l : ℝ) ^ τ := Real.rpow_le_self_of_one_le hN hr1
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (hζ l u ω) r)
    exact absurd hu (not_lt.2 (h1'.trans h3))

private theorem imp_of_le_add_sqrt_mul (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω →
        (size l : ℝ) ^ τ' * (ζ l u ω + Real.sqrt (ζ l u ω * ξ l u ω)) < ξ l u ω := by
  intro τ hτ
  refine ⟨τ / 3, by positivity, ?_⟩
  filter_upwards [hsize.eventually
    (eventually_le_rpow 4 (by positivity : (0 : ℝ) < τ / 3))] with l h4 u ω hu
  refine lt_of_not_ge fun hle => ?_
  set T := (size l : ℝ) ^ (τ / 3)
  have hT1 : 1 ≤ T := by linarith
  have hT3 : T ^ 3 = (size l : ℝ) ^ τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1; push_cast; ring
  set x := ξ l u ω
  set a := ζ l u ω
  have hx := hξ l u ω
  have ha := hζ l u ω
  have hs := Real.sq_sqrt hx
  have hr := Real.sq_sqrt ha
  have key : Real.sqrt x ^ 2 ≤ T * (Real.sqrt a ^ 2 + Real.sqrt a * Real.sqrt x) := by
    rw [hs, hr, ← Real.sqrt_mul ha]; exact hle
  have h4' := sq_le_four_mul_of_le_add_mul (Real.sqrt_nonneg _) hT1 key
  rw [hs, hr] at h4'
  have : 4 * T ^ 2 * a ≤ T ^ 3 * a := by
    have : 4 * T ^ 2 ≤ T ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right this ha
  rw [hT3] at this
  exact absurd hu (not_lt.2 (h4'.trans this))

private theorem imp_add {ξ₁ ξ₂ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ} :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * (ζ₁ l u ω + ζ₂ l u ω) < ξ₁ l u ω + ξ₂ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  by_contra hno
  simp only [not_or, not_lt] at hno
  simp only [mul_add] at hu
  linarith [hno.1, hno.2]

private theorem imp_mul {ξ₁ ξ₂ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ} (hξ₂ : ∀ l u ω, 0 ≤ ξ₂ l u ω)
    (hζ₁ : ∀ l u ω, 0 ≤ ζ₁ l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * (ζ₁ l u ω * ζ₂ l u ω) < ξ₁ l u ω * ξ₂ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω := by
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  by_contra hno
  simp only [not_or, not_lt] at hno
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := calc ξ₁ l u ω * ξ₂ l u ω
        ≤ ((size l : ℝ) ^ (τ / 2) * ζ₁ l u ω) * ξ₂ l u ω :=
          mul_le_mul_of_nonneg_right hno.1 (hξ₂ l u ω)
    _ ≤ ((size l : ℝ) ^ (τ / 2) * ζ₁ l u ω) * ((size l : ℝ) ^ (τ / 2) * ζ₂ l u ω) :=
        mul_le_mul_of_nonneg_left hno.2 (mul_nonneg hpos (hζ₁ l u ω))
    _ = ((size l : ℝ) ^ (τ / 2) * (size l : ℝ) ^ (τ / 2)) * (ζ₁ l u ω * ζ₂ l u ω) := by ring
    _ = (size l : ℝ) ^ τ * (ζ₁ l u ω * ζ₂ l u ω) := by
        rw [UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
  linarith

private theorem imp_mono (hsize : Tendsto size atTop atTop) {ξ ζ ζ' : ∀ l, U l → Ω → ℝ}
    (hζ' : ∀ l u ω, 0 ≤ ζ' l u ω) (C : ℝ)
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ C * ζ' l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ' l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ l u ω < ξ l u ω := by
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, hsize.eventually (eventually_le_rpow C (half_pos hτ))] with l hN hC u ω hu
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (size l : ℝ) ^ (τ / 2) * ζ l u ω
      ≤ (size l : ℝ) ^ (τ / 2) * (C * ζ' l u ω) := mul_le_mul_of_nonneg_left (hN u ω) hpos
    _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ' l u ω) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC (hζ' l u ω)) hpos
    _ = (size l : ℝ) ^ τ * ζ' l u ω := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
    _ < ξ l u ω := hu

private theorem imp_forall_or {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}
    (hor : ∀ l u ω, (ξ l u ω ≤ ξ₁ l u ω ∧ ζ₁ l u ω ≤ ζ l u ω) ∨
      (ξ l u ω ≤ ξ₂ l u ω ∧ ζ₂ l u ω ≤ ζ l u ω)) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  have hpos : 0 ≤ (size l : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases hor l u ω with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by nlinarith [mul_le_mul_of_nonneg_left h2 hpos])
  · exact Or.inr (by nlinarith [mul_le_mul_of_nonneg_left h2 hpos])

private theorem imp_min {ξ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ} :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * min (ζ₁ l u ω) (ζ₂ l u ω) < ξ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  have hpos : 0 ≤ (size l : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [mul_min_of_nonneg _ _ hpos, min_lt_iff] at hu
  exact hu

private theorem imp_left_eventually {ξ ξ' ζ : ∀ l, U l → Ω → ℝ}
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ ξ' l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ l u ω < ξ' l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hle] with l hl u ω hu
  exact lt_of_lt_of_le hu (hl u ω)

end Cores

/-! ### The per-time variants (`PerTimeDomAt`) -/

section PerTimeSection

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

namespace PerTime

variable {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}

/-! #### Base layer (per time) -/

/-- A failure event eventually contained in the failure event of a single domination
(pointwise form).  Per-time analogue of RBM1D `StochDom.of_subset` (`Defs/StochDom.lean:109`). -/
theorem perTimeCalc_of_imp (h : PerTimeDomAt P size ξ₁ ζ₁)
    (himp : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2 u
  exact (measure_mono fun ω hω => h1 u ω hω).trans (h2 u)

/-- A failure event eventually contained in the union of two failure events (pointwise form).
Per-time analogue of RBM1D `StochDom.of_subset_union` (`Defs/StochDom.lean:118`). -/
theorem perTimeCalc_of_imp_union (hsize : Tendsto size atTop atTop)
    (h₁ : PerTimeDomAt P size ξ₁ ζ₁) (h₂ : PerTimeDomAt P size ξ₂ ζ₂)
    (himp : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  filter_upwards [hs, h₁ τ' hτ' (D + 1) (by linarith), h₂ τ' hτ' (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3 u
  refine (measure_mono ?_).trans (measure_union_le_of_two (Nat.cast_nonneg _) (h1 u) (h2 u) h3)
  intro ω hω
  rcases h0 u ω hω with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- `ζ ≺ ζ` for a non-negative family (needs `1 ≤ size l` eventually).  Per-time analogue of
RBM1D `StochDom.refl` (`Defs/StochDom.lean:151`). -/
theorem perTimeCalc_refl (hsize : Tendsto size atTop atTop) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    PerTimeDomAt P size ζ ζ := by
  intro τ hτ D hD
  filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with l hl u
  have hN : (1 : ℝ) ≤ (size l : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hl) hτ.le
  have hE : {ω | (size l : ℝ) ^ τ * ζ l u ω < ζ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith [hζ l u ω]
  rw [hE, measure_empty]
  exact zero_le

/-- `≺` is closed under addition.  Per-time analogue of RBM1D `StochDom.add`
(`Defs/StochDom.lean:174`). -/
theorem perTimeCalc_add (hsize : Tendsto size atTop atTop) (h₁ : PerTimeDomAt P size ξ₁ ζ₁)
    (h₂ : PerTimeDomAt P size ξ₂ ζ₂) :
    PerTimeDomAt P size (fun l u ω => ξ₁ l u ω + ξ₂ l u ω)
      (fun l u ω => ζ₁ l u ω + ζ₂ l u ω) :=
  perTimeCalc_of_imp_union hsize h₁ h₂ imp_add

/-- `≺` is closed under multiplication of non-negative quantities.  Per-time analogue of RBM1D
`StochDom.mul` (`Defs/StochDom.lean:184`). -/
theorem perTimeCalc_mul (hsize : Tendsto size atTop atTop) (hξ₂ : ∀ l u ω, 0 ≤ ξ₂ l u ω)
    (hζ₁ : ∀ l u ω, 0 ≤ ζ₁ l u ω) (h₁ : PerTimeDomAt P size ξ₁ ζ₁)
    (h₂ : PerTimeDomAt P size ξ₂ ζ₂) :
    PerTimeDomAt P size (fun l u ω => ξ₁ l u ω * ξ₂ l u ω)
      (fun l u ω => ζ₁ l u ω * ζ₂ l u ω) :=
  perTimeCalc_of_imp_union hsize h₁ h₂ (imp_mul hξ₂ hζ₁)

/-- `ξ ≺ ζ` and `ζ ≤ C ζ'` (eventually, pointwise) give `ξ ≺ ζ'`.  Per-time analogue of RBM1D
`Step3.stochDom_mono` (`Defs/StochDomMono.lean:24`). -/
theorem perTimeCalc_mono (hsize : Tendsto size atTop atTop) {ζ' : ∀ l, U l → Ω → ℝ}
    (hζ' : ∀ l u ω, 0 ≤ ζ' l u ω) (C : ℝ)
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ C * ζ' l u ω) (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size ξ ζ' :=
  perTimeCalc_of_imp h (imp_mono hsize hζ' C hle)

/-! #### Targets: `ContinuityAssembly.lean`, section `StochGeneric` -/

/-- Enlarging the right side of `≺` (for large `l`).  Port of RBM1D
`StochDom.mono_right_eventually` (`ContinuityAssembly.lean:540`). -/
theorem mono_right_eventually {ζ' : ∀ l, U l → Ω → ℝ} (h : PerTimeDomAt P size ξ ζ)
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ ζ' l u ω) : PerTimeDomAt P size ξ ζ' :=
  perTimeCalc_of_imp h (imp_mono_right hle)

/-- Powers `0 < r ≤ 1` preserve `≺`: `ξ ≺ ζ` implies `ξ^r ≺ ζ^r`.  Port of RBM1D
`StochDom.rpow_of_le_one` (`ContinuityAssembly.lean:549`); no growth hypothesis on `size`
(the case `size l = 0` is treated separately). -/
theorem rpow_of_le_one {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun l u ω => ξ l u ω ^ r) (fun l u ω => ζ l u ω ^ r) :=
  perTimeCalc_of_imp h (imp_rpow_of_le_one hr0 hr1 hξ hζ)

/-- Square roots preserve `≺`.  Port of RBM1D `StochDom.sqrt_of`
(`ContinuityAssembly.lean:565`). -/
theorem sqrt_of (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun l u ω => Real.sqrt (ξ l u ω)) (fun l u ω => Real.sqrt (ζ l u ω)) := by
  simp only [Real.sqrt_eq_rpow]
  exact rpow_of_le_one (by norm_num) (by norm_num) hξ hζ h

/-- **Absorbing `(size l)^δ`**: if `ξ ≺ (size l)^δ ζ` for every `δ > 0`, then `ξ ≺ ζ`.  Port of
RBM1D `StochDom.of_forall_rpow_mul` (`ContinuityAssembly.lean:572`). -/
theorem of_forall_rpow_mul
    (h : ∀ δ > (0 : ℝ), PerTimeDomAt P size ξ (fun l u ω => (size l : ℝ) ^ δ * ζ l u ω)) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h (τ / 2) (half_pos hτ) (τ / 2) (half_pos hτ) D hD] with l hl u
  refine (measure_mono ?_).trans (hl u)
  intro ω hω
  change (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) < ξ l u ω
  rwa [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]

/-- **The last step of §6**: `X ≺ A + A^{1/2} X^{1/2}` implies `X ≺ A` (for `X, A ≥ 0`).  Port of
RBM1D `StochDom.of_le_add_sqrt_mul` (`ContinuityAssembly.lean:594`). -/
theorem of_le_add_sqrt_mul (hsize : Tendsto size atTop atTop)
    (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : PerTimeDomAt P size ξ (fun l u ω => ζ l u ω + Real.sqrt (ζ l u ω * ξ l u ω))) :
    PerTimeDomAt P size ξ ζ :=
  perTimeCalc_of_imp h (imp_of_le_add_sqrt_mul hsize hξ hζ)

/-- `≺` is closed under finite sums.  Port of RBM1D `StochDom.finset_sum_of`
(`ContinuityAssembly.lean:625`). -/
theorem finset_sum_of (hsize : Tendsto size atTop atTop) {ι : Type*} (s : Finset ι)
    {ξ ζ : ι → ∀ l, U l → Ω → ℝ} (h : ∀ i ∈ s, PerTimeDomAt P size (ξ i) (ζ i)) :
    PerTimeDomAt P size (fun l u ω => ∑ i ∈ s, ξ i l u ω) (fun l u ω => ∑ i ∈ s, ζ i l u ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := perTimeCalc_refl (P := P) (size := size) hsize
      (ζ := fun (l : ℕ) (_ : U l) (_ : Ω) => (0 : ℝ)) (fun _ _ _ => le_rfl)
    simpa using h0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact perTimeCalc_add hsize (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! #### Targets: `Hierarchy/Step1.lean`, section `Generic`, and `Defs/StochDomHighProb.lean` -/

/-- **Removing a parameter-dependent indicator.**  If `1_{Ω(l,u)} ξ ≺ ζ` and the events
`Ω(l,u)` hold for all `u` simultaneously with high probability, then `ξ ≺ ζ`.  Port of RBM1D
`stochDom_of_indicator` (`Step1.lean:188`). -/
theorem stochDom_of_indicator (hsize : Tendsto size atTop atTop)
    {Ωs : ∀ l, U l → Set Ω} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (hΩ : HighProbAt P size (fun l => {ω | ∀ u, ω ∈ Ωs l u}))
    (h : PerTimeDomAt P size (fun l u ω => (Ωs l u).indicator (fun ω => ξ l u ω) ω) ζ) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ (D + 1) (by linarith), hΩ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h1 h2 h3 u
  refine (measure_mono ?_).trans (measure_union_le_of_two (Nat.cast_nonneg _) (h1 u) h2 h3)
  intro ω hu
  by_cases hω : ∀ u, ω ∈ Ωs l u
  · refine Or.inl ?_
    change (size l : ℝ) ^ τ * ζ l u ω < (Ωs l u).indicator (fun ω => ξ l u ω) ω
    rw [Set.indicator_of_mem (hω u)]
    exact hu
  · exact Or.inr hω

/-- **Case splitting under `≺`**: if at every `(l, u, ω)` the pair `(ξ, ζ)` is dominated by
`(ξ₁, ζ₁)` or by `(ξ₂, ζ₂)` (`ξ ≤ ξᵢ`, `ζᵢ ≤ ζ`), then `ξ₁ ≺ ζ₁` and `ξ₂ ≺ ζ₂` give `ξ ≺ ζ`.
Port of RBM1D `stochDom_of_forall_or` (`Step1.lean:218`). -/
theorem stochDom_of_forall_or (hsize : Tendsto size atTop atTop)
    {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}
    (h₁ : PerTimeDomAt P size ξ₁ ζ₁) (h₂ : PerTimeDomAt P size ξ₂ ζ₂)
    (hor : ∀ l u ω, (ξ l u ω ≤ ξ₁ l u ω ∧ ζ₁ l u ω ≤ ζ l u ω) ∨
      (ξ l u ω ≤ ξ₂ l u ω ∧ ζ₂ l u ω ≤ ζ l u ω)) : PerTimeDomAt P size ξ ζ :=
  perTimeCalc_of_imp_union hsize h₁ h₂ (imp_forall_or hor)

/-- A pointwise bound `ξ ≤ C ζ` (`ξ, ζ ≥ 0`) gives `ξ ≺ ζ`.  Port of RBM1D
`stochDom_of_le_const_mul` (`Step1.lean:230`). -/
theorem stochDom_of_le_const_mul (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, 0 ≤ ξ l u ω)
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (C : ℝ) (h : ∀ l u ω, ξ l u ω ≤ C * ζ l u ω) :
    PerTimeDomAt P size ξ ζ :=
  perTimeCalc_mono hsize hζ C (Eventually.of_forall h) (perTimeCalc_refl hsize hξ)

/-- A left side that is eventually pointwise smaller.  Port of RBM1D
`stochDom_of_le_left_eventually` (`Step1.lean:236`). -/
theorem stochDom_of_le_left_eventually {ξ ξ' ζ : ∀ l, U l → Ω → ℝ}
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ ξ' l u ω) (h : PerTimeDomAt P size ξ' ζ) :
    PerTimeDomAt P size ξ ζ :=
  perTimeCalc_of_imp h (imp_left_eventually hle)

/-- **High probability gives `≺`**: if `ξ ≤ ζ` for all `u` w.h.p. (`ζ ≥ 0`), then `ξ ≺ ζ`.
Port of RBM1D `stochDom_of_highProb` (`Defs/StochDomHighProb.lean:25`). -/
theorem stochDom_of_highProb (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ ζ l u ω})) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h D hD, hsize.eventually (eventually_ge_atTop 1)] with l hl hl1 u
  refine (measure_mono ?_).trans hl
  intro ω hω hω'
  have h1 : (1 : ℝ) ≤ (size l : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hl1) hτ.le
  have := hω' u
  have hω'' : (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω := hω
  nlinarith [hζ l u ω]

/-! #### Targets: `Hierarchy/Step45.lean` -/

/-- Two bounds give the minimum: `ξ ≺ ζ₁` and `ξ ≺ ζ₂` imply `ξ ≺ min(ζ₁, ζ₂)`.  Port of RBM1D
`stochDom_min` (`Step45.lean:109`). -/
theorem stochDom_min (hsize : Tendsto size atTop atTop) {ξ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ}
    (h₁ : PerTimeDomAt P size ξ ζ₁) (h₂ : PerTimeDomAt P size ξ ζ₂) :
    PerTimeDomAt P size ξ fun l u ω => min (ζ₁ l u ω) (ζ₂ l u ω) :=
  perTimeCalc_of_imp_union hsize h₁ h₂ imp_min

/-- A product bound: `X_p ≺ f`, `X_q ≺ g` and `f g A⁻¹ ≤ C` (eventually) give
`X_p X_q A⁻¹ ≺ 1`.  Port of RBM1D `quad_le_one` (`Step45.lean:121`). -/
theorem quad_le_one (hsize : Tendsto size atTop atTop) {ξp ξq : ∀ l, U l → Ω → ℝ}
    {f g A : ∀ l, U l → ℝ}
    (hA : ∀ l u, 0 < A l u) (hq0 : ∀ l u ω, 0 ≤ ξq l u ω) (hf : ∀ l u, 0 ≤ f l u)
    (hg : ∀ l u, 0 ≤ g l u)
    (hp : PerTimeDomAt P size ξp fun l u _ => f l u)
    (hq : PerTimeDomAt P size ξq fun l u _ => g l u)
    (C : ℝ) (hle : ∀ᶠ l : ℕ in atTop, ∀ u, f l u * g l u * (A l u)⁻¹ ≤ C) :
    PerTimeDomAt P size (fun l u ω => ξp l u ω * ξq l u ω * (A l u)⁻¹) fun _ _ _ => 1 := by
  have hA' : ∀ l u (_ : Ω), 0 ≤ (A l u)⁻¹ := fun l u _ => (inv_pos.2 (hA l u)).le
  have h12 := perTimeCalc_mul hsize hq0 (fun l u _ => hf l u) hp hq
  have h3 := perTimeCalc_mul hsize hA' (fun l u _ => mul_nonneg (hf l u) (hg l u)) h12
    (perTimeCalc_refl hsize hA')
  exact perTimeCalc_mono hsize (fun _ _ _ => zero_le_one) C
    (hle.mono fun l hN u _ => by simpa using hN u) h3

end PerTime

end PerTimeSection

/-! ### The uniform variants (`StochDomAt`) -/

section UnifSection

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

namespace Unif

variable {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}

/-! #### Base layer (uniform) -/

/-- A failure event eventually contained in the failure event of a single domination
(pointwise form).  Uniform analogue of RBM1D `StochDom.of_subset`
(`Defs/StochDom.lean:109`). -/
theorem perTimeCalc_of_imp (h : StochDomAt P size ξ₁ ζ₁)
    (himp : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  refine (measure_mono ?_).trans h2
  rintro ω ⟨u, hu⟩
  exact ⟨u, h1 u ω hu⟩

/-- A failure event eventually contained in the union of two failure events (pointwise form).
Uniform analogue of RBM1D `StochDom.of_subset_union` (`Defs/StochDom.lean:118`). -/
theorem perTimeCalc_of_imp_union (hsize : Tendsto size atTop atTop)
    (h₁ : StochDomAt P size ξ₁ ζ₁) (h₂ : StochDomAt P size ξ₂ ζ₂)
    (himp : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  filter_upwards [hs, h₁ τ' hτ' (D + 1) (by linarith), h₂ τ' hτ' (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3
  refine (measure_mono ?_).trans (measure_union_le_of_two (Nat.cast_nonneg _) h1 h2 h3)
  rintro ω ⟨u, hu⟩
  rcases h0 u ω hu with h | h
  · exact Or.inl ⟨u, h⟩
  · exact Or.inr ⟨u, h⟩

/-- `ζ ≺ ζ` for a non-negative family (needs `1 ≤ size l` eventually).  Uniform analogue of
RBM1D `StochDom.refl` (`Defs/StochDom.lean:151`). -/
theorem perTimeCalc_refl (hsize : Tendsto size atTop atTop) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    StochDomAt P size ζ ζ := by
  intro τ hτ D hD
  filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with l hl
  have hN : (1 : ℝ) ≤ (size l : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hl) hτ.le
  have hE : badSetAt size ζ ζ τ l = ∅ := by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
      not_lt]
    intro u
    nlinarith [hζ l u ω]
  rw [hE, measure_empty]
  exact zero_le

/-- `≺` is closed under addition.  Uniform analogue of RBM1D `StochDom.add`
(`Defs/StochDom.lean:174`). -/
theorem perTimeCalc_add (hsize : Tendsto size atTop atTop) (h₁ : StochDomAt P size ξ₁ ζ₁)
    (h₂ : StochDomAt P size ξ₂ ζ₂) :
    StochDomAt P size (fun l u ω => ξ₁ l u ω + ξ₂ l u ω)
      (fun l u ω => ζ₁ l u ω + ζ₂ l u ω) :=
  perTimeCalc_of_imp_union hsize h₁ h₂ imp_add

/-- `≺` is closed under multiplication of non-negative quantities.  Uniform analogue of RBM1D
`StochDom.mul` (`Defs/StochDom.lean:184`). -/
theorem perTimeCalc_mul (hsize : Tendsto size atTop atTop) (hξ₂ : ∀ l u ω, 0 ≤ ξ₂ l u ω)
    (hζ₁ : ∀ l u ω, 0 ≤ ζ₁ l u ω) (h₁ : StochDomAt P size ξ₁ ζ₁)
    (h₂ : StochDomAt P size ξ₂ ζ₂) :
    StochDomAt P size (fun l u ω => ξ₁ l u ω * ξ₂ l u ω)
      (fun l u ω => ζ₁ l u ω * ζ₂ l u ω) :=
  perTimeCalc_of_imp_union hsize h₁ h₂ (imp_mul hξ₂ hζ₁)

/-- `ξ ≺ ζ` and `ζ ≤ C ζ'` (eventually, pointwise) give `ξ ≺ ζ'`.  Uniform analogue of RBM1D
`Step3.stochDom_mono` (`Defs/StochDomMono.lean:24`). -/
theorem perTimeCalc_mono (hsize : Tendsto size atTop atTop) {ζ' : ∀ l, U l → Ω → ℝ}
    (hζ' : ∀ l u ω, 0 ≤ ζ' l u ω) (C : ℝ)
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ C * ζ' l u ω) (h : StochDomAt P size ξ ζ) :
    StochDomAt P size ξ ζ' :=
  perTimeCalc_of_imp h (imp_mono hsize hζ' C hle)

/-! #### Targets: `ContinuityAssembly.lean`, section `StochGeneric` -/

/-- Enlarging the right side of `≺` (for large `l`).  Port of RBM1D
`StochDom.mono_right_eventually` (`ContinuityAssembly.lean:540`). -/
theorem mono_right_eventually {ζ' : ∀ l, U l → Ω → ℝ} (h : StochDomAt P size ξ ζ)
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ ζ' l u ω) : StochDomAt P size ξ ζ' :=
  perTimeCalc_of_imp h (imp_mono_right hle)

/-- Powers `0 < r ≤ 1` preserve `≺`: `ξ ≺ ζ` implies `ξ^r ≺ ζ^r`.  Port of RBM1D
`StochDom.rpow_of_le_one` (`ContinuityAssembly.lean:549`); no growth hypothesis on `size`
(the case `size l = 0` is treated separately). -/
theorem rpow_of_le_one {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (h : StochDomAt P size ξ ζ) :
    StochDomAt P size (fun l u ω => ξ l u ω ^ r) (fun l u ω => ζ l u ω ^ r) :=
  perTimeCalc_of_imp h (imp_rpow_of_le_one hr0 hr1 hξ hζ)

/-- Square roots preserve `≺`.  Port of RBM1D `StochDom.sqrt_of`
(`ContinuityAssembly.lean:565`). -/
theorem sqrt_of (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : StochDomAt P size ξ ζ) :
    StochDomAt P size (fun l u ω => Real.sqrt (ξ l u ω)) (fun l u ω => Real.sqrt (ζ l u ω)) := by
  simp only [Real.sqrt_eq_rpow]
  exact rpow_of_le_one (by norm_num) (by norm_num) hξ hζ h

/-- **Absorbing `(size l)^δ`**: if `ξ ≺ (size l)^δ ζ` for every `δ > 0`, then `ξ ≺ ζ`.  Port of
RBM1D `StochDom.of_forall_rpow_mul` (`ContinuityAssembly.lean:572`). -/
theorem of_forall_rpow_mul
    (h : ∀ δ > (0 : ℝ), StochDomAt P size ξ (fun l u ω => (size l : ℝ) ^ δ * ζ l u ω)) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h (τ / 2) (half_pos hτ) (τ / 2) (half_pos hτ) D hD] with l hl
  refine (measure_mono ?_).trans hl
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rwa [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]

/-- **The last step of §6**: `X ≺ A + A^{1/2} X^{1/2}` implies `X ≺ A` (for `X, A ≥ 0`).  Port of
RBM1D `StochDom.of_le_add_sqrt_mul` (`ContinuityAssembly.lean:594`). -/
theorem of_le_add_sqrt_mul (hsize : Tendsto size atTop atTop)
    (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : StochDomAt P size ξ (fun l u ω => ζ l u ω + Real.sqrt (ζ l u ω * ξ l u ω))) :
    StochDomAt P size ξ ζ :=
  perTimeCalc_of_imp h (imp_of_le_add_sqrt_mul hsize hξ hζ)

/-- `≺` is closed under finite sums.  Port of RBM1D `StochDom.finset_sum_of`
(`ContinuityAssembly.lean:625`). -/
theorem finset_sum_of (hsize : Tendsto size atTop atTop) {ι : Type*} (s : Finset ι)
    {ξ ζ : ι → ∀ l, U l → Ω → ℝ} (h : ∀ i ∈ s, StochDomAt P size (ξ i) (ζ i)) :
    StochDomAt P size (fun l u ω => ∑ i ∈ s, ξ i l u ω) (fun l u ω => ∑ i ∈ s, ζ i l u ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := perTimeCalc_refl (P := P) (size := size) hsize
      (ζ := fun (l : ℕ) (_ : U l) (_ : Ω) => (0 : ℝ)) (fun _ _ _ => le_rfl)
    simpa using h0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact perTimeCalc_add hsize (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! #### Targets: `Hierarchy/Step1.lean`, section `Generic`, and `Defs/StochDomHighProb.lean` -/

/-- **The forbidden region (5.9).**  Let `x ≥ 0` be random and `f, a, b` deterministic with
`a > 0`.  If `1(x ≤ b) x ≺ f` and `f ≪ a` (i.e. `f ≤ (size l)^{-ε} a` for some `ε > 0`), then
with high probability `x` avoids `[a, b]`, simultaneously for all parameters `u`.  Port of RBM1D
`forbidden_region` (`Step1.lean:123`); only the uniform variant is stated (the per-time variant
is false, see the module docstring). -/
theorem forbidden_region (hsize : Tendsto size atTop atTop) {x : ∀ l, U l → Ω → ℝ}
    {f a b : ∀ l, U l → ℝ}
    (ha : ∀ l u, 0 < a l u) {ε : ℝ} (hε : 0 < ε)
    (hfa : ∀ᶠ l : ℕ in atTop, ∀ u, f l u ≤ (size l : ℝ) ^ (-ε) * a l u)
    (h : StochDomAt P size (fun l u ω => {ω | x l u ω ≤ b l u}.indicator (fun ω => x l u ω) ω)
      (fun l u _ => f l u)) :
    HighProbAt P size (fun l => {ω | ∀ u, x l u ω < a l u ∨ b l u < x l u ω}) := by
  refine perTimeCalc_highProbAt_mono (perTimeCalc_highProbAt_of_stochDomAt h (half_pos hε)) ?_
  filter_upwards [hfa, hsize.eventually (eventually_ge_atTop 2)] with l hN hN2
  intro ω hω u
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hno
  push Not at hno
  obtain ⟨hax, hxb⟩ := hno
  have h1 := hω u
  have hmem : x l u ω ≤ b l u := hxb
  rw [Set.indicator_of_mem (show ω ∈ {ω | x l u ω ≤ b l u} from hmem)] at h1
  have hpos : 0 ≤ (size l : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : (size l : ℝ) ^ (ε / 2) * f l u ≤
      (size l : ℝ) ^ (ε / 2) * (size l : ℝ) ^ (-ε) * a l u := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hN u) hpos
  have h3 := rpow_mul_rpow_neg_lt_one hN2 (half_lt_self hε)
  have h4 : (size l : ℝ) ^ (ε / 2) * (size l : ℝ) ^ (-ε) * a l u < a l u := by
    have := ha l u
    nlinarith
  linarith

/-- **Removing a parameter-dependent indicator.**  If `1_{Ω(l,u)} ξ ≺ ζ` and the events
`Ω(l,u)` hold for all `u` simultaneously with high probability, then `ξ ≺ ζ`.  Port of RBM1D
`stochDom_of_indicator` (`Step1.lean:188`). -/
theorem stochDom_of_indicator (hsize : Tendsto size atTop atTop)
    {Ωs : ∀ l, U l → Set Ω} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (hΩ : HighProbAt P size (fun l => {ω | ∀ u, ω ∈ Ωs l u}))
    (h : StochDomAt P size (fun l u ω => (Ωs l u).indicator (fun ω => ξ l u ω) ω) ζ) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ (D + 1) (by linarith), hΩ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h1 h2 h3
  refine (measure_mono ?_).trans (measure_union_le_of_two (Nat.cast_nonneg _) h1 h2 h3)
  rintro ω ⟨u, hu⟩
  by_cases hω : ∀ u, ω ∈ Ωs l u
  · refine Or.inl ⟨u, ?_⟩
    change (size l : ℝ) ^ τ * ζ l u ω < (Ωs l u).indicator (fun ω => ξ l u ω) ω
    rw [Set.indicator_of_mem (hω u)]
    exact hu
  · exact Or.inr hω

/-- **Case splitting under `≺`**: if at every `(l, u, ω)` the pair `(ξ, ζ)` is dominated by
`(ξ₁, ζ₁)` or by `(ξ₂, ζ₂)` (`ξ ≤ ξᵢ`, `ζᵢ ≤ ζ`), then `ξ₁ ≺ ζ₁` and `ξ₂ ≺ ζ₂` give `ξ ≺ ζ`.
Port of RBM1D `stochDom_of_forall_or` (`Step1.lean:218`). -/
theorem stochDom_of_forall_or (hsize : Tendsto size atTop atTop)
    {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}
    (h₁ : StochDomAt P size ξ₁ ζ₁) (h₂ : StochDomAt P size ξ₂ ζ₂)
    (hor : ∀ l u ω, (ξ l u ω ≤ ξ₁ l u ω ∧ ζ₁ l u ω ≤ ζ l u ω) ∨
      (ξ l u ω ≤ ξ₂ l u ω ∧ ζ₂ l u ω ≤ ζ l u ω)) : StochDomAt P size ξ ζ :=
  perTimeCalc_of_imp_union hsize h₁ h₂ (imp_forall_or hor)

/-- A pointwise bound `ξ ≤ C ζ` (`ξ, ζ ≥ 0`) gives `ξ ≺ ζ`.  Port of RBM1D
`stochDom_of_le_const_mul` (`Step1.lean:230`). -/
theorem stochDom_of_le_const_mul (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, 0 ≤ ξ l u ω)
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (C : ℝ) (h : ∀ l u ω, ξ l u ω ≤ C * ζ l u ω) :
    StochDomAt P size ξ ζ :=
  perTimeCalc_mono hsize hζ C (Eventually.of_forall h) (perTimeCalc_refl hsize hξ)

/-- A left side that is eventually pointwise smaller.  Port of RBM1D
`stochDom_of_le_left_eventually` (`Step1.lean:236`). -/
theorem stochDom_of_le_left_eventually {ξ ξ' ζ : ∀ l, U l → Ω → ℝ}
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ ξ' l u ω) (h : StochDomAt P size ξ' ζ) :
    StochDomAt P size ξ ζ :=
  perTimeCalc_of_imp h (imp_left_eventually hle)

/-- **High probability gives `≺`**: if `ξ ≤ ζ` for all `u` w.h.p. (`ζ ≥ 0`), then `ξ ≺ ζ`.
Port of RBM1D `stochDom_of_highProb` (`Defs/StochDomHighProb.lean:25`). -/
theorem stochDom_of_highProb (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ ζ l u ω})) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h D hD, hsize.eventually (eventually_ge_atTop 1)] with l hl hl1
  refine (measure_mono ?_).trans hl
  rintro ω ⟨u, hu⟩ hω
  have h1 : (1 : ℝ) ≤ (size l : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hl1) hτ.le
  have := hω u
  nlinarith [hζ l u ω]

/-! #### Targets: `Hierarchy/Step45.lean` -/

/-- Two bounds give the minimum: `ξ ≺ ζ₁` and `ξ ≺ ζ₂` imply `ξ ≺ min(ζ₁, ζ₂)`.  Port of RBM1D
`stochDom_min` (`Step45.lean:109`). -/
theorem stochDom_min (hsize : Tendsto size atTop atTop) {ξ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ}
    (h₁ : StochDomAt P size ξ ζ₁) (h₂ : StochDomAt P size ξ ζ₂) :
    StochDomAt P size ξ fun l u ω => min (ζ₁ l u ω) (ζ₂ l u ω) :=
  perTimeCalc_of_imp_union hsize h₁ h₂ imp_min

/-- A product bound: `X_p ≺ f`, `X_q ≺ g` and `f g A⁻¹ ≤ C` (eventually) give
`X_p X_q A⁻¹ ≺ 1`.  Port of RBM1D `quad_le_one` (`Step45.lean:121`). -/
theorem quad_le_one (hsize : Tendsto size atTop atTop) {ξp ξq : ∀ l, U l → Ω → ℝ}
    {f g A : ∀ l, U l → ℝ}
    (hA : ∀ l u, 0 < A l u) (hq0 : ∀ l u ω, 0 ≤ ξq l u ω) (hf : ∀ l u, 0 ≤ f l u)
    (hg : ∀ l u, 0 ≤ g l u)
    (hp : StochDomAt P size ξp fun l u _ => f l u)
    (hq : StochDomAt P size ξq fun l u _ => g l u)
    (C : ℝ) (hle : ∀ᶠ l : ℕ in atTop, ∀ u, f l u * g l u * (A l u)⁻¹ ≤ C) :
    StochDomAt P size (fun l u ω => ξp l u ω * ξq l u ω * (A l u)⁻¹) fun _ _ _ => 1 := by
  have hA' : ∀ l u (_ : Ω), 0 ≤ (A l u)⁻¹ := fun l u _ => (inv_pos.2 (hA l u)).le
  have h12 := perTimeCalc_mul hsize hq0 (fun l u _ => hf l u) hp hq
  have h3 := perTimeCalc_mul hsize hA' (fun l u _ => mul_nonneg (hf l u) (hg l u)) h12
    (perTimeCalc_refl hsize hA')
  exact perTimeCalc_mono hsize (fun _ _ _ => zero_le_one) C
    (hle.mono fun l hN u _ => by simpa using hN u) h3

end Unif

end UnifSection

/-! ### The continuity argument (bootstrap) -/

section Bootstrap

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}

/-- **The continuity argument (bootstrap).**  Let `M(u)` be random, continuous in `u ∈ [s,t]`
with high probability, and `a ≤ b` deterministic, `a` continuous.  If the forbidden region
`[a(u), b(u)]` is avoided for all `u` simultaneously (w.h.p.) and `M(s) < a(s)` (w.h.p.), then
`M(u) < a(u)` for all `u ∈ [s,t]` (w.h.p.).  Port of RBM1D `bootstrap` (`Step1.lean:167`),
renamed `stepOneBootstrap`.  It is a statement about events only, so there is no per-time /
uniform split. -/
theorem stepOneBootstrap (hsize : Tendsto size atTop atTop)
    {M : ∀ _ : ℕ, ℝ → Ω → ℝ} {a b : ∀ _ : ℕ, ℝ → ℝ} {s t : ℕ → ℝ}
    (hcont : HighProbAt P size
      (fun l => {ω | ContinuousOn (fun u => M l u ω) (Set.Icc (s l) (t l))}))
    (ha : ∀ l, ContinuousOn (a l) (Set.Icc (s l) (t l)))
    (hab : ∀ᶠ l : ℕ in atTop, ∀ u : TimeIcc s t l, a l u ≤ b l u)
    (hforb : HighProbAt P size
      (fun l => {ω | ∀ u : TimeIcc s t l, M l u ω < a l u ∨ b l u < M l u ω}))
    (hinit : HighProbAt P size (fun l => {ω | M l (s l) ω < a l (s l)})) :
    HighProbAt P size (fun l => {ω | ∀ u : TimeIcc s t l, M l u ω < a l u}) := by
  refine perTimeCalc_highProbAt_mono
    (perTimeCalc_highProbAt_inter hsize (perTimeCalc_highProbAt_inter hsize hcont hforb) hinit) ?_
  filter_upwards [hab] with l hab
  rintro ω ⟨⟨hc, hf⟩, hi⟩
  simp only [Set.mem_ofPred_eq] at hc hf hi ⊢
  intro u
  refine lt_of_forall_ne_of_continuousOn hc (ha l) hi (fun v hv => ?_) u u.2
  rcases hf ⟨v, hv⟩ with h | h
  · exact h.ne
  · have := hab ⟨v, hv⟩
    simp only at h this
    exact (lt_of_le_of_lt this h).ne'

end Bootstrap

end RBM.Ind.PerTimeCalc

/-! ## Instances at `d = 3` (the merged preflight sequence `sz0`)

Data: `RBM.Gauss.SizesInst.sz0` (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `N_0 = 2097152`),
the model measure `seqP sz0`, the scale `sz0.size = N_n = (W_n L_n)^3`, the random bounded
observable `RBM.Gauss.StochDomAtInst.obs` (`|sin|` of a Gaussian coordinate, not constant,
`obs_nonconst`), and the nondegenerate window `[s_n, t_n] = [0, 1/16]` (`TimeIcc s t n`, a nonempty
interval of positive length).  The hypothesis `hsize` is `tendsto_sz0_size`.  Every hypothesis of
`forbidden_region` and `stepOneBootstrap` is discharged at these data. -/

noncomputable section

namespace RBM.Ind.PerTimeCalcInst

open MeasureTheory Filter RBM RBM.Gauss RBM.Path RBM.Gauss.Sizes RBM.Gauss.SizesInst
  RBM.Gauss.StochDomAtInst

/-- The start time `s ≡ 0` of the window `[0, 1/16]`. -/
def s0 : ℕ → ℝ := fun _ => 0

/-- The end time `t ≡ 1/16` of the window `[0, 1/16]`. -/
def t0 : ℕ → ℝ := fun _ => 1 / 16

theorem s0_lt_t0 (n : ℕ) : s0 n < t0 n := by unfold s0 t0; norm_num

private theorem one_le_size (n : ℕ) : (1 : ℝ) ≤ (sz0.size n : ℝ) := by
  exact_mod_cast sz0.one_le_size n

/-- The random family `x = N^{-1/2} obs` on the window `TimeIcc s0 t0 n`. -/
def xF (n : ℕ) (_ : TimeIcc s0 t0 n) (ω : SeqΩ sz0) : ℝ :=
  (sz0.size n : ℝ) ^ (-(1 / 2 : ℝ)) * obs n ω

/-- The deterministic bound `f = N^{-1/2}`. -/
def fF (n : ℕ) (_ : TimeIcc s0 t0 n) : ℝ := (sz0.size n : ℝ) ^ (-(1 / 2 : ℝ))

theorem xF_nonneg (n : ℕ) (u : TimeIcc s0 t0 n) (ω : SeqΩ sz0) : 0 ≤ xF n u ω :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (obs_nonneg n ω)

theorem xF_le_fF (n : ℕ) (u : TimeIcc s0 t0 n) (ω : SeqΩ sz0) : xF n u ω ≤ fF n u := by
  unfold xF fF
  have h0 : 0 ≤ (sz0.size n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (sz0.size n : ℝ) ^ (-(1 / 2 : ℝ)) * obs n ω ≤ (sz0.size n : ℝ) ^ (-(1 / 2 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (obs_le_one n ω) h0
    _ = _ := mul_one _

theorem fF_nonneg (n : ℕ) (u : TimeIcc s0 t0 n) : 0 ≤ fF n u :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- `xF` is not constant in `ω`: `N^{-1/2} > 0` and `obs_nonconst`. -/
theorem xF_nonconst (n : ℕ) (u : TimeIcc s0 t0 n) : ∃ ω ω' : SeqΩ sz0, xF n u ω ≠ xF n u ω' := by
  obtain ⟨ω, ω', h⟩ := obs_nonconst n
  refine ⟨ω, ω', fun hx => h ?_⟩
  have hpos : (sz0.size n : ℝ) ^ (-(1 / 2 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast (sz0.one_le_size n : 0 < sz0.size n)) _).ne'
  exact mul_left_cancel₀ hpos hx

/-- **`forbidden_region` at `sz0`** (`Unif`, the only variant): `x = N^{-1/2} obs` on the window
`[0, 1/16]`, `f = N^{-1/2}`, `a = 1`, `b = 2`, `ε = 1/4`; `1(x ≤ b) x ≺ f` holds because the
indicator is `≤ f` pointwise (`prec_of_le`), and `f ≤ N^{-1/4} a`.  The conclusion is the `w.h.p.`
event that `x` avoids `[1, 2]` simultaneously for all `u` in the window. -/
theorem forbidden_region_sz0 :
    HighProbAt (seqP sz0) sz0.size
      (fun n => {ω | ∀ u : TimeIcc s0 t0 n, xF n u ω < 1 ∨ 2 < xF n u ω}) := by
  refine PerTimeCalc.Unif.forbidden_region tendsto_sz0_size
    (x := xF) (f := fF) (a := fun _ _ => 1) (b := fun _ _ => 2)
    (fun _ _ => one_pos) (ε := 1 / 4) (by norm_num) ?_ ?_
  · refine Eventually.of_forall fun n u => ?_
    unfold fF
    rw [mul_one]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_size n) (by norm_num)
  · refine Sizes.prec_of_le sz0 (ζ := fun n u _ => fF n u) (fun n u _ => fF_nonneg n u)
      fun n u ω => ?_
    by_cases hx : xF n u ω ≤ 2
    · rw [Set.indicator_of_mem (show ω ∈ {ω | xF n u ω ≤ 2} from hx)]
      exact xF_le_fF n u ω
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | xF n u ω ≤ 2} from hx)]
      exact fF_nonneg n u

/-- **`stepOneBootstrap` at `sz0`**: `M(u) = u · obs` (random, continuous in `u`), `a ≡ 1`
(continuous), `b ≡ 2`, window `[0, 1/16]`.  `M < a` on the whole window (`u obs ≤ 1/16 < 1`), so the
forbidden region `[a, b]` is avoided and `M(s) = 0 < a(s)`; the conclusion is
`M < a` on the window w.h.p.  Every hypothesis is discharged. -/
theorem stepOneBootstrap_sz0 :
    HighProbAt (seqP sz0) sz0.size
      (fun n => {ω | ∀ u : TimeIcc s0 t0 n, (u : ℝ) * obs n ω < 1}) := by
  have hlt : ∀ (n : ℕ) (u : TimeIcc s0 t0 n) (ω : SeqΩ sz0), (u : ℝ) * obs n ω < 1 := by
    intro n u ω
    have hu : (u : ℝ) ≤ 1 / 16 := u.2.2
    have hu0 : (0 : ℝ) ≤ u := by have := u.2.1; simpa [s0] using this
    have ho0 := obs_nonneg n ω
    have ho1 := obs_le_one n ω
    nlinarith
  refine PerTimeCalc.stepOneBootstrap tendsto_sz0_size
    (M := fun n u ω => u * obs n ω) (a := fun _ _ => 1) (b := fun _ _ => 2) (s := s0) (t := t0)
    ?_ (fun _ => continuousOn_const) (Eventually.of_forall fun n u => by norm_num) ?_ ?_
  · exact HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω =>
      (continuous_id.mul continuous_const).continuousOn)
  · exact HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω u => Or.inl (hlt n u ω))
  · exact HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω => by
      simp only [Set.mem_ofPred_eq, s0, zero_mul]; norm_num)

/-! ### The calculus at the random chain `Xi ≺ Ze ≺ Ch` of `StochDomAtInst`

`Xi = obs`, `Ze = 1 + obs`, `Ch = 2 + obs` on `seqP sz0`, parameter set `Unit`; every lemma of the
two variants is applied (`PerTimeDomAt` from `precPT_of_le`, `StochDomAt` from `prec_of_le`). -/

section Calculus

/-- `Xi ≺ Ze` per time. -/
theorem pt_Xi_Ze : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  Sizes.precPT_of_le sz0 Ze_nonneg fun n u ω => by unfold Xi Ze; linarith [obs_nonneg n ω]

/-- `Ze ≺ Ch` per time. -/
theorem pt_Ze_Ch : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Ze Ch :=
  Sizes.precPT_of_le sz0 Ch_nonneg fun n u ω => by unfold Ze Ch; linarith [obs_nonneg n ω]

private theorem Xi_le_Ze (n : ℕ) (u : Unit) (ω : SeqΩ sz0) : Xi n u ω ≤ Ze n u ω := by
  unfold Xi Ze; linarith [obs_nonneg n ω]

private theorem Ze_le_Ch (n : ℕ) (u : Unit) (ω : SeqΩ sz0) : Ze n u ω ≤ Ch n u ω := by
  unfold Ze Ch; linarith [obs_nonneg n ω]

/-! #### Per-time variants -/

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Xi n u ω + Ze n u ω) (fun n u ω => Ze n u ω + Ch n u ω) :=
  PerTimeCalc.PerTime.perTimeCalc_add tendsto_sz0_size pt_Xi_Ze pt_Ze_Ch

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Xi n u ω * Ze n u ω) (fun n u ω => Ze n u ω * Ch n u ω) :=
  PerTimeCalc.PerTime.perTimeCalc_mul tendsto_sz0_size (fun n u ω => Ze_nonneg n u ω)
    (fun n u ω => Ze_nonneg n u ω) pt_Xi_Ze pt_Ze_Ch

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Ze Ze :=
  PerTimeCalc.PerTime.perTimeCalc_refl tendsto_sz0_size (fun n u ω => Ze_nonneg n u ω)

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ch :=
  PerTimeCalc.PerTime.perTimeCalc_mono tendsto_sz0_size (fun n u ω => Ch_nonneg n u ω) 1
    (Eventually.of_forall fun n u ω => by simpa using Ze_le_Ch n u ω) pt_Xi_Ze

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ch :=
  PerTimeCalc.PerTime.mono_right_eventually pt_Xi_Ze
    (Eventually.of_forall fun n u ω => Ze_le_Ch n u ω)

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Xi n u ω ^ (1 / 2 : ℝ)) (fun n u ω => Ze n u ω ^ (1 / 2 : ℝ)) :=
  PerTimeCalc.PerTime.rpow_of_le_one (by norm_num) (by norm_num) (fun n u ω => Xi_nonneg n u ω)
    (fun n u ω => Ze_nonneg n u ω) pt_Xi_Ze

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Real.sqrt (Xi n u ω)) (fun n u ω => Real.sqrt (Ze n u ω)) :=
  PerTimeCalc.PerTime.sqrt_of (fun n u ω => Xi_nonneg n u ω) (fun n u ω => Ze_nonneg n u ω) pt_Xi_Ze

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.of_forall_rpow_mul fun δ hδ =>
    PerTimeCalc.PerTime.mono_right_eventually pt_Xi_Ze (Eventually.of_forall fun n u ω => by
      have h1 : (1 : ℝ) ≤ (sz0.size n : ℝ) ^ δ :=
        Real.one_le_rpow (by exact_mod_cast sz0.one_le_size n) hδ.le
      have := Ze_nonneg n u ω
      nlinarith)

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.of_le_add_sqrt_mul tendsto_sz0_size (fun n u ω => Xi_nonneg n u ω)
    (fun n u ω => Ze_nonneg n u ω)
    (PerTimeCalc.PerTime.mono_right_eventually pt_Xi_Ze (Eventually.of_forall fun n u ω => by
      have := Real.sqrt_nonneg (Ze n u ω * Xi n u ω)
      linarith))

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => ∑ _i ∈ (Finset.univ : Finset (Fin 2)), Xi n u ω)
    (fun n u ω => ∑ _i ∈ (Finset.univ : Finset (Fin 2)), Ze n u ω) :=
  PerTimeCalc.PerTime.finset_sum_of tendsto_sz0_size (Finset.univ : Finset (Fin 2))
    (ξ := fun (_ : Fin 2) => Xi) (ζ := fun (_ : Fin 2) => Ze) fun _ _ => pt_Xi_Ze

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.stochDom_of_indicator tendsto_sz0_size (Ωs := fun _ _ => (Set.univ : Set (SeqΩ sz0)))
    (HighProbAt.of_eventually_univ (Eventually.of_forall fun _ ω _ => Set.mem_univ ω))
    (by simpa only [Set.indicator_univ] using pt_Xi_Ze)

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.stochDom_of_forall_or tendsto_sz0_size (ξ₁ := Xi) (ζ₁ := Ze) (ξ₂ := Xi)
    (ζ₂ := Ze) pt_Xi_Ze pt_Xi_Ze (fun _ _ _ => Or.inl ⟨le_rfl, le_rfl⟩)

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.stochDom_of_le_const_mul tendsto_sz0_size (fun n u ω => Xi_nonneg n u ω)
    (fun n u ω => Ze_nonneg n u ω) 1 fun n u ω => by simpa using Xi_le_Ze n u ω

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.stochDom_of_le_left_eventually (ξ' := Ze)
    (Eventually.of_forall fun n u ω => Xi_le_Ze n u ω) (by
      simpa using PerTimeCalc.PerTime.perTimeCalc_refl (P := seqP sz0) (size := sz0.size)
        (U := fun _ => Unit) tendsto_sz0_size (fun n u ω => Ze_nonneg n u ω))

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.stochDom_of_highProb tendsto_sz0_size (fun n u ω => Ze_nonneg n u ω)
    (HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω u => Xi_le_Ze n u ω))

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi
    (fun n u ω => min (Ze n u ω) (Ch n u ω)) :=
  PerTimeCalc.PerTime.stochDom_min tendsto_sz0_size pt_Xi_Ze
    (PerTimeCalc.PerTime.mono_right_eventually pt_Xi_Ze (Eventually.of_forall fun n u ω => Ze_le_Ch n u ω))

/-- `Xi ≺ 1` per time (`obs ≤ 1`). -/
private theorem pt_Xi_one : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi
    (fun _ _ _ => (1 : ℝ)) :=
  Sizes.precPT_of_le sz0 (fun _ _ _ => zero_le_one) fun n u ω => by unfold Xi; exact obs_le_one n ω

/-- `Xi ≺ 1` uniformly (`obs ≤ 1`). -/
private theorem prec_Xi_one : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi
    (fun _ _ _ => (1 : ℝ)) :=
  Sizes.prec_of_le sz0 (fun _ _ _ => zero_le_one) fun n u ω => by unfold Xi; exact obs_le_one n ω

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Xi n u ω * Xi n u ω * ((1 : ℝ))⁻¹) (fun _ _ _ => 1) :=
  PerTimeCalc.PerTime.quad_le_one tendsto_sz0_size (ξp := Xi) (ξq := Xi) (f := fun _ _ => (1 : ℝ))
    (g := fun _ _ => 1) (A := fun _ _ => 1) (fun _ _ => one_pos) (fun n u ω => Xi_nonneg n u ω)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) pt_Xi_one pt_Xi_one 1
    (Eventually.of_forall fun _ _ => by norm_num)

/-! #### Uniform variants -/

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Xi n u ω + Ze n u ω) (fun n u ω => Ze n u ω + Ch n u ω) :=
  PerTimeCalc.Unif.perTimeCalc_add tendsto_sz0_size prec_Xi_Ze prec_Ze_Ch

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Xi n u ω * Ze n u ω) (fun n u ω => Ze n u ω * Ch n u ω) :=
  PerTimeCalc.Unif.perTimeCalc_mul tendsto_sz0_size (fun n u ω => Ze_nonneg n u ω)
    (fun n u ω => Ze_nonneg n u ω) prec_Xi_Ze prec_Ze_Ch

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Ze Ze :=
  PerTimeCalc.Unif.perTimeCalc_refl tendsto_sz0_size (fun n u ω => Ze_nonneg n u ω)

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ch :=
  PerTimeCalc.Unif.perTimeCalc_mono tendsto_sz0_size (fun n u ω => Ch_nonneg n u ω) 1
    (Eventually.of_forall fun n u ω => by simpa using Ze_le_Ch n u ω) prec_Xi_Ze

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ch :=
  PerTimeCalc.Unif.mono_right_eventually prec_Xi_Ze
    (Eventually.of_forall fun n u ω => Ze_le_Ch n u ω)

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Xi n u ω ^ (1 / 2 : ℝ)) (fun n u ω => Ze n u ω ^ (1 / 2 : ℝ)) :=
  PerTimeCalc.Unif.rpow_of_le_one (by norm_num) (by norm_num) (fun n u ω => Xi_nonneg n u ω)
    (fun n u ω => Ze_nonneg n u ω) prec_Xi_Ze

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Real.sqrt (Xi n u ω)) (fun n u ω => Real.sqrt (Ze n u ω)) :=
  PerTimeCalc.Unif.sqrt_of (fun n u ω => Xi_nonneg n u ω) (fun n u ω => Ze_nonneg n u ω) prec_Xi_Ze

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.of_forall_rpow_mul fun δ hδ =>
    PerTimeCalc.Unif.mono_right_eventually prec_Xi_Ze (Eventually.of_forall fun n u ω => by
      have h1 : (1 : ℝ) ≤ (sz0.size n : ℝ) ^ δ :=
        Real.one_le_rpow (by exact_mod_cast sz0.one_le_size n) hδ.le
      have := Ze_nonneg n u ω
      nlinarith)

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.of_le_add_sqrt_mul tendsto_sz0_size (fun n u ω => Xi_nonneg n u ω)
    (fun n u ω => Ze_nonneg n u ω)
    (PerTimeCalc.Unif.mono_right_eventually prec_Xi_Ze (Eventually.of_forall fun n u ω => by
      have := Real.sqrt_nonneg (Ze n u ω * Xi n u ω)
      linarith))

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => ∑ _i ∈ (Finset.univ : Finset (Fin 2)), Xi n u ω)
    (fun n u ω => ∑ _i ∈ (Finset.univ : Finset (Fin 2)), Ze n u ω) :=
  PerTimeCalc.Unif.finset_sum_of tendsto_sz0_size (Finset.univ : Finset (Fin 2))
    (ξ := fun (_ : Fin 2) => Xi) (ζ := fun (_ : Fin 2) => Ze) fun _ _ => prec_Xi_Ze

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.stochDom_of_indicator tendsto_sz0_size
    (Ωs := fun _ _ => (Set.univ : Set (SeqΩ sz0)))
    (HighProbAt.of_eventually_univ (Eventually.of_forall fun _ ω _ => Set.mem_univ ω))
    (by
      have h : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze := prec_Xi_Ze
      simpa only [Set.indicator_univ] using h)

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.stochDom_of_forall_or tendsto_sz0_size (ξ₁ := Xi) (ζ₁ := Ze) (ξ₂ := Xi)
    (ζ₂ := Ze) prec_Xi_Ze prec_Xi_Ze (fun _ _ _ => Or.inl ⟨le_rfl, le_rfl⟩)

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.stochDom_of_le_const_mul tendsto_sz0_size (fun n u ω => Xi_nonneg n u ω)
    (fun n u ω => Ze_nonneg n u ω) 1 fun n u ω => by simpa using Xi_le_Ze n u ω

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.stochDom_of_le_left_eventually (ξ' := Ze)
    (Eventually.of_forall fun n u ω => Xi_le_Ze n u ω)
    (PerTimeCalc.Unif.perTimeCalc_refl tendsto_sz0_size (fun n u ω => Ze_nonneg n u ω))

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.stochDom_of_highProb tendsto_sz0_size (fun n u ω => Ze_nonneg n u ω)
    (HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω u => Xi_le_Ze n u ω))

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi
    (fun n u ω => min (Ze n u ω) (Ch n u ω)) :=
  PerTimeCalc.Unif.stochDom_min tendsto_sz0_size prec_Xi_Ze
    (PerTimeCalc.Unif.mono_right_eventually prec_Xi_Ze
      (Eventually.of_forall fun n u ω => Ze_le_Ch n u ω))

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n u ω => Xi n u ω * Xi n u ω * ((1 : ℝ))⁻¹) (fun _ _ _ => 1) :=
  PerTimeCalc.Unif.quad_le_one tendsto_sz0_size (ξp := Xi) (ξq := Xi) (f := fun _ _ => (1 : ℝ))
    (g := fun _ _ => 1) (A := fun _ _ => 1) (fun _ _ => one_pos) (fun n u ω => Xi_nonneg n u ω)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) prec_Xi_one prec_Xi_one 1
    (Eventually.of_forall fun _ _ => by norm_num)

/-! #### `HighProbAt` helpers, the real facts, and the base layer -/

example : HighProbAt (seqP sz0) sz0.size (fun n => {ω | ∀ u : Unit, Xi n u ω ≤ Ze n u ω}) :=
  PerTimeCalc.perTimeCalc_highProbAt_mono
    (HighProbAt.of_eventually_univ (Eventually.of_forall fun _ ω => Set.mem_univ ω))
    (Eventually.of_forall fun n ω _ u => Xi_le_Ze n u ω)

example : HighProbAt (seqP sz0) sz0.size (fun n => {ω | ∀ u : Unit, Xi n u ω ≤ Ze n u ω} ∩ Set.univ) :=
  PerTimeCalc.perTimeCalc_highProbAt_inter tendsto_sz0_size
    (HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω u => Xi_le_Ze n u ω))
    (HighProbAt.of_eventually_univ (Eventually.of_forall fun _ ω => Set.mem_univ ω))

example : HighProbAt (seqP sz0) sz0.size
    (fun n => {ω | ∀ u : Unit, Xi n u ω ≤ (sz0.size n : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω}) :=
  PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt prec_Xi_Ze (by norm_num)

example : (1 : ℝ) ^ 2 ≤ 4 * (1 : ℝ) ^ 2 * 1 ^ 2 :=
  PerTimeCalc.sq_le_four_mul_of_le_add_mul (s := 1) (r := 1) (T := 1) (by norm_num) le_rfl
    (by norm_num)

example : ((2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ)) < 1 :=
  PerTimeCalc.rpow_mul_rpow_neg_lt_one (N := 2) le_rfl (τ := 1 / 2) (ε := 1) (by norm_num)

example : ∀ u ∈ Set.Icc (0 : ℝ) 1, (fun u : ℝ => u / 2) u < (fun _ : ℝ => (1 : ℝ)) u :=
  PerTimeCalc.lt_of_forall_ne_of_continuousOn (g := fun u : ℝ => u / 2) (a := fun _ => (1 : ℝ))
    (s := 0) (t := 1) (by fun_prop) continuousOn_const (by norm_num)
    (fun u hu => by
      have := hu.2
      intro h
      linarith)

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.perTimeCalc_of_imp pt_Xi_Ze (fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun _ _ _ h => h⟩)

example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.PerTime.perTimeCalc_of_imp_union tendsto_sz0_size pt_Xi_Ze pt_Xi_Ze
    (ξ₁ := Xi) (ζ₁ := Ze) (ξ₂ := Xi) (ζ₂ := Ze) (fun τ hτ =>
      ⟨τ, hτ, Eventually.of_forall fun _ _ _ h => Or.inl h⟩)

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.perTimeCalc_of_imp prec_Xi_Ze (fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun _ _ _ h => h⟩)

example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  PerTimeCalc.Unif.perTimeCalc_of_imp_union tendsto_sz0_size prec_Xi_Ze prec_Xi_Ze
    (ξ₁ := Xi) (ζ₁ := Ze) (ξ₂ := Xi) (ζ₂ := Ze) (fun τ hτ =>
      ⟨τ, hτ, Eventually.of_forall fun _ _ _ h => Or.inl h⟩)

end Calculus

end RBM.Ind.PerTimeCalcInst

end
