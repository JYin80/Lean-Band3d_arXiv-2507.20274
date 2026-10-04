/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Iterate
import RBM3D.Green.GbEXP

/-!
# ST2-16 (ticket T2130, part 1): `(initialGT2)` at every time and `(Gt_avgbound_flow)`

The closing paragraph of Step 2 (`paper/tex/3_5_Loop_Hierarchy.tex:455–465`): `(eq:L2_decay)`
(`STL2decayPT`) and the weak law `(Gtmwc)` (`STStep1Weak`) verify `(initialGT2)` at every time
(`stInitialGT2_of_L2decay`), and `lem_GbEXP` (`stGbEXP_holds`, `(GavLGEX)`) gives
`(Gt_avgbound_flow)` per time (`stStep2AvgPT_of_L2decay`).  The part 2 file `LocalAvg2.lean`
gives `(Gt_bound_flow)` and the pin `STLocalAvgOfL2`.

* The control of `(initialGT2)` is `Ψ_u = max(W^{-d/2}, (W^{-d} B_{u,0})^{1/2})` (`stLocalPsi`), a
  constant multiple of the paper's `Ψ_u = (W^{-d} B_{u,0})^{1/2}` on the window
  `W^{-d/2} ≤ Ψ_u ≤ W^{-ε₀}` (paper-delta candidate `T2130a`).
* `ε₀ = min(1/2, d c / 8)`, `c` of the size data `ST_Bdata_holds`: `W^{-d} B_{u,0} ≤ N^{-c}` for
  `u ≤ t_n ≤ lemT z_n`, and `cB W^{-d} ≤ W^{-d} B_{u,0}`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Generic tools for `StochDomAt` -/

section Tools

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- `≺` from a family of events of high probability on which the bound holds deterministically
(eventually in `l`), one event for each `τ`. -/
theorem localAvg1_stochDomAt_of_whp {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), ∃ Ξ : ℕ → Set Ω, HighProbAt P size Ξ ∧
      ∀ᶠ l in atTop, ∀ ω ∈ Ξ l, ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨Ξ, hΞ, hev⟩ := h τ hτ
  filter_upwards [hΞ D hD, hev] with l hl hl2
  refine le_trans (measure_mono ?_) hl
  intro ω hω
  by_contra hmem
  obtain ⟨u, hu⟩ := hω
  exact absurd (hl2 ω (by simpa using hmem) u) (not_le.2 hu)

/-- `ξ ≺ ζ'` and `ζ' ≤ C ζ` (eventually, `ζ ≥ 0`) give `ξ ≺ ζ`: constants are absorbed by `N^τ`. -/
theorem localAvg1_domAt_of_le_const (hsize : Tendsto size atTop atTop)
    {ξ ζ ζ' : ∀ l, U l → Ω → ℝ} {C : ℝ} (h : StochDomAt P size ξ ζ')
    (hle : ∀ᶠ l in atTop, (∀ u ω, 0 ≤ ζ l u ω) ∧ ∀ u ω, ζ' l u ω ≤ C * ζ l u ω) :
    StochDomAt P size ξ ζ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, hsize.eventually (eventually_le_rpow C (half_pos hτ))] with l hl hcN
  obtain ⟨h0, hl⟩ := hl
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (size l : ℝ) ^ (τ / 2) * ζ' l u ω ≤ (size l : ℝ) ^ (τ / 2) * (C * ζ l u ω) :=
        mul_le_mul_of_nonneg_left (hl u ω) hpos
    _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcN (h0 u ω)) hpos
    _ = (size l : ℝ) ^ τ * ζ l u ω := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
    _ < ξ l u ω := hu

/-- Uniform `≺` implies per-time `≺` (each event is contained in the union). -/
theorem localAvg1_perTime_of_stoch {ξ ζ : ∀ l, U l → Ω → ℝ} (h : StochDomAt P size ξ ζ) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  refine le_trans (measure_mono ?_) hl
  intro ω hω
  exact ⟨u, hω⟩

end Tools

/-! ## 2. The profile `STWB`: comparison lemmas and the numerics of the window -/

section WB

variable {d : ℕ} (sz : Sizes d)

/-- `W^{-d} B_{u,K} ≤ W^{-d} B_{u,0} = Bctl` (`B_{u,K}` is non-increasing in `K`). -/
theorem localAvg1_STWB_le (n : ℕ) (u : ℝ) (K : ℕ) : STWB sz n u K ≤ sz.Bctl n u := by
  unfold STWB Sizes.Bctl Bparam
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ (d - 2) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
  have h2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hA : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
  have h3 : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h2 hA]

/-- `((K+1)^{d-2})⁻¹ · Bctl ≤ W^{-d} B_{u,K}`. -/
theorem localAvg1_STWB_ge (n : ℕ) (u : ℝ) (K : ℕ) :
    (((K : ℝ) + 1) ^ (d - 2))⁻¹ * sz.Bctl n u ≤ STWB sz n u K := by
  unfold STWB Sizes.Bctl Bparam
  have h1 : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ (d - 2) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
  have h2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hA : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
  have hC : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by positivity
  have hf : 0 ≤ (((K : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hW : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have h3 : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
  rw [h3]
  set f := (((K : ℝ) + 1) ^ (d - 2))⁻¹
  set A := (sz.lam n ^ 2 + |1 - u|)⁻¹
  set Cc := (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹
  set w := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
  have : f * (w * (A * 1 + Cc)) = w * (A * f + f * Cc) := by ring
  rw [this]
  refine mul_le_mul_of_nonneg_left ?_ hW
  nlinarith [mul_le_mul_of_nonneg_right h2 hC]

/-- `B_{u,K'} ≤ 3^{d-2} B_{u,K}` as soon as `K ≤ K' + 2` (so `K + 1 ≤ 3 (K' + 1)`). -/
theorem localAvg1_STWB_comp (n : ℕ) (u : ℝ) {K K' : ℕ} (h : K ≤ K' + 2) :
    STWB sz n u K' ≤ (3 : ℝ) ^ (d - 2) * STWB sz n u K := by
  unfold STWB Bparam
  have hA : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
  have hC : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by positivity
  have hW : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hx : (0 : ℝ) < (K' : ℝ) + 1 := by positivity
  have hy : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hyx : (K : ℝ) + 1 ≤ 3 * ((K' : ℝ) + 1) := by
    have : (K : ℝ) ≤ (K' : ℝ) + 2 := by exact_mod_cast h
    nlinarith [(Nat.cast_nonneg K' : (0 : ℝ) ≤ K')]
  have hpow : ((K : ℝ) + 1) ^ (d - 2) ≤ (3 : ℝ) ^ (d - 2) * ((K' : ℝ) + 1) ^ (d - 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hy.le hyx _
  have hf : (((K' : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (3 : ℝ) ^ (d - 2) * (((K : ℝ) + 1) ^ (d - 2))⁻¹ := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (d - 2) := by positivity
    calc (((K' : ℝ) + 1) ^ (d - 2))⁻¹
        = (3 : ℝ) ^ (d - 2) * ((3 : ℝ) ^ (d - 2) * ((K' : ℝ) + 1) ^ (d - 2))⁻¹ := by
          field_simp
      _ ≤ (3 : ℝ) ^ (d - 2) * (((K : ℝ) + 1) ^ (d - 2))⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpow) h3.le
  have h31 : (1 : ℝ) ≤ (3 : ℝ) ^ (d - 2) := one_le_pow₀ (by norm_num)
  set f' := (((K' : ℝ) + 1) ^ (d - 2))⁻¹
  set f := (((K : ℝ) + 1) ^ (d - 2))⁻¹
  set A := (sz.lam n ^ 2 + |1 - u|)⁻¹
  set Cc := (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹
  set w := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
  set T := (3 : ℝ) ^ (d - 2)
  have : T * (w * (A * f + Cc)) = w * (T * (A * f) + T * Cc) := by ring
  rw [this]
  refine mul_le_mul_of_nonneg_left ?_ hW
  nlinarith [mul_le_mul_of_nonneg_left hf hA, mul_le_mul_of_nonneg_right h31 hC]

/-- `(y^{1/2})² = y` for `y ≥ 0`. -/
theorem localAvg1_rpow_half_sq {y : ℝ} (hy : 0 ≤ y) : (y ^ (1 / 2 : ℝ)) ^ 2 = y := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hy]

/-- The control of `(initialGT2)`: `Ψ_u = max(W^{-d/2}, (W^{-d} B_{u,0})^{1/2})` (paper:
`Ψ_u = (W^{-d} B_{u,0})^{1/2}`; the `max` makes the lower window `W^{-d/2} ≤ Ψ_u` hold, T2130a). -/
def stLocalPsi (sz : Sizes d) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ((sz.Bctl n (u n)) ^ (1 / 2 : ℝ))

/-- The numerics of the window at one size index (`B = W^{-d} B_{u,0}`; the exponents of the
preflight table (a): `ε₀ ≤ 1/2`, `ε₀ ≤ d c / 8`). -/
theorem localAvg1_det (n : ℕ) (hd : 0 < d) {cB c ε₀ B : ℝ} (hcB : 0 < cB) (hc : 0 < c)
    (hε₀1 : ε₀ ≤ 1 / 2) (hε₀2 : ε₀ ≤ d * c / 8)
    (hlow : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ B) (hup : B ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) :
    ((sz.size n : ℕ) : ℝ) ^ (c / 8) * B ^ (1 / 4 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ∧
    max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (B ^ (1 / 2 : ℝ)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ∧
    B ≤ (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (B ^ (1 / 2 : ℝ))) ^ 2 ∧
    (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (B ^ (1 / 2 : ℝ))) ^ 2 ≤ (cB⁻¹ + 1) * B ∧
    0 < B := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWd : (0 : ℝ) < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hB0 : 0 < B := lt_of_lt_of_le (mul_pos hcB hWd) hlow
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- `N^{-c/8} ≤ W^{-ε₀}`
  have hNW : ((sz.size n : ℕ) : ℝ) ^ (-(c / 8)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
    (ST_size_rpow_neg_le sz n (by positivity : 0 ≤ c / 8)).trans
      (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (c / 8) * B ^ (1 / 4 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
    have hB4 : B ^ (1 / 4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c * (1 / 4 : ℝ)) := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow hB0.le hup (by norm_num)
    calc ((sz.size n : ℕ) : ℝ) ^ (c / 8) * B ^ (1 / 4 : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (c / 8) * ((sz.size n : ℕ) : ℝ) ^ (-c * (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hB4 (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (-(c / 8)) := by
          rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ _ := hNW
  have hhalf : B ^ (1 / 2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
    have hB2 : B ^ (1 / 2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c * (1 / 2 : ℝ)) := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow hB0.le hup (by norm_num)
    refine hB2.trans ?_
    have : ((sz.size n : ℕ) : ℝ) ^ (-c * (1 / 2 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(c / 8)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    exact this.trans hNW
  have hWhalf : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hsq1 : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [ST_rpow_neg_half hW0.le, localAvg1_rpow_half_sq hWd.le]
  have hWB : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ cB⁻¹ * B := by
    rw [le_inv_mul_iff₀ hcB]; linarith
  have hmax_sq : (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (B ^ (1 / 2 : ℝ))) ^ 2 ≤
      (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 + (B ^ (1 / 2 : ℝ)) ^ 2 := by
    have hp1 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hW0.le _
    have hp2 : 0 ≤ B ^ (1 / 2 : ℝ) := Real.rpow_nonneg hB0.le _
    rcases le_total (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (B ^ (1 / 2 : ℝ)) with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2))]
    · rw [max_eq_left h]; nlinarith [sq_nonneg (B ^ (1 / 2 : ℝ))]
  refine ⟨h1, max_le hWhalf hhalf, ?_, ?_, hB0⟩
  · calc B = (B ^ (1 / 2 : ℝ)) ^ 2 := (localAvg1_rpow_half_sq hB0.le).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hB0.le _) (le_max_right _ _) 2
  · refine hmax_sq.trans ?_
    rw [hsq1, localAvg1_rpow_half_sq hB0.le]
    linarith

end WB

/-! ## 3. The events of high probability at a time section -/

section Events

variable {d : ℕ} (sz : Sizes d)

/-- The size data of `ST_Bdata_holds` at the constants of the flow: `cB W^{-d} ≤ W^{-d} B_{u,0} ≤
N^{-c}` for `0 ≤ u ≤ t_n ≤ lemT z_n`, eventually in `n`. -/
theorem localAvg1_data {d : ℕ} (hd : 0 < d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (𝔠 : ℝ) :
    ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧
            sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
  obtain ⟨cB, hcB, hall⟩ := ST_Bdata_holds hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hall'⟩ := hall 𝔠
  exact ⟨cB, c, hcB, hc, hall'⟩

private theorem localAvg1_card_Zd (n : ℕ) : Fintype.card (Zd d (sz.L n)) ≤ sz.size n := by
  have h : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := by simp [Zd, ZMod.card]
  rw [h]
  unfold Sizes.size
  exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d

/-- **`(eq:L2_decay)` at a section, uniformly in `(a,b)`** (the union over the `≤ N²` pairs is
absorbed: `D ↦ D + 2`): w.h.p., for every `τ > 0`, `‖𝓛^{(2)}_{u,(-,+),(a,b)}‖ ≤ N^τ W^{-d}
B_{u,|a-b|}` for all `a, b`. -/
theorem localAvg1_whp_L2 {E s t : ℕ → ℝ} (hL2 : STL2decayPT sz E s t) {u : ℕ → ℝ}
    (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) {τ : ℝ} (hτ : 0 < τ) :
    sz.Whp (fun n => {ω | ∀ a b : Zd d (sz.L n),
      ‖Lloop sz n (E n) (u n) ![false, true] ![a, b] ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * STWB sz n (u n) (zdistInf d (sz.L n) (a - b))}) := by
  have hsec := Green.perSeq_of_perTime_timeIcc sz.seqP sz.size (s := s) (t := t)
    (V := fun n => Fin 2 → Zd d (sz.L n)) (fun n => ⟨0⟩)
    (fun n v p ω => ‖Lloop sz n (E n) v ![false, true] p ω‖)
    (fun n v p _ => STWB sz n v (zdistInf d (sz.L n) (p 0 - p 1))) hL2 u hu
  have h1 : HighProbAt sz.seqP sz.size (fun n => ⋂ k : Fin 2 → Zd d (sz.L n),
      {ω | ‖Lloop sz n (E n) (u n) ![false, true] k ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * STWB sz n (u n) (zdistInf d (sz.L n) (k 0 - k 1))}) := by
    refine Path.highProbAt_iInter sz.seqP sz.size (C := 2) (by norm_num)
      (Eventually.of_forall fun n => ?_) ?_
    · have hc : Fintype.card (Fin 2 → Zd d (sz.L n)) = Fintype.card (Zd d (sz.L n)) ^ 2 := by
        simp
      rw [hc, Real.rpow_two]
      push_cast
      have := localAvg1_card_Zd sz n
      have h2 : ((Fintype.card (Zd d (sz.L n)) : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
        exact_mod_cast this
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2
    · intro D hD
      filter_upwards [hsec τ hτ D hD] with n hn k
      have h3 := hn ((), k)
      have : (({ω | ‖Lloop sz n (E n) (u n) ![false, true] k ω‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * STWB sz n (u n) (zdistInf d (sz.L n) (k 0 - k 1))} :
          Set sz.SeqΩ))ᶜ = {ω | ((sz.size n : ℕ) : ℝ) ^ τ *
            STWB sz n (u n) (zdistInf d (sz.L n) (k 0 - k 1)) <
            ‖Lloop sz n (E n) (u n) ![false, true] k ω‖} := by
        ext ω; simp
      rw [this]
      exact h3
  refine h1.mono (Eventually.of_forall fun n ω hω a b => ?_)
  have := Set.mem_iInter.1 hω ![a, b]
  simpa using this

/-- **`‖G_u - M‖_max ≤ W^{-ε₀}` w.h.p.** (`Ω(u, ε₀)`), from the weak law `(Gtmwc)` at the section
`u` (`‖G_u - M‖_max ≺ (W^{-d}B_{u,0})^{1/4}`) at the exponent `τ = c/8`, when
`N^{c/8} (W^{-d}B_{u,0})^{1/4} ≤ W^{-ε₀}` eventually. -/
theorem localAvg1_whp_omega {E s t : ℕ → ℝ} (hweak : STStep1Weak sz E s t) {u : ℕ → ℝ}
    (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) {c ε₀ : ℝ} (hc : 0 < c)
    (hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n (u n)) ^ (1 / 4 : ℝ) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) :
    sz.Whp (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖STGM sz n (E n) (u n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)}) := by
  have hweak' : StochDomAt sz.seqP sz.size
      (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) := hweak
  have h1 := StochDomAt.precomp_param hweak'
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n v => (⟨u n, hu n⟩, v))
  have h2 := h1.highProb (τ := c / 8) (by positivity)
  refine HighProbAt.mono h2 ?_
  filter_upwards [hev] with n hn ω hω x y
  exact (hω (x, y)).trans hn

/-- The maximum over `(a,b)` of the two-loops is controlled by the bound on every `𝓛^{(2)}`:
`max_{a,b} ‖𝓛^{(2)}_{(-,+),(a,b)}‖ ≤ X · W^{-d} B_{u,0}`. -/
theorem localAvg1_maxLoop2_le (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) {X : ℝ} (hX : 0 ≤ X)
    (hL : ∀ a b : Zd d (sz.L n), ‖Lloop sz n E u ![false, true] ![a, b] ω‖ ≤
      X * STWB sz n u (zdistInf d (sz.L n) (a - b))) :
    STmaxLoop2 sz n E u ω ≤ X * sz.Bctl n u := by
  unfold STmaxLoop2
  refine Finset.sup'_le _ _ fun p _ => ?_
  exact (hL p.1 p.2).trans (mul_le_mul_of_nonneg_left (localAvg1_STWB_le sz n u _) hX)

end Events

/-! ## 4. Item 1: `(initialGT2)` at every time -/

section Item1

variable {d : ℕ}

/-- **`(initialGT2)` at every time** (`3_5:28–30`, `455–460`): under `(eq:L2_decay)` (`STL2decayPT`)
and the weak law `(Gtmwc)` (`STStep1Weak`), for every flow and `0 ≤ s ≤ t ≤ lemT z`, there are
`ε₀ > 0` and `CΨ > 0` (depending only on `d, κ, ε, 𝔡, 𝔠`) such that for every time sequence
`u_n ∈ [s_n, t_n]`, the control `Ψ_u = max(W^{-d/2}, (W^{-d} B_{u,0})^{1/2})` (`stLocalPsi`)
satisfies, eventually in `n`, the window `W^{-d/2} ≤ Ψ_u ≤ W^{-ε₀}` and `W^{-d} B_{u,0} ≤ Ψ_u² ≤
CΨ W^{-d} B_{u,0}`, and `(initialGT2)` holds at `(u, ε₀, Ψ_u)`: `‖G_u - M‖_max ≺ W^{-ε₀}` and
`max_{a,b} 𝓛^{(2)}_{u,(-,+),(a,b)} ≺ Ψ_u²`.  Here `ε₀ = min(1/2, d c/8)`, `CΨ = cB⁻¹ + 1`, with
`cB, c` of the size data `ST_Bdata_holds` (`Ψ_u ≤ W^{-ε₀}` comes from `W^{-d} B_{u,0} ≤ N^{-c}`
for `u ≤ t ≤ lemT z`).  Needs only `0 < d` (no `lem_GbEXP` input; items 2-4 add `3 ≤ d`). -/
theorem stInitialGT2_of_L2decay (hd : 0 < d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {𝔠 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ lemT (z n))
    (hweak : STStep1Weak sz (STflowE z) s t) (hL2 : STL2decayPT sz (STflowE z) s t) :
    ∃ ε₀ CΨ : ℝ, 0 < ε₀ ∧ 0 < CΨ ∧ ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ stLocalPsi sz u n ∧
        stLocalPsi sz u n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ∧
        sz.Bctl n (u n) ≤ stLocalPsi sz u n ^ 2 ∧
        stLocalPsi sz u n ^ 2 ≤ CΨ * sz.Bctl n (u n)) ∧
      STInitialGT2 sz (STflowE z) u ε₀ (stLocalPsi sz u) := by
  obtain ⟨cB, c, hcB, hc, hdat⟩ := localAvg1_data hd hκ hε h𝔡 𝔠
  have hev := hdat sz z hflow t (fun n => (hs n).trans (hst n)) htl
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hflow.1.2.2.1
  have hε₀pos : 0 < min (1 / 2 : ℝ) (d * c / 8) :=
    lt_min (by norm_num) (by have : (0 : ℝ) < d := by exact_mod_cast hd
                             positivity)
  refine ⟨min (1 / 2 : ℝ) (d * c / 8), cB⁻¹ + 1, hε₀pos, by positivity, fun u hu => ?_⟩
  have hfact : ∀ᶠ n in atTop,
      ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n (u n)) ^ (1 / 4 : ℝ) ≤
          ((sz.W n : ℕ) : ℝ) ^ (-min (1 / 2 : ℝ) (d * c / 8)) ∧
      stLocalPsi sz u n ≤ ((sz.W n : ℕ) : ℝ) ^ (-min (1 / 2 : ℝ) (d * c / 8)) ∧
      sz.Bctl n (u n) ≤ stLocalPsi sz u n ^ 2 ∧
      stLocalPsi sz u n ^ 2 ≤ (cB⁻¹ + 1) * sz.Bctl n (u n) := by
    filter_upwards [hev] with n hn
    obtain ⟨h1, h2⟩ := hn (u n) ((hs n).trans (hu n).1) (hu n).2
    obtain ⟨a1, a2, a3, a4, -⟩ := localAvg1_det sz n hd hcB hc (min_le_left _ _)
      (min_le_right _ _) h1 h2
    exact ⟨a1, a2, a3, a4⟩
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hfact] with n hn
    exact ⟨le_max_left _ _, hn.2.1, hn.2.2.1, hn.2.2.2⟩
  · -- `‖G_u - M‖_max ≺ W^{-ε₀}`
    refine localAvg1_stochDomAt_of_whp fun τ hτ => ?_
    refine ⟨_, localAvg1_whp_omega sz hweak hu hc (hfact.mono fun n hn => hn.1), ?_⟩
    refine Eventually.of_forall fun n ω hω v => ?_
    have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
      Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ.le
    have h2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-min (1 / 2 : ℝ) (d * c / 8)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ‖STGM sz n (STflowE z n) (u n) ω v.1 v.2‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (-min (1 / 2 : ℝ) (d * c / 8)) := hω v.1 v.2
      _ ≤ _ := by nlinarith
  · -- `max_{a,b} 𝓛^{(2)} ≺ Ψ_u²`
    refine localAvg1_stochDomAt_of_whp fun τ hτ => ?_
    refine ⟨_, localAvg1_whp_L2 sz hL2 hu hτ, ?_⟩
    filter_upwards [hfact] with n hn ω hω _
    have h1 := localAvg1_maxLoop2_le sz n (STflowE z n) (u n) ω
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hω)
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left hn.2.2.1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end Item1

/-! ## 5. Item 2: `(Gt_avgbound_flow)` per time -/

section Item2

variable {d : ℕ}

/-- **`(Gt_avgbound_flow)` per time** (`3_5:462–465`): `max_a |𝓛^{(1)}_{u,+,a} - m| ≺ W^{-d} B_{u,0}`
uniformly in `u ∈ [s,t]` (per time), from `(GavLGEX)` of `lem_GbEXP` (`stGbEXP_holds`) at the
control `Ψ_u` of `stInitialGT2_of_L2decay` and `Ψ_u² ≤ CΨ W^{-d} B_{u,0}`.  The hypothesis
`3 ≤ d` is that of `stGbEXP_holds` (DECISIONS §36). -/
theorem stStep2AvgPT_of_L2decay (hd : 3 ≤ d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {𝔠 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ lemT (z n))
    (hweak : STStep1Weak sz (STflowE z) s t) (hL2 : STL2decayPT sz (STflowE z) s t) :
    STStep2AvgPT sz (STflowE z) s t := by
  have hd0 : 0 < d := by omega
  obtain ⟨ε₀, CΨ, hε₀, hCΨ, hinit⟩ :=
    stInitialGT2_of_L2decay hd0 hκ hε h𝔡 hflow hs hst htl hweak hL2
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hflow.1.2.2.1
  refine Green.perTime_timeIcc_of_forall_seq sz.seqP sz.size hst
    (V := fun n => Zd d (sz.L n)) (fun n => ⟨0⟩)
    (fun n v a ω => ‖Lloop sz n (STflowE z n) v (fun _ : Fin 1 => true) (fun _ => a) ω -
      mE (STflowE z n)‖)
    (fun n v _ _ => sz.Bctl n v) ?_
  intro u hu
  obtain ⟨hwin, hinit_u⟩ := hinit u hu
  have hav := (Green.stGbEXP_holds hd).2.2 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u
    (fun n => (hs n).trans (hu n).1) (fun n => (hu n).2.trans (htl n)) ε₀ hε₀
    (stLocalPsi sz u) (hwin.mono fun n h => h.1) (hwin.mono fun n h => h.2.1)
    hinit_u.1 hinit_u.2
  have h2 : StochDomAt sz.seqP sz.size (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖Lloop sz n (STflowE z n) (u n) (fun _ : Fin 1 => true) (fun _ => a) ω -
        mE (STflowE z n)‖) (fun n _ _ => sz.Bctl n (u n)) :=
    localAvg1_domAt_of_le_const hsize hav (C := CΨ)
      (hwin.mono fun n h => ⟨fun _ _ => (STBctl_pos sz n ((hu n).2.trans_lt
        ((htl n).trans_lt (lemT_lt_one (ST_flow_im_pos sz hflow n))))).le, fun _ _ => h.2.2.2⟩)
  exact localAvg1_perTime_of_stoch (h2.precomp_param (V := fun n => Unit × Zd d (sz.L n))
    (fun n p => p.2))

end Item2

end RBM.Gauss.Sizes

/-! ## 6. Compiled nonempty instances at `d = 3`

The merged flow instance `(sz0, z0)` (`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`),
the window `s ≡ 0`, `t ≡ 1/16 ≤ lemT z0` (`Step2IterateInst.hs0`, `hst`, `htT`, `flow_z0`) and the
time section `u ≡ 1/32`.  Every deterministic hypothesis is discharged; what stays a hypothesis is the
weak law `STStep1Weak` and `(eq:L2_decay)` `STL2decayPT`, the outputs of other gates. -/

namespace RBM.Gauss.LocalAvg1Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step2IterateInst Filter

/-- **Item 1 at the data**: `(initialGT2)` at the time section `u ≡ 1/32`, with the window
`W^{-3/2} ≤ Ψ_u ≤ W^{-ε₀}`. -/
example (hweak : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hL2 : STL2decayPT sz0 (STflowE z0) sInst tInst) :
    ∃ ε₀ CΨ : ℝ, 0 < ε₀ ∧ 0 < CΨ ∧
      (∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤
          stLocalPsi sz0 (fun _ => 1 / 32) n ∧
        stLocalPsi sz0 (fun _ => 1 / 32) n ≤ ((sz0.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
      STInitialGT2 sz0 (STflowE z0) (fun _ => 1 / 32) ε₀ (stLocalPsi sz0 (fun _ => 1 / 32)) := by
  obtain ⟨ε₀, CΨ, h1, h2, h⟩ := stInitialGT2_of_L2decay (by norm_num : 0 < 3)
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 hs0 hst htT hweak hL2
  obtain ⟨hw, hi⟩ := h (fun _ => 1 / 32) (fun n => by
    simp only [sInst, tInst, Set.mem_Icc]; norm_num)
  exact ⟨ε₀, CΨ, h1, h2, hw.mono fun n hn => ⟨hn.1, hn.2.1⟩, hi⟩

/-- **Item 2 at the data**: `(Gt_avgbound_flow)` per time on `[0, 1/16]`. -/
example (hweak : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hL2 : STL2decayPT sz0 (STflowE z0) sInst tInst) :
    STStep2AvgPT sz0 (STflowE z0) sInst tInst :=
  stStep2AvgPT_of_L2decay (by norm_num : 3 ≤ 3) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 hs0 hst htT hweak hL2

end RBM.Gauss.LocalAvg1Inst
