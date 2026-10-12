/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGridTail

/-!
# BA stage TL, row TL2a3 (T2438), part 2: the tail at one size index, the asymptotics, `baTwistGridTail_holds` and its instance

Continuation of `RBM3D/BA/TwistGridTail.lean` (split file named by the ticket; import order `TwistGridTail → TwistGridTail2`).

* `TwistGridTail2_core`: the tail of `twMart` at one size index (twin of `difRepTail_core`, `Path/DifREP2.lean:1951`):
  `μ (∃ k ≤ K, N^{ε'} (Σ_{j<k} Δ ‖twEEk_j‖ + N^{-D})^{1/2} < ‖twMart_k‖) ≤ N^{-D}` from the three numerical budgets
  (shift, `Y`, `Z`) and `η_{u_j} ≥ 1/(16 N)` along the grid.
* `TwistGridTail2_eventually_Z`: the `Z` budget holds for large `N` (polynomial levels against `e^{-N^{2ε'}/64}`).
* **`baTwistGridTail_holds d : BATwistGridTail d`** for every `d` (`CK = 2 D + 20`), and its compiled nonempty instance.

Every helper is `private` or prefixed `TwistGridTail2_`; the private helpers of `TwistGridTail.lean` and of the
merged band files are reached through `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private TwistGridTail_Zv TwistGridTail_Yv TwistGridTail_aSeq TwistGridTail_martInc_ae TwistGridTail_Z_tail
  TwistGridTail_Y_tail TwistGridTail_eta_pos TwistGridTail_Hh_herm TwistGridTail_norm_twEEM from RBM3D.BA.TwistGridTail
open private difRepTail_K_mul_step difRepTail_gridTime_le difRepTail_gridTime_nonneg difRepTail_tendsto_rpow_exp
  from RBM3D.Path.DifREP2

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.Ind RBM.Loop

/-! ## 1. The tail at one size index -/

section Core

variable {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- **The tail of `twMart` at one size index** (twin of `difRepTail_core`): given the three numerical budgets (shift sum,
`Y` part, `Z` levels) and `η_{u_j} ≥ 1/(16 N)` along the grid, at the label `(σ; b, c₁, c₂)`,
`μ (∃ k ≤ K, N^{ε'} (Σ_{j<k} Δ ‖twEEk_j‖ + N^{-D})^{1/2} < ‖twMart_k‖) ≤ N^{-D}`. -/
private theorem TwistGridTail2_core (hm : 0 < (BAmF sz lam0 E n).im) (hmn : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε')
    (hη : ∀ j, j ≤ K n → 1 / (16 * (sz.size n : ℝ)) ≤ etaOf (BAmF sz lam0 E n) (gridTime s t K n j))
    (hshift : (24 * 16 ^ 7) * (sz.size n : ℝ) ^ 9 * gridStep s t K n ≤ (sz.size n : ℝ) ^ (-D))
    (hY : 16 * gridStep s t K n * ((768 * 36 * 16 ^ 8) * (sz.size n : ℝ) ^ 18) * (sz.size n : ℝ) ^ D ≤ (sz.size n : ℝ) ^ (-D) / 2)
    (hZ : ((⌈(4 * 16 ^ 6) * (sz.size n : ℝ) ^ 8 * (sz.size n : ℝ) ^ D⌉₊ : ℝ) + 1) *
        (4 * Real.exp (-((sz.size n : ℝ) ^ ε' / 2) ^ 2 / (16 * (1 : ℝ)))) ≤ (sz.size n : ℝ) ^ (-D) / 2)
    (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n)) :
    ((baStep2Mat sz lam0 E).Pp) {ω | ∃ k, k ≤ K n ∧
      (sz.size n : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n * ‖twEEk sz lam0 E s t K n σ b c₁ c₂ j ω‖ +
        (sz.size n : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) < ‖twMart sz lam0 E s t K n σ b c₁ c₂ k ω‖} ≤
      ENNReal.ofReal ((sz.size n : ℝ) ^ (-D)) := by
  set N : ℝ := (sz.size n : ℝ) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  have hKΔ : (K n : ℝ) * Δ ≤ 1 := by
    rw [hΔdef, difRepTail_K_mul_step s t K n hK]; linarith
  set δ : ℝ := N ^ (-D) with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN0 _
  have hNδ : N ^ D * δ = 1 := by
    rw [hδdef, ← Real.rpow_add hN0]; simp
  set ρ : ℝ := N ^ ε' / 2 with hρdef
  have hNε1 : 1 ≤ N ^ ε' := Real.one_le_rpow hN1 hε'.le
  have hρ : 0 ≤ ρ := by positivity
  set Bm : ℝ := (4 * 16 ^ 6) * N ^ 8 with hBm
  have hBm0 : 0 ≤ Bm := by positivity
  set Lmax : ℕ := ⌈Bm * N ^ D⌉₊ with hLmax
  have hu1 : ∀ j, j + 1 ≤ K n → gridTime s t K n (j + 1) < 1 := fun j hj =>
    (difRepTail_gridTime_le hst hK hj).trans_lt ht1
  -- the shift budget
  have hesum : (K n : ℝ) * (Δ * (N ^ 2 * (24 * (Δ * (16 * N) ^ 7)))) ≤ δ := by
    have h1 : (K n : ℝ) * (Δ * (N ^ 2 * (24 * (Δ * (16 * N) ^ 7)))) = ((K n : ℝ) * Δ) * ((24 * 16 ^ 7) * N ^ 9 * Δ) := by
      rw [mul_pow]; ring
    rw [h1]
    calc ((K n : ℝ) * Δ) * ((24 * 16 ^ 7) * N ^ 9 * Δ) ≤ 1 * ((24 * 16 ^ 7) * N ^ 9 * Δ) :=
          mul_le_mul_of_nonneg_right hKΔ (by positivity)
      _ = (24 * 16 ^ 7) * N ^ 9 * Δ := one_mul _
      _ ≤ δ := hshift
  -- the threshold sum is at most `2^Lmax δ`
  have hη0 : ∀ j, j ≤ K n → 0 < etaOf (BAmF sz lam0 E n) (gridTime s t K n j) := fun j hj =>
    lt_of_lt_of_le (by positivity) (hη j hj)
  have haL : ∀ ω, ∑ j ∈ Finset.range (K n), TwistGridTail_aSeq sz lam0 E s t K n σ c₁ c₂ b j ω ≤ 2 ^ Lmax * δ := by
    intro ω
    have hterm : ∀ j ∈ Finset.range (K n), TwistGridTail_aSeq sz lam0 E s t K n σ c₁ c₂ b j ω ≤ Δ * Bm := by
      intro j hj
      have hj' : j < K n := Finset.mem_range.1 hj
      have hH := TwistGridTail_Hh_herm sz lam0 n (pathH_isHermitian (sz.withLam 0) s t K n j ω)
      have hcr := TwistGridTail_norm_twEEM sz lam0 E n (hη0 j hj'.le) hH σ b b c₁ c₂
      have hinv : (etaOf (BAmF sz lam0 E n) (gridTime s t K n j))⁻¹ ≤ 16 * N := by
        calc (etaOf (BAmF sz lam0 E n) (gridTime s t K n j))⁻¹ ≤ (1 / (16 * N))⁻¹ :=
              inv_anti₀ (by positivity) (hη j hj'.le)
          _ = 16 * N := by rw [one_div, inv_inv]
      have hηp := hη0 j hj'.le
      have hηi : 0 ≤ (etaOf (BAmF sz lam0 E n) (gridTime s t K n j))⁻¹ := inv_nonneg.2 hηp.le
      have h6 : (etaOf (BAmF sz lam0 E n) (gridTime s t K n j))⁻¹ ^ 3 ≤ (16 * N) ^ 3 := pow_le_pow_left₀ hηi hinv 3
      have h66 : (2 * (etaOf (BAmF sz lam0 E n) (gridTime s t K n j))⁻¹ ^ 3) ^ 2 ≤ (2 * (16 * N) ^ 3) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have hbd : ‖twEEM sz lam0 E n (gridTime s t K n j) ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ b b c₁ c₂‖ ≤ Bm := by
        refine hcr.trans ?_
        calc N ^ 2 * (2 * (etaOf (BAmF sz lam0 E n) (gridTime s t K n j))⁻¹ ^ 3) ^ 2 ≤ N ^ 2 * (2 * (16 * N) ^ 3) ^ 2 :=
              mul_le_mul_of_nonneg_left h66 (by positivity)
          _ = Bm := by rw [hBm]; ring
      unfold TwistGridTail_aSeq twEEk
      exact mul_le_mul_of_nonneg_left hbd hΔ
    calc ∑ j ∈ Finset.range (K n), TwistGridTail_aSeq sz lam0 E s t K n σ c₁ c₂ b j ω ≤ ∑ j ∈ Finset.range (K n), Δ * Bm :=
          Finset.sum_le_sum hterm
      _ = ((K n : ℝ) * Δ) * Bm := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 1 * Bm := mul_le_mul_of_nonneg_right hKΔ hBm0
      _ = Bm := one_mul _
      _ ≤ 2 ^ Lmax * δ := by
          have h1 : Bm * N ^ D ≤ (Lmax : ℝ) := Nat.le_ceil _
          have h2 : (Lmax : ℝ) < 2 ^ Lmax := by exact_mod_cast Nat.lt_two_pow_self
          have h3 : Bm * N ^ D * δ ≤ 2 ^ Lmax * δ := mul_le_mul_of_nonneg_right (h1.trans h2.le) hδ.le
          calc Bm = Bm * (N ^ D * δ) := by rw [hNδ, mul_one]
            _ = Bm * N ^ D * δ := by ring
            _ ≤ 2 ^ Lmax * δ := h3
  -- the `Z` part
  have hZtail := TwistGridTail_Z_tail sz lam0 E s t K n σ c₁ c₂ b hm hmn hst ht1 hK hη Lmax hδ hρ hesum haL
  have hZb : ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * (1 : ℝ)))) ≤ δ / 2 := hZ
  -- the `Y` part
  set P : ℝ := (768 * 36 * 16 ^ 8) * N ^ 18 with hP
  have hxY : 0 < ρ * Real.sqrt δ := by
    have : 0 < ρ := by rw [hρdef]; positivity
    positivity
  have hYtail := TwistGridTail_Y_tail sz lam0 E s t K n σ c₁ c₂ b hm hst ht1 hK hη (P := P) (by rw [hP]; apply le_of_eq; ring) hxY
  have hYb : 4 * ((K n : ℝ) * (Δ ^ 2 * P)) / (ρ * Real.sqrt δ) ^ 2 ≤ δ / 2 := by
    have hx2 : (ρ * Real.sqrt δ) ^ 2 = ρ ^ 2 * δ := by rw [mul_pow, Real.sq_sqrt hδ.le]
    have hρ2 : 1 / 4 ≤ ρ ^ 2 := by rw [hρdef]; nlinarith
    have hP0 : 0 ≤ P := by positivity
    have hY' : 16 * Δ * P ≤ δ / 2 * δ := by
      calc 16 * Δ * P = (16 * Δ * P * N ^ D) * δ := by
            rw [mul_assoc (16 * Δ * P), hNδ, mul_one]
        _ ≤ δ / 2 * δ := mul_le_mul_of_nonneg_right hY hδ.le
    rw [hx2, div_le_iff₀ (by positivity)]
    have h1 : (K n : ℝ) * (Δ ^ 2 * P) ≤ Δ * P := by
      calc (K n : ℝ) * (Δ ^ 2 * P) = ((K n : ℝ) * Δ) * (Δ * P) := by ring
        _ ≤ 1 * (Δ * P) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
        _ = Δ * P := one_mul _
    nlinarith [mul_le_mul_of_nonneg_left hρ2 (by positivity : (0 : ℝ) ≤ δ / 2 * δ)]
  -- the sets
  set EZ : Set (PathΩ (sz.withLam 0)) := {ω | ∃ k, k ≤ K n ∧
    ρ * (∑ j ∈ Finset.range k, TwistGridTail_aSeq sz lam0 E s t K n σ c₁ c₂ b j ω + δ) ^ (1 / 2 : ℝ) <
      ‖∑ j ∈ Finset.range k, TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω‖} with hEZ
  set EY : Set (PathΩ (sz.withLam 0)) := {ω | ∃ k, k ≤ K n ∧
    ρ * Real.sqrt δ ≤ ‖∑ j ∈ Finset.range k, TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω‖} with hEY
  have hgood : ∀ᵐ ω ∂(pathP (sz.withLam 0)), ∀ j, j < K n →
      twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b =
        TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω + TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hj : j < K n
    · filter_upwards [TwistGridTail_martInc_ae sz lam0 E s t K n σ c₁ c₂ b j hm (hu1 j hj)] with ω h _ using h
    · exact Filter.Eventually.of_forall fun ω h => absurd h hj
  have hnull : (pathP (sz.withLam 0)) {ω | ¬ ∀ j, j < K n →
      twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b =
        TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω + TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω} = 0 :=
    ae_iff.1 hgood
  have hincl : {ω | ∃ k, k ≤ K n ∧
      N ^ ε' * (∑ j ∈ Finset.range k, Δ * ‖twEEk sz lam0 E s t K n σ b c₁ c₂ j ω‖ + N ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖twMart sz lam0 E s t K n σ b c₁ c₂ k ω‖} ⊆
      (EZ ∪ EY) ∪ {ω | ¬ ∀ j, j < K n →
        twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b =
          TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω + TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω} := by
    intro ω hω
    by_cases hg : ∀ j, j < K n → twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b =
        TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω + TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω
    · left
      obtain ⟨k, hk, hlt⟩ := hω
      have hMart : twMart sz lam0 E s t K n σ b c₁ c₂ k ω =
          ∑ j ∈ Finset.range k, TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω +
            ∑ j ∈ Finset.range k, TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω := by
        unfold twMart
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j hj => hg j (lt_of_lt_of_le (Finset.mem_range.1 hj) hk)
      have hA0 : 0 ≤ ∑ j ∈ Finset.range k, TwistGridTail_aSeq sz lam0 E s t K n σ c₁ c₂ b j ω :=
        Finset.sum_nonneg fun j _ => mul_nonneg hΔ (norm_nonneg _)
      set T : ℝ := (∑ j ∈ Finset.range k, TwistGridTail_aSeq sz lam0 E s t K n σ c₁ c₂ b j ω + δ) ^ (1 / 2 : ℝ) with hT
      have hlt' : N ^ ε' * T < ‖twMart sz lam0 E s t K n σ b c₁ c₂ k ω‖ := hlt
      have hTδ : Real.sqrt δ ≤ T := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow hδ.le (by linarith) (by norm_num)
      have hρ2 : N ^ ε' = 2 * ρ := by rw [hρdef]; ring
      by_cases hZ' : ρ * T < ‖∑ j ∈ Finset.range k, TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω‖
      · exact Or.inl ⟨k, hk, hZ'⟩
      · right
        refine ⟨k, hk, ?_⟩
        have h1 : N ^ ε' * T < ‖∑ j ∈ Finset.range k, TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω‖ +
            ‖∑ j ∈ Finset.range k, TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω‖ := by
          refine hlt'.trans_le ?_
          rw [hMart]
          exact norm_add_le _ _
        have h2 : ρ * T < ‖∑ j ∈ Finset.range k, TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω‖ := by
          rw [hρ2] at h1
          push Not at hZ'
          linarith
        calc ρ * Real.sqrt δ ≤ ρ * T := mul_le_mul_of_nonneg_left hTδ hρ
          _ ≤ _ := h2.le
    · exact Or.inr hg
  have hEZm : pathP (sz.withLam 0) EZ ≤ ENNReal.ofReal (δ / 2) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hZtail.trans hZb)
  have hEYm : pathP (sz.withLam 0) EY ≤ ENNReal.ofReal (δ / 2) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hYtail.trans hYb)
  calc (pathP (sz.withLam 0)) {ω | ∃ k, k ≤ K n ∧
      N ^ ε' * (∑ j ∈ Finset.range k, Δ * ‖twEEk sz lam0 E s t K n σ b c₁ c₂ j ω‖ + N ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖twMart sz lam0 E s t K n σ b c₁ c₂ k ω‖}
      ≤ (pathP (sz.withLam 0)) ((EZ ∪ EY) ∪ {ω | ¬ ∀ j, j < K n →
        twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b =
          TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω + TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω}) := measure_mono hincl
    _ ≤ (pathP (sz.withLam 0)) (EZ ∪ EY) + (pathP (sz.withLam 0)) {ω | ¬ ∀ j, j < K n →
        twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b =
          TwistGridTail_Zv sz lam0 E s t K n σ c₁ c₂ b j ω + TwistGridTail_Yv sz lam0 E s t K n σ c₁ c₂ b j ω} := measure_union_le _ _
    _ ≤ ((pathP (sz.withLam 0)) EZ + (pathP (sz.withLam 0)) EY) + 0 := by
        rw [hnull]
        exact add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2)) + 0 := add_le_add (add_le_add hEZm hEYm) le_rfl
    _ = ENNReal.ofReal δ := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Core

/-! ## 2. The asymptotics of the `Z` budget -/

section Asymptotics

/-- **The `Z` budget holds for large `N`**: `(⌈c N^8 N^D⌉ + 1) · 4 e^{-(N^{ε'}/2)²/16} ≤ N^{-D}/2` eventually, `c = 4 · 16⁶`
(the polynomial number of levels is beaten by the stretched exponential; twin of `difRepTail_eventually_Z`). -/
private theorem TwistGridTail2_eventually_Z (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε') :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧
      ((⌈(4 * 16 ^ 6) * N ^ 8 * N ^ D⌉₊ : ℝ) + 1) * (4 * Real.exp (-(N ^ ε' / 2) ^ 2 / (16 * (1 : ℝ)))) ≤ N ^ (-D) / 2 := by
  set c₃ : ℝ := 4 * 16 ^ 6 with hc₃
  set q : ℝ := 8 + D with hq
  set c₄ : ℝ := 8 * (c₃ + 2) with hc₄
  have hc₃0 : 0 < c₃ := by positivity
  have hc₄0 : 0 < c₄ := by positivity
  have hlim := difRepTail_tendsto_rpow_exp (q + D) (1 / 64) (2 * ε') (by positivity) (by positivity)
  have hev := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / c₄))
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  refine ⟨hN1, ?_⟩
  have hN0 : 0 < N := by linarith
  have hND : 0 < N ^ D := Real.rpow_pos_of_pos hN0 _
  set x : ℝ := c₃ * N ^ 8 * N ^ D with hx
  have hx0 : 0 ≤ x := by positivity
  have hceil : (⌈x⌉₊ : ℝ) + 1 ≤ x + 2 := by
    have := Nat.ceil_lt_add_one hx0
    linarith
  have hxq : x = c₃ * N ^ q := by
    rw [hx, hq, Real.rpow_add hN0, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hNq1 : 1 ≤ N ^ q := Real.one_le_rpow hN1 (by positivity)
  have hexp : -(N ^ ε' / 2) ^ 2 / (16 * (1 : ℝ)) = -(1 / 64) * N ^ (2 * ε') := by
    have : (N ^ ε') ^ 2 = N ^ (2 * ε') := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    rw [div_pow, this]
    ring
  rw [hexp]
  set Ee : ℝ := Real.exp (-(1 / 64) * N ^ (2 * ε')) with hEe
  have hE0 : 0 < Ee := Real.exp_pos _
  have hG : N ^ (q + D) * Ee < 1 / c₄ := hN
  have hNqD : N ^ (q + D) = N ^ q * N ^ D := Real.rpow_add hN0 _ _
  have hkey : (x + 2) * (4 * Ee) * (2 * N ^ D) ≤ 1 := by
    have h1 : x + 2 ≤ (c₃ + 2) * N ^ q := by rw [hxq]; nlinarith
    calc (x + 2) * (4 * Ee) * (2 * N ^ D) = 8 * (x + 2) * (N ^ D * Ee) := by ring
      _ ≤ 8 * ((c₃ + 2) * N ^ q) * (N ^ D * Ee) := by gcongr
      _ = c₄ * (N ^ (q + D) * Ee) := by rw [hNqD, hc₄]; ring
      _ ≤ c₄ * (1 / c₄) := by gcongr
      _ = 1 := by field_simp
  have hnegD : N ^ (-D) = (N ^ D)⁻¹ := Real.rpow_neg hN0.le D
  rw [hnegD]
  refine (mul_le_mul_of_nonneg_right hceil (by positivity)).trans ?_
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← one_div, le_div_iff₀ hND] at *
  nlinarith [hkey]

end Asymptotics

/-! ## 3. Target 1: `baTwistGridTail_holds` -/

section Main

/-- **Target 1, `baTwistGridTail_holds`**: the owed martingale tail of `twMart` with the quadratic variation `twEEk` (clause (iii) of 4 (b)), for
every `d` (no `3 ≤ d`: the pin and the band's `gridRepTailN_holds` carry none).  The grid exponent is `CK = 2 D + 20` (it depends on `D` only).
Route (T2180 step 3, `DifREP2` §7-§12): `Mart_k = S^Z_k + S^Y_k` (`stepDecompCN` of the twisted family); the `Z` part by the peeling lemma
`difRep2_peel` (the random predictable proxy `Δ Re twEEM_{u_{j+1}}(b,b)` of `TwistGridTail_condMGF_Z`, moved to `u_j` at the cost
`24 N⁹ Δ` of the shift bound), with `ρ = N^{ε'}/2`; the `Y` part by Doob's `L²` maximal inequality.  The budgets are `24 · 16⁷ ≤ N` (shift),
`32 · 768 · 36 · 16⁸ ≤ N²` (`Y`) and `(L + 1) · 4 e^{-N^{2ε'}/64} ≤ N^{-D}/2` with `L` polynomial in `N` (`Z`). -/
theorem baTwistGridTail_holds (d : ℕ) : BATwistGridTail d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨2 * D + 20, by positivity, ?_⟩
  intro K hK0 hKN ε' hε'
  have hsize : sz.SizeTendsto := hz.1.2.2.1
  have hmF : ∀ n, κ ≤ (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := fun n => (EMn2BA_mF_data sz hz n).1
  have hm : ∀ n, 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := fun n => lt_of_lt_of_le hκ (hmF n)
  have hmn : ∀ n, ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 := fun n =>
    BAm_norm_le_one d (sz.L n) _ ((BAflowEs sz z n : ℝ) : ℂ) _ (by simp) (BAflow_real κ ε 𝔠 𝔡 sz z hz n).1
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (EMn2BA_T0_lt_one hκ sz hz n)
  have hbigε := ((tendsto_rpow_atTop hε).comp hsize).eventually (eventually_ge_atTop (8 * κ)⁻¹)
  have hbig := hsize.eventually (eventually_ge_atTop (max (24 * 16 ^ 7) (32 * (768 * 36 * 16 ^ 8))))
  have hZev := hsize.eventually (TwistGridTail2_eventually_Z D ε' hD hε')
  filter_upwards [hKN, hbigε, hbig, hZev] with n hKNn hbigεn hbign hZn
  intro i
  obtain ⟨hN1, hZn⟩ := hZn
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n (hst n)
  have hKΔ : (K n : ℝ) * Δ ≤ 1 := by
    rw [hΔdef, difRepTail_K_mul_step s t K n (hK0 n)]; linarith [hs n, ht1 n]
  have hΔN : Δ * N ^ (2 * D + 20) ≤ 1 := by
    calc Δ * N ^ (2 * D + 20) ≤ Δ * (K n : ℝ) := mul_le_mul_of_nonneg_left hKNn hΔ
      _ = (K n : ℝ) * Δ := mul_comm _ _
      _ ≤ 1 := hKΔ
  have hΔle : Δ ≤ N ^ (-(2 * D + 20)) := by
    rw [Real.rpow_neg hN0.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hN0 _)]
    exact hΔN
  have hcE : 24 * 16 ^ 7 ≤ N := (le_max_left _ _).trans hbign
  have hcP : 32 * (768 * 36 * 16 ^ 8) ≤ N := (le_max_right _ _).trans hbign
  have hcPN : 32 * (768 * 36 * 16 ^ 8) ≤ N ^ 2 := by nlinarith
  -- the spectral height along the grid
  have hη : ∀ j, j ≤ K n → 1 / (16 * N) ≤ etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (gridTime s t K n j) := by
    intro j hj
    have hu : gridTime s t K n j ≤ BAflowT0 sz z n :=
      (difRepTail_gridTime_le (hst n) (hK0 n) hj).trans (htT n)
    have h1 := EMn2BA_one_sub_T0 hκ sz hz n
    have h2 : N ^ (-1 + ε) ≤ (z n).im := (hz.2 n).2.1
    have h3 : N ^ (-1 + ε) = N ^ ε * N⁻¹ := by
      rw [Real.rpow_add hN0, Real.rpow_neg_one, mul_comm]
    have h4 : (z n).im / 2 * κ ≤ etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (gridTime s t K n j) := by
      unfold etaOf
      have h5 : (z n).im / 2 ≤ 1 - gridTime s t K n j := by linarith
      have hzim : 0 < (z n).im := EMn2BA_zim_pos sz hz n
      exact mul_le_mul h5 (hmF n) hκ.le (by linarith)
    refine le_trans ?_ h4
    have h6 : N ^ ε * N⁻¹ * κ / 2 ≤ (z n).im / 2 * κ := by
      rw [← h3]
      nlinarith [mul_le_mul_of_nonneg_right h2 hκ.le]
    refine le_trans ?_ h6
    have h7 : (8 * κ)⁻¹ ≤ N ^ ε := hbigεn
    have h8 : 1 / (16 * N) = (8 * κ)⁻¹ * N⁻¹ * κ / 2 := by
      field_simp
      ring
    rw [h8]
    gcongr
  -- the shift budget
  have hshift : (24 * 16 ^ 7) * N ^ 9 * Δ ≤ N ^ (-D) := by
    have h1 : N ^ 9 * N ^ (-(2 * D + 20)) = N ^ (-(2 * D) - 11) := by
      rw [← Real.rpow_natCast N 9, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hcE' : (24 * 16 ^ 7 : ℝ) ≤ N ^ (D + 11) := by
      calc (24 * 16 ^ 7 : ℝ) ≤ N := hcE
        _ = N ^ (1 : ℝ) := (Real.rpow_one N).symm
        _ ≤ N ^ (D + 11) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc (24 * 16 ^ 7) * N ^ 9 * Δ ≤ (24 * 16 ^ 7) * N ^ 9 * N ^ (-(2 * D + 20)) := by gcongr
      _ = (24 * 16 ^ 7) * N ^ (-(2 * D) - 11) := by rw [mul_assoc, h1]
      _ ≤ N ^ (D + 11) * N ^ (-(2 * D) - 11) := by gcongr
      _ = N ^ (-D) := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
  -- the `Y` budget
  have hY : 16 * Δ * ((768 * 36 * 16 ^ 8) * N ^ 18) * N ^ D ≤ N ^ (-D) / 2 := by
    have h1 : N ^ 18 * N ^ D * N ^ (-(2 * D + 20)) = N ^ (-D - 2) := by
      rw [← Real.rpow_natCast N 18, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hcP0 : (0 : ℝ) ≤ 768 * 36 * 16 ^ 8 := by positivity
    have h2 : N ^ (-D) = N ^ (-D - 2) * N ^ 2 := by
      rw [← Real.rpow_natCast N 2, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hND2 : 0 < N ^ (-D - 2) := Real.rpow_pos_of_pos hN0 _
    calc 16 * Δ * ((768 * 36 * 16 ^ 8) * N ^ 18) * N ^ D
        = 16 * (768 * 36 * 16 ^ 8) * Δ * (N ^ 18 * N ^ D) := by ring
      _ ≤ 16 * (768 * 36 * 16 ^ 8) * N ^ (-(2 * D + 20)) * (N ^ 18 * N ^ D) := by gcongr
      _ = 16 * (768 * 36 * 16 ^ 8) * (N ^ 18 * N ^ D * N ^ (-(2 * D + 20))) := by ring
      _ = 16 * (768 * 36 * 16 ^ 8) * N ^ (-D - 2) := by rw [h1]
      _ ≤ N ^ (-D) / 2 := by
          rw [h2]
          nlinarith [mul_le_mul_of_nonneg_left hcPN hND2.le]
  exact TwistGridTail2_core sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n (hm n) (hmn n) (hs n) (hst n) (ht1 n) (hK0 n) D ε' hD hε'
    hη hshift hY hZn i.1 i.2.2.1 i.2.2.2 i.2.1

end Main

/-! ## 4. Compiled nonempty instances (`d = 3`, `sz0`: `L = 4(n+1)`, `W = (2(n+1))⁵`; flow `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `z = zSeq`;
the window `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` by `t0_sz0`; `D = 1`, `ε' = 1/10`, the grid `K_n = ⌈N_n^{CK}⌉ + 1`).  Every deterministic hypothesis of
`baTwistGridTail_holds` is discharged; the part pins of 4 (b) other than `BATwistGridTail` (T2437, T2439) stay hypotheses of the last example. -/

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.EKPinsInst

/-- The instance grid `K_n = ⌈N_n^{CK}⌉ + 1` (never `0`, eventually `≥ N_n^{CK}`). -/
private def TwistGridTail2_Kinst (CK : ℝ) (n : ℕ) : ℕ := ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1

/-- `baTwistGridTail_holds` at `d = 3`, the BA datum `(sz0, zSeq, flow_sz0)`, the window `s ≡ 1/2`, `t ≡ 2/3`, `D = 1`, the grid `K_n = ⌈N_n^{CK}⌉ + 1` and
`ε' = 1/10`: for `CK` of the theorem, eventually in `n`, for every label `(σ, a, c₁, c₂)` the martingale `twMart` stays below
`N^{ε'} (Σ_{j<k} Δ ‖twEEk_j‖ + N^{-1})^{1/2}` up to probability `N^{-1}`. -/
example : ∃ CK : ℝ, 0 ≤ CK ∧ ∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × Zd 3 (sz0.L n) × Zd 3 (sz0.L n) × Zd 3 (sz0.L n),
    ((baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).Pp) {ω | ∃ k, k ≤ TwistGridTail2_Kinst CK n ∧
      ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * (∑ j ∈ Finset.range k, gridStep (fun _ => 1 / 2) (fun _ => 2 / 3) (TwistGridTail2_Kinst CK) n *
        ‖twEEk sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (TwistGridTail2_Kinst CK) n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω‖ +
          ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) <
      ‖twMart sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (TwistGridTail2_Kinst CK) n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖} ≤
      ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨CK, hCK, H⟩ := baTwistGridTail_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) 1 one_pos
  exact ⟨CK, hCK, H (TwistGridTail2_Kinst CK) (fun n => Nat.succ_ne_zero _)
    (Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)) (1 / 10) (by norm_num)⟩

/-- `baTwistGridTail_holds` for every `d`, as a plain `example`. -/
example : ∀ d, BATwistGridTail d := baTwistGridTail_holds

/-- The pin `BATwistGridTail 3` assembled with the other two parts (T2437, T2439: hypotheses) into 4 (b) at `C₀ = 11` (`baTwistGridAssemble_holds`). -/
example (hRem : BATwistGridRem 3 11) (hW : BATwistGridWTail 3) : BATwistGridMartAt 3 11 :=
  baTwistGridAssemble_holds 3 11 (by norm_num) hRem (baTwistGridTail_holds 3) hW

/-- The assembled pin applied at the BA datum `(sz0, zSeq, flow_sz0)`, any `D > 0`, the grid `K_n = ⌈N_n^{CK}⌉ + 1`, with `BATwistGridTail 3` proved here. -/
example (hRem : BATwistGridRem 3 11) (hW : BATwistGridWTail 3) {D : ℝ} (hD : 0 < D) : True := by
  have H := baTwistGridAssemble_holds 3 11 (by norm_num) hRem (baTwistGridTail_holds 3) hW
  obtain ⟨CK, hCK, H2⟩ := H (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) D hD
  have := H2 (TwistGridTail2_Kinst CK) (fun n => Nat.succ_ne_zero _)
    (Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _))
  trivial

end Inst

end RBM.BA
