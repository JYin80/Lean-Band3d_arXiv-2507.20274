/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpEtermsA
import RBM3D.Chain.KDecayGen
import RBM3D.Chain.CltFarUGen

/-!
# (6.3) `eq:Exp(L-K)1` over the carrier

Restatement of `Induction/ExpEtermsA` over a carrier `C : FlowFM sz` and a law `μ`, on the vocabulary of
`Chain/Step6Gen`.  Paper: (6.3) `eq:Exp(L-K)1`:
`𝔼ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}`, uniformly in `u ∈ [s,t]`.

* **The kit at `(C, μ)`**: `expLK_window_leg` (the window sum on the kernel `C.S`, column sums `≤ 1`),
  `expLK_envg` and `expLK_env_polyg` (the polynomial envelope `≤ N⁶` of `ℰ^{LK×LK}` along the flow:
  `‖C.L^{(2)}‖ ≤ η⁻²` from the representation `CltRepg`, `‖C.K^{(2)}‖ ≤ N B` from
  `stKbound_timeIccgL` at `τ = 1`, `η⁻¹ ≤ N`, `(1-u)⁻¹ ≤ N` from `κ' ≤ Im m` and `N^{-1+δ} ≤ 1 - T0`),
  `expLK_precg` (`≺ (1-u)⁻¹ B^{11/5}` from `STLKUgL` at `k = 2` and `STGdecayWgL … 0`), `expLK_expectg`
  (`≺ → 𝔼`).  The size-level lemma `expLK_latticeSum` (`KDecay_sum_tailT_le`) is reused by name.
* **The statement**: `STExpLKLKHiConclgL_of_LKU` (per carrier) and `stExpLKLKHigL_of` (the statement
  `STExpLKLKHigL` of `Chain/Step6Gen`, per family).

The family hypotheses of the wrappers are written inline.  Helpers shared with `Chain/ExpEtermsBGen` are
public and carry the prefix of this file's name.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private expLK_Bctl_ge expLK_first_moment from RBM3D.Induction.ExpEtermsA

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Deterministic steps -/

section Kit

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- **The window sum on the carrier kernel** (band `expLK_window_le`): `‖ℰ^{LK×LK}‖ ≤ W^d M Σ_y f(y)` if the first factor is at most `M` and the
second at most the profile `f(y)`, given the column sums `Σ_x |S_{xy}| ≤ 1` of `C.S` (the band has `= 1`). -/
theorem expLK_window_leg (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (M : ℝ)
    (f : Zd d (sz.L n) → ℝ) (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (hM : ∀ x, ‖C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]‖ ≤ M)
    (hf : ∀ y, ‖C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y]‖ ≤ f y) :
    ‖STELKLKg C n u σ a ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * M * ∑ y : Zd d (sz.L n), f y := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hf0 : ∀ y, 0 ≤ f y := fun y => (norm_nonneg _).trans (hf y)
  have key : ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      (C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]) * C.S n x y *
        (C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y])‖ ≤ M * ∑ y, f y := by
    calc _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          ‖(C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]) * C.S n x y *
            (C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y])‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_le _ _)
      _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), M * (‖C.S n x y‖ * f y) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => by
            rw [norm_mul, norm_mul]
            calc ‖C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]‖ * ‖C.S n x y‖ *
                  ‖C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y]‖
                = ‖C.S n x y‖ * (‖C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]‖ *
                  ‖C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y]‖) := by ring
              _ ≤ ‖C.S n x y‖ * (M * f y) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul (hM x) (hf y) (norm_nonneg _) hM0) (norm_nonneg _)
              _ = M * (‖C.S n x y‖ * f y) := by ring
      _ ≤ M * ∑ y, f y := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_le_sum fun y _ => ?_
          have h1 : ∑ x : Zd d (sz.L n), M * (‖C.S n x y‖ * f y) = M * f y * ∑ x : Zd d (sz.L n), ‖C.S n x y‖ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
          rw [h1]
          calc M * f y * ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ M * f y * 1 :=
                mul_le_mul_of_nonneg_left (hcol y) (mul_nonneg hM0 (hf0 y))
            _ = M * f y := mul_one _
  unfold STELKLKg
  rw [norm_mul, norm_pow, Complex.norm_natCast, mul_assoc]
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-- **The envelope** (band `expLK_env`): `|ℰ^{LK×LK}| ≤ W^d L^d (c_L + c_K)²` for every sample if `‖𝓛^{(2)}‖ ≤ c_L` and `‖𝒦^{(2)}‖ ≤ c_K`
(the window sum with `M = f = c_L + c_K` and `Σ_y 1 = L^d`). -/
theorem expLK_envg (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (cL cK : ℝ)
    (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (hL : ∀ b : Fin 2 → Zd d (sz.L n), ‖C.L n u σ b ω‖ ≤ cL) (hK : ∀ b : Fin 2 → Zd d (sz.L n), ‖C.K n u σ b‖ ≤ cK) :
    ‖STELKLKg C n u σ a ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * (cL + cK) ^ 2 := by
  have hbd : ∀ b : Fin 2 → Zd d (sz.L n), ‖C.L n u σ b ω - C.K n u σ b‖ ≤ cL + cK := fun b =>
    (norm_sub_le _ _).trans (add_le_add (hL b) (hK b))
  have h := expLK_window_leg C n u ω σ a (cL + cK) (fun _ => cL + cK) hcol (fun x => hbd _) (fun y => hbd _)
  have hsum : ∑ _y : Zd d (sz.L n), (cL + cK) = ((sz.L n : ℕ) : ℝ) ^ d * (cL + cK) := by
    rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    push_cast; ring
  rw [hsum] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end Kit

/-! ## 2. The bounds along the flow and the loop envelope -/

/-- `B_{u,0} ≤ 2 (1-u)⁻¹` for `u < 1` (copy of the private `expDr_Bctl_le_two`; shared with `Chain/ExpEtermsBGen`). -/
theorem ExpEtermsAGen_Bctl_le_two {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) :
    sz.Bctl n u ≤ 2 * (1 - u)⁻¹ := by
  have h1 : 0 < 1 - u := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLd : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
  have hWd : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
  have hA : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1 (by nlinarith [sq_nonneg (sz.lam n)])
  have hB : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1 (by nlinarith)
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos h1]
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [hz, inv_one, mul_one]
  have hWi : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWd
  have hnn : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ 1 * ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) :=
        mul_le_mul_of_nonneg_right hWi hnn
    _ ≤ (1 - u)⁻¹ + (1 - u)⁻¹ := by rw [one_mul]; exact add_le_add hA hB
    _ = 2 * (1 - u)⁻¹ := by ring

/-- **The bounds along the flow** (band `expLK_eta_inv_le` and `expDr_ctrl`; the band reads `1 - u ≥ 1 - lemT z ≥ N^{-1+ε}/4` and
`Im m ≥ √(2κ)/2`, here the family data supply `κ' ≤ Im m` and `N^{-1+δ} ≤ 1 - T0`): eventually in `n`, `N ≥ 20` and for every `u ≤ t_n ≤ T_n`,
`0 < 1 - u`, `η_u⁻¹ ≤ N` (`η_u = (1-u) Im m`, `etaOf`) and `(1-u)⁻¹ ≤ N`. -/
theorem ExpEtermsAGen_ctrl {d : ℕ} {sz : Sizes d} (hsz : sz.SizeTendsto) {m : ℕ → ℂ} {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ)
    (hm : ∀ n, κ' ≤ (m n).im) {t T : ℕ → ℝ} (htT : ∀ n, t n ≤ T n)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) :
    ∀ᶠ n in atTop, 20 ≤ ((sz.size n : ℕ) : ℝ) ∧ ∀ u : ℝ, u ≤ t n →
      0 < 1 - u ∧ (etaOf (m n) u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hNδ : ∀ᶠ n in atTop, κ'⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp hsz).eventually (eventually_ge_atTop κ'⁻¹)
  filter_upwards [hrange, hsz.eventually (eventually_ge_atTop 20), hNδ] with n hr hN hNd
  refine ⟨hN, fun u hu => ?_⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hp : 0 < N ^ (-1 + δ) := Real.rpow_pos_of_pos hNpos _
  have h1u : N ^ (-1 + δ) ≤ 1 - u := hr.trans (by linarith [htT n])
  have h0 : 0 < 1 - u := hp.trans_le h1u
  have hinv : (1 - u)⁻¹ ≤ N ^ (1 - δ) := by
    refine (inv_anti₀ hp h1u).trans (le_of_eq ?_)
    rw [show (-1 + δ : ℝ) = -(1 - δ) by ring, Real.rpow_neg hNpos.le, inv_inv]
  have hN1δ : N ^ (1 - δ) ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - δ ≤ (1 : ℝ) by linarith)
    rwa [Real.rpow_one] at this
  refine ⟨h0, ?_, hinv.trans hN1δ⟩
  have hηpos : 0 < κ' * (1 - u) := mul_pos hκ' h0
  have hη : κ' * (1 - u) ≤ etaOf (m n) u := by
    unfold etaOf
    nlinarith [hm n]
  calc (etaOf (m n) u)⁻¹ ≤ (κ' * (1 - u))⁻¹ := inv_anti₀ hηpos hη
    _ = κ'⁻¹ * (1 - u)⁻¹ := mul_inv _ _
    _ ≤ N ^ δ * N ^ (1 - δ) := mul_le_mul hNd hinv (inv_nonneg.2 h0.le) (Real.rpow_nonneg hNpos.le _)
    _ = N := by rw [← Real.rpow_add hNpos]; simp

/-- **The loop envelope on the carrier** (band `norm_Lloop_le`): under the representation `CltRepg` (the loops of the Hermitian matrix `H₀ n + H_u`
at `z = ztOf (C.m n) (E n) u`) and `0 < Im m`, `|𝓛^{(k+1)}_{u,σ,a}| ≤ (η_u⁻¹)^{k+1}` for every sample (`norm_loopM_le`). -/
theorem ExpEtermsAGen_norm_L_le {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {μ : Measure sz.SeqΩ}
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hu : u < 1) (him : 0 < (C.m n).im) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖C.L n u σ a ω‖ ≤ (etaOf (C.m n) u)⁻¹ ^ (k + 1) := by
  obtain ⟨-, hH₀, hr⟩ := hrep
  rw [(hr n u ω).2 (k + 1) σ a]
  have hη : 0 < etaOf (C.m n) u := mul_pos (by linarith) him
  have hH : (blockMat d (sz.L n) (sz.W n)
      (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam g') n u ω i j)).IsHermitian :=
    ((hH₀ n).add (Sizes.seqHflow_isHermitian (sz.withLam g') n u ω)).submatrix _
  unfold loopFine
  exact norm_loopM_le d (sz.L n) (sz.W n) hH hη (by rw [ztOf_im, abs_of_pos hη]) σ a

section Flow

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- **The envelope is polynomial** along the flow, uniformly in `u ∈ [s_n,t_n]`, `σ`, `a`, `ω` (band `expLK_env_poly`): `ℰ^{LK×LK} ≤ N⁶`
eventually.  `‖𝓛^{(2)}‖ ≤ η_u⁻² ≤ N²` (`ExpEtermsAGen_norm_L_le`, `ExpEtermsAGen_ctrl`), `‖𝒦^{(2)}‖ ≤ N B ≤ 2N²` (`stKbound_timeIccgL` at `τ = 1`, a deterministic `≺`
through `st6_prec_det_iffg`, `B ≤ 2(1-u)⁻¹ ≤ 2N`), `N (N² + 2N²)² = 9 N⁵ ≤ N⁶` for `N ≥ 9`. -/
theorem expLK_env_polyg (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im)
    {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ)
    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) :
    ∀ᶠ n in atTop, ∀ (p : STIdx2 sz s t n) (ω : sz.SeqΩ),
      ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) := by
  have := hμ
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT1 n)
  have hK := (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p => (sz.Bctl n (p.1 : ℝ)) ^ (2 - 1))).1
    (stKbound_timeIccgL sz C μ hsz hKb s t hs0 hst ht1 2 (by norm_num)) 1 one_pos
  filter_upwards [ExpEtermsAGen_ctrl hsz hκ' hδ hm htT hrange, hK] with n ⟨hN20, hc⟩ hKn
  rintro ⟨⟨u, hu⟩, σ, a⟩ ω
  obtain ⟨h0, hη, hy⟩ := hc u hu.2
  have hu1 : u < 1 := by linarith
  have hm0 : 0 < (C.m n).im := hκ'.trans_le (hm n)
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hB : sz.Bctl n u ≤ 2 * N := by
    have := ExpEtermsAGen_Bctl_le_two sz n hu1
    linarith
  have hB0 : 0 ≤ sz.Bctl n u := (STBctl_pos sz n hu1).le
  have hη0 : 0 ≤ (etaOf (C.m n) u)⁻¹ := inv_nonneg.2 (mul_pos h0 hm0).le
  have hL : ∀ b : Fin 2 → Zd d (sz.L n), ‖C.L n u σ b ω‖ ≤ N ^ 2 := fun b =>
    (ExpEtermsAGen_norm_L_le hrep n hu1 hm0 (k := 1) σ b ω).trans (pow_le_pow_left₀ hη0 hη 2)
  have hKk : ∀ b : Fin 2 → Zd d (sz.L n), ‖C.K n u σ b‖ ≤ 2 * N ^ 2 := by
    intro b
    have h := hKn (⟨u, hu⟩, σ, b)
    simp only [Nat.reduceSub, pow_one, Real.rpow_one] at h
    refine h.trans ?_
    calc N * sz.Bctl n u ≤ N * (2 * N) := mul_le_mul_of_nonneg_left hB hN0.le
      _ = 2 * N ^ 2 := by ring
  have h := expLK_envg C n u ω σ a (N ^ 2) (2 * N ^ 2) (hcol n) hL hKk
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = N := by
    rw [hNdef]; simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  rw [hWL] at h
  have h6 : N ^ (6 : ℝ) = N ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h6]
  refine h.trans ?_
  have h5 : 0 ≤ N ^ 5 := by positivity
  calc N * (N ^ 2 + 2 * N ^ 2) ^ 2 = 9 * N ^ 5 := by ring
    _ ≤ N ^ 6 := by nlinarith

/-! ## 3. The decay step: `ℰ^{LK×LK} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}` -/

/-- The deterministic core of `expLK_precg` (band `expLK_det_core`, on the carrier kernel): outside the failure events,
`|ℰ| ≤ N^{2τ'} (C_∞(d) + 1) (1-u)⁻¹ B^{11/5}` (window sum, lattice sum, `W^{-D} ≤ N^{-2}`, `B ≥ N⁻¹`: the zero-mode part `N B² W^{-D} ≤ B^{11/5}`). -/
private theorem ExpEtermsAGen_det_core (hd : 2 ≤ d) (n : ℕ) {u τ' D : ℝ} (ω : sz.SeqΩ)
    (hlam : 0 ≤ sz.lam n) (hu0 : 0 ≤ u) (hu1 : u < 1) (hN : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (hWD : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ))
    (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (h1 : ∀ x : Zd d (sz.L n), ‖C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n u ^ 2)
    (h2 : ∀ y : Zd d (sz.L n), ‖C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' *
        (sz.Bctl n u ^ (1 / 5 : ℝ) * sz.STWB n u (zdistInf d (sz.L n) (a 0 - y)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D))) :
    ‖STELKLKg C n u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * ((sz.size n : ℕ) : ℝ) ^ τ' *
      (KDecay_tailC d + 1) * ((1 - u)⁻¹ * sz.Bctl n u ^ (11 / 5 : ℝ)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set X : ℝ := N ^ τ' with hX
  set B : ℝ := sz.Bctl n u with hB
  set Wd : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hWd
  set Ld : ℝ := ((sz.L n : ℕ) : ℝ) ^ d with hLd
  set P : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-D) with hP
  set Bq : ℝ := B ^ (1 / 5 : ℝ) with hBq
  set g : Zd d (sz.L n) → ℝ := fun y => sz.STWB n u (zdistInf d (sz.L n) (a 0 - y)) *
    Real.exp (-(((zdistInf d (sz.L n) (a 0 - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) with hg
  have hBpos : 0 < B := STBctl_pos sz n hu1
  have hBN : N⁻¹ ≤ B := expLK_Bctl_ge sz n hu0 hu1
  have hNpos : 0 < N := by linarith
  have hWL : Wd * Ld = N := by
    rw [hNdef, hWd, hLd]; simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hf : ∀ y, ‖C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y]‖ ≤ X * (Bq * g y + P) := by
    intro y
    refine (h2 y).trans (le_of_eq ?_)
    simp only [hg, mul_assoc]
  have hwin := expLK_window_leg C n u ω σ a (X * B ^ 2) (fun y => X * (Bq * g y + P)) hcol h1 hf
  have hsumf : ∑ y : Zd d (sz.L n), X * (Bq * g y + P) = X * (Bq * (∑ y, g y) + Ld * P) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      card_Zd, nsmul_eq_mul]
    push_cast; rw [hLd]
  rw [hsumf] at hwin
  have hlat : Wd * ∑ y, g y ≤ KDecay_tailC d / (1 - u) := expLK_latticeSum sz hd n hlam hu1 (a 0)
  have hB2 : B ^ 2 * Bq = B ^ (11 / 5 : ℝ) := by
    rw [hBq, ← Real.rpow_natCast B 2, ← Real.rpow_add hBpos]; norm_num
  have hmain : Wd * (X * B ^ 2) * (X * (Bq * (∑ y, g y) + Ld * P)) =
      X * X * (B ^ 2 * Bq * (Wd * ∑ y, g y) + B ^ 2 * (Wd * Ld) * P) := by ring
  rw [hWL, hB2] at hmain
  -- the zero-mode part
  have hNinv : N⁻¹ ≤ Bq := by
    have h0 : 0 < N⁻¹ := inv_pos.2 hNpos
    have h1' : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
    have ha : N⁻¹ ^ (1 : ℝ) ≤ N⁻¹ ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h0 h1' (by norm_num)
    rw [Real.rpow_one] at ha
    exact ha.trans (Real.rpow_le_rpow h0.le hBN (by norm_num))
  have hPN : N * P ≤ N⁻¹ := by
    have h2' : P ≤ (N ^ 2)⁻¹ := by
      refine hWD.trans (le_of_eq ?_)
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hNpos.le, Real.rpow_natCast]
    calc N * P ≤ N * (N ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2' hNpos.le
      _ = N⁻¹ := by field_simp
  have hzero : B ^ 2 * N * P ≤ B ^ (11 / 5 : ℝ) := by
    calc B ^ 2 * N * P = B ^ 2 * (N * P) := by ring
      _ ≤ B ^ 2 * N⁻¹ := mul_le_mul_of_nonneg_left hPN (by positivity)
      _ ≤ B ^ 2 * Bq := mul_le_mul_of_nonneg_left hNinv (by positivity)
      _ = B ^ (11 / 5 : ℝ) := hB2
  have hB115 : 0 ≤ B ^ (11 / 5 : ℝ) := Real.rpow_nonneg hBpos.le _
  have hu' : 0 < 1 - u := by linarith
  have hone : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ hu').2 (by linarith)
  have hX0 : 0 ≤ X := Real.rpow_nonneg hNpos.le _
  have hmid : B ^ (11 / 5 : ℝ) * (Wd * ∑ y, g y) + B ^ 2 * N * P ≤
      (KDecay_tailC d + 1) * ((1 - u)⁻¹ * B ^ (11 / 5 : ℝ)) := by
    have hl : B ^ (11 / 5 : ℝ) * (Wd * ∑ y, g y) ≤ B ^ (11 / 5 : ℝ) * (KDecay_tailC d / (1 - u)) :=
      mul_le_mul_of_nonneg_left hlat hB115
    have hz2 : B ^ 2 * N * P ≤ (1 - u)⁻¹ * B ^ (11 / 5 : ℝ) := by
      calc B ^ 2 * N * P ≤ B ^ (11 / 5 : ℝ) := hzero
        _ = 1 * B ^ (11 / 5 : ℝ) := (one_mul _).symm
        _ ≤ (1 - u)⁻¹ * B ^ (11 / 5 : ℝ) := mul_le_mul_of_nonneg_right hone hB115
    calc B ^ (11 / 5 : ℝ) * (Wd * ∑ y, g y) + B ^ 2 * N * P
        ≤ B ^ (11 / 5 : ℝ) * (KDecay_tailC d / (1 - u)) + (1 - u)⁻¹ * B ^ (11 / 5 : ℝ) := add_le_add hl hz2
      _ = (KDecay_tailC d + 1) * ((1 - u)⁻¹ * B ^ (11 / 5 : ℝ)) := by
          rw [div_eq_mul_inv]; ring
  calc ‖STELKLKg C n u σ a ω‖ ≤ Wd * (X * B ^ 2) * (X * (Bq * (∑ y, g y) + Ld * P)) := by
        have := hwin
        simpa only [mul_assoc] using this
    _ = X * X * (B ^ (11 / 5 : ℝ) * (Wd * ∑ y, g y) + B ^ 2 * N * P) := hmain
    _ ≤ X * X * ((KDecay_tailC d + 1) * ((1 - u)⁻¹ * B ^ (11 / 5 : ℝ))) :=
        mul_le_mul_of_nonneg_left hmid (mul_nonneg hX0 hX0)
    _ = X * X * (KDecay_tailC d + 1) * ((1 - u)⁻¹ * B ^ (11 / 5 : ℝ)) := by ring

/-- **The decay step** (band `expLK_prec`; (6.3) `eq:Exp(L-K)1` before the expectation): `ℰ^{LK×LK}_{u,σ,a} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}`
uniformly in `u ∈ [s,t]`.  On the complement of the two failure events of `STLKUgL` (`k = 2`, the factor `(x,a₂)`) and `STGdecayWgL … 0` (the factor `(a₁,y)`, at
`D = 2/𝔠`) every bound holds for every index at once, so `ExpEtermsAGen_det_core` applies; `StochDomAt.of_subset_union` with `τ' = τ/3`.  No grid lift. -/
theorem expLK_precg (μ : Measure sz.SeqΩ) (hd : 2 ≤ d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : sz.SizeTendsto)
    (hband : sz.Bandwidth 𝔠) (hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (ht1 : ∀ n, t n < 1) (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (hLKU : STLKUgL C μ s t) (hGd : STGdecayWgL C μ s t 0) :
    PrecL sz μ (U := STIdx2 sz s t)
      (fun n p ω => ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ)) := by
  have hsize := tendsto_size sz hsz
  have hD : (0 : ℝ) < 2 / 𝔠 := by positivity
  refine StochDomAt.of_subset_union hsize (hLKU 2 (by norm_num)) (hGd (2 / 𝔠) hD) ?_
  intro τ hτ
  refine ⟨τ / 3, by positivity, ?_⟩
  have hτ3 : 0 < τ / 3 := by positivity
  have hC : ∀ᶠ n in atTop, KDecay_tailC d + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) :=
    ((tendsto_rpow_atTop hτ3).comp hsz).eventually (eventually_ge_atTop (KDecay_tailC d + 1))
  filter_upwards [hlam, hband, hC, hsz.eventually (eventually_ge_atTop 1)] with n hl hb hCn hN1 ω hω
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  -- the two good events, at every index
  have hg1 : ∀ p : STIdx2 sz s t n,
      ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n (p.1 : ℝ) ^ 2 := by
    intro p
    by_contra hc
    exact hn1 ⟨p, lt_of_not_ge hc⟩
  have hg2 : ∀ p : STIdx2 sz s t n,
      ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
          (((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) * sz.Bctl n (p.1 : ℝ) ^ (1 / 5 : ℝ) *
            sz.STWB n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
              ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-(2 / 𝔠))) := by
    intro p
    by_contra hc
    exact hn2 ⟨p, lt_of_not_ge hc⟩
  -- `W^{-D} ≤ N^{-2}` from the bandwidth
  have hWD : ((sz.W n : ℕ) : ℝ) ^ (-(2 / 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) := by
    have h1 : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hNpos _
    have h2 := Real.rpow_le_rpow_of_nonpos h1 hb (by linarith : -(2 / 𝔠) ≤ 0)
    refine h2.trans (le_of_eq ?_)
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    field_simp
  -- the index of the endpoint
  obtain ⟨p, hp⟩ := hω
  obtain ⟨⟨u, hu⟩, σ, a⟩ := p
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (ht1 n)
  have key := ExpEtermsAGen_det_core C hd n (τ' := τ / 3) (D := 2 / 𝔠) ω hl hu0 hu1 hN hWD (hcol n) σ a
    (fun x => hg1 (⟨u, hu⟩, σ, ![x, a 1])) (fun y => by
      have h := hg2 (⟨u, hu⟩, σ, ![a 0, y])
      simp only [Real.rpow_zero, one_mul] at h
      exact h)
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := Real.rpow_nonneg hNpos.le _
  have hR0 : 0 ≤ (1 - u)⁻¹ * sz.Bctl n u ^ (11 / 5 : ℝ) :=
    mul_nonneg (inv_nonneg.2 (by linarith)) (Real.rpow_nonneg (STBctl_pos sz n hu1).le _)
  have hXXX : ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
      (KDecay_tailC d + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
          ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := mul_le_mul_of_nonneg_left hCn (mul_nonneg hX0 hX0)
      _ = ((sz.size n : ℕ) : ℝ) ^ τ := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; congr 1; ring
  have hle : ‖STELKLKg C n u σ a ω‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - u)⁻¹ * sz.Bctl n u ^ (11 / 5 : ℝ)) :=
    key.trans (mul_le_mul_of_nonneg_right hXXX hR0)
  exact absurd hp (not_lt.2 hle)

/-! ## 4. `≺ → 𝔼`: the first moment outside the failure event -/

/-- **`≺ → 𝔼`** for `ℰ^{LK×LK}` (band `expLK_expect`; (6.3) `eq:Exp(L-K)1` after the expectation): from the `≺` of `‖ℰ‖` against `R = (1-u)⁻¹ B^{11/5}`
(`expLK_precg`) and an almost-sure polynomial envelope `N^{Kenv}` along the window (`expLK_env_polyg`): `𝔼|ℰ| ≤ N^{τ/2} R + Env P(S_n)`, `P(S_n) ≤ N^{-(|Kenv|+3)}`, and
the floor `R ≥ N^{-11/5}`; the deterministic `Prec` through `st6_prec_det_iffg`. -/
theorem expLK_expectg (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ) {s t : ℕ → ℝ} {Kenv : ℝ}
    (hsz : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (henv : ∀ᶠ n in atTop, ∀ (p : STIdx2 sz s t n) (ω : sz.SeqΩ),
      ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
    (hprec : PrecL sz μ (U := STIdx2 sz s t)
        (fun n p ω => ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))) :
    STExpLKLKHiConclgL C μ s t := by
  have := hμ
  unfold STExpLKLKHiConclgL
  refine (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpELKLKg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  have hDp : 0 < |Kenv| + 3 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hprec (τ / 2) hτ2 (|Kenv| + 3) hDp, henv, hC, hsz.eventually (eventually_ge_atTop 1)]
    with n hP hEnv hN2 hN1
  rintro ⟨⟨u, hu⟩, σ, a⟩
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (ht1 n)
  have h1u : 0 < 1 - u := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set R : ℝ := (1 - u)⁻¹ * sz.Bctl n u ^ (11 / 5 : ℝ) with hR
  have hBpos : 0 < sz.Bctl n u := STBctl_pos sz n hu1
  -- the floor `R ≥ N^{-11/5}`
  have hone : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ h1u).2 (by linarith)
  have hfloor : N ^ (-(11 / 5 : ℝ)) ≤ R := by
    have hBN : N⁻¹ ≤ sz.Bctl n u := expLK_Bctl_ge sz n hu0 hu1
    have h1 : N ^ (-(11 / 5 : ℝ)) = (N⁻¹) ^ (11 / 5 : ℝ) := by
      rw [Real.rpow_neg hNpos.le, Real.inv_rpow hNpos.le]
    rw [h1]
    calc (N⁻¹) ^ (11 / 5 : ℝ) ≤ sz.Bctl n u ^ (11 / 5 : ℝ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hNpos.le) hBN (by norm_num)
      _ = 1 * sz.Bctl n u ^ (11 / 5 : ℝ) := (one_mul _).symm
      _ ≤ R := mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg hBpos.le _)
  have hR0 : 0 ≤ R := (Real.rpow_nonneg hNpos.le _).trans hfloor
  -- the failure event
  set S : Set sz.SeqΩ := badSetAt sz.size
    (fun n (p : STIdx2 sz s t n) ω => ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
    (fun n (p : STIdx2 sz s t n) _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ)) (τ / 2) n with hS
  have hPS : (μ S).toReal ≤ N ^ (-(|Kenv| + 3)) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hP
  -- the envelope
  have hEnvu : ∀ ω, ‖STELKLKg C n u σ a ω‖ ≤ N ^ Kenv := fun ω => hEnv (⟨u, hu⟩, σ, a) ω
  -- off `S`
  have hin : ∀ ω, ω ∉ S → ‖STELKLKg C n u σ a ω‖ ≤ N ^ (τ / 2) * R := by
    intro ω hω
    by_contra hc
    exact hω ⟨(⟨u, hu⟩, σ, a), lt_of_not_ge hc⟩
  have hfm := expLK_first_moment (P := μ) (f := fun ω => STELKLKg C n u σ a ω) (S := S)
    (c := N ^ (τ / 2) * R) (B := N ^ Kenv) (mul_nonneg (Real.rpow_nonneg hNpos.le _) hR0) hEnvu hin
  -- the tail
  have htail : N ^ Kenv * (μ S).toReal ≤ R := by
    calc N ^ Kenv * (μ S).toReal ≤ N ^ Kenv * N ^ (-(|Kenv| + 3)) :=
          mul_le_mul_of_nonneg_left hPS (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (Kenv + -(|Kenv| + 3)) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N ^ (-(11 / 5 : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le hN ?_
          have := le_abs_self Kenv
          linarith
      _ ≤ R := hfloor
  have hexp : STExpELKLKg C μ n u σ a = ∫ ω, STELKLKg C n u σ a ω ∂μ := rfl
  have hX2 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  calc ‖STExpELKLKg C μ n u σ a‖ ≤ ∫ ω, ‖STELKLKg C n u σ a ω‖ ∂μ := by
        rw [hexp]; exact norm_integral_le_integral_norm _
    _ ≤ N ^ (τ / 2) * R + N ^ Kenv * (μ S).toReal := hfm
    _ ≤ N ^ (τ / 2) * R + R := add_le_add le_rfl htail
    _ ≤ N ^ (τ / 2) * R + N ^ (τ / 2) * R := by
        have : R ≤ N ^ (τ / 2) * R := by nlinarith
        linarith
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * R) := by
        have h3 : 0 ≤ N ^ (τ / 2) * R := mul_nonneg hX2 hR0
        linarith [mul_le_mul_of_nonneg_right hN2 h3]
    _ = N ^ τ * R := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]; congr 2; ring

end Flow

/-! ## 5. The conclusion from the hypotheses it uses, and the statement `STExpLKLKHigL` -/

/-- **(6.3) `eq:Exp(L-K)1` per carrier** (band `STExpLKLKHiConcl_of_LKU`): from the hypotheses it uses -- admissibility, `0 ≤ s`, the right end `t ≤ T0`, `STLKUgL`
(`k = 2`), `STGdecayWgL … 0`, and the family data of the carrier: the representation `CltRepg` with `κ' ≤ Im m` and `N^{-1+δ} ≤ 1 - T0`, `STKboundgL`, the column
sums of `C.S`: `expLK_precg`, then `expLK_expectg` with `Kenv = 6` (`expLK_env_polyg`).  The window `STDriftHi` and the other hypotheses of `STIngR6gL` are not used:
the bound holds for every `u < 1`. -/
theorem STExpLKLKHiConclgL_of_LKU {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ)
    (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im)
    {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ)
    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (hLKU : STLKUgL C μ s t) (hGd : STGdecayWgL C μ s t 0) : STExpLKLKHiConclgL C μ s t := by
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT1 n)
  have hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n := (st6_lam_pos sz hadm.2.2.2.2).mono fun n h => h.le
  have hprec := expLK_precg C μ (by omega) hadm.1 hadm.2.2.1 hadm.2.2.2.1 hlam hs0 ht1 hcol hLKU hGd
  exact expLK_expectg C μ hμ hadm.2.2.1 hs0 ht1
    (expLK_env_polyg C μ hμ hadm.2.2.1 hrep hκ' hδ hm hs0 hst htT hT1 hrange hKb hcol) hprec

/-- **(6.3) `eq:Exp(L-K)1` over the carrier family** (band `stExpLKLKHi_holds`): the statement `STExpLKLKHigL` of `Chain/Step6Gen`, proved with `𝔠_d = 1/100`.  Family hypotheses:
the laws, `Step2EventsGen_Flow` (`Admissible`, `T0 < 1`), the class `IniTermGen_CltFlow` (`κ'`, `δ` before `(𝔠, sz, z)`, `CltRepg`),
`STKboundgL` and the column sums of `C.S`, each guarded by `0 < κ → Flow`.  Hypotheses of `STExpLKLKHigL` used: `0 ≤ s`, `s < t` (as `≤`), `t ≤ T0`, `STLKUgL`,
`STGdecayWgL … 0`; unused: `STDriftHi`, `STLKgL`, `STDecaygL`, `STExp2gL`, `STConStInd`, `STStep2CoregL`, `STLmaxUgL`. -/
theorem stExpLKLKHigL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz : Sizes d, IsProbabilityMeasure (law sz))
    (hFl : Step2EventsGen_Flow d Flow T0) (hClt : IniTermGen_CltFlow d law Flow mk T0)
    (hK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz))
    (hS : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(mk sz z).S n x y‖ ≤ 1) :
    STExpLKLKHigL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨κ', δ, hκ', -, hδ, H⟩ := hClt hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hHi hLK hDec hExp hcon hS2 hLmax hLKU hGd
  obtain ⟨H₀, g', E, hm, hrange, hrep, -⟩ := H 𝔠 sz z hflow
  exact STExpLKLKHiConclgL_of_LKU (mk sz z) (law sz) (hμ sz) hd (hFl.1 sz κ ε 𝔠 𝔡 z hflow) hrep hκ' hδ hm hs0
    (fun n => (hst n).le) htT (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow) hrange (hK sz κ ε 𝔠 𝔡 z hκ hflow)
    (hS sz κ ε 𝔠 𝔡 z hκ hflow) hLKU hGd

end RBM.BA
