/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpIniI
import RBM3D.Induction.DecayLoopB
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.KDecay
import RBM3D.Loop.KLFinal
import RBM3D.Path.Walk

/-!
# S6-07 (T2228, ST-5): the proofs of the pins `STExpDriftLo` and `STExpDriftDecay`

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:63-79` (`(eq:Exp(L-K)2)`,
`(eq:ExpLWn=2_smalleta)`, regime (iv)) and `paper/tex/3_5_Loop_Hierarchy.tex:1634` (`(deccA0)` for
the drift `D_u`).  Patterns: RBM2D `Evolution/MLExpDrift.lean` at `c9a24cf` (`_env_X` `:610`,
`_first_moment` `:717`) and T2222 (`Induction/ExpEtermsA.lean`); the `d = 2` bulk/far numerics
(`:1092`, `:1230`) are not ported.

Regime (iv).  `B = Bctl n u = W^{-d}B_{u,0}`, `N = (W L)^d`, `R_u = (1-u)⁻¹ (N(1-u))⁻³`.  `1-u ≤
1-s ≤ λ²/L^d` gives `B ≤ 2 (N(1-u))⁻¹`, so `N B⁴ ≤ 16 R_u`.  The drift is `D_u = 𝔼ℰ^{LK×LK} +
𝔼ℰ^{G̃}` and `𝔼ℰ^{G̃} = A + 𝔼 X_B` with `A` the deterministic part `(𝔼 avg)·S·𝒦^{(3)}` and `X_B`
the `(𝓛-𝒦)^{(3)}` part (`expDr_EGt_split`).  `ℰ^{LK×LK}` and `X_B` are `≺ N B⁴` off the failure
events of `STLKU` (`k = 1, 2, 3`), `A` is `≺ N B⁴` by `STExpAvgU` and `stKbound_timeIcc` (both
deterministic); `≺ → 𝔼` is the first moment off the failure event with a polynomial envelope `N⁶`
(`expDr_expect`).  No input is per time: every random input is uniform in `u ∈ [s,t]` (`Prec` over
`TimeIcc`), so no grid lift (DECISIONS §64 (4)).

Decay.  `stDecayLoopU_of_step2 … 0` and `stEtermDecay … 2` give, w.h.p., `|ℰ| ≤ W^{-(D+1)}` for
every `v ∈ [s_n,t_n]` and every far `a`; the first moment with the envelope `N⁶` and `P ≤
N^{-(D+7)}` gives `|𝔼ℰ| ≤ 2 W^{-(D+1)}`, hence `|D_v(a)| ≤ 4 W^{-(D+1)} ≤ W^{-D}` (`W ≥ 4`
eventually).  The regime `STReg5I` is not used.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 0. Vocabulary -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- The `(𝓛-𝒦)^{(3)}` part of `𝓔^{G̃,(2)}` of a fine matrix `H` (`STEGtM` with `STLM` replaced by `STLKM` in the cut 3-loops). -/
noncomputable def expDrEGtLKM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    (sz.STavgM n E u H (σ 0) x * SB d (sz.L n) (sz.lam n) x y *
        sz.STLKM n E u H ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      sz.STavgM n E u H (σ 1) x * SB d (sz.L n) (sz.lam n) x y *
        sz.STLKM n E u H ![σ 0, σ 1, σ 1] ![a 0, y, a 1])

/-- The deterministic part `W^d Σ_k Σ_{x,y} (𝔼 avg_{σ_k}(x)) S_{xy} 𝒦^{(3)}(cut_k y)` of `𝔼𝓔^{G̃,(2)}`. -/
noncomputable def expDrEGtK {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    ((∫ ω, sz.STavgM n E u (sz.seqHflow n u ω) (σ 0) x ∂(sz.seqP)) * SB d (sz.L n) (sz.lam n) x y *
        sz.STKloop n E u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      (∫ ω, sz.STavgM n E u (sz.seqHflow n u ω) (σ 1) x ∂(sz.seqP)) * SB d (sz.L n) (sz.lam n) x y *
        sz.STKloop n E u ![σ 0, σ 1, σ 1] ![a 0, y, a 1])

end RBM.Gauss.Sizes

/-! ## 1. Deterministic steps (one size) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The regime bound** (regime (iv), `1-u ≤ λ²/L^d`): `L^d(1-u) ≤ λ² ≤ λ² + (1-u)`, so
`(λ²+(1-u))⁻¹ ≤ (L^d(1-u))⁻¹` and `B_{u,0} ≤ 2 (L^d(1-u))⁻¹`, i.e. `W^{-d}B_{u,0} ≤ 2 (N(1-u))⁻¹` (`size = W^d L^d`). -/
theorem expDr_Bctl_le_IV {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1)
    (hreg : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d) :
    sz.Bctl n u ≤ 2 * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
  have h1 : 0 < 1 - u := by linarith
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hLu : ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) ≤ sz.lam n ^ 2 := by
    have := (le_div_iff₀ hLd).1 hreg
    linarith
  have hinv : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos h1, hsize]
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [hz, inv_one, mul_one]
  have hrhs : 2 * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
    rw [mul_assoc, mul_inv]; ring
  rw [hrhs]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith

/-- `B_{u,0} ≤ 2 (1-u)⁻¹` for `u < 1` (`λ² ≥ 0`, `W^d ≥ 1`, `L^d ≥ 1`). -/
private theorem expDr_Bctl_le_two {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) :
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

/-- The floor `N⁻¹ ≤ W^{-d}B_{u,0}` for `0 ≤ u < 1` (the merged `expAvg_Bctl_ge`, `ExpAvg.lean:604`). -/
private theorem expDr_Bctl_ge {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n u := expAvg_Bctl_ge sz n hu0 hu1

/-- Column sums of the block covariance: `Σ_x |S_{xy}| = 1` (`SB_transpose`, `sum_norm_SB_row`, `3 ≤ L`). -/
private theorem expDr_hcol {d : ℕ} (sz : Sizes d) (n : ℕ) (y : Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) x y‖ = 1 := by
  have hL3 := sz.three_le_L n
  rw [← sum_norm_SB_row d (sz.L n) (sz.lam n) hL3 y]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := congrFun (congrFun (SB_transpose d (sz.L n) (sz.lam n)) y) x
  rw [Matrix.transpose_apply] at h
  rw [h]

/-- The bilinear sum with the covariance: `‖Σ_{x,y} A_x S_{xy} C_y‖ ≤ α β L^d` if `|A| ≤ α`, `|C| ≤ β`. -/
private theorem expDr_bilin_le {d : ℕ} (sz : Sizes d) (n : ℕ) (A C : Zd d (sz.L n) → ℂ) {α β : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ α) (hC : ∀ y, ‖C y‖ ≤ β) :
    ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), A x * SB d (sz.L n) (sz.lam n) x y * C y‖ ≤
      α * β * ((sz.L n : ℕ) : ℝ) ^ d := by
  have hα : 0 ≤ α := (norm_nonneg _).trans (hA 0)
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hC 0)
  calc _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ‖A x * SB d (sz.L n) (sz.lam n) x y * C y‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_le _ _)
    _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), (α * β) * ‖SB d (sz.L n) (sz.lam n) x y‖ :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => by
          rw [norm_mul, norm_mul]
          calc ‖A x‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ * ‖C y‖
              = ‖A x‖ * ‖C y‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ := by ring
            _ ≤ (α * β) * ‖SB d (sz.L n) (sz.lam n) x y‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul (hA x) (hC y) (norm_nonneg _) hα) (norm_nonneg _)
    _ = α * β * ((sz.L n : ℕ) : ℝ) ^ d := by
        rw [Finset.sum_comm]
        have : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), (α * β) * ‖SB d (sz.L n) (sz.lam n) x y‖ = α * β := by
          intro y
          rw [← Finset.mul_sum, expDr_hcol sz n y, mul_one]
        simp only [this, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast; ring

/-- The two cuts of `𝓔^{G̃}` with a common bound: `‖W^d Σ_{x,y} (A₀ S C₀ + A₁ S C₁)‖ ≤ 2 W^d L^d α β`. -/
private theorem expDr_cuts_le {d : ℕ} (sz : Sizes d) (n : ℕ) (A₀ A₁ C₀ C₁ : Zd d (sz.L n) → ℂ) {α β : ℝ}
    (hA₀ : ∀ x, ‖A₀ x‖ ≤ α) (hA₁ : ∀ x, ‖A₁ x‖ ≤ α) (hC₀ : ∀ y, ‖C₀ y‖ ≤ β) (hC₁ : ∀ y, ‖C₁ y‖ ≤ β) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        (A₀ x * SB d (sz.L n) (sz.lam n) x y * C₀ y + A₁ x * SB d (sz.L n) (sz.lam n) x y * C₁ y)‖ ≤
      2 * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * (α * β) := by
  have h0 := expDr_bilin_le sz n A₀ C₀ hA₀ hC₀
  have h1 := expDr_bilin_le sz n A₁ C₁ hA₁ hC₁
  have hsum : ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        (A₀ x * SB d (sz.L n) (sz.lam n) x y * C₀ y + A₁ x * SB d (sz.L n) (sz.lam n) x y * C₁ y) =
      (∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), A₀ x * SB d (sz.L n) (sz.lam n) x y * C₀ y) +
        ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), A₁ x * SB d (sz.L n) (sz.lam n) x y * C₁ y := by
    simp only [Finset.sum_add_distrib]
  rw [hsum, norm_mul, norm_pow, Complex.norm_natCast]
  have hW : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖_‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
        (α * β * ((sz.L n : ℕ) : ℝ) ^ d + α * β * ((sz.L n : ℕ) : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h0 h1)) hW
    _ = _ := by ring

/-- `avg = (𝓛-𝒦)^{(1)}`: `STavgM` of the model matrix is `𝓛^{(1)} - 𝒦^{(1)}` (`KLK_one`, `STmsig = mSigma`). -/
private theorem expDr_avg_eq {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (τ : Bool) (x : Zd d (sz.L n)) :
    sz.STavgM n E u (sz.seqHflow n u ω) τ x =
      sz.Lloop n E u (fun _ : Fin 1 => τ) (fun _ => x) ω -
        sz.STKloop n E u (fun _ : Fin 1 => τ) (fun _ => x) := by
  have h : sz.STKloop n E u (fun _ : Fin 1 => τ) (fun _ => x) = mSigma E τ := by
    have : KLloopOf d (sz.L n) (fun _ : Fin 1 => τ) (fun _ => x) = ⟨[τ], [x]⟩ := by
      simp [KLloopOf, List.ofFn_succ]
    unfold Sizes.STKloop
    rw [this, KLK_one]
  rw [h]
  rfl

/-- **The envelope of `𝓔^{G̃}`**: `‖avg‖ ≤ η⁻¹ + 1` (`norm_Lloop_le` at `k = 0`, `norm_mSigma`), `‖𝓛^{(3)}‖ ≤ η⁻³`
(`k = 2`), the column sums of `S` and the two cuts. -/
theorem expDr_envEGt {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖sz.STEGt n E u σ a ω‖ ≤
      2 * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ 3) := by
  have hav : ∀ (τ : Bool) (x : Zd d (sz.L n)),
      ‖sz.STavgM n E u (sz.seqHflow n u ω) τ x‖ ≤ (etaT E u)⁻¹ + 1 := by
    intro τ x
    have h1 := sz.norm_Lloop_le n hE hu (k := 0) (fun _ : Fin 1 => τ) (fun _ => x) ω
    have h2 : ‖sz.STavgM n E u (sz.seqHflow n u ω) τ x‖ ≤
        ‖sz.Lloop n E u (fun _ : Fin 1 => τ) (fun _ => x) ω‖ + ‖STmsig E τ‖ := norm_sub_le _ _
    have h3 : ‖STmsig E τ‖ = 1 := norm_mSigma hE.le τ
    rw [pow_one] at h1
    linarith
  have hL3 : ∀ (σ' : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)),
      ‖sz.STLM n E u (sz.seqHflow n u ω) σ' b‖ ≤ (etaT E u)⁻¹ ^ 3 :=
    fun σ' b => sz.norm_Lloop_le n hE hu (k := 2) σ' b ω
  exact expDr_cuts_le sz n _ _ _ _ (fun x => hav (σ 0) x) (fun x => hav (σ 1) x)
    (fun y => hL3 _ _) (fun y => hL3 _ _)

end RBM.Gauss.Sizes

/-! ## 2. The split `𝔼ℰ^{G̃} = (𝔼 avg)·S·𝒦^{(3)} + 𝔼[avg·S·(𝓛-𝒦)^{(3)}]` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- A bounded measurable `ℂ`-valued random variable is integrable on the probability space `seqP`. -/
private theorem expDr_integrable {d : ℕ} (sz : Sizes d) {f : sz.SeqΩ → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f sz.seqP :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)

/-- Measurability of the loops of the model matrix (`walk_measurable_Lloop`, `STLM_seqHflow`). -/
private theorem expDr_meas_STLM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) : Measurable fun ω : sz.SeqΩ => sz.STLM n E u (sz.seqHflow n u ω) σ a :=
  walk_measurable_Lloop sz n E u σ a

private theorem expDr_meas_STavgM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (τ : Bool) (x : Zd d (sz.L n)) :
    Measurable fun ω : sz.SeqΩ => sz.STavgM n E u (sz.seqHflow n u ω) τ x :=
  (walk_measurable_Lloop sz n E u (fun _ : Fin 1 => τ) (fun _ => x)).sub_const _

/-- `𝓔^{G̃}` is a bounded measurable random variable (`expDr_envEGt`, `walk_measurable_Lloop`). -/
private theorem expDr_integrable_EGt {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : Integrable (fun ω => sz.STEGt n E u σ a ω) sz.seqP := by
  refine expDr_integrable sz ?_ (fun ω => expDr_envEGt sz n hE hu σ a ω)
  unfold Sizes.STEGt Sizes.STEGtM
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
  exact (((expDr_meas_STavgM sz n E u _ x).mul_const _).mul (expDr_meas_STLM sz n E u _ _)).add
    (((expDr_meas_STavgM sz n E u _ x).mul_const _).mul (expDr_meas_STLM sz n E u _ _))

/-- `𝓛^{(1)}` is integrable (`norm_Lloop_le` at `k = 0`, `walk_measurable_Lloop`). -/
private theorem expDr_integrable_L1 {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (τ : Bool) (x : Zd d (sz.L n)) :
    Integrable (fun ω => sz.Lloop n E u (fun _ : Fin 1 => τ) (fun _ => x) ω) sz.seqP :=
  expDr_integrable sz (walk_measurable_Lloop sz n E u _ _)
    (fun ω => (sz.norm_Lloop_le n hE hu (k := 0) (fun _ : Fin 1 => τ) (fun _ => x) ω))

/-- `avg` is integrable. -/
private theorem expDr_integrable_avg {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (τ : Bool) (x : Zd d (sz.L n)) :
    Integrable (fun ω => sz.STavgM n E u (sz.seqHflow n u ω) τ x) sz.seqP := by
  have h := (expDr_integrable_L1 sz n hE hu τ x).sub (integrable_const (STmsig E τ))
  exact h

/-- `𝔼 avg = 𝔼 𝓛^{(1)} - m(σ)` (`seqP` is a probability measure). -/
private theorem expDr_int_avg {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (τ : Bool) (x : Zd d (sz.L n)) :
    ∫ ω, sz.STavgM n E u (sz.seqHflow n u ω) τ x ∂(sz.seqP) =
      (∫ ω, sz.Lloop n E u (fun _ : Fin 1 => τ) (fun _ => x) ω ∂(sz.seqP)) - mSigma E τ := by
  have h : ∀ ω, sz.STavgM n E u (sz.seqHflow n u ω) τ x =
      sz.Lloop n E u (fun _ : Fin 1 => τ) (fun _ => x) ω - mSigma E τ := fun ω => rfl
  simp_rw [h]
  rw [integral_sub (expDr_integrable_L1 sz n hE hu τ x) (integrable_const _), integral_const]
  simp

/-- **The split** `𝔼𝓔^{G̃} = (𝔼 avg)·S·𝒦^{(3)} + 𝔼[avg·S·(𝓛-𝒦)^{(3)}]`: `STLM = STKloop + STLKM` pointwise and linearity
of the integral (`avg` bounded and measurable, `𝓔^{G̃}` bounded and measurable; `seqP` is a probability measure). -/
theorem expDr_EGt_split {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpEGt n E u σ a =
      expDrEGtK sz n E u σ a + ∫ ω, expDrEGtLKM sz n E u (sz.seqHflow n u ω) σ a ∂(sz.seqP) := by
  -- the pointwise decomposition `𝓔^{G̃} = Kpart + LKpart`
  set Kpart : sz.SeqΩ → ℂ := fun ω => (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    (sz.STavgM n E u (sz.seqHflow n u ω) (σ 0) x * SB d (sz.L n) (sz.lam n) x y *
        sz.STKloop n E u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      sz.STavgM n E u (sz.seqHflow n u ω) (σ 1) x * SB d (sz.L n) (sz.lam n) x y *
        sz.STKloop n E u ![σ 0, σ 1, σ 1] ![a 0, y, a 1]) with hKpart
  have hpt : ∀ ω, sz.STEGt n E u σ a ω = Kpart ω + expDrEGtLKM sz n E u (sz.seqHflow n u ω) σ a := by
    intro ω
    have hL : ∀ {k : ℕ} (σ' : Fin k → Bool) (b : Fin k → Zd d (sz.L n)),
        sz.STLM n E u (sz.seqHflow n u ω) σ' b =
          sz.STKloop n E u σ' b + sz.STLKM n E u (sz.seqHflow n u ω) σ' b := by
      intro k σ' b
      unfold Sizes.STLKM
      ring
    unfold Sizes.STEGt Sizes.STEGtM expDrEGtLKM
    simp only [hKpart]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hL, hL]
    ring
  -- integrability
  have hint_avg : ∀ (τ : Bool) (x : Zd d (sz.L n)),
      Integrable (fun ω => sz.STavgM n E u (sz.seqHflow n u ω) τ x) sz.seqP :=
    fun τ x => expDr_integrable_avg sz n hE hu τ x
  have hint_K : Integrable Kpart sz.seqP := by
    refine Integrable.const_mul (integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => ?_) _
    exact (((hint_avg _ x).mul_const _).mul_const _).add (((hint_avg _ x).mul_const _).mul_const _)
  have hint_E := expDr_integrable_EGt sz n hE hu σ a
  -- `LKpart = 𝓔^{G̃} - Kpart`
  have hLK : (fun ω => expDrEGtLKM sz n E u (sz.seqHflow n u ω) σ a) =
      fun ω => sz.STEGt n E u σ a ω - Kpart ω := by
    funext ω
    rw [hpt ω]; ring
  -- the integral of `Kpart`
  set F : Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℂ := fun x y ω =>
    sz.STavgM n E u (sz.seqHflow n u ω) (σ 0) x * SB d (sz.L n) (sz.lam n) x y *
        sz.STKloop n E u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      sz.STavgM n E u (sz.seqHflow n u ω) (σ 1) x * SB d (sz.L n) (sz.lam n) x y *
        sz.STKloop n E u ![σ 0, σ 1, σ 1] ![a 0, y, a 1] with hF
  have hFint : ∀ x y, Integrable (F x y) sz.seqP := fun x y =>
    (((hint_avg _ x).mul_const _).mul_const _).add (((hint_avg _ x).mul_const _).mul_const _)
  have e1 : ∫ ω, (∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), F x y ω) ∂(sz.seqP) =
      ∑ x : Zd d (sz.L n), ∫ ω, (∑ y : Zd d (sz.L n), F x y ω) ∂(sz.seqP) :=
    integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hFint x y
  have e2 : ∀ x : Zd d (sz.L n), ∫ ω, (∑ y : Zd d (sz.L n), F x y ω) ∂(sz.seqP) =
      ∑ y : Zd d (sz.L n), ∫ ω, F x y ω ∂(sz.seqP) :=
    fun x => integral_finsetSum _ fun y _ => hFint x y
  have e3 : ∀ x y : Zd d (sz.L n), ∫ ω, F x y ω ∂(sz.seqP) =
      (∫ ω, sz.STavgM n E u (sz.seqHflow n u ω) (σ 0) x ∂(sz.seqP)) * SB d (sz.L n) (sz.lam n) x y *
          sz.STKloop n E u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
        (∫ ω, sz.STavgM n E u (sz.seqHflow n u ω) (σ 1) x ∂(sz.seqP)) * SB d (sz.L n) (sz.lam n) x y *
          sz.STKloop n E u ![σ 0, σ 1, σ 1] ![a 0, y, a 1] := by
    intro x y
    rw [hF, integral_add (((hint_avg _ x).mul_const _).mul_const _) (((hint_avg _ x).mul_const _).mul_const _),
      integral_mul_const, integral_mul_const, integral_mul_const, integral_mul_const]
  have hKint : ∫ ω, Kpart ω ∂(sz.seqP) = expDrEGtK sz n E u σ a := by
    have : ∫ ω, Kpart ω ∂(sz.seqP) =
        (((sz.W n : ℕ) : ℂ) ^ d) * ∫ ω, (∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), F x y ω) ∂(sz.seqP) :=
      integral_const_mul _ _
    rw [this, e1]
    simp only [e2, e3]
    rfl
  rw [hLK, integral_sub hint_E hint_K, hKint]
  unfold Sizes.STExpEGt
  ring

end RBM.Gauss.Sizes

/-! ## 3. Along the sequence: the polynomial envelopes -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- `lemT z_n < 1` on the flow (`Im z_n > 0`, `N ≥ 1`). -/
private theorem expDr_lemT_lt_one {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : lemT (z n) < 1 := by
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (hz.2 n).2.1
  exact lemT_lt_one him

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually (the 5-line pattern of `KLFinal_flowLam`, `KLFinal.lean:294`). -/
private theorem expDr_flowLam {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hz.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- **`𝒦^{(3)}` uniformly in `u ∈ [s,t]`** (`(eq:bcal_k)` at `k = 3`, the merged `stKbound_timeIcc`) from `STFlow`. -/
private theorem expDr_K3 {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ)
    {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) :
    sz.Prec (U := fun n => TimeIcc s t n × (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n)))
      (fun n p _ => ‖sz.STKloop n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2) :=
  stKbound_timeIcc sz hd hκ (inv_pos.2 hz.1.2.1) hz.1.2.2.1
    (Eventually.of_forall (st6_flowE_le sz hz)) (expDr_flowLam sz hz) hs0 hst (st5_t_lt_one sz hz htT) 3 (by norm_num)

/-- The control at `u ≤ lemT z_n`, eventually in `n` uniformly in `u`: `N ≥ 20`, `u < 1`, `η_u > 0`,
`η_u⁻¹ ≤ N` (`expAvg_eta_inv_le`), `(1-u)⁻¹ ≤ η_u⁻¹ ≤ N` (`Im m ≤ 1`). -/
private theorem expDr_ctrl {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 20 ≤ ((sz.size n : ℕ) : ℝ) ∧ ∀ u : ℝ, u ≤ lemT (z n) →
      u < 1 ∧ 0 < etaT (STflowE z n) u ∧ (etaT (STflowE z n) u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧
        (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [expAvg_eta_inv_le sz hκ hε hz, hz.1.2.2.1.eventually (eventually_ge_atTop 20)] with n hη hN
  refine ⟨hN, fun u hu => ?_⟩
  have hu1 : u < 1 := hu.trans_lt (expDr_lemT_lt_one sz hz n)
  have hE2 : |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz n
  have hepos : 0 < etaT (STflowE z n) u := etaT_pos hE2 hu1
  have hx := hη u hu
  have hIm1 : (mE (STflowE z n)).im ≤ 1 := by
    have := Complex.im_le_norm (mE (STflowE z n))
    rwa [norm_mE hE2.le] at this
  have hle : etaT (STflowE z n) u ≤ 1 - u := by
    unfold etaT
    have h0 : 0 < 1 - u := by linarith
    calc (1 - u) * (mE (STflowE z n)).im ≤ (1 - u) * 1 := by gcongr
      _ = 1 - u := mul_one _
  exact ⟨hu1, hepos, hx, (inv_anti₀ hepos hle).trans hx⟩

/-- **The envelopes are polynomial** on the flow, uniformly in `u ∈ [s_n,t_n]`, `σ`, `a`, `ω`: `𝓔^{LK×LK}`, `𝓔^{G̃}` and its
`(𝓛-𝒦)^{(3)}` part are `≤ N⁶` eventually.  `𝓔^{LK×LK}`: `expLK_env`, `η_u⁻¹ ≤ N`, `(1-u)⁻¹ ≤ N`, `4N⁵ ≤ N⁶`;
`𝓔^{G̃}`: `expDr_envEGt`, `2N(η⁻¹+1)η⁻³ ≤ 4N⁵`; `X_B`: the same with `η⁻³ + ‖𝒦^{(3)}‖`, `‖𝒦^{(3)}‖ ≤ N B² ≤ 4N³`
(`stKbound_timeIcc` at `τ = 1` through `st6_prec_det_iff`, `B ≤ 2(1-u)⁻¹ ≤ 2N`), `20N⁵ ≤ N⁶`. -/
theorem expDr_env_poly {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, ∀ (p : STIdx2 sz s t n) (ω : sz.SeqΩ),
      ‖sz.STELKLK n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
      ‖sz.STEGt n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
      ‖expDrEGtLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) := by
  have hsz := hz.1.2.2.1
  have hK := (st6_prec_det_iff sz hsz (V := fun n => TimeIcc s t n × (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n)))
    (fun n p => ‖sz.STKloop n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (sz.Bctl n (p.1 : ℝ)) ^ 2)).1 (expDr_K3 sz hd hκ hz hs0 hst htT) 1 one_pos
  filter_upwards [expDr_ctrl sz hκ hε hz, hK] with n ⟨hN20, hc⟩ hKn
  rintro ⟨⟨u, hu⟩, σ, a⟩ ω
  obtain ⟨hu1, hepos, hx, hy⟩ := hc u (hu.2.trans (htT n))
  have hE2 : |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz n
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have h6 : N ^ (6 : ℝ) = N ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h6]
  have hx0 : 0 ≤ (etaT (STflowE z n) u)⁻¹ := (inv_pos.2 hepos).le
  have hy0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = N := by
    rw [hNdef]; simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hN5 : ∀ c : ℝ, 0 ≤ c → c ≤ 20 → c * N ^ 5 ≤ N ^ 6 := by
    intro c hc0 hc20
    have h5 : 0 ≤ N ^ 5 := by positivity
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · -- `ℰ^{LK×LK}`
    refine (expLK_env sz n hE2 hu0 hu1 σ a ω).trans ?_
    rw [hWL]
    have hsq : (etaT (STflowE z n) u)⁻¹ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hx0 hx 2
    have hsum : (etaT (STflowE z n) u)⁻¹ ^ 2 + (1 - u)⁻¹ ≤ 2 * N ^ 2 := by nlinarith
    have hsum0 : 0 ≤ (etaT (STflowE z n) u)⁻¹ ^ 2 + (1 - u)⁻¹ := by positivity
    have hsq2 : ((etaT (STflowE z n) u)⁻¹ ^ 2 + (1 - u)⁻¹) ^ 2 ≤ (2 * N ^ 2) ^ 2 := pow_le_pow_left₀ hsum0 hsum 2
    calc N * ((etaT (STflowE z n) u)⁻¹ ^ 2 + (1 - u)⁻¹) ^ 2 ≤ N * (2 * N ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq2 (by linarith)
      _ = 4 * N ^ 5 := by ring
      _ ≤ N ^ 6 := hN5 4 (by norm_num) (by norm_num)
  · -- `ℰ^{G̃}`
    refine (expDr_envEGt sz n hE2 hu1 σ a ω).trans ?_
    rw [hWL]
    have h1 : (etaT (STflowE z n) u)⁻¹ + 1 ≤ 2 * N := by linarith
    have h3 : (etaT (STflowE z n) u)⁻¹ ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ hx0 hx 3
    have h13 : ((etaT (STflowE z n) u)⁻¹ + 1) * (etaT (STflowE z n) u)⁻¹ ^ 3 ≤ (2 * N) * N ^ 3 :=
      mul_le_mul h1 h3 (by positivity) (by positivity)
    calc 2 * N * (((etaT (STflowE z n) u)⁻¹ + 1) * (etaT (STflowE z n) u)⁻¹ ^ 3) ≤ 2 * N * ((2 * N) * N ^ 3) :=
          mul_le_mul_of_nonneg_left h13 (by linarith)
      _ = 4 * N ^ 5 := by ring
      _ ≤ N ^ 6 := hN5 4 (by norm_num) (by norm_num)
  · -- the `(𝓛-𝒦)^{(3)}` part
    have hB : sz.Bctl n u ≤ 2 * N := by
      have := expDr_Bctl_le_two sz n hu1
      linarith
    have hB0 : 0 ≤ sz.Bctl n u := (STBctl_pos sz n hu1).le
    have hK3 : ∀ (σ' : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)),
        ‖sz.STKloop n (STflowE z n) u σ' b‖ ≤ 4 * N ^ 3 := by
      intro σ' b
      have h := hKn (⟨u, hu⟩, σ', b)
      rw [Real.rpow_one] at h
      refine h.trans ?_
      calc N * sz.Bctl n u ^ 2 ≤ N * (2 * N) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hB 2) (by linarith)
        _ = 4 * N ^ 3 := by ring
    have hav : ∀ (τ : Bool) (x : Zd d (sz.L n)),
        ‖sz.STavgM n (STflowE z n) u (sz.seqHflow n u ω) τ x‖ ≤ (etaT (STflowE z n) u)⁻¹ + 1 := by
      intro τ x
      have h1 := sz.norm_Lloop_le n hE2 hu1 (k := 0) (fun _ : Fin 1 => τ) (fun _ => x) ω
      have h2 : ‖sz.STavgM n (STflowE z n) u (sz.seqHflow n u ω) τ x‖ ≤
          ‖sz.Lloop n (STflowE z n) u (fun _ : Fin 1 => τ) (fun _ => x) ω‖ + ‖STmsig (STflowE z n) τ‖ :=
        norm_sub_le _ _
      have h3 : ‖STmsig (STflowE z n) τ‖ = 1 := norm_mSigma hE2.le τ
      rw [pow_one] at h1
      linarith
    have hLK3 : ∀ (σ' : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)),
        ‖sz.STLKM n (STflowE z n) u (sz.seqHflow n u ω) σ' b‖ ≤ N ^ 3 + 4 * N ^ 3 := by
      intro σ' b
      have e : sz.STLKM n (STflowE z n) u (sz.seqHflow n u ω) σ' b =
          sz.Lloop n (STflowE z n) u σ' b ω - sz.STKloop n (STflowE z n) u σ' b := rfl
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hK3 σ' b))
      refine (sz.norm_Lloop_le n hE2 hu1 (k := 2) σ' b ω).trans ?_
      exact pow_le_pow_left₀ hx0 hx 3
    unfold expDrEGtLKM
    refine (expDr_cuts_le sz n _ _ _ _ (fun x => hav (σ 0) x) (fun x => hav (σ 1) x)
      (fun y => hLK3 _ _) (fun y => hLK3 _ _)).trans ?_
    rw [hWL]
    have h1 : (etaT (STflowE z n) u)⁻¹ + 1 ≤ 2 * N := by linarith
    calc 2 * N * (((etaT (STflowE z n) u)⁻¹ + 1) * (N ^ 3 + 4 * N ^ 3)) ≤ 2 * N * ((2 * N) * (N ^ 3 + 4 * N ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) (by linarith)
      _ = 20 * N ^ 5 := by ring
      _ ≤ N ^ 6 := hN5 20 (by norm_num) (by norm_num)

end RBM.Gauss.Sizes

/-! ## 4. `≺ → 𝔼` and the three random/deterministic estimates in regime (iv) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The first moment outside a small event** (copy of the private `expLK_first_moment`, `ExpEtermsA.lean:461`; RBM2D
`MLExpDrift_first_moment` `MLExpDrift.lean:717`): `‖f‖ ≤ c` off `S` and `‖f‖ ≤ B` everywhere give `𝔼‖f‖ ≤ c + B P(S)`, with no
measurability of `f` or `S`. -/
private theorem expDr_first_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℂ} {S : Set Ω} {c B : ℝ} (hc : 0 ≤ c) (hB : ∀ ω, ‖f ω‖ ≤ B)
    (hin : ∀ ω, ω ∉ S → ‖f ω‖ ≤ c) : ∫ ω, ‖f ω‖ ∂P ≤ c + B * (P S).toReal := by
  classical
  set S' : Set Ω := toMeasurable P S with hS'
  have hmeas : MeasurableSet S' := measurableSet_toMeasurable P S
  have hPS : P S' = P S := measure_toMeasurable S
  have hpt : ∀ ω, ‖f ω‖ ≤ c + B * S'.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ S'
    · rw [Set.indicator_of_mem hω]
      have := hB ω
      linarith
    · rw [Set.indicator_of_notMem hω]
      have := hin ω (fun h => hω (subset_toMeasurable P S h))
      linarith
  have hint : Integrable (fun ω => c + B * S'.indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const c).add (Integrable.const_mul ((integrable_const (1 : ℝ)).indicator hmeas) B)
  calc ∫ ω, ‖f ω‖ ∂P ≤ ∫ ω, (c + B * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = c + B * (P S).toReal := by
        rw [integral_add (integrable_const c) (Integrable.const_mul
          ((integrable_const (1 : ℝ)).indicator hmeas) B), integral_const,
          integral_const_mul, integral_indicator_const _ hmeas]
        simp [measureReal_def, hPS]

/-- **`≺ → 𝔼`** (generic): from the `≺` of `‖X_v‖` against a deterministic `R`, a polynomial envelope `N^{Kenv}` and a
polynomial floor `R ≥ N^{-Kf}`: `𝔼‖X_v‖ ≤ N^{τ/2} R + N^{Kenv} P(S_n)`, `P(S_n) ≤ N^{-(|Kenv|+|Kf|+1)}`; the deterministic
`Prec` through `st6_prec_det_iff`. -/
theorem expDr_expect {d : ℕ} (sz : Sizes d) {V : ℕ → Type} (X : ∀ n, V n → sz.SeqΩ → ℂ) (R : ∀ n, V n → ℝ)
    {Kenv Kf : ℝ} (hsz : sz.SizeTendsto)
    (henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
    (hfloor : ∀ᶠ n in atTop, ∀ v, ((sz.size n : ℕ) : ℝ) ^ (-Kf) ≤ R n v)
    (hprec : sz.Prec (U := V) (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v)) :
    sz.Prec (U := V) (fun n v _ => ‖∫ ω, X n v ω ∂(sz.seqP)‖) (fun n v _ => R n v) := by
  refine (st6_prec_det_iff sz hsz (fun n v => ‖∫ ω, X n v ω ∂(sz.seqP)‖) R).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  have hDp : 0 < |Kenv| + |Kf| + 1 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hprec (τ / 2) hτ2 (|Kenv| + |Kf| + 1) hDp, henv, hfloor, hC,
    hsz.eventually (eventually_ge_atTop 1)] with n hP hEnv hFl hN2 hN1
  intro v
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hR0 : 0 ≤ R n v := (Real.rpow_nonneg hNpos.le _).trans (hFl v)
  set S : Set sz.SeqΩ := badSetAt sz.size (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v) (τ / 2) n with hS
  have hPS : (sz.seqP S).toReal ≤ N ^ (-(|Kenv| + |Kf| + 1)) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hP
  have hin : ∀ ω, ω ∉ S → ‖X n v ω‖ ≤ N ^ (τ / 2) * R n v := by
    intro ω hω
    by_contra hc
    exact hω ⟨v, lt_of_not_ge hc⟩
  have hfm := expDr_first_moment (P := sz.seqP) (f := fun ω => X n v ω) (S := S)
    (c := N ^ (τ / 2) * R n v) (B := N ^ Kenv) (mul_nonneg (Real.rpow_nonneg hNpos.le _) hR0)
    (fun ω => hEnv v ω) hin
  have htail : N ^ Kenv * (sz.seqP S).toReal ≤ R n v := by
    calc N ^ Kenv * (sz.seqP S).toReal ≤ N ^ Kenv * N ^ (-(|Kenv| + |Kf| + 1)) :=
          mul_le_mul_of_nonneg_left hPS (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (Kenv + -(|Kenv| + |Kf| + 1)) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N ^ (-Kf) := by
          refine Real.rpow_le_rpow_of_exponent_le hN ?_
          have h1 := le_abs_self Kenv
          have h2 := le_abs_self Kf
          linarith
      _ ≤ R n v := hFl v
  have hX2 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  calc ‖∫ ω, X n v ω ∂(sz.seqP)‖ ≤ ∫ ω, ‖X n v ω‖ ∂(sz.seqP) := norm_integral_le_integral_norm _
    _ ≤ N ^ (τ / 2) * R n v + N ^ Kenv * (sz.seqP S).toReal := hfm
    _ ≤ N ^ (τ / 2) * R n v + R n v := add_le_add le_rfl htail
    _ ≤ N ^ (τ / 2) * R n v + N ^ (τ / 2) * R n v := by
        have : R n v ≤ N ^ (τ / 2) * R n v := by nlinarith
        linarith
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * R n v) := by
        have h3 : 0 ≤ N ^ (τ / 2) * R n v := mul_nonneg hX2 hR0
        linarith [mul_le_mul_of_nonneg_right hN2 h3]
    _ = N ^ τ * R n v := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]; congr 2; ring

/-- **`𝓔^{LK×LK}` in regime (iv), random, no regime used**: off the failure event of `STLKU … 2` at `τ/2`, both factors are
`≤ N^{τ/2}B²` for every index, so `‖𝓔‖ ≤ W^d L^d N^τ B⁴ = N^τ · N B⁴` (`expLK_window_le` with `M = f = N^{τ/2}B²`).
No grid lift (`STLKU` is uniform in `u`). -/
theorem expDr_LK_prec {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (hLKU : STLKU sz E s t) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) := by
  refine StochDomAt.of_subset (hLKU 2 (by norm_num)) ?_
  intro τ hτ
  refine ⟨τ / 2, by positivity, ?_⟩
  filter_upwards [hsz.eventually (eventually_ge_atTop 1)] with n hN1 ω hω
  by_contra hcon
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hg : ∀ p : STIdx2 sz s t n,
      ‖sz.Lloop n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - sz.STKloop n (E n) (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (p.1 : ℝ) ^ 2 := by
    intro p
    by_contra hc
    exact hcon ⟨p, lt_of_not_ge hc⟩
  obtain ⟨p, hp⟩ := hω
  obtain ⟨⟨u, hu⟩, σ, a⟩ := p
  have key := expLK_window_le sz n (E n) u (sz.seqHflow n u ω) σ a
    (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n u ^ 2) (fun _ => ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n u ^ 2)
    (fun x => hg (⟨u, hu⟩, σ, ![x, a 1])) (fun y => hg (⟨u, hu⟩, σ, ![a 0, y]))
  have hsum : ∑ _y : Zd d (sz.L n), ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n u ^ 2 =
      ((sz.L n : ℕ) : ℝ) ^ d * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n u ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    push_cast; ring
  rw [hsum] at key
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hXX : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hle : ‖sz.STELKLK n (E n) u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by
    unfold Sizes.STELKLK
    refine key.trans (le_of_eq ?_)
    rw [← hXX, ← hWL]
    ring
  exact absurd hp (not_lt.2 hle)

/-- **`X_B` (the `(𝓛-𝒦)^{(3)}` part of `𝓔^{G̃}`), random**: `STLKU … 1` (`avg = (𝓛-𝒦)^{(1)}`, `expDr_avg_eq`) and `STLKU … 3` at
the cut indices, `of_subset_union`, `τ' = τ/3`: `‖X_B‖ ≤ 2 N^{2τ/3} N B⁴ ≤ N^τ · N B⁴`. -/
theorem expDr_EGtLK_prec {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (hLKU : STLKU sz E s t) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖expDrEGtLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) (hLKU 1 le_rfl) (hLKU 3 (by norm_num)) ?_
  intro τ hτ
  refine ⟨τ / 3, by positivity, ?_⟩
  have hτ3 : 0 < τ / 3 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) :=
    ((tendsto_rpow_atTop hτ3).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hC, hsz.eventually (eventually_ge_atTop 1)] with n hN2 hN1 ω hω
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  obtain ⟨hn1, hn3⟩ := hcon
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hg1 : ∀ p : TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)),
      ‖sz.Lloop n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - sz.STKloop n (E n) (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n (p.1 : ℝ) ^ 1 := by
    intro p
    by_contra hc
    exact hn1 ⟨p, lt_of_not_ge hc⟩
  have hg3 : ∀ p : TimeIcc s t n × (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n)),
      ‖sz.Lloop n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - sz.STKloop n (E n) (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n (p.1 : ℝ) ^ 3 := by
    intro p
    by_contra hc
    exact hn3 ⟨p, lt_of_not_ge hc⟩
  obtain ⟨p, hp⟩ := hω
  obtain ⟨⟨u, hu⟩, σ, a⟩ := p
  have hav : ∀ (τ' : Bool) (x : Zd d (sz.L n)),
      ‖sz.STavgM n (E n) u (sz.seqHflow n u ω) τ' x‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 1 := by
    intro τ' x
    rw [expDr_avg_eq]
    exact hg1 (⟨u, hu⟩, fun _ => τ', fun _ => x)
  have key := expDr_cuts_le sz n
    (fun x => sz.STavgM n (E n) u (sz.seqHflow n u ω) (σ 0) x) (fun x => sz.STavgM n (E n) u (sz.seqHflow n u ω) (σ 1) x)
    (fun y => sz.STLKM n (E n) u (sz.seqHflow n u ω) ![σ 0, σ 0, σ 1] ![y, a 0, a 1])
    (fun y => sz.STLKM n (E n) u (sz.seqHflow n u ω) ![σ 0, σ 1, σ 1] ![a 0, y, a 1])
    (α := ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 1) (β := ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 3)
    (fun x => hav (σ 0) x) (fun x => hav (σ 1) x)
    (fun y => hg3 (⟨u, hu⟩, ![σ 0, σ 0, σ 1], ![y, a 0, a 1]))
    (fun y => hg3 (⟨u, hu⟩, ![σ 0, σ 1, σ 1], ![a 0, y, a 1]))
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hXXX : ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
      ((sz.size n : ℕ) : ℝ) ^ (τ / 3) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; congr 1; ring
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := Real.rpow_nonneg hNpos.le _
  have hNB : 0 ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4 := by positivity
  have hle : ‖expDrEGtLKM sz n (E n) u (sz.seqHflow n u ω) σ a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by
    unfold expDrEGtLKM
    refine key.trans ?_
    rw [hWL, ← hXXX]
    have h2 : 2 * (((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := by
      have := mul_nonneg hX0 hX0
      nlinarith
    calc 2 * ((sz.size n : ℕ) : ℝ) * ((((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 1) *
          (((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 3))
        = 2 * (((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) *
          (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hNB
  exact absurd hp (not_lt.2 hle)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The deterministic part of `𝔼𝓔^{G̃}`**: `(res_ELK_n=1)` (`STExpAvgU`, `|𝔼 avg| ≺ B²`, through `expDr_int_avg`) and `(eq:bcal_k)`
at `k = 3` uniformly in `u` (`stKbound_timeIcc`, `|𝒦^{(3)}| ≺ B²`), both deterministic (`st6_prec_det_iff`), and the two cuts:
`|A| ≤ 2 N (N^{τ/4}B²)² ≤ N^τ · N B⁴`. -/
theorem expDr_EGtK_prec {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (_hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hAvg : STExpAvgU sz (STflowE z) s t) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p _ => ‖expDrEGtK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) := by
  have hsz := hz.1.2.2.1
  refine (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖expDrEGtK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)).2 ?_
  intro τ hτ
  have hτ4 : 0 < τ / 4 := by positivity
  have hA := (st6_prec_det_iff sz hsz (V := fun n => TimeIcc s t n × Bool × Zd d (sz.L n))
    (fun n p => ‖(∫ ω, sz.Lloop n (STflowE z n) (p.1 : ℝ) (fun _ : Fin 1 => p.2.1) (fun _ => p.2.2) ω ∂(sz.seqP)) -
      mSigma (STflowE z n) p.2.1‖)
    (fun n p => (sz.Bctl n (p.1 : ℝ)) ^ 2)).1 hAvg (τ / 4) hτ4
  have hK := (st6_prec_det_iff sz hsz (V := fun n => TimeIcc s t n × (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n)))
    (fun n p => ‖sz.STKloop n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (sz.Bctl n (p.1 : ℝ)) ^ 2)).1 (expDr_K3 sz hd hκ hz hs0 hst htT) (τ / 4) hτ4
  have hτ2 : 0 < τ / 2 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hA, hK, hC, hsz.eventually (eventually_ge_atTop 1)] with n hAn hKn hN2 hN1
  rintro ⟨⟨u, hu⟩, σ, a⟩
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hE2 : |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz n
  have hu1 : u < 1 := hu.2.trans_lt (st5_t_lt_one sz hz htT n)
  have hav : ∀ (τ' : Bool) (x : Zd d (sz.L n)),
      ‖∫ ω, sz.STavgM n (STflowE z n) u (sz.seqHflow n u ω) τ' x ∂(sz.seqP)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2 := by
    intro τ' x
    rw [expDr_int_avg sz n hE2 hu1]
    exact hAn (⟨u, hu⟩, τ', x)
  have key := expDr_cuts_le sz n
    (fun x => ∫ ω, sz.STavgM n (STflowE z n) u (sz.seqHflow n u ω) (σ 0) x ∂(sz.seqP))
    (fun x => ∫ ω, sz.STavgM n (STflowE z n) u (sz.seqHflow n u ω) (σ 1) x ∂(sz.seqP))
    (fun y => sz.STKloop n (STflowE z n) u ![σ 0, σ 0, σ 1] ![y, a 0, a 1])
    (fun y => sz.STKloop n (STflowE z n) u ![σ 0, σ 1, σ 1] ![a 0, y, a 1])
    (α := ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2) (β := ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2)
    (fun x => hav (σ 0) x) (fun x => hav (σ 1) x)
    (fun y => hKn (⟨u, hu⟩, ![σ 0, σ 0, σ 1], ![y, a 0, a 1]))
    (fun y => hKn (⟨u, hu⟩, ![σ 0, σ 1, σ 1], ![a 0, y, a 1]))
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hXX : ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hXX2 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hNB : 0 ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4 := by positivity
  unfold expDrEGtK
  refine key.trans ?_
  rw [hWL]
  have h2 : 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    nlinarith
  calc 2 * ((sz.size n : ℕ) : ℝ) * ((((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2) *
        (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2))
      = 2 * (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) *
        (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by ring
    _ = 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by rw [hXX]
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) :=
        mul_le_mul_of_nonneg_right h2 hNB
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by rw [hXX2]

end RBM.Gauss.Sizes

/-! ## 5. Regime (iv): the conclusion from the premises it uses, and the pin -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The floor** `N^{-3} ≤ N B⁴` for `0 ≤ u < 1` (`B ≥ N⁻¹`, `expDr_Bctl_ge`): the polynomial floor of `expDr_expect` with `Kf = 3`. -/
private theorem expDr_floor {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (ht1 : ∀ n, t n < 1) :
    ∀ᶠ n in atTop, ∀ p : STIdx2 sz s t n,
      ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4 := by
  filter_upwards [hsz.eventually (eventually_ge_atTop 1)] with n hN1 p
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hB := expDr_Bctl_ge sz n hu0 hu1
  have h4 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ 4 ≤ (sz.Bctl n (p.1 : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (inv_nonneg.2 hNpos.le) hB 4
  have e : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) = ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ)⁻¹) ^ 4 := by
    rw [show (-(3 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hNpos.le, Real.rpow_natCast]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h4 hNpos.le

/-- **(iv) assembly** (`(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`): `D_u = 𝔼ℰ^{LK×LK} + A + 𝔼 X_B` (`expDr_EGt_split`); `expDr_expect`
(`Kenv = 6` from `expDr_env_poly`, `Kf = 3` from the floor `B ≥ N⁻¹`) turns `expDr_LK_prec`, `expDr_EGtLK_prec` into deterministic
bounds `≺ N B⁴`, `expDr_EGtK_prec` is already deterministic; then `N B⁴ ≤ 16 R_u` (`expDr_Bctl_le_IV`, `1-u ≤ 1-s`).  The regime
`STReg5IV` is used only there. -/
theorem STExpDriftLoConcl_of_LKU {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5IV sz s t) (hLKU : STLKU sz (STflowE z) s t)
    (hAvg : STExpAvgU sz (STflowE z) s t) : STExpDriftLoConcl sz (STflowE z) s t := by
  have hsz := hz.1.2.2.1
  have henv := expDr_env_poly sz hd hκ hε hz hs0 hst htT
  have hfloor := expDr_floor sz hsz hs0 (st5_t_lt_one sz hz htT)
  have P1 := expDr_expect sz (V := STIdx2 sz s t)
    (fun n p ω => sz.STELKLK n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) (Kenv := 6) (Kf := 3) hsz
    (henv.mono fun n h p ω => (h p ω).1) hfloor (expDr_LK_prec sz hsz hLKU)
  have P3 := expDr_expect sz (V := STIdx2 sz s t)
    (fun n p ω => expDrEGtLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) (Kenv := 6) (Kf := 3) hsz
    (henv.mono fun n h p ω => (h p ω).2.2) hfloor (expDr_EGtLK_prec sz hsz hLKU)
  have P2 := expDr_EGtK_prec sz hd hκ hε hz hs0 hst htT hAvg
  have D1 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖∫ ω, sz.STELKLK n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω ∂(sz.seqP)‖)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)).1 P1
  have D3 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖∫ ω, expDrEGtLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2 ∂(sz.seqP)‖)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)).1 P3
  have D2 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖expDrEGtK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)).1 P2
  refine (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖sz.STExpDrift n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - (p.1 : ℝ)))⁻¹) ^ 3)).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  have hC : ∀ᶠ n in atTop, (48 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 48)
  filter_upwards [D1 (τ / 2) hτ2, D2 (τ / 2) hτ2, D3 (τ / 2) hτ2, hC,
    hsz.eventually (eventually_ge_atTop 1)] with n h1 h2 h3 hN48 hN1
  intro p
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  obtain ⟨⟨u, hu⟩, σ, a⟩ := p
  have hE2 : |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz n
  have hu1 : u < 1 := hu.2.trans_lt (st5_t_lt_one sz hz htT n)
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have h1u : 0 < 1 - u := by linarith
  have hBpos : 0 < sz.Bctl n u := STBctl_pos sz n hu1
  have hreg : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d := by
    have := hR n
    linarith [hu.1]
  have hB := expDr_Bctl_le_IV sz n hu1 hreg
  -- `N B⁴ ≤ 16 R_u`
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hw : N * (sz.Bctl n u) ^ 4 ≤ 16 * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) := by
    calc N * (sz.Bctl n u) ^ 4 ≤ N * (2 * (N * (1 - u))⁻¹) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBpos.le hB 4) hNpos.le
      _ = 16 * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) := by
          field_simp
          ring
  have hRu : 0 ≤ (1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3 := by positivity
  have hX0 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hsplit := expDr_EGt_split sz n hE2 hu1 σ a
  have e1 := h1 (⟨u, hu⟩, σ, a)
  have e2 := h2 (⟨u, hu⟩, σ, a)
  have e3 := h3 (⟨u, hu⟩, σ, a)
  have hXX : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  calc ‖sz.STExpDrift n (STflowE z n) u σ a‖
      = ‖(∫ ω, sz.STELKLK n (STflowE z n) u σ a ω ∂(sz.seqP)) + (expDrEGtK sz n (STflowE z n) u σ a +
          ∫ ω, expDrEGtLKM sz n (STflowE z n) u (sz.seqHflow n u ω) σ a ∂(sz.seqP))‖ := by
        unfold Sizes.STExpDrift
        rw [hsplit]; rfl
    _ ≤ ‖∫ ω, sz.STELKLK n (STflowE z n) u σ a ω ∂(sz.seqP)‖ + (‖expDrEGtK sz n (STflowE z n) u σ a‖ +
          ‖∫ ω, expDrEGtLKM sz n (STflowE z n) u (sz.seqHflow n u ω) σ a ∂(sz.seqP)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ N ^ (τ / 2) * (N * sz.Bctl n u ^ 4) + (N ^ (τ / 2) * (N * sz.Bctl n u ^ 4) +
          N ^ (τ / 2) * (N * sz.Bctl n u ^ 4)) := add_le_add e1 (add_le_add e2 e3)
    _ = 3 * N ^ (τ / 2) * (N * sz.Bctl n u ^ 4) := by ring
    _ ≤ 3 * N ^ (τ / 2) * (16 * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (48 * N ^ (τ / 2)) * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) := by ring
    _ ≤ (N ^ (τ / 2) * N ^ (τ / 2)) * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hRu
    _ = N ^ τ * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) := by rw [hXX]

/-- **`(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`** (`6:63-66`, `6:73-79`): the merged pin `STExpDriftLo` (`Step6Pins.lean:323`,
unchanged), proved with `𝔠_d = 1/100`.  Premises used: `STFlow`, `0 ≤ s`, `s < t` (as `≤`), `t ≤ lemT z`, `STReg5IV`, `STLKU`,
`STExpAvgU`; unused: `STLK`, `STDecay`, `STExp2` at `s`, `STConStInd`, `STStep2Core`, `STLmaxU`, `STGdecayW … 0`. -/
theorem stExpDriftLo_holds (d : ℕ) : STExpDriftLo d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK hDec hExp hcon hS2 hLmax hLKU hGd hAvg
  exact STExpDriftLoConcl_of_LKU sz hd hκ hε hflow hs0 (fun n => (hst n).le) htT hR hLKU hAvg

end RBM.Gauss.Sizes

/-! ## 6. The decay `(deccA0)` of the drift `D_u` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- `W ≤ N` (`N = (W L)^d`, `L ≥ 1`, `d ≥ 1`). -/
private theorem expDr_W_le_size {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have h : sz.W n ≤ sz.size n :=
    calc sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
      _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
  exact_mod_cast h

/-- `𝓔^{G̃,(2)}` is the general-`n` term `ℰ^{G̃,(n)}` at the loop `(σ, a)` (`STEGtM_eq_STegtM`, `STegtM_seqHflow`). -/
private theorem expDr_EGt_eq_egt {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    sz.STEGt n E u σ a ω = sz.STegt n E u ω ⟨List.ofFn σ, List.ofFn a⟩ :=
  (STEGtM_eq_STegtM sz n E u _ σ a).trans (STegtM_seqHflow sz n E u ω _)

/-- `𝓔^{LK×LK,(2)}` is the general-`n` term at the loop `(σ, a)` (`STELKLKM_eq_STelklkM`, `STelklkM_seqHflow`). -/
private theorem expDr_ELKLK_eq_elklk {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    sz.STELKLK n E u σ a ω = sz.STelklk n E u ω ⟨List.ofFn σ, List.ofFn a⟩ :=
  (STELKLKM_eq_STelklkM sz n E u _ σ a).trans (STelklkM_seqHflow sz n E u ω _)

/-- The first moment with a `W^{-(D+1)}` level: `‖f‖ ≤ W^{-(D+1)}` off `S`, `‖f‖ ≤ N⁶` everywhere, `P(S) ≤ N^{-(D+7)}`,
`W ≤ N`: `‖𝔼 f‖ ≤ 2 W^{-(D+1)}`. -/
private theorem expDr_decay_step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℂ} {S : Set Ω} {N W D : ℝ} (hD : 0 ≤ D) (hN : 1 ≤ N) (hW : 0 < W) (hWN : W ≤ N)
    (hB : ∀ ω, ‖f ω‖ ≤ N ^ (6 : ℝ)) (hin : ∀ ω, ω ∉ S → ‖f ω‖ ≤ W ^ (-(D + 1)))
    (hP : (P S).toReal ≤ N ^ (-(D + 7))) : ‖∫ ω, f ω ∂P‖ ≤ 2 * W ^ (-(D + 1)) := by
  have hNpos : 0 < N := by linarith
  have hc : 0 ≤ W ^ (-(D + 1)) := Real.rpow_nonneg hW.le _
  have hfm := expDr_first_moment (P := P) (f := f) (S := S) (c := W ^ (-(D + 1))) (B := N ^ (6 : ℝ)) hc hB hin
  have htail : N ^ (6 : ℝ) * (P S).toReal ≤ W ^ (-(D + 1)) := by
    calc N ^ (6 : ℝ) * (P S).toReal ≤ N ^ (6 : ℝ) * N ^ (-(D + 7)) :=
          mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (-(D + 1)) := by rw [← Real.rpow_add hNpos]; congr 1; ring
      _ ≤ W ^ (-(D + 1)) := by
          refine Real.rpow_le_rpow_of_nonpos hW hWN ?_
          linarith
  calc ‖∫ ω, f ω ∂P‖ ≤ ∫ ω, ‖f ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ W ^ (-(D + 1)) + N ^ (6 : ℝ) * (P S).toReal := hfm
    _ ≤ W ^ (-(D + 1)) + W ^ (-(D + 1)) := add_le_add le_rfl htail
    _ = 2 * W ^ (-(D + 1)) := by ring

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`(deccA0)` for `D_u` from `STGdecayW … 0`**: `stDecayLoopU_of_step2 … 0` gives `STDecayLoopU`, `stEtermDecay … 2` (at
`(ε, D+1)`) gives, w.h.p., `|ℰ^{G̃}|, |ℰ^{LK×LK}| ≤ W^{-(D+1)}` for every `v ∈ [s_n,t_n]` and every far `a`; the first moment with the
envelope `N⁶` (`expDr_env_poly`) and `P ≤ N^{-(D+7)}` gives `|𝔼ℰ| ≤ 2 W^{-(D+1)}`, so `|D_v(a)| ≤ 4 W^{-(D+1)} ≤ W^{-D}` (`W ≥ 4`
eventually, `W ≤ N`).  The statement `STEKDecay` of the deterministic `D` is a `Whp` of a set that is eventually full.
The regime `STReg5I` is not used: the bound holds in every regime. -/
theorem STExpDriftDecayConcl_of_GdecayW {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hGd : STGdecayW sz (STflowE z) s t 0) :
    STExpDriftDecayConcl sz (STflowE z) s t := by
  have hsz := hz.1.2.2.1
  have hU := stDecayLoopU_of_step2 hd sz hκ hε hz hs0 hst htT 0 hGd
  have ht1 := st5_t_lt_one sz hz htT
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := st6_flowE_le sz hz
  have henv := expDr_env_poly sz hd hκ hε hz hs0 hst htT
  have hDE := fun σ : Fin 2 → Bool => stEtermDecay hd sz hκ hE hz.1 hs0 hst ht1 hU 2 le_rfl σ
  have hW4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
    have h1 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 𝔠 :=
      ((tendsto_rpow_atTop hz.1.1).comp hsz).eventually (eventually_ge_atTop 4)
    filter_upwards [h1, hz.1.2.2.2.1] with n h1 h2
    exact h1.trans h2
  intro σ ε' D hε' hD
  have hG1 := (hDE σ).1 ε' (D + 1) hε' (by linarith)
  have hG2 := (hDE σ).2.2.1 ε' (D + 1) hε' (by linarith)
  have hev : ∀ᶠ n in atTop, ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' D
        (fun a : Fin 2 → Zd d (sz.L n) => sz.STExpDrift n (STflowE z n) (v : ℝ) σ a) := by
    filter_upwards [hG1 (D + 7) (by linarith), hG2 (D + 7) (by linarith), henv, hW4,
      hsz.eventually (eventually_ge_atTop 1)] with n hP1 hP2 hEnv hW4n hN1
    intro v a hfar
    have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hWN := expDr_W_le_size sz hd n
    have hP1' : (sz.seqP {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' (D + 1)
        (fun a : Fin 2 → Zd d (sz.L n) => sz.STegt n (STflowE z n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩)}ᶜ).toReal ≤
        ((sz.size n : ℕ) : ℝ) ^ (-(D + 7)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (by linarith) _) hP1
    have hP2' : (sz.seqP {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' (D + 1)
        (fun a : Fin 2 → Zd d (sz.L n) => sz.STelklk n (STflowE z n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩)}ᶜ).toReal ≤
        ((sz.size n : ℕ) : ℝ) ^ (-(D + 7)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (by linarith) _) hP2
    have hE1 := expDr_decay_step (P := sz.seqP) (f := fun ω => sz.STEGt n (STflowE z n) (v : ℝ) σ a ω)
      (hD.le) hN hW0 hWN (fun ω => (hEnv (v, σ, a) ω).2.1)
      (fun ω hω => by
        have hω' : ω ∈ {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' (D + 1)
            (fun a : Fin 2 → Zd d (sz.L n) => sz.STegt n (STflowE z n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩)} := by
          simpa using hω
        rw [expDr_EGt_eq_egt]
        exact hω' v a hfar) hP1'
    have hE2 := expDr_decay_step (P := sz.seqP) (f := fun ω => sz.STELKLK n (STflowE z n) (v : ℝ) σ a ω)
      (hD.le) hN hW0 hWN (fun ω => (hEnv (v, σ, a) ω).1)
      (fun ω hω => by
        have hω' : ω ∈ {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' (D + 1)
            (fun a : Fin 2 → Zd d (sz.L n) => sz.STelklk n (STflowE z n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩)} := by
          simpa using hω
        rw [expDr_ELKLK_eq_elklk]
        exact hω' v a hfar) hP2'
    have hdr : sz.STExpDrift n (STflowE z n) (v : ℝ) σ a =
        (∫ ω, sz.STELKLK n (STflowE z n) (v : ℝ) σ a ω ∂(sz.seqP)) +
          ∫ ω, sz.STEGt n (STflowE z n) (v : ℝ) σ a ω ∂(sz.seqP) := rfl
    have hpow : ((sz.W n : ℕ) : ℝ) ^ (-D) = ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) * ((sz.W n : ℕ) : ℝ) := by
      have := Real.rpow_add hW0 (-(D + 1)) 1
      rw [Real.rpow_one] at this
      rw [← this]; congr 1; ring
    have hc : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hW0.le _
    change ‖sz.STExpDrift n (STflowE z n) (v : ℝ) σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)
    rw [hdr]
    calc _ ≤ ‖∫ ω, sz.STELKLK n (STflowE z n) (v : ℝ) σ a ω ∂(sz.seqP)‖ +
          ‖∫ ω, sz.STEGt n (STflowE z n) (v : ℝ) σ a ω ∂(sz.seqP)‖ := norm_add_le _ _
      _ ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) + 2 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) := add_le_add hE2 hE1
      _ = 4 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) := by ring
      _ ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) := mul_le_mul_of_nonneg_right hW4n hc
      _ = ((sz.W n : ℕ) : ℝ) ^ (-D) := by rw [hpow]; ring
  intro D' hD'
  filter_upwards [hev] with n hn
  have h0 : {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' D
      (fun a : Fin 2 → Zd d (sz.L n) => sz.STExpDrift n (STflowE z n) (v : ℝ) σ a)}ᶜ = (∅ : Set sz.SeqΩ) := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hn
  change sz.seqP _ ≤ _
  rw [h0, measure_empty]
  exact zero_le

/-- **`(deccA0)` for `D_u`** (`3_5:1634`): the merged pin `STExpDriftDecay` (`Step6Pins.lean:335`, unchanged), proved with
`𝔠_d = 1/100`.  Premises used: `STFlow`, `0 ≤ s`, `s < t` (as `≤`), `t ≤ lemT z`, `STGdecayW … 0`; unused: `STReg5I`, `STLK`,
`STDecay`, `STExp2`, `STConStInd`, `STStep2Core`, `STLmaxU`, `STLKU`. -/
theorem stExpDriftDecay_holds (d : ℕ) : STExpDriftDecay d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK hDec hExp hcon hS2 hLmax hLKU hGd
  exact STExpDriftDecayConcl_of_GdecayW sz hd hκ hε hflow hs0 (fun n => (hst n).le) htT hGd

end RBM.Gauss.Sizes

/-! ## 7. Instances (nonempty, nondegenerate data of the merged Step-6 instances)

Regime (iv): `szG` (`L = 4`, `W_n = n + 4`, `ilambda = 5`), flow `zB`, `(s,t) = (5/8, 3/4)`, `n = 0`: `N = 4096`; regime (i):
`szB`, `zB`, `(7/8, 15/16)`; the deterministic one-size lemmas at `sz0` (`n = 0`, `L = 4`, `W = 32`).  Every deterministic hypothesis is
discharged; what stays a hypothesis is a stochastic premise of a pin (`STLKU`, `STExpAvgU`, `STGdecayW … 0`, `STLK`, `STDecay`,
`STExp2`, `STStep2Core`, `STLmaxU`) or another gate's pin (`LWtermEXP`, `STExpDuhamelZ/Q`, `STExpWardI`, `STExpIntI`, `STExpIntIV`). -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path RBM.Loop Filter

/-- `stExpDriftLo_holds 3` at the data of regime (iv) (`szG`, `zB`, `[5/8, 3/4]`). -/
theorem inst_expDriftLo_holds :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) szG zB
      (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_expDriftLo (stExpDriftLo_holds 3)

/-- `stExpDriftDecay_holds 3` at the data of regime (i) (`szB`, `zB`, `[7/8, 15/16]`). -/
theorem inst_expDriftDecay_holds :
    InstIng6Concl (fun sz E s t => STExpDriftDecayConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_expDriftDecay (stExpDriftDecay_holds 3)

/-- The regime-(iv) skeleton with `hLo := stExpDriftLo_holds 3`: what remains are the other gates' pins. -/
theorem inst_skeleton6IV_Lo :
    STExpDuhamelZ 3 → STExpIntIV 3 →
      InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  fun hDu hInt => inst_skeleton6IV_avg hDu (stExpDriftLo_holds 3) hInt

/-- The regime-(i) skeleton with the merged route-A primed initial-term pin, `hLK := stExpLKLKHi_holds 3`,
`hAvg := stImproveExpAver_holds 3`, `hDec := stExpDriftDecay_holds 3`: open are only `LWtermEXP`, `STExpDuhamelZ/Q`, `STExpWardI`,
`STExpIntI`. -/
theorem inst_skeleton6I_Dec :
    LWtermEXP 3 → STExpDuhamelZ 3 → STExpDuhamelQ 3 → STExpWardI 3 → STExpIntI 3 →
      InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  fun hLW hDu hDuQ hWd hInt =>
    inst_skeleton6I' (stExpLKLKHi_holds 3) hLW (stImproveExpAver_holds 3) hDu hDuQ (stExpDriftDecay_holds 3) hWd hInt

/-- `expDr_Bctl_le_IV` at `szG`, `n = 0`, `u = 3/4` (`1 - u = 1/4 ≤ 25/64 = lam²/L³`). -/
theorem inst_expDr_Bctl_le_IV :
    szG.Bctl 0 (3 / 4) ≤ 2 * (((szG.size 0 : ℕ) : ℝ) * (1 - 3 / 4))⁻¹ :=
  expDr_Bctl_le_IV szG 0 (by norm_num) (by simp [szG, szB]; norm_num)

/-- `expDr_envEGt` at `sz0`, `n = 0`, `E = u = 1/2`, `σ = (+,-)`, `a = (0,0)`. -/
theorem inst_expDr_envEGt :
    ∀ ω : sz0.SeqΩ,
      ‖sz0.STEGt 0 (1 / 2) (1 / 2) ![true, false] ![(0 : Zd 3 (sz0.L 0)), 0] ω‖ ≤
        2 * (((sz0.W 0 : ℕ) : ℝ) ^ 3 * ((sz0.L 0 : ℕ) : ℝ) ^ 3) *
          (((etaT (1 / 2) (1 / 2))⁻¹ + 1) * (etaT (1 / 2) (1 / 2))⁻¹ ^ 3) :=
  fun ω => expDr_envEGt sz0 0 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num)
    ![true, false] ![0, 0] ω

/-- `expDr_EGt_split` at `sz0`, `n = 0`, `E = u = 1/2`, `σ = (+,-)`, `a = (0,0)`. -/
theorem inst_expDr_EGt_split :
    sz0.STExpEGt 0 (1 / 2) (1 / 2) ![true, false] ![(0 : Zd 3 (sz0.L 0)), 0] =
      expDrEGtK sz0 0 (1 / 2) (1 / 2) ![true, false] ![0, 0] +
        ∫ ω, expDrEGtLKM sz0 0 (1 / 2) (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) ![true, false] ![0, 0] ∂(sz0.seqP) :=
  expDr_EGt_split sz0 0 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num)
    ![true, false] ![0, 0]

/-- `expDr_env_poly` along `szG`, `zB`, `[5/8, 3/4]`. -/
theorem inst_expDr_env_poly :
    ∀ᶠ n in atTop, ∀ (p : STIdx2 szG (fun _ => 5 / 8) (fun _ => 3 / 4) n) (ω : szG.SeqΩ),
      ‖szG.STELKLK n (STflowE zB n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((szG.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
      ‖szG.STEGt n (STflowE zB n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((szG.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
      ‖expDrEGtLKM szG n (STflowE zB n) (p.1 : ℝ) (szG.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2‖ ≤
        ((szG.size n : ℕ) : ℝ) ^ (6 : ℝ) :=
  expDr_env_poly szG (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_zG
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num))

/-- `expDr_expect` for `𝓔^{LK×LK}` at `szG`, `zB`, `[5/8, 3/4]`, `Kenv = 6`, `Kf = 3`: the `≺` input stays a hypothesis. -/
theorem inst_expDr_expect
    (hprec : szG.Prec (U := STIdx2 szG (fun _ => 5 / 8) (fun _ => 3 / 4))
      (fun n p ω => ‖szG.STELKLK n (STflowE zB n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((szG.size n : ℕ) : ℝ) * (szG.Bctl n (p.1 : ℝ)) ^ 4)) :
    szG.Prec (U := STIdx2 szG (fun _ => 5 / 8) (fun _ => 3 / 4))
      (fun n p _ => ‖∫ ω, szG.STELKLK n (STflowE zB n) (p.1 : ℝ) p.2.1 p.2.2 ω ∂(szG.seqP)‖)
      (fun n p _ => ((szG.size n : ℕ) : ℝ) * (szG.Bctl n (p.1 : ℝ)) ^ 4) :=
  expDr_expect szG (V := STIdx2 szG (fun _ => 5 / 8) (fun _ => 3 / 4))
    (fun n p ω => szG.STELKLK n (STflowE zB n) (p.1 : ℝ) p.2.1 p.2.2 ω)
    (fun n p => ((szG.size n : ℕ) : ℝ) * (szG.Bctl n (p.1 : ℝ)) ^ 4) (Kenv := 6) (Kf := 3) flow_zG.1.2.2.1
    (inst_expDr_env_poly.mono fun n h p ω => (h p ω).1)
    (expDr_floor szG flow_zG.1.2.2.1 (fun _ => by norm_num) (fun _ => by norm_num)) hprec

/-- `expDr_LK_prec` at `szG`, `[5/8, 3/4]`: `STLKU` stays a hypothesis. -/
theorem inst_expDr_LK_prec (hLKU : STLKU szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4)) :
    szG.Prec (U := STIdx2 szG (fun _ => 5 / 8) (fun _ => 3 / 4))
      (fun n p ω => ‖szG.STELKLK n (STflowE zB n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((szG.size n : ℕ) : ℝ) * (szG.Bctl n (p.1 : ℝ)) ^ 4) :=
  expDr_LK_prec szG flow_zG.1.2.2.1 hLKU

/-- `expDr_EGtLK_prec` at `szG`, `[5/8, 3/4]`: `STLKU` stays a hypothesis. -/
theorem inst_expDr_EGtLK_prec (hLKU : STLKU szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4)) :
    szG.Prec (U := STIdx2 szG (fun _ => 5 / 8) (fun _ => 3 / 4))
      (fun n p ω => ‖expDrEGtLKM szG n (STflowE zB n) (p.1 : ℝ) (szG.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2‖)
      (fun n p _ => ((szG.size n : ℕ) : ℝ) * (szG.Bctl n (p.1 : ℝ)) ^ 4) :=
  expDr_EGtLK_prec szG flow_zG.1.2.2.1 hLKU

/-- `expDr_EGtK_prec` at `szG`, `zB`, `[5/8, 3/4]`: `STExpAvgU` stays a hypothesis. -/
theorem inst_expDr_EGtK_prec (hAvg : STExpAvgU szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4)) :
    szG.Prec (U := STIdx2 szG (fun _ => 5 / 8) (fun _ => 3 / 4))
      (fun n p _ => ‖expDrEGtK szG n (STflowE zB n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((szG.size n : ℕ) : ℝ) * (szG.Bctl n (p.1 : ℝ)) ^ 4) :=
  expDr_EGtK_prec szG (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_zG
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) hAvg

/-- `STExpDriftLoConcl_of_LKU` at `szG`, `zB`, `[5/8, 3/4]`: `STLKU` and `STExpAvgU` stay hypotheses. -/
theorem inst_STExpDriftLoConcl_of_LKU (hLKU : STLKU szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4))
    (hAvg : STExpAvgU szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4)) :
    STExpDriftLoConcl szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  STExpDriftLoConcl_of_LKU szG (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    flow_zG (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szG_reg4 hLKU hAvg

/-- `STExpDriftDecayConcl_of_GdecayW` at `szB`, `zB`, `[7/8, 15/16]`: `STGdecayW … 0` stays a hypothesis. -/
theorem inst_STExpDriftDecayConcl_of_GdecayW
    (hGd : STGdecayW szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) 0) :
    STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  STExpDriftDecayConcl_of_GdecayW szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    flow_zB (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) hGd

end RBM.Gauss.Step6Inst
