/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ExpIniI
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpDuhamel
import RBM3D.Induction.B45
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Induction.ConArgDet
import RBM3D.Loop.KLWard
import RBM3D.Loop.KLTree
import RBM3D.Loop.GLoopFlow
import RBM3D.Path.Walk

/-!
# The Ward terms of regime (i) (Step 6 of `lem:main_ind`)

Paper: Section 6 (`eq:EPL-K`, (6.11) `eq:boundELKQ1`, (6.12) `eq:boundcommutator`), with Ward's
identities (4.30) `eq:Ward_typeP` and (4.61) `A4`.

For `f_u = 𝔼(𝓛-𝒦)^{(2)}_u` (`STExpErr`), `σ₁ ≠ σ₂`, `u ∈ [s,t]` in regime (i) this file proves:
* `expWI_Psum_eq`: Ward's identity at the last label in expectation,
  `(𝒫 f_u)_{a₁} = (2iW^dη_u)⁻¹ ((𝔼𝓛^{(1)}_{+,a₁} - m) - (𝔼𝓛^{(1)}_{-,a₁} - m̄))` (pathwise
  `B45_ward_fin` at `m = 0`, integrated; `𝒦^{(1)} = m`);
* `expWI_Psum_prec`: `‖𝒫 f_u‖_∞ ≺ (W^dη_u)⁻¹ (W^{-d}B_{u,0})²` from (6.2) `res_ELK_n=1`
  (`STExpAvgU`);
* `expWI_window`, `expWI_vth_le`: regime (i) puts `ℓ_u = ilambda/√(1-u)` in `[1, L]`, so
  `‖ϑ_u‖_∞ ≤ C(e^{|c|d/2} + 2/d) ℓ_u^{-d}` for every real `c` (`B45_vth_mid` at `m = 1`);
* `expWI_core`, `expWI_concl_prime`: the conclusions `STExpWardIConcl` (every real `C, c`) and
  `STExpWardIConcl'` (`0 < C`, `0 < c`), from the flow, regime (i) and (6.2) `res_ELK_n=1` alone;
* `stExpWardI_holds : STExpWardI d` (`Step6Pins.lean`) and `stExpWardI'_holds : STExpWardI' d`.

The proof does not use `c` (only through `B45_vth_mid`) nor `0 < C`.  `expWI_scale` is the first
conjunct of `B45_scales`, `expWI_pw` the pathwise Ward identity at the last label.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Ward's identity at the last label in expectation -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

private theorem expWI_integrable_Lloop (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) :
    Integrable (fun ω => Lloop sz n E u σ a ω) sz.seqP :=
  Integrable.of_bound (walk_measurable_Lloop sz n E u σ a).aestronglyMeasurable ((etaT E u)⁻¹ ^ (k + 1))
    (Filter.Eventually.of_forall fun ω => norm_Lloop_le sz n hE hu σ a ω)

private theorem expWI_integrable_LK (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) {m : ℕ}
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
    Integrable (fun ω => STLKtensor sz n E u ω σ a) sz.seqP :=
  (expWI_integrable_Lloop sz n hE hu σ a).sub (integrable_const _)

/-- `𝔼(𝓛-𝒦)^{(m+1)} = 𝔼𝓛^{(m+1)} - 𝒦^{(m+1)}`: the integral of the `𝒦`-part is itself (probability measure). -/
private theorem expWI_int_LK (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) {m : ℕ}
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
    ∫ ω, STLKtensor sz n E u ω σ a ∂sz.seqP =
      (∫ ω, Lloop sz n E u σ a ω ∂sz.seqP) - STKloop sz n E u σ a := by
  unfold STLKtensor
  rw [integral_sub (expWI_integrable_Lloop sz n hE hu σ a) (integrable_const _)]
  simp

private theorem expWI_int_Psum (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a₁ : Zd d (sz.L n)) :
    ∫ ω, STPsum (d := d) (STLKtensor sz n E u ω σ) a₁ ∂sz.seqP =
      STPsum (d := d) (fun b => STExpErr sz n E u σ b) a₁ := by
  unfold STPsum
  rw [integral_finsetSum _ (fun a _ => expWI_integrable_LK sz n hE hu σ a)]
  exact Finset.sum_congr rfl fun a _ => expWI_int_LK sz n hE hu σ a

private theorem expWI_sgnCons (b : Bool) (σ : Fin 2 → Bool) :
    B45_sgnCons (m := 0) b σ = fun _ => b := by
  funext i; fin_cases i; simp [B45_sgnCons]

/-- Pathwise Ward at the last label for `σ₁ ≠ σ₂`, in terms of `𝒫`. -/
private theorem expWI_pw (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : sz.SeqΩ)
    (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a₁ : Zd d (sz.L n)) :
    STPsum (d := d) (STLKtensor sz n E u ω σ) a₁ =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (STLKtensor sz n E u ω (fun _ : Fin 1 => true) (fun _ => a₁) -
          STLKtensor sz n E u ω (fun _ : Fin 1 => false) (fun _ => a₁)) := by
  have hlast : σ (Fin.last (0 + 1)) = !σ 0 := by
    have : Fin.last (0 + 1) = (1 : Fin 2) := rfl
    rw [this]
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all
  have hw := B45_ward_fin sz n hE hu0 hu1 ω (m := 0) σ hlast (fun _ => a₁)
  rw [B45_Psum_snoc]
  have hfil : Finset.univ.filter (fun a' : Fin (0 + 1) → Zd d (sz.L n) => a' 0 = a₁) = {fun _ => a₁} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext i; fin_cases i; exact h
    · intro h; rw [h]
  rw [hfil, Finset.sum_singleton, hw, expWI_sgnCons, expWI_sgnCons]

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **Ward's identity in expectation** (`eq:EPL-K`, (2.56) `WI_calL`, (2.57) `WI_calK`; `𝒦^{(1)} = m`):
`σ₁ ≠ σ₂`, `(𝒫 f_u)_{a₁} = (2iW^dη_u)⁻¹ ((𝔼𝓛^{(1)}_{+,a₁} - m) - (𝔼𝓛^{(1)}_{-,a₁} - m̄))`. -/
theorem expWI_Psum_eq {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a₁ : Zd d (sz.L n)) :
    STPsum (d := d) (fun b => STExpErr sz n E u σ b) a₁ =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (((∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a₁) ω ∂(sz.seqP)) - mSigma E true) -
          ((∫ ω, Lloop sz n E u (fun _ : Fin 1 => false) (fun _ => a₁) ω ∂(sz.seqP)) - mSigma E false)) := by
  rw [← expWI_int_Psum sz n hE hu1 σ a₁]
  simp only [expWI_pw sz n hE hu0 hu1 _ σ hσ a₁]
  rw [integral_const_mul, integral_sub (expWI_integrable_LK sz n hE hu1 _ _) (expWI_integrable_LK sz n hE hu1 _ _)]
  congr 2
  · rw [expWI_int_LK sz n hE hu1, lemDecCalEPrec_STKloop_one]
  · rw [expWI_int_LK sz n hE hu1, lemDecCalEPrec_STKloop_one]

end RBM.Gauss.Sizes

/-! ## 2. `‖𝒫 f_u‖_∞` from (6.2) `res_ELK_n=1` uniformly in `u` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`‖𝒫 f_u‖_∞ ≺ (W^dη_u)⁻¹ (W^{-d}B_{u,0})²`** uniformly in `u ∈ [s,t]`, `σ₁ ≠ σ₂`, `a₁`: Ward's identity in expectation
(`expWI_Psum_eq`) with `‖(2iW^dη)⁻¹‖ = (2W^dη)⁻¹` and (6.2) `res_ELK_n=1` (`STExpAvgU`) for both signs.  No regime, no mollifier. -/
theorem expWI_Psum_prec {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hAvg : STExpAvgU sz (STflowE z) s t) :
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
      (fun n q _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (STflowE z n) (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 2) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  have hA := (st6_prec_det_iff sz hsz _ _).1 hAvg τ hτ
  filter_upwards [hA] with n hn
  rintro ⟨⟨u, hu⟩, ⟨σ, hσ⟩, a⟩
  have hE := st6_flowE_lt_two sz hκ hflow n
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (st5_t_lt_one sz hflow htT n)
  have h1 := hn ⟨⟨u, hu⟩, true, a⟩
  have h2 := hn ⟨⟨u, hu⟩, false, a⟩
  simp only at h1 h2 ⊢
  rw [expWI_Psum_eq sz n hE hu0 hu1 σ hσ a, norm_mul, B45_norm_kappa sz n hE hu1]
  have hd0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d * etaT (STflowE z n) u := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact mul_pos (by positivity) (etaT_pos hE hu1)
  have hsub := norm_sub_le ((∫ ω, Lloop sz n (STflowE z n) u (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP)) -
      mSigma (STflowE z n) true)
    ((∫ ω, Lloop sz n (STflowE z n) u (fun _ : Fin 1 => false) (fun _ => a) ω ∂(sz.seqP)) -
      mSigma (STflowE z n) false)
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT (STflowE z n) u))⁻¹ * ‖_ - _‖
      ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT (STflowE z n) u))⁻¹ *
        (((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u) ^ 2 + ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsub.trans (add_le_add h1 h2)) (by positivity)
    _ = _ := by rw [mul_inv]; field_simp; ring

end RBM.Gauss.Sizes

/-! ## 3. Regime (i) puts every `u ∈ [s_n, t_n]` in the window `1 ≤ ℓ_u ≤ L`; the mollifier size for every real `c` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- Regime (i) `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²` puts every `u ∈ [s_n, t_n]` in the window
`1 ≤ ilambda/√(1-u) ≤ L` (so `ℓ_u = ilambda/√(1-u)`), when `ilambda > 0`. -/
theorem expWI_window {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (hR : STReg5I sz s t) (n : ℕ) (u : ℝ)
    (hsu : s n ≤ u) (hut : u ≤ t n) (hlam : 0 < sz.lam n) :
    1 ≤ sz.lam n / Real.sqrt (1 - u) ∧ sz.lam n / Real.sqrt (1 - u) ≤ ((sz.L n : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := hR n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hv : 0 < 1 - u := by
    have : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  have hsq : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hv
  constructor
  · rw [le_div_iff₀ hsq, one_mul, Real.sqrt_le_left hlam.le]
    nlinarith
  · rw [div_le_iff₀ hsq]
    have hle : sz.lam n ^ 2 ≤ (((sz.L n : ℕ) : ℝ) * Real.sqrt (1 - u)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hv.le]
      rw [div_le_iff₀ (by positivity)] at h1
      nlinarith
    exact (pow_le_pow_iff_left₀ hlam.le (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hle

/-- **`‖ϑ_u‖_∞ ≤ C(e^{|c|d/2} + 2/d) ℓ_u^{-d}`** in the window `1 ≤ g/√(1-u) ≤ L`, for every real `c`
(`B45_vth_mid` at `m = 1`). -/
theorem expWI_vth_le {d L : ℕ} [NeZero L] {g C c : ℝ} (ϑ : ℝ → (Fin 2 → Zd d L) → ℂ) (hd : 1 ≤ d) (hL : 3 ≤ L)
    (hg : 0 < g) (hϑ : STMollifierProps (d := d) g C c ϑ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hx1 : 1 ≤ g / Real.sqrt (1 - u)) (hxL : g / Real.sqrt (1 - u) ≤ (L : ℝ)) (a : Fin 2 → Zd d L) :
    ‖ϑ u a‖ ≤ (C * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * C / (d : ℝ)) * ((ellT L g u) ^ d)⁻¹ := by
  have h := B45_vth_mid (m := 1) hL hg hϑ (by omega) hu0 hu1 hx1 hxL a
  simpa [mul_one, pow_one] using h

end RBM.Gauss.Sizes

/-! ## 4. The deterministic bound at one `(n, u, σ)` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- `(W^dη_u)⁻¹ ℓ_u^{-d} ≤ 2Γ W^{-d}B_{u,0}`, `Γ = 2/√(2κ) ≥ (Im m)⁻¹` (`B45_scale`: `(ℓ_u^d (1-u))⁻¹ ≤ 2 B_{u,0}` for every
`u < 1`, `d ≥ 2`; `η_u = (1-u) Im m`, `Im m ≥ √(2κ)/2`).  The first conjunct of `B45_scales` without its
unused hypothesis `N⁻¹ ≤ 1-u`. -/
private theorem expWI_scale {d : ℕ} (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu1 : u < 1) (hg : 0 < sz.lam n) :
    (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ≤
      2 * (2 / Real.sqrt (2 * κ)) * sz.Bctl n u := by
  have hv : 0 < 1 - u := by linarith
  have hsqκ : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.mpr (by linarith)
  have hμ : Real.sqrt (2 * κ) / 2 ≤ (mE E).im := st6_mE_im_ge hκ hE
  have hsc := B45_scale (d := d) (L := sz.L n) hd (by have := sz.three_le_L n; omega) hg hu1
  have h1 : (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((mE E).im)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹) := by
    unfold etaT
    simp only [mul_inv]
    ring
  rw [h1]
  have hΓ : ((mE E).im)⁻¹ ≤ 2 / Real.sqrt (2 * κ) := by
    calc ((mE E).im)⁻¹ ≤ (Real.sqrt (2 * κ) / 2)⁻¹ := inv_anti₀ (by positivity) hμ
      _ = 2 / Real.sqrt (2 * κ) := by field_simp
  have hΓ0 : 0 ≤ 2 / Real.sqrt (2 * κ) := by positivity
  unfold Sizes.Bctl
  have hpos : 0 ≤ (ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹ := by
    have := ellT_pos (L := sz.L n) (g := sz.lam n) (t := u) (by
      have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n))
    positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((mE E).im)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 / Real.sqrt (2 * κ)) * (2 * Bparam d (sz.L n) (sz.lam n) u 0) := by
        gcongr
    _ = 2 * (2 / Real.sqrt (2 * κ)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0) := by ring

/-- **The two Ward bounds at one point.**  For `σ₁ ≠ σ₂`, `‖𝒫 f_u‖_∞ ≤ Y (W^dη_u)⁻¹ (W^{-d}B_{u,0})²`, a mollifier with
`‖ϑ_u‖_∞ ≤ K ℓ_u^{-d}` and `‖∂_uϑ_u‖_∞ ≤ C(1-u)⁻¹ℓ_u^{-d}`, and the scale `(W^dη_u)⁻¹ℓ_u^{-d} ≤ 2Γ W^{-d}B_{u,0}`:
(6.9) `eq:EPL-K`: `‖(𝒫f_u)_{a₁} ϑ_{u,a}‖ ≤ 2ΓK Y B³`;
(6.12) `eq:boundcommutator` + (6.11) `eq:boundELKQ1`: `‖[𝒬_u, Θ^{(2)}_{u,σ}] f_u‖ + ‖(𝒫f_u)_{a₁} ∂_uϑ_u‖ ≤ (1-u)⁻¹ 2Γ(4K + C) Y B³`
(`B45_B4_le` at `m = 1`, `Θ^{(2)} = ThetaN`, `‖m(σ_i)‖ = 1`). -/
private theorem expWI_pt {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {C K Γ Y : ℝ} (hY : 0 ≤ Y) (hΓ : 0 ≤ Γ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ}
    (hvs : ∀ a, ‖ϑ u a‖ ≤ K * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹))
    (hdv : ∀ a, ‖deriv (fun τ => ϑ τ a) u‖ ≤ C * (1 - u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹))
    (hsc : (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ≤ 2 * Γ * sz.Bctl n u)
    (σ : Fin 2 → Bool)
    (hP : ∀ b₁, ‖STPsum (d := d) (fun b => STExpErr sz n E u σ b) b₁‖ ≤
      Y * ((((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ * (sz.Bctl n u) ^ 2))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖STPsum (d := d) (fun b => STExpErr sz n E u σ b) (a 0) * ϑ u a‖ ≤ Y * (2 * Γ * K) * (sz.Bctl n u) ^ 3 ∧
    ‖STQop (d := d) ϑ u (STthetaOp sz n E u σ (fun c => STExpErr sz n E u σ c)) a -
        STthetaOp sz n E u σ (STQop (d := d) ϑ u (fun c => STExpErr sz n E u σ c)) a‖ +
      ‖STPsum (d := d) (fun b => STExpErr sz n E u σ b) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
      (1 - u)⁻¹ * (Y * (2 * Γ * (4 * K + C)) * (sz.Bctl n u) ^ 3) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hP0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ := by positivity
  have hB0 : 0 ≤ sz.Bctl n u := (STBctl_pos sz n hu1).le
  have hv0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have hLz : 0 ≤ ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) := by
    have := ellT_pos (L := sz.L n) (g := sz.lam n) (t := u) (by
      have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n))
    positivity
  set P0 : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ with hP0def
  set Lz : ℝ := ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) with hLzdef
  set B : ℝ := sz.Bctl n u with hBdef
  set Pa : ℝ := ‖STPsum (d := d) (fun b => STExpErr sz n E u σ b) (a 0)‖ with hPa
  have hPa' : Pa ≤ Y * (P0 * B ^ 2) := hP (a 0)
  have hPi0 : 0 ≤ Y * (P0 * B ^ 2) := by positivity
  constructor
  · calc ‖STPsum (d := d) (fun b => STExpErr sz n E u σ b) (a 0) * ϑ u a‖ = Pa * ‖ϑ u a‖ := norm_mul _ _
      _ ≤ (Y * (P0 * B ^ 2)) * (K * Lz) := mul_le_mul hPa' (hvs a) (norm_nonneg _) hPi0
      _ = Y * K * B ^ 2 * (P0 * Lz) := by ring
      _ ≤ Y * K * B ^ 2 * (2 * Γ * B) := by gcongr
      _ = Y * (2 * Γ * K) * B ^ 3 := by ring
  · have hθ : ∀ A, STthetaOp sz n E u σ A = ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u A :=
      fun A => funext (STthetaOp_eq_ThetaN sz n E u σ A)
    have hB4 := B45_B4_le (m := 1) (d := d) (L := sz.L n) (sz.lam n) (sz.three_le_L n)
      (μs := fun i => mSigma E (σ i)) (fun i => norm_mSigma hE.le _) hu0 hu1 ϑ
      (fun b => STExpErr sz n E u σ b) (Pi := Y * (P0 * B ^ 2)) (vs := K * Lz) hP hvs a
    simp only [hθ]
    have h2 : ‖STPsum (d := d) (fun b => STExpErr sz n E u σ b) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
        (Y * (P0 * B ^ 2)) * (C * (1 - u)⁻¹ * Lz) := by
      rw [norm_mul]
      exact mul_le_mul hPa' (hdv a) (norm_nonneg _) hPi0
    have hn2 : 2 * (((1 + 1 : ℕ) : ℝ)) = 4 := by norm_num
    rw [hn2] at hB4
    calc _ ≤ 4 * (1 - u)⁻¹ * ((Y * (P0 * B ^ 2)) * (K * Lz)) + (Y * (P0 * B ^ 2)) * (C * (1 - u)⁻¹ * Lz) := by
          linarith
      _ = (1 - u)⁻¹ * (Y * (4 * K + C) * B ^ 2 * (P0 * Lz)) := by ring
      _ ≤ (1 - u)⁻¹ * (Y * (4 * K + C) * B ^ 2 * (2 * Γ * B)) := by gcongr
      _ = (1 - u)⁻¹ * (Y * (2 * Γ * (4 * K + C)) * B ^ 3) := by ring

end RBM.Gauss.Sizes

/-! ## 5. The statements with positive mollifier constants and the core theorems -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- `STExpWardIConcl` (`Step6Pins.lean`) with `0 < C → 0 < c →` after `∀ (C c : ℝ)` (the paper's mollifier has
`c > 0`, Definition 4.7 `Def:QtPt`; the consumer's family `st6_mollifier_family` has `0 < C`, `0 < c`). -/
def STExpWardIConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3) ∧
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ =>
        ‖STQop (d := d) (ϑ n) (q.1 : ℝ) (STthetaOp sz n (E n) (q.1 : ℝ) q.2.1.1
            (fun c => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 c)) q.2.2 -
          STthetaOp sz n (E n) (q.1 : ℝ) q.2.1.1
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (fun c => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 c)) q.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
          deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)

/-- The statement `STExpWardI'`: the shape `STIngR6` of `STExpWardI` (`Step6Pins.lean`) with `STExpWardIConcl'`. -/
def STExpWardI' (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl' sz E s t)

/-- The constant of (6.9) `eq:EPL-K`: `2Γ K_c`, `Γ = 2/√(2κ) ≥ (Im m)⁻¹`, `K_c = C e^{|c|d/2} + 2C/d`. -/
private def expWI_K1 (d : ℕ) (κ C c : ℝ) : ℝ :=
  2 * (2 / Real.sqrt (2 * κ)) * (C * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * C / (d : ℝ))

/-- The constant of (6.12) `eq:boundcommutator` + (6.11) `eq:boundELKQ1`: `2Γ (4K_c + C)`. -/
private def expWI_K2 (d : ℕ) (κ C c : ℝ) : ℝ :=
  2 * (2 / Real.sqrt (2 * κ)) * (4 * (C * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * C / (d : ℝ)) + C)

/-- The two bounds at one index `(n, q)` of regime (i): the inputs are the Ward bound `‖𝒫 f_u‖ ≤ N^{τ/2} (W^dη_u)⁻¹B²`
(`expWI_Psum_prec`), the window, the mollifier at size `n`, and the constants `≤ N^{τ/2}`. -/
private theorem expWI_step {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) (z : ℕ → ℂ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5I sz s t) {C c τ : ℝ} (hτ : 0 < τ) (n : ℕ) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hl : 0 < sz.lam n) (hm : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (hK1 : expWI_K1 d κ C c ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hK2 : expWI_K2 d κ C c ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hn : ∀ v : TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n),
      ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (v.1 : ℝ) v.2.1.1 b) v.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.W n : ℕ) : ℝ) ^ d * etaT (STflowE z n) (v.1 : ℝ))⁻¹ * (sz.Bctl n (v.1 : ℝ)) ^ 2))
    (q : TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) :
    ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) * ϑ (q.1 : ℝ) q.2.2‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n (q.1 : ℝ)) ^ 3 ∧
    ‖STQop (d := d) ϑ (q.1 : ℝ) (STthetaOp sz n (STflowE z n) (q.1 : ℝ) q.2.1.1
        (fun c => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 c)) q.2.2 -
      STthetaOp sz n (STflowE z n) (q.1 : ℝ) q.2.1.1
        (STQop (d := d) ϑ (q.1 : ℝ) (fun c => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 c)) q.2.2‖ +
    ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
      deriv (fun τ => ϑ τ q.2.2) (q.1 : ℝ)‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3) := by
  obtain ⟨⟨u, hu⟩, ⟨σ, hσ⟩, a⟩ := q
  have hE := st6_flowE_lt_two sz hκ hflow n
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (st5_t_lt_one sz hflow htT n)
  have hL3 := sz.three_le_L n
  have hC := B45_C_nonneg hL3 hl hm
  have hKc : 0 ≤ C * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * C / (d : ℝ) := by positivity
  have hΓ : 0 ≤ 2 / Real.sqrt (2 * κ) := by positivity
  obtain ⟨hx1, hxL⟩ := expWI_window sz s t hR n u hu.1 hu.2 hl
  have hvs := fun b => expWI_vth_le ϑ (by omega) hL3 hl hm u hu0 hu1 hx1 hxL b
  have hdv : ∀ b, ‖deriv (fun τ => ϑ τ b) u‖ ≤ C * (1 - u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) := fun b => by
    simpa using hm.2.2.2 u hu0 hu1 b
  have hsc := expWI_scale (by omega : 2 ≤ d) sz n hκ (st6_flowE_le sz hflow n) hu1 hl
  have hY : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hP : ∀ b₁, ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) u σ b) b₁‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
        ((((sz.W n : ℕ) : ℝ) ^ d * etaT (STflowE z n) u)⁻¹ * (sz.Bctl n u) ^ 2) :=
    fun b₁ => hn ⟨⟨u, hu⟩, ⟨σ, hσ⟩, b₁⟩
  obtain ⟨h1, h2⟩ := expWI_pt sz n hE hu0 hu1 hY hΓ hKc hC hvs hdv hsc σ hP a
  have hB3 : 0 ≤ (sz.Bctl n u) ^ 3 := by have := (STBctl_pos sz n hu1).le; positivity
  have hv0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have hYY : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ :=
    UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ
  constructor
  · calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (2 * (2 / Real.sqrt (2 * κ)) *
          (C * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * C / (d : ℝ))) * (sz.Bctl n u) ^ 3 := h1
      _ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * expWI_K1 d κ C c * (sz.Bctl n u) ^ 3 := rfl
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 3 := by gcongr
      _ = _ := by rw [hYY]
  · calc _ ≤ (1 - u)⁻¹ * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (2 * (2 / Real.sqrt (2 * κ)) *
          (4 * (C * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * C / (d : ℝ)) + C)) * (sz.Bctl n u) ^ 3) := h2
      _ = (1 - u)⁻¹ * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * expWI_K2 d κ C c * (sz.Bctl n u) ^ 3) := rfl
      _ ≤ (1 - u)⁻¹ * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 3) := by
          gcongr
      _ = _ := by rw [← hYY]; ring

/-- **The Ward terms of regime (i), every real `C, c`** (`eq:EPL-K`, (6.11) `eq:boundELKQ1`, (6.12) `eq:boundcommutator`):
from the flow, regime (i) and (6.2) `res_ELK_n=1` (`STExpAvgU`) alone.  Neither `0 < C` nor `0 < c` is used (`c` enters only through
`‖ϑ_u‖_∞ ≤ C(e^{|c|d/2} + 2/d) ℓ_u^{-d}`, `expWI_vth_le`). -/
theorem expWI_core {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hAvg : STExpAvgU sz (STflowE z) s t) :
    STExpWardIConcl sz (STflowE z) s t := by
  intro C c ϑ hϑ
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hPrec := expWI_Psum_prec hd hκ hε h𝔡 sz z hflow s t hs0 htT hAvg
  have hlam := st6_lam_pos sz hflow.1.2.2.2.2
  refine ⟨(st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_, (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_⟩
  all_goals
    have hA := (st6_prec_det_iff sz hsz _ _).1 hPrec (τ / 2) (half_pos hτ)
    filter_upwards [hA, hlam, hϑ, (tendsto_size sz hsz).eventually (eventually_le_rpow (expWI_K1 d κ C c) (half_pos hτ)),
      (tendsto_size sz hsz).eventually (eventually_le_rpow (expWI_K2 d κ C c) (half_pos hτ))] with n hn hl hm hK1 hK2 q
  · exact (expWI_step hd hκ sz z hflow s t hs0 htT hR hτ n (ϑ n) hl hm hK1 hK2 hn q).1
  · exact (expWI_step hd hκ sz z hflow s t hs0 htT hR hτ n (ϑ n) hl hm hK1 hK2 hn q).2

/-- The unsigned conclusion implies `STExpWardIConcl'` (the extra hypotheses `0 < C`, `0 < c` are dropped). -/
theorem expWI_concl_prime {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (h : STExpWardIConcl sz E s t) :
    STExpWardIConcl' sz E s t :=
  fun C c _ _ ϑ hϑ => h C c ϑ hϑ

/-- **`STExpWardI` (`Step6Pins.lean`), proved** (`𝔠_d = 1/100`: no premise of `STIngR6` beyond `STReg5I` and
`STExpAvgU` is used). -/
theorem stExpWardI_holds (d : ℕ) : STExpWardI d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR _ _ _ _ _ _ _ _ hAvg
  exact expWI_core hd hκ hε h𝔡 sz z hflow s t hs0 hst htT hR hAvg

/-- **`STExpWardI'`, proved** (from `STExpWardI`, `expWI_concl_prime`). -/
theorem stExpWardI'_holds (d : ℕ) : STExpWardI' d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨𝔠d, h0, h1, H⟩ := stExpWardI_holds d hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨𝔠d, h0, h1, fun 𝔠 sz z hflow s t hs0 hst htT hR hLK hDec hExp hcon hS2 hLmax hLKU hS5 hAvg =>
    expWI_concl_prime sz _ s t (H 𝔠 sz z hflow s t hs0 hst htT hR hLK hDec hExp hcon hS2 hLmax hLKU hS5 hAvg)⟩

end RBM.Gauss.Sizes
