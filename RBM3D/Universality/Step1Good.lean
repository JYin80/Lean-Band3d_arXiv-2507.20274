/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.PinsDens
import RBM3D.Universality.InjSum

/-!
# `RBM3D.Universality.Step1Good` (UN-12): the Step-1 regularity event against an abstract density

Ticket T2208.  Proves the owed pin `UNStep1Good'` (`PinsDens.lean:73`, statement unchanged) as the
theorem `step1Good'`, from the local law `UNTrLocal`, the norm bound `UNNormBound`, the density
hypothesis `UNDens'` and target 4 of T2190 (`freeConv_stable_lip`, `FreeConvRegular.lean:1234`).

Port of RBM2D `Universality/Step1RegularityB.lean` (commit `c9a24cf`, 906 lines): sections 1, 2, 5,
6, 8, 9, 10, 11 (elementary facts on `a = e^{-T/2}`, `t = 1 - e^{-T}`; the eigenvalue dictionary;
the domain of the event; the regularity part; the strip; the deterministic half; the probability
bound).
Replaced: the band event `Step1LocalEvent` by the complements of the bad sets of `UNTrLocal` and
`UNNormBound`; `msc` by `m n` (bounds from the `UNDens'` box); `Meta ≥ min(W², Nη)` by `un_Bctl_le`
and `un_step1_floor`; `freeConv_stable_local` (error `C₀ ε`) by `freeConv_stable_lip` (error
`C₀ (ε + t)`); `rhoSC E₀` by `ρ n`; `CV = 2` by `CV₀ + 1`; `τs ≤ 𝔠` by `τs ≤ 𝔠𝔡`.  Not ported: RBM2D
sections 3, 4, 7 and the instance.

Sections: 1 the eigenvalue dictionary; 2 what `Admissible` says about `𝔠`, `𝔡` (the `d ≥ 3`
bookkeeping); 3 elementary facts on `a`, `t`; 4 the strip and the regularity part at one `n`; 5 the
deterministic half and the pin; 6 compiled nonempty instances (`Step1GoodInst`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

/-! ## 1. The eigenvalue dictionary and elementary bounds on `mV` -/

/-- Spectral decomposition of the Green's function `(H - z)⁻¹` (RBM2D `Delocalization.lean:47`,
`green_eq_spectral`, commit `c9a24cf`; copy of the private `InjSum_green_eq_spectral`, `InjSum.lean:43`). -/
private theorem Step1Good_green_eq_spectral {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) :
    green H z = (hH.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)
      * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun l => (hH.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hz1 : (z • 1 : Matrix n n ℂ) = U * diagonal (fun _ => z) * star U := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU']
  have hsub : H - z • 1 = U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U := by
    rw [hz1]
    conv_lhs => rw [hspec]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U
        * (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹) * star U)
      = U * (diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * (star U * U)
          * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => ((hH.eigenvalues l : ℂ) - z) * ((hH.eigenvalues l : ℂ) - z)⁻¹)
            = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

/-- **Target 1a** `stieltjesN_eq_mV`: the spectral formula `N⁻¹ tr (H - z)⁻¹ = mV λ(H) z`
(RBM2D `Step1RegularityB_stieltjesN_eq_mV`, `Universality/Step1RegularityB.lean:129` at `c9a24cf`). -/
theorem stieltjesN_eq_mV :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ},
      0 < z.im → stieltjesN H z = mV hH.eigenvalues z := by
  intro ι _ _ H hH z hz
  have hzne : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := fun l h => by
    have h2 : (0 : ℝ) = z.im := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  rw [InjSum_stieltjesN_eq_stieltjes]
  unfold InjSum_stieltjes mV
  congr 1
  rw [Step1Good_green_eq_spectral hH hzne]
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  rw [Matrix.trace_mul_comm (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) (star U),
    ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]

private theorem Step1Good_inv_mul_re (a : ℝ) (X : ℂ) :
    (((a : ℝ) : ℂ)⁻¹ * X).re = a⁻¹ * X.re := by
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]

private theorem Step1Good_inv_mul_im (a : ℝ) (X : ℂ) :
    (((a : ℝ) : ℂ)⁻¹ * X).im = a⁻¹ * X.im := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]

/-- The affine dictionary: `m_V(w) = a⁻¹ m_N(a⁻¹ (w + E₀))` for `v_i = a λ_i - E₀`, `a > 0`
(RBM2D `Step1RegularityB_mV_vOU`, `:147`). -/
private theorem Step1Good_mV_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {a : ℝ} (ha : 0 < a) (E₀ : ℝ) {w : ℂ}
    (hw : 0 < w.im) :
    mV (fun i => a * hH.eigenvalues i - E₀) w =
      ((a : ℝ) : ℂ)⁻¹ * stieltjesN H (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) := by
  have hz : 0 < (((a : ℝ) : ℂ)⁻¹ * (w + E₀)).im := by
    rw [Step1Good_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
    positivity
  rw [stieltjesN_eq_mV hH hz]
  unfold mV
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set lami : ℝ := hH.eigenvalues i with hlam_def
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hkey : ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w =
      (a : ℂ) * ((lami : ℂ) - (((a : ℝ) : ℂ)⁻¹ * (w + E₀))) := by
    rw [mul_sub]
    rw [show (a : ℂ) * (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) = w + E₀ by field_simp]
    ring
  rw [show ((a * lami - E₀ : ℝ) : ℂ) - w = ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w by push_cast; ring,
    hkey, mul_inv]

/-- **Target 1b** `mV_vOU`: the affine dictionary of Step 1, `mV v (w) = a⁻¹ m_N(a⁻¹ (w + E))`,
`a = e^{-t*/2}`, for `v = vOU = a λ(H) - E` (RBM2D `Step1RegularityB_mV_vOU`, `:147`). -/
theorem mV_vOU :
    ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τs E : ℝ) (ω : Sizes.SeqΩ sz) {w : ℂ}, 0 < w.im →
      mV (vOU sz M n τs E ω) w =
        ((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ *
          stieltjesN (M.H n ω) (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E)) := by
  intro d sz M n τs E ω w hw
  exact Step1Good_mV_affine (M.herm n ω) (Real.exp_pos _) E hw

/-- The imaginary part of one term `((a : ℂ) - (x + iη))⁻¹`. -/
private theorem Step1Good_term_im (a x η : ℝ) (_hη : 0 < η) :
    (((a : ℂ) - (⟨x, η⟩ : ℂ))⁻¹).im = η / ((a - x) ^ 2 + η ^ 2) := by
  have hn : Complex.normSq ((a : ℂ) - (⟨x, η⟩ : ℂ)) = (a - x) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [Complex.inv_im, hn]
  simp

/-- `Im mV v (x + iη) = N⁻¹ ∑ η / ((v_i - x)² + η²)`. -/
private theorem Step1Good_mV_im {ι : Type*} [Fintype ι] (v : ι → ℝ) (x η : ℝ) (hη : 0 < η) :
    (mV v ⟨x, η⟩).im = (Fintype.card ι : ℝ)⁻¹ * ∑ i, η / ((v i - x) ^ 2 + η ^ 2) := by
  unfold mV
  have e : ((Fintype.card ι : ℂ)⁻¹) = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [e, Complex.im_ofReal_mul, Complex.im_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Step1Good_term_im (v i) x η hη

/-- **Target 1c** `mV_eta_mul_im_mono`: `η ↦ η Im mV v (x + iη)` is nondecreasing. -/
theorem mV_eta_mul_im_mono :
    ∀ {ι : Type*} [Fintype ι] (v : ι → ℝ) (x η η' : ℝ), 0 < η → η ≤ η' →
      η * (mV v ⟨x, η⟩).im ≤ η' * (mV v ⟨x, η'⟩).im := by
  intro ι _ v x η η' hη hηη'
  have hη' : 0 < η' := lt_of_lt_of_le hη hηη'
  have hsq : η ^ 2 ≤ η' ^ 2 := pow_le_pow_left₀ hη.le hηη' 2
  have key : ∀ i, η * (η / ((v i - x) ^ 2 + η ^ 2)) ≤ η' * (η' / ((v i - x) ^ 2 + η' ^ 2)) := by
    intro i
    have hc : 0 ≤ (v i - x) ^ 2 := sq_nonneg _
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hsq hc]
  have e : ∀ (s : ℝ) (f : ι → ℝ), s * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, f i) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, s * f i := by
    intro s f; rw [mul_left_comm, Finset.mul_sum]
  rw [Step1Good_mV_im v x η hη, Step1Good_mV_im v x η' hη', e, e]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i) (by positivity)

/-- **Target 1d** `mV_im_le_inv`: `Im mV v (x + iη) ≤ 1/η`. -/
theorem mV_im_le_inv :
    ∀ {ι : Type*} [Fintype ι] (v : ι → ℝ) (x η : ℝ), 0 < η → (mV v ⟨x, η⟩).im ≤ 1 / η := by
  intro ι _ v x η hη
  rw [Step1Good_mV_im v x η hη]
  have hterm : ∀ i, η / ((v i - x) ^ 2 + η ^ 2) ≤ 1 / η := by
    intro i
    rw [div_le_div_iff₀ (by positivity) hη]
    nlinarith [sq_nonneg (v i - x)]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, _root_.inv_zero, zero_mul]; positivity
  · have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hpos
    calc (Fintype.card ι : ℝ)⁻¹ * ∑ i, η / ((v i - x) ^ 2 + η ^ 2)
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, 1 / η :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
      _ = 1 / η := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

/-! ## 2. What `Admissible` says about `𝔠`, `𝔡` (the `d ≥ 3` bookkeeping: `τ_s ≤ 𝔠𝔡 < 1/2 < 8/11`) -/

/-- `W → ∞` along an admissible sequence (`W ≥ N^𝔠` and `N → ∞`); copy of the 4-line proof of
`scaleFacts3_W_tendsto` (`Induction/ScaleFacts3.lean:410`, not imported). -/
private theorem Step1Good_W_tendsto {d : ℕ} {sz : Sizes d} {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hN, hB, -⟩ := hA
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  exact tendsto_atTop_mono' atTop hB h1

/-- **Target 2a** `un_admissible_c_mul_lt_one`: `W ≥ N^𝔠` and `N = (W L)^d > W^d` (`L ≥ 3`) give `𝔠 d < 1`
(at one `n`; `un_dc_lt_one`, `Pins.lean:1011`). -/
theorem un_admissible_c_mul_lt_one :
    ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, 0 < d → sz.Admissible 𝔠 𝔡 → 𝔠 * (d : ℝ) < 1 := by
  intro d sz 𝔠 𝔡 hd hA
  obtain ⟨n, hn⟩ := hA.2.2.2.1.exists
  have h := un_dc_lt_one (d := d) (L := sz.L n) (W := sz.W n) hd (sz.three_le_L n) (sz.W_pos n) hA.1 hn
  linarith

/-- **Target 2b** `un_admissible_d_le_half`: `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` eventually and `W → ∞` give
`𝔡 ≤ d/2`. -/
theorem un_admissible_d_le_half :
    ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → 𝔡 ≤ (d : ℝ) / 2 := by
  intro d sz 𝔠 𝔡 hA
  by_contra hcon
  have hlt : (d : ℝ) / 2 < 𝔡 := not_le.mp hcon
  have hpos : 0 < -(d : ℝ) / 2 + 𝔡 := by linarith
  have h1 : Tendsto (fun n => ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡)) atTop atTop :=
    (tendsto_rpow_atTop hpos).comp (Step1Good_W_tendsto hA)
  have h2 := (h1.eventually_gt_atTop (𝔡⁻¹))
  obtain ⟨n, hn1, hn2⟩ := (h2.and hA.2.2.2.2).exists
  have := lt_of_lt_of_le hn1 hn2.1
  linarith [hn2.2]

/-- **Target 2c** `un_admissible_cd_lt_half`: hence `𝔠𝔡 < 1/2`; with `τ_s ≤ 𝔠𝔡` the term `C₀ t`,
`t ≤ N^{-1+τ_s}`, of target 4 is `≪ N^{-3τ_s/8}` (needs `τ_s < 8/11`; the pin's `τ_s < 1` alone does not
give it). -/
theorem un_admissible_cd_lt_half :
    ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, 0 < d → sz.Admissible 𝔠 𝔡 → 𝔠 * 𝔡 < 1 / 2 := by
  intro d sz 𝔠 𝔡 hd hA
  have h1 := un_admissible_c_mul_lt_one sz hd hA
  have h2 := un_admissible_d_le_half sz hA
  have h𝔠 := hA.1
  nlinarith

/-! ## 3. Elementary facts on `a = e^{-T/2}`, `t = 1 - e^{-T}` (RBM2D `Step1RegularityB.lean:74-123`) -/

private theorem Step1Good_exp_le_one {T : ℝ} (hT : 0 ≤ T) : Real.exp (-T / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith

private theorem Step1Good_one_le_inv {T : ℝ} (hT : 0 ≤ T) : 1 ≤ (Real.exp (-T / 2))⁻¹ := by
  rw [one_le_inv₀ (Real.exp_pos _)]
  exact Step1Good_exp_le_one hT

/-- `(e^{-T/2})⁻¹ ≤ 1 + T` for `0 ≤ T ≤ 1`. -/
private theorem Step1Good_inv_le {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (Real.exp (-T / 2))⁻¹ ≤ 1 + T := by
  have h := Real.add_one_le_exp (-T / 2)
  have h1 : (0 : ℝ) < -T / 2 + 1 := by linarith
  refine (inv_anti₀ h1 h).trans ?_
  rw [inv_le_iff_one_le_mul₀ h1]
  nlinarith

/-- `1 - e^{-T} ≤ T`. -/
private theorem Step1Good_one_sub_exp_le (T : ℝ) : 1 - Real.exp (-T) ≤ T := by
  have := Real.add_one_le_exp (-T); linarith

/-- `T / 2 ≤ 1 - e^{-T}` for `0 ≤ T ≤ 1`. -/
private theorem Step1Good_half_le_one_sub_exp {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    T / 2 ≤ 1 - Real.exp (-T) := by
  have h := Real.add_one_le_exp T
  have h1 : (0 : ℝ) < T + 1 := by linarith
  have h2 : Real.exp (-T) ≤ (T + 1)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ h1 h
  have h3 : (T + 1)⁻¹ ≤ 1 - T / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]; nlinarith
  linarith

private theorem Step1Good_one_sub_exp_pos {T : ℝ} (hT : 0 < T) : 0 < 1 - Real.exp (-T) := by
  have : Real.exp (-T) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  linarith

private theorem Step1Good_sqrt_exp (T : ℝ) : Real.sqrt (Real.exp (-T)) = Real.exp (-T / 2) :=
  (Real.exp_half (-T)).symm

private theorem Step1Good_rpow_ev {e c : ℝ} (he : e < 0) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ e ≤ c := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).eventually (ge_mem_nhds hc)
  simpa using h

/-- `W ≤ N`: `W ≤ W L ≤ (W L)^d` for `d ≥ 1`. -/
private theorem Step1Good_W_le_size {d : ℕ} (sz : Sizes d) (hd : 0 < d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ Nsz sz n := by
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have h1 : sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
  have h2 : sz.W n * sz.L n ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow hd.ne' _
  exact_mod_cast h1.trans h2

/-! ## 4. The local-law precision, the strip and the regularity part at one `n` -/

/-- **The local-law precision at height `y`** (RBM2D `Step1RegularityB_err_pow`, with `Meta ≥ min (W², N η)`
replaced by `un_Bctl_le` and `un_step1_floor`): `W^{τ_s/8} Bctl n (1 - y) ≤ N^{-15τ_s/16} +
N^{τ_s/8} (N y)⁻¹`, for `τ_s ≤ 𝔠𝔡`, `𝔠 < 1`. -/
private theorem Step1Good_bctl {d : ℕ} (sz : Sizes d) (n : ℕ) {𝔠 𝔡 τs : ℝ} (hd : 0 < d) (h𝔠 : 0 < 𝔠)
    (h𝔠1 : 𝔠 < 1) (h𝔡 : 0 < 𝔡) (hτs : 0 < τs) (hτ𝔠 : τs ≤ 𝔠 * 𝔡) (hN1 : 1 ≤ Nsz sz n)
    (hB : Nsz sz n ^ 𝔠 ≤ (sz.W n : ℝ))
    (hWO : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) {y : ℝ} (hy : 0 < y) :
    ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - y) ≤
      Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * y)⁻¹ := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hApos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := Real.rpow_pos_of_pos hW0 _
  have hlam := Sizes.lam_sq_mul_pow_ge sz n hWO
  have hb := un_Bctl_le sz n hy hApos hlam
  have hfloor := un_step1_floor hN1 hW1 h𝔠 h𝔠1 h𝔡 hτs hτ𝔠 hB
  have hWN : ((sz.W n : ℕ) : ℝ) ^ (τs / 8) ≤ Nsz sz n ^ (τs / 8) :=
    Real.rpow_le_rpow hW0.le (Step1Good_W_le_size sz hd n) (by linarith)
  have hAinv : (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) :=
    (Real.rpow_neg hW0.le _).symm
  have hy' : 0 ≤ (Nsz sz n * y)⁻¹ := by
    have : 0 < Nsz sz n := by linarith
    positivity
  calc ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - y)
      ≤ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) *
          ((((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ + (Nsz sz n * y)⁻¹) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hW0.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) +
          ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (Nsz sz n * y)⁻¹ := by rw [hAinv]; ring
    _ ≤ Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * y)⁻¹ :=
        add_le_add hfloor (mul_le_mul_of_nonneg_right hWN hy')

/-- **The closeness hypothesis of `freeConv_stable_lip`** on the strip (RBM2D `Step1RegularityB_strip`, `:657`,
at the reference `mr = m n`; error `2 (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8})` instead of `N^{-3τ_s/8}/C₀`):
for `|Re w| ≤ c₁`, `c₀ t/4 ≤ Im w ≤ 1/2`, the rescaled point `ζ = a⁻¹ (w + E)` lies in the window of the local
law (`Im ζ ≥ c₀ t*/8 ≥ N^{-1+τ_s/8}`: `τ_s/8 < τ_s`), and `‖m_V(w) - a⁻¹ m(ζ)‖ = a⁻¹ ‖m_N(ζ) - m(ζ)‖`. -/
private theorem Step1Good_strip {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (mr : ℂ → ℂ) {N T E δ τs c₀ c₁ : ℝ}
    (hN1 : 1 ≤ N) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hc₁ : c₁ ≤ δ / 4)
    (hTN : T = N ^ (-1 + τs)) (hT1 : T ≤ 1 / 2) (hET : |E| * T ≤ δ / 4)
    (hedge : N ^ (-1 + τs / 8) ≤ c₀ / 8 * T)
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN H ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹)
    {w : ℂ} (hw : |w.re| ≤ c₁) (hlow : c₀ * (1 - Real.exp (-T)) / 4 ≤ w.im) (hw1 : w.im ≤ 1 / 2) :
    ‖mV (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) w -
        (Real.sqrt (Real.exp (-T)) : ℂ)⁻¹ * mr ((Real.sqrt (Real.exp (-T)) : ℂ)⁻¹ * (w + E))‖ ≤
      2 * (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  have hT1' : T ≤ 1 := by linarith
  rw [Step1Good_sqrt_exp]
  have ha0 : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have hainv : (Real.exp (-T / 2))⁻¹ ≤ 1 + T := Step1Good_inv_le hTpos.le hT1'
  have hainv1 : 1 ≤ (Real.exp (-T / 2))⁻¹ := Step1Good_one_le_inv hTpos.le
  have hhalf := Step1Good_half_le_one_sub_exp hTpos.le hT1'
  have hy : c₀ / 8 * T ≤ w.im := by
    have : c₀ / 8 * T ≤ c₀ * (1 - Real.exp (-T)) / 4 := by nlinarith
    exact this.trans hlow
  have hy0 : 0 < c₀ / 8 * T := by positivity
  have hw0 : 0 < w.im := lt_of_lt_of_le hy0 hy
  set a : ℝ := Real.exp (-T / 2) with ha
  set ζ : ℂ := ((a : ℝ) : ℂ)⁻¹ * (w + E) with hζ
  have hzre : ζ.re = a⁻¹ * (w.re + E) := by
    rw [hζ, Step1Good_inv_mul_re, Complex.add_re, Complex.ofReal_re]
  have hzim : ζ.im = a⁻¹ * w.im := by
    rw [hζ, Step1Good_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
  have hzim_ge : w.im ≤ ζ.im := by
    rw [hzim]
    calc w.im = 1 * w.im := (one_mul _).symm
      _ ≤ a⁻¹ * w.im := mul_le_mul_of_nonneg_right hainv1 hw0.le
  have hc₁0 : 0 ≤ c₁ := (abs_nonneg _).trans hw
  have hdomre : |ζ.re - E| ≤ δ := by
    rw [hzre]
    have e1 : a⁻¹ * (w.re + E) - E = a⁻¹ * w.re + (a⁻¹ - 1) * E := by ring
    rw [e1]
    have h1 : |a⁻¹ * w.re| ≤ (1 + T) * c₁ := by
      rw [abs_mul, abs_of_pos (inv_pos.2 ha0)]
      exact mul_le_mul hainv hw (abs_nonneg _) (by linarith)
    have h2 : |(a⁻¹ - 1) * E| ≤ T * |E| := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    calc |a⁻¹ * w.re + (a⁻¹ - 1) * E| ≤ |a⁻¹ * w.re| + |(a⁻¹ - 1) * E| := abs_add_le _ _
      _ ≤ (1 + T) * c₁ + T * |E| := add_le_add h1 h2
      _ ≤ δ := by nlinarith
  have hdomlo : N ^ (-1 + τs / 8) ≤ ζ.im := hedge.trans (hy.trans hzim_ge)
  have hdomhi : ζ.im ≤ 1 := by
    rw [hzim]
    calc a⁻¹ * w.im ≤ (1 + T) * (1 / 2) := mul_le_mul hainv hw1 hw0.le (by linarith)
      _ ≤ 1 := by linarith
  have herrz := hpt ζ hdomre hdomlo hdomhi
  -- `(N Im ζ)⁻¹ ≤ 8 c₀⁻¹ N^{-τs}`
  have hNT : N * T = N ^ τs := by
    have : N ^ (1 + (-1 + τs)) = N * N ^ (-1 + τs) := by rw [Real.rpow_add hN0, Real.rpow_one]
    rw [hTN, ← this]; congr 1; ring
  have hinv : (N * ζ.im)⁻¹ ≤ 8 * c₀⁻¹ * (N ^ τs)⁻¹ := by
    have h1 : N * (c₀ / 8 * T) ≤ N * ζ.im :=
      mul_le_mul_of_nonneg_left (hy.trans hzim_ge) hN0.le
    have h2 : 0 < N * (c₀ / 8 * T) := by positivity
    refine (inv_anti₀ h2 h1).trans (le_of_eq ?_)
    rw [← hNT]
    have : N * (c₀ / 8 * T) = c₀ / 8 * (N * T) := by ring
    rw [this, mul_inv, inv_div]
    have hNTpos : 0 < N * T := by positivity
    field_simp
  have hsplit : N ^ (τs / 8) * (N ^ τs)⁻¹ = N ^ (-(7 * τs / 8)) := by
    rw [← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; congr 1; ring
  have herr' : ‖stieltjesN H ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8)) := by
    refine herrz.trans ?_
    have hNa : 0 ≤ N ^ (τs / 8) := Real.rpow_nonneg hN0.le _
    calc N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹
        ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (8 * c₀⁻¹ * (N ^ τs)⁻¹) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv hNa)
      _ = N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * (N ^ (τs / 8) * (N ^ τs)⁻¹) := by ring
      _ = _ := by rw [hsplit]
  have hdict : mV (fun i => a * hH.eigenvalues i - E) w = ((a : ℝ) : ℂ)⁻¹ * stieltjesN H ζ :=
    Step1Good_mV_affine hH ha0 E hw0
  rw [hdict, ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha0.le]
  have ha2 : a⁻¹ ≤ 2 := by linarith
  calc a⁻¹ * ‖stieltjesN H ζ - mr ζ‖
      ≤ 2 * (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) :=
        mul_le_mul ha2 herr' (norm_nonneg _) (by norm_num)

/-- **The regularity part** (RBM2D `Step1RegularityB_regular`, `:531`; supervisor 2.2): `[32]`-regularity (2.2),
(2.3) of `v = a λ(H) - E` with `g = N^{-1+τ_s/4}`, `c = c_box/40`, `C = 2K + c_box + 2`, `CV = CV₀ + 1`, from the
local law at the rescaled points (`η ≤ 1/2`: `Im m_V ∈ [c_box/2, 2K + c_box]`; `1/2 < η ≤ 10`: `η Im m_V`
nondecreasing and `Im m_V ≤ 1/η`) and from `|λ_i| ≤ N^{CV₀}`. -/
private theorem Step1Good_regular {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (mr : ℂ → ℂ) {N T E δ τs cb K CV₀ G : ℝ}
    (hN : |E| + 2 ≤ N) (hcard : (Fintype.card ι : ℝ) = N) (hcb : 0 < cb) (hK : 0 < K) (hδ : 0 < δ)
    (hτs : 0 < τs) (hTN : T = N ^ (-1 + τs)) (hT1 : T ≤ 1 / 2) (hET : |E| * T ≤ δ / 4)
    (hG : 2 * G ≤ δ / 2)
    (hbox : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → cb ≤ (mr z).im ∧ ‖mr z‖ ≤ K)
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN H ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹)
    (herr : N ^ (-(15 * τs / 16)) + N ^ (-(τs / 8)) ≤ cb / 2)
    (hnorm : ∀ i, |hH.eigenvalues i| ≤ N ^ CV₀) (hCV : 0 ≤ CV₀) :
    IsRegular32 (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) (N ^ (-1 + τs / 4)) G
      (cb / 40) (2 * K + cb + 2) (CV₀ + 1) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  have hT1' : T ≤ 1 := by linarith
  have ha0 : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have hainv : (Real.exp (-T / 2))⁻¹ ≤ 1 + T := Step1Good_inv_le hTpos.le hT1'
  have hainv1 : 1 ≤ (Real.exp (-T / 2))⁻¹ := Step1Good_one_le_inv hTpos.le
  have hgpos : 0 < N ^ (-1 + τs / 4) := Real.rpow_pos_of_pos hN0 _
  have hg12 : N ^ (-1 + τs / 4) ≤ 1 / 2 := by
    calc N ^ (-1 + τs / 4) ≤ N ^ (-1 + τs) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = T := hTN.symm
      _ ≤ 1 / 2 := hT1
  -- the bulk claim: `η ≤ 1/2`
  have hmain : ∀ E' η : ℝ, |E'| ≤ G → N ^ (-1 + τs / 4) ≤ η → η ≤ 1 / 2 →
      cb / 2 ≤ (mV (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) ⟨E', η⟩).im ∧
        (mV (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) ⟨E', η⟩).im ≤ 2 * K + cb := by
    intro E' η hE' hgη hη1
    have hη0 : 0 < η := lt_of_lt_of_le hgpos hgη
    have hG0 : 0 ≤ G := (abs_nonneg _).trans hE'
    set a : ℝ := Real.exp (-T / 2) with ha
    set ζ : ℂ := ((a : ℝ) : ℂ)⁻¹ * ((⟨E', η⟩ : ℂ) + E) with hζ
    have hzre : ζ.re = a⁻¹ * (E' + E) := by
      rw [hζ, Step1Good_inv_mul_re, Complex.add_re, Complex.ofReal_re]
    have hzim : ζ.im = a⁻¹ * η := by
      rw [hζ, Step1Good_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
    have hzim_ge : η ≤ ζ.im := by
      rw [hzim]
      calc η = 1 * η := (one_mul _).symm
        _ ≤ a⁻¹ * η := mul_le_mul_of_nonneg_right hainv1 hη0.le
    have hdomre : |ζ.re - E| ≤ δ := by
      rw [hzre]
      have e1 : a⁻¹ * (E' + E) - E = a⁻¹ * E' + (a⁻¹ - 1) * E := by ring
      rw [e1]
      have h1 : |a⁻¹ * E'| ≤ (1 + T) * G := by
        rw [abs_mul, abs_of_pos (inv_pos.2 ha0)]
        exact mul_le_mul hainv hE' (abs_nonneg _) (by linarith)
      have h2 : |(a⁻¹ - 1) * E| ≤ T * |E| := by
        rw [abs_mul, abs_of_nonneg (by linarith)]
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      calc |a⁻¹ * E' + (a⁻¹ - 1) * E| ≤ |a⁻¹ * E'| + |(a⁻¹ - 1) * E| := abs_add_le _ _
        _ ≤ (1 + T) * G + T * |E| := add_le_add h1 h2
        _ ≤ δ := by nlinarith
    have hgg : N ^ (-1 + τs / 8) ≤ N ^ (-1 + τs / 4) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hdomlo : N ^ (-1 + τs / 8) ≤ ζ.im := hgg.trans (hgη.trans hzim_ge)
    have hzpos : 0 < ζ.im := lt_of_lt_of_le hη0 hzim_ge
    have hdomhi : ζ.im ≤ 1 := by
      rw [hzim]
      calc a⁻¹ * η ≤ (1 + T) * (1 / 2) := mul_le_mul hainv hη1 hη0.le (by linarith)
        _ ≤ 1 := by linarith
    have herrz := hpt ζ hdomre hdomlo hdomhi
    -- `N^{τs/8} (N Im ζ)⁻¹ ≤ N^{-τs/8}`
    have hNg : N * N ^ (-1 + τs / 4) = N ^ (τs / 4) := by
      have : N ^ (1 + (-1 + τs / 4)) = N * N ^ (-1 + τs / 4) := by rw [Real.rpow_add hN0, Real.rpow_one]
      rw [← this]; congr 1; ring
    have hinv : (N * ζ.im)⁻¹ ≤ (N ^ (τs / 4))⁻¹ := by
      rw [← hNg]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (hgη.trans hzim_ge) hN0.le)
    have hsplit : N ^ (τs / 8) * (N ^ (τs / 4))⁻¹ = N ^ (-(τs / 8)) := by
      rw [← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; congr 1; ring
    have hloc : ‖stieltjesN H ζ - mr ζ‖ ≤ cb / 2 := by
      refine herrz.trans (le_trans ?_ herr)
      have hNa : 0 ≤ N ^ (τs / 8) := Real.rpow_nonneg hN0.le _
      calc N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹
          ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N ^ (τs / 4))⁻¹ :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv hNa)
        _ = _ := by rw [hsplit]
    obtain ⟨hb1, hb2⟩ := hbox ζ hdomre hzpos hdomhi
    have hIm : |(stieltjesN H ζ).im - (mr ζ).im| ≤ cb / 2 := by
      calc |(stieltjesN H ζ).im - (mr ζ).im| = |(stieltjesN H ζ - mr ζ).im| := by rw [Complex.sub_im]
        _ ≤ ‖stieltjesN H ζ - mr ζ‖ := Complex.abs_im_le_norm _
        _ ≤ cb / 2 := hloc
    have hmrim : (mr ζ).im ≤ K := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hb2)
    obtain ⟨h1, h2⟩ := abs_le.mp hIm
    have hdict : mV (fun i => a * hH.eigenvalues i - E) ⟨E', η⟩ =
        ((a : ℝ) : ℂ)⁻¹ * stieltjesN H ζ := Step1Good_mV_affine hH ha0 E (w := ⟨E', η⟩) hη0
    have hdictIm : (mV (fun i => a * hH.eigenvalues i - E) ⟨E', η⟩).im =
        a⁻¹ * (stieltjesN H ζ).im := by rw [hdict, Step1Good_inv_mul_im]
    rw [hdictIm]
    have hS0 : 0 ≤ (stieltjesN H ζ).im := by linarith
    refine ⟨?_, ?_⟩
    · calc cb / 2 ≤ (stieltjesN H ζ).im := by linarith
        _ = 1 * (stieltjesN H ζ).im := (one_mul _).symm
        _ ≤ a⁻¹ * (stieltjesN H ζ).im := mul_le_mul_of_nonneg_right hainv1 hS0
    · calc a⁻¹ * (stieltjesN H ζ).im ≤ 2 * (K + cb / 2) :=
          mul_le_mul (by linarith) (by linarith) hS0 (by norm_num)
        _ = 2 * K + cb := by ring
  refine ⟨?_, ?_⟩
  · intro E' η hE' hgη hη10
    have hη0 : 0 < η := lt_of_lt_of_le hgpos hgη
    by_cases hη12 : η ≤ 1 / 2
    · obtain ⟨h1, h2⟩ := hmain E' η hE' hgη hη12
      exact ⟨by linarith, by linarith⟩
    · have hη12' : 1 / 2 < η := not_le.mp hη12
      obtain ⟨hl, -⟩ := hmain E' (1 / 2) hE' hg12 le_rfl
      have hmono := mV_eta_mul_im_mono
        (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) E' (1 / 2) η (by norm_num) hη12'.le
      set S := (mV (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) ⟨E', η⟩).im with hS
      have h4 : cb / 4 ≤ η * S := by nlinarith
      have hSpos : 0 < S := by
        by_contra hneg
        push Not at hneg
        nlinarith [mul_nonneg hη0.le (neg_nonneg.2 hneg)]
      refine ⟨?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_right hη10 hSpos.le]
      · have hle := mV_im_le_inv (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) E' η hη0
        have : 1 / η ≤ 2 := by
          rw [div_le_iff₀ hη0]; linarith
        linarith
  · intro i
    rw [hcard]
    have hlam := hnorm i
    have ha1 : Real.exp (-T / 2) ≤ 1 := Step1Good_exp_le_one hTpos.le
    have h1 : |Real.exp (-T / 2) * hH.eigenvalues i - E| ≤ N ^ CV₀ + |E| := by
      calc |Real.exp (-T / 2) * hH.eigenvalues i - E|
          ≤ |Real.exp (-T / 2) * hH.eigenvalues i| + |E| := abs_sub _ _
        _ = Real.exp (-T / 2) * |hH.eigenvalues i| + |E| := by rw [abs_mul, abs_of_pos ha0]
        _ ≤ N ^ CV₀ + |E| := by
            have : Real.exp (-T / 2) * |hH.eigenvalues i| ≤ |hH.eigenvalues i| :=
              mul_le_of_le_one_left (abs_nonneg _) ha1
            linarith
    have hx1 : (1 : ℝ) ≤ N ^ CV₀ := Real.one_le_rpow hN1 hCV
    have hpow : N ^ (CV₀ + 1) = N ^ CV₀ * N := by rw [Real.rpow_add hN0, Real.rpow_one]
    rw [hpow]
    nlinarith [mul_le_mul_of_nonneg_right hx1 (by linarith [abs_nonneg E] : (0 : ℝ) ≤ N - 1)]

/-- The size conditions of the rate: `C₀ (ε + T) ≤ N^{-3τ_s/8}` for `ε = 2 (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8})`,
`T = N^{-1+τ_s}`; the three exponent gaps `9τ_s/16`, `τ_s/2`, `1 - 11τ_s/8` (positive iff `τ_s < 8/11`). -/
private theorem Step1Good_rate {N τs C₀ c₀ : ℝ} (hN0 : 0 < N) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (h1 : N ^ (-(9 * τs / 16)) ≤ 1 / (6 * C₀)) (h2 : N ^ (-(τs / 2)) ≤ c₀ / (48 * C₀))
    (h3 : N ^ (-(1 - 11 * τs / 8)) ≤ 1 / (3 * C₀)) :
    C₀ * (2 * (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + τs)) ≤
      N ^ (-(3 * τs / 8)) := by
  have hX : 0 < N ^ (-(3 * τs / 8)) := Real.rpow_pos_of_pos hN0 _
  have eA : N ^ (-(15 * τs / 16)) = N ^ (-(9 * τs / 16)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have eB : N ^ (-(7 * τs / 8)) = N ^ (-(τs / 2)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have eC : N ^ (-1 + τs) = N ^ (-(1 - 11 * τs / 8)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  set X := N ^ (-(3 * τs / 8)) with hXdef
  set p := N ^ (-(9 * τs / 16)) with hp
  set q := N ^ (-(τs / 2)) with hq
  set r := N ^ (-(1 - 11 * τs / 8)) with hr
  rw [eA, eB, eC]
  have q1 : p * (6 * C₀) ≤ 1 := (le_div_iff₀ (by positivity)).1 h1
  have q2 : q * (48 * C₀) ≤ c₀ := (le_div_iff₀ (by positivity)).1 h2
  have q3 : r * (3 * C₀) ≤ 1 := (le_div_iff₀ (by positivity)).1 h3
  have hq2 : c₀⁻¹ * (q * (48 * C₀)) ≤ 1 := by
    calc c₀⁻¹ * (q * (48 * C₀)) ≤ c₀⁻¹ * c₀ := mul_le_mul_of_nonneg_left q2 (by positivity)
      _ = 1 := inv_mul_cancel₀ hc₀.ne'
  have hs : 2 * C₀ * p + 16 * C₀ * c₀⁻¹ * q + C₀ * r ≤ 1 := by
    have e : 16 * C₀ * c₀⁻¹ * q = c₀⁻¹ * (q * (48 * C₀)) / 3 := by ring
    rw [e]
    nlinarith
  calc C₀ * (2 * (p * X + 8 * c₀⁻¹ * (q * X)) + r * X)
      = X * (2 * C₀ * p + 16 * C₀ * c₀⁻¹ * q + C₀ * r) := by ring
    _ ≤ X * 1 := mul_le_mul_of_nonneg_left hs hX.le
    _ = X := mul_one _

/-- **The deterministic half at one `n`** (RBM2D `Step1RegularityB_det`, `:737`, after `filter_upwards`): all the
size conditions are hypotheses.  Regularity from `Step1Good_regular`; the free-convolution part from
`freeConv_stable_lip` (`hFC`, the three conjuncts used) with the strip closeness `Step1Good_strip`, and
`ρ₀ = ρ_n` by uniqueness of limits. -/
private theorem Step1Good_at_n {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (mr : ℂ → ℂ) (ρn : ℝ) {N T E δ τs cb K C₀ c₀ c₁ CV₀ G : ℝ}
    (hδ : 0 < δ) (hcb : 0 < cb) (hK : 0 < K) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) (hc₁ : c₁ ≤ δ / 4)
    (hτs : 0 < τs) (hCV : 0 ≤ CV₀)
    (hN : |E| + 2 ≤ N) (hcard : (Fintype.card ι : ℝ) = N) (hTN : T = N ^ (-1 + τs))
    (hTc : T ≤ c₀) (hT1 : T ≤ 1 / 2) (hET : |E| * T ≤ δ / 4) (hG : 2 * G ≤ δ / 2)
    (hedge : N ^ (-1 + τs / 8) ≤ c₀ / 8 * T)
    (e15 : N ^ (-(15 * τs / 16)) ≤ c₀ / 4) (e78 : N ^ (-(7 * τs / 8)) ≤ c₀ ^ 2 / 32)
    (herr : N ^ (-(15 * τs / 16)) + N ^ (-(τs / 8)) ≤ cb / 2)
    (hrate : C₀ * (2 * (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + T) ≤ N ^ (-(3 * τs / 8)))
    (hbox : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → cb ≤ (mr z).im ∧ ‖mr z‖ ≤ K)
    (hρn : Tendsto (fun η : ℝ => (mr ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρn))
    (hFC : ∀ (v : ι → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t → 0 ≤ ε → ε ≤ c₀ →
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * mr ((Real.sqrt s : ℂ)⁻¹ * (w + E))‖ ≤ ε) →
      ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (mr ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧ |ρ - ρ₀| ≤ C₀ * (ε + t))
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN H ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹)
    (hnorm : ∀ i, |hH.eigenvalues i| ≤ N ^ CV₀) :
    IsRegular32 (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) (N ^ (-1 + τs / 4)) G
        (cb / 40) (2 * K + cb + 2) (CV₀ + 1) ∧
      ∃ mfc : ℂ → ℂ, IsFreeConv32 (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E)
          (1 - Real.exp (-T)) mfc ∧
        ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
          |ρ' - ρn| ≤ N ^ (-(3 * τs / 8)) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  refine ⟨Step1Good_regular hH mr hN hcard hcb hK hδ hτs hTN hT1 hET hG hbox hpt herr hnorm hCV, ?_⟩
  have ht : 0 < 1 - Real.exp (-T) := Step1Good_one_sub_exp_pos hTpos
  have htT : 1 - Real.exp (-T) ≤ T := Step1Good_one_sub_exp_le T
  have hε0 : 0 ≤ 2 * (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) := by positivity
  have hεc : 2 * (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) ≤ c₀ := by
    have h2 : 8 * c₀⁻¹ * N ^ (-(7 * τs / 8)) ≤ c₀ / 4 := by
      calc 8 * c₀⁻¹ * N ^ (-(7 * τs / 8)) ≤ 8 * c₀⁻¹ * (c₀ ^ 2 / 32) :=
            mul_le_mul_of_nonneg_left e78 (by positivity)
        _ = c₀ / 4 := by field_simp; ring
    linarith
  obtain ⟨ρ, ρ₀, h1, h2, h3⟩ := hFC (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E)
    (Real.exp (-T)) (1 - Real.exp (-T)) (2 * (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))))
    ht (htT.trans hTc) (by ring) hε0 hεc
    (fun w hw hlow hw1 => Step1Good_strip hH mr hN1 hc₀ hδ hc₁ hTN hT1 hET hedge hpt hw hlow hw1)
  have hρ : ρ₀ = ρn := tendsto_nhds_unique h2 hρn
  refine ⟨freeConvST (fun i => Real.exp (-T / 2) * hH.eigenvalues i - E) (1 - Real.exp (-T)),
    isFreeConv51_freeConvST _ ht.le, ρ, h1, ?_⟩
  rw [← hρ]
  refine h3.trans (le_trans ?_ hrate)
  exact mul_le_mul_of_nonneg_left (by linarith) hC₀.le

/-! ## 5. The deterministic half and the pin -/

/-- **Target 3a** `step1Good'_det` (RBM2D `Step1RegularityB_det`, `:737`, with `msc ↦ m n` under `UNDens'`,
`freeConv_stable_local ↦ freeConv_stable_lip`, the band event `Step1LocalEvent` replaced by the complement of the
bad sets of `UNTrLocal` at `(ε, τ) = (τ_s/8, τ_s/8)` and of `UNNormBound`): eventually in `n`, every `ω` on which
the local law holds at heights `≥ N^{-1+τ_s/8}` and all eigenvalues are `≤ N^{CV₀}` has the good event of
`UNStep1Good'`.  The constants `c C` come before `∀ᶠ n`. -/
theorem step1Good'_det :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ →
        ∀ τs : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 →
          ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz,
            (∀ z : ℂ, |z.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ z.im → z.im ≤ 1 →
              ‖stieltjesN (M.H n ω) z - m n z‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - z.im)) →
            (∀ i, |(M.herm n ω).eigenvalues i| ≤ Nsz sz n ^ CV₀) →
            (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                  (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8))) := by
  intro d hd 𝔠 𝔡 sz hA M m E ρ δ hD CV₀ hCV τs hτs0 hτs1 hτs𝔠𝔡
  obtain ⟨hδ, c', C', Lp', hc', hC', hLp', hUev⟩ := hD.1
  obtain ⟨cb, K, Lp, hcb, hK, hLp, hbev⟩ := hD.2
  obtain ⟨c₀, c₁, C₀, hc₀, hc₀c₁, hc₁δ, hC₀, hFC⟩ :=
    freeConv_stable_lip cb K Lp δ |E| hcb hK hLp hδ (abs_nonneg E)
  have hd0 : 0 < d := by omega
  have h𝔠 : 0 < 𝔠 := hA.1
  have h𝔡 : 0 < 𝔡 := hA.2.1
  have hcd := un_admissible_cd_lt_half sz hd0 hA
  have h𝔠1 : 𝔠 < 1 := by
    have h1 := un_admissible_c_mul_lt_one sz hd0 hA
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    nlinarith
  have hτs118 : τs < 8 / 11 := by linarith
  have hσ0 : 0 < min (τs / 4) ((1 - τs) / 3) := lt_min (by linarith) (by linarith)
  refine ⟨cb / 40, 2 * K + cb + 2, by positivity, ?_⟩
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop := hA.2.2.1
  have hc₁4 : c₁ ≤ δ / 4 := by
    refine hc₁δ.trans ?_
    exact div_le_div_of_nonneg_left hδ.le (by norm_num) (by nlinarith [abs_nonneg E])
  filter_upwards [hbev, hUev, hA.2.2.2.1, hA.2.2.2.2, hNtend.eventually_ge_atTop (|E| + 2),
    hNtend.eventually (Step1Good_rpow_ev (e := -1 + τs) (c := min c₀ (1 / 2)) (by linarith)
      (lt_min hc₀ (by norm_num))),
    hNtend.eventually (Step1Good_rpow_ev (e := -(min (τs / 4) ((1 - τs) / 3))) (c := δ / 4)
      (by linarith) (by positivity)),
    hNtend.eventually (Step1Good_rpow_ev (e := -(7 * τs / 8)) (c := c₀ / 8) (by linarith)
      (by positivity)),
    hNtend.eventually (Step1Good_rpow_ev (e := -(15 * τs / 16)) (c := min (c₀ / 4) (cb / 4))
      (by linarith) (lt_min (by positivity) (by positivity))),
    hNtend.eventually (Step1Good_rpow_ev (e := -(7 * τs / 8)) (c := c₀ ^ 2 / 32) (by linarith)
      (by positivity)),
    hNtend.eventually (Step1Good_rpow_ev (e := -(τs / 8)) (c := cb / 4) (by linarith)
      (by positivity)),
    hNtend.eventually (Step1Good_rpow_ev (e := -(9 * τs / 16)) (c := 1 / (6 * C₀)) (by linarith)
      (by positivity)),
    hNtend.eventually (Step1Good_rpow_ev (e := -(τs / 2)) (c := c₀ / (48 * C₀)) (by linarith)
      (by positivity)),
    hNtend.eventually (Step1Good_rpow_ev (e := -(1 - 11 * τs / 8)) (c := 1 / (3 * C₀))
      (by linarith) (by positivity))] with
    n hbn hUn hB hWO hNE eT eG eedge e15 e78 e18 e9 e12 e1118
  intro ω hLL hnorm
  have : Nonempty (Idx d (sz.L n) (sz.W n)) := ⟨fun _ => 0⟩
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith
  have hTc : ouTStar sz τs n ≤ c₀ := eT.trans (min_le_left _ _)
  have hT1 : ouTStar sz τs n ≤ 1 / 2 := eT.trans (min_le_right _ _)
  have hET : |E| * ouTStar sz τs n ≤ δ / 4 := by
    have h1 : ouTStar sz τs n ≤ δ / (4 * (1 + |E|)) := hTc.trans (hc₀c₁.trans hc₁δ)
    calc |E| * ouTStar sz τs n ≤ |E| * (δ / (4 * (1 + |E|))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg E)
      _ ≤ δ / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [abs_nonneg E]
  have hedge : Nsz sz n ^ (-1 + τs / 8) ≤ c₀ / 8 * ouTStar sz τs n := by
    have hsplit : Nsz sz n ^ (-1 + τs / 8) =
        Nsz sz n ^ (-(7 * τs / 8)) * Nsz sz n ^ (-1 + τs) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right eedge (Real.rpow_nonneg hN0.le _)
  have hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN (M.H n ω) ζ - m n ζ‖ ≤
        Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * ζ.im)⁻¹ := by
    intro ζ h1 h2 h3
    have hpos : 0 < ζ.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) h2
    exact (hLL ζ h1 h2 h3).trans
      (Step1Good_bctl sz n hd0 h𝔠 h𝔠1 h𝔡 hτs0 hτs𝔠𝔡 hN1 hB hWO.1 hpos)
  have hrate := Step1Good_rate (τs := τs) hN0 hC₀ hc₀ e9 e12 e1118
  have hFC' : ∀ (v : Idx d (sz.L n) (sz.W n) → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t → 0 ≤ ε →
      ε ≤ c₀ →
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * m n ((Real.sqrt s : ℂ)⁻¹ * (w + E))‖ ≤ ε) →
      ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (m n ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
          |ρ - ρ₀| ≤ C₀ * (ε + t) := by
    intro v s t ε h1 h2 h3 h4 h5 h6
    obtain ⟨ρ, ρ₀, a, b, c, -⟩ := hFC (m n) E le_rfl hbn.1 hbn.2 v s t ε h1 h2 h3 h4 h5 h6
    exact ⟨ρ, ρ₀, a, b, c⟩
  have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = Nsz sz n := by
    exact_mod_cast sz.card_Idx n
  exact Step1Good_at_n (M.herm n ω) (m n) (ρ n) hδ hcb hK hC₀ hc₀ hc₁4 hτs0 hCV hNE hcard rfl hTc hT1
    hET (by linarith) hedge (e15.trans (min_le_left _ _)) e78
    (by linarith [e15.trans (min_le_right _ _)]) hrate hbn.1 hUn.2.2 hFC' hpt hnorm

/-- **Target 3b** `step1Good'`: **the owed pin `UNStep1Good'`** (`PinsDens.lean:73`, unchanged), from `step1Good'_det`,
`UNTrLocal` at `(τ_s/8, τ_s/8, D + 1)` and `UNNormBound` at `D + 1` (two bad events, `2 N^{-D-1} ≤ N^{-D}` for
`N ≥ 2`; RBM2D `step1Good_highProb`, `:817`). -/
theorem step1Good' : UNStep1Good' := by
  intro d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT CV₀ hCV hN τs D hτs0 hτs1 hτs𝔠𝔡 hD0
  obtain ⟨c, C, hc, hdet⟩ := step1Good'_det d hd 𝔠 𝔡 sz hA M m E ρ δ hD CV₀ hCV τs hτs0 hτs1 hτs𝔠𝔡
  refine ⟨c, C, hc, ?_⟩
  have hT1 := hT (τs / 8) (τs / 8) (D + 1) (by positivity) (by positivity) (by linarith)
  have hN1 := hN (D + 1) (by linarith)
  filter_upwards [hdet, hT1, hN1, (hA.2.2.1 : Tendsto (fun n => Nsz sz n) atTop atTop).eventually_ge_atTop 2]
    with n hdn hTn hNn hN2
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith
  set A : Set (Sizes.SeqΩ sz) := {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + τs / 8) ≤ z.im ∧
    z.im ≤ 1 ∧ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - z.im) <
      ‖stieltjesN (M.H n ω) z - m n z‖} with hAdef
  set B : Set (Sizes.SeqΩ sz) := {ω | ∃ i, Nsz sz n ^ CV₀ < |(M.herm n ω).eigenvalues i|} with hBdef
  have hsub : {ω | ¬ (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ⊆ A ∪ B := by
    intro ω hω
    by_contra hnot
    simp only [hAdef, hBdef, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and,
      not_lt] at hnot
    obtain ⟨h1, h2⟩ := hnot
    exact hω (hdn ω (fun z hz1 hz2 hz3 => h1 z hz1 hz2 hz3) (fun i => h2 i))
  calc M.μ _ ≤ M.μ (A ∪ B) := measure_mono hsub
    _ ≤ M.μ A + M.μ B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Nsz sz n ^ (-(D + 1))) + ENNReal.ofReal (Nsz sz n ^ (-(D + 1))) :=
        add_le_add hTn hNn
    _ = ENNReal.ofReal (Nsz sz n ^ (-(D + 1)) + Nsz sz n ^ (-(D + 1))) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)).symm
    _ ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : Nsz sz n ^ (-(D + 1)) = Nsz sz n ^ (-D) * (Nsz sz n)⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; congr 1; ring
        have hinv : (Nsz sz n)⁻¹ ≤ 1 / 2 := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) hN2
        have hpos : 0 ≤ Nsz sz n ^ (-D) := Real.rpow_nonneg hN0.le _
        rw [e]
        nlinarith

/-! ## 6. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2)

The data: `RBM.Gauss.SizesInst.sz0` (`d = 3`; `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `𝔠 = 1/6`,
`𝔡 = 1/10`, the band model, `m = msc`, `E = 0`, `ρ = rhoSC 0`, `δ = 1/2` (`un_dens'_msc_zero`), `τ_s = 1/60 = 𝔠𝔡`,
`D = 1` (the consumer's `D`, RBM2D `Step1Band.lean:1037`).  The band rows `UNLocAvgBand`, `UNTrLocalBandRow`,
`UNNormBandRow` are other gates' pins and stay hypotheses; every deterministic hypothesis is discharged.  The
conclusions are eventual in `n` (the size conditions hold only for `N ≳ e^{2290}` at these constants: the instances
do not use a concrete `n`; DECISIONS §56). -/

namespace Step1GoodInst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `inst_step1Good'_band`: `step1Good'` at the band model (`sz0`, `msc`, `E = 0`, `ρ = rhoSC 0`, `δ = 1/2`), the
local law from `UNTrLocalBandRow` at `κ = 1`, the norm bound from `UNNormBandRow`, `τ_s = 1/60`, `D = 1`. -/
theorem inst_step1Good'_band :
    UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
        (UNModel.band sz0).μ {ω | ¬ (IsRegular32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω)
              (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4))
              (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (CV₀ + 1) ∧
            ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω)
                (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧
              ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))} ≤
          ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) := by
  intro hLoc rT rN
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  refine ⟨CV₀, hCV, ?_⟩
  exact step1Good' 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))
    CV₀ hCV hN (1 / 60) 1 (by norm_num) (by norm_num) (by norm_num) one_pos

/-- `inst_step1Good'_det_band`: `step1Good'_det` at the same data (`CV₀ = 1`); the event hypotheses on `ω` stay
hypotheses (they hold only for `N ≳ e^{2290}` at these constants). -/
theorem inst_step1Good'_det_band :
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz0,
      (∀ z : ℂ, |z.re - 0| ≤ 1 / 2 → Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 8) ≤ z.im → z.im ≤ 1 →
        ‖stieltjesN ((UNModel.band sz0).H n ω) z - msc z‖ ≤
          ((sz0.W n : ℕ) : ℝ) ^ ((1 / 60 : ℝ) / 8) * sz0.Bctl n (1 - z.im)) →
      (∀ i, |((UNModel.band sz0).herm n ω).eigenvalues i| ≤ Nsz sz0 n ^ (1 : ℝ)) →
      (IsRegular32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω) (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4))
            (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (1 + 1) ∧
        ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω)
            (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧
          ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
            |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8))) :=
  step1Good'_det 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero 1 zero_le_one (1 / 60) (by norm_num) (by norm_num)
    (by norm_num)

/-- `inst_admissible_sz0`: the three `Admissible` facts at `sz0` (`d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`), from targets
2a-2c and `sz0_adm` (not by `norm_num`). -/
theorem inst_admissible_sz0 :
    (1 / 6 : ℝ) * ((3 : ℕ) : ℝ) < 1 ∧ (1 / 10 : ℝ) ≤ ((3 : ℕ) : ℝ) / 2 ∧ (1 / 6 : ℝ) * (1 / 10) < 1 / 2 :=
  ⟨un_admissible_c_mul_lt_one sz0 (by norm_num) sz0_adm, un_admissible_d_le_half sz0 sz0_adm,
    un_admissible_cd_lt_half sz0 (by norm_num) sz0_adm⟩

end Step1GoodInst

end RBM.Univ

end
