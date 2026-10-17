/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.EMn2Exp2
import RBM3D.Induction.Contract
import RBM3D.BA.FlowPins
import RBM3D.BA.KSolve
import RBM3D.BA.KInduct
import RBM3D.BA.Prop6Path
import RBM3D.BA.KKernel
import RBM3D.BA.GreenSchur
import RBM3D.BA.Ward

/-!
# Lemma 3.13 (`lem: EMn2_N`) at block Anderson

Paper: Lemma 3.13 (`lem: EMn2_N`) for the block Anderson model: (8.14) `eq:MG_conclusion3_BA`, (2.71) `Kn2sol`, `BAProp5`.

The three estimates of Lemma 3.13 hold over any carrier under the fact blocks
`emn2PolyFacts`, `emn2ExpFacts`, `emn2ExpHK` (`Induction/EMn2Poly.lean`, `EMn2Exp1.lean`, `EMn2Exp2.lean`).  This file
discharges the blocks at the BA reading `Flow := BAFlow`, `mk := baFMz`, `T0 := BAflowT0`, `Hf := baEMn2Hf` (`seqHflowBA` at
`BAflowLam0`), `ζf := baEMn2Zf` (`ztOf` at the real-axis `m_F`), and states the estimates at that reading.

* `baEMn2PolyFacts`, `baEMn2ExpFacts`: the clauses (A), (R), (S), (T), (E), (B) from `BAFlow`
  alone (constants in `(d, κ, 𝔡)`).
* `baComp_Q_row`, `baComp_Q_col`, `baComp_row_le`, `baComp_col_le`, `baComp_holds` (`BACompBound`): the composition `Θ_BA M^{(σσ')}` has row and column sums
  `≤ (1-t)⁻¹` and decays beyond `ℓ_t(g)`, for every charge pair.
* `baEMn2ExpHK`: `emn2ExpHK` from `(Kn2sol)` (`baKsol_two`) and `baComp_holds`.
* `baSTEMn2Poly`, `baSTEMn2Exp`: the estimates at the BA reading; the Green function hypotheses `STInitialGT2gL`,
  `STLWassmgL`, `STLWassmExpgL` are hypotheses of the statements `STEMn2PolygL`, `STEMn2ExpgL`.

No scalar `m`, no smallness of `g`, no `‖M - m₀ I‖` small.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The BA reading and the elementary flow facts -/

section Reading

variable {d : ℕ}

/-- The matrix `Hf` of the BA reading: `seqHflowBA` at the flow coupling `g₀ = BAflowLam0`. -/
def baEMn2Hf (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  sz.seqHflowBA (BAflowLam0 sz z) n u ω

/-- The spectral parameter `ζf` of the BA reading: `z_u = E_n + (1 - u) m_F`. -/
def baEMn2Zf (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) u

/-- `seqHflowBA` is Hermitian. -/
theorem EMn2BA_seqHflowBA_herm (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) :
    (sz.seqHflowBA lam0 n u ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- `S^{(B)}(0) = 1`: `sbKernel d L 0 = δ₀`. -/
theorem EMn2BA_SB_zero (L : ℕ) [NeZero L] : SB d L 0 = 1 := by
  ext a b
  simp only [SB_apply, sbKernel, Matrix.one_apply, sub_eq_zero]
  by_cases h : a = b
  · simp [h]
  · simp [h]

/-- `Im z_n > 0` on the chain domain (`N^{-1+ε} ≤ Im z_n`, `N ≥ 1`). -/
theorem EMn2BA_zim_pos {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im := by
  have h1 := (h.2 n).2.1
  have h2 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  linarith

/-- `0 < Im m(z_n, g_n)` on the chain domain (`BAdom`, `κ > 0`). -/
theorem EMn2BA_mim_pos {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im :=
  lt_of_lt_of_le hκ (h.2 n).1

/-- `Im m(z_n, g_n) ≤ ‖m‖ ≤ 1` (Ward, `BAm_norm_le_one`, uniform in `g`). -/
theorem EMn2BA_mim_le_one {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    (BAm d (sz.L n) (sz.lam n) (z n)).im ≤ 1 := by
  have hz := EMn2BA_zim_pos sz h n
  have hs := BAm_self d (sz.L n) (sz.lam n) (z n) hz
  exact (Complex.im_le_norm _).trans (BAm_norm_le_one d (sz.L n) (sz.lam n) (z n) _ hz.le hs)

/-- `t₀_n < 1`, every `n` (`BAt0_lt_one`). -/
theorem EMn2BA_T0_lt_one {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : BAflowT0 sz z n < 1 :=
  BAt0_lt_one (EMn2BA_zim_pos sz h n) (EMn2BA_mim_pos hκ sz h n)

/-- `1 - t₀_n ≥ Im z_n / 2` (`1 - t₀ = Im z/(Im m + Im z)`, `Im m ≤ 1`, `Im z ≤ 1`). -/
theorem EMn2BA_one_sub_T0 {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : (z n).im / 2 ≤ 1 - BAflowT0 sz z n := by
  have hz := EMn2BA_zim_pos sz h n
  have hm := EMn2BA_mim_pos hκ sz h n
  have hm1 := EMn2BA_mim_le_one sz h n
  have hz1 := (h.2 n).2.2
  have e : 1 - BAflowT0 sz z n = (z n).im / ((BAm d (sz.L n) (sz.lam n) (z n)).im + (z n).im) := by
    unfold BAflowT0 BAt0
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

/-- `Im m_F ≤ 1` and `κ ≤ Im m_F` at the flow parameters (`BAflow_real`). -/
theorem EMn2BA_mF_data {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    κ ≤ (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ∧
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≤ 1 := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z h n
  refine ⟨hr.2, (Complex.im_le_norm _).trans ?_⟩
  exact BAm_norm_le_one d (sz.L n) _ ((BAflowEs sz z n : ℝ) : ℂ) _ (by simp) hr.1

end Reading

/-! ## 2. The fact blocks -/

section Facts

variable (d : ℕ)

/-- **Clauses (A), (R), (S)**: `emn2PolyFacts` at the BA reading. -/
theorem baEMn2PolyFacts : emn2PolyFacts d BAFlow baFMz BAflowT0 baEMn2Hf baEMn2Zf := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  refine ⟨hflow.1, fun n u hu0 huT => ?_, fun n => ⟨0, ?_⟩⟩
  · have hT := EMn2BA_T0_lt_one hκ sz hflow n
    have hm := (EMn2BA_mF_data sz hflow n).1
    have hη : 0 < (1 - u) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im :=
      mul_pos (by linarith) (by linarith)
    refine ⟨fun ω => EMn2BA_seqHflowBA_herm sz _ n u ω, ?_, ?_, fun ω k σ a => rfl⟩
    · exact (ztOf_im _ _ _).symm ▸ hη
    · exact ztOf_im _ _ _
  · exact (EMn2BA_SB_zero (sz.L n)).symm

set_option maxHeartbeats 800000 in
-- the proof follows that of `ST_Bdata_holds` and needs the same heartbeat limit
/-- **Clauses (T), (E), (B)**: `emn2ExpFacts` at the BA reading.

(B) is the block Anderson analogue of `ST_Bdata_holds`: `Bctl` reads `sz.lam n = g`,
`cB = (𝔡⁻² + 1)⁻¹`, `c = min (2𝔡𝔠) ε / 2`; the upper bound is `(g² W^d)⁻¹ + (N(1-u))⁻¹ ≤ N^{-2𝔡𝔠} + 2N^{-ε}`
with `1 - u ≥ 1 - t₀ ≥ Im z_n / 2 ≥ N^{-1+ε}/2` (`EMn2BA_one_sub_T0`). -/
theorem baEMn2ExpFacts :
    emn2ExpFacts d BAFlow baFMz BAflowT0 baEMn2Hf baEMn2Zf := by
  refine ⟨baEMn2PolyFacts d, ?_⟩
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hT1 : ∀ n, BAflowT0 sz z n < 1 := fun n => EMn2BA_T0_lt_one hκ sz hflow n
  refine ⟨hT1, ?_, (𝔡⁻¹ ^ 2 + 1)⁻¹, min (2 * 𝔡 * 𝔠) ε / 2, by positivity, by
    have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith, ?_⟩
  · intro n u hu0 huT
    have hm := (EMn2BA_mF_data sz hflow n).2
    have hu1 : 0 < 1 - u := by linarith [hT1 n]
    change etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u ≤ 1 - u
    unfold etaOf
    nlinarith
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize := tendsto_size sz hsz
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hc1 : 2 * c ≤ 2 * 𝔡 * 𝔠 := by rw [hcdef]; have := min_le_left (2 * 𝔡 * 𝔠) ε; linarith
  have hc2 : 2 * c ≤ ε := by rw [hcdef]; have := min_le_right (2 * 𝔡 * 𝔠) ε; linarith
  rw [← hcdef]
  filter_upwards [hWO, hband, ST_size_pow_big sz hsize (a := c) (M := 5) hc,
    hsize.eventually (eventually_ge_atTop 1)] with n hwo hbn hN5 hN1 u hu0 hut
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hlt1 : u < 1 := lt_of_le_of_lt hut (hT1 n)
  have hlam : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hwo.1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hBp : Bparam d (sz.L n) (sz.lam n) u 0 =
      (sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    unfold Bparam
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - u)]
    simp
  have hBc : sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0 := rfl
  constructor
  · -- the lower bound
    rw [hBc, hBp, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hWd.le)
    have h1 : (sz.lam n ^ 2 + (1 - u))⁻¹ ≥ (𝔡⁻¹ ^ 2 + 1)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      have := pow_le_pow_left₀ hlam.le hwo.2 2
      linarith
    have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
      inv_nonneg.mpr (mul_nonneg hLd.le (by linarith))
    linarith
  · -- the upper bound
    have hz := EMn2BA_zim_pos sz hflow n
    have hu1 : (z n).im / 2 ≤ 1 - u := by
      have := EMn2BA_one_sub_T0 hκ sz hflow n
      linarith
    have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
    have hsz2 : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
      unfold Sizes.size; push_cast; ring
    -- `(N(1-u))⁻¹ ≤ 4 N^{-ε}`
    have hA : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤
        4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
      have h1 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ =
          (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [hsz2]; field_simp
      rw [h1]
      have hNε : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_pos_of_pos hN0 _
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4 ≤ 1 - u := by linarith
      have h3 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4) ≤
          ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul_of_nonneg_left h2 hN0.le
      have h4 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4) =
          ((sz.size n : ℕ) : ℝ) ^ ε / 4 := by
        have : ((sz.size n : ℕ) : ℝ) ^ ε = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
          conv_lhs => rw [show ε = 1 + (-1 + ε) by ring]
          rw [Real.rpow_add hN0, Real.rpow_one]
        rw [this]; ring
      rw [h4] at h3
      have h5 : 0 < ((sz.size n : ℕ) : ℝ) ^ ε / 4 := by positivity
      calc (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ ε / 4)⁻¹ :=
            inv_anti₀ h5 h3
        _ = 4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
            rw [Real.rpow_neg hN0.le]; field_simp
    -- `(W^d lam²)⁻¹ ≤ W^{-2𝔡} ≤ N^{-2𝔡𝔠}`
    have hB : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
      have h1 := Sizes.lam_sq_mul_pow_ge sz n hwo.1
      have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ =
          (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_comm, mul_inv]
      rw [h2]
      have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
      calc (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hW _) h1
        _ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := (Real.rpow_neg hW.le _).symm
        _ ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(2 * 𝔡)) :=
            Real.rpow_le_rpow_of_nonpos hNc hbn (by linarith)
        _ = ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
            rw [← Real.rpow_mul hN0.le]; congr 1; ring
    rw [hBc, hBp, mul_add]
    have hfirst : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith))
        (inv_nonneg.mpr hWd.le)
    have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤
        4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by rw [mul_comm]; exact hA
    have hN2c : ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hNe : ((sz.size n : ℕ) : ℝ) ^ (-ε) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hsum : 5 * ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) =
          ((sz.size n : ℕ) : ℝ) ^ (-c) * ((sz.size n : ℕ) : ℝ) ^ (-c) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      have h5 : 5 * ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ 1 := by
        have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ c := Real.rpow_pos_of_pos hN0 _
        rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_one hNc]
        linarith
      have hp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := Real.rpow_nonneg hN0.le _
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right h5 hp]
    linarith

end Facts

/-! ## 3. The composition `Θ_BA M^{(σσ')}` for every charge pair

`𝒦^{(2)}_{t,(σ,σ')} = W^{-d} (Θ^{(σσ')}_t M^{(σσ')})` (`(Kn2sol)`, `BAKsolve`).  Its marginals are `≤ (1-t)⁻¹` and it decays
beyond `ℓ_t(g)`: the sources are `baProp5_holds` (all `σ₁ σ₂`, rate `ellT L g t`), `BAK_row_sum`/`BAK_col_sum`
(`|M^{(σσ')}_{ab}| = BAK_{ab}`, `BAMss_norm_eq_BAK`) and `BAMB_decay_large`.  `baTheta_weighted_l1` covers
only `σ₁ = σ₂`.  Constants `(d, Λ, κ)`. -/

section Comp

variable {d L : ℕ} [NeZero L]

/-- `Σ_b |Θ(a,b)| ≤ (1-t)⁻¹` from `Θ = 1 + t Θ Q` and `Σ_b |Q(c,b)| ≤ 1`. -/
private theorem EMn2BA_row_of_resolvent {G : Type*} [Fintype G] [DecidableEq G] (Θ Q : Matrix G G ℂ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hres : Θ = 1 + (t : ℂ) • (Θ * Q))
    (hQ : ∀ c, ∑ b, ‖Q c b‖ ≤ 1) (a : G) : ∑ b, ‖Θ a b‖ ≤ (1 - t)⁻¹ := by
  set R : ℝ := ∑ b, ‖Θ a b‖ with hR
  have hpt : ∀ b, ‖Θ a b‖ ≤ (if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Θ a c‖ * ‖Q c b‖ := by
    intro b
    have h := congrFun (congrFun hres a) b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.mul_apply] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if a = b then (1 : ℂ) else 0)‖ = if a = b then (1 : ℝ) else 0 := by split_ifs <;> simp
    have h2 : ‖(t : ℂ) * ∑ c, Θ a c * Q c b‖ ≤ t * ∑ c, ‖Θ a c‖ * ‖Q c b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) ht0
      exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    rw [h1]
    linarith
  have hsum : R ≤ 1 + t * R := by
    calc R = ∑ b, ‖Θ a b‖ := rfl
      _ ≤ ∑ b, ((if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Θ a c‖ * ‖Q c b‖) := Finset.sum_le_sum fun b _ => hpt b
      _ = 1 + t * ∑ c, ‖Θ a c‖ * ∑ b, ‖Q c b‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
      _ ≤ 1 + t * ∑ c, ‖Θ a c‖ * 1 := by
          gcongr with c _
          exact hQ c
      _ = 1 + t * R := by simp [hR]
  have h1t : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h1t]
  nlinarith

/-- `Σ_a |Θ(a,b)| ≤ (1-t)⁻¹` from `Θ = 1 + t Q Θ` and `Σ_a |Q(a,c)| ≤ 1`. -/
private theorem EMn2BA_col_of_resolvent {G : Type*} [Fintype G] [DecidableEq G] (Θ Q : Matrix G G ℂ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hres : Θ = 1 + (t : ℂ) • (Q * Θ))
    (hQ : ∀ c, ∑ a, ‖Q a c‖ ≤ 1) (b : G) : ∑ a, ‖Θ a b‖ ≤ (1 - t)⁻¹ := by
  set R : ℝ := ∑ a, ‖Θ a b‖ with hR
  have hpt : ∀ a, ‖Θ a b‖ ≤ (if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Q a c‖ * ‖Θ c b‖ := by
    intro a
    have h := congrFun (congrFun hres a) b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.mul_apply] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if a = b then (1 : ℂ) else 0)‖ = if a = b then (1 : ℝ) else 0 := by split_ifs <;> simp
    have h2 : ‖(t : ℂ) * ∑ c, Q a c * Θ c b‖ ≤ t * ∑ c, ‖Q a c‖ * ‖Θ c b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) ht0
      exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    rw [h1]
    linarith
  have hsum : R ≤ 1 + t * R := by
    calc R = ∑ a, ‖Θ a b‖ := rfl
      _ ≤ ∑ a, ((if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Q a c‖ * ‖Θ c b‖) := Finset.sum_le_sum fun a _ => hpt a
      _ = 1 + t * ∑ c, (∑ a, ‖Q a c‖) * ‖Θ c b‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul]
      _ ≤ 1 + t * ∑ c, 1 * ‖Θ c b‖ := by
          gcongr with c _
          exact hQ c
      _ = 1 + t * R := by simp [hR]
  have h1t : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h1t]
  nlinarith

/-- The row sums of `|Q|`, `Q = M^{(σ₁σ₂)}`: `Σ_b |Q_{cb}| = Σ_b BAK_{cb} = 1`. -/
theorem baComp_Q_row {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) (c : Zd d L) :
    ∑ b, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ = 1 := by
  simp only [BAMss_norm_eq_BAK]
  exact BAK_row_sum d L g E m hr.1 c

/-- The column sums of `|Q|`: `Σ_a |Q_{ac}| = Σ_a BAK_{ac} = 1`. -/
theorem baComp_Q_col {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) (c : Zd d L) :
    ∑ a, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a c‖ = 1 := by
  simp only [BAMss_norm_eq_BAK]
  exact BAK_col_sum d L g E m hr.1 c

/-- **`Σ_b |Θ^{(σ₁σ₂)}_t(a,b)| ≤ (1-t)⁻¹`**, all four charge pairs. -/
theorem baTheta_row_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) (a : Zd d L) : ∑ b, ‖BATheta d L g E m t σ₁ σ₂ a b‖ ≤ (1 - t)⁻¹ :=
  EMn2BA_row_of_resolvent _ _ ht0 ht1 (BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂).2
    (fun c => (baComp_Q_row hr σ₁ σ₂ c).le) a

/-- **`Σ_a |Θ^{(σ₁σ₂)}_t(a,b)| ≤ (1-t)⁻¹`**, all four charge pairs. -/
theorem baTheta_col_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) (b : Zd d L) : ∑ a, ‖BATheta d L g E m t σ₁ σ₂ a b‖ ≤ (1 - t)⁻¹ :=
  EMn2BA_col_of_resolvent _ _ ht0 ht1 (BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂).1
    (fun c => (baComp_Q_col hr σ₁ σ₂ c).le) b

/-- **Rows of the composition**: `Σ_b |(Θ M^{(σ₁σ₂)})(a,b)| ≤ (1-t)⁻¹`. -/
theorem baComp_row_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) (a : Zd d L) :
    ∑ b, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤ (1 - t)⁻¹ := by
  calc ∑ b, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖
      ≤ ∑ b, ∑ c, ‖BATheta d L g E m t σ₁ σ₂ a c‖ * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    _ = ∑ c, ‖BATheta d L g E m t σ₁ σ₂ a c‖ * ∑ b, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ c, ‖BATheta d L g E m t σ₁ σ₂ a c‖ := by
        simp only [baComp_Q_row hr, mul_one]
    _ ≤ (1 - t)⁻¹ := baTheta_row_le hr ht0 ht1 σ₁ σ₂ a

/-- **Columns of the composition**: `Σ_a |(Θ M^{(σ₁σ₂)})(a,b)| ≤ (1-t)⁻¹`. -/
theorem baComp_col_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) (b : Zd d L) :
    ∑ a, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤ (1 - t)⁻¹ := by
  calc ∑ a, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖
      ≤ ∑ a, ∑ c, ‖BATheta d L g E m t σ₁ σ₂ a c‖ * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    _ = ∑ c, (∑ a, ‖BATheta d L g E m t σ₁ σ₂ a c‖) * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ c, (1 - t)⁻¹ * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_right (baTheta_col_le hr ht0 ht1 σ₁ σ₂ c) (norm_nonneg _)
    _ = (1 - t)⁻¹ * ∑ c, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ := (Finset.mul_sum _ _ _).symm
    _ = (1 - t)⁻¹ := by
        have := baComp_Q_col hr σ₁ σ₂ b
        simp only [this, mul_one]

/-- `‖Θ(a,c)‖ = ‖Θ(0, c - a)‖`, translation invariance (`baP8_BATheta_shift`, every `(σ₁, σ₂)`). -/
theorem EMn2BA_theta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a c : Zd d L) :
    BATheta d L g E m t σ₁ σ₂ a c = BATheta d L g E m t σ₁ σ₂ 0 (c - a) := by
  have h := baP8_BATheta_shift (d := d) (L := L) g E m t σ₁ σ₂ a c (-a)
  simp only [add_neg_cancel, ← sub_eq_add_neg] at h
  exact h.symm

/-- `B_{t,K} ≤ 2 (1-t)⁻¹` for `t < 1`, `L ≥ 1`. -/
theorem EMn2BA_bparam_le (d L : ℕ) (hL : 1 ≤ L) (g : ℝ) {u : ℝ} (hu : u < 1) (n : ℕ) :
    Bparam d L g u n ≤ 2 * (1 - u)⁻¹ := by
  have hx : 0 < 1 - u := by linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold Bparam
  rw [abs_of_pos hx]
  have hxi : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr hx.le
  have h1 : (g ^ 2 + (1 - u))⁻¹ * (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ := by
    have a1 : (g ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hx (by nlinarith [sq_nonneg g])
    have a2 : (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc (g ^ 2 + (1 - u))⁻¹ * (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ * 1 :=
          mul_le_mul a1 a2 (by positivity) hxi
      _ = (1 - u)⁻¹ := mul_one _
  have h2 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
    exact inv_anti₀ hx (by nlinarith)
  linarith

end Comp

/-- **The composition bound** (statement shape as `BAProp5`): for `3 ≤ d`, `Λ, κ > 0` there are `C, c > 0` (depending on `(d, Λ, κ)` only), fixed before
`L, g, E, m`, such that for `0 < g ≤ Λ`, `L ≥ 3`, the real-axis datum `BAReal d L g κ E m`, `0 ≤ t < 1` and **every** pair
`σ₁ σ₂ ∈ {±}` (the mixed pair `(+,-)` included): the marginals of `Θ^{(σ₁σ₂)}_t M^{(σ₁σ₂)}` are `≤ (1-t)⁻¹`, and
`|(Θ M)(a,b)| ≤ C (1-t)⁻¹ exp(-c |a - b|_L / ℓ_t(g))` (`ellT L g t`, the rate of `BAProp5`).  No `L^d` volume factor, no smallness
of `g`, no scalar `m`. -/
def BACompBound (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool,
          (∀ a : Zd d L, ∑ b, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤ (1 - t)⁻¹) ∧
          (∀ b : Zd d L, ∑ a, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤ (1 - t)⁻¹) ∧
          ∀ a b : Zd d L, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤
            C * (1 - t)⁻¹ * Real.exp (-c * (zdistD d L (a - b) : ℝ) / ellT L g t)

/-- **`BACompBound` holds** (all constants in `(d, Λ, κ)`): `C = 2 C₅ + c₀⁻²`, `c = min (c₅ / 2) c₀` with `(C₅, c₅)` from `baProp5_holds` and
`c₀ = BAct_rate d Λ κ`.  Proof: `Σ_c |Θ(a,c)| |Q(c,b)|`, `|a - b| ≤ |a - c| + |c - b|`; the case `|a - c| ≥ |a - b|/2` uses `BAProp5` for
`Θ` and `Σ_c |Q(c,b)| = 1`; the case `|c - b| ≥ |a - b|/2` uses `|Q_{cb}| = |M^{(B)}_{cb}|²` and `(Mbound_AO2)` (`BAMB_decay_large`),
`ℓ_t ≥ 1`, and `Σ_c |Θ(a,c)| ≤ (1-t)⁻¹`. -/
theorem baComp_holds (d : ℕ) (Λ κ : ℝ) : BACompBound d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := baProp5_holds d Λ κ hd hΛ hκ
  have hd0 : 0 < d := by omega
  have hc₀ := BAct_rate_pos d Λ κ hd0 hΛ hκ
  set c₀ := BAct_rate d Λ κ with hc₀def
  refine ⟨2 * C₅ + c₀⁻¹ ^ 2, by positivity, min (c₅ / 2) c₀, lt_min (by positivity) hc₀, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂
  have : NeZero L := ⟨by omega⟩
  refine ⟨baComp_row_le hr ht0 ht1 σ₁ σ₂, baComp_col_le hr ht0 ht1 σ₁ σ₂, fun a b => ?_⟩
  set Θ := BATheta d L g E m t σ₁ σ₂ with hΘdef
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ with hQdef
  set ℓ := ellT L g t with hℓdef
  have hℓ1 : 1 ≤ ℓ := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ L))
  have hℓ0 : 0 < ℓ := by linarith
  set r : ℝ := (zdistD d L (a - b) : ℝ) with hr_def
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have h1t : 0 < 1 - t := by linarith
  have hinv0 : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr h1t.le
  have hc1 : min (c₅ / 2) c₀ ≤ c₅ / 2 := min_le_left _ _
  have hc2 : min (c₅ / 2) c₀ ≤ c₀ := min_le_right _ _
  have hcpos : 0 < min (c₅ / 2) c₀ := lt_min (by positivity) hc₀
  -- pointwise bound for the two cases
  have hpt : ∀ c : Zd d L, ‖Θ a c‖ * ‖Q c b‖ ≤
      (2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ)) * ‖Q c b‖ +
        ‖Θ a c‖ * (c₀⁻¹ ^ 2 * Real.exp (-c₀ * r)) := by
    intro c
    have hadd : zdistD d L (a - b) ≤ zdistD d L (a - c) + zdistD d L (c - b) := by
      have := zdistD_add_le d L (a - c) (c - b)
      rwa [show a - c + (c - b) = a - b by ring] at this
    have hQnn : 0 ≤ ‖Q c b‖ := norm_nonneg _
    have hΘnn : 0 ≤ ‖Θ a c‖ := norm_nonneg _
    by_cases hcase : zdistD d L (a - b) ≤ 2 * zdistD d L (a - c)
    · -- `Θ` carries the decay
      have h5 := H5 L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ (c - a)
      have hB := EMn2BA_bparam_le d L (by omega) g ht1 (zdistD d L (c - a))
      have hdist : zdistD d L (c - a) = zdistD d L (a - c) := by
        rw [← neg_sub a c, zdistD_neg]
      have hx : r ≤ 2 * (zdistD d L (c - a) : ℝ) := by
        rw [hdist, hr_def]; exact_mod_cast hcase
      have hexp : Real.exp (-c₅ * (zdistD d L (c - a) : ℝ) / ℓ) ≤ Real.exp (-(c₅ / 2) * r / ℓ) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_div_iff_of_pos_right hℓ0]
        nlinarith
      have hΘc : ‖Θ 0 (c - a)‖ ≤ 2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ) := by
        calc ‖Θ 0 (c - a)‖ ≤ C₅ * Bparam d L g t (zdistD d L (c - a)) *
              Real.exp (-c₅ * (zdistD d L (c - a) : ℝ) / ℓ) := h5
          _ ≤ C₅ * (2 * (1 - t)⁻¹) * Real.exp (-(c₅ / 2) * r / ℓ) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hB hC₅.le) hexp (Real.exp_pos _).le (by positivity)
          _ = 2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ) := by ring
      have hsh : Θ a c = Θ 0 (c - a) := EMn2BA_theta_shift g E m t σ₁ σ₂ a c
      have hmain : ‖Θ a c‖ * ‖Q c b‖ ≤ (2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ)) * ‖Q c b‖ :=
        mul_le_mul_of_nonneg_right (by rw [hsh]; exact hΘc) hQnn
      have hsec : 0 ≤ ‖Θ a c‖ * (c₀⁻¹ ^ 2 * Real.exp (-c₀ * r)) := by positivity
      linarith
    · -- `Q` carries the decay
      have hcase' : zdistD d L (a - b) ≤ 2 * zdistD d L (c - b) := by omega
      have hM := BAMB_decay_large (d := d) (L := L) hL hd0 Λ g κ E m hΛ hg hgΛ hκ hr c b
      have hQe : ‖Q c b‖ = ‖BAMB d L g (E : ℂ) m c b‖ ^ 2 := by
        rw [hQdef, BAMss_norm_eq_BAK, BAK_apply]
      have hx : r ≤ 2 * (zdistD d L (c - b) : ℝ) := by rw [hr_def]; exact_mod_cast hcase'
      have hMn : 0 ≤ ‖BAMB d L g (E : ℂ) m c b‖ := norm_nonneg _
      have hQb : ‖Q c b‖ ≤ c₀⁻¹ ^ 2 * Real.exp (-c₀ * r) := by
        rw [hQe]
        calc ‖BAMB d L g (E : ℂ) m c b‖ ^ 2
            ≤ (c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (c - b) : ℝ))) ^ 2 :=
              pow_le_pow_left₀ hMn hM 2
          _ = c₀⁻¹ ^ 2 * Real.exp (-c₀ * (2 * (zdistD d L (c - b) : ℝ))) := by
              rw [mul_pow, ← Real.exp_nat_mul]
              congr 2
              push_cast; ring
          _ ≤ c₀⁻¹ ^ 2 * Real.exp (-c₀ * r) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
              nlinarith
      have hmain : ‖Θ a c‖ * ‖Q c b‖ ≤ ‖Θ a c‖ * (c₀⁻¹ ^ 2 * Real.exp (-c₀ * r)) :=
        mul_le_mul_of_nonneg_left hQb hΘnn
      have hsec : 0 ≤ (2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ)) * ‖Q c b‖ := by positivity
      linarith
  -- sum over `c`
  have hsum : ‖(Θ * Q) a b‖ ≤ 2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ) +
      c₀⁻¹ ^ 2 * Real.exp (-c₀ * r) * (1 - t)⁻¹ := by
    calc ‖(Θ * Q) a b‖ ≤ ∑ c, ‖Θ a c‖ * ‖Q c b‖ := by
          rw [Matrix.mul_apply]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun c _ => norm_mul _ _
      _ ≤ ∑ c, ((2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ)) * ‖Q c b‖ +
            ‖Θ a c‖ * (c₀⁻¹ ^ 2 * Real.exp (-c₀ * r))) := Finset.sum_le_sum fun c _ => hpt c
      _ = (2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ)) * ∑ c, ‖Q c b‖ +
            (∑ c, ‖Θ a c‖) * (c₀⁻¹ ^ 2 * Real.exp (-c₀ * r)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ 2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ) +
            (1 - t)⁻¹ * (c₀⁻¹ ^ 2 * Real.exp (-c₀ * r)) := by
          rw [baComp_Q_col hr σ₁ σ₂ b, mul_one]
          gcongr
          exact baTheta_row_le hr ht0 ht1 σ₁ σ₂ a
      _ = _ := by ring
  have e1 : Real.exp (-(c₅ / 2) * r / ℓ) ≤ Real.exp (-(min (c₅ / 2) c₀) * r / ℓ) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff_of_pos_right hℓ0]
    nlinarith
  have e2 : Real.exp (-c₀ * r) ≤ Real.exp (-(min (c₅ / 2) c₀) * r / ℓ) := by
    apply Real.exp_le_exp.mpr
    have : -c₀ * r ≤ -c₀ * r / ℓ := by
      rw [le_div_iff₀ hℓ0]; nlinarith [mul_nonneg hc₀.le hr0]
    have h2 : -c₀ * r / ℓ ≤ -(min (c₅ / 2) c₀) * r / ℓ := by
      rw [div_le_div_iff_of_pos_right hℓ0]; nlinarith
    linarith
  calc ‖(Θ * Q) a b‖ ≤ 2 * C₅ * (1 - t)⁻¹ * Real.exp (-(c₅ / 2) * r / ℓ) +
        c₀⁻¹ ^ 2 * Real.exp (-c₀ * r) * (1 - t)⁻¹ := hsum
    _ ≤ 2 * C₅ * (1 - t)⁻¹ * Real.exp (-(min (c₅ / 2) c₀) * r / ℓ) +
        c₀⁻¹ ^ 2 * Real.exp (-(min (c₅ / 2) c₀) * r / ℓ) * (1 - t)⁻¹ := by
        gcongr
    _ = (2 * C₅ + c₀⁻¹ ^ 2) * (1 - t)⁻¹ * Real.exp (-(min (c₅ / 2) c₀) * r / ℓ) := by ring

/-! ## 4. `emn2ExpHK` at the BA reading -/

section HK

/-- `ℓ_t` is nondecreasing in the coupling: `0 ≤ g₀ ≤ g` gives `ℓ_t(g₀) ≤ ℓ_t(g)` (`ellT_mono` is monotonicity in `t`). -/
theorem EMn2BA_ellT_mono_g (L : ℕ) {g₀ g : ℝ} (h : g₀ ≤ g) (t : ℝ) : ellT L g₀ t ≤ ellT L g t := by
  unfold ellT
  exact min_le_min (max_le_max (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)) le_rfl) le_rfl

/-- The closing inequality of the far field, for `x = log W ≥ 1` with `2C + k + |D| ≤ c δ √x`:
`2C e^{x k} e^{-c δ x^{3/2}} ≤ e^{-x D}`. -/
private theorem EMn2BA_arith {C c δ D k x : ℝ} (hC : 0 < C) (hx1 : 1 ≤ x)
    (hsq : 2 * C + k + |D| ≤ c * δ * Real.sqrt x) :
    C * (2 * Real.exp (x * k)) * Real.exp (-(c * δ * x ^ ((3 : ℝ) / 2))) ≤
      Real.exp (x * (-D)) := by
  have hx0 : 0 < x := by linarith
  have h32 : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
    have h : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
    rw [h, Real.rpow_add hx0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h1 : 2 * C ≤ Real.exp (2 * C) := by
    have := Real.add_one_le_exp (2 * C); linarith
  have h2 : 2 * C + x * k - c * δ * x ^ ((3 : ℝ) / 2) ≤ x * (-D) := by
    rw [h32]
    have hDx : D * x ≤ |D| * x := mul_le_mul_of_nonneg_right (le_abs_self D) hx0.le
    have hCx : 2 * C ≤ 2 * C * x := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq hx0.le
    nlinarith
  calc C * (2 * Real.exp (x * k)) * Real.exp (-(c * δ * x ^ ((3 : ℝ) / 2)))
      = (2 * C) * Real.exp (x * k) * Real.exp (-(c * δ * x ^ ((3 : ℝ) / 2))) := by ring
    _ ≤ Real.exp (2 * C) * Real.exp (x * k) * Real.exp (-(c * δ * x ^ ((3 : ℝ) / 2))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (2 * C + x * k - c * δ * x ^ ((3 : ℝ) / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]; rfl
    _ ≤ Real.exp (x * (-D)) := Real.exp_le_exp.mpr h2

/-- **`(Kn2sol)` at the carrier**: `𝒦^{(2)}_{t,(s,-s)}(x,x') = W^{-d} (Θ M^{(s,-s)})(x,x')` at `(g₀, E_n, m_F)`
(`baKsol_two`; needs `0 < g₀`, `BAReal` from `BAflow_real`). -/
theorem EMn2BA_K_two {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) (hg : 0 < BAflowLam0 sz z n) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) (x x' : Zd d (sz.L n)) :
    (baFMz sz z).K n t ![s, !s] ![x, x'] =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
        (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t s (!s) *
          BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ)
            (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) s (!s)) x x' :=
  baKsol_two d hκ hg (sz.three_le_L n) (sz.W n) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) ht ![s, !s] ![x, x']

/-- **`emn2ExpHK` at the BA reading** (`3 ≤ d`): for every `D > 0`, eventually, `‖𝒦^{(2)}_{t_n,(s,-s),(x,x')}‖ ≤
W^{-d} W^{-(D+d)}` once `ℓ*_{t_n}(g) ≤ |x - x'|_∞`.  Proof: `(Kn2sol)` (`EMn2BA_K_two`) and `baComp_holds` (`Λ = 𝔡⁻¹`) at the
flow coupling `g₀ ≤ g`: `ℓ_t(g₀) ≤ ℓ_t(g)` (`EMn2BA_ellT_mono_g`), `|x - x'|_∞ ≤ |x - x'|_L`; the amplitude is
`(1-t_n)⁻¹ ≤ 2N ≤ 2W^{1/𝔠}` (`1 - t₀ ≥ Im z/2 ≥ N^{-1}/2`, `Bandwidth`) and `(log W)^{3/2}` beats `log W` (`EMn2BA_arith`). -/
theorem baEMn2ExpHK (hd : 3 ≤ d) : emn2ExpHK d BAFlow baFMz BAflowT0 := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT D hD
  obtain ⟨C, hC, c, hc, H⟩ := baComp_holds d 𝔡⁻¹ κ hd (inv_pos.mpr h𝔡) hκ
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hNc : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hsz
  have hWtop : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := tendsto_atTop_mono' _ hband hNc
  have hxtop : Tendsto (fun n => Real.log ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hWtop
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * C + 1 / 𝔠 + |D + (d : ℝ)| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hX := (tendsto_atTop.1 hxtop) (max 1 ((K / c) ^ 2))
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, hband, hX, hflow.1.2.2.2.2] with n hlam hBn hXn hwo x x' s hfar
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hx1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hXn
  have hx0 : 0 < Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  have hsq : 2 * C + 1 / 𝔠 + |D + (d : ℝ)| ≤ c * 1 * Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ)) := by
    have hA' : 0 ≤ K / c := by positivity
    have h1 : (K / c) ^ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ) := (le_max_right _ _).trans hXn
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hA', div_le_iff₀ hc] at h2
    rw [← hK]
    linarith
  have ht1 : t n < 1 := lt_of_le_of_lt (htT n) (EMn2BA_T0_lt_one hκ sz hflow n)
  have hx : 0 < 1 - t n := by linarith
  -- the amplitude `(1 - t_n)⁻¹ ≤ 2 W^{1/𝔠}`
  have hNpos : 0 < sz.size n := by
    unfold Sizes.size
    exact pow_pos (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega)) d
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hamp : (1 - t n)⁻¹ ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
    have hz := EMn2BA_zim_pos sz hflow n
    have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
    have hNim' : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hT := EMn2BA_one_sub_T0 hκ sz hflow n
    have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) := Real.rpow_pos_of_pos hN0 _
    have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2 ≤ 1 - t n := by linarith [htT n]
    have h3 : (1 - t n)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2)⁻¹ :=
      inv_anti₀ (by positivity) h2
    have h4 : (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2)⁻¹ = 2 * ((sz.size n : ℕ) : ℝ) := by
      rw [Real.rpow_neg_one]; field_simp
    have h5 : ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
      have := sz.size_rpow_le_W_rpow h𝔠 n hBn (τ := 1) zero_le_one
      rwa [Real.rpow_one] at this
    rw [h4] at h3
    linarith
  -- the composition bound at `g₀`
  obtain ⟨hg0, hgΛ⟩ := hlam
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hCK := (H (sz.L n) (sz.three_le_L n) _ hg0 hgΛ _ _ hr (t n) (ht0 n) ht1 s (!s)).2.2 x x'
  have hK2 := EMn2BA_K_two hκ sz hflow n hg0 ⟨ht0 n, ht1⟩ s x x'
  rw [hK2]
  have hlam_le : BAflowLam0 sz z n ≤ sz.lam n := by
    have h1 : Real.sqrt (BAflowT0 sz z n) ≤ 1 :=
      Real.sqrt_le_one.mpr (EMn2BA_T0_lt_one hκ sz hflow n).le
    have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
    have e : BAflowLam0 sz z n = Real.sqrt (BAflowT0 sz z n) * sz.lam n := rfl
    rw [e]
    nlinarith
  -- the far condition and the exponential
  have hℓ0 : 0 < ellT (sz.L n) (BAflowLam0 sz z n) (t n) :=
    ellT_pos (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
  have hmono := EMn2BA_ellT_mono_g (sz.L n) hlam_le (t n)
  have hdist : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (BAflowLam0 sz z n) (t n) ≤
      (zdistD d (sz.L n) (x - x') : ℝ) := by
    refine le_trans ?_ ((hfar.trans (by exact_mod_cast zdistInf_le_zdistD d (sz.L n) (x - x'))))
    unfold emn2ExpEllStar
    exact mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hx0.le _)
  have hexp : Real.exp (-c * (zdistD d (sz.L n) (x - x') : ℝ) / ellT (sz.L n) (BAflowLam0 sz z n) (t n)) ≤
      Real.exp (-(c * 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_div, neg_le_neg_iff, le_div_iff₀ hℓ0]
    nlinarith
  -- the norm
  have hnorm : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) s (!s) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) s (!s)) x x'‖ =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖(BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) s (!s) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) s (!s)) x x'‖ := by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_nonneg hWpos.le d))
  calc _ ≤ C * (1 - t n)⁻¹ * Real.exp (-c * (zdistD d (sz.L n) (x - x') : ℝ) /
        ellT (sz.L n) (BAflowLam0 sz z n) (t n)) := hCK
    _ ≤ C * (2 * ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠)) *
          Real.exp (-(c * 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hamp hC.le) hexp (Real.exp_pos _).le (by positivity)
    _ = C * (2 * Real.exp (Real.log ((sz.W n : ℕ) : ℝ) * (1 / 𝔠))) *
          Real.exp (-(c * 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) := by
        rw [Real.rpow_def_of_pos hWpos]
    _ ≤ Real.exp (Real.log ((sz.W n : ℕ) : ℝ) * (-(D + (d : ℝ)))) := EMn2BA_arith hC hx1 hsq
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(D + (d : ℝ))) := (Real.rpow_def_of_pos hWpos _).symm

end HK

/-! ## 5. The estimates of Lemma 3.13 at the BA reading

The law is `Sizes.seqP (sz.withLam 0)` (`S^{(B)}(0) = I`), the setting `BAFlow`, the carrier `baFMz`, the horizon
`BAflowT0`.  The three Green function hypotheses `STInitialGT2gL`, `STLWassmgL`, `STLWassmExpgL` remain hypotheses of the statements.
The "second estimate" of Lemma 3.13 is (3.35) `eq:MG_conclusion3`: the `J` form and the `Ĵ`
form below; (3.34) `eq:MG_conclusion2` is the special case of the first estimate at `Ψ = (W^{-c₀} B_{t,|a-b|∧K})^{1/2}` and has no Lean form
in `RBM3D/`. -/

section Pins

variable (d : ℕ)

/-- **The first estimate** (3.33) `eq:MG_conclusion` at the BA reading: `STEMn2PolygL`, by `stEMn2PolygL_of`.
All `d` (no `3 ≤ d` is assumed); constants in `(d, κ, 𝔡)`. -/
theorem baSTEMn2Poly :
    STEMn2PolygL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  stEMn2PolygL_of _ (baEMn2PolyFacts d)

/-- **The `Ĵ` form** (`3 ≤ d`): `STEMn2ExpgL` at the BA reading, `stEMn2ExpgL_of` (the `J = Ĵ` corollary, every `D > 0`). -/
theorem baSTEMn2Exp (hd : 3 ≤ d) :
    STEMn2ExpgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  stEMn2ExpgL_of _ hd (baEMn2ExpFacts d) (baEMn2ExpHK hd)

end Pins

end RBM.BA
