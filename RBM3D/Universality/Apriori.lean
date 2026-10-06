/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.OU
import RBM3D.Universality.InjSum
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The a priori bound `UNApriori` from the tracial local law (T2275, UN-18b, Apriori half)

Paper: RBM2D paper `1-2:352-356` (the a priori input of `(417)`, RBM1D `AprioriImM`), as cited by
`Universality/Pins.lean:520`.  Port of RBM2D `Universality/Apriori.lean` (commit `c9a24cf`,
424 lines; there from `locSC`, error `W^τ/√Meta`, band only) onto the merged inputs, for every
`M : UNModel sz`.

* `apriori_im_bounds` (target 1): `0 ≤ Im m(E + iη) ≤ 1/η`.
* `apriori_im_le_of_near` (target 2): `‖m(E + iη₁) - w‖ ≤ ζ`, `0 < η₀ ≤ η₁` gives
  `Im m(E + iη₀) ≤ (η₁/η₀)(Im w + ζ)`.
* `apriori_ouMat_zero_integral` (target 3): the law transfer at `t = 0`, for every model.
* `apriori_bctl_le` (target 4): `Bctl n (1 - η) ≤ W^{-2𝔡} + (N η)⁻¹` under the lower half of
  `(eq:WO)`.
* `unApriori_of_trLocal` (target 5): `UNApriori sz M E` from `UNDens` and `UNTrLocal` near `E`.
* `unApriori_band_of_rows` (target 6): the band row from `UNTrLocalBandRow`, `UNDensBandRow`.

Changes against RBM2D: `locSC`/`Meta` (`apriori_ratio_le_one`, 60 lines) are replaced by the tracial
`UNTrLocal` with error `W^τ Bctl n (1 - Im z)` and target 4 (`lam_sq_mul_pow_ge`, `Bctl`);
the entrywise diagonal sum of `apriori_good_bound` disappears (the input is already tracial);
the measurability helpers `apriori_measurable_*` are not needed (transfer by `ouMat_zero` and
`integral_fun_fst`); `W ≤ N` is `Sizes.W_rpow_le`.  `UNTrLocal` is owed (MA/BA) and stays a
hypothesis.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal

/-! ### Deterministic facts -/

/-- Target 1 (RBM2D `Apriori.lean:32`): `0 ≤ Im m(E + iη) ≤ 1/η`. -/
theorem apriori_im_bounds {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (E η : ℝ) (hη : 0 < η) :
    0 ≤ (stieltjesN H ((E : ℂ) + (η : ℂ) * Complex.I)).im ∧
      (stieltjesN H ((E : ℂ) + (η : ℂ) * Complex.I)).im ≤ 1 / η := by
  rw [stieltjesN_im_eq_normalized_specWeight H hH E η hη]
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · refine mul_nonneg (inv_nonneg.2 hc.le) (Finset.sum_nonneg fun l _ => ?_)
    positivity
  · calc (Fintype.card ι : ℝ)⁻¹ * ∑ l : ι, (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _l : ι, (1 / η) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (inv_nonneg.2 hc.le)
          rw [div_le_div_iff₀ (by positivity) hη]
          nlinarith [sq_nonneg (hH.eigenvalues l - E)]
      _ = 1 / η := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- Target 2 (RBM2D `apriori_good_bound` `:192` without `Meta`): the monotonicity of `η Im m(E + iη)`
and the closeness of `m(E + iη₁)` to `w` bound `Im m(E + iη₀)`. -/
theorem apriori_im_le_of_near {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (E η₀ η₁ : ℝ) (w : ℂ) (ζ : ℝ) (h0 : 0 < η₀) (h01 : η₀ ≤ η₁)
    (hnear : ‖stieltjesN H ((E : ℂ) + (η₁ : ℂ) * Complex.I) - w‖ ≤ ζ) :
    (stieltjesN H ((E : ℂ) + (η₀ : ℂ) * Complex.I)).im ≤ η₁ / η₀ * (w.im + ζ) := by
  have hmono := stieltjesN_eta_mul_im_mono H hH E η₀ η₁ h0 h01
  have h1 : 0 < η₁ := lt_of_lt_of_le h0 h01
  have him : (stieltjesN H ((E : ℂ) + (η₁ : ℂ) * Complex.I)).im ≤ w.im + ζ := by
    have h2 : (stieltjesN H ((E : ℂ) + (η₁ : ℂ) * Complex.I) - w).im ≤ ζ :=
      (Complex.im_le_norm _).trans hnear
    rw [Complex.sub_im] at h2
    linarith
  have h3 : η₀ * (stieltjesN H ((E : ℂ) + (η₀ : ℂ) * Complex.I)).im ≤ η₁ * (w.im + ζ) :=
    hmono.trans (mul_le_mul_of_nonneg_left him h1.le)
  rw [div_mul_eq_mul_div, le_div_iff₀ h0]
  linarith

/-! ### Law transfer -/

/-- Target 3 (RBM2D `apriori_transfer` `:153`): at `t = 0` the OU marginal is the model, for every
model and every test function `g` (no measurability: `ouMat_zero`, `integral_fun_fst`). -/
theorem apriori_ouMat_zero_integral {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ)
    (g : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ) :
    ∫ ω, g (ouMat M n 0 ω) ∂(ouP M n) = ∫ ω, g (M.H n ω) ∂M.μ := by
  have h : ∀ ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n), g (ouMat M n 0 ω) = g (M.H n ω.1) :=
    fun ω => by rw [ouMat_zero]
  simp_rw [h]
  unfold ouP
  refine (integral_fun_fst (μ := M.μ) (ν := gueP d (sz.L n) (sz.W n))
    (fun x => g (M.H n x))).trans ?_
  have : ((gueP d (sz.L n) (sz.W n)).real Set.univ) = 1 := by
    simp [Measure.real]
  rw [this, one_smul]

/-! ### The `Bctl` bound -/

/-- Target 4 (replaces RBM2D `apriori_ratio_le_one` `:51`): under the lower half of `(eq:WO)` at `n`,
`Bctl n (1 - η) ≤ W^{-2𝔡} + (N η)⁻¹` for `η > 0`. -/
theorem apriori_bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) (𝔡 η : ℝ) (hη : 0 < η)
    (hwo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) :
    sz.Bctl n (1 - η) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + (Nsz sz n * η)⁻¹ := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hlam := sz.lam_sq_mul_pow_ge n hwo
  have hW2 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := Real.rpow_pos_of_pos hW _
  have hlam2 : 0 < sz.lam n ^ 2 := by
    by_contra hneg
    have h0 : sz.lam n ^ 2 ≤ 0 := not_lt.1 hneg
    have : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0 hWd.le
    linarith
  have habs : |1 - (1 - η)| = η := by rw [sub_sub_cancel, abs_of_pos hη]
  unfold Sizes.Bctl Bparam
  rw [habs]
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  have hN : Nsz sz n = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Nsz, Sizes.size]
    push_cast
    rw [mul_pow]
  have hfirst : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + η)⁻¹ ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := by
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + η)⁻¹
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hlam2 (by linarith)) (inv_nonneg.2 hWd.le)
      _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_comm, mul_inv]
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ := inv_anti₀ hW2 hlam
      _ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := (Real.rpow_neg hW.le _).symm
  have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ =
      (Nsz sz n * η)⁻¹ := by
    rw [hN, ← mul_inv, mul_assoc]
  rw [mul_add]
  exact add_le_add hfirst hsecond.le

/-! ### The row -/

/-- Target 5 (RBM2D `aprioriRow` `:270`): the a priori bound `UNApriori` for every model at admissible
sizes, from `UNDens` and the tracial local law `UNTrLocal` near `E`.  Only `0 < d` is used. -/
theorem unApriori_of_trLocal (d : ℕ) (hd : 3 ≤ d) (𝔠 𝔡 : ℝ) (sz : Sizes d)
    (hA : sz.Admissible 𝔠 𝔡) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ)
    (hD : UNDens m E ρ δ) (hT : UNTrLocal sz M m E δ) : UNApriori sz M E := by
  intro p ε hε
  obtain ⟨hδ, c₀, C, Lp, hc₀, hC, hLp, hdens⟩ := hD
  set τ : ℝ := min (ε / (4 * ((p : ℝ) + 1))) (1 / 2) with hτdef
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hτ0 : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτ12 : τ ≤ 1 / 2 := min_le_right _ _
  have h2pτ : 2 * (p : ℝ) * τ ≤ ε / 2 := by
    have h1 : τ ≤ ε / (4 * ((p : ℝ) + 1)) := min_le_left _ _
    calc 2 * (p : ℝ) * τ ≤ 2 * (p : ℝ) * (ε / (4 * ((p : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε / 2 * ((p : ℝ) / ((p : ℝ) + 1)) := by field_simp; ring
      _ ≤ ε / 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one hp1]; linarith
      _ = ε / 2 := mul_one _
  have hev := hT τ τ ((p : ℝ) + 1) hτ0 hτ0 hp1
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop := hA.2.2.1
  have hbig : ∀ᶠ n in atTop, ((C + 2) ^ p + 1 : ℝ) ≤ Nsz sz n ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hNtend).eventually_ge_atTop _
  have hN1' : ∀ᶠ n in atTop, (1 : ℝ) ≤ Nsz sz n := hNtend.eventually_ge_atTop 1
  filter_upwards [hev, hbig, hN1', hdens, hA.2.2.2.2] with n hn hbig hN1 hdn hwo
  refine le_of_eq_of_le (apriori_ouMat_zero_integral sz M n
    (fun H => (stieltjesN H ((E : ℂ) + ((Nsz sz n)⁻¹ : ℂ) * Complex.I)).im ^ p)) ?_
  set N : ℝ := Nsz sz n with hNdef
  have hNpos : 0 < N := by linarith
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW1 : 1 ≤ W := Nat.one_le_cast.mpr (sz.W_pos n)
  set η₁ : ℝ := N ^ (-1 + τ) with hη₁
  have hη₁pos : 0 < η₁ := Real.rpow_pos_of_pos hNpos _
  have hη₁1 : η₁ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hle : N⁻¹ ≤ η₁ := by
    rw [hη₁, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hNη : N * η₁ = N ^ τ := by
    rw [hη₁]
    calc N * N ^ (-1 + τ) = N ^ (1 : ℝ) * N ^ (-1 + τ) := by rw [Real.rpow_one]
      _ = N ^ (1 + (-1 + τ)) := (Real.rpow_add hNpos _ _).symm
      _ = N ^ τ := by ring_nf
  have hNτ1 : 1 ≤ N ^ τ := Real.one_le_rpow hN1 hτ0.le
  have hNτpos : 0 < N ^ τ := by linarith
  have hz0 : ((E : ℂ) + ((N : ℂ))⁻¹ * Complex.I) = (E : ℂ) + ((N⁻¹ : ℝ) : ℂ) * Complex.I := by
    push_cast; rfl
  have hne : Nonempty (Idx d (sz.L n) (sz.W n)) :=
    Fintype.card_pos_iff.1 (by
      rw [Sizes.card_Idx]
      have h1 := sz.W_pos n
      have h2 := sz.three_le_L n
      unfold Sizes.size
      positivity)
  -- the data of the density and the local law at `z₁ = E + i η₁`
  set z₁ : ℂ := ⟨E, η₁⟩ with hz₁
  have hz₁eq : (E : ℂ) + (η₁ : ℂ) * Complex.I = z₁ := by
    apply Complex.ext <;> simp [hz₁]
  have hdens1 : (m n z₁).im ≤ C := by
    have := (hdn.1 E η₁ (by simpa [hz₁] using hδ.le) hη₁pos (by linarith)).2
    exact this
  -- the bound on `Bctl` and `W^τ`
  have hBctl : sz.Bctl n (1 - η₁) ≤ 2 := by
    have h := apriori_bctl_le sz n 𝔡 η₁ hη₁pos hwo.1
    have h1 : W ^ (-(2 * 𝔡)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith [hA.2.1])
    have h2 : (N * η₁)⁻¹ ≤ 1 := by
      rw [hNη]; exact inv_le_one_of_one_le₀ hNτ1
    linarith
  have hWτ : W ^ τ ≤ N ^ τ := by
    have h1 := sz.W_rpow_le (by omega : 0 < d) n hτ0.le
    refine h1.trans (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left this hτ0.le
    linarith
  have hBnn : 0 ≤ sz.Bctl n (1 - η₁) := by
    have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 0 < sz.L n)
    unfold Sizes.Bctl Bparam
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    have habs : |1 - (1 - η₁)| = η₁ := by rw [sub_sub_cancel, abs_of_pos hη₁pos]
    rw [habs]
    positivity
  -- the bad event
  set Bset : Set (Sizes.SeqΩ sz) := {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + τ) ≤ z.im ∧
        z.im ≤ 1 ∧ ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
          ‖stieltjesN (M.H n ω) z - m n z‖} with hBset
  set B' := toMeasurable M.μ Bset with hB'
  have hB'meas : MeasurableSet B' := measurableSet_toMeasurable _ _
  set cc : ℝ := ((C + 2) * N ^ (2 * τ)) ^ p with hcc
  have hcc0 : 0 ≤ cc := by positivity
  set F : Sizes.SeqΩ sz → ℝ := fun ω =>
    (stieltjesN (M.H n ω) ((E : ℂ) + ((Nsz sz n)⁻¹ : ℂ) * Complex.I)).im with hF
  have hFb : ∀ ω, 0 ≤ F ω ∧ F ω ≤ N := by
    intro ω
    have := apriori_im_bounds (M.H n ω) (M.herm n ω) E N⁻¹ (inv_pos.2 hNpos)
    rw [one_div, inv_inv] at this
    have hz : ((E : ℂ) + ((Nsz sz n)⁻¹ : ℂ) * Complex.I) = (E : ℂ) + ((N⁻¹ : ℝ) : ℂ) * Complex.I := by
      rw [hNdef]; push_cast; rfl
    simp only [hF, hz]
    exact this
  have hpt : ∀ ω, F ω ^ p ≤ cc + N ^ p * B'.indicator 1 ω := by
    intro ω
    obtain ⟨hF0, hFN⟩ := hFb ω
    by_cases hω : ω ∈ B'
    · rw [Set.indicator_of_mem hω]
      have : F ω ^ p ≤ N ^ p := pow_le_pow_left₀ hF0 hFN p
      simp only [Pi.one_apply, mul_one]
      linarith
    · rw [Set.indicator_of_notMem hω]
      have hω' : ω ∉ Bset := fun h => hω (subset_toMeasurable _ _ h)
      have hgood : ‖stieltjesN (M.H n ω) z₁ - m n z₁‖ ≤ W ^ τ * sz.Bctl n (1 - η₁) := by
        by_contra hcon
        refine hω' ⟨z₁, ?_, ?_, ?_, ?_⟩
        · simpa [hz₁] using hδ.le
        · exact le_rfl
        · exact hη₁1
        · exact not_le.1 hcon
      have hnear : ‖stieltjesN (M.H n ω) ((E : ℂ) + (η₁ : ℂ) * Complex.I) - m n z₁‖ ≤
          W ^ τ * sz.Bctl n (1 - η₁) := by rw [hz₁eq]; exact hgood
      have h2 := apriori_im_le_of_near (M.H n ω) (M.herm n ω) E N⁻¹ η₁ (m n z₁)
        (W ^ τ * sz.Bctl n (1 - η₁)) (inv_pos.2 hNpos) hle hnear
      have hz : ((E : ℂ) + ((Nsz sz n)⁻¹ : ℂ) * Complex.I) = (E : ℂ) + ((N⁻¹ : ℝ) : ℂ) * Complex.I := by
        rw [hNdef]; push_cast; rfl
      have hFle : F ω ≤ (C + 2) * N ^ (2 * τ) := by
        have h3 : F ω ≤ η₁ / N⁻¹ * ((m n z₁).im + W ^ τ * sz.Bctl n (1 - η₁)) := by
          simp only [hF, hz]; exact h2
        have h4 : η₁ / N⁻¹ = N ^ τ := by rw [div_inv_eq_mul, mul_comm, hNη]
        rw [h4] at h3
        have h5 : W ^ τ * sz.Bctl n (1 - η₁) ≤ 2 * N ^ τ :=
          calc W ^ τ * sz.Bctl n (1 - η₁) ≤ N ^ τ * 2 :=
                mul_le_mul hWτ hBctl hBnn hNτpos.le
            _ = 2 * N ^ τ := mul_comm _ _
        have h6 : N ^ (2 * τ) = N ^ τ * N ^ τ := by
          rw [two_mul, Real.rpow_add hNpos]
        calc F ω ≤ N ^ τ * ((m n z₁).im + W ^ τ * sz.Bctl n (1 - η₁)) := h3
          _ ≤ N ^ τ * (C + 2 * N ^ τ) :=
              mul_le_mul_of_nonneg_left (by linarith) hNτpos.le
          _ ≤ N ^ τ * (C * N ^ τ + 2 * N ^ τ) :=
              mul_le_mul_of_nonneg_left (by
                have := mul_le_mul_of_nonneg_left hNτ1 hC.le
                linarith) hNτpos.le
          _ = (C + 2) * N ^ (2 * τ) := by rw [h6]; ring
      simp only [mul_zero, add_zero]
      exact pow_le_pow_left₀ hF0 hFle p
  have hI : Integrable (B'.indicator (1 : Sizes.SeqΩ sz → ℝ)) M.μ :=
    (integrable_const (1 : ℝ)).indicator hB'meas
  have hint : Integrable (fun ω => cc + N ^ p * B'.indicator (1 : Sizes.SeqΩ sz → ℝ) ω) M.μ :=
    (integrable_const cc).add (hI.const_mul _)
  have hmain : ∫ ω, F ω ^ p ∂M.μ ≤
      ∫ ω, (cc + N ^ p * B'.indicator (1 : Sizes.SeqΩ sz → ℝ) ω) ∂M.μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) hint
      (Filter.Eventually.of_forall hpt)
    exact pow_nonneg (hFb ω).1 p
  have hval : ∫ ω, (cc + N ^ p * B'.indicator (1 : Sizes.SeqΩ sz → ℝ) ω) ∂M.μ =
      cc + N ^ p * M.μ.real B' := by
    rw [integral_add (integrable_const cc) (hI.const_mul _), integral_const_mul,
      integral_indicator_one hB'meas]
    simp
  have hreal : M.μ.real B' ≤ N ^ (-((p : ℝ) + 1)) := by
    unfold Measure.real
    rw [hB', measure_toMeasurable]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)] at this
  have hbad : N ^ p * M.μ.real B' ≤ 1 := by
    calc N ^ p * M.μ.real B' ≤ N ^ p * N ^ (-((p : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = N ^ (-1 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hgoodc : cc ≤ (C + 2) ^ p * N ^ (ε / 2) := by
    rw [hcc, mul_pow, ← Real.rpow_natCast (N ^ (2 * τ)) p, ← Real.rpow_mul hNpos.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    linarith
  have hX1 : (1 : ℝ) ≤ N ^ (ε / 2) := Real.one_le_rpow hN1 (by positivity)
  have hNε : N ^ ε = N ^ (ε / 2) * N ^ (ε / 2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have h2p : (0 : ℝ) ≤ (C + 2) ^ p := by positivity
  calc ∫ ω, F ω ^ p ∂M.μ ≤ cc + N ^ p * M.μ.real B' := hmain.trans hval.le
    _ ≤ (C + 2) ^ p * N ^ (ε / 2) + 1 := add_le_add hgoodc hbad
    _ ≤ ((C + 2) ^ p + 1) * N ^ (ε / 2) := by linarith
    _ ≤ N ^ (ε / 2) * N ^ (ε / 2) := mul_le_mul_of_nonneg_right hbig (by linarith)
    _ = N ^ ε := hNε.symm

/-- Target 6: the band row.  Bulk `E`: `UNDensBandRow` gives `δ ≤ κ/2` and `UNDens` (so `0 < δ`),
`UNTrLocalBandRow` (from `UNLocAvgBand`) gives `UNTrLocal`, and target 5 applies. -/
theorem unApriori_band_of_rows (hT : UNTrLocalBandRow) (hD : UNDensBandRow) (hL : UNLocAvgBand)
    (d : ℕ) (hd : 3 ≤ d) (𝔠 𝔡 : ℝ) (sz : Sizes d) (hA : sz.Admissible 𝔠 𝔡) (κ : ℝ) (hκ : 0 < κ)
    (E : ℝ) (hE : |E| ≤ 2 - κ) : UNApriori sz (UNModel.band sz) E := by
  obtain ⟨δ, hδκ, hdens⟩ := hD κ hκ E hE
  exact unApriori_of_trLocal d hd 𝔠 𝔡 sz hA (UNModel.band sz) (fun _ => msc) E
    (fun _ => rhoSC E) δ hdens (hT hL d hd 𝔠 𝔡 sz hA κ hκ E hE δ hdens.1 hδκ)

end RBM.Univ

/-! ## Compiled instances (`d = 3`, `sz0`: `L = 4`, `W = 32`, `N = 2^21` at `n = 0`) -/

namespace RBM.Univ.AprioriInst

open MeasureTheory Matrix Filter Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst

/-- (a) Target 5 at `sz0`, the band model, `m = msc`, `E = 0`, `ρ = ρ_sc(0)`, `δ = 1/2`
(`un_dens_msc_zero` discharges `UNDens`); `UNTrLocal` is the owed pin and stays a hypothesis. -/
theorem inst_unApriori_band_zero :
    UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
      UNApriori sz0 (UNModel.band sz0) 0 :=
  fun h => unApriori_of_trLocal 3 le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm (UNModel.band sz0)
    (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) un_dens_msc_zero h

/-- (b) Target 6 at `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `sz0`, `κ = 1/2`, `E = 1` (`|1| ≤ 3/2`); the three
owed band inputs stay hypotheses. -/
theorem inst_unApriori_band_one :
    UNTrLocalBandRow → UNDensBandRow → UNLocAvgBand → UNApriori sz0 (UNModel.band sz0) 1 :=
  fun hT hD hL => unApriori_band_of_rows hT hD hL 3 le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm
    (1 / 2) (by norm_num) 1 (by rw [abs_one]; norm_num)

/-- (c) Target 2 at `H = 0 : Matrix (Fin 1) (Fin 1) ℂ`, `E = 0`, `η₀ = 1/2`, `η₁ = 1`, `w = m(i)`,
`ζ = 0` (the hypothesis `‖w - w‖ ≤ 0` is discharged; the equality case). -/
theorem inst_im_le_of_near :
    (stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ) (((0 : ℝ) : ℂ) + (((1 / 2 : ℝ)) : ℂ) * Complex.I)).im ≤
      1 / (1 / 2) * ((stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ)
        (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im + 0) :=
  apriori_im_le_of_near (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_zero 0 (1 / 2) 1
    (stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ) (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)) 0
    (by norm_num) (by norm_num) (by simp)

/-- (d) Target 4 at `sz0`, `n = 0`, `𝔡 = 1/10`, `η = 1/2` (`W^{-3/2+1/10} = 1/128 ≤ 1/64 = lam`). -/
theorem inst_bctl_le :
    sz0.Bctl 0 (1 - 1 / 2) ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 10 : ℝ))) + (Nsz sz0 0 * (1 / 2))⁻¹ := by
  refine apriori_bctl_le sz0 0 (1 / 10) (1 / 2) (by norm_num) ?_
  obtain ⟨-, hW, -, hl⟩ := sz0_values
  rw [hl, hW]
  have h1 : (((32 : ℕ) : ℝ)) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10) = ((2 : ℝ) ^ (7 : ℕ))⁻¹ := by
    rw [show ((32 : ℕ) : ℝ) = (2 : ℝ) ^ (5 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    rw [show (5 : ℝ) * (-((3 : ℕ) : ℝ) / 2 + 1 / 10) = -((7 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [h1]
  norm_num

/-- Target 1 at the `1 × 1` zero matrix, `E = 0`, `η = 1`: `0 ≤ Im m(i) = 1 ≤ 1`. -/
theorem inst_im_bounds :
    0 ≤ (stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ) (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im ∧
      (stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ)
        (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im ≤ 1 / 1 :=
  apriori_im_bounds (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_zero 0 1 one_pos

/-- Target 3 at `sz0`, the band model, `n = 0`, `g ≡ 1`: both sides are `1`
(probability measures). -/
theorem inst_ouMat_zero_integral :
    ∫ ω, (fun _ => (1 : ℝ)) (ouMat (UNModel.band sz0) 0 0 ω) ∂(ouP (UNModel.band sz0) 0) =
      ∫ ω, (fun _ => (1 : ℝ)) ((UNModel.band sz0).H 0 ω) ∂(UNModel.band sz0).μ :=
  apriori_ouMat_zero_integral sz0 (UNModel.band sz0) 0 (fun _ => 1)

end RBM.Univ.AprioriInst

end
