/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.EMCTE2
import RBM3D.Universality.Uyw
import RBM3D.BA.UNPins
import RBM3D.BA.MReg

/-!
# The block Anderson weighted [DYYY25, (2.21)] estimate and the bad-event bounds

The block Anderson producer `unEMCTE2RowBA_holds` of the statement `UNEMCTE2RowBA` (`BA/UNPins.lean`), and the
three kind hypotheses `UNBulkWindowk`, `UNBadBoundk`, `UNBad2Boundk` with their block Anderson instances, which feed the
model-generic forms `unJak_of_ouClaimsk`, `unUyw_of_ouClaimsk` (used by `jakUywRowkD` in `BA/UNBUniv.lean`).

Paper: Theorem 2.4 (`Thm: B_Univ`) for the block Anderson model `H = V + iλ Ψ` ((2.30) `eq:H_blocka`).  Its proof is the
Green's function comparison of [DYYY25, Theorem 2.6]: the weighted estimate [DYYY25, (2.21)] is obtained "as in Step 3" of the
proof of [YY_25, Theorem 2.6], and the two estimates of item (ii) are [DYYY25, (2.22)] and [DYYY25, (2.23)].

* **(i) [DYYY25, (2.21)]**: the centred block Anderson flow is `λ_n Ψ` plus the band OU flow of
  `sz.withLam 0` (`ouMatC_ba_eq_band_add`, on the same probability space; profile
  `S^{(B)}(0) = I`, `lamV = 0`).  So the generator identity holds for the shifted test function
  `Φ(A + ·)` (`EMCTE2BA_testFunH_translate`, `EMCTE2BA_wirtSecond_translate`);
  `eq225_intervalShift` is `eq225_interval` for it, `unEMCTE2k_ba` is
  `unEMCTE2_of_sizeTendsto` read through the translation, and
  `unEMCTE2RowBA_holds` is the statement `UNEMCTE2RowBA`.
* **(ii) [DYYY25, (2.22)], [DYYY25, (2.23)]**: `unJak_of_ouClaimsk`, `unUyw_of_ouClaimsk`
  are the model-generic forms of `unJak_of_ouClaims`, `unUyw_of_ouClaims`
  (`Jak.lean`, `Uyw.lean`: the private fixed-time lemmas carry the profile coupling
  `lamV` and the bulk window, and are reached by `open private`), under the three kind
  hypotheses `UNBulkWindowk`, `UNBadBoundk`, `UNBad2Boundk`.  At the band kind they are
  `measure_bad_le_of_queBadMat`, `measure_bad2_le_of_queBadMat`; at block Anderson they are
  `BAbulk_window`, `unBadYBA_measure_le` and the one-block pair bound
  `EMCTE2BA_bad2_subset` (`UNBulkWindowk_ba`, `UNBadBoundk_ba`, `UNBad2Boundk_ba`).

Helpers of `EMCTE2.lean` reached by `open private` (all generic in the matrix family):
`EMCTE2_hsum`, `EMCTE2_hsum_nonneg`, `EMCTE2_integrable_hsum`,
`EMCTE2_integrable_L1t_term`, `EMCTE2_integrable_L2t_term`, `EMCTE2_sum_integral_swap`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

open private EMCTE2_hsum EMCTE2_hsum_nonneg EMCTE2_integrable_hsum EMCTE2_integrable_L1t_term
  EMCTE2_integrable_L2t_term EMCTE2_sum_integral_swap from RBM3D.Universality.EMCTE2
open private Jak_fixed_time Jak_queBound_eq from RBM3D.Universality.Jak
open private UNPins_hg_3_10 from RBM3D.BA.UNPins
open private Uyw_fixed_time Uyw_queBound_eq from RBM3D.Universality.Uyw

namespace RBM.Univ

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 1. The translation of test functions -/

section Translate

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **Test functions**: a Hermitian translate of a `TestFunH` is a `TestFunH`. -/
theorem EMCTE2BA_testFunH_translate {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ} (hΦ : TestFunH d L W Φ)
    {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) : TestFunH d L W (fun K => Φ (A + K)) := by
  obtain ⟨h1, ⟨C0, h2⟩, ⟨C1, h3⟩, ⟨C2, h4⟩⟩ := hΦ
  have hfd : ∀ x, fderiv ℝ (fun K => Φ (A + K)) x = fderiv ℝ Φ (A + x) := fun x => fderiv_comp_add_left A
  refine ⟨fun M hM => ?_, ⟨C0, fun M hM => h2 _ (hA.add hM)⟩, ⟨C1, fun M hM => ?_⟩, ⟨C2, fun M hM => ?_⟩⟩
  · exact (h1 _ (hA.add hM)).comp M (contDiffAt_const.add contDiffAt_id)
  · rw [hfd]; exact h3 _ (hA.add hM)
  · rw [funext hfd, fderiv_comp_add_left (𝕜 := ℝ) (f := fderiv ℝ Φ) (x := M) A]; exact h4 _ (hA.add hM)

/-- **Second derivative**: `wirtSecond` of a translate is `wirtSecond` at the translated point. -/
theorem EMCTE2BA_wirtSecond_translate (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ)
    (A M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Idx d L W) :
    wirtSecond d L W (fun K => Φ (A + K)) M a b = wirtSecond d L W Φ (A + M) a b := by
  have hfd : ∀ x, fderiv ℝ (fun K => Φ (A + K)) x = fderiv ℝ Φ (A + x) := fun x => fderiv_comp_add_left A
  have h2 : fderiv ℝ (fderiv ℝ (fun K => Φ (A + K))) M = fderiv ℝ (fderiv ℝ Φ) (A + M) := by
    rw [funext hfd]; exact fderiv_comp_add_left (𝕜 := ℝ) (f := fderiv ℝ Φ) (x := M) A
  have hc : ∀ c, coordD2 d L W (fun K => Φ (A + K)) M c = coordD2 d L W Φ (A + M) c := fun c => by
    unfold coordD2; rw [h2]
  unfold wirtSecond
  simp only [hc]

/-- A translate of a measurable matrix family is measurable. -/
theorem EMCTE2BA_measurable_shift {Ω' : Type*} [MeasurableSpace Ω'] (A : Matrix (Idx d L W) (Idx d L W) ℂ)
    {M : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ} (hM : Measurable M) : Measurable fun ω => A + M ω :=
  Measurable.of_eval_matrix _ fun i j => measurable_const.add (hM.eval_matrix (i := i) (j := j))

end Translate

/-! ## 2. `eq225_interval` for the shifted functional -/

/-- **`eq225_interval` for the shifted functional** `Φ(A + ·)`, `A` a deterministic
Hermitian matrix, on the band carrier of any `sz`; the kernels `L1t`, `L2t` are read at `A + ouMat`.  At `A = 0` it is
`eq225_interval`. -/
theorem eq225_intervalShift (d : ℕ) (sz : Sizes d) (n nf : ℕ) (z : Fin nf → ℂ)
    (hz : ∀ i : Fin nf, 0 < (z i).im)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hA : A.IsHermitian)
    (t T Bd : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (hB : ∀ s ∈ Set.Ioo t T,
      ∫ ω, ((∑ i : Fin nf, (∏ j ∈ Finset.univ.erase i,
              (stieltjesN (A + ouMat (UNModel.band sz) n s ω) (z j)).im) *
              L1t d (sz.L n) (sz.W n) (sz.lam n) (A + ouMat (UNModel.band sz) n s ω) (z i)) +
            ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i,
              (∏ k ∈ (Finset.univ.erase i).erase j,
                (stieltjesN (A + ouMat (UNModel.band sz) n s ω) (z k)).im) *
              L2t d (sz.L n) (sz.W n) (sz.lam n) (A + ouMat (UNModel.band sz) n s ω) (z i) (z j))
        ∂(ouP (UNModel.band sz) n) ≤ Bd) :
    |(∫ ω, ∏ i : Fin nf, (stieltjesN (A + ouMat (UNModel.band sz) n t ω) (z i)).im
          ∂(ouP (UNModel.band sz) n)) -
      ∫ ω, ∏ i : Fin nf, (stieltjesN (A + ouMat (UNModel.band sz) n T ω) (z i)).im
          ∂(ouP (UNModel.band sz) n)| ≤
      (1 / 2) * (T - t) * Bd := by
  classical
  set Φ0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
    fun K => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ) with hΦ0def
  have hΦ0 : TestFunH d (sz.L n) (sz.W n) Φ0 :=
    testFunH_stieltjesImProduct d (sz.L n) (sz.W n) nf z hz
  set Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
    fun K => Φ0 (A + K) with hΦdef
  have hΦ : TestFunH d (sz.L n) (sz.W n) Φ := EMCTE2BA_testFunH_translate hΦ0 hA
  set F : ℝ → ℂ := fun s => ∫ ω, Φ (ouMat (UNModel.band sz) n s ω) ∂(ouP (UNModel.band sz) n)
    with hFdef
  set g : ℝ → ℂ := fun s => (-(1 / 2 : ℝ) * Real.exp (-s)) •
      ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
      (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n) with hgdef
  have hcast : ∀ s : ℝ, F s =
      ((∫ ω, ∏ i, (stieltjesN (A + ouMat (UNModel.band sz) n s ω) (z i)).im
        ∂(ouP (UNModel.band sz) n) : ℝ) : ℂ) := by
    intro s
    simp only [hFdef, hΦdef, hΦ0def]
    exact integral_ofReal
  have hFd : ∀ s : ℝ, 0 < s → HasDerivAt F (g s) s := fun s hs =>
    ouGenerator_hasDerivAt_integral d sz n Φ hΦ s hs
  have hFT : F T - F 0 = ∫ s in (0 : ℝ)..T, g s :=
    ouGenerator_integral_sub_eq d sz n Φ hΦ T (ht.trans htT)
  have hFt : F t - F 0 = ∫ s in (0 : ℝ)..t, g s :=
    ouGenerator_integral_sub_eq d sz n Φ hΦ t ht
  -- the hypothesis forces `0 ≤ Bd` as soon as `(t, T)` is nonempty
  have hBd : t < T → 0 ≤ Bd := by
    intro htT'
    have hmid : (t + T) / 2 ∈ Set.Ioo t T := ⟨by linarith, by linarith⟩
    refine le_trans ?_ (hB _ hmid)
    exact integral_nonneg fun ω =>
      EMCTE2_hsum_nonneg (lam := sz.lam n) (hA.add (ouMat_isHermitian (UNModel.band sz) n _ ω)) z hz
  -- the norm of the weighted sum of expected Hessians is at most `Bd`
  have hS : ∀ s ∈ Set.Ioo t T,
      ‖∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
        (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n)‖ ≤ Bd := by
    intro s hs
    rw [EMCTE2_sum_integral_swap sz n hΦ s]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hbound : ∀ᵐ ω ∂(ouP (UNModel.band sz) n),
        ‖∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
          (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
          wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b‖ ≤
          EMCTE2_hsum d (sz.L n) (sz.W n) (sz.lam n) z (A + ouMat (UNModel.band sz) n s ω) := by
      refine Filter.Eventually.of_forall fun ω => ?_
      have hH := hA.add (ouMat_isHermitian (UNModel.band sz) n s ω)
      have hk := centeredVariance_wirtProduct_kernel_bound_Lt d (sz.L n) (sz.W n) (sz.lam n)
        (Finset.univ : Finset (Fin nf)) (A + ouMat (UNModel.band sz) n s ω) hH z (fun i _ => hz i)
      simp only [hΦdef, EMCTE2BA_wirtSecond_translate]
      exact hk
    exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
      (EMCTE2_integrable_hsum (ouP (UNModel.band sz) n)
        (EMCTE2BA_measurable_shift A (measurable_ouMat (UNModel.band sz) n s))
        (fun ω => hA.add (ouMat_isHermitian (UNModel.band sz) n s ω)) z hz)
      hbound).trans (hB s hs)
  -- the generator integrand is bounded by `½ Bd` on `(t, T)` (`e^{-s} ≤ 1` for `s ≥ 0`)
  have hg : ∀ s ∈ Set.Ioo t T, ‖g s‖ ≤ (1 / 2) * Bd := by
    intro s hs
    have hS' := hS s hs
    have hexp : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    have hexppos : 0 < Real.exp (-s) := Real.exp_pos _
    have habs : ‖(-(1 / 2 : ℝ) * Real.exp (-s))‖ = (1 / 2 : ℝ) * Real.exp (-s) := by
      rw [Real.norm_eq_abs, abs_of_neg (by nlinarith [hexppos])]
      ring
    have hSnn := norm_nonneg (∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
      (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
        ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
          ∂(ouP (UNModel.band sz) n))
    calc ‖g s‖ = ‖(-(1 / 2 : ℝ) * Real.exp (-s))‖ *
          ‖∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
          (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
            ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n s ω) a b
              ∂(ouP (UNModel.band sz) n)‖ := by
          rw [hgdef]; exact norm_smul _ _
      _ ≤ (1 / 2 : ℝ) * Bd := by
          rw [habs]
          nlinarith [mul_le_mul_of_nonneg_right hexp hSnn, hS']
  -- `g` is interval integrable on `[t, T]`: it is `deriv F` (measurable) on `(0, ∞)` and bounded
  have hIntTT : IntervalIntegrable g MeasureTheory.volume t T := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le htT]
    have hm : AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioc t T)) := by
      have hm' : AEStronglyMeasurable (deriv F)
          (MeasureTheory.volume.restrict (Set.Ioc t T)) :=
        (measurable_deriv F).aestronglyMeasurable
      refine hm'.congr ?_
      exact (ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun s hs => (hFd s (lt_of_le_of_lt ht hs.1)).deriv)
    refine Integrable.of_bound (C := (1 / 2) * Bd) hm ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [MeasureTheory.volume.ae_ne T] with s hsne hs
    exact hg s ⟨hs.1, hs.2.lt_of_ne hsne⟩
  have hnn : 0 ≤ (1 / 2 * Bd) * |T - t| := by
    rcases eq_or_lt_of_le htT with h | h
    · simp [h]
    · exact mul_nonneg (by have := hBd h; positivity) (abs_nonneg _)
  have hmain : ‖F T - F t‖ ≤ (1 / 2 * Bd) * |T - t| := by
    by_cases h0t : IntervalIntegrable g MeasureTheory.volume 0 t
    · have hsum := intervalIntegral.integral_add_adjacent_intervals h0t hIntTT
      have hdiff : F T - F t = ∫ s in t..T, g s := by
        linear_combination hFT - hFt - hsum
      rw [hdiff]
      refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
      filter_upwards [MeasureTheory.volume.ae_ne T] with s hsne hs
      rw [Set.uIoc_of_le htT] at hs
      exact hg s ⟨hs.1, hs.2.lt_of_ne hsne⟩
    · have hnot : ¬ IntervalIntegrable g MeasureTheory.volume 0 T := fun h =>
        h0t (h.mono_set (by
          rw [Set.uIcc_of_le ht, Set.uIcc_of_le (ht.trans htT)]
          exact Set.Icc_subset_Icc_right htT))
      rw [intervalIntegral.integral_undef hnot] at hFT
      rw [intervalIntegral.integral_undef h0t] at hFt
      have : F T - F t = 0 := by linear_combination hFT - hFt
      rw [this, norm_zero]
      exact hnn
  calc _ = |(∫ ω, ∏ i, (stieltjesN (A + ouMat (UNModel.band sz) n T ω) (z i)).im
            ∂(ouP (UNModel.band sz) n)) -
        ∫ ω, ∏ i, (stieltjesN (A + ouMat (UNModel.band sz) n t ω) (z i)).im
            ∂(ouP (UNModel.band sz) n)| := abs_sub_comm _ _
    _ = ‖F T - F t‖ := by
        rw [hcast T, hcast t, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / 2 * Bd) * |T - t| := hmain
    _ = (1 / 2) * (T - t) * Bd := by rw [abs_of_nonneg (sub_nonneg.2 htT)]; ring

/-! ## 3. `UNEMCTE2k` at the block Anderson kind -/

/-- **The weighted [DYYY25, (2.21)] at a size sequence**: the block Anderson kind at every size sequence with
`N → ∞` and `τU ≤ Cn τU` (the argument of `unEMCTE2_of_sizeTendsto`).  The centred flow is `λ_n Ψ` plus the
band flow of `sz.withLam 0` (`ouMatC_ba_eq_band_add`), the probability space is the same, the profile coupling
is `lamV = 0 = (sz.withLam 0).lam n`; then `eq225_intervalShift` at `A = λ_n Ψ` (Hermitian: `mean_herm`).  `E` is not used. -/
theorem unEMCTE2k_ba (d : ℕ) (sz : Sizes d) (hd : sz.SizeTendsto) (E : ℝ) (nf : ℕ) (τU Cn : ℝ)
    (hτ : τU ≤ Cn * τU) : UNEMCTE2k (UNKind.ba d) sz E nf τU Cn := by
  rcases Nat.eq_zero_or_pos nf with rfl | hpos
  · intro C₀ ε _ _
    refine Eventually.of_forall fun n z _ B hB _ _ t _ _ => ?_
    simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero]
    have : 0 ≤ Nsz sz n ^ ε * Nsz sz n ^ (-1 + Cn * τU) := by positivity
    exact mul_nonneg this hB
  intro C₀ ε hC₀ hε
  have hNε : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp hd
  filter_upwards [hNε.eventually_ge_atTop ((1 / 2) * (nf : ℝ) ^ 2)] with n hn
  intro z hz B hB0 hB1 hB2 t ht htT
  have hNnat : 0 < sz.size n := by
    simp only [Sizes.size]
    have := sz.three_le_L n
    have := sz.W_pos n
    positivity
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hNnat
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hNnat
  have hzim : ∀ i, 0 < (z i).im := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (hz i).2.1
  have hT0 : 0 ≤ ouTStar sz τU n := Real.rpow_nonneg hNpos.le _
  have hnf : 0 ≤ (nf : ℝ) ^ 2 * B := by positivity
  -- the translation: `ouMatC = A + ouMat band` with `A = λ_n Ψ`
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      A = ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := ⟨_, rfl⟩
  have hA : A.IsHermitian := hAdef ▸ (UNModelC.ba sz).mean_herm n
  have hfun : ∀ (s : ℝ) ω, ouMatC (UNModelC.ba sz) n s ω =
      A + (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from
        ouMat (UNModel.band (sz.withLam 0)) n s ω) := fun s ω => by
    rw [hAdef]; exact sub_eq_iff_eq_add'.mp (ouMatC_ba_eq_band_add sz n s ω)
  have hMmeas : ∀ s : ℝ, Measurable (ouMatC (UNModelC.ba sz) n s) := fun s => by
    have h : ouMatC (UNModelC.ba sz) n s = fun ω => A +
        (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from
          ouMat (UNModel.band (sz.withLam 0)) n s ω) := funext (hfun s)
    rw [h]
    exact EMCTE2BA_measurable_shift A (measurable_ouMat (UNModel.band (sz.withLam 0)) n s)
  have hMherm := ouMatC_isHermitian (UNModelC.ba sz) n
  have hBint : ∀ s ∈ Set.Ioo t (ouTStar sz τU n),
      ∫ ω, ((∑ i : Fin nf, (∏ j ∈ Finset.univ.erase i,
              (stieltjesN (ouMatC (UNModelC.ba sz) n s ω) (z j)).im) *
              L1t d (sz.L n) (sz.W n) 0 (ouMatC (UNModelC.ba sz) n s ω) (z i)) +
            ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i,
              (∏ k ∈ (Finset.univ.erase i).erase j,
                (stieltjesN (ouMatC (UNModelC.ba sz) n s ω) (z k)).im) *
              L2t d (sz.L n) (sz.W n) 0 (ouMatC (UNModelC.ba sz) n s ω) (z i) (z j))
        ∂(ouP (UNModelC.ba sz).toUNModel n) ≤ (nf : ℝ) ^ 2 * B := fun s hs => by
    have hs0 : 0 ≤ s := ht.trans hs.1.le
    have hsT : s ≤ ouTStar sz τU n := hs.2.le
    have iL1 := fun i => EMCTE2_integrable_L1t_term (lam := (0 : ℝ)) (ouP (UNModelC.ba sz).toUNModel n)
      (hMmeas s) (hMherm s) z hzim (Finset.univ.erase i) i
    have iL2 := fun i j => EMCTE2_integrable_L2t_term (lam := (0 : ℝ))
      (ouP (UNModelC.ba sz).toUNModel n) (hMmeas s) (hMherm s) z hzim ((Finset.univ.erase i).erase j) i j
    rw [integral_add (integrable_finsetSum _ fun i _ => iL1 i)
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iL2 i j),
      integral_finsetSum _ fun i _ => iL1 i,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iL2 i j]
    have e2 : ∀ i, ∫ ω, ∑ j ∈ Finset.univ.erase i,
        (∏ k ∈ (Finset.univ.erase i).erase j,
          (stieltjesN (ouMatC (UNModelC.ba sz) n s ω) (z k)).im) *
          L2t d (sz.L n) (sz.W n) 0 (ouMatC (UNModelC.ba sz) n s ω) (z i) (z j)
            ∂(ouP (UNModelC.ba sz).toUNModel n) =
        ∑ j ∈ Finset.univ.erase i, ∫ ω, (∏ k ∈ (Finset.univ.erase i).erase j,
          (stieltjesN (ouMatC (UNModelC.ba sz) n s ω) (z k)).im) *
          L2t d (sz.L n) (sz.W n) 0 (ouMatC (UNModelC.ba sz) n s ω) (z i) (z j)
            ∂(ouP (UNModelC.ba sz).toUNModel n) := fun i =>
      integral_finsetSum _ fun j _ => iL2 i j
    simp only [e2]
    have h1 : ∑ i : Fin nf, ∫ ω, (∏ j ∈ Finset.univ.erase i,
        (stieltjesN (ouMatC (UNModelC.ba sz) n s ω) (z j)).im) *
        L1t d (sz.L n) (sz.W n) 0 (ouMatC (UNModelC.ba sz) n s ω) (z i)
          ∂(ouP (UNModelC.ba sz).toUNModel n) ≤
        ∑ _i : Fin nf, B := Finset.sum_le_sum fun i _ => hB1 s hs0 hsT i
    have h2 : ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i, ∫ ω, (∏ k ∈ (Finset.univ.erase i).erase j,
        (stieltjesN (ouMatC (UNModelC.ba sz) n s ω) (z k)).im) *
        L2t d (sz.L n) (sz.W n) 0 (ouMatC (UNModelC.ba sz) n s ω) (z i) (z j)
          ∂(ouP (UNModelC.ba sz).toUNModel n) ≤ ∑ _i : Fin nf, ∑ _j ∈ Finset.univ.erase _i, B :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
        hB2 s hs0 hsT i j (Finset.ne_of_mem_erase hj).symm
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.card_erase_of_mem (Finset.mem_univ _), nsmul_eq_mul]
    rw [Nat.cast_sub hpos]
    push_cast
    ring
  have key := eq225_intervalShift d (sz.withLam 0) n nf z hzim A hA t (ouTStar sz τU n)
    ((nf : ℝ) ^ 2 * B) ht htT (fun s hs => by
      have h := hBint s hs
      simp only [hfun] at h
      exact h)
  simp only [UNKind.ba, hfun]
  refine key.trans ?_
  have hq : (1 / 2 : ℝ) * (ouTStar sz τU n - t) * ((nf : ℝ) ^ 2 * B) ≤
      (1 / 2 : ℝ) * ouTStar sz τU n * ((nf : ℝ) ^ 2 * B) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_self (ouTStar sz τU n) ht) (by norm_num : (0 : ℝ) ≤ 1 / 2))
      hnf
  refine hq.trans ?_
  have hTB : 0 ≤ ouTStar sz τU n * B := mul_nonneg hT0 hB0
  have h3 : (1 / 2 : ℝ) * ouTStar sz τU n * ((nf : ℝ) ^ 2 * B) =
      ((1 / 2) * (nf : ℝ) ^ 2) * (ouTStar sz τU n * B) := by ring
  have hexp : ouTStar sz τU n ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + Cn * τU) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h4 : ((sz.size n : ℕ) : ℝ) ^ ε * ouTStar sz τU n * B ≤
      ((sz.size n : ℕ) : ℝ) ^ ε * ((sz.size n : ℕ) : ℝ) ^ (-1 + Cn * τU) * B :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hNpos.le _)) hB0
  calc _ = ((1 / 2) * (nf : ℝ) ^ 2) * (ouTStar sz τU n * B) := h3
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (ouTStar sz τU n * B) :=
        mul_le_mul_of_nonneg_right hn hTB
    _ = ((sz.size n : ℕ) : ℝ) ^ ε * ouTStar sz τU n * B := by ring
    _ ≤ _ := h4

/-! ## 4. The kind hypotheses and the model-generic forms of `Jak` and `Uyw` -/

/-- **Kind hypothesis (bulk window)**: the bulk of a kind is open, uniformly in `n`: for every `κ > 0` there are `κ' > 0` and
`r > 0` with `bulk κ E n`, `|e - E| ≤ r` ⟹ `bulk κ' e n`.  Band: `κ' = r = κ/2`.  Block Anderson:
`κ' = κ/2`, `r = (π κ)³/8` (`BAbulk_window`; `UNBulkWindowk_ba`). -/
def UNBulkWindowk (K : ∀ d, UNKind d) : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ : ℝ), 0 < κ → ∃ κ' r : ℝ, 0 < κ' ∧ 0 < r ∧
    ∀ (n : ℕ) (E e : ℝ), (K d).bulk sz κ E n → |e - E| ≤ r → (K d).bulk sz κ' e n

/-- **Kind hypothesis (bad-event transfer, `Jak`)**: QUE at the coupling `sz.lam n` with bound `p` at every block gives the
`blockM` event at the profile coupling `(K d).lamV sz n` probability `≤ (2d + 1) p`.  Band: `measure_bad_le_of_queBadMat`.
Block Anderson: `unBadY_of_blockM` and `unBadYBA_measure_le`
(`UNBadBoundk_ba`). -/
def UNBadBoundk (K : ∀ d, UNKind d) : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (t 𝔡 E : ℝ) (y : Idx d (sz.L n) (sz.W n)) (p : ℝ≥0∞),
    3 ≤ d → 0 < 𝔡 → (sz.W n : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n →
    (∀ b : Zd d (sz.L n), ouP ((K d).M sz).toUNModel n
        {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E b (ouMatC ((K d).M sz) n t ω)} ≤ p) →
    ouP ((K d).M sz).toUNModel n
        {ω | ∃ α, |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues α - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            (sz.W n : ℝ) ^ (-(𝔡 / 6)) ≤
              ‖blockM d (sz.L n) (sz.W n) ((K d).lamV sz n) (ouMatC_isHermitian ((K d).M sz) n t ω)
                (siteBlock d (sz.L n) (sz.W n) y) α‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p

/-- **Kind hypothesis (bad-event transfer, `Uyw`)**: the pair form (`blockM2`).  Band: `measure_bad2_le_of_queBadMat`.
Block Anderson: the one-block pair bound at `lamV = 0`
(`EMCTE2BA_bad2_subset`; `UNBad2Boundk_ba`). -/
def UNBad2Boundk (K : ∀ d, UNKind d) : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (t 𝔡 E : ℝ) (a0 : Zd d (sz.L n)) (p : ℝ≥0∞),
    3 ≤ d → 0 < 𝔡 → (sz.W n : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n →
    (∀ b : Zd d (sz.L n), ouP ((K d).M sz).toUNModel n
        {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E b (ouMatC ((K d).M sz) n t ω)} ≤ p) →
    ouP ((K d).M sz).toUNModel n
        {ω | ∃ α β, |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues α - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues β - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            (sz.W n : ℝ) ^ (-(𝔡 / 6)) ≤
              ‖blockM2 d (sz.L n) (sz.W n) ((K d).lamV sz n) (ouMatC_isHermitian ((K d).M sz) n t ω) a0 α β‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p

/-- `κ_eff = min κ (min 2 (2r))` of the K-forms: positive, `≤ κ`, `≤ 2`, `κ_eff/2 ≤ r`. -/
theorem EMCTE2BA_keff {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) :
    0 < min κ (min 2 (2 * r)) ∧ min κ (min 2 (2 * r)) ≤ κ ∧ min κ (min 2 (2 * r)) ≤ 2 ∧
      min κ (min 2 (2 * r)) / 2 ≤ r := by
  refine ⟨lt_min hκ (lt_min (by norm_num) (by positivity)), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  have := (min_le_right κ (min 2 (2 * r))).trans (min_le_right (2 : ℝ) (2 * r))
  linarith

/-- The `Jak` bad-block hypothesis `hbad` of a kind, from `UNBadBoundk`, `UNOUQUEk` (at `κ`, `τ_Q = 𝔡/30`) and `(eq:WO)`. -/
theorem EMCTE2BA_hbad_of_K (K : ∀ d, UNKind d) (hbb : UNBadBoundk K) {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d)
    (𝔡 τU κ : ℝ) (h𝔡 : 0 < 𝔡) (hκ : 0 < κ) (hwo : sz.WO 𝔡) (hQ : UNOUQUEk (K d) sz 𝔡 τU) :
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n → ∀ E : ℝ, (K d).bulk sz κ E n →
      ∀ y : Idx d (sz.L n) (sz.W n), ouP ((K d).M sz).toUNModel n
        {ω | ∃ α, |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues α - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            (sz.W n : ℝ) ^ (-(𝔡 / 6)) ≤
              ‖blockM d (sz.L n) (sz.W n) ((K d).lamV sz n) (ouMatC_isHermitian ((K d).M sz) n t ω)
                (siteBlock d (sz.L n) (sz.W n) y) α‖} ≤
        ((2 * d + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((sz.W n : ℝ) ^ (-(𝔡 / 30))) := by
  filter_upwards [hQ κ (𝔡 / 30) hκ (by positivity), hwo] with n hn hw t ht0 htT E hE y
  have hq := Jak_queBound_eq (sz.W n) h𝔡
  exact hbb d sz n t 𝔡 E y _ hd h𝔡 hw.1 (fun b => hq ▸ hn t ht0 htT E hE b)

/-- The `Uyw` pair-block hypothesis `hbad` of a kind, from `UNBad2Boundk`, `UNOUQUEk` and `(eq:WO)`. -/
theorem EMCTE2BA_hbad2_of_K (K : ∀ d, UNKind d) (hbb : UNBad2Boundk K) {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d)
    (𝔡 τU κ : ℝ) (h𝔡 : 0 < 𝔡) (hκ : 0 < κ) (hwo : sz.WO 𝔡) (hQ : UNOUQUEk (K d) sz 𝔡 τU) :
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n → ∀ E : ℝ, (K d).bulk sz κ E n →
      ∀ y : Idx d (sz.L n) (sz.W n), ouP ((K d).M sz).toUNModel n
        {ω | ∃ α β, |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues α - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues β - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            (sz.W n : ℝ) ^ (-(𝔡 / 6)) ≤
              ‖blockM2 d (sz.L n) (sz.W n) ((K d).lamV sz n) (ouMatC_isHermitian ((K d).M sz) n t ω)
                (siteBlock d (sz.L n) (sz.W n) y) α β‖} ≤
        ((2 * d + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((sz.W n : ℝ) ^ (-(𝔡 / 30))) := by
  filter_upwards [hQ κ (𝔡 / 30) hκ (by positivity), hwo] with n hn hw t ht0 htT E hE y
  have hq := Uyw_queBound_eq (sz.W n) h𝔡
  exact hbb d sz n t 𝔡 E (siteBlock d (sz.L n) (sz.W n) y) _ hd h𝔡 hw.1 (fun b => hq ▸ hn t ht0 htT E hE b)

/-- **`Jak`, model-generic**: `unJak_of_ouClaims` over a kind `K`: the profile coupling
`(K d).lamV` in `scirc`, `blockM`, the bulk window `UNBulkWindowk` for `hdiag` at `κ_eff = min κ (min 2 (2r))`, the bad-event
transfer `UNBadBoundk`.  `C = 3 nf + 16`, `c' = 𝔠𝔡/30` as in the band. -/
theorem unJak_of_ouClaimsk (K : ∀ d, UNKind d) (hbw : UNBulkWindowk K) (hbb : UNBadBoundk K) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
        UNOUQUEk (K d) sz 𝔡 τU → UNOUDiagk (K d) sz τU →
          UNJakk (K d) sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30) := by
  intro d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτ hτ4 hQUE hDiag C₀ ε hC₀ hε
  have hcd : 𝔠 * 𝔡 ≤ 1 / 2 := un_cd_le_half d (by omega) 𝔠 𝔡 sz hadm
  obtain ⟨h𝔠, h𝔡, hsize', hband, hWO⟩ := hadm
  obtain ⟨κ', r, hκ', hr, hw⟩ := hbw d sz κ hκ
  obtain ⟨hκe0, hκeκ, hκ2, hκer⟩ := EMCTE2BA_keff hκ hr
  generalize min κ (min 2 (2 * r)) = κe at hκe0 hκeκ hκ2 hκer
  have hcd0 : 0 < 𝔠 * 𝔡 := mul_pos h𝔠 h𝔡
  -- parameters fixed before `n`: `c = 2𝔠𝔡`, `δ = τU/(nf+5)` and the exponent `D` of `UNOUDiag`
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 2 * (𝔠 * 𝔡) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; linarith
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = τU / (nf + 5) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hmδ : ((nf : ℝ) + 3) * δ ≤ τU := by
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (1 + τU) * ((nf : ℝ) + 3) + 3 := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hDdef]; positivity
  have hsize : Tendsto (fun n => Nsz sz n) atTop atTop := hsize'
  -- the eventual conditions on `n` (finitely many, uniform in `t, s, z, i, y, b₁, b₂`)
  have ev1 : ∀ᶠ n in atTop, 12 * (3 + (nf : ℝ)) ≤ Nsz sz n :=
    hsize.eventually_ge_atTop _
  have ev2 : ∀ᶠ n in atTop, 2 * C₀ ≤ Nsz sz n ^ (c / 6) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have ev3 : ∀ᶠ n in atTop, C₀ / Nsz sz n + 2 * Nsz sz n ^ (-1 + 2 * τU) < κe / 4 := by
    have h1 : Tendsto (fun n => C₀ / Nsz sz n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsize
    have h2 : Tendsto (fun n => Nsz sz n ^ (-1 + 2 * τU)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - 2 * τU) (by linarith)).comp hsize
      refine this.congr fun n => ?_
      simp only [Function.comp]; congr 1; ring
    have h3 := h1.add (h2.const_mul 2)
    simp only [mul_zero, add_zero] at h3
    exact h3.eventually_lt_const (by positivity)
  have ev4 : ∀ᶠ n in atTop, Nsz sz n ^ (-1 + c / 6) < κe / 2 := by
    have h2 : Tendsto (fun n => Nsz sz n ^ (-1 + c / 6)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - c / 6) (by linarith)).comp hsize
      refine this.congr fun n => ?_
      simp only [Function.comp]; congr 1; ring
    exact h2.eventually_lt_const (by positivity)
  have ev5 : ∀ᶠ n in atTop,
      3 * ((193 + 128 / κe ^ 2) + 4 * ((2 * d + 1 : ℕ) : ℝ)) * (6 + 16 / τU + 8 / κe) ≤
        Nsz sz n ^ (6 * τU) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have evD := hDiag κ' δ D hκ' hδ hD0
  have evQ := EMCTE2BA_hbad_of_K K hbb hd sz 𝔡 τU κ h𝔡 hκ hWO hQUE
  filter_upwards [hband, hWO, ev1, ev2, ev3, ev4, ev5, evD, evQ, hE] with
    n hWn hWOn h1 h2 h3 h4 h5 hDn hQn hEn
  intro z hz t ht0 htT s i y b₁ b₂
  have hX1 : (1 : ℝ) ≤ Nsz sz n := by
    have : (0 : ℝ) ≤ nf := nf.cast_nonneg
    linarith
  have hsc : s.card ≤ nf := by simpa using Finset.card_le_univ s
  have hfix := Jak_fixed_time (sz.three_le_L n) ((K d).lamV sz n) (ouP ((K d).M sz).toUNModel n)
    (ouMatC ((K d).M sz) n t) (ouMatC_isHermitian ((K d).M sz) n t) (X := Nsz sz n)
    (𝔠 := 𝔠) (𝔡 := 𝔡) (c := c) (κ := κe) (τ := τU) (δ := δ) (C₀ := C₀) (E := E) (D := D)
    (m := nf) rfl hWn h𝔠 h𝔡 hcdef hcd hκe0 hκ2 hτ hδ hmδ (by rw [hDdef]) h1 h2 h3 h4 h5
    (fun e he => hDn t ht0 htT e (hw n E e hEn (he.le.trans hκer))) s z (z i) (fun j => hz j)
    (hz i) y (hQn t ht0 htT E hEn y) b₁ b₂
  refine hfix.trans ?_
  calc Nsz sz n ^ (1 - 𝔠 * 𝔡 / 30 + (3 * (s.card : ℝ) + 16) * τU)
      ≤ Nsz sz n ^ (1 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        have : (s.card : ℝ) ≤ nf := by exact_mod_cast hsc
        nlinarith
    _ = 1 * Nsz sz n ^ (1 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := (one_mul _).symm
    _ ≤ Nsz sz n ^ ε * Nsz sz n ^ (1 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := by
        gcongr
        exact Real.one_le_rpow hX1 hε.le


/-- **`Uyw`, model-generic**: `unUyw_of_ouClaims` over a kind `K`; the pair-event transfer is
`UNBad2Boundk`.  `C = 3 nf + 16`, `c' = 𝔠𝔡/30` as in the band. -/
theorem unUyw_of_ouClaimsk (K : ∀ d, UNKind d) (hbw : UNBulkWindowk K) (hbb : UNBad2Boundk K) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
        UNOUQUEk (K d) sz 𝔡 τU → UNOUDiagk (K d) sz τU →
          UNUywk (K d) sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30) := by
  intro d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτ hτ4 hQUE hDiag C₀ ε hC₀ hε
  have hcd : 𝔠 * 𝔡 ≤ 1 / 2 := un_cd_le_half d (by omega) 𝔠 𝔡 sz hadm
  obtain ⟨h𝔠, h𝔡, hsize', hband, hWO⟩ := hadm
  obtain ⟨κ', r, hκ', hr, hw⟩ := hbw d sz κ hκ
  obtain ⟨hκe0, hκeκ, hκ2, hκer⟩ := EMCTE2BA_keff hκ hr
  generalize min κ (min 2 (2 * r)) = κe at hκe0 hκeκ hκ2 hκer
  have hcd0 : 0 < 𝔠 * 𝔡 := mul_pos h𝔠 h𝔡
  -- parameters fixed before `n`: `c = 2𝔠𝔡`, `δ = τU/(nf+5)` and the exponent `D` of `UNOUDiag`
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 2 * (𝔠 * 𝔡) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; linarith
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = τU / (nf + 5) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hmδ : ((nf : ℝ) + 3) * δ ≤ τU := by
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (1 + τU) * ((nf : ℝ) + 4) + 3 := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hDdef]; positivity
  have hsize : Tendsto (fun n => Nsz sz n) atTop atTop := hsize'
  -- the eventual conditions on `n` (finitely many, uniform in `t, s, z, i, j, y, b₁, b₂`)
  have ev1 : ∀ᶠ n in atTop, 16 * (4 + (nf : ℝ)) ≤ Nsz sz n :=
    hsize.eventually_ge_atTop _
  have ev2 : ∀ᶠ n in atTop, 2 * C₀ ≤ Nsz sz n ^ (c / 6) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have ev3 : ∀ᶠ n in atTop, C₀ / Nsz sz n + 2 * Nsz sz n ^ (-1 + 2 * τU) < κe / 4 := by
    have h1 : Tendsto (fun n => C₀ / Nsz sz n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsize
    have h2 : Tendsto (fun n => Nsz sz n ^ (-1 + 2 * τU)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - 2 * τU) (by linarith)).comp hsize
      refine this.congr fun n => ?_
      simp only [Function.comp]; congr 1; ring
    have h3 := h1.add (h2.const_mul 2)
    simp only [mul_zero, add_zero] at h3
    exact h3.eventually_lt_const (by positivity)
  have ev4 : ∀ᶠ n in atTop, Nsz sz n ^ (-1 + c / 6) < κe / 2 := by
    have h2 : Tendsto (fun n => Nsz sz n ^ (-1 + c / 6)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - c / 6) (by linarith)).comp hsize
      refine this.congr fun n => ?_
      simp only [Function.comp]; congr 1; ring
    exact h2.eventually_lt_const (by positivity)
  have ev5 : ∀ᶠ n in atTop,
      2 * ((193 + 256 / κe ^ 2) + 4 * ((2 * d + 1 : ℕ) : ℝ)) ≤ Nsz sz n ^ (6 * τU) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have evD := hDiag κ' δ D hκ' hδ hD0
  have evQ := EMCTE2BA_hbad2_of_K K hbb hd sz 𝔡 τU κ h𝔡 hκ hWO hQUE
  filter_upwards [hband, hWO, ev1, ev2, ev3, ev4, ev5, evD, evQ, hE] with
    n hWn hWOn h1 h2 h3 h4 h5 hDn hQn hEn
  intro z hz t ht0 htT s i j _hij y b₁ b₂
  have hX1 : (1 : ℝ) ≤ Nsz sz n := by
    have : (0 : ℝ) ≤ nf := nf.cast_nonneg
    linarith
  have hsc : s.card ≤ nf := by simpa using Finset.card_le_univ s
  have hfix := Uyw_fixed_time (sz.three_le_L n) ((K d).lamV sz n) (ouP ((K d).M sz).toUNModel n)
    (ouMatC ((K d).M sz) n t) (ouMatC_isHermitian ((K d).M sz) n t) (X := Nsz sz n)
    (𝔠 := 𝔠) (𝔡 := 𝔡) (c := c) (κ := κe) (τ := τU) (δ := δ) (C₀ := C₀) (E := E) (D := D)
    (m := nf) rfl hWn h𝔠 h𝔡 hcdef hcd hκe0 hκ2 hτ hδ hmδ (by rw [hDdef]) h1 h2 h3 h4 h5
    (fun e he => hDn t ht0 htT e (hw n E e hEn (he.le.trans hκer))) s z (z i) (z j)
    (fun k => hz k) (hz i) (hz j) y (hQn t ht0 htT E hEn y) b₁ b₂
  refine hfix.trans ?_
  calc Nsz sz n ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (s.card : ℝ) + 16) * τU)
      ≤ Nsz sz n ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        have : (s.card : ℝ) ≤ nf := by exact_mod_cast hsc
        nlinarith
    _ = 1 * Nsz sz n ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := (one_mul _).symm
    _ ≤ Nsz sz n ^ ε * Nsz sz n ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := by
        gcongr
        exact Real.one_le_rpow hX1 hε.le


/-! ## 5. The statement `UNEMCTE2RowBA` -/

/-- **The weighted [DYYY25, (2.21)] of the block Anderson kind**, `UNEMCTE2Rowk` at `UNKind.ba`:
`Cn = 1`, `τ₀ = 1`; the size hypothesis is the third conjunct of `Admissible`; the bulk premise is not used. -/
theorem unEMCTE2RowBA_holds : UNEMCTE2RowBA := by
  intro d _ 𝔠 𝔡 sz hA κ _ E _ nf
  exact ⟨1, 1, one_pos, fun τU _ _ => unEMCTE2k_ba d sz hA.2.2.1 E nf τU 1 (one_mul τU).ge⟩

/-! ## 6. The bulk window and the one-block bad events at block Anderson -/

/-- **The bulk window of block Anderson**, `κ' = κ/2`, `r = (π κ)³/8` (`BAbulk_window`). -/
theorem UNBulkWindowk_ba : UNBulkWindowk (fun d => UNKind.ba d) := fun d sz κ hκ =>
  ⟨κ / 2, (Real.pi * κ) ^ 3 / 8, by positivity, by positivity,
    fun n E e hE he => BAbulk_window d (sz.L n) (sz.lam n) κ E e hκ hE he⟩

/-- **The `Jak` bad block of block Anderson is a one-block event** (`unBadYBA_measure_le`,
no factor `2d + 1`), contained in `UNBadY` at any coupling (`unBadY_of_blockM`); then `p ≤ (2d + 1) p`. -/
theorem UNBadBoundk_ba : UNBadBoundk (fun d => UNKind.ba d) := by
  intro d sz n t 𝔡 E y p _ h𝔡 hlam hp
  have h := unBadYBA_measure_le (ouP ((UNKind.ba d).M sz).toUNModel n) (sz.three_le_L n)
    (by exact_mod_cast sz.W_pos n) h𝔡 hlam y (fun ω => ouMatC ((UNKind.ba d).M sz) n t ω) p hp
  refine le_trans (measure_mono ?_) (h.trans ?_)
  · rintro ω ⟨α, h1, h2⟩
    exact unBadY_of_blockM (sz.three_le_L n) (ouMatC_isHermitian _ n t ω) y α h1 h2
  · exact le_mul_of_one_le_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))

/-- **The one-block pair lemma**: at the profile coupling `lamV = 0`, `blockM2 0 … a0 α β` is the block quantity
of `a0` itself (`SBR_zero_ne`, `sum_SBR_row`), so a pair bad event at `a0` is a `queBadMat` failure at `a0` (`un_window_sub`;
the eigenvectors are the orthonormal eigenbasis of `M`).  (The lemma `UywKernel_bad2_subset` is private and
single-coupling.) -/
theorem EMCTE2BA_bad2_subset {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {lamQ 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ))
    (h𝔡 : 0 < 𝔡) (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ) (a0 : Zd d L)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (α β : Idx d L W)
    (hα : |hM.eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3))
    (hβ : |hM.eigenvalues β - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3))
    (hθ : (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM2 d L W 0 hM a0 α β‖) :
    queBadMat d L W lamQ (𝔡 / 3) (𝔡 / 6) E a0 M := by
  classical
  have hW0 : (0 : ℝ) < (W : ℝ) := lt_of_lt_of_le one_pos hW
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W)) (Nat.pos_of_ne_zero (NeZero.ne L))) _
  have hrow : ∑ b : Zd d L, SBR d L 0 b a0 = 1 := by
    simp_rw [SBR_comm _ a0]; exact sum_SBR_row hL a0
  have hzero : ∀ b, b ≠ a0 → SBR d L 0 b a0 = 0 := fun b hb => by
    by_contra h; exact hb (SBR_zero_ne h)
  have hone : SBR d L 0 a0 a0 = 1 := by
    rwa [Finset.sum_eq_single a0 (fun b _ hb => hzero b hb) (by simp)] at hrow
  have hM2 : blockM2 d L W 0 hM a0 α β = (((W * L) ^ d : ℕ) : ℂ) / (W : ℂ) ^ d *
      (∑ x ∈ Iblk d L W a0, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
        (if α = β then 1 else 0) := by
    unfold blockM2
    rw [Finset.sum_eq_single a0 (fun b _ hb => by rw [hzero b hb]; simp) (by simp), hone]
    simp
  refine ⟨hM.eigenvalues, fun k x => hM.eigenvectorBasis k x, isOrthoEigenbasis_eigenvectorBasis hM, β, α,
    hβ.trans (un_window_sub (d := d) hW hN h𝔡 hlam), hα.trans (un_window_sub (d := d) hW hN h𝔡 hlam), ?_⟩
  set N : ℝ := (((W * L) ^ d : ℕ) : ℝ) with hNdef
  have hWdc : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne W))
  have hNc : (((W * L) ^ d : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero d (Nat.mul_ne_zero (NeZero.ne W) (NeZero.ne L)))
  have hite : (if α = β then (1 : ℂ) else 0) = if β = α then 1 else 0 := by simp only [eq_comm]
  have hrel : blockM2 d L W 0 hM a0 α β = (((W * L) ^ d : ℕ) : ℂ) / (W : ℂ) ^ d *
      ((∑ x ∈ Iblk d L W a0, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
        (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) * (if β = α then 1 else 0)) := by
    rw [hM2]; simp only [mul_sub, hite]; congr 1; field_simp
  have hnorm : ‖blockM2 d L W 0 hM a0 α β‖ = N / (W : ℝ) ^ d *
      ‖(∑ x ∈ Iblk d L W a0, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
        (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) * (if β = α then 1 else 0)‖ := by
    rw [hrel, norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_natCast]
  have hWc : (W : ℝ) ^ ((d : ℝ) - 𝔡 / 6) = (W : ℝ) ^ d * (W : ℝ) ^ (-(𝔡 / 6)) := by
    rw [sub_eq_add_neg, Real.rpow_add hW0, Real.rpow_natCast]
  rw [hWc, div_le_iff₀ hN]
  have hq := hnorm ▸ hθ
  have h2 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ (W : ℝ) ^ d / N)
  have h3 : (W : ℝ) ^ d / N * (N / (W : ℝ) ^ d) = 1 := by field_simp
  calc (W : ℝ) ^ d * (W : ℝ) ^ (-(𝔡 / 6)) = (W : ℝ) ^ d / N * (W : ℝ) ^ (-(𝔡 / 6)) * N := by field_simp
    _ ≤ (W : ℝ) ^ d / N * (N / (W : ℝ) ^ d *
        ‖(∑ x ∈ Iblk d L W a0, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
          (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) * (if β = α then 1 else 0)‖) * N := by gcongr
    _ = _ := by rw [← mul_assoc, h3, one_mul]


/-- **The `Uyw` pair event of block Anderson is a one-block event** at `a0`; then `p ≤ (2d + 1) p`. -/
theorem UNBad2Boundk_ba : UNBad2Boundk (fun d => UNKind.ba d) := by
  intro d sz n t 𝔡 E a0 p _ h𝔡 hlam hp
  refine le_trans (measure_mono ?_) ((hp a0).trans ?_)
  · rintro ω ⟨α, β, hα, hβ, hθ⟩
    exact EMCTE2BA_bad2_subset (sz.three_le_L n) (by exact_mod_cast sz.W_pos n) h𝔡 hlam a0
      (ouMatC_isHermitian _ n t ω) α β hα hβ hθ
  · exact le_mul_of_one_le_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))


end RBM.Univ

end
