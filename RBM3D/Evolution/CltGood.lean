/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.FarEntry
import RBM3D.Chain.CltGen
import RBM3D.Evolution.CltPath
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The good event of the replacement step on the finite model

Paper (arXiv:2507.20274): the coordinate tails are the entry bounds `|X_{ij}| ≺ S_{ij}^{1/2}` used
at the step length `W^{-1/2}`; the bounds `|G_{xy}| ≤ 2` and the far decay `|G_{xy}| ≤ W^{-D'}` are
`(Gt_bound_flow)` at the section `τ` and the log-scale far decay of (5.36) `eq:bound_isolated`.

Contents (namespace `RBM.Evol`), every `∀ᶠ n` along `sz : Sizes d`:
* `cltCoord_tail : CltCoordTail sz`: every real coordinate exceeds `W^{-1/2}` with
  probability `≤ 2 exp(-W/2) ≤ N^{-D}` (variance `gvarF ≤ W^{-d}`, `W ≥ N^𝔠`, `d ≥ 2`);
* the carrier forms (section 5): `cltGmax_whpOf` (all `G_τ(±)_{xy}` are `≤ 2` outside an event of
  probability `≤ N^{-D}`: `STLocalEntryUgL` at `τ`, `|M_{xy}| ≤ 1`, `STWB ≤ 2 N^{-a}`),
  `cltFarEntry_whpOf` (far entries are `≤ W^{-D'}` outside such an event) and `cltGood_whpOf`
  (`cltGoodAtOf` fails with probability `≤ N^{-D}`), all under the premise block `HCltOf`.

The union over the `N²` entries is inside the probability of `Prec` (`badSetAt`), so the exponents
are `D`, `D'+1` without a further `+2`.  The transfer from `seqP sz` to `PF` is `seqP_map_slice`
and `Measure.map_apply` for the measurable failure events (the integral form is `cltTransfer` of
`CltSwap.lean`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

/-! ## 1. The statements -/

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- The conclusion event of `CltCoordTail`: every real coordinate exceeds `W^{-1/2}` with
probability `≤ N^{-D}`. -/
def CltCoordConcl (D : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ c : CoordF d (sz.L n) (sz.W n),
    PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- **The coordinate tails**: every real coordinate exceeds `W^{-1/2}` with probability
`≤ N^{-D}`, eventually (`gvarF ≤ W^{-d}`, `d ≥ 2`, `W ≥ N^𝔠`). -/
def CltCoordTail : Prop :=
  2 ≤ d → ∀ 𝔠 : ℝ, 0 < 𝔠 → sz.SizeTendsto → sz.Bandwidth 𝔠 →
    ∀ D : ℝ, 0 < D → CltCoordConcl sz D

end Pins

/-! ## 2. Private helpers -/

section Helpers

/-- The transfer from the common product space `Sizes.seqP sz` to the finite model `PF`, for a
measurable event (`Sizes.seqP_map_slice`). -/
private theorem cltGood_P_le_of_seqP {d : ℕ} (sz : Sizes d) (n : ℕ)
    {S : Set (Ω d (sz.L n) (sz.W n))} (hS : MeasurableSet S) {b : ℝ≥0∞}
    (h : Sizes.seqP sz (Sizes.slice sz n ⁻¹' S) ≤ b) :
    PF d (sz.L n) (sz.W n) (sz.lam n) S ≤ b := by
  rw [← Sizes.seqP_map_slice sz n, Measure.map_apply (Sizes.measurable_slice sz n) hS]
  exact h

private theorem cltGood_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

end Helpers

/-! ## 3. The coordinate tail -/

section CoordTail

/-- Every coordinate variance is at most `W^{-d}` (`gvarF ≤ svarF = W^{-d} sbKernelR ≤ W^{-d}`,
`∑ sbKernelR = 1`). -/
private theorem cltGood_gvarF_le {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (g : ℝ)
    (c : CoordF d L W) : (gvarF d L W g c : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hk : sbKernelR d L g ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1 := by
    rw [← sum_sbKernelR d L g hL]
    exact Finset.single_le_sum (f := fun x => sbKernelR d L g x)
      (fun x _ => sbKernelR_nonneg d L g x) (Finset.mem_univ _)
  have hs : svarF d L W g c.1 c.2.1 ≤ ((W : ℝ) ^ d)⁻¹ := by
    unfold svarF SBR
    simp only [Matrix.of_apply]
    calc ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g ((split d L W c.1).1 - (split d L W c.2.1).1)
        ≤ ((W : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := mul_one _
  have h0 := svarF_nonneg d L W g c.1 c.2.1
  change (if c.1 = c.2.1 then svarF d L W g c.1 c.2.1 else svarF d L W g c.1 c.2.1 / 2) ≤ _
  split_ifs <;> linarith

/-- The Gaussian tail of one coordinate on the finite model:
`P(W^{-1/2} < |ω_c|) ≤ 2 exp(-W/2)` (variance at most `W^{-d}`, `d ≥ 2`). -/
private theorem cltGood_coord_tail_finite {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (hd : 2 ≤ d) (g : ℝ) (c : CoordF d L W) :
    PF d L W g {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤
      ENNReal.ofReal (2 * Real.exp (-(W : ℝ) / 2)) := by
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  set B : ℝ := (W : ℝ) ^ (-(1 / 2 : ℝ)) with hBdef
  have hB : 0 ≤ B := Real.rpow_nonneg hW.le _
  have hB2 : B ^ 2 = (W : ℝ)⁻¹ := by
    rw [hBdef, ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num [Real.rpow_neg_one]
  have hmeas : Measurable (fun ω : Ω d L W => ω c) := measurable_pi_apply c
  have hv0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  let v : ℝ≥0 := ⟨((W : ℝ) ^ d)⁻¹, hv0⟩
  have hsg : HasSubgaussianMGF (fun ω : Ω d L W => ω c) v (PF d L W g) := by
    rw [← HasSubgaussianMGF.id_map_iff hmeas.aemeasurable]
    have hmap : (PF d L W g).map (fun ω : Ω d L W => ω c) = gaussianReal 0 (gvarF d L W g c) :=
      Measure.infinitePi_map_eval _ c
    rw [hmap]
    refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
    rw [mgf_id_gaussianReal]
    apply Real.exp_le_exp.2
    have h1 := cltGood_gvarF_le (W := W) hL g c
    have h2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    have hvc : (v : ℝ) = ((W : ℝ) ^ d)⁻¹ := rfl
    simp only [zero_mul, zero_add]
    rw [hvc]
    nlinarith
  have h1 := hsg.measure_ge_le hB
  have h2 := hsg.neg.measure_ge_le hB
  have hexp : -B ^ 2 / (2 * (v : ℝ)) ≤ -(W : ℝ) / 2 := by
    change -B ^ 2 / (2 * ((W : ℝ) ^ d)⁻¹) ≤ _
    rw [hB2]
    have hWd : (W : ℝ) ^ 2 ≤ (W : ℝ) ^ d := pow_le_pow_right₀ hW1 hd
    have hWd0 : (0 : ℝ) < (W : ℝ) ^ d := by positivity
    have : -(W : ℝ)⁻¹ / (2 * ((W : ℝ) ^ d)⁻¹) = -((W : ℝ) ^ d / (W : ℝ)) / 2 := by
      field_simp
    rw [this]
    have h3 : (W : ℝ) ≤ (W : ℝ) ^ d / (W : ℝ) := by
      rw [le_div_iff₀ hW]; nlinarith
    linarith
  have h1' := h1.trans (Real.exp_le_exp.2 hexp)
  have h2' := h2.trans (Real.exp_le_exp.2 hexp)
  have hsub : {ω : Ω d L W | B < |ω c|} ⊆
      {ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : Ω d L W => ω c)) ω} := by
    intro ω hω
    have hω' : B < |ω c| := hω
    rcases le_abs.1 (le_of_lt hω') with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hf1 : PF d L W g {ω | B ≤ ω c} ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h1'
  have hf2 : PF d L W g {ω | B ≤ (-(fun ω : Ω d L W => ω c)) ω} ≤
      ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h2'
  have hp : (0 : ℝ) ≤ Real.exp (-(W : ℝ) / 2) := (Real.exp_pos _).le
  calc PF d L W g {ω | B < |ω c|}
      ≤ PF d L W g ({ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : Ω d L W => ω c)) ω}) :=
        measure_mono hsub
    _ ≤ PF d L W g {ω | B ≤ ω c} + PF d L W g {ω | B ≤ (-(fun ω : Ω d L W => ω c)) ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) +
          ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := add_le_add hf1 hf2
    _ = ENNReal.ofReal (2 * Real.exp (-(W : ℝ) / 2)) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf

/-- `2 exp(-W/2) ≤ N^{-D}` eventually, from `W ≥ N^𝔠` and `N → ∞`. -/
private theorem cltGood_tail_eventually {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hN : sz.SizeTendsto) (hW : sz.Bandwidth 𝔠) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (-((sz.W n : ℕ) : ℝ) / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
  have hx : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  have h1 : Tendsto (fun x : ℝ => x ^ (D / 𝔠) * Real.exp (-(1 / 2) * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D / 𝔠) (1 / 2) (by norm_num)
  filter_upwards [(h1.comp hx).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), hW,
    hN.eventually_gt_atTop 0] with n hn hWn hN0
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := hN0
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set x : ℝ := N ^ 𝔠 with hxdef
  have hND : x ^ (D / 𝔠) = N ^ D := by
    rw [hxdef, ← Real.rpow_mul hNpos.le]
    congr 1
    field_simp
  have hNDpos : 0 < N ^ D := Real.rpow_pos_of_pos hNpos D
  have hexp : Real.exp (-((sz.W n : ℕ) : ℝ) / 2) ≤ Real.exp (-(1 / 2) * x) := by
    apply Real.exp_le_exp.2
    linarith
  have hexp0 : 0 < Real.exp (-(1 / 2) * x) := Real.exp_pos _
  have hcomb : 2 * Real.exp (-(1 / 2) * x) * N ^ D ≤ 1 := by
    have : N ^ D * Real.exp (-(1 / 2) * x) < 1 / 2 := by
      have hn' : x ^ (D / 𝔠) * Real.exp (-(1 / 2) * x) < 1 / 2 := hn
      rwa [hND] at hn'
    nlinarith
  rw [Real.rpow_neg hNpos.le]
  calc 2 * Real.exp (-((sz.W n : ℕ) : ℝ) / 2) ≤ 2 * Real.exp (-(1 / 2) * x) := by linarith
    _ = 2 * Real.exp (-(1 / 2) * x) * N ^ D * (N ^ D)⁻¹ := by field_simp
    _ ≤ 1 * (N ^ D)⁻¹ := by gcongr
    _ = (N ^ D)⁻¹ := one_mul _

/-- **Item 2.**  Every real coordinate exceeds `W^{-1/2}` with probability at most `N^{-D}`,
eventually. -/
theorem cltCoord_tail {d : ℕ} (sz : Sizes d) : CltCoordTail sz := by
  intro hd 𝔠 h𝔠 hN hW D hD
  unfold CltCoordConcl
  filter_upwards [cltGood_tail_eventually sz h𝔠 hN hW D] with n hn c
  exact (cltGood_coord_tail_finite (sz.three_le_L n) hd _ c).trans (ENNReal.ofReal_le_ofReal hn)

end CoordTail

/-! ## 4. A bound on `STWB` -/

section Gmax

/-- `STWB ≤ 2 N^{-a}` with `a = min(2𝔠𝔡, δ)`, eventually, uniformly in `K` and in `u ≤ t_n` (generic in the range exponent `δ`):
`W^{-d} B_{u,K} ≤ (λ² W^d)⁻¹ + (N (1-u))⁻¹`, `(λ² W^d)⁻¹ ≤ W^{-2𝔡} ≤ N^{-2𝔠𝔡}`
(`(eq:WO)`, `W ≥ N^𝔠`), `(N (1-u))⁻¹ ≤ N^{-ε/2}` (`RangeCond`). -/
private theorem cltGood_STWB_leOf {d : ℕ} (sz : Sizes d) {𝔠 𝔡 δ : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (_hδ : 0 < δ) {t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) (hRC : sz.RangeCond δ t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n → ∀ K : ℕ,
      STWB sz n u K ≤ 2 * (((sz.size n : ℕ) : ℝ) ^ min (2 * 𝔠 * 𝔡) δ)⁻¹ := by
  obtain ⟨h𝔠, h𝔡, hN, hBW, hWO⟩ := id hadm
  filter_upwards [hBW, hWO, hRC] with n hBn hWOn hRn u hu K
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hu1 : u < 1 := lt_of_le_of_lt hu (ht1 n)
  have hv : 0 < 1 - u := by linarith
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hWOn.1
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hA := lam_sq_mul_pow_ge sz n hWOn.1
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hmain : STWB sz n u K ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ +
      (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
    unfold STWB Bparam
    rw [abs_of_pos hv]
    have hT1 : (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
        (sz.lam n ^ 2)⁻¹ := by
      have ha : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
      have hb : ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]))
      calc (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
          ≤ (sz.lam n ^ 2)⁻¹ * 1 := mul_le_mul ha hb (by positivity) (by positivity)
        _ = _ := mul_one _
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
          ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ +
            (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by gcongr
      _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ +
            (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
          rw [hNe]; field_simp
  set a : ℝ := min (2 * 𝔠 * 𝔡) δ with ha
  have ha1 : a ≤ 2 * 𝔠 * 𝔡 := min_le_left _ _
  have ha2 : a ≤ δ := min_le_right _ _
  have hNa : 0 < ((sz.size n : ℕ) : ℝ) ^ a := Real.rpow_pos_of_pos hNpos _
  -- first term
  have h1 : (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ a)⁻¹ := by
    apply inv_anti₀ hNa
    have e1 : ((sz.size n : ℕ) : ℝ) ^ a ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 𝔠 * 𝔡) :=
      Real.rpow_le_rpow_of_exponent_le hN1 ha1
    have e2 : ((sz.size n : ℕ) : ℝ) ^ (2 * 𝔠 * 𝔡) =
        (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (2 * 𝔡) := by
      rw [← Real.rpow_mul hNpos.le]; congr 1; ring
    have e3 : (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (2 * 𝔡) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hBn (by linarith)
    linarith
  -- second term
  have h2 : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ a)⁻¹ := by
    apply inv_anti₀ hNa
    have e1 : ((sz.size n : ℕ) : ℝ) ^ a ≤ ((sz.size n : ℕ) : ℝ) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hN1 ha2
    have e2 : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) =
        ((sz.size n : ℕ) : ℝ) ^ δ := by
      calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + δ)
          = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) := by
            rw [Real.rpow_one]
        _ = ((sz.size n : ℕ) : ℝ) ^ (1 + (-1 + δ)) := (Real.rpow_add hNpos _ _).symm
        _ = _ := by congr 1; ring
    have e3 : ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u := by linarith
    calc ((sz.size n : ℕ) : ℝ) ^ a ≤ ((sz.size n : ℕ) : ℝ) ^ δ := e1
      _ = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) := e2.symm
      _ ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul_of_nonneg_left e3 hNpos.le
  linarith

end Gmax

/-! ## 5. The carrier forms

The statements over `C : FlowFM sz`: the law of the entries is `PF d L W (g' n)` (`g' = sz.lam` at
the band, `0` at block Anderson), the matrix is `H₀ n + H_u(ω)` and the spectral value is `C.m n`
(`gEntryOf`, `cltGoodAtOf`).  The premise block is `HCltOf` (`Chain/CltGen`) at the time `τ = s`;
`M` enters through the Ward row (`|M_{xy}| ≤ 1`) in place of `norm_mE`.  The coordinate tail
`CltCoordTail` holds for every coupling and is unchanged. -/

section Carrier

variable {d : ℕ} {sz : Sizes d} (C : RBM.BA.FlowFM sz)
  (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ)

/-- The conclusion event of `CltGmaxWhpOf`: all entries of `G_τ(±)` at `H₀ n + H_τ(ω)` are `≤ 2` outside an event of probability
`≤ N^{-D}` under `PF d L W (g' n)`. -/
def CltGmaxConclOf (τ : ℕ → ℝ) (D : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    PF d (sz.L n) (sz.W n) (g' n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        2 < ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (τ n)
          (H₀ n + Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- The conclusion event of `CltFarEntryWhpOf`: entries with `c (log W)^3 ℓ_τ ≤ |[x] - [y]|_∞` are `≤ W^{-D'}` outside an event of
probability `≤ N^{-D}`. -/
def CltFarEntryConclOf (τ : ℕ → ℝ) (c D' D : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    PF d (sz.L n) (sz.W n) (g' n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
              (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
          ((sz.W n : ℕ) : ℝ) ^ (-D') <
            ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (τ n)
              (H₀ n + Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- The conclusion of `CltGoodWhpOf`: `cltGoodAtOf` at the far threshold `θ n` holds outside an event of probability `≤ N^{-D}`. -/
def CltGoodConclOf (τ θ : ℕ → ℝ) (D' D : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    PF d (sz.L n) (sz.W n) (g' n)
        {ω | ¬ cltGoodAtOf d (sz.L n) (sz.W n) (C.m n) (E n) (τ n) (θ n) D' (H₀ n) ω} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

end Carrier

/-- **The entries of `G` over the carrier** (`(Gt_bound_flow)` at the section `s`): under `HCltOf`,
all entries of `G_s(±)` are `≤ 2` outside an event of probability `≤ N^{-D}`, eventually. -/
def CltGmaxWhpOf (d : ℕ) : Prop :=
  ∀ (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : RBM.BA.FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ),
    RBM.BA.HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → ∀ D : ℝ, 0 < D → CltGmaxConclOf C H₀ g' E s D

/-- **The far entries over the carrier** (the log-scale far decay, `STFarEntryAtLoggL`). -/
def CltFarEntryWhpOf (d : ℕ) : Prop :=
  ∀ (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : RBM.BA.FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ),
    RBM.BA.HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → ∀ c : ℝ, 0 < c → ∀ D' : ℝ, 0 < D' → ∀ D : ℝ, 0 < D →
      CltFarEntryConclOf C H₀ g' E s c D' D

/-- **The consumer's form over the carrier**: `cltGoodAtOf` holds with high probability at every far threshold
`θ n ≥ c (log W)^3 ℓ_s`. -/
def CltGoodWhpOf (d : ℕ) : Prop :=
  ∀ (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : RBM.BA.FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ),
    RBM.BA.HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → ∀ (c : ℝ) (θ : ℕ → ℝ), 0 < c →
      (∀ n, c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤ θ n) →
      ∀ D' : ℝ, 0 < D' → ∀ D : ℝ, 0 < D → CltGoodConclOf C H₀ g' E s θ D' D

section CarrierHelpers

/-- The entries of the resolvent of `H₀ + H_u(ω)` are measurable in `ω`. -/
private theorem cltGood_gEntryOf_meas {d L W : ℕ} [NeZero L] [NeZero W] (m : ℂ) (E s u : ℝ)
    (H₀ : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) (x y : Idx d L W) :
    Measurable fun ω : Ω d L W => gEntryOf d L W m E s (H₀ + Hflow d L W u ω) σ x y := by
  have hH : Measurable fun ω : Ω d L W => H₀ + Hflow d L W u ω :=
    Measurable.of_eval fun a => Measurable.of_eval fun b =>
      measurable_const.add (measurable_Hflow d L W u a b)
  exact (walk_measurable_Gres_apply (ztOf m E s) σ x y).comp hH

/-- `G(-)_{xy} = conj G(+)_{yx}` for a Hermitian `M`, in norm. -/
private theorem cltGood_norm_gEntryOf_false {d L W : ℕ} [NeZero L] [NeZero W] (m : ℂ) (E s : ℝ)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (x y : Idx d L W) :
    ‖gEntryOf d L W m E s M false x y‖ = ‖gEntryOf d L W m E s M true y x‖ := by
  have h := cltGood_Gres_conjTranspose hM (ztOf m E s) true
  have h2 : gEntryOf d L W m E s M false x y = star (gEntryOf d L W m E s M true y x) := by
    have h3 := congrFun (congrFun h x) y
    rw [Matrix.conjTranspose_apply] at h3
    exact h3.symm
  rw [h2, norm_star]

/-- A bound on `G(+)` at every pair gives the same bound for both charges. -/
private theorem cltGood_exists_trueOf {d L W : ℕ} [NeZero L] [NeZero W] (m : ℂ)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (E s : ℝ) (hM : M.IsHermitian) {r : ℝ}
    (h : ∃ (σ : Bool) (x y : Idx d L W), r < ‖gEntryOf d L W m E s M σ x y‖) :
    ∃ x y : Idx d L W, r < ‖gEntryOf d L W m E s M true x y‖ := by
  obtain ⟨σ, x, y, hr⟩ := h
  cases σ
  · rw [cltGood_norm_gEntryOf_false m E s hM] at hr
    exact ⟨y, x, hr⟩
  · exact ⟨x, y, hr⟩

end CarrierHelpers

/-- **Item 3 over the carrier.**  Under `HCltOf`, all entries of `G_s(±)` are `≤ 2` outside an event of probability `≤ N^{-D}`,
eventually: `STLocalEntryUgL` at the section `s`, `|M_{xy}| ≤ 1` from the Ward row, `STWB ≤ 2 N^{-a}`. -/
theorem cltGmax_whpOf (d : ℕ) : CltGmaxWhpOf d := by
  intro κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t h D hD
  obtain ⟨hd, hκ, hκ1, hδ, hadm, hκm, hs, hst, ht1, hrange, hRep, hWard, hMf, hLoc, hDec, hGij, hK⟩ := h
  obtain ⟨hμ, hHerm, hGL⟩ := hRep
  subst hμ
  obtain ⟨h𝔠, h𝔡, hN, hBW, hWO⟩ := id hadm
  have hsize : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hN
  set a : ℝ := min (2 * 𝔠 * 𝔡) δ with ha
  have ha0 : 0 < a := lt_min (by positivity) hδ
  have hLocS := StochDomAt.precomp_param hLoc
    (fun n (p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      ((⟨s n, le_rfl, (hst n).le⟩ : RBM.Path.TimeIcc s t n), p.1, p.2))
  have hP := hLocS (a / 2) (by linarith) D hD
  filter_upwards [hP, cltGood_STWB_leOf sz hadm hδ ht1 hrange,
    hsize.eventually (eventually_le_rpow 2 (show 0 < a / 2 by linarith)),
    hsize.eventually_ge_atTop 1] with n hn hW hq hN1
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set q : ℝ := N ^ (a / 2) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hNpos _
  have hqq : N ^ a = q * q := by
    rw [hqdef, ← Real.rpow_add hNpos]; congr 1; ring
  let T : Set (Ω d (sz.L n) (sz.W n)) := ⋃ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
    {ω | q * STWB sz n (s n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)) <
      ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
          (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) true p.1 p.2 - C.M n p.1 p.2‖ ^ 2}
  have hTmeas : MeasurableSet T := by
    refine MeasurableSet.iUnion fun p => ?_
    exact measurableSet_lt measurable_const
      (((cltGood_gEntryOf_meas (C.m n) (E n) (s n) (s n) (H₀ n) true p.1 p.2).sub
        measurable_const).norm.pow_const 2)
  have hsub : {ω : Ω d (sz.L n) (sz.W n) | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
      2 < ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
        (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) σ x y‖} ⊆ T := by
    intro ω hω
    obtain ⟨x, y, hxy⟩ := cltGood_exists_trueOf (C.m n) (E n) (s n)
      ((hHerm n).add (Hflow_isHermitian d (sz.L n) (sz.W n) (s n) ω)) hω
    refine Set.mem_iUnion.2 ⟨(x, y), ?_⟩
    have hM1 : ‖C.M n x y‖ ≤ 1 := by
      have h1 := Finset.single_le_sum (f := fun y' => ‖C.M n x y'‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ y)
      have h2 := hWard n x
      by_contra hlt
      push Not at hlt
      nlinarith [norm_nonneg (C.M n x y)]
    have h1 := norm_sub_norm_le
      (gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
        (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) true x y) (C.M n x y)
    have h2 := hW (s n) (hst n).le (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
    have h3 : q * STWB sz n (s n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) ≤ 1 := by
      calc q * STWB sz n (s n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
          ≤ q * (2 * (N ^ a)⁻¹) := mul_le_mul_of_nonneg_left h2 hq0.le
        _ = 2 / q := by rw [hqq]; field_simp
        _ ≤ 1 := by rw [div_le_one hq0]; exact hq
    change q * STWB sz n (s n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) <
      ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
          (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) true x y - C.M n x y‖ ^ 2
    have h4 : 1 < ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
          (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) true x y - C.M n x y‖ := by linarith
    nlinarith
  calc PF d (sz.L n) (sz.W n) (g' n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        2 < ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
          (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) σ x y‖}
      ≤ PF d (sz.L n) (sz.W n) (g' n) T := measure_mono hsub
    _ ≤ ENNReal.ofReal (N ^ (-D)) := cltGood_P_le_of_seqP (sz.withLam g') n hTmeas
      ((measure_mono fun ω hω => by
        obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
        refine ⟨p, ?_⟩
        have e := (hGL n (s n) ω).1 p.1 p.2
        change q * STWB sz n (s n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)) <
          ‖C.G n (s n) ω p.1 p.2 - C.M n p.1 p.2‖ ^ 2
        rw [e]
        exact hp).trans hn)

/-- `|a - b|_∞ = |b - a|_∞`. -/
private theorem cltGood_zdistInf_comm {d L : ℕ} [NeZero L] (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub b a]
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

/-- **Item 4 over the carrier.**  Under `HCltOf`, for every `c > 0`, the entries of `G_s(±)` with
`c (log W)^3 ℓ_s ≤ |[x] - [y]|_∞` are `≤ W^{-D'}` outside an event of probability `≤ N^{-D}`, eventually:
`stFarEntryAtLoggL` at `(c, D' + 1)` and `N^𝔠 ≤ W`; the charge `-` is the transpose (`G(-) = G(+)ᴴ`). -/
theorem cltFarEntry_whpOf (d : ℕ) : CltFarEntryWhpOf d := by
  intro κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t h c hc D' hD' D hD
  obtain ⟨hd, hκ, hκ1, hδ, hadm, hκm, hs, hst, ht1, hrange, hRep, hWard, hMf, hLoc, hDec, hGij, hK⟩ := h
  have hF := RBM.BA.stFarEntryAtLoggL C μ hd hadm hδ hRep hWard hs (fun n => le_rfl) (fun n => (hst n).le)
    ht1 hrange hLoc hDec hGij hK hMf
  obtain ⟨hμ, hHerm, hGL⟩ := hRep
  subst hμ
  obtain ⟨h𝔠, h𝔡, hN, hBW, hWO⟩ := id hadm
  have hP := hF c hc (D' + 1) (by linarith) 𝔠 h𝔠 D hD
  filter_upwards [hP, hBW] with n hn hWn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  let T : Set (Ω d (sz.L n) (sz.W n)) := ⋃ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
    {ω | N ^ 𝔠 * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) <
      ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
          (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) true p.1 p.2‖ *
        (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
            ((zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2) : ℕ) : ℝ) then 1 else 0)}
  have hTmeas : MeasurableSet T := by
    refine MeasurableSet.iUnion fun p => ?_
    exact measurableSet_lt measurable_const
      ((cltGood_gEntryOf_meas (C.m n) (E n) (s n) (s n) (H₀ n) true p.1 p.2).norm.mul measurable_const)
  have hsub : {ω : Ω d (sz.L n) (sz.W n) | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
      c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
          ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
            (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
        ((sz.W n : ℕ) : ℝ) ^ (-D') <
          ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
            (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) σ x y‖} ⊆ T := by
    rintro ω ⟨σ, x, y, hf, hg⟩
    have hHω : (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω).IsHermitian :=
      (hHerm n).add (Hflow_isHermitian d (sz.L n) (sz.W n) (s n) ω)
    have key : ∀ x y : Idx d (sz.L n) (sz.W n),
        c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
          ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) →
        ((sz.W n : ℕ) : ℝ) ^ (-D') <
          ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
            (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) true x y‖ →
        ω ∈ T := by
      intro x y hf' hg'
      refine Set.mem_iUnion.2 ⟨(x, y), ?_⟩
      change N ^ 𝔠 * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) <
        ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
            (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) true x y‖ *
          (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
              ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) then 1 else 0)
      simp only [hf', ↓reduceIte, mul_one]
      calc N ^ 𝔠 * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1))
          ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) :=
            mul_le_mul_of_nonneg_right hWn (Real.rpow_nonneg hW0.le _)
        _ = ((sz.W n : ℕ) : ℝ) ^ (-D') := by
            calc ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1))
                = ((sz.W n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := by
                  rw [Real.rpow_one]
              _ = ((sz.W n : ℕ) : ℝ) ^ (1 + (-(D' + 1))) := (Real.rpow_add hW0 _ _).symm
              _ = _ := by congr 1; ring
        _ < _ := hg'
    cases σ
    · rw [cltGood_norm_gEntryOf_false (C.m n) (E n) (s n) hHω] at hg
      exact key y x (by rw [cltGood_zdistInf_comm]; exact hf) hg
    · exact key x y hf hg
  calc PF d (sz.L n) (sz.W n) (g' n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
            ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
              (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
          ((sz.W n : ℕ) : ℝ) ^ (-D') <
            ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
              (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) σ x y‖}
      ≤ PF d (sz.L n) (sz.W n) (g' n) T := measure_mono hsub
    _ ≤ ENNReal.ofReal (N ^ (-D)) :=
        cltGood_P_le_of_seqP (sz.withLam g') n hTmeas
          ((measure_mono fun ω hω => by
            obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
            refine ⟨p, ?_⟩
            have e := (hGL n (s n) ω).1 p.1 p.2
            change N ^ 𝔠 * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) <
              ‖C.G n (s n) ω p.1 p.2‖ *
                (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
                    ((zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2) : ℕ) : ℝ) then 1 else 0)
            rw [e]
            exact hp).trans hn)

/-- **Item 5 over the carrier.**  Under `HCltOf`, `cltGoodAtOf` holds outside an event of probability `≤ N^{-D}`, at every far
threshold `θ n ≥ c (log W)^3 ℓ_s`: the union of the events of items 3 and 4 at `D + 1`, `2 N^{-(D+1)} ≤ N^{-D}` once `N ≥ 2`. -/
theorem cltGood_whpOf (d : ℕ) : CltGoodWhpOf d := by
  intro κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t h c θ hc hθ D' hD' D hD
  have h3 := cltGmax_whpOf d κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t h (D + 1) (by linarith)
  have h4 := cltFarEntry_whpOf d κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t h c hc D' hD' (D + 1) (by linarith)
  have hsize : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz h.2.2.2.2.1.2.2.1
  unfold CltGmaxConclOf at h3
  unfold CltFarEntryConclOf at h4
  unfold CltGoodConclOf
  filter_upwards [h3, h4, hsize.eventually_ge_atTop 2] with n h3n h4n hN2
  have hN2' : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hp : (0 : ℝ) ≤ N ^ (-(D + 1)) := Real.rpow_nonneg hNpos.le _
  have h22 : 2 * N ^ (-(D + 1)) ≤ N ^ (-D) := by
    have e : N ^ (-(D + 1)) = N ^ (-D) * N⁻¹ := by
      rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
    rw [e]
    have hD0 : 0 ≤ N ^ (-D) := Real.rpow_nonneg hNpos.le _
    have h2N : 2 * N⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hNpos]; exact hN2'
    nlinarith
  have hsub : {ω : Ω d (sz.L n) (sz.W n) |
      ¬ cltGoodAtOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n) (θ n) D' (H₀ n) ω} ⊆
      {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        2 < ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
          (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) σ x y‖} ∪
      {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
            ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
              (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
          ((sz.W n : ℕ) : ℝ) ^ (-D') <
            ‖gEntryOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n)
              (H₀ n + Hflow d (sz.L n) (sz.W n) (s n) ω) σ x y‖} := by
    intro ω hω
    by_contra hno
    apply hω
    refine ⟨fun σ x y => ?_, fun σ x y hθ' => ?_⟩
    · by_contra hlt
      push Not at hlt
      exact hno (Or.inl ⟨σ, x, y, hlt⟩)
    · by_contra hlt
      push Not at hlt
      exact hno (Or.inr ⟨σ, x, y, (hθ n).trans hθ', hlt⟩)
  calc PF d (sz.L n) (sz.W n) (g' n)
        {ω | ¬ cltGoodAtOf d (sz.L n) (sz.W n) (C.m n) (E n) (s n) (θ n) D' (H₀ n) ω}
      ≤ PF d (sz.L n) (sz.W n) (g' n) _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (N ^ (-(D + 1))) + ENNReal.ofReal (N ^ (-(D + 1))) := add_le_add h3n h4n
    _ = ENNReal.ofReal (2 * N ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal h22

end RBM.Evol

end
