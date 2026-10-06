/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpDuhamel

/-!
# S6-12b (T2233): the integrated estimate of regime (ii) of Step 6

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:136-147` (the identity `(iisuwjyys_exp)`
`6:142-146` and its estimate `6:147`), `paper/tex/3_5_Loop_Hierarchy.tex:1666-1671`
(`lem:sum_decay_nonzero`, `(sum_res_Ndecay_nonzero)`), `6:56-62` (`(eq:Exp(L-K)1)`), `6:83-88`
(`(eq:ExpLWn=2)`), `paper/tex/1_2_Intro_model_result.tex:1390-1396` (`(Eq:Gtlp_exp_flow)`).

This file proves the merged pin `STExpIntII` (`Step6Pins.lean:441`, text unchanged): in regime (ii)
`ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`, given the Duhamel identity `STExpDuhEq` and the drift
bounds `STExpDriftHiConcl`, `Q^{(A)} f_u = Q^{(A)} 𝒰_{s,u} f_s + ∫_s^u Q^{(A)} 𝒰_{v,u} D_v dv`
(`A = {1,2}` for `σ₁ ≠ σ₂`, `A = ∅` for `σ₁ = σ₂`) is `≺ F + T_u` for every deterministic control
`F` of the initial term.  The route (all inputs merged, no hypothesis added):
* `expIntII_log_ratio`: `∫_s^u (1-v)⁻¹ dv = log((1-s)/(1-u)) ≤ (d-2) log L`
  (`1-s ≤ g²/L²`, `1-u ≥ g²/L^d`);
* `expIntII_Bctl_le`, `expIntII_rates_le_target`: `W^{-d}B_{u,0} ≤ 2 (ilambda² W^d)⁻¹` and
  `B^{11/5} + B^{5/2} ≤ 2·2^{1/5} T_u ≤ 3 T_u`, `T_u = B²((ilambda² W^d)^{-1/5} + B)`;
* `expIntII_drift_integral_le`: at one size, a kernel bound `M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})`
  gives the drift integral `≤ M · 3 T_u · (d-2) log L` (`norm_integral_le_of_norm_le`, no
  integrability of the integrand);
* `expIntII_log_eventually`: `log L ≺ 1`;
* `expIntII_kernel_unif`: `(sum_res_Ndecay_nonzero)` (the merged `stek_nonzero_holds`, no loss)
  applied to the deterministic drift tensors `D_v` at `t ↦ u`, then lifted over the time sequence
  `u` (the failing-sequence argument of `st6_precU_of_forall_seq`, `Step6Kit.lean:115`, for a
  deterministic property with the second time `v ≤ u`: both sides are deterministic,
  `st6_prec_det_iff`);
* `STExpIntConcl_of_kernel`, `STExpIntIIConcl_of_flow`, `stExpIntII_holds`: the assembly and
  the pin.

`(normQA2)` is not needed (the kernel estimate bounds `Q^{(A)} 𝒰` directly) and `σ₁ = σ₂` is the
same argument with `A = ∅` (`I_diff = ∅`, `T2191a`).  Compiled nonempty instances at `d = 3`,
`szB`, `zB`, regime (ii) times `(15/16, 31/32)` are in the last section (namespace
`RBM.Gauss.Step6Inst`).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. The `u`-integral -/

/-- `∫_s^u (1-v)⁻¹ dv = log((1-s)/(1-u))` for `s ≤ u < 1` (substitution `v ↦ 1 - v`, `integral_inv`). -/
private theorem expIntII_integral_inv_one_sub {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) :
    ∫ v in s..u, (1 - v)⁻¹ = Real.log ((1 - s) / (1 - u)) := by
  have h := intervalIntegral.integral_comp_sub_left (a := s) (b := u) (fun x : ℝ => x⁻¹) 1
  rw [h]
  apply integral_inv
  rw [Set.uIcc_of_le (by linarith)]
  intro hmem
  have := hmem.1
  linarith

/-- **The `u`-integral of regime (ii)** (`6:146`). -/
theorem expIntII_log_ratio {d L : ℕ} {g s u : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ L) (hsu : s ≤ u) (hu : u < 1)
    (h1 : 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2) (h2 : g ^ 2 / (L : ℝ) ^ d ≤ 1 - u) :
    ∫ v in s..u, (1 - v)⁻¹ ≤ ((d : ℝ) - 2) * Real.log (L : ℝ) := by
  rw [expIntII_integral_inv_one_sub hsu hu]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hx : 0 < 1 - u := by linarith
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  have hg2 : 0 < g ^ 2 := by
    have : 0 < g ^ 2 / (L : ℝ) ^ 2 := by linarith
    have h0 : 0 < (L : ℝ) ^ 2 := by positivity
    exact (div_pos_iff_of_pos_right h0).1 this
  have hxs : 0 < 1 - s := by linarith
  have hratio : (1 - s) / (1 - u) ≤ (L : ℝ) ^ e := by
    rw [div_le_iff₀ hx]
    have h3 : g ^ 2 / (L : ℝ) ^ (e + 2) ≤ 1 - u := h2
    have h4 : g ^ 2 / (L : ℝ) ^ 2 = (L : ℝ) ^ e * (g ^ 2 / (L : ℝ) ^ (e + 2)) := by
      rw [pow_add]; field_simp
    calc 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 := h1
      _ = (L : ℝ) ^ e * (g ^ 2 / (L : ℝ) ^ (e + 2)) := h4
      _ ≤ (L : ℝ) ^ e * (1 - u) := by gcongr
  have hpos : 0 < (1 - s) / (1 - u) := div_pos hxs hx
  calc Real.log ((1 - s) / (1 - u)) ≤ Real.log ((L : ℝ) ^ e) := Real.log_le_log hpos hratio
    _ = (e : ℝ) * Real.log (L : ℝ) := Real.log_pow (L : ℝ) e
    _ = (((e + 2 : ℕ) : ℝ) - 2) * Real.log (L : ℝ) := by push_cast; ring


/-! ## 2. The control `B ≤ 2 (ilambda² W^d)⁻¹` and the rates against the target -/

section Rates

variable {d : ℕ} (sz : Sizes d)

/-- **The window `1-u ≥ ilambda²/L^d`**: `W^{-d}B_{u,0} = W^{-d}((ilambda² + 1-u)⁻¹ + (L^d(1-u))⁻¹) ≤ 2 (ilambda² W^d)⁻¹`
(`λ ≠ 0`). -/
theorem expIntII_Bctl_le (n : ℕ) {u : ℝ} (hu : u < 1) (hl : sz.lam n ≠ 0)
    (hw : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u) :
    sz.Bctl n u ≤ 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  rw [st6_Bctl_eq sz n hu]
  have hx : 0 < 1 - u := by linarith
  have hlam : 0 < sz.lam n ^ 2 := by positivity
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hNeq : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hw' : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) := by
    have := (div_le_iff₀ hLd).1 hw
    linarith
  have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤
      (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    have h : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hlam (by linarith)
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ := by gcongr
      _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_comm, mul_inv]
  have h2 : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [hNeq]
    apply inv_anti₀ (by positivity)
    calc sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d = ((sz.W n : ℕ) : ℝ) ^ d * sz.lam n ^ 2 := by ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u)) := by gcongr
      _ = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) := by ring
  linarith

/-- `2^{1/5} ≤ 3/2` (`(3/2)^5 = 243/32 ≥ 2`). -/
private theorem expIntII_two_rpow_le : (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 3 / 2 := by
  have h5 : ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ 5 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  by_contra h
  push Not at h
  have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)
  rw [h5] at this
  norm_num at this

/-- `B^{1/2} ≤ B^{1/5} + B` (`B ≤ 1`: `B^{1/2} ≤ B^{1/5}`; `B > 1`: `B^{1/2} ≤ B`). -/
private theorem expIntII_sqrt_le {B : ℝ} (hB : 0 < B) : B ^ (1 / 2 : ℝ) ≤ B ^ (1 / 5 : ℝ) + B := by
  rcases le_or_gt B 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hB h (by norm_num : (1 / 5 : ℝ) ≤ 1 / 2)
    linarith
  · have h1 : B ^ (1 / 2 : ℝ) ≤ B ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
    have h2 : 0 ≤ B ^ (1 / 5 : ℝ) := Real.rpow_nonneg hB.le _
    rw [Real.rpow_one] at h1
    linarith

/-- **The drift rates against the target** (`(eq:Exp(L-K)1)`, `(eq:ExpLWn=2)` against `(Eq:Gtlp_exp_flow)`):
`B^{11/5} + B^{5/2} ≤ 2·2^{1/5} B²((ilambda²W^d)^{-1/5} + B) ≤ 3 T_u` for `1-u ≥ ilambda²/L^d`. -/
theorem expIntII_rates_le_target (n : ℕ) {u : ℝ} (hu : u < 1) (hl : sz.lam n ≠ 0)
    (hw : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u) :
    sz.Bctl n u ^ (11 / 5 : ℝ) + sz.Bctl n u ^ (5 / 2 : ℝ) ≤ 3 * STExpTarget sz n u := by
  have hB0 : 0 < sz.Bctl n u := STBctl_pos sz n hu
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hA0 : 0 < sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hBle := expIntII_Bctl_le sz n hu hl hw
  unfold STExpTarget
  generalize sz.Bctl n u = B at hB0 hBle ⊢
  generalize sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d = A at hA0 hBle ⊢
  have hG0 : 0 ≤ A ^ (-(1 / 5 : ℝ)) := Real.rpow_nonneg hA0.le _
  have h15 : B ^ (1 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 5 : ℝ) * A ^ (-(1 / 5 : ℝ)) := by
    calc B ^ (1 / 5 : ℝ) ≤ (2 * A⁻¹) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hB0.le hBle (by norm_num)
      _ = (2 : ℝ) ^ (1 / 5 : ℝ) * (A⁻¹) ^ (1 / 5 : ℝ) := Real.mul_rpow (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ (1 / 5 : ℝ) * A ^ (-(1 / 5 : ℝ)) := by
          rw [Real.inv_rpow hA0.le, Real.rpow_neg hA0.le]
  have e1 : B ^ (11 / 5 : ℝ) = B ^ 2 * B ^ (1 / 5 : ℝ) := by
    rw [show (11 / 5 : ℝ) = ((2 : ℕ) : ℝ) + 1 / 5 by norm_num, Real.rpow_add hB0, Real.rpow_natCast]
  have e2 : B ^ (5 / 2 : ℝ) = B ^ 2 * B ^ (1 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hB0, Real.rpow_natCast]
  have hc := expIntII_two_rpow_le
  have hsq := expIntII_sqrt_le hB0
  have hB2 : 0 ≤ B ^ 2 := by positivity
  rw [e1, e2]
  have h3 : B ^ (1 / 5 : ℝ) + B ^ (1 / 2 : ℝ) ≤ 3 * (A ^ (-(1 / 5 : ℝ)) + B) := by
    have h4 : (2 : ℝ) ^ (1 / 5 : ℝ) * A ^ (-(1 / 5 : ℝ)) ≤ 3 / 2 * A ^ (-(1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_right hc hG0
    nlinarith
  calc B ^ 2 * B ^ (1 / 5 : ℝ) + B ^ 2 * B ^ (1 / 2 : ℝ) = B ^ 2 * (B ^ (1 / 5 : ℝ) + B ^ (1 / 2 : ℝ)) := by ring
    _ ≤ B ^ 2 * (3 * (A ^ (-(1 / 5 : ℝ)) + B)) := mul_le_mul_of_nonneg_left h3 hB2
    _ = 3 * (B ^ 2 * (A ^ (-(1 / 5 : ℝ)) + B)) := by ring

end Rates

/-! ## 3. One size: the drift integral -/

section OneSize

variable {d : ℕ} (sz : Sizes d)

/-- **The drift integral at one size** (`6:146`): a kernel bound `‖Q^{(A)} 𝒰_{v,u} D_v‖_∞ ≤ M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` on
`[s,u]` gives `‖∫_s^u Q^{(A)} 𝒰_{v,u} D_v dv‖ ≤ M · 3 T_u · (d-2) log L` (`B_v ≤ B_u`, `∫ (1-v)⁻¹ ≤ (d-2) log L`; the integrability
of the integrand is not needed: `intervalIntegral.norm_integral_le_of_norm_le`). -/
theorem expIntII_drift_integral_le (n : ℕ) {E s u M : ℝ} (hd : 2 ≤ d) (hM : 0 ≤ M) (hsu : s ≤ u) (hu : u < 1)
    (hwin : 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u)
    (σ : Fin 2 → Bool) (A : Finset (Fin 2))
    (hker : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖RBM.zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b))‖ ≤
        M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖∫ v in s..u, RBM.zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b)) a‖ ≤
      M * (3 * STExpTarget sz n u * (((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ))) := by
  have hx : 0 < 1 - u := by linarith
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  -- `ilambda ≠ 0`: `0 < 1 - u ≤ 1 - s ≤ ilambda²/L²`
  have hl : sz.lam n ≠ 0 := by
    intro h0
    rw [h0] at hwin
    norm_num at hwin
    linarith
  have hT0 : 0 ≤ STExpTarget sz n u := st6_target_nonneg sz n hu
  have hrate := expIntII_rates_le_target sz n hu hl hlo
  have hlogL : 0 ≤ ((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL1
    exact mul_nonneg (by linarith) (Real.log_nonneg h1)
  -- the bound `g v = M (3 T_u) (1-v)⁻¹`
  have hbound : ∀ v : ℝ, s ≤ v → v ≤ u →
      M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) ≤
        (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹ := by
    intro v hv1 hv2
    have hvu : v < 1 := lt_of_le_of_lt hv2 hu
    have hmono := STBctl_mono sz n hv2 hu
    have hBv := (STBctl_pos sz n hvu).le
    have h1 : sz.Bctl n v ^ (11 / 5 : ℝ) ≤ sz.Bctl n u ^ (11 / 5 : ℝ) :=
      Real.rpow_le_rpow hBv hmono (by norm_num)
    have h2 : sz.Bctl n v ^ (5 / 2 : ℝ) ≤ sz.Bctl n u ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow hBv hmono (by norm_num)
    have hinv : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
    calc M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))
        ≤ M * ((1 - v)⁻¹ * (3 * STExpTarget sz n u)) := by
          gcongr
          linarith
      _ = (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹ := by ring
  have hint : IntervalIntegrable (fun v : ℝ => (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹) volume s u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
    intro v hv
    rw [Set.uIcc_of_le hsu] at hv
    have : v ≤ u := hv.2
    change 1 - v ≠ 0
    linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun v => RBM.zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b)) a)
    (g := fun v : ℝ => (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹) hsu
    (Filter.Eventually.of_forall fun v hv =>
      ((norm_le_pi_norm _ a).trans (hker v hv.1.le hv.2)).trans (hbound v hv.1.le hv.2)) hint
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hlog := expIntII_log_ratio (d := d) (L := sz.L n) (g := sz.lam n) hd hL1 hsu hu hwin hlo
  calc M * (3 * STExpTarget sz n u) * ∫ v in s..u, (1 - v)⁻¹
      ≤ M * (3 * STExpTarget sz n u) * (((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = M * (3 * STExpTarget sz n u * (((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ))) := by ring

end OneSize

/-! ## 4. `log L ≺ 1` -/

section LogL

variable {d : ℕ} (sz : Sizes d)

/-- **`log L ≺ 1`**: for every `C` and `τ > 0`, eventually `C log L_n ≤ N^τ` (`L ≤ N`, `log N ≤ N^{τ/2}/(τ/2)`, `N → ∞`). -/
theorem expIntII_log_eventually (hsz : sz.SizeTendsto) (hd : 1 ≤ d) (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, C * Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hK : ∀ᶠ n in atTop, 2 * |C| / τ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop _
  filter_upwards [hK] with n hn
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hLN : ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have h1 : sz.L n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_left _ (sz.W_pos n)
    have h2 : sz.W n * sz.L n ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
    exact_mod_cast h1.trans h2
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hlog0 : 0 ≤ Real.log ((sz.L n : ℕ) : ℝ) := Real.log_nonneg hL1
  have hlogN : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) / (τ / 2) :=
    (Real.log_le_log (by linarith) hLN).trans (Real.log_le_rpow_div hN0.le hτ2)
  have hP : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  calc C * Real.log ((sz.L n : ℕ) : ℝ) ≤ |C| * Real.log ((sz.L n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
    _ ≤ |C| * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) / (τ / 2)) := by gcongr
    _ = (2 * |C| / τ) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
        mul_le_mul_of_nonneg_right hn hP
    _ = ((sz.size n : ℕ) : ℝ) ^ τ := hrpow.symm

end LogL

/-! ## 5. The uniform kernel bound: `(sum_res_Ndecay_nonzero)` applied to the deterministic drift tensors -/

section Kernel

variable {d : ℕ} (sz : Sizes d)

/-- `Ugen` at the energy `E` is the merged `UN` with the signs `EKsgn (mE E) σ` (as in `st6_ini_nonzero`). -/
private theorem expIntII_Ugen_eq (n : ℕ) (E : ℝ) (σ : Fin 2 → Bool) (v w : ℝ) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) :
    RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v w A = UN d (sz.L n) (sz.lam n) (EKsgn (mE E) σ) v w A := rfl

/-- **`(eq:Exp(L-K)1)` + `(eq:ExpLWn=2)` for the drift tensor** (premise `STExpDriftHiConcl`): `‖D_v^σ‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})`
for all large `n`, all `v ∈ [s_n, t_n]` and `σ` (`st6_prec_det_iff` for the two summands, the triangle inequality). -/
private theorem expIntII_drift_pi (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STExpDriftHiConcl sz E s t) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (v : TimeIcc s t n) (σ : Fin 2 → Bool),
      ‖fun b => STExpDrift sz n (E n) (v : ℝ) σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by
  have h1 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))).1 h.1 τ hτ
  have h2 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))).1 h.2 τ hτ
  filter_upwards [h1, h2] with n hn1 hn2
  intro v σ
  have hv1 : (v : ℝ) < 1 := lt_of_le_of_lt v.2.2 (ht1 n)
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hB0 := (STBctl_pos sz n hv1).le
  have hinv : 0 ≤ (1 - (v : ℝ))⁻¹ := inv_nonneg.2 (by linarith)
  have hX : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) :=
    mul_nonneg hN0 (mul_nonneg hinv (add_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hB0 _)))
  rw [pi_norm_le_iff_of_nonneg hX]
  intro a
  calc ‖STExpDrift sz n (E n) (v : ℝ) σ a‖
      = ‖STExpELKLK sz n (E n) (v : ℝ) σ a + STExpEGt sz n (E n) (v : ℝ) σ a‖ := rfl
    _ ≤ ‖STExpELKLK sz n (E n) (v : ℝ) σ a‖ + ‖STExpEGt sz n (E n) (v : ℝ) σ a‖ := norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (v : ℝ))⁻¹ * sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ)) +
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (v : ℝ))⁻¹ * sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)) :=
        add_le_add (hn1 (v, σ, a)) (hn2 (v, σ, a))
    _ = ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by ring

/-- **(g) with a second time `v ≤ u`**: if for every time sequence `u ∈ [s,t]` a property `Φ n (u n) v` holds eventually for all
`v ∈ [s_n, u_n]`, then eventually it holds for all `u ∈ [s_n,t_n]` and `v ∈ [s_n, u]` (a failing `(n, u_n, v_n)` for infinitely
many `n` is a time sequence: the argument of `st6_precU_of_forall_seq`, for a deterministic property). -/
private theorem expIntII_lift {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (Φ : ℕ → ℝ → ℝ → Prop)
    (h : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → Φ n (u n) v) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) → Φ n (u : ℝ) v := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  let u : ℕ → ℝ := fun n =>
    if hn : ∃ q : TimeIcc s t n × ℝ, s n ≤ q.2 ∧ q.2 ≤ (q.1 : ℝ) ∧ ¬ Φ n (q.1 : ℝ) q.2
    then ((Classical.choose hn).1 : ℝ) else s n
  have hu1 : ∀ n, s n ≤ u n := by
    intro n
    by_cases hn : ∃ q : TimeIcc s t n × ℝ, s n ≤ q.2 ∧ q.2 ≤ (q.1 : ℝ) ∧ ¬ Φ n (q.1 : ℝ) q.2
    · simp only [u, hn, ↓reduceDIte]; exact (Classical.choose hn).1.2.1
    · simp only [u, hn, ↓reduceDIte]; exact le_rfl
  have hu2 : ∀ n, u n ≤ t n := by
    intro n
    by_cases hn : ∃ q : TimeIcc s t n × ℝ, s n ≤ q.2 ∧ q.2 ≤ (q.1 : ℝ) ∧ ¬ Φ n (q.1 : ℝ) q.2
    · simp only [u, hn, ↓reduceDIte]; exact (Classical.choose hn).1.2.2
    · simp only [u, hn, ↓reduceDIte]; exact hst n
  have h' := h u hu1 hu2
  obtain ⟨n, hn1, hn2⟩ := (hcon.and_eventually h').exists
  push Not at hn1
  obtain ⟨w, v, hv1, hv2, hv3⟩ := hn1
  have hex : ∃ q : TimeIcc s t n × ℝ, s n ≤ q.2 ∧ q.2 ≤ (q.1 : ℝ) ∧ ¬ Φ n (q.1 : ℝ) q.2 :=
    ⟨(w, v), hv1, hv2, hv3⟩
  have hun : u n = ((Classical.choose hex).1 : ℝ) := by simp only [u, hex, ↓reduceDIte]
  obtain ⟨c1, c2, c3⟩ := Classical.choose_spec hex
  have := hn2 (Classical.choose hex).2 c1 (by rw [hun]; exact c2)
  rw [hun] at this
  exact c3 this

/-- **`(sum_res_Ndecay_nonzero)` applied to the deterministic drift tensors, uniformly in `s_n ≤ v ≤ u ≤ t_n`**
(`6:144-146`): `‖Q^{(A)} 𝒰_{v,u} D_v^σ‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` for `σ` in a class with `A ⊇ I_diff(σ)`, from the
drift bounds `(eq:Exp(L-K)1)`, `(eq:ExpLWn=2)` (`STExpDriftHiConcl`), no loss: for every time sequence `u` the merged
`stek_nonzero_holds` at `t ↦ u`, then `expIntII_lift` over `u`. -/
theorem expIntII_kernel_unif (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n)
    (hdr : STExpDriftHiConcl sz (STflowE z) s t) (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop)
    (hA : ∀ σ, P σ → ∀ i, σ i ≠ σ (finRotate 2 i) → i ∈ A) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖RBM.zeroModeSet d (sz.L n) A
            (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u : ℝ)
              (fun b => STExpDrift sz n (STflowE z n) v σ b))‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hκ' : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  refine expIntII_lift (fun n => (hst n).le)
    (fun n u v => ∀ σ : Fin 2 → Bool, P σ →
      ‖RBM.zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v u
            (fun b => STExpDrift sz n (STflowE z n) v σ b))‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hX : ∀ n (v : TimeIcc s u n) (_ : sz.SeqΩ), 0 ≤ (1 - (v : ℝ))⁻¹ *
      (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)) := by
    intro n v _
    have hv1 : (v : ℝ) < 1 := lt_of_le_of_lt v.2.2 (hu1 n)
    have hB0 := (STBctl_pos sz n hv1).le
    exact mul_nonneg (inv_nonneg.2 (by linarith))
      (add_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hB0 _))
  have key : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, P σ → ∀ v : TimeIcc s u n,
      ‖RBM.zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ (v : ℝ) (u n)
            (fun b => STExpDrift sz n (STflowE z n) (v : ℝ) σ b))‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by
    intro σ
    by_cases hP : P σ
    · have hdom : sz.Prec (U := fun n => TimeIcc s u n)
          (fun n v _ => ‖fun b => STExpDrift sz n (STflowE z n) (v : ℝ) σ b‖)
          (fun n v _ => (1 - (v : ℝ))⁻¹ *
            (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by
        refine (st6_prec_det_iff sz hsz (V := fun n => TimeIcc s u n)
          (fun n v => ‖fun b => STExpDrift sz n (STflowE z n) (v : ℝ) σ b‖)
          (fun n v => (1 - (v : ℝ))⁻¹ *
            (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)))).2 ?_
        intro τ' hτ'
        filter_upwards [expIntII_drift_pi sz hsz ht1 hdr hτ'] with n hn v
        exact hn ⟨(v : ℝ), v.2.1, v.2.2.trans (hut n)⟩ σ
      have hk := stek_nonzero_holds d hd 2 le_rfl (Real.sqrt (2 * κ) / 2) 𝔠 𝔡 hκ' sz hflow.1 s u hsg hs0 hsu hu1
        (fun n => mE (STflowE z n)) (fun n => norm_mE (st6_flowE_lt_two sz hκ hflow n).le)
        (fun n => st6_mE_im_ge hκ (st6_flowE_le sz hflow n)) σ A (hA σ hP)
        (fun n v _ => fun b => STExpDrift sz n (STflowE z n) (v : ℝ) σ b)
        (fun n v _ => (1 - (v : ℝ))⁻¹ *
          (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) hX hdom
      have hk' := ((st6_prec_det_iff sz hsz (V := fun n => TimeIcc s u n)
        (fun n v => ‖RBM.zeroModeSet d (sz.L n) A (UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ) (v : ℝ) (u n)
          (fun b => STExpDrift sz n (STflowE z n) (v : ℝ) σ b))‖)
        (fun n v => (1 - (v : ℝ))⁻¹ *
          (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)))).1 hk) τ hτ
      filter_upwards [hk'] with n hn _ v
      rw [expIntII_Ugen_eq sz n (STflowE z n) σ (v : ℝ) (u n)]
      exact hn v
    · exact Filter.Eventually.of_forall fun n h => absurd h hP
  filter_upwards [Filter.eventually_all.2 key] with n hn v hv1 hv2 σ hP
  exact hn σ hP ⟨v, hv1, hv2⟩

end Kernel

/-! ## 6. The integrated estimate and the pin -/

section Assembly

variable {d : ℕ} (sz : Sizes d)

/-- **`(iisuwjyys_exp)` closed** (`6:142-146`), regime (ii) (any `A`, `P`): the Duhamel identity (`STExpDuhEq` at `A`), the uniform kernel
bound `‖Q^{(A)} 𝒰_{v,u} D_v‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})`, the one-size integral bound (`M = N^{τ/2}`) and `log L ≺ 1`
give `‖Q^{(A)} f_u‖ ≤ N^τ F + N^τ T_u` for the control `F` of the initial term. -/
theorem STExpIntConcl_of_kernel (hsz : sz.SizeTendsto) (hd : 2 ≤ d) {E s t : ℕ → ℝ}
    (_hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5II sz s t) (hduh : STExpDuhEq sz E s t)
    (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop)
    (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖RBM.zeroModeSet d (sz.L n) A
            (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b))‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) :
    STExpIntConcl sz A P E s t := by
  intro F hF hini
  have hini' := ((st6_prec_det_iff sz hsz (V := STIdx2P sz P s t)
    (fun n p => ‖zeroModeSet d (sz.L n) A
      (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
    (fun n p => F n p)).1 hini)
  refine (st6_prec_det_iff sz hsz (V := STIdx2P sz P s t)
    (fun n p => ‖zeroModeSet d (sz.L n) A (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
    (fun n p => F n p + STExpTarget sz n (p.1 : ℝ))).2 ?_
  intro τ hτ
  have h3 := expIntII_log_eventually sz hsz (by omega) (3 * ((d : ℝ) - 2)) (half_pos hτ)
  filter_upwards [hini' τ hτ, hker (τ / 2) (half_pos hτ), h3] with n hn1 hn2 hn3
  rintro ⟨u, ⟨σ, hP⟩, a⟩
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
  have hwin := (hR n).2
  have hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - (u : ℝ) := by
    have := (hR n).1
    have h2 : (u : ℝ) ≤ t n := u.2.2
    linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hP0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  have hint := expIntII_drift_integral_le sz n (E := E n) (s := s n) (u := (u : ℝ))
    (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) hd hP0 u.2.1 hu1 hwin hlo σ A
    (fun v hv1 hv2 => hn2 u v hv1 hv2 σ hP) a
  have hT0 : 0 ≤ STExpTarget sz n (u : ℝ) := st6_target_nonneg sz n hu1
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  change ‖zeroModeSet d (sz.L n) A (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (F n (u, ⟨σ, hP⟩, a) + STExpTarget sz n (u : ℝ))
  rw [hduh n u σ A a]
  refine (norm_add_le _ _).trans ?_
  have hn1' := hn1 (u, ⟨σ, hP⟩, a)
  have hlog : 3 * ((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := hn3
  calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          (3 * STExpTarget sz n (u : ℝ) * (((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ))) :=
        add_le_add hn1' hint
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) *
          (3 * ((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ))) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) := by
        gcongr
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (F n (u, ⟨σ, hP⟩, a) + STExpTarget sz n (u : ℝ)) := by
        rw [hrpow]; ring

/-- **The conclusion of the pin from the flow data alone** (no stochastic premise of `STIngR6` is used): `A = {1,2}` for `σ₁ ≠ σ₂`;
`A = ∅` for `σ₁ = σ₂` (`I_diff = ∅`, `st6_Idiff_same`; not `(sum_res_2_NAL)`, `T2191a`). -/
theorem STExpIntIIConcl_of_flow (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5II sz s t) (hduh : STExpDuhEq sz (STflowE z) s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t) :
    STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed (STflowE z) s t ∧
      STExpIntConcl sz ∅ STSigSame (STflowE z) s t := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n := fun n => by linarith [(hR n).2]
  refine ⟨STExpIntConcl_of_kernel sz hsz (by omega) hst ht1 hR hduh _ _ fun τ hτ => ?_,
    STExpIntConcl_of_kernel sz hsz (by omega) hst ht1 hR hduh _ _ fun τ hτ => ?_⟩
  · exact expIntII_kernel_unif sz hd hκ hflow hs0 hst htT hsg hdr _ _ (fun σ _ i _ => Finset.mem_univ i) τ hτ
  · exact expIntII_kernel_unif sz hd hκ hflow hs0 hst htT hsg hdr _ _
      (fun σ hσ i hi => absurd hi (st6_Idiff_same hσ i)) τ hτ

end Assembly

/-- **The pin `STExpIntII`** (`Step6Pins.lean:441`, text unchanged), every `d`: the constant `𝔠_d = 1/100`; the proof uses only the flow data
(`SizeTendsto`, `|E_n| ≤ 2 - κ`, `t ≤ lemT z`), `0 ≤ s < t`, the regime, and the two conclusion premises `STExpDuhEq`,
`STExpDriftHiConcl`; the stochastic premises of `STIngR6` (`STLK`, `STDecay`, `STExp2`, `STConStInd`, `STStep2Core`, `STLmaxU`, `STLKU`,
`STGdecayW … 0`) are not used. -/
theorem stExpIntII_holds (d : ℕ) : STExpIntII d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5 hduh hdr
  exact STExpIntIIConcl_of_flow sz hd hκ hflow hs0 hst htT hR hduh hdr

end RBM.Gauss.Sizes

/-! ## 7. Compiled nonempty instances (`d = 3`, `szB`, `zB`, regime (ii) times `(15/16, 31/32)`) -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- `stExpIntII_holds 3` at the data of regime (ii): `(szB, zB, 15/16, 31/32)`; the stochastic premises of `STIngR6` stay hypotheses of
the produced statement (other gates' pins). -/
theorem inst_expIntII_holds :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_expIntII (stExpIntII_holds 3)

/-- The regime-(ii) skeleton with the merged `stExpLKLKHi_holds`, `stImproveExpAver_holds`, `stExpDuhamelZ_holds` and the proved
`stExpIntII_holds`: only `LWtermEXP 3` (LW-14) and `STExpWardII 3` (S6-12a) stay open. -/
theorem inst_skeleton6II_Int (hLW : LWtermEXP 3) (hWd : STExpWardII 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_skeleton6II (stExpLKLKHi_holds 3) hLW (stImproveExpAver_holds 3) (stExpDuhamelZ_holds 3)
    (stExpIntII_holds 3) hWd

/-- `STExpIntIIConcl_of_flow` at `szB`, the flow `zB` (`κ = 1/10`), times `(15/16, 31/32)`: the Duhamel identity is discharged with the
merged `st6_duhEq_of_pin (stExpDuhamelZ_holds 3)`; the drift bounds `STExpDriftHiConcl` stay a hypothesis. -/
theorem inst_expIntII_concl :
    STExpDriftHiConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      STExpIntConcl szB (Finset.univ : Finset (Fin 2)) STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ∧
        STExpIntConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  STExpIntIIConcl_of_flow szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5II
    (st6_duhEq_of_pin szB (stExpDuhamelZ_holds 3) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
      (fun _ => by norm_num) (szB_flow_ht (by norm_num)))

/-- `expIntII_log_ratio` at `d = 3`, `L = 4`, `g = 1`, `(s, u) = (15/16, 31/32)`: `1 - s = 1/16 = g²/L²` is the boundary of the window,
`log 2 = 0.693 ≤ log 4 = 1.386`. -/
theorem inst_expIntII_log_ratio :
    ∫ v in (15 / 16 : ℝ)..(31 / 32), (1 - v)⁻¹ ≤ (((3 : ℕ) : ℝ) - 2) * Real.log ((szB.L 0 : ℕ) : ℝ) :=
  expIntII_log_ratio (d := 3) (L := szB.L 0) (g := szB.lam 0) (by norm_num) (by simp [szB]) (by norm_num)
    (by norm_num) (by simp [szB]; norm_num) (by simp [szB]; norm_num)

/-- `expIntII_Bctl_le` at `szB`, `n = 0`, `u = 31/32`: `B = (32/33 + 1/2)/64 = 0.0230 ≤ 2/64 = 0.03125`. -/
theorem inst_expIntII_Bctl_le :
    szB.Bctl 0 (31 / 32) ≤ 2 * (szB.lam 0 ^ 2 * ((szB.W 0 : ℕ) : ℝ) ^ 3)⁻¹ :=
  expIntII_Bctl_le szB 0 (by norm_num) (by simp [szB]) (by simp [szB]; norm_num)

/-- `expIntII_rates_le_target` at the same data: `3.28e-4 ≤ 3 · 2.42e-4`. -/
theorem inst_expIntII_rates_le_target :
    szB.Bctl 0 (31 / 32) ^ (11 / 5 : ℝ) + szB.Bctl 0 (31 / 32) ^ (5 / 2 : ℝ) ≤ 3 * STExpTarget szB 0 (31 / 32) :=
  expIntII_rates_le_target szB 0 (by norm_num) (by simp [szB]) (by simp [szB]; norm_num)

/-- `expIntII_log_eventually` at `szB` (`L = 4`, `N = (4(n+4))^3 → ∞`, from `flow_zB`), `C = 3 (d - 2) = 3`, `τ = 1/10`: eventually
`3 log 4 = 4.16 ≤ N^{1/10}`. -/
theorem inst_expIntII_log_eventually :
    ∀ᶠ n in atTop, 3 * (((3 : ℕ) : ℝ) - 2) * Real.log ((szB.L n : ℕ) : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) :=
  expIntII_log_eventually szB flow_zB.1.2.2.1 (by norm_num) _ (by norm_num)

/-- `expIntII_kernel_unif` at `szB`, `zB` (`κ = 1/10`), `(15/16, 31/32)`, `A = {1,2}`, `P = STSigMixed`: every deterministic hypothesis
(`flow_zB`, the times, the window `1 - 1/16 ≤ 15/16`, `A ⊇ I_diff(σ)`) is discharged; the drift bounds `STExpDriftHiConcl`
(`(eq:Exp(L-K)1)`, `(eq:ExpLWn=2)`: S6-06, LW-14) stay a hypothesis. -/
theorem inst_expIntII_kernel_unif
    (hdr : STExpDriftHiConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ => 31 / 32) n) (v : ℝ), 15 / 16 ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, STSigMixed σ →
        ‖RBM.zeroModeSet 3 (szB.L n) (Finset.univ : Finset (Fin 2))
            (RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) σ v (u : ℝ)
              (fun b => szB.STExpDrift n (STflowE zB n) v σ b))‖ ≤
          ((szB.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (szB.Bctl n v ^ (11 / 5 : ℝ) + szB.Bctl n v ^ (5 / 2 : ℝ))) :=
  expIntII_kernel_unif szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun n => by simp [szB]; norm_num) hdr _ STSigMixed
    (fun σ _ i _ => Finset.mem_univ i) τ hτ

/-- `expIntII_drift_integral_le` at the same data with `M = N^τ` (the kernel bound of `inst_expIntII_kernel_unif`): eventually, for every
`u ∈ [15/16, 31/32]`, `σ₁ ≠ σ₂`, `a`, the drift integral is `≤ N^τ · 3 T_u · (3-2) log 4`; the drift bounds stay a hypothesis. -/
theorem inst_expIntII_drift_integral_le
    (hdr : STExpDriftHiConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ => 31 / 32) n) (σ : Fin 2 → Bool), STSigMixed σ →
      ∀ a : Fin 2 → Zd 3 (szB.L n),
        ‖∫ v in (15 / 16 : ℝ)..(u : ℝ), RBM.zeroModeSet 3 (szB.L n) (Finset.univ : Finset (Fin 2))
            (RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) σ v (u : ℝ)
              (fun b => szB.STExpDrift n (STflowE zB n) v σ b)) a‖ ≤
          ((szB.size n : ℕ) : ℝ) ^ τ *
            (3 * STExpTarget szB n (u : ℝ) * ((((3 : ℕ) : ℝ) - 2) * Real.log ((szB.L n : ℕ) : ℝ))) := by
  filter_upwards [inst_expIntII_kernel_unif hdr τ hτ] with n hn u σ hσ a
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (by norm_num)
  exact expIntII_drift_integral_le szB n (E := STflowE zB n) (s := 15 / 16) (u := (u : ℝ))
    (M := ((szB.size n : ℕ) : ℝ) ^ τ) (by norm_num)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) u.2.1 hu1 (by simp [szB]; norm_num)
    (by have := u.2.2; simp [szB]; norm_num; linarith) σ Finset.univ
    (fun v hv1 hv2 => hn u v hv1 hv2 σ hσ) a

end RBM.Gauss.Step6Inst

end
