/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpIntII

/-!
# The integrated estimate of regime (ii) over the carrier (BA-V row V1s2', ticket T2506 row b, targets 12-13)

Additive restatement of `Induction/ExpIntII.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the one kernel `Step2Gen_UN C` and the
vocabulary and pins of `Chain/Step6Gen.lean`.  Paper: arXiv:2507.20274, `6:133-152` (the identity `(iisuwjyys_exp)` `6:142-146`, its estimate `6:147`),
`3_5:1666-1671` (`lem:sum_decay_nonzero`), `1_2:1390-1396` (`(Eq:Gtlp_exp_flow)`).

* **Target 12.**  `expIntII_drift_integral_leg` (band `expIntII_drift_integral_le`, `ExpIntII:202`): at one size the drift integral of a kernel bound
  `M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` is `≤ M · 3 T_u · (d-2) log L`.  `expIntII_kernel_unifg` (band `expIntII_kernel_unif`, `:393`) is
  `(sum_res_Ndecay_nonzero)` (`STEKNonzerogL`, the A-form) applied to the deterministic drift tensors, the window `(1-s) L² ≤ lam²` becoming
  `≤ Aof κm · gK²` by the comparison R1 (`lam² ≤ A gK²`; DECISIONS §273 (1)): R1 is read at this window and nowhere else.
  `STExpIntConclgL_of_kernel` (`:472`) and `STExpIntIIConclgL_of_flow` (`:533`) assemble the conclusions of `STExpIntIIgL`.  The size-level lemmas
  `expIntII_log_ratio`, `expIntII_Bctl_le`, `expIntII_rates_le_target`, `expIntII_log_eventually` are reused by name.
* **Target 13.**  `stExpIntIIgL_of` (`STExpIntIIgL`, `Chain/Step6Gen:368`) from the family premises (probability law, flow facts, the class `Ker` at the coupling
  `gK` with R1, `STEKNonzerogL`); the band `stExpIntII_holds` (`ExpIntII:553`) is re-derived through `STExpIntII_of_gL` (`Step6Gen:634`).

No `def`, `abbrev` or `structure` is added; helpers are `private` and prefixed `ExpIntIIGen_`.  The private lemma `expIntII_lift` of the band file is
used by `open private` (no `private` is deleted).  Ports: none from `../RBM1D`, `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private expIntII_lift from RBM3D.Induction.ExpIntII

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. One size: the drift integral (target 12) -/

section OneSize

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The drift integral at one size** (`6:146`; band `expIntII_drift_integral_le`): a kernel bound
`‖Q^{(A)} 𝒰_{v,u} D_v‖_∞ ≤ M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` on `[s,u]` gives `‖∫_s^u Q^{(A)} 𝒰_{v,u} D_v dv‖ ≤ M · 3 T_u · (d-2) log L`, the kernel
`Step2Gen_UN C` and the drift `STExpDriftg C μ` of the carrier. -/
theorem expIntII_drift_integral_leg (n : ℕ) {s u M : ℝ} (hd : 2 ≤ d) (hM : 0 ≤ M) (hsu : s ≤ u) (hu : u < 1)
    (hwin : 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u)
    (σ : Fin 2 → Bool) (A : Finset (Fin 2))
    (hker : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ v u (fun b => STExpDriftg C μ n v σ b))‖ ≤
        M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖∫ v in s..u, zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ v u (fun b => STExpDriftg C μ n v σ b)) a‖ ≤
      M * (3 * STExpTarget sz n u * (((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ))) := by
  have hx : 0 < 1 - u := by linarith
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hl : sz.lam n ≠ 0 := by
    intro h0
    rw [h0] at hwin
    norm_num at hwin
    linarith
  have hT0 : 0 ≤ STExpTarget sz n u := st6_target_nonneg sz n hu
  have hrate := expIntII_rates_le_target sz n hu hl hlo
  have hbound : ∀ v : ℝ, s ≤ v → v ≤ u →
      M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) ≤
        (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹ := by
    intro v hv1 hv2
    have hvu : v < 1 := lt_of_le_of_lt hv2 hu
    have hmono := STBctl_mono sz n hv2 hu
    have hBv := (STBctl_pos sz n hvu).le
    have h1 : sz.Bctl n v ^ (11 / 5 : ℝ) ≤ sz.Bctl n u ^ (11 / 5 : ℝ) := Real.rpow_le_rpow hBv hmono (by norm_num)
    have h2 : sz.Bctl n v ^ (5 / 2 : ℝ) ≤ sz.Bctl n u ^ (5 / 2 : ℝ) := Real.rpow_le_rpow hBv hmono (by norm_num)
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
    (f := fun v => zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ v u (fun b => STExpDriftg C μ n v σ b)) a)
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

/-! ## 2. The uniform kernel bound: `(sum_res_Ndecay_nonzero)` applied to the deterministic drift tensors (target 12) -/

section Kernel

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`(eq:Exp(L-K)1)` + `(eq:ExpLWn=2)` for the drift tensor** (premise `STExpDriftHiConclgL`): `‖D_v^σ‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` for all
large `n`, all `v ∈ [s_n, t_n]` and `σ` (band `expIntII_drift_pi`, `ExpIntII:323`). -/
private theorem ExpIntIIGen_drift_pi (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STExpDriftHiConclgL C μ s t) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (v : TimeIcc s t n) (σ : Fin 2 → Bool),
      ‖fun b => STExpDriftg C μ n (v : ℝ) σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by
  have h1 := (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpELKLKg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))).1 h.1 τ hτ
  have h2 := (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpEGtg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
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
  calc ‖STExpDriftg C μ n (v : ℝ) σ a‖
      = ‖STExpELKLKg C μ n (v : ℝ) σ a + STExpEGtg C μ n (v : ℝ) σ a‖ := rfl
    _ ≤ ‖STExpELKLKg C μ n (v : ℝ) σ a‖ + ‖STExpEGtg C μ n (v : ℝ) σ a‖ := norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (v : ℝ))⁻¹ * sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ)) +
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (v : ℝ))⁻¹ * sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)) :=
        add_le_add (hn1 (v, σ, a)) (hn2 (v, σ, a))
    _ = ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by ring

/-- **`(sum_res_Ndecay_nonzero)` applied to the deterministic drift tensors, uniformly in `s_n ≤ v ≤ u ≤ t_n`** (`6:144-146`; band
`expIntII_kernel_unif`, `ExpIntII:393`): `‖Q^{(A)} 𝒰_{v,u} D_v^σ‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` for `σ` in a class with `A ⊇ I_diff(σ)`, from the
drift bounds `STExpDriftHiConclgL`, no loss: for every time sequence `u` the pin `STEKNonzerogL` at `t ↦ u`, then `expIntII_lift` over `u`.  The band window
`(1-s) L² ≤ lam²` becomes the A-form window by R1 (`hcmp`, `lam² ≤ Aof κm · gK²`). -/
theorem expIntII_kernel_unifg {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}
    (hNZ : STEKNonzerogL d law Ker Aof) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm)
    (hadm : sz.Admissible 𝔠 𝔡) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) (hdr : STExpDriftHiConclgL C (law sz) s t)
    (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop)
    (hA : ∀ σ, P σ → ∀ i, σ i ≠ σ (finRotate 2 i) → i ∈ A) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ v (u : ℝ) (fun b => STExpDriftg C (law sz) n v σ b))‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hwin : ∀ n, (1 - s n) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ Aof κm * gK n ^ 2 := fun n => by
    have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := by
      have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
      positivity
    have h1 : 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by linarith [hsg n]
    rw [le_div_iff₀ hL] at h1
    exact h1.trans (hcmp n).2.2
  refine expIntII_lift (fun n => (hst n).le)
    (fun n u v => ∀ σ : Fin 2 → Bool, P σ →
      ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ v u (fun b => STExpDriftg C (law sz) n v σ b))‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hX : ∀ n (v : TimeIcc s u n) (_ : sz.SeqΩ), 0 ≤ (1 - (v : ℝ))⁻¹ *
      (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)) := by
    intro n v _
    have hv1 : (v : ℝ) < 1 := lt_of_le_of_lt v.2.2 (hu1 n)
    have hB0 := (STBctl_pos sz n hv1).le
    exact mul_nonneg (inv_nonneg.2 (by linarith)) (add_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hB0 _))
  have key : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, P σ → ∀ v : TimeIcc s u n,
      ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ (v : ℝ) (u n) (fun b => STExpDriftg C (law sz) n (v : ℝ) σ b))‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by
    intro σ
    by_cases hP : P σ
    · have hdom : PrecL sz (law sz) (U := fun n => TimeIcc s u n)
          (fun n v _ => ‖fun b => STExpDriftg C (law sz) n (v : ℝ) σ b‖)
          (fun n v _ => (1 - (v : ℝ))⁻¹ *
            (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by
        refine (st6_prec_det_iffg sz (law sz) hμ hsz (V := fun n => TimeIcc s u n)
          (fun n v => ‖fun b => STExpDriftg C (law sz) n (v : ℝ) σ b‖)
          (fun n v => (1 - (v : ℝ))⁻¹ *
            (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)))).2 ?_
        intro τ' hτ'
        filter_upwards [ExpIntIIGen_drift_pi C (law sz) hμ hsz ht1 hdr hτ'] with n hn v
        exact hn ⟨(v : ℝ), v.2.1, v.2.2.trans (hut n)⟩ σ
      have hk := hNZ hd 2 le_rfl κm 𝔠 𝔡 hκm hAof sz hadm C gK hKer hg s u hwin hs0 hsu hu1 σ A (hA σ hP)
        (fun n v _ => fun b => STExpDriftg C (law sz) n (v : ℝ) σ b)
        (fun n v _ => (1 - (v : ℝ))⁻¹ *
          (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) hX hdom
      have hk' := ((st6_prec_det_iffg sz (law sz) hμ hsz (V := fun n => TimeIcc s u n)
        (fun n v => ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ (v : ℝ) (u n)
          (fun b => STExpDriftg C (law sz) n (v : ℝ) σ b))‖)
        (fun n v => (1 - (v : ℝ))⁻¹ *
          (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)))).1 hk) τ hτ
      filter_upwards [hk'] with n hn _ v
      exact hn v
    · exact Filter.Eventually.of_forall fun n h => absurd h hP
  filter_upwards [Filter.eventually_all.2 key] with n hn v hv1 hv2 σ hP
  exact hn σ hP ⟨v, hv1, hv2⟩

end Kernel

/-! ## 3. The integrated estimate and the pin (targets 12, 13) -/

section Assembly

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`(iisuwjyys_exp)` closed** (`6:142-146`; band `STExpIntConcl_of_kernel`, `ExpIntII:472`), regime (ii), any `A`, `P`: the Duhamel identity
(`STExpDuhEqgL`, eventually in `n`), the uniform kernel bound `‖Q^{(A)} 𝒰_{v,u} D_v‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})`, the one-size integral bound
(`M = N^{τ/2}`) and `log L ≺ 1` give `‖Q^{(A)} f_u‖ ≤ N^τ F + N^τ T_u` for every control `F` of the initial term. -/
theorem STExpIntConclgL_of_kernel (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) (hd : 2 ≤ d) {s t : ℕ → ℝ}
    (_hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5II sz s t) (hduh : STExpDuhEqgL C μ s t)
    (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop)
    (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ v (u : ℝ) (fun b => STExpDriftg C μ n v σ b))‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) :
    STExpIntConclgL C μ A P s t := by
  intro F hF hini
  have hini' := ((st6_prec_det_iffg sz μ hμ hsz (V := STIdx2P sz P s t)
    (fun n p => ‖zeroModeSet d (sz.L n) A
      (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
    (fun n p => F n p)).1 hini)
  refine (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2P sz P s t)
    (fun n p => ‖zeroModeSet d (sz.L n) A (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
    (fun n p => F n p + STExpTarget sz n (p.1 : ℝ))).2 ?_
  intro τ hτ
  have h3 := expIntII_log_eventually sz hsz (by omega) (3 * ((d : ℝ) - 2)) (half_pos hτ)
  filter_upwards [hini' τ hτ, hker (τ / 2) (half_pos hτ), h3, hduh] with n hn1 hn2 hn3 hDu
  rintro ⟨u, ⟨σ, hP⟩, a⟩
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
  have hwin := (hR n).2
  have hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - (u : ℝ) := by
    have := (hR n).1
    have h2 : (u : ℝ) ≤ t n := u.2.2
    linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hP0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  have hint := expIntII_drift_integral_leg C μ n (s := s n) (u := (u : ℝ))
    (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) hd hP0 u.2.1 hu1 hwin hlo σ A
    (fun v hv1 hv2 => hn2 u v hv1 hv2 σ hP) a
  have hT0 : 0 ≤ STExpTarget sz n (u : ℝ) := st6_target_nonneg sz n hu1
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  change ‖zeroModeSet d (sz.L n) A (fun b => (∫ ω, C.L n (u : ℝ) σ b ω ∂μ) - C.K n (u : ℝ) σ b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (F n (u, ⟨σ, hP⟩, a) + STExpTarget sz n (u : ℝ))
  rw [hDu u σ A a]
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

/-- **The conclusion of the pin from the flow data alone** (band `STExpIntIIConcl_of_flow`, `ExpIntII:533`): `A = {1,2}` for `σ₁ ≠ σ₂`; `A = ∅` for `σ₁ = σ₂`
(`I_diff = ∅`, `st6_Idiff_same`). -/
theorem STExpIntIIConclgL_of_flow {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}
    (hNZ : STEKNonzerogL d law Ker Aof) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm)
    (hadm : sz.Admissible 𝔠 𝔡) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hR : STReg5II sz s t) (hduh : STExpDuhEqgL C (law sz) s t) (hdr : STExpDriftHiConclgL C (law sz) s t) :
    STExpIntConclgL C (law sz) (Finset.univ : Finset (Fin 2)) STSigMixed s t ∧ STExpIntConclgL C (law sz) ∅ STSigSame s t := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n := fun n => by linarith [(hR n).2]
  refine ⟨STExpIntConclgL_of_kernel C (law sz) hμ hsz (by omega) hst ht1 hR hduh _ _ fun τ hτ => ?_,
    STExpIntConclgL_of_kernel C (law sz) hμ hsz (by omega) hst ht1 hR hduh _ _ fun τ hτ => ?_⟩
  · exact expIntII_kernel_unifg C hNZ hd hκm hAof hadm gK hKer hg hcmp hμ hs0 hst ht1 hsg hdr _ _
      (fun σ _ i _ => Finset.mem_univ i) τ hτ
  · exact expIntII_kernel_unifg C hNZ hd hκm hAof hadm gK hKer hg hcmp hμ hs0 hst ht1 hsg hdr _ _
      (fun σ hσ i hi => absurd hi (st6_Idiff_same hσ i)) τ hτ

end Assembly

/-- **Target 13, the pin `STExpIntIIgL`** (`Step6Gen:368`; band `stExpIntII_holds`, `ExpIntII:553`) from the family premises: probability law (row 1), flow facts
(row 3), the class `Ker` at the coupling `gK` with the comparison R1 `∃ A` (written `Aof κm`, `κm` before `(sz, z)`) and the pin `STEKNonzerogL` (row 6; U3-BA
(a) at BA).  The constant `𝔠_d = 1/100`; the stochastic premises of `STIngR6gL` (`STLK`, `STDecay`, `STExp2`, `STConStInd`, `STStep2Core`, `STLmaxU`, `STLKU`,
`STGdecayW … 0`) are not used. -/
theorem stExpIntIIgL_of {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} {Ker : STEKKer d} {Aof : ℝ → ℝ}
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz, IsProbabilityMeasure (law sz))
    (hFF : Step5CasesGen_FlowFacts d Flow mk T0) (hNZ : STEKNonzerogL d law Ker Aof) (hAof : ∀ κm : ℝ, 0 < κm → 1 ≤ Aof κm)
    (hKer : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ (∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹) ∧
        ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK sz z n ^ 2) :
    STExpIntIIgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR _ _ _ _ _ _ _ _ hduh hdr
  obtain ⟨_, _, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  obtain ⟨κm, hκm, hKF⟩ := hKer κ hκ
  obtain ⟨-, hKer', hg', hR1'⟩ := hKF sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  exact STExpIntIIConclgL_of_flow (mk sz z) hNZ hd hκm (hAof κm hκm) hadm (gK sz z) hKer' hg' hR1' (hμ sz) hs0 hst ht1 hR
    hduh hdr

/-! ## 4. The band re-derivation -/

/-! ## 5. Compiled nonempty instances at `d = 3` (regime (ii) data of the band: `szB`, `zB`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `(s, t) = (15/16, 31/32)`)

`szB`: `L = 4`, `W_n = n + 4`, `lam = 1`; `lam²/L³ = 1/64 ≤ 1 - t = 1/32 ≤ 1 - s = 1/16 = lam²/L²` (the boundary of the window of
`(sum_res_Ndecay_nonzero)` is hit).  Discharged: flow, times, regime, admissibility, probability law, flow facts, the class `STEKBandKer` with `gK = lam` and R1 at `Aof = 1`,
the kernel pin `stek_nonzerogL_band`, the Duhamel identity (merged `stExpDuhamelZ_holds`).  The drift bounds `STExpDriftHiConclgL` (`(eq:Exp(L-K)1)`,
`(eq:ExpLWn=2)`: rows a and LW-14) stay a hypothesis of the examples that read them. -/

end RBM.BA

end
