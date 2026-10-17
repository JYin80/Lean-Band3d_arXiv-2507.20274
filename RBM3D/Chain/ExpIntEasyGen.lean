/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpIntEasy

/-!
# The integrated estimates of regimes (iii) and (iv) over the carrier (BA-V row V1s3', ticket T2508 row a, targets 3-4)

Additive restatement of `Induction/ExpIntEasy.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the one kernel `Step2Gen_UN C` and the vocabulary and pins of
`Chain/Step6Gen.lean`.  Paper: arXiv:2507.20274, `6:93-96` (regimes (iii), (iv)), `(Eexpint_K-L)` `6:3-7`, `(sum_res_Ndecay)` `3_5:1620-1622`.

* **Target 3.**  `expIntEasy_kernel_seqg` (band `expIntEasy_kernel_seq`, `ExpIntEasy:355`): `(sum_res_Ndecay)` with `n = 2` (the pin `STEKSumNdecaygL`, kernel `Step2Gen_UN C`, class `Ker` at
  the coupling `gK`; no ratio, so no comparison R1) applied per time sequence `u` to the drift `D_v = STExpDriftg C μ`; `expIntIII_int_unifg`, `expIntIV_int_unifg` (band `:504`, `:531`): the
  drift integral `∫_s^u 𝒰_{v,u} D_v dv ≺ T_u` uniformly in `(u,σ,a)`, one lift over `u` (`st6_precU_of_forall_seqg`).  The size-level inputs (`expIntEasy_integral_rpow`,
  `expIntIII_rates_le_target`, `expIntIV_rate_le_target`, `expIntIII_drift_integral_le`, `expIntIV_drift_integral_le`, `:48-305`) are reused by name.
* **Target 4.**  `STExpIntConclgL_of_int` (band `STExpIntConcl_of_int`, `:556`; the Duhamel identity is the eventual `STExpDuhEqgL`, D725), `STExpIntIIIConclgL_of_flow`,
  `STExpIntIVConclgL_of_flow` (`:593`, `:601`), `stExpIntIIIgL_of`, `stExpIntIVgL_of` (→ `STExpIntIIIgL`, `STExpIntIVgL`, `Step6Gen:356-365`); the band `stExpIntIII_holds`,
  `stExpIntIV_holds` (`:610`, `:618`) are re-derived through `STExpIntIII_of_gL`, `STExpIntIV_of_gL` (`Step6Gen:618`, `:626`).  `stStep6IV_holds` (`:626`) reads the global
  `stImproveExpAver_holds`: band only (V1L-C1).

Coupling (UBA-C1): `STReg5III/IV`, `Bctl` and the kernel at `gK` through the pin `STEKSumNdecaygL` (no ratio): R1 never.  No `def`, `abbrev` or `structure` is added; helpers are
`private` and prefixed `ExpIntEasyGen_`.  Ports: none from `../RBM1D`, `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The kernel estimate per time sequence (target 3) -/

section Kernel

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d}

/-- **`(sum_res_Ndecay)` with `n = 2` on the drift `D_v`** (band `expIntEasy_kernel_seq`, `ExpIntEasy:355`): from an eventual bound `‖D_v^σ‖_∞ ≤ N^τ X_v` on `[s_n,u_n]` (every `τ > 0`) the
same for `‖𝒰_{v,u}D_v^σ‖_∞` with the factor `((1-v)/(1-u))²`, uniformly in `v ∈ [s_n,u_n]` and `σ` (no lift: `u` is one sequence).  The pin `STEKSumNdecaygL` is read at the class
`Ker sz C gK κm` (kernel `Step2Gen_UN C`, no comparison). -/
theorem expIntEasy_kernel_seqg (hSum : STEKSumNdecaygL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm)
    {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) (hμ : IsProbabilityMeasure (law sz))
    {s u : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsu : ∀ n, s n ≤ u n) (hu1 : ∀ n, u n < 1) (X : ℕ → ℝ → ℝ)
    (hX : ∀ n v, s n ≤ v → v ≤ u n → 0 ≤ X n v)
    (h : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpDriftg C (law sz) n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool,
      ‖Step2Gen_UN C n σ v (u n) (fun b => STExpDriftg C (law sz) n v σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - v) / (1 - u n)) ^ 2 * X n v) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have key : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, ∀ v : TimeIcc s u n,
      ‖Step2Gen_UN C n σ (v : ℝ) (u n) (fun b => STExpDriftg C (law sz) n (v : ℝ) σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - (v : ℝ)) / (1 - u n)) ^ 2 * X n (v : ℝ)) := by
    intro σ
    have hdom : PrecL sz (law sz) (U := fun n => TimeIcc s u n)
        (fun n v _ => ‖(fun b => STExpDriftg C (law sz) n (v : ℝ) σ b)‖) (fun n v _ => X n (v : ℝ)) := by
      rw [st6_prec_det_iffg sz (law sz) hμ hsz]
      intro τ' hτ'
      filter_upwards [h τ' hτ'] with n hn v
      exact hn v v.2.1 v.2.2 σ
    have hk := hSum hd 2 le_rfl κm 𝔠 𝔡 hκm sz hadm C gK hKer hg s u hs0 hsu hu1 σ
      (fun n v _ => fun b => STExpDriftg C (law sz) n (v : ℝ) σ b)
      (fun n v _ => X n (v : ℝ)) (fun n v _ => hX n v v.2.1 v.2.2) hdom
    rw [st6_prec_det_iffg sz (law sz) hμ hsz] at hk
    exact hk τ hτ
  have hall := Filter.eventually_all.2 key
  filter_upwards [hall] with n hn v h1 h2 σ
  exact hn σ ⟨v, h1, h2⟩

end Kernel

/-! ## 2. The drift bounds as pointwise eventual bounds, and the lift over `u` -/

section Lift

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- The drift premise of the window `1-u ≥ lam²/L^d`, regime (iii), as an eventual pointwise bound of `‖D_v^σ‖_∞` (band `expIntEasy_drift_pi_hi`, `ExpIntEasy:397`; deterministic:
`st6_prec_det_iffg`, the triangle inequality `D = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}`, `pi_norm_le_iff_of_nonneg`). -/
private theorem ExpIntEasyGen_drift_pi_hi (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ}
    (ht1 : ∀ n, t n < 1) (hDr : STExpDriftHiConclgL C μ s t) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpDriftg C μ n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
  have h1 := (st6_prec_det_iffg sz μ hμ hsz _ _).1 hDr.1 τ hτ
  have h2 := (st6_prec_det_iffg sz μ hμ hsz _ _).1 hDr.2 τ hτ
  filter_upwards [h1, h2] with n hn1 hn2 v hsv hvt σ
  have hv1 : v < 1 := lt_of_le_of_lt hvt (ht1 n)
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hB : 0 < sz.Bctl n v := STBctl_pos sz n hv1
  have hxinv : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
  have hX : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) :=
    mul_nonneg hN (mul_nonneg hxinv (add_nonneg (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hB.le _)))
  rw [pi_norm_le_iff_of_nonneg hX]
  intro a
  have e1 := hn1 (⟨⟨v, hsv, hvt⟩, σ, a⟩ : STIdx2 sz s t n)
  have e2 := hn2 (⟨⟨v, hsv, hvt⟩, σ, a⟩ : STIdx2 sz s t n)
  change ‖STExpELKLKg C μ n v σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * sz.Bctl n v ^ (11 / 5 : ℝ)) at e1
  change ‖STExpEGtg C μ n v σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * sz.Bctl n v ^ (5 / 2 : ℝ)) at e2
  calc ‖STExpDriftg C μ n v σ a‖ = ‖STExpELKLKg C μ n v σ a + STExpEGtg C μ n v σ a‖ := rfl
    _ ≤ ‖STExpELKLKg C μ n v σ a‖ + ‖STExpEGtg C μ n v σ a‖ := norm_add_le _ _
    _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

/-- The drift premise of regime (iv) as an eventual pointwise bound of `‖D_v^σ‖_∞` (band `expIntEasy_drift_pi_lo`, `ExpIntEasy:423`). -/
private theorem ExpIntEasyGen_drift_pi_lo (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ}
    (ht1 : ∀ n, t n < 1) (hDr : STExpDriftLoConclgL C μ s t) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpDriftg C μ n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3) := by
  have h1 := (st6_prec_det_iffg sz μ hμ hsz _ _).1 hDr τ hτ
  filter_upwards [h1] with n hn v hsv hvt σ
  have hv1 : v < 1 := lt_of_le_of_lt hvt (ht1 n)
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hX : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      ((1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3) := by
    have : 0 < 1 - v := by linarith
    positivity
  rw [pi_norm_le_iff_of_nonneg hX]
  intro a
  exact hn (⟨⟨v, hsv, hvt⟩, σ, a⟩ : STIdx2 sz s t n)

end Lift

section LiftCore

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d}

/-- **The lift over `u`** (band `expIntEasy_lift_core`, `ExpIntEasy:445`; §64 (4), one lift per regime): given the eventual pointwise drift bound `‖D_v^σ‖_∞ ≤ N^τ X_v`
(`v ∈ [s_n,t_n]`), the one-size integral estimate (with the kernel factor `((1-v)/(1-u))²`) and the rate `R_u ≤ c T_u` (eventually in `n`, every `u ∈ [s_n,t_n]`), the deterministic
family `‖∫_{s_n}^u 𝒰_{v,u} D_v^σ dv‖_a` is `≺ T_u` uniformly in `(u,σ,a)`: per time sequence `u` the kernel bound (`expIntEasy_kernel_seqg`, at `τ/2`), then
`st6_precU_of_forall_seqg` (both sides deterministic). -/
private theorem ExpIntEasyGen_lift_core (hSum : STEKSumNdecaygL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm)
    {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) (hμ : IsProbabilityMeasure (law sz))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (X R : ℕ → ℝ → ℝ) (c : ℝ)
    (hX : ∀ n v, s n ≤ v → v ≤ t n → 0 ≤ X n v)
    (hdrift : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpDriftg C (law sz) n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v)
    (hint : ∀ n (u M : ℝ) (F : ℝ → ℂ), 0 ≤ M → s n ≤ u → u ≤ t n →
      (∀ v : ℝ, s n ≤ v → v ≤ u → ‖F v‖ ≤ M * (((1 - v) / (1 - u)) ^ 2 * X n v)) →
        ‖∫ v in (s n)..u, F v‖ ≤ M * R n u)
    (hrate : ∀ᶠ n in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n → R n u ≤ c * STExpTarget sz n u) :
    PrecL sz (law sz) (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1 v (p.1 : ℝ)
          (fun b => STExpDriftg C (law sz) n v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  refine st6_precU_of_forall_seqg sz (law sz) hμ hsz (fun n => (hst n).le)
    (W := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖∫ v in (s n)..u, Step2Gen_UN C n w.1 v u (fun b => STExpDriftg C (law sz) n v w.1 b) w.2‖)
    (fun n u _ => STExpTarget sz n u) ?_
  intro u hsu hut
  rw [st6_prec_det_iffg sz (law sz) hμ hsz]
  intro τ hτ
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hk := expIntEasy_kernel_seqg hSum hd hκm hadm C gK hKer hg hμ hs0 hsu hu1 X
    (fun n v h1 h2 => hX n v h1 (h2.trans (hut n)))
    (fun τ' hτ' => (hdrift τ' hτ').mono fun n hn v h1 h2 σ => hn v h1 (h2.trans (hut n)) σ)
    (τ / 2) (half_pos hτ)
  filter_upwards [hk, hrate, (tendsto_size sz hsz).eventually (eventually_le_rpow c (half_pos hτ))] with n hkn hrn hc
  rintro ⟨σ, a⟩
  have hM : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 := hint n (u n) (((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (fun v => Step2Gen_UN C n σ v (u n) (fun b => STExpDriftg C (law sz) n v σ b) a) hM (hsu n) (hut n)
    (fun v h1 h2 => (norm_le_pi_norm _ a).trans (hkn v h1 h2 σ))
  have hT := st6_target_nonneg sz n (hu1 n)
  change ‖∫ v in (s n)..(u n), Step2Gen_UN C n σ v (u n) (fun b => STExpDriftg C (law sz) n v σ b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (u n)
  calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * R n (u n) := h1
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (c * STExpTarget sz n (u n)) :=
        mul_le_mul_of_nonneg_left (hrn (u n) (hsu n) (hut n)) hM
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * STExpTarget sz n (u n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hT) hM
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (u n) := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]

end LiftCore

/-! ## 3. The drift integrals, the assembly and the pins (targets 3, 4) -/

section Pins

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d}

/-- **Regime (iii): the drift integral `∫_s^u 𝒰_{v,u}D_v dv ≺ T_u`, uniformly in `(u,σ,a)`** (band `expIntIII_int_unif`, `ExpIntEasy:504`): per time sequence `u` the kernel bound
(`expIntEasy_kernel_seqg` with `X_v = (1-v)⁻¹(B_v^{11/5} + B_v^{5/2})` from `STExpDriftHiConclgL`), `expIntIII_drift_integral_le` with `M = N^{τ/2}`, `expIntIII_rates_le_target`
(`lam_n ≠ 0` eventually: `st6_lam_pos`), `64 ≤ N^{τ/2}`; then one lift over `u`.  The kernel pin is read at `Ker sz C gK κm`, no ratio. -/
theorem expIntIII_int_unifg (hSum : STEKSumNdecaygL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm)
    {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) (hμ : IsProbabilityMeasure (law sz))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5III sz s t)
    (hDr : STExpDriftHiConclgL C (law sz) s t) :
    PrecL sz (law sz) (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1 v (p.1 : ℝ)
          (fun b => STExpDriftg C (law sz) n v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  refine ExpIntEasyGen_lift_core hSum hd hκm hadm C gK hKer hg hμ hs0 hst ht1
    (fun n v => (1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))
    (fun n u => 5 * (2 * sz.Bctl n u) ^ (11 / 5 : ℝ) + 2 * (2 * sz.Bctl n u) ^ (5 / 2 : ℝ)) 64
    ?_ (ExpIntEasyGen_drift_pi_hi C (law sz) hμ hsz ht1 hDr) ?_ ?_
  · intro n v h1 h2
    have hv1 : v < 1 := lt_of_le_of_lt h2 (ht1 n)
    have hB : 0 < sz.Bctl n v := STBctl_pos sz n hv1
    exact mul_nonneg (inv_nonneg.2 (by linarith))
      (add_nonneg (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hB.le _))
  · intro n u M F hM hsu hut hF
    exact expIntIII_drift_integral_le sz n F hM hsu (lt_of_le_of_lt hut (ht1 n))
      ((hR n).trans (by linarith)) hF
  · filter_upwards [st6_lam_pos sz hadm.2.2.2.2] with n hn u hsu hut
    exact expIntIII_rates_le_target sz n (lt_of_le_of_lt hut (ht1 n)) hn.ne'
      ((hR n).trans (by linarith))

/-- **Regime (iv)**: the same with `X_v = (1-v)⁻¹(N(1-v))^{-3}` from `STExpDriftLoConclgL`, `expIntIV_drift_integral_le`, `expIntIV_rate_le_target` (no regime hypothesis, no
`lam ≠ 0`); one lift over `u` (band `expIntIV_int_unif`, `ExpIntEasy:531`). -/
theorem expIntIV_int_unifg (hSum : STEKSumNdecaygL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm)
    {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) (hμ : IsProbabilityMeasure (law sz))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hDr : STExpDriftLoConclgL C (law sz) s t) :
    PrecL sz (law sz) (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1 v (p.1 : ℝ)
          (fun b => STExpDriftg C (law sz) n v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  refine ExpIntEasyGen_lift_core hSum hd hκm hadm C gK hKer hg hμ hs0 hst ht1
    (fun n v => (1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3)
    (fun n u => ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3) 1
    ?_ (ExpIntEasyGen_drift_pi_lo C (law sz) hμ hsz ht1 hDr) ?_ ?_
  · intro n v h1 h2
    have hv1 : 0 < 1 - v := by linarith [ht1 n]
    have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    positivity
  · intro n u M F hM hsu hut hF
    exact expIntIV_drift_integral_le sz n F hM hsu (lt_of_le_of_lt hut (ht1 n)) hF
  · exact Filter.Eventually.of_forall fun n u hsu hut => by
      rw [one_mul]
      exact expIntIV_rate_le_target sz n (lt_of_le_of_lt hut (ht1 n))

end Pins

section Concl

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`(Eexpint_K-L)` (`6:3-7`) closed, `A = ∅`, all `σ`** (band `STExpIntConcl_of_int`, `ExpIntEasy:556`): the Duhamel identity (`STExpDuhEqgL` at `A = ∅`, `st5_zeroModeSet_empty`; eventual,
D725), the initial-term control `F` and the drift-integral bound give `STExpIntConclgL ∅ STSigAll` (`‖f_u‖ ≤ N^τ F + N^τ T_u`). -/
theorem STExpIntConclgL_of_int (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ}
    (hduh : STExpDuhEqgL C μ s t)
    (hint : PrecL sz μ (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1 v (p.1 : ℝ)
          (fun b => STExpDriftg C μ n v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))) :
    STExpIntConclgL C μ ∅ STSigAll s t := by
  intro F hF0 hini
  rw [st6_prec_det_iffg sz μ hμ hsz] at hini ⊢
  intro τ hτ
  have hint' := (st6_prec_det_iffg sz μ hμ hsz _ _).1 hint τ hτ
  filter_upwards [hini τ hτ, hint', hduh] with n h1 h2 hD p
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp := h2 ((p.1, p.2.1.1, p.2.2) : STIdx2 sz s t n)
  have hi := h1 p
  have hd := hD p.1 p.2.1.1 ∅ p.2.2
  simp only [st5_zeroModeSet_empty] at hd hi ⊢
  have hd' : STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2 =
      Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b) p.2.2 +
      ∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1.1 v (p.1 : ℝ) (fun b => STExpDriftg C μ n v p.2.1.1 b) p.2.2 := hd
  rw [hd']
  calc ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b) p.2.2 +
      ∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1.1 v (p.1 : ℝ) (fun b => STExpDriftg C μ n v p.2.1.1 b) p.2.2‖
      ≤ ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b) p.2.2‖ +
        ‖∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1.1 v (p.1 : ℝ)
          (fun b => STExpDriftg C μ n v p.2.1.1 b) p.2.2‖ := norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * F n p + ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (p.1 : ℝ) :=
        add_le_add hi hp
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (F n p + STExpTarget sz n (p.1 : ℝ)) := by ring

/-- **Regime (iii): the conclusion of the pin from the flow data** (band `STExpIntIIIConcl_of_flow`, `ExpIntEasy:593`; no stochastic premise of `STIngR6gL` is used). -/
theorem STExpIntIIIConclgL_of_flow {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d}
    (hSum : STEKSumNdecaygL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm)
    (hadm : sz.Admissible 𝔠 𝔡) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) (hμ : IsProbabilityMeasure (law sz))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5III sz s t)
    (hduh : STExpDuhEqgL C (law sz) s t) (hDr : STExpDriftHiConclgL C (law sz) s t) :
    STExpIntConclgL C (law sz) ∅ STSigAll s t :=
  STExpIntConclgL_of_int C (law sz) hμ hadm.2.2.1 hduh (expIntIII_int_unifg hSum hd hκm hadm C gK hKer hg hμ hs0 hst ht1 hR hDr)

/-- **Regime (iv)**: the same, without the regime (the drift premise carries it; band `STExpIntIVConcl_of_flow`, `ExpIntEasy:601`). -/
theorem STExpIntIVConclgL_of_flow {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d}
    (hSum : STEKSumNdecaygL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm)
    (hadm : sz.Admissible 𝔠 𝔡) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) (hμ : IsProbabilityMeasure (law sz))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hduh : STExpDuhEqgL C (law sz) s t) (hDr : STExpDriftLoConclgL C (law sz) s t) :
    STExpIntConclgL C (law sz) ∅ STSigAll s t :=
  STExpIntConclgL_of_int C (law sz) hμ hadm.2.2.1 hduh (expIntIV_int_unifg hSum hd hκm hadm C gK hKer hg hμ hs0 hst ht1 hDr)

end Concl

/-! ## 4. The pins (target 4) -/

section PinsOf

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
  {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
  {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} {Ker : STEKKer d}

/-- **The pin `STExpIntIIIgL`** (`Step6Gen:356`; band `stExpIntIII_holds`, `ExpIntEasy:610`, regime (iii), `6:94-96`) from the family premises: probability law (row 1), flow facts (row 3: admissibility,
`T0 < 1`), the kernel pin `STEKSumNdecaygL` (row 5) and the kernel data at the coupling `gK` (`κm ≤ Im m`, the class `Ker`, `0 < gK ≤ 𝔡⁻¹` eventually; the `hKer` of `ST_step6_caseIII_of_pinsgL`,
`Step6KitGen:682-684`).  The constant `𝔠_d = 1/100`; the stochastic premises of `STIngR6gL` are not used. -/
theorem stExpIntIIIgL_of (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz, IsProbabilityMeasure (law sz))
    (hFF : Step5CasesGen_FlowFacts d Flow mk T0) (hSum : STEKSumNdecaygL d law Ker)
    (hKer : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ ∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹) :
    STExpIntIIIgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR _ _ _ _ _ _ _ _ hduh hDr
  obtain ⟨_, _, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  obtain ⟨κm, hκm, hKF⟩ := hKer κ hκ
  obtain ⟨-, hKer', hg'⟩ := hKF sz ε 𝔠 𝔡 z hflow
  exact STExpIntIIIConclgL_of_flow (mk sz z) hSum hd hκm hadm (gK sz z) hKer' hg' (hμ sz) hs0 hst
    (fun n => (htT n).trans_lt (hT0 n)) hR hduh hDr

/-- **The pin `STExpIntIVgL`** (`Step6Gen:362`; band `stExpIntIV_holds`, `ExpIntEasy:618`, regime (iv), `6:94-96`): the same premises; the regime hypothesis is not used. -/
theorem stExpIntIVgL_of (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz, IsProbabilityMeasure (law sz))
    (hFF : Step5CasesGen_FlowFacts d Flow mk T0) (hSum : STEKSumNdecaygL d law Ker)
    (hKer : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ ∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹) :
    STExpIntIVgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT _ _ _ _ _ _ _ _ _ hduh hDr
  obtain ⟨_, _, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  obtain ⟨κm, hκm, hKF⟩ := hKer κ hκ
  obtain ⟨-, hKer', hg'⟩ := hKF sz ε 𝔠 𝔡 z hflow
  exact STExpIntIVConclgL_of_flow (mk sz z) hSum hd hκm hadm (gK sz z) hKer' hg' (hμ sz) hs0 hst
    (fun n => (htT n).trans_lt (hT0 n)) hduh hDr

end PinsOf

/-! ## 5. The band re-derivations -/

/-! ## 6. Compiled nonempty instances at `d = 3` (regime (iii) `(sz0, z0, 0, 1/16)`, regime (iv) `(szG, zB, 5/8, 3/4)`)

Data (merged, `Step6Pins` §8; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`).  Discharged: flow, times, regime, admissibility, probability law, flow facts, the kernel pin
`stek_sumNdecaygL_band` and the band class `STEKBandKer` with its bulk datum `κm = √(2κ)/2`.  What stays a hypothesis is another gate's pin: the drift bounds
(`STExpDriftHiConclgL`, `STExpDriftLoConclgL`: rows of T2506 and `LWtermEXPG`).  The Duhamel identity along `[s,t]` (`STExpDuhEqgL`) is discharged by the merged
`stExpDuhamelZ_holds` through `st6_duhEq_of_ping`. -/

end RBM.BA

end
