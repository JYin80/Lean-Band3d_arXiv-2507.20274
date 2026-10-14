/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.Step2Gen
import RBM3D.Induction.QopDecay

/-!
# Propagation of `(deccA0)` through `Θ^{(n)}` of the carrier (BA-V row V1s3', ticket T2508 row b, target 9)

Additive restatement of `Induction/QopDecay.lean` (not edited) §5-§6 over a carrier `C : FlowFM sz`: `Θ^{(n)}` is `Step2Gen_ThetaN C` and the kernel decay is the class
`Step5KerGen_ThDecay C gK Λ C₆` (family row 22; the decay `|θ(a,b)| ≤ C₆ 𝒯_u(|b-a|_∞)` at the kernel coupling `gK` and the row sums `C₆/(1-u)`), which replaces the band
`QopDecay_thetaKer_decay` (`:636`).  Paper: arXiv:2507.20274, `3_5:112` (`def:op_thn`), `3_5:1215`, `3_5:1250`.

* **Target 9, `QopDecayGen_ThetaN_fastDecayg`** (= `T2508_QopDecayGenOf`, W-q): `Θ^{(n)}_u` maps a `(u, ε, D)`-decaying tensor of size `≤ W^{C₀}` (the scale `W^ε ℓ_u` at the
  coupling `sz.lam`) to a `(u, 2ε, D - (K+1))`-decaying tensor, for `W ≥ W₀(d, n, Λ, K, C₀, ε, D, C₆)`.  The only relation between the two couplings is `gK ≤ sz.lam`
  (`ellT` is monotone in the coupling, `QopDecayGen_ellT_mono`).  The generic tail is `𝒯_u(r) = B_{u,r} exp(-(r/ℓ_u)^{1/2})` (`Defs/Tail:48`), so the far term decays like
  `exp(-W^ε/(2d))` (the band has `exp(-c r/ℓ)` and `W^{2ε}`); `|b - a_i|_1 ≤ d |b - a_i|_∞` (`zdistD_le_mul_zdistInf`) converts the distance.  The `n = 2` form is
  `QopDecayGen_ThetaN2_fastDecayg`; the band `QopDecay_STthetaOp_fastDecay` (`:883`) is re-derived in §3 from `step5KerGen_thDecay_band` and `Step2Kern_ThetaN_band`.
  `QopAlgebra_mollifier_derivDecay`, `QopDecay_deriv_fastDecay` (`:497`, `:514`, deterministic) are reused by name.

The model-free private helpers of the band file `qdec_far_dist` and `qdec_growth` are used by `open private`.  No `def`, `abbrev` or `structure`; helpers are `private` and
prefixed `QopDecayGen_`.  Ports: none from `../RBM1D`, `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private qdec_far_dist qdec_growth from RBM3D.Induction.QopDecay

open Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The kernel profile at the coupling `gK ≤ sz.lam` -/

/-- `ℓ_u` is monotone in the coupling (`ℓ = min (max (g / √|1-u|) 1) L`). -/
private theorem QopDecayGen_ellT_mono {L : ℕ} {g g' t : ℝ} (hgg : g ≤ g') : ellT L g t ≤ ellT L g' t := by
  unfold ellT
  exact min_le_min_right _ (max_le_max_right _ (div_le_div_of_nonneg_right hgg (Real.sqrt_nonneg _)))

/-- `B_{u,r} ≤ 2 (1-u)⁻¹` for `r ≥ 0`, `u < 1`, `L ≥ 1` (the real-argument form of the band `qdec_Bparam_le`, `QopDecay:614`). -/
private theorem QopDecayGen_BparamR_le {d L : ℕ} (hL : 1 ≤ L) {g u : ℝ} (hu : u < 1) {r : ℝ} (hr : 0 ≤ r) :
    BparamR d L g u r ≤ 2 * (1 - u)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold BparamR
  rw [abs_of_pos h1u]
  have a1 : (g ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ h1u (by nlinarith [sq_nonneg g])
  have a2 : ((r + 1) ^ (d - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have a3 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ h1u (by nlinarith [one_le_pow₀ (n := d) hL1])
  have a4 : 0 ≤ (g ^ 2 + (1 - u))⁻¹ := inv_nonneg.2 (by nlinarith [sq_nonneg g])
  have a5 : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := inv_nonneg.2 (by positivity)
  calc (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹
      ≤ (1 - u)⁻¹ * 1 + (1 - u)⁻¹ := by gcongr
    _ = 2 * (1 - u)⁻¹ := by ring

/-! ## 2. Target 9 -/

set_option maxHeartbeats 400000 in
-- one near/far estimate with many `positivity` side goals in a single declaration
/-- **Target 9, `QopDecayGen_ThetaN_fastDecayg`** (= `T2508_QopDecayGenOf`; band `QopDecay_ThetaN_fastDecay`, `QopDecay:762`; W-q): `Θ^{(n)}_u` of the carrier maps a `(u, ε, D)`-decaying tensor
of size `≤ W^{C₀}` to a `(u, 2ε, D - (K+1))`-decaying tensor for `W ≥ W₀(d, n, Λ, K, C₀, ε, D, C₆)`, `L^d ≤ W^K`, `(1 - u)⁻¹ ≤ W^K`, at the coupling `sz.lam` (the scale `W^ε ℓ_u` of
`EKFastDecay`), from the class `Step5KerGen_ThDecay C gK Λ C₆` at `0 < gK k ≤ Λ` and `gK k ≤ sz.lam k` only.  Near terms: the row sum `C₆/(1-u)` and the decay of `A`; far terms:
`C₆ 𝒯_u(|b-a_i|_∞) ≤ 2 C₆ (1-u)⁻¹ exp(-W^ε/(2d))`. -/
theorem QopDecayGen_ThetaN_fastDecayg (d n : ℕ) (hd : 3 ≤ d) (Λ K C₀ ε D C₆ : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) (hC₆ : 0 < C₆) :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ →
      ∀ k : ℕ, 0 < gK k → gK k ≤ Λ → gK k ≤ sz.lam k → W₀ ≤ ((sz.W k : ℕ) : ℝ) →
        ((sz.L k : ℕ) : ℝ) ^ d ≤ ((sz.W k : ℕ) : ℝ) ^ K →
        ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W k : ℕ) : ℝ) ^ K →
        ∀ (σ : Fin n → Bool) (A : (Fin n → Zd d (sz.L k)) → ℂ), ‖A‖ ≤ ((sz.W k : ℕ) : ℝ) ^ C₀ →
          EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) ε D A →
          EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (Step2Gen_ThetaN C k σ u A) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  obtain ⟨W₁, hW₁, hgrow⟩ := qdec_growth (C := 4 * ((n : ℝ) + 1) * C₆) (c := 1 / (d : ℝ)) (ε' := ε)
    (p := K + C₀ + D - 1) (by positivity) (by positivity) hε
  refine ⟨max W₁ (max ((2 : ℝ) ^ (1 / ε)) (2 * n * C₆)), lt_of_lt_of_le hW₁ (le_max_left _ _), ?_⟩
  intro sz C gK hTh k hg hgΛ hgl hW hLW u hu0 hu1 hKu σ A hA hAd a ⟨j, j', hjj⟩
  set W : ℝ := ((sz.W k : ℕ) : ℝ) with hWdef
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans hW
  have hW2ε : (2 : ℝ) ^ (1 / ε) ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWn : 2 * (n : ℝ) * C₆ ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hW1 : 1 < W := lt_of_lt_of_le hW₁ hWW₁
  have hW0 : 0 < W := by linarith
  have hWε : 2 ≤ W ^ ε := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
      _ ≤ W ^ ε := Real.rpow_le_rpow (by positivity) hW2ε hε.le
  have hWε2 : W ^ (2 * ε) = W ^ ε * W ^ ε := by rw [two_mul, Real.rpow_add hW0]
  have hL1n : 1 ≤ sz.L k := by have := sz.three_le_L k; omega
  have hL1 : (1 : ℝ) ≤ sz.L k := by exact_mod_cast hL1n
  set ℓ : ℝ := ellT (sz.L k) (sz.lam k) u with hℓ
  set ℓ' : ℝ := ellT (sz.L k) (gK k) u with hℓ'
  have hℓ'1 : 1 ≤ ℓ' := one_le_ellT hL1
  have hℓℓ : ℓ' ≤ ℓ := QopDecayGen_ellT_mono hgl
  have hℓ1 : 1 ≤ ℓ := hℓ'1.trans hℓℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ'0 : 0 < ℓ' := by linarith
  set x : ℝ := 1 / (d : ℝ) * W ^ ε / 2 with hx
  have hr : 2 * (W ^ ε * ℓ) ≤ W ^ (2 * ε) * ℓ := by
    rw [hWε2]
    nlinarith [mul_nonneg (sub_nonneg.2 hWε) (mul_nonneg (by linarith : (0 : ℝ) ≤ W ^ ε) hℓ0.le)]
  have hθ := hTh k hg hgΛ
  set E : ℝ := C₆ * (2 * W ^ K) * W ^ C₀ * Real.exp (-x) with hE
  have hE0 : 0 ≤ E := by positivity
  have hpar : ∀ i : Fin n, ‖∑ b : Zd d (sz.L k), Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b *
      A (Function.update a i b)‖ ≤ C₆ * (W ^ K * W ^ (-D)) + W ^ K * E := by
    intro i
    obtain ⟨hdec, hrow⟩ := hθ (σ i) (σ (finRotate n i)) u hu0 hu1
    have hpt : ∀ b : Zd d (sz.L k), ‖Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b *
        A (Function.update a i b)‖ ≤
        ‖Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b‖ * W ^ (-D) + E := by
      intro b
      rw [norm_mul]
      by_cases hnear : ∃ p q : Fin n,
          W ^ ε * ℓ ≤ (zdistD d (sz.L k) (Function.update a i b p - Function.update a i b q) : ℝ)
      · have h1 : ‖A (Function.update a i b)‖ ≤ W ^ (-D) := hAd _ hnear
        have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b))
        linarith
      · push Not at hnear
        have hdist := qdec_far_dist a b i j j' hr hjj hnear
        have hdD : (zdistD d (sz.L k) (b - a i) : ℝ) ≤ (d : ℝ) * ((zdistInf d (sz.L k) (b - a i) : ℕ) : ℝ) := by
          exact_mod_cast zdistD_le_mul_zdistInf d (sz.L k) (b - a i)
        set r : ℝ := ((zdistInf d (sz.L k) (b - a i) : ℕ) : ℝ) with hrdef
        have hr0 : 0 ≤ r := Nat.cast_nonneg _
        have hrlow : W ^ (2 * ε) * ℓ ≤ 2 * ((d : ℝ) * r) := by linarith
        have hx0 : 0 ≤ x := by positivity
        have hxr : x ≤ Real.sqrt (r / ℓ') := by
          refine Real.le_sqrt_of_sq_le ?_
          rw [le_div_iff₀ hℓ'0]
          have hx2 : x ^ 2 = W ^ (2 * ε) / (4 * (d : ℝ) ^ 2) := by
            rw [hx, hWε2]; field_simp; ring
          rw [hx2, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have hW2ℓ : 0 ≤ W ^ (2 * ε) * ℓ' := by positivity
          calc W ^ (2 * ε) * ℓ' ≤ W ^ (2 * ε) * ℓ := mul_le_mul_of_nonneg_left hℓℓ (by positivity)
            _ ≤ 2 * ((d : ℝ) * r) := hrlow
            _ ≤ r * (4 * (d : ℝ) ^ 2) := by nlinarith [mul_nonneg hr0 (sub_nonneg.2 hd1)]
        have hexp : Real.exp (-Real.sqrt (r / ℓ')) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
        have hB := QopDecayGen_BparamR_le (d := d) (L := sz.L k) (g := gK k) hL1n hu1 hr0
        have hB0 : 0 ≤ BparamR d (sz.L k) (gK k) u r := BparamR_nonneg hr0
        have htail : tailT d (sz.L k) (gK k) u r ≤ 2 * W ^ K * Real.exp (-x) := by
          unfold tailT
          calc BparamR d (sz.L k) (gK k) u r * Real.exp (-Real.sqrt (r / ellT (sz.L k) (gK k) u))
              ≤ (2 * (1 - u)⁻¹) * Real.exp (-x) := mul_le_mul hB hexp (Real.exp_pos _).le (by positivity)
            _ ≤ (2 * W ^ K) * Real.exp (-x) := by gcongr
        have hK1 : ‖Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b‖ ≤ C₆ * (2 * W ^ K * Real.exp (-x)) :=
          (hdec (a i) b).trans (mul_le_mul_of_nonneg_left (by simpa [hrdef] using htail) hC₆.le)
        have hA1 : ‖A (Function.update a i b)‖ ≤ W ^ C₀ := (norm_le_pi_norm A _).trans hA
        have h3 := mul_le_mul hK1 hA1 (norm_nonneg _) (by positivity)
        have h4 : 0 ≤ ‖Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b‖ * W ^ (-D) := by positivity
        calc _ ≤ C₆ * (2 * W ^ K * Real.exp (-x)) * W ^ C₀ := h3
          _ = E := by rw [hE]; ring
          _ ≤ _ := by linarith
    calc ‖∑ b : Zd d (sz.L k), Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b * A (Function.update a i b)‖
        ≤ ∑ b : Zd d (sz.L k), ‖Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b * A (Function.update a i b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ b : Zd d (sz.L k), (‖Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b‖ * W ^ (-D) + E) :=
          Finset.sum_le_sum fun b _ => hpt b
      _ = (∑ b : Zd d (sz.L k), ‖Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b‖) * W ^ (-D) +
            (sz.L k : ℝ) ^ d * E := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast; ring
      _ ≤ C₆ * (W ^ K * W ^ (-D)) + W ^ K * E := by
          have hrow' : ∑ b : Zd d (sz.L k), ‖Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b‖ ≤ C₆ * W ^ K := by
            refine (hrow (a i)).trans ?_
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left hKu hC₆.le
          have h5 := mul_le_mul_of_nonneg_right hrow' (by positivity : 0 ≤ W ^ (-D))
          have h6 := mul_le_mul_of_nonneg_right hLW hE0
          linarith
  unfold Step2Gen_ThetaN
  refine (norm_sum_le _ _).trans ?_
  have hQ0 : 0 ≤ W ^ K * W ^ (-D) := by positivity
  set Z := W ^ (-(D - (K + 1))) with hZ
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos hW0 _
  have hZe : Z = W * (W ^ K * W ^ (-D)) := by
    rw [hZ, show -(D - (K + 1)) = 1 + K + -D by ring, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
    ring
  have hT1 : (n : ℝ) * (C₆ * (W ^ K * W ^ (-D))) ≤ Z / 2 := by
    rw [hZe]
    have h := mul_le_mul_of_nonneg_right hWn hQ0
    calc (n : ℝ) * (C₆ * (W ^ K * W ^ (-D))) = (2 * (n : ℝ) * C₆ * (W ^ K * W ^ (-D))) / 2 := by ring
      _ ≤ (W * (W ^ K * W ^ (-D))) / 2 := div_le_div_of_nonneg_right h (by norm_num)
  have hpow : W ^ K * (C₆ * (2 * W ^ K) * W ^ C₀) = 2 * C₆ * (W ^ (K + C₀ + D - 1) * Z) := by
    have h1 : W ^ K * W ^ K * W ^ C₀ = W ^ (K + K + C₀) := by rw [Real.rpow_add hW0, Real.rpow_add hW0]
    have h2 : W ^ (K + C₀ + D - 1) * Z = W ^ (K + C₀ + D - 1 + -(D - (K + 1))) := by
      rw [hZ, Real.rpow_add hW0]
    have h3 : W ^ K * (C₆ * (2 * W ^ K) * W ^ C₀) = 2 * C₆ * (W ^ K * W ^ K * W ^ C₀) := by ring
    have h4 : K + K + C₀ = K + C₀ + D - 1 + -(D - (K + 1)) := by ring
    rw [h3, h1, h2, h4]
  have hg1 : 4 * ((n : ℝ) + 1) * C₆ * W ^ (K + C₀ + D - 1) ≤ Real.exp x := hgrow W hWW₁
  set q := 2 * C₆ * W ^ (K + C₀ + D - 1) * Real.exp (-x) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : 2 * ((n : ℝ) + 1) * q ≤ 1 := by
    calc 2 * ((n : ℝ) + 1) * q = (4 * ((n : ℝ) + 1) * C₆ * W ^ (K + C₀ + D - 1)) * Real.exp (-x) := by
          rw [hq]; ring
      _ ≤ Real.exp x * Real.exp (-x) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hT2 : (n : ℝ) * (W ^ K * E) ≤ Z / 2 := by
    have e : W ^ K * E = Z * q := by
      calc W ^ K * E = W ^ K * (C₆ * (2 * W ^ K) * W ^ C₀) * Real.exp (-x) := by rw [hE]; ring
        _ = 2 * C₆ * (W ^ (K + C₀ + D - 1) * Z) * Real.exp (-x) := by rw [hpow]
        _ = Z * q := by rw [hq]; ring
    rw [e]
    have hn1 : (n : ℝ) * q ≤ ((n : ℝ) + 1) * q := mul_le_mul_of_nonneg_right (by linarith) hq0
    have hnq : (n : ℝ) * q ≤ 1 / 2 := by linarith only [hn1, hq1]
    calc (n : ℝ) * (Z * q) = Z * ((n : ℝ) * q) := by ring
      _ ≤ Z * (1 / 2) := mul_le_mul_of_nonneg_left hnq hZ0.le
      _ = Z / 2 := by ring
  calc ∑ i : Fin n, ‖∑ b : Zd d (sz.L k), Step2Gen_thetaKer C k (σ i) (σ (finRotate n i)) u (a i) b *
        A (Function.update a i b)‖
      ≤ ∑ _i : Fin n, (C₆ * (W ^ K * W ^ (-D)) + W ^ K * E) := Finset.sum_le_sum fun i _ => hpar i
    _ = (n : ℝ) * (C₆ * (W ^ K * W ^ (-D))) + (n : ℝ) * (W ^ K * E) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ Z := by linarith

/-- **The `n = 2` form** (band `QopDecay_STthetaOp_fastDecay`, `QopDecay:883`, sizes form): target 9 at two-index tensors, every sign pattern `σ : Fin 2 → Bool`. -/
theorem QopDecayGen_ThetaN2_fastDecayg (d : ℕ) (hd : 3 ≤ d) (Λ K C₀ ε D C₆ : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) (hC₆ : 0 < C₆) :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ →
      ∀ k : ℕ, 0 < gK k → gK k ≤ Λ → gK k ≤ sz.lam k → W₀ ≤ ((sz.W k : ℕ) : ℝ) →
        ((sz.L k : ℕ) : ℝ) ^ d ≤ ((sz.W k : ℕ) : ℝ) ^ K →
        ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W k : ℕ) : ℝ) ^ K →
        ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L k)) → ℂ), ‖A‖ ≤ ((sz.W k : ℕ) : ℝ) ^ C₀ →
          EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) ε D A →
          EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (Step2Gen_ThetaN C k σ u A) :=
  QopDecayGen_ThetaN_fastDecayg d 2 hd Λ K C₀ ε D C₆ hΛ hε hC₆

/-! ## 3. The band re-derivation -/

/-- **Band `QopDecay_STthetaOp_fastDecay` re-derived** (`QopDecay:883`) from `QopDecayGen_ThetaN2_fastDecayg` at `bandFM sz (fun _ => E)`, `gK = sz.lam`: the class `Step5KerGen_ThDecay` is
the merged `step5KerGen_thDecay_band` (`|E| ≤ 2`), the carrier operator is `STthetaOp` through `Step2Kern_ThetaN_band` and `STthetaOp_eq_ThetaN`. -/
theorem QopDecayGen_STthetaOp_fastDecay_band {d : ℕ} (hd : 3 ≤ d) (Λ K C₀ ε D : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λ →
      W₀ ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ), ‖A‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε D A →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (STthetaOp sz n E u σ A) := by
  obtain ⟨C₆, hC₆, hTh⟩ := step5KerGen_thDecay_band d Λ hd hΛ
  obtain ⟨W₀, hW₀, h⟩ := QopDecayGen_ThetaN2_fastDecayg d hd Λ K C₀ ε D C₆ hΛ hε hC₆
  refine ⟨W₀, hW₀, ?_⟩
  intro sz n E hE hlam hlamΛ hW hLW u hu0 hu1 hKu σ A hA hAd
  have key := h sz (bandFM sz (fun _ => E)) sz.lam (hTh sz (fun _ => E) (fun _ => hE)) n hlam hlamΛ le_rfl hW hLW u hu0 hu1
    hKu σ A hA hAd
  have e : Step2Gen_ThetaN (bandFM sz (fun _ => E)) n σ u A = STthetaOp sz n E u σ A := by
    rw [Step2Kern_ThetaN_band]
    funext a
    exact (STthetaOp_eq_ThetaN sz n E u σ A a).symm
  rw [← e]
  exact key

/-! ## 4. Compiled nonempty instances (`d = 3`, `sz0`: `L_k = 4(k+1)`, `W_k = (2(k+1))^5`, `lam_k = (2(k+1))^{-6}`; `gK = lam`, `Λ = 1`, `E = 0`, `u = 1/2`, `K = 3`, `C₀ = 1`, `ε = 1/10`,
`D = 5`)

`szB` (`L = 4`) is not used: there `zdistD ≤ 6` and the decay windows `W^ε ℓ ≤ zdistD` are empty for large `W`.  At `sz0` the windows are nonempty: `ℓ_u = 1` for `lam ≤ 1/2`, `u ≤ 3/4`, and
`W_k^{1/5} = 2(k+1) = L_k/2` is the distance of `x = (2(k+1), 0, 0)` to `0`; every instance proves that the input and the output decay conditions fail for the constant tensor `1`. -/

section Instances

open RBM.Gauss.SizesInst

/-- `0 < lam_k ≤ 1/2` along `sz0`. -/
private theorem QopDecayGen_sz0_lam (k : ℕ) : 0 < sz0.lam k ∧ sz0.lam k ≤ 1 / 2 := by
  have hm : (2 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have h2 : (2 : ℝ) ≤ (2 * ((k : ℝ) + 1)) ^ 6 := hm.trans (le_self_pow₀ (by linarith) (by norm_num))
  change 0 < ((2 * ((k : ℝ) + 1)) ^ 6)⁻¹ ∧ ((2 * ((k : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 2
  exact ⟨inv_pos.2 (by positivity), by rw [one_div]; exact inv_anti₀ (by norm_num) h2⟩

/-- `W_k = (2(k+1))^5` as a real number. -/
private theorem QopDecayGen_sz0_W (k : ℕ) : ((sz0.W k : ℕ) : ℝ) = (2 * ((k : ℝ) + 1)) ^ 5 := by
  change (((2 * (k + 1)) ^ 5 : ℕ) : ℝ) = _
  push_cast; ring

/-- `ℓ_t = 1` (upper bound) for `0 ≤ g ≤ 1/2`, `t ≤ 3/4`. -/
private theorem QopDecayGen_ellT_le_one {L : ℕ} {g t : ℝ} (hg : g ≤ 1 / 2) (ht : t ≤ 3 / 4) : ellT L g t ≤ 1 := by
  unfold ellT
  refine (min_le_left _ _).trans (max_le ?_ le_rfl)
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt |1 - t| := by
    rw [show (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by rw [abs_of_pos (by linarith)]; linarith)
  rw [div_le_one (by linarith)]
  linarith

/-- **The far pair at `sz0`**: for `ε ≤ 1/5` and `ℓ ≤ 1` the window `W_k^ε ℓ ≤ |a_1 - a_0|` contains `a = (0, (2(k+1), 0, 0))`. -/
private theorem QopDecayGen_sz0_far (k : ℕ) {ε g t : ℝ} (hε : ε ≤ 1 / 5) (hℓ : ellT (sz0.L k) g t ≤ 1) :
    ∃ a : Fin 2 → Zd 3 (sz0.L k), ∃ i j : Fin 2,
      ((sz0.W k : ℕ) : ℝ) ^ ε * ellT (sz0.L k) g t ≤ (zdistD 3 (sz0.L k) (a i - a j) : ℝ) := by
  set x : Zd 3 (sz0.L k) := fun i => if i = 0 then ((2 * (k + 1) : ℕ) : ZMod (sz0.L k)) else 0 with hx
  have hv : (((2 * (k + 1) : ℕ) : ZMod (sz0.L k))).val = 2 * (k + 1) := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by change _ < 4 * (k + 1); omega)
  have hz : zdistD 3 (sz0.L k) x = 2 * (k + 1) := by
    simp only [zdistD, Fin.sum_univ_three, hx]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Fin.reduceEq, zdist_zero, add_zero]
    simp only [zdist, hv]
    change min (2 * (k + 1)) (4 * (k + 1) - 2 * (k + 1)) = 2 * (k + 1)
    omega
  refine ⟨![0, x], 1, 0, ?_⟩
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero]
  rw [hz]
  have hm : (1 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hW1 : (1 : ℝ) ≤ ((sz0.W k : ℕ) : ℝ) := by
    rw [QopDecayGen_sz0_W]; exact one_le_pow₀ hm
  have h15 : ((sz0.W k : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((k : ℝ) + 1) := by
    rw [QopDecayGen_sz0_W, show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by linarith) (by norm_num)
  have hℓ0 : 0 < ellT (sz0.L k) g t := ellT_pos (by change (1 : ℝ) ≤ ((4 * (k + 1) : ℕ) : ℝ); push_cast; linarith)
  calc ((sz0.W k : ℕ) : ℝ) ^ ε * ellT (sz0.L k) g t ≤ ((sz0.W k : ℕ) : ℝ) ^ (1 / 5 : ℝ) * 1 :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le hW1 hε) hℓ hℓ0.le (Real.rpow_nonneg (by linarith) _)
    _ = ((2 * (k + 1) : ℕ) : ℝ) := by rw [h15]; push_cast; ring

/-- **The decay condition is not empty at `sz0`**: for `ε ≤ 1/5`, `D > 0` and `ℓ ≤ 1`, the constant tensor `1` is not `(ε, D)`-decaying. -/
private theorem QopDecayGen_sz0_nontriv (k : ℕ) {ε g t D : ℝ} (hε : ε ≤ 1 / 5) (hD : 0 < D) (hℓ : ellT (sz0.L k) g t ≤ 1) :
    ¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay g t ((sz0.W k : ℕ) : ℝ) ε D A := by
  intro h
  obtain ⟨a, i, j, hij⟩ := QopDecayGen_sz0_far k hε hℓ
  have h1 := h (fun _ => 1) a ⟨i, j, hij⟩
  have hm : (1 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hW : (1 : ℝ) < ((sz0.W k : ℕ) : ℝ) := by
    rw [QopDecayGen_sz0_W]
    calc (1 : ℝ) < 2 := by norm_num
      _ ≤ 2 * ((k : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
      _ ≤ (2 * ((k : ℝ) + 1)) ^ 5 := le_self_pow₀ hm (by norm_num)
  have hlt := Real.rpow_lt_one_of_one_lt_of_neg hW (neg_lt_zero.2 hD)
  simp only [norm_one] at h1
  linarith

/-- The size data and the tensor of the instances at `k = ⌈W₀⌉₊`: `W₀ ≤ W_k`, `L_k^3 ≤ W_k^3`, `(1 - 1/2)⁻¹ = 2 ≤ W_k^3`, and the delta tensor `𝟙_{a = 0}` (nonzero, `‖·‖ = 1 ≤ W_k`,
`(1/10, 5)`-decaying since it vanishes off `0` and `0` is outside every window). -/
private theorem QopDecayGen_inst_data (W₀ : ℝ) :
    W₀ ≤ ((sz0.W ⌈W₀⌉₊ : ℕ) : ℝ) ∧ ((sz0.L ⌈W₀⌉₊ : ℕ) : ℝ) ^ 3 ≤ ((sz0.W ⌈W₀⌉₊ : ℕ) : ℝ) ^ (3 : ℝ) ∧
      (1 - (1 / 2 : ℝ))⁻¹ ≤ ((sz0.W ⌈W₀⌉₊ : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ‖(fun a : Fin 2 → Zd 3 (sz0.L ⌈W₀⌉₊) => if a = 0 then (1 : ℂ) else 0)‖ ≤ ((sz0.W ⌈W₀⌉₊ : ℕ) : ℝ) ^ (1 : ℝ) ∧
      EKFastDecay (sz0.lam ⌈W₀⌉₊) (1 / 2) ((sz0.W ⌈W₀⌉₊ : ℕ) : ℝ) (1 / 10) 5
        (fun a : Fin 2 → Zd 3 (sz0.L ⌈W₀⌉₊) => if a = 0 then (1 : ℂ) else 0) := by
  set k := ⌈W₀⌉₊ with hk
  set m : ℝ := 2 * ((k : ℝ) + 1) with hmdef
  have hk0 := Nat.cast_nonneg (α := ℝ) k
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; linarith
  have hW : ((sz0.W k : ℕ) : ℝ) = m ^ 5 := QopDecayGen_sz0_W k
  have hL : ((sz0.L k : ℕ) : ℝ) = 2 * m := by
    change (((4 * (k + 1)) : ℕ) : ℝ) = _
    rw [hmdef]; push_cast; ring
  have hm5 : m ≤ m ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
  have hW32 : (32 : ℝ) ≤ m ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ m ^ 5 := pow_le_pow_left₀ (by norm_num) hm2 5
  have hp3 : ∀ x : ℝ, x ^ (3 : ℝ) = x ^ 3 := fun x => by exact_mod_cast Real.rpow_natCast x 3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hW]
    have := Nat.le_ceil W₀
    rw [← hk] at this
    linarith
  · rw [hp3, hW, hL]
    have h8 : (8 : ℝ) ≤ m ^ 12 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hm2 12)
    calc (2 * m) ^ 3 = 8 * m ^ 3 := by ring
      _ ≤ m ^ 12 * m ^ 3 := mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = (m ^ 5) ^ 3 := by ring
  · rw [hp3, hW]
    have : (32 : ℝ) ≤ (m ^ 5) ^ 3 := hW32.trans (le_self_pow₀ (by linarith) (by norm_num))
    norm_num; linarith
  · rw [Real.rpow_one]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
    rw [hW]
    split_ifs
    · simp only [norm_one]; linarith
    · simp only [norm_zero]; positivity
  · intro a ⟨i, j, hij⟩
    have hW0 : (0 : ℝ) < ((sz0.W k : ℕ) : ℝ) := by rw [hW]; positivity
    by_cases h0 : a = 0
    · exfalso
      have hL1 : (1 : ℝ) ≤ ((sz0.L k : ℕ) : ℝ) := by rw [hL]; linarith
      have hpos : 0 < ((sz0.W k : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ellT (sz0.L k) (sz0.lam k) (1 / 2) :=
        mul_pos (Real.rpow_pos_of_pos hW0 _) (ellT_pos hL1)
      rw [h0, Pi.zero_apply, Pi.zero_apply, sub_self, zdistD_zero] at hij
      push_cast at hij
      linarith
    · beta_reduce
      simp only [h0, ↓reduceIte, norm_zero]
      exact Real.rpow_nonneg hW0.le _

/-- **Target 9, `QopDecayGen_ThetaN_fastDecayg` (`n = 2`)** at `sz0`: the class `Step5KerGen_ThDecay` is the merged `step5KerGen_thDecay_band` at `gK = lam`, `Λ = 1`; the size conditions and the tensor are
`QopDecayGen_inst_data`; no hypothesis remains.  The first two conjuncts: the input `(1/10, 5)` and the output `(1/5, 1)` decay conditions are not empty at `k`. -/
example : ∃ k : ℕ,
    (¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (1 / 10) 5 A) ∧
    (¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (2 * (1 / 10)) (5 - (3 + 1)) A) ∧
    ∀ σ : Fin 2 → Bool,
    EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (2 * (1 / 10)) (5 - (3 + 1))
      (Step2Gen_ThetaN (bandFM sz0 (fun _ => (0 : ℝ))) k σ (1 / 2)
        (fun a : Fin 2 → Zd 3 (sz0.L k) => if a = 0 then (1 : ℂ) else 0)) := by
  obtain ⟨C₆, hC₆, hTh⟩ := step5KerGen_thDecay_band 3 1 (by norm_num) one_pos
  obtain ⟨W₀, hW₀, H⟩ := QopDecayGen_ThetaN_fastDecayg 3 2 (by norm_num) 1 3 1 (1 / 10) 5 C₆ one_pos (by norm_num) hC₆
  obtain ⟨hW, hL, hK, hA, hAd⟩ := QopDecayGen_inst_data W₀
  obtain ⟨hl0, hl1⟩ := QopDecayGen_sz0_lam ⌈W₀⌉₊
  have hℓ := QopDecayGen_ellT_le_one (L := sz0.L ⌈W₀⌉₊) hl1 (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
  exact ⟨⌈W₀⌉₊, QopDecayGen_sz0_nontriv _ (by norm_num) (by norm_num) hℓ, QopDecayGen_sz0_nontriv _ (by norm_num) (by norm_num) hℓ,
    fun σ => H sz0 (bandFM sz0 (fun _ => (0 : ℝ))) sz0.lam (hTh sz0 (fun _ => 0) (fun _ => by norm_num)) ⌈W₀⌉₊
      hl0 (by linarith) le_rfl hW hL (1 / 2) (by norm_num) (by norm_num) hK σ _ hA hAd⟩

/-- **The `n = 2` form** `QopDecayGen_ThetaN2_fastDecayg` at the same data. -/
example : ∃ k : ℕ,
    (¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (1 / 10) 5 A) ∧
    (¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (2 * (1 / 10)) (5 - (3 + 1)) A) ∧
    ∀ σ : Fin 2 → Bool,
    EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (2 * (1 / 10)) (5 - (3 + 1))
      (Step2Gen_ThetaN (bandFM sz0 (fun _ => (0 : ℝ))) k σ (1 / 2)
        (fun a : Fin 2 → Zd 3 (sz0.L k) => if a = 0 then (1 : ℂ) else 0)) := by
  obtain ⟨C₆, hC₆, hTh⟩ := step5KerGen_thDecay_band 3 1 (by norm_num) one_pos
  obtain ⟨W₀, hW₀, H⟩ := QopDecayGen_ThetaN2_fastDecayg 3 (by norm_num) 1 3 1 (1 / 10) 5 C₆ one_pos (by norm_num) hC₆
  obtain ⟨hW, hL, hK, hA, hAd⟩ := QopDecayGen_inst_data W₀
  obtain ⟨hl0, hl1⟩ := QopDecayGen_sz0_lam ⌈W₀⌉₊
  have hℓ := QopDecayGen_ellT_le_one (L := sz0.L ⌈W₀⌉₊) hl1 (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
  exact ⟨⌈W₀⌉₊, QopDecayGen_sz0_nontriv _ (by norm_num) (by norm_num) hℓ, QopDecayGen_sz0_nontriv _ (by norm_num) (by norm_num) hℓ,
    fun σ => H sz0 (bandFM sz0 (fun _ => (0 : ℝ))) sz0.lam (hTh sz0 (fun _ => 0) (fun _ => by norm_num)) ⌈W₀⌉₊
      hl0 (by linarith) le_rfl hW hL (1 / 2) (by norm_num) (by norm_num) hK σ _ hA hAd⟩

/-- **The band re-derivation** `QopDecayGen_STthetaOp_fastDecay_band` at the same data (`E = 0`): the band operator `STthetaOp sz0 k 0 (1/2) σ` applied to the delta tensor. -/
example : ∃ k : ℕ,
    (¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (1 / 10) 5 A) ∧
    (¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (2 * (1 / 10)) (5 - (3 + 1)) A) ∧
    ∀ σ : Fin 2 → Bool,
    EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (2 * (1 / 10)) (5 - (3 + 1))
      (STthetaOp sz0 k 0 (1 / 2) σ (fun a : Fin 2 → Zd 3 (sz0.L k) => if a = 0 then (1 : ℂ) else 0)) := by
  obtain ⟨W₀, hW₀, H⟩ := QopDecayGen_STthetaOp_fastDecay_band (d := 3) (by norm_num) 1 3 1 (1 / 10) 5 one_pos (by norm_num)
  obtain ⟨hW, hL, hK, hA, hAd⟩ := QopDecayGen_inst_data W₀
  obtain ⟨hl0, hl1⟩ := QopDecayGen_sz0_lam ⌈W₀⌉₊
  have hℓ := QopDecayGen_ellT_le_one (L := sz0.L ⌈W₀⌉₊) hl1 (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
  exact ⟨⌈W₀⌉₊, QopDecayGen_sz0_nontriv _ (by norm_num) (by norm_num) hℓ, QopDecayGen_sz0_nontriv _ (by norm_num) (by norm_num) hℓ,
    fun σ => H sz0 ⌈W₀⌉₊ 0 (by norm_num) hl0 (by linarith) hW hL (1 / 2) (by norm_num) (by norm_num) hK σ _ hA hAd⟩

end Instances

end RBM.BA

end
