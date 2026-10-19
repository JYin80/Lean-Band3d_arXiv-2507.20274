/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpIntI
import RBM3D.Chain.ExpIniIGen
import RBM3D.Chain.ExpWardIGen
import RBM3D.Chain.ExpIntIIGen
import RBM3D.Chain.ExpAvgGen

/-!
# The integrated estimate of regime (i) and the consumer over the carrier

Restatement of `Induction/ExpIntI` over a carrier `C : FlowFM sz` and a law `μ`, on the one kernel
`Step2Gen_UN C` and the vocabulary and statements of `Chain/Step6Gen`.  Paper: regime (i) in the proof
of Lemma 6.2 (`lem:LWterm_EXP`); Lemma 4.16 (`lem:sum_decay`), (4.54) `sum_res_2_NAL`, (4.56) `sum_res_2`.

* **Vocabulary.**  `STExpIntQConclgL'` (band `STExpIntQConcl'`, with the extra hypotheses
  `0 < Cq → 0 < c →`) and `STExpIntIgL'` (band `STExpIntI'`: the primed Ward hypothesis
  `STExpWardIConclgL'` and the second conjunct `STExpIntQConclgL'`).
* **The kernel.**  `expIntI_kernel_unifg` (band `expIntI_kernel_unif`): (4.54) `sum_res_2_NAL`
  (`σ₁ = σ₂`) or (4.56) `sum_res_2` (sum-zero family) with `n = 2` at the kernel coupling `gK`; the
  window `gK² ≤ lam²`, the decay class `lam² ≤ A gK²` and the ratio `(gK² + 1-v)/(gK² + 1-u) ≤ 2A` are
  read from the comparison hypothesis and `STReg5I` at `sz.lam` through the toolkit `step34Gen_*`; the
  constant is `4 A²` (band `A = 1`: `4`); `expIntI_concl_of_kernelg` and `expIntI_sameg`: the first
  conjunct of `STExpIntIgL'`.  The size-level `expIntI_ratio_le`, `expIntI_log_ratio` are reused by
  name.
* **The core.**  `st6_caseI_coreg'`: the Step 6 skeleton in regime (i) with `STExpWardIConclgL'`,
  `STExpIniIConclgL'`, `STExpIntQConclgL'` (the proof of band `ST_step6_caseI_of_pins''` per carrier);
  the average is per flow, `hAvgU : STExpAvgUgL C μ s t`.

The comparison hypothesis
`∀ n, 0 ≤ gK n * lam n ∧ gK n ^ 2 ≤ lam n ^ 2 ∧ lam n ^ 2 ≤ Aof κm * gK n ^ 2` enters only at the
window, the decay class and the ratio of `expIntI_kernel_unifg`.  The private model-free lemmas of the
band file (`expIntI_window`, `expIntI_lift`, `expIntI_Bctl_nonneg`) are used by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private expIntI_window expIntI_lift expIntI_Bctl_nonneg from RBM3D.Induction.ExpIntI

open private ExpIntIIGen_drift_pi from RBM3D.Chain.ExpIntIIGen

open private Step5CasesGen_prec_mono from RBM3D.Chain.Step5CasesGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The primed vocabulary -/

/-- `STExpIntQConclgL'` (band `STExpIntQConcl'`), with the extra hypotheses `0 < Cq → 0 < c →`. -/
def STExpIntQConclgL' {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ (Cq c : ℝ), 0 < Cq → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) → STExpDuhEqQgL C μ s t ϑ →
    ∀ F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ F n p) →
      PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => F n p) →
      PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
          (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
        (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))

/-- `STExpIntIgL'` (band `STExpIntI'`): the statement with the primed Ward hypothesis and the primed second conjunct. -/
def STExpIntIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftHiConclgL (mk sz z) (law sz) s t →
      STExpDriftDecayConclgL (mk sz z) (law sz) s t → STExpWardIConclgL' (mk sz z) (law sz) s t →
        STExpIntConclgL (mk sz z) (law sz) ∅ STSigSame s t ∧ STExpIntQConclgL' (mk sz z) (law sz) s t)

/-! ## 2. The kernel, uniformly in the end time -/

section Kernel

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}

/-- **The kernel at one end-time sequence `u ∈ [s,t]`** (band `expIntI_kernel_seq`; (4.54) `sum_res_2_NAL` for `σ₁ = σ₂`, (4.56) `sum_res_2` for a sum-zero family;
`n = 2`): the kernel statement at the window `STEKWinKgL sz gK s u` (`step34Gen_winK_of_cmp`, from the band window `expIntI_window` at `sz.lam` and `gK² ≤ lam²`), the decay class at `gK`
(`step34Gen_decayK_of_cmp`, `lam² ≤ A gK²`), applied to the deterministic family `𝒜_v`; `Prec` of a deterministic family is the pointwise bound, and the ratio at `gK`
`(gK² + 1-v)/(gK² + 1-u) ≤ A · (lam² + 1-v)/(lam² + 1-u) ≤ 2A` (`step34Gen_ratio_le`, `expIntI_ratio_le`, `1 - s ≤ lam²`), so the factor is `≤ 2A ≤ 4A²` (NAL, exponent `n-1 = 1`)
or `≤ 4A²` (sum-zero, exponent `n = 2`). -/
private theorem ExpIntIGen_kernel_seq (hd : 3 ≤ d) {κm 𝔠 𝔡 𝔠d : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ)
    (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (σ : Fin 2 → Bool)
    (𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) (X : ℕ → ℝ → ℝ)
    (hpin : (σ 0 = σ 1 ∧ STEKSumRes2NALgL d law Ker) ∨ ((∀ n v, EKSumZero (𝒜 n v)) ∧ STEKSumRes2gL d law Ker))
    (hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
      EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v))
    (hX0 : ∀ n v, 0 ≤ X n v)
    (hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v)
    (hbd : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
      ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v)
    (τ : ℝ) (hτ : 0 < τ) (u : ℕ → ℝ) (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n →
      ‖Step2Gen_UN C n σ v (u n) (𝒜 n v)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (4 * Aof κm ^ 2 * X n v) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hWt := step34Gen_W_tendsto hadm
  have hwin : STEKWinKgL sz gK s u :=
    step34Gen_winK_of_cmp hcmp (expIntI_window sz h𝔠d hdc hadm.2.2.2.2 hWt hs0 hst hsu hut ht1 hcon hR)
  have hdec' : STEKDecayKgL gK (law sz) s u (fun n v _ => 𝒜 n (v : ℝ)) := by
    refine step34Gen_decayK_of_cmp hcmp hAof hWt (law sz) ?_
    intro ε' D hε' hD
    refine HighProbAt.of_eventually_univ ?_
    filter_upwards [hdec ε' D hε' hD] with n hn ω v
    exact hn v v.2.1 (v.2.2.trans (hut n))
  obtain ⟨b, hb⟩ := hlow
  have hlow' : STEKLowgL (law sz) s u (fun n v _ => X n (v : ℝ)) := by
    refine ⟨b, HighProbAt.of_eventually_univ ?_⟩
    filter_upwards [hb] with n hn ω v
    exact hn v v.2.1 (v.2.2.trans (hut n))
  have hdom : PrecL sz (law sz) (U := fun n => TimeIcc s u n) (fun n v _ => ‖𝒜 n (v : ℝ)‖) (fun n v _ => X n (v : ℝ)) := by
    refine (st6_prec_det_iffg sz (law sz) hμ hsz (V := fun n => TimeIcc s u n) (fun n v => ‖𝒜 n (v : ℝ)‖)
      (fun n v => X n (v : ℝ))).2 ?_
    intro τ' hτ'
    filter_upwards [hbd τ' hτ'] with n hn v
    exact hn v v.2.1 (v.2.2.trans (hut n))
  have hA0 : 0 ≤ Aof κm := by linarith
  have hratio : ∀ n, ∀ v : ℝ, s n ≤ v → v ≤ u n →
      (gK n ^ 2 + |1 - v|) / (gK n ^ 2 + |1 - u n|) ≤ 2 * Aof κm := fun n v h1 h2 =>
    (step34Gen_ratio_le hcmp hAof n (hu1 n)).trans
      (by have := mul_le_mul_of_nonneg_left (expIntI_ratio_le h1 h2 (hu1 n) (hR n).2) hA0; linarith)
  have hr0 : ∀ n, ∀ v : ℝ, 0 ≤ (gK n ^ 2 + |1 - v|) / (gK n ^ 2 + |1 - u n|) := fun n v => by positivity
  rcases hpin with ⟨hσ, hSR⟩ | ⟨hzero, hS2⟩
  · -- `(sum_res_2_NAL)`: exponent `n - 1 = 1`
    have hσ' : ∃ k, σ k = σ (finRotate 2 k) := by
      refine ⟨0, ?_⟩
      have : finRotate 2 (0 : Fin 2) = 1 := by decide
      rw [this]; exact hσ
    have hk := hSR hd 2 le_rfl κm 𝔠 𝔡 hκm sz hadm C gK hKer hg s u hwin σ hσ' (fun n v _ => 𝒜 n (v : ℝ)) hdec'
      (fun n v _ => X n (v : ℝ)) hlow' hdom
    have hk' := ((st6_prec_det_iffg sz (law sz) hμ hsz (V := fun n => TimeIcc s u n)
      (fun n v => ‖Step2Gen_UN C n σ (v : ℝ) (u n) (𝒜 n (v : ℝ))‖)
      (fun n v => ((gK n ^ 2 + |1 - (v : ℝ)|) / (gK n ^ 2 + |1 - u n|)) ^ (2 - 1) * X n (v : ℝ))).1 hk) τ hτ
    filter_upwards [hk'] with n hn v hv1 hv2
    refine (hn ⟨v, hv1, hv2⟩).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h2 := hratio n v hv1 hv2
    have hx := hX0 n v
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    exact mul_le_mul_of_nonneg_right (h2.trans (by nlinarith)) hx
  · -- `(sum_res_2)`: exponent `n = 2`
    have hk := hS2 hd 2 le_rfl κm 𝔠 𝔡 hκm sz hadm C gK hKer hg s u hwin σ (fun n v _ => 𝒜 n (v : ℝ)) hdec'
      (fun n v _ => hzero n (v : ℝ)) (fun n v _ => X n (v : ℝ)) hlow' hdom
    have hk' := ((st6_prec_det_iffg sz (law sz) hμ hsz (V := fun n => TimeIcc s u n)
      (fun n v => ‖Step2Gen_UN C n σ (v : ℝ) (u n) (𝒜 n (v : ℝ))‖)
      (fun n v => ((gK n ^ 2 + |1 - (v : ℝ)|) / (gK n ^ 2 + |1 - u n|)) ^ 2 * X n (v : ℝ))).1 hk) τ hτ
    filter_upwards [hk'] with n hn v hv1 hv2
    refine (hn ⟨v, hv1, hv2⟩).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h2 := hratio n v hv1 hv2
    have h0 := hr0 n v
    have hx := hX0 n v
    have hsq : ((gK n ^ 2 + |1 - v|) / (gK n ^ 2 + |1 - u n|)) ^ 2 ≤ 4 * Aof κm ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq hx

/-- **The kernel, uniformly in the end time** (band `expIntI_kernel_unif`; (4.54) `sum_res_2_NAL` for `σ₁ = σ₂`, (4.56) `sum_res_2` for a sum-zero family, `n = 2`, regime (i)):
for a deterministic family `𝒜_v` with the decay (4.52) `deccA0` on `[s,t]`, a bound `X ≥ N^{-b}` and `‖𝒜_v‖ ≺ X`, eventually for all `u ∈ [s_n,t_n]` and `v ∈ [s_n,u]`,
`‖𝒰_{v,u} 𝒜_v‖ ≤ N^τ · 4A² X_v` (`A = Aof κm`; the band constant `4` at `A = 1`).  The statement of the case is the hypothesis `hpin`: `STEKSumRes2NALgL` for `σ₁ = σ₂`, `STEKSumRes2gL` for a
sum-zero family.  For every time sequence `u` the statement is applied at the window `STEKWinKgL sz gK s u`; the lift over `u` is the failing-sequence argument (`expIntI_lift`). -/
theorem expIntI_kernel_unifg (hd : 3 ≤ d) {κm 𝔠 𝔡 𝔠d : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ)
    (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (σ : Fin 2 → Bool)
    (𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) (X : ℕ → ℝ → ℝ)
    (hpin : (σ 0 = σ 1 ∧ STEKSumRes2NALgL d law Ker) ∨ ((∀ n v, EKSumZero (𝒜 n v)) ∧ STEKSumRes2gL d law Ker))
    (hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
      EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v))
    (hX0 : ∀ n v, 0 ≤ X n v)
    (hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v)
    (hbd : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
      ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ‖Step2Gen_UN C n σ v (u : ℝ) (𝒜 n v)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (4 * Aof κm ^ 2 * X n v) :=
  expIntI_lift (fun n => (hst n).le)
    (fun n u v => ‖Step2Gen_UN C n σ v u (𝒜 n v)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (4 * Aof κm ^ 2 * X n v))
    (fun u hsu hut => ExpIntIGen_kernel_seq hd hκm hAof h𝔠d hdc hadm C gK hKer hg hcmp hμ hs0 hst ht1 hR hcon σ 𝒜 X hpin hdec
      hX0 hlow hbd τ hτ u hsu hut)

end Kernel

/-! ## 3. The drift integral and the assembly -/

section Assembly

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The drift integral at one size**, regime (i) (band `expIntI_drift_integral_le`; proof of Lemma 6.2 `lem:LWterm_EXP`): a kernel bound `‖𝒰_{v,u} D_v‖_∞ ≤ M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` on `[s,u]`
gives `‖∫_s^u 𝒰_{v,u} D_v dv‖ ≤ M · 3 T_u · 2 log L` (`B_v ≤ B_u`, `∫_s^u (1-v)⁻¹ ≤ 2 log L`, `expIntI_log_ratio`; the rates need only `lam²/L^d ≤ 1-u`, which holds since `L^d ≥ L²`). -/
private theorem ExpIntIGen_drift_integral_le (n : ℕ) {s u M : ℝ} (hd : 2 ≤ d) (hM : 0 ≤ M)
    (hsu : s ≤ u) (hu : u < 1) (hwin : 1 - s ≤ sz.lam n ^ 2)
    (hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u) (σ : Fin 2 → Bool)
    (hker : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖Step2Gen_UN C n σ v u (fun b => STExpDriftg C μ n v σ b)‖ ≤
        M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖∫ v in s..u, zeroModeSet d (sz.L n) ∅ (Step2Gen_UN C n σ v u (fun b => STExpDriftg C μ n v σ b)) a‖ ≤
      M * (3 * STExpTarget sz n u * (2 * Real.log ((sz.L n : ℕ) : ℝ))) := by
  simp only [st5_zeroModeSet_empty]
  have hx : 0 < 1 - u := by linarith
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hLr : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL1
  have hl : sz.lam n ≠ 0 := by
    intro h0
    rw [h0] at hwin
    norm_num at hwin
    linarith
  have hlo' : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u := by
    refine le_trans ?_ hlo
    have h2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hLr hd
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h2
  have hT0 : 0 ≤ STExpTarget sz n u := st6_target_nonneg sz n hu
  have hrate := expIntII_rates_le_target sz n hu hl hlo'
  have hlogL : 0 ≤ 2 * Real.log ((sz.L n : ℕ) : ℝ) := mul_nonneg (by norm_num) (Real.log_nonneg hLr)
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
    (f := fun v => Step2Gen_UN C n σ v u (fun b => STExpDriftg C μ n v σ b) a)
    (g := fun v : ℝ => (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹) hsu
    (Filter.Eventually.of_forall fun v hv =>
      ((norm_le_pi_norm _ a).trans (hker v hv.1.le hv.2)).trans (hbound v hv.1.le hv.2)) hint
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hlog := expIntI_log_ratio (L := sz.L n) (g := sz.lam n) hL1 hsu hu hwin hlo
  calc M * (3 * STExpTarget sz n u) * ∫ v in s..u, (1 - v)⁻¹
      ≤ M * (3 * STExpTarget sz n u) * (2 * Real.log ((sz.L n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = M * (3 * STExpTarget sz n u * (2 * Real.log ((sz.L n : ℕ) : ℝ))) := by ring

/-- **(6.14) `iisuwjyys_exp` closed in regime (i)** (band `expIntI_concl_of_kernel`), `σ₁ = σ₂` (any class `P`, `A = ∅`): the Duhamel identity (`STExpDuhEqgL` at `A = ∅`, eventual),
the uniform kernel bound `‖𝒰_{v,u} D_v‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})`, the one-size integral bound (`M = N^{τ/2}`) and `log L ≺ 1` (`expIntII_log_eventually`, constant `6 = 3 · 2`) give
`‖f_u‖ ≤ N^τ F + N^τ T_u` for the bound `F` of the initial term. -/
theorem expIntI_concl_of_kernelg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) (hd : 3 ≤ d) {s t : ℕ → ℝ}
    (_hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t) (hduh : STExpDuhEqgL C μ s t)
    (P : (Fin 2 → Bool) → Prop)
    (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖Step2Gen_UN C n σ v (u : ℝ) (fun b => STExpDriftg C μ n v σ b)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) :
    STExpIntConclgL C μ ∅ P s t := by
  intro F hF hini
  have hini' := ((st6_prec_det_iffg sz μ hμ hsz (V := STIdx2P sz P s t)
    (fun n p => ‖zeroModeSet d (sz.L n) ∅
      (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
    (fun n p => F n p)).1 hini)
  refine (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2P sz P s t)
    (fun n p => ‖zeroModeSet d (sz.L n) ∅ (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
    (fun n p => F n p + STExpTarget sz n (p.1 : ℝ))).2 ?_
  intro τ hτ
  have h3 := expIntII_log_eventually sz hsz (by omega) 6 (half_pos hτ)
  filter_upwards [hini' τ hτ, hker (τ / 2) (half_pos hτ), h3, hduh] with n hn1 hn2 hn3 hDu
  rintro ⟨u, ⟨σ, hP⟩, a⟩
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
  have hwin := (hR n).2
  have hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - (u : ℝ) := by
    have := (hR n).1
    have h2 : (u : ℝ) ≤ t n := u.2.2
    linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hP0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  have hint := ExpIntIGen_drift_integral_le C μ n (s := s n) (u := (u : ℝ))
    (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (by omega) hP0 u.2.1 hu1 hwin hlo σ
    (fun v hv1 hv2 => hn2 u v hv1 hv2 σ hP) a
  have hT0 : 0 ≤ STExpTarget sz n (u : ℝ) := st6_target_nonneg sz n hu1
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  change ‖zeroModeSet d (sz.L n) ∅ (fun b => (∫ ω, C.L n (u : ℝ) σ b ω ∂μ) - C.K n (u : ℝ) σ b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (F n (u, ⟨σ, hP⟩, a) + STExpTarget sz n (u : ℝ))
  rw [hDu u σ ∅ a]
  refine (norm_add_le _ _).trans ?_
  have hn1' := hn1 (u, ⟨σ, hP⟩, a)
  have hlog : 6 * Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := hn3
  calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          (3 * STExpTarget sz n (u : ℝ) * (2 * Real.log ((sz.L n : ℕ) : ℝ))) :=
        add_le_add hn1' hint
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) *
          (6 * Real.log ((sz.L n : ℕ) : ℝ))) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) := by
        gcongr
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (F n (u, ⟨σ, hP⟩, a) + STExpTarget sz n (u : ℝ)) := by
        rw [hrpow]; ring

end Assembly

/-! ## 4. The `σ₁ = σ₂` conjunct -/

section Same

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}

/-- **The first conjunct of `STExpIntIgL'` from the flow data** (band `expIntI_same`; (4.54) `sum_res_2_NAL`, `n = 2`, `σ₁ = σ₂`): the bound `X_v = |1-v|⁻¹ (B_v^{11/5} + B_v^{5/2})` of the drift
(`STExpDriftHiConclgL`; the decay `STExpDriftDecayConclgL` of the deterministic tensors `D_v^σ` through `HighProbAt.nonempty`) in the kernel `expIntI_kernel_unifg` (loss `4A²`, absorbed by `4A² ≤ N^{τ/2}`) and
the assembly `expIntI_concl_of_kernelg`.  Lower bound `X ≥ N^{-3}` from `W^{-d}B_{v,0} ≥ N⁻¹` (`expAvg_Bctl_ge`).  The kernel statement is `STEKSumRes2NALgL` at `Ker sz C gK κm` with the comparison hypothesis; the hypotheses `STLK`,
`STDecay`, `STExp2`, `STStep2Core`, `STLmaxU`, `STLKU`, `STGdecayW … 0` of `STIngR6gL` are not used. -/
theorem expIntI_sameg (hSR : STEKSumRes2NALgL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 𝔠d : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ)
    (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (hduh : STExpDuhEqgL C (law sz) s t)
    (hdr : STExpDriftHiConclgL C (law sz) s t) (hdd : STExpDriftDecayConclgL C (law sz) s t) :
    STExpIntConclgL C (law sz) ∅ STSigSame s t := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  refine expIntI_concl_of_kernelg C (law sz) hμ hsz hd hst ht1 hR hduh STSigSame ?_
  intro τ hτ
  have h4 : ∀ᶠ n in atTop, 4 * Aof κm ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    (tendsto_size sz hsz).eventually (eventually_le_rpow (4 * Aof κm ^ 2) (half_pos hτ))
  have key : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, STSigSame σ → ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ‖Step2Gen_UN C n σ v (u : ℝ) (fun b => STExpDriftg C (law sz) n v σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
    intro σ
    by_cases hσ : STSigSame σ
    · have hdecay : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
          EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (fun b => STExpDriftg C (law sz) n v σ b) := by
        intro ε' D hε' hD
        filter_upwards [HighProbAt.nonempty (tendsto_size sz hsz) hμ.measure_univ (hdd σ ε' D hε' hD)]
          with n hn v hv1 hv2
        obtain ⟨ω, hω⟩ := hn
        exact hω ⟨v, hv1, hv2⟩
      have hX0 : ∀ n v, 0 ≤ |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) := by
        intro n v
        have hB0 := expIntI_Bctl_nonneg sz n v
        positivity
      have hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
          ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) := by
        refine ⟨3, Filter.Eventually.of_forall fun n v hv1 hv2 => ?_⟩
        have hv0 : 0 ≤ v := (hs0 n).trans hv1
        have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
        have hB := expAvg_Bctl_ge sz n hv0 hvl
        have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
        have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
        have hxpos : 0 < |1 - v| := abs_pos.2 (by linarith)
        have hx1 : 1 ≤ |1 - v|⁻¹ := by
          rw [abs_of_pos (by linarith : 0 < 1 - v)]
          exact (one_le_inv₀ (by linarith)).2 (by linarith)
        have hB0 := expIntI_Bctl_nonneg sz n v
        have h1 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ (11 / 5 : ℝ) ≤ sz.Bctl n v ^ (11 / 5 : ℝ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hN0.le) hB (by norm_num)
        have h2 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ (11 / 5 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (-(11 / 5 : ℝ)) := by
          rw [Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]
        have h3 : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(11 / 5 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        have h5 : 0 ≤ sz.Bctl n v ^ (5 / 2 : ℝ) := Real.rpow_nonneg hB0 _
        have h6 : 0 ≤ sz.Bctl n v ^ (11 / 5 : ℝ) := Real.rpow_nonneg hB0 _
        calc ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(11 / 5 : ℝ)) := h3
          _ ≤ sz.Bctl n v ^ (11 / 5 : ℝ) := h2 ▸ h1
          _ ≤ sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) := by linarith
          _ ≤ |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) :=
              le_mul_of_one_le_left (by linarith) hx1
      have hbd : ∀ τ' : ℝ, 0 < τ' → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
          ‖fun b => STExpDriftg C (law sz) n v σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' *
            (|1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
        intro τ' hτ'
        filter_upwards [ExpIntIIGen_drift_pi C (law sz) hμ hsz ht1 hdr hτ'] with n hn v hv1 hv2
        have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
        rw [abs_of_pos (by linarith : 0 < 1 - v)]
        exact hn ⟨v, hv1, hv2⟩ σ
      have hk := expIntI_kernel_unifg hd hκm hAof h𝔠d hdc hadm C gK hKer hg hcmp hμ hs0 hst ht1 hR hcon σ
        (fun n v b => STExpDriftg C (law sz) n v σ b)
        (fun n v => |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))
        (Or.inl ⟨hσ, hSR⟩) hdecay hX0 hlow hbd (τ / 2) (half_pos hτ)
      filter_upwards [hk, h4] with n hn h4n _ u v hv1 hv2
      have hvl : v < 1 := lt_of_le_of_lt (hv2.trans u.2.2) (ht1 n)
      have hn' := hn u v hv1 hv2
      have hx0 : 0 ≤ (1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) := by
        have hB0 := expIntI_Bctl_nonneg sz n v
        have : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
        positivity
      have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ =
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
        (UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ).symm
      rw [abs_of_pos (by linarith : 0 < 1 - v)] at hn'
      refine hn'.trans ?_
      rw [hrpow]
      calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (4 * Aof κm ^ 2 * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) +
            sz.Bctl n v ^ (5 / 2 : ℝ))))
          ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hN0
            exact mul_le_mul_of_nonneg_right h4n hx0
        _ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by ring
    · exact Filter.Eventually.of_forall fun n h => absurd h hσ
  filter_upwards [Filter.eventually_all.2 key] with n hn u v hv1 hv2 σ hP
  exact hn σ hP u v hv1 hv2

end Same

/-! ## 5. The regime (i) core -/

section Cores

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **Step 6, regime (i), per carrier, with the primed Ward, initial and integrated inputs** (band `ST_step6_caseI_of_pins''`).  `σ₁ = σ₂`: the plain Duhamel (`hint.1`) with the initial term `hini.1`; `σ₁ ≠ σ₂`: for a mollifier family (`st6_mollifier_familyg`, `0 < Cq`, `0 < c`) the `𝒬`-Duhamel
(`hint.2`, identity `hDuQ`) with the initial term `hini.2` and `f_u = 𝒬_u f_u + (𝒫 f_u) ϑ_u`, `(𝒫 f_u) ϑ_u ≺ B³` from the primed Ward conclusion `hward`.  The average is per flow (`hAvgU`). -/
theorem st6_caseI_coreg' {𝔠 𝔡 : ℝ} (hd : 3 ≤ d) (h𝔡 : 0 < 𝔡) (hadm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t)
    (hlk : STExpLKLKHiConclgL C μ s t) (hegt : STExpEGtHiConclgL C μ s t) (hdec : STExpDriftDecayConclgL C μ s t)
    (hAvgU : STExpAvgUgL C μ s t) (hward : STExpAvgUgL C μ s t → STExpWardIConclgL' C μ s t)
    (hini : STExpIniIConclgL' C μ s t) (hduh : STExpDuhEqgL C μ s t)
    (hDuQ : ∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
      (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) → STExpDuhEqQgL C μ s t ϑ)
    (hint : STExpDuhEqgL C μ s t → STExpDriftHiConclgL C μ s t → STExpDriftDecayConclgL C μ s t →
      STExpWardIConclgL' C μ s t → STExpIntConclgL C μ ∅ STSigSame s t ∧ STExpIntQConclgL' C μ s t) :
    STStep6ConclgL C μ s t := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hward' := hward hAvgU
  have hint' := hint hduh ⟨hlk, hegt⟩ hdec hward'
  have hT0 : ∀ n (u : ℝ), u ≤ t n → 0 ≤ STExpTarget sz n u := fun n u hu =>
    st6_target_nonneg sz n (lt_of_le_of_lt hu (ht1 n))
  -- `σ₁ = σ₂`
  have hS : PrecL sz μ (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hiniS : PrecL sz μ (U := STIdx2P sz STSigSame s t)
        (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
      simp only [st5_zeroModeSet_empty]
      exact hini.1
    have hmainS := hint'.1 (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2) hiniS
    simp only [st5_zeroModeSet_empty] at hmainS
    refine Step5CasesGen_prec_mono sz μ hsz (c := 2) hmainS (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    linarith
  -- `σ₁ ≠ σ₂`
  obtain ⟨Cq, c', hC, hc', ϑ, hϑ⟩ := st6_mollifier_familyg sz hd h𝔡 hadm.2.2.2.2
  have hmainQ := hint'.2 Cq c' hC hc' ϑ hϑ (hDuQ Cq c' ϑ hϑ) (fun n p => STExpTarget sz n (p.1 : ℝ))
    (fun n p => hT0 n _ p.1.2.2) (hini.2 Cq c' hC hc' ϑ hϑ)
  have hw := (hward' Cq c' hC hc' ϑ hϑ).1
  have hM : PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hsum := StochDomAt.add (tendsto_size sz hsz) hmainQ hw
    have hsum' : PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖)
        (fun n p _ => (STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ)) + (sz.Bctl n (p.1 : ℝ)) ^ 3) := by
      refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
      change ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖ ≤
        ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) * ϑ n (p.1 : ℝ) p.2.2‖
      calc ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖
          = ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2 +
            STPsum (d := d) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) * ϑ n (p.1 : ℝ) p.2.2‖ := by
            unfold STQop; ring_nf
        _ ≤ _ := norm_add_le _ _
    refine Step5CasesGen_prec_mono sz μ hsz (c := 3) hsum' (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have h2 := st6_cube_le_target sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ) + (sz.Bctl n (p.1 : ℝ)) ^ 3 ≤
      3 * STExpTarget sz n (p.1 : ℝ)
    linarith
  exact st6_cover_exp2Ug sz μ (ξ := fun n u σ a => ‖STExpErrg C μ n (u : ℝ) σ a‖)
    (ζ := fun n u _ _ => STExpTarget sz n (u : ℝ)) hsz (P₁ := STSigSame) (P₂ := STSigMixed)
    (fun σ => by by_cases h : σ 0 = σ 1 <;> simp [STSigSame, STSigMixed, h]) hS hM

end Cores

end RBM.BA

end
