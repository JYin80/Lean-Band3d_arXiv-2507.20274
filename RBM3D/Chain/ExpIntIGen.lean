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
# The integrated estimate of regime (i) and the consumer over the carrier (BA-V row V1s3', ticket T2508 row a, targets 5-8)

Additive restatement of `Induction/ExpIntI.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the one kernel `Step2Gen_UN C` and the vocabulary and pins of
`Chain/Step6Gen.lean`.  Paper: arXiv:2507.20274, `6:97, 104-132` (regime (i)), `3_5:1630-1662` (`lem:sum_decay`, `(sum_res_2_NAL)` `3_5:1649`, `(sum_res_2)` `3_5:1659`).

* **Target 5** (vocabulary).  `STExpIntQConclgL'` (band `STExpIntQConcl'`, `ExpIntI:56`: `STExpIntQConclgL`, `Step6Gen:280`, with `0 < Cq → 0 < c →`) and `STExpIntIgL'` (band `STExpIntI'`, `:71`:
  the primed Ward premise `STExpWardIConclgL'` and the second conjunct `STExpIntQConclgL'`); the bridges `bandFM_STExpIntQConcl'` (iff) and `STExpIntI'_of_gL'` (one way: the generic Duhamel
  identity `STExpDuhEqgL` is eventual, D725).
* **Target 6.**  `expIntI_kernel_unifg` (band `expIntI_kernel_unif`, `:253`; W-b'): `(sum_res_2_NAL)` (`σ₁ = σ₂`) or `(sum_res_2)` (sum-zero family) with `n = 2` at the kernel coupling `gK`, the window
  `gK² ≤ lam²`, the decay class `lam² ≤ A gK²` and the ratio `(gK² + 1-v)/(gK² + 1-u) ≤ 2A` read from the comparison R1 and `STReg5I` at `sz.lam` through the toolkit `step34Gen_*`, the constant is
  `4 A²` (band `A = 1`: `4`); `expIntI_concl_of_kernelg` (`:356`) and `expIntI_sameg` (`:465`): the first conjunct of `STExpIntIgL'`.  The size-level `expIntI_ratio_le`, `expIntI_log_ratio` (`:80`, `:90`)
  are reused by name.
* **Target 7.**  `st6_caseI_coreg'` (= `T2508_CaseICoreg'`): `st6_caseI_coreg` (`Step6KitGen:601`) with `STExpWardIConclgL'`, `STExpIniIConclgL'`, `STExpIntQConclgL'` (the proof of band `ExpIntI:573-658`
  per carrier); the average is per flow, `hAvgU : STExpAvgUgL C μ s t` (V1L-C1).
* **Target 8.**  `ST_step6_caseI_of_pinsgL''` (→ `T2508_Step6IAvgUgL`: `STStep6IgL` with `STExpAvgUgL` on the `Concl` slot) and its corollary `ST_step6_caseI_of_pinsgL''_core` (the 16a core `STImproveCoregL`
  and W1 (iii) on `[s,t]` on the slot; `stExpAvgUgL_of_core`).  The band `ST_step6_caseI_of_pins''`, `ST_step6I_of_LW_Int` (`:573`, `:660`) read the global `STImproveExpAver`: they are re-derived in the last
  section with the global average recovered through 16b (`stImproveExpAver_of_gL`) and `st6_expAvgU_of_ping`, the integrated pin in its generic form `STExpIntIgL'` (the band `STExpIntI'` cannot
  be recovered from it: `STExpDuhEq` is `∀ n`, `STExpDuhEqgL` eventual).

Coupling (UBA-C1): `STReg5I` at `sz.lam`, kernels at `gK`; R1 (`∀ n, 0 ≤ gK n * lam n ∧ gK n ^ 2 ≤ lam n ^ 2 ∧ lam n ^ 2 ≤ Aof κm * gK n ^ 2`) enters only at the window, the decay class and the ratio of
`expIntI_kernel_unifg`.  No `def`, `abbrev` or `structure` is added beyond the two of target 5; helpers are `private` and prefixed `ExpIntIGen_`.  The private model-free lemmas of the band file
(`expIntI_window`, `expIntI_lift`, `expIntI_Bctl_nonneg`) are used by `open private`.  Ports: none from `../RBM1D`, `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private expIntI_window expIntI_lift expIntI_Bctl_nonneg from RBM3D.Induction.ExpIntI

open private ExpIntIIGen_drift_pi from RBM3D.Chain.ExpIntIIGen

open private Step5CasesGen_prec_mono from RBM3D.Chain.Step5CasesGen

open private Step6KitGen_K1_band Step6KitGen_KerFR1_band from RBM3D.Chain.Step6KitGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The primed vocabulary and its bridges (target 5) -/

/-- **Target 5, `STExpIntQConclgL'`** (band `STExpIntQConcl'`, `ExpIntI:56`): `STExpIntQConclgL` (`Step6Gen:280`) with `0 < Cq → 0 < c →`. -/
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

/-- **Target 5, `STExpIntIgL'`** (band `STExpIntI'`, `ExpIntI:71`): `STExpIntIgL` (`Step6Gen:375`) with the primed Ward premise and second conjunct. -/
def STExpIntIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftHiConclgL (mk sz z) (law sz) s t →
      STExpDriftDecayConclgL (mk sz z) (law sz) s t → STExpWardIConclgL' (mk sz z) (law sz) s t →
        STExpIntConclgL (mk sz z) (law sz) ∅ STSigSame s t ∧ STExpIntQConclgL' (mk sz z) (law sz) s t)

section Bridges

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

/-- Band `STExpIntQConcl'` is `STExpIntQConclgL'` at `bandFM`: through `bandStep2_Ugen` and `bandFM_STExpDuhEqQ`, nothing else (pattern `bandFM_STExpIntQConcl`, `Step6Gen:488`). -/
theorem bandFM_STExpIntQConcl' :
    STExpIntQConcl' sz E s t ↔ STExpIntQConclgL' (bandFM sz E) (Sizes.seqP sz) s t := by
  unfold STExpIntQConcl' STExpIntQConclgL'
  simp only [bandStep2_Ugen, bandFM_STExpDuhEqQ]
  exact Iff.rfl

end Bridges

/-- **The generic pin gives the band pin** (one way; pattern `STExpIntI_of_gL`, `Step6Gen:645`): the band Duhamel identity `STExpDuhEq` (`∀ n`) gives the eventual generic one, not conversely (D725). -/
theorem STExpIntI'_of_gL' (d : ℕ)
    (h : STExpIntIgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) : STExpIntI' d :=
  Step6Gen_ingR6_of_gL d STReg5I
    (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t →
      STExpWardIConcl' sz E s t → STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl' sz E s t) _
    (fun sz z s t H hDu hHi hDec hW =>
      let r := H (bandFM_STExpDuhEq_to_gL sz (STflowE z) s t hDu) ((bandFM_STExpDriftHiConcl sz (STflowE z) s t).1 hHi)
        ((bandFM_STExpDriftDecayConcl sz (STflowE z) s t).1 hDec) ((bandFM_STExpWardIConcl' sz (STflowE z) s t).1 hW)
      ⟨(bandFM_STExpIntConcl sz (STflowE z) s t ∅ STSigSame).2 r.1, (bandFM_STExpIntQConcl' sz (STflowE z) s t).2 r.2⟩) h

/-! ## 2. The kernel, uniformly in the end time (target 6, W-b') -/

section Kernel

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}

/-- **The kernel at one end-time sequence `u ∈ [s,t]`** (band `expIntI_kernel_seq`, `ExpIntI:165`; `(sum_res_2_NAL)` `3_5:1649` for `σ₁ = σ₂`, `(sum_res_2)` `3_5:1659` for a sum-zero family;
`n = 2`): the kernel pin at the window `STEKWinKgL sz gK s u` (`step34Gen_winK_of_cmp`, from the band window `expIntI_window` at `sz.lam` and `gK² ≤ lam²`), the decay class at `gK`
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

/-- **Target 6: the kernel, uniformly in the end time** (band `expIntI_kernel_unif`, `ExpIntI:253`; `(sum_res_2_NAL)` for `σ₁ = σ₂`, `(sum_res_2)` for a sum-zero family, `n = 2`, regime (i)):
for a deterministic family `𝒜_v` with the decay `(deccA0)` on `[s,t]`, a control `X ≥ N^{-b}` and `‖𝒜_v‖ ≺ X`, eventually for all `u ∈ [s_n,t_n]` and `v ∈ [s_n,u]`,
`‖𝒰_{v,u} 𝒜_v‖ ≤ N^τ · 4A² X_v` (`A = Aof κm`; the band constant `4` at `A = 1`).  The pin of the case is the hypothesis `hpin`: `STEKSumRes2NALgL` for `σ₁ = σ₂`, `STEKSumRes2gL` for a
sum-zero family.  For every time sequence `u` the pin is applied at the window `STEKWinKgL sz gK s u`; the lift over `u` is the failing-sequence argument (`expIntI_lift`). -/
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

/-! ## 3. The drift integral and the assembly (target 6) -/

section Assembly

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The drift integral at one size**, regime (i) (band `expIntI_drift_integral_le`, `ExpIntI:283`; `6:97`, `6:104`): a kernel bound `‖𝒰_{v,u} D_v‖_∞ ≤ M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` on `[s,u]`
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

/-- **`(iisuwjyys_exp)` closed in regime (i)** (band `expIntI_concl_of_kernel`, `ExpIntI:356`; `6:97`, `6:104`), `σ₁ = σ₂` (any class `P`, `A = ∅`): the Duhamel identity (`STExpDuhEqgL` at `A = ∅`, eventual),
the uniform kernel bound `‖𝒰_{v,u} D_v‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})`, the one-size integral bound (`M = N^{τ/2}`) and `log L ≺ 1` (`expIntII_log_eventually`, constant `6 = 3 · 2`) give
`‖f_u‖ ≤ N^τ F + N^τ T_u` for the control `F` of the initial term. -/
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

/-! ## 4. The `σ₁ = σ₂` conjunct (target 6) -/

section Same

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}

/-- **The first conjunct of `STExpIntIgL'` from the flow data** (band `expIntI_same`, `ExpIntI:465`; `6:97`: `(sum_res_2_NAL)`, `n = 2`, `σ₁ = σ₂`): the control `X_v = |1-v|⁻¹ (B_v^{11/5} + B_v^{5/2})` of the drift
(`STExpDriftHiConclgL`; the decay `STExpDriftDecayConclgL` of the deterministic tensors `D_v^σ` through `HighProbAt.nonempty`) in the kernel `expIntI_kernel_unifg` (loss `4A²`, absorbed by `4A² ≤ N^{τ/2}`) and
the assembly `expIntI_concl_of_kernelg`.  Lower control `X ≥ N^{-3}` from `W^{-d}B_{v,0} ≥ N⁻¹` (`expAvg_Bctl_ge`).  The kernel pin is `STEKSumRes2NALgL` at `Ker sz C gK κm` with the comparison R1; the premises `STLK`,
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

/-! ## 5. The regime-(i) core and the consumer (targets 7, 8; V1L-C1) -/

section Cores

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **Step 6, regime (i), per carrier, with the primed Ward, initial and integrated inputs** (target 7, `T2508_CaseICoreg'`; band `ST_step6_caseI_of_pins''`, `ExpIntI:573-658`; core `st6_caseI_coreg`,
`Step6KitGen:601`).  `σ₁ = σ₂`: the plain Duhamel (`hint.1`) with the initial term `hini.1`; `σ₁ ≠ σ₂`: for a mollifier family (`st6_mollifier_familyg`, `0 < Cq`, `0 < c`) the `𝒬`-Duhamel
(`hint.2`, identity `hDuQ`) with the initial term `hini.2` and `f_u = 𝒬_u f_u + (𝒫 f_u) ϑ_u`, `(𝒫 f_u) ϑ_u ≺ B³` from the primed Ward conclusion `hward`.  The average is per flow (`hAvgU`, V1L-C1). -/
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

section Consumer

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
  {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
  {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}

/-- **Step 6, regime (i), from its pins, the average per flow on the `Concl` slot** (target 8, `T2508_Step6IAvgUgL`; band `ST_step6_caseI_of_pins''`, `ExpIntI:573`; wrapper `ST_step6_caseI_of_pinsgL`,
`Step6KitGen:795`): the ingredient pins are `STExpLKLKHigL`, `LWtermEXPG`, the Duhamel families `STExpDuhamelZgL`, `STExpDuhamelQgL`, `STExpDriftDecaygL` and the primed `STExpWardIgL'`, `STExpIniIgL'`, `STExpIntIgL'`;
the constant `𝔠d` is the minimum of those of the five pins.  The average `(res_ELK_n=1)` is `STExpAvgUgL` along the flow on `[s,t]` (V1L-C1, §319 (3)): no `STImproveExpAvergL`, no global average. -/
theorem ST_step6_caseI_of_pinsgL'' (hμ : ∀ sz, IsProbabilityMeasure (law sz)) (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hRot : ∀ sz z, Step2EventsGen_Rot3 (mk sz z))
    (hK1 : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    (hLW : LWtermEXPG d law Flow mk T0) (hDu : STExpDuhamelZgL d law Flow mk) (hDuQ : STExpDuhamelQgL d law Flow mk)
    (hLK : STExpLKLKHigL d law Flow mk T0) (hDec : STExpDriftDecaygL d law Flow mk T0)
    (hWd : STExpWardIgL' d law Flow mk T0) (hIni : STExpIniIgL' d law Flow mk T0) (hInt : STExpIntIgL' d law Flow mk T0) :
    STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
      STExpAvgUgL (mk sz z) (law sz) s t → STStep6ConclgL (mk sz z) (law sz) s t) := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hDec hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := hIni hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ (min c₃ (min c₄ c₅))) :=
    lt_min hc₁ (lt_min hc₂ (lt_min hc₃ (lt_min hc₄ hc₅)))
  refine ⟨min c₁ (min c₂ (min c₃ (min c₄ c₅))), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5 hAvgU
  obtain ⟨κm, hκm, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, himm, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  have m : ∀ c', min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c' → STConStInd sz c' s t :=
    fun c' hcc => st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hm1 := m c₁ (min_le_left _ _)
  have hm2 := m c₂ ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 := m c₃ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm4 := m c₄ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hm5 := m c₅ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hHi := st6_hi_of_reg5I sz (by omega) hR
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec0 hExp hm1 hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LWg (mk sz z) (law sz) s t (hμ sz) hadm.2.2.1 (fun n => (hst n).le) hHi (hRot sz z)
    (fun u hsu hut => hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n))
      (fun n => (hut n).trans (htT n)) (STLocalEntrygL_of_STLocalEntryUgL_at (mk sz z) hsu hut hS2.1)
      (LWAvgLawgL_of_STAvgUgL_at (mk sz z) hsu hut (hK1 sz z) hs0 ht1 hS2.2)
      (STLmaxgL_of_STLmaxUgL_at (mk sz z) hsu hut hLmax) (STLKgL_of_STLKUgL_at (mk sz z) hsu hut hLKU)
      (STDecaygL_of_STGdecayWgL_at (mk sz z) hsu hut hS5))
  have hdec := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm2 hS2 hLmax hLKU hS5
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm3 hS2 hLmax hLKU hS5
  have hini := H₄ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm4 hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_ping hDu hκ hflow hs0 ht1
  have hint := H₅ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm5 hS2 hLmax hLKU hS5
  exact st6_caseI_coreg' (mk sz z) (law sz) hd h𝔡 hadm hs0 hst ht1 hR hlk hegt hdec hAvgU hward hini hduh
    (fun Cq c ϑ hϑ => st6_duhEqQ_of_ping hDuQ hκ hflow hs0 ht1 Cq c ϑ hϑ) hint

/-- **The corollary with the 16c inputs** (target 8, `T2508_Step6ICoreAvgUgL`): the average on `[s,t]` is `stExpAvgUgL_of_core` (16c, `ExpAvgGen:1416`) from the per-time core `STImproveCoregL` (16a) and
W1 (iii) at every `u ∈ [s,t]` on the `Concl` slot (V1-BA: TL1 `BATwistAvgLaw`); the same premises as `ST_step6_caseI_of_pinsgL''`. -/
theorem ST_step6_caseI_of_pinsgL''_core (hμ : ∀ sz, IsProbabilityMeasure (law sz)) (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hRot : ∀ sz z, Step2EventsGen_Rot3 (mk sz z))
    (hK1 : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    (hLW : LWtermEXPG d law Flow mk T0) (hDu : STExpDuhamelZgL d law Flow mk) (hDuQ : STExpDuhamelQgL d law Flow mk)
    (hLK : STExpLKLKHigL d law Flow mk T0) (hDec : STExpDriftDecaygL d law Flow mk T0)
    (hWd : STExpWardIgL' d law Flow mk T0) (hIni : STExpIniIgL' d law Flow mk T0) (hInt : STExpIntIgL' d law Flow mk T0)
    (hCore : STImproveCoregL d law Flow mk T0) :
    STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
      (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → ExpAvgGen_W1iii (mk sz z) (law sz) u) →
        STStep6ConclgL (mk sz z) (law sz) s t) := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hc', H⟩ := ST_step6_caseI_of_pinsgL'' hμ hFF hRot hK1 hLW hDu hDuQ hLK hDec hWd hIni hInt hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨c, hc, hc', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5 hiii
  obtain ⟨_, _, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  exact H 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5
    (stExpAvgUgL_of_core hCore hd hκ hε h𝔡 hflow (hμ sz) hadm.2.2.1 (hK1 sz z) hs0 hst htT ht1 hS2 hLKU hiii)

end Consumer

/-! ## 6. The band re-derivations (V1L-C1 (ii)) -/

/-- **Band `ST_step6_caseI_of_pins''` re-derived** (`ExpIntI:573`) from `ST_step6_caseI_of_pinsgL''` at the band tuple: the global average `STImproveExpAver` of the band statement is not read; the per-flow average is
recovered through 16b (`stImproveExpAvergL_of` with the band family texts `ExpAvgGen_band_W1fam`, `ExpAvgGen_band_W1iiiOfLW`) and `st6_expAvgU_of_ping`.  The band ingredient pins are read through their bridges
(`STExpLKLKHi_iff_gL`, `STExpDuhamelZ_to_gL`, `STExpDuhamelQ_to_gL`, `STExpDriftDecay_iff_gL`, `STExpWardI'_iff_gL'`, `STExpIniI'_iff_gL'`, `LWtermEXP_iff`); the integrated pin is the generic `STExpIntIgL'`
(the band `STExpIntI'` has the `∀ n` Duhamel premise and cannot be recovered from the eventual one: D725). -/
theorem ST_step6_caseI_of_pins''_gen_band (d : ℕ) (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hDu : STExpDuhamelZ d)
    (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI' d) (hIni : STExpIniI' d)
    (hInt : STExpIntIgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) : STStep6I d := by
  refine (STStep6I_iff_gL d).2 ?_
  intro hd κ ε 𝔡 hκ hε h𝔡
  have hAvg := stImproveExpAvergL_of (step5CasesGen_flowFacts_band d) (ExpAvgGen_band_W1fam d) (ExpAvgGen_band_W1iiiOfLW d)
  obtain ⟨c, hc, hc', H⟩ := ST_step6_caseI_of_pinsgL'' (fun sz => inferInstance) (step5CasesGen_flowFacts_band d)
    (fun sz z => Step2EventsGen_bandRot3 sz (STflowE z)) (fun sz z n τ a h0 h1 => Step6KitGen_K1_band sz (STflowE z) n τ a h0 h1)
    ((LWtermEXP_iff d).1 hLW) (STExpDuhamelZ_to_gL d hd hDu) (STExpDuhamelQ_to_gL d hd hDuQ) ((STExpLKLKHi_iff_gL d).1 hLK)
    ((STExpDriftDecay_iff_gL d).1 hDec) ((STExpWardI'_iff_gL' d).1 hWd) ((STExpIniI'_iff_gL' d).1 hIni) hInt hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨c, hc, hc', fun 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5 => ?_⟩
  obtain ⟨_, _, hFl⟩ := step5CasesGen_flowFacts_band d κ hκ
  obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  exact H 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5
    (st6_expAvgU_of_ping hAvg hd hκ hε h𝔡 hflow inferInstance hadm.2.2.1
      (fun n τ a h0 h1 => Step6KitGen_K1_band sz (STflowE z) n τ a h0 h1) hs0 hst htT (fun n => (htT n).trans_lt (hT0 n)) hS2 hLKU)

/-- **Band `ST_step6I_of_LW_Int` re-derived** (`ExpIntI:660`): every other regime-(i) pin by its merged proof (`stExpLKLKHi_holds`, `stExpDuhamelZ_holds`, `stExpDuhamelQ_holds`, `stExpDriftDecay_holds`,
`stExpWardI'_holds`, `stExpIniI'_holds`), the global average recovered as in `ST_step6_caseI_of_pins''_gen_band`; the integrated pin generic. -/
theorem ST_step6I_of_LW_Int_gen_band (d : ℕ) (hLW : LWtermEXP d)
    (hInt : STExpIntIgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) : STStep6I d :=
  ST_step6_caseI_of_pins''_gen_band d (stExpLKLKHi_holds d) hLW (stExpDuhamelZ_holds d) (stExpDuhamelQ_holds d)
    (stExpDriftDecay_holds d) (stExpWardI'_holds d) (stExpIniI'_holds d) hInt

/-! ## 7. Compiled nonempty instances at `d = 3` (regime (i) data of the band: `szB`, `zB`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/300`, `(s, t) = (7/8, 15/16)`)

`szB`: `L = 4`, `W_n = n + 4`, `lam = 1`; `1/16 = lam²/L² ≤ 1 - t = 1/16 ≤ 1 - s = 1/8 ≤ lam² = 1`.  Discharged: flow, times, regime, admissibility, probability law, flow facts, `(con_st_ind)` (`conStInd_const`),
the kernel pins `stek_sumRes2NALgL_band`, the band class `STEKBandKer` with R1 at `Aof = 1`, the Duhamel identity along `[7/8, 15/16]` (`stExpDuhamelZ_holds`), and the ingredient pins whose merged
proofs exist.  What stays a hypothesis is another gate's pin: `STExpDriftHiConclgL`, `STExpDriftDecayConclgL` (T2506 rows a), `LWtermEXPG` (LW-14), `STExpIntIgL'` (row b of this ticket). -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst RBM.Gauss.Step6Inst

/-- The average-on-the-slot shape at the band tuple read through `Step6Gen_ingR6_iff_congr` (instances only). -/
private theorem ExpIntIGen_avgU_iff (d : ℕ) :
    STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STStep6Concl sz E s t) ↔
      STIngR6gL d STReg5I (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
        (fun sz z s t => STExpAvgUgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t →
          STStep6ConclgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t) :=
  Step6Gen_ingR6_iff_congr d STReg5I _ _
    (fun sz z s t => imp_congr (bandFM_STExpAvgU sz (STflowE z) s t) (bandFM_STStep6Concl sz (STflowE z) s t))

/-- **Target 5**: the bridge of the conclusion at the data of regime (i) and the pin through `STExpIntI'_of_gL'` read at the data through the merged `inst_ing6_I`. -/
example (h : STExpIntQConcl' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STExpIntQConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  (bandFM_STExpIntQConcl' szB (STflowE zB) _ _).1 h

example (h : STExpIntIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t →
      STExpWardIConcl' sz E s t → STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl' sz E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ (STExpIntI'_of_gL' 3 h) szB_reg5I

/-- **Target 6, `expIntI_kernel_unifg`** at `(szB, zB, 7/8, 15/16)`, `σ = (+,+)`, `X ≡ 1` and the nonzero deterministic family `𝒜_v = 1_{a = 0}` (a delta tensor: decays since it vanishes off `0`, and
`‖𝒜_v‖ = 1 ≤ N^τ`): the pin `stek_sumRes2NALgL_band`, the band class with R1 at `Aof = 1` and `(con_st_ind)` are discharged; no hypothesis remains. -/
example (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) (v : ℝ), 7 / 8 ≤ v → v ≤ (u : ℝ) →
      ‖Step2Gen_UN (bandFM szB (STflowE zB)) n ![true, true] v (u : ℝ)
          (fun a : Fin 2 → Zd 3 (szB.L n) => if a = 0 then (1 : ℂ) else 0)‖ ≤ ((szB.size n : ℕ) : ℝ) ^ τ * (4 * 1 ^ 2 * 1) := by
  obtain ⟨κm, hκm, H⟩ := Step6KitGen_KerFR1_band (d := 3) (1 / 10) (by norm_num)
  obtain ⟨-, hKer, hg, hR1⟩ := H szB (1 / 10) (1 / 6) (1 / 10) zB flow_zB
  have hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, (7 / 8 : ℝ) ≤ v → v ≤ 15 / 16 →
      EKFastDecay (szB.lam n) v ((szB.W n : ℕ) : ℝ) ε' D (fun a : Fin 2 → Zd 3 (szB.L n) => if a = 0 then (1 : ℂ) else 0) := by
    intro ε' D hε' hD
    refine Filter.Eventually.of_forall fun n v _ _ a ha => ?_
    have hW : (0 : ℝ) < ((szB.W n : ℕ) : ℝ) := by exact_mod_cast szB.W_pos n
    by_cases h0 : a = 0
    · exfalso
      obtain ⟨i, j, hij⟩ := ha
      have hL : (1 : ℝ) ≤ ((szB.L n : ℕ) : ℝ) := by
        exact_mod_cast (by have := szB.three_le_L n; omega : 1 ≤ szB.L n)
      have hpos : 0 < ((szB.W n : ℕ) : ℝ) ^ ε' * ellT (szB.L n) (szB.lam n) v := mul_pos (Real.rpow_pos_of_pos hW _) (ellT_pos hL)
      rw [h0, Pi.zero_apply, Pi.zero_apply, sub_self, zdistD_zero] at hij
      push_cast at hij
      linarith
    · beta_reduce
      simp only [h0, ↓reduceIte, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, (7 / 8 : ℝ) ≤ v → v ≤ 15 / 16 → ((szB.size n : ℕ) : ℝ) ^ (-b) ≤ 1 :=
    ⟨0, Filter.Eventually.of_forall fun n v _ _ => by simp⟩
  have hbd : ∀ τ' : ℝ, 0 < τ' → ∀ᶠ n in atTop, ∀ v : ℝ, (7 / 8 : ℝ) ≤ v → v ≤ 15 / 16 →
      ‖fun a : Fin 2 → Zd 3 (szB.L n) => if a = 0 then (1 : ℂ) else 0‖ ≤ ((szB.size n : ℕ) : ℝ) ^ τ' * 1 := by
    intro τ' hτ'
    refine Filter.Eventually.of_forall fun n v _ _ => ?_
    have hN1 : (1 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) := by exact_mod_cast szB.one_le_size n
    have h1 : (1 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro a
    split_ifs
    · simpa using h1
    · simp only [norm_zero, mul_one]; positivity
  exact expIntI_kernel_unifg (Aof := fun _ => 1) (Ker := @STEKBandKer 3) (law := fun sz => Sizes.seqP sz) (by norm_num) hκm le_rfl
    (𝔠d := 1 / 300) (by norm_num) (by norm_num) szB_admissible (bandFM szB (STflowE zB)) szB.lam hKer hg hR1 inferInstance
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) szB_reg5I
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) ![true, true]
    (fun n v => fun a : Fin 2 → Zd 3 (szB.L n) => if a = 0 then (1 : ℂ) else 0) (fun _ _ => 1)
    (Or.inl ⟨rfl, stek_sumRes2NALgL_band 3⟩) hdec (fun _ _ => zero_le_one) hlow hbd τ hτ

/-- **Target 6, `expIntI_sameg`** at the same data: the first conjunct of `STExpIntIgL'`.  The Duhamel identity is the merged `stExpDuhamelZ_holds`; the drift bounds and the drift decay stay hypotheses. -/
example (hdr : STExpDriftHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hdd : STExpDriftDecayConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STExpIntConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigSame (fun _ => 7 / 8) (fun _ => 15 / 16) := by
  obtain ⟨κm, hκm, H⟩ := Step6KitGen_KerFR1_band (d := 3) (1 / 10) (by norm_num)
  obtain ⟨-, hKer, hg, hR1⟩ := H szB (1 / 10) (1 / 6) (1 / 10) zB flow_zB
  exact expIntI_sameg (Aof := fun _ => 1) (Ker := @STEKBandKer 3) (stek_sumRes2NALgL_band 3) (by norm_num) hκm le_rfl
    (𝔠d := 1 / 300) (by norm_num) (by norm_num) szB_admissible (bandFM szB (STflowE zB)) szB.lam hKer hg hR1 inferInstance
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) szB_reg5I
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num))
    (st6_duhEq_of_ping (STExpDuhamelZ_to_gL 3 (by norm_num) (stExpDuhamelZ_holds 3)) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
      (fun _ => by norm_num) (fun _ => by norm_num)) hdr hdd

/-- **Target 6, `expIntI_concl_of_kernelg`** at the same data: the uniform kernel bound of the drift stays a hypothesis (the drift bounds of T2506). -/
example (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) (v : ℝ),
      7 / 8 ≤ v → v ≤ (u : ℝ) → ∀ σ : Fin 2 → Bool, STSigSame σ →
        ‖Step2Gen_UN (bandFM szB (STflowE zB)) n σ v (u : ℝ)
            (fun b => STExpDriftg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n v σ b)‖ ≤
          ((szB.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (szB.Bctl n v ^ (11 / 5 : ℝ) + szB.Bctl n v ^ (5 / 2 : ℝ)))) :
    STExpIntConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigSame (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  expIntI_concl_of_kernelg (bandFM szB (STflowE zB)) (Sizes.seqP szB) inferInstance szB_tendsto (by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) szB_reg5I
    (st6_duhEq_of_ping (STExpDuhamelZ_to_gL 3 (by norm_num) (stExpDuhamelZ_holds 3)) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
      (fun _ => by norm_num) (fun _ => by norm_num)) STSigSame hker

/-- **Target 7, `st6_caseI_coreg'`** at the data of regime (i): the conclusions of the ingredient pins stay hypotheses (the primed Ward, initial and integrated conclusions among them); the administrative
facts and the Duhamel identities (`stExpDuhamelZ_holds`, `stExpDuhamelQ_holds`) are discharged. -/
example (hlk : STExpLKLKHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hegt : STExpEGtHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hdec : STExpDriftDecayConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hAvgU : STExpAvgUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hward : STExpAvgUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpWardIConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hini : STExpIniIConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hint : STExpDuhEqgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpDriftHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpDriftDecayConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpWardIConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpIntConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigSame (fun _ => 7 / 8) (fun _ => 15 / 16) ∧
        STExpIntQConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STStep6ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  st6_caseI_coreg' _ _ (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB_admissible (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) szB_reg5I hlk hegt hdec hAvgU hward hini
    (st6_duhEq_of_ping (STExpDuhamelZ_to_gL 3 (by norm_num) (stExpDuhamelZ_holds 3)) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
      (fun _ => by norm_num) (fun _ => by norm_num))
    (fun Cq c ϑ hϑ => st6_duhEqQ_of_ping (STExpDuhamelQ_to_gL 3 (by norm_num) (stExpDuhamelQ_holds 3)) (by norm_num : (0 : ℝ) < 1 / 10)
      flow_zB (fun _ => by norm_num) (fun _ => by norm_num) Cq c ϑ hϑ) hint

/-- **Target 8, `ST_step6_caseI_of_pinsgL''`** at the band tuple, read at the data of regime (i) through `inst_ing6_I`: every deterministic family premise is discharged (`hμ`, the flow facts
`step5CasesGen_flowFacts_band`, F7 `Step2EventsGen_bandRot3`, the one-loop datum) and so are the ingredient pins with merged band proofs (`stExpLKLKHi_holds`, `stExpDuhamelZ_holds`,
`stExpDuhamelQ_holds`, `stExpDriftDecay_holds`, `stExpWardI'_holds`, `stExpIniI'_holds`); `LWtermEXPG` and `STExpIntIgL'` stay hypotheses. -/
example (hLW : LWtermEXPG 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hInt : STExpIntIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STStep6Concl sz E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ ((ExpIntIGen_avgU_iff 3).2
    (ST_step6_caseI_of_pinsgL'' (fun sz => inferInstance) (step5CasesGen_flowFacts_band 3)
      (fun sz z => Step2EventsGen_bandRot3 sz (STflowE z)) (fun sz z n τ a h0 h1 => Step6KitGen_K1_band sz (STflowE z) n τ a h0 h1)
      hLW (STExpDuhamelZ_to_gL 3 (by norm_num) (stExpDuhamelZ_holds 3)) (STExpDuhamelQ_to_gL 3 (by norm_num) (stExpDuhamelQ_holds 3))
      ((STExpLKLKHi_iff_gL 3).1 (stExpLKLKHi_holds 3)) ((STExpDriftDecay_iff_gL 3).1 (stExpDriftDecay_holds 3))
      ((STExpWardI'_iff_gL' 3).1 (stExpWardI'_holds 3)) ((STExpIniI'_iff_gL' 3).1 (stExpIniI'_holds 3)) hInt)) szB_reg5I

/-- **Target 8, the corollary `ST_step6_caseI_of_pinsgL''_core`** applied at the data of regime (i): the per-time core `STImproveCoregL` is the merged `stImproveCoregL_of` at the band family texts, W1 (iii) at every
`u ∈ [7/8, 15/16]` is row 15 (`ExpAvgGen_band_W1iiiOfLW`) from `LWAvgLawgL` (the section of `STAvgUgL`); the premises of `STIngR6gL` at `s` and the pins `LWtermEXPG`, `STExpIntIgL'` stay hypotheses. -/
example (hLW : LWtermEXPG 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hInt : STExpIntIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hLK0 : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hDec0 : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hExp : STExp2gL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hS2 : STStep2CoregL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hLmax : STLmaxUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hLKU : STLKUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hS5 : STGdecayWgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) 0) :
    STStep6ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) := by
  obtain ⟨c, hc, hc', H⟩ := ST_step6_caseI_of_pinsgL''_core (fun sz => inferInstance) (step5CasesGen_flowFacts_band 3)
    (fun sz z => Step2EventsGen_bandRot3 sz (STflowE z)) (fun sz z n τ a h0 h1 => Step6KitGen_K1_band sz (STflowE z) n τ a h0 h1)
    hLW (STExpDuhamelZ_to_gL 3 (by norm_num) (stExpDuhamelZ_holds 3)) (STExpDuhamelQ_to_gL 3 (by norm_num) (stExpDuhamelQ_holds 3))
    ((STExpLKLKHi_iff_gL 3).1 (stExpLKLKHi_holds 3)) ((STExpDriftDecay_iff_gL 3).1 (stExpDriftDecay_holds 3))
    ((STExpWardI'_iff_gL' 3).1 (stExpWardI'_holds 3)) ((STExpIniI'_iff_gL' 3).1 (stExpIniI'_holds 3)) hInt
    (stImproveCoregL_of (step5CasesGen_flowFacts_band 3) (ExpAvgGen_band_W1fam 3)) (by norm_num) (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  refine H (1 / 6) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5I hLK0 hDec0 hExp
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) hc) hS2 hLmax hLKU hS5 ?_
  intro u hsu hut
  exact ExpAvgGen_band_W1iiiOfLW 3 (1 / 10) (1 / 10) (1 / 6) (1 / 10) szB zB (by norm_num) flow_zB u
    (fun n => (by norm_num : (0 : ℝ) ≤ 7 / 8).trans (hsu n)) (fun n => (hut n).trans (szB_flow_ht (by norm_num) n))
    (LWAvgLawgL_of_STAvgUgL_at (bandFM szB (STflowE zB)) hsu hut (fun n τ a h0 h1 => Step6KitGen_K1_band szB (STflowE zB) n τ a h0 h1)
      (fun _ => by norm_num) (fun _ => by norm_num) hS2.2)

/-- **The band re-derivations** `ST_step6_caseI_of_pins''_gen_band`, `ST_step6I_of_LW_Int_gen_band` at `d = 3`, read at the data of regime (i) through the merged `inst_step6I`: the global
average is recovered through 16b; `LWtermEXP` and the generic `STExpIntIgL'` stay hypotheses. -/
example (hLW : LWtermEXP 3)
    (hInt : STExpIntIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I (ST_step6I_of_LW_Int_gen_band 3 hLW hInt)

example (hLW : LWtermEXP 3)
    (hInt : STExpIntIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I (ST_step6_caseI_of_pins''_gen_band 3 (stExpLKLKHi_holds 3) hLW (stExpDuhamelZ_holds 3) (stExpDuhamelQ_holds 3)
    (stExpDriftDecay_holds 3) (stExpWardI'_holds 3) (stExpIniI'_holds 3) hInt)

end Instances

end RBM.BA

end
