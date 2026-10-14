/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpWardI
import RBM3D.Chain.B45Gen
import RBM3D.Chain.Step2IterGen
import RBM3D.Chain.CltGen

/-!
# The Ward terms of regime (i) over the carrier (BA-V row V1s2', ticket T2506 row b, targets 9-11)

Additive restatement of `Induction/ExpWardI.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the one kernel `Step2Gen_ThetaN C` and the
vocabulary and pins of `Chain/Step6Gen.lean`.  Paper: arXiv:2507.20274, `6:103-132` (`(eq:EPL-K)`, `(eq:boundELKQ1)`, `(eq:boundcommutator)`), Ward's identities
`3_5:1264` (`(eq:Ward_typeP)`), `3_5:1692-1705` (`(A4)`).

* **Target 9** (vocabulary).  `STExpWardIConclgL'` (band `STExpWardIConcl'`, `ExpWardI:321`: `STExpWardIConclgL`, `Step6Gen:244`, with `0 < Cq → 0 < c →`) and `STExpWardIgL'`
  (band `STExpWardI'`, `:339`); the bridges `bandFM_STExpWardIConcl'`, `STExpWardI'_iff_gL'` and `expWIg_concl_prime` (band `expWI_concl_prime`, `:428`).
* **Target 10.**  `expWI_Psum_eqg` (band `expWI_Psum_eq`, `:120`): Ward's identity at the last label in expectation, `B45_ward_fing` (`Chain/B45Gen:117`) under
  `ZeroModeGen_WardCls`, integrated: the loops of the carrier are measurable and bounded by `η_u^{-k}` from `CltRepg` and `κ ≤ Im m` (`η_u = (1-u) Im m = C.eta n u`);
  `expWI_Psum_precg` (band `expWI_Psum_prec`, `:143`) reads `STExpAvgUgL` and `𝒦^{(1)}_σ = m_σ` at both charges; the size lemmas `expWI_window`, `expWI_vth_le`
  (`:184`, `:206`) are reused by name.
* **Target 11.**  `expWI_coreg` (band `expWI_core`, `:411`: `STExpAvgUgL C μ s t → STExpWardIConclgL C μ s t`), `stExpWardIgL_of` (→ `STExpWardIgL`, `Step6Gen:346`),
  `stExpWardIgL'_of` (→ `STExpWardIgL'`); the band `stExpWardI_holds`, `stExpWardI'_holds` (`:441`, `:448`) are re-derived.  The commutator `[𝒬_u, Θ^{(2)}_{u,σ}]` of
  `(eq:boundcommutator)` reads the kernel `Step2Gen_ThetaN C` only through `B45_B4_leg` (`Chain/B45Gen:275`): constant row and column sums of `Step2Gen_thetaKer` and the
  bound `K₆/(1-t)` (the merged class `B45Gen_Facts`, BA discharge `baB45Gen_facts`); the band has `K₆ = 1` (`‖μ‖ = 1`).

Coupling (UBA-C1): `ℓ_u = ellT L lam u` at `sz.lam` and `Step2Gen_ThetaN C` inside the texts; no comparison R1.  No `def`, `abbrev` or `structure` is added beyond the two of
target 9; helpers are `private` and prefixed `ExpWardIGen_`.  The private band helper `Step6Gen_STthetaOp_eq` is used by `open private`.  Ports: none from `../RBM1D`, `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private Step6Gen_STthetaOp_eq from RBM3D.Chain.Step6Gen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The primed vocabulary and its bridges (target 9) -/

/-- **Target 9, `STExpWardIConclgL'`** (band `STExpWardIConcl'`, `ExpWardI:321`): `STExpWardIConclgL` (`Step6Gen:244`) with `0 < Cq → 0 < c →`. -/
def STExpWardIConclgL' {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ (Cq c : ℝ), 0 < Cq → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3) ∧
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ =>
        ‖STQop (d := d) (ϑ n) (q.1 : ℝ) (Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
            (fun c' => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c')) q.2.2 -
          Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (fun c' => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c')) q.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
          deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)

/-- **Target 9, `STExpWardIgL'`** (band `STExpWardI'`, `ExpWardI:339`): the average input is per flow (`STExpAvgUgL` on `[s,t]`, V1L-C1). -/
def STExpWardIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → STExpWardIConclgL' (mk sz z) (law sz) s t)

section Bridges

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

/-- Band `STExpWardIConcl'` is `STExpWardIConclgL'` at `bandFM`: through the bridge of `Θ^{(2)}` (`Step2Kern_ThetaN_band`), nothing else. -/
theorem bandFM_STExpWardIConcl' :
    STExpWardIConcl' sz E s t ↔ STExpWardIConclgL' (bandFM sz E) (Sizes.seqP sz) s t := by
  unfold STExpWardIConcl' STExpWardIConclgL'
  simp only [Step6Gen_STthetaOp_eq]
  exact Iff.rfl

end Bridges

/-- Band `STExpWardI'` is `STExpWardIgL'` at the band tuple `(seqP, STFlow, bandFM ∘ STflowE, lemT)`. -/
theorem STExpWardI'_iff_gL' (d : ℕ) :
    STExpWardI' d ↔ STExpWardIgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl' sz E s t) _
    (fun sz z s t => imp_congr (bandFM_STExpAvgU sz (STflowE z) s t) (bandFM_STExpWardIConcl' sz (STflowE z) s t))

/-- The unprimed conclusion implies the primed one (the extra hypotheses `0 < Cq`, `0 < c` are dropped; band `expWI_concl_prime`, `ExpWardI:428`). -/
theorem expWIg_concl_prime {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ)
    (h : STExpWardIConclgL C μ s t) : STExpWardIConclgL' C μ s t :=
  fun Cq c _ _ ϑ hϑ => h Cq c ϑ hϑ

/-! ## 2. Ward's identity at the last label in expectation (target 10) -/

section Ward

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- The loops of the carrier are integrable (measurable and bounded by `η_u^{-k}`, `CltRepg` and `κ ≤ Im m`; the generic `walk_measurable_Lloop`, `norm_Lloop_le`;
the case `k = 2` is `meanFarG_lenv_of_rep`, `Evolution/MeanFarG:68`). -/
private theorem ExpWardIGen_integrable_L [IsFiniteMeasure μ]
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) :
    Integrable (fun ω => C.L n u σ a ω) μ := by
  have hη : 0 < etaOf (C.m n) u := mul_pos (sub_pos.2 hu) (lt_of_lt_of_le hκ hm)
  have hmeas : Measurable fun ω : sz.SeqΩ => H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) =>
      Sizes.seqHflow (sz.withLam g') n u ω i j :=
    Measurable.of_eval_matrix _ fun i j => measurable_const.add (Sizes.measurable_seqHflow_entry (sz.withLam g') n u i j)
  refine Integrable.of_bound ?_ ((etaOf (C.m n) u)⁻¹ ^ (k + 1)) (Filter.Eventually.of_forall fun ω => ?_)
  · rw [funext fun ω => (hrep.2.2 n u ω).2 (k + 1) σ a]
    exact ((walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (C.m n) (E n) u) σ a).comp hmeas).aestronglyMeasurable
  · rw [(hrep.2.2 n u ω).2 (k + 1) σ a]
    exact norm_loopM_le d (sz.L n) (sz.W n)
      (((hrep.2.1 n).add (Sizes.seqHflow_isHermitian (sz.withLam g') n u ω)).submatrix _)
      hη (by rw [ztOf_im, abs_of_pos hη]) (n := k) σ a

/-- `𝔼(𝓛-𝒦)^{(k+1)} = 𝔼𝓛^{(k+1)} - 𝒦^{(k+1)}` (probability law; band `expWI_int_LK`, `ExpWardI:71`). -/
private theorem ExpWardIGen_int_LK (hμ : IsProbabilityMeasure μ)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) :
    ∫ ω, STLKtensorg C n u ω σ a ∂μ = (∫ ω, C.L n u σ a ω ∂μ) - C.K n u σ a := by
  have : IsProbabilityMeasure μ := hμ
  unfold STLKtensorg
  rw [integral_sub (ExpWardIGen_integrable_L C μ hrep hκ n hm hu σ a) (integrable_const _), integral_const]
  simp

private theorem ExpWardIGen_sgnCons (b : Bool) (σ : Fin 2 → Bool) :
    B45_sgnCons (m := 0) b σ = fun _ => b := by
  funext i; fin_cases i; simp [B45_sgnCons]

/-- Pathwise Ward at the last label for `σ₁ ≠ σ₂`, in terms of `𝒫` (band `expWI_pw`, `ExpWardI:92`; `B45_ward_fing` replaces `B45_ward_fin`). -/
private theorem ExpWardIGen_pw (hward : ZeroModeGen_WardCls sz C) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : sz.SeqΩ)
    (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a₁ : Zd d (sz.L n)) :
    STPsum (d := d) (STLKtensorg C n u ω σ) a₁ =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n u : ℂ))⁻¹ *
        (STLKtensorg C n u ω (fun _ : Fin 1 => true) (fun _ => a₁) -
          STLKtensorg C n u ω (fun _ : Fin 1 => false) (fun _ => a₁)) := by
  have hlast : σ (Fin.last (0 + 1)) = !σ 0 := by
    have : Fin.last (0 + 1) = (1 : Fin 2) := rfl
    rw [this]
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all
  have hw := B45_ward_fing C hward n hu0 hu1 ω (m := 0) σ hlast (fun _ => a₁)
  rw [B45_Psum_snoc]
  have hfil : Finset.univ.filter (fun a' : Fin (0 + 1) → Zd d (sz.L n) => a' 0 = a₁) = {fun _ => a₁} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext i; fin_cases i; exact h
    · intro h; rw [h]
  rw [hfil, Finset.sum_singleton, hw, ExpWardIGen_sgnCons, ExpWardIGen_sgnCons]

/-- **Ward's identity in expectation** (`(eq:EPL-K)` `6:105`, `(WI_calL)`, `(WI_calK)`; band `expWI_Psum_eq`, `ExpWardI:120`): for `σ₁ ≠ σ₂`,
`(𝒫 f_u)_{a₁} = (2iW^dη_u)⁻¹ ((𝔼𝓛^{(1)}_{+,a₁} - 𝒦^{(1)}_{+,a₁}) - (𝔼𝓛^{(1)}_{-,a₁} - 𝒦^{(1)}_{-,a₁}))`, `η_u = C.eta n u`.  The loops are integrable by `CltRepg`
and `κ ≤ Im m`; the Ward step is the one text `ZeroModeGen_WardCls`. -/
theorem expWI_Psum_eqg (hμ : IsProbabilityMeasure μ) (hward : ZeroModeGen_WardCls sz C)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a₁ : Zd d (sz.L n)) :
    STPsum (d := d) (fun b => STExpErrg C μ n u σ b) a₁ =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n u : ℂ))⁻¹ *
        (((∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a₁) ω ∂μ) - C.K n u (fun _ : Fin 1 => true) (fun _ => a₁)) -
          ((∫ ω, C.L n u (fun _ : Fin 1 => false) (fun _ => a₁) ω ∂μ) - C.K n u (fun _ : Fin 1 => false) (fun _ => a₁))) := by
  have : IsProbabilityMeasure μ := hμ
  have hint : ∀ (b : Fin 2 → Zd d (sz.L n)), STExpErrg C μ n u σ b = ∫ ω, STLKtensorg C n u ω σ b ∂μ := fun b =>
    (ExpWardIGen_int_LK C μ hμ hrep hκ n hm hu1 σ b).symm
  have hI : ∀ {k : ℕ} (σ' : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)),
      Integrable (fun ω => STLKtensorg C n u ω σ' a) μ := fun σ' a =>
    (ExpWardIGen_integrable_L C μ hrep hκ n hm hu1 σ' a).sub (integrable_const _)
  have hP : STPsum (d := d) (fun b => STExpErrg C μ n u σ b) a₁ = ∫ ω, STPsum (d := d) (STLKtensorg C n u ω σ) a₁ ∂μ := by
    unfold STPsum
    rw [integral_finsetSum _ (fun a _ => hI σ a)]
    exact Finset.sum_congr rfl fun a _ => hint a
  rw [hP]
  simp only [ExpWardIGen_pw C hward n hu0 hu1 _ σ hσ a₁]
  rw [integral_const_mul, integral_sub (hI (fun _ : Fin 1 => true) (fun _ => a₁)) (hI (fun _ : Fin 1 => false) (fun _ => a₁))]
  congr 2
  · exact ExpWardIGen_int_LK C μ hμ hrep hκ n hm hu1 _ _
  · exact ExpWardIGen_int_LK C μ hμ hrep hκ n hm hu1 _ _

/-- **`‖𝒫 f_u‖_∞ ≺ (W^dη_u)⁻¹ (W^{-d}B_{u,0})²`** uniformly in `u ∈ [s,t]`, `σ₁ ≠ σ₂`, `a₁` (band `expWI_Psum_prec`, `ExpWardI:143`): Ward's identity in expectation
(`expWI_Psum_eqg`) with `‖(2iW^dη)⁻¹‖ = (2W^dη)⁻¹`, `𝒦^{(1)}_σ = m_σ` for both charges (`hK1`, eventually) and `(res_ELK_n=1)` (`STExpAvgUgL`) for both signs.  No regime,
no mollifier. -/
theorem expWI_Psum_precg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) (hward : ZeroModeGen_WardCls sz C)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (hmn : ∀ n, κ ≤ (C.m n).im)
    (heta : ∀ (n : ℕ) (t : ℝ), C.eta n t = (1 - t) * (C.m n).im)
    (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then C.m n else (starRingEnd ℂ) (C.m n))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hAvg : STExpAvgUgL C μ s t) :
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
      (fun n q _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 2) := by
  refine (st6_prec_det_iffg sz μ hμ hsz _ _).2 fun τ hτ => ?_
  have hA := (st6_prec_det_iffg sz μ hμ hsz _ _).1 hAvg τ hτ
  filter_upwards [hA, hK1] with n hn hk1
  rintro ⟨⟨u, hu⟩, ⟨σ, hσ⟩, a⟩
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
  have hη : 0 < C.eta n u := by
    rw [heta n u]; exact mul_pos (by linarith) (lt_of_lt_of_le hκ (hmn n))
  have h1 := hn ⟨⟨u, hu⟩, true, a⟩
  have h2 := hn ⟨⟨u, hu⟩, false, a⟩
  simp only [↓reduceIte, Bool.false_eq_true] at h1 h2 ⊢
  rw [expWI_Psum_eqg C μ hμ hward hrep hκ n (hmn n) hu0 hu1 σ hσ a, norm_mul, B45_norm_kappag sz n hη,
    hk1 u hu0 hu1 true a, hk1 u hu0 hu1 false a]
  simp only [↓reduceIte, Bool.false_eq_true]
  have hd0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d * C.eta n u := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact mul_pos (by positivity) hη
  have hsub := norm_sub_le ((∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω ∂μ) - C.m n)
    ((∫ ω, C.L n u (fun _ : Fin 1 => false) (fun _ => a) ω ∂μ) - (starRingEnd ℂ) (C.m n))
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u))⁻¹ * ‖_ - _‖
      ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u))⁻¹ *
        (((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u) ^ 2 + ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsub.trans (add_le_add h1 h2)) (by positivity)
    _ = _ := by rw [mul_inv]; field_simp; ring

/-! ## 3. The deterministic bound at one `(n, u, σ)` (target 11) -/

/-- `(W^dη_u)⁻¹ ℓ_u^{-d} ≤ 2Γ W^{-d}B_{u,0}`, `Γ = κm⁻¹ ≥ (Im m)⁻¹` (`B45_scale`: `(ℓ_u^d (1-u))⁻¹ ≤ 2 B_{u,0}` for every `u < 1`, `d ≥ 2`; `η_u = C.eta n u = (1-u) Im m`,
`Im m ≥ κm`); band `expWI_scale` (`ExpWardI:224`), `Γ = 2/√(2κ)` there. -/
private theorem ExpWardIGen_scale (hd : 2 ≤ d) (n : ℕ) {u κm : ℝ} (hκm : 0 < κm) (hmn : κm ≤ (C.m n).im)
    (heta : C.eta n u = (1 - u) * (C.m n).im) (hu1 : u < 1) (hg : 0 < sz.lam n) :
    (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ≤ 2 * κm⁻¹ * sz.Bctl n u := by
  have hv : 0 < 1 - u := by linarith
  have hsc := B45_scale (d := d) (L := sz.L n) hd (by have := sz.three_le_L n; omega) hg hu1
  have h1 : (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((C.m n).im)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹) := by
    rw [heta]
    simp only [mul_inv]
    ring
  rw [h1]
  have hΓ : ((C.m n).im)⁻¹ ≤ κm⁻¹ := inv_anti₀ hκm hmn
  have hΓ0 : 0 ≤ κm⁻¹ := by positivity
  unfold Sizes.Bctl
  have hpos : 0 ≤ (ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹ := by
    have := ellT_pos (L := sz.L n) (g := sz.lam n) (t := u) (by
      have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n))
    positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((C.m n).im)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * κm⁻¹ * (2 * Bparam d (sz.L n) (sz.lam n) u 0) := by
        gcongr
    _ = 2 * κm⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0) := by ring

/-- **The two Ward bounds at one point** (band `expWI_pt`, `ExpWardI:257`).  For `σ₁ ≠ σ₂`, `‖𝒫 f_u‖_∞ ≤ Y (W^dη_u)⁻¹ (W^{-d}B_{u,0})²`, a mollifier with `‖ϑ_u‖_∞ ≤ K ℓ_u^{-d}` and
`‖∂_uϑ_u‖_∞ ≤ Cq (1-u)⁻¹ℓ_u^{-d}`, and the scale `(W^dη_u)⁻¹ℓ_u^{-d} ≤ 2Γ W^{-d}B_{u,0}`: `(eq:EPL-K)`: `‖(𝒫f_u)_{a₁} ϑ_{u,a}‖ ≤ 2ΓK Y B³`;
`(eq:boundcommutator)` + `(eq:boundELKQ1)`: `‖[𝒬_u, Θ^{(2)}_{u,σ}] f_u‖ + ‖(𝒫f_u)_{a₁} ∂_uϑ_u‖ ≤ (1-u)⁻¹ 2Γ(4K₆K + Cq) Y B³` (`B45_B4_leg` at `m = 1`: row and column
sums of `Step2Gen_thetaKer C` at most `K₆/(1-u)`, constant column sums). -/
private theorem ExpWardIGen_pt (n : ℕ) {u K₆ : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {Cq K Γ Y : ℝ} (hY : 0 ≤ Y) (hΓ : 0 ≤ Γ)
    (hK : 0 ≤ K) (hC : 0 ≤ Cq) (hK₆ : 0 ≤ K₆) (hker : ZeroModeGen_KerSums C n)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ}
    (hvs : ∀ a, ‖ϑ u a‖ ≤ K * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹))
    (hdv : ∀ a, ‖deriv (fun τ => ϑ τ a) u‖ ≤ Cq * (1 - u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹))
    (hsc : (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ≤ 2 * Γ * sz.Bctl n u)
    (hη : 0 < C.eta n u) (σ : Fin 2 → Bool)
    (hP : ∀ b₁, ‖STPsum (d := d) (fun b => STExpErrg C μ n u σ b) b₁‖ ≤
      Y * ((((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ * (sz.Bctl n u) ^ 2))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖STPsum (d := d) (fun b => STExpErrg C μ n u σ b) (a 0) * ϑ u a‖ ≤ Y * (2 * Γ * K) * (sz.Bctl n u) ^ 3 ∧
    ‖STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (fun c => STExpErrg C μ n u σ c)) a -
        Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (fun c => STExpErrg C μ n u σ c)) a‖ +
      ‖STPsum (d := d) (fun b => STExpErrg C μ n u σ b) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
      (1 - u)⁻¹ * (Y * (2 * Γ * (4 * K₆ * K + Cq)) * (sz.Bctl n u) ^ 3) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hP0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ := by positivity
  have hB0 : 0 ≤ sz.Bctl n u := (STBctl_pos sz n hu1).le
  have hv0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have hLz : 0 ≤ ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) := by
    have := ellT_pos (L := sz.L n) (g := sz.lam n) (t := u) (by
      have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n))
    positivity
  set P0 : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ with hP0def
  set Lz : ℝ := ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) with hLzdef
  set B : ℝ := sz.Bctl n u with hBdef
  set Pa : ℝ := ‖STPsum (d := d) (fun b => STExpErrg C μ n u σ b) (a 0)‖ with hPa
  have hPa' : Pa ≤ Y * (P0 * B ^ 2) := hP (a 0)
  have hPi0 : 0 ≤ Y * (P0 * B ^ 2) := by positivity
  constructor
  · calc ‖STPsum (d := d) (fun b => STExpErrg C μ n u σ b) (a 0) * ϑ u a‖ = Pa * ‖ϑ u a‖ := norm_mul _ _
      _ ≤ (Y * (P0 * B ^ 2)) * (K * Lz) := mul_le_mul hPa' (hvs a) (norm_nonneg _) hPi0
      _ = Y * K * B ^ 2 * (P0 * Lz) := by ring
      _ ≤ Y * K * B ^ 2 * (2 * Γ * B) := by gcongr
      _ = Y * (2 * Γ * K) * B ^ 3 := by ring
  · have hB4 := B45_B4_leg C n hker hrow hcol (m := 1) σ hu0 hu1 ϑ (fun b => STExpErrg C μ n u σ b)
      (Pi := Y * (P0 * B ^ 2)) (vs := K * Lz) hP hvs a
    have h2 : ‖STPsum (d := d) (fun b => STExpErrg C μ n u σ b) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
        (Y * (P0 * B ^ 2)) * (Cq * (1 - u)⁻¹ * Lz) := by
      rw [norm_mul]
      exact mul_le_mul hPa' (hdv a) (norm_nonneg _) hPi0
    have hn2 : 2 * (((1 + 1 : ℕ) : ℝ)) = 4 := by norm_num
    rw [hn2] at hB4
    calc _ ≤ 4 * (K₆ / (1 - u)) * ((Y * (P0 * B ^ 2)) * (K * Lz)) + (Y * (P0 * B ^ 2)) * (Cq * (1 - u)⁻¹ * Lz) := by
          linarith
      _ = (1 - u)⁻¹ * (Y * (4 * K₆ * K + Cq) * B ^ 2 * (P0 * Lz)) := by rw [div_eq_mul_inv]; ring
      _ ≤ (1 - u)⁻¹ * (Y * (4 * K₆ * K + Cq) * B ^ 2 * (2 * Γ * B)) := by gcongr
      _ = (1 - u)⁻¹ * (Y * (2 * Γ * (4 * K₆ * K + Cq)) * B ^ 3) := by ring

/-- `K_c = Cq e^{|c|d/2} + 2Cq/d` (the mollifier constant of `expWI_vth_le`). -/
private def ExpWardIGen_Kc (d : ℕ) (Cq c : ℝ) : ℝ := Cq * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * Cq / (d : ℝ)

/-- The two bounds at one index `(n, q)` of regime (i) (band `expWI_step`, `ExpWardI:352`): the inputs are the Ward bound `‖𝒫 f_u‖ ≤ N^{τ/2} (W^dη_u)⁻¹B²`
(`expWI_Psum_precg`), the window, the mollifier at size `n`, and the constants `2Γ K_c`, `2Γ(4K₆K_c + Cq) ≤ N^{τ/2}`, `Γ = κm⁻¹`. -/
private theorem ExpWardIGen_step (hd : 3 ≤ d) {κm K₆ : ℝ} (hκm : 0 < κm) (hK₆ : 0 ≤ K₆) (n : ℕ) (hmn : κm ≤ (C.m n).im)
    (heta : ∀ t : ℝ, C.eta n t = (1 - t) * (C.m n).im) (hker : ZeroModeGen_KerSums C n)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t) {Cq c τ : ℝ} (hτ : 0 < τ)
    (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) (hl : 0 < sz.lam n) (hm : STMollifierProps (d := d) (sz.lam n) Cq c ϑ)
    (hK1 : 2 * κm⁻¹ * ExpWardIGen_Kc d Cq c ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hK2 : 2 * κm⁻¹ * (4 * K₆ * ExpWardIGen_Kc d Cq c + Cq) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hn : ∀ v : TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n),
      ‖STPsum (d := d) (fun b => STExpErrg C μ n (v.1 : ℝ) v.2.1.1 b) v.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.W n : ℕ) : ℝ) ^ d * C.eta n (v.1 : ℝ))⁻¹ * (sz.Bctl n (v.1 : ℝ)) ^ 2))
    (q : TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) :
    ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) * ϑ (q.1 : ℝ) q.2.2‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n (q.1 : ℝ)) ^ 3 ∧
    ‖STQop (d := d) ϑ (q.1 : ℝ) (Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
        (fun c => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c)) q.2.2 -
      Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
        (STQop (d := d) ϑ (q.1 : ℝ) (fun c => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c)) q.2.2‖ +
    ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
      deriv (fun τ => ϑ τ q.2.2) (q.1 : ℝ)‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3) := by
  obtain ⟨⟨u, hu⟩, ⟨σ, hσ⟩, a⟩ := q
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
  have hη : 0 < C.eta n u := by
    rw [heta u]; exact mul_pos (by linarith) (lt_of_lt_of_le hκm hmn)
  have hL3 := sz.three_le_L n
  have hC := B45_C_nonneg hL3 hl hm
  have hKc : 0 ≤ ExpWardIGen_Kc d Cq c := by unfold ExpWardIGen_Kc; positivity
  have hΓ : 0 ≤ κm⁻¹ := by positivity
  obtain ⟨hx1, hxL⟩ := expWI_window sz s t hR n u hu.1 hu.2 hl
  have hvs := fun b => expWI_vth_le ϑ (by omega) hL3 hl hm u hu0 hu1 hx1 hxL b
  have hdv : ∀ b, ‖deriv (fun τ => ϑ τ b) u‖ ≤ Cq * (1 - u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) := fun b => by
    simpa using hm.2.2.2 u hu0 hu1 b
  have hsc := ExpWardIGen_scale C (by omega : 2 ≤ d) n hκm hmn (heta u) hu1 hl
  have hY : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hP : ∀ b₁, ‖STPsum (d := d) (fun b => STExpErrg C μ n u σ b) b₁‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
        ((((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ * (sz.Bctl n u) ^ 2) :=
    fun b₁ => hn ⟨⟨u, hu⟩, ⟨σ, hσ⟩, b₁⟩
  obtain ⟨h1, h2⟩ := ExpWardIGen_pt C μ n hu0 hu1 hY hΓ hKc hC hK₆ hker hrow hcol hvs hdv hsc hη σ hP a
  have hB3 : 0 ≤ (sz.Bctl n u) ^ 3 := by have := (STBctl_pos sz n hu1).le; positivity
  have hv0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have hYY : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ :=
    UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ
  constructor
  · calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (2 * κm⁻¹ * ExpWardIGen_Kc d Cq c) * (sz.Bctl n u) ^ 3 := h1
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 3 := by gcongr
      _ = _ := by rw [hYY]
  · calc _ ≤ (1 - u)⁻¹ * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (2 * κm⁻¹ * (4 * K₆ * ExpWardIGen_Kc d Cq c + Cq)) *
          (sz.Bctl n u) ^ 3) := h2
      _ ≤ (1 - u)⁻¹ * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 3) := by
          gcongr
      _ = _ := by rw [hYY]; ring

/-- **The Ward terms of regime (i), every `Cq, c`** (`(eq:EPL-K)`, `(eq:boundELKQ1)`, `(eq:boundcommutator)`, `6:104-132`; band `expWI_core`, `ExpWardI:411`) at one carrier and
one law: from `STReg5I`, `(res_ELK_n=1)` (`STExpAvgUgL`), the Ward text, `𝒦^{(1)} = m` and the kernel facts.  The data of the carrier: `κm ≤ Im m`, `η = (1-t) Im m` (flow facts),
`CltRepg` (integrability of the loops) and `K₆` (rows and columns of `Step2Gen_thetaKer`, `ZeroModeGen_KerSums`; the class `B45Gen_Facts`). -/
theorem expWI_coreg (hd : 3 ≤ d) {κm 𝔠 𝔡 K₆ : ℝ} (hκm : 0 < κm) (hK₆ : 0 ≤ K₆) (hadm : sz.Admissible 𝔠 𝔡)
    (hμ : IsProbabilityMeasure μ)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) (hmn : ∀ n, κm ≤ (C.m n).im) (heta : ∀ (n : ℕ) (t : ℝ), C.eta n t = (1 - t) * (C.m n).im)
    (hward : ZeroModeGen_WardCls sz C)
    (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then C.m n else (starRingEnd ℂ) (C.m n))
    (hker : ∀ n, ZeroModeGen_KerSums C n)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t)
    (hAvg : STExpAvgUgL C μ s t) : STExpWardIConclgL C μ s t := by
  intro Cq c ϑ hϑ
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hPrec := expWI_Psum_precg C μ hμ hsz hward hrep hκm hmn heta hK1 hs0 ht1 hAvg
  have hlam := st6_lam_pos sz hadm.2.2.2.2
  refine ⟨(st6_prec_det_iffg sz μ hμ hsz _ _).2 fun τ hτ => ?_, (st6_prec_det_iffg sz μ hμ hsz _ _).2 fun τ hτ => ?_⟩
  all_goals
    have hA := (st6_prec_det_iffg sz μ hμ hsz _ _).1 hPrec (τ / 2) (half_pos hτ)
    filter_upwards [hA, hlam, hϑ, hK1, (tendsto_size sz hsz).eventually
      (eventually_le_rpow (2 * κm⁻¹ * ExpWardIGen_Kc d Cq c) (half_pos hτ)),
      (tendsto_size sz hsz).eventually
      (eventually_le_rpow (2 * κm⁻¹ * (4 * K₆ * ExpWardIGen_Kc d Cq c + Cq)) (half_pos hτ))] with n hn hl hm _ hK1' hK2' q
  · exact (ExpWardIGen_step C μ hd hκm hK₆ n (hmn n) (heta n) (hker n) (hrow n) (hcol n) hs0 ht1 hR hτ (ϑ n) hl hm hK1' hK2' hn q).1
  · exact (ExpWardIGen_step C μ hd hκm hK₆ n (hmn n) (heta n) (hker n) (hrow n) (hcol n) hs0 ht1 hR hτ (ϑ n) hl hm hK1' hK2' hn q).2

end Ward

/-! ## 4. The pins (target 11) -/

/-- **The pin `STExpWardIgL`** (`Step6Gen:346`; band `stExpWardI_holds`, `ExpWardI:441`) from the family premises: probability law (row 1), flow facts (row 3), `∃ H₀ g' E, CltRepg`
along the flow (row 9; the loops are integrable), the class `B45Gen_Facts` (row 19: the Ward text `ZeroModeGen_WardCls` and the kernel sums; BA `baB45Gen_facts`), and `𝒦^{(1)}_σ = m_σ`
at both charges along the flow (row 19; BA `baKsol_oneLoop`).  The constant `𝔠_d = 1/100`; no premise of `STIngR6gL` beyond `STReg5I` and `STExpAvgUgL` is used. -/
theorem stExpWardIgL_of {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hμ : ∀ sz, IsProbabilityMeasure (law sz))
    (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hRep : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E)
    (hB45 : B45Gen_Facts d Flow mk)
    (hK1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
        (mk sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n)) :
    STExpWardIgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR _ _ _ _ _ _ _ _ hAvg
  obtain ⟨κm, hκm, H⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, hmn, heta⟩ := H sz ε 𝔠 𝔡 z hflow
  obtain ⟨K₆, hK₆, G⟩ := hB45 κ hκ
  obtain ⟨hward, -, -, hker, hsums⟩ := G sz ε 𝔠 𝔡 z hflow
  obtain ⟨H₀, g', E, hrep⟩ := hRep sz κ ε 𝔠 𝔡 z hκ hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  exact expWI_coreg (mk sz z) (law sz) hd hκm hK₆.le hadm (hμ sz) hrep hmn heta hward (hK1 sz κ ε 𝔠 𝔡 z hκ hflow) hker
    (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).1) (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).2) hs0 hst ht1 hR hAvg

/-- **The primed pin `STExpWardIgL'`** (band `stExpWardI'_holds`, `ExpWardI:448`), from `stExpWardIgL_of` by `expWIg_concl_prime`; same premises. -/
theorem stExpWardIgL'_of {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hμ : ∀ sz, IsProbabilityMeasure (law sz))
    (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hRep : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E)
    (hB45 : B45Gen_Facts d Flow mk)
    (hK1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
        (mk sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n)) :
    STExpWardIgL' d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨𝔠d, h0, h1, H⟩ := stExpWardIgL_of hμ hFF hRep hB45 hK1 hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨𝔠d, h0, h1, fun 𝔠 sz z hflow s t hs0 hst htT hR hLK hDec hExp hcon hS2 hLmax hLKU hS5 hAvg =>
    expWIg_concl_prime _ _ s t (H 𝔠 sz z hflow s t hs0 hst htT hR hLK hDec hExp hcon hS2 hLmax hLKU hS5 hAvg)⟩

/-! ## 5. The band re-derivations -/

/-- **Band `stExpWardI_holds` re-derived** (`ExpWardI:441`) from `stExpWardIgL_of` through `STExpWardI_iff_gL` (`Step6Gen`): the premises at the band tuple are the merged
`step5CasesGen_flowFacts_band`, `cltRepg_band`, `b45Gen_facts_band` and `step2IterGen_oneLoop_band`. -/
theorem stExpWardI_gen_band (d : ℕ) : STExpWardI d :=
  (STExpWardI_iff_gL d).2 (stExpWardIgL_of (fun sz => inferInstance) (step5CasesGen_flowFacts_band d)
    (fun sz κ ε 𝔠 𝔡 z _ _ => ⟨fun _ => 0, sz.lam, STflowE z, cltRepg_band sz (STflowE z)⟩) (b45Gen_facts_band d)
    (fun sz κ ε 𝔠 𝔡 z _ _ => (step2IterGen_oneLoop_band sz (STflowE z)).1))

/-- **Band `stExpWardI'_holds` re-derived** (`ExpWardI:448`) from `stExpWardIgL'_of` through `STExpWardI'_iff_gL'`. -/
theorem stExpWardI'_gen_band (d : ℕ) : STExpWardI' d :=
  (STExpWardI'_iff_gL' d).2 (stExpWardIgL'_of (fun sz => inferInstance) (step5CasesGen_flowFacts_band d)
    (fun sz κ ε 𝔠 𝔡 z _ _ => ⟨fun _ => 0, sz.lam, STflowE z, cltRepg_band sz (STflowE z)⟩) (b45Gen_facts_band d)
    (fun sz κ ε 𝔠 𝔡 z _ _ => (step2IterGen_oneLoop_band sz (STflowE z)).1))

/-! ## 6. Compiled nonempty instances at `d = 3` (regime (i) data of the band: `szB`, `zB`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `(s, t) = (7/8, 15/16)`)

`szB`: `L = 4`, `W_n = n + 4`, `lam = 1`; `1/16 = lam²/L² ≤ 1 - t = 1/16 ≤ 1 - s = 1/8 ≤ lam² = 1`.  Discharged: flow, times, regime, admissibility, probability law, flow facts,
`CltRepg` (`cltRepg_band`, `H₀ = 0`, `g' = lam`), the class `B45Gen_Facts` (`b45Gen_facts_band`, `K₆ = 1` there), `𝒦^{(1)}_σ = m_σ` at both charges
(`step2IterGen_oneLoop_band`).  What stays a hypothesis is `STExpAvgUgL` at the instance (`(res_ELK_n=1)`, the conclusion of `STImproveExpAvergL`, row c of T2502). -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst RBM.Gauss.Step6Inst

/-- The kernel facts of the band flow `zB` at `K₆`: the Ward text, constant column sums and the row and column bounds of `Step2Gen_thetaKer` (`b45Gen_facts_band`). -/
private theorem ExpWardIGen_bandData :
    ∃ K₆ : ℝ, 0 < K₆ ∧ ZeroModeGen_WardCls szB (bandFM szB (STflowE zB)) ∧
      (∀ n, ZeroModeGen_KerSums (bandFM szB (STflowE zB)) n) ∧
      (∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd 3 (szB.L n),
        ∑ b : Zd 3 (szB.L n), ‖Step2Gen_thetaKer (bandFM szB (STflowE zB)) n σ σ' t a b‖ ≤ K₆ / (1 - t)) ∧
      (∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd 3 (szB.L n),
        ‖∑ a : Zd 3 (szB.L n), Step2Gen_thetaKer (bandFM szB (STflowE zB)) n σ σ' t a b‖ ≤ K₆ / (1 - t)) := by
  obtain ⟨K₆, hK₆, G⟩ := b45Gen_facts_band 3 (1 / 10) (by norm_num)
  obtain ⟨hward, -, -, hker, hsums⟩ := G szB (1 / 10) (1 / 6) (1 / 10) zB flow_zB
  exact ⟨K₆, hK₆, hward, hker, fun n σ σ' t h0 h1 a => (hsums n σ σ' t h0 h1).1 a,
    fun n σ σ' t h0 h1 b => (hsums n σ σ' t h0 h1).2 b⟩

/-- **Target 9**: the bridge of the conclusion and the bridge of the pin at the band data. -/
example (h : STExpWardIConcl' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STExpWardIConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  (bandFM_STExpWardIConcl' szB (STflowE zB) _ _).1 h

example (h : STExpWardIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STExpWardIConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  expWIg_concl_prime _ _ _ _ h

example (h : STExpWardIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl' sz E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ ((STExpWardI'_iff_gL' 3).2 h) szB_reg5I

/-- **Target 10, `expWI_Psum_eqg`** at `szB`, `n = 0`, `u = 7/8`, `σ = (+, -)`, `a₁ = 0` (band carrier at `zB`, law `seqP szB`): Ward's identity in expectation; every hypothesis
is discharged. -/
example :
    STPsum (d := 3) (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) 0 (7 / 8) ![true, false] b)
        (0 : Zd 3 (szB.L 0)) =
      (2 * Complex.I * ((szB.W 0 : ℕ) : ℂ) ^ 3 * ((bandFM szB (STflowE zB)).eta 0 (7 / 8) : ℂ))⁻¹ *
        (((∫ ω, (bandFM szB (STflowE zB)).L 0 (7 / 8) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(Sizes.seqP szB)) -
            (bandFM szB (STflowE zB)).K 0 (7 / 8) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (szB.L 0)))) -
          ((∫ ω, (bandFM szB (STflowE zB)).L 0 (7 / 8) (fun _ : Fin 1 => false) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(Sizes.seqP szB)) -
            (bandFM szB (STflowE zB)).K 0 (7 / 8) (fun _ : Fin 1 => false) (fun _ => (0 : Zd 3 (szB.L 0))))) := by
  obtain ⟨K₆, hK₆, hward, -⟩ := ExpWardIGen_bandData
  exact expWI_Psum_eqg (bandFM szB (STflowE zB)) (Sizes.seqP szB) inferInstance hward (cltRepg_band szB (STflowE zB))
    (κ := Real.sqrt (2 * (1 / 10)) / 2) (by positivity) 0 (st6_mE_im_ge (by norm_num) (st6_flowE_le szB flow_zB 0))
    (by norm_num) (by norm_num) ![true, false] (by decide) 0

/-- **Target 10, `expWI_Psum_precg`** at `(szB, zB, 7/8, 15/16)`: the premise `(res_ELK_n=1)` stays a hypothesis. -/
example (hAvg : STExpAvgUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    PrecL szB (Sizes.seqP szB) (U := fun n => TimeIcc (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n ×
        {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd 3 (szB.L n))
      (fun n q _ => ‖STPsum (d := 3) (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (q.1 : ℝ) q.2.1.1 b)
        q.2.2‖)
      (fun n q _ => (((szB.W n : ℕ) : ℝ) ^ 3 * (bandFM szB (STflowE zB)).eta n (q.1 : ℝ))⁻¹ * (szB.Bctl n (q.1 : ℝ)) ^ 2) := by
  obtain ⟨K₆, hK₆, hward, -⟩ := ExpWardIGen_bandData
  exact expWI_Psum_precg (bandFM szB (STflowE zB)) (Sizes.seqP szB) inferInstance szB_tendsto hward
    (cltRepg_band szB (STflowE zB)) (κ := Real.sqrt (2 * (1 / 10)) / 2) (by positivity)
    (fun n => st6_mE_im_ge (by norm_num) (st6_flowE_le szB flow_zB n)) (fun n t => rfl)
    (step2IterGen_oneLoop_band szB (STflowE zB)).1 (fun _ => by norm_num) (fun _ => by norm_num) hAvg

/-- **Target 11, `expWI_coreg`** at `(szB, zB, 7/8, 15/16)`: the Ward terms of regime (i), unprimed and primed; the premise `(res_ELK_n=1)` stays a hypothesis. -/
example (hAvg : STExpAvgUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STExpWardIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) ∧
      STExpWardIConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) := by
  obtain ⟨K₆, hK₆, hward, hker, hrow, hcol⟩ := ExpWardIGen_bandData
  have h := expWI_coreg (bandFM szB (STflowE zB)) (Sizes.seqP szB) (by norm_num) (κm := Real.sqrt (2 * (1 / 10)) / 2)
    (by positivity) hK₆.le szB_admissible inferInstance (cltRepg_band szB (STflowE zB))
    (fun n => st6_mE_im_ge (by norm_num) (st6_flowE_le szB flow_zB n)) (fun n t => rfl) hward
    (step2IterGen_oneLoop_band szB (STflowE zB)).1 hker hrow hcol (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) szB_reg5I hAvg
  exact ⟨h, expWIg_concl_prime _ _ _ _ h⟩

/-- The class of mollifiers read by the conclusion is nonempty at the data (`st6_mollifier_familyg`, `0 < Cq`, `0 < c`, `STMollifierProps` eventually). -/
example : ∃ (Cq c : ℝ), 0 < Cq ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
    ∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) Cq c (ϑ n) :=
  st6_mollifier_familyg szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB_WO

/-- **Target 11, the pins at the band tuple, `d = 3`**: every family premise is discharged (probability law, flow facts, `cltRepg_band`, `b45Gen_facts_band`,
`step2IterGen_oneLoop_band`); no hypothesis remains. -/
example : STExpWardIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  stExpWardIgL_of (fun sz => inferInstance) (step5CasesGen_flowFacts_band 3)
    (fun sz κ ε 𝔠 𝔡 z _ _ => ⟨fun _ => 0, sz.lam, STflowE z, cltRepg_band sz (STflowE z)⟩) (b45Gen_facts_band 3)
    (fun sz κ ε 𝔠 𝔡 z _ _ => (step2IterGen_oneLoop_band sz (STflowE z)).1)

example : STExpWardIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  stExpWardIgL'_of (fun sz => inferInstance) (step5CasesGen_flowFacts_band 3)
    (fun sz κ ε 𝔠 𝔡 z _ _ => ⟨fun _ => 0, sz.lam, STflowE z, cltRepg_band sz (STflowE z)⟩) (b45Gen_facts_band 3)
    (fun sz κ ε 𝔠 𝔡 z _ _ => (step2IterGen_oneLoop_band sz (STflowE z)).1)

/-- **The band re-derivations** `stExpWardI_gen_band`, `stExpWardI'_gen_band`, read at the data of regime (i) `(szB, zB, 7/8, 15/16)` through the merged
`inst_ing6_I`; the stochastic premises of `STIngR6` are the hypotheses of the produced statements. -/
example : InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t) szB zB
    (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ (stExpWardI_gen_band 3) szB_reg5I

example : InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl' sz E s t) szB zB
    (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ (stExpWardI'_gen_band 3) szB_reg5I

end Instances

end RBM.BA

end
