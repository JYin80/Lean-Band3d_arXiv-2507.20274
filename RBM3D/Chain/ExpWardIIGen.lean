/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpWardII
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.B45Gen
import RBM3D.Chain.CltGen

/-!
# The Ward decomposition of regime (ii) over the carrier (BA-V row V1s3', ticket T2508 row a, targets 1-2)

Additive restatement of `Induction/ExpWardII.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the vocabulary and pins of `Chain/Step6Gen.lean`.
Paper: arXiv:2507.20274, `6:136-147` (Ward decomposition `6:137-141`), `1_2:1030-1045` (`(WI_calL)`, `(WI_calK)`).

* **Target 1.**  `expWII_slot0g` (band `expWII_slot0`, `ExpWardII:182`): the first slot of `f_u - Q^{(1)} f_u` is `Im 𝔼(𝓛-𝒦)^{(1)}_{u,+,a₂} / (N η_u)`, the expectation of the
  samplewise identity `Step5CasesGen_WardIdent` (`Step5CasesGen:187`; `N = (WL)^d`, `η_u = C.eta n u`); the loops of the carrier are integrable by `CltRepg` and `κ ≤ Im m`.
  `expWII_slot1g` (band `:223`): the second slot, through the cyclic rotation of the Ward family `ZeroModeGen_WardFam` (first conjunct of `ZeroModeGen_WardCls`, a field of
  `B45Gen_Facts`).  `expWII_det_boundg` (band `:329`): the one-size bound with the constant `3`.  `expWII_two_slot_bound` (band `:251`, `norm_zeroModeOp_le`) is reused by name.
* **Target 2.**  `STExpWardIIConclgL_of_avgU` (band `STExpWardIIConcl_of_avgU`, `:364`; `STExpAvgUgL C μ s t → STExpWardIIConclgL C μ s t`, `𝒦^{(1)}_+ = m` eventually,
  `(Im m)⁻¹ ≤ κm⁻¹`, so the constant is `3 κm⁻¹`), `stExpWardIIgL_of` (→ `STExpWardIIgL`, `Step6Gen:351`); the band `stExpWardII_holds` (`:419`) is re-derived through
  `STExpWardII_iff_gL` (`Step6Gen:603`).

Coupling (UBA-C1): `STReg5II` and `Bctl` only, no kernel, R1 never.  No `def`, `abbrev` or `structure` is added; helpers are `private` and prefixed `ExpWardIIGen_`.
The private band helpers `expWII_zeroModeOp_eq0`, `expWII_zeroModeOp_eq1`, `expWII_zeroModeSet_zero`, `expWII_STKloop_eq1` are used by `open private`.  Ports: none from `../RBM1D`, `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private expWII_zeroModeOp_eq0 expWII_zeroModeOp_eq1 expWII_zeroModeSet_zero expWII_STKloop_eq1 from RBM3D.Induction.ExpWardII

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Bridges: integrability, the rotation of the 2-loop, the size level -/

section Bridges

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- The loops of the carrier are integrable (measurable and bounded by `η_u^{-k}`, `CltRepg` and `κ ≤ Im m`; copy of the private `ExpWardIGen_integrable_L`, `ExpWardIGen:109`). -/
private theorem ExpWardIIGen_integrable_L [IsFiniteMeasure μ]
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

/-- `𝔼(𝓛-𝒦)^{(k+1)} = 𝔼𝓛^{(k+1)} - 𝒦^{(k+1)}` (probability law; band `expWII_avg_eq`, `ExpWardII:90`). -/
private theorem ExpWardIIGen_int_LK (hμ : IsProbabilityMeasure μ)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) :
    ∫ ω, (C.L n u σ a ω - C.K n u σ a) ∂μ = (∫ ω, C.L n u σ a ω ∂μ) - C.K n u σ a := by
  have : IsProbabilityMeasure μ := hμ
  rw [integral_sub (ExpWardIIGen_integrable_L C μ hrep hκ n hm hu σ a) (integrable_const _), integral_const]
  simp

/-- `f_u = 𝔼(𝓛 - 𝒦)^{(2)}_u` as the integral of `(𝓛 - 𝒦)^{(2)}` (band `expWII_expErr_eq`, `ExpWardII:60`). -/
private theorem ExpWardIIGen_expErr_eq (hμ : IsProbabilityMeasure μ)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErrg C μ n u σ a = ∫ ω, (C.L n u σ a ω - C.K n u σ a) ∂μ :=
  (ExpWardIIGen_int_LK C μ hμ hrep hκ n hm hu (k := 1) σ a).symm

/-- **The rotation of the 2-loop** (band `expWII_STLKM_swap`, `ExpWardII:158`): `𝓛^{(2)}_{σ,a} = 𝓛^{(2)}_{(σ₂,σ₁),(a₂,a₁)}` and the same for `𝒦`, the cyclic rotation
of the Ward family `ZeroModeGen_WardFam` (first conjunct), at `[0,1)`. -/
private theorem ExpWardIIGen_swap (hward : ZeroModeGen_WardCls sz C) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : sz.SeqΩ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    C.L n u σ a ω = C.L n u ![σ 1, σ 0] ![a 1, a 0] ω ∧ C.K n u σ a = C.K n u ![σ 1, σ 0] ![a 1, a 0] := by
  obtain ⟨TL, TK, hL, hK, hwL, hwK⟩ := hward n u hu0 hu1 ω
  have e1 : loopOf σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by simp [loopOf, List.ofFn_succ]
  have e2 : loopOf (![σ 1, σ 0] : Fin 2 → Bool) (![a 1, a 0] : Fin 2 → Zd d (sz.L n)) = ⟨[σ 1, σ 0], [a 1, a 0]⟩ := by
    simp [loopOf, List.ofFn_succ]
  exact ⟨by rw [hL 2 σ a, hL 2 _ _, e1, e2]; exact hwL.1 (σ 0) (a 0) [σ 1] [a 1] rfl,
    by rw [hK 2 σ a, hK 2 _ _, e1, e2]; exact hwK.1 (σ 0) (a 0) [σ 1] [a 1] rfl⟩

/-- `f_u` is invariant under the rotation of the 2-loop (band `expWII_STExpErr_swap`, `ExpWardII:165`). -/
private theorem ExpWardIIGen_expErr_swap (hμ : IsProbabilityMeasure μ) (hward : ZeroModeGen_WardCls sz C) (n : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErrg C μ n u σ a = STExpErrg C μ n u ![σ 1, σ 0] ![a 1, a 0] := by
  have : Nonempty sz.SeqΩ := Measure.nonempty_of_neZero μ
  obtain ⟨ω₀⟩ := this
  unfold STExpErrg
  rw [(ExpWardIIGen_swap C hward n hu0 hu1 ω₀ σ a).2,
    integral_congr_ae (Filter.Eventually.of_forall fun ω => (ExpWardIIGen_swap C hward n hu0 hu1 ω σ a).1)]


/-- `(N(1-u))⁻¹ ≤ W^{-d}B_{u,0}`, hence `(N η_u)⁻¹ ≤ κm⁻¹ W^{-d}B_{u,0}` (the size-level half of the band `expWII_inv_Neta_le`, `ExpWardII:303`; pattern `QtBootGen_inv_one_sub_le`). -/
private theorem ExpWardIIGen_inv_N_le (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) :
    (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ sz.Bctl n u := by
  have h1 : 0 < 1 - u := by linarith
  have hsize : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
    rw [mul_assoc, mul_inv]
  rw [st6_Bctl_eq sz n hu]
  have h5 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ := by positivity
  linarith

end Bridges

/-! ## 2. The two slots and the one-size bound (target 1) -/

section Slots

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **First slot** (`6:138-140`, `(WI_calL)`, `(WI_calK)`; band `expWII_slot0`, `ExpWardII:182`): for `σ₁ ≠ σ₂`, `f_u - Q^{(1)} f_u = Im 𝔼(𝓛-𝒦)^{(1)}_{u,+,a₂} / (N η_u)`,
the expectation of the samplewise identity `Step5CasesGen_WardIdent` (`η_u = C.eta n u`); the loops are integrable by `CltRepg` and `κ ≤ Im m`. -/
theorem expWII_slot0g (hμ : IsProbabilityMeasure μ) (hWI : Step5CasesGen_WardIdent C)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErrg C μ n u σ a - zeroModeOp d (sz.L n) 0 (fun b => STExpErrg C μ n u σ b) a =
      ((((∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω ∂μ) -
          C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) /
        (((sz.size n : ℕ) : ℂ) * (C.eta n u : ℂ)) := by
  have : IsProbabilityMeasure μ := hμ
  refine (expWII_zeroModeOp_eq0 sz n (fun b => STExpErrg C μ n u σ b) a).trans ?_
  have hint : ∀ b : Fin 2 → Zd d (sz.L n), Integrable (fun ω => C.L n u σ b ω - C.K n u σ b) μ := fun b =>
    (ExpWardIIGen_integrable_L C μ hrep hκ n hm hu1 (k := 1) σ b).sub (integrable_const _)
  have hsum : ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) * ∑ c : Zd d (sz.L n), STExpErrg C μ n u σ ![c, a 1] =
      ∫ ω, (((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) *
        ∑ c : Zd d (sz.L n), (C.L n u σ ![c, a 1] ω - C.K n u σ ![c, a 1])) ∂μ := by
    rw [integral_const_mul, integral_finsetSum _ (fun c _ => hint _)]
    simp only [ExpWardIIGen_expErr_eq C μ hμ hrep hκ n hm hu1]
  have hpt : ∀ ω, ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) *
      ∑ c : Zd d (sz.L n), (C.L n u σ ![c, a 1] ω - C.K n u σ ![c, a 1]) =
      (((C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω - C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) /
        ((((sz.size n : ℕ) : ℂ)) * (C.eta n u : ℂ)) := by
    intro ω
    rw [← expWII_zeroModeOp_eq0 sz n (fun b => C.L n u σ b ω - C.K n u σ b) a, ← expWII_zeroModeSet_zero]
    exact hWI n u hu0 hu1 ω σ hσ a
  have hint1 : Integrable (fun ω => C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω -
      C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)) μ :=
    (ExpWardIIGen_integrable_L C μ hrep hκ n hm hu1 (k := 0) (fun _ : Fin 1 => true) (fun _ => a 1)).sub (integrable_const _)
  change ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) * ∑ c : Zd d (sz.L n), STExpErrg C μ n u σ ![c, a 1] = _
  rw [hsum]
  simp_rw [hpt]
  rw [integral_div]
  have h1 : ∫ ω, (((C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω -
        C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) ∂μ =
      ((∫ ω, (C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω -
        C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)).im ∂μ : ℝ) : ℂ) :=
    integral_ofReal
  have h2 : ∫ ω, (C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω - C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)).im ∂μ =
      (∫ ω, (C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω - C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)) ∂μ).im :=
    integral_im (μ := μ) hint1
  rw [h1, h2, ExpWardIIGen_int_LK C μ hμ hrep hκ n hm hu1 (k := 0) (fun _ : Fin 1 => true) (fun _ => a 1)]

/-- **Second slot** (band `expWII_slot1`, `ExpWardII:223`): `f_u - Q^{(2)} f_u = Im 𝔼(𝓛-𝒦)^{(1)}_{u,+,a₁} / (N η_u)`: the first slot of the rotated loop `(σ₂,σ₁),(a₂,a₁)`
(`ExpWardIIGen_swap`, the cyclic rotation of `ZeroModeGen_WardCls`; `σ' = ![σ 1, σ 0]` is again mixed). -/
theorem expWII_slot1g (hμ : IsProbabilityMeasure μ) (hWI : Step5CasesGen_WardIdent C) (hward : ZeroModeGen_WardCls sz C)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErrg C μ n u σ a - zeroModeOp d (sz.L n) 1 (fun b => STExpErrg C μ n u σ b) a =
      ((((∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a 0) ω ∂μ) -
          C.K n u (fun _ : Fin 1 => true) (fun _ => a 0)).im : ℝ) : ℂ) /
        (((sz.size n : ℕ) : ℂ) * (C.eta n u : ℂ)) := by
  have hσ' : (![σ 1, σ 0] : Fin 2 → Bool) 0 ≠ (![σ 1, σ 0] : Fin 2 → Bool) 1 := fun h => hσ h.symm
  have h0 := expWII_slot0g C μ hμ hWI hrep hκ n hm hu0 hu1 hσ' (![a 1, a 0] : Fin 2 → Zd d (sz.L n))
  have h0' := (expWII_zeroModeOp_eq0 sz n (fun b => STExpErrg C μ n u ![σ 1, σ 0] b)
    (![a 1, a 0] : Fin 2 → Zd d (sz.L n))).symm.trans h0
  refine (expWII_zeroModeOp_eq1 sz n (fun b => STExpErrg C μ n u σ b) a).trans ?_
  have e1 : ∀ c : Zd d (sz.L n), STExpErrg C μ n u σ ![a 0, c] = STExpErrg C μ n u ![σ 1, σ 0] ![c, a 0] := fun c =>
    ExpWardIIGen_expErr_swap C μ hμ hward n hu0 hu1 σ ![a 0, c]
  simp_rw [e1]
  exact h0'

/-- **The decomposition bound at one size** (`6:138-140`, constant `3`; band `expWII_det_bound`, `ExpWardII:329`): from a bound `M` of the one-point averages,
`‖f_u - Q^{({1,2})} f_u‖_∞ ≤ 3 M (N η_u)⁻¹`. -/
theorem expWII_det_boundg (hμ : IsProbabilityMeasure μ) (hWI : Step5CasesGen_WardIdent C) (hward : ZeroModeGen_WardCls sz C)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (heta : C.eta n u = (1 - u) * (C.m n).im) {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) {M : ℝ}
    (hM : ∀ x : Zd d (sz.L n),
      ‖(∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => x) ω ∂μ) - C.K n u (fun _ : Fin 1 => true) (fun _ => x)‖ ≤ M)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖STExpErrg C μ n u σ a -
        zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErrg C μ n u σ b) a‖ ≤
      3 * (M * (((sz.size n : ℕ) : ℝ) * C.eta n u)⁻¹) := by
  have hη : 0 < C.eta n u := by rw [heta]; exact mul_pos (by linarith) (lt_of_lt_of_le hκ hm)
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hslot : ∀ x : Zd d (sz.L n),
      ‖((((∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => x) ω ∂μ) -
          C.K n u (fun _ : Fin 1 => true) (fun _ => x)).im : ℝ) : ℂ) /
        (((sz.size n : ℕ) : ℂ) * (C.eta n u : ℂ))‖ ≤ M * (((sz.size n : ℕ) : ℝ) * C.eta n u)⁻¹ := by
    intro x
    rw [norm_div, Complex.norm_real, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hη.le, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 (mul_pos hN hη).le)
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hM x)
  exact expWII_two_slot_bound (fun b => STExpErrg C μ n u σ b)
    (fun b => (expWII_slot0g C μ hμ hWI hrep hκ n hm hu0 hu1 hσ b).symm ▸ hslot (b 1))
    (fun b => (expWII_slot1g C μ hμ hWI hward hrep hκ n hm hu0 hu1 hσ b).symm ▸ hslot (b 0)) a

end Slots

/-! ## 3. Along the sequence and the pin (target 2) -/

section Seq

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`STExpWardIIConclgL` from `(res_ELK_n=1)` uniformly in `u`** (`6:141`; band `STExpWardIIConcl_of_avgU`, `ExpWardII:364`; regime-free): `STExpAvgUgL` and the conclusion
are deterministic (`st6_prec_det_iffg`); `𝒦^{(1)}_+ = m` eventually turns the average into the one-point bound, `(Im m)⁻¹ ≤ κm⁻¹`, and the constant `3 κm⁻¹` is absorbed into `N^{τ/2}`. -/
theorem STExpWardIIConclgL_of_avgU (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) (hWI : Step5CasesGen_WardIdent C)
    (hward : ZeroModeGen_WardCls sz C)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κm : ℝ} (hκm : 0 < κm) (hmn : ∀ n, κm ≤ (C.m n).im)
    (heta : ∀ (n : ℕ) (t : ℝ), C.eta n t = (1 - t) * (C.m n).im)
    (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then C.m n else (starRingEnd ℂ) (C.m n))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (_hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hAvg : STExpAvgUgL C μ s t) :
    STExpWardIIConclgL C μ s t := by
  unfold STExpWardIIConclgL
  refine (st6_prec_det_iffg sz μ hμ hsz _ _).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hA := (st6_prec_det_iffg sz μ hμ hsz _ _).1 hAvg (τ / 2) hτ2
  have hNge : ∀ᶠ n in atTop, 3 * κm⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    (tendsto_size sz hsz).eventually (eventually_le_rpow (3 * κm⁻¹) hτ2)
  filter_upwards [hA, hNge, hK1] with n hn hNn hk1
  rintro ⟨⟨u, hu⟩, ⟨σ, hσ⟩, a⟩
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hB0 : 0 ≤ sz.Bctl n u := (STBctl_pos sz n hu1).le
  have hbd := expWII_det_boundg C μ hμ hWI hward hrep hκm n (hmn n) hu0 hu1 (heta n u) hσ
    (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 2)
    (fun x => by
      have := hn (⟨u, hu⟩, true, x)
      rwa [← hk1 u hu0 hu1 true x] at this) a
  have hc : (((sz.size n : ℕ) : ℝ) * C.eta n u)⁻¹ ≤ κm⁻¹ * sz.Bctl n u := by
    have hm0 : 0 < (C.m n).im := lt_of_lt_of_le hκm (hmn n)
    have heq : (((sz.size n : ℕ) : ℝ) * C.eta n u)⁻¹ = ((C.m n).im)⁻¹ * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
      rw [heta n u]
      field_simp
    rw [heq]
    exact mul_le_mul (inv_anti₀ hκm (hmn n)) (ExpWardIIGen_inv_N_le sz n hu1) (by positivity) (inv_nonneg.2 hκm.le)
  have hP : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN.le _
  have hM0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 2 := mul_nonneg hP (by positivity)
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    (UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ).symm
  change ‖STExpErrg C μ n u σ a -
      zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErrg C μ n u σ b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u) ^ 3
  calc _ ≤ 3 * ((((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 2) *
          (((sz.size n : ℕ) : ℝ) * C.eta n u)⁻¹) := hbd
    _ ≤ 3 * ((((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 2) * (κm⁻¹ * sz.Bctl n u)) := by gcongr
    _ = (3 * κm⁻¹) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 3 := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 3 := by
        have hB3 : 0 ≤ (sz.Bctl n u) ^ 3 := by positivity
        have := mul_le_mul_of_nonneg_right hNn hP
        exact mul_le_mul_of_nonneg_right this hB3
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u) ^ 3 := by rw [hrpow]

end Seq

/-- **The pin `STExpWardIIgL`** (`Step6Gen:351`; band `stExpWardII_holds`, `ExpWardII:419`) from the family premises: probability law (row 1), flow facts (row 3), `∃ H₀ g' E, CltRepg`
along the flow (row 9; the loops are integrable), `𝒦^{(1)}_σ = m_σ` at both charges along the flow (row 19; BA `baKsol_oneLoop`), the samplewise Ward identity
`Step5CasesGen_WardIdent` along the flow (row 23; BA `baStep5CasesGen_wardIdent`) and the class `B45Gen_Facts` (row 19': its field `ZeroModeGen_WardCls` gives the rotation;
BA `baB45Gen_facts`).  The constant `𝔠_d = 1/100`; no premise of `STIngR6gL` beyond `STReg5II` and `STExpAvgUgL` is used. -/
theorem stExpWardIIgL_of {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hμ : ∀ sz, IsProbabilityMeasure (law sz))
    (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hRep : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E)
    (hK1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
        (mk sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n))
    (hWI : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → Step5CasesGen_WardIdent (mk sz z))
    (hB45 : B45Gen_Facts d Flow mk) :
    STExpWardIIgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR _ _ _ _ _ _ _ _ hAvg
  obtain ⟨κm, hκm, H⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, hmn, heta⟩ := H sz ε 𝔠 𝔡 z hflow
  obtain ⟨K₆, hK₆, G⟩ := hB45 κ hκ
  obtain ⟨hward, -⟩ := G sz ε 𝔠 𝔡 z hflow
  obtain ⟨H₀, g', E, hrep⟩ := hRep sz κ ε 𝔠 𝔡 z hκ hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  exact STExpWardIIConclgL_of_avgU (mk sz z) (law sz) (hμ sz) hadm.2.2.1 (hWI sz κ ε 𝔠 𝔡 z hκ hflow) hward hrep hκm hmn heta
    (hK1 sz κ ε 𝔠 𝔡 z hκ hflow) hs0 (fun n => (hst n).le) ht1 hAvg

/-! ## 4. The band re-derivation -/

/-! ## 5. Compiled nonempty instances at `d = 3` (regime (ii) data of the band: `szB`, `zB`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `(s, t) = (15/16, 31/32)`)

`szB`: `L = 4`, `W_n = n + 4`, `lam = 1`.  Discharged: flow, times, admissibility, probability law, flow facts, `CltRepg` (`cltRepg_band`, `H₀ = 0`, `g' = lam`), the samplewise Ward identity
(`step5CasesGen_wardIdent_band`), the Ward class with its rotation (`zeroModeGen_wardCls_band`, `b45Gen_facts_band`), `𝒦^{(1)}_σ = m_σ` at both charges.  What stays a hypothesis is
`STExpAvgUgL` at the instance (`(res_ELK_n=1)`, the conclusion of `STImproveExpAvergL`, row c of T2502). -/

end RBM.BA

end
