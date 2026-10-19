/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Chain.StepDecompGen
import RBM3D.Chain.GridRepTailGen2
import RBM3D.Chain.DecayGen
import RBM3D.Induction.GridAssemblyN

/-!
# The assembly of the stopped grid walk over the carrier

Generic forms of `Induction/GridAssemblyN` over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`.
The per-step vocabulary is in `Chain/StepDecompGen`.

* §1 the statements `qvFormNg`, `StoppedAzumaZNg`, `AzumaSubGNg`, `YMomentBoundsNg`,
  `GridAssemblyHypNg` (structure), `AssembledNg`: the kernel is `Step2Gen_UN Cm.toFlowFM n`, the field
  `hE : |E| ≤ 2` of the band bundle is the kernel class `GridRepTailGen_Ker` (its near-identity
  conjunct gives the coarse bound `(1 + (1 - u_m)⁻¹)^k`);
* §2 the coarse row bound; §3 measurability of `ZvecNg` / `YvecNg` under `StepDecompGen_LoopForm`
  and `StepDecompGen_WalkForm` (`GridAssemblyGen_stronglyMeasurable_ZvecNg`,
  `GridAssemblyGen_stronglyMeasurable_YvecNg`);
* §4 the stopped Azuma bound; §5 the fourth moment of the stopped `Y` sum;
  §6 the single-scale core and the assembled bound `assembledNg`;
* §7 band bridges (`qvFormN`, the bundle, `YMomentBoundsN`).

Private band helpers that are model-free are reused by `open private`; the lemmas that read `Ugen`,
`pathP`, `pathH`, `zt E u` are copied and adapted.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private gridAsm_measurable_deriv_zero gridAsm_loopL_line_regular gridAsm_azuma_step gridAsm_mart_moment4
  gridAsm_norm_pow4_le_re_im gridAsm_zBudget gridAsm_moment4_budget_le gridAsm_yBudget gridAsm_card_label
  from RBM3D.Induction.GridAssemblyN

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The statements over the carrier -/

section Pins

variable {d : ℕ} {sz : Sizes d}

/-- `qvFormN` over the carrier: the real part of `STeeUMg`; the band bridge is `qvFormN`. -/
def qvFormNg (Cm : Step2Mat sz) (n : ℕ) (v w : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin k → Zd d (sz.L n)) : ℝ :=
  (STeeUMg Cm n v w M σ a).re

/-- **`StoppedAzumaZNg`** (band `StoppedAzumaZN`): `ZvecNg`, `Step2Gen_UN`; the hypothesis `|E n| < 2` is
dropped. -/
def StoppedAzumaZNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n k : ℕ) (σ : Fin k → Bool) (τ : PathΩ sz → ℕ),
    (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    ∀ (m : ℕ), m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0),
      (∀ j < m, SubGaussStopNg Cm σ (gridTime s t K n) τ (fun j ω => ZvecNg Cm s t K n j σ ω) m a j (c j)) →
      ∀ x : ℝ, 0 ≤ x →
        Cm.Pp.real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m) (ZvecNg Cm s t K n j σ ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ)))

/-- **`AzumaSubGNg`** (band `AzumaSubGN`): the walk coupling `g` enters only through `gvarF`; the
increment is `ZfamNg` (`Cm.Hpath`); the theorem is the band `azumaSubGN` at `sz.withLam g` under `StepDecompGen_WalkForm`
(`azumaSubGNg`). -/
def AzumaSubGNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] (g : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) {ι : Type} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ),
    (∀ b, HermTestFun sz n (Φ b)) → ∀ (κ : ι → ℂ) (τ : PathΩ sz → ℕ)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)),
    (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    (∀ ω j, j < τ ω → Cm.Hpath s t K n j ω ∈ G j) →
    ∀ (j : ℕ) (Q : ℝ≥0),
      (∀ M ∈ G j, M.IsHermitian →
        gridStep s t K n * ∑ c : CoordF d (sz.L n) (sz.W n),
          (gvarF d (sz.L n) (sz.W n) (g n) c : ℝ) *
          ‖∑ b, κ b * RBM.Ind.dirDerivN (Φ b) M (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 ≤ (Q : ℝ)) →
      SubGaussFormNg Cm j τ (fun ω => ∑ b, κ b * ZfamNg Cm s t K n j Φ ω b) Q

/-- `YMomentBoundsN` over the carrier. -/
def YMomentBoundsNg (Cm : Step2Mat sz) {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ)
    (τ : PathΩ sz → ℕ) (K : ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (v w : ℕ → ℝ) : Prop :=
  (∀ j, StronglyMeasurable[filt sz (j + 1)] (Y j)) ∧
  ∀ m ≤ K, ∀ (b : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
    Cm.Pp[fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b j ω).re | filt sz j] =ᵐ[Cm.Pp] 0 ∧
    Cm.Pp[fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b j ω).im | filt sz j] =ᵐ[Cm.Pp] 0 ∧
    Integrable (fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b j ω).re ^ 4) Cm.Pp ∧
    Integrable (fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b j ω).im ^ 4) Cm.Pp ∧
    Cm.Pp[fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b j ω).re ^ 2 | filt sz j] ≤ᵐ[Cm.Pp] (fun _ => v j) ∧
    Cm.Pp[fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b j ω).im ^ 2 | filt sz j] ≤ᵐ[Cm.Pp] (fun _ => v j) ∧
    ∫ ω, (stoppedEdgeNg Cm σ u (u m) τ Y b j ω).re ^ 4 ∂Cm.Pp ≤ w j ∧
    ∫ ω, (stoppedEdgeNg Cm σ u (u m) τ Y b j ω).im ^ 4 ∂Cm.Pp ≤ w j

/-- `GridAssemblyHypN` over the carrier: the field `hE : |E| ≤ 2` becomes `hKer` (the four conjuncts of `GridRepTailGen_Ker`;
the near-identity conjunct gives the coarse bound), the kernel is `Step2Gen_UN Cm.toFlowFM n`. -/
structure GridAssemblyHypNg (Cm : Step2Mat sz) {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ)
    (τ : PathΩ sz → ℕ) (Δ : ℝ) (K : ℕ)
    (Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop)
    (A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (Dr Z Y R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → PathΩ sz → ℝ)
    (c : ℕ → (Fin k → Zd d (sz.L n)) → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) : Prop where
  hKer : GridRepTailGen_Ker Cm.toFlowFM n
  hu0 : ∀ i ≤ K, 0 ≤ u i
  hu1 : ∀ i ≤ K, u i < 1
  hΔ0 : 0 ≤ Δ
  hexp : ∀ m ≤ K, ∀ᵐ ω ∂Cm.Pp, A m ω =
    Step2Gen_UN Cm.toFlowFM n σ (u 0) (u m) (A0 ω) +
    ∑ j ∈ Finset.range (min m (τ ω)), Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m)
      ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)
  hκ0 : ∀ i m, i ≤ m → m ≤ K → 0 ≤ κ i m
  hε0 : ∀ i m, i ≤ m → m ≤ K → 0 ≤ εK i m
  hker : ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
    (∀ b, ‖X b‖ ≤ M) → Cls i δ X →
    ∀ a, ‖Step2Gen_UN Cm.toFlowFM n σ (u i) (u m) X a‖ ≤ κ i m * M + εK i m * δ
  hδ0 : 0 ≤ δ0
  hA0cls : ∀ ω, 0 < τ ω → Cls 0 δ0 (A0 ω)
  hdDrift0 : ∀ ω j, j < K → 0 ≤ dDrift j ω
  hδD0 : ∀ ω j, j < K → 0 ≤ δD j ω
  hdrift : ∀ ω j, j < K → j < τ ω → ∀ b, ‖Dr j ω b‖ ≤ dDrift j ω
  hDcls : ∀ ω j, j < K → j < τ ω → Cls (j + 1) (δD j ω) (Dr j ω)
  hc_pos : ∀ m, 1 ≤ m → m ≤ K → ∀ a, 0 < ∑ j ∈ Finset.range m, (c m a j : ℝ)
  hv0 : ∀ j < K, 0 ≤ v j
  hw0 : ∀ j < K, 0 ≤ w j
  hY : YMomentBoundsNg Cm σ u τ K Y v w
  hstepErr0 : ∀ j < K, 0 ≤ stepErr j
  hR : ∀ᵐ ω ∂Cm.Pp, ∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j

/-- **`AssembledNg`** (band `AssembledN`) over the carrier. -/
def AssembledNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] : Prop :=
  sz.SizeTendsto → ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ (D D₁ C_P C_K : ℝ), 0 ≤ C_K →
    D₁ + 4 * D + (k : ℝ) + 2 * C_P + 8 ≤ C_K →
    ∀ᶠ n : ℕ in atTop, ∀ (K : ℕ) (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ)
      (Δ : ℝ) (Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop)
      (A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (Dr Z Y R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → PathΩ sz → ℝ)
      (c : ℕ → (Fin k → Zd d (sz.L n)) → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) (P : ℝ),
      1 ≤ K → K ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊ →
      Δ ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) → (K : ℝ) * Δ ≤ 1 →
      0 ≤ P → P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P →
      (∀ j < K, v j ≤ Δ ^ 2 * P) → (∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) →
      (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
      (∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j)) →
      (∀ m ≤ K, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m → SubGaussStopNg Cm σ u τ Z m a j (c m a j)) →
      GridAssemblyHypNg Cm σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr →
      ∃ G : Set (PathΩ sz), Cm.Pp.real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G, 0 < τ ω → ∀ m ≤ K, ∀ a : Fin k → Zd d (sz.L n),
          ‖A m ω a‖ ≤
            κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) + εK 0 m * δ0 +
            Δ * ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) +
            ((sz.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) +
            ((sz.size n : ℕ) : ℝ) ^ (-D) +
            ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j

end Pins

/-! ## 2. The kernel `Step2Gen_UN`: strong measurability, sums of four, the coarse row bound -/

section KernelBounds

variable {d : ℕ} {sz : Sizes d}

/-- `A ↦ (Step2Gen_UN A)_a` is continuous, so it preserves strong measurability (band `gridAsm_stronglyMeasurable_Ugen_apply`,
). -/
private theorem GridAssemblyGen_stronglyMeasurable_UN_apply {Ω' : Type*} {m : MeasurableSpace Ω'} (C : FlowFM sz)
    (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) {W : Ω' → (Fin k → Zd d (sz.L n)) → ℂ}
    (hW : StronglyMeasurable[m] W) (a : Fin k → Zd d (sz.L n)) :
    StronglyMeasurable[m] (fun ω => Step2Gen_UN C n σ v w (W ω) a) := by
  have hcont : Continuous (fun A : (Fin k → Zd d (sz.L n)) → ℂ => Step2Gen_UN C n σ v w A a) := by
    unfold Step2Gen_UN
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

/-- `Step2Gen_UN` of the four-term increment `Δ D + Z + Y + R`, at one label (band `gridAsm_Ugen_four`). -/
private theorem GridAssemblyGen_UN_four (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) (Δ : ℂ)
    (D Z Y R : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)) :
    Step2Gen_UN C n σ v w (Δ • D + Z + Y + R) a =
      Δ * Step2Gen_UN C n σ v w D a + Step2Gen_UN C n σ v w Z a + Step2Gen_UN C n σ v w Y a
        + Step2Gen_UN C n σ v w R a := by
  unfold Step2Gen_UN
  set κ : (Fin k → Zd d (sz.L n)) → ℂ := fun b =>
    ∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w (a i) (b i) with hκ
  have hterm : ∀ b : Fin k → Zd d (sz.L n), κ b * ((Δ • D + Z + Y + R) b) =
      Δ * (κ b * D b) + κ b * Z b + κ b * Y b + κ b * R b := by
    intro b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **The one-slot row bound from the near-identity conjunct of `GridRepTailGen_Ker`** (`‖uKer_{v,w}‖_{ℓ^∞} ≤ 1 + (1 - w)⁻¹` for `0 ≤ v, w < 1`, no order between `v` and `w`;
band `gridAsm_norm_uKer_le`, where `|w - v| ≤ 1` replaces `w - v`). -/
private theorem GridAssemblyGen_row_le {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n) (σ σ' : Bool) {v w : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) (a : Zd d (sz.L n)) :
    ∑ b, ‖Step2Gen_uKer C n σ σ' v w a b‖ ≤ 1 + (1 - w)⁻¹ := by
  have h3 := hK.2.2.1 σ σ' v w hw0 hw1 a
  have hdiff : |w - v| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hinv : 0 ≤ (1 - w)⁻¹ := inv_nonneg.mpr (by linarith)
  calc ∑ b, ‖Step2Gen_uKer C n σ σ' v w a b‖
      ≤ ∑ b, (‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ +
          ‖Step2Gen_uKer C n σ σ' v w a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have := norm_add_le ((1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b)
          (Step2Gen_uKer C n σ σ' v w a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b)
        rwa [add_sub_cancel] at this
    _ = 1 + ∑ b, ‖Step2Gen_uKer C n σ σ' v w a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [Matrix.one_apply, apply_ite norm, norm_one, norm_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _ ≤ 1 + |w - v| * (1 - w)⁻¹ := by
        refine add_le_add le_rfl ?_
        have := h3
        rwa [show |w - v| = |w - v| from rfl] at this
    _ ≤ 1 + (1 - w)⁻¹ := by
        refine add_le_add le_rfl ?_
        calc |w - v| * (1 - w)⁻¹ ≤ 1 * (1 - w)⁻¹ := mul_le_mul_of_nonneg_right hdiff hinv
          _ = (1 - w)⁻¹ := one_mul _

/-- **The coarse row-sum kernel bound of `Step2Gen_UN`** (band `gridAsm_norm_Ugen_coarse`; the kernel class
`GridRepTailGen_Ker` replaces `3 ≤ L`, `|E| ≤ 2`): for `0 ≤ v, w < 1`, `‖(𝒰_{v,w,σ} X)_a‖ ≤ (1 + (1 - w)⁻¹)^k ‖X‖_max`. -/
theorem GridAssemblyGen_norm_UN_coarse {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n) {k : ℕ}
    (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    {X : (Fin k → Zd d (sz.L n)) → ℂ} {M : ℝ} (hM : 0 ≤ M) (hX : ∀ b, ‖X b‖ ≤ M) (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ v w X a‖ ≤ (1 + (1 - w)⁻¹) ^ k * M := by
  set Kk : Fin k → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ := fun i =>
    Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w with hKk
  have hrow : ∀ i, ∑ c, ‖Kk i (a i) c‖ ≤ 1 + (1 - w)⁻¹ := fun i =>
    GridAssemblyGen_row_le hK (σ i) (σ (finRotate k i)) hv0 hv1 hw0 hw1 (a i)
  calc ‖Step2Gen_UN C n σ v w X a‖
      ≤ ∑ b : Fin k → Zd d (sz.L n), ‖(∏ i, Kk i (a i) (b i)) * X b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin k → Zd d (sz.L n), (∏ i, ‖Kk i (a i) (b i)‖) * M := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (hX b) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (∏ i, ∑ c, ‖Kk i (a i) c‖) * M := by
        rw [← Finset.sum_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ (1 + (1 - w)⁻¹) ^ k * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        calc ∏ i, ∑ c, ‖Kk i (a i) c‖ ≤ ∏ _i : Fin k, (1 + (1 - w)⁻¹) :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _)
                fun i _ => hrow i
          _ = (1 + (1 - w)⁻¹) ^ k := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end KernelBounds

/-! ## 3. Measurability of the first-chaos part `ZvecNg` and of the remainder `YvecNg`

Under `StepDecompGen_LoopForm Cm E` (the loops of the carrier are the loops at `ztOf (Cm.m n) (E n) u`) and
`StepDecompGen_WalkForm Cm lam' Ψ` (the carrier walk is `Ψ n + pathH (sz.withLam lam')`, adapted to the coordinate filtration),
both are `filt sz (j + 1)`-strongly measurable for every `j` (no window hypothesis): the Carathéodory argument of band
`gridAsm_measurable_loopDerivN` at the spectral value `ztOf (Cm.m n) (E n) u`. -/

section Meas

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
  {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- `(M, X) ↦ StepDecompGen_loopDerivZ z M X σ b` is measurable on all pairs of matrices (band
`gridAsm_measurable_loopDerivN`, `zt E u` replaced by an arbitrary spectral value `z`). -/
private theorem GridAssemblyGen_measurable_loopDerivZ (d L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Zd d L) :
    Measurable fun p : Matrix (Idx d L W) (Idx d L W) ℂ × Matrix (Idx d L W) (Idx d L W) ℂ =>
      StepDecompGen_loopDerivZ d L W z p.1 p.2 σ b := by
  unfold StepDecompGen_loopDerivZ
  refine gridAsm_measurable_deriv_zero
    (fun (p : Matrix (Idx d L W) (Idx d L W) ℂ × Matrix (Idx d L W) (Idx d L W) ℂ) (y : ℝ) =>
      loopL d L W (blockMat d L W (p.1 + (y : ℂ) • p.2)) z (loopOf σ b)) (fun y => ?_)
    (fun p => gridAsm_loopL_line_regular d L W z (loopOf σ b) p.1 p.2)
  have hlin : Measurable fun p : Matrix (Idx d L W) (Idx d L W) ℂ × Matrix (Idx d L W) (Idx d L W) ℂ =>
      p.1 + (y : ℂ) • p.2 :=
    Measurable.of_eval_matrix _ fun i j => by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact measurable_fst.eval_matrix.add (measurable_snd.eval_matrix.const_mul _)
  exact ((walk_measurable_loopL d L W z (loopOf σ b)).comp
    (walk_measurable_blockMat d L W)).comp hlin

/-- Under `StepDecompGen_WalkForm` the carrier walk is adapted to the coordinate filtration (`pathH_measurable_filt`). -/
private theorem GridAssemblyGen_Hpath_measurable (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) : Measurable[filt sz j] (fun ω : PathΩ sz => Cm.Hpath s t K n j ω) := by
  have hT : Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => Ψ n + H :=
    Measurable.of_eval_matrix _ fun i j => measurable_const.add ((measurable_pi_apply j).comp (measurable_pi_apply i))
  have h1 : (fun ω : PathΩ sz => Cm.Hpath s t K n j ω) = fun ω : PathΩ sz =>
      Ψ n + StepDecompGen_pathH sz lam' s t K n j ω := funext fun ω => hW.2.2 s t K n j ω
  rw [h1]
  exact hT.comp (pathH_measurable_filt (sz.withLam lam') s t K n j)

/-- Under `LoopForm`, `Cm.LM` is measurable in the matrix. -/
private theorem GridAssemblyGen_meas_LM (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => Cm.LM n u H σ a := by
  simp only [(hL n).2.1 u _ k σ a]
  exact walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (Cm.m n) (E n) u) σ a

/-- The `b`-th component of `ZvecNg` is `filt sz (j + 1)`-measurable (band `gridAsm_measurable_ZvecN_apply`). -/
private theorem GridAssemblyGen_measurable_ZvecNg_apply (hL : StepDecompGen_LoopForm Cm E)
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Zd d (sz.L n)) :
    Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ZvecNg Cm s t K n j σ ω b) := by
  have hΨ := GridAssemblyGen_measurable_loopDerivZ d (sz.L n) (sz.W n)
    (ztOf (Cm.m n) (E n) (gridTime s t K n (j + 1))) σ b
  have h0 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => Cm.Hpath s t K n j ω) :=
    (GridAssemblyGen_Hpath_measurable hW s t K n j).mono ((filt sz).mono (Nat.le_succ j)) le_rfl
  have h1 := GridAssemblyGen_Hpath_measurable hW s t K n (j + 1)
  have hsub : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => Cm.Hpath s t K n (j + 1) ω - Cm.Hpath s t K n j ω) :=
    @Measurable.of_eval_matrix _ _ _ _ _ (filt sz (j + 1)) _ fun i j' => by
      simp only [Matrix.sub_apply]
      exact (@Measurable.eval_matrix _ _ _ _ _ (filt sz (j + 1)) i j' _ h1).sub
        (@Measurable.eval_matrix _ _ _ _ _ (filt sz (j + 1)) i j' _ h0)
  have h := hΨ.comp (h0.prodMk hsub)
  convert h using 1
  funext ω
  unfold ZvecNg loopFamNg
  exact StepDecompGen_dirDerivN_LM hL n _ _ _ σ b

/-- The `b`-th component of `martIncNg` is `filt sz (j + 1)`-measurable (band `gridAsm_measurable_martIncN_apply`). -/
private theorem GridAssemblyGen_measurable_martIncNg_apply (hL : StepDecompGen_LoopForm Cm E)
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Zd d (sz.L n)) :
    Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => martIncNg Cm s t K n j σ ω b) := by
  have h1 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => AvecNg Cm s t K n (j + 1) σ ω b) :=
    ((GridAssemblyGen_meas_LM hL n (gridTime s t K n (j + 1)) σ b).comp
      (GridAssemblyGen_Hpath_measurable hW s t K n (j + 1))).sub measurable_const
  have h2 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz =>
      MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' b) ω) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt sz).mono (Nat.le_succ j)) le_rfl
  exact h1.sub h2

/-- **`ZvecNg` is `filt sz (j + 1)`-strongly measurable** (the `hZmeas` input of `AssembledNg`), for every window and `j`
(band `gridAsm_stronglyMeasurable_ZvecN`). -/
theorem GridAssemblyGen_stronglyMeasurable_ZvecNg (hL : StepDecompGen_LoopForm Cm E)
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => ZvecNg Cm s t K n j σ ω) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt sz (j + 1)) _ _ fun b =>
    GridAssemblyGen_measurable_ZvecNg_apply hL hW s t K n j σ b

/-- **`YvecNg = martIncNg - ZvecNg` is `filt sz (j + 1)`-strongly measurable** (the first field of `YMomentBoundsNg`; band
`gridAsm_stronglyMeasurable_YvecN`). -/
theorem GridAssemblyGen_stronglyMeasurable_YvecNg (hL : StepDecompGen_LoopForm Cm E)
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => YvecNg Cm s t K n j σ ω) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt sz (j + 1)) _ _ fun b =>
    (GridAssemblyGen_measurable_martIncNg_apply hL hW s t K n j σ b).sub
      (GridAssemblyGen_measurable_ZvecNg_apply hL hW s t K n j σ b)

end Meas

/-! ## 4. The stopped Azuma bound for the first-chaos part -/

section StoppedAzuma

variable {d : ℕ} {sz : Sizes d}

/-- The label-weighted Azuma tail for a fixed endpoint `m` and label `a` and an arbitrary step-indexed increment `Z`
(`Z j` is `filt (j+1)`-strongly measurable for `j < m`): `sum_stopped` rewrites the stopped sum as `Σ_{j<m} 1{j<τ}
(𝒰_{u_{j+1},u_m} Z_j)_a` and `azuma_complex` (via `gridAsm_azuma_step`) gives the tail (band `gridAsm_azuma_Ugen`). -/
private theorem GridAssemblyGen_azuma_UN (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] {n k : ℕ} (σ : Fin k → Bool)
    (u : ℕ → ℝ) {τ : PathΩ sz → ℕ} (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    {Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} (m : ℕ)
    (hZ : ∀ j < m, StronglyMeasurable[filt sz (j + 1)] (Z j)) (a : Fin k → Zd d (sz.L n))
    (c : ℕ → ℝ≥0) (hsubG : ∀ j < m, SubGaussStopNg Cm σ u τ Z m a j (c j)) {x : ℝ} (hx : 0 ≤ x) :
    Cm.Pp.real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Z j ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  set X : ℕ → PathΩ sz → ℂ := fun j => {ω' | j < τ ω'}.indicator (fun ω' =>
    Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Z j ω') a) with hXdef
  have hX : ∀ j < m, StronglyMeasurable[filt sz (j + 1)] (X j) := by
    intro j hj
    have hset : MeasurableSet[filt sz (j + 1)] {ω | j < τ ω} :=
      ((filt sz).mono (Nat.le_succ j)) _ (hτ j)
    exact (GridAssemblyGen_stronglyMeasurable_UN_apply Cm.toFlowFM n σ _ _ (hZ j hj) a).indicator hset
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Z j ω) a‖}
      = {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    have h := sum_stopped (Ω' := PathΩ sz) (M := ℂ)
      (fun i ω' => Step2Gen_UN Cm.toFlowFM n σ (u i) (u m) (Z (i - 1) ω') a) τ m ω
    simp only [Nat.add_sub_cancel] at h
    rw [h]
  rw [hset]
  exact gridAsm_azuma_step (μ := Cm.Pp) (ℱ := filt sz) hX hsubG hx

end StoppedAzuma

/-! ## 5. The fourth-moment tail of the second-order part `Y` -/

section YMoment

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp]

/-- `stoppedEdgeNg … b j` is `filt sz (j+1)`-strongly measurable (band `gridAsm_stronglyMeasurable_stoppedEdgeN`). -/
private theorem GridAssemblyGen_stronglyMeasurable_stoppedEdge {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ)
    {τ : PathΩ sz → ℕ} (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    {Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ}
    (hY : ∀ j, StronglyMeasurable[filt sz (j + 1)] (Y j)) (b : Fin k → Zd d (sz.L n)) (j : ℕ) :
    StronglyMeasurable[filt sz (j + 1)] (stoppedEdgeNg Cm σ u t' τ Y b j) := by
  have hset : MeasurableSet[filt sz (j + 1)] {ω | j < τ ω} :=
    ((filt sz).mono (Nat.le_succ j)) _ (hτ j)
  exact (GridAssemblyGen_stronglyMeasurable_UN_apply Cm.toFlowFM n σ _ _ (hY j) b).indicator hset

/-- The stopped sum at one label is the `m`-horizon sum of `stoppedEdgeNg` (`sum_stopped`; band `gridAsm_stopped_sum_eq`). -/
private theorem GridAssemblyGen_stopped_sum_eq {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ)
    (τ : PathΩ sz → ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ) (ω : PathΩ sz)
    (b : Fin k → Zd d (sz.L n)) :
    ∑ j ∈ Finset.range (min m (τ ω)), Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) t' (Y j ω) b
      = ∑ j ∈ Finset.range m, stoppedEdgeNg Cm σ u t' τ Y b j ω := by
  have h := sum_stopped (Ω' := PathΩ sz) (M := ℂ)
    (fun i ω' => Step2Gen_UN Cm.toFlowFM n σ (u i) t' (Y (i - 1) ω') b) τ m ω
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  rfl

/-- **The per-endpoint fourth moment of the propagated, stopped `Y` sum** (band `gridAsm_moment4_fixed`): from
`YMomentBoundsNg`, `E‖(Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} Y_j)_b‖⁴ ≤ 4 (8 (Σ_{j<m} v_j)² + 3 Σ_{j<m} w_j)`; the fourth power is
integrable. -/
private theorem GridAssemblyGen_moment4_fixed {n k : ℕ} {σ : Fin k → Bool}
    {u : ℕ → ℝ} {τ : PathΩ sz → ℕ} (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) {K : ℕ}
    {Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} {v w : ℕ → ℝ}
    (hY : YMomentBoundsNg Cm σ u τ K Y v w) (hv0 : ∀ j < K, 0 ≤ v j) {m : ℕ} (hm : m ≤ K)
    (b : Fin k → Zd d (sz.L n)) :
    Integrable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) Cm.Pp
      ∧ ∫ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4 ∂Cm.Pp
        ≤ 4 * (8 * (∑ j ∈ Finset.range m, v j) ^ 2 + 3 * ∑ j ∈ Finset.range m, w j) := by
  set W : ℕ → PathΩ sz → ℂ := stoppedEdgeNg Cm σ u (u m) τ Y b with hWdef
  have hsum : ∀ ω, ∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b = ∑ j ∈ Finset.range m, W j ω :=
    fun ω => GridAssemblyGen_stopped_sum_eq Cm σ u (u m) τ Y m ω b
  have hWm : ∀ j, StronglyMeasurable[filt sz (j + 1)] (W j) := fun j =>
    GridAssemblyGen_stronglyMeasurable_stoppedEdge Cm σ u (u m) hτ hY.1 b j
  have h8 : ∀ j < m, _ := fun j hj => hY.2 m hm b j hj
  have hre := gridAsm_mart_moment4 (μ := Cm.Pp) (ℱ := filt sz) (fun j ω => (W j ω).re) v w m
    (fun j => Complex.continuous_re.comp_stronglyMeasurable (hWm j))
    (fun j hj => (h8 j hj).1) (fun j hj => (h8 j hj).2.2.1)
    (fun j hj => (h8 j hj).2.2.2.2.1) (fun j hj => hv0 j (by omega))
    (fun j hj => (h8 j hj).2.2.2.2.2.2.1)
  have him := gridAsm_mart_moment4 (μ := Cm.Pp) (ℱ := filt sz) (fun j ω => (W j ω).im) v w m
    (fun j => Complex.continuous_im.comp_stronglyMeasurable (hWm j))
    (fun j hj => (h8 j hj).2.1) (fun j hj => (h8 j hj).2.2.2.1)
    (fun j hj => (h8 j hj).2.2.2.2.2.1) (fun j hj => hv0 j (by omega))
    (fun j hj => (h8 j hj).2.2.2.2.2.2.2)
  have hpt : ∀ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4
        ≤ 2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4 + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4) := by
    intro ω
    rw [hsum ω]
    have := gridAsm_norm_pow4_le_re_im (∑ j ∈ Finset.range m, W j ω)
    rwa [Complex.re_sum, Complex.im_sum] at this
  have hsm : StronglyMeasurable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) := by
    have heq : (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4)
        = fun ω => ‖∑ j ∈ Finset.range m, W j ω‖ ^ 4 := funext fun ω => by rw [hsum ω]
    rw [heq]
    refine (Finset.stronglyMeasurable_fun_sum (Finset.range m) fun j _ =>
      (hWm j).mono ((filt sz).le (j + 1))).norm.pow 4
  have hdom : Integrable (fun ω =>
      2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4 + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4))
      Cm.Pp := (hre.1.add him.1).const_mul 2
  have hint : Integrable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) Cm.Pp :=
    hdom.mono' hsm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4 ∂Cm.Pp
      ≤ ∫ ω, 2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4
          + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4) ∂Cm.Pp := integral_mono hint hdom hpt
    _ = 2 * (∫ ω, (∑ j ∈ Finset.range m, (W j ω).re) ^ 4 ∂Cm.Pp
          + ∫ ω, (∑ j ∈ Finset.range m, (W j ω).im) ^ 4 ∂Cm.Pp) := by
        rw [integral_const_mul, integral_add hre.1 him.1]
    _ ≤ 4 * (8 * (∑ j ∈ Finset.range m, v j) ^ 2 + 3 * ∑ j ∈ Finset.range m, w j) := by
        linarith [hre.2.2, him.2.2]

/-- **Markov + union (the moment `Y` tail)** (band `gridAsm_moment4_union`): over all endpoints `m ≤ K` and all labels,
`P{∃ m ≤ K, ∃ a, x ≤ ‖Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} Y_j‖_a} ≤ (K+1) Lc · 4 (8 V² + 3 W) / x⁴`. -/
private theorem GridAssemblyGen_moment4_union {n k : ℕ} {σ : Fin k → Bool}
    {u : ℕ → ℝ} {τ : PathΩ sz → ℕ} (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) {K : ℕ}
    {Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} {v w : ℕ → ℝ}
    (hY : YMomentBoundsNg Cm σ u τ K Y v w) (hv0 : ∀ j < K, 0 ≤ v j) (hw0 : ∀ j < K, 0 ≤ w j)
    {x : ℝ} (hx : 0 < x) :
    Cm.Pp.real {ω | ∃ m ≤ K, ∃ a : Fin k → Zd d (sz.L n), x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) a‖} ≤
      (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
        * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / x ^ 4 := by
  set F : ℕ → (Fin k → Zd d (sz.L n)) → PathΩ sz → ℝ := fun m a ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) a‖ with hFdef
  set Bd : ℝ := 4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)
    with hBd
  have hx4 : 0 < x ^ 4 := by positivity
  have hone : ∀ m ≤ K, ∀ a, Cm.Pp.real {ω | x ≤ F m a ω} ≤ Bd / x ^ 4 := by
    intro m hm a
    obtain ⟨hI, hM⟩ := GridAssemblyGen_moment4_fixed Cm hτ hY hv0 hm a
    have hV : ∑ j ∈ Finset.range m, v j ≤ ∑ j ∈ Finset.range K, v j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        (fun j hj _ => hv0 j (Finset.mem_range.mp hj))
    have hV0 : 0 ≤ ∑ j ∈ Finset.range m, v j := Finset.sum_nonneg fun j hj =>
      hv0 j (by have := Finset.mem_range.mp hj; omega)
    have hW : ∑ j ∈ Finset.range m, w j ≤ ∑ j ∈ Finset.range K, w j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        (fun j hj _ => hw0 j (Finset.mem_range.mp hj))
    have hMk : ∫ ω, F m a ω ^ 4 ∂Cm.Pp ≤ Bd := by
      refine hM.trans ?_
      rw [hBd]
      have : (∑ j ∈ Finset.range m, v j) ^ 2 ≤ (∑ j ∈ Finset.range K, v j) ^ 2 :=
        pow_le_pow_left₀ hV0 hV 2
      linarith
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => by positivity) hI (x ^ 4)
    have hset : {ω | x ≤ F m a ω} = {ω | x ^ 4 ≤ F m a ω ^ 4} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h; exact pow_le_pow_left₀ hx.le h 4
      · intro h
        exact (pow_le_pow_iff_left₀ hx.le (norm_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp h
    rw [hset, le_div_iff₀ hx4]
    calc Cm.Pp.real {ω | x ^ 4 ≤ F m a ω ^ 4} * x ^ 4
        = x ^ 4 * Cm.Pp.real {ω | x ^ 4 ≤ F m a ω ^ 4} := by ring
      _ ≤ ∫ ω, F m a ω ^ 4 ∂Cm.Pp := hmark
      _ ≤ Bd := hMk
  have hincl : {ω | ∃ m ≤ K, ∃ a, x ≤ F m a ω}
      ⊆ ⋃ m ∈ Finset.range (K + 1), ⋃ a : Fin k → Zd d (sz.L n), {ω | x ≤ F m a ω} := by
    rintro ω ⟨m, hm, a, ha⟩
    simp only [Set.mem_iUnion]
    exact ⟨m, Finset.mem_range.mpr (by omega), a, ha⟩
  calc Cm.Pp.real {ω | ∃ m ≤ K, ∃ a, x ≤ F m a ω}
      ≤ Cm.Pp.real (⋃ m ∈ Finset.range (K + 1), ⋃ a : Fin k → Zd d (sz.L n), {ω | x ≤ F m a ω}) :=
        measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ m ∈ Finset.range (K + 1), Cm.Pp.real
          (⋃ a : Fin k → Zd d (sz.L n), {ω | x ≤ F m a ω}) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ Finset.range (K + 1), ∑ a : Fin k → Zd d (sz.L n),
          Cm.Pp.real {ω | x ≤ F m a ω} :=
        Finset.sum_le_sum fun m _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ _m ∈ Finset.range (K + 1), ∑ _a : Fin k → Zd d (sz.L n), Bd / x ^ 4 := by
        refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun a _ => ?_
        exact hone m (by have := Finset.mem_range.mp hm; omega) a
    _ = (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * Bd / x ^ 4 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_range, nsmul_eq_mul,
          nsmul_eq_mul]
        push_cast
        ring

end YMoment

/-! ## 6. The single-scale core and the assembled bound -/

section Core

variable {d : ℕ} {sz : Sizes d}

/-- **The single-scale core of `assembledNg`** (band `gridAsm_core`), with free thresholds `lam ≥ 0`
(Azuma, first-chaos part `Z`) and `xY > 0` (fourth-moment tail, second-order part `Y`).  The sharp restricted `κ, ε` act only
on `A0` and the drift; the remainder `R` uses the coarse `(1 + (1 - u_m)⁻¹)^k` from the kernel class `hKer` (its near-identity conjunct). -/
private theorem GridAssemblyGen_core (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] {n k : ℕ} {σ : Fin k → Bool}
    {u : ℕ → ℝ} {τ : PathΩ sz → ℕ} {Δ : ℝ} {K : ℕ}
    {Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop}
    {A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} {A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ}
    {Dr Z Y R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} {κ εK : ℕ → ℕ → ℝ} {δ0 : ℝ}
    {dDrift δD : ℕ → PathΩ sz → ℝ} {c : ℕ → (Fin k → Zd d (sz.L n)) → ℕ → ℝ≥0}
    {v w stepErr : ℕ → ℝ}
    (hτmeas : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (hZmeas : ∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j))
    (hsubG : ∀ m ≤ K, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
      SubGaussStopNg Cm σ u τ Z m a j (c m a j))
    (h : GridAssemblyHypNg Cm σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr)
    {lam : ℝ} (hlam : 0 ≤ lam) {xY : ℝ} (hxY : 0 < xY) :
    ∃ G : Set (PathΩ sz), Cm.Pp.real Gᶜ ≤
        4 * (K : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4)
        + (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
          * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / xY ^ 4
      ∧ ∀ ω ∈ G, 0 < τ ω → ∀ m ≤ K, ∀ a : Fin k → Zd d (sz.L n),
          ‖A m ω a‖ ≤ κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖))
            + εK 0 m * δ0
            + Δ * ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω)
            + lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ))
            + xY
            + ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j := by
  -- the Azuma event: endpoints `1 ≤ m ≤ K` (the `m = 0` sum is empty)
  set GZ : Set (PathΩ sz) := {ω | ∃ m ∈ Finset.Icc 1 K, ∃ a : Fin k → Zd d (sz.L n),
      lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min m (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Z j ω) a‖} with hGZdef
  have hGZbound : Cm.Pp.real GZ ≤
      4 * (K : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4) := by
    set E' : ℕ → (Fin k → Zd d (sz.L n)) → Set (PathΩ sz) := fun m a =>
      {ω | lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min m (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Z j ω) a‖} with hE'def
    have hincl : GZ ⊆ ⋃ m ∈ Finset.Icc 1 K, ⋃ a : Fin k → Zd d (sz.L n), E' m a := by
      rintro ω ⟨m, hm, a, ha⟩
      simp only [Set.mem_iUnion]
      exact ⟨m, hm, a, ha⟩
    have hone : ∀ m ∈ Finset.Icc 1 K, ∀ a : Fin k → Zd d (sz.L n),
        Cm.Pp.real (E' m a) ≤ 4 * Real.exp (-lam ^ 2 / 4) := by
      intro m hm a
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmK : m ≤ K := (Finset.mem_Icc.mp hm).2
      have hcpos : 0 < ∑ j ∈ Finset.range m, (c m a j : ℝ) := h.hc_pos m hm1 hmK a
      have hx0 : 0 ≤ lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by positivity
      have hax := GridAssemblyGen_azuma_UN Cm σ u hτmeas m (fun j _ => hZmeas j) a (c m a)
        (hsubG m hmK a) hx0
      have hxsq : (lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ))) ^ 2
          = lam ^ 2 * ∑ j ∈ Finset.range m, (c m a j : ℝ) := by
        rw [mul_pow, Real.sq_sqrt hcpos.le]
      rw [hxsq] at hax
      have hexp : -(lam ^ 2 * ∑ j ∈ Finset.range m, (c m a j : ℝ)) /
          (4 * ∑ j ∈ Finset.range m, (c m a j : ℝ)) = -lam ^ 2 / 4 := by
        field_simp
      rw [hexp] at hax
      exact hax
    calc Cm.Pp.real GZ
        ≤ Cm.Pp.real (⋃ m ∈ Finset.Icc 1 K, ⋃ a : Fin k → Zd d (sz.L n), E' m a) :=
          measureReal_mono hincl (measure_ne_top _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 K, Cm.Pp.real (⋃ a : Fin k → Zd d (sz.L n), E' m a) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 K, ∑ a : Fin k → Zd d (sz.L n), Cm.Pp.real (E' m a) :=
          Finset.sum_le_sum fun m _ => measureReal_iUnion_fintype_le _
      _ ≤ ∑ _m ∈ Finset.Icc 1 K, ∑ _a : Fin k → Zd d (sz.L n), 4 * Real.exp (-lam ^ 2 / 4) :=
          Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun a _ => hone m hm a
      _ = 4 * (K : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4) := by
          rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Finset.card_univ, nsmul_eq_mul,
            nsmul_eq_mul]
          have hcard : K + 1 - 1 = K := by omega
          rw [hcard]
          ring
  -- the fourth-moment `Y` event
  set GY : Set (PathΩ sz) := {ω | ∃ m ≤ K, ∃ a : Fin k → Zd d (sz.L n), xY ≤
      ‖∑ j ∈ Finset.range (min m (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) a‖} with hGYdef
  have hGYbound : Cm.Pp.real GY ≤ (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
      * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / xY ^ 4 :=
    GridAssemblyGen_moment4_union Cm hτmeas h.hY h.hv0 h.hw0 hxY
  -- the full-measure events `hexp`, `hR`
  have hexpAll : ∀ᵐ ω ∂Cm.Pp, ∀ m, m ≤ K → A m ω = Step2Gen_UN Cm.toFlowFM n σ (u 0) (u m) (A0 ω)
      + ∑ j ∈ Finset.range (min m (τ ω)), Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m)
          ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) := by
    refine ae_all_iff.mpr fun m => ?_
    by_cases hm : m ≤ K
    · filter_upwards [h.hexp m hm] with ω hω _ using hω
    · exact ae_of_all _ fun ω hm' => absurd hm' hm
  have hAllAE := hexpAll.and h.hR
  set Ω0c : Set (PathΩ sz) := {ω | ¬ ((∀ m, m ≤ K → A m ω = Step2Gen_UN Cm.toFlowFM n σ (u 0) (u m) (A0 ω)
      + ∑ j ∈ Finset.range (min m (τ ω)), Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m)
          ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)) ∧
      (∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j))} with hΩ0cdef
  have hΩ0cnull : Cm.Pp.real Ω0c = 0 := by
    have h0 : Cm.Pp Ω0c = 0 := (MeasureTheory.ae_iff).mp hAllAE
    simp [Measure.real, h0]
  refine ⟨(GZ ∪ GY ∪ Ω0c)ᶜ, ?_, ?_⟩
  · rw [compl_compl]
    calc Cm.Pp.real (GZ ∪ GY ∪ Ω0c)
        ≤ Cm.Pp.real (GZ ∪ GY) + Cm.Pp.real Ω0c := measureReal_union_le _ _
      _ ≤ (Cm.Pp.real GZ + Cm.Pp.real GY) + Cm.Pp.real Ω0c := by
          have h1 := measureReal_union_le (μ := Cm.Pp) GZ GY
          linarith
      _ ≤ _ := by rw [hΩ0cnull]; linarith
  · intro ω hω hτpos m hmK a
    have hωGZ : ω ∉ GZ := fun h' => hω (Or.inl (Or.inl h'))
    have hωGY : ω ∉ GY := fun h' => hω (Or.inl (Or.inr h'))
    have hωΩ0 : ω ∉ Ω0c := fun h' => hω (Or.inr h')
    have hAllω : (∀ m, m ≤ K → A m ω = Step2Gen_UN Cm.toFlowFM n σ (u 0) (u m) (A0 ω)
        + ∑ j ∈ Finset.range (min m (τ ω)), Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m)
            ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)) ∧
        (∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j) := by
      by_contra hc
      exact hωΩ0 hc
    obtain ⟨hAll, hRall⟩ := hAllω
    set INIT : ℂ := Step2Gen_UN Cm.toFlowFM n σ (u 0) (u m) (A0 ω) a with hINITdef
    set S1 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Dr j ω) a with hS1def
    set S2 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Z j ω) a with hS2def
    set S3 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) a with hS3def
    set S4 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (R j ω) a with hS4def
    have hAeq : A m ω a = INIT + ((Δ : ℂ) * S1 + S2 + S3 + S4) := by
      rw [hAll m hmK, Pi.add_apply, Finset.sum_apply]
      congr 1
      rw [Finset.sum_congr rfl (fun j _ => GridAssemblyGen_UN_four Cm.toFlowFM n σ (u (j + 1)) (u m)
        (Δ : ℂ) (Dr j ω) (Z j ω) (Y j ω) (R j ω) a), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hINITle : ‖INIT‖
        ≤ κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) + εK 0 m * δ0 := by
      obtain ⟨b0⟩ := (inferInstance : Nonempty (Fin k → Zd d (sz.L n)))
      have hA0nn : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖) :=
        le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖A0 ω b‖) (Finset.mem_univ b0))
      exact h.hker 0 m (Nat.zero_le m) hmK (A0 ω) _ δ0 hA0nn h.hδ0
        (fun b => Finset.le_sup' (fun b => ‖A0 ω b‖) (Finset.mem_univ b)) (h.hA0cls ω hτpos) a
    have hS1le : ‖S1‖ ≤ ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) := by
      have h2 : ∀ j ∈ Finset.range (min m (τ ω)),
          ‖Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Dr j ω) a‖
            ≤ κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω := by
        intro j hj
        have hjm : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _)
        have hjτ : j < τ ω := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        exact h.hker (j + 1) m hjm hmK (Dr j ω) (dDrift j ω) (δD j ω)
          (h.hdDrift0 ω j (by omega)) (h.hδD0 ω j (by omega)) (h.hdrift ω j (by omega) hjτ)
          (h.hDcls ω j (by omega) hjτ) a
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h2).trans ?_)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_left _ _)) ?_
      intro j hj _
      have hjm : j < m := Finset.mem_range.mp hj
      exact add_nonneg (mul_nonneg (h.hκ0 (j + 1) m hjm hmK) (h.hdDrift0 ω j (by omega)))
        (mul_nonneg (h.hε0 (j + 1) m hjm hmK) (h.hδD0 ω j (by omega)))
    have hS1le' : ‖(Δ : ℂ) * S1‖
        ≤ Δ * ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h.hΔ0]
      exact mul_le_mul_of_nonneg_left hS1le h.hΔ0
    have hS2le : ‖S2‖ ≤ lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by
      by_cases hm0 : m = 0
      · subst hm0
        simp [hS2def]
      · have hlt : ‖S2‖ < lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by
          by_contra hc
          push Not at hc
          exact hωGZ ⟨m, Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0, hmK⟩, a, hc⟩
        exact hlt.le
    have hS3le : ‖S3‖ ≤ xY := by
      by_contra hc
      push Not at hc
      exact hωGY ⟨m, hmK, a, hc.le⟩
    have hS4le : ‖S4‖ ≤ ∑ j ∈ Finset.range m, (1 + (1 - u m) ⁻¹) ^ k * stepErr j := by
      have hm0 := h.hu0 m hmK
      have hm1 := h.hu1 m hmK
      have h2 : ∀ j ∈ Finset.range (min m (τ ω)),
          ‖Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (R j ω) a‖
            ≤ (1 + (1 - u m) ⁻¹) ^ k * stepErr j := by
        intro j hj
        have hjm : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _)
        have hjτ : j < τ ω := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        exact GridAssemblyGen_norm_UN_coarse h.hKer σ
          (h.hu0 (j + 1) (by omega)) (h.hu1 (j + 1) (by omega)) hm0 hm1
          (h.hstepErr0 j (by omega)) (hRall j (by omega) hjτ) a
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h2).trans ?_)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_left _ _)) ?_
      intro j hj _
      have hjm : j < m := Finset.mem_range.mp hj
      have hpos : 0 < 1 - u m := by linarith
      exact mul_nonneg (by positivity) (h.hstepErr0 j (by omega))
    rw [hAeq]
    calc ‖INIT + ((Δ : ℂ) * S1 + S2 + S3 + S4)‖
        ≤ ‖INIT‖ + ‖(Δ : ℂ) * S1‖ + ‖S2‖ + ‖S3‖ + ‖S4‖ := by
          have e1 := norm_add_le INIT ((Δ : ℂ) * S1 + S2 + S3 + S4)
          have e2 := norm_add_le ((Δ : ℂ) * S1 + S2 + S3) S4
          have e3 := norm_add_le ((Δ : ℂ) * S1 + S2) S3
          have e4 := norm_add_le ((Δ : ℂ) * S1) S2
          linarith
      _ ≤ _ := by linarith

/-- **`assembledNg`** (the statement `AssembledNg`; band `assembledN`).  Proof outline: `SizeTendsto` turns
the real-variable Azuma budget (`gridAsm_zBudget`) into an eventual statement in `n`; the single-scale core at `lam = N^ε`,
`xY = N^{-D} > 0` gives an event `G` with `P(Gᶜ) ≤ 4 K Lc exp(-N^{2ε}/4) + (K+1) Lc · 4 (8 V² + 3 W) / xY⁴`; the first term is
`≤ N^{-D₁}/2` by the Azuma budget and the second by `gridAsm_moment4_budget_le` and `gridAsm_yBudget` (exponent
`D₁ + 4D + k + 2C_P + 8 ≤ C_K`, label count `Lc ≤ N^k`).  The probability budget is the only place where `sz.SizeTendsto` is
used; the carrier enters through `hKer` (coarse bound) and the law `Cm.Pp` only. -/
theorem assembledNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] : AssembledNg Cm := by
  intro hSize k ε hε D D₁ C_P C_K hCK0 hCK
  filter_upwards [hSize.eventually (gridAsm_zBudget k hε D₁ C_K hCK0)] with n hn
  obtain ⟨hN2, hbudZ⟩ := hn
  intro K σ u τ Δ Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr P hK1 hK hΔ hKΔ hP0 hP hv
    hw hτmeas hZmeas hsubG h
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hx : 0 < ((sz.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨G, hG, hbd⟩ := GridAssemblyGen_core Cm hτmeas hZmeas hsubG h
    (Real.rpow_nonneg hN0.le ε) hx
  refine ⟨G, hG.trans ?_, hbd⟩
  have hLc0 : (0 : ℝ) ≤ (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) := Nat.cast_nonneg _
  have hLc : (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ k := by
    exact_mod_cast gridAsm_card_label sz n k
  have hZ := hbudZ K _ hK hLc0 hLc
  have hbud := gridAsm_moment4_budget_le h.hΔ0 hP0 hKΔ hK1 h.hv0 h.hw0 hv hw
  have hY := gridAsm_yBudget hN2 k hCK hLc0 hLc h.hΔ0 hΔ hP0 hP
  have hx4 : 0 < (((sz.size n : ℕ) : ℝ) ^ (-D)) ^ 4 := by positivity
  have hYle : (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
      * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
        / (((sz.size n : ℕ) : ℝ) ^ (-D)) ^ 4 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) / 2 := by
    refine le_trans ?_ hY
    rw [show (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
        * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
        = (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * ((K + 1 : ℝ)
          * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))) by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbud hLc0) hx4.le
  linarith

end Core

/-! ## 7. Band bridges (`bandStep2Mat sz E`) -/

section BandBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ)

/-- `YMomentBoundsN` is `YMomentBoundsNg` at `bandStep2Mat` (`stoppedEdgeN = stoppedEdgeNg`; the law `pathP sz` is `Cm.Pp`). -/
theorem bandStep2_YMomentBoundsN {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ) (K : ℕ)
    (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (v w : ℕ → ℝ) :
    RBM.Ind.YMomentBoundsN sz (E n) σ u τ K Y v w ↔ YMomentBoundsNg (bandStep2Mat sz E) σ u τ K Y v w := by
  unfold RBM.Ind.YMomentBoundsN YMomentBoundsNg
  simp only [bandStep2_stoppedEdgeN]
  exact Iff.rfl

end BandBridge

end RBM.BA

end
