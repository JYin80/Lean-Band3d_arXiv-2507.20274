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
# The assembly of the stopped grid walk over the carrier (BA-T row T4s2b, ticket T2473, target 7)

Generic forms of `Induction/GridAssemblyN.lean` (not edited) over a carrier `Cm : Step2Mat sz`,
namespace `RBM.BA`, no `BA/*` import.  Amend 1 of T2473 (S1): this is the second row T4s2b,
target 7 (target 6, the per-step vocabulary, is T2474's `StepDecompGen`).

* §1 the pins `qvFormNg`, `StoppedAzumaZNg`, `AzumaSubGNg`, `YMomentBoundsNg`, `YMomentsConclNg`,
  `YMomentsNg`, `GridAssemblyHypNg` (structure), `AssembledNg` (probe texts of
  `RBM3D/Probe/T2473Pins.lean:125-247`): the kernel is `Step2Gen_UN Cm.toFlowFM n`, the field
  `hE : |E| ≤ 2` of the band bundle is the kernel class `GridRepTailGen_Ker` (T2471, K1-K4; the
  coarse bound `(1 + (1 - u_m)⁻¹)^k` follows from K3);
* §2 the coarse row bound; §3 measurability of `ZvecNg` / `YvecNg` under `StepDecompGen_LoopForm`
  and `StepDecompGen_WalkForm` (`GridAssemblyGen_stronglyMeasurable_ZvecNg`, `_YvecNg`);
* §4 the stopped Azuma bound `stoppedAzumaZNg`; §5 the fourth moment of the stopped `Y` sum;
  §6 the single-scale core and the assembled bound `assembledNg`;
* §7 band bridges (`qvFormN`, the bundle, `YMomentBoundsN`) and band corollaries; §8 compiled
  nonempty instances at `d = 3`.

Private band helpers that are model-free are reused by `open private`; the lemmas that read `Ugen`,
`pathP`, `pathH`, `zt E u` are copied and adapted under the stem `GridAssemblyGen_`.
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

/-! ## 1. The pins over the carrier -/

section Pins

variable {d : ℕ} {sz : Sizes d}

/-- `qvFormN` over the carrier (D2 (4)): the real part of T8b's `STeeUMg`; the band bridge is `bandStep2_qvFormN`. -/
def qvFormNg (Cm : Step2Mat sz) (n : ℕ) (v w : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin k → Zd d (sz.L n)) : ℝ :=
  (STeeUMg Cm n v w M σ a).re

/-- **Pin `StoppedAzumaZNg`** (`StoppedAzumaZN`, `GridAssemblyN:87`): `ZvecNg`, `Step2Gen_UN`; the premise `|E n| < 2` is
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

/-- **Pin `AzumaSubGNg`** (`AzumaSubGN`, `GridAssemblyN:122`): the walk coupling `g` enters only through `gvarF`; the
increment is `ZfamNg` (`Cm.Hpath`); the theorem is the band `azumaSubGN` at `sz.withLam g` under `StepDecompGen_WalkForm`
(T4s2c). -/
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

/-- `YMomentBoundsN` (`GridAssemblyN:141`) over the carrier. -/
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

/-- `YMomentsConclN` over the carrier. -/
def YMomentsConclNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ) (σ : Fin k → Bool) : Prop :=
  ∃ C_P : ℝ, 0 ≤ C_P ∧
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsNg Cm σ (gridTime s t K n) τ (K n) (fun j ω => YvecNg Cm s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

/-- `YMomentsN` over the carrier: `0 < κ`, `|E n| ≤ 2 - κ` become `DecayGen_Spec` (`κm ≤ Im m`, `η = (1 - t) Im m`). -/
def YMomentsNg (Cm : Step2Mat sz) (κm τ' : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  DecayGen_Spec Cm.toFlowFM κm → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  (∀ n, K n ≠ 0) → sz.SizeTendsto → sz.RangeCond τ' t →
  ∀ (k : ℕ) (σ : Fin k → Bool), YMomentsConclNg Cm s t K k σ

/-- `GridAssemblyHypN` (`GridAssemblyN:183`) over the carrier: the field `hE : |E| ≤ 2` becomes `hKer` (T2471's K1-K4,
one text; K3 gives the coarse bound), the kernel is `Step2Gen_UN Cm.toFlowFM n`. -/
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

/-- **Pin `AssembledNg`** (`AssembledN`, `GridAssemblyN:227`) over the carrier. -/
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
`GridAssemblyN:556`). -/
private theorem GridAssemblyGen_stronglyMeasurable_UN_apply {Ω' : Type*} {m : MeasurableSpace Ω'} (C : FlowFM sz)
    (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) {W : Ω' → (Fin k → Zd d (sz.L n)) → ℂ}
    (hW : StronglyMeasurable[m] W) (a : Fin k → Zd d (sz.L n)) :
    StronglyMeasurable[m] (fun ω => Step2Gen_UN C n σ v w (W ω) a) := by
  have hcont : Continuous (fun A : (Fin k → Zd d (sz.L n)) → ℂ => Step2Gen_UN C n σ v w A a) := by
    unfold Step2Gen_UN
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

/-- `Step2Gen_UN` of the four-term increment `Δ D + Z + Y + R`, at one label (band `gridAsm_Ugen_four`, `:566`). -/
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

/-- **The one-slot row bound from K3** (`‖uKer_{v,w}‖_{ℓ^∞} ≤ 1 + (1 - w)⁻¹` for `0 ≤ v, w < 1`, no order between `v` and `w`;
band `gridAsm_norm_uKer_le`, `:586`, where `|w - v| ≤ 1` replaces `w - v`). -/
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

/-- **The coarse row-sum kernel bound of `Step2Gen_UN`** (band `gridAsm_norm_Ugen_coarse`, `GridAssemblyN:616`; the kernel class
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
`gridAsm_measurable_loopDerivN` (`GridAssemblyN:851`) at the spectral value `ztOf (Cm.m n) (E n) u`. -/

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

/-- Under `WalkForm` the carrier walk is adapted to the coordinate filtration (`pathH_measurable_filt`). -/
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

/-- The `b`-th component of `ZvecNg` is `filt sz (j + 1)`-measurable (band `gridAsm_measurable_ZvecN_apply`, `:897`). -/
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

/-- The `b`-th component of `martIncNg` is `filt sz (j + 1)`-measurable (band `gridAsm_measurable_martIncN_apply`, `:915`). -/
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
(band `gridAsm_stronglyMeasurable_ZvecN`, `GridAssemblyN:927`). -/
theorem GridAssemblyGen_stronglyMeasurable_ZvecNg (hL : StepDecompGen_LoopForm Cm E)
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => ZvecNg Cm s t K n j σ ω) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt sz (j + 1)) _ _ fun b =>
    GridAssemblyGen_measurable_ZvecNg_apply hL hW s t K n j σ b

/-- **`YvecNg = martIncNg - ZvecNg` is `filt sz (j + 1)`-strongly measurable** (the first field of `YMomentBoundsNg`; band
`gridAsm_stronglyMeasurable_YvecN`, `:937`). -/
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

/-- The label-weighted Azuma tail for a fixed target `m` and label `a` and an arbitrary step-indexed increment `Z`
(`Z j` is `filt (j+1)`-strongly measurable for `j < m`): `sum_stopped` rewrites the stopped sum as `Σ_{j<m} 1{j<τ}
(𝒰_{u_{j+1},u_m} Z_j)_a` and `azuma_complex` (via `gridAsm_azuma_step`) gives the tail (band `gridAsm_azuma_Ugen`, `:959`). -/
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

/-- **Target 7, `stoppedAzumaZNg`** (the pin `StoppedAzumaZNg`; band `stoppedAzumaZN`, `GridAssemblyN:1014`): the stopped
Azuma bound for the first-chaos part `ZvecNg`, real and imaginary parts sub-Gaussian with the common proxy `c j` (input
`SubGaussStopNg`, the output of `azumaSubGNg`).  The measurability input of `azuma_complex` is
`GridAssemblyGen_stronglyMeasurable_ZvecNg` (`LoopForm` and `WalkForm`); the window premises of the pin are not needed.  This
is a conditional adapter: the sub-Gaussian hypothesis is an input of the pin. -/
theorem stoppedAzumaZNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    StoppedAzumaZNg Cm s t K := by
  intro _hs0 _hst _ht1 _hK n k σ τ hτ m _hmK a c hsubG x hx
  exact GridAssemblyGen_azuma_UN Cm σ (gridTime s t K n) hτ m
    (fun j _ => GridAssemblyGen_stronglyMeasurable_ZvecNg hL hW s t K n j σ) a c hsubG hx

end StoppedAzuma

/-! ## 5. The fourth-moment tail of the second-order part `Y` -/

section YMoment

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp]

/-- `stoppedEdgeNg … b j` is `filt sz (j+1)`-strongly measurable (band `gridAsm_stronglyMeasurable_stoppedEdgeN`, `:1205`). -/
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

/-- **The per-target fourth moment of the propagated, stopped `Y` sum** (band `gridAsm_moment4_fixed`, `:1232`): from
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

/-- **Markov + union (the moment `Y` tail)** (band `gridAsm_moment4_union`, `:1296`): over all targets `m ≤ K` and all labels,
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

/-- **The single-scale core of `assembledNg`** (band `gridAsm_core`, `GridAssemblyN:1378`), with free thresholds `lam ≥ 0`
(Azuma, first-chaos part `Z`) and `xY > 0` (fourth-moment tail, second-order part `Y`).  The sharp restricted `κ, ε` act only
on `A0` and the drift; the remainder `R` uses the coarse `(1 + (1 - u_m)⁻¹)^k` from the kernel class `hKer` (K3). -/
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
  -- the Azuma event: targets `1 ≤ m ≤ K` (the `m = 0` sum is empty)
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

/-- **Target 7, `assembledNg`** (the pin `AssembledNg`; band `assembledN`, `GridAssemblyN:1605`).  Route: `SizeTendsto` turns
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

/-! ## 7. Band bridges and band corollaries (`bandStep2Mat sz E`) -/

section BandBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ)

/-- **`qvFormNg` band bridge** (proved, not `rfl`): the pairing of `STeeUMg` is the conjugate pairing of the band `qvFormN`
under K4 (`gridRepTailGen_ker_band`); the hypotheses `|E n| ≤ 2`, `0 ≤ w < 1` are the band window of the kernel class. -/
theorem bandStep2_qvFormN (n : ℕ) (hE : |E n| ≤ 2) {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {k : ℕ}
    (σ : Fin k → Bool) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Fin k → Zd d (sz.L n)) :
    RBM.Ind.qvFormN sz n (E n) v w σ M a = qvFormNg (bandStep2Mat sz E) n v w σ M a := by
  have hK4 := (gridRepTailGen_ker_band sz E n hE).2.2.2
  unfold RBM.Ind.qvFormN qvFormNg STeeUMg
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  have hconj : ∏ i : Fin k, Step2Gen_uKer (bandStep2Mat sz E).toFlowFM n (!σ i) (!σ (finRotate k i)) v w (a i) (b' i) =
      (starRingEnd ℂ) (∏ i : Fin k, Step2Gen_uKer (bandStep2Mat sz E).toFlowFM n (σ i) (σ (finRotate k i)) v w
        (a i) (b' i)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => hK4 _ _ v w hw0 hw1 _ _
  rw [hconj]
  have hfm : (bandStep2Mat sz E).toFlowFM = bandFM sz E := rfl
  simp only [hfm, Step2Kern_uKer_band]
  rfl

/-- `YMomentBoundsN` is `YMomentBoundsNg` at `bandStep2Mat` (`stoppedEdgeN = stoppedEdgeNg`; the law `pathP sz` is `Cm.Pp`). -/
theorem bandStep2_YMomentBoundsN {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ) (K : ℕ)
    (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (v w : ℕ → ℝ) :
    RBM.Ind.YMomentBoundsN sz (E n) σ u τ K Y v w ↔ YMomentBoundsNg (bandStep2Mat sz E) σ u τ K Y v w := by
  unfold RBM.Ind.YMomentBoundsN YMomentBoundsNg
  simp only [bandStep2_stoppedEdgeN]
  exact Iff.rfl

/-- **Band bridge of the bundle**: the band bundle `GridAssemblyHypN` at the energy `E n` is `GridAssemblyHypNg` at
`bandStep2Mat sz E` (`hE` gives the kernel class by `gridRepTailGen_ker_band`; `Ugen = Step2Gen_UN` by `bandStep2_Ugen`;
`stoppedEdgeN = stoppedEdgeNg`). -/
theorem bandStep2_GridAssemblyHypN {n k : ℕ} {σ : Fin k → Bool} {u : ℕ → ℝ}
    {τ : PathΩ sz → ℕ} {Δ : ℝ} {K : ℕ}
    {Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop}
    {A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ}
    {A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ}
    {Dr Z Y R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ}
    {κ εK : ℕ → ℕ → ℝ} {δ0 : ℝ} {dDrift δD : ℕ → PathΩ sz → ℝ}
    {c : ℕ → (Fin k → Zd d (sz.L n)) → ℕ → ℝ≥0} {v w stepErr : ℕ → ℝ}
    (h : RBM.Ind.GridAssemblyHypN sz (E n) σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr) :
    GridAssemblyHypNg (bandStep2Mat sz E) σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr := by
  have hU : ∀ (v' w' : ℝ) (X : (Fin k → Zd d (sz.L n)) → ℂ),
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v' w' X =
        Step2Gen_UN (bandStep2Mat sz E).toFlowFM n σ v' w' X := fun v' w' X => bandStep2_Ugen sz E n σ v' w' X
  exact
    { hKer := gridRepTailGen_ker_band sz E n h.hE
      hu0 := h.hu0
      hu1 := h.hu1
      hΔ0 := h.hΔ0
      hexp := fun m hm => by
        filter_upwards [h.hexp m hm] with ω hω
        rw [hω]
        simp only [hU]
      hκ0 := h.hκ0
      hε0 := h.hε0
      hker := fun i m him hm X M δ hM hδ hX hc a => by
        rw [← hU]
        exact h.hker i m him hm X M δ hM hδ hX hc a
      hδ0 := h.hδ0
      hA0cls := h.hA0cls
      hdDrift0 := h.hdDrift0
      hδD0 := h.hδD0
      hdrift := h.hdrift
      hDcls := h.hDcls
      hc_pos := h.hc_pos
      hv0 := h.hv0
      hw0 := h.hw0
      hY := (bandStep2_YMomentBoundsN sz E σ u τ K Y v w).1 h.hY
      hstepErr0 := h.hstepErr0
      hR := h.hR }

/-- **Band corollary of `stoppedAzumaZNg`**: the merged band pin `StoppedAzumaZN` (`GridAssemblyN:87`) from the generic
theorem at `bandStep2Mat sz E` (`LoopForm`, `WalkForm` by `stepDecompGen_loopForm_band`, `stepDecompGen_walkForm_band`;
`ZvecN = ZvecNg`, `Ugen = Step2Gen_UN`). -/
theorem stoppedAzumaZN_of_Ng (s t : ℕ → ℝ) (K : ℕ → ℕ) : RBM.Ind.StoppedAzumaZN sz E s t K := by
  intro hE hs hst ht1 hK n k σ τ hτ m hm a c hsub x hx
  have hZ : (fun j ω => RBM.Ind.ZvecN sz E s t K n j σ ω) =
      fun j ω => ZvecNg (bandStep2Mat sz E) s t K n j σ ω :=
    funext fun j => funext fun ω => bandStep2_ZvecN sz E s t K n j σ ω
  have h := stoppedAzumaZNg (bandStep2Mat sz E) (stepDecompGen_loopForm_band sz E hE)
    (stepDecompGen_walkForm_band sz E) s t K hs hst ht1 hK n k σ τ hτ m hm a c (fun j hj => by
      rw [← hZ]
      exact (bandStep2_SubGaussStopN sz E σ (gridTime s t K n) τ _ m a j (c j)).1 (hsub j hj)) x hx
  have e : ∀ ω : PathΩ sz, ∑ j ∈ Finset.range (min m (τ ω)), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ
        (gridTime s t K n (j + 1)) (gridTime s t K n m) (RBM.Ind.ZvecN sz E s t K n j σ ω) a =
      ∑ j ∈ Finset.range (min m (τ ω)), Step2Gen_UN (bandStep2Mat sz E).toFlowFM n σ
        (gridTime s t K n (j + 1)) (gridTime s t K n m) (ZvecNg (bandStep2Mat sz E) s t K n j σ ω) a :=
    fun ω => Finset.sum_congr rfl fun j _ => by rw [bandStep2_Ugen, bandStep2_ZvecN]; rfl
  simp only [e]
  exact h

/-- **Band corollary of `assembledNg`** at `bandStep2Mat sz E`: the band pin `AssembledN` (`GridAssemblyN:227`) with the energy
fixed to the sequence `E` (inside `∀ᶠ n` the band pin quantifies `E : ℝ`; the generic pin is per carrier, so this is its
`E n`-slice).  The bundle is converted by `bandStep2_GridAssemblyHypN`, the sub-Gaussian input by `bandStep2_SubGaussStopN`,
the conclusion is unchanged (`A` is the same function). -/
example : sz.SizeTendsto → ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ (D D₁ C_P C_K : ℝ), 0 ≤ C_K →
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
      (∀ m ≤ K, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
        RBM.Ind.SubGaussStopN sz (E n) σ u τ Z m a j (c m a j)) →
      RBM.Ind.GridAssemblyHypN sz (E n) σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr →
      ∃ G : Set (PathΩ sz), (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G, 0 < τ ω → ∀ m ≤ K, ∀ a : Fin k → Zd d (sz.L n),
          ‖A m ω a‖ ≤
            κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) + εK 0 m * δ0 +
            Δ * ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) +
            ((sz.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) +
            ((sz.size n : ℕ) : ℝ) ^ (-D) +
            ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j := by
  intro hS k ε hε D D₁ C_P C_K hC hCK
  filter_upwards [assembledNg (bandStep2Mat sz E) hS k ε hε D D₁ C_P C_K hC hCK] with n hn
  intro K σ u τ Δ Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr P hK1 hK hΔ hKΔ hP0 hP hv hw hτ hZ hsub h
  exact hn K σ u τ Δ Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr P hK1 hK hΔ hKΔ hP0 hP hv hw hτ hZ
    (fun m hm a j hj => (bandStep2_SubGaussStopN sz E σ u τ Z m a j (c m a j)).1 (hsub m hm a j hj))
    (bandStep2_GridAssemblyHypN sz E h)

end BandBridge

/-! ## 8. Compiled nonempty instances (`d = 3`, `sz0`, the band carrier at `E ≡ 1/2`) -/

section Inst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst RBM.Ind.GridAssemblyNInst

/-- The band carrier at the instance energy `E ≡ 1/2` (`gridAsm_E`) on the merged sizes `sz0`. -/
private abbrev GridAssemblyGen_Cm : Step2Mat sz0 := bandStep2Mat sz0 gridAsm_E

private theorem GridAssemblyGen_hL : StepDecompGen_LoopForm GridAssemblyGen_Cm gridAsm_E :=
  stepDecompGen_loopForm_band sz0 gridAsm_E gridAsm_E_abs_lt

private theorem GridAssemblyGen_hW : StepDecompGen_WalkForm GridAssemblyGen_Cm sz0.lam (fun _ => 0) :=
  stepDecompGen_walkForm_band sz0 gridAsm_E

/-- Instance of `GridAssemblyGen_stronglyMeasurable_ZvecNg` and `_YvecNg` at `n = 0`, `j = 2`, `σ = (+,+,-)`, the window
`(0, 1/16)` with `K_n = N_n^{17}`: `LoopForm` and `WalkForm` are the band lemmas. -/
example : StronglyMeasurable[filt sz0 (2 + 1)]
      (fun ω => ZvecNg GridAssemblyGen_Cm sInst tInst gridAsm_K 0 2 ![true, true, false] ω) ∧
    StronglyMeasurable[filt sz0 (2 + 1)]
      (fun ω => YvecNg GridAssemblyGen_Cm sInst tInst gridAsm_K 0 2 ![true, true, false] ω) :=
  ⟨GridAssemblyGen_stronglyMeasurable_ZvecNg GridAssemblyGen_hL GridAssemblyGen_hW _ _ _ 0 2 _,
    GridAssemblyGen_stronglyMeasurable_YvecNg GridAssemblyGen_hL GridAssemblyGen_hW _ _ _ 0 2 _⟩

/-- **Instance of `stoppedAzumaZNg`** at the band carrier, `n = 0` (`L = 4`, `W = 32`, `N = 2097152`), the merged grid
`(sInst, vg, Kg)` (`Kg 0 = 4` steps), `k = 3`, `σ = (+,+,-)`, label `a = 0`, `τ ≡ m ≡ 4`, a constant proxy `C > 0` and the
threshold `x = 4 √(4 C)`: the tail is `< 1` (it is at most `4 e^{-4}`, `gridAsm_stoppedAzumaZN_bound_lt_one`).  Every
deterministic hypothesis is discharged; only the sub-Gaussian family for `ZvecNg` (the output of `azumaSubGNg`, row T4s2c)
stays a hypothesis. -/
example (C : ℝ≥0) (hC : 0 < C)
    (hsub : ∀ j < Kg 0, SubGaussStopNg GridAssemblyGen_Cm ![true, true, false] (gridTime sInst vg Kg 0) (fun _ => Kg 0)
      (fun j ω => ZvecNg GridAssemblyGen_Cm sInst vg Kg 0 j ![true, true, false] ω) (Kg 0) (fun _ => 0) j C) :
    GridAssemblyGen_Cm.Pp.real {ω | 4 * Real.sqrt ((Kg 0 : ℝ) * (C : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min (Kg 0) (Kg 0)), Step2Gen_UN GridAssemblyGen_Cm.toFlowFM 0 ![true, true, false]
          (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 (Kg 0))
          (ZvecNg GridAssemblyGen_Cm sInst vg Kg 0 j ![true, true, false] ω) (fun _ => 0)‖} < 1 := by
  have h := stoppedAzumaZNg GridAssemblyGen_Cm GridAssemblyGen_hL GridAssemblyGen_hW sInst vg Kg
    (fun n => by simp [sInst]) (fun n => by norm_num [sInst, vg]) (fun n => by norm_num [vg])
    (fun n => by simp [Kg]) 0 3 ![true, true, false] (fun _ => Kg 0) (fun j => MeasurableSet.const _)
    (Kg 0) le_rfl (fun _ => 0) (fun _ => C) hsub (4 * Real.sqrt ((Kg 0 : ℝ) * (C : ℝ))) (by positivity)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  exact lt_of_le_of_lt h (gridAsm_stoppedAzumaZN_bound_lt_one 0 hC)

/-- **`assembledNg` at the instance data, with an arbitrary first-chaos increment `Z`**: `k = 3`, any `ε > 0`, `D`, `D₁`, `C_P`
with `D₁ + 4D + 3 + 2C_P + 8 ≤ C_K = 17`, the window `(0, 1/16)`, the grid `K_n = N_n^{17}` (`gridAsm_K`) with `τ ≡ K n`,
`Δ = gridStep`, `P = 1` (`v = Δ²`, `w = Δ⁴`), `A_0 ≡ 1`, `Dr = Y = R = 0`, `A` the process
`𝒰_{u_0,u_m} A_0 + Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} Z_j`.  Discharged: `SizeTendsto` (`sz0_tendsto`), the grid, the stopping-time
measurability, the bundle (the band `gridAsm_bundle` through `bandStep2_GridAssemblyHypN`: the kernel class `hKer` is
`gridRepTailGen_ker_band`).  Given any strongly measurable `Z` with the sub-Gaussian input at a constant proxy `cc > 0`,
eventually in `n` there is an event `G` of probability at least `1 - N^{-D₁}` on which the assembled bound holds. -/
private theorem GridAssemblyGen_assembled_instance_gen (ε : ℝ) (hε : 0 < ε) (D D₁ C_P : ℝ)
    (hCK : D₁ + 4 * D + ((3 : ℕ) : ℝ) + 2 * C_P + 8 ≤ 17) (hCP : 0 ≤ C_P) :
    ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 3 → Bool)
      (Z : ℕ → PathΩ sz0 → (Fin 3 → Zd 3 (sz0.L n)) → ℂ) (cc : ℝ≥0), 0 < cc →
      (∀ j, StronglyMeasurable[filt sz0 (j + 1)] (Z j)) →
      (∀ m ≤ gridAsm_K n, ∀ (a : Fin 3 → Zd 3 (sz0.L n)) (j : ℕ), j < m →
        SubGaussStopNg GridAssemblyGen_Cm σ (gridTime sInst tInst gridAsm_K n) (fun _ => gridAsm_K n) Z m a j cc) →
      ∃ G : Set (PathΩ sz0), GridAssemblyGen_Cm.Pp.real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G, ∀ m ≤ gridAsm_K n, ∀ a : Fin 3 → Zd 3 (sz0.L n),
          ‖Step2Gen_UN GridAssemblyGen_Cm.toFlowFM n σ (gridTime sInst tInst gridAsm_K n 0)
              (gridTime sInst tInst gridAsm_K n m) (fun _ => (1 : ℂ)) a +
            ∑ j ∈ Finset.range m, Step2Gen_UN GridAssemblyGen_Cm.toFlowFM n σ
              (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m) (Z j ω) a‖ ≤
            (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 +
              ((sz0.size n : ℕ) : ℝ) ^ ε * Real.sqrt (m * cc) +
              ((sz0.size n : ℕ) : ℝ) ^ (-D) := by
  filter_upwards [assembledNg GridAssemblyGen_Cm sz0_tendsto 3 ε hε D D₁ C_P 17 (by norm_num) hCK] with n hn
  intro σ Z cc hcc hZmeas hsub
  have hΔ0 : 0 ≤ gridStep sInst tInst gridAsm_K n := (gridAsm_step_pos n).le
  obtain ⟨hK1, hK, hΔ, hKΔ⟩ := gridAsm_grid_data n
  have hN1 : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast gridAsm_size_pos n
  have hu0 : ∀ i ≤ gridAsm_K n, 0 ≤ gridTime sInst tInst gridAsm_K n i := fun i hi =>
    (gridAsm_gridTime_bounds n hi).1
  have hu1 : ∀ i ≤ gridAsm_K n, gridTime sInst tInst gridAsm_K n i < 1 := fun i hi =>
    (gridAsm_gridTime_bounds n hi).2.trans_lt (by norm_num)
  obtain ⟨G, hG, hb⟩ := hn (gridAsm_K n) σ (gridTime sInst tInst gridAsm_K n)
    (fun _ => gridAsm_K n) (gridStep sInst tInst gridAsm_K n) (fun _ _ _ => True)
    (fun _ _ => 1)
    (fun m ω => RBM.Ind.Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n 0)
        (gridTime sInst tInst gridAsm_K n m) (fun _ => (1 : ℂ)) +
      ∑ j ∈ Finset.range (min m ((fun _ : PathΩ sz0 => gridAsm_K n) ω)),
        RBM.Ind.Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n (j + 1))
          (gridTime sInst tInst gridAsm_K n m) (Z j ω))
    (fun _ _ _ => 0) Z (fun _ _ _ => 0) (fun _ _ _ => 0)
    (fun _ m => (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3) (fun _ _ => 0) 0
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => cc)
    (fun _ => gridStep sInst tInst gridAsm_K n ^ 2) (fun _ => gridStep sInst tInst gridAsm_K n ^ 4)
    (fun _ => 0) 1 hK1 hK hΔ (by rw [hKΔ]; norm_num) zero_le_one
    (Real.one_le_rpow hN1 hCP)
    (fun _ _ => by simp) (fun _ _ => by simp)
    (fun j => MeasurableSet.const _) hZmeas hsub
    (bandStep2_GridAssemblyHypN sz0 gridAsm_E
      (gridAsm_bundle n σ Z cc hcc (gridTime sInst tInst gridAsm_K n) (gridAsm_E n)
        (gridAsm_E_abs_lt n).le hu0 hu1 (fun _ => gridAsm_K n) _ hΔ0
        (fun _ => gridStep sInst tInst gridAsm_K n ^ 2) (fun _ => gridStep sInst tInst gridAsm_K n ^ 4)
        (fun _ => by positivity) (fun _ => by positivity)))
  refine ⟨G, hG, fun ω hω m hm a => ?_⟩
  have := hb ω hω (gridAsm_K_pos n) m hm a
  have hfm : GridAssemblyGen_Cm.toFlowFM = bandFM sz0 gridAsm_E := rfl
  simpa [hfm, min_eq_left hm, bandStep2_Ugen] using this

/-- **Nondegenerate instance of `assembledNg`** (all hypotheses discharged, no unproved pin): the witness
`Z_j = √Δ · Re tr X_{j+1}` (a genuinely random Gaussian increment, `gridAsm_witZ_ne_zero`), whose sub-Gaussian input is
proved by the band `gridAsm_witSubGaussStop` (through `bandStep2_SubGaussStopN`), `d = 3`, `sz0`, `k = 3`, `σ = (+,+,-)`,
`E ≡ 1/2`, `ε = 1`, `D = D₁ = 1`, `C_P = 0`, `C_K = 17` (exponent count `1 + 4 + 3 + 0 + 8 = 16 ≤ 17`), the window
`(0, 1/16)` and the grid `K_n = N_n^{17}`.  Eventually in `n`, on an event of probability at least `1 - N^{-1}`, for every
`m ≤ K n` and label `a` the assembled process is bounded as stated. -/
example : ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz0),
    GridAssemblyGen_Cm.Pp.real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
    ∀ ω ∈ G, ∀ m ≤ gridAsm_K n, ∀ a : Fin 3 → Zd 3 (sz0.L n),
      ‖Step2Gen_UN GridAssemblyGen_Cm.toFlowFM n ![true, true, false] (gridTime sInst tInst gridAsm_K n 0)
          (gridTime sInst tInst gridAsm_K n m) (fun _ => (1 : ℂ)) a +
        ∑ j ∈ Finset.range m, Step2Gen_UN GridAssemblyGen_Cm.toFlowFM n ![true, true, false]
          (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m)
          (gridAsm_witZvec n j ω) a‖ ≤
        (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 +
          ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * Real.sqrt (m * gridAsm_witProxy n) +
          ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [GridAssemblyGen_assembled_instance_gen 1 one_pos 1 1 0 (by norm_num) le_rfl] with n hn
  exact hn ![true, true, false] (gridAsm_witZvec n) (gridAsm_witProxy n) (gridAsm_witProxy_pos n)
    (fun j => gridAsm_stronglyMeasurable_witZvec n j)
    (fun m hm a j hj => (bandStep2_SubGaussStopN sz0 gridAsm_E _ _ _ _ m a j _).1
      (gridAsm_witSubGaussStop n _ m hm a j hj))

/-- **Instance of `assembledNg` with `Z = ZvecNg`** (the paper's first-chaos part; `hZmeas` from
`GridAssemblyGen_stronglyMeasurable_ZvecNg`) at the same data, `ε = 1/100`, `D = D₁ = 1`, `C_P = 0`: the sub-Gaussian family
for `ZvecNg` (the output of `azumaSubGNg`, row T4s2c) stays a hypothesis, at an arbitrary constant proxy `cc > 0`. -/
example : ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 3 → Bool) (cc : ℝ≥0), 0 < cc →
    (∀ m ≤ gridAsm_K n, ∀ (a : Fin 3 → Zd 3 (sz0.L n)) (j : ℕ), j < m →
      SubGaussStopNg GridAssemblyGen_Cm σ (gridTime sInst tInst gridAsm_K n) (fun _ => gridAsm_K n)
        (fun j ω => ZvecNg GridAssemblyGen_Cm sInst tInst gridAsm_K n j σ ω) m a j cc) →
    ∃ G : Set (PathΩ sz0), GridAssemblyGen_Cm.Pp.real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
      ∀ ω ∈ G, ∀ m ≤ gridAsm_K n, ∀ a : Fin 3 → Zd 3 (sz0.L n),
        ‖Step2Gen_UN GridAssemblyGen_Cm.toFlowFM n σ (gridTime sInst tInst gridAsm_K n 0)
            (gridTime sInst tInst gridAsm_K n m) (fun _ => (1 : ℂ)) a +
          ∑ j ∈ Finset.range m, Step2Gen_UN GridAssemblyGen_Cm.toFlowFM n σ
            (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m)
            (ZvecNg GridAssemblyGen_Cm sInst tInst gridAsm_K n j σ ω) a‖ ≤
          (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 +
            ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) * Real.sqrt (m * cc) +
            ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [GridAssemblyGen_assembled_instance_gen (1 / 100) (by norm_num) 1 1 0 (by norm_num)
    le_rfl] with n hn
  intro σ cc hcc hsub
  exact hn σ (fun j ω => ZvecNg GridAssemblyGen_Cm sInst tInst gridAsm_K n j σ ω) cc hcc
    (fun j => GridAssemblyGen_stronglyMeasurable_ZvecNg GridAssemblyGen_hL GridAssemblyGen_hW _ _ _ n j σ) hsub

/-- The `qvFormNg` bridge at the instance data (`n = 0`, `E ≡ 1/2`, `v = 0`, `w = 1/16`). -/
example (σ : Fin 3 → Bool) (M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
    (a : Fin 3 → Zd 3 (sz0.L 0)) :
    RBM.Ind.qvFormN sz0 0 (gridAsm_E 0) 0 (1 / 16) σ M a = qvFormNg GridAssemblyGen_Cm 0 0 (1 / 16) σ M a :=
  bandStep2_qvFormN sz0 gridAsm_E 0 (gridAsm_E_abs_lt 0).le (by norm_num) (by norm_num) σ M a

/-- The coarse row bound at the band carrier, for `v = 1/16 > w = 1/32` (no order between the two times). -/
example (X : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) (a : Fin 3 → Zd 3 (sz0.L 0)) (hX : ∀ b, ‖X b‖ ≤ 1) :
    ‖Step2Gen_UN GridAssemblyGen_Cm.toFlowFM 0 ![true, true, false] (1 / 16) (1 / 32) X a‖ ≤
      (1 + (1 - (1 / 32 : ℝ))⁻¹) ^ 3 * 1 :=
  GridAssemblyGen_norm_UN_coarse (gridRepTailGen_ker_band sz0 gridAsm_E 0 (gridAsm_E_abs_lt 0).le) _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) zero_le_one hX a

/-! The stopped Azuma instance with **no open hypothesis** (below, the last `example`): `m = 1`, step `j = 0` (where `H_0 = 0`
makes the walk deterministic), the carrier `bandStep2Mat sz0 (fun _ => 0)`, the window `(0, 1/2)` with `K = 4` (`Δ = 1/8`),
`σ = (+,-,+)`, label `0`, `τ ≡ 4`; the sub-Gaussian input is T2474's `subGaussStopNg_zvecNg` with the proxy `c3` of the loop
family (`Δ · linTrVar` of `AbCN` and of `(-I) • AbCN`, `AbCN` independent of `ω` at `H_0 = 0`). -/

namespace GridAssemblyGenCheck

open RBM.Ind (AbCN)

private abbrev E0 : ℕ → ℝ := fun _ => 0
private abbrev s0 : ℕ → ℝ := fun _ => 0
private abbrev t0 : ℕ → ℝ := fun _ => 1 / 2
private abbrev K0 : ℕ → ℕ := fun _ => 4
private abbrev Ψ0 : ∀ n : ℕ, Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ := fun _ => 0
private abbrev Cm0 : Step2Mat sz0 := bandStep2Mat sz0 E0
private abbrev σ3 : Fin 3 → Bool := ![true, false, true]
private abbrev b3 : Fin 3 → Zd 3 (sz0.L 0) := ![0, 0, 0]

private theorem hL0 : StepDecompGen_LoopForm Cm0 E0 :=
  stepDecompGen_loopForm_band sz0 E0 (fun _ => by norm_num)
private theorem hW0 : StepDecompGen_WalkForm Cm0 sz0.lam Ψ0 := stepDecompGen_walkForm_band sz0 E0

private abbrev U3 : (Fin 3 → Zd 3 (sz0.L 0)) → (Fin 3 → Zd 3 (sz0.L 0)) → ℂ :=
  fun a b => ∏ i : Fin 3, Step2Gen_uKer Cm0.toFlowFM 0 (σ3 i) (σ3 (finRotate 3 i))
    (gridTime s0 t0 K0 0 (0 + 1)) (gridTime s0 t0 K0 0 1) (a i) (b i)

private theorem hΔ : 0 ≤ gridStep s0 t0 K0 0 := by norm_num [gridStep]

private def A₀3 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ :=
  AbCN (sz0.withLam sz0.lam) s0 t0 K0 0 0 (loopFamNgShift Cm0 Ψ0 s0 t0 K0 0 0 σ3) U3 b3 (fun _ => 0)

private theorem AbCN_eq (ω : PathΩ sz0) :
    AbCN (sz0.withLam sz0.lam) s0 t0 K0 0 0 (loopFamNgShift Cm0 Ψ0 s0 t0 K0 0 0 σ3) U3 b3 ω = A₀3 := by
  simp [A₀3, AbCN, pathH, s0]

private def c3 : ℝ :=
  max (gridStep s0 t0 K0 0 * linTrVar 0 A₀3) (gridStep s0 t0 K0 0 * linTrVar 0 ((-Complex.I) • A₀3))

private theorem c3_nonneg : 0 ≤ c3 := le_max_of_le_left (mul_nonneg hΔ (linTrVar_nonneg 0 _))

example (x : ℝ) (hx : 0 ≤ x) :
    Cm0.Pp.real {ω | x ≤ ‖∑ j ∈ Finset.range (min 1 ((fun _ : PathΩ sz0 => K0 0) ω)),
        Step2Gen_UN Cm0.toFlowFM 0 σ3 (gridTime s0 t0 K0 0 (j + 1)) (gridTime s0 t0 K0 0 1)
          (ZvecNg Cm0 s0 t0 K0 0 j σ3 ω) b3‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ _j ∈ Finset.range 1, ((⟨c3, c3_nonneg⟩ : ℝ≥0) : ℝ))) := by
  have hτ : ∀ j, MeasurableSet[filt sz0 j] {ω : PathΩ sz0 | j < (fun _ : PathΩ sz0 => K0 0) ω} :=
    fun j => MeasurableSet.const _
  have hsub : ∀ j < 1, SubGaussStopNg Cm0 σ3 (gridTime s0 t0 K0 0) (fun _ => K0 0)
      (fun j ω => ZvecNg Cm0 s0 t0 K0 0 j σ3 ω) 1 b3 j ⟨c3, c3_nonneg⟩ := by
    intro j hj
    obtain rfl : j = 0 := by omega
    exact subGaussStopNg_zvecNg hL0 hW0 s0 t0 K0 0 0 (by norm_num) (by norm_num) (by norm_num) σ3 (fun _ => K0 0)
      (hτ 0) 1 b3 c3 c3_nonneg (fun ω _ => by rw [AbCN_eq]; exact le_max_left _ _)
      (fun ω _ => by rw [AbCN_eq]; exact le_max_right _ _)
  have h := stoppedAzumaZNg Cm0 hL0 hW0 s0 t0 K0 (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) 0 3 σ3 (fun _ => K0 0) hτ 1 (by norm_num) b3 (fun _ => ⟨c3, c3_nonneg⟩) hsub x hx
  exact h

end GridAssemblyGenCheck

end Inst

end RBM.BA

end
