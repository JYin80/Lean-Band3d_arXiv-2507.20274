/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.WardII
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpDuhamel
import RBM3D.Loop.KLUnique
import RBM3D.Path.Walk

/-!
# S6-12a (T2229): the Ward decomposition of regime (ii) of Step 6

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:136-147` (Ward decomposition `6:137-141`),
`paper/tex/1_2_Intro_model_result.tex:1030-1045` (`(WI_calL)`, `(WI_calK)`),
`paper/tex/6_Step6_two_loop.tex:14` (`(res_ELK_n=1)`), `paper/tex/3_5_Loop_Hierarchy.tex:1440-1470`
(`Def;zero_mode_remove`, `(normQA2)`).

This file proves the merged pin `STExpWardII` (`Step6Pins.lean:376`, text unchanged):
* `expWII_slot0`, `expWII_slot1`: for `σ₁ ≠ σ₂`, `f_u - Q^{(1)} f_u` and `f_u - Q^{(2)} f_u` are
  `Im 𝔼(𝓛-𝒦)^{(1)}_{u,+,x} / (N η_u)` (`x = a₂`, resp. `a₁`): the expectation of the merged
  samplewise identity `stWardII_identity`, the second slot through the rotation of the 2-loop;
* `expWII_two_slot_bound`: `‖T - Q^{({1,2})} T‖_∞ ≤ 3 M` from the two one-slot bounds `M`;
* `expWII_inv_Neta_le`, `expWII_det_bound`: `(N η_u)⁻¹ ≤ (Im m)⁻¹ W^{-d}B_{u,0}` and the one-size
  bound;
* `STExpWardIIConcl_of_avgU`: the conclusion from `STExpAvgU` along a bulk sequence
  (regime-free), and the pin `stExpWardII_holds`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Bridges -/

section Bridges

variable {d : ℕ} (sz : Sizes d)

/-- The loops `𝓛^{(k+1)}_{u,σ,a}` are integrable (measurable and bounded by `η_u^{-(k+1)}`; copy of the private
`expIniI_integrable_L`, `ExpIniI.lean:176`, for `k + 1` factors). -/
private theorem expWII_integrable_Lloop (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) :
    Integrable (fun ω => Lloop sz n E u σ a ω) sz.seqP :=
  Integrable.of_bound (walk_measurable_Lloop sz n E u σ a).aestronglyMeasurable
    ((etaT E u)⁻¹ ^ (k + 1)) (Filter.Eventually.of_forall fun ω => norm_Lloop_le sz n hE hu σ a ω)

/-- `f_u = 𝔼(𝓛 - 𝒦)^{(2)}_u` as the integral of `(𝓛 - 𝒦)^{(2)}` of the flow matrix (copy of the private
`expIniI_expErr_eq`, `ExpIniI.lean:183`). -/
private theorem expWII_expErr_eq (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErr sz n E u σ a = ∫ ω, STLKM sz n E u (sz.seqHflow n u ω) σ a ∂(sz.seqP) := by
  have h : ∀ ω, STLKM sz n E u (sz.seqHflow n u ω) σ a =
      Lloop sz n E u σ a ω - STKloop sz n E u σ a := fun ω => rfl
  simp_rw [h]
  unfold STExpErr
  rw [integral_sub (expWII_integrable_Lloop sz n hE hu σ a) (integrable_const _), integral_const]
  simp

private theorem expWII_STKloop_eq (n : ℕ) (E u : ℝ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a = KLK d (sz.L n) (sz.lam n) (sz.W n) E u ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
  simp [STKloop, KLloopOf, List.ofFn_succ]

private theorem expWII_STKloop_eq1 (n : ℕ) (E u : ℝ) (s : Bool) (a : Zd d (sz.L n)) :
    STKloop sz n E u (fun _ : Fin 1 => s) (fun _ => a) =
      KLK d (sz.L n) (sz.lam n) (sz.W n) E u ⟨[s], [a]⟩ := by
  simp [STKloop, KLloopOf, List.ofFn_succ]

private theorem expWII_STLM_eq (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STLM sz n E u H σ a =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (zt E u) ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
  unfold STLM loopFine
  rw [loopM_eq_loopL]
  simp [loopOf, List.ofFn_succ]

/-- `𝒦^{(1)}_{u,+,x} = m(E)` and `𝔼 (𝓛 - 𝒦)^{(1)}_{u,+,x} = 𝔼𝓛^{(1)}_{u,+,x} - m(E)` (probability measure). -/
private theorem expWII_avg_eq (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (x : Zd d (sz.L n)) :
    ∫ ω, STLKM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => true) (fun _ => x) ∂(sz.seqP) =
      (∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => x) ω ∂(sz.seqP)) - mSigma E true := by
  have hK : STKloop sz n E u (fun _ : Fin 1 => true) (fun _ => x) = mSigma E true := by
    rw [expWII_STKloop_eq1, KLK_one]
  have h : ∀ ω, STLKM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => true) (fun _ => x) =
      Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => x) ω - mSigma E true := fun ω => by
    change Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => x) ω -
      STKloop sz n E u (fun _ : Fin 1 => true) (fun _ => x) = _
    rw [hK]
  simp_rw [h]
  rw [integral_sub (expWII_integrable_Lloop sz n hE hu _ _) (integrable_const _), integral_const]
  simp

/-- `T a - Q^{(1)}T(a) = P^{(1)}T(a) = L^{-d} Σ_c T(c, a₂)` (`zeroModeOp` at the slot `0`; copy of the private
`wardII_zeroMode`, `WardII.lean:131`, for `zeroModeOp`). -/
private theorem expWII_zeroModeOp_eq0 (n : ℕ) (T : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    T a - zeroModeOp d (sz.L n) 0 T a =
      ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) * ∑ c : Zd d (sz.L n), T ![c, a 1] := by
  have hup : ∀ c : Zd d (sz.L n), Function.update a 0 c = ![c, a 1] := by
    intro c
    funext i
    fin_cases i <;> simp
  simp only [zeroModeOp, avgOp, hup]
  ring

/-- The slot-`1` mirror: `T a - Q^{(2)}T(a) = L^{-d} Σ_c T(a₁, c)`. -/
private theorem expWII_zeroModeOp_eq1 (n : ℕ) (T : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    T a - zeroModeOp d (sz.L n) 1 T a =
      ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) * ∑ c : Zd d (sz.L n), T ![a 0, c] := by
  have hup : ∀ c : Zd d (sz.L n), Function.update a 1 c = ![a 0, c] := by
    intro c
    funext i
    fin_cases i <;> simp
  simp only [zeroModeOp, avgOp, hup]
  ring

/-- `Q^{({0})} = Q^{(0)}` (`Finset.toList_singleton`). -/
private theorem expWII_zeroModeSet_zero (n : ℕ) (T : (Fin 2 → Zd d (sz.L n)) → ℂ) :
    zeroModeSet d (sz.L n) {0} T = zeroModeOp d (sz.L n) 0 T := by
  simp [zeroModeSet]

/-- Trace cyclicity for the 2-loop (copy of the private `wardII_loopL_rot`, `WardII.lean:31`). -/
private theorem expWII_loopL_rot {L W : ℕ} [NeZero L] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (s t : Bool) (b a : Zd d L) :
    loopL d L W H z ⟨[s, t], [b, a]⟩ = loopL d L W H z ⟨[t, s], [a, b]⟩ := by
  simp only [loopL, List.zip_cons_cons, List.zip_nil_left, List.foldr_cons, List.foldr_nil,
    Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

private theorem expWII_STLM_swap (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STLM sz n E u H σ a = STLM sz n E u H ![σ 1, σ 0] ![a 1, a 0] := by
  rw [expWII_STLM_eq, expWII_STLM_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact expWII_loopL_rot (σ 0) (σ 1) (a 0) (a 1)

private theorem expWII_STKloop_swap (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a = STKloop sz n E u ![σ 1, σ 0] ![a 1, a 0] := by
  rw [expWII_STKloop_eq, expWII_STKloop_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact KLK_rotate d (sz.L n) (sz.W n) (sz.lam n) E (sz.three_le_L n) (sz.W_pos n) hE u ⟨hu0, hu1⟩
    (σ 0) (a 0) [σ 1] [a 1] rfl

/-- **The rotation of the 2-loop**: `(𝓛 - 𝒦)^{(2)}_{σ,a} = (𝓛 - 𝒦)^{(2)}_{(σ₂,σ₁),(a₂,a₁)}` (trace cyclicity for `𝓛`,
`KLK_rotate` for `𝒦`). -/
private theorem expWII_STLKM_swap (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STLKM sz n E u H σ a = STLKM sz n E u H ![σ 1, σ 0] ![a 1, a 0] := by
  unfold STLKM
  rw [expWII_STLM_swap sz n E u H σ a, expWII_STKloop_swap sz n hE hu0 hu1 σ a]

private theorem expWII_STExpErr_swap (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErr sz n E u σ a = STExpErr sz n E u ![σ 1, σ 0] ![a 1, a 0] := by
  rw [expWII_expErr_eq sz n hE hu1 σ a, expWII_expErr_eq sz n hE hu1 ![σ 1, σ 0] ![a 1, a 0]]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    expWII_STLKM_swap sz n hE hu0 hu1 _ σ a)

end Bridges

/-! ## 2. The two slots -/

section Slots

variable {d : ℕ} (sz : Sizes d)

/-- **First slot** (`6:138-140`, `(WI_calL)`, `(WI_calK)`): for `σ₁ ≠ σ₂`, `f_u - Q^{(1)} f_u = Im 𝔼(𝓛-𝒦)^{(1)}_{u,+,a₂} / (N η_u)`,
the expectation of the merged samplewise identity `stWardII_identity`. -/
theorem expWII_slot0 (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErr sz n E u σ a - zeroModeOp d (sz.L n) 0 (fun b => STExpErr sz n E u σ b) a =
      ((((∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a 1) ω ∂(sz.seqP)) -
          mSigma E true).im : ℝ) : ℂ) /
        (((sz.size n : ℕ) : ℂ) * (etaT E u : ℂ)) := by
  refine (expWII_zeroModeOp_eq0 sz n (fun b => STExpErr sz n E u σ b) a).trans ?_
  have hint : ∀ b : Fin 2 → Zd d (sz.L n),
      Integrable (fun ω => STLKM sz n E u (sz.seqHflow n u ω) σ b) sz.seqP := fun b =>
    (expWII_integrable_Lloop sz n hE hu1 σ b).sub (integrable_const _)
  have hsum : ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) * ∑ c : Zd d (sz.L n), STExpErr sz n E u σ ![c, a 1] =
      ∫ ω, (((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) *
        ∑ c : Zd d (sz.L n), STLKM sz n E u (sz.seqHflow n u ω) σ ![c, a 1]) ∂(sz.seqP) := by
    rw [integral_const_mul, integral_finsetSum _ (fun c _ => hint _)]
    simp only [expWII_expErr_eq sz n hE hu1]
  have hpt : ∀ ω, ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) *
      ∑ c : Zd d (sz.L n), STLKM sz n E u (sz.seqHflow n u ω) σ ![c, a 1] =
      (((STLKM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) /
        ((((sz.size n : ℕ) : ℂ)) * (etaT E u : ℂ)) := by
    intro ω
    rw [← expWII_zeroModeOp_eq0 sz n (fun b => STLKM sz n E u (sz.seqHflow n u ω) σ b) a,
      ← expWII_zeroModeSet_zero]
    exact stWardII_identity sz n hE hu0 hu1 (sz.seqHflow_isHermitian n u ω) hσ a
  have hint1 : ∀ x : Fin 1 → Zd d (sz.L n),
      Integrable (fun ω => STLKM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => true) x) sz.seqP := fun x =>
    (expWII_integrable_Lloop sz n hE hu1 (fun _ : Fin 1 => true) x).sub (integrable_const _)
  change ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) * ∑ c : Zd d (sz.L n), STExpErr sz n E u σ ![c, a 1] = _
  rw [hsum]
  simp_rw [hpt]
  rw [integral_div]
  have h1 : ∫ ω, (((STLKM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ)
      ∂(sz.seqP) =
      ((∫ ω, (STLKM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => true) (fun _ => a 1)).im ∂(sz.seqP) : ℝ) : ℂ) :=
    integral_ofReal
  have h2 : ∫ ω, (STLKM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => true) (fun _ => a 1)).im ∂(sz.seqP) =
      (∫ ω, STLKM sz n E u (sz.seqHflow n u ω) (fun _ : Fin 1 => true) (fun _ => a 1) ∂(sz.seqP)).im := by
    exact integral_im (μ := sz.seqP) (hint1 (fun _ => a 1))
  rw [h1, h2, expWII_avg_eq sz n hE hu1 (a 1)]

/-- **Second slot**: `f_u - Q^{(2)} f_u = Im 𝔼(𝓛-𝒦)^{(1)}_{u,+,a₁} / (N η_u)`: the first slot of the rotated loop
`(σ₂,σ₁),(a₂,a₁)` (`σ' = ![σ 1, σ 0]` is again mixed). -/
theorem expWII_slot1 (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErr sz n E u σ a - zeroModeOp d (sz.L n) 1 (fun b => STExpErr sz n E u σ b) a =
      ((((∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a 0) ω ∂(sz.seqP)) -
          mSigma E true).im : ℝ) : ℂ) /
        (((sz.size n : ℕ) : ℂ) * (etaT E u : ℂ)) := by
  have hσ' : (![σ 1, σ 0] : Fin 2 → Bool) 0 ≠ (![σ 1, σ 0] : Fin 2 → Bool) 1 := fun h => hσ h.symm
  have h0 := expWII_slot0 sz n hE hu0 hu1 hσ' (![a 1, a 0] : Fin 2 → Zd d (sz.L n))
  have h0' := (expWII_zeroModeOp_eq0 sz n (fun b => STExpErr sz n E u ![σ 1, σ 0] b)
    (![a 1, a 0] : Fin 2 → Zd d (sz.L n))).symm.trans h0
  refine (expWII_zeroModeOp_eq1 sz n (fun b => STExpErr sz n E u σ b) a).trans ?_
  have e1 : ∀ c : Zd d (sz.L n), STExpErr sz n E u σ ![a 0, c] =
      STExpErr sz n E u ![σ 1, σ 0] ![c, a 0] := fun c =>
    expWII_STExpErr_swap sz n hE hu0 hu1 σ ![a 0, c]
  simp_rw [e1]
  exact h0'

end Slots

/-! ## 3. Two slots and the bound -/

section TwoSlot

variable {d L : ℕ} [NeZero L]

/-- **Two slots** (`6:138-140`): `Q^{({1,2})} = Q^{(i)} Q^{(j)}` for `Finset.univ.toList = [i, j]` (either order), so
`T - Q^{({1,2})} T = (T - Q^{(i)} T) + Q^{(i)} (T - Q^{(j)} T)`; with `‖Q^{(i)} g‖_∞ ≤ 2 ‖g‖_∞` (`norm_zeroModeOp_le`) both
one-slot bounds `M` give `3 M`. -/
theorem expWII_two_slot_bound (T : (Fin 2 → Zd d L) → ℂ) {M : ℝ}
    (h0 : ∀ b, ‖T b - RBM.zeroModeOp d L 0 T b‖ ≤ M) (h1 : ∀ b, ‖T b - RBM.zeroModeOp d L 1 T b‖ ≤ M)
    (a : Fin 2 → Zd d L) :
    ‖T a - RBM.zeroModeSet d L (Finset.univ : Finset (Fin 2)) T a‖ ≤ 3 * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (h0 a)
  have hgen : ∀ (i : Fin 2) (b : Fin 2 → Zd d L), ‖T b - RBM.zeroModeOp d L i T b‖ ≤ M := by
    intro i b
    fin_cases i
    · exact h0 b
    · exact h1 b
  have key : ∀ i j : Fin 2, ‖T a - RBM.zeroModeOp d L i (RBM.zeroModeOp d L j T) a‖ ≤ 3 * M := by
    intro i j
    have hlin : RBM.zeroModeOp d L i (T - RBM.zeroModeOp d L j T) =
        RBM.zeroModeOp d L i T - RBM.zeroModeOp d L i (RBM.zeroModeOp d L j T) := by
      funext b
      simp only [RBM.zeroModeOp, RBM.avgOp, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]
      ring
    have hdecomp : T a - RBM.zeroModeOp d L i (RBM.zeroModeOp d L j T) a =
        (T a - RBM.zeroModeOp d L i T a) + RBM.zeroModeOp d L i (T - RBM.zeroModeOp d L j T) a := by
      rw [hlin]
      simp only [Pi.sub_apply]
      ring
    have hg : ‖T - RBM.zeroModeOp d L j T‖ ≤ M :=
      (pi_norm_le_iff_of_nonneg hM).2 (fun b => hgen j b)
    have hq : ‖RBM.zeroModeOp d L i (T - RBM.zeroModeOp d L j T) a‖ ≤ 2 * M :=
      (norm_le_pi_norm _ a).trans ((RBM.norm_zeroModeOp_le i _).trans (by linarith))
    rw [hdecomp]
    calc ‖(T a - RBM.zeroModeOp d L i T a) + RBM.zeroModeOp d L i (T - RBM.zeroModeOp d L j T) a‖
        ≤ ‖T a - RBM.zeroModeOp d L i T a‖ +
          ‖RBM.zeroModeOp d L i (T - RBM.zeroModeOp d L j T) a‖ := norm_add_le _ _
      _ ≤ M + 2 * M := add_le_add (hgen i a) hq
      _ = 3 * M := by ring
  have hlen : (Finset.univ : Finset (Fin 2)).toList.length = 2 := by
    rw [Finset.length_toList]
    simp
  obtain ⟨i, j, hij⟩ := List.length_eq_two.1 hlen
  have hset : RBM.zeroModeSet d L (Finset.univ : Finset (Fin 2)) T =
      RBM.zeroModeOp d L i (RBM.zeroModeOp d L j T) := by
    simp only [RBM.zeroModeSet, hij, List.foldr_cons, List.foldr_nil]
  rw [hset]
  exact key i j

end TwoSlot

/-! ## 4. `(N η_u)⁻¹` and the one-size bound -/

section OneSize

variable {d : ℕ} (sz : Sizes d)

/-- **`(N η_u)⁻¹ ≤ (Im m)⁻¹ W^{-d}B_{u,0}`** (`6:141`; `η_u = (1-u) Im m`, `W^{-d}B_{u,0} ≥ W^{-d}(L^d(1-u))⁻¹ = (N(1-u))⁻¹`):
every `d`, every regime, `u < 1`, `|E| < 2`. -/
theorem expWII_inv_Neta_le (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) :
    (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹ ≤ ((mE E).im)⁻¹ * sz.Bctl n u := by
  have h1 : 0 < 1 - u := by linarith
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsize : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
    rw [mul_assoc, mul_inv]
  have hB : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ sz.Bctl n u := by
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos h1, hsize, mul_add]
    have h5 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
        ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) := by positivity
    linarith
  have heq : (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹ = ((mE E).im)⁻¹ * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
    have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    unfold etaT
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hB (inv_nonneg.2 hm.le)

/-- **The decomposition bound at one size** (`6:138-140`, constant `3`): from a bound `M` of the one-point averages,
`‖f_u - Q^{({1,2})} f_u‖_∞ ≤ 3 M (N η_u)⁻¹`. -/
theorem expWII_det_bound (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) {M : ℝ}
    (hM : ∀ x : Zd d (sz.L n),
      ‖(∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => x) ω ∂(sz.seqP)) - mSigma E true‖ ≤ M)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖STExpErr sz n E u σ a -
        zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErr sz n E u σ b) a‖ ≤
      3 * (M * (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹) := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hslot : ∀ x : Zd d (sz.L n),
      ‖((((∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => x) ω ∂(sz.seqP)) -
          mSigma E true).im : ℝ) : ℂ) /
        (((sz.size n : ℕ) : ℂ) * (etaT E u : ℂ))‖ ≤ M * (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹ := by
    intro x
    rw [norm_div, Complex.norm_real, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hη.le, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 (mul_pos hN hη).le)
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hM x)
  exact expWII_two_slot_bound (fun b => STExpErr sz n E u σ b)
    (fun b => (expWII_slot0 sz n hE hu0 hu1 hσ b).symm ▸ hslot (b 1))
    (fun b => (expWII_slot1 sz n hE hu0 hu1 hσ b).symm ▸ hslot (b 0)) a

end OneSize

/-! ## 5. Along the sequence -/

section Seq

variable {d : ℕ} (sz : Sizes d)

/-- **`STExpWardIIConcl` from `(res_ELK_n=1)` uniformly in `u`** (`6:141`; bulk `|E_n| ≤ 2 - κ`; regime-free):
both `STExpAvgU` and the conclusion are deterministic (`st6_prec_det_iff`); `(Im m)⁻¹ ≤ 2/√(2κ)` and the constant
`6/√(2κ)` are absorbed into `N^{τ/2}` eventually. -/
theorem STExpWardIIConcl_of_avgU (hsz : sz.SizeTendsto) {κ : ℝ} (hκ : 0 < κ) {E s t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (_hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hAvg : STExpAvgU sz E s t) : STExpWardIIConcl sz E s t := by
  unfold STExpWardIIConcl
  refine (st6_prec_det_iff sz hsz _ _).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hA := (st6_prec_det_iff sz hsz _ _).1 hAvg (τ / 2) hτ2
  have hsq : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  have hNge : ∀ᶠ n in atTop, 3 * (2 / Real.sqrt (2 * κ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop _
  filter_upwards [hA, hNge] with n hn hNn
  rintro ⟨⟨u, hu⟩, ⟨σ, hσ⟩, a⟩
  have hE2 : |E n| < 2 := by linarith [hE n]
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hB0 : 0 ≤ sz.Bctl n u := by
    unfold Sizes.Bctl Bparam
    have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hL : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  have hbd := expWII_det_bound sz n hE2 hu0 hu1 hσ
    (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 2)
    (fun x => hn (⟨u, hu⟩, true, x)) a
  have hc := expWII_inv_Neta_le sz n hE2 hu1
  have hm : Real.sqrt (2 * κ) / 2 ≤ (mE (E n)).im := st6_mE_im_ge hκ (hE n)
  have hmi : ((mE (E n)).im)⁻¹ ≤ 2 / Real.sqrt (2 * κ) := by
    have := inv_anti₀ (by positivity : 0 < Real.sqrt (2 * κ) / 2) hm
    simpa [inv_div] using this
  have hc2 : (((sz.size n : ℕ) : ℝ) * etaT (E n) u)⁻¹ ≤ 2 / Real.sqrt (2 * κ) * sz.Bctl n u :=
    hc.trans (mul_le_mul_of_nonneg_right hmi hB0)
  have hP : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN.le _
  have hM0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 2 := mul_nonneg hP (by positivity)
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  change ‖STExpErr sz n (E n) u σ a -
      zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErr sz n (E n) u σ b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u) ^ 3
  calc _ ≤ 3 * ((((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 2) *
          (((sz.size n : ℕ) : ℝ) * etaT (E n) u)⁻¹) := hbd
    _ ≤ 3 * ((((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 2) *
          (2 / Real.sqrt (2 * κ) * sz.Bctl n u)) := by gcongr
    _ = (3 * (2 / Real.sqrt (2 * κ))) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 3 := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n u) ^ 3 := by
        have hB3 : 0 ≤ (sz.Bctl n u) ^ 3 := by positivity
        have := mul_le_mul_of_nonneg_right hNn hP
        exact mul_le_mul_of_nonneg_right this hB3
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u) ^ 3 := by rw [hrpow]

/-- **The pin `STExpWardII`** (`Step6Pins.lean:376`, text unchanged), every `d`: the constant `𝔠_d = 1/100`; the proof uses
only `SizeTendsto` and `|E_n| ≤ 2 - κ` of the flow, `0 ≤ s`, `s ≤ t`, `t < 1`, and the premise `STExpAvgU`. -/
theorem stExpWardII_holds (d : ℕ) : STExpWardII d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5
  exact STExpWardIIConcl_of_avgU sz hflow.1.2.2.1 hκ (st6_flowE_le sz hflow) hs0
    (fun n => (hst n).le) (st5_t_lt_one sz hflow htT)

end Seq

end RBM.Gauss.Sizes

/-! ## 6. Compiled nonempty instances (`d = 3`, `szB`, `zB`, regime (ii) times `(15/16, 31/32)`) -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- `stExpWardII_holds 3` at the data of regime (ii): `(szB, zB, 15/16, 31/32)`; the stochastic premises of `STIngR6` and
`STExpAvgU` stay hypotheses of the produced statement (other gates' pins). -/
theorem inst_expWardII_holds :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_expWardII (stExpWardII_holds 3)

/-- The regime-(ii) skeleton with the merged `stExpLKLKHi_holds`, `stImproveExpAver_holds`, `stExpDuhamelZ_holds` and the
proved `stExpWardII_holds`: only `LWtermEXP 3` (LW-14) and `STExpIntII 3` (S6-12b) stay open. -/
theorem inst_skeleton6II_Wd (hLW : LWtermEXP 3) (hInt : STExpIntII 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_skeleton6II (stExpLKLKHi_holds 3) hLW (stImproveExpAver_holds 3) (stExpDuhamelZ_holds 3) hInt
    (stExpWardII_holds 3)

/-- `STExpWardIIConcl_of_avgU` at `szB`, the flow `zB` (`|E_n| ≤ 2 - 1/10`), `κ = 1/10`, times `(15/16, 31/32)`; the
premise `STExpAvgU` stays a hypothesis. -/
theorem inst_expWII_concl :
    STExpAvgU szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      STExpWardIIConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  STExpWardIIConcl_of_avgU szB flow_zB.1.2.2.1 (κ := 1 / 10) (by norm_num) (st6_flowE_le szB flow_zB)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)

/-- `expWII_inv_Neta_le` at `szB`, `n = 0` (`N = 4096`), `E = 0` (`Im m = 1`), `u = 15/16`:
`(N η)⁻¹ = 1/256 ≤ W^{-3}B = (16/17 + 1/4)/64`. -/
theorem inst_expWII_inv_Neta_le :
    (((szB.size 0 : ℕ) : ℝ) * RBM.Gauss.etaT 0 (15 / 16))⁻¹ ≤ ((RBM.mE 0).im)⁻¹ * szB.Bctl 0 (15 / 16) :=
  expWII_inv_Neta_le szB 0 (by norm_num) (by norm_num)

/-- `expWII_slot0` at `szB`, `n = 0`, `E = 0`, `u = 15/16`, `σ = (+,-)`, `a = (0,0)`. -/
theorem inst_expWII_slot0 :
    szB.STExpErr 0 0 (15 / 16) ![true, false] ![0, 0] -
        RBM.zeroModeOp 3 (szB.L 0) 0 (fun b => szB.STExpErr 0 0 (15 / 16) ![true, false] b) ![0, 0] =
      ((((∫ ω, szB.Lloop 0 0 (15 / 16) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(szB.seqP)) -
          RBM.mSigma 0 true).im : ℝ) : ℂ) /
        (((szB.size 0 : ℕ) : ℂ) * (RBM.Gauss.etaT 0 (15 / 16) : ℂ)) :=
  expWII_slot0 szB 0 (by norm_num) (by norm_num) (by norm_num) (by decide) _

/-- `expWII_slot1` at the same data (`szB`, `n = 0`, `E = 0`, `u = 15/16`, `σ = (+,-)`, `a = (0,0)`). -/
theorem inst_expWII_slot1 :
    szB.STExpErr 0 0 (15 / 16) ![true, false] ![0, 0] -
        RBM.zeroModeOp 3 (szB.L 0) 1 (fun b => szB.STExpErr 0 0 (15 / 16) ![true, false] b) ![0, 0] =
      ((((∫ ω, szB.Lloop 0 0 (15 / 16) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(szB.seqP)) -
          RBM.mSigma 0 true).im : ℝ) : ℂ) /
        (((szB.size 0 : ℕ) : ℂ) * (RBM.Gauss.etaT 0 (15 / 16) : ℂ)) :=
  expWII_slot1 szB 0 (by norm_num) (by norm_num) (by norm_num) (by decide) _

/-- `expWII_det_bound` at the same data with the explicit bound `M = η⁻¹ + 1` of the one-point averages
(`‖𝔼𝓛^{(1)}‖ ≤ η⁻¹` by `norm_Lloop_le`, `‖m‖ = 1`): no hypothesis left. -/
theorem inst_expWII_det_bound :
    ‖szB.STExpErr 0 0 (15 / 16) ![true, false] ![0, 0] -
        RBM.zeroModeSet 3 (szB.L 0) (Finset.univ : Finset (Fin 2))
          (fun b => szB.STExpErr 0 0 (15 / 16) ![true, false] b) ![0, 0]‖ ≤
      3 * (((RBM.Gauss.etaT 0 (15 / 16))⁻¹ + 1) *
        (((szB.size 0 : ℕ) : ℝ) * RBM.Gauss.etaT 0 (15 / 16))⁻¹) := by
  refine expWII_det_bound szB 0 (by norm_num) (by norm_num) (by norm_num) (by decide) (fun x => ?_) _
  have h1 : ‖∫ ω, szB.Lloop 0 0 (15 / 16) (fun _ : Fin 1 => true) (fun _ => x) ω ∂(szB.seqP)‖ ≤
      (RBM.Gauss.etaT 0 (15 / 16))⁻¹ := by
    have := norm_integral_le_of_norm_le_const (μ := szB.seqP)
      (f := fun ω => szB.Lloop 0 0 (15 / 16) (fun _ : Fin 1 => true) (fun _ => x) ω)
      (C := (RBM.Gauss.etaT 0 (15 / 16))⁻¹ ^ 1)
      (Filter.Eventually.of_forall fun ω =>
        norm_Lloop_le szB 0 (k := 0) (by norm_num) (by norm_num) (fun _ : Fin 1 => true) (fun _ => x) ω)
    simpa using this
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mSigma (by norm_num)]
  linarith

/-- `expWII_two_slot_bound` at `d = 3`, `L = 4` for the constant tensor `T = 1` (`Q^{(i)} T = 0`, so both one-slot
differences have norm exactly `M = 1`): `‖T - Q^{({1,2})} T‖ ≤ 3`. -/
theorem inst_expWII_two_slot_bound (a : Fin 2 → Zd 3 4) :
    ‖(1 : ℂ) - RBM.zeroModeSet 3 4 (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℂ)) a‖ ≤ 3 * 1 := by
  have hQ : ∀ (i : Fin 2) (b : Fin 2 → Zd 3 4), RBM.zeroModeOp 3 4 i (fun _ => (1 : ℂ)) b = 0 := by
    intro i b
    simp [RBM.zeroModeOp, RBM.avgOp, Zd, ZMod.card]
    norm_num
  exact expWII_two_slot_bound (d := 3) (L := 4) (fun _ => (1 : ℂ)) (M := 1)
    (fun b => by simp [hQ]) (fun b => by simp [hQ]) a

end RBM.Gauss.Step6Inst

end
