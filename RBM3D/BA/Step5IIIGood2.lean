/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIGood
import RBM3D.Path.LemDecCalEwG

/-!
# U5c, part 2: the scalar part of U5b's bundle along a flow, and the composed instance

Ticket T2485.  Paper: the scalar hypotheses of `lem_dec_calE` (`3_5:2314-2338`): `M_u = W^d(1-u)`,
`ℓ_u = 1` as `lam² ≤ 1 - u`, `J ≤ W^{1/2}`; BA `7_8:2101` (omitted details, paper-delta candidate
T2459a).  Design `docs/reports/T2459-design.md` U5-2; audit `docs/reports/T2459-audit.md` O2
(second half).

1. `baStep5III_scalar_flow` (target 4): along a flow in the regime, eventually, every
   `u ∈ [s_n, t_n]`, every level `D' ≥ D` and every control `1 ≤ J ≤ W^{1/2}` meet the scalar part
   of the bundle (written inline) at `Λ = K₀ = N^{τ'}`.  Sources: `Sizes.WO` (`0 < lam`;
   `lam_sq_mul_pow_ge`, `Defs/Sizes.lean:193`), `Sizes.Bandwidth`, `Sizes.SizeTendsto`
   (`4 ≤ log W`).
2. Compiled nonempty instances (target 5) at `d = 3`, `sz0`, `zSeq`, `flow_sz0`: target 4 with its
   floor premise discharged, and the composed instance (audit O2): on `G ∩ {J♯ ≤ W^{1/2}}` both
   parts of the bundle hold, and the three ℰ-bounds follow through an exact-type hypothesis
   `Step5IIIGood2_Edet 3` (the text of `T2482_BAEdet`, `docs/tickets/checks/T2482-check.lean:180`;
   U5b-2's pin, not merged).  The private bundle copies `Step5IIIGood2_Scalar`, `_Matrix`,
   `_EdetConcl`, `_Edet` appear only in this section.

Helpers carry the stem `Step5IIIGood2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 4: the scalar part at the flow -/

section ScalarFlow

/-- **Target 4** (content binding `T2485_ScalarFlow`; audit O2, second half): along a flow in the regime, eventually, every
`u ∈ [s_n, t_n]`, every level `D' ≥ D` and every control `1 ≤ J ≤ W^{1/2}` meet the scalar part of the bundle (inline) at
`Λ = K₀ = N^{τ'}`; the floor premise is `(L^d W^{6d})² ≤ W^D` eventually. -/
theorem baStep5III_scalar_flow :
    ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
      STReg5III sz s t → ∀ D τ' : ℝ, 0 ≤ τ' →
        (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
        ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (D' J : ℝ), D ≤ D' → 1 ≤ J → J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) →
          3 ≤ 3 ∧ 0 ≤ (u : ℝ) ∧ (u : ℝ) < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - (u : ℝ) ∧
            1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ 3 ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' ∧
            4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ (((sz.L n : ℕ) : ℝ) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D' ∧
            1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
  intro κ ε 𝔠 𝔡 sz z hflow s t hs hst hReg D τ' hτ' hfl
  obtain ⟨h𝔠, h𝔡, hsize, hband, hWO⟩ := hflow.1
  have hNtop : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop := (tendsto_rpow_atTop h𝔠).comp hsize
  have hWtop : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := tendsto_atTop_mono' _ hband hNtop
  have hlog : ∀ᶠ n in atTop, 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    (Real.tendsto_log_atTop.comp hWtop).eventually_ge_atTop 4
  filter_upwards [hWO, hlog, hfl] with n hwo hlogn hfln
  intro u D' J hDD' hJ1 hJW
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hwo.1
  have hreg : sz.lam n ^ 2 ≤ 1 - (u : ℝ) := by have := hReg n; linarith [u.2.2]
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hQ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'
  refine ⟨le_rfl, (hs n).trans u.2.1, ?_, hlam, hreg, ?_, hQ, hQ, hlogn, ?_, hJ1, hJW⟩
  · nlinarith [pow_pos hlam 2]
  · exact (Real.one_le_rpow hW1 (by linarith)).trans (sz.lam_sq_mul_pow_ge n hwo.1)
  · exact hfln.trans (Real.rpow_le_rpow_of_exponent_le hW1 hDD')

end ScalarFlow

/-! ## 2. Compiled nonempty instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`

Data: `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 < t₀`, `D = 40`, `Cd = 1`, `θ = 1/10`.  The four Steps 2-4 predicates
and `Step5IIIGood2_Edet 3` stay hypotheses. -/

section Instances

/-- The scalar part of the bundle as one `Prop` (private stem copy of the text fixed at T2482's 1a-audit; instance section only). -/
private def Step5IIIGood2_Scalar {d : ℕ} (sz : Sizes d) (n : ℕ) (u D Λ K₀ J : ℝ) : Prop :=
  3 ≤ d ∧ 0 ≤ u ∧ u < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - u ∧ 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧ 1 ≤ Λ ∧ 1 ≤ K₀ ∧
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)

/-- The matrix part of the bundle as one `Prop` (private stem copy of the text fixed at T2482's 1a-audit; instance section only). -/
private def Step5IIIGood2_Matrix {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  H.IsHermitian ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ J * STtailTD sz n u D a) ∧
  (∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
    ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
  (∀ (σ : Bool) (a : Zd d (sz.L n)), ‖STavgMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) ∧
  (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧
  (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ *
    ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- The three ℰ-bounds (`res_deccalE_lk`, `_wG`, `_dif`) as one `Prop` (the conclusion of `T2482_BAEdet`, verbatim up to the name). -/
private def Step5IIIGood2_EdetConcl {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2)) * STtailTD sz n u D a) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ *
        ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a)) ∧
  (∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
    (∀ i : Fin 2, (zdistInf d (sz.L n) (a i - a' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
    ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
        ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) * ((1 - u)⁻¹ *
        ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2))

/-- **`T2482_BAEdet`** (U5b-2's pin, not merged; verbatim up to the names of the bundle parts): `lem_dec_calE` at BA, deterministic,
one time `u`.  An exact-type hypothesis of the composed instance only. -/
private def Step5IIIGood2_Edet (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), 0 < θ → 0 < Cd →
    Step5IIIGood2_Scalar sz n u D Λ K₀ J → Step5IIIGood2_Matrix sz lam0 E n u D Λ K₀ J θ Cd H →
      Step5IIIGood2_EdetConcl sz lam0 E n u D Λ K₀ J θ Cd H

/-- The floor premise of target 4 at `sz0`, `D = 40`: `(L^3 W^{18})² ≤ W^{40}` (`L = 4(n+1)`, `W = (2(n+1))^5`; `L^6 ≤ W^4`). -/
theorem Step5IIIGood2_sz0_floor (n : ℕ) :
    (((SizesInst.sz0.L n : ℕ) : ℝ) ^ 3 * ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (40 : ℝ) := by
  have hm : 1 ≤ n + 1 := by omega
  have hnat : (SizesInst.sz0.L n) ^ 6 ≤ (SizesInst.sz0.W n) ^ 4 := by
    change (4 * (n + 1)) ^ 6 ≤ ((2 * (n + 1)) ^ 5) ^ 4
    calc (4 * (n + 1)) ^ 6 = 4 ^ 6 * (n + 1) ^ 6 := by ring
      _ ≤ 2 ^ 20 * (n + 1) ^ 20 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right hm (by norm_num))
      _ = ((2 * (n + 1)) ^ 5) ^ 4 := by ring
  have hreal : ((SizesInst.sz0.L n : ℕ) : ℝ) ^ 6 ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ 4 := by exact_mod_cast hnat
  have hW0 : (0 : ℝ) ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (((SizesInst.sz0.L n : ℕ) : ℝ) ^ 3 * ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2
      = ((SizesInst.sz0.L n : ℕ) : ℝ) ^ 6 * ((SizesInst.sz0.W n : ℕ) : ℝ) ^ 36 := by ring
    _ ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ 4 * ((SizesInst.sz0.W n : ℕ) : ℝ) ^ 36 :=
        mul_le_mul_of_nonneg_right hreal (by positivity)
    _ = ((SizesInst.sz0.W n : ℕ) : ℝ) ^ 40 := by ring

/-- **Target 4 at the instance** (`τ' ≥ 0`, level `40`): the scalar part holds eventually, at every `u ∈ [1/10, 1/2]`, level `D' ≥ 40` and
control `1 ≤ J ≤ W^{1/2}`; the flow, the regime and the floor premise are discharged. -/
example (τ' : ℝ) (hτ' : 0 ≤ τ') :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) n) (D' J : ℝ), 40 ≤ D' → 1 ≤ J →
      J ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) →
        Step5IIIGood2_Scalar SizesInst.sz0 n (u : ℝ) D' (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') J :=
  baStep5III_scalar_flow (1 / 2) (1 / 10) (1 / 6) (1 / 10) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 _ _
    (fun n => by norm_num) (fun n => by norm_num) Step5IIIGood_reg_sz0 40 τ' hτ'
    (Eventually.of_forall Step5IIIGood2_sz0_floor)

/-- **The composed instance** (audit O2; T2482 dispatcher answer (4)): at the instance (`D = 40`, `θ = 1/10`, `Cd = 1`), eventually, at every
`u ∈ [1/10, 1/2]` there is an event `G` of probability `≥ 1 - N^{-D₁}` on which, as soon as `J♯ ≤ W^{1/2}`, both parts of the bundle
hold and the three ℰ-bounds follow through the exact-type hypothesis `Step5IIIGood2_Edet 3`. -/
example (hAvg : STAvgUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)))
    (hLmax : STLmaxUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)))
    (hLK : STLKUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)))
    (hDec : STGdecayWgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1)
    (hE : Step5IIIGood2_Edet 3) (τ' D₁ : ℝ) (hτ' : 0 < τ') (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, ∀ u : TimeIcc (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) n, ∃ G : Set SizesInst.sz0.SeqΩ,
      Sizes.seqP (SizesInst.sz0.withLam 0) Gᶜ ≤ ENNReal.ofReal (((SizesInst.sz0.size n : ℕ) : ℝ) ^ (-D₁)) ∧ ∀ ω ∈ G,
        let H := SizesInst.sz0.seqHflowBA (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) n (u : ℝ) ω;
        let J := BAStep5IIIJsharp SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n 40 (u : ℝ) H;
        J ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) →
          Step5IIIGood2_Scalar SizesInst.sz0 n (u : ℝ) 40 (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') J ∧
          Step5IIIGood2_Matrix SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n (u : ℝ) 40
            (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') J (1 / 10) 1 H ∧
          Step5IIIGood2_EdetConcl SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n (u : ℝ) 40
            (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') J (1 / 10) 1 H := by
  have hg := baStep5IIIGoodThm_holds (1 / 2) (1 / 10) (1 / 6) (1 / 10) 1 SizesInst.sz0 FlowPinsInst.zSeq (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) FlowPinsInst.flow_sz0 _ _ (fun n => by norm_num) (fun n => by norm_num)
    (fun n => (FlowPinsInst.half_lt_t0 n).le) Step5IIIGood_reg_sz0 hAvg hLmax hLK hDec 40 (by norm_num) τ' D₁ (1 / 10) hτ' hD₁
    (by norm_num) (by norm_num)
  have hs := baStep5III_scalar_flow (1 / 2) (1 / 10) (1 / 6) (1 / 10) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 _ _
    (fun n => by norm_num) (fun n => by norm_num) Step5IIIGood_reg_sz0 40 τ' hτ'.le (Eventually.of_forall Step5IIIGood2_sz0_floor)
  filter_upwards [hg, hs] with n hgn hsn u
  obtain ⟨G, hG, hGm⟩ := hgn u
  refine ⟨G, hG, fun ω hω => ?_⟩
  intro H J hJ
  have hm : Step5IIIGood2_Matrix SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n (u : ℝ) 40
      (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') J (1 / 10) 1 H := hGm ω hω
  have hsc : Step5IIIGood2_Scalar SizesInst.sz0 n (u : ℝ) 40 (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') J :=
    hsn u 40 J le_rfl (baStep5IIIJsharp_spec 3 _ _ _ n 40 (u : ℝ) H).1 hJ
  exact ⟨hsc, hm, hE le_rfl SizesInst.sz0 _ _ n (u : ℝ) 40 _ _ J (1 / 10) 1 H (by norm_num) (by norm_num) hsc hm⟩

end Instances

end RBM.BA
