/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.IniTermIIGen
import RBM3D.Induction.EtermsMid2
import RBM3D.Chain.NewKLKLGen
import RBM3D.Chain.NQEndFlowGen
import RBM3D.BA.Step2IterBA
import RBM3D.BA.NewKLKBA
import RBM3D.BA.KBase
import RBM3D.BA.Prop6Path
import RBM3D.BA.Prop5Short
import RBM3D.BA.TwistGrid
import RBM3D.BA.TwistStep2
import RBM3D.BA.KInduct
import RBM3D.BA.KTreeRep

/-!
# U4-BA, row a1: the BA producers of the kernel, `lem:newKLK` at `ℓ = L`, D2 and D3 classes

Ticket T2501 (row a1; DECISIONS §311).  Paper: arXiv:2507.20274, Steps 3-6 "extend verbatim" to BA
(`7_8:2099-2100`); `lem:newKLK` `3_5:371-378`, proof `3_5:610-664`; its BA change touches
`(uu2j2ois)` (F7) only (`7_8:2032`), which target 3 does not read.  Band twins (not edited):
`iniTermGen_kerFacts_band` (`Chain/IniTermIIGen.lean:107`), `etermsMid_newKLKL_band`
(`Induction/EtermsMid2.lean:62`), `lemDecCalELipG_flowMod_band`
(`Induction/LemDecCalELip.lean:355`), `nqEndFlowGen_kLip_band`
(`Chain/NQEndFlowGen.lean:222`).  The check is
`docs/tickets/checks/T2501-check.lean` (pins `T2501_*`).

BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; Step2Mat family
`mkM sz z = baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`; `gK = BAflowLam0`.  Constants depend
on `(d, κ, 𝔡)` only (UBA-C1: `A = (κ+1)/κ`, `c = 1`, `δ₀ = κ/2`).

* 1. `baStep5KerGen_thDecay` (= `T2501_ThDecayBA`, `∃ C₆` after `κ`) and `baIniTermGen_kerFacts`
  (= `T2501_KerFactsBA`): the semigroup law `Step2Kern_uKer_BA` + `BAuKerSemigroup_holds`, the decay
  `Step2Kern_thetaKer_BA` + `NewKLKBA_tail` + `baComp_row_le`, the R1 conjunct `TwistStep2_lam0_sq`,
  the swap `BATheta_swap`, the column sum `BATheta_row_sum_pm`, the zero mode `baProp8_holds`, the
  short range `baProp5s_holds`; every `∀ n` clause needs `BAReal` only (`BAflow_real`), none needs
  `0 < g₀`.
* 3. `baEtermsMid_newKLKL` (= `T2501_NewKLKLBA`; A9): a private per-carrier copy of
  `stNewKLKLAtgL'_of` (`Chain/NewKLKLGen.lean:190-299`); F5, F8, F9 from `baNewKLKGenHyp` at
  `sz.withLam g₀`; F7 is not read, so R1 does not enter.
* 4. `baLemDecCalELipG_flowMod` (= `T2501_FlowModBA`; D2): `Hm = sz.seqHflowBA g₀`,
  `G = contGood (sz.withLam 0)`, `c = 1`.
* 5. `baKLip_two` (= `T2501_KLipBA`; D3): `NQEndFlowGen_KLip (baFMz sz z) t 2` from `baKsol_two` and
  `1 - t₀ ≥ Im z / 2`.
* 6. the inline premises `Step5KerBA_hmn`, `Step5KerBA_hSr` (private).
* 7. `baNewKLKLgL'` (= `T2501_NewKLKLgLBA`): `stNewKLKLgL'_of` with `baNewKLKGenHyp`.
* 8. Compiled nonempty instances at `d = 3` (section 6).

Helpers are private and carry the stem `Step5KerBA_`.
-/

set_option linter.style.longLine false

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private nkl_zdistInf_sub_comm from RBM3D.Induction.NewKLK
open private NewKLKBA_tail from RBM3D.BA.NewKLKBA
open private Step2IterBA_lam_window from RBM3D.BA.Step2IterBA
open private newKLKL_Cs_ge_one newKLKL_tailT_le_tailW from RBM3D.Induction.NewKLKL
open private NewKLKGen_ward_LKM from RBM3D.Chain.NewKLKGen
open private NewKLKLGen_bound2 from RBM3D.Chain.NewKLKLGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 1: the kernel facts and the decay at `gK = g₀` -/

section KerFacts

variable {d : ℕ}

/-- `Im (E_n + m_F) ≠ 0` along a BA flow (`κ ≤ Im m_F` from `BAflow_real`). -/
private theorem Step5KerBA_hIm {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    (((BAflowEs sz z n : ℝ) : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0 := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  simpa using (lt_of_lt_of_le hκ hr.2).ne'

/-- `STThg` at the BA carrier is `BATheta` (`Step2Kern_Mss_BA`, `S = 1`). -/
private theorem Step5KerBA_STThg_eq (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ)
    (hIm : (((BAflowEs sz z n : ℝ) : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0) (σ σ' : Bool) (t : ℝ) :
    STThg (baFMz sz z) n σ σ' t =
      BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t σ σ' := by
  unfold STThg
  have e : Step2Kern_Mss (baFMz sz z) n σ σ' =
      BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) σ σ' :=
    Step2Kern_Mss_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hIm σ σ'
  have hS : (baFMz sz z).S n = 1 := rfl
  rw [hS, mul_one, e]
  rfl

/-- Row sums of `Θ^{(σ,!σ)}`: `Σ_b Θ_t(a,b) = (1-t)⁻¹` (`BATheta_row_sum_pm`, `BATheta_swap`). -/
private theorem Step5KerBA_row_sum {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ : Bool) (a : Zd d L) :
    ∑ b, BATheta d L g E m t σ (!σ) a b = (1 - (t : ℂ))⁻¹ := by
  cases σ
  · simp only [Bool.not_false]
    rw [BATheta_swap g E m t false true]
    exact BATheta_row_sum_pm d L g κ E m hr t ht0 ht1 a
  · simpa only [Bool.not_true] using BATheta_row_sum_pm d L g κ E m hr t ht0 ht1 a

/-- Column sums of `Θ^{(σ,!σ)}`: `Σ_a Θ_t(a,b) = (1-t)⁻¹` (symmetry `BATheta_isSymm`). -/
private theorem Step5KerBA_col_sum {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ : Bool) (b : Zd d L) :
    ∑ a, BATheta d L g E m t σ (!σ) a b = (1 - (t : ℂ))⁻¹ := by
  have hT := BATheta_isSymm d L g κ E m hr t ht0 ht1 σ (!σ)
  have hsym : ∀ a, BATheta d L g E m t σ (!σ) a b = BATheta d L g E m t σ (!σ) b a := fun a => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hT b) a
  rw [Finset.sum_congr rfl fun a _ => hsym a]
  exact Step5KerBA_row_sum hr ht0 ht1 σ b

/-- Translation: `Θ_t(a,b) = Θ_t(0, b - a)` (`baP8_BATheta_shift`). -/
private theorem Step5KerBA_Theta_shift {L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ) (σ σ' : Bool) (a b : Zd d L) :
    BATheta d L g E m t σ σ' a b = BATheta d L g E m t σ σ' 0 (b - a) := by
  have h := baP8_BATheta_shift (d := d) (L := L) g E m t σ σ' 0 (b - a) a
  rw [zero_add, sub_add_cancel] at h
  exact h

/-- **Target 1, the decay at `gK = g₀`** (`T2501_ThDecayBA`; `∃ C₆` after `κ`, T2498 Amend 1): `thetaKer = Θ_BA M^{(σσ')}`
(`Step2Kern_thetaKer_BA`), the tail `NewKLKBA_tail` (`Q₀` in `(d, 𝔡⁻¹, κ)`) and the row sum `baComp_row_le` (`(1-t)⁻¹`); `C₆ = max Q₀ 1`. -/
theorem baStep5KerGen_thDecay : ∀ d : ℕ, 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      Step5KerGen_ThDecay (baFMz sz z) (BAflowLam0 sz z) 𝔡⁻¹ C₆ := by
  intro d hd κ 𝔡 hκ h𝔡
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨Q₀, hQ₀, HQ⟩ := NewKLKBA_tail d hd 𝔡⁻¹ κ hΛ hκ
  refine ⟨max Q₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro sz ε 𝔠 z hflow n hg hgΛ σ σ' t ht0 ht1
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hIm := Step5KerBA_hIm hκ hflow n
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hker : Step2Gen_thetaKer (baFMz sz z) n σ σ' t =
      BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t σ σ' *
        BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) σ σ' :=
    Step2Kern_thetaKer_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hIm σ σ' t
  rw [hker]
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · have h := HQ (sz.L n) hL (BAflowLam0 sz z n) hg hgΛ (BAflowEs sz z n) _ hr t ht0 ht1 σ σ' a b
    rw [nkl_zdistInf_sub_comm b a]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (tailT_nonneg (Nat.cast_nonneg _)))
  · refine (baComp_row_le hr ht0 ht1 σ σ' a).trans ?_
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by linarith)

/-- **Target 1** (`T2501_KerFactsBA`): the class `IniTermGen_KerFacts` at the BA family, `gK = g₀ = BAflowLam0`, `A = (κ+1)/κ`.  The
semigroup law and the swap need `BAReal` at every `n` (`BAflow_real`), the decay is `baStep5KerGen_thDecay`, the R1 conjunct is
`TwistStep2_lam0_sq`, and the three entrywise facts (column sum, zero mode, short range) are read at the indices with `0 < g₀ ≤ 𝔡⁻¹`,
through `baProp8_holds`, `baProp5s_holds` and translation invariance. -/
theorem baIniTermGen_kerFacts : ∀ d : ℕ,
    IniTermGen_KerFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowLam0 := by
  intro d hd κ 𝔡 hκ h𝔡
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨C₆, hC₆, hdec⟩ := baStep5KerGen_thDecay d hd κ 𝔡 hκ h𝔡
  obtain ⟨C₈, hC₈, H8⟩ := baProp8_holds d 𝔡⁻¹ κ hd hΛ hκ
  obtain ⟨Cs, hCs, c₀, hc₀, H5⟩ := baProp5s_holds d 𝔡⁻¹ κ hd hΛ hκ
  refine ⟨C₆, C₈, Cs, c₀, (κ + 1) / κ, hC₆, hC₈, hCs, hc₀, ?_, ?_⟩
  · rw [le_div_iff₀ hκ]; linarith
  intro sz ε 𝔠 z hflow
  refine ⟨?_, hdec sz ε 𝔠 z hflow, ?_, ?_, ?_⟩
  · -- the semigroup law of `uKer`, every `n`
    intro n σ σ' u v w hv0 hv1 hw0 hw1
    have h := BAuKerSemigroup_holds d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) σ σ' u v w hv0 hv1 hw0 hw1
    simp only [← Step2Kern_uKer_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n (Step5KerBA_hIm hκ hflow n)] at h
    exact h
  · -- R1, every `n`
    intro n
    have h := TwistStep2_lam0_sq hκ hflow n
    refine ⟨?_, h.1, h.2⟩
    have e : BAflowLam0 sz z n * sz.lam n = Real.sqrt (BAflowT0 sz z n) * (sz.lam n * sz.lam n) := by
      unfold BAflowLam0; ring
    rw [e]
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_self_nonneg _)
  · -- the swap E1, every `n`
    intro n t _ _ σ
    rw [Step5KerBA_STThg_eq sz z n (Step5KerBA_hIm hκ hflow n), Step5KerBA_STThg_eq sz z n (Step5KerBA_hIm hκ hflow n)]
    exact BATheta_swap _ _ _ _ σ (!σ)
  · intro n hg hgΛ t ht0 ht1
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have hIm := Step5KerBA_hIm hκ hflow n
    have hL : 3 ≤ sz.L n := sz.three_le_L n
    have hT := Step5KerBA_STThg_eq sz z n hIm
    refine ⟨fun σ b => ?_, fun σ a b => ?_, fun σ a b => ?_⟩
    · rw [hT]
      have := Step5KerBA_col_sum hr ht0 ht1 σ b
      rw [this]; push_cast; rfl
    · -- zero mode
      have h8 := H8 (sz.L n) hL (BAflowLam0 sz z n) hg hgΛ (BAflowEs sz z n) _ hr t ht0 ht1 σ (!σ) (b - a)
      have hsum : ∑ a', ∑ b', BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t σ (!σ) a' b' =
          (((sz.L n : ℕ) : ℂ) ^ d) * (1 - (t : ℂ))⁻¹ := by
        simp only [Step5KerBA_row_sum hr ht0 ht1 σ, Finset.sum_const, Finset.card_univ, BAcard_Zd, nsmul_eq_mul]
        push_cast; ring
      have hL0 : (((sz.L n : ℕ) : ℂ) ^ d) ≠ 0 := by
        have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
        exact_mod_cast (pow_pos this d).ne'
      have e : BATheta0 d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t σ (!σ)
          0 (b - a) =
          STThg (baFMz sz z) n σ (!σ) t a b - (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (((1 - t : ℝ) : ℂ))⁻¹ := by
        unfold BATheta0
        rw [Matrix.of_apply, hsum, hT, Step5KerBA_Theta_shift _ _ _ t σ (!σ) a b]
        have : ((((sz.L n : ℕ) : ℂ) ^ (2 * d)))⁻¹ * ((((sz.L n : ℕ) : ℂ) ^ d) * (1 - (t : ℂ))⁻¹) =
            (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (1 - (t : ℂ))⁻¹ := by
          rw [two_mul, pow_add]; field_simp
        rw [this]; push_cast; rfl
      rw [← e]
      refine h8.trans (le_of_eq ?_)
      ring
    · -- short range
      have h5 := H5 (sz.L n) hL (BAflowLam0 sz z n) hg hgΛ (BAflowEs sz z n) _ hr t ht0 ht1 σ (b - a)
      rw [hT, Step5KerBA_Theta_shift _ _ _ t σ σ a b]
      have hif : (if b - a = 0 then (1 : ℝ) else 0) = if a = b then 1 else 0 := if_congr (sub_eq_zero.trans eq_comm) rfl rfl
      rw [hif, neg_mul] at h5
      exact h5

end KerFacts

/-! ## 2. Target 3: `lem:newKLK` at `ℓ = L` along the BA flow (A9) -/

section NewKLKL

/-- **`lem:newKLK` at `ℓ = L` at one carrier and one size index, with explicit constants** (private per-carrier copy of `stNewKLKLAtgL'_of`,
`Chain/NewKLKLGen.lean:190-299`, `3_5:628-651`; the pattern of `Step2IterBA_newKLKAtN_of`, `BA/Step2IterBA.lean:490`): the facts F5, F8, F9 of
`NewKLKGenHyp` (`Chain/NewKLKGen.lean:383`) are read at the one carrier `Cm` and the one index `n`, the `(TTT2)` bound is the hypothesis `hTT` at the
profile `g = sz.lam n`; F6 and F7 are not read, so no comparison of the kernel coupling with `sz.lam n` enters.  The constant is
`C = 2 (4 + C_K) + C_s C_T`, a function of `C_K, C_T` only (`C_s = 2^{d-2} e`). -/
private theorem Step5KerBA_newKLKLAtN_of {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) {κ C_K CT : ℝ} (hκ : 0 < κ)
    (hCK : 0 ≤ C_K) (hCT : 0 < CT) (hlam : 0 < sz.lam n) (hIm : κ ≤ (Cm.m n).im)
    (hTT : ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
      tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
        tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
      (CT / (1 - u)) * tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ))
    (hsupp : ∀ x y, Cm.S n x y ≠ 0 → zdistInf d (sz.L n) (x - y) ≤ 1) (hrow : ∀ x, ∑ y, ‖Cm.S n x y‖ ≤ 1)
    (hsym : ∀ x y, ‖Cm.S n x y‖ = ‖Cm.S n y x‖)
    (hK : ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ σ : Fin 2 → Bool,
      (∀ a₁ : Zd d (sz.L n), ∑ x, ‖Cm.K n u σ ![x, a₁]‖ ≤ C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) ∧
      (∀ a₀ : Zd d (sz.L n), ∑ y, ‖Cm.K n u σ ![a₀, y]‖ ≤ C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)))
    (hlink : ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∃ ζ : ℂ, ζ.im = (1 - u) * (Cm.m n).im ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
          (a : Fin 2 → Zd d (sz.L n)), Cm.LM n u H σ a = loopFine d (sz.L n) (sz.W n) H ζ σ a) ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (x : Idx d (sz.L n) (sz.W n)),
          Cm.GMM n u H x x = Gres H ζ true x x - Cm.m n)) :
    EtermsMid_NewKLKLAtN Cm n (2 * (4 + C_K) + (2 ^ (d - 2) * Real.exp 1) * CT) (κ / 2) := by
  have hCs := newKLKL_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hCs0 : 0 < Cs := by linarith
  intro u D hu0 hu1 hD H hH hGM σ a
  have hv : 0 < 1 - u := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have hℓ0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
  set Wr : ℝ := ((sz.W n : ℕ) : ℝ) with hWr
  set ℓ : ℝ := ((sz.L n : ℕ) : ℝ) with hℓdef
  set J : ℝ := STJhatMg Cm n D ℓ u H with hJ
  set g : ℝ := sz.lam n with hg
  set P : ℝ → ℝ := tailW d (sz.L n) g u ℓ Wr D with hP
  have hP0 : ∀ r, 0 < P r := fun r => tailW_pos hWpos r
  have hprof : ∀ x y : Zd d (sz.L n), STprof sz n u D ℓ x y =
      (Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) := fun x y => rfl
  have hprof0 : ∀ x y : Zd d (sz.L n), 0 < STprof sz n u D ℓ x y := fun x y => by
    rw [hprof]; have := hP0 ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ); positivity
  have hF : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Zd d (sz.L n)),
      ‖STLKMg Cm n u H σ' a'‖ ≤ J * STprof sz n u D ℓ (a' 0) (a' 1) := by
    intro σ' a'
    have h := Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKMg Cm n u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1)) (Finset.mem_univ (σ', a'))
    rw [div_le_iff₀ (hprof0 _ _)] at h
    exact h
  have hJ0 : 0 ≤ J := by
    have h := hF σ (fun _ => 0)
    have h1 := norm_nonneg (STLKMg Cm n u H σ (fun _ => 0))
    have h2 := hprof0 (0 : Zd d (sz.L n)) 0
    by_contra hneg
    push Not at hneg
    nlinarith
  have hTTT : ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
      tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
        tailT d (sz.L n) g u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
      (CT / (1 - u)) * tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
    fun x y => hTT u hu0 hu1 x y
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = Wr ^ d := by rw [norm_pow, Complex.norm_natCast]
  obtain ⟨ζ, hζ, hLM, hGMd⟩ := hlink u hu0 hu1
  obtain ⟨hKa, hKb⟩ := hK u hu0 hu1 σ
  obtain ⟨hSumA, hSumB⟩ := NewKLKGen_ward_LKM Cm n hκ hIm hu1 hζ hLM hGMd σ hKa hKb H hH hGM
  have hA : ∀ x : Zd d (sz.L n), ‖STLKMg Cm n u H σ ![x, a 1]‖ ≤
      J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (x - a 1) : ℕ) : ℝ)) := by
    intro x
    have h := hF σ ![x, a 1]
    simpa [hprof] using h
  have hB : ∀ y : Zd d (sz.L n), ‖STLKMg Cm n u H σ ![a 0, y]‖ ≤
      J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - y) : ℕ) : ℝ)) := by
    intro y
    have h := hF σ ![a 0, y]
    simpa [hprof] using h
  have key := NewKLKLGen_bound2 hsupp hrow hsym (g := g) (t := u) (D := D) (CT := CT / (1 - u)) hWpos hJ0
    (cW := (Wr ^ d)⁻¹) (by positivity) (fun x => ‖STLKMg Cm n u H σ ![x, a 1]‖)
    (fun y => ‖STLKMg Cm n u H σ ![a 0, y]‖) (fun x => norm_nonneg _) (fun y => norm_nonneg _)
    (a 0) (a 1) hA hB (hSumA (a 1)) (hSumB (a 0)) hTTT
  have hB2 : ‖STELKLKMg Cm n u H σ a‖ ≤ Wr ^ d *
      (2 * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) * ((4 + C_K) * ((Wr ^ d)⁻¹ * (1 - u)⁻¹)) +
        (J * (Wr ^ d)⁻¹) ^ 2 * (Cs * ((CT / (1 - u)) *
          tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)))) := by
    unfold STELKLKMg
    rw [norm_mul, hWd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => norm_sum_le _ _).trans ?_)
    refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_) key
    rw [norm_mul, norm_mul]
  have hw : 0 < Wr ^ d := by positivity
  set Q : ℝ := 2 * (4 + C_K) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  set Ps : ℝ := P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hPs
  set Ts : ℝ := tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hTs
  have hTsP : Ts ≤ Ps := newKLKL_tailT_le_tailW hℓ0 (Nat.cast_nonneg _)
  have hTs0 : 0 ≤ Ts := tailT_nonneg (Nat.cast_nonneg _)
  have hPs0 : 0 < Ps := hP0 _
  have hω0 : 0 < Wr ^ (-D) := Real.rpow_pos_of_pos hWpos _
  have hpr : STprof sz n u D ℓ (a 0) (a 1) = (Wr ^ d)⁻¹ * Ps := hprof _ _
  have e1 : Wr ^ d * (2 * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) * ((4 + C_K) * ((Wr ^ d)⁻¹ * (1 - u)⁻¹))) =
      Q / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by
    rw [hQ]
    field_simp
  have e2 : Wr ^ d * ((J * (Wr ^ d)⁻¹) ^ 2 * (Cs * (CT / (1 - u) * Ts))) =
      Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ts)) := by
    field_simp
  rw [hpr]
  refine hB2.trans ?_
  rw [mul_add, e1, e2]
  have hq : J ^ 2 * ((Wr ^ d)⁻¹ * Ts) ≤ J ^ 2 * ((Wr ^ d)⁻¹ * Ps) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTsP (by positivity)) (sq_nonneg _)
  have h1 : Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ts)) ≤
      Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have hdiff : (Q + Cs * CT) / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps) + J * (Wr ^ d)⁻¹ * Wr ^ (-D)) -
      (Q / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) +
        Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps))) =
      Q / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) +
        Cs * CT / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by ring
  have hn1 : 0 ≤ Q / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) := by positivity
  have hn2 : 0 ≤ Cs * CT / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by positivity
  linarith

/-- **Target 3** (`T2501_NewKLKLBA`; A9, DECISIONS §301 (2)): `lem:newKLK` at `ℓ = L`, sharp form, along every BA flow at the Step2Mat family
`baStep2Mat sz g₀ E`, with `Ck = 2 (4 + C_K) + C_s C_T`, `δ₀ = κ/2` before the sizes.  Per index `n` in the window `0 < g₀_n ≤ 𝔡⁻¹`,
`0 < g_n ≤ 𝔡⁻¹` (`BAflow_lam0_window`, `(eq:WO)`), the per-carrier copy is applied at `baStep2Mat sz g₀ E`: F5, F8, F9 come from `baNewKLKGenHyp` at
`sz.withLam g₀` (`baStep2Fam (sz.withLam g₀) (fun _ => E n)` and `baStep2Mat sz g₀ E` have the same fields at index `n`, definitionally, the pattern of
`baStep2_newKLK`, `BA/Step2IterBA.lean:706-731`; the datum `κ ≤ Im m_F` is `EMn2BA_mF_data`), `(TTT2)` is `ekPropTInf_holds` at `g = sz.lam n`.
F7 is not read (R1 does not enter). -/
theorem baEtermsMid_newKLKL : ∀ d : ℕ, EtermsMid_NewKLKL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) := by
  intro d hd κ 𝔡 hκ h𝔡
  obtain ⟨CT, hCT, HT⟩ := ekPropTInf_holds d hd
  obtain ⟨-, C_K, -, hCK, hF5, -, -, hF8, hF9⟩ := baNewKLKGenHyp hd κ 𝔡 hκ h𝔡
  have hCs := newKLKL_Cs_ge_one (d := d)
  have hCs0 : 0 < 2 ^ (d - 2) * Real.exp 1 := by linarith
  refine ⟨2 * (4 + C_K) + (2 ^ (d - 2) * Real.exp 1) * CT, κ / 2, by positivity, by positivity, ?_⟩
  intro ε 𝔠 sz z hflow
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, Step2IterBA_lam_window hflow] with n hn1 hn2
  have hm := (EMn2BA_mF_data sz hflow n).1
  exact Step5KerBA_newKLKLAtN_of (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n hκ hCK hCT hn2.1 hm
    (fun u hu0 hu1 x y => HT (sz.L n) (sz.lam n) u u hn2.1 hu0 le_rfl hu1 (le_total _ _) x y)
    (hF5 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) hn1.1 hn1.2 hm).1
    (hF5 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) hn1.1 hn1.2 hm).2.1
    (hF5 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) hn1.1 hn1.2 hm).2.2
    (fun u hu0 hu1 σ => hF8 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) u hn1.1 hn1.2 hm hu0 hu1 σ)
    (fun u hu0 hu1 => hF9 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) u hn1.1 hn1.2 hm hu0 hu1)

end NewKLKL

/-! ## 3. Target 4: D2, the flow modulus at the BA carrier -/

section FlowMod

/-- **Target 4** (`T2501_FlowModBA`; D2, the `hFM` text): the model matrix `Hm = sz.seqHflowBA g₀` (Hermitian: `g₀ Ψ` is Hermitian, `seqHflow` is
Hermitian) moves by `2 N √|u-u'|` entrywise on `G = contGood (sz.withLam 0)` (`g₀ Ψ` cancels in the difference,
`lemDecCalELipG_seqHflow_entry_sub`), `c = 1`; the clauses `LM` and `GMM` are definitional at `baStep2Mat`.  `HighProbAt` needs `size → ∞`
(`Admissible`, `cont_highProbAt_good`). -/
theorem baLemDecCalELipG_flowMod : ∀ d : ℕ, ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      LemDecCalELipG_FlowMod (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) c := by
  intro d κ ε 𝔡 _ _ _
  refine ⟨1, zero_le_one, fun sz 𝔠 z h => ?_⟩
  refine ⟨fun n u => sz.seqHflowBA (BAflowLam0 sz z) n u, RBM.Ind.ContinuityNet.contGood (sz.withLam 0), fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, RBM.Ind.ContinuityNet.cont_highProbAt_good (sz.withLam 0) (sz.tendsto_size h.1.2.2.1),
    fun n ω hω u u' hu0 _ hu'0 _ => ⟨?_, fun x y => ?_⟩⟩
  · have h1 : (((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d (sz.L n) (sz.W n)).eq,
        show star ((BAflowLam0 sz z n : ℝ) : ℂ) = ((BAflowLam0 sz z n : ℝ) : ℂ) from Complex.conj_ofReal _]
    exact h1.add (Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω)
  · have h := lemDecCalELipG_seqHflow_entry_sub (sz.withLam 0) n hω hu0 hu'0 x y
    simp only [Sizes.seqHflowBA, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, add_sub_add_left_eq_sub]
    exact h

end FlowMod

/-! ## 4. Target 5: D3, the time modulus of `𝒦^{(2)}` at the BA carrier -/

section KLip

variable {d : ℕ}

/-- `(1 - u)⁻¹ ≤ 2 N` for `u ≤ t₀_n`: `1 - u ≥ 1 - t₀ ≥ Im z_n / 2 ≥ N^{-1+ε} / 2` (`EMn2BA_one_sub_T0`), `N^{1-ε} ≤ N`. -/
private theorem Step5KerBA_one_sub_inv {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {sz : Sizes d} {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u : ℝ} (hu : u ≤ BAflowT0 sz z n) :
    (1 - u)⁻¹ ≤ 2 * ((sz.size n : ℕ) : ℝ) := by
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hz := EMn2BA_one_sub_T0 hκ sz hflow n
  have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 2 ≤ 1 - u := by linarith
  calc (1 - u)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 2)⁻¹ := inv_anti₀ (by positivity) h1
    _ = 2 * ((sz.size n : ℕ) : ℝ) ^ (-(-1 + ε)) := by
        rw [Real.rpow_neg (by linarith), inv_div, div_eq_mul_inv]
    _ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
    _ = _ := by rw [Real.rpow_one]

/-- The resolvent difference `(Θ_u - Θ_{u'}) M = (u - u') (Θ_u M)(Θ_{u'} M)` at BA data (`BATheta_resolvent`: `Θ_u = 1 + u Θ_u M`,
`Θ_{u'} = 1 + u' M Θ_{u'}`). -/
private theorem Step5KerBA_Theta_sub {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {u u' : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hu'0 : 0 ≤ u') (hu'1 : u' < 1) (σ₁ σ₂ : Bool) :
    (BATheta d L g E m u σ₁ σ₂ - BATheta d L g E m u' σ₁ σ₂) * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ =
      (((u - u' : ℝ) : ℂ)) • ((BATheta d L g E m u σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) *
        (BATheta d L g E m u' σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂)) := by
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ with hQ
  set T := BATheta d L g E m u σ₁ σ₂ with hT
  set T' := BATheta d L g E m u' σ₁ σ₂ with hT'
  have hR : T = 1 + (u : ℂ) • (T * Q) := (BATheta_resolvent d L g κ E m hr u hu0 hu1 σ₁ σ₂).2
  have hL : T' = 1 + (u' : ℂ) • (Q * T') := (BATheta_resolvent d L g κ E m hr u' hu'0 hu'1 σ₁ σ₂).1
  have h1 : T * (1 - (u : ℂ) • Q) = 1 := by
    rw [mul_sub, mul_one, mul_smul_comm]
    exact sub_eq_iff_eq_add.2 hR
  have h2 : (1 - (u' : ℂ) • Q) * T' = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc]
    exact sub_eq_iff_eq_add.2 hL
  have key : T - T' = ((u - u' : ℝ) : ℂ) • (T * Q * T') := by
    calc T - T' = T * ((1 - (u' : ℂ) • Q) * T') - (T * (1 - (u : ℂ) • Q)) * T' := by
          rw [h1, h2, mul_one, one_mul]
      _ = _ := by
          push_cast
          simp only [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, sub_smul, Matrix.mul_assoc]
          abel
  rw [key, smul_mul_assoc]
  congr 1
  simp only [Matrix.mul_assoc]

/-- An entry of a product is at most the product of the row-sum bounds. -/
private theorem Step5KerBA_entry_mul_le {L : ℕ} [NeZero L] (X Y : Matrix (Zd d L) (Zd d L) ℂ) {a b : ℝ}
    (hX : ∀ x, ∑ y, ‖X x y‖ ≤ a) (hY : ∀ x, ∑ y, ‖Y x y‖ ≤ b) (x y : Zd d L) : ‖(X * Y) x y‖ ≤ a * b := by
  have hb : 0 ≤ b := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hY x)
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ c, ‖X x c * Y c y‖ = ∑ c, ‖X x c‖ * ‖Y c y‖ := Finset.sum_congr rfl fun c _ => norm_mul _ _
    _ ≤ ∑ c, ‖X x c‖ * b := Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
        (((Finset.single_le_sum (f := fun y' => ‖Y c y'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)).trans (hY c))) (norm_nonneg _)
    _ = (∑ c, ‖X x c‖) * b := (Finset.sum_mul _ _ _).symm
    _ ≤ a * b := mul_le_mul_of_nonneg_right (hX x) hb

/-- **Target 5** (`T2501_KLipBA`; D3, the `k = 2` text of `NQEndFlowGen_KLip`, the inline premise `hKs` of `stDuhamelIgL_of`, `stDuhamelIIgL_of`):
`𝒦^{(2)}_u = W^{-d} (Θ_u M)(a₀, a₁)` (`baKsol_two` at `g₀ > 0`, eventually `BAflow_lam0_window`), `𝒦^{(2)}_u - 𝒦^{(2)}_{u'} =
W^{-d} (u - u') (Θ_u M)(Θ_{u'} M)` (`Step5KerBA_Theta_sub`), entry `≤ W^{-d} |u - u'| (1-u)⁻¹ (1-u')⁻¹` (`baComp_row_le`), and
`(1-u)⁻¹ ≤ 2 N` for `u ≤ t₀` (`EMn2BA_one_sub_T0`): `4 N² ≤ N⁶` for `N ≥ 2` (eventually). -/
theorem baKLip_two : ∀ d : ℕ, 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → NQEndFlowGen_KLip (baFMz sz z) t 2 := by
  intro d hd sz κ ε 𝔠 𝔡 z hκ hε hflow t ht
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, (sz.tendsto_size hflow.1.2.2.1).eventually_ge_atTop 2] with n hn hN2
  intro u u' hu0 hut hu'0 hu't σ a
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hT1 : BAflowT0 sz z n < 1 := EMn2BA_T0_lt_one hκ sz hflow n
  have hu1 : u < 1 := lt_of_le_of_lt (hut.trans (ht n)) hT1
  have hu'1 : u' < 1 := lt_of_le_of_lt (hu't.trans (ht n)) hT1
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hK2 : ∀ v : ℝ, 0 ≤ v → v < 1 → (baFMz sz z).K n v σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
        (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (σ 0) (σ 1) *
          BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
            (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1)) (a 0) (a 1) :=
    fun v hv0 hv1 => baKsol_two d hκ hn.1 hL (sz.W n) hr ⟨hv0, hv1⟩ σ a
  rw [hK2 u hu0 hu1, hK2 u' hu'0 hu'1, ← mul_sub, ← Matrix.sub_apply, ← Matrix.sub_mul,
    Step5KerBA_Theta_sub hr hu0 hu1 hu'0 hu'1 (σ 0) (σ 1), Matrix.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_inv, norm_pow, Complex.norm_natCast]
  have hv : 0 < 1 - u := by linarith
  have hv' : 0 < 1 - u' := by linarith
  have hN : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN2
  have h1 := Step5KerBA_one_sub_inv hκ hε hflow n (hut.trans (ht n))
  have h2 := Step5KerBA_one_sub_inv hκ hε hflow n (hu't.trans (ht n))
  have hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (Nat.one_le_cast.2 (sz.W_pos n)))
  have hent := Step5KerBA_entry_mul_le _ _ (fun x => baComp_row_le hr hu0 hu1 (σ 0) (σ 1) x)
    (fun x => baComp_row_le hr hu'0 hu'1 (σ 0) (σ 1) x) (a 0) (a 1)
  have hN4 : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 4 :=
    calc (4 : ℝ) ≤ 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hN 4
  have hprod : (1 - u)⁻¹ * (1 - u')⁻¹ ≤ (2 * ((sz.size n : ℕ) : ℝ)) * (2 * ((sz.size n : ℕ) : ℝ)) :=
    mul_le_mul h1 h2 (inv_nonneg.2 hv'.le) (by linarith)
  have hfin : (2 * ((sz.size n : ℕ) : ℝ)) * (2 * ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) := by
    have : ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) = ((sz.size n : ℕ) : ℝ) ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hN4 (sq_nonneg ((sz.size n : ℕ) : ℝ))]
  have hA0 : 0 ≤ |u - u'| := abs_nonneg _
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (|u - u'| * ‖((BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u (σ 0) (σ 1) * BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n)
          (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1)) *
        (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u' (σ 0) (σ 1) *
          BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
            (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1))) (a 0) (a 1)‖)
      ≤ 1 * (|u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹)) :=
        mul_le_mul hW (mul_le_mul_of_nonneg_left hent hA0) (by positivity) zero_le_one
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'| := by
        rw [one_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hprod.trans hfin) hA0

end KLip

/-! ## 5. Targets 6 and 7: the inline premises and `lem:newKLK` at `ℓ = L` at the BA family -/

/-! ## 6. Compiled nonempty instances at `d = 3` (target 8)

`sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), the flow `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`
(`BA/FlowPins.lean:1214`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`.  The window
`0 < g₀_n ≤ 𝔡⁻¹ = 10` holds at every `n` (`Step5KerBA_inst_window`: `g₀_n ≤ lam_n ≤ 1`).  Every
deterministic premise is discharged; no premise is a pin of another gate. -/

end RBM.BA

end
