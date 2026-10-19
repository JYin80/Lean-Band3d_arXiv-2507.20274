/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.CltFarUGen
import RBM3D.Chain.Step2Kern
import RBM3D.Evolution.ExpInv
import RBM3D.Evolution.MeanFar
import RBM3D.BA.EMn2BA
import RBM3D.BA.Step2CloseBA
import RBM3D.BA.Ward
import RBM3D.BA.KSolve
import RBM3D.BA.KTreeRep
import RBM3D.BA.KInduct
import RBM3D.BA.Prop6Path
import RBM3D.BA.TwistStep2
import RBM3D.BA.CombesThomas

/-!
# The class `IniTermGen_CltFlow` at the block Anderson tuple

The block Anderson proofs of the five inputs `STThPropsg`, `STKpropsg`, `STMfarg`, `STKfargL`,
`CltInvg` over the carrier `baFMz sz z` along every `BAFlow`, and the class `IniTermGen_CltFlow`
(`Chain/CltFarUGen.lean`) at `(fun sz => seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`
(`baIniTermGen_cltFlow`).

Coupling: the propagator `STThg (baFMz sz z)` is `BATheta`
at the kernel coupling `g₀ = BAflowLam0`; every estimate of `STThPropsg`, `STKpropsg` is stated at
`sz.lam`.  The one comparison is `TwistStep2_lam0_sq`: `g₀² ≤ g²` and `g² ≤ A g₀²` with
`A = (κ+1)/κ`, used as `(g₀²+x)⁻¹ ≤ A (g²+x)⁻¹`, `Bparam(g₀) ≤ A Bparam(g)` and
`ℓ_t(g₀) ≤ ℓ_t(g)` (`EMn2BA_ellT_mono_g`).  Constants depend on `(d, κ, 𝔡)` only.

Paper: arXiv:2507.20274, Lemma 2.19 (`lem_propTH`) properties 5-7 (with the block Anderson remark after (2.67)
`prop:ThfadC_short`), Lemma 8.3 (`lem:propM`), (2.71) `Kn2sol`, and the hypotheses of Lemma 5.1 (`lem;CLT`).

The argument follows the band formalization: the class proof is that of `Chain/CltFarUGen.lean`, and the producers
of `STThPropsg`, `STKpropsg` follow `Evolution/MeanFarG.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The data at one size index -/

section Data

variable {d : ℕ}

private theorem CltFlowBA_Im_ne {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    (((BAflowEs sz z n : ℝ) : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0 := by
  have h := (EMn2BA_mF_data sz hflow n).1
  rw [Complex.add_im, Complex.ofReal_im, zero_add]
  exact (lt_of_lt_of_le hκ h).ne'

private theorem CltFlowBA_STThg {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (σ σ' : Bool) (t : ℝ) :
    STThg (baFMz sz z) n σ σ' t = BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t σ σ' := by
  have hS : (baFMz sz z).S n = 1 := rfl
  unfold STThg Step2Gen_Theta BATheta PropThetaQ
  rw [hS, mul_one]
  have := Step2Kern_Mss_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n (CltFlowBA_Im_ne hκ hflow n) σ σ'
  rw [show baFMz sz z = baFM sz (BAflowLam0 sz z) (BAflowEs sz z) from rfl, this]

/-- The comparison of `g₀` with `g` at one index: `0 < g₀` gives `0 < g`, `g₀ ≤ g`, and `g² ≤ A g₀²`, `A = (κ+1)/κ` (`TwistStep2_lam0_sq`). -/
private theorem CltFlowBA_cmp {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {sz : Sizes d} {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (hg0 : 0 < BAflowLam0 sz z n) :
    0 < sz.lam n ∧ BAflowLam0 sz z n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2 := by
  have hsq := TwistStep2_lam0_sq hκ hflow n
  have hlam : 0 < sz.lam n := by
    by_contra h
    have : Real.sqrt (BAflowT0 sz z n) * sz.lam n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (not_lt.1 h)
    exact absurd hg0 (not_lt.2 this)
  exact ⟨hlam, (sq_le_sq₀ hg0.le hlam.le).1 hsq.1, hsq.2⟩

private theorem CltFlowBA_inv_le {g₀ g x A : ℝ} (hx : 0 < x) (hA : 1 ≤ A) (h1 : g ^ 2 ≤ A * g₀ ^ 2) :
    (g₀ ^ 2 + x)⁻¹ ≤ A * (g ^ 2 + x)⁻¹ := by
  have h0 : 0 < g₀ ^ 2 + x := by positivity
  have h2 : 0 < g ^ 2 + x := by positivity
  calc (g₀ ^ 2 + x)⁻¹ = 1 / (g₀ ^ 2 + x) := (one_div _).symm
    _ ≤ A / (g ^ 2 + x) := by
        rw [div_le_div_iff₀ h0 h2]
        nlinarith [sq_nonneg g₀]
    _ = A * (g ^ 2 + x)⁻¹ := div_eq_mul_inv _ _

private theorem CltFlowBA_Bparam_le (d : ℕ) {g₀ g t A : ℝ} {L K : ℕ} (ht : t < 1) (hA : 1 ≤ A)
    (h1 : g ^ 2 ≤ A * g₀ ^ 2) : Bparam d L g₀ t K ≤ A * Bparam d L g t K := by
  have hx : 0 < |1 - t| := abs_pos.2 (by linarith)
  have e1 := CltFlowBA_inv_le hx hA h1
  have hK : 0 ≤ (((K : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hL : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  unfold Bparam
  calc _ ≤ A * (g ^ 2 + |1 - t|)⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ + A * ((L : ℝ) ^ d * |1 - t|)⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_right e1 hK) (le_mul_of_one_le_left hL hA)
    _ = _ := by ring

private theorem CltFlowBA_scale {X C P₀ P A R Q : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hP : P₀ ≤ A * P) (h : X ≤ C * P₀ * R * Q) : X ≤ (A * C) * P * R * Q := by
  refine h.trans ?_
  have : C * P₀ * R * Q ≤ C * (A * P) * R * Q := by gcongr
  calc _ ≤ _ := this
    _ = _ := by ring

end Data

/-! ## 2. `STThPropsg`: shift, symmetry, `(prop:ThfadC)`, `(prop:BD1)`, `(prop:BD2)` of `STThg (baFMz sz z)` at `sz.lam` -/

section ThProps

variable {d : ℕ}

/-- **`STThPropsg` along every BA flow** (the second conjunct of `TwistStep2_lam0_sq` only).
`Θ = STThg (baFMz sz z) = BATheta` at the kernel coupling `g₀` (`Step2Kern_Mss_BA`); shift `baP8_BATheta_shift`, symmetry
`BATheta_isSymm`, decay and the two differences from `baProp5to8_holds d 𝔡⁻¹ κ (1/2)` (`Λ = 𝔡⁻¹`, window `0 < g₀ ≤ 𝔡⁻¹` eventually,
`BAflow_lam0_window`), each converted from `g₀` to `sz.lam` through `g² ≤ A g₀²`, `A = (κ+1)/κ`, `ℓ_t(g₀) ≤ ℓ_t(g)`.
Constants `(A C₅, c₅, A C₆, A C₇)` depend on `(d, κ, 𝔡)` only. -/
theorem baSTThPropsg_holds (d : ℕ) (hd : 3 ≤ d) : ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → STThPropsg (baFMz sz z) := by
  intro κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hA1 : 1 ≤ (κ + 1) / κ := by rw [le_div_iff₀ hκ]; linarith
  have hA0 : 0 < (κ + 1) / κ := by linarith
  obtain ⟨C5, hC5, c5, hc5, H5⟩ := baProp5to8_holds d 𝔡⁻¹ κ (1 / 2) |>.decay hd hΛ hκ
  obtain ⟨C6, hC6, H6⟩ := baProp5to8_holds d 𝔡⁻¹ κ (1 / 2) |>.diffOne hd hΛ hκ (by norm_num) (by norm_num)
  obtain ⟨C7, hC7, H7⟩ := baProp5to8_holds d 𝔡⁻¹ κ (1 / 2) |>.diffTwo hd hΛ hκ (by norm_num) (by norm_num)
  refine ⟨(κ + 1) / κ * C5, c5, (κ + 1) / κ * C6, (κ + 1) / κ * C7, by positivity, hc5, by positivity, by positivity, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hwin t ht0 ht1 σ hσ
  obtain ⟨hg0, hgΛ⟩ := hwin
  obtain ⟨hlam, hle, hR1⟩ := CltFlowBA_cmp hκ hflow n hg0
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hL := sz.three_le_L n
  have hx : 0 < |1 - t| := abs_pos.2 (by linarith)
  simp only [CltFlowBA_STThg hκ hflow n]
  refine ⟨fun x y => ?_, fun x y => ?_, fun a => ?_, fun a r hr' => ?_, fun a r hr' => ?_⟩
  · have := baP8_BATheta_shift (d := d) (L := sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t (σ 0) (σ 1) 0 (y - x) x
    rwa [zero_add, sub_add_cancel] at this
  · have := congrFun (congrFun (BATheta_isSymm d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hr t ht0 ht1 (σ 0) (σ 1)) x) y
    simpa [Matrix.transpose_apply] using this.symm
  · have h := H5 (sz.L n) hL (BAflowLam0 sz z n) hg0 hgΛ (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
      hr t ht0 ht1 (σ 0) (σ 1) a
    refine h.trans ?_
    have hB := CltFlowBA_Bparam_le d (L := sz.L n) (K := zdistD d (sz.L n) a) ht1 hA1 hR1
    have hell : ellT (sz.L n) (BAflowLam0 sz z n) t ≤ ellT (sz.L n) (sz.lam n) t := EMn2BA_ellT_mono_g (sz.L n) hle t
    have hell0 : 0 < ellT (sz.L n) (BAflowLam0 sz z n) t :=
      ellT_pos (by exact_mod_cast (by omega : 1 ≤ sz.L n))
    have hexp : Real.exp (-c5 * (zdistD d (sz.L n) a : ℝ) / ellT (sz.L n) (BAflowLam0 sz z n) t) ≤
        Real.exp (-c5 * (zdistD d (sz.L n) a : ℝ) / ellT (sz.L n) (sz.lam n) t) := by
      refine Real.exp_le_exp.2 ?_
      rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) hell0 hell
    have hBl : 0 ≤ C5 * ((κ + 1) / κ * Bparam d (sz.L n) (sz.lam n) t (zdistD d (sz.L n) a)) := by
      have : 0 ≤ Bparam d (sz.L n) (sz.lam n) t (zdistD d (sz.L n) a) := by unfold Bparam; positivity
      exact mul_nonneg hC5.le (mul_nonneg hA0.le this)
    calc C5 * Bparam d (sz.L n) (BAflowLam0 sz z n) t (zdistD d (sz.L n) a) *
          Real.exp (-c5 * (zdistD d (sz.L n) a : ℝ) / ellT (sz.L n) (BAflowLam0 sz z n) t)
        ≤ C5 * ((κ + 1) / κ * Bparam d (sz.L n) (sz.lam n) t (zdistD d (sz.L n) a)) *
          Real.exp (-c5 * (zdistD d (sz.L n) a : ℝ) / ellT (sz.L n) (sz.lam n) t) := by
          gcongr
      _ = _ := by ring
  · have h := H6 (sz.L n) hL (BAflowLam0 sz z n) hg0 hgΛ (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
      hr t ht0 ht1 (σ 0) (σ 1) a r hr'
    exact CltFlowBA_scale hC6.le (by positivity) (by positivity) (CltFlowBA_inv_le hx hA1 hR1) h
  · have h := H7 (sz.L n) hL (BAflowLam0 sz z n) hg0 hgΛ (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
      hr t ht0 ht1 (σ 0) (σ 1) a r hr'
    exact CltFlowBA_scale hC7.le (by positivity) (by positivity) (CltFlowBA_inv_le hx hA1 hR1) h

end ThProps

/-! ## 3. `STMfarg`: the entries of `M` across far blocks, and the Ward row of `M` -/

section Mfarg

variable {d : ℕ}

/-- The Ward row of the fine-lattice matrix `M = M^{(B)} ⊗ I_{W^d}` (`BAMfine`): `Σ_y |M_xy|² = Σ_b |M^{(B)}_{[x] b}|² = 1`. -/
private theorem CltFlowBA_Mfine_row (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (hm : 0 < (BAmF sz lam0 E n).im)
    (h : BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (x : Idx d (sz.L n) (sz.W n)) :
    ∑ y, ‖BAMfine sz lam0 E n x y‖ ^ 2 = 1 := by
  have e : ∀ y : Idx d (sz.L n) (sz.W n), ‖BAMfine sz lam0 E n x y‖ ^ 2 =
      (fun p : Vtx d (sz.L n) (sz.W n) => if p.2 = (split d (sz.L n) (sz.W n) x).2 then
        ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) (split d (sz.L n) (sz.W n) x).1 p.1‖ ^ 2 else 0)
        (splitEquiv d (sz.L n) (sz.W n) y) := by
    intro y
    rw [BAMfine_eq sz lam0 E n hm x y]
    have hy : splitEquiv d (sz.L n) (sz.W n) y = split d (sz.L n) (sz.W n) y := rfl
    rw [hy]
    by_cases hh : (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2
    · simp [hh]
    · simp [hh, Ne.symm hh]
  rw [Finset.sum_congr rfl fun y _ => e y,
    Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n))
      (fun p : Vtx d (sz.L n) (sz.W n) => if p.2 = (split d (sz.L n) (sz.W n) x).2 then
        ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) (split d (sz.L n) (sz.W n) x).1 p.1‖ ^ 2 else 0),
    Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact BAMB_row_sq_real d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) h _

/-- One decay profile for both branches of Lemma 8.3 `lem:propM` (3) (`baPropM_holds`):
`‖M^{(B)}_{ab}‖ ≤ K e^{-c_M |a-b|}`, `K = max (c⁻¹, 1)`, `c_M = min (c, log 2)`; constants in `(d, κ, 𝔡)` only.  Small branch
`g₀ < (2C)⁻¹`: `(C g₀)^{|a-b|} ≤ 2^{-|a-b|}`; large branch: `c⁻¹ e^{-c|a-b|}`. -/
private theorem CltFlowBA_MB_decay (hd : 3 ≤ d) {κ 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ K cM : ℝ, 1 ≤ K ∧ 0 < cM ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 𝔡⁻¹ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ a b : Zd d L,
        ‖BAMB d L g (E : ℂ) m a b‖ ≤ K * Real.exp (-cM * (zdistD d L (a - b) : ℝ)) := by
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨C, hC, c, hc, H⟩ := baPropM_holds d 𝔡⁻¹ κ hd hΛ hκ
  refine ⟨max c⁻¹ 1, min c (Real.log 2), le_max_right _ _, lt_min hc (Real.log_pos (by norm_num)), ?_⟩
  intro L hL g hg hgΛ E m hr a b
  have : NeZero L := ⟨by omega⟩
  obtain ⟨-, -, -, -, hsm, hlg⟩ := H L hL g hg hgΛ E m hr
  have hk : (0 : ℝ) ≤ (zdistD d L (a - b) : ℝ) := Nat.cast_nonneg _
  have hK0 : 0 < max c⁻¹ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  by_cases hg2 : g < (2 * C)⁻¹
  · have h1 := (hsm hg2 a b).2
    have hCg : C * g ≤ 1 / 2 := by
      have : C * g < C * (2 * C)⁻¹ := mul_lt_mul_of_pos_left hg2 hC
      have e : C * (2 * C)⁻¹ = 1 / 2 := by field_simp
      linarith
    have h2 : (C * g) ^ zdistD d L (a - b) ≤ (1 / 2 : ℝ) ^ zdistD d L (a - b) :=
      pow_le_pow_left₀ (by positivity) hCg _
    have h3 : (1 / 2 : ℝ) ^ zdistD d L (a - b) = Real.exp (-(Real.log 2) * (zdistD d L (a - b) : ℝ)) := by
      rw [neg_mul, Real.exp_neg, mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log (by norm_num), one_div, inv_pow]
    have h4 : Real.exp (-(Real.log 2) * (zdistD d L (a - b) : ℝ)) ≤ Real.exp (-(min c (Real.log 2)) * (zdistD d L (a - b) : ℝ)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [min_le_right c (Real.log 2)]
    calc ‖BAMB d L g (E : ℂ) m a b‖ ≤ (C * g) ^ zdistD d L (a - b) := h1
      _ ≤ _ := h2.trans (h3 ▸ h4.trans (le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _)))
  · have h1 := hlg (not_lt.1 hg2) a b
    refine h1.trans ?_
    have h4 : Real.exp (-c * (zdistD d L (a - b) : ℝ)) ≤ Real.exp (-(min c (Real.log 2)) * (zdistD d L (a - b) : ℝ)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [min_le_left c (Real.log 2)]
    exact mul_le_mul (le_max_left _ _) h4 (Real.exp_pos _).le hK0.le

/-- **`STMfarg` along every BA flow**: `M = M^{(B)} ⊗ I` has entries
`≤ W^{-D}` between blocks at distance `≥ c (log W)³ ℓ_τ ≥ c (log W)³` (`ℓ_τ ≥ 1`), from the decay profile of `M^{(B)}` at `g₀`
(`CltFlowBA_MB_decay`) and `log W → ∞` (`W ≥ N^𝔠`).  Needs `|blk x - blk y|_∞ ≤ |blk x - blk y|_L` only; no comparison of `g₀` with `g` is needed. -/
theorem baSTMfarg_holds (d : ℕ) (hd : 3 ≤ d) : ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ τ : ℕ → ℝ, STMfarg (baFMz sz z) τ := by
  intro κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow τ c₀ D hc₀ hD
  obtain ⟨K, cM, hK, hcM, H⟩ := CltFlowBA_MB_decay hd hκ h𝔡
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hWt : Filter.Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_atTop_mono' _ hflow.1.2.2.2.1 ((tendsto_rpow_atTop h𝔠).comp hflow.1.2.2.1)
  have hlogW := Real.tendsto_log_atTop.comp hWt
  set X0 : ℝ := max 1 (Real.sqrt ((D + |Real.log K|) / (cM * c₀))) with hX0
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, hlogW.eventually_ge_atTop X0] with n hwin hX x y hfar
  obtain ⟨hg0, hgΛ⟩ := hwin
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hLn := sz.three_le_L n
  have hx1 : (1 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hX
  have hx2 : (D + |Real.log K|) / (cM * c₀) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 2 :=
    (Real.sqrt_le_iff.1 ((le_max_right _ _).trans hX)).2
  have hcc : 0 < cM * c₀ := mul_pos hcM hc₀
  have hx3 : D + |Real.log K| ≤ cM * c₀ * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by
    rwa [div_le_iff₀ hcc, mul_comm] at hx2
  have hell : 1 ≤ ellT (sz.L n) (sz.lam n) (τ n) := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  have hdist : c₀ * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 ≤ (zdistD d (sz.L n) (STblk sz n x - STblk sz n y) : ℝ) := by
    refine le_trans ?_ (hfar.trans (by exact_mod_cast zdistInf_le_zdistD d (sz.L n) (STblk sz n x - STblk sz n y)))
    exact le_mul_of_one_le_right (by positivity) hell
  have hM : ‖(baFMz sz z).M n x y‖ ≤ K * Real.exp (-cM * (zdistD d (sz.L n) (STblk sz n x - STblk sz n y) : ℝ)) := by
    have e : (baFMz sz z).M n x y = BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n x y := rfl
    rw [e, BAMfine_eq sz _ _ n (lt_of_lt_of_le hκ (EMn2BA_mF_data sz hflow n).1) x y]
    split_ifs
    · exact H (sz.L n) hLn (BAflowLam0 sz z n) hg0 hgΛ (BAflowEs sz z n) _ hr _ _
    · rw [norm_zero]; positivity
  refine hM.trans ?_
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  rw [Real.rpow_def_of_pos hWpos]
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  rw [← Real.exp_log hK0, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  set x₀ := Real.log ((sz.W n : ℕ) : ℝ) with hx₀
  have hl : Real.log K ≤ |Real.log K| := le_abs_self _
  have h4 : cM * (c₀ * x₀ ^ 3) ≤ cM * (zdistD d (sz.L n) (STblk sz n x - STblk sz n y) : ℝ) :=
    mul_le_mul_of_nonneg_left hdist hcM.le
  nlinarith [mul_nonneg (abs_nonneg (Real.log K)) (sub_nonneg.2 hx1), mul_le_mul_of_nonneg_left hx3 (by linarith : (0 : ℝ) ≤ x₀)]

end Mfarg

/-! ## 4. `STKfargL`, `CltRepg` and `CltInvg` at the BA tuple -/

section Rep

variable {d : ℕ}

/-- **`STKfargL` along every BA flow**: `baEMn2ExpHK` (`BA/EMn2BA`, from (2.71) `Kn2sol`)
is the premise `emn2ExpHK` whose conclusion is `STKfargL` verbatim (`emn2ExpEllStar` unfolds). -/
theorem baSTKfargL_holds (d : ℕ) (hd : 3 ≤ d) : ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STKfargL (baFMz sz z) t :=
  fun κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow t ht0 htT => baEMn2ExpHK hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT

/-- **`CltRepg` at the BA tuple** (`H₀ = g₀ Ψ`, `g' = 0`, `E = BAflowEs`): `baFMz` represents `seqHflowBA g₀` of the law
`seqP (sz.withLam 0)` at `ztOf m_F E u`; `H₀` is Hermitian since `g₀` is real and `Ψ` is.  Every other clause is definitional. -/
theorem baCltRepg_holds {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) :
    CltRepg (baFMz sz z) (Sizes.seqP (sz.withLam 0))
      (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (fun _ => 0) (BAflowEs sz z) :=
  ⟨rfl, fun n => by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq, show star ((BAflowLam0 sz z n : ℝ) : ℂ) = ((BAflowLam0 sz z n : ℝ) : ℂ) from
      Complex.conj_ofReal _],
    fun n u ω => ⟨fun x y => rfl, fun k σ a => rfl⟩⟩

private theorem CltFlowBA_PsiB_inv (L : ℕ) [NeZero L] (T : Zd d L ≃ Zd d L)
    (hT : T = Equiv.neg _ ∨ ∃ c, T = Equiv.addRight c) (a b : Zd d L) : PsiB d L (T a) (T b) = PsiB d L a b := by
  have hA : Adj d L (T a) (T b) ↔ Adj d L a b := by
    rcases hT with rfl | ⟨c, rfl⟩
    · simp only [Adj, Equiv.neg_apply]
      rw [show -a - -b = -(a - b) by ring, zdistD_neg]
    · simp only [Adj, Equiv.coe_addRight]
      rw [add_sub_add_right_eq_sub]
  simp only [PsiB, Matrix.of_apply]
  by_cases h : Adj d L a b
  · simp [h, hA.2 h]
  · simp [h, mt hA.1 h]

/-- **`CltInvg` at the BA tuple**: `H₀ = g₀ Ψ` is invariant under the lift to the fine
lattice of the block translations and of the reflection, because `Ψ = Ψ^{(B)} ⊗ I` and `Adj` depends on `|a - b|_L` only. -/
theorem baCltInvg_holds {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) :
    CltInvg (sz := sz) (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) := by
  intro n T hT lift x y
  simp only [Matrix.smul_apply, smul_eq_mul]
  congr 1
  have hx : ∀ x, splitEquiv d (sz.L n) (sz.W n) (lift x) = ((T (splitEquiv d (sz.L n) (sz.W n) x).1, (splitEquiv d (sz.L n) (sz.W n) x).2)) := by
    intro x
    simp [lift, Prod.map]
  unfold PsiI PsiV
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, hx]
  rw [CltFlowBA_PsiB_inv (sz.L n) T hT]

end Rep

/-! ## 5. `STKpropsg`: invariance and size of `𝒦^{(2)}` -/

section Kprops

variable {d : ℕ}

/-- `BAKsol` solves `IsKLoopS` at every size index from `BAReal` alone (no `0 < g`): `baKcac_isKLoopS` is the witness (as the private
`SEforLnBA_Ksol_isKLoopS` in `BA/SEforLnBA`).  This is the source of the `∀ n` clauses at indices with `g₀ n ≤ 0`. -/
private theorem CltFlowBA_Ksol_isKLoopS {L W : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1)
      (BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m)) := by
  have hex : ∃ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K := ⟨_, baKcac_isKLoopS hr⟩
  simp only [BAKsol, hex, ↓reduceDIte]
  exact hex.choose_spec

/-- `(Kn2sol)` for `BAKsol` at every `g` (`BAReal` only): `baKsol_two` (`BA/KInduct`) without `0 < g`; `baK_unique` against the spliced
family `BAKcac` (`BAKcac_spliced` clause 2). -/
private theorem CltFlowBA_K_two {L W : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d L) :
    BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) =
      (((W : ℂ) ^ d)⁻¹) *
        (BATheta d L g E m t (σ 0) (σ 1) * BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) (a 1) := by
  have heq := baK_unique _ _ (CltFlowBA_Ksol_isKLoopS (W := W) hr) (baKcac_isKLoopS (W := W) hr) t ht
    (KLloopOf d L σ a) (by simp [LoopIdx.WF, KLloopOf]) (by simp [LoopIdx.length, KLloopOf])
  rw [heq]
  have hloop : KLloopOf d L σ a = ⟨[(σ 0, σ 1).1, (σ 0, σ 1).2], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [hloop]
  exact (BAKcac_spliced (d := d) (L := L) (W := W) (g := g) (E := E) (m := m)).2.1 t (σ 0) (σ 1) (a 0) (a 1)

variable {L : ℕ} [NeZero L]

private theorem CltFlowBA_MB_neg (g : ℝ) (z m : ℂ) (x y : Zd d L) :
    BAMB d L g z m (-x) (-y) = BAMB d L g z m x y := by
  have h := BAMB_shift d L g z m (-x) (-y) (x + y)
  rw [show -x + (x + y) = y by ring, show -y + (x + y) = x by ring] at h
  exact h.symm.trans (BAMB_symm d L g z m y x)

private theorem CltFlowBA_Msig_neg (g : ℝ) (z m : ℂ) (σ : Bool) (x y : Zd d L) :
    BAMsigma d L (BAMB d L g z m) σ (-x) (-y) = BAMsigma d L (BAMB d L g z m) σ x y := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, CltFlowBA_MB_neg]
  · simp only [BAMsigma, ite_true, CltFlowBA_MB_neg]

private theorem CltFlowBA_Mss_neg (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ (-a) (-b) = BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b := by
  simp only [BAMss, Matrix.of_apply, CltFlowBA_Msig_neg]

/-- `Θ_t(-a, -b) = Θ_t(a, b)`, every `(σ₁, σ₂)`, unconditional (as `baP8_BATheta_shift`, with `Equiv.neg`). -/
private theorem CltFlowBA_Theta_neg (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    BATheta d L g E m t σ₁ σ₂ (-a) (-b) = BATheta d L g E m t σ₁ σ₂ a b := by
  have hA : (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂).submatrix (Equiv.neg _) (Equiv.neg _)
      = 1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ := by
    ext x y
    have h1 : (-x = -y) ↔ (x = y) := neg_inj
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Equiv.neg_apply, h1, CltFlowBA_Mss_neg]
  have h2 := Matrix.inv_submatrix_equiv
    (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) (Equiv.neg _) (Equiv.neg _)
  rw [hA] at h2
  unfold BATheta PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 a) b
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

private theorem CltFlowBA_prod_neg (A B : Matrix (Zd d L) (Zd d L) ℂ) (hA : ∀ x y, A (-x) (-y) = A x y)
    (hB : ∀ x y, B (-x) (-y) = B x y) (x y : Zd d L) : (A * B) (-x) (-y) = (A * B) x y := by
  simp only [Matrix.mul_apply]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun c => ?_
  rw [Equiv.neg_apply, ← hA x (-c), ← hB (-c) y]
  simp

/-- Column `ℓ¹`-sum of `M^{(σ₁σ₂)}`: `Σ_c |M^{(σ₁σ₂)}_{cb}| = Σ_c |M^{(B)}_{cb}|² = 1` (Ward, `BAMB_row_sq_real`; symmetry of `M^{(B)}`). -/
private theorem CltFlowBA_Mss_col (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (σ₁ σ₂ : Bool) (b : Zd d L) :
    ∑ c, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ = 1 := by
  have hn : ∀ σ x y, ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y‖ = ‖BAMB d L g (E : ℂ) m x y‖ := by
    intro σ x y
    cases σ
    · simp [BAMsigma, Matrix.conjTranspose_apply, BAMB_symm d L g (E : ℂ) m y x]
    · simp [BAMsigma]
  have e : ∀ c, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ c b‖ = ‖BAMB d L g (E : ℂ) m b c‖ ^ 2 := by
    intro c
    simp only [BAMss, Matrix.of_apply, norm_mul, hn]
    rw [BAMB_symm d L g (E : ℂ) m c b]
    ring
  rw [Finset.sum_congr rfl fun c _ => e c]
  exact BAMB_row_sq_real d L g E m h b

end Kprops

section KpropsMain

variable {d : ℕ}

/-- **`STKpropsg` along every BA flow**.  Invariance, for every `n` and `t ∈ [0,1)`
(`BAReal` only, so also at indices with `g₀ n ≤ 0`): translation by `baK_translate` with `baKcac_isKLoopS` (`BAKsol` solves `IsKLoopS`
through the witness), reflection from `(Kn2sol)` (`CltFlowBA_K_two`) with `Θ(-a,-b) = Θ(a,b)` and `M^{(σσ')}(-a,-b) = M^{(σσ')}(a,b)`.
Size: `‖𝒦^{(2)}_s‖ = W^{-d} |(Θ M^{(σσ')})(a,b)| ≤ W^{-d} sup|Θ| ≤ c₁/(g² W^d)` with `c₁ = A C₅ (1 + 2^{d-1})`, `sup|Θ| ≤ c₁/g²`
from the decay of `STThPropsg` at `s` through `meanFar_T1` (regime `STReg5I`: `g²/L² ≤ 1 - s`) and the unit column sum `Σ_c |M^{(σσ')}_{cb}| = 1`. -/
theorem baSTKpropsg_holds (d : ℕ) (hd : 3 ≤ d) : ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STReg5I sz s t → STKpropsg (baFMz sz z) s := by
  intro κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow s t hs0 hst htT hreg
  refine ⟨fun n t' ht0 ht1 σ hσ a c => ?_, ?_⟩
  · have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    refine ⟨?_, ?_⟩
    · have hIs := CltFlowBA_Ksol_isKLoopS (W := sz.W n) hr
      have h := baK_translate _ _ (fun σ x y c => BAMsigma_shift d (sz.L n) _ _ _ σ x y c) hIs t' ⟨ht0, ht1⟩ c
        (KLloopOf d (sz.L n) σ a) (by simp [LoopIdx.WF, KLloopOf])
      have e : (⟨(KLloopOf d (sz.L n) σ a).σ, (KLloopOf d (sz.L n) σ a).a.map (· + c)⟩ : LoopIdx (Zd d (sz.L n))) =
          KLloopOf d (sz.L n) σ (fun i => a i + c) := by
        simp [KLloopOf]
      rw [e] at h
      exact h
    · have hK : ∀ b : Fin 2 → Zd d (sz.L n), (baFMz sz z).K n t' σ b = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
          (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t' (σ 0) (σ 1) *
            BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n))
              (σ 0) (σ 1)) (b 0) (b 1) := fun b => CltFlowBA_K_two hr ⟨ht0, ht1⟩ σ b
      rw [hK, hK]
      congr 1
      exact CltFlowBA_prod_neg _ _
        (fun x y => CltFlowBA_Theta_neg _ _ _ _ _ _ x y) (fun x y => CltFlowBA_Mss_neg _ _ _ _ _ x y) (a 0) (a 1)
  · obtain ⟨C5, c5, C6, C7, hC5, hc5, -, -, H⟩ := baSTThPropsg_holds d hd κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow
    refine ⟨C5 * (1 + 2 ^ (d - 1)), by positivity, ?_⟩
    filter_upwards [H, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hH hwin σ hσ a b
    obtain ⟨hg0, hgΛ⟩ := hwin
    obtain ⟨hlam, -, -⟩ := CltFlowBA_cmp hκ hflow n hg0
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have hs1 : s n < 1 := (lt_of_lt_of_le (hst n) (htT n)).trans (EMn2BA_T0_lt_one hκ sz hflow n)
    have hreg1 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s n :=
      (hreg n).1.trans (by linarith [hst n])
    obtain ⟨hshift, -, hdec, -, -⟩ := hH (s n) (hs0 n) hs1 σ hσ
    have hT1 : ∀ x, ‖STThg (baFMz sz z) n (σ 0) (σ 1) (s n) 0 x‖ ≤
        (C5 * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) := fun x =>
      meanFar_T1 hd (sz.three_le_L n) hlam hs1 hreg1 hC5.le hc5
        (fun x => STThg (baFMz sz z) n (σ 0) (σ 1) (s n) 0 x) hdec x
    have hTs : ∀ x, ‖STThg (baFMz sz z) n (σ 0) (σ 1) (s n) 0 x‖ ≤ C5 * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 := fun x =>
      (hT1 x).trans (div_le_self (by positivity) (one_le_pow₀ (by
        have : (0 : ℝ) ≤ ((zdistInf d (sz.L n) x : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith)))
    have hΘ : ∀ x y, ‖BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (s n) (σ 0) (σ 1) x y‖ ≤ C5 * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 := fun x y => by
      have e := congrFun (congrFun (CltFlowBA_STThg hκ hflow n (σ 0) (σ 1) (s n)) x) y
      rw [← e, hshift x y]
      exact hTs _
    have hcol := CltFlowBA_Mss_col (d := d) (L := sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hr.1 (σ 0) (σ 1) b
    have hK : (baFMz sz z).K n (s n) σ ![a, b] = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
        (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (s n) (σ 0) (σ 1) *
          BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n))
            (σ 0) (σ 1)) a b := by
      have := CltFlowBA_K_two (W := sz.W n) hr ⟨hs0 n, hs1⟩ σ ![a, b]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      exact this
    have hprod : ‖(BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (s n) (σ 0) (σ 1) *
          BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n))
            (σ 0) (σ 1)) a b‖ ≤ C5 * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 := by
      rw [Matrix.mul_apply]
      calc _ ≤ ∑ c, ‖BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
            (s n) (σ 0) (σ 1) a c * BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
              (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1) c b‖ := norm_sum_le _ _
        _ ≤ ∑ c, C5 * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 * ‖BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
              (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1) c b‖ :=
            Finset.sum_le_sum fun c _ => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right (hΘ a c) (norm_nonneg _)
        _ = C5 * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 := by rw [← Finset.mul_sum, hcol, mul_one]
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by have := sz.W_pos n; positivity
    rw [hK, norm_mul]
    have e1 : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by simp
    rw [e1]
    refine (mul_le_mul_of_nonneg_left hprod (inv_nonneg.2 hW.le)).trans (le_of_eq ?_)
    change (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C5 * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2) =
      C5 * (1 + 2 ^ (d - 1)) / (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)
    have : sz.lam n ^ 2 ≠ 0 := by positivity
    field_simp

end KpropsMain

/-! ## 6. The class `IniTermGen_CltFlow` at the BA tuple -/

section Class

variable {d : ℕ}

/-- `N^{-1+ε/2} ≤ 1 - t₀_n` eventually: `1 - t₀ ≥ Im z/2 ≥ N^{-1+ε}/2` (`EMn2BA_one_sub_T0`, `BAdom`) and `N^{ε/2} ≥ 2`. -/
private theorem CltFlowBA_one_sub_T0 {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {sz : Sizes d} {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ 1 - BAflowT0 sz z n := by
  filter_upwards [ST_size_pow_big sz (tendsto_size sz hflow.1.2.2.1) (a := ε / 2) (M := 2) (half_pos hε)] with n hn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    have := sz.one_le_size n
    exact_mod_cast (by omega : 0 < sz.size n)
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) =
      ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) * ((sz.size n : ℕ) : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have h3 := EMn2BA_one_sub_T0 hκ sz hflow n
  have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) := Real.rpow_pos_of_pos hN0 _
  nlinarith [mul_le_mul_of_nonneg_left hn hp.le]

/-- **`baIniTermGen_cltFlow`**: the class `IniTermGen_CltFlow`
at `(fun sz => seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, every `d` (the class carries its own `3 ≤ d`).  `κ' = min κ 1`, `δ = ε/2`
before `(𝔠, sz, z)`; along a flow: `H₀ = g₀ Ψ`, `g' = 0`, `E = BAflowEs`; `κ' ≤ Im m_F` (`EMn2BA_mF_data`); `N^{-1+δ} ≤ 1 - T₀`;
`CltRepg` (`baCltRepg_holds`); the Ward row `Σ_y |M_xy|² = 1` (`CltFlowBA_Mfine_row`); `STThPropsg`; `STExpInvgL` through
`stExpInvgL_of_rep` (`baCltRepg_holds`, `baCltInvg_holds`); and, per `(s, t)` under `STReg5I`: `STMfarg`, `STGijDecgL`
(`baSTGijDecgL_holds`), `STKfargL`, `STKpropsg`. -/
theorem baIniTermGen_cltFlow (d : ℕ) : IniTermGen_CltFlow d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨min κ 1, ε / 2, lt_min hκ one_pos, min_le_right _ _, half_pos hε, ?_⟩
  intro 𝔠 sz z hflow
  refine ⟨fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n), fun _ => 0, BAflowEs sz z,
    fun n => (min_le_left κ 1).trans (EMn2BA_mF_data sz hflow n).1, CltFlowBA_one_sub_T0 hκ hε hflow,
    baCltRepg_holds sz z, fun n x => ?_, baSTThPropsg_holds d hd κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow,
    stExpInvgL_of_rep (baCltRepg_holds sz z) (baCltInvg_holds sz z), ?_⟩
  · exact (CltFlowBA_Mfine_row sz (BAflowLam0 sz z) (BAflowEs sz z) n
      (lt_of_lt_of_le hκ (EMn2BA_mF_data sz hflow n).1) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1 x).le
  · intro s t hs0 hst htl hreg
    exact ⟨baSTMfarg_holds d hd κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow s,
      baSTGijDecgL_holds d (by omega) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s hs0 (fun n => (hst n).le.trans (htl n)),
      baSTKfargL_holds d hd κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow s hs0 (fun n => (hst n).le.trans (htl n)),
      baSTKpropsg_holds d hd κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow s t hs0 hst htl hreg⟩

end Class

end RBM.BA
