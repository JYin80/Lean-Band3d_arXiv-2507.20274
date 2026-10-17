/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.B45Gen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.SEforLnBA
import RBM3D.BA.KKernel
import RBM3D.BA.KBase
import RBM3D.BA.Ward

/-!
# Ticket T2486, targets 6-8: `(eq:Ward_typeP)` and `(y27kasdfg)` at the block Anderson carrier (U2-BA, part (b))

The BA readings of the merged generic results of `Chain/B45Gen.lean` (U2b) at the BA tuple
`(law, Flow, mk, T0) = (seqP ∘ withLam 0, BAFlow, baFMz, BAflowT0)`.  No merged file is edited.

* **Target 6** `baZeroModeGen_kerSums`: `ZeroModeGen_KerSums (baFMz sz z) n` at every size index.  `S = 1`, so `Step2Kern_Mss * S` is
  `BAMss` of `M^{(B)} = BAMB` (`Step2Kern_Mss_BA`), a translation invariant (`BAMB_shift`) and symmetric (`BAMB_symm`) matrix for all four
  charge pairs; such a matrix has equal constant row and column sums.  `baB45Gen_facts`: `B45Gen_Facts` at the BA family with `C₆ = 1`:
  the Ward class (`baZeroModeGen_wardCls`), the Ward pair (`DecayGenTw_baWardPair`), `Im m ≤ 1`, `KerSums`, and the row and column sums of
  `thetaKer = Θ_BA M^{(σσ')}` (`Step2Kern_thetaKer_BA`): with `Q = M^{(σσ')}`, `|Q_ab| = BAK_ab` has unit row sums, so `‖Q‖_{∞→∞} ≤ 1`,
  `Y = ΘQ` solves `Y = Q + t Q Y` (`BATheta_resolvent`) and `‖Y‖ ≤ (1-t)⁻¹`; the column sums are `c (1 - t c)⁻¹` with `|c| ≤ 1`.
  Every step reads `BAReal` only (no `0 < g₀`).
* **Target 7** `baWardTypePgL_of`, `baB45gL_of`: `stWardTypePgL_of`, `stB45gL_of` at `baFMz`, with targets 1 and 6 and the Ward class.
  Only `STGdecayWgL` (T1-BA), the times and `N⁻¹ ≤ 1 - t_n` (eventually) stay hypotheses.
* **Target 8** `BAWardTypePPin`, `BAB45Pin` and `baWardTypePPin_holds`, `baB45Pin_holds` (every regime `R`): unconditional.  The generic
  pins `stWardTypePPingL_of`, `stB45PingL_of` take `STKcalDecaygL` along the flow, which `baKcalDecay_holds` gives for `3 ≤ d`; for `d < 3`
  the setting `STIngRgL` has the premise `3 ≤ d` itself, so the pin is vacuous there.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 6: the kernel sums -/

section KerSums

variable {d : ℕ}

/-- A translation invariant and symmetric matrix on `Z_L^d` has the same constant row and column sums. -/
private theorem B45BA_sums_of_shift_symm {L : ℕ} [NeZero L] (X : Matrix (Zd d L) (Zd d L) ℂ)
    (hs : ∀ a b r : Zd d L, X (a + r) (b + r) = X a b) (hT : ∀ a b : Zd d L, X a b = X b a) :
    ∃ c : ℂ, (∀ a : Zd d L, ∑ b, X a b = c) ∧ ∀ b : Zd d L, ∑ a, X a b = c := by
  have hrow : ∀ a : Zd d L, ∑ b, X a b = ∑ b, X 0 b := fun a =>
    (Fintype.sum_equiv (Equiv.addRight a) (fun b => X 0 b) (fun b => X a b) fun b => by
      simpa using (hs 0 b a).symm).symm
  refine ⟨∑ b, X 0 b, hrow, fun b => ?_⟩
  rw [← hrow b]
  exact Finset.sum_congr rfl fun a _ => hT a b

/-- `M(σ)` is symmetric. -/
private theorem B45BA_Msigma_symm (L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b = BAMsigma d L (BAMB d L g (E : ℂ) m) σ b a := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply,
      BAMB_symm d L g (E : ℂ) m a b]
  · exact BAMB_symm d L g (E : ℂ) m a b

/-- `M(σ)` is translation invariant. -/
private theorem B45BA_Msigma_shift (L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (σ : Bool) (a b r : Zd d L) :
    BAMsigma d L (BAMB d L g (E : ℂ) m) σ (a + r) (b + r) = BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, BAMB_shift d L g (E : ℂ) m b a r]
  · exact BAMB_shift d L g (E : ℂ) m a b r

/-- `M^{(σσ')}` is translation invariant. -/
private theorem B45BA_Mss_shift (L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (σ σ' : Bool) (a b r : Zd d L) :
    BAMss d L (BAMB d L g (E : ℂ) m) σ σ' (a + r) (b + r) = BAMss d L (BAMB d L g (E : ℂ) m) σ σ' a b := by
  simp only [BAMss, Matrix.of_apply, B45BA_Msigma_shift]

/-- `M^{(σσ')}` is symmetric. -/
private theorem B45BA_Mss_symm (L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (σ σ' : Bool) (a b : Zd d L) :
    BAMss d L (BAMB d L g (E : ℂ) m) σ σ' a b = BAMss d L (BAMB d L g (E : ℂ) m) σ σ' b a := by
  simp only [BAMss, Matrix.of_apply]
  rw [B45BA_Msigma_symm L g E m σ b a, B45BA_Msigma_symm L g E m σ' a b]

/-- The derived block kernel times `S = 1` at the BA carrier is `M^{(σσ')}` of `M^{(B)}`, along the flow of `BAReal` data. -/
private theorem B45BA_X_eq (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ) (n : ℕ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (σ σ' : Bool) :
    Step2Kern_Mss (baFM sz lam0 E) n σ σ' * (baFM sz lam0 E).S n =
      BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ' := by
  have hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by
    simpa using (lt_of_lt_of_le hκ hr.2).ne'
  rw [Step2Kern_Mss_BA sz lam0 E n hIm σ σ']
  change _ * (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) = _
  rw [mul_one]

/-- **Target 6, `KerSums` at the BA carrier of one size index**: constant, equal row and column sums of `M^{(σσ')}`, all four charge pairs. -/
private theorem B45BA_kerSums_at (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ) (n : ℕ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) : ZeroModeGen_KerSums (baFM sz lam0 E) n := by
  intro σ σ'
  simp only [B45BA_X_eq sz lam0 E κ hκ n hr σ σ']
  exact B45BA_sums_of_shift_symm _ (fun a b r => B45BA_Mss_shift _ _ _ _ σ σ' a b r)
    (fun a b => B45BA_Mss_symm _ _ _ _ σ σ' a b)

/-- **Target 6, `baZeroModeGen_kerSums`** (`T2486_BAKerSums`; DECISIONS §286 (2)): `ZeroModeGen_KerSums (baFMz sz z) n` at every size
index, along every BA flow.  `S = 1`; `Step2Kern_Mss * S = BAMss` (`Step2Kern_Mss_BA`) is translation invariant and symmetric for the four
charge pairs (`BAMB_shift`, `BAMB_symm`), hence has equal constant row and column sums.  The mixed pairs are `BAK` with sums `1`
(`BAMss_pm_eq`, `BAK_row_sum`); this route covers the equal pairs by the same two lemmas. -/
theorem baZeroModeGen_kerSums (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ n : ℕ, ZeroModeGen_KerSums (baFMz sz z) n :=
  fun sz κ ε 𝔠 𝔡 z hκ hflow n =>
    B45BA_kerSums_at sz (BAflowLam0 sz z) (BAflowEs sz z) κ hκ n (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)

end KerSums

/-! ## 2. Target 6: the row and column sums of `thetaKer` -/

section ThetaSums

open scoped Matrix.Norms.Operator

variable {d : ℕ}

/-- `‖M^{(σσ')}‖_{∞→∞} ≤ 1`: `|M^{(σσ')}_{ab}| = BAK_{ab}` has unit row sums (`BAMss_norm_eq_BAK`, `BAK_row_sum`). -/
private theorem B45BA_Mss_norm_le (L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (σ σ' : Bool) :
    ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ'‖ ≤ 1 := by
  have h : ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ'‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa [BAMss_norm_eq_BAK] using (BAK_row_sum d L g E m hr.1 a).le
  exact_mod_cast h

/-- `Y = Θ Q` with `Θ = 1 + t Q Θ`, `‖Q‖_{∞→∞} ≤ 1`, `0 ≤ t < 1`: `Y = Q + t Q Y`, so `‖Y‖ ≤ 1 + t ‖Y‖`, i.e. `‖Y‖ ≤ (1-t)⁻¹`. -/
private theorem B45BA_norm_ThQ_le {L : ℕ} [NeZero L] (Q Θ : Matrix (Zd d L) (Zd d L) ℂ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hQ : ‖Q‖ ≤ 1) (hres : Θ = 1 + (t : ℂ) • (Q * Θ)) : ‖Θ * Q‖ ≤ (1 - t)⁻¹ := by
  have hpos : 0 < 1 - t := by linarith
  have hY : Θ * Q = Q + (t : ℂ) • (Q * (Θ * Q)) := by
    calc Θ * Q = (1 + (t : ℂ) • (Q * Θ)) * Q := by rw [← hres]
      _ = Q + (t : ℂ) • (Q * (Θ * Q)) := by rw [add_mul, one_mul, smul_mul_assoc, mul_assoc]
  have hmul : ‖Q * (Θ * Q)‖ ≤ ‖Θ * Q‖ :=
    (Matrix.linfty_opNorm_mul Q (Θ * Q)).trans (by nlinarith [norm_nonneg (Θ * Q)])
  have h1 : ‖Θ * Q‖ ≤ 1 + t * ‖Θ * Q‖ := by
    calc ‖Θ * Q‖ = ‖Q + (t : ℂ) • (Q * (Θ * Q))‖ := by rw [← hY]
      _ ≤ ‖Q‖ + ‖(t : ℂ) • (Q * (Θ * Q))‖ := norm_add_le _ _
      _ ≤ 1 + t * ‖Θ * Q‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht0]
        nlinarith [mul_le_mul_of_nonneg_left hmul ht0]
  rw [← one_div, le_div_iff₀ hpos]
  nlinarith

/-- **Row sums of `thetaKer` at the BA carrier**: `Σ_b ‖thetaKer_{ab}‖ ≤ (1-t)⁻¹`, all four charge pairs. -/
private theorem B45BA_row_thetaKer (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ) (n : ℕ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (σ σ' : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Zd d (sz.L n)) : ∑ b, ‖Step2Gen_thetaKer (baFM sz lam0 E) n σ σ' t a b‖ ≤ 1 / (1 - t) := by
  have hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by
    simpa using (lt_of_lt_of_le hκ hr.2).ne'
  rw [Step2Kern_thetaKer_BA sz lam0 E n hIm σ σ' t]
  exact (sum_norm_row_le _ a).trans (by
    rw [one_div]
    exact B45BA_norm_ThQ_le _ _ ht0 ht1 (B45BA_Mss_norm_le _ _ κ _ _ hr σ σ')
      (BATheta_resolvent d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) hr t ht0 ht1 σ σ').1)

/-- `‖c (1 - t c)⁻¹‖ ≤ (1-t)⁻¹` for `‖c‖ ≤ 1`, `0 ≤ t < 1`. -/
private theorem B45BA_norm_colsum_le {c : ℂ} (hc : ‖c‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖c * (1 - (t : ℂ) * c)⁻¹‖ ≤ 1 / (1 - t) := by
  have hpos : 0 < 1 - t := by linarith
  have htc : ‖(t : ℂ) * c‖ ≤ t := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    nlinarith [norm_nonneg c]
  have h1 : 1 - t ≤ ‖1 - (t : ℂ) * c‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * c)
    rw [norm_one] at this
    linarith
  rw [norm_mul, norm_inv, ← one_mul (1 / (1 - t)), one_div]
  exact mul_le_mul hc (inv_anti₀ hpos h1) (inv_nonneg.2 (norm_nonneg _)) zero_le_one

/-- **Column sums of `thetaKer` at the BA carrier**: `‖Σ_a thetaKer_{ab}‖ ≤ (1-t)⁻¹`, all four charge pairs
(`QopAlgebra_col_sum_thetaKerg`: the sum is `c (1 - t c)⁻¹`, `c` the constant sum of `M^{(σσ')}`, `|c| ≤ Σ_b BAK_{ab} = 1`). -/
private theorem B45BA_col_thetaKer (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ) (n : ℕ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (σ σ' : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (b : Zd d (sz.L n)) : ‖∑ a, Step2Gen_thetaKer (baFM sz lam0 E) n σ σ' t a b‖ ≤ 1 / (1 - t) := by
  obtain ⟨c, hrow, hcol⟩ := B45BA_kerSums_at sz lam0 E κ hκ n hr σ σ'
  have hu : IsUnit (1 - (t : ℂ) • (Step2Kern_Mss (baFM sz lam0 E) n σ σ' * (baFM sz lam0 E).S n)) := by
    rw [B45BA_X_eq sz lam0 E κ hκ n hr σ σ']
    exact BATheta_isUnit d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) hr t ht0 ht1 σ σ'
  rw [QopAlgebra_col_sum_thetaKerg (baFM sz lam0 E) n σ σ' t c hcol hu b]
  refine B45BA_norm_colsum_le ?_ ht0 ht1
  rw [← hrow 0, B45BA_X_eq sz lam0 E κ hκ n hr σ σ']
  refine (norm_sum_le _ _).trans ?_
  simp only [BAMss_norm_eq_BAK]
  exact (BAK_row_sum d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) hr.1 0).le

end ThetaSums

/-! ## 3. Target 6: `B45Gen_Facts` at the BA family -/

section Facts

/-- **Target 6, `baB45Gen_facts`** (`T2486_BAB45Facts`; `C₆ = 1`): `B45Gen_Facts` at the BA family `(BAFlow, baFMz)`, every `d`.  The Ward class is
`baZeroModeGen_wardCls` (target 2 (a)), the Ward pair `DecayGenTw_baWardPair`, `Im m ≤ 1` is `EMn2BA_mF_data`, `KerSums` is
`baZeroModeGen_kerSums`, and the sums of `thetaKer = Θ_BA M^{(σσ')}` are `B45BA_row_thetaKer`, `B45BA_col_thetaKer`. -/
theorem baB45Gen_facts (d : ℕ) :
    B45Gen_Facts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) := by
  intro κ hκ
  refine ⟨1, one_pos, ?_⟩
  intro sz ε 𝔠 𝔡 z hflow
  refine ⟨baZeroModeGen_wardCls d sz κ ε 𝔠 𝔡 z hκ hflow, DecayGenTw_baWardPair sz _ _,
    fun n => (EMn2BA_mF_data sz hflow n).2, baZeroModeGen_kerSums d sz κ ε 𝔠 𝔡 z hκ hflow,
    fun n σ σ' t ht0 ht1 => ⟨fun a => ?_, fun b => ?_⟩⟩
  · exact B45BA_row_thetaKer sz (BAflowLam0 sz z) (BAflowEs sz z) κ hκ n (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) σ σ' ht0 ht1 a
  · exact B45BA_col_thetaKer sz (BAflowLam0 sz z) (BAflowEs sz z) κ hκ n (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) σ σ' ht0 ht1 b

end Facts

/-! ## 4. Target 7: `(eq:Ward_typeP)` and `(y27kasdfg)` per carrier -/

/-! ## 5. Target 8: the two ingredient pins at the BA tuple -/

/-! ## 6. Compiled nonempty instances (targets 6-8)

`d = 3`, the preflight sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the spectral parameters `zSeq` with
`flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`), the windows `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` (`t0_sz0`,
`BA/FlowPins.lean:1227`), `C_d = 1`.  Every deterministic premise is discharged; the inputs that stay hypotheses are other gates' pins:
the Step 2 conclusions `STStep2ConclgL` / the decay `STGdecayWgL` (T1-BA) and `STLKgL` (the stage-L pin, consumed by the generic pins). -/

end RBM.BA

end
