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

section PerCarrier

/-- **Target 7, `baWardTypePgL_of`** (conclusion head `STWardTypePgL`; paper `(eq:Ward_typeP)` `3_5:1264`): `stWardTypePgL_of` at the BA carrier
`baFMz sz z` and the law `seqP (sz.withLam 0)`.  The carrier facts are `baB45Gen_facts` (with `baZeroModeGen_wardCls`), the far decay of `𝒦` is
`baKcalDecay_holds`, the flow data are `EMn2BA_mF_data`; only the Step 2 decay `STGdecayWgL` (T1-BA), the times and the eventual
`N⁻¹ ≤ 1 - t_n` stay hypotheses. -/
theorem baWardTypePgL_of (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (κ ε 𝔠 𝔡 Cd : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ)
    (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n)
    (hD : STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) :
    STWardTypePgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t := by
  obtain ⟨C₆, -, G⟩ := baB45Gen_facts d κ hκ
  obtain ⟨hward, hpair, him1, hker, hsums⟩ := G sz ε 𝔠 𝔡 z hflow
  exact stWardTypePgL_of hd sz (baFMz sz z) (Sizes.seqP (sz.withLam 0))
    ⟨hκ, fun n => (EMn2BA_mF_data sz hflow n).1, fun n t => rfl⟩ him1 hflow.1 hward hpair hker
    (fun n σ σ' t h0 h1 a => (hsums n σ σ' t h0 h1).1 a) (fun n σ σ' t h0 h1 b => (hsums n σ σ' t h0 h1).2 b)
    (baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow) hs ht1 hNt hD

/-- **Target 7, `baB45gL_of`** (conclusion head `STB45gL`; paper `(y27kasdfg)` `3_5:1692`): `stB45gL_of` at the BA carrier, the hypotheses of
`baWardTypePgL_of`. -/
theorem baB45gL_of (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (κ ε 𝔠 𝔡 Cd : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ)
    (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n)
    (hD : STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) :
    STB45gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t := by
  obtain ⟨C₆, -, G⟩ := baB45Gen_facts d κ hκ
  obtain ⟨hward, hpair, him1, hker, hsums⟩ := G sz ε 𝔠 𝔡 z hflow
  exact stB45gL_of hd sz (baFMz sz z) (Sizes.seqP (sz.withLam 0))
    ⟨hκ, fun n => (EMn2BA_mF_data sz hflow n).1, fun n t => rfl⟩ him1 hflow.1 hward hpair hker
    (fun n σ σ' t h0 h1 a => (hsums n σ σ' t h0 h1).1 a) (fun n σ σ' t h0 h1 b => (hsums n σ σ' t h0 h1).2 b)
    (baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow) hs ht1 hNt hD

end PerCarrier

/-! ## 5. Target 8: the two ingredient pins at the BA tuple -/

section Pins

/-- **Target 8, `BAWardTypePPin`** (`T2486_BAWardTypePPin`; `(eq:Ward_typeP)` as an ingredient pin at the BA tuple), for every regime `R`. -/
def BAWardTypePPin (d : ℕ) : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STWardTypePPingL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- **Target 8, `BAB45Pin`** (`T2486_BAB45Pin`; `(y27kasdfg)` as an ingredient pin at the BA tuple), for every regime `R`. -/
def BAB45Pin (d : ℕ) : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STB45PingL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- **`BAWardTypePPin` is proved, unconditionally**: `stWardTypePPingL_of` with `baStep5CasesGen_flowFacts`, `baB45Gen_facts` and
`baKcalDecay_holds`.  For `d < 3` the setting `STIngRgL` has the premise `3 ≤ d`, so the pin is vacuous there. -/
theorem baWardTypePPin_holds (d : ℕ) : BAWardTypePPin d := fun R => by
  by_cases hd : 3 ≤ d
  · exact stWardTypePPingL_of d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
      (baStep5CasesGen_flowFacts d) (baB45Gen_facts d)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow)
  · intro h
    exact absurd h hd

/-- **`BAB45Pin` is proved, unconditionally** (as `baWardTypePPin_holds`, with `stB45PingL_of`). -/
theorem baB45Pin_holds (d : ℕ) : BAB45Pin d := fun R => by
  by_cases hd : 3 ≤ d
  · exact stB45PingL_of d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
      (baStep5CasesGen_flowFacts d) (baB45Gen_facts d)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow)
  · intro h
    exact absurd h hd

end Pins

/-! ## 6. Compiled nonempty instances (targets 6-8)

`d = 3`, the preflight sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the spectral parameters `zSeq` with
`flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`), the windows `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` (`t0_sz0`,
`BA/FlowPins.lean:1227`), `C_d = 1`.  Every deterministic premise is discharged; the inputs that stay hypotheses are other gates' pins:
the Step 2 conclusions `STStep2ConclgL` / the decay `STGdecayWgL` (T1-BA) and `STLKgL` (the stage-L pin, consumed by the generic pins). -/

namespace B45BAInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- `N⁻¹ ≤ 1/3` at every size index of `sz0` (`N = (W L)^3 ≥ 3`). -/
private theorem B45BAInst_inv_size (n : ℕ) : (((sz0.size n : ℕ) : ℝ))⁻¹ ≤ 1 - 2 / 3 := by
  have h3 : 3 ≤ sz0.W n * sz0.L n := le_trans (sz0.three_le_L n) (Nat.le_mul_of_pos_left _ (sz0.W_pos n))
  have h2 : 3 ≤ sz0.size n :=
    h3.trans (Nat.le_self_pow (by norm_num) _)
  have h2' : ((3 : ℕ) : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast h2
  calc (((sz0.size n : ℕ) : ℝ))⁻¹ ≤ ((3 : ℕ) : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2'
    _ = 1 - 2 / 3 := by norm_num

/-- **Target 6** at the data: `KerSums` of `baFMz sz0 zSeq` at every size index. -/
theorem inst_kerSums (n : ℕ) : ZeroModeGen_KerSums (baFMz sz0 zSeq) n :=
  baZeroModeGen_kerSums 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 n

/-- **Target 6** at the data, `C₆ = 1`: the row sums of `‖thetaKer‖` at `n = 0`, `σ = (+,-)`, `a = 0`, `t = 1/2` are at most `2`. -/
example : ∑ b, ‖Step2Gen_thetaKer (baFMz sz0 zSeq) 0 true false (1 / 2) 0 b‖ ≤ 1 / (1 - 1 / 2) :=
  B45BA_row_thetaKer sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (1 / 2) (by norm_num) 0
    (BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0) true false (by norm_num) (by norm_num) 0

/-- **Target 6** at the data, `C₆ = 1`: the column sums of `thetaKer` at `n = 0`, `σ = (-,-)` (an equal pair), `b = 0`, `t = 1/2`. -/
example : ‖∑ a, Step2Gen_thetaKer (baFMz sz0 zSeq) 0 false false (1 / 2) a 0‖ ≤ 1 / (1 - 1 / 2) :=
  B45BA_col_thetaKer sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (1 / 2) (by norm_num) 0
    (BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0) false false (by norm_num) (by norm_num) 0

/-- **Target 6, `baB45Gen_facts`** at the data: some `C₆ > 0` with the Ward class, the Ward pair, `Im m ≤ 1`, `KerSums` and the sums of
`thetaKer` for `sz0`, `zSeq`. -/
theorem inst_b45Facts : ∃ C₆ : ℝ, 0 < C₆ ∧ ZeroModeGen_WardCls sz0 (baFMz sz0 zSeq) ∧ DecayGen_WardPair (baFMz sz0 zSeq) ∧
    (∀ n : ℕ, ((baFMz sz0 zSeq).m n).im ≤ 1) ∧ (∀ n : ℕ, ZeroModeGen_KerSums (baFMz sz0 zSeq) n) ∧
    ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 →
      (∀ a : Zd 3 (sz0.L n), ∑ b : Zd 3 (sz0.L n), ‖Step2Gen_thetaKer (baFMz sz0 zSeq) n σ σ' t a b‖ ≤ C₆ / (1 - t)) ∧
      ∀ b : Zd 3 (sz0.L n), ‖∑ a : Zd 3 (sz0.L n), Step2Gen_thetaKer (baFMz sz0 zSeq) n σ σ' t a b‖ ≤ C₆ / (1 - t) := by
  obtain ⟨C₆, hC₆, H⟩ := baB45Gen_facts 3 (1 / 2) (by norm_num)
  exact ⟨C₆, hC₆, H sz0 (1 / 10) (1 / 6) (1 / 10) zSeq flow_sz0⟩

/-- **Target 7, `baWardTypePgL_of`** at the data (`s ≡ 1/2 < t ≡ 2/3`, `C_d = 1`): only `STGdecayWgL` (T1-BA's pin) stays a hypothesis;
`N⁻¹ ≤ 1 - t_n = 1/3` holds for every `n` (`B45BAInst_inv_size`). -/
theorem inst_wardTypePgL
    (hD : STGdecayWgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) 1) :
    STWardTypePgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) :=
  baWardTypePgL_of 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) 1 zSeq (fun _ => 1 / 2) (fun _ => 2 / 3) (by norm_num)
    flow_sz0 (fun _ => by norm_num) (fun _ => by norm_num) (Filter.Eventually.of_forall fun n => B45BAInst_inv_size n)
    hD

/-- **Target 7, `baB45gL_of`** at the data (same window and hypothesis). -/
theorem inst_b45gL
    (hD : STGdecayWgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) 1) :
    STB45gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) :=
  baB45gL_of 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) 1 zSeq (fun _ => 1 / 2) (fun _ => 2 / 3) (by norm_num)
    flow_sz0 (fun _ => by norm_num) (fun _ => by norm_num) (Filter.Eventually.of_forall fun n => B45BAInst_inv_size n)
    hD

/-- **Target 8, `BAWardTypePPin`** at `d = 3`, the trivial regime `STAny`: unconditional. -/
theorem inst_baWardTypePPin : STWardTypePPingL 3 STAny (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  baWardTypePPin_holds 3 STAny

/-- **Target 8, `BAB45Pin`** at `d = 3`, the trivial regime `STAny`: unconditional. -/
theorem inst_baB45Pin : STB45PingL 3 STAny (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  baB45Pin_holds 3 STAny

/-- **Target 8, `BAWardTypePPin` applied** at the data: `κ = 1/2`, `ε = 𝔡 = 1/10`, `C_d = 1`, `𝔠 = 1/6`, `sz0`, `zSeq`, `s ≡ 1/2 < t ≡ 2/3 ≤ T0`;
`STKboundgL`, `STKwardgL` are `baKbound_holds`, `baKward_holds`, `STConStInd` is `s1Setup_conStInd_const`; only `STLKgL` and
`STStep2ConclgL` (other gates' pins) stay hypotheses. -/
theorem inst_wardTypePPin_applied
    (hLK : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2))
    (hStep2 : STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) 1) :
    STWardTypePgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) := by
  obtain ⟨𝔠d, h𝔠d, -, H⟩ := baWardTypePPin_holds 3 STAny le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos
  exact H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun n => t0_sz0 n) trivial
    (baKbound_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0)
    (baKward_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0)
    hLK (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠d) hStep2

/-- **Target 8, `BAB45Pin` applied** at the same data. -/
theorem inst_b45Pin_applied
    (hLK : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2))
    (hStep2 : STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) 1) :
    STB45gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) := by
  obtain ⟨𝔠d, h𝔠d, -, H⟩ := baB45Pin_holds 3 STAny le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos
  exact H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun n => t0_sz0 n) trivial
    (baKbound_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0)
    (baKward_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0)
    hLK (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠d) hStep2

end B45BAInst




end RBM.BA

end
