/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridGoodGen
import RBM3D.Chain.GridAssemblyGen
import RBM3D.Induction.AzumaProxyN2

/-!
# The Azuma proxies and the `Y` moments over the carrier

Generic forms of `Induction/AzumaProxyN` and `Induction/AzumaProxyN2` over a carrier
`Cm : Step2Mat sz`, namespace `RBM.BA`.  The hypotheses `AzumaSubGNg` and `AssembledNg` are in
`Chain/GridAssemblyGen`; the per-step vocabulary and the classes `StepDecompGen_LoopForm`,
`StepDecompGen_WalkForm`, `QVPropagatedNg` are in `Chain/StepDecompGen`.

* `azumaSubGNg`: the band `azumaSubGN` at the walk `sz.withLam lam'` with the test family shifted by
  the Hermitian `Ψ n` (the carrier walk is `Ψ n + pathH (sz.withLam lam')`,
  `StepDecompGen_WalkForm`).
* `azumaProxy_subG_ugeng`: the composition, with the identity `AzumaProxyGen_qvForm_eq`.
* The weighted `Y` fields `AzumaProxyN_YfieldsWg`, the uniform `Y` moments `YMomentsUnifNg` and
  `yMomentsUnifNg`, and the public forms `AzumaProxyN_eta_inv_le_pubg`, `AzumaProxyN_rowsum_UN_pubg`
  of the numerical helpers.

Private band helpers that mention no band object are reused by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private azumaProxy2_condExp_incr azumaProxy2_measurable_normX azumaProxy2_moments_of_dom
  azumaProxy2_condExp_stopped_reim azumaProxy2_gridStep_nonneg azumaProxy2_gridTime_nonneg azumaProxy2_gridTime_le
  from RBM3D.Induction.AzumaProxyN2
open private GridAssemblyGen_row_le from RBM3D.Chain.GridAssemblyGen

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Matrix.Norms.L2Operator

noncomputable section

namespace RBM.BA

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. `azumaSubGNg` -/

section Azuma

variable {d : ℕ} {sz : Sizes d}

/-- Translation of the directional derivative by a fixed matrix. -/
private theorem AzumaProxyGen_dirDerivN_shift {L W : ℕ} [NeZero L] [NeZero W]
    (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (Ψ M X : Matrix (Idx d L W) (Idx d L W) ℂ) :
    RBM.Ind.dirDerivN (fun H => Φ (Ψ + H)) M X = RBM.Ind.dirDerivN Φ (Ψ + M) X := by
  unfold RBM.Ind.dirDerivN
  simp only [add_assoc]

variable {Cm : Step2Mat sz} {lam' : ℕ → ℝ}
  {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The increment of a carrier with the property `StepDecompGen_WalkForm`: `H_{j+1} - H_j = √Δ X_{j+1}` (`pathH_succ`). -/
private theorem AzumaProxyGen_incr (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (ω : PathΩ sz) :
    Cm.Hpath s t K n (j + 1) ω - Cm.Hpath s t K n j ω =
      (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n (ω (j + 1)) := by
  rw [StepDecompGen_Hpath_eq hW, StepDecompGen_Hpath_eq hW]
  rw [show StepDecompGen_pathH sz lam' s t K n (j + 1) ω = _ from pathH_succ (sz.withLam lam') s t K n j ω]
  abel

/-- **`azumaSubGNg`** (band `azumaSubGN`, the statement `AzumaSubGNg`): for a finite family `Φ` in the
Hermitian test class, weights `κ`, a stopping family `{j < τ} ∈ F_j` on which the carrier walk lies in `G j`, and `Q`
majorising `Δ Σ_c gvar_c(lam' n) ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on the Hermitian matrices of `G j`, the stopped combination
`1_{j<τ} Σ_b κ_b Z_b` is conditionally sub-Gaussian with proxy `Q`.  Proof outline: the band `azumaSubGN` at the walk
`sz.withLam lam'` for the family `M ↦ Φ_b (Ψ n + M)`, which is in `HermTestFun` by `StepDecompGen_hermTestFun_shift`; the
carrier law is `pathP (sz.withLam lam')` and the carrier walk is `Ψ n + pathH (sz.withLam lam')` (`StepDecompGen_WalkForm`). -/
theorem azumaSubGNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] {lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : AzumaSubGNg Cm lam' s t K := by
  intro n ι _ Φ hΦ κ τ G hτ hG j Q hQ
  have hPp : Cm.Pp = pathP (sz.withLam lam') := hW.2.1
  set Φ' : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
    fun b M => Φ b (Ψ n + M) with hΦ'def
  set G' : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    fun j => {M | Ψ n + M ∈ G j} with hG'def
  have hΦ' : ∀ b, HermTestFun (sz.withLam lam') n (Φ' b) := fun b =>
    StepDecompGen_hermTestFun_withLam lam' (StepDecompGen_hermTestFun_shift (hΦ b) (hW.1 n))
  have hG' : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → StepDecompGen_pathH sz lam' s t K n j ω ∈ G' j := by
    intro ω j hj
    change Ψ n + StepDecompGen_pathH sz lam' s t K n j ω ∈ G j
    rw [← StepDecompGen_Hpath_eq hW]
    exact hG ω j hj
  have hQ' : ∀ M ∈ G' j, M.IsHermitian →
      gridStep s t K n * ∑ c : CoordF d (sz.L n) (sz.W n),
        (gvarF d (sz.L n) (sz.W n) (lam' n) c : ℝ) *
        ‖∑ b, κ b * RBM.Ind.dirDerivN (Φ' b) M (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 ≤ (Q : ℝ) := by
    intro M hM hMH
    have h := hQ (Ψ n + M) hM ((hW.1 n).add hMH)
    simp only [hΦ'def, AzumaProxyGen_dirDerivN_shift]
    exact h
  have key := RBM.Ind.azumaSubGN (sz.withLam lam') s t K n Φ' hΦ' κ τ G' hτ hG' j Q hQ'
  have hZ : ∀ (ω : PathΩ sz) (b : ι), ZfamNg Cm s t K n j Φ ω b =
      RBM.Ind.ZfamN (sz.withLam lam') s t K n j Φ' ω b := by
    intro ω b
    unfold ZfamNg RBM.Ind.ZfamN
    rw [AzumaProxyGen_incr hW, StepDecompGen_dirDerivN_smul, StepDecompGen_Hpath_eq hW]
    refine congrArg (HMul.hMul _) ?_
    exact (AzumaProxyGen_dirDerivN_shift (Φ b) (Ψ n) _ _).symm
  have hF : (fun ω : PathΩ sz => ∑ b, κ b * ZfamNg Cm s t K n j Φ ω b) =
      fun ω => ∑ b, κ b * RBM.Ind.ZfamN (sz.withLam lam') s t K n j Φ' ω b :=
    funext fun ω => Finset.sum_congr rfl fun b _ => by rw [hZ]
  unfold SubGaussFormNg
  rw [hF]
  exact ⟨StepDecompGen_hcsg_of_withLam lam' hPp key.1, StepDecompGen_hcsg_of_withLam lam' hPp key.2⟩

end Azuma

/-! ## 2. The composition -/

section Compose

variable {d : ℕ} {sz : Sizes d}

/-- The conjugation conjunct of `GridRepTailGen_Ker` turns the paired kernel of `STeeUMg` into the conjugate pairing of `QVPropagatedNg`
(the generic form of the identity `qvFormN = Re Σ κ κ̄' 𝓔⊗𝓔` that is definitional in the band, `qvFormN`). -/
private theorem AzumaProxyGen_qvForm_eq {Cm : Step2Mat sz} {n : ℕ} (hK : GridRepTailGen_Ker Cm.toFlowFM n) {v w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) {k : ℕ} (σ : Fin k → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin k → Zd d (sz.L n)) :
    qvFormNg Cm n v w σ M a = (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
      (∏ i : Fin k, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate k i)) v w (a i) (b i)) *
        (starRingEnd ℂ) (∏ i : Fin k, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate k i)) v w (a i) (b' i)) *
        STeeMg Cm n v M σ b b').re := by
  have hK4 := hK.2.2.2
  unfold qvFormNg STeeUMg
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  have hconj : ∏ i : Fin k, Step2Gen_uKer Cm.toFlowFM n (!σ i) (!σ (finRotate k i)) v w (a i) (b' i) =
      (starRingEnd ℂ) (∏ i : Fin k, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate k i)) v w (a i) (b' i)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => hK4 _ _ v w hw0 hw1 _ _
  rw [hconj]

/-- **`azumaProxy_subG_ugeng`** (band `azumaProxy_subG_ugen`): `SubGaussStopNg` for `ZvecNg` from the
statement `AzumaSubGNg`.  For the loop family `Φ_b = Cm.LM n u_{j+1} · σ b` (in the test class by `hermTestFunLoopNOf` under
`LoopForm`), the propagator weights `κ_b = Π_i (uKer-slot)(a_i, b_i)` and the variance proxy `QVPropagatedNg Cm g`
(`Σ_c gvar_c ‖Σ_b κ_b ∂_c 𝓛_b‖² ≤ k · Re Σ κ κ̄' STeeMg`); the identification of the right side with `qvFormNg` is the conjugation conjunct of `GridRepTailGen_Ker`.  What
remains for a consumer is the majorant `hQ` of `Δ · k · qvFormNg` on `G j`. -/
theorem azumaProxy_subG_ugeng {Cm : Step2Mat sz} [IsProbabilityMeasure Cm.Pp] {E g s t : ℕ → ℝ} {K : ℕ → ℕ}
    (h : AzumaSubGNg Cm g s t K) (hL : StepDecompGen_LoopForm Cm E) (hQV : QVPropagatedNg Cm g)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (n k : ℕ) (hKer : GridRepTailGen_Ker Cm.toFlowFM n) (hk : 2 ≤ k) (σ : Fin k → Bool)
    (τ : PathΩ sz → ℕ) (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
    (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (hG : ∀ ω j, j < τ ω → Cm.Hpath s t K n j ω ∈ G j) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s t K n * ((k : ℝ) * qvFormNg Cm n (gridTime s t K n (j + 1)) (gridTime s t K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopNg Cm σ (gridTime s t K n) τ (fun j ω => ZvecNg Cm s t K n j σ ω) m a j Q := by
  have hKn : K n ≠ 0 := by omega
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := azumaProxy2_gridTime_nonneg s t K n (hs0 n) (hst n) (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    (azumaProxy2_gridTime_le s t K n (hst n) (show j + 1 ≤ K n by omega) hKn).trans_lt (ht1 n)
  have hw0 : 0 ≤ gridTime s t K n m := azumaProxy2_gridTime_nonneg s t K n (hs0 n) (hst n) m
  have hw1 : gridTime s t K n m < 1 := (azumaProxy2_gridTime_le s t K n (hst n) hm hKn).trans_lt (ht1 n)
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy2_gridStep_nonneg (hst n)
  have hΦ : ∀ b, HermTestFun sz n (loopFamNg Cm s t K n j σ b) := fun b => by
    change HermTestFun sz n (fun H => Cm.LM n (gridTime s t K n (j + 1)) H σ b)
    rw [StepDecompGen_LM_eq hL]
    exact (hermTestFunLoopNOf sz k n (Cm.m n) (E n) _ (hL n).1 hu1 σ b).1
  have key := h n (loopFamNg Cm s t K n j σ) hΦ
    (fun b => ∏ i : Fin k, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate k i)) (gridTime s t K n (j + 1))
      (gridTime s t K n m) (a i) (b i)) τ G hτ hG j Q
    (fun M hMG hMH => by
      have hv := hQV n _ hu0 hu1 M hMH k hk σ
        (fun b => ∏ i : Fin k, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate k i)) (gridTime s t K n (j + 1))
          (gridTime s t K n m) (a i) (b i))
      have hq := hQ M hMG hMH
      rw [AzumaProxyGen_qvForm_eq hKer hw0 hw1] at hq
      exact (mul_le_mul_of_nonneg_left hv hΔ).trans hq)
  exact key

end Compose


/-! ## 3. The `Y` moments over the carrier -/

section YMoments

variable {d : ℕ}

/-- **The eight moment fields of the stopped weighted remainder, for an abstract walk** (core of `AzumaProxyN_YfieldsWg`;
band `AzumaProxyN_YfieldsW`, with the loop family `Φ` and the remainder `Yv` as data): `Yv` is a.e.
`stepYCN` of the identity kernel for `Φ`, `Φ` is in the Hermitian test class with the second-derivative bound `C₂`, `Σ_c ‖κ_c‖ ≤ S`
and `P ≥ 2000 (S C₂)² N⁸`; then the real and imaginary parts of `1_{j<τ} Σ_c κ_c Yv_c` have conditional mean zero, integrable
fourth power, conditional second moment `≤ Δ² P` and fourth moment `≤ Δ⁴ P²`. -/
private theorem AzumaProxyGen_YfieldsW_core (P : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n)
    {k : ℕ} {Φ : (Fin k → Zd d (P.L n)) → Matrix (Idx d (P.L n) (P.W n)) (Idx d (P.L n) (P.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun P n (Φ a)) (κ : (Fin k → Zd d (P.L n)) → ℂ)
    {Smax C2 Pb : ℝ} (hS0 : 0 ≤ Smax) (hC20 : 0 ≤ C2) (hrow : ∑ c, ‖κ c‖ ≤ Smax)
    (hC2 : ∀ (a : Fin k → Zd d (P.L n))
      (M y : Matrix (Idx d (P.L n) (P.W n)) (Idx d (P.L n) (P.W n)) ℂ), M.IsHermitian →
      y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C2 * ‖y‖ ^ 2)
    (hP : 2000 * (Smax * C2) ^ 2 * (P.size n : ℝ) ^ 8 ≤ Pb)
    (Yv : PathΩ P → (Fin k → Zd d (P.L n)) → ℂ) (hYm : Measurable Yv)
    (hYall : ∀ᵐ ω ∂(pathP P), ∀ c, Yv ω c =
      RBM.Ind.stepYCN P s t K n j Φ (fun a a' => if a = a' then 1 else 0) c ω)
    (τ : PathΩ P → ℕ) (hτ : ∀ j, MeasurableSet[filt P j] {ω | j < τ ω}) :
    (pathP P)[fun ω => ({ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * Yv ω' c) ω).re | filt P j] =ᵐ[pathP P] 0 ∧
    (pathP P)[fun ω => ({ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * Yv ω' c) ω).im | filt P j] =ᵐ[pathP P] 0 ∧
    Integrable (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * Yv ω' c) ω).re ^ 4) (pathP P) ∧
    Integrable (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * Yv ω' c) ω).im ^ 4) (pathP P) ∧
    (pathP P)[fun ω => ({ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * Yv ω' c) ω).re ^ 2 | filt P j]
      ≤ᵐ[pathP P] (fun _ => gridStep s t K n ^ 2 * Pb) ∧
    (pathP P)[fun ω => ({ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * Yv ω' c) ω).im ^ 2 | filt P j]
      ≤ᵐ[pathP P] (fun _ => gridStep s t K n ^ 2 * Pb) ∧
    ∫ ω, ({ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * Yv ω' c) ω).re ^ 4 ∂(pathP P)
      ≤ gridStep s t K n ^ 4 * Pb ^ 2 ∧
    ∫ ω, ({ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * Yv ω' c) ω).im ^ 4 ∂(pathP P)
      ≤ gridStep s t K n ^ 4 * Pb ^ 2 := by
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy2_gridStep_nonneg hst
  set Δ := gridStep s t K n with hΔdef
  set N : ℝ := (P.size n : ℝ) with hNdef
  set δ : (Fin k → Zd d (P.L n)) → (Fin k → Zd d (P.L n)) → ℂ := fun a a' => if a = a' then 1 else 0
    with hδ
  have hδrow : ∀ c : Fin k → Zd d (P.L n), ∑ a, ‖δ c a‖ = 1 := by
    intro c
    have h1 : ∀ x, ‖δ c x‖ = if c = x then (1 : ℝ) else 0 := by
      intro x
      by_cases h : c = x <;> simp [hδ, h]
    simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- the identity kernel, label by label
  have hDec : ∀ c : Fin k → Zd d (P.L n),
      (∀ᵐ ω ∂(pathP P), ‖RBM.Ind.stepYCN P s t K n j Φ δ c ω‖ ≤
          (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) * ‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 +
            (pathP P)[fun ω' => (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) *
              ‖Sizes.seqXmat P n (ω' (j + 1))‖ ^ 2 | filt P j] ω) ∧
      (pathP P)[RBM.Ind.stepYCN P s t K n j Φ δ c | filt P j] =ᵐ[pathP P]
        fun _ => (0 : ℂ) := by
    intro c
    have hIntRe := RBM.Ind.integrable_stepZCN_re_of_hermTestFun P s t K n j hΦ hC2 hΔ δ c
    have hIntIm := RBM.Ind.integrable_stepZCN_im_of_hermTestFun P s t K n j hΦ hC2 hΔ δ c
    obtain ⟨-, -, hbound, hmeanY⟩ := RBM.Ind.stepDecompCN P s t K n j hΦ hC2 hΔ δ c hIntRe hIntIm
    exact ⟨hbound, hmeanY⟩
  -- the increment moments
  set m2 : ℝ := ∫ ω, ‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 ∂(pathP P) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun _ => by positivity
  have hm2le : m2 ≤ 16 * N ^ 4 := integral_normSq_incr_le P n j
  set R1 : ℝ := (C2 / 2) * Δ with hR1
  set ρ : ℝ := Smax * R1 with hρ
  have hR10 : 0 ≤ R1 := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hcond : (pathP P)[fun ω' => R1 * ‖Sizes.seqXmat P n (ω' (j + 1))‖ ^ 2 | filt P j]
      =ᵐ[pathP P] fun _ => R1 * m2 := by
    have h := azumaProxy2_condExp_incr P j (φ := fun x => R1 * ‖Sizes.seqXmat P n x‖ ^ 2)
      (((azumaProxy2_measurable_normX P n).pow_const 2).const_mul _)
    have hint : ∫ ω, R1 * ‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 ∂(pathP P) = R1 * m2 :=
      integral_const_mul _ _
    rw [hint] at h
    exact h
  -- `Yv ω c` a.e. equals `stepYCN` of the identity kernel
  have hdomc : ∀ᵐ ω ∂(pathP P), ∀ c : Fin k → Zd d (P.L n),
      ‖Yv ω c‖ ≤ R1 * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2) := by
    have h1 : ∀ᵐ ω ∂(pathP P), ∀ c : Fin k → Zd d (P.L n),
        ‖RBM.Ind.stepYCN P s t K n j Φ δ c ω‖ ≤
          (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) * ‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 +
            (pathP P)[fun ω' => (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) *
              ‖Sizes.seqXmat P n (ω' (j + 1))‖ ^ 2 | filt P j] ω :=
      ae_all_iff.mpr fun c => (hDec c).1
    simp only [hδrow, one_mul] at h1
    filter_upwards [hYall, h1, hcond] with ω hY hb hcd c
    rw [hY c]
    refine (hb c).trans ?_
    rw [hcd]
    nlinarith
  have hYcm : ∀ c : Fin k → Zd d (P.L n), Measurable fun ω : PathΩ P => Yv ω c :=
    fun c => (measurable_pi_apply c).comp hYm
  have hYcint : ∀ c : Fin k → Zd d (P.L n), Integrable (fun ω : PathΩ P => Yv ω c) (pathP P) := fun c =>
    (((integrable_normSq_incr P n j).add (integrable_const m2)).const_mul R1).mono'
      (hYcm c).aestronglyMeasurable (by filter_upwards [hdomc] with ω h using h c)
  have hYcmean : ∀ c : Fin k → Zd d (P.L n),
      (pathP P)[fun ω => Yv ω c | filt P j] =ᵐ[pathP P] fun _ => (0 : ℂ) :=
    fun c => by
      have hae : (fun ω => Yv ω c) =ᵐ[pathP P] RBM.Ind.stepYCN P s t K n j Φ δ c := by
        filter_upwards [hYall] with ω h using h c
      exact (condExp_congr_ae hae).trans (hDec c).2
  -- the weighted combination
  set Vfull : PathΩ P → ℂ := fun ω => ∑ c, κ c * Yv ω c with hVfull
  have hVm : Measurable Vfull :=
    Finset.measurable_sum _ fun c _ => (hYcm c).const_mul _
  have hdom : ∀ᵐ ω ∂(pathP P), ‖Vfull ω‖ ≤
      ρ * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomc] with ω h
    have hX0 : 0 ≤ ‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2 := by positivity
    calc ‖Vfull ω‖ ≤ ∑ c, ‖κ c * Yv ω c‖ := norm_sum_le _ _
      _ = ∑ c, ‖κ c‖ * ‖Yv ω c‖ := by simp only [norm_mul]
      _ ≤ ∑ c, ‖κ c‖ * (R1 * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2)) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h c) (norm_nonneg _)
      _ = (∑ c, ‖κ c‖) * (R1 * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ Smax * (R1 * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2)) :=
          mul_le_mul_of_nonneg_right hrow (by positivity)
      _ = ρ * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2) := by rw [hρ]; ring
  have hmean : (pathP P)[Vfull | filt P j] =ᵐ[pathP P] fun _ => (0 : ℂ) := by
    have hint : ∀ c ∈ (Finset.univ : Finset (Fin k → Zd d (P.L n))),
        Integrable (fun ω => κ c * Yv ω c) (pathP P) :=
      fun c _ => (hYcint c).const_mul (κ c)
    have hcs := condExp_finsetSum hint (filt P j)
    have hsm : ∀ᵐ ω ∂(pathP P), ∀ c : Fin k → Zd d (P.L n),
        (pathP P)[fun ω' => κ c * Yv ω' c | filt P j] ω =
          κ c * (pathP P)[fun ω' => Yv ω' c | filt P j] ω :=
      ae_all_iff.mpr fun c =>
        condExp_smul (κ c) (fun ω' => Yv ω' c) (filt P j)
    have hz : ∀ᵐ ω ∂(pathP P), ∀ c : Fin k → Zd d (P.L n),
        (pathP P)[fun ω' => Yv ω' c | filt P j] ω = 0 :=
      ae_all_iff.mpr fun c => hYcmean c
    have hsumfn : (∑ c : Fin k → Zd d (P.L n), fun ω' => κ c * Yv ω' c) = Vfull := by
      funext ω'
      simp only [hVfull, Finset.sum_apply]
    rw [hsumfn] at hcs
    filter_upwards [hcs, hsm, hz] with ω h1 h2 h3
    rw [h1]
    simp only [Finset.sum_apply, h2, h3, mul_zero, Finset.sum_const_zero]
  have hS : MeasurableSet[filt P j] {ω | j < τ ω} := hτ j
  have hB4 := integral_normPow4_incr_le P n j
  have hB8 := RBM.Ind.AzumaProxyN_integral_normPow8_incr_le P n j
  -- the stopped moments
  have hVint : Integrable Vfull (pathP P) :=
    (((integrable_normSq_incr P n j).add (integrable_const m2)).const_mul ρ).mono'
      hVm.aestronglyMeasurable hdom
  have hSm : MeasurableSet {ω | j < τ ω} := (filt P).le j _ hS
  have hVind : Measurable ({ω | j < τ ω}.indicator Vfull) := hVm.indicator hSm
  have hdomS : ∀ᵐ ω ∂(pathP P), ‖{ω | j < τ ω}.indicator Vfull ω‖
      ≤ ρ * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdom] with ω hω
    exact (norm_indicator_le_norm_self _ _).trans hω
  have hdomRe : ∀ᵐ ω ∂(pathP P), |({ω | j < τ ω}.indicator Vfull ω).re|
      ≤ ρ * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_re_le_norm _).trans h
  have hdomIm : ∀ᵐ ω ∂(pathP P), |({ω | j < τ ω}.indicator Vfull ω).im|
      ≤ ρ * (‖Sizes.seqXmat P n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_im_le_norm _).trans h
  obtain ⟨hRe4, hRe2, hRe4'⟩ := azumaProxy2_moments_of_dom P n j
    (Complex.measurable_re.comp hVind) hρ0 hm20 hB4 hB8 hdomRe
  obtain ⟨hIm4, hIm2, hIm4'⟩ := azumaProxy2_moments_of_dom P n j
    (Complex.measurable_im.comp hVind) hρ0 hm20 hB4 hB8 hdomIm
  obtain ⟨hmRe, hmIm⟩ := azumaProxy2_condExp_stopped_reim P j hS hVint hmean
  -- the numerical bounds
  have hq0 : 0 ≤ Smax * C2 := mul_nonneg hS0 hC20
  have hN0 : 0 ≤ N := by positivity
  have hρq : ρ = (Smax * C2) * Δ / 2 := by simp only [hρ, hR1]; ring
  have hv : 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2) ≤ Δ ^ 2 * Pb := by
    have hm2sq : m2 ^ 2 ≤ 256 * N ^ 8 := by
      calc m2 ^ 2 ≤ (16 * N ^ 4) ^ 2 := pow_le_pow_left₀ hm20 hm2le 2
        _ = 256 * N ^ 8 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8 := by positivity
    calc 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2)
        ≤ 2 * ρ ^ 2 * (768 * N ^ 8 + 256 * N ^ 8) := by gcongr
      _ = 512 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by rw [hρq]; ring
      _ ≤ 2000 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by nlinarith
      _ = Δ ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8) := by ring
      _ ≤ Δ ^ 2 * Pb := by gcongr
  have hw : 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4) ≤ Δ ^ 4 * Pb ^ 2 := by
    have hm2q : m2 ^ 4 ≤ 65536 * N ^ 16 := by
      calc m2 ^ 4 ≤ (16 * N ^ 4) ^ 4 := pow_le_pow_left₀ hm20 hm2le 4
        _ = 65536 * N ^ 16 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16 := by positivity
    have hP0 : 0 ≤ 2000 * (Smax * C2) ^ 2 * N ^ 8 := by positivity
    calc 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4)
        ≤ 8 * ρ ^ 4 * (6881280 * N ^ 16 + 65536 * N ^ 16) := by gcongr
      _ = 3473408 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by rw [hρq]; ring
      _ ≤ 4000000 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by nlinarith
      _ = Δ ^ 4 * (2000 * (Smax * C2) ^ 2 * N ^ 8) ^ 2 := by ring
      _ ≤ Δ ^ 4 * Pb ^ 2 := by gcongr
  refine ⟨hmRe, hmIm, hRe4, hIm4, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hRe2] with ω h
    exact h.trans hv
  · filter_upwards [hIm2] with ω h
    exact h.trans hv
  · exact hRe4'.trans hw
  · exact hIm4'.trans hw


variable {sz : Sizes d}

/-- **`AzumaProxyN_stopWg`** (band `AzumaProxyN_stopW`): the stopped weighted increment
`1_{j<τ} Σ_c κ_c Y_c` of the step `j → j+1`. -/
def AzumaProxyN_stopWg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (κ : (Fin k → Zd d (sz.L n)) → ℂ) (τ : PathΩ sz → ℕ) (ω : PathΩ sz) : ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * YvecNg Cm s t K n j σ ω' c) ω

/-- **`AzumaProxyN_YfieldsWg`** (band `AzumaProxyN_YfieldsW`): the eight moment fields for the stopped
weighted increment `1_{j<τ} Σ_c κ_c (Y_j)_c` of an arbitrary weight vector, over the carrier.  For `Σ_c ‖κ_c‖ ≤ S`, the Hermitian
second-derivative bound `C₂` of the loop family seen from the shifted walk (`loopFamNgShift`) and `P ≥ 2000 (S C₂)² N⁸`, the
real and imaginary parts have conditional mean zero, integrable fourth power, conditional second moment `≤ Δ² P` and fourth
moment `≤ Δ⁴ P²`.  Proof outline: the core at the walk `sz.withLam lam'` (`YvecNg_eq_stepYCN`, `stepDecompCN`); the carrier law is
`pathP (sz.withLam lam')` (`StepDecompGen_WalkForm`).  The hypotheses `0 ≤ s n`, `|E n| < 2` of the band are not read. -/
theorem AzumaProxyN_YfieldsWg {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ)
    {Smax C2 P : ℝ} (hS0 : 0 ≤ Smax) (hC20 : 0 ≤ C2) (hrow : ∑ c, ‖κ c‖ ≤ Smax)
    (hC2 : ∀ (a : Fin k → Zd d (sz.L n))
      (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
      y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamNgShift Cm Ψ s t K n j σ a)) M y y‖ ≤ C2 * ‖y‖ ^ 2)
    (hP : 2000 * (Smax * C2) ^ 2 * (sz.size n : ℝ) ^ 8 ≤ P)
    (τ : PathΩ sz → ℕ) (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) :
    Cm.Pp[fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).re | filt sz j] =ᵐ[Cm.Pp] 0 ∧
    Cm.Pp[fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).im | filt sz j] =ᵐ[Cm.Pp] 0 ∧
    Integrable (fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).re ^ 4) Cm.Pp ∧
    Integrable (fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).im ^ 4) Cm.Pp ∧
    Cm.Pp[fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).re ^ 2 | filt sz j]
      ≤ᵐ[Cm.Pp] (fun _ => gridStep s t K n ^ 2 * P) ∧
    Cm.Pp[fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).im ^ 2 | filt sz j]
      ≤ᵐ[Cm.Pp] (fun _ => gridStep s t K n ^ 2 * P) ∧
    ∫ ω, (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).re ^ 4 ∂Cm.Pp ≤ gridStep s t K n ^ 4 * P ^ 2 ∧
    ∫ ω, (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).im ^ 4 ∂Cm.Pp ≤ gridStep s t K n ^ 4 * P ^ 2 := by
  have hPp : Cm.Pp = pathP (sz.withLam lam') := hW.2.1
  have hYm : Measurable fun ω : PathΩ sz => YvecNg Cm s t K n j σ ω :=
    (GridAssemblyGen_stronglyMeasurable_YvecNg hL hW s t K n j σ).measurable.mono ((filt sz).le (j + 1)) le_rfl
  have hYall : ∀ᵐ ω ∂(pathP (sz.withLam lam')), ∀ c, YvecNg Cm s t K n j σ ω c =
      RBM.Ind.stepYCN (sz.withLam lam') s t K n j (loopFamNgShift Cm Ψ s t K n j σ)
        (fun a a' => if a = a' then 1 else 0) c ω := by
    rw [← hPp]
    exact YvecNg_eq_stepYCN hL hW s t K n j hst ht1 hj σ
  rw [hPp]
  exact AzumaProxyGen_YfieldsW_core (sz.withLam lam') s t K n j hst
    (StepDecompGen_hΦ hL hW s t K n j hst ht1 hj σ) κ hS0 hC20 hrow hC2 hP
    (fun ω => YvecNg Cm s t K n j σ ω) hYm hYall τ hτ


/-! ### The numerical helpers, over a carrier

`AzumaProxyN_inv_one_sub_le_pub` and `AzumaProxyN_P_le_pub` are model-free and are used as they are. -/

/-- **`η_u⁻¹ ≤ N^{1-τ'} / c₀`** for `u ≤ t` under the range condition,
from `DecayGen_Spec` (`η_u = (1 - u) Im m ≥ (1 - u) κm`). -/
theorem AzumaProxyN_eta_inv_le_pubg {C : FlowFM sz} {κm : ℝ} (h : DecayGen_Spec C κm) (n : ℕ) {u t τ' N : ℝ}
    (hut : u ≤ t) (hN0 : 0 < N) (hR : N ^ (-1 + τ') ≤ 1 - t) :
    (C.eta n u)⁻¹ ≤ N ^ (1 - τ') / κm := by
  have hc0 := h.1
  have hpos : 0 < N ^ (-1 + τ') := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (-1 + τ') ≤ 1 - u := by linarith
  have hη : N ^ (-1 + τ') * κm ≤ C.eta n u := by
    rw [h.2.2 n u]
    exact mul_le_mul h1 (h.2.1 n) hc0.le (by linarith)
  calc (C.eta n u)⁻¹ ≤ (N ^ (-1 + τ') * κm)⁻¹ := inv_anti₀ (mul_pos hpos hc0) hη
    _ = N ^ (1 - τ') / κm := by
        rw [mul_inv, show (-1 + τ') = -(1 - τ') by ring, Real.rpow_neg hN0.le, inv_inv]
        exact (div_eq_mul_inv _ _).symm

/-- **The row sums of the kernel of `Step2Gen_UN`** : for `0 ≤ v, w < 1`,
`Σ_b ‖Π_i uKer(a_i, b_i)‖ ≤ (1 + (1 - w)⁻¹)^k`, from the near-identity conjunct of `GridRepTailGen_Ker` (the one-slot bound is
`GridAssemblyGen_row_le`; the row-sum conjunct would need `v ≤ w`). -/
theorem AzumaProxyN_rowsum_UN_pubg {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n) {k : ℕ}
    (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (a : Fin k → Zd d (sz.L n)) :
    ∑ b : Fin k → Zd d (sz.L n), ‖∏ i : Fin k, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w (a i) (b i)‖ ≤
      (1 + (1 - w)⁻¹) ^ k := by
  have hrow : ∀ i : Fin k, ∑ c : Zd d (sz.L n), ‖Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w (a i) c‖ ≤
      1 + (1 - w)⁻¹ := fun i => GridAssemblyGen_row_le hK _ _ hv0 hv1 hw0 hw1 (a i)
  simp_rw [norm_prod]
  rw [← Fintype.prod_sum (fun (i : Fin k) (c : Zd d (sz.L n)) =>
    ‖Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w (a i) c‖)]
  calc ∏ i : Fin k, ∑ c : Zd d (sz.L n), ‖Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w (a i) c‖
      ≤ ∏ _i : Fin k, (1 + (1 - w)⁻¹) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _) (fun i _ => hrow i)
    _ = (1 + (1 - w)⁻¹) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The statement `YMomentsUnifNg` and the uniform `Y` moments -/

/-- **`YMomentsUnifNg`** (band `YMomentsUnifN`): the constant `C_P` is
taken **before** the grid `K`; `0 < κ` and `|E n| ≤ 2 - κ` become `DecayGen_Spec` (`κm ≤ Im m`, `η = (1 - t) Im m`). -/
def YMomentsUnifNg (Cm : Step2Mat sz) (κm τ' : ℝ) (s t : ℕ → ℝ) : Prop :=
  DecayGen_Spec Cm.toFlowFM κm → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  sz.SizeTendsto → sz.RangeCond τ' t →
  ∀ (k : ℕ) (σ : Fin k → Bool), ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsNg Cm σ (gridTime s t K n) τ (K n) (fun j ω => YvecNg Cm s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

/-- **`yMomentsUnifNg`** (band `yMomentsUnifN`): the uniform `Y` moments over the carrier.  **Explicit
witness** `C_P = 11 + (4k + 4) · max 0 (1 - τ')`, chosen before the grid `K` (the same as the band's: `N` enters only as a symbol);
`P = 2000 (S C₂)² N⁸` with `S = (2 Θ)^k` (row sums of the kernel, near-identity conjunct), `C₂ = k (k + 1) N (Θ / κm)^{k+2}` (the Hermitian second
derivative of the loops, `StepDecompGen_loopFamShift_hermTestFun`), `Θ = N^{max 0 (1-τ')}`.  The kernel class
`GridRepTailGen_Ker` is the hypothesis `hKer`; `StepDecompGen_LoopForm` and `StepDecompGen_WalkForm` are the classes of the per-step layer. -/
theorem yMomentsUnifNg {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hKer : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n) (κm τ' : ℝ) (s t : ℕ → ℝ) : YMomentsUnifNg Cm κm τ' s t := by
  intro hspec hs0 hst ht1 hsize hrange k σ
  have hc0 : 0 < κm := hspec.1
  set θ : ℝ := max 0 (1 - τ') with hθdef
  have hθ0 : 0 ≤ θ := le_max_left _ _
  refine ⟨11 + (4 * k + 4) * θ, by positivity, ?_⟩
  intro K hK
  have hbig := hsize.eventually (eventually_ge_atTop
    (max 1 (2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (κm⁻¹) ^ (k + 2)) ^ 2)))
  filter_upwards [hrange, hbig] with n hR hN
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hN
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hΘ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ θ := Real.one_le_rpow hN1 hθ0
  have hΘ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ θ := by positivity
  set Smax : ℝ := (2 * ((sz.size n : ℕ) : ℝ) ^ θ) ^ k with hSmax
  set C2 : ℝ := ((k * (k + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ)
    * (((sz.size n : ℕ) : ℝ) ^ θ / κm) ^ (k + 2) with hC2def
  have hS0 : 0 ≤ Smax := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨2000 * (Smax * C2) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8, by positivity, ?_, ?_⟩
  · exact RBM.Ind.AzumaProxyN_P_le_pub k hc0 hθ0 hN1 ((le_max_right _ _).trans hN)
  · intro τ hτ
    refine ⟨fun j => GridAssemblyGen_stronglyMeasurable_YvecNg hL hW s t K n j σ, ?_⟩
    intro m hm b j hjm
    have hj : j + 1 ≤ K n := by omega
    have hKn : K n ≠ 0 := hK n
    have hv0 : 0 ≤ gridTime s t K n (j + 1) := azumaProxy2_gridTime_nonneg s t K n (hs0 n) (hst n) (j + 1)
    have hvt : gridTime s t K n (j + 1) ≤ t n := azumaProxy2_gridTime_le s t K n (hst n) hj hKn
    have hv1 : gridTime s t K n (j + 1) < 1 := hvt.trans_lt (ht1 n)
    have hw0 : 0 ≤ gridTime s t K n m := azumaProxy2_gridTime_nonneg s t K n (hs0 n) (hst n) m
    have hwt : gridTime s t K n m ≤ t n := azumaProxy2_gridTime_le s t K n (hst n) hm hKn
    have hw1 : gridTime s t K n m < 1 := hwt.trans_lt (ht1 n)
    refine AzumaProxyN_YfieldsWg hL hW s t K n j (hst n) (ht1 n) hj σ
      (fun c => ∏ i : Fin k, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate k i)) (gridTime s t K n (j + 1))
        (gridTime s t K n m) (b i) (c i)) hS0 hC20 ?_ ?_ le_rfl τ hτ
    · refine (AzumaProxyN_rowsum_UN_pubg (hKer n) σ hv0 hv1 hw0 hw1 b).trans ?_
      have h1 : (1 - gridTime s t K n m)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τ') :=
        RBM.Ind.AzumaProxyN_inv_one_sub_le_pub hwt hN0 hR
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (1 - τ') ≤ ((sz.size n : ℕ) : ℝ) ^ θ :=
        Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    · intro a M y hM hy
      have hη := AzumaProxyN_eta_inv_le_pubg hspec n (u := gridTime s t K n (j + 1)) (t := t n) (τ' := τ')
        (N := ((sz.size n : ℕ) : ℝ)) hvt hN0 hR
      have hη' : (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ θ / κm :=
        hη.trans (by
          gcongr
          exact le_max_right _ _)
      have h := (StepDecompGen_loopFamShift_hermTestFun hL hW s t K n j (hst n) (ht1 n) hj σ a).2 M y hM hy
      refine h.trans ?_
      have hpos : 0 < Cm.eta n (gridTime s t K n (j + 1)) := by
        rw [hspec.2.2 n]
        exact mul_pos (by linarith) (lt_of_lt_of_le hc0 (hspec.2.1 n))
      have hle : ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ)
          * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (k + 2) ≤ C2 := by
        rw [hC2def]
        have hη0 : 0 ≤ (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ := inv_nonneg.mpr hpos.le
        have := pow_le_pow_left₀ hη0 hη' (k + 2)
        have hpos' : 0 ≤ ((k * (k + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left this hpos' |>.trans (le_of_eq (by ring))
      exact mul_le_mul_of_nonneg_right hle (by positivity)

end YMoments

end RBM.BA

end
