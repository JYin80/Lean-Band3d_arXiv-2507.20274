/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridGoodGen
import RBM3D.Chain.GridAssemblyGen
import RBM3D.Induction.AzumaProxyN2

/-!
# The Azuma proxies and the `Y` moments over the carrier (T4s2c of T2473, targets 8-10)

Generic forms of `Induction/AzumaProxyN.lean` and `Induction/AzumaProxyN2.lean` (not edited) over a
carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.  Amend 1 and Amend 2 of T2473:
this is the third row T4s2c (`AzumaProxyGen`: targets 8, 9, 10).  The pins `AzumaSubGNg`,
`YMomentsNg`, `AssembledNg` are T4s2b's (`Chain/GridAssemblyGen`); the per-step vocabulary and the
classes `StepDecompGen_LoopForm`, `StepDecompGen_WalkForm`, `QVPropagatedNg` are T2474's
(`Chain/StepDecompGen`).

* §1 target 8: `azumaSubGNg`, the band `azumaSubGN` at the walk `sz.withLam lam'` with the test
  family shifted by the Hermitian `Ψ n` (the carrier walk is `Ψ n + pathH (sz.withLam lam')`,
  `StepDecompGen_WalkForm`).
* §2 targets 8 and 9: the compositions `azumaProxy_subG_ugeng`, `azumaProxy_subG_goodExitg`, the
  positivity of the exit time `azumaProxy_pos_gridExitTauNg`, `azumaProxy_Hpath_zerog`; the
  initial membership is the inline hypothesis `h0` of `azumaProxy_pos_goodExitTauNg` (band:
  `zero_mem_goodSetN_of_levels`; BA: owed to T4-BA).
* §3 target 10: the pin `YMomentsUnifNg`, the weighted `Y` fields `AzumaProxyN_YfieldsWg`,
  `yMomentsUnifNg`, `yMomentsNg_of_unif`, `yMomentsNg` and the public forms of the numerical
  helpers.
* §4 band bridges and band corollaries; §5 compiled nonempty instances at `d = 3`.

Private band helpers that mention no band object are reused by `open private`; the lemmas that
read `Ugen`, `pathP`, `pathH`, `zt E u` are restated under the stem `AzumaProxyGen_`.
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

/-! ## 1. Target 8: `azumaSubGNg` -/

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

/-- The increment of a `WalkForm` carrier: `H_{j+1} - H_j = √Δ X_{j+1}` (`pathH_succ`). -/
private theorem AzumaProxyGen_incr (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (ω : PathΩ sz) :
    Cm.Hpath s t K n (j + 1) ω - Cm.Hpath s t K n j ω =
      (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n (ω (j + 1)) := by
  rw [StepDecompGen_Hpath_eq hW, StepDecompGen_Hpath_eq hW]
  rw [show StepDecompGen_pathH sz lam' s t K n (j + 1) ω = _ from pathH_succ (sz.withLam lam') s t K n j ω]
  abel

/-- **Target 8, `azumaSubGNg`** (band `azumaSubGN`, `AzumaProxyN:257`, the pin `AzumaSubGNg`): for a finite family `Φ` in the
Hermitian test class, weights `κ`, a stopping family `{j < τ} ∈ F_j` on which the carrier walk lies in `G j`, and `Q`
majorising `Δ Σ_c gvar_c(lam' n) ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on the Hermitian matrices of `G j`, the stopped combination
`1_{j<τ} Σ_b κ_b Z_b` is conditionally sub-Gaussian with proxy `Q`.  Route: the band `azumaSubGN` at the walk
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

/-! ## 2. Targets 8 and 9: the compositions, the exit time, the initial state -/

section Compose

variable {d : ℕ} {sz : Sizes d}

/-- **Target 8, `azumaProxy_Hpath_zerog`** (band `azumaProxy_pathH_zero_of_s_zero`, `AzumaProxyN:970`): at `s n = 0` the carrier
walk starts at the Hermitian shift `Ψ n` (`H_0 = Ψ n + √s X_0 = Ψ n`); band `Ψ = 0`, BA `Ψ = λ₀ Ψ_B`. -/
theorem azumaProxy_Hpath_zerog {Cm : Step2Mat sz} {lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs : s n = 0) (ω : PathΩ sz) :
    Cm.Hpath s t K n 0 ω = Ψ n := by
  rw [StepDecompGen_Hpath_eq hW]
  have h : StepDecompGen_pathH sz lam' s t K n 0 ω = 0 :=
    RBM.Ind.azumaProxy_pathH_zero_of_s_zero (sz.withLam lam') s t K n hs ω
  rw [h, add_zero]

/-- **Target 8, `azumaProxy_pos_gridExitTauNg`** (band `azumaProxy_pos_gridExitTauN`, `AzumaProxyN:1027`): the exit time of the
carrier walk from `G` is positive when `H_0 ∈ G 0` and the grid has a step. -/
theorem azumaProxy_pos_gridExitTauNg {Cm : Step2Mat sz} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    {G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}
    {ω : PathΩ sz} (hK : 0 < K n) (h0 : Cm.Hpath s v K n 0 ω ∈ G 0) :
    0 < gridExitTauNg Cm s v K n G ω := by
  unfold gridExitTauNg firstHit
  by_contra hle
  have hle' := Nat.le_of_not_lt hle
  obtain ⟨j, hj, hmem⟩ := (MeasureTheory.hittingBtwn_le_iff_of_lt (i := 0) hK).1 hle'
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  have hnot : Cm.Hpath s v K n 0 ω ∉ (G 0)ᶜ := fun h => h h0
  rw [Set.indicator_of_notMem hnot] at hmem
  norm_num at hmem

/-- **Target 9, `azumaProxy_pos_goodExitTauNg`**: the exit time of the carrier walk from the good set is positive when the
initial state is good, `H_0 ∈ GoodSetNg … u_0`.  The initial membership `h0` is an **inline hypothesis** (no named `Prop`):
band `zero_mem_goodSetN_of_levels` (`AzumaProxyN:924`) at `s n = 0` with `azumaProxy_Hpath_zerog`; BA: owed to T4-BA. -/
theorem azumaProxy_pos_goodExitTauNg {Cm : Step2Mat sz} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (k : ℕ) (Γ Λ Φ : ℕ → ℝ)
    (τ' D' : ℝ) {ω : PathΩ sz} (hK : 0 < K n)
    (h0 : GoodSetNg Cm n (gridTime s v K n 0) k (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v K n 0 ω)) :
    0 < goodExitTauNg Cm s v K k Γ Λ Φ τ' D' n ω :=
  azumaProxy_pos_gridExitTauNg (G := fun j => {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H}) hK h0

/-- `K4` turns the paired kernel of `STeeUMg` into the conjugate pairing of `QVPropagatedNg` (the generic form of the
identity `qvFormN = Re Σ κ κ̄' 𝓔⊗𝓔` that is definitional in the band; proved under `K4`, cf. `bandStep2_qvFormN`). -/
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

/-- **Target 8, `azumaProxy_subG_ugeng`** (band `azumaProxy_subG_ugen`, `AzumaProxyN:980`): `SubGaussStopNg` for `ZvecNg` from the
pin `AzumaSubGNg`.  For the loop family `Φ_b = Cm.LM n u_{j+1} · σ b` (in the test class by `hermTestFunLoopNOf` under
`LoopForm`), the propagator weights `κ_b = Π_i (uKer-slot)(a_i, b_i)` and the variance proxy `QVPropagatedNg Cm g`
(`Σ_c gvar_c ‖Σ_b κ_b ∂_c 𝓛_b‖² ≤ k · Re Σ κ κ̄' STeeMg`); the identification of the right side with `qvFormNg` is K4.  What
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

/-- **Target 8, `azumaProxy_subG_goodExitg`** (band `azumaProxy_subG_goodExit`, `AzumaProxyN:1010`): with `G j = GoodSetNg …` and
`τ = goodExitTauNg`, the membership hypothesis of `azumaProxy_subG_ugeng` is `mem_of_lt_gridExitTauNg` and its measurability
hypothesis is `goodExitMeasNg` (`LoopForm`, `WalkForm`); what remains is the majorant `hQ` on the good set. -/
theorem azumaProxy_subG_goodExitg {Cm : Step2Mat sz} [IsProbabilityMeasure Cm.Pp] {E g lam' s v : ℕ → ℝ} {K : ℕ → ℕ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (h : AzumaSubGNg Cm g s v K) (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hQV : QVPropagatedNg Cm g)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n k : ℕ) (hKer : GridRepTailGen_Ker Cm.toFlowFM n) (hk : 2 ≤ k) (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ)
    (m : ℕ) (hm : m ≤ K n) (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M, GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' M → M.IsHermitian →
      gridStep s v K n * ((k : ℝ) * qvFormNg Cm n (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopNg Cm σ (gridTime s v K n) (goodExitTauNg Cm s v K k Γ Λ Φ τ' D' n)
      (fun j ω => ZvecNg Cm s v K n j σ ω) m a j Q :=
  azumaProxy_subG_ugeng h hL hQV hs0 hsv hv1 n k hKer hk σ (goodExitTauNg Cm s v K k Γ Λ Φ τ' D' n)
    (fun j => {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H})
    (fun j => goodExitMeasNg hL hW s v K n k Γ Λ Φ τ' D' j) (fun ω j hj => mem_of_lt_gridExitTauNg hj) m hm a j hj Q hQ

end Compose


/-! ## 3. Target 10: the `Y` moments over the carrier -/

section YMoments

variable {d : ℕ}

/-- **The eight moment fields of the stopped weighted remainder, for an abstract walk** (core of `AzumaProxyN_YfieldsWg`;
band `AzumaProxyN_YfieldsW`, `AzumaProxyN2:1025`, with the loop family `Φ` and the remainder `Yv` as data): `Yv` is a.e.
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

/-- **`AzumaProxyN_stopWg`** (band `AzumaProxyN_stopW`, `AzumaProxyN2:1016`): the stopped weighted increment
`1_{j<τ} Σ_c κ_c Y_c` of the step `j → j+1`. -/
def AzumaProxyN_stopWg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (κ : (Fin k → Zd d (sz.L n)) → ℂ) (τ : PathΩ sz → ℕ) (ω : PathΩ sz) : ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * YvecNg Cm s t K n j σ ω' c) ω

/-- **Target 10, `AzumaProxyN_YfieldsWg`** (band `AzumaProxyN_YfieldsW`, `AzumaProxyN2:1025`): the eight moment fields for the stopped
weighted increment `1_{j<τ} Σ_c κ_c (Y_j)_c` of an arbitrary weight vector, over the carrier.  For `Σ_c ‖κ_c‖ ≤ S`, the Hermitian
second-derivative bound `C₂` of the loop family seen from the shifted walk (`loopFamNgShift`) and `P ≥ 2000 (S C₂)² N⁸`, the
real and imaginary parts have conditional mean zero, integrable fourth power, conditional second moment `≤ Δ² P` and fourth
moment `≤ Δ⁴ P²`.  Route: the core at the walk `sz.withLam lam'` (`YvecNg_eq_stepYCN`, `stepDecompCN`); the carrier law is
`pathP (sz.withLam lam')` (`StepDecompGen_WalkForm`).  The premises `0 ≤ s n`, `|E n| < 2` of the band are not read. -/
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


/-! ### The numerical helpers, over a carrier (the public forms of `AzumaProxyN2:1227-1266`)

`AzumaProxyN_inv_one_sub_le_pub` and `AzumaProxyN_P_le_pub` are model-free and reused unchanged. -/

/-- **`c₀ > 0`** (band `AzumaProxyN_c0_pos_pub`, `AzumaProxyN2:1231`): the lower bound `κm` of `Im m` of `DecayGen_Spec` is the
constant `c₀` (band `√κ/2`, `DecayGen_bandSpec`). -/
theorem AzumaProxyN_c0_pos_pubg {C : FlowFM sz} {κm : ℝ} (h : DecayGen_Spec C κm) : 0 < κm := h.1

/-- **`η_u⁻¹ ≤ N^{1-τ'} / c₀`** for `u ≤ t` under the range condition (band `AzumaProxyN_etaT_inv_le_pub`, `AzumaProxyN2:1243`),
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

/-- **The row sums of the kernel of `Step2Gen_UN`** (band `AzumaProxyN_rowsum_Ugen_pub`, `AzumaProxyN2:1258`): for `0 ≤ v, w < 1`,
`Σ_b ‖Π_i uKer(a_i, b_i)‖ ≤ (1 + (1 - w)⁻¹)^k`, from the near-identity bound K3 of `GridRepTailGen_Ker` (the one-slot bound is
`GridAssemblyGen_row_le`; K2 would need `v ≤ w`, see `T2473b-prove.md` (a′)). -/
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

/-! ### The pin `YMomentsUnifNg` and the uniform `Y` moments -/

/-- **Pin `YMomentsUnifNg`: the primed successor of `YMomentsNg`** (band `YMomentsUnifN`, `AzumaProxyN2:894`): the constant `C_P` is
taken **before** the grid `K`; `0 < κ` and `|E n| ≤ 2 - κ` become `DecayGen_Spec` (`κm ≤ Im m`, `η = (1 - t) Im m`).  It implies
`YMomentsNg` (`yMomentsNg_of_unif`). -/
def YMomentsUnifNg (Cm : Step2Mat sz) (κm τ' : ℝ) (s t : ℕ → ℝ) : Prop :=
  DecayGen_Spec Cm.toFlowFM κm → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  sz.SizeTendsto → sz.RangeCond τ' t →
  ∀ (k : ℕ) (σ : Fin k → Bool), ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsNg Cm σ (gridTime s t K n) τ (K n) (fun j ω => YvecNg Cm s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

/-- **Target 10, `yMomentsUnifNg`** (band `yMomentsUnifN`, `AzumaProxyN2:915`): the uniform `Y` moments over the carrier.  **Explicit
witness** `C_P = 11 + (4k + 4) · max 0 (1 - τ')`, chosen before the grid `K` (the same as the band's: `N` enters only as a symbol);
`P = 2000 (S C₂)² N⁸` with `S = (2 Θ)^k` (row sums of the kernel, K3), `C₂ = k (k + 1) N (Θ / κm)^{k+2}` (the Hermitian second
derivative of the loops, `StepDecompGen_loopFamShift_hermTestFun`), `Θ = N^{max 0 (1-τ')}`.  The kernel class
`GridRepTailGen_Ker` is premise `hKer`; `LoopForm` and `WalkForm` are the classes of the per-step layer. -/
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

/-- `YMomentsUnifNg` implies `YMomentsNg` (the `C_P` of the uniform statement serves every `K`; band `yMomentsN_of_unif`). -/
theorem yMomentsNg_of_unif {Cm : Step2Mat sz} {κm τ' : ℝ} {s t : ℕ → ℝ} (h : YMomentsUnifNg Cm κm τ' s t)
    (K : ℕ → ℕ) : YMomentsNg Cm κm τ' s t K := by
  intro hspec hs hst ht hK hsize hrange k σ
  obtain ⟨C_P, hC, hev⟩ := h hspec hs hst ht hsize hrange k σ
  exact ⟨C_P, hC, hev K hK⟩

/-- **Target 10, `yMomentsNg`** (band `yMomentsN`, `AzumaProxyN2:992`): the pin `YMomentsNg` (`Chain/GridAssemblyGen`) over the
carrier, explicit witness `C_P = 11 + (4k + 4) · max 0 (1 - τ')`; obtained from `yMomentsUnifNg`. -/
theorem yMomentsNg {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hKer : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n) (κm τ' : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    YMomentsNg Cm κm τ' s t K :=
  yMomentsNg_of_unif (yMomentsUnifNg hL hW hKer κm τ' s t) K

end YMoments

/-! ## 4. Band bridges and band corollaries (target 11) -/

section BandBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ)

/-- **Band bridge of the pin `AzumaSubGN`**: the merged pin is `AzumaSubGNg` at `bandStep2Mat sz E` with the walk coupling
`sz.lam` (`ZfamN = ZfamNg`, `bandStep2_ZfamN`; `SubGaussFormN = SubGaussFormNg`, `Iff.rfl`). -/
theorem bandStep2_AzumaSubGN (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    RBM.Ind.AzumaSubGN sz s t K ↔ AzumaSubGNg (bandStep2Mat sz E) sz.lam s t K := by
  unfold RBM.Ind.AzumaSubGN AzumaSubGNg
  simp only [← bandStep2_ZfamN sz E s t K]
  exact Iff.rfl

/-- **Band corollary of `azumaSubGNg`**: the merged theorem `azumaSubGN` from the generic one at `bandStep2Mat sz E`
(`WalkForm` by `stepDecompGen_walkForm_band`). -/
example (s t : ℕ → ℝ) (K : ℕ → ℕ) : RBM.Ind.AzumaSubGN sz s t K :=
  (bandStep2_AzumaSubGN sz E s t K).2 (azumaSubGNg (bandStep2Mat sz E) (stepDecompGen_walkForm_band sz E) s t K)

/-- **Band corollary of `azumaProxy_subG_ugeng`**: the merged `azumaProxy_subG_ugen` (`AzumaProxyN:980`) from the generic
composition at `bandStep2Mat sz E` (`LoopForm` by `stepDecompGen_loopForm_band`, `QVPropagatedNg` by `qvPropagatedNg`, K1-K4
by `gridRepTailGen_ker_band`, `qvFormN = qvFormNg` by `bandStep2_qvFormN`). -/
example {s t : ℕ → ℝ} {K : ℕ → ℕ} (h : RBM.Ind.AzumaSubGN sz s t K)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (n k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool)
    (τ : PathΩ sz → ℕ) (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
    (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (hG : ∀ ω j, j < τ ω → pathH sz s t K n j ω ∈ G j) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s t K n * ((k : ℝ) * RBM.Ind.qvFormN sz n (E n) (gridTime s t K n (j + 1))
        (gridTime s t K n m) σ M a) ≤ (Q : ℝ)) :
    RBM.Ind.SubGaussStopN sz (E n) σ (gridTime s t K n) τ (fun j ω => RBM.Ind.ZvecN sz E s t K n j σ ω) m a j Q := by
  have hKn : K n ≠ 0 := by omega
  have hw0 : 0 ≤ gridTime s t K n m := azumaProxy2_gridTime_nonneg s t K n (hs0 n) (hst n) m
  have hw1 : gridTime s t K n m < 1 := (azumaProxy2_gridTime_le s t K n (hst n) hm hKn).trans_lt (ht1 n)
  have hL := stepDecompGen_loopForm_band sz E hE
  have hkey := azumaProxy_subG_ugeng ((bandStep2_AzumaSubGN sz E s t K).1 h) hL
    (qvPropagatedNg (bandStep2Mat sz E) E sz.lam hL (fun _ => rfl)) hs0 hst ht1 n k
    (gridRepTailGen_ker_band sz E n (hE n).le) hk σ τ G hτ hG m hm a j hj Q
    (fun M hM hMH => by
      rw [← bandStep2_qvFormN sz E n (hE n).le hw0 hw1]
      exact hQ M hM hMH)
  have hZ : (fun j ω => RBM.Ind.ZvecN sz E s t K n j σ ω) =
      fun j ω => ZvecNg (bandStep2Mat sz E) s t K n j σ ω :=
    funext fun j => funext fun ω => bandStep2_ZvecN sz E s t K n j σ ω
  rw [hZ]
  exact (bandStep2_SubGaussStopN sz E σ _ τ _ m a j Q).2 hkey

/-- **Band corollary of `azumaProxy_pos_gridExitTauNg`** (the exit time of the band walk, `gridExitTauN = gridExitTauNg`, `rfl`). -/
example {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    {G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}
    {ω : PathΩ sz} (hK : 0 < K n) (h0 : pathH sz s v K n 0 ω ∈ G 0) : 0 < gridExitTauN sz s v K n G ω :=
  azumaProxy_pos_gridExitTauNg (Cm := bandStep2Mat sz E) hK h0

/-- **Band corollary of `azumaProxy_Hpath_zerog`**: the merged `azumaProxy_pathH_zero_of_s_zero` (`WalkForm`, `Ψ = 0`). -/
example (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs : s n = 0) (ω : PathΩ sz) : pathH sz s t K n 0 ω = 0 :=
  azumaProxy_Hpath_zerog (stepDecompGen_walkForm_band sz E) s t K n hs ω

/-- **Band corollary of `yMomentsUnifNg`**: the merged `yMomentsUnifN` (`AzumaProxyN2:915`) from the generic uniform moments at
`bandStep2Mat sz E` with the spectral data `κm = √κ/2` (`DecayGen_bandSpec`); the conclusion is converted by
`bandStep2_YMomentBoundsN` and `bandStep2_YvecN`. -/
example (κ τ' : ℝ) (s t : ℕ → ℝ) : RBM.Ind.YMomentsUnifN sz κ τ' E s t := by
  intro hκ hE hs0 hst ht1 hsize hrange k σ
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  obtain ⟨C_P, hC, hev⟩ := yMomentsUnifNg (stepDecompGen_loopForm_band sz E hE2)
    (stepDecompGen_walkForm_band sz E) (fun n => gridRepTailGen_ker_band sz E n (hE2 n).le) (Real.sqrt κ / 2) τ' s t
    (DecayGen_bandSpec sz hκ hE) hs0 hst ht1 hsize hrange k σ
  refine ⟨C_P, hC, fun K hK => ?_⟩
  filter_upwards [hev K hK] with n hn
  obtain ⟨P, hP0, hPN, hY⟩ := hn
  refine ⟨P, hP0, hPN, fun τ hτ => ?_⟩
  have hYeq : (fun j ω => RBM.Ind.YvecN sz E s t K n j σ ω) =
      fun j ω => YvecNg (bandStep2Mat sz E) s t K n j σ ω :=
    funext fun j => funext fun ω => bandStep2_YvecN sz E s t K n j σ ω
  rw [hYeq]
  exact (bandStep2_YMomentBoundsN sz E σ _ τ _ _ _ _).2 (hY τ hτ)

/-- **Band corollary of `yMomentsNg`**: the merged `yMomentsN` (`AzumaProxyN2:992`, the pin `YMomentsN`) from the generic theorem at
`bandStep2Mat sz E`. -/
example (κ τ' : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : RBM.Ind.YMomentsN sz κ τ' E s t K := by
  intro hκ hE hs0 hst ht1 hK hsize hrange k σ
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  obtain ⟨C_P, hC, hev⟩ := yMomentsNg (stepDecompGen_loopForm_band sz E hE2)
    (stepDecompGen_walkForm_band sz E) (fun n => gridRepTailGen_ker_band sz E n (hE2 n).le) (Real.sqrt κ / 2) τ' s t K
    (DecayGen_bandSpec sz hκ hE) hs0 hst ht1 hK hsize hrange k σ
  refine ⟨C_P, hC, ?_⟩
  filter_upwards [hev] with n hn
  obtain ⟨P, hP0, hPN, hY⟩ := hn
  refine ⟨P, hP0, hPN, fun τ hτ => ?_⟩
  have hYeq : (fun j ω => RBM.Ind.YvecN sz E s t K n j σ ω) =
      fun j ω => YvecNg (bandStep2Mat sz E) s t K n j σ ω :=
    funext fun j => funext fun ω => bandStep2_YvecN sz E s t K n j σ ω
  rw [hYeq]
  exact (bandStep2_YMomentBoundsN sz E σ _ τ _ _ _ _).2 (hY τ hτ)

end BandBridge

/-! ## 5. Compiled nonempty instances at the band carrier (`d = 3`)

The sizes are the merged `sz0` (`L = 4 (n+1)`, `W = (2(n+1))^5`; at `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), the carrier is
`bandStep2Mat sz0 Einst` with `Einst ≡ 1/2`, the grid is that of the band instance of `Induction/AzumaProxyN.lean:1110-1260` and
`Induction/AzumaProxyN2.lean:1268-1405` (`s ≡ 0`, `t ≡ 1/32`, `K ≡ 4`, `Δ = 1/128`), the loop length is `k = 3` and the signs
`σ = (+,-,+)`.  The classes `LoopForm`, `WalkForm` (`lam' = sz0.lam`, `Ψ = 0`), the kernel class `GridRepTailGen_Ker`, `QVPropagatedNg`
and the spectral data `DecayGen_Spec` (`κm = 1/2`) are discharged by the band lemmas.  The initial membership of target 9 is the
band lemma `zero_mem_goodSetN_instance_grid`; the majorant `hQ` of `azumaProxy_subG_goodExitg` on the good set (Step 3, other
gates) stays a hypothesis of its example. -/

section Instances

namespace AzumaProxyGenCheck

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst RBM.Ind.AzumaProxyNInst

private abbrev Cm0 : Step2Mat sz0 := bandStep2Mat sz0 Einst

private theorem hL0 : StepDecompGen_LoopForm Cm0 Einst := stepDecompGen_loopForm_band sz0 Einst Einst_abs_lt
private theorem hW0 : StepDecompGen_WalkForm Cm0 sz0.lam (fun _ => 0) := stepDecompGen_walkForm_band sz0 Einst
private theorem hKer0 : ∀ n, GridRepTailGen_Ker Cm0.toFlowFM n := fun n =>
  gridRepTailGen_ker_band sz0 Einst n (Einst_abs_lt n).le
private theorem hQV0 : QVPropagatedNg Cm0 sz0.lam := qvPropagatedNg Cm0 Einst sz0.lam hL0 (fun _ => rfl)
private theorem hspec0 : DecayGen_Spec Cm0.toFlowFM (Real.sqrt 1 / 2) :=
  DecayGen_bandSpec sz0 (E := Einst) (κ := 1) one_pos (fun n => by norm_num [Einst])

/-- `RangeCond` at the instance: `N^{-1+1/2} ≤ 1 - 1/32` for `N ≥ 4` (as `AzumaProxyN2Inst`, restated). -/
private theorem rangeCond_vg : sz0.RangeCond (1 / 2) vg := by
  filter_upwards [sz0_tendsto.eventually_ge_atTop (4 : ℝ)] with n hn
  have h4 : (0 : ℝ) < 4 := by norm_num
  have h := Real.rpow_le_rpow_of_nonpos h4 hn (show (-1 + (1 / 2 : ℝ)) ≤ 0 by norm_num)
  have h2 : (4 : ℝ) ^ (-1 + (1 / 2 : ℝ)) = 1 / 2 := by
    rw [show (-1 + (1 / 2 : ℝ)) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h3 : (1 : ℝ) - vg n = 31 / 32 := by norm_num [vg]
  rw [h3]
  linarith

private theorem Kg_ne_zero : ∀ n, Kg n ≠ 0 := fun n => by simp [Kg]

private theorem gridStep_pos (n : ℕ) : 0 < gridStep sInst vg Kg n := by
  unfold gridStep
  exact div_pos (by norm_num [vg, sInst]) (Nat.cast_pos.2 (Nat.pos_of_ne_zero (Kg_ne_zero n)))

/-- The data are nondegenerate: `L = 4`, `W = 32`, `N = 2097152`, `K = 4`, `Δ = 1/128`, `u_1 = 1/128`, `u_4 = 1/32`. -/
example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ Kg 0 = 4 ∧ gridStep sInst vg Kg 0 = 1 / 128 :=
  ⟨sz0_values.1, sz0_values.2.1, sz0_values.2.2.1, rfl, grid_data.1⟩

/-- **Target 8, `azumaSubGNg`** at the data: the family `Φ_b = 𝓛_{u_1,(+,-,+),b}` (`phi3`, in the test class), the propagator
weights `κ = kap3 m a`, the stopping time `τ ≡ Kg 0` (`{j < τ}` is the whole space at `j = 0`), the sets `G 0 = {0}` (the
carrier walk starts at `Ψ 0 = 0`: `azumaProxy_Hpath_zerog`) and `G j = {Hermitian}`, and `Q` the exact variance form at `M = 0`;
no hypothesis is open.  The proxy is positive for `m = 1`, `a = (0,0,0)` (`qProxy3_pos`, the last example). -/
theorem azumaSubGNg_instance (m : ℕ) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    SubGaussFormNg Cm0 0 (fun _ => Kg 0) (fun ω => ∑ b, kap3 m a b * ZfamNg Cm0 sInst vg Kg 0 0 phi3 ω b) (qProxy3 m a) := by
  refine azumaSubGNg Cm0 hW0 sInst vg Kg 0 phi3 phi3_hermTestFun (kap3 m a) (fun _ => Kg 0)
    (fun j M => M.IsHermitian ∧ (j = 0 → M = 0)) (fun j => MeasurableSet.const _)
    (fun ω j hj => ⟨pathH_isHermitian sz0 sInst vg Kg 0 j ω, fun hj0 => ?_⟩) 0 (qProxy3 m a) (fun M hM _ => ?_)
  · subst hj0
    exact azumaProxy_Hpath_zerog hW0 sInst vg Kg 0 rfl ω
  · rw [hM.2 rfl]
    exact Real.le_coe_toNNReal _

example : 0 < qProxy3 1 b0 := qProxy3_pos

/-- **Target 8, `azumaProxy_Hpath_zerog`** at the data (`s ≡ 0`): the carrier walk starts at `Ψ 0 = 0`. -/
example (ω : PathΩ sz0) : Cm0.Hpath sInst vg Kg 0 0 ω = 0 := azumaProxy_Hpath_zerog hW0 sInst vg Kg 0 rfl ω

/-- **Target 8, `azumaProxy_pos_gridExitTauNg`** at the data: the exit time from the Hermitian matrices is positive. -/
example (ω : PathΩ sz0) : 0 < gridExitTauNg Cm0 sInst vg Kg 0 (fun _ => {H | H.IsHermitian}) ω :=
  azumaProxy_pos_gridExitTauNg (by norm_num [Kg]) (pathH_isHermitian sz0 sInst vg Kg 0 0 ω)

/-- The initial state `H_0 = 0` is in the carrier good set at `u_0 = 0` for the levels `Γ = 4`, `Λ = 3`, `Φ = 1`, `τ' = 1/2`,
`D' = 1`, `k = 3`: the **band discharge of the inline hypothesis of target 9** (`zero_mem_goodSetN_instance_grid`,
`bandStep2_GoodSetN`).  There is no BA discharge in this file (owed to T4-BA). -/
private theorem h0_inst (ω : PathΩ sz0) :
    GoodSetNg Cm0 0 (gridTime sInst vg Kg 0 0) 3 (Γ4 0) (Λ3 0) (Φ1 0) (1 / 2) 1 (Cm0.Hpath sInst vg Kg 0 0 ω) := by
  rw [azumaProxy_Hpath_zerog hW0 sInst vg Kg 0 rfl ω]
  exact (bandStep2_GoodSetN sz0 Einst 0 _ 3 _ _ _ (1 / 2) 1 0).1 zero_mem_goodSetN_instance_grid

/-- **Target 9, `azumaProxy_pos_goodExitTauNg`** at the data: with the initial membership discharged by the band lemma, the exit
time from the good set is positive at every sample, so `{0 < τ}` is the whole space and `G_0 = GoodSetNg ∩ {0}` is nonempty. -/
example (ω : PathΩ sz0) : 0 < goodExitTauNg Cm0 sInst vg Kg 3 Γ4 Λ3 Φ1 (1 / 2) 1 0 ω :=
  azumaProxy_pos_goodExitTauNg 3 Γ4 Λ3 Φ1 (1 / 2) 1 (by norm_num [Kg]) (h0_inst ω)

/-- **Target 8, `azumaProxy_subG_ugeng`** at the data (`n = 0`, `j = 0`, every `m ∈ [1, 4]`, every label `a`): `G 0 = {0}`,
`τ ≡ 4`, and `Q` is the majorant `Δ · 3 · qvFormNg` at the only point `M = 0` of `G 0`; every hypothesis is discharged. -/
example (m : ℕ) (hm : m ≤ Kg 0) (hj : 0 < m) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    SubGaussStopNg Cm0 sig3 (gridTime sInst vg Kg 0) (fun _ => Kg 0)
      (fun j ω => ZvecNg Cm0 sInst vg Kg 0 j sig3 ω) m a 0
      (Real.toNNReal (gridStep sInst vg Kg 0 * (((3 : ℕ) : ℝ) *
        qvFormNg Cm0 0 (gridTime sInst vg Kg 0 1) (gridTime sInst vg Kg 0 m) sig3 0 a))) :=
  azumaProxy_subG_ugeng (azumaSubGNg Cm0 hW0 sInst vg Kg) hL0 hQV0 sInst_nonneg sInst_le_vg vg_lt_one 0 3 (hKer0 0)
    (by norm_num) sig3 (fun _ => Kg 0) (fun j M => M.IsHermitian ∧ (j = 0 → M = 0)) (fun j => MeasurableSet.const _)
    (fun ω j hj => ⟨pathH_isHermitian sz0 sInst vg Kg 0 j ω, fun hj0 => by
      subst hj0
      exact azumaProxy_Hpath_zerog hW0 sInst vg Kg 0 rfl ω⟩) m hm a 0 hj _
    (fun M hM _ => by
      rw [hM.2 rfl]
      exact Real.le_coe_toNNReal _)

/-- **Target 8, `azumaProxy_subG_goodExitg`** at the data (`τ = goodExitTauNg`, `G j = GoodSetNg …`, any levels): all hypotheses
are discharged but the deterministic majorant `hQ` of `Δ · k · qvFormNg` on the good set (the output of the Step 3 tickets,
other gates' pin). -/
example (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (hm : m ≤ Kg 0) (hj : 0 < m) (a : Fin 3 → Zd 3 (sz0.L 0)) (Q : ℝ≥0)
    (hQ : ∀ M, GoodSetNg Cm0 0 (gridTime sInst vg Kg 0 0) 3 (Γ 0) (Λ 0) (Φ 0) τ' D' M → M.IsHermitian →
      gridStep sInst vg Kg 0 * (((3 : ℕ) : ℝ) * qvFormNg Cm0 0 (gridTime sInst vg Kg 0 1)
        (gridTime sInst vg Kg 0 m) sig3 M a) ≤ (Q : ℝ)) :
    SubGaussStopNg Cm0 sig3 (gridTime sInst vg Kg 0) (goodExitTauNg Cm0 sInst vg Kg 3 Γ Λ Φ τ' D' 0)
      (fun j ω => ZvecNg Cm0 sInst vg Kg 0 j sig3 ω) m a 0 Q :=
  azumaProxy_subG_goodExitg (azumaSubGNg Cm0 hW0 sInst vg Kg) hL0 hW0 hQV0 sInst_nonneg sInst_le_vg vg_lt_one 0 3
    (hKer0 0) (by norm_num) sig3 Γ Λ Φ τ' D' m hm a 0 hj Q hQ

/-- **Target 10, the public forms** at the data. -/
example : 0 < Real.sqrt 1 / 2 := AzumaProxyN_c0_pos_pubg hspec0

example : (Cm0.eta 0 (1 / 4))⁻¹ ≤ (4 : ℝ) ^ (1 - (1 / 2 : ℝ)) / (Real.sqrt 1 / 2) :=
  AzumaProxyN_eta_inv_le_pubg hspec0 0 (u := 1 / 4) (t := 1 / 2) (τ' := 1 / 2) (N := 4) (by norm_num) (by norm_num) (by
    rw [show (-1 + (1 / 2 : ℝ)) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num)

example : ∑ b : Fin 3 → Zd 3 (sz0.L 0), ‖∏ i : Fin 3, Step2Gen_uKer Cm0.toFlowFM 0 (sig3 i) (sig3 (finRotate 3 i))
      (1 / 128) (1 / 32) ((fun _ => (0 : Zd 3 (sz0.L 0))) i) (b i)‖ ≤ (1 + (1 - (1 / 32 : ℝ))⁻¹) ^ 3 :=
  AzumaProxyN_rowsum_UN_pubg (hKer0 0) sig3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ => 0)

/-- **Target 10, `yMomentsUnifNg`** at the data (`k = 3`, every `σ`): all hypotheses are discharged; `C_P` comes before the grid
`Kg`, and the conclusion is applied at a concrete `n` (from the eventual filter) with the stopping time `τ ≡ K n` and the window
`Δ > 0`. -/
theorem yMomentsUnifNg_instance (σ : Fin 3 → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsNg Cm0 σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => YvecNg Cm0 sInst vg Kg n j σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsUnifNg hL0 hW0 hKer0 (Real.sqrt 1 / 2) (1 / 2) sInst vg hspec0 sInst_nonneg
    sInst_le_vg vg_lt_one sz0_tendsto rangeCond_vg 3 σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := (hev Kg Kg_ne_zero).exists
  exact ⟨C_P, hC, n, P, hP0, hPN, gridStep_pos n, hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩

/-- **Target 10, `yMomentsNg_of_unif`** at the data. -/
example (σ : Fin 3 → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsNg Cm0 σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => YvecNg Cm0 sInst vg Kg n j σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsNg_of_unif (yMomentsUnifNg hL0 hW0 hKer0 (Real.sqrt 1 / 2) (1 / 2) sInst vg) Kg
    hspec0 sInst_nonneg sInst_le_vg vg_lt_one Kg_ne_zero sz0_tendsto rangeCond_vg 3 σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := hev.exists
  exact ⟨C_P, hC, n, P, hP0, hPN, gridStep_pos n, hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩

/-- **Target 10, `yMomentsNg`** at the data (`k = 3`, every `σ`): applied at a concrete `n`; at `j = 0`, `m = 1` and every label `b`
the real and imaginary parts of the stopped propagated increment have fourth moment at most `Δ⁴ P²`. -/
example (σ : Fin 3 → Bool) :
    ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ 0 < gridStep sInst vg Kg n ∧
      YMomentBoundsNg Cm0 σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => YvecNg Cm0 sInst vg Kg n j σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) ∧
      ∀ b : Fin 3 → Zd 3 (sz0.L n),
        ∫ ω, (stoppedEdgeNg Cm0 σ (gridTime sInst vg Kg n) (gridTime sInst vg Kg n 1) (fun _ => Kg n)
            (fun j ω => YvecNg Cm0 sInst vg Kg n j σ ω) b 0 ω).re ^ 4 ∂Cm0.Pp
          ≤ gridStep sInst vg Kg n ^ 4 * P ^ 2 ∧
        ∫ ω, (stoppedEdgeNg Cm0 σ (gridTime sInst vg Kg n) (gridTime sInst vg Kg n 1) (fun _ => Kg n)
            (fun j ω => YvecNg Cm0 sInst vg Kg n j σ ω) b 0 ω).im ^ 4 ∂Cm0.Pp
          ≤ gridStep sInst vg Kg n ^ 4 * P ^ 2 := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsNg hL0 hW0 hKer0 (Real.sqrt 1 / 2) (1 / 2) sInst vg Kg hspec0 sInst_nonneg
    sInst_le_vg vg_lt_one Kg_ne_zero sz0_tendsto rangeCond_vg 3 σ
  obtain ⟨n, P, hP0, -, hτ⟩ := hev.exists
  have hY := hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)
  have hK1 : 1 ≤ Kg n := Nat.one_le_iff_ne_zero.2 (Kg_ne_zero n)
  refine ⟨n, P, hP0, gridStep_pos n, hY, fun b => ?_⟩
  have h := hY.2 1 hK1 b 0 Nat.zero_lt_one
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- **Target 10, `AzumaProxyN_YfieldsWg`** at `n = 0`, `j = 0` (`j + 1 = 1 ≤ Kg 0 = 4`), `k = 3`, `σ = (+,-,+)`, for every weight vector
`κ` (with `S = Σ_c ‖κ_c‖`), the stopping time `τ ≡ Kg 0` and the constants `C₂ = k (k + 1) N η^{-(k+2)}` (the Hermitian second
derivative of the loops seen from the shifted walk) and `P = 2000 (S C₂)² N⁸`: every hypothesis is discharged. -/
theorem yfieldsWg_instance (κ : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
    let C2 : ℝ := ((3 * (3 + 1) : ℕ) : ℝ) * (sz0.size 0 : ℝ) * (Cm0.eta 0 (gridTime sInst vg Kg 0 1))⁻¹ ^ (3 + 2)
    let P : ℝ := 2000 * ((∑ c, ‖κ c‖) * C2) ^ 2 * (sz0.size 0 : ℝ) ^ 8
    Cm0.Pp[fun ω => (AzumaProxyN_stopWg Cm0 sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).re | filt sz0 0] =ᵐ[Cm0.Pp] 0 ∧
    Cm0.Pp[fun ω => (AzumaProxyN_stopWg Cm0 sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).im | filt sz0 0] =ᵐ[Cm0.Pp] 0 ∧
    Integrable (fun ω => (AzumaProxyN_stopWg Cm0 sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).re ^ 4) Cm0.Pp ∧
    Integrable (fun ω => (AzumaProxyN_stopWg Cm0 sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).im ^ 4) Cm0.Pp ∧
    Cm0.Pp[fun ω => (AzumaProxyN_stopWg Cm0 sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).re ^ 2 | filt sz0 0]
      ≤ᵐ[Cm0.Pp] (fun _ => gridStep sInst vg Kg 0 ^ 2 * P) ∧
    Cm0.Pp[fun ω => (AzumaProxyN_stopWg Cm0 sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).im ^ 2 | filt sz0 0]
      ≤ᵐ[Cm0.Pp] (fun _ => gridStep sInst vg Kg 0 ^ 2 * P) ∧
    ∫ ω, (AzumaProxyN_stopWg Cm0 sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).re ^ 4 ∂Cm0.Pp
      ≤ gridStep sInst vg Kg 0 ^ 4 * P ^ 2 ∧
    ∫ ω, (AzumaProxyN_stopWg Cm0 sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).im ^ 4 ∂Cm0.Pp
      ≤ gridStep sInst vg Kg 0 ^ 4 * P ^ 2 := by
  intro C2 P
  have hu : gridTime sInst vg Kg 0 1 = 1 / 128 := grid_data.2.2.1
  have hu1 : gridTime sInst vg Kg 0 1 < 1 := by rw [hu]; norm_num
  have hpos : 0 < Cm0.eta 0 (gridTime sInst vg Kg 0 1) := by
    rw [hspec0.2.2 0]
    exact mul_pos (by linarith) (lt_of_lt_of_le hspec0.1 (hspec0.2.1 0))
  refine AzumaProxyN_YfieldsWg hL0 hW0 sInst vg Kg 0 0 (sInst_le_vg 0) (vg_lt_one 0) (by simp [Kg]) sig3 κ
    (Smax := ∑ c, ‖κ c‖) (C2 := C2) (P := P) (Finset.sum_nonneg fun c _ => norm_nonneg _) (by positivity) le_rfl
    (fun a M y hM hy => ?_) le_rfl (fun _ => Kg 0) (fun j => MeasurableSet.const _)
  exact (StepDecompGen_loopFamShift_hermTestFun hL0 hW0 sInst vg Kg 0 0 (sInst_le_vg 0) (vg_lt_one 0) (by simp [Kg])
    sig3 a).2 M y hM hy

end AzumaProxyGenCheck

end Instances

end RBM.BA

end
