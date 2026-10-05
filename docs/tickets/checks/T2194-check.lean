/-
Release check for T2194 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2, §57, §62 (4)).
S3-14 (ST-3, alternating chain, first ticket): the martingale part of the `𝒬`-process with the variance proxy
`(𝒬_v ⊗ 𝒬̄_v)(𝓔 ⊗ 𝓔)`, port of RBM2D `Induction/AltProxyQ.lean` (`c9a24cf`) to `d ≥ 3` in the new file
`RBM3D/Induction/QProxy.lean`.  Every statement is generic in the stopping time / set family (`τ`, `G`) and in
the mollifier family `ϑ`; no statement carries a level of the current length (DECISIONS §62 (4)).
Section 1: the merged names the ticket cites.  Section 2: pinned vocabulary in `RBM.Ind.T2194Check` (T2194
defines it in `RBM.Ind` verbatim).  Section 3: pinned statements as `Prop`s (T2194 proves each with this
statement, in `RBM.Ind`, under the name in its docstring).  The four bounds of targets 4-6 (two-copy `lem_+Q`,
the EK-4 pair kernel, `qvFormQN_le_of_bounds`, `qvFormQN_le_of_goodSetN`) are NOT pinned here: their
mathematical statements are in the ticket and the preflight fixes their Lean shape.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2194-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- the `𝒬`-process on the grid (`Induction/QGridA`, 549a62d; `Induction/QGridB`, 3013163)
#check @RBM.Ind.aTrueQN
#check @RBM.Ind.dGridQN
#check @RBM.Ind.aFrozQN
#check @RBM.Ind.martIncQN
#check @RBM.Ind.QGridA_condExp_aTrueQN
#check @RBM.Ind.gridDriftQN
#check @RBM.Ind.stoppedDuhamelQN
#check @RBM.Ind.QGridACheck.sigma4
#check @RBM.Ind.QGridACheck.sigma4_alternating
#check @RBM.Ind.QGridACheck.moll
#check @RBM.Ind.sum_weighted_qErrQN_le
-- the Step 3-4 vocabulary (`Induction/Step34Pins`, fc76526)
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.Gauss.Sizes.STAlternating
-- `𝒫 ∘ 𝒬 = 0`, the mollifier (`Induction/QopAlgebra`, 6b2494e) and `lem_+Q` (`Induction/QopNorm`, eb6d67a)
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_Qop
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_of_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props
#check @RBM.Gauss.Sizes.stMollifierEx_holds
#check @RBM.Gauss.Sizes.stQopNorm_holds
#check @RBM.Gauss.Sizes.stQop_sub_fastDecay
-- EK-4 and its inputs (`Evolution/Pins`, `Evolution/SumDecayZero`, d9de66f; `Propagator/*`)
#check @RBM.EKsgn
#check @RBM.EKFastDecay
#check @RBM.EKSumZero
#check @RBM.EKSumNdecay
#check @RBM.EKSumDecay2
#check @RBM.ekSumNdecay_holds
#check @RBM.ekSumDecay2_holds
#check @RBM.prop5Decay_holds
#check @RBM.prop5Short_holds
#check @RBM.prop6Diff1_holds
#check @RBM.UN
#check @RBM.uKer
#check @RBM.cycProd
#check @RBM.norm_UN_apply_le
#check @RBM.mE
#check @RBM.mSigma
-- the good set and the exit times (`Induction/GridGoodN`, 2f246bf)
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.measurableGoodSetN
#check @RBM.Path.gridExitTauN
#check @RBM.Path.goodExitTauN
#check @RBM.Path.mem_of_lt_gridExitTauN
#check @RBM.Path.gridExitTauN_measurableSet
#check @RBM.Path.goodExitMeasN
-- the loop vocabulary (`Induction/Step2Defs`, 86124dc; `Induction/DecayLoopA`, 6179d8c)
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STdiamInf
-- (D4)-level source (`Induction/SEforLn2`, ae259a6)
#check @RBM.Gauss.Sizes.stSEforLn_holds
-- the assembled bound and its inputs (`Induction/GridAssemblyN`, 686cf71; `Induction/StepDecompN`, 45ca385;
-- `Induction/GridDuhamelN`, 2ebee73)
#check @RBM.Ind.qvFormN
#check @RBM.Ind.AzumaSubGN
#check @RBM.Ind.YMomentBoundsN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.gridAsm_stronglyMeasurable_YvecN
#check @RBM.Ind.loopFamN
#check @RBM.Ind.ZfamN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.YvecN
#check @RBM.Ind.stoppedEdgeN
#check @RBM.Ind.SubGaussFormN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.Ugen
#check @RBM.Ind.AvecN
#check @RBM.Ind.martIncN
-- Azuma proxies and `Y` moments (`Induction/AzumaProxyN`, 43ab861; `Induction/AzumaProxyN2`, 88183f4)
#check @RBM.Ind.azumaSubGN
#check @RBM.Ind.azumaProxy_subG_ugen
#check @RBM.Ind.azumaProxy_subG_goodExit
#check @RBM.Ind.azumaProxy_pos_gridExitTauN
#check @RBM.Ind.zero_mem_goodSetN_of_levels
#check @RBM.Ind.YMomentsUnifN
#check @RBM.Ind.yMomentsUnifN
#check @RBM.Ind.AzumaProxyN_stopW
#check @RBM.Ind.AzumaProxyN_YfieldsW
-- the variance identity (`Induction/QVN`, e56d95c) and the test class (`Induction/LoopC2N`, 14137ce)
#check @RBM.Ind.QVPropagatedN
#check @RBM.Ind.qvPropagatedN
#check @RBM.Ind.loopDerivN
#check @RBM.Ind.HermTestFunLoopN
#check @RBM.Ind.hermTestFunLoopN
-- the non-alternating analogues (patterns; `Induction/NQGood1`, 691566a; `Induction/NQGood2`, cc96b69)
#check @RBM.Ind.UgenPairN
#check @RBM.Ind.nqGood1_UgenPairN_eq_Ugen
#check @RBM.Ind.qvFormN_eq_re_UgenPairN
#check @RBM.Ind.nqGood1C
#check @RBM.Ind.hker_of_case1N
#check @RBM.Ind.nqGood1_mE_im_ge
#check @RBM.Ind.nqGood1_ugenPairN_le_of_bounds
#check @RBM.Ind.nqGood1_qvFormN_le_of_bounds
#check @RBM.Ind.qvFormN_le_of_goodSetN
#check @RBM.Ind.nqGood1_ellT_mono
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.norm_STeeM_shiftN_le
#check @RBM.Ind.NQGood1Inst.zero_mem_goodSetN_inst_grid
#check @RBM.Ind.qvBdNonAltN
#check @RBM.Ind.cQVNonAltN
#check @RBM.Ind.qvFormN_le_of_goodSetN_shiftN
#check @RBM.Ind.hQ_nonAltN
#check @RBM.Ind.subGaussStop_nonAltN

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind.T2194Check

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Green RBM.Ind

/-! ## 2. Pinned vocabulary (T2194 defines these in `RBM.Ind`, verbatim) -/

/-- `(𝒬_t ⊗ 𝒬̄_t) 𝒜 = Σ_{c,c'} Qmat_t(b,c) conj(Qmat_t(b',c')) 𝒜(c,c')` (RBM2D `qqTensorN`, `AltProxyQ:93`),
for the merged `STQop` with an abstract mollifier family `ϑ`, tensors of `m + 1` indices. -/
def qqTensorN {d L m : ℕ} [NeZero L] (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (A : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ) (b b' : Fin (m + 1) → Zd d L) : ℂ :=
  STQop (d := d) ϑ t
    (fun c => starRingEnd ℂ (STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (A c c')) b')) b

/-- The merged `qvFormN` (`GridAssemblyN.lean:105`) with `𝓔 ⊗ 𝓔` (`STeeM`) replaced by
`(𝒬_v ⊗ 𝒬̄_v)(𝓔 ⊗ 𝓔)` (RBM2D `qvFormQN`, `AltProxyQ:98`). -/
noncomputable def qvFormQN {d : ℕ} (sz : Sizes d) (n : ℕ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (E v w : ℝ) (σ : Fin (m + 1) → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Fin (m + 1) → Zd d (sz.L n)) : ℝ :=
  (∑ b : Fin (m + 1) → Zd d (sz.L n), ∑ b' : Fin (m + 1) → Zd d (sz.L n),
    (∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) v w
        (a i) (b i)) *
      (starRingEnd ℂ) (∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n)
        (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b' i)) *
      qqTensorN ϑ v (fun c c' => sz.STeeM n E v M σ c c') b b').re

/-- The first-chaos part of the `𝒬`-martingale increment, `𝒬_{u_{j+1}} ZvecN` (RBM2D `zVecQN`, `AltProxyQ:107`). -/
noncomputable def zVecQN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n (j + 1)) (ZvecN sz E s t K n j σ ω)

/-- The second-order part, `𝒬_{u_{j+1}} YvecN` (RBM2D `yVecQN`, `AltProxyQ:112`). -/
noncomputable def yVecQN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n (j + 1)) (YvecN sz E s t K n j σ ω)

/-! ## 3. Pinned statements (T2194 proves each with exactly this statement) -/

/-- Target 2 (`RBM.Ind.martIncQN_ae_eq`): a.e. `martIncQN_j = zVecQN_j + yVecQN_j` (any `ϑ`). -/
def T2194_martIncQN_ae_eq : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ), |E n| < 2 →
    gridTime s t K n (j + 1) < 1 →
    ∀ {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
      (a : Fin (m + 1) → Zd d (sz.L n)),
      ∀ᵐ ω ∂(pathP sz), martIncQN sz E s t K n ϑ σ j ω a =
        zVecQN sz E s t K n j ϑ σ ω a + yVecQN sz E s t K n j ϑ σ ω a

/-- Target 3a (`RBM.Ind.qv_at_propagatorQ`): the merged `qvPropagatedN` at the transposed weights
`κ'_c = Σ_b κ_b Qmat_u(b,c)` (any `ϑ`). -/
def T2194_qv_at_propagatorQ : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u w : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
    ∀ (m : ℕ), 1 ≤ m → ∀ (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
      (a : Fin (m + 1) → Zd d (sz.L n)),
      ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
          ‖∑ b : Fin (m + 1) → Zd d (sz.L n),
            (∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) u w
              (a i) (b i)) *
            STQop (d := d) ϑ u (fun b'' => loopDerivN d (sz.L n) (sz.W n) E u M
              (coordinateMatrix d (sz.L n) (sz.W n) c) σ b'') b‖ ^ 2 ≤
        ((m + 1 : ℕ) : ℝ) * qvFormQN sz n ϑ E u w σ M a

/-- Target 3b (`RBM.Ind.qqTensorN_sumZero`): `(𝒬_t ⊗ 𝒬̄_t) 𝒜` is sum-zero in each block (`𝒫 ∘ 𝒬_t = 0`,
merged `QopAlgebra_Psum_Qop`), for every `𝒜`; RBM2D `doubleSumZero_qqTensorN` in the form EK-4 consumes. -/
def T2194_qqTensorN_sumZero : Prop :=
  ∀ {d L m : ℕ} [NeZero L] (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ),
    (∀ a₁ : Zd d L, ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ t a = 1) →
    ∀ A : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ,
      (∀ b' : Fin (m + 1) → Zd d L, EKSumZero (fun b => qqTensorN ϑ t A b b')) ∧
        (∀ b : Fin (m + 1) → Zd d L, EKSumZero (fun b' => qqTensorN ϑ t A b b'))

/-- Target 7a (`RBM.Ind.azumaSubGQ_ugenN`): the merged `azumaProxy_subG_ugen` for `zVecQN`, `qvFormQN`,
generic in the stopping family `τ` and the sets `G` (no `AzumaSubGN` hypothesis: `azumaSubGN` is merged). -/
def T2194_azumaSubGQ_ugenN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s t : ℕ → ℝ} {K : ℕ → ℕ},
    (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    ∀ (n m : ℕ), 1 ≤ m → ∀ (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
      (τ : PathΩ sz → ℕ)
      (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)),
      (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
      (∀ ω j, j < τ ω → pathH sz s t K n j ω ∈ G j) →
      ∀ (p : ℕ), p ≤ K n → ∀ (a : Fin (m + 1) → Zd d (sz.L n)) (j : ℕ), j < p → ∀ (Q : ℝ≥0),
      (∀ M ∈ G j, M.IsHermitian →
        gridStep s t K n * (((m + 1 : ℕ) : ℝ) * qvFormQN sz n ϑ (E n) (gridTime s t K n (j + 1))
          (gridTime s t K n p) σ M a) ≤ (Q : ℝ)) →
      SubGaussStopN sz (E n) σ (gridTime s t K n) τ (fun j ω => zVecQN sz E s t K n j ϑ σ ω) p a j Q

/-- Target 7b (`RBM.Ind.azumaSubGQ_gridExitN`): 7a at `τ = gridExitTauN … G` for ANY measurable family `G`
(replaces RBM2D `azumaSubGQ_goodExit`, which hard-wires `goodExitTauN` at one level `Φ`; DECISIONS §62 (4)). -/
def T2194_azumaSubGQ_gridExitN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ},
    (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) →
    ∀ (n m : ℕ), 1 ≤ m → ∀ (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
      (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)),
      (∀ j, MeasurableSet (G j)) →
      ∀ (p : ℕ), p ≤ K n → ∀ (a : Fin (m + 1) → Zd d (sz.L n)) (j : ℕ), j < p → ∀ (Q : ℝ≥0),
      (∀ M ∈ G j, M.IsHermitian →
        gridStep s v K n * (((m + 1 : ℕ) : ℝ) * qvFormQN sz n ϑ (E n) (gridTime s v K n (j + 1))
          (gridTime s v K n p) σ M a) ≤ (Q : ℝ)) →
      SubGaussStopN sz (E n) σ (gridTime s v K n) (gridExitTauN sz s v K n G)
        (fun j ω => zVecQN sz E s v K n j ϑ σ ω) p a j Q

/-- Target 8 (`RBM.Ind.yMomentsQUnifN`): the `𝒬`-analogue of the merged `YMomentsUnifN`
(`AzumaProxyN2.lean:894`) for a mollifier family `ϑ n` with constants `C, c`; `C_P` before the grid `K`. -/
def T2194_yMomentsQUnifN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ),
    0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.SizeTendsto → sz.RangeCond τ' t →
    ∀ (m : ℕ) (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), 0 < C → 0 ≤ c →
      (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → ∀ σ : Fin (m + 1) → Bool,
      ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
        ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
          ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
            YMomentBoundsN sz (E n) σ (gridTime s t K n) τ (K n)
              (fun j ω => yVecQN sz E s t K n j (ϑ n) σ ω)
              (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

end RBM.Ind.T2194Check
