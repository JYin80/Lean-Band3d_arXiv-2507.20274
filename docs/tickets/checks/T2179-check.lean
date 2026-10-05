/-
Release check for T2179 (dispatcher V1, Mon Oct  5 06:00 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2).
S3-11: the term budgets of the non-alternating assembled bound at the `d ≥ 3` data of S3-10b
(`Induction/NQGood2`, T2167 cc96b69).  Section 1: the merged names it builds on (NQGood2, NQGood1,
GridAssemblyN, GridEnvelopeN, GridDriftN, the scale and grid facts, the instance data) and the downstream
pins.  Section 2: the pinned vocabulary (four definitions), in namespace `RBM.Ind.T2179Check` here; T2179
defines it in `RBM.Ind` verbatim.  Section 3: the pinned statement of `budgetNonAltN` as a `Prop`.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2179-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- S3-10b (`Induction/NQGood2`, T2167)
#check @RBM.Ind.nonAltClsN
#check @RBM.Ind.kappaNonAltN
#check @RBM.Ind.epsNonAltN
#check @RBM.Ind.dDriftNonAltN
#check @RBM.Ind.qvBdNonAltN
#check @RBM.Ind.cQVNonAltN
#check @RBM.Ind.nqGood2_ratio_mul_Bctl_le
#check @RBM.Ind.kappaNonAltN_mul_Bctl_pow_le
#check @RBM.Ind.kappaNonAltN_succ_mul_Bctl_pow_le
#check @RBM.Ind.nonAlt_hκ0N
#check @RBM.Ind.nonAlt_hε0N
#check @RBM.Ind.nonAlt_hdDrift0N
#check @RBM.Ind.qvBdNonAltN_pos
#check @RBM.Ind.cQVNonAltN_sum_pos
#check @RBM.Ind.NQGood2Inst.gridTime_inst
#check @RBM.Ind.NQGood2Inst.tau0
#check @RBM.Ind.NQGood2Inst.delta_shift_ok
#check @RBM.Ind.NQGood2Inst.gridAssemblyHyp_instance
-- S3-10a (`Induction/NQGood1`)
#check @RBM.Ind.nqGood1C
#check @RBM.Ind.nqGood1C_pos
#check @RBM.Ind.NQGood1Inst.aFar
-- assembly, envelope, step error
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.assembledN
#check @RBM.Ind.sum_gridStep_div_etaT_le
#check @RBM.Ind.SumWeightedStepErrN_Stmt
#check @RBM.Ind.sum_weighted_stepErrN_le
#check @RBM.Ind.stepErrN
#check @RBM.Ind.kStepC
#check @RBM.Ind.uStepC
#check @RBM.Path.envConst
-- scales, times, sizes
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Green.etaT_le_of_le
#check @RBM.mE
#check @RBM.mE_im_pos
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.gridTime_last
#check @RBM.Gauss.Sizes.ST_gridTime_zero
#check @RBM.Gauss.Sizes.ST_gridTime_mono
#check @RBM.Gauss.Sizes.ST_gridStep_nonneg
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.GridGoodNInst.vg
#check @RBM.Gauss.GridGoodNInst.Kg
#check @RBM.Ind.AzumaProxyNInst.Einst
#check @RBM.Ind.AzumaProxyNInst.Γ4
#check @RBM.Ind.AzumaProxyNInst.Λ3
#check @RBM.Ind.AzumaProxyNInst.Φ1
#check @RBM.Ind.GridEnvelopeNCheck.E1
#check @RBM.Ind.GridEnvelopeNCheck.Kc
#check @RBM.Ind.GridEnvelopeNCheck.Kc_ne_zero
#check @RBM.Ind.GridEnvelopeNCheck.rpow_21_le_Kc
#check @RBM.Ind.GridEnvelopeNCheck.rangeCond_half
#check @RBM.Ind.GridEnvelopeNCheck.sum_weighted_stepErrN_instance
#check @RBM.Ind.GridEnvelopeNCheck.sum_gridStep_instance
-- downstream pins (S3-12)
#check @RBM.Gauss.Sizes.STNQConcl
#check @RBM.Gauss.Sizes.STOeqNQ

/-! ## 2. Pinned vocabulary (T2179 target 1; defined in `RBM.Ind` verbatim) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind.T2179Check

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind

/-- **The right-hand side of the merged `AssembledN` at `m = K n`** with the data of S3-10b
(RBM2D `assembledRHSNonAlt`, `NonAltBudget.lean:57`): `κ = kappaNonAltN`, `εK = epsNonAltN`,
`δ₀ = δ_D = W^{-D'}`, `d_j = dDriftNonAltN(u_j)`, `c = cQVNonAltN`, `stepErr_j = stepErrN` at the
envelope `B_k = N^{τ_K} η_{u_{j+1}}^{-k}`, initial supremum `X0`, Azuma exponent `εq`, `D = D_Y`. -/
def assembledRHSNonAltN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Λg κ' ε : ℝ) (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y τK εq X0 : ℝ) (a : Fin k → Zd d (sz.L n)) : ℝ :=
  kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n) +
        epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)

/-- **The shape of the quadratic-variation majorant** (RBM2D `NonAltBudget_qvShape`,
`NonAltBudget.lean:240`, at `d ≥ 3`): `κ(κ(G B^{2k}/η + Wd) + Ce Wd) + Cc Wd`; `qvBdNonAltN` is the
case `κ = W^{Cε} r^{k-1}`, `Ce = W^C`, `Cc = W^C W^k`, `G = Γ(ΓΛ)`, `Wd = W^{-D''}`, `B = B_u`, `η = η_u`. -/
def nqBudget_qvShape (k : ℕ) (κ Ce Cc G Wd B η : ℝ) : ℝ :=
  κ * (κ * (G * (B ^ (2 * k) / η) + Wd) + Ce * Wd) + Cc * Wd

/-- **The far bound of the kernel weight**: `κ_{i,m} ≤ W^{Cε} ((1+g²) N)^{k-1}` when
`(1-u_m)⁻¹ ≤ N` (`r_{i,m} ≤ (1+g²)(1-u_m)⁻¹`). -/
def nqBudget_kapFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' ε : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
    ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1)

/-- **The far coefficient of the quadratic variation**: the coefficient of `W^{-D''}` in
`nqBudget_qvShape` at `κ ≤ nqBudget_kapFar`, `Ce = W^C`, `Cc = W^C W^k`. -/
def nqBudget_qvFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' ε : ℝ) : ℝ :=
  nqBudget_kapFar sz n k Λg κ' ε *
      (nqBudget_kapFar sz n k Λg κ' ε + ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ') +
    ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ k

/-! ## 3. Pinned statement of `budgetNonAltN` (T2179 target 4; proved in `RBM.Ind` with this
signature, hypotheses in this order, named `hk hε₁ hE hs0 hsv hv1 hK hη hΔη hΓ hΛ hΦ hlog hX0 hR
ha1 ha2 ha3 he1 he2 he3 he4`) -/

/-- **The (5.93) budget of the non-alternating endpoint at `d ≥ 3`** (RBM2D `budgetNonAlt`,
`NonAltBudget.lean:587`): at a fixed `n`, under explicit numerical inequalities only,
`assembledRHSNonAltN ≤ N^{ε₀} (Λ^{1/2} + Φ + Φ²) B_v^k`.  The `Φ²` is the `k Γ³ Φ²` part of
`dDriftNonAltN` (clause (D2) of `GoodSetN`). -/
def budgetNonAltN_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ)
    (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ) (a : Fin k → Zd d (sz.L n)),
    (2 ≤ k) → (0 ≤ ε₁) →
    (|E n| < 2) → (0 ≤ s n) → (s n ≤ v n) → (v n < 1) → (K n ≠ 0) →
    ((etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
    (gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1) →
    (Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) → (1 ≤ Λ n) → (0 ≤ Φ n) →
    ((∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j)) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) →
    (X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
    ((∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t)) →
    (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) →
    ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 3 *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) →
    (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) →
    (((sz.size n : ℕ) : ℝ) ^ k *
        (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) →
    (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) →
    (((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) →
    (((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) →
    assembledRHSNonAltN sz E s v K n k Λg κ' ε Γ Λ Φ D' D'' D_Y τK εq X0 a ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ n + Φ n ^ 2) *
        (sz.Bctl n (v n)) ^ k

end RBM.Ind.T2179Check

end
