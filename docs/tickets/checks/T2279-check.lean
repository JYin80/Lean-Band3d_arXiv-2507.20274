import RBM3D.Induction.QLevelsB
import RBM3D.Induction.QProxy
import RBM3D.Induction.NQLin

/-!
# T2279 (S3-17a, `Induction/QBudgetA`): check file

Section 1: `#check` of every merged name the ticket uses (compiles on `main` = 803bb88).
Section 2: the vocabulary (six definitions, copied VERBATIM into `RBM3D/Induction/QBudgetA.lean`).
Section 3: the pinned statements `T2279_*` (each proved in `QBudgetA.lean` with exactly this statement, theorem
name = the `Prop` name without `T2279_`).
No proofs, no `sorry`, no `by` here.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. Merged names (file:line on `main` 803bb88) -/

-- `Induction/QDriftA.lean` (88ee6fd)
#check @RBM.Ind.kappaAltQN            -- :100
#check @RBM.Ind.epsAltQN              -- :104
#check @RBM.Ind.altClsQN              -- :93
#check @RBM.Ind.alt_hkerQN            -- :353
#check @RBM.Ind.alt_hA0clsQN          -- :473
#check @RBM.Ind.dFlowQN               -- :79
-- `Induction/QDriftB.lean` (c01b292)
#check @RBM.Ind.alt_hDclsQN           -- :379
#check @RBM.Ind.drift13_fastDecay     -- :152
-- `Induction/QLevelsA.lean` (f515695)
#check @RBM.Ind.altB45N_levelM        -- :376
#check @RBM.Ind.startLevelQN          -- :421
-- `Induction/QLevelsB.lean` (54b8610)
#check @RBM.Ind.dDriftAltQN           -- :53
#check @RBM.Ind.goodSetN_LKM_far      -- :108
#check @RBM.Ind.qopB13N_levelM        -- :126
#check @RBM.Ind.dFlowQN_levelM        -- :171
#check @RBM.Ind.alt_hdriftQN          -- :245
#check @RBM.Ind.dDriftAltQN_nonneg    -- :287
-- `Induction/QProxy.lean` (9a207a1)
#check @RBM.Ind.qvFormQN              -- :83
#check @RBM.Ind.qProxyCn              -- :434
#check @RBM.Ind.qProxyCQ              -- :440
#check @RBM.Ind.qProxy4C              -- :444
#check @RBM.Ind.qProxyCn_pos          -- :458
#check @RBM.Ind.qProxy4C_pos          -- :465
#check @RBM.Ind.qvFormQN_le_of_goodSetN  -- :1167
#check @RBM.Ind.azumaSubGQ_gridExitN  -- :409
-- `Induction/NQGood2.lean` (cc96b69)
#check @RBM.Ind.kappaNonAltN          -- :86
#check @RBM.Ind.dDriftNonAltN         -- :96
#check @RBM.Ind.nqGood2_ratio_mul_Bctl_le      -- :131
#check @RBM.Ind.kappaNonAltN_mul_Bctl_pow_le   -- :188
#check @RBM.Ind.kappaNonAltN_succ_mul_Bctl_pow_le  -- :206
-- `Induction/NQBudget.lean` (5b887a6)
#check @RBM.Ind.nqBudget_qvShape      -- :96
#check @RBM.Ind.nqBudget_kapFar       -- :101
#check @RBM.Ind.nqBudget_qvFar        -- :107
#check @RBM.Ind.nqBudget_inv_one_sub_le   -- :125
#check @RBM.Ind.nqBudget_sum_succ_le  -- :141
#check @RBM.Ind.nqBudget_sqrt_add_le  -- :148
#check @RBM.Ind.nqBudget_kappa_le_kapFar  -- :163
#check @RBM.Ind.tbInitN               -- :207
#check @RBM.Ind.tbDriftN              -- :221
#check @RBM.Ind.tbQvN                 -- :269
#check @RBM.Ind.tbInitNonAltN         -- :368
#check @RBM.Ind.tbQvNonAltN           -- :458
#check @RBM.Ind.nqBudget_merged_inputs    -- :834
#check @RBM.Ind.NQBudgetInst.hlog_instance  -- :1271
#check @RBM.Ind.NQBudgetInst.hR_instance    -- :1241
-- `Induction/NQLin.lean` (d783ee3)
#check @RBM.Gauss.Sizes.GoodLinN      -- :66
#check @RBM.Ind.dDriftLinN            -- :711
#check @RBM.Ind.driftTensorN_norm_le_of_goodLin  -- :732
#check @RBM.Ind.assembledRHSLinN      -- :825
#check @RBM.Ind.tbDriftLinN           -- :876
#check @RBM.Ind.budgetNonAltLinN      -- :966
#check @RBM.Ind.NQLinInst.budgetNonAltLinN_instance  -- :1724
-- `Induction/GridAssemblyN.lean` (686cf71), `Induction/GridDriftN.lean` (14137ce)
#check @RBM.Ind.GridAssemblyHypN      -- :183
#check @RBM.Ind.AssembledN            -- :227
#check @RBM.Ind.stepErrN              -- GridDriftN:289
-- walk, scales (ddf5f74, 7f9bfa1, 5d1e6b1)
#check @RBM.Path.gridStep             -- Path/Walk:67
#check @RBM.Path.gridTime             -- Path/Walk:70
#check @RBM.Path.gridTime_last        -- Path/Walk:160
#check @RBM.Gauss.Sizes.ST_gridTime_mono    -- Step2Events:1151
#check @RBM.Gauss.Sizes.ST_gridStep_nonneg  -- Step2Events:1158
#check @RBM.Gauss.Sizes.Bctl          -- Defs/Sizes:214
#check @RBM.Gauss.Sizes.STBctl_pos    -- ScaleFacts:64
#check @RBM.Gauss.Sizes.STBctl_mono   -- ScaleFacts:74
#check @RBM.Gauss.etaT                -- Loop/GLoop:75
#check @RBM.Gauss.etaT_pos            -- Loop/GLoop:83
#check @RBM.mE                        -- Defs/Semicircle:38

/-! ## 2. Vocabulary (copied verbatim into `QBudgetA.lean`) -/

/-- **The far bound of the alternating kernel weight**: `κ_{i,m} ≤ W^{C₄ε} ((1+g²) N)^k` when `(1-u_m)⁻¹ ≤ N`
(`kappaAltQN`, `QDriftA.lean:100`, exponent `k`, not `k-1`; analogue of `nqBudget_kapFar`, `NQBudget.lean:101`). -/
def altBudget_kapFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) *
    ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k

/-- **The far coefficient of the alternating quadratic variation**: `C_far (C_far + C_e) + C_c` of the generic
`tbQvN` (`NQBudget.lean:269`) at `C_far = altBudget_kapFar`, `C_e = W^{C₄}`, `C_c = W^{C₄} W^k`. -/
def altBudget_qvFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) : ℝ :=
  altBudget_kapFar sz n k Λg κ' KL ε *
      (altBudget_kapFar sz n k Λg κ' KL ε + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL) +
    ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL * ((sz.W n : ℕ) : ℝ) ^ k

/-- **The variance majorant of the `𝒬`-process** (tensors of `m + 1 + 1` indices): the right side of the merged
`qvFormQN_le_of_goodSetN` (`QProxy.lean:1167`) with its `m` at `m + 1`. -/
def qvBdAltQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (m : ℕ) (Λg κ' KL C c ε Γ Λ D u w : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
      ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1)) *
    ((((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
        ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1)) *
      (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / etaT E u)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c)) +
      ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL *
        ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c)) +
    ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL *
      (((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c))

/-- **The sub-Gaussian proxy of the `j`-th propagated `𝒬`-increment towards `u_p`**: `Δ · (m+2) · qvBdAltQN(u_{j+1}, u_p)`
(the left side of the `hQ` premise of `azumaSubGQ_gridExitN`, `QProxy.lean:409`, at its `m` = `m + 1`; the label does
not enter; pattern `cQVNonAltN`, `NQGood2.lean:115`). -/
def cQVAltQN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (Λg κ' KL C c ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (p : ℕ) (_a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) * qvBdAltQN sz n (E n) m Λg κ' KL C c ε (Γ n) (Λ n) D''
    (gridTime s v K n (j + 1)) (gridTime s v K n p))).toNNReal

/-- **The linear drift level of the alternating chain** (DECISIONS §62 (2)/(4)): `dDriftAltQN` (`QLevelsB.lean:53`)
with the quadratic `dDriftNonAltN` replaced by the linear `dDriftLinN` (`NQLin.lean:711`):
`W^{C_n ε'} Γ²(B^k/η)((k-2)Φ₁ + Φ₂ + Φ₃) + W^{-D'+C_n} + N^{τ_N} η⁻¹ B^{m+2} X`, `k = m + 2`. -/
def dDriftAltLinQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftLinN sz n E u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ +
    ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) +
    ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

/-- **The right-hand side of the merged `AssembledN` at the target `K n` for the alternating chain** (tensors of
`m + 1 + 1` indices; pattern `assembledRHSLinN`, `NQLin.lean:825`): `κ = kappaAltQN`, `εK = epsAltQN` at `g = lam n`
(`alt_hkerQN`), initial supremum `X0`, initial decay error `δ0` (`alt_hA0clsQN`), drift levels `dd j` (generic:
`dDriftAltLinQN` or `dDriftAltQN` at `u_j`), drift decay error `δD` (`alt_hDclsQN`: `4 W^{-D'}`), proxy `cQVAltQN`,
`N^{-D_Y}`, `stepErrN` at the envelope `N^{τ_K} η_{u_{j+1}}^{-k}`. -/
def assembledRHSAltQN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (Λg κ' KL C c ε : ℝ) (Γ Λ : ℕ → ℝ) (dd : ℕ → ℝ) (δ0 δD D'' D_Y τK εq X0 : ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) : ℝ :=
  kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) 0 (K n) * δ0 +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dd j +
        epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
      stepErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1))

/-! ## 3. Pinned statements -/

/-- Target 1 (sharp kernel, initial datum; analogue of `kappaNonAltN_mul_Bctl_pow_le`, `NQGood2.lean:188`). -/
def T2279_kappaAltQN_mul_Bctl_pow_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) {W : ℝ}, 0 ≤ W →
    ∀ (u : ℕ → ℝ) {i m : ℕ}, u i ≤ u m → u m < 1 →
      kappaAltQN d k Λg κ' KL (sz.lam n) W ε u i m * (sz.Bctl n (u i)) ^ k ≤
        W ^ (qProxy4C d k Λg κ' KL * ε) * (sz.Bctl n (u m)) ^ k

/-- Target 2 (sharp kernel, drift; analogue of `kappaNonAltN_succ_mul_Bctl_pow_le`, `NQGood2.lean:206`). -/
def T2279_kappaAltQN_succ_mul_Bctl_pow_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) {W : ℝ}, 0 ≤ W →
    ∀ (u : ℕ → ℝ) (j m : ℕ), u j ≤ u (j + 1) → u (j + 1) ≤ u m → u m < 1 →
      kappaAltQN d k Λg κ' KL (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k ≤
        W ^ (qProxy4C d k Λg κ' KL * ε) * (sz.Bctl n (u m)) ^ k

/-- Target 3 (far bound; analogue of `nqBudget_kappa_le_kapFar`, `NQBudget.lean:163`). -/
def T2279_kappaAltQN_le_kapFar : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) (u : ℕ → ℝ) {i m : ℕ},
    0 ≤ u i → u i ≤ u m → u m < 1 → (1 - u m)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) →
      kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m ≤ altBudget_kapFar sz n k Λg κ' KL ε

/-- Target 4 (the variance majorant is a `nqBudget_qvShape`; analogue of `qvBdNonAltN_eq_qvShape`,
`NQBudget.lean:355`). -/
def T2279_qvBdAltQN_eq_qvShape : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (m : ℕ) (Λg κ' KL C c ε Γ Λ D u w : ℝ),
    qvBdAltQN sz n E m Λg κ' KL C c ε Γ Λ D u w =
      nqBudget_qvShape (m + 1 + 1)
        (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
          ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1))
        (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL)
        (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1))
        (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ * (Γ * Λ)))
        (((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c))
        (sz.Bctl n u) (etaT E u)

/-- Target 5 (initial term; analogue of `tbInitNonAltN`, `NQBudget.lean:368`). -/
def T2279_tbInitAltQN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' KL ε G X0 : ℝ),
    0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 → 0 ≤ G → X0 ≤ G * (sz.Bctl n (s n)) ^ k →
      kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 ≤
        ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) * G * (sz.Bctl n (v n)) ^ k

/-- Target 6 (drift term at a generic level `dd j ≤ Pa Φd B_{u_j}^k/η_{u_j} + b`; the merged generic `tbDriftN`,
`NQBudget.lean:221`, with targets 2 and 3; analogue of `tbDriftLinN`, `NQLin.lean:876`). -/
def T2279_tbDriftAltQN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' KL ε : ℝ)
    (dd : ℕ → ℝ) (Pa Φd b δD : ℝ),
    |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 →
    0 ≤ Pa → 0 ≤ Φd → 0 ≤ b → 0 ≤ δD →
    (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) →
    (∀ j < K n, dd j ≤ Pa * Φd * ((sz.Bctl n (gridTime s v K n j)) ^ k / etaT (E n) (gridTime s v K n j)) + b) →
      gridStep s v K n * ∑ j ∈ Finset.range (K n),
        (kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) * dd j +
          epsAltQN d k Λg κ' KL ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) ≤
        ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) * (Pa * Φd) * (sz.Bctl n (v n)) ^ k *
            ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) +
          ((K n : ℝ) * gridStep s v K n) *
            (altBudget_kapFar sz n k Λg κ' KL ε * b + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL * δD)

/-- Target 7 (quadratic-variation term; the merged generic `tbQvN`, `NQBudget.lean:269`, with targets 1 and 4;
analogue of `tbQvNonAltN`, `NQBudget.lean:458`). -/
def T2279_tbQvAltQN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n m : ℕ) (Λg κ' KL C c ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (a : Fin (m + 1 + 1) → Zd d (sz.L n)),
    |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 → 0 ≤ Λ n →
    (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) →
      ∑ j ∈ Finset.range (K n), (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ) ≤
        ((m + 1 + 1 : ℕ) : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε)) ^ 2 *
            (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n))) *
            ((sz.Bctl n (v n)) ^ (m + 1 + 1)) ^ 2 *
            ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n (j + 1)) +
          ((K n : ℝ) * gridStep s v K n) *
            (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))

/-- Target 8 (the linear level in the generic shape of target 6: `Pa = W^{C_nε'}Γ²k + N^{τ_N}`,
`Φd = Φ₁ + Φ₂ + Φ₃ + X`, `b = W^{-D'+C_n}`). -/
def T2279_dDriftAltLinQN_le_shape : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ),
    |E| < 2 → u < 1 → 0 ≤ Φ₁ → 0 ≤ Φ₂ → 0 ≤ Φ₃ → 0 ≤ X →
      dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X ≤
        (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) + ((sz.size n : ℕ) : ℝ) ^ τN) *
            (Φ₁ + Φ₂ + Φ₃ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) +
          ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn)

/-- Target 9 (the merged quadratic level `dDriftAltQN` of S3-16b in the generic shape of target 6: `Pa` carries
the factor `1 + ΓΦ`, see Design (c)). -/
def T2279_dDriftAltQN_le_shape : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ),
    |E| < 2 → u < 1 → 0 ≤ Γ → 0 ≤ Φ → 0 ≤ X →
      dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X ≤
        (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ) +
            ((sz.size n : ℕ) : ℝ) ^ τN) *
            (Φ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) +
          ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn)

/-- Target 10 (**the budget of the alternating endpoint**, `d ≥ 3`; analogue of `budgetNonAltLinN`, `NQLin.lean:966`):
at a fixed `n`, under explicit numerical inequalities only (eventual forms: S3-17b),
`assembledRHSAltQN ≤ N^{ε₀} (Λ^{1/2} + Φd) B_v^k`, `k = m + 2`, `C₄ = qProxy4C d k Λg κ' KL`,
`C_n = qProxyCn d (m+1) Λg KL C c`, `C_Q = qProxyCQ d (m+1) Λg KL C c`. -/
def T2279_budgetAltQN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (Λg κ' KL C c ε : ℝ)
    (Γ Λ : ℕ → ℝ) (dd : ℕ → ℝ) (Pa Φd b δ0 δD D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)),
    0 ≤ ε₁ → |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 →
    (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) →
    gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1 →
    Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁ → 1 ≤ Λ n →
    0 ≤ Pa → 0 ≤ Φd → 0 ≤ b → 0 ≤ δ0 → 0 ≤ δD →
    (∀ j < K n, dd j ≤ Pa * Φd * ((sz.Bctl n (gridTime s v K n j)) ^ (m + 1 + 1) /
      etaT (E n) (gridTime s v K n j)) + b) →
    -- `hlog` (merged input, `nqBudget_merged_inputs` conjunct 1)
    ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) →
    -- `hX0` (initial level; S3-18a: `startLevelQN`)
    X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1) →
    -- `hR` (merged input, `nqBudget_merged_inputs` conjunct 2 at `k = m + 2`)
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
        stepErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t) →
    -- `ha1` (initial term)
    ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
    -- `ha2` (drift, main part)
    ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * Pa *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `ha3` (quadratic variation, main part)
    ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
        ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `he0` (initial decay error)
    ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δ0) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `he1` (drift, far part)
    ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * (altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε * b +
        ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δD) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `he2` (quadratic variation, far part)
    ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) *
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `he3`, `he4`
    ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
    ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      assembledRHSAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ dd δ0 δD D'' D_Y τK εq X0 a ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φd) * (sz.Bctl n (v n)) ^ (m + 1 + 1)

end RBM.Ind

end
