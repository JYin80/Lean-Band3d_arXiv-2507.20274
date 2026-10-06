/-
T2274 (S3-21) check file: statements only (no proofs, no `sorry`, no `by`).
Compiles on `main` (f515695) as is: imports of merged modules, `#check`s of merged names,
the two vocabulary definitions (§2, verbatim targets), the seven pinned statements (§3).
-/
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.NQLin
import RBM3D.Induction.NQGood1
import RBM3D.Induction.NQGood2
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.GridDriftN
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.AzumaProxyN
import RBM3D.Induction.QVN
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.SEforLn2
import RBM3D.Induction.NewPQ
import RBM3D.Evolution.Prec
import RBM3D.Evolution.Nonzero
import RBM3D.Evolution.Pins
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.Prop5Short
import RBM3D.Defs.Semicircle

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Merged names used (all on `main`) -/

-- the target of S3-22 (R2*, owed; never the unprimed `STOeqQtNZ`)
#check @RBM.Gauss.Sizes.STOeqQtNZ'            -- NQEndFlow.lean:130
#check @RBM.Gauss.Sizes.STXiBoot'             -- NQEndFlow.lean:95
#check @RBM.Gauss.Sizes.STOeqQtNZ             -- Step34Pins.lean:465 (superseded, DECISIONS §80 (1))
#check @RBM.Gauss.Sizes.STIngR                -- Step34Pins.lean:445
#check @RBM.Gauss.Sizes.STCaseII              -- Step34Pins.lean:241
#check @RBM.Gauss.Sizes.STIdiff               -- Step34Pins.lean:97
#check @RBM.Gauss.Sizes.STbootRHS             -- Step34Pins.lean:402
#check @RBM.Gauss.Sizes.STSEforLnConcl        -- Step34Pins.lean:363
#check @RBM.Gauss.Sizes.STEKNonzero           -- Step34Pins.lean:666 (Prec form; not used, see Design 1)
#check @RBM.Gauss.Sizes.stek_nonzero_holds    -- Evolution/Prec.lean:422
-- EK-5, deterministic and loss-free
#check @RBM.EKSumDecayNonzero                 -- Evolution/Pins.lean:128
#check @RBM.ekSumDecayNonzero_holds           -- Evolution/Nonzero.lean:146
#check @RBM.prop5Short_holds                  -- Propagator/Prop5Short.lean:400
#check @RBM.prop8ZeroMode_holds               -- Propagator/Prop5Hold.lean:1266
#check @RBM.norm_mE                           -- Defs/Semicircle.lean:63
-- S3-20 (zero-mode calculus)
#check @RBM.zeroModeOp                        -- Kernel/Evolution.lean:194
#check @RBM.zeroModeSet                       -- Kernel/Evolution.lean:199
#check @RBM.SameSignOutside                   -- Kernel/Evolution.lean:618
#check @RBM.norm_zeroModeSet_UN_le            -- Kernel/Evolution.lean:629
#check @RBM.norm_zeroModeSet_le               -- ZeroModeCalc.lean:163
#check @RBM.zeroModeSet_sub                   -- ZeroModeCalc.lean:110
#check @RBM.zeroModeSet_sum                   -- ZeroModeCalc.lean:114
#check @RBM.Ind.Ugen_eq_UN_EKsgn              -- ZeroModeCalc.lean:445
#check @RBM.Ind.zeroModeSet_Ugen              -- ZeroModeCalc.lean:450
#check @RBM.Ind.zeroModeCalc_duhamel_at       -- ZeroModeCalc.lean:493
#check @RBM.Ind.zeroModeCalc_duhamel_inside_at -- ZeroModeCalc.lean:522
#check @RBM.Gauss.Sizes.zeroModeCalc_LK_expansion_empty -- ZeroModeCalc.lean:595
#check @RBM.Gauss.Sizes.stNewPQ_holds         -- NewPQ.lean:584
-- grid kernel, Duhamel, assembly (ST-2, T2039 chain)
#check @RBM.Ind.Ugen                          -- GridDuhamelN.lean:65
#check @RBM.Ind.AvecN                         -- GridDuhamelN.lean:272
#check @RBM.Ind.martIncN                      -- GridDuhamelN.lean:277
#check @RBM.Ind.predIncN                      -- GridDuhamelN.lean:284
#check @RBM.Ind.stoppedDuhamelN_at            -- GridDuhamelN.lean:310
#check @RBM.Ind.YMomentBoundsN                -- GridAssemblyN.lean:141
#check @RBM.Ind.YMomentsN                     -- GridAssemblyN.lean:173
#check @RBM.Ind.GridAssemblyHypN              -- GridAssemblyN.lean:183 (hker :201, hdrift :208, hDcls :209, hY :213)
#check @RBM.Ind.AssembledN                    -- GridAssemblyN.lean:227
#check @RBM.Ind.assembledN                    -- GridAssemblyN.lean:1605
#check @RBM.Ind.loopFamN                      -- StepDecompN.lean:150
#check @RBM.Ind.ZvecN                         -- StepDecompN.lean:185
#check @RBM.Ind.YvecN                         -- StepDecompN.lean:192
#check @RBM.Ind.stoppedEdgeN                  -- StepDecompN.lean:198
#check @RBM.Ind.SubGaussFormN                 -- StepDecompN.lean:206
#check @RBM.Ind.SubGaussStopN                 -- StepDecompN.lean:215
#check @RBM.Ind.azumaSubGN                    -- AzumaProxyN.lean:257
#check @RBM.Ind.azumaProxy_subG_ugen          -- AzumaProxyN.lean:980 (pattern)
#check @RBM.Ind.QVPropagatedN                 -- QVN.lean:799
#check @RBM.Ind.qvPropagatedN                 -- QVN.lean:813
#check @RBM.Ind.stepErrN                      -- GridDriftN.lean:289
#check @RBM.Path.gridStep                     -- Path/Walk.lean:67
#check @RBM.Path.gridTime                     -- Path/Walk.lean:70
#check @RBM.Path.pathH                        -- Path/Walk.lean:75
-- the good sets and the case-(i) analogues (patterns; reused where stated)
#check @RBM.Gauss.Sizes.GoodSetN              -- GridGoodN.lean:124
#check @RBM.Gauss.Sizes.gridGoodN_holds       -- GridGoodN.lean:930
#check @RBM.Gauss.Sizes.GoodLinN              -- NQLin.lean:66
#check @RBM.Gauss.Sizes.nqLinGood_holds       -- NQLin.lean:591
#check @RBM.Ind.driftTensorN                  -- NQGood1.lean:95
#check @RBM.Ind.eeShiftErrN                   -- NQGood1.lean:982
#check @RBM.Ind.cQVNonAltN                    -- NQGood2.lean:115
#check @RBM.Ind.hQ_nonAltN                    -- NQGood2.lean:519
#check @RBM.Ind.dDriftLinN                    -- NQLin.lean:711
#check @RBM.Ind.nqLinExitTauN                 -- NQLin.lean:716
#check @RBM.Ind.nqLin_hdriftN                 -- NQLin.lean:761
#check @RBM.Ind.mem_of_lt_nqLinExitTauN       -- NQLin.lean:772
#check @RBM.Ind.nqLinExitMeasN                -- NQLin.lean:781
#check @RBM.Ind.subGaussStop_linN             -- NQLin.lean:792
#check @RBM.Ind.assembledRHSLinN              -- NQLin.lean:825
#check @RBM.Ind.budgetNonAltLinN              -- NQLin.lean:966
#check @RBM.Gauss.Sizes.STBctl_mono           -- ScaleFacts.lean:74
#check @RBM.Gauss.Sizes.stSEforLn_holds       -- SEforLn2.lean:1287

namespace RBM.Ind.T2274Check

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind

/-! ## 2. Vocabulary (targets 1–2 of the ticket; verbatim in `RBM.Ind`) -/

/-- The sub-Gaussian proxy of the `j`-th propagated zero-mode-removed increment (case (ii)):
`Δ · k · C² · (Γ(ΓΛ) B_{u_j}^{2k}/η_{u_j} + W^{-D''})` (`C` = row-sum bound of `Q^{(A)}∘𝒰`;
no ratio factor, no far part: the analogue of `cQVNonAltN`, `NQGood2.lean:115`). -/
def cQVNZN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (C Γ Λ D'' : ℝ) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * C ^ 2 *
    (Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / etaT (E n) (gridTime s v K n j)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D'')))).toNNReal

/-- The right side of `AssembledN` (`GridAssemblyN.lean:227`) at `m = K n` for the zero-mode-removed
evolution: kernel weight `κ ≡ C`, `εK ≡ 0`, drift level `cA · dDriftLinN`, proxy `cQVNZN`,
step error `cA · stepErrN` (`cA = 2^{|A|}`); the analogue of `assembledRHSLinN` (`NQLin.lean:825`). -/
def assembledRHSNZN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (C cA : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D'' D_Y τK εq X0 : ℝ) : ℝ :=
  C * X0 +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      C * (cA * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * (cA *
      stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k))

/-! ## 3. The pinned statements (targets 3–9) -/

/-- Target 3, `RBM.zeroModeSet_idem`: `Q^{(A)} ∘ Q^{(A)} = Q^{(A)}`. -/
def T2274_zeroModeSet_idem : Prop :=
  ∀ (d L : ℕ) [NeZero L] (n : ℕ) (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ),
    zeroModeSet d L A (zeroModeSet d L A T) = zeroModeSet d L A T

/-- Target 4, `RBM.Ind.nzUgen_holds`: `lem:sum_decay_nonzero` (`3_5:1666`) for the grid kernel `Ugen`,
loss-free (EK-5), as an operator bound and as a row-sum bound with one constant. -/
def T2274_nzUgen : Prop :=
  ∀ (d k : ℕ), 3 ≤ d → 2 ≤ k → ∀ Λg κ' : ℝ, 0 < Λg → 0 < κ' →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g E : ℝ, 0 < g → g ≤ Λg → |E| < 2 → κ' ≤ (mE E).im →
        ∀ v w : ℝ, 0 ≤ v → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ v → v ≤ w → w < 1 →
        ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
          (∀ X : (Fin k → Zd d L) → ℂ, ‖zeroModeSet d L A (Ugen d L g E σ v w X)‖ ≤ C * ‖X‖) ∧
          ∀ a : Fin k → Zd d L, ∃ κ : (Fin k → Zd d L) → ℂ,
            (∀ X : (Fin k → Zd d L) → ℂ, zeroModeSet d L A (Ugen d L g E σ v w X) a = ∑ b, κ b * X b) ∧
            ∑ b, ‖κ b‖ ≤ C

/-- Target 5, `RBM.Ind.nz_hker`: the `hker` field of `GridAssemblyHypN` (`GridAssemblyN.lean:201`) for
the class `Cls := fun _ _ X => zeroModeSet d (sz.L n) A X = X`, `κ ≡ C`, `εK ≡ 0`. -/
def T2274_nz_hker : Prop :=
  ∀ {d k : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (σ : Fin k → Bool) (A : Finset (Fin k)) (u : ℕ → ℝ)
    (K : ℕ) (C : ℝ), 0 ≤ C → |E| ≤ 2 → (∀ i ≤ K, 0 ≤ u i) → (∀ i ≤ K, u i < 1) →
    (∀ i m, i ≤ m → m ≤ K → ∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
      ‖zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X)‖ ≤ C * ‖X‖) →
    ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → zeroModeSet d (sz.L n) A X = X →
      ∀ a, ‖Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X a‖ ≤ C * M + 0 * δ

/-- Target 6, `RBM.Ind.nz_hdriftN`: the drift of the zero-mode-removed hierarchy on `GoodLinN`
(`Q^{(A)}` of the merged `driftTensorN`; `nqLin_hdriftN` and `(normQA2)`). -/
def T2274_nz_hdriftN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {n k : ℕ}, 2 ≤ k → ∀ (σ : Fin k → Bool) (A : Finset (Fin k))
    (E s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ : PathΩ sz → ℕ),
    (∀ ω j, j < τ ω → pathH sz s v K n j ω ∈
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
    ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n),
      ‖zeroModeSet d (sz.L n) A
          (driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ) b‖ ≤
        2 ^ A.card * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)

/-- Target 7, `RBM.Ind.subGaussStop_nzN`: the Azuma input (`SubGaussStopN`, `StepDecompN.lean:215`) for the
zero-mode-removed first-chaos part `Q^{(A)} Z_j`, proxy `cQVNZN`, on any stopping family that stays in
`GoodSetN` (its `STeeM` clause only), from a row-sum bound `≤ C` of `Q^{(A)}∘𝒰_{u_{j+1},u_m}`. -/
def T2274_subGaussStop_nzN : Prop :=
  ∀ {d k : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin k → Bool)
    (A : Finset (Fin k)) (C Γ Λ Φ τ' D' D'' : ℝ) (τ : PathΩ sz → ℕ),
    2 ≤ k → (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) →
    0 ≤ C → 0 ≤ Γ → 0 ≤ Λ →
    (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    (∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k Γ Λ Φ τ' D') →
    ∀ m, m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
      (∃ κ : (Fin k → Zd d (sz.L n)) → ℂ,
        (∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
          zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s v K n (j + 1))
            (gridTime s v K n m) X) a = ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C) →
      ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k
          (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') →
      SubGaussStopN sz (E n) σ (gridTime s v K n) τ
        (fun j ω => zeroModeSet d (sz.L n) A (ZvecN sz E s v K n j σ ω)) m a j
        (cQVNZN sz E s v K n k C Γ Λ D'' j)

/-- Target 8, `RBM.Ind.yMomentBounds_nzN`: the `Y`-moment inputs (`YMomentBoundsN`, `GridAssemblyN.lean:141`)
pass to `Q^{(A)} Y` with the levels `4^{|A|+1} v`, `16^{|A|+1} w`. -/
def T2274_yMomentBounds_nzN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (A : Finset (Fin k)) (u : ℕ → ℝ)
    (τ : PathΩ sz → ℕ) (K : ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (v w : ℕ → ℝ),
    |E| ≤ 2 → (∀ i ≤ K, 0 ≤ u i) → (∀ i ≤ K, u i < 1) →
    YMomentBoundsN sz E σ u τ K Y v w →
    YMomentBoundsN sz E σ u τ K (fun j ω => zeroModeSet d (sz.L n) A (Y j ω))
      (fun j => 4 ^ (A.card + 1) * v j) (fun j => 16 ^ (A.card + 1) * w j)

/-- Target 9, `RBM.Ind.budgetNZN`: the budget of the case-(ii) grid endpoint at the linear levels
(the analogue of `budgetNonAltLinN`, `NQLin.lean:966`; no ratio weights, no far parts):
`assembledRHSNZN ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`. -/
def T2274_budgetNZN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (C cA : ℝ)
    (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ),
    2 ≤ k → 0 < C → 0 ≤ cA → 0 ≤ ε₁ → |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 →
    Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁ → 1 ≤ Λ n → 0 ≤ Φ₁ n → 0 ≤ Φ₂ n → 0 ≤ Φ₃ n →
    ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) →
    X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k →
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t) →
    C * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
    C * cA * (k : ℝ) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
    ((sz.size n : ℕ) : ℝ) ^ εq * (C * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
    cA * ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
    assembledRHSNZN sz E s v K n k C cA Γ Λ Φ₁ Φ₂ Φ₃ D'' D_Y τK εq X0 ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
        (sz.Bctl n (v n)) ^ k

/-! ## 4. Shape examples (Prop-valued, no proof obligations) -/

-- The S3-22 target is the primed pin at `d = 3` (consumer check, DECISIONS §45 O2).
example : Prop := RBM.Gauss.Sizes.STOeqQtNZ' 3

-- The case-(ii) window predicate at a size sequence (consumer of target 4's `1 - g²/L² ≤ v`).
example {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop := STCaseII sz s t

end RBM.Ind.T2274Check
