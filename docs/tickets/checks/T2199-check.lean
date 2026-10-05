/-
Release check for T2199 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2, §57, §62 (2)).
S3-12b (second of three; S3-12a = T2186 merged d783ee3, S3-12c flow endpoint after): the non-alternating grid
endpoint with the linear right side `N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃)B_v^k`, in the new file
`Induction/NQEndLin` (namespace `RBM.Ind`): absorption and regime lemmas, the assembly per sign vector at the
exit time `nqLinExitTauN` with the drift level `dDriftLinN`, the budget `budgetNonAltLinN`, the union over the
sign vectors.  `GoodSetN` enters at a free crude level `Φc` (S3-12c takes `Φc n = N^{C₀}`); the good-event
probability (`nqLinGood_holds` ∩ `gridGoodN_holds`) is S3-12c's.
Section 1: the merged names the ticket cites.  Section 2: the pinned statement as a `Prop` in
`RBM.Ind.T2199Check` (T2199 proves `RBM.Ind.nqGridEndLinN` with exactly this statement).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2199-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names (private helpers of `NQLin`, `NQGood2`, `NQBudget` cannot be `#check`ed; the ticket copies
them, it does not call them) -/

-- the primed pin and the old pin (`Induction/Step34PinsP`, `Induction/Step34Pins`)
#check @RBM.Gauss.Sizes.STNQConcl'
#check @RBM.Gauss.Sizes.STOeqNQ'
#check @RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ
#check @RBM.Gauss.Step34PInst.inst_OeqNQ'
#check @RBM.Gauss.Sizes.STNQConcl
#check @RBM.Gauss.Sizes.STOeqNQ
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Step34Inst.sz0_caseI
-- the sizes, the window, the regime (`Defs/Sizes`, `Green/Pins`, `Induction/Defs`, `Loop/KLFinal`)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.stKbound_holds
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.etaT
#check @RBM.mE
#check @RBM.mE_im
#check @RBM.mE_im_pos
#check @RBM.lemT_lt_one
#check @RBM.Zd
#check @RBM.Gauss.Idx
-- the grid walk (`Path/Walk`, `Induction/Step2Events`, `Defs/StochDomAt`)
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.pathH
#check @RBM.Path.gridTime_last
#check @RBM.Path.map_pathH_eq
#check @RBM.Path.TimeIcc
#check @RBM.Path.highProbAt_iInter
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.Sizes.ST_gridTime_zero
#check @RBM.Gauss.Sizes.ST_gridTime_mono
#check @RBM.Gauss.Sizes.ST_gridStep_nonneg
-- loops and `ℰ` terms at the matrix level (`Induction/Step2Defs`, `Induction/Defs`, `Induction/GridGoodN`)
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STXiLKM
#check @RBM.Gauss.Sizes.STksimLKM
#check @RBM.Gauss.Sizes.STelklkM
#check @RBM.Gauss.Sizes.STegtM
-- the good set, exit times, good event (`Induction/GridGoodN`)
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.measurableGoodSetN
#check @RBM.Gauss.Sizes.GridGoodNConcl
#check @RBM.Gauss.Sizes.gridGoodN_holds
#check @RBM.Path.gridExitTauN
#check @RBM.Path.mem_of_lt_gridExitTauN
#check @RBM.Path.gridExitTauN_eq_of_forall_mem
-- the Duhamel identity, the step decomposition, the envelope (`GridDuhamelN`, `StepDecompN`, `GridDriftN`,
-- `GridEnvelopeN`)
#check @RBM.Ind.Ugen
#check @RBM.Ind.AvecN
#check @RBM.Ind.martIncN
#check @RBM.Ind.predIncN
#check @RBM.Ind.stoppedDuhamelN_at
#check @RBM.Ind.ZvecN
#check @RBM.Ind.YvecN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.stepErrN
#check @RBM.Ind.gridDriftN_envelope
#check @RBM.Ind.sum_gridStep_div_etaT_le
#check @RBM.Ind.sum_weighted_stepErrN_le
-- the assembly (`Induction/GridAssemblyN`) and the uniform `Y` moments (`Induction/AzumaProxyN2`)
#check @RBM.Ind.YMomentBoundsN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.assembledN
#check @RBM.Ind.gridAsm_stronglyMeasurable_ZvecN
#check @RBM.Ind.YMomentsUnifN
#check @RBM.Ind.yMomentsUnifN
-- the kernel constant, the drift tensor, crude bounds, shift errors (`Induction/NQGood1`)
#check @RBM.Ind.driftTensorN
#check @RBM.Ind.nqGood1C
#check @RBM.Ind.nqGood1C_pos
#check @RBM.Ind.nqGood1_mE_im_ge
#check @RBM.Ind.STXiLKM_crudeN
#check @RBM.Ind.loopShiftErrN
#check @RBM.Ind.eeShiftErrN
-- the fields of the bundle (`Induction/NQGood2`)
#check @RBM.Ind.nonAltClsN
#check @RBM.Ind.kappaNonAltN
#check @RBM.Ind.epsNonAltN
#check @RBM.Ind.dDriftNonAltN
#check @RBM.Ind.cQVNonAltN
#check @RBM.Ind.nonAlt_hkerN
#check @RBM.Ind.nonAlt_hA0clsN
#check @RBM.Ind.nonAlt_hDclsN
#check @RBM.Ind.nonAlt_hκ0N
#check @RBM.Ind.nonAlt_hε0N
#check @RBM.Ind.hQ_nonAltN
#check @RBM.Ind.cQVNonAltN_sum_pos
-- the merged budget pieces (`Induction/NQBudget`)
#check @RBM.Ind.assembledRHSNonAltN
#check @RBM.Ind.nqBudget_kapFar
#check @RBM.Ind.nqBudget_qvFar
#check @RBM.Ind.tbInitNonAltN
#check @RBM.Ind.tbQvNonAltN
#check @RBM.Ind.budgetNonAltN
#check @RBM.Ind.nqBudget_merged_inputs
-- S3-12a (`Induction/NQLin`, d783ee3)
#check @RBM.Gauss.Sizes.GoodLinN
#check @RBM.Gauss.Sizes.measurableGoodLinN
#check @RBM.Gauss.Sizes.nqLinPhi1
#check @RBM.Gauss.Sizes.nqLinPhi2
#check @RBM.Gauss.Sizes.nqLinPhi3
#check @RBM.Gauss.Sizes.NQLinConcl
#check @RBM.Gauss.Sizes.NQLinGood
#check @RBM.Gauss.Sizes.nqLinGood_holds
#check @RBM.Ind.dDriftLinN
#check @RBM.Ind.nqLinExitTauN
#check @RBM.Ind.driftTensorN_norm_le_of_goodLin
#check @RBM.Ind.nqLin_hdriftN
#check @RBM.Ind.mem_of_lt_nqLinExitTauN
#check @RBM.Ind.nqLinExitMeasN
#check @RBM.Ind.subGaussStop_linN
#check @RBM.Ind.assembledRHSLinN
#check @RBM.Ind.tbDriftLinN
#check @RBM.Ind.budgetNonAltLinN
-- the continuity net (`Induction/ContinuityNet`; S3-12c)
#check @RBM.Ind.ContinuityNet.cont_core
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.Gauss.SizesInst.sz0_bandwidth
#check @RBM.Gauss.SizesInst.sz0_WO
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.W_ge_32
#check @RBM.Gauss.GridGoodNInst.vg
#check @RBM.Gauss.GridGoodNInst.Kg
#check @RBM.Gauss.GridGoodNInst.grid_data
#check @RBM.Gauss.GridGoodNInst.gridGood_instance
#check @RBM.Gauss.GridGoodNInst.gridGood_instance_nonempty
#check @RBM.Ind.azumaSubGN
#check @RBM.Ind.qvFormN_le_of_goodSetN_shiftN
#check @RBM.Ind.driftTensorN_far_of_goodSet
#check @RBM.Ind.AzumaProxyNInst.Einst
#check @RBM.Ind.AzumaProxyNInst.Einst_abs_lt
#check @RBM.Ind.AzumaProxyNInst.sig3
#check @RBM.Ind.AzumaProxyNInst.sInst_le_vg
#check @RBM.Ind.AzumaProxyNInst.Γ4
#check @RBM.Ind.AzumaProxyNInst.Λ3
#check @RBM.Ind.AzumaProxyNInst.Φ1
#check @RBM.Ind.NQGood1Inst.aFar
#check @RBM.Ind.NQGood1Inst.zero_mem_goodSetN_inst
#check @RBM.Ind.NQGood2Inst.tau0
#check @RBM.Ind.NQGood2Inst.tau0_pos
#check @RBM.Ind.NQGood2Inst.gridAssemblyHyp_instance
#check @RBM.Ind.NQBudgetInst.hlog_instance
#check @RBM.Ind.NQBudgetInst.hR_instance
#check @RBM.Ind.NQBudgetInst.budgetNonAltN_instance
#check @RBM.Ind.NQLinInst.nqLinExitTauN_eq_tau0
#check @RBM.Ind.NQLinInst.zero_mem_goodLinN_inst
#check @RBM.Ind.NQLinInst.subGaussStop_lin_instance
#check @RBM.Ind.NQLinInst.nqLinGood_instance
#check @RBM.Ind.NQLinInst.nqLinGood_instance_nonempty
#check @RBM.Ind.NQLinInst.budgetNonAltLinN_instance
#check @RBM.Ind.GridEnvelopeNCheck.rangeCond_half
#check @RBM.Ind.AzumaProxyN2Inst.yMomentsUnifN_instance
#check @RBM.Ind.GridAssemblyNInst.gridAsm_assembledN_instance_gen

/-! ## 2. The pinned statement (T2199 proves `RBM.Ind.nqGridEndLinN` with exactly this type; the theorem is
checked by `example : RBM.Ind.T2199Check.T2199_nqGridEndLinN := @RBM.Ind.nqGridEndLinN`) -/

namespace RBM.Ind.T2199Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-- **`nqGridEndLinN`: the non-alternating grid endpoint with the linear right side** (`lem:STOeq_NQ`, `3_5:1136`,
proof `3_5:1152-1180`; RBM2D `nonAltGridEnd`, `Induction/NonAltEnd.lean:1116` at `c9a24cf`, pin `GridEndConcl`,
`Induction/StoppedEndDefs.lean:126`).  Setting: `3 ≤ d`, constants `κ, 𝔠, τ, 𝔡 > 0`, `N → ∞`, `W ≥ N^𝔠`,
`(eq:WO)`, `|E| ≤ 2 - κ`, `0 ≤ s ≤ t < 1`, case (i) `1 - t ≥ g²/L²`, `1 - t ≥ N^{-1+τ}`, and `W⁻¹ ≤ (1-t)/(1-s)`
eventually.  For every length `k ≥ 2`, deterministic levels `Λ ≥ 0` (`≥ 1` eventually), `Φ₁, Φ₂, Φ₃ ≥ 0`, end time
`v ∈ [s,t]`, final loss `ε₀ > 0` and failure exponent `D₁ > 0` there are exponents `ε₁, τ', D', C_K` such that, for
every crude level `Φc` of `GoodSetN` and every grid `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`, eventually there is an event `G`,
`P(Gᶜ) ≤ N^{-D₁}`, on which: if the grid walk is in `GoodSetN(N^{ε₁}, Λ, Φc, τ', D') ∩ GoodLinN(N^{ε₁}, Φ₁, Φ₂, Φ₃)`
at every `j ≤ K_n` and the initial loops satisfy `|(𝓛-𝒦)_{s,σ,a}| ≤ N^{ε₁} B_s^k` for the non-alternating `σ`, then
`|(𝓛-𝒦)_{v,σ,a}(H_{K_n})| ≤ N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k` for every non-alternating `σ` and label `a`.
No `Φ²`, no `Φc` on the right side; no `STKbound` premise (`stKbound_holds` discharges it). -/
def T2199_nqGridEndLinN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseI s t → sz.RangeCond τ t →
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) →
    ∀ k : ℕ, 2 ≤ k →
    ∀ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          (∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                (sz.Bctl n (v n)) ^ k

end RBM.Ind.T2199Check
