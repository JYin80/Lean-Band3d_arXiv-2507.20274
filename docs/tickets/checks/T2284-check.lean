/-
Release check for T2284 (dispatcher V1, Tue Oct  6 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2, §62 (2),
§91 (2), §92 (3) O4, §93 (3)).
S3-22a (ST-3 case (ii) `1 - s ≤ ilambda²/L²`, first of three after the §91 (2) cut; S3-21 = T2274 merged 95d8b2a,
S3-22b flow per-time + lift and S3-22c `newPQ` combination + bootstrap after): the case-(ii) grid endpoint
`nzGridEndN` for the zero-mode-removed loops `Q^{(A)}(𝓛 - 𝒦)^{(k)}`, `A ⊇ I_diff(σ)`, every `σ`, in the new
file `Induction/QtNonzeroEnd` (namespace `RBM.Ind`): the merged `assembledN` with the S3-21 data (`nzUgen_holds`,
`nz_hker`, `nz_hdriftN`, `subGaussStop_nzN`, `yMomentBounds_nzN`, `budgetNZN`, `zeroModeSet_idem`) at the merged
exit time `nqLinExitTauN`, the union over the pairs `(σ, A)`, right side `N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃)B_v^k`.
`GoodSetN` enters at a free crude level `Φc`; the good-event probability (`gridGoodN_holds` ∩ `nqLinGood_holds`)
and the initial event are S3-22b's (as in case (i): T2199 → T2246).
Section 1: the merged names the ticket cites.  Section 2: the pinned statement as a `Prop` in
`RBM.Ind.T2284Check` (T2284 proves `RBM.Ind.nzGridEndN` with exactly this statement).  Section 3: shape
examples (Prop-valued, no proof obligations).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree (7a8a4eb): `lake env lean docs/tickets/checks/T2284-check.lean`.
-/
import RBM3D.Induction.QtNonzero
import RBM3D.Induction.NQEndLin
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.NQLin
import RBM3D.Induction.NQGood1
import RBM3D.Induction.NQBudget
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.GridDriftN
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.AzumaProxyN
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Defs
import RBM3D.Induction.NewPQ
import RBM3D.Loop.KLFinal
import RBM3D.Green.Pins
import RBM3D.Evolution.Nonzero

/-! ## 1. Merged names (private helpers of `NQEndLin`, `NQEndFlow`, `QtNonzero` cannot be `#check`ed; the ticket
copies them, it does not call them) -/

-- S3-21 (`Induction/QtNonzero`, 95d8b2a): the data of the bundle and the budget
#check @RBM.zeroModeSet_idem
#check @RBM.Ind.cQVNZN
#check @RBM.Ind.assembledRHSNZN
#check @RBM.Ind.nzUgen_holds
#check @RBM.Ind.nz_hker
#check @RBM.Ind.nz_hdriftN
#check @RBM.Ind.subGaussStop_nzN
#check @RBM.Ind.yMomentBounds_nzN
#check @RBM.Ind.budgetNZN
#check @RBM.Ind.QtNonzeroInst.idem_instance
#check @RBM.Ind.QtNonzeroInst.nzUgen_instance
#check @RBM.Ind.QtNonzeroInst.subGaussStop_nz_instance
#check @RBM.Ind.QtNonzeroInst.yMoment_zero_instance
#check @RBM.Ind.QtNonzeroInst.budgetNZN_instance
-- `Q^{(A)}`, its linearity, `(normQA2)`, the commutation, `(iisuwjyys)` on the grid (`Kernel/Evolution`,
-- `Induction/ZeroModeCalc`)
#check @RBM.zeroModeSet
#check @RBM.zeroModeSet_add
#check @RBM.zeroModeSet_smul
#check @RBM.zeroModeSetLin
#check @RBM.zeroModeSet_sub
#check @RBM.zeroModeSet_sum
#check @RBM.norm_zeroModeSet_le
#check @RBM.Ind.Ugen_eq_UN_EKsgn
#check @RBM.Ind.zeroModeSet_Ugen
#check @RBM.Ind.zeroModeCalc_duhamel_inside_at
#check @RBM.ekSumDecayNonzero_holds
-- the owed target, the R2* pins, the regime (`Induction/NQEndFlow`, `Induction/Step34Pins`)
#check @RBM.Gauss.Sizes.STOeqQtNZ'
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Gauss.Sizes.STNQConclPT''
#check @RBM.Gauss.Sizes.STOeqNQPT''
#check @RBM.Ind.stOeqNQPT''_holds
#check @RBM.Ind.nqFlowLam
#check @RBM.Ind.nqFlowPhiC
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STIdiff
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.stNewPQ_holds
#check @RBM.Gauss.Sizes.zeroModeCalc_LK_expansion_empty
-- the sizes, the window, the regime (`Defs/Sizes`, `Green/Pins`, `Induction/Defs`, `Loop/KLFinal`, `ScaleFacts`)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.stKbound_holds
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.Gauss.etaT
#check @RBM.mE
#check @RBM.Zd
-- the grid walk (`Path/Walk`, `Induction/Step2Events`)
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.pathH
#check @RBM.Path.gridTime_last
#check @RBM.Path.map_pathH_eq
#check @RBM.Gauss.Sizes.ST_gridTime_zero
#check @RBM.Gauss.Sizes.ST_gridTime_mono
#check @RBM.Gauss.Sizes.ST_gridStep_nonneg
-- loops (`Induction/Step2Defs`)
#check @RBM.Gauss.Sizes.STLKM
-- the good sets, exit times, good events (`Induction/GridGoodN`, `Induction/NQLin`)
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.measurableGoodSetN
#check @RBM.Gauss.Sizes.GridGoodNConcl
#check @RBM.Gauss.Sizes.gridGoodN_holds
#check @RBM.Path.gridExitTauN
#check @RBM.Path.gridExitTauN_eq_of_forall_mem
#check @RBM.Gauss.Sizes.GoodLinN
#check @RBM.Gauss.Sizes.measurableGoodLinN
#check @RBM.Gauss.Sizes.nqLinPhi1
#check @RBM.Gauss.Sizes.nqLinPhi2
#check @RBM.Gauss.Sizes.nqLinPhi3
#check @RBM.Gauss.Sizes.NQLinConcl
#check @RBM.Gauss.Sizes.nqLinGood_holds
#check @RBM.Ind.dDriftLinN
#check @RBM.Ind.nqLinExitTauN
#check @RBM.Ind.mem_of_lt_nqLinExitTauN
#check @RBM.Ind.nqLinExitMeasN
#check @RBM.Ind.nqLin_hdriftN
-- the Duhamel identity, the step decomposition, drift, envelope (`GridDuhamelN`, `StepDecompN`, `NQGood1`,
-- `GridDriftN`, `GridEnvelopeN`, `NQBudget`)
#check @RBM.Ind.Ugen
#check @RBM.Ind.GridDuhamelN_Ugen_add
#check @RBM.Ind.AvecN
#check @RBM.Ind.martIncN
#check @RBM.Ind.predIncN
#check @RBM.Ind.stoppedDuhamelN_at
#check @RBM.Ind.ZvecN
#check @RBM.Ind.YvecN
#check @RBM.Ind.stoppedEdgeN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.driftTensorN
#check @RBM.Ind.nqGood1_mE_im_ge
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.stepErrN
#check @RBM.Ind.gridDriftN_envelope
#check @RBM.Ind.sum_gridStep_div_etaT_le
#check @RBM.Ind.nqBudget_merged_inputs
-- the assembly (`Induction/GridAssemblyN`) and the uniform `Y` moments (`Induction/AzumaProxyN2`)
#check @RBM.Ind.YMomentBoundsN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.assembledN
#check @RBM.Ind.gridAsm_stronglyMeasurable_ZvecN
#check @RBM.Ind.YMomentsUnifN
#check @RBM.Ind.yMomentsUnifN
-- the format model (S3-12b, `Induction/NQEndLin`) and its instance grid
#check @RBM.Ind.nqGridEndLinN
#check @RBM.Ind.NQEndLinInst.KC
#check @RBM.Ind.NQEndLinInst.KC_ne_zero
#check @RBM.Ind.NQEndLinInst.KC_low
#check @RBM.Ind.NQEndLinInst.KC_up
-- instance data (case (ii) window at `szB`: `L = 4`, `W = n + 4`, `ilambda = 1`, `(s, t) = (15/16, 31/32)`)
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.szB_size_ge
#check @RBM.Gauss.Step34Inst.szB_tendsto
#check @RBM.Gauss.Step34Inst.szB_bandwidth
#check @RBM.Gauss.Step34Inst.szB_WO
#check @RBM.Gauss.Step34Inst.szB_caseII
#check @RBM.Ind.AzumaProxyNInst.Einst
#check @RBM.Ind.AzumaProxyNInst.Einst_abs_lt
#check @RBM.Ind.AzumaProxyNInst.sig3

/-! ## 2. The pinned statement (T2284 proves `RBM.Ind.nzGridEndN` with exactly this type; the theorem is
checked by `example : RBM.Ind.T2284Check.T2284_nzGridEndN := @RBM.Ind.nzGridEndN`) -/

namespace RBM.Ind.T2284Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-- **`nzGridEndN`: the case-(ii) grid endpoint of the zero-mode-removed loops** (`lem:STOeq_Qt_nonzero`,
`3_5:1561`, proof `3_5:1889-1928`: `(sahwNQ_smalleta)` `:1903`, `(sahwNQ2)` `:1910`, `(am;asoiuw_smalleta)`
`:1916`; `(iisuwjyys)` `3_5:1545`; shape of `T2199_nqGridEndLinN`, `NQEndLin.lean:1067`).  Setting: `3 ≤ d`,
constants `κ, 𝔠, τ, 𝔡 > 0`, `N → ∞`, `W ≥ N^𝔠`, `(eq:WO)`, `|E| ≤ 2 - κ`, `0 ≤ s ≤ t < 1`, case (ii)
`1 - s ≤ g²/L²`, `1 - t ≥ N^{-1+τ}` (no `W⁻¹ ≤ (1-t)/(1-s)`: EK-5 has no such window).  For every length `k ≥ 2`,
deterministic levels `Λ ≥ 0` (`≥ 1` eventually), `Φ₁, Φ₂, Φ₃ ≥ 0`, end time `v ∈ [s,t]`, final loss `ε₀ > 0` and
failure exponent `D₁ > 0` there are exponents `ε₁, τ', D', C_K` such that, for every crude level `Φc` of
`GoodSetN` and every grid `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`, eventually there is an event `G`, `P(Gᶜ) ≤ N^{-D₁}`, on
which: if the grid walk is in `GoodSetN(N^{ε₁}, Λ, Φc, τ', D') ∩ GoodLinN(N^{ε₁}, Φ₁, Φ₂, Φ₃)` at every `j ≤ K_n`
and the initial zero-mode-removed loops satisfy `|(Q^{(A)}(𝓛-𝒦))_{s,σ,a}| ≤ N^{ε₁} B_s^k` for every `σ` and
`A ⊇ I_diff(σ)`, then `|(Q^{(A)}(𝓛-𝒦))_{v,σ,a}(H_{K_n})| ≤ N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k` for every `σ`,
every `A ⊇ I_diff(σ)` and every label `a`.  No `Φ²`, no `Φc` on the right side; no `STKbound` premise
(`stKbound_holds` discharges it). -/
def T2284_nzGridEndN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseII s t → sz.RangeCond τ t →
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
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd d (sz.L n),
              ‖zeroModeSet d (sz.L n) A
                  (fun b : Fin k → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd d (sz.L n),
              ‖zeroModeSet d (sz.L n) A
                  (fun b : Fin k → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                  (sz.Bctl n (v n)) ^ k

/-! ## 3. Shape examples (Prop-valued, no proof obligations) -/

-- The pin is a `Prop` (the statement script checks `@RBM.Ind.nzGridEndN` against it).
example : Prop := T2284_nzGridEndN

-- The final consumer of the S3-22 chain (S3-22c): the owed primed pin at `d = 3`.
example : Prop := RBM.Gauss.Sizes.STOeqQtNZ' 3

-- The case-(ii) window of the instance (merged `szB_caseII`).
example : Prop := RBM.Gauss.Sizes.STCaseII RBM.Gauss.Step34Inst.szB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- The object of the conclusion at the terminal grid index is `Q^{(A)} (AvecN … (K n))` after `gridTime_last`.
example {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (σ : Fin k → Bool)
    (A : Finset (Fin k)) (ω : PathΩ sz) : Prop :=
  zeroModeSet d (sz.L n) A (AvecN sz E s v K n (K n) σ ω) =
    zeroModeSet d (sz.L n) A
      (fun b : Fin k → Zd d (sz.L n) => sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b)

end RBM.Ind.T2284Check
