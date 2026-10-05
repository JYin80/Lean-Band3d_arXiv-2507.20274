/-
Release check for T2180 (dispatcher V1, Mon Oct  5 06:06 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §28, §29, §36, §45 O2, §53).
ST2-13a: the plain martingale tail `GridRepTailNAt d m` (clause (iii) of `STGridRepNAt` for the merged
`difRepMartN`, T2168) at every loop length `m ≥ 2`, by an Azuma bound with a random predictable proxy; with
the merged `stGridMart_of_tail` it makes `STGridMart d` (and `STGridMartAt d 11`) unconditional for `3 ≤ d`.
Section 1: the merged names it builds on (`Path/DifREP1`, `Induction/{StepDecompN,AzumaProxyN,AzumaProxyN2,
GridAssemblyN,QVN,NQGood1,LoopC2N,Split,Step2Defs,Step2Iterate,OptL2b}`, `Path/{Markov,Azuma,Walk,Stop}`,
`Defs/Block`, Mathlib, the instance data) and the downstream consumers.  Section 2: the pinned statements of
the targets as `Prop`s (elaboration check only; each target theorem's type is the body of its `…Stmt`).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2180-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- T2168 (`Path/DifREP1`, 3df1812): vocabulary, the owed tails, the interface, the assembly
#check @RBM.Ind.difRepMartN
#check @RBM.Ind.difRepRemN
#check @RBM.Ind.GridRepRemNAt
#check @RBM.Ind.GridRepTailNAt
#check @RBM.Ind.GridRepWTailNAt
#check @RBM.Ind.difRep_identity
#check @RBM.Ind.difRepMartN_succ_sub
#check @RBM.Ind.difRep_Ugen_step_le
#check @RBM.Ind.difRep_flow_bounds
#check @RBM.Ind.gridRepRemN_holds
#check @RBM.Ind.stGridRepNAt_of_parts
#check @RBM.Ind.stGridRepN_of_tails
#check @RBM.Ind.stGridMartAt_of_parts2
#check @RBM.Ind.stGridMart_of_tail
-- the increment `ξ = Z + Y` and the first-chaos machinery (`Induction/StepDecompN`, T2121; `GridDuhamelN`)
#check @RBM.Ind.martIncN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.YvecN
#check @RBM.Ind.ZvecN_eq_stepZCN
#check @RBM.Ind.YvecN_eq_stepYCN
#check @RBM.Ind.loopFamN
#check @RBM.Ind.AbCN
#check @RBM.Ind.stepZCN
#check @RBM.Ind.dirDerivN
#check @RBM.Ind.StepDecompCN_Stmt
#check @RBM.Ind.stepDecompCN
#check @RBM.Ind.stepDecompCN_Z_subG
-- deterministic-proxy sub-Gaussian step and the `Y` moments (`AzumaProxyN` T2159, `AzumaProxyN2` T2160)
#check @RBM.Ind.AzumaSubGN
#check @RBM.Ind.azumaSubGN
#check @RBM.Ind.YMomentsUnifN
#check @RBM.Ind.yMomentsUnifN
#check @RBM.Ind.AzumaProxyN_stopW
#check @RBM.Ind.AzumaProxyN_YfieldsW
#check @RBM.Ind.gridAsm_stronglyMeasurable_ZvecN
#check @RBM.Ind.gridAsm_stronglyMeasurable_YvecN
#check @RBM.Ind.HermTestFunLoopN
#check @RBM.Ind.hermTestFunLoopN
-- the quadratic-variation proxy and its time shift (`QVN` T2103, `NQGood1` T2166)
#check @RBM.Ind.QVPropagatedN
#check @RBM.Ind.qvPropagatedN
#check @RBM.Ind.qvFormN_eq_re_UgenPairN
#check @RBM.Ind.UgenPairN
#check @RBM.Ind.norm_STeeM_shiftN_le
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.loopShiftErrN
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STeeUM
#check @RBM.Gauss.Sizes.STLIM
#check @RBM.Gauss.Sizes.STeeLoop
#check @RBM.Ind.norm_gloop_le_of_le_abs_im
#check @RBM.sum_norm_SB_row
-- Gaussian conditional mgf, Azuma, Doob (`Path/Markov`, `Path/Azuma`, T2021); walk measurability
#check @RBM.Path.condExp_freeze
#check @RBM.Path.linTr
#check @RBM.Path.linTrVar
#check @RBM.Path.linTrVar_nonneg
#check @RBM.Path.map_linTr_seqXmat
#check @RBM.Path.hasCondSubgaussianMGF_linear
#check @RBM.Path.azuma_two_sided
#check @RBM.Path.azuma_complex
#check @RBM.Path.doob_L2_max
#check @RBM.Path.martingale_sq_eq_sum
#check @RBM.Path.stopped_martingale
#check @RBM.Path.pathH_measurable_filt
#check @RBM.Path.pathH_isHermitian
#check @RBM.Gauss.walk_measurable_loopL
#check @RBM.Gauss.walk_measurable_blockMat
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.pathH
#check @RBM.Path.pathP
#check @RBM.Path.filt
-- flow
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.SizeTendsto
-- Mathlib (grep in `.lake/packages/mathlib`)
#check @MeasureTheory.martingale_of_condExp_sub_eq_zero_nat
#check @MeasureTheory.condExp_mul_of_stronglyMeasurable_left
#check @MeasureTheory.integral_condExp
#check @MeasureTheory.ofReal_measureReal
#check @ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.sixteenth_le_lemT
-- downstream (consumers of `GridRepTailNAt`, `STGridMart`, `STGridMartAt`)
#check @RBM.Gauss.Sizes.STGridMartAt
#check @RBM.Gauss.Sizes.STGridMart
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Gauss.Sizes.ST_gridMart_of_repN
#check @RBM.Gauss.Sizes.ST_selfImprove_section
#check @RBM.Gauss.Sizes.ST_step2_of_pins'
#check @RBM.Gauss.Sizes.stOptL2_of_pins
#check @RBM.Gauss.Sizes.STLWB
#check @RBM.Gauss.Sizes.STOptL2
#check @RBM.Gauss.Sizes.STNewKLK
#check @RBM.Gauss.Sizes.STLWT
#check @RBM.Gauss.Sizes.STEMn2Exp
#check @RBM.Gauss.Sizes.STLocalAvgOfL2
#check @RBM.Gauss.Sizes.STStep2

/-! ## 2. Pinned statements (T2180 targets 1-4; elaboration only) -/

noncomputable section

namespace RBM.Ind.T2180Check

open MeasureTheory ProbabilityTheory Filter RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-- Target 1, `azumaRandProxy_max` (model-free): **the maximal Azuma bound with a random predictable
proxy.**  Increments `ζ_j` (`F_{j+1}`-measurable) with `𝔼[e^{r ζ_j} | F_j] ≤ e^{r² v_j / 2}` for an
`F_j`-measurable proxy `0 ≤ v_j ≤ B`, switched on by `F_j`-measurable sets `G_j`; if the switched proxy
sums to at most `V` on every path, the running maximum of the switched sum exceeds `x` with probability
at most `e^{-x²/(2V)}`, uniformly in the horizon `K`. -/
def AzumaRandProxyMaxStmt : Prop :=
  ∀ {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω') [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ') (ζ v : ℕ → Ω' → ℝ) (G : ℕ → Set Ω') (K : ℕ) (B V x : ℝ),
    (∀ j < K, StronglyMeasurable[ℱ (j + 1)] (ζ j)) →
    (∀ j < K, StronglyMeasurable[ℱ j] (v j)) →
    (∀ j < K, MeasurableSet[ℱ j] (G j)) →
    (∀ j < K, ∀ ω, 0 ≤ v j ω ∧ v j ω ≤ B) →
    (∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * ζ j ω)) μ) →
    (∀ j < K, ∀ r : ℝ,
      μ[fun ω => Real.exp (r * ζ j ω) | ℱ j] ≤ᵐ[μ] fun ω => Real.exp (r ^ 2 * v j ω / 2)) →
    (∀ ω, ∑ j ∈ Finset.range K, (G j).indicator (v j) ω ≤ V) → 0 < V → 0 ≤ x →
    μ.real {ω | ∃ k, k ≤ K ∧ x ≤ ∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω} ≤
      Real.exp (-x ^ 2 / (2 * V))

/-- Target 2, `difRepTail_condMGF_Z`: **the conditional mgf of a weighted first-chaos increment, with
its random proxy.**  For weights `κ`, the real and imaginary parts of `Σ_b κ_b Z_{j,b}` (`Z = ZvecN`,
the step `j → j+1`) are exponentially integrable and have conditional mgf at most
`exp(r² Δ k Re Σ_{b,b'} κ_b conj(κ_{b'}) (𝓔⊗𝓔)_{u_{j+1}}(H_j)_{σ,b,b'} / 2)` given `F_j`
(the Gaussian mgf with the variance `Δ linTrVar` of the frozen gradient, bounded by `qvPropagatedN`). -/
def DifRepTailCondMGFZStmt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ),
    |E n| < 2 → 0 ≤ s n → s n ≤ t n → t n < 1 → j + 1 ≤ K n →
    ∀ {k : ℕ}, 2 ≤ k → ∀ (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ) (r : ℝ),
      Integrable (fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).re)) (pathP sz) ∧
      Integrable (fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).im)) (pathP sz) ∧
      (pathP sz)[fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).re) | filt sz j]
        ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * ((k : ℝ) *
          (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n), κ b * (starRingEnd ℂ) (κ b') *
            sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re)) / 2)) ∧
      (pathP sz)[fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).im) | filt sz j]
        ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * ((k : ℝ) *
          (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n), κ b * (starRingEnd ℂ) (κ b') *
            sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re)) / 2))

/-- Target 3, `gridRepTailN_holds`: the owed plain tail (clause (iii) of `STGridRepNAt` for
`difRepMartN`) at every loop length `m ≥ 2`, every `d`. -/
def GridRepTailNHoldsStmt : Prop :=
  ∀ d m : ℕ, 2 ≤ m → GridRepTailNAt d m

/-- Target 4, `stGridMart_holds`: the pin `STGridMart` (Step 2 martingale input), unconditional for `3 ≤ d`
(`stGridMart_of_tail` + target 3 at `m = 2`). -/
def StGridMartHoldsStmt : Prop :=
  ∀ d : ℕ, 3 ≤ d → STGridMart d

/-- Target 4, `stGridMartAt_holds`: the loop-length-`2` pin at the explicit constant `C₀ = 2 + 9 = 11`
(`stGridMartAt_of_parts2` + `gridRepRemN_holds` at `m = 2` + target 3). -/
def StGridMartAtHoldsStmt : Prop :=
  ∀ d : ℕ, 3 ≤ d → STGridMartAt d 11

end RBM.Ind.T2180Check

end
