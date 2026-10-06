/-
Release check for T2266 (dispatcher V1, Tue Oct  6 06:30 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §48, §50, §54, §56, §57 (1)-(2), §64 (4), §65, §66, §69 B).
UN-18 (EMCTE2 half): the weighted `(EMCTE2)` from the OU generator identity (RBM2D paper 1-2:364-376, "argue as in
Step 3 of the proof of Theorem 2.6 in [YY_25]"): port of RBM2D `Universality/EMCTE2.lean` (c9a24cf, 726 lines) to
the band carrier `ouP (UNModel.band sz) n`, `ouMat (UNModel.band sz) n`, kernels `L1t`/`L2t` at `sz.lam n`
(`Pins.lean:617, 624`, read by `UNEMCTE2` at `:675-676, 680-681`).
Route: UN-15 B2 (`ouGenerator_integral_sub_eq`, `OUGenerator.lean:1073`) at `T` and at `t` with
`Φ = ∏ Im m` (UN-15 S, `:1272`), the pointwise kernel bound UN-17 (`OUContraction.lean:1077`) at
`H = ouMat (UNModel.band sz) n s ω`, `lam = sz.lam n`; then the arithmetic `½ nf² (t* - t) B ≤ N^ε N^{-1+Cn τU} B`.
Section 1: merged names.  Section 2: the statements `def T2266_<name> : Prop` (the library states `<name>` in
namespace `RBM.Univ`, instances in `RBM.Univ.EMCTE2Inst`, with exactly this statement; binder names may differ).
Section 3: downstream (information only).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2266-check.lean`.
-/
import RBM3D
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, f8ad4b4; namespace `RBM.Univ`; `UNInst` = `:1497-1898`)
#check @RBM.Univ.stieltjesN                    -- :88
#check @RBM.Univ.UNModel.band                  -- :116
#check @RBM.Univ.ouTStar                       -- :142
#check @RBM.Univ.ouP                           -- :145
#check @RBM.Univ.ouMat                         -- :150
#check @RBM.Univ.ouMat_isHermitian             -- :154
#check @RBM.Univ.Nsz                           -- :372
#check @RBM.Univ.InWindow                      -- :501
#check @RBM.Univ.scirc                         -- :612
#check @RBM.Univ.L1t                           -- :617
#check @RBM.Univ.L2t                           -- :624
#check @RBM.Univ.UNEMCTE2                      -- :669 (target pin, owed; Axioms.lean:205)
#check @RBM.Univ.UNEMCTE2Row                   -- :797 (target row, owed; Axioms.lean:213)
#check @RBM.Univ.UNClaimRow                    -- :815 (consumer of `UNEMCTE2`)
#check @RBM.Univ.un_claimAll_of_rows           -- :849 (consumer of `UNEMCTE2Row`)
#check @RBM.Univ.UNInst.sz0_adm                -- :1518
#check @RBM.Univ.UNInst.un_emcte2_zero         -- :1835 (`nf = 0`; RBM2D `PinsCheck.emcte2_zero`)
-- UN-02a (`Universality/OU.lean`, T2177, a52eb85)
#check @RBM.Univ.isProbabilityMeasure_ouP      -- :44
#check @RBM.Univ.measurable_ouMat              -- :80
-- UN-15 (`Universality/OUGenerator.lean`, T2261, a1d865a)
#check @RBM.Univ.TestFunH                      -- :68
#check @RBM.Univ.ouPairP                       -- :77
#check @RBM.Univ.ouPairMat                     -- :81
#check @RBM.Univ.ouMat_band_eq_ouPairMat       -- :1002 (T1, `rfl`)
#check @RBM.Univ.ouP_band_map_pair             -- :1011 (T2)
#check @RBM.Univ.ouGenerator_hasDerivAt_integral  -- :1057 (B1)
#check @RBM.Univ.ouGenerator_integral_sub_eq   -- :1073 (B2)
#check @RBM.Univ.testFunH_stieltjesImProduct   -- :1272 (S)
-- UN-16 (`Universality/OUHessian.lean`, T2247, 398ebe4)
#check @RBM.Univ.wirtSecond                    -- :216
#check @RBM.Univ.centeredVarianceEntry         -- :1115
#check @RBM.Univ.paperL1Kernel_eq_L1t          -- :1150
#check @RBM.Univ.paperL2Kernel_eq_L2t          -- :1157
-- UN-17 (`Universality/OUContraction.lean`, T2253, a18620d)
#check @RBM.Univ.centeredVariance_wirtProduct_kernel_bound_Lt  -- :1077
-- UN-01b (`Universality/PinsK.lean`, T2187, fdbb6f0)
#check @RBM.Univ.UNKind.band                   -- :315
#check @RBM.Univ.UNEMCTE2k                     -- :345
#check @RBM.Univ.UNEMCTE2Rowk                  -- :429
#check @RBM.Univ.un_claimAll_of_rowsk_band     -- :580 (consumer of target 4)
#check @RBM.Univ.UNEMCTE2k_band                -- :534 (band bridge, `↔`)
-- BA-C1b (`BA/UNPins.lean`, T2241, 88d7676): not a target (section 3)
#check @RBM.Univ.UNModelC.ba                   -- :64
#check @RBM.Univ.UNKind.ba                     -- :84
#check @RBM.Univ.UNEMCTE2RowBA                 -- :128
-- UN-03a (`Universality/InjSum.lean`, T2178, 4c52041): `Im m ≥ 0` (RBM2D `:197-205` uses the same lemma)
#check @RBM.Univ.stieltjesN_im_eq_normalized_specWeight  -- :196
-- Resolvent bounds and measurability (RBM2D `EMCTE2_*` section 2 inputs, `Gres` form)
#check @RBM.Gauss.Gres                         -- Loop/GLoopFlow.lean:74 (868b3b4)
#check @RBM.Gauss.norm_Gsig_le_inv_eta         -- Gauss/FlowCalculus.lean:644 (6f99812)
#check @RBM.Gauss.walk_measurable_Gres_apply   -- Path/Walk.lean:737 (ddf5f74)
#check @RBM.Ind.norm_apply_le_l2_opNorm        -- Induction/Split.lean:670 (aa42e43)
-- Sizes (`Defs/Sizes.lean`, `Gauss/FineModel.lean`, T2006, 0a873f1)
#check @RBM.Gauss.Sizes.size                   -- Defs/Sizes.lean:157
#check @RBM.Gauss.Sizes.SizeTendsto            -- :173 (structural, Axioms.lean:280)
#check @RBM.Gauss.Sizes.Admissible             -- :177
#check @RBM.Gauss.SizesInst.sz0                -- :260
#check @RBM.Gauss.SizesInst.sz0_tendsto        -- :300
#check @RBM.Gauss.SizesInst.sz0_admissible     -- :331
#check @RBM.Gauss.Sizes.slice                  -- Gauss/FineModel.lean:176
#check @RBM.Gauss.Sizes.measurable_slice       -- :178
#check @RBM.Gauss.continuous_Xmat              -- :427
-- Downstream (UN-01c, `Universality/PinsDens.lean`, T2201, 3fc9d03)
#check @RBM.Univ.un_core_of_rows'              -- :220
#check @RBM.Univ.un_bUniv_of_rows'             -- :233 (takes `rE : UNEMCTE2Row`)
-- Mathlib (route)
#check @integral_ofReal
#check @MeasureTheory.integral_finsetSum
#check @MeasureTheory.integrable_finsetSum
#check @intervalIntegral.norm_integral_le_of_norm_le_const_ae
#check @intervalIntegral.integral_add_adjacent_intervals
#check @Real.rpow_le_rpow_of_exponent_le
#check @tendsto_rpow_atTop

/-! ## 2. Statements -/

noncomputable section

namespace RBM.Univ.T2266Check

open MeasureTheory Matrix Filter ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst
open scoped NNReal

/-! ### 2.1 Target 1: `eq225_interval` (RBM2D `EMCTE2.lean:440`), band carrier, at a fixed size `n` -/

/-- On `[t, T]`, `0 ≤ t ≤ T`, a bound `Bd` on the expected weighted kernel sum along the band OU flow bounds the
change of `E ∏ Im m` by `½ (T - t) Bd`.  Hypotheses on the spectral parameters: `0 < Im z_i` only. -/
def T2266_eq225_interval : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n nf : ℕ) (z : Fin nf → ℂ), (∀ i : Fin nf, 0 < (z i).im) →
    ∀ t T Bd : ℝ, 0 ≤ t → t ≤ T →
      (∀ s ∈ Set.Ioo t T,
        ∫ ω, ((∑ i : Fin nf, (∏ j ∈ Finset.univ.erase i,
                (stieltjesN (ouMat (UNModel.band sz) n s ω) (z j)).im) *
                L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i)) +
              ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i,
                (∏ k ∈ (Finset.univ.erase i).erase j,
                  (stieltjesN (ouMat (UNModel.band sz) n s ω) (z k)).im) *
                L2t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i) (z j))
          ∂(ouP (UNModel.band sz) n) ≤ Bd) →
      |(∫ ω, ∏ i : Fin nf, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z i)).im
            ∂(ouP (UNModel.band sz) n)) -
        ∫ ω, ∏ i : Fin nf, (stieltjesN (ouMat (UNModel.band sz) n T ω) (z i)).im
            ∂(ouP (UNModel.band sz) n)| ≤
        (1 / 2) * (T - t) * Bd

/-! ### 2.2 Target 2: the pin `UNEMCTE2` (`Pins.lean:669`) at every size sequence with `N → ∞` -/

/-- `UNEMCTE2 sz E nf τU Cn` whenever `N → ∞` and `τU ≤ Cn τU` (e.g. `Cn = 1`, any `τU`; or `Cn ≥ 1`, `τU ≥ 0`).
`E` is unused (the window gives `Im z_i ≥ N^{-1-τU} > 0`). -/
def T2266_unEMCTE2_of_sizeTendsto : Prop :=
  ∀ (d : ℕ) (sz : Sizes d), sz.SizeTendsto → ∀ (E : ℝ) (nf : ℕ) (τU Cn : ℝ), τU ≤ Cn * τU →
    UNEMCTE2 sz E nf τU Cn

/-! ### 2.3 Target 3: the row `UNEMCTE2Row` (`Pins.lean:797`; RBM2D `emcte2Row`, `EMCTE2.lean:567`) -/

def T2266_unEMCTE2Row : Prop := UNEMCTE2Row

/-! ### 2.4 Target 4: the model-generic row at the band kind (`PinsK.lean:429` at `UNKind.band`, via
`UNEMCTE2k_band`, `PinsK.lean:534`; the bulk premise is not used) -/

def T2266_unEMCTE2Rowk_band : Prop := UNEMCTE2Rowk (fun d => UNKind.band d)

/-! ### 2.5 Instances (namespace `RBM.Univ.EMCTE2Inst`; `sz0`: `d = 3`, `L = 4`, `W = 32` at `n = 0`) -/

/-- Target 1 at `sz0`, `n = 0`, `nf = 1`, `z = ![I]`, `t = 0`, `T = 1`, with the kernel hypothesis discharged
(RBM2D `EMCTE2Check.eq225_interval_instance`, `:686`). -/
def T2266_inst_eq225_interval : Prop :=
  ∃ Bd : ℝ,
    (∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, ((∑ i : Fin 1, (∏ j ∈ Finset.univ.erase i,
              (stieltjesN (ouMat (UNModel.band sz0) 0 s ω) (![Complex.I] j)).im) *
              L1t 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (ouMat (UNModel.band sz0) 0 s ω) (![Complex.I] i)) +
            ∑ i : Fin 1, ∑ j ∈ Finset.univ.erase i,
              (∏ k ∈ (Finset.univ.erase i).erase j,
                (stieltjesN (ouMat (UNModel.band sz0) 0 s ω) (![Complex.I] k)).im) *
              L2t 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (ouMat (UNModel.band sz0) 0 s ω)
                (![Complex.I] i) (![Complex.I] j))
        ∂(ouP (UNModel.band sz0) 0) ≤ Bd) ∧
    |(∫ ω, ∏ i : Fin 1, (stieltjesN (ouMat (UNModel.band sz0) 0 0 ω) (![Complex.I] i)).im
          ∂(ouP (UNModel.band sz0) 0)) -
      ∫ ω, ∏ i : Fin 1, (stieltjesN (ouMat (UNModel.band sz0) 0 1 ω) (![Complex.I] i)).im
          ∂(ouP (UNModel.band sz0) 0)| ≤
      (1 / 2) * (1 - 0) * Bd

/-- Target 2 at `sz0` (`sz0_tendsto`), `E = 0`, `nf = 2`, `τU = 1/2`, `Cn = 1`. -/
def T2266_inst_unEMCTE2_sz0 : Prop := UNEMCTE2 sz0 0 2 (1 / 2) 1

/-- Target 3 at `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `sz0` (`UNInst.sz0_adm`), `κ = 1/2`, `E = 1`, `nf = 2`. -/
def T2266_inst_unEMCTE2Row_sz0 : Prop := ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧ UNEMCTE2 sz0 1 2 τ₀ Cn

/-! ## 3. Downstream (information; not targets)

`UNEMCTE2Row` feeds `un_claimAll_of_rows` (`Pins.lean:849`) and `un_bUniv_of_rows'` (`PinsDens.lean:233`);
`UNEMCTE2` feeds `UNClaimRow` (`Pins.lean:815`, arithmetic row, UN-24); `UNEMCTE2Rowk (fun d => UNKind.band d)`
feeds `un_claimAll_of_rowsk_band` (`PinsK.lean:580`).  `UNEMCTE2RowBA` (`BA/UNPins.lean:128`) =
`UNEMCTE2Rowk (fun d => UNKind.ba d)` stays owed: the centred flow `ouMatC (UNModelC.ba sz)` =
`λΨ + e^{-t/2} V + √(1-e^{-t}) H'` holds the mean fixed, so it needs the mean shift `Φ ↦ Φ(λ_n Ψ + ·)` and the
carrier transfer for `UNModel.ba` (law `seqP (sz.withLam 0)`, `S°` at coupling `0` = `UNKind.ba`'s `lamV`), not
a drift term. -/

example : Prop := UNEMCTE2RowBA
example : Prop := UNEMCTE2Row → UNClaimRow

end RBM.Univ.T2266Check

end
