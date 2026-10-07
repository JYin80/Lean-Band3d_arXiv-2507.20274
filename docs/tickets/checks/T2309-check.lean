/-
T2309 (UN-24, `Universality/UnivMain`) check file: pin texts, `#check`s of merged names, statements of the
targets as `Prop` defs.  No proofs.  Compiles on `main` (4db5994) as is.
-/
import RBM3D.Universality.Apriori
import RBM3D.Universality.GreenCorr
import RBM3D.Universality.EigenMeasurable
import RBM3D.Universality.PinsK
import RBM3D.Universality.PinsDens
import RBM3D.Universality.GUETranslation
import RBM3D.Universality.JakKernel
import RBM3D.Universality.EMCTE2
import RBM3D.Universality.Uyw
import RBM3D.Path.Walk
import RBM3D.Induction.Split

open MeasureTheory Filter Topology
open RBM RBM.Gauss RBM.Gauss.Sizes

namespace RBM.Univ.T2309Check

/-! ## 1. Merged names used (every one on `main` at 4db5994) -/

-- the pins and rows (`Pins.lean`, f8ad4b4)
#check @RBM.Univ.UNUnivMainRow          -- Pins.lean:745 (owed, Axioms.lean:206)
#check @RBM.Univ.UNClaimRow             -- Pins.lean:815 (owed, Axioms.lean:207)
#check @RBM.Univ.UNUnivMain             -- Pins.lean:563
#check @RBM.Univ.UNClaimAll             -- Pins.lean:516
#check @RBM.Univ.UNClaim417             -- Pins.lean:508
#check @RBM.Univ.UNGreenCorr            -- Pins.lean:535
#check @RBM.Univ.UNGreenCorrAll         -- Pins.lean:546
#check @RBM.Univ.UNApriori              -- Pins.lean:522
#check @RBM.Univ.UNDens                 -- Pins.lean:462
#check @RBM.Univ.UNTrLocal              -- Pins.lean:447
#check @RBM.Univ.UNEMCTE2               -- Pins.lean:669
#check @RBM.Univ.UNJak                  -- Pins.lean:694
#check @RBM.Univ.UNUyw                  -- Pins.lean:708
#check @RBM.Univ.L1t                    -- Pins.lean:617
#check @RBM.Univ.L2t                    -- Pins.lean:624
#check @RBM.Univ.scirc                  -- Pins.lean:612
#check @RBM.Univ.InWindow               -- Pins.lean:501
#check @RBM.Univ.ouTStar                -- Pins.lean:142
#check @RBM.Univ.Nsz                    -- Pins.lean:372
#check @RBM.Univ.kPoint                 -- Pins.lean:77
#check @RBM.Univ.stieltjesN             -- Pins.lean:88
#check @RBM.Univ.ouP                    -- Pins.lean:145
#check @RBM.Univ.ouMat                  -- Pins.lean:150
#check @RBM.Univ.ouMat_isHermitian      -- Pins.lean:154
#check @RBM.Univ.ouMat_zero             -- Pins.lean:160
#check @RBM.Univ.UNModel                -- Pins.lean:104
#check @RBM.Univ.UNModel.band           -- Pins.lean:116
#check @RBM.Univ.un_core_of_rows        -- Pins.lean:772
#check @RBM.Univ.un_claimAll_of_rows    -- Pins.lean:849
#check @RBM.Univ.UNInst.sz0_adm         -- Pins.lean:1518
#check @RBM.Univ.UNInst.bump            -- Pins.lean:1502
#check @RBM.Univ.UNInst.bump_testFun    -- Pins.lean:1504
#check @RBM.Univ.un_dens_msc_zero       -- Pins.lean:1455
-- the model-generic rows (`PinsK.lean`, fdbb6f0)
#check @RBM.Univ.UNKind                 -- PinsK.lean:307
#check @RBM.Univ.UNKind.band            -- PinsK.lean:315
#check @RBM.Univ.UNModelC               -- PinsK.lean:55
#check @RBM.Univ.ouMatC                 -- PinsK.lean:69
#check @RBM.Univ.ouMatC_isHermitian     -- PinsK.lean:79
#check @RBM.Univ.ouMatC_eq_ouMat_add    -- PinsK.lean:100
#check @RBM.Univ.UNClaim417C            -- PinsK.lean:150
#check @RBM.Univ.UNClaimAllC            -- PinsK.lean:158
#check @RBM.Univ.UNEMCTE2k              -- PinsK.lean:345
#check @RBM.Univ.UNJakk                 -- PinsK.lean:365
#check @RBM.Univ.UNUywk                 -- PinsK.lean:378
#check @RBM.Univ.UNClaimRowk            -- PinsK.lean:442 (owed, Axioms.lean:223)
#check @RBM.Univ.UNClaimRowk_band       -- PinsK.lean:573
-- `PinsDens.lean` (3fc9d03), `GUETranslation.lean` (dc2d99b)
#check @RBM.Univ.UNCore'                -- PinsDens.lean:99
#check @RBM.Univ.un_core_of_rows'       -- PinsDens.lean:220
#check @RBM.Univ.un_infty1Row'          -- GUETranslation.lean:787
#check @RBM.Univ.un_core'_of_univMainRow -- GUETranslation.lean:791
-- the inputs (`Apriori` 95a50be, `GreenCorr` 0818c49, `EigenMeasurable`/`OU` a52eb85)
#check @RBM.Univ.unApriori_of_trLocal   -- Apriori.lean:149
#check @RBM.Univ.apriori_ouMat_zero_integral -- Apriori.lean:89
#check @RBM.Univ.apriori_im_bounds      -- Apriori.lean:49
#check @RBM.Univ.unGreenCorr            -- GreenCorr.lean:864
#check @RBM.Univ.greenCorrAll           -- GreenCorr.lean:873
#check @RBM.Univ.integral_kPoint_eq_of_map_eq -- EigenMeasurable.lean:458
#check @RBM.Univ.measurable_ouMat       -- OU.lean:80
#check @RBM.Univ.ouMat_zero_map         -- OU.lean:233
-- deterministic helpers
#check @RBM.Univ.stieltjesN_im_eq_normalized_specWeight -- InjSum.lean:196
#check @RBM.Univ.JakKernelInst.im_Gres_le_inv  -- JakKernel.lean:984
#check @RBM.Gauss.Gres                  -- Loop/GLoopFlow.lean:74
#check @RBM.Gauss.walk_measurable_Gres_apply -- Path/Walk.lean:737
#check @RBM.Ind.norm_apply_le_l2_opNorm -- Induction/Split.lean:670
#check @RBM.Gauss.Sizes.card_Idx        -- Defs/Sizes.lean:160
#check @RBM.Gauss.Sizes.Admissible      -- Defs/Sizes.lean:177
#check @RBM.Gauss.Sizes.SizeTendsto     -- Defs/Sizes.lean:173
-- the merged rows used by instance (d) (`EMCTE2` 061aa73, `Uyw` 44dd942)
#check @RBM.Univ.unEMCTE2Row            -- EMCTE2.lean:683
#check @RBM.Univ.jakUywRow              -- Uyw.lean:881
-- Mathlib
#check @MeasureTheory.integral_mono_of_nonneg
#check @MeasureTheory.Integrable.of_bound
#check @MeasureTheory.integral_finset_sum
#check @Finset.inf'_le
#check @Finset.lt_inf'_iff
#check @tendsto_rpow_atTop
#check @ge_of_tendsto
#check @le_of_tendsto

/-! ## 2. Target statements (the prover's theorems must have exactly these types) -/

/-- 2.1 Target 1 `unClaim417C_of_rows`: the arithmetic core, for every model class `K`
(RBM2D `UnivMain_claim417_of`, `UnivMain.lean:360`), `C_n' = C_n + C + 1`. -/
def T2309_unClaim417C_of_rows : Prop :=
  ∀ {d : ℕ} (K : UNKind d) (sz : Sizes d), sz.SizeTendsto →
    ∀ (E : ℝ) (nf : ℕ) (τU c' Cn C : ℝ), 0 < τU →
      UNEMCTE2k K sz E nf τU Cn → UNJakk K sz E nf τU C c' → UNUywk K sz E nf τU C c' →
        UNClaim417C sz (K.M sz) E nf τU c' (Cn + C + 1)

/-- 2.2 Target 2 `unClaimRowk`: the model-generic claim row (owed, `Axioms.lean:223`). -/
def T2309_unClaimRowk : Prop := ∀ K : ∀ d, UNKind d, UNClaimRowk K

/-- 2.3 Target 3 `unClaimRow`: the band claim row (owed, `Axioms.lean:207`). -/
def T2309_unClaimRow : Prop := UNClaimRow

/-- 2.4 Target 4 `unDens_rho_bounds`: the density sequence of `UNDens` is eventually in `[c/π, C/π]`. -/
def T2309_unDens_rho_bounds : Prop :=
  ∀ (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens m E ρ δ →
    ∃ a b : ℝ, 0 < a ∧ ∀ᶠ n in atTop, a ≤ ρ n ∧ ρ n ≤ b

/-- 2.5 Target 5 `univMain_transfer`: the `k`-point functional of the model equals that of `𝐇_0` (law transfer
at `t = 0`, every `O`, no measurability). -/
def T2309_univMain_transfer : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ),
    ∫ ω, kPoint k O E (M.herm n ω).eigenvalues ∂M.μ =
      ∫ ω, kPoint k O E (ouMat_isHermitian M n 0 ω).eigenvalues ∂(ouP M n)

/-- 2.6 Target 6 `univMainRow`: the row (owed, `Axioms.lean:206`). -/
def T2309_univMainRow : Prop := UNUnivMainRow

/-- 2.7 Target 7 `unCore'_holds`: the core pin `UNCore'` (consumer `un_core'_of_univMainRow`). -/
def T2309_unCore'_holds : Prop := UNCore'

/-! ## 3. Instance statements (namespace `RBM.Univ.UnivMainInst`; `d = 3`, `sz0`, `𝔠 = 1/6`, `𝔡 = 1/10`) -/

/-- 3.1 (a) target 6 at the band model, `m = msc`, `E = 0`, `δ = 1/2`, `k = 1`, `O = bump`; the owed `UNTrLocal`
and the claim `UNClaimAll` stay hypotheses, `UNGreenCorrAll` is discharged by `greenCorrAll`. -/
def T2309_inst_univMain_band_zero : Prop :=
  UNTrLocal RBM.Gauss.SizesInst.sz0 (UNModel.band RBM.Gauss.SizesInst.sz0) (fun _ => msc) 0 (1 / 2) →
    UNClaimAll RBM.Gauss.SizesInst.sz0 (UNModel.band RBM.Gauss.SizesInst.sz0) 0 →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNUnivMain RBM.Gauss.SizesInst.sz0 (UNModel.band RBM.Gauss.SizesInst.sz0) (fun _ => rhoSC 0) 0 1
          (RBM.Univ.UNInst.bump : (Fin 1 → ℝ) → ℝ) τU

/-- 3.2 (b) target 1 at `sz0`, the band kind, `E = 0`, `nf = 2`, `τU = 1/4`, `c' = 1/1800`, `Cn = C = 1`. -/
def T2309_inst_claim417_core : Prop :=
  UNEMCTE2k (UNKind.band 3) RBM.Gauss.SizesInst.sz0 0 2 (1 / 4) 1 →
    UNJakk (UNKind.band 3) RBM.Gauss.SizesInst.sz0 0 2 (1 / 4) 1 (1 / 1800) →
      UNUywk (UNKind.band 3) RBM.Gauss.SizesInst.sz0 0 2 (1 / 4) 1 (1 / 1800) →
        UNClaim417C RBM.Gauss.SizesInst.sz0 ((UNKind.band 3).M RBM.Gauss.SizesInst.sz0) 0 2 (1 / 4) (1 / 1800) 3

/-- 3.3 (c) the band chain: target 3 with the merged `unEMCTE2Row`, `jakUywRow`: the claim at `sz0`, `E = 0` from
the two owed inputs `UNLocAvgBand`, `UNOUClaims` only. -/
def T2309_inst_claimAll_band_zero : Prop :=
  UNLocAvgBand → UNOUClaims → UNClaimAll RBM.Gauss.SizesInst.sz0 (UNModel.band RBM.Gauss.SizesInst.sz0) 0

/-- 3.4 (d) target 4 at `msc`, `E = 0`, `δ = 1/2` (`un_dens_msc_zero`). -/
def T2309_inst_rho_bounds_zero : Prop :=
  ∃ a b : ℝ, 0 < a ∧ ∀ᶠ n in atTop, a ≤ (fun _ : ℕ => rhoSC 0) n ∧ (fun _ : ℕ => rhoSC 0) n ≤ b

end RBM.Univ.T2309Check
