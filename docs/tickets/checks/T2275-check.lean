/-
Release check for T2275 (dispatcher V1, Tue Oct  6 08:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §48, §50, §54, §57 (1)-(2), §64 (4), §65, §66, §88 (2), §90).
UN-18b (Apriori half of UN-18): the a priori bound `UNApriori` (`Pins.lean:522`, RBM1D `AprioriImM`) from the
tracial local law `UNTrLocal` (`Pins.lean:447`, error `W^τ Bctl n (1 - Im z)`) and the density bounds `UNDens`
(`:462`) at admissible sizes: port of RBM2D `Universality/Apriori.lean` (c9a24cf, 424 lines, 378 kept; there from `locSC`
with `Meta`, here from `UNTrLocal` with `Bctl`, for every `M : UNModel sz`).
Route: law transfer `𝐇_0 = M.H n ∘ fst` (`ouMat_zero`, `Pins.lean:160`; `integral_fun_fst`); `0 ≤ Im m ≤ 1/η`
(`stieltjesN_im_eq_normalized_specWeight`, `InjSum.lean:196`); `η Im m(E+iη)` nondecreasing
(`stieltjesN_eta_mul_im_mono`, `InjSum.lean:203`); on the good event of `UNTrLocal` at `z₁ = E + i N^{-1+τ'}`:
`Im m(z₁) ≤ C + W^{τ'} Bctl n (1 - N^{-1+τ'}) ≤ C + 2 N^{τ'}` (`UNDens` upper bound `C`; `Bctl ≤ W^{-2𝔡} + N^{-τ'}`
by `(eq:WO)`), so `Im m(z₀) ≤ N^{τ'} (C + 2 N^{τ'})`; bad event `μ ≤ N^{-(p+1)}`, there `Im m(z₀) ≤ N`.
Section 1: merged names.  Section 2: the statements `def T2275_<name> : Prop` (the library states `<name>` in
namespace `RBM.Univ`, instances in `RBM.Univ.AprioriInst`, with exactly this statement; binder names may differ).
Section 3: downstream (information only).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2275-check.lean`.
-/
import RBM3D
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, f8ad4b4; namespace `RBM.Univ`; `UNInst` = `:1497-1898`)
#check @RBM.Univ.rhoSC                         -- :84
#check @RBM.Univ.stieltjesN                    -- :88
#check @RBM.Univ.UNModel                       -- :104
#check @RBM.Univ.UNModel.band                  -- :116
#check @RBM.Univ.ouP                           -- :145
#check @RBM.Univ.ouMat                         -- :150
#check @RBM.Univ.ouMat_zero                    -- :160 (`𝐇_0 = M.H n ω.1`)
#check @RBM.Univ.Nsz                           -- :372
#check @RBM.Univ.UNLocAvgBand                  -- :416 (premise of target 6)
#check @RBM.Univ.UNTrLocal                     -- :447 (premise; owed, Axioms.lean:203)
#check @RBM.Univ.UNDens                        -- :462 (premise; structural, Axioms.lean:328)
#check @RBM.Univ.UNApriori                     -- :522 (target pin; owed, Axioms.lean:205)
#check @RBM.Univ.UNGreenCorr                   -- :535 (consumer: hypothesis `UNApriori sz M E`, :537)
#check @RBM.Univ.UNUnivMainRow                 -- :745 (consumer row: has `UNDens`, `UNTrLocal`, admissible sizes)
#check @RBM.Univ.UNCore                        -- :760
#check @RBM.Univ.un_core_of_rows               -- :772
#check @RBM.Univ.UNDensBandRow                 -- :826 (premise of target 6)
#check @RBM.Univ.UNTrLocalBandRow              -- :842 (premise of target 6)
#check @RBM.Univ.un_dens_msc_zero              -- :1455 (instance 7a)
#check @RBM.Univ.UNInst.sz0_adm                -- :1518
-- UN-02a (`Universality/OU.lean`, T2177, a52eb85)
#check @RBM.Univ.isProbabilityMeasure_ouP      -- :44
#check @RBM.Univ.measurable_ouMat              -- :80
#check @RBM.Univ.ouMat_zero_map                -- :233 (alternative transfer, needs measurability)
-- UN-03a (`Universality/InjSum.lean`, T2178, 4c52041)
#check @RBM.Univ.stieltjesN_im_eq_normalized_specWeight  -- :196
#check @RBM.Univ.stieltjesN_eta_mul_im_mono    -- :203
-- UN-01b (`Universality/PinsK.lean`, T2187, fdbb6f0): second consumer
#check @RBM.Univ.UNGreenCorrC                  -- :187 (`UNApriori sz M.toUNModel E`, :190)
-- UN-01c (`Universality/PinsDens.lean`, T2201, 3fc9d03): consumers of `UNUnivMainRow`
#check @RBM.Univ.un_core_of_rows'              -- :220
#check @RBM.Univ.un_bUniv_of_rows'             -- :233
-- UN-05 (`Universality/GreenCorr.lean`, T2188, 0818c49): `UNApriori` as a hypothesis
#check @RBM.Univ.unGreenCorr                   -- :864
#check @RBM.Univ.GreenCorrCheck.instance_band  -- :892 (hypothesis `UNApriori sz0 (UNModel.band sz0) 0`, :897)
-- MD-1 (`Defs/Sizes.lean`, T2006, 0a873f1)
#check @RBM.Gauss.Idx                          -- :46
#check @RBM.Gauss.Sizes.size                   -- :157
#check @RBM.Gauss.Sizes.card_Idx               -- :160
#check @RBM.Gauss.Sizes.WO                     -- :164
#check @RBM.Gauss.Sizes.SizeTendsto            -- :173
#check @RBM.Gauss.Sizes.Admissible             -- :177
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge      -- :193
#check @RBM.Gauss.Sizes.Bctl                   -- :214
#check @RBM.Gauss.Sizes.W_rpow_le              -- :220
#check @RBM.Gauss.SizesInst.sz0                -- :260
#check @RBM.Gauss.SizesInst.sz0_values         -- :267
#check @RBM.Gauss.SizesInst.sz0_admissible     -- :331
-- `Defs/Params.lean` (c3f3d5d), `Defs/Semicircle.lean`
#check @RBM.Bparam                             -- Params.lean:36
#check @RBM.msc                                -- Semicircle.lean:116
-- Mathlib
#check @MeasureTheory.integral_fun_fst
#check @MeasureTheory.integral_mono_of_nonneg
#check @MeasureTheory.measure_toMeasurable
#check @Real.rpow_le_rpow_of_exponent_le
#check @Real.one_le_rpow
#check @Real.rpow_le_one_of_one_le_of_nonpos
#check @tendsto_rpow_atTop

/-! ## 2. Statements -/

noncomputable section

namespace RBM.Univ.T2275Check

open MeasureTheory Matrix Filter ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst
open scoped NNReal

/-! ### 2.1 Target 1: `apriori_im_bounds` (RBM2D `Apriori.lean:32`, private there): `0 ≤ Im m ≤ 1/η` -/

def T2275_apriori_im_bounds : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (H : Matrix ι ι ℂ), H.IsHermitian →
    ∀ E η : ℝ, 0 < η →
      0 ≤ (stieltjesN H ((E : ℂ) + (η : ℂ) * Complex.I)).im ∧
        (stieltjesN H ((E : ℂ) + (η : ℂ) * Complex.I)).im ≤ 1 / η

/-! ### 2.2 Target 2: `apriori_im_le_of_near` (the good-event step, RBM2D `apriori_good_bound` `:192` without
`Meta`): if `m(E + iη₁)` is `ζ`-close to `w`, then `Im m(E + iη₀) ≤ (η₁/η₀)(Im w + ζ)` for `0 < η₀ ≤ η₁`. -/

def T2275_apriori_im_le_of_near : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), H.IsHermitian →
    ∀ (E η₀ η₁ : ℝ) (w : ℂ) (ζ : ℝ), 0 < η₀ → η₀ ≤ η₁ →
      ‖stieltjesN H ((E : ℂ) + (η₁ : ℂ) * Complex.I) - w‖ ≤ ζ →
        (stieltjesN H ((E : ℂ) + (η₀ : ℂ) * Complex.I)).im ≤ η₁ / η₀ * (w.im + ζ)

/-! ### 2.3 Target 3: `apriori_ouMat_zero_integral` (law transfer at `t = 0`, RBM2D `apriori_transfer` `:153`,
model-generic, no measurability hypothesis: `ouMat_zero` + `integral_fun_fst` + `measure_univ`) -/

def T2275_apriori_ouMat_zero_integral : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ)
    (g : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ),
    ∫ ω, g (ouMat M n 0 ω) ∂(ouP M n) = ∫ ω, g (M.H n ω) ∂M.μ

/-! ### 2.4 Target 4: `apriori_bctl_le` (new; replaces RBM2D `apriori_ratio_le_one` `:51`, the `Meta` arithmetic):
under the lower half of `(eq:WO)` at `n`, `W^{-d}B_{η,0} = Bctl n (1 - η) ≤ W^{-2𝔡} + (N η)⁻¹` for `η > 0`
(`Bparam` at `K = 0`, `|1 - (1 - η)| = η`, `W^d L^d = N`, `lam_sq_mul_pow_ge`). -/

def T2275_apriori_bctl_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (𝔡 η : ℝ), 0 < η →
    ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n →
      sz.Bctl n (1 - η) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + (Nsz sz n * η)⁻¹

/-! ### 2.5 Target 5: `unApriori_of_trLocal` (RBM2D `aprioriRow` `:270`): the pin `UNApriori` for every model at
admissible sizes, from `UNDens` and `UNTrLocal` near `E` (binder order of `UNUnivMainRow`, `Pins.lean:745-748`;
only `0 < d` is used, through `W ≤ N`). -/

def T2275_unApriori_of_trLocal : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens m E ρ δ → UNTrLocal sz M m E δ → UNApriori sz M E

/-! ### 2.6 Target 6: `unApriori_band_of_rows` (the band row, RBM2D `AprioriRow` `Pins.lean:447` shape): bulk `E`,
from `UNTrLocalBandRow`, `UNDensBandRow`, `UNLocAvgBand` and target 5 (`δ` from `UNDensBandRow`, `0 < δ` from
`UNDens`). -/

def T2275_unApriori_band_of_rows : Prop :=
  UNTrLocalBandRow → UNDensBandRow → UNLocAvgBand →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, |E| ≤ 2 - κ → UNApriori sz (UNModel.band sz) E

/-! ### 2.7 Instances (namespace `RBM.Univ.AprioriInst`; `sz0`: `d = 3`, `L = 4`, `W = 32`, `N = 2^21` at `n = 0`) -/

/-- (a) Target 5 at `sz0` (`UNInst.sz0_adm`), the band model, `m = msc`, `E = 0`, `ρ = ρ_sc(0)`, `δ = 1/2`
(`un_dens_msc_zero` discharges `UNDens`); `UNTrLocal` is the owed pin and stays a hypothesis (RBM2D
`AprioriCheck`: `(h : locSC)`). -/
def T2275_inst_unApriori_band_zero : Prop :=
  UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) → UNApriori sz0 (UNModel.band sz0) 0

/-- (b) Target 6 at `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `sz0`, `κ = 1/2`, `E = 1` (`|1| ≤ 3/2`). -/
def T2275_inst_unApriori_band_one : Prop :=
  UNTrLocalBandRow → UNDensBandRow → UNLocAvgBand → UNApriori sz0 (UNModel.band sz0) 1

/-- (c) Target 2 at `H = 0 : Matrix (Fin 1) (Fin 1) ℂ`, `E = 0`, `η₀ = 1/2`, `η₁ = 1`, `w = m(i)`, `ζ = 0`
(hypothesis `‖w - w‖ ≤ 0` discharged; equality case: `Im m(i/2) = 2 = 2 · Im m(i)`). -/
def T2275_inst_im_le_of_near : Prop :=
  (stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ) (((0 : ℝ) : ℂ) + (((1 / 2 : ℝ)) : ℂ) * Complex.I)).im ≤
    1 / (1 / 2) * ((stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im + 0)

/-- (d) Target 4 at `sz0`, `n = 0`, `𝔡 = 1/10`, `η = 1/2` (`W^{-3/2+1/10} = 1/128 ≤ 1/64 = lam`, `sz0_values`). -/
def T2275_inst_bctl_le : Prop :=
  sz0.Bctl 0 (1 - 1 / 2) ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 10 : ℝ))) + (Nsz sz0 0 * (1 / 2))⁻¹

/-! ## 3. Downstream (information; not targets)

`UNApriori` is a hypothesis of `UNGreenCorr` (`Pins.lean:537`, proved generically by `unGreenCorr`,
`GreenCorr.lean:864`) and of `UNGreenCorrC` (`PinsK.lean:190`, read at `M.toUNModel`).  UN-24
(`Universality/UnivMain`, RBM2D `UnivMain.lean:453`: `have hap : AprioriImM d E := aprioriRow hloc …`) proves
`UNUnivMainRow` and calls target 5 at the row's own `hD : UNDens m E ρ δ`, `hT : UNTrLocal sz M m E δ`, `hA`;
`UNUnivMainRow` feeds `un_core_of_rows` (`Pins.lean:772`), `un_core_of_rows'`, `un_bUniv_of_rows'`
(`PinsDens.lean:220, 233`).  `EMCTE2.lean` (T2266, 061aa73) does not use `UNApriori` (0 hits). -/

example : Prop := ∀ d : ℕ, ∀ sz : Sizes d, ∀ M : UNModel sz, ∀ E : ℝ, UNApriori sz M E → UNGreenCorr sz M → True
example : Prop := UNUnivMainRow → UNCore

end RBM.Univ.T2275Check

end
