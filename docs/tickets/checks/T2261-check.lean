/-
Release check for T2261 (dispatcher V1, Tue Oct  6 05:16 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §50, §54, §56, §57 (1)-(2), §64 (4), §65, §66, §69 B).
UN-15: the OU generator identity `d/dt E Φ(𝐇_t) = -½ e^{-t} Σ_{ab} S°_{ab} E ∂_{ab}∂_{ba} Φ(𝐇_t)` (RBM2D paper
1-2:333-341, 364-369): port of RBM2D `Universality/OUGenerator.lean` (c9a24cf, 1223 lines) to `Idx d L W`,
`svarF d L W g`, `N = (W L)^d`, on the RBM3D carrier.
Carrier decision (T2261 design): the RBM2D proof (two independent Gaussian fields, Stein on each, Fubini) is ported
on the PAIR carrier `ouPairP d L W g = PF d L W g ⊗ gueP d L W` on `Ω d L W × Ω d L W` with
`ouPairMat d L W t ω = e^{-t/2} Xmat ω.1 + √(1-e^{-t}) Xmat ω.2` (section 2.1, verbatim vocabulary), and transferred
to the merged model-generic carrier `ouP (UNModel.band sz) n` on `SeqΩ sz × Ω d (L n) (W n)` (`Pins.lean:145-152`)
by the push-forward along `Prod.map (slice sz n) id` (section 2.3: `ouMat (band) = ouPairMat ∘ Prod.map …`,
`(ouP band n).map (Prod.map (slice sz n) id) = ouPairP … (sz.lam n)`, the second being the inner `this` of
`ouSample_law`, `OU.lean:215-220`).  The consumer form (section 2.4) is stated on `ouP (UNModel.band sz) n`,
`ouMat (UNModel.band sz) n`, `S° = centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n)`, the tokens of the owed
`UNEMCTE2` (`Pins.lean:669-689`) and of UN-17 target 5 at `lam = sz.lam n`.
Section 1: merged names.  Section 2: vocabulary (2.1) and the statements `def T2261_<name> : Prop` (2.2-2.6); the
library states `<name>` (namespace `RBM.Univ`; instances in `RBM.Univ.OUGeneratorInst`) with exactly this statement
(binder names may differ).  Section 3: downstream (information only).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2261-check.lean`.
-/
import RBM3D
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, f8ad4b4; namespace `RBM.Univ`)
#check @RBM.Univ.gueVar                        -- :61
#check @RBM.Univ.gueP                          -- :67
#check @RBM.Univ.stieltjesN                    -- :88
#check @RBM.Univ.UNModel.band                  -- :116
#check @RBM.Univ.ouTStar                       -- :142
#check @RBM.Univ.ouP                           -- :145
#check @RBM.Univ.ouMat                         -- :150
#check @RBM.Univ.ouMat_isHermitian             -- :154
#check @RBM.Univ.ouMat_zero                    -- :160
#check @RBM.Univ.InWindow                      -- :501
#check @RBM.Univ.L1t                           -- :617
#check @RBM.Univ.L2t                           -- :624
#check @RBM.Univ.UNEMCTE2                      -- :669 (consumer pin, owed; UN-18)
#check @RBM.Univ.UNEMCTE2Row                   -- :797
-- UN-01b (`Universality/PinsK.lean`, T2187, fdbb6f0)
#check @RBM.Univ.ouMatC                        -- :69
#check @RBM.Univ.ouMatC_toC                    -- :119
#check @RBM.Univ.UNEMCTE2k                     -- :345
-- UN-02a (`Universality/OU.lean`, T2177, a52eb85)
#check @RBM.Univ.isProbabilityMeasure_ouP      -- :44
#check @RBM.Univ.ouSample                      -- :50
#check @RBM.Univ.ouMat_eq_Xmat_ouSample        -- :61
#check @RBM.Univ.measurable_ouMat              -- :80
#check @RBM.Univ.ouSample_law                  -- :208 (proof :215-220 = template of target T2)
#check @RBM.Univ.ouMat_zero_map                -- :233
-- UN-16 (`Universality/OUHessian.lean`, T2247, 398ebe4)
#check @RBM.Univ.Bmat_swap_true                -- :134
#check @RBM.Univ.Bmat_swap_false               -- :149
#check @RBM.Univ.coordD1                       -- :202
#check @RBM.Univ.coordD2                       -- :208
#check @RBM.Univ.wirtSecond                    -- :216
#check @RBM.Univ.centeredVarianceEntry         -- :1115
-- UN-17 (`Universality/OUContraction.lean`, T2253, a18620d): the pointwise half UN-18 combines with UN-15
#check @RBM.Univ.centeredVariance_wirtProduct_kernel_bound_Lt  -- :1077
-- Green / Gauss (merged ST-1, MD files)
#check @RBM.Green.Bmat                         -- FlucVanish.lean:382 (40f70b9)
#check @RBM.Green.GreenDeriv_mem_usedCoords    -- FlucVanish.lean:396
#check @RBM.Green.GreenDeriv_Xmat_update       -- FlucVanish.lean:529 (RBM2D `:409` of OUGenerator)
#check @RBM.Gauss.usedCoords                   -- Hierarchy/ContractionBasic.lean:394 (e318c24)
#check @RBM.Gauss.GaussianProduct.law          -- Gauss/DominationAt.lean:500 (9e2b00f)
#check @RBM.Gauss.GaussianProduct.stein        -- Gauss/DominationAt.lean:559
#check @RBM.integrable_id_gaussianReal         -- Gauss/Stein.lean:182 (eb24464)
#check @RBM.Gauss.card_Idx                     -- Defs/Sizes.lean:107 (0a873f1)
#check @RBM.Gauss.CoordF                       -- Gauss/FineModel.lean:80 (0a873f1)
#check @RBM.Gauss.Ω                            -- :84
#check @RBM.Gauss.gvarF                        -- :89
#check @RBM.Gauss.PF                           -- :97
#check @RBM.Gauss.Xmat                         -- :113
#check @RBM.Gauss.Xmat_isHermitian             -- :142
#check @RBM.Gauss.Sizes.slice                  -- :176
#check @RBM.Gauss.Sizes.measurable_slice       -- :178
#check @RBM.Gauss.Sizes.seqP_map_slice         -- :184
#check @RBM.Gauss.Sizes.seqXmat                -- :218
#check @RBM.Gauss.continuous_Xmat              -- :427
#check @RBM.Gauss.SizesInst.sz0                -- Defs/Sizes.lean:260
-- Mathlib (route)
#check @MeasureTheory.integral_map
#check @MeasureTheory.Measure.map_prod_map
#check @MeasureTheory.integral_prod_symm
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le

/-! ## 2. Vocabulary and statements -/

noncomputable section

namespace RBM.Univ.T2261Check

open MeasureTheory Matrix ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst
open scoped NNReal
open scoped Matrix.Norms.L2Operator

/-! ### 2.1 Vocabulary (copied verbatim into namespace `RBM.Univ`) -/

section Defs

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- Test functions (RBM2D `TestFunH`, `OUGenerator.lean:57`, `Idx L W` ↦ `Idx d L W`). -/
def TestFunH (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) : Prop :=
  (∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ContDiffAt ℝ 2 Φ M) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖Φ M‖ ≤ C) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
    ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)

/-- The pair carrier (RBM2D `ouP L W = P ⊗ gueP`, `Universality/Pins.lean:53`), law `PF d L W g ⊗ gueP d L W`. -/
def ouPairP (g : ℝ) : Measure (Ω d L W × Ω d L W) :=
  (PF d L W g).prod (gueP d L W)

/-- The OU matrix on the pair carrier (RBM2D `ouMat L W`, `Universality/Pins.lean:59`). -/
def ouPairMat (t : ℝ) (ω : Ω d L W × Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Real.exp (-t / 2) • Xmat d L W ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω.2

/-- The instance test function `Φ(K) = Im m(K, I) · Im m(K, 2I)` (RBM2D `OUGeneratorCheck.Phi2`, `:1186`). -/
def Phi2 (K : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  ((∏ i : Fin 2, (stieltjesN K (![Complex.I, 2 * Complex.I] i)).im : ℝ) : ℂ)

end Defs

/-! ### 2.2 The generator identity on the pair carrier (targets P1, P2; RBM2D `:940`, `:951`) -/

/-- Target P1 `ouGeneratorPair_hasDerivAt_integral`. -/
def T2261_ouGeneratorPair_hasDerivAt_integral : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ),
    TestFunH d L W Φ → ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => ∫ ω, Φ (ouPairMat d L W s ω) ∂(ouPairP d L W g))
        ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
          (centeredVarianceEntry d L W g a b : ℂ) *
            ∫ ω, wirtSecond d L W Φ (ouPairMat d L W t ω) a b ∂(ouPairP d L W g)) t

/-- Target P2 `ouGeneratorPair_integral_sub_eq`. -/
def T2261_ouGeneratorPair_integral_sub_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ),
    TestFunH d L W Φ → ∀ T : ℝ, 0 ≤ T →
      (∫ ω, Φ (ouPairMat d L W T ω) ∂(ouPairP d L W g)) -
          ∫ ω, Φ (ouPairMat d L W 0 ω) ∂(ouPairP d L W g) =
        ∫ t in (0 : ℝ)..T, (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
          (centeredVarianceEntry d L W g a b : ℂ) *
            ∫ ω, wirtSecond d L W Φ (ouPairMat d L W t ω) a b ∂(ouPairP d L W g)

/-! ### 2.3 The carrier transfer (targets T1, T2; new) -/

/-- Target T1 `ouMat_band_eq_ouPairMat` (expected `rfl`: `UNModel.band sz` has `H = seqXmat sz`,
`seqXmat sz n ω = Xmat … (slice sz n ω)`). -/
def T2261_ouMat_band_eq_ouPairMat : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    ouMat (UNModel.band sz) n t ω =
      ouPairMat d (sz.L n) (sz.W n) t
        (Prod.map (Sizes.slice sz n) (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n)) ω)

/-- Target T2 `ouP_band_map_pair` (the inner `this` of `ouSample_law`, `OU.lean:215-220`, made public). -/
def T2261_ouP_band_map_pair : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ),
    (ouP (UNModel.band sz) n).map
        (Prod.map (Sizes.slice sz n) (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n))) =
      ouPairP d (sz.L n) (sz.W n) (sz.lam n)

/-! ### 2.4 The consumer form on the merged carrier (targets B1, B2; what UN-18 calls) -/

/-- Target B1 `ouGenerator_hasDerivAt_integral`. -/
def T2261_ouGenerator_hasDerivAt_integral : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ),
    TestFunH d (sz.L n) (sz.W n) Φ → ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => ∫ ω, Φ (ouMat (UNModel.band sz) n s ω) ∂(ouP (UNModel.band sz) n))
        ((-(1 / 2 : ℝ) * Real.exp (-t)) •
          ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
            (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
              ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n t ω) a b
                ∂(ouP (UNModel.band sz) n)) t

/-- Target B2 `ouGenerator_integral_sub_eq`. -/
def T2261_ouGenerator_integral_sub_eq : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ),
    TestFunH d (sz.L n) (sz.W n) Φ → ∀ T : ℝ, 0 ≤ T →
      (∫ ω, Φ (ouMat (UNModel.band sz) n T ω) ∂(ouP (UNModel.band sz) n)) -
          ∫ ω, Φ (ouMat (UNModel.band sz) n 0 ω) ∂(ouP (UNModel.band sz) n) =
        ∫ t in (0 : ℝ)..T, (-(1 / 2 : ℝ) * Real.exp (-t)) •
          ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
            (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
              ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n t ω) a b
                ∂(ouP (UNModel.band sz) n)

/-! ### 2.5 `∏ Im m(z_i)` is a test function (target S; RBM2D `:1157`) -/

/-- Target S `testFunH_stieltjesImProduct`. -/
def T2261_testFunH_stieltjesImProduct : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (nf : ℕ) (z : Fin nf → ℂ), (∀ i, 0 < (z i).im) →
    TestFunH d L W (fun K => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ))

/-! ### 2.6 Instances (namespace `RBM.Univ.OUGeneratorInst`; pair: `d = 3`, `L = 3`, `W = 2`, `g = 1/2`,
`N = 216`; band: `UNModel.band sz0`, `n = 0`, `T = ouTStar sz0 (1/2) 0`) -/

/-- `inst_testFunH`. -/
def T2261_inst_testFunH : Prop := TestFunH 3 3 2 (Phi2 3 3 2)

/-- `inst_pair_sub_eq` (target P2 at `T = 1`). -/
def T2261_inst_pair_sub_eq : Prop :=
  (∫ ω, Phi2 3 3 2 (ouPairMat 3 3 2 1 ω) ∂(ouPairP 3 3 2 (1 / 2))) -
      ∫ ω, Phi2 3 3 2 (ouPairMat 3 3 2 0 ω) ∂(ouPairP 3 3 2 (1 / 2)) =
    ∫ t in (0 : ℝ)..1, (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx 3 3 2, ∑ b : Idx 3 3 2,
      (centeredVarianceEntry 3 3 2 (1 / 2) a b : ℂ) *
        ∫ ω, wirtSecond 3 3 2 (Phi2 3 3 2) (ouPairMat 3 3 2 t ω) a b ∂(ouPairP 3 3 2 (1 / 2))

/-- `inst_band_hasDerivAt` (target B1 at `t = 1`). -/
def T2261_inst_band_hasDerivAt : Prop :=
  HasDerivAt (fun s : ℝ => ∫ ω, Phi2 3 (sz0.L 0) (sz0.W 0) (ouMat (UNModel.band sz0) 0 s ω)
      ∂(ouP (UNModel.band sz0) 0))
    ((-(1 / 2 : ℝ) * Real.exp (-1)) •
      ∑ a : Idx 3 (sz0.L 0) (sz0.W 0), ∑ b : Idx 3 (sz0.L 0) (sz0.W 0),
        (centeredVarianceEntry 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) a b : ℂ) *
          ∫ ω, wirtSecond 3 (sz0.L 0) (sz0.W 0) (Phi2 3 (sz0.L 0) (sz0.W 0))
            (ouMat (UNModel.band sz0) 0 1 ω) a b ∂(ouP (UNModel.band sz0) 0)) 1

/-- `inst_band_sub_eq` (target B2 at `T = ouTStar sz0 (1/2) 0`, the time `UNEMCTE2` reads). -/
def T2261_inst_band_sub_eq : Prop :=
  (∫ ω, Phi2 3 (sz0.L 0) (sz0.W 0) (ouMat (UNModel.band sz0) 0 (ouTStar sz0 (1 / 2) 0) ω)
      ∂(ouP (UNModel.band sz0) 0)) -
      ∫ ω, Phi2 3 (sz0.L 0) (sz0.W 0) (ouMat (UNModel.band sz0) 0 0 ω) ∂(ouP (UNModel.band sz0) 0) =
    ∫ t in (0 : ℝ)..(ouTStar sz0 (1 / 2) 0), (-(1 / 2 : ℝ) * Real.exp (-t)) •
      ∑ a : Idx 3 (sz0.L 0) (sz0.W 0), ∑ b : Idx 3 (sz0.L 0) (sz0.W 0),
        (centeredVarianceEntry 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) a b : ℂ) *
          ∫ ω, wirtSecond 3 (sz0.L 0) (sz0.W 0) (Phi2 3 (sz0.L 0) (sz0.W 0))
            (ouMat (UNModel.band sz0) 0 t ω) a b ∂(ouP (UNModel.band sz0) 0)

/-! ## 3. Downstream (information; not targets)

UN-18 (`EMCTE2`, RBM2D `EMCTE2.lean:440` `eq225_interval`) applies target B2 at `T` and at `t` with
`Φ = fun K => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ)` (target S, `0 < (z i).im` from `InWindow`), then bounds the
integrand pointwise by UN-17 `centeredVariance_wirtProduct_kernel_bound_Lt` at `H = ouMat (UNModel.band sz) n s ω`,
`lam = sz.lam n`, `hH = ouMat_isHermitian …`: the `L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω)
(z u)` and `L2t …` of `UNEMCTE2` (`Pins.lean:675-676, 680-681`) under `∂(ouP (UNModel.band sz) n)`. -/

end RBM.Univ.T2261Check

end
