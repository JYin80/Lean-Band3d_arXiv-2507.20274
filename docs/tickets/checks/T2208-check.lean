/-
Release check for T2208 (dispatcher V1, Mon Oct  5 19:30 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §56, §57 (1), §65, §66 (3); supervisor `docs/supervisor/2026-10-05-1651.md` 2.2, 2.4, 3.1, 4, O1).
UN-12: the primed Step-1 pin `UNStep1Good'` (UN-01c = T2201, `RBM3D/Universality/PinsDens.lean:73`) proved in the new
file `RBM3D/Universality/Step1Good.lean` from the local law `UNTrLocal`, the norm bound `UNNormBound`, the density
hypothesis `UNDens'` and target 4 of T2190 (`freeConv_stable_lip`, `FreeConvRegular.lean:1234`), with the rescaling of
supervisor 2.2.  The C form `UNStep1GoodC'` is not a target (ticket, "Scope decision": findings T2208a, T2208b).
The prime is the ASCII `'` of `main`.
Section 1: the merged names the new file builds on (UN-01 = T2174, UN-01b = T2187, UN-01c = T2201, UN-06 = T2176,
UN-07 = T2190, UN-03a = T2178, the size sequences, the registry) and the Mathlib names of the route.
Section 2: the statements of the theorems of T2208 as `def T2208_<name> : Prop`; the library states the theorem
`<name>` (namespace in the docstring) with exactly this body (binder names may be added to the hypotheses; only
`Type` → `Type*` may differ in index binders).  No new vocabulary and no new `Prop`-valued definition.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2208-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4): model, scales, Step 1 vocabulary, local law, rows, arithmetic
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.Nsz
#check @RBM.Univ.ouTStar
#check @RBM.Univ.rhoSC
#check @RBM.Univ.stieltjesN
#check @RBM.Univ.mV
#check @RBM.Univ.IsRegular32
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNDens
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.vOU
#check @RBM.Univ.UNStep1Good
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.UNNormBandRow
#check @RBM.Univ.UNTrLocalBandRow
#check @RBM.Univ.un_W_neg_le
#check @RBM.Univ.un_Bctl_le
#check @RBM.Univ.un_step1_floor
#check @RBM.Univ.UNInst.sz0_adm
-- UN-01b (`Universality/PinsK.lean`, T2187, merged fdbb6f0): the C form (not a target; findings T2208a, T2208b)
#check @RBM.Univ.UNModelC
#check @RBM.Univ.UNModel.toC
#check @RBM.Univ.ouInit
#check @RBM.Univ.ouInit_isHermitian
#check @RBM.Univ.vOUC
#check @RBM.Univ.UNTrLocalInit
#check @RBM.Univ.UNStep1GoodC
-- UN-01c (`Universality/PinsDens.lean`, T2201, merged 3fc9d03): the primed density hypothesis and Step-1 pins
#check @RBM.Univ.UNDens'
#check @RBM.Univ.UNDens'.toUNDens
#check @RBM.Univ.UNStep1Good'
#check @RBM.Univ.UNStep1GoodC'
#check @RBM.Univ.un_msc_box_zero
#check @RBM.Univ.un_dens'_msc_zero
#check @RBM.Univ.unDens_shift
#check @RBM.Univ.not_UNStep1Good
#check @RBM.Univ.UNDensInst.not_UNStep1Good_band
-- UN-06 (`Universality/FreeConv.lean`, T2176, merged 52c856e): the free convolution
#check @RBM.Univ.freeConv_existsUnique
#check @RBM.Univ.freeConvST
#check @RBM.Univ.isFreeConv51_freeConvST
#check @RBM.Univ.isFreeConv32_unique
-- UN-07 (`Universality/FreeConvRegular.lean`, T2190, merged d1a0316): targets 4-5 (the abstract Step 1)
#check @RBM.Univ.freeConv_stable_lip
#check @RBM.Univ.freeConv_stable_freeConvST
#check @RBM.Univ.FreeConvRegularInst.freeConvST_zero_eq_msc
#check @RBM.Univ.FreeConvRegularInst.stable_lip_msc
-- UN-03a (`Universality/InjSum.lean`, T2178, merged 4c52041): Stieltjes transform of a Hermitian matrix
#check @RBM.Univ.InjSum_stieltjesN_eq_stieltjes
#check @RBM.Univ.stieltjesN_im_eq_normalized_specWeight
#check @RBM.Univ.stieltjesN_eta_mul_im_mono
-- size sequences (`Defs/Sizes.lean`, T2006, merged 0a873f1; `Induction/ScaleFacts3.lean`, T2058, merged 7c3072a)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.card_Idx
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.W_rpow_le
#check @RBM.Gauss.Sizes.scaleFacts3_W_tendsto
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
-- registry (`Test/Axioms.lean`, last changed 3fc9d03)
#check @RBM.Audit.owedProps
#check @RBM.Audit.refutedProps
#check @RBM.Audit.structuralProps
#check @RBM.Audit.scanPremises
-- Mathlib (two bad events; limits in `ℝ` are unique; eventual size conditions `N^{-e} ≤ c`; `e^{-t*}` facts)
#check @MeasureTheory.measure_union_le
#check @MeasureTheory.measure_mono
#check @ENNReal.ofReal_add
#check @tendsto_nhds_unique
#check @Filter.Eventually.exists
#check @Real.rpow_le_rpow_of_exponent_le
#check @tendsto_rpow_neg_atTop
#check @Real.add_one_le_exp
#check @Real.sqrt_sq

noncomputable section

namespace RBM.Univ.T2208Check

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-! ## 2. Statements of the theorems (`T2208_<name>` is the body of the theorem `<name>`, namespace `RBM.Univ`) -/

/-! ### 2.1 The eigenvalue dictionary and two elementary bounds on `mV` -/

/-- `stieltjesN_eq_mV`: the spectral formula `N⁻¹ tr (H - z)⁻¹ = mV λ(H) z` (copy the private
`InjSum_green_eq_spectral`, `InjSum.lean:43`, as a `private` helper; RBM2D `Step1RegularityB_stieltjesN_eq_mV`,
`Universality/Step1RegularityB.lean:129` at c9a24cf). -/
def T2208_stieltjesN_eq_mV : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ},
    0 < z.im → stieltjesN H z = mV hH.eigenvalues z

/-- `mV_vOU`: the affine dictionary of Step 1, `mV v (w) = a⁻¹ m_N(a⁻¹ (w + E))`, `a = e^{-t*/2}`, for
`v = vOU = a λ(H) - E` (RBM2D `Step1RegularityB_mV_vOU`, `:147`; supervisor 2.2 "band form"). -/
def T2208_mV_vOU : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τs E : ℝ) (ω : Sizes.SeqΩ sz) {w : ℂ}, 0 < w.im →
    mV (vOU sz M n τs E ω) w =
      ((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ *
        stieltjesN (M.H n ω) (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E))

/-- `mV_eta_mul_im_mono`: `η ↦ η Im mV v (x + iη)` is nondecreasing (the regime `1/2 < η ≤ 10` of `IsRegular32`
needs no reference value; supervisor 2.2; RBM2D uses `stieltjesN_eta_mul_im_mono` through the dictionary). -/
def T2208_mV_eta_mul_im_mono : Prop :=
  ∀ {ι : Type} [Fintype ι] (v : ι → ℝ) (x η η' : ℝ), 0 < η → η ≤ η' →
    η * (mV v ⟨x, η⟩).im ≤ η' * (mV v ⟨x, η'⟩).im

/-- `mV_im_le_inv`: `Im mV v (x + iη) ≤ 1/η`. -/
def T2208_mV_im_le_inv : Prop :=
  ∀ {ι : Type} [Fintype ι] (v : ι → ℝ) (x η : ℝ), 0 < η → (mV v ⟨x, η⟩).im ≤ 1 / η

/-! ### 2.2 What `Admissible` says about `𝔠`, `𝔡` (the `d ≥ 3` bookkeeping: `τ_s ≤ 𝔠𝔡 < 1/2 < 8/11`) -/

/-- `un_admissible_c_mul_lt_one`: `W ≥ N^𝔠` and `N = (W L)^d > W^d` (`L ≥ 3`) give `𝔠 d < 1` (at one `n`). -/
def T2208_un_admissible_c_mul_lt_one : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, 0 < d → sz.Admissible 𝔠 𝔡 → 𝔠 * (d : ℝ) < 1

/-- `un_admissible_d_le_half`: `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` eventually and `W → ∞` give `𝔡 ≤ d/2`. -/
def T2208_un_admissible_d_le_half : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → 𝔡 ≤ (d : ℝ) / 2

/-- `un_admissible_cd_lt_half`: hence `𝔠𝔡 < 1/2`; with `τ_s ≤ 𝔠𝔡` the term `C₀ t`, `t ≤ N^{-1+τ_s}`, of target 4 is
`≪ N^{-3τ_s/8}` (needs `τ_s < 8/11`; the pin's `τ_s < 1` alone does not give it). -/
def T2208_un_admissible_cd_lt_half : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, 0 < d → sz.Admissible 𝔠 𝔡 → 𝔠 * 𝔡 < 1 / 2

/-! ### 2.3 The deterministic half and the pin -/

/-- `step1Good'_det` (RBM2D `Step1RegularityB_det`, `:737`, with `msc ↦ m n` under `UNDens'`,
`freeConv_stable_local ↦ freeConv_stable_lip`, the band event `Step1LocalEvent` replaced by the complement of the bad
sets of `UNTrLocal` at `(ε, τ) = (τ_s/8, τ_s/8)` and of `UNNormBound`): eventually in `n`, every `ω` on which the local
law holds at heights `≥ N^{-1+τ_s/8}` and all eigenvalues are `≤ N^{CV₀}` has the good event of `UNStep1Good'`.  The
constants `c C` come before `∀ᶠ n`. -/
def T2208_step1Good'_det : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ →
      ∀ τs : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz,
          (∀ z : ℂ, |z.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ z.im → z.im ≤ 1 →
            ‖stieltjesN (M.H n ω) z - m n z‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - z.im)) →
          (∀ i, |(M.herm n ω).eigenvalues i| ≤ Nsz sz n ^ CV₀) →
          (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
            ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
              ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))

/-- `step1Good'`: **the owed pin `UNStep1Good'`** (`PinsDens.lean:73`, unchanged), from `step1Good'_det`, `UNTrLocal`
at `(τ_s/8, τ_s/8, D + 1)` and `UNNormBound` at `D + 1` (two bad events, `2 N^{-D-1} ≤ N^{-D}` for `N ≥ 2`; RBM2D
`step1Good_highProb`, `:817`). -/
def T2208_step1Good' : Prop := UNStep1Good'

/-! ### 2.4 Compiled nonempty instances (namespace `RBM.Univ.Step1GoodInst`) -/

section Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `inst_step1Good'_band`: `step1Good'` at `sz0` (`d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`), the band model, `msc`, `E = 0`,
`ρ = rhoSC 0`, `δ = 1/2` (`un_dens'_msc_zero`), the local law from the row `UNTrLocalBandRow` at `κ = 1`, the norm
bound from `UNNormBandRow`, `τ_s = 1/60 = 𝔠𝔡`, `D = 1` (the consumer's `D`, RBM2D `Step1Band.lean:1037`); the band
rows and `UNLocAvgBand` stay hypotheses (other gates' pins). -/
def T2208_inst_step1Good'_band : Prop :=
  UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
    ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      (UNModel.band sz0).μ {ω | ¬ (IsRegular32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω)
            (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4))
            (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (CV₀ + 1) ∧
          ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω)
              (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧
            ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
              |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ)))

/-- `inst_step1Good'_det_band`: `step1Good'_det` at the same data; the event hypotheses on `ω` stay hypotheses
(DECISIONS §56: they hold only for `N ≳ e^{2290}` at these constants, preflight (iv)). -/
def T2208_inst_step1Good'_det_band : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz0,
    (∀ z : ℂ, |z.re - 0| ≤ 1 / 2 → Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 8) ≤ z.im → z.im ≤ 1 →
      ‖stieltjesN ((UNModel.band sz0).H n ω) z - msc z‖ ≤
        ((sz0.W n : ℕ) : ℝ) ^ ((1 / 60 : ℝ) / 8) * sz0.Bctl n (1 - z.im)) →
    (∀ i, |((UNModel.band sz0).herm n ω).eigenvalues i| ≤ Nsz sz0 n ^ (1 : ℝ)) →
    (IsRegular32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω) (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4))
          (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (1 + 1) ∧
      ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω)
          (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧
        ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
          |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))

/-- `inst_admissible_sz0`: the three `Admissible` facts at `sz0` (`d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`). -/
def T2208_inst_admissible_sz0 : Prop :=
  (1 / 6 : ℝ) * ((3 : ℕ) : ℝ) < 1 ∧ (1 / 10 : ℝ) ≤ ((3 : ℕ) : ℝ) / 2 ∧ (1 / 6 : ℝ) * (1 / 10) < 1 / 2

end Inst

end RBM.Univ.T2208Check

end
