/-
Release check for T2214 (dispatcher V1, Mon Oct  5 20:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §54, §56, §57 (1), §66 (3), §69).
UN-13: Step 1 of `(1infyuniv)` against the GUE at energy `0`, model-generic: port of RBM2D
`Universality/Step1Band.lean` (c9a24cf, `step1Band` `:1072`) onto the abstract model `UNModel` with the primed
density hypothesis `UNDens'`, consuming `step1Good'` (UN-12 = T2208, `RBM3D/Universality/Step1Good.lean:757`), the
conditioning `integral_kPoint_ouMat_cond` (UN-02b = T2183, `Step1Cond.lean:368`) and the borrowed `UNL32`; new file
`RBM3D/Universality/Step1Band.lean`.  The conclusion is the merged `UNInfty1` (`Pins.lean:552`) at the GUE energy
`E' = 0`.  The C form (UN-12b) and the refuted pins are not used.  The prime is the ASCII `'` of `main`.
Section 1: the merged names the new file builds on and the Mathlib names of the route.
Section 2: the statements of the theorems of T2214 as `def T2214_<name> : Prop`; the library states the theorem
`<name>` (namespace in the docstring) with exactly this body (binder names may be added to hypotheses; only
`Type` → `Type*` may differ in index binders).  No new vocabulary and no new `Prop`-valued definition.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2214-check.lean`.
-/
import RBM3D
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4): vocabulary, the OU carrier, `L32`, the local laws, `UNInfty1`
#check @RBM.Univ.kPoint
#check @RBM.Univ.gueP
#check @RBM.Univ.rhoSC
#check @RBM.Univ.rhoSC_pos
#check @RBM.Univ.IsTestFun
#check @RBM.Univ.isTestFun_comp_smul
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.ouTStar
#check @RBM.Univ.ouP
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouMat_isHermitian
#check @RBM.Univ.IsRegular32
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.dbmMat
#check @RBM.Univ.dbmMat_isHermitian
#check @RBM.Univ.UNL32
#check @RBM.Univ.un_L32_arith
#check @RBM.Univ.Nsz
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNDens
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.UNInfty1
#check @RBM.Univ.vOU
#check @RBM.Univ.UNDensBandRow
#check @RBM.Univ.UNNormBandRow
#check @RBM.Univ.UNTrLocalBandRow
#check @RBM.Univ.UNInst.bump
#check @RBM.Univ.UNInst.bump_testFun
#check @RBM.Univ.UNInst.bump_nondegenerate
#check @RBM.Univ.UNInst.sz0_adm
#check @RBM.msc
-- UN-01c (`Universality/PinsDens.lean`, T2201, merged 3fc9d03): the primed density hypothesis and rows
#check @RBM.Univ.UNDens'
#check @RBM.Univ.UNDens'.toUNDens
#check @RBM.Univ.UNStep1Good'
#check @RBM.Univ.UNInfty1Row'
#check @RBM.Univ.UNCore'
#check @RBM.Univ.UNDensBandRow'
#check @RBM.Univ.unDensBandRow'_of_row
#check @RBM.Univ.un_core_of_rows'
#check @RBM.Univ.un_bUniv_of_rows'
#check @RBM.Univ.un_dens'_msc_zero
-- UN-12 (`Universality/Step1Good.lean`, T2208, merged a42cad0): the Step-1 regularity event
#check @RBM.Univ.stieltjesN_eq_mV
#check @RBM.Univ.un_admissible_cd_lt_half
#check @RBM.Univ.step1Good'_det
#check @RBM.Univ.step1Good'
#check @RBM.Univ.Step1GoodInst.inst_step1Good'_band
-- UN-02b (`Universality/Step1Cond.lean`, T2183, merged 7771372): conditioning, rescaling, counting
#check @RBM.Univ.integral_kPoint_ouMat_cond
#check @RBM.Univ.Step1Cond_gueMatPairing_eq_integral
#check @RBM.Univ.Step1Cond_scaledPairing_lipschitz
#check @RBM.Univ.Step1Cond_exists_dominating_testFun
#check @RBM.Univ.Step1Cond_corrPairing_le_count
#check @RBM.Univ.Step1Cond_exists_le_indicator
#check @RBM.Univ.Step1Cond_corrPairing_le_count_smul
-- UN-02a (`Universality/EigenMeasurable.lean`, `Universality/OU.lean`, T2177, merged a52eb85): measurability
#check @RBM.Univ.eigenvalues₀_abs_sub_le
#check @RBM.Univ.measurable_kPoint_eigenvalues
#check @RBM.Univ.integral_kPoint_eq_of_map_eq
#check @RBM.Univ.measurable_ouMat
-- size sequences and the fine-lattice model (`Defs/Sizes.lean`, `Gauss/FineModel.lean`, T2006, merged 0a873f1)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.card_Idx
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Xmat_isHermitian
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
-- registry (`Test/Axioms.lean`, last changed a42cad0)
#check @RBM.Audit.borrowedProps
#check @RBM.Audit.owedProps
#check @RBM.Audit.structuralProps
#check @RBM.Audit.refutedProps
-- Mathlib (`size → ∞` in `ℕ`; the diagonal argument; the bad event; `ε`-form of a limit)
#check @tendsto_natCast_atTop_iff
#check @Filter.Frequently.and_eventually
#check @MeasureTheory.abs_integral_le_integral_abs
#check @MeasureTheory.integral_indicator_const
#check @MeasureTheory.measure_union_le
#check @Metric.tendsto_nhds

noncomputable section

namespace RBM.Univ.T2214Check

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-! ## 2. Statements of the theorems (`T2214_<name>` is the body of the theorem `<name>`, namespace `RBM.Univ`) -/

/-! ### 2.1 Carrier-free helpers, public for UN-14 (RBM2D `GUETranslation.lean` copied them privately) -/

/-- `step1Band_abs_integral_kPoint_le`: `|∫ kPoint k P E λ| ≤ N^k sup|P|` (RBM2D `Step1Band_abs_integral_kPoint_le`,
`Universality/Step1Band.lean:170` at c9a24cf). -/
def T2214_step1Band_abs_integral_kPoint_le : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (Pm : Measure Ω') [IsProbabilityMeasure Pm] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Hm : Ω' → Matrix ι ι ℂ) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ} {B : ℝ},
    (∀ x, |P x| ≤ B) → ∀ E : ℝ,
      |∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm| ≤ (Fintype.card ι : ℝ) ^ k * B

/-- `step1Band_kPoint_shift`: the energy shift `kPoint k O 0 λ(A - c) = kPoint k O c λ(A)` (RBM2D
`Step1Band_kPoint_shift`, `:419`). -/
def T2214_step1Band_kPoint_shift : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (c : ℝ),
    B = A - (c : ℂ) • (1 : Matrix ι ι ℂ) → ∀ (k : ℕ) (O : (Fin k → ℝ) → ℝ),
      kPoint k O 0 hB.eigenvalues = kPoint k O c hA.eigenvalues

/-- `step1Band_eventually_forall`: the worst-sequence (diagonal) argument for a carrier that may depend on `n`
(RBM2D `Step1Band_eventually_forall`, `:999`, constant carrier; RBM2D `GUETranslation` needed the dependent form). -/
def T2214_step1Band_eventually_forall : Prop :=
  ∀ {α : ℕ → Type} (A P : ∀ n, α n → Prop) (b : ∀ n, α n),
    (∀ᶠ n in atTop, A n (b n)) →
    (∀ f : ∀ n, α n, (∀ᶠ n in atTop, A n (f n)) → ∀ᶠ n in atTop, P n (f n)) →
    ∀ᶠ n in atTop, ∀ z : α n, A n z → P n z

/-- `step1Band_gue_count`: the GUE count at scale `N^{-1+a}` from the weak GUE local law, against the rate
`N^{-3τ_s/8}` (RBM2D `Step1Band_gue_count`, `:466`; only `N` enters). -/
def T2214_step1Band_gue_count : Prop :=
  UNGUELocal → ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
    ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ), IsTestFun Q → 0 ≤ Q →
      Tendsto (fun n => Nsz sz n ^ (-(3 * τs / 8)) *
        ∫ ω, kPoint k Q 0 (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
        atTop (𝓝 0)

/-! ### 2.2 The model carrier: conditioning on `H` and the energy shift into the diagonal -/

/-- `step1Band_integral_ouP`: the `ouP` functional of `𝐇_{t*}` at `E` is the `M.μ`-average of the DBM functional of
`vOU = e^{-t*/2} λ(H) - E` at energy `0`, time `1 - e^{-t*}` (`integral_kPoint_ouMat_cond` at `t = t*`, then the shift;
RBM2D `Step1Band_integral_ouP`, `:711`, without its slice transfer: the merged conditioning is model-indexed). -/
def T2214_step1Band_integral_ouP : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τU E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ), IsTestFun O →
    ∫ ω, kPoint k O E (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n) =
      ∫ ω, (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vOU sz M n τU E ω)
          (1 - Real.exp (-(ouTStar sz τU n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) ∂M.μ

/-! ### 2.3 Step 1 against the GUE at energy `0` (the target of UN-13) -/

/-- `step1Band`: **Step 1 of `(1infyuniv)`, model-generic** (RBM2D `step1Band`, `:1072`): for an abstract model with
the primed density hypothesis `UNDens'`, the tracial local law `UNTrLocal` and the norm bound `UNNormBound`, every
`0 < τ_U ≤ 𝔠𝔡`, every `k` and every test function, the `𝐇_{t*}` functional at `E` dilated by `ρ_n` is asymptotically
the GUE functional at energy `0` dilated by `ρ_sc(0)`: `UNInfty1 sz M ρ E 0 k O τU` (`Pins.lean:552`).  RBM2D's
`|E| ≤ 2 - κ` is not needed (`UNDens` gives `ρ_n ∈ [c/π, C/π]`); `τ_U < 1` follows from `un_admissible_cd_lt_half`. -/
def T2214_step1Band : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            ∀ τU : ℝ, 0 < τU → τU ≤ 𝔠 * 𝔡 → UNInfty1 sz M ρ E 0 k O τU

/-- `step1Band_row`: the consumer shape for UN-14: `UNInfty1Row'` (`PinsDens.lean:88`) at the GUE energy `E' = 0`,
with `τ₁ = 𝔠𝔡`. -/
def T2214_step1Band_row : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1 sz M ρ E 0 k O τU

/-! ### 2.4 Compiled nonempty instances (namespace `RBM.Univ.Step1BandInst`) -/

section Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `inst_step1Band_band`: `step1Band` at `sz0` (`d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`), the band model, `msc`, `E = 0`,
`ρ = rhoSC 0`, `δ = 1/2` (`un_dens'_msc_zero`), the local law from `UNTrLocalBandRow` at `κ = 1`, the norm bound from
`UNNormBandRow`, `k = 1`, `O = bump`, `τ_U = 1/60 = 𝔠𝔡`; the external input, the GUE local law and the band rows stay
hypotheses. -/
def T2214_inst_step1Band_band : Prop :=
  UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
    UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) (1 / 60)

/-- `inst_step1Band_band_one`: the same at `E = 1` (`κ = 1/2`), `ρ = rhoSC 1`; the density from the row
`UNDensBandRow` through `unDensBandRow'_of_row` (`δ ≤ 1/4`, `0 < δ` from `UNDens`), so the energy shift `E ↦ 0`
and the dilation `ρ_sc(1) ≠ ρ_sc(0)` are both nontrivial. -/
def T2214_inst_step1Band_band_one : Prop :=
  UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow → UNDensBandRow →
    UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 1) 1 0 1 (bump : (Fin 1 → ℝ) → ℝ) (1 / 60)

/-- `inst_rhoSC_one_lt_zero`: the two dilations of `inst_step1Band_band_one` differ (`√3/(2π) < 1/π`). -/
def T2214_inst_rhoSC_one_lt_zero : Prop := rhoSC 1 < rhoSC 0

end Inst

end RBM.Univ.T2214Check

end
