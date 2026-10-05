/-
Release check for T2201 (dispatcher V1, Mon Oct  5 17:20 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §57 (1),
§65, §66; supervisor `docs/supervisor/2026-10-05-1651.md` answers 1-3 and table 3.1).
UN-01c: the primed successors of the UN pins made defective by finding T2190a, in the new file
`RBM3D/Universality/PinsDens.lean`, without changing any merged signature (CLAUDE.md §5.3).  The prime is the ASCII
`'` of `main` (`RBM.Gauss.Sizes.STNQConcl'`, `RBM3D/Induction/Step34PinsP.lean:53`, T2186).
Section 1: the merged names the new file builds on (UN-01 = T2174 `Universality/Pins.lean`, UN-01b = T2187
`Universality/PinsK.lean`, UN-06 = T2176 `Universality/FreeConv.lean`, UN-07 = T2190
`Universality/FreeConvRegular.lean`, the semicircle, the size sequences, the registry) and the Mathlib names of the
refutation route.
Section 2: the pinned vocabulary and pins (`UNDens'`, `unDensShift`, `UNStep1Good'`, `UNInfty1Row'`, `UNCore'`,
`UNDensBandRow'`, `UNStep1GoodC'`, `UNCoreC'`) in the temporary namespace `RBM.Univ.T2201Check`; T2201 defines each
in `RBM.Univ` with exactly this text.  Every primed pin is the merged text with `UNDens m E ρ δ` replaced by
`UNDens' m E ρ δ` and nothing else.
Section 3: the statements of the theorems of T2201 as `def T2201_<name> : Prop`; the library states the theorem
`<name>` (namespace in the docstring) with exactly this body (binder names may be added to the hypotheses; only
`Type` → `Type*` may differ in index binders).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2201-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4): model, scales, density, local law, Step 1, rows
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.Nsz
#check @RBM.Univ.ouTStar
#check @RBM.Univ.rhoSC
#check @RBM.Univ.rhoSC_pos
#check @RBM.Univ.kPoint
#check @RBM.Univ.IsTestFun
#check @RBM.Univ.isTestFun_comp_smul
#check @RBM.Univ.UNUnivDilAt
#check @RBM.Univ.unBUniv_diff_eq
#check @RBM.Univ.UNBUniv
#check @RBM.Univ.mV
#check @RBM.Univ.IsRegular32
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.UNL32
#check @RBM.Univ.UNQueBand
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.UNMLOut
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNDens
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.UNClaimAll
#check @RBM.Univ.UNGreenCorrAll
#check @RBM.Univ.UNInfty1
#check @RBM.Univ.vOU
#check @RBM.Univ.UNStep1Good
#check @RBM.Univ.UNInfty1Row
#check @RBM.Univ.UNUnivMainRow
#check @RBM.Univ.UNCore
#check @RBM.Univ.un_core_of_rows
#check @RBM.Univ.UNOURow
#check @RBM.Univ.UNEMCTE2Row
#check @RBM.Univ.UNJakUywRow
#check @RBM.Univ.UNClaimRow
#check @RBM.Univ.UNDensBandRow
#check @RBM.Univ.UNNormBandRow
#check @RBM.Univ.UNTrLocalBandRow
#check @RBM.Univ.un_claimAll_of_rows
#check @RBM.Univ.un_bUniv_of_rows
#check @RBM.Univ.un_Bctl_le
#check @RBM.Univ.un_msc_im_ge
#check @RBM.Univ.un_msc_lip
#check @RBM.Univ.un_dens_msc_zero
#check @RBM.Univ.UNInst.bump
#check @RBM.Univ.UNInst.bump_testFun
#check @RBM.Univ.UNInst.sz0_adm
#check @RBM.Univ.UNInst.inst_bUniv_band
#check @RBM.Univ.UNInst.inst_core_band
#check @RBM.Univ.UNInst.inst_core_of_rows
-- UN-01b (`Universality/PinsK.lean`, T2187, merged fdbb6f0): centred model, initial matrix, C-form pins, generic rows
#check @RBM.Univ.UNModelC
#check @RBM.Univ.UNModel.toC
#check @RBM.Univ.ouInit
#check @RBM.Univ.ouInit_isHermitian
#check @RBM.Univ.UNClaimAllC
#check @RBM.Univ.UNGreenCorrAllC
#check @RBM.Univ.UNTrLocalInit
#check @RBM.Univ.vOUC
#check @RBM.Univ.UNStep1GoodC
#check @RBM.Univ.UNCoreC
#check @RBM.Univ.UNKind.band
#check @RBM.Univ.UNOURowk
#check @RBM.Univ.UNEMCTE2Rowk
#check @RBM.Univ.UNJakUywRowk
#check @RBM.Univ.UNClaimRowk
#check @RBM.Univ.UNOURowk_band
#check @RBM.Univ.UNEMCTE2Rowk_band
#check @RBM.Univ.UNJakUywRowk_band
#check @RBM.Univ.UNClaimRowk_band
#check @RBM.Univ.UNKInst.inst_bUniv_band_k
#check @RBM.Univ.UNKInst.inst_coreC_band
-- UN-06 (`Universality/FreeConv.lean`, T2176, merged 52c856e): the free convolution and its uniqueness
#check @RBM.Univ.freeConvST
#check @RBM.Univ.freeConv_existsUnique
#check @RBM.Univ.isFreeConv51_freeConvST
#check @RBM.Univ.isFreeConv32_unique
-- UN-07 (`Universality/FreeConvRegular.lean`, T2190, merged d1a0316): targets 1-6, the bridge, the instances
#check @RBM.Univ.freeConvST_sub_le
#check @RBM.Univ.freeConvST_norm_sq_le
#check @RBM.Univ.unDens_freeConvST
#check @RBM.Univ.unDens_not_eta_determined
#check @RBM.Univ.freeConv_stable_lip
#check @RBM.Univ.freeConv_stable_freeConvST
#check @RBM.Univ.FreeConvRegularInst.freeConvST_zero_eq_msc
#check @RBM.Univ.FreeConvRegularInst.uI
#check @RBM.Univ.FreeConvRegularInst.uI_lower
#check @RBM.Univ.FreeConvRegularInst.stable_lip_msc
-- the semicircle (`Defs/Semicircle.lean`), the size sequences (`Defs/Sizes.lean`), the ASCII-prime precedent
#check @RBM.msc
#check @RBM.msc_im_pos
#check @RBM.norm_msc_lt_one
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
#check @RBM.Gauss.Sizes.STNQConcl'
-- the registry (`Test/Axioms.lean`, last changed d783ee3): the three lists and the scan
#check @RBM.Audit.borrowedProps
#check @RBM.Audit.owedProps
#check @RBM.Audit.structuralProps
#check @RBM.Audit.interfaceProps
#check @RBM.Audit.scanPremises
-- Mathlib (the refutation: two events of probability `≥ 1 - N^{-D}` meet; limits in `ℝ` are unique; `N^{-2} ≤ N^{-1+ε}`)
#check @MeasureTheory.measure_union_le
#check @tendsto_nhds_unique
#check @Filter.Eventually.exists
#check @Real.rpow_le_rpow_of_exponent_le

/-! ## 2. Pinned vocabulary and pins (defined in `RBM.Univ` verbatim, file `RBM3D/Universality/PinsDens.lean`) -/

noncomputable section

namespace RBM.Univ.T2201Check

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-- **`UNDens'` (structural)**: the merged `UNDens` (`Pins.lean:462`) and the box hypotheses `hbox`, `hlip` of
`freeConv_stable_lip` (`FreeConvRegular.lean:1238-1240`) at `mref = m n`, `E₀ = E`, on the box `|Re z - E| ≤ δ`,
`0 < Im z ≤ 1`: `Im` bounded below, bounded, Lipschitz as a complex function, the constants `c K Lp` fixed before
`∀ᶠ n` (uniform in `n`). -/
def UNDens' (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) : Prop :=
  UNDens m E ρ δ ∧ ∃ c K Lp : ℝ, 0 < c ∧ 0 < K ∧ 0 < Lp ∧ ∀ᶠ n in atTop,
    (∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (m n z).im ∧ ‖m n z‖ ≤ K) ∧
    (∀ z z' : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 →
      |z'.re - E| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖m n z - m n z'‖ ≤ Lp * ‖z - z'‖)

/-- **The shift of finding T2190a** (supervisor 1651, 1.1; target 6 of T2190 is the case `m = msc`, `E = 0`):
`m^h_n(z) = m_n(z) + (i/2) 1{Im z < h_n}`. -/
noncomputable def unDensShift (m : ℕ → ℂ → ℂ) (h : ℕ → ℝ) : ℕ → ℂ → ℂ :=
  fun n z => m n z + (if z.im < h n then Complex.I / 2 else 0)

/-- **`UNStep1Good'` (owed, UN-12)**: `UNStep1Good` (`Pins.lean:584`) with `UNDens ↦ UNDens'`. -/
def UNStep1Good' : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNInfty1Row'` (owed, UN-14)**: `UNInfty1Row` (`Pins.lean:733`) with `UNDens ↦ UNDens'`. -/
def UNInfty1Row' : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          ∀ E' : ℝ, |E'| < 2 →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1 sz M ρ E E' k O τU

/-- **`UNCore'`** (composed by `un_core_of_rows'`; not registered): `UNCore` (`Pins.lean:760`) with
`UNDens ↦ UNDens'`. -/
def UNCore' : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAll →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          UNClaimAll sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M ρ E E' k O

/-- **`UNDensBandRow'`** (proved from the merged owed row `UNDensBandRow` by `unDensBandRow'_of_row`; not
registered): `UNDensBandRow` (`Pins.lean:826`) with `UNDens ↦ UNDens'`. -/
def UNDensBandRow' : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∃ δ : ℝ, δ ≤ κ / 2 ∧ UNDens' (fun _ => msc) E (fun _ => rhoSC E) δ

/-- **`UNStep1GoodC'` (owed)**: `UNStep1GoodC` (`PinsK.lean:275`) with `UNDens ↦ UNDens'`. -/
def UNStep1GoodC' : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M.toUNModel CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNCoreC'` (owed)**: `UNCoreC` (`PinsK.lean:292`) with `UNDens ↦ UNDens'`. -/
def UNCoreC' : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAllC →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNTrLocalInit sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀) → UNClaimAllC sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M.toUNModel ρ E E' k O

/-! ## 3. Statements of the theorems (`T2201_<name>` is the body of the theorem `<name>`) -/

/-! ### 3.1 Projection, bridges, the generic BA lemma (namespace `RBM.Univ`) -/

/-- `UNDens'.toUNDens` (implicit data, so that `h.toUNDens` works). -/
def T2201_UNDens'_toUNDens : Prop :=
  ∀ {m : ℕ → ℂ → ℂ} {E : ℝ} {ρ : ℕ → ℝ} {δ : ℝ}, UNDens' m E ρ δ → UNDens m E ρ δ

/-- `unDens'_msc_of_unDens`: for `m = msc` the box hypotheses follow from `UNDens` (`c` from its first clause, the
window `η ≤ 10` contains the box; `K = 1`; `Lp = 1/(2c²)` from `freeConvST_sub_le` through `freeConvST_zero_eq_msc`). -/
def T2201_unDens'_msc_of_unDens : Prop :=
  ∀ (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens (fun _ => msc) E ρ δ → UNDens' (fun _ => msc) E ρ δ

/-- `unDensBandRow'_of_row`: the band row in primed form from the merged owed row (no new owed pin). -/
def T2201_unDensBandRow'_of_row : Prop := UNDensBandRow → UNDensBandRow'

/-- `unDens'_freeConvST`: `unDens_freeConvST` (`FreeConvRegular.lean:387`) with `UNDens ↦ UNDens'` (`K = 1` by
target 2, `Lp = 1/(2c²)` by target 1); BA-C1b/BA-C2 cite it for `UNDensBARow'`. -/
def T2201_unDens'_freeConvST : Prop :=
  ∀ {ι : ℕ → Type} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)] (u : ∀ n, ι n → ℝ) (E δ c : ℝ),
    0 < δ → 0 < c →
    (∀ᶠ n in atTop, ∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 → c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) →
    ∃ ρ : ℕ → ℝ, UNDens' (fun n => freeConvST (u n) 1) E ρ δ ∧
      ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 →
        |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - ρ n| ≤ η / c ^ 2

/-! ### 3.2 Composition (namespace `RBM.Univ`) -/

/-- `un_core_of_rows'` (`UNUnivMainRow` consumed through `UNDens'.toUNDens`). -/
def T2201_un_core_of_rows' : Prop := UNInfty1Row' → UNUnivMainRow → UNCore'

/-- `un_bUniv_of_rows'`: `un_bUniv_of_rows` (`Pins.lean:866`) with `UNInfty1Row ↦ UNInfty1Row'`; the band density
enters through `unDensBandRow'_of_row`. -/
def T2201_un_bUniv_of_rows' : Prop :=
  UNInfty1Row' → UNUnivMainRow → UNClaimRow → UNEMCTE2Row → UNJakUywRow → UNOURow → UNDensBandRow →
    UNTrLocalBandRow → UNNormBandRow →
    UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNGreenCorrAll → UNBUniv

/-! ### 3.3 The compiled refutation (namespace `RBM.Univ`) -/

/-- `unDensShift_of_le`: the shifted data agree with `m` on `Im z ≥ h n`. -/
def T2201_unDensShift_of_le : Prop :=
  ∀ (m : ℕ → ℂ → ℂ) (h : ℕ → ℝ) (n : ℕ) (z : ℂ), h n ≤ z.im → unDensShift m h n z = m n z

/-- `unDens_shift` (supervisor 1.1, generic `m`, `E`, `δ`): constants `(c, C + 1/2, Lp)`. -/
def T2201_unDens_shift : Prop :=
  ∀ (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (h : ℕ → ℝ), (∀ n, 0 < h n) → UNDens m E ρ δ →
    UNDens (unDensShift m h) E (fun n => ρ n + 1 / (2 * Real.pi)) δ

/-- `unTrLocal_shift`: at `h n = N^{-2} ≤ N^{-1+ε}` the event of `UNTrLocal` does not change. -/
def T2201_unTrLocal_shift : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ), UNTrLocal sz M m E δ →
    UNTrLocal sz M (unDensShift m (fun n => Nsz sz n ^ (-2 : ℝ))) E δ

/-- `unTrLocalInit_shift`: the same for `UNTrLocalInit`. -/
def T2201_unTrLocalInit_shift : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ), UNTrLocalInit sz M m E δ →
    UNTrLocalInit sz M (unDensShift m (fun n => Nsz sz n ^ (-2 : ℝ))) E δ

/-- `not_unDens'_unDensShift` (the "two data, one model" test, compiled half): the shift of a `UNDens'` datum is
never `UNDens'` once `h n ≤ 1` (a jump `1/2` across `Im z = h n` against a uniform `Lp`). -/
def T2201_not_unDens'_unDensShift : Prop :=
  ∀ (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ ρ' : ℕ → ℝ) (δ : ℝ) (h : ℕ → ℝ), (∀ n, 0 < h n) →
    (∀ᶠ n in atTop, h n ≤ 1) → UNDens' m E ρ δ → ¬ UNDens' (unDensShift m h) E ρ' δ

/-- `not_UNStep1Good` (supervisor 1.2): `UNStep1Good` refutes every datum that meets its hypotheses. -/
def T2201_not_UNStep1Good : Prop :=
  UNStep1Good → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M CV₀ → False

/-- `not_UNStep1GoodC` (supervisor 1.2, last line): the same for the C form. -/
def T2201_not_UNStep1GoodC : Prop :=
  UNStep1GoodC → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ →
        UNNormBound sz M.toUNModel CV₀ → False

/-! ### 3.4 The semicircle at `E = 0`, `δ = 1/2` (namespace `RBM.Univ`; constants of `stable_lip_msc`) -/

/-- `un_msc_box_zero`: `c = 9/100`, `K = 1`, `Lp = 62` on the box at `E = 0`, `δ = 1/2`. -/
def T2201_un_msc_box_zero : Prop :=
  ∀ z z' : ℂ, |z.re - 0| ≤ 1 / 2 → 0 < z.im → z.im ≤ 1 → |z'.re - 0| ≤ 1 / 2 → 0 < z'.im → z'.im ≤ 1 →
    9 / 100 ≤ (msc z).im ∧ ‖msc z‖ ≤ 1 ∧ ‖msc z - msc z'‖ ≤ 62 * ‖z - z'‖

/-- `un_dens'_msc_zero`: from `un_dens_msc_zero` and `un_msc_box_zero`. -/
def T2201_un_dens'_msc_zero : Prop := UNDens' (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2)

/-! ### 3.5 Instances (namespace `RBM.Univ.UNDensInst`; data of `UNInst`: `sz0`, `𝔠 = 1/6`, `𝔡 = 1/10`) -/

section Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `inst_core_band'`: `UNInst.inst_core_band` (`Pins.lean:1773`) with `UNCore ↦ UNCore'`. -/
def T2201_inst_core_band' : Prop :=
  UNCore' → UNL32 → UNGUELocal → UNGreenCorrAll →
    UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
    (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) →
    UNClaimAll sz0 (UNModel.band sz0) 0 →
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)

/-- `inst_core_of_rows'`: `UNInst.inst_core_of_rows` (`Pins.lean:1888`) with `UNInfty1Row ↦ UNInfty1Row'`. -/
def T2201_inst_core_of_rows' : Prop :=
  UNInfty1Row' → UNUnivMainRow → UNL32 → UNGUELocal → UNGreenCorrAll →
    UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
    (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) →
    UNClaimAll sz0 (UNModel.band sz0) 0 →
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)

/-- `inst_bUniv_band'`: `UNInst.inst_bUniv_band` (`Pins.lean:1757`) with `UNInfty1Row ↦ UNInfty1Row'`. -/
def T2201_inst_bUniv_band' : Prop :=
  UNInfty1Row' → UNUnivMainRow → UNClaimRow → UNEMCTE2Row → UNJakUywRow → UNOURow → UNDensBandRow →
    UNTrLocalBandRow → UNNormBandRow → UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand →
    UNGUELocal → UNGreenCorrAll →
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
      atTop (𝓝 0)

/-- `inst_bUniv_band_k'`: `UNKInst.inst_bUniv_band_k` (`PinsK.lean:653`) with `UNInfty1Row ↦ UNInfty1Row'`. -/
def T2201_inst_bUniv_band_k' : Prop :=
  UNInfty1Row' → UNUnivMainRow →
    UNClaimRowk (fun d => UNKind.band d) → UNEMCTE2Rowk (fun d => UNKind.band d) →
    UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand →
    UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand →
    UNDensBandRow → UNTrLocalBandRow → UNNormBandRow → UNL32 →
    (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNGreenCorrAll →
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
      atTop (𝓝 0)

/-- `inst_coreC_band'`: `UNKInst.inst_coreC_band` (`PinsK.lean:673`) with `UNCoreC ↦ UNCoreC'`. -/
def T2201_inst_coreC_band' : Prop :=
  UNCoreC' → UNL32 → UNGUELocal → UNGreenCorrAllC →
    UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
    UNTrLocalInit sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 2) →
    (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) →
    UNClaimAllC sz0 (UNModel.band sz0).toC 0 →
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)

/-- `inst_dens'_uI`: `unDens'_freeConvST` at the constant BA-class sequence `u n = uI`, `E = 0`, `δ = 1/2`,
`c = 1/20` (`uI_lower`). -/
def T2201_inst_dens'_uI : Prop :=
  ∃ ρ : ℕ → ℝ, UNDens' (fun _ : ℕ => freeConvST FreeConvRegularInst.uI 1) 0 ρ (1 / 2) ∧
    ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 →
      |(freeConvST FreeConvRegularInst.uI 1 ⟨0, η⟩).im / Real.pi - ρ n| ≤ η / (1 / 20 : ℝ) ^ 2

/-- `inst_T2190a_family`: the T2190a family at `sz0` (`h n = N_n^{-2}`) meets `UNDens` and the band local law
whenever `msc` does, and is not `UNDens'`. -/
def T2201_inst_T2190a_family : Prop :=
  UNDens (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0
      (fun _ => rhoSC 0 + 1 / (2 * Real.pi)) (1 / 2) ∧
    (UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
      UNTrLocal sz0 (UNModel.band sz0) (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0
        (1 / 2)) ∧
    ¬ UNDens' (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0
      (fun _ => rhoSC 0 + 1 / (2 * Real.pi)) (1 / 2)

/-- `not_UNStep1Good_band`: the band rows refute `UNStep1Good` (`sz0`, `E = 0`, `δ = 1/2`, `κ = 1`,
`un_dens_msc_zero`). -/
def T2201_not_UNStep1Good_band : Prop :=
  UNStep1Good → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow → False

end Inst

end RBM.Univ.T2201Check

end
