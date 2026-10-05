/-
Release check for T2213 (dispatcher V1, Mon Oct  5 20:37 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 (O2), §56, §57 (1), §65, §66, §69; supervisor `docs/supervisor/2026-10-05-1955.md` part B (B1, B2, B3, O3)).
UN-12b: the C″ re-pin of the C form (findings T2208a, T2208b), the conditional refutation of `UNStep1GoodC'` on a
diagonal model, the band instance of `UNTrLocalInit'` (scaling), the C-form Step 1 `UNStep1GoodC''` and the primed
band instances, in the new file `RBM3D/Universality/PinsC2.lean` (no merged signature changes, CLAUDE.md §5.3).
Primes are ASCII: `'` as on `main` (`UNStep1GoodC'`, T2201), `''` for the supervisor's `″`.
Section 1: the merged names the new file builds on (UN-01 = T2174, UN-01b = T2187, UN-01c = T2201, UN-12 = T2208,
UN-06 = T2176, UN-07 = T2190, UN-03a = T2178, the semicircle, the size sequences, the registry) and the Mathlib names
of the route (Weyl by positive semidefiniteness, the spectrum of a diagonal matrix by the characteristic polynomial,
the resolvent of a scalar multiple).
Section 2: the pins `UNTrLocalInit'`, `UNMeanBound`, `UNStep1GoodC''`, `UNCoreC''` in the temporary namespace
`RBM.Univ.T2213Check`; T2213 defines each in `RBM.Univ` with exactly this text.  Each is the merged text with only
the changes of supervisor 1955 B2 (script diff in the ticket): `UNTrLocalInit` (`PinsK.lean:259`) with the tolerance
`W^τ (Bctl + t*)`; `UNStep1GoodC'` (`PinsDens.lean:116`) and `UNCoreC'` (`PinsDens.lean:131`) with
`UNTrLocalInit ↦ UNTrLocalInit'` and `UNMeanBound sz M CV₀` beside `UNNormBound sz M.toUNModel CV₀`.
Section 3: the statements of the theorems of T2213 as `def T2213_<name> : Prop`; the library states the theorem
`<name>` (namespace in the docstring) with exactly this body (binder names may be added to the hypotheses; only
`Type` → `Type*` may differ in index binders).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2213-check.lean`.
-/
import RBM3D
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4): model, scales, Step 1 vocabulary, local law, rows, msc facts
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.Nsz
#check @RBM.Univ.ouTStar
#check @RBM.Univ.rhoSC
#check @RBM.Univ.stieltjesN
#check @RBM.Univ.mV
#check @RBM.Univ.IsRegular32
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.IsTestFun
#check @RBM.Univ.UNUnivDilAt
#check @RBM.Univ.UNL32
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNDens
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.UNNormBandRow
#check @RBM.Univ.UNTrLocalBandRow
#check @RBM.Univ.un_Bctl_le
#check @RBM.Univ.un_step1_floor
#check @RBM.Univ.un_msc_im_ge
#check @RBM.Univ.un_msc_lip
#check @RBM.Univ.un_msc_imag_axis
#check @RBM.Univ.un_dens_msc_zero
#check @RBM.Univ.UNInst.bump
#check @RBM.Univ.UNInst.bump_testFun
#check @RBM.Univ.UNInst.sz0_adm
-- UN-01b (`Universality/PinsK.lean`, T2187, merged fdbb6f0): the centred model, the initial matrix, the C form
#check @RBM.Univ.UNModelC
#check @RBM.Univ.UNModel.toC
#check @RBM.Univ.ouInit
#check @RBM.Univ.ouInit_isHermitian
#check @RBM.Univ.vOUC
#check @RBM.Univ.UNClaimAllC
#check @RBM.Univ.UNGreenCorrAllC
#check @RBM.Univ.UNTrLocalInit
#check @RBM.Univ.UNStep1GoodC
#check @RBM.Univ.UNCoreC
#check @RBM.Univ.UNKInst.inst_coreC_band
-- UN-01c (`Universality/PinsDens.lean`, T2201, merged 3fc9d03): the primed density hypothesis and C′ pins
#check @RBM.Univ.UNDens'
#check @RBM.Univ.UNDens'.toUNDens
#check @RBM.Univ.UNStep1GoodC'
#check @RBM.Univ.UNCoreC'
#check @RBM.Univ.not_UNStep1GoodC
#check @RBM.Univ.unTrLocalInit_shift
#check @RBM.Univ.un_msc_box_zero
#check @RBM.Univ.un_dens'_msc_zero
#check @RBM.Univ.UNDensInst.inst_coreC_band'
-- UN-12 (`Universality/Step1Good.lean`, T2208, merged a42cad0): the dictionary, the Admissible facts, the band Step 1
#check @RBM.Univ.stieltjesN_eq_mV
#check @RBM.Univ.mV_vOU
#check @RBM.Univ.mV_eta_mul_im_mono
#check @RBM.Univ.mV_im_le_inv
#check @RBM.Univ.un_admissible_c_mul_lt_one
#check @RBM.Univ.un_admissible_d_le_half
#check @RBM.Univ.un_admissible_cd_lt_half
#check @RBM.Univ.step1Good'_det
#check @RBM.Univ.step1Good'
#check @RBM.Univ.Step1GoodInst.inst_step1Good'_band
-- UN-06 (`Universality/FreeConv.lean`, T2176, merged 52c856e) and UN-07 (`Universality/FreeConvRegular.lean`, T2190,
-- merged d1a0316): the free convolution and target 4
#check @RBM.Univ.freeConvST
#check @RBM.Univ.isFreeConv51_freeConvST
#check @RBM.Univ.isFreeConv32_unique
#check @RBM.Univ.freeConv_stable_lip
#check @RBM.Univ.freeConvST_sub_le
#check @RBM.Univ.FreeConvRegularInst.freeConvST_zero_eq_msc
-- UN-03a (`Universality/InjSum.lean`, T2178, merged 4c52041)
#check @RBM.Univ.InjSum_stieltjesN_eq_stieltjes
-- the semicircle (`Defs/Semicircle.lean`, fbc9870) and the resolvent (`Loop/GLoopFlow.lean:74`)
#check @RBM.msc
#check @RBM.msc_im_pos
#check @RBM.norm_msc_lt_one
#check @RBM.Gauss.Gres
-- size sequences (`Defs/Sizes.lean`, 0a873f1; `Gauss/FineModel.lean`; `Induction/ScaleFacts.lean`, 5d1e6b1, source of
-- a private copy only, not imported)
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.card_Idx
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.scaleFacts3_W_tendsto
#check @RBM.Gauss.SizesInst.sz0
-- registry (`Test/Axioms.lean`, last changed 8a43715)
#check @RBM.Audit.owedProps
#check @RBM.Audit.structuralProps
#check @RBM.Audit.refutedProps
#check @RBM.Audit.scanPremises
-- Mathlib: eigenvalues, Weyl by positive semidefiniteness, the spectrum of a diagonal matrix, resolvent algebra,
-- two bad events, limits, `e^{-x}` facts
#check @Matrix.IsHermitian.eigenvalues
#check @Matrix.IsHermitian.eigenvalues_eq
#check @Matrix.IsHermitian.eigenvalues_eq_zero_iff
#check @Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues
#check @Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg
#check @Matrix.IsHermitian.charpoly_eq
#check @Matrix.charpoly_diagonal
#check @Matrix.PosSemidef.add
#check @Matrix.PosSemidef.smul
#check @spectrum.singleton_sub_eq
#check @Matrix.isHermitian_diagonal_of_self_adjoint
#check @Matrix.inv_diagonal
#check @Matrix.nonsing_inv_eq_ringInverse
#check @Ring.inverse_mul
#check @Polynomial.eval_prod
#check @Finset.prod_eq_zero_iff
#check @MeasureTheory.measure_union_le
#check @MeasureTheory.measure_mono
#check @ENNReal.ofReal_add
#check @tendsto_nhds_unique
#check @Filter.Eventually.exists
#check @Real.add_one_le_exp
#check @Real.rpow_le_rpow_of_exponent_le
#check @tendsto_rpow_neg_atTop

/-! ## 2. Pins (defined in `RBM.Univ` verbatim, file `RBM3D/Universality/PinsC2.lean`) -/

noncomputable section

namespace RBM.Univ.T2213Check

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

section Init

variable {d : ℕ}

/-- **Pin `UNTrLocalInit'` (owed; band: `unTrLocalInit'_band_zero`; BA: the BA row of BA-C1b)**: the merged
`UNTrLocalInit` (`PinsK.lean:259`, refuted for the band model, finding T2208b) with the tolerance
`W^τ (Bctl n (1 - Im z) + t*)`, `t* = ouTStar sz τs n` (supervisor 1955 B2): the spectrum of `ouInit` is shifted by
`O(t*)` against a `τ_s`-independent `m`. -/
def UNTrLocalInit' (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
  ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 ∧
        ((sz.W n : ℕ) : ℝ) ^ τ * (sz.Bctl n (1 - z.im) + ouTStar sz τs n) <
          ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNMeanBound` (structural)**: the deterministic mean of a centred model has all eigenvalues `≤ N^{CV₀}` in
modulus, eventually (supervisor 1955 B2; finding T2208a: `UNStep1GoodC'` never observes the mean).  Band: mean `0`
(`unMeanBound_toC`); BA: `‖λΨ‖ ≤ 2d 𝔡⁻¹ ≤ N^{CV₀}` eventually for `CV₀ > 0`. -/
def UNMeanBound (sz : Sizes d) (M : UNModelC sz) (CV₀ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ i, |(M.mean_herm n).eigenvalues i| ≤ Nsz sz n ^ CV₀

end Init

/-- **`UNStep1GoodC''`** (proved here by `step1GoodC''`; not registered): `UNStep1GoodC'` (`PinsDens.lean:116`,
refuted: `not_UNStep1GoodC'_of_diag`, supervisor 1955 B1) with `UNTrLocalInit ↦ UNTrLocalInit'` and
`UNMeanBound sz M CV₀` beside `UNNormBound sz M.toUNModel CV₀`. -/
def UNStep1GoodC'' : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → UNTrLocalInit' sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M.toUNModel CV₀ → UNMeanBound sz M CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNCoreC''` (owed, BA-C1b `baBUniv_of_rows`)**: `UNCoreC'` (`PinsDens.lean:131`, superseded: its hypothesis
`UNTrLocalInit` fails for the band model, supervisor 1955 B1) with `UNTrLocalInit ↦ UNTrLocalInit'` and
`UNMeanBound sz M CV₀` beside `UNNormBound sz M.toUNModel CV₀`. -/
def UNCoreC'' : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAllC →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNTrLocalInit' sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀ ∧ UNMeanBound sz M CV₀) → UNClaimAllC sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M.toUNModel ρ E E' k O

/-! ## 3. Statements of the theorems (`T2213_<name>` is the body of the theorem `<name>`) -/

/-! ### 3.1 Matrix facts and the C-form dictionary (namespace `RBM.Univ`) -/

/-- `un_eigenvalues_abs_le_convex` (Weyl for a convex combination; route: `|λ_i| ≤ R` for all `i` iff `R • 1 - A`
and `R • 1 + A` are positive semidefinite, by `spectrum_real_eq_range_eigenvalues`, `spectrum.singleton_sub_eq`,
`posSemidef_iff_eigenvalues_nonneg`; then `PosSemidef.add`, `PosSemidef.smul`).  Used for `ouInit = a H + (1-a) μ`. -/
def T2213_un_eigenvalues_abs_le_convex : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B C : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) {a R : ℝ}, 0 ≤ a → a ≤ 1 → C = a • A + (1 - a) • B →
      (∀ i, |hA.eigenvalues i| ≤ R) → (∀ i, |hB.eigenvalues i| ≤ R) → ∀ i, |hC.eigenvalues i| ≤ R

/-- `un_exists_eigenvalues_eq_diagonal`: every diagonal entry of a real diagonal matrix is one of its
`IsHermitian.eigenvalues` (route: `charpoly_eq`, `charpoly_diagonal`, `eval_prod`, `prod_eq_zero_iff`; the order of
`eigenvalues` is not needed). -/
def T2213_un_exists_eigenvalues_eq_diagonal : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    (hA : (Matrix.diagonal (fun i => (u i : ℂ))).IsHermitian) (j : ι), ∃ i, hA.eigenvalues i = u j

/-- `stieltjesN_diagonal`: `N⁻¹ tr (diag u - z)⁻¹ = mV u z` (`Gres`, `inv_diagonal`, `nonsing_inv_eq_ringInverse`). -/
def T2213_stieltjesN_diagonal : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) {z : ℂ}, 0 < z.im →
    stieltjesN (Matrix.diagonal (fun i => (u i : ℂ))) z = mV u z

/-- `stieltjesN_vert_le`: the `η`-Lipschitz bridge on a vertical line (`stieltjesN_eq_mV`, termwise
`|(λ - z)⁻¹ - (λ - z')⁻¹| ≤ |z - z'| / (Im z Im z')`). -/
def T2213_stieltjesN_vert_le : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ (x y y' : ℝ), 0 < y → 0 < y' →
    ‖stieltjesN H ⟨x, y⟩ - stieltjesN H ⟨x, y'⟩‖ ≤ |y - y'| / (y * y')

/-- `mV_vOUC`: the C-form dictionary `mV (vOUC) (w) = stieltjesN (ouInit) (w + E)` (supervisor 1955 B2; from
`stieltjesN_eq_mV`; no rescaling). -/
def T2213_mV_vOUC : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (n : ℕ) (τs E : ℝ) (ω : Sizes.SeqΩ sz) {w : ℂ}, 0 < w.im →
    mV (vOUC sz M n τs E ω) w = stieltjesN (ouInit M n (ouTStar sz τs n) ω) (w + E)

/-- `stieltjesN_ouInit_toC`: for a mean-`0` model `ouInit = a H`, `a = e^{-t/2}`, and
`stieltjesN (a H) z = a⁻¹ stieltjesN H (a⁻¹ z)` (`Gres`; `a • H - z • 1 = (a • 1) * (H - a⁻¹ z • 1)`,
`Ring.inverse_mul`). -/
def T2213_stieltjesN_ouInit_toC : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) {z : ℂ}, 0 < z.im →
    stieltjesN (ouInit M.toC n t ω) z =
      ((Real.exp (-t / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (M.H n ω) (((Real.exp (-t / 2) : ℝ) : ℂ)⁻¹ * z)

/-! ### 3.2 Monotonicity in the window, the mean bound of a mean-`0` model (namespace `RBM.Univ`) -/

/-- `UNDens'.mono`: `UNDens'` passes to a smaller window. -/
def T2213_UNDens'_mono : Prop :=
  ∀ {m : ℕ → ℂ → ℂ} {E : ℝ} {ρ : ℕ → ℝ} {δ δ' : ℝ}, 0 < δ → δ ≤ δ' → UNDens' m E ρ δ' → UNDens' m E ρ δ

/-- `UNTrLocal.mono`: `UNTrLocal` passes to a smaller window (the bad event shrinks). -/
def T2213_UNTrLocal_mono : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {M : UNModel sz} {m : ℕ → ℂ → ℂ} {E δ δ' : ℝ}, δ ≤ δ' →
    UNTrLocal sz M m E δ' → UNTrLocal sz M m E δ

/-- `unMeanBound_toC`: a mean-`0` model (in particular `(UNModel.band sz).toC`) has `UNMeanBound` for every `CV₀`
(`eigenvalues_eq_zero_iff`). -/
def T2213_unMeanBound_toC : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (CV₀ : ℝ), UNMeanBound sz M.toC CV₀

/-! ### 3.3 The band instance of `UNTrLocalInit'`: the scaling argument (namespace `RBM.Univ`) -/

/-- `unTrLocalInit'_of_unTrLocal` (supervisor 1955 B2, "Band"): for a mean-`0` model and an `n`-independent reference
`m` bounded by `K` and `Lp`-Lipschitz on `|Re z - E| ≤ δ'`, `0 < Im z ≤ 2`, the local law in the window `δ' > δ`
gives `UNTrLocalInit'` in the window `δ`.  Route: `stieltjesN_ouInit_toC`; the point `ζ = a⁻¹ z` lies in the window
`δ'` eventually (`(1 + t*) δ + t* |E| ≤ δ'`) with `Im ζ ≥ Im z`, so `Bctl (1 - Im ζ) ≤ Bctl (1 - Im z)`;
`‖a⁻¹ m (a⁻¹ z) - m z‖ ≤ t* (K + Lp (|E| + δ' + 2))`; for `Im ζ ∈ (1, a⁻¹]` the bridge `stieltjesN_vert_le` and the
Lipschitz bound to `Re ζ + i` (cost `≤ (1 + Lp) t*`); the local law at `(ε, τ/2, D)`, and `2 W^{τ/2} ≤ W^τ`,
`const ≤ W^τ` eventually (`W → ∞`). -/
def T2213_unTrLocalInit'_of_unTrLocal : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModel sz) (m : ℂ → ℂ) (E δ δ' K Lp : ℝ), 0 < δ → δ < δ' →
      (∀ z : ℂ, |z.re - E| ≤ δ' → 0 < z.im → z.im ≤ 2 → ‖m z‖ ≤ K) →
      (∀ z z' : ℂ, |z.re - E| ≤ δ' → 0 < z.im → z.im ≤ 2 →
        |z'.re - E| ≤ δ' → 0 < z'.im → z'.im ≤ 2 → ‖m z - m z'‖ ≤ Lp * ‖z - z'‖) →
      UNTrLocal sz M (fun _ => m) E δ' → UNTrLocalInit' sz M.toC (fun _ => m) E δ

/-- `unTrLocalInit'_band_zero`: the band model at `msc`, `E = 0`: `UNTrLocal` in the window `1/2` gives
`UNTrLocalInit'` in the window `1/4` (`K = 1` from `norm_msc_lt_one`, `Lp = 10000/81` from `un_msc_lip` with
`un_msc_im_ge` on `|Re z| ≤ 1/2`, `0 < Im z ≤ 2 ≤ 10`). -/
def T2213_unTrLocalInit'_band_zero : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 →
    UNTrLocal sz (UNModel.band sz) (fun _ => msc) 0 (1 / 2) →
      UNTrLocalInit' sz (UNModel.band sz).toC (fun _ => msc) 0 (1 / 4)

/-! ### 3.4 The conditional refutation (namespace `RBM.Univ`; supervisor 1955 B1, T2208a, "recommended compiled
target") -/

/-- `not_UNStep1GoodC'_of_diag`: if a deterministic diagonal model `H = mean = diag γ_n` meets the hypotheses of
`UNStep1GoodC'`, then `UNStep1GoodC'` gives `False`.  Route: `M'` = `M` with `mean' n = diag (γ_n + R_n e_{i₀})`,
`R_n = 8 N^{CV₀+2}`, `i₀ = fun _ => 0`; `ouInit M' = diag (γ_n + (1 - a) R_n e_{i₀})`; `UNTrLocalInit` transfers from
`M` at `τ/2` (`stieltjesN_diagonal`: the two transforms differ by `≤ 2/(Nη)`, and `(Nη)⁻¹ ≤ Bctl (1 - η)`;
`W^{τ/2}(W^{τ/2} - 1) ≥ 2` eventually); `M'.toUNModel = M.toUNModel`; `UNStep1GoodC'` at `M'`,
`τ_s = min (𝔠𝔡) (1/2)`, `D = 1`; the bad event is everything, because `un_exists_eigenvalues_eq_diagonal` gives an
eigenvalue `γ_{i₀} + (1 - a) R_n ≥ 2 N^{CV₀+1} - N^{CV₀}` of `ouInit M'` (`1 - a ≥ t*/4 ≥ N^{-1}/4`), so (2.3) fails;
`1 ≤ N^{-1}` is false for `N ≥ 2`. -/
def T2213_not_UNStep1GoodC'_of_diag : Prop :=
  UNStep1GoodC' →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (γ : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ),
        (∀ n ω, M.H n ω = Matrix.diagonal (fun i => (γ n i : ℂ))) →
        (∀ n, M.mean n = Matrix.diagonal (fun i => (γ n i : ℂ))) →
        ∀ (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
          UNDens' m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ →
            UNNormBound sz M.toUNModel CV₀ → False

/-! ### 3.5 The C-form Step 1 (namespace `RBM.Univ`; supervisor 1955 B2, "Proof route") -/

/-- `step1GoodC''_det`: eventually in `n`, every `ω` on which the `UNTrLocalInit'` local law holds at heights
`≥ N^{-1+τ_s/8}` (at `τ = τ_s/8`) and all eigenvalues of `H` are `≤ N^{CV₀}` has the good event of `UNStep1GoodC''`.
Target 4 at `mref = m n`, `E₀ = E`, `A = |E|`, `v = vOUC`, `s = e^{-t*}`, `t = 1 - e^{-t*}`; strip closeness through
`mV_vOUC` and the Lipschitz bridge `‖m ζ - a⁻¹ m (a⁻¹ ζ)‖ ≤ t* (K + Lp (|E| + 1))`;
`ε_n = 2 (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8}) + N^{-1+9τ_s/8} + (K + Lp (|E| + 1)) N^{-1+τ_s}`; (2.3) by
`un_eigenvalues_abs_le_convex` with `UNMeanBound`; `ρ₀ = ρ n` by uniqueness of limits.  Constants `c C` before
`∀ᶠ n` (`c = c_box/40`, `C = 2K + c_box + 2`). -/
def T2213_step1GoodC''_det : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNMeanBound sz M CV₀ →
      ∀ τs : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz,
          (∀ z : ℂ, |z.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ z.im → z.im ≤ 1 →
            ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖ ≤
              ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (sz.Bctl n (1 - z.im) + ouTStar sz τs n)) →
          (∀ i, |(M.herm n ω).eigenvalues i| ≤ Nsz sz n ^ CV₀) →
          (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
            ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
              ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))

/-- `step1GoodC''`: the pin `UNStep1GoodC''`, from `step1GoodC''_det`, `UNTrLocalInit'` at
`(τ_s, τ_s/8, τ_s/8, D + 1)` and `UNNormBound` at `D + 1` (two bad events, `2 N^{-D-1} ≤ N^{-D}` for `N ≥ 2`). -/
def T2213_step1GoodC'' : Prop := UNStep1GoodC''

/-! ### 3.6 Compiled nonempty instances (namespace `RBM.Univ.PinsC2Inst`; `sz0`, `𝔠 = 1/6`, `𝔡 = 1/10`, `E = 0`,
`δ = 1/4`) -/

section Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `inst_diag_model`: a deterministic diagonal centred model `H = mean = diag γ_n` exists for every `sz`, `γ`
(law `Sizes.seqP sz`): the structural hypotheses of `not_UNStep1GoodC'_of_diag` are satisfiable. -/
def T2213_inst_diag_model : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (γ : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ),
    ∃ M : UNModelC sz, (∀ n ω, M.H n ω = Matrix.diagonal (fun i => (γ n i : ℂ))) ∧
      ∀ n, M.mean n = Matrix.diagonal (fun i => (γ n i : ℂ))

/-- `inst_unTrLocalInit'_band`: `unTrLocalInit'_band_zero` at `sz0` with the band local law from the row
`UNTrLocalBandRow` at `κ = 1`, `E = 0`, `δ = 1/2`; `UNLocAvgBand` and the row stay hypotheses. -/
def T2213_inst_unTrLocalInit'_band : Prop :=
  UNLocAvgBand → UNTrLocalBandRow →
    UNTrLocalInit' sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 4)

/-- `inst_step1GoodC''_band`: `step1GoodC''` at `sz0`, `(UNModel.band sz0).toC`, `msc`, `E = 0`, `ρ = rhoSC 0`,
`δ = 1/4` (`UNDens'.mono` of `un_dens'_msc_zero`), `UNTrLocalInit'` from `inst_unTrLocalInit'_band`, the norm bound
from `UNNormBandRow`, `UNMeanBound` from `unMeanBound_toC`, `τ_s = 1/60`, `D = 1`. -/
def T2213_inst_step1GoodC''_band : Prop :=
  UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
    ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      (UNModel.band sz0).toC.μ {ω | ¬ (IsRegular32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω)
            (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4))
            (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (CV₀ + 1) ∧
          ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω)
              (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧
            ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
              |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ)))

/-- `inst_coreC_band''` (replaces the vacuous `UNKInst.inst_coreC_band`, `UNDensInst.inst_coreC_band'`):
`UNCoreC''` at `(UNModel.band sz0).toC`, `msc`, `E = 0`, `ρ = ρ_sc(0)`, `δ = 1/4`, `E' = 0`, `k = 1`, `𝒪 = bump`;
discharged: `UNDens'` (`UNDens'.mono`, `un_dens'_msc_zero`), `UNTrLocal` at `1/4` (`UNTrLocal.mono`),
`UNTrLocalInit'` (`unTrLocalInit'_band_zero`), `UNMeanBound` (`unMeanBound_toC`); kept: `UNL32`, `UNGUELocal`,
`UNGreenCorrAllC`, the band local law at `1/2`, the norm bound, `UNClaimAllC` (preflight (iii): numbers for each). -/
def T2213_inst_coreC_band'' : Prop :=
  UNCoreC'' → UNL32 → UNGUELocal → UNGreenCorrAllC →
    UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
    (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) →
    UNClaimAllC sz0 (UNModel.band sz0).toC 0 →
      UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)

end Inst

end RBM.Univ.T2213Check

end
