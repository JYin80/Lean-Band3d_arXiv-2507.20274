/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Pins

/-!
# `RBM3D.Universality.PinsK` (UN-01b): the model-generic pins of bulk universality

Promotion of the model-generic part of the BA-DS design probe of ticket T2173
(`RBM3D/Probe/T2173Pins.lean` on branch `t/T2173` at `a543154`; ticket T2187) to the library,
**without changing any merged signature** (CLAUDE.md §5.3, DECISIONS §57 (1)).  The probe amends
`UNModel` (a field `mean`) and `ouMat` (centred) in place; here the amended structure is the
primed successor `UNModelC sz extends UNModel sz`, and the centred flow is `ouMatC`.  The class
`UNKind` carries the model with its mean (`UNKind.M : ∀ sz, UNModelC sz`), the mean determines the
flow and the initial matrix `ouInit`; the flow is deliberately not a free field (`UNCoreC`
quantifies over all models).

Substitutions from the probe (ticket T2187, design): S1 amended `UNModel sz` becomes `UNModelC sz`;
S2 `ouMat`, `ouMat_isHermitian`, `ouMat_zero` become `ouMatC`, `ouMatC_isHermitian`, `ouMatC_zero`;
S3 `ouP M n` becomes `ouP M.toUNModel n`; S4 model-level merged pins (`UNTrLocal`, `UNNormBound`,
`UNUnivDilAt`, `UNApriori`) take `M.toUNModel`; S5 claim-level pins over the amended model become
the copies `UNClaim417C`, `UNClaimAllC`, `UNGreenCorrC`, `UNGreenCorrAllC`, `UNInfty1C`,
`UNUnivMainC`; S6 `UNModel.band sz` (mean `0`) becomes `(UNModel.band sz).toC`.

Sections: 1 the centred model, flow and initial matrix; 2 claim-level copies and their mean-`0`
bridges; 3 the model class and the generic Claim `(417)` pins; 4 the consumed shapes, the generic
rows and `un_claimAll_of_rowsk`; 5 band bridges (the band chain closes on the generic forms);
6 compiled nonempty instances (`UNKInst`).

Not here (ticket T2187): band bridges for `vOUC`/`UNStep1GoodC`/`UNCoreC` (they need
`λ(e^{-t/2}H) = e^{-t/2}λ(H)` for `IsHermitian.eigenvalues` and the owed rescaling
`UNTrLocal → UNTrLocalInit`); the generator identity and the drift (UN-15, BA-C1); every
BA-specific item (BA-C1).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

/-! ## 1. The centred model, the centred flow and the initial matrix -/

/-- **The centred model (primed successor of the merged `UNModel`, CLAUDE.md §5.3)**: a model and the deterministic
mean `E H` that the centred OU flow holds fixed (`0` for the band model, `ilambda Ψ` for block Anderson).  This is the
probe's amended `UNModel` (A1, probe `:119-130`) under a new name. -/
structure UNModelC {d : ℕ} (sz : Sizes d) extends UNModel sz where
  /-- the deterministic mean `E H` -/
  mean : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
  mean_herm : ∀ n, (mean n).IsHermitian

/-- A model with mean `0` as a centred model (`mean := 0`); the band model is `(UNModel.band sz).toC`. -/
def UNModel.toC {d : ℕ} {sz : Sizes d} (M : UNModel sz) : UNModelC sz :=
  { M with mean := fun _ => 0, mean_herm := fun _ => Matrix.isHermitian_zero }

section Flow

variable {d : ℕ} {sz : Sizes d}

/-- **The centred OU matrix** `μ + e^{-t/2}(H - μ) + √(1 - e^{-t}) H'` (probe `ouMat`, `:179-182`, renamed). -/
def ouMatC (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  M.mean n + Real.exp (-t / 2) • (M.H n ω.1 - M.mean n) +
    Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2

/-- The DBM initial matrix `μ + e^{-t/2}(H - μ)` (probe `ouInit`, `:2523-2525`, over `UNModelC`). -/
def ouInit (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  M.mean n + Real.exp (-t / 2) • (M.H n ω - M.mean n)

theorem ouMatC_isHermitian (M : UNModelC sz) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : (ouMatC M n t ω).IsHermitian :=
  ((M.mean_herm n).add (((M.herm n ω.1).sub (M.mean_herm n)).smul (IsSelfAdjoint.all _))).add
    ((Xmat_isHermitian d _ _ ω.2).smul (IsSelfAdjoint.all _))

/-- `𝐇_0 = H` for the centred flow (probe `ouMat_zero`, `:197`, under S1, S2). -/
theorem ouMatC_zero (M : UNModelC sz) (n : ℕ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMatC M n 0 ω = M.H n ω.1 := by
  simp [ouMatC]

theorem ouInit_isHermitian (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) :
    (ouInit M n t ω).IsHermitian :=
  (M.mean_herm n).add (((M.herm n ω).sub (M.mean_herm n)).smul (IsSelfAdjoint.all _))

theorem ouMatC_eq_ouInit_add (M : UNModelC sz) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMatC M n t ω = ouInit M n t ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2 :=
  rfl

/-- The centred flow is the merged (non-centred) flow `ouMat` plus `(1 - e^{-t/2}) μ`
(statement `T2187_ouMatC_eq_ouMat_add` of the check file; probe `ouMat_eq_ouMatNC_add`, `:2642`). -/
theorem ouMatC_eq_ouMat_add (M : UNModelC sz) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMatC M n t ω = ouMat M.toUNModel n t ω + (1 - Real.exp (-t / 2)) • M.mean n := by
  unfold ouMatC ouMat
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
  push_cast
  ring

/-- `(UNModel.toC M).toUNModel = M`. -/
theorem unPinsK_toC_toUNModel (M : UNModel sz) : M.toC.toUNModel = M := rfl

/-- At mean `0` the centred flow is the merged one, pointwise form. -/
theorem ouMatC_toC_apply (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMatC M.toC n t ω = ouMat M n t ω := by
  rw [ouMatC_eq_ouMat_add]
  simp [UNModel.toC]

/-- `ouMatC M.toC = ouMat M` (function equality). -/
theorem ouMatC_toC (M : UNModel sz) : ouMatC M.toC = ouMat M := by
  funext n t ω
  exact ouMatC_toC_apply M n t ω

/-- The initial matrix at mean `0` is `e^{-t/2} H` (probe `ouInit_band`, `:2772`, for any model). -/
theorem ouInit_toC (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) :
    ouInit M.toC n t ω = Real.exp (-t / 2) • M.H n ω := by
  simp [ouInit, UNModel.toC]

end Flow

/-! The pinned statements `T2187_ouMatC_eq_ouMat_add`, `T2187_ouMatC_mean_zero` of the check file, as compiled
`example`s (the bodies are copied from the check file by script). -/

example :
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    ouMatC M n t ω = ouMat M.toUNModel n t ω + (1 - Real.exp (-t / 2)) • M.mean n :=
  fun _ M n t ω => ouMatC_eq_ouMat_add M n t ω

example :
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz), (∀ n, M.mean n = 0) →
    ∀ (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)), ouMatC M n t ω = ouMat M.toUNModel n t ω :=
  fun _ M h n t ω => by rw [ouMatC_eq_ouMat_add, h n, smul_zero, add_zero]

/-! ## 2. Claim-level copies over `UNModelC` and their mean-`0` bridges -/

section ClaimC

variable {d : ℕ} {sz : Sizes d}

/-- **Pin `UNClaim417C`** (merged `UNClaim417`, `Pins.lean:508-513`, under S1-S3). -/
def UNClaim417C (sz : Sizes d) (M : UNModelC sz) (E : ℝ) (nf : ℕ) (τU c' Cn : ℝ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ, (∀ i, InWindow sz E C₀ τU n (z i)) →
    ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
      |(∫ ω, ∏ i, (stieltjesN (ouMatC M n t ω) (z i)).im ∂(ouP M.toUNModel n)) -
        ∫ ω, ∏ i, (stieltjesN (ouMatC M n (ouTStar sz τU n) ω) (z i)).im ∂(ouP M.toUNModel n)| ≤
        Nsz sz n ^ (-c' + Cn * τU)

/-- `UNClaim417C` for all `n_f`, all small `τ_U` (merged `UNClaimAll`, `Pins.lean:516-518`, under S1, S5). -/
def UNClaimAllC (sz : Sizes d) (M : UNModelC sz) (E : ℝ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
    ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNClaim417C sz M E nf τU c' Cn

/-- The eigenvalues of Hermitian matrices that are equal are equal (the Hermitian proofs differ). -/
private theorem unPinsK_eigenvalues_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hA.eigenvalues = hB.eigenvalues := by
  subst h; rfl

private theorem unPinsK_eig_toC (M : UNModel sz) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    (ouMatC_isHermitian M.toC n t ω).eigenvalues = (ouMat_isHermitian M n t ω).eigenvalues :=
  unPinsK_eigenvalues_congr (ouMatC_toC_apply M n t ω) _ _

/-- `UNClaim417C` at mean `0` is the merged `UNClaim417`. -/
theorem UNClaim417C_toC (M : UNModel sz) (E : ℝ) (nf : ℕ) (τU c' Cn : ℝ) :
    UNClaim417C sz M.toC E nf τU c' Cn ↔ UNClaim417 sz M E nf τU c' Cn := by
  unfold UNClaim417C UNClaim417
  simp only [unPinsK_toC_toUNModel, ouMatC_toC_apply]

/-- `UNClaimAllC` at mean `0` is the merged `UNClaimAll`. -/
theorem UNClaimAllC_toC (M : UNModel sz) (E : ℝ) :
    UNClaimAllC sz M.toC E ↔ UNClaimAll sz M E := by
  unfold UNClaimAllC UNClaimAll
  simp only [UNClaim417C_toC]

/-- **Pin `UNGreenCorrC`** (merged `UNGreenCorr`, `Pins.lean:535-544`, under S1-S5: the model is a `UNModelC`, the flow
is `ouMatC`, the model-level pin `UNApriori` and the carrier `ouP` read `M.toUNModel`). -/
def UNGreenCorrC (sz : Sizes d) (M : UNModelC sz) : Prop :=
  ∀ (E : ℝ) (k : ℕ) (c' : ℝ), 0 < c' → ∀ Cn : ℕ → ℝ, ∃ τ₀ : ℝ, 0 < τ₀ ∧
    ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      (∀ nf ≤ k, UNClaim417C sz M E nf τU c' (Cn nf)) → UNApriori sz M.toUNModel E →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → ∀ (r : ℕ → ℝ) (a b : ℝ), 0 < a →
        (∀ᶠ n in atTop, a ≤ r n ∧ r n ≤ b) →
        Tendsto (fun n =>
          (∫ ω, kPoint k (fun α => O (r n • α)) E (ouMatC_isHermitian M n 0 ω).eigenvalues
              ∂(ouP M.toUNModel n)) -
          (∫ ω, kPoint k (fun α => O (r n • α)) E
              (ouMatC_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M.toUNModel n)))
          atTop (𝓝 0)

end ClaimC

/-- `UNGreenCorrC` for every model along every size sequence with `size n → ∞` (merged `UNGreenCorrAll`,
`Pins.lean:546-549`, under S1, S5). -/
def UNGreenCorrAllC : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
    ∀ M : UNModelC sz, UNGreenCorrC sz M

section ClaimC2

variable {d : ℕ} {sz : Sizes d}

/-- **`(1infyuniv)`** over `UNModelC` (merged `UNInfty1`, `Pins.lean:552-560`, under S1-S4). -/
def UNInfty1C (sz : Sizes d) (M : UNModelC sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E
        (ouMatC_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M.toUNModel n)) -
    (∫ ω, kPoint k (fun α => O (rhoSC E' • α)) E'
        (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))))
    atTop (𝓝 0)

/-- **`(univ-main)`** over `UNModelC` (merged `UNUnivMain`, `Pins.lean:563-571`, under S1-S4). -/
def UNUnivMainC (sz : Sizes d) (M : UNModelC sz) (ρ : ℕ → ℝ) (E : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E (M.herm n ω).eigenvalues ∂M.μ) -
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E
        (ouMatC_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M.toUNModel n)))
    atTop (𝓝 0)

/-- `UNGreenCorrC` at mean `0` is the merged `UNGreenCorr`. -/
theorem UNGreenCorrC_toC (M : UNModel sz) : UNGreenCorrC sz M.toC ↔ UNGreenCorr sz M := by
  unfold UNGreenCorrC UNGreenCorr
  simp only [unPinsK_toC_toUNModel, UNClaim417C_toC, unPinsK_eig_toC]

/-- `UNInfty1C` at mean `0` is the merged `UNInfty1`. -/
theorem UNInfty1C_toC (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (τU : ℝ) :
    UNInfty1C sz M.toC ρ E E' k O τU ↔ UNInfty1 sz M ρ E E' k O τU := by
  unfold UNInfty1C UNInfty1
  simp only [unPinsK_toC_toUNModel, unPinsK_eig_toC]

/-- `UNUnivMainC` at mean `0` is the merged `UNUnivMain`. -/
theorem UNUnivMainC_toC (M : UNModel sz) (ρ : ℕ → ℝ) (E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (τU : ℝ) :
    UNUnivMainC sz M.toC ρ E k O τU ↔ UNUnivMain sz M ρ E k O τU := by
  unfold UNUnivMainC UNUnivMain
  simp only [unPinsK_toC_toUNModel, unPinsK_eig_toC]

end ClaimC2

/-- `UNGreenCorrAllC` gives the merged `UNGreenCorrAll` (one direction, through `toC`). -/
theorem UNGreenCorrAllC.toAll (h : UNGreenCorrAllC) : UNGreenCorrAll :=
  fun d hd sz hs M => (UNGreenCorrC_toC M).1 (h d hd sz hs M.toC)

section Init

variable {d : ℕ} {sz : Sizes d}

/-- **Pin `UNTrLocalInit`** (probe `:2544-2549`, under S1; `stieltjesN` of the initial matrix). -/
def UNTrLocalInit (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
  ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 ∧
        ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
          ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-- `vOU` of Step 1 read from the initial matrix: `v_i = λ_i(A) - E₀`, `A = ouInit M n t* ω`, `t* = N^{-1+τ_s}`
(probe `vOUC`, `:2535-2538`, under S1; merged `vOU`, `Pins.lean:573-576`, is `e^{-t*/2} λ_i(H) - E₀`). -/
def vOUC (sz : Sizes d) (M : UNModelC sz) (n : ℕ) (τs E₀ : ℝ) (ω : Sizes.SeqΩ sz) :
    Idx d (sz.L n) (sz.W n) → ℝ :=
  fun i => (ouInit_isHermitian M n (ouTStar sz τs n) ω).eigenvalues i - E₀

/-- **Pin `UNStep1GoodC`** (probe `:2553-2568`, under S1, S4: merged `UNStep1Good`, `Pins.lean:584-594`, with
`vOU ↦ vOUC` and `UNTrLocal ↦ UNTrLocalInit`): the regularity event of Step 1 for the DBM initial data of the
centred flow.  Registry class: **owed** (UN, Step 1). -/
def UNStep1GoodC : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M.toUNModel CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **The core `UNCoreC`** (probe `:2570-2577`, under S1-S5: merged `UNCore`, `Pins.lean:760-766`, with the added
hypothesis `UNTrLocalInit`, `UNGreenCorrAll ↦ UNGreenCorrAllC`, `UNClaimAll ↦ UNClaimAllC`, and the model-level pins
at `M.toUNModel`): universality from the inputs for a model with a mean and the centred OU flow.  Registry class:
**owed** (UN). -/
def UNCoreC : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAllC →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNTrLocalInit sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀) → UNClaimAllC sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M.toUNModel ρ E E' k O

end Init

/-! ## 3. The model class and the generic Claim `(417)` pins -/

/-- The model class: the four data in which the band and block Anderson models enter the Claim `(417)` pins
(probe `:2243-2252`; field `M` is now a `UNModelC`). -/
structure UNKind (d : ℕ) where
  M : ∀ sz : Sizes d, UNModelC sz
  lamV : ∀ sz : Sizes d, ℕ → ℝ
  bulk : ∀ sz : Sizes d, ℝ → ℝ → ℕ → Prop
  mdet : ∀ sz : Sizes d, ℕ → ℂ → ℂ

/-- The band kind: `UNModel.band` (mean `0`), profile coupling `sz.lam`, bulk `|E| ≤ 2 - κ`, `m = msc`
(probe `UNKind.band`, `:2254-2258`, under S6). -/
def UNKind.band (d : ℕ) : UNKind d where
  M := fun sz => (UNModel.band sz).toC
  lamV := fun sz => sz.lam
  bulk := fun _ κ E _ => |E| ≤ 2 - κ
  mdet := fun _ _ => msc

section Claims

variable {d : ℕ}

/-- **Pin `UNOUQUEk`** (probe `:2275-2281`, under S2, S3). -/
def UNOUQUEk (K : UNKind d) (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
  ∀ κ τQ : ℝ, 0 < κ → 0 < τQ → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
    ∀ E : ℝ, K.bulk sz κ E n → ∀ a : Zd d (sz.L n),
      ouP (K.M sz).toUNModel n
          {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E a
            (ouMatC (K.M sz) n t ω)} ≤
        queBound (sz.W n) 𝔡 (𝔡 / 3) (𝔡 / 6) τQ

/-- **Pin `UNOUDiagk`** (probe `:2284-2291`, under S2, S3). -/
def UNOUDiagk (K : UNKind d) (sz : Sizes d) (τU : ℝ) : Prop :=
  ∀ κ ε D : ℝ, 0 < κ → 0 < ε → 0 < D → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
    ∀ E : ℝ, K.bulk sz κ E n →
      ouP (K.M sz).toUNModel n {ω | ∃ x : Idx d (sz.L n) (sz.W n),
          Nsz sz n ^ ε <
            ‖Gres (ouMatC (K.M sz) n t ω)
                ((E : ℂ) + ((Nsz sz n ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) true x x‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **Pin `UNEMCTE2k`** (probe `:2296-2313`, under S2, S3). -/
def UNEMCTE2k (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow sz E C₀ τU n (z i)) → ∀ B : ℝ, 0 ≤ B →
      (∀ s : ℝ, 0 ≤ s → s ≤ ouTStar sz τU n → ∀ u : Fin nf,
        ∫ ω, (∏ j ∈ Finset.univ.erase u,
            (stieltjesN (ouMatC (K.M sz) n s ω) (z j)).im) *
          L1t d (sz.L n) (sz.W n) (K.lamV sz n) (ouMatC (K.M sz) n s ω) (z u)
          ∂(ouP (K.M sz).toUNModel n) ≤ B) →
      (∀ s : ℝ, 0 ≤ s → s ≤ ouTStar sz τU n → ∀ u v : Fin nf, u ≠ v →
        ∫ ω, (∏ k ∈ (Finset.univ.erase u).erase v,
            (stieltjesN (ouMatC (K.M sz) n s ω) (z k)).im) *
          L2t d (sz.L n) (sz.W n) (K.lamV sz n) (ouMatC (K.M sz) n s ω) (z u) (z v)
          ∂(ouP (K.M sz).toUNModel n) ≤ B) →
      ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
        |(∫ ω, ∏ i, (stieltjesN (ouMatC (K.M sz) n t ω) (z i)).im ∂(ouP (K.M sz).toUNModel n)) -
          ∫ ω, ∏ i, (stieltjesN (ouMatC (K.M sz) n (ouTStar sz τU n) ω) (z i)).im
            ∂(ouP (K.M sz).toUNModel n)| ≤
          Nsz sz n ^ ε * Nsz sz n ^ (-1 + Cn * τU) * B

/-- **Pin `UNJakk`** (probe `:2316-2326`, under S2, S3). -/
def UNJakk (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow sz E C₀ τU n (z i)) → ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
      ∀ (s : Finset (Fin nf)) (i : Fin nf) (y : Idx d (sz.L n) (sz.W n)) (b₁ b₂ : Bool),
        ∫ ω, (∏ j ∈ s, (stieltjesN (ouMatC (K.M sz) n t ω) (z j)).im) *
          ‖∑ x, (Gres (ouMatC (K.M sz) n t ω) (z i) b₁ *
              Gres (ouMatC (K.M sz) n t ω) (z i) b₁) x x *
            scirc d (sz.L n) (sz.W n) (K.lamV sz n) x y *
              Gres (ouMatC (K.M sz) n t ω) (z i) b₂ y y‖
          ∂(ouP (K.M sz).toUNModel n) ≤
          Nsz sz n ^ ε * Nsz sz n ^ (1 - c' + C * τU)

/-- **Pin `UNUywk`** (probe `:2329-2340`, under S2, S3). -/
def UNUywk (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow sz E C₀ τU n (z i)) → ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
      ∀ (s : Finset (Fin nf)) (i j : Fin nf), i ≠ j → ∀ (y : Idx d (sz.L n) (sz.W n)) (b₁ b₂ : Bool),
        ∫ ω, (∏ k ∈ s, (stieltjesN (ouMatC (K.M sz) n t ω) (z k)).im) *
          ‖∑ x, (Gres (ouMatC (K.M sz) n t ω) (z i) b₁ *
              Gres (ouMatC (K.M sz) n t ω) (z i) b₁) x y *
            scirc d (sz.L n) (sz.W n) (K.lamV sz n) x y *
              (Gres (ouMatC (K.M sz) n t ω) (z j) b₂ *
                Gres (ouMatC (K.M sz) n t ω) (z j) b₂) y x‖
          ∂(ouP (K.M sz).toUNModel n) ≤
          Nsz sz n ^ ε * Nsz sz n ^ (2 - c' + C * τU)

end Claims

/-! ## 4. The consumed shapes, the generic rows and `un_claimAll_of_rowsk` -/

section Consumed

/-- **Consumed `UNQuek`** (probe `:2378-2384`, verbatim: it reads only `μ`, `H`, `bulk`). -/
def UNQuek (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, (K d).bulk sz κ E n → ∀ a : Zd d (sz.L n),
        ((K d).M sz).μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (((K d).M sz).H n ω)} ≤
          queBound (sz.W n) 𝔡 ε₀ c τ

/-- **Consumed `UNLocAvgk`** (probe `:2390-2398`, verbatim). -/
def UNLocAvgk (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      ((K d).M sz).μ {ω | ∃ z : ℂ, ((K d).bulk sz κ z.re n ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1) ∧
          ∃ a : Zd d (sz.L n),
          ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
            ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
                Gres (((K d).M sz).H n ω) z true x x - (K d).mdet sz n z‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

end Consumed

section Rows

/-- `UNOUClaimsk` (probe `:2426-2428`, verbatim). -/
def UNOUClaimsk (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUEk (K d) sz 𝔡 τU ∧ UNOUDiagk (K d) sz τU

/-- **Row `UNOURowk`** (probe `:2433`, verbatim). -/
def UNOURowk (K : ∀ d, UNKind d) (ML Loc Que : Prop) : Prop := ML → Loc → Que → UNOUClaimsk K

/-- **Row `UNEMCTE2Rowk`** (probe `:2441-2444`, verbatim). -/
def UNEMCTE2Rowk (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNEMCTE2k (K d) sz E nf τU Cn

/-- **Row `UNJakUywRowk`** (probe `:2448-2452`, verbatim). -/
def UNJakUywRowk (K : ∀ d, UNKind d) (Loc : Prop) : Prop :=
  Loc → UNOUClaimsk K → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNJakk (K d) sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUywk (K d) sz E nf τU C (𝔠 * 𝔡 / 30)

/-- **Row `UNClaimRowk`** (probe `:2456-2463`, under S5: the conclusion is `UNClaimAllC`). -/
def UNClaimRowk (K : ∀ d, UNKind d) : Prop :=
  (∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ Cn C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNEMCTE2k (K d) sz E nf τU Cn ∧ UNJakk (K d) sz E nf τU C (𝔠 * 𝔡 / 30) ∧
          UNUywk (K d) sz E nf τU C (𝔠 * 𝔡 / 30)) →
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E

/-- **The Claim `(417)` from the rows, for every class `K`** (probe `un_claimAll_of_rowsk`, `:2467-2477`, proof
verbatim; statement `T2187_un_claimAll_of_rowsk` of the check file): the output is `UNClaimAllC sz (K d).M E`, the
input of the core `UNCoreC`. -/
theorem un_claimAll_of_rowsk (K : ∀ d, UNKind d) {ML Loc Que : Prop}
    (rC : UNClaimRowk K) (rE : UNEMCTE2Rowk K) (rJ : UNJakUywRowk K Loc) (rO : UNOURowk K ML Loc Que)
    (hML : ML) (hLoc : Loc) (hQ : Que) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E := by
  have hOU := rO hML hLoc hQ
  apply rC
  intro d hd 𝔠 𝔡 sz hA κ hκ E hE nf
  obtain ⟨Cn, τ₁, hτ₁, h1⟩ := rE d hd 𝔠 𝔡 sz hA κ hκ E hE nf
  obtain ⟨C, τ₂, hτ₂, h2⟩ := rJ hLoc hOU d hd 𝔠 𝔡 sz hA κ hκ E hE nf
  refine ⟨Cn, C, min τ₁ τ₂, lt_min hτ₁ hτ₂, fun τU h0 hle => ?_⟩
  have hJU := h2 τU h0 (hle.trans (min_le_right _ _))
  exact ⟨h1 τU h0 (hle.trans (min_le_left _ _)), hJU.1, hJU.2⟩

/-- The statement `T2187_un_claimAll_of_rowsk` of the check file, as a compiled `example` (body copied by script). -/
example :
  ∀ (K : ∀ d, UNKind d) {ML Loc Que : Prop},
    UNClaimRowk K → UNEMCTE2Rowk K → UNJakUywRowk K Loc → UNOURowk K ML Loc Que → ML → Loc → Que →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E :=
  fun K => un_claimAll_of_rowsk K

end Rows

section TZero

variable {d : ℕ} {sz : Sizes d}

/-- A cylinder set of the OU carrier has the measure of its base (probe `ouP_cylinder`, `:2917-2925`, under S1). -/
theorem ouP_cylinder (M : UNModelC sz) (n : ℕ) (S : Set (Sizes.SeqΩ sz)) :
    ouP M.toUNModel n {ω | ω.1 ∈ S} = M.μ S := by
  have h : {ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) | ω.1 ∈ S} = S ×ˢ Set.univ := by
    ext ω; simp
  rw [h]
  unfold ouP
  rw [Measure.prod_prod, measure_univ, mul_one]

/-- **At `t = 0` the `𝐇_t` claim `UNOUQUEk` is the consumed QUE `UNQuek`** (`ouMatC M n 0 = H`, `ouMatC_zero`):
for the parameters `(ε₀, c) = (𝔡/3, 𝔡/6)` of `1_2:575-577`, `UNQuek K` gives the `t = 0` case of `UNOUQUEk (K d)`
for every class `K` (probe `UNOUQUEk_zero_of_UNQuek`, `:2927-2940`, under S2, S3). -/
theorem UNOUQUEk_zero_of_UNQuek (K : ∀ d, UNKind d) (hQ : UNQuek K) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ}
    (hA : sz.Admissible 𝔠 𝔡) (κ τQ : ℝ) (hκ : 0 < κ) (hτ : 0 < τQ) :
    ∀ᶠ n in atTop, ∀ E : ℝ, (K d).bulk sz κ E n → ∀ a : Zd d (sz.L n),
      ouP ((K d).M sz).toUNModel n
          {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E a
            (ouMatC ((K d).M sz) n 0 ω)} ≤
        queBound (sz.W n) 𝔡 (𝔡 / 3) (𝔡 / 6) τQ := by
  have h𝔡 : 0 < 𝔡 := hA.2.1
  filter_upwards [hQ d hd 𝔠 𝔡 sz hA κ hκ (𝔡 / 3) (𝔡 / 6) τQ (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hτ] with n hn E hE a
  have h1 := hn E hE a
  simp only [ouMatC_zero]
  exact (ouP_cylinder ((K d).M sz) n
    {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E a (((K d).M sz).H n ω)}).le.trans h1

end TZero

/-! ## 5. Band bridges: at `UNKind.band` the generic pins and rows are the merged ones -/

section Band

variable {d : ℕ}

theorem unPinsK_band_bulk (sz : Sizes d) (κ E : ℝ) (n : ℕ) :
    (UNKind.band d).bulk sz κ E n = (|E| ≤ 2 - κ) := rfl

theorem unPinsK_band_M (sz : Sizes d) : (UNKind.band d).M sz = (UNModel.band sz).toC := rfl

theorem UNOUQUEk_band (sz : Sizes d) (𝔡 τU : ℝ) :
    UNOUQUEk (UNKind.band d) sz 𝔡 τU ↔ UNOUQUE sz 𝔡 τU := by
  unfold UNOUQUEk UNOUQUE
  rw [unPinsK_band_M, ouMatC_toC]
  exact Iff.rfl

theorem UNOUDiagk_band (sz : Sizes d) (τU : ℝ) :
    UNOUDiagk (UNKind.band d) sz τU ↔ UNOUDiag sz τU := by
  unfold UNOUDiagk UNOUDiag
  rw [unPinsK_band_M, ouMatC_toC]
  exact Iff.rfl

theorem UNEMCTE2k_band (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) :
    UNEMCTE2k (UNKind.band d) sz E nf τU Cn ↔ UNEMCTE2 sz E nf τU Cn := by
  unfold UNEMCTE2k UNEMCTE2
  rw [unPinsK_band_M, ouMatC_toC]
  exact Iff.rfl

theorem UNJakk_band (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) :
    UNJakk (UNKind.band d) sz E nf τU C c' ↔ UNJak sz E nf τU C c' := by
  unfold UNJakk UNJak
  rw [unPinsK_band_M, ouMatC_toC]
  exact Iff.rfl

theorem UNUywk_band (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) :
    UNUywk (UNKind.band d) sz E nf τU C c' ↔ UNUyw sz E nf τU C c' := by
  unfold UNUywk UNUyw
  rw [unPinsK_band_M, ouMatC_toC]
  exact Iff.rfl

theorem UNQuek_band : UNQuek (fun d => UNKind.band d) ↔ UNQueBand := Iff.rfl

theorem UNLocAvgk_band : UNLocAvgk (fun d => UNKind.band d) ↔ UNLocAvgBand := Iff.rfl

theorem UNOUClaimsk_band : UNOUClaimsk (fun d => UNKind.band d) ↔ UNOUClaims := by
  unfold UNOUClaimsk UNOUClaims
  simp only [UNOUQUEk_band, UNOUDiagk_band]

theorem UNOURowk_band :
    UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand ↔ UNOURow := by
  unfold UNOURowk UNOURow
  rw [UNOUClaimsk_band]

theorem UNEMCTE2Rowk_band : UNEMCTE2Rowk (fun d => UNKind.band d) ↔ UNEMCTE2Row := by
  unfold UNEMCTE2Rowk UNEMCTE2Row
  simp only [unPinsK_band_bulk, UNEMCTE2k_band, Filter.eventually_const]

theorem UNJakUywRowk_band : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand ↔ UNJakUywRow := by
  unfold UNJakUywRowk UNJakUywRow
  simp only [unPinsK_band_bulk, UNOUClaimsk_band, UNJakk_band, UNUywk_band, Filter.eventually_const]

theorem UNClaimRowk_band : UNClaimRowk (fun d => UNKind.band d) ↔ UNClaimRow := by
  unfold UNClaimRowk UNClaimRow
  simp only [unPinsK_band_bulk, unPinsK_band_M, UNEMCTE2k_band, UNJakk_band, UNUywk_band,
    Filter.eventually_const, UNClaimAllC_toC]

/-- **The merged `UNClaimAll` of the band model from the four generic band rows** and `UNMLOut`, `UNLocAvgBand`,
`UNQueBand`: the band chain closes on the generic forms. -/
theorem un_claimAll_of_rowsk_band
    (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d))
    (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand)
    (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, |E| ≤ 2 - κ → UNClaimAll sz (UNModel.band sz) E := by
  intro d hd 𝔠 𝔡 sz hA κ hκ E hE
  exact (UNClaimAllC_toC (UNModel.band sz) E).1
    (un_claimAll_of_rowsk (fun d => UNKind.band d) rC rE rJ rO hML hLoc hQ d hd 𝔠 𝔡 sz hA κ hκ E
      (Filter.Eventually.of_forall fun _ => hE))

end Band

/-! ## 6. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2)

The data are those of `UNInst` (`Pins.lean`, section 7): `RBM.Gauss.SizesInst.sz0` (`n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `k = 1`, `E = 0`, `E' = 0`, `δ = 1/2`,
`𝒪 = bump`.  Hypotheses that are pins of other gates (the rows, the consumed shapes, `UNL32`, `UNGUELocal`,
`UNGreenCorrAll(C)`, `UNTrLocal`, `UNTrLocalInit`, the norm bound) stay hypotheses; every deterministic hypothesis
is discharged. -/

namespace UNKInst

open RBM.Gauss.SizesInst UNInst

/-- `z = E + i N⁻¹` lies in the spectral window `|Re z - E| ≤ C₀/N`, `N^{-1-τ_U} ≤ Im z ≤ N^{-1+τ_U}`
(probe `inWindow_nonempty`, `:3454`, verbatim): the window of `(417)` is nonempty. -/
theorem inWindow_nonempty (sz : Sizes 3) (E C₀ τU : ℝ) (n : ℕ) (hC : 0 ≤ C₀) (hτ : 0 ≤ τU) :
    InWindow sz E C₀ τU n ⟨E, (Nsz sz n)⁻¹⟩ := by
  have hN : (1 : ℝ) ≤ Nsz sz n := by
    have h1 : 1 ≤ sz.size n := by
      simp only [Sizes.size]
      have := sz.three_le_L n
      have := sz.W_pos n
      exact Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by omega))
    exact_mod_cast h1
  have hinv : (Nsz sz n)⁻¹ = Nsz sz n ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
  refine ⟨?_, ?_, ?_⟩
  · simp only [sub_self, abs_zero]
    exact div_nonneg hC (by linarith)
  · change Nsz sz n ^ (-1 - τU) ≤ (Nsz sz n)⁻¹
    rw [hinv]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · change (Nsz sz n)⁻¹ ≤ Nsz sz n ^ (-1 + τU)
    rw [hinv]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The Claim `(417)` of the band model, in the centred form, from the four generic band rows (`un_claimAll_of_rowsk`
at `UNKind.band`), at the instance (`κ = 1/10`, `E = 0`). -/
theorem inst_claimAllC_band
    (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d))
    (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand)
    (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNClaimAllC sz0 (UNModel.band sz0).toC 0 :=
  un_claimAll_of_rowsk (fun d => UNKind.band d) rC rE rJ rO hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0
    sz0_adm (1 / 10) (by norm_num) 0 (Filter.Eventually.of_forall fun _ => by rw [unPinsK_band_bulk]; norm_num)

/-- The merged `UNClaimAll` of the band model at the instance from the four generic band rows. -/
theorem inst_claimAll_band_k
    (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d))
    (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand)
    (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNClaimAll sz0 (UNModel.band sz0) 0 :=
  un_claimAll_of_rowsk_band rC rE rJ rO hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (1 / 10)
    (by norm_num) 0 (by norm_num)

/-- **`Thm: B_Univ` (band) at the instance** (conclusion of `UNInst.inst_bUniv_band`) with the four band rows taken in
generic form through the row bridges; the merged `UNInfty1Row`, `UNUnivMainRow`, `UNDensBandRow`, `UNTrLocalBandRow`,
`UNNormBandRow`, `UNL32`, `UNGUELocal`, `UNGreenCorrAll` and the consumed `UNMLOut`, `UNLocAvgBand`, `UNQueBand` stay
hypotheses. -/
theorem inst_bUniv_band_k (rI : UNInfty1Row) (rU : UNUnivMainRow)
    (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d))
    (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand)
    (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (rD : UNDensBandRow) (rT : UNTrLocalBandRow) (rN : UNNormBandRow) (h32 : UNL32)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) (hGL : UNGUELocal)
    (hGC : UNGreenCorrAll) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
      atTop (𝓝 0) :=
  inst_bUniv_band rI rU (UNClaimRowk_band.1 rC) (UNEMCTE2Rowk_band.1 rE) (UNJakUywRowk_band.1 rJ)
    (UNOURowk_band.1 rO) rD rT rN h32 hML hLoc hQ hGL hGC

/-- **The centred core at the band model** at the instance: `UNCoreC` at `(UNModel.band sz0).toC`, `m = msc`, `E = 0`,
`ρ = ρ_sc(0)`, `δ = 1/2`, `E' = 0`, `k = 1`, `𝒪 = bump`; `UNDens` is discharged (`un_dens_msc_zero`); the local laws
`UNTrLocal`, `UNTrLocalInit`, the norm bound, `UNClaimAllC` and the pins `UNL32`, `UNGUELocal`, `UNGreenCorrAllC` stay
hypotheses. -/
theorem inst_coreC_band (hcore : UNCoreC) (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC)
    (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2))
    (hTi : UNTrLocalInit sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 2))
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀)
    (hC : UNClaimAllC sz0 (UNModel.band sz0).toC 0) :
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) :=
  hcore h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0).toC (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens_msc_zero hT hTi hN hC 0 (by norm_num) 1 le_rfl bump bump_testFun

/-- **The `t = 0` case of the `𝐇_t` QUE claim at the instance** from the consumed `UNQueBand`
(`UNOUQUEk_zero_of_UNQuek` at the band kind; `κ = 1/10`, `τ_Q = 1/2`). -/
theorem inst_OUQUEk_zero_band (hQ : UNQueBand) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 → ∀ a : Zd 3 (sz0.L n),
      ouP (UNModel.band sz0) n
          {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) ((1 / 10) / 3) ((1 / 10) / 6) E a
            (ouMatC (UNModel.band sz0).toC n 0 ω)} ≤
        queBound (sz0.W n) (1 / 10) ((1 / 10) / 3) ((1 / 10) / 6) (1 / 2) :=
  UNOUQUEk_zero_of_UNQuek (fun d => UNKind.band d) (UNQuek_band.2 hQ) (le_refl 3) sz0_adm (1 / 10) (1 / 2)
    (by norm_num) (by norm_num)

private theorem unPinsK_blk0 : blk 4 32 (0 : ZMod (32 * 4)) = 0 := by decide

private theorem unPinsK_blk32 : blk 4 32 (32 : ZMod (32 * 4)) = 1 := by decide

private theorem unPinsK_ofs_eq : ofs 4 32 (0 : ZMod (32 * 4)) = ofs 4 32 32 := by decide

/-- `Ψ` has the entry `1` between the block `0` and the block `e₁` (same offset `0`) at `(L, W) = (4, 32)`. -/
private theorem unPinsK_psiI_entry :
    PsiI 3 4 32 (0 : Idx 3 4 32) (fun k => if k = 0 then 32 else 0) = 1 := by
  have hj : (fun k : Fin 3 => blk 4 32 (if k = 0 then (32 : ZMod (32 * 4)) else 0)) =
      fun k => if k = 0 then 1 else 0 := by
    funext k; by_cases h : k = 0 <;> simp [h, unPinsK_blk32, unPinsK_blk0]
  have hi : (fun k : Fin 3 => blk 4 32 (0 : (ZMod (32 * 4)))) = 0 := by
    funext k; simp [unPinsK_blk0]
  have ho : (fun k : Fin 3 => ofs 4 32 (if k = 0 then (32 : ZMod (32 * 4)) else 0)) =
      fun k : Fin 3 => ofs 4 32 (0 : ZMod (32 * 4)) := by
    funext k; by_cases h : k = 0 <;> simp [h, unPinsK_ofs_eq]
  have hadj : Adj 3 4 (0 : Zd 3 4) (fun k => if k = 0 then 1 else 0) := by
    unfold Adj zdistD; decide
  simpa [PsiI, PsiV, PsiB, splitEquiv, split, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, hj, hi, ho]
    using hadj

/-- A model with a nonzero mean at the instance (not the BA kind): the law and matrix of `UNModel.ba sz0` with the
mean `λ Ψ`. -/
private def unPinsK_baC : UNModelC sz0 :=
  { UNModel.ba sz0 with
    mean := fun n => (sz0.lam n : ℂ) • PsiI 3 (sz0.L n) (sz0.W n)
    mean_herm := fun n => by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, (PsiI_isHermitian 3 _ _).eq,
        show star (sz0.lam n : ℂ) = (sz0.lam n : ℂ) from Complex.conj_ofReal _] }

/-- **A model with nonzero mean at the instance**: the centred flow differs from the merged flow `ouMat` at `n = 0`,
`t > 0` in the entry between the blocks `0` and `e₁` (offset `0`), where the mean is `λ_0 Ψ_{ij} = 1/64` and the
difference is `(1 - e^{-t/2})/64 > 0` (`ouMatC_eq_ouMat_add`). -/
theorem inst_ouMatC_ne_ouMat (t : ℝ) (ht : 0 < t) :
    ∃ M : UNModelC sz0, ∀ ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0),
      ∃ i j : Idx 3 (sz0.L 0) (sz0.W 0), ouMatC M 0 t ω i j ≠ ouMat M.toUNModel 0 t ω i j := by
  refine ⟨unPinsK_baC, fun ω => ?_⟩
  let i0 : Idx 3 (sz0.L 0) (sz0.W 0) := 0
  let j0 : Idx 3 (sz0.L 0) (sz0.W 0) := fun k => if k = 0 then 32 else 0
  refine ⟨i0, j0, fun h1 => ?_⟩
  rw [ouMatC_eq_ouMat_add] at h1
  simp only [Matrix.add_apply, Matrix.smul_apply] at h1
  have hm : unPinsK_baC.mean 0 i0 j0 = ((1 / 64 : ℝ) : ℂ) := by
    change ((sz0.lam 0 : ℝ) : ℂ) * PsiI 3 4 32 (0 : Idx 3 4 32) (fun k => if k = 0 then 32 else 0) = _
    rw [unPinsK_psiI_entry]
    norm_num [sz0]
  rw [hm, Complex.real_smul] at h1
  have h2 : ((((1 - Real.exp (-t / 2)) * (1 / 64) : ℝ)) : ℂ) = 0 := by
    push_cast at h1 ⊢
    linear_combination h1
  rw [Complex.ofReal_eq_zero] at h2
  have hlt : Real.exp (-t / 2) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  nlinarith

end UNKInst

end RBM.Univ
