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

end Flow

/-! The pinned statements `T2187_ouMatC_eq_ouMat_add`, `T2187_ouMatC_mean_zero` of the check file, as compiled
`example`s (the bodies are copied from the check file by script). -/

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

end ClaimC2

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

end Rows

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

theorem UNClaimRowk_band : UNClaimRowk (fun d => UNKind.band d) ↔ UNClaimRow := by
  unfold UNClaimRowk UNClaimRow
  simp only [unPinsK_band_bulk, unPinsK_band_M, UNEMCTE2k_band, UNJakk_band, UNUywk_band,
    Filter.eventually_const, UNClaimAllC_toC]

end Band

/-! ## 6. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2)

The data are those of `UNInst` (`Pins.lean`, section 7): `RBM.Gauss.SizesInst.sz0` (`n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `k = 1`, `E = 0`, `E' = 0`, `δ = 1/2`,
`𝒪 = bump`.  Hypotheses that are pins of other gates (the rows, the consumed shapes, `UNL32`, `UNGUELocal`,
`UNGreenCorrAll(C)`, `UNTrLocal`, `UNTrLocalInit`, the norm bound) stay hypotheses; every deterministic hypothesis
is discharged. -/

end RBM.Univ
