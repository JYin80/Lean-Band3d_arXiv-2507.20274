/-
Release check for T2187 (dispatcher V1, Mon Oct  5 07:09 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §57).
UN-01b: promote the model-generic part of the BA-DS probe (`t/T2173` at a543154, `RBM3D/Probe/T2173Pins.lean`) to
`RBM3D/Universality/PinsK.lean` without changing any merged signature (CLAUDE.md §5.3, DECISIONS §57 (1)).
Section 1: the merged names the new file builds on (UN-01 = T2174 `Universality/Pins.lean`, the Gaussian model, the
block Anderson matrix, the instance data, the registry) and the Mathlib names of the route.
Section 2: the pinned vocabulary (`UNModelC`, `ouMatC`, `ouInit`, `UNKind`) and the pinned statements that need no
proof term to elaborate, in namespace `RBM.Univ.T2187Check` here; T2187 defines them in `RBM.Univ` verbatim.  The
pins that read eigenvalues (`UNGreenCorrC`, `UNGreenCorrAllC`, `UNInfty1C`, `UNUnivMainC`, `vOUC`, `UNStep1GoodC`,
`UNCoreC`) need the proofs `ouMatC_isHermitian`, `ouInit_isHermitian` and are not elaborated here: they are the merged
text (`Universality/Pins.lean:535-594`, `:760-766`) and the probe text (`:2535-2577`) under the substitutions S1-S5 of
the ticket; every name they use is `#check`ed in section 1.  Section 2 also states (as `Prop`s, not proved) the two
flow identities behind the bridges.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2187-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4): the model, the OU carrier and the non-centred flow
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.UNModel.ba
#check @RBM.Univ.ouTStar
#check @RBM.Univ.ouP
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouMat_isHermitian
#check @RBM.Univ.ouMat_zero
-- UN-01: the claim-level pins (copied as `…C` over `UNModelC`) and the model-level ones (reused at `M.toUNModel`)
#check @RBM.Univ.UNUnivDilAt
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNDens
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.InWindow
#check @RBM.Univ.UNClaim417
#check @RBM.Univ.UNClaimAll
#check @RBM.Univ.UNApriori
#check @RBM.Univ.UNGreenCorr
#check @RBM.Univ.UNGreenCorrAll
#check @RBM.Univ.UNInfty1
#check @RBM.Univ.UNUnivMain
#check @RBM.Univ.vOU
#check @RBM.Univ.UNStep1Good
#check @RBM.Univ.IsRegular32
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.UNL32
#check @RBM.Univ.UNCore
#check @RBM.Univ.UNInfty1Row
#check @RBM.Univ.UNUnivMainRow
#check @RBM.Univ.un_core_of_rows
-- UN-01: the band chain (the targets of the band bridges)
#check @RBM.Univ.scirc
#check @RBM.Univ.L1t
#check @RBM.Univ.L2t
#check @RBM.Univ.UNOUQUE
#check @RBM.Univ.UNOUDiag
#check @RBM.Univ.UNOUClaims
#check @RBM.Univ.UNEMCTE2
#check @RBM.Univ.UNJak
#check @RBM.Univ.UNUyw
#check @RBM.Univ.UNQueBand
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.UNMLOut
#check @RBM.Univ.UNOURow
#check @RBM.Univ.UNEMCTE2Row
#check @RBM.Univ.UNJakUywRow
#check @RBM.Univ.UNClaimRow
#check @RBM.Univ.UNDensBandRow
#check @RBM.Univ.UNNormBandRow
#check @RBM.Univ.UNTrLocalBandRow
#check @RBM.Univ.un_claimAll_of_rows
#check @RBM.Univ.un_bUniv_of_rows
#check @RBM.Univ.UNBUniv
-- UN-01: vocabulary
#check @RBM.Univ.queBound
#check @RBM.Univ.queBadMat
#check @RBM.Univ.Nsz
#check @RBM.Univ.stieltjesN
#check @RBM.Univ.IsTestFun
#check @RBM.Univ.kPoint
#check @RBM.Univ.gueP
#check @RBM.Univ.rhoSC
#check @RBM.Univ.un_dens_msc_zero
-- UN-01 section 7: the instance data reused by T2187's instances
#check @RBM.Univ.UNInst.bump
#check @RBM.Univ.UNInst.bump_testFun
#check @RBM.Univ.UNInst.sz0_adm
#check @RBM.Univ.UNInst.inst_bUniv_band
#check @RBM.Univ.UNInst.inst_core_band
#check @RBM.Univ.UNInst.inst_claimAll_band
-- Gaussian model, block Anderson matrix, sizes, resolvent, semicircle
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Xmat_isHermitian
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.PsiI_isHermitian
#check @RBM.Gauss.Sizes.seqHBA
#check @RBM.Gauss.Sizes.seqHBA_isHermitian
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.Gres
#check @RBM.msc
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
-- registry (DECISIONS §16, §20)
#check @RBM.Audit.borrowedProps
#check @RBM.Audit.owedProps
#check @RBM.Audit.structuralProps
-- Mathlib names of the route (bridges)
#check @Filter.eventually_const
#check @Matrix.isHermitian_zero
#check @Matrix.IsHermitian.eigenvalues

/-! ## 2. Pinned vocabulary and statements (T2187 targets 1-4; defined in `RBM.Univ` verbatim) -/

set_option linter.unusedVariables false

noncomputable section

namespace RBM.Univ.T2187Check

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-- **The centred model (primed successor of the merged `UNModel`, CLAUDE.md §5.3)**: a model and the deterministic
mean `E H` that the centred OU flow holds fixed (`0` for the band model, `ilambda Ψ` for block Anderson).  This is the
probe's amended `UNModel` (A1, probe `:119-130`) under a new name. -/
structure UNModelC {d : ℕ} (sz : Sizes d) extends UNModel sz where
  /-- the deterministic mean `E H` -/
  mean : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
  mean_herm : ∀ n, (mean n).IsHermitian

/-- The model class: the four data in which the band and block Anderson models enter the Claim `(417)` pins
(probe `:2243-2252`; field `M` is now a `UNModelC`). -/
structure UNKind (d : ℕ) where
  M : ∀ sz : Sizes d, UNModelC sz
  lamV : ∀ sz : Sizes d, ℕ → ℝ
  bulk : ∀ sz : Sizes d, ℝ → ℝ → ℕ → Prop
  mdet : ∀ sz : Sizes d, ℕ → ℂ → ℂ

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

end Flow

/-- Flow identity behind the bridges (target 1, `ouMatC_eq_ouMat_add`; stated here, proved by T2187):
the centred flow is the merged (non-centred) flow plus `(1 - e^{-t/2}) μ`. -/
def T2187_ouMatC_eq_ouMat_add : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    ouMatC M n t ω = ouMat M.toUNModel n t ω + (1 - Real.exp (-t / 2)) • M.mean n

/-- Flow identity at mean `0` (target 1, `ouMatC_toC`, pointwise form): the centred flow of a model with mean `0` is the
merged `ouMat`. -/
def T2187_ouMatC_mean_zero : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz), (∀ n, M.mean n = 0) →
    ∀ (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)), ouMatC M n t ω = ouMat M.toUNModel n t ω

section ClaimC

variable {d : ℕ}

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

/-- **Pin `UNTrLocalInit`** (probe `:2544-2549`, under S1; `stieltjesN` of the initial matrix). -/
def UNTrLocalInit (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
  ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 ∧
        ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
          ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

end ClaimC

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

/-- Statement of `un_claimAll_of_rowsk` (probe `:2467-2471`, under S5; T2187 proves it with the probe proof). -/
def T2187_un_claimAll_of_rowsk : Prop :=
  ∀ (K : ∀ d, UNKind d) {ML Loc Que : Prop},
    UNClaimRowk K → UNEMCTE2Rowk K → UNJakUywRowk K Loc → UNOURowk K ML Loc Que → ML → Loc → Que →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E

end Rows

end RBM.Univ.T2187Check

end
