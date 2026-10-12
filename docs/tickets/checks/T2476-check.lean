/-
Release check for T2476 (dispatcher V3, Mon Oct 12 21:29 UTC 2026; DECISIONS §278).  BA stage M/N row N3a: E1 = the BA producer of the merged
pin `UNEMCTE2RowBA` (transfer of the shifted functional, new leaf `BA/EMCTE2BA.lean`) and E2 = the BA producer of the
merged pin `UNJakUywRowBA` (two couplings and the bulk window, in place in `Universality/Jak.lean`, `Universality/Uyw.lean`;
BA discharge in the leaf).  Supervisor 2049 GMN-C2: public statements of the in-place files verbatim; new forms, new names.
Part 1: merged names.  Part 2: the two binding targets (the merged pins themselves), the proposals `T2476_*` (not binding:
the 1a fixes the final premise lists, the auditor compares), shapes.  Part 3: the band declarations kept verbatim (G1) and the
terminal invariants (GMN-C2 (c)).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2476-check.lean
-/
import RBM3D.Universality.Jak
import RBM3D.Universality.JakSpectral
import RBM3D.Universality.JakKernel
import RBM3D.Universality.Uyw
import RBM3D.Universality.UywKernel
import RBM3D.Universality.EMCTE2
import RBM3D.Universality.PinsK
import RBM3D.Universality.OUGenerator
import RBM3D.Universality.OUHessian
import RBM3D.Universality.OUContraction
import RBM3D.Universality.UnivMain
import RBM3D.BA.UNPins
import RBM3D.BA.MReg
import RBM3D.Main.BUnivHolds
import RBM3D.Main.BandTerminal

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the two target pins and their consumer (`BA/UNPins.lean:126-147, 367`)
#check @RBM.Univ.UNEMCTE2RowBA
#check @RBM.Univ.UNJakUywRowBA
#check @RBM.Univ.baBUniv_of_rows
#check @RBM.Univ.un_claimAll_of_rowsBA
#check @RBM.Univ.BAInst.inst_UNEMCTE2RowBA
#check @RBM.Univ.BAInst.inst_UNJakUywRowBA
#check @RBM.Univ.BAInst.inst_claimAll_ba
#check @RBM.Univ.BAInst.inst_univ_ba
#check @RBM.Endpoints.unClaimRowBA_holds
#check @RBM.Univ.unDensBARow'_holds
-- the other hypotheses of the consumer (pins of other rows)
#check @RBM.Univ.UNCoreC''
#check @RBM.Univ.UNL32
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.UNGreenCorrAllC
#check @RBM.Univ.UNDensBARow'
#check @RBM.Univ.UNTrLocalBARow
#check @RBM.Univ.UNTrLocalInitBARow'
#check @RBM.Univ.UNNormBARow
#check @RBM.Univ.UNClaimRowBA
#check @RBM.Univ.UNOURowBA
#check @RBM.Univ.UNMLOutBA
#check @RBM.Univ.UNLocAvgBA
#check @RBM.Univ.UNQueBA
#check @RBM.BA.BAEnd_BUnivL
-- the kind, the centred model and flow, the generic pins and rows (`PinsK`, `BA/UNPins`)
#check @RBM.Univ.UNKind
#check @RBM.Univ.UNKind.band
#check @RBM.Univ.UNKind.ba
#check @RBM.Univ.UNKind.ba_M
#check @RBM.Univ.UNModelC
#check @RBM.Univ.UNModelC.ba
#check @RBM.Univ.UNModelC.ba_spec
#check @RBM.Univ.ouMatC
#check @RBM.Univ.ouMatC_isHermitian
#check @RBM.Univ.ouMatC_toC
#check @RBM.Univ.isProbabilityMeasure_ouP
#check @RBM.Univ.UNEMCTE2k
#check @RBM.Univ.UNJakk
#check @RBM.Univ.UNUywk
#check @RBM.Univ.UNEMCTE2Rowk
#check @RBM.Univ.UNJakUywRowk
#check @RBM.Univ.UNOUClaimsk
#check @RBM.Univ.UNOUQUEk
#check @RBM.Univ.UNOUDiagk
#check @RBM.Univ.UNClaimRowk
#check @RBM.Univ.un_claimAll_of_rowsk
#check @RBM.Univ.unClaimRowk
#check @RBM.Univ.UNEMCTE2k_band
#check @RBM.Univ.UNJakk_band
#check @RBM.Univ.UNUywk_band
#check @RBM.Univ.UNOUQUEk_band
#check @RBM.Univ.UNOUDiagk_band
#check @RBM.Univ.UNEMCTE2Rowk_band
#check @RBM.Univ.UNJakUywRowk_band
#check @RBM.Univ.UNOUClaimsk_band
#check @RBM.Univ.unPinsK_band_bulk
-- E1: the translation identity of the centred flow and the band generator layer
#check @RBM.Univ.ouMatC_ba_eq_band_add
#check @RBM.Univ.ouP_ba_eq_band
#check @RBM.Univ.ouMatC_ba_eq_ouMat
#check @RBM.Univ.UNEMCTE2k_ba_zero
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.PsiI
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouP
#check @RBM.Univ.eq225_interval
#check @RBM.Univ.unEMCTE2_of_sizeTendsto
#check @RBM.Univ.unEMCTE2Row
#check @RBM.Univ.unEMCTE2Rowk_band
#check @RBM.Univ.EMCTE2Inst.inst_eq225_interval
#check @RBM.Univ.TestFunH
#check @RBM.Univ.testFunH_stieltjesImProduct
#check @RBM.Univ.ouGenerator_hasDerivAt_integral
#check @RBM.Univ.ouGenerator_integral_sub_eq
#check @RBM.Univ.wirtSecond
#check @RBM.Univ.centeredVarianceEntry
#check @RBM.Univ.centeredVariance_wirtProduct_kernel_bound_Lt
#check @RBM.Univ.L1t
#check @RBM.Univ.L2t
#check @RBM.Univ.stieltjesN
#check @RBM.Univ.InWindow
#check @RBM.Univ.ouTStar
#check @RBM.Univ.Nsz
-- E2: the kernels (profile coupling only), the bad events, the BA one-block event, the BA bulk window
#check @RBM.Univ.jak_pointwise_good
#check @RBM.Univ.uyw_pointwise_good
#check @RBM.Univ.jakGridGood
#check @RBM.Univ.scirc
#check @RBM.Univ.siteBlock
#check @RBM.Univ.blockM
#check @RBM.Univ.blockM2
#check @RBM.Univ.blockM2_self
#check @RBM.Univ.unBadY_of_blockM
#check @RBM.Univ.measure_bad_le_of_queBadMat
#check @RBM.Univ.measure_bad2_le_of_queBadMat
#check @RBM.Univ.UNBadY
#check @RBM.Univ.unBadY_subset
#check @RBM.Univ.unBadY_measure_le
#check @RBM.Univ.unBadY_card_le
#check @RBM.Univ.queBadMat
#check @RBM.Univ.queBound
#check @RBM.Univ.un_window_sub
#check @RBM.Univ.unBadY_subset'
#check @RBM.Univ.SBR_zero_ne
#check @RBM.Univ.unBadYBA_subset
#check @RBM.Univ.unBadYBA_measure_le
#check @RBM.SBR
#check @RBM.sum_SBR_row
#check @RBM.BA.BAbulk
#check @RBM.BA.BAbulk_window
-- the instance data
#check @RBM.Univ.BAInst.S0
#check @RBM.Univ.BAInst.S0_adm
#check @RBM.Univ.BAInst.S0_bulk
#check @RBM.BA.UNPinsInst.clsκ
#check @RBM.BA.UNPinsInst.fp
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Univ.UNInst.sz0_adm
#check @RBM.Univ.UNKInst.inWindow_nonempty
#check @RBM.Univ.JakInst.inst_unJak
#check @RBM.Univ.JakInst.inst_row

/-! ## Part 2: the targets (binding), the proposals `T2476_*` (not binding) and shapes -/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.Univ
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

-- **Target 4 (E1)**, content binding: the merged pin `UNEMCTE2RowBA` (`BA/UNPins.lean:128`); producer `unEMCTE2RowBA_holds`.
example : Prop := UNEMCTE2RowBA

-- **Target 10 (E2)**, content binding: the merged pin `UNJakUywRowBA` (`BA/UNPins.lean:132`); producer `unJakUywRowBA_holds`.
example : Prop := UNJakUywRowBA

/-- Shape (consumer after this row): `baBUniv_of_rows` (`BA/UNPins.lean:367`) with `rE`, `rJ` discharged; the remaining
hypotheses are pins of other rows or merged results (`rC` = `unClaimRowBA_holds`, `rD` = `unDensBARow'_holds`).  The auditor
writes it as a term from `baBUniv_of_rows` and the two producers. -/
def T2476_BUnivBA : Prop :=
  UNCoreC'' → UNL32 → UNGUELocal → UNGreenCorrAllC → UNDensBARow' → UNTrLocalBARow → UNTrLocalInitBARow' →
    UNNormBARow → UNClaimRowBA → UNOURowBA → (∀ d : ℕ, UNMLOutBA d) → UNLocAvgBA → UNQueBA →
      ∀ d : ℕ, BAEnd_BUnivL d

/-- **Proposal (target 2, E1 core; not binding)**: `eq225_interval` (`Universality/EMCTE2.lean:455`) for the shifted
functional `Φ(A + ·)`, `A` deterministic Hermitian, on the band carrier of any `sz`; the kernels `L1t`, `L2t` are read at
`A + ouMat`.  At `A = 0` it is `eq225_interval`. -/
def T2476_eq225Shift : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n nf : ℕ) (z : Fin nf → ℂ), (∀ i : Fin nf, 0 < (z i).im) →
    ∀ A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, A.IsHermitian →
      ∀ t T Bd : ℝ, 0 ≤ t → t ≤ T →
        (∀ s ∈ Set.Ioo t T,
          ∫ ω, ((∑ i : Fin nf, (∏ j ∈ Finset.univ.erase i,
                  (stieltjesN (A + ouMat (UNModel.band sz) n s ω) (z j)).im) *
                  L1t d (sz.L n) (sz.W n) (sz.lam n) (A + ouMat (UNModel.band sz) n s ω) (z i)) +
                ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i,
                  (∏ k ∈ (Finset.univ.erase i).erase j,
                    (stieltjesN (A + ouMat (UNModel.band sz) n s ω) (z k)).im) *
                  L2t d (sz.L n) (sz.W n) (sz.lam n) (A + ouMat (UNModel.band sz) n s ω) (z i) (z j))
            ∂(ouP (UNModel.band sz) n) ≤ Bd) →
        |(∫ ω, ∏ i : Fin nf, (stieltjesN (A + ouMat (UNModel.band sz) n t ω) (z i)).im
              ∂(ouP (UNModel.band sz) n)) -
          ∫ ω, ∏ i : Fin nf, (stieltjesN (A + ouMat (UNModel.band sz) n T ω) (z i)).im
              ∂(ouP (UNModel.band sz) n)| ≤
          (1 / 2) * (T - t) * Bd

/-- **Proposal (target 3, E1 at a size sequence; not binding)**: the weighted `(EMCTE2)` of the block Anderson kind at every
size sequence with `N → ∞` (the band `unEMCTE2_of_sizeTendsto`, `Universality/EMCTE2.lean:597`, read through
`ouMatC_ba_eq_band_add` and `ouP_ba_eq_band` at `sz.withLam 0`). -/
def T2476_unEMCTE2k_ba : Prop :=
  ∀ (d : ℕ) (sz : Sizes d), sz.SizeTendsto → ∀ (E : ℝ) (nf : ℕ) (τU Cn : ℝ), τU ≤ Cn * τU →
    UNEMCTE2k (UNKind.ba d) sz E nf τU Cn

/-- **Proposal (E2, hypothesis of the K-forms; not binding)**: the bulk of a kind is open, uniformly in `n`.  Band:
`κ' = r = κ/2`.  Block Anderson: `κ' = κ/2`, `r = (πκ)³/8` (`BAbulk_window`, `BA/MReg.lean:122`). -/
def T2476_BulkWindowk (K : ∀ d, UNKind d) : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ : ℝ), 0 < κ → ∃ κ' r : ℝ, 0 < κ' ∧ 0 < r ∧
    ∀ (n : ℕ) (E e : ℝ), (K d).bulk sz κ E n → |e - E| ≤ r → (K d).bulk sz κ' e n

/-- **Proposal (E2, hypothesis of `unJak_of_ouClaimsk`; not binding)**: the bad-event transfer with two couplings, the QUE
window at `sz.lam n`, the profile `(K d).lamV sz n` in `blockM`, factor `2d + 1`.  Band: `measure_bad_le_of_queBadMat`
(`Universality/JakSpectral.lean:559`).  Block Anderson: `unBadY_of_blockM` and `unBadYBA_measure_le` (`BA/UNPins.lean:738`). -/
def T2476_BadBoundk (K : ∀ d, UNKind d) : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (t 𝔡 E : ℝ) (y : Idx d (sz.L n) (sz.W n)) (p : ℝ≥0∞),
    3 ≤ d → 0 < 𝔡 → (sz.W n : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n →
    (∀ b : Zd d (sz.L n), ouP ((K d).M sz).toUNModel n
        {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E b (ouMatC ((K d).M sz) n t ω)} ≤ p) →
    ouP ((K d).M sz).toUNModel n
        {ω | ∃ α, |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues α - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            (sz.W n : ℝ) ^ (-(𝔡 / 6)) ≤
              ‖blockM d (sz.L n) (sz.W n) ((K d).lamV sz n) (ouMatC_isHermitian ((K d).M sz) n t ω)
                (siteBlock d (sz.L n) (sz.W n) y) α‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p

/-- **Proposal (E2, hypothesis of `unUyw_of_ouClaimsk`; not binding)**: the pair form (`blockM2`).  Band:
`measure_bad2_le_of_queBadMat` (`Universality/UywKernel.lean:1061`).  Block Anderson: the new one-block pair statement at
`lamV = 0` (ticket target 9). -/
def T2476_Bad2Boundk (K : ∀ d, UNKind d) : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (t 𝔡 E : ℝ) (a0 : Zd d (sz.L n)) (p : ℝ≥0∞),
    3 ≤ d → 0 < 𝔡 → (sz.W n : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n →
    (∀ b : Zd d (sz.L n), ouP ((K d).M sz).toUNModel n
        {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E b (ouMatC ((K d).M sz) n t ω)} ≤ p) →
    ouP ((K d).M sz).toUNModel n
        {ω | ∃ α β, |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues α - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            |(ouMatC_isHermitian ((K d).M sz) n t ω).eigenvalues β - E| ≤
              (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)⁻¹ * (sz.W n : ℝ) ^ (𝔡 / 3) ∧
            (sz.W n : ℝ) ^ (-(𝔡 / 6)) ≤
              ‖blockM2 d (sz.L n) (sz.W n) ((K d).lamV sz n) (ouMatC_isHermitian ((K d).M sz) n t ω) a0 α β‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p

-- Shape (target 6, `unJak_of_ouClaimsk`, proposal): the band `unJak_of_ouClaims` (`Jak.lean:854`) over a kind; the bulk is
-- the row's eventual form; `C = 3 nf + 16`, `c' = 𝔠𝔡/30` as in the band.
example : Prop := ∀ K : ∀ d, UNKind d, T2476_BulkWindowk K → T2476_BadBoundk K →
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUEk (K d) sz 𝔡 τU → UNOUDiagk (K d) sz τU →
        UNJakk (K d) sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30)

-- Shape (target 6, `unUyw_of_ouClaimsk`, proposal): the band `unUyw_of_ouClaims` (`Uyw.lean:793`) over a kind.
example : Prop := ∀ K : ∀ d, UNKind d, T2476_BulkWindowk K → T2476_Bad2Boundk K →
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUEk (K d) sz 𝔡 τU → UNOUDiagk (K d) sz τU →
        UNUywk (K d) sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30)

-- Shape (target 6, `jakUywRowk`, proposal): the generic row under the three hypotheses, for every `Loc`.
example : Prop := ∀ K : ∀ d, UNKind d, T2476_BulkWindowk K → T2476_BadBoundk K → T2476_Bad2Boundk K →
  ∀ Loc : Prop, UNJakUywRowk K Loc

-- Shapes (targets 6 and 7-9): the three hypotheses at the band kind and at the block Anderson kind.
example : Prop := T2476_BulkWindowk (fun d => UNKind.band d) ∧ T2476_BadBoundk (fun d => UNKind.band d) ∧
  T2476_Bad2Boundk (fun d => UNKind.band d)

example : Prop := T2476_BulkWindowk (fun d => UNKind.ba d) ∧ T2476_BadBoundk (fun d => UNKind.ba d) ∧
  T2476_Bad2Boundk (fun d => UNKind.ba d)

-- Shape (E1 at the band, consistency of the transfer at `λ = 0`): the BA pin equals the band pin of `sz.withLam 0` when
-- `sz.lam = 0` (`UNEMCTE2k_ba_zero`, `BA/UNPins.lean:555`).
example : Prop := ∀ (d : ℕ) (sz : Sizes d), (∀ n, sz.lam n = 0) → ∀ (E : ℝ) (nf : ℕ) (τU Cn : ℝ),
  UNEMCTE2k (UNKind.ba d) sz E nf τU Cn ↔ UNEMCTE2k (UNKind.band d) (sz.withLam 0) E nf τU Cn

end RBM.Univ

end

/-! ## Part 3: the band declarations kept verbatim (GMN-C2 (b), G1) and the terminal invariants (GMN-C2 (c)) -/

-- `Jak` (read outside the file: `un_cd_le_half`, `unJak_of_ouClaims`, `jakRow`)
#check @RBM.Univ.un_cd_le_half
#check @RBM.Univ.unJak_of_ouClaims
#check @RBM.Univ.jakRow
-- `Uyw` (read outside the file: `jakUywRow`; readers `UnivMain`, `Main/BUniv`)
#check @RBM.Univ.unUyw_of_ouClaims
#check @RBM.Univ.uywRow
#check @RBM.Univ.jakUywRow
-- `JakSpectral` (readers `JakKernel`, `UywKernel`, `Jak`, `Uyw`)
#check @RBM.Univ.spectralPole
#check @RBM.Univ.spectralGsigPole
#check @RBM.Univ.isOrthoEigenbasis_eigenvectorBasis
#check @RBM.Univ.Gres_sq_apply_self
#check @RBM.Univ.Gres_apply_self_spectral
#check @RBM.Univ.Gres_sq_apply_self_spectral
#check @RBM.Univ.spectralGsigPole_norm_eq_spectralPole
#check @RBM.Univ.blockM_eq_unMy
#check @RBM.Univ.blockM_eq
#check @RBM.Univ.green_spectral_identity_blockM
#check @RBM.Univ.norm_green_spectral_identity_blockM_le
#check @RBM.Univ.sum_norm_blockM_le
-- the band pins these produce (`Universality/Pins.lean`)
#check @RBM.Univ.UNJak
#check @RBM.Univ.UNUyw
#check @RBM.Univ.UNEMCTE2
#check @RBM.Univ.UNJakUywRow
#check @RBM.Univ.UNEMCTE2Row
#check @RBM.Univ.UNOUQUE
#check @RBM.Univ.UNOUDiag
#check @RBM.Univ.UNOUClaims
#check @RBM.Univ.UNLocAvgBand
-- the terminal invariants: `#print axioms` of both, on `main` and on the branch, must agree
#check @RBM.Endpoints.band_terminal
#check @RBM.Endpoints.bUniv_holds
