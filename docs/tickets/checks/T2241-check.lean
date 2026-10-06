/-
Release check for T2241 (dispatcher V1, Tue Oct  6 01:24 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §72, §69 B, §68, §66,
§57, §52, §45 O2, §29, §20, §17, §16).
BA-C1b (block Anderson, gate BA; the UN side of the portmap row BA-C1, split note `docs/tickets/T2197.md:28-30`):
`RBM3D/BA/UNPins.lean`, the UN-side block Anderson pins over the merged C″ form (`UNCoreC''`, `UNTrLocalInit'`,
`UNMeanBound`, `UNDens'`) and the merged T2197 carrier.
Section 1: the merged names the ticket uses (exact namespaces; file:line, last commit on `main` e5b944a).
Section 2: vocabulary and pin texts, in the temporary namespace `RBM.Univ.T2241Check`.  `UNModelC.ba` is not merged, so
every pin that mentions it is written over an abstract centred family `Mba : ∀ {d} (sz : Sizes d), UNModelC sz`; T2241
defines `UNModelC.ba` and the pins without the parameter, and the comparison instantiates `Mba := @UNModelC.ba`
(ticket, Acceptance).  `KBA Mba` is the class `UNKind.ba`.
Section 3: the statements of the public theorems of T2241 as `*_stmt : Prop`.
Section 4: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2241-check.lean`.
-/
import RBM3D.BA.FlowPins
import RBM3D.Universality.PinsC2
import RBM3D.Endpoints
import RBM3D.Defs.Neighbours
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open scoped NNReal ENNReal Kronecker

/-! ## 1. Merged names -/

-- T2174 (f8ad4b4): `RBM3D/Universality/Pins.lean`, namespace `RBM.Univ`
#check @RBM.Univ.IsOrthoEigenbasis      -- :53
#check @RBM.Univ.gueP                   -- :67
#check @RBM.Univ.kPoint                 -- :77
#check @RBM.Univ.rhoSC                  -- :84
#check @RBM.Univ.stieltjesN             -- :88
#check @RBM.Univ.IsTestFun              -- :92
#check @RBM.Univ.UNModel                -- :104
#check @RBM.Univ.UNModel.band           -- :116
#check @RBM.Univ.UNModel.ba             -- :125
#check @RBM.Univ.ouTStar                -- :142
#check @RBM.Univ.ouP                    -- :145
#check @RBM.Univ.ouMat                  -- :150
#check @RBM.Univ.UNUnivDilAt            -- :195
#check @RBM.Univ.UNL32                  -- :281
#check @RBM.Univ.Nsz                    -- :372
#check @RBM.Univ.queWindow              -- :380
#check @RBM.Univ.queBound               -- :384
#check @RBM.Univ.queBadMat              -- :392
#check @RBM.Univ.UNTrLocal              -- :447
#check @RBM.Univ.UNDens                 -- :462
#check @RBM.Univ.UNNormBound            -- :477
#check @RBM.Univ.UNGUELocal             -- :489
#check @RBM.Univ.InWindow               -- :501
#check @RBM.Univ.scirc                  -- :612
#check @RBM.Univ.L1t                    -- :617
#check @RBM.Univ.L2t                    -- :624
#check @RBM.Univ.un_window_sub          -- :908
#check @RBM.Univ.UNBadY                 -- :1147
#check @RBM.Univ.unBadY_subset          -- :1205
#check @RBM.Univ.unBadY_measure_le      -- :1320
#check @RBM.Univ.UNInst.bump            -- :1502
#check @RBM.Univ.UNInst.bump_testFun    -- :1504
#check @RBM.Univ.UNInst.bump_nondegenerate -- :1507
#check @RBM.Univ.UNInst.inst_que_exponent -- :1591
#check @RBM.Univ.UNInst.pow32           -- :1608
#check @RBM.Univ.UNInst.unMy_single_self -- :1701
#check @RBM.Univ.UNInst.isOrthoEigenbasis_zero -- :1713
-- T2187 (fdbb6f0): `RBM3D/Universality/PinsK.lean`, namespace `RBM.Univ`
#check @RBM.Univ.UNModelC               -- :55
#check @RBM.Univ.UNModel.toC            -- :61
#check @RBM.Univ.ouMatC                 -- :69
#check @RBM.Univ.ouInit                 -- :75
#check @RBM.Univ.ouMatC_isHermitian     -- :79
#check @RBM.Univ.ouInit_isHermitian     -- :89
#check @RBM.Univ.ouMatC_eq_ouInit_add   -- :93
#check @RBM.Univ.ouMatC_eq_ouMat_add    -- :100
#check @RBM.Univ.ouMatC_toC             -- :119
#check @RBM.Univ.ouInit_toC             -- :124
#check @RBM.Univ.UNClaimAllC            -- :158
#check @RBM.Univ.UNGreenCorrAllC        -- :204
#check @RBM.Univ.UNKind                 -- :307
#check @RBM.Univ.UNKind.band            -- :315
#check @RBM.Univ.UNOUQUEk               -- :326
#check @RBM.Univ.UNOUDiagk              -- :335
#check @RBM.Univ.UNEMCTE2k              -- :345
#check @RBM.Univ.UNJakk                 -- :365
#check @RBM.Univ.UNUywk                 -- :378
#check @RBM.Univ.UNQuek                 -- :398
#check @RBM.Univ.UNLocAvgk              -- :406
#check @RBM.Univ.UNOUClaimsk            -- :421
#check @RBM.Univ.UNOURowk               -- :426
#check @RBM.Univ.UNEMCTE2Rowk           -- :429
#check @RBM.Univ.UNJakUywRowk           -- :435
#check @RBM.Univ.UNClaimRowk            -- :442
#check @RBM.Univ.un_claimAll_of_rowsk   -- :454
#check @RBM.Univ.ouP_cylinder           -- :483
#check @RBM.Univ.UNOUQUEk_zero_of_UNQuek -- :494
#check @RBM.Univ.UNKInst.inWindow_nonempty -- :608
#check @RBM.Univ.UNKInst.inst_ouMatC_ne_ouMat -- :728
-- T2201 (3fc9d03): `RBM3D/Universality/PinsDens.lean`, namespace `RBM.Univ`
#check @RBM.Univ.UNDens'                -- :59
#check @RBM.Univ.UNDens'.toUNDens       -- :143
#check @RBM.Univ.unDens'_freeConvST     -- :200
-- T2213 (122f299): `RBM3D/Universality/PinsC2.lean`, namespace `RBM.Univ`
#check @RBM.Univ.UNTrLocalInit'         -- :72
#check @RBM.Univ.UNMeanBound            -- :82
#check @RBM.Univ.UNStep1GoodC''         -- :90
#check @RBM.Univ.UNCoreC''              -- :106
#check @RBM.Univ.un_eigenvalues_abs_le_convex -- :350
#check @RBM.Univ.unMeanBound_toC        -- :548
#check @RBM.Univ.step1GoodC''           -- :1469
#check @RBM.Univ.PinsC2Inst.inst_coreC_band'' -- :1613
-- T2210 (8a43715): `RBM3D/Endpoints.lean`, namespace `RBM.Endpoints`
#check @RBM.Endpoints.que2BadMat        -- :154
#check @RBM.Endpoints.QUE               -- :182
-- T2197 (b750bf3): `RBM3D/BA/FlowPins.lean`, namespace `RBM.BA`
#check @RBM.BA.STLKgL                   -- :357
#check @RBM.BA.STLmaxgL                 -- :364
#check @RBM.BA.STDecaygL                -- :371
#check @RBM.BA.STLocalEntrygL           -- :398
#check @RBM.BA.STExp2gL                 -- :404
#check @RBM.BA.BAflowT0                 -- :537
#check @RBM.BA.BAFlow                   -- :546
#check @RBM.BA.baFMz                    -- :550
-- T2197: namespace `RBM.BA.FlowPinsInst` (instance data)
#check @RBM.BA.FlowPinsInst.zSeq        -- :1333
#check @RBM.BA.FlowPinsInst.flow_sz0    -- :1366
#check @RBM.BA.FlowPinsInst.t0_sz0      -- :1379
-- T2189 (ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA`
#check @RBM.BA.BASelf                   -- :193
#check @RBM.BA.BAm                      -- :379
#check @RBM.BA.BArho                    -- :384
#check @RBM.BA.BAbulk                   -- :429
#check @RBM.BA.BAReal                   -- :432
#check @RBM.BA.BAbulk_iff               -- :448
#check @RBM.BA.BAmExists                -- :536
#check @RBM.BA.BAmUniqReal              -- :542
#check @RBM.BA.baMExists_holds          -- :795
#check @RBM.BA.baMUniqReal_holds        -- :803
-- T2189: namespace `RBM.BA.MFixedPointInst`
#check @RBM.BA.MFixedPointInst.FlowPt   -- :877
#check @RBM.BA.MFixedPointInst.exists_flowPt -- :885
-- T2013 (868b3b4): `RBM3D/Gauss/BlockAnderson.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.PsiB                  -- :45
#check @RBM.Gauss.PsiV                  -- :48
#check @RBM.Gauss.PsiI                  -- :52
#check @RBM.Gauss.PsiI_isHermitian      -- :65
#check @RBM.Gauss.Sizes.seqHBA          -- :96
#check @RBM.Gauss.Sizes.seqHBA_isHermitian -- :101
-- T2013 (868b3b4): `RBM3D/Loop/GLoopFlow.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.Gres                  -- :74
-- T2006 (0a873f1): `RBM3D/Defs/Sizes.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.split                 -- :64
#check @RBM.Gauss.Iblk                  -- :92
#check @RBM.Gauss.Sizes                 -- :138
#check @RBM.Gauss.Sizes.neZeroL         -- :152
#check @RBM.Gauss.Sizes.size            -- :157
#check @RBM.Gauss.Sizes.WO              -- :164
#check @RBM.Gauss.Sizes.SizeTendsto     -- :173
#check @RBM.Gauss.Sizes.Admissible      -- :177
#check @RBM.Gauss.Sizes.withLam         -- :182
#check @RBM.Gauss.Sizes.Bctl            -- :214
#check @RBM.Gauss.SizesInst.sz0         -- :260
-- T2006 (0a873f1): `RBM3D/Gauss/FineModel.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.Ω                     -- :84
#check @RBM.Gauss.Xmat                  -- :113
#check @RBM.Gauss.Xmat_isHermitian      -- :142
#check @RBM.Gauss.Sizes.SeqΩ            -- :160
#check @RBM.Gauss.Sizes.seqP            -- :169
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP -- :171
#check @RBM.Gauss.Sizes.seqXmat         -- :218
-- `RBM3D/Defs/Neighbours.lean` (be709a6), namespace `RBM`
#check @RBM.card_adj                    -- :168
-- `RBM3D/Propagator/Props4.lean` (892334b), namespace `RBM`
#check @RBM.SBR                         -- :48
-- `RBM3D/Defs/Lattice.lean` (51f1a17), namespace `RBM`
#check @RBM.Zd                          -- :63
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), namespace `RBM`
#check @RBM.msc                         -- :116
-- Mathlib (routes of `unMeanBound_ba`, `UNPins_normBound_mono`)
#check @Matrix.IsHermitian.mulVec_eigenvectorBasis   -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.IsHermitian.eigenvalues               -- Mathlib.Analysis.Matrix.Spectrum
#check @tendsto_rpow_atTop                           -- Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
#check @Real.rpow_le_rpow_of_exponent_le             -- Mathlib.Analysis.SpecialFunctions.Pow.Real
#check @MeasureTheory.measure_mono

/-! ## 2. Vocabulary and pin texts -/

namespace RBM.Univ.T2241Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.Univ

/-- The block Anderson class over a centred family `Mba` (T2173 `UNKind.ba`, `:2262-2266`, under S1, S6 of T2187):
T2241's `UNKind.ba d` is `KBA @UNModelC.ba d` (`rfl`). -/
noncomputable def KBA (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) (d : ℕ) : UNKind d where
  M := fun sz => Mba sz
  lamV := fun _ _ => 0
  bulk := fun sz κ E n => BAbulk d (sz.L n) (sz.lam n) κ E
  mdet := fun sz n => BAm d (sz.L n) (sz.lam n)

/-- What `UNModelC.ba` is (target 1): the merged `UNModel.ba` with the mean `λΨ`. -/
def UNModelCba_spec (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), (Mba sz).toUNModel = UNModel.ba sz ∧
    ∀ n : ℕ, (Mba sz).mean n = (sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n)

/-- `UNQueBA` (T2173 `:2405`). -/
def UNQueBA_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop := UNQuek (KBA Mba)

/-- `UNLocAvgBA` (T2173 `:2407`). -/
def UNLocAvgBA_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop := UNLocAvgk (KBA Mba)

/-- `UNMLOutBA` (T2173 `:2414-2419`, verbatim). -/
def UNMLOutBA_pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
        STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STExp2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
        STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t

/-- The four BA rows (T2173 `:2484-2492`). -/
def UNOURowBA_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  UNOURowk (KBA Mba) (∀ d : ℕ, UNMLOutBA_pin d) (UNLocAvgBA_pin Mba) (UNQueBA_pin Mba)

def UNEMCTE2RowBA_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop := UNEMCTE2Rowk (KBA Mba)

def UNJakUywRowBA_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  UNJakUywRowk (KBA Mba) (UNLocAvgBA_pin Mba)

def UNClaimRowBA_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop := UNClaimRowk (KBA Mba)

/-- `UNDensBARow'` (T2173 `UNDensBARow` `:2588-2596` with `UNDens ↦ UNDens'`, R1). -/
def UNDensBARow'_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        UNDens' (fun n => BAm d (sz.L n) (sz.lam n)) E (fun n => BArho d (sz.L n) (sz.lam n) E) δ ∧
          ∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x

/-- `UNTrLocalBARow` (T2173 `:2597-2604` under S4). -/
def UNTrLocalBARow_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  UNLocAvgBA_pin Mba → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocal sz (Mba sz).toUNModel (fun n => BAm d (sz.L n) (sz.lam n)) E δ

/-- `UNTrLocalInitBARow'` (T2173 `UNTrLocalInitBARow` `:2606-2613` with `UNTrLocalInit ↦ UNTrLocalInit'`, R2). -/
def UNTrLocalInitBARow'_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  UNLocAvgBA_pin Mba → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocalInit' sz (Mba sz) (fun n => BAm d (sz.L n) (sz.lam n)) E δ

/-- `UNNormBARow` (T2173 `:2614-2617` under S4). -/
def UNNormBARow_pin (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz (Mba sz).toUNModel CV₀

/-- `BAqueConclL` (T2173 `:3238-3247`, R4: merged `queBadMat`, `que2BadMat`, `queBound`); T2241 puts it in `RBM.BA`. -/
def BAqueConclL {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) (𝔡 κ ε₀ c τ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ E : ℝ, BAbulk d (sz.L n) (sz.lam n) κ E →
    (∀ a : Zd d (sz.L n),
      μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqHBA n ω)} ≤
        queBound (sz.W n) 𝔡 ε₀ c τ) ∧
    (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      μ {ω | RBM.Endpoints.que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqHBA n ω)} ≤
        queBound (sz.W n) 𝔡 ε₀ c τ)

/-- `BAEnd_QUEL` (T2173 `:3249-3253`); T2241 puts it in `RBM.BA`. -/
def BAEnd_QUEL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      BAqueConclL sz (Sizes.seqP (sz.withLam 0)) 𝔡 κ ε₀ c τ

/-- `BAEnd_BUnivL` (T2173 `:3230-3234`, in the merged dilated form `UNUnivDilAt`, R4); T2241 puts it in `RBM.BA`. -/
def BAEnd_BUnivL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ E' : ℝ, |E'| < 2 →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
        UNUnivDilAt sz (UNModel.ba sz) (fun n => BArho d (sz.L n) (sz.lam n) E) E E' k O

/-- `lamHat` (T2173 `:2702`, verbatim). -/
noncomputable def lamHat {d : ℕ} (sz : Sizes d) (s : ℕ → ℝ) : ℕ → ℝ := fun n => sz.lam n * Real.exp (s n / 2)

/-! ## 3. Statements of the public theorems -/

/-- `un_claimAll_of_rowsBA` (T2173 `:2496-2501` under S5). -/
def un_claimAll_of_rowsBA_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  UNClaimRowBA_pin Mba → UNEMCTE2RowBA_pin Mba → UNJakUywRowBA_pin Mba → UNOURowBA_pin Mba →
    (∀ d : ℕ, UNMLOutBA_pin d) → UNLocAvgBA_pin Mba → UNQueBA_pin Mba →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → UNClaimAllC sz (Mba sz) E

/-- `unMeanBound_ba` (new, R3). -/
def unMeanBound_ba_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ CV₀ : ℝ, 0 < CV₀ → UNMeanBound sz (Mba sz) CV₀

/-- `UNQueBA_of_BAEnd_QUEL` (T2173 `:3256`). -/
def UNQueBA_of_BAEnd_QUEL_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  (∀ d : ℕ, BAEnd_QUEL d) → UNQueBA_pin Mba

/-- `baBUniv_of_rows` (T2173 `:3283-3286`, R3: through `UNCoreC''`, `UNGreenCorrAllC`). -/
def baBUniv_of_rows_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  UNCoreC'' → UNL32 → UNGUELocal → UNGreenCorrAllC →
    UNDensBARow'_pin → UNTrLocalBARow_pin Mba → UNTrLocalInitBARow'_pin Mba → UNNormBARow_pin Mba →
    UNClaimRowBA_pin Mba → UNEMCTE2RowBA_pin Mba → UNJakUywRowBA_pin Mba → UNOURowBA_pin Mba →
    (∀ d : ℕ, UNMLOutBA_pin d) → UNLocAvgBA_pin Mba → UNQueBA_pin Mba → ∀ d : ℕ, BAEnd_BUnivL d

/-- `ouMatC_ba_eq_ouMat` (T2173 `ouMat_ba_eq_ouMatNC` `:2709-2710` under S1, S2). -/
def ouMatC_ba_eq_ouMat_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    ouMatC (Mba sz) n (s n) ω = ouMat (UNModel.ba (sz.withLam (lamHat sz s))) n (s n) ω

/-- `ouP_ba_withLam` (T2173 `:2738-2739` under S3). -/
def ouP_ba_withLam_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (g : ℕ → ℝ) (n : ℕ), ouP (Mba sz).toUNModel n = ouP (UNModel.ba (sz.withLam g)) n

/-- `ouP_ba_eq_band` (T2173 `:2768-2769` under S3). -/
def ouP_ba_eq_band_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), ouP (Mba sz).toUNModel n = ouP (UNModel.band (sz.withLam 0)) n

/-- `ouMatC_ba_eq_band_add` (T2173 `ouMat_ba_eq_band_add` `:2746-2749` under S1, S2). -/
def ouMatC_ba_eq_band_add_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    ouMatC (Mba sz) n t ω - ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) =
      ouMat (UNModel.band (sz.withLam 0)) n t ω

/-- `ouInit_ba` (T2173 `:2778-2779` under S1). -/
def ouInit_ba_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ sz),
    ouInit (Mba sz) n (s n) ω = Real.exp (-(s n) / 2) • (UNModel.ba (sz.withLam (lamHat sz s))).H n ω

/-- `admissible_lamHat` (T2173 `:2807-2808`, verbatim). -/
def admissible_lamHat_stmt : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ 1) →
    (sz.withLam (lamHat sz s)).Admissible 𝔠 (𝔡 / 2)

/-- `ba_zero_H` (T2173 `:2833-2834` under S1). -/
def ba_zero_H_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} {sz : Sizes d}, (∀ n, sz.lam n = 0) → ∀ (n : ℕ) (ω : Sizes.SeqΩ sz),
    (Mba sz).H n ω = (UNModel.band (sz.withLam 0)).H n ω

/-- `ba_zero_mean` (T2173 `:2838-2839` under S1, S6). -/
def ba_zero_mean_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} {sz : Sizes d}, (∀ n, sz.lam n = 0) → ∀ n : ℕ,
    (Mba sz).mean n = ((UNModel.band (sz.withLam 0)).toC).mean n

/-- `ouMatC_ba_zero` (T2173 `ouMat_ba_zero` `:2845-2846` under S1, S2, S6). -/
def ouMatC_ba_zero_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} {sz : Sizes d}, (∀ n, sz.lam n = 0) →
    ∀ (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
      ouMatC (Mba sz) n t ω = ouMatC (UNModel.band (sz.withLam 0)).toC n t ω

/-- `UNEMCTE2k_ba_zero`, `UNJakk_ba_zero`, `UNUywk_ba_zero` (T2173 `:2851-2873`). -/
def UNEMCTE2k_ba_zero_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} {sz : Sizes d}, (∀ n, sz.lam n = 0) → ∀ (E : ℝ) (nf : ℕ) (τU Cn : ℝ),
    UNEMCTE2k (KBA Mba d) sz E nf τU Cn ↔ UNEMCTE2k (UNKind.band d) (sz.withLam 0) E nf τU Cn

def UNJakk_ba_zero_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} {sz : Sizes d}, (∀ n, sz.lam n = 0) → ∀ (E : ℝ) (nf : ℕ) (τU C c' : ℝ),
    UNJakk (KBA Mba d) sz E nf τU C c' ↔ UNJakk (UNKind.band d) (sz.withLam 0) E nf τU C c'

def UNUywk_ba_zero_stmt (Mba : ∀ {d : ℕ} (sz : Sizes d), UNModelC sz) : Prop :=
  ∀ {d : ℕ} {sz : Sizes d}, (∀ n, sz.lam n = 0) → ∀ (E : ℝ) (nf : ℕ) (τU C c' : ℝ),
    UNUywk (KBA Mba d) sz E nf τU C c' ↔ UNUywk (UNKind.band d) (sz.withLam 0) E nf τU C c'

/-- `BASelf_msc` (T2173 `:2879`; T2241 puts it in `RBM.BA`). -/
def BASelf_msc_stmt : Prop :=
  ∀ (d L : ℕ) [NeZero L] {z : ℂ}, 0 < z.im → BASelf d L 0 z (msc z)

/-- `unBadY_subset'` (T2173 `:2964-2968`, verbatim). -/
def unBadY_subset'_stmt : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ {lamV lamQ 𝔡 E : ℝ}, 1 ≤ (W : ℝ) → 0 < 𝔡 →
    (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ → ∀ (y : Idx d L W) (M : Matrix (Idx d L W) (Idx d L W) ℂ),
      UNBadY d L W lamV 𝔡 E y M →
        ∃ b : Zd d L, SBR d L lamV b (split d L W y).1 ≠ 0 ∧ queBadMat d L W lamQ (𝔡 / 3) (𝔡 / 6) E b M

/-- `SBR_zero_ne` (T2173 `:3047`, verbatim). -/
def SBR_zero_ne_stmt : Prop :=
  ∀ {d L : ℕ} [NeZero L] {b a : Zd d L}, SBR d L 0 b a ≠ 0 → b = a

/-- `unBadYBA_subset` (T2173 `:3054-3057`, verbatim). -/
def unBadYBA_subset_stmt : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ {lamQ 𝔡 E : ℝ}, 1 ≤ (W : ℝ) → 0 < 𝔡 →
    (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ → ∀ (y : Idx d L W) (M : Matrix (Idx d L W) (Idx d L W) ℂ),
      UNBadY d L W 0 𝔡 E y M → queBadMat d L W lamQ (𝔡 / 3) (𝔡 / 6) E (split d L W y).1 M

/-- `unBadYBA_measure_le` (T2173 `:3063-3068`, verbatim). -/
def unBadYBA_measure_le_stmt : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {Ω' : Type} [MeasurableSpace Ω'] (μ : Measure Ω'), 3 ≤ L →
    ∀ {lamQ 𝔡 E : ℝ}, 1 ≤ (W : ℝ) → 0 < 𝔡 → (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ →
      ∀ (y : Idx d L W) (Mf : Ω' → Matrix (Idx d L W) (Idx d L W) ℂ) (p : ℝ≥0∞),
        (∀ b : Zd d L, μ {ω | queBadMat d L W lamQ (𝔡 / 3) (𝔡 / 6) E b (Mf ω)} ≤ p) →
          μ {ω | UNBadY d L W 0 𝔡 E y (Mf ω)} ≤ p

/-! ## 4. Prop-valued examples at merged data (no proof obligation) -/

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

example : Prop := UNMLOutBA_pin 3
example : Prop := BAEnd_QUEL 3
example : Prop := BAEnd_BUnivL 3
example : Prop := UNDensBARow'_pin
example : Prop := UNModelCba_spec (fun sz => (UNModel.band sz).toC)
example : Prop := UNEMCTE2k (KBA (fun sz => (UNModel.band sz).toC) 3) sz0 0 1 (1 / 100) 1
example : Prop := UNTrLocalInitBARow'_pin (fun sz => (UNModel.band sz).toC)
example : Prop :=
  BAqueConclL sz0 (Sizes.seqP (sz0.withLam 0)) (1 / 10) (1 / 2) (1 / 30) (1 / 60) (1 / 100)
example : Prop :=
  STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0)
example : Prop := UNMeanBound sz0 (UNModel.band sz0).toC (1 / 2)
example : Prop := (sz0.withLam (lamHat sz0 (ouTStar sz0 (1 / 100)))).Admissible (1 / 6) (1 / 20)
example : Prop := baBUniv_of_rows_stmt (fun sz => (UNModel.band sz).toC)

end RBM.Univ.T2241Check
