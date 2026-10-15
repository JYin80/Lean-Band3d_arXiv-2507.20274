/-
Release check for T2518 (dispatcher V4, 2026-10-15; DECISIONS §336 (2) MNO-C3, §337 T2514 decision (3), §340 (2), (4);
supervisor 2026-10-15-0643 Q4 (a), (c), MNO-C1, MNO-C3, MNO-C4, closing (i), (vi)-(vii); design `docs/reports/T2449-design.md`
§2 `:61-62`, §5 `:139`; MN-D3 `docs/reports/T2513-design.md` §5 (D5; probe `t/T2513` `:218`, `:235-239`); not compiled by the
dispatcher).  M/N M3 (`BA/MADecolQUE`): decol and QUE at BA per `d`, the `d = 3` forms, the per-`d` reading `UNQueBAAt` and the
per-`d` core of the `UNQueBA` bridge (MNO-C3).
Part 1: merged names (`main` 89947ef7; `file:line` relative to `RBM3D/`).
Part 2: pins `T2518_*` (binding).  The MN1 texts are read by name from the merged `BA/MAPins` (3a67e18d, X1-C4).  Unmerged
inputs, in prose only: M2 = T2516 `baEnd_QDiffL`, `baEnd_QDiffL_three` (`T2516-check:144`, `:146`: `T2516_EndOfML`,
`T2516_EndThree`); C3 row a = T2515 `baThetaDiff` in `BA/GUEKPrim` (`T2515-check:166`: `T2515_ThetaDiffBA`, DELIVERED at the
1a-audit, §340 (4)).  Binder style of Part 2 copied from merged statements (`UNQuek` PinsK:398, `queFixed` QUEFromQDiff:285,
`queRowDiff` :244, `BAEnd_QDiffL` MAPins:107): `NeZero (sz.L n)`, `NeZero (sz.W n)` are the global instances
`Sizes.neZeroL`, `neZeroW` (`Defs/Sizes:152-153`), so no instance binder is added.
Statements only; no proofs.  Run: lake env lean docs/tickets/checks/T2518-check.lean
-/
import RBM3D.BA.MALocal
import RBM3D.Main.QUEFromQDiff
import RBM3D.Main.BandTerminal
import RBM3D.Universality.QUEFlow

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 1: merged names -/
-- the MN1 pins M3 concludes or reads (published once by T2514 row a in `BA/MAPins`; X1-C4)
#check @RBM.BA.BAEnd_decolL                       -- BA/MAPins:121 (owner BA-M3)
#check @RBM.BA.BAMADecol                          -- MAPins:161 (`BAEnd_locSCL d → BAEnd_decolL d`)
#check @RBM.BA.BAMAQUE                            -- MAPins:164 (`BAEnd_QDiffL d → BAEnd_QUEL d`)
#check @RBM.BA.BAdecolBad                         -- MAPins:86 (ρ-bulk eigenvalue)
#check @RBM.BA.BAEnd_locSCL                       -- MAPins:97
#check @RBM.BA.BAEnd_QDiffL                       -- MAPins:107 (concluded by M2)
#check @RBM.BA.BAendDom                           -- MAPins:65
#check @RBM.BA.BAlocBad1z                         -- MAPins:69
#check @RBM.BA.BAGz                               -- MAPins:51
#check @RBM.BA.BAMz                               -- MAPins:55
#check @RBM.BA.BAprof                             -- MAPins:59
#check @RBM.BA.BAThm27L                           -- MAPins:126 (N2; reads `baEnd_decolL_three`, `baEnd_QUEL_three`)
#check @RBM.BA.UNLocAvgBAAt                       -- MAPins:170 (template of `UNQueBAAt`)
#check @RBM.BA.UNLocAvgBA_iff_at                  -- MAPins:196 (template of `UNQueBA_iff_at`)
-- M1 row a (3a67e18d) and V
#check @RBM.BA.baEnd_locSCL                       -- BA/MALocal:834
#check @RBM.BA.baEnd_locSCL_three                 -- MALocal:839
#check @RBM.BA.unLocAvgBAAt_of_locSCL             -- MALocal:843 (template of the core, target 9)
#check @RBM.BA.UNLocAvgBA_of_BAEnd_locSCL         -- MALocal:854 (template of the one-line corollary)
#check @RBM.BA.unLocAvgBAAt_of_ML                 -- MALocal:858
#check @RBM.Univ.UNMLOutBA                        -- BA/UNPins:110
#check @RBM.BA.unMLOutBA_three                    -- BA/MainIndTermBA:47
#check @RBM.BA.baMainIndFamTL_any                 -- MainIndTermBA:53 (`d > 3` only under `STStep5IIIgL d`; closing (vii))
-- the QUE pin, the UN-side reading, the merged bridge
#check @RBM.BA.BAEnd_QUEL                         -- BA/UNPins:333 (registry `Test/Axioms:183`, owner BA-M3)
#check @RBM.BA.BAqueConclL                        -- UNPins:321
#check @RBM.Univ.UNQueBA                          -- UNPins:99
#check @RBM.Univ.UNQuek                           -- Universality/PinsK:398 (structural `Test/Axioms:388`)
#check @RBM.Univ.UNQueBA_of_BAEnd_QUEL            -- UNPins:357 (merged `∀ d` bridge; stays, MNO-C1)
#check @RBM.Univ.UNKind.ba                        -- UNPins:84
#check @RBM.Univ.UNModel.ba                       -- Universality/Pins:125 (`meas`: entrywise measurability of `seqHBA`)
#check @RBM.Univ.queBadMat                        -- Pins:392 (structural `Test/Axioms:313`)
#check @RBM.Univ.queBound                         -- Pins:384
#check @RBM.Univ.queWindow                        -- Pins:380
#check @RBM.Endpoints.que2BadMat                  -- Endpoints:154
#check @RBM.Univ.BAInst.inst_BAEnd_QUEL           -- UNPins:1225 (merged instance at `τ = 1/100`, bound ≥ 1)
-- decol inputs (targets 1-4)
#check @RBM.BA.BAMres_fine_apply                  -- BA/FlowPins:102 (`M_xy = 1(same offset) M^{(B)}_{[x][y]}`)
#check @RBM.BA.BAMB_diag_eq                       -- BA/Ward:89 (`M^{(B)}_aa = m`)
#check @RBM.BA.BAm_norm_le_one                    -- Ward:136
#check @RBM.BA.BAm_self                           -- BA/MFixedPoint:809
#check @RBM.BA.BAbulk                             -- MFixedPoint:429
#check @RBM.Endpoints.decol_scalars               -- Main/FixedZ:639 (`sz` only; reused verbatim)
#check @RBM.Endpoints.decol_spectral_core         -- FixedZ:733 (carrier-free; `ukx` :596)
#check @RBM.Endpoints.zdistInf_zero               -- FixedZ:633
#check @RBM.Endpoints.calB                        -- Endpoints:58
-- QUE inputs (targets 5-8)
#check @RBM.Endpoints.queDomain                   -- Main/QUEFromQDiff:91 (the `Im` half only, at `(κ, E) = (1, 0)`)
#check @RBM.Endpoints.etaQ                        -- QUEFromQDiff:85
#check @RBM.Endpoints.queChain                    -- QUEFromQDiff:463 (carrier-free exponent count)
#check @RBM.Endpoints.queMarkov                   -- Main/QUECore:1087
#check @RBM.Endpoints.normSq_le_trace             -- QUECore:422
#check @RBM.Endpoints.queObs                      -- QUECore:186 (`queImG` :176)
#check @RBM.Endpoints.avg2                        -- Endpoints:75
#check @RBM.Endpoints.qdBoundExp                  -- Endpoints:101
#check @RBM.Gauss.Sizes.seqHBA                    -- Gauss/BlockAnderson:96
#check @RBM.Gauss.Sizes.seqHBA_isHermitian        -- BlockAnderson:101
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP -- Gauss/FineModel:171
#check @RBM.Univ.g2bRowk                          -- Universality/QUEFlow:898; its private generic-carrier copies are reached by
--   `open private` (not `#check`able): `QUEFlow_queFixed` :815, `QUEFlow_core` :612, `QUEFlow_X` :542, `QUEFlow_obs_eq` :341,
--   `QUEFlow_obs_herm` :335, `QUEFlow_sub_of_normSq` :740, `QUEFlow_rpow_sub` :755; `queCore_quad_blk` Main/QUECore:933
#check @RBM.PropThetaQ                            -- Propagator/Pins:214 (the `Θ` of `BAprof`)
-- band twins
#check @RBM.Endpoints.decol_of_locSC              -- Main/FixedZ:789 (`MADecol` :787)
#check @RBM.Endpoints.decol_core                  -- FixedZ:750
#check @RBM.Endpoints.QUE_of_QDiff                -- Main/QUEFromQDiff:502 (`MAQUE` :234)
#check @RBM.Endpoints.queRowDiff                  -- QUEFromQDiff:244 (consumer form of `thetaDiff`)
#check @RBM.Endpoints.queFixed                    -- QUEFromQDiff:285
#check @RBM.Endpoints.que2Bad_sub                 -- Main/QUECore:1013 (carrier `seqXmat`; its generic copy is target 6)
#check @RBM.Endpoints.thetaDiff                   -- QUECore:105 (band; the BA one is C3's `baThetaDiff`)
#check @RBM.Endpoints.QUE_holds                   -- Main/BandTerminal:58
#check @RBM.Endpoints.decol_holds                 -- BandTerminal:61

/-! ## Part 2: pins (binding) -/

open MeasureTheory Filter Topology

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints

/-! ### P: the per-`d` reading of `UNQueBA` (new; M3's by T2514 decision (3); MNO-C3) -/

/-- **P1 `UNQueBAAt d`**: `UNQuek` (`Universality/PinsK.lean:398-403`) at `UNKind.ba d` after `∀ d, 3 ≤ d →`, cut as
`UNLocAvgBAAt` (`BA/MAPins:170`).  The only public `def` of `BA/MADecolQUE`. -/
def T2518_UNQueBAAt (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, (UNKind.ba d).bulk sz κ E n → ∀ a : Zd d (sz.L n),
        ((UNKind.ba d).M sz).μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (((UNKind.ba d).M sz).H n ω)} ≤
          queBound (sz.W n) 𝔡 ε₀ c τ

/-- **P2 `UNQueBA_iff_at`** (`Iff.rfl`; twin `UNLocAvgBA_iff_at`, `MAPins:196`). -/
def T2518_QueIffAt : Prop := UNQueBA ↔ ∀ d : ℕ, 3 ≤ d → T2518_UNQueBAAt d

/-! ### Decol (targets 1-4; twin `decol_of_locSC`, `FixedZ:789`) -/

/-- **1 `baMz_diag`**: on the fine lattice `M_xx = m(z)` (`BAMres_fine_apply` at the same offset, `BAMB_diag_eq` at `BAm_self`),
so `Im M_xx ≤ ‖m‖ ≤ 1` (`BAm_norm_le_one`): the band's `Mband x x = msc`, `‖msc‖ < 1`, with the same constant `C_M = 1`. -/
def T2518_MzDiag : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ x : Idx d (sz.L n) (sz.W n),
    BAMz sz n z x x = BAm d (sz.L n) (sz.lam n) z ∧ (BAMz sz n z x x).im ≤ 1

/-- **3 `baMADecol`** (private core 2 = twin `decol_core` `:750` on `¬ ∃ z, BAendDom ∧ BAlocBad1z` at
`(κ, min (τ/2) (1/2), min 𝔡 (d ε/2))`; `decol_scalars` verbatim; `decol_spectral_core` with `C_M = 1`). -/
def T2518_MADecolAll : Prop := ∀ d : ℕ, BAMADecol d
/-- **4 `baEnd_decolL`** (3 ∘ `baEnd_locSCL`). -/
def T2518_DecolOfML : Prop := ∀ d : ℕ, UNMLOutBA d → BAEnd_decolL d
/-- **4 `baEnd_decolL_three`** (3 at `baEnd_locSCL_three`; closing (i); N2 reads it for `BAThm27L 3`). -/
def T2518_DecolThree : Prop := BAEnd_decolL 3

/-! ### QUE (targets 5-8; twin `QUE_of_QDiff`, `QUEFromQDiff:502`) -/

/-- **5 (private, shape binding) the row differences of `BAprof`**: `baThetaDiff` (= `T2515_ThetaDiffBA`) at `σ = false, true`
by unfolding `BAprof` (`MAPins:59`); the consumer form of `queRowDiff` (`:244`).  `∃ C` before `sz` as in both (U5S-C3). -/
def T2518_RowDiff : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d (sz.L n) (sz.lam n) κ z.re → ∀ a b b' : Zd d (sz.L n),
        ‖BAprof sz n z true false a b - BAprof sz n z true false a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
        ‖BAprof sz n z true true a b - BAprof sz n z true true a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d

/-- **7 `baQueFixed`** (twin `queFixed`, `QUEFromQDiff:285`): QUE at one `(sz, n, E)`, `z = E + iη_Q`, law
`seqP (sz.withLam 0)`, matrix `sz.seqHBA`; first half `QUEFlow_queFixed` (`QUEFlow:815`) at `Hm = sz.seqHBA n`, second half
`QUEFlow_core` at `c = 1_A/|A|`, target 6 (generic `que2Bad_sub`), `queMarkov`. -/
def T2518_QueFixed : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E ε K : ℝ) (z : ℂ),
    z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I → 0 < etaQ sz n ε₀ →
    (∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0))) -
          BAprof sz n z true false a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => BAGz sz n z ω x y * BAGz sz n z ω y x) a b ∂(Sizes.seqP (sz.withLam 0))) -
          BAprof sz n z true true a b‖ ≤ ε) →
    (∀ a b b' : Zd d (sz.L n),
      ‖BAprof sz n z true false a b - BAprof sz n z true false a b'‖ ≤ K ∧
        ‖BAprof sz n z true true a b - BAprof sz n z true true a b'‖ ≤ K) →
    (∀ a : Zd d (sz.L n),
      Sizes.seqP (sz.withLam 0) {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqHBA n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) / ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) ∧
    (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      Sizes.seqP (sz.withLam 0) {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqHBA n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) / ((sz.W n : ℕ) : ℝ) ^ (-(2 * c))))

/-- **8 `baMAQUE`**: `BAEnd_QDiffL d` at `(κ, 𝔠(𝔡 - ε₀), τ/2, 1)`, its expectation half at `z = E + iη_Q ∈ BAendDom`, 5, 7,
`queChain` at the `C` of 5. -/
def T2518_MAQUEAll : Prop := ∀ d : ℕ, BAMAQUE d
/-- **8 `baEnd_QUEL`** (8 ∘ M2's `baEnd_QDiffL`). -/
def T2518_QUEOfML : Prop := ∀ d : ℕ, UNMLOutBA d → BAEnd_QUEL d
/-- **8 `baEnd_QUEL_three`** (8 at M2's `baEnd_QDiffL_three`; closing (i); concludes the registry head `BAEnd_QUEL`). -/
def T2518_QUEThree : Prop := BAEnd_QUEL 3

/-! ### The `UNQueBA` bridge through a per-`d` core (target 9; MNO-C3, T2513 D5 `T2513_que_core`) -/

/-- **9 `unQueBAAt_of_QUEL`**, the per-`d` core: the first half of `BAqueConclL` at one `d` (the merged bridge's
`.mono fun n hn E hE a => (hn E hE).1 a`, `UNPins:357-359`). -/
def T2518_QueCore : Prop := ∀ d : ℕ, 3 ≤ d → BAEnd_QUEL d → T2518_UNQueBAAt d
/-- **9 `unQueBAAt_of_ML`** (core ∘ `baEnd_QUEL`). -/
def T2518_QueAtOfML : Prop := ∀ d : ℕ, 3 ≤ d → UNMLOutBA d → T2518_UNQueBAAt d
/-- **9 `unQueBAAt_three`** (core at `baEnd_QUEL_three`): N2's `d = 3` input, no `∀ d` BA input (closing (vi)). -/
def T2518_QueAtThree : Prop := T2518_UNQueBAAt 3
/-- **9, the merged `∀ d` text** (= the statement of `UNQueBA_of_BAEnd_QUEL`, `UNPins:357`) as one line from the core and P2:
`example (h : ∀ d, BAEnd_QUEL d) : UNQueBA := UNQueBA_iff_at.2 fun d hd => unQueBAAt_of_QUEL d hd (h d)`. -/
def T2518_QueBridge : Prop := (∀ d : ℕ, BAEnd_QUEL d) → UNQueBA

end RBM.BA

end
