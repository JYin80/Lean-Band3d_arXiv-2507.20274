/-
T2277 check file (BA-S3, dispatcher V1, Tue Oct  6 09:00 UTC 2026).  Statements of the proof targets of
`RBM3D/BA/Step1Fam.lean` (the `BAStep1` family assembly: probe `t/T2205:RBM3D/Probe/T2205Pins.lean` 3.1, 3.3,
4.1-4.3, 5.1, 5.3 and 7.1 at 96e4087, with the event form `BAConArg''` / `BABootstrap'` of DECISIONS §81 and the
ConArg time range of §86).  Defs, `#check`s and Prop-valued statement defs only: no proofs.  Compiles on `main`
(ed29a8b) as is.
-/
import RBM3D.BA.Step1

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 0. Merged names used (each `#check` with its full namespace) -/

-- BA-S2b2b (T2269, `BA/Step1.lean`)
#check @RBM.BA.baBootstrap'_holds
#check @RBM.BA.Step1Inst.inst_hcon_full
#check @RBM.BA.Step1Inst.inst_baBootstrap'
-- BA-S2b2a (T2262, `BA/Step1Setup.lean`)
#check @RBM.BA.Step1SetupInst.sI
#check @RBM.BA.Step1SetupInst.tI
-- BA-S2b1 (T2256, `BA/Step1Boot.lean`)
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.BAGbEXPij
#check @RBM.BA.BAFlowMember
#check @RBM.BA.BABootstrap'
#check @RBM.BA.BAFamZ_mono
#check @RBM.BA.BAFamZ_horizon
#check @RBM.BA.PrecL_congr
#check @RBM.BA.Step1BootInst.inst_hcon
-- BA-S1 (T2237, `BA/ConArg.lean`)
#check @RBM.BA.FlowFM.omegaC
#check @RBM.BA.BAConArgLoop''
#check @RBM.BA.BAConArg''
#check @RBM.BA.baConArg''_holds
-- BA-S2a (T2238, `BA/Step1Trivial.lean`)
#check @RBM.BA.BAFamZ
#check @RBM.BA.BAflow_T0_bounds
#check @RBM.BA.BAFamZ_main
#check @RBM.BA.BAFamZ_lam0_window
#check @RBM.BA.BAFamZ_im_m_ge
#check @RBM.BA.BATrivialLmax
#check @RBM.BA.BATrivialLmax_holds
-- BA-D8 (T2227, `BA/CouplingWindow.lean`)
#check @RBM.BA.BAzztE_inv_core
#check @RBM.BA.BAself_im_le_one
#check @RBM.BA.BAwindow_floor
#check @RBM.BA.BAWinBulk
-- BA-D1a/D2 (T2189, `BA/MFixedPoint.lean`)
#check @RBM.BA.BAt0
#check @RBM.BA.BAflowE
#check @RBM.BA.BAt0_pos
#check @RBM.BA.BASelf_subord
#check @RBM.BA.BAm
#check @RBM.BA.BAm_spec
#check @RBM.BA.BAdom_real
#check @RBM.BA.BAg0_le
#check @RBM.BA.BAm_self
#check @RBM.BA.MFixedPointInst.wI
#check @RBM.BA.MFixedPointInst.one_lt_wI
#check @RBM.BA.MFixedPointInst.wI_norm
#check @RBM.BA.MFixedPointInst.mS
#check @RBM.BA.MFixedPointInst.zS
#check @RBM.BA.MFixedPointInst.zS_im_pos
-- BA-C1a (T2197, `BA/FlowPins.lean`)
#check @RBM.BA.BAmF
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.STLKgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STDecayStronggL
#check @RBM.BA.STLocalMaxgL
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STExp2gL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.baFM
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
#check @RBM.BA.BAlamS
#check @RBM.BA.BAConArgVec
#check @RBM.BA.FlowPinsInst.sz0_lam_L
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.sz0_lam_pos
#check @RBM.BA.FlowPinsInst.BAm_zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
-- generic (StochDomAt, Sizes, band instances)
#check @RBM.StochDomAt
#check @RBM.StochDomAt.add
#check @RBM.StochDomAt.of_le_left
#check @RBM.StochDomAt.trans
#check @RBM.StochDomAt.of_eventually_empty
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.conStInd_inst
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const

noncomputable section

namespace RBM.BA.T2277Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 1. Vocabulary (bodies verbatim from the probe; targets use the same names in `RBM.BA`) -/

/-- `τ'' = t₀(z') s/u`, the horizon of the ConArg source of the member `z'` (probe `:1395`). -/
def BAtauS {d : ℕ} (sz : Sizes d) (z' : ℕ → ℂ) (s u : ℕ → ℝ) (n : ℕ) : ℝ := BAflowT0 sz z' n * (s n / u n)

/-- The ConArg source member (probe `:1399`). -/
def BAzSrc {d : ℕ} (sz : Sizes d) (z' : ℕ → ℂ) (s u : ℕ → ℝ) : ℕ → ℂ := fun n =>
  ztOf (BAm d (sz.L n) (Real.sqrt (BAtauS sz z' s u n) * sz.lam n) (BAflowEs sz z' n : ℂ)) (BAflowEs sz z' n)
      (BAtauS sz z' s u n) / (Real.sqrt (BAtauS sz z' s u n) : ℂ)

/-- `c_κ = √min(κ/(κ+1), 1/2)` (probe `:1897`). -/
def cκ (κ : ℝ) : ℝ := Real.sqrt (min (κ / (κ + 1)) (1 / 2))

/-! ## 2. The pins (new; registry: none, both are proved in this ticket, §90 for `BAStep1`) -/

/-- `(eq:loopbound_s)` from `(Eq:L-KGt)` and `ML:Kbound` for any carrier (probe `:1789`, verbatim). -/
def BALmaxFromLK (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (C : FlowFM sz) (τ : ℕ → ℝ), sz.SizeTendsto → (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) →
    (∀ᶠ n in atTop, sz.Bctl n (τ n) ≤ 1) → STKboundgL C (Sizes.seqP (sz.withLam 0)) →
      STLKgL C (Sizes.seqP (sz.withLam 0)) τ → STLmaxgL C (Sizes.seqP (sz.withLam 0)) τ

/-- **Step 1 of `lem:main_ind_BA`, family form** (probe `:1695`, verbatim). -/
def BAStep1 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
            (∀ n, t n ≤ BAflowT0 sz z n) →
            (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' →
              STKboundgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) ∧
                STLKgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s ∧
                STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s) →
            STConStInd sz 𝔠d s t →
              ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
                STStep1LoopgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t ∧
                  STStep1WeakgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t

/-! ## 3. Statements of the targets (names without `_stmt`) -/

/-- Target 2 (probe `:1420`, **generalized** for the §86 range): `hu : u n ≤ max t₀(z) (s n)` replaces
`u n ≤ t₀(z)`, `0 < t₀(z)` is added, the first conclusion is `min t₀(z) (s n) ≤ τ''` instead of `s n ≤ τ''`. -/
def BAzSrc_spec_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z z' : ℕ → ℂ) (c₁ κ : ℝ), 0 < κ → 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
    ∀ (s u : ℕ → ℝ) (n : ℕ), 0 ≤ sz.lam n → 0 < BAflowT0 sz z n → BAflowT0 sz z n < 1 →
      1 - c₁ ≤ s n → s n ≤ u n → u n ≤ max (BAflowT0 sz z n) (s n) →
      BAflowEs sz z' n = BAflowEs sz z n →
      min (BAflowT0 sz z n) (max (u n) (1 - c₁)) ≤ BAflowT0 sz z' n → BAflowT0 sz z' n ≤ BAflowT0 sz z n →
        min (BAflowT0 sz z n) (s n) ≤ BAtauS sz z' s u n ∧ BAtauS sz z' s u n ≤ BAflowT0 sz z n ∧
          κ ≤ (BAm d (sz.L n) (BAlamS sz z' s u n) (BAflowEs sz z' n : ℂ)).im ∧
          BAflowT0 sz (BAzSrc sz z' s u) n = BAtauS sz z' s u n ∧
          BAflowEs sz (BAzSrc sz z' s u) n = BAflowEs sz z' n ∧
          BAflowLam0 sz (BAzSrc sz z' s u) n = BAlamS sz z' s u n

/-- Target 3 (probe `:1478`, generalized as target 2). -/
def BAFamZ_closed_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ), 0 < κ → 0 < c₁ → c₁ ≤ 1 / 2 → (∀ n, 0 ≤ sz.lam n) →
    BAWinBulk sz z c₁ κ → (∀ n, 0 < BAflowT0 sz z n) → (∀ n, BAflowT0 sz z n < 1) →
      ∀ s u : ℕ → ℝ, (∀ n, 1 - c₁ ≤ s n) → (∀ n, s n ≤ u n) → (∀ n, u n ≤ max (BAflowT0 sz z n) (s n)) →
        ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ u z' → BAFamZ sz z c₁ s (BAzSrc sz z' s u)

/-- Target 4 (new): `Fam(t) ⊆ Fam(u)` as soon as `max(u, 1 - c₁) ≤ max(t, 1 - c₁)`. -/
def BAFamZ_mono_max_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u t : ℕ → ℝ) (z' : ℕ → ℂ),
    (∀ n, max (u n) (1 - c₁) ≤ max (t n) (1 - c₁)) → BAFamZ sz z c₁ t z' → BAFamZ sz z c₁ u z'

/-- Target 7 (new; the event-form analogue of the probe's `BAConArgLoop_congr` `:1630`). -/
def BAConArgLoop''_congr_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z₁ z₂ : ℕ → ℂ), (∀ᶠ n in atTop, z₁ n = z₂ n) →
    ∀ (s t : ℕ → ℝ) (k : ℕ) (C₀ : ℝ), (BAConArgLoop'' sz z₁ s t k C₀ ↔ BAConArgLoop'' sz z₂ s t k C₀)

/-- Target 6 (probe `:1643`). -/
def BAConArgVec_congr_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z₁ z₂ : ℕ → ℂ), (∀ᶠ n in atTop, z₁ n = z₂ n) →
    ∀ s t : ℕ → ℝ, (BAConArgVec sz z₁ s t ↔ BAConArgVec sz z₂ s t)

/-- Target 6 (probe `:1668`). -/
def STLmaxgL_max_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s : ℕ → ℝ) (c : ℝ),
    STLmaxgL C μ s → STLmaxgL C μ (fun _ => c) → STLmaxgL C μ (fun n => max (s n) c)

/-- Target 9 (`BAStep1_of_parts'`, DECISIONS §81 (1): the probe's `BAStep1_of_parts` `:1830` in event form). -/
def BAStep1_of_parts'_stmt (d : ℕ) : Prop :=
  BAFlowMember d → BALmaxFromLK d → BATrivialLmax d → BAConArg'' d → BABootstrap' d → BAStep1 d

/-- Target 10 (conditional proof, DECISIONS §90: the open content is carried by the owed `BAGbEXPii/ij`). -/
def baStep1_holds_stmt (d : ℕ) : Prop := BAGbEXPii d → BAGbEXPij d → BAStep1 d

/-! ## 4. Instance statements (namespace of the targets: `RBM.BA.Step1FamInst`) -/

section Inst

open RBM.BA.MFixedPointInst RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.Step1SetupInst
  RBM.Gauss.InductionDefsInst

/-- `mS_im_ge` (probe `:3348`). -/
def mS_im_ge_stmt : Prop :=
  ∀ (L : ℕ) [NeZero L] (g : ℝ), g ^ 2 * (L ^ 3 : ℕ) ≤ 1 / 64 → 41 / 50 ≤ (mS L g).im

/-- `t₀_n ≥ 17/25` along `sz0` (probe `t0_sz0` `:3434`; merged `t0_sz0` has `2/3`). -/
def t0_sz0_ge_stmt : Prop := ∀ n : ℕ, (17 / 25 : ℝ) ≤ BAflowT0 sz0 zSeq n

/-- `sz0_win` (probe `:3464`) at `κ = 1/2` (the probe had `1/10`; the floor is `3/5`). -/
def sz0_win_stmt : Prop :=
  ∀ c₁ ρ : ℝ, 1 - Real.sqrt (1 - c₁) ≤ ρ → ρ ≤ 3 / 10 → BAWinBulk sz0 zSeq c₁ (1 / 2)

/-- The `s < t` instance of `BAConArg''` with every premise discharged (§72 (2); probe `sz0_conArg_bulk` `:3507`). -/
def inst_conArg_lt_stmt : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ →
    (∀ k : ℕ, 2 ≤ k → BAConArgLoop'' sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25) k C₀) ∧
      BAConArgVec sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)

/-- `BALmaxFromLK_holds` at `sz0` (§72 (2), T2205 audit O1). -/
def inst_BALmaxFromLK_stmt : Prop :=
  STKboundgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) →
    STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI →
      STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI

/-- `baStep1_holds` at `sz0`, `(s, t) = (1/2, 2/3)`. -/
def inst_baStep1_stmt : Prop :=
  BAGbEXPii 3 → BAGbEXPij 3 →
    (∀ z' : ℕ → ℂ, BAFamZ sz0 zSeq (1 / 3) sI z' →
      STKboundgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) ∧
        STLKgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sI ∧
        STLocalMaxgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sI) →
    STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧
      STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI

/-- `baStep1_holds` at `sz0`, `(s, t) = (0, 1/16)` (probe `inst_BAStep1` `:3532`: `t < 1 - c₁`, so the ConArg range of
`BABootstrap'` is `{u ≡ 2/3}`, above `t`: the §86 case). -/
def inst_baStep1_low_stmt : Prop :=
  BAGbEXPii 3 → BAGbEXPij 3 →
    (∀ z' : ℕ → ℂ, BAFamZ sz0 zSeq (1 / 3) sInst z' →
      STKboundgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) ∧
        STLKgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sInst ∧
        STLocalMaxgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sInst) →
    STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sInst tInst ∧
      STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sInst tInst

end Inst

end RBM.BA.T2277Check

end
