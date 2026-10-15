/-
Release check for T2512 (dispatcher V4, 2026-10-15; DECISIONS §334; DECISIONS §314 (1) Q4, §316, §317 (1)/(3), §318 (T2504
decisions (1)-(3), (8)), §320 (2), §332 (2); supervisor 0342 Q1 `:49-51`, Q2 `:53`; design `docs/reports/T2503-design.md:132`
(V2b row) and `:108`; not compiled by the dispatcher).  V V2b: the regime glue of `lem:main_ind_BA` in family form with TL2,
new BA leaf `BA/MainIndGlue`.  Every target concludes the merged def `BAMainIndFamTL d R` (`BA/MainIndOutBA.lean:60`, T2504 =
T2503's binding text), which this ticket does not restate.  The regime inputs are hypotheses of that merged type, so no
unmerged name is read: T2511 (V2a) and T2510 (V1-BA) names appear in the ticket prose only.
Model: the merged band glue `ST_mainInd_of_regimes` (`Induction/MainIndRegimes.lean:616`, T2245) with its public pattern
machinery; compiled BA pieces of the probe `t/T2205:RBM3D/Probe/T2205Pins.lean` (`BA_mainInd_compose` :2462, `BAFamZ_extend`
:3086, `BAMainIndR_of_cover` :3111, `BA_mainInd_of_regimes` :3293).
Part 1: merged names (`main` beefb80b), declaration lines from `grep` at drafting.  Part 2: pins `T2512_*`, binding unless
marked "shape" or "conditional".  Statements only.
Run: lake env lean docs/tickets/checks/T2512-check.lean
-/
import RBM3D.BA.MainIndOutBA
import RBM3D.Induction.MainIndRegimes

set_option linter.style.longLine false

/-! ## Part 1: merged names (`main` beefb80b) -/
-- V3 (T2504, 364e0d1e): the family step and the terminal plug-ins
#check @RBM.BA.BAMainIndFamTL                     -- BA/MainIndOutBA:60
#check @RBM.BA.baConclShift                       -- MainIndOutBA:155 (model of the back transport; private `MainIndOutBA_precL_shift` :145)
#check @RBM.BA.baMLOutTL_of_famStep               -- MainIndOutBA:315 (target 7 only)
#check @RBM.BA.unMLOutBA_of_famStep               -- MainIndOutBA:326 (target 7 only)
-- private instance data read by `open private` (not checkable here): `MainIndOutBA_flow` :343, `MainIndOutBA_win` :346, `MainIndOutBA_mem` :349
#check @RBM.BA.BATwistLoopLaw                     -- BA/TwistPins:95
#check @RBM.BA.BAMLOutTL                          -- TwistPins:178
#check @RBM.Univ.UNMLOutBA                        -- BA/UNPins:110
-- the BA tuple, the family, the window
#check @RBM.BA.BAFlow                             -- BA/FlowPins:389
#check @RBM.BA.BAflowT0                           -- FlowPins:380
#check @RBM.BA.BAflowEs                           -- FlowPins:383
#check @RBM.BA.baFMz                              -- FlowPins:393
#check @RBM.BA.BAWinBulk                          -- BA/CouplingWindow:799
#check @RBM.BA.BAFamZ                             -- BA/Step1Trivial:42
#check @RBM.BA.BAflow_T0_bounds                   -- Step1Trivial:47 (`T0 < 1`, so `t < 1`)
#check @RBM.BA.BAFamZ_main                        -- Step1Trivial:56 (off the range of a class: the main flow)
#check @RBM.BA.BAflowT0_congr                     -- BA/Step1Fam:74
#check @RBM.BA.BAflowEs_congr                     -- Step1Fam:77
#check @RBM.BA.BAzSrc                             -- Step1Fam:63 (instance member)
#check @RBM.BA.BAFamZ_mono_max                    -- Step1Fam:172
-- the seven carrier predicates (`Chain/Carrier`) and the cut-time reading
#check @RBM.BA.PrecL                              -- Chain/Carrier:51
#check @RBM.BA.STLKgL                             -- Carrier:80
#check @RBM.BA.STLmaxgL                           -- Carrier:87
#check @RBM.BA.STDecaygL                          -- Carrier:94
#check @RBM.BA.STDecayStronggL                    -- Carrier:105
#check @RBM.BA.STLocalMaxgL                       -- Carrier:115
#check @RBM.BA.STLocalEntrygL                     -- Carrier:121
#check @RBM.BA.STExp2gL                           -- Carrier:127
#check @RBM.BA.STLocalMaxgL_of_STLocalEntrygL     -- Induction/MainIndChain:126
#check @RBM.BA.STStep5IIIgL                       -- Chain/Step5Gen:228 (target 7's general-`d` form only)
-- regimes and the band glue (T2245, 05e50523)
#check @RBM.Gauss.Sizes.STAny                     -- Induction/Step34Pins:272
#check @RBM.Gauss.Sizes.STReg5I                   -- Induction/Step5Pins:44
#check @RBM.Gauss.Sizes.STReg5II                  -- Step5Pins:48
#check @RBM.Gauss.Sizes.STReg5III                 -- Step5Pins:58
#check @RBM.Gauss.Sizes.STReg5IV                  -- Step5Pins:63
#check @RBM.Gauss.Sizes.STRegSeq                  -- Induction/Step6Pins:482
#check @RBM.Gauss.Sizes.STConStInd                -- Induction/Defs:168
#check @RBM.Gauss.Sizes.st_conStInd_sub           -- Induction/ScaleFacts3:478
#check @RBM.Gauss.Sizes.st5_conStInd_mono         -- Induction/Step5Kit:101
#check @RBM.Gauss.Sizes.STMainIndR_mono           -- Induction/MainIndRegimes:105 (model of target 1)
#check @RBM.Gauss.Sizes.ST_mainIndR_seq           -- MainIndRegimes:289 (model of target 2; private `STMainIndRAt_seq` :266)
#check @RBM.Gauss.Sizes.STRegK                    -- MainIndRegimes:445
#check @RBM.Gauss.Sizes.STRegChain                -- MainIndRegimes:453
#check @RBM.Gauss.Sizes.STRegChain_succ           -- MainIndRegimes:460 (`Iff.rfl` with `STRegSeq`)
#check @RBM.Gauss.Sizes.STStage_le                -- MainIndRegimes:505
#check @RBM.Gauss.Sizes.STPattern                 -- MainIndRegimes:546
#check @RBM.Gauss.Sizes.STRegChain_of_class       -- MainIndRegimes:551 (model of target 3: private `STMainIndRAt_stage`/`_chain` :586, :598)
#check @RBM.Gauss.Sizes.ST_mainInd_of_regimes     -- MainIndRegimes:616 (model of target 4)
-- the subsequence layer (T2206 / ST-A, `Induction/SizesComp`)
#check @RBM.Gauss.Sizes.comp                      -- SizesComp:55
#check @RBM.Gauss.Sizes.comp_admissible           -- SizesComp:93
#check @RBM.Gauss.Sizes.STConStInd_comp           -- SizesComp:104
#check @RBM.Gauss.Sizes.reindex                   -- SizesComp:222
#check @RBM.Gauss.Sizes.seqP_withLam_reindex_preimage -- SizesComp:239
#check @RBM.Gauss.Sizes.integral_reindex          -- SizesComp:253 (the `STExp2gL` transport)
#check @RBM.nth_cover                             -- SizesComp:470
#check @RBM.Gauss.Sizes.stochDomAt_iff_comp_cover -- SizesComp:536 (all 13 transports, TL2 included)
-- Mathlib (replace the probe's `BAextend` and the band's private constant form)
#check @Function.Injective.extend_apply
#check @Function.extend_apply'
#check @Finset.inf'
-- instance data (d = 3)
#check @RBM.Gauss.SizesInst.sz0                   -- Defs/Sizes:260
#check @RBM.BA.FlowPinsInst.zSeq                  -- BA/FlowPins:1181
#check @RBM.BA.FlowPinsInst.flow_sz0              -- FlowPins:1214
#check @RBM.BA.FlowPinsInst.half_lt_t0            -- FlowPins:1254
#check @RBM.BA.Step1FamInst.sz0_win_third         -- BA/Step1Fam:802
#check @RBM.BA.Step1FamInst.inst_BAFamZ_closed    -- Step1Fam:820
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const -- Induction/Step1Setup:1226

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-! ## Part 2: pins -/

/-- **Target 1, `baMainIndFamTL_mono`** (twin of `STMainIndR_mono`, `MainIndRegimes:105`): a smaller regime. -/
def T2512_Mono (d : ℕ) : Prop :=
  ∀ R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop,
    (∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) → BAMainIndFamTL d R → BAMainIndFamTL d R'

/-- **Target 2, `baMainIndFamTL_seq`** (twin of `ST_mainIndR_seq`, `:289`; probe `BA_mainInd_compose` T2205:2462 with TL2):
the conclusions of stage 1 at the cut `m` for every member of `Fam(m)` are the hypotheses of stage 2. -/
def T2512_Seq (d : ℕ) : Prop :=
  ∀ R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop,
    BAMainIndFamTL d R₁ → BAMainIndFamTL d R₂ → BAMainIndFamTL d (STRegSeq R₁ R₂)

/-- **Target 3, `baMainIndFamTL_chain`** (twin of the private `STMainIndRAt_stage`/`_chain`, `:586-614`): every chain of stages. -/
def T2512_Chain (d : ℕ) : Prop :=
  BAMainIndFamTL d STReg5III → BAMainIndFamTL d STReg5I → BAMainIndFamTL d STReg5II → BAMainIndFamTL d STReg5IV →
    ∀ m i : ℕ, i + m ≤ 3 → BAMainIndFamTL d (STRegChain i m)

/-- **Target 4, `baMainIndFamTL_of_regimes`** (the main target; twin of `ST_mainInd_of_regimes`, `:616`; binder order of the
probe's `BA_mainInd_of_regimes` (iii), (i), (ii), (iv)).  All `d`; no `STStep5IIIgL` (it sits in the producer of the first premise). -/
def T2512_OfRegimes (d : ℕ) : Prop :=
  BAMainIndFamTL d STReg5III → BAMainIndFamTL d STReg5I → BAMainIndFamTL d STReg5II → BAMainIndFamTL d STReg5IV →
    BAMainIndFamTL d STAny

/-- **Target 5, private `MainIndGlue_extendMember`** (probe `BAFamZ_extend`, T2205:3086, with `Function.extend` for `BAextend`):
a member of the family along a subsequence, extended by the main flow, is a member of the family. -/
def T2512_ExtendMember (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ → ∀ z'' : ℕ → ℂ,
    BAFamZ (sz.comp φ) (fun j => z (φ j)) c₁ (fun j => u (φ j)) z'' → BAFamZ sz z c₁ u (Function.extend φ z'' z)

/-- Shape (not binding) of the private `MainIndGlue_down` (target 6 (a)): the six hypotheses at `τ` along every class of a
finite cover (`stochDomAt_iff_comp_cover`, `→`; five by `rfl`, `STExp2gL` by `integral_reindex`). -/
def T2512_DownShape (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    (let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
      STLKgL C μ τ ∧ STDecaygL C μ τ ∧ STDecayStronggL C μ τ ∧ STLocalMaxgL C μ τ ∧ STExp2gL C μ τ ∧ BATwistLoopLaw C μ τ) →
    ∀ k, let C := baFMz (sz.comp (φ k)) (fun j => z (φ k j)); let μ := Sizes.seqP ((sz.comp (φ k)).withLam 0)
      let τ' : ℕ → ℝ := fun j => τ (φ k j)
      STLKgL C μ τ' ∧ STDecaygL C μ τ' ∧ STDecayStronggL C μ τ' ∧ STLocalMaxgL C μ τ' ∧ STExp2gL C μ τ' ∧ BATwistLoopLaw C μ τ'

/-- Shape (not binding) of the private `MainIndGlue_up` (target 6 (b)): the seven conclusions along every class give them along
`sz` (`stochDomAt_iff_comp_cover`, `←`; the cover form of `baConclShift`). -/
def T2512_UpShape (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    (∀ k, let C := baFMz (sz.comp (φ k)) (fun j => z (φ k j)); let μ := Sizes.seqP ((sz.comp (φ k)).withLam 0)
      let τ' : ℕ → ℝ := fun j => τ (φ k j)
      STLKgL C μ τ' ∧ STLmaxgL C μ τ' ∧ STDecaygL C μ τ' ∧ STExp2gL C μ τ' ∧ STLocalEntrygL C μ τ' ∧ STDecayStronggL C μ τ' ∧
        BATwistLoopLaw C μ τ') →
    let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
    STLKgL C μ τ ∧ STLmaxgL C μ τ ∧ STDecaygL C μ τ ∧ STExp2gL C μ τ ∧ STLocalEntrygL C μ τ ∧ STDecayStronggL C μ τ ∧
      BATwistLoopLaw C μ τ

/-! ### Instances (`d = 3`, `sz0`, `zSeq`; data of `MainIndOutBA:343-351` by `open private`) -/

/-- Hypothesis-free: the regime-(iii) split of `[1/10, 1/2]` at `3/10` (`lam_n² ≤ 2⁻¹²`), the instance of target 2. -/
def T2512_InstSeqReg : Prop := STRegSeq STReg5III STReg5III sz0 (fun _ => 1 / 10) (fun _ => 1 / 2)

/-- Hypothesis-free: the stage pattern of `[1/10, 1/2]` along `sz0` is `(0, 0)` at every `n` (one class, regime (iii)). -/
def T2512_InstPattern : Prop := ∀ n, STPattern sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) n = (0, 0)

/-- Target 4 at `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2`, `(con_st_ind)` by
`s1Setup_conStInd_const`; hypotheses: the four regime steps and the six conjuncts on `Fam(1/10)`; output at the non-main member. -/
def T2512_InstOfRegimes : Prop :=
  BAMainIndFamTL 3 STReg5III → BAMainIndFamTL 3 STReg5I → BAMainIndFamTL 3 STReg5II → BAMainIndFamTL 3 STReg5IV →
    (∀ z' : ℕ → ℂ, BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' →
      let C := baFMz sz0 z'; let μ := Sizes.seqP (sz0.withLam 0); let s : ℕ → ℝ := fun _ => 1 / 10
      STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s) →
    let C := baFMz sz0 (BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)); let μ := Sizes.seqP (sz0.withLam 0)
    let t : ℕ → ℝ := fun _ => 1 / 2
    STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧
      BATwistLoopLaw C μ t

/-! ### Conditional (target 7: only if T2511 row b has merged at this row's start; else T2511 target 11) -/

/-- **Target 7** = the text of T2511 targets 11–12 (not written by T2512, V2O-C1): `baMainIndFamTL_three`, `baMLOutTL_three`, `unMLOutBA_three`
(names of T2504 decision (8)). -/
def T2512_Terminal : Prop := BAMainIndFamTL 3 STAny ∧ BAMLOutTL 3 ∧ Univ.UNMLOutBA 3

/-- Proposed with target 7 (0342 Q4 shape; dispatcher note (5)): the general-`d` step at `STAny` under `STStep5IIIgL d`. -/
def T2512_AnyD : Prop :=
  ∀ d : ℕ, STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STAny

end RBM.BA

end
