/-
Release check for T2245 (dispatcher V1, Tue Oct  6 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §45 O2,
§67, §68 (7) (9) (10), §73 (4), §76 (3)).
ST-5, the main-induction regime assembly (supervisor `docs/supervisor/2026-10-05-1806.md`, answers to REQ-2026-10-05-1746,
Q2 "Assembly" 1-2): `STMainIndR d R` (the shape of `STMainInd` with a regime `R`), `ST_mainIndR_of_steps` (generic and per
regime (iii), (i), (ii), (iv)), the stage chaining `ST_mainIndR_seq`, the seven predicate transfers along a finite
`StrictMono` cover, `ST_mainInd_of_regimes` (the ten stage patterns glued by route (A)), `ST_mainInd_of_pins`.
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` 25362ad) and of the two Mathlib lemmas
(their module imported explicitly).
Section 2: the vocabulary def `STMainIndR_voc` (the library defines `RBM.Gauss.Sizes.STMainIndR` with exactly this body).
Section 3: the pins (`def … _pin : Prop`), one per pinned public theorem of the new file; each theorem's type is the pin body
with `STMainIndR_voc` read as `STMainIndR` (binder order included).
Section 4: Prop-valued examples at `d = 3` (the statements of the instances; no proof obligation).
No theorem, no proof, no placeholder, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2245-check.lean`.
-/
import RBM3D
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STLocalMax
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STMainInd
#check @RBM.Gauss.Sizes.STStep1
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STGM
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.flow_z0

-- `RBM3D/Induction/Step34Pins.lean` (fc76526)
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STStep3R
#check @RBM.Gauss.Sizes.STStep4R
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STStep3
#check @RBM.Gauss.Sizes.STStep4
#check @RBM.Gauss.Sizes.STStep3I
#check @RBM.Gauss.Sizes.STStep3II
#check @RBM.Gauss.Sizes.STStep4I
#check @RBM.Gauss.Sizes.STStep4II
#check @RBM.Gauss.Sizes.STLmax_of_STLmaxU
#check @RBM.Gauss.Sizes.STLK_of_STLKU
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB

-- `RBM3D/Induction/Step2Defs.lean` (86124dc)
#check @RBM.Gauss.Sizes.STStep2

-- `RBM3D/Induction/Step5Pins.lean` (d7da51e)
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STStep5Concl
#check @RBM.Gauss.Sizes.STStep5R
#check @RBM.Gauss.Sizes.STStep5I
#check @RBM.Gauss.Sizes.STStep5II
#check @RBM.Gauss.Sizes.STStep5III
#check @RBM.Gauss.Sizes.STStep5IV
#check @RBM.Gauss.Sizes.STStep5
#check @RBM.Gauss.Step5Inst.szG
#check @RBM.Gauss.Step5Inst.flow_zG
#check @RBM.Gauss.Step5Inst.szG_reg4
#check @RBM.Gauss.Step5Inst.szB_reg5I
#check @RBM.Gauss.Step5Inst.szB_reg5II
#check @RBM.Gauss.Step5Inst.sz0_reg5III

-- `RBM3D/Induction/Step5Kit.lean` (85e43db)
#check @RBM.Gauss.Sizes.ST_step5_assembly
#check @RBM.Gauss.Sizes.st5_conStInd_mono
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.stStep5IV_holds

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2)
#check @RBM.Gauss.Sizes.STExp2U
#check @RBM.Gauss.Sizes.STExp2_of_STExp2U
#check @RBM.Gauss.Sizes.STStep2Core
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STStep6R
#check @RBM.Gauss.Sizes.STStep6I
#check @RBM.Gauss.Sizes.STStep6II
#check @RBM.Gauss.Sizes.STStep6III
#check @RBM.Gauss.Sizes.STStep6IV
#check @RBM.Gauss.Sizes.STStep6
#check @RBM.Gauss.Sizes.ST_step6R_of_any
#check @RBM.Gauss.Sizes.STRegSeq
#check @RBM.Gauss.Sizes.STExpIniI
#check @RBM.Gauss.Sizes.STExpIntI

-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7)
#check @RBM.Gauss.Sizes.STLK_of_STLKU_at
#check @RBM.Gauss.Sizes.STDecay_of_STGdecayW_at
#check @RBM.Gauss.Sizes.STLocalEntry_of_STLocalEntryU
#check @RBM.Gauss.Sizes.st6_GdecayW_of_zero
#check @RBM.Gauss.Sizes.ST_step6R_mono

-- `RBM3D/Induction/SizesComp.lean` (8810a23)
#check @RBM.Gauss.Sizes.comp
#check @RBM.Gauss.Sizes.reindex
#check @RBM.Gauss.Sizes.STFlow_comp
#check @RBM.Gauss.Sizes.STConStInd_comp
#check @RBM.Gauss.Sizes.Lloop_reindex
#check @RBM.Gauss.Sizes.STGM_reindex
#check @RBM.Gauss.Sizes.STKloop_comp
#check @RBM.Gauss.Sizes.Bctl_comp
#check @RBM.Gauss.Sizes.STWB_comp
#check @RBM.Gauss.Sizes.STblk_comp
#check @RBM.Gauss.Sizes.STflowE_comp
#check @RBM.Gauss.Sizes.integral_Lloop_reindex
#check @RBM.Gauss.Sizes.Prec_comp
#check @RBM.Gauss.Sizes.Prec_iff_comp_cover
#check @RBM.nth_cover

-- `RBM3D/Induction/ScaleFacts3.lean` (7c3072a)
#check @RBM.Gauss.Sizes.st_conStInd_sub

-- `RBM3D/Green/GbEXP.lean` (0ce09c2)
#check @RBM.Green.stStep1_holds

-- `RBM3D/Induction/PfStep5.lean` (e2ec919)
#check @RBM.Gauss.Sizes.stStep5III_holds

-- `RBM3D/Induction/ExpIntEasy.lean` (cc4d165)
#check @RBM.Gauss.Sizes.stStep6IV_holds

-- `RBM3D/Induction/ExpIntI.lean` (25362ad): the consumer of §73 (4)
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins''

-- `RBM3D/Loop/KLFinal.lean` (471b643)
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKward_of_flow

-- `RBM3D/Induction/IterationsA.lean` (6583ca2), `RBM3D/Induction/LocalAvg1.lean` (3389d24)
#check @RBM.Gauss.Sizes.iterationsA_prec_rpow
#check @RBM.Gauss.Sizes.localAvg1_STWB_le

-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.StochDomAt.trans
#check @RBM.StochDomAt.precomp_param

-- `RBM3D/Test/Axioms.lean` (25362ad)
#check @RBM.Audit.owedProps
#check @RBM.Audit.structuralProps
#check @RBM.Audit.refutedProps

-- Mathlib
#check @Nat.nth_strictMono
#check @StrictMono.tendsto_atTop

namespace RBM.Gauss.Sizes.T2245Check

open RBM RBM.Loop RBM.Path RBM.Gauss Filter

/-! ## 2. Vocabulary -/

/-- `lem:main_ind` under a regime predicate `R` of the time sequences: the body of the merged `STMainInd`
(`Induction/Defs.lean:294-306`) with the hypothesis `R sz s t` inserted after `t ≤ lemT z`. -/
def STMainIndR_voc (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) → R sz s t →
          (STLK sz (STflowE z) s ∧ STDecay sz (STflowE z) s ∧ STDecayStrong sz (STflowE z) s ∧
            STLocalMax sz (STflowE z) s ∧ STExp2 sz (STflowE z) s) →
          STConStInd sz 𝔠d s t →
          STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
            STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t ∧
            STDecayStrong sz (STflowE z) t

/-! ## 3. Pins -/

/-- Target 1: `STMainInd` is the regime-free instance. -/
def ST_mainInd_iff_any_pin : Prop :=
  ∀ d : ℕ, STMainInd d ↔ STMainIndR_voc d STAny

/-- Target 1: a weaker regime gives a stronger hypothesis-free statement (as `ST_step6R_mono`). -/
def STMainIndR_mono_pin : Prop :=
  ∀ (d : ℕ) (R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    (∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) →
    STMainIndR_voc d R → STMainIndR_voc d R'

/-- Target 2: the Step 5/6 regimes inside the Step 3/4 cases (the alignment of supervisor 1806 Q2 "Assembly" 1). -/
def st_caseI_of_reg5III_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ), STReg5III sz s t → STCaseI sz s t

def st_caseI_of_reg5I_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ), STReg5I sz s t → STCaseI sz s t

def st_caseII_of_reg5II_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ), STReg5II sz s t → STCaseII sz s t

def st_caseII_of_reg5IV_pin : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), STReg5IV sz s t → STCaseII sz s t

/-- Target 3: one main-induction step from the six step pins, the Step 3/4 regime `R34` containing `R`
(proof of the T2191 probe `ST_mainInd_of_steps`, `t/T2191` 96c6b4c `:351-404`, with `R` threaded through). -/
def ST_mainIndR_of_steps_pin : Prop :=
  ∀ (d : ℕ) (R R34 : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    (3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → R34 sz s t) →
    STStep1 d → STStep2 d → STStep3R d R34 → STStep4R d R34 → STStep5R d R → STStep6R d R →
      STMainIndR_voc d R

/-- Target 3: the four regimes, in the stage order (iii), (i), (ii), (iv). -/
def ST_mainIndR_III_of_steps_pin : Prop :=
  ∀ d : ℕ, STStep1 d → STStep2 d → STStep3I d → STStep4I d → STStep5III d → STStep6III d →
    STMainIndR_voc d STReg5III

def ST_mainIndR_I_of_steps_pin : Prop :=
  ∀ d : ℕ, STStep1 d → STStep2 d → STStep3I d → STStep4I d → STStep5I d → STStep6I d →
    STMainIndR_voc d STReg5I

def ST_mainIndR_II_of_steps_pin : Prop :=
  ∀ d : ℕ, STStep1 d → STStep2 d → STStep3II d → STStep4II d → STStep5II d → STStep6II d →
    STMainIndR_voc d STReg5II

def ST_mainIndR_IV_of_steps_pin : Prop :=
  ∀ d : ℕ, STStep1 d → STStep2 d → STStep3II d → STStep4II d → STStep5IV d → STStep6IV d →
    STMainIndR_voc d STReg5IV

/-- Target 4: the input `(c)` of the next stage from the conclusion `(Gt_bound)` of the previous one. -/
def STLocalMax_of_STLocalEntry_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E τ : ℕ → ℝ), STLocalEntry sz E τ → STLocalMax sz E τ

/-- Target 4: two stages cut at an intermediate time sequence. -/
def ST_mainIndR_seq_pin : Prop :=
  ∀ (d : ℕ) (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STMainIndR_voc d R₁ → STMainIndR_voc d R₂ → STMainIndR_voc d (STRegSeq R₁ R₂)

/-- Target 5: the seven predicates of `STMainInd` along a finite `StrictMono` cover (premises forward,
conclusions back). -/
def STLK_iff_comp_cover_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) → ∀ E τ : ℕ → ℝ,
      (STLK sz E τ ↔ ∀ k, STLK (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)))

def STLmax_iff_comp_cover_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) → ∀ E τ : ℕ → ℝ,
      (STLmax sz E τ ↔ ∀ k, STLmax (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)))

def STDecay_iff_comp_cover_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) → ∀ E τ : ℕ → ℝ,
      (STDecay sz E τ ↔ ∀ k, STDecay (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)))

def STDecayStrong_iff_comp_cover_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) → ∀ E τ : ℕ → ℝ,
      (STDecayStrong sz E τ ↔
        ∀ k, STDecayStrong (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)))

def STLocalMax_iff_comp_cover_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) → ∀ E τ : ℕ → ℝ,
      (STLocalMax sz E τ ↔
        ∀ k, STLocalMax (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)))

def STLocalEntry_iff_comp_cover_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) → ∀ E τ : ℕ → ℝ,
      (STLocalEntry sz E τ ↔
        ∀ k, STLocalEntry (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)))

def STExp2_iff_comp_cover_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ), (∀ k, StrictMono (φ k)) →
    (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) → ∀ E τ : ℕ → ℝ,
      (STExp2 sz E τ ↔ ∀ k, STExp2 (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)))

/-- Target 6: the four regime steps give `lem:main_ind` (the ten stage patterns, route (A)). -/
def ST_mainInd_of_regimes_pin : Prop :=
  ∀ d : ℕ, STMainIndR_voc d STReg5III → STMainIndR_voc d STReg5I → STMainIndR_voc d STReg5II →
    STMainIndR_voc d STReg5IV → STMainInd d

/-- Target 7: `lem:main_ind` from the step pins still owed (`STStep1`, `STStep5III`, `STStep5IV`, `STStep6IV`
are discharged by `stStep1_holds`, `stStep5III_holds`, `stStep5IV_holds`, `stStep6IV_holds`). -/
def ST_mainInd_of_pins_pin : Prop :=
  ∀ d : ℕ, STStep2 d → STStep3I d → STStep3II d → STStep4I d → STStep4II d →
    STStep5I d → STStep5II d → STStep6I d → STStep6II d → STStep6III d → STMainInd d

/-! ## 4. Instances (statements; `d = 3`) -/

/-- 1. `inst_caseI_III`: the regime-(iii) data of `sz0_reg5III` are in case (i) of Steps 3-4. -/
example : Prop :=
  STCaseI RBM.Gauss.SizesInst.sz0 RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst

/-- 2. `inst_caseI_I`: the regime-(i) data of `szB_reg5I`. -/
example : Prop := STCaseI RBM.Gauss.Step34Inst.szB (fun _ => 7 / 8) (fun _ => 15 / 16)

/-- 3. `inst_caseII_II`: the regime-(ii) data of `szB_reg5II`. -/
example : Prop := STCaseII RBM.Gauss.Step34Inst.szB (fun _ => 15 / 16) (fun _ => 31 / 32)

/-- 4. `inst_caseII_IV`: the regime-(iv) data of `szG_reg4`. -/
example : Prop := STCaseII RBM.Gauss.Step5Inst.szG (fun _ => 5 / 8) (fun _ => 3 / 4)

/-- 5. `inst_regSeq_szB`: two nonempty stages (i), (ii) at `szB` on `[0, 49/50]`, cut at `15/16`. -/
example : Prop :=
  STRegSeq STReg5I STReg5II RBM.Gauss.Step34Inst.szB (fun _ => 0) (fun _ => 49 / 50)

/-- 6. `inst_localMax_sz0`: target 4 at the merged data. -/
example : Prop :=
  STLocalEntry RBM.Gauss.SizesInst.sz0 (STflowE RBM.Gauss.InductionDefsInst.z0)
      RBM.Gauss.InductionDefsInst.sInst →
    STLocalMax RBM.Gauss.SizesInst.sz0 (STflowE RBM.Gauss.InductionDefsInst.z0)
      RBM.Gauss.InductionDefsInst.sInst

/-- 7. `inst_regimes3`: target 6 at `d = 3`. -/
example : Prop :=
  STMainIndR_voc 3 STReg5III → STMainIndR_voc 3 STReg5I → STMainIndR_voc 3 STReg5II →
    STMainIndR_voc 3 STReg5IV → STMainInd 3

/-- 8. `inst_mainInd3`: target 7 at `d = 3` (what `lem:main_ind` still owes). -/
example : Prop :=
  STStep2 3 → STStep3I 3 → STStep3II 3 → STStep4I 3 → STStep4II 3 →
    STStep5I 3 → STStep5II 3 → STStep6I 3 → STStep6II 3 → STStep6III 3 → STMainInd 3

end RBM.Gauss.Sizes.T2245Check
