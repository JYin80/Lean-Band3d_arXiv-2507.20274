/-
Release check for T2204 (dispatcher V1, Mon Oct  5 18:15 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §40, §45 O2, §57, §67).
S6-01 (stochastic layer ST-5, Step 6, first proof ticket): the Step-6 vocabulary and pins of the T2191 probe
(`git show 96c6b4c:RBM3D/Probe/T2191Pins.lean`, branch `t/T2191`; design merged report-only at 4fecaa2, §67) moved
into the new file `RBM3D/Induction/Step6Pins.lean`, with the registry lines and the instances whose proofs use
nothing of S6-02 (`Induction/Step6Kit`).
Section 1: the merged names the moved text uses (exact namespaces; file and last commit on `main` 9a207a1).
Section 2: the vocabulary and the 40 `Prop` pins of `RBM.Gauss.Sizes`, copied from the probe with the docstrings
stripped, in the temporary namespace `RBM.Gauss.Sizes.T2204Check` (T2204 defines each in `RBM.Gauss.Sizes`, verbatim,
docstrings kept).  Probe lines: §1 `46-165` (defs only; the theorems `STExp2U_iff`, `STExp2_of_STExp2U`,
`ST_step6R_of_any` are moved too but are not pinned here), §4 `401-717`, `STRegSeq` `1644-1646`.
Section 3: `InstIng6Concl` (probe `1753-1760`) in `RBM.Gauss.Step6Inst.T2204Check`, and the statements of the
instances T2204 compiles, as `Prop`-valued `example`s (no proof obligation; the probe's binders and types verbatim;
`inst_expHier`, `inst_duhamelZ`, `inst_duhamelQ` are omitted: their statements use the dot notation `sz0.STExpErr` on a name
that does not exist on `main` yet).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Imports: exactly the eleven merged modules the probe imports (probe lines 6-16; none changed between the probe's base
0818c49 and `main` 9a207a1), so the pins elaborate in the probe's environment; not the probe, not `RBM3D`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2204-check.lean`.
-/
import RBM3D.Induction.Step5Kit
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopNorm
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.DecayLoopB
import RBM3D.Loop.KLFinal
import RBM3D.Green.GbEXP
import RBM3D.Graph.LWPins
import RBM3D.Evolution.Prec

/-! ## 1. Merged names -/

-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.Sizes.Lloop
-- `RBM3D/Gauss/FineModel.lean` (0a873f1)
#check @RBM.Gauss.Sizes.seqP
-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.SizesInst.sz0
-- `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.Zd
-- `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.lemT
#check @RBM.mSigma
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Path.TimeIcc
#check @RBM.StochDomAt.precomp_param
-- `RBM3D/Kernel/Evolution.lean` (ff8d36d)
#check @RBM.zeroModeSet
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STMainInd
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
-- `RBM3D/Induction/Step2Defs.lean` (86124dc)
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STthetaOp
-- `RBM3D/Induction/Step34Pins.lean` (fc76526)
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.szB_W_tendsto
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step34Inst.conStInd_const
#check @RBM.Gauss.Step34Inst.sz0_hs0
#check @RBM.Gauss.Step34Inst.sz0_hst
#check @RBM.Gauss.Step34Inst.sz0_ht
#check @RBM.Gauss.Step34Inst.sz0_con
-- `RBM3D/Induction/Step5Pins.lean` (c8e4f17)
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STStep5R
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STSigSame
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STSigAll
#check @RBM.Gauss.Step5Inst.szG
#check @RBM.Gauss.Step5Inst.szG_W_tendsto
#check @RBM.Gauss.Step5Inst.flow_zG
#check @RBM.Gauss.Step5Inst.szG_reg4
#check @RBM.Gauss.Step5Inst.szB_reg5I
#check @RBM.Gauss.Step5Inst.szB_reg5II
#check @RBM.Gauss.Step5Inst.sz0_reg5III
#check @RBM.Gauss.Step5Inst.InstIng5Concl
#check @RBM.Gauss.Step5Inst.inst_ing5
-- `RBM3D/Induction/GridDuhamelN.lean` (2ebee73)
#check @RBM.Ind.Ugen
-- `RBM3D/Induction/ZeroModeCalc.lean` (d1cb5a6)
#check @RBM.norm_zeroModeSet_le
-- `RBM3D/Induction/QopAlgebra.lean` (6b2494e)
#check @RBM.Gauss.Sizes.stMollifierEx_holds
-- `RBM3D/Graph/LWPins.lean` (975f4ff): `LWAvgLaw` (premise of `STImproveExpAver`); `LWtermEXP` (LW-14, consumed by S6-02 only)
#check @RBM.Gauss.Sizes.LWAvgLaw
#check @RBM.Gauss.Sizes.LWtermEXP

/-! ## 2. Vocabulary and `Prop` pins (probe §1 `46-165`, §4 `401-717`, `STRegSeq` `1644-1646`; docstrings stripped) -/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2204Check

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

-- probe `:55`
def STExpErr (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) - STKloop sz n E u σ a

-- probe `:59`
def STExpELKLK (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STELKLK sz n E u σ a ω ∂(sz.seqP)

-- probe `:64`
def STExpEGt (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STEGt sz n E u σ a ω ∂(sz.seqP)

-- probe `:69`
def STExpDrift (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  STExpELKLK sz n E u σ a + STExpEGt sz n E u σ a

-- probe `:75`
def STExpTarget (n : ℕ) (u : ℝ) : ℝ :=
  (sz.Bctl n u) ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n u)

-- probe `:81`
def STExp2U (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω ∂(sz.seqP)) -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (p.1 : ℝ)))

-- probe `:105`
def STStep2Core (E s t : ℕ → ℝ) : Prop := STLocalEntryU sz E s t ∧ STAvgU sz E s t

-- probe `:121`
def STIngR6 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STExp2 sz (STflowE z) s →
          STConStInd sz 𝔠d s t → STStep2Core sz (STflowE z) s t → STLmaxU sz (STflowE z) s t →
          STLKU sz (STflowE z) s t → STGdecayW sz (STflowE z) s t 0 →
            Concl sz (STflowE z) s t

-- probe `:133`
def STStep6Concl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop := STExp2U sz E s t

-- probe `:136`
def STStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6 d R (fun sz E s t => STStep6Concl sz E s t)

-- probe `:141`
def STStep6I (d : ℕ) : Prop := STStep6R d STReg5I

-- probe `:144`
def STStep6II (d : ℕ) : Prop := STStep6R d STReg5II

-- probe `:147`
def STStep6III (d : ℕ) : Prop := STStep6R d STReg5III

-- probe `:150`
def STStep6IV (d : ℕ) : Prop := STStep6R d STReg5IV

-- probe `:155`
def STStep6 (d : ℕ) : Prop := STStep6R d STAny

-- probe `:421`
def STExpAvgAt (E u : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂(sz.seqP)) - mSigma (E n) p.1‖)
    (fun n _ _ => (sz.Bctl n (u n)) ^ 2)

-- probe `:435`
def STImproveExpAver (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ lemT (z n)) →
        LWAvgLaw sz (STflowE z) u → STLK sz (STflowE z) u → STExpAvgAt sz (STflowE z) u

-- probe `:442`
def STExpAvgU (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) (fun _ : Fin 1 => p.2.1) (fun _ => p.2.2) ω ∂(sz.seqP)) -
      mSigma (E n) p.2.1‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2)

-- probe `:457`
def STExpHier (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => STExpErr sz n E u σ a) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => STExpDrift sz n E u σ a) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => STExpErr sz n E v σ a)
      (STthetaOp sz n E u σ (fun b => STExpErr sz n E u σ b) a + STExpDrift sz n E u σ a) u

-- probe `:469`
def STExpDuhamelZ (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A (fun b => STExpErr sz n E t σ b) a =
        zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t (fun b => STExpErr sz n E s σ b)) a +
        ∫ u in s..t, zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (fun b => STExpDrift sz n E u σ b)) a

-- probe `:480`
def STExpQsrc (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    (Fin 2 → Zd d (sz.L n)) → ℂ := fun b =>
  STQop (d := d) ϑ u (fun c => STExpDrift sz n E u σ c) b +
    (STQop (d := d) ϑ u (STthetaOp sz n E u σ (fun c => STExpErr sz n E u σ c)) b -
      STthetaOp sz n E u σ (STQop (d := d) ϑ u (fun c => STExpErr sz n E u σ c)) b) -
    STPsum (d := d) (fun c => STExpErr sz n E u σ c) (b 0) * deriv (fun τ => ϑ τ b) u

-- probe `:490`
def STExpDuhamelQ (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    STMollifierProps (d := d) (sz.lam n) C c ϑ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STQop (d := d) ϑ t (fun b => STExpErr sz n E t σ b) a =
        RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t
          (STQop (d := d) ϑ s (fun b => STExpErr sz n E s σ b)) a +
        ∫ u in s..t, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (STExpQsrc sz n E u σ ϑ) a

-- probe `:500`
def STExpDuhEq (E s t : ℕ → ℝ) : Prop :=
  ∀ n (u : TimeIcc s t n) (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
    zeroModeSet d (sz.L n) A (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a =
      zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (u : ℝ) (fun b => STExpErr sz n (E n) (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b)) a

-- probe `:510`
def STExpDuhEqQ (E s t : ℕ → ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    STQop (d := d) (ϑ n) (u : ℝ) (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a =
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (u : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ)
        (STExpQsrc sz n (E n) v σ (ϑ n)) a

-- probe `:530`
def STDriftHi {d : ℕ} (sz : Sizes d) (_s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n

-- probe `:536`
def STExpLKLKHiConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))

-- probe `:545`
def STExpLKLKHi (d : ℕ) : Prop := STIngR6 d STDriftHi (fun sz E s t => STExpLKLKHiConcl sz E s t)

-- probe `:549`
def STExpEGtHiConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))

-- probe `:555`
def STExpDriftHiConcl (E s t : ℕ → ℝ) : Prop := STExpLKLKHiConcl sz E s t ∧ STExpEGtHiConcl sz E s t

-- probe `:559`
def STExpDriftLoConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpDrift sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - (p.1 : ℝ)))⁻¹) ^ 3)

-- probe `:567`
def STExpDriftLo (d : ℕ) : Prop :=
  STIngR6 d STReg5IV (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t)

-- probe `:574`
def STExpDriftDecayConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ σ : Fin 2 → Bool, STEKDecay sz s t (fun n v _ a => STExpDrift sz n (E n) (v : ℝ) σ a)

-- probe `:579`
def STExpDriftDecay (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpDriftDecayConcl sz E s t)

-- probe `:586`
def STExpWardIConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3) ∧
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ =>
        ‖STQop (d := d) (ϑ n) (q.1 : ℝ) (STthetaOp sz n (E n) (q.1 : ℝ) q.2.1.1
            (fun c => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 c)) q.2.2 -
          STthetaOp sz n (E n) (q.1 : ℝ) q.2.1.1
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (fun c => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 c)) q.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
          deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)

-- probe `:605`
def STExpWardI (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t)

-- probe `:612`
def STExpWardIIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q _ => ‖STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 -
      zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
    (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3)

-- probe `:620`
def STExpWardII (d : ℕ) : Prop :=
  STIngR6 d STReg5II (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t)

-- probe `:639`
def STExpIntConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (E s t : ℕ → ℝ) : Prop :=
  ∀ F : ∀ n, STIdx2P sz P s t n → ℝ, (∀ n p, 0 ≤ F n p) →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) Q
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p) →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) Q (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))

-- probe `:653`
def STExpIntQConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → STExpDuhEqQ sz E s t ϑ →
    ∀ F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ F n p) →
      Prec sz (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => F n p) →
      Prec sz (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
          (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
        (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))

-- probe `:669`
def STExpIntIII (d : ℕ) : Prop :=
  STIngR6 d STReg5III (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t)

-- probe `:676`
def STExpIntIV (d : ℕ) : Prop :=
  STIngR6 d STReg5IV (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t)

-- probe `:685`
def STExpIntII (d : ℕ) : Prop :=
  STIngR6 d STReg5II (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t)

-- probe `:693`
def STExpIntI (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t → STExpWardIConcl sz E s t →
      STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl sz E s t)

-- probe `:702`
def STExpIniIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2P sz STSigSame s t)
    (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
      (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b) p.2.2‖)
    (fun n p _ => STExpTarget sz n (p.1 : ℝ)) ∧
  ∀ (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))

-- probe `:715`
def STExpIniI (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpIniIConcl sz E s t)

-- probe `:1645`
def STRegSeq (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∃ m : ℕ → ℝ, (∀ n, s n < m n) ∧ (∀ n, m n < t n) ∧ R₁ sz s m ∧ R₂ sz m t

end RBM.Gauss.Sizes.T2204Check

/-! ## 3. `InstIng6Concl` and the statements of the instances T2204 compiles (probe §8) -/

namespace RBM.Gauss.Step6Inst.T2204Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter RBM.Gauss.Sizes.T2204Check

-- probe `:1755`
def InstIng6Concl (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (sz : Sizes 3)
    (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STExp2 sz (STflowE z) s →
      STStep2Core sz (STflowE z) s t → STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t →
      STGdecayW sz (STflowE z) s t 0 → Concl sz (STflowE z) s t)

-- statement of `inst_ing6` (probe `:1763`)
example : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n)) (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t),
    InstIng6Concl Concl sz z s t

-- statement of `inst_ing6_I` (probe `:1775`)
example : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (hR : R szB (fun _ => 7 / 8) (fun _ => 15 / 16)),
    InstIng6Concl Concl szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_ing6_II` (probe `:1784`)
example : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (hR : R szB (fun _ => 15 / 16) (fun _ => 31 / 32)),
    InstIng6Concl Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_ing6_III` (probe `:1793`)
example : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (hR : R sz0 sInst tInst),
    InstIng6Concl Concl sz0 z0 sInst tInst

-- statement of `inst_ing6_IV` (probe `:1800`)
example : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (hR : R szG (fun _ => 5 / 8) (fun _ => 3 / 4)),
    InstIng6Concl Concl szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_step6I` (probe `:1810`)
example : Prop :=
  ∀ (h : STStep6I 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_step6II` (probe `:1814`)
example : Prop :=
  ∀ (h : STStep6II 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_step6III` (probe `:1818`)
example : Prop :=
  ∀ (h : STStep6III 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst

-- statement of `inst_step6IV` (probe `:1822`)
example : Prop :=
  ∀ (h : STStep6IV 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_step6` (probe `:1827`)
example : Prop :=
  ∀ (h : STStep6 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst

-- statement of `inst_step6_atI` (probe `:1832`)
example : Prop :=
  ∀ (h : STStep6 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expDriftLo` (probe `:1861`)
example : Prop :=
  ∀ (h : STExpDriftLo 3),
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) szG zB
      (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_expDriftDecay` (probe `:1867`)
example : Prop :=
  ∀ (h : STExpDriftDecay 3),
    InstIng6Concl (fun sz E s t => STExpDriftDecayConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expWardI` (probe `:1872`)
example : Prop :=
  ∀ (h : STExpWardI 3),
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expWardII` (probe `:1878`)
example : Prop :=
  ∀ (h : STExpWardII 3),
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_expIniI` (probe `:1884`)
example : Prop :=
  ∀ (h : STExpIniI 3),
    InstIng6Concl (fun sz E s t => STExpIniIConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expIntI` (probe `:1889`)
example : Prop :=
  ∀ (h : STExpIntI 3),
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpDriftDecayConcl sz E s t → STExpWardIConcl sz E s t →
      STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expIntII` (probe `:1894`)
example : Prop :=
  ∀ (h : STExpIntII 3),
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_expIntIII` (probe `:1899`)
example : Prop :=
  ∀ (h : STExpIntIII 3),
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) sz0 z0 sInst tInst

-- statement of `inst_expIntIV` (probe `:1903`)
example : Prop :=
  ∀ (h : STExpIntIV 3),
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_improveExpAver` (probe `:2085`)
example : Prop :=
  ∀ (h : STImproveExpAver 3) (hA : LWAvgLaw sz0 (STflowE z0) tInst) (hK : STLK sz0 (STflowE z0) tInst),
    STExpAvgAt sz0 (STflowE z0) tInst

-- statement of `inst_A_value` (probe `:2229`)
example : Prop :=
  sz0.lam 0 ^ 2 * ((sz0.W 0 : ℕ) : ℝ) ^ 3 = 8

-- statement of `st6_idx2_nonempty` (probe `:2260`)
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ),
    Nonempty (STIdx2 sz s t n)

-- statement of `st6_idxSame_nonempty` (probe `:2264`)
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ),
    Nonempty (STIdx2P sz STSigSame s t n)

-- statement of `st6_idxMixed_nonempty` (probe `:2268`)
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ),
    Nonempty (STIdx2P sz STSigMixed s t n)

-- statement of `inst_normQA2` (probe `:2273`)
example : Prop :=
  ∀ (T : (Fin 2 → Zd 3 4) → ℂ),
    ‖zeroModeSet 3 4 (Finset.univ : Finset (Fin 2)) T‖ ≤ 4 * ‖T‖

-- statement of `inst_step6R_of_any` (probe `:2287`)
example : Prop :=
  ∀ (h : STStep6 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

end RBM.Gauss.Step6Inst.T2204Check
