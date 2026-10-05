/-
Release check for T2223 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68).
S6-11 (stochastic layer ST-5, Step 6): the initial term of regime (i) (`6:97`, `6:117`), the merged pin `STExpIniI`
(`RBM3D/Induction/Step6Pins.lean:471`, conclusion `STExpIniIConcl` `:458`, unchanged), in the new file
`RBM3D/Induction/ExpIniI.lean`.  Finding T2223a (ticket): the second conjunct of `STExpIniIConcl` quantifies over every
mollifier family, also `c ≤ 0` (no decay of `ϑ`); the primed successor `STExpIniI'` (section 2) adds `0 < C`, `0 < c`.
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and
last commit on `main` 63d62b4).
Section 2: the statements of the public declarations of `ExpIniI.lean` as closed `Prop`s, and the two new `Prop`
vocabulary definitions (`STExpIniIConcl'`, `STExpIniI'`, verbatim as T2223 defines them in `RBM.Gauss.Sizes`), in the
temporary namespace `RBM.Gauss.Sizes.T2223Check` (T2223 proves each `Prop`-valued pin of this section under the same
name in `RBM.Gauss.Sizes`; `{d : ℕ}` first).
Section 3: the statements of the instances T2223 compiles (`RBM.Gauss.Step6Inst`; merged data of regime (i):
`szB` (`L = 4`, `W_n = n + 4`, `lam = 1`), flow `zB`, `(s,t) = (7/8, 15/16)`), as `Prop`-valued `example`s.
Statements and `#check` only: no theorem, no proof term, no proof placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2223-check.lean`.
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.QopNorm
import RBM3D.Evolution.Prec
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step2Events
import RBM3D.Gauss.DominationAt
import RBM3D.Path.Walk
import RBM3D.Loop.GLoopFlow
import RBM3D.Loop.KLFinal
import RBM3D.Evolution.ExpInv

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the pin, its conclusion, the shape, the vocabulary,
-- the other regime-(i) pins (premises of the consumer), the instance machinery
#check @RBM.Gauss.Sizes.STExpIniI
#check @RBM.Gauss.Sizes.STExpIniIConcl
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STExpTarget
#check @RBM.Gauss.Sizes.STStep2Core
#check @RBM.Gauss.Sizes.STStep6I
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Sizes.STImproveExpAver
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STExpDuhamelQ
#check @RBM.Gauss.Sizes.STExpLKLKHi
#check @RBM.Gauss.Sizes.STExpDriftDecay
#check @RBM.Gauss.Sizes.STExpWardI
#check @RBM.Gauss.Sizes.STExpIntQConcl
#check @RBM.Gauss.Sizes.STExpIntI
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_I
#check @RBM.Gauss.Step6Inst.inst_step6I
#check @RBM.Gauss.Step6Inst.inst_expIniI
-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): the consumer, the `Prec` calculus, the comparisons
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins
#check @RBM.Gauss.Step6Inst.inst_skeleton6I
#check @RBM.Gauss.Sizes.st6_mollifier_family
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_precU_of_forall_seq
#check @RBM.Gauss.Sizes.st6_prec_pi_norm
#check @RBM.Gauss.Sizes.st6_prec_of_forall_fin
#check @RBM.Gauss.Sizes.st6_flowE_lt_two
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.st6_target_nonneg
#check @RBM.Gauss.Sizes.st6_target_mono
#check @RBM.Gauss.Sizes.st6_Bctl_eq
#check @RBM.Gauss.Sizes.st6_ini_sumNdecay
#check @RBM.Gauss.Sizes.st6_ini_nonzero
#check @RBM.Gauss.Sizes.st6_cover_exp2U
#check @RBM.Gauss.Sizes.STDecay_of_STGdecayW_at
#check @RBM.Gauss.Sizes.st6_lam_pos
-- `RBM3D/Induction/Step5Pins.lean` (d7da51e), `Induction/Step5Kit.lean` (85e43db)
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STSigSame
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Step5Inst.szB_reg5I
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_conStInd_mono
#check @RBM.Gauss.Sizes.st5_zeroModeSet_empty
-- `RBM3D/Induction/Step34Pins.lean` (fc76526): `𝒫`, `𝒬_t`, the mollifier, `lem_+Q`, the kernel consumer forms
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.Gauss.Sizes.STEKLow
#check @RBM.Gauss.Sizes.STEKWin
#check @RBM.Gauss.Sizes.STEKSumNdecay
#check @RBM.Gauss.Sizes.STEKSumRes2NAL
#check @RBM.Gauss.Sizes.STEKSumRes2
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step34Inst.conStInd_const
-- `RBM3D/Evolution/Prec.lean` (fc76526): the kernel theorems (proved)
#check @RBM.Gauss.Sizes.stek_sumRes2NAL_holds
#check @RBM.Gauss.Sizes.stek_sumRes2_holds
#check @RBM.Gauss.Sizes.stek_sumNdecay_holds
-- `RBM3D/Induction/QopNorm.lean` (eb6d67a), `Induction/QopAlgebra.lean` (6b2494e): `lem_+Q` and the `𝒬` algebra
#check @RBM.Gauss.Sizes.stQopNorm_holds
#check @RBM.Gauss.Sizes.stQop_sub_fastDecay
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_Qop
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_of_sumZero
#check @RBM.Gauss.Sizes.stMollifierEx_holds
-- `RBM3D/Evolution/Pins.lean` (d9de66f): `(deccA0)`, `(sumAzero)`, the charges
#check @RBM.EKFastDecay
#check @RBM.EKSumZero
#check @RBM.EKsgn
-- `RBM3D/Induction/Defs.lean` (64bdfd3): the premises of `STIngR6` and the flow
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STKbound
-- `RBM3D/Defs/Sizes.lean` (0a873f1), `Defs/Lattice.lean` (51f1a17), `Defs/Params.lean` (c3f3d5d),
-- `Defs/Semicircle.lean` (fbc9870)
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.zdistInf_le_zdistD
#check @RBM.Gauss.zdistD_le_mul_zdistInf
#check @RBM.zdistD
#check @RBM.ellT
#check @RBM.one_le_ellT
#check @RBM.lemT
-- `RBM3D/Induction/ScaleFacts3.lean` (7c3072a), `Induction/ScaleFacts.lean` (5d1e6b1): the kernel window, `B`
#check @RBM.Gauss.Sizes.st_window
#check @RBM.Gauss.Sizes.st_EKWin
#check @RBM.Gauss.Sizes.scaleFacts3_W_tendsto
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.STBctl_ge
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f), `Gauss/DominationAt.lean` (9e2b00f): `≺`, `w.h.p.`, `≺ → 𝔼` (pattern)
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.Whp
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_le_left
#check @RBM.Gauss.momentDomAt_of_stochDomAt
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4), `Path/Walk.lean` (ddf5f74), `Loop/GLoop.lean` (e0c58e6),
-- `Loop/KLFinal.lean` (471b643), `Induction/Step2Events.lean` (7f9bfa1): envelope, measurability, `η`, `|𝒦|`
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.norm_Lloop_le
#check @RBM.Gauss.Sizes.walk_measurable_Lloop
#check @RBM.Gauss.etaT_pos
#check @RBM.Gauss.Sizes.ST_flow_eta_pos
#check @RBM.Gauss.Sizes.stKbound_of_flow
-- `RBM3D/Induction/GridDuhamelN.lean` (2ebee73), `Kernel/Evolution.lean` (ff8d36d): the kernel of the pin and of EK
#check @RBM.Ind.Ugen
#check @RBM.UN
-- `RBM3D/Graph/LWPins.lean` (975f4ff): premise of the consumer
#check @RBM.Gauss.Sizes.LWtermEXP
-- `RBM3D/Evolution/ExpInv.lean` (88600b1): translation invariance of `𝔼𝓛` (Finding T2223a only)
#check @RBM.Gauss.Sizes.stExpInv_holds

/-! ## 2. Statements of the public declarations of `ExpIniI.lean` (closed `Prop`s) and the new vocabulary -/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2223Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### Decay of `f_s = 𝔼(𝓛-𝒦)^{(2)}_s` through `≺ → 𝔼` (new; pattern: the private `meanFar_norm_integral_le`,
`meanFar_bad_le`, `meanFar_B_bound`, `Evolution/MeanFar.lean:845, 942, 964`) -/

-- `(Eq:Gdecay+IND)` at `s` (`STDecay`, `Induction/Defs.lean:121`) plus the a.s. envelope `|𝓛^{(2)}_s| ≤ η_s^{-2}`
-- (`norm_Lloop_le`) and `|𝒦| ≤ poly`: `f_s` is `(s, ε', D)`-decaying (`(deccA0)`, `EKFastDecay`) for every
-- `ε', D > 0`, eventually, every `σ`.  Deterministic conclusion.
def expIniI_fastDecay : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → STDecay sz (STflowE z) s →
      ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
        EKFastDecay (sz.lam n) (s n) ((sz.W n : ℕ) : ℝ) ε' D
          (fun b => STExpErr sz n (STflowE z n) (s n) σ b)

-- `(deccA0)` at the kernel start `s` passes to every later start `v` (`ℓ_v ≥ ℓ_s`): the kernel pins ask for the
-- decay at every `v ∈ [s_n, u_n]` of their index set (`STEKDecay`, `Step34Pins.lean:595`).
def expIniI_fastDecay_mono : Prop :=
  ∀ {d L n : ℕ} {g s v W ε D : ℝ} (A : (Fin n → Zd d L) → ℂ), 0 ≤ g → 0 ≤ W → s ≤ v → v < 1 →
    EKFastDecay g s W ε D A → EKFastDecay g v W ε D A

/-! ### `σ₁ = σ₂`: `(sum_res_2_NAL)` (`3_5:1649`; `stek_sumRes2NAL_holds`), ratio `(ilambda² + 1-s)/(ilambda² + 1-u) ≤ 2` -/

-- The first conjunct of `STExpIniIConcl` (`Step6Pins.lean:458-462`) on regime (i), with an explicit `𝔠_d`
-- (`d 𝔠_d < 1`: the window `STEKWin` from `st_window`).
def expIniI_same : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 𝔠d : ℝ}, 0 < κ → 0 < 𝔠d → (d : ℝ) * 𝔠d < 1 →
    ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5I sz s t →
        STDecay sz (STflowE z) s → STExp2 sz (STflowE z) s → STConStInd sz 𝔠d s t →
          Prec sz (U := STIdx2P sz STSigSame s t)
            (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
              (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b) p.2.2‖)
            (fun n p _ => STExpTarget sz n (p.1 : ℝ))

/-! ### `σ₁ ≠ σ₂`: `lem_+Q` (`stQopNorm_holds`, `stQop_sub_fastDecay`), `(sum_res_2)` (`3_5:1659`; `stek_sumRes2_holds`),
ratio `≤ 4`; mollifier constants positive -/

-- The three inputs of `(sum_res_2)` for `𝒬_s f_s` (deterministic, eventually): `‖𝒬_s f_s‖_∞ ≤ N^τ T_s`
-- (`lem_+Q`), `(deccA0)` of `𝒬_s f_s`, `(sumAzero)` of `𝒬_s f_s` (`𝒫 ∘ 𝒬_s = 0`).
def expIniI_Qop : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → STDecay sz (STflowE z) s →
      STExp2 sz (STflowE z) s →
      ∀ (C c : ℝ), 0 < C → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
        (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
          (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
            ‖STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (s n)) ∧
          (∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
            EKFastDecay (sz.lam n) (s n) ((sz.W n : ℕ) : ℝ) ε' D
              (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b))) ∧
          (∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
            EKSumZero (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)))

-- The second conjunct of `STExpIniIConcl` (`Step6Pins.lean:463-469`) for **positive** mollifier constants.
def expIniI_mixed : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 𝔠d : ℝ}, 0 < κ → 0 < 𝔠d → (d : ℝ) * 𝔠d < 1 →
    ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5I sz s t →
        STDecay sz (STflowE z) s → STExp2 sz (STflowE z) s → STConStInd sz 𝔠d s t →
        ∀ (C c : ℝ), 0 < C → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
          (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
          Prec sz (U := STIdx2P sz STSigMixed s t)
            (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
              (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
            (fun n p _ => STExpTarget sz n (p.1 : ℝ))

/-! ### Finding T2223a: the class of the merged second conjunct contains non-decaying mollifiers -/

-- A mollifier family with `c ≥ 0`, translated in the indices `a_i`, `i ≠ 0`, through a fixed shift `v`, satisfies
-- `STMollifierProps` with `c = 0` (no decay): the merged `STExpIniIConcl` quantifies over it.
def expIniI_props_shift : Prop :=
  ∀ {d L m : ℕ} [NeZero L] (g C c : ℝ) (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (v : Zd d L), 0 ≤ c →
    STMollifierProps (d := d) g C c ϑ →
      STMollifierProps (d := d) g C 0 (fun t a => ϑ t (fun i => if i = 0 then a 0 else a i + v))

/-! ### The primed successor (new `Prop`s of `ExpIniI.lean`, verbatim; T2223a) -/

/-- `STExpIniIConcl` with `0 < C → 0 < c →` in the second conjunct (the constants of `STQopNorm`,
`stQop_sub_fastDecay`, and of the family `st6_mollifier_family` the consumer builds). -/
def STExpIniIConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2P sz STSigSame s t)
    (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
      (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b) p.2.2‖)
    (fun n p _ => STExpTarget sz n (p.1 : ℝ)) ∧
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))

/-- The primed pin: the shape `STIngR6` of the merged `STExpIniI` (`Step6Pins.lean:471`) with `STExpIniIConcl'`. -/
def STExpIniI' (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpIniIConcl' sz E s t)

-- The primed pin, proved (route A; the premise `3 ≤ d` is used).
def stExpIniI'_holds : Prop := ∀ d : ℕ, STExpIniI' d

-- The merged pin, proved: required **only** on route B (the preflight shows the second conjunct for `c ≤ 0`).
def stExpIniI_holds : Prop := ∀ d : ℕ, STExpIniI d

-- The consumer of the primed pin: `ST_step6_caseI_of_pins` (`Step6Kit.lean:947`) with `STExpIniI'` for `STExpIniI`
-- (its family `st6_mollifier_family` has `0 < C`, `0 < c`).  Route A only.
def ST_step6_caseI_of_pins' : Prop :=
  ∀ {d : ℕ}, STExpLKLKHi d → LWtermEXP d → STImproveExpAver d → STExpDuhamelZ d → STExpDuhamelQ d →
    STExpDriftDecay d → STExpWardI d → STExpIniI' d → STExpIntI d → STStep6I d

end RBM.Gauss.Sizes.T2223Check

/-! ## 3. The statements of the instances T2223 compiles (`d = 3`, regime (i): `szB`, `zB`, `(7/8, 15/16)`) -/

namespace RBM.Gauss.Step6Inst.T2223Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst RBM.Path Filter

-- statement of `inst_expIniI'` (`inst_ing6_I` at `stExpIniI'_holds 3`; stochastic premises stay hypotheses)
example : Prop :=
  InstIng6Concl (fun sz E s t => RBM.Gauss.Sizes.T2223Check.STExpIniIConcl' sz E s t) szB zB
    (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_skeleton6I'` (`ST_step6_caseI_of_pins'` with `stExpIniI'_holds 3`, then `inst_step6I`)
example : Prop :=
  STExpLKLKHi 3 → LWtermEXP 3 → STImproveExpAver 3 → STExpDuhamelZ 3 → STExpDuhamelQ 3 → STExpDriftDecay 3 →
    STExpWardI 3 → STExpIntI 3 →
      InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expIniI_fastDecay` (`expIniI_fastDecay` at `szB`, `zB`, `s ≡ 7/8`)
example : Prop :=
  STDecay szB (STflowE zB) (fun _ => 7 / 8) →
    ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKFastDecay (szB.lam n) (7 / 8) ((szB.W n : ℕ) : ℝ) ε' D
        (fun b => STExpErr szB n (STflowE zB n) (7 / 8) σ b)

-- statement of `inst_expIniI_props_shift` (`d = 3`, `L = 4`, `g = 1`, shift `v = 2 e₀`; no hypothesis on `ϑ` left)
example : Prop :=
  ∀ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 4) → ℂ), 0 ≤ c → STMollifierProps (d := 3) 1 C c ϑ →
    STMollifierProps (d := 3) 1 C 0 (fun t a => ϑ t (fun i => if i = 0 then a 0 else a i + Pi.single 0 2))

end RBM.Gauss.Step6Inst.T2223Check
