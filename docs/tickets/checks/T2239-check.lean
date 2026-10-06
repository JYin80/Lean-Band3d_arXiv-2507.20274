/-
Release check for T2239 (dispatcher V1, Tue Oct  6 01:03 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68 (9), §71, §73).
S6-09a (stochastic layer ST-5, Step 6, regime (i), `6:97`, `6:104-132`): first half of the split S6-09 (estimate > 1500).
New file `RBM3D/Induction/ExpIntI.lean`.  Policy DECISIONS §73 (3)-(4), supervisor `2026-10-05-2347.md` Q2 "Correction
(interface)", "Consumer", O2: the primed successor `STExpIntI'` takes the **primed** Ward conclusion `STExpWardIConcl'`
(merged, T2232, `ExpWardI.lean:321`) as premise and has second conjunct `STExpIntQConcl'` (= merged `STExpIntQConcl`
`Step6Pins.lean:409` with `0 < C → 0 < c →` after `∀ (C c : ℝ)`).  This ticket (part a) defines both, proves the
`σ₁ = σ₂` conjunct and the regime-(i) kernel/assembly lemmas, and compiles the consumer `ST_step6_caseI_of_pins''` with
`hInt : STExpIntI' d` as a hypothesis; S6-09b proves `stExpIntI'_holds`.
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and last
commit on `main` f6650b2).
Section 2: the two new `Prop` vocabulary definitions (verbatim as T2239 defines them in `RBM.Gauss.Sizes`) and the
statements of the public theorems of `ExpIntI.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2239Check` (T2239 proves each under the same name in `RBM.Gauss.Sizes`).
Section 3: the statements of the instances (`RBM.Gauss.Step6Inst`; `szB`, `zB`, `(7/8, 15/16)`), as `Prop`-valued
`example`s.
Statements and `#check` only: no theorem, no proof term, no proof placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2239-check.lean`.
-/
import RBM3D.Induction.ExpWardI
import RBM3D.Induction.ExpIntII
import RBM3D.Induction.ExpIniI
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpEtermsB
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpDuhamel
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.QopNorm
import RBM3D.Evolution.Prec

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): shape, pins, vocabulary, instance machinery
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Sizes.STStep6R
#check @RBM.Gauss.Sizes.STStep6I
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STExpDrift
#check @RBM.Gauss.Sizes.STExpTarget
#check @RBM.Gauss.Sizes.STImproveExpAver
#check @RBM.Gauss.Sizes.STExpAvgU
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STExpQsrc
#check @RBM.Gauss.Sizes.STExpDuhamelQ
#check @RBM.Gauss.Sizes.STExpDuhEq
#check @RBM.Gauss.Sizes.STExpDuhEqQ
#check @RBM.Gauss.Sizes.STExpLKLKHi
#check @RBM.Gauss.Sizes.STExpDriftHiConcl
#check @RBM.Gauss.Sizes.STExpDriftDecayConcl
#check @RBM.Gauss.Sizes.STExpDriftDecay
#check @RBM.Gauss.Sizes.STExpWardIConcl
#check @RBM.Gauss.Sizes.STExpIntConcl
#check @RBM.Gauss.Sizes.STExpIntQConcl
#check @RBM.Gauss.Sizes.STExpIntI
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_I
#check @RBM.Gauss.Step6Inst.inst_step6I
#check @RBM.Gauss.Step6Inst.inst_expIntI

-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211)
#check @RBM.Gauss.Sizes.st6_lam_pos
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_precU_of_forall_seq
#check @RBM.Gauss.Sizes.st6_flowE_lt_two
#check @RBM.Gauss.Sizes.st6_hi_of_reg5I
#check @RBM.Gauss.Sizes.st6_duhEq_of_pin
#check @RBM.Gauss.Sizes.st6_Bctl_eq
#check @RBM.Gauss.Sizes.st6_target_nonneg
#check @RBM.Gauss.Sizes.st6_cube_le_target
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.st6_expAvgU_of_pin
#check @RBM.Gauss.Sizes.st6_EGtHi_of_LW
#check @RBM.Gauss.Sizes.st6_ini_nonzero
#check @RBM.Gauss.Sizes.st6_cover_exp2U
#check @RBM.Gauss.Sizes.st6_duhEqQ_of_pin
#check @RBM.Gauss.Sizes.st6_mollifier_family
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins
#check @RBM.Gauss.Step6Inst.inst_skeleton6I

-- `RBM3D/Induction/ExpIniI.lean` (f2766db; S6-11 = T2223): primed initial term, primed consumer (format model)
#check @RBM.Gauss.Sizes.STExpIniIConcl'
#check @RBM.Gauss.Sizes.STExpIniI'
#check @RBM.Gauss.Sizes.stExpIniI'_holds
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins'
#check @RBM.Gauss.Step6Inst.inst_skeleton6I'
#check @RBM.Gauss.Step6Inst.inst_expIniI_mixed

-- `RBM3D/Induction/ExpWardI.lean` (b112700; S6-10 = T2232): primed Ward conclusion and pin (route U)
#check @RBM.Gauss.Sizes.STExpWardIConcl'
#check @RBM.Gauss.Sizes.STExpWardI'
#check @RBM.Gauss.Sizes.stExpWardI'_holds
#check @RBM.Gauss.Sizes.stExpWardI_holds
#check @RBM.Gauss.Step6Inst.inst_expWardI'
#check @RBM.Gauss.Step6Inst.inst_expWardI'_mixed

-- `RBM3D/Induction/ExpIntII.lean` (f6650b2; S6-12b = T2233): regime-(ii) pattern; public lemmas reused
#check @RBM.Gauss.Sizes.expIntII_log_ratio
#check @RBM.Gauss.Sizes.expIntII_Bctl_le
#check @RBM.Gauss.Sizes.expIntII_rates_le_target
#check @RBM.Gauss.Sizes.expIntII_drift_integral_le
#check @RBM.Gauss.Sizes.expIntII_log_eventually
#check @RBM.Gauss.Sizes.expIntII_kernel_unif
#check @RBM.Gauss.Sizes.STExpIntConcl_of_kernel

-- the proved ingredient pins of regime (i) (consumer target 6)
#check @RBM.Gauss.Sizes.stExpLKLKHi_holds       -- ExpEtermsA.lean:607 (cd6fcba, T2222)
#check @RBM.Gauss.Sizes.stImproveExpAver_holds  -- ExpAvg.lean:879 (d0d79ce, T2217)
#check @RBM.Gauss.Sizes.stExpDuhamelZ_holds     -- ExpDuhamel.lean:385 (1fb83da, T2224)
#check @RBM.Gauss.Sizes.stExpDuhamelQ_holds     -- ExpDuhamel.lean:570 (1fb83da, T2224)
#check @RBM.Gauss.Sizes.stExpDriftDecay_holds   -- ExpEtermsB.lean:1049 (6b4fe24, T2228)
#check @RBM.Gauss.Sizes.LWtermEXP               -- Graph/LWPins.lean:311 (975f4ff; owed, LW-14)

-- kernel estimates, windows (`RBM3D/Induction/Step34Pins.lean` fc76526, `RBM3D/Evolution/Prec.lean` fc76526,
-- `RBM3D/Evolution/Pins.lean` d9de66f, `RBM3D/Induction/ScaleFacts3.lean` 7c3072a)
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.Gauss.Sizes.STEKLow
#check @RBM.Gauss.Sizes.STEKWin
#check @RBM.Gauss.Sizes.STEKSumRes2NAL
#check @RBM.Gauss.Sizes.STEKSumRes2
#check @RBM.Gauss.Sizes.stek_sumRes2NAL_holds
#check @RBM.Gauss.Sizes.stek_sumRes2_holds
#check @RBM.EKFastDecay
#check @RBM.EKSumZero
#check @RBM.Gauss.Sizes.st_window

-- mollifier and `𝒬` (`Step34Pins.lean` fc76526, `QopAlgebra.lean` 6b2494e, `QopNorm.lean` eb6d67a; part b inputs)
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.Gauss.Sizes.stQopNorm_holds
#check @RBM.Gauss.Sizes.stMollifierEx_holds
#check @RBM.Gauss.Sizes.stQop_sub_fastDecay
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_Qop
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_of_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_deriv
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_UN_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_ThetaN
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_UN

-- regimes, index sets, flow, scales (`Step5Pins.lean` d7da51e, `Step5Kit.lean` 85e43db, `Induction/Defs.lean` 64bdfd3,
-- `ScaleFacts.lean` 5d1e6b1, `GridDuhamelN.lean` 2ebee73, `Kernel/Evolution.lean`, `Defs/Params.lean`, `Defs/Semicircle.lean`,
-- `Defs/StochDomAt.lean`)
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STSigSame
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.st5_conStInd_mono
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Ind.Ugen
#check @RBM.UN
#check @RBM.zeroModeSet
#check @RBM.ellT
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.lemT

-- instance data (`Step34Pins.lean` fc76526, `Step5Pins.lean` d7da51e)
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.szB_W_tendsto
#check @RBM.Gauss.Step34Inst.conStInd_const
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step5Inst.szB_reg5I

/-! ## 2. New vocabulary (verbatim) and statements of the public theorems of `ExpIntI.lean` (closed `Prop`s) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2239Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### The primed successor (DECISIONS §73 (3); supervisor 2347 Q2 "Correction (interface)") -/

/-- `STExpIntQConcl` (`Step6Pins.lean:409-421`) with `0 < C → 0 < c →` after `∀ (C c : ℝ)`. -/
def STExpIntQConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
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

/-- The merged `STExpIntI` (`Step6Pins.lean:449-452`) with the premise `STExpWardIConcl'` and the second conjunct
`STExpIntQConcl'`. -/
def STExpIntI' (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t → STExpWardIConcl' sz E s t →
      STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl' sz E s t)

/-! ### Regime-(i) arithmetic (targets 1, 2) -/

/-- Target 1: the ratio of `(sum_res_2_NAL)`/`(sum_res_2)` in regime (i) (`1 - s ≤ g²`, `s ≤ v ≤ u < 1`). -/
def expIntI_ratio_le : Prop :=
  ∀ {g s v u : ℝ}, s ≤ v → v ≤ u → u < 1 → 1 - s ≤ g ^ 2 →
    (g ^ 2 + |1 - v|) / (g ^ 2 + |1 - u|) ≤ 2

/-- Target 2: the `u`-integral in regime (i), `∫_s^u (1-v)⁻¹ dv ≤ 2 log L` (dispatcher route: the merged
`expIntII_log_ratio` at `d := 4`, `g := g L`). -/
def expIntI_log_ratio : Prop :=
  ∀ {L : ℕ} {g s u : ℝ}, 1 ≤ L → s ≤ u → u < 1 → 1 - s ≤ g ^ 2 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u →
    ∫ v in s..u, (1 - v)⁻¹ ≤ 2 * Real.log (L : ℝ)

/-! ### The kernel, uniformly in the end time (target 3) -/

/-- Target 3: `(sum_res_2_NAL)` (`σ₁ = σ₂`) or `(sum_res_2)` (sum-zero) with `n = 2` on regime (i), for a
deterministic decaying family `𝒜_v`, lifted from "per end-time sequence `u`" to "uniformly in `s_n ≤ v ≤ u ≤ t_n`". -/
def expIntI_kernel_unif : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 𝔠d : ℝ}, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < 𝔠d → (d : ℝ) * 𝔠d < 1 →
    ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5I sz s t →
    STConStInd sz 𝔠d s t →
    ∀ (σ : Fin 2 → Bool) (𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) (X : ℕ → ℝ → ℝ),
      (σ 0 = σ 1 ∨ ∀ n v, EKSumZero (𝒜 n v)) →
      (∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v)) →
      (∀ n v, 0 ≤ X n v) →
      (∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v) →
      (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v) →
      ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
        ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u : ℝ) (𝒜 n v)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * (4 * X n v)

/-! ### The `σ₁ = σ₂` conjunct (targets 4, 5) -/

/-- Target 4: the plain Duhamel integral bound on regime (i) from a uniform drift-kernel bound (regime-(i) analogue of
the merged `STExpIntConcl_of_kernel`, `ExpIntII.lean:472`; `∫ ≤ 2 log L`, rates `expIntII_rates_le_target`). -/
def expIntI_concl_of_kernel : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → 3 ≤ d → ∀ {E s t : ℕ → ℝ},
    (∀ n, s n < t n) → (∀ n, t n < 1) → STReg5I sz s t → STExpDuhEq sz E s t →
    ∀ P : (Fin 2 → Bool) → Prop,
    (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) →
    STExpIntConcl sz ∅ P E s t

/-- Target 5: the first conjunct of `STExpIntI'` from the flow (`6:97`: `(sum_res_2_NAL)`, `n = 2`). -/
def expIntI_same : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 𝔠d : ℝ}, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < 𝔠d → (d : ℝ) * 𝔠d < 1 →
    ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5I sz s t →
    STConStInd sz 𝔠d s t → STExpDuhEq sz (STflowE z) s t → STExpDriftHiConcl sz (STflowE z) s t →
    STExpDriftDecayConcl sz (STflowE z) s t → STExpIntConcl sz ∅ STSigSame (STflowE z) s t

/-! ### The consumer (target 6; supervisor 2347 "Consumer", O2) -/

/-- Target 6a: `ST_step6_caseI_of_pins'` (`ExpIniI.lean:1127`) with `hWd : STExpWardI' d`, `hInt : STExpIntI' d`. -/
def ST_step6_caseI_of_pins'' : Prop :=
  ∀ {d : ℕ}, STExpLKLKHi d → LWtermEXP d → STImproveExpAver d → STExpDuhamelZ d → STExpDuhamelQ d →
    STExpDriftDecay d → STExpWardI' d → STExpIniI' d → STExpIntI' d → STStep6I d

/-- Target 6b: every other regime-(i) pin discharged by its merged proof; open: `LWtermEXP` (LW-14), `STExpIntI'`
(S6-09b). -/
def ST_step6I_of_LW_Int : Prop :=
  ∀ d : ℕ, LWtermEXP d → STExpIntI' d → STStep6I d

end RBM.Gauss.Sizes.T2239Check

end

/-! ## 3. The statements of the instances T2239 compiles (`d = 3`, regime (i): `szB`, `zB`, `(7/8, 15/16)`) -/

namespace RBM.Gauss.Step6Inst.T2239Check

open MeasureTheory
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst RBM.Path Filter

-- statement of `inst_skeleton6I''` (`inst_step6I (ST_step6I_of_LW_Int 3 hLW hInt)`)
example : Prop :=
  LWtermEXP 3 → RBM.Gauss.Sizes.T2239Check.STExpIntI' 3 →
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expIntI_same` (`expIntI_same` at `𝔠d = 1/300`, `conStInd_const`, Duhamel by `st6_duhEq_of_pin szB
-- (stExpDuhamelZ_holds 3)`; the drift conclusions stay hypotheses)
example : Prop :=
  STExpDriftHiConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
    STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpIntConcl szB ∅ STSigSame (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expIntI_log_ratio` (target 2 at `L = szB.L 0 = 4`, `g = 1`, `(7/8, 15/16)`: `log 2 ≤ 2 log 4`)
example : Prop :=
  ∫ v in (7 / 8 : ℝ)..(15 / 16), (1 - v)⁻¹ ≤ 2 * Real.log (((szB.L 0 : ℕ) : ℝ))

end RBM.Gauss.Step6Inst.T2239Check
