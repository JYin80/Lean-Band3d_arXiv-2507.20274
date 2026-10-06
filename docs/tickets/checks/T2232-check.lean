/-
Release check for T2232 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68 (9), §71, §73).
S6-10 (stochastic layer ST-5, Step 6): the Ward terms of regime (i) (`(eq:EPL-K)` `6:104-107`, `(eq:boundELKQ1)`
`6:121-123`, `(eq:boundcommutator)` `6:126-131`), the merged pin `STExpWardI` (`RBM3D/Induction/Step6Pins.lean:361`,
conclusion `STExpWardIConcl` `:342`, unchanged), in the new file `RBM3D/Induction/ExpWardI.lean`.  Policy DECISIONS §73 (2)
(supervisor `2026-10-05-2347.md` Q2): the primed successor `STExpWardI'` (section 2, verbatim: `STExpWardIConcl` with
`0 < C → 0 < c →` after `∀ (C c : ℝ)`); route U (optional) also proves the unsigned `STExpWardI`.
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and
last commit on `main` dc2d99b).
Section 2: the statements of the public declarations of `ExpWardI.lean` as closed `Prop`s, and the two new `Prop`
vocabulary definitions (`STExpWardIConcl'`, `STExpWardI'`, verbatim as T2232 defines them in `RBM.Gauss.Sizes`), in the
temporary namespace `RBM.Gauss.Sizes.T2232Check` (T2232 proves each `Prop`-valued pin of this section under the same
name in `RBM.Gauss.Sizes`; `{d : ℕ}` first).
Section 3: the statements of the instances T2232 compiles (`RBM.Gauss.Step6Inst`; merged data of regime (i):
`szB` (`L = 4`, `W_n = n + 4`, `lam = 1`), flow `zB`, `(s,t) = (7/8, 15/16)`), as `Prop`-valued `example`s.
Statements and `#check` only: no theorem, no proof term, no proof placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2232-check.lean`.
-/
import RBM3D.Induction.ExpIniI
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpDuhamel
import RBM3D.Induction.B45
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Induction.ConArgDet
import RBM3D.Loop.KLWard
import RBM3D.Loop.KLTree
import RBM3D.Loop.GLoopFlow
import RBM3D.Path.Walk

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the pin, its conclusion, the shape, the vocabulary,
-- the instance machinery
#check @RBM.Gauss.Sizes.STExpWardI
#check @RBM.Gauss.Sizes.STExpWardIConcl
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STExpAvgU
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STImproveExpAver
#check @RBM.Gauss.Sizes.STStep6I
#check @RBM.Gauss.Sizes.STExpIntI
#check @RBM.Gauss.Sizes.STExpIntQConcl
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_I
#check @RBM.Gauss.Step6Inst.inst_expWardI
#check @RBM.Gauss.Step6Inst.inst_step6I
-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): the `Prec` calculus, the consumer
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_precU_of_forall_seq
#check @RBM.Gauss.Sizes.st6_prec_of_forall_fin
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.st6_lam_pos
#check @RBM.Gauss.Sizes.st6_Bctl_eq
#check @RBM.Gauss.Sizes.st6_mollifier_family
#check @RBM.Gauss.Sizes.st6_expAvgU_of_pin
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins
#check @RBM.Gauss.Step6Inst.inst_skeleton6I
-- `RBM3D/Induction/ExpAvg.lean` (d0d79ce; S6-03 = T2217): `(res_ELK_n=1)` proved
#check @RBM.Gauss.Sizes.stImproveExpAver_holds
#check @RBM.Gauss.Step6Inst.inst_skeleton6I_avg
-- `RBM3D/Induction/ExpIniI.lean` (f2766db; S6-11 = T2223): the format model of the primed pattern
#check @RBM.Gauss.Sizes.STExpIniIConcl'
#check @RBM.Gauss.Sizes.STExpIniI'
#check @RBM.Gauss.Sizes.stExpIniI'_holds
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins'
#check @RBM.Gauss.Step6Inst.inst_expIniI'
#check @RBM.Gauss.Step6Inst.inst_expIniI_mixed
#check @RBM.Gauss.Step6Inst.inst_skeleton6I'
-- `RBM3D/Induction/ExpDuhamel.lean` (1fb83da; S6-05 = T2224)
#check @RBM.Gauss.Sizes.expDuh_STthetaOp_eq_ThetaN
#check @RBM.Gauss.Sizes.stExpDuhamelQ_holds
-- `RBM3D/Induction/B45.lean` (1ef8fa7; S3-19 = T2136): Ward at the last label for `𝓛-𝒦`, `(A4)`, the mollifier
-- sup bound for every real `c`, the scale inequality
#check @RBM.Gauss.Sizes.B45_ward_fin
#check @RBM.Gauss.Sizes.B45_sgnCons
#check @RBM.Gauss.Sizes.B45_ofFn_sigma
#check @RBM.Gauss.Sizes.B45_Lloop_eq
#check @RBM.Gauss.Sizes.B45_STKloop_eq
#check @RBM.Gauss.Sizes.B45_Psum_snoc
#check @RBM.Gauss.Sizes.B45_norm_kappa
#check @RBM.Gauss.Sizes.B45_scale
#check @RBM.Gauss.Sizes.B45_scales
#check @RBM.Gauss.Sizes.B45_vth_mid
#check @RBM.Gauss.Sizes.B45_vth_sup
#check @RBM.Gauss.Sizes.B45_C_nonneg
#check @RBM.Gauss.Sizes.B45_log_le
#check @RBM.Gauss.Sizes.B45_B4_le
#check @RBM.Gauss.Sizes.B45_norm_EKsgn
#check @RBM.Gauss.Sizes.B45_cmp
#check @RBM.Gauss.Sizes.stWardTypePPin_holds
-- `RBM3D/Induction/Step2Iterate.lean` (c5bbae7), `Step2Defs.lean` (86124dc): `Θ^{(2)}`
#check @RBM.Gauss.Sizes.STthetaOp
#check @RBM.Gauss.Sizes.STthetaOp_eq_ThetaN
-- `RBM3D/Induction/Step34Pins.lean` (fc76526): `𝒫`, `𝒬_t`, the mollifier, the instance data
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.STLKtensor
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step34Inst.conStInd_const
-- `RBM3D/Induction/QopAlgebra.lean` (6b2494e), `Kernel/Evolution.lean` (ff8d36d)
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_ThetaN
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_Qop
#check @RBM.Gauss.Sizes.stMollifierEx_holds
#check @RBM.ThetaN
-- `RBM3D/Induction/Step5Pins.lean` (d7da51e), `Induction/Step5Kit.lean` (85e43db)
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Step5Inst.szB_reg5I
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_t_lt_one
-- the loops, their envelope and measurability, `η`, `m`, Ward's identities, `𝒦^{(1)} = m`
-- (`Loop/GLoopFlow` 868b3b4, `Path/Walk` ddf5f74, `Loop/GLoop` e0c58e6, `Defs/Semicircle` fbc9870, `Loop/KLWard` 85ab436,
-- `Induction/ConArgDet` bbd22a5, `Induction/LemDecCalEPrec` d7da51e, `Loop/KLTree` b06ff9b, `Induction/Defs` 64bdfd3)
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.norm_Lloop_le
#check @RBM.Gauss.Sizes.walk_measurable_Lloop
#check @RBM.Gauss.etaT_pos
#check @RBM.norm_mE
#check @RBM.mE_im
#check @RBM.Loop.KLK_ward
#check @RBM.sum_gloop_ward_last_div
#check @RBM.Gauss.Sizes.lemDecCalEPrec_STKloop_one
#check @RBM.Loop.KLK_one
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
-- `Defs/Sizes` (0a873f1), `Defs/StochDomAt` (9e2b00f), `Defs/Params` (c3f3d5d), `Induction/ScaleFacts` (5d1e6b1),
-- `Induction/ScaleFacts3` (7c3072a), `Graph/LWPins` (975f4ff)
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Path.TimeIcc
#check @RBM.ellT
#check @RBM.one_le_ellT
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.scaleFacts3_W_tendsto
#check @RBM.Gauss.Sizes.LWtermEXP

/-! ## 2. Statements of the public declarations of `ExpWardI.lean` (closed `Prop`s) and the new vocabulary -/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2232Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### Ward step: `(WI_calL)`, `(WI_calK)` at the last label, in expectation (`(eq:EPL-K)` `6:105`) -/

-- `σ₁ ≠ σ₂`: `(𝒫 f_u)_{a₁} = (2iW^dη_u)⁻¹ ((𝔼⟨G_u E_{a₁}⟩ - m) - (𝔼⟨G_u^* E_{a₁}⟩ - m̄))`, per size, deterministic
-- (pathwise `B45_ward_fin` at `m = 0`, integrated; `𝒦^{(1)} = m(σ)` by `lemDecCalEPrec_STKloop_one`).
def expWI_Psum_eq : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → 0 ≤ u → u < 1 →
    ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a₁ : Zd d (sz.L n),
      STPsum (d := d) (fun b => STExpErr sz n E u σ b) a₁ =
        (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
          (((∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a₁) ω ∂(sz.seqP)) - mSigma E true) -
            ((∫ ω, Lloop sz n E u (fun _ : Fin 1 => false) (fun _ => a₁) ω ∂(sz.seqP)) - mSigma E false))

-- `(res_ELK_n=1)` uniformly in `u` (`STExpAvgU`) gives `‖𝒫 f_u‖_∞ ≺ (W^dη_u)⁻¹ (W^{-d}B_{u,0})²`, uniformly in
-- `u ∈ [s,t]`, `σ₁ ≠ σ₂`, `a₁` (deterministic; `st6_prec_det_iff`).  No regime, no mollifier.
def expWI_Psum_prec : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, t n ≤ lemT (z n)) →
      STExpAvgU sz (STflowE z) s t →
        Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n))
          (fun n q _ => ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
          (fun n q _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (STflowE z n) (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 2)

/-! ### The mollifier size in regime (i), for every real `c` (supervisor 2347 Q2; merged `B45_vth_mid`) -/

-- Regime (i) puts every `u ∈ [s_n, t_n]` in the window `1 ≤ ilambda/√(1-u) ≤ L` (`ℓ_u = ilambda/√(1-u)`).
def expWI_window : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ), STReg5I sz s t → ∀ (n : ℕ) (u : ℝ), s n ≤ u → u ≤ t n →
    0 < sz.lam n → 1 ≤ sz.lam n / Real.sqrt (1 - u) ∧ sz.lam n / Real.sqrt (1 - u) ≤ ((sz.L n : ℕ) : ℝ)

-- `‖ϑ_u‖_∞ ≤ C(e^{|c|d/2} + 2/d) ℓ_u^{-d}` in that window, every real `c` (`B45_vth_mid` at `m = 1`).
def expWI_vth_le : Prop :=
  ∀ {d L : ℕ} [NeZero L] {g C c : ℝ} (ϑ : ℝ → (Fin 2 → Zd d L) → ℂ), 1 ≤ d → 3 ≤ L → 0 < g →
    STMollifierProps (d := d) g C c ϑ → ∀ u : ℝ, 0 ≤ u → u < 1 →
      1 ≤ g / Real.sqrt (1 - u) → g / Real.sqrt (1 - u) ≤ (L : ℝ) →
        ∀ a, ‖ϑ u a‖ ≤ (C * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * C / (d : ℝ)) * ((ellT L g u) ^ d)⁻¹

/-! ### The primed successor (new `Prop`s of `ExpWardI.lean`, verbatim; DECISIONS §73 (2)) -/

/-- `STExpWardIConcl` (`Step6Pins.lean:342-357`) with `0 < C → 0 < c →` after `∀ (C c : ℝ)` (the paper's mollifier has
`c > 0`, `Def:QtPt` `3_5:1214`; the consumer's family `st6_mollifier_family` has `0 < C`, `0 < c`). -/
def STExpWardIConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
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

/-- The primed pin: the shape `STIngR6` of the merged `STExpWardI` (`Step6Pins.lean:361-362`) with `STExpWardIConcl'`. -/
def STExpWardI' (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl' sz E s t)

/-! ### The core theorems (minimal premises) and the pins -/

-- Both routes: the primed conclusion from the flow, regime (i) and `(res_ELK_n=1)` alone.
def expWI_core' : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
      STReg5I sz s t → STExpAvgU sz (STflowE z) s t → STExpWardIConcl' sz (STflowE z) s t

-- Route U only: the merged (unsigned) conclusion, every real `C, c`.
def expWI_core : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
      STReg5I sz s t → STExpAvgU sz (STflowE z) s t → STExpWardIConcl sz (STflowE z) s t

-- Route U only: the one-line passage from the unsigned to the primed conclusion.
def expWI_concl_prime : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), STExpWardIConcl sz E s t → STExpWardIConcl' sz E s t

-- The primed pin, proved (both routes; route U: from `stExpWardI_holds` and `expWI_concl_prime`).
def stExpWardI'_holds : Prop := ∀ d : ℕ, STExpWardI' d

-- The merged pin, proved: required **only** on route U.
def stExpWardI_holds : Prop := ∀ d : ℕ, STExpWardI d

end RBM.Gauss.Sizes.T2232Check

/-! ## 3. The statements of the instances T2232 compiles (`d = 3`, regime (i): `szB`, `zB`, `(7/8, 15/16)`) -/

namespace RBM.Gauss.Step6Inst.T2232Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst RBM.Path Filter

-- statement of `inst_expWardI'` (`inst_ing6_I STReg5I _ (stExpWardI'_holds 3) szB_reg5I`; both routes)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → RBM.Gauss.Sizes.T2232Check.STExpWardIConcl' sz E s t) szB zB
    (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expWardI'_mixed` (`expWI_core'` at `szB`, `zB`, `(7/8, 15/16)` for the positive family
-- `st6_mollifier_family`, as `inst_expIniI_mixed` `ExpIniI.lean:1292`; the premise `(res_ELK_n=1)` stays a hypothesis)
example : Prop :=
  STExpAvgU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧
      Prec szB (U := fun n => TimeIcc (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n ×
          {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd 3 (szB.L n)))
        (fun n q _ => ‖STPsum (d := 3) (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
          ϑ n (q.1 : ℝ) q.2.2‖)
        (fun n q _ => (szB.Bctl n (q.1 : ℝ)) ^ 3) ∧
      Prec szB (U := fun n => TimeIcc (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n ×
          {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd 3 (szB.L n)))
        (fun n q _ =>
          ‖STQop (d := 3) (ϑ n) (q.1 : ℝ) (STthetaOp szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1
              (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b)) q.2.2 -
            STthetaOp szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1
              (STQop (d := 3) (ϑ n) (q.1 : ℝ) (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b)) q.2.2‖ +
          ‖STPsum (d := 3) (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
            deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
        (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (szB.Bctl n (q.1 : ℝ)) ^ 3)

-- statement of `inst_expWardI_holds` (route U only: `inst_expWardI (stExpWardI_holds 3)`, `Step6Pins.lean:607`)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t) szB zB
    (fun _ => 7 / 8) (fun _ => 15 / 16)

end RBM.Gauss.Step6Inst.T2232Check
