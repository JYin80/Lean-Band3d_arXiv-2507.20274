/-
Release check for T2257 (dispatcher V1, Tue Oct  6 04:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §81 (2)-(3), §73 (3)-(4),
§76 (1)-(3), §79, §64 (4), §45 O2, §29, §20, §17, §16).
S6-09b (stochastic layer ST-5, Step 6, regime (i), `6:97`, `6:104-132`): the `𝒬` conjunct of the merged primed pin
`STExpIntI'` (`Induction/ExpIntI.lean:71`, T2239) by the transfer route (d) of supervisor `2026-10-06-0255.md` §2.2:
the explicit mollifier `ϑ* = QopAlgebra_mollifier d (L_n) 1 (ilambda_n)` (decaying derivative: T2249 `QopDecay.lean`),
the initial-term difference `R_s = (𝒫f_s)(ϑ_s − ϑ*_s)`, the paper's route for `ϑ*`, the back-transfer to `ϑ`.
New file `RBM3D/Induction/ExpIntIQ.lean`.  No new `Prop` pin; the merged pins `STExpIntI'`, `STExpIntQConcl'` are unchanged.
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and last
commit on `main` 88ee6fd).
Section 2: one vocabulary definition (`expIntIQ_star`, the explicit family) and the statements of the public theorems
of `ExpIntIQ.lean` as closed `Prop`s, in the temporary namespace `RBM.Gauss.Sizes.T2257Check` (T2257 proves each under the
same name in `RBM.Gauss.Sizes`).
Section 3: the statements of the instances (`RBM.Gauss.Step6Inst`; `szB`, `zB`, `(7/8, 15/16)`), as `Prop`-valued
`example`s.
Statements and `#check` only: no theorem, no proof term, no proof placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2257-check.lean`.
-/
import RBM3D.Induction.ExpIntI
import RBM3D.Induction.QopDecay
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.QopNorm
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.Step6Pins
import RBM3D.Induction.ExpWardI
import RBM3D.Induction.ExpIntII
import RBM3D.Induction.ExpDuhamel
import RBM3D.Induction.LemDecCalELip
import RBM3D.Loop.GLoopFlow
import RBM3D.Kernel.PropT
import RBM3D.Evolution.Prec

/-! ## 1. Merged names -/

-- `RBM3D/Induction/ExpIntI.lean` (25362ad; S6-09a = T2239): the primed pin, its first conjunct, the kernel, the consumer
#check @RBM.Gauss.Sizes.STExpIntQConcl'
#check @RBM.Gauss.Sizes.STExpIntI'
#check @RBM.Gauss.Sizes.expIntI_ratio_le
#check @RBM.Gauss.Sizes.expIntI_log_ratio
#check @RBM.Gauss.Sizes.expIntI_kernel_unif
#check @RBM.Gauss.Sizes.expIntI_concl_of_kernel
#check @RBM.Gauss.Sizes.expIntI_same
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins''
#check @RBM.Gauss.Sizes.ST_step6I_of_LW_Int
#check @RBM.Gauss.Step6Inst.inst_skeleton6I''
#check @RBM.Gauss.Step6Inst.inst_expIntI_same
#check @RBM.Gauss.Step6Inst.inst_expIntI_kernel_unif_sumzero

-- `RBM3D/Induction/QopDecay.lean` (24b85cd; S6-09c = T2249): derivative decay, `Θ^{(n)}` decay propagation
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_derivDecay
#check @RBM.Gauss.Sizes.QopDecay_deriv_fastDecay
#check @RBM.Gauss.Sizes.QopDecay_thetaKer_decay
#check @RBM.Gauss.Sizes.QopDecay_ThetaN_fastDecay
#check @RBM.Gauss.Sizes.QopDecay_STthetaOp_fastDecay

-- `RBM3D/Induction/QopAlgebra.lean` (6b2494e; S3-04 = T2055): the explicit mollifier and the `𝒬`-algebra
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_sum
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props
#check @RBM.Gauss.Sizes.stMollifierEx_holds
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_differentiableAt
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_Qop
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_of_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_deriv
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sub
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_ThetaN

-- `RBM3D/Induction/QopNorm.lean` (eb6d67a; S3-05 = T2059): `lem_+Q` and its decay clause
#check @RBM.Gauss.Sizes.stQopNorm_holds
#check @RBM.Gauss.Sizes.stQop_sub_fastDecay

-- `RBM3D/Induction/Step34Pins.lean` (fc76526): operators, mollifier class, kernel pins; `RBM.Gauss.Step34Inst` data
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.Gauss.Sizes.STEKSumRes2
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.szB_W_tendsto
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.conStInd_const
#check @RBM.Gauss.Step34Inst.szB_flow_ht

-- `RBM3D/Evolution/Prec.lean` (fc76526), `RBM3D/Evolution/Pins.lean` (d9de66f): `(sum_res_2)`, `(deccA0)`, `(sumAzero)`
#check @RBM.Gauss.Sizes.stek_sumRes2_holds
#check @RBM.EKFastDecay
#check @RBM.EKSumZero

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): vocabulary, source, Duhamel, drift conclusions, instances
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STStep6I
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STExpDrift
#check @RBM.Gauss.Sizes.STExpTarget
#check @RBM.Gauss.Sizes.STExpQsrc
#check @RBM.Gauss.Sizes.STExpDuhamelQ
#check @RBM.Gauss.Sizes.STExpDuhEq
#check @RBM.Gauss.Sizes.STExpDuhEqQ
#check @RBM.Gauss.Sizes.STExpDriftHiConcl
#check @RBM.Gauss.Sizes.STExpDriftDecayConcl
#check @RBM.Gauss.Sizes.STExpIntConcl
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_I
#check @RBM.Gauss.Step6Inst.inst_step6I
#check @RBM.Gauss.Step6Inst.inst_expIntI

-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211)
#check @RBM.Gauss.Sizes.st6_lam_pos
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_flowE_lt_two
#check @RBM.Gauss.Sizes.st6_cube_le_target
#check @RBM.Gauss.Sizes.st6_target_nonneg
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st6_duhEqQ_of_pin
#check @RBM.Gauss.Sizes.st6_mollifier_family

-- `RBM3D/Induction/ExpWardI.lean` (b112700; S6-10 = T2232): the primed Ward premise
#check @RBM.Gauss.Sizes.STExpWardIConcl'
#check @RBM.Gauss.Sizes.STExpWardI'
#check @RBM.Gauss.Sizes.stExpWardI'_holds
#check @RBM.Gauss.Step6Inst.inst_expWardI'
#check @RBM.Gauss.Step6Inst.inst_expWardI'_mixed

-- `RBM3D/Induction/ExpDuhamel.lean` (1fb83da; S6-05 = T2224), `RBM3D/Induction/ExpIntII.lean` (f6650b2; S6-12b = T2233)
#check @RBM.Gauss.Sizes.stExpDuhamelQ_holds
#check @RBM.Gauss.Sizes.expIntII_rates_le_target
#check @RBM.Gauss.Sizes.expIntII_log_eventually

-- `RBM3D/Induction/ExpIniI.lean` (f2766db; S6-11 = T2223): instance pattern (positive family)
#check @RBM.Gauss.Sizes.stExpIniI'_holds
#check @RBM.Gauss.Step6Inst.inst_expIniI_mixed

-- envelopes of `f = STExpErr` (the polynomial bound `‖f_v‖ ≤ W^{C₀}` of the decay lemmas)
#check @RBM.Gauss.Sizes.norm_Lloop_le
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_norm
#check @RBM.Gauss.Sizes.LemDecCalELip_STKloop_two_norm

-- generic vocabulary
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STthetaOp
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.Step5Inst.szB_reg5I
#check @RBM.Ind.Ugen
#check @RBM.Ind.GridDuhamelN_Ugen_add
#check @RBM.ThetaN
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.lemT
#check @RBM.ellT
#check @RBM.ellT_mono

/-! ## 2. Vocabulary and statements of the public theorems of `ExpIntIQ.lean` (closed `Prop`s) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2257Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### The explicit family `ϑ*` (supervisor 0255 §2.2 step 1; DECISIONS §81 (2)) -/

/-- `ϑ*_n = QopAlgebra_mollifier d (L_n) 1 (ilambda_n)`: the explicit mollifier of `rmk:choosechi` at `m = 1` (tensors of
two indices), for every `n` (no case split: clause 1 holds for every real `g`, `QopAlgebra_mollifier_sum`). -/
def expIntIQ_star {d : ℕ} (sz : Sizes d) : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ :=
  fun n => QopAlgebra_mollifier d (sz.L n) 1 (sz.lam n)

/-- **Target 1**: `ϑ*` is admissible eventually, constants `C* = (1 + 40 d) 6^d`, `c = 1/2` (`QopAlgebra_mollifier_props` at
`m = 1`, `0 < ilambda_n` eventually by `st6_lam_pos`). -/
def expIntIQ_star_props : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (𝔡 : ℝ), sz.WO 𝔡 →
    ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) ((1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1)) (1 / 2)
      (expIntIQ_star sz n)

/-! ### Algebra of the transfer (route (d) steps 3, 5) -/

/-- **Target 2**: changing the mollifier changes `𝒬` by `(𝒫A)(ϑ − ϑ')`: `𝒬^{ϑ'}A = 𝒬^{ϑ}A + (𝒫A)_{a₁}(ϑ_a − ϑ'_a)`. -/
def expIntIQ_Qop_sub : Prop :=
  ∀ (d L : ℕ) [NeZero L] (ϑ ϑ' : ℝ → (Fin 2 → Zd d L) → ℂ) (s : ℝ) (A : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L),
    STQop (d := d) ϑ' s A a = STQop (d := d) ϑ s A a + STPsum (d := d) A (a 0) * (ϑ s a - ϑ' s a)

/-- **Target 3**: the difference `R = (𝒫A)(ϑ − ϑ')` of two admissible mollifiers is sum-zero (clause 1 of both). -/
def expIntIQ_diff_sumZero : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g C c C' c' : ℝ) (ϑ ϑ' : ℝ → (Fin 2 → Zd d L) → ℂ),
    STMollifierProps (d := d) g C c ϑ → STMollifierProps (d := d) g C' c' ϑ' →
    ∀ (s : ℝ) (A : (Fin 2 → Zd d L) → ℂ),
      EKSumZero (fun a : Fin 2 → Zd d L => STPsum (d := d) A (a 0) * (ϑ s a - ϑ' s a))

/-- **Target 4**: the `𝒬`-source `A*_v = 𝒬*_v D_v + [𝒬*_v, Θ] f_v − (𝒫f_v) ∂_vϑ*_v` of `ϑ*` is sum-zero, for every `n` with
`0 < ilambda_n`, `|E| ≤ 2`, `0 ≤ v < 1` (`QopAlgebra_Psum_Qop`, `QopAlgebra_ThetaN_sumZero` with `‖mSigma E b‖ = 1`,
`QopAlgebra_Psum_deriv` with `QopAlgebra_mollifier_differentiableAt`). -/
def expIntIQ_src_sumZero : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| ≤ 2 → 0 < sz.lam n →
    ∀ (v : ℝ), 0 ≤ v → v < 1 → ∀ σ : Fin 2 → Bool,
      EKSumZero (STExpQsrc sz n E v σ (expIntIQ_star sz n))

/-! ### Decay of the `ϑ*`-source (route (d) step 4; supervisor 0255 §2.2 (c)) -/

/-- **Target 5**: `(deccA0)` of the `ϑ*`-source on `[s,t]`, every `σ`: `𝒬*D` by `STExpDriftDecayConcl` and `stQop_sub_fastDecay`;
the commutator `Θ(f − 𝒬*f) − (Θf − 𝒬*(Θf))` by `stQop_sub_fastDecay` and `QopDecay_STthetaOp_fastDecay`; `(𝒫f)∂ϑ*` by
`QopDecay_deriv_fastDecay`.  The side conditions `L^d ≤ W^K`, `(1-v)⁻¹ ≤ W^K`, `ilambda ≤ 𝔡⁻¹`, `‖·‖ ≤ W^{C₀}` are discharged
from `STFlow`, regime (i) and the envelopes. -/
def expIntIQ_src_decay : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (κ ε 𝔠 𝔡 : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 →
  ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
  ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5I sz s t →
    STExpDriftHiConcl sz (STflowE z) s t → STExpDriftDecayConcl sz (STflowE z) s t →
    ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (STExpQsrc sz n (STflowE z n) v σ (expIntIQ_star sz n))

/-! ### The transfer (route (d) steps 3–5) -/

/-- **Target 6 (step 3, the initial term)**: from the bound `F` on `𝒰_{s,u}𝒬^ϑ_s f_s` (any admissible `ϑ`, `0 < C`, `0 < c`) to
the bound `F + B_u³` on `𝒰_{s,u}𝒬^{ϑ*}_s f_s`: `R_s = (𝒫f_s)(ϑ_s − ϑ*_s)` is sum-zero (target 3), deterministic, fast-decaying
(clause 2 of both, `stQop_sub_fastDecay`), `‖R_s‖ ≺ B_s³` (first Ward conjunct at `u = s`, for `ϑ` and `ϑ*`), so `(sum_res_2)`
(the sum-zero branch of `expIntI_kernel_unif`) gives `‖𝒰_{s,u}R_s‖ ≺ 4B_s³ ≤ 4B_u³` (`STBctl_mono`). -/
def expIntIQ_ini : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (κ ε 𝔠 𝔡 𝔠d : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < 𝔠d → (d : ℝ) * 𝔠d < 1 →
  ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
  ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5I sz s t →
    STConStInd sz 𝔠d s t → STExpWardIConcl' sz (STflowE z) s t →
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
  ∀ F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ F n p) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p + sz.Bctl n (p.1 : ℝ) ^ 3)

/-- **Target 7 (step 4, the `ϑ*` bound)**: the paper's route `6:109-132` for `ϑ*`: the `𝒬`-Duhamel identity of `ϑ*`
(`stExpDuhamelQ_holds`, `st6_duhEqQ_of_pin`, target 1), every source sum-zero (target 4) and decaying (target 5), the sup bound
`‖A*_v‖ ≺ (1-v)⁻¹(B_v^{11/5} + B_v^{5/2} + B_v³)` (`lem_+Q` for `𝒬*D`, the second Ward conjunct for `ϑ*`), the sum-zero branch of
`expIntI_kernel_unif`, `∫_s^u (1-v)⁻¹ ≤ 2 log L` (`expIntI_log_ratio`), rates `≤ 4T_u` (`expIntII_rates_le_target`,
`st6_cube_le_target`), `log L ≺ 1` (`expIntII_log_eventually`). -/
def expIntIQ_star_bound : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (κ ε 𝔠 𝔡 𝔠d : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < 𝔠d → (d : ℝ) * 𝔠d < 1 →
  ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
  ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5I sz s t →
    STConStInd sz 𝔠d s t →
    STExpDriftHiConcl sz (STflowE z) s t → STExpDriftDecayConcl sz (STflowE z) s t →
    STExpWardIConcl' sz (STflowE z) s t →
  ∀ G : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ G n p) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => G n p) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ)
        (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p + STExpTarget sz n (p.1 : ℝ))

/-- **Target 8 (step 5, back to `ϑ`)**: `𝒬^ϑ_u f_u = 𝒬^{ϑ*}_u f_u + (𝒫f_u)ϑ*_u − (𝒫f_u)ϑ_u` (target 2), the last two terms
`≺ B_u³` by the first Ward conjunct for `ϑ*` and for `ϑ`. -/
def expIntIQ_back : Prop :=
  ∀ (d : ℕ) (sz : Sizes d), sz.SizeTendsto → ∀ (E s t : ℕ → ℝ), (∀ n, s n < t n) → (∀ n, t n < 1) →
    STExpWardIConcl' sz E s t →
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) ((1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1)) (1 / 2)
      (expIntIQ_star sz n)) →
  ∀ G : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ G n p) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ)
        (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p) →
    Prec sz (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
        (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p + sz.Bctl n (p.1 : ℝ) ^ 3)

/-- **Target 9 (assembly)**: the second conjunct of `STExpIntI'` under the premises of `STIngR6`, regime (i): targets 6, 7
(`G = F + B³`), 8, then `F + B³ + T + B³ ≤ 3(F + T)` (`st6_cube_le_target`) absorbed by `Prec`. -/
def expIntIQ_concl : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (κ ε 𝔠 𝔡 𝔠d : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < 𝔠d → (d : ℝ) * 𝔠d < 1 →
  ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
  ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5I sz s t →
    STConStInd sz 𝔠d s t →
    STExpDriftHiConcl sz (STflowE z) s t → STExpDriftDecayConcl sz (STflowE z) s t →
    STExpWardIConcl' sz (STflowE z) s t →
      STExpIntQConcl' sz (STflowE z) s t

/-! ### The pin and the regime-(i) step (DECISIONS §81 (2); T2239 split section) -/

/-- **Target 10**: the merged primed pin, proved (first conjunct `expIntI_same`, second conjunct target 9). -/
def stExpIntI'_holds : Prop := ∀ d : ℕ, STExpIntI' d

/-- **Target 11**: Step 6, regime (i), with only `LWtermEXP` open: `ST_step6I_of_LW_Int d h (stExpIntI'_holds d)`. -/
def stStep6I_of_LW : Prop := ∀ d : ℕ, LWtermEXP d → STStep6I d

end RBM.Gauss.Sizes.T2257Check

end

/-! ## 3. The statements of the instances T2257 compiles (`d = 3`, regime (i): `szB`, `zB`, `(7/8, 15/16)`) -/

namespace RBM.Gauss.Step6Inst.T2257Check

open MeasureTheory
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst RBM.Path Filter

/-- `inst_expIntI'`: `stExpIntI'_holds 3` at the data of regime (i) (as `inst_expWardI'`, `ExpWardI.lean:469`). -/
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t →
      STExpWardIConcl' sz E s t → STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl' sz E s t)
    szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

/-- `inst_expIntIQ_star_props`: the explicit family is admissible at `szB` (`ilambda ≡ 1`), constants `(121·216, 1/2)`. -/
example : Prop :=
  ∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1)) (1 / 2)
    (RBM.Gauss.Sizes.T2257Check.expIntIQ_star szB n)

/-- `inst_expIntI'_mixed`: the `𝒬` conjunct at `szB`, `zB`, `(7/8, 15/16)` for a **positive** family (`0 < C`, `0 < c`,
admissible eventually, its `𝒬`-Duhamel identity discharged by `st6_duhEqQ_of_pin (stExpDuhamelQ_holds 3)`); the drift and Ward
conclusions stay hypotheses (as `inst_expWardI'_mixed`, `ExpWardI.lean:483`; `inst_expIniI_mixed`, `ExpIniI.lean:1292`). -/
example : Prop :=
  STExpDriftHiConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
  STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
  STExpWardIConcl' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧
      STExpDuhEqQ szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ϑ ∧
      ∀ F : ∀ n, STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n → ℝ, (∀ n p, 0 ≤ F n p) →
        Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
          (fun n p _ => ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (7 / 8) (p.1 : ℝ)
            (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErr szB n (STflowE zB n) (7 / 8) p.2.1.1 b)) p.2.2‖)
          (fun n p _ => F n p) →
        Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16))
          (fun n p _ => ‖STQop (d := 3) (ϑ n) (p.1 : ℝ)
            (fun b => STExpErr szB n (STflowE zB n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
          (fun n p _ => F n p + STExpTarget szB n (p.1 : ℝ))

/-- `inst_stStep6I_of_LW`: regime (i) of Step 6 at the data, with only `LWtermEXP 3` open (supersedes `inst_skeleton6I''`'s
second hypothesis). -/
example : Prop :=
  LWtermEXP 3 → InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

end RBM.Gauss.Step6Inst.T2257Check
