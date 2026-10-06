/-
Release check for T2235 (dispatcher V1, Tue Oct  6 00:20 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68, §73 (5)).
S6-08 (stochastic layer ST-5, Step 6, regimes (iii) and (iv), integrated estimates `6:94-96`): proves the merged pins
`STExpIntIII`, `STExpIntIV` (`RBM3D/Induction/Step6Pins.lean:425`, `:432`, text unchanged) and, with the merged skeleton
`ST_step6_caseIV_of_pins` (`Step6Kit.lean:786`) and the merged `stImproveExpAver_holds`, `stExpDuhamelZ_holds`,
`stExpDriftLo_holds`, the regime pin `STStep6IV` (`Step6Pins.lean:140`), in the new file `RBM3D/Induction/ExpIntEasy.lean`;
deletes three owed registry lines (`RBM3D/Test/Axioms.lean:234`, `:236`, `:237` on `main` b750bf3).
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and last
commit on `main` b750bf3), and the Mathlib lemmas of the route (modules imported below).
Section 2: the statements of the public theorems of `ExpIntEasy.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2235Check` (T2235 proves each, same name, in `RBM.Gauss.Sizes`).
Section 3: the statements of the instances T2235 compiles (`RBM.Gauss.Step6Inst`; merged data: regime (iii) `(sz0, z0, 0, 1/16)`,
regime (iv) `(szG, zB, 5/8, 3/4)`), as `Prop`-valued `example`s (no proof obligation).
Statement and `#check` only: no theorem, no proof, no placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2235-check.lean`.
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ExpEtermsB
import RBM3D.Induction.ExpDuhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.Filter.Finite

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the pins, their conclusion, premises, vocabulary, instances
#check @RBM.Gauss.Sizes.STExpIntIII
#check @RBM.Gauss.Sizes.STExpIntIV
#check @RBM.Gauss.Sizes.STStep6IV
#check @RBM.Gauss.Sizes.STStep6III
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STExpIntConcl
#check @RBM.Gauss.Sizes.STExpDuhEq
#check @RBM.Gauss.Sizes.STExpDriftHiConcl
#check @RBM.Gauss.Sizes.STExpLKLKHiConcl
#check @RBM.Gauss.Sizes.STExpEGtHiConcl
#check @RBM.Gauss.Sizes.STExpDriftLoConcl
#check @RBM.Gauss.Sizes.STExpDrift
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STExpTarget
#check @RBM.Gauss.Sizes.STExpLKLKHi
#check @RBM.Gauss.Sizes.STExpDriftLo
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STImproveExpAver
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_III
#check @RBM.Gauss.Step6Inst.inst_ing6_IV
#check @RBM.Gauss.Step6Inst.inst_expIntIII
#check @RBM.Gauss.Step6Inst.inst_expIntIV
#check @RBM.Gauss.Step6Inst.inst_step6IV

-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): the consumers (§45 O2) and the glue used
#check @RBM.Gauss.Sizes.ST_step6_caseIII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseIV_of_pins
#check @RBM.Gauss.Step6Inst.inst_skeleton6III
#check @RBM.Gauss.Step6Inst.inst_skeleton6IV
#check @RBM.Gauss.Step6Inst.inst_duhEq
#check @RBM.Gauss.Sizes.st6_lam_pos
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_precU_of_forall_seq
#check @RBM.Gauss.Sizes.st6_prec_of_forall_fin
#check @RBM.Gauss.Sizes.st6_flowE_lt_two
#check @RBM.Gauss.Sizes.st6_hi_of_reg5III
#check @RBM.Gauss.Sizes.st6_duhEq_of_pin
#check @RBM.Gauss.Sizes.st6_Bctl_eq
#check @RBM.Gauss.Sizes.st6_xB_III
#check @RBM.Gauss.Sizes.st6_target_nonneg
#check @RBM.Gauss.Sizes.st6_cube_le_target
#check @RBM.Gauss.Sizes.st6_ini_sumNdecay

-- merged proofs of the other pins of the skeletons and of the Duhamel identity, and their merged instance wrappers
-- (`Induction/ExpEtermsA.lean` cd6fcba, `Induction/ExpEtermsB.lean` 6b4fe24, `Induction/ExpAvg.lean` d0d79ce,
-- `Induction/ExpDuhamel.lean` 1fb83da, `Graph/LWPins.lean` 975f4ff)
#check @RBM.Gauss.Sizes.stExpLKLKHi_holds
#check @RBM.Gauss.Sizes.stExpDriftLo_holds
#check @RBM.Gauss.Sizes.stImproveExpAver_holds
#check @RBM.Gauss.Sizes.stExpDuhamelZ_holds
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.Step6Inst.inst_skeleton6III_LK
#check @RBM.Gauss.Step6Inst.inst_skeleton6IV_Lo
#check @RBM.Gauss.Step6Inst.inst_skeleton6IV_avg
#check @RBM.Gauss.Step6Inst.inst_duhEq_holds

-- the kernel estimate `(sum_res_Ndecay)` (`Induction/Step34Pins.lean` fc76526, `Evolution/Prec.lean` fc76526),
-- the kernel (`Induction/GridDuhamelN.lean` 2ebee73, `Kernel/Evolution.lean` ff8d36d, `Evolution/Pins.lean` d9de66f),
-- `Q^{(∅)} = id` (`Induction/Step5Kit.lean` 85e43db)
#check @RBM.Gauss.Sizes.STEKSumNdecay
#check @RBM.Gauss.Sizes.stek_sumNdecay_holds
#check @RBM.Ind.Ugen
#check @RBM.UN
#check @RBM.EKsgn
#check @RBM.zeroModeSet
#check @RBM.Gauss.Sizes.st5_zeroModeSet_empty

-- sizes, `W^{-d}B_{u,0}`, `≺`, `m`, regimes, index sets, glue (`Defs/Sizes.lean` 0a873f1, `Defs/StochDomAt.lean` 9e2b00f,
-- `Defs/Semicircle.lean` fbc9870, `Induction/ScaleFacts.lean` 5d1e6b1, `Induction/Defs.lean` 64bdfd3,
-- `Induction/Step5Pins.lean` d7da51e, `Induction/Step5Kit.lean` 85e43db)
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Path.TimeIcc
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_le_left
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.lemT
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STSigAll
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.st5_prec_mono

-- instance data (`Defs/Sizes.lean` 0a873f1, `Induction/Defs.lean` 64bdfd3, `Induction/Step34Pins.lean` fc76526,
-- `Induction/Step5Pins.lean` d7da51e)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.Step34Inst.sz0_hs0
#check @RBM.Gauss.Step34Inst.sz0_hst
#check @RBM.Gauss.Step34Inst.sz0_ht
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step5Inst.szG
#check @RBM.Gauss.Step5Inst.flow_zG
#check @RBM.Gauss.Step5Inst.szG_reg4
#check @RBM.Gauss.Step5Inst.sz0_reg5III

-- Mathlib (modules imported above): the norm of an interval integral without integrability of the integrand, the
-- substitution `v ↦ 1 - v`, `∫ x^r`, integrability of `x^r` and of a continuous bound, linearity and monotonicity of the
-- interval integral, `rpow` algebra, the sup norm on functions, finitely many eventualities
#check @intervalIntegral.norm_integral_le_of_norm_le
#check @intervalIntegral.integral_comp_sub_left
#check @intervalIntegral.integral_add
#check @intervalIntegral.integral_const_mul
#check @intervalIntegral.integral_mono_on
#check @integral_rpow
#check @intervalIntegral.intervalIntegrable_rpow
#check @ContinuousOn.intervalIntegrable
#check @Real.rpow_le_rpow
#check @Real.mul_rpow
#check @Real.div_rpow
#check @Real.rpow_add
#check @Real.rpow_natCast
#check @Real.rpow_neg
#check @pi_norm_le_iff_of_nonneg
#check @norm_le_pi_norm
#check @Filter.eventually_all

/-! ## 2. Statements of the public theorems of `ExpIntEasy.lean` (closed `Prop`s) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2235Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### 1. Deterministic, one size -/

-- the `u`-integrals of `6:94-96`: `∫_s^u (1-v)^{-r} dv = ((1-u)^{1-r} - (1-s)^{1-r})/(r-1) ≤ (1-u)^{1-r}/(r-1)` for `r > 1`
-- (used at `r = 6/5`, `3/2` (regime (iii)) and `r = 2` (regime (iv))).
def expIntEasy_integral_rpow : Prop :=
  ∀ {s u r : ℝ}, s ≤ u → u < 1 → 1 < r →
    ∫ v in s..u, (1 - v) ^ (-r) ≤ (r - 1)⁻¹ * (1 - u) ^ (1 - r)

-- regime (iii) `ilambda² ≤ 1-u`: the rates against the target,
-- `5 (2B)^{11/5} + 2 (2B)^{5/2} ≤ 64 B²((ilambda²W^d)^{-1/5} + B)` (`B ≤ 2(ilambda²W^d)⁻¹`, so `B^{1/5} ≤ 2^{1/5}(ilambda²W^d)^{-1/5}`;
-- `B^{1/2} ≤ B^{1/5} + B`; worst ratio on the preflight grid `22.4`).  `ilambda ≠ 0`: at `ilambda = 0` Mathlib has `0^{-1/5} = 0`.
def expIntIII_rates_le_target : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ}, u < 1 → sz.lam n ≠ 0 → sz.lam n ^ 2 ≤ 1 - u →
    5 * (2 * sz.Bctl n u) ^ (11 / 5 : ℝ) + 2 * (2 * sz.Bctl n u) ^ (5 / 2 : ℝ) ≤ 64 * STExpTarget sz n u

-- regime (iii), one size: a kernel bound `‖F v‖ ≤ M ((1-v)/(1-u))² (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` on `[s,u]` (`(sum_res_Ndecay)`,
-- `n = 2`) gives `‖∫_s^u F‖ ≤ M (5 (2B_u)^{11/5} + 2 (2B_u)^{5/2})`: `(1-v)B_v ≤ 2(1-u)B_u` (`st6_xB_III` at `(v,u)`) turns the
-- integrand into `(1-u)^{-2}((2(1-u)B_u)^{11/5}(1-v)^{-6/5} + (2(1-u)B_u)^{5/2}(1-v)^{-3/2})`, then `expIntEasy_integral_rpow`
-- (no integrability of `F`: `norm_integral_le_of_norm_le`).
def expIntIII_drift_integral_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {s u M : ℝ} (F : ℝ → ℂ), 0 ≤ M → s ≤ u → u < 1 → sz.lam n ^ 2 ≤ 1 - u →
    (∀ v : ℝ, s ≤ v → v ≤ u →
      ‖F v‖ ≤ M * (((1 - v) / (1 - u)) ^ 2 *
        ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))))) →
      ‖∫ v in s..u, F v‖ ≤ M * (5 * (2 * sz.Bctl n u) ^ (11 / 5 : ℝ) + 2 * (2 * sz.Bctl n u) ^ (5 / 2 : ℝ))

-- regime (iv), the rate against the target (no regime hypothesis): `(N(1-u))^{-3} ≤ B_u³ ≤ T_u` (`st6_Bctl_eq`,
-- `st6_cube_le_target`).
def expIntIV_rate_le_target : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ}, u < 1 →
    ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3 ≤ STExpTarget sz n u

-- regime (iv), one size (no regime hypothesis): `‖F v‖ ≤ M ((1-v)/(1-u))² (1-v)⁻¹ (N(1-v))^{-3} = M N^{-3}(1-u)^{-2}(1-v)^{-2}`
-- on `[s,u]` gives `‖∫_s^u F‖ ≤ M (N(1-u))^{-3}` (`expIntEasy_integral_rpow` at `r = 2`).
def expIntIV_drift_integral_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {s u M : ℝ} (F : ℝ → ℂ), 0 ≤ M → s ≤ u → u < 1 →
    (∀ v : ℝ, s ≤ v → v ≤ u →
      ‖F v‖ ≤ M * (((1 - v) / (1 - u)) ^ 2 * ((1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3))) →
      ‖∫ v in s..u, F v‖ ≤ M * ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3

/-! ### 2. Along the sequences (deterministic: `st6_prec_det_iff`; §64 (4): both sides deterministic) -/

-- `(sum_res_Ndecay)` (`stek_sumNdecay_holds`, `n = 2`, any `σ`, `m = mE E`) applied to the deterministic drift `D_v` along one
-- time sequence `u` (`s ≤ u < 1`): from an eventual bound `‖D_v^σ‖_∞ ≤ N^τ X_v` on `[s_n,u_n]` (every `τ > 0`) the same for
-- `‖𝒰_{v,u}D_v^σ‖_∞` with the factor `((1-v)/(1-u))²`, uniformly in `v ∈ [s_n,u_n]` and `σ` (no lift: `u` is one sequence).
def expIntEasy_kernel_seq : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s u : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ u n) → (∀ n, u n < 1) →
    ∀ X : ℕ → ℝ → ℝ, (∀ n v, s n ≤ v → v ≤ u n → 0 ≤ X n v) →
      (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool,
        ‖(fun b => STExpDrift sz n (STflowE z n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v) →
      ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool,
        ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u n)
            (fun b => STExpDrift sz n (STflowE z n) v σ b)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - v) / (1 - u n)) ^ 2 * X n v)

-- regime (iii): the drift integral `∫_s^u 𝒰_{v,u}D_v dv ≺ T_u`, uniformly in `(u,σ,a)`: per time sequence `u` the kernel bound
-- (`expIntEasy_kernel_seq` with `X_v = (1-v)⁻¹(B_v^{11/5} + B_v^{5/2})` from `STExpDriftHiConcl`), `expIntIII_drift_integral_le`
-- with `M = N^{τ/2}`, `expIntIII_rates_le_target` (`ilambda_n ≠ 0` eventually: `st6_lam_pos`), `64 ≤ N^{τ/2}`; then **one lift**
-- over `u` (`st6_precU_of_forall_seq`, deterministic both sides).
def expIntIII_int_unif : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5III sz s t →
      STExpDriftHiConcl sz (STflowE z) s t →
        Prec sz (U := STIdx2 sz s t)
          (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 v (p.1 : ℝ)
              (fun b => STExpDrift sz n (STflowE z n) v p.2.1 b) p.2.2‖)
          (fun n p _ => STExpTarget sz n (p.1 : ℝ))

-- regime (iv): the same with `X_v = (1-v)⁻¹(N(1-v))^{-3}` from `STExpDriftLoConcl`, `expIntIV_drift_integral_le`,
-- `expIntIV_rate_le_target` (no regime hypothesis, no `ilambda ≠ 0`); one lift over `u`.
def expIntIV_int_unif : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
      STExpDriftLoConcl sz (STflowE z) s t →
        Prec sz (U := STIdx2 sz s t)
          (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 v (p.1 : ℝ)
              (fun b => STExpDrift sz n (STflowE z n) v p.2.1 b) p.2.2‖)
          (fun n p _ => STExpTarget sz n (p.1 : ℝ))

-- `(Eexpint_K-L)` (`6:3-7`) closed, `A = ∅`, all `σ`: the Duhamel identity (`STExpDuhEq` at `A = ∅`, `st5_zeroModeSet_empty`),
-- the initial-term control `F` and the drift-integral bound give `STExpIntConcl ∅ STSigAll` (`‖f_u‖ ≤ N^τ F + N^τ T_u`).
def STExpIntConcl_of_int : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → ∀ {E s t : ℕ → ℝ}, (∀ n, t n < 1) → STExpDuhEq sz E s t →
    Prec sz (U := STIdx2 sz s t)
      (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1 v (p.1 : ℝ)
          (fun b => STExpDrift sz n (E n) v p.2.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) →
    STExpIntConcl sz ∅ STSigAll E s t

-- regime (iii): the conclusion of the pin from the flow data (no stochastic premise of `STIngR6` is used).
def STExpIntIIIConcl_of_flow : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5III sz s t →
      STExpDuhEq sz (STflowE z) s t → STExpDriftHiConcl sz (STflowE z) s t →
        STExpIntConcl sz ∅ STSigAll (STflowE z) s t

-- regime (iv): the same, without the regime (the drift premise carries it).
def STExpIntIVConcl_of_flow : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
      STExpDuhEq sz (STflowE z) s t → STExpDriftLoConcl sz (STflowE z) s t →
        STExpIntConcl sz ∅ STSigAll (STflowE z) s t

-- the pins `STExpIntIII`, `STExpIntIV` (`Step6Pins.lean:425`, `:432`, unchanged), every `d`
def stExpIntIII_holds : Prop := ∀ d : ℕ, STExpIntIII d
def stExpIntIV_holds : Prop := ∀ d : ℕ, STExpIntIV d

-- the regime pin `STStep6IV` (`Step6Pins.lean:140`, unchanged), every `d` (dispatcher's addition, see the ticket): the merged skeleton `ST_step6_caseIV_of_pins`
-- (`Step6Kit.lean:786`) with `stImproveExpAver_holds`, `stExpDuhamelZ_holds`, `stExpDriftLo_holds` (merged) and `stExpIntIV_holds`
def stStep6IV_holds : Prop := ∀ d : ℕ, STStep6IV d

end RBM.Gauss.Sizes.T2235Check

/-! ## 3. Statements of the instances (`RBM.Gauss.Step6Inst`; regime (iii) `(sz0, z0, 0, 1/16)`, regime (iv) `(szG, zB, 5/8, 3/4)`) -/

namespace RBM.Gauss.Step6Inst.T2235Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst

-- statement of `inst_expIntIII_holds` (= `inst_expIntIII (stExpIntIII_holds 3)`, `Step6Pins.lean:634`)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) sz0 z0 sInst tInst

-- statement of `inst_expIntIV_holds` (= `inst_expIntIV (stExpIntIV_holds 3)`, `Step6Pins.lean:638`)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_skeleton6III_Int` (= `fun hLW => inst_skeleton6III_LK hLW (stExpDuhamelZ_holds 3) (stExpIntIII_holds 3)`,
-- `ExpEtermsA.lean:638`; open: `LWtermEXP` (LW-14) only)
example : Prop :=
  LWtermEXP 3 → InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst

-- statement of `inst_skeleton6IV_Int` (= `inst_step6IV (stStep6IV_holds 3)`, `Step6Pins.lean:572`, or
-- `inst_skeleton6IV_Lo (stExpDuhamelZ_holds 3) (stExpIntIV_holds 3)`, `ExpEtermsB.lean:1081`; no pin open)
example : Prop :=
  InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_expIntIII_concl` (`STExpIntIIIConcl_of_flow` at `sz0`, `z0`, `κ = 1/10` (`flow_z0`), `(0, 1/16)`
-- (`sz0_hs0`, `sz0_hst`, `sz0_ht`, `sz0_reg5III`), the Duhamel identity from `inst_duhEq_holds`; the drift bounds stay a hypothesis)
example : Prop :=
  STExpDriftHiConcl sz0 (STflowE z0) sInst tInst → STExpIntConcl sz0 ∅ STSigAll (STflowE z0) sInst tInst

-- statement of `inst_expIntIV_concl` (`STExpIntIVConcl_of_flow` at `szG`, `zB`, `κ = 1/10` (`flow_zG`), `(5/8, 3/4)`
-- (`szB_flow_ht`), Duhamel from `st6_duhEq_of_pin szG (stExpDuhamelZ_holds 3) …`; the drift bound stays a hypothesis)
example : Prop :=
  STExpDriftLoConcl szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4) →
    STExpIntConcl szG ∅ STSigAll (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_expIntEasy_integral_rpow` (`r = 6/5`, `(s,u) = (0, 1/16)`: `0.0650 ≤ 5 (15/16)^{-1/5} = 5.065`)
example : Prop :=
  ∫ v in (0 : ℝ)..(1 / 16), (1 - v) ^ (-(6 / 5 : ℝ)) ≤ (6 / 5 - 1 : ℝ)⁻¹ * (1 - 1 / 16 : ℝ) ^ (1 - 6 / 5 : ℝ)

-- statement of `inst_expIntIII_rates_le_target` (`sz0`, `n = 0` (`L = 4`, `W = 32`, `ilambda = 1/64`), `u = 1/16`:
-- `B = 3.305e-5`, `3.26e-9 ≤ 64 · 7.21e-10 = 4.61e-8`)
example : Prop :=
  5 * (2 * sz0.Bctl 0 (1 / 16)) ^ (11 / 5 : ℝ) + 2 * (2 * sz0.Bctl 0 (1 / 16)) ^ (5 / 2 : ℝ) ≤
    64 * STExpTarget sz0 0 (1 / 16)

-- statement of `inst_expIntIV_rate_le_target` (`szG`, `n = 0` (`N = 4096`), `u = 3/4`: `9.31e-10 ≤ 5.86e-7`)
example : Prop :=
  ((((szG.size 0 : ℕ) : ℝ) * (1 - 3 / 4))⁻¹) ^ 3 ≤ STExpTarget szG 0 (3 / 4)

end RBM.Gauss.Step6Inst.T2235Check

end
