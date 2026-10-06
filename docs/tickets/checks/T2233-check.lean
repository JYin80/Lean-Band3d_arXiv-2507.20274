/-
Release check for T2233 (dispatcher V1, Mon Oct  5 23:58 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68, §73 (1)).
S6-12b (stochastic layer ST-5, Step 6, regime (ii), integrated estimate `6:142-147`): proves the merged pin `STExpIntII`
(`RBM3D/Induction/Step6Pins.lean:441`, text unchanged) in the new file `RBM3D/Induction/ExpIntII.lean`; deletes its one owed
registry line (`RBM3D/Test/Axioms.lean:235` on `main` e1fec21).  The Ward decomposition `STExpWardII` (`:376`) is S6-12a = T2229
(`Induction/ExpWardII.lean`), not this one.
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and last
commit on `main` e1fec21), and the Mathlib lemmas of the route (modules imported below).
Section 2: the statements of the public theorems of `ExpIntII.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2233Check` (T2233 proves each, same name, in `RBM.Gauss.Sizes`).
Section 3: the statements of the instances T2233 compiles (`RBM.Gauss.Step6Inst`; merged data `szB` (`L = 4`, `W_n = n + 4`,
`lam = 1`), `zB`, regime (ii) times `(15/16, 31/32)`), as `Prop`-valued `example`s (no proof obligation).
Statement and `#check` only: no theorem, no proof, no placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2233-check.lean`.
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpDuhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the pin, its conclusion, its premises, its vocabulary, its instances
#check @RBM.Gauss.Sizes.STExpIntII
#check @RBM.Gauss.Sizes.STExpIntConcl
#check @RBM.Gauss.Sizes.STExpDuhEq
#check @RBM.Gauss.Sizes.STExpDriftHiConcl
#check @RBM.Gauss.Sizes.STExpLKLKHiConcl
#check @RBM.Gauss.Sizes.STExpEGtHiConcl
#check @RBM.Gauss.Sizes.STDriftHi
#check @RBM.Gauss.Sizes.STExpDrift
#check @RBM.Gauss.Sizes.STExpELKLK
#check @RBM.Gauss.Sizes.STExpEGt
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STExpTarget
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STStep6II
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Sizes.STExpWardII
#check @RBM.Gauss.Sizes.STExpLKLKHi
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STImproveExpAver
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_II
#check @RBM.Gauss.Step6Inst.inst_expIntII

-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): the consumer (§45 O2) and the glue used
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins
#check @RBM.Gauss.Step6Inst.inst_skeleton6II
#check @RBM.Gauss.Step6Inst.inst_ini_nonzero
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_precU_of_forall_seq
#check @RBM.Gauss.Sizes.st6_prec_of_forall_fin
#check @RBM.Gauss.Sizes.st6_ini_nonzero
#check @RBM.Gauss.Sizes.st6_Idiff_same
#check @RBM.Gauss.Sizes.st6_hi_of_reg5II
#check @RBM.Gauss.Sizes.st6_duhEq_of_pin
#check @RBM.Gauss.Sizes.st6_flowE_lt_two
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.st6_Bctl_eq
#check @RBM.Gauss.Sizes.st6_target_nonneg
#check @RBM.Gauss.Sizes.st6_target_mono

-- merged proofs of the other premises of `inst_skeleton6II` (instance target 2) and of the Duhamel identity
#check @RBM.Gauss.Sizes.stExpLKLKHi_holds
#check @RBM.Gauss.Sizes.stImproveExpAver_holds
#check @RBM.Gauss.Sizes.stExpDuhamelZ_holds
#check @RBM.Gauss.Sizes.LWtermEXP

-- the kernel estimate `(sum_res_Ndecay_nonzero)` (`Induction/Step34Pins.lean` fc76526, `Evolution/Prec.lean` fc76526),
-- the kernel (`Induction/GridDuhamelN.lean` 2ebee73, `Kernel/Evolution.lean` ff8d36d, `Evolution/Pins.lean` d9de66f),
-- `Q^{(A)}` (`Kernel/Evolution.lean`, `Induction/ZeroModeCalc.lean` d1cb5a6, `Induction/Step5Kit.lean` 85e43db)
#check @RBM.Gauss.Sizes.STEKNonzero
#check @RBM.Gauss.Sizes.stek_nonzero_holds
#check @RBM.Ind.Ugen
#check @RBM.UN
#check @RBM.EKsgn
#check @RBM.zeroModeSet
#check @RBM.norm_zeroModeSet_le
#check @RBM.Ind.zeroModeSet_Ugen
#check @RBM.Gauss.Sizes.st5_zeroModeSet_empty

-- sizes, `W^{-d}B_{u,0}`, `≺`, `m`, regime, index sets, glue (`Defs/Sizes.lean` 0a873f1, `Defs/Params.lean` c3f3d5d,
-- `Defs/StochDomAt.lean` 9e2b00f, `Defs/Semicircle.lean` fbc9870, `Induction/ScaleFacts.lean` 5d1e6b1,
-- `Induction/Step5Pins.lean` d7da51e, `Induction/Step5Kit.lean` 85e43db)
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Bparam
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
#check @RBM.mSigma
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STSigSame
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.st5_prec_mono

-- instance data (`Induction/Step34Pins.lean` fc76526, `Induction/Step5Pins.lean` d7da51e)
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step5Inst.szB_reg5II

-- Mathlib (modules imported above): the norm of an interval integral without integrability of the integrand, the
-- substitution `v ↦ 1 - v`, `∫ x⁻¹ = log`, integrability of a continuous bound, `log x ≤ x^ε/ε`, `rpow` algebra
#check @intervalIntegral.norm_integral_le_of_norm_le
#check @intervalIntegral.integral_comp_sub_left
#check @integral_inv
#check @ContinuousOn.intervalIntegrable
#check @Real.log_le_rpow_div
#check @Real.rpow_le_rpow
#check @Real.mul_rpow
#check @Real.inv_rpow
#check @Real.rpow_add

/-! ## 2. Statements of the public theorems of `ExpIntII.lean` (closed `Prop`s) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2233Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### 1. Deterministic, one size -/

-- `6:146`: the `u`-integral of regime (ii): `∫_s^u (1-v)⁻¹ dv = log((1-s)/(1-u)) ≤ log L^{d-2}` (`1-s ≤ g²/L²`,
-- `1-u ≥ g²/L^d`; `g ≠ 0` follows from `1-s ≥ 1-u > 0`).
def expIntII_log_ratio : Prop :=
  ∀ {d L : ℕ} {g s u : ℝ}, 2 ≤ d → 1 ≤ L → s ≤ u → u < 1 →
    1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → g ^ 2 / (L : ℝ) ^ d ≤ 1 - u →
      ∫ v in s..u, (1 - v)⁻¹ ≤ ((d : ℝ) - 2) * Real.log (L : ℝ)

-- the window `1-u ≥ ilambda²/L^d`: `W^{-d}B_{u,0} = W^{-d}((ilambda² + 1-u)⁻¹ + (L^d(1-u))⁻¹) ≤ 2 (ilambda² W^d)⁻¹`.
def expIntII_Bctl_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ}, u < 1 → sz.lam n ≠ 0 →
    sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u →
      sz.Bctl n u ≤ 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹

-- the drift rates of `(eq:Exp(L-K)1)`, `(eq:ExpLWn=2)` against the target: `B^{11/5} + B^{5/2} ≤ 3 B²((ilambda²W^d)^{-1/5} + B)`
-- (`B^{1/5} ≤ 2^{1/5}(ilambda²W^d)^{-1/5}`; `B^{1/2} ≤ B^{1/5}` if `B ≤ 1`, `≤ B` otherwise; `2·2^{1/5} ≤ 3`).
def expIntII_rates_le_target : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ}, u < 1 → sz.lam n ≠ 0 →
    sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u →
      sz.Bctl n u ^ (11 / 5 : ℝ) + sz.Bctl n u ^ (5 / 2 : ℝ) ≤ 3 * STExpTarget sz n u

-- one size: a kernel bound `‖Q^{(A)} 𝒰_{v,u} D_v‖_∞ ≤ M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})` on `[s,u]` gives the drift integral
-- `≤ M · 3 T_u · (d-2) log L` (`B_v ≤ B_u`; no integrability of the integrand: `norm_integral_le_of_norm_le`).
def expIntII_drift_integral_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E s u M : ℝ}, 2 ≤ d → 0 ≤ M → s ≤ u → u < 1 →
    1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u →
    ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)),
      (∀ v : ℝ, s ≤ v → v ≤ u →
        ‖RBM.zeroModeSet d (sz.L n) A
            (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b))‖ ≤
          M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) →
      ∀ a : Fin 2 → Zd d (sz.L n),
        ‖∫ v in s..u, RBM.zeroModeSet d (sz.L n) A
            (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b)) a‖ ≤
          M * (3 * STExpTarget sz n u * (((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ)))

/-! ### 2. Along the sequence (deterministic: `st6_prec_det_iff`; §64 (4): both sides deterministic) -/

-- `log L ≺ 1`: for every `C` and `τ > 0`, eventually `C log L_n ≤ N^τ` (`L ≤ N`, `log N ≤ N^{τ/2}/(τ/2)`).
def expIntII_log_eventually : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → 1 ≤ d → ∀ (C : ℝ) {τ : ℝ}, 0 < τ →
    ∀ᶠ n in atTop, C * Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ

-- `(sum_res_Ndecay_nonzero)` (`stek_nonzero_holds`, constant absorbed) applied to the deterministic drift `D_v` with the bound
-- `(eq:Exp(L-K)1)` + `(eq:ExpLWn=2)` (`STExpDriftHiConcl`), uniformly in `s_n ≤ v ≤ u ≤ t_n` (per time sequence `u`, then the
-- failing-sequence argument of `st6_precU_of_forall_seq`: deterministic both sides), window `1 - ilambda²/L² ≤ s`, `A ⊇ I_diff(σ)`.
def expIntII_kernel_unif : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
      (∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) →
      STExpDriftHiConcl sz (STflowE z) s t →
      ∀ (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop),
        (∀ σ, P σ → ∀ i, σ i ≠ σ (finRotate 2 i) → i ∈ A) →
        ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
          ∀ σ : Fin 2 → Bool, P σ →
            ‖RBM.zeroModeSet d (sz.L n) A
                (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u : ℝ)
                  (fun b => STExpDrift sz n (STflowE z n) v σ b))‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ τ *
                ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))

-- `(iisuwjyys_exp)` (`6:142-146`) closed: Duhamel (`STExpDuhEq` at `A`), the uniform kernel bound, the one-size integral bound
-- and `log L ≺ 1` give `STExpIntConcl A P` (regime (ii), any `A`, `P`).
def STExpIntConcl_of_kernel : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → 2 ≤ d → ∀ {E s t : ℕ → ℝ},
    (∀ n, s n < t n) → (∀ n, t n < 1) → STReg5II sz s t → STExpDuhEq sz E s t →
    ∀ (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop),
      (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
        ∀ σ : Fin 2 → Bool, P σ →
          ‖RBM.zeroModeSet d (sz.L n) A
              (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b))‖ ≤
            ((sz.size n : ℕ) : ℝ) ^ τ *
              ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) →
      STExpIntConcl sz A P E s t

-- the conclusion of the pin from the flow data alone (no stochastic premise of `STIngR6` is used): `A = {1,2}` for `σ₁ ≠ σ₂`,
-- `A = ∅` for `σ₁ = σ₂` (`st6_Idiff_same`).
def STExpIntIIConcl_of_flow : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STReg5II sz s t →
      STExpDuhEq sz (STflowE z) s t → STExpDriftHiConcl sz (STflowE z) s t →
        STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed (STflowE z) s t ∧
          STExpIntConcl sz ∅ STSigSame (STflowE z) s t

-- the pin `STExpIntII` (`Step6Pins.lean:441`, unchanged), every `d`
def stExpIntII_holds : Prop := ∀ d : ℕ, STExpIntII d

end RBM.Gauss.Sizes.T2233Check

/-! ## 3. Statements of the instances (`RBM.Gauss.Step6Inst`; `szB`, `zB`, regime (ii) at `(15/16, 31/32)`) -/

namespace RBM.Gauss.Step6Inst.T2233Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

-- statement of `inst_expIntII_holds` (= `inst_expIntII (stExpIntII_holds 3)`, `Step6Pins.lean:629`)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t)
    szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_skeleton6II_Int` (= `inst_skeleton6II` (`Step6Kit.lean:1116`) with the merged `stExpLKLKHi_holds 3`,
-- `stImproveExpAver_holds 3`, `stExpDuhamelZ_holds 3` and `stExpIntII_holds 3`; open: `LWtermEXP` (LW-14), `STExpWardII` (T2229))
example : Prop :=
  LWtermEXP 3 → STExpWardII 3 →
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_expIntII_concl` (`STExpIntIIConcl_of_flow` at `szB`, `zB`, `κ = 1/10` (`flow_zB`), `(15/16, 31/32)`
-- (`szB_reg5II`), the Duhamel identity discharged with `st6_duhEq_of_pin (stExpDuhamelZ_holds 3)`; the drift bounds stay a hypothesis)
example : Prop :=
  STExpDriftHiConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
    STExpIntConcl szB (Finset.univ : Finset (Fin 2)) STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ∧
      STExpIntConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_expIntII_log_ratio` (`expIntII_log_ratio` at `d = 3`, `L = 4`, `g = 1`, `(s,u) = (15/16, 31/32)`:
-- `log 2 = 0.693 ≤ log 4 = 1.386`; `1 - s = 1/16 = g²/L²` is the boundary)
example : Prop :=
  ∫ v in (15 / 16 : ℝ)..(31 / 32), (1 - v)⁻¹ ≤ (((3 : ℕ) : ℝ) - 2) * Real.log ((szB.L 0 : ℕ) : ℝ)

-- statement of `inst_expIntII_Bctl_le` (`szB`, `n = 0`, `u = 31/32`: `B = (32/33 + 1/2)/64 = 0.0230 ≤ 2/64 = 0.03125`)
example : Prop :=
  szB.Bctl 0 (31 / 32) ≤ 2 * (szB.lam 0 ^ 2 * ((szB.W 0 : ℕ) : ℝ) ^ 3)⁻¹

-- statement of `inst_expIntII_rates_le_target` (`szB`, `n = 0`, `u = 31/32`: `3.28e-4 ≤ 3 · 2.42e-4`)
example : Prop :=
  szB.Bctl 0 (31 / 32) ^ (11 / 5 : ℝ) + szB.Bctl 0 (31 / 32) ^ (5 / 2 : ℝ) ≤ 3 * STExpTarget szB 0 (31 / 32)

end RBM.Gauss.Step6Inst.T2233Check

end
