/-
Release check for T2224 (dispatcher V1, Mon Oct  5 22:25 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68, §71).
S6-05 (stochastic layer ST-5, Step 6): proves the merged pins `STExpDuhamelZ` (`(Eexpint_K-L)` `6:3-7`,
`(iisuwjyys_exp)` `6:142-146`; `RBM3D/Induction/Step6Pins.lean:225`) and `STExpDuhamelQ` (`(int_K-L+QE)` `6:109-116`;
`:246`), texts unchanged, by porting RBM2D `Evolution/MLExpDuhamel.lean` (c9a24cf, `expDuhamelPin_of_hier` `:412`,
`expQDuhamelPin_of_hier` `:423`) to `d ≥ 3` and to a start time `s`, in the new file `RBM3D/Induction/ExpDuhamel.lean`;
deletes their two owed registry lines (`RBM3D/Test/Axioms.lean:228-229` on `main` afdb81e).
Section 1: the merged names the port uses (exact namespaces, from the enclosing `namespace … end` blocks; file and
last commit on `main` afdb81e), and the Mathlib lemmas of the route (module imported below).
Section 2: the statements of the public theorems of `ExpDuhamel.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2224Check` (T2224 proves each, same name, in `RBM.Gauss.Sizes`).  RBM2D source in the comment above.
Section 3: the statements of the instances T2224 compiles (`RBM.Gauss.Step6Inst`; merged data `sz0`, `n = 0`:
`L = 4`, `W = 32`, `lam = 1/64`, `E = 1/2`), as `Prop`-valued `example`s (no proof obligation).
Statement and `#check` only: no theorem, no proof, no placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2224-check.lean`.
-/
import RBM3D.Induction.ExpHier
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.GridDuhamelN
import RBM3D.Propagator.Deriv
import RBM3D.Propagator.Props4
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the two pins, their vocabulary, their instances
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STExpDuhamelQ
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STExpDrift
#check @RBM.Gauss.Sizes.STExpQsrc
#check @RBM.Gauss.Sizes.STExpHier
#check @RBM.Gauss.Sizes.STExpDuhEq
#check @RBM.Gauss.Sizes.STExpDuhEqQ
#check @RBM.Gauss.Step6Inst.inst_duhamelZ
#check @RBM.Gauss.Step6Inst.inst_duhamelQ

-- `RBM3D/Induction/ExpHier.lean` (bbeeabb; S6-04 = T2218): the expected hierarchy, proved (public, no `3 ≤ d`)
#check @RBM.Gauss.Sizes.stExpHier_holds
#check @RBM.Gauss.Sizes.expHier_continuousOn_err
#check @RBM.Gauss.Sizes.expHier_continuousOn_drift
#check @RBM.Gauss.Sizes.expHier_hasDerivAt

-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): the consumers (§45 O2)
#check @RBM.Gauss.Sizes.st6_duhEq_of_pin
#check @RBM.Gauss.Sizes.st6_duhEqQ_of_pin
#check @RBM.Gauss.Sizes.st6_mollifier_family
#check @RBM.Gauss.Sizes.ST_step6_caseIII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseIV_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins
#check @RBM.Gauss.Step6Inst.inst_skeleton6I
#check @RBM.Gauss.Step6Inst.inst_skeleton6II
#check @RBM.Gauss.Step6Inst.inst_skeleton6III
#check @RBM.Gauss.Step6Inst.inst_skeleton6IV
#check @RBM.Gauss.Step6Inst.inst_duhEq

-- `RBM3D/Induction/Step34Pins.lean` (fc76526): `𝒫`, `𝒬_t`, the mollifier properties
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STMollifierProps

-- `RBM3D/Induction/QopAlgebra.lean` (6b2494e): `∂_t 𝒬_t`, commutators, the mollifier existence
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_hasDerivAt
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_deriv
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_ThetaN
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sub
#check @RBM.Gauss.Sizes.stMollifierEx_holds

-- `RBM3D/Induction/Step2Defs.lean` (86124dc): `Θ^{(2)}_{u,σ}`, `m(σ)`
#check @RBM.Gauss.Sizes.STthetaOp
#check @RBM.Gauss.Sizes.STmsig

-- `RBM3D/Induction/GridDuhamelN.lean` (2ebee73): the kernel `𝒰` and its laws
#check @RBM.Ind.Ugen
#check @RBM.Ind.GridDuhamelN_Ugen_add
#check @RBM.Ind.GridDuhamelN_Ugen_self
#check @RBM.Ind.GridDuhamelN_Ugen_comp

-- `RBM3D/Induction/ZeroModeCalc.lean` (d1cb5a6): `Q^{(A)}` and `𝒰`, `Θ`
#check @RBM.Ind.zeroModeSet_Ugen
#check @RBM.Ind.Ugen_eq_UN_EKsgn
#check @RBM.zeroModeSet_ThetaN
#check @RBM.zeroModeSetLin
#check @RBM.zeroModeSet_add
#check @RBM.zeroModeSet_sum

-- `RBM3D/Kernel/Evolution.lean` (ff8d36d): one-index kernels, `Θ^{(n)}`, `U^{(n)}`, `Q^{(A)}`
#check @RBM.cycProd
#check @RBM.thetaKer
#check @RBM.uKer
#check @RBM.ThetaN
#check @RBM.UN
#check @RBM.zeroModeSet
#check @RBM.uKer_eq_one_add

-- `RBM3D/Propagator/Basic.lean` (020ec7a), `Propagator/Props4.lean` (892334b), `Propagator/Deriv.lean` (2d0baa3)
#check @RBM.Theta
#check @RBM.mul_Theta_of_three_le
#check @RBM.Theta_sub_Theta
#check @RBM.continuousAt_Theta
#check @RBM.hasDerivAt_Theta_mul_apply

-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `Defs/Params.lean` (c3f3d5d)
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.norm_mul_mSigma_lt_one
#check @RBM.ellT

-- instance data: `RBM3D/Defs/Sizes.lean` (0a873f1), `Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.flow_z0

-- Mathlib (modules imported above): FTC with an integrable derivative, measurability of `deriv`, product rule,
-- integrability of (continuous) × (integrable), finite sums under the integral
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
#check @measurable_deriv
#check @HasDerivAt.fun_finsetProd
#check @IntervalIntegrable.continuousOn_mul
#check @ContinuousOn.intervalIntegrable
#check @intervalIntegral.integral_finsetSum

/-! ## 2. Statements of the public theorems of `ExpDuhamel.lean` (closed `Prop`s) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2224Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### 1. The kernel `𝒰_{v,t,σ}` as a function of its first time (RBM2D §Kernel `MLExpDuhamel.lean:46-156`) -/

-- RBM2D `MLExpDuhamel_hasDerivAt_ukerMat` (`:55`; `ukerMat_eq` `:50`): `uKer μ r t = (1 - r μ S) Θ_{tμ}` is affine
-- in `r`, with derivative `-μ S Θ_{tμ} = -thetaKer μ t` (no hypothesis).
def expDuh_hasDerivAt_uKer : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g : ℝ) (μ : ℂ) (t : ℝ) (x y : Zd d L) (v : ℝ),
    HasDerivAt (fun r : ℝ => RBM.uKer d L g μ r t x y) (-(RBM.thetaKer d L g μ t x y)) v

-- RBM2D `uker_mul_thetaGenMat` (`MLExpVocab.lean:190`, with `S` on the left): the one-slot identity
-- `(1 - vμS) Θ_{tμ} · μ S Θ_{vμ} = μ S Θ_{tμ}` (`S` commutes with `Θ`; `(1 - vμS) Θ_{vμ} = 1`, `mul_Theta_of_three_le`).
def expDuh_uKer_mul_thetaKer : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g : ℝ), 3 ≤ L → ∀ {μ : ℂ} {v t : ℝ}, ‖(v : ℂ) * μ‖ < 1 → ‖(t : ℂ) * μ‖ < 1 →
    RBM.uKer d L g μ v t * RBM.thetaKer d L g μ v = RBM.thetaKer d L g μ t

-- RBM2D `MLExpDuhamel_Uker_theta` (`:96`, with `MLExpDuhamel_sum_update_reindex` `:75`): `𝒰_{v,t} Θ_v` slot by slot.
def expDuh_Ugen_ThetaN : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 → ∀ {k : ℕ} (σ : Fin k → Bool) {v t : ℝ},
    0 ≤ v → v < 1 → 0 ≤ t → t < 1 → ∀ (A : (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L),
      RBM.Ind.Ugen d L g E σ v t (RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) v A) a =
        ∑ b : Fin k → Zd d L, (∑ i : Fin k,
          (∏ j ∈ Finset.univ.erase i,
              RBM.uKer d L g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) j) v t (a j) (b j)) *
            RBM.thetaKer d L g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) i) t (a i) (b i)) * A b

-- RBM2D `MLExpDuhamel_ftc` (`:188`), the derivative part (`hterm`, `hprod`, `hθ'`): `∂_v (𝒰_{v,t} Y_v) = 𝒰_{v,t}(Y' - Θ_v Y_v)`.
def expDuh_hasDerivAt_Ugen : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 → ∀ {k : ℕ} (σ : Fin k → Bool) {u t : ℝ},
    0 ≤ u → u < 1 → 0 ≤ t → t < 1 → ∀ {Y : ℝ → (Fin k → Zd d L) → ℂ} {Y' : (Fin k → Zd d L) → ℂ},
      (∀ b, HasDerivAt (fun v => Y v b) (Y' b) u) → ∀ a : Fin k → Zd d L,
        HasDerivAt (fun v => RBM.Ind.Ugen d L g E σ v t (Y v) a)
          (RBM.Ind.Ugen d L g E σ u t
            (fun b => Y' b - RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) b) a) u

-- RBM2D `MLExpDuhamel_continuousOn_Ugen` (`:174`; `_continuous_ukerMat` `:67`): no hypothesis on the times.
def expDuh_continuousOn_Ugen : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g E : ℝ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ) {S : Set ℝ}
    {Y : ℝ → (Fin k → Zd d L) → ℂ}, (∀ b, ContinuousOn (fun v => Y v b) S) → ∀ a : Fin k → Zd d L,
      ContinuousOn (fun v => RBM.Ind.Ugen d L g E σ v t (Y v) a) S

-- new (RBM2D integrates continuous sources only): `𝒰_{u,t} D_u` is integrable on `[s,t]` when every entry of `D` is
-- (the kernel entries are continuous in `u`; `IntervalIntegrable.continuousOn_mul`, finite sums).
def expDuh_intervalIntegrable_Ugen : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g E : ℝ) {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) {D : ℝ → (Fin k → Zd d L) → ℂ},
    (∀ b, IntervalIntegrable (fun u => D u b) MeasureTheory.volume s t) → ∀ a : Fin k → Zd d L,
      IntervalIntegrable (fun u => RBM.Ind.Ugen d L g E σ u t (D u) a) MeasureTheory.volume s t

/-! ### 2. The Duhamel engine from `s` (RBM2D `MLExpDuhamel_ftc` `:188`, started at `s`, integrable source) -/

-- RBM2D `MLExpDuhamel_ftc` (`:188`) with `Y_0 = 0` replaced by the initial term `𝒰_{s,t} Y_s` and the continuity of `D`
-- replaced by its interval integrability (needed for `STExpDuhamelQ`: `∂_uϑ` is only bounded and measurable).
def expDuh_duhamel : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 → ∀ {k : ℕ} (σ : Fin k → Bool) {s t : ℝ},
    0 ≤ s → s ≤ t → t < 1 → ∀ {Y D : ℝ → (Fin k → Zd d L) → ℂ},
      (∀ b, ContinuousOn (fun u => Y u b) (Set.Icc s t)) →
      (∀ b, IntervalIntegrable (fun u => D u b) MeasureTheory.volume s t) →
      (∀ u ∈ Set.Ioo s t, ∀ b, HasDerivAt (fun v => Y v b)
        (RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) b + D u b) u) →
      ∀ a : Fin k → Zd d L,
        Y t a = RBM.Ind.Ugen d L g E σ s t (Y s) a + ∫ u in s..t, RBM.Ind.Ugen d L g E σ u t (D u) a

-- public copy (reversed) of the private `expHier_ThetaN_two` (`ExpHier.lean:375`): `Θ^{(2)}_{u,σ}` is `ThetaN` at `k = 2`.
def expDuh_STthetaOp_eq_ThetaN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)),
    sz.STthetaOp n E u σ A a = RBM.ThetaN d (sz.L n) (sz.lam n) (fun l => RBM.mSigma E (σ l)) u A a

/-! ### 3. The plain and zero-mode Duhamel formulas (RBM2D `expDuhamelPin_of_hier` `:412`, from `s`) -/

-- RBM2D `expDuhamelPin_of_hier` (`:412`) from `s` (`A = ∅`, without `zeroModeSet`); every `d` (the public
-- `expHier_continuousOn_err`, `_drift`, `expHier_hasDerivAt` carry no `3 ≤ d`).
def expDuh_plain : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      sz.STExpErr n E t σ a =
        RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t (fun b => sz.STExpErr n E s σ b) a +
        ∫ u in s..t, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (fun b => sz.STExpDrift n E u σ b) a

-- new (RBM2D has no `Q^{(A)}` Duhamel): `Q^{(A)}` is a finite linear map, so it passes through `∂_u` entrywise.
def expDuh_zeroModeSet_hasDerivAt : Prop :=
  ∀ {d L : ℕ} [NeZero L] {k : ℕ} (A : Finset (Fin k)) {Y : ℝ → (Fin k → Zd d L) → ℂ}
    {Y' : (Fin k → Zd d L) → ℂ} {u : ℝ}, (∀ b, HasDerivAt (fun v => Y v b) (Y' b) u) →
      ∀ a : Fin k → Zd d L, HasDerivAt (fun v => RBM.zeroModeSet d L A (Y v) a) (RBM.zeroModeSet d L A Y' a) u

-- new: the same for continuity.
def expDuh_zeroModeSet_continuousOn : Prop :=
  ∀ {d L : ℕ} [NeZero L] {k : ℕ} (A : Finset (Fin k)) {Y : ℝ → (Fin k → Zd d L) → ℂ} {S : Set ℝ},
    (∀ b, ContinuousOn (fun v => Y v b) S) → ∀ a : Fin k → Zd d L,
      ContinuousOn (fun v => RBM.zeroModeSet d L A (Y v) a) S

-- the pin `STExpDuhamelZ` (`Step6Pins.lean:225`, unchanged), every `d`
def stExpDuhamelZ_holds : Prop := ∀ d : ℕ, STExpDuhamelZ d

/-! ### 4. The `𝒬`-Duhamel formula (RBM2D `expQDuhamelPin_of_hier` `:423`, abstract mollifier, from `s`) -/

-- RBM2D `MLExpDuhamel_continuousOn_Qop` (`:320`) for an abstract `ϑ` (`DifferentiableOn` on `[0,1)` gives continuity).
def expDuh_continuousOn_Qop : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ {C c : ℝ} {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ},
    STMollifierProps (d := d) (sz.lam n) C c ϑ → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ContinuousOn (fun u => STQop (d := d) ϑ u (fun b => sz.STExpErr n E u σ b) a) (Set.Ico 0 1)

-- RBM2D `MLExpDuhamel_hasDerivAt_Qop` (`:367`) + `qop_source` (`MLExpVocab.lean:229`, sign of T2166a): on `(0,1)`,
-- `∂_u (𝒬_u f_u) = Θ_u (𝒬_u f_u) + A_u` with `A_u = STExpQsrc` (`ϑ` differentiable at interior points of `[0,1)`).
def expDuh_Qop_hasDerivAt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ {C c : ℝ} {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ},
    STMollifierProps (d := d) (sz.lam n) C c ϑ → ∀ (σ : Fin 2 → Bool), ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      ∀ a : Fin 2 → Zd d (sz.L n),
        HasDerivAt (fun v => STQop (d := d) ϑ v (fun b => sz.STExpErr n E v σ b) a)
          (sz.STthetaOp n E u σ (STQop (d := d) ϑ u (fun b => sz.STExpErr n E u σ b)) a +
            sz.STExpQsrc n E u σ ϑ a) u

-- new: `1 ≤ ℓ_t` (`ellT = min (max (g/√|1-t|) 1) L`), so `((ℓ_t^d)⁻¹)^m ≤ 1` in the bounds of `STMollifierProps`.
def expDuh_one_le_ellT : Prop :=
  ∀ (L : ℕ) (g t : ℝ), 1 ≤ L → 1 ≤ RBM.ellT L g t

-- new (RBM2D: `MLExpDuhamel_continuousOn_qDriftT` `:387`, continuity from the closed form of `ϑ̇`): the source is
-- interval integrable on `[s,t] ⊂ [0,1)`; `∂_uϑ` is measurable (`measurable_deriv`) and bounded by
-- `C (1-t)⁻¹` there (fourth conjunct of `STMollifierProps`, `expDuh_one_le_ellT`); the rest is continuous.
def expDuh_intervalIntegrable_Qsrc : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ {C c : ℝ} {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ},
    STMollifierProps (d := d) (sz.lam n) C c ϑ → ∀ (σ : Fin 2 → Bool) {s t : ℝ}, 0 ≤ s → s ≤ t → t < 1 →
      ∀ b : Fin 2 → Zd d (sz.L n),
        IntervalIntegrable (fun u => sz.STExpQsrc n E u σ ϑ b) MeasureTheory.volume s t

-- the pin `STExpDuhamelQ` (`Step6Pins.lean:246`, unchanged), every `d`
def stExpDuhamelQ_holds : Prop := ∀ d : ℕ, STExpDuhamelQ d

end RBM.Gauss.Sizes.T2224Check

/-! ## 3. Statements of the instances (`RBM.Gauss.Step6Inst`, data `sz0`, `n = 0`, `E = 1/2`) -/

namespace RBM.Gauss.Step6Inst.T2224Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

-- statement of `inst_duhamelZ_holds` (= `inst_duhamelZ (stExpDuhamelZ_holds 3)`; `A = {1,2}`, `σ = (+,-)`, `[1/4, 1/2]`)
example : Prop :=
  RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
      (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] =
    RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
      (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2)
        (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] +
    ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
      (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] u (1 / 2)
        (fun b => sz0.STExpDrift 0 (1 / 2) u ![true, false] b)) ![0, Pi.single 0 1]

-- statement of `inst_duhamelQ_holds` (= `inst_duhamelQ (stExpDuhamelQ_holds 3)`; the mollifier of `stMollifierEx_holds`)
example : Prop :=
  ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) C c ϑ ∧
    STQop (d := 3) ϑ (1 / 2) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] =
      RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2)
        (STQop (d := 3) ϑ (1 / 4) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] +
      ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] u (1 / 2)
        (sz0.STExpQsrc 0 (1 / 2) u ![true, false] ϑ) ![0, Pi.single 0 1]

-- statement of `inst_duhEq_holds` (= `inst_duhEq (stExpDuhamelZ_holds 3)`, `Step6Kit.lean:1200`; `[0, 1/16]` along `z0`)
example : Prop := STExpDuhEq sz0 (STflowE z0) sInst tInst

-- statement of `inst_expDuh_plain` (`expDuh_plain` from `s = 0`, the endpoint where only continuity is known;
-- `σ = (+,+)`, `t = 1/2`)
example : Prop :=
  sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, true] ![0, Pi.single 0 1] =
    RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, true] 0 (1 / 2)
      (fun b => sz0.STExpErr 0 (1 / 2) 0 ![true, true] b) ![0, Pi.single 0 1] +
    ∫ u in (0 : ℝ)..(1 / 2 : ℝ), RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, true] u (1 / 2)
      (fun b => sz0.STExpDrift 0 (1 / 2) u ![true, true] b) ![0, Pi.single 0 1]

-- statement of `inst_expDuh_single` (`stExpDuhamelZ_holds 3` at `A = {2}` (`Fin` index `1`), `σ = (-,+)`, `[0, 1/2]`)
example : Prop :=
  RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2))
      (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![false, true] b) ![0, Pi.single 0 1] =
    RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2))
      (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![false, true] 0 (1 / 2)
        (fun b => sz0.STExpErr 0 (1 / 2) 0 ![false, true] b)) ![0, Pi.single 0 1] +
    ∫ u in (0 : ℝ)..(1 / 2 : ℝ), RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2))
      (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![false, true] u (1 / 2)
        (fun b => sz0.STExpDrift 0 (1 / 2) u ![false, true] b)) ![0, Pi.single 0 1]

end RBM.Gauss.Step6Inst.T2224Check

end
