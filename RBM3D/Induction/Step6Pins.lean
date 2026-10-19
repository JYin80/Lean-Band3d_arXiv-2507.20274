/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Graph.LWPins
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopAlgebra

/-!
# The statements of Step 6 of `lem:main_ind`

Paper: arXiv:2507.20274, Step 6 of Theorem 2.24 (`lem:main_ind`), (2.94) `Eq:Gtlp_exp_flow`
((2.76) `Eq:Gtlp_exp` at time `t`), and Section 6.

This file holds the Step-6 vocabulary, the shape `STIngR6`, the target `STExp2U`, the regime
statements `STStep6R`, `STStep6I..IV`, the ingredient
statements with their `*Concl` predicates (section 4), and `STRegSeq`.  The skeletons
`ST_step6_case*_of_pins`, the glue and the bridges are in `Induction/Step6Kit`.
-/


set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Vocabulary, the shape `STIngR6`, the target `STExp2U` and the Step-6 statements -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `f_{u,σ}(a) = 𝔼 𝓛^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u,σ,a}` ((6.1) `Eexpint_K-L`): a deterministic tensor. -/
def STExpErr (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) - STKloop sz n E u σ a

/-- `𝔼 ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}` (`STELKLK`, `(def_ELKLK)`). -/
def STExpELKLK (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STELKLK sz n E u σ a ω ∂(sz.seqP)

/-- `𝔼 ℰ^{G̃,(2)}_{u,σ,a}` (`STEGt`, `(def_EwtG)`; equal to `𝔼 𝓔^{Gc,(2)}` = `𝔼 LWE` by the rotation bridge
`STEGt = LWE` of `Step6Kit.lean`). -/
def STExpEGt (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STEGt sz n E u σ a ω ∂(sz.seqP)

/-- The drift `D_{u,σ} = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}` of the expected hierarchy at `n = 2` (the martingale term `dℰ^M` has
expectation `0`, see the remark after Lemma 6.2). -/
def STExpDrift (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  STExpELKLK sz n E u σ a + STExpEGt sz n E u σ a

/-- The target `(W^{-d}B_{u,0})² ((ilambda² W^d)^{-1/5} + W^{-d}B_{u,0})` of `(Eq:Gtlp_exp_flow)` at
size index `n`, time `u`.  At `lam n = 0` Mathlib has `0 ^ (-1/5) = 0`; `(eq:WO)` gives `0 < lam n` eventually
(`st6_lam_pos`). -/
def STExpTarget (n : ℕ) (u : ℝ) : ℝ :=
  (sz.Bctl n u) ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n u)

/-- **`(Eq:Gtlp_exp_flow)`**, uniformly in `u ∈ [s,t]`, left side deterministic: the shape of
`STExp2` (`Induction/Defs.lean`, `(Eq:Gtlp_exp)`) with the time `u ∈ [s_n, t_n]` inside `Prec` (union over `u` inside
`P`, as the paper's "uniformly in `u`"). -/
def STExp2U (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω ∂(sz.seqP)) -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (p.1 : ℝ)))

/-- **The endpoint `u = t`** of `STExp2U` is `(Eq:Gtlp_exp)` at time `t` (proof of the main results: "Hence the estimate `(Eq:Gtlp_exp)`
holds at time `t`"), the conclusion `STExp2` of `lem:main_ind` (consumer: `Induction/Defs.lean`). -/
theorem STExp2_of_STExp2U {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STExp2U sz E s t) : STExp2 sz E t := by
  exact StochDomAt.precomp_param h
    (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) => ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))

/-- **The loss-free part of Step 2** (`(Gt_bound_flow)`, `(Gt_avgbound_flow)`, uniformly in `u ∈ [s,t]`): the third
conjunct of `STStep2Concl`, `(Eq:Gdecay_w)`, has the loss `((1-s)/(1-u))^{C_d}` relative to the start `s` of the interval, so it does not
restrict to a sub-interval `[s',t']` (the sub-interval needs the smaller loss `((1-s')/(1-u))^{C_d}`); Step 6 does not use it (its decay input is
`(Eq:Gdecay_flow)` without loss, `STGdecayW … 0`, which implies it). -/
def STStep2Core (E s t : ℕ → ℝ) : Prop := STLocalEntryU sz E s t ∧ STAvgU sz E s t

/-- **A Step-6 statement.**  The shape of `STIngR5` (`Induction/Step5Pins.lean`) with the premises that Step 6 does not use removed, so that
every premise restricts to a sub-interval `[s',t'] ⊂ [s,t]`:
`3 ≤ d`, constants first (`κ, ε, 𝔡`, then `𝔠_d ∈ (0, 10^{-2}]`, then `𝔠`, the sizes and `z`), `0 ≤ s < t ≤ lemT z` (`t < 1`
follows, `st5_t_lt_one`), a regime `R`, the hypotheses `(a)`, `(b)` first part and `(d)` (`STExp2`, (2.82) `Eq:Gtlp_exp+IND`) at `s`,
`(con_st_ind)`, the conclusions of Steps 2 (loss-free part `STStep2Core`), 3, 4 on `[s,t]` and of Step 5 in the form `(Eq:Gdecay_flow)`
(`STGdecayW … 0`, no loss).  Differences from `STIngR5`: `STKbound`, `STKward` dropped (theorems of the flow:
`stKbound_of_flow`, `stKward_of_flow`); `STDecayStrong s` and the second conjunct `STDecayStrongU` of `STStep5Concl` dropped
(`(Eq:Gdecay+IND_s<g)`, `(Eq:Gdecay+s<g_flow)`: index `ilambda² ≤ 1-t`, not inherited by sub-intervals; the proof of Step 6 cites neither);
`STStep1Loop` dropped (`(lRB1)` is not used: Step 3 gives the sharper bound; it is not inherited); `STStep2Concl … C_d` replaced by `STStep2Core` and the quantifier
`∀ C_d` dropped (its lossy conjunct `(Eq:Gdecay_w)` does not restrict to a sub-interval and Step 6 does not use it).  For every
statement of this file: the regime is `STReg5*` (`0 ≤ s` explicit, so `ilambda > L` does not reach negative times), `L^d ≤ W^K` is not a
premise (it follows from `Bandwidth` in `STFlow`, `W ≥ N^𝔠`), `0 < lam n` eventually from `WO` in `STFlow` (`st6_lam_pos`), hypotheses on the
sequences are for every `n` and conclusions are `≺` (mollifier properties are eventual), every `≺` is `Prec` at the scale `N`; per time or
uniform in `u` is stated in each docstring. -/
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

/-- The conclusion of Step 6: `(Eq:Gtlp_exp_flow)`, uniformly in `u ∈ [s,t]`. -/
def STStep6Concl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop := STExp2U sz E s t

/-- **Step 6 of `lem:main_ind`** (proof of Step 6) under a regime predicate `R`. -/
def STStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6 d R (fun sz E s t => STStep6Concl sz E s t)

/-- **Step 6, regime (i)** `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²` (proof of Step 6, (6.9)-(6.12)). -/
def STStep6I (d : ℕ) : Prop := STStep6R d STReg5I
/-- **Step 6, regime (ii)** `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²` (proof of Step 6, (6.14); `ST_step6_caseII_of_pins`). -/
def STStep6II (d : ℕ) : Prop := STStep6R d STReg5II
/-- **Step 6, regime (iii)** `1-s ≥ 1-t ≥ ilambda²` (proof of Step 6; `ST_step6_caseIII_of_pins`). -/
def STStep6III (d : ℕ) : Prop := STStep6R d STReg5III
/-- **Step 6, regime (iv)** `1-t ≤ 1-s ≤ ilambda²/L^d` (proof of Step 6; `ST_step6_caseIV_of_pins`). -/
def STStep6IV (d : ℕ) : Prop := STStep6R d STReg5IV
end RBM.Gauss.Sizes

/-! ## 4. The ingredient statements of Step 6

* (b) `lem:improve_exp_aver` per time (`STImproveExpAver`) and uniformly (`STExpAvgU`);
* (c) the expected hierarchy at `n = 2` (`STExpHier`) and its Duhamel forms (`STExpDuhamelZ` plain/`Q^{(A)}`, `STExpDuhamelQ`);
* (d) the expected drift bounds (`STExpLKLKHi`, `STExpDriftDecay`, `STExpDriftLo`; `(eq:ExpLWn=2)` is derived from `LWtermEXP`);
* (e) regime (i), `σ₁ ≠ σ₂`: `STExpWardI`; (f) regime (ii), `σ₁ ≠ σ₂`: `STExpWardII`;
* the integrated estimates (`STExpIntII/III/IV`: Duhamel + kernel + `u`-integral, conditional on the drift and Ward bounds).
Each docstring begins with the paper statement that it formalizes. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ### (b) `lem:improve_exp_aver` -/

/-- **`(res_ELK_n=1)`** at one time sequence `u`: `max_a |𝔼 tr((G_u - M) E_a)| ≺ (W^{-d}B_{u,0})²`, both charges
(`tr((G_u - M)E_a) = 𝓛^{(1)}_{u,+,a} - m(E)`; for `σ = -` the conjugate).  Deterministic left side, per time. -/
def STExpAvgAt (E u : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂(sz.seqP)) - mSigma (E n) p.1‖)
    (fun n _ _ => (sz.Bctl n (u n)) ^ 2)

/-- **`lem:improve_exp_aver`** (Lemma 6.1: "the same as [YY_25, Lemma 5.15] by using `(Gt_avgbound_flow)` and
`(Eq:L-KGt-flow)`"), per time sequence `u ∈ [0, lemT z]`.  Premises, at the time sequence `u`: `(Gt_avgbound_flow)` (`LWAvgLaw`) and
`(Eq:L-KGt-flow)` (`STLK`; its `k = 1` case is the first premise, so `LWAvgLaw` is redundant, kept as in the paper).  Proof outline (as in RBM2D):
Stein for `H_u = √u X` gives `𝔼 tr(H G E_a) = -u Σ_p S_{pa} 𝔼[g_p g_a]`, with `z_u m + 1 = -u m²` the self-consistent equation
`x = u m² S x + y`, `y ≺ (W^{-d}B_{u,0})²` by the second moments of `g_p - m` (`≺ → 𝔼`, envelope `‖G_u‖ ≤ η_u⁻¹ ≤ N^{1-ε}`) and
`‖Θ_{u m²}‖_{∞→∞} ≤ C` (`ekSameRow_holds`, `Evolution/XiPins.lean`; RBM2D has `1 + cShortRow κ (1 + log L)`).
Consumer: `st6_expAvgU_of_pin` (`Step6Kit.lean`), hence the Ward statements `STExpWardI/II` and `STExpDriftLo` and `ST_step6_case{II,IV}_of_pins`.
The statement has `0 ≤ u ≤ lemT z`; no regime, no `Q`, no `L^d ≤ W^K`; it is **per time** (`Prec` over `a` only), at the scale `N`. -/
def STImproveExpAver (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ lemT (z n)) →
        LWAvgLaw sz (STflowE z) u → STLK sz (STflowE z) u → STExpAvgAt sz (STflowE z) u

/-- `(res_ELK_n=1)` uniformly in `u ∈ [s,t]` (the form in which Step 6 integrates over `u`). -/
def STExpAvgU (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) (fun _ : Fin 1 => p.2.1) (fun _ => p.2.2) ω ∂(sz.seqP)) -
      mSigma (E n) p.2.1‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2)

/-! ### (c) the expected hierarchy and its Duhamel forms (deterministic, fixed size) -/

/-- **The expected hierarchy at `n = 2`** ((3.8) `eq_L-Keee` at `n = 2` after taking expectations; the remark after Lemma 6.2: "the leading
error arises from the martingale term, which vanishes after taking the expectation"): for every `|E| < 2`, `σ`, `a`:
`u ↦ f_u(σ)(a)` and `u ↦ D_u(σ)(a)` are continuous on `[0,1)`, and on `(0,1)` `∂_u f_u = Θ^{(2)}_{u,σ} f_u + D_u`.  Continuity
at `u = 0` (`H_u = √u X` is not differentiable there).  Inputs: `Ind.hierarchyN_holds`,
`Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts` (`Gauss/LoopGenerator.lean`) and the initial loop values of the
two-edge loops; after RBM2D's `ExpHierPin`.  Consumer: the proof of `STExpDuhamelZ/Q` (RBM2D's `expDuhamelPin_of_hier`). -/
def STExpHier (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => STExpErr sz n E u σ a) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => STExpDrift sz n E u σ a) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => STExpErr sz n E v σ a)
      (STthetaOp sz n E u σ (fun b => STExpErr sz n E u σ b) a + STExpDrift sz n E u σ a) u

/-- **Duhamel from `s`, plain and zero-mode** ((6.1) `Eexpint_K-L`; (6.14) `iisuwjyys_exp`): for `0 ≤ s ≤ t < 1`,
`σ` and `A ⊂ {1,2}`, `Q^{(A)} f_t = Q^{(A)} 𝒰_{s,t} f_s + ∫_s^t Q^{(A)} 𝒰_{u,t} D_u du` (`Q^{(A)}` commutes with `𝒰`,
`zeroModeSet_Ugen`; `A = ∅` is the plain form, `A = {1,2}` is regime (ii)).  RBM2D's `ExpDuhamelPin` starts at `0` with `f_0 = 0`; the paper integrates from `s` with the initial term `𝒰_{s,t} f_s`.  Consumer:
`st6_duhEq_of_pin` (`Step6Kit.lean`). -/
def STExpDuhamelZ (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A (fun b => STExpErr sz n E t σ b) a =
        zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t (fun b => STExpErr sz n E s σ b)) a +
        ∫ u in s..t, zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (fun b => STExpDrift sz n E u σ b)) a

/-- The source `A_u = 𝒬_u D_u + [𝒬_u, Θ^{(2)}_{u,σ}] f_u - (𝒫 f_u) ∂_u ϑ_u` of the `𝒬`-Duhamel formula `(int_K-L+QE)`
(RBM2D's `qDriftT`; the sign of the last term is `-` as printed in `(int_K-L+QE)`). -/
def STExpQsrc (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    (Fin 2 → Zd d (sz.L n)) → ℂ := fun b =>
  STQop (d := d) ϑ u (fun c => STExpDrift sz n E u σ c) b +
    (STQop (d := d) ϑ u (STthetaOp sz n E u σ (fun c => STExpErr sz n E u σ c)) b -
      STthetaOp sz n E u σ (STQop (d := d) ϑ u (fun c => STExpErr sz n E u σ c)) b) -
    STPsum (d := d) (fun c => STExpErr sz n E u σ c) (b 0) * deriv (fun τ => ϑ τ b) u

/-- **Duhamel with `𝒬`** (`(int_K-L+QE)`): for a mollifier `ϑ` with `STMollifierProps` (`Def:QtPt`), `0 ≤ s ≤ t < 1`:
`𝒬_t f_t = 𝒰_{s,t} 𝒬_s f_s + ∫_s^t 𝒰_{u,t} A_u du`.  RBM2D's `ExpQDuhamelPin`.  Consumer:
`st6_duhEqQ_of_pin` (`Step6Kit.lean`). -/
def STExpDuhamelQ (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    STMollifierProps (d := d) (sz.lam n) C c ϑ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STQop (d := d) ϑ t (fun b => STExpErr sz n E t σ b) a =
        RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t
          (STQop (d := d) ϑ s (fun b => STExpErr sz n E s σ b)) a +
        ∫ u in s..t, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (STExpQsrc sz n E u σ ϑ) a

/-- The Duhamel identities of `STExpDuhamelZ` along the sequences `[s_n, t_n]` (the hypothesis of the integrated statements). -/
def STExpDuhEq (E s t : ℕ → ℝ) : Prop :=
  ∀ n (u : TimeIcc s t n) (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
    zeroModeSet d (sz.L n) A (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a =
      zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (u : ℝ) (fun b => STExpErr sz n (E n) (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b)) a

/-- The `𝒬`-Duhamel identities of `STExpDuhamelQ` along the sequences, for a mollifier family `ϑ`, **eventually in `n`** (the
mollifier exists for `0 < ilambda_n ≤ 𝔡⁻¹`, which holds eventually). -/
def STExpDuhEqQ (E s t : ℕ → ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    STQop (d := d) (ϑ n) (u : ℝ) (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a =
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (u : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ)
        (STExpQsrc sz n (E n) v σ (ϑ n)) a

end RBM.Gauss.Sizes

/-! ### (d) the expected drift bounds, (e) regime (i) Ward terms, (f) regime (ii) Ward decomposition -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The window `ilambda²/L^d ≤ 1-t` (so `1-u ≥ ilambda²/L^d` for every `u ≤ t`): where `lem:LWterm_EXP` and `(eq:Exp(L-K)1)`
apply ((6.3), (6.7)); it contains regimes (i), (ii), (iii) (`st6_hi_of_reg5I/II/III`). -/
def STDriftHi {d : ℕ} (sz : Sizes d) (_s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n

/-- **`(eq:Exp(L-K)1)`**, `1-u ≥ ilambda²/L^d`: `𝔼ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a} ≺ (W^{-d}B_{u,0})^{11/5} Σ_b
B_{u,|a₁-b|} e^{-(|a₁-b|/ℓ_u)^{1/2}} ≲ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}`, uniformly in `u ∈ [s,t]` (the sum over `b` is `≲ (1-u)⁻¹`
by the shell count, absolute constant). -/
def STExpLKLKHiConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))

/-- **`(eq:Exp(L-K)1)`**: the statement `STExpLKLKHi`.  Inputs: `(Eq:Gdecay_flow)` (Step 5, pointwise decay), `(Eq:L-KGt-flow)` at `n = 2` (Step 4,
the maximum bound), `Σ_y S^{(B)}_{xy} = 1`, the `≺ → 𝔼` step (`momentDomAt_of_stochDomAt`, `Gauss/DominationAt.lean`, envelope
`‖G_u‖ ≤ η_u⁻¹ ≤ N^{1-ε}`).  Consumers: `ST_step6_case{II,III}_of_pins`.  Window `STDriftHi`; uniform in `u`
(`Prec` over `TimeIcc`). -/
def STExpLKLKHi (d : ℕ) : Prop := STIngR6 d STDriftHi (fun sz E s t => STExpLKLKHiConcl sz E s t)

/-- **`(eq:ExpLWn=2)`** (Lemma 6.2 `lem:LWterm_EXP`), `1-u ≥ ilambda²/L^d`: `𝔼ℰ^{G̃,(2)}_{u,σ,a} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{5/2}`,
uniformly in `u ∈ [s,t]`; derived from the per-time statement `LWtermEXP` by `st6_EGtHi_of_LW`. -/
def STExpEGtHiConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))

/-- The drift bounds of the window `1-u ≥ ilambda²/L^d` (regimes (i), (ii), (iii)): `(eq:Exp(L-K)1)` and `(eq:ExpLWn=2)`. -/
def STExpDriftHiConcl (E s t : ℕ → ℝ) : Prop := STExpLKLKHiConcl sz E s t ∧ STExpEGtHiConcl sz E s t

/-- **`(eq:Exp(L-K)2)` and `(eq:ExpLWn=2_smalleta)`** ((6.4), (6.6)), `1-u ≤ ilambda²/L^d` (regime (iv)): both `𝔼ℰ^{LK×LK}`
and `𝔼ℰ^{G̃}` are `≺ W^d L^d (N|1-u|)^{-4} = (1-u)⁻¹ (N(1-u))^{-3}`, hence the drift `D_u`, uniformly in `u ∈ [s,t]`. -/
def STExpDriftLoConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpDrift sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - (p.1 : ℝ)))⁻¹) ^ 3)

/-- **`(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`**: the statement `STExpDriftLo`, regime (iv).  Inputs: `(Eq:L-KGt-flow)` at `n = 2, 3` (Step 4), `(eq:bcal_k)`
at `n = 3` (`stKbound_of_flow`), `(res_ELK_n=1)` (`STExpAvgU`, from `STImproveExpAver`, `STAvgU` and `STLKU`),
`(Gt_avgbound_flow)`; `W^d Σ_{x,y} S_{xy} = N`.  Consumer: `ST_step6_caseIV_of_pins`. -/
def STExpDriftLo (d : ℕ) : Prop :=
  STIngR6 d STReg5IV (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t)

/-- **`(deccA0)` for the expected drift** (`Def_decay`, for the deterministic tensor `D_{u,σ}`): for every `ε, D > 0`,
eventually in `n`, `|D_{u,σ}(a)| ≤ W^{-D}` whenever `max_{i,j} |a_i - a_j| ≥ W^ε ℓ_u`, for every `u ∈ [s_n, t_n]`, `σ`
(the hypothesis `STEKDecay` of `(sum_res_1)`, `(sum_res_2_NAL)`, `(sum_res_2)`, needed in regime (i); by `lem_decayLoop`, `STDecayLoopU`,
for the loops of length `2, 3` inside `ℰ`, `ℓ¹` against `L^∞` distances: `STdiamInf`). -/
def STExpDriftDecayConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ σ : Fin 2 → Bool, STEKDecay sz s t (fun n v _ a => STExpDrift sz n (E n) (v : ℝ) σ a)

/-- **`(deccA0)` for `D_u`**: the statement `STExpDriftDecay`, window `1-t ≥ ilambda²/L²` (regime (i)); from `STDecayLoopU` (`Induction/DecayLoopB.lean`)
and the `≺ → 𝔼` step. -/
def STExpDriftDecay (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpDriftDecayConcl sz E s t)

/-- **Regime (i), `σ₁ ≠ σ₂`** (`(eq:EPL-K)`, `(eq:boundELKQ1)`, `(eq:boundcommutator)`), for every
mollifier family `ϑ` with `STMollifierProps` (eventually in `n`: `ilambda_n > 0` only eventually): by Ward's identities
`(WI_calL)`, `(WI_calK)`, `(res_ELK_n=1)` and `(eq:derv_Theta)`:
`[𝒫∘f_u]_{a₁} ϑ_{u,a} = Im 𝔼tr((G_u-M)E_{a₁})/(W^dη_u) ϑ_{u,a} ≺ (W^{-d}B_{u,0})³`,
`‖[𝒫∘f_u] ∂_uϑ_u‖_∞, ‖[𝒬_u, Θ^{(2)}_{u,σ}] f_u‖_∞ ≺ (1-u)⁻¹ (W^{-d}B_{u,0})³`, uniformly in `u ∈ [s,t]`. -/
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

/-- **Regime (i) Ward terms**: the statement `STExpWardI` (window `1-t ≥ ilambda²/L²`: `(ℓ_u^d η_u)⁻¹ ≲ B_{u,0}` needs it). -/
def STExpWardI (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t)

/-- **Regime (ii) Ward decomposition**: for `σ₁ ≠ σ₂`, `f_{u,σ} - Q^{({1,2})} f_{u,σ} = Im[𝔼tr(G̃(E_{a₁}+E_{a₂})) -
N^{-1} 𝔼tr G̃]/(N η_u)` (`tr` the unnormalised trace, `E_a = W^{-d} 1_{[a]}`, `N = (WL)^d`, `η_u = (1-u) Im m`), hence by `(res_ELK_n=1)`, `(N η_u)⁻¹ ≤ (Im m)⁻¹ (N(1-u))⁻¹ ≤
(Im m)⁻¹ W^{-d}B_{u,0}` (bulk `Im m ≥ c(κ)`): `≺ (W^{-d}B_{u,0})³`, uniformly in `u ∈ [s,t]`. -/
def STExpWardIIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q _ => ‖STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 -
      zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
    (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3)

/-- **Regime (ii) Ward decomposition**: the statement `STExpWardII` (`(normQA2)` at `A = {1,2}` is `norm_zeroModeSet_le`,
`‖Q^{(A)}𝒜‖ ≤ 2^{|A|}‖𝒜‖`).  Consumer: `ST_step6_caseII_of_pins`. -/
def STExpWardII (d : ℕ) : Prop :=
  STIngR6 d STReg5II (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t)

end RBM.Gauss.Sizes

/-! ### The integrated estimates (Duhamel + kernel estimate + `u`-integral)

`STExpIntConcl Q P`: if the initial term `Q^{(A)}𝒰_{s,u} f_s` is `≺ F` (a deterministic control), then `Q^{(A)} f_u ≺ F +
(W^{-d}B_{u,0})² ((ilambda² W^d)^{-1/5} + W^{-d}B_{u,0})`, uniformly in `u ∈ [s,t]`: the drift integral
`∫_s^u Q^{(A)} 𝒰_{v,u} D_v dv` is bounded by the kernel estimates (`stek_*_holds`) applied to the deterministic tensors `D_v`,
integrated against the drift bounds.  `P` restricts the sign vectors. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The integrated estimate for `Q^{(A)} f_u`, sign class `P`. -/
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

/-- **Regime (iii)** `1-t ≥ ilambda²`, all `σ`, no `Q` (proof of Step 6: `(sum_res_Ndecay)` with `n = 2`, `∫_s^u ((1-v)/(1-u))² (1-v)⁻¹
(W^{-d}B_{v,0})^{11/5} dv ≲ (1-u)^{-2-1/5} W^{-11d/5}`, no `log`: `x^{-6/5}`, `x^{-3/2}`); conditional on the Duhamel identity and the drift
bounds of the window.  Consumer: `ST_step6_caseIII_of_pins`. -/
def STExpIntIII (d : ℕ) : Prop :=
  STIngR6 d STReg5III (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t)

/-- **Regime (iv)** `1-s ≤ ilambda²/L^d`, all `σ`, no `Q` (proof of Step 6: `(sum_res_Ndecay)`, `n = 2`, `∫_s^u ((1-v)/(1-u))² x_v⁻¹
(N x_v)^{-3} dv ≲ (N x_u)^{-3}`); conditional on the Duhamel identity and `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`.
Consumer: `ST_step6_caseIV_of_pins`. -/
def STExpIntIV (d : ℕ) : Prop :=
  STIngR6 d STReg5IV (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t)

/-- **Regime (ii)** `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`: `Q^{({1,2})}` for `σ₁ ≠ σ₂`, none for `σ₁ = σ₂` (proof of Step 6, (6.14):
`(sum_res_Ndecay_nonzero)` of Lemma 4.17 with `A ⊇ I_diff(σ)`; for `σ₁ = σ₂`, `A = ∅` (`I_diff = ∅`), **not** `(sum_res_2_NAL)`: the
latter, `lem:sum_decay` (Lemma 4.16), needs `1-t ≥ ilambda²/L²`, which with `1-s ≤ ilambda²/L²` forces `s = t`); the kernel loses
nothing, the `u`-integral `∫_s^u x_v⁻¹ dv ≤ log(x_s/x_u) ≤ (d-2) log L`; conditional on the Duhamel
identity and the drift bounds.  Consumer: `ST_step6_caseII_of_pins`. -/
def STExpIntII (d : ℕ) : Prop :=
  STIngR6 d STReg5II (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- **A regime in two pieces**: `[s,t]` is cut at a sequence `m`, `s < m < t`, with `R₁` on `[s,m]` and `R₂` on `[m,t]`. -/
def STRegSeq (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∃ m : ℕ → ℝ, (∀ n, s n < m n) ∧ (∀ n, m n < t n) ∧ R₁ sz s m ∧ R₂ sz m t

end RBM.Gauss.Sizes





