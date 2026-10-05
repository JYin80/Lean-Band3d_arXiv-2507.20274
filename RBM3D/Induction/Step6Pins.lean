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
# S6-01 (T2204): the Step-6 pins of `lem:main_ind` (ST-5)

Moved verbatim from the compiled design probe of T2191 (branch `t/T2191`, commit `96c6b4c`,
`RBM3D/Probe/T2191Pins.lean`).  Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex`
(`1_2:line`: `lem:main_ind` `1256-1330`, Step 6 `1390-1396`) and `paper/tex/6_Step6_two_loop.tex`
(`6:line`).

This file holds the Step-6 vocabulary, the shape `STIngR6`, the target `STExp2U`, the regime pins
`STStep6R`, `STStep6I..IV`, the general pin `STStep6`, the twenty ingredient pins with their
`*Concl` predicates (probe section 4), `STRegSeq`, and the compiled nonempty instances (probe
section 8) whose proofs use nothing of the skeletons.  The skeletons `ST_step6_case*_of_pins`, the
glue (`ST_step6_compose`, ...), the bridges and `STGenericPos` are `Induction/Step6Kit` (S6-02).
The registry class of each pin (DECISIONS sections 16, 20) is in its docstring or in
`RBM3D/Test/Axioms.lean`.
-/


set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Vocabulary, the shape `STIngR6`, the target `STExp2U` and the Step-6 pins -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `f_{u,σ}(a) = 𝔼 𝓛^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u,σ,a}` (`Eexpint_K-L`, `6:3-7`): a deterministic tensor. -/
def STExpErr (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) - STKloop sz n E u σ a

/-- `𝔼 ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}` (merged `STELKLK`, `(def_ELKLK)`). -/
def STExpELKLK (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STELKLK sz n E u σ a ω ∂(sz.seqP)

/-- `𝔼 ℰ^{G̃,(2)}_{u,σ,a}` (merged `STEGt`, `(def_EwtG)`; equal to `𝔼 𝓔^{Gc,(2)}` = `𝔼 LWE` by the rotation bridge
`STEGt = LWE` of T2080, §7 of this file). -/
def STExpEGt (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STEGt sz n E u σ a ω ∂(sz.seqP)

/-- The drift `D_{u,σ} = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}` of the expected hierarchy at `n = 2` (the martingale term `dℰ^M` has
expectation `0`, `6:90`). -/
def STExpDrift (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  STExpELKLK sz n E u σ a + STExpEGt sz n E u σ a

/-- The target `(W^{-d}B_{u,0})² ((ilambda² W^d)^{-1/5} + W^{-d}B_{u,0})` of `(Eq:Gtlp_exp_flow)` (`1_2:1390-1396`) at
size index `n`, time `u`.  At `lam n = 0` Mathlib has `0 ^ (-1/5) = 0`; `(eq:WO)` gives `0 < lam n` eventually
(`st6_lam_pos`). -/
def STExpTarget (n : ℕ) (u : ℝ) : ℝ :=
  (sz.Bctl n u) ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n u)

/-- **`(Eq:Gtlp_exp_flow)`** (`1_2:1390-1396`), uniformly in `u ∈ [s,t]`, left side deterministic: the shape of the merged
`STExp2` (`Induction/Defs.lean:159`, `(Eq:Gtlp_exp)`) with the time `u ∈ [s_n, t_n]` inside `Prec` (union over `u` inside
`P`, as the paper's "uniformly in `u`", `1_2:1400`).  Registry class: **owed** (S6-13, through `STStep6`). -/
def STExp2U (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω ∂(sz.seqP)) -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (p.1 : ℝ)))

/-- The statement `STExp2U` written with `STExpErr` and `STExpTarget`. -/
theorem STExp2U_iff (E s t : ℕ → ℝ) :
    STExp2U sz E s t ↔
      Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p _ => ‖STExpErr sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
        (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := Iff.rfl

/-- **The endpoint `u = t`** of `STExp2U` is `(Eq:Gtlp_exp)` at time `t` (`1_2:1396`: "Hence the estimate `(Eq:Gtlp_exp)`
holds at time `t`"), the conclusion `STExp2` of `lem:main_ind` (consumer: `Induction/Defs.lean:304`). -/
theorem STExp2_of_STExp2U {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STExp2U sz E s t) : STExp2 sz E t := by
  exact StochDomAt.precomp_param h
    (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) => ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))

/-- **The loss-free part of Step 2** (`(Gt_bound_flow)`, `(Gt_avgbound_flow)` of `1_2:1342-1344`, uniformly in `u ∈ [s,t]`): the third
conjunct of `STStep2Concl`, `(Eq:Gdecay_w)`, has the loss `((1-s)/(1-u))^{C_d}` relative to the start `s` of the interval, so it does not
restrict to a sub-interval `[s',t']` (the sub-interval needs the smaller loss `((1-s')/(1-u))^{C_d}`); Step 6 does not use it (its decay input is
`(Eq:Gdecay_flow)` without loss, `STGdecayW … 0`, which implies it: `st6_GdecayW_of_zero`).  Structural. -/
def STStep2Core (E s t : ℕ → ℝ) : Prop := STLocalEntryU sz E s t ∧ STAvgU sz E s t

/-- **A Step-6 pin.**  The shape of `STIngR5` (`Induction/Step5Pins.lean:82`) with the premises that Step 6 does not use removed, so that
every premise restricts to a sub-interval `[s',t'] ⊂ [s,t]` (the gluing by intermediate times of `STStep6`: `ST_step6_compose`):
`3 ≤ d`, constants first (`κ, ε, 𝔡`, then `𝔠_d ∈ (0, 10^{-2}]`, then `𝔠`, the sizes and `z`), `0 ≤ s < t ≤ lemT z` (§29 (1); `t < 1`
follows, `st5_t_lt_one`), a regime `R`, the hypotheses `(a)`, `(b)` first part and `(d)` (`STExp2`, `(Eq:Gtlp_exp+IND)` `1_2:1281`) at `s`,
`(con_st_ind)`, the conclusions of Steps 2 (loss-free part `STStep2Core`), 3, 4 on `[s,t]` and of Step 5 in the form `(Eq:Gdecay_flow)`
(`STGdecayW … 0`, no loss).  Differences from `STIngR5` (report (d), T2191b): `STKbound`, `STKward` dropped (theorems of the flow:
`stKbound_of_flow`, `stKward_of_flow`); `STDecayStrong s` and the second conjunct `STDecayStrongU` of `STStep5Concl` dropped
(`(Eq:Gdecay+IND_s<g)`, `(Eq:Gdecay+s<g_flow)`: index `ilambda² ≤ 1-t`, not inherited by sub-intervals; `6:93-152` cites neither);
`STStep1Loop` dropped (`(lRB1)`: superseded by Step 3, not inherited); `STStep2Concl … C_d` replaced by `STStep2Core` and the quantifier
`∀ C_d` dropped (its lossy conjunct `(Eq:Gdecay_w)` does not restrict to a sub-interval and Step 6 does not use it).  §29 (2)-(7) for every
pin of this file: the regime is the merged `STReg5*` (`0 ≤ s` explicit, so `ilambda > L` does not reach negative times), `L^d ≤ W^K` is not a
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

/-- **Step 6 of `lem:main_ind`** (`1_2:1390-1396`; proof `6:93-152`) under a regime predicate `R`. -/
def STStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6 d R (fun sz E s t => STStep6Concl sz E s t)

/-- **Step 6, regime (i)** `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²` (`6:97`, `6:103-132`).  Registry class: **owed**
(follows from the ingredient pins by `ST_step6_caseI_of_pins`, S6-02; the ingredients are proved in S6-09, S6-10, S6-11). -/
def STStep6I (d : ℕ) : Prop := STStep6R d STReg5I
/-- **Step 6, regime (ii)** `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²` (`6:97`, `6:136-147`).  Registry class: **owed**
(`ST_step6_caseII_of_pins`, S6-02; ingredients S6-12). -/
def STStep6II (d : ℕ) : Prop := STStep6R d STReg5II
/-- **Step 6, regime (iii)** `1-s ≥ 1-t ≥ ilambda²` (`6:94-96`).  Registry class: **owed** (`ST_step6_caseIII_of_pins`, S6-02;
ingredient S6-08). -/
def STStep6III (d : ℕ) : Prop := STStep6R d STReg5III
/-- **Step 6, regime (iv)** `1-t ≤ 1-s ≤ ilambda²/L^d` (`6:94-96`).  Registry class: **owed**
(`ST_step6_caseIV_of_pins`, S6-02; ingredients S6-07, S6-08). -/
def STStep6IV (d : ℕ) : Prop := STStep6R d STReg5IV
/-- **Step 6, general** `0 ≤ s < t ≤ lemT z`: the four regimes glued by intermediate times (as `STStep5`,
`Induction/Step5Pins.lean:461`; `6:93-97` states the four regimes separately).  An assembly pin.  One intermediate time is compiled
(`ST_step6_compose`, §7b); the general case needs the split of `ℕ` into the patterns of nonempty stages.  Registry class: **owed**
(S6-13). -/
def STStep6 (d : ℕ) : Prop := STStep6R d STAny

/-- The general pin implies each regime (`STAny` is `True`): the regime pins are consequences of `STStep6`; the converse (the four regimes glued by
intermediate times, `6:93-97`) is the assembly ticket S6-13. -/
theorem ST_step6R_of_any {d : ℕ} (h : STStep6 d) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    STStep6R d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hc', H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨c, hc, hc', fun 𝔠 sz z hflow s t hs0 hst htT _ => H 𝔠 sz z hflow s t hs0 hst htT trivial⟩

end RBM.Gauss.Sizes

/-! ## 4. The ingredient pins of Step 6

* (b) `lem:improve_exp_aver` per time (`STImproveExpAver`) and uniformly (`STExpAvgU`);
* (c) the expected hierarchy at `n = 2` (`STExpHier`) and its Duhamel forms (`STExpDuhamelZ` plain/`Q^{(A)}`, `STExpDuhamelQ`);
* (d) the expected drift bounds (`STExpLKLKHi`, `STExpDriftDecay`, `STExpDriftLo`; `(eq:ExpLWn=2)` is compiled from `LWtermEXP`);
* (e) regime (i), `σ₁ ≠ σ₂`: `STExpWardI`; (f) regime (ii), `σ₁ ≠ σ₂`: `STExpWardII`;
* the integrated estimates (`STExpIntI/II/III/IV`: Duhamel + kernel + `u`-integral, conditional on the drift and Ward bounds)
  and the initial term of regime (i) (`STExpIniI`).
The first column of every docstring is the paper statement, the last line the registry class (DECISIONS §16, §20). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ### (b) `lem:improve_exp_aver` -/

/-- **`(res_ELK_n=1)`** (`6:14-16`) at one time sequence `u`: `max_a |𝔼 tr((G_u - M) E_a)| ≺ (W^{-d}B_{u,0})²`, both charges
(`tr((G_u - M)E_a) = 𝓛^{(1)}_{u,+,a} - m(E)`; for `σ = -` the conjugate).  Deterministic left side, per time. -/
def STExpAvgAt (E u : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂(sz.seqP)) - mSigma (E n) p.1‖)
    (fun n _ _ => (sz.Bctl n (u n)) ^ 2)

/-- **`lem:improve_exp_aver`** (`6:12-21`: "the same as [YY_25, Lemma 5.15] by using `(Gt_avgbound_flow)` and
`(Eq:L-KGt-flow)`"), per time sequence `u ∈ [0, lemT z]`.  Premises, at the time sequence `u`: `(Gt_avgbound_flow)` (`LWAvgLaw`) and
`(Eq:L-KGt-flow)` (`STLK`; its `k = 1` case is the first premise, so `LWAvgLaw` is redundant, kept as in the paper).  Route (RBM2D `Evolution/Step61.lean`):
Stein for `H_u = √u X` gives `𝔼 tr(H G E_a) = -u Σ_p S_{pa} 𝔼[g_p g_a]`, with `z_u m + 1 = -u m²` the self-consistent equation
`x = u m² S x + y`, `y ≺ (W^{-d}B_{u,0})²` by the second moments of `g_p - m` (`≺ → 𝔼`, envelope `‖G_u‖ ≤ η_u⁻¹ ≤ N^{1-ε}`) and
`‖Θ_{u m²}‖_{∞→∞} ≤ C` (the merged `ekSameRow_holds`, `Evolution/XiPins.lean:357`; RBM2D has `1 + cShortRow κ (1 + log L)`).
Consumer: `st6_expAvgU_of_pin` (§7), hence the Ward pins `STExpWardI/II` and `STExpDriftLo` and `ST_step6_case{I,II,IV}_of_pins`.
§29: `0 ≤ u ≤ lemT z` (1); no regime, no `Q`, no `L^d ≤ W^K` (2)(3); **per time** (`Prec` over `a` only) (5); scale `N` (7).
Registry class: **owed** (S6-03). -/
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

/-- **The expected hierarchy at `n = 2`** (`(eq_L-Keee)` `3_5:73` at `n = 2` after taking expectations, `6:90`: "the leading
error arises from the martingale term, which vanishes after taking the expectation"): for every `|E| < 2`, `σ`, `a`:
`u ↦ f_u(σ)(a)` and `u ↦ D_u(σ)(a)` are continuous on `[0,1)`, and on `(0,1)` `∂_u f_u = Θ^{(2)}_{u,σ} f_u + D_u`.  Continuity
at `u = 0` (`H_u = √u X` is not differentiable there).  Inputs: `Ind.hierarchyN_holds`, the merged
`Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts` (`Gauss/LoopGenerator.lean:312`) and
`Gauss.initialLoopValue_two_edges` (`:487`); port of RBM2D `ExpHierPin` (`Evolution/MLExpVocab.lean:111`, S2.1).  Consumer: the proof of
`STExpDuhamelZ/Q` (RBM2D `expDuhamelPin_of_hier`, `MLExpDuhamel.lean:412`).  Registry class: **owed** (S6-04). -/
def STExpHier (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => STExpErr sz n E u σ a) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => STExpDrift sz n E u σ a) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => STExpErr sz n E v σ a)
      (STthetaOp sz n E u σ (fun b => STExpErr sz n E u σ b) a + STExpDrift sz n E u σ a) u

/-- **Duhamel from `s`, plain and zero-mode** (`(Eexpint_K-L)` `6:3-7`; `(iisuwjyys_exp)` `6:142-146`): for `0 ≤ s ≤ t < 1`,
`σ` and `A ⊂ {1,2}`, `Q^{(A)} f_t = Q^{(A)} 𝒰_{s,t} f_s + ∫_s^t Q^{(A)} 𝒰_{u,t} D_u du` (`Q^{(A)}` commutes with `𝒰`,
the merged `zeroModeSet_Ugen`; `A = ∅` is the plain form, `A = {1,2}` is regime (ii)).  RBM2D starts at `0` with `f_0 = 0`
(`ExpDuhamelPin`, `MLExpVocab.lean:124`); the paper integrates from `s` with the initial term `𝒰_{s,t} f_s`.  Consumer:
`st6_duhEq_of_pin` (§5).  Registry class: **owed** (S6-05). -/
def STExpDuhamelZ (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A (fun b => STExpErr sz n E t σ b) a =
        zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t (fun b => STExpErr sz n E s σ b)) a +
        ∫ u in s..t, zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (fun b => STExpDrift sz n E u σ b)) a

/-- The source `A_u = 𝒬_u D_u + [𝒬_u, Θ^{(2)}_{u,σ}] f_u - (𝒫 f_u) ∂_u ϑ_u` of the `𝒬`-Duhamel formula `(int_K-L+QE)`
(`6:109-116`; RBM2D `qDriftT`, `MLExpVocab.lean:70`, the sign of the last term is `-` as printed at `6:115`, paper-delta T2166a). -/
def STExpQsrc (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    (Fin 2 → Zd d (sz.L n)) → ℂ := fun b =>
  STQop (d := d) ϑ u (fun c => STExpDrift sz n E u σ c) b +
    (STQop (d := d) ϑ u (STthetaOp sz n E u σ (fun c => STExpErr sz n E u σ c)) b -
      STthetaOp sz n E u σ (STQop (d := d) ϑ u (fun c => STExpErr sz n E u σ c)) b) -
    STPsum (d := d) (fun c => STExpErr sz n E u σ c) (b 0) * deriv (fun τ => ϑ τ b) u

/-- **Duhamel with `𝒬`** (`(int_K-L+QE)` `6:109-116`): for a mollifier `ϑ` with `STMollifierProps` (`Def:QtPt`), `0 ≤ s ≤ t < 1`:
`𝒬_t f_t = 𝒰_{s,t} 𝒬_s f_s + ∫_s^t 𝒰_{u,t} A_u du`.  RBM2D `ExpQDuhamelPin` (`MLExpVocab.lean:131`).  Consumer:
`st6_duhEqQ_of_pin` (§7).  Registry class: **owed** (S6-05). -/
def STExpDuhamelQ (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    STMollifierProps (d := d) (sz.lam n) C c ϑ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STQop (d := d) ϑ t (fun b => STExpErr sz n E t σ b) a =
        RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t
          (STQop (d := d) ϑ s (fun b => STExpErr sz n E s σ b)) a +
        ∫ u in s..t, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (STExpQsrc sz n E u σ ϑ) a

/-- The Duhamel identities of `STExpDuhamelZ` along the sequences `[s_n, t_n]` (the hypothesis of the integrated pins). -/
def STExpDuhEq (E s t : ℕ → ℝ) : Prop :=
  ∀ n (u : TimeIcc s t n) (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
    zeroModeSet d (sz.L n) A (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a =
      zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (u : ℝ) (fun b => STExpErr sz n (E n) (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b)) a

/-- The `𝒬`-Duhamel identities of `STExpDuhamelQ` along the sequences, for a mollifier family `ϑ`, **eventually in `n`** (the
mollifier exists for `0 < ilambda_n ≤ 𝔡⁻¹`, which holds eventually: §29 (4), (6)). -/
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
apply (`6:58`, `6:83`); it contains regimes (i), (ii), (iii) (`st6_hi_of_reg5I/II/III`). -/
def STDriftHi {d : ℕ} (sz : Sizes d) (_s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n

/-- **`(eq:Exp(L-K)1)`** (`6:58-62`), `1-u ≥ ilambda²/L^d`: `𝔼ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a} ≺ (W^{-d}B_{u,0})^{11/5} Σ_b
B_{u,|a₁-b|} e^{-(|a₁-b|/ℓ_u)^{1/2}} ≲ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}`, uniformly in `u ∈ [s,t]` (the sum over `b` is `≲ (1-u)⁻¹`
by the shell count, absolute constant: report (a)). -/
def STExpLKLKHiConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))

/-- **`(eq:Exp(L-K)1)`**: the pin.  Inputs: `(Eq:Gdecay_flow)` (Step 5, pointwise decay), `(Eq:L-KGt-flow)` at `n = 2` (Step 4,
the maximum bound), `Σ_y S^{(B)}_{xy} = 1`, the `≺ → 𝔼` step (`momentDomAt_of_stochDomAt`, `Gauss/DominationAt.lean:328`, envelope
`‖G_u‖ ≤ η_u⁻¹ ≤ N^{1-ε}`).  Consumers: `ST_step6_case{I,II,III}_of_pins`.  §29: (2) window `STDriftHi`; (5) uniform in `u`
(`Prec` over `TimeIcc`).  Registry class: **owed** (S6-06). -/
def STExpLKLKHi (d : ℕ) : Prop := STIngR6 d STDriftHi (fun sz E s t => STExpLKLKHiConcl sz E s t)

/-- **`(eq:ExpLWn=2)`** (`6:83-88`, `lem:LWterm_EXP`), `1-u ≥ ilambda²/L^d`: `𝔼ℰ^{G̃,(2)}_{u,σ,a} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{5/2}`,
uniformly in `u ∈ [s,t]`; compiled from the per-time pin `LWtermEXP` (LW-14) by `st6_EGtHi_of_LW`. -/
def STExpEGtHiConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))

/-- The drift bounds of the window `1-u ≥ ilambda²/L^d` (regimes (i), (ii), (iii)): `(eq:Exp(L-K)1)` and `(eq:ExpLWn=2)`. -/
def STExpDriftHiConcl (E s t : ℕ → ℝ) : Prop := STExpLKLKHiConcl sz E s t ∧ STExpEGtHiConcl sz E s t

/-- **`(eq:Exp(L-K)2)` and `(eq:ExpLWn=2_smalleta)`** (`6:63-66`, `6:73-79`), `1-u ≤ ilambda²/L^d` (regime (iv)): both `𝔼ℰ^{LK×LK}`
and `𝔼ℰ^{G̃}` are `≺ W^d L^d (N|1-u|)^{-4} = (1-u)⁻¹ (N(1-u))^{-3}`, hence the drift `D_u`, uniformly in `u ∈ [s,t]`. -/
def STExpDriftLoConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpDrift sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - (p.1 : ℝ)))⁻¹) ^ 3)

/-- **`(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`**: the pin, regime (iv).  Inputs: `(Eq:L-KGt-flow)` at `n = 2, 3` (Step 4), `(eq:bcal_k)`
at `n = 3` (merged `stKbound_of_flow`), `(res_ELK_n=1)` (`STExpAvgU`, from `STImproveExpAver`, `STAvgU` and `STLKU`),
`(Gt_avgbound_flow)`; `W^d Σ_{x,y} S_{xy} = N`.  Consumer: `ST_step6_caseIV_of_pins`.  Registry class: **owed** (S6-07). -/
def STExpDriftLo (d : ℕ) : Prop :=
  STIngR6 d STReg5IV (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t)

/-- **`(deccA0)` for the expected drift** (`3_5:1634`, `Def_decay`, for the deterministic tensor `D_{u,σ}`): for every `ε, D > 0`,
eventually in `n`, `|D_{u,σ}(a)| ≤ W^{-D}` whenever `max_{i,j} |a_i - a_j| ≥ W^ε ℓ_u`, for every `u ∈ [s_n, t_n]`, `σ`
(the hypothesis `STEKDecay` of `(sum_res_1)`, `(sum_res_2_NAL)`, `(sum_res_2)`, needed in regime (i); by `lem_decayLoop`, `STDecayLoopU`,
for the loops of length `2, 3` inside `ℰ`, `ℓ¹` against `L^∞` distances: `STdiamInf`). -/
def STExpDriftDecayConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ σ : Fin 2 → Bool, STEKDecay sz s t (fun n v _ a => STExpDrift sz n (E n) (v : ℝ) σ a)

/-- **`(deccA0)` for `D_u`**: the pin, window `1-t ≥ ilambda²/L²` (regime (i)); from `STDecayLoopU` (`Induction/DecayLoopB.lean:792`)
and the `≺ → 𝔼` step.  Consumer: `ST_step6_caseI_of_pins`.  Registry class: **owed** (S6-07). -/
def STExpDriftDecay (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpDriftDecayConcl sz E s t)

/-- **Regime (i), `σ₁ ≠ σ₂`** (`(eq:EPL-K)` `6:104-107`, `(eq:boundELKQ1)` `6:121-123`, `(eq:boundcommutator)` `6:126-131`), for every
mollifier family `ϑ` with `STMollifierProps` (eventually in `n`: `ilambda_n > 0` only eventually, §29 (4), (6)): by Ward's identities
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

/-- **Regime (i) Ward terms**: the pin (window `1-t ≥ ilambda²/L²`, §29 (2): `(ℓ_u^d η_u)⁻¹ ≲ B_{u,0}` needs it).  Consumer:
`ST_step6_caseI_of_pins`.  Registry class: **owed** (S6-10). -/
def STExpWardI (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t)

/-- **Regime (ii) Ward decomposition** (`6:137-141`): for `σ₁ ≠ σ₂`, `f_{u,σ} - Q^{({1,2})} f_{u,σ} = Im[𝔼tr(G̃(E_{a₁}+E_{a₂})) -
N^{-1} 𝔼tr G̃]/(N η_u)` (`tr` the unnormalised trace, `E_a = W^{-d} 1_{[a]}`, `N = (WL)^d`, `η_u = (1-u) Im m`; checked as a
deterministic identity at `d = 3`, `L = 3`, `W ∈ {1,2}`: report (a)), hence by `(res_ELK_n=1)`, `(N η_u)⁻¹ ≤ (Im m)⁻¹ (N(1-u))⁻¹ ≤
(Im m)⁻¹ W^{-d}B_{u,0}` (bulk `Im m ≥ c(κ)`): `≺ (W^{-d}B_{u,0})³`, uniformly in `u ∈ [s,t]`. -/
def STExpWardIIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q _ => ‖STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 -
      zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
    (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3)

/-- **Regime (ii) Ward decomposition**: the pin (`(normQA2)` at `A = {1,2}` is the merged `norm_zeroModeSet_le`, `‖Q^{(A)}𝒜‖ ≤ 2^{|A|}‖𝒜‖`).
Consumer: `ST_step6_caseII_of_pins`.  Registry class: **owed** (S6-12). -/
def STExpWardII (d : ℕ) : Prop :=
  STIngR6 d STReg5II (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t)

end RBM.Gauss.Sizes

/-! ### The integrated estimates (Duhamel + kernel estimate + `u`-integral) and the initial term of regime (i)

`STExpIntConcl Q P`: if the initial term `Q^{(A)}𝒰_{s,u} f_s` is `≺ F` (a deterministic control), then `Q^{(A)} f_u ≺ F +
(W^{-d}B_{u,0})² ((ilambda² W^d)^{-1/5} + W^{-d}B_{u,0})`, uniformly in `u ∈ [s,t]`: the drift integral
`∫_s^u Q^{(A)} 𝒰_{v,u} D_v dv` is bounded by the kernel estimates (merged `stek_*_holds`) applied to the deterministic tensors `D_v`,
integrated against the drift bounds; the exponents close as in report (a).  `P` restricts the sign vectors. -/

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

/-- The integrated estimate for `𝒬_u f_u`, `σ₁ ≠ σ₂` (regime (i): `(int_K-L+QE)` `6:109-116`, `lem_+Q` `3_5:1285`, `(sum_res_2)` `3_5:1659`):
for every mollifier family `ϑ` (eventually `STMollifierProps`) satisfying the `𝒬`-Duhamel identities and every deterministic control `F` of
the initial term `𝒰_{s,u} 𝒬_s f_s`. -/
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

/-- **Regime (iii)** `1-t ≥ ilambda²`, all `σ`, no `Q` (`6:94-96`: `(sum_res_Ndecay)` with `n = 2`, `∫_s^u ((1-v)/(1-u))² (1-v)⁻¹
(W^{-d}B_{v,0})^{11/5} dv ≲ (1-u)^{-2-1/5} W^{-11d/5}`, no `log`: `x^{-6/5}`, `x^{-3/2}`); conditional on the Duhamel identity and the drift
bounds of the window.  Consumer: `ST_step6_caseIII_of_pins`.  Registry class: **owed** (S6-08). -/
def STExpIntIII (d : ℕ) : Prop :=
  STIngR6 d STReg5III (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t)

/-- **Regime (iv)** `1-s ≤ ilambda²/L^d`, all `σ`, no `Q` (`6:94-96`: `(sum_res_Ndecay)`, `n = 2`, `∫_s^u ((1-v)/(1-u))² x_v⁻¹
(N x_v)^{-3} dv ≲ (N x_u)^{-3}`); conditional on the Duhamel identity and `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`.
Consumer: `ST_step6_caseIV_of_pins`.  Registry class: **owed** (S6-08). -/
def STExpIntIV (d : ℕ) : Prop :=
  STIngR6 d STReg5IV (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t)

/-- **Regime (ii)** `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`: `Q^{({1,2})}` for `σ₁ ≠ σ₂`, none for `σ₁ = σ₂` (`6:97`, `6:142-147`:
`(sum_res_Ndecay_nonzero)` `3_5:1667` with `A ⊇ I_diff(σ)`; for `σ₁ = σ₂`, `A = ∅` (`I_diff = ∅`), **not** `(sum_res_2_NAL)`: the
latter, `lem:sum_decay` `3_5:1633`, needs `1-t ≥ ilambda²/L²`, which with `1-s ≤ ilambda²/L²` forces `s = t`: compiled as `st6_F1_window_vs_reg5II`, report (a), F1, paper-delta
candidate `T2191a`); the kernel loses nothing, the `u`-integral `∫_s^u x_v⁻¹ dv ≤ log(x_s/x_u) ≤ (d-2) log L`; conditional on the Duhamel
identity and the drift bounds.  Consumer: `ST_step6_caseII_of_pins`.  Registry class: **owed** (S6-12). -/
def STExpIntII (d : ℕ) : Prop :=
  STIngR6 d STReg5II (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t)

/-- **Regime (i)** `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²`: `σ₁ = σ₂`: plain Duhamel with `(sum_res_2_NAL)` `3_5:1649` (the drift tensors
decay: `STExpDriftDecayConcl`); `σ₁ ≠ σ₂`: the `𝒬`-form with `lem_+Q` (the merged `stQopNorm_holds`), `(sum_res_2)` and the Ward
bounds `(eq:boundELKQ1)`, `(eq:boundcommutator)`; the `u`-integral `∫ x_v⁻¹ dv ≤ 2 log L`.  Consumer: `ST_step6_caseI_of_pins`.  Registry class: **owed** (S6-09). -/
def STExpIntI (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t → STExpWardIConcl sz E s t →
      STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl sz E s t)

/-- **The initial term of regime (i)** (`6:97`, `6:117`): `𝒰_{s,u} f_s ≺ (W^{-d}B_{u,0})² ((ilambda² W^d)^{-1/5} + W^{-d}B_{u,0})` for `σ₁ = σ₂`
(`(sum_res_2_NAL)`: `((ilambda² + 1-s)/(ilambda² + 1-u))^{1} ≤ 2` since `1-s ≤ ilambda²`; `(Eq:Gtlp_exp+IND)` gives `‖f_s‖_∞`, `(Eq:Gdecay+IND)`
the decay `(deccA0)` of `f_s` through `≺ → 𝔼`), and `𝒰_{s,u} 𝒬_s f_s ≺` the same for `σ₁ ≠ σ₂` (`(sum_res_2)`: ratio `≤ 4`, `lem_+Q`).
`L^∞`-only (`(sum_res_Ndecay)`) would lose `((1-s)/(1-t))² = (W^{-d}B_{t,0})^{-2𝔠_d}`, a power of `W` (report (a)). -/
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

/-- **The initial term of regime (i)**: the pin.  Consumer: `ST_step6_caseI_of_pins`.  Registry class: **owed** (S6-11). -/
def STExpIniI (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpIniIConcl sz E s t)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- **A two-stage regime**: `[s,t]` is cut at a sequence `m`, `s < m < t`, with `R₁` on `[s,m]` and `R₂` on `[m,t]`.  Registry class: structural. -/
def STRegSeq (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∃ m : ℕ → ℝ, (∀ n, s n < m n) ∧ (∀ n, m n < t n) ∧ R₁ sz s m ∧ R₂ sz m t

end RBM.Gauss.Sizes

/-! ## 8. Compiled nonempty instances at `d = 3`

Data (all merged, `RBM.Gauss.Step5Inst` and `Step34Inst`, ticket item 7): `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`;
* regime (i): `szB` (`L = 4`, `W_n = n + 4`, `ilambda = 1`), flow `zB`, `(s,t) = (7/8, 15/16)`: `1/16 = ilambda²/L² ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`;
* regime (ii): `szB`, `(s,t) = (15/16, 31/32)`: `ilambda²/L³ = 1/64 ≤ 1-t = 1/32 ≤ 1-s = 1/16 ≤ 1/16`;
* regime (iii): `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `ilambda_n = (2(n+1))^{-6}`), flow `z0`, `(s,t) = (0, 1/16)`;
* regime (iv): `szG` (`szB` with `ilambda = 5`), flow `zB`, `(s,t) = (5/8, 3/4)`: `1-t = 1/4 ≤ 1-s = 3/8 ≤ 25/64`.
Every deterministic hypothesis (flow, time ranges, regime, `(con_st_ind)` for every `𝔠_d > 0`) is discharged; what stays a
hypothesis of an instance is a stochastic premise (`(a)`, `(b)`, `(d)` at `s`, the conclusions of Steps 2-5) or the premise of another gate's pin
(`LWtermEXP`, `LWAvgLaw`).  `(ilambda² W^d)^{-1/5} ≠ 0` at each data (`inst_G_pos_*`). -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- The result of applying a Step-6 pin `STIngR6` at the data `(sz, z, s, t)`: the constant `𝔠_d`, then the stochastic premises, then the
conclusion. -/
def InstIng6Concl (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (sz : Sizes 3)
    (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STExp2 sz (STflowE z) s →
      STStep2Core sz (STflowE z) s t → STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t →
      STGdecayW sz (STflowE z) s t 0 → Concl sz (STflowE z) s t)

/-- The common shape of the instances: the constant `𝔠_d` of the pin, then deterministic data with the regime `R` and `(con_st_ind)`. -/
theorem inst_ing6 (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl)
    (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t) :
    InstIng6Concl Concl sz z s t := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨𝔠d, h0, h1, fun hLK hDec hExp hS2 hLmax hLKU hS5 =>
    H (1 / 6) sz z hflow s t hs0 hst ht hR hLK hDec hExp (hcon 𝔠d h0) hS2 hLmax hLKU hS5⟩

/-- Data of regime (i) (and of the window `STDriftHi`): `(szB, zB, 7/8, 15/16)`. -/
theorem inst_ing6_I (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl)
    (hR : R szB (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    InstIng6Concl Concl szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6 R Concl h szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) hR
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠)

/-- Data of regime (ii): `(szB, zB, 15/16, 31/32)`. -/
theorem inst_ing6_II (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl)
    (hR : R szB (fun _ => 15 / 16) (fun _ => 31 / 32)) :
    InstIng6Concl Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_ing6 R Concl h szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) hR
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠)

/-- Data of regime (iii) and of the general statement: `(sz0, z0, 0, 1/16)`. -/
theorem inst_ing6_III (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl)
    (hR : R sz0 sInst tInst) :
    InstIng6Concl Concl sz0 z0 sInst tInst :=
  inst_ing6 R Concl h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht hR sz0_con

/-- Data of regime (iv): `(szG, zB, 5/8, 3/4)`. -/
theorem inst_ing6_IV (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl)
    (hR : R szG (fun _ => 5 / 8) (fun _ => 3 / 4)) :
    InstIng6Concl Concl szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_ing6 R Concl h szG zB flow_zG (fun _ => 5 / 8) (fun _ => 3 / 4) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) hR
    (fun _ h𝔠 => conStInd_const szG szG_W_tendsto (by norm_num) (by norm_num) h𝔠)

/-! ### The four regime pins and the general pin -/

theorem inst_step6I (h : STStep6I 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ h szB_reg5I

theorem inst_step6II (h : STStep6II 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_ing6_II STReg5II _ h szB_reg5II

theorem inst_step6III (h : STStep6III 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  inst_ing6_III STReg5III _ h sz0_reg5III

theorem inst_step6IV (h : STStep6IV 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_ing6_IV STReg5IV _ h szG_reg4

/-- `STStep6` (general) at the data of regime (iii): the regime predicate `STAny` is `True`. -/
theorem inst_step6 (h : STStep6 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  inst_ing6_III STAny _ h trivial

/-- `STStep6` at the data of regime (i): `STAny` again. -/
theorem inst_step6_atI (h : STStep6 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STAny _ h trivial

end RBM.Gauss.Step6Inst

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-! ### The ingredient pins, one instance per regime of their window -/

/-- `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` at the data of regime (iv). -/
theorem inst_expDriftLo (h : STExpDriftLo 3) :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) szG zB
      (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_ing6_IV STReg5IV _ h szG_reg4

/-- `(deccA0)` of the expected drift at the data of regime (i). -/
theorem inst_expDriftDecay (h : STExpDriftDecay 3) :
    InstIng6Concl (fun sz E s t => STExpDriftDecayConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ h szB_reg5I

/-- The Ward terms of regime (i). -/
theorem inst_expWardI (h : STExpWardI 3) :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ h szB_reg5I

/-- The Ward decomposition of regime (ii). -/
theorem inst_expWardII (h : STExpWardII 3) :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_ing6_II STReg5II _ h szB_reg5II

/-- The initial term of regime (i). -/
theorem inst_expIniI (h : STExpIniI 3) :
    InstIng6Concl (fun sz E s t => STExpIniIConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ h szB_reg5I

/-- The integrated estimates, one per regime. -/
theorem inst_expIntI (h : STExpIntI 3) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpDriftDecayConcl sz E s t → STExpWardIConcl sz E s t →
      STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ h szB_reg5I
theorem inst_expIntII (h : STExpIntII 3) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_ing6_II STReg5II _ h szB_reg5II
theorem inst_expIntIII (h : STExpIntIII 3) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) sz0 z0 sInst tInst :=
  inst_ing6_III STReg5III _ h sz0_reg5III
theorem inst_expIntIV (h : STExpIntIV 3) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_ing6_IV STReg5IV _ h szG_reg4

end RBM.Gauss.Step6Inst

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-! ### The deterministic pins at concrete data (`sz0`, `n = 0`: `L = 4`, `W = 32`, `ilambda = 1/64`, `E = 1/2`) -/

/-- `lem:improve_exp_aver` at `(sz0, z0, u ≡ 1/16)`: the premise `LWAvgLaw` (`(Gt_avgbound_flow)`) stays a hypothesis. -/
theorem inst_improveExpAver (h : STImproveExpAver 3) (hA : LWAvgLaw sz0 (STflowE z0) tInst)
    (hK : STLK sz0 (STflowE z0) tInst) : STExpAvgAt sz0 (STflowE z0) tInst :=
  h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst (fun n => by simp only [tInst]; norm_num) sz0_ht hA hK

/-- The expected hierarchy at `d = 3`, `sz0`, `n = 0`, `E = 1/2`, the loop `((+,-), (0, e₁))`: the instance of the pin. -/
theorem inst_expHier (h : STExpHier 3) :
    ContinuousOn (fun u => sz0.STExpErr 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => sz0.STExpDrift 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz0.STExpErr 0 (1 / 2) v ![true, false] ![0, Pi.single 0 1])
      (sz0.STthetaOp 0 (1 / 2) u ![true, false] (fun b => sz0.STExpErr 0 (1 / 2) u ![true, false] b)
          ![0, Pi.single 0 1] + sz0.STExpDrift 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) u :=
  h (by norm_num) sz0 0 (1 / 2) (by norm_num [abs_of_pos]) ![true, false] ![0, Pi.single 0 1]

/-- Plain and zero-mode Duhamel at `d = 3`, `sz0`, `n = 0`, `E = 1/2`, `s = 1/4 < t = 1/2`, `A = {1,2}`, `σ = (+,-)`. -/
theorem inst_duhamelZ (h : STExpDuhamelZ 3) :
    zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
        (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] =
      zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
        (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2)
          (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] +
      ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
        (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] u (1 / 2)
          (fun b => sz0.STExpDrift 0 (1 / 2) u ![true, false] b)) ![0, Pi.single 0 1] :=
  h (by norm_num) sz0 0 (1 / 2) (by norm_num [abs_of_pos]) (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    ![true, false] (Finset.univ : Finset (Fin 2)) ![0, Pi.single 0 1]

/-- `𝒬`-Duhamel at the same data, for the mollifier of `stMollifierEx_holds` (constants `C, c`, `ilambda_0 = 1/64 ≤ 1`). -/
theorem inst_duhamelQ (h : STExpDuhamelQ 3) :
    ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) C c ϑ ∧
      STQop (d := 3) ϑ (1 / 2) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] =
        RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2)
          (STQop (d := 3) ϑ (1 / 4) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] +
        ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] u (1 / 2)
          (sz0.STExpQsrc 0 (1 / 2) u ![true, false] ϑ) ![0, Pi.single 0 1] := by
  obtain ⟨C, c, hC, hc, hex⟩ := stMollifierEx_holds 3 (by norm_num) 1 1 one_pos
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ 1 := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  obtain ⟨ϑ, hϑ⟩ := hex (sz0.L 0) (sz0.three_le_L 0) (sz0.lam 0) hlam hlam'
  exact ⟨C, c, ϑ, hϑ, h (by norm_num) sz0 0 (1 / 2) (by norm_num [abs_of_pos]) C c ϑ hϑ (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) ![true, false] ![0, Pi.single 0 1]⟩

/-! ### `(ilambda² W^d)^{-1/5} ≠ 0`, the target, the index sets, `(normQA2)` -/

/-- At `sz0`, `n = 0`: `ilambda² W^d = (1/64)² 32³ = 8`, so `(ilambda² W^d)^{-1/5} = 8^{-1/5} > 0`. -/
theorem inst_A_value : sz0.lam 0 ^ 2 * ((sz0.W 0 : ℕ) : ℝ) ^ 3 = 8 := by norm_num [sz0]

/-- **The index sets are nonempty** at the four data: `TimeIcc s t n ∋ s n`, both sign classes `σ₁ = σ₂`, `σ₁ ≠ σ₂` and every label. -/
theorem st6_idx2_nonempty {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ) :
    Nonempty (STIdx2 sz s t n) :=
  ⟨⟨⟨s n, le_rfl, hst n⟩, ![true, false], 0⟩⟩

theorem st6_idxSame_nonempty {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ) :
    Nonempty (STIdx2P sz STSigSame s t n) :=
  ⟨⟨⟨s n, le_rfl, hst n⟩, ⟨![true, true], rfl⟩, 0⟩⟩

theorem st6_idxMixed_nonempty {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ) :
    Nonempty (STIdx2P sz STSigMixed s t n) :=
  ⟨⟨⟨s n, le_rfl, hst n⟩, ⟨![true, false], by simp [STSigMixed]⟩, 0⟩⟩

/-- **`(normQA2)` at `A = {1,2}`** (`Q^{({1,2})} = Q^{(1)}Q^{(2)}`, regime (ii)): `‖Q^{({1,2})} 𝒜‖_∞ ≤ 4 ‖𝒜‖_∞` for a `2`-tensor on `Z_4^3`. -/
theorem inst_normQA2 (T : (Fin 2 → Zd 3 4) → ℂ) : ‖zeroModeSet 3 4 (Finset.univ : Finset (Fin 2)) T‖ ≤ 4 * ‖T‖ := by
  have h := norm_zeroModeSet_le (d := 3) (L := 4) (Finset.univ : Finset (Fin 2)) T
  rw [Finset.card_univ, Fintype.card_fin] at h
  norm_num at h
  exact h

end RBM.Gauss.Step6Inst

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- `STStep6` implies the regime (i) pin; at the data of regime (i) it is `inst_step6I`. -/
theorem inst_step6R_of_any (h : STStep6 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I (ST_step6R_of_any h STReg5I)

end RBM.Gauss.Step6Inst
