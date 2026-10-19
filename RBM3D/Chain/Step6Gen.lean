/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Pins
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.LWGen
import RBM3D.Chain.Step34Gen

/-!
# The Step 6 vocabulary and statements over the carrier

Restatement of `Induction/Step6Pins` over a carrier `C : FlowFM sz` and a law `μ`, on the one kernel
`Step2Gen_UN`.  Paper: Step 6 is (2.94) `Eq:Gtlp_exp_flow`; its proof is Section 6 (`Sec:Step6`).
Pattern: `Chain/Step5Gen`.

* Vocabulary of the expected hierarchy: `STExpErrg`, `STExpELKLKg`, `STExpEGtg`, `STExpDriftg`,
  `STExpQsrcg`.
* The statement `STExp2UgL`, the loss-free part `STStep2CoregL` of Step 2, the conclusion
  `STStep6ConclgL` and the shape `STIngR6gL` of a Step 6 statement.
* The ingredient statements, per carrier (`STExp*Concl*gL`) and per tuple (`STExp*gL`).

Size-level names are reused as they are.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Vocabulary of the expected hierarchy -/

section Vocab

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `f_{u,σ}(a) = 𝔼 𝓛^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u,σ,a}` ((6.1) `Eexpint_K-L`) of the carrier (band `STExpErr`). -/
def STExpErrg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (∫ ω, C.L n u σ a ω ∂μ) - C.K n u σ a

/-- `𝔼 ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}` (band `STExpELKLK`). -/
def STExpELKLKg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STELKLKg C n u σ a ω ∂μ

/-- `𝔼 ℰ^{G̃,(2)}_{u,σ,a}` (band `STExpEGt`). -/
def STExpEGtg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STEGtg C n u σ a ω ∂μ

/-- The drift `D_{u,σ} = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}` of the expected hierarchy at `n = 2` (band `STExpDrift`). -/
def STExpDriftg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  STExpELKLKg C μ n u σ a + STExpEGtg C μ n u σ a

/-- The source `A_u = 𝒬_u D_u + [𝒬_u, Θ^{(2)}_{u,σ}] f_u - (𝒫 f_u) ∂_u ϑ_u` of the `𝒬`-Duhamel formula ((6.10) `int_K-L+QE`; band `STExpQsrc`), with `Θ^{(2)}` the carrier generator `Step2Gen_ThetaN`. -/
def STExpQsrcg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    (Fin 2 → Zd d (sz.L n)) → ℂ := fun b =>
  STQop (d := d) ϑ u (fun c => STExpDriftg C μ n u σ c) b +
    (STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (fun c => STExpErrg C μ n u σ c)) b -
      Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (fun c => STExpErrg C μ n u σ c)) b) -
    STPsum (d := d) (fun c => STExpErrg C μ n u σ c) (b 0) * deriv (fun τ => ϑ τ b) u

end Vocab

/-! ## 2. The statement of Step 6 and the shape of a Step 6 statement -/

section Target

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **(2.94) `Eq:Gtlp_exp_flow`** over a carrier and a law, uniformly in `u ∈ [s,t]` (band `STExp2U`; the uniform form of `STExp2gL`). -/
def STExp2UgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, C.L n (p.1 : ℝ) p.2.1 p.2.2 ω ∂μ) - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (p.1 : ℝ)))

/-- **The endpoint `u = t`** of `STExp2UgL` is `STExp2gL` at `t` (band `STExp2_of_STExp2U`). -/
theorem STExp2gL_of_STExp2UgL {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STExp2UgL C μ s t) : STExp2gL C μ t :=
  StochDomAt.precomp_param h
    (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) => ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))

/-- **The loss-free part of Step 2** over a carrier (band `STStep2Core`). -/
def STStep2CoregL (s t : ℕ → ℝ) : Prop := STLocalEntryUgL C μ s t ∧ STAvgUgL C μ s t

/-- The conclusion of Step 6 over a carrier: `(Eq:Gtlp_exp_flow)` uniformly in `u ∈ [s,t]` (band `STStep6Concl`). -/
def STStep6ConclgL (s t : ℕ → ℝ) : Prop := STExp2UgL C μ s t

end Target

/-- **A Step 6 statement over a carrier tuple `(law, Flow, mk, T0)`** (the shape of `STIngR6`; the tuple of `STIngR5gL`): the band
hypotheses read over the carrier, with the constants `κ, ε, 𝔡`, then `𝔠d ∈ (0, 10⁻²]`, then `𝔠`, the sizes and `z`; `STKboundgL`, `STKwardgL`
are not hypotheses (they are theorems of the flow). -/
def STIngR6gL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Concl : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STLKgL (mk sz z) (law sz) s → STDecaygL (mk sz z) (law sz) s →
          STExp2gL (mk sz z) (law sz) s → STConStInd sz 𝔠d s t →
          STStep2CoregL (mk sz z) (law sz) s t → STLmaxUgL (mk sz z) (law sz) s t →
          STLKUgL (mk sz z) (law sz) s t → STGdecayWgL (mk sz z) (law sz) s t 0 →
            Concl sz z s t

/-! ## 3. The ingredient statements of Step 6 -/

section Ingredient

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-! ### Lemma 6.1 (`lem:improve_exp_aver`) -/

/-- **(6.2) `res_ELK_n=1`** at one time sequence `u` over a carrier: `max_a |𝔼 𝓛^{(1)}_{u,σ,a} - m_σ| ≺ (W^{-d}B_{u,0})²`, both charges (band `STExpAvgAt`). -/
def STExpAvgAtgL (u : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, C.L n (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂μ) -
      (if p.1 then C.m n else (starRingEnd ℂ) (C.m n))‖)
    (fun n _ _ => (sz.Bctl n (u n)) ^ 2)

/-- (6.2) `res_ELK_n=1` uniformly in `u ∈ [s,t]` (band `STExpAvgU`). -/
def STExpAvgUgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, C.L n (p.1 : ℝ) (fun _ : Fin 1 => p.2.1) (fun _ => p.2.2) ω ∂μ) -
      (if p.2.1 then C.m n else (starRingEnd ℂ) (C.m n))‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2)

/-! ### The expected hierarchy and its Duhamel forms, per index -/

/-- **The expected hierarchy at `n = 2`** at one size index `n` over a carrier (band `STExpHier`, without `|E| < 2`):
`f_u` and `D_u` are continuous on `[0,1)` and `∂_u f_u = Θ^{(2)}_{u,σ} f_u + D_u` on `(0,1)`, `Θ` the carrier generator `Step2Gen_ThetaN`. -/
def STExpHierAtgL (n : ℕ) : Prop :=
  ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => (∫ ω, C.L n u σ a ω ∂μ) - C.K n u σ a) (Set.Ico (0 : ℝ) 1) ∧
    ContinuousOn (fun u => (∫ ω, STELKLKg C n u σ a ω ∂μ) + ∫ ω, STEGtg C n u σ a ω ∂μ) (Set.Ico (0 : ℝ) 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => (∫ ω, C.L n v σ a ω ∂μ) - C.K n v σ a)
      (Step2Gen_ThetaN C n σ u (fun b => (∫ ω, C.L n u σ b ω ∂μ) - C.K n u σ b) a +
        ((∫ ω, STELKLKg C n u σ a ω ∂μ) + ∫ ω, STEGtg C n u σ a ω ∂μ)) u

/-- **Duhamel from `s`, plain and zero-mode** at one index (band `STExpDuhamelZ`), kernel `Step2Gen_UN C`. -/
def STExpDuhamelZAtgL (n : ℕ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A (fun b => (∫ ω, C.L n t σ b ω ∂μ) - C.K n t σ b) a =
        zeroModeSet d (sz.L n) A
          (Step2Gen_UN C n σ s t (fun b => (∫ ω, C.L n s σ b ω ∂μ) - C.K n s σ b)) a +
        ∫ u in s..t, zeroModeSet d (sz.L n) A
          (Step2Gen_UN C n σ u t (fun b => (∫ ω, STELKLKg C n u σ b ω ∂μ) + ∫ ω, STEGtg C n u σ b ω ∂μ)) a

/-- **Duhamel with `𝒬`** at one index (band `STExpDuhamelQ`; the source is `STExpQsrcg`). -/
def STExpDuhamelQAtgL (n : ℕ) : Prop :=
  ∀ (Cq c : ℝ) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ), STMollifierProps (d := d) (sz.lam n) Cq c ϑ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STQop (d := d) ϑ t (fun b => (∫ ω, C.L n t σ b ω ∂μ) - C.K n t σ b) a =
        Step2Gen_UN C n σ s t (STQop (d := d) ϑ s (fun b => (∫ ω, C.L n s σ b ω ∂μ) - C.K n s σ b)) a +
        ∫ u in s..t, Step2Gen_UN C n σ u t (fun b =>
          STQop (d := d) ϑ u (fun c' => (∫ ω, STELKLKg C n u σ c' ω ∂μ) + ∫ ω, STEGtg C n u σ c' ω ∂μ) b +
            (STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b -
              Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b) -
            STPsum (d := d) (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c') (b 0) * deriv (fun τ => ϑ τ b) u) a

/-- The Duhamel identities of `STExpDuhamelZAtgL` along the sequences `[s_n, t_n]`, **eventually in `n`** (band `STExpDuhEq`, which is `∀ n`). -/
def STExpDuhEqgL (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
    zeroModeSet d (sz.L n) A (fun b => (∫ ω, C.L n (u : ℝ) σ b ω ∂μ) - C.K n (u : ℝ) σ b) a =
      zeroModeSet d (sz.L n) A
        (Step2Gen_UN C n σ (s n) (u : ℝ) (fun b => (∫ ω, C.L n (s n) σ b ω ∂μ) - C.K n (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), zeroModeSet d (sz.L n) A
        (Step2Gen_UN C n σ v (u : ℝ) (fun b => (∫ ω, STELKLKg C n v σ b ω ∂μ) + ∫ ω, STEGtg C n v σ b ω ∂μ)) a

/-- The `𝒬`-Duhamel identities along the sequences for a mollifier family `ϑ`, eventually in `n` (band `STExpDuhEqQ`). -/
def STExpDuhEqQgL (s t : ℕ → ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    STQop (d := d) (ϑ n) (u : ℝ) (fun b => STExpErrg C μ n (u : ℝ) σ b) a =
      Step2Gen_UN C n σ (s n) (u : ℝ) (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), Step2Gen_UN C n σ v (u : ℝ) (STExpQsrcg C μ n v σ (ϑ n)) a

/-! ### The expected drift bounds, the regime (i) Ward terms and the regime (ii) Ward decomposition -/

/-- **(6.3) `eq:Exp(L-K)1`**, `1-u ≥ lam²/L^d` (band `STExpLKLKHiConcl`). -/
def STExpLKLKHiConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpELKLKg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))

/-- **(6.7) `eq:ExpLWn=2`**, `1-u ≥ lam²/L^d` (band `STExpEGtHiConcl`): `𝔼ℰ^{G̃,(2)}_{u,σ,a} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{5/2}`. -/
def STExpEGtHiConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpEGtg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))

/-- The drift bounds of the window `1-u ≥ lam²/L^d` (band `STExpDriftHiConcl`). -/
def STExpDriftHiConclgL (s t : ℕ → ℝ) : Prop := STExpLKLKHiConclgL C μ s t ∧ STExpEGtHiConclgL C μ s t

/-- **(6.4) `eq:Exp(L-K)2` and (6.6) `eq:ExpLWn=2_smalleta`**, `1-u ≤ lam²/L^d` (band `STExpDriftLoConcl`). -/
def STExpDriftLoConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpDriftg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - (p.1 : ℝ)))⁻¹) ^ 3)

/-- **(4.52) `deccA0` for `D_u`** (band `STExpDriftDecayConcl`): the kernel hypothesis `STEKDecaygL` at the law `μ`. -/
def STExpDriftDecayConclgL (s t : ℕ → ℝ) : Prop :=
  ∀ σ : Fin 2 → Bool, STEKDecaygL μ s t (fun n v _ a => STExpDriftg C μ n (v : ℝ) σ a)

/-- **Regime (i), `σ₁ ≠ σ₂`** ((6.9) `eq:EPL-K`, (6.11) `eq:boundELKQ1`, (6.12) `eq:boundcommutator`; band `STExpWardIConcl`). -/
def STExpWardIConclgL (s t : ℕ → ℝ) : Prop :=
  ∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3) ∧
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ =>
        ‖STQop (d := d) (ϑ n) (q.1 : ℝ) (Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
            (fun c' => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c')) q.2.2 -
          Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (fun c' => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c')) q.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
          deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)

/-- **Regime (ii) Ward decomposition** (proof of Lemma 6.2 `lem:LWterm_EXP`; band `STExpWardIIConcl`). -/
def STExpWardIIConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q _ => ‖STExpErrg C μ n (q.1 : ℝ) q.2.1.1 q.2.2 -
      zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
    (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3)

/-- The integrated estimate for `Q^{(A)} f_u`, sign class `P`, kernel `Step2Gen_UN C` (band `STExpIntConcl`). -/
def STExpIntConclgL (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (s t : ℕ → ℝ) : Prop :=
  ∀ F : ∀ n, STIdx2P sz P s t n → ℝ, (∀ n p, 0 ≤ F n p) →
    PrecL sz μ (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) Q
        (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p) →
    PrecL sz μ (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) Q (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))

end Ingredient

/-! ### The ingredient statements over the carrier tuple -/

section Pins

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- The expected hierarchy, Duhamel plain and zero-mode: the eventual family forms (the hierarchy classes hold only eventually in the block Anderson model). -/
def STExpDuhamelZgL : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, STExpDuhamelZAtgL (mk sz z) (law sz) n

/-- Duhamel with `𝒬`, the eventual family form. -/
def STExpDuhamelQgL : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, STExpDuhamelQAtgL (mk sz z) (law sz) n

/-- (6.3) `eq:Exp(L-K)1` (band `STExpLKLKHi`). -/
def STExpLKLKHigL : Prop :=
  STIngR6gL d STDriftHi law Flow mk T0 (fun sz z s t => STExpLKLKHiConclgL (mk sz z) (law sz) s t)

/-- (6.4) `eq:Exp(L-K)2`, (6.6) `eq:ExpLWn=2_smalleta` (band `STExpDriftLo`). -/
def STExpDriftLogL : Prop :=
  STIngR6gL d STReg5IV law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → STExpDriftLoConclgL (mk sz z) (law sz) s t)

/-- (4.52) `deccA0` for the expected drift (band `STExpDriftDecay`). -/
def STExpDriftDecaygL : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t => STExpDriftDecayConclgL (mk sz z) (law sz) s t)

/-- Regime (i) Ward terms (band `STExpWardI`). -/
def STExpWardIgL : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → STExpWardIConclgL (mk sz z) (law sz) s t)

/-- Regime (ii) Ward decomposition (band `STExpWardII`). -/
def STExpWardIIgL : Prop :=
  STIngR6gL d STReg5II law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → STExpWardIIConclgL (mk sz z) (law sz) s t)

/-- Regime (iii) integrated estimate (band `STExpIntIII`). -/
def STExpIntIIIgL : Prop :=
  STIngR6gL d STReg5III law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftHiConclgL (mk sz z) (law sz) s t →
      STExpIntConclgL (mk sz z) (law sz) ∅ STSigAll s t)

/-- Regime (iv) integrated estimate (band `STExpIntIV`). -/
def STExpIntIVgL : Prop :=
  STIngR6gL d STReg5IV law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftLoConclgL (mk sz z) (law sz) s t →
      STExpIntConclgL (mk sz z) (law sz) ∅ STSigAll s t)

/-- Regime (ii) integrated estimate (band `STExpIntII`). -/
def STExpIntIIgL : Prop :=
  STIngR6gL d STReg5II law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftHiConclgL (mk sz z) (law sz) s t →
      STExpIntConclgL (mk sz z) (law sz) (Finset.univ : Finset (Fin 2)) STSigMixed s t ∧
        STExpIntConclgL (mk sz z) (law sz) ∅ STSigSame s t)

end Pins

/-! ## 4. Bridges of the conclusions (band name to generic name) -/

/-! ## 5. The shape `STIngR6gL` and the band bridges of the statements -/

/-! ## 6. The band bridges of the ingredient statements -/

/-! The four integrated statements read `STExpDuhEq` (band: `∀ n`) and `STExpDuhEqgL` (eventually in `n`) as a hypothesis, so only the generic
statement implies the band one. -/

end RBM.BA

end
