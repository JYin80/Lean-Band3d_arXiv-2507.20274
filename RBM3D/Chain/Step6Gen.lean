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
# The Step 6 vocabulary and pins over the carrier (BA-V row V1s1, ticket T2502 row a)

Additive restatement of `Induction/Step6Pins.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the one kernel `Step2Gen_UN`
(no kernel, propagator or second bridge is defined here).  Paper: arXiv:2507.20274, Step 6 is `1_2:1390-1396`, its proof `6:3-152`.
Pattern: `Chain/Step5Gen.lean`.  Vocabulary `STExp*g` (target 1); the target and shape `STExp2UgL`, `STIngR6gL`, `STStep6RgL`, `STStep6IgL` to
`STStep6gL` (target 2); the ingredient texts, per carrier (`STExp*Concl*gL`) and per tuple (`STExp*gL`; rows b, c prove the heads) (target 3);
bridges `bandFM_<band name>`, `<band name>_iff_gL` (target 4), one way for the eventual twins.  Size-level names are reused as they are.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Vocabulary of the expected hierarchy (target 1) -/

section Vocab

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `f_{u,σ}(a) = 𝔼 𝓛^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u,σ,a}` (`Eexpint_K-L`, `6:3-7`) of the carrier (band `STExpErr`, `Step6Pins:45`). -/
def STExpErrg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (∫ ω, C.L n u σ a ω ∂μ) - C.K n u σ a

/-- `𝔼 ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}` (band `STExpELKLK`, `Step6Pins:49`). -/
def STExpELKLKg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STELKLKg C n u σ a ω ∂μ

/-- `𝔼 ℰ^{G̃,(2)}_{u,σ,a}` (band `STExpEGt`, `Step6Pins:54`). -/
def STExpEGtg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∫ ω, STEGtg C n u σ a ω ∂μ

/-- The drift `D_{u,σ} = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}` of the expected hierarchy at `n = 2` (band `STExpDrift`, `Step6Pins:59`). -/
def STExpDriftg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  STExpELKLKg C μ n u σ a + STExpEGtg C μ n u σ a

/-- The source `A_u = 𝒬_u D_u + [𝒬_u, Θ^{(2)}_{u,σ}] f_u - (𝒫 f_u) ∂_u ϑ_u` of the `𝒬`-Duhamel formula (`6:109-116`; band `STExpQsrc`, `Step6Pins:236`), with `Θ^{(2)}` the carrier generator `Step2Gen_ThetaN`. -/
def STExpQsrcg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    (Fin 2 → Zd d (sz.L n)) → ℂ := fun b =>
  STQop (d := d) ϑ u (fun c => STExpDriftg C μ n u σ c) b +
    (STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (fun c => STExpErrg C μ n u σ c)) b -
      Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (fun c => STExpErrg C μ n u σ c)) b) -
    STPsum (d := d) (fun c => STExpErrg C μ n u σ c) (b 0) * deriv (fun τ => ϑ τ b) u

end Vocab

/-! ## 2. The target of Step 6 and the shape of a Step-6 pin (target 2) -/

section Target

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`(Eq:Gtlp_exp_flow)`** (`1_2:1390-1396`) over a carrier and a law, uniformly in `u ∈ [s,t]` (band `STExp2U`, `Step6Pins:71`; the uniform form of `STExp2gL`, `Carrier:127`). -/
def STExp2UgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, C.L n (p.1 : ℝ) p.2.1 p.2.2 ω ∂μ) - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (p.1 : ℝ)))

/-- **The endpoint `u = t`** of `STExp2UgL` is `STExp2gL` at `t` (band `STExp2_of_STExp2U`, `Step6Pins:87`). -/
theorem STExp2gL_of_STExp2UgL {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STExp2UgL C μ s t) : STExp2gL C μ t :=
  StochDomAt.precomp_param h
    (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) => ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))

/-- **The loss-free part of Step 2** over a carrier (band `STStep2Core`, `Step6Pins:95`). -/
def STStep2CoregL (s t : ℕ → ℝ) : Prop := STLocalEntryUgL C μ s t ∧ STAvgUgL C μ s t

/-- The conclusion of Step 6 over a carrier: `(Eq:Gtlp_exp_flow)` uniformly in `u ∈ [s,t]` (band `STStep6Concl`). -/
def STStep6ConclgL (s t : ℕ → ℝ) : Prop := STExp2UgL C μ s t

end Target

/-- **A Step-6 pin over a carrier tuple `(law, Flow, mk, T0)`** (the shape of `STIngR6`, `Step6Pins:111`; the tuple of `STIngR5gL`): the band
premises read over the carrier, with the constants `κ, ε, 𝔡`, then `𝔠d ∈ (0, 10⁻²]`, then `𝔠`, the sizes and `z`; `STKboundgL`, `STKwardgL`
are not premises (theorems of the flow). -/
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

/-! ## 3. The ingredient texts of Step 6 (target 3) -/

section Ingredient

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-! ### (b) `lem:improve_exp_aver` -/

/-- **`(res_ELK_n=1)`** (`6:14-16`) at one time sequence `u` over a carrier: `max_a |𝔼 𝓛^{(1)}_{u,σ,a} - m_σ| ≺ (W^{-d}B_{u,0})²`, both charges (band `STExpAvgAt`, `Step6Pins:177`). -/
def STExpAvgAtgL (u : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, C.L n (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂μ) -
      (if p.1 then C.m n else (starRingEnd ℂ) (C.m n))‖)
    (fun n _ _ => (sz.Bctl n (u n)) ^ 2)

/-- `(res_ELK_n=1)` uniformly in `u ∈ [s,t]` (band `STExpAvgU`, `Step6Pins:198`). -/
def STExpAvgUgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, C.L n (p.1 : ℝ) (fun _ : Fin 1 => p.2.1) (fun _ => p.2.2) ω ∂μ) -
      (if p.2.1 then C.m n else (starRingEnd ℂ) (C.m n))‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2)

/-! ### (c) the expected hierarchy and its Duhamel forms, per index (row b proves them) -/

/-- **The expected hierarchy at `n = 2`** at one size index `n` over a carrier (band `STExpHier`, `Step6Pins:213`, without `|E| < 2`):
`f_u` and `D_u` are continuous on `[0,1)` and `∂_u f_u = Θ^{(2)}_{u,σ} f_u + D_u` on `(0,1)`, `Θ` the carrier generator `Step2Gen_ThetaN`. -/
def STExpHierAtgL (n : ℕ) : Prop :=
  ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => (∫ ω, C.L n u σ a ω ∂μ) - C.K n u σ a) (Set.Ico (0 : ℝ) 1) ∧
    ContinuousOn (fun u => (∫ ω, STELKLKg C n u σ a ω ∂μ) + ∫ ω, STEGtg C n u σ a ω ∂μ) (Set.Ico (0 : ℝ) 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => (∫ ω, C.L n v σ a ω ∂μ) - C.K n v σ a)
      (Step2Gen_ThetaN C n σ u (fun b => (∫ ω, C.L n u σ b ω ∂μ) - C.K n u σ b) a +
        ((∫ ω, STELKLKg C n u σ a ω ∂μ) + ∫ ω, STEGtg C n u σ a ω ∂μ)) u

/-- **Duhamel from `s`, plain and zero-mode** at one index (band `STExpDuhamelZ`, `Step6Pins:225`), kernel `Step2Gen_UN C`. -/
def STExpDuhamelZAtgL (n : ℕ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A (fun b => (∫ ω, C.L n t σ b ω ∂μ) - C.K n t σ b) a =
        zeroModeSet d (sz.L n) A
          (Step2Gen_UN C n σ s t (fun b => (∫ ω, C.L n s σ b ω ∂μ) - C.K n s σ b)) a +
        ∫ u in s..t, zeroModeSet d (sz.L n) A
          (Step2Gen_UN C n σ u t (fun b => (∫ ω, STELKLKg C n u σ b ω ∂μ) + ∫ ω, STEGtg C n u σ b ω ∂μ)) a

/-- **Duhamel with `𝒬`** at one index (band `STExpDuhamelQ`, `Step6Pins:246`; the source is `STExpQsrcg`). -/
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

/-- The Duhamel identities of `STExpDuhamelZAtgL` along the sequences `[s_n, t_n]`, **eventually in `n`** (answer (5); band `STExpDuhEq`, `Step6Pins:256`, which is `∀ n`). -/
def STExpDuhEqgL (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
    zeroModeSet d (sz.L n) A (fun b => (∫ ω, C.L n (u : ℝ) σ b ω ∂μ) - C.K n (u : ℝ) σ b) a =
      zeroModeSet d (sz.L n) A
        (Step2Gen_UN C n σ (s n) (u : ℝ) (fun b => (∫ ω, C.L n (s n) σ b ω ∂μ) - C.K n (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), zeroModeSet d (sz.L n) A
        (Step2Gen_UN C n σ v (u : ℝ) (fun b => (∫ ω, STELKLKg C n v σ b ω ∂μ) + ∫ ω, STEGtg C n v σ b ω ∂μ)) a

/-- The `𝒬`-Duhamel identities along the sequences for a mollifier family `ϑ`, eventually in `n` (band `STExpDuhEqQ`, `Step6Pins:266`). -/
def STExpDuhEqQgL (s t : ℕ → ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    STQop (d := d) (ϑ n) (u : ℝ) (fun b => STExpErrg C μ n (u : ℝ) σ b) a =
      Step2Gen_UN C n σ (s n) (u : ℝ) (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), Step2Gen_UN C n σ v (u : ℝ) (STExpQsrcg C μ n v σ (ϑ n)) a

/-! ### (d) the expected drift bounds, (e) regime (i) Ward terms, (f) regime (ii) Ward decomposition -/

/-- **`(eq:Exp(L-K)1)`**, `1-u ≥ lam²/L^d` (band `STExpLKLKHiConcl`, `Step6Pins:292`). -/
def STExpLKLKHiConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpELKLKg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))

/-- **`(eq:ExpLWn=2)`**, `1-u ≥ lam²/L^d` (band `STExpEGtHiConcl`, `Step6Pins:305`): `𝔼ℰ^{G̃,(2)}_{u,σ,a} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{5/2}`. -/
def STExpEGtHiConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpEGtg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))

/-- The drift bounds of the window `1-u ≥ lam²/L^d` (band `STExpDriftHiConcl`, `Step6Pins:311`). -/
def STExpDriftHiConclgL (s t : ℕ → ℝ) : Prop := STExpLKLKHiConclgL C μ s t ∧ STExpEGtHiConclgL C μ s t

/-- **`(eq:Exp(L-K)2)` and `(eq:ExpLWn=2_smalleta)`**, `1-u ≤ lam²/L^d` (band `STExpDriftLoConcl`, `Step6Pins:315`). -/
def STExpDriftLoConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2 sz s t)
    (fun n p _ => ‖STExpDriftg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - (p.1 : ℝ)))⁻¹) ^ 3)

/-- **`(deccA0)` for `D_u`** (band `STExpDriftDecayConcl`, `Step6Pins:330`): the kernel pin text `STEKDecaygL` at the law `μ`. -/
def STExpDriftDecayConclgL (s t : ℕ → ℝ) : Prop :=
  ∀ σ : Fin 2 → Bool, STEKDecaygL μ s t (fun n v _ a => STExpDriftg C μ n (v : ℝ) σ a)

/-- **Regime (i), `σ₁ ≠ σ₂`** (`(eq:EPL-K)`, `(eq:boundELKQ1)`, `(eq:boundcommutator)`; band `STExpWardIConcl`, `Step6Pins:342`). -/
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

/-- **Regime (ii) Ward decomposition** (`6:137-141`; band `STExpWardIIConcl`, `Step6Pins:368`). -/
def STExpWardIIConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q _ => ‖STExpErrg C μ n (q.1 : ℝ) q.2.1.1 q.2.2 -
      zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
    (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3)

/-- The integrated estimate for `Q^{(A)} f_u`, sign class `P`, kernel `Step2Gen_UN C` (band `STExpIntConcl`, `Step6Pins:395`). -/
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

/-! ### The ingredient pins over the carrier tuple -/

section Pins

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- The expected hierarchy, Duhamel plain and zero-mode: the eventual family forms (UP-C4: the hierarchy classes hold only eventually at BA); proved by row b of T2502. -/
def STExpDuhamelZgL : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, STExpDuhamelZAtgL (mk sz z) (law sz) n

/-- Duhamel with `𝒬`, the eventual family form. -/
def STExpDuhamelQgL : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, STExpDuhamelQAtgL (mk sz z) (law sz) n

/-- `(eq:Exp(L-K)1)` (band `STExpLKLKHi`, `Step6Pins:301`). -/
def STExpLKLKHigL : Prop :=
  STIngR6gL d STDriftHi law Flow mk T0 (fun sz z s t => STExpLKLKHiConclgL (mk sz z) (law sz) s t)

/-- `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` (band `STExpDriftLo`, `Step6Pins:323`). -/
def STExpDriftLogL : Prop :=
  STIngR6gL d STReg5IV law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → STExpDriftLoConclgL (mk sz z) (law sz) s t)

/-- `(deccA0)` for the expected drift (band `STExpDriftDecay`, `Step6Pins:335`). -/
def STExpDriftDecaygL : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t => STExpDriftDecayConclgL (mk sz z) (law sz) s t)

/-- Regime (i) Ward terms (band `STExpWardI`, `Step6Pins:361`). -/
def STExpWardIgL : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → STExpWardIConclgL (mk sz z) (law sz) s t)

/-- Regime (ii) Ward decomposition (band `STExpWardII`, `Step6Pins:376`). -/
def STExpWardIIgL : Prop :=
  STIngR6gL d STReg5II law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → STExpWardIIConclgL (mk sz z) (law sz) s t)

/-- Regime (iii) integrated estimate (band `STExpIntIII`, `Step6Pins:425`). -/
def STExpIntIIIgL : Prop :=
  STIngR6gL d STReg5III law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftHiConclgL (mk sz z) (law sz) s t →
      STExpIntConclgL (mk sz z) (law sz) ∅ STSigAll s t)

/-- Regime (iv) integrated estimate (band `STExpIntIV`, `Step6Pins:432`). -/
def STExpIntIVgL : Prop :=
  STIngR6gL d STReg5IV law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftLoConclgL (mk sz z) (law sz) s t →
      STExpIntConclgL (mk sz z) (law sz) ∅ STSigAll s t)

/-- Regime (ii) integrated estimate (band `STExpIntII`, `Step6Pins:441`). -/
def STExpIntIIgL : Prop :=
  STIngR6gL d STReg5II law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftHiConclgL (mk sz z) (law sz) s t →
      STExpIntConclgL (mk sz z) (law sz) (Finset.univ : Finset (Fin 2)) STSigMixed s t ∧
        STExpIntConclgL (mk sz z) (law sz) ∅ STSigSame s t)

end Pins

/-! ## 4. Bridges of the conclusions (band name to generic name; target 4) -/

/-! ## 5. The shape `STIngR6gL` and the band bridges of the pins -/

/-! ## 6. The band bridges of the ingredient pins -/

/-! The four integrated pins read `STExpDuhEq` (band: `∀ n`) and `STExpDuhEqgL` (eventually in `n`) as a premise, so only the generic pin implies
the band one (the eventual twins; answer (5)). -/

end RBM.BA

/-! ## 7. Compiled nonempty instances at `d = 3`

Data (merged, `Step6Pins` §8; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`): regime (i) `(szB, zB, 7/8, 15/16)`, (ii) `(szB, zB, 15/16, 31/32)`, (iii) and the general statement
`(sz0, z0, 0, 1/16)`, (iv) `(szG, zB, 5/8, 3/4)`.  Deterministic hypotheses are discharged; what stays a hypothesis is a pin of another row (generic pins,
the Duhamel pins of row b, the stochastic premises at `s`). -/

end
