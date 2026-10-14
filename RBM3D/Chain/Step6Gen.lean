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

/-- `STExp2UgL` written with `STExpErrg` and `STExpTarget`. -/
theorem STExp2UgL_iff (s t : ℕ → ℝ) :
    STExp2UgL C μ s t ↔
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := Iff.rfl

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

/-- **Step 6 of `lem:main_ind`** (`1_2:1390-1396`) over a carrier tuple, under a regime predicate `R` (band `STStep6R`, `Step6Pins:126`). -/
def STStep6RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d R law Flow mk T0 (fun sz z s t => STStep6ConclgL (mk sz z) (law sz) s t)

section Wrapped

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- **Step 6, the four regimes and the general statement** (band `STStep6I` .. `STStep6`, `Step6Pins:131-145`). -/
def STStep6IgL : Prop := STStep6RgL d STReg5I law Flow mk T0
def STStep6IIgL : Prop := STStep6RgL d STReg5II law Flow mk T0
def STStep6IIIgL : Prop := STStep6RgL d STReg5III law Flow mk T0
def STStep6IVgL : Prop := STStep6RgL d STReg5IV law Flow mk T0
def STStep6gL : Prop := STStep6RgL d STAny law Flow mk T0

end Wrapped

/-- The general pin implies each regime (`STAny` is `True`; band `ST_step6R_of_any`, `Step6Pins:149`). -/
theorem ST_step6R_of_anygL {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (h : STStep6gL d law Flow mk T0)
    (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : STStep6RgL d R law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hc', H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨c, hc, hc', fun 𝔠 sz z hflow s t hs0 hst htT _ => H 𝔠 sz z hflow s t hs0 hst htT trivial⟩

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

/-- The integrated estimate for `𝒬_u f_u`, `σ₁ ≠ σ₂` (band `STExpIntQConcl`, `Step6Pins:409`). -/
def STExpIntQConclgL (s t : ℕ → ℝ) : Prop :=
  ∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) → STExpDuhEqQgL C μ s t ϑ →
    ∀ F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ F n p) →
      PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => F n p) →
      PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
          (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
        (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))

/-- **The initial term of regime (i)** (band `STExpIniIConcl`, `Step6Pins:458`). -/
def STExpIniIConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2P sz STSigSame s t)
    (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b) p.2.2‖)
    (fun n p _ => STExpTarget sz n (p.1 : ℝ)) ∧
  ∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) →
    PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))

end Ingredient

/-! ### The ingredient pins over the carrier tuple -/

section Pins

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- **`lem:improve_exp_aver`** over the carrier tuple (band `STImproveExpAver`, `Step6Pins:191`); proved by row c of T2502. -/
def STImproveExpAvergL : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ T0 sz z n) →
        LWAvgLawgL (mk sz z) (law sz) u → STLKgL (mk sz z) (law sz) u → STExpAvgAtgL (mk sz z) (law sz) u

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

/-- Regime (i) integrated estimate (band `STExpIntI`, `Step6Pins:449`). -/
def STExpIntIgL : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftHiConclgL (mk sz z) (law sz) s t →
      STExpDriftDecayConclgL (mk sz z) (law sz) s t → STExpWardIConclgL (mk sz z) (law sz) s t →
        STExpIntConclgL (mk sz z) (law sz) ∅ STSigSame s t ∧ STExpIntQConclgL (mk sz z) (law sz) s t)

/-- The initial term of regime (i) (band `STExpIniI`, `Step6Pins:471`). -/
def STExpIniIgL : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t => STExpIniIConclgL (mk sz z) (law sz) s t)

end Pins

/-! ## 4. Bridges of the conclusions (band name to generic name; target 4) -/

section ConclBridge

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

/-- `Θ^{(2)}` of the band is `Step2Gen_ThetaN` at `bandFM` (copy of `expDuh_STthetaOp_eq_ThetaN`, `ExpDuhamel:327`, composed with `Step2Kern_ThetaN_band`; the band file is not imported). -/
private theorem Step6Gen_STthetaOp_eq (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) :
    sz.STthetaOp n (E n) u σ A = Step2Gen_ThetaN (bandFM sz E) n σ u A := by
  funext a
  rw [Step2Kern_ThetaN_band]
  unfold RBM.ThetaN STthetaOp
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  have hμ : RBM.cycProd (fun l => RBM.mSigma (E n) (σ l)) i = STmsig (E n) (σ 0) * STmsig (E n) (σ 1) := by
    fin_cases i
    · rfl
    · exact mul_comm _ _
  simp only [RBM.thetaKer, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, hμ]

theorem bandFM_STExpErr (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpErr n (E n) u σ a = STExpErrg (bandFM sz E) (Sizes.seqP sz) n u σ a := rfl

theorem bandFM_STExpELKLK (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpELKLK n (E n) u σ a = STExpELKLKg (bandFM sz E) (Sizes.seqP sz) n u σ a := rfl

theorem bandFM_STExpEGt (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpEGt n (E n) u σ a = STExpEGtg (bandFM sz E) (Sizes.seqP sz) n u σ a := rfl

theorem bandFM_STExpDrift (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpDrift n (E n) u σ a = STExpDriftg (bandFM sz E) (Sizes.seqP sz) n u σ a := rfl

/-- The source of the `𝒬`-Duhamel formula: through the bridge of `Θ^{(2)}`. -/
theorem bandFM_STExpQsrc (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    sz.STExpQsrc n (E n) u σ ϑ = STExpQsrcg (bandFM sz E) (Sizes.seqP sz) n u σ ϑ := by
  unfold STExpQsrc STExpQsrcg
  simp only [Step6Gen_STthetaOp_eq]
  rfl

theorem bandFM_STExp2U : STExp2U sz E s t ↔ STExp2UgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STStep2Core : STStep2Core sz E s t ↔ STStep2CoregL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STStep6Concl : STStep6Concl sz E s t ↔ STStep6ConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STExpAvgAt : STExpAvgAt sz E s ↔ STExpAvgAtgL (bandFM sz E) (Sizes.seqP sz) s := Iff.rfl

theorem bandFM_STExpAvgU : STExpAvgU sz E s t ↔ STExpAvgUgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STExpLKLKHiConcl :
    STExpLKLKHiConcl sz E s t ↔ STExpLKLKHiConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STExpEGtHiConcl :
    STExpEGtHiConcl sz E s t ↔ STExpEGtHiConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STExpDriftHiConcl :
    STExpDriftHiConcl sz E s t ↔ STExpDriftHiConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STExpDriftLoConcl :
    STExpDriftLoConcl sz E s t ↔ STExpDriftLoConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STExpDriftDecayConcl :
    STExpDriftDecayConcl sz E s t ↔ STExpDriftDecayConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STExpWardIIConcl :
    STExpWardIIConcl sz E s t ↔ STExpWardIIConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

/-- Regime (i) Ward terms: proved through the bridge of `Θ^{(2)}`, nothing else. -/
theorem bandFM_STExpWardIConcl : STExpWardIConcl sz E s t ↔ STExpWardIConclgL (bandFM sz E) (Sizes.seqP sz) s t := by
  unfold STExpWardIConcl STExpWardIConclgL
  simp only [Step6Gen_STthetaOp_eq]
  exact Iff.rfl

/-- The integrated estimate: proved through `bandStep2_Ugen`, nothing else. -/
theorem bandFM_STExpIntConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) :
    STExpIntConcl sz Q P E s t ↔ STExpIntConclgL (bandFM sz E) (Sizes.seqP sz) Q P s t := by
  unfold STExpIntConcl STExpIntConclgL
  simp only [bandStep2_Ugen]
  exact Iff.rfl

/-- The initial term of regime (i): proved through `bandStep2_Ugen`, nothing else. -/
theorem bandFM_STExpIniIConcl : STExpIniIConcl sz E s t ↔ STExpIniIConclgL (bandFM sz E) (Sizes.seqP sz) s t := by
  unfold STExpIniIConcl STExpIniIConclgL
  simp only [bandStep2_Ugen]
  exact Iff.rfl

/-- The Duhamel identity along `[s,t]`: the band `∀ n` gives the eventual generic form (one direction). -/
theorem bandFM_STExpDuhEq_to_gL (h : STExpDuhEq sz E s t) : STExpDuhEqgL (bandFM sz E) (Sizes.seqP sz) s t := by
  refine Filter.Eventually.of_forall fun n => ?_
  intro u σ A a
  have := h n u σ A a
  simp only [bandStep2_Ugen] at this
  exact this

/-- The `𝒬`-Duhamel identity along `[s,t]`, a mollifier family: both are eventual. -/
theorem bandFM_STExpDuhEqQ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    STExpDuhEqQ sz E s t ϑ ↔ STExpDuhEqQgL (bandFM sz E) (Sizes.seqP sz) s t ϑ := by
  unfold STExpDuhEqQ STExpDuhEqQgL
  simp only [bandStep2_Ugen, bandFM_STExpQsrc]
  exact Iff.rfl

/-- The integrated estimate for `𝒬_u f_u`: through `bandFM_STExpDuhEqQ` and `bandStep2_Ugen`. -/
theorem bandFM_STExpIntQConcl : STExpIntQConcl sz E s t ↔ STExpIntQConclgL (bandFM sz E) (Sizes.seqP sz) s t := by
  unfold STExpIntQConcl STExpIntQConclgL
  simp only [bandStep2_Ugen, bandFM_STExpDuhEqQ]
  exact Iff.rfl

end ConclBridge

/-! ## 5. The shape `STIngR6gL` and the band bridges of the pins -/

section PinBridge

variable (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
  (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
  (Concl' : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop)

/-- The band shape `STIngR6` is `STIngR6gL` at the band tuple `(seqP, STFlow, bandFM ∘ STflowE, lemT)` for a band conclusion `Concl` and a
generic one `Concl'` that agree pointwise: every premise is definitionally the band one. -/
theorem Step6Gen_ingR6_iff_congr
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), Concl sz (STflowE z) s t ↔ Concl' sz z s t) :
    STIngR6 d R Concl ↔
      STIngR6gL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) Concl' := by
  unfold STIngR6 STIngR6gL
  constructor
  · intro h hd κ ε 𝔡 hκ hε h𝔡
    obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
    exact ⟨𝔠d, h0, h1, fun 𝔠 sz z hf s t hs0 hst ht hR hK hDec hExp hCon hS2 hLm hLKU hGd =>
      (hC sz z s t).1 (H 𝔠 sz z hf s t hs0 hst ht hR hK hDec hExp hCon hS2 hLm hLKU hGd)⟩
  · intro h hd κ ε 𝔡 hκ hε h𝔡
    obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
    exact ⟨𝔠d, h0, h1, fun 𝔠 sz z hf s t hs0 hst ht hR hK hDec hExp hCon hS2 hLm hLKU hGd =>
      (hC sz z s t).2 (H 𝔠 sz z hf s t hs0 hst ht hR hK hDec hExp hCon hS2 hLm hLKU hGd)⟩

/-- The other direction of the congruence: generic to band. -/
theorem Step6Gen_ingR6_of_gL
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), Concl' sz z s t → Concl sz (STflowE z) s t) :
    STIngR6gL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) Concl' → STIngR6 d R Concl := by
  intro h hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨𝔠d, h0, h1, fun 𝔠 sz z hf s t hs0 hst ht hR hK hDec hExp hCon hS2 hLm hLKU hGd =>
    hC sz z s t (H 𝔠 sz z hf s t hs0 hst ht hR hK hDec hExp hCon hS2 hLm hLKU hGd)⟩

/-- **Target 4 bridge**: for every band conclusion `Concl`, `STIngR6 d R Concl` is `STIngR6gL` at the band tuple with the conclusion `fun sz z s t => Concl sz (STflowE z) s t`. -/
theorem STIngR6_iff_gL :
    STIngR6 d R Concl ↔
      STIngR6gL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
        (fun sz z s t => Concl sz (STflowE z) s t) :=
  Step6Gen_ingR6_iff_congr d R Concl _ (fun _ _ _ _ => Iff.rfl)

/-- `STStep6R` is `STStep6RgL` at the band tuple. -/
theorem STStep6R_iff_gL :
    STStep6R d R ↔ STStep6RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d R (fun sz E s t => STStep6Concl sz E s t) _
    (fun sz z s t => bandFM_STStep6Concl sz (STflowE z) s t)

theorem STStep6I_iff_gL :
    STStep6I d ↔ STStep6IgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep6R_iff_gL d STReg5I

theorem STStep6II_iff_gL :
    STStep6II d ↔ STStep6IIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep6R_iff_gL d STReg5II

theorem STStep6III_iff_gL :
    STStep6III d ↔ STStep6IIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep6R_iff_gL d STReg5III

theorem STStep6IV_iff_gL :
    STStep6IV d ↔ STStep6IVgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep6R_iff_gL d STReg5IV

theorem STStep6_iff_gL :
    STStep6 d ↔ STStep6gL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep6R_iff_gL d STAny

end PinBridge

/-! ## 6. The band bridges of the ingredient pins -/

section IngredientBridge

variable (d : ℕ)

/-- `lem:improve_exp_aver`: the band pin is the generic pin at the band tuple (every premise and the conclusion are definitionally the band ones). -/
theorem STImproveExpAver_iff_gL :
    STImproveExpAver d ↔ STImproveExpAvergL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl

theorem STExpLKLKHi_iff_gL :
    STExpLKLKHi d ↔ STExpLKLKHigL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d STDriftHi (fun sz E s t => STExpLKLKHiConcl sz E s t) _
    (fun sz z s t => bandFM_STExpLKLKHiConcl sz (STflowE z) s t)

theorem STExpDriftLo_iff_gL :
    STExpDriftLo d ↔ STExpDriftLogL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d STReg5IV (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) _
    (fun sz z s t => imp_congr (bandFM_STExpAvgU sz (STflowE z) s t) (bandFM_STExpDriftLoConcl sz (STflowE z) s t))

theorem STExpDriftDecay_iff_gL :
    STExpDriftDecay d ↔ STExpDriftDecaygL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d STReg5I (fun sz E s t => STExpDriftDecayConcl sz E s t) _
    (fun sz z s t => bandFM_STExpDriftDecayConcl sz (STflowE z) s t)

theorem STExpWardI_iff_gL :
    STExpWardI d ↔ STExpWardIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t) _
    (fun sz z s t => imp_congr (bandFM_STExpAvgU sz (STflowE z) s t) (bandFM_STExpWardIConcl sz (STflowE z) s t))

theorem STExpWardII_iff_gL :
    STExpWardII d ↔ STExpWardIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d STReg5II (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t) _
    (fun sz z s t => imp_congr (bandFM_STExpAvgU sz (STflowE z) s t) (bandFM_STExpWardIIConcl sz (STflowE z) s t))

theorem STExpIniI_iff_gL :
    STExpIniI d ↔ STExpIniIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d STReg5I (fun sz E s t => STExpIniIConcl sz E s t) _
    (fun sz z s t => bandFM_STExpIniIConcl sz (STflowE z) s t)

/-! The four integrated pins read `STExpDuhEq` (band: `∀ n`) and `STExpDuhEqgL` (eventually in `n`) as a premise, so only the generic pin implies
the band one (the eventual twins; answer (5)). -/

theorem STExpIntIII_of_gL
    (h : STExpIntIIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) : STExpIntIII d :=
  Step6Gen_ingR6_of_gL d STReg5III
    (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t) _
    (fun sz z s t H hDu hHi => (bandFM_STExpIntConcl sz (STflowE z) s t ∅ STSigAll).2
      (H (bandFM_STExpDuhEq_to_gL sz (STflowE z) s t hDu) ((bandFM_STExpDriftHiConcl sz (STflowE z) s t).1 hHi))) h

theorem STExpIntIV_of_gL
    (h : STExpIntIVgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) : STExpIntIV d :=
  Step6Gen_ingR6_of_gL d STReg5IV
    (fun sz E s t => STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t) _
    (fun sz z s t H hDu hLo => (bandFM_STExpIntConcl sz (STflowE z) s t ∅ STSigAll).2
      (H (bandFM_STExpDuhEq_to_gL sz (STflowE z) s t hDu) ((bandFM_STExpDriftLoConcl sz (STflowE z) s t).1 hLo))) h

theorem STExpIntII_of_gL
    (h : STExpIntIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) : STExpIntII d :=
  Step6Gen_ingR6_of_gL d STReg5II
    (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t) _
    (fun sz z s t H hDu hHi =>
      let r := H (bandFM_STExpDuhEq_to_gL sz (STflowE z) s t hDu) ((bandFM_STExpDriftHiConcl sz (STflowE z) s t).1 hHi)
      ⟨(bandFM_STExpIntConcl sz (STflowE z) s t _ STSigMixed).2 r.1,
        (bandFM_STExpIntConcl sz (STflowE z) s t ∅ STSigSame).2 r.2⟩) h

theorem STExpIntI_of_gL
    (h : STExpIntIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) : STExpIntI d :=
  Step6Gen_ingR6_of_gL d STReg5I
    (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t →
      STExpWardIConcl sz E s t → STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl sz E s t) _
    (fun sz z s t H hDu hHi hDec hW =>
      let r := H (bandFM_STExpDuhEq_to_gL sz (STflowE z) s t hDu) ((bandFM_STExpDriftHiConcl sz (STflowE z) s t).1 hHi)
        ((bandFM_STExpDriftDecayConcl sz (STflowE z) s t).1 hDec) ((bandFM_STExpWardIConcl sz (STflowE z) s t).1 hW)
      ⟨(bandFM_STExpIntConcl sz (STflowE z) s t ∅ STSigSame).2 r.1, (bandFM_STExpIntQConcl sz (STflowE z) s t).2 r.2⟩) h

/-- `|E_n| < 2` on the band flow (`|E| ≤ |Re z| ≤ 2 - κ`; the band `st6_flowE_lt_two`, `Step6Kit:282`, is not imported). -/
private theorem Step6Gen_flowE_lt_two {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : |STflowE z n| < 2 := by
  have h := hz.2 n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) h.2.1
  have h2 : |lemE (z n)| < 2 := by linarith [(abs_lemE_le him).trans h.1]
  exact h2

/-- The eventual twins `STExpDuhamelZgL`, `STExpDuhamelQgL`: the band pins (`∀ n`, `|E| < 2`) give the generic ones at the band tuple (one direction, `3 ≤ d` as in the band pin; `|E_n| < 2` from the flow). -/
theorem STExpDuhamelZ_to_gL (hd : 3 ≤ d) (h : STExpDuhamelZ d) :
    STExpDuhamelZgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow
  refine Filter.Eventually.of_forall fun n => ?_
  intro s t hs hst ht σ A a
  have := h hd sz n (STflowE z n) (Step6Gen_flowE_lt_two d hκ hflow n) s t hs hst ht σ A a
  simp only [bandStep2_Ugen] at this
  exact this

theorem STExpDuhamelQ_to_gL (hd : 3 ≤ d) (h : STExpDuhamelQ d) :
    STExpDuhamelQgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow
  refine Filter.Eventually.of_forall fun n => ?_
  intro Cq c ϑ hϑ s t hs hst ht σ a
  have := h hd sz n (STflowE z n) (Step6Gen_flowE_lt_two d hκ hflow n) Cq c ϑ hϑ s t hs hst ht σ a
  simp only [bandStep2_Ugen, bandFM_STExpQsrc] at this
  exact this

end IngredientBridge

end RBM.BA

namespace RBM.BA

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Gauss.Step6Inst

/-! ## 7. Compiled nonempty instances at `d = 3`

Data (merged, `Step6Pins` §8; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`): regime (i) `(szB, zB, 7/8, 15/16)`, (ii) `(szB, zB, 15/16, 31/32)`, (iii) and the general statement
`(sz0, z0, 0, 1/16)`, (iv) `(szG, zB, 5/8, 3/4)`.  Deterministic hypotheses are discharged; what stays a hypothesis is a pin of another row (generic pins,
the Duhamel pins of row b, the stochastic premises at `s`). -/

section Instances

/-- Target 1: the vocabulary at `(sz0, z0, n = 0, u = 1/32)`, the loop `((+,-), (0, e₁))`. -/
example (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ) :
    sz0.STExpErr 0 (STflowE z0 0) (1 / 32) ![true, false] ![0, Pi.single 0 1] =
      STExpErrg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] ∧
    sz0.STExpELKLK 0 (STflowE z0 0) (1 / 32) ![true, false] ![0, Pi.single 0 1] =
      STExpELKLKg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] ∧
    sz0.STExpEGt 0 (STflowE z0 0) (1 / 32) ![true, false] ![0, Pi.single 0 1] =
      STExpEGtg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] ∧
    sz0.STExpDrift 0 (STflowE z0 0) (1 / 32) ![true, false] ![0, Pi.single 0 1] =
      STExpDriftg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] ∧
    sz0.STExpQsrc 0 (STflowE z0 0) (1 / 32) ![true, false] ϑ =
      STExpQsrcg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) 0 (1 / 32) ![true, false] ϑ :=
  ⟨bandFM_STExpErr sz0 (STflowE z0) 0 _ _ _, bandFM_STExpELKLK sz0 (STflowE z0) 0 _ _ _,
    bandFM_STExpEGt sz0 (STflowE z0) 0 _ _ _, bandFM_STExpDrift sz0 (STflowE z0) 0 _ _ _,
    bandFM_STExpQsrc sz0 (STflowE z0) 0 _ _ ϑ⟩

/-- Target 2: the target, `STStep2CoregL`, the conclusion at `(sz0, z0, 0, 1/16)`, the endpoint `u = t`. -/
example : (STExp2U sz0 (STflowE z0) sInst tInst ↔ STExp2UgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) ∧
    (STStep2Core sz0 (STflowE z0) sInst tInst ↔ STStep2CoregL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) ∧
    (STStep6Concl sz0 (STflowE z0) sInst tInst ↔ STStep6ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) :=
  ⟨bandFM_STExp2U sz0 (STflowE z0) sInst tInst, bandFM_STStep2Core sz0 (STflowE z0) sInst tInst,
    bandFM_STStep6Concl sz0 (STflowE z0) sInst tInst⟩

example (h : STExp2UgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) :
    STExp2gL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst :=
  STExp2gL_of_STExp2UgL _ _ (fun n => (sz0_hst n).le) h

example := STExp2UgL_iff (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst

example := STStep6R_iff_gL 3 STReg5III

/-- Target 2: the general pin gives each regime pin; at the data of regime (iii) it is the band instance `inst_step6III`. -/
example (h : STStep6gL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  inst_step6III ((STStep6III_iff_gL 3).2 (ST_step6R_of_anygL h STReg5III))

/-- Target 4 bridges of the four regime pins and the general pin, at the data of their regimes. -/
example (h : STStep6IgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I ((STStep6I_iff_gL 3).2 h)

example (h : STStep6IIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_step6II ((STStep6II_iff_gL 3).2 h)

example (h : STStep6IVgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_step6IV ((STStep6IV_iff_gL 3).2 h)

example (h : STStep6gL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  inst_step6 ((STStep6_iff_gL 3).2 h)

example (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (h : STIngR6gL 3 STReg5I (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z s t => Concl sz (STflowE z) s t)) :
    InstIng6Concl Concl szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I Concl ((STIngR6_iff_gL 3 STReg5I Concl).2 h) szB_reg5I

/-- Target 3 / 4: the ingredient texts and their bridges at the data of their regimes (the band pins of `d = 3` are the generic ones at the band tuple). -/
example (h : STImproveExpAvergL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hA : LWAvgLawgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst)
    (hK : STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst) :
    STExpAvgAtgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst :=
  inst_improveExpAver ((STImproveExpAver_iff_gL 3).2 h) hA hK

example (h : STExpDriftLogL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) szG zB
      (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_expDriftLo ((STExpDriftLo_iff_gL 3).2 h)

example (h : STExpDriftDecaygL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpDriftDecayConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_expDriftDecay ((STExpDriftDecay_iff_gL 3).2 h)

example (h : STExpWardIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_expWardI ((STExpWardI_iff_gL 3).2 h)

example (h : STExpWardIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_expWardII ((STExpWardII_iff_gL 3).2 h)

example (h : STExpIniIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpIniIConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_expIniI ((STExpIniI_iff_gL 3).2 h)

/-- The four integrated pins: the generic pin gives the band pin (the eventual twins, one direction), applied at the data of each regime. -/
example (h : STExpIntIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpDriftDecayConcl sz E s t → STExpWardIConcl sz E s t →
      STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_expIntI (STExpIntI_of_gL 3 h)

example (h : STExpIntIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_expIntII (STExpIntII_of_gL 3 h)

example (h : STExpIntIIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) sz0 z0 sInst tInst :=
  inst_expIntIII (STExpIntIII_of_gL 3 h)

example (h : STExpIntIVgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t →
      STExpIntConcl sz ∅ STSigAll E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_expIntIV (STExpIntIV_of_gL 3 h)

/-- The conclusions at the data: the integrated estimate, the initial term, the Ward terms, the drift bounds (`Iff.rfl` or through `bandStep2_Ugen`,
`Θ^{(2)}`), and the Duhamel identity along `[0, 1/16]` (band `∀ n` to generic eventual). -/
example : STExpIntConcl sz0 ∅ STSigAll (STflowE z0) sInst tInst ↔
    STExpIntConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) ∅ STSigAll sInst tInst :=
  bandFM_STExpIntConcl sz0 (STflowE z0) sInst tInst ∅ STSigAll

example : STExpIntQConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ↔
    STExpIntQConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  bandFM_STExpIntQConcl szB (STflowE zB) _ _

example : STExpIniIConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ↔
    STExpIniIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  bandFM_STExpIniIConcl szB (STflowE zB) _ _

example : STExpWardIConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ↔
    STExpWardIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  bandFM_STExpWardIConcl szB (STflowE zB) _ _

example : STExpWardIIConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ↔
    STExpWardIIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  bandFM_STExpWardIIConcl szB (STflowE zB) _ _

example : STExpDriftLoConcl szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4) ↔
    STExpDriftLoConclgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  bandFM_STExpDriftLoConcl szG (STflowE zB) _ _

example : STExpDriftHiConcl sz0 (STflowE z0) sInst tInst ↔
    STExpDriftHiConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STExpDriftHiConcl sz0 (STflowE z0) sInst tInst

example : STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ↔
    STExpDriftDecayConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  bandFM_STExpDriftDecayConcl szB (STflowE zB) _ _

example : STExpAvgU sz0 (STflowE z0) sInst tInst ↔
    STExpAvgUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst := bandFM_STExpAvgU sz0 (STflowE z0) sInst tInst

example : STExpAvgAt sz0 (STflowE z0) tInst ↔ STExpAvgAtgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst :=
  bandFM_STExpAvgAt sz0 (STflowE z0) tInst

example : STExpLKLKHiConcl sz0 (STflowE z0) sInst tInst ↔
    STExpLKLKHiConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STExpLKLKHiConcl sz0 (STflowE z0) sInst tInst

example : STExpEGtHiConcl sz0 (STflowE z0) sInst tInst ↔
    STExpEGtHiConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STExpEGtHiConcl sz0 (STflowE z0) sInst tInst

example (h : STExpDuhEq sz0 (STflowE z0) sInst tInst) :
    STExpDuhEqgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STExpDuhEq_to_gL sz0 (STflowE z0) sInst tInst h

example (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (sz0.L n)) → ℂ) :
    STExpDuhEqQ sz0 (STflowE z0) sInst tInst ϑ ↔
      STExpDuhEqQgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst ϑ :=
  bandFM_STExpDuhEqQ sz0 (STflowE z0) sInst tInst ϑ

/-- The eventual twins `STExpDuhamelZgL`, `STExpDuhamelQgL` from the band pins (one direction, `d = 3`). -/
example (h : STExpDuhamelZ 3) :
    STExpDuhamelZgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) :=
  STExpDuhamelZ_to_gL 3 (by norm_num) h

example (h : STExpDuhamelQ 3) :
    STExpDuhamelQgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) :=
  STExpDuhamelQ_to_gL 3 (by norm_num) h

end Instances

end RBM.BA

end
