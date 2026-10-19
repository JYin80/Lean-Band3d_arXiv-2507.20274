/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Induction.Step5Pins

/-!
# The Step 5 vocabulary and statements over the carrier

Restatement of the vocabulary and statements of `Induction/Step5Pins` (sections 2 to 6) over a carrier
`C : FlowFM sz` and a law `μ`, on the one kernel `Step2Gen_UN` of `Chain/Step2Gen`; the band kernel is
reached only through the bridge `bandStep2_Ugen` of `Chain/GridDuhamelGen`.  Paper: Step 5 of
Lemma 2.24 (`lem:main_ind`) is (2.91) `Eq:L-KGt-flow`, (2.92) `Eq:Gdecay_flow`, (2.93)
`Eq:Gdecay+s<g_flow`; its proof is Section 5 (`Sec:Step5`).

* **Conclusions.** `STDecayStrongUgL`, `STStep5ConclgL` (the conclusion of Step 5); `STEtermsMidConclgL`,
  `STIniTermConclgL`, `STDuhamelConclgL`, `STWardIIConclgL` (cases (i)-(ii)); `STPfConclgL` (case (iii)).
* **Vocabulary.** `STLK2g`, `STELKLKg`.
* **Matrix level.** `STTailtoTailConclgL` (Lemma 5.3, `TailtoTail`, for the kernel `Step2Gen_UN`).
* **The shape.** `STIngR5gL d R law Flow mk T0 Concl` is the shape of every Step 5 statement over the
  carrier tuple `(law, Flow, mk, T0)` of `STMainIndG`; the hypotheses from Steps 3-4 are written inline
  (conjuncts 2 and 3 of `twSteps`).  `STStep5RgL`, `STStep5IgL` to `STStep5IVgL` and the wrapped case
  statements `STEtermsMidgL`, `STDuhamelIgL`, `STIniTermIgL`, `STDuhamelIIgL`, `STIniTermIIgL`,
  `STWardIIgL`, `STPfStep5gL`.
* **Bridges.** `bandFM_STEtermsMidConcl`, `bandFM_STDuhamelConcl` for the conclusions and
  `STEtermsMid_iff_gL`, `STDuhamelI_iff_gL`, `STDuhamelII_iff_gL` for the wrapped statements.  The
  size-level names (`STReg5I`, ..., `STIdx2`, `STtailTD`, `STAI`, `STprof`, ...) are reused as they are.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The Step 5 conclusion, (2.92) `Eq:Gdecay_flow` and (2.93) `Eq:Gdecay+s<g_flow` -/

/-- **(2.93) `Eq:Gdecay+s<g_flow`** over a carrier `C` and a law `μ`, uniformly in `u ∈ [s,t]`, at the sizes with
`lam² ≤ 1 - t`: `|𝓛^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})² e^{-|a₁-a₂|^{1/2}} + W^{-D}`. -/
def STDecayStrongUgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ
      (U := fun n => {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => ‖C.L n (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - C.K n (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1.1 : ℝ)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2.2 0 - p.1.2.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Step 5 of Lemma 2.24 (`lem:main_ind`)** over a carrier: (2.92) `Eq:Gdecay_flow` is `STGdecayWgL` with the loss
exponent `0` (no factor `((1-s)/(1-u))^{C_d}`) and (2.93) `Eq:Gdecay+s<g_flow` is `STDecayStrongUgL`. -/
def STStep5ConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  STGdecayWgL C μ s t 0 ∧ STDecayStrongUgL C μ s t

/-! ## 2. Model-level vocabulary -/

/-- `|(𝓛 - 𝒦)^{(2)}_{u,σ,a}|` at the single time `u` of the carrier. -/
def STLK2g {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  ‖C.L n u σ a ω - C.K n u σ a‖

/-- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}` of the carrier ((3.10) `def_ELKLK`):
`W^d Σ_{x,y} (𝓛-𝒦)_{u,σ,(x,a₁)} S_{xy} (𝓛-𝒦)_{u,σ,(a₀,y)}`, `S` the kernel `C.S` of the carrier. -/
def STELKLKg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    (C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]) * C.S n x y *
      (C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y])

/-! ## 3. The conclusions of cases (i)-(iii) on the one kernel -/

/-- **(5.4) `S5WG+M000` and (5.5) `S5WG+M`** over a carrier: the three error terms of (5.1) `int_K-LcalE_n=2` at
`ℓ = L` in the window `lam²/L^d ≤ 1-t ≤ 1-s ≤ lam²`, uniformly in `u ∈ [s,t]`, `A = lam² W^d` (`STAI`),
with the spectral datum `C.eta`. -/
def STEtermsMidConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := STIdx2 sz s t)
      (fun n p ω => ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (C.eta n (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    PrecL sz μ (U := STIdx2 sz s t)
      (fun n p ω => ‖STEGtg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (C.eta n (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    PrecL sz μ (U := fun n => STIdx2 sz s t n × Fin 2)
      (fun n p ω => ‖STEEg C n (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (C.eta n (p.1.1 : ℝ))⁻¹ *
        STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2)

/-- **The initial term** `𝒰^{(2)}_{s,u,σ} ∘ (𝓛-𝒦)^{(2)}_{s,σ}` ((5.16) `iksjuwjx0`; (5.40) `zYU2`) over a
carrier, with the kernel `Step2Gen_UN C` and the zero-mode-removing set `Q`; a statement at the time `s` only. -/
def STIniTermConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (Q : Finset (Fin 2))
    (P : (Fin 2 → Bool) → Prop) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => C.L n (s n) p.2.1.1 b ω - C.K n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **The integrated hierarchy at `n = 2`** ((5.1) `int_K-LcalE_n=2`; (5.12) `iois-mtx` to (5.15) `iois-mtx2`)
over a carrier, conditional on a deterministic bound `F` of the initial term; the kernel is
`Step2Gen_UN C`. -/
def STDuhamelConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (Q : Finset (Fin 2))
    (P : (Fin 2 → Bool) → Prop) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ F : ∀ n, STIdx2P sz P s t n → ℝ, (∀ n p, 0 ≤ F n p) →
    PrecL sz μ (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => C.L n (s n) p.2.1.1 b ω - C.K n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p) →
    PrecL sz μ (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (fun a' => C.L n (p.1 : ℝ) p.2.1.1 a' ω - C.K n (p.1 : ℝ) p.2.1.1 a') p.2.2‖)
      (fun n p _ => F n p + (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **(5.37) `zYU1`** over a carrier, `σ₁ ≠ σ₂`: the Ward term, with `C.eta`. -/
def STWardIIConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2P sz STSigMixed s t)
    (fun n p ω => ‖(C.L n (p.1 : ℝ) p.2.1.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1.1 p.2.2) -
      zeroModeSet d (sz.L n) {0}
        (fun a' => C.L n (p.1 : ℝ) p.2.1.1 a' ω - C.K n (p.1 : ℝ) p.2.1.1 a') p.2.2‖)
    (fun n p _ => (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * C.eta n (p.1 : ℝ))⁻¹)

/-- **Lemma 5.4 (`lem:pf_step5`)** over a carrier, at the sequence level; the index set is empty unless
`lam² ≤ 1 - t`. -/
def STPfConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ
      (U := fun n => {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => STLK2g C n (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω)
      (fun n p _ => STtailTD sz n (p.1.1 : ℝ) D p.1.2.2)

/-! ## 4. `TailtoTail` -/

/-- **Lemma 5.3 (`TailtoTail`)**, (5.46) `neiwuj`, for the one kernel `Step2Gen_UN C` at size index `n`: for
`0 ≤ s ≤ t < 1` and `|A_b| ≤ T_{s,D}(|b₁-b₂|)`, `|(𝒰^{(2)}_{s,t,σ} ∘ A)_a| ≤ Cc T_{t,D}(|a₁-a₂|) + ((1-s)/(1-t))² W^{-D}`. -/
def STTailtoTailConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (Cc D s t : ℝ) : Prop :=
  ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ b, ‖A b‖ ≤ tailTD d ((sz.W n : ℕ) : ℝ) s D (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) →
    ∀ a, ‖Step2Gen_UN C n σ s t A a‖ ≤
      Cc * tailTD d ((sz.W n : ℕ) : ℝ) t D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
        ((1 - s) / (1 - t)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D)

/-! ## 5. The shape of a Step 5 statement over the carrier, and Step 5 per regime -/

/-- **A Step 5 statement over a carrier tuple `(law, Flow, mk, T0)`** (the shape of `STIngR5`; the tuple of `STMainIndG` and
`STStep2G`): the setting of Lemma 2.24 (`lem:main_ind`) with Steps 1-4 on `[s,t]`, the induction hypothesis at `s` and
(2.83) `con_st_ind`, a regime `R`, and the conclusion `Concl` about `(sz, z, s, t)`.  The Steps 1-2 hypotheses are
`STKboundgL`, `STKwardgL`, `STLKgL`, `STDecaygL`, `STDecayStronggL`, `STStep1LoopgL`, `STStep2ConclgL`; the Steps 3-4
hypotheses are written inline (they are conjuncts 2 and 3 of `twSteps`). -/
def STIngR5gL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Concl : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STKwardgL (mk sz z) (law sz) →
          STLKgL (mk sz z) (law sz) s → STDecaygL (mk sz z) (law sz) s →
          STDecayStronggL (mk sz z) (law sz) s → STConStInd sz 𝔠d s t →
          STStep1LoopgL (mk sz z) (law sz) s t → STStep2ConclgL (mk sz z) (law sz) s t Cd →
          (∀ k : ℕ, 1 ≤ k → PrecL sz (law sz)
            (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
            (fun n p ω => ‖(mk sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
            (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))) →
          (∀ k : ℕ, 1 ≤ k → PrecL sz (law sz)
            (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
            (fun n p ω => ‖(mk sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω - (mk sz z).K n (p.1 : ℝ) p.2.1 p.2.2‖)
            (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)) →
            Concl sz z s t

/-- **Step 5 under a regime `R`** (`True` for the general statement): `STIngR5gL` with the conclusion `STStep5ConclgL`. -/
def STStep5RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR5gL d R law Flow mk T0 (fun sz z s t => STStep5ConclgL (mk sz z) (law sz) s t)

section Wrapped

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- **Step 5, the four regimes and the general statement** (`STStep5RgL` at `STReg5I` to `STReg5IV`). -/
def STStep5IgL : Prop := STStep5RgL d STReg5I law Flow mk T0
def STStep5IIgL : Prop := STStep5RgL d STReg5II law Flow mk T0
def STStep5IIIgL : Prop := STStep5RgL d STReg5III law Flow mk T0
def STStep5IVgL : Prop := STStep5RgL d STReg5IV law Flow mk T0
/-- **The wrapped case statements**: (5.4) `S5WG+M000`, (5.5) `S5WG+M`, the integrated hierarchy, the initial term, (5.37) `zYU1` and
Lemma 5.4 (`lem:pf_step5`) as Step 5 statements over the carrier tuple. -/
def STEtermsMidgL : Prop :=
  STIngR5gL d STReg5Mid law Flow mk T0 (fun sz z s t => STEtermsMidConclgL (mk sz z) (law sz) s t)
def STDuhamelIgL : Prop :=
  STIngR5gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STEtermsMidConclgL (mk sz z) (law sz) s t → STDuhamelConclgL (mk sz z) (law sz) ∅ STSigAll s t)
def STIniTermIgL : Prop :=
  STIngR5gL d STReg5I law Flow mk T0 (fun sz z s t => STIniTermConclgL (mk sz z) (law sz) ∅ STSigAll s t)
def STDuhamelIIgL : Prop :=
  STIngR5gL d STReg5II law Flow mk T0 (fun sz z s t =>
    STEtermsMidConclgL (mk sz z) (law sz) s t →
      STDuhamelConclgL (mk sz z) (law sz) {0} STSigMixed s t ∧
        STDuhamelConclgL (mk sz z) (law sz) ∅ STSigSame s t)
def STIniTermIIgL : Prop :=
  STIngR5gL d STReg5II law Flow mk T0 (fun sz z s t =>
    STIniTermConclgL (mk sz z) (law sz) {0} STSigMixed s t ∧
      STIniTermConclgL (mk sz z) (law sz) ∅ STSigSame s t)
def STWardIIgL : Prop :=
  STIngR5gL d STReg5II law Flow mk T0 (fun sz z s t => STWardIIConclgL (mk sz z) (law sz) s t)
def STPfStep5gL : Prop :=
  STIngR5gL d STReg5III law Flow mk T0 (fun sz z s t => STPfConclgL (mk sz z) (law sz) s t)

end Wrapped

/-! ## 6. Bridges of the conclusions (band name to generic name) -/

section ConclBridge

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

theorem bandFM_STEtermsMidConcl :
    STEtermsMidConcl sz E s t ↔ STEtermsMidConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

/-- The integrated hierarchy: proved through `bandStep2_Ugen`, nothing else. -/
theorem bandFM_STDuhamelConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConcl sz Q P E s t ↔ STDuhamelConclgL (bandFM sz E) (Sizes.seqP sz) Q P s t := by
  unfold STDuhamelConcl STDuhamelConclgL
  simp only [bandStep2_Ugen]
  exact Iff.rfl

end ConclBridge

/-! ## 7. The shape `STIngR5gL` and the band bridges of the statements -/

/-- The band shape `STIngR5` is `STIngR5gL` at the band tuple `(seqP, STFlow, bandFM ∘ STflowE, lemT)`, for a band
conclusion `Concl` and a generic one `Concl'` that agree pointwise.  The premise `STKward` is the only one that is not
definitionally equal to its carrier form (`bandFM_STKward`); the other premises are `Iff.rfl`. -/
theorem Step5Gen_ingR5_iff_congr (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl' : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), Concl sz (STflowE z) s t ↔ Concl' sz z s t) :
    STIngR5 d R Concl ↔
      STIngR5gL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) Concl' := by
  unfold STIngR5 STIngR5gL
  constructor
  · intro h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
    obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
    refine ⟨𝔠d, h0, h1, fun 𝔠 sz z hf s t hs0 hst ht hR hK hKw hLK hDec hDS hCon hS1 hS2 hLm hLKU => ?_⟩
    exact (hC sz z s t).1 (H 𝔠 sz z hf s t hs0 hst ht hR hK ((bandFM_STKward sz (STflowE z)).2 hKw)
      hLK hDec hDS hCon hS1 hS2 hLm hLKU)
  · intro h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
    obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
    refine ⟨𝔠d, h0, h1, fun 𝔠 sz z hf s t hs0 hst ht hR hK hKw hLK hDec hDS hCon hS1 hS2 hLm hLKU => ?_⟩
    exact (hC sz z s t).2 (H 𝔠 sz z hf s t hs0 hst ht hR hK ((bandFM_STKward sz (STflowE z)).1 hKw)
      hLK hDec hDS hCon hS1 hS2 hLm hLKU)

/-! ## 8. The band bridges of Step 5 per regime and of the wrapped case statements -/

/-- **Bridges**: the wrapped case statements are the band case statements at the band tuple.  The ones that read the
kernel go through `bandFM_STDuhamelConcl`. -/
theorem STEtermsMid_iff_gL (d : ℕ) :
    STEtermsMid d ↔ STEtermsMidgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d STReg5Mid (fun sz E s t => STEtermsMidConcl sz E s t) _
    (fun sz z s t => bandFM_STEtermsMidConcl sz (STflowE z) s t)

theorem STDuhamelI_iff_gL (d : ℕ) :
    STDuhamelI d ↔ STDuhamelIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d STReg5I
    (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t) _
    (fun sz z s t => imp_congr (bandFM_STEtermsMidConcl sz (STflowE z) s t)
      (bandFM_STDuhamelConcl sz (STflowE z) s t ∅ STSigAll))

theorem STDuhamelII_iff_gL (d : ℕ) :
    STDuhamelII d ↔ STDuhamelIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d STReg5II
    (fun sz E s t => STEtermsMidConcl sz E s t →
      STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t) _
    (fun sz z s t => imp_congr (bandFM_STEtermsMidConcl sz (STflowE z) s t)
      (and_congr (bandFM_STDuhamelConcl sz (STflowE z) s t {0} STSigMixed)
        (bandFM_STDuhamelConcl sz (STflowE z) s t ∅ STSigSame)))

end RBM.BA

end
