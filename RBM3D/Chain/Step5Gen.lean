/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Induction.Step5Pins

/-!
# The Step 5 vocabulary and pins over the carrier (BA-U row U6, ticket T2458)

Additive restatement of the vocabulary and pins of `Induction/Step5Pins.lean` (sections 2 to 6, not edited) over a
carrier `C : FlowFM sz` and a law `μ`, on the one kernel `Step2Gen_UN` of `Chain/Step2Gen.lean`
(supervisor 1152 U-C4: no kernel, no propagator and no second kernel bridge are defined here; the older
kernel is reached only through the merged bridge of `Chain/GridDuhamelGen.lean`).  Paper: arXiv:2507.20274,
Step 5 is `1_2:1379-1388`, its proof `3_5:1935-2383`.

* **Conclusions.** `STDecayStrongUgL`, `STStep5ConclgL` (the conclusion of Step 5); `STEtermsMidConclgL`,
  `STIniTermConclgL`, `STDuhamelConclgL`, `STWardIIConclgL` (cases (i)-(ii)); `STPfConclgL` (case (iii)).
* **Vocabulary.** `STLK2g`, `STELKLKg`.
* **Matrix level.** `STNewKLKLAtgL'`, `STNewKLKLgL'` (`lem:newKLK` at `ℓ = L`, with the datum `κ ≤ Im m` of the family
  in place of the energy window, as `STNewKLKgL'` of `Chain/NewKLKGen.lean`) and `STTailtoTailConclgL`,
  `STTailtoTailgL'` (`TailtoTail` for the kernel `Step2Gen_UN`).  The theorems `stNewKLKLgL'_band`,
  `stTailtoTailgL'_band` run from the band pins to the generic ones.
* **The shape.** `STIngR5gL d R law Flow mk T0 Concl` is the shape of every Step-5 pin over the carrier tuple
  `(law, Flow, mk, T0)` of `STMainIndG`; the Steps 3-4 premises are written inline (conjuncts 2 and 3 of `twSteps`).
  `STStep5RgL`, `STStep5IgL` to `STStep5gL` and the wrapped case pins `STEtermsMidgL`, `STDuhamelIgL`, `STIniTermIgL`,
  `STDuhamelIIgL`, `STIniTermIIgL`, `STWardIIgL`, `STPfStep5gL`.
* **Bridges.** `bandFM_<band name>` for the conclusions and `<band name>_iff_gL` for the pins.  The size-level names
  (`STReg5I`, ..., `STIdx2`, `STtailTD`, `STAI`, `STprof`, ...) are reused as they are.

Nothing here states or imports the cancellation pins of case (i) (owner: row X1a).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The Step-5 conclusion (`(Eq:Gdecay_flow)`, `(Eq:Gdecay+s<g_flow)`) -/

/-- **`(Eq:Gdecay+s<g_flow)`** (`1_2:1384`) over a carrier `C` and a law `μ`, uniformly in `u ∈ [s,t]`, at the sizes with
`lam² ≤ 1 - t`: `|𝓛^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})² e^{-|a₁-a₂|^{1/2}} + W^{-D}`. -/
def STDecayStrongUgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ
      (U := fun n => {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => ‖C.L n (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - C.K n (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1.1 : ℝ)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2.2 0 - p.1.2.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Step 5 of `lem:main_ind`** (`1_2:1379-1388`) over a carrier: `(Eq:Gdecay_flow)` is `STGdecayWgL` with the loss
exponent `0` (no factor `((1-s)/(1-u))^{C_d}`) and `(Eq:Gdecay+s<g_flow)` is `STDecayStrongUgL`. -/
def STStep5ConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  STGdecayWgL C μ s t 0 ∧ STDecayStrongUgL C μ s t

/-! ## 2. Model-level vocabulary -/

/-- `|(𝓛 - 𝒦)^{(2)}_{u,σ,a}|` at the single time `u` of the carrier. -/
def STLK2g {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  ‖C.L n u σ a ω - C.K n u σ a‖

/-- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}` of the carrier (`(def_ELKLK)`, `3_5:98`):
`W^d Σ_{x,y} (𝓛-𝒦)_{u,σ,(x,a₁)} S_{xy} (𝓛-𝒦)_{u,σ,(a₀,y)}`, `S` the kernel `C.S` of the carrier. -/
def STELKLKg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    (C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]) * C.S n x y *
      (C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y])

/-! ## 3. The conclusions of cases (i)-(iii) on the one kernel -/

/-- **`(S5WG+M000)` and `(S5WG+M)`** (`3_5:1968-1979`) over a carrier: the three error terms of `(int_K-LcalE_n=2)` at
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

/-- **The initial term** `𝒰^{(2)}_{s,u,σ} ∘ (𝓛-𝒦)^{(2)}_{s,σ}` (`(iksjuwjx0)` `3_5:2072`; `(zYU2)` `3_5:2269`) over a
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

/-- **The integrated hierarchy at `n = 2`** (`(int_K-LcalE_n=2)` `3_5:1942-1948`, `(iois-mtx)`..`(iois-mtx2)`
`3_5:2046-2069`) over a carrier, conditional on a deterministic control `F` of the initial term; the kernel is
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

/-- **`(zYU1)`** (`3_5:2257-2262`) over a carrier, `σ₁ ≠ σ₂`: the Ward term, with `C.eta`. -/
def STWardIIConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2P sz STSigMixed s t)
    (fun n p ω => ‖(C.L n (p.1 : ℝ) p.2.1.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1.1 p.2.2) -
      zeroModeSet d (sz.L n) {0}
        (fun a' => C.L n (p.1 : ℝ) p.2.1.1 a' ω - C.K n (p.1 : ℝ) p.2.1.1 a') p.2.2‖)
    (fun n p _ => (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * C.eta n (p.1 : ℝ))⁻¹)

/-- **`lem:pf_step5`** (`3_5:2371-2383`) over a carrier, at the sequence level; the index set is empty unless
`lam² ≤ 1 - t`. -/
def STPfConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ
      (U := fun n => {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => STLK2g C n (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω)
      (fun n p _ => STtailTD sz n (p.1.1 : ℝ) D p.1.2.2)

/-! ## 4. `lem:newKLK` at `ℓ = L` and `TailtoTail`, primed -/

/-- **`lem:newKLK` at `ℓ = L`, sharp form** (`(i2kk2zgg)` `3_5:628-651` with `ℓ = L`), primed: the premise on the energy
window of the older statement is replaced by the datum `κ ≤ Im m` of the family `mk` at the constant sequence `fun _ => E`
(the shape of `STNewKLKAtgL'`, `Chain/NewKLKGen.lean:58`). -/
def STNewKLKLAtgL' (d : ℕ) (κ 𝔡 Ck δ₀ : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
    0 ≤ u → u < 1 → 0 ≤ D →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg (mk sz (fun _ => E)) n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STELKLKMg (mk sz (fun _ => E)) n u H σ a‖ ≤
          Ck / (1 - u) * (STJhatMg (mk sz (fun _ => E)) n D ((sz.L n : ℕ) : ℝ) u H ^ 2 *
              STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
            STJhatMg (mk sz (fun _ => E)) n D ((sz.L n : ℕ) : ℝ) u H * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **`lem:newKLK` at `ℓ = L`, the pin, primed** (the constants depend on `d, κ, 𝔡` only). -/
def STNewKLKLgL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Ck δ₀ : ℝ, 0 < Ck ∧ 0 < δ₀ ∧ STNewKLKLAtgL' d κ 𝔡 Ck δ₀ mk

/-- **`TailtoTail`**, `(neiwuj)` (`3_5:2344-2362`), for the one kernel `Step2Gen_UN C` at size index `n`: for
`0 ≤ s ≤ t < 1` and `|A_b| ≤ T_{s,D}(|b₁-b₂|)`, `|(𝒰^{(2)}_{s,t,σ} ∘ A)_a| ≤ Cc T_{t,D}(|a₁-a₂|) + ((1-s)/(1-t))² W^{-D}`. -/
def STTailtoTailConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (Cc D s t : ℝ) : Prop :=
  ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ b, ‖A b‖ ≤ tailTD d ((sz.W n : ℕ) : ℝ) s D (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) →
    ∀ a, ‖Step2Gen_UN C n σ s t A a‖ ≤
      Cc * tailTD d ((sz.W n : ℕ) : ℝ) t D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
        ((1 - s) / (1 - t)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **`TailtoTail`, the pin, primed**: the constant `Cc` depends on `κ` only; the spectral datum is `κ ≤ Im m` of the family
(with `0 < lam` and `lam² ≤ 1 - t`). -/
def STTailtoTailgL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → FlowFM sz) : Prop :=
  3 ≤ d → ∀ κ : ℝ, 0 < κ → ∃ Cc : ℝ, 0 < Cc ∧
    ∀ (sz : Sizes d) (n : ℕ) (E D s t : ℝ), 0 < sz.lam n → κ ≤ ((mk sz (fun _ => E)).m n).im →
      0 ≤ s → s ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t →
        STTailtoTailConclgL (mk sz (fun _ => E)) n Cc D s t

/-! ## 5. The shape of a Step-5 pin over the carrier, and Step 5 per regime -/

/-- **A Step-5 pin over a carrier tuple `(law, Flow, mk, T0)`** (the shape of `STIngR5`; the tuple of `STMainIndG` and
`STStep2G`): the setting of `lem:main_ind` with Steps 1-4 on `[s,t]`, the induction hypothesis at `s` and `(con_st_ind)`,
a regime `R`, and the conclusion `Concl` about `(sz, z, s, t)`.  The Steps 1-2 premises are the carrier pins
`STKboundgL`, `STKwardgL`, `STLKgL`, `STDecaygL`, `STDecayStronggL`, `STStep1LoopgL`, `STStep2ConclgL`; the Steps 3-4
premises are written inline (they are conjuncts 2 and 3 of `twSteps`). -/
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

/-- **Step 5, the four regimes and the general statement** (`Step5Pins.lean:453-463`). -/
def STStep5IgL : Prop := STStep5RgL d STReg5I law Flow mk T0
def STStep5IIgL : Prop := STStep5RgL d STReg5II law Flow mk T0
def STStep5IIIgL : Prop := STStep5RgL d STReg5III law Flow mk T0
def STStep5IVgL : Prop := STStep5RgL d STReg5IV law Flow mk T0
def STStep5gL : Prop := STStep5RgL d STAny law Flow mk T0

/-- **The wrapped case pins**: `(S5WG+M000)`, `(S5WG+M)`, the integrated hierarchy, the initial term, `(zYU1)` and
`lem:pf_step5` as Step-5 pins over the carrier tuple. -/
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

theorem bandFM_STDecayStrongU :
    STDecayStrongU sz E s t ↔ STDecayStrongUgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STStep5Concl :
    STStep5Concl sz E s t ↔ STStep5ConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STLK2 (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STLK2 sz n (E n) u σ a ω = STLK2g (bandFM sz E) n u σ a ω := rfl

theorem bandFM_STELKLK (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STELKLK sz n (E n) u σ a ω = STELKLKg (bandFM sz E) n u σ a ω := rfl

theorem bandFM_STEtermsMidConcl :
    STEtermsMidConcl sz E s t ↔ STEtermsMidConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STWardIIConcl :
    STWardIIConcl sz E s t ↔ STWardIIConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

theorem bandFM_STPfConcl :
    STPfConcl sz E s t ↔ STPfConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

/-- The initial term: proved through `bandStep2_Ugen` (the kernel under the `Prec` binder), nothing else. -/
theorem bandFM_STIniTermConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) :
    STIniTermConcl sz Q P E s t ↔ STIniTermConclgL (bandFM sz E) (Sizes.seqP sz) Q P s t := by
  unfold STIniTermConcl STIniTermConclgL
  simp only [bandStep2_Ugen]
  exact Iff.rfl

/-- The integrated hierarchy: proved through `bandStep2_Ugen`, nothing else. -/
theorem bandFM_STDuhamelConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConcl sz Q P E s t ↔ STDuhamelConclgL (bandFM sz E) (Sizes.seqP sz) Q P s t := by
  unfold STDuhamelConcl STDuhamelConclgL
  simp only [bandStep2_Ugen]
  exact Iff.rfl

end ConclBridge

/-! ## 7. The band theorems of `lem:newKLK` at `ℓ = L` and `TailtoTail` -/

/-- The energy window from the bulk datum: `κ ≤ Im m(E)` gives `|E| ≤ 2 - κ²` (`mE_im`; `κ ≤ 1` is automatic since
`Im m ≤ 1`). -/
private theorem Step5Gen_abs_le_of_im {κ E : ℝ} (hκ : 0 < κ) (h : κ ≤ (mE E).im) : |E| ≤ 2 - κ ^ 2 := by
  rw [mE_im] at h
  have h0 : 0 < Real.sqrt (4 - E ^ 2) := by linarith
  have h1 : 0 < 4 - E ^ 2 := Real.sqrt_pos.1 h0
  have h2 : 2 * κ ≤ Real.sqrt (4 - E ^ 2) := by linarith
  have h3 : (2 * κ) ^ 2 ≤ 4 - E ^ 2 := by
    have h4 := Real.sq_sqrt h1.le
    nlinarith [Real.sqrt_nonneg (4 - E ^ 2)]
  have hk1 : κ ^ 2 ≤ 1 := by nlinarith [sq_nonneg E]
  refine abs_le_of_sq_le_sq ?_ (by linarith)
  nlinarith [sq_nonneg (κ ^ 2)]

/-- **`lem:newKLK` at `ℓ = L`, band to generic** (target 6): the band pin `STNewKLKL` gives `STNewKLKLgL'` at the band
family.  The band pin is applied at the margin `κ²` (`κ ≤ Im m(E)` gives `|E| ≤ 2 - κ²`); the matrix-level objects of
the family at the band are the band objects (`bandStep2_STELKLKM`, `bandStep2_STJhatM`, `bandStep2_STGMM` are `rfl`). -/
theorem stNewKLKLgL'_band (d : ℕ) (h : STNewKLKL d) :
    STNewKLKLgL' d (fun sz E => bandStep2Mat sz E) := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨Ck, δ₀, hC, hδ, hAt⟩ := h hd (κ ^ 2) 𝔡 (by positivity) h𝔡
  refine ⟨Ck, δ₀, hC, hδ, ?_⟩
  intro sz n E u D hlam hlam' hIm hu0 hu1 hD H hH hGM σ a
  have hE : |E| ≤ 2 - κ ^ 2 := Step5Gen_abs_le_of_im hκ hIm
  exact hAt sz n E u D hlam hlam' hE hu0 hu1 hD H hH hGM σ a

/-- **`TailtoTail`, band to generic** (target 7): the band pin `STTailtoTail` gives `STTailtoTailgL'` at the band carrier
(`κ ≤ Im m(E)` and `0 < κ` give `|E| ≤ 2`, hence `‖m(E)‖ = 1`; the kernel `Step2Gen_UN` at the band is the band kernel by
`Step2Kern_UN_band`, with the charges `m(σ_i)`).  Not claimed at the block Anderson carrier: the band proof uses
the row-sum identity at `‖m‖ = 1`. -/
theorem stTailtoTailgL'_band (d : ℕ) (h : STTailtoTail d) :
    STTailtoTailgL' d (fun sz E => bandFM sz E) := by
  intro hd κ hκ
  obtain ⟨Cc, hC, H⟩ := h hd
  refine ⟨Cc, hC, ?_⟩
  intro sz n E D s t hlam hIm hs hst ht hlt σ A hA a
  have hE : |E| ≤ 2 :=
    (Step5Gen_abs_le_of_im hκ hIm).trans (by nlinarith [sq_nonneg κ])
  have hm : ‖mE E‖ = 1 := norm_mE hE
  have key := H (sz.L n) (sz.three_le_L n) (sz.lam n) (((sz.W n : ℕ) : ℝ)) D s t hlam
    (Nat.cast_pos.2 (sz.W_pos n)) hs hst ht hlt (mE E) hm σ A hA a
  have e : Step2Gen_UN (bandFM sz (fun _ => E)) n σ s t A =
      RBM.UN d (sz.L n) (sz.lam n) (EKsgn (mE E) σ) s t A :=
    Step2Kern_UN_band sz (fun _ => E) n 2 σ s t A
  rw [e]
  exact key

/-! ## 8. The shape `STIngR5gL` and the band bridges of the pins -/

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

/-- **Target 8 bridge**: for every band conclusion `Concl`, `STIngR5 d R Concl` is `STIngR5gL` at the band tuple with the
conclusion `fun sz z s t => Concl sz (STflowE z) s t`. -/
theorem STIngR5_iff_gL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    STIngR5 d R Concl ↔
      STIngR5gL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
        (fun sz z s t => Concl sz (STflowE z) s t) :=
  Step5Gen_ingR5_iff_congr d R Concl _ (fun _ _ _ _ => Iff.rfl)

/-! ## 9. The band bridges of Step 5 per regime and of the wrapped case pins -/

/-- **Target 9 bridge**: `STStep5R` is `STStep5RgL` at the band tuple. -/
theorem STStep5R_iff_gL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    STStep5R d R ↔ STStep5RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d R (fun sz E s t => STStep5Concl sz E s t) _
    (fun sz z s t => bandFM_STStep5Concl sz (STflowE z) s t)

theorem STStep5I_iff_gL (d : ℕ) :
    STStep5I d ↔ STStep5IgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  STStep5R_iff_gL d STReg5I

theorem STStep5II_iff_gL (d : ℕ) :
    STStep5II d ↔ STStep5IIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  STStep5R_iff_gL d STReg5II

theorem STStep5III_iff_gL (d : ℕ) :
    STStep5III d ↔ STStep5IIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  STStep5R_iff_gL d STReg5III

theorem STStep5IV_iff_gL (d : ℕ) :
    STStep5IV d ↔ STStep5IVgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  STStep5R_iff_gL d STReg5IV

theorem STStep5_iff_gL (d : ℕ) :
    STStep5 d ↔ STStep5gL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  STStep5R_iff_gL d STAny

/-- **Target 10 bridges**: the wrapped case pins are the band case pins at the band tuple.  The four rows that read the
kernel go through `bandFM_STIniTermConcl`, `bandFM_STDuhamelConcl`. -/
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

theorem STIniTermI_iff_gL (d : ℕ) :
    STIniTermI d ↔ STIniTermIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d STReg5I (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t) _
    (fun sz z s t => bandFM_STIniTermConcl sz (STflowE z) s t ∅ STSigAll)

theorem STDuhamelII_iff_gL (d : ℕ) :
    STDuhamelII d ↔ STDuhamelIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d STReg5II
    (fun sz E s t => STEtermsMidConcl sz E s t →
      STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t) _
    (fun sz z s t => imp_congr (bandFM_STEtermsMidConcl sz (STflowE z) s t)
      (and_congr (bandFM_STDuhamelConcl sz (STflowE z) s t {0} STSigMixed)
        (bandFM_STDuhamelConcl sz (STflowE z) s t ∅ STSigSame)))

theorem STIniTermII_iff_gL (d : ℕ) :
    STIniTermII d ↔ STIniTermIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d STReg5II
    (fun sz E s t => STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t) _
    (fun sz z s t => and_congr (bandFM_STIniTermConcl sz (STflowE z) s t {0} STSigMixed)
      (bandFM_STIniTermConcl sz (STflowE z) s t ∅ STSigSame))

theorem STWardII_iff_gL (d : ℕ) :
    STWardII d ↔ STWardIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d STReg5II (fun sz E s t => STWardIIConcl sz E s t) _
    (fun sz z s t => bandFM_STWardIIConcl sz (STflowE z) s t)

theorem STPfStep5_iff_gL (d : ℕ) :
    STPfStep5 d ↔ STPfStep5gL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step5Gen_ingR5_iff_congr d STReg5III (fun sz E s t => STPfConcl sz E s t) _
    (fun sz z s t => bandFM_STPfConcl sz (STflowE z) s t)

end RBM.BA

namespace RBM.BA

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst

/-! ## 10. Compiled nonempty instances at `d = 3`

The size data are the merged `szB` (`L = 4`, `W_n = n + 4`, `lam = 1`, flow `zB`) and `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`lam_n = (2(n+1))^{-6}`, flow `z0`, `(s,t) = (0, 1/16)`); case (i) and the window of cases (i)+(ii) at `(7/8, 15/16)`, case (ii)
at `(15/16, 31/32)`, case (iii) at `(0, 1/16)` (the regimes of `Step5Inst`).  In the bridge examples the index sets are nonempty
(`lam² ≤ 1 - t` holds at every `n` for `sz0`).  What stays a hypothesis of an instance is a pin of another row (the wrapped
generic pins, and the band pins `STNewKLKL`, `STTailtoTail`, proved in files this file cannot import). -/

section Instances

/-- Target 2: the conclusions at `(sz0, z0, 0, 1/16)`. -/
example : STDecayStrongU sz0 (STflowE z0) sInst tInst ↔
    STDecayStrongUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STDecayStrongU sz0 (STflowE z0) sInst tInst

example : STStep5Concl sz0 (STflowE z0) sInst tInst ↔
    STStep5ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STStep5Concl sz0 (STflowE z0) sInst tInst

/-- Target 3: the vocabulary at `(sz0, z0, n = 0, u = 1/32)`. -/
example (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) :
    STLK2 sz0 0 (STflowE z0 0) (1 / 32) σ a ω = STLK2g (bandFM sz0 (STflowE z0)) 0 (1 / 32) σ a ω :=
  bandFM_STLK2 sz0 (STflowE z0) 0 (1 / 32) σ a ω

example (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) :
    STELKLK sz0 0 (STflowE z0 0) (1 / 32) σ a ω = STELKLKg (bandFM sz0 (STflowE z0)) 0 (1 / 32) σ a ω :=
  bandFM_STELKLK sz0 (STflowE z0) 0 (1 / 32) σ a ω

/-- Target 4: the conclusions of cases (i)-(ii) at `(szB, zB)` (the two rows that read the kernel are proved, not `Iff.rfl`). -/
example : STEtermsMidConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ↔
    STEtermsMidConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  bandFM_STEtermsMidConcl szB (STflowE zB) _ _

example : STIniTermConcl szB ∅ STSigAll (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ↔
    STIniTermConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigAll (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  bandFM_STIniTermConcl szB (STflowE zB) _ _ ∅ STSigAll

example : STDuhamelConcl szB ∅ STSigAll (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ↔
    STDuhamelConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigAll (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  bandFM_STDuhamelConcl szB (STflowE zB) _ _ ∅ STSigAll

example : STIniTermConcl szB {0} STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ↔
    STIniTermConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) {0} STSigMixed (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  bandFM_STIniTermConcl szB (STflowE zB) _ _ {0} STSigMixed

example : STDuhamelConcl szB {0} STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ↔
    STDuhamelConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) {0} STSigMixed (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  bandFM_STDuhamelConcl szB (STflowE zB) _ _ {0} STSigMixed

example : STWardIIConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ↔
    STWardIIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  bandFM_STWardIIConcl szB (STflowE zB) _ _

/-- Target 5: `lem:pf_step5` at `(sz0, z0, 0, 1/16)`. -/
example : STPfConcl sz0 (STflowE z0) sInst tInst ↔
    STPfConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STPfConcl sz0 (STflowE z0) sInst tInst

/-- Targets 9-10: the band pins of `d = 3` are the generic pins at the band tuple, and the instances of `Step5Pins` follow
from the generic pins through the bridges (the generic pins stay hypotheses: they are the pins of the rows U4s1-U4s3, U5). -/
example (h : STEtermsMidgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_etermsMid ((STEtermsMid_iff_gL 3).2 h) Cd hCd

example (h : STDuhamelIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_duhamelI ((STDuhamelI_iff_gL 3).2 h) Cd hCd

example (h : STIniTermIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_iniTermI ((STIniTermI_iff_gL 3).2 h) Cd hCd

example (h : STWardIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STWardIIConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_wardII ((STWardII_iff_gL 3).2 h) Cd hCd

example (h : STPfStep5gL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STPfConcl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_pfStep5 ((STPfStep5_iff_gL 3).2 h) Cd hCd

example (h : STDuhamelIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t →
      STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_duhamelII ((STDuhamelII_iff_gL 3).2 h) Cd hCd

example (h : STIniTermIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)
      szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_iniTermII ((STIniTermII_iff_gL 3).2 h) Cd hCd

/-- Target 8: the bridge at `d = 3`, for every band conclusion, and the instance of `Step5Pins` (`inst_ing5_I`: the flow
`zB`, the sizes `szB`, `(s,t) = (7/8, 15/16)` of case (i), `(con_st_ind)` for every `𝔠d > 0`) from the generic pin. -/
example (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (h : STIngR5gL 3 STReg5I (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z s t => Concl sz (STflowE z) s t))
    (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl Concl szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_ing5_I STReg5I Concl ((STIngR5_iff_gL 3 STReg5I Concl).2 h) szB_reg5I Cd hCd

/-- Target 9: the per-regime bridge at the window of cases (i)+(ii) (the regime `STReg5Mid` has no named Step-5 pin). -/
example : STStep5R 3 STReg5Mid ↔ STStep5RgL 3 STReg5Mid (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  STStep5R_iff_gL 3 STReg5Mid

/-- Target 9: Step 5 in the four regimes and in general, at `d = 3` (the bridges are the equivalences themselves). -/
example : STStep5I 3 ↔ STStep5IgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep5I_iff_gL 3

example : STStep5II 3 ↔ STStep5IIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep5II_iff_gL 3

example : STStep5III 3 ↔ STStep5IIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep5III_iff_gL 3

example : STStep5IV 3 ↔ STStep5IVgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep5IV_iff_gL 3

example : STStep5 3 ↔ STStep5gL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STStep5_iff_gL 3

/-- The band carrier at `sz0`, `E ≡ 0`, and the matrix `H = 0` at `n = 0`. -/
private abbrev Step5Gen_cm0 : Step2Mat sz0 := bandStep2Mat sz0 (fun _ => 0)

private abbrev Step5Gen_H0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ := 0

/-- `Im m(0) = 1 ≥ 1/10`. -/
private theorem Step5Gen_im_zero : (1 / 10 : ℝ) ≤ ((bandStep2Mat sz0 fun _ => 0).m 0).im := by
  change (1 / 10 : ℝ) ≤ (mE 0).im
  rw [mE_im]
  have h2 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h2]; norm_num

/-- **Target 6, instantiated**: `stNewKLKLgL'_band` at `sz0`, `n = 0`, `E = 0` (`Im m(0) = 1 ≥ κ = 1/10`), `u = 0`, `D = 1`,
`ℓ = L = 4` and `H = 0` (Hermitian, `‖G_0 - M‖_max = 0 ≤ δ₀`): the constants of the generic pin, then the sharp bound. -/
example (h : STNewKLKL 3) :
    ∃ Ck δ₀ : ℝ, 0 < Ck ∧ 0 < δ₀ ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STELKLKMg Step5Gen_cm0 0 0 Step5Gen_H0 σ a‖ ≤
        Ck / (1 - 0) * (STJhatMg Step5Gen_cm0 0 1 ((sz0.L 0 : ℕ) : ℝ) 0 Step5Gen_H0 ^ 2 *
            STprof sz0 0 0 1 ((sz0.L 0 : ℕ) : ℝ) (a 0) (a 1) +
          STJhatMg Step5Gen_cm0 0 1 ((sz0.L 0 : ℕ) : ℝ) 0 Step5Gen_H0 * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ *
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨Ck, δ₀, hC, hδ, hAt⟩ := stNewKLKLgL'_band 3 h (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  refine ⟨Ck, δ₀, hC, hδ, fun σ a => ?_⟩
  exact hAt sz0 0 0 0 1 hlam hlam' Step5Gen_im_zero le_rfl one_pos zero_le_one Step5Gen_H0 Matrix.isHermitian_zero
    (fun x y => by
      have h0 : STGMM sz0 0 0 0 Step5Gen_H0 x y = 0 :=
        Step2DefsInst.STGMM_zero sz0 0 (E := 0) (by norm_num) x y
      have h1 : STGMMg Step5Gen_cm0 0 0 Step5Gen_H0 x y = 0 := h0
      rw [h1]; simpa using hδ.le) σ a

/-- **Target 7, instantiated**: `stTailtoTailgL'_band` at `sz0`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`), `E = 0`
(`Im m(0) = 1 ≥ κ = 1/10`), `D = 2`, `s = 1/2`, `t = 3/4` (`lam² = 1/4096 ≤ 1/4 = 1 - t`), `σ = (+,-)` and the
extremal tensor `A_b = T_{s,D}(|b₁-b₂|)` (nonzero): every hypothesis of the generic pin is discharged. -/
example (h : STTailtoTail 3) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ a : Fin 2 → Zd 3 (sz0.L 0),
      ‖Step2Gen_UN (bandFM sz0 (fun _ => (0 : ℝ))) 0 ![true, false] (1 / 2 : ℝ) (3 / 4 : ℝ)
          (fun b : Fin 2 → Zd 3 (sz0.L 0) =>
            ((tailTD 3 ((sz0.W 0 : ℕ) : ℝ) (1 / 2 : ℝ) 2 (zdistInf 3 (sz0.L 0) (b 0 - b 1) : ℕ) : ℝ) : ℂ)) a‖ ≤
        Cc * tailTD 3 ((sz0.W 0 : ℕ) : ℝ) (3 / 4 : ℝ) 2 (zdistInf 3 (sz0.L 0) (a 0 - a 1) : ℕ) +
          ((1 - 1 / 2 : ℝ) / (1 - 3 / 4 : ℝ)) ^ 2 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨Cc, hC, H⟩ := stTailtoTailgL'_band 3 h (by norm_num) (1 / 10) (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam2 : sz0.lam 0 ^ 2 ≤ 1 - 3 / 4 := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  refine ⟨Cc, hC, fun a => ?_⟩
  exact H sz0 0 0 2 (1 / 2) (3 / 4) hlam Step5Gen_im_zero (by norm_num) (by norm_num) (by norm_num) hlam2
    ![true, false] _
    (fun b => by rw [Complex.norm_real, Real.norm_of_nonneg (tailTD_nonneg (by norm_num))]) a

end Instances

end RBM.BA

end
