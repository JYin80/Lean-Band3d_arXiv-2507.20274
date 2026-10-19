/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.Graph.LWPins

/-!
# The light-weight statements over a flow carrier

The light-weight observables and hypotheses of `Graph/LWPins` restated over a carrier `C : FlowFM sz`:
`LWcutg`, `LWEg`, `LWAvgLawgL`, `LWLoop2gL`, `LWAssmgL`, `LWLoopExpgL`, `LWAssmExpgL`; and, in the shape
`(law, Flow, mk, T0)` of `STMainIndG`, the two bounds `LWtermG` (Lemma 3.10, `lem:LWterm`) and
`LWtermExpG` (Lemma 3.11, `lem: EWGn2_N`).  The statements `STEGtg`, `STLWassmgL`, `STLWBgL`,
`STLWTgL`, `STEMn2ExpgL` over a carrier are in `Chain/Step2Gen`.  `PinFam` is the type of
statements of the shape `(d, law, Flow, mk, T0)`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

section Generic
variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-! ## 1. The light-weight observables and hypotheses over the carrier -/

/-- `LWcut` (`Graph/LWPins`) over the carrier (kernel `C.S`, loops `C.L`, one-loop value `C.m`). -/
def LWcutg (n : ℕ) (t : ℝ) (σc σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, C.S n a₁ a₂ *
    (C.L n t ![σc] ![a₁] ω - (if σc then C.m n else (starRingEnd ℂ) (C.m n))) * C.L n t ![σc, σc, σo] ![a₂, ac, ao] ω

/-- `LWE` (`Graph/LWPins`) over the carrier. -/
def LWEg (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  LWcutg C n t (σ 1) (σ 0) (a 1) (a 0) ω + LWcutg C n t (σ 0) (σ 1) (a 0) (a 1) ω

/-- (2.88) `Gt_avgbound_flow`, `LWAvgLaw` (`Graph/LWPins`). -/
def LWAvgLawgL (t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Zd d (sz.L n))
    (fun n a ω => ‖C.L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - C.m n‖) (fun n _ _ => sz.Bctl n (t n))

/-- (3.27) `eq:LW_assm`, `LWLoop2` (`Graph/LWPins`). -/
def LWLoop2gL (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖C.L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
    (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2)

/-- `LWAssm` (`Graph/LWPins`): the window, (3.4) `initialGT2`, the class and (3.27) `eq:LW_assm`. -/
def LWAssmgL (t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL C μ t ε₀ Ψ ∧ LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    LWLoop2gL C μ t Φ

/-- (3.31) `eq:LW_assm_exp` (`Graph/LWPins`). -/
def LWLoopExpgL (t ℓ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖C.L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
        ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ))

/-- `LWAssmExp` (`Graph/LWPins`). -/
def LWAssmExpgL (t : ℕ → ℝ) (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL C μ t ε₀ Ψ ∧ (∀ n, 0 ≤ ℓ n) ∧
    (∀ n, ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) (t n)) ∧ LWLoopExpgL C μ t ℓ

/-! ### The statements in the shape of `STMainIndG`: law, flow setting, carrier, horizon -/

/-- Lemma 3.10 (`lem:LWterm`), the `B`-bound, over a carrier family. -/
def LWtermG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
          LWAssmgL (mk sz z) (law sz) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
          PrecL sz (law sz) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖LWEg (mk sz z) n (t n) p.1 p.2 ω‖)
            (fun n p _ => ((mk sz z).eta n (t n))⁻¹ * Φ n 0 *
              Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2)

/-- Lemma 3.11 (`lem: EWGn2_N`), the `T`-bound, over a carrier family. -/
def LWtermExpG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (mk sz z) (law sz) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            PrecL sz (law sz) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖LWEg (mk sz z) n (t n) p.1 p.2 ω‖)
              (fun n p _ => ((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ)))

end Generic

/-! ## 2. The shape of the statements over a carrier family -/

/-- A statement of the shape `(d, law, Flow, mk, T0)` of `STMainIndG` and `STStep2G`. -/
abbrev PinFam : Type := ∀ d : ℕ, (∀ sz : Sizes d, Measure sz.SeqΩ) → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) →
  (∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) → (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → Prop

end RBM.BA

end
