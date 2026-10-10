/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.Graph.LWPins

/-!
# The generic light-weight pins over the carrier (BA-L0, ticket T2394)

Design `docs/reports/T2387-design.md` §2 (LD2), §6 (row L0); probe `t/T2387:RBM3D/Probe/T2387Pins.lean:39-244`;
rebuilt on the merged `Chain/Step2Gen` (T2386; supervisor 2149 L2).  The light-weight observables and pins of
`Graph/LWPins.lean` are restated over a carrier `C : FlowFM sz` (`LWcutg`, `LWEg`, `LWAvgLawgL`, `LWLoop2gL`,
`LWAssmgL`, `LWLoopExpgL`, `LWAssmExpgL`) and in the `(law, Flow, mk, T0)` shape of `STMainIndG`
(`LWtermG`, `LWtermExpG`, `LWtermEXPG`).  `Step2Gen` already has `STEGtg`, `STLWassmgL`, `STLWBgL`, `STLWTgL`,
`STEMn2ExpgL`: not redefined here.  Every band pin is recovered by `Iff.rfl` over `bandFM` (`Chain/Carrier`).
The imports contain no downstream chain file; the band theorems and the BA readings are in `BA/LWPinsBA`.
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

/-! ## 1. The light-weight observables and pins over the carrier -/

/-- `LWcut` (`Graph/LWPins.lean:211`) over the carrier (kernel `C.S`, loops `C.L`, one-loop value `C.m`). -/
def LWcutg (n : ℕ) (t : ℝ) (σc σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, C.S n a₁ a₂ *
    (C.L n t ![σc] ![a₁] ω - (if σc then C.m n else (starRingEnd ℂ) (C.m n))) * C.L n t ![σc, σc, σo] ![a₂, ac, ao] ω

/-- `LWE` (`LWPins.lean:218`) over the carrier. -/
def LWEg (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  LWcutg C n t (σ 1) (σ 0) (a 1) (a 0) ω + LWcutg C n t (σ 0) (σ 1) (a 0) (a 1) ω

/-- `(Gt_avgbound_flow)`, `LWAvgLaw` (`LWPins.lean:303`). -/
def LWAvgLawgL (t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Zd d (sz.L n))
    (fun n a ω => ‖C.L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - C.m n‖) (fun n _ _ => sz.Bctl n (t n))

/-- `(LW_assm)` (`LWPins.lean:228`). -/
def LWLoop2gL (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖C.L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
    (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2)

/-- `LWAssm` (`LWPins.lean:234`): the window, `(initialGT2)`, the class and `(LW_assm)`. -/
def LWAssmgL (t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL C μ t ε₀ Ψ ∧ LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    LWLoop2gL C μ t Φ

/-- `(LW_assm_exp)` (`LWPins.lean:274`). -/
def LWLoopExpgL (t ℓ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖C.L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
        ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ))

/-- `LWAssmExp` (`LWPins.lean:283`). -/
def LWAssmExpgL (t : ℕ → ℝ) (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL C μ t ε₀ Ψ ∧ (∀ n, 0 ≤ ℓ n) ∧
    (∀ n, ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) (t n)) ∧ LWLoopExpgL C μ t ℓ

/-! ### The generic pins: the shape of `STMainIndG` (`BA/FlowPins.lean:434`): law, flow setting, carrier, horizon -/

/-- `lem:LWterm` (`LWPins.lean:240`), the `B`-bound, over a carrier family. -/
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

/-- `lem: EWGn2_N` (`LWPins.lean:290`), the `T`-bound. -/
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

/-- `lem:LWterm_EXP` (`LWPins.lean:311`): the premises are the generic Step 1/2 pins of `Chain/Carrier`. -/
def LWtermEXPG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        STLocalEntrygL (mk sz z) (law sz) t → LWAvgLawgL (mk sz z) (law sz) t → STLmaxgL (mk sz z) (law sz) t →
        STLKgL (mk sz z) (law sz) t → STDecaygL (mk sz z) (law sz) t →
        PrecL sz (law sz) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWEg (mk sz z) n (t n) p.1.1 p.1.2 ω ∂(law sz)‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

end Generic

/-! ## 2. The family of generic pins and the band instance (`Iff.rfl` bridges) -/

/-- A generic pin of the shape `(d, law, Flow, mk, T0)` of `STMainIndG` (`BA/FlowPins.lean:434`, `Step2Gen.STStep2G`). -/
abbrev PinFam : Type := ∀ d : ℕ, (∀ sz : Sizes d, Measure sz.SeqΩ) → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) →
  (∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) → (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → Prop

/-- Band: law `seqP`, setting `STFlow`, carrier `bandFM`, horizon `lemT` (as `Step2Gen.bandFM_STLWB`). -/
def bandPin (P : PinFam) (d : ℕ) : Prop := P d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
  (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

theorem band_LWE {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) : LWE sz n (E n) t σ a ω = LWEg (bandFM sz E) n t σ a ω := rfl
theorem band_LWAvgLaw {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) :
    LWAvgLaw sz E t ↔ LWAvgLawgL (bandFM sz E) (Sizes.seqP sz) t := Iff.rfl
theorem band_LWAssm {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (C₁ C₂ C₃ : ℝ)
    (Cc : ℝ → ℝ) : LWAssm sz E t ε₀ Ψ Φ C₁ C₂ C₃ Cc ↔ LWAssmgL (bandFM sz E) (Sizes.seqP sz) t ε₀ Ψ Φ C₁ C₂ C₃ Cc :=
  Iff.rfl
theorem band_LWAssmExp {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ) :
    LWAssmExp sz E t ε₀ Ψ ℓ ↔ LWAssmExpgL (bandFM sz E) (Sizes.seqP sz) t ε₀ Ψ ℓ := Iff.rfl
theorem LWterm_iff (d : ℕ) : LWterm d ↔ bandPin LWtermG d := Iff.rfl
theorem LWtermExp_iff (d : ℕ) : LWtermExp d ↔ bandPin LWtermExpG d := Iff.rfl
theorem LWtermEXP_iff (d : ℕ) : LWtermEXP d ↔ bandPin LWtermEXPG d := Iff.rfl
/-- `bandFM_STLWB` (`Step2Gen`) in the `bandPin` form. -/
theorem STLWB_bandPin (d : ℕ) : STLWB d ↔ bandPin STLWBgL d := Iff.rfl
theorem STLWT_bandPin (d : ℕ) : STLWT d ↔ bandPin STLWTgL d := Iff.rfl

end RBM.BA

end
