/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.DecayGen
import RBM3D.BA.TwistPins
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins

/-!
# TLF-C5 and the BA readings of `Chain/Step34Gen` (BA-U row U3s1 leaf, ticket T2457)

A leaf (no module imports it): it may import `BA/`, while `Chain/Step34Gen.lean` may not.

* **TLF-C5 (target 8).** `twSteps` (`BA/TwistPins.lean:133`) is `STStep2ConclgL ∧ STLmaxUgL ∧ STLKUgL ∧ STDecayLoopUgL`
  (conjuncts 2-3 are the pins of `Chain/Step34Gen`, conjunct 4 is T7's `STDecayLoopUgL`, `Chain/DecayGen.lean:66`): the first
  `example` is `Iff.rfl` (supervisor `2026-10-11-1049.md:123-127`), the other two extract conjuncts 2 and 3 (`h.2.1`, `h.2.2.1`).
  They are also applied at concrete data (the band carrier `bandFM sz0 (fun _ => 0)`).
* **BA readings, statement level** (`example : Prop := ...`, proofs owed by U3-BA): targets 1 and 5 at the BA carrier family
  `(law, Flow, mk, T0) = (seqP ∘ withLam 0, BAFlow, baFMz, BAflowT0)`; target 3 at `baStep2Mat` and the flow matrix
  `seqHflowBA (BAflowLam0 sz z)`; `STSEforLngL` at the BA reading.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 8 (TLF-C5): `twSteps` and the pins of `Chain/Step34Gen` -/

/-- `twSteps` is definitionally `STStep2ConclgL ∧ STLmaxUgL ∧ STLKUgL ∧ STDecayLoopUgL`. -/
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ) :
    twSteps C μ s t Cd ↔ (STStep2ConclgL C μ s t Cd ∧ STLmaxUgL C μ s t ∧ STLKUgL C μ s t ∧ STDecayLoopUgL C μ s t) := Iff.rfl

/-- Conjunct 2 of `twSteps` is `STLmaxUgL`. -/
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ) (h : twSteps C μ s t Cd) :
    STLmaxUgL C μ s t := h.2.1

/-- Conjunct 3 of `twSteps` is `STLKUgL`. -/
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ) (h : twSteps C μ s t Cd) :
    STLKUgL C μ s t := h.2.2.1

section Concrete

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- The same at concrete data: the band carrier `bandFM sz0 (fun _ => 0)`, the law `seqP sz0`, `s ≡ 0`, `t ≡ 1/16` (the premise `twSteps` is the
owed pin of V2a / TL). -/
example (Cd : ℝ) (h : twSteps (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst Cd) :
    STLmaxUgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst ∧ STLKUgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst :=
  ⟨h.2.1, h.2.2.1⟩

/-- ... and in the converse direction: the four pins give `twSteps` at the concrete data. -/
example (Cd : ℝ) (h2 : STStep2ConclgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst Cd)
    (h3 : STLmaxUgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst) (h4 : STLKUgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst)
    (h5 : STDecayLoopUgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst) :
    twSteps (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst Cd := ⟨h2, h3, h4, h5⟩

end Concrete

/-! ## 2. The BA readings (statement level; the proofs are owed by U3-BA) -/

/-- Targets 1 and 5 at the BA carrier family: `(law, Flow, mk, T0) = (seqP ∘ withLam 0, BAFlow, baFMz, BAflowT0)` (the shape of `BATwFrame`,
`BA/TwistPins.lean:146`, `BAStep2`, `BA/FlowPins.lean:432`). -/
example : Prop := ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
  STStep3RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
    STStep4RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- Target 1 at the BA carrier `baFMz sz z`. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
  STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧ STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- Target 3 at the BA carrier: the compatibility facts of `baStep2Mat` with the flow matrix `seqHflowBA (BAflowLam0 sz z)`. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ),
  Step34Gen_LCompat (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) ∧
    Step34Gen_KCompat (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))

/-- Targets 3-5: the ℰ-term setting `STSEforLngL` at the BA reading (`mkM = baStep2Mat`, `Hf = seqHflowBA (BAflowLam0 sz z)`). -/
example : Prop := STSEforLngL 3 STAny (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) BAflowT0

/-- Target 3: the ℰ-term vocabulary at the BA carrier and flow matrix. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))),
  STegtg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n τ ω I =
    STegtMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n τ (sz.seqHflowBA (BAflowLam0 sz z) n τ ω) I

end RBM.BA

end
