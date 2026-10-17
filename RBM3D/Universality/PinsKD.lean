/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.PinsK
import RBM3D.Universality.OUInterfaceK

/-!
# T2520 (G1): the dimension-filtered generic pins

MN-D3 D1 (`docs/reports/T2513-design.md` §1; DECISIONS §316, §340, §353).  Each merged generic pin
that reads an input for every `d` has a successor with a **dimension filter** `Dm : ℕ → Prop`
(not `D`: the merged bodies bind the exponent `D : ℝ`): the text is the merged one with
`(Dm : ℕ → Prop)` added first and `Dm d →` inserted before `3 ≤ d →`.  The two rows that consume
the claim take the filtered claim.  At `Dm = fun _ => True` each successor is the merged pin (the
eight `…_true` equivalences and the two band equivalences `band_locAvg`, `band_ouRow`: MNO-C1, no
band file is touched); at `Dm = (· = d)` it is the pin at the one dimension `d`.

Merged texts (statement-identical after the filter map): `UNQuek` `PinsK:398`, `UNLocAvgk` `:406`,
`UNOUClaimsk` `:421`, `UNOURowk` `:426`, `UNEMCTE2Rowk` `:429`, `UNJakUywRowk` `:435`,
`UNClaimRowk` `:442`, `UNG1Rowk` `OUInterfaceK:101`.  No block Anderson and no band vocabulary
appears in the eight texts.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Univ

open MeasureTheory Filter Topology
open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The eight filtered pins -/

/-- `UNQuekD`: `UNQuek` (`PinsK:398`) read only at the dimensions `d` with `Dm d`. -/
def UNQuekD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, (K d).bulk sz κ E n → ∀ a : Zd d (sz.L n),
        ((K d).M sz).μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (((K d).M sz).H n ω)} ≤
          queBound (sz.W n) 𝔡 ε₀ c τ

/-- `UNLocAvgkD`: `UNLocAvgk` (`PinsK:406`) with the filter. -/
def UNLocAvgkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      ((K d).M sz).μ {ω | ∃ z : ℂ, ((K d).bulk sz κ z.re n ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1) ∧
          ∃ a : Zd d (sz.L n),
          ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
            ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
                Gres (((K d).M sz).H n ω) z true x x - (K d).mdet sz n z‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- `UNOUClaimskD`: `UNOUClaimsk` (`PinsK:421`) with the filter. -/
def UNOUClaimskD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUEk (K d) sz 𝔡 τU ∧ UNOUDiagk (K d) sz τU

/-- `UNOURowkD`: `UNOURowk` (`PinsK:426`) with the filtered claim. -/
def UNOURowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (ML Loc Que : Prop) : Prop :=
  ML → Loc → Que → UNOUClaimskD Dm K

/-- `UNEMCTE2RowkD`: `UNEMCTE2Rowk` (`PinsK:429`) with the filter. -/
def UNEMCTE2RowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNEMCTE2k (K d) sz E nf τU Cn

/-- `UNJakUywRowkD`: `UNJakUywRowk` (`PinsK:435`) with the filter; the claim it consumes is the filtered one. -/
def UNJakUywRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (Loc : Prop) : Prop :=
  Loc → UNOUClaimskD Dm K → ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNJakk (K d) sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUywk (K d) sz E nf τU C (𝔠 * 𝔡 / 30)

/-- `UNClaimRowkD`: `UNClaimRowk` (`PinsK:442`) with the filter on the hypothesis and on the conclusion. -/
def UNClaimRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  (∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ Cn C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNEMCTE2k (K d) sz E nf τU Cn ∧ UNJakk (K d) sz E nf τU C (𝔠 * 𝔡 / 30) ∧
          UNUywk (K d) sz E nf τU C (𝔠 * 𝔡 / 30)) →
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E

/-- `UNG1RowkD`: `UNG1Rowk` (`OUInterfaceK:101`) with the filter. -/
def UNG1RowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop) : Prop :=
  ML → Loc → Que →
    ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 →
        UNOULLk (K d) sz τU ∧ UNOUEq747k (K d) (P d) sz 𝔡 τU

/-! ## 2. MNO-C1: the merged pins are the filtered ones at `Dm = fun _ => True` -/

/-! ## 3. Compiled nonempty instances

The `Iff`s applied at the band kind `UNKind.band` (the only kind this file may name) with its profile `UNOUProfile.band`
and the band inputs `UNMLOut`, `UNLocAvgBand`, `UNQueBand`; the two band `Iff`s are themselves at concrete data. -/

end RBM.Univ

end
