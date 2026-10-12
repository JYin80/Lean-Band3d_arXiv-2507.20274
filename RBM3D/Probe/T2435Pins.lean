/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AuxGraph2
import RBM3D.Graph.BAAtom2
import RBM3D.BA.LWPinsBA
import RBM3D.BA.GreenOff
import RBM3D.BA.GreenLocal
import RBM3D.BA.Step1Boot
import RBM3D.BA.Ward

/-!
# T2435 probe (BA-L L3c3a `BAAuxGraph2`, design gate (vi)): ζ, the carrier form of `LWXi`, targets 3-6 (never merged)

Paper `paper/tex/B_graphical_lemmas.tex:415-497` (`(Gyiyjatom)`, `(eq:Gbyxi2_BA)`, `(G_by_auxG_BA)`), `7_8_light_weight.tex:870-890`
(`(eq:Gbyxi)`, `(eq:xia1a2)`, `claim:xi`); basis `Graph/AuxGraph2.lean` (`lwXiSq`, `lwXiClaim_holds`, `lwGbyXi_holds`, `lwEntryPsi_holds`).
Definitions and Prop-valued pins only (no proof of a target); each pin is applied at concrete data in the `example`s of section 4:
`d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`), `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2`, `ε₀ = 1/10`, `Φ0 ≡ W^{-1/2}`
(`C₁ = C₂ = 2`, `C₃ = 1`, `Cc ≡ 1`), `ε₁ = 1/20`, `D₁ = 12`, `R = (log W)^{21/20}`, `ρ = 2R + (log W)^{3/2}`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open MeasureTheory Filter

noncomputable section

namespace RBM.Graph
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 1. Target 1: the BA edge variable ζ (twin of `lwXiSq`, `lwXiVar`, `AuxGraph2:67, 76`) and its deterministic facts -/

/-- `ζ([a₁],[a₂])²` on the carrier `baFMz sz z`: the `(+,-)`, `(-,+)` two-loops over the `‖·‖_∞`-ball pairs of radius `ρ`, plus
`W^{-d} 1(|a₁ - a₂| ≤ ρ)`, plus the floor `W^{-D₁}` (the `+ W^{-D}` of `(Gyiyjatom)`, `B:425`). -/
def baZetaSq {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℝ :=
  (∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
    ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0) +
    ((sz.W n : ℕ) : ℝ) ^ (-D₁)

/-- `ζ = √(ζ²)`. -/
def baZetaVar {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℝ :=
  Real.sqrt (baZetaSq sz z t ρ D₁ n a₁ a₂ ω)

/-- `ζ ≥ 0` (twin of `lwXiVar_nonneg`, `:135`). -/
def BAZetaVarNonneg : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ),
    0 ≤ baZetaVar sz z t ρ D₁ n a₁ a₂ ω

/-- `ζ([a₁],[a₂]) = ζ([a₂],[a₁])` (twin of `lwXiVar_symm`, `:160`: trace cyclicity of `loopFine`). -/
def BAZetaVarSymm : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ),
    baZetaVar sz z t ρ D₁ n a₁ a₂ ω = baZetaVar sz z t ρ D₁ n a₂ a₁ ω

/-- The Ward sum in block form (twin of `lwXi_ward_sum`, `:507`; paper-delta candidate T2435d): `A` bounds `‖G - M‖` entrywise,
`‖G_{yy}‖ ≤ |m| + A ≤ 1 + A` (`BAm_norm_le_one`), `η = C.eta`; the floor contributes `L^d W^{-D₁}`. -/
def BAZetaWard : Prop :=
  ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ), 0 ≤ t n → t n < 1 → 0 ≤ ρ n → ∀ (ω : sz.SeqΩ) {A : ℝ},
      (∀ x y, ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ A) → ∀ a₁ : Zd d (sz.L n),
        ∑ a₂, baZetaSq sz z t ρ D₁ n a₁ a₂ ω ≤
          2 * (2 * ρ n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (t n))⁻¹ * (1 + A)) +
            (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ + ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁)

/-! ## 2. Target 2: the carrier form of `LWXi` (`LWPins.lean:360`) -/

/-- `LWXi` over a carrier `C` and a law `μ` (`Prec sz` is `PrecL sz μ`, `etaT (E n) (t n)` is `C.eta n (t n)`); the check file's
`T2435_LWXigL` up to the name. -/
def LWXigL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ξ n p.1 p.2 ω)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * C.eta n (t n))⁻¹)

/-- The bridge: at the band carrier and the band law the carrier form is the merged `LWXi`. -/
example {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) :
    LWXigL (bandFM sz E) (Sizes.seqP sz) t Φ ξ ↔ LWXi sz E t Φ ξ := Iff.rfl

/-! ## 3. Targets 3-6 (pins; the 1b proves 3-5, target 6 is pinned for L3d1) -/

/-- **Target 3** (`claim:xi` at BA; twin of `LWXiClaim`, `:951`): at the `baPin` data, `LWPsiAll`, `LWLoop2gL` and `‖G - M‖ ≺ W^{-ε₁}`
give `LWXigL` for `ζ` at a radius `ρ = N^{o(1)}` and a floor exponent `D₁ ≥ d + 2C₂/(𝔠 d) + 1`. -/
def BAZetaClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
            (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ) →
            ∀ D₁ : ℝ, (d : ℝ) + 2 * C₂ / (𝔠 * d) + 1 ≤ D₁ →
              LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ (baZetaVar sz z t ρ D₁)

/-- The index set of `BAGbyZeta`: all pairs `x, y` (`x = y` included) with blocks `a`, `b` within `zdistD`-distance `R` of `[x]`, `[y]`. -/
abbrev BAGbyZetaU {d : ℕ} (sz : Sizes d) (R : ℕ → ℝ) (n : ℕ) : Type :=
  {q : (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) × (Zd d (sz.L n) × Zd d (sz.L n)) //
    (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.1).1 - q.2.1) : ℝ) ≤ R n ∧
    (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.2).1 - q.2.2) : ℝ) ≤ R n}

/-- **Target 4, `(eq:Gbyxi2_BA)` (a)** (twin of `LWGbyXi`, `:1106`): `‖(G_t - M)_{xy}‖ ≺ ζ(a, b)` for all `x, y` and the blocks `a`, `b` at
distance `≤ R` (`R ≥ 0`, `ρ - 2R ≥ K log W` eventually for every `K`); no `LWPsiAll`, no `LWLoop2gL`, no unprimed `BAGbEXPij`. -/
def BAGbyZeta (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₁ : ℝ, 0 < ε₁ →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
        ∀ (ρ R : ℕ → ℝ) (D₁ : ℝ), (∀ n, 0 ≤ R n) →
          (∀ K : ℝ, ∀ᶠ n in atTop, K * Real.log ((sz.W n : ℕ) : ℝ) ≤ ρ n - 2 * R n) →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAGbyZetaU sz R)
            (fun n q ω => ‖(baFMz sz z).GM n (t n) ω q.1.1.1 q.1.1.2‖)
            (fun n q ω => baZetaVar sz z t ρ D₁ n q.1.2.1 q.1.2.2 ω)

/-- **Target 4, sample form** (twin of `lwGbyXi_hxi`, `:1160`): for `c ≥ 0`, data `D` with `D.G = C.G`, `D.M = C.M` and a sample with
`‖(G - M)_{xy}‖ ≤ c ζ(a, b)` on the `R`-balls, `ξ = c ζ` satisfies `hξ0`, `hξ` of `baGtoAG_holds` / `baGtoAG_E` (`BAAtom2:404-406, 616-618`). -/
def BAGbyZetaHxi : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ R : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (D : BALData (Idx d (sz.L n) (sz.W n)))
    (ω : sz.SeqΩ) {c : ℝ}, 0 ≤ c → (∀ x y, D.G x y = (baFMz sz z).G n (t n) ω x y) →
    (∀ x y, D.M x y = (baFMz sz z).M n x y) →
    (∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)),
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n →
      ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ c * baZetaVar sz z t ρ D₁ n a b ω) →
    (∀ a b : Zd d (sz.L n), 0 ≤ (fun a b : Zd d (sz.L n) => c * baZetaVar sz z t ρ D₁ n a b ω) a b) ∧
    (∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)),
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n →
      ‖D.G x y - D.M x y‖ ≤ (fun a b : Zd d (sz.L n) => c * baZetaVar sz z t ρ D₁ n a b ω) a b)

/-- **Target 5** (`(eq:Gbyxi)` entrywise; twin of `LWEntryPsi`, `:1177`): `‖G - M‖ ≺ Φ(0)` at all pairs (G3's `‖D.G - D.M‖ ≤ Ψ`). -/
def BAEntryPsi (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => Φ n 0)

/-- **Target 6, G4 on the BA carrier** (`BAAnpAux`, `BAAtom2:677`, with `BAFlow`, `BAflowT0`, `baFMz`, `PrecL` and `LWXigL`, `η = C.eta`).
Pin only; owner L3d1. -/
def BAAnpAuxG (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ) (P : BAPGraph (Fin 2)), 0 < p → P.g.nM ≤ p → (BAShadowPG P).LocReg345 p →
      P.g.mol (Sum.inl (P.ext 0)) ≠ P.g.mol (Sum.inl (P.ext 1)) →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ →
                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
                  (fun n ab ω => P.g.auxVal (fun α β => ξ n α β ω) (fun e => if e = P.ext 0 then ab.1 else ab.2))
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ P.g.nM *
                    Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (P.g.auxOrd - p))

/-! ## 4. Compiled nonempty instances -/

section Inst
open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- The instance data: `Φ0 ≡ W^{-1/2}`, `R = (log W)^{21/20}`, `ρ = 2R + (log W)^{3/2}`. -/
def pPhi : ℕ → ℝ → ℝ := fun n _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
def pR : ℕ → ℝ := fun n => Real.log ((sz0.W n : ℕ) : ℝ) ^ (21 / 20 : ℝ)
def pρ : ℕ → ℝ := fun n => 2 * pR n + Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)

/-- Targets 1, 3, 4, 5, 6 at the data above and one joint `(ρ, R, D₁) = (pρ, pR, 12)`: every deterministic hypothesis is discharged
(`LWPsiAll`, `ρ ≥ 0`, `ρ + 1 ≤ N^τ`, `D₁ ≥ 12`, `R ≥ 0`, `ρ - 2R ≥ K log W`, the Ward `hA`); `LWLoop2gL` and the entry bound
`‖G - M‖ ≺ W^{-1/20}` (other gates' pins) stay hypotheses.  Target 6 is fed with `ζ` from target 3. -/
example (hNn : BAZetaVarNonneg) (hSy : BAZetaVarSymm) (hWd : BAZetaWard) (h3 : BAZetaClaim 3) (h4 : BAGbyZeta 3)
    (h5 : BAEntryPsi 3) (h6 : BAAnpAuxG 3) (ω : sz0.SeqΩ) (a₁ : Zd 3 (sz0.L 0))
    (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) pPhi)
    (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) :
    True := by
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := RBM.Gauss.LWInst.one_le_W
  have hlog1 : ∀ n, 1 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := fun n => by
    rw [Real.le_log_iff_exp_le (by linarith [hW1 n])]
    linarith [RBM.Gauss.InductionDefsInst.W_ge_32 n, Real.exp_one_lt_d9]
  have hΦ : LWPsiAll sz0 (1 / 10) 2 2 1 (fun _ => 1) pPhi := by
    refine ⟨by norm_num, ⟨Eventually.of_forall fun n r _ => ⟨Real.rpow_pos_of_pos (by linarith [hW1 n]) _,
      Real.rpow_le_rpow_of_exponent_le (hW1 n) (by norm_num)⟩, one_pos, Eventually.of_forall fun n => ?_⟩,
      fun n a _ b _ _ => le_rfl, by norm_num, by norm_num,
      fun C _ => Eventually.of_forall fun n ℓ _ _ => by simp [pPhi], Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_⟩
    · simp only [pPhi, one_mul]
      exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by norm_num)
    · simp only [pPhi]
      have hW : 0 < ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith [hW1 n]) _
      have hr : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div (by linarith)).mpr h12
      have : (1 : ℝ) ≤ (ℓ₂ / ℓ₁) ^ (2 : ℝ) := Real.one_le_rpow hr (by norm_num)
      nlinarith
  have hR0 : ∀ n, 0 ≤ pR n := fun n => Real.rpow_nonneg (by linarith [hlog1 n]) _
  have hρ0 : ∀ n, 0 ≤ pρ n := fun n => by
    unfold pρ
    linarith [hR0 n, Real.rpow_nonneg (by linarith [hlog1 n] : (0 : ℝ) ≤ Real.log ((sz0.W n : ℕ) : ℝ)) (3 / 2 : ℝ)]
  have hrad : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, pρ n + 1 ≤ ((sz0.size n : ℕ) : ℝ) ^ τ := fun τ hτ => by
    filter_upwards [lwXiRad_holds sz0 sz0_tendsto 3 0 (3 / 2) (by norm_num) le_rfl (by norm_num) τ hτ] with n hn
    have := Real.rpow_le_rpow_of_exponent_le (hlog1 n) (by norm_num : (21 / 20 : ℝ) ≤ 3 / 2)
    unfold pρ pR
    linarith
  have hsep : ∀ K : ℝ, ∀ᶠ n in atTop, K * Real.log ((sz0.W n : ℕ) : ℝ) ≤ pρ n - 2 * pR n := fun K => by
    have hW : Tendsto (fun n => ((sz0.W n : ℕ) : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      have : n ≤ sz0.W n := by
        change n ≤ (2 * (n + 1)) ^ 5
        exact (by omega : n ≤ 2 * (n + 1)).trans (Nat.le_self_pow (by norm_num) _)
      exact_mod_cast this
    filter_upwards [(Real.tendsto_log_atTop.comp hW).eventually_ge_atTop (K ^ 2),
      (Real.tendsto_log_atTop.comp hW).eventually_ge_atTop 1] with n h1' h2'
    have h1 : K ^ 2 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := h1'
    have h2 : 1 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := h2'
    have e : Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
        Real.log ((sz0.W n : ℕ) : ℝ) * Real.sqrt (Real.log ((sz0.W n : ℕ) : ℝ)) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one, Real.sqrt_eq_rpow]
    have h3 : pρ n - 2 * pR n = Real.log ((sz0.W n : ℕ) : ℝ) * Real.sqrt (Real.log ((sz0.W n : ℕ) : ℝ)) := by
      rw [← e]; unfold pρ; ring
    rw [h3]
    calc K * Real.log ((sz0.W n : ℕ) : ℝ) ≤ |K| * Real.log ((sz0.W n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
      _ ≤ Real.sqrt (Real.log ((sz0.W n : ℕ) : ℝ)) * Real.log ((sz0.W n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.abs_le_sqrt h1) (by linarith)
      _ = _ := mul_comm _ _
  -- target 1: the facts at the data, `ζ > 0` (the floor), the Ward sum with `A = Σ‖G - M‖`
  have _ := hNn sz0 zSeq (fun _ => 1 / 2) pρ 12 0 a₁ a₁ ω
  have _ := hSy sz0 zSeq (fun _ => 1 / 2) pρ 12 0 a₁ a₁ ω
  have hζ : 0 < baZetaVar sz0 zSeq (fun _ => 1 / 2) pρ 12 0 a₁ a₁ ω := by
    refine Real.sqrt_pos.2 ?_
    unfold baZetaSq
    exact add_pos_of_nonneg_of_pos (add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)) (Real.rpow_pos_of_pos (by linarith [hW1 0]) _)
  have hAle : ∀ (n : ℕ) (ω' : sz0.SeqΩ) (x y : Idx 3 (sz0.L n) (sz0.W n)),
      ‖(baFMz sz0 zSeq).GM n (1 / 2) ω' x y‖ ≤ ∑ x', ∑ y', ‖(baFMz sz0 zSeq).GM n (1 / 2) ω' x' y'‖ :=
    fun n ω' x y => (Finset.single_le_sum (f := fun y' => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω' x y'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ y)).trans (Finset.single_le_sum
      (f := fun x' => ∑ y', ‖(baFMz sz0 zSeq).GM n (1 / 2) ω' x' y'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x))
  have cW := hWd (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 (fun _ => 1 / 2) pρ 12 0 (by norm_num) (by norm_num)
    (hρ0 0) ω (hAle 0 ω) a₁
  -- target 3 (`D₁ = 12 = d + 2 C₂/(𝔠 d) + 1` exactly), target 5
  have c3 := h3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) pPhi hΦ hL
    (1 / 20) (by norm_num) hent pρ hρ0 hrad 12 (by norm_num)
  have c5 := h5 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) pPhi hΦ hL
    (1 / 20) (by norm_num) hent
  -- target 4 at the same `ρ`, `D₁`; the index set contains every diagonal pair `(x, x)`
  have c4 := h4 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 20) (by norm_num) hent pρ pR 12 hR0 hsep
  have hdiag : ∀ n (x : Idx 3 (sz0.L n) (sz0.W n)), ∃ q : BAGbyZetaU sz0 pR n, q.1.1 = (x, x) := fun n x =>
    ⟨⟨((x, x), ((split 3 (sz0.L n) (sz0.W n) x).1, (split 3 (sz0.L n) (sz0.W n) x).1)),
      by simpa using hR0 n, by simpa using hR0 n⟩, rfl⟩
  -- target 6 fed with ζ from target 3 (the BA two-path graph `baPQ`, `p = 2`)
  obtain ⟨c, hc, H⟩ := h6 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2
    BAAtomInst2.baPQ (by norm_num) (by decide) localReg2_inst_Q_locReg345 (by decide) (1 / 10) 2 2 1 (fun _ => 1)
  have c6 := H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) pPhi hΦ _ c3
  trivial

/-- The data `D` of `BAGbyZetaHxi` exists (`D.G = C.G`, `D.M = C.M` at a sample). -/
example (ω : sz0.SeqΩ) : ∃ D : BALData (Idx 3 (sz0.L 0) (sz0.W 0)),
    (∀ x y, D.G x y = (baFMz sz0 zSeq).G 0 (1 / 2) ω x y) ∧ (∀ x y, D.M x y = (baFMz sz0 zSeq).M 0 x y) :=
  ⟨⟨⟨Matrix.of fun x y => (baFMz sz0 zSeq).G 0 (1 / 2) ω x y, Matrix.of fun x y => (baFMz sz0 zSeq).M 0 x y, 0, 0⟩, 0⟩,
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The bridge to G3**: `BAGbyZetaHxi` feeds `hξ0`, `hξ` of `baGtoAG_holds` verbatim (`ξ = cξ ζ`, `R = pR 0`); the other premises are
those of `baGtoAG_holds`, the sample event of target 4 is the hypothesis `h`. -/
example (hX : BAGbyZetaHxi) {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (hN : Γ.Normal) (hext : ∀ a b : E, Γ.mol (Sum.inl a) = Γ.mol (Sum.inl b) → a = b)
    (D : BALData (Idx 3 (sz0.L 0) (sz0.W 0))) (ω : sz0.SeqΩ)
    (hDG : ∀ x y, D.G x y = (baFMz sz0 zSeq).G 0 (1 / 2) ω x y) (hDM : ∀ x y, D.M x y = (baFMz sz0 zSeq).M 0 x y)
    (Ψ A K₀ K₁ Kd C c r cξ : ℝ) (hcξ : 0 ≤ cξ) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hA : 0 ≤ A)
    (hwin : (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ≤ A * Ψ ^ 2)
    (hS : LWKBound D.S (K₀ * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) K₁)
    (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (hC : 0 ≤ C) (hc : 0 < c)
    (hSd : ∀ x y, ‖D.S x y‖ ≤ C * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))))
    (hSpd : ∀ x y, ‖D.Sp x y‖ ≤ C * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))))
    (hMPd : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))))
    (hoff : ∀ x y, (split 3 (sz0.L 0) (sz0.W 0) x).2 ≠ (split 3 (sz0.L 0) (sz0.W 0) y).2 → D.M x y = 0 ∧ D.gPsi x y = 0)
    (hr : 0 ≤ r) (hRr : (Fintype.card (E ⊕ I) : ℝ) * r ≤ pR 0)
    (h : ∀ (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (a b : Zd 3 (sz0.L 0)),
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) x).1 - a) : ℝ) ≤ pR 0 →
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) y).1 - b) : ℝ) ≤ pR 0 →
      ‖(baFMz sz0 zSeq).GM 0 (1 / 2) ω x y‖ ≤ cξ * baZetaVar sz0 zSeq (fun _ => 1 / 2) pρ 12 0 a b ω)
    (ℓe : E → Idx 3 (sz0.L 0) (sz0.W 0)) :=
  baGtoAG_holds 3 le_rfl (sz0.L 0) (sz0.W 0) Γ hN hext D Ψ A K₀ K₁ Kd C c r (pR 0)
    (fun a b => cξ * baZetaVar sz0 zSeq (fun _ => 1 / 2) pρ 12 0 a b ω) hG hA hwin hS hSp hM hP hC hc hSd hSpd hMPd hoff hr hRr
    (hX sz0 zSeq (fun _ => 1 / 2) pρ pR 12 0 D ω hcξ hDG hDM h).1 (hX sz0 zSeq (fun _ => 1 / 2) pρ pR 12 0 D ω hcξ hDG hDM h).2 ℓe

end Inst

#check @baZetaSq
#check @baZetaVar
#check @BAZetaVarNonneg
#check @BAZetaVarSymm
#check @BAZetaWard
#check @LWXigL
#check @BAZetaClaim
#check @BAGbyZetaU
#check @BAGbyZeta
#check @BAGbyZetaHxi
#check @BAEntryPsi
#check @BAAnpAuxG
#check @baGtoAG_holds
#check @baGbEXPij'_holds
#check @baGbEXPii_holds
#check @BAm_norm_le_one

end RBM.Graph

end
