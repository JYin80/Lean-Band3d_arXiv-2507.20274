/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs
import RBM3D.Graph.ScalingOrder
import RBM3D.Graph.LWVocab
import RBM3D.Graph.LWPsi
import RBM3D.Graph.LWStein
import RBM3D.Defs.Tail
import RBM3D.Evolution.Pins
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The light-weight layer: statements, premises and data

The statements of the light-weight layer, as definitions of `Prop`s (and data).
Paper: Section 7, Section 3 (Step 2), Section 6 (Step 6) and Section 2 (the flow bounds).

* `RBM.Graph`: the weight expansion `LWweightExp` (`(Owx)` (7.20)), as an identity of
  expectations at a fixed size `(d, L, W)` over the one-size law `PF`, with the fixed-size objects
  under the prefix `LWPins_` (`LWPins_dH`, `LWPins_resPoly`, `LWPins_lwG`, `LWPins_lwGc`,
  `LWPins_lwS`, `LWPins_lwSp`, `LWPins_lwf`, `LWPins_lwdf`).  They are not the `lwG`, `lwS`,
  `lwSplus`, `lwPoly`, `dhSample` of `Graph/LWStein` (those live on the sequence space `sz.seqP`
  of `Sizes d`, take `n`, `u`, and the sample as arguments).
* `RBM.Gauss.Sizes`: the premises `LWInteg`, `LWInit`, `LWLoop2`, `LWLoopExp`, `LWXi`, `LWAvgLaw`,
  `LWAssm`, `LWAssmExp` (and the data `LWS`, `LWf`, `LWcut`, `LWE`) and the statements `LWterm`,
  `LWtermExp` (`LWtermExpS`, `LWtermExpN`), `LWtermEXP`, `LWMoment`, `LWMomentExp`, `LWAnpKey`,
  `LWAnpKeyGh`, `LWAnp`, `LWReduceB`, `LWReduceT`.  The class predicates `LWWindow`, `LWClass`,
  `LWPsiRel`, `LWPsiAll` are in `Graph/LWPsi`.

Every declaration here is a `def` of a `Prop` (or data): no theorem is proved in this file.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss

/-- `∂_{h_{αw}} F` (`(Owx)` (7.20)): the complex derivative of `F` at `H` in the direction of the
matrix unit `E_{αw}`, the entry `h_{wα}` held fixed (Wirtinger: `h_{αw}` and `h_{wα} = conj h_{αw}` are
independent variables; for `F` holomorphic in the entries of `H`, e.g. a polynomial in the entries of
`(H - z)⁻¹` and `(H - z̄)⁻¹`, this is `∂/∂ h̄_{wα}` of the real coordinates).  For `F = G_{ij}` it is
`-G_{iα} G_{wj}` (`RBM.Graph.hasDerivAt_inverse_apply`). -/
def LWPins_dH {ι : Type*} [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) (H : Matrix ι ι ℂ) (α w : ι) : ℂ :=
  deriv (fun s : ℂ => F (H + s • Matrix.single α w 1)) 0

section FlowData

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `f(G)` of the expansion lemmas: a polynomial in the entries of `G = (H - z)⁻¹` (`v.1 = true`) and of
`G^* = (H - z̄)⁻¹` (`v.1 = false`; `Ḡ_{xy} = conj G_{xy}` is the entry `(y, x)` of `G^*` at a
Hermitian `H`): every graph value is of this form.  The paper's "differentiable function of `G`" is
more general. -/
def LWPins_resPoly (z : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    Matrix (Idx d L W) (Idx d L W) ℂ → ℂ :=
  fun H => MvPolynomial.eval (fun v => Gres H z v.1 v.2.1 v.2.2) P

variable (g E t : ℝ)

def LWPins_lwG (ω : Ω d L W) (x y : Idx d L W) : ℂ := Gres (Hflow d L W t ω) (zt E t) true x y
def LWPins_lwGc (ω : Ω d L W) (x y : Idx d L W) : ℂ := LWPins_lwG d L W E t ω x y - if x = y then mE E else 0
def LWPins_lwS (x y : Idx d L W) : ℂ := (t : ℂ) * svarF d L W g x y
def LWPins_lwSp : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of (LWPins_lwS d L W g t) * Ring.inverse (1 - (mE E) ^ 2 • Matrix.of (LWPins_lwS d L W g t))

end FlowData

section ExpansionPins

variable (d L W : ℕ) [NeZero L] [NeZero W] (E t : ℝ)

/-- `f(G)` at the sample `ω`: a resolvent polynomial `P` evaluated at `H_t = √t X`. -/
def LWPins_lwf (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω : Ω d L W) : ℂ :=
  LWPins_resPoly d L W (zt E t) P (Hflow d L W t ω)

/-- `∂_{h_{αw}} f(G)` at the sample `ω`. -/
def LWPins_lwdf (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω : Ω d L W) (α w : Idx d L W) : ℂ :=
  LWPins_dH (LWPins_resPoly d L W (zt E t) P) (Hflow d L W t ω) α w

/-- **Lemma 7.11 (`ssl`, `(Owx)` (7.20))** as an identity of expectations at a fixed size `(d, L, W)`,
coupling `g`, flow energy `E`, time `t`: for every resolvent polynomial `f` and vertex `x`,
`E[Ǧ_{xx} f] = E[m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f + m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{αα} Ǧ_{ββ} f
- m Σ_α S_{xα} G_{αx} ∂_{h_{αx}} f - m³ Σ_{α,β} S⁺_{xα} S_{αβ} G_{βα} ∂_{h_{βα}} f]`,
with `S = t S^{(B)}` (the variance of `H_t`) and `S⁺ = S (1 - m² S)⁻¹`. -/
def LWweightExp (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x : Idx d L W),
      ∫ ω, LWPins_lwGc d L W E t ω x x * LWPins_lwf d L W E t P ω ∂(PF d L W g) =
        ∫ ω, (mE E * ∑ α, LWPins_lwS d L W g t x α * LWPins_lwGc d L W E t ω x x * LWPins_lwGc d L W E t ω α α *
                LWPins_lwf d L W E t P ω +
            mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β *
                LWPins_lwGc d L W E t ω α α * LWPins_lwGc d L W E t ω β β * LWPins_lwf d L W E t P ω -
            mE E * ∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α x * LWPins_lwdf d L W E t P ω α x -
            mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β *
                LWPins_lwG d L W E t ω β α * LWPins_lwdf d L W E t P ω β α) ∂(PF d L W g)

end ExpansionPins

end RBM.Graph

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `S_{αβ} = W^{-d} S^{(B)}_{[α][β]}` of the model at size `n` (`svarF`; `(eq:variancematrix)` (2.5)). -/
def LWS (n : ℕ) (α β : Idx d (sz.L n) (sz.W n)) : ℝ :=
  svarF d (sz.L n) (sz.W n) (sz.lam n) α β

/-- **`f_{xy}(G)`** of `(fxyG_sum)` (7.4), `σ = +`, `G ≡ G_t`: `Σ_{α∉{x,y}} Σ_β S_{αβ} Ǧ_{ββ}
G_{xα} G_{αy}`, `Ǧ = G - M`, `M = m(E) I` (`STGM`). -/
def LWf (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, if α = x ∨ α = y then 0 else
    ∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β * Gt sz n E t true ω x α * Gt sz n E t true ω α y

/-- Integrability of `|f_{xy}(G)|^p` (a bounded measurable function on the probability space, since
`‖G_t‖ ≤ η_t⁻¹` for `t < 1`): the technical premise of the Markov step. -/
def LWInteg (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 ≤ t → t < 1 → ∀ (p : ℕ)
    (x y : Idx d (sz.L n) (sz.W n)), Integrable (fun ω => ‖LWf sz n E t ω x y‖ ^ p) sz.seqP

/-- One term of `(eq:EGC)` (7.1): `W^d Σ_{a₁,a₂} S^{(B)}_{a₁a₂} tr(Ǧ_t(σc) E_{a₁})
tr(G_t(σc) E_{a₂} G_t(σc) E_{ac} G_t(σo) E_{ao})`, with `tr(Ǧ(σ) E_a) = 𝓛^{(1)}_{t,σ,a} - m(σ)`. -/
def LWcut (n : ℕ) (E t : ℝ) (σc σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, SB d (sz.L n) (sz.lam n) a₁ a₂ *
    (Lloop sz n E t ![σc] ![a₁] ω - mSigma E σc) * Lloop sz n E t ![σc, σc, σo] ![a₂, ac, ao] ω

/-- **The light-weight term `𝓔^{Gc,(2)}_{t,σ,a}`** (`(eq:LW-n=2)` (6.5); its form `(eq:EGC)` (7.1)):
for `σ = (σ', σ)`, `a = (a, b)` the term above with the charge `σ`, the block `b`, plus the term
with `(σ, a) ↔ (σ', b)` exchanged. -/
def LWE (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  LWcut sz n E t (σ 1) (σ 0) (a 1) (a 0) ω + LWcut sz n E t (σ 0) (σ 1) (a 0) (a 1) ω

/-- `(initialGT2)` (3.4) for the control parameter `Ψ`. -/
def LWInit (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    Prec sz (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω) (fun n _ _ => Ψ n ^ 2)

/-- `(LW_assm)` (3.27): `𝓛^{(2)}_{t,σ,(a,b)} ≺ Ψ_t²(|a-b|)` for `σ ∈ {(+,-),(-,+)}`, all `a, b`. -/
def LWLoop2 (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  Prec sz (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖Lloop sz n (E n) (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
    (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2)

/-- All hypotheses of `lem:LWterm` beyond the flow setting (Lemma 3.10). -/
def LWAssm (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ LWInit sz E t ε₀ Ψ ∧ LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    LWLoop2 sz E t Φ

/-- **`lem:LWterm`** (Lemma 3.10), `(LW_conclusion)` (3.29): `𝓔^{Gc,(2)}_{t,σ,(a,b)} ≺ η_t⁻¹ Ψ_t(0) Ψ_t²(|a-b|)`
for all `σ ∈ {+,-}²`, `a, b ∈ Z_L^d`. -/
def LWterm (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
          LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
          Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
              Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2)

/-- `(LW_assm_exp)` (3.31): `𝓛^{(2)}_{t,σ,(a,b)} ≺ W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|)` for every `D > 0` (`≺` for
all large `D` is equivalent: larger `D` is the stronger hypothesis). -/
def LWLoopExp (E t : ℕ → ℝ) (ℓ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖Lloop sz n (E n) (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
        ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ))

/-- The hypotheses of `lem: EWGn2_N` (Lemma 3.11) beyond the flow setting: `(initialGT2)` for a
control parameter `Ψ`, a length `0 ≤ ℓ ≤ (log W)^{10} ℓ_t`, and `(LW_assm_exp)`. -/
def LWAssmExp (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ LWInit sz E t ε₀ Ψ ∧ (∀ n, 0 ≤ ℓ n) ∧
    (∀ n, ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) (t n)) ∧
    LWLoopExp sz E t ℓ

/-- **`lem: EWGn2_N`** (Lemma 3.11), `(LW_conclusion_exp)` (3.32): `𝓔^{Gc,(2)}_{t,σ,(a,b)} ≺ η_t⁻¹
(W^{-d}B_{t,0})^{1/2} W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|)` for every `D > 0`. -/
def LWtermExp (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ)))

/-- `(Gt_avgbound_flow)` (2.88): `max_a |tr((G_t - M)E_a)| ≺ W^{-d} B_{t,0}`. -/
def LWAvgLaw (E t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Zd d (sz.L n))
    (fun n a ω => ‖Lloop sz n (E n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (E n)‖)
    (fun n _ _ => sz.Bctl n (t n))

/-- **`lem:LWterm_EXP`** (Lemma 6.2), `(eq:ExpLWn=2)` (6.7): if `1 - t ≥ ĝ²/L^d` (the sizes where it fails are
outside the index set) and `(Gt_bound_flow)`-`(Eq:Gdecay_flow)` hold at `t`, then
`E 𝓔^{Gc,(2)}_{t,σ,a} ≺ (1-t)⁻¹ (W^{-d} B_{t,0})^{5/2}`; the left side is deterministic. -/
def LWtermEXP (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω ∂(sz.seqP)‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **`lem:LW_moment`** (Lemma 7.1): for every fixed `p ∈ 2ℕ` there is `c > 0` (depending on `p`
and on the constants of the hypotheses) with `E |f_{xy}(G)|^p ≺ η_t^{-p} [Ψ_t(0)]^p [Ψ_t(c|a-b|)]^p`,
`a = [x]`, `b = [y]`.  The left side is deterministic. -/
def LWMoment (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ),
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
              LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
              Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
                (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖ ^ p ∂(sz.seqP))
                (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
                  Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))) ^ p)

/-- **`lem:LW_moment_exp`** (Lemma 7.2): in the setting of `lem: EWGn2_N` with `1 - t > ĝ²/L²`, for
every fixed `p ∈ 2ℕ` and every `D > 0`: `E |f_{xy}|^p ≺ η_t^{-p} (W^{-d} B_{t,0})^{p/2}
[𝖳_t(|a-b| ∧ ℓ)]^p + W^{-D}` (`𝖳_t` is `sfT`). -/
def LWMomentExp (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
          ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
                  sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
                (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂(sz.seqP))
                (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
                    (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p +
                  ((sz.W n : ℕ) : ℝ) ^ (-D))

/-! ### Nested graphs: `lem:Anp_key`, `lem:Anp_key_gh`, `lem:Anp` (Lemmas 7.22-7.24) -/

/-- `(eq:Gbyxi3)` (7.38): the edge variables `ξ_{αβ} = ξ_{βα} ≥ 0`, `ξ_{αβ} ≺ Ψ_t(|α-β|)` and
`Σ_β |ξ_{αβ}|² ≺ (W^d η_t)⁻¹`, uniformly in `α, β ∈ Z_L^d`. -/
def LWXi (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ξ n p.1 p.2 ω)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
    Prec sz (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (E n) (t n))⁻¹)


/-- **`lem:Anp_key`** (Lemma 7.23): a nested graph (`p` edge-disjoint paths, `q ≤ p` internal vertices,
properties (1)-(3), no self-loops, no ghost edge) with edge variables `ξ` satisfying `(eq:Gbyxi3)`
has `𝒢_{ab} ≺ (W^d η_t)^{-q} Ψ_t^{ord(𝒢) - p} Π_i Ψ_t(c|a_i - b_i|)`, `Ψ_t = Ψ_t(0)`, `c > 0`
depending on the graph and the constants. -/
def LWAnpKey (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXi sz (STflowE z) t Φ ξ →
                Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2)
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q *
                    Φ n 0 ^ (Γ.ordN - p) *
                    ∏ i, Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)))

/-- **`lem:Anp_key_gh`** (Lemma 7.24): the same with ghost edges (at most one per path, an ending
edge): `𝒢_{ab} ≺ (W^d η_t)^{-q} Ψ_t^{ord(𝒢) - n_ngh} Π_i [Ψ_t(c|a_i - b_i|)]^{1(𝔓_i has no ghost edge)}`. -/
def LWAnpKeyGh (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.GhostOK → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXi sz (STflowE z) t Φ ξ →
                Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2)
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q *
                    Φ n 0 ^ (Γ.ordN - Γ.nngh) *
                    ∏ i, (if Γ.noGhostPath i = true then
                      Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1))

/-- **`lem:Anp`** (Lemma 7.22, `(eq:bddGamma_aux)` (7.37)): the auxiliary graph of a locally standard graph
has all `a_i = [a]`, `b_i = [b]`: `Γ^{aux}_{[a][b]} ≺ (W^d η_t)^{-q} [Ψ_t(c|[a]-[b]|)]^p Ψ_t^{ord(Γ^{aux}) - p}`.
The properties (3)-(5) of `lem:localregular` of `Γ_{μ,xy}` are the nested properties of `Γ^{aux}`
(Subsection 7.4); `Γ^{aux}` is a nested graph here (the passage `Γ_{μ,xy} ↦ Γ^{aux}` is `def_auxgraph`). -/
def LWAnp (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXi sz (STflowE z) t Φ ξ →
                Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q *
                    Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p *
                    Φ n 0 ^ (Γ.ordN - p))

/-- The reduction of `lem:LWterm` to the moment bound (Section 7): from `f_{xy} ≺ η_t⁻¹ Ψ_t(0)
Ψ_t(|a-b|)` (the Markov step) and the local laws (`(eq:directG1)`, `(eq:recolterm)`,
`(eq:recoltermwt)`) to `𝓔^{Gc,(2)} ≺ η_t⁻¹ Ψ_t(0) Ψ_t²(|a-b|)`; its proof uses `lem_GbEXP` (`STGbEXP`)
and `(LW_assm)`. -/
def LWReduceB (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
          LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖)
            (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
              Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) →
          Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
              Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2)

/-- `lem: EWGn2_N` on the sizes where `1 - t > ĝ²/L²` (the index set is empty elsewhere).  The other
regime `1 - t ≤ ĝ²/L²` (`LWtermExpN`) is `lem:LWterm` (Section 7: "an immediate consequence", with
`ℓ_t = L`, `Ψ_t²(r) = W^{-d} 𝒯̃(r)`); the two index sets are glued by the union bound, and the passage from
`lem:LWterm` to the sub-sequence of the second regime needs a transfer lemma. -/
def LWtermExpS (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
              (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))

/-- `lem: EWGn2_N` on the sizes where `1 - t ≤ ĝ²/L²`: the same conclusion on the complementary index set
(then `ℓ_t = L` and the exponential factor of `𝒯_t` is of order one for `r ≲ L`). -/
def LWtermExpN (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2})
              (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))

/-- The reduction of `lem: EWGn2_N` to the moment bound (`(eq:directG2)` (7.3),
`(eq:recolterm2)` (7.6), `(eq:recoltermwt2)` (7.8)), on the sizes with `1 - t > ĝ²/L²`: from `f_{xy} ≺ η_t⁻¹
(W^{-d}B_{t,0})^{1/2} 𝖳_t(|a-b|∧ℓ) + W^{-D}` to the conclusion of `lem: EWGn2_N`. -/
def LWReduceT (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            Prec sz (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
                sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
              (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖)
              (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
                  (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n)) +
                ((sz.W n : ℕ) : ℝ) ^ (-D)) →
            Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
              (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))

end RBM.Gauss.Sizes

end
