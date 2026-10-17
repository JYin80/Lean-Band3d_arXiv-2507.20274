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
# LW-P: the light-weight pins (T2067)

The pins of the light-weight layer of the T2040 design probe
(`eeda441:RBM3D/Probe/T2040Graphs.lean`, sections 5 and 6, and the three definitions
`LWtermExpS`, `LWtermExpN`, `LWReduceT` of section 7), copied into the library.
Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (`7_8:line`),
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`), `paper/tex/6_Step6_two_loop.tex` (`6:line`).

* `RBM.Graph`: the three expansions `LWweightExp` (`(Owx)`), `LWedgeExp` (`(Oe1x)`),
  `LWggExp` (`(Oe2x)`), as identities of expectations at a fixed size `(d, L, W)` over the
  one-size law `PF`, with the probe's fixed-size objects under the prefix `LWPins_` (`LWPins_dH`,
  `LWPins_resPoly`, `LWPins_lwG`, `LWPins_lwGb`, `LWPins_lwGc`, `LWPins_lwGcb`, `LWPins_lwS`,
  `LWPins_lwSp`, `LWPins_lwf`, `LWPins_lwdf`, `LWPins_oe1xRest`).  They are not the merged
  `lwG`, `lwS`, `lwSplus`, `lwPoly`, `dhSample` of `Graph/LWStein` (those live on the sequence space
  `sz.seqP` of `Sizes d`, take `n`, `u`, and the sample as arguments).
* `RBM.Gauss.Sizes`: the premises `LWInteg`, `LWInit`, `LWLoop2`, `LWLoopExp`, `LWXi`, `LWAvgLaw`,
  `LWAssm`, `LWAssmExp` (and the data `LWS`, `LWf`, `LWcut`, `LWE`) and the pins `LWterm`,
  `LWtermB`,
  `LWtermExp` (`LWtermExpS`, `LWtermExpN`), `LWtermEXP`, `LWMoment`, `LWMomentExp`, `LWAnpKey`,
  `LWAnpKeyGh`, `LWAnp`, `LWReduceB`, `LWReduceT`.  The class predicates `LWWindow`, `LWClass`,
  `LWPsiRel`, `LWPsiAll` are the merged ones of `Graph/LWPsi` (T2051, text identical to the probe).

Every declaration here is a `def` of a `Prop` (or data): no theorem of the layer is proved in this
file; the pins are registered in `RBM3D/Test/Axioms.lean` as owed, their random premises as owed,
and the data conditions as structural.
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

/-- `∂_{h_{αw}} F` (`(Owx)`, `7_8:298`): the complex derivative of `F` at `H` in the direction of the
matrix unit `E_{αw}`, the entry `h_{wα}` held fixed (Wirtinger: `h_{αw}` and `h_{wα} = conj h_{αw}` are
independent variables; for `F` holomorphic in the entries of `H`, e.g. a polynomial in the entries of
`(H - z)⁻¹` and `(H - z̄)⁻¹`, this is `∂/∂ h̄_{wα}` of the real coordinates).  For `F = G_{ij}` it is
`-G_{iα} G_{wj}` (merged `RBM.Graph.hasDerivAt_inverse_apply`). -/
def LWPins_dH {ι : Type*} [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) (H : Matrix ι ι ℂ) (α w : ι) : ℂ :=
  deriv (fun s : ℂ => F (H + s • Matrix.single α w 1)) 0

section FlowData

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `f(G)` of the expansion lemmas: a polynomial in the entries of `G = (H - z)⁻¹` (`v.1 = true`) and of
`G^* = (H - z̄)⁻¹` (`v.1 = false`; `Ḡ_{xy} = conj G_{xy}` is the entry `(y, x)` of `G^*` at a
Hermitian `H`): every graph value is of this form.  The paper's "differentiable function of `G`" is
more general (T2040d). -/
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

/-- **`lem ssl` (`(Owx)`, `7_8:294-306`)** as an identity of expectations at a fixed size `(d, L, W)`,
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

/-- `S_{αβ} = W^{-d} S^{(B)}_{[α][β]}` of the model at size `n` (merged `svarF`; `(eq:variancematrix)`). -/
def LWS (n : ℕ) (α β : Idx d (sz.L n) (sz.W n)) : ℝ :=
  svarF d (sz.L n) (sz.W n) (sz.lam n) α β

/-- **`f_{xy}(G)`** of `(fxyG_sum)` (`7_8:31-34`), `σ = +`, `G ≡ G_t`: `Σ_{α∉{x,y}} Σ_β S_{αβ} Ǧ_{ββ}
G_{xα} G_{αy}`, `Ǧ = G - M`, `M = m(E) I` (merged `STGM`). -/
def LWf (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, if α = x ∨ α = y then 0 else
    ∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β * Gt sz n E t true ω x α * Gt sz n E t true ω α y

/-- Integrability of `|f_{xy}(G)|^p` (a bounded measurable function on the probability space, since
`‖G_t‖ ≤ η_t⁻¹` for `t < 1`): the technical premise of the Markov step, not proved here. -/
def LWInteg (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 ≤ t → t < 1 → ∀ (p : ℕ)
    (x y : Idx d (sz.L n) (sz.W n)), Integrable (fun ω => ‖LWf sz n E t ω x y‖ ^ p) sz.seqP

/-- One term of `(eq:EGC)` (`7_8:9-10`): `W^d Σ_{a₁,a₂} S^{(B)}_{a₁a₂} tr(Ǧ_t(σc) E_{a₁})
tr(G_t(σc) E_{a₂} G_t(σc) E_{ac} G_t(σo) E_{ao})`, with `tr(Ǧ(σ) E_a) = 𝓛^{(1)}_{t,σ,a} - m(σ)`. -/
def LWcut (n : ℕ) (E t : ℝ) (σc σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, SB d (sz.L n) (sz.lam n) a₁ a₂ *
    (Lloop sz n E t ![σc] ![a₁] ω - mSigma E σc) * Lloop sz n E t ![σc, σc, σo] ![a₂, ac, ao] ω

/-- **The light-weight term `𝓔^{Gc,(2)}_{t,σ,a}`** (`(eq:LW-n=2)`, `3_5`; its form `(eq:EGC)`, `7_8:9-14`):
for `σ = (σ', σ)`, `a = (a, b)` the term above with the charge `σ`, the block `b`, plus the term
with `(σ, a) ↔ (σ', b)` exchanged. -/
def LWE (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  LWcut sz n E t (σ 1) (σ 0) (a 1) (a 0) ω + LWcut sz n E t (σ 0) (σ 1) (a 0) (a 1) ω

/-- `(initialGT2)` (`3_5:30`) for the control parameter `Ψ`. -/
def LWInit (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    Prec sz (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω) (fun n _ _ => Ψ n ^ 2)

/-- `(LW_assm)` (`3_5:388`): `𝓛^{(2)}_{t,σ,(a,b)} ≺ Ψ_t²(|a-b|)` for `σ ∈ {(+,-),(-,+)}`, all `a, b`. -/
def LWLoop2 (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  Prec sz (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖Lloop sz n (E n) (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
    (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2)

/-- All hypotheses of `lem:LWterm` beyond the flow setting (`3_5:385-392`). -/
def LWAssm (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ LWInit sz E t ε₀ Ψ ∧ LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    LWLoop2 sz E t Φ

/-- **`lem:LWterm`** (`3_5:385-404`), `(LW_conclusion)`: `𝓔^{Gc,(2)}_{t,σ,(a,b)} ≺ η_t⁻¹ Ψ_t(0) Ψ_t²(|a-b|)`
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

/-- `(LW_assm_exp)` (`3_5:411`): `𝓛^{(2)}_{t,σ,(a,b)} ≺ W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|)` for every `D > 0` (`≺` for
all large `D` is equivalent: larger `D` is the stronger hypothesis). -/
def LWLoopExp (E t : ℕ → ℝ) (ℓ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖Lloop sz n (E n) (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
        ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ))

/-- The hypotheses of `lem: EWGn2_N` (`3_5:406-411`) beyond the flow setting: `(initialGT2)` for a
control parameter `Ψ`, a length `0 ≤ ℓ ≤ (log W)^{10} ℓ_t`, and `(LW_assm_exp)`. -/
def LWAssmExp (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ LWInit sz E t ε₀ Ψ ∧ (∀ n, 0 ≤ ℓ n) ∧
    (∀ n, ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) (t n)) ∧
    LWLoopExp sz E t ℓ

/-- **`lem: EWGn2_N`** (`3_5:406-415`), `(LW_conclusion_exp)`: `𝓔^{Gc,(2)}_{t,σ,(a,b)} ≺ η_t⁻¹
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

/-- `(Gt_avgbound_flow)` (`1_2:1344`): `max_a |tr((G_t - M)E_a)| ≺ W^{-d} B_{t,0}`. -/
def LWAvgLaw (E t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Zd d (sz.L n))
    (fun n a ω => ‖Lloop sz n (E n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (E n)‖)
    (fun n _ _ => sz.Bctl n (t n))

/-- **`lem:LWterm_EXP`** (`6:83-88`), `(eq:ExpLWn=2)`: if `1 - t ≥ ĝ²/L^d` (the sizes where it fails are
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

/-- **`lem:LW_moment`** (`7_8:72-77`): for every fixed `p ∈ 2ℕ` there is `c > 0` (depending on `p`
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

/-- **`lem:LW_moment_exp`** (`7_8:78-83`): in the setting of `lem: EWGn2_N` with `1 - t > ĝ²/L²`, for
every fixed `p ∈ 2ℕ` and every `D > 0`: `E |f_{xy}|^p ≺ η_t^{-p} (W^{-d} B_{t,0})^{p/2}
[𝖳_t(|a-b| ∧ ℓ)]^p + W^{-D}` (`𝖳_t` is the merged `sfT`). -/
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

/-! ### Nested graphs: `lem:Anp_key`, `lem:Anp_key_gh`, `lem:Anp` (`7_8:933-1077`) -/

/-- `(eq:Gbyxi3)` (`7_8:963-966`): the edge variables `ξ_{αβ} = ξ_{βα} ≥ 0`, `ξ_{αβ} ≺ Ψ_t(|α-β|)` and
`Σ_β |ξ_{αβ}|² ≺ (W^d η_t)⁻¹`, uniformly in `α, β ∈ Z_L^d`. -/
def LWXi (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ξ n p.1 p.2 ω)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
    Prec sz (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (E n) (t n))⁻¹)


/-- **`lem:Anp_key`** (`7_8:960-985`): a nested graph (`p` edge-disjoint paths, `q ≤ p` internal vertices,
properties (1)-(3), no self-loops, no ghost edge) with edge variables `ξ` satisfying `(eq:Gbyxi3)`
has `𝒢_{ab} ≺ (W^d η_t)^{-q} Ψ_t^{ord(𝒢) - p} Π_i Ψ_t(c|a_i - b_i|)`, `Ψ_t = Ψ_t(0)` (T2040g), `c > 0`
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

/-- **`lem:Anp_key_gh`** (`7_8:1041-1077`): the same with ghost edges (at most one per path, an ending
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

/-- **`lem:Anp`** (`7_8:933-939`, `(eq:bddGamma_aux)`): the auxiliary graph of a locally standard graph
has all `a_i = [a]`, `b_i = [b]`: `Γ^{aux}_{[a][b]} ≺ (W^d η_t)^{-q} [Ψ_t(c|[a]-[b]|)]^p Ψ_t^{ord(Γ^{aux}) - p}`.
The properties (3)-(5) of `lem:localregular` of `Γ_{μ,xy}` are the nested properties of `Γ^{aux}`
(`7_8:956`); `Γ^{aux}` is a nested graph here (the passage `Γ_{μ,xy} ↦ Γ^{aux}` is `def_auxgraph`). -/
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

/-- The reduction of `lem:LWterm` to the moment bound (`7_8:20-91`): from `f_{xy} ≺ η_t⁻¹ Ψ_t(0)
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
regime `1 - t ≤ ĝ²/L²` (`LWtermExpN`) is `lem:LWterm` (`7_8:20`: "an immediate consequence", with
`ℓ_t = L`, `Ψ_t²(r) = W^{-d} 𝒯̃(r)`); the two index sets are glued by the union bound, and the passage from
`lem:LWterm` to the sub-sequence of the second regime needs a transfer lemma (finding T2040k). -/
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
(then `ℓ_t = L` and the exponential factor of `𝒯_t` is of order one for `r ≲ L`, `7_8:20`). -/
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

/-- The reduction of `lem: EWGn2_N` to the moment bound (`7_8:20-58`, `(eq:directG2)`,
`(eq:recolterm2)`, `(eq:recoltermwt2)`), on the sizes with `1 - t > ĝ²/L²`: from `f_{xy} ≺ η_t⁻¹
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

/-! ## 8. Compiled nonempty instances at `d = 3`

The merged preflight data of `RBM.Gauss.InductionDefsInst` (`d = 3`; `L_n = 4(n+1)`, `W_n =
(2(n+1))^5`, `lam_n = (2(n+1))^{-6} → 0`; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `z_n = 1/2 + i N_n^{-4/5}`;
`t ≡ 1/16 ≤ lemT z_n`), with the class `Ψ_t(r) ≡ W_n^{-1}` (constant: `W^{-3/2} ≤ Ψ_t ≤ W^{-ε₀}` at
`ε₀ = 1/20`, `(eq:Psi)` with `C₁ = C₂ = 2`, `C₃ = Cc = 1`).  Every deterministic hypothesis of each pin is
discharged; what stays a hypothesis of an instance is a stochastic premise of the lemma itself
(`(initialGT2)`, `(LW_assm)`, the edge variables `ξ`, the local laws of `lem:LWterm_EXP`). -/

-- the type of each instance is the pin's own instantiated statement (inferred from the application)
/-! ### The end of the flow, `t = t₀ = lemT z_n` (`t → 1`)

The extreme time of the flow framework: `1 - t₀ = η_{t₀}/Im m ≍ Im z_n ≥ N^{-1+ε}`.  The deterministic
hypotheses do not depend on `t` here, so the same data discharge them; the hypotheses `(initialGT2)`,
`(LW_assm)`, `ξ`, the local laws are those at `t₀`.  (At these data the strict regime `1 - t > ĝ²/L²` of
`lem:LW_moment_exp` is empty at `t₀` for `n ∈ {0,1,2,5,10,50,500}`, while `1 - t₀ ≥ ĝ²/L^d` holds: report b.7.) -/

end
