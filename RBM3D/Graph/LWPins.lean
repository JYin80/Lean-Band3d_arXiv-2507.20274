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
def LWPins_lwGb (ω : Ω d L W) (x y : Idx d L W) : ℂ := star (LWPins_lwG d L W E t ω x y)
def LWPins_lwGc (ω : Ω d L W) (x y : Idx d L W) : ℂ := LWPins_lwG d L W E t ω x y - if x = y then mE E else 0
def LWPins_lwGcb (ω : Ω d L W) (x y : Idx d L W) : ℂ := star (LWPins_lwGc d L W E t ω x y)
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

/-- The product `𝒢 / (G_{xy₁} f)` of `(Oe1x)` (`7_8:312`): `k₁` further blue out-edges `G_{xy_i}`, the
red out-edges `Ḡ_{xy'_i}` for `i ∈ s₂`, the blue in-edges `G_{w_i x}` for `i ∈ s₃`, all `k₄` red
in-edges `Ḡ_{w'_i x}`. -/
def LWPins_oe1xRest {k₁ k₂ k₃ k₄ : ℕ} (ω : Ω d L W) (x : Idx d L W) (y : Fin (k₁ + 1) → Idx d L W)
    (y' : Fin k₂ → Idx d L W) (w : Fin k₃ → Idx d L W) (w' : Fin k₄ → Idx d L W)
    (s₂ : Finset (Fin k₂)) (s₃ : Finset (Fin k₃)) : ℂ :=
  (∏ i : Fin k₁, LWPins_lwG d L W E t ω x (y i.succ)) * (∏ i ∈ s₂, LWPins_lwGb d L W E t ω x (y' i)) *
    (∏ i ∈ s₃, LWPins_lwG d L W E t ω (w i) x) * (∏ i : Fin k₄, LWPins_lwGb d L W E t ω (w' i) x)

/-- **`lem Oe14` (`(Oe1x)`, `7_8:309-330`)**, the edge expansion with respect to `G_{xy₁}`: the graph
`𝒢 = ∏_{i ≤ k₁+1} G_{xy_i} ∏_{i ≤ k₂} Ḡ_{xy'_i} ∏_{i ≤ k₃} G_{w_i x} ∏_{i ≤ k₄} Ḡ_{w'_i x} f`
(the paper's `k₁` is `k₁ + 1` here, so that `y₁ = y 0` exists; its `(k₁ - 1)` is `k₁`).  The nine
terms of `(Oe1x)`, in the order of `7_8:316-319`. -/
def LWedgeExp (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
    ∀ (k₁ k₂ k₃ k₄ : ℕ) (x : Idx d L W) (y : Fin (k₁ + 1) → Idx d L W) (y' : Fin k₂ → Idx d L W)
      (w : Fin k₃ → Idx d L W) (w' : Fin k₄ → Idx d L W)
      (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ),
      ∫ ω, LWPins_lwG d L W E t ω x (y 0) * (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
          LWPins_lwf d L W E t P ω) ∂(PF d L W g) =
        ∫ ω, (mE E * (if x = y 0 then 1 else 0) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * LWPins_lwf d L W E t P ω) +
          mE E * (∑ α, LWPins_lwS d L W g t x α * LWPins_lwGc d L W E t ω α α) *
            (LWPins_lwG d L W E t ω x (y 0) * (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
              LWPins_lwf d L W E t P ω)) +
          ∑ i : Fin k₂, (mE E * star (mE E)) *
            (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α (y 0) * LWPins_lwGb d L W E t ω α (y' i)) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' (Finset.univ.erase i) Finset.univ * LWPins_lwf d L W E t P ω) +
          ∑ i : Fin k₃, mE E ^ 2 *
            (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α (y 0) * LWPins_lwG d L W E t ω (w i) α) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ (Finset.univ.erase i) * LWPins_lwf d L W E t P ω) +
          ∑ i : Fin k₂, mE E * LWPins_lwGcb d L W E t ω x x *
            (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α (y 0) * LWPins_lwGb d L W E t ω α (y' i)) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' (Finset.univ.erase i) Finset.univ * LWPins_lwf d L W E t P ω) +
          ∑ i : Fin k₃, mE E * LWPins_lwGc d L W E t ω x x *
            (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α (y 0) * LWPins_lwG d L W E t ω (w i) α) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ (Finset.univ.erase i) * LWPins_lwf d L W E t P ω) +
          (k₁ : ℂ) * mE E * (∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω x α * LWPins_lwG d L W E t ω α (y 0)) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * LWPins_lwf d L W E t P ω) +
          (k₄ : ℂ) * mE E * (∑ α, LWPins_lwS d L W g t x α * LWPins_lwGb d L W E t ω α x * LWPins_lwG d L W E t ω α (y 0)) *
            (LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * LWPins_lwf d L W E t P ω) -
          mE E * ∑ α, LWPins_lwS d L W g t x α * LWPins_oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
            LWPins_lwG d L W E t ω α (y 0) * LWPins_lwdf d L W E t P ω α x) ∂(PF d L W g)

/-- **`lem T eq0` (`(Oe2x)`, the `GG` expansion, `7_8:334-349`)** of `𝒢 = G_{xy} G_{y'x} f`: the eight
terms of `7_8:337-339`. -/
def LWggExp (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
    ∀ (x y y' : Idx d L W) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ),
      ∫ ω, LWPins_lwG d L W E t ω x y * LWPins_lwG d L W E t ω y' x * LWPins_lwf d L W E t P ω ∂(PF d L W g) =
        ∫ ω, (mE E * (if x = y then 1 else 0) * LWPins_lwG d L W E t ω y' x * LWPins_lwf d L W E t P ω +
          mE E ^ 3 * LWPins_lwSp d L W g E t x y * LWPins_lwG d L W E t ω y' y * LWPins_lwf d L W E t P ω +
          mE E * (∑ α, LWPins_lwS d L W g t x α * LWPins_lwGc d L W E t ω α α) *
            (LWPins_lwG d L W E t ω x y * LWPins_lwG d L W E t ω y' x * LWPins_lwf d L W E t P ω) +
          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β * LWPins_lwGc d L W E t ω β β *
            LWPins_lwG d L W E t ω α y * LWPins_lwG d L W E t ω y' α * LWPins_lwf d L W E t P ω +
          mE E * LWPins_lwGc d L W E t ω x x * ∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α y *
            LWPins_lwG d L W E t ω y' α * LWPins_lwf d L W E t P ω +
          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β * LWPins_lwGc d L W E t ω α α *
            LWPins_lwG d L W E t ω β y * LWPins_lwG d L W E t ω y' β * LWPins_lwf d L W E t P ω -
          mE E * ∑ α, LWPins_lwS d L W g t x α * LWPins_lwG d L W E t ω α y * LWPins_lwG d L W E t ω y' x *
            LWPins_lwdf d L W E t P ω α x -
          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β * LWPins_lwG d L W E t ω β y *
            LWPins_lwG d L W E t ω y' α * LWPins_lwdf d L W E t P ω β α) ∂(PF d L W g)

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

/-- **`lem:LWterm`, "in particular"** (`(LW_conclusion2)`, `3_5:393-397`): `Ψ_t(|a-b|) = (W^{-c₀}
B_{t,|a-b|∧K})^{1/2}`, `c₀ > 0`, `0 ≤ K ≤ L`; then `𝓔^{Gc,(2)}_{t,σ,(a,b)} ≺ η_t⁻¹ (W^{-c₀} B_{t,0})^{1/2}
W^{-c₀} B_{t,|a-b|∧K}`.  `(eq:Psi)` for this class is a deterministic fact (`Φ` is monotone and
`B_{t,r} = A (r+1)^{-(d-2)} + B₀`), not a hypothesis. -/
def LWtermB (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ c₀ C₃ : ℝ) (K : ℕ → ℕ) (Ψ : ℕ → ℝ), 0 < c₀ → (∀ n, K n ≤ sz.L n) →
          0 < ε₀ → LWWindow sz ε₀ Ψ → LWInit sz (STflowE z) t ε₀ Ψ →
          LWClass sz ε₀ C₃ (fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
            Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)) →
          LWLoop2 sz (STflowE z) t (fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
            Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)) →
          Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ *
              (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0) ^ (1 / 2 : ℝ) *
              (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
                Bparam d (sz.L n) (sz.lam n) (t n) (min (zdistInf d (sz.L n) (p.2 0 - p.2 1)) (K n))))

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

/-- Binding to the merged vocabulary: the lambda that `LWtermB` passes to `LWClass`/`LWLoop2` is the merged
`LWPhiB` of `Graph/LWPsi` (T2051), definitionally. -/
example (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) : LWPhiB sz c₀ K t = fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
    Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ) := rfl

end RBM.Gauss.Sizes

/-! ## 8. Compiled nonempty instances at `d = 3`

The merged preflight data of `RBM.Gauss.InductionDefsInst` (`d = 3`; `L_n = 4(n+1)`, `W_n =
(2(n+1))^5`, `lam_n = (2(n+1))^{-6} → 0`; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `z_n = 1/2 + i N_n^{-4/5}`;
`t ≡ 1/16 ≤ lemT z_n`), with the class `Ψ_t(r) ≡ W_n^{-1}` (constant: `W^{-3/2} ≤ Ψ_t ≤ W^{-ε₀}` at
`ε₀ = 1/20`, `(eq:Psi)` with `C₁ = C₂ = 2`, `C₃ = Cc = 1`).  Every deterministic hypothesis of each pin is
discharged; what stays a hypothesis of an instance is a stochastic premise of the lemma itself
(`(initialGT2)`, `(LW_assm)`, the edge variables `ξ`, the local laws of `lem:LWterm_EXP`). -/

namespace RBM.Gauss.LWInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

theorem one_le_W (n : ℕ) : (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := (by norm_num : (1 : ℝ) ≤ 32).trans (W_ge_32 n)

/-- The class `Ψ_t(r) ≡ W_n^{-1}` and the control parameter `Ψ_t = W_n^{-1}`. -/
def Φ0 : ℕ → ℝ → ℝ := fun n _ => ((sz0.W n : ℕ) : ℝ)⁻¹
def Ψ0 : ℕ → ℝ := fun n => ((sz0.W n : ℕ) : ℝ)⁻¹

theorem W_rpow_inv_le (n : ℕ) : ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ) / 2) ≤ ((sz0.W n : ℕ) : ℝ)⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_W n) (by norm_num)

theorem W_inv_le_rpow (n : ℕ) : ((sz0.W n : ℕ) : ℝ)⁻¹ ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)) := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_W n) (by norm_num)

theorem window0 : LWWindow sz0 (1 / 20) Ψ0 :=
  Eventually.of_forall fun n => by
    simp only [Ψ0]
    exact ⟨by simpa using W_rpow_inv_le n, W_inv_le_rpow n⟩

theorem class0 : LWClass sz0 (1 / 20) 1 Φ0 :=
  ⟨Eventually.of_forall fun n r _ => ⟨inv_pos.mpr (by have := one_le_W n; positivity),
      W_inv_le_rpow n⟩, one_pos, Eventually.of_forall fun n => by
    simp only [Φ0, one_mul]; simpa using W_rpow_inv_le n⟩

theorem psiRel0 : LWPsiRel 2 2 (fun _ => 1) Φ0 := by
  refine ⟨fun n a _ b _ _ => le_rfl, by norm_num, by norm_num,
    fun C _ => Eventually.of_forall fun n ℓ _ _ => by simp [Φ0],
    Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_⟩
  simp only [Φ0]
  have hW : 0 < ((sz0.W n : ℕ) : ℝ)⁻¹ := inv_pos.mpr (by have := one_le_W n; positivity)
  have hr : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div (by linarith)).mpr h12
  have : (1 : ℝ) ≤ (ℓ₂ / ℓ₁) ^ (2 : ℝ) := Real.one_le_rpow hr (by norm_num)
  nlinarith

theorem psiAll0 : LWPsiAll sz0 (1 / 20) 2 2 1 (fun _ => 1) Φ0 := ⟨by norm_num, class0, psiRel0⟩

/-- `t ≡ 1/16` is a time in the flow range. -/
theorem tInst_range : (∀ n, 0 ≤ tInst n) ∧ ∀ n, tInst n ≤ lemT (z0 n) :=
  ⟨fun n => by simp [tInst], fun n => by simp only [tInst]; exact sixteenth_le_lemT n⟩

/-- The deterministic part of the hypotheses of `lem:LWterm` at the instance (`LWAssm` minus the
stochastic `(initialGT2)`, `(LW_assm)`). -/
theorem assm_of (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
    LWAssm sz0 (STflowE z0) tInst (1 / 20) Ψ0 Φ0 2 2 1 (fun _ => 1) :=
  ⟨by norm_num, window0, hI, class0, psiRel0, hL⟩

/-- **`lem:LWterm`, instantiated** (`d = 3`): the conclusion at the preflight data; the stochastic
premises `(initialGT2)`, `(LW_assm)` stay hypotheses. -/
theorem inst_LWterm (h : LWterm 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
        Φ0 n ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 20) 2 2 1 (fun _ => 1) Ψ0 Φ0 (assm_of hI hL)

end RBM.Gauss.LWInst

namespace RBM.Gauss.LWInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- The length `ℓ_n = ℓ_{t_n}` of `lem: EWGn2_N` (`0 ≤ ℓ ≤ (log W)^{10} ℓ_t`); not collapsed:
`1 ≤ ℓ_n` (`ℓT_one_le`). -/
def ℓT (t : ℕ → ℝ) : ℕ → ℝ := fun n => ellT (sz0.L n) (sz0.lam n) (t n)

theorem ℓT_one_le (t : ℕ → ℝ) (n : ℕ) : 1 ≤ ℓT t n :=
  one_le_ellT (by exact_mod_cast (by have := sz0.three_le_L n; omega : 1 ≤ sz0.L n))

theorem ℓT_window (t : ℕ → ℝ) (n : ℕ) :
    ℓT t n ≤ (Real.log ((sz0.W n : ℕ) : ℝ)) ^ 10 * ellT (sz0.L n) (sz0.lam n) (t n) := by
  have h0 : 0 ≤ ellT (sz0.L n) (sz0.lam n) (t n) := ellT_nonneg
  have hW : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := W_ge_32 n
  have hlog : (1 : ℝ) ≤ Real.log ((sz0.W n : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have : (1 : ℝ) ≤ (Real.log ((sz0.W n : ℕ) : ℝ)) ^ 10 := one_le_pow₀ hlog
  simp only [ℓT]
  nlinarith

theorem assmExpT_of (t : ℕ → ℝ) (hI : LWInit sz0 (STflowE z0) t (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) t (ℓT t)) :
    LWAssmExp sz0 (STflowE z0) t (1 / 20) Ψ0 (ℓT t) :=
  ⟨by norm_num, window0, hI, fun n => zero_le_one.trans (ℓT_one_le t n), ℓT_window t, hL⟩

theorem assmExp_of (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) :
    LWAssmExp sz0 (STflowE z0) tInst (1 / 20) Ψ0 (ℓT tInst) :=
  assmExpT_of tInst hI hL

/-- The two regimes of `lem: EWGn2_N` are both nonempty at the instance (`t ≡ 1/16`, `lam_n ≤ 1/64`). -/
theorem strict_all (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n := by
  have hx : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlam : sz0.lam n ≤ 1 / 64 := by
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 6])
  have hlam0 : 0 ≤ sz0.lam n := by change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹; positivity
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz0.three_le_L n; omega : 1 ≤ sz0.L n)
  have h1 : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ sz0.lam n ^ 2 :=
    div_le_self (by positivity) (one_le_pow₀ hL1)
  have h2 : sz0.lam n ^ 2 ≤ (1 / 64) ^ 2 := pow_le_pow_left₀ hlam0 hlam 2
  simp only [tInst]
  nlinarith

/-- **`lem: EWGn2_N`, instantiated** (`d = 3`), for every `D > 0`. -/
theorem inst_LWtermExp (h : LWtermExp 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tInst n) (ℓT tInst n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD

/-- **`lem:LW_moment`, instantiated**: every even `p` gives `c > 0` and the moment bound at the
preflight data. -/
theorem inst_LWMoment (h : LWMoment 3) (p : ℕ) (hp : 2 ∣ p)
    (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1 q.2‖ ^ p ∂(sz0.seqP))
        (fun n q _ => ((etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ p) := by
  obtain ⟨c, hc, H⟩ := h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) p hp
    (1 / 20) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 Ψ0 Φ0 (assm_of hI hL)⟩

/-- **`lem:LW_moment_exp`, instantiated**: the index set (the sizes with `1 - t > ĝ²/L²`) is all of
`n` at the instance (`strict_all`). -/
theorem inst_LWMomentExp (h : LWMomentExp 3) (p : ℕ) (hp : 2 ∣ p)
    (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst))
    (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => {_q : Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n})
      (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1.1 q.1.2‖ ^ p ∂(sz0.seqP))
      (fun n q _ => ((etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n)
          (min ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1.1 - STblk sz0 n q.1.2) : ℕ) : ℝ) (ℓT tInst n))) ^ p +
        ((sz0.W n : ℕ) : ℝ) ^ (-D)) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) p hp (1 / 6) sz0 z0
    flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD

/-- **`lem:LWterm_EXP`, instantiated**: the local laws are the premises (other gates' pins); the index set
`1 - t ≥ ĝ²/L^d` is all of `n` (`strict_all`). -/
theorem inst_LWtermEXP (h : LWtermEXP 3) (h1 : STLocalEntry sz0 (STflowE z0) tInst)
    (h2 : LWAvgLaw sz0 (STflowE z0) tInst) (h3 : STLmax sz0 (STflowE z0) tInst)
    (h4 : STLK sz0 (STflowE z0) tInst) (h5 : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 h1 h2 h3 h4 h5

end RBM.Gauss.LWInst

namespace RBM.Gauss.LWInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- **`lem:Anp_key`, instantiated** on the auxiliary graph `figAux` of the left panel of
`fig:p=2expansion` (`p = q = 2`; nested, no ghost edge: `figAux_nested`): the constant `c` of the graph,
then the bound at the preflight data; the edge variables `ξ` and their bounds `(eq:Gbyxi3)` stay
hypotheses. -/
theorem inst_AnpKey (h : LWAnpKey 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => (Fin 2 → Zd 3 (sz0.L n)) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) ab.1 ab.2)
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - (2 : ℕ)) *
          ∏ i, Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ))) := by
  obtain ⟨c, hc, H⟩ := h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 2
    le_rfl RBM.Graph.figAux RBM.Graph.figAux_nested.2 RBM.Graph.figAux_nested.1 (1 / 20) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 Φ0 psiAll0 ξ hξ⟩

/-- **`lem:Anp`, instantiated** on `figAux` (`a_i ≡ [a]`, `b_i ≡ [b]`). -/
theorem inst_Anp (h : LWAnp 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - (2 : ℕ))) := by
  obtain ⟨c, hc, H⟩ := h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 2
    le_rfl RBM.Graph.figAux RBM.Graph.figAux_nested.2 RBM.Graph.figAux_nested.1 (1 / 20) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 Φ0 psiAll0 ξ hξ⟩

/-- **`lem:Anp_key_gh`, instantiated** on `figAux` (no ghost edge: `GhostOK` holds). -/
theorem figAux_ghostOK : RBM.Graph.figAux.GhostOK := by
  unfold RBM.Graph.NGraph.GhostOK
  decide +kernel

end RBM.Gauss.LWInst

namespace RBM.Graph.LWInstFixed

open RBM RBM.Gauss

-- the type of each instance is the pin's own instantiated statement (inferred from the application)
set_option linter.defProp false

/-- The resolvent polynomial `P = X_{(+,0,1)} X_{(-,1,0)}` (the entry `G_{01}` times the entry `(1,0)` of
`G^*`, i.e. `G_{01} Ḡ_{01}`) at `d = 3`, `L = 3`, `W = 2`. -/
def P01 : MvPolynomial (Bool × Idx 3 3 2 × Idx 3 3 2) ℂ :=
  MvPolynomial.X (true, 0, 1) * MvPolynomial.X (false, 1, 0)

/-- **`(Owx)`, instantiated** (the application of the pin below) at `d = 3`, `L = 3`, `W = 2`, `g = 1`, `E = 0`, `t = 1/2`: every
hypothesis (`3 ≤ L`, `|E| < 2`, `0 ≤ t < 1`) discharged. -/
def inst_ssl (h : LWweightExp 3) (x : Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) P01 x

/-- **`(Oe1x)`, instantiated** (`k₁ = 1`, so `k₁ + 1 = 2` blue out-edges; `k = (2, 1, 1, 1)`: two blue and one red out-edge, one in-edge each). -/
def inst_edge (h : LWedgeExp 3) (x : Idx 3 3 2) (y : Fin 2 → Idx 3 3 2) (y' : Fin 1 → Idx 3 3 2)
    (w : Fin 1 → Idx 3 3 2) (w' : Fin 1 → Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 1 1 1 1 x y y' w w' P01

/-- **`(Oe2x)`, instantiated**. -/
def inst_gg (h : LWggExp 3) (x y y' : Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) x y y' P01

end RBM.Graph.LWInstFixed

/-! ### The end of the flow, `t = t₀ = lemT z_n` (`t → 1`)

The extreme time of the flow framework: `1 - t₀ = η_{t₀}/Im m ≍ Im z_n ≥ N^{-1+ε}`.  The deterministic
hypotheses do not depend on `t` here, so the same data discharge them; the hypotheses `(initialGT2)`,
`(LW_assm)`, `ξ`, the local laws are those at `t₀`.  (At these data the strict regime `1 - t > ĝ²/L²` of
`lem:LW_moment_exp` is empty at `t₀` for `n ∈ {0,1,2,5,10,50,500}`, while `1 - t₀ ≥ ĝ²/L^d` holds: report b.7.) -/

namespace RBM.Gauss.LWInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- The merged `InductionDefsInst.tEnd` (`t ≡ t₀ = lemT z_n`) is a time in the flow range. -/
theorem tEnd_range : (∀ n, 0 ≤ tEnd n) ∧ ∀ n, tEnd n ≤ lemT (z0 n) :=
  ⟨fun n => (lemT_pos (z0_im_pos n)).le, fun _ => le_rfl⟩

theorem inst_LWterm_endT (h : LWterm 3) (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tEnd Φ0) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tEnd n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tEnd n))⁻¹ * Φ0 n 0 *
        Φ0 n ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tEnd tEnd_range.1 tEnd_range.2 (1 / 20) 2 2 1 (fun _ => 1) Ψ0 Φ0
    ⟨by norm_num, window0, hI, class0, psiRel0, hL⟩

theorem inst_LWtermExp_endT (h : LWtermExp 3) (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tEnd (ℓT tEnd)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tEnd n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tEnd n))⁻¹ * (sz0.Bctl n (tEnd n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tEnd n) (ℓT tEnd n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tEnd tEnd_range.1 tEnd_range.2 (1 / 20) Ψ0 (ℓT tEnd) (assmExpT_of tEnd hI hL) D hD

/-- **`lem: EWGn2_N`, second regime (`LWtermExpN`), instantiated** at `t = t₀` with the window
`ℓ = ℓ_{t₀}`: the index set `1 - t ≤ ĝ²/L²` is the regime that holds at `t₀` (report b.7). -/
theorem inst_LWtermExpN (h : LWtermExpN 3) (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tEnd (ℓT tEnd)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        1 - tEnd n ≤ sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2})
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tEnd n) p.1.1 p.1.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tEnd n))⁻¹ * (sz0.Bctl n (tEnd n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tEnd n) (ℓT tEnd n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tEnd tEnd_range.1 tEnd_range.2 (1 / 20) Ψ0 (ℓT tEnd) (assmExpT_of tEnd hI hL) D hD

theorem inst_LWMoment_endT (h : LWMoment 3) (p : ℕ) (hp : 2 ∣ p)
    (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0) (hL : LWLoop2 sz0 (STflowE z0) tEnd Φ0) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tEnd n) ω q.1 q.2‖ ^ p ∂(sz0.seqP))
        (fun n q _ => ((etaT (STflowE z0 n) (tEnd n))⁻¹ * Φ0 n 0 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ p) := by
  obtain ⟨c, hc, H⟩ := h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) p hp
    (1 / 20) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 z0 flow_z0 tEnd tEnd_range.1 tEnd_range.2 Ψ0 Φ0
    ⟨by norm_num, window0, hI, class0, psiRel0, hL⟩⟩

theorem inst_AnpKey_endT (h : LWAnpKey 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tEnd Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => (Fin 2 → Zd 3 (sz0.L n)) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) ab.1 ab.2)
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tEnd n))⁻¹ ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - (2 : ℕ)) *
          ∏ i, Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ))) := by
  obtain ⟨c, hc, H⟩ := h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 2
    le_rfl RBM.Graph.figAux RBM.Graph.figAux_nested.2 RBM.Graph.figAux_nested.1 (1 / 20) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 z0 flow_z0 tEnd tEnd_range.1 tEnd_range.2 Φ0 psiAll0 ξ hξ⟩

theorem inst_LWtermEXP_endT (h : LWtermEXP 3) (h1 : STLocalEntry sz0 (STflowE z0) tEnd)
    (h2 : LWAvgLaw sz0 (STflowE z0) tEnd) (h3 : STLmax sz0 (STflowE z0) tEnd)
    (h4 : STLK sz0 (STflowE z0) tEnd) (h5 : STDecay sz0 (STflowE z0) tEnd) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tEnd n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tEnd n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tEnd n)⁻¹ * (sz0.Bctl n (tEnd n)) ^ (5 / 2 : ℝ)) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tEnd tEnd_range.1 tEnd_range.2 h1 h2 h3 h4 h5

end RBM.Gauss.LWInst

namespace RBM.Gauss.LWInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

theorem lam_le (n : ℕ) : sz0.lam n ≤ 1 / 64 := by
  have hx : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
  rw [one_div]
  exact inv_anti₀ (by norm_num) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 6])

theorem lam_nonneg (n : ℕ) : 0 ≤ sz0.lam n := by
  change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹; positivity

/-- The explicit class of `(LW_conclusion2)` at `c₀ = 1`, `K ≡ 1`, `t ≡ 1/16`:
`Ψ_t(r) = (W^{-1} B_{t, ⌊r⌋∧1})^{1/2}`. -/
def ΦB : ℕ → ℝ → ℝ := fun n r => (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) *
  Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) (min ⌊r⌋₊ 1)) ^ (1 / 2 : ℝ)

theorem Bparam_bounds (n k : ℕ) :
    0 < Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) k ∧ Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) k ≤ 3 ∧
      (k = 0 → 1 ≤ Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) k) := by
  have hg := lam_le n
  have hg0 := lam_nonneg n
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz0.three_le_L n; omega : 1 ≤ sz0.L n)
  have ht : |1 - tInst n| = 15 / 16 := by simp only [tInst]; norm_num [abs_of_pos]
  have hg2 : sz0.lam n ^ 2 ≤ 1 / 4096 := by nlinarith
  have hA : 0 < sz0.lam n ^ 2 + 15 / 16 := by positivity
  have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ (3 - 2) := by
    simp only [show 3 - 2 = 1 from rfl, pow_one]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hL3 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 3 := one_le_pow₀ hL1
  have e1 : (sz0.lam n ^ 2 + 15 / 16)⁻¹ ≤ 16 / 15 := by
    rw [inv_le_comm₀ hA (by norm_num)]; nlinarith
  have e2 : (((k : ℝ) + 1) ^ (3 - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk1
  have e3 : (((sz0.L n : ℕ) : ℝ) ^ 3 * (15 / 16))⁻¹ ≤ 16 / 15 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have p1 : 0 < (sz0.lam n ^ 2 + 15 / 16)⁻¹ := inv_pos.mpr hA
  have p2 : 0 < (((k : ℝ) + 1) ^ (3 - 2))⁻¹ := inv_pos.mpr (by linarith)
  have p3 : 0 < (((sz0.L n : ℕ) : ℝ) ^ 3 * (15 / 16))⁻¹ := inv_pos.mpr (by positivity)
  simp only [Bparam, ht]
  refine ⟨by positivity, ?_, fun hk => ?_⟩
  · nlinarith
  · subst hk
    have h1 : 1 ≤ (sz0.lam n ^ 2 + 15 / 16)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hA]; nlinarith
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    nlinarith

theorem classB : LWClass sz0 (1 / 20) 1 ΦB := by
  refine ⟨Eventually.of_forall fun n r _ => ?_, one_pos, Eventually.of_forall fun n => ?_⟩
  · obtain ⟨hp, hle, -⟩ := Bparam_bounds n (min ⌊r⌋₊ 1)
    have hW : 0 < ((sz0.W n : ℕ) : ℝ) := by have := one_le_W n; positivity
    have hWm : 0 < ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hW _
    refine ⟨Real.rpow_pos_of_pos (mul_pos hWm hp) _, ?_⟩
    simp only [ΦB]
    have h3 : (3 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (9 / 10 : ℝ) := by
      have h32 : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := W_ge_32 n
      calc (3 : ℝ) ≤ Real.sqrt 32 := Real.le_sqrt_of_sq_le (by norm_num)
        _ = (32 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 32
        _ ≤ (32 : ℝ) ^ (9 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ ((sz0.W n : ℕ) : ℝ) ^ (9 / 10 : ℝ) := Real.rpow_le_rpow (by norm_num) h32 (by norm_num)
    have h4 : ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) * Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) (min ⌊r⌋₊ 1) ≤
        ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) := by
      have e : ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) =
          ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) * ((sz0.W n : ℕ) : ℝ) ^ (9 / 10 : ℝ) := by
        rw [← Real.rpow_add hW]; norm_num
      rw [e]
      exact mul_le_mul_of_nonneg_left (hle.trans h3) hWm.le
    calc (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) *
          Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) (min ⌊r⌋₊ 1)) ^ (1 / 2 : ℝ)
        ≤ (((sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ))) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (mul_pos hWm hp).le h4 (by norm_num)
      _ = ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)) := by
          rw [← Real.rpow_mul hW.le]; norm_num
  · obtain ⟨hp, -, hge⟩ := Bparam_bounds n 0
    have hW : 0 < ((sz0.W n : ℕ) : ℝ) := by have := one_le_W n; positivity
    have hWm : 0 < ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hW _
    simp only [ΦB, one_mul, Nat.floor_zero, Nat.zero_min]
    calc ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ) / 2) ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_W n) (by norm_num)
      _ = (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hW.le]; norm_num
      _ ≤ (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) * Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) 0) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hWm.le (by nlinarith [hge rfl]) (by norm_num)

/-- **`lem:LWterm`, "in particular", instantiated** (`(LW_conclusion2)`): the explicit class
`Ψ_t(r) = (W^{-1} B_{t,|a-b|∧1})^{1/2}` (`c₀ = 1`, `K ≡ 1`), `t ≡ 1/16`: positivity, `≤ W^{-1/20}` and
`W^{-3/2} ≤ Ψ_t(0)` (`classB`) are proved; `(initialGT2)` and `(LW_assm)` stay hypotheses. -/
theorem inst_LWtermB (h : LWtermB 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tInst ΦB) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ *
        (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) * Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) 0) ^ (1 / 2 : ℝ) *
        (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) *
          Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) (min (zdistInf 3 (sz0.L n) (p.2 0 - p.2 1)) 1))) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 20) 1 1 (fun _ => 1) Ψ0 one_pos
    (fun n => by have := sz0.three_le_L n; simpa using (by omega : 1 ≤ sz0.L n)) (by norm_num) window0 hI
    classB hL

end RBM.Gauss.LWInst

namespace RBM.Gauss.LWInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- **`lem: EWGn2_N`, strict regime, instantiated**: the index set `1 - t > ĝ²/L²` is all of `n` at
`t ≡ 1/16` (`strict_all`). -/
theorem inst_LWtermExpS (h : LWtermExpS 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n})
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tInst n) (ℓT tInst n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
    flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD

/-- **`lem:Anp_key_gh`, instantiated** on `figAux` (the ghost condition holds trivially: no ghost
edge): `n_ngh = p = 2`. -/
theorem inst_AnpKeyGh (h : LWAnpKeyGh 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => (Fin 2 → Zd 3 (sz0.L n)) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) ab.1 ab.2)
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - RBM.Graph.figAux.nngh) *
          ∏ i, (if RBM.Graph.figAux.noGhostPath i = true then
            Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1)) := by
  obtain ⟨c, hc, H⟩ := h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 2
    le_rfl RBM.Graph.figAux figAux_ghostOK RBM.Graph.figAux_nested.1 (1 / 20) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 Φ0 psiAll0 ξ hξ⟩

/-- **`(eq:Psi)` shift** at the instance: `Ψ_t(r/3) ≤ K Ψ_t(r)` with a constant `K`. -/
theorem inst_shift :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → Φ0 n (1 / 3 * r) ≤ K * Φ0 n r :=
  psiAll0.shift sz0 (c := 1 / 3) (by norm_num)

/-- **Reduction of `lem:LWterm` to the moment bound, instantiated** (`LWReduceB`, `7_8:20-91`) at
`t ≡ 1/16`: `(initialGT2)`, `(LW_assm)` and the Markov-step bound on `f_{xy}` stay hypotheses. -/
theorem inst_LWReduceB (h : LWReduceB 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0)
    (hf : Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n q ω => ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1 q.2‖)
      (fun n q _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
        Φ0 n ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
        Φ0 n ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 20) 2 2 1 (fun _ => 1) Ψ0 Φ0 (assm_of hI hL) hf

/-- **Reduction of `lem: EWGn2_N` to the moment bound, instantiated** (`LWReduceT`, `7_8:20-58`) at
`t ≡ 1/16`, `ℓ = ℓ_t`, every `D > 0`: the index set `1 - t > ĝ²/L²` is all of `n` (`strict_all`);
`(initialGT2)`, `(LW_assm)` and the bound on `f_{xy}` stay hypotheses. -/
theorem inst_LWReduceT (h : LWReduceT 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D)
    (hf : Prec sz0 (U := fun n => {_q : Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n})
      (fun n q ω => ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1.1 q.1.2‖)
      (fun n q _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n)
          (min ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1.1 - STblk sz0 n q.1.2) : ℕ) : ℝ) (ℓT tInst n)) +
        ((sz0.W n : ℕ) : ℝ) ^ (-D))) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n})
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tInst n) (ℓT tInst n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) :=
  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
    flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD hf

end RBM.Gauss.LWInst

end
